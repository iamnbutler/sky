import CairnFrame
import CairnHost
import CairnRender
import Foundation
import ImageIO
import UniformTypeIdentifiers

// `Sky --selftest <server.ts>`: Sky against cairn_atproto's fake PDS, driven through Cairn's
// `Engine` and the host's real world (files, http, timers, the Keychain) as a person would:
// clicks at controls' centres and typing. It reads only the frame, never the Lean state.
//
// Nothing here reaches the network or a real account: the fake runs on 127.0.0.1 with the
// identifier and app password it generates, a URL protocol refuses every other host, the home
// directory is the Makefile's scratch one (CFFIXED_USER_HOME), and the Keychain items live under a
// throwaway service, `cairn.sky-selftest-<uuid>`, deleted at the end whatever happens. Only items
// this run wrote are read or deleted.

/// What the frames ask the host for beyond drawing: the Dock badges and the announcements.
final class Heard: @unchecked Sendable {
    private let lock = NSLock()
    private var badges: [String?] = []
    private var said: [String] = []
    func take(_ p: CairnHost.Published) {
        for e in p.frame.effects {
            switch e {
            case let .badge(b): lock.withLock { badges.append(b) }
            case let .announce(t, _): lock.withLock { said.append(t) }
            default: break
            }
        }
    }
    /// The badge last sent, `.some(nil)` for none, `nil` if never sent.
    var badge: String?? { lock.withLock { badges.last } }
    var announced: [String] { lock.withLock { said } }
    /// Every badge sent, in order.
    var sent: [String?] { lock.withLock { badges } }
}

/// The fake PDS, run with Bun on a free port of 127.0.0.1.
final class FakePDS {
    let process = Process()
    let service: String
    let identifier: String
    let password: String

    init?(_ script: String, _ extra: [String] = []) {
        let out = Pipe()
        process.executableURL = URL(fileURLWithPath: "/usr/bin/env")
        process.arguments = ["bun", script, "--port", "0", "--quiet", "--seed", "20261025"] + extra
        process.standardOutput = out
        process.standardError = FileHandle.nullDevice
        do { try process.run() } catch { return nil }
        var text = ""
        var fields: [String: String] = [:]
        let end = Date().addingTimeInterval(20)
        while fields["app password"] == nil, Date() < end, process.isRunning {
            let d = out.fileHandleForReading.availableData
            if d.isEmpty { Thread.sleep(forTimeInterval: 0.05); continue }
            text += String(decoding: d, as: UTF8.self)
            for line in text.split(separator: "\n") {
                for k in ["fake-pds listening on", "identifier", "app password"] where line.hasPrefix(k + " ") {
                    fields[k] = String(line.dropFirst(k.count + 1))
                }
            }
        }
        guard let s = fields["fake-pds listening on"], let i = fields["identifier"], let p = fields["app password"] else {
            process.terminate()
            return nil
        }
        service = s; identifier = i; password = p
    }

    /// `POST /control/<path>`: posts arrive, the next calls fail, replies slow down.
    func control(_ path: String) {
        var r = URLRequest(url: URL(string: service + "/control/" + path)!)
        r.httpMethod = "POST"
        let done = DispatchSemaphore(value: 0)
        URLSession.shared.dataTask(with: r) { _, _, _ in done.signal() }.resume()
        _ = done.wait(timeout: .now() + 5)
    }

    /// `GET /control/state`: the server's state (the tester's records, the accounts muted).
    func state() -> [String: Any] {
        let done = DispatchSemaphore(value: 0)
        nonisolated(unsafe) var out: [String: Any] = [:]
        URLSession.shared.dataTask(with: URL(string: service + "/control/state")!) { d, _, _ in
            if let d, let j = try? JSONSerialization.jsonObject(with: d) as? [String: Any] { out = j }
            done.signal()
        }.resume()
        _ = done.wait(timeout: .now() + 5)
        return out
    }
    /// The tester's records on the server: likes, reposts and follows.
    func records() -> [String] { state()["records"] as? [String] ?? [] }
    /// Waits up to `seconds` for the tester's records to number `n`.
    func awaitRecords(_ n: Int, _ seconds: Double = 8) -> Bool {
        let end = Date().addingTimeInterval(seconds)
        while Date() < end { if records().count == n { return true }; Thread.sleep(forTimeInterval: 0.1) }
        return false
    }

    /// Stops the server (this process's child, by its pid).
    func stop() {
        guard process.isRunning else { return }
        kill(process.processIdentifier, SIGTERM)
        process.waitUntilExit()
    }
}

/// Refuses every request to a host other than 127.0.0.1.
final class LoopbackOnly: URLProtocol, @unchecked Sendable {
    override class func canInit(with request: URLRequest) -> Bool { request.url?.host != "127.0.0.1" }
    override class func canonicalRequest(for request: URLRequest) -> URLRequest { request }
    override func startLoading() {
        client?.urlProtocol(self, didFailWithError: NSError(domain: NSURLErrorDomain, code: NSURLErrorNotConnectedToInternet))
    }
    override func stopLoading() {}
}

/// The Keychain under a throwaway service, remembering every item it wrote. `KeychainStore`
/// makes every Security call on one queue for the process (Cairn 0.4.1, cairn#237), so a read
/// here never races the app's `forgetSecret`.
final class ThrowawayKeychain: SecretStore, @unchecked Sendable {
    let keychain = KeychainStore(service: "cairn.sky-selftest-" + UUID().uuidString)
    private let lock = NSLock()
    private var written: Set<String> = []

    func read(_ account: String) -> Result<String?, ReplyError> { keychain.read(account) }
    func write(_ account: String, _ value: String) -> Result<Void, ReplyError> {
        lock.withLock { _ = written.insert(account) }
        return keychain.write(account, value)
    }
    func delete(_ account: String) -> Result<Void, ReplyError> { keychain.delete(account) }

    var accounts: Set<String> { lock.withLock { written } }
    /// The items this run wrote that are still there.
    var held: [String] {
        accounts.filter { if case .success(.some) = read($0) { true } else { false } }.sorted()
    }
    func clean() { for a in accounts { _ = delete(a) } }
}

final class Selftest {
    let script: String
    let shots: URL?
    var fake: FakePDS?
    let heard = Heard()
    let store = ThrowawayKeychain()
    var engine: Engine?
    private lazy var renderer = try? Renderer()

    init(server: String, shots: String?) {
        script = server
        self.shots = shots.map { URL(fileURLWithPath: $0, isDirectory: true) }
    }

    func clean() {
        engine?.stop()
        store.clean()
        fake?.stop()
    }

    func fail(_ message: String) -> Never {
        let seen = engine?.latest.map { texts($0.frame).joined(separator: " | ") } ?? ""
        clean()
        FileHandle.standardError.write(Data("selftest: FAIL: \(message)\n  frame: \(seen)\n".utf8))
        exit(1)
    }

    var frame: Frame { engine?.latest?.frame ?? Frame(size: size, draws: []) }
    func texts(_ f: Frame) -> [String] { f.ax.map(\.label).filter { !$0.isEmpty } }
    func node(_ claim: UInt32, _ f: Frame? = nil) -> AxNode? {
        (f ?? frame).ax.first { $0.control == ControlRef(claim: claim) }
    }
    func shows(_ text: String, _ f: Frame) -> Bool { f.ax.contains { $0.label == text } }
    func node(_ r: ControlRef, _ f: Frame? = nil) -> AxNode? { (f ?? frame).ax.first { $0.control == r } }
    /// Whether the toggle `r` shows on (VoiceOver's "selected").
    func on(_ r: ControlRef, _ f: Frame? = nil) -> Bool? { node(r, f).map(\.selected) }

    @discardableResult
    func until(_ seconds: Double, _ what: String, _ ok: (Frame) -> Bool) -> Frame {
        let end = Date().addingTimeInterval(seconds)
        while Date() < end {
            if let p = engine?.latest, ok(p.frame) { return p.frame }
            Thread.sleep(forTimeInterval: 0.02)
        }
        fail("\(what) (after \(seconds) s)")
    }

    /// Clicks control `claim` once the frame offers it.
    func click(_ claim: UInt32) {
        guard let n = node(claim, until(2, "no control ^\(claim)") { self.node(claim, $0) != nil }) else { fail("no control ^\(claim)") }
        let p = Point(x: n.rect.x + n.rect.w / 2, y: n.rect.y + n.rect.h / 2)
        engine?.send([.pointerMove(p), .pointerDown(p, .primary, clicks: 1, Mods()), .pointerUp(p, .primary, Mods())])
    }

    /// Clicks the control `r` (a row's, `^N#k`) once the frame offers it.
    func click(_ r: ControlRef) {
        guard let n = node(r, until(2, "no control \(r.label)") { self.node(r, $0) != nil }) else { fail("no control \(r.label)") }
        let p = Point(x: n.rect.x + n.rect.w / 2, y: n.rect.y + n.rect.h / 2)
        engine?.send([.pointerMove(p), .pointerDown(p, .primary, clicks: 1, Mods()), .pointerUp(p, .primary, Mods())])
    }

    /// The window's open control menu, if its owner is `owner` (docs/frame.md, "Surface records").
    func openMenu(_ owner: ControlRef, _ f: Frame) -> [MenuRecord]? {
        guard let st = f.surface(1)?.status, st.control == owner, !st.menu.isEmpty else { return nil }
        return st.menu
    }
    /// Opens a post's ⋯ menu (^52#k) by clicking it, as a person does, and returns its items.
    func menu(_ k: UInt32) -> [MenuRecord] {
        let owner = ControlRef(claim: 52, key: k)
        click(owner)
        let end = Date().addingTimeInterval(2)
        while Date() < end {
            if let m = engine?.latest.flatMap({ openMenu(owner, $0.frame) }) { return m }
            Thread.sleep(forTimeInterval: 0.02)
        }
        let st = frame.surface(1)?.status
        fail("\(owner.label)'s menu didn't open: the window's menu is \(st?.control.label ?? "-") with \(st?.menu.count ?? 0) items; \(owner.label) is \(node(owner).map { "\($0.rect)" } ?? "not in the frame")")
    }
    /// Chooses `r` in the open control menu; the host then says it closed.
    func choose(_ r: ControlRef) { engine?.send([.menuSelect(place: 1, r), .menuClose(place: 1)]) }
    func closeMenu() { engine?.send([.menuClose(place: 1)]) }
    /// The menu bar's items (^48).
    func menuBar(_ f: Frame) -> [MenuRecord] { f.surface(48)?.status.menu ?? [] }
    func signOutItem(_ f: Frame) -> MenuRecord? { menuBar(f).first { $0.control == ControlRef(claim: 49) } }

    /// Clicks field `claim` and types `text` over what it holds.
    func type(_ claim: UInt32, _ text: String) {
        click(claim)
        until(2, "^\(claim) not focused") { self.node(claim, $0)?.focused == true }
        engine?.send([.selectAll, .insertText(text)])
    }

    /// The latest frame, rendered offscreen at 2×, as `<name>.png` under `--shots`.
    func shot(_ name: String) {
        guard let dir = shots else { return }
        Thread.sleep(forTimeInterval: 0.1)
        try? FileManager.default.createDirectory(at: dir, withIntermediateDirectories: true)
        let url = dir.appendingPathComponent(name + ".png")
        guard let r = renderer, let img = try? r.image(frame, scale: 2) else { fail("couldn't render \(name)") }
        let d = CGImageDestinationCreateWithURL(url as CFURL, UTType.png.identifier as CFString, 1, nil)!
        CGImageDestinationAddImage(d, img.cgImage(), nil)
        guard CGImageDestinationFinalize(d) else { fail("couldn't write \(url.path)") }
    }

    /// Launches Sky on a fresh engine: the fake's service as the saved default, the throwaway
    /// Keychain, loopback only. The bench passes its own core and hears every frame.
    func launch(_ service: String, core: (() -> AppCore)? = nil, onPublish: (@Sendable (CairnHost.Published) -> Void)? = nil) {
        var h = Handlers.standard
        h.table[14] = { r, reply in
            guard case let .readDefault(d, k) = r else { return }
            reply(d == "dev.cairn.sky" && k == "service" ? .bytes(Array(service.utf8)) : .failed(.notFound, "no such default"))
        }
        h.table[12] = { _, reply in reply(.done) }  // the app-passwords link opens nothing
        let c = URLSessionConfiguration.ephemeral
        c.protocolClasses = [LoopbackOnly.self] + (c.protocolClasses ?? [])
        let inert = Devices.inert
        let devices = Devices(microphone: inert.microphone, keys: inert.keys, typist: inert.typist,
                              secrets: SecretSource(environment: { _ in nil }, readFile: { _ in nil }, store: store),
                              session: URLSession(configuration: c))
        let e = Engine(size: size, scalePercent: 200, world: World(handlers: h, devices: devices), makeCore: core ?? { LeanCore(app) })
        e.onPublish = onPublish
        engine = e
        e.start()
        guard e.wait(through: 0) != nil else { fail("no first frame") }
    }

    /// The feed's list: the largest clip the frame pushes.
    func listRect(_ f: Frame) -> Rect? {
        var best: Rect?
        for d in f.draws { if case let .pushClip(r) = d, r.y > 0, r.w >= 300, r.h >= 300, r.h > (best?.h ?? 0) { best = r } }
        return best
    }
    /// The post rows (^32#k) by key: where each is laid.
    func rows(_ f: Frame) -> [UInt32: Rect] {
        var out: [UInt32: Rect] = [:]
        for n in f.ax { if let c = n.control, c.claim == 32 { out[c.key] = n.rect } }
        return out
    }
    /// The first post row showing at the top of the list, and its y.
    func firstShown(_ f: Frame) -> (key: UInt32, y: Int32)? {
        guard let l = listRect(f) else { return nil }
        return rows(f).filter { $0.value.y + $0.value.h > l.y && $0.value.y < l.y + l.h }
            .min { $0.value.y < $1.value.y }.map { ($0.key, $0.value.y) }
    }
    /// Each post row's author (^32#k is "Post by @handle"), by key.
    func authors(_ f: Frame) -> [UInt32: String] {
        var out: [UInt32: String] = [:]
        for n in f.ax { if let c = n.control, c.claim == 32, n.label.hasPrefix("Post by ") { out[c.key] = String(n.label.dropFirst(8)) } }
        return out
    }
    /// The key of the topmost row with anything showing in the list (its post, toggles or ⋯):
    /// the row the runtime keeps still.
    func topRow(_ f: Frame) -> UInt32? {
        guard let l = listRect(f) else { return nil }
        return f.ax.filter { n in
            guard let c = n.control, [32, 37, 38, 52].contains(c.claim) else { return false }
            return n.rect.h > 0 && n.rect.y + n.rect.h > l.y && n.rect.y < l.y + l.h
        }.min { $0.rect.y < $1.rect.y }?.control?.key
    }
    /// Each row's author, from its ⋯ ("More for @handle's post"), by key.
    func rowAuthors(_ f: Frame) -> [UInt32: String] {
        var out: [UInt32: String] = [:]
        for n in f.ax { if let c = n.control, c.claim == 52, n.label.hasPrefix("More for "), n.label.hasSuffix("'s post") {
            out[c.key] = String(n.label.dropFirst(9).dropLast(7))
        } }
        return out
    }

    /// Rows whose Like and ⋯ are wholly inside the list, top first.
    func actable(_ f: Frame) -> [UInt32] {
        guard let l = listRect(f) else { return [] }
        let inside = { (r: Rect) in r.h > 0 && r.y >= l.y && r.y + r.h <= l.y + l.h }
        return rows(f).keys.sorted { rows(f)[$0]!.y < rows(f)[$1]!.y }.filter { k in
            guard let a = node(ControlRef(claim: 37, key: k), f), let m = node(ControlRef(claim: 52, key: k), f) else { return false }
            return inside(a.rect) && inside(m.rect)
        }
    }
    /// The status line's rollback, if it says one.
    func rollback(_ f: Frame) -> String? { texts(f).first { $0.hasPrefix("Couldn't ") } }

    /// Loaded images drawn (Draw.image appears once the host has the pixels).
    func images(_ f: Frame) -> Int { f.draws.filter { if case .image = $0 { true } else { false } }.count }
    /// Wheel ticks over the list: `dy` points each, toward the end when positive.
    func wheel(_ dy: Int32, _ times: Int) {
        guard let l = listRect(frame) else { fail("no feed list") }
        let p = Point(x: l.x + l.w / 2, y: l.y + l.h / 2)
        for _ in 0..<times { engine?.send([.pointerMove(p), .scroll(p, dx: 0, dy: dy)]); Thread.sleep(forTimeInterval: 0.01) }
    }

    /// A load-more or refresh in flight.
    func busy(_ f: Frame) -> Bool { texts(f).contains { $0.contains(" · loading more") || $0.contains(" · refreshing") } }

    /// The count on the Notifications tab: "Notifications · 4", nil without one (0).
    func unreadOf(_ f: Frame) -> Int? {
        guard let l = node(61, f)?.label else { return nil }
        return l == "Notifications" ? 0 : Int(l.dropFirst("Notifications · ".count))
    }

    func posts(_ f: Frame) -> Int? {
        for t in texts(f) {
            let digits = t.prefix { $0.isNumber }
            let rest = t.dropFirst(digits.count)
            if rest == " posts" || rest.hasPrefix(" posts ·"), let n = Int(digits) { return n }
        }
        return nil
    }

    /// Acting on posts with the fake's replies slowed (cairn#254): like, unlike, repost and follow
    /// shown at once and kept; a refused like rolled back with its line; a like whose reply is lost
    /// after the server made it, settled by a read and made once; a mute hiding an author's posts
    /// and reposts while the post being read stays put, and Undo bringing them back.
    func actsScenario(_ f: FakePDS) -> String {
        f.control("slow?ms=1200")
        let me = "@" + f.identifier
        var fr = until(5, "no post by someone else to act on") { f in
            self.actable(f).count >= 2 && self.actable(f).contains { self.authors(f)[$0] != me }
        }
        let ks = actable(fr)
        guard let k = ks.first(where: { authors(fr)[$0] != me && on(ControlRef(claim: 37, key: $0), fr) == false }) else { fail("no rows") }
        let like = ControlRef(claim: 37, key: k), repost = ControlRef(claim: 38, key: k)
        let records0 = f.records().count

        // Like: shown in the same frame, kept once the slow reply comes.
        guard on(like, fr) == false else { fail("\(like.label) starts liked") }
        click(like)
        until(1, "the like didn't show at once") { self.on(like, $0) == true }
        shot("like-pending")
        guard f.awaitRecords(records0 + 1) else { fail("the like wasn't made on the server") }
        Thread.sleep(forTimeInterval: 1.5)
        guard on(like) == true, rollback(frame) == nil else { fail("the like didn't hold once answered") }
        shot("liked")

        // Unlike, then repost.
        click(like)
        until(1, "the unlike didn't show at once") { self.on(like, $0) == false }
        guard f.awaitRecords(records0) else { fail("the unlike wasn't made on the server") }
        Thread.sleep(forTimeInterval: 1.5)
        guard on(like) == false else { fail("the unlike didn't hold") }
        click(repost)
        until(1, "the repost didn't show at once") { self.on(repost, $0) == true }
        guard f.awaitRecords(records0 + 1) else { fail("the repost wasn't made on the server") }
        Thread.sleep(forTimeInterval: 1.5)
        guard on(repost) == true else { fail("the repost didn't hold") }

        // Follow from the ⋯ menu: the menu then says Unfollow.
        // On a row wholly in view now: the unread poll's refresh may have put posts above.
        let ff = frame
        guard let kf = actable(ff).first(where: { authors(ff)[$0] != me }), let who = authors(ff)[kf] else {
            fail("no one else's post in view to follow")
        }
        let items = menu(kf)
        guard let follow = items.first(where: { $0.control?.claim == 39 }) else {
            fail("no Follow in \(who)'s menu: \(items.map(\.label))")
        }
        guard items.contains(where: { $0.control?.claim == 40 && $0.label == "Mute \(who)" }),
              items.contains(where: { $0.control?.claim == 53 }), items.contains(where: { $0.control?.claim == 54 }) else {
            fail("the post's menu is missing an item: \(items.map(\.label))")
        }
        let followed = follow.label == "Follow \(who)"
        choose(follow.control!)
        guard f.awaitRecords(records0 + (followed ? 2 : 0)) else { fail("the follow wasn't made on the server") }
        Thread.sleep(forTimeInterval: 1.5)
        let again = menu(kf)
        guard again.first(where: { $0.control?.claim == 39 })?.label == (followed ? "Unfollow " : "Follow ") + who else {
            fail("the menu doesn't show the follow: \(again.map(\.label))")
        }
        closeMenu()
        shot("followed")

        // A refused like: shown, then rolled back with its line, said aloud.
        let fl = frame
        guard let k2 = actable(fl).first(where: { $0 != k && on(ControlRef(claim: 37, key: $0), fl) == false }) else {
            fail("no unliked post in view")
        }
        let like2 = ControlRef(claim: 37, key: k2)
        f.control("fail?n=1&kind=400")
        click(like2)
        until(1, "the refused like didn't show at once") { self.on(like2, $0) == true }
        fr = until(5, "no rollback line") { self.on(like2, $0) == false && self.rollback($0) != nil }
        let line = rollback(fr) ?? ""
        guard line.hasPrefix("Couldn't like ") else { fail("the rollback says \(line)") }
        shot("like-refused")
        until(Double(10), "the rollback line didn't clear") { self.rollback($0) == nil }

        // A like whose reply is lost after the server made it: kept, settled by a read, made once.
        f.control("slow?ms=0")
        let records1 = f.records().count
        f.control("fail?n=1&kind=lost-after")
        click(like2)
        until(1, "the like didn't show at once") { self.on(like2, $0) == true }
        let end = Date().addingTimeInterval(45)
        while Date() < end, f.records().count == records1 { Thread.sleep(forTimeInterval: 0.2) }
        Thread.sleep(forTimeInterval: 35)
        guard on(like2) == true, rollback(frame) == nil else { fail("the lost like didn't settle as liked") }
        guard f.records().count == records1 + 1 else { fail("the lost like was made \(f.records().count - records1) times") }

        // Mute an author mid-feed: their posts and reposts are gone, the post being read stays put.
        // Down the feed until an author other than the reader's has two posts showing.
        var pick: (UInt32, String)?
        var reader: (key: UInt32, y: Int32) = (0, 0)
        var byAuthor: [UInt32: String] = [:]
        for _ in 0..<40 {
            wheel(40, 3)
            until(5, "the feed didn't settle") { self.firstShown($0) != nil && !self.busy($0) }
            Thread.sleep(forTimeInterval: 0.3)
            fr = frame
            guard let r = firstShown(fr) else { continue }
            reader = r
            byAuthor = authors(fr)
            let seen = byAuthor
            pick = actable(fr).compactMap({ k -> (UInt32, String)? in
                let top = topRow(fr).flatMap { rowAuthors(fr)[$0] }
            guard let a = seen[k], a != me, a != seen[r.key], a != top, seen.values.filter({ $0 == a }).count >= 2 else { return nil }
                return (k, a)
            }).first
            if pick != nil { break }
        }
        guard let (mk, muted) = pick else { fail("no author with two posts showing") }
        let mute = menu(mk).first { $0.control?.claim == 40 }
        guard let mute, mute.label == "Mute \(muted)" else { fail("no Mute \(muted) in the menu") }
        let shownBefore = authors(fr).values.filter { $0 == muted }.count
        shot("before-mute")
        choose(mute.control!)
        fr = until(2, "\(muted)'s posts still show") { !self.authors($0).values.contains(muted) }
        guard let still = firstShown(fr), still.key == reader.key, still.y == reader.y else {
            fail("the mute moved the reader: \(reader) → \(String(describing: firstShown(fr)))")
        }
        guard texts(fr).contains("Muted \(muted). Their posts are hidden.") else { fail("no Muted line") }
        guard !texts(fr).contains(where: { $0.hasPrefix("Reposted by ") && $0.hasSuffix(String(muted.dropFirst())) }) else {
            fail("a repost by \(muted) still shows")
        }
        shot("muted")
        Thread.sleep(forTimeInterval: 1.5)
        guard (f.state()["muted"] as? [Any])?.isEmpty == false else { fail("the mute wasn't made on the server") }

        // Undo (^58): the posts are back, the reader still where they were.
        click(58)
        fr = until(5, "Undo didn't bring \(muted)'s posts back") { self.authors($0).values.contains(muted) }
        guard let back = firstShown(fr), back.key == reader.key, back.y == reader.y else {
            fail("Undo moved the reader: \(reader) → \(String(describing: firstShown(fr)))")
        }
        let end2 = Date().addingTimeInterval(5)
        while Date() < end2, (f.state()["muted"] as? [Any])?.isEmpty == false { Thread.sleep(forTimeInterval: 0.1) }
        guard (f.state()["muted"] as? [Any])?.isEmpty == true else { fail("the unmute wasn't made on the server") }
        shot("unmuted")

        return "liked, unliked, reposted and followed with replies slowed; a refused like rolled back (\"\(line)\"); "
            + "a lost like settled by a read and made once; muting \(muted) hid their \(shownBefore) posts on screen with the reader kept, Undo brought them back"
    }

    /// A row's control menu (`owner`, e.g. a notification's ⋯ ^78#k), opened by a click.
    func menu(of owner: ControlRef) -> [MenuRecord] {
        click(owner)
        let end = Date().addingTimeInterval(2)
        while Date() < end {
            if let m = engine?.latest.flatMap({ openMenu(owner, $0.frame) }) { return m }
            Thread.sleep(forTimeInterval: 0.02)
        }
        fail("\(owner.label)'s menu didn't open")
    }
    /// The controls of claim `claim` in the frame, by key.
    func keyed(_ claim: UInt32, _ f: Frame) -> [UInt32: AxNode] {
        var out: [UInt32: AxNode] = [:]
        for n in f.ax { if let c = n.control, c.claim == claim { out[c.key] = n } }
        return out
    }
    /// The Go menu's Home (^73) and Notifications (^74): enabled, ⌘1 and ⌘2, which one checked.
    func goMenu(_ f: Frame) -> (home: Bool, notes: Bool)? {
        let m = menuBar(f)
        guard let go = m.firstIndex(where: { $0.place == 72 && $0.label == "Go" }),
              let h = m.first(where: { $0.control == ControlRef(claim: 73) }),
              let n = m.first(where: { $0.control == ControlRef(claim: 74) }),
              h.parent == go, n.parent == go, h.label == "Home", n.label == "Notifications",
              h.enabled, n.enabled, let hc = h.checked, let nc = n.checked else { return nil }
        return (hc, nc)
    }

    /// Notifications on screen (cairn#255): others act while the reader is on Home, so the tab's
    /// count and the Dock badge rise, said aloud; Go ▸ Notifications (⌘2) opens the list, which
    /// is marked seen, the count and badge going to 0; Follow back from a follow row; a like from
    /// a reply's or mention's row; muting its author takes their rows away; Go ▸ Home (⌘1) is
    /// back where the reader was.
    func notesScenario(_ f: FakePDS) -> String {
        f.control("slow?ms=0")
        // On Home, partway down the feed.
        click(62)
        wheel(-200, 30)
        wheel(40, 8)
        var fr = until(5, "the feed didn't settle") { self.firstShown($0) != nil && !self.busy($0) }
        guard let g0 = goMenu(fr), g0.home, !g0.notes else { fail("no Go menu with Home checked: \(menuBar(fr).map(\.label))") }
        let unread0 = unreadOf(fr) ?? 0
        let said0 = heard.announced.count
        // A repost between the follow and any older one, so the follow is a row of its own.
        f.control("act?kind=repost&actor=5")
        f.control("act?kind=follow&actor=1")
        for a in 1...4 { f.control("act?kind=like&actor=\(a)") }
        f.control("catchup")
        // The count is polled each minute (the clock's tick).
        fr = until(70, "the unread count didn't rise on the Notifications tab from \(unread0)") { (self.unreadOf($0) ?? 0) > unread0 && !self.busy($0) }
        let unread = unreadOf(fr) ?? 0
        until(2, "the Dock badge isn't the tab's count") { f in self.heard.badge == .some(String(self.unreadOf(f) ?? -1)) }
        guard heard.announced.count > said0, heard.announced.last?.hasSuffix("unread notifications") == true else {
            fail("the rise wasn't said: \(heard.announced.suffix(2))")
        }
        Thread.sleep(forTimeInterval: 0.3)
        fr = until(5, "the feed didn't settle") { self.firstShown($0) != nil && !self.busy($0) }
        guard let home = firstShown(fr) else { fail("no first row on Home") }
        shot("notes-unread")

        // Go ▸ Notifications (⌘2): the list, marked seen once on screen; the count and the badge go
        // to 0 (others keep acting between requests, so new ones may come in after).
        let sent0 = heard.sent.count
        engine?.send([.menuSelect(place: 48, ControlRef(claim: 74))])
        fr = until(10, "no notification rows") { f in !self.keyed(66, f).isEmpty }
        guard let g1 = goMenu(fr), !g1.home, g1.notes else { fail("Go ▸ Notifications isn't checked once shown") }
        until(10, "the seen time never reached the server") { _ in f.state()["seenAt"] != nil }
        until(10, "the Dock badge and the tab's count didn't go to 0 once the notifications were seen") { _ in
            self.heard.sent.dropFirst(sent0).contains { $0 == nil }
        }
        shot("notes-seen")

        // Follow back from a follow row.
        let records0 = f.records().count
        fr = frame
        guard let (fk, fb) = keyed(83, fr).first(where: { $0.value.label.hasPrefix("Follow back @") }) else {
            fail("no Follow back on a follow row: \(keyed(83, fr).values.map(\.label))")
        }
        let who = String(fb.label.dropFirst("Follow back ".count))
        click(ControlRef(claim: 83, key: fk))
        until(2, "Follow back didn't show at once") { self.node(ControlRef(claim: 83, key: fk), $0)?.label == "Following " + who }
        guard f.awaitRecords(records0 + 1) else { fail("the follow back wasn't made on the server") }
        shot("notes-followed-back")

        // A reply or mention: posts arrive until one notifies, then its Like.
        var lk: UInt32?
        for _ in 0..<20 {
            fr = frame
            if let l = listRect(fr), let k = keyed(76, fr).filter({ k, n in
                !n.selected && n.rect.h > 0 && n.rect.y >= l.y && n.rect.y + n.rect.h <= l.y + l.h
                    && self.node(ControlRef(claim: 78, key: k), fr).map { $0.rect.y + $0.rect.h <= l.y + l.h } == true
            }).min(by: { $0.value.rect.y < $1.value.rect.y })?.key { lk = k; break }
            f.control("post?n=4")
            click(63)
            until(10, "the notifications didn't refresh") { !self.busy($0) }
            Thread.sleep(forTimeInterval: 0.5)
        }
        guard let lk else { fail("no reply or mention row to like") }
        let like = ControlRef(claim: 76, key: lk)
        let records1 = f.records().count
        click(like)
        until(1, "the like didn't show at once") { self.on(like, $0) == true }
        guard f.awaitRecords(records1 + 1) else { fail("the like from the notification wasn't made on the server") }
        shot("notes-liked")

        // Mute its author from the row's ⋯: their rows go.
        let more = ControlRef(claim: 78, key: lk)
        guard let ml = node(more)?.label, ml.hasPrefix("More for @"), ml.hasSuffix("'s post") else { fail("no ⋯ on the liked row") }
        let muted = String(ml.dropFirst("More for ".count).dropLast("'s post".count))
        let items = menu(of: more)
        guard let mute = items.first(where: { $0.control == ControlRef(claim: 80, key: lk) }), mute.label == "Mute \(muted)",
              items.contains(where: { $0.control == ControlRef(claim: 81, key: lk) }),
              items.contains(where: { $0.control == ControlRef(claim: 82, key: lk) }) else {
            fail("the notification's menu is missing an item: \(items.map(\.label))")
        }
        choose(mute.control!)
        fr = until(3, "\(muted)'s notifications still show") { f in
            self.node(ControlRef(claim: 66, key: lk), f) == nil && !self.keyed(78, f).values.contains { $0.label == "More for \(muted)'s post" }
        }
        let end = Date().addingTimeInterval(5)
        while Date() < end, (f.state()["muted"] as? [Any])?.isEmpty != false { Thread.sleep(forTimeInterval: 0.1) }
        guard (f.state()["muted"] as? [Any])?.isEmpty == false else { fail("the mute wasn't made on the server") }
        shot("notes-muted")

        // Go ▸ Home (⌘1): where the reader was.
        engine?.send([.menuSelect(place: 48, ControlRef(claim: 73))])
        fr = until(5, "Home didn't show") { self.firstShown($0) != nil && self.goMenu($0)?.home == true }
        guard let back = firstShown(fr), back.key == home.key, back.y == home.y else {
            fail("Home moved while Notifications showed: \(home) → \(String(describing: firstShown(fr)))")
        }
        shot("notes-home-again")
        return "\(unread) unread on the tab and the Dock badge on Home, said aloud; Go ▸ Notifications marked them seen, "
            + "the count and badge to 0; followed back \(who); liked a reply's post from its row; muting \(muted) took their rows away; "
            + "Go ▸ Home back at the same row and y"
    }

    func run() {
        // Files go to the scratch home, never the real one.
        guard ProcessInfo.processInfo.environment["CFFIXED_USER_HOME"] != nil else {
            fail("run through `make selftest` (CFFIXED_USER_HOME unset)")
        }
        let account = NSHomeDirectory() + "/Library/Application Support/dev.cairn.sky/account.json"
        guard let f = FakePDS(script) else { fail("the fake PDS didn't start (bun \(script))") }
        fake = f
        let me = "@" + f.identifier

        // Launch: the sign-in screen, the service filled in from the default, Sign in greyed.
        let heard = heard
        launch(f.service, onPublish: { heard.take($0) })
        until(5, "no sign-in screen") { self.node(6, $0) != nil && self.node(8, $0)?.value == f.service }
        guard node(10) == nil, node(12) == nil else { fail("Sign in or Cancel offered on an empty form") }
        guard node(7)?.secure == true else { fail("the app password field isn't secure") }
        guard let so0 = signOutItem(frame), so0.label == "Sign Out", !so0.enabled else {
            fail("Sign Out isn't in the app menu, greyed, while signed out: \(menuBar(frame).map(\.label))")
        }
        shot("sign-in")

        // A wrong password: said in words, the field emptied.
        type(6, f.identifier)
        engine?.send([.key(.enter, Mods())])
        until(2, "Enter didn't move to the password") { self.node(7, $0)?.focused == true }
        engine?.send([.insertText("wrong-pass-word-0000")])
        until(2, "Sign in not offered once both fields are typed in") { self.node(10, $0) != nil }
        guard node(7)?.value == "" else { fail("the password field shows its text") }
        shot("sign-in-typed")
        click(10)
        until(5, "no word of the wrong password") { self.shows("Wrong handle, email or app password.", $0) }
        guard node(10) == nil else { fail("the password wasn't cleared") }
        shot("sign-in-wrong-password")

        // Rate limited.
        f.control("fail?n=1&kind=429")
        type(7, f.password)
        click(10)
        until(5, "no word of the rate limit") { self.shows("Too many tries. Wait a few minutes, then try again.", $0) }
        shot("sign-in-rate-limited")

        // Offline: a service nothing answers at.
        type(8, "http://127.0.0.1:9")
        type(7, f.password)
        click(10)
        until(10, "no word of being offline") { self.shows("You're offline, or the service can't be reached.", $0) }
        shot("sign-in-offline")
        type(8, f.service)

        // Slow: "Signing in…", then Cancel offered after a few seconds.
        f.control("slow?ms=4500")
        type(7, f.password)
        click(10)
        until(2, "no Signing in…") { self.shows("Signing in…", $0) }
        shot("sign-in-busy")
        until(5, "Cancel not offered on a slow sign-in") { self.node(12, $0) != nil }
        shot("sign-in-slow")
        f.control("slow?ms=0")

        // Signed in: who, the feed, both tokens in the Keychain, the account saved.
        var fr = until(15, "not signed in") { self.shows(me, $0) && (self.posts($0) ?? 0) > 0 && !self.rows($0).isEmpty }
        guard store.held.count == 2 else { fail("\(store.held.count) Keychain items after sign-in, not 2") }
        guard FileManager.default.fileExists(atPath: account) else { fail("the account wasn't saved") }
        let first = posts(fr) ?? 0
        guard let top0 = firstShown(fr), top0.key == rows(fr).keys.min() else { fail("the feed doesn't open at its first post") }

        // Images: avatars and embeds load from the fake into their placeholders.
        fr = until(10, "no image drawn") { self.images($0) > 0 }
        shot("feed")

        // Scrolling: wheel ticks move the list; the top row changes.
        wheel(40, 12)
        fr = until(5, "the wheel didn't scroll the feed") { (self.firstShown($0)?.key ?? 0) != top0.key }
        until(10, "no image drawn after scrolling") { self.images($0) > 0 }
        shot("feed-scrolled")

        // Load more: scrolling to the list's end shows its Loading… row, whose appear loads more.
        var guardTicks = 0
        while (posts(frame) ?? 0) <= first {
            guardTicks += 1
            if guardTicks > 200 { fail("scrolling to the end didn't load more (\(posts(frame) ?? 0) posts)") }
            wheel(600, 1)
            Thread.sleep(forTimeInterval: 0.03)
        }
        fr = until(10, "Load more didn't finish") { (self.posts($0) ?? 0) > first && !self.busy($0) }
        let more = posts(fr) ?? 0
        shot("feed-more")

        // Refresh with posts arriving at the head: the reader doesn't move, "3 new posts" offered.
        wheel(-200, 30)
        wheel(300, 1)
        fr = until(5, "the feed didn't settle") { self.firstShown($0) != nil && !self.busy($0) }
        Thread.sleep(forTimeInterval: 0.2)
        guard let before = firstShown(frame) else { fail("no first row") }
        f.control("post?n=3")
        click(4)
        fr = until(10, "Refresh didn't bring the new posts (\(more) before)") { (self.posts($0) ?? 0) >= more + 3 && !self.busy($0) && self.node(33, $0) != nil }
        let refreshed = posts(fr) ?? 0
        guard let after = firstShown(fr), after.key == before.key, after.y == before.y else {
            fail("Refresh moved the reader: \(before) → \(String(describing: firstShown(fr)))")
        }
        guard node(33, fr)?.label == "3 new posts" else { fail("no \"3 new posts\": \(node(33, fr)?.label ?? "-")") }
        shot("feed-new-posts")

        // "3 new posts": the list starts again at its first post, the newest.
        click(33)
        fr = until(5, "\"3 new posts\" didn't go to the top") { self.node(33, $0) == nil && self.firstShown($0) != nil }
        guard let newest = firstShown(fr), newest.key == rows(fr).keys.min() else { fail("not at the newest post") }
        until(10, "no image drawn at the top") { self.images($0) > 0 }
        shot("feed-top")

        let acts = actsScenario(f)
        let notes = notesScenario(f)

        // Quit and launch again: the session resumes from the Keychain, nothing typed.
        engine?.stop()
        launch(f.service)
        until(15, "the session didn't resume") { self.shows(me, $0) && (self.posts($0) ?? 0) > 0 }
        shot("resumed")

        // Sign Out from the app menu (^49): both items forgotten, the account file gone.
        guard let so = signOutItem(frame), so.enabled else { fail("Sign Out not offered in the app menu while signed in") }
        engine?.send([.menuSelect(place: 48, ControlRef(claim: 49))])
        let out = until(5, "not signed out") { self.node(6, $0) != nil }
        guard signOutItem(out)?.enabled == false else { fail("Sign Out still offered once signed out") }
        let end = Date().addingTimeInterval(5)
        while Date() < end, !store.held.isEmpty || FileManager.default.fileExists(atPath: account) {
            Thread.sleep(forTimeInterval: 0.05)
        }
        guard store.held.isEmpty else { fail("\(store.held.count) Keychain items left after Sign out") }
        guard !FileManager.default.fileExists(atPath: account) else { fail("the account file outlived Sign out") }
        let items = store.accounts.count

        clean()
        print("selftest: PASS (Sky against the fake PDS: wrong password, rate limit, offline and slow sign-ins in words; "
              + "signed in by typing; images drawn; scrolled; \(first) → \(more) posts by scrolling to the end, \(refreshed) by Refresh with the reader kept and 3 new posts offered; "
              + "\(acts); \(notes); resumed; Sign Out from the app menu forgot \(items) Keychain items and the account)")
    }
}
