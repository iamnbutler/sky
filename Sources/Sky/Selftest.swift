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

/// The fake PDS, run with Bun on a free port of 127.0.0.1.
final class FakePDS {
    let process = Process()
    let service: String
    let identifier: String
    let password: String

    init?(_ script: String) {
        let out = Pipe()
        process.executableURL = URL(fileURLWithPath: "/usr/bin/env")
        process.arguments = ["bun", script, "--port", "0", "--quiet", "--seed", "20261025"]
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

/// The Keychain under a throwaway service, remembering every item it wrote. Calls go one at a
/// time: the file-based keychain deadlocks a read racing a delete (cairn#237).
final class ThrowawayKeychain: SecretStore, @unchecked Sendable {
    let keychain = KeychainStore(service: "cairn.sky-selftest-" + UUID().uuidString)
    private let lock = NSLock()
    private let calls = NSLock()
    private var written: Set<String> = []

    func read(_ account: String) -> Result<String?, ReplyError> { calls.withLock { keychain.read(account) } }
    func write(_ account: String, _ value: String) -> Result<Void, ReplyError> {
        lock.withLock { _ = written.insert(account) }
        return calls.withLock { keychain.write(account, value) }
    }
    func delete(_ account: String) -> Result<Void, ReplyError> { calls.withLock { keychain.delete(account) } }

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
    /// Keychain, loopback only.
    func launch(_ service: String) {
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
        let e = Engine(size: size, scalePercent: 200, world: World(handlers: h, devices: devices)) { LeanCore(app) }
        engine = e
        e.start()
        guard e.wait(through: 0) != nil else { fail("no first frame") }
    }

    /// The feed's list: the largest clip the frame pushes.
    func listRect(_ f: Frame) -> Rect? {
        var best: Rect?
        for d in f.draws { if case let .pushClip(r) = d, r.w >= 300, r.h >= 300, r.h > (best?.h ?? 0) { best = r } }
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

    func posts(_ f: Frame) -> Int? {
        for t in texts(f) {
            let digits = t.prefix { $0.isNumber }
            let rest = t.dropFirst(digits.count)
            if rest == " posts" || rest.hasPrefix(" posts ·"), let n = Int(digits) { return n }
        }
        return nil
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
        launch(f.service)
        until(5, "no sign-in screen") { self.node(6, $0) != nil && self.node(8, $0)?.value == f.service }
        guard node(10) == nil, node(12) == nil else { fail("Sign in or Cancel offered on an empty form") }
        guard node(7)?.secure == true else { fail("the app password field isn't secure") }
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

        // Quit and launch again: the session resumes from the Keychain, nothing typed.
        engine?.stop()
        launch(f.service)
        until(15, "the session didn't resume") { self.shows(me, $0) && (self.posts($0) ?? 0) > 0 }
        shot("resumed")

        // Sign out from the account panel: both items forgotten, the account file gone.
        click(13)
        until(2, "no account panel") { self.node(11, $0) != nil }
        shot("account")
        click(11)
        until(5, "not signed out") { self.node(6, $0) != nil }
        let end = Date().addingTimeInterval(5)
        while Date() < end, !store.held.isEmpty || FileManager.default.fileExists(atPath: account) {
            Thread.sleep(forTimeInterval: 0.05)
        }
        guard store.held.isEmpty else { fail("\(store.held.count) Keychain items left after Sign out") }
        guard !FileManager.default.fileExists(atPath: account) else { fail("the account file outlived Sign out") }
        let items = store.accounts.count

        clean()
        print("selftest: PASS (Sky against the fake PDS: wrong password, rate limit, offline and slow sign-ins in words; "
              + "signed in by typing; images drawn; scrolled; \(first) → \(more) posts by scrolling to the end, \(refreshed) by Refresh with the reader kept and 3 new posts offered; resumed; "
              + "Sign out forgot \(items) Keychain items and the account)")
    }
}
