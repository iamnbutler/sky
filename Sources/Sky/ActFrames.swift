import CairnFrame
import CairnHost
import CairnRender
import Foundation

// `Sky --act-frames <server.ts> <dir>`: acting on posts against cairn_atproto's fake PDS, its
// replies slowed, rendered offscreen at 30 frames a second (cairn#254's media). Two runs of
// numbered PNGs, which ffmpeg turns into videos:
//   <dir>/like/    a like that the server confirms, a repost, then a like it refuses, rolled
//                  back with its line in the status row
//   <dir>/mute/    mid-feed, ⋯ on a post, Mute: the author's posts go and the post being read
//                  stays put; then Undo brings them back
// The ⋯ menu is AppKit's own, which the offscreen renderer doesn't draw: the ⋯ button shows
// pressed while it is open, and the item is chosen as the host chooses it (`menuSelect`).
// Like the selftest it signs in by typing, under a throwaway Keychain service and a scratch home.

/// The frames the engine shows, sampled 30 times a second, rendered once the run is over (so
/// rendering never slows the sampling).
final class Recorder: @unchecked Sendable {
    private let engine: Engine
    private let lock = NSLock()
    private var frames: [Frame] = []
    private var running = false
    private var thread: Thread?

    init(_ engine: Engine) { self.engine = engine }

    func start() {
        lock.withLock { running = true; frames = [] }
        let t = Thread { [self] in
            let start = Date()
            var i = 0
            while lock.withLock({ running }) {
                let due = start.addingTimeInterval(Double(i) / 30)
                let wait = due.timeIntervalSinceNow
                if wait > 0 { Thread.sleep(forTimeInterval: wait) }
                if let f = engine.latest?.frame { lock.withLock { frames.append(f) } }
                i += 1
            }
        }
        thread = t
        t.start()
    }

    /// Stops sampling and writes the frames as `0000.png`… under `dir`; returns how many.
    func stop(into dir: URL, _ renderer: Renderer) throws -> Int {
        lock.withLock { running = false }
        Thread.sleep(forTimeInterval: 0.1)
        let fs = lock.withLock { frames }
        try FileManager.default.createDirectory(at: dir, withIntermediateDirectories: true)
        for (i, f) in fs.enumerated() {
            try renderer.image(f, scale: 2).writePNG(to: dir.appendingPathComponent(String(format: "%04d.png", i)))
        }
        return fs.count
    }
}

final class ActFrames {
    let t: Selftest
    let out: URL

    init(server: String, dir: String) {
        t = Selftest(server: server, shots: nil)
        out = URL(fileURLWithPath: dir, isDirectory: true)
    }

    func hold(_ s: Double) { Thread.sleep(forTimeInterval: s) }

    func run() {
        guard ProcessInfo.processInfo.environment["CFFIXED_USER_HOME"] != nil else {
            t.fail("run through `make act-frames` (CFFIXED_USER_HOME unset)")
        }
        guard let f = FakePDS(t.script, ["--act", "0"]) else { t.fail("the fake PDS didn't start") }
        t.fake = f
        guard let renderer = try? Renderer() else { t.fail("no renderer") }
        let me = "@" + f.identifier

        // Sign in by typing, then wait for the feed and its images.
        t.launch(f.service)
        t.until(5, "no sign-in screen") { self.t.node(6, $0) != nil }
        t.type(6, f.identifier)
        t.type(7, f.password)
        t.click(10)
        t.until(15, "not signed in") { self.t.shows(me, $0) && !self.t.rows($0).isEmpty }
        t.until(10, "no images") { self.t.images($0) > 0 }
        hold(1.5)
        guard let engine = t.engine else { t.fail("no engine") }

        // 1. Like (confirmed), repost (confirmed), like refused and rolled back.
        f.control("slow?ms=1400")
        let fr = t.frame
        let ks = t.actable(fr)
        guard let k = ks.first(where: { t.authors(fr)[$0] != me && t.on(ControlRef(claim: 37, key: $0), fr) == false }),
              let k2 = ks.first(where: { $0 != k && t.on(ControlRef(claim: 37, key: $0), fr) == false }) else {
            t.fail("no posts to like")
        }
        let rec = Recorder(engine)
        rec.start()
        hold(1.2)
        t.click(ControlRef(claim: 37, key: k))
        hold(2.6)
        t.click(ControlRef(claim: 38, key: k))
        hold(2.6)
        f.control("fail?n=1&kind=400")
        t.click(ControlRef(claim: 37, key: k2))
        t.until(5, "no rollback") { self.t.rollback($0) != nil }
        hold(3.5)
        let n1 = (try? rec.stop(into: out.appendingPathComponent("like"), renderer)) ?? 0
        f.control("slow?ms=0")
        t.until(10, "the line didn't clear") { self.t.rollback($0) == nil }

        // 2. Mute mid-feed: scroll, then ⋯ → Mute on the author with the most posts showing.
        // Down the feed until an author other than the reader's has two posts showing.
        var pick: (UInt32, String)?
        var fm = t.frame
        var byAuthor: [UInt32: String] = [:]
        var reader: (key: UInt32, y: Int32)?
        for _ in 0..<40 {
            t.wheel(40, 3)
            t.until(5, "the feed didn't settle") { self.t.firstShown($0) != nil && !self.t.busy($0) }
            hold(0.3)
            fm = t.frame
            guard let r = t.firstShown(fm) else { continue }
            reader = r
            byAuthor = t.authors(fm)
            let seen = byAuthor
            pick = t.actable(fm).compactMap({ k -> (UInt32, String)? in
                let top = t.topRow(fm).flatMap { t.rowAuthors(fm)[$0] }
                guard let a = seen[k], a != me, a != seen[r.key], a != top, seen.values.filter({ $0 == a }).count >= 2 else { return nil }
                return (k, a)
            }).first
            if pick != nil { break }
        }
        guard let (mk, who) = pick, reader != nil else { t.fail("no author with two posts showing") }
        let count = { (a: String) in byAuthor.values.filter { $0 == a }.count }
        hold(0.7)
        f.control("slow?ms=900")
        rec.start()
        hold(1.2)
        let items = t.menu(mk)
        hold(1.2)
        guard let mute = items.first(where: { $0.control?.claim == 40 }) else { t.fail("no Mute in the menu") }
        t.choose(mute.control!)
        t.until(2, "\(who)'s posts still show") { !self.t.authors($0).values.contains(who) }
        hold(3)
        t.click(58)
        t.until(5, "Undo didn't bring them back") { self.t.authors($0).values.contains(who) }
        hold(2.5)
        let n2 = (try? rec.stop(into: out.appendingPathComponent("mute"), renderer)) ?? 0

        t.clean()
        print("act-frames: \(n1) frames in \(out.path)/like, \(n2) in \(out.path)/mute (muted \(who), \(count(who)) posts on screen)")
    }
}
