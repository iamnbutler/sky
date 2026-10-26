import CLean
import CairnFrame
import CairnHost
import CairnRender
import Darwin
import Foundation
import Metal

// `Sky --bench [server.ts]` (`make bench`, bench/README.md): Sky against cairn_atproto's fake PDS
// with 1,000 posts, through Cairn's `Engine` and the host's real world, as the selftest drives
// it (Selftest.swift: loopback only, a scratch home, a throwaway Keychain service, the server
// stopped at the end), with a render thread painting every new frame offscreen with Metal, as
// the window's would. No window, no screen.
//
//   sign-in → first page painted, and refresh → new posts painted, with 0 and 100 ms added to
//   every XRPC reply (`/control/slow`)
//   flings down through all 1,000 posts and back: each frame's Lean step, encode, Swift decode
//   and Metal render, and input → frame
//   memory (the process's physical footprint) and the image store against Sky's budget

/// `LeanCore` with a clock: each batch's step (`cairn_app_step`: update, view, layout and
/// settle for every event), encode (`cairn_app_frame`) and decode, while `recording`.
final class TimedCore: AppCore, @unchecked Sendable {
    struct Sample { var step = 0.0, encode = 0.0, decode = 0.0, bytes = 0, batch = "" }
    private let lean: LeanApp
    private var state: OpaquePointer?
    private var stepMs = 0.0
    private var batch: [Event] = []
    private let lock = NSLock()
    private var kept: [Sample] = []
    private var on = false

    init(_ app: LeanApp) { lean = app }

    var recording: Bool {
        get { lock.withLock { on } }
        set { lock.withLock { on = newValue; if newValue { kept = [] } } }
    }
    var samples: [Sample] { lock.withLock { kept } }

    func start(size: Size, scalePercent: UInt32) {
        if let old = state { cairn_lean_dec(old) } else { LeanRuntime.enter(module: lean.module) }
        state = lean.initialize(UInt32(max(0, size.w)), UInt32(max(0, size.h)), scalePercent)
    }

    func step(_ events: [Event]) {
        guard let s = state else { return }
        let bytes = LeanRuntime.bytes(lean.codec.encode(events))
        let t0 = hostNow()
        state = lean.step(s, bytes)
        stepMs = (hostNow() - t0) * 1000
        batch = events
    }

    func frame() throws -> Frame {
        guard let s = state else { throw CodecError.noState }
        cairn_lean_inc(s)
        let t0 = hostNow()
        let o = lean.frame(s)
        let t1 = hostNow()
        var n = 0
        let f = try LeanRuntime.withBytes(o) { b in n = b.count; return try lean.codec.decodeFrame(b) }
        let t2 = hostNow()
        var x = Sample(step: stepMs, encode: (t1 - t0) * 1000, decode: (t2 - t1) * 1000, bytes: n)
        if stepMs > 8 { x.batch = Self.describe(batch) }
        lock.withLock { if on { kept.append(x) } }
        return f
    }

    /// A batch's events by kind: "scroll×3 reply×2".
    static func describe(_ es: [Event]) -> String {
        var counts: [(String, Int)] = []
        for e in es {
            var k = String("\(e)".prefix { $0 != "(" })
            if case let .reply(_, r) = e { k += "." + String("\(r)".prefix { $0 != "(" }) }
            if let i = counts.firstIndex(where: { $0.0 == k }) { counts[i].1 += 1 } else { counts.append((k, 1)) }
        }
        return counts.map { "\($0.0)×\($0.1)" }.joined(separator: " ")
    }

    deinit { if let s = state { cairn_lean_dec(s) } }
}

/// The render thread: paints the engine's latest frame whenever it changes, offscreen at 2×,
/// waiting for the GPU each time, as the window's display link would. It times each paint and
/// notes when a frame `watch` accepts is first painted.
final class Painter: @unchecked Sendable {
    private let lock = NSLock()
    private var running = true
    private var times: [Double] = []
    private var watch: ((Frame) -> Bool)?
    private var hit: Double?
    private var published: Double?
    weak var engine: Engine?

    func start() {
        let t = Thread { [self] in loop() }
        t.name = "sky.bench.render"
        t.qualityOfService = .userInteractive
        t.start()
    }
    func stop() { lock.withLock { running = false } }

    /// Waits for frames `ok` accepts: when the engine first published one, and when it was
    /// first painted (`hostNow()` base).
    func arm(_ ok: @escaping (Frame) -> Bool) { lock.withLock { watch = ok; hit = nil; published = nil } }
    var painted: Double? { lock.withLock { hit } }
    var publishedAt: Double? { lock.withLock { published } }
    /// Called on the Lean thread for each frame published.
    func heard(_ p: CairnHost.Published) {
        let w = lock.withLock { published == nil ? watch : nil }
        if let w, w(p.frame) { let t = hostNow(); lock.withLock { if published == nil { published = t } } }
    }
    func reset() { lock.withLock { times = [] } }
    var renders: [Double] { lock.withLock { times } }

    private func loop() {
        guard let r = try? Renderer() else { return }
        let d = MTLTextureDescriptor.texture2DDescriptor(pixelFormat: .bgra8Unorm, width: Int(size.w) * 2, height: Int(size.h) * 2, mipmapped: false)
        d.usage = [.renderTarget, .shaderRead]
        d.storageMode = .private
        let tex = r.device.makeTexture(descriptor: d)!
        var last = -1
        while lock.withLock({ running }) {
            guard let p = engine?.latest, p.version != last else { usleep(500); continue }
            last = p.version
            let t0 = hostNow()
            r.draw(frame: p.frame, into: tex, scale: 2).waitUntilCompleted()
            let t1 = hostNow()
            lock.withLock {
                times.append((t1 - t0) * 1000)
                if hit == nil, let w = watch, w(p.frame) { hit = t1 }
            }
        }
    }
}

/// The process's physical footprint (what Activity Monitor calls Memory), in bytes.
func footprint() -> Int {
    var info = task_vm_info_data_t()
    var count = mach_msg_type_number_t(MemoryLayout<task_vm_info_data_t>.size / MemoryLayout<natural_t>.size)
    let kr = withUnsafeMutablePointer(to: &info) {
        $0.withMemoryRebound(to: integer_t.self, capacity: Int(count)) { task_info(mach_task_self_, task_flavor_t(TASK_VM_INFO), $0, &count) }
    }
    return kr == KERN_SUCCESS ? Int(info.phys_footprint) : -1
}

/// Where the footprint is: malloc's bytes in use, and what the Metal device has allocated
/// (textures and buffers, the image textures among them).
func breakdown() -> String {
    var st = malloc_statistics_t()
    malloc_zone_statistics(nil, &st)
    let metal = MTLCreateSystemDefaultDevice()?.currentAllocatedSize ?? 0
    var info = task_vm_info_data_t()
    var count = mach_msg_type_number_t(MemoryLayout<task_vm_info_data_t>.size / MemoryLayout<natural_t>.size)
    _ = withUnsafeMutablePointer(to: &info) {
        $0.withMemoryRebound(to: integer_t.self, capacity: Int(count)) { task_info(mach_task_self_, task_flavor_t(TASK_VM_INFO), $0, &count) }
    }
    return "footprint \(mb(footprint())): malloc in use \(mb(Int(st.size_in_use))), Metal allocated \(mb(metal)), internal \(mb(Int(info.internal))) (malloc and Lean's heap), graphics \(mb(Int(info.ledger_tag_graphics_footprint))), purgeable \(mb(Int(info.ledger_purgeable_nonvolatile))), media \(mb(Int(info.ledger_tag_media_footprint))), compressed \(mb(Int(info.compressed)))"
}

func pct(_ xs: [Double], _ q: Double) -> Double {
    guard !xs.isEmpty else { return .nan }
    let s = xs.sorted()
    return s[min(s.count - 1, Int((Double(s.count - 1) * q).rounded()))]
}
func ms(_ x: Double) -> String { String(format: "%.2f", x) }
func summary(_ xs: [Double]) -> String { "p50 \(ms(pct(xs, 0.5))), p95 \(ms(pct(xs, 0.95))), max \(ms(pct(xs, 1))) ms" }
func mb(_ b: Int) -> String { String(format: "%.1f MB", Double(b) / 1_000_000) }

/// A trackpad fling's wheel deltas, one per frame at 120 Hz: 120 points, falling by 4% a frame
/// until under one point (117 frames, about 2,900 points), as Cairn's bench (bench/vlist.md).
let flingDeltas: [Int32] = {
    var v = 120_000, out: [Int32] = []
    while v >= 1000 { out.append(Int32(v / 1000)); v = v * 96 / 100 }
    return out
}()

final class Bench {
    let t: Selftest
    let core = TimedCore(app)
    let painter = Painter()
    let runs = 10

    init(server: String) { t = Selftest(server: server, shots: nil) }

    func caughtUp(_ f: Frame) -> Bool { t.shows("You're all caught up.", f) }

    /// Clicks `claim` and waits for a frame `ok` accepts to be painted: ms from the click to
    /// the frame published, and to it painted.
    func timed(_ claim: UInt32, _ what: String, _ ok: @escaping (Frame) -> Bool) -> (Double, Double) {
        guard let n = t.node(claim, t.until(2, "no control ^\(claim)") { self.t.node(claim, $0) != nil }) else { t.fail("no ^\(claim)") }
        let p = Point(x: n.rect.x + n.rect.w / 2, y: n.rect.y + n.rect.h / 2)
        painter.arm(ok)
        let t0 = hostNow()
        t.engine?.send([.pointerMove(p), .pointerDown(p, .primary, clicks: 1, Mods()), .pointerUp(p, .primary, Mods())], time: t0)
        let end = Date().addingTimeInterval(15)
        while painter.painted == nil, Date() < end { usleep(200) }
        guard let painted = painter.painted, let published = painter.publishedAt else { t.fail("\(what): not painted") }
        return ((published - t0) * 1000, (painted - t0) * 1000)
    }

    func signIn(_ f: FakePDS) -> (Double, Double) {
        t.type(6, f.identifier)
        t.type(7, f.password)
        t.until(2, "Sign in not offered") { self.t.node(10, $0) != nil }
        return timed(10, "sign-in") { !self.t.rows($0).isEmpty && (self.t.posts($0) ?? 0) > 0 }
    }

    func signOut() {
        t.engine?.send([.menuSelect(place: 48, ControlRef(claim: 49))])  // Sky ▸ Sign Out
        t.until(5, "not signed out") { self.t.node(6, $0) != nil }
        let end = Date().addingTimeInterval(5)
        while Date() < end, !t.store.held.isEmpty { usleep(20_000) }
    }

    /// The flings: `flingDeltas` at 120 Hz, `dir` 1 down or -1 up, until the first post shown
    /// stops changing over a whole fling (or `max` flings). Returns how many.
    func fling(_ dir: Int32, max: Int) -> Int {
        guard let l = t.listRect(t.frame) else { t.fail("no feed list") }
        let p = Point(x: l.x + l.w / 2, y: l.y + l.h / 2)
        t.engine?.send([.pointerMove(p)])
        var n = 0
        var top = t.firstShown(t.frame)?.key
        var next = hostNow()
        while n < max {
            for d in flingDeltas {
                next += 1.0 / 120
                t.engine?.send([.scroll(p, dx: 0, dy: dir * d)])
                let wait = next - hostNow()
                if wait > 0 { usleep(UInt32(wait * 1_000_000)) }
            }
            n += 1
            usleep(30_000)
            let now = t.firstShown(t.frame)?.key
            if now == top { break }
            top = now
        }
        return n
    }

    func report(_ label: String) {
        let s = core.samples
        let r = painter.renders
        let lean = s.map { $0.step + $0.encode + $0.decode }
        print("  \(label): \(s.count) frames published, \(r.count) painted")
        print("    Lean thread (step + encode + decode): \(summary(lean))")
        print("      step (update, view, layout, settle): \(summary(s.map(\.step)))")
        print("      encode: \(summary(s.map(\.encode))); decode: \(summary(s.map(\.decode))); frame \(Int(pct(s.map { Double($0.bytes) }, 0.5))) bytes (p50)")
        print("    render (Metal, offscreen, 2×, waited): \(summary(r))")
        print("    over 8 ms: Lean \(lean.filter { $0 > 8 }.count), render \(r.filter { $0 > 8 }.count)")
        var kinds: [String: Int] = [:]
        for x in s where x.step > 8 { kinds[x.batch, default: 0] += 1 }
        for (k, n) in kinds.sorted(by: { $0.value > $1.value }) { print("      step over 8 ms ×\(n): \(k)") }
        print("    input → frame: \(t.engine!.stats.summary(.inputToFrame))")
    }

    func run() {
        guard ProcessInfo.processInfo.environment["CFFIXED_USER_HOME"] != nil else {
            t.fail("run through `make bench` (CFFIXED_USER_HOME unset)")
        }
        guard let f = FakePDS(t.script, ["--base", "1000"]) else { t.fail("the fake PDS didn't start (bun \(t.script))") }
        t.fake = f
        print("Sky bench: release, LEAN_ABORT_ON_NONLINEAR=\(ProcessInfo.processInfo.environment["LEAN_ABORT_ON_NONLINEAR"] ?? "unset"), \(size.w) × \(size.h) window at 2×, fake PDS with 1,000 posts (seed 20261025)")
        let p = painter
        t.launch(f.service, core: { self.core }, onPublish: { p.heard($0) })
        painter.engine = t.engine
        painter.start()
        t.until(5, "no sign-in screen") { self.t.node(6, $0) != nil }
        let launched = footprint()
        print("memory, launched: \(breakdown())")

        // Sign-in → first page painted, 0 and 100 ms added to each XRPC reply.
        for lat in [0, 100] {
            f.control("slow?ms=\(lat)")
            var pub: [Double] = [], paint: [Double] = []
            for _ in 0..<runs {
                let (a, b) = signIn(f)
                pub.append(a); paint.append(b)
                signOut()
            }
            print("sign-in → first page, +\(lat) ms: published \(summary(pub)); painted \(summary(paint)) (\(runs) runs)")
        }
        f.control("slow?ms=0")

        // Refresh → new posts painted, at the top of a fresh feed, 3 posts arriving each time.
        _ = signIn(f)
        for lat in [0, 100] {
            f.control("slow?ms=\(lat)")
            var pub: [Double] = [], paint: [Double] = []
            for _ in 0..<runs {
                let before = t.posts(t.frame) ?? 0
                f.control("post?n=3")
                let (a, b) = timed(4, "refresh") { (self.t.posts($0) ?? 0) >= before + 3 && !self.t.busy($0) && self.t.node(33, $0) != nil }
                pub.append(a); paint.append(b)
                usleep(100_000)
            }
            print("refresh → new posts, +\(lat) ms: published \(summary(pub)); painted \(summary(paint)) (\(runs) runs)")
        }
        f.control("slow?ms=0")

        // The whole timeline: scroll to the end until the fake has no more.
        var guardTicks = 0
        while !caughtUp(t.frame) || t.busy(t.frame) {
            guardTicks += 1
            if guardTicks > 2000 { t.fail("didn't reach the end (\(t.posts(t.frame) ?? 0) posts)") }
            t.wheel(3000, 1)
            usleep(20_000)
        }
        let posts = t.posts(t.frame) ?? 0
        t.wheel(-100_000_000, 1)
        t.until(5, "not back at the top") { (self.t.firstShown($0)?.key ?? 0) == self.t.rows($0).keys.min() }
        usleep(2_000_000)
        let loaded = footprint()
        print("memory, loaded: \(breakdown())")

        // Flings down to the end and back up, every frame timed.
        print("flings through \(posts) posts with images (the fake's PNGs, 64 to 1,263 px a side):")
        core.recording = true
        painter.reset()
        t.engine!.stats.reset()
        let down = fling(1, max: 200)
        report("\(down) flings down to the end")
        let afterDown = footprint()
        print("memory, at the end: \(breakdown())")
        let storeDown = (ImageStore.shared.bytes, ImageStore.shared.count)
        core.recording = true
        painter.reset()
        t.engine!.stats.reset()
        let up = fling(-1, max: 200)
        report("\(up) flings back up")
        core.recording = false
        usleep(1_000_000)
        let afterUp = footprint()
        print("memory, back at the top: \(breakdown())")
        let storeUp = (ImageStore.shared.bytes, ImageStore.shared.count)
        print("memory (physical footprint): signed out \(mb(launched)), \(posts) posts loaded at the top \(mb(loaded)), after flinging to the end \(mb(afterDown)), and back \(mb(afterUp))")
        print("image store: \(mb(storeDown.0)) in \(storeDown.1) images at the end, \(mb(storeUp.0)) in \(storeUp.1) back at the top; budget \(mb(96 * 1024 * 1024))")

        f.control("slow?ms=0")
        signOut()
        painter.stop()
        t.clean()
        guard t.store.held.isEmpty else { t.fail("Keychain items left") }
    }
}
