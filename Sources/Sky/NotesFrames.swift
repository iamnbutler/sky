import CairnFrame
import CairnHost
import CairnRender
import Foundation

// `Sky --notes-frames <server.ts> <dir>`: notifications arriving and being read against
// cairn_atproto's fake PDS, rendered offscreen at 30 frames a second (cairn#255's media) into
// <dir>/notes as numbered PNGs. On Home partway down the feed, others like, repost and follow;
// the count comes onto the Notifications tab at the next poll (a cut while it waits for the
// minute's tick); the tab opens the list, refreshed, with "N new" taking it to the new rows,
// marked seen once on screen; Follow back on a
// follow row; a like from a reply's or mention's row; Home again, where the reader was.
// Like the selftest it signs in by typing, under a throwaway Keychain service and a scratch home.
final class NotesFrames {
    let t: Selftest
    let out: URL

    init(server: String, dir: String) {
        t = Selftest(server: server, shots: nil)
        out = URL(fileURLWithPath: dir, isDirectory: true)
    }

    func hold(_ s: Double) { Thread.sleep(forTimeInterval: s) }

    func run() {
        guard ProcessInfo.processInfo.environment["CFFIXED_USER_HOME"] != nil else {
            t.fail("run through `make notes-media` (CFFIXED_USER_HOME unset)")
        }
        guard let f = FakePDS(t.script, ["--act", "0", "--life", "500"]) else { t.fail("the fake PDS didn't start") }
        t.fake = f
        guard let renderer = try? Renderer() else { t.fail("no renderer") }
        let me = "@" + f.identifier

        // Sign in by typing; read what's there, so the count starts at 0; Home, partway down.
        t.launch(f.service)
        t.until(5, "no sign-in screen") { self.t.node(6, $0) != nil }
        t.type(6, f.identifier)
        t.type(7, f.password)
        t.click(10)
        t.until(15, "not signed in") { self.t.shows(me, $0) && !self.t.rows($0).isEmpty }
        t.until(10, "no images") { self.t.images($0) > 0 }
        t.click(61)
        t.until(10, "no notification rows") { f in !self.t.keyed(66, f).isEmpty }
        hold(2)
        t.click(62)
        t.until(5, "no feed") { self.t.firstShown($0) != nil }
        t.wheel(40, 4)
        t.until(5, "the feed didn't settle") { self.t.firstShown($0) != nil && !self.t.busy($0) }
        t.until(10, "no images") { self.t.images($0) > 0 }
        hold(1)

        let rec = Recorder(t.engine!)
        let before = t.unreadOf(t.frame) ?? 0
        rec.start()
        hold(2)
        rec.pause()
        f.control("act?kind=repost&actor=5")
        f.control("act?kind=follow&actor=1")
        for a in 1...4 { f.control("act?kind=like&actor=\(a)") }
        f.control("catchup")
        t.until(70, "the count didn't come") { (self.t.unreadOf($0) ?? 0) > before }
        rec.start(fresh: false)
        hold(2.5)
        t.click(61)
        t.until(10, "no notification rows") { f in !self.t.keyed(66, f).isEmpty }
        hold(2.5)
        // The list held its place; "N new" takes it to the top, to the new rows.
        if t.node(75) != nil {
            t.click(75)
            t.until(5, "\"N new\" didn't go") { self.t.node(75, $0) == nil }
            hold(2.5)
        }
        let fr = t.frame
        guard let l0 = t.listRect(fr) else { t.fail("no list") }
        guard let (fk, _) = t.keyed(83, fr).first(where: { $0.value.label.hasPrefix("Follow back @") && $0.value.rect.y >= l0.y && $0.value.rect.y + $0.value.rect.h <= l0.y + l0.h }) else {
            t.fail("no Follow back")
        }
        t.click(ControlRef(claim: 83, key: fk))
        hold(2)
        if let l = t.listRect(t.frame), let k = t.keyed(76, t.frame).filter({ _, n in
            !n.selected && n.rect.h > 0 && n.rect.y >= l.y && n.rect.y + n.rect.h <= l.y + l.h
        }).min(by: { $0.value.rect.y < $1.value.rect.y })?.key {
            t.click(ControlRef(claim: 76, key: k))
            hold(2)
        }
        t.click(62)
        hold(2.5)
        let n = (try? rec.stop(into: out.appendingPathComponent("notes"), renderer)) ?? 0

        t.clean()
        print("notes-frames: \(n) frames in \(out.path)/notes")
    }
}
