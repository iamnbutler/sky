import CSky
import CairnFrame
import CairnHost
import Foundation

// Sky on Cairn's host (Cairn's docs/package.md).
//   Sky               open the window
//   Sky --selftest    run the Lean side headlessly: press Count, check the count

let app = LeanApp(
    module: runtime_initialize_sky_Sky_Abi,
    initialize: { w, h, scale in cairn_app_init(w, h, scale) },
    step: { cairn_app_step($0, $1) },
    frame: { cairn_app_frame($0) },
    codec: FrameV1Codec())

let size = Size(w: 480, h: 320)

if CommandLine.arguments.contains("--selftest") {
    func fail(_ message: String) -> Never {
        FileHandle.standardError.write(Data("selftest: FAIL: \(message)\n".utf8))
        exit(1)
    }
    let engine = Engine(size: size, scalePercent: 200) { LeanCore(app) }
    engine.start()
    guard let first = engine.wait(through: 0) else { fail("no first frame") }
    guard let button = first.frame.ax.first(where: { $0.control?.label == "^2" }) else { fail("no Count button (^2)") }
    let c = Point(x: button.rect.x + button.rect.w / 2, y: button.rect.y + button.rect.h / 2)
    let seq = engine.send([.pointerMove(c), .pointerDown(c, .primary, clicks: 1, Mods()), .pointerUp(c, .primary, Mods())])
    guard let after = engine.wait(through: seq) else { fail("no frame after the click") }
    guard after.frame.ax.contains(where: { $0.label == "Count: 1" }) else { fail("the count isn't 1 after a press on ^2") }
    engine.stop()
    print("selftest: PASS (Sky: first frame, a press on ^2)")
    exit(0)
}

MainActor.assumeIsolated {
    CairnApp.main(CairnApp.Config(title: "Sky", size: size) { LeanCore(app) })
}
