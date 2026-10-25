import CSky
import CairnFrame
import CairnHost
import Foundation

// Sky on Cairn's host (Cairn's docs/package.md). The host only performs effects; the model is
// Lean's (lean/Sky).
//   Sky               open the window
//   Sky --selftest    run the Lean side headlessly: the first frames, signed out, Sign in (^2)
//                     offered; nothing is pressed, so nothing reaches the network

let app = LeanApp(
    module: runtime_initialize_sky_Sky_Abi,
    initialize: { w, h, scale in cairn_app_init(w, h, scale) },
    step: { cairn_app_step($0, $1) },
    frame: { cairn_app_frame($0) },
    codec: FrameV1Codec())

let size = Size(w: 480, h: 360)

if CommandLine.arguments.contains("--selftest") {
    func fail(_ message: String) -> Never {
        FileHandle.standardError.write(Data("selftest: FAIL: \(message)\n".utf8))
        exit(1)
    }
    let engine = Engine(size: size, scalePercent: 200) { LeanCore(app) }
    engine.start()
    guard let first = engine.wait(through: 0) else { fail("no first frame") }
    guard first.frame.ax.contains(where: { $0.control?.label == "^2" }) else { fail("no Sign in button (^2)") }
    // The saved service is read at launch (a fresh home has none): signed out, nothing to load.
    let deadline = Date().addingTimeInterval(5)
    var signedOut = false
    while Date() < deadline {
        if let f = engine.latest, f.frame.ax.contains(where: { $0.label == "Signed out" }) { signedOut = true; break }
        Thread.sleep(forTimeInterval: 0.05)
    }
    guard signedOut else { fail("not signed out after launch with no saved service") }
    guard let last = engine.latest, !last.frame.ax.contains(where: { $0.control?.label == "^3" || $0.control?.label == "^5" }) else {
        fail("Load more or Sign out offered while signed out")
    }
    engine.stop()
    print("selftest: PASS (Sky: signed out at launch, Sign in offered, no request to the network)")
    exit(0)
}

MainActor.assumeIsolated {
    CairnApp.main(CairnApp.Config(title: "Sky", size: size) { LeanCore(app) })
}
