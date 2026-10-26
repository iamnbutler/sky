import CSky
import CairnFrame
import CairnHost
import Foundation

// Sky on Cairn's host (Cairn's docs/package.md). The host only performs effects; the model is
// Lean's (lean/Sky).
//   Sky                                   open the window
//   Sky --selftest <server.ts> [--shots <dir>]
//       sign in to cairn_atproto's fake PDS (`server.ts`, run here with Bun on 127.0.0.1) by
//       typing in the form, read the feed, quit and resume, sign out (Selftest.swift)
//   Sky --bench [<server.ts>]
//       first page, refresh, flings through 1,000 posts and memory against the fake PDS
//       (Bench.swift, bench/README.md); `cairn bench` runs it from the package's root

let app = LeanApp(
    module: runtime_initialize_sky_Sky_Abi,
    initialize: { w, h, scale in cairn_app_init(w, h, scale) },
    step: { cairn_app_step($0, $1) },
    frame: { cairn_app_frame($0) },
    codec: FrameV1Codec())

let size = Size(w: 600, h: 820)

if let i = CommandLine.arguments.firstIndex(of: "--selftest") {
    let args = CommandLine.arguments
    guard i + 1 < args.count else {
        FileHandle.standardError.write(Data("selftest: give the fake PDS's server.ts\n".utf8))
        exit(2)
    }
    let shots = args.firstIndex(of: "--shots").flatMap { $0 + 1 < args.count ? args[$0 + 1] : nil }
    Selftest(server: args[i + 1], shots: shots).run()
    exit(0)
}

if let i = CommandLine.arguments.firstIndex(of: "--bench") {
    let args = CommandLine.arguments
    let server = i + 1 < args.count ? args[i + 1] : "lean/.lake/packages/cairn_atproto/tools/fake-pds/server.ts"
    Bench(server: server).run()
    exit(0)
}

MainActor.assumeIsolated {
    CairnApp.main(CairnApp.Config(title: "Sky", size: size) { LeanCore(app) })
}
