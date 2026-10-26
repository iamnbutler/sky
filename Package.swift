// swift-tools-version: 6.0
// The app's host: Cairn's AppKit host, linking .cairn/lib/libsky.a, which
// `cairn build` makes from the Lean code (bin/cairn-link).
import PackageDescription

let lib = Context.packageDirectory + "/.cairn/lib"

let package = Package(
    name: "sky",
    platforms: [.macOS("27.0")],
    dependencies: [.package(url: "https://cairn.registry.nexthub.sh/git/iamnbutler/cairn.git", from: "0.4.0")],
    targets: [
        // The Lean exports Cairn's CLean doesn't declare: the app's initializer.
        .target(name: "CSky", dependencies: [.product(name: "CLean", package: "cairn")]),
        .executableTarget(
            name: "Sky",
            dependencies: ["CSky",
                           .product(name: "CLean", package: "cairn"),
                           .product(name: "CairnFrame", package: "cairn"),
                           .product(name: "CairnHost", package: "cairn"),
                           .product(name: "CairnRender", package: "cairn")],
            linkerSettings: [.unsafeFlags(["-L" + lib, "-lsky"])]),
    ]
)
