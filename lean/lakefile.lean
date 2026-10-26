import Lake
open Lake DSL

/-- Sky on Cairn. The package name is the claim scope: Sky's claims are `sky^N`. -/
package sky where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩,
    -- `weak.`: Lake passes it to every module, and only those that use the claim commands know it.
    ⟨`weak.cairn.claims.scope, "sky"⟩]

require "iamnbutler" / "cairn" @ "^0.4.0"
require "iamnbutler" / "cairn_json" @ "^0.1.1"
require "iamnbutler" / "cairn_atproto" @ "^0.2.0"

/-- The app: its exports (`Sky.Abi`) and everything they import from this package. -/
@[default_target]
lean_lib Sky where
  roots := #[`Sky.Abi, `Sky]
  defaultFacets := #[LeanLib.staticFacet]

/-- The app with its proofs and checks (`Checks.lean`): what the ledger, the axiom audit and the
kernel replay read. Never linked into the app. -/
@[default_target]
lean_lib Checks

/-- `lake exe fuzz` (`cairn fuzz`): Cairn's fuzzer on the app and a simulated host. -/
lean_exe fuzz where
  root := `FuzzMain


/-- `lake exe bench`: Sky's feed of 1,000 posts in flings, each frame timed by phase, against
cairn_atproto's Lean fake (bench/README.md). -/
lean_exe bench where
  root := `Bench
