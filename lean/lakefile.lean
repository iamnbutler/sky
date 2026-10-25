import Lake
open Lake DSL

package sky where
  leanOptions := #[⟨`weak.cairn.claims.scope, "sky"⟩]

require "iamnbutler" / "cairn" @ "^0.2.5"
require "iamnbutler" / "cairn_json" @ "^0.1.0"
require "iamnbutler" / "cairn_atproto" @ "^0.1.0"

@[default_target]
lean_lib Sky where
  roots := #[`Sky.Abi, `Sky]
  defaultFacets := #[LeanLib.staticFacet]
