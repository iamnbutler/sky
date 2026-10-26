import Checks
import Sky.Fuzz
import Cairn.Fuzz.Collect
import Cairn.Fuzz.Main

/-! `lake exe fuzz` (`cairn fuzz`): Cairn's claim-driven fuzzer on Sky's controls (Cairn's
docs/fuzz.md), the invariants checked after each step. It plays the host too, with Sky's fake
server and checks (`Sky.fuzz`, Sky/Fuzz.lean). Since Cairn 0.4.0 `fuzz_targets%` names a
dependency's machine with its package (`cairn_atproto/Claims`), and `cairn fuzz` runs only Sky's
own unless asked (`--deps`). -/

def targets : List Cairn.Fuzz.Target := fuzz_targets%

def main (args : List String) : IO UInt32 := Cairn.Fuzz.main targets args
