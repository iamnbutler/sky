import Checks
import Sky.Fuzz
import Cairn.Fuzz.Collect
import Cairn.Fuzz.Main

/-! `lake exe fuzz` (`cairn fuzz`): Cairn's claim-driven fuzzer on Sky's controls (Cairn's
docs/fuzz.md), the invariants checked after each step. It plays the host too, with Sky's fake
server and checks (`Sky.fuzz`, Sky/Fuzz.lean). -/

/-- Sky's own machine. `fuzz_targets%` also collects cairn_atproto's session machine, under the
same name (`Claims`, its module's last component), which would shadow Sky's; cairn_atproto fuzzes
its own. -/
def targets : List Cairn.Fuzz.Target :=
  -- cairn#221.
  (fuzz_targets% : List Cairn.Fuzz.Target).filter (·.module.startsWith "Sky.")

def main (args : List String) : IO UInt32 := Cairn.Fuzz.main targets args
