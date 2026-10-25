module

public import Cairn

/-! Sky: a Cairn app. Its claims are `sky^N`, locked in claims.lock (Cairn's
docs/claims.md); its exports are in `Sky.Abi`. -/

@[expose] public section

namespace Sky
open Cairn Cairn.Claims

structure State where
  count : Nat := 0
deriving Repr, DecidableEq, Inhabited

place ^1 window "Sky window" where
  does "The app's window: the count and a Count button."

move ^2 count (s : State) "Count" in ^1 where
  does "Press Count."
  sees "The count goes up by one."
  on press
    apply := { s with count := s.count + 1 }
    post s' := s'.count = s.count + 1
    sound := by intro s; rfl

def machine : Machine State := { init := {}, moves := moves% }

def claimInfos : List ClaimInfo := claims%

def white : Color := ⟨255, 255, 255, 255⟩
def ink : Color := ⟨28, 28, 30, 255⟩
def green : Color := ⟨48, 160, 80, 255⟩

def view (s : State) (_ : UI) : Node :=
  .box { width := .fill, height := .fill, padding := ⟨40, 40, 40, 40⟩, gap := 16,
         background := some white, clip := true } none
    [ .box { width := .fill, height := .fixed 20, clip := true } none
        [.text { font := { size := 15 }, color := ink } s!"Count: {s.count}"],
      .box { width := .fixed 160, height := .fixed 44, radius := 6, align := .center,
             justify := .center, clip := true, background := some green }
        (some { ref := ⟨2, 0⟩, label := "Count" })
        [.text { font := { size := 15, weight := 600 }, color := white } "Count"] ]

def app : App State := machine.toApp [.window 1 "Sky" view] claimInfos

end Sky
