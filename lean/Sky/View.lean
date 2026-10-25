module

public import Sky.Proofs

/-! # A bare window

Sky is headless for now (#210 and #211 add the real view): this window shows just enough for the
runtime and `cairn fuzz` to drive the model. A line of who is signed in, a line of what went
wrong, a button for each move while it is enabled, and the first posts of the feed, one line
each. -/

@[expose] public section

namespace Sky
open Cairn CairnAtproto CairnAtproto.Session

def white : Color := ⟨255, 255, 255, 255⟩
def paper : Color := ⟨246, 245, 241, 255⟩
def ink : Color := ⟨28, 28, 30, 255⟩
def muted : Color := ⟨110, 110, 118, 255⟩
def accent : Color := ⟨32, 105, 224, 255⟩

def pad : Nat := 16
def lineH : Nat := 18
/-- How many posts the bare window lists. -/
def shown : Nat := 12

/-- Room for every row at once: three lines, the buttons, `shown` posts, and the gaps between
the `4 + shown` rows. -/
def minSize (_ : State) : Size := ⟨420, 2 * pad + 3 * lineH + 30 + shown * lineH + (3 + shown) * 7⟩

def textLine (t : String) (color : Color := ink) (size : Nat := 13) : Node :=
  .box { width := .fill, height := .fixed lineH, clip := true, axis := .row, align := .center } none
    [.text { font := { size }, color } t]

def button (claim : Nat) (t : String) : Node :=
  .box { width := .fixed 84, height := .fixed 30, radius := 7, align := .center, justify := .center,
         clip := true, background := some accent, corner := .continuous }
    (some { ref := ⟨claim, 0⟩, label := t })
    [.text { font := { size := 13, weight := 600 }, color := white } t]

/-- Who is signed in, or what the session is doing. -/
def who (s : State) : String :=
  match s.session.phase with
  | .launched => if s.booting then "Starting…" else "Signed out"
  | .signedOut => "Signed out"
  | .signingIn .. => "Signing in…"
  | .signedIn a => "@" ++ a.handle
  | .refreshing _ _ (some a) => "@" ++ a.handle
  | .refreshing _ _ none => "Resuming…"

def canSignOut (ss : Session.State) : Bool :=
  match ss.phase with
  | .launched | .signedOut => false
  | _ => true

def buttons (s : State) : List Node :=
  (if canSignIn s.session then [button 2 "Sign in"] else []) ++
  (if canLoadMore s then [button 3 "Load more"] else []) ++
  (if canRefresh s then [button 4 "Refresh"] else []) ++
  (if canSignOut s.session then [button 5 "Sign out"] else [])

def itemLine (i : FeedItem) : Node :=
  textLine ("@" ++ i.post.author.handle ++ ": " ++ i.post.text)

def feedLine (f : Feed) : String :=
  s!"{f.items.length} posts" ++ (if f.atEnd then " · the end" else "") ++
    (if f.refresh.isSome then " · refreshing" else "") ++
    (if f.loadMore.isSome then " · loading more" else "")

def view (s : State) (_ : UI) : Node :=
  .box { width := .fill, height := .fill, padding := ⟨pad, pad, pad, pad⟩, gap := 7,
         background := some paper, clip := true } none
    ([textLine (who s) ink 15, textLine (s.problem.getD "") muted,
      .box { axis := .row, width := .fill, height := .fixed 30, gap := 8 } none (buttons s),
      textLine (feedLine s.feed) muted] ++
     (s.feed.items.take shown).map itemLine)

end Sky
