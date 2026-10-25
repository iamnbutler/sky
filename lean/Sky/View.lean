module

public import Sky.Secrets

/-! # The window

Signed out, the sign-in screen: handle or email, the app password (a secure field, bullets
only), a link to Bluesky's app-passwords page, the service, Sign In (a control only while it is
enabled; otherwise drawn greyed, with no control), what is happening ("Signing in…") with a
Cancel once it has taken a few seconds, and what went wrong, in words. Signed in: who, Sign Out, Load more and Refresh while
enabled, and the first posts of the feed, one line each (#211 adds the real feed). -/

@[expose] public section

namespace Sky
open Cairn CairnAtproto CairnAtproto.Session

def white : Color := ⟨255, 255, 255, 255⟩
def paper : Color := ⟨246, 245, 241, 255⟩
def ink : Color := ⟨28, 28, 30, 255⟩
def muted : Color := ⟨110, 110, 118, 255⟩
def line : Color := ⟨206, 206, 212, 255⟩
def accent : Color := ⟨32, 105, 224, 255⟩
def greyed : Color := ⟨188, 196, 212, 255⟩
def alert : Color := ⟨190, 40, 40, 255⟩

def pad : Nat := 16
def lineH : Nat := 18
/-- How many posts the window lists. -/
def shown : Nat := 12

/-- Room for the sign-in screen and for the feed's rows. -/
def minSize (_ : State) : Size := ⟨440, 520⟩

def textLine (t : String) (color : Color := ink) (size : Nat := 13) (weight : Nat := 400) : Node :=
  .box { width := .fill, height := .fixed lineH, clip := true, axis := .row, align := .center } none
    [.text { font := { size, weight }, color } t]

def ring (ui : UI) (r : ControlRef) (otherwise : Option Border := none) : Option Border :=
  if ui.focus = some r then some ⟨2, accent⟩ else otherwise

def button (ui : UI) (claim : Nat) (t : String) (width : Nat := 96) : Node :=
  .box { width := .fixed width, height := .fixed 30, radius := 7, align := .center,
         justify := .center, clip := true, background := some accent, corner := .continuous,
         border := ring ui ⟨claim, 0⟩ }
    (some { ref := ⟨claim, 0⟩, label := t })
    [.text { font := { size := 13, weight := 600 }, color := white } t]

/-- A button that can't be pressed now: drawn, with no control. -/
def greyButton (t : String) (width : Nat := 96) : Node :=
  .box { width := .fixed width, height := .fixed 30, radius := 7, align := .center,
         justify := .center, clip := true, background := some greyed, corner := .continuous } none
    [.text { font := { size := 13, weight := 600 }, color := white } t]

def link (ui : UI) (claim : Nat) (t : String) : Node :=
  .box { height := .fixed lineH, align := .center, border := ring ui ⟨claim, 0⟩ }
    (some { ref := ⟨claim, 0⟩, role := .link, label := t })
    [.text { font := { size := 12 }, color := accent } t]

def label (t : String) : Node := textLine t muted 12 600

def field (ui : UI) (claim : Nat) (name : String) (v : FieldView) : Node :=
  .field { width := .fill, height := .fixed 30, padding := ⟨6, 8, 6, 8⟩, background := some white,
           radius := 6, border := ring ui ⟨claim, 0⟩ (some ⟨1, line⟩) }
    { font := { size := 13 }, color := ink }
    { ref := ⟨claim, 0⟩, role := .textField, label := name } v

def canSignOut (ss : Session.State) : Bool :=
  match ss.phase with
  | .launched | .signedOut => false
  | _ => true

/-- Cancel is offered once a sign-in or resume has taken `slowMs`. -/
def offerCancel (s : State) : Bool := s.slow && canSignOut s.session && !live s.session

/-- What the session is doing while the form shows. -/
def busy (s : State) : Option String :=
  match s.session.phase with
  | .signingIn .. => some (if s.slow then "Still signing in…" else "Signing in…")
  | .refreshing _ _ none => some "Resuming your session…"
  | _ => if s.own.any (·.2 == .readAccount) || s.own.any (·.2 == .readService) then some "Starting…"
         else none

def problemLine (s : State) : List Node :=
  match s.problem with
  | some p => [.para { font := { size := 12 }, color := alert } {} p]
  | none => []

/-- The sign-in screen. -/
def signInView (s : State) (ui : UI) : List Node :=
  [ textLine "Sign in to Bluesky" ink 20 700,
    .para { font := { size := 12 }, color := muted } {}
      "Use an app password, not your account's password. Sky keeps its session in your Keychain.",
    label "Handle or email",
    field ui 6 "Handle or email" (s.identifier.view (ui.focus = some ⟨6, 0⟩)),
    label "App password",
    field ui 7 "App password" (s.password.view (ui.focus = some ⟨7, 0⟩)),
    link ui 9 "What's an app password?",
    label "Service",
    field ui 8 "Service" (s.service.view (ui.focus = some ⟨8, 0⟩)),
    .box { axis := .row, width := .fill, height := .fixed 30, gap := 10, align := .center } none
      ((if ready s then [button ui 10 "Sign in"] else [greyButton "Sign in"]) ++
       (match busy s with
        | some t => [.text { font := { size := 12 }, color := muted } t]
        | none => []) ++
       (if offerCancel s then [button ui 12 "Cancel" 80] else [])) ] ++
  problemLine s

def itemLine (i : FeedItem) : Node :=
  textLine ("@" ++ i.post.author.handle ++ ": " ++ i.post.text)

def feedLine (f : Feed) : String :=
  s!"{f.items.length} posts" ++ (if f.atEnd then " · the end" else "") ++
    (if f.refresh.isSome then " · refreshing" else "") ++
    (if f.loadMore.isSome then " · loading more" else "")

def who (s : State) : String :=
  match account s.session with
  | some a => "@" ++ a.handle
  | none => ""

/-- The account panel: where the session is, and Sign out. -/
def accountPanel (s : State) (ui : UI) : List Node :=
  if s.accountOpen then
    [ .box { axis := .row, width := .fill, height := .fixed 30, gap := 8, align := .center,
             padding := ⟨0, 8, 0, 8⟩, background := some white, radius := 6 } none
        [ .box { width := .fill, height := .fixed lineH, clip := true } none
            [.text { font := { size := 12 }, color := muted } (who s ++ " on " ++ s.host)],
          button ui 11 "Sign out" 84 ] ]
  else []

/-- Signed in: who (the account button), the account panel, the feed's buttons and its first
posts. -/
def feedView (s : State) (ui : UI) : List Node :=
  [ .box { axis := .row, width := .fill, height := .fixed 30, gap := 8, align := .center } none
      [ .box { width := .fill, height := .fixed lineH, clip := true } none
          [.text { font := { size := 15, weight := 600 }, color := ink } (who s)],
        button ui 13 (if s.accountOpen then "Done" else "Account") 84 ] ] ++
  accountPanel s ui ++
  [
    .box { axis := .row, width := .fill, height := .fixed 30, gap := 8 } none
      ((if canLoadMore s then [button ui 3 "Load more"] else []) ++
       (if canRefresh s then [button ui 4 "Refresh"] else [])),
    textLine (feedLine s.feed) muted ] ++
  problemLine s ++
  (s.feed.items.take shown).map itemLine

def view (s : State) (ui : UI) : Node :=
  .box { width := .fill, height := .fill, padding := ⟨pad, pad, pad, pad⟩, gap := 7,
         background := some paper, clip := true } none
    (if live s.session then feedView s ui else signInView s ui)

end Sky
