module

public import Sky.View
meta import Cairn.Claims.Elab

/-! # Sky's claims

| Id | Kind | What |
|---|---|---|
| ^1 | place | the window (bare until #210) |
| ^2 | move | Sign in |
| ^3 | move | Load more |
| ^4 | move | Refresh |
| ^5 | move | Sign out |
| ^20 | invariant | the feed is a contiguous run of the server's timeline, in its order |
| ^21 | invariant | a load-more page for a cursor the feed no longer holds changes nothing |
| ^22 | invariant | the cursor is never lost |
| ^23 | invariant | a refresh racing a load-more: either order, the same feed |
| ^24 | invariant | at most one load-more and one refresh in flight; every call answered, cancelled or live |
| ^25 | invariant | signed out ⇒ the feed is empty and nothing is in flight |
-/

@[expose] public section

namespace Sky
open Cairn Cairn.Claims CairnAtproto CairnAtproto.Session

/-! ## Places -/

place ^1 window "Sky window" where
  does "Sky's window. Bare for now: who is signed in, what went wrong, a button for each thing you can do, and the first posts of the home feed."

/-! ## Moves -/

move ^2 signInMove (s : State) "Sign in" in ^1 where
  does "While signed out, press Sign in (with the service, handle and app password typed)."
  sees "Sky signs in to the service; once signed in it loads the head of the home feed. A refused sign-in says why. The password is not kept."
  enabled := canSignIn s.session
  on press
    emit := s.step .signIn
    post s' := s'.login.password = ""
    sound := by intro s h; exact signIn_post h

move ^3 loadMoreMove (s : State) "Load more" in ^1 where
  does "With a feed that isn't at its end, press Load more."
  sees "The next page of the feed, from the cursor the feed holds, is appended below the posts already there; if a refresh replaced the feed first, the page is dropped."
  enabled := canLoadMore s
  on press
    emit := s.step .loadMore
    post s' := s'.feed.items = s.feed.items ∧ s'.feed.loadMore.isSome
    sound := by intro s h; exact loadMore_post h

move ^4 refreshMove (s : State) "Refresh" in ^1 where
  does "While signed in, press Refresh."
  sees "Sky asks for the head of the feed and stops any load-more in flight. New posts are put on top; if more than a page arrived, the feed is replaced by the new page."
  enabled := canRefresh s
  on press
    emit := s.step .refresh
    post s' := s'.feed.items = s.feed.items ∧ s'.feed.loadMore = none ∧ s'.feed.refresh = some s.nextCall
    sound := by intro s h; exact refresh_post h

move ^5 signOutMove (s : State) "Sign out" in ^1 where
  does "While signed in or signing in, press Sign out."
  sees "Sky signs out and forgets the session's tokens; the feed is emptied and every request it was waiting on is cancelled."
  enabled := canSignOut s.session
  on press
    emit := s.step .signOut
    post s' := s'.session.phase = .signedOut ∧ s'.feed = {}
    sound := by intro s _; exact signOut_post s

def machine : Machine State :=
  { init := initial, moves := moves%, receive := fun s m => s.step (.msg m) }

/-! ## Invariants -/

/-- Every move is a step of the model. -/
theorem update_step (s : State) (a : Action) :
    (machine.update s a).1 = s ∨ ∃ c, (machine.update s a).1 = (s.step c).1 := by
  rcases dispatch_cases machine.moves s a with h0 | ⟨m, hm, h, hh, -, -, -, e⟩
  · exact Or.inl (by rw [Machine.update, h0])
  · rw [Machine.update, e]
    simp only [machine, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    all_goals simp only [signInMove, loadMoreMove, refreshMove, signOutMove] at hh
    all_goals obtain rfl | hh := List.mem_cons.mp hh
    all_goals first
      | exact Or.inr ⟨_, rfl⟩
      | exact absurd hh List.not_mem_nil

theorem update_inv {P : State → Prop} (hp : ∀ s c, P s → P (s.step c).1) (s : State) (a : Action)
    (h : P s) : P (machine.update s a).1 := by
  rcases update_step s a with e | ⟨c, e⟩
  · rw [e]; exact h
  · rw [e]; exact hp s c h

invariant ^20 contiguous "The feed is a run of the timeline" for machine where
  does "The feed is a contiguous run of the server's timeline, in its order: no post twice, none skipped. Stated against a timeline with no duplicates: a feed that is a run of it stays one when the next page is appended, when a head page puts new posts on top, and when a head page that doesn't reach the feed replaces it."
  holds _s := Feed.Contiguous
  init := Feed.contiguous
  step := fun _ _ _ => Feed.contiguous
  receive := fun _ _ _ => Feed.contiguous

/-- A load-more page for a cursor the feed no longer holds changes nothing it shows. -/
def StalePage : Prop :=
  ∀ (f : Feed) (id : Nat) (page : Option FeedPage),
    (∀ c, f.loadMore = some (id, c) → f.cursor ≠ some c) →
    (f.gotLoadMore id page).content = f.content

theorem stale_page : StalePage := fun f id page h => Feed.gotLoadMore_stale f id page h

invariant ^21 stalePage "A stale page changes nothing" for machine where
  does "A load-more page asked from a cursor the feed no longer holds (a refresh replaced the feed meanwhile) never changes the posts, the cursor or the end; nor does an answer to any call but the load-more in flight."
  holds _s := StalePage
  init := stale_page
  step := fun _ _ _ => stale_page
  receive := fun _ _ _ => stale_page

invariant ^22 cursorKept "The cursor is never lost" for machine where
  does "A feed with posts that isn't at its end holds a cursor: the one that came with its last page (fuzzed: equal to it)."
  holds s := Inv s ∧ CursorKept s.feed
  init := ⟨inv_initial, inv_initial.cur⟩
  step := fun s a h => by
    have i := update_inv (P := Inv) (fun s c h => step_inv h c) s a h.1
    exact ⟨i, i.cur⟩
  receive := fun s m h => by
    have i := step_inv h.1 (.msg m)
    exact ⟨i, i.cur⟩

/-- A refresh racing a load-more: their answers in either order give the same feed. -/
def Race : Prop :=
  ∀ (f : Feed) (l r : Nat) (c : String) (pl pr : Option FeedPage),
    f.loadMore = some (l, c) → f.cursor = some c → f.items ≠ [] → f.refresh = some r →
    (f.gotLoadMore l pl).gotRefresh r pr = (f.gotRefresh r pr).gotLoadMore l pl

theorem race_any : Race := fun f l r c pl pr hl hc hne hr => Feed.race f l r c pl pr hl hc hne hr

invariant ^23 race "A refresh racing a load-more" for machine where
  does "With a load-more and a refresh both in flight, their answers in either order (or either failing) leave the same feed: the result of one of the two orders, and so of both."
  holds _s := Race
  init := race_any
  step := fun _ _ _ => race_any
  receive := fun _ _ _ => race_any

invariant ^24 inFlight "Requests in flight are accounted for" for machine where
  does "At most one load-more and one refresh are in flight, each a different call the session has taken on (sent or held for a token refresh); the load-more was asked from the cursor the feed holds; the session's requests have distinct ids. The fuzz checks every request is answered, cancelled or live."
  holds s := Inv s
  init := inv_initial
  step := fun s a h => update_inv (P := Inv) (fun _s c h => step_inv h c) s a h
  receive := fun _s m h => step_inv h (.msg m)

theorem signedOut_initial : SignedOutEmpty initial := fun _ => ⟨rfl, rfl, rfl⟩

invariant ^25 signedOutEmpty "Signed out, nothing shown or in flight" for machine where
  does "Whenever the session isn't signed in, the feed is empty and no call is in flight or held: every one was cancelled."
  holds s := SignedOutEmpty s
  init := signedOut_initial
  step := fun s a h => update_inv (P := SignedOutEmpty) (fun s c _ => step_signedOut s c) s a h
  receive := fun s m _ => step_signedOut s (.msg m)

def claimInfos : List ClaimInfo := claims%

def app : App State :=
  { machine.toApp [.window 1 "Sky" view] claimInfos with
    initEffects
    minSize }

end Sky
