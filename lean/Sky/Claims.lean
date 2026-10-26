module

public import Sky.View
meta import Cairn.Claims.Elab

/-! # Sky's claims

| Id | Kind | What |
|---|---|---|
| ^1 | place | the window: the sign-in screen, or the feed |
| ^2 | move | Sign in (retired: reissued as ^10) |
| ^3 | move | Load more (retired: the end row loads more, ^30 and ^31) |
| ^4 | move | Refresh |
| ^5 | move | Sign out (retired: reissued as ^11 and ^12) |
| ^6 | move | the Handle or email field |
| ^7 | move | the App password field (secure) |
| ^8 | move | the Service field |
| ^9 | move | What's an app password? (opens Bluesky's page) |
| ^10 | move | Sign in: enabled exactly when both fields are typed in and no sign-in is in flight |
| ^11 | move | Sign out, in the account panel |
| ^12 | move | Cancel a sign-in or resume, offered once it has taken a few seconds |
| ^13 | move | Account: open or close the account panel |
| ^14 | place | the feed: a virtual list of posts and the end row |
| ^20 | invariant | the feed is a contiguous run of the server's timeline, in its order |
| ^21 | invariant | a load-more page for a cursor the feed no longer holds changes nothing |
| ^22 | invariant | the cursor is never lost |
| ^23 | invariant | a refresh racing a load-more: either order, the same feed |
| ^24 | invariant | at most one load-more and one refresh in flight; every call answered, cancelled or live |
| ^25 | invariant | signed out ⇒ the feed is empty and nothing is in flight |
| ^26 | invariant | the password reaches one request (retired: reissued as ^28) |
| ^27 | invariant | Sign Out forgets both items; signed out, no secret (retired: reissued as ^29) |
| ^28 | invariant | the password reaches one request, redacted, and is cleared as it is sent |
| ^29 | invariant | Sign Out forgets both Keychain items; signed out, no request carries a secret |
| ^30 | move | the end of the feed comes into view: load more |
| ^31 | move | Retry, after a load-more failed |
| ^32 | move | a post: press to open it on bsky.app; in view, its images load |
| ^33 | move | "N new posts": back to the top |
| ^34 | invariant | the rows are the feed's posts; posts put on top keep every key below them |
| ^35 | invariant | the post the reader is at stays still when rows are put above it |
| ^36 | invariant | image loads only for rows near the view; none signed out |
-/

@[expose] public section

namespace Sky
open Cairn Cairn.Claims CairnAtproto CairnAtproto.Session

/-! ## Places -/

place ^1 window "Sky window" where
  does "Sky's window. Signed out, the sign-in screen: handle or email, app password, service, Sign in, and what went wrong. Signed in: the home feed (Following), with Refresh and Account above it and a status line that offers new posts."

place ^14 feedPlace "The feed" in ^1 where
  does "The home feed in a virtual list: one row per post (avatar, name, handle, time, the text wrapped, up to four images, Reposted by and Replying to, other embeds as a line, the counts), then the end row. Cairn owns its offset and lays only the rows near the view; the wheel, the trackpad and the page keys move it."

/-! ## Moves -/

retire ^2 move "Sign in" because "Sign in is enabled only with both fields typed in (cairn#210): reissued as ^10."

retire ^3 move "Load more" because "The end of the list loads more as it comes into view (cairn#211): reissued as ^30, and ^31 to retry."

move ^4 refreshMove (s : State) "Refresh" in ^1 where
  does "While signed in, press Refresh."
  sees "Sky asks for the head of the feed and stops any load-more in flight. New posts are put on top; if more than a page arrived, the feed is replaced by the new page."
  enabled := canRefresh s
  on press
    emit := s.step .refresh
    post s' := s'.feed.items = s.feed.items ∧ s'.feed.loadMore = none ∧ s'.feed.refresh = some s.nextCall
    sound := by intro s h; exact refresh_post h

retire ^5 move "Sign out" because "Sign out moved into the account panel, and Cancel is its own move (cairn#210): reissued as ^11 and ^12."

move ^6 typeIdentifier (s : State) "Type your handle or email" in ^1 where
  does "While signed out, type in the Handle or email field, and press Enter."
  sees "The text appears in the field; Enter moves on to the App password field."
  enabled := !live s.session
  on edit (op : TextOp)
    emit := s.step (.editIdentifier op)
    post s' := s'.identifier = (Text.Field.apply op s.identifier).1 ∧ s'.password = s.password
    sound := by intro s op _; exact ⟨step1_identifier _ _, rfl⟩
  on submit
    emit := s.step .nextField
    post s' := s'.identifier = s.identifier ∧ s'.password = s.password
    sound := by intro s _; exact ⟨step1_identifier _ _, rfl⟩

move ^7 typePassword (s : State) "Type your app password" in ^1 where
  does "While signed out, type in the App password field, and press Enter."
  sees "One bullet per character; copy, cut and undo beep. Enter signs in, as Sign in does, when it is enabled."
  enabled := !live s.session
  on edit (op : TextOp)
    emit := s.step (.editPassword op)
    post s' := s'.password = (Text.SecureField.apply op s.password).1 ∧ s'.identifier = s.identifier
    sound := by intro s op _; exact ⟨step1_password _ _, step1_identifier _ _⟩
  on submit
    emit := s.step .signIn
    post s' := ready s = true →
      s'.password = Text.SecureField.empty passwordHint ∧ signingIn s'.session = true
    sound := by intro s _ h; exact signIn_post h

move ^8 typeService (s : State) "Type the service" in ^1 where
  does "While signed out, type in the Service field (empty: https://bsky.social, or the default Sky reads at launch)."
  sees "The text appears in the field; Sign in goes to that service."
  enabled := !live s.session
  on edit (op : TextOp)
    emit := s.step (.editService op)
    post s' := s'.service = (Text.Field.apply op s.service).1 ∧ s'.password = s.password
    sound := by intro s op _; exact ⟨step1_service _ _, rfl⟩

move ^9 appPasswordHelp (s : State) "What's an app password?" in ^1 where
  does "While signed out, press What's an app password?"
  sees "Bluesky's App Passwords settings page opens in the browser."
  enabled := !live s.session
  on press
    emit := s.step .openHelp
    post s' := s'.session.phase = s.session.phase ∧ s'.password = s.password
    sound := by intro s _; exact ⟨step1_phase _ _, rfl⟩

move ^10 signInMove (s : State) "Sign in" in ^1 where
  does "Type a handle or email and an app password, and press Sign in. It is enabled exactly when both fields are typed in and no sign-in (or resume) is in flight."
  sees "Sky sends the one createSession request (its body redacted in every tool), and the password field is empty from that step on. Signed in, it loads the head of the home feed; refused, it says why in words."
  enabled := ready s
  on press
    emit := s.step .signIn
    post s' := s'.password = Text.SecureField.empty passwordHint ∧ signingIn s'.session = true
    sound := by intro s h; exact signIn_post h

move ^11 signOutMove (s : State) "Sign out" in ^1 where
  does "While signed in, open the account panel and press Sign out."
  sees "Sky signs out: it forgets both Keychain items and the saved account, empties the feed and cancels every request it was waiting on. The sign-in screen shows, the handle still filled in."
  enabled := live s.session && s.accountOpen
  on press
    emit := s.step .signOut
    post s' := s'.session.phase = .signedOut ∧ s'.feed = {}
    sound := by intro s _; exact signOut_post s

move ^12 cancelSignIn (s : State) "Cancel signing in" in ^1 where
  does "While Sky has been signing in or resuming the session for a few seconds, press Cancel."
  sees "The sign-in screen is ready again. Whatever the cancelled request brings back is forgotten (both Keychain items), and until it does Sign in waits."
  enabled := offerCancel s
  on press
    emit := s.step .signOut
    post s' := s'.session.phase = .signedOut ∧ s'.feed = {}
    sound := by intro s _; exact signOut_post s

move ^13 accountMove (s : State) "Account" in ^1 where
  does "While signed in, press Account (Done when it is open)."
  sees "The account panel opens, with the handle, the service and Sign out; pressed again, it closes."
  enabled := live s.session
  on press
    emit := s.step .toggleAccount
    post s' := s'.accountOpen = !s.accountOpen ∧ s'.feed = s.feed
    sound := by intro s h; exact toggleAccount_post h

move ^30 reachEnd (s : State) "Reach the end of the feed" in ^14 where
  does "Scroll the feed to its end, while it isn't at the end of the timeline."
  sees "Loading… shows at the end, and the next page, from the cursor the feed holds, is appended below the posts already there; if a refresh replaced the feed first, the page is dropped."
  enabled := canLoadMore s && !s.moreFailed
  on appear
    emit := s.step .loadMore
    post s' := s'.feed.items = s.feed.items ∧ s'.feed.loadMore.isSome
    sound := by intro s h; exact loadMore_post (bool_left h)

move ^31 retryMore (s : State) "Retry loading more" in ^14 where
  does "After a load-more failed, press Retry at the end of the feed."
  sees "Sky asks for the next page again, from the cursor the feed holds."
  enabled := canLoadMore s && s.moreFailed
  on press
    emit := s.step .loadMore
    post s' := s'.feed.items = s.feed.items ∧ s'.feed.loadMore.isSome
    sound := by intro s h; exact loadMore_post (bool_left h)

move ^32 postRowMove (s : State) (k : Nat) "A post" in ^14 where
  does "Press a post (or Return on it); or scroll it into view."
  sees "Pressed, the post opens on bsky.app. In view, its avatar and images load (grey until they do, the same size after), and loads for posts far from it are cancelled."
  enabled := canOpenRow s k
  on press
    emit := s.step (.openPost k)
    post s' := s'.feed = s.feed ∧ s'.session = s.session
    sound := by intro s k h; exact openPost_post (bool_left h) k
  on appear
    emit := s.step (.appearRow k)
    post s' := s'.feed = s.feed ∧ s'.session = s.session
    sound := by intro s k h; exact appearRow_post (bool_left h) k

move ^33 showNewMove (s : State) "Show new posts" in ^1 where
  does "After a refresh put posts above the one you are reading, press N new posts."
  sees "The feed goes back to its top, the newest post first."
  enabled := canShowNew s
  on press
    emit := s.step .showNew
    post s' := s.gen < s'.gen ∧ s'.feed = s.feed
    sound := by intro s h; exact showNew_post (bool_left h)

def machine : Machine State :=
  { init := initial, moves := moves%, receive := fun s m => s.step (.msg m) }

/-! ## Invariants -/

/-- Every move is a step of the model, so a property every step keeps, every move keeps. -/
theorem moves_keep {P : State → Prop} (hp : ∀ s c, P s → P (s.step c).1) :
    ∀ m ∈ machine.moves, m.Preserves P :=
  Move.all_cons (refreshMove.preserves _ fun s _ h => hp s _ h)
  (Move.all_cons (typeIdentifier.preserves _ (fun s _ _ h => hp s _ h) fun s _ h => hp s _ h)
  (Move.all_cons (typePassword.preserves _ (fun s _ _ h => hp s _ h) fun s _ h => hp s _ h)
  (Move.all_cons (typeService.preserves _ fun s _ _ h => hp s _ h)
  (Move.all_cons (appPasswordHelp.preserves _ fun s _ h => hp s _ h)
  (Move.all_cons (signInMove.preserves _ fun s _ h => hp s _ h)
  (Move.all_cons (signOutMove.preserves _ fun s _ h => hp s _ h)
  (Move.all_cons (cancelSignIn.preserves _ fun s _ h => hp s _ h)
  (Move.all_cons (accountMove.preserves _ fun s _ h => hp s _ h)
  (Move.all_cons (reachEnd.preserves _ fun s _ h => hp s _ h)
  (Move.all_cons (retryMore.preserves _ fun s _ h => hp s _ h)
  (Move.all_cons (postRowMove.preserves _ (fun s _ _ h => hp s _ h) fun s _ _ h => hp s _ h)
  (Move.all_cons (showNewMove.preserves _ fun s _ h => hp s _ h) Move.all_nil))))))))))))

theorem update_inv {P : State → Prop} (hp : ∀ s c, P s → P (s.step c).1) (s : State) (a : Action)
    (h : P s) : P (machine.update s a).1 := machine.preserves (moves_keep hp) s a h

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

retire ^26 invariant "The password reaches one request" because "Sky's step gained the feed's rows and images (cairn#211), so the statement's step is a new one: reissued as ^28."

retire ^27 invariant "Signed out, no secret" because "Sky's step gained the feed's rows and images (cairn#211), so the statement's step is a new one: reissued as ^29."

invariant ^28 passwordOnce "The password reaches one request" for machine where
  does "Every step but Sign in (the button, or Enter in the password field) has the same effects whatever the password field holds. Sign in's effects are the same too, for any password of the same length, once the redacted request's contents are blanked; with Sign in enabled its only request is createSession, carrying the password and marked redact, and the field is empty after. So the password is sent in exactly one request, and never shown by a tool (Cairn redacts it in dumps and logs; the fuzzer plants text in the field and checks)."
  holds _s := PasswordSent
  init := passwordSent
  step := fun _ _ _ => passwordSent
  receive := fun _ _ _ => passwordSent

invariant ^29 signOutSecrets "Signed out, no secret" for machine where
  does "Sign out's effects include forgetting both Keychain items (access and refresh). While signed out, no step sends a request carrying a Keychain secret."
  holds _s := SignOutForgets ∧ SignedOutNoSecret
  init := ⟨signOutForgets, signedOutNoSecret⟩
  step := fun _ _ _ => ⟨signOutForgets, signedOutNoSecret⟩
  receive := fun _ _ _ => ⟨signOutForgets, signedOutNoSecret⟩

theorem rowsFollow_step (s : State) (c : Cmd) (h : RowsFollow s) : RowsFollow (s.step c).1 :=
  step_follows s c h.2

invariant ^34 rowsFollow "Posts keep their keys" for machine where
  does "The rows of the list are the feed's posts in its order, keyed from a first key up, with the end row's key 0 last and never a post's. Posts a refresh puts on top take the keys below the first; every post already there keeps its key and the list stays the same one, so the reader's post is found where it was; they are counted as new posts until they come into view. A feed replaced or emptied starts a new list, at the top."
  holds s := RowsFollow s ∧ PrependKeeps
  init := ⟨follows_initial, prependKeeps⟩
  step := fun s a h => ⟨update_inv (P := RowsFollow) rowsFollow_step s a h.1, prependKeeps⟩
  receive := fun s m h => ⟨rowsFollow_step s (.msg m) h.1, prependKeeps⟩

/-- Cairn's anchor (`VList.record_keeps`), for any list: when the runtime keeps a row still, the
corrected offset moves exactly as much as the row's top moved, so the row shows where it did,
unless the clamp moved the offset. -/
def AnchorKept : Prop :=
  ∀ (info : VList.Info) (r : Rect) (pad : Insets) (o lim : Int) (kids : List Laid) {i : Nat} {t : Int},
    VList.keepRow info (VList.after info (r.w - pad.left - pad.right) kids).rows o = some (i, t) →
    (0 ≤ o + ((VList.after info (r.w - pad.left - pad.right) kids).topF
        (VList.after info (r.w - pad.left - pad.right) kids).pre i - t) ∧
      o + ((VList.after info (r.w - pad.left - pad.right) kids).topF
        (VList.after info (r.w - pad.left - pad.right) kids).pre i - t) ≤ lim) →
    (VList.after info (r.w - pad.left - pad.right) kids).topF
        (VList.after info (r.w - pad.left - pad.right) kids).pre i -
      (VList.record info r pad o lim kids).2 = t - o

theorem anchorKept : AnchorKept := fun info r pad o lim kids _ _ hk hc =>
  VList.record_keeps info r pad o lim kids hk hc

invariant ^35 anchor "The post you are reading stays still" for machine where
  does "When a refresh puts posts above the post at the top of the view (^34 keeps its key), or heights above it are corrected, the runtime moves the offset by exactly as much as that post moved, so it stays where it was on screen, unless the offset is clamped. At the very top too: the new posts land above the view, and N new posts (^33) offers them. Checked by the fuzzer at every step."
  holds _s := AnchorKept
  init := anchorKept
  step := fun _ _ _ => anchorKept
  receive := fun _ _ _ => anchorKept

invariant ^36 imagesNearInvariant "Image loads only near the view" for machine where
  does "When a post comes into view, every image load still in flight is for a post within 12 rows of it: loads for posts scrolled far away are cancelled. Signed out, no image load is in flight and there are no rows. At most 6 requests are with the host at once (Cairn's maxInFlight, Runtime.step_cap)."
  holds _s := ImagesNear
  init := imagesNear
  step := fun _ _ _ => imagesNear
  receive := fun _ _ _ => imagesNear

def claimInfos : List ClaimInfo := claims%

def app : App State :=
  { machine.toApp [.window 1 "Sky" view] claimInfos with
    initEffects
    subscriptions
    minSize }

end Sky
