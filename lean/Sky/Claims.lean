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
| ^11 | move | Sign out, in the account panel (retired: Sign Out is in the app menu, ^49) |
| ^12 | move | Cancel a sign-in or resume, offered once it has taken a few seconds |
| ^13 | move | Account: open or close the account panel (retired with the panel) |
| ^14 | place | the feed: a virtual list of posts and the end row |
| ^20 | invariant | the feed is a contiguous run of the server's timeline (retired: cairn_atproto^26) |
| ^21 | invariant | a stale load-more page changes nothing (retired: cairn_atproto^27) |
| ^22 | invariant | the cursor is never lost (retired: cairn_atproto^28; Sky's steps keep it in ^24) |
| ^23 | invariant | a refresh racing a load-more (retired: cairn_atproto^29) |
| ^24 | invariant | at most one load-more and one refresh in flight; every call answered, cancelled or live |
| ^25 | invariant | signed out ⇒ the feed is empty and nothing is in flight |
| ^26 | invariant | the password reaches one request (retired: reissued as ^28) |
| ^27 | invariant | Sign Out forgets both items; signed out, no secret (retired: reissued as ^29) |
| ^28 | invariant | the password reaches one request (retired: reissued as ^44) |
| ^29 | invariant | Sign Out forgets both items; signed out, no secret (retired: reissued as ^45) |
| ^30 | move | the end of the feed comes into view: load more |
| ^31 | move | Retry, after a load-more failed |
| ^32 | move | a post: press to open it on bsky.app; in view, its images load |
| ^33 | move | "N new posts": back to the top |
| ^34 | invariant | posts keep their keys (retired: reissued as ^46) |
| ^35 | invariant | the post the reader is at stays still when rows are put above it |
| ^36 | invariant | image loads only near the view (retired: reissued as ^47) |
| ^37 | move | Like a post: a toggle with its count |
| ^38 | move | Repost a post: a toggle with its count |
| ^39 | move | Follow or Unfollow a post's author, in the post's menu |
| ^40 | move | Mute a post's author, in the post's menu |
| ^41 | invariant | the acts' tables are calm: a settled like, repost, follow or mute shows the server's; counts through `count` |
| ^42 | invariant | a muted account's posts appear nowhere: their rows lay a point high, keeping their keys |
| ^43 | invariant | signed out ⇒ the acts hold nothing |
| ^44 | invariant | the password reaches one request, redacted, and is cleared as it is sent |
| ^45 | invariant | Sign Out forgets both Keychain items; signed out, no request carries a secret |
| ^46 | invariant | the rows are the feed's posts; posts put on top keep every key below them |
| ^47 | invariant | image loads only for rows near the view; none signed out |
| ^48 | place | Sky's menus in the menu bar |
| ^49 | move | Sign Out, in the app menu |
| ^50 | place | the View menu |
| ^51 | move | View ▸ Refresh, ⌘R |
| ^52 | place | a post's menu: its ⋯ button `^52#k`, and the secondary click on the post |
| ^53 | move | Copy Link to Post, in a post's menu |
| ^54 | move | Open on bsky.app, in a post's menu |
| ^55 | invariant | Like and Repost: on every post that shows exactly when signed in; checked as the table shows |
| ^56 | invariant | Sign Out is in the app menu, enabled exactly when signed in |
| ^57 | invariant | a post's menu says Follow or Unfollow, Mute or Unmute, as the tables show |
| ^58 | move | Undo a mute, in the status line |
| ^60 | place | the notifications: a virtual list of grouped rows and the end row |
| ^61 | move | Notifications (with the unread count): show the notifications |
| ^62 | move | Home: back to the feed |
| ^63 | move | Refresh the notifications |
| ^64 | move | the end of the notifications comes into view: load more |
| ^65 | move | Retry, after loading more notifications failed |
| ^66 | move | a row of the notifications comes into view: marked seen up to it |
| ^67 | invariant | the notifications are a contiguous, newest-first run of the server's |
| ^68 | invariant | the groups partition the notifications shown, in order; each one reason and subject |
| ^69 | invariant | no row is from a muted account |
| ^70 | invariant | `seenAt` never decreases and never passes a notification that hasn't been on screen |
| ^71 | invariant | at most one unread poll, none signed out; the badge is the unread count shown |
-/

@[expose] public section

namespace Sky
open Cairn Cairn.Claims CairnAtproto CairnAtproto.Session

/-! ## Places -/

place ^1 window "Sky window" where
  does "Sky's window. Signed out, the sign-in screen: handle or email, app password, service, Sign in, and what went wrong. Signed in: the home feed (Following), with Refresh and Account above it and a status line that offers new posts."

place ^14 feedPlace "The feed" in ^1 where
  does "The home feed in a virtual list: one row per post (avatar, name, handle, time, the text wrapped, up to four images, Reposted by and Replying to, other embeds as a line, the counts), then the end row. Cairn owns its offset and lays only the rows near the view; the wheel, the trackpad and the page keys move it."

place ^60 notesPlace "The notifications" in ^1 where
  does "The notifications in a virtual list, newest first: likes, reposts and follows of the same post (or of you) next to each other make one row (\"Alice, Bob and 3 others liked your post\"); mentions, replies and quotes a row each; a dot on the ones newer than what is marked seen. Then the end row. The Notifications button in the header shows the unread count."

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

retire ^11 move "Sign out" because "Sign Out moved to the app menu and the account panel is gone (cairn#254): reissued as ^49."

move ^12 cancelSignIn (s : State) "Cancel signing in" in ^1 where
  does "While Sky has been signing in or resuming the session for a few seconds, press Cancel."
  sees "The sign-in screen is ready again. Whatever the cancelled request brings back is forgotten (both Keychain items), and until it does Sign in waits."
  enabled := offerCancel s
  on press
    emit := s.step .signOut
    post s' := s'.session.phase = .signedOut ∧ s'.feed = {}
    sound := by intro s _; exact signOut_post s

retire ^13 move "Account" because "The account panel held only Sign out, which moved to the app menu (cairn#254, ^49); the header shows who is signed in."

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
  does "Press a post (or Return on it); or scroll it into view. A post hidden by a mute is neither."
  sees "Pressed, the post opens on bsky.app. In view, its avatar and images load (grey until they do, the same size after), and loads for posts far from it are cancelled."
  enabled := canOpenRow s k
  on press
    emit := s.step (.openPost k)
    post s' := s'.feed = s.feed ∧ s'.session = s.session
    sound := by intro s k h; exact openPost_post (bool_left (bool_left h)) k
  on appear
    emit := s.step (.appearRow k)
    post s' := s'.feed = s.feed ∧ s'.session = s.session
    sound := by intro s k h; exact appearRow_post (bool_left (bool_left h)) k

move ^33 showNewMove (s : State) "Show new posts" in ^1 where
  does "After a refresh put posts above the one you are reading, press N new posts."
  sees "The feed goes back to its top, the newest post first."
  enabled := canShowNew s
  on press
    emit := s.step .showNew
    post s' := s.gen < s'.gen ∧ s'.feed = s.feed
    sound := by intro s h; exact showNew_post (bool_left h)

place ^48 menuBarPlace "Sky's menus" in ^1 where
  does "Sky's own items in the menu bar: Sign Out at the top of the app menu, and the View menu."

place ^50 viewMenu "The View menu" in ^48 where
  does "The View menu in the menu bar: Refresh (⌘R)."

place ^52 postMenuPlace "A post's menu" in ^14 where
  does "A post's ⋯ button opens its menu (a click, Space or Return); the secondary click on the post or on its Like or Repost toggle, Shift-F10 on any of them, or VoiceOver's Show Menu, opens the same menu. It has Follow or Unfollow and Mute for someone else's post, then Copy Link to Post and Open on bsky.app."

move ^37 likeMove (s : State) (k : Nat) "Like a post" in ^14 where
  does "While signed in, press the Like toggle (♡ and the count) under a post."
  sees "The post shows liked (♥, selected) or not, and its like count moves by one, in the same frame, everywhere it appears; greyed until the server answers. Sky writes the like record (putRecord with a record key it mints, or deleteRecord); if the server refuses, the post shows what it did before and the status line says why; if the answer is lost, Sky reads the record back before it believes either."
  enabled := canAct s .like k
  on press
    emit := s.step (.act .like k)
    post s' := ∀ it, s.rows.item? k = some it → s'.acts.liked it.post.uri = !s.acts.liked it.post.uri
    sound := by intro s k h it hit; exact act_post h it hit

move ^38 repostMove (s : State) (k : Nat) "Repost a post" in ^14 where
  does "While signed in, press the Repost toggle (⇄ and the count) under a post."
  sees "The post shows reposted (selected) or not, and its repost count moves by one, in the same frame. The write, a refusal and a lost answer go as for Like (^37)."
  enabled := canAct s .repost k
  on press
    emit := s.step (.act .repost k)
    post s' := ∀ it, s.rows.item? k = some it →
      s'.acts.reposted it.post.uri = !s.acts.reposted it.post.uri
    sound := by intro s k h it hit; exact act_post h it hit

move ^39 followMove (s : State) (k : Nat) "Follow a post's author" in ^52 where
  does "While signed in, open someone else's post's menu (⋯, or the secondary click on the post) and choose Follow @handle (Unfollow once following)."
  sees "Every post by that account shows Unfollow (or Follow) in the same frame. Sky writes the follow record; a refusal and a lost answer go as for Like (^37)."
  enabled := canAct s .follow k
  on press
    emit := s.step (.act .follow k)
    post s' := ∀ it, s.rows.item? k = some it →
      s'.acts.following it.post.author.did = !s.acts.following it.post.author.did
    sound := by intro s k h it hit; exact act_post h it hit

move ^40 muteMove (s : State) (k : Nat) "Mute an account" in ^52 where
  does "While signed in, open someone else's post's menu (⋯, or the secondary click on the post) and choose Mute @handle."
  sees "Every post by the account, and every repost by it, is gone from the feed in the same frame, without moving the post you are reading (^42, ^35), and a post quoting it says \"Quoted post from an account you muted\". The status line says \"Muted @handle\" with Undo (^58) for a few seconds. Sky sends muteActor; a refusal brings the posts back and says why; a lost answer sends the same mute again until one is answered."
  enabled := canAct s .mute k
  on press
    emit := s.step (.act .mute k)
    post s' := ∀ it, s.rows.item? k = some it →
      s'.acts.muted (muteTarget s it) = !s.acts.muted (muteTarget s it)
    sound := by intro s k h it hit; exact act_post h it hit
move ^61 notesTab (s : State) "Notifications" in ^1 where
  does "While signed in, on the feed, press Notifications (it shows the unread count, if there is one)."
  sees "The notifications show, and Sky asks for their head. Once rows have come into view, Sky marks them seen."
  enabled := live s.session && s.tab == .home
  on press
    emit := s.step .openNotes
    post s' := s'.tab = .notifications ∧ s'.feed = s.feed
    sound := by intro s h; exact openNotes_post (bool_left h)

move ^62 homeTab (s : State) "Home" in ^1 where
  does "While the notifications show, press Home."
  sees "The feed shows again, where it was."
  enabled := live s.session && s.tab == .notifications
  on press
    emit := s.step .openHome
    post s' := s'.tab = .home ∧ s'.feed = s.feed
    sound := by intro s h; exact openHome_post (bool_left h)

move ^63 noteRefreshMove (s : State) "Refresh the notifications" in ^1 where
  does "While the notifications show, press Refresh."
  sees "Sky asks for the head of the notifications; new ones are put on top (grouped with the row below when they can be), or the list is replaced if more than a page arrived. The unread count is polled after."
  enabled := canNoteRefresh s && s.tab == .notifications
  on press
    emit := s.step .noteRefresh
    post s' := s'.notes.list.items = s.notes.list.items ∧ s'.notes.list.refresh = some s.nextCall
    sound := by intro s h; exact noteRefresh_post (bool_left h)

move ^64 reachNotesEnd (s : State) "Reach the end of the notifications" in ^60 where
  does "Scroll the notifications to their end, while there are older ones."
  sees "Loading… shows at the end, and the next page is appended below; if a refresh replaced the list first, the page is dropped."
  enabled := canNoteMore s && !s.notes.moreFailed
  on appear
    emit := s.step .noteMore
    post s' := s'.notes.list.items = s.notes.list.items ∧ s'.notes.list.loadMore.isSome
    sound := by intro s h; exact noteMore_post (bool_left h)

move ^65 retryNotes (s : State) "Retry loading more notifications" in ^60 where
  does "After loading more notifications failed, press Retry at the end of the list."
  sees "Sky asks for the next page again."
  enabled := canNoteMore s && s.notes.moreFailed
  on press
    emit := s.step .noteMore
    post s' := s'.notes.list.items = s.notes.list.items ∧ s'.notes.list.loadMore.isSome
    sound := by intro s h; exact noteMore_post (bool_left h)

move ^66 noteRowMove (s : State) (k : Nat) "A notification" in ^60 where
  does "Scroll a row of the notifications into view."
  sees "Sky marks the notifications seen up to the row's newest, at once on screen (the dots go), and tells the server (updateSeen) in the background; if the server refuses, the dots come back and the problem line says why."
  enabled := live s.session && s.tab == .notifications && s.noteGroups.any (·.key == k)
  on appear
    emit := s.step (.noteAppear k)
    post s' := s.notes.seen.1.mark ≤ s'.notes.seen.1.mark ∧ s'.feed = s.feed
    sound := by intro s k h; exact noteAppear_post (bool_left (bool_left h)) k

move ^49 signOutMenu (s : State) "Sign Out" in ^48 where
  does "While signed in, choose Sky ▸ Sign Out in the menu bar. It is greyed while signed out."
  sees "Sky signs out: it forgets both Keychain items and the saved account, empties the feed and cancels every request it was waiting on. The sign-in screen shows, the handle still filled in."
  enabled := live s.session
  on press
    emit := s.step .signOut
    post s' := s'.session.phase = .signedOut ∧ s'.feed = {}
    sound := by intro s _; exact signOut_post s

move ^51 refreshMenu (s : State) "Refresh from the View menu" in ^50 where
  does "While signed in, choose View ▸ Refresh, or press ⌘R. It is greyed while a refresh is in flight or signed out."
  sees "As Refresh in the header (^4): Sky asks for the head of the feed and stops any load-more in flight."
  enabled := canRefresh s
  on press
    emit := s.step .refresh
    post s' := s'.feed.items = s.feed.items ∧ s'.feed.loadMore = none ∧ s'.feed.refresh = some s.nextCall
    sound := by intro s h; exact refresh_post h

move ^53 copyLinkMove (s : State) (k : Nat) "Copy a post's link" in ^52 where
  does "Open a post's menu and choose Copy Link to Post."
  sees "The post's address on bsky.app is on the clipboard. Nothing else changes."
  enabled := canOpenRow s k
  on press
    emit := s.step (.copyLink k)
    post s' := s'.feed = s.feed ∧ s'.session = s.session ∧ s'.acts.tables.likes = s.acts.tables.likes
    sound := by intro s k h; exact copyLink_post (bool_left (bool_left h)) k

move ^54 openMenuMove (s : State) (k : Nat) "Open a post on bsky.app" in ^52 where
  does "Open a post's menu and choose Open on bsky.app."
  sees "The post opens on bsky.app in the browser, as pressing the post does (^32)."
  enabled := canOpenRow s k
  on press
    emit := s.step (.openPost k)
    post s' := s'.feed = s.feed ∧ s'.session = s.session
    sound := by intro s k h; exact openPost_post (bool_left (bool_left h)) k

move ^58 undoMuteMove (s : State) "Undo a mute" in ^1 where
  does "Just after muting an account from a post's menu, press Undo in the status line (\"Muted @handle. Their posts are hidden.\"). It is offered for a few seconds."
  sees "The account is unmuted: its posts and reposts show again in the same frame, where they were, and Sky sends unmuteActor."
  enabled := canUndoMute s
  on press
    emit := s.step .undoMute
    post s' := ∀ d, s.undoMute = some d → s'.acts.muted d = false
    sound := by intro s h d hd; exact undoMute_post h hd

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
  (Move.all_cons (cancelSignIn.preserves _ fun s _ h => hp s _ h)
  (Move.all_cons (reachEnd.preserves _ fun s _ h => hp s _ h)
  (Move.all_cons (retryMore.preserves _ fun s _ h => hp s _ h)
  (Move.all_cons (postRowMove.preserves _ (fun s _ _ h => hp s _ h) fun s _ _ h => hp s _ h)
  (Move.all_cons (showNewMove.preserves _ fun s _ h => hp s _ h)
  (Move.all_cons (likeMove.preserves _ fun s _ _ h => hp s _ h)
  (Move.all_cons (repostMove.preserves _ fun s _ _ h => hp s _ h)
  (Move.all_cons (followMove.preserves _ fun s _ _ h => hp s _ h)
  (Move.all_cons (muteMove.preserves _ fun s _ _ h => hp s _ h)
  (Move.all_cons (signOutMenu.preserves _ fun s _ h => hp s _ h)
  (Move.all_cons (refreshMenu.preserves _ fun s _ h => hp s _ h)
  (Move.all_cons (copyLinkMove.preserves _ fun s _ _ h => hp s _ h)
  (Move.all_cons (openMenuMove.preserves _ fun s _ _ h => hp s _ h)
  (Move.all_cons (undoMuteMove.preserves _ fun s _ h => hp s _ h)
  (Move.all_cons (notesTab.preserves _ fun s _ h => hp s _ h)
  (Move.all_cons (homeTab.preserves _ fun s _ h => hp s _ h)
  (Move.all_cons (noteRefreshMove.preserves _ fun s _ h => hp s _ h)
  (Move.all_cons (reachNotesEnd.preserves _ fun s _ h => hp s _ h)
  (Move.all_cons (retryNotes.preserves _ fun s _ h => hp s _ h)
  (Move.all_cons (noteRowMove.preserves _ fun s _ _ h => hp s _ h) Move.all_nil)))))))))))))))))))))))))

theorem update_inv {P : State → Prop} (hp : ∀ s c, P s → P (s.step c).1) (s : State) (a : Action)
    (h : P s) : P (machine.update s a).1 := machine.preserves (moves_keep hp) s a h

retire ^20 invariant "The feed is a run of the timeline" because "The feed is cairn_atproto's Paged list now (cairn#250), and this is proved for every paged list there: cairn_atproto^26."

retire ^21 invariant "A stale page changes nothing" because "The feed is cairn_atproto's Paged list now (cairn#250), and this is proved for every paged list there: cairn_atproto^27."

retire ^22 invariant "The cursor is never lost" because "The feed is cairn_atproto's Paged list now (cairn#250), and every operation on a paged list keeps its cursor: cairn_atproto^28. Sky's steps keep it as part of ^24's invariant (`Inv.cur`)."

retire ^23 invariant "A refresh racing a load-more" because "The feed is cairn_atproto's Paged list now (cairn#250), and this is proved for every paged list there: cairn_atproto^29."

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

retire ^28 invariant "The password reaches one request" because "Sky's state gained the likes, reposts, follows and mutes, and its step sends their calls (cairn#252), so the statement's step is a new one: reissued as ^44."

invariant ^44 passwordOnce "The password reaches one request" for machine where
  does "Every step but Sign in (the button, or Enter in the password field) has the same effects whatever the password field holds. Sign in's effects are the same too, for any password of the same length, once the redacted request's contents are blanked; with Sign in enabled its only request is createSession, carrying the password and marked redact, and the field is empty after. So the password is sent in exactly one request, and never shown by a tool (Cairn redacts it in dumps and logs; the fuzzer plants text in the field and checks)."
  holds _s := PasswordSent
  init := passwordSent
  step := fun _ _ _ => passwordSent
  receive := fun _ _ _ => passwordSent

retire ^29 invariant "Signed out, no secret" because "Sky's state gained the likes, reposts, follows and mutes, and its step sends their calls (cairn#252), so the statement's step is a new one: reissued as ^45."

invariant ^45 signOutSecrets "Signed out, no secret" for machine where
  does "Sign out's effects include forgetting both Keychain items (access and refresh). While signed out, no step sends a request carrying a Keychain secret."
  holds _s := SignOutForgets ∧ SignedOutNoSecret
  init := ⟨signOutForgets, signedOutNoSecret⟩
  step := fun _ _ _ => ⟨signOutForgets, signedOutNoSecret⟩
  receive := fun _ _ _ => ⟨signOutForgets, signedOutNoSecret⟩

theorem rowsFollow_step (s : State) (c : Cmd) (h : RowsFollow s) : RowsFollow (s.step c).1 :=
  step_follows s c h.2

retire ^34 invariant "Posts keep their keys" because "Sky's state gained the likes, reposts, follows and mutes, and its step sends their calls (cairn#252), so the statement's step is a new one: reissued as ^46."

invariant ^46 rowsFollow "Posts keep their keys" for machine where
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
  does "When a refresh puts posts above the post at the top of the view (^46 keeps its key), or heights above it are corrected, the runtime moves the offset by exactly as much as that post moved, so it stays where it was on screen, unless the offset is clamped. At the very top too: the new posts land above the view, and N new posts (^33) offers them. Checked by the fuzzer at every step."
  holds _s := AnchorKept
  init := anchorKept
  step := fun _ _ _ => anchorKept
  receive := fun _ _ _ => anchorKept

retire ^36 invariant "Image loads only near the view" because "Sky's state gained the likes, reposts, follows and mutes, and its step sends their calls (cairn#252), so the statement's step is a new one: reissued as ^47."

invariant ^47 imagesNearInvariant "Image loads only near the view" for machine where
  does "When a post comes into view, every image load still in flight is for a post within 12 rows of it: loads for posts scrolled far away are cancelled. Signed out, no image load is in flight and there are no rows. At most 6 requests are with the host at once (Cairn's maxInFlight, Runtime.step_cap)."
  holds _s := ImagesNear
  init := imagesNear
  step := fun _ _ _ => imagesNear
  receive := fun _ _ _ => imagesNear

/-- ^41: the acts' tables are calm, so a key at rest shows what the server last confirmed, and a
count shown is never less than the viewer's own part of it. -/
def ActsSound (s : State) : Prop :=
  s.acts.tables.Ok ∧ ∀ p : Post, Optimistic.ind (s.acts.liked p.uri) ≤ s.acts.likeCount p ∧
    Optimistic.ind (s.acts.reposted p.uri) ≤ s.acts.repostCount p

theorem actsSound (s : State) : ActsSound s :=
  ⟨s.acts.ok, fun p => ⟨s.acts.likeCount_ge p, s.acts.repostCount_ge p⟩⟩

invariant ^41 actsSettle "Likes, reposts, follows and mutes settle on the server's" for machine where
  does "Each of likes, reposts, follows and mutes is a Cairn.Optimistic table (cairn^1100–^1114), changed only by its feed, so it is always calm: once a post's like (or any key) has no write in flight and no read-back pending, it shows what the server last confirmed, whatever order the replies came in and whichever were lost; a lost write is read back from the account's own repo (getRecord), or for a mute sent again, before it is believed. A count shown is the view's count, less the viewer's own in it, plus what is shown (Cairn.Optimistic.count), so never below the viewer's own. The fuzz drives Sky against cairn_atproto's fake server and checks that every settled key and count matches the server's."
  holds s := ActsSound s
  init := actsSound _
  step := fun _ _ _ => actsSound _
  receive := fun _ _ _ => actsSound _

/-- ^42: a muted account's posts appear nowhere: a row whose author (or reposter) shows muted is
`hiddenRow`, a point high with no control, and its key stays (the rows are the feed's, ^46); a
quoted post by a muted account is words. -/
def MutedHidden : Prop :=
  (∀ (s : State) (it : FeedItem), s.acts.muted it.post.author.did = true → hiddenItem s it = true) ∧
  (∀ (s : State) (ui : UI) (k : Nat) (it : FeedItem), k ≠ 0 → s.rows.item? k = some it →
    hiddenItem s it = true → rowOf s ui k = hiddenRow) ∧
  (∀ (s : State) (k : Nat), hiddenAt s k = true → canOpenRow s k = false ∧
    ∀ kind, canAct s kind k = false) ∧
  (∀ (s : State) (q : QuotedPost), s.acts.muted q.author.did = true →
    quoteLineFor s (.post q) = mutedQuote)

theorem mutedHidden : MutedHidden := by
  refine ⟨fun s it h => ?_, fun s ui k it hk hit hh => ?_, fun s k h => ?_, fun s q h => ?_⟩
  · simp only [hiddenItem, h, Bool.true_or]
  · simp only [rowOf, hk, hit, postRow, hh, ↓reduceIte]
  · unfold hiddenAt at h
    split at h
    · next it hit =>
      refine ⟨by simp [canOpenRow, hiddenAt, hit, h], fun kind => ?_⟩
      simp only [canAct, hit, h, Bool.not_true, Bool.false_and, Bool.and_false]
    · cases h
  · simp only [quoteLineFor, h, ↓reduceIte]

invariant ^42 mutedNowhere "A muted account's posts appear nowhere" for machine where
  does "A post whose author is muted, or a repost by a muted account, is gone from the feed: its row lays a point high, with nothing of the post (its text, images, embeds and counts are not read) and no control, so it can't be opened or acted on; it keeps its key, so the post you are reading stays where it is (^35, ^46). A quoted post by a muted account shows as \"Quoted post from an account you muted\". Muted means as shown: a mute shows in the step it is chosen (^40), and Undo (^58) brings the posts back."
  holds _s := MutedHidden
  init := mutedHidden
  step := fun _ _ _ => mutedHidden
  receive := fun _ _ _ => mutedHidden

/-- ^55: on a post that shows, Like and Repost are offered exactly when signed in, each a toggle
checked as its table shows the post. -/
def TogglesShown : Prop :=
  ∀ (s : State) (ui : UI) (k : Nat) (it : FeedItem), s.rows.item? k = some it → hiddenItem s it = false →
    canAct s .like k = live s.session ∧ canAct s .repost k = live s.session ∧
    (likeNodes s ui k it).length = (if live s.session then 1 else 0) ∧
    (repostNodes s ui k it).length = (if live s.session then 1 else 0) ∧
    (likeControl s k it).checked = some (s.acts.liked it.post.uri) ∧
    (repostControl s k it).checked = some (s.acts.reposted it.post.uri)

theorem togglesShown : TogglesShown := by
  intro s ui k it hit hh
  have hl : canAct s .like k = live s.session := by simp [canAct, hit, hh]
  have hr : canAct s .repost k = live s.session := by simp [canAct, hit, hh]
  refine ⟨hl, hr, ?_, ?_, rfl, rfl⟩
  · simp only [likeNodes, hl]; split <;> simp_all
  · simp only [repostNodes, hr]; split <;> simp_all

invariant ^55 togglesInvariant "Like and Repost are toggles that show the table" for machine where
  does "Under every post that shows, Like and Repost are offered exactly when signed in. Each is a toggle whose checked (and selected) state is what the likes' or reposts' table shows for the post (^41), so VoiceOver says \"selected\" when it is on; its count is the view's, less the viewer's own in it, plus what is shown."
  holds _s := TogglesShown
  init := togglesShown
  step := fun _ _ _ => togglesShown
  receive := fun _ _ _ => togglesShown

/-- ^56: Sign Out is in the app menu, enabled exactly when signed in. -/
def SignOutInMenu : Prop := ∀ s : State, MenuItem.enabledOf (menuBar s) signOutRef = some (live s.session)

theorem signOutInMenu : SignOutInMenu := fun s => by
  simp [MenuItem.enabledOf, MenuItem.find, MenuItem.findOf, menuBar, signOutRef]

invariant ^56 signOutMenuInvariant "Sign Out is in the app menu" for machine where
  does "The app menu has Sign Out in every state, enabled exactly when signed in (greyed otherwise, and choosing it then does nothing)."
  holds _s := SignOutInMenu
  init := signOutInMenu
  step := fun _ _ _ => signOutInMenu
  receive := fun _ _ _ => signOutInMenu

/-- The label of item `r` of a menu. -/
def labelOf (items : List MenuItem) (r : ControlRef) : Option String :=
  (MenuItem.find r items).map (·.1.label)

/-- ^57: a post's menu says Follow or Unfollow, Mute or Unmute, by what the tables show. -/
def MenuWords : Prop :=
  ∀ (s : State) (k : Nat) (it : FeedItem),
    (canAct s .follow k = true →
      labelOf (postMenu s k it) ⟨39, k⟩ =
        some (followWords (s.acts.following it.post.author.did) ("@" ++ it.post.author.handle))) ∧
    (canAct s .mute k = true →
      labelOf (postMenu s k it) ⟨40, k⟩ =
        some (muteWords (s.acts.muted (muteTarget s it)) ("@" ++ it.post.author.handle)))

theorem menuWords : MenuWords := by
  intro s k it
  constructor
  · intro h
    simp [labelOf, postMenu, h, MenuItem.find, MenuItem.findOf]
  · intro h
    simp only [labelOf, postMenu, h]
    split <;> simp [MenuItem.find, MenuItem.findOf]

invariant ^57 menuWordsInvariant "A post's menu says what the tables show" for machine where
  does "On someone else's post, the post's menu says Follow @handle or Unfollow @handle as the follows' table shows the author, and Mute @handle or Unmute @handle as the mutes' table shows them."
  holds _s := MenuWords
  init := menuWords
  step := fun _ _ _ => menuWords
  receive := fun _ _ _ => menuWords

invariant ^43 actsGone "Signed out, no acts held" for machine where
  does "Whenever the session isn't signed in, Sky holds no like, repost, follow or mute, no view of a post, no act in flight and no line about one: signing out drops them, and the next account starts from its own server's."
  holds s := ActsGone s
  init := fun _ => rfl
  step := fun s a h => update_inv (P := ActsGone) (fun s c _ => step_actsGone s c) s a h
  receive := fun s m _ => step_actsGone s (.msg m)
invariant ^67 notesContiguous "The notifications are a run of the server's" for machine where
  does "The notifications are cairn_atproto's Paged list (cairn#250), the same as the feed: a contiguous, newest-first run of the server's notifications with no duplicates, staying one when a page is appended, a head page arrives or new notifications arrive on the server (cairn_atproto^26); a stale page changes nothing (^27), the cursor is kept (^28), and a refresh racing a load-more ends the same either way (^29). The fuzz checks Sky's list against the fake server's after every step."
  holds _s := Paged.Contiguous Notification
  init := Paged.contiguous
  step := fun _ _ _ => Paged.contiguous
  receive := fun _ _ _ => Paged.contiguous

invariant ^68 groupsInvariant "The groups partition the notifications" for machine where
  does "The rows are the notifications shown, in order, cut into runs: flattened, the groups are exactly the list (less muted accounts'); every member of a group has its reason and subject, and only likes, reposts and follows group; no two groups next to each other could have been one."
  holds _s := GroupsPartition
  init := groupsPartition
  step := fun _ _ _ => groupsPartition
  receive := fun _ _ _ => groupsPartition

invariant ^69 noMutedNotes "No row from a muted account" for machine where
  does "No notification from a muted account is in any row."
  holds s := NoMutedRow s
  init := noMutedRow _
  step := fun _ _ _ => noMutedRow _
  receive := fun _ _ _ => noMutedRow _

theorem seenOk_any (s : State) : SeenOk s.notes.seen.1 := s.notes.seen.2

invariant ^70 seenInvariant "Seen only once on screen" for machine where
  does "Sky's seen marker is a one-key optimistic entry (Cairn.Optimistic): what shows as seen moves at once, and updateSeen goes to the server in the background, read back when its answer is lost, rolled back when refused. Every updateSeen Sky sends is at least the one before it and at most the mark, and the mark only rises when a row of the list comes into view, to that row's newest notification. So seenAt never decreases and never passes a notification that hasn't been on screen. The fuzz checks the fake server's seenAt against the rows that have been in view."
  holds s := SeenOk s.notes.seen.1 ∧ SeenMonotone ∧ SeenOnScreen
  init := ⟨seenOk_any _, seenMonotone, seenOnScreen⟩
  step := fun s _ _ => ⟨seenOk_any _, seenMonotone, seenOnScreen⟩
  receive := fun s _ _ => ⟨seenOk_any _, seenMonotone, seenOnScreen⟩

theorem notesOut_step (s : State) (c : Cmd) (_h : NotesSignedOut s) : NotesSignedOut (s.step c).1 :=
  step_notesOut s c

invariant ^71 pollInvariant "At most one unread poll" for machine where
  does "Sky polls the unread count every minute, after a refresh of the notifications, at sign-in and once updateSeen is answered, but never with a poll in flight (one due then goes once it answers), so at most one is; signed out it polls nothing, and the notes hold no notifications and wait on no call. The badge (the Notifications button's count; the Dock's in cairn#255) is the last poll's count less the notifications marked seen since it was sent, and none at 0."
  holds s := NotesSignedOut s ∧ PollOnce ∧ BadgeIsCount s
  init := ⟨notesOut_initial, pollOnce, badgeIsCount _⟩
  step := fun s a h => ⟨update_inv (P := NotesSignedOut) notesOut_step s a h.1, pollOnce, badgeIsCount _⟩
  receive := fun s m _ => ⟨step_notesOut s (.msg m), pollOnce, badgeIsCount _⟩

def claimInfos : List ClaimInfo := claims%

def app : App State :=
  { machine.toApp [.window 1 "Sky" view, .menuBar 48 menuBar] claimInfos with
    initEffects
    subscriptions
    minSize }

end Sky
