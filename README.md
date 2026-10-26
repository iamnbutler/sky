# Sky

A Bluesky reader on [Cairn](https://github.com/iamnbutler/cairn): Cairn's M4 demo (cairn's
docs/goals/m4.md). Package `sky`, claims `sky^N`. Built only from the registry: Cairn,
cairn_json and cairn_atproto.

Signed out, Sky shows its sign-in screen (cairn#210): handle or email, the app password in a
secure field, the service (`https://bsky.social` unless the `service` default says otherwise),
Sign in, and what went wrong in words. The session's tokens live in the Keychain and go on every
call from there; Lean never holds one. The handle and service are saved in
`~/Library/Application Support/dev.cairn.sky/account.json`, so the next launch resumes the
session; Sky ▸ Sign Out in the menu bar forgets both Keychain items and that file. View ▸
Refresh (⌘R) refreshes the feed, as the header's Refresh does.

Signed in, Sky shows the home feed (cairn#211) in Cairn's virtual list (`VList`): each post's
avatar, name, handle and age, its text wrapped, its images (placeholders until loaded),
"Reposted by" and "Replying to" lines, quotes and link cards in words, and its counts. Clicking a
post (or Return on it) opens it on bsky.app. Scrolling to the end loads more; the end row says
Loading…, "Couldn't load more." with Retry, or "You're all caught up." Refresh puts new posts
above without moving the reader, and offers "↑ N new posts" to go back to the top. Images load
for rows near the view (at most 6 at a time) and are cancelled as the reader moves away.

Under each post (cairn#252, cairn#254): the reply count, then Repost (⇄) and Like (♡/♥)
toggles with their counts (checked as the tables show, greyed while the write is in flight), and
⋯, the post's menu, which the secondary click on the post or a toggle opens too: Follow or
Unfollow and Mute or Unmute its author (on others' posts), Copy Link to Post and Open on
bsky.app. A press shows in the same frame, everywhere the post or account appears, counts
included; Sky then writes the record (or mutes) and settles on the server's answer: a refusal
shows what was there before and says why in the status line for 8 seconds, read out by
VoiceOver; a lost answer is read back from the account's own repo before it is believed. A muted
account's posts, and its reposts, are gone from the feed without moving the post being read:
each row keeps its key and lays a point high. The status line says "Muted @handle" with Undo for
8 seconds; a post quoting a muted account says "Quoted post from an account you muted".

Notifications (cairn#253) show in their own virtual list, one press from the header, whose
button carries the unread count. Likes, reposts and follows of the same post (or of you) next to
each other are one row ("Alice, Bob and 3 others liked your post"); mentions, replies and quotes
are a row each; a muted account's notifications are left out. A row coming into view marks the list seen up to its newest notification: at
once on screen, and with `updateSeen` in the background (Cairn's optimistic entry: read back
when the answer is lost, rolled back in words when refused). Nothing is marked seen that hasn't
been on screen, and what Sky sends never goes back. The unread count is polled every minute,
after a refresh, at sign-in and once the server has the new seen time, at most one poll at a time.

## The model (`lean/Sky`)

- `Feed`: cairn_atproto's paged list of timeline items (`Paged FeedItem`): the items shown
  (keyed by post URI and repost reason), the cursor of the last page, `atEnd`, and at most one
  load-more and one refresh in flight, each with its call id. Load more appends a page only if
  the feed still holds the cursor it asked from; a refresh puts the new posts on top when its
  page reaches the feed's head, and replaces the feed when it doesn't. Proved in cairn_atproto
  (`cairn_atproto^26`–`^29`).
- `Model`: `State.step` drives cairn_atproto's session machine (sign in, resume at launch, sign
  out, expiry and token refresh) and routes its answers to the feed. A refresh withdraws the
  load-more in flight (`cancelRequest`); whenever the session isn't signed in, the feed is
  emptied and every call withdrawn.
- `Acts`: likes, reposts, follows and mutes, each a `Cairn.Optimistic` table (cairn's
  docs/optimistic.md) keyed by post URI or DID. A press sets the table and mints a record key
  (`TidClock`); the table's writes and read-backs become session calls (`putRecord`,
  `deleteRecord`, `getRecord`, `muteActor`, `unmuteActor`), queued and sent in the same step
  (`flush` in `Model`); answers go back through `WriteOutcome` and `ReadBack`. Every page's
  posts and accounts are `seen`, and a post's counts are the newest view's through `count`.
- `Proofs`, `SessionFacts`: what every step keeps, and the moves' posts. `Secrets`: the app
  password reaches exactly one request, redacted, and is cleared as it is sent; signed out, no
  request carries a Keychain secret; Sign out forgets both items.
- `Notifications`: the groups (`groupAll`, proved a partition, in order, of runs of one reason
  and subject, maximal), the seen marker (`Seen`: the mark, a one-key `Cairn.Optimistic` entry,
  the last value sent; `SeenOk` kept by construction) and the notes (the paged list, the poll,
  the unread count and the badge). `NoteProofs`: the notes' handlers, the moves' posts, only a
  row on screen raising the mark, and signed out, no notes and no poll.
- `Rows`: the list's keys (posts put on top get the keys below the first, so nothing below
  moves), and the image loads near the view.
- `View`: the sign-in screen, the feed's and the notifications' virtual lists, a post's menu, and
  the menu bar (Sky ▸ Sign Out, View ▸ Refresh).
- `Claims`: places, moves and invariants. `Fuzz`: the checks against cairn_atproto's fake PDS.

| Id | Kind | Claim |
|---|---|---|
| ^1 | place | the window: the sign-in screen, the feed or the notifications |
| ^2 | move | Sign in (retired: reissued as ^10) |
| ^3 | move | Load more (retired: the end row loads more, ^30 and ^31) |
| ^4 | move | Refresh |
| ^5 | move | Sign out (retired: reissued as ^11 and ^12) |
| ^6 | move | the Handle or email field |
| ^7 | move | the App password field (secure) |
| ^8 | move | the Service field |
| ^9 | move | What's an app password? (opens Bluesky's page) |
| ^10 | move | Sign in: enabled exactly when both fields are typed in and no sign-in is in flight |
| ^11 | move | Sign out, in the account panel (retired: reissued as ^49, in the app menu) |
| ^12 | move | Cancel a sign-in or resume, offered once it has taken a few seconds |
| ^13 | move | Account (retired: the account panel is gone; Sign Out is in the app menu) |
| ^14 | place | the feed: a virtual list of posts and the end row |
| ^20–^23 | invariant | retired: the feed is cairn_atproto's `Paged` list, proved there (`cairn_atproto^26`–`^29`) |
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
| ^37 | move | Like or Unlike a post: the ♡ toggle |
| ^38 | move | Repost or Undo repost: the ⇄ toggle |
| ^39 | move | Follow or Unfollow a post's author, in its menu |
| ^40 | move | Mute or Unmute a post's author, in its menu |
| ^41 | invariant | likes, reposts, follows and mutes settle on the server's; counts through `count` |
| ^42 | invariant | a muted account's posts appear nowhere: their rows lay a point high, with no control |
| ^43 | invariant | signed out ⇒ the acts hold nothing |
| ^44 | invariant | the password reaches one request, redacted, and is cleared as it is sent |
| ^45 | invariant | Sign Out forgets both Keychain items; signed out, no request carries a secret |
| ^46 | invariant | the rows are the feed's posts; posts put on top keep every key below them |
| ^47 | invariant | image loads only for rows near the view; none signed out |
| ^48 | place | Sky's menus in the menu bar |
| ^49 | move | Sign Out, in the app menu |
| ^50 | place | the View menu |
| ^51 | move | View ▸ Refresh, ⌘R |
| ^52 | place | a post's menu: its ⋯ button and the secondary click on the post |
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

## Checking

`make check`: build, lint, axiom audit, ledger, kernel replay, the selftest, `cairn fuzz`
against cairn_atproto's fake PDS (`CairnAtproto.Fake`), size and claims. No network and no real
account. The fuzz types into the form and runs the whole fake PDS as its server
(`Fake.server`): likes, reposts, follows and mutes persist through a sequence, replies fail
before the server acts or are lost after it, other accounts act and the AppView lags; after
every step each settled like, repost, follow and mute Sky wrote, and each settled like count,
is checked against what the server holds. The selftest
(`Sources/Sky/Selftest.swift`, needs [Bun](https://bun.sh)) runs the fake's HTTP server on
127.0.0.1 and drives the app through Cairn's engine: a wrong password, a rate limit, offline and
a slow sign-in, each in words; then signs in by typing, waits for images, scrolls with the wheel,
loads more by scrolling to the end, refreshes with posts arriving (the first post in view stays
put and "3 new posts" is offered, then taken back to the top), opens the notifications, then,
with the fake's replies slowed, likes, unlikes, reposts and follows (from ⋯), has a like refused
and rolled back with its line, has a like's reply lost and settled by a read, mutes an author
mid-feed (their posts gone, the post being read still) and undoes it; quits and resumes, and
signs out from the app menu. It runs with a home of its own (`build/home`), refuses every host but 127.0.0.1,
keeps its Keychain items under a throwaway service it deletes, stops the server, and leaves
offscreen renders of each screen in `build/shots`.

`make act-media` renders liking and muting against the fake offscreen at 30 frames a second
(`Sky --act-frames`) and makes `build/media/act-like.mov` and `act-mute.mov` with ffmpeg.

`make bench` and `make bench-lean`: first page, refresh, flings through 1,000 posts, memory
and size against the fake PDS, with the numbers in [bench/README.md](bench/README.md).

`make app` builds Sky.app for release with `cairn bundle`, signs it with the first Developer ID
Application identity in the keychain (else ad hoc) and installs it in `~/Applications`.

To run the app against the fake PDS over HTTP, see cairn_atproto's README, "Running Sky against
the fake PDS" (Sky's defaults domain is `dev.cairn.sky`).
