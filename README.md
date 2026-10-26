# Sky

A Bluesky reader on [Cairn](https://github.com/iamnbutler/cairn): Cairn's M4 demo (cairn's
docs/goals/m4.md). Package `sky`, claims `sky^N`. Built only from the registry: Cairn,
cairn_json and cairn_atproto.

Signed out, Sky shows its sign-in screen (cairn#210): handle or email, the app password in a
secure field, the service (`https://bsky.social` unless the `service` default says otherwise),
Sign in, and what went wrong in words. The session's tokens live in the Keychain and go on every
call from there; Lean never holds one. The handle and service are saved in
`~/Library/Application Support/dev.cairn.sky/account.json`, so the next launch resumes the
session; Sign out (in the account panel) forgets both Keychain items and that file.

Signed in, Sky shows the home feed (cairn#211) in Cairn's virtual list (`VList`): each post's
avatar, name, handle and age, its text wrapped, its images (placeholders until loaded),
"Reposted by" and "Replying to" lines, quotes and link cards in words, and its counts. Clicking a
post (or Return on it) opens it on bsky.app. Scrolling to the end loads more; the end row says
Loading…, "Couldn't load more." with Retry, or "You're all caught up." Refresh puts new posts
above without moving the reader, and offers "↑ N new posts" to go back to the top. Images load
for rows near the view (at most 6 at a time) and are cancelled as the reader moves away.

## The model (`lean/Sky`)

- `Feed`: the items shown (keyed by post URI and repost reason), the cursor of the last page,
  `atEnd`, and at most one load-more and one refresh in flight, each with its call id. Load more
  appends a page only if the feed still holds the cursor it asked from; a refresh puts the new
  posts on top when its page reaches the feed's head, and replaces the feed when it doesn't.
- `Model`: `State.step` drives cairn_atproto's session machine (sign in, resume at launch, sign
  out, expiry and token refresh) and routes its answers to the feed. A refresh withdraws the
  load-more in flight (`cancelRequest`); whenever the session isn't signed in, the feed is
  emptied and every call withdrawn.
- `Proofs`, `SessionFacts`: what every step keeps, and the moves' posts. `Secrets`: the app
  password reaches exactly one request, redacted, and is cleared as it is sent; signed out, no
  request carries a Keychain secret; Sign out forgets both items.
- `Rows`: the list's keys (posts put on top get the keys below the first, so nothing below
  moves), and the image loads near the view.
- `View`: the sign-in screen, the account panel and the feed's virtual list.
- `Claims`: places, moves and invariants. `Fuzz`: the checks against cairn_atproto's fake PDS.

| Id | Kind | Claim |
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

## Checking

`make check`: build, lint, axiom audit, ledger, kernel replay, the selftest, `cairn fuzz`
against cairn_atproto's fake PDS (`CairnAtproto.Fake`), size and claims. No network and no real
account. The fuzz types into the form and plays the fake as its host. The selftest
(`Sources/Sky/Selftest.swift`, needs [Bun](https://bun.sh)) runs the fake's HTTP server on
127.0.0.1 and drives the app through Cairn's engine: a wrong password, a rate limit, offline and
a slow sign-in, each in words; then signs in by typing, waits for images, scrolls with the wheel,
loads more by scrolling to the end, refreshes with posts arriving (the first post in view stays
put and "3 new posts" is offered, then taken back to the top), quits and resumes, and signs out. It runs with a home of its own (`build/home`), refuses every host but 127.0.0.1,
keeps its Keychain items under a throwaway service it deletes, stops the server, and leaves
offscreen renders of each screen in `build/shots`.

`make bench` and `make bench-lean`: first page, refresh, flings through 1,000 posts, memory
and size against the fake PDS, with the numbers in [bench/README.md](bench/README.md).

`make app` builds Sky.app for release with `cairn bundle`, signs it with the first Developer ID
Application identity in the keychain (else ad hoc) and installs it in `~/Applications`.

To run the app against the fake PDS over HTTP, see cairn_atproto's README, "Running Sky against
the fake PDS" (Sky's defaults domain is `dev.cairn.sky`).
