# Sky

A Bluesky reader on [Cairn](https://github.com/iamnbutler/cairn): Cairn's M4 demo (cairn's
docs/goals/m4.md). Package `sky`, claims `sky^N`. Built only from the registry: Cairn,
cairn_json and cairn_atproto.

Signed out, Sky shows its sign-in screen (cairn#210): handle or email, the app password in a
secure field, the service (`https://bsky.social` unless the `service` default says otherwise),
Sign in, and what went wrong in words. The session's tokens live in the Keychain and go on every
call from there; Lean never holds one. The handle and service are saved in
`~/Library/Application Support/dev.cairn.sky/account.json`, so the next launch resumes the
session; Sign out (in the account panel) forgets both Keychain items and that file. The feed is
a list of lines for now (cairn#211 adds the real one).

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
- `View`: the sign-in screen, the account panel and the feed.
- `Claims`: places, moves and invariants. `Fuzz`: the checks against cairn_atproto's fake PDS.

| Id | Kind | Claim |
|---|---|---|
| ^1 | place | the window: the sign-in screen, or the feed |
| ^2, ^5 | move | retired (Sign in, Sign out): reissued as ^10, ^11 and ^12 |
| ^3, ^4 | move | Load more, Refresh |
| ^6–^8 | move | the Handle or email, App password (secure) and Service fields |
| ^9 | move | What's an app password? (opens Bluesky's page) |
| ^10 | move | Sign in: enabled exactly when both fields are typed in and no sign-in is in flight |
| ^11 | move | Sign out, in the account panel |
| ^12 | move | Cancel a sign-in or resume, offered once it has taken a few seconds |
| ^13 | move | Account: open or close the account panel |
| ^20 | invariant | the feed is a contiguous run of the server's timeline, in its order |
| ^21 | invariant | a load-more page for a cursor the feed no longer holds changes nothing |
| ^22 | invariant | the cursor is never lost |
| ^23 | invariant | a refresh racing a load-more: either order, the same feed |
| ^24 | invariant | at most one load-more and one refresh in flight; every request answered, cancelled or live |
| ^25 | invariant | signed out ⇒ the feed is empty and nothing is in flight |
| ^26 | invariant | the password reaches one request, redacted, and is cleared as it is sent |
| ^27 | invariant | Sign out forgets both Keychain items; signed out, no request carries a secret |

## Checking

`make check`: build, lint, axiom audit, ledger, kernel replay, the selftest, `cairn fuzz`
against cairn_atproto's fake PDS (`CairnAtproto.Fake`), size and claims. No network and no real
account. The fuzz types into the form and plays the fake as its host. The selftest
(`Sources/Sky/Selftest.swift`, needs [Bun](https://bun.sh)) runs the fake's HTTP server on
127.0.0.1 and drives the app through Cairn's engine: a wrong password, a rate limit, offline and
a slow sign-in, each in words; then signs in by typing, loads more, refreshes, quits and resumes,
and signs out. It runs with a home of its own (`build/home`), refuses every host but 127.0.0.1,
keeps its Keychain items under a throwaway service it deletes, stops the server, and leaves
offscreen renders of each screen in `build/shots`.

To run the app against the fake PDS over HTTP, see cairn_atproto's README, "Running Sky against
the fake PDS" (Sky's defaults domain is `dev.cairn.sky`).
