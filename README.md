# Sky

A Bluesky reader on [Cairn](https://github.com/iamnbutler/cairn): Cairn's M4 demo (cairn's
docs/goals/m4.md). Package `sky`, claims `sky^N`. Built only from the registry: Cairn,
cairn_json and cairn_atproto.

For now Sky is its timeline and session as a headless model (cairn#209) behind a bare window;
cairn#210 and cairn#211 add the real view.

## The model (`lean/Sky`)

- `Feed`: the items shown (keyed by post URI and repost reason), the cursor of the last page,
  `atEnd`, and at most one load-more and one refresh in flight, each with its call id. Load more
  appends a page only if the feed still holds the cursor it asked from; a refresh puts the new
  posts on top when its page reaches the feed's head, and replaces the feed when it doesn't.
- `Model`: `State.step` drives cairn_atproto's session machine (sign in, resume at launch, sign
  out, expiry and token refresh) and routes its answers to the feed. A refresh withdraws the
  load-more in flight (`cancelRequest`); whenever the session isn't signed in, the feed is
  emptied and every call withdrawn.
- `Proofs`, `SessionFacts`: what every step keeps, and the moves' posts.
- `Claims`: places, moves and invariants. `Fuzz`: the checks against cairn_atproto's fake PDS.

| Id | Kind | Claim |
|---|---|---|
| ^1 | place | the window (bare until #210) |
| ^2–^5 | move | Sign in, Load more, Refresh, Sign out |
| ^20 | invariant | the feed is a contiguous run of the server's timeline, in its order |
| ^21 | invariant | a load-more page for a cursor the feed no longer holds changes nothing |
| ^22 | invariant | the cursor is never lost |
| ^23 | invariant | a refresh racing a load-more: either order, the same feed |
| ^24 | invariant | at most one load-more and one refresh in flight; every request answered, cancelled or live |
| ^25 | invariant | signed out ⇒ the feed is empty and nothing is in flight |

## Checking

`make check`: build, lint, axiom audit, ledger, kernel replay, the headless selftest, `cairn fuzz`
against cairn_atproto's fake PDS (`CairnAtproto.Fake`), size and claims. No network and no real
account: the fuzz's server is the fake, and the selftest runs with a home of its own.

To run the app against the fake PDS over HTTP, see cairn_atproto's README, "Running Sky against
the fake PDS" (Sky's defaults domain is `dev.cairn.sky`).
