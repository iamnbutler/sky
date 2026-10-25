# AGENTS

Sky is a Bluesky reader on [Cairn](https://github.com/iamnbutler/cairn): sign in with an app
password, keep the session, and read the home feed, however long it gets. It is Cairn's M4 demo
(cairn's docs/goals/m4.md), built only through Cairn's package path: `cairn new sky --bin`,
`cairn add cairn`, `cairn add cairn_json`, `cairn add cairn_atproto`. Nothing here reaches into
the cairn repository; Cairn, cairn_json and cairn_atproto come from the registry at
https://cairn.registry.nexthub.sh.

## Layout

- `lean/`: the Lake package (scope `sky`). `Sky/` is the app: the headless timeline and session
  model, its claims and proofs, and the exports (`Sky/Abi.lean`).
- `Sources/`: the Swift host (`Sky`, Cairn's AppKit host) and the app's C exports (`CSky`). No
  app logic in Swift.
- `cairn.toml`, `claims.lock`: the package and every `sky^N` claim id ever issued. Tools write
  the lock (`make ledger-update`); never edit it by hand.

## Rules

Cairn's rules apply (cairn's AGENTS.md, "Rules" and "Writing Lean"):

- **No `sorry`, no new axioms.** Only `propext`, `Classical.choice` and `Quot.sound`.
  **Banned:** `implemented_by`, `debug.skipKernelTC`, `native_decide`, `bv_decide`, `axiom`.
- **Ids are the contract.** Never renumber, reuse or delete a claim id; retire it. The registry
  refuses a changed statement hash on a published claim.
- **Pure Lean core; the host stays thin.** Swift performs effects, Lean decides.
- **No credentials, tokens or private timelines** in this repository: no real account in a
  fixture, test, log or file. Tests run against fakes.
- **A gap in Cairn or cairn_atproto** (a missing effect or API, a bug) is fixed upstream, not
  worked around here: open an issue on iamnbutler/cairn.

## Toolchain

`export PATH=$HOME/.elan/bin:$PATH` if `lake` is missing. Lake resolves registry requires with
`RESERVOIR_API_URL=https://cairn.registry.nexthub.sh/api/v1` (the `cairn` CLI and the Makefile
set it). The `cairn` CLI is built from Cairn's `tools/cairn` in the checkout Lake fetched
(`make cairn-tool`). `make build`, `make check`.

## Workflow: lane

Every change happens in a lane, never in the main checkout and never with a bare
`git worktree add`.

1. `lane new <name>` from an up-to-date main, then work in the printed tree.
2. `lane why <path>` before editing a file.
3. Commit as you go. Add a `Why: <path> | <note>` trailer only for a non-obvious constraint.
4. `lane check`; confirm, replace or retire stale notes.
5. `make check` passes.
6. `lane push`, then `gh pr create`. Check `git log --oneline -2` after pushing: the lane must sit
   on current `origin/main`.
7. Squash-merge (`gh pr merge --squash`, no `--delete-branch`), `git pull --ff-only` in the main
   checkout, `lane prune --dry-run`, then `lane rm <name>` for merged lanes prune misses. Never a
   bare `lane prune` while other agents may have lanes open.

<!-- lane:protocol -->
## Context memory

- Before editing a file, read `.lane/memory/<path>/` if it exists, or run `lane why <path>`.
- Record non-obvious findings with `lane note add <path> -a <anchor> "..."`.
- Do not edit `.lane/` by hand; landing manages it.
- Land with `lane merge`, or `lane push` where trunk is protected, then `lane prune` once it merges.
- Detailed workflow lives in `.agents/skills/lane/SKILL.md`; run `lane install skill` if it is absent.
<!-- /lane:protocol -->
