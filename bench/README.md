# Sky benchmarks

Cairn's M4 "Measured" (cairn's docs/goals/m4.md, cairn#212) for Sky. Cairn's framework numbers
(virtual lists of 100 to 100,000 rows) are in cairn's `bench/`.

Apple M4 Max (Mac16,6), macOS 27.0.1, Lean 4.35.0, Swift 6.4, Bun 1.4.0, Cairn 0.4.0, Sky at
`0713a11`, 2026-10-26, release builds, other agents' builds running (load average 2–3). Two runs
each; ranges are the two.

## Method

`make bench` is `cairn bench`: a release build, then `Sky --bench` (Sources/Sky/Bench.swift)
with `LEAN_ABORT_ON_NONLINEAR=1` and a scratch home. It runs cairn_atproto's fake PDS
(`tools/fake-pds/server.ts`, Bun, 127.0.0.1, seed 20261025, `--base 1000`: 1,000 posts, more
arriving at the head as calls are made) and drives Sky through Cairn's `Engine` and the host's
real world (HTTP, Keychain under a throwaway service, image decoding) as the selftest does, by
clicks, typing and wheel events. No window: a render thread paints every new frame offscreen
with Metal at 2× (600 × 820 points) and waits for the GPU, as the window's display link would.

- **Sign-in → first page**: from the click on Sign in to the first frame showing posts,
  published by the engine and painted by the render thread. 10 sign-ins (each signed out after)
  with 0 and with 100 ms added to every XRPC reply (`/control/slow`).
- **Refresh → new posts**: 3 posts arrive at the head, then from the click on Refresh to the
  frame showing them with "3 new posts". 10 refreshes each way. The fake's tokens last 1 to 6
  calls (`--life 6`), so some refreshes first refresh the session: 3 round trips instead of 1.
- **Flings**: every post loaded first (wheel to the end until "You're all caught up."), back to
  the top, then flings of 117 wheel deltas at 120 Hz (120 points falling 4% a frame to 1: a fast
  trackpad flick's momentum, about 2,900 points), 30 ms apart, down until the first post shown
  stops moving, then the same number back up. Per batch: the Lean step (`cairn_app_step`: update,
  view, layout and settle for the batch's events), encode (`cairn_app_frame`), Swift decode, and
  the Metal render; input → frame from the engine's stats.
- **Memory**: the process's physical footprint (`TASK_VM_INFO`), malloc's bytes in use, what the
  Metal device has allocated, and the image store against Sky's `imageBudget` (96 MiB).

`make bench-lean` (lean/Bench.lean, `lake exe bench`) splits the Lean step by phase: the same
flings through Sky's app in a Lean executable, the host played by cairn_atproto's Lean fake
(`CairnAtproto.Fake`, every request answered in the next frame, images as their sizes), each
frame through `Runtime.step` written out with a clock between its phases, as Cairn's own bench
(cairn's bench/vlist.md) and checked against it. A Lean executable has no Core Text, so text is
measured with `TextMetrics.mono` there.

`make size`, and `cairn bundle --product Sky` for Sky.app.

## Numbers

### Sign-in and refresh (ms, 10 runs)

| | added latency | published p50 / p95 | painted p50 / p95 |
|---|---:|---:|---:|
| sign-in → first page | 0 ms | 74–77 / 91–101 | 78 / 93–109 |
| sign-in → first page | 100 ms | 291–325 / 333–362 | 293–326 / 335–364 |
| refresh → new posts | 0 ms | 19–20 / 124–146 | 21–22 / 125–149 |
| refresh → new posts | 100 ms | 151–153 / 402–411 | 153–155 / 404–413 |

Sign-in is two calls (`createSession`, `getTimeline`) plus writing both tokens to the Keychain;
a refresh one call, or three when the access token has expired (the p95).

### Flings through 1,102 posts with images (ms per frame)

60 flings down, 59–60 back up; about 7,500 frames each way.

| | p50 | p95 | max |
|---|---:|---:|---:|
| Lean thread: step + encode + decode | 1.51–1.72 | 3.64–3.93 | 12.1–18.2 |
| step (update, view, layout, settle) | 1.39–1.60 | 3.41–3.73 | 11.8–18.0 |
| encode | 0.10–0.11 | 0.23–0.24 | 0.7–1.5 |
| decode (Swift) | 0.02 | 0.04 | 0.3–2.2 |
| render (Metal, offscreen 2×, waited) | 1.11–1.20 | 1.63–1.67 | 16.7–31.3 |
| input → frame | 1.54–1.83 | 3.87–4.27 | 15.9–19.5 |

Frames over the 8 ms budget: 26–35 of each pass's ~7,500 Lean steps (0.4%), 1 render. Every
slow step is the first frame of a fling, after the Lean thread sat idle; profiled in
[cairn#241](https://github.com/iamnbutler/cairn/issues/241). Frames are about 8.5 KB.

By phase, in Lean with `TextMetrics.mono` (`make bench-lean`; 1,003 posts, 54 flings down and
back, 12,636 frames; two runs agreed within 1%):

| | frame | update | view | layout | settle | encode |
|---|---:|---:|---:|---:|---:|---:|
| p50 | 0.36 | 0.011 | 0.061 | 0.060 | 0.193 | 0.035 |
| p95 | 0.82 | 0.24 | 0.135 | 0.144 | 0.265 | 0.047 |
| max | 1.9–2.4 | | | | | |

The host's step is about 4× the mono one: text measured by Core Text (400 to 1,200
`cairn_text_metrics` calls a frame, about 0.5 ms for each string not yet shaped) and the
host's load. Settle (the virtual list's record of heights, Cairn's bench/vlist.md) is half of
the Lean frame; update's p95 is the frames whose rows come into view and ask for images.

### Memory

| | footprint | malloc in use | Metal allocated | image store |
|---|---:|---:|---:|---:|
| signed out | 5.5–7.0 MB | 1.0 MB | 0.1 MB | |
| 1,102 posts loaded, at the top | 358–361 MB | 175 MB | 174 MB | |
| after flinging to the end | 615–634 MB | 178–180 MB | 188 MB | 99.3 MB, 72 images |
| back at the top | 611–621 MB | 175–178 MB | 188 MB | 98.3 MB, 62 images |

The image cache budget holds: the store stays under 100.7 MB (96 MiB). The process is about 6×
that: the renderer keeps a mipmapped texture of every image in the store, released textures
stay in the graphics ledger (428 MB at the end) for a while, and images are decoded at full
size. Filed as [cairn#240](https://github.com/iamnbutler/cairn/issues/240).

### Size

| | bytes |
|---|---:|
| Sky.app (`cairn bundle`, ad hoc signed; the executable, Info.plist, signature) | 5,473,578 (5.47 MB) |
| Sky executable, stripped (`make size`; Cairn's limit 5,000,000) | 3,619,024 (3.62 MB) |

Stripped, by origin: Lean's Init and Std 1,173,318 (32.4%), Lean's C runtime, libuv and libgmp
434,995 (12.0%), Cairn's Lean 601,050 (16.6%), Sky's Lean 188,507 (5.2%), the Swift host 941,513
(26.0%; Sky's own target, with the selftest and this bench, 127,847), Metal shader source 4,304,
linker and other 275,337.
