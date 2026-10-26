import Sky
import CairnAtproto.Fake

/-! `lake exe bench` (bench/README.md, "Frames by phase"): Sky's feed of 1,000 posts during
trackpad flings, each frame timed by phase (update, view, layout, settle, encode), with the
host played by cairn_atproto's Lean fake PDS (`CairnAtproto.Fake`, cairn#208): every request
answered in the next frame, images as their sizes (`Reply.image`). No network, no Swift, and
`TextMetrics.mono`: a Lean executable has no Core Text, so text is measured as the fallback's
fixed advance (Cairn's `TextMetrics.host`). The Swift bench (`Sky --bench`, Sources/Sky/Bench.swift)
times the same frames with Core Text in the real host.

`timedStep` and `timedFrame` are Cairn's (its lean/Bench.lean, bench/vlist.md), which Cairn
0.4.0 doesn't export. -/

open Cairn CairnAtproto

/-! ## A frame, by phase (as Cairn's lean/Bench.lean) -/

partial def checksum : Laid → Int
  | .box r c _ _ kids => kids.foldl (fun a k => a + checksum k) (r.x + r.y + r.w + r.h + c.w)
  | .text r _ b _ _ => r.x + r.y + r.w + b
  | .field r _ _ _ _ _ _ c _ => r.x + c.x

structure Phases where
  update : Nat := 0
  view : Nat := 0
  layout : Nat := 0
  settle : Nat := 0
  encode : Nat := 0

def Phases.total (p : Phases) : Nat := p.update + p.view + p.layout + p.settle + p.encode

instance : Add Phases where
  add a b := { update := a.update + b.update, view := a.view + b.view, layout := a.layout + b.layout,
               settle := a.settle + b.settle, encode := a.encode + b.encode }

def nodeTag : Node → Nat
  | .box .. => 1
  | _ => 2

/-- `Runtime.step` with a clock between its phases. -/
def timedStep {S : Type} (app : App S) (cfg : Runtime.Config) (s : Runtime.State S) (e : Event) :
    IO (Runtime.State S × Phases) := do
  let t0 ← IO.monoNanosNow
  let (s1, acts) := Runtime.route cfg.metrics s e
  let c0 := Runtime.admit app s e
  if acts.isEmpty && !c0.delivered && Runtime.UI.same s1.ui s.ui then
    let s' := { s1 with world := c0.world }
    let t1 ← IO.monoNanosNow
    return (s', { update := t1 - t0 })
  let c := Runtime.act app c0 acts
  let (subs, cmds, next) :=
    if c.delivered then Runtime.diffSubs c.world.subs (app.subscriptions c.app) c.world.nextSub
    else (c.world.subs, [], c.world.nextSub)
  let ui1 := Runtime.applyFocus c.effs s1.ui
  let surfaces := if c.delivered then Runtime.shows app cfg c.app else s1.surfaces
  if surfaces.length + cmds.length == 1000000 then IO.println "many"
  let t1 ← IO.monoNanosNow
  let node := app.view c.app ui1
  if nodeTag node == 0 then IO.println "no view"
  let t2 ← IO.monoNanosNow
  let laid := cfg.layout cfg.metrics ui1.size node
  if checksum laid == -1 then IO.println "odd"
  let t3 ← IO.monoNanosNow
  let ui' := Runtime.fixUI laid s1.pointer ui1
  let (ui, laid) :=
    if Runtime.UI.same ui' ui1 then (ui', laid)
    else Runtime.settle app cfg c.app s1.pointer ui1 (Runtime.settleFuel - 1) ui'
  if checksum laid == -1 then IO.println "odd"
  let t4 ← IO.monoNanosNow
  let s' := { s1 with app := c.app, ui, laid, world := { c.world with subs, nextSub := next },
                      subCmds := s1.subCmds ++ cmds.toArray, surfaces }
  return (s', { update := t1 - t0, view := t2 - t1, layout := t3 - t2, settle := t4 - t3 })

/-- One frame of `es` (a host batch, `Runtime.stepBytes`, then `Runtime.frameBytes`), by
phase; the effects come from `Runtime.steps`, outside the clock, which must lay the same tree. -/
def timedFrame {S : Type} (app : App S) (cfg : Runtime.Config) (s : Runtime.State S)
    (es : List Event) : IO (Runtime.State S × List Effect × Phases) := do
  let s0 := { s with effects := #[], subCmds := #[] }
  let mut st := s0
  let mut ph : Phases := {}
  for e in es ++ Runtime.frameEvents do
    let (s', p) ← timedStep app cfg st e
    st := s'
    ph := ph + p
  let (r, effs) := Runtime.steps app cfg s0 es
  st := { st with effects := effs.toArray }
  let t0 ← IO.monoNanosNow
  let bytes := Runtime.frameBytes Frame.boundary st
  if bytes.size == 0 then IO.println "empty frame"
  let t1 ← IO.monoNanosNow
  if checksum r.laid != checksum st.laid || !Runtime.UI.same r.ui st.ui then
    throw <| IO.userError "timedStep and Runtime.step disagree"
  return (st, effs, { ph with encode := t1 - t0 })

def pct (ns : Array Nat) (q : Nat) : Float :=
  let a := ns.qsort (· < ·)
  (a[min (a.size - 1) (a.size * q / 100)]!).toFloat / 1e6

def ms3 (x : Float) : String :=
  let n := (x * 1000.0).round.toUInt64.toNat
  s!"{n / 1000}.{(toString (n % 1000 + 1000)).drop 1}"

/-! ## The host -/

def fakeCfg : Fake.Config := { seed := 20261025, base := 1000 }

/-- Sky's runtime state and the fake's world, with the replies due in the next frame. -/
structure Run where
  s : Runtime.State Sky.State
  world : Fake.World
  due : List Event := []
  clock : Nat := 1_000_000
  frames : Array Phases := #[]

/-- What the host answers to `r`: the fake's service as the saved default, no saved account,
images by the size in their URL, HTTP through the fake (with its Keychain), the rest done. -/
def answer (w : Fake.World) : Request → Fake.World × Reply
  | .readDefault _ "service" => (w, .bytes fakeCfg.service.toUTF8)
  | .readFile _ => (w, .failed .notFound "No such file.")
  | .loadImage src _ => match Fake.imageSize (Fake.pathOf src) with
    | some (iw, ih) => (w, .image iw ih)
    | none => (w, .failed .notFound "no image")
  | r@(.http ..) => w.send r
  | .forgetSecret item => (w.forget item, .done)
  | _ => (w, .done)

/-- One frame: the clock 8 ms on, the replies due, then `es`; its requests are answered in the
next. Recorded when `record`. -/
def Run.frame (r : Run) (es : List Event) (record := false) : IO Run := do
  let clock := r.clock + 8
  let batch := [Event.clock { mono := clock, wall := 1793000000000 + clock }] ++ r.due ++ es
  let (s, effs, ph) ← timedFrame Sky.app {} r.s batch
  let mut w := r.world
  let mut due := []
  for e in effs do
    if let .request id q := e then
      let (w', rep) := answer w q
      w := w'
      due := due ++ [.reply id rep]
  return { r with s, world := w, due, clock, frames := if record then r.frames.push ph else r.frames }

/-- Frames with no input until nothing is due (at most `n`). -/
def Run.idle (r : Run) (n := 50) : IO Run := do
  let mut r := r
  for _ in [0:n] do
    if r.due.isEmpty then break
    r ← r.frame []
  return r

def Run.center (r : Run) (c : ControlRef) : IO Point := do
  match Runtime.find r.s.laid c with
  | some t => let v := t.visible; return ⟨v.x + v.w / 2, v.y + v.h / 2⟩
  | none => throw <| IO.userError s!"no control {repr c}"

def Run.click (r : Run) (c : ControlRef) : IO Run := do
  let p ← r.center c
  r.frame [.pointerMove p, .pointerDown p .primary 1 {}, .pointerUp p .primary {}]

def Run.typeIn (r : Run) (c : ControlRef) (text : String) : IO Run := do
  let r ← r.click c
  r.frame [.selectAll, .insertText text]

/-- A point over the feed list: the middle of the window, below the header. -/
def Run.listPoint (_ : Run) : IO Point := pure ⟨300, 450⟩

/-- A trackpad fling's wheel deltas, one per frame: 120 points, falling by 4% a frame until
under one point (about 120 frames, 2,900 points), as Cairn's bench (bench/vlist.md). -/
def fling : Array Int := Id.run do
  let mut v : Nat := 120_000
  let mut out := #[]
  while v ≥ 1000 do
    out := out.push (Int.ofNat (v / 1000))
    v := v * 96 / 100
  return out

def report (label : String) (ps : Array Phases) : IO Unit := do
  let med (f : Phases → Nat) := ms3 (pct (ps.map f) 50)
  let p95 (f : Phases → Nat) := ms3 (pct (ps.map f) 95)
  let tot := ps.map Phases.total
  IO.println s!"{label}, {ps.size} frames: frame p50 {ms3 (pct tot 50)} ms, p95 {ms3 (pct tot 95)} ms, max {ms3 (pct tot 100)} ms"
  IO.println s!"  p50: update {med (·.update)}, view {med (·.view)}, layout {med (·.layout)}, settle {med (·.settle)}, encode {med (·.encode)} ms"
  IO.println s!"  p95: update {p95 (·.update)}, view {p95 (·.view)}, layout {p95 (·.layout)}, settle {p95 (·.settle)}, encode {p95 (·.encode)} ms"

def main : IO Unit := do
  let s := Runtime.start Sky.app {} ⟨600, 820⟩ 200
  let mut r : Run := { s, world := Fake.World.init fakeCfg }
  -- Launch, then sign in by typing (the fake's generated test identifier and app password).
  r ← r.frame []
  r ← r.idle
  r ← r.typeIn ⟨6, 0⟩ fakeCfg.identifier
  r ← r.typeIn ⟨7, 0⟩ fakeCfg.password
  r ← r.click ⟨10, 0⟩
  r ← r.idle
  unless Sky.live r.s.app.session do
    throw <| IO.userError "not signed in"
  -- Load the whole timeline: big wheel steps to the end until the fake has no more.
  let mut p ← r.listPoint
  let mut guard := 0
  while !r.s.app.feed.atEnd && guard < 400 do
    r ← r.frame [.pointerMove p, .scroll p 0 3000]
    r ← r.idle
    guard := guard + 1
  let posts := r.s.app.feed.items.length
  -- Back to the top, images settled.
  r ← r.frame [.scroll p 0 (-100_000_000)]
  r ← r.idle 200
  -- Flings down through the feed until its end, every frame timed.
  p ← r.listPoint
  let mut flings := 0
  let mut last := -1
  while flings < 200 do
    for d in fling do
      r ← r.frame [.scroll p 0 d] (record := true)
    flings := flings + 1
    let off := r.s.ui.scrollOf (Sky.listRef r.s.app)
    if off == last then break
    last := off
  let down := r.frames
  r := { r with frames := #[] }
  -- And flings back up to the top.
  for _ in [0:flings] do
    for d in fling do
      r ← r.frame [.scroll p 0 (-d)] (record := true)
  IO.println s!"Sky, {posts} posts with images (fake PDS, seed {fakeCfg.seed}), 600 × 820 window, TextMetrics.mono"
  IO.println s!"{flings} flings of {fling.size} frames down to the end, offset {last}; {r.s.app.images.known.length} images known"
  report "flings down" down
  report "flings up" r.frames
  report "both" (down ++ r.frames)
