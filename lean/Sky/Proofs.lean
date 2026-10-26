module

public import Sky.Model

/-! # What every step keeps

* `step_inv`: every step keeps `Inv`: the session's requests in flight have distinct ids
  (`RidsOk`); the load-more in flight is a call the session has taken on, asked from the cursor
  the feed holds, of a non-empty feed; the refresh in flight is one too; they are different
  calls; and a feed that isn't at its end holds a cursor (`CursorKept`).
* `step_signedOut`: after every step, with no live session the feed is empty and nothing is in
  flight (`SignedOutEmpty`): `settle` ends every step.

Inside a step Sky folds over the session's outputs (`handleOuts`), so the in-flight facts are
proved in a weaker form, `Q rest`: a call Sky waits on is taken on by the session, or answered
by an output still to come (`rest`). The session's step gives `Q outs` (`SessionFacts`:
`step_kept`), each output keeps it (`handleOut_Q`), and with no outputs left it is `Inv`. -/

@[expose] public section

namespace Sky
open Cairn CairnAtproto CairnAtproto.Session

/-! ## The invariants -/

/-- A feed that isn't at its end holds a cursor: cairn_atproto's `Paged.CursorKept` (cairn_atproto^28). -/
abbrev CursorKept (f : Feed) : Prop := Paged.CursorKept f

/-- The load-more in flight is `pending`, asked from the feed's cursor, of a non-empty feed. -/
def LmOk (pending : Nat → Prop) (s : State) : Prop :=
  match s.feed.loadMore with
  | some (l, c) => pending l ∧ s.feed.cursor = some c ∧ s.feed.items ≠ [] ∧ l < s.nextCall
  | none => True

def RfOk (pending : Nat → Prop) (s : State) : Prop :=
  match s.feed.refresh with
  | some r => pending r ∧ r < s.nextCall
  | none => True

/-- The load-more and the refresh in flight are different calls. -/
def Distinct (f : Feed) : Prop :=
  match f.loadMore, f.refresh with
  | some (l, _), some r => l ≠ r
  | _, _ => True

instance {p : Nat → Prop} [DecidablePred p] (s : State) : Decidable (LmOk p s) := by
  unfold LmOk; split <;> infer_instance

instance {p : Nat → Prop} [DecidablePred p] (s : State) : Decidable (RfOk p s) := by
  unfold RfOk; split <;> infer_instance

instance (f : Feed) : Decidable (Distinct f) := by unfold Distinct; split <;> infer_instance

/-- ^24: at most one load-more and one refresh in flight (by construction), each a call the
session has taken on, and different; the session's requests have distinct ids. With
`CursorKept`. -/
structure Inv (s : State) : Prop where
  rids : RidsOk s.session
  lm : LmOk (· ∈ pids s.session) s
  rf : RfOk (· ∈ pids s.session) s
  dis : Distinct s.feed
  cur : CursorKept s.feed

instance (s : State) : Decidable (Inv s) :=
  decidable_of_iff (RidsOk s.session ∧ LmOk (· ∈ pids s.session) s ∧ RfOk (· ∈ pids s.session) s ∧
      Distinct s.feed ∧ CursorKept s.feed)
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

/-- ^25: with no live session, the feed is empty and nothing is in flight. -/
def SignedOutEmpty (s : State) : Prop :=
  live s.session = false → s.feed = {} ∧ s.session.inflight = [] ∧ s.session.held = []

instance (s : State) : Decidable (SignedOutEmpty s) := by unfold SignedOutEmpty; infer_instance

/-- Inside a fold over the session's outputs: a call waited on is taken on, or answered later. -/
structure Q (rest : List Out) (s : State) : Prop where
  rids : RidsOk s.session
  lm : LmOk (fun x => x ∈ pids s.session ∨ Answered x rest) s
  rf : RfOk (fun x => x ∈ pids s.session ∨ Answered x rest) s
  dis : Distinct s.feed
  cur : CursorKept s.feed

theorem lmOk_mono {p q : Nat → Prop} {s : State} (h : ∀ x, p x → q x) (hl : LmOk p s) :
    LmOk q s := by
  unfold LmOk at *; split at hl <;> simp_all

theorem rfOk_mono {p q : Nat → Prop} {s : State} (h : ∀ x, p x → q x) (hl : RfOk p s) :
    RfOk q s := by
  unfold RfOk at *; split at hl <;> simp_all

theorem answered_nil (x : Nat) : ¬ Answered x [] := fun ⟨_, h⟩ => by simp at h

theorem Q.inv {s : State} (h : Q [] s) : Inv s :=
  ⟨h.rids, lmOk_mono (fun x hx => hx.resolve_right (answered_nil x)) h.lm,
   rfOk_mono (fun x hx => hx.resolve_right (answered_nil x)) h.rf, h.dis, h.cur⟩

/-! ## The feed's handlers -/

theorem cursorKept_empty : CursorKept ({} : Feed) := Paged.cursorKept_empty

theorem cursorKept_gotLoadMore {f : Feed} (h : CursorKept f) (id : Nat)
    (p : Option (Page FeedItem)) : CursorKept (f.gotLoadMore id p) :=
  Paged.cursorKept_gotLoadMore h id p

theorem cursorKept_gotRefresh {f : Feed} (h : CursorKept f) (id : Nat)
    (p : Option (Page FeedItem)) : CursorKept (f.gotRefresh id p) :=
  Paged.cursorKept_gotRefresh h id p

@[simp] theorem gotLoadMore_refresh (f : Feed) (id : Nat) (p : Option (Page FeedItem)) :
    (f.gotLoadMore id p).refresh = f.refresh := by
  unfold Paged.gotLoadMore
  repeat' split
  all_goals rfl

theorem gotLoadMore_lm {f : Feed} {l : Nat} {c : String} (hl : f.loadMore = some (l, c))
    (p : Option (Page FeedItem)) : (f.gotLoadMore l p).loadMore = none := by
  unfold Paged.gotLoadMore
  rw [hl]
  dsimp only
  rw [ite_eq_left_of_eq_true _ _ (eq_self l)]
  split
  · split <;> rfl
  · rfl

theorem gotLoadMore_other {f : Feed} {id : Nat} (h : ∀ c, f.loadMore ≠ some (id, c))
    (p : Option (Page FeedItem)) : f.gotLoadMore id p = f := by
  unfold Paged.gotLoadMore
  split
  · next l c e =>
    split
    · next hl => subst hl; exact absurd e (h c)
    · rfl
  · rfl

theorem gotRefresh_refresh {f : Feed} {id : Nat} (h : f.refresh = some id) (p : Option (Page FeedItem)) :
    (f.gotRefresh id p).refresh = none := by
  unfold Paged.gotRefresh
  simp only [h, ↓reduceIte]
  split
  · unfold Paged.headPage; split <;> rfl
  · rfl

theorem gotRefresh_other {f : Feed} {id : Nat} (h : f.refresh ≠ some id) (p : Option (Page FeedItem)) :
    f.gotRefresh id p = f := by
  simp [Paged.gotRefresh, h]

/-- After a refresh's answer, a load-more still in flight is the one before, the cursor is the
same and the items no fewer. -/
theorem gotRefresh_lm {f : Feed} {id : Nat} {p : Option (Page FeedItem)} {x : Nat × String}
    (h : (f.gotRefresh id p).loadMore = some x) :
    f.loadMore = some x ∧ (f.gotRefresh id p).cursor = f.cursor ∧
      (f.items ≠ [] → (f.gotRefresh id p).items ≠ []) := by
  unfold Paged.gotRefresh at *
  by_cases hr : f.refresh = some id
  · simp only [hr, ite_true] at h ⊢
    cases p with
    | none => exact ⟨h, by simp, fun x => x⟩
    | some q =>
      simp only at h ⊢
      unfold Paged.headPage at *
      cases hn : newOnTop f.items q.items with
      | none => simp [hn, Paged.replaceBy] at h
      | some new =>
        simp only [hn] at h ⊢
        refine ⟨h, by simp, fun hne => ?_⟩
        simp [hne]
  · simp only [hr, ite_false] at h ⊢
    exact ⟨h, by simp, fun x => x⟩

/-! ## One output -/

theorem answered_tail {x : Nat} {o : Out} {rest : List Out} (h : Answered x (o :: rest))
    (ho : ∀ a, o ≠ .answer x a) : Answered x rest := by
  obtain ⟨a, ha⟩ := h
  rcases List.mem_cons.1 ha with e | e
  · exact absurd e.symm (ho a)
  · exact ⟨a, e⟩

theorem Q.tail {s : State} {o : Out} {rest : List Out} (h : Q (o :: rest) s)
    (ho : ∀ x a, o = .answer x a → (∀ l c, s.feed.loadMore = some (l, c) → x ≠ l) ∧
      (∀ r, s.feed.refresh = some r → x ≠ r)) : Q rest s := by
  refine ⟨h.rids, ?_, ?_, h.dis, h.cur⟩
  · have hl := h.lm
    unfold LmOk at hl ⊢
    split at hl
    · next l c e =>
      refine ⟨?_, hl.2⟩
      rcases hl.1 with hm | ha
      · exact Or.inl hm
      · exact Or.inr (answered_tail ha fun a e' => (ho l a e').1 l c e rfl)
    · trivial
  · have hr := h.rf
    unfold RfOk at hr ⊢
    split at hr
    · next r e =>
      refine ⟨?_, hr.2⟩
      rcases hr.1 with hm | ha
      · exact Or.inl hm
      · exact Or.inr (answered_tail ha fun a e' => (ho r a e').2 r e rfl)
    · trivial

theorem withdraw_fst (ss : Session.State) (l : Nat) :
    (withdraw ss l).1 = { ss with inflight := ss.inflight.filter (fun x => x.2.id ∉ [l]),
                                  held := ss.held.filter (fun p => p.id ∉ [l]) } := cancel_fst ss [l]

theorem pids_withdraw (ss : Session.State) (l : Nat) {x : Nat} (hx : x ∈ pids ss) (hl : x ≠ l) :
    x ∈ pids (withdraw ss l).1 := by
  rw [withdraw_fst]
  simp only [pids, List.mem_append, List.mem_map, List.mem_filter, List.mem_singleton,
    decide_eq_true_eq] at hx ⊢
  rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
  · exact Or.inl ⟨y, ⟨hy, hl⟩, rfl⟩
  · exact Or.inr ⟨y, ⟨hy, hl⟩, rfl⟩

theorem ridsOk_withdraw {ss : Session.State} (h : RidsOk ss) (l : Nat) :
    RidsOk (withdraw ss l).1 := by
  rw [withdraw_fst]; exact ridsOk_filter h _ rfl (Nat.le_refl _)

theorem onAnswer0_Q {s : State} {id : Nat} {a : Answer} {rest : List Out}
    (h : Q (.answer id a :: rest) s) : Q rest (onAnswer0 s id a).1 := by
  have hl := h.lm
  have hr := h.rf
  have hd := h.dis
  unfold onAnswer0
  generalize readPage a = pr
  obtain ⟨page, prob⟩ := pr
  dsimp only
  split
  · next l c hlm =>
    simp only [LmOk, hlm] at hl
    split
    · -- The load-more's answer.
      next hli =>
      subst hli
      refine ⟨h.rids, ?_, ?_, ?_, cursorKept_gotLoadMore h.cur _ _⟩
      · simp [LmOk, gotLoadMore_lm hlm]
      · unfold RfOk at hr ⊢
        simp only [gotLoadMore_refresh]
        split at hr
        · next r hrf =>
          try rw [hrf]
          refine ⟨?_, hr.2⟩
          rcases hr.1 with hm | ha
          · exact Or.inl hm
          · refine Or.inr (answered_tail ha fun a' e => ?_)
            cases e
            simp only [Distinct, hlm, hrf] at hd
            exact hd rfl
        · next hrf => (try rw [hrf]); trivial
      · simp [Distinct, gotLoadMore_lm hlm]
    · next hne =>
      split
      · -- The refresh's answer, with a load-more in flight.
        next hrf =>
        have hlid : ∀ a', Out.answer id a = Out.answer l a' → False := fun a' e => by
          cases e; exact hne rfl
        have lmTail : l ∈ pids s.session ∨ Answered l rest := by
          rcases hl.1 with hm | ha
          · exact Or.inl hm
          · exact Or.inr (answered_tail ha fun a' e => hlid a' e)
        try dsimp only
        split
        · next hnone =>
          refine ⟨ridsOk_withdraw h.rids l, ?_, ?_, ?_, cursorKept_gotRefresh h.cur _ _⟩
          · simp only [LmOk]
            rw [Option.isNone_iff_eq_none.mp hnone]; trivial
          · simp [RfOk, gotRefresh_refresh hrf]
          · simp [Distinct, gotRefresh_refresh hrf]
        · next hsome =>
          rcases hx : (s.feed.gotRefresh id page).loadMore with _ | x
          · simp [hx] at hsome
          · obtain ⟨e1, e2, e3⟩ := gotRefresh_lm hx
            rw [hlm] at e1
            cases e1
            refine ⟨h.rids, ?_, ?_, ?_, cursorKept_gotRefresh h.cur _ _⟩
            · simp only [LmOk, hx]
              exact ⟨lmTail, e2.trans hl.2.1, e3 hl.2.2.1, hl.2.2.2⟩
            · simp [RfOk, gotRefresh_refresh hrf]
            · simp [Distinct, gotRefresh_refresh hrf]
      · next hrf =>
        refine (h.tail fun x a' e => ?_)
        cases e
        exact ⟨fun l' c' e' => (by rw [hlm] at e'; cases e'; exact fun e => hne e.symm),
          fun r e' e => hrf (by rw [e]; exact e')⟩
  · next hlm =>
    split
    · next hrf =>
      refine ⟨h.rids, ?_, ?_, ?_, cursorKept_gotRefresh h.cur _ _⟩
      · simp only [LmOk]
        cases hx : (s.feed.gotRefresh id page).loadMore with
        | none => trivial
        | some x =>
          have := (gotRefresh_lm hx).1
          rw [hlm] at this; cases this
      · simp [RfOk, gotRefresh_refresh hrf]
      · simp [Distinct, gotRefresh_refresh hrf]
    · next hrf =>
      refine (h.tail fun x a' e => ?_)
      cases e
      exact ⟨fun l' c' e' => (by rw [hlm] at e'; cases e'),
        fun r e' e => hrf (by rw [e]; exact e')⟩

/-- `Q` reads only the session, the feed and the call ids. -/
theorem Q.other {rest : List Out} {s t : State} (h : Q rest s) (e1 : t.session = s.session)
    (e2 : t.feed = s.feed) (e3 : t.nextCall = s.nextCall) : Q rest t := by
  obtain ⟨a, b, c, d, f⟩ := h
  cases t; cases s; simp only at e1 e2 e3; subst e1 e2 e3
  exact ⟨a, b, c, d, f⟩

/-- The acts' share of an answer touches neither the session nor the feed. -/
theorem onAnswer_Q {s : State} {id : Nat} {a : Answer} {rest : List Out}
    (h : Q (.answer id a :: rest) s) : Q rest (onAnswer s id a).1 :=
  (onAnswer0_Q h).other rfl rfl rfl

theorem handleOut_Q {s : State} {es : List Effect} {o : Out} {rest : List Out}
    (h : Q (o :: rest) s) : Q rest (handleOut (s, es) o).1 := by
  cases o with
  | send rid k ht => exact h.tail fun _ _ e => by cases e
  | forget rid item =>
    have h' := h.tail fun _ _ e' => by cases e'
    exact ⟨h'.rids, h'.lm, h'.rf, h'.dis, h'.cur⟩
  | cancel rid => exact h.tail fun _ _ e => by cases e
  | answer id a => exact onAnswer_Q h
  | event e =>
    have h' := h.tail fun _ _ e' => by cases e'
    simp only [handleOut]
    cases e with
    | signInFailed r => exact ⟨h'.rids, h'.lm, h'.rf, h'.dis, h'.cur⟩
    | refreshFailed r => exact ⟨h'.rids, h'.lm, h'.rf, h'.dis, h'.cur⟩
    | signedOut why => cases why <;> exact ⟨h'.rids, h'.lm, h'.rf, h'.dis, h'.cur⟩
    | signedIn a => exact ⟨h'.rids, h'.lm, h'.rf, h'.dis, h'.cur⟩
    | refreshed a => exact h'
    | busy => exact h'

theorem foldl_Q : ∀ (outs : List Out) (s : State) (es : List Effect), Q outs s →
    Q [] (outs.foldl handleOut (s, es)).1
  | [], _, _, h => h
  | o :: rest, s, es, h => by
    simp only [List.foldl_cons]
    have := handleOut_Q (es := es) h
    exact foldl_Q rest _ _ this

theorem handleOuts_inv {s : State} {outs : List Out} (h : Q outs s) :
    Inv (handleOuts s outs).1 := (foldl_Q outs s [] h).inv

/-! ## Driving the session -/

/-- A call the app makes with a live session is taken on. -/
theorem call_taken {ss : Session.State} (h : live ss = true) (id : Nat) (c : Call) :
    id ∈ pids (Session.step ss (.call id c)).1 := by
  simp only [Session.step]
  unfold live at h
  split
  · simp [sendCall, pids]
  · simp [pids]
  · next hn1 hn2 =>
    exfalso
    split at h
    · exact hn1 _ (by assumption)
    · exact hn2 _ _ _ (by assumption)
    · exact absurd h (by simp)

/-- Driving the session from a state whose calls are taken on, or (when the input is that call,
with a live session) about to be. -/
theorem drive_inv {s : State} {i : Session.Input} (hr : RidsOk s.session)
    (hp : ∀ x, x ∈ pids s.session ∨ (∃ c, i = .call x c) ∧ live s.session = true →
      x ∈ pids (Session.step s.session i).1 ∨ Answered x (Session.step s.session i).2)
    (hl : LmOk (fun x => x ∈ pids s.session ∨ (∃ c, i = .call x c) ∧ live s.session = true) s)
    (hf : RfOk (fun x => x ∈ pids s.session ∨ (∃ c, i = .call x c) ∧ live s.session = true) s)
    (hd : Distinct s.feed) (hc : CursorKept s.feed) : Inv (drive s i).1 := by
  apply handleOuts_inv
  exact ⟨step_ridsOk hr i, lmOk_mono hp hl, rfOk_mono hp hf, hd, hc⟩

theorem pending_of {s : State} {i : Session.Input} (hr : RidsOk s.session) (hc : NotCancel i)
    (x : Nat) (h : x ∈ pids s.session ∨ (∃ c, i = .call x c) ∧ live s.session = true) :
    x ∈ pids (Session.step s.session i).1 ∨ Answered x (Session.step s.session i).2 := by
  rcases h with hm | ⟨⟨c, rfl⟩, hlive⟩
  · exact step_kept hr _ hc x hm
  · exact Or.inl (call_taken hlive x c)

/-- Driving the session from a state that keeps `Inv` (any input but a new call). -/
theorem drive_inv_of {s : State} (h : Inv s) (i : Session.Input) (hc : NotCancel i) :
    Inv (drive s i).1 :=
  drive_inv h.rids (pending_of h.rids hc) (lmOk_mono (fun _ hx => Or.inl hx) h.lm)
    (rfOk_mono (fun _ hx => Or.inl hx) h.rf) h.dis h.cur

theorem live_withdraw (ss : Session.State) (l : Nat) : live (withdraw ss l).1 = live ss := rfl

theorem startRefresh_core {s : State} (h : Inv s) (hlive : live s.session = true)
    (ss : Session.State) (hr : RidsOk ss) (hl : live ss = live s.session) :
    Inv (drive { s with session := ss, nextCall := s.nextCall + 1,
                        feed := { s.feed with loadMore := none, refresh := some s.nextCall } }
      (.call s.nextCall (Call.getTimeline (some pageSize)))).1 :=
  drive_inv hr (pending_of hr trivial) (by simp [LmOk])
    (by simp only [RfOk]; exact ⟨Or.inr ⟨⟨_, rfl⟩, hl.trans hlive⟩, Nat.lt_succ_self _⟩)
    (by simp [Distinct]) (fun a b => h.cur a b)

theorem startRefresh_inv {s : State} (h : Inv s) : Inv (startRefresh s).1 := by
  unfold startRefresh
  split
  · next hc =>
    simp only [Bool.and_eq_true] at hc
    obtain ⟨hlive, _⟩ := hc
    rcases hlm : s.feed.loadMore with _ | ⟨l, c⟩
    · exact startRefresh_core h hlive s.session h.rids rfl
    · exact startRefresh_core h hlive _ (ridsOk_withdraw h.rids l) rfl
  · exact h

theorem startLoadMore_inv {s : State} (h : Inv s) : Inv (startLoadMore s).1 := by
  unfold startLoadMore
  split
  · next c hcan hcur =>
    simp only [canLoadMore, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      Option.isNone_iff_eq_none] at hcan
    obtain ⟨⟨⟨⟨hlive, hlm⟩, hne⟩, _⟩, _⟩ := hcan
    show Inv (drive { s with nextCall := s.nextCall + 1, feed := { s.feed with loadMore := some (s.nextCall, c) }, moreFailed := false } (.call s.nextCall (Call.getTimeline (some pageSize) (some c)))).1
    apply drive_inv
    · exact h.rids
    · exact pending_of h.rids trivial
    · simp only [LmOk]
      exact ⟨Or.inr ⟨⟨_, rfl⟩, hlive⟩, hcur, hne, Nat.lt_succ_self _⟩
    · have hr := h.rf
      simp only [RfOk] at hr ⊢
      split at hr
      · exact ⟨Or.inl hr.1, Nat.lt_succ_of_lt hr.2⟩
      · trivial
    · have hr := h.rf
      simp only [Distinct, RfOk] at hr ⊢
      split at hr
      · next r hrf =>
        rw [hrf]
        exact fun e => by subst e; exact Nat.lt_irrefl _ hr.2
      · next hrf => rw [hrf]; trivial
    · exact h.cur
  · exact h

theorem driveSession_inv {s : State} (h : Inv s) (i : Session.Input) (hc : NotCancel i) :
    Inv (driveSession s i).1 := by
  unfold driveSession
  try dsimp only
  split
  · exact startRefresh_inv (drive_inv_of h i hc)
  · exact drive_inv_of h i hc

/-- `Inv` reads only the session, the feed and the call ids. -/
theorem Inv.other {s t : State} (h : Inv s) (e1 : t.session = s.session) (e2 : t.feed = s.feed)
    (e3 : t.nextCall = s.nextCall) : Inv t := by
  obtain ⟨a, b, c, d, f⟩ := h
  cases t; cases s; simp only at e1 e2 e3; subst e1 e2 e3
  exact ⟨a, b, c, d, f⟩

theorem sendOwn_inv {s : State} (h : Inv s) (k : Own) (r : Request) : Inv (sendOwn s k r).1 :=
  h.other rfl rfl rfl

theorem loadSources_core : ∀ (s : State) (srcs : List String),
    (loadSources s srcs).1.session = s.session ∧ (loadSources s srcs).1.feed = s.feed ∧
      (loadSources s srcs).1.nextCall = s.nextCall ∧ (loadSources s srcs).1.password = s.password ∧
      (loadSources s srcs).1.rows = s.rows
  | _, [] => ⟨rfl, rfl, rfl, rfl, rfl⟩
  | s, src :: rest => by
    simp only [loadSources]
    split
    · exact loadSources_core _ rest
    · exact loadSources_core s rest

theorem appearRow_core (s : State) (k : Nat) :
    (appearRow s k).1.session = s.session ∧ (appearRow s k).1.feed = s.feed ∧
      (appearRow s k).1.nextCall = s.nextCall ∧ (appearRow s k).1.password = s.password ∧
      (appearRow s k).1.rows = s.rows := by
  unfold appearRow
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact loadSources_core _ _

theorem loadSources_acts : ∀ (s : State) (srcs : List String), (loadSources s srcs).1.acts = s.acts
  | _, [] => rfl
  | s, src :: rest => by
    simp only [loadSources]
    split
    · exact loadSources_acts _ rest
    · exact loadSources_acts s rest

theorem appearRow_acts (s : State) (k : Nat) : (appearRow s k).1.acts = s.acts := by
  unfold appearRow
  split
  · rfl
  · exact loadSources_acts _ _

theorem appearRow_inv {s : State} (h : Inv s) (k : Nat) : Inv (appearRow s k).1 :=
  h.other (appearRow_core s k).1 (appearRow_core s k).2.1 (appearRow_core s k).2.2.1

theorem step0_inv {s : State} (h : Inv s) (c : Cmd) : Inv (step0 s c).1 := by
  cases c with
  | signIn =>
    simp only [step0, signIn]
    split
    · refine driveSession_inv ?_ _ trivial; exact h.other rfl rfl rfl
    · exact h
  | loadMore => exact startLoadMore_inv h
  | refresh => exact startRefresh_inv h
  | signOut =>
    simp only [step0, signOut]
    refine sendOwn_inv (driveSession_inv ?_ .signOut trivial) _ _; exact h.other rfl rfl rfl
  | editIdentifier op => exact h.other rfl rfl rfl
  | editPassword op => exact h.other rfl rfl rfl
  | editService op => exact h.other rfl rfl rfl
  | nextField => exact h
  | toggleAccount => exact h.other rfl rfl rfl
  | openHelp => exact sendOwn_inv h _ _
  | appearRow k => exact appearRow_inv h k
  | openPost k =>
    simp only [step0, Sky.openPost]
    split
    · exact sendOwn_inv h _ _
    · exact h
  | showNew => exact h.other rfl rfl rfl
  | act kind k =>
    simp only [step0, actPress]
    split
    · split
      · split <;> exact h.other rfl rfl rfl
      · exact h
    · exact h
  | msg m =>
    simp only [step0]
    cases m with
    | reply id r =>
      simp only [receive0]
      split
      · next k _ =>
        have hb : Inv { s with own := s.own.filter (·.1 != id) } := h.other rfl rfl rfl
        cases k with
        | readService =>
          simp only [onReadService]
          exact sendOwn_inv (by split <;> (try split) <;> (try split) <;> exact hb.other rfl rfl rfl) _ _
        | readAccount =>
          simp only [onReadAccount]
          split
          · split
            · dsimp only; refine driveSession_inv ?_ (.resume _) trivial; exact hb.other rfl rfl rfl
            · exact hb
          · exact hb
        | save => exact hb
        | delete => exact hb
        | openHelp => exact hb
        | openPost => exact hb
      · split
        · refine driveSession_inv ?_ _ trivial; exact h.other rfl rfl rfl
        · split
          · exact h.other rfl rfl rfl
          · exact h
    | timer n =>
      simp only [receive0]
      split <;> exact h.other rfl rfl rfl
    | clock t => exact h.other rfl rfl rfl
    | sub sb e => cases e <;> first | exact h.other rfl rfl rfl | exact h

theorem settle_fst (s : State) :
    (settle s).1 = if live s.session then s
      else { s with feed := {}, session := { s.session with inflight := [], held := [] },
                    acts := {} } := by
  unfold settle; split <;> simp_all [cancel_all]

theorem settle_inv {s : State} (h : Inv s) : Inv (settle s).1 := by
  rw [settle_fst]
  split
  · exact h
  · exact ⟨⟨by simp, by simp⟩, by simp [LmOk], by simp [RfOk], by simp [Distinct], cursorKept_empty⟩

theorem settle_signedOut (s : State) : SignedOutEmpty (settle s).1 := by
  rw [settle_fst]
  split
  · next hl => intro h; simp_all
  · intro _; exact ⟨rfl, rfl, rfl⟩

/-- `tidy` changes only the rows, the list's generation, the new posts, the load-more's failure
and the images. -/
theorem tidy_shape (s : State) : ∃ r g f m im,
    (tidy s).1 = { s with rows := r, gen := g, fresh := f, moreFailed := m, images := im } := by
  unfold tidy restart
  split
  · split
    · exact ⟨s.rows, s.gen, s.fresh, s.moreFailed, s.images, rfl⟩
    · split
      · exact ⟨_, s.gen, _, s.moreFailed, s.images, rfl⟩
      · exact ⟨_, _, _, _, _, rfl⟩
    · split
      · exact ⟨_, _, _, _, _, rfl⟩
      · exact ⟨_, s.gen, s.fresh, s.moreFailed, s.images, rfl⟩
    · exact ⟨_, _, _, _, _, rfl⟩
  · exact ⟨_, s.gen, _, _, _, rfl⟩

structure Core (s t : State) : Prop where
  session : t.session = s.session
  feed : t.feed = s.feed
  nextCall : t.nextCall = s.nextCall
  password : t.password = s.password
  identifier : t.identifier = s.identifier
  service : t.service = s.service
  accountOpen : t.accountOpen = s.accountOpen

theorem tidy_core (s : State) : Core s (tidy s).1 := by
  obtain ⟨r, g, f, m, im, e⟩ := tidy_shape s
  rw [e]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tidy_inv {s : State} (h : Inv s) : Inv (tidy s).1 :=
  h.other (tidy_core s).session (tidy_core s).feed (tidy_core s).nextCall

theorem tidy_signedOut {s : State} (h : SignedOutEmpty s) : SignedOutEmpty (tidy s).1 := by
  unfold SignedOutEmpty at *
  rw [(tidy_core s).session, (tidy_core s).feed]; exact h

/-! ## Sending the acts' calls -/

/-- `Inv` holds with any later next call id. -/
theorem Inv.bump {s : State} (h : Inv s) (n : Nat) (hn : s.nextCall ≤ n) :
    Inv { s with nextCall := n } := by
  obtain ⟨a, b, c, d, f⟩ := h
  refine ⟨a, ?_, ?_, d, f⟩
  · unfold LmOk at b ⊢; split at b
    · next l c' e => simp only [e]; exact ⟨b.1, b.2.1, b.2.2.1, Nat.lt_of_lt_of_le b.2.2.2 hn⟩
    · next e => simp only [e]
  · unfold RfOk at c ⊢; split at c
    · next r e => simp only [e]; exact ⟨c.1, Nat.lt_of_lt_of_le c.2 hn⟩
    · next e => simp only [e]

theorem flushJobs_inv : ∀ (js : List Job) {s : State}, Inv s → Inv (flushJobs s js).1
  | [], _, h => h
  | .effect _ :: js, _, h => flushJobs_inv js h
  | .call q c :: js, s, h => by
    simp only [flushJobs]
    apply flushJobs_inv js
    refine drive_inv_of ?_ _ trivial
    have hb := h.bump (s.nextCall + 1) (Nat.le_succ _)
    exact hb.other rfl rfl rfl

theorem flush_inv {s : State} (h : Inv s) : Inv (flush s).1 := by
  unfold flush
  split
  · exact h
  · split
    · exact flushJobs_inv _ (h.other rfl rfl rfl)
    · exact h.other rfl rfl rfl

theorem flushIf_inv {s : State} (h : Inv s) (b : Bool) : Inv (flushIf b s).1 := by
  unfold flushIf; split
  · exact flush_inv h
  · exact h

theorem step1_fst (s : State) (c : Cmd) :
    (step1 s c).1 = (tidy (settle (flushIf (live s.session) (step0 (clearOut s) c).1).1).1).1 := rfl

theorem step1_inv {s : State} (h : Inv s) (c : Cmd) : Inv (step1 s c).1 := by
  rw [step1_fst]
  exact tidy_inv (settle_inv (flushIf_inv (step0_inv (s := clearOut s) (h.other rfl rfl rfl) c) _))

/-- Every command but sign in and the password's edits runs blind. -/
theorem step_blind (s : State) (c : Cmd) (h1 : c ≠ .signIn) (h2 : ∀ op, c ≠ .editPassword op) :
    s.step c = ({ (step1 s.blank c).1 with password := s.password }, (step1 s.blank c).2) := by
  cases c with
  | signIn => exact absurd rfl h1
  | editPassword op => exact absurd rfl (h2 op)
  | _ => rfl

theorem step_cases (s : State) (c : Cmd) :
    s.step c = step1 s c ∨
      s.step c = ({ (step1 s.blank c).1 with password := s.password }, (step1 s.blank c).2) := by
  cases c
  case signIn => exact Or.inl rfl
  case editPassword => exact Or.inl rfl
  all_goals exact Or.inr rfl

theorem step_inv {s : State} (h : Inv s) (c : Cmd) : Inv (s.step c).1 := by
  rcases step_cases s c with e | e <;> rw [e]
  · exact step1_inv h c
  · exact (step1_inv (s := s.blank) (h.other rfl rfl rfl) c).other rfl rfl rfl

theorem step_signedOut (s : State) (c : Cmd) : SignedOutEmpty (s.step c).1 := by
  rcases step_cases s c with e | e <;> rw [e]
  · rw [step1_fst]; exact tidy_signedOut (settle_signedOut _)
  · show SignedOutEmpty (step1 s.blank c).1
    rw [step1_fst]; exact tidy_signedOut (settle_signedOut _)

theorem inv_initial : Inv initial :=
  ⟨ridsOk_init, by simp [LmOk, initial], by simp [RfOk, initial], by simp [Distinct, initial],
   cursorKept_empty⟩


/-! ## What a move does (the moves' posts) -/

/-- What every output leaves alone: the password field, the call ids, the session's phase. -/
structure Same (s s' : State) : Prop where
  password : s'.password = s.password
  nextCall : s'.nextCall = s.nextCall
  phase : s'.session.phase = s.session.phase

theorem Same.refl (s : State) : Same s s := ⟨rfl, rfl, rfl⟩

theorem Same.trans {a b c : State} (h1 : Same a b) (h2 : Same b c) : Same a c :=
  ⟨h2.password.trans h1.password, h2.nextCall.trans h1.nextCall, h2.phase.trans h1.phase⟩

theorem onAnswer0_same (s : State) (id : Nat) (a : Answer) : Same s (onAnswer0 s id a).1 := by
  unfold onAnswer0
  generalize readPage a = pr
  obtain ⟨page, prob⟩ := pr
  dsimp only
  split
  · split
    · exact ⟨rfl, rfl, rfl⟩
    · split
      · try dsimp only
        split
        · exact ⟨rfl, rfl, rfl⟩
        · exact ⟨rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩

theorem onAnswer_same (s : State) (id : Nat) (a : Answer) : Same s (onAnswer s id a).1 :=
  have h := onAnswer0_same s id a
  ⟨h.password, h.nextCall, h.phase⟩

theorem handleOut_same (acc : State × List Effect) (o : Out) : Same acc.1 (handleOut acc o).1 := by
  cases o with
  | send => exact Same.refl _
  | forget => exact ⟨rfl, rfl, rfl⟩
  | cancel => exact Same.refl _
  | answer id a => exact onAnswer_same _ _ _
  | event e => cases e <;> first | exact ⟨rfl, rfl, rfl⟩ | (rename_i x; cases x <;> exact ⟨rfl, rfl, rfl⟩)

theorem handleOut_quiet (acc : State × List Effect) (o : Out) (h : ∀ x a, o ≠ .answer x a) :
    (handleOut acc o).1.feed = acc.1.feed ∧ (handleOut acc o).1.session = acc.1.session := by
  cases o with
  | send => exact ⟨rfl, rfl⟩
  | forget => exact ⟨rfl, rfl⟩
  | cancel => exact ⟨rfl, rfl⟩
  | answer id a => exact absurd rfl (h id a)
  | event e => cases e <;> first | exact ⟨rfl, rfl⟩ | (rename_i x; cases x <;> exact ⟨rfl, rfl⟩)

theorem foldl_same : ∀ (outs : List Out) (acc : State × List Effect),
    Same acc.1 (outs.foldl handleOut acc).1
  | [], _ => Same.refl _
  | o :: rest, acc => (handleOut_same acc o).trans (foldl_same rest _)

theorem foldl_quiet : ∀ (outs : List Out) (acc : State × List Effect),
    (∀ o ∈ outs, ∀ x a, o ≠ .answer x a) →
    (outs.foldl handleOut acc).1.feed = acc.1.feed ∧
      (outs.foldl handleOut acc).1.session = acc.1.session
  | [], _, _ => ⟨rfl, rfl⟩
  | o :: rest, acc, h => by
    have h1 := handleOut_quiet acc o (h o (List.mem_cons_self ..))
    have h2 := foldl_quiet rest (handleOut acc o) (fun o' ho => h o' (List.mem_cons_of_mem _ ho))
    exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem drive_same (s : State) (i : Session.Input) :
    (drive s i).1.password = s.password ∧ (drive s i).1.nextCall = s.nextCall ∧
      (drive s i).1.session.phase = (Session.step s.session i).1.phase := by
  have := foldl_same (Session.step s.session i).2 ({ s with session := (Session.step s.session i).1 }, [])
  exact ⟨this.password, this.nextCall, this.phase⟩

/-- A call with a live session puts out no answer, and leaves it live. -/
theorem call_quiet {ss : Session.State} (h : live ss = true) (id : Nat) (c : Call) :
    (∀ o ∈ (Session.step ss (.call id c)).2, ∀ x a, o ≠ .answer x a) ∧
      (Session.step ss (.call id c)).1.phase = ss.phase := by
  simp only [Session.step]
  unfold live at h
  split
  · simp [sendCall]
  · simp
  · next hn1 hn2 =>
    exfalso
    split at h
    · exact hn1 _ (by assumption)
    · exact hn2 _ _ _ (by assumption)
    · exact absurd h (by simp)

theorem drive_call {s : State} (h : live s.session = true) (id : Nat) (c : Call) :
    (drive s (.call id c)).1.feed = s.feed ∧ live (drive s (.call id c)).1.session = true ∧
      (drive s (.call id c)).1.nextCall = s.nextCall := by
  have hq := call_quiet h id c
  have := foldl_quiet _ ({ s with session := (Session.step s.session (.call id c)).1 }, []) hq.1
  refine ⟨this.1, ?_, (drive_same s _).2.1⟩
  have hp := (drive_same s (.call id c)).2.2
  unfold live at h ⊢
  rw [hp, hq.2]
  exact h

theorem settle_live {s : State} (h : live s.session = true) : (settle s).1 = s := by
  simp [settle, h]

theorem clearOut_session (s : State) : (clearOut s).session = s.session := rfl
theorem clearOut_password (s : State) : (clearOut s).password = s.password := rfl
theorem serviceOf_clearOut (s : State) : serviceOf (clearOut s) = serviceOf s := rfl
theorem identifierOf_clearOut (s : State) : identifierOf (clearOut s) = identifierOf s := rfl

theorem step1_snd (s : State) (c : Cmd) :
    (step1 s c).2 = (step0 (clearOut s) c).2 ++ (flushIf (live s.session) (step0 (clearOut s) c).1).2 ++
      (settle (flushIf (live s.session) (step0 (clearOut s) c).1).1).2 ++
      (tidy (settle (flushIf (live s.session) (step0 (clearOut s) c).1).1).1).2 := rfl

theorem flushIf_false (t : State) : flushIf false t = (t, []) := rfl

theorem live_signedOut {ss : Session.State} (h : ss.phase = .signedOut) : live ss = false := by
  unfold live; rw [h]

/-! ### Flushing changes only the session (not its phase), the call ids and the acts -/

/-- A call with a live session puts out only requests. -/
theorem call_sends {ss : Session.State} (h : live ss = true) (id : Nat) (c : Call) :
    ∀ o ∈ (Session.step ss (.call id c)).2, ∃ rid k r, o = Out.send rid k r := by
  simp only [Session.step]
  unfold live at h
  split
  · simp [sendCall]
  · simp
  · next hn1 hn2 =>
    exfalso
    split at h
    · exact hn1 _ (by assumption)
    · exact hn2 _ _ _ (by assumption)
    · exact absurd h (by simp)

theorem foldl_sends : ∀ (outs : List Out) (acc : State × List Effect),
    (∀ o ∈ outs, ∃ rid k r, o = Out.send rid k r) → (outs.foldl handleOut acc).1 = acc.1
  | [], _, _ => rfl
  | o :: rest, acc, h => by
    obtain ⟨rid, k, r, rfl⟩ := h o (List.mem_cons_self ..)
    simp only [List.foldl_cons]
    rw [foldl_sends rest _ (fun o' ho => h o' (List.mem_cons_of_mem _ ho))]
    rfl

/-- A call with a live session changes only the session. -/
theorem drive_call_eq {s : State} (h : live s.session = true) (id : Nat) (c : Call) :
    (drive s (.call id c)).1 = { s with session := (Session.step s.session (.call id c)).1 } :=
  foldl_sends _ _ (call_sends h id c)

theorem live_call {ss : Session.State} (h : live ss = true) (id : Nat) (c : Call) :
    live (Session.step ss (.call id c)).1 = true := by
  have hp := (call_quiet h id c).2
  unfold live at h ⊢
  rw [hp]
  exact h

/-- `t` is `s` with another session in the same phase, another next call id and other acts. -/
def Flushed (s t : State) : Prop :=
  ∃ ss n a, t = { s with session := ss, nextCall := n, acts := a } ∧ ss.phase = s.session.phase

theorem Flushed.refl (s : State) : Flushed s s := ⟨s.session, s.nextCall, s.acts, rfl, rfl⟩

theorem Flushed.trans {a b c : State} (h1 : Flushed a b) (h2 : Flushed b c) : Flushed a c := by
  obtain ⟨ss, n, x, rfl, hp⟩ := h1
  obtain ⟨ss', n', x', rfl, hp'⟩ := h2
  exact ⟨ss', n', x', rfl, hp'.trans hp⟩

theorem Flushed.live {s t : State} (h : Flushed s t) : Sky.live t.session = Sky.live s.session := by
  obtain ⟨ss, n, x, rfl, hp⟩ := h
  unfold Sky.live
  show (match ss.phase with | .signedIn _ => true | .refreshing _ _ (some _) => true | _ => false) = _
  rw [hp]; rfl

theorem flushJobs_flushed : ∀ (js : List Job) (s : State), live s.session = true →
    Flushed s (flushJobs s js).1
  | [], s, _ => Flushed.refl s
  | .effect _ :: js, s, h => flushJobs_flushed js s h
  | .call q c :: js, s, h => by
    simp only [flushJobs]
    rw [drive_call_eq (s := { s with nextCall := s.nextCall + 1,
                                     acts := { s.acts with reqs := s.acts.reqs.insert s.nextCall q } })
      h s.nextCall c]
    exact Flushed.trans ⟨_, _, _, rfl, (call_quiet h _ c).2⟩
      (flushJobs_flushed js _ (live_call h _ _))

theorem flush_flushed (s : State) : Flushed s (flush s).1 := by
  unfold flush
  split
  · exact Flushed.refl s
  · split
    · next h =>
      exact Flushed.trans (⟨s.session, s.nextCall, _, rfl, rfl⟩ : Flushed s (clearOut s))
        (flushJobs_flushed _ _ h)
    · exact ⟨s.session, s.nextCall, _, rfl, rfl⟩

theorem flushIf_flushed (b : Bool) (s : State) : Flushed s (flushIf b s).1 := by
  unfold flushIf; split
  · exact flush_flushed s
  · exact Flushed.refl s

/-- Nothing queued: nothing to flush. -/
theorem flushIf_nil {s : State} (h : s.acts.outbox = []) (b : Bool) : flushIf b s = (s, []) := by
  unfold flushIf flush; split <;> simp [h]

theorem Flushed.rows {s t : State} (h : Flushed s t) : t.rows = s.rows := by
  obtain ⟨_, _, _, rfl, _⟩ := h; rfl

theorem Flushed.images {s t : State} (h : Flushed s t) : t.images = s.images := by
  obtain ⟨_, _, _, rfl, _⟩ := h; rfl

theorem Flushed.gen {s t : State} (h : Flushed s t) : t.gen = s.gen := by
  obtain ⟨_, _, _, rfl, _⟩ := h; rfl

theorem step1_live {s : State} {c : Cmd} (h : live (step0 (clearOut s) c).1.session = true)
    (ho : (step0 (clearOut s) c).1.acts.outbox = []) :
    Core (step0 (clearOut s) c).1 (step1 s c).1 := by
  rw [step1_fst, flushIf_nil ho, settle_live h]; exact tidy_core _

theorem step1_feed_live {s : State} {c : Cmd} (h : live (step0 (clearOut s) c).1.session = true) :
    (step1 s c).1.feed = (step0 (clearOut s) c).1.feed := by
  have hf := flushIf_flushed (live s.session) (step0 (clearOut s) c).1
  rw [step1_fst, (tidy_core _).feed, settle_live (hf.live.trans h)]
  obtain ⟨ss, n, x, e, -⟩ := hf
  rw [e]

theorem settle_password (s : State) : (settle s).1.password = s.password := by
  rw [settle_fst]; split <;> rfl

theorem settle_phase (s : State) : (settle s).1.session.phase = s.session.phase := by
  rw [settle_fst]; split <;> rfl

theorem settle_identifier (s : State) : (settle s).1.identifier = s.identifier := by
  rw [settle_fst]; split <;> rfl

theorem settle_service (s : State) : (settle s).1.service = s.service := by
  rw [settle_fst]; split <;> rfl

theorem step1_password (s : State) (c : Cmd) :
    (step1 s c).1.password = (step0 (clearOut s) c).1.password := by
  rw [step1_fst, (tidy_core _).password, settle_password]
  obtain ⟨ss, n, x, e, -⟩ := flushIf_flushed (live s.session) (step0 (clearOut s) c).1
  rw [e]

theorem step1_phase (s : State) (c : Cmd) :
    (step1 s c).1.session.phase = (step0 (clearOut s) c).1.session.phase := by
  rw [step1_fst, (tidy_core _).session, settle_phase]
  obtain ⟨ss, n, x, e, hp⟩ := flushIf_flushed (live s.session) (step0 (clearOut s) c).1
  rw [e]; exact hp

theorem step1_identifier (s : State) (c : Cmd) :
    (step1 s c).1.identifier = (step0 (clearOut s) c).1.identifier := by
  rw [step1_fst, (tidy_core _).identifier, settle_identifier]
  obtain ⟨ss, n, x, e, -⟩ := flushIf_flushed (live s.session) (step0 (clearOut s) c).1
  rw [e]

theorem step1_service (s : State) (c : Cmd) :
    (step1 s c).1.service = (step0 (clearOut s) c).1.service := by
  rw [step1_fst, (tidy_core _).service, settle_service]
  obtain ⟨ss, n, x, e, -⟩ := flushIf_flushed (live s.session) (step0 (clearOut s) c).1
  rw [e]

theorem loadMore_post1 {s : State} (h : canLoadMore s = true) :
    (step1 s .loadMore).1.feed.items = s.feed.items ∧ (step1 s .loadMore).1.feed.loadMore.isSome := by
  have hc : s.feed.cursor.isSome = true := by
    simp only [canLoadMore, Bool.and_eq_true] at h; exact h.2
  obtain ⟨c, hcur⟩ := Option.isSome_iff_exists.mp hc
  have hlive : live s.session = true := by
    simp only [canLoadMore, Bool.and_eq_true] at h; exact h.1.1.1.1
  have h' : canLoadMore (clearOut s) = true := h
  have hcur' : (clearOut s).feed.cursor = some c := hcur
  have e : step0 (clearOut s) .loadMore = drive { (clearOut s) with nextCall := (clearOut s).nextCall + 1, feed := { (clearOut s).feed with loadMore := some ((clearOut s).nextCall, c) }, moreFailed := false } (.call (clearOut s).nextCall (Call.getTimeline (some pageSize) (some c))) := by
    simp only [step0, startLoadMore, h', hcur']
  have hd := drive_call (s := { (clearOut s) with nextCall := (clearOut s).nextCall + 1, feed := { (clearOut s).feed with loadMore := some ((clearOut s).nextCall, c) }, moreFailed := false }) hlive (clearOut s).nextCall (Call.getTimeline (some pageSize) (some c))
  rw [← e] at hd
  rw [step1_feed_live hd.2.1, hd.1]
  exact ⟨rfl, rfl⟩

/-- Load more, enabled: the items stay, and a load-more is in flight. -/
theorem loadMore_post {s : State} (h : canLoadMore s = true) :
    (s.step .loadMore).1.feed.items = s.feed.items ∧ (s.step .loadMore).1.feed.loadMore.isSome :=
  loadMore_post1 (s := s.blank) h

def canRefresh (s : State) : Bool := live s.session && s.feed.refresh.isNone

/-- Refresh, enabled: the items stay, the load-more in flight is withdrawn, a refresh is in
flight. -/
def refreshFrom (s : State) (ss : Session.State) : State :=
  { s with session := ss, nextCall := s.nextCall + 1, feed := { s.feed with loadMore := none, refresh := some s.nextCall } }

theorem refresh_post1 {s : State} (h : canRefresh s = true) :
    (step1 s .refresh).1.feed.items = s.feed.items ∧ (step1 s .refresh).1.feed.loadMore = none ∧
      (step1 s .refresh).1.feed.refresh = some s.nextCall := by
  have hlive : live s.session = true := by
    simp only [canRefresh, Bool.and_eq_true] at h; exact h.1
  simp only [canRefresh] at h
  have fin : ∀ ss, live ss = true →
      (step0 (clearOut s) .refresh).1 = (drive (refreshFrom (clearOut s) ss) (.call s.nextCall (Call.getTimeline (some pageSize)))).1 →
      (step1 s .refresh).1.feed.items = s.feed.items ∧ (step1 s .refresh).1.feed.loadMore = none ∧
        (step1 s .refresh).1.feed.refresh = some s.nextCall := by
    intro ss hl e
    have k := drive_call (s := refreshFrom (clearOut s) ss) hl s.nextCall (Call.getTimeline (some pageSize))
    rw [← e] at k
    rw [step1_feed_live k.2.1, k.1]
    exact ⟨rfl, rfl, rfl⟩
  have h' : (live (clearOut s).session && (clearOut s).feed.refresh.isNone) = true := h
  rcases hlm : s.feed.loadMore with _ | ⟨l, c⟩
  · have hlm' : (clearOut s).feed.loadMore = none := hlm
    exact fin s.session hlive (by simp only [step0, startRefresh, h', hlm']; rfl)
  · have hlm' : (clearOut s).feed.loadMore = some (l, c) := hlm
    exact fin (withdraw s.session l).1 hlive (by simp only [step0, startRefresh, h', hlm']; rfl)

theorem refresh_post {s : State} (h : canRefresh s = true) :
    (s.step .refresh).1.feed.items = s.feed.items ∧ (s.step .refresh).1.feed.loadMore = none ∧
      (s.step .refresh).1.feed.refresh = some s.nextCall :=
  refresh_post1 (s := s.blank) h

theorem startRefresh_dead {s : State} (h : live s.session = false) : startRefresh s = (s, []) := by
  simp [startRefresh, h]

/-- A sign-in the session can take: it sends `createSession`, and nothing else. -/
theorem signIn_step {ss : Session.State} (h : canSignIn ss = true) (host i p : String) :
    Session.step ss (.signIn host i p) =
      ({ ss with phase := .signingIn ss.next host, next := ss.next + 1 },
       [.send ss.next .signIn (createSession host i p)]) := by
  unfold canSignIn at h
  simp only [Session.step]
  split <;> simp_all

/-- Sign in, enabled: the password field is emptied in the step that sends it, and a sign-in is
in flight. -/
theorem signIn_post {s : State} (h : ready s = true) :
    (s.step .signIn).1.password = Text.SecureField.empty passwordHint ∧
      signingIn (s.step .signIn).1.session = true := by
  have hc : canSignIn s.session = true := by simp only [ready, Bool.and_eq_true] at h; exact h.2
  let s0 := clearOut s
  let t : State := { s0 with password := Text.SecureField.empty passwordHint, host := serviceOf s,
                              problem := none, accountOpen := false, slow := false }
  let i : Session.Input := .signIn (serviceOf s) (identifierOf s) s.password.text
  have h' : ready (clearOut s) = true := h
  have e0 : (step0 (clearOut s) .signIn).1 = (drive t i).1 := by
    simp only [step0, signIn, h', ↓reduceIte, driveSession, clearOut_session, clearOut_password, serviceOf_clearOut,
      identifierOf_clearOut, signIn_step hc]
    simp [signedInEvent, t, i, s0]
    rfl
  have hd := drive_same t i
  show (step1 s .signIn).1.password = _ ∧ signingIn (step1 s .signIn).1.session = true
  refine ⟨by rw [step1_password, e0]; exact hd.1, ?_⟩
  have hp := step1_phase s .signIn
  unfold signingIn
  rw [hp, e0, hd.2.2]
  show signingIn (Session.step s.session i).1 = true
  rw [signIn_step hc]
  rfl

theorem signOut_phase (ss : Session.State) : (Session.step ss .signOut).1.phase = .signedOut := by
  simp [Session.step, forgetBoth]

theorem signOut_post1 (s : State) :
    (step1 s .signOut).1.session.phase = .signedOut ∧ (step1 s .signOut).1.feed = {} := by
  have hp : (step0 (clearOut s) .signOut).1.session.phase = .signedOut := by
    show (driveSession { (clearOut s) with problem := none, accountOpen := false } .signOut).1.session.phase = .signedOut
    simp only [driveSession]
    have hd : (drive { (clearOut s) with problem := none, accountOpen := false } .signOut).1.session.phase = .signedOut :=
      (drive_same _ _).2.2.trans (signOut_phase _)
    split
    · rw [startRefresh_dead (by simp [live, hd])]; exact hd
    · exact hd
  obtain ⟨ss, n, x, e, hpf⟩ := flushIf_flushed (live s.session) (step0 (clearOut s) .signOut).1
  have hp2 : (flushIf (live s.session) (step0 (clearOut s) .signOut).1).1.session.phase = .signedOut := by
    rw [e]; exact hpf.trans hp
  have hl : live (flushIf (live s.session) (step0 (clearOut s) .signOut).1).1.session = false := by
    exact live_signedOut hp2
  rw [step1_fst, (tidy_core _).session, (tidy_core _).feed, settle_fst]
  simp only [hl, Bool.false_eq_true, ↓reduceIte]
  exact ⟨hp2, trivial⟩

/-- Account, while signed in: the panel opens or closes, the feed stays. -/
theorem toggleAccount_post {s : State} (h : live s.session = true) :
    (s.step .toggleAccount).1.accountOpen = !s.accountOpen ∧ (s.step .toggleAccount).1.feed = s.feed := by
  have c := step1_live (s := s.blank) (c := .toggleAccount) h rfl
  exact ⟨c.accountOpen, c.feed⟩

/-- Sign out: signed out, the feed empty. -/
theorem signOut_post (s : State) :
    (s.step .signOut).1.session.phase = .signedOut ∧ (s.step .signOut).1.feed = {} :=
  signOut_post1 s.blank

end Sky
