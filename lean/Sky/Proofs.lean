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

/-- A feed that isn't at its end holds a cursor (^22). -/
def CursorKept (f : Feed) : Prop := f.atEnd = false → f.items ≠ [] → f.cursor.isSome = true

instance (f : Feed) : Decidable (CursorKept f) := by unfold CursorKept; infer_instance

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

theorem cursorKept_empty : CursorKept ({} : Feed) := fun _ h => absurd rfl h

theorem cursorKept_append (f : Feed) (p : FeedPage) : CursorKept (f.appendPage p) := by
  intro h _
  simp only [Feed.appendPage] at h ⊢
  cases hc : p.cursor <;> simp_all

theorem cursorKept_replace (f : Feed) (p : FeedPage) : CursorKept (f.replaceBy p) := by
  intro h _
  simp only [Feed.replaceBy] at h ⊢
  cases hc : p.cursor <;> simp_all

theorem cursorKept_headPage {f : Feed} (h : CursorKept f) (p : FeedPage) :
    CursorKept (f.headPage p) := by
  unfold Feed.headPage
  split
  · next new hn =>
    intro ha _
    have hne : f.items ≠ [] := by
      intro e; simp [e, newOnTop] at hn
    exact h ha hne
  · exact cursorKept_replace f p

theorem cursorKept_gotLoadMore {f : Feed} (h : CursorKept f) (id : Nat) (p : Option FeedPage) :
    CursorKept (f.gotLoadMore id p) := by
  unfold Feed.gotLoadMore
  split
  · split
    · split
      · split
        · exact cursorKept_append _ _
        · exact h
      · exact h
    · exact h
  · exact h

theorem cursorKept_gotRefresh {f : Feed} (h : CursorKept f) (id : Nat) (p : Option FeedPage) :
    CursorKept (f.gotRefresh id p) := by
  unfold Feed.gotRefresh
  split
  · split
    · exact cursorKept_headPage (f := { f with refresh := none }) h _
    · exact h
  · exact h

@[simp] theorem gotLoadMore_refresh (f : Feed) (id : Nat) (p : Option FeedPage) :
    (f.gotLoadMore id p).refresh = f.refresh := by
  unfold Feed.gotLoadMore
  repeat' split
  all_goals rfl

theorem gotLoadMore_lm {f : Feed} {l : Nat} {c : String} (hl : f.loadMore = some (l, c))
    (p : Option FeedPage) : (f.gotLoadMore l p).loadMore = none := by
  unfold Feed.gotLoadMore
  rw [hl]
  dsimp only
  rw [ite_eq_left_of_eq_true _ _ (eq_self l)]
  split
  · split <;> rfl
  · rfl

theorem gotLoadMore_other {f : Feed} {id : Nat} (h : ∀ c, f.loadMore ≠ some (id, c))
    (p : Option FeedPage) : f.gotLoadMore id p = f := by
  unfold Feed.gotLoadMore
  split
  · next l c e =>
    split
    · next hl => subst hl; exact absurd e (h c)
    · rfl
  · rfl

theorem gotRefresh_refresh {f : Feed} {id : Nat} (h : f.refresh = some id) (p : Option FeedPage) :
    (f.gotRefresh id p).refresh = none := by
  unfold Feed.gotRefresh
  simp only [h, ↓reduceIte]
  split
  · unfold Feed.headPage; split <;> rfl
  · rfl

theorem gotRefresh_other {f : Feed} {id : Nat} (h : f.refresh ≠ some id) (p : Option FeedPage) :
    f.gotRefresh id p = f := by
  simp [Feed.gotRefresh, h]

/-- After a refresh's answer, a load-more still in flight is the one before, the cursor is the
same and the items no fewer. -/
theorem gotRefresh_lm {f : Feed} {id : Nat} {p : Option FeedPage} {x : Nat × String}
    (h : (f.gotRefresh id p).loadMore = some x) :
    f.loadMore = some x ∧ (f.gotRefresh id p).cursor = f.cursor ∧
      (f.items ≠ [] → (f.gotRefresh id p).items ≠ []) := by
  unfold Feed.gotRefresh at *
  by_cases hr : f.refresh = some id
  · simp only [hr, ite_true] at h ⊢
    cases p with
    | none => exact ⟨h, by simp, fun x => x⟩
    | some q =>
      simp only at h ⊢
      unfold Feed.headPage at *
      cases hn : newOnTop f.items q.feed with
      | none => simp [hn, Feed.replaceBy] at h
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

theorem pids_withdraw (ss : Session.State) (l : Nat) {x : Nat} (hx : x ∈ pids ss) (hl : x ≠ l) :
    x ∈ pids (withdraw ss l).1 := by
  simp only [pids, withdraw, List.mem_append, List.mem_map, List.mem_filter, bne_iff_ne,
    ne_eq] at hx ⊢
  rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
  · exact Or.inl ⟨y, ⟨hy, hl⟩, rfl⟩
  · exact Or.inr ⟨y, ⟨hy, hl⟩, rfl⟩

theorem ridsOk_withdraw {ss : Session.State} (h : RidsOk ss) (l : Nat) :
    RidsOk (withdraw ss l).1 := ridsOk_filter h _ rfl (Nat.le_refl _)

theorem onAnswer_Q {s : State} {id : Nat} {a : Answer} {rest : List Out}
    (h : Q (.answer id a :: rest) s) : Q rest (onAnswer s id a).1 := by
  have hl := h.lm
  have hr := h.rf
  have hd := h.dis
  unfold onAnswer
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

theorem handleOut_Q {s : State} {es : List Effect} {o : Out} {rest : List Out}
    (h : Q (o :: rest) s) : Q rest (handleOut (s, es) o).1 := by
  cases o with
  | send rid k ht => exact h.tail fun _ _ e => by cases e
  | forget rid item => exact h.tail fun _ _ e => by cases e
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

theorem pending_of {s : State} {i : Session.Input} (hr : RidsOk s.session) (x : Nat)
    (h : x ∈ pids s.session ∨ (∃ c, i = .call x c) ∧ live s.session = true) :
    x ∈ pids (Session.step s.session i).1 ∨ Answered x (Session.step s.session i).2 := by
  rcases h with hm | ⟨⟨c, rfl⟩, hlive⟩
  · exact step_kept hr _ x hm
  · exact Or.inl (call_taken hlive x c)

/-- Driving the session from a state that keeps `Inv` (any input but a new call). -/
theorem drive_inv_of {s : State} (h : Inv s) (i : Session.Input) : Inv (drive s i).1 :=
  drive_inv h.rids (pending_of h.rids) (lmOk_mono (fun _ hx => Or.inl hx) h.lm)
    (rfOk_mono (fun _ hx => Or.inl hx) h.rf) h.dis h.cur

theorem live_withdraw (ss : Session.State) (l : Nat) : live (withdraw ss l).1 = live ss := rfl

theorem startRefresh_core {s : State} (h : Inv s) (hlive : live s.session = true)
    (ss : Session.State) (hr : RidsOk ss) (hl : live ss = live s.session) :
    Inv (drive { s with session := ss, nextCall := s.nextCall + 1,
                        feed := { s.feed with loadMore := none, refresh := some s.nextCall } }
      (.call s.nextCall (Call.getTimeline (some pageSize)))).1 :=
  drive_inv hr (pending_of hr) (by simp [LmOk])
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
    show Inv (drive { s with nextCall := s.nextCall + 1, feed := { s.feed with loadMore := some (s.nextCall, c) } } (.call s.nextCall (Call.getTimeline (some pageSize) (some c)))).1
    apply drive_inv
    · exact h.rids
    · exact pending_of h.rids
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

theorem driveSession_inv {s : State} (h : Inv s) (i : Session.Input) :
    Inv (driveSession s i).1 := by
  unfold driveSession
  try dsimp only
  split
  · exact startRefresh_inv (drive_inv_of h i)
  · exact drive_inv_of h i

theorem inv_login {s : State} (h : Inv s) (l : Login) (p : Option String) :
    Inv { s with login := l, problem := p } := ⟨h.rids, h.lm, h.rf, h.dis, h.cur⟩

theorem step0_inv {s : State} (h : Inv s) (c : Cmd) : Inv (step0 s c).1 := by
  cases c with
  | signIn =>
    simp only [step0, signIn]
    split
    · exact driveSession_inv (inv_login h _ _) _
    · exact h
  | loadMore => exact startLoadMore_inv h
  | refresh => exact startRefresh_inv h
  | signOut => exact driveSession_inv (inv_login h _ _) _
  | msg m =>
    simp only [step0]
    cases m with
    | reply id r =>
      simp only [receive0]
      split
      · simp only [onBoot]
        have hb : Inv { s with booting := false } := ⟨h.rids, h.lm, h.rf, h.dis, h.cur⟩
        split
        · split
          · try dsimp only
            split
            · exact hb
            · apply driveSession_inv; exact ⟨h.rids, h.lm, h.rf, h.dis, h.cur⟩
          · exact hb
        · exact hb
      · split
        · exact driveSession_inv h _
        · exact h
    | _ => exact h

theorem settle_inv {s : State} (h : Inv s) : Inv (settle s).1 := by
  unfold settle
  split
  · exact h
  · exact ⟨⟨by simp, by simp⟩, by simp [LmOk], by simp [RfOk], by simp [Distinct], cursorKept_empty⟩

theorem settle_signedOut (s : State) : SignedOutEmpty (settle s).1 := by
  unfold settle
  split
  · next hl => intro h; simp_all
  · intro _; exact ⟨rfl, rfl, rfl⟩

theorem step_inv {s : State} (h : Inv s) (c : Cmd) : Inv (s.step c).1 := by
  simp only [State.step]
  exact settle_inv (step0_inv h c)

theorem step_signedOut (s : State) (c : Cmd) : SignedOutEmpty (s.step c).1 := by
  simp only [State.step]
  exact settle_signedOut _

theorem inv_initial : Inv initial :=
  ⟨ridsOk_init, by simp [LmOk, initial], by simp [RfOk, initial], by simp [Distinct, initial],
   cursorKept_empty⟩


/-! ## What a move does (the moves' posts) -/

/-- What every output leaves alone: the sign-in form, the call ids, the session's phase. -/
structure Same (s s' : State) : Prop where
  login : s'.login = s.login
  nextCall : s'.nextCall = s.nextCall
  phase : s'.session.phase = s.session.phase

theorem Same.refl (s : State) : Same s s := ⟨rfl, rfl, rfl⟩

theorem Same.trans {a b c : State} (h1 : Same a b) (h2 : Same b c) : Same a c :=
  ⟨h2.login.trans h1.login, h2.nextCall.trans h1.nextCall, h2.phase.trans h1.phase⟩

theorem onAnswer_same (s : State) (id : Nat) (a : Answer) : Same s (onAnswer s id a).1 := by
  unfold onAnswer
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

theorem handleOut_same (acc : State × List Effect) (o : Out) : Same acc.1 (handleOut acc o).1 := by
  cases o with
  | send => exact Same.refl _
  | forget => exact Same.refl _
  | answer id a => exact onAnswer_same _ _ _
  | event e => cases e <;> first | exact ⟨rfl, rfl, rfl⟩ | (rename_i x; cases x <;> exact ⟨rfl, rfl, rfl⟩)

theorem handleOut_quiet (acc : State × List Effect) (o : Out) (h : ∀ x a, o ≠ .answer x a) :
    (handleOut acc o).1.feed = acc.1.feed ∧ (handleOut acc o).1.session = acc.1.session := by
  cases o with
  | send => exact ⟨rfl, rfl⟩
  | forget => exact ⟨rfl, rfl⟩
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
    (drive s i).1.login = s.login ∧ (drive s i).1.nextCall = s.nextCall ∧
      (drive s i).1.session.phase = (Session.step s.session i).1.phase := by
  have := foldl_same (Session.step s.session i).2 ({ s with session := (Session.step s.session i).1 }, [])
  exact ⟨this.login, this.nextCall, this.phase⟩

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

theorem step_live {s : State} {c : Cmd} (h : live (step0 s c).1.session = true) :
    (s.step c).1 = (step0 s c).1 := by
  simp only [State.step]
  exact settle_live h

theorem settle_login (s : State) : (settle s).1.login = s.login := by
  unfold settle; split <;> rfl

/-- Load more, enabled: the items stay, and a load-more is in flight. -/
theorem loadMore_post {s : State} (h : canLoadMore s = true) :
    (s.step .loadMore).1.feed.items = s.feed.items ∧ (s.step .loadMore).1.feed.loadMore.isSome := by
  have hc : s.feed.cursor.isSome = true := by
    simp only [canLoadMore, Bool.and_eq_true] at h; exact h.2
  obtain ⟨c, hcur⟩ := Option.isSome_iff_exists.mp hc
  have hlive : live s.session = true := by
    simp only [canLoadMore, Bool.and_eq_true] at h; exact h.1.1.1.1
  have e : step0 s .loadMore = drive { s with nextCall := s.nextCall + 1, feed := { s.feed with loadMore := some (s.nextCall, c) } } (.call s.nextCall (Call.getTimeline (some pageSize) (some c))) := by
    simp only [step0, startLoadMore, h, hcur]
  have hd := drive_call (s := { s with nextCall := s.nextCall + 1, feed := { s.feed with loadMore := some (s.nextCall, c) } }) hlive s.nextCall (Call.getTimeline (some pageSize) (some c))
  rw [← e] at hd
  rw [step_live hd.2.1, hd.1]
  exact ⟨rfl, rfl⟩

def canRefresh (s : State) : Bool := live s.session && s.feed.refresh.isNone

/-- Refresh, enabled: the items stay, the load-more in flight is withdrawn, a refresh is in
flight. -/
def refreshFrom (s : State) (ss : Session.State) : State :=
  { s with session := ss, nextCall := s.nextCall + 1, feed := { s.feed with loadMore := none, refresh := some s.nextCall } }

theorem refresh_post {s : State} (h : canRefresh s = true) :
    (s.step .refresh).1.feed.items = s.feed.items ∧ (s.step .refresh).1.feed.loadMore = none ∧
      (s.step .refresh).1.feed.refresh = some s.nextCall := by
  have hlive : live s.session = true := by
    simp only [canRefresh, Bool.and_eq_true] at h; exact h.1
  simp only [canRefresh] at h
  have fin : ∀ ss, live ss = true →
      (step0 s .refresh).1 = (drive (refreshFrom s ss) (.call s.nextCall (Call.getTimeline (some pageSize)))).1 →
      (s.step .refresh).1.feed.items = s.feed.items ∧ (s.step .refresh).1.feed.loadMore = none ∧
        (s.step .refresh).1.feed.refresh = some s.nextCall := by
    intro ss hl e
    have k := drive_call (s := refreshFrom s ss) hl s.nextCall (Call.getTimeline (some pageSize))
    rw [← e] at k
    rw [step_live k.2.1, k.1]
    exact ⟨rfl, rfl, rfl⟩
  rcases hlm : s.feed.loadMore with _ | ⟨l, c⟩
  · exact fin s.session hlive (by simp only [step0, startRefresh, h, hlm]; rfl)
  · exact fin (withdraw s.session l).1 hlive (by simp only [step0, startRefresh, h, hlm]; rfl)

theorem startRefresh_login (s : State) : (startRefresh s).1.login = s.login := by
  unfold startRefresh
  split
  · rcases hlm : s.feed.loadMore with _ | ⟨l, c⟩
    · exact (drive_same (refreshFrom s s.session) _).1
    · exact (drive_same (refreshFrom s (withdraw s.session l).1) _).1
  · rfl

theorem startRefresh_dead {s : State} (h : live s.session = false) : startRefresh s = (s, []) := by
  simp [startRefresh, h]

theorem driveSession_login (s : State) (i : Session.Input) :
    (driveSession s i).1.login = s.login := by
  unfold driveSession
  try dsimp only
  split
  · exact (startRefresh_login _).trans (drive_same s i).1
  · exact (drive_same s i).1

/-- Sign in, enabled: the password is gone from the state once sent. -/
theorem signIn_post {s : State} (h : canSignIn s.session = true) :
    (s.step .signIn).1.login.password = "" := by
  simp only [State.step]
  rw [settle_login]
  simp only [step0, signIn, h, ↓reduceIte]
  rw [driveSession_login]

theorem signOut_phase (ss : Session.State) : (Session.step ss .signOut).1.phase = .signedOut := by
  simp [Session.step, forgetBoth]

/-- Sign out: signed out, the feed empty. -/
theorem signOut_post (s : State) :
    (s.step .signOut).1.session.phase = .signedOut ∧ (s.step .signOut).1.feed = {} := by
  have hp : (step0 s .signOut).1.session.phase = .signedOut := by
    simp only [step0, signOut, driveSession]
    have hd : (drive { s with problem := none } .signOut).1.session.phase = .signedOut :=
      (drive_same _ _).2.2.trans (signOut_phase _)
    split
    · rw [startRefresh_dead (by simp [live, hd])]; exact hd
    · exact hd
  have hl : live (step0 s .signOut).1.session = false := by simp [live, hp]
  simp only [State.step, settle, hl]
  exact ⟨hp, rfl⟩

end Sky
