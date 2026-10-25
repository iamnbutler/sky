module

public import CairnAtproto

/-! # What Sky needs of the session machine

Sky makes its timeline calls through `CairnAtproto.Session` and waits for each by its call id.
Two facts about `Session.step`, for every input, let Sky prove it never waits on a call the
session has dropped (claim ^24):

* `step_ridsOk`: the requests in flight have distinct ids, all below `next` (`RidsOk`).
* `step_kept`: a call the session has taken on (in flight or held for a refresh) is still taken
  on after the step, or the step answers it. -/

@[expose] public section

namespace Sky
open CairnAtproto CairnAtproto.Session

/-- The app's call ids the session has taken on: in flight, then held. -/
def pids (s : Session.State) : List Nat := s.inflight.map (·.2.id) ++ s.held.map (·.id)

/-- The step answered call `i`. -/
def Answered (i : Nat) (outs : List Out) : Prop := ∃ a, Out.answer i a ∈ outs

/-- Every call taken on before is still taken on, or answered. -/
def Kept (s s' : Session.State) (outs : List Out) : Prop :=
  ∀ i ∈ pids s, i ∈ pids s' ∨ Answered i outs

structure RidsOk (s : Session.State) : Prop where
  nodup : (s.inflight.map (·.1)).Nodup
  lt : ∀ x ∈ s.inflight, x.1 < s.next

instance (s : Session.State) : Decidable (RidsOk s) :=
  decidable_of_iff ((s.inflight.map (·.1)).Nodup ∧ ∀ x ∈ s.inflight, x.1 < s.next)
    ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

theorem ridsOk_init : RidsOk Session.init := ⟨by simp [Session.init], by simp [Session.init]⟩

theorem ridsOk_of {s s' : Session.State} (h : RidsOk s) (hi : s'.inflight = s.inflight)
    (hn : s.next ≤ s'.next) : RidsOk s' :=
  ⟨hi ▸ h.nodup, fun x hx => Nat.lt_of_lt_of_le (h.lt x (hi ▸ hx)) hn⟩

theorem ridsOk_filter {s s' : Session.State} (h : RidsOk s) (p : Nat × Pending → Bool)
    (hi : s'.inflight = s.inflight.filter p) (hn : s.next ≤ s'.next) : RidsOk s' := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [hi]; exact (List.Sublist.map _ List.filter_sublist).nodup h.nodup
  · rw [hi] at hx; exact Nat.lt_of_lt_of_le (h.lt x (List.mem_filter.1 hx).1) hn

theorem kept_of {s s' : Session.State} {outs : List Out} (h : ∀ i ∈ pids s, i ∈ pids s') :
    Kept s s' outs := fun i hi => Or.inl (h i hi)

theorem answered_answerAll {ps : List Pending} {a : Answer} {i : Nat} (h : i ∈ ps.map (·.id))
    (os os' : List Out) : Answered i (os ++ answerAll ps a ++ os') := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
  exact ⟨a, by simp only [answerAll, List.mem_append, List.mem_map]; exact Or.inl (Or.inr ⟨p, hp, rfl⟩)⟩

/-! ## Each part of a step -/

theorem forgetBoth_fst (s : Session.State) :
    (forgetBoth s).1 = { s with next := s.next + 2 } := rfl

theorem sendCall_ridsOk {s : Session.State} (h : RidsOk s) (svc : String) (p : Pending) :
    RidsOk (sendCall svc s p).1 := by
  refine ⟨?_, ?_⟩
  · simp only [sendCall, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => by
      obtain ⟨x, hx, e⟩ := List.mem_map.1 hm
      have := h.lt x hx; omega, h.nodup⟩
  · intro x hx
    simp only [sendCall, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp [sendCall]
    · have := h.lt x hx; simp only [sendCall]; omega

theorem sendAll_ridsOk {s s0 : Session.State} (h : RidsOk s0) (hi : s.inflight = s0.inflight)
    (hn : s.next = s0.next) (svc : String) (ps : List Pending) :
    RidsOk (sendAll svc s ps).1 := by
  have hm : ∀ x ∈ numbered s.next ps, s.next ≤ x.1 ∧ x.1 < s.next + ps.length := fun x hx =>
    ⟨(mem_numbered hx).1, (mem_numbered hx).2.1⟩
  refine ⟨?_, ?_⟩
  · simp only [sendAll, List.map_append, List.map_map]
    rw [List.nodup_append]
    refine ⟨?_, hi ▸ h.nodup, ?_⟩
    · have : (numbered s.next ps).map ((·.1) ∘ fun x => (x.1, { x.2 with tries := x.2.tries + 1 })) =
          List.range' s.next ps.length := by
        rw [← numbered_fst]; rfl
      rw [this]; exact List.nodup_range'
    · intro a ha b hb e
      subst e
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      rw [hi] at hb
      obtain ⟨y, hy, ey⟩ := List.mem_map.1 hb
      have := h.lt y hy
      have := (hm x hx).1
      simp only [Function.comp] at ey
      omega
  · intro x hx
    simp only [sendAll, List.mem_append, List.mem_map] at hx ⊢
    rcases hx with ⟨y, hy, rfl⟩ | hx
    · have := hm y hy; simp only; omega
    · rw [hi] at hx; have := h.lt x hx; omega

theorem sendAll_ridsOk_eq {s s0 : Session.State} (h : RidsOk s0) (hi : s.inflight = s0.inflight)
    (hn : s.next = s0.next) {svc : String} {ps : List Pending} {x : Session.State × List Out}
    (e : sendAll svc s ps = x) : RidsOk x.1 := e ▸ sendAll_ridsOk h hi hn svc ps

theorem pids_sendAll (svc : String) (s : Session.State) (ps : List Pending) :
    pids (sendAll svc s ps).1 = ps.map (·.id) ++ s.inflight.map (·.2.id) ++ s.held.map (·.id) := by
  have e : ∀ (n : Nat) (ps : List Pending),
      (numbered n ps).map (fun x => ({ x.2 with tries := x.2.tries + 1 } : Pending).id) =
        ps.map (·.id) := by
    intro n ps
    induction ps generalizing n with
    | nil => rfl
    | cons p ps ih => simp only [numbered, List.map_cons, ih]
  simp only [pids, sendAll, List.map_append, List.map_map, List.append_assoc, Function.comp_def, e]

theorem onCallReply_ridsOk {s : Session.State} (h : RidsOk s) (rid : Nat) (r : Cairn.Reply) :
    RidsOk (onCallReply s rid r).1 := by
  unfold onCallReply
  split
  · exact ridsOk_of h rfl (by simp [forgetBoth])
  · split
    · exact h
    · next x p _ =>
      have h1 : RidsOk { s with inflight := s.inflight.filter (·.1 ≠ rid) } :=
        ridsOk_filter h _ rfl (Nat.le_refl _)
      dsimp only
      split
      · split
        · exact ridsOk_of h1 rfl (by simp [startRefresh])
        · exact ridsOk_of h1 rfl (Nat.le_refl _)
        · exact ridsOk_of h1 rfl (Nat.le_refl _)
      · exact h1

theorem onCallReply_kept {s : Session.State} (h : RidsOk s) (rid : Nat) (r : Cairn.Reply) :
    Kept s (onCallReply s rid r).1 (onCallReply s rid r).2 := by
  unfold onCallReply
  split
  · exact kept_of fun i hi => by simpa [forgetBoth, pids] using hi
  · split
    · exact kept_of fun i hi => hi
    · next x p hf =>
      have hmem := List.mem_of_find?_eq_some hf
      have hrid : x = rid := by simpa using List.find?_some hf
      subst hrid
      -- Every call taken on but `p` is still in flight or held after the filter.
      have rest : ∀ i ∈ pids s, i = p.id ∨
          i ∈ pids { s with inflight := s.inflight.filter (·.1 ≠ x) } := by
        intro i hi
        simp only [pids, List.mem_append, List.mem_map] at hi ⊢
        rcases hi with ⟨y, hy, rfl⟩ | hh
        · by_cases e : y.1 = x
          · left
            have := inj_of_nodup_map h.nodup hy hmem e
            subst this; rfl
          · right; left
            exact ⟨y, List.mem_filter.2 ⟨hy, by simpa using e⟩, rfl⟩
        · right; right; exact hh
      dsimp only
      split
      · split
        · intro i hi
          rcases rest i hi with rfl | hh
          · left; simp [startRefresh, pids]
          · left; simp only [startRefresh, pids, List.map_append, List.mem_append] at hh ⊢
            rcases hh with hh | hh
            · exact Or.inl hh
            · exact Or.inr (Or.inl hh)
        · intro i hi
          rcases rest i hi with rfl | hh
          · left; simp [pids]
          · left; simp only [pids, List.map_append, List.mem_append] at hh ⊢
            rcases hh with hh | hh
            · exact Or.inl hh
            · exact Or.inr (Or.inl hh)
        · intro i hi
          rcases rest i hi with rfl | hh
          · right; exact ⟨.reply r, by simp⟩
          · left; exact hh
      · intro i hi
        rcases rest i hi with rfl | hh
        · right; exact ⟨.reply r, by simp⟩
        · left; exact hh

theorem onSignIn_ridsOk {s : Session.State} (h : RidsOk s) (host : String) (r : Cairn.Reply) :
    RidsOk (onSignIn s host r).1 := by
  unfold onSignIn
  split
  · exact ridsOk_of h rfl (Nat.le_refl _)
  · exact ridsOk_of h rfl (by simp [forgetBoth])

theorem onSignIn_kept (s : Session.State) (host : String) (r : Cairn.Reply) :
    Kept s (onSignIn s host r).1 (onSignIn s host r).2 := by
  unfold onSignIn
  split
  · exact kept_of fun i hi => by simpa [pids] using hi
  · exact kept_of fun i hi => by simpa [pids, forgetBoth] using hi

theorem onRefresh_ridsOk {s : Session.State} (h : RidsOk s) (host : String)
    (prev : Option Account) (r : Cairn.Reply) : RidsOk (onRefresh s host prev r).1 := by
  unfold onRefresh
  split
  · dsimp only
    generalize hq : sendAll _ _ s.held = q
    obtain ⟨s1, o⟩ := q
    refine sendAll_ridsOk_eq h ?_ ?_ hq <;> rfl
  · split
    · exact ridsOk_of h rfl (Nat.le_refl _)
    · exact ridsOk_of h rfl (by simp [forgetBoth])

theorem onRefresh_kept (s : Session.State) (host : String) (prev : Option Account)
    (r : Cairn.Reply) : Kept s (onRefresh s host prev r).1 (onRefresh s host prev r).2 := by
  unfold onRefresh
  split
  · intro i hi
    left
    simp only [pids_sendAll, List.map_nil, List.append_nil]
    simp only [pids, List.mem_append] at hi ⊢
    rcases hi with hi | hi
    · exact Or.inr hi
    · exact Or.inl hi
  · split
    · intro i hi
      simp only [pids, List.mem_append] at hi
      rcases hi with hi | hi
      · left; simpa [pids] using hi
      · right
        have := answered_answerAll (a := .reply r) hi [] [.event (.refreshFailed r)]
        simpa using this
    · intro i hi
      simp only [pids, List.mem_append] at hi
      rcases hi with hi | hi
      · left; simpa [pids, forgetBoth] using hi
      · right
        have := answered_answerAll (a := .signedOut) hi []
          ((forgetBoth { s with phase := .signedOut, held := [] }).2 ++ [.event (.signedOut .refused)])
        simpa [List.append_assoc] using this

/-! ## A whole step -/

theorem step_ridsOk {s : Session.State} (h : RidsOk s) (i : Input) : RidsOk (step s i).1 := by
  cases i with
  | signIn host idn pw =>
    simp only [step]
    split
    · split
      · exact ridsOk_of h rfl (by simp)
      · exact h
    · split
      · exact ridsOk_of h rfl (by simp)
      · exact h
    · exact h
  | resume host =>
    simp only [step]
    split
    · exact ridsOk_of h rfl (by simp)
    · exact h
  | call id c =>
    simp only [step]
    split
    · exact sendCall_ridsOk (ridsOk_of (s' := { s with nextTicket := s.nextTicket + 1 }) h rfl
        (Nat.le_refl _)) _ _
    · exact ridsOk_of h rfl (Nat.le_refl _)
    · exact ridsOk_of h rfl (Nat.le_refl _)
  | signOut =>
    simp only [step]
    exact ridsOk_of h rfl (by simp [forgetBoth])
  | reply rid r =>
    simp only [step]
    split
    · split
      · exact onSignIn_ridsOk h _ _
      · exact onCallReply_ridsOk h _ _
    · split
      · exact onRefresh_ridsOk h _ _ _
      · exact onCallReply_ridsOk h _ _
    · exact onCallReply_ridsOk h _ _

theorem step_kept {s : Session.State} (h : RidsOk s) (i : Input) :
    Kept s (step s i).1 (step s i).2 := by
  cases i with
  | signIn host idn pw =>
    simp only [step]
    split
    · split
      · exact kept_of fun i hi => by simpa [pids] using hi
      · exact kept_of fun i hi => hi
    · split
      · exact kept_of fun i hi => by simpa [pids] using hi
      · exact kept_of fun i hi => hi
    · exact kept_of fun i hi => hi
  | resume host =>
    simp only [step]
    split
    · exact kept_of fun i hi => by simpa [pids] using hi
    · exact kept_of fun i hi => hi
  | call id c =>
    simp only [step]
    split
    · exact kept_of fun i hi => by
        simp only [pids, sendCall, List.map_cons, List.mem_append, List.mem_cons] at hi ⊢
        rcases hi with hi | hi
        · exact Or.inl (Or.inr hi)
        · exact Or.inr hi
    · exact kept_of fun i hi => by
        simp only [pids, List.map_append, List.mem_append] at hi ⊢
        rcases hi with hi | hi
        · exact Or.inl hi
        · exact Or.inr (Or.inl hi)
    · exact kept_of fun i hi => by simpa [pids] using hi
  | signOut =>
    simp only [step, forgetBoth]
    intro i hi
    simp only [pids, List.mem_append] at hi
    rcases hi with hi | hi
    · left; simpa [pids] using hi
    · right
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
      exact ⟨.signedOut, by simp only [answerAll, List.mem_append, List.mem_map]; exact Or.inl (Or.inl ⟨p, hp, rfl⟩)⟩
  | reply rid r =>
    simp only [step]
    split
    · split
      · exact onSignIn_kept _ _ _
      · exact onCallReply_kept h _ _
    · split
      · exact onRefresh_kept _ _ _ _
      · exact onCallReply_kept h _ _
    · exact onCallReply_kept h _ _

end Sky
