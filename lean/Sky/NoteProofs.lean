module

public import Sky.Rows

/-! # The notifications: what Sky's steps keep

* `drive_call_eq`: a call made signed in only sends; Sky's state changes in nothing but the
  session (so the notes record exactly what `noteCall` says).
* `Calm`: the notes' handlers leave the session's phase, the feed and the tab alone, and the
  mark (the newest notification that has appeared) too. The moves' posts follow (^61–^66).
* `seenOnScreen`: no step but a row of the list coming into view raises the mark, and that one
  raises it at most to the newest notification of a row on screen (^70).
* `NotesSignedOut`: signed out, the notes hold no list and no call, and Home shows (^71). -/

@[expose] public section

namespace Sky
open Cairn CairnAtproto CairnAtproto.Session

/-! ## A call, signed in -/

theorem call_phase {ss : Session.State} (h : live ss = true) (id : Nat) (c : Call) :
    (Session.step ss (.call id c)).1.phase = ss.phase := (call_quiet h id c).2

theorem live_after_call {ss : Session.State} (h : live ss = true) (id : Nat) (c : Call) :
    live (Session.step ss (.call id c)).1 = true := by
  unfold live; rw [call_phase h]; exact h

theorem noteCall_eq {s : State} (h : live s.session = true) (f : Nat → Notes → Notes) (c : Call) :
    (Sky.noteCall s f c).1 = { s with nextCall := s.nextCall + 1, notes := f s.nextCall s.notes,
                                      session := (Session.step s.session (.call s.nextCall c)).1 } :=
  drive_call_eq (s := { s with nextCall := s.nextCall + 1, notes := f s.nextCall s.notes }) h _ _

/-! ## The notes' handlers are calm -/

/-- What the notes' handlers leave alone. -/
structure Calm (s t : State) : Prop where
  phase : t.session.phase = s.session.phase
  feed : t.feed = s.feed
  tab : t.tab = s.tab
  mark : t.notes.seen.1.mark = s.notes.seen.1.mark

theorem Calm.refl (s : State) : Calm s s := ⟨rfl, rfl, rfl, rfl⟩

theorem Calm.trans {a b c : State} (h1 : Calm a b) (h2 : Calm b c) : Calm a c :=
  ⟨h2.phase.trans h1.phase, h2.feed.trans h1.feed, h2.tab.trans h1.tab, h2.mark.trans h1.mark⟩

theorem Calm.liveEq {s t : State} (h : Calm s t) : live t.session = live s.session := by
  unfold Sky.live; rw [h.phase]

/-- Seen is the notes' seen marker, untouched. -/
def KeepsSeen (f : Nat → Notes → Notes) : Prop := ∀ i n, (f i n).seen = n.seen

theorem noteCall_calm {s : State} (h : live s.session = true) {f : Nat → Notes → Notes}
    (hf : KeepsSeen f) (c : Call) : Calm s (Sky.noteCall s f c).1 := by
  rw [noteCall_eq h]
  exact ⟨call_phase h _ _, rfl, rfl, congrArg (fun x : SeenKept => x.1.mark) (hf _ _)⟩

theorem seenAct_seen (acc : State × List Effect) (a : Cairn.Optimistic.Act Nat) :
    (seenAct acc a).1.notes.seen = acc.1.notes.seen ∧ Calm acc.1 (seenAct acc a).1 := by
  cases a <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem foldl_seenAct_seen : ∀ (as : List (Cairn.Optimistic.Act Nat)) (acc : State × List Effect),
    (as.foldl seenAct acc).1.notes.seen = acc.1.notes.seen ∧ Calm acc.1 (as.foldl seenAct acc).1
  | [], _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
  | a :: as, acc => by
    have h1 := seenAct_seen acc a
    have h2 := foldl_seenAct_seen as (seenAct acc a)
    exact ⟨h2.1.trans h1.1, h1.2.trans h2.2⟩

theorem hearSeen_mark (s : State) (e : SeenEv) :
    (hearSeen s e).1.notes.seen.1.mark = s.notes.seen.1.mark := by
  unfold hearSeen; rw [(foldl_seenAct_seen _ _).1]; rfl

theorem hearSeen_calm (s : State) (e : SeenEv) : Calm s (hearSeen s e).1 := by
  have := (foldl_seenAct_seen (s.notes.seen.hear e).2
    ({ s with notes := { s.notes with seen := (s.notes.seen.hear e).1 } }, [])).2
  exact ⟨this.phase, this.feed, this.tab, hearSeen_mark s e⟩

theorem sendSeen_calm (acc : State × List Effect) (h : live acc.1.session = true)
    (a : Cairn.Optimistic.Act Nat) : Calm acc.1 (sendSeen acc a).1 := by
  cases a with
  | write k v => dsimp only [sendSeen]; exact noteCall_calm h (by intro _ _; rfl) _
  | read k => dsimp only [sendSeen]; exact noteCall_calm h (by intro _ _; rfl) _
  | _ => exact ⟨rfl, rfl, rfl, rfl⟩

theorem foldl_sendSeen_calm : ∀ (as : List (Cairn.Optimistic.Act Nat)) (acc : State × List Effect),
    live acc.1.session = true → Calm acc.1 (as.foldl sendSeen acc).1
  | [], _, _ => Calm.refl _
  | a :: as, acc, h => by
    have h1 := sendSeen_calm acc h a
    exact h1.trans (foldl_sendSeen_calm as _ (h1.liveEq.trans h))

theorem startPoll_calm (s : State) : Calm s (startPoll s).1 := by
  unfold startPoll; split
  · next hc => exact noteCall_calm (by simp only [Bool.and_eq_true] at hc; exact hc.1) (by intro _ _; rfl) _
  · exact ⟨rfl, rfl, rfl, rfl⟩

theorem foldl_sendPosts_calm : ∀ (us : List (List String)) (acc : State × List Effect),
    live acc.1.session = true → Calm acc.1 (us.foldl sendPosts acc).1
  | [], _, _ => Calm.refl _
  | u :: us, acc, h => by
    have h1 : Calm acc.1 (sendPosts acc u).1 := by
      unfold sendPosts; exact noteCall_calm h (by intro _ _; rfl) _
    exact h1.trans (foldl_sendPosts_calm us _ (h1.liveEq.trans h))

theorem flushNotes_calm (s : State) : Calm s (flushNotes s).1 := by
  unfold flushNotes; split
  · next hl =>
    have hp : Calm s { s with notes := { s.notes with postsDue := [] } } := ⟨rfl, rfl, rfl, rfl⟩
    have h00 := hp.trans (foldl_sendPosts_calm (chunksOf maxGetPosts s.notes.postsDue)
      ({ s with notes := { s.notes with postsDue := [] } }, []) hl)
    generalize (chunksOf maxGetPosts s.notes.postsDue).foldl sendPosts
      ({ s with notes := { s.notes with postsDue := [] } }, []) = r at h00 ⊢
    obtain ⟨s₀, e₀⟩ := r
    dsimp only at h00 ⊢
    have h0 : Calm s₀ { s₀ with notes := { s₀.notes with todo := [] } } := ⟨rfl, rfl, rfl, rfl⟩
    have h1 := h00.trans (h0.trans
      (foldl_sendSeen_calm s₀.notes.todo ({ s₀ with notes := { s₀.notes with todo := [] } }, [])
        (h00.liveEq.trans hl)))
    generalize s₀.notes.todo.foldl sendSeen ({ s₀ with notes := { s₀.notes with todo := [] } }, []) = q at h1 ⊢
    obtain ⟨s1, e1⟩ := q
    dsimp only at h1 ⊢; split
    · exact h1.trans (startPoll_calm _)
    · exact h1
  · exact ⟨rfl, rfl, rfl, rfl⟩

theorem markSeen_mark (s : SeenKept) : s.markSeen.1.1.mark = s.1.mark := by
  show s.1.markSeen.1.mark = s.1.mark
  unfold Seen.markSeen; split <;> rfl

theorem markSeenNow_calm (s : State) : Calm s (markSeenNow s).1 := by
  unfold markSeenNow; split
  · have h := foldl_seenAct_seen s.notes.seen.markSeen.2
      ({ s with notes := { s.notes with seen := s.notes.seen.markSeen.1 } }, [])
    have h1 : Calm s (s.notes.seen.markSeen.2.foldl seenAct
        ({ s with notes := { s.notes with seen := s.notes.seen.markSeen.1 } }, [])).1 :=
      ⟨h.2.phase, h.2.feed, h.2.tab, by rw [h.1]; exact markSeen_mark _⟩
    exact h1.trans (flushNotes_calm _)
  · exact ⟨rfl, rfl, rfl, rfl⟩

theorem startNoteRefresh_calm (s : State) : Calm s (startNoteRefresh s).1 := by
  unfold startNoteRefresh; split
  · next hl => split
               · exact noteCall_calm hl (by intro _ _; rfl) _
               · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

theorem startNoteMore_calm (s : State) : Calm s (startNoteMore s).1 := by
  unfold startNoteMore; split
  · next hl => split
               · exact noteCall_calm hl (by intro _ _; rfl) _
               · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## The moves' posts -/

/-- What a step keeps of `step0`'s state while the session stays live. -/
structure StepKept (t u : State) : Prop where
  notes : u.notes = t.notes
  tab : u.tab = t.tab
  feed : u.feed = t.feed

/-- A command whose `step0` keeps the session live: `step` is `step0` (on the state with the
acts' outbox empty), the acts' calls sent, then `tidy`; the notes, tab and feed are `step0`'s. -/
theorem step_core {s : State} {c : Cmd} (_hb : c ≠ .signIn) (_hp : ∀ op, c ≠ .editPassword op)
    (h : live (step0 (clearOut s.blank) c).1.session = true) :
    StepKept (step0 (clearOut s.blank) c).1 (step1 s.blank c).1 := by
  have hf := flushIf_flushed (live s.blank.session) (step0 (clearOut s.blank) c).1
  rw [step1_fst, settle_live (hf.live.trans h)]
  obtain ⟨ss, n, x, e, -⟩ := hf
  exact ⟨by rw [(tidy_core _).notes, e], by rw [(tidy_core _).tab, e], by rw [(tidy_core _).feed, e]⟩

theorem step_eq {s : State} {c : Cmd} (hb : c ≠ .signIn) (hp : ∀ op, c ≠ .editPassword op) :
    (s.step c).1 = { (step1 s.blank c).1 with password := s.password } := by
  rw [step_blind s c hb hp]

/-- The Notifications tab, signed in: the notifications show (pressed again, at their top);
the feed stays. -/
theorem openNotes_post {s : State} (h : live s.session = true) :
    (s.step .openNotes).1.tab = .notifications ∧ (s.step .openNotes).1.feed = s.feed := by
  have hc : Calm { clearOut s.blank with tab := .notifications } (step0 (clearOut s.blank) .openNotes).1 := by
    show Calm _ (if (clearOut s.blank).tab == .notifications then notesTop _ else openNotes _).1
    split
    · next ht =>
      have ht : s.tab = .notifications := by simpa [clearOut, State.blank] using ht
      exact ⟨rfl, rfl, by simp [notesTop, clearOut, State.blank, ht], rfl⟩
    · unfold openNotes
      exact (startNoteRefresh_calm _).trans (markSeenNow_calm _)
  have k := step_core (s := s) (c := .openNotes) (by intro h; cases h) (by intro _ h; cases h) (hc.liveEq.trans h)
  rw [step_eq (by intro h; cases h) (by intro _ h; cases h)]
  exact ⟨k.tab.trans hc.tab, k.feed.trans hc.feed⟩

/-- Home, signed in: the feed shows (pressed again, at its top). -/
theorem openHome_post {s : State} (h : live s.session = true) :
    (s.step .openHome).1.tab = .home ∧ (s.step .openHome).1.feed = s.feed := by
  have hc : Calm { clearOut s.blank with tab := .home } (step0 (clearOut s.blank) .openHome).1 := by
    show Calm _ (if (clearOut s.blank).tab == .home then feedTop _ else ({ clearOut s.blank with tab := .home }, [])).1
    split
    · next ht =>
      have ht : s.tab = .home := by simpa [clearOut, State.blank] using ht
      exact ⟨rfl, rfl, by simp [feedTop, clearOut, State.blank, ht], rfl⟩
    · exact Calm.refl _
  have k := step_core (s := s) (c := .openHome) (by intro h; cases h) (by intro _ h; cases h) (hc.liveEq.trans h)
  rw [step_eq (by intro h; cases h) (by intro _ h; cases h)]
  exact ⟨k.tab.trans hc.tab, k.feed.trans hc.feed⟩

def canNoteRefresh (s : State) : Bool := live s.session && s.notes.list.refresh.isNone

/-- Refresh the notifications: a refresh in flight, the notifications held stay until it is
answered. -/
theorem noteRefresh_post {s : State} (h : canNoteRefresh s = true) :
    (s.step .noteRefresh).1.notes.list.items = s.notes.list.items ∧
      (s.step .noteRefresh).1.notes.list.refresh = some s.nextCall := by
  simp only [canNoteRefresh, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  obtain ⟨hl, hr⟩ := h
  have e : step0 (clearOut s.blank) .noteRefresh = Sky.noteCall (clearOut s.blank)
      (fun _ n => { n with list := { s.notes.list with loadMore := none, refresh := some s.nextCall } })
      (Call.listNotifications (some notePageSize) none) := by
    show startNoteRefresh (clearOut s.blank) = _
    simp only [startNoteRefresh, clearOut, State.blank, hl, ↓reduceIte, Paged.beginRefresh, hr,
      Option.isNone_none]
  have hn := noteCall_eq (s := clearOut s.blank) hl
    (fun _ n => { n with list := { s.notes.list with loadMore := none, refresh := some s.nextCall } })
    (Call.listNotifications (some notePageSize) none)
  rw [← e] at hn
  have hl2 : live (step0 (clearOut s.blank) .noteRefresh).1.session = true := by
    rw [hn]; exact live_after_call hl _ _
  have k := step_core (s := s) (c := .noteRefresh) (by intro h; cases h) (by intro _ h; cases h) hl2
  rw [step_eq (by intro h; cases h) (by intro _ h; cases h), k.notes, hn]
  exact ⟨rfl, rfl⟩

/-- Load more notifications, when it can: in flight, the notifications held stay. -/
theorem noteMore_post {s : State} (h : canNoteMore s = true) :
    (s.step .noteMore).1.notes.list.items = s.notes.list.items ∧
      (s.step .noteMore).1.notes.list.loadMore.isSome := by
  simp only [canNoteMore, Bool.and_eq_true] at h
  obtain ⟨hl, hm⟩ := h
  have hb : ∃ g c, s.notes.list.beginLoadMore s.nextCall = some (g, c) := by
    unfold Paged.beginLoadMore
    have hc : s.notes.list.cursor.isSome = true := by
      simp only [Paged.canLoadMore, Bool.and_eq_true] at hm; exact hm.2
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hc
    rw [hm, hc]; exact ⟨_, _, rfl⟩
  obtain ⟨g, c, hgc⟩ := hb
  have hg := Paged.beginLoadMore_cursor hgc
  have e : step0 (clearOut s.blank) .noteMore = Sky.noteCall (clearOut s.blank)
      (fun _ n => { n with list := g, moreFailed := false })
      (Call.listNotifications (some notePageSize) (some c)) := by
    show startNoteMore (clearOut s.blank) = _
    simp only [startNoteMore, clearOut, State.blank, hl, ↓reduceIte, hgc]
  have hn := noteCall_eq (s := clearOut s.blank) hl (fun _ n => { n with list := g, moreFailed := false })
    (Call.listNotifications (some notePageSize) (some c))
  rw [← e] at hn
  have hl2 : live (step0 (clearOut s.blank) .noteMore).1.session = true := by
    rw [hn]; exact live_after_call hl _ _
  have k := step_core (s := s) (c := .noteMore) (by intro h; cases h) (by intro _ h; cases h) hl2
  rw [step_eq (by intro h; cases h) (by intro _ h; cases h), k.notes, hn]
  exact ⟨hg.2.2, by simp [hg.1]⟩

/-- A row of the notifications came into view: the mark never goes down; the feed stays. -/
theorem noteAppear_post {s : State} (h : live s.session = true) (k : Nat) :
    s.notes.seen.1.mark ≤ (s.step (.noteAppear k)).1.notes.seen.1.mark ∧
      (s.step (.noteAppear k)).1.feed = s.feed := by
  have hc : s.notes.seen.1.mark ≤ (step0 (clearOut s.blank) (.noteAppear k)).1.notes.seen.1.mark ∧
      ((step0 (clearOut s.blank) (.noteAppear k)).1.session.phase = s.session.phase ∧
        (step0 (clearOut s.blank) (.noteAppear k)).1.feed = s.feed) := by
    show s.notes.seen.1.mark ≤ (noteAppear (clearOut s.blank) k).1.notes.seen.1.mark ∧
      ((noteAppear (clearOut s.blank) k).1.session.phase = s.session.phase ∧ (noteAppear (clearOut s.blank) k).1.feed = s.feed)
    unfold noteAppear; split
    · exact ⟨Nat.le_refl _, rfl, rfl⟩
    split
    · next g _ =>
      have c := markSeenNow_calm
        { clearOut s.blank with notes := { s.notes with
            seen := s.notes.seen.appear (newestMs g.members),
            fresh := min s.notes.fresh ((clearOut s.blank).noteGroups.findIdx (·.key == k)) } }
      refine ⟨?_, c.phase, c.feed⟩
      exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_eq c.mark.symm)
    · exact ⟨Nat.le_refl _, rfl, rfl⟩
  have k' := step_core (s := s) (c := .noteAppear k) (by intro h; cases h) (by intro _ h; cases h)
    (by unfold live; rw [hc.2.1]; exact h)
  rw [step_eq (by intro h; cases h) (by intro _ h; cases h)]
  exact ⟨by rw [k'.notes]; exact hc.1, k'.feed.trans hc.2.2⟩

/-! ## Only a row on screen raises the mark (^70) -/

/-- The newest notification that has appeared on screen, as the seen marker holds it. -/
def State.seenMark (s : State) : Nat := s.notes.seen.1.mark

theorem actPress_notes (s : State) (kind : Kind) (k : Nat) : (actPress s kind k).notes = s.notes := by
  unfold actPress; split <;> (try split) <;> (try split) <;> rfl

theorem actStep_notes (s : State) (kind : Kind) (k : Nat) : (actStep s kind k).1.notes = s.notes := by
  have h := actPress_notes s kind k
  unfold actStep; dsimp only; split
  · split <;> exact h
  · exact h

theorem onAnswer0_notes (s : State) (id : Nat) (a : Answer) : (onAnswer0 s id a).1.notes = s.notes := by
  unfold onAnswer0
  generalize readPage a = pr
  obtain ⟨page, prob⟩ := pr
  dsimp only
  split
  · split
    · rfl
    · split
      · try dsimp only
        split <;> rfl
      · rfl
  · split <;> rfl

theorem onAnswer_notes (s : State) (id : Nat) (a : Answer) : (onAnswer s id a).1.notes = s.notes :=
  onAnswer0_notes s id a

theorem noteAnswer_mark (s : State) (id : Nat) (a : Answer) :
    (noteAnswer s id a).1.notes.seen.1.mark ≤ s.notes.seen.1.mark := by
  unfold noteAnswer
  split
  dsimp only
  split
  · split
    · rw [hearSeen_mark]; exact Nat.le_refl _
    · exact Nat.le_refl _
  split
  · split
    · rw [hearSeen_mark]; exact Nat.le_refl _
    · exact Nat.le_refl _
  split
  · split
    · exact Nat.le_refl _
    · exact Nat.le_refl _
  split
  · split
    · split
      · exact Nat.le_refl _
      · exact Nat.le_refl _
    · exact Nat.le_refl _
  split
  · split
    · rw [hearSeen_mark]; exact Nat.le_refl _
    · split
      · rw [hearSeen_mark]; exact Nat.le_refl _
      · rw [hearSeen_mark]; exact Nat.le_refl _
  · exact Nat.le_refl _

theorem handleOut_mark (acc : State × List Effect) (o : Out) :
    (handleOut acc o).1.seenMark ≤ acc.1.seenMark := by
  cases o with
  | answer id a =>
    show (answerCall acc.1 id a).1.seenMark ≤ _
    unfold answerCall; split
    · exact noteAnswer_mark _ _ _
    · exact Nat.le_of_eq (congrArg (fun n : Notes => n.seen.1.mark) (onAnswer_notes _ _ _))
  | event e =>
    cases e <;> first
      | exact Nat.le_refl _
      | (rename_i x; cases x <;> exact Nat.le_refl _)
      | (dsimp only [handleOut, onEvent, sendOwn, State.seenMark]; split <;> first | exact Nat.le_refl _ | exact Nat.zero_le _)
  | _ => exact Nat.le_refl _

theorem foldl_mark : ∀ (outs : List Out) (acc : State × List Effect),
    (outs.foldl handleOut acc).1.seenMark ≤ acc.1.seenMark
  | [], _ => Nat.le_refl _
  | o :: rest, acc => Nat.le_trans (foldl_mark rest _) (handleOut_mark acc o)

theorem drive_mark (s : State) (i : Session.Input) : (drive s i).1.seenMark ≤ s.seenMark :=
  foldl_mark _ _

theorem startRefresh_mark (s : State) : (startRefresh s).1.seenMark ≤ s.seenMark := by
  unfold startRefresh
  split
  · exact drive_mark _ _
  · exact Nat.le_refl _

theorem startLoadMore_mark (s : State) : (startLoadMore s).1.seenMark ≤ s.seenMark := by
  unfold startLoadMore
  split
  · exact drive_mark _ _
  · exact Nat.le_refl _

theorem driveSession_mark (s : State) (i : Session.Input) :
    (driveSession s i).1.seenMark ≤ s.seenMark := by
  unfold driveSession
  try dsimp only
  split
  · exact Nat.le_trans (startRefresh_mark _) (drive_mark _ _)
  · exact drive_mark _ _

theorem loadSources_notes : ∀ (s : State) (srcs : List String), (loadSources s srcs).1.notes = s.notes
  | _, [] => rfl
  | s, src :: rest => by
    simp only [loadSources]
    split
    · exact loadSources_notes _ rest
    · exact loadSources_notes s rest

theorem appearRow_notes (s : State) (k : Nat) : (appearRow s k).1.notes = s.notes := by
  unfold appearRow
  split
  · rfl
  · exact loadSources_notes _ _

/-- What a command does to the mark: nothing raises it but a row of the list coming into view,
and that, only up to the newest notification of the row. -/
def MarkStep (s t : State) : Prop :=
  t.seenMark ≤ s.seenMark ∨ ∃ g ∈ s.noteGroups, t.seenMark ≤ newestMs g.members

theorem MarkStep.le {s t : State} (h : t.seenMark ≤ s.seenMark) : MarkStep s t := Or.inl h

theorem MarkStep.calm {s t : State} (h : Calm s t) : MarkStep s t := Or.inl (Nat.le_of_eq h.mark)

theorem step0_mark (s : State) (c : Cmd) : MarkStep s (step0 s c).1 := by
  cases c with
  | signIn =>
    simp only [step0, signIn]
    split
    · exact .le (driveSession_mark _ _)
    · exact .le (Nat.le_refl _)
  | loadMore => exact .le (startLoadMore_mark s)
  | refresh => exact .le (startRefresh_mark s)
  | signOut => exact .le (driveSession_mark _ _)
  | appearRow k => exact .le (Nat.le_of_eq (congrArg (fun n : Notes => n.seen.1.mark) (appearRow_notes s k)))
  | openPost k =>
    simp only [step0, Sky.openPost]
    split <;> exact .le (Nat.le_refl _)
  | openNotes =>
    show MarkStep s (if s.tab == .notifications then notesTop s else openNotes s).1
    split
    · exact .le (Nat.le_refl _)
    · exact MarkStep.le (Nat.le_of_eq
        ((startNoteRefresh_calm { s with tab := .notifications }).trans (markSeenNow_calm _)).mark)
  | openHome =>
    show MarkStep s (if s.tab == .home then feedTop s else ({ s with tab := .home }, [])).1
    split <;> exact .le (Nat.le_refl _)
  | noteShowNew => exact .le (Nat.le_refl _)
  | noteAct kind k =>
    show MarkStep s (noteActStep s kind k)
    unfold noteActStep; split
    · split <;> exact .le (Nat.le_refl _)
    · exact .le (Nat.le_refl _)
  | noteOpen k =>
    show MarkStep s (Sky.noteOpen s k).1
    unfold Sky.noteOpen; split <;> exact .le (Nat.le_refl _)
  | noteCopy k =>
    show MarkStep s (Sky.noteCopy s k).1
    unfold Sky.noteCopy; split <;> exact .le (Nat.le_refl _)
  | noteRefresh => exact .le (Nat.le_of_eq (startNoteRefresh_calm s).mark)
  | noteMore => exact .le (Nat.le_of_eq (startNoteMore_calm s).mark)
  | noteAppear k =>
    show MarkStep s (noteAppear s k).1
    unfold noteAppear; split
    · exact .le (Nat.le_refl _)
    split
    · next g hg =>
      have c := markSeenNow_calm
        { s with notes := { s.notes with
            seen := s.notes.seen.appear (newestMs g.members),
            fresh := min s.notes.fresh (s.noteGroups.findIdx (·.key == k)) } }
      have hm : (markSeenNow { s with notes := { s.notes with
            seen := s.notes.seen.appear (newestMs g.members),
            fresh := min s.notes.fresh (s.noteGroups.findIdx (·.key == k)) } }).1.seenMark
          = max s.seenMark (newestMs g.members) := c.mark
      unfold MarkStep; rw [hm]
      by_cases hle : newestMs g.members ≤ s.seenMark
      · exact Or.inl (by omega)
      · exact Or.inr ⟨g, List.mem_of_find?_eq_some hg, by omega⟩
    · exact .le (Nat.le_refl _)
  | act kind k =>
    show MarkStep s (actStep s kind k).1
    exact .le (Nat.le_of_eq (congrArg (·.seen.1.mark) (actStep_notes s kind k)))
  | undoMute =>
    show MarkStep s (undoMuteStep s)
    unfold undoMuteStep; split
    · split <;> exact .le (Nat.le_refl _)
    · exact .le (Nat.le_refl _)
  | copyLink k =>
    show MarkStep s (Sky.copyLink s k).1
    unfold Sky.copyLink; split <;> exact .le (Nat.le_refl _)
  | msg m =>
    simp only [step0]
    cases m with
    | reply id r =>
      simp only [receive0]
      split
      · next k _ =>
        cases k with
        | readService =>
          simp only [onReadService]
          apply MarkStep.le
          split <;> (try split) <;> (try split) <;> exact Nat.le_refl _
        | readAccount =>
          simp only [onReadAccount]
          apply MarkStep.le
          split
          · split
            · exact driveSession_mark _ _
            · exact Nat.le_refl _
          · exact Nat.le_refl _
        | _ => exact .le (Nat.le_refl _)
      · split
        · exact .le (Nat.le_trans (Nat.le_of_eq (flushNotes_calm _).mark) (driveSession_mark _ _))
        · split <;> exact .le (Nat.le_refl _)
    | timer n =>
      simp only [receive0]
      split
      · exact .le (Nat.le_refl _)
      · split
        · exact MarkStep.calm ((hearSeen_calm _ _).trans (flushNotes_calm _))
        · split <;> exact .le (Nat.le_refl _)
    | sub sb e =>
      cases e
      case tick =>
        show MarkStep s (flushNotes { s with notes := { s.notes with pollDue := true } }).1
        exact MarkStep.calm ((⟨rfl, rfl, rfl, rfl⟩ : Calm s { s with notes := { s.notes with pollDue := true } }).trans
          (flushNotes_calm _))
      all_goals exact .le (Nat.le_refl _)
    | _ => exact .le (Nat.le_refl _)
  | _ => exact .le (Nat.le_refl _)

theorem settle_mark (s : State) : (settle s).1.seenMark = s.seenMark := by
  rw [State.seenMark, settle_fst]; split <;> rfl

theorem flushIf_notes (b : Bool) (s : State) : (flushIf b s).1.notes = s.notes := by
  obtain ⟨_, _, _, e, -⟩ := flushIf_flushed b s; rw [e]

theorem flushIf_tab (b : Bool) (s : State) : (flushIf b s).1.tab = s.tab := by
  obtain ⟨_, _, _, e, -⟩ := flushIf_flushed b s; rw [e]

theorem step1_mark (s : State) (c : Cmd) :
    (step1 s c).1.seenMark = (step0 (clearOut s) c).1.seenMark := by
  rw [step1_fst, State.seenMark, (tidy_core _).notes]
  rw [show (settle (flushIf (live s.session) (step0 (clearOut s) c).1).1).1.notes.seen.1.mark =
      (flushIf (live s.session) (step0 (clearOut s) c).1).1.seenMark from settle_mark _]
  unfold State.seenMark; rw [flushIf_notes]

/-- **The seen marker only passes what has been on screen**: no step raises the mark (and so
no `updateSeen`, which never passes it, ^70's `SeenMonotone`) but a row of the list coming into
view, and that one only up to the newest notification of a row the list shows. -/
def SeenOnScreen : Prop :=
  ∀ (s : State) (c : Cmd), (s.step c).1.seenMark ≤ s.seenMark ∨
    ∃ g ∈ s.noteGroups, (s.step c).1.seenMark ≤ newestMs g.members

theorem seenOnScreen : SeenOnScreen := fun s c => by
  rcases step_cases s c with e | e <;> rw [e]
  · show MarkStep s (step1 s c).1
    unfold MarkStep; rw [step1_mark]; exact step0_mark (clearOut s) c
  · show MarkStep s.blank (step1 s.blank c).1
    unfold MarkStep; rw [step1_mark]; exact step0_mark (clearOut s.blank) c

/-! ## Signed out, no notes and no poll (^71) -/

/-- Signed out, the notes hold no notifications and wait on no call, and Home shows. -/
def NotesSignedOut (s : State) : Prop :=
  live s.session = false →
    s.notes.list = {} ∧ s.notes.poll = none ∧ s.notes.seenCalls = [] ∧ s.tab = .home

theorem settle_notesOut (s : State) : NotesSignedOut (settle s).1 := by
  rw [NotesSignedOut, settle_fst]
  split
  · next h => intro h'; simp_all
  · intro _; exact ⟨rfl, rfl, rfl, rfl⟩

theorem step1_notesOut (s : State) (c : Cmd) : NotesSignedOut (step1 s c).1 := by
  rw [step1_fst]
  have k := tidy_core (settle (flushIf (live s.session) (step0 (clearOut s) c).1).1).1
  have h := settle_notesOut (flushIf (live s.session) (step0 (clearOut s) c).1).1
  unfold NotesSignedOut at h ⊢; rw [k.session, k.notes, k.tab]; exact h

theorem step_notesOut (s : State) (c : Cmd) : NotesSignedOut (s.step c).1 := by
  rcases step_cases s c with e | e <;> rw [e]
  · exact step1_notesOut s c
  · exact step1_notesOut s.blank c

theorem notesOut_initial : NotesSignedOut initial := fun _ => ⟨rfl, rfl, rfl, rfl⟩

/-- **At most one poll**: with a poll in flight, or signed out, Sky starts none (and `startPoll`
is the only place Sky asks for the unread count). -/
def PollOnce : Prop :=
  ∀ s : State, (s.notes.poll.isSome = true ∨ live s.session = false) → (startPoll s).2 = []

theorem pollOnce : PollOnce := fun s h => by
  unfold startPoll; split
  · next hc =>
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
    rcases h with h | h
    · simp [hc.2] at h
    · simp [hc.1] at h
  · rfl

/-- **The badge is the unread count shown**, or none at 0. -/
def BadgeIsCount (s : State) : Prop :=
  s.notes.badge = if s.notes.unreadShown = 0 then none else some (toString s.notes.unreadShown)

theorem badgeIsCount (s : State) : BadgeIsCount s := rfl

/-! ## The groups (^68, ^69) -/

/-- **The groups partition the notifications shown, in order**: flattened, they are the list
less the muted accounts'; each is a run of one reason and subject (more than one only for likes,
reposts and follows), and no two next to each other could have been one. -/
def GroupsPartition : Prop :=
  ∀ (muted : String → Bool) (l : List Notification),
    ((shownGroups muted l).map (·.members)).flatten = l.filter (fun n => !muted n.author.did) ∧
    (∀ g ∈ shownGroups muted l, g.Ok) ∧ Apart (shownGroups muted l)

theorem groupsPartition : GroupsPartition := fun _ _ =>
  ⟨flatten_groupAll _, groupAll_ok _, groupAll_maximal _⟩

/-- **No row is from a muted account.** -/
def NoMutedRow (s : State) : Prop := ∀ g ∈ s.noteGroups, ∀ n ∈ g.members, s.muted n.author.did = false

theorem noMutedRow (s : State) : NoMutedRow s := shownGroups_unmuted s.muted s.notes.list.items

end Sky
