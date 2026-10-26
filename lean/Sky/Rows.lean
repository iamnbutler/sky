module

public import Sky.Secrets

/-! # The rows and the images: what every step keeps

* `RowsFollow`: after every step the rows are the feed's items, the keys are `top`, `top + 1`, …
  then the end row's `0`, and `top` is never `0`, so no post's key is the end row's (^46).
* `prepend_keeps`: posts put on top of the feed take the keys below the first; every post already
  there keeps its key and the list stays the same (`gen`), so the runtime's anchor finds the
  reader's post where it was (^46, with Cairn's `VList.record_keeps`, ^35).
* `ImagesNear`: when a row comes into view, every image load still in flight is for a row within
  `span` rows of it; signed out, none is, and there are no rows (^47). -/

@[expose] public section

namespace Sky
open Cairn CairnAtproto CairnAtproto.Session

/-! ## The rows are untouched until `tidy` -/

theorem onAnswer0_rows (s : State) (id : Nat) (a : Answer) : (onAnswer0 s id a).1.rows = s.rows := by
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

theorem onAnswer_rows (s : State) (id : Nat) (a : Answer) : (onAnswer s id a).1.rows = s.rows :=
  onAnswer0_rows s id a
theorem NotesOnly.rows {s t : State} (h : NotesOnly s t) : t.rows = s.rows := by
  obtain ⟨n, p, rfl⟩ := h; rfl

theorem sendOwn_rows (s : State) (k : Own) (r : Request) : (sendOwn s k r).1.rows = s.rows := rfl

theorem handleOut_rows (acc : State × List Effect) (o : Out) :
    (handleOut acc o).1.rows = acc.1.rows := by
  cases o with
  | answer id a =>
    show (answerCall acc.1 id a).1.rows = acc.1.rows
    unfold answerCall; split
    · exact NotesOnly.rows (noteAnswer_only _ _ _).1
    · exact onAnswer_rows _ _ _
  | event e => cases e <;> first | rfl | (rename_i x; cases x <;> rfl)
  | _ => rfl

theorem foldl_rows : ∀ (outs : List Out) (acc : State × List Effect),
    (outs.foldl handleOut acc).1.rows = acc.1.rows
  | [], _ => rfl
  | o :: rest, acc => (foldl_rows rest _).trans (handleOut_rows acc o)

theorem drive_rows (s : State) (i : Session.Input) : (drive s i).1.rows = s.rows :=
  foldl_rows _ _

theorem startRefresh_rows (s : State) : (startRefresh s).1.rows = s.rows := by
  unfold startRefresh
  split
  · exact drive_rows _ _
  · rfl

theorem startLoadMore_rows (s : State) : (startLoadMore s).1.rows = s.rows := by
  unfold startLoadMore
  split
  · exact drive_rows _ _
  · rfl

theorem driveSession_rows (s : State) (i : Session.Input) : (driveSession s i).1.rows = s.rows := by
  unfold driveSession
  try dsimp only
  split
  · exact (startRefresh_rows _).trans (drive_rows _ _)
  · exact drive_rows _ _

theorem noteCall_rows (s : State) (f : Nat → Notes → Notes) (c : Call) :
    (Sky.noteCall s f c).1.rows = s.rows := drive_rows _ _

theorem sendSeen_rows (acc : State × List Effect) (a : Cairn.Optimistic.Act Nat) :
    (sendSeen acc a).1.rows = acc.1.rows := by
  cases a with
  | write k v => dsimp only [sendSeen]; exact noteCall_rows _ _ _
  | read k => dsimp only [sendSeen]; exact noteCall_rows _ _ _
  | _ => rfl

theorem foldl_sendSeen_rows : ∀ (as : List (Cairn.Optimistic.Act Nat)) (acc : State × List Effect),
    (as.foldl sendSeen acc).1.rows = acc.1.rows
  | [], _ => rfl
  | a :: as, acc => (foldl_sendSeen_rows as _).trans (sendSeen_rows acc a)

theorem startPoll_rows (s : State) : (startPoll s).1.rows = s.rows := by
  unfold startPoll; split
  · exact noteCall_rows _ _ _
  · rfl

theorem flushNotes_rows (s : State) : (flushNotes s).1.rows = s.rows := by
  unfold flushNotes; split
  · have h1 := foldl_sendSeen_rows s.notes.todo ({ s with notes := { s.notes with todo := [] } }, [])
    dsimp only; split
    · exact (startPoll_rows _).trans h1
    · exact h1
  · rfl

theorem hearSeen_rows (s : State) (e : SeenEv) : (hearSeen s e).1.rows = s.rows :=
  NotesOnly.rows (hearSeen_only s e).1

theorem startNoteRefresh_rows (s : State) : (startNoteRefresh s).1.rows = s.rows := by
  unfold startNoteRefresh; split
  · split
    · exact noteCall_rows _ _ _
    · rfl
  · rfl

theorem startNoteMore_rows (s : State) : (startNoteMore s).1.rows = s.rows := by
  unfold startNoteMore; split
  · split
    · exact noteCall_rows _ _ _
    · rfl
  · rfl

theorem markSeenNow_rows (s : State) : (markSeenNow s).1.rows = s.rows := by
  unfold markSeenNow; split
  · have := (foldl_seenAct s.notes.seen.markSeen.2
      ({ s with notes := { s.notes with seen := s.notes.seen.markSeen.1 } }, []) timers_nil).1
    exact (flushNotes_rows _).trans (NotesOnly.rows this)
  · rfl

theorem noteAppear_rows (s : State) (k : Nat) : (noteAppear s k).1.rows = s.rows := by
  unfold noteAppear; split
  · rfl
  · split
    · exact markSeenNow_rows _
    · rfl

theorem openNotes_rows (s : State) : (openNotes s).1.rows = s.rows := by
  unfold openNotes
  exact (markSeenNow_rows _).trans (startNoteRefresh_rows _)

theorem loadSources_rows (s : State) (srcs : List String) : (loadSources s srcs).1.rows = s.rows :=
  (loadSources_core s srcs).2.2.2.2

theorem step0_rows (s : State) (c : Cmd) : (step0 s c).1.rows = s.rows := by
  cases c with
  | signIn =>
    simp only [step0, signIn]
    split
    · exact driveSession_rows _ _
    · rfl
  | loadMore => exact startLoadMore_rows s
  | refresh => exact startRefresh_rows s
  | signOut => exact driveSession_rows _ _
  | appearRow k => exact (appearRow_core s k).2.2.2.2
  | openNotes => exact openNotes_rows s
  | noteRefresh => exact startNoteRefresh_rows s
  | noteMore => exact startNoteMore_rows s
  | noteAppear k => exact noteAppear_rows s k
  | openPost k =>
    simp only [step0, Sky.openPost]
    split <;> rfl
  | act kind k => exact (actStep_core s kind k).2.2.2.2.1
  | undoMute =>
    simp only [step0, undoMuteStep]
    split
    · split <;> rfl
    · rfl
  | copyLink k =>
    simp only [step0, Sky.copyLink]
    split <;> rfl
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
          split <;> (try split) <;> (try split) <;> rfl
        | readAccount =>
          simp only [onReadAccount]
          split
          · split
            · exact driveSession_rows _ _
            · rfl
          · rfl
        | _ => rfl
      · split
        · exact (flushNotes_rows _).trans (driveSession_rows _ _)
        · split <;> rfl
    | timer n =>
      simp only [receive0]
      split
      · rfl
      · split
        · exact (flushNotes_rows _).trans (hearSeen_rows _ _)
        · split <;> rfl
    | sub sb e =>
      cases e
      case tick => exact flushNotes_rows _
      all_goals rfl
    | _ => rfl
  | _ => rfl

theorem settle_rows (s : State) : (settle s).1.rows = s.rows := by
  rw [settle_fst]; split <;> rfl

/-- Signed out after `settle`, the feed is empty. -/
theorem settle_dead (s : State) (h : live (settle s).1.session = false) : (settle s).1.feed = {} := by
  rw [settle_fst] at h ⊢
  split
  · next hl => simp only [hl, ↓reduceIte] at h; exact absurd h (by simp)
  · rfl

/-! ## The rows follow the feed (^46) -/

/-- The rows as `Rows.make` builds them, from a first key that isn't the end row's. -/
def Rows.WF (r : Rows) : Prop := r = Rows.make r.top r.items ∧ 0 < r.top

theorem Rows.wf_make {top : Nat} (h : 0 < top) (items : List FeedItem) : (Rows.make top items).WF :=
  ⟨rfl, h⟩

theorem baseTop_pos : 0 < baseTop := by decide

theorem Rows.wf_empty : ({} : Rows).WF := ⟨rfl, baseTop_pos⟩

/-- ^46's first half: the rows are the feed's items, keyed `top`, `top + 1`, … and `0` last. -/
def RowsFollow (s : State) : Prop := s.rows.items = s.feed.items ∧ s.rows.WF

theorem change_same {old new : List FeedItem} (h : change old new = .same) : new = old := by
  unfold change at h
  split at h
  · assumption
  · split at h
    · cases h
    · split at h <;> cases h

theorem tidy_follows (t : State) (hw : t.rows.WF) (hd : live t.session = false → t.feed = {}) :
    RowsFollow (tidy t).1 := by
  unfold tidy restart
  split
  · split
    · next hs => exact ⟨(change_same hs).symm, hw⟩
    · split
      · next n _ hn => exact ⟨rfl, Rows.wf_make (by omega) _⟩
      · exact ⟨rfl, Rows.wf_make baseTop_pos _⟩
    · split
      · exact ⟨rfl, Rows.wf_make baseTop_pos _⟩
      · exact ⟨rfl, Rows.wf_make hw.2 _⟩
    · exact ⟨rfl, Rows.wf_make baseTop_pos _⟩
  · next hl =>
    simp only [Bool.not_eq_true] at hl
    exact ⟨by rw [hd hl], Rows.wf_empty⟩

theorem step1_follows (s : State) (c : Cmd) (h : s.rows.WF) : RowsFollow (step1 s c).1 := by
  rw [step1_fst]
  apply tidy_follows
  · rw [settle_rows, (flushIf_flushed _ _).rows, step0_rows]; exact h
  · exact settle_dead _

theorem step_follows (s : State) (c : Cmd) (h : s.rows.WF) : RowsFollow (s.step c).1 := by
  rcases step_cases s c with e | e <;> rw [e]
  · exact step1_follows s c h
  · exact step1_follows s.blank c h

theorem follows_initial : RowsFollow initial := ⟨rfl, Rows.wf_empty⟩

/-- ^46's second half: `n` posts put on top of rows that follow the feed take the `n` keys
below the first, every post already there keeps its key, the list stays the same, and the
new posts are counted. -/
def PrependKeeps : Prop :=
  ∀ (t : State) (new : List FeedItem), live t.session = true → t.rows.items ≠ [] → new ≠ [] →
    t.feed.items = new ++ t.rows.items → new.length < t.rows.top →
    (tidy t).1.rows = Rows.make (t.rows.top - new.length) t.feed.items ∧
      (tidy t).1.gen = t.gen ∧ (tidy t).1.fresh = t.fresh + new.length

theorem change_prepend {old new : List FeedItem} (ho : old ≠ []) (hn : new ≠ []) :
    change old (new ++ old) = .prepended new.length := by
  have hlen : old.length < (new ++ old).length := by
    simp only [List.length_append]
    have : 0 < new.length := List.length_pos_iff.mpr hn
    omega
  have hne : new ++ old ≠ old := fun e => by
    have := congrArg List.length e
    simp only [List.length_append] at this
    exact absurd (List.length_pos_iff.mpr hn) (by omega)
  have hd : (new ++ old).drop ((new ++ old).length - old.length) = old := by
    simp only [List.length_append, Nat.add_sub_cancel]
    exact List.drop_left
  unfold change
  simp only [hne, ↓reduceIte]
  have hoe : old.isEmpty = false := List.isEmpty_eq_false_iff.mpr ho
  have h1 : old.length < new.length + old.length := by simpa using hlen
  simp only [hoe, Bool.not_false, List.length_append, Nat.add_sub_cancel, h1,
    List.drop_left, decide_true, Bool.and_self, ↓reduceIte]

theorem prependKeeps : PrependKeeps := by
  intro t new hl ho hn he hlt
  unfold tidy
  simp only [hl, ↓reduceIte]
  rw [he, change_prepend ho hn]
  simp [hlt]

/-! ## Image loads (^47) -/

theorem pending_load (t : Images) (id : Nat) (src : String) (p : Nat × String)
    (h : p ∈ (t.load id src).1.pending) : p ∈ t.pending ∨ p.2 = src := by
  simp only [Images.load, List.mem_cons, List.mem_filter] at h
  rcases h with rfl | ⟨h, -⟩
  · exact Or.inr rfl
  · exact Or.inl h

theorem loadSources_pending : ∀ (s : State) (srcs : List String) (p : Nat × String),
    p ∈ (loadSources s srcs).1.images.pending → p ∈ s.images.pending ∨ p.2 ∈ srcs
  | _, [], _, h => Or.inl h
  | s, src :: rest, p, h => by
    simp only [loadSources] at h
    split at h
    · rcases loadSources_pending _ rest p h with h | h
      · rcases pending_load _ _ _ p h with h | h
        · exact Or.inl h
        · exact Or.inr (h ▸ List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases loadSources_pending s rest p h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem tidy_pending (t : State) (p : Nat × String) (h : p ∈ (tidy t).1.images.pending) :
    p ∈ t.images.pending := by
  unfold tidy restart at h
  split at h
  · split at h
    · exact h
    · split at h
      · exact h
      · cases h
    · split at h
      · cases h
      · exact h
    · cases h
  · cases h

theorem settle_images (s : State) : (settle s).1.images = s.images := by
  rw [settle_fst]; split <;> rfl

theorem row_near (r : Rows) (i : Nat) (it : FeedItem) (h : r.arr[i]? = some it) (n : Nat) :
    ∀ src ∈ sourcesOf it, src ∈ r.sourcesNear i n := by
  intro src hs
  simp only [Rows.sourcesNear, List.mem_flatMap, List.mem_filterMap, List.mem_range']
  exact ⟨it, ⟨i, ⟨i - (i - n), by omega, by omega⟩, h⟩, hs⟩

theorem appearRow_pending (s : State) (k i : Nat) (hi : s.rows.index? k = some i)
    (p : Nat × String) (h : p ∈ (appearRow s k).1.images.pending) :
    p.2 ∈ s.rows.sourcesNear i span := by
  unfold appearRow at h
  rw [hi] at h
  dsimp only at h
  rcases loadSources_pending _ _ p h with h | h
  · obtain ⟨-, hp⟩ := Images.pending_cancelWhere s.images
      (fun src => !(s.rows.sourcesNear i span).contains src) p h
    simpa using hp
  · split at h
    · next it hit => exact row_near s.rows i it hit span _ h
    · cases h

/-- ^47: when the row with key `k` (row `i`) comes into view, every image load in flight is for a
row within `span` rows of it; and after any step that leaves Sky signed out, no load is in flight
and there are no rows. -/
def ImagesNear : Prop :=
  (∀ (s : State) (k i : Nat), s.rows.index? k = some i →
    ∀ p ∈ (s.step (.appearRow k)).1.images.pending, p.2 ∈ s.rows.sourcesNear i span) ∧
  (∀ (s : State) (c : Cmd), live (s.step c).1.session = false →
    (s.step c).1.images.pending = [] ∧ (s.step c).1.rows = {})

theorem tidy_dead (t : State) (h : live (tidy t).1.session = false) :
    (tidy t).1.images.pending = [] ∧ (tidy t).1.rows = {} := by
  rw [(tidy_core t).session] at h
  unfold tidy
  simp only [h, Bool.false_eq_true, ↓reduceIte]
  exact ⟨trivial, trivial⟩

theorem step1_dead (s : State) (c : Cmd) (h : live (step1 s c).1.session = false) :
    (step1 s c).1.images.pending = [] ∧ (step1 s c).1.rows = {} := by
  rw [step1_fst] at h ⊢; exact tidy_dead _ h

theorem imagesNear : ImagesNear := by
  refine ⟨fun s k i hi p hp => ?_, fun s c h => ?_⟩
  · have hp' : p ∈ (step1 s.blank (.appearRow k)).1.images.pending := hp
    rw [step1_fst] at hp'
    have := tidy_pending _ p hp'
    rw [settle_images, (flushIf_flushed _ _).images] at this
    exact appearRow_pending (clearOut s.blank) k i hi p this
  · rcases step_cases s c with e | e <;> rw [e] at h ⊢
    · exact step1_dead s c h
    · exact step1_dead s.blank c h

/-! ## The rows' moves -/

theorem bool_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> simp_all

def canShowNew (s : State) : Bool := live s.session && s.fresh != 0

def newPostsLabel (n : Nat) : String := if n = 1 then "1 new post" else s!"{n} new posts"

/-- A post's row can be opened (or its link copied): signed in, and the row shows (not hidden by a
mute). -/
def canOpenRow (s : State) (k : Nat) : Bool := live s.session && s.rows.has k && !hiddenAt s k

theorem tidy_gen (t : State) : t.gen ≤ (tidy t).1.gen := by
  unfold tidy restart
  split
  · split
    · exact Nat.le_refl _
    · split
      · exact Nat.le_refl _
      · exact Nat.le_succ _
    · split
      · exact Nat.le_succ _
      · exact Nat.le_refl _
    · exact Nat.le_succ _
  · exact Nat.le_refl _

/-- New posts, while signed in: a new list (so it starts at the top), the feed as it was. -/
theorem showNew_post {s : State} (h : live s.session = true) :
    s.gen < (s.step .showNew).1.gen ∧ (s.step .showNew).1.feed = s.feed := by
  show s.gen < (step1 s.blank .showNew).1.gen ∧ (step1 s.blank .showNew).1.feed = s.feed
  rw [step1_fst, flushIf_nil (s := (step0 (clearOut s.blank) .showNew).1) rfl,
    settle_live (s := (step0 (clearOut s.blank) .showNew).1) h]
  exact ⟨Nat.lt_of_lt_of_le (Nat.lt_succ_self s.gen) (tidy_gen (step0 (clearOut s.blank) .showNew).1),
    (tidy_core _).feed⟩

theorem openPost_core (s : State) (k : Nat) :
    (step0 s (.openPost k)).1.session = s.session ∧ (step0 s (.openPost k)).1.feed = s.feed := by
  simp only [step0, Sky.openPost]
  split <;> exact ⟨rfl, rfl⟩

/-- Opening a post, or a row coming into view, while signed in: the feed and the session stay. -/
theorem openPost_post {s : State} (h : live s.session = true) (k : Nat) :
    (s.step (.openPost k)).1.feed = s.feed ∧ (s.step (.openPost k)).1.session = s.session := by
  have c := (openPost_core (clearOut s.blank) k)
  have ho : (step0 (clearOut s.blank) (.openPost k)).1.acts.outbox = [] := by
    simp only [step0, Sky.openPost]; split <;> rfl
  have l := step1_live (s := s.blank) (c := .openPost k) (by rw [c.1]; exact h) ho
  exact ⟨l.feed.trans c.2, l.session.trans c.1⟩

theorem appearRow_post {s : State} (h : live s.session = true) (k : Nat) :
    (s.step (.appearRow k)).1.feed = s.feed ∧ (s.step (.appearRow k)).1.session = s.session := by
  have c := appearRow_core (clearOut s.blank) k
  have ho : (step0 (clearOut s.blank) (.appearRow k)).1.acts.outbox = [] :=
    congrArg Acts.outbox (appearRow_acts (clearOut s.blank) k)
  have l := step1_live (s := s.blank) (c := .appearRow k)
    (by show live (appearRow (clearOut s.blank) k).1.session = true; rw [c.1]; exact h) ho
  exact ⟨l.feed.trans c.2.1, l.session.trans c.1⟩

end Sky
