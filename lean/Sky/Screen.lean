module

public import Sky.View
public import Cairn.Runtime.Step

/-! # The notifications on screen (cairn#255)

* `noteAct_post`: a press on a notification's Like, Repost, Follow back or Mute shows the other
  value for its key in the press's own step (^76, ^77, ^79, ^80, ^83).
* `noteOpen_post`, `noteCopy_post`, `noteShowNew_post`: the row's other moves (^66, ^75, ^81,
  ^82).
* `PlacesKept` (^84): Home or Notifications shows, each list under one ref in every state, both
  kept by the runtime while the other shows; a new generation goes to the top when it shows.
* `DockShown` (^85): after every step Sky has sent the Dock the unread count the tab shows. -/

@[expose] public section

namespace Sky
open Cairn Cairn.Runtime CairnAtproto CairnAtproto.Session

/-! ## Acting from a notification -/

theorem noteActStep_session (s : State) (kind : Kind) (k : Nat) :
    (noteActStep s kind k).session = s.session := by
  unfold noteActStep; split
  · split <;> rfl
  · rfl

/-- A notification's act leaves the tables as the press set them. -/
theorem noteAct_tables {s : State} {kind : Kind} {k : Nat} (h : live s.session = true) :
    (s.step (.noteAct kind k)).1.acts.tables = (noteActStep (clearOut s.blank) kind k).acts.tables := by
  show (step1 s.blank (.noteAct kind k)).1.acts.tables = _
  rw [step1_fst, tidy_acts]
  have hf := flushIf_flushed (live s.blank.session) (step0 (clearOut s.blank) (.noteAct kind k)).1
  have hl : live (flushIf (live s.blank.session) (step0 (clearOut s.blank) (.noteAct kind k)).1).1.session = true := by
    rw [hf.live]; show live (noteActStep (clearOut s.blank) kind k).session = true
    rw [noteActStep_session]; exact h
  rw [settle_live hl, flushIf_tables]
  rfl

/-- ^76, ^77, ^79, ^80, ^83: a press on a notification shows the other value for its key (the
post, or its account) in the press's own step. -/
theorem noteAct_post {s : State} {kind : Kind} {k : Nat} (h : canNoteAct s kind k = true) :
    (s.step (.noteAct kind k)).1.acts.on kind (noteKey s kind k) = !s.acts.on kind (noteKey s kind k) := by
  have hl : live s.session = true := by
    simp only [canNoteAct, Bool.and_eq_true] at h; exact h.1.1
  have e : ∀ a b : Acts, a.tables = b.tables → ∀ key, a.on kind key = b.on kind key := by
    intro a b hab key; cases kind <;> simp only [Acts.on, hab]
  rw [e _ _ (noteAct_tables hl)]
  have hc : canNoteAct (clearOut s.blank) kind k = true := h
  cases kind with
  | mute =>
    simp only [noteActStep, hc, ↓reduceIte]
    exact Acts.toggleMute_on _ _
  | like =>
    simp only [noteActStep, hc, ↓reduceIte]
    exact Acts.toggle_on _ _ _ (by decide) _
  | repost =>
    simp only [noteActStep, hc, ↓reduceIte]
    exact Acts.toggle_on _ _ _ (by decide) _
  | follow =>
    simp only [noteActStep, hc, ↓reduceIte]
    exact Acts.toggle_on _ _ _ (by decide) _

theorem noteAct_post_of {s : State} {kind : Kind} {k : Nat} (h : canNoteAct s kind k = true)
    {key : String} (hk : noteKey s kind k = key) :
    (s.step (.noteAct kind k)).1.acts.on kind key = !s.acts.on kind key := hk ▸ noteAct_post h

theorem notePost_key {s : State} {k : Nat} {p : Post} (hp : s.notePost? k = some p) (kind : Kind)
    (hk : kind = .like ∨ kind = .repost) : noteKey s kind k = p.uri := by
  rcases hk with rfl | rfl <;> simp [noteKey, hp]

theorem noteAuthor_key {s : State} {k : Nat} {a : Profile} (ha : s.noteAuthor? k = some a) (kind : Kind)
    (hk : kind = .follow ∨ kind = .mute) : noteKey s kind k = a.did := by
  rcases hk with rfl | rfl <;> simp [noteKey, ha]

/-! ## Opening, copying, "N new" -/

/-- Opening what a notification is about, or copying its link, while signed in: the feed, the
session and the notes stay. -/
theorem noteOpen_post {s : State} (h : live s.session = true) (k : Nat) :
    (s.step (.noteOpen k)).1.feed = s.feed ∧ (s.step (.noteOpen k)).1.session = s.session ∧
      (s.step (.noteOpen k)).1.notes = s.notes := by
  have c : (step0 (clearOut s.blank) (.noteOpen k)).1.session = s.session ∧
      (step0 (clearOut s.blank) (.noteOpen k)).1.feed = s.feed ∧
      (step0 (clearOut s.blank) (.noteOpen k)).1.notes = s.notes ∧
      (step0 (clearOut s.blank) (.noteOpen k)).1.acts.outbox = [] := by
    simp only [step0, Sky.noteOpen]; split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have l := step1_live (s := s.blank) (c := .noteOpen k) (by rw [c.1]; exact h) c.2.2.2
  exact ⟨l.feed.trans c.2.1, l.session.trans c.1, l.notes.trans c.2.2.1⟩

theorem noteCopy_post {s : State} (h : live s.session = true) (k : Nat) :
    (s.step (.noteCopy k)).1.feed = s.feed ∧ (s.step (.noteCopy k)).1.session = s.session ∧
      (s.step (.noteCopy k)).1.notes = s.notes := by
  have c : (step0 (clearOut s.blank) (.noteCopy k)).1 = clearOut s.blank := by
    simp only [step0, Sky.noteCopy]; split <;> rfl
  have l := step1_live (s := s.blank) (c := .noteCopy k) (by rw [c]; exact h) (by rw [c]; rfl)
  exact ⟨l.feed.trans (by rw [c]; rfl), l.session.trans (by rw [c]; rfl), l.notes.trans (by rw [c]; rfl)⟩

/-- "N new" in the notifications, while signed in: a new generation of the list (so `dock`
puts it at its top); the feed stays. -/
theorem noteShowNew_post {s : State} (h : live s.session = true) :
    s.notes.gen < (s.step .noteShowNew).1.notes.gen ∧ (s.step .noteShowNew).1.feed = s.feed := by
  have l := step1_live (s := s.blank) (c := .noteShowNew) h rfl
  show s.notes.gen < (step1 s.blank .noteShowNew).1.notes.gen ∧ (step1 s.blank .noteShowNew).1.feed = s.feed
  exact ⟨by rw [l.notes]; exact Nat.lt_succ_self _, l.feed⟩

/-! ## Refresh, for the list shown (^51) -/

theorem refreshShown_post {s : State} (h : canRefreshShown s = true) :
    ((s.tab == .home) = true → (s.step .refresh).1.feed.items = s.feed.items ∧
        (s.step .refresh).1.feed.refresh = some s.nextCall) ∧
      ((s.tab == .home) = false → (s.step .noteRefresh).1.notes.list.items = s.notes.list.items ∧
        (s.step .noteRefresh).1.notes.list.refresh = some s.nextCall) := by
  unfold canRefreshShown at h
  constructor
  · intro ht; rw [ht] at h
    exact ⟨(refresh_post h).1, (refresh_post h).2.2⟩
  · intro ht; rw [ht] at h
    exact noteRefresh_post h

/-! ## The two places (^84) -/

/-- The lists the runtime keeps while they are off screen: the feed's and the notifications'. -/
def keptLists (_ : State) : List ControlRef := [feedRef, notesRef]

/-- ^84: Home or Notifications shows; each list has one ref in every state; the runtime keeps
both, so the offset the view reads for the one not shown is the one it had (cairn's
`fixUI_keeps_offset`), and the list's record too (`fixUI_keeps_list`); and a list given a new
generation (a refresh that replaced it, "N new", its tab pressed again) is put at its top in the
step it shows. Cairn's `fixUI_keeps_offset` lives in a non-`module` file (cairn#278), so
`Sky.Tests.keptOffset` applies it to `keptLists` there. -/
def PlacesKept : Prop :=
  (∀ s : State, s.tab = .home ∨ s.tab = .notifications) ∧
  (∀ s : State, (feedList s).ref = feedRef ∧ (notesList s).ref = notesRef ∧
    feedRef ∈ keptLists s ∧ notesRef ∈ keptLists s) ∧
  (∀ (s : State) (laid : Laid) (pointer : Option Point) (ui : UI),
    (fixUI laid pointer ui (keptLists s)).kept =
      keepOff (onScreen (scrollersOf laid)) (keptLists s) ui.scroll ui.kept) ∧
  (∀ x : State, feedAim x = true → Effect.scrollTo feedRef .start ∈ (dock x).2) ∧
  (∀ x : State, notesAim x = true → Effect.scrollTo notesRef .start ∈ (dock x).2)

theorem placesKept : PlacesKept := by
  refine ⟨fun s => ?_, fun s => ⟨rfl, rfl, by simp [keptLists], by simp [keptLists]⟩,
    fun _ _ _ _ => rfl,
    fun x h => ?_, fun x h => ?_⟩
  · cases s.tab
    · exact Or.inl rfl
    · exact Or.inr rfl
  · simp [dock, h]
  · simp [dock, h]

/-! ## The Dock's badge (^85) -/

/-- Sky has sent the Dock the unread count shown. -/
def BadgeSent (s : State) : Prop := s.unreadSent = s.notes.unreadShown

/-- `dock` sends the badge exactly when the count shown is not the one it last sent, and then
the badge the tab shows. -/
def DockSends : Prop :=
  ∀ x : State, (Effect.badge x.notes.badge ∈ (dock x).2 ↔ x.notes.unreadShown ≠ x.unreadSent)

theorem dockSends : DockSends := by
  intro x
  unfold dock
  by_cases e : x.notes.unreadShown = x.unreadSent
  · simp [e]
  · simp [e]

theorem tidy_sent (x : State) : BadgeSent (tidy x).1 := rfl

theorem step_sent (s : State) (c : Cmd) : BadgeSent (s.step c).1 := by
  rcases step_cases s c with e | e <;> rw [e]
  · rw [step1_fst]; exact tidy_sent _
  · show (step1 s.blank c).1.unreadSent = (step1 s.blank c).1.notes.unreadShown
    rw [step1_fst]; exact tidy_sent _

theorem sent_initial : BadgeSent initial := rfl

end Sky

namespace Sky

open Cairn

/-! ## The sign-in fields, stated for `step` (so a claim's proof needn't unfold it) -/

theorem step_editIdentifier (s : State) (op : TextOp) :
    (s.step (.editIdentifier op)).1.identifier = (Text.Field.apply op s.identifier).1 := by
  show (step1 s.blank (.editIdentifier op)).1.identifier = _
  rw [step1_identifier]; rfl

theorem step_nextField (s : State) : (s.step .nextField).1.identifier = s.identifier := by
  show (step1 s.blank .nextField).1.identifier = _
  rw [step1_identifier]; rfl

theorem step_editPassword_identifier (s : State) (op : TextOp) :
    (s.step (.editPassword op)).1.identifier = s.identifier := by
  show (step1 s (.editPassword op)).1.identifier = _
  rw [step1_identifier]; rfl

theorem step_editService (s : State) (op : TextOp) :
    (s.step (.editService op)).1.service = (Text.Field.apply op s.service).1 := by
  show (step1 s.blank (.editService op)).1.service = _
  rw [step1_service]; rfl

theorem step_openHelp_phase (s : State) : (s.step .openHelp).1.session.phase = s.session.phase := by
  show (step1 s.blank .openHelp).1.session.phase = _
  rw [step1_phase]; rfl

theorem step_password (s : State) (c : Cmd) (h1 : c ≠ .signIn) (h2 : ∀ op, c ≠ .editPassword op) :
    (s.step c).1.password = s.password := by
  rw [step_blind s c h1 h2]

end Sky
