module

public import CairnAtproto

/-! # The feed

What Sky shows of the home timeline: the items, newest first, the cursor of the last page and
whether that page was the last (`atEnd`), and the load-more and refresh in flight, each with the
app's call id (`CairnAtproto.Session.Input.call`).

* **Load more** asks from the cursor the feed holds; its page is appended only if the feed still
  holds that cursor when it comes (`gotLoadMore`), so a page for a feed that has moved on is
  dropped.
* **Refresh** asks for the head. If the page holds the feed's first item, the items above it are
  the new ones and go on top (`newOnTop`); if it doesn't (more than a page arrived), the feed is
  replaced by the page and its cursor, and a load-more in flight is for a feed that is gone
  (`headPage` forgets it; the app withdraws its request).

Items are keyed by their post's URI and the repost that put them in the timeline (`itemKey`), as
the server's timeline is. What is proved here is about the merges, against a server timeline
`T` (newest first, keys distinct) that only grows at its head:

* `run_append`, `headPage_run`, `run_grow`, `run_nodup`: a feed that is a contiguous run of `T`
  stays one: a load-more page that follows it, a head page of `T` or of a grown `T`, and a run
  has no duplicates (claim ^20).
* `gotLoadMore_stale`: a load-more page for a cursor the feed no longer holds changes nothing it
  shows (^21).
* `race`: a refresh and a load-more both in flight, answered in either order, end the same
  (^23). -/

@[expose] public section

namespace Sky
open CairnAtproto

/-- What identifies an item in the timeline: its post, and the repost that put it there. -/
abbrev Key := String × Option String

def reasonKey : Option Reason → Option String
  | none => none
  | some (.repost b _) => some b.did
  | some (.other t) => some ("$" ++ t)

def itemKey (i : FeedItem) : Key := (i.post.uri, reasonKey i.reason)

def keys (l : List FeedItem) : List Key := l.map itemKey

/-- The position of the first item with key `k`. -/
def indexOf (k : Key) : List FeedItem → Option Nat
  | [] => none
  | x :: xs => if itemKey x = k then some 0 else (indexOf k xs).map (· + 1)

/-- A head page against the feed: when the page holds the feed's first item, the items above
it (the new ones); otherwise `none`. -/
def newOnTop (items page : List FeedItem) : Option (List FeedItem) :=
  match items with
  | [] => none
  | f :: _ => (indexOf (itemKey f) page).map page.take

structure Feed where
  /-- Newest first. -/
  items : List FeedItem := []
  /-- The cursor that came with the last page: where the next page starts. -/
  cursor : Option String := none
  /-- The last page came without a cursor: there is nothing older. -/
  atEnd : Bool := false
  /-- The load-more in flight: its call id and the cursor it asked from. -/
  loadMore : Option (Nat × String) := none
  /-- The refresh in flight: its call id. -/
  refresh : Option Nat := none
deriving Repr, DecidableEq, Inhabited

namespace Feed

/-- What the feed shows: its items, cursor and end. -/
def content (f : Feed) : List FeedItem × Option String × Bool := (f.items, f.cursor, f.atEnd)

def appendPage (f : Feed) (p : FeedPage) : Feed :=
  { f with items := f.items ++ p.feed, cursor := p.cursor, atEnd := p.cursor.isNone }

/-- The feed replaced by a page: its items and cursor. A load-more in flight was for the old
feed. -/
def replaceBy (f : Feed) (p : FeedPage) : Feed :=
  { f with items := p.feed, cursor := p.cursor, atEnd := p.cursor.isNone, loadMore := none }

/-- A head page: the new items on top, or the feed replaced. -/
def headPage (f : Feed) (p : FeedPage) : Feed :=
  match newOnTop f.items p.feed with
  | some new => { f with items := new ++ f.items }
  | none => f.replaceBy p

/-- The answer to call `id`, if it is the load-more in flight: its page, or `none` if it
failed. The page is appended only if the feed still holds the cursor it asked from. -/
def gotLoadMore (f : Feed) (id : Nat) (page : Option FeedPage) : Feed :=
  match f.loadMore with
  | some (l, c) =>
    if l = id then
      match page with
      | some p => if f.cursor = some c then { f with loadMore := none }.appendPage p
                  else { f with loadMore := none }
      | none => { f with loadMore := none }
    else f
  | none => f

/-- The answer to call `id`, if it is the refresh in flight. -/
def gotRefresh (f : Feed) (id : Nat) (page : Option FeedPage) : Feed :=
  if f.refresh = some id then
    match page with
    | some p => { f with refresh := none }.headPage p
    | none => { f with refresh := none }
  else f

/-! ## A stale page -/

/-- **A load-more page for a cursor the feed no longer holds changes nothing it shows**; nor
does an answer to any call but the load-more in flight. -/
theorem gotLoadMore_stale (f : Feed) (id : Nat) (page : Option FeedPage)
    (h : ∀ c, f.loadMore = some (id, c) → f.cursor ≠ some c) :
    (f.gotLoadMore id page).content = f.content := by
  unfold gotLoadMore
  split
  · next l c e =>
    split
    · next hl =>
      subst hl
      have hc := h c e
      split
      · simp only [hc, ↓reduceIte]; rfl
      · rfl
    · rfl
  · rfl

/-! ## A refresh racing a load-more -/

theorem newOnTop_append (a : FeedItem) (as p page : List FeedItem) :
    newOnTop ((a :: as) ++ p) page = newOnTop (a :: as) page := rfl

/-- **A refresh and a load-more both in flight end the same whichever is answered first**: the
load-more's page (or failure) then the refresh's, or the other way round. So the result is that
of the two in sequence, the load-more first. -/
theorem race (f : Feed) (l r : Nat) (c : String) (pl pr : Option FeedPage)
    (hl : f.loadMore = some (l, c)) (hc : f.cursor = some c) (hne : f.items ≠ [])
    (hr : f.refresh = some r) :
    (f.gotLoadMore l pl).gotRefresh r pr = (f.gotRefresh r pr).gotLoadMore l pl := by
  obtain ⟨items, cursor, atEnd, lm, rf⟩ := f
  simp only at hl hc hr
  subst hl hc hr
  obtain _ | ⟨a, as⟩ := items
  · exact absurd rfl hne
  cases pl with
  | none =>
    cases pr with
    | none => simp [gotLoadMore, gotRefresh]
    | some q =>
      simp only [gotLoadMore, gotRefresh, headPage, replaceBy, ↓reduceIte]
      split <;> simp
  | some p =>
    cases pr with
    | none => simp [gotLoadMore, gotRefresh, appendPage]
    | some q =>
      simp only [gotLoadMore, gotRefresh, headPage, replaceBy, appendPage, ↓reduceIte]
      rw [newOnTop_append]
      split <;> simp

/-! ## Runs of the server's timeline -/

/-- `F` is the run of `T` (the server's timeline, newest first) that starts at position `i`. -/
def IsRun (T : List FeedItem) (i : Nat) (F : List FeedItem) : Prop :=
  (T.drop i).take F.length = F

theorem run_nil (T : List FeedItem) (i : Nat) : IsRun T i [] := by
  simp [IsRun]

/-- A head page is a run. -/
theorem run_head (T : List FeedItem) (k : Nat) : IsRun T 0 (T.take k) := by
  simp only [IsRun, List.drop_zero, List.length_take]
  grind

/-- New posts at the server's head leave a run a run, further down. -/
theorem run_grow {T : List FeedItem} {i : Nat} {F : List FeedItem} (N : List FeedItem)
    (h : IsRun T i F) : IsRun (N ++ T) (N.length + i) F := by
  simp only [IsRun] at *
  have e : List.drop (N.length + i) N = [] := List.drop_eq_nil_of_le (by omega)
  simpa [List.drop_append, e] using h

/-- A run followed by the run after it is a run. -/
theorem run_append {T : List FeedItem} {i : Nat} {F P : List FeedItem} (hF : IsRun T i F)
    (hP : IsRun T (i + F.length) P) : IsRun T i (F ++ P) := by
  simp only [IsRun, List.length_append] at *
  rw [List.take_add, hF, List.drop_drop, hP]

theorem run_sublist {T : List FeedItem} {i : Nat} {F : List FeedItem} (h : IsRun T i F) :
    F.Sublist T := by
  rw [← h]
  exact (List.take_sublist _ _).trans (List.drop_sublist _ _)

/-- A run of a timeline without duplicates has none. -/
theorem run_nodup {T : List FeedItem} {i : Nat} {F : List FeedItem} (hT : (keys T).Nodup)
    (h : IsRun T i F) : (keys F).Nodup :=
  hT.sublist ((run_sublist h).map _)

theorem indexOf_spec {k : Key} : ∀ {l : List FeedItem} {j : Nat}, indexOf k l = some j →
    ∃ hj : j < l.length, itemKey l[j] = k
  | [], _, h => by simp [indexOf] at h
  | x :: xs, j, h => by
    simp only [indexOf] at h
    split at h
    · next e =>
      cases h
      exact ⟨by simp, e⟩
    · obtain ⟨j', hj', rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hlt, e⟩ := indexOf_spec hj'
      exact ⟨by simp; omega, by simpa using e⟩

theorem run_getElem {T : List FeedItem} {i : Nat} {a : FeedItem} {as : List FeedItem}
    (h : IsRun T i (a :: as)) : ∃ hi : i < T.length, T[i] = a := by
  simp only [IsRun] at h
  have hl : 0 < ((T.drop i).take (a :: as).length).length := by rw [h]; simp
  simp only [List.length_take, List.length_drop, List.length_cons] at hl
  refine ⟨by omega, ?_⟩
  have e := congrArg (·[0]?) h
  simp only [List.getElem?_take, List.getElem?_drop, List.length_cons] at e
  simp only [Nat.zero_lt_succ, ↓reduceIte, Nat.add_zero, List.getElem?_cons_zero] at e
  rw [List.getElem?_eq_getElem (by omega)] at e
  exact Option.some.inj e

/-- **A head page holding the feed's first item puts exactly the posts above it on top**: the
result is the timeline from its head to the feed's end. -/
theorem newOnTop_run {T : List FeedItem} {i k : Nat} {F new : List FeedItem}
    (hT : (keys T).Nodup) (hF : IsRun T i F) (h : newOnTop F (T.take k) = some new) :
    new ++ F = T.take (i + F.length) := by
  obtain _ | ⟨a, as⟩ := F
  · simp [newOnTop] at h
  simp only [newOnTop] at h
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hjl, ej⟩ := indexOf_spec hj
  obtain ⟨hil, ei⟩ := run_getElem hF
  simp only [List.length_take] at hjl
  have hjT : j < T.length := by omega
  simp only [List.getElem_take] at ej
  have hji : j = i := by
    have hk : (keys T)[j]'(by simp [keys]; omega) = (keys T)[i]'(by simp [keys]; omega) := by
      simp only [keys, List.getElem_map, ej, ei]
    exact (List.Nodup.getElem_inj hT).mp hk
  subst hji
  rw [List.take_take, Nat.min_eq_left (by omega), List.take_add]
  congr 1
  exact hF.symm

/-- A head page that holds the feed's first item: exactly when that item is within a page of
the head. -/
theorem newOnTop_isSome {T : List FeedItem} {i k : Nat} {a : FeedItem} {as : List FeedItem}
    (hF : IsRun T i (a :: as)) (hik : i < k) :
    (newOnTop (a :: as) (T.take k)).isSome := by
  obtain ⟨hil, ei⟩ := run_getElem hF
  simp only [newOnTop, Option.isSome_map]
  cases e : indexOf (itemKey a) (T.take k) with
  | some j => rfl
  | none =>
    exfalso
    have : ∀ (l : List FeedItem) (n : Nat) (hn : n < l.length), indexOf (itemKey l[n]) l ≠ none := by
      intro l
      induction l with
      | nil => intro n hn; simp at hn
      | cons x xs ih =>
        intro n hn
        simp only [indexOf]
        split
        · simp
        · cases n with
          | zero => simp_all
          | succ n =>
            simp only [List.getElem_cons_succ, ne_eq, Option.map_eq_none_iff]
            exact ih n (by simp at hn; omega)
    have hn : i < (T.take k).length := by simp; omega
    apply this (T.take k) i hn
    rw [List.getElem_take, ei]
    exact e

/-- **A head page leaves the feed a run of the timeline**, from the head: the new items on top
of the old run, or the page itself. -/
theorem headPage_run {T : List FeedItem} {i k : Nat} (hT : (keys T).Nodup) (f : Feed)
    (hF : IsRun T i f.items) (cursor : Option String) :
    IsRun T 0 (f.headPage { feed := T.take k, cursor }).items := by
  unfold headPage
  split
  · next new h =>
    show IsRun T 0 (new ++ f.items)
    rw [newOnTop_run hT hF h]
    exact run_head T _
  · exact run_head T k

/-- What ^20 claims of the merges, for every server timeline without duplicates: a feed that
is a run of it stays a run when the page after it is appended or a head page arrives, also after
new posts arrive at the head, and a run has no duplicates. -/
def Contiguous : Prop :=
  ∀ T : List FeedItem, (keys T).Nodup → ∀ (f : Feed) (i : Nat), IsRun T i f.items →
    (keys f.items).Nodup ∧
    (∀ p : FeedPage, IsRun T (i + f.items.length) p.feed → IsRun T i (f.appendPage p).items) ∧
    (∀ k cursor, IsRun T 0 (f.headPage { feed := T.take k, cursor }).items) ∧
    (∀ N : List FeedItem, IsRun (N ++ T) (N.length + i) f.items)

theorem contiguous : Contiguous := fun _T hT f _i hF =>
  ⟨run_nodup hT hF, fun _p hp => run_append hF hp, fun _k c => headPage_run hT f hF c,
   fun N => run_grow N hF⟩

end Feed

end Sky
