module

public import CairnAtproto.Paged
public import CairnAtproto.Proofs.Paged
public import CairnAtproto.Datetime
public import Cairn.Optimistic

/-! # Notifications, headless (cairn#253)

What Sky holds of the account's notifications and how it shows them, without the screen:

* **The list** is cairn_atproto's paged list (`Paged Notification`, cairn#250): load more at
  the end, refresh on top, and their race, with the proofs made there (`cairn_atproto^26`–`^29`).
* **Groups** (`groupAll`): likes of the same post that are adjacent in the list form one group,
  as do reposts of the same post and adjacent follows; every other reason (mention, reply,
  quote, anything newer) is a row of its own. Notifications from muted accounts are left out
  before grouping (`shownGroups`). Proved: the groups partition what is shown, in order
  (`flatten_groupAll`); each group's members share its reason and subject, and only likes,
  reposts and follows ever have more than one (`groupAll_ok`); two groups next to each other
  could not have been one (`groupAll_maximal`); no member is muted (`shownGroups_unmuted`).
* **Seen** (`Seen`): the newest notification that has appeared on screen (`mark`, in ms) is
  marked seen through a one-key `Cairn.Optimistic` table (its one `Entry`, stepped with
  `Entry.step`), so what is shown as seen moves at once and goes back if `updateSeen` is
  refused. Proved (`SeenOk`, kept by every input): every `updateSeen` Sky sends is at least the
  one before it and at most `mark` (`Seen.sendOk`).
* **Unread** (`unreadShown`): the count the last poll gave, less the notifications Sky holds
  that the shown seen marker has since passed. So it drops to 0 at once when the list is read,
  and comes back if the call is refused. -/

@[expose] public section

namespace Sky
open CairnAtproto Cairn.Optimistic

/-! ## Groups -/

/-- Whether a reason's notifications group with their neighbours: likes, reposts, follows. -/
def groupable : NotificationReason → Bool
  | .like | .repost | .follow => true
  | _ => false

/-- One row of the list: one or more notifications, newest first. -/
structure Group where
  reason : NotificationReason
  /-- The liked or reposted post's URI; none for a follow. -/
  subject : Option String
  members : List Notification
deriving Repr, DecidableEq, Inhabited

def Group.one (n : Notification) : Group := ⟨n.reason, n.reasonSubject, [n]⟩

/-- `n` joins group `g` just above it: a like, repost or follow, of the same reason and subject. -/
def joins (n : Notification) (g : Group) : Bool :=
  groupable n.reason && decide (n.reason = g.reason) && decide (n.reasonSubject = g.subject)

/-- The rows of a list of notifications, newest first: each maximal run of adjacent likes of the
same post (reposts of the same post, follows) is one group; every other notification is a
group of its own. -/
def groupAll : List Notification → List Group
  | [] => []
  | n :: ns =>
    match groupAll ns with
    | g :: gs => if joins n g then { g with members := n :: g.members } :: gs
                 else Group.one n :: g :: gs
    | [] => [Group.one n]

/-- What a group needs: members, all of its reason and subject, and more than one only for a
like, repost or follow. -/
def Group.Ok (g : Group) : Prop :=
  g.members ≠ [] ∧ (∀ n ∈ g.members, n.reason = g.reason ∧ n.reasonSubject = g.subject) ∧
    (1 < g.members.length → groupable g.reason = true)

/-- Two groups, one above the other, that could have been one. -/
def mergeable (a b : Group) : Prop :=
  groupable a.reason = true ∧ a.reason = b.reason ∧ a.subject = b.subject

/-- **The groups partition the list, in order.** -/
theorem flatten_groupAll : ∀ l : List Notification, ((groupAll l).map (·.members)).flatten = l
  | [] => rfl
  | n :: ns => by
    have ih := flatten_groupAll ns
    simp only [groupAll]
    split
    · next g gs e =>
      rw [e] at ih
      split
      · simp only [List.map_cons, List.flatten_cons, List.cons_append] at ih ⊢; rw [ih]
      · simp only [Group.one, List.map_cons, List.flatten_cons, List.singleton_append] at ih ⊢
        rw [ih]
    · next e => rw [e] at ih; simp only [Group.one, List.map_cons, List.map_nil,
        List.flatten_cons, List.flatten_nil, List.append_nil]; simp at ih; rw [ih]

theorem one_ok (n : Notification) : (Group.one n).Ok := by
  refine ⟨by simp [Group.one], ?_, ?_⟩
  · intro x hx; simp only [Group.one, List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx
    exact ⟨rfl, rfl⟩
  · simp [Group.one]

/-- **Every group is a group**: members of one reason and subject, several only for likes,
reposts and follows. -/
theorem groupAll_ok : ∀ (l : List Notification), ∀ g ∈ groupAll l, g.Ok
  | [] => by simp [groupAll]
  | n :: ns => by
    have ih := groupAll_ok ns
    simp only [groupAll]
    split
    · next g gs e =>
      rw [e] at ih
      have hg := ih g (List.mem_cons_self ..)
      have hgs : ∀ x ∈ gs, x.Ok := fun x hx => ih x (List.mem_cons_of_mem _ hx)
      split
      · next hj =>
        simp only [joins, Bool.and_eq_true, decide_eq_true_eq] at hj
        obtain ⟨⟨hgr, hr⟩, hs⟩ := hj
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · refine ⟨by simp, ?_, fun _ => hr ▸ hgr⟩
          intro m hm
          simp only [List.mem_cons] at hm
          rcases hm with rfl | hm
          · exact ⟨hr, hs⟩
          · exact hg.2.1 m hm
        · exact hgs x hx
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · exact one_ok n
        · exact hg
        · exact hgs x hx
    · intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact one_ok n

theorem groupAll_head : ∀ (n : Notification) (ns : List Notification),
    ∃ g gs, groupAll (n :: ns) = g :: gs ∧ g.reason = n.reason ∧ g.subject = n.reasonSubject := by
  intro n ns
  simp only [groupAll]
  split
  · next g gs _ =>
    split
    · next hj =>
      simp only [joins, Bool.and_eq_true, decide_eq_true_eq] at hj
      exact ⟨_, _, rfl, hj.1.2.symm, hj.2.symm⟩
    · exact ⟨_, _, rfl, rfl, rfl⟩
  · exact ⟨_, _, rfl, rfl, rfl⟩

/-- No two groups next to each other could have been one. -/
def Apart : List Group → Prop
  | a :: b :: rest => ¬ mergeable a b ∧ Apart (b :: rest)
  | _ => True

/-- **Groups are maximal**: no two groups next to each other could have been one. -/
theorem groupAll_maximal : ∀ l : List Notification,
    Apart (groupAll l)
  | [] => trivial
  | n :: ns => by
    have ih := groupAll_maximal ns
    simp only [groupAll]
    split
    · next g gs e =>
      rw [e] at ih
      split
      · next hj =>
        simp only [joins, Bool.and_eq_true, decide_eq_true_eq] at hj
        cases gs with
        | nil => trivial
        | cons h hs => exact ih
      · next hj =>
        refine ⟨?_, ih⟩
        intro ⟨h1, h2, h3⟩
        apply hj
        simp only [Group.one] at h1 h2 h3
        simp only [joins, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨h1, h2⟩, h3⟩
    · trivial

/-- The rows shown: the notifications from accounts not muted (`muted`, by DID), grouped. -/
def shownGroups (muted : String → Bool) (l : List Notification) : List Group :=
  groupAll (l.filter fun n => !muted n.author.did)

/-- **No row is from a muted account.** -/
theorem shownGroups_unmuted (muted : String → Bool) (l : List Notification) :
    ∀ g ∈ shownGroups muted l, ∀ n ∈ g.members, muted n.author.did = false := by
  intro g hg n hn
  have : n ∈ ((shownGroups muted l).map (·.members)).flatten :=
    List.mem_flatten.mpr ⟨g.members, List.mem_map.mpr ⟨g, hg, rfl⟩, hn⟩
  rw [shownGroups, flatten_groupAll] at this
  simpa using (List.mem_filter.mp this).2

/-! ## Words -/

/-- An account's name as a row says it: its display name, or its handle. -/
def nameOf (p : Profile) : String :=
  match p.displayName with
  | some d => if d.trimAscii.isEmpty then "@" ++ p.handle else d
  | none => "@" ++ p.handle

/-- The accounts of a group, each once, newest first. -/
def Group.authors (g : Group) : List Profile :=
  (g.members.map (·.author)).foldl (fun acc p => if acc.any (·.did == p.did) then acc else acc ++ [p]) []

/-- "Alice", "Alice and Bob", "Alice, Bob and Carol", "Alice, Bob and 3 others". -/
def namesOf : List Profile → String
  | [] => "Someone"
  | [a] => nameOf a
  | [a, b] => nameOf a ++ " and " ++ nameOf b
  | [a, b, c] => nameOf a ++ ", " ++ nameOf b ++ " and " ++ nameOf c
  | a :: b :: rest => nameOf a ++ ", " ++ nameOf b ++ s!" and {rest.length} others"

/-- What a group did. -/
def reasonWords : NotificationReason → String
  | .like => "liked your post"
  | .repost => "reposted your post"
  | .follow => "followed you"
  | .mention => "mentioned you"
  | .reply => "replied to you"
  | .quote => "quoted your post"
  | .other r => s!"({r})"

/-- A row's line: "Alice, Bob and 3 others liked your post". -/
def Group.words (g : Group) : String := namesOf g.authors ++ " " ++ reasonWords g.reason

/-! ## Times -/

/-- A notification's `indexedAt`, in milliseconds since the epoch (0 if it can't be read). -/
def msOf (t : String) : Nat := ((parseDatetime t).getD 0).toNat

def noteMs (n : Notification) : Nat := msOf n.indexedAt

/-- The newest `indexedAt` among some notifications. -/
def newestMs (l : List Notification) : Nat := l.foldl (fun m n => max m (noteMs n)) 0

/-! ## Seen -/

/-- The seen marker's values are milliseconds; two are the same when equal. -/
def sameMs : Nat → Nat → Bool := fun a b => a == b

theorem sameMs_same : Same sameMs := Same.beq

/-- The seen marker: the newest notification that has appeared (`mark`), the one-key optimistic
entry for the account's `seenAt`, and the last value Sky sent with `updateSeen` (`sent`). -/
structure Seen where
  /-- The newest `indexedAt` (ms) of the notifications that have appeared on screen. -/
  mark : Nat := 0
  /-- The table's one key. -/
  entry : Entry Nat := Entry.fresh 0
  /-- The last `seenAt` Sky sent (0: none yet). -/
  sent : Nat := 0
deriving Repr, DecidableEq, Inhabited

/-- **What `SeenOk` keeps**: the last value sent is at most the mark; a write in flight or in
doubt is the last one sent, and is at most what is shown, which is at most the mark. -/
def SeenOk (s : Seen) : Prop :=
  s.sent ≤ s.mark ∧
    match s.entry.phase.pending with
    | some w => w = s.sent ∧ w ≤ s.entry.want ∧ s.entry.want ≤ s.mark
    | none => True

instance (s : Seen) : Decidable (SeenOk s) := by unfold SeenOk; split <;> infer_instance

/-- The writes among an entry's actions. -/
def writesOf (as : List (Act Nat)) : List Nat := as.filterMap fun | .write _ v => some v | _ => none

/-- The entry's step at the seen key: what it asks to write is sent, and the last one recorded. -/
def Seen.feed (s : Seen) (ev : Ev Nat) : Seen × List (Act Nat) :=
  let r := s.entry.step sameMs ev
  ({ s with entry := r.1, sent := (writesOf r.2).getLast?.getD s.sent }, r.2)

/-- A notification appeared at `ms`: the mark moves up to it. -/
def Seen.appear (s : Seen) (ms : Nat) : Seen := { s with mark := max s.mark ms }

/-- What is shown as seen. -/
def Seen.shown (s : Seen) : Nat := s.entry.want

/-- With the list on screen: mark seen up to `mark`, if that is past what is shown. -/
def Seen.markSeen (s : Seen) : Seen × List (Act Nat) :=
  if s.shown < s.mark then s.feed (.set fun _ => s.mark) else (s, [])

/-- Every write the step asks for is at least `lo` and at most `hi`, in order and not
decreasing. -/
def SendsOk (lo hi : Nat) (vs : List Nat) : Prop :=
  vs.Pairwise (· ≤ ·) ∧ ∀ v ∈ vs, lo ≤ v ∧ v ≤ hi

theorem seenOk_init : SeenOk {} := by
  exact ⟨Nat.le_refl _, trivial⟩

/-- **`Seen.feed` keeps `SeenOk`, and every write it asks for is between the last one sent and
the mark**, for any input but a `set` (whose value is the mark, `markSeen`). -/
theorem feed_ok (s : Seen) (h : SeenOk s) (ev : Ev Nat)
    (hset : ∀ f, ev = .set f → ∀ x, f x = s.mark) :
    SeenOk (s.feed ev).1 ∧ SendsOk s.sent s.mark (writesOf (s.feed ev).2) := by
  obtain ⟨mark, ⟨server, want, written, phase, seq, backoff⟩, sent⟩ := s
  obtain ⟨hsm, hp⟩ := h
  simp only at hsm hp hset ⊢
  cases ev <;> cases phase <;>
    simp only [Seen.feed, Entry.step, Entry.send, Entry.ask, Entry.settle, Entry.rollback,
      Phase.isOpen, Phase.isIdle, Phase.pending] at hp ⊢ <;>
    (repeat' split) <;> simp_all [SeenOk, SendsOk, writesOf, Phase.pending, sameMs]
  all_goals (repeat' split) <;> (try simp_all) <;> (try omega)

/-- `markSeen` keeps `SeenOk`, and the write it asks for (if any) is the mark, at least the last
one sent. -/
theorem markSeen_ok (s : Seen) (h : SeenOk s) :
    SeenOk s.markSeen.1 ∧ SendsOk s.sent s.mark (writesOf s.markSeen.2) := by
  unfold Seen.markSeen
  split
  · exact feed_ok s h _ (fun f e x => by cases e; rfl)
  · exact ⟨h, by simp [SendsOk, writesOf]⟩

/-- A notification appearing keeps `SeenOk`: the mark only moves up. -/
theorem appear_ok (s : Seen) (h : SeenOk s) (ms : Nat) : SeenOk (s.appear ms) := by
  obtain ⟨mark, entry, sent⟩ := s
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simp only [Seen.appear] at h1 ⊢; omega, ?_⟩
  simp only [Seen.appear] at h2 ⊢
  revert h2
  cases entry.phase.pending <;> simp only [imp_self, and_imp] <;> omega

/-- Signed out: nothing outstanding for the key; the mark and the last value sent are kept for
the account. -/
def Seen.reset (s : Seen) : Seen := { s with entry := Entry.fresh 0 }

theorem reset_ok (s : Seen) (h : SeenOk s) : SeenOk s.reset := ⟨h.1, trivial⟩

/-! ### The seen marker, kept `SeenOk` by construction -/

/-- What the seen key hears besides a set: a call's answer, the retry timer, a view. -/
inductive SeenEv where
  | acked (n : Nat)
  | refused (n : Nat) (why : String)
  | lost (n : Nat)
  | read (n : Nat) (v : Nat)
  | readFailed (n : Nat)
  | retry
  | seen (v : Nat)
deriving Repr, DecidableEq, Inhabited

def SeenEv.ev : SeenEv → Ev Nat
  | .acked n => .acked n
  | .refused n w => .refused n w
  | .lost n => .lost n
  | .read n v => .read n v
  | .readFailed n => .readFailed n
  | .retry => .retry
  | .seen v => .seen v

/-- The seen marker with `SeenOk` attached: every way Sky changes it keeps it. -/
abbrev SeenKept := { s : Seen // SeenOk s }

instance : Inhabited SeenKept := ⟨⟨{}, seenOk_init⟩⟩

namespace SeenKept

def init : SeenKept := ⟨{}, seenOk_init⟩

/-- An answer, the retry timer or a view, at the seen key. -/
def hear (s : SeenKept) (e : SeenEv) : SeenKept × List (Act Nat) :=
  (⟨(s.1.feed e.ev).1, (feed_ok s.1 s.2 e.ev (fun f h => by cases e <;> cases h)).1⟩, (s.1.feed e.ev).2)

/-- With the list on screen: mark seen up to the mark. -/
def markSeen (s : SeenKept) : SeenKept × List (Act Nat) :=
  (⟨s.1.markSeen.1, (markSeen_ok s.1 s.2).1⟩, s.1.markSeen.2)

def appear (s : SeenKept) (ms : Nat) : SeenKept := ⟨s.1.appear ms, appear_ok s.1 s.2 ms⟩

def reset (s : SeenKept) : SeenKept := ⟨s.1.reset, reset_ok s.1 s.2⟩

def shown (s : SeenKept) : Nat := s.1.shown

end SeenKept

/-- **What is claimed of the seen marker** (every `updateSeen` Sky sends is at least the one
before it and at most the newest notification that has appeared): whatever the key hears, and
when Sky marks the list seen, the writes asked for are in order, between the last one sent and
the mark, and `SeenOk` holds after. -/
def SeenMonotone : Prop :=
  ∀ s : Seen, SeenOk s →
    (∀ e : SeenEv, SeenOk (s.feed e.ev).1 ∧ SendsOk s.sent s.mark (writesOf (s.feed e.ev).2)) ∧
    (SeenOk s.markSeen.1 ∧ SendsOk s.sent s.mark (writesOf s.markSeen.2)) ∧
    (∀ ms, SeenOk (s.appear ms) ∧ s.mark ≤ (s.appear ms).mark)

theorem seenMonotone : SeenMonotone := fun s h =>
  ⟨fun e => feed_ok s h e.ev (fun f hf => by cases e <;> cases hf), markSeen_ok s h,
   fun ms => ⟨appear_ok s h ms, Nat.le_max_left _ _⟩⟩

/-! ## Notes: the list, the seen marker, the unread count -/

/-- What a seen call of Sky's is: write `seq` of the key, or read `seq`. -/
inductive SeenCall where
  | write (seq : Nat)
  | read (seq : Nat)
deriving Repr, DecidableEq, Inhabited

structure Notes where
  /-- The notifications, newest first, paged. -/
  list : Paged Notification := {}
  /-- The seen marker. -/
  seen : SeenKept := SeenKept.init
  /-- The account the seen marker is for. -/
  did : String := ""
  /-- The seen marker's calls in flight, by call id. -/
  seenCalls : List (Nat × SeenCall) := []
  /-- The unread poll in flight: its call id. -/
  poll : Option Nat := none
  /-- What was shown as seen when the poll in flight was sent. -/
  pollBase : Nat := 0
  /-- The last poll's count, and what was shown as seen when it was sent. -/
  unread : Nat := 0
  unreadBase : Nat := 0
  /-- The last load-more failed: the end row offers Retry. -/
  moreFailed : Bool := false
  /-- The seen key's writes and reads asked for, not yet sent (sent at the end of the step). -/
  todo : List (Act Nat) := []
  /-- A poll is due: after a refresh, at sign-in, and on the minute's tick. -/
  pollDue : Bool := false
  /-- The list's generation: a new list (the first notifications, a replaced list, another
  account) is a new virtual list, at the top. -/
  gen : Nat := 0
deriving Repr, DecidableEq, Inhabited

/-- **The unread count shown**: the last poll's, less the notifications Sky holds that what is
shown as seen has passed since that poll was sent. -/
def Notes.unreadShown (n : Notes) : Nat :=
  n.unread - (n.list.items.filter fun x => n.unreadBase < noteMs x && noteMs x ≤ n.seen.shown).length

/-- The Dock badge: the unread count shown, or none at 0. -/
def Notes.badge (n : Notes) : Option String :=
  if n.unreadShown = 0 then none else some (toString n.unreadShown)

/-- The ids of the calls the notes wait on. -/
def Notes.calls (n : Notes) : List Nat :=
  n.list.inFlight ++ n.poll.toList ++ n.seenCalls.map (·.1)

/-- What the rows of the list are keyed by: the group's oldest notification (new ones join a
group at its top), hashed, never `0` (the end row's key). -/
def Group.key (g : Group) : Nat :=
  match g.members.getLast? with
  | some n => (hash n.uri).toNat % 1000000000 + 1
  | none => 1

/-- A rollback, in words. -/
def rollbackWords : Cairn.Optimistic.Reason → String
  | .refused why => why
  | .notApplied => "it didn't go through"

end Sky
