import Sky.Claims
import Cairn.Fuzz.Rng

/-! # Sky on `cairn fuzz`'s host

`cairn fuzz` presses Sky's buttons (sign in, load more, refresh, sign out) and plays the host:
replies late, in any order, to cancelled and stray ids, failing (Cairn's docs/fuzz.md). The
server is cairn_atproto's fake PDS (`CairnAtproto.Fake`, cairn#208): a timeline that only grows at
its head, `getTimeline` paged by an opaque cursor, access tokens that expire, refreshes refused,
a missing Keychain item by the session's phase, and faults. No network, no real account. The
saved service Sky reads at launch (`readDefault`) is the fake's, or none.

Cairn 0.2.5's hook keeps no state between replies, so each reply is what the fake answers in a
state drawn at random that fits request `id`: the timeline as it stands then (`lengthAt`),
growing as ids grow, and post `k` (from the oldest) the same whenever it is answered.

Sky's sign-in form is empty until #210 adds its fields, so the fuzz plays a person who typed the
fake's identifier and app password three times in four (`typed`): it hands the fake the
`createSession` body with them. The fourth time the fake refuses the sign-in (401).

Every claim is checked after every step: ^22, ^24, ^25 are decidable and checked as states;
^20–^23 also as relations on the feed each step reaches, against the fake's timeline; ^24 against
the runtime's ids (`outstanding`) and once everything is answered (`drained`). -/

namespace Sky.FakeCheck

open Cairn Cairn.Fuzz CairnJson CairnAtproto CairnAtproto.Fake

def cfg : Config := {}

/-- The timeline's length when request `id` is answered (cairn_atproto's README). -/
def lengthAt (id : Nat) : Nat := cfg.base + arrivedBefore cfg (id + 1)

/-- The saved service, or none. -/
def readService : Gen Reply := do
  if ← Gen.chance 3 4 then return .bytes cfg.service.toUTF8
  return .failed .notFound "No value."

/-- A `createSession` as if the person typed the fake's test identifier and app password
(generated from the seed; not a credential), three times in four. -/
def typed : Request → Gen Request
  | r@(.http m url hs _ t) => do
    if (url.splitOn nsidCreateSession).length > 1 && (← Gen.chance 3 4) then
      return .http m url hs (createSession cfg.service cfg.identifier cfg.password).body.toUTF8 t
    return r
  | r => pure r

/-- The index `k` of a post of the fake's timeline, from its URI's record key (`rkey`). -/
def indexOf (i : FeedItem) : Option Nat :=
  match (i.post.uri.splitOn "/").getLast? with
  | some t => if t.startsWith "3fk" then (t.drop 3).toString.toNat? else none
  | none => none

def indices (f : Feed) : Option (List Nat) := f.items.mapM indexOf

/-- A run of the timeline, in its order (newest first): consecutive indices, descending. -/
def isRun : List Nat → Bool
  | a :: b :: rest => a == b + 1 && isRun (b :: rest)
  | _ => true

/-- ^20: the feed is a contiguous run of the fake's timeline, each post the timeline's own. -/
def contiguous (f : Feed) : Bool :=
  match indices f with
  | some ns => isRun ns && (f.items.zip ns).all fun (i, k) => i.post.uri == postUri cfg k
  | none => false

/-- ^22, fuzzed: the cursor is the one that came with the last page: the fake's cursor of the
oldest post, or none (and the end) at post 0. -/
def cursorOfLast (f : Feed) : Bool :=
  match f.items.getLast? with
  | none => true
  | some i => match indexOf i with
    | some 0 => f.cursor.isNone && f.atEnd
    | some k => f.cursor == some (cursorOf cfg k) && !f.atEnd
    | none => false

def pageAt (len : Nat) (cur : Option String) : FeedPage :=
  page cfg len pageSize (cur.bind (cursorPos cfg len))

/-- ^21: a load-more page for a cursor the feed doesn't hold changes nothing it shows. -/
def stale (f : Feed) (len : Nat) : Bool :=
  match f.loadMore with
  | some (l, c) =>
    let g := { f with cursor := some (c ++ "0") }
    [some (pageAt len (some c)), some (pageAt len none), none].all fun p =>
      (g.gotLoadMore l p).content == g.content
  | none => true

/-- ^23: a refresh racing a load-more, either order of answers (or failures): the same feed. -/
def race (f : Feed) (len : Nat) : Bool :=
  match f.loadMore, f.refresh with
  | some (l, c), some r =>
    let pls := [some (pageAt len (some c)), none]
    let prs := [some (pageAt len none), some (pageAt (len + 100) none), none]
    pls.all fun pl => prs.all fun pr =>
      (f.gotLoadMore l pl).gotRefresh r pr == (f.gotRefresh r pr).gotLoadMore l pl
  | _, _ => true

/-- The timeline as far as the requests the session has sent. -/
def lengthOf (s : State) : Nat := lengthAt (sessionId s.session.next + 2)

end Sky.FakeCheck

namespace Sky

open Cairn Cairn.Fuzz

def fuzz : Cairn.Fuzz.Custom State where
  replies := fun s id r => match r with
    | .readDefault _ "service" => some FakeCheck.readService
    | _ => some do
      let r ← FakeCheck.typed r
      match CairnAtproto.Fake.replies FakeCheck.cfg { phase := fun s => some s.session.phase } s id r with
      | some g => g
      | none => return .failed .other "not the fake's"
  relations :=
    [ (20, fun t => FakeCheck.contiguous t.after.feed),
      (21, fun t => FakeCheck.stale t.after.feed (FakeCheck.lengthOf t.after)),
      (22, fun t => FakeCheck.cursorOfLast t.after.feed),
      (23, fun t => FakeCheck.race t.after.feed (FakeCheck.lengthOf t.after)),
      (24, fun t => decide (Inv t.after)),
      (25, fun t => decide (SignedOutEmpty t.after)) ]
  outstanding := [(24, fun s ids => ids.mergeSort == s.waiting.mergeSort)]
  drained := [(24, fun s => s.feed.loadMore.isNone && s.feed.refresh.isNone &&
    s.session.inflight.isEmpty && s.session.held.isEmpty && !s.booting)]

end Sky
