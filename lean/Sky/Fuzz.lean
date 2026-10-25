import Sky.Claims
import Cairn.Fuzz.Rng
import Cairn.Fuzz.Text

/-! # Sky on `cairn fuzz`'s host

`cairn fuzz` types in Sky's fields, presses its buttons (sign in, load more, refresh, sign out, the
app-password link) and plays the host:
replies late, in any order, to cancelled and stray ids, failing (Cairn's docs/fuzz.md). The
server is cairn_atproto's fake PDS (`CairnAtproto.Fake`, cairn#208): a timeline that only grows at
its head, `getTimeline` paged by an opaque cursor, access tokens that expire, refreshes refused,
a missing Keychain item by the session's phase, and faults. No network, no real account. The
service default Sky reads at launch (`readDefault`) is the fake's, or none; the saved account
(`readFile`) is the fake's identifier, or none.

Cairn 0.2.5's hook keeps no state between replies, so each reply is what the fake answers in a
state drawn at random that fits request `id`: the timeline as it stands then (`lengthAt`),
growing as ids grow, and post `k` (from the oldest) the same whenever it is answered.

The fuzz types into the sign-in form (`edits`): mostly the fake's identifier, app password and
service, sometimes a wrong password, the password appended to what is there (after the text
the fuzzer plants in the secure field, which must never reach an effect unredacted), an empty
service, or Cairn's random editing script.

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

/-- The account Sky saved, or none. -/
def readAccount : Gen Reply := do
  if ← Gen.chance 3 4 then return .bytes (accountJson cfg.service cfg.identifier)
  return .failed .notFound "No such file."

/-- What a person types: the fake's test identifier, app password and service (generated from
the seed; not credentials), mostly. -/
def typeIdentifier : Gen (List TextOp) :=
  Gen.weighted [(6, pure [.selectAll, .insert cfg.identifier]), (1, pure [.selectAll, .insert ("@" ++ cfg.identifier)]),
                (1, Cairn.Fuzz.Text.script)]

def typePassword : Gen (List TextOp) :=
  Gen.weighted [(12, pure [.selectAll, .insert cfg.password]), (2, pure [.insert cfg.password]),
                (1, pure [.selectAll, .insert "not-the-password"]), (1, Cairn.Fuzz.Text.script)]

def typeService : Gen (List TextOp) :=
  Gen.weighted [(6, pure [.selectAll, .insert cfg.service]), (1, pure [.selectAll, .deleteBackward]),
                (1, Cairn.Fuzz.Text.script)]

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
    | .readFile _ => some FakeCheck.readAccount
    | .writeFile .. | .deleteFile _ | .openItem _ | .forgetSecret _ => some do
      if ← Gen.chance 1 10 then return .failed .other "The fuzz's host failed it."
      return .done
    | _ => some do
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
  edits := fun _ id => match id with
    | 6 => some FakeCheck.typeIdentifier
    | 7 => some FakeCheck.typePassword
    | 8 => some FakeCheck.typeService
    | _ => none
  outstanding := [(24, fun s ids => ids.mergeSort == s.waiting.mergeSort)]
  drained := [(24, fun s => s.feed.loadMore.isNone && s.feed.refresh.isNone &&
    s.session.inflight.isEmpty && s.session.held.isEmpty && s.own.isEmpty && s.forgetting.isEmpty)]

end Sky
