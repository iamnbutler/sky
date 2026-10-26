import Sky.Claims
import Cairn.Fuzz.Rng
import Cairn.Fuzz.Text

/-! # Sky on `cairn fuzz`'s host

`cairn fuzz` types in Sky's fields, presses its buttons (sign in, load more, refresh, sign out,
the app-password link, like, repost, follow, mute, the notifications) and plays the host:
replies late, in any order, to cancelled and stray ids, failing (Cairn's docs/fuzz.md).

The server is cairn_atproto's whole fake PDS (`Fake.server`, cairn#260): every XRPC request
reaches it, and it holds the tester's repo, mutes and seen time through the sequence. Requests
fail before it acts or are lost after it (retransmit off), and between steps posts arrive, other
accounts like, repost and follow (so notifications arrive), the AppView catches up and the
access token expires. Half the sequences start from the seed the fuzz types (`cfg`), saved
signed in half of those; the rest from a random seed, saved signed in (`worldGen`). Often other
accounts have acted a few pages' worth first, so the notifications load more and group, and a
load-more fails one time in four before it reaches the server, so Retry gets pressed. The rest
of the host (the saved service and account, files, images) is `replies`, from the seed's fake.
The fuzz types into the sign-in form (`edits`): mostly the fake's identifier, app password and
service, sometimes a wrong password, the password appended to what is there (after the text
the fuzzer plants in the secure field, which must never reach an effect unredacted), an empty
service, or Cairn's random editing script.

Every claim is checked after every step: ^24, ^25, ^43 and ^69 are decidable and checked as
states; ^24 against the runtime's ids (`outstanding`) and once everything is answered
(`drained`), and Sky's wiring of the feed against the server's timeline (`feedOk`). ^41 against
the server (`actsHeld`, `countsHeld`): every key Sky wrote and holds settled shows what the
server holds, and a settled like count is the server's whenever no one else acted since the
view. The notifications against the server too: a contiguous run of its notifications (^67),
and its `seenAt` never past the newest notification that has been on screen (^70); the groups
(^68, ^69) and the poll (^71) as states. -/

namespace Sky.FakeCheck

open Cairn Cairn.Fuzz CairnJson CairnAtproto CairnAtproto.Fake

def cfg : Config := {}

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

/-- Strictly newest first. -/
def isDesc : List Nat → Bool
  | a :: b :: rest => b < a && isDesc (b :: rest)
  | _ => true

/-- cairn_atproto^26 through Sky: the feed is a run of the fake's timeline, newest first, each
post the timeline's own. The fake's timeline leaves out muted accounts' posts as they are muted,
so a run of it is the posts it showed, in order: not always consecutive. -/
def contiguous (c : Config) (f : Feed) : Bool :=
  match indices f with
  | some ns => isDesc ns && (f.items.zip ns).all fun (i, k) => i.post.uri == postUri c k
  | none => false

/-- cairn_atproto^28 through Sky: the cursor is the one that came with the last page: the fake's cursor of the
oldest post, or none (and the end) at post 0. -/
def cursorOfLast (c : Config) (f : Feed) : Bool :=
  match f.items.getLast? with
  | none => true
  | some i => match indexOf i with
    | some 0 => f.cursor.isNone && f.atEnd
    | some k => (f.cursor == some (cursorOf c k) && !f.atEnd) || (f.cursor.isNone && f.atEnd)
    | none => false

def pageAt (c : Config) (len : Nat) (cur : Option String) : Page FeedItem :=
  (page c len pageSize (cur.bind (cursorPos c len))).page

/-- cairn_atproto^27 through Sky: a load-more page for a cursor the feed doesn't hold changes nothing it shows. -/
def stale (cf : Config) (f : Feed) (len : Nat) : Bool :=
  match f.loadMore with
  | some (l, c) =>
    let g := { f with cursor := some (c ++ "0") }
    [some (pageAt cf len (some c)), some (pageAt cf len none), none].all fun p =>
      (g.gotLoadMore l p).content == g.content
  | none => true

/-- cairn_atproto^29 through Sky: a refresh racing a load-more, either order of answers (or failures): the same feed. -/
def race (cf : Config) (f : Feed) (len : Nat) : Bool :=
  match f.loadMore, f.refresh with
  | some (l, c), some r =>
    let pls := [some (pageAt cf len (some c)), none]
    let prs := [some (pageAt cf len none), some (pageAt cf (len + 100) none), none]
    pls.all fun pl => prs.all fun pr =>
      (f.gotLoadMore l pl).gotRefresh r pr == (f.gotRefresh r pr).gotLoadMore l pl
  | _, _ => true

/-- ^46, as a state: the rows are the feed's posts, keyed by `Rows.make`, from a key above `0`. -/
def rowsFollow (s : State) : Bool :=
  s.rows.items == s.feed.items && s.rows == Rows.make s.rows.top s.rows.items && 0 < s.rows.top

/-- ^46, as a step: posts put on top of the posts there (signed in) leave every one of those
with its key, and the list the same. -/
def prependKeeps (t : Transition State) : Bool :=
  let old := t.before.rows.items
  let new := t.after.feed.items
  let n := new.length - old.length
  if live t.after.session && !old.isEmpty && 0 < n && new.drop n == old && n < t.before.rows.top then
    t.after.rows.top + n == t.before.rows.top && t.after.gen == t.before.gen
  else true

/-- ^47, as a state: every image load in flight is for an image a row shows; signed out, none
is, and there are no rows. -/
def imagesNear (s : State) : Bool :=
  if live s.session then
    let srcs := s.rows.items.flatMap sourcesOf
    s.images.pending.all fun p => srcs.contains p.2
  else s.images.pending.isEmpty && s.rows == {}

/-- The host drops an image Sky knows, or one it never loaded. -/
def evict (s : State) : Gen SubEvent := do
  let known := s.images.known.map (·.1)
  if known.isEmpty || (← Gen.chance 1 8) then return .evicted "https://example.invalid/never.png"
  return .evicted (← Gen.elem known)

/-! ## Against the fake PDS as a server (cairn#252)

The world is the whole fake PDS (`Fake.server`): the tester's repo and mutes persist through a
sequence, replies fail before the server acts or are lost after it, and between steps posts
arrive, other accounts like, repost and follow, the AppView catches up and the token expires. -/

/-- The feed as the server's timeline has it (^24, through cairn_atproto^26–^29). -/
def feedOk (s : State) (w : World) : Bool :=
  let c := w.server.cfg
  let len := w.server.length
  contiguous c s.feed && cursorOfLast c s.feed && stale c s.feed len && race c s.feed len

/-- ^41: every key Sky's tables wrote this session and hold settled shows what the server
holds: the tester's repo for likes, reposts and follows (the PDS's own truth), the mutes. -/
def actsHeld (s : State) (w : World) : Bool :=
  let t := s.acts.tables
  let rec_ok (tb : Cairn.Optimistic.Table String RKey) (truth : String → Bool) : Bool :=
    tb.entries.toList.all fun (k, e) =>
      !(e.written && e.phase.isIdle) || ((tb.shown k).isSome == truth k)
  rec_ok t.likes w.likedBy && rec_ok t.reposts w.repostedBy &&
    rec_ok t.follows (fun d => (w.server.now.myFollow d).isSome) &&
    t.mutes.entries.toList.all fun (k, e) =>
      !(e.written && e.phase.isIdle) || (t.mutes.shown k == w.muted k)

/-- ^41's counts: a post Sky has a view of, whose like settled, shows the server's like count
whenever no one else liked it or took a like back since the view (its others are the server's). -/
def countsHeld (s : State) (w : World) : Bool :=
  s.feed.items.all fun it =>
    let p := it.post
    match s.acts.views[p.uri]? with
    | none => true
    | some v =>
      let mine := w.likedBy p.uri
      let others := w.likeCount p.uri - Cairn.Optimistic.ind mine
      !(s.acts.tables.likes.settled p.uri && s.acts.tables.likes.written p.uri &&
          v.likes - Cairn.Optimistic.ind v.liked.isSome == others) ||
        s.acts.likeCount p == w.likeCount p.uri

/-- A world for a sequence. Half start from the seed the fuzz types (`cfg`'s identifier and
password), saved signed in half of those; the rest from a random seed, saved signed in, since
their password can't be typed. -/
def worldGen : Gen World := do
  let w ← Fake.worldGen {}
  if ← Gen.chance 1 2 then
    let w0 := World.init { w.server.cfg with seed := cfg.seed }
    if ← Gen.chance 1 2 then return w0.saved
    return w0
  return w.saved

/-- Like, repost, follow and mute pressed often, so their writes race; Undo after a mute too;
Sign Out (the app menu) only once a page is in, and seldom, like Cancel, since a world whose
password can't be typed stays signed out after them. The notifications and both Retries often
enough that their rows come into view, load more and refresh; acting from a notification (Like,
Repost, Follow back) often, and the tabs and the Go menu often enough that each list is left and
come back to. -/
def weights (s : State) (r : ControlRef) : Nat :=
  if r.claim == 37 || r.claim == 38 then 6
  else if r.claim == 76 || r.claim == 77 then 10
  else if r.claim == 83 then 4
  else if r.claim == 62 || r.claim == 73 || r.claim == 74 || r.claim == 75 then 3
  else if r.claim == 39 || r.claim == 40 || r.claim == 58 then 3
  else if r.claim == 49 then (if s.acts.reqs.isEmpty && s.acts.views.isEmpty then 0 else 1)
  else if r.claim == 12 then 1
  else if r.claim == 61 || r.claim == 65 || r.claim == 31 then 4
  else 2

/-- ^67 against the server: the notifications are a contiguous run of the server's, newest
first (the server keeps them oldest first, and only adds at the newest end). -/
def notesRun (s : State) (w : World) : Bool :=
  let mine := s.notes.list.items.map (·.uri)
  let theirs := w.server.notices.reverse.map (·.uri)
  mine.isEmpty || (List.range (theirs.length + 1)).any fun i => mine.isPrefixOf (theirs.drop i)

/-- ^68 and ^69 as states: the rows, flattened, are the notifications held, in order; each row
is of one reason and subject; no row is from a muted account. -/
def groupsOk (s : State) : Bool :=
  let gs := s.noteGroups
  (gs.flatMap (·.members)).map (·.uri) == (s.notes.list.items.filter fun n => !s.muted n.author.did).map (·.uri) &&
    gs.all (fun g => !g.members.isEmpty && g.members.all fun n => n.reason == g.reason && n.reasonSubject == g.subject) &&
    gs.all (fun g => g.members.all fun n => !s.muted n.author.did)

/-- ^70 against the server: the `seenAt` the server holds is at most the newest notification
that has appeared on screen. -/
def seenOk (s : State) (w : World) : Bool := (w.seenAt.getD 0) ≤ s.notes.seen.1.mark

/-- ^71 as a state: at most one `getUnreadCount` the session holds (in flight or held for a
token refresh); signed out, none, no notifications and Home. -/
def pollOk (s : State) : Bool :=
  let polls := (s.session.inflight.map (·.2) ++ s.session.held).filter (·.call == CairnAtproto.Session.Call.getUnreadCount)
  polls.length ≤ 1 &&
    (live s.session || (polls.isEmpty && s.notes.list == {} && s.notes.poll.isNone &&
      s.notes.seenCalls.isEmpty && s.tab == .home))

/-- The world a sequence starts with (`worldGen`), where other accounts have often acted
already, more than a page's worth at times, so the notifications load more (^64, ^65) and group. -/
def worldInit : Gen World := do
  let w ← worldGen
  let n ← Gen.elem [0, 5, 20, 60, 120]
  let mut srv := w.server.grow 20
  let mine := (List.range srv.length).filter (isMine srv.cfg)
  for _ in List.range n do
    let kind ← Gen.elem [ActKind.like, .like, .repost, .follow]
    let post ← if mine.isEmpty then pure none else some <$> Gen.elem mine
    srv := srv.control (.act kind (← Gen.below authorNames.length) post)
  return { w with server := srv.control .catchup }

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
    | .http .. => some do
      -- Images: the fake's (`Fake.server` answers only XRPC).
      match CairnAtproto.Fake.replies FakeCheck.cfg { phase := fun s => some s.session.phase } s id r with
      | some g => g
      | none => return .failed .other "not the fake's"
    | _ => some do
      match CairnAtproto.Fake.replies FakeCheck.cfg { phase := fun s => some s.session.phase } s id r with
      | some g => g
      | none => return .failed .other "not the fake's"
  relations :=
    [ (24, fun t => decide (Inv t.after)),
      (25, fun t => decide (SignedOutEmpty t.after)),
      (46, fun t => FakeCheck.rowsFollow t.after && FakeCheck.prependKeeps t),
      (47, fun t => FakeCheck.imagesNear t.after),
      (68, fun t => FakeCheck.groupsOk t.after),
      (69, fun t => FakeCheck.groupsOk t.after),
      (71, fun t => FakeCheck.pollOk t.after),
      (84, fun t => (t.after.tab == .home || t.after.tab == .notifications) &&
        keptLists t.after == [feedRef, notesRef]),
      (85, fun t => t.after.unreadSent == t.after.notes.unreadShown) ]
  badge := [(85, fun s b => b == s.notes.badge)]
  subEvents := fun s sb => match sb with
    | .imageCache _ => some (FakeCheck.evict s)
    | _ => none
  edits := fun _ id => match id with
    | 6 => some FakeCheck.typeIdentifier
    | 7 => some FakeCheck.typePassword
    | 8 => some FakeCheck.typeService
    | _ => none
  weights := FakeCheck.weights
  server := some { CairnAtproto.Fake.server (S := State) {}
      [(24, FakeCheck.feedOk), (41, FakeCheck.actsHeld), (41, FakeCheck.countsHeld),
       (67, FakeCheck.notesRun), (70, FakeCheck.seenOk)]
      [(41, FakeCheck.actsHeld), (67, FakeCheck.notesRun), (70, FakeCheck.seenOk)] with
    init := FakeCheck.worldInit
    -- A load-more fails one time in four before it reaches the server, so Retry (^31, ^65)
    -- gets pressed.
    handle := fun w id r => match r with
      | .http _ url .. => do
        if (url.splitOn "cursor=").length > 1 && (← Gen.chance 1 4) then
          return (w, .failed .network "The fuzz's host dropped the connection.")
        CairnAtproto.Fake.serve w id r
      | _ => CairnAtproto.Fake.serve w id r }
  outstanding := [(24, fun s ids => ids.mergeSort == s.waiting.mergeSort)]
  drained := [(24, fun s => s.feed.loadMore.isNone && s.feed.refresh.isNone &&
    s.session.inflight.isEmpty && s.session.held.isEmpty && s.own.isEmpty && s.forgetting.isEmpty &&
    s.images.pending.isEmpty && s.notes.calls.isEmpty && s.notes.todo.isEmpty && s.notes.postsDue.isEmpty)]

end Sky
