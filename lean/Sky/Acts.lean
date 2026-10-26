module

public import Sky.Feed
public import Cairn.Optimistic
public import CairnAtproto

/-! # Acting: like, repost, follow and mute (cairn#252)

Each kind of act is a `Cairn.Optimistic` table (Cairn's docs/optimistic.md), and every place a
post or an account appears reads the same table, so one post shows one state everywhere:

* **likes** and **reposts**, keyed by the post's URI; the value is the record's key in the
  account's repo, or none (`RKey`), and two values are the same to the server when both are
  some or both none (`sameKey`): liked or not, whichever record;
* **follows**, keyed by the account's DID, the follow record's key;
* **mutes**, keyed by DID, a boolean.

**A press** mints a record key (`TidClock.mint`, cairn_atproto^17) and sets the table, which shows
the new value in that step. The table's outputs become session calls, queued in `outbox` and
sent by the model's `flush` in the same step (`Sky.Model`): `putRecord` / `deleteRecord` for a
record, `muteActor` / `unmuteActor` for a mute; each call id is kept with what it is for
(`reqs`). A write's answer is read by `WriteOutcome.ofAnswer`: 2xx `acked`, a 4xx `refused`
(said in `line` and announced), a 5xx or a lost reply `lost`, then read back:

* a record by `getRecord` on the account's PDS (`ReadBack`), which reflects every write it
  acknowledged (cairn_atproto^23);
* a mute by sending the same mute again (`muteActor` and `unmuteActor` are idempotent): its 2xx
  says the server holds the value now. `getProfile`'s `viewer.muted` is the AppView's, which can
  lag behind a mute, so it only checks a view that disagrees with a written mute, and can
  confirm the written value but never overturn it (`profileInput`).

**Views.** Every post and account in a page Sky receives is `seen` by the tables (the viewer's
like, repost, follow and mute), and each post's last view is kept (`views`, the newest by call id)
for its counts: shown, a count is `count c v w` (`Cairn.Optimistic.count`), the view's count
less the viewer's own in it, plus what is shown.

**The tables are always calm** (`Tables.Ok`, kept as a field of `Acts`): every key at rest shows
the value last heard from the server (`Table.Calm`), whatever happened, because every change of
a table is a `Table.feed` (`Table.calm_feed`). -/

@[expose] public section

namespace Sky
open Cairn Cairn.Optimistic CairnAtproto CairnAtproto.Session

/-- A like's, repost's or follow's record key, or none. -/
abbrev RKey := Option String

/-- The same to the server: both some (whichever record), or both none. -/
def sameKey (a b : RKey) : Bool := a.isSome == b.isSome

theorem sameKey_same : Same sameKey :=
  ⟨fun a => by simp [sameKey],
   fun a b h => by simp only [sameKey, beq_iff_eq] at h ⊢; exact h.symm,
   fun a b c h1 h2 => by simp only [sameKey, beq_iff_eq] at h1 h2 ⊢; exact h1.trans h2⟩

def sameBool (a b : Bool) : Bool := a == b

theorem sameBool_same : Same sameBool := Same.beq

/-- The kinds of act. -/
inductive Kind where
  | like
  | repost
  | follow
  | mute
deriving Repr, DecidableEq, Inhabited

def Kind.tag : Kind → String
  | .like => "like"
  | .repost => "repost"
  | .follow => "follow"
  | .mute => "mute"

/-- The record collection a kind writes (none for a mute). -/
def Kind.collection : Kind → String
  | .like => nsidLike
  | .repost => nsidRepost
  | .follow => nsidFollow
  | .mute => ""

/-- The timer that clears the status line's rollback (and a mute's Undo) after `lineMs`. -/
def Acts.lineTimer : String := "line"
def Acts.lineMs : Nat := 8000

/-- What a call Sky made for an act is for. -/
inductive Req where
  /-- A table's write. -/
  | write (k : Kind) (t : Ticket String)
  /-- A record read back with `getRecord`, at `rkey`. -/
  | record (k : Kind) (t : Ticket String) (rkey : String)
  /-- A mute whose answer was lost, sent again to find out (`v`: muted or not). -/
  | remute (t : Ticket String) (v : Bool)
  /-- A mute checked with `getProfile`, after a view disagreed with it. -/
  | profile (t : Ticket String)
deriving Repr, DecidableEq, Inhabited

/-- What the model sends for the acts in this step: a session call, or an effect. -/
inductive Job where
  | call (q : Req) (c : Call)
  | effect (e : Effect)
deriving Repr, Inhabited

/-- A post's last view: the call it came in, its CID and author, and its counts with the
viewer's own like and repost (record keys) in them. -/
structure PostView where
  call : Nat
  cid : String
  handle : String
  likes : Nat
  liked : RKey
  reposts : Nat
  reposted : RKey
deriving Repr, DecidableEq, Inhabited

/-- The four tables. -/
structure Tables where
  likes : Table String RKey := .empty none sameKey
  reposts : Table String RKey := .empty none sameKey
  follows : Table String RKey := .empty none sameKey
  mutes : Table String Bool := .empty false sameBool

/-- Every table compares as it should and is calm. -/
def Tables.Ok (t : Tables) : Prop :=
  t.likes.same = sameKey ∧ t.likes.Calm ∧ t.reposts.same = sameKey ∧ t.reposts.Calm ∧
    t.follows.same = sameKey ∧ t.follows.Calm ∧ t.mutes.same = sameBool ∧ t.mutes.Calm

theorem Tables.ok_empty : ({} : Tables).Ok :=
  ⟨rfl, Table.calm_empty _ _ sameKey_same, rfl, Table.calm_empty _ _ sameKey_same,
   rfl, Table.calm_empty _ _ sameKey_same, rfl, Table.calm_empty _ _ sameBool_same⟩

/-- The table of a record kind (a mute is not one: its table is `mutes`). -/
def Tables.tableOf (t : Tables) : Kind → Table String RKey
  | .like => t.likes
  | .repost => t.reposts
  | _ => t.follows

/-- A record kind's table fed one input. -/
def Tables.feedRec (t : Tables) (k : Kind) (i : Input String RKey) :
    Tables × List (Out String RKey) :=
  match k with
  | .like => ({ t with likes := (t.likes.feed i).1 }, (t.likes.feed i).2)
  | .repost => ({ t with reposts := (t.reposts.feed i).1 }, (t.reposts.feed i).2)
  | _ => ({ t with follows := (t.follows.feed i).1 }, (t.follows.feed i).2)

def Tables.feedMute (t : Tables) (i : Input String Bool) : Tables × List (Out String Bool) :=
  ({ t with mutes := (t.mutes.feed i).1 }, (t.mutes.feed i).2)

theorem Tables.feedRec_ok {t : Tables} (h : t.Ok) (k : Kind) (i : Input String RKey) :
    (t.feedRec k i).1.Ok := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  cases k <;> simp only [feedRec]
  · exact ⟨by rw [Table.feed_same]; exact h1, Table.calm_feed _ (h1 ▸ sameKey_same) h2 i,
      h3, h4, h5, h6, h7, h8⟩
  · exact ⟨h1, h2, by rw [Table.feed_same]; exact h3,
      Table.calm_feed _ (h3 ▸ sameKey_same) h4 i, h5, h6, h7, h8⟩
  all_goals exact ⟨h1, h2, h3, h4, by rw [Table.feed_same]; exact h5,
      Table.calm_feed _ (h5 ▸ sameKey_same) h6 i, h7, h8⟩

theorem Tables.feedMute_ok {t : Tables} (h : t.Ok) (i : Input String Bool) :
    (t.feedMute i).1.Ok := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, by simp only [feedMute, Table.feed_same]; exact h7,
    Table.calm_feed _ (h7 ▸ sameBool_same) h8 i⟩

/-- **The acts.** -/
structure Acts where
  tables : Tables := {}
  /-- The tables are calm: always (`Tables.Ok`). -/
  ok : tables.Ok := by exact Tables.ok_empty
  /-- The calls in flight for the acts, by Sky's call id. -/
  reqs : Std.TreeMap Nat Req compare := {}
  /-- Each post's last view, by URI. -/
  views : Std.TreeMap String PostView compare := {}
  /-- The handles of the accounts seen, by DID, for the words of a rollback. -/
  handles : Std.TreeMap String String compare := {}
  /-- The record key of the last view of a follow, by DID. -/
  followSeen : Std.TreeMap String String compare := {}
  /-- Record keys come from here: strictly increasing (cairn_atproto^18). -/
  clock : TidClock := TidClock.new 0
  /-- What to send in this step. -/
  outbox : List Job := []
  /-- The last rollback, in words. A press clears it. -/
  line : Option String := none

instance : Inhabited Acts := ⟨{}⟩

instance : Repr Acts where
  reprPrec a _ := s!"acts: {a.reqs.size} calls, {a.views.size} views, {a.outbox.length} to send"

/-- Nothing held: the acts of a signed-out Sky. -/
def Acts.isEmpty (a : Acts) : Bool :=
  a.reqs.isEmpty && a.views.isEmpty && a.outbox.isEmpty && a.line.isNone &&
    a.tables.likes.size == 0 && a.tables.reposts.size == 0 && a.tables.follows.size == 0 &&
    a.tables.mutes.size == 0

/-- The status line's rollback cleared (its timer, `lineTimer`). -/
def Acts.clearLine (a : Acts) : Acts := { a with line := none }

/-! ## What is shown -/

def Acts.liked (a : Acts) (uri : String) : Bool := (a.tables.likes.shown uri).isSome
def Acts.reposted (a : Acts) (uri : String) : Bool := (a.tables.reposts.shown uri).isSome
def Acts.following (a : Acts) (did : String) : Bool := (a.tables.follows.shown did).isSome
def Acts.muted (a : Acts) (did : String) : Bool := a.tables.mutes.shown did

/-- A post's like count as shown: its last view's (or the post's own), less the viewer's like in
that view, plus the like shown. -/
def Acts.likeCount (a : Acts) (p : Post) : Nat :=
  match a.views[p.uri]? with
  | some v => count v.likes v.liked.isSome (a.liked p.uri)
  | none => count p.likeCount p.viewer.like.isSome (a.liked p.uri)

def Acts.repostCount (a : Acts) (p : Post) : Nat :=
  match a.views[p.uri]? with
  | some v => count v.reposts v.reposted.isSome (a.reposted p.uri)
  | none => count p.repostCount p.viewer.repost.isSome (a.reposted p.uri)

theorem Acts.likeCount_ge (a : Acts) (p : Post) : ind (a.liked p.uri) ≤ a.likeCount p := by
  unfold Acts.likeCount; split <;> exact count_ge _ _ _

theorem Acts.repostCount_ge (a : Acts) (p : Post) : ind (a.reposted p.uri) ≤ a.repostCount p := by
  unfold Acts.repostCount; split <;> exact count_ge _ _ _

/-- A settled key shows what the server last confirmed. -/
theorem Acts.settled_like (a : Acts) {uri : String} (h : a.tables.likes.settled uri = true) :
    a.liked uri = (a.tables.likes.server uri).isSome := by
  have := a.ok.2.1.settled h
  rw [a.ok.1] at this
  simpa [Acts.liked, sameKey] using this

/-! ## Words -/

/-- The record key at the end of an AT URI. -/
def rkeyOf (uri : String) : String := (uri.splitOn "/").getLast?.getD ""

def Kind.verb (k : Kind) (on : Bool) : String :=
  match k, on with
  | .like, true => "like"
  | .like, false => "unlike"
  | .repost, true => "repost"
  | .repost, false => "undo the repost of"
  | .follow, true => "follow"
  | .follow, false => "unfollow"
  | .mute, true => "mute"
  | .mute, false => "unmute"

/-- Whose: "@alice's post" for a post, "@alice" for an account. -/
def Acts.whose (a : Acts) (k : Kind) (key : String) : String :=
  match k with
  | .like | .repost =>
    match a.views[key]? with
    | some v => "@" ++ v.handle ++ "'s post"
    | none => "the post"
  | _ =>
    match a.handles[key]? with
    | some h => "@" ++ h
    | none => "the account"

/-- What a rollback says: "Couldn't like @alice's post: rate limited, try again in 40 s". `on`
is what the person asked for. -/
def Acts.say (a : Acts) (k : Kind) (key : String) (on : Bool) : Optimistic.Reason → String
  | .refused why => s!"Couldn't {k.verb on} {a.whose k key}: {why}"
  | .notApplied => s!"Couldn't {k.verb on} {a.whose k key}: it never reached the server"

/-! ## Carrying out a table's outputs -/

/-- Where a write or read goes, and when it is: the account's DID and the clock (ms). -/
structure Ctx where
  did : String
  nowMs : Nat
deriving Repr, Inhabited

def timerName (k : Kind) (key : String) : String := s!"act {k.tag} {key}"

/-- The record a kind writes for key `key`. -/
def Acts.recordOf (a : Acts) (k : Kind) (key : String) (createdAt : String) : Record :=
  let cid := (a.views[key]?.map (·.cid)).getD ""
  match k with
  | .like => .like ⟨key, cid⟩ createdAt
  | .repost => .repost ⟨key, cid⟩ createdAt
  | _ => .follow key createdAt

/-- The record key to read back for key `key` of a record kind: the one being written, else the
one the server holds, else the one a view showed. -/
def Acts.readKey (a : Acts) (k : Kind) (key : String) : String :=
  let e := (a.tables.tableOf k).get key
  let viewKey : Option String := match k with
    | .like => (a.views[key]?).bind (·.liked)
    | .repost => (a.views[key]?).bind (·.reposted)
    | _ => a.followSeen[key]?
  match e.phase.pending, e.server, e.want with
  | some (some r), _, _ => r
  | _, some r, _ => r
  | _, _, some r => r
  | _, _, _ => viewKey.getD ""

def Acts.push (a : Acts) (j : Job) : Acts := { a with outbox := a.outbox ++ [j] }

/-- One output of a record kind's table. -/
def Acts.performRec (ctx : Ctx) (k : Kind) (a : Acts) : Out String RKey → Acts
  | .write t v =>
    let c := match v with
      | some r => Call.putRecord { repo := ctx.did, rkey := r,
                                   record := a.recordOf k t.key (formatDatetime ctx.nowMs) }
      | none => Call.deleteRecord ⟨ctx.did, k.collection, ((a.tables.tableOf k).server t.key).getD ""⟩
    a.push (.call (.write k t) c)
  | .read t =>
    let r := a.readKey k t.key
    a.push (.call (.record k t r) (Call.getRecord ⟨ctx.did, k.collection, r⟩))
  | .retryIn key ms => a.push (.effect (.setTimer (timerName k key) ms))
  | .rolledBack key r =>
    -- What was asked for is the opposite of what is shown again.
    let w := a.say k key ((a.tables.tableOf k).shown key).isNone r
    (({ a with line := some w }.push (.effect (.announce w .high))).push
      (.effect (.setTimer Acts.lineTimer Acts.lineMs)))

/-- One output of the mutes' table. -/
def Acts.performMute (a : Acts) : Out String Bool → Acts
  | .write t v =>
    a.push (.call (.write .mute t) (if v then Call.muteActor t.key else Call.unmuteActor t.key))
  | .read t =>
    match (a.tables.mutes.get t.key).phase with
    | .doubt w =>
      a.push (.call (.remute t w) (if w then Call.muteActor t.key else Call.unmuteActor t.key))
    | _ => a.push (.call (.profile t) (Call.getProfile t.key))
  | .retryIn key ms => a.push (.effect (.setTimer (timerName .mute key) ms))
  | .rolledBack key r =>
    let w := a.say .mute key (!a.tables.mutes.shown key) r
    (({ a with line := some w }.push (.effect (.announce w .high))).push
      (.effect (.setTimer Acts.lineTimer Acts.lineMs)))

/-- Feed a record kind's table and carry out what it asks. -/
def Acts.feedRec (ctx : Ctx) (a : Acts) (k : Kind) (i : Input String RKey) : Acts :=
  let r := a.tables.feedRec k i
  r.2.foldl (Acts.performRec ctx k) { a with tables := r.1, ok := Tables.feedRec_ok a.ok k i }

def Acts.feedMute (a : Acts) (i : Input String Bool) : Acts :=
  let r := a.tables.feedMute i
  r.2.foldl Acts.performMute { a with tables := r.1, ok := Tables.feedMute_ok a.ok i }

/-! ## Presses -/

/-- Mint a record key at the clock (ms). -/
def Acts.mint (a : Acts) (nowMs : Nat) : Acts × String :=
  match a.clock.mint (nowMs * 1000) with
  | some (t, c) => ({ a with clock := c }, t.encode)
  | none => (a, "2222222222222")

/-- Toggle a record kind's key: off if it shows some record, else on with a new record key. -/
def Acts.toggle (ctx : Ctx) (a : Acts) (k : Kind) (key : String) : Acts :=
  let (a, rk) := a.mint ctx.nowMs
  Acts.feedRec ctx { a with line := none } k (.set key fun v => if v.isSome then none else some rk)

def Acts.toggleMute (a : Acts) (did : String) : Acts :=
  Acts.feedMute { a with line := none } (.set did (!·))

/-! ## A press shows at once -/

/-- What a kind shows for a key: liked, reposted, following or muted. -/
def Acts.on (a : Acts) : Kind → String → Bool
  | .like, key => (a.tables.likes.shown key).isSome
  | .repost, key => (a.tables.reposts.shown key).isSome
  | .follow, key => (a.tables.follows.shown key).isSome
  | .mute, key => a.tables.mutes.shown key

theorem Acts.foldl_performRec_tables (ctx : Ctx) (k : Kind) :
    ∀ (os : List (Out String RKey)) (a : Acts), (os.foldl (Acts.performRec ctx k) a).tables = a.tables
  | [], _ => rfl
  | o :: os, a => (Acts.foldl_performRec_tables ctx k os _).trans (by cases o <;> rfl)

theorem Acts.foldl_performMute_tables :
    ∀ (os : List (Out String Bool)) (a : Acts), (os.foldl Acts.performMute a).tables = a.tables
  | [], _ => rfl
  | o :: os, a => (Acts.foldl_performMute_tables os _).trans (by
      cases o <;> first | rfl | (simp only [Acts.performMute]; split <;> rfl))

theorem Acts.feedRec_tables (ctx : Ctx) (a : Acts) (k : Kind) (i : Input String RKey) :
    (Acts.feedRec ctx a k i).tables = (a.tables.feedRec k i).1 :=
  Acts.foldl_performRec_tables ctx k _ _

theorem Acts.feedMute_tables (a : Acts) (i : Input String Bool) :
    (a.feedMute i).tables = (a.tables.feedMute i).1 :=
  Acts.foldl_performMute_tables _ _

theorem Acts.mint_tables (a : Acts) (now : Nat) : (a.mint now).1.tables = a.tables := by
  unfold Acts.mint; split <;> rfl

/-- A press of like, repost or follow shows the other value in its own step. -/
theorem Acts.toggle_on (ctx : Ctx) (a : Acts) (k : Kind) (hk : k ≠ .mute) (key : String) :
    (Acts.toggle ctx a k key).on k key = !a.on k key := by
  have ht := Acts.mint_tables a ctx.nowMs
  cases k with
  | mute => exact absurd rfl hk
  | like =>
    simp only [Acts.toggle, Acts.on, Acts.feedRec_tables, Tables.feedRec, Table.shown_set, ht]
    split <;> simp_all
  | repost =>
    simp only [Acts.toggle, Acts.on, Acts.feedRec_tables, Tables.feedRec, Table.shown_set, ht]
    split <;> simp_all
  | follow =>
    simp only [Acts.toggle, Acts.on, Acts.feedRec_tables, Tables.feedRec, Table.shown_set, ht]
    split <;> simp_all

/-- A press of mute shows the other value in its own step. -/
theorem Acts.toggleMute_on (a : Acts) (did : String) :
    (a.toggleMute did).on .mute did = !a.on .mute did := by
  simp only [Acts.toggleMute, Acts.on, Acts.feedMute_tables, Tables.feedMute, Table.shown_set]

/-! ## Views -/

/-- A post seen in the answer to call `call`: its view kept if newer than the last, and the
viewer's like and repost fed as `seen`. -/
def Acts.seePost (ctx : Ctx) (call : Nat) (a : Acts) (p : Post) : Acts :=
  let liked := p.viewer.like.map rkeyOf
  let reposted := p.viewer.repost.map rkeyOf
  let newer : Bool := match a.views[p.uri]? with
    | some v => decide (v.call ≤ call)
    | none => true
  if newer then
    let v : PostView := { call, cid := p.cid, handle := p.author.handle, likes := p.likeCount,
                          liked, reposts := p.repostCount, reposted }
    let a := { a with views := a.views.insert p.uri v }
    let a := Acts.feedRec ctx a .like (.seen p.uri liked)
    Acts.feedRec ctx a .repost (.seen p.uri reposted)
  else a

/-- An account seen: its handle, and the viewer's follow and mute fed as `seen`. Not the
account itself. -/
def Acts.seeProfile (ctx : Ctx) (a : Acts) (p : Profile) : Acts :=
  if p.did = ctx.did then a
  else
    let following := p.viewer.following.map rkeyOf
    let a := { a with handles := a.handles.insert p.did p.handle,
                      followSeen := match following with
                        | some r => a.followSeen.insert p.did r
                        | none => a.followSeen }
    let a := Acts.feedRec ctx a .follow (.seen p.did following)
    a.feedMute (.seen p.did p.viewer.muted)

/-- The author of the post a post quotes, if it quotes one. -/
def quotedAuthor : Option Embed → Option Profile
  | some (.record (.post q)) => some q.author
  | some (.recordWithMedia (.post q) _) => some q.author
  | _ => none

/-- The posts and accounts of a feed item: the post and its author, the quoted post's author, the
reposter, and the reply's parent and root. -/
def Acts.seeItem (ctx : Ctx) (call : Nat) (a : Acts) (it : FeedItem) : Acts :=
  let a := Acts.seePost ctx call a it.post
  let a := Acts.seeProfile ctx a it.post.author
  let a := match quotedAuthor it.post.embed with
    | some q => Acts.seeProfile ctx a q
    | none => a
  let a := match it.reason with
    | some (.repost b _) => Acts.seeProfile ctx a b
    | _ => a
  match it.reply with
  | some r =>
    let a := match r.parent with
      | .post p => Acts.seeProfile ctx (Acts.seePost ctx call a p) p.author
      | _ => a
    match r.root with
    | .post p => Acts.seeProfile ctx (Acts.seePost ctx call a p) p.author
    | _ => a
  | none => a

/-- A page received in the answer to call `call`. -/
def Acts.seePage (ctx : Ctx) (call : Nat) (a : Acts) (items : List FeedItem) : Acts :=
  items.foldl (Acts.seeItem ctx call) a

/-! ## Answers -/

/-- A write's answer as the table's input. -/
def writeInput {V : Type} (t : Ticket String) (nowMs : Nat) (a : Answer) : Input String V :=
  match WriteOutcome.ofAnswer a with
  | .acked => .acked t
  | o@(.refused ..) => .refused t (o.describe (nowMs / 1000))
  | .notSent => .refused t "not signed in"
  | .lost _ => .lost t

/-- A read back's answer: the record at `rkey`, or none. -/
def readInput (t : Ticket String) (rkey : String) (a : Answer) : Input String RKey :=
  match ReadBack.ofAnswer a with
  | .found _ => .read t (some rkey)
  | .missing => .read t none
  | .unsure => .readFailed t

/-- A mute sent again: a 2xx says the server holds `v`. -/
def remuteInput (t : Ticket String) (v : Bool) (a : Answer) : Input String Bool :=
  match WriteOutcome.ofAnswer a with
  | .acked => .read t v
  | _ => .readFailed t

/-- A mute checked with `getProfile`, the AppView's view, which can lag behind a mute: it can
confirm what the server last confirmed (`v`), never overturn it, so a disagreeing answer drops the
check (`readFailed`, which leaves the key as it was). -/
def profileInput (t : Ticket String) (v : Bool) (a : Answer) : Input String Bool :=
  match a with
  | .reply r =>
    match Outcome.ofReply ProfileDetail.ofJson r with
    | .ok d => if d.profile.viewer.muted == v then .read t v else .readFailed t
    | _ => .readFailed t
  | .signedOut => .readFailed t

/-- The answer to call `id`, if it is one of the acts'. -/
def Acts.answer (ctx : Ctx) (a : Acts) (id : Nat) (ans : Answer) : Acts :=
  match a.reqs[id]? with
  | none => a
  | some q =>
    let a := { a with reqs := a.reqs.erase id }
    match q with
    | .write .mute t => a.feedMute (writeInput t ctx.nowMs ans)
    | .write k t => Acts.feedRec ctx a k (writeInput t ctx.nowMs ans)
    | .record k t r => Acts.feedRec ctx a k (readInput t r ans)
    | .remute t v => a.feedMute (remuteInput t v ans)
    | .profile t => a.feedMute (profileInput t (a.tables.mutes.server t.key) ans)

/-- A timer: a read back's retry. -/
def Acts.timer (ctx : Ctx) (a : Acts) (name : String) : Acts :=
  if name.startsWith "act like " then Acts.feedRec ctx a .like (.retry (name.drop 9).toString)
  else if name.startsWith "act repost " then Acts.feedRec ctx a .repost (.retry (name.drop 11).toString)
  else if name.startsWith "act follow " then Acts.feedRec ctx a .follow (.retry (name.drop 11).toString)
  else if name.startsWith "act mute " then a.feedMute (.retry (name.drop 9).toString)
  else a

end Sky
