module

public import Sky.Feed
public import Sky.Acts
public import Sky.Notifications
public import Sky.SessionFacts
public import Cairn.Text.Field
public import Cairn.UI.Images

/-! # Sky's model

The timeline, the session and the sign-in form, headless. `State` is the session
(`CairnAtproto.Session`), the feed (`Sky.Feed`), the next call id, the form (handle or email, the
app password in a secure field, the service), Sky's own requests and the last problem. Everything
Sky does is a `Cmd` to `State.step`: the person's (type in a field, sign in, load more, refresh,
sign out, open the app-passwords page) and the host's (`Cairn.Msg`). Each step is the input's
handling, then `settle`.

**The password.** The secure field's text reaches one place: `signIn`, which puts it in the one
`createSession` request (marked `redact`) and empties the field in the same step. Every command
but `signIn` and the field's own edits runs on the state with the field blank (`State.blank`), and
the field is put back after, so nothing else Sky does can depend on it (`Sky.Secrets`).

**Requests.** The session chooses its requests' ids; Sky sends session request `rid` as Cairn
request `2 * rid` (`sessionId`) and its own (`Own`: reading the saved service and account at
launch, saving and deleting the account, opening the app-passwords page) under odd ids
(`ownId`), so the two never meet. The session's requests carry their Keychain secret, capture
and `redact` as cairn_atproto builds them; its `forget` outputs are `forgetSecret` requests and
its `cancel` outputs `cancelRequest`s.

**Calls.** A load-more and a refresh are session calls (`Call.getTimeline`) under Sky's call
ids. The app's answer to a call (`Out.answer`) goes to the feed (`Paged.gotLoadMore`,
`Paged.gotRefresh`). Starting a refresh withdraws the load-more in flight (`withdraw`: the
session's `Input.cancel`, which cancels its request or drops it if held for a token refresh), and
so does a refresh whose page replaces the feed.

**Launch.** Sky reads the service default (`readDefault`, the form's service), then the account
it saved (`accountPath`: the service and handle, never a token). With one, it fills in the handle
and resumes the session the Keychain holds (`Input.resume`: `refreshSession`, which a missing item
answers `failed notFound`, so the session signs out and the form shows, the handle filled in).
Signing in saves the account; signing out deletes it.

**Signed out** (`settle`): whenever the session isn't signed in, the feed is emptied and every
call the session has taken on is cancelled. -/

@[expose] public section

namespace Sky
open Cairn CairnJson CairnAtproto CairnAtproto.Session

/-- The defaults domain Sky reads its service from (the app's bundle identifier). -/
def bundleId : String := "dev.cairn.sky"

/-- Posts per page. -/
def pageSize : Nat := 30

def sessionId (rid : Nat) : Nat := 2 * rid

/-- Sky's own request `n`. -/
def ownId (n : Nat) : Nat := 2 * n + 1

def defaultService : String := "https://bsky.social"

/-- Where Sky keeps the account it resumes at launch: the service and the handle. -/
def accountPath : String := "~/Library/Application Support/dev.cairn.sky/account.json"

/-- Bluesky's page for making an app password. -/
def appPasswordsUrl : String := "https://bsky.app/settings/app-passwords"

/-- How long a rollback's line, or a mute's Undo, stays in the status line (`Acts.lineTimer`). -/
def lineMs : Nat := Acts.lineMs

/-- How long a sign-in or resume may take before Cancel is offered. -/
def slowTimer : String := "slow"
def slowMs : Nat := 3000

def identifierHint : String := "handle or email"
def passwordHint : String := "app password"

/-- The password field's control (claim ^7), which Enter in the handle field focuses. -/
def passwordRef : ControlRef := ⟨7, 0⟩

/-- What one of Sky's own requests is for. -/
inductive Own where
  | readService
  | readAccount
  | save
  | delete
  | openHelp
  /-- Opening a post on bsky.app. -/
  | openPost
deriving Repr, DecidableEq, Inhabited

instance : DecidableEq Images := fun a b =>
  decidable_of_iff (a.known = b.known ∧ a.pending = b.pending) (by cases a; cases b; simp)

/-! ## Rows

The feed's posts as the virtual list shows them. Item `i` of the feed is the row with key
`top + i`, and the end row (Loading…, Retry, You're all caught up) has key `0`, last. Posts put
on top take the keys below `top`, so every post already there keeps its key, and the runtime's
anchor (`VList.record_keeps`) finds the reader's post where it was. A feed replaced or emptied
starts a new list (`gen`), at the top. -/

/-- The first key of a new list. -/
def baseTop : Nat := 1000000000

/-- The keys of `n` posts from `top`, then the end row's `0`. -/
def keysOf (top n : Nat) : Array Nat := ((Array.range n).map (top + ·)).push 0

structure Rows where
  /-- The first post's key. -/
  top : Nat := baseTop
  /-- The posts, as the feed holds them. -/
  items : List FeedItem := []
  /-- The same, by index. -/
  arr : Array FeedItem := #[]
  /-- `keysOf top items.length`, kept so the view doesn't build it each frame. -/
  keys : Array Nat := keysOf baseTop 0
deriving Repr, DecidableEq, Inhabited

def Rows.make (top : Nat) (items : List FeedItem) : Rows :=
  { top, items, arr := items.toArray, keys := keysOf top items.length }

/-- The index of the post with key `k`. -/
def Rows.index? (r : Rows) (k : Nat) : Option Nat :=
  if r.top ≤ k ∧ k - r.top < r.arr.size then some (k - r.top) else none

def Rows.item? (r : Rows) (k : Nat) : Option FeedItem := (r.index? k).bind (r.arr[·]?)

def Rows.has (r : Rows) (k : Nat) : Bool := (r.index? k).isSome

/-- How the feed changed since the rows were made. -/
inductive Change where
  | same
  /-- `n` posts were put on top of the posts there. -/
  | prepended (n : Nat)
  | appended
  /-- Anything else: emptied, or replaced. -/
  | replaced
deriving Repr, DecidableEq

def change (old new : List FeedItem) : Change :=
  if new = old then .same
  else if !old.isEmpty && old.length < new.length && new.drop (new.length - old.length) = old then
    .prepended (new.length - old.length)
  else if new.take old.length = old then .appended
  else .replaced

/-- Which list the window shows. -/
inductive Tab where
  | home
  | notifications
deriving Repr, DecidableEq, Inhabited

structure State where
  session : Session.State := Session.init
  feed : Feed := {}
  /-- The next call id. -/
  nextCall : Nat := 0
  /-- Handle or email. -/
  identifier : Text.Field := Text.Field.empty identifierHint
  /-- The app password, until the step that sends it (`signIn` empties it). -/
  password : Text.SecureField := Text.SecureField.empty passwordHint
  /-- The service; empty means `defaultService`, its placeholder. -/
  service : Text.Field := Text.Field.empty defaultService
  /-- The service the session signed in to or resumed at: what Sky saves. -/
  host : String := defaultService
  /-- Sky's own requests in flight, by Cairn id. -/
  own : List (Nat × Own) := []
  nextOwn : Nat := 0
  /-- The session's `forgetSecret` requests in flight, by Cairn id. -/
  forgetting : List Nat := []
  /-- What went wrong last, in words. -/
  problem : Option String := none
  /-- A sign-in or resume has taken a while (`slowTimer`): Cancel is offered. -/
  slow : Bool := false
  /-- The feed's rows. -/
  rows : Rows := {}
  /-- The list's generation: its ref is `⟨14, gen⟩`, so a new one starts at the top. -/
  gen : Nat := 0
  /-- Posts put on top that haven't come into view: the "N new posts" control. -/
  fresh : Nat := 0
  /-- The last load-more failed: the end row offers Retry. -/
  moreFailed : Bool := false
  /-- The avatars and thumbnails: what is known of each, and the loads in flight (odd ids). -/
  images : Images := {}
  /-- The runtime's clock, for "3m" and "Oct 12". -/
  now : Time := {}
  /-- Likes, reposts, follows and mutes (`Sky.Acts`, cairn#252). -/
  acts : Acts := {}
  /-- The notifications: the list, the seen marker, the unread count (`Sky.Notifications`). -/
  notes : Notes := {}
  /-- Which list the window shows. -/
  tab : Tab := .home
  /-- The account just muted from a row: the status line offers Undo until `lineTimer`. -/
  undoMute : Option String := none
  /-- The unread count the Dock badge was last set to (`dock`). -/
  unreadSent : Nat := 0
  /-- The feed's generation its list was last put at the top for (`dock`). -/
  feedAimed : Nat := 0
  /-- The notifications' generation their list was last put at the top for (`dock`). -/
  notesAimed : Nat := 0
deriving Repr, Inhabited

/-! ## Reading the state -/

/-- A session is live: signed in, or refreshing a signed-in session's tokens. -/
def live (s : Session.State) : Bool :=
  match s.phase with
  | .signedIn _ => true
  | .refreshing _ _ (some _) => true
  | _ => false

def account (s : Session.State) : Option Account :=
  match s.phase with
  | .signedIn a => some a
  | .refreshing _ _ (some a) => some a
  | _ => none

/-- Sign-in is possible: launched or signed out, and no abandoned sign-in still outstanding. -/
def canSignIn (s : Session.State) : Bool :=
  (match s.phase with
   | .launched | .signedOut => true
   | _ => false) && s.abandoned.isEmpty

/-- A sign-in is in flight. -/
def signingIn (s : Session.State) : Bool :=
  match s.phase with
  | .signingIn .. => true
  | _ => false

/-- Sign In is enabled: both fields typed in, and no sign-in in flight. -/
def ready (s : State) : Bool :=
  !s.identifier.text.isEmpty && !s.password.field.text.isEmpty && canSignIn s.session

/-- The service typed, or the default. -/
def serviceOf (s : State) : String :=
  let t := s.service.textString.trimAscii.toString
  if t.isEmpty then defaultService else t

/-- The handle or email typed, without spaces round it or a leading `@`. -/
def identifierOf (s : State) : String :=
  let t := s.identifier.textString.trimAscii.toString
  if t.startsWith "@" then (t.drop 1).toString else t

/-- The session's own request in flight (sign-in or refresh). -/
def phaseRid : Phase → List Nat
  | .signingIn rid _ => [rid]
  | .refreshing rid _ _ => [rid]
  | _ => []

/-- Every Cairn request id Sky still waits on. -/
def State.waiting (s : State) : List Nat :=
  s.own.map (·.1) ++ s.forgetting ++ s.session.inflight.map (sessionId ·.1) ++
    (phaseRid s.session.phase).map sessionId ++ s.session.abandoned.map sessionId ++
    s.images.pending.map (·.1)

/-! ## Words -/

def faultWords : Fault → String
  | .notFound => "not found"
  | .denied => "denied"
  | .timeout => "timed out"
  | .network => "no connection"
  | .invalid => "invalid"
  | .other => "failed"

/-- A reply that went wrong, as it came. -/
def describe : Cairn.Reply → String
  | .http st _ body =>
    let e := XrpcError.ofBody body
    let name := e.name.toString
    s!"{st}" ++ (if name.isEmpty then "" else " " ++ name) ++
      (match e.message with | some m => ": " ++ m | none => "")
  | .failed f m => faultWords f ++ (if m.isEmpty then "" else ": " ++ m)
  | _ => "an unexpected reply"

def offline : String := "You're offline, or the service can't be reached."
def rateLimited : String := "Too many tries. Wait a few minutes, then try again."
def wrongPassword : String := "Wrong handle, email or app password."
def authFactor : String :=
  "This account asks for a code from email at sign-in. Sign in with an app password instead: it needs no code."

/-- A refused sign-in, in words. -/
def signInWords : Cairn.Reply → String
  | r@(.http st _ body) =>
    match (XrpcError.ofBody body).name.toString with
    | "AuthenticationRequired" => wrongPassword
    | "AuthFactorTokenRequired" => authFactor
    | "AccountTakedown" => "This account has been taken down."
    | "RateLimitExceeded" => rateLimited
    | _ =>
      if st == 401 then wrongPassword
      else if st == 429 then rateLimited
      else if 500 ≤ st then s!"The service had a problem ({st}). Try again in a moment."
      else describe r
  | .failed .network _ => offline
  | .failed .timeout _ => "The service didn't answer. Try again."
  | .failed .invalid _ => "That service address isn't valid."
  | r => describe r

/-- A call's answer, read as a timeline page; and what went wrong, if it did. -/
def readPage : Answer → Option (Page FeedItem) × Option String
  | .reply r =>
    match Outcome.ofReply FeedPage.ofJson r with
    | .ok p => (some p.page, none)
    | .malformed st => (none, some s!"{st}: not a timeline page")
    | _ => (none, some (describe r))
  | .signedOut => (none, none)

/-! ## The saved account -/

def accountJson (host handle : String) : ByteArray :=
  (encode (.obj [("service", .str host), ("handle", .str handle)])).toUTF8

/-- The saved service and handle. -/
def parseAccount (b : ByteArray) : Option (String × String) := do
  let j ← decodeBytes b
  let svc ← j.str? "service"
  let h ← j.str? "handle"
  if svc.isEmpty then none else some (svc, h)

/-! ## Steps -/

/-- Send one of Sky's own requests. -/
def sendOwn (s : State) (k : Own) (r : Request) : State × List Effect :=
  ({ s with nextOwn := s.nextOwn + 1, own := (ownId s.nextOwn, k) :: s.own },
   [.request (ownId s.nextOwn) r])

/-- The session's cancellations, as Cairn's. -/
def cancelEffects (outs : List Out) : List Effect :=
  outs.filterMap fun
    | .cancel rid => some (.cancelRequest (sessionId rid))
    | _ => none

/-- Withdraw call `id` (the session's `Input.cancel`): in flight, its request is cancelled; held
for a refresh, dropped. -/
def withdraw (ss : Session.State) (id : Nat) : Session.State × List Effect :=
  ((Session.step ss (.cancel [id])).1, cancelEffects (Session.step ss (.cancel [id])).2)

/-- The answer to call `id`, for the feed. -/
def onAnswer0 (s : State) (id : Nat) (a : Answer) : State × List Effect :=
  let (page, prob) := readPage a
  match s.feed.loadMore with
  | some (l, _) =>
    if l = id then
      ({ s with feed := s.feed.gotLoadMore id page,
                problem := prob.map ("Couldn't load more: " ++ ·), moreFailed := prob.isSome }, [])
    else if s.feed.refresh = some id then
      let f := s.feed.gotRefresh id page
      let s := { s with feed := f, problem := prob.map ("Couldn't refresh: " ++ ·) }
      if f.loadMore.isNone then
        let (ss, es) := withdraw s.session l
        ({ s with session := ss }, es)
      else (s, [])
    else (s, [])
  | none =>
    if s.feed.refresh = some id then
      ({ s with feed := s.feed.gotRefresh id page,
                problem := prob.map ("Couldn't refresh: " ++ ·) }, [])
    else (s, [])

/-- Where an act goes and when: the account's DID and the clock. -/
def ctxOf (s : State) : Ctx :=
  { did := ((account s.session).map (·.did)).getD "", nowMs := s.now.wall.toNat }

/-- Whether call `id` is the feed's (the load-more or the refresh in flight). -/
def feedCall (f : Feed) (id : Nat) : Bool :=
  (match f.loadMore with
   | some (l, _) => l == id
   | none => false) || f.refresh == some id

/-- The acts after the answer to call `id`: an act's call goes to its table; a page of the feed
is seen by the tables (the viewer's like, repost, follow and mute of everything in it). -/
def actsAnswer (s : State) (id : Nat) (a : Answer) : Acts :=
  if s.acts.reqs.contains id then s.acts.answer (ctxOf s) id a
  else if feedCall s.feed id then
    match (readPage a).1 with
    | some p => Acts.seePage (ctxOf s) id s.acts p.items
    | none => s.acts
  else s.acts

/-- The answer to call `id`: the feed's, then the acts'. -/
def onAnswer (s : State) (id : Nat) (a : Answer) : State × List Effect :=
  ({ (onAnswer0 s id a).1 with acts := actsAnswer s id a }, (onAnswer0 s id a).2)
/-! ## Notifications' answers

Answers come inside the fold over the session's outputs, where Sky only records them: the list
(`Paged.gotLoadMore`, `Paged.gotRefresh`), the unread count, and what the seen key hears. The
writes and reads the seen key asks for, and a poll that is due, are sent once the fold is done
(`flushNotes`). The notes never withdraw a call: a load-more a refresh forgot is answered into
nothing (`Paged.gotLoadMore` ignores an answer to a call it doesn't wait on). -/

/-- Notifications per page. -/
def notePageSize : Nat := 30

/-- The timer for the seen key's next read, after one failed. -/
def seenRetryTimer : String := "seen-retry"

/-- A call's answer, read as a page of notifications; and what went wrong, if it did. -/
def readNotes : Answer → Option NotificationPage × Option String
  | .reply r =>
    match Outcome.ofReply NotificationPage.ofJson r with
    | .ok p => (some p, none)
    | .malformed st => (none, some s!"{st}: not a page of notifications")
    | _ => (none, some (describe r))
  | .signedOut => (none, none)

/-- The seen key's actions: the retry timer and a rollback's line now; writes and reads queued. -/
def seenAct (acc : State × List Effect) : Cairn.Optimistic.Act Nat → State × List Effect
  | .retryIn ms => (acc.1, acc.2 ++ [.setTimer seenRetryTimer ms])
  | .rolledBack r =>
    ({ acc.1 with problem := some ("Couldn't mark notifications read: " ++ rollbackWords r) }, acc.2)
  | a => ({ acc.1 with notes := { acc.1.notes with todo := acc.1.notes.todo ++ [a] } }, acc.2)

/-- The seen key hears `e`. -/
def hearSeen (s : State) (e : SeenEv) : State × List Effect :=
  (s.notes.seen.hear e).2.foldl seenAct
    ({ s with notes := { s.notes with seen := (s.notes.seen.hear e).1 } }, [])

/-- A write's answer, as the seen key hears it. -/
def writeEv (k : Nat) (now : Nat) : WriteOutcome → SeenEv
  | .acked => .acked k
  | o@(.refused ..) => .refused k (o.describe now)
  | .lost _ => .lost k
  | .notSent => .refused k "not signed in"

/-- Whether a refresh's answer starts a new list: the first notifications, or a head page that
replaced the list rather than putting new ones on top. The view shows a new list then, at the
top (the runtime's anchor would keep the old first row still). -/
def newList (old new : Paged Notification) : Bool :=
  new.items != old.items && (old.items.isEmpty || !old.items.isSuffixOf new.items)

/-- Accounts whose notifications are left out: those the mute table shows muted (`Sky.Acts`). -/
def State.muted (s : State) (did : String) : Bool := s.acts.muted did

/-- The rows of the notifications list. -/
def State.noteGroups (s : State) : List Group := shownGroups s.muted s.notes.list.items

/-- The notifications in a page, as the acts see them: each author's follow and mute
(`Acts.seeProfile`), so Follow back and a row's menu show the server's. -/
def seeAuthors (s : State) (items : List Notification) : Acts :=
  items.foldl (fun a n => Acts.seeProfile (ctxOf s) a n.author) s.acts

/-- The rows a head page `l` put above the row at the top: the groups before the old first
group's key. -/
def freshAbove (s : State) (l : Paged Notification) : Nat :=
  match s.noteGroups.head? with
  | some g => ((shownGroups s.muted l.items).findIdx? (·.key == g.key)).getD 0
  | none => 0

/-- A `getPosts` answer: the posts, or none if it failed. -/
def postsOf : Answer → Option (List Post)
  | .reply r =>
    match Outcome.ofReply Posts.ofJson r with
    | .ok ps => some ps.posts
    | _ => none
  | .signedOut => none

/-- The answer to one of the notes' calls. A page's notifications ask for the posts their rows
show (`Notes.want`) and are seen by the acts (`seeAuthors`); `getPosts`' answer is kept and
seen by the acts like a timeline page. -/
def noteAnswer (s : State) (id : Nat) (a : Answer) : State × List Effect :=
  let n := s.notes
  if n.list.loadMore.map (·.1) = some id then
    let (page, prob) := readNotes a
    let items := (page.map (·.page.items)).getD []
    let s := { s with notes := { n.want items with
                                   list := n.list.gotLoadMore id (page.map (·.page)),
                                   moreFailed := prob.isSome },
                      acts := seeAuthors s items }
    match page.bind (·.seenAt) with
    | some t => hearSeen s (.seen (msOf t))
    | none => (s, [])
  else if n.list.refresh = some id then
    let (page, prob) := readNotes a
    let items := (page.map (·.page.items)).getD []
    let l := n.list.gotRefresh id (page.map (·.page))
    let s := { s with notes := { n.want items with
                                   list := l, pollDue := true,
                                   gen := n.gen + if newList n.list l then 1 else 0,
                                   fresh := if newList n.list l then 0 else n.fresh + freshAbove s l },
                      acts := seeAuthors s items,
                      problem := match prob with
                        | some p => some ("Couldn't load notifications: " ++ p)
                        | none => s.problem }
    match page.bind (·.seenAt) with
    | some t => hearSeen s (.seen (msOf t))
    | none => (s, [])
  else if n.postCalls.any (·.1 == id) then
    let uris := ((n.postCalls.find? (·.1 == id)).map (·.2)).getD []
    let n := { n with postCalls := n.postCalls.filter (·.1 != id) }
    match postsOf a with
    | some ps => ({ s with notes := n.gotPosts ps,
                           acts := Acts.seePage (ctxOf s) id s.acts (ps.map fun p => { post := p }) }, [])
    | none => ({ s with notes := { n with asked := n.asked.filter fun u => !uris.contains u } }, [])
  else if n.poll = some id then
    let n := { n with poll := none }
    match a with
    | .reply r =>
      match Outcome.ofReply unreadCountOf r with
      | .ok c => ({ s with notes := { n with unread := c, unreadBase := n.pollBase } }, [])
      | _ => ({ s with notes := n }, [])
    | .signedOut => ({ s with notes := n }, [])
  else
    match n.seenCalls.lookup id with
    | some c =>
      let s := { s with notes := { n with seenCalls := n.seenCalls.filter (·.1 != id), pollDue := true } }
      match c with
      | .write k => hearSeen s (writeEv k (s.now.wall / 1000).toNat (WriteOutcome.ofAnswer a))
      | .read k =>
        match (readNotes a).1 with
        | some p => hearSeen s (.read k ((p.seenAt.map msOf).getD 0))
        | none => hearSeen s (.readFailed k)
    | none => (s, [])

/-- Whether call `id` is the feed's load-more or refresh. -/
def State.feedCall (s : State) (id : Nat) : Bool :=
  s.feed.loadMore.map (·.1) == some id || s.feed.refresh == some id

/-- Whether call `id` is one of the notes' (and not the feed's). -/
def State.noteCall (s : State) (id : Nat) : Bool := s.notes.calls.contains id && !s.feedCall id

/-- The answer to call `id`: the notes', or the feed's. -/
def answerCall (s : State) (id : Nat) (a : Answer) : State × List Effect :=
  if s.noteCall id then noteAnswer s id a else onAnswer s id a

def onEvent (s : State) : Session.Event → State × List Effect
  | .signInFailed r => ({ s with problem := some (signInWords r) }, [])
  | .refreshFailed r => ({ s with problem := some ("Couldn't reach the service: " ++ describe r) }, [])
  | .signedOut .refused =>
    ({ s with problem := some "Your session ended. Sign in again." }, [])
  | .signedIn a =>
    sendOwn { s with problem := none,
                     notes := if a.did = s.notes.did then { s.notes with pollDue := true }
                              else { did := a.did, pollDue := true, gen := s.notes.gen + 1 } }
      .save (.writeFile accountPath (accountJson s.host a.handle))
  | _ => (s, [])

def handleOut (acc : State × List Effect) : Out → State × List Effect
  | .send rid _ r => (acc.1, acc.2 ++ [.request (sessionId rid) r])
  | .forget rid item =>
    ({ acc.1 with forgetting := sessionId rid :: acc.1.forgetting },
     acc.2 ++ [.request (sessionId rid) (.forgetSecret item)])
  | .cancel rid => (acc.1, acc.2 ++ [.cancelRequest (sessionId rid)])
  | .answer id a =>
    let (s, es) := answerCall acc.1 id a
    (s, acc.2 ++ es)
  | .event e => let (s, es) := onEvent acc.1 e; (s, acc.2 ++ es)

def handleOuts (s : State) (outs : List Out) : State × List Effect := outs.foldl handleOut (s, [])

/-- One input to the session, and what Sky does with everything it puts out. -/
def drive (s : State) (i : Session.Input) : State × List Effect :=
  handleOuts { s with session := (Session.step s.session i).1 } (Session.step s.session i).2

/-- Ask for the head: withdraw the load-more in flight, then call `getTimeline`. -/
def startRefresh (s : State) : State × List Effect :=
  if live s.session && s.feed.refresh.isNone then
    let (ss, es) := match s.feed.loadMore with
      | some (l, _) => withdraw s.session l
      | none => (s.session, [])
    let id := s.nextCall
    let s := { s with session := ss, nextCall := id + 1,
                      feed := { s.feed with loadMore := none, refresh := some id } }
    let (s, es') := drive s (.call id (Call.getTimeline (some pageSize)))
    (s, es ++ es')
  else (s, [])

def canLoadMore (s : State) : Bool :=
  live s.session && s.feed.loadMore.isNone && !s.feed.items.isEmpty && !s.feed.atEnd &&
    s.feed.cursor.isSome

/-- Ask for the page after the cursor the feed holds. -/
def startLoadMore (s : State) : State × List Effect :=
  match canLoadMore s, s.feed.cursor with
  | true, some c =>
    let id := s.nextCall
    drive { s with nextCall := id + 1, feed := { s.feed with loadMore := some (id, c) },
                   moreFailed := false }
      (.call id (Call.getTimeline (some pageSize) (some c)))
  | _, _ => (s, [])

/-! ## Notifications' calls -/

/-- Make session call `c` as Sky's next call id, with `f` recording it in the notes. -/
def noteCall (s : State) (f : Nat → Notes → Notes) (c : Call) : State × List Effect :=
  drive { s with nextCall := s.nextCall + 1, notes := f s.nextCall s.notes } (.call s.nextCall c)

/-- Send a write or a read the seen key asked for. A write of `v` is `updateSeen` at `v`; a read
is the first page of notifications, which says the account's `seenAt`. -/
def sendSeen (acc : State × List Effect) : Cairn.Optimistic.Act Nat → State × List Effect
  | .write k v =>
    let (s, es) := noteCall acc.1 (fun id n => { n with seenCalls := (id, .write k) :: n.seenCalls })
      (Call.updateSeen (formatDatetime v))
    (s, acc.2 ++ es)
  | .read k =>
    let (s, es) := noteCall acc.1 (fun id n => { n with seenCalls := (id, .read k) :: n.seenCalls })
      (Call.listNotifications (some 1) none)
    (s, acc.2 ++ es)
  | _ => acc

/-- Poll the unread count, unless a poll is in flight: at most one. A poll due while one is in
flight stays due and goes once that one answers (an acked seen write makes one due). -/
def startPoll (s : State) : State × List Effect :=
  if live s.session && s.notes.poll.isNone then
    noteCall s (fun id n => { n with poll := some id, pollBase := n.seen.1.entry.server,
                                     pollDue := false }) Call.getUnreadCount
  else ({ s with notes := { s.notes with pollDue := s.notes.pollDue && live s.session } }, [])

/-- Ask for the posts `uris` (at most 25) with `getPosts`. -/
def sendPosts (acc : State × List Effect) (uris : List String) : State × List Effect :=
  let (s, es) := noteCall acc.1 (fun id n => { n with postCalls := (id, uris) :: n.postCalls })
    (Call.getPosts uris)
  (s, acc.2 ++ es)

/-- Send what the notes queued in this step: the posts the rows show (25 to a call), the seen
key's writes and reads, and a poll that is due. Signed out, nothing (and `settle` empties the
notes). -/
def flushNotes (s : State) : State × List Effect :=
  if live s.session then
    let (s₀, e₀) := (chunksOf maxGetPosts s.notes.postsDue).foldl sendPosts
      ({ s with notes := { s.notes with postsDue := [] } }, [])
    let (s₁, e₁) := s₀.notes.todo.foldl sendSeen ({ s₀ with notes := { s₀.notes with todo := [] } }, [])
    if s₁.notes.pollDue then
      let (s₂, e₂) := startPoll s₁
      (s₂, e₀ ++ e₁ ++ e₂)
    else (s₁, e₀ ++ e₁)
  else (s, [])

/-- Ask for the head of the notifications. A load-more in flight is forgotten (its answer will
change nothing). -/
def startNoteRefresh (s : State) : State × List Effect :=
  if live s.session then
    match s.notes.list.beginRefresh s.nextCall with
    | some (l, _) =>
      noteCall s (fun _ n => { n with list := l }) (Call.listNotifications (some notePageSize) none)
    | none => (s, [])
  else (s, [])

/-- Whether the notifications can load more. -/
def canNoteMore (s : State) : Bool := live s.session && s.notes.list.canLoadMore

/-- Ask for the notifications after the cursor the list holds. -/
def startNoteMore (s : State) : State × List Effect :=
  if live s.session then
    match s.notes.list.beginLoadMore s.nextCall with
    | some (l, c) =>
      noteCall s (fun _ n => { n with list := l, moreFailed := false })
        (Call.listNotifications (some notePageSize) (some c))
    | none => (s, [])
  else (s, [])

/-- With the list on screen: mark seen up to the newest notification that has appeared. -/
def markSeenNow (s : State) : State × List Effect :=
  if live s.session && s.tab == .notifications then
    let (s₁, e₁) := s.notes.seen.markSeen.2.foldl seenAct
      ({ s with notes := { s.notes with seen := s.notes.seen.markSeen.1 } }, [])
    let (s₂, e₂) := flushNotes s₁
    (s₂, e₁ ++ e₂)
  else (s, [])

/-- The row with key `k` came into view: the mark moves up to its newest notification, and the
list is marked seen. Only while the list shows (an appear from a frame before Home is late). -/
def noteAppear (s : State) (k : Nat) : State × List Effect :=
  if s.tab != .notifications then (s, []) else
  match s.noteGroups.find? (·.key == k) with
  | some g =>
    markSeenNow { s with notes := { s.notes with
                                    seen := s.notes.seen.appear (newestMs g.members),
                                    fresh := min s.notes.fresh (s.noteGroups.findIdx (·.key == k)) } }
  | none => (s, [])

/-- Show the notifications: load their head, and mark seen what has appeared. -/
def openNotes (s : State) : State × List Effect :=
  let (s₁, e₁) := startNoteRefresh { s with tab := .notifications }
  let (s₂, e₂) := markSeenNow s₁
  (s₂, e₁ ++ e₂)

def signedInEvent : Out → Bool
  | .event (.signedIn _) => true
  | _ => false

/-- A session input; once signed in, load the head. -/
def driveSession (s : State) (i : Session.Input) : State × List Effect :=
  let outs := (Session.step s.session i).2
  let (s₁, e₁) := drive s i
  if outs.any signedInEvent then
    let (s₂, e₂) := startRefresh s₁
    (s₂, e₁ ++ e₂)
  else (s₁, e₁)

/-- Sign in with what the form holds; the password field is emptied in this step. -/
def signIn (s : State) : State × List Effect :=
  if ready s then
    let (s₁, e₁) := driveSession { s with password := Text.SecureField.empty passwordHint,
                                          host := serviceOf s, problem := none, slow := false }
      (.signIn (serviceOf s) (identifierOf s) s.password.text)
    (s₁, e₁ ++ [.setTimer slowTimer slowMs])
  else (s, [])

/-- Sign out (or, while signing in, stop): forget both items, and the saved account. -/
def signOut (s : State) : State × List Effect :=
  let (s₁, e₁) := driveSession { s with problem := none } .signOut
  let (s₂, e₂) := sendOwn s₁ .delete (.deleteFile accountPath)
  (s₂, e₁ ++ e₂)

/-- The service default, read at launch; then read the saved account. -/
def onReadService (s : State) (r : Cairn.Reply) : State × List Effect :=
  let s := match r with
    | .bytes b =>
      match String.fromUTF8? b with
      | some t =>
        let svc := t.trimAscii.toString
        if svc.isEmpty then s else { s with service := Text.Field.ofString svc defaultService }
      | none => s
    | _ => s
  sendOwn s .readAccount (.readFile accountPath)

/-- The saved account, read at launch: fill in the handle and resume. -/
def onReadAccount (s : State) (r : Cairn.Reply) : State × List Effect :=
  match s.session.phase, r with
  | .launched, .bytes b =>
    match parseAccount b with
    | some (svc, h) =>
      let (s₁, e₁) := driveSession { s with identifier := Text.Field.ofString h identifierHint,
                                            host := svc, slow := false } (.resume svc)
      (s₁, e₁ ++ [.setTimer slowTimer slowMs])
    | none => (s, [])
  | _, _ => (s, [])

/-! ## Images and rows -/

/-- The thumbnails a post shows: at most four. -/
def thumbsOf : Option Embed → List CairnAtproto.Image
  | some (.images is) => is.take 4
  | some (.recordWithMedia _ (.images is)) => is.take 4
  | _ => []

/-- The images a row shows: the author's avatar and the thumbnails. -/
def sourcesOf (i : FeedItem) : List String :=
  (i.post.author.avatar.toList ++ (thumbsOf i.post.embed).map (·.thumb)).eraseDups

/-- Image loads stay in flight only for rows within `span` rows of the last row that came into
view; what is known of the images within `keepSpan` rows is kept. -/
def span : Nat := 12
def keepSpan : Nat := 40

/-- The images of the rows `n` either side of row `i`. -/
def Rows.sourcesNear (r : Rows) (i n : Nat) : List String :=
  ((List.range' (i - n) (2 * n + 1)).filterMap (r.arr[·]?)).flatMap sourcesOf

/-- Load each of `srcs` that is neither known nor in flight, as Sky's own requests. -/
def loadSources (s : State) : List String → State × List Effect
  | [] => (s, [])
  | src :: rest =>
    if s.images.state src = ImageState.loading && !s.images.pending.any (·.2 == src) then
      let (im, e) := s.images.load (ownId s.nextOwn) src
      let (s', es) := loadSources { s with images := im, nextOwn := s.nextOwn + 1 } rest
      (s', e :: es)
    else loadSources s rest

/-- Row `k` came into view: load its images, cancel the loads for rows far from it, and count
the new posts above it as seen. -/
def appearRow (s : State) (k : Nat) : State × List Effect :=
  match s.rows.index? k with
  | none => (s, [])
  | some i =>
    let near := s.rows.sourcesNear i span
    let keep := s.rows.sourcesNear i keepSpan
    let (im, cs) := s.images.cancelWhere fun src => !near.contains src
    let im := { im with known := im.known.filter fun p => keep.contains p.1 }
    let (s', es) := loadSources { s with images := im, fresh := min s.fresh i }
      (match s.rows.arr[i]? with | some it => sourcesOf it | none => [])
    (s', cs ++ es)

/-- The post's page on bsky.app. -/
def postUrl (p : Post) : String :=
  "https://bsky.app/profile/" ++ p.author.handle ++ "/post/" ++ ((p.uri.splitOn "/").getLast?.getD "")

/-- Open row `k`'s post. -/
def openPost (s : State) (k : Nat) : State × List Effect :=
  match s.rows.item? k with
  | some it => sendOwn s .openPost (.openItem (postUrl it.post))
  | none => (s, [])

def receive0 (s : State) : Msg → State × List Effect
  | .reply id r =>
    match s.own.lookup id with
    | some k =>
      let s := { s with own := s.own.filter (·.1 != id) }
      match k with
      | .readService => onReadService s r
      | .readAccount => onReadAccount s r
      | _ => (s, [])
    | none =>
      if id % 2 = 0 then
        let (s₁, e₁) := driveSession { s with forgetting := s.forgetting.filter (· != id) } (.reply (id / 2) r)
        let (s₂, e₂) := flushNotes s₁
        (s₂, e₁ ++ e₂)
      else if s.images.waiting id then ({ s with images := s.images.receive id r }, [])
      else (s, [])
  | .timer n =>
    if n = slowTimer then ({ s with slow := true }, [])
    else if n = seenRetryTimer then
      let (s₁, e₁) := hearSeen s .retry
      let (s₂, e₂) := flushNotes s₁
      (s₂, e₁ ++ e₂)
    else if n = Acts.lineTimer then ({ s with acts := s.acts.clearLine, undoMute := none }, [])
    else ({ s with acts := s.acts.timer (ctxOf s) n }, [])
  | .clock t => ({ s with now := t }, [])
  | .sub _ (.evicted src) => ({ s with images := (s.images.evicted src).1 }, (s.images.evicted src).2)
  | .sub _ .tick => flushNotes { s with notes := { s.notes with pollDue := true } }
  | _ => (s, [])

/-- Signed out (no live session): the feed and the acts are emptied and every call the session
has taken on cancelled (the session's `Input.cancel`), the acts' with the rest. -/
def settle (s : State) : State × List Effect :=
  if live s.session then (s, [])
  else ({ s with feed := {}, session := (Session.step s.session (.cancel (pids s.session))).1,
                 acts := {}, undoMute := none,
                 notes := { did := s.notes.did, seen := s.notes.seen.reset, gen := s.notes.gen }, tab := .home },
        cancelEffects (Session.step s.session (.cancel (pids s.session))).2)

/-- The other first key, for a list replaced: keys from the other end of the range, so the rows of
the new list never take the keys (and the heights the runtime knew) of the old one's. -/
def altTop : Nat := 3000000000

/-- The first key of a new list: `baseTop` or `altTop`, whichever the rows aren't near. -/
def nextTop (s : State) : Nat := if 2000000000 < s.rows.top then baseTop else altTop

/-- The rows anew, for a feed replaced or emptied: a new list (a new generation, put at the top
by `dock`); every image load cancelled. -/
def restart (s : State) : State × List Effect :=
  ({ s with rows := Rows.make (nextTop s) s.feed.items, gen := s.gen + 1, fresh := 0,
            moreFailed := false, images := {} },
   s.images.pending.map fun p => .cancelRequest p.1)

/-- The rows follow the feed. Posts put on top take keys below the first (the rest keep
theirs, and count as new until they come into view); posts appended take keys after the last;
the first posts, and anything else, start a new list. Signed out, there are no rows, and no image loads. -/
def tidyRows (s : State) : State × List Effect :=
  if live s.session then
    match change s.rows.items s.feed.items with
    | .same => (s, [])
    | .prepended n =>
      if n < s.rows.top then
        ({ s with rows := Rows.make (s.rows.top - n) s.feed.items, fresh := s.fresh + n }, [])
      else restart s
    | .appended =>
      -- The first posts start a new list: the end row was the only row, so the anchor would
      -- keep it still and the list would open at its end.
      if s.rows.items.isEmpty then restart s
      else ({ s with rows := Rows.make s.rows.top s.feed.items }, [])
    | .replaced => restart s
  else
    ({ s with rows := {}, fresh := 0, moreFailed := false, images := {} },
     s.images.pending.map fun p => .cancelRequest p.1)

/-! ## The Dock badge and the lists' tops -/

/-- The feed's list. Its ref never changes: a new generation is put at the top with `scrollTo`,
and the runtime keeps the list's place while the notifications show (`App.keepScroll`). -/
def feedRef : ControlRef := ⟨14, 0⟩

/-- The notifications' list, likewise. -/
def notesRef : ControlRef := ⟨60, 0⟩

/-- The feed shows and its list hasn't been put at the top for its generation. -/
def feedAim (s : State) : Bool := live s.session && s.tab == .home && s.feedAimed != s.gen

def notesAim (s : State) : Bool := live s.session && s.tab == .notifications && s.notesAimed != s.notes.gen

/-- The end of every step: the Dock badge set to the unread count shown when it changed (and a
rise announced), and the list shown put at its top if its generation is new since it was last. -/
def dock (s : State) : State × List Effect :=
  ({ s with unreadSent := s.notes.unreadShown,
            feedAimed := if feedAim s then s.gen else s.feedAimed,
            notesAimed := if notesAim s then s.notes.gen else s.notesAimed },
   (if s.notes.unreadShown == s.unreadSent then []
    else .badge s.notes.badge ::
      (if s.unreadSent < s.notes.unreadShown then [.announce (unreadWords s.notes.unreadShown) .low] else [])) ++
   (if feedAim s then [.scrollTo feedRef .start] else []) ++
   (if notesAim s then [.scrollTo notesRef .start] else []))

/-- The rows follow the feed (`tidyRows`), then the badge and the lists' tops (`dock`). -/
def tidy (s : State) : State × List Effect :=
  ((dock (tidyRows s).1).1, (tidyRows s).2 ++ (dock (tidyRows s).1).2)

/-! ## Acts -/

/-- A feed item is hidden while its author, or the account that reposted it, shows muted. -/
def hiddenItem (s : State) (it : FeedItem) : Bool :=
  s.acts.muted it.post.author.did ||
    (match it.reason with
     | some (.repost b _) => s.acts.muted b.did
     | _ => false)

/-- The account Mute acts on from a row: the post's author; on a hidden row, the account that
hides it (the author if muted, else the reposter), which it unmutes. -/
def muteTarget (s : State) (it : FeedItem) : String :=
  if s.acts.muted it.post.author.did then it.post.author.did
  else match it.reason with
    | some (.repost b _) => if s.acts.muted b.did then b.did else it.post.author.did
    | _ => it.post.author.did

/-- Whether the row with key `k` is a post hidden by a mute (it lays at a point's height, with
no control). -/
def hiddenAt (s : State) (k : Nat) : Bool :=
  match s.rows.item? k with
  | some it => hiddenItem s it
  | none => false

/-- Whether `kind` can be pressed on the row with key `k`: signed in, a post's row that shows
(not hidden by a mute); follow and mute not on the account's own posts. -/
def canAct (s : State) (kind : Kind) (k : Nat) : Bool :=
  live s.session &&
    match s.rows.item? k with
    | none => false
    | some it =>
      !hiddenItem s it &&
      match kind with
      | .like | .repost => true
      | .follow => it.post.author.did != (ctxOf s).did
      | .mute => muteTarget s it != (ctxOf s).did

/-- The key `kind` acts on, from the row's item. -/
def actKey (s : State) (kind : Kind) (it : FeedItem) : String :=
  match kind with
  | .like | .repost => it.post.uri
  | .follow => it.post.author.did
  | .mute => muteTarget s it

/-- Press `kind` on the row with key `k`: the table shows the toggled value at once and queues
its write. -/
def actPress (s : State) (kind : Kind) (k : Nat) : State :=
  if canAct s kind k then
    match s.rows.item? k with
    | some it =>
      match kind with
      | .mute => { s with acts := s.acts.toggleMute (actKey s .mute it) }
      | _ => { s with acts := Acts.toggle (ctxOf s) s.acts kind (actKey s kind it) }
    | none => s
  else s

/-- A press of `kind` on row `k`, and what it says: a mute that hides an account offers Undo in
the status line for `lineMs` (the account in `undoMute`, and the line's timer). -/
def actStep (s : State) (kind : Kind) (k : Nat) : State × List Effect :=
  let s' := actPress s kind k
  match kind, s.rows.item? k with
  | .mute, some it =>
    if canAct s .mute k && s'.acts.muted (muteTarget s it) then
      ({ s' with undoMute := some (muteTarget s it) }, [.setTimer Acts.lineTimer lineMs])
    else (s', [])
  | _, _ => (s', [])

/-- Undo is offered: an account muted from a row, still shown muted, while signed in. -/
def canUndoMute (s : State) : Bool :=
  live s.session &&
    match s.undoMute with
    | some d => s.acts.muted d
    | none => false

/-- Undo the mute the status line offers: the account is unmuted (its posts show again in this
step), and the offer goes. -/
def undoMuteStep (s : State) : State :=
  match s.undoMute with
  | some d => if canUndoMute s then { s with acts := s.acts.toggleMute d, undoMute := none } else s
  | none => s

/-- Copy row `k`'s post's link (on bsky.app) to the clipboard. -/
def copyLink (s : State) (k : Nat) : State × List Effect :=
  match s.rows.item? k with
  | some it => (s, [.setClipboard (postUrl it.post)])
  | none => (s, [])

/-! ## Acting from the notifications -/

/-- The notifications' row with key `k`. -/
def State.noteGroup? (s : State) (k : Nat) : Option Group := s.noteGroups.find? (·.key == k)

/-- The post the row with key `k` is (a reply, mention or quote), once its view has arrived. -/
def State.notePost? (s : State) (k : Nat) : Option Post :=
  match s.noteGroup? k with
  | some g => if isPostReason g.reason then (g.members.head?).bind fun n => s.notes.post? n.uri else none
  | none => none

/-- The account a row's Follow back or menu acts on: its newest member's. -/
def State.noteAuthor? (s : State) (k : Nat) : Option Profile :=
  (s.noteGroup? k).bind fun g => g.members.head?.map (·.author)

/-- Whether `kind` can be pressed on the notifications' row with key `k`, with the
notifications showing: Like and Repost on a reply, mention or quote whose view has arrived;
Follow on such a row's menu, and as Follow back on a follow row of one account; Mute on such a
row's menu; never on the account's own. -/
def canNoteAct (s : State) (kind : Kind) (k : Nat) : Bool :=
  live s.session && s.tab == .notifications &&
    match s.noteGroup? k, s.noteAuthor? k with
    | some g, some a =>
      match kind with
      | .like | .repost => (s.notePost? k).isSome
      | .follow => (isPostReason g.reason || (g.reason == .follow && g.authors.length == 1)) &&
          a.did != (ctxOf s).did
      | .mute => isPostReason g.reason && a.did != (ctxOf s).did
    | _, _ => false

/-- Whether the notifications' row with key `k` is a post (a reply, mention or quote). -/
def State.notePostRow (s : State) (k : Nat) : Bool := (s.noteGroup? k).any (isPostReason ·.reason)

/-- A post row's menu (^78) is offered: signed in, the notifications showing. -/
def canNoteMenu (s : State) (k : Nat) : Bool :=
  live s.session && s.tab == .notifications && s.notePostRow k

/-- The key `kind` acts on from the row with key `k`: the post, or its account. -/
def noteKey (s : State) (kind : Kind) (k : Nat) : String :=
  match kind with
  | .like | .repost => ((s.notePost? k).map (·.uri)).getD ""
  | .follow | .mute => ((s.noteAuthor? k).map (·.did)).getD ""

/-- Press `kind` on the notifications' row with key `k`: the table shows the toggled value at
once and queues its write. A mute takes the account's rows away in the same step (^69). -/
def noteActStep (s : State) (kind : Kind) (k : Nat) : State :=
  if canNoteAct s kind k then
    match kind with
    | .mute => { s with acts := s.acts.toggleMute (noteKey s .mute k) }
    | _ => { s with acts := Acts.toggle (ctxOf s) s.acts kind (noteKey s kind k) }
  else s

/-- Open what the row with key `k` is about on bsky.app (`Group.url`). -/
def noteOpen (s : State) (k : Nat) : State × List Effect :=
  match s.noteGroup? k with
  | some g => sendOwn s .openPost (.openItem g.url)
  | none => (s, [])

/-- Copy the link of the post the row with key `k` is. -/
def noteCopy (s : State) (k : Nat) : State × List Effect :=
  match s.noteGroup? k with
  | some g => (s, [.setClipboard g.url])
  | none => (s, [])

/-- The list showing goes to its top: a new generation (`dock` puts it there), nothing new. -/
def feedTop (s : State) : State × List Effect := ({ s with gen := s.gen + 1, fresh := 0 }, [])

def notesTop (s : State) : State × List Effect :=
  ({ s with notes := { s.notes with gen := s.notes.gen + 1, fresh := 0 } }, [])

/-- What Sky does: the person's moves and the host's messages. -/
inductive Cmd where
  | signIn
  | loadMore
  | refresh
  | signOut
  | editIdentifier (op : TextOp)
  | editPassword (op : TextOp)
  | editService (op : TextOp)
  /-- Enter in the handle field: on to the password. -/
  | nextField
  /-- Open Bluesky's app-passwords page. -/
  | openHelp
  /-- The row with key `k` came into view. -/
  | appearRow (k : Nat)
  /-- Open the post of the row with key `k`. -/
  | openPost (k : Nat)
  /-- Show the new posts: the list starts again at the top. -/
  | showNew
  /-- Like, repost, follow or mute from the row with key `k`. -/
  | act (kind : Kind) (k : Nat)
  /-- Show the notifications; showing, back to their top. -/
  | openNotes
  /-- Show the home feed; showing, back to its top. -/
  | openHome
  /-- Refresh the notifications. -/
  | noteRefresh
  /-- Load more notifications. -/
  | noteMore
  /-- The notifications row with key `k` came into view. -/
  | noteAppear (k : Nat)
  /-- Undo the mute the status line offers. -/
  | undoMute
  /-- Copy the link of the post of the row with key `k`. -/
  | copyLink (k : Nat)
  /-- "N new" in the notifications: back to their top. -/
  | noteShowNew
  /-- Like, repost, follow or mute from the notifications' row with key `k`. -/
  | noteAct (kind : Kind) (k : Nat)
  /-- Open what the notifications' row with key `k` is about, on bsky.app. -/
  | noteOpen (k : Nat)
  /-- Copy the link of the notifications' row with key `k`. -/
  | noteCopy (k : Nat)
  | msg (m : Msg)

def step0 (s : State) : Cmd → State × List Effect
  | .signIn => signIn s
  | .loadMore => startLoadMore s
  | .refresh => startRefresh s
  | .signOut => signOut s
  | .editIdentifier op =>
    ({ s with identifier := (Text.Field.apply op s.identifier).1 }, (Text.Field.apply op s.identifier).2)
  | .editPassword op =>
    ({ s with password := (Text.SecureField.apply op s.password).1 },
     (Text.SecureField.apply op s.password).2)
  | .editService op =>
    ({ s with service := (Text.Field.apply op s.service).1 }, (Text.Field.apply op s.service).2)
  | .nextField => (s, [.focus passwordRef])
  | .openHelp => sendOwn s .openHelp (.openItem appPasswordsUrl)
  | .appearRow k => appearRow s k
  | .openPost k => openPost s k
  | .showNew => ({ s with gen := s.gen + 1, fresh := 0 }, [])
  | .act kind k => actStep s kind k
  | .undoMute => (undoMuteStep s, [])
  | .copyLink k => copyLink s k
  | .openNotes => if s.tab == .notifications then notesTop s else openNotes s
  | .openHome => if s.tab == .home then feedTop s else ({ s with tab := .home }, [])
  | .noteShowNew => notesTop s
  | .noteAct kind k => (noteActStep s kind k, [])
  | .noteOpen k => noteOpen s k
  | .noteCopy k => noteCopy s k
  | .noteRefresh => startNoteRefresh s
  | .noteMore => startNoteMore s
  | .noteAppear k => noteAppear s k
  | .msg m => receive0 s m

/-- The acts' outbox emptied: each step starts with nothing to send. -/
def clearOut (s : State) : State := { s with acts := { s.acts with outbox := [] } }

/-- Send what the acts queued: each call under a new call id, through the session (`drive`),
remembered with what it is for (`Acts.reqs`); each effect as it is. -/
def flushJobs (s : State) : List Job → State × List Effect
  | [] => (s, [])
  | .effect e :: js =>
    let r := flushJobs s js
    (r.1, e :: r.2)
  | .call q c :: js =>
    let id := s.nextCall
    let d := drive { s with nextCall := id + 1, acts := { s.acts with reqs := s.acts.reqs.insert id q } }
      (.call id c)
    let r := flushJobs d.1 js
    (r.1, d.2 ++ r.2)

/-- Send the acts' outbox, with a live session; otherwise drop it (`settle` empties the acts). -/
def flush (s : State) : State × List Effect :=
  match s.acts.outbox with
  | [] => (s, [])
  | js =>
    if live s.session then flushJobs (clearOut s) js
    else (clearOut s, [])

/-- Flush only after a step that began signed in: one that began signed out has no acts. -/
def flushIf (live₀ : Bool) (s : State) : State × List Effect := if live₀ then flush s else (s, [])

/-- The input (with the acts' outbox empty), the acts' calls sent (`flush`), then `settle`, then
the rows follow the feed (`tidy`). -/
def step1 (s : State) (i : Cmd) : State × List Effect :=
  let (s₁, e₁) := step0 (clearOut s) i
  let (s₁', e₁') := flushIf (live s.session) s₁
  let (s₂, e₂) := settle s₁'
  let (s₃, e₃) := tidy s₂
  (s₃, e₁ ++ e₁' ++ e₂ ++ e₃)

/-- The state with the password field blank. -/
def State.blank (s : State) : State := { s with password := {} }

/-- Every step. Sign in and the password field's edits see the password; every other command runs
on the state with the field blank, and the field is put back after. -/
def State.step (s : State) : Cmd → State × List Effect
  | .signIn => step1 s .signIn
  | .editPassword op => step1 s (.editPassword op)
  | c => ({ (step1 s.blank c).1 with password := s.password }, (step1 s.blank c).2)

/-- At launch: read the service default. -/
def initial : State := { own := [(ownId 0, .readService)], nextOwn := 1 }

def initEffects : List Effect := [.request (ownId 0) (.readDefault bundleId "service")]

/-- About 96 MB of decoded images. -/
def imageBudget : Nat := 96 * 1024 * 1024

/-- Signed in: the host keeps the images within `imageBudget`, and the clock ticks each minute
for the posts' times. -/
def subscriptions (s : State) : List Sub :=
  if live s.session then [.imageCache imageBudget, .every 60000] else []

end Sky
