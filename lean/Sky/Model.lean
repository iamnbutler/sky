module

public import Sky.Feed
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
ids. The app's answer to a call (`Out.answer`) goes to the feed (`Feed.gotLoadMore`,
`Feed.gotRefresh`). Starting a refresh withdraws the load-more in flight (`withdraw`: the
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
  /-- The account panel (who is signed in, and Sign out) is open. -/
  accountOpen : Bool := false
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
deriving Repr, DecidableEq, Inhabited

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
def readPage : Answer → Option FeedPage × Option String
  | .reply r =>
    match Outcome.ofReply FeedPage.ofJson r with
    | .ok p => (some p, none)
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

/-- The answer to call `id`. -/
def onAnswer (s : State) (id : Nat) (a : Answer) : State × List Effect :=
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

def onEvent (s : State) : Session.Event → State × List Effect
  | .signInFailed r => ({ s with problem := some (signInWords r) }, [])
  | .refreshFailed r => ({ s with problem := some ("Couldn't reach the service: " ++ describe r) }, [])
  | .signedOut .refused =>
    ({ s with problem := some "Your session ended. Sign in again." }, [])
  | .signedIn a => sendOwn { s with problem := none } .save (.writeFile accountPath (accountJson s.host a.handle))
  | _ => (s, [])

def handleOut (acc : State × List Effect) : Out → State × List Effect
  | .send rid _ r => (acc.1, acc.2 ++ [.request (sessionId rid) r])
  | .forget rid item =>
    ({ acc.1 with forgetting := sessionId rid :: acc.1.forgetting },
     acc.2 ++ [.request (sessionId rid) (.forgetSecret item)])
  | .cancel rid => (acc.1, acc.2 ++ [.cancelRequest (sessionId rid)])
  | .answer id a => let (s, es) := onAnswer acc.1 id a; (s, acc.2 ++ es)
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
                                          host := serviceOf s, problem := none, accountOpen := false,
                                          slow := false }
      (.signIn (serviceOf s) (identifierOf s) s.password.text)
    (s₁, e₁ ++ [.setTimer slowTimer slowMs])
  else (s, [])

/-- Sign out (or, while signing in, stop): forget both items, and the saved account. -/
def signOut (s : State) : State × List Effect :=
  let (s₁, e₁) := driveSession { s with problem := none, accountOpen := false } .signOut
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
        driveSession { s with forgetting := s.forgetting.filter (· != id) } (.reply (id / 2) r)
      else if s.images.waiting id then ({ s with images := s.images.receive id r }, [])
      else (s, [])
  | .timer n => if n = slowTimer then ({ s with slow := true }, []) else (s, [])
  | .clock t => ({ s with now := t }, [])
  | .sub _ (.evicted src) => ({ s with images := (s.images.evicted src).1 }, (s.images.evicted src).2)
  | _ => (s, [])

/-- Signed out (no live session): the feed is emptied and every call the session has taken on
cancelled (the session's `Input.cancel`). -/
def settle (s : State) : State × List Effect :=
  if live s.session then (s, [])
  else ({ s with feed := {}, session := (Session.step s.session (.cancel (pids s.session))).1 },
        cancelEffects (Session.step s.session (.cancel (pids s.session))).2)

/-- The rows anew, for a feed replaced or emptied: a new list, at the top; every image load
cancelled. -/
def restart (s : State) : State × List Effect :=
  ({ s with rows := Rows.make baseTop s.feed.items, gen := s.gen + 1, fresh := 0,
            moreFailed := false, images := {} },
   s.images.pending.map fun p => .cancelRequest p.1)

/-- The rows follow the feed. Posts put on top take keys below the first (the rest keep
theirs, and count as new until they come into view); posts appended take keys after the last;
the first posts, and anything else, start a new list. Signed out, there are no rows, and no image loads. -/
def tidy (s : State) : State × List Effect :=
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
  /-- Open or close the account panel. -/
  | toggleAccount
  /-- The row with key `k` came into view. -/
  | appearRow (k : Nat)
  /-- Open the post of the row with key `k`. -/
  | openPost (k : Nat)
  /-- Show the new posts: the list starts again at the top. -/
  | showNew
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
  | .toggleAccount => ({ s with accountOpen := !s.accountOpen }, [])
  | .appearRow k => appearRow s k
  | .openPost k => openPost s k
  | .showNew => ({ s with gen := s.gen + 1, fresh := 0 }, [])
  | .msg m => receive0 s m

/-- The input, then `settle`, then the rows follow the feed (`tidy`). -/
def step1 (s : State) (i : Cmd) : State × List Effect :=
  let (s₁, e₁) := step0 s i
  let (s₂, e₂) := settle s₁
  let (s₃, e₃) := tidy s₂
  (s₃, e₁ ++ e₂ ++ e₃)

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
