module

public import Sky.Feed
public import Sky.SessionFacts

/-! # Sky's model

The timeline and the session, headless. `State` is the session (`CairnAtproto.Session`), the
feed (`Sky.Feed`), the next call id, the sign-in form and the last problem. Everything Sky does
is a `Cmd` to `State.step`: the person's (sign in, load more, refresh, sign out) and the
host's (`Cairn.Msg`). Each step is the input's handling, then `settle`.

**Requests.** The session chooses its requests' ids; Sky sends session request `rid` as Cairn
request `2 * rid` (`sessionId`) and its own (the saved service, read at launch) under odd ids,
so the two never meet. Cairn 0.2.5's `Request.http` carries no Keychain secret yet (cairn#205
lands it in Cairn 0.3.0), so `toRequest` sends the method, URL, headers, body and timeout,
and the session's `forget` outputs are not sent; the next release maps both.

**Calls.** A load-more and a refresh are session calls (`Call.getTimeline`) under Sky's call
ids. The app's answer to a call (`Out.answer`) goes to the feed (`Feed.gotLoadMore`,
`Feed.gotRefresh`). Starting a refresh withdraws the load-more in flight (`withdraw`: its
request is cancelled, or, held for a token refresh, dropped), and so does a refresh whose page
replaces the feed.

**Launch.** Sky reads the service it saved (`readDefault`). With one, it resumes the session the
Keychain holds (`Input.resume`: `refreshSession`, which a missing item answers `failed
notFound`, so the session signs out); without one it stays signed out.

**Signed out** (`settle`): whenever the session isn't signed in, the feed is emptied and every
call the session has taken on is withdrawn. -/

@[expose] public section

namespace Sky
open Cairn CairnAtproto CairnAtproto.Session

/-- The defaults domain Sky reads its saved service from (the app's bundle identifier). -/
def bundleId : String := "dev.cairn.sky"

/-- Posts per page. -/
def pageSize : Nat := 30

def sessionId (rid : Nat) : Nat := 2 * rid

/-- The read of the saved service at launch. -/
def bootId : Nat := 1

def bootRequest : Request := .readDefault bundleId "service"

/-- A session request as Cairn 0.2.5 sends it (no Keychain secret yet). -/
def toRequest (h : Http) : Request :=
  .http h.method.name h.url h.headers h.body.toUTF8 h.timeoutMs

structure Login where
  service : String := "https://bsky.social"
  identifier : String := ""
  /-- Held only until the step that sends it (`signIn` clears it). -/
  password : String := ""
deriving Repr, DecidableEq, Inhabited

structure State where
  session : Session.State := Session.init
  feed : Feed := {}
  /-- The next call id. -/
  nextCall : Nat := 0
  login : Login := {}
  /-- The read of the saved service is in flight. -/
  booting : Bool := false
  /-- What went wrong last, in words. -/
  problem : Option String := none
deriving Repr, DecidableEq, Inhabited

/-! ## Reading the session -/

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

/-- The session's own request in flight (sign-in or refresh). -/
def phaseRid : Phase → List Nat
  | .signingIn rid _ => [rid]
  | .refreshing rid _ _ => [rid]
  | _ => []

/-- Every Cairn request id Sky still waits on. -/
def State.waiting (s : State) : List Nat :=
  (if s.booting then [bootId] else []) ++ s.session.inflight.map (sessionId ·.1) ++
    (phaseRid s.session.phase).map sessionId ++ s.session.abandoned.map sessionId

/-! ## Words -/

def faultWords : Fault → String
  | .notFound => "not found"
  | .denied => "denied"
  | .timeout => "timed out"
  | .network => "no connection"
  | .invalid => "invalid"
  | .other => "failed"

/-- A reply that went wrong, in words. -/
def describe : Cairn.Reply → String
  | .http st _ body =>
    let e := XrpcError.ofBody body
    let name := e.name.toString
    s!"{st}" ++ (if name.isEmpty then "" else " " ++ name) ++
      (match e.message with | some m => ": " ++ m | none => "")
  | .failed f m => faultWords f ++ (if m.isEmpty then "" else ": " ++ m)
  | _ => "an unexpected reply"

/-- A call's answer, read as a timeline page; and what went wrong, if it did. -/
def readPage : Answer → Option FeedPage × Option String
  | .reply r =>
    match Outcome.ofReply FeedPage.ofJson r with
    | .ok p => (some p, none)
    | .malformed st => (none, some s!"{st}: not a timeline page")
    | _ => (none, some (describe r))
  | .signedOut => (none, none)

/-! ## Steps -/

/-- Withdraw call `id`: in flight, its request is cancelled; held for a refresh, dropped. -/
def withdraw (ss : Session.State) (id : Nat) : Session.State × List Effect :=
  ({ ss with inflight := ss.inflight.filter (·.2.id != id), held := ss.held.filter (·.id != id) },
   (ss.inflight.filter (·.2.id == id)).map fun x => .cancelRequest (sessionId x.1))

/-- The answer to call `id`. -/
def onAnswer (s : State) (id : Nat) (a : Answer) : State × List Effect :=
  let (page, prob) := readPage a
  match s.feed.loadMore with
  | some (l, _) =>
    if l = id then
      ({ s with feed := s.feed.gotLoadMore id page,
                problem := prob.map ("Couldn't load more: " ++ ·) }, [])
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

def onEvent (s : State) : Session.Event → State
  | .signInFailed r => { s with problem := some ("Couldn't sign in: " ++ describe r) }
  | .refreshFailed r => { s with problem := some ("Couldn't reach the server: " ++ describe r) }
  | .signedOut .refused => { s with problem := some "Your session ended. Sign in again." }
  | .signedIn _ => { s with problem := none }
  | _ => s

def handleOut (acc : State × List Effect) : Out → State × List Effect
  | .send rid _ h => (acc.1, acc.2 ++ [.request (sessionId rid) (toRequest h)])
  | .forget _ _ => acc
  | .answer id a => let (s, es) := onAnswer acc.1 id a; (s, acc.2 ++ es)
  | .event e => (onEvent acc.1 e, acc.2)

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
    drive { s with nextCall := id + 1, feed := { s.feed with loadMore := some (id, c) } }
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

def signIn (s : State) : State × List Effect :=
  if canSignIn s.session then
    let l := s.login
    let (s, es) := driveSession { s with login := { l with password := "" }, problem := none }
      (.signIn l.service l.identifier l.password)
    (s, es)
  else (s, [])

def signOut (s : State) : State × List Effect := driveSession { s with problem := none } .signOut

/-- The saved service, read at launch. -/
def onBoot (s : State) (r : Cairn.Reply) : State × List Effect :=
  let s := { s with booting := false }
  match r with
  | .bytes b =>
    match String.fromUTF8? b with
    | some t =>
      let svc := t.trimAscii.toString
      if svc.isEmpty then (s, [])
      else driveSession { s with login := { s.login with service := svc } } (.resume svc)
    | none => (s, [])
  | _ => (s, [])

def receive0 (s : State) : Msg → State × List Effect
  | .reply id r =>
    if id = bootId && s.booting then onBoot s r
    else if id % 2 = 0 then driveSession s (.reply (id / 2) r)
    else (s, [])
  | _ => (s, [])

/-- Signed out (no live session): the feed is emptied and every call withdrawn. -/
def settle (s : State) : State × List Effect :=
  if live s.session then (s, [])
  else ({ s with feed := {}, session := { s.session with inflight := [], held := [] } },
        s.session.inflight.map fun x => .cancelRequest (sessionId x.1))

/-- What Sky does: the person's moves and the host's messages. -/
inductive Cmd where
  | signIn
  | loadMore
  | refresh
  | signOut
  | msg (m : Msg)

def step0 (s : State) : Cmd → State × List Effect
  | .signIn => signIn s
  | .loadMore => startLoadMore s
  | .refresh => startRefresh s
  | .signOut => signOut s
  | .msg m => receive0 s m

/-- Every step: the input, then `settle`. -/
def State.step (s : State) (i : Cmd) : State × List Effect :=
  let (s₁, e₁) := step0 s i
  let (s₂, e₂) := settle s₁
  (s₂, e₁ ++ e₂)

/-- At launch: read the saved service. -/
def initial : State := { booting := true }

def initEffects : List Effect := [.request bootId bootRequest]

end Sky
