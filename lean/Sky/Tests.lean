import Sky.Fuzz

/-! Sky's model, scenario by scenario, with pages of cairn_atproto's fake PDS
(`CairnAtproto.Fake`). `#guard`s, so they run whenever this builds (`make lean`, via
`Checks`). -/

namespace Sky.Tests
open Cairn CairnJson CairnAtproto Sky.FakeCheck

def service : String := cfg.service

def json (st : Nat) (j : Json) : Reply := .http st [("Content-Type", "application/json")] (encode j).toUTF8

def err (st : Nat) (name msg : String) : Reply :=
  json st (.obj [("error", .str name), ("message", .str msg)])

/-- A session call's 200, its tokens blanked as the host captures them. -/
def sessionReply : Reply := json 200 (SessionInfo.toJson { did := cfg.did, handle := cfg.identifier })

def page (len limit : Nat) (before : Option Nat) : FeedPage := Fake.page cfg len limit before

def cur (k : Nat) : Option String := some (Fake.cursorOf cfg k)

def contains (s t : String) : Bool := (s.splitOn t).length > 1

def run (s : State) (cs : List Cmd) : State := cs.foldl (fun s c => (s.step c).1) s

def reply (id : Nat) (r : Reply) : Cmd := .msg (.reply id r)

def pageReply (p : FeedPage) : Reply := json 200 p.toJson

def idxs (s : State) : List Nat := (indices s.feed).getD []

def requests (s : State) (c : Cmd) : List (Nat × String) :=
  (s.step c).2.filterMap fun
    | .request id (.http _ url ..) => some (id, url)
    | _ => none

def cancels (s : State) (c : Cmd) : List Nat :=
  (s.step c).2.filterMap fun
    | .cancelRequest id => some id
    | _ => none

def bootId : Nat := ownId 0
def accountId : Nat := ownId 1

/- Launched with a service default and a saved account: the handle filled in, resume
(refreshSession, request 0), signed in, the account saved (request 5), the head (request 2, 30
posts of 100). -/
def resumed : State :=
  run initial [reply bootId (.bytes service.toUTF8), reply accountId (.bytes (accountJson service cfg.identifier)),
               reply 0 sessionReply, reply 2 (pageReply (page 100 30 none)), reply 5 .done]

#guard initial.waiting == [bootId]
#guard (requests initial (reply bootId (.bytes service.toUTF8))).isEmpty
#guard (initial.step (reply bootId (.bytes service.toUTF8))).2.any fun
  | .request 3 (.readFile p) => p == accountPath
  | _ => false
#guard (requests (run initial [reply bootId (.bytes service.toUTF8)]) (reply accountId (.bytes (accountJson service cfg.identifier)))).map (·.1) == [0]
#guard live resumed.session
#guard resumed.identifier.textString == cfg.identifier
#guard idxs resumed == (List.range 30).map (99 - ·)
#guard resumed.feed.cursor == cur 70 && !resumed.feed.atEnd
#guard resumed.waiting == []

/- No saved account: signed out, nothing sent, the service from the default. -/
def fresh : State := run initial [reply bootId (.bytes service.toUTF8), reply accountId (.failed .notFound "")]
#guard fresh.session.phase == .launched && fresh.waiting == [] && canSignIn fresh.session
#guard serviceOf fresh == service
/- No default either: bsky.social. -/
#guard serviceOf (run initial [reply bootId (.failed .notFound ""), reply accountId (.failed .notFound "")]) == defaultService

/- A missing Keychain item at resume: signed out, both items forgotten, the handle filled in. -/
#guard let s := run initial [reply bootId (.bytes service.toUTF8),
    reply accountId (.bytes (accountJson service cfg.identifier)), reply 0 (.failed .notFound "No Keychain item")]
  !live s.session && s.feed == {} && s.waiting == [4, 2] && s.identifier.textString == cfg.identifier &&
    s.problem == some "Your session ended. Sign in again."

/- Load more: from the cursor; appended. -/
def more : State := run resumed [.loadMore]
#guard (requests resumed .loadMore).any fun (id, u) => id == 4 && contains u "cursor="
#guard run more [reply 4 (pageReply (page 100 30 (some 70)))] |> fun s =>
  idxs s == (List.range 60).map (99 - ·) && s.feed.cursor == cur 40 && s.feed.loadMore.isNone

/- The end: no cursor, `atEnd`. -/
#guard run more [reply 4 (pageReply (page 100 80 (some 70)))] |> fun s =>
  idxs s == (List.range 100).map (99 - ·) && s.feed.cursor.isNone && s.feed.atEnd && !canLoadMore s

/- Refresh with load-more in flight: the load-more is cancelled (request 4); the late page
changes nothing. -/
#guard cancels more .refresh == [4]
def refreshing : State := run more [.refresh]
#guard refreshing.feed.loadMore.isNone && refreshing.feed.refresh == some 2
#guard (run refreshing [reply 4 (pageReply (page 100 30 (some 70)))]).feed == refreshing.feed

/- Refresh: five new posts on top. -/
#guard run refreshing [reply 6 (pageReply (page 105 30 none))] |> fun s =>
  idxs s == (List.range 35).map (104 - ·) && s.feed.cursor == cur 70

/- Refresh: more than a page arrived, so the feed is replaced. -/
#guard run refreshing [reply 6 (pageReply (page 200 30 none))] |> fun s =>
  idxs s == (List.range 30).map (199 - ·) && s.feed.cursor == cur 170

/- A refresh racing a load-more: either order, the same feed. -/
def racing : State := run resumed [.refresh, .loadMore]
#guard racing.feed.refresh == some 1 && racing.feed.loadMore == some (2, (cur 70).getD "")
#guard (run racing [reply 4 (pageReply (page 103 30 none)), reply 6 (pageReply (page 103 30 (some 70)))]).feed ==
       (run racing [reply 6 (pageReply (page 103 30 (some 70))), reply 4 (pageReply (page 103 30 none))]).feed

/- An expired token: the call is held, the session refreshed (request 6), the call sent again
(request 8). -/
#guard (requests more (reply 4 (err 400 "ExpiredToken" "expired"))).map (·.1) == [6]
#guard let s := run more [reply 4 (err 400 "ExpiredToken" "expired")]
  (requests s (reply 6 sessionReply)).map (·.1) == [8]

/- A refused refresh: signed out, the feed emptied, nothing in flight. -/
#guard let s := run more [reply 4 (err 400 "ExpiredToken" "expired"), reply 6 (err 400 "ExpiredToken" "revoked")]
  !live s.session && s.feed == {} && s.session.held == [] && s.session.inflight == []

/- Sign out with a load-more in flight: cancelled, both items forgotten, the account deleted. -/
#guard cancels more .signOut == [4]
#guard (more.step .signOut).2.any fun | .request _ (.forgetSecret i) => i == accessItem | _ => false
#guard (more.step .signOut).2.any fun | .request _ (.forgetSecret i) => i == refreshItem | _ => false
#guard (more.step .signOut).2.any fun | .request _ (.deleteFile p) => p == accountPath | _ => false
#guard let s := run more [.signOut]
  s.session.phase == .signedOut && s.feed == {} && s.waiting.length == 3

/- The form: Sign in is enabled only with both fields typed in. -/
def typed : State := run fresh [.editIdentifier (.insert cfg.identifier), .editPassword (.insert cfg.password)]
#guard !ready fresh
#guard !ready (run fresh [.editIdentifier (.insert cfg.identifier)])
#guard !ready (run fresh [.editPassword (.insert cfg.password)])
#guard ready typed
#guard (typed.step .signIn).2.length == 2
/- Sign in: the password is sent once, redacted, and the field emptied in the same step. -/
#guard (typed.step .signIn).2.all fun
  | .request 0 r => r.redact && contains (String.fromUTF8! (match r with | .http _ _ _ b .. => b | _ => .empty)) cfg.password
  | .setTimer n _ => n == slowTimer
  | _ => false
#guard let s := run typed [.signIn]
  s.password.field.text == [] && s.waiting == [0] && !ready s && signingIn s.session
/- Enter in the handle field moves on to the password. -/
#guard (typed.step .nextField).2.length == 1
/- A leading @ is dropped. -/
#guard identifierOf (run fresh [.editIdentifier (.insert ("@" ++ cfg.identifier))]) == cfg.identifier

/- Refused, in words. -/
def refused (r : Reply) : Option String := (run typed [.signIn, reply 0 r]).problem
#guard refused (err 401 "AuthenticationRequired" "Invalid identifier or password") == some wrongPassword
#guard refused (err 401 "AuthFactorTokenRequired" "A sign in code has been sent") == some authFactor
#guard refused (err 429 "RateLimitExceeded" "Rate Limit Exceeded") == some rateLimited
#guard refused (.failed .network "The Internet connection appears to be offline.") == some offline
#guard (run typed [.signIn, reply 0 (err 401 "AuthenticationRequired" "no")]).session.phase == .signedOut

/- Signed in by the form: the account saved, then the head. -/
#guard let s := run typed [.signIn]
  ((s.step (reply 0 sessionReply)).2.any fun | .request _ (.writeFile p _) => p == accountPath | _ => false) &&
  live (run s [reply 0 sessionReply]).session

/- Cancelling a sign-in: it stays outstanding (so the session can forget its tokens). -/
#guard let s := run typed [.signIn, .signOut]
  s.waiting.contains 0 && !canSignIn s.session

/- Cancel is offered only once the sign-in has taken a while. -/
#guard let s := run typed [.signIn]
  !offerCancel s && (s.step .signIn).1.slow == false && offerCancel (run s [.msg (.timer slowTimer)])
#guard (run typed [.signIn]).step .signIn |>.2.isEmpty
#guard ((typed.step .signIn).2.any fun | .setTimer n _ => n == slowTimer | _ => false)

/- The link opens Bluesky's page. -/
#guard (fresh.step .openHelp).2.any fun | .request _ (.openItem u) => u == appPasswordsUrl | _ => false

/-! ## Acting (^37–^43) -/

/- The first post's row, and its post. -/
def k1 : Nat := resumed.rows.top
def post1 : Post := ((resumed.rows.item? k1).map (·.post)).getD default

/- Like: liked and counted in the same step, one putRecord out. -/
def liking : State := run resumed [.act .like k1]
#guard canAct resumed .like k1
#guard !resumed.acts.liked post1.uri && liking.acts.liked post1.uri
#guard liking.acts.likeCount post1 == resumed.acts.likeCount post1 + 1
#guard (requests resumed (.act .like k1)).map (contains ·.2 "putRecord") == [true]
def likeId : Nat := ((requests resumed (.act .like k1)).head?.map (·.1)).getD 0

/- Acknowledged: settled, liked. -/
#guard let s := run liking [reply likeId (json 200 (.obj [("uri", .str "at://x/y/z"), ("cid", .str "c")]))]
  s.acts.liked post1.uri && s.acts.tables.likes.settled post1.uri

/- Refused: shows what it did before, and says why. -/
#guard let s := run liking [reply likeId (err 400 "InvalidRequest" "no")]
  !s.acts.liked post1.uri && s.acts.line.isSome && s.acts.tables.likes.settled post1.uri

/- Lost: still liked, and read back (getRecord) before it is believed; the record missing, rolled back. -/
#guard let s := liking
  let ids := requests s (reply likeId (.failed .timeout "timed out"))
  ids.length == 1 && ids.all (contains ·.2 "getRecord") &&
    (run s [reply likeId (.failed .timeout "timed out")]).acts.liked post1.uri &&
    !(run s [reply likeId (.failed .timeout "timed out")]).acts.tables.likes.settled post1.uri &&
    (ids.head?.map fun (id, _) =>
      let t := run s [reply likeId (.failed .timeout "timed out"),
                      reply id (err 400 "RecordNotFound" "Could not locate record")]
      !t.acts.liked post1.uri && t.acts.tables.likes.settled post1.uri) == some true

/- A second press while the write is out sends nothing more, and shows not liked. -/
#guard (requests liking (.act .like k1)).isEmpty && !(run liking [.act .like k1]).acts.liked post1.uri

/- Mute: every post by the author hidden at once; muteActor out; Unmute on the row. -/
def muting : State := run resumed [.act .mute k1]
#guard muting.acts.muted post1.author.did && hiddenItem muting ((muting.rows.item? k1).getD default)
#guard (requests resumed (.act .mute k1)).map (contains ·.2 "muteActor") == [true]
#guard canAct muting .mute k1 && !canAct muting .like k1
#guard muting.rows.items.all fun it => it.post.author.did != post1.author.did || hiddenItem muting it

/- Signed out: nothing held. -/
#guard (run liking [.signOut]).acts.isEmpty

end Sky.Tests
