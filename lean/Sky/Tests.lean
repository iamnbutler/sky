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

/- Launched with a saved service: resume (refreshSession, request 0), signed in, the head
(request 2, 30 posts of 100). -/
def resumed : State :=
  run initial [reply bootId (.bytes service.toUTF8), reply 0 sessionReply,
               reply 2 (pageReply (page 100 30 none))]

#guard initial.waiting == [bootId]
#guard (requests initial (reply bootId (.bytes service.toUTF8))).map (·.1) == [0]
#guard live resumed.session
#guard idxs resumed == (List.range 30).map (99 - ·)
#guard resumed.feed.cursor == cur 70 && !resumed.feed.atEnd
#guard resumed.waiting == []

/- No saved service: signed out, nothing sent. -/
#guard let s := run initial [reply bootId (.failed .notFound "")]
  s.session.phase == .launched && s.waiting == [] && canSignIn s.session

/- A missing Keychain item at resume: signed out. -/
#guard let s := run initial [reply bootId (.bytes service.toUTF8), reply 0 (.failed .notFound "No Keychain item")]
  !live s.session && s.feed == {} && s.waiting == []

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

/- Sign out with a load-more in flight: cancelled, the feed emptied. -/
#guard cancels more .signOut == [4]
#guard let s := run more [.signOut]
  s.session.phase == .signedOut && s.feed == {} && s.waiting == []

/- Sign in: the password is sent once and not kept. -/
#guard let s := run initial [reply bootId (.failed .notFound ""), .signIn]
  s.login.password == "" && s.waiting == [0]
#guard let s := run initial [reply bootId (.failed .notFound ""), .signIn, reply 0 (err 401 "AuthenticationRequired" "no")]
  s.session.phase == .signedOut && (s.problem.getD "").startsWith "Couldn't sign in"

/- Signing out while signing in: the sign-in stays outstanding (so the session can forget its
tokens), and nothing else. -/
#guard let s := run initial [reply bootId (.failed .notFound ""), .signIn, .signOut]
  s.waiting == [0] && !canSignIn s.session

end Sky.Tests
