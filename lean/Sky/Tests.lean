import Sky.Fuzz
import Cairn.Runtime.ScrollProofs

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

/-- The unread count's 200. -/
def unreadReply (n : Nat) : Reply := json 200 (unreadCountJson n)

/- Launched with a service default and a saved account: the handle filled in, resume
(refreshSession, request 0), signed in, the account saved (request 5), the head (request 2, 30
posts of 100) and the unread count (request 4). -/
def resumed : State :=
  run initial [reply bootId (.bytes service.toUTF8), reply accountId (.bytes (accountJson service cfg.identifier)),
               reply 0 sessionReply, reply 2 (pageReply (page 100 30 none)), reply 5 .done,
               reply 4 (unreadReply 3)]

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
#guard resumed.notes.unread == 3 && resumed.notes.badge == some "3" && resumed.notes.poll.isNone

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
#guard (requests resumed .loadMore).any fun (id, u) => id == 6 && contains u "cursor="
#guard run more [reply 6 (pageReply (page 100 30 (some 70)))] |> fun s =>
  idxs s == (List.range 60).map (99 - ·) && s.feed.cursor == cur 40 && s.feed.loadMore.isNone

/- The end: no cursor, `atEnd`. -/
#guard run more [reply 6 (pageReply (page 100 80 (some 70)))] |> fun s =>
  idxs s == (List.range 100).map (99 - ·) && s.feed.cursor.isNone && s.feed.atEnd && !canLoadMore s

/- Refresh with load-more in flight: the load-more is cancelled (request 6); the late page
changes nothing. -/
#guard cancels more .refresh == [6]
def refreshing : State := run more [.refresh]
#guard refreshing.feed.loadMore.isNone && refreshing.feed.refresh == some 3
#guard (run refreshing [reply 6 (pageReply (page 100 30 (some 70)))]).feed == refreshing.feed

/- Refresh: five new posts on top. -/
#guard run refreshing [reply 8 (pageReply (page 105 30 none))] |> fun s =>
  idxs s == (List.range 35).map (104 - ·) && s.feed.cursor == cur 70

/- Refresh: more than a page arrived, so the feed is replaced. -/
#guard run refreshing [reply 8 (pageReply (page 200 30 none))] |> fun s =>
  idxs s == (List.range 30).map (199 - ·) && s.feed.cursor == cur 170

/- A refresh racing a load-more: either order, the same feed. -/
def racing : State := run resumed [.refresh, .loadMore]
#guard racing.feed.refresh == some 2 && racing.feed.loadMore == some (3, (cur 70).getD "")
#guard (run racing [reply 6 (pageReply (page 103 30 none)), reply 8 (pageReply (page 103 30 (some 70)))]).feed ==
       (run racing [reply 8 (pageReply (page 103 30 (some 70))), reply 6 (pageReply (page 103 30 none))]).feed

/- An expired token: the call is held, the session refreshed (request 8), the call sent again
(request 10). -/
#guard (requests more (reply 6 (err 400 "ExpiredToken" "expired"))).map (·.1) == [8]
#guard let s := run more [reply 6 (err 400 "ExpiredToken" "expired")]
  (requests s (reply 8 sessionReply)).map (·.1) == [10]

/- A refused refresh: signed out, the feed emptied, nothing in flight. -/
#guard let s := run more [reply 6 (err 400 "ExpiredToken" "expired"), reply 8 (err 400 "ExpiredToken" "revoked")]
  !live s.session && s.feed == {} && s.session.held == [] && s.session.inflight == []

/- Sign out with a load-more in flight: cancelled, both items forgotten, the account deleted. -/
#guard cancels more .signOut == [6]
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

/- Refused: the line is announced and set to clear after `lineMs`; the timer clears it. -/
#guard let r := liking.step (reply likeId (err 400 "InvalidRequest" "no"))
  (r.2.any fun | .announce t _ => some t == r.1.acts.line | _ => false) &&
  (r.2.any fun | .setTimer n ms => n == Acts.lineTimer && ms == lineMs | _ => false) &&
  (run r.1 [.msg (.timer Acts.lineTimer)]).acts.line.isNone

/- Mute: every post by the author hidden at once (their rows a point high, keeping their keys);
muteActor out; the status line offers Undo, which brings them back. -/
def muting : State := run resumed [.act .mute k1]
#guard muting.acts.muted post1.author.did && hiddenItem muting ((muting.rows.item? k1).getD default)
#guard (requests resumed (.act .mute k1)).map (contains ·.2 "muteActor") == [true]
#guard !canAct muting .mute k1 && !canAct muting .like k1 && !canOpenRow muting k1
#guard muting.rows.items.all fun it => it.post.author.did != post1.author.did || hiddenItem muting it
#guard muting.rows.keys == resumed.rows.keys
#guard canUndoMute muting && muting.undoMute == some post1.author.did
#guard (resumed.step (.act .mute k1)).2.any fun | .setTimer n _ => n == Acts.lineTimer | _ => false
#guard let u := run muting [.undoMute]
  !u.acts.muted post1.author.did && !hiddenItem u ((u.rows.item? k1).getD default) && !canUndoMute u
#guard (run muting [.msg (.timer Acts.lineTimer)]).undoMute.isNone

/- The post's menu: Follow and Mute on someone else's post, then Copy Link and Open. -/
#guard ((postMenu resumed k1 ((resumed.rows.item? k1).getD default)).filterMap fun
  | .item c .. => some c.ref.claim | _ => none) == [39, 40, 53, 54]
#guard (resumed.step (.copyLink k1)).2.any fun | .setClipboard u => u == postUrl post1 | _ => false

/- The menu bar: Sign Out enabled exactly when signed in; Refresh with ⌘R. -/
#guard MenuItem.enabledOf (menuBar resumed) signOutRef == some true
#guard MenuItem.enabledOf (menuBar initial) signOutRef == some false
#guard live (run resumed [.signOut]).session == false

/- Signed out: nothing held. -/
#guard (run liking [.signOut]).acts.isEmpty
/-! ## Notifications -/

def t0 : Nat := 1790812800000
def who (h : String) : Profile := { did := "did:plc:" ++ h, handle := h ++ ".test" }
def postP : String := "at://" ++ cfg.did ++ "/app.bsky.feed.post/p"
def notice (i : Nat) (h : String) (r : NotificationReason) (subj : Option String := none) : Notification :=
  { uri := s!"at://did:plc:{h}/x/{i}", cid := "c", author := who h, reason := r, reasonSubject := subj,
    indexedAt := formatDatetime (t0 + i * 1000) }

/-- Newest first: Bob and Alice liked the post, Carol followed, Dan replied. -/
def notesPage (cursor : Option String := none) (seenAt : Option Nat := none) : Reply :=
  json 200 ({ notifications := [notice 4 "bob" .like postP, notice 3 "alice" .like postP,
                                 notice 2 "carol" .follow, notice 1 "dan" .reply postP],
              cursor, seenAt := seenAt.map formatDatetime } : NotificationPage).toJson

def notesOpen : State := run resumed [.openNotes]

/- Notifications: the head (request 6, 30 a page); grouped, likes of one post in one row. -/
#guard (requests resumed .openNotes).any fun (id, u) => id == 6 && contains u "listNotifications?limit=30"
#guard notesOpen.tab == .notifications
def loaded : State := run notesOpen [reply 6 notesPage]
#guard loaded.noteGroups.map (·.words) ==
  ["@bob.test and @alice.test liked your post", "@carol.test followed you", "@dan.test replied to you"]
#guard loaded.notes.list.items.length == 4
/- A muted account's notifications are left out of the rows (the mute table, ^40). -/
#guard (State.noteGroups { loaded with acts := loaded.acts.toggleMute "did:plc:dan" }).map Group.words ==
  ["@bob.test and @alice.test liked your post", "@carol.test followed you"]
/- After the head, the posts the rows show are asked for in one getPosts (request 8): the
liked post and Dan's reply. -/
#guard (requests notesOpen (reply 6 notesPage)).any fun (id, u) =>
  id == 8 && contains u "getPosts" && contains u "did%3Aplc%3Adan"
/- Then the unread count is polled (request 10); at most one: the minute's tick sends
none while it is in flight. -/
#guard (requests notesOpen (reply 6 notesPage)).map (·.2) |>.any (contains · "getUnreadCount")
#guard loaded.notes.poll.isSome
#guard !((requests loaded (.msg (.sub (.every 60000) .tick))).any fun (_, u) => contains u "getUnreadCount")
/- The badge: the poll's count, then less what is marked seen. -/
def polled : State := run loaded [reply 10 (unreadReply 4)]
#guard polled.notes.badge == some "4" && polled.notes.poll.isNone
/- Seen only once on screen: nothing is marked until a row appears; the newest row appearing
marks the list seen up to it at once (the badge goes) and sends updateSeen (request 12). -/
#guard polled.notes.seen.shown == 0 && polled.notes.seen.1.mark == 0
def keyOf (s : State) (i : Nat) : Nat := (s.noteGroups[i]?.map (·.key)).getD 0
#guard (requests polled (.noteAppear (keyOf polled 0))).any fun (id, u) => id == 12 && contains u "updateSeen"
def marked : State := run polled [.noteAppear (keyOf polled 0)]
#guard marked.notes.seen.shown == t0 + 4000 && marked.notes.seen.1.mark == t0 + 4000
#guard marked.notes.badge == none
/- An older row appearing raises nothing and sends nothing. -/
#guard (requests marked (.noteAppear (keyOf marked 2))).isEmpty
#guard (run marked [.noteAppear (keyOf marked 2)]).notes.seen.1.mark == t0 + 4000
/- A row appearing from a frame before Home (late) marks nothing. -/
#guard (run polled [.openHome, .noteAppear (keyOf polled 0)]).notes.seen.1.mark == 0
/- Acknowledged: what the server holds. Refused: rolled back, in words. -/
#guard (run marked [reply 12 (json 200 (.obj []))]).notes.seen.1.entry.server == t0 + 4000
/- Acknowledged, the count is polled again: the server's own, from the new seen time. A poll due
while one is in flight goes once that one answers. -/
#guard (requests marked (reply 12 (json 200 (.obj [])))).any fun (_, u) => contains u "getUnreadCount"
#guard (run marked [reply 12 (json 200 (.obj [])), reply 14 (unreadReply 1)]).notes.badge == some "1"
#guard (run loaded [.msg (.sub (.every 60000) .tick)]).notes.pollDue &&
  (requests loaded (reply 10 (unreadReply 4)) |>.any fun (_, u) => contains u "getUnreadCount") == false &&
  ((requests (run loaded [.msg (.sub (.every 60000) .tick)]) (reply 10 (unreadReply 4))).any fun (_, u) => contains u "getUnreadCount")
#guard (run marked [reply 12 (err 400 "InvalidRequest" "no")]) |> fun s =>
  s.notes.seen.shown == 0 && (s.problem.map (contains · "Couldn't mark notifications read")).getD false
/- Lost (a timeout): read back with the first page, whose seenAt says it was applied. -/
#guard (requests marked (reply 12 (.failed .timeout "timed out"))).any fun (_, u) => contains u "listNotifications?limit=1"
/- The Dock: the poll's count goes to the badge, said once as it rises; marked seen, cleared. -/
#guard (loaded.step (reply 10 (unreadReply 4))).2.any fun | .badge b => b == some "4" | _ => false
#guard (loaded.step (reply 10 (unreadReply 4))).2.any fun
  | .announce t _ => t == "4 unread notifications" | _ => false
#guard polled.unreadSent == 4 && marked.unreadSent == 0
#guard (polled.step (.noteAppear (keyOf polled 0))).2.any fun | .badge b => b == none | _ => false
/- Follow back, on Carol's follow: the follows' table shows her followed at once. -/
#guard canNoteAct polled .follow (keyOf polled 1) && !polled.notePostRow (keyOf polled 1)
#guard (run polled [.noteAct .follow (keyOf polled 1)]).acts.following "did:plc:carol"
/- Dan's reply is a post row: Like once its view arrives (getPosts, request 8). -/
def dansPost : Post := { uri := "at://did:plc:dan/x/1", cid := "c", author := who "dan", text := "hi",
                         indexedAt := formatDatetime (t0 + 1000) }
def viewed : State := run polled [reply 8 (json 200 ({ posts := [dansPost] } : Posts).toJson)]
#guard !canNoteAct polled .like (keyOf polled 2) && canNoteAct viewed .like (keyOf viewed 2)
#guard (run viewed [.noteAct .like (keyOf viewed 2)]).acts.liked dansPost.uri
/- Muting Dan from his row's menu takes his row away in the same step (^69). -/
#guard (run viewed [.noteAct .mute (keyOf viewed 2)]).noteGroups.length == 2
/- Home and back: each list keeps its ref; pressing the tab showing puts it at its top. -/
#guard (run polled [.openHome]).tab == .home && (run polled [.openHome, .openNotes]).tab == .notifications
#guard (run polled [.openHome]).gen == polled.gen
#guard ((run polled [.openHome]).step .openHome).2.any fun
  | .scrollTo r .start => r == feedRef | _ => false
#guard (polled.step .openNotes).2.any fun | .scrollTo r .start => r == notesRef | _ => false
#guard (MenuItem.enabledOf (menuBar polled) goHomeRef) == some true

/- Signed out: no notifications, no poll, Home. -/
#guard (run polled [.signOut]) |> fun s => s.notes.list == {} && s.notes.poll.isNone && s.tab == .home

/-- ^84: the list not shown keeps its offset. Cairn's `fixUI_keeps_offset` applied to Sky's
`keptLists`, here because the runtime's proofs are not a `module` (cairn#278). -/
theorem keptOffset (s : State) (laid : Laid) (pointer : Option Point) (ui : UI) {r : ControlRef}
    (hk : r ∈ keptLists s) (hs : Cairn.Runtime.onScreen (Cairn.Runtime.scrollersOf laid) r = false) :
    (Cairn.Runtime.fixUI laid pointer ui (keptLists s)).scrollOf r = ui.scrollOf r :=
  Cairn.Runtime.fixUI_keeps_offset laid pointer ui (keptLists s) hk hs

end Sky.Tests
