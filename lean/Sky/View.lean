module

public import Sky.NoteProofs
public import Cairn.VList

/-! # The window

Signed out, the sign-in screen: handle or email, the app password (a secure field, bullets
only), a link to Bluesky's app-passwords page, the service, Sign In (a control only while it is
enabled; otherwise drawn greyed, with no control), what is happening ("Signing in…") with a
Cancel once it has taken a few seconds, and what went wrong, in words. Signed in: the home feed
(Following) in a virtual list: each post with its avatar, name, handle and time, its text
wrapped, up to four images (loaded as their rows come into view), "Reposted by" and "Replying
to", other embeds as one line and the counts; the end row loads more as it comes into view.
Refresh in the header; new posts put above the reader are offered as "N new posts". Under each
post, its replies, Repost and Like, and the ⋯ menu; Sign Out and Refresh (⌘R) in the menu bar. -/

@[expose] public section

namespace Sky
open Cairn CairnAtproto CairnAtproto.Session

def white : Color := ⟨255, 255, 255, 255⟩
def paper : Color := ⟨246, 245, 241, 255⟩
def ink : Color := ⟨28, 28, 30, 255⟩
def muted : Color := ⟨110, 110, 118, 255⟩
def line : Color := ⟨206, 206, 212, 255⟩
def accent : Color := ⟨32, 105, 224, 255⟩
def greyed : Color := ⟨188, 196, 212, 255⟩
def alert : Color := ⟨190, 40, 40, 255⟩

def pad : Nat := 16
def lineH : Nat := 18

/-- Room for the sign-in screen, and for a post with a full-width image (360 points) beside its avatar. -/
def minSize (_ : State) : Size := ⟨520, 600⟩

def textLine (t : String) (color : Color := ink) (size : Nat := 13) (weight : Nat := 400) : Node :=
  .box { width := .fill, height := .fixed lineH, clip := true, axis := .row, align := .center } none
    [.text { font := { size, weight }, color } t]

def ring (ui : UI) (r : ControlRef) (otherwise : Option Border := none) : Option Border :=
  if ui.focus = some r then some ⟨2, accent⟩ else otherwise

def button (ui : UI) (claim : Nat) (t : String) (width : Nat := 96) : Node :=
  .box { width := .fixed width, height := .fixed 30, radius := 7, align := .center,
         justify := .center, clip := true, background := some accent, corner := .continuous,
         border := ring ui ⟨claim, 0⟩ }
    (some { ref := ⟨claim, 0⟩, label := t })
    [.text { font := { size := 13, weight := 600 }, color := white } t]

/-- A button that can't be pressed now: drawn, with no control. -/
def greyButton (t : String) (width : Nat := 96) : Node :=
  .box { width := .fixed width, height := .fixed 30, radius := 7, align := .center,
         justify := .center, clip := true, background := some greyed, corner := .continuous } none
    [.text { font := { size := 13, weight := 600 }, color := white } t]

def link (ui : UI) (claim : Nat) (t : String) : Node :=
  .box { height := .fixed lineH, align := .center, border := ring ui ⟨claim, 0⟩ }
    (some { ref := ⟨claim, 0⟩, role := .link, label := t })
    [.text { font := { size := 12 }, color := accent } t]

def label (t : String) : Node := textLine t muted 12 600

def field (ui : UI) (claim : Nat) (name : String) (v : FieldView) : Node :=
  .field { width := .fill, height := .fixed 30, padding := ⟨6, 8, 6, 8⟩, background := some white,
           radius := 6, border := ring ui ⟨claim, 0⟩ (some ⟨1, line⟩) }
    { font := { size := 13 }, color := ink }
    { ref := ⟨claim, 0⟩, role := .textField, label := name } v

def canSignOut (ss : Session.State) : Bool :=
  match ss.phase with
  | .launched | .signedOut => false
  | _ => true

/-- Cancel is offered once a sign-in or resume has taken `slowMs`. -/
def offerCancel (s : State) : Bool := s.slow && canSignOut s.session && !live s.session

/-- What the session is doing while the form shows. -/
def busy (s : State) : Option String :=
  match s.session.phase with
  | .signingIn .. => some (if s.slow then "Still signing in…" else "Signing in…")
  | .refreshing _ _ none => some "Resuming your session…"
  | _ => if s.own.any (·.2 == .readAccount) || s.own.any (·.2 == .readService) then some "Starting…"
         else none

def problemLine (s : State) : List Node :=
  match s.problem with
  | some p => [.para { font := { size := 12 }, color := alert } {} p]
  | none => []

/-- The sign-in screen. -/
def signInView (s : State) (ui : UI) : List Node :=
  [ textLine "Sign in to Bluesky" ink 20 700,
    .para { font := { size := 12 }, color := muted } {}
      "Use an app password, not your account's password. Sky keeps its session in your Keychain.",
    label "Handle or email",
    field ui 6 "Handle or email" (s.identifier.view (ui.focus = some ⟨6, 0⟩)),
    label "App password",
    field ui 7 "App password" (s.password.view (ui.focus = some ⟨7, 0⟩)),
    link ui 9 "What's an app password?",
    label "Service",
    field ui 8 "Service" (s.service.view (ui.focus = some ⟨8, 0⟩)),
    .box { axis := .row, width := .fill, height := .fixed 30, gap := 10, align := .center } none
      ((if ready s then [button ui 10 "Sign in"] else [greyButton "Sign in"]) ++
       (match busy s with
        | some t => [.text { font := { size := 12 }, color := muted } t]
        | none => []) ++
       (if offerCancel s then [button ui 12 "Cancel" 80] else [])) ] ++
  problemLine s

/-! ## Times -/

def monthNames : Array String :=
  #["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

/-- The year, month (1 to 12) and day of the date `z` days after 1970-01-01 (the proleptic
Gregorian calendar; Howard Hinnant's `civil_from_days`). -/
def civilFromDays (z : Int) : Int × Nat × Nat :=
  let z := z + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (yoe + era * 400 + (if m ≤ 2 then 1 else 0), m.toNat, d.toNat)

def msPerDay : Int := 86400000

/-- When a post was written, as the feed says it: "now", "3m", "2h", then the day ("Oct 12"),
with the year if it isn't this year's. Local dates, from the runtime's clock. -/
def relTime (now : Time) (createdAt : String) : String :=
  match parseDatetime createdAt with
  | none => ""
  | some t =>
    let d := now.wall - t
    if d < 60000 then "now"
    else if d < 3600000 then s!"{d / 60000}m"
    else if d < msPerDay then s!"{d / 3600000}h"
    else
      let (y, m, day) := civilFromDays ((t + now.zone * 1000) / msPerDay)
      let (ny, _, _) := civilFromDays ((now.wall + now.zone * 1000) / msPerDay)
      let md := s!"{monthNames[m - 1]?.getD "?"} {day}"
      if y = ny then md else s!"{md}, {y}"

/-! ## The feed -/

/-- The feed list's ref (`feedRef`): the same in every state, so the runtime keeps the list's
place while the notifications show; a new generation is put at the top by `dock`. -/
def listRef (_ : State) : ControlRef := feedRef

def feedList (s : State) : VList :=
  { ref := listRef s, style := { width := .fill, height := .fill, background := some white,
                                  radius := 8, clip := true } }

def avatarSize : Nat := 40
/-- The widest an image is drawn, and the tallest. -/
def imageW : Nat := 360
def imageMaxH : Nat := 400
def tileW : Nat := 178
def tileH : Nat := 132

def displayName (p : Profile) : String :=
  match p.displayName with
  | some n => if n.trimAscii.isEmpty then p.handle else n
  | none => p.handle

/-- An account's avatar, `size` points across: its picture, or its initial on grey. -/
def avatarOf (s : State) (p : Profile) (size : Nat) : Node :=
  match p.avatar with
  | some src =>
    .box { width := .fixed size, height := .fixed size, radius := size / 2,
           clip := true } none
      [Node.image { source := src, width := size, height := size,
                    state := s.images.state src }]
  | none =>
    .box { width := .fixed size, height := .fixed size, radius := size / 2,
           align := .center, justify := .center, background := some line } none
      [.text { font := { size := size * 2 / 5, weight := 600 }, color := white }
        ((displayName p).take 1).toString.toUpper]

def avatar (s : State) (p : Profile) : Node := avatarOf s p avatarSize

/-- One image, its height from its aspect ratio (so nothing moves when it loads), capped. -/
def imageHeight (i : CairnAtproto.Image) : Nat :=
  match i.aspect with
  | some (w, h) => if w = 0 then 240 else max 80 (min imageMaxH (imageW * h / w))
  | none => 240

def thumb (s : State) (i : CairnAtproto.Image) (w h : Nat) : Node :=
  .box { width := .fixed w, height := .fixed h, radius := 6, clip := true } none
    [Node.image { source := i.thumb, width := w, height := h, state := s.images.state i.thumb }]

/-- The thumbnails: one at its aspect, or two to four in a grid of two columns. -/
def images (s : State) : List CairnAtproto.Image → List Node
  | [] => []
  | [i] => [thumb s i imageW (imageHeight i)]
  | is =>
    [.box { gap := 4 } none
      ((List.range ((is.length + 1) / 2)).map fun r =>
        .box { axis := .row, gap := 4 } none
          ((is.drop (2 * r)).take 2 |>.map fun i => thumb s i tileW tileH))]

def domainOf (uri : String) : String :=
  let rest := match uri.splitOn "://" with
    | [_, r] => r
    | _ => uri
  ((rest.splitOn "/").head?.getD rest)

def quoteLine : Quote → String
  | .post q => "Quoted post · @" ++ q.author.handle ++ (if q.text.isEmpty then "" else ": " ++ q.text)
  | .notFound _ => "Quoted post (deleted)"
  | .blocked _ => "Quoted post (blocked)"
  | .detached _ => "Quoted post (removed)"
  | .other _ => "Quoted feed or list"

def mediaLine : Media → Option String
  | .images _ => none
  | .external e => some ((if e.title.isEmpty then e.uri else e.title) ++ " · " ++ domainOf e.uri)
  | .other t => some (if (t.splitOn "video").length > 1 then "Video" else "Embedded content")

/-- What a quoted post by a muted account shows instead of itself (^42). -/
def mutedQuote : String := "Quoted post from an account you muted"

/-- A quoted post's line, unless its author is muted. -/
def quoteLineFor (s : State) : Quote → String
  | .post q => if s.acts.muted q.author.did then mutedQuote else quoteLine (.post q)
  | q => quoteLine q

/-- Other embeds, one line each: a link's title and domain, a quoted post, a video. -/
def embedLines (s : State) : Option Embed → List String
  | some (.external e) => [(if e.title.isEmpty then e.uri else e.title) ++ " · " ++ domainOf e.uri]
  | some (.record q) => [quoteLineFor s q]
  | some (.recordWithMedia q m) => (mediaLine m).toList ++ [quoteLineFor s q]
  | some (.other t) => [if (t.splitOn "video").length > 1 then "Video" else "Embedded content"]
  | _ => []

def embedLine (t : String) : Node :=
  .box { width := .fill, height := .fixed 28, padding := ⟨0, 10, 0, 10⟩, align := .start,
         justify := .center, radius := 6, border := some ⟨1, line⟩, clip := true } none
    [.text { font := { size := 12 }, color := muted } t]

/-- "Reposted by" and "Replying to". -/
def contextLines (it : FeedItem) : List Node :=
  (match it.reason with
   | some (.repost b _) => [textLine ("Reposted by " ++ displayName b) muted 12 600]
   | _ => []) ++
  (match it.reply with
   | some r => match r.parent with
     | .post p => [textLine ("Replying to @" ++ p.author.handle) muted 12]
     | _ => [textLine "Replying to a post" muted 12]
   | none => [])

def plural (n : Nat) (one many : String) : String := s!"{n} " ++ (if n = 1 then one else many)

/-! ## A post's actions

Under each post: the reply count (read only), then Repost and Like as toggles with their counts
(`checked` and `selected` are what the table shows, so VoiceOver says "selected"), then the ⋯
button (^52), whose menu has Follow or Unfollow and Mute (^39, ^40, not on the account's own
posts), Copy Link to Post (^53) and Open on bsky.app (^54). The secondary click on the post, or on
either toggle, opens the same menu. They sit outside the post's own control (^32), since a
control can't hold another. -/

/-- Follow or Unfollow, as the follows' table shows the account. -/
def followWords (following : Bool) (h : String) : String :=
  (if following then "Unfollow " else "Follow ") ++ h

/-- Mute or Unmute, as the mutes' table shows the account. -/
def muteWords (muted : Bool) (h : String) : String :=
  (if muted then "Unmute " else "Mute ") ++ h

def copyLinkWords : String := "Copy Link to Post"
def openWords : String := "Open on bsky.app"

/-- The ⋯ button's ref on row `k` (^52). -/
def moreRef (k : Nat) : ControlRef := ⟨52, k⟩

/-- A post's menu (^52): Follow or Unfollow and Mute or Unmute its author, each as the table
shows (^57), on someone else's post; then Copy Link to Post and Open on bsky.app. -/
def postMenu (s : State) (k : Nat) (it : FeedItem) : List MenuItem :=
  let h := "@" ++ it.post.author.handle
  let acct : List MenuItem :=
    (if canAct s .follow k then [.item { ref := ⟨39, k⟩, label := followWords (s.acts.following it.post.author.did) h }]
     else []) ++
    (if canAct s .mute k then [.item { ref := ⟨40, k⟩, label := muteWords (s.acts.muted (muteTarget s it)) h }]
     else [])
  acct ++ (if acct.isEmpty then [] else [.separator]) ++
    [.item { ref := ⟨53, k⟩, label := copyLinkWords }, .item { ref := ⟨54, k⟩, label := openWords }]

def plainCount (n : Nat) : String := if n = 0 then "" else s!" {n}"

/-- The Like toggle's control on row `k` (^37): checked and selected as the likes' table shows the
post (^55), with the post's menu. -/
def likeControl (s : State) (k : Nat) (it : FeedItem) : Control :=
  let on := s.acts.liked it.post.uri
  { ref := ⟨37, k⟩, label := "Like, " ++ plural (s.acts.likeCount it.post) "like" "likes",
    checked := some on, selected := on }

/-- The Repost toggle's control on row `k` (^38), as the reposts' table shows the post (^55). -/
def repostControl (s : State) (k : Nat) (it : FeedItem) : Control :=
  let on := s.acts.reposted it.post.uri
  { ref := ⟨38, k⟩, label := "Repost, " ++ plural (s.acts.repostCount it.post) "repost" "reposts",
    checked := some on, selected := on }

def likeRed : Color := ⟨214, 36, 96, 255⟩
def repostGreen : Color := ⟨22, 150, 90, 255⟩

/-- A toggle: its glyph and count, coloured when on, greyed while its write is in flight. -/
def toggle (s : State) (ui : UI) (k : Nat) (it : FeedItem) (c : Control) (glyph : String)
    (n : Nat) (onColor : Color) (busy : Bool) : Node :=
  let on := c.checked == some true
  .box { axis := .row, height := .fixed 22, align := .center, padding := ⟨0, 8, 0, 8⟩, radius := 11,
         background := if ui.hover = some c.ref then some ⟨240, 240, 244, 255⟩ else none,
         border := ring ui c.ref, menu := some { items := postMenu s k it } }
    (some c)
    [.text { font := { size := 13, weight := if on then 600 else 400 },
             color := if busy then greyed else if on then onColor else muted } (glyph ++ plainCount n)]

/-- The ⋯ button (^52): a menu button with the post's menu. -/
def moreButton (s : State) (ui : UI) (k : Nat) (it : FeedItem) : Node :=
  .box { height := .fixed 22, align := .center, justify := .center, padding := ⟨0, 8, 0, 8⟩, radius := 11,
         background := if ui.menu = some (moreRef k) || ui.hover = some (moreRef k) then some ⟨236, 236, 240, 255⟩ else none,
         border := ring ui (moreRef k),
         menu := some { items := postMenu s k it, button := true } }
    (some { ref := moreRef k, label := "More for @" ++ it.post.author.handle ++ "'s post" })
    [.text { font := { size := 14, weight := 700 }, color := muted } "⋯"]

/-- The like toggle, exactly when it can be pressed (^55: on every row that shows, signed in). -/
def likeNodes (s : State) (ui : UI) (k : Nat) (it : FeedItem) : List Node :=
  if canAct s .like k then
    [toggle s ui k it (likeControl s k it) (if s.acts.liked it.post.uri then "♥" else "♡")
      (s.acts.likeCount it.post) likeRed (s.acts.tables.likes.inFlight it.post.uri)]
  else []

def repostNodes (s : State) (ui : UI) (k : Nat) (it : FeedItem) : List Node :=
  if canAct s .repost k then
    [toggle s ui k it (repostControl s k it) "⇄" (s.acts.repostCount it.post) repostGreen
      (s.acts.tables.reposts.inFlight it.post.uri)]
  else []

/-- The row of actions: the reply count, Repost, Like and ⋯. -/
def actsRow (s : State) (ui : UI) (k : Nat) (it : FeedItem) : Node :=
  .box { axis := .row, width := .fill, height := .fixed 22, gap := 18, align := .center } none
    ([ .box { width := .fixed 64, height := .fixed 22, align := .start, justify := .center } none
         [.text { font := { size := 13 }, color := muted } ("↩" ++ plainCount it.post.replyCount)] ] ++
     repostNodes s ui k it ++ likeNodes s ui k it ++
     [ .box { width := .fill } none [], moreButton s ui k it ])

/-- A row hidden by a mute (^42): a point high, with no control and nothing of the post, so its
key stays in the list and the reader's post stays where it is (^35). A point, not zero: Cairn's
virtual list counts every row as at least a point high (`VList.model_good`). -/
def hiddenRow : Node := .box { width := .fill, height := .fixed 1, background := some white } none []

/-- A post: the avatar, then who and when, the text, the images and other embeds, which together
open the post (^32), with its menu on the secondary click, and tell Sky when they come into view,
to load the images; then the actions, outside that control, since a control can't hold
another. -/
def postRow (s : State) (ui : UI) (k : Nat) (it : FeedItem) : Node :=
  if hiddenItem s it then hiddenRow else
  let p := it.post
  let r : ControlRef := ⟨32, k⟩
  let bg : Color := if ui.hover = some r then ⟨248, 248, 250, 255⟩ else white
  .box { width := .fill, background := some bg } none
    [ .box { width := .fill, border := ring ui r, menu := some { items := postMenu s k it } }
        (some { ref := r, role := .listItem, appear := true, label := "Post by @" ++ p.author.handle })
        [ .box { axis := .row, width := .fill, padding := ⟨12, 14, 4, 14⟩, gap := 10 } none
            [ avatar s p.author,
              .box { width := .fill, gap := 5 } none
                (contextLines it ++
                 [ .box { axis := .row, width := .fill, height := .fixed lineH, gap := 6, align := .center,
                          clip := true } none
                     [ .text { font := { size := 14, weight := 600 }, color := ink } (displayName p.author),
                       .text { font := { size := 13 }, color := muted } ("@" ++ p.author.handle),
                       .text { font := { size := 13 }, color := muted } ("· " ++ relTime s.now p.createdAt) ] ] ++
                 (if p.text.isEmpty then [] else [.para { font := { size := 14 }, color := ink } {} p.text]) ++
                 images s (thumbsOf p.embed) ++
                 (embedLines s p.embed).map embedLine) ] ],
      .box { width := .fill, padding := ⟨0, 14, 8, 56⟩ } none [actsRow s ui k it],
      .box { width := .fill, height := .fixed 1, background := some line } none [] ]

def endH : Nat := 64

/-- The end of the list: loading more as it comes into view (^30), a failed load with Retry
(^31), or the end of the timeline. -/
def endRow (s : State) (ui : UI) : Node :=
  let base : Style := { width := .fill, height := .fixed endH, align := .center, justify := .center,
                        gap := 10, axis := .row }
  if canLoadMore s && !s.moreFailed then
    .box base (some { ref := ⟨30, 0⟩, role := .text, label := "Loading more posts", appear := true })
      [.text { font := { size := 13 }, color := muted } "Loading…"]
  else if canLoadMore s && s.moreFailed then
    .box base none
      [.text { font := { size := 13 }, color := alert } "Couldn't load more.",
       button ui 31 "Retry" 80]
  else
    .box base none
      [.text { font := { size := 13 }, color := muted }
        (if s.feed.loadMore.isSome || (s.feed.items.isEmpty && s.feed.refresh.isSome) then "Loading…"
         else if s.feed.atEnd then "You're all caught up."
         else if s.feed.items.isEmpty then "No posts yet."
         else "")]

/-- The row with key `k`: the end row for `0`. -/
def rowOf (s : State) (ui : UI) (k : Nat) : Node :=
  if k = 0 then endRow s ui
  else match s.rows.item? k with
    | some it => postRow s ui k it
    | none => .box { width := .fill, height := .fixed 1 } none []

def feedLine (f : Feed) : String :=
  s!"{f.items.length} posts" ++ (if f.atEnd then " · the end" else "") ++
    (if f.refresh.isSome then " · refreshing" else "") ++
    (if f.loadMore.isSome then " · loading more" else "")

def who (s : State) : String :=
  match account s.session with
  | some a => "@" ++ a.handle
  | none => ""

/-- The new posts above the reader, when there are any (^33). -/
def newPosts (s : State) (ui : UI) : List Node :=
  if canShowNew s then
    [ .box { height := .fixed 24, padding := ⟨0, 12, 0, 12⟩, radius := 12, align := .center,
             justify := .center, background := some accent, corner := .continuous,
             border := ring ui ⟨33, 0⟩ } (some { ref := ⟨33, 0⟩, label := newPostsLabel s.fresh })
        [.text { font := { size := 12, weight := 600 }, color := white } ("↑ " ++ newPostsLabel s.fresh)] ]
  else []

/-- What the status line says after a mute: the account, and Undo (^58). -/
def mutedLine (s : State) : String :=
  match s.undoMute with
  | some d => "Muted " ++ (match s.acts.handles[d]? with
      | some h => "@" ++ h
      | none => "the account") ++ ". Their posts are hidden."
  | none => ""

/-- One line under the header, always there so the list never moves: the new posts, then a
rollback said in words (for `lineMs`), or a mute just made with Undo, or what went wrong, or what
the feed is doing. -/
def statusRow (s : State) (ui : UI) : Node :=
  .box { axis := .row, width := .fill, height := .fixed 24, gap := 8, align := .center } none
    (newPosts s ui ++
     [ .box { width := .fill, height := .fixed lineH, clip := true } none
        [match s.acts.line, canUndoMute s, s.problem with
         | some l, _, _ => .text { font := { size := 12 }, color := alert } l
         | none, true, _ => .text { font := { size := 12 }, color := ink } (mutedLine s)
         | none, false, some p => .text { font := { size := 12 }, color := alert } p
         | none, false, none => .text { font := { size := 12 }, color := muted } (feedLine s.feed)] ] ++
     (if canUndoMute s then [link ui 58 "Undo"] else []))

/-! ## The notifications -/

/-- The notifications' list (`notesRef`, kept like the feed's). -/
def notesList (_ : State) : VList :=
  { ref := notesRef,
    style := { width := .fill, height := .fill, background := some white, radius := 8, clip := true } }

def unreadTint : Color := ⟨241, 246, 255, 255⟩

/-- What a row says a post did, above its text. -/
def postReasonWords : NotificationReason → String
  | .reply => "replied to you"
  | .mention => "mentioned you"
  | .quote => "quoted your post"
  | r => reasonWords r

/-- The glyph beside a group's avatars. -/
def reasonGlyph : NotificationReason → String × Color
  | .like => ("♥", likeRed)
  | .repost => ("⇄", repostGreen)
  | .follow => ("＋", accent)
  | _ => ("•", muted)

/-- The ⋯ button's ref on the notifications' row `k` (^78). -/
def noteMoreRef (k : Nat) : ControlRef := ⟨78, k⟩

/-- A reply's, mention's or quote's menu (^78): Follow or Unfollow and Mute or Unmute its author
(as the tables show), then Copy Link to Post and Open on bsky.app. -/
def noteMenu (s : State) (k : Nat) (a : Profile) : List MenuItem :=
  let h := "@" ++ a.handle
  let acct : List MenuItem :=
    (if canNoteAct s .follow k then [.item { ref := ⟨79, k⟩, label := followWords (s.acts.following a.did) h }]
     else []) ++
    (if canNoteAct s .mute k then [.item { ref := ⟨80, k⟩, label := muteWords (s.acts.muted a.did) h }]
     else [])
  acct ++ (if acct.isEmpty then [] else [.separator]) ++
    [.item { ref := ⟨81, k⟩, label := copyLinkWords }, .item { ref := ⟨82, k⟩, label := openWords }]

/-- A toggle under a notification's post, as the feed's (`toggle`), with its own menu. -/
def noteToggle (s : State) (ui : UI) (c : Control) (glyph : String) (n : Nat) (onColor : Color)
    (busy : Bool) (menu : List MenuItem) : Node :=
  let on := c.checked == some true
  .box { axis := .row, height := .fixed 22, align := .center, padding := ⟨0, 8, 0, 8⟩, radius := 11,
         background := if ui.hover = some c.ref then some ⟨240, 240, 244, 255⟩ else none,
         border := ring ui c.ref, menu := some { items := menu } }
    (some c)
    [.text { font := { size := 13, weight := if on then 600 else 400 },
             color := if busy then greyed else if on then onColor else muted } (glyph ++ plainCount n)]

/-- Like and Repost (^76, ^77) once the post's view has arrived, then ⋯ (^78). -/
def noteActs (s : State) (ui : UI) (k : Nat) (a : Profile) : Node :=
  let menu := noteMenu s k a
  let toggles : List Node := match s.notePost? k with
    | some p =>
      (if canNoteAct s .repost k then
        let on := s.acts.reposted p.uri
        [noteToggle s ui { ref := ⟨77, k⟩, label := "Repost, " ++ plural (s.acts.repostCount p) "repost" "reposts",
                           checked := some on, selected := on } "⇄" (s.acts.repostCount p) repostGreen
          (s.acts.tables.reposts.inFlight p.uri) menu] else []) ++
      (if canNoteAct s .like k then
        let on := s.acts.liked p.uri
        [noteToggle s ui { ref := ⟨76, k⟩, label := "Like, " ++ plural (s.acts.likeCount p) "like" "likes",
                           checked := some on, selected := on } (if on then "♥" else "♡") (s.acts.likeCount p) likeRed
          (s.acts.tables.likes.inFlight p.uri) menu] else [])
    | none => []
  .box { axis := .row, width := .fill, height := .fixed 22, gap := 18, align := .center } none
    (toggles ++
     [ .box { width := .fill } none [],
       .box { height := .fixed 22, align := .center, justify := .center, padding := ⟨0, 8, 0, 8⟩, radius := 11,
              background := if ui.menu = some (noteMoreRef k) || ui.hover = some (noteMoreRef k) then some ⟨236, 236, 240, 255⟩ else none,
              border := ring ui (noteMoreRef k), menu := some { items := menu, button := true } }
         (some { ref := noteMoreRef k, label := "More for @" ++ a.handle ++ "'s post" })
         [.text { font := { size := 14, weight := 700 }, color := muted } "⋯"] ])

/-- Follow back (^83) on a follow from one account: a toggle, checked as the follows' table
shows the account. -/
def followBack (s : State) (ui : UI) (k : Nat) (a : Profile) : List Node :=
  if canNoteAct s .follow k then
    let on := s.acts.following a.did
    let r : ControlRef := ⟨83, k⟩
    [ .box { height := .fixed 26, align := .center, justify := .center, padding := ⟨0, 12, 0, 12⟩, radius := 13,
             corner := .continuous, background := some (if on then white else accent),
             border := ring ui r (if on then some ⟨1, line⟩ else none) }
        (some { ref := r, label := (if on then "Following @" else "Follow back @") ++ a.handle,
                checked := some on, selected := on })
        [.text { font := { size := 12, weight := 600 },
                 color := if s.acts.tables.follows.inFlight a.did then greyed else if on then ink else white }
          (if on then "Following" else "Follow back")] ]
  else []

/-- A row of the notifications. Its control (^66) is who did what (the avatars, up to five, and
"Alice, Bob and 3 others liked your post", with the post's text), which opens it on bsky.app
and, coming into view, marks the list seen up to it. A reply, mention or quote is a post, with
Like, Repost and ⋯ under it; a follow from one account has Follow back. Unread rows are tinted,
with a dot, until marked seen: only the colour, so marking never moves the rows. -/
def noteRow (s : State) (ui : UI) (g : Group) : Node :=
  let k := g.key
  let r : ControlRef := ⟨66, k⟩
  let unseen := s.notes.seen.shown < newestMs g.members
  let bg : Color := if ui.hover = some r then ⟨248, 248, 250, 255⟩ else if unseen then unreadTint else white
  let when := match g.members.head? with
    | some n => relTime s.now n.indexedAt
    | none => ""
  let dot : Node := .box { width := .fixed 8, height := .fixed 8, radius := 4,
                           background := some (if unseen then accent else bg) } none []
  let author := (g.members.head?.map (·.author)).getD default
  let menu : Option ControlMenu := if isPostReason g.reason then some { items := noteMenu s k author } else none
  let body : List Node :=
    if isPostReason g.reason then
      [ .box { axis := .row, width := .fill, padding := ⟨12, 14, 4, 14⟩, gap := 10 } none
          [ .box { width := .fixed 8, height := .fixed avatarSize, align := .center, justify := .center } none [dot],
            avatar s author,
            .box { width := .fill, gap := 4 } none
              ([ .box { axis := .row, width := .fill, height := .fixed lineH, gap := 6, align := .center, clip := true } none
                   [ .text { font := { size := 14, weight := 600 }, color := ink } (displayName author),
                     .text { font := { size := 13 }, color := muted } ("@" ++ author.handle),
                     .text { font := { size := 13 }, color := muted } ("· " ++ when) ],
                 textLine (postReasonWords g.reason) muted 12 ] ++
               (match (g.members.head?.bind (·.text)) with
                | some t => if t.isEmpty then [] else [.para { font := { size := 14 }, color := ink } {} t]
                | none => [])) ] ]
    else
      let (glyph, gc) := reasonGlyph g.reason
      let subject : List Node := match g.subject.bind s.notes.post? with
        | some p => if p.text.isEmpty then [] else [.para { font := { size := 13 }, color := muted } {} p.text]
        | none => []
      [ .box { axis := .row, width := .fill, padding := ⟨10, 14, 10, 14⟩, gap := 10 } none
          [ .box { width := .fixed 8, height := .fixed 28, align := .center, justify := .center } none [dot],
            .box { width := .fixed 22, height := .fixed 28, align := .center, justify := .center } none
              [.text { font := { size := 16, weight := 700 }, color := gc } glyph],
            .box { width := .fill, gap := 5 } none
              ([ .box { axis := .row, height := .fixed 28, gap := 4, align := .center } none
                   ((g.authors.take 5).map fun a => avatarOf s a 28),
                 .para { font := { size := 13, weight := 500 }, color := ink } {} (g.words ++ " · " ++ when) ] ++
               subject) ] ]
  let acts : List Node :=
    if isPostReason g.reason then
      [.box { width := .fill, padding := ⟨0, 14, 8, 74⟩ } none [noteActs s ui k author]]
    else match followBack s ui k author with
      | [] => []
      | b => [.box { axis := .row, width := .fill, padding := ⟨0, 14, 10, 54⟩ } none b]
  .box { width := .fill, background := some bg } none
    ([ .box { width := .fill, border := ring ui r, menu }
         (some { ref := r, role := .listItem, appear := true, label := g.words })
         body ] ++
     acts ++
     [ .box { width := .fill, height := .fixed 1, background := some line } none [] ])

/-- The end of the notifications: loading more as it comes into view (^64), Retry after a
failure (^65), or the end. -/
def noteEndRow (s : State) (ui : UI) : Node :=
  let base : Style := { width := .fill, height := .fixed endH, align := .center, justify := .center,
                        gap := 10, axis := .row }
  if canNoteMore s && !s.notes.moreFailed then
    .box base (some { ref := ⟨64, 0⟩, role := .text, label := "Loading more notifications", appear := true })
      [.text { font := { size := 13 }, color := muted } "Loading…"]
  else if canNoteMore s && s.notes.moreFailed then
    .box base none
      [.text { font := { size := 13 }, color := alert } "Couldn't load more.",
       button ui 65 "Retry" 80]
  else
    .box base none
      [.text { font := { size := 13 }, color := muted }
        (if s.notes.list.loadMore.isSome || (s.notes.list.items.isEmpty && s.notes.list.refresh.isSome) then "Loading…"
         else if s.notes.list.items.isEmpty then "No notifications yet."
         else "That's all.")]

def noteRowOf (s : State) (ui : UI) (k : Nat) : Node :=
  if k = noteEndKey then noteEndRow s ui
  else match s.noteGroups.find? (·.key == k) with
    | some g => noteRow s ui g
    | none => .box { width := .fill, height := .fixed 1 } none []

/-- The rows' keys: one per group, then the end row's (`noteEndKey`). -/
def noteKeys (s : State) : Array Nat := (s.noteGroups.map Group.key ++ [noteEndKey]).toArray

/-- The unread count, on the Notifications tab (the Dock badge's, `Notes.badge`). -/
def notesLabel (s : State) : String :=
  match s.notes.badge with
  | some n => "Notifications · " ++ n
  | none => "Notifications"

def notesLine (s : State) : String :=
  plural s.notes.list.items.length "notification" "notifications" ++
    (if s.notes.list.refresh.isSome then " · refreshing" else "") ++
    (if s.notes.list.loadMore.isSome then " · loading more" else "")

/-- "N new" in the notifications (^75): a refresh put rows above the one at the top. -/
def canNoteShowNew (s : State) : Bool := live s.session && s.notes.fresh != 0

def newNotesLabel (n : Nat) : String := if n = 1 then "1 new notification" else s!"{n} new notifications"

/-- The notifications' status line: "N new", then a rollback said in words, what went wrong, or
what the list is doing. -/
def notesStatus (s : State) (ui : UI) : Node :=
  .box { axis := .row, width := .fill, height := .fixed 24, gap := 8, align := .center } none
    ((if canNoteShowNew s then
       [ .box { height := .fixed 24, padding := ⟨0, 12, 0, 12⟩, radius := 12, align := .center,
                justify := .center, background := some accent, corner := .continuous,
                border := ring ui ⟨75, 0⟩ } (some { ref := ⟨75, 0⟩, label := newNotesLabel s.notes.fresh })
           [.text { font := { size := 12, weight := 600 }, color := white } ("↑ " ++ newNotesLabel s.notes.fresh)] ]
      else []) ++
     [ .box { width := .fill, height := .fixed lineH, clip := true } none
         [match s.acts.line, s.problem with
          | some l, _ => .text { font := { size := 12 }, color := alert } l
          | none, some p => .text { font := { size := 12 }, color := alert } p
          | none, none => .text { font := { size := 12 }, color := muted } (notesLine s)] ])

/-- The known rows for `keys`, each hidden row (`hidden`) a point high whether laid yet or not:
`rs` is what the runtime knew, moved to the keys' indices (`VList.align`), sorted by index. -/
def hideRows (hidden : Nat → Bool) : List (Nat × Nat) → List VList.Row → List VList.Row
  | [], _ => []
  | (k, i) :: ks, rs =>
    let rs := rs.dropWhile (·.index < i)
    let here := match rs with
      | r :: _ => decide (r.index = i)
      | [] => false
    let rest := if here then rs.drop 1 else rs
    if hidden k then { index := i, key := k, height := 1 } :: hideRows hidden ks rest
    else if here then rs.take 1 ++ hideRows hidden ks rest
    else hideRows hidden ks rest

/-- What the feed's list is laid by: the runtime's record, with every row a mute hides known at
the point it lays at. A mute can hide many rows at once, each recorded taller; laid by the
record alone, the list would learn them a window at a time, a layout each, and could show a
frame laid by heights it no longer has. Known, the list is laid right in the layout after the
mute, and the record keeps the post being read still (`VList.record_keeps`, ^35). Until the
runtime settles a list however many layouts it takes (cairn#276). -/
def feedUI (s : State) (ui : UI) : UI :=
  if s.acts.tables.mutes.size == 0 then ui else
  let r := listRef s
  let keys := s.rows.keys
  let fix (k : VList.Known) : VList.Known :=
    { k with rows := (hideRows (hiddenAt s) keys.toList.zipIdx (VList.align keys k).toList).toArray,
             count := keys.size }
  { ui with lists := ui.lists.map fun (x, k) => if x == r then (x, fix k) else (x, k) }

/-- One of the two places, as a segment of the control that switches them (^61, ^62): selected
when it shows. Pressed again, it goes to the top of its list. -/
def segment (ui : UI) (claim : Nat) (label : String) (on : Bool) (count : Option String := none) : Node :=
  let r : ControlRef := ⟨claim, 0⟩
  .box { axis := .row, width := .hug, height := .fixed 26, radius := 6, align := .center,
         justify := .center, gap := 6, corner := .continuous, padding := ⟨0, 12, 0, 12⟩,
         background := if on then some white else if ui.hover = some r then some ⟨222, 222, 228, 255⟩ else none,
         border := ring ui r (if on then some ⟨1, line⟩ else none) }
    (some { ref := r, role := .tab, label := label ++ (match count with | some n => " · " ++ n | none => ""),
            selected := on })
    ([.text { font := { size := 13, weight := if on then 600 else 500 }, color := if on then ink else muted } label] ++
     (match count with
      | some n =>
        [.box { height := .fixed 16, padding := ⟨0, 6, 0, 6⟩, radius := 8, align := .center, justify := .center,
                background := some likeRed, corner := .continuous } none
          [.text { font := { size := 11, weight := 700 }, color := white } n]]
      | none => []))

/-- Home and Notifications, the unread count on the second (the Dock badge's). -/
def tabs (s : State) (ui : UI) : Node :=
  .box { axis := .row, height := .fixed 30, padding := ⟨2, 2, 2, 2⟩, gap := 2, radius := 8,
         background := some ⟨232, 232, 236, 255⟩, corner := .continuous } none
    [ segment ui 62 "Home" (s.tab == .home),
      segment ui 61 "Notifications" (s.tab == .notifications) s.notes.badge ]

/-- Signed in: the header (Home and Notifications, who, Refresh), the status line and the list
shown: the feed's, or the notifications'. Sign Out is in the app menu (^49). -/
def feedView (s : State) (ui : UI) : List Node :=
  let home := s.tab == .home
  [ .box { axis := .row, width := .fill, height := .fixed 30, gap := 8, align := .center } none
      [ tabs s ui,
        .box { width := .fill, height := .fixed lineH, clip := true, align := .center } none
          [.text { font := { size := 12 }, color := muted } (who s)],
        (if home then (if canRefresh s then button ui 4 "Refresh" 84 else greyButton "Refresh" 84)
         else (if canNoteRefresh s then button ui 63 "Refresh" 84 else greyButton "Refresh" 84)) ] ] ++
  (if home then
    [ statusRow s ui,
      VList.node (feedList s) (feedUI s ui) s.rows.keys (rowOf s ui) ]
   else
    [ notesStatus s ui,
      VList.node (notesList s) ui (noteKeys s) (noteRowOf s ui) ])

def view (s : State) (ui : UI) : Node :=
  .box { width := .fill, height := .fill, padding := ⟨pad, pad, pad, pad⟩, gap := 7,
         background := some paper, clip := true } none
    (if live s.session then feedView s ui else signInView s ui)

/-! ## The menu bar -/

def signOutRef : ControlRef := ⟨49, 0⟩
def refreshMenuRef : ControlRef := ⟨51, 0⟩
def goHomeRef : ControlRef := ⟨73, 0⟩
def goNotesRef : ControlRef := ⟨74, 0⟩

/-- Refresh, for the list shown. -/
def canRefreshShown (s : State) : Bool := if s.tab == .home then canRefresh s else canNoteRefresh s

/-- Sky's own items in the menu bar (^48): Sign Out at the top of the app menu, enabled exactly
when signed in (^56); a View menu (^50) with Refresh, ⌘R (^51), for the list shown; a Go menu
(^72) with Home, ⌘1 (^73), and Notifications, ⌘2 (^74), the one shown checked. -/
def menuBar (s : State) : List MenuItem :=
  [ .item { ref := signOutRef, label := "Sign Out" } (enabled := live s.session),
    .submenu "View" (some 50)
      [ .item { ref := refreshMenuRef, label := "Refresh" } (enabled := canRefreshShown s)
          (shortcut := some { key := .char 'r' }) ],
    .submenu "Go" (some 72)
      [ .item { ref := goHomeRef, label := "Home", checked := some (s.tab == .home) }
          (enabled := live s.session) (shortcut := some { key := .char '1' }),
        .item { ref := goNotesRef, label := "Notifications", checked := some (s.tab == .notifications) }
          (enabled := live s.session) (shortcut := some { key := .char '2' }) ] ]

end Sky
