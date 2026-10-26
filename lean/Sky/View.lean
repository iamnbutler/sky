module

public import Sky.Rows
public import Cairn.VList

/-! # The window

Signed out, the sign-in screen: handle or email, the app password (a secure field, bullets
only), a link to Bluesky's app-passwords page, the service, Sign In (a control only while it is
enabled; otherwise drawn greyed, with no control), what is happening ("Signing in…") with a
Cancel once it has taken a few seconds, and what went wrong, in words. Signed in: the home feed
(Following) in a virtual list: each post with its avatar, name, handle and time, its text
wrapped, up to four images (loaded as their rows come into view), "Reposted by" and "Replying
to", other embeds as one line and the counts; the end row loads more as it comes into view.
Refresh and Account in the header; new posts put above the reader are offered as "N new
posts". -/

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

/-- The list's ref: a new generation is a new list, at the top. -/
def listRef (s : State) : ControlRef := ⟨14, s.gen⟩

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

def avatar (s : State) (p : Profile) : Node :=
  match p.avatar with
  | some src =>
    .box { width := .fixed avatarSize, height := .fixed avatarSize, radius := avatarSize / 2,
           clip := true } none
      [Node.image { source := src, width := avatarSize, height := avatarSize,
                    state := s.images.state src }]
  | none =>
    .box { width := .fixed avatarSize, height := .fixed avatarSize, radius := avatarSize / 2,
           align := .center, justify := .center, background := some line } none
      [.text { font := { size := 16, weight := 600 }, color := white }
        ((displayName p).take 1).toString.toUpper]

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

/-- Other embeds, one line each: a link's title and domain, a quoted post, a video. -/
def embedLines : Option Embed → List String
  | some (.external e) => [(if e.title.isEmpty then e.uri else e.title) ++ " · " ++ domainOf e.uri]
  | some (.record q) => [quoteLine q]
  | some (.recordWithMedia q m) => (mediaLine m).toList ++ [quoteLine q]
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

def countsLine (p : Post) : String :=
  plural p.replyCount "reply" "replies" ++ " · " ++ plural p.repostCount "repost" "reposts" ++
    " · " ++ plural p.likeCount "like" "likes"

/-- A post: the avatar, then who and when, the text, the images, other embeds and the counts.
The whole row opens the post (^32); it tells Sky when it comes into view, to load its images. -/
def postRow (s : State) (ui : UI) (k : Nat) (it : FeedItem) : Node :=
  let p := it.post
  let r : ControlRef := ⟨32, k⟩
  .box { width := .fill, background := some (if ui.hover = some r then ⟨248, 248, 250, 255⟩ else white),
         border := ring ui r } (some { ref := r, role := .listItem, appear := true,
                                       label := "Post by @" ++ p.author.handle })
    [ .box { axis := .row, width := .fill, padding := ⟨12, 14, 12, 14⟩, gap := 10 } none
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
             (embedLines p.embed).map embedLine ++
             [textLine (countsLine p) muted 12]) ] ,
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

/-- The account panel: where the session is, and Sign out. -/
def accountPanel (s : State) (ui : UI) : List Node :=
  if s.accountOpen then
    [ .box { axis := .row, width := .fill, height := .fixed 30, gap := 8, align := .center,
             padding := ⟨0, 8, 0, 8⟩, background := some white, radius := 6 } none
        [ .box { width := .fill, height := .fixed lineH, clip := true } none
            [.text { font := { size := 12 }, color := muted } (who s ++ " on " ++ s.host)],
          button ui 11 "Sign out" 84 ] ]
  else []

/-- The new posts above the reader, when there are any (^33). -/
def newPosts (s : State) (ui : UI) : List Node :=
  if canShowNew s then
    [ .box { height := .fixed 24, padding := ⟨0, 12, 0, 12⟩, radius := 12, align := .center,
             justify := .center, background := some accent, corner := .continuous,
             border := ring ui ⟨33, 0⟩ } (some { ref := ⟨33, 0⟩, label := newPostsLabel s.fresh })
        [.text { font := { size := 12, weight := 600 }, color := white } ("↑ " ++ newPostsLabel s.fresh)] ]
  else []

/-- One line under the header, always there so the list never moves: the new posts, and what
the feed is doing or what went wrong. -/
def statusRow (s : State) (ui : UI) : Node :=
  .box { axis := .row, width := .fill, height := .fixed 24, gap := 8, align := .center } none
    (newPosts s ui ++
     [ .box { width := .fill, height := .fixed lineH, clip := true } none
        [match s.problem with
         | some p => .text { font := { size := 12 }, color := alert } p
         | none => .text { font := { size := 12 }, color := muted } (feedLine s.feed)] ])

/-- Signed in: the header (who, Refresh, Account), the account panel, the status line and the
feed's virtual list. -/
def feedView (s : State) (ui : UI) : List Node :=
  [ .box { axis := .row, width := .fill, height := .fixed 30, gap := 8, align := .center } none
      [ .text { font := { size := 17, weight := 700 }, color := ink } "Following",
        .box { width := .fill, height := .fixed lineH, clip := true } none
          [.text { font := { size := 12 }, color := muted } (who s)],
        (if canRefresh s then button ui 4 "Refresh" 84 else greyButton "Refresh" 84),
        button ui 13 (if s.accountOpen then "Done" else "Account") 84 ] ] ++
  accountPanel s ui ++
  [ statusRow s ui,
    VList.node (feedList s) ui s.rows.keys (rowOf s ui) ]

def view (s : State) (ui : UI) : Node :=
  .box { width := .fill, height := .fill, padding := ⟨pad, pad, pad, pad⟩, gap := 7,
         background := some paper, clip := true } none
    (if live s.session then feedView s ui else signInView s ui)

end Sky
