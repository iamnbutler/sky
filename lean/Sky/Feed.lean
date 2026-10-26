module

public import CairnAtproto.Paged
public import CairnAtproto.Proofs.Paged

/-! # The feed

What Sky shows of the home timeline is cairn_atproto's paged list of timeline items
(`CairnAtproto.Paged FeedItem`, cairn#250): the items, newest first, the cursor of the last page
and whether that page was the last (`atEnd`), and the load-more and refresh in flight, each with
the app's call id (`CairnAtproto.Session.Input.call`). Items are keyed by their post's URI and
the repost that put them in the timeline (`FeedItem.key`).

The merges and what is proved of them moved to cairn_atproto with the list
(`CairnAtproto.Proofs.Paged`, `cairn_atproto^26`–`^29`): the feed stays a contiguous run of the
server's timeline, a stale load-more page changes nothing, the cursor is never lost, and a refresh
racing a load-more ends the same in either order. -/

@[expose] public section

namespace Sky
open CairnAtproto

/-- The home feed. -/
abbrev Feed := Paged FeedItem

end Sky
