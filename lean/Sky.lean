module

public import Cairn
public import Sky.Claims

/-! Sky: a Bluesky reader on Cairn. The headless model (`Sky.Model`: the feed, `Sky.Feed`, and
the session, cairn_atproto's), what every step keeps (`Sky.Proofs`), a bare window
(`Sky.View`) and the claims (`Sky.Claims`, `sky^N`, locked in claims.lock). Its exports are in
`Sky.Abi`. -/
