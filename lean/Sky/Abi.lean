module

public import Sky

/-! Sky's v1 exports (Cairn's docs/runtime.md), which the host calls. The host starts
the app with `runtime_initialize_sky_Sky_Abi`. -/

@[expose] public section

namespace Sky
open Cairn

/-- Core Text metrics in the running app. -/
def cfg : Runtime.Config := { metrics := TextMetrics.host }

@[export cairn_app_init]
def appInit (w h scalePercent : UInt32) : Runtime.State State :=
  Runtime.initState app cfg w h scalePercent

@[export cairn_app_step]
def appStep (s : Runtime.State State) (events : ByteArray) : Runtime.State State :=
  Runtime.stepBytes app cfg Frame.boundary s events

@[export cairn_app_frame]
def appFrame (s : Runtime.State State) : ByteArray := Runtime.frameBytes Frame.boundary s

end Sky
