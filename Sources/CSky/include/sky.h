// Sky's Lean exports, from lean/Sky/Abi.lean. Cairn's CLean declares the
// runtime and the v1 app ABI (`cairn_app_init`, `cairn_app_step`, `cairn_app_frame`).
#pragma once
#include <stdint.h>
#include "cairn_lean.h"

// The app module's initializer, named after the package and the module.
cairn_obj *runtime_initialize_sky_Sky_Abi(uint8_t builtin);
