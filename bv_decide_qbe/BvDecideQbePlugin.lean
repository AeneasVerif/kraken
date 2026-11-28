module

/-!
# Lightweight Native Plugin Initializer for `bv_decide_qbe` & `bv_cut_qbe`

Single-root plugin library (`precompileModules := true`, `isPlugin == true`) that initializes
`BvDecideQbe.TacticImpl` (registering `bv_decide_qbe`, `bv_decide_qbe_push`, `bv_cut_qbe`, and
`bv_decide_qbe.mode`) without exporting any `Lean.*` `.olean` imports into user files.
-/

set_option autoImplicit false

public section

namespace BvDecideQbe

@[extern "leanqbe_init_tactics"]
private opaque initTactics : IO Unit

initialize initTactics

end BvDecideQbe
