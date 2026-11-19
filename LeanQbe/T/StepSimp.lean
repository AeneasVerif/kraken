module

public meta import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# `[t_step_simp]` simp attribute for typed Kraken target backends (`T8`, `T9`, `T11b`)
-/

set_option autoImplicit false

public section

register_simp_attr t_step_simp
