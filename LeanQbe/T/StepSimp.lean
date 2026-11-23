module

public meta import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# `[t_step_simp]` simp attribute for typed Kraken target backends
-/

set_option autoImplicit false

public section

register_simp_attr t_step_simp
