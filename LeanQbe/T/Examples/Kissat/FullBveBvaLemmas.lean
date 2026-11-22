module

public import LeanQbe.T.Examples.Kissat.FullBveBvaLemmas1
public import LeanQbe.T.Examples.Kissat.FullBveBvaLemmas2
public import LeanQbe.T.Examples.Kissat.FullBveBvaLemmas3

/-!
# Kissat `D-Full` UNSAT-Only BVE/BCE `Func.wp` Proofs (`Stage 4`, Umbrella Hub)

Re-exports the 6 assigned parametric `(Γ : Env)` `Func.wp` theorems for `full_bve_collect`,
`full_bve_mark_and`, `full_bve_gates`, `full_bve_resolve_pair`, `full_bve_weaken`, and
`full_bve_try_bce` (`Full.lean` lines 680–848, aligned 1:1 to `FullSpec3` + `#1050` weak bounds).
-/

set_option autoImplicit false

public section
