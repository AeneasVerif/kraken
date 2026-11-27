/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aProof3c
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aProof3d
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aProof3e

/-!
# Kissat Wave-4F Step-13 Callee-Parametric WP Lifts — Part 3 (`FullFidelityStep13S6aProof3`)

Thin assembly re-exporting the 3 callee-parametric `(Γ : Env)` Step-13 `Func.wp` lifts (`0`
`@[expose]`, `0` `import all`, `std3`, `XPost`-polymorphic):
1. `full_fwd_check_cl_m7_step13_wp` (`FullM7BveGates.full_fwd_check_cl_m7_body`,
   `FullM7BveGates.fullFwdCheckClM7Spec`, via `FullFidelityStep13S6aProof3d`).
2. `full_elim_bve_m7_step13_wp` (`FullFidelityBve.full_elim_bve_m7_body`,
   `FullM3CongBva.m3ElimBveSpec`, via `FullFidelityStep13S6aProof3e`).
3. `full_deduce_1uip_m6_hdr_step13_wp` (`FullFidelityBacktrackCs.fid11Deduce1uipM6HdrFn.body`,
   `FullFidelityStep11.s11Deduce1uipHdrSpec`, via `FullFidelityStep13S6aProof3c`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
