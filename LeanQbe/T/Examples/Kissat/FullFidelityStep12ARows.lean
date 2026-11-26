/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep12A

/-!
# Kissat Fidelity Step 12A Data-Pure Patch Barrel (`FullFidelityStep12ARows`)

Data-pure barrel (`0` `*Proof*` imports, passing `check_firewall.py --require-isa --data-proof`)
exporting the Step-12A Stage-3 P0 scaling replacement & insertion name lists and name-mapping
lemmas for `fidStep10Module`.

Proof rows (`fidStep12AReplRows`, `fidStep12ABeforeRows`), `checkCallsOk` certificates, and
parametric `SpecEntry.Impl` proofs live in `FullFidelityStep12ARowsProof.lean`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12A

open LeanQbe.T

@[expose] public section

/-- Names of the `6` signature-preserving Step-12A replacement functions. -/
def fidStep12AReplNames : List Sym :=
  [ "full_trans_sort_m6"
  , "full_m6_sweep_sim"
  , "full_m6_sweep_vars"
  , "full_factor"
  , "full_probe_m6"
  , "full_preprocess_m6" ]

/-- Empty list of inserted helper names (`0` inserted functions in Step 12A). -/
def fidStep12ABeforeNames : List Sym := []

end

public section

theorem fidStep12ARepls_map_name :
    fidStep12ARepls.map Fn.name = fidStep12AReplNames :=
  rfl

theorem fidStep12ABefores_map_name :
    (fidStep12ABefores.flatMap Prod.snd).map Fn.name = fidStep12ABeforeNames :=
  rfl

theorem fidStep12AReplNames_nodup : fidStep12AReplNames.Nodup := by decide

theorem fidStep12ABeforeNames_nodup : fidStep12ABeforeNames.Nodup := by decide

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep12A
