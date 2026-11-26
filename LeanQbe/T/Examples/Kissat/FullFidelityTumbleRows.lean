/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityTumble

/-!
# Kissat Fidelity Step 11 PR 2 Data-Pure Patch Barrel (`FullFidelityTumbleRows`)

Data-pure barrel (`0` `*Proof*` imports, passing `check_firewall.py --require-isa --data-proof`)
exporting the Step-11 PR 2 (`S11-3` Lazy Activation + `1 - 1/k` Scores + `S11-5` True `tumble`
Variable Renaming + `LUCKY_EXT`) replacement & insertion lists and their well-formedness proofs
for direct plug-in to `FullFidelityAssemblyStep11.lean`.

Proof rows (`fidStep11TumReplRows`, `fidStep11TumBeforeRows`) and `SpecEntry.Impl` proofs live
in the companion proof module `FullFidelityTumbleRowsProof.lean`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityTumble

open LeanQbe.T

@[expose] public section

/-- Names of the `6` sig-preserving PR 2 replacement functions. -/
def fidStep11TumReplNames : List Sym :=
  [ "full_zero_tables2"
  , "full_init_hdr"
  , "full_ingest_cl"
  , "full_parse_body_m6"
  , "full_extend"
  , "full_lucky_scan" ]

/-- Names of the `5` inserted PR 2 helper functions. -/
def fidStep11TumBeforeNames : List Sym :=
  [ "full_activate_lit_fid"
  , "full_tumble_finish_fid"
  , "full_extend_core_fid"
  , "full_unperm_fid"
  , "full_lucky_ord_fid" ]

end

public section

theorem fidStep11TumRepls_map_name :
    fidStep11TumRepls.map Fn.name = fidStep11TumReplNames :=
  rfl

theorem fidStep11TumBefores_map_name :
    (fidStep11TumBefores.flatMap Prod.snd).map Fn.name = fidStep11TumBeforeNames :=
  rfl

theorem fidStep11TumReplNames_nodup : fidStep11TumReplNames.Nodup := by decide

theorem fidStep11TumBeforeNames_nodup : fidStep11TumBeforeNames.Nodup := by decide

end

end LeanQbe.T.Examples.Kissat.FullFidelityTumble
