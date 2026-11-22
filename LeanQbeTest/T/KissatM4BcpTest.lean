module

public import LeanQbe.T.Examples.Kissat.FullM4BcpProof
meta import LeanQbe.T.Examples.Kissat.FullM4BcpProof
import all Kraken.Mem
import all Kraken.Separation

/-!
# Audit & Verification for Kissat M4e Hot-Loop BCP (`FullM4Bcp*`)

1. Executable `#guard` checks on `m4Bcp_fns`, `m4BcpModule.checkAcyclic`, and `nvFastProp`
   arena geometry.
2. Source-level UNSAT soundness & `FullSparseInv` preservation checks (`nv_m4_bcp_sound_ok`,
   `XPost := False`, zero SAT proofs).
3. Single-line `#print axioms` audit (`< 115` chars) via short root aliases across all exported
   `FullM4Bcp` and `FullM4BcpProof` theorems (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatM4BcpTest

open Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.FullM4Bcp
  LeanQbe.T.Examples.Kissat.FastCore

/-! ## 1. Executable `#guard` sanity checks -/

#guard m4Bcp_fns.length == 3
#guard m4Bcp_fns.map Fn.name ==
  ["full_prop_lit_m4", "full_propagate_ignore_m4", "full_bcp_m4"]
#guard m4BcpModule.checkAcyclic == true
#guard nvFastPropBytes.length == 1760
#guard nvFastPropCfg.avail == 1760

/-! ## 2. Concrete `Mem 64` UNSAT soundness sanity check (`XPost := False`) -/

theorem nv_m4_bcp_sound_ok :
    Func.wp m4BcpEnv full_bcp_m4_body (nvFastPropCfg.hdr, ()) nvFastPropMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) ∧
        (r = 1#64 → Full.nvOneLitF0.Unsat) ∧
        ∃ s', (Full.FullMem nvFastPropCfg s' ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  nv_m4_bcp_sound

end LeanQbeTest.T.KissatM4BcpTest

/-! ## 3. Single-line `#print axioms` audit across all exported theorems -/

abbrev m4_lit_wf := @LeanQbe.T.Examples.Kissat.FullM4Bcp.full_prop_lit_m4_wf
abbrev m4_ign_wf := @LeanQbe.T.Examples.Kissat.FullM4Bcp.full_propagate_ignore_m4_wf
abbrev m4_bcp_wf := @LeanQbe.T.Examples.Kissat.FullM4Bcp.full_bcp_m4_wf
abbrev m4_fns_wf := @LeanQbe.T.Examples.Kissat.FullM4Bcp.m4Bcp_fns_wf
abbrev m4_acyclic := @LeanQbe.T.Examples.Kissat.FullM4Bcp.m4Bcp_acyclic
abbrev m4_lit_wp := @LeanQbe.T.Examples.Kissat.FullM4Bcp.full_prop_lit_m4_wp
abbrev m4_ign_wp := @LeanQbe.T.Examples.Kissat.FullM4Bcp.full_propagate_ignore_m4_wp
abbrev m4_bcp_wp := @LeanQbe.T.Examples.Kissat.FullM4Bcp.full_bcp_m4_wp
abbrev m4_sp_pres := @LeanQbe.T.Examples.Kissat.FullM4Bcp.full_bcp_m4_preserves_sparseInv
abbrev m4_noEx_t := @LeanQbe.T.Examples.Kissat.FullM4Bcp.m4BcpSpecTable_noExit
abbrev m4_noEx := @LeanQbe.T.Examples.Kissat.FullM4Bcp.m4Bcp_noExit
abbrev m4_tblImpl := @LeanQbe.T.Examples.Kissat.FullM4Bcp.m4Bcp_tableImpl
abbrev m4_modOk := @LeanQbe.T.Examples.Kissat.FullM4Bcp.m4Bcp_moduleOk
abbrev m4_nv_bcp := @LeanQbe.T.Examples.Kissat.FullM4Bcp.nv_m4_bcp_sound
abbrev m4_nv_test := @LeanQbeTest.T.KissatM4BcpTest.nv_m4_bcp_sound_ok

#print axioms m4_lit_wf
#print axioms m4_ign_wf
#print axioms m4_bcp_wf
#print axioms m4_fns_wf
#print axioms m4_acyclic
#print axioms m4_lit_wp
#print axioms m4_ign_wp
#print axioms m4_bcp_wp
#print axioms m4_sp_pres
#print axioms m4_noEx_t
#print axioms m4_noEx
#print axioms m4_tblImpl
#print axioms m4_modOk
#print axioms m4_nv_bcp
#print axioms m4_nv_test
