module

public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM6BcpS15
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Audit & Verification for Kissat M6 Delayed-Watch BCP (`FullM6BcpS15*`)

1. Executable `#guard` checks on `m6BcpS15_fns` (`4` fns), signatures, `checkAcyclic`,
   `PrintCpp`, `PrintQbe`, and `Fn.legal` across `.aarch64`, `.scalar64`, `.x64AVX2`.
2. UNSAT soundness, `FullSparseInv` preservation, and concrete `Mem 64` non-vacuity check
   (`nv_m6_bcp_s15_sound_ok`, `XPost := False`, zero SAT proofs).
3. Single-line `#print axioms` audit via short root aliases across all exported
   `FullM6BcpS15*` theorems (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM6BcpS15Test

open Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.FullM6BcpS15
  LeanQbe.T.Examples.Kissat.FastCore

/-! ## 1. Executable `#guard` sanity & codegen checks -/

#guard m6BcpS15_fns.length == 4
#guard m6BcpS15_fns.map Fn.name ==
  ["full_prop_lit_ovf_s15", "full_prop_lit_raw_s15", "full_propagate_ignore_s15", "full_bcp_s15"]
#guard full_prop_lit_ovf_s15.as == [i64, i32, i64, i64, i64, i64]
#guard full_prop_lit_ovf_s15.rs == [Ty.bool]
#guard full_prop_lit_raw_s15.as == [i64, i32, i64]
#guard full_prop_lit_raw_s15.rs == [Ty.bool]
#guard full_propagate_ignore_s15.as == [i64, i64]
#guard full_propagate_ignore_s15.rs == [i64]
#guard full_bcp_s15.as == [i64]
#guard full_bcp_s15.rs == [i64]
#guard m6BcpS15Module.checkAcyclic == true
#guard (ppTModule m6BcpS15Module).isOk
#guard (PrintQbe.module m6BcpS15Module).isOk
#guard (ppModule (m6BcpS15_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m6BcpS15_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m6BcpS15_fns.map (Fn.legal .x64AVX2))).isOk

/-! ## 2. Concrete `Mem 64` UNSAT soundness sanity check (`XPost := False`) -/

theorem nv_m6_bcp_s15_sound_ok :
    Func.wp m6BcpS15Env full_bcp_s15_body (nvFastPropCfg.hdr, ()) nvFastPropMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) ∧
        (r = 1#64 → Full.nvOneLitF0.Unsat) ∧
        ∃ s', (Full.FullMem nvFastPropCfg s' ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  nv_m6_bcp_s15_sound

end LeanQbeTest.T.KissatM6BcpS15Test

/-! ## 3. Single-line `#print axioms` audit across all exported theorems -/

abbrev s15_ovf_wf := @LeanQbe.T.Examples.Kissat.FullM6BcpS15.full_prop_lit_ovf_s15_wf
abbrev s15_raw_wf := @LeanQbe.T.Examples.Kissat.FullM6BcpS15.full_prop_lit_raw_s15_wf
abbrev s15_ign_wf := @LeanQbe.T.Examples.Kissat.FullM6BcpS15.full_propagate_ignore_s15_wf
abbrev s15_bcp_wf := @LeanQbe.T.Examples.Kissat.FullM6BcpS15.full_bcp_s15_wf
abbrev s15_fns_wf := @LeanQbe.T.Examples.Kissat.FullM6BcpS15.m6BcpS15_fns_wf
abbrev s15_acyc := @LeanQbe.T.Examples.Kissat.FullM6BcpS15.m6BcpS15_acyclic
abbrev s15_ovf_wp := @LeanQbe.T.Examples.Kissat.FullM6BcpS15.full_prop_lit_ovf_s15_wp
abbrev s15_raw_wp := @LeanQbe.T.Examples.Kissat.FullM6BcpS15.full_prop_lit_raw_s15_wp
abbrev s15_dcap0 := @LeanQbe.T.Examples.Kissat.FullM6BcpS15.full_prop_lit_raw_s15_wp_canon_dcap0
abbrev s15_ign_wp := @LeanQbe.T.Examples.Kissat.FullM6BcpS15.full_propagate_ignore_s15_wp
abbrev s15_bcp_wp := @LeanQbe.T.Examples.Kissat.FullM6BcpS15.full_bcp_s15_wp
abbrev s15_sp_pr := @LeanQbe.T.Examples.Kissat.FullM6BcpS15.full_bcp_s15_preserves_sparseInv
abbrev s15_noEx_t := @LeanQbe.T.Examples.Kissat.FullM6BcpS15.m6BcpS15SpecTable_noExit
abbrev s15_noEx := @LeanQbe.T.Examples.Kissat.FullM6BcpS15.m6BcpS15_noExit
abbrev s15_tbl := @LeanQbe.T.Examples.Kissat.FullM6BcpS15.m6BcpS15_tableImpl
abbrev s15_modOk := @LeanQbe.T.Examples.Kissat.FullM6BcpS15.m6BcpS15_moduleOk
abbrev s15_nv_bcp := @LeanQbe.T.Examples.Kissat.FullM6BcpS15.nv_m6_bcp_s15_sound
abbrev s15_nv_tst := @LeanQbeTest.T.KissatM6BcpS15Test.nv_m6_bcp_s15_sound_ok

#print axioms s15_ovf_wf
#print axioms s15_raw_wf
#print axioms s15_ign_wf
#print axioms s15_bcp_wf
#print axioms s15_fns_wf
#print axioms s15_acyc
#print axioms s15_ovf_wp
#print axioms s15_raw_wp
#print axioms s15_dcap0
#print axioms s15_ign_wp
#print axioms s15_bcp_wp
#print axioms s15_sp_pr
#print axioms s15_noEx_t
#print axioms s15_noEx
#print axioms s15_tbl
#print axioms s15_modOk
#print axioms s15_nv_bcp
#print axioms s15_nv_tst
