module

public import LeanQbe.T.Examples.Kissat.FullFastCoreLemmas
meta import LeanQbe.T.Examples.Kissat.FullFastCoreLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Audit & Verification for Kissat Stage-5 Fast-Core (`FullFastCore*`)

1. Executable `#guard` checks on `fastCore_fns` (`3` fns), `fastCoreModule.checkAcyclic`,
   `[47..49]` splice into `Full.fullFns` (`fastCoreFullFns`), and concrete `nvFastProp` geometry.
2. Source-level UNSAT soundness sanity check (`nv_fast_propagate_sound_ok`, `XPost := False`,
   strictly UNSAT-only — `0` SAT model proofs).
3. Single-line `#print axioms` audit (`< 115` chars output) via short root aliases across all
   exported `FullFastCore`, `FullFastCoreBcpLemmas`, and `FullFastCoreLemmas` theorems
   (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatFastCoreTest

open Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.FastCore

/-! ## 1. Executable `#guard` sanity checks -/

#guard fastCore_fns.length == 3
#guard fastCore_fns.map Fn.name ==
  ["full_prop_lit", "full_propagate_ignore", "full_propagate"]
#guard fastCoreModule.checkAcyclic == true
#guard fastCoreFullFns.length == 166
#guard fastCoreFullModule.checkAcyclic == true
#guard ((fastCoreFullFns.drop 47).take 3).map Fn.name ==
  ["full_prop_lit", "full_propagate_ignore", "full_propagate"]
#guard nvFastPropBytes.length == 1760
#guard nvFastPropCfg.avail == 1760

/-! ## 2. Concrete `Mem 64` UNSAT soundness sanity check (`XPost := False`) -/

theorem nv_fast_propagate_sound_ok :
    Func.wp fastCoreEnv full_propagate_body (nvFastPropCfg.hdr, ()) nvFastPropMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) ∧
        (r = 1#64 → Full.nvOneLitF0.Unsat) ∧
        ∃ s', (Full.FullMem nvFastPropCfg s' ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  nv_fast_propagate_sound

end LeanQbeTest.T.KissatFastCoreTest

/-! ## 3. Single-line `#print axioms` audit across all exported theorems -/

abbrev fc_prop_lit_wf := @LeanQbe.T.Examples.Kissat.FastCore.full_prop_lit_wf
abbrev fc_prop_ign_wf := @LeanQbe.T.Examples.Kissat.FastCore.full_propagate_ignore_wf
abbrev fc_prop_wf := @LeanQbe.T.Examples.Kissat.FastCore.full_propagate_wf
abbrev fc_fns_wf := @LeanQbe.T.Examples.Kissat.FastCore.fastCore_fns_wf
abbrev fc_acyclic := @LeanQbe.T.Examples.Kissat.FastCore.fastCore_acyclic
abbrev fc_prop_lit_wp := @LeanQbe.T.Examples.Kissat.FastCore.full_prop_lit_wp
abbrev fc_prop_ign_wp := @LeanQbe.T.Examples.Kissat.FastCore.full_propagate_ignore_wp
abbrev fc_prop_wp := @LeanQbe.T.Examples.Kissat.FastCore.full_propagate_wp
abbrev fc_noExit_tbl := @LeanQbe.T.Examples.Kissat.FastCore.fastCoreSpecTable_noExit
abbrev fc_noExit := @LeanQbe.T.Examples.Kissat.FastCore.fastCore_noExit
abbrev fc_tableImpl := @LeanQbe.T.Examples.Kissat.FastCore.fastCore_tableImpl
abbrev fc_moduleOk := @LeanQbe.T.Examples.Kissat.FastCore.fastCore_moduleOk
abbrev fc_full_wf := @LeanQbe.T.Examples.Kissat.FastCore.fastCoreFull_fns_wf
abbrev fc_full_acyclic := @LeanQbe.T.Examples.Kissat.FastCore.fastCoreFull_acyclic
abbrev fc_full_tblImpl :=
  @LeanQbe.T.Examples.Kissat.FastCore.fastCore_fullEnv_tableImpl_of_missing
abbrev fc_full_modOk :=
  @LeanQbe.T.Examples.Kissat.FastCore.fastCore_fullEnv_moduleOk_of_missing
abbrev fc_full_modOk_rem :=
  @LeanQbe.T.Examples.Kissat.FastCore.fastCore_fullEnv_modOk_rem
abbrev fc_nv_mem := @LeanQbe.T.Examples.Kissat.FastCore.nvFastPropMem_ok
abbrev fc_nv_len := @LeanQbe.T.Examples.Kissat.FastCore.nvFastProp_lengths
abbrev fc_nv_wit := @LeanQbe.T.Examples.Kissat.FastCore.nvFastProp_witness
abbrev fc_nv_prop := @LeanQbe.T.Examples.Kissat.FastCore.nv_fast_propagate_sound
abbrev fc_nv_test := @LeanQbeTest.T.KissatFastCoreTest.nv_fast_propagate_sound_ok

#print axioms fc_prop_lit_wf
#print axioms fc_prop_ign_wf
#print axioms fc_prop_wf
#print axioms fc_fns_wf
#print axioms fc_acyclic
#print axioms fc_prop_lit_wp
#print axioms fc_prop_ign_wp
#print axioms fc_prop_wp
#print axioms fc_noExit_tbl
#print axioms fc_noExit
#print axioms fc_tableImpl
#print axioms fc_moduleOk
#print axioms fc_full_wf
#print axioms fc_full_acyclic
#print axioms fc_full_tblImpl
#print axioms fc_full_modOk
#print axioms fc_full_modOk_rem
#print axioms fc_nv_mem
#print axioms fc_nv_len
#print axioms fc_nv_wit
#print axioms fc_nv_prop
#print axioms fc_nv_test
