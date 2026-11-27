module

public import LeanQbe.T.Examples.Kissat.FullM7ParityBvaTie
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7ParityBvaTie
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Compilation Guards, `Fn.Wf`, Acyclicity & Axiom Audit for `FullM7ParityBvaTie`

1. Executable `#guard` checks on `m7ParityBvaTieModule` (`3` fns, `19` externs, `0` exits),
   `FullM7Splice.patchFns` handles (`m7btBvaPickCandFn`, `m7btProbeTailFn`, `m7btProbeFn`),
   `PrintCpp`, `PrintQbe`, and 4-ISA `Fn.legal` across `.aarch64`, `.scalar64`, `.x64AVX2`,
   and `.x64AVX512`.
2. Audit-ready restated headline theorems covering `Func.Wf`, `Fn.Wf`, and `checkAcyclic`.
3. Single-line `< 115c` `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7ParityBvaTieTest

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat.FullM7ParityBvaTie

/-! ## 1. Executable `#guard` Codegen & Legalization Checks -/

#guard m7ParityBvaTie_fns.length == 3
#guard m7ParityBvaTieExterns.length == 19
#guard m7ParityBvaTieModule.checkAcyclic == true
#guard m7ParityBvaTieModule.exits.isEmpty == true
#guard m7ParityBvaTie_fns.map Fn.name ==
  [ "full_bva_pick_cand_bt", "full_probe_tail_bt", "full_probe_bt" ]
#guard m7ParityBvaTiePatchFns.map Fn.name ==
  [ "full_bva_pick_cand", "full_probe_tail_m6", "full_probe_m6" ]
#guard (ppTModule m7ParityBvaTieModule).isOk
#guard (PrintQbe.module m7ParityBvaTieModule).isOk
#guard (ppModule (m7ParityBvaTie_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7ParityBvaTie_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7ParityBvaTie_fns.map (Fn.legal .x64AVX2))).isOk
#guard m7ParityBvaTie_fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem bt_pick_wf : Func.Wf full_bva_pick_cand_bt_body := full_bva_pick_cand_bt_wf
theorem bt_tail_wf : Func.Wf full_probe_tail_bt_body := full_probe_tail_bt_wf
theorem bt_probe_wf : Func.Wf full_probe_bt_body := full_probe_bt_wf
theorem bt_fns_wf : ∀ f ∈ m7ParityBvaTie_fns, f.Wf := m7ParityBvaTie_fns_wf
theorem bt_patch_fns_wf : ∀ f ∈ m7ParityBvaTiePatchFns, f.Wf := m7ParityBvaTiePatchFns_wf
theorem bt_acyc : m7ParityBvaTieModule.checkAcyclic = true := m7ParityBvaTie_acyclic

end LeanQbeTest.T.KissatM7ParityBvaTieTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev m7bt_wf_p := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_pick_wf
abbrev m7bt_wf_t := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_tail_wf
abbrev m7bt_wf_b := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_probe_wf
abbrev m7bt_wf_all := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_fns_wf
abbrev m7bt_wf_pat := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_patch_fns_wf
abbrev m7bt_acyc := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_acyc

#print axioms m7bt_wf_p
#print axioms m7bt_wf_t
#print axioms m7bt_wf_b
#print axioms m7bt_wf_all
#print axioms m7bt_wf_pat
#print axioms m7bt_acyc
