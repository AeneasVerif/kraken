/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7BcpHot
public import LeanQbe.T.Examples.Kissat.FullM7BcpHotProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7BcpHot
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Backend Guards, and Axiom Audit (`FullM7BcpHot`)

1. Executable `#guard` checks on `m7BcpHotModule` (`4` fns, `3` externs, `7` spec rows, `0` exits),
   `checkAcyclic = true`, drop-in handles (`m7PropLitOvfFn`, `m7PropChronoFn`, `m7PropIgnoreFn`,
   `m7PropFn`), `PrintCpp`, `PrintQbe`, and `Fn.legal` across `.aarch64`, `.scalar64`,
   `.x64AVX2`, and `.x64AVX512`.
2. Restated headline theorems for `m7BcpHot_fns_wf`, `full_propagate_canon_wf`,
   `m7BcpHot_acyclic`, `m7BcpHotEnv_noExit`, all `5` parametric WP specs
   (`full_prop_lit_ovf_hot_wp`, `full_prop_chrono_hot_wp`, `full_propagate_ignore_hot_wp`,
   `full_bcp_hot_wp`, `m7PropFn_wp`), `m7BcpHot_moduleOk`, and concrete `Mem 64` UNSAT
   non-vacuity (`nv_m7_bcp_hot`, `XPost := False`).
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7BcpHotTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM7BcpHot

/-! ## 1. Module Structure, Backend Printers, and 4-ISA Legalization Guards -/

#guard m7BcpHotModule.checkAcyclic == true
#guard m7BcpHotModule.exits.isEmpty == true
#guard m7BcpHot_fns.length == 4
#guard m7BcpHotModule.externs.length == 3
#guard m7PropLitOvfFn.name == "full_prop_lit_ovf_hot"
#guard m7PropChronoFn.name == "full_prop_chrono_hot"
#guard m7PropIgnoreFn.name == "full_propagate_ignore"
#guard m7PropFn.name == "full_propagate"
#guard (m7BcpHotModule.externs.map Extern.name) ==
  ["full_wstack_defrag", "full_unwatch_large", "full_watch_push"]
#guard (ppTModule m7BcpHotModule).isOk
#guard (PrintQbe.module m7BcpHotModule).isOk
#guard (ppModule (m7BcpHot_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7BcpHot_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7BcpHot_fns.map (Fn.legal .x64AVX2))).isOk
#guard m7BcpHot_fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard (Fn.legal .x64AVX512 m7PropFn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

section AuditSpec

theorem m7bh_wf : ∀ f ∈ m7BcpHot_fns, f.Wf := m7BcpHot_fns_wf
theorem m7bh_canon_wf : Func.Wf FullM7BcpHot.full_propagate_body := full_propagate_canon_wf
theorem m7bh_acyc : m7BcpHotModule.checkAcyclic = true := m7BcpHot_acyclic
theorem m7bh_tbl_len : m7BcpHotSpecTable.length = 7 := m7BcpHotSpecTable_length
theorem m7bh_tbl_nx : ∀ e ∈ m7BcpHotSpecTable, e.noExit = true := m7BcpHotSpecTable_noExit
theorem m7bh_nd : (m7BcpHotSpecTable.map SpecEntry.name).Nodup := m7BcpHotSpecTable_nodup

theorem m7bh_no_exit :
    ∀ f as bs xs m Q X X',
      m7BcpHotEnv f as bs xs m Q X → m7BcpHotEnv f as bs xs m Q X' :=
  m7BcpHotEnv_noExit

theorem m7bh_ovf_wp (Γ : Env)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullPropLitOvfHotSpec a m Q X →
      Func.wp Γ full_prop_lit_ovf_hot_body a m Q X :=
  full_prop_lit_ovf_hot_wp Γ hPush

theorem m7bh_chrono_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hUnw : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullPropChronoHotSpec a m Q X →
      Func.wp Γ full_prop_chrono_hot_body a m Q X :=
  full_prop_chrono_hot_wp Γ hDefrag hUnw hPush

theorem m7bh_prop_ign_wp (Γ : Env)
    (hOvf : ∀ a m Q X, fullPropLitOvfHotSpec a m Q X →
      Γ "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool] a m Q X)
    (hChrono : ∀ a m Q X, fullPropChronoHotSpec a m Q X →
      Γ "full_prop_chrono_hot" [i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, FullPropDecSpecs.fullPropagateIgnoreSpec a m Q X →
      Func.wp Γ full_propagate_ignore_hot_body a m Q X :=
  full_propagate_ignore_hot_wp Γ hOvf hChrono

theorem m7bh_bcp_wp (Γ : Env)
    (hPropIgn : ∀ a m Q X, FullPropDecSpecs.fullPropagateIgnoreSpec a m Q X →
      Γ "full_propagate_ignore_hot" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullPropDecSpecs.fullPropagateSpec a m Q X →
      Func.wp Γ full_bcp_hot_body a m Q X :=
  full_bcp_hot_wp Γ hPropIgn

theorem m7bh_prop_wp (Γ : Env)
    (hPropIgn : ∀ a m Q X, FullPropDecSpecs.fullPropagateIgnoreSpec a m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullPropDecSpecs.fullPropagateSpec a m Q X →
      Func.wp Γ m7PropFn.body a m Q X :=
  m7PropFn_wp Γ hPropIgn

theorem m7bh_mod_ok : ModuleOk m7BcpHotEnv m7BcpHotModule := m7BcpHot_moduleOk

theorem m7bh_nv :
    Func.wp m7BcpHotEnv full_bcp_hot_body (FastCore.nvFastPropCfg.hdr, ())
      FastCore.nvFastPropMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) ∧
        (r = 1#64 → Full.nvOneLitF0.Unsat) ∧
        ∃ s', (FullMem FastCore.nvFastPropCfg s' ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  nv_m7_bcp_hot

end AuditSpec

end LeanQbeTest.T.KissatM7BcpHotTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev m7bh_a_wf := @LeanQbeTest.T.KissatM7BcpHotTest.m7bh_wf
abbrev m7bh_a_cwf := @LeanQbeTest.T.KissatM7BcpHotTest.m7bh_canon_wf
abbrev m7bh_a_acyc := @LeanQbeTest.T.KissatM7BcpHotTest.m7bh_acyc
abbrev m7bh_a_nd := @LeanQbeTest.T.KissatM7BcpHotTest.m7bh_nd
abbrev m7bh_a_nx := @LeanQbeTest.T.KissatM7BcpHotTest.m7bh_no_exit
abbrev m7bh_a_ovf := @LeanQbeTest.T.KissatM7BcpHotTest.m7bh_ovf_wp
abbrev m7bh_a_chr := @LeanQbeTest.T.KissatM7BcpHotTest.m7bh_chrono_wp
abbrev m7bh_a_ign := @LeanQbeTest.T.KissatM7BcpHotTest.m7bh_prop_ign_wp
abbrev m7bh_a_bcp := @LeanQbeTest.T.KissatM7BcpHotTest.m7bh_bcp_wp
abbrev m7bh_a_prp := @LeanQbeTest.T.KissatM7BcpHotTest.m7bh_prop_wp
abbrev m7bh_a_mod := @LeanQbeTest.T.KissatM7BcpHotTest.m7bh_mod_ok
abbrev m7bh_a_nv := @LeanQbeTest.T.KissatM7BcpHotTest.m7bh_nv

#print axioms m7bh_a_wf
#print axioms m7bh_a_cwf
#print axioms m7bh_a_acyc
#print axioms m7bh_a_nd
#print axioms m7bh_a_nx
#print axioms m7bh_a_ovf
#print axioms m7bh_a_chr
#print axioms m7bh_a_ign
#print axioms m7bh_a_bcp
#print axioms m7bh_a_prp
#print axioms m7bh_a_mod
#print axioms m7bh_a_nv
