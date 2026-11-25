module

public import LeanQbe.T.Examples.Kissat.FullFidelityBcp
public import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof1
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullFidelityBcp
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, and Axiom Audit for Kissat `FullFidelityBcp`

1. Executable `#guard` checks on `fidBcpModule` (`8` fns, `14` externs, `0` exits), the
   canonical drop-in handles (`fidBcpRepls`, `fidBcpBefores`), the composed
   `FullM7HotWatchPush` / `FullM7MemShrinkV5` descriptors, `checkAcyclic`, `PrintCpp`,
   `PrintQbe`, and 4-ISA `Fn.legal` checks (`.aarch64`, `.scalar64`, `.x64AVX2`, `.x64AVX512`).
2. Audit-ready restated headline theorems: `Wf`, `checkAcyclic`, and parametric `Func.wp`
   proofs of the bit-identical base-pointer-cached overrides against their unmodified canonical
   specifications (`fullHeapDownSpec`, `fullHeapPopSpec`, `fullNextDecVarSpec`,
   `m6HdrDecideSpec`, `fullDeduce1uipSpec`, `m6Deduce1uipHdrSpec`) plus the linear
   delayed-watch flush `full_prop_flush_del_fid` (`fidPropFlushDelSpec`).
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatFidelityBcpTest

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullFidelityBcp

/-! ## 1. Executable `#guard` Codegen, Descriptor & Legalization Checks -/

#guard fidBcp_fns.length == 8
#guard fidBcpModule.externs.length == 14
#guard fidBcpModule.exits.isEmpty == true
#guard fidBcpModule.checkAcyclic == true
#guard fidBcpRepls.map Fn.name ==
  [ "full_heap_down", "full_heap_pop", "full_propagate_ignore_hot", "full_propagate_ignore"
  , "full_deduce_1uip_m6", "full_deduce_1uip_m6_hdr", "full_next_dec_var"
  , "m6_hdr_decide_fid" ]
#guard fidHeapDownFn.sig == ("full_heap_down", [i64, i32], [])
#guard fidHeapPopFn.sig == ("full_heap_pop", [i64], [i64])
#guard fidPropagateIgnoreHotFn.sig == ("full_propagate_ignore_hot", [i64, i64], [i64])
#guard fidPropagateIgnoreFn.sig == ("full_propagate_ignore", [i64, i64], [i64])
#guard fidDeduce1uipM6Fn.sig == ("full_deduce_1uip_m6", [i64], [i64])
#guard fidDeduce1uipM6HdrFn.sig == ("full_deduce_1uip_m6_hdr", [i64], [i64])
#guard fidNextDecVarFn.sig == ("full_next_dec_var", [i64], [i64])
#guard fidHdrDecideFn.sig == ("m6_hdr_decide_fid", [i64], [i64])
#guard fidPropFlushDelFn.sig == ("full_prop_flush_del_fid", [i64, i64], [.bool])
#guard fidBcpBefores.map Prod.fst == ["full_propagate_ignore_hot"]
#guard (fidBcpBefores.flatMap Prod.snd).map Fn.name == ["full_prop_flush_del_fid"]
#guard fidBcpHotPushRepls.length == 9
#guard (fidBcpHotPushBefores.flatMap Prod.snd).length == 2
#guard fidBcpHotPushMemRepls.length == 21
#guard (fidBcpHotPushMemRepls.map Fn.name).eraseDups.length == 21
#guard ((fidBcpHotPushMemBefores.flatMap Prod.snd).map Fn.name).eraseDups.length ==
  (fidBcpHotPushMemBefores.flatMap Prod.snd).length
#guard (ppTModule fidBcpModule).isOk
#guard (PrintQbe.module fidBcpModule).isOk
#guard (ppModule (fidBcp_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (fidBcp_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (fidBcp_fns.map (Fn.legal .x64AVX2))).isOk
#guard fidBcp_fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem fidbcp_fns_wf : ∀ f ∈ fidBcp_fns, f.Wf := fidBcp_fns_wf

theorem fidbcp_repls_wf : ∀ f ∈ fidBcpRepls, f.Wf := fidBcpRepls_wf

theorem fidbcp_hotpush_mem_repls_wf : ∀ f ∈ fidBcpHotPushMemRepls, f.Wf :=
  fidBcpHotPushMemRepls_wf

theorem fidbcp_hotpush_mem_befores_wf :
    ∀ f ∈ fidBcpHotPushMemBefores.flatMap Prod.snd, f.Wf :=
  fidBcpHotPushMemBefores_wf

theorem fidbcp_acyc : fidBcpModule.checkAcyclic = true := fidBcp_acyclic

theorem fidbcp_heap_down_wp (Γ : Env) :
    ∀ a m Q X, Full.fullHeapDownSpec a m Q X → Func.wp Γ full_heap_down_fid_body a m Q X :=
  full_heap_down_fid_wp Γ

theorem fidbcp_heap_pop_wp (Γ : Env)
    (hDown : ∀ a m Q X, Full.fullHeapDownSpec a m Q X →
      Γ "full_heap_down" [i64, i32] [] a m Q X) :
    ∀ a m Q X, Full.fullHeapPopSpec a m Q X → Func.wp Γ full_heap_pop_fid_body a m Q X :=
  full_heap_pop_fid_wp Γ hDown

theorem fidbcp_next_dec_var_wp (Γ : Env)
    (hPop : ∀ a m Q X, Full.fullHeapPopSpec a m Q X → Γ "full_heap_pop" [i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullNextDecVarSpec a m Q X →
      Func.wp Γ full_next_dec_var_fid_body a m Q X :=
  full_next_dec_var_fid_wp Γ hPop

theorem fidbcp_hdr_decide_wp (Γ : Env)
    (hDecide : ∀ a m Q X, m7DecideSpec a m Q X → Γ "full_decide_m7" [i64] [i64] a m Q X)
    (hDrInit : ∀ a m Q X, m6HdrDrMutSpec a m Q X → Γ "m6_hdr_dr_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrDecideSpec a m Q X → Func.wp Γ m6_hdr_decide_fid_fast_body a m Q X :=
  m6_hdr_decide_fid_fast_wp Γ hDecide hDrInit

theorem fidbcp_flush_wp (Γ : Env)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fidPropFlushDelSpec a m Q X → Func.wp Γ full_prop_flush_del_fid_body a m Q X :=
  full_prop_flush_del_fid_wp Γ hPush

theorem fidbcp_deduce_wp (Γ : Env)
    (hAlit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X)
    (hArsn : ∀ a m Q X, Full.fullAnalyzeRsnSpec a m Q X →
      Γ "full_analyze_rsn" [i64, i32, i32] [.bool] a m Q X)
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    (hOtfsLarge : ∀ a m Q X, Full.fullOtfsLargeSpec a m Q X →
      Γ "full_otfs_large" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsBin : ∀ a m Q X, Full.fullOtfsBinSpec a m Q X →
      Γ "full_otfs_bin" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsSub : ∀ a m Q X, Full.fullOtfsSubsumeSpec a m Q X →
      Γ "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X) :
    ∀ a m Q X, Full.fullDeduce1uipSpec a m Q X →
      Func.wp Γ full_deduce_1uip_fid_body a m Q X :=
  full_deduce_1uip_fid_wp Γ hAlit hArsn hClear hOtfsLarge hOtfsBin hOtfsSub

theorem fidbcp_deduce_hdr_wp (Γ : Env)
    (hAlit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X)
    (hArsn : ∀ a m Q X, m6AnalyzeRsnHdrSpec a m Q X →
      Γ "full_analyze_rsn_m6_hdr" [i64, i32, i32] [.bool] a m Q X)
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    (hOtfsLarge : ∀ a m Q X, Full.fullOtfsLargeSpec a m Q X →
      Γ "full_otfs_large" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsBin : ∀ a m Q X, Full.fullOtfsBinSpec a m Q X →
      Γ "full_otfs_bin" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsSub : ∀ a m Q X, Full.fullOtfsSubsumeSpec a m Q X →
      Γ "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X) :
    ∀ a m Q X, m6Deduce1uipHdrSpec a m Q X →
      Func.wp Γ full_deduce_1uip_hdr_fid_body a m Q X :=
  full_deduce_1uip_hdr_fid_wp Γ hAlit hArsn hClear hOtfsLarge hOtfsBin hOtfsSub

end LeanQbeTest.T.KissatFidelityBcpTest

/-! ## 3. Single-Line `#print axioms` Audit (`std3` Only) -/

abbrev fidbcp_ax_fns_wf := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_fns_wf
abbrev fidbcp_ax_repls_wf := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_repls_wf
abbrev fidbcp_ax_hpm_repls := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_hotpush_mem_repls_wf
abbrev fidbcp_ax_hpm_bef := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_hotpush_mem_befores_wf
abbrev fidbcp_ax_acyc := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_acyc
abbrev fidbcp_ax_heap_down := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_heap_down_wp
abbrev fidbcp_ax_heap_pop := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_heap_pop_wp
abbrev fidbcp_ax_ndv := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_next_dec_var_wp
abbrev fidbcp_ax_decide := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_hdr_decide_wp
abbrev fidbcp_ax_flush := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_flush_wp
abbrev fidbcp_ax_deduce := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_deduce_wp
abbrev fidbcp_ax_deduce_hdr := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_deduce_hdr_wp

#print axioms fidbcp_ax_fns_wf
#print axioms fidbcp_ax_repls_wf
#print axioms fidbcp_ax_hpm_repls
#print axioms fidbcp_ax_hpm_bef
#print axioms fidbcp_ax_acyc
#print axioms fidbcp_ax_heap_down
#print axioms fidbcp_ax_heap_pop
#print axioms fidbcp_ax_ndv
#print axioms fidbcp_ax_decide
#print axioms fidbcp_ax_flush
#print axioms fidbcp_ax_deduce
#print axioms fidbcp_ax_deduce_hdr

end
