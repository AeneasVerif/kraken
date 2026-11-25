module

public import LeanQbe.T.Examples.Kissat.FullFidelityBcp
public import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof1
public import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof2
public import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof3
public import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof
public import LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5Proof
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof2
meta import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof3
meta import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof
meta import LeanQbe.T.Examples.Kissat.FullM7HotWatchPush
meta import LeanQbe.T.Examples.Kissat.FullM7BcpHot
meta import LeanQbe.T.Examples.Kissat.FullM6WatchGc
meta import LeanQbe.T.Examples.Kissat.PatchModule
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

section ComposedBundle

open Std.Sat
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FastCore
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM7BcpHot
open LeanQbe.T.Examples.Kissat.FullM7HotWatchPush
open LeanQbe.T.Examples.Kissat.FullM7MemShrink
open LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5
open LeanQbe.T.Examples.Kissat.PatchModule

#guard fidBcpHotPushMod.fns.length == 8
#guard fidBcpHotPushMod.externs.length == 3
#guard fidBcpHotPushMod.exits.isEmpty == true
#guard fidBcpHotPushMod.checkAcyclic == true
#guard (ppTModule fidBcpHotPushMod).isOk
#guard (LeanQbe.T.PrintQbe.module fidBcpHotPushMod).isOk
#guard (ppModule (fidBcpHotPushMod.fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (fidBcpHotPushMod.fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (fidBcpHotPushMod.fns.map (Fn.legal .x64AVX2))).isOk
#guard fidBcpHotPushMod.fns.all fun fn =>
  (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

theorem fidbcp_propagate_ignore_fid_wp (Γ : Env)
    (hOvf : ∀ a m Q X, fullPropLitOvfHotSpec a m Q X →
      Γ "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool] a m Q X)
    (hCh : ∀ a m Q X, fullPropChronoHotSpec a m Q X →
      Γ "full_prop_chrono_hot" [i64, i64] [.bool] a m Q X)
    (hFl : ∀ a m Q X, fidPropFlushDelSpec a m Q X →
      Γ "full_prop_flush_del_fid" [i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullPropagateIgnoreS15Spec a m Q X →
      Func.wp Γ fidPropagateIgnoreHotFn.body a m Q X :=
  full_propagate_ignore_fid_wp Γ hOvf hCh hFl

theorem fidbcp_full_bcp_hot_s15_wp (Γ : Env)
    (hIgn : ∀ a m Q X, fullPropagateIgnoreS15Spec a m Q X →
      Γ "full_propagate_ignore_hot" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullBcpS15Spec a m Q X →
      Func.wp Γ FullM7BcpHot.full_bcp_hot_body a m Q X :=
  full_bcp_hot_s15_wp Γ hIgn

theorem fidbcp_hotpush_base_module_ok :
    ModuleOk fidBcpHotPushBaseEnv fidBcpHotPushBaseMod :=
  fidBcpHotPushBase_moduleOk

theorem fidbcp_standalone_module_ok : ModuleOk fidBcpEnv fidBcpModule :=
  fidBcp_moduleOk

theorem fidbcp_hotpush_acyc : fidBcpHotPushMod.checkAcyclic = true :=
  fidBcpHotPush_acyclic

theorem fidbcp_hotpush_names_nodup : fidBcpHotPushMod.namesNodup :=
  fidBcpHotPush_namesNodup

theorem fidbcp_hotpush_module_ok : ModuleOk fidBcpHotPushEnv fidBcpHotPushMod :=
  fidBcpHotPush_moduleOk

theorem fidbcp_hot_unsat_sound (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (m : Mem 64)
    (hlen0 : s.LengthsOk c) (hw0 : FullWitnessInv c F0 F_cur s.core)
    (hdense0 : s.core.dense_mode = 0#64) (hm0 : (FullMem c s ⋆ R) m) :
    Func.wp fidBcpHotPushEnv FullM7BcpHot.full_bcp_hot_body (c.hdr, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) ∧
        ∃ s', s'.LengthsOk c ∧ FullWitnessInv c F0 F_cur s'.core ∧
          (c.delayed_cap = 0 → s'.scratch.delayed = s.scratch.delayed) ∧
          (r = 1#64 → s'.core.cur_level = 0 → F0.Unsat) ∧
          (FullMem c s' ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fid_bcp_hot_unsat_sound c F0 F_cur s R m hlen0 hw0 hdense0 hm0

theorem fidbcp_mem_repls_nodup : (fidBcpHotPushMemRepls.map Fn.name).Nodup :=
  fidBcpHotPushMemRepls_names_nodup

theorem fidbcp_mem_befores_nodup : (fidBcpHotPushMemBefores.map Prod.fst).Nodup :=
  fidBcpHotPushMemBefores_targets_nodup

theorem fidbcp_m7ms_m6_mem_init_4k :
    Func.wp m7msM6Env FullM6Hdr.full_m6_mem_init_body
      (0x2000#64, 0x2000#64 + BitVec.ofNat 64 nvMsUnsatBytes.length,
       0x2000#64 + BitVec.ofNat 64 nvMsUnsatBytes.length, 6400#64, 16#64, ())
      nvMs4kInitMem
      (fun (r, ()) m' => ∃ (c : MemShrinkCfg) (ext : List (BitVec 64)) (s : FullState),
        r = c.hdr ∧ c.hdr = (0x2000#64 + BitVec.ofNat 64 nvMsUnsatBytes.length) +
          BitVec.ofNat 64 fullM6ExtBytes ∧
        c.avail = 4096 ∧ c.mv = 1 ∧ c.nc = 2 ∧ nvMsUnsatCnf.Unsat ∧
        MsM6HdrExtInitOk ext ∧ MemShrinkM6HdrInv c ext s ∧
        (bytes 0x2000#64 nvMsUnsatBytes ⋆ MemShrinkM6HdrMem c ext s) m')
      (fun _ _ _ _ => False) :=
  fid_m7ms_m6_mem_init_4k

theorem fidbcp_nv_bcp_hot :
    Func.wp fidBcpHotPushEnv FullM7BcpHot.full_bcp_hot_body (FastCore.nvFastPropCfg.hdr, ())
      FastCore.nvFastPropMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) ∧ Full.nvOneLitF0.Unsat ∧
        ∃ s', s'.LengthsOk FastCore.nvFastPropCfg ∧
          FullWitnessInv FastCore.nvFastPropCfg Full.nvOneLitF0 [[0], [1]] s'.core ∧
          s'.scratch.delayed = FastCore.nvFastPropState.scratch.delayed ∧
          FullMem FastCore.nvFastPropCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_bcp_hot

theorem fidbcp_nv_bcp_delayed :
    Func.wp fidBcpHotPushEnv FullM7BcpHot.full_bcp_hot_body (nvDelayedCfg.hdr, ()) nvDelayedMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) ∧ nvDelayedF0.Unsat ∧
        ∃ s', s'.LengthsOk nvDelayedCfg ∧
          FullWitnessInv nvDelayedCfg nvDelayedF0 [[1, 3, 4], [0], [2], [3, 5]] s'.core ∧
          FullMem nvDelayedCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_bcp_delayed

theorem fidbcp_nv_flush_del :
    Func.wp fidBcpHotPushEnv full_prop_flush_del_fid_body (nvDelayedCfg.hdr, 3#64, ())
      nvFlushDelMem
      (fun (_ok, ()) m' =>
        nvDelayedF0.Unsat ∧
        ∃ wvec' wstk' wlen' wu' wsort',
          let st' : FullState :=
            { nvFlushDelState with
              core := { nvFlushDelState.core with
                wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
              scratch := { nvFlushDelState.scratch with wsort := wsort' } }
          st'.LengthsOk nvDelayedCfg ∧ WatchStackLayout st'.core ∧ FullMem nvDelayedCfg st' m')
      (fun _ _ _ _ => False) :=
  nv_fid_flush_del

theorem fidbcp_nv_hotpush_watch_push :
    Func.wp fidBcpHotPushEnv m7WatchPushFastFn.body
      (nvOneLitCfg.hdr, 0#32, 0#32, 0#32, 1#32, ()) nvOneLitMem
      (fun (ok, ()) m' =>
        Full.nvOneLitF0.Unsat ∧ ok = false ∧
        ∃ wvec' wstk' wlen' wu' wsort',
          let s' : FullState :=
            { nvOneLitState with
              core := { nvOneLitState.core with
                wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
              scratch := { nvOneLitState.scratch with wsort := wsort' } }
          s'.LengthsOk nvOneLitCfg ∧ WatchStackLayout s'.core ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_bcp_hotpush_watch_push

end ComposedBundle

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

abbrev fidbcp2_ax_prop_ign := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_propagate_ignore_fid_wp
abbrev fidbcp2_ax_bcp_hot_s15 := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_full_bcp_hot_s15_wp
abbrev fidbcp2_ax_base_ok := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_hotpush_base_module_ok
abbrev fidbcp2_ax_standalone_ok := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_standalone_module_ok
abbrev fidbcp2_ax_hotpush_acyc := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_hotpush_acyc
abbrev fidbcp2_ax_hotpush_nodup := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_hotpush_names_nodup
abbrev fidbcp2_ax_hotpush_ok := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_hotpush_module_ok
abbrev fidbcp2_ax_unsat_sound := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_hot_unsat_sound
abbrev fidbcp2_ax_mem_repls := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_mem_repls_nodup
abbrev fidbcp2_ax_mem_befores := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_mem_befores_nodup
abbrev fidbcp2_ax_mem_init_4k := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_m7ms_m6_mem_init_4k
abbrev fidbcp2_ax_nv_hot := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_nv_bcp_hot
abbrev fidbcp2_ax_nv_delayed := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_nv_bcp_delayed
abbrev fidbcp2_ax_nv_flush_del := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_nv_flush_del
abbrev fidbcp2_ax_nv_watch_push := @LeanQbeTest.T.KissatFidelityBcpTest.fidbcp_nv_hotpush_watch_push

#print axioms fidbcp2_ax_prop_ign
#print axioms fidbcp2_ax_bcp_hot_s15
#print axioms fidbcp2_ax_base_ok
#print axioms fidbcp2_ax_standalone_ok
#print axioms fidbcp2_ax_hotpush_acyc
#print axioms fidbcp2_ax_hotpush_nodup
#print axioms fidbcp2_ax_hotpush_ok
#print axioms fidbcp2_ax_unsat_sound
#print axioms fidbcp2_ax_mem_repls
#print axioms fidbcp2_ax_mem_befores
#print axioms fidbcp2_ax_mem_init_4k
#print axioms fidbcp2_ax_nv_hot
#print axioms fidbcp2_ax_nv_delayed
#print axioms fidbcp2_ax_nv_flush_del
#print axioms fidbcp2_ax_nv_watch_push

end
