module

public import LeanQbe.T.Examples.Kissat.FullM6WalkParse
public import LeanQbe.T.Examples.Kissat.FullM6WalkParseLemmas
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM6WalkParse
meta import LeanQbe.T.Examples.Kissat.FullM6WalkParseLemmas
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Backend Guards, and Axiom Audit for Kissat M6 WalkSAT & Parse (`FullM6WalkParse`)

1. Executable `#guard` checks on `m6WalkParseModule` (`11` fns + `7` externs, `0` exits),
   `checkAcyclic = true`, `m6WalkParseSpecTable` (`18` rows), drop-in replacement `Fn` handles,
   `PrintCpp`, `PrintQbe`, and `Fn.legal` across `aarch64`, `scalar64`, and `x64AVX2`.
2. Audit-ready restated headline theorems for `m6WalkParse_fns_wf`, `m6WalkParse_acyclic`, all
   `11` parametric `Func.wp` contracts, closed `18`-row `m6WalkParse_moduleOk`, and concrete
   `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs).
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM6WalkParseTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6WalkParse
open Kraken.Bedrock2.Test

/-! ## 1. Static Checks & Backend Compilation Guards -/

#guard m6WalkParseModule.checkAcyclic == true
#guard m6WalkParseModule.exits.isEmpty
#guard m6WalkParse_fns.length == 11
#guard m6WalkParseExterns.length == 7
#guard m6WalkParseSpecTable.length == 18
#guard m6RescaleFn.name == "full_rescale"
#guard m6ParseBodyFn.name == "full_parse_body"
#guard m6WalkCbInvFn.name == "full_walk_cb_inv_m6"
#guard m6WalkScoreFn.name == "full_walk_score_m6"
#guard m6WalkCollectFn.name == "full_walk_collect_m6"
#guard m6WalkBuildCsrFn.name == "full_walk_build_csr_m6"
#guard m6WalkBreakFn.name == "full_walk_break_m6"
#guard m6WalkPickFn.name == "full_walk_pick_m6"
#guard m6WalkFlipFn.name == "full_walk_flip_m6"
#guard m6WalkCoreHelperFn.name == "full_walk_core_m6"
#guard m6WalkCoreFn.name == "full_walk"
#guard m6WalkFn.name == "full_walk"
#guard (ppTModule m6WalkParseModule).isOk
#guard (PrintQbe.module m6WalkParseModule).isOk
#guard (ppModule (m6WalkParse_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m6WalkParse_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m6WalkParse_fns.map (Fn.legal .x64AVX2))).isOk

/-! ## 2. Audit-Ready Restated Headline Theorems -/

section AuditSpec

theorem m6wp_wf : ∀ f ∈ m6WalkParse_fns, f.Wf :=
  m6WalkParse_fns_wf

theorem m6wp_acyc : m6WalkParseModule.checkAcyclic = true :=
  m6WalkParse_acyclic

theorem m6wp_rescale_wp (Γ : Env) :
    ∀ a m Q X, fullRescaleSpec a m Q X → Func.wp Γ full_rescale_m6_body a m Q X :=
  full_rescale_m6_wp Γ

theorem m6wp_parse_body_wp (Γ : Env)
    (hSwc : ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] a m Q X)
    (hSkip : ∀ a m Q X, fullSkipClSpec a m Q X →
      Γ "full_skip_cl" [i64, i64] [.bool] a m Q X)
    (hIngest : ∀ a m Q X, fullIngestClSpec a m Q X →
      Γ "full_ingest_cl" [i64, i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullParseBodySpec a m Q X → Func.wp Γ full_parse_body_m6_body a m Q X :=
  full_parse_body_m6_wp Γ hSkip hIngest hProp hSwc

theorem m6wp_cb_inv_wp (Γ : Env) :
    ∀ a m Q X, m6WalkCbInvSpec a m Q X → Func.wp Γ full_walk_cb_inv_m6_body a m Q X :=
  full_walk_cb_inv_m6_wp Γ

theorem m6wp_score_wp (Γ : Env) :
    ∀ a m Q X, m6WalkScoreSpec a m Q X → Func.wp Γ full_walk_score_m6_body a m Q X :=
  full_walk_score_m6_wp Γ

theorem m6wp_collect_wp (Γ : Env)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, m6WalkCollectSpec a m Q X → Func.wp Γ full_walk_collect_m6_body a m Q X :=
  full_walk_collect_m6_wp Γ hArenaNext

theorem m6wp_build_csr_wp (Γ : Env) :
    ∀ a m Q X, m6WalkBuildCsrSpec a m Q X → Func.wp Γ full_walk_build_csr_m6_body a m Q X :=
  full_walk_build_csr_m6_wp Γ

theorem m6wp_break_wp (Γ : Env) :
    ∀ a m Q X, m6WalkBreakSpec a m Q X → Func.wp Γ full_walk_break_m6_body a m Q X :=
  full_walk_break_m6_wp Γ

theorem m6wp_pick_wp (Γ : Env)
    (hBreak : ∀ a m Q X, m6WalkBreakSpec a m Q X →
      Γ "full_walk_break_m6" [i64, i32, i64, i64, i64] [i64] a m Q X)
    (hScore : ∀ a m Q X, m6WalkScoreSpec a m Q X →
      Γ "full_walk_score_m6" [i64, i64] [i32] a m Q X)
    (hRng : ∀ a m Q X, fullRngNextSpec a m Q X →
      Γ "full_rng_next" [i64] [i64] a m Q X) :
    ∀ a m Q X, m6WalkPickSpec a m Q X → Func.wp Γ full_walk_pick_m6_body a m Q X :=
  full_walk_pick_m6_wp Γ hBreak hScore hRng

theorem m6wp_flip_wp (Γ : Env) :
    ∀ a m Q X, m6WalkFlipSpec a m Q X → Func.wp Γ full_walk_flip_m6_body a m Q X :=
  full_walk_flip_m6_wp Γ

theorem m6wp_walk_core_wp (Γ : Env)
    (hCollect : ∀ a m Q X, m6WalkCollectSpec a m Q X →
      Γ "full_walk_collect_m6" [i64, i64, i64] [i64] a m Q X)
    (hBuildCsr : ∀ a m Q X, m6WalkBuildCsrSpec a m Q X →
      Γ "full_walk_build_csr_m6" [i64, i64, i64, i64] [i64] a m Q X)
    (hCbInv : ∀ a m Q X, m6WalkCbInvSpec a m Q X →
      Γ "full_walk_cb_inv_m6" [i64, i64, i64] [i64] a m Q X)
    (hRng : ∀ a m Q X, fullRngNextSpec a m Q X →
      Γ "full_rng_next" [i64] [i64] a m Q X)
    (hPick : ∀ a m Q X, m6WalkPickSpec a m Q X →
      Γ "full_walk_pick_m6" [i64, i64, i64, i64, i64, i64] [i32] a m Q X)
    (hFlip : ∀ a m Q X, m6WalkFlipSpec a m Q X →
      Γ "full_walk_flip_m6" [i64, i32, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullWalkSpec a m Q X → Func.wp Γ full_walk_core_m6_body a m Q X :=
  full_walk_core_m6_wp Γ hCollect hBuildCsr hCbInv hRng hPick hFlip

theorem m6wp_walk_wp (Γ : Env)
    (hWarmup : ∀ a m Q X, fullWarmupSpec a m Q X → Γ "full_warmup" [i64] [] a m Q X)
    (hWalkCore : ∀ a m Q X, fullWalkSpec a m Q X →
      Γ "full_walk_core_m6" [i64] [] a m Q X) :
    ∀ a m Q X, m6WalkSpec a m Q X → Func.wp Γ full_walk_m6_body a m Q X :=
  full_walk_m6_wp Γ hWarmup hWalkCore

theorem m6wp_mod_ok : ModuleOk m6WalkParseEnv m6WalkParseModule :=
  m6WalkParse_moduleOk

theorem m6wp_nv_rescale :
    Func.wp m6WalkParseEnv full_rescale_m6_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s',
        PreservesCoreSlice FullState.core nvOneLitState s' ∧
        s'.LengthsOk nvOneLitCfg ∧ FullProbeScratchPres nvOneLitState s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_rescale

theorem m6wp_nv_walk_core :
    Func.wp m6WalkParseEnv full_walk_core_m6_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ fuel' sc',
        let s' := { nvOneLitState with core := { nvOneLitState.core with fuel := fuel' },
                                       scratch := sc' }
        FullCoreInv nvOneLitCfg nvOneLitF0 s' ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_walk_core

theorem m6wp_nv_walk :
    Func.wp m6WalkParseEnv full_walk_m6_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s', FullCoreInv nvOneLitCfg nvOneLitF0 s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_walk

theorem m6wp_nv_parse :
    Func.wp m6WalkParseEnv full_parse_body_m6_body
      (nvOneLitCfg.hdr, m6NvCnfPtr + BitVec.ofNat 64 m6NvUnsatBytes.length, ()) nvM6ParseMem
      (fun (r, ()) m' =>
        r = 20#64 ∧ (∃ cnf, parseDimacs m6NvUnsatBytes = some cnf ∧ cnf.Unsat) ∧
        ∃ s', (bytes m6NvCnfPtr m6NvUnsatBytes ⋆ FullMem nvOneLitCfg s') m')
      (fun _ _ _ _ => False) :=
  nv_m6_parse_body

end AuditSpec

end LeanQbeTest.T.KissatM6WalkParseTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev m6wp_a_wf := @LeanQbeTest.T.KissatM6WalkParseTest.m6wp_wf
abbrev m6wp_a_acyc := @LeanQbeTest.T.KissatM6WalkParseTest.m6wp_acyc
abbrev m6wp_a_rsc := @LeanQbeTest.T.KissatM6WalkParseTest.m6wp_rescale_wp
abbrev m6wp_a_pb := @LeanQbeTest.T.KissatM6WalkParseTest.m6wp_parse_body_wp
abbrev m6wp_a_cb := @LeanQbeTest.T.KissatM6WalkParseTest.m6wp_cb_inv_wp
abbrev m6wp_a_sc := @LeanQbeTest.T.KissatM6WalkParseTest.m6wp_score_wp
abbrev m6wp_a_col := @LeanQbeTest.T.KissatM6WalkParseTest.m6wp_collect_wp
abbrev m6wp_a_csr := @LeanQbeTest.T.KissatM6WalkParseTest.m6wp_build_csr_wp
abbrev m6wp_a_brk := @LeanQbeTest.T.KissatM6WalkParseTest.m6wp_break_wp
abbrev m6wp_a_pck := @LeanQbeTest.T.KissatM6WalkParseTest.m6wp_pick_wp
abbrev m6wp_a_flp := @LeanQbeTest.T.KissatM6WalkParseTest.m6wp_flip_wp
abbrev m6wp_a_wc := @LeanQbeTest.T.KissatM6WalkParseTest.m6wp_walk_core_wp
abbrev m6wp_a_w := @LeanQbeTest.T.KissatM6WalkParseTest.m6wp_walk_wp
abbrev m6wp_a_mod := @LeanQbeTest.T.KissatM6WalkParseTest.m6wp_mod_ok
abbrev m6wp_a_nv_r := @LeanQbeTest.T.KissatM6WalkParseTest.m6wp_nv_rescale
abbrev m6wp_a_nv_wc := @LeanQbeTest.T.KissatM6WalkParseTest.m6wp_nv_walk_core
abbrev m6wp_a_nv_w := @LeanQbeTest.T.KissatM6WalkParseTest.m6wp_nv_walk
abbrev m6wp_a_nv_p := @LeanQbeTest.T.KissatM6WalkParseTest.m6wp_nv_parse

#print axioms m6wp_a_wf
#print axioms m6wp_a_acyc
#print axioms m6wp_a_rsc
#print axioms m6wp_a_pb
#print axioms m6wp_a_cb
#print axioms m6wp_a_sc
#print axioms m6wp_a_col
#print axioms m6wp_a_csr
#print axioms m6wp_a_brk
#print axioms m6wp_a_pck
#print axioms m6wp_a_flp
#print axioms m6wp_a_wc
#print axioms m6wp_a_w
#print axioms m6wp_a_mod
#print axioms m6wp_a_nv_r
#print axioms m6wp_a_nv_wc
#print axioms m6wp_a_nv_w
#print axioms m6wp_a_nv_p
