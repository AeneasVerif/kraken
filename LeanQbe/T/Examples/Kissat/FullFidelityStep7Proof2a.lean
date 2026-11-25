/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep7
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof2a0
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullM4BvaLemmas2
import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas1
import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas3
import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas5
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Examples.Kissat.FullBridgeLemmas3
import LeanQbe.T.Examples.Kissat.FullIngestLemmas2
import LeanQbe.T.Logic.C0Agrees
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step-7 BVA Commit WP Proof (`FullFidelityStep7Proof2a`)

M1-clean UNSAT-only parametric `Func.wp` proof (`public section`, `XPost`-polymorphic) of
`full_bva_commit_step7_wp`: Step-7 `FullFidelityStep7.full_bva_commit_body` satisfies
`step7BvaCommitSpec`. Relative to Step 6 (`FullFidelityBvaProof2a`) the body differs in the
per-literal `FL_FACT_P` / `FL_FACT_N` flag updates of phases 1a/1b and replaces the parent-chain
deletion walk by (i) in-place row compaction `row[q][fi] := row[q][par[q+1][fi]]` for
`q = best_k - 1 .. 0` (pairwise-disjoint monotone bump blocks, `Step7BvaLayout`) and (ii) a
per-row deletion sweep (`full_delete_binary` / `full_unwatch_large` + `PH_GARB`), after which the
compacted rows `0 ..= best_k` (all of length `mn`) and `h->res_sz = best_k` are exported as
`Step7BvaCommittedOk` for `full_factor`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep7

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullArenaTactics
open FullBvaHeap FullBvaHeap.FullBvaHeapHelpers FullBvaHeap.FullBvaHeapTactics
open FullBvaHeap.FullBvaHeapScanHelpers FullM4Bva
open LeanQbe.T.Examples.Kissat.FullFidelityBva LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof2a
open scoped FullArenaTactics FullBvaHeapTactics

@[local bv_c0] private theorem bv64_one_toNat : (1 : BitVec 64).toNat = 1 := rfl
@[local bv_c0] private theorem bv32_one_toNat : (1 : BitVec 32).toNat = 1 := rfl
@[local bv_c0] private theorem bv64_two_toNat : (2 : BitVec 64).toNat = 2 := rfl
@[local bv_c0] private theorem bv64_three_toNat : (3 : BitVec 64).toNat = 3 := rfl

local elab "c0_hsteps_np" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000
local elab "c0_hstep_np" : tactic => LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 1
local elab "c0_hsteps_nogrp_np" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

private theorem bv32_shl1_xor1 {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    ((x <<< (1 : Nat)) ^^^ 1#32).toNat = 2 * x.toNat + 1 := by
  have hev : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
    rw [bv32_shl1_nat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl, hev]; apply Nat.eq_of_testBit_eq; intro k
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ j =>
    rw [Nat.testBit_xor, show Nat.testBit 1 (j + 1) = false by rw [Nat.testBit_succ]; simp,
      Bool.xor_false, Nat.testBit_succ, Nat.testBit_succ,
      show (2 * x.toNat + 1) / 2 = (2 * x.toNat) / 2 by omega]

private theorem bv32_shl1_or1 {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    ((x <<< (1 : Nat)) ||| 1#32).toNat = 2 * x.toNat + 1 := by
  have hev : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
    rw [bv32_shl1_nat, Nat.mod_eq_of_lt (by omega)]
  rw [FullBvaFwdTactics.bv32_or1_of_even (by rw [hev]; omega), hev]

private theorem fullDenseInvW_set_wsort {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {ws' : List (BitVec 32)} (hws : ws'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with wsort := ws' } } :=
  fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len)
    (sc' := { s.scratch with wsort := ws' }) hinv hinv.1.core_ok.repr_len
    hinv.1.core_ok.min_clr_len_arr hinv.1.core_ok.tmp_len_arr hinv.1.core_ok.flags_len
    hinv.1.core_ok.tmp_len_le { hinv.1.scratch_ok with wsort_len := hws } rfl rfl

/-! ## 1. Invariant Preservation Helpers & Commit AST Navigators -/

private abbrev S7PreOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sd : FullState) : Prop :=
  FullDenseInvW c F0 F_cur sd ∧ sd.core.cur_vars = s.core.cur_vars ∧
  sd.core.fuel = s.core.fuel ∧ sd.core.arena = s.core.arena ∧
  sd.core.arena_len = s.core.arena_len ∧ sd.scratch.scratch_buf = s.scratch.scratch_buf ∧
  sd.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  sd.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ sd.scratch.res_sz = s.scratch.res_sz

private theorem denseWatchSliceOk_congr {F_cur : List (List Nat)} {k k' : FullCoreState}
    {l off off' n : Nat} (hcv : k'.cur_vars = k.cur_vars)
    (hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k)
    (hw : ∀ j < n, k'.wstk[off' + j]? = k.wstk[off + j]?)
    (h : DenseWatchSliceOk F_cur k l off n) : DenseWatchSliceOk F_cur k' l off' n := by
  induction h generalizing off' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    exact .bin (by simpa using (hw 0 (Nat.zero_lt_succ _)).trans hp) hflag hne (by omega) hent
      (ih fun j hj => by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hw (j + 1) (by omega))
  | @occ p rem w0 cref hp hp1 hflag h3 hlt href _ ih =>
    exact .occ (by simpa using (hw 0 (by omega)).trans hp) ((hw 1 (by omega)).trans hp1)
      hflag h3 hlt (by rwa [hrefs])
      (ih fun j hj => by simpa [Nat.add_assoc, Nat.add_comm 2 j] using hw (j + 2) (by omega))

private theorem fullDenseInvW_of_defrag {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat}
    (hlen' : let k' := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
      ({ s with core := k', scratch := { s.scratch with wsort := wsort' } } :
        FullState).LengthsOk c)
    (hlay' : WatchStackLayout
      { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 })
    (hsl : let k' := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
      ∀ l < 2 * s.core.cur_vars, fullWatchSizeCore k' l = fullWatchSizeCore s.core l ∧
      ∀ k < fullWatchSizeCore s.core l,
        wstk'[fullWatchOffCore k' l + k]? = s.core.wstk[fullWatchOffCore s.core l + k]?) :
    let k' := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
    FullDenseInvW c F0 F_cur
      { s with core := k', scratch := { s.scratch with wsort := wsort' } } := by
  intro k'; have hdm := hinv.2.2.2.2.2.2; have hdw : DenseWatchesInv F_cur s.core := by
    have h := hinv.2.1.watches; unfold ModeWatchesInv at h; rwa [ite_eq_right hdm] at h
  have hdw' : DenseWatchesInv F_cur k' :=
    DenseWatchesInv.of_slices hlay'.bounds hlay'.pos_off hlay'.disjoint fun l hl => by
      obtain ⟨hsz, hget⟩ := hsl l hl; rw [hsz]
      exact denseWatchSliceOk_congr (k := s.core) (k' := k') rfl rfl (fun j hj => hget j hj)
        (hdw.slices l hl)
  refine ⟨hlen', { hinv.2.1 with
    arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
    watches := by unfold ModeWatchesInv; rw [ite_eq_right hdm]; exact hdw' },
    hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hdm⟩

private theorem fullDenseInvW_of_addBin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' wvec' wstk' wsort' : List (BitVec 32)}
    {ph' : List (BitVec 8)} {te' wlen' : Nat} {unass' unfl' wu' nb' oom' inc' : BitVec 64}
    (hlen' : let k' := { s.core with
      vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
      trail_end := te', unassigned := unass', unflushed := unfl', wvec := wvec', wstk := wstk',
      wlen := wlen', wusable := wu', num_binary := nb', oom := oom', inconsistent := inc' }
      ({ s with core := k', scratch := { s.scratch with phases := ph', wsort := wsort' } } :
        FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur { s.core with
      vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
      trail_end := te', unassigned := unass', unflushed := unfl', wvec := wvec', wstk := wstk',
      wlen := wlen', wusable := wu', num_binary := nb', oom := oom', inconsistent := inc' }) :
    let k' := { s.core with
      vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
      trail_end := te', unassigned := unass', unflushed := unfl', wvec := wvec', wstk := wstk',
      wlen := wlen', wusable := wu', num_binary := nb', oom := oom', inconsistent := inc' }
    FullDenseInvW c F0 F_cur
      { s with core := k', scratch := { s.scratch with phases := ph', wsort := wsort' } } :=
  ⟨hlen', hw', hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem fullDenseInvW_of_delBin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s) {wvec' wstk' : List (BitVec 32)}
    {wu' nb' : BitVec 64}
    (hlen' : ({ s with core := { s.core with
      wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } } :
      FullState).LengthsOk c)
    (hwat' : ModeWatchesInv F_cur { s.core with
      wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' }) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with
      wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } } :=
  ⟨hlen', { hinv.2.1 with
    arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }, watches := hwat' },
    hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem fullDenseInvW_of_unwatchLarge {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {wvec' wstk' : List (BitVec 32)} {wu' : BitVec 64}
    (hlen' : ({ s with core := { s.core with
      wvec := wvec', wstk := wstk', wusable := wu' } } : FullState).LengthsOk c)
    (hwat' : ModeWatchesInv F_cur { s.core with
      wvec := wvec', wstk := wstk', wusable := wu' }) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } } :=
  fullDenseInvW_of_delBin hinv (nb' := s.core.num_binary) hlen' hwat'

private def sDummyVal : (t : Ty) → Val t
  | .bits _ => 0 | .bool => true | .float _ => 0 | .pair a b => (sDummyVal a, sDummyVal b)
private def sDummyTup : (ts : List Ty) → Tup Val ts
  | [] => () | t :: ts => (sDummyVal t, sDummyTup ts)

private def sStep {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := ts) _ k => k (sDummyTup ts) | .load t _ k => k (sDummyVal t)
  | .store _ _ k => k | .call (bs := bs) _ _ k => k (sDummyTup bs) | _ => .hlt
private def sSteps {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e | n + 1, e => sSteps n (sStep e)

private def sLd64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 64) _ k => k v | _ => .hlt
private def sLd32 {rs : List Ty} (v : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 32) _ k => k v | _ => .hlt
private def sCall32 {rs : List Ty} (v : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .call (bs := [.bits 32]) _ _ k => k (v, ()) | _ => .hlt
private def sLet32 {rs : List Ty} (v : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := [.bits 32]) _ k => k (v, ()) | _ => .hlt
private def sThen {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ t _ => t | _ => .hlt
private def sElse {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ _ e => e | _ => .hlt
private def sGrp0 {rs : List Ty} (J : Cont []) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[]]) bs _ => (match bs (J, ()) with | .cons f .nil => f ()) | _ => .hlt
private def sGrp1 {rs : List Ty} (J : Cont [i32]) (x : Val i32) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32]]) bs _ =>
    (match bs (J, ()) with | .cons f .nil => f (x, ())) | _ => .hlt
private def sGrp64_32 {rs : List Ty} (J : Cont [i64, i32]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64, .bits 32]]) bs _ =>
    (match bs (J, ()) with | .cons f .nil => f (0#64, 0#32, ())) | _ => .hlt
private def sGrp64_64_32 {rs : List Ty} (J : Cont [i64, i64, i32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64, .bits 64, .bits 32]]) bs _ =>
    (match bs (J, ()) with | .cons f .nil => f (0#64, 0#64, 0#32, ())) | _ => .hlt
private def sGrp64_64_32v {rs : List Ty} (J : Cont [i64, i64, i32])
    (a b : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64, .bits 64, .bits 32]]) bs _ =>
    (match bs (J, ()) with | .cons f .nil => f (a, b, 0#32, ())) | _ => .hlt
private def sGrp32b {rs : List Ty} (J : Cont [i32, .bool]) (a : Val i32) (b : Val .bool) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bool]]) bs _ =>
    (match bs (J, ()) with | .cons f .nil => f (a, b, ())) | _ => .hlt

@[irreducible] private def s7HdrExpr (h pAr pScr : Val i64) (best_k sc : Val i32) :
    Expr Val Cont [.bool] :=
  FullFidelityStep7.full_bva_commit_body Val Cont (h, best_k, ())
    |> sSteps 3 |> sElse |> sSteps 2 |> sCall32 sc |> sStep |> sElse |> sStep |> sElse |> sStep
    |> sLd64 pAr |> sStep |> sLd64 pScr

@[irreducible] private def s7PreMidExpr (h pAr pScr pCnt pFl pWv : Val i64)
    (best_k sc dm brow_off mn : Val i32) : Expr Val Cont [.bool] :=
  s7HdrExpr h pAr pScr best_k sc |> sStep |> sLd64 pCnt |> sStep |> sLd64 pFl
    |> sStep |> sLd64 pWv |> sLet32 dm |> sSteps 4 |> sLd32 brow_off
    |> sSteps 5 |> sLd32 mn |> sSteps 6

@[irreducible] private def s7MidExpr (e : Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  e |> sGrp64_32 (fun (_ : Tup Val [i64, i32]) (_ : Mem 64) => True) |> sStep |> sElse
    |> sGrp64_64_32 (fun (_ : Tup Val [i64, i64, i32]) (_ : Mem 64) => True) |> sStep |> sElse
    |> sSteps 5 |> sElse |> sSteps 5 |> sElse |> sSteps 6 |> sElse
    |> sGrp0 (fun (_ : Tup Val []) (_ : Mem 64) => True)

@[irreducible] private def s7PreExitExpr (h pAr pScr pCnt pFl pWv : Val i64)
    (best_k sc dm brow_off mn : Val i32) (need_ar need_w : Val i64) :
    Expr Val Cont [.bool] :=
  s7PreMidExpr h pAr pScr pCnt pFl pWv best_k sc dm brow_off mn
    |> sGrp64_32 (fun (_ : Tup Val [i64, i32]) (_ : Mem 64) => True) |> sStep |> sElse
    |> sGrp64_64_32v (fun (_ : Tup Val [i64, i64, i32]) (_ : Mem 64) => True) need_ar need_w
    |> sStep |> sElse |> sSteps 5 |> sElse |> sSteps 5 |> sElse |> sSteps 6 |> sElse

@[irreducible] private def s7PostDefragExpr (h pAr pScr pCnt pFl pWv : Val i64)
    (best_k sc dm brow_off mn : Val i32) : Expr Val Cont [.bool] :=
  s7PreMidExpr h pAr pScr pCnt pFl pWv best_k sc dm brow_off mn |> s7MidExpr

@[irreducible] private def s7Phase1bExpr (h pAr pScr pCnt pFl pWv pDeg pTmp : Val i64)
    (best_k sc dm brow_off mn fresh : Val i32) (ok1a : Val .bool) : Expr Val Cont [.bool] :=
  s7PostDefragExpr h pAr pScr pCnt pFl pWv best_k sc dm brow_off mn
    |> sSteps 10 |> sLd64 pDeg |> sSteps 22 |> sLet32 fresh |> sStep |> sLd64 pTmp
    |> sGrp32b (fun (_ : Tup Val [i32, .bool]) (_ : Mem 64) => True) 0#32 ok1a

@[irreducible] private def s7Phase2Expr (h pAr pScr pCnt pFl pWv pDeg pTmp : Val i64)
    (best_k sc dm brow_off mn fresh mi0 : Val i32) : Expr Val Cont [.bool] :=
  s7Phase1bExpr h pAr pScr pCnt pFl pWv pDeg pTmp best_k sc dm brow_off mn fresh true
    |> sGrp32b (fun (_ : Tup Val [i32, .bool]) (_ : Mem 64) => True) mi0 true |> sThen

private abbrev FidDelBinHyp (Γ : Env) :=
  ∀ a m Q X, Full.fullDeleteBinarySpec a m Q X → Γ "full_delete_binary" [i64, i32, i32] [] a m Q X
private abbrev FidUnwatchHyp (Γ : Env) :=
  ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X → Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X
private abbrev FidAddBinHyp (Γ : Env) :=
  ∀ a m Q X, Full.fullAddBinSpec a m Q X → Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X
private abbrev FidAllocClHyp (Γ : Env) :=
  ∀ a m Q X, Full.fullAllocClSpec a m Q X → Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X
private abbrev FidWPushHyp (Γ : Env) :=
  ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
    Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X

/-! ## 2. Phase 2: Row Compaction, Per-Row Deletion Sweep & `Step7BvaCommittedOk` -/

private def sGrp32_32 {rs : List Ty} (J : Cont [i32, i32]) (a b : Val i32) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32]]) bs _ =>
    (match bs (J, ()) with | .cons f .nil => f (a, b, ())) | _ => .hlt

@[irreducible] private def s7DelExpr (h pAr pScr pCnt pFl pWv pDeg pTmp : Val i64)
    (best_k sc dm brow_off mn fresh mi0 : Val i32) : Expr Val Cont [.bool] :=
  s7Phase2Expr h pAr pScr pCnt pFl pWv pDeg pTmp best_k sc dm brow_off mn fresh mi0
    |> sGrp1 (fun (_ : Tup Val [i32]) (_ : Mem 64) => True) 0#32 |> sStep |> sElse

@[irreducible] private def s7DelRowExpr (h pAr pScr pCnt pFl pWv pDeg pTmp : Val i64)
    (best_k sc dm brow_off mn fresh mi0 mv qsv : Val i32) (Jq : Cont [i32, i32]) :
    Expr Val Cont [.bool] :=
  s7DelExpr h pAr pScr pCnt pFl pWv pDeg pTmp best_k sc dm brow_off mn fresh mi0
    |> sStep |> sGrp32_32 Jq mv qsv |> sStep |> sThen

@[irreducible] private def s7FinalExpr (h pAr pScr pCnt pFl pWv pDeg pTmp : Val i64)
    (best_k sc dm brow_off mn fresh mi0 mv qsv : Val i32) : Expr Val Cont [.bool] :=
  s7DelExpr h pAr pScr pCnt pFl pWv pDeg pTmp best_k sc dm brow_off mn fresh mi0
    |> sStep |> sGrp32_32 (fun (_ : Tup Val [i32, i32]) (_ : Mem 64) => True) mv qsv
    |> sStep |> sElse

/-- Deletion-sweep state relation w.r.t. the compacted state `stF`: only watches, arena headers
(`PH_GARB`), `arena_garbage`, `wusable`, and `num_binary` change. -/
private abbrev S7DelOk (c : FullCfg) (F0 : CNF Nat) (F_next : List (List Nat))
    (stF st : FullState) : Prop :=
  FullDenseInvW c F0 F_next st ∧ st.core.cur_vars = stF.core.cur_vars ∧
  st.core.fuel = stF.core.fuel ∧ st.scratch = stF.scratch ∧
  st.core.arena_len = stF.core.arena_len ∧ FidBvaArenaMono stF.core st.core

private theorem s7_del_row_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hDelBin : FidDelBinHyp Γ) (hUnwatch : FidUnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_next : List (List Nat)} {stF std : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv fresh mi0 mv qsv : Val i32}
    {Jq : Cont [i32, i32]} {m0 : Mem 64}
    (hsc_eq : sc.toNat = fidStepsCap c.scratch_cap)
    (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hqs_pos : 0 < qsv.toNat) (hqs_le : qsv.toNat ≤ best_k.toNat + 1)
    (hro : ∀ q ≤ best_k.toNat, s7Ro (fidStepsCap c.scratch_cap) stF.scratch.scratch_buf q +
      mn_bv.toNat ≤ c.scratch_cap)
    (hval : ∀ q ≤ best_k.toNat, ∀ j < mn_bv.toNat, Step7RowRefOk stF
      (stF.scratch.scratch_buf[s7Ro (fidStepsCap c.scratch_cap) stF.scratch.scratch_buf q +
        j]?.getD 0#32))
    (hstd : S7DelOk c F0 F_next stF std) (hm0 : (FullMem c std ⋆ R) m0)
    (hJq : ∀ (mv : Val i32) (st' : FullState) (mm : Mem 64), S7DelOk c F0 F_next stF st' →
      (FullMem c st' ⋆ R) mm → Jq (mv, qsv - 1, ()) mm) :
    wp Γ Q X (s7DelRowExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp
      best_k sc dm_bv brow_off mn_bv fresh mi0 mv qsv Jq) m0 := by
  have hscr_b : c.scratch_cap < 2 ^ 28 := c.hscr
  have hsc4 := fidStepsCap_mul4_le c.scratch_cap
  have hsbd : std.scratch.scratch_buf = stF.scratch.scratch_buf := by rw [hstd.2.2.2.1]
  have hsbF_len : stF.scratch.scratch_buf.length = c.scratch_cap := by
    rw [← hsbd]; exact hstd.1.1.scratch_ok.scratch_buf_len
  unfold s7DelRowExpr s7DelExpr s7Phase2Expr s7Phase1bExpr s7PostDefragExpr s7MidExpr
    s7PreMidExpr s7HdrExpr
  dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrp0, sGrp1, sGrp64_32,
    sGrp64_64_32, sGrp32b, sGrp32_32, sThen, sElse, sDummyTup, sDummyVal, i64, i32,
    FullFidelityStep7.full_bva_commit_body]
  have hq1 : (qsv - 1).toNat = qsv.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by simp only [bv_c0]; omega)]; rfl
  have hqsc_n : (BitVec.setWidth 64 (sc + (qsv - 1))).toNat =
      fidStepsCap c.scratch_cap + (qsv.toNat - 1) := by
    rw [bv64_setWidth_32, BitVec.toNat_add, hq1, hsc_eq]; omega
  have hqsc_lt : (BitVec.setWidth 64 (sc + (qsv - 1))).toNat < std.scratch.scratch_buf.length := by
    rw [hqsc_n, hsbd, hsbF_len]; omega
  have hq_n : (BitVec.setWidth 64 (qsv - 1)).toNat = qsv.toNat - 1 := by
    rw [bv64_setWidth_32, hq1]
  have hq_lt : (BitVec.setWidth 64 (qsv - 1)).toNat < std.scratch.scratch_buf.length := by
    rw [hq_n, hsbd, hsbF_len]; omega
  c0_hsteps_nogrp
  generalize hrov : std.scratch.scratch_buf[(BitVec.setWidth 64 (sc + (qsv - 1))).toNat]'hqsc_lt =
    rov
  generalize std.scratch.scratch_buf[(BitVec.setWidth 64 (qsv - 1)).toNat]'hq_lt = fsv
  have hrov_n : rov.toNat =
      s7Ro (fidStepsCap c.scratch_cap) stF.scratch.scratch_buf (qsv.toNat - 1) := by
    have h1 : stF.scratch.scratch_buf[fidStepsCap c.scratch_cap + (qsv.toNat - 1)]? =
        some rov := by
      rw [← hsbd, ← hqsc_n, List.getElem?_eq_getElem hqsc_lt, hrov]
    simp only [s7Ro, h1, Option.getD_some]
  have hrow_b := hro (qsv.toNat - 1) (by omega)
  refine wp_loop_inv
    (fun (mi, ()) mm => ∃ st' : FullState, mi.toNat ≤ mn_bv.toNat ∧
      S7DelOk c F0 F_next stF st' ∧ (FullMem c st' ⋆ R) mm)
    (fun (mi, ()) _ => mn_bv.toNat - mi.toNat)
    (fun Jm hJm => ?_) (fun Jm (mi, ()) mm ⟨st', hmi_le, hst', hmm⟩ ihm => ?_)
  · c0_hstep
    exact hJm (0, ()) m0 ⟨std, Nat.zero_le _, hstd, hm0⟩
  · c0_hsplit
    · have hmi_lt : mi.toNat < mn_bv.toNat := by assumption
      obtain ⟨hinv', hcv', hfuel', hsc', hal', hmono'⟩ := hst'
      have hsb' : st'.scratch.scratch_buf = stF.scratch.scratch_buf := by rw [hsc']
      have hcs_n : (BitVec.setWidth 64 (rov + mi)).toNat = rov.toNat + mi.toNat := by
        rw [bv64_setWidth_32, BitVec.toNat_add]; omega
      have hcs_lt : (BitVec.setWidth 64 (rov + mi)).toNat < st'.scratch.scratch_buf.length := by
        rw [hcs_n, hsb', hsbF_len, hrov_n]; omega
      c0_hsteps_nogrp
      generalize hcsv : st'.scratch.scratch_buf[(BitVec.setWidth 64 (rov + mi)).toNat]'hcs_lt = cs
      have hcs_okF : Step7RowRefOk stF cs := by
        have h1 : stF.scratch.scratch_buf[s7Ro (fidStepsCap c.scratch_cap)
            stF.scratch.scratch_buf (qsv.toNat - 1) + mi.toNat]? = some cs := by
          rw [← hrov_n, ← hcs_n, ← hsb', List.getElem?_eq_getElem hcs_lt, hcsv]
        have h2 := hval (qsv.toNat - 1) (by omega) mi.toNat hmi_lt
        rwa [h1, Option.getD_some] at h2
      refine wp_join_state0 (α := FullState)
        (fun stc mc => (FullMem c stc ⋆ R) mc ∧ S7DelOk c F0 F_next stF stc)
        (fun _ stc mc ⟨hmc, hstc⟩ => ?_) (fun Jc hJc => ?_)
      · have hmi1 : (mi + 1).toNat = mi.toNat + 1 := by
          rw [BitVec.toNat_add]; simp only [show (1 : BitVec 32).toNat = 1 from rfl]; omega
        c0_hsteps
        exact ihm (mi + 1, ()) mc (by dsimp only; omega) ⟨stc, by omega, hstc, hmc⟩
      · c0_hsplit
        · c0_hsteps
          c0_call hDelBin
          refine ⟨c, st', R, rfl, hinv'.1, hinv'.2.1.watches.layout, hmm,
            fun wvec' wstk' wu' nb' md1 hlen_d _ hwat_d hmd1 => ?_⟩
          have hinv_d := fullDenseInvW_of_delBin hinv' hlen_d (hwat_d F_next hinv'.2.1.watches)
          c0_hsteps
          exact hJc _ md1 ⟨hmd1, hinv_d, hcv', hfuel', hsc', hal', hmono'⟩
        · have hbin : (cs &&& 0x80000000#32) = 0#32 := by assumption
          have hcs_ok := step7RowRefOk_mono hcs_okF hmono' (by omega) hinv'.2.1.arena
          unfold Step7RowRefOk at hcs_ok; rw [ite_eq_right (fun h' => h' hbin)] at hcs_ok
          obtain ⟨_, hcs_end, _⟩ := hcs_ok
          have hcl' := hinv'.1.core_ok
          have har_le : st'.core.arena_len ≤ st'.core.arena.length := by
            have := hcl'.arena_len_le; have := hcl'.arena_len_arr; omega
          have hcs2_n : (BitVec.setWidth 64 cs + 2).toNat = cs.toNat + 2 := by
            change (BitVec.setWidth 64 cs + 2#64).toNat = _; c0_bound
          have hcs2_lt : (BitVec.setWidth 64 cs + 2).toNat < st'.core.arena.length := by
            rw [hcs2_n]; omega
          c0_hsteps_nogrp
          generalize hcszv : st'.core.arena[(BitVec.setWidth 64 cs + 2).toNat]'hcs2_lt = csz
          have hcsz : csz.toNat = fullArenaClauseSize st' cs.toNat := by
            show _ = (st'.core.arena[cs.toNat + 2]?.getD 0#32).toNat
            rw [← hcs2_n, List.getElem?_eq_getElem hcs2_lt, hcszv, Option.getD_some]
          refine wp_loop_inv
            (fun (k, ()) mk => ∃ stk : FullState, k.toNat ≤ csz.toNat ∧
              S7DelOk c F0 F_next stF stk ∧ stk.core.arena = st'.core.arena ∧
              (FullMem c stk ⋆ R) mk)
            (fun (k, ()) _ => csz.toNat - k.toNat)
            (fun Jk hJk => ?_) (fun Jk (k, ()) mk ⟨stk, hk_le, hstk, hark, hmk⟩ ihk => ?_)
          · c0_hstep
            exact hJk (0, ()) mm ⟨st', Nat.zero_le _, ⟨hinv', hcv', hfuel', hsc', hal', hmono'⟩,
              rfl, hmm⟩
          · obtain ⟨hinvk, hcvk, hfuelk, hsck, halk, hmonok⟩ := hstk
            c0_hsplit
            · have hk_lt : k.toNat < csz.toNat := by assumption
              have hk1 : (k + 1).toNat = k.toNat + 1 := by
                rw [BitVec.toNat_add]; simp only [show (1 : BitVec 32).toNat = 1 from rfl]; omega
              have hcsk_n : (BitVec.setWidth 64 cs + 3 + BitVec.setWidth 64 k).toNat =
                  cs.toNat + 3 + k.toNat := by
                change (BitVec.setWidth 64 cs + 3#64 + BitVec.setWidth 64 k).toNat = _; c0_bound
              have hcsk_lt : (BitVec.setWidth 64 cs + 3 + BitVec.setWidth 64 k).toNat <
                  stk.core.arena.length := by
                rw [hcsk_n, hark]; omega
              c0_hsteps
              c0_call hUnwatch
              refine ⟨c, stk, R, rfl, hinvk.1, hinvk.2.1.watches.layout, hmk,
                fun wvec' wstk' wu' mu hlen_u _ hwat_u hmu => ?_⟩
              have hinv_u := fullDenseInvW_of_unwatchLarge hinvk hlen_u
                (hwat_u F_next hinvk.2.1.watches)
              c0_hsteps
              exact ihk (k + 1, ()) mu (by dsimp only; omega)
                ⟨_, by omega, ⟨hinv_u, hcvk, hfuelk, hsck, halk, hmonok⟩, hark, hmu⟩
            · have hcs_okk := step7RowRefOk_mono hcs_okF hmonok (by omega) hinvk.2.1.arena
              unfold Step7RowRefOk at hcs_okk; rw [ite_eq_right (fun h' => h' hbin)] at hcs_okk
              have hcs_refk : cs.toNat ∈ fullArenaClauseRefsCore stk.core := hcs_okk.1
              have hcs_lt : (BitVec.setWidth 64 cs).toNat < stk.core.arena.length := by
                rw [bv64_setWidth_32, hark]; omega
              have hgen : ∀ ag' : BitVec 64, S7DelOk c F0 F_next stF { stk with
                  core := { stk.core with
                    arena := stk.core.arena.set cs.toNat
                      (fullArenaHdrCore stk.core cs.toNat ||| 0x00080000#32)
                    arena_garbage := ag' } } := fun ag' => by
                obtain ⟨hinv_g, hmono_g⟩ :=
                  FullFidelityBva.fullDenseInvW_of_markGarb hinvk hcs_refk ag'
                exact ⟨hinv_g, hcvk, hfuelk, hsck, halk, fidBvaArenaMono_trans hmonok hmono_g⟩
              have harr : stk.core.arena.set (BitVec.setWidth 64 cs).toNat
                  (stk.core.arena[(BitVec.setWidth 64 cs).toNat]'hcs_lt ||| 0x00080000#32) =
                  stk.core.arena.set cs.toNat
                    (fullArenaHdrCore stk.core cs.toNat ||| 0x00080000#32) := by
                have h1 : fullArenaHdrCore stk.core cs.toNat =
                    stk.core.arena[(BitVec.setWidth 64 cs).toNat]'hcs_lt := by
                  unfold fullArenaHdrCore
                  rw [← bv64_setWidth_32 cs, List.getElem?_eq_getElem hcs_lt, Option.getD_some]
                rw [h1]
                exact congrArg (fun i => List.set stk.core.arena i
                  (stk.core.arena[(BitVec.setWidth 64 cs).toNat]'hcs_lt ||| 0x00080000#32))
                  (bv64_setWidth_32 cs)
              c0_hsteps
              refine hJc _ m ⟨?_, hgen (stk.core.arena_garbage + 3 + BitVec.setWidth 64 csz)⟩
              rw [← harr]; exact hm
    · c0_hsteps
      exact hJq mi st' mm hst' hmm

private theorem s7_final_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_next : List (List Nat)} {s stF stm : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv fresh mi0 mv qsv : Val i32}
    {mm : Mem 64}
    (hfresh_nat : fresh.toNat = 2 * s.core.cur_vars)
    (hfresh1 : (fresh ^^^ 1#32).toNat = 2 * s.core.cur_vars + 1)
    (hcvF : stF.core.cur_vars = s.core.cur_vars + 1) (hfuelF : stF.core.fuel = s.core.fuel)
    (htmF : stF.scratch.tarjan_mark = s.scratch.tarjan_mark)
    (htrF : stF.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hcommF : ∀ st', S7DelOk c F0 F_next stF st' → Step7BvaCommittedOk c st' best_k.toNat)
    (hstm : S7DelOk c F0 F_next stF stm) (hmm : (FullMem c stm ⋆ R) mm)
    (hQ : ∀ ok s' m', FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) →
      (ok = true → Step7BvaCommittedOk c s' best_k.toNat) → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (s7FinalExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp
      best_k sc dm_bv brow_off mn_bv fresh mi0 mv qsv) mm := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcomm := hcommF stm hstm
  obtain ⟨hinvm, hcvm, hfuelm, hscm', _, _⟩ := hstm
  have hclm := hinvm.1.core_ok; have hscm := hinvm.1.scratch_ok; have hcv_le := hclm.cur_vars_le
  have htmm : stm.scratch.tarjan_mark = s.scratch.tarjan_mark := by rw [hscm']; exact htmF
  have htrm : stm.scratch.tarjan_reach = s.scratch.tarjan_reach := by rw [hscm']; exact htrF
  have h2cv : (BitVec.ofNat 64 stm.core.cur_vars <<< (1 : Nat)).toNat =
      2 * (s.core.cur_vars + 1) := by
    rw [hcvm, hcvF]; simp only [bv_c0]; omega
  unfold s7FinalExpr s7DelExpr s7Phase2Expr s7Phase1bExpr s7PostDefragExpr s7MidExpr
    s7PreMidExpr s7HdrExpr
  dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrp0, sGrp1, sGrp64_32,
    sGrp64_64_32, sGrp32b, sGrp32_32, sThen, sElse, sDummyTup, sDummyVal, i64, i32,
    FullFidelityStep7.full_bva_commit_body]
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (zi, ()) mzi => ∃ wsz : List (BitVec 32), zi.toNat ≤ 2 * (s.core.cur_vars + 1) ∧
      wsz.length = 2 * c.max_vars ∧
      (FullMem c { stm with scratch := { stm.scratch with wsort := wsz } } ⋆ R) mzi)
    (fun (zi, _) _ => 2 * (s.core.cur_vars + 1) - zi.toNat) (fun Jz hJz => ?_)
    (fun Jz (zi, ()) mzi ⟨wsz, hzi_le, hwsz_l, hmzi⟩ ihz => ?_)
  · c0_hstep; exact hJz (0#64, ()) mm ⟨stm.scratch.wsort, Nat.zero_le _, hscm.wsort_len, hmm⟩
  c0_hsplit
  · have hzi_lt : zi.toNat < 2 * (s.core.cur_vars + 1) := by
      have h1 : zi.toNat < (BitVec.ofNat 64 stm.core.cur_vars <<< (1 : Nat)).toNat :=
        by assumption
      rwa [h2cv] at h1
    have hzi1 : (zi + 1#64).toNat = zi.toNat + 1 := by simp only [bv_c0]; omega
    c0_hfast; exact ihz (zi + 1#64, ()) m (by dsimp only; rw [hzi1]; omega)
      ⟨_, by rw [hzi1]; omega, by simp [hwsz_l], hm⟩
  · have hfr_rp : (BitVec.setWidth 64 fresh).toNat < stm.core.repr.length := by
      rw [bv64_setWidth_32, hfresh_nat, hclm.repr_len]; omega
    have hfr1_rp :
        (BitVec.setWidth 64 (fresh ^^^ 1#32)).toNat <
          (stm.core.repr.set (BitVec.setWidth 64 fresh).toNat dm_bv).length := by
      rw [List.length_set, bv64_setWidth_32, hfresh1, hclm.repr_len]; omega
    c0_hfast
    have hrp_len :
        ((stm.core.repr.set (BitVec.setWidth 64 fresh).toNat dm_bv).set
          (BitVec.setWidth 64 (fresh ^^^ 1#32)).toNat mn_bv).length = 2 * c.max_vars := by
      simp [hclm.repr_len]
    have hinv_fin := fullDenseInv_with_core_aux (tc' := stm.core.tmp_cnt)
      (tl' := stm.core.tmp_len)
      (sc' := { stm.scratch with wsort := wsz, bva_cnt := stm.scratch.bva_cnt + 1#64 })
      hinvm hrp_len hclm.min_clr_len_arr hclm.tmp_len_arr hclm.flags_len
      hclm.tmp_len_le { hscm with wsort_len := hwsz_l } rfl rfl
    exact hQ true _ m hinv_fin.toDense (by dsimp only; omega)
      (fun _ => by dsimp only; omega) (fun _ => hcomm.congr rfl rfl rfl rfl rfl)
      (hfuelm.trans hfuelF) htmm htrm hm

private theorem s7_del_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hDelBin : FidDelBinHyp Γ) (hUnwatch : FidUnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_next : List (List Nat)} {stF : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv fresh mi0 : Val i32} {m0 : Mem 64}
    (hsc_eq : sc.toNat = fidStepsCap c.scratch_cap)
    (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hro : ∀ q ≤ best_k.toNat, s7Ro (fidStepsCap c.scratch_cap) stF.scratch.scratch_buf q +
      mn_bv.toNat ≤ c.scratch_cap)
    (hval : ∀ q ≤ best_k.toNat, ∀ j < mn_bv.toNat, Step7RowRefOk stF
      (stF.scratch.scratch_buf[s7Ro (fidStepsCap c.scratch_cap) stF.scratch.scratch_buf q +
        j]?.getD 0#32))
    (hinvF : FullDenseInvW c F0 F_next stF) (hm0 : (FullMem c stF ⋆ R) m0)
    (hfin : ∀ (mv qsv : Val i32) (st' : FullState) (mm : Mem 64), S7DelOk c F0 F_next stF st' →
      (FullMem c st' ⋆ R) mm → wp Γ Q X (s7FinalExpr c.hdr c.pArena c.pScratchBuf c.pWsort
        c.pFlags c.pWvec c.pRepr c.pTmp best_k sc dm_bv brow_off mn_bv fresh mi0 mv qsv) mm) :
    wp Γ Q X (s7DelExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp
      best_k sc dm_bv brow_off mn_bv fresh mi0) m0 := by
  have hscr_b : c.scratch_cap < 2 ^ 28 := c.hscr
  have hsc4 := fidStepsCap_mul4_le c.scratch_cap
  have hbk1 : (best_k + 1).toNat = best_k.toNat + 1 := by
    rw [BitVec.toNat_add]; simp only [show (1 : BitVec 32).toNat = 1 from rfl]; omega
  have heq : s7DelExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp
      best_k sc dm_bv brow_off mn_bv fresh mi0 = s7DelExpr c.hdr c.pArena c.pScratchBuf c.pWsort
      c.pFlags c.pWvec c.pRepr c.pTmp best_k sc dm_bv brow_off mn_bv fresh mi0 := rfl
  conv at heq =>
    rhs
    unfold s7DelExpr s7Phase2Expr s7Phase1bExpr s7PostDefragExpr s7MidExpr s7PreMidExpr
      s7HdrExpr
    dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrp0, sGrp1, sGrp64_32,
      sGrp64_64_32, sGrp32b, sThen, sElse, sDummyTup, sDummyVal, i64, i32,
      FullFidelityStep7.full_bva_commit_body]
  rw [heq]
  c0_hstep
  refine wp_loop_inv
    (fun (_, qsv, ()) mm => ∃ st' : FullState, qsv.toNat ≤ best_k.toNat + 1 ∧
      S7DelOk c F0 F_next stF st' ∧ (FullMem c st' ⋆ R) mm)
    (fun (_, qsv, ()) _ => qsv.toNat)
    (fun J hJ => ?_) (fun J (mv, qsv, ()) mm ⟨st', hqs_le, hst', hmm⟩ ih => ?_)
  · c0_hstep
    exact hJ (_, best_k + 1, ()) m0 ⟨stF, by omega,
      ⟨hinvF, rfl, rfl, rfl, rfl, fidBvaArenaMono_refl _⟩, hm0⟩
  · c0_hsplit
    · have hqs_pos : 0 < qsv.toNat := by simpa using hc
      have hq1 : (qsv - 1).toNat = qsv.toNat - 1 := by
        rw [BitVec.toNat_sub_of_le (by simp only [bv_c0]; omega)]; rfl
      have h := s7_del_row_wp (Γ := Γ) (Q := Q) (X := X) hDelBin hUnwatch (dm_bv := dm_bv)
        (brow_off := brow_off) (fresh := fresh) (mi0 := mi0) (mv := mv) (Jq := J) hsc_eq hbk_sc
        hqs_pos hqs_le hro hval hst' hmm (fun mv' st'' mm' hst'' hmm' =>
          ih (mv', qsv - 1, ()) mm' (by dsimp only; omega) ⟨st'', by omega, hst'', hmm'⟩)
      unfold s7DelRowExpr at h; rw [heq] at h; exact h
    · have h := hfin mv qsv st' mm hst' hmm
      unfold s7FinalExpr at h; rw [heq] at h; exact h

private theorem fullDenseInvW_set_sb {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {sb' : List (BitVec 32)} (hsb : sb'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with scratch_buf := sb' } } :=
  fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len)
    (sc' := { s.scratch with scratch_buf := sb' }) hinv hinv.1.core_ok.repr_len
    hinv.1.core_ok.min_clr_len_arr hinv.1.core_ok.tmp_len_arr hinv.1.core_ok.flags_len
    hinv.1.core_ok.tmp_len_le { hinv.1.scratch_ok with scratch_buf_len := hsb } rfl rfl

private theorem s7_phase2_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hDelBin : FidDelBinHyp Γ) (hUnwatch : FidUnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s st0 : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv fresh mi0 : Val i32} {m0 : Mem 64}
    {bump : Nat}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hbk1 : 1 ≤ best_k.toNat) (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hmat : FidBvaMatrixInv c F_cur s (best_k.toNat + 1) bump)
    (hlay : Step7BvaLayout c s (best_k.toNat + 1))
    (hres : s.scratch.res_sz = BitVec.ofNat 64 best_k.toNat)
    (hsc_eq : sc.toNat = fidStepsCap c.scratch_cap)
    (hmn_getD : (s.scratch.scratch_buf[2 * sc.toNat + best_k.toNat]?.getD 0#32).toNat = mn_bv.toNat)
    (hfresh_nat : fresh.toNat = 2 * s.core.cur_vars)
    (hfresh1 : (fresh ^^^ 1#32).toNat = 2 * s.core.cur_vars + 1)
    (hst0 : S7StOk c F0 F_next s st0) (hm0 : (FullMem c st0 ⋆ R) m0)
    (hQ : ∀ ok s' m', FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) →
      (ok = true → Step7BvaCommittedOk c s' best_k.toNat) → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (s7Phase2Expr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr
      c.pTmp best_k sc dm_bv brow_off mn_bv fresh mi0) m0 := by
  obtain ⟨hinv0, hcv0, hfuel0, hsb0s, htm0, htr0, hmono0, hres0⟩ := hst0
  have hmx := c.hmaxv; have hscr_b := c.hscr; unfold dimacsBound at hmx hscr_b
  have hsc0 := hinv0.1.scratch_ok
  have hsb0_len : st0.scratch.scratch_buf.length = c.scratch_cap := hsc0.scratch_buf_len
  have hsc4 := fidStepsCap_mul4_le c.scratch_cap
  have hg : S7Geom (fidStepsCap c.scratch_cap) c.scratch_cap best_k.toNat
      st0.scratch.scratch_buf := by rw [hsb0s]; exact s7Geom_of hmat hlay
  have hmn : mn_bv.toNat =
      s7Qn (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf best_k.toNat := by
    rw [hsb0s, ← hmn_getD, hsc_eq]
  have hrows : ∀ r ≤ best_k.toNat, ∀ j < s7Qn (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf r,
      Step7RowRefOk st0 (st0.scratch.scratch_buf[s7Ro (fidStepsCap c.scratch_cap)
        st0.scratch.scratch_buf r + j]?.getD 0#32) := by
    rw [hsb0s]; exact s7_rows_ok hinv hmat hmono0 (by omega) hinv0.2.1.arena
  have hpars : ∀ r ≤ best_k.toNat, 0 < r →
      ∀ j < s7Qn (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf r,
      (st0.scratch.scratch_buf[s7Po (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf r +
        j]?.getD 0#32).toNat <
        s7Qn (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf (r - 1) := by
    rw [hsb0s]; exact s7_pars_ok hmat
  have hqmn : ∀ r ≤ best_k.toNat, mn_bv.toNat ≤
      s7Qn (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf r := fun r hr =>
    hmn ▸ s7Geom_qn_le hg hr
  have heq2 : s7Phase2Expr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp
      best_k sc dm_bv brow_off mn_bv fresh mi0 = s7Phase2Expr c.hdr c.pArena c.pScratchBuf
      c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp best_k sc dm_bv brow_off mn_bv fresh mi0 := rfl
  conv at heq2 =>
    rhs
    unfold s7Phase2Expr s7Phase1bExpr s7PostDefragExpr s7MidExpr s7PreMidExpr s7HdrExpr
    dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrp0, sGrp64_32, sGrp64_64_32,
      sGrp32b, sThen, sElse, sDummyTup, sDummyVal, i64, i32,
      FullFidelityStep7.full_bva_commit_body]
  rw [heq2]
  refine wp_loop_inv
    (fun (fsi, ()) mv => ∃ sbv : List (BitVec 32), fsi.toNat ≤ best_k.toNat ∧
      S7CompInv (fidStepsCap c.scratch_cap) c.scratch_cap best_k.toNat mn_bv.toNat fsi.toNat mn_bv
        st0.scratch.scratch_buf sbv (Step7RowRefOk st0) ∧
      (FullMem c { st0 with scratch := { st0.scratch with scratch_buf := sbv } } ⋆ R) mv)
    (fun (fsi, ()) _ => fsi.toNat)
    (fun J hJ => ?_) (fun J (fsi, ()) mv ⟨sbv, hfsi_le, hcomp, hmv⟩ ih => ?_)
  · c0_hstep
    exact hJ (best_k, ()) m0 ⟨st0.scratch.scratch_buf, Nat.le_refl _,
      s7CompInv_base hsb0_len (fun j hj => hrows _ (Nat.le_refl _) j (by omega))
        (fun hb j hj => hpars _ (Nat.le_refl _) hb j (by omega)), hm0⟩
  · c0_hsplit
    · clear heq2
      have hfsi_pos : 0 < fsi.toNat := by simpa using hc
      have hsbv_len := hcomp.1
      have hfm1 : (fsi - 1).toNat = fsi.toNat - 1 := by
        rw [BitVec.toNat_sub_of_le (by simp only [bv_c0]; omega)]; rfl
      have hro_n : (BitVec.setWidth 64 (sc + (fsi - 1))).toNat =
          fidStepsCap c.scratch_cap + (fsi.toNat - 1) := by
        rw [bv64_setWidth_32, BitVec.toNat_add, hfm1, hsc_eq]; omega
      have hro_lt : (BitVec.setWidth 64 (sc + (fsi - 1))).toNat < sbv.length := by
        rw [hro_n, hsbv_len]; omega
      have hpo_n : (BitVec.setWidth 64 (3 * sc + fsi)).toNat =
          3 * fidStepsCap c.scratch_cap + fsi.toNat := by
        rw [bv64_setWidth_32, BitVec.toNat_add, BitVec.toNat_mul, hsc_eq]
        simp only [show (3 : BitVec 32).toNat = 3 from rfl]; omega
      have hpo_lt : (BitVec.setWidth 64 (3 * sc + fsi)).toNat < sbv.length := by
        rw [hpo_n, hsbv_len]; omega
      c0_hsteps_nogrp
      generalize hrov : sbv[(BitVec.setWidth 64 (sc + (fsi - 1))).toNat]'hro_lt = rov
      generalize hpov : sbv[(BitVec.setWidth 64 (3 * sc + fsi)).toNat]'hpo_lt = pov
      obtain ⟨_, hB, hC, hD, hE, hF, hG⟩ := hcomp
      have hrov_n : rov.toNat = s7Ro (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf
          (fsi.toNat - 1) := by
        have h1 : sbv[fidStepsCap c.scratch_cap + (fsi.toNat - 1)]? = some rov := by
          rw [← hro_n, List.getElem?_eq_getElem hro_lt, hrov]
        have h2 := hB (fidStepsCap c.scratch_cap + (fsi.toNat - 1)) (by omega)
          (fun r h1 h2 => by omega)
        rw [h1] at h2; simp only [s7Ro, ← h2, Option.getD_some]
      have hpov_n : pov.toNat = s7Po (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf
          fsi.toNat := by
        have h1 : sbv[3 * fidStepsCap c.scratch_cap + fsi.toNat]? = some pov := by
          rw [← hpo_n, List.getElem?_eq_getElem hpo_lt, hpov]
        have h2 := hB (3 * fidStepsCap c.scratch_cap + fsi.toNat) (by omega)
          (fun r h1 h2 => by omega)
        rw [h1] at h2; simp only [s7Po, ← h2, Option.getD_some]
      have hcomp : S7CompInv (fidStepsCap c.scratch_cap) c.scratch_cap best_k.toNat mn_bv.toNat
          fsi.toNat mn_bv st0.scratch.scratch_buf sbv (Step7RowRefOk st0) :=
        ⟨hsbv_len, hB, hC, hD, hE, hF, hG⟩
      refine wp_join_group (ts := [i32])
        (fun (pp, ()) mm => mm = mv ∧ (1 < fsi.toNat → pp.toNat =
          s7Po (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf (fsi.toNat - 1)))
        (fun _ (pp, ()) mm ⟨hmm, hpp⟩ => ?_) (fun Jt hJt => ?_)
      rotate_left
      · have h3m_n : (BitVec.setWidth 64 (3 * sc + (fsi - 1))).toNat =
            3 * fidStepsCap c.scratch_cap + (fsi.toNat - 1) := by
          rw [bv64_setWidth_32, BitVec.toNat_add, BitVec.toNat_mul, hfm1, hsc_eq]
          simp only [show (3 : BitVec 32).toNat = 3 from rfl]; omega
        have h3m_lt : (BitVec.setWidth 64 (3 * sc + (fsi - 1))).toNat < sbv.length := by
          rw [h3m_n, hsbv_len]; omega
        c0_hsteps
        · exact hJt (_, ()) mv ⟨rfl, fun _ => by
            have h1 : sbv[3 * fidStepsCap c.scratch_cap + (fsi.toNat - 1)]? =
                some (sbv[(BitVec.setWidth 64 (3 * sc + (fsi - 1))).toNat]'h3m_lt) := by
              rw [← h3m_n, List.getElem?_eq_getElem h3m_lt]
            have h2 := hB (3 * fidStepsCap c.scratch_cap + (fsi.toNat - 1)) (by omega)
              (fun r h1 h2 => by omega)
            rw [h1] at h2; simp only [s7Po, ← h2, Option.getD_some]⟩
        · exact hJt (0, ()) mv ⟨rfl, fun h => absurd h (by assumption)⟩
      · subst hmm
        refine wp_loop_inv
          (fun (fi, ()) mw => ∃ sbw : List (BitVec 32), fi.toNat ≤ mn_bv.toNat ∧
            S7RowInv (fidStepsCap c.scratch_cap) c.scratch_cap (fsi.toNat - 1)
              st0.scratch.scratch_buf sbv sbw (Step7RowRefOk st0) ∧
            (FullMem c { st0 with scratch := { st0.scratch with scratch_buf := sbw } } ⋆ R) mw)
          (fun (fi, ()) _ => mn_bv.toNat - fi.toNat)
          (fun Ji hJi => ?_) (fun Ji (fi, ()) mw ⟨sbw, hfi_le, hrinv, hmw⟩ ihi => ?_)
        · c0_hstep
          exact hJi (0, ()) mm ⟨sbv, Nat.zero_le _, s7RowInv_init hcomp (by omega)
            (hrows _ (by omega)) (fun hq => hpars _ (by omega) hq), hmv⟩
        · have hsbw_len := hrinv.1
          c0_hsplit
          · have hfi_lt : fi.toNat < mn_bv.toNat := hc
            obtain ⟨_, hfj_lt⟩ := s7_par_read hg hcomp hrinv (by omega) hfsi_le hmn hfi_lt
            have hqb : fsi.toNat - 1 < best_k.toNat := by omega
            have hqmn' := hqmn (fsi.toNat - 1) (by omega)
            have hgq := hg.2.2.1 (fsi.toNat - 1) (by omega)
            have hgi := hg.2.2.2.1 fsi.toNat hfsi_le (by omega)
            have hqmn_i := hqmn fsi.toNat hfsi_le
            have hpofi_n : (BitVec.setWidth 64 (pov + fi)).toNat = pov.toNat + fi.toNat := by
              rw [bv64_setWidth_32, BitVec.toNat_add]; omega
            have hpofi_lt : (BitVec.setWidth 64 (pov + fi)).toNat < sbw.length := by
              rw [hpofi_n, hsbw_len, hpov_n]; omega
            c0_hsteps_nogrp
            generalize hfjv : sbw[(BitVec.setWidth 64 (pov + fi)).toNat]'hpofi_lt = fjv
            have hfjv_lt : fjv.toNat < s7Qn (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf
                (fsi.toNat - 1) := by
              have h1 : sbw[s7Po (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf fsi.toNat +
                  fi.toNat]? = some fjv := by
                rw [← hpov_n, ← hpofi_n, List.getElem?_eq_getElem hpofi_lt, hfjv]
              rw [h1] at hfj_lt; simpa using hfj_lt
            have hrofj_n : (BitVec.setWidth 64 (rov + fjv)).toNat = rov.toNat + fjv.toNat := by
              rw [bv64_setWidth_32, BitVec.toNat_add]; omega
            have hrofi_n : (BitVec.setWidth 64 (rov + fi)).toNat = rov.toNat + fi.toNat := by
              rw [bv64_setWidth_32, BitVec.toNat_add]; omega
            refine wp_join_state0 (α := List (BitVec 32))
              (fun sbw1 mf => (FullMem c { st0 with scratch := { st0.scratch with
                  scratch_buf := sbw1 } } ⋆ R) mf ∧
                (1 < fsi.toNat → ∃ v1, sbw[s7Po (fidStepsCap c.scratch_cap)
                  st0.scratch.scratch_buf (fsi.toNat - 1) + fjv.toNat]? = some v1 ∧
                  sbw1 = sbw.set (s7Po (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf
                    (fsi.toNat - 1) + fi.toNat) v1) ∧
                (¬ 1 < fsi.toNat → sbw1 = sbw))
              (fun _ sbw1 mf ⟨hmf, hsbw1a, hsbw1b⟩ => ?_) (fun Jf hJf => ?_)
            rotate_left
            · c0_hsplit
              · have hgt1 : 1 < fsi.toNat := by assumption
                have hpp_n := hpp hgt1
                have hgq' := hg.2.2.2.1 (fsi.toNat - 1) (by omega) (by omega)
                have hppfi_n : (BitVec.setWidth 64 (pp + fi)).toNat = pp.toNat + fi.toNat := by
                  rw [bv64_setWidth_32, BitVec.toNat_add]; omega
                have hppfj_n : (BitVec.setWidth 64 (pp + fjv)).toNat = pp.toNat + fjv.toNat := by
                  rw [bv64_setWidth_32, BitVec.toNat_add]; omega
                have hppfi_lt : (BitVec.setWidth 64 (pp + fi)).toNat < sbw.length := by
                  rw [hppfi_n, hsbw_len, hpp_n]; omega
                have hppfj_lt : (BitVec.setWidth 64 (pp + fjv)).toNat < sbw.length := by
                  rw [hppfj_n, hsbw_len, hpp_n]; omega
                c0_hsteps
                refine hJf _ m ⟨hm, fun _ => ⟨sbw[(BitVec.setWidth 64 (pp + fjv)).toNat]'hppfj_lt,
                  ?_, ?_⟩, fun h => absurd hgt1 h⟩
                · rw [← hpp_n, ← hppfj_n, List.getElem?_eq_getElem hppfj_lt]
                · show List.set sbw _ _ = _
                  rw [hppfi_n, hpp_n]
              · c0_hsteps
                exact hJf sbw mw ⟨hmw, fun h => absurd h (by assumption), fun _ => rfl⟩
            · have hsbw1_len : sbw1.length = c.scratch_cap := by
                by_cases hgt : 1 < fsi.toNat
                · obtain ⟨v1, _, hsbw1e⟩ := hsbw1a hgt; rw [hsbw1e]; simp [hsbw_len]
                · rw [hsbw1b hgt]; exact hsbw_len
              have hrofi_lt : (BitVec.setWidth 64 (rov + fi)).toNat < sbw1.length := by
                rw [hrofi_n, hsbw1_len, hrov_n]; omega
              have hrofj_lt : (BitVec.setWidth 64 (rov + fjv)).toNat < sbw1.length := by
                rw [hrofj_n, hsbw1_len, hrov_n]; omega
              have hfi1 : (fi + 1).toNat = fi.toNat + 1 := by
                rw [BitVec.toNat_add]; simp only [show (1 : BitVec 32).toNat = 1 from rfl]; omega
              c0_hsteps
              refine ihi (fi + 1, ()) m (by dsimp only; omega) ⟨_, by omega, ?_, hm⟩
              show S7RowInv (fidStepsCap c.scratch_cap) c.scratch_cap (fsi.toNat - 1)
                st0.scratch.scratch_buf sbv (List.set sbw1 _ _) (Step7RowRefOk st0)
              rw [hrofi_n, hrov_n]
              by_cases hgt : 1 < fsi.toNat
              · obtain ⟨v1, hv1, hsbw1e⟩ := hsbw1a hgt
                subst hsbw1e
                refine s7RowInv_step_pos hg hrinv (by omega) (by omega) (by omega) hfjv_lt hv1 ?_
                rw [← hrov_n, ← hrofj_n, List.getElem?_eq_getElem hrofj_lt]
              · have hq0 : fsi.toNat - 1 = 0 := by omega
                have hs1 := hsbw1b hgt
                subst hs1
                have hrinv0 := hrinv
                rw [hq0] at hrinv0 hfjv_lt hrov_n ⊢
                refine s7RowInv_step_zero hg hrinv0 (by have := hqmn 0 (by omega); omega)
                  hfjv_lt ?_
                rw [← hrov_n, ← hrofj_n, List.getElem?_eq_getElem hrofj_lt]
          · have hfi_eq : fi.toNat = mn_bv.toNat := by
              have : ¬ fi.toNat < mn_bv.toNat := hc
              omega
            have hh_n : (BitVec.setWidth 64 (2 * sc + (fsi - 1))).toNat =
                2 * fidStepsCap c.scratch_cap + (fsi.toNat - 1) := by
              rw [bv64_setWidth_32, BitVec.toNat_add, BitVec.toNat_mul, hfm1, hsc_eq]
              simp only [show (2 : BitVec 32).toNat = 2 from rfl]; omega
            have hh_lt : (BitVec.setWidth 64 (2 * sc + (fsi - 1))).toNat < sbw.length := by
              rw [hh_n, hsbw_len]; omega
            c0_hsteps
            refine ih (fsi - 1, ()) m (by dsimp only; omega) ⟨_, by omega, ?_, hm⟩
            show S7CompInv (fidStepsCap c.scratch_cap) c.scratch_cap best_k.toNat mn_bv.toNat
              (fsi - 1).toNat mn_bv st0.scratch.scratch_buf (List.set sbw _ _) (Step7RowRefOk st0)
            rw [hh_n, hfm1]
            exact s7CompInv_step hg hcomp hrinv (by omega) hfsi_le hmn
    · have hfsi0 : fsi.toNat = 0 := by
        have : ¬ 0 < fsi.toNat := by simpa using hc
        omega
      rw [hfsi0] at hcomp
      have hz := s7CompInv_zero hg hcomp hmn rfl
      have hcommF : ∀ st', S7DelOk c F0 F_next
          { st0 with scratch := { st0.scratch with scratch_buf := sbv } } st' →
          Step7BvaCommittedOk c st' best_k.toNat := fun st' hst' => by
        obtain ⟨hinv', hcv', _, hsc', _, hmono'⟩ := hst'
        have hcv'' : st'.core.cur_vars = s.core.cur_vars + 1 := hcv'.trans hcv0
        have hsb' : st'.scratch.scratch_buf = sbv := by rw [hsc']
        have hres' : st'.scratch.res_sz = BitVec.ofNat 64 best_k.toNat := by
          rw [hsc']; exact hres0.trans hres
        dsimp only [Step7BvaCommittedOk]
        rw [hsb']
        refine ⟨hbk_sc, hres', fun q hq => ?_⟩
        obtain ⟨hq0, hro1, hqn1, hrob, hent⟩ := hz q hq
        have hfr := (hmat.2.2.2.2.2 q (by omega)).1
        refine ⟨?_, ?_, fun qi hqi => ?_⟩
        · rw [hq0, hsb0s]; omega
        · show s7Ro _ sbv q + s7Qn _ sbv q ≤ _
          rw [hro1, hqn1]; exact hrob
        · have hqi' : qi < mn_bv.toNat := by rw [← hqn1]; exact hqi
          exact step7RowRefOk_mono ((hent qi hqi').congr rfl rfl rfl) hmono'
            (Nat.le_of_eq hcv'.symm) hinv'.2.1.arena
      have hd := s7_del_wp (Γ := Γ) (Q := Q) (X := X) hDelBin hUnwatch
        (stF := { st0 with scratch := { st0.scratch with scratch_buf := sbv } })
        (dm_bv := dm_bv) (brow_off := brow_off) (fresh := fresh) (mi0 := mi0)
        hsc_eq hbk_sc
        (fun q hq => by
          obtain ⟨_, hro1, _, hrob, _⟩ := hz q hq
          show s7Ro _ sbv q + _ ≤ _
          rw [hro1]; exact hrob)
        (fun q hq j hj => ((hz q hq).2.2.2.2 j hj).congr rfl rfl rfl)
        (fullDenseInvW_set_sb hinv0 hcomp.1) hmv
        (fun _ _ st' mm hst' hmm => s7_final_wp (s := s)
          (stF := { st0 with scratch := { st0.scratch with scratch_buf := sbv } }) hfresh_nat
          hfresh1 hcv0 hfuel0 htm0 htr0 hcommF hst' hmm hQ)
      unfold s7DelExpr at hd; rw [heq2] at hd; exact hd

/-! ## 3. Phase 1b Negative Clauses & Phase 1a Binary Propagation -/

private theorem s7_phase1b_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hAddBin : FidAddBinHyp Γ) (hAllocCl : FidAllocClHyp Γ) (hWPush : FidWPushHyp Γ)
    (hDelBin : FidDelBinHyp Γ) (hUnwatch : FidUnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s st1a : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv fresh : Val i32}
    {ok1a : Val .bool} {m1a : Mem 64} {bump : Nat}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hbk1 : 1 ≤ best_k.toNat) (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hmat : FidBvaMatrixInv c F_cur s (best_k.toNat + 1) bump)
    (hlay : Step7BvaLayout c s (best_k.toNat + 1))
    (hres : s.scratch.res_sz = BitVec.ofNat 64 best_k.toNat)
    (hsc_eq : sc.toNat = fidStepsCap c.scratch_cap)
    (hbo_getD : (s.scratch.scratch_buf[sc.toNat + best_k.toNat]?.getD 0#32).toNat = brow_off.toNat)
    (hmn_getD : (s.scratch.scratch_buf[2 * sc.toNat + best_k.toNat]?.getD 0#32).toNat = mn_bv.toNat)
    (hfresh_nat : fresh.toNat = 2 * s.core.cur_vars)
    (hfresh1 : (fresh ^^^ 1#32).toNat = 2 * s.core.cur_vars + 1)
    (resAt : Nat → List Nat)
    (hresAt : ∀ idx < mn_bv.toNat,
      (∀ x ∈ resAt idx, x < 2 * s.core.cur_vars) ∧ ((resAt idx).map (· / 2)).Nodup ∧
      FidBvaRowEntryOk F_cur s (s.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat
        (s.scratch.scratch_buf[brow_off.toNat + idx]?.getD 0#32) (resAt idx) ∧
      (cnfOfClauses F_next).EntailsClause (cnfClause ((2 * s.core.cur_vars + 1) :: resAt idx)))
    (hst1a : S7StOk c F0 F_next s st1a) (hm1a : (FullMem c st1a ⋆ R) m1a)
    (hQ : ∀ ok s' m', FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) →
      (ok = true → Step7BvaCommittedOk c s' best_k.toNat) → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (s7Phase1bExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr
      c.pTmp best_k sc dm_bv brow_off mn_bv fresh ok1a) m1a := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hsb_len := hsc.scratch_buf_len
  let old_cv := s.core.cur_vars
  have hsc_pos := hmat.1; have hbump_ge := hmat.2.2.2.1; have hbump_le := hmat.2.2.2.2.1
  have hsc4 := fidStepsCap_mul4_le c.scratch_cap
  have hbk_row := hmat.2.2.2.2.2 best_k.toNat (by omega)
  obtain ⟨hfbk_lt, hro_ge, hmn_lo, hro_mn, _, hbk_entries⟩ := hbk_row
  rw [← hsc_eq] at hro_ge hmn_lo hro_mn hbk_entries
  rw [hbo_getD] at hro_ge hro_mn hbk_entries
  rw [hmn_getD] at hmn_lo hro_mn hbk_entries
  unfold s7Phase1bExpr s7PostDefragExpr s7MidExpr s7PreMidExpr s7HdrExpr
  dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrp0, sGrp64_32, sGrp64_64_32,
    sGrp32b, sThen, sElse, sDummyTup, sDummyVal, i64, i32, FullFidelityStep7.full_bva_commit_body]
  refine wp_join_group (ts := [i32, .bool])
    (fun (_, ok1b, ()) m1b => ∃ st1b : FullState,
      S7StOk c F0 F_next s st1b ∧ (FullMem c st1b ⋆ R) m1b)
    (fun _ (mi1b, ok1b, ()) m1b ⟨st1b, hst1b, hm1b⟩ => ?_) (fun J1b hJ1b => ?_)
  · c0_hsteps_nogrp
    · have hp2 := s7_phase2_wp (Γ := Γ) (Q := Q) (X := X) hDelBin hUnwatch
        (F_next := F_next) (dm_bv := dm_bv) (brow_off := brow_off) (mn_bv := mn_bv)
        (fresh := fresh) (mi0 := mi1b) hinv hbk1 hbk_sc hmat hlay hres hsc_eq hmn_getD hfresh_nat
        hfresh1 hst1b hm1b hQ
      unfold s7Phase2Expr s7Phase1bExpr s7PostDefragExpr s7MidExpr
        s7PreMidExpr s7HdrExpr at hp2
      exact hp2
    · obtain ⟨hinv1b, hcv1b, hfuel1b, hsb1b, htm1b, htr1b, _⟩ := hst1b
      have hcl1b := hinv1b.1.core_ok; have hsc1b := hinv1b.1.scratch_ok
      have hcv1b_le : old_cv + 1 ≤ c.max_vars := by have := hcl1b.cur_vars_le; omega
      have h2cv : (BitVec.ofNat 64 st1b.core.cur_vars <<< (1 : Nat)).toNat = 2 * (old_cv + 1) := by
        rw [hcv1b]; simp only [bv_c0]; omega
      refine wp_loop_inv
        (fun (zi, ()) mzi => ∃ wsz : List (BitVec 32), zi.toNat ≤ 2 * (old_cv + 1) ∧
          wsz.length = 2 * c.max_vars ∧
          (FullMem c { st1b with scratch := { st1b.scratch with wsort := wsz } } ⋆ R) mzi)
        (fun (zi, _) _ => 2 * (old_cv + 1) - zi.toNat) (fun Jz hJz => by
          c0_hsteps; exact hJz (0#64, ()) m1b ⟨st1b.scratch.wsort, Nat.zero_le _, hsc1b.wsort_len,
            hm1b⟩)
        (fun Jz (zi, ()) mzi ⟨wsz, hzi_le, hwsz_l, hmzi⟩ ihz => ?_)
      c0_hsteps
      · have hzi_lt : zi.toNat < 2 * (old_cv + 1) := by
          have h1 : zi.toNat < (BitVec.ofNat 64 st1b.core.cur_vars <<< (1 : Nat)).toNat :=
            by assumption
          rwa [h2cv] at h1
        have hzi1 : (zi + 1#64).toNat = zi.toNat + 1 := by simp only [bv_c0]; omega
        c0_hsteps; exact ihz (zi + 1#64, ()) m (by dsimp only; rw [hzi1]; omega)
          ⟨_, by rw [hzi1]; omega, by simp [hwsz_l], hm⟩
      · c0_hsteps
        exact hQ false _ mzi (fullDenseInvW_set_wsort hinv1b hwsz_l).toDense
          (by dsimp only; omega) (fun h => absurd h (by decide))
          (fun h => absurd h (by decide)) hfuel1b htm1b htr1b hmzi
  · refine wp_loop_inv
      (fun (mi, okm, ()) mm => ∃ stm : FullState, mi.toNat ≤ mn_bv.toNat ∧
        S7StOk c F0 F_next s stm ∧ (FullMem c stm ⋆ R) mm)
      (fun (mi, _, _) _ => mn_bv.toNat - mi.toNat) (fun J1bl hJ1bl => by
        c0_hsteps; exact hJ1bl (0#32, ok1a, ()) m1a ⟨st1a, Nat.zero_le _, hst1a, hm1a⟩)
      (fun J1bl (mi, okm, ()) mm ⟨stm, hmi_le, hstm, hmm⟩ ihm => ?_)
    obtain ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩ := hstm
    have hclm := hinvm.1.core_ok; have hscm := hinvm.1.scratch_ok; c0_hsteps_nogrp
    · have hmi_lt : mi.toNat < mn_bv.toNat := by assumption
      have hokm_t : okm = true := by assumption
      subst hokm_t; have hmi1 : (mi + 1#32).toNat = mi.toNat + 1 := by c0_bound
      have hctop_idx : (brow_off + mi).toNat = brow_off.toNat + mi.toNat := by
        have h1 : (brow_off + mi).toNat = (brow_off + mi : BitVec 32).toNat := rfl
        rw [h1, BitVec.toNat_add]; apply Nat.mod_eq_of_lt; omega
      have hctop_sb : (BitVec.setWidth 64 (brow_off + mi)).toNat <
          stm.scratch.scratch_buf.length := by
        rw [bv64_setWidth_32, hctop_idx, hscm.scratch_buf_len]; omega
      let c_top := s.scratch.scratch_buf[brow_off.toNat + mi.toNat]'(by omega)
      have hctop_eq : stm.scratch.scratch_buf[(BitVec.setWidth 64
          (brow_off + mi)).toNat]'hctop_sb = c_top := by
        dsimp only [c_top]; simp only [hsbm, bv64_setWidth_32, hctop_idx]
      have hctop_mod_n : (brow_off.toNat + mi.toNat) % 2 ^ 32 =
          brow_off.toNat + mi.toNat := Nat.mod_eq_of_lt (by omega)
      have hctop_mod : stm.scratch.scratch_buf[(brow_off.toNat + mi.toNat) % 2 ^ 32]'(by
          rw [hctop_mod_n, hscm.scratch_buf_len]; omega) = c_top := by
        dsimp only [c_top]; simp only [hsbm, hctop_mod_n]
      obtain ⟨hresm_lt, hresm_nd, hctop_ok0, hresm_ent⟩ := hresAt mi.toNat hmi_lt
      let resm := resAt mi.toNat
      have hctop_getD : s.scratch.scratch_buf[brow_off.toNat + mi.toNat]?.getD 0#32 =
          c_top := by
        dsimp only [c_top]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hctop_ok : FidBvaRowEntryOk F_cur s
          (s.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat c_top resm :=
        hctop_getD ▸ hctop_ok0
      c0_hsteps_nogrp; refine wp_join_group (ts := [.bool])
        (fun (_ok', ()) m1 => ∃ st1 : FullState, (FullMem c st1 ⋆ R) m1 ∧
          S7StOk c F0 F_next s st1)
        (fun _ (ok', ()) m1 ⟨st1, hm1, hst1⟩ => by
          c0_hsteps; exact ihm (mi + 1#32, ok', ()) m1 (by dsimp only; rw [hmi1]; omega)
            ⟨st1, by rw [hmi1]; omega, hst1, hm1⟩)
        (fun Jtop hJtop => ?_)
      c0_hsplit
      · c0_hsteps
        have hbin_ct : (c_top &&& 0x80000000#32) ≠ 0#32 := by
          simpa only [← hctop_mod] using (by assumption : _)
        unfold FidBvaRowEntryOk at hctop_ok; rw [ite_eq_left hbin_ct] at hctop_ok
        obtain ⟨hq_lt, hres_q, _⟩ := hctop_ok; c0_call hAddBin
        refine ⟨c, F0, F_next, stm, R, rfl, hinvm.1, hinvm.2.1, hinvm.2.2.2.2.2.1,
          fun _ _ => ?_, hmm,
          fun _ _ fl1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 hlen1' hw1' _ _ _ hms1' => ?_⟩
        · rw [hctop_eq]; dsimp only [resm] at hres_q; rw [hres_q] at hresm_ent
          simpa only [show (1 : BitVec 32) = 1#32 from rfl, hfresh1,
            show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl] using hresm_ent
        · have hinv1' := fullDenseInvW_of_addBin hinvm hlen1' hw1'
          have hfl1 : fl1.length = c.max_vars := hlen1'.core_ok.flags_len
          have hcvm_lt : old_cv < c.max_vars := by have := hclm.cur_vars_le; omega
          have hfr_shr : (BitVec.setWidth 64 (fresh >>> (1 : BitVec 32))).toNat < fl1.length := by
            rw [bv64_setWidth_32, bv32_lshr1_bv, hfl1, hfresh_nat]; omega
          have hfr_shr_n : (BitVec.setWidth 64 (fresh >>> (1 : Nat))).toNat < fl1.length := by
            rw [bv64_setWidth_32, bv32_lshr1_nat, hfl1, hfresh_nat]; omega
          have hq_shr : (BitVec.setWidth 64 ((stm.scratch.scratch_buf[(BitVec.setWidth 64
              (brow_off + mi)).toNat]'hctop_sb &&& 2147483647) >>> (1 : BitVec 32))).toNat <
              c.max_vars := by
            rw [bv64_setWidth_32, hctop_eq, bv32_lshr1_bv,
              show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl]; omega
          have hq_shr_n : (BitVec.setWidth 64 ((stm.scratch.scratch_buf[(BitVec.setWidth 64
              (brow_off + mi)).toNat]'hctop_sb &&& 2147483647) >>> (1 : Nat))).toNat <
              c.max_vars := by
            rw [bv64_setWidth_32, hctop_eq, bv32_lshr1_nat,
              show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl]; omega
          have hlen2 : ∀ (i j : Nat) (v w : BitVec 32),
              ((fl1.set i v).set j w).length = c.max_vars := fun _ _ _ _ => by simp [hfl1]
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i32]) (fun (_, ()) mf => mf = m)
            (fun _ _ mf hmf => ?_) (fun Jt hJt => by
              c0_hsteps
              · exact hJt _ m rfl
              · exact hJt _ m rfl)
          subst hmf
          c0_hsteps
          all_goals first
            | exact hJ1b (mi, false, ()) _ ⟨_, ⟨fullDenseInvW_set_flags hinv1' (hlen2 _ _ _ _),
                hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩, hm⟩
            | exact hJtop (true, ()) _ ⟨_, hm, fullDenseInvW_set_flags hinv1' (hlen2 _ _ _ _),
                hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩
      · have hbin_ct : (c_top &&& 0x80000000#32) = 0#32 := by
          simpa only [← hctop_mod] using (by assumption : _)
        unfold FidBvaRowEntryOk at hctop_ok
        rw [ite_eq_right (fun h' => h' hbin_ct)] at hctop_ok
        obtain ⟨hct_ref0, hct_ng0, hct_sz3, _, hfbk_mem, hres_perm_f, _⟩ := hctop_ok
        have hlt := s7_bva_large_top_wp (Γ := Γ) (Q := Q) (X := X) hAllocCl hWPush hUnwatch
          (F_next := F_next) (best_k := best_k) (mi := mi) (resm := resm)
          (c_top := stm.scratch.scratch_buf[(BitVec.setWidth 64
            (brow_off + mi)).toNat]'hctop_sb)
          (fresh := fresh) (J4 := J1b) (J6 := Jtop) hinv (by omega) hfresh1 hresm_lt
          hresm_nd hresm_ent (by rwa [hctop_eq]) (by rwa [hctop_eq]) (by rwa [hctop_eq])
          (by rwa [hctop_eq]) (by rwa [hctop_eq]) hmm
          ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩
          (fun st1 m1 hm1 hst1 => hJ1b (mi, false, ()) m1 ⟨st1, hst1, hm1⟩)
          (fun ok' st1 m1 hm1 hst1 => hJtop (ok', ()) m1 ⟨st1, hm1, hst1⟩)
        unfold fidBvaLargeTopExpr fidBvaLargeWatchExpr fidBZext fidBOp64 fidBOp32 fidBCmp32
          fidBPtr32 fidBLd32 at hlt
        exact hlt
    · exact hJ1b (mi, okm, ()) mm ⟨stm, ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩, hmm⟩
    · exact hJ1b (mi, okm, ()) mm ⟨stm, ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩, hmm⟩

private theorem s7_post_defrag_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hInitFresh : ∀ args m Q X, step7InitFreshVarSpec args m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] args m Q X)
    (hAddBin : FidAddBinHyp Γ) (hAllocCl : FidAllocClHyp Γ) (hWPush : FidWPushHyp Γ)
    (hDelBin : FidDelBinHyp Γ) (hUnwatch : FidUnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sd : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv : Val i32} {md : Mem 64} {bump : Nat}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hbk1 : 1 ≤ best_k.toNat) (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hmat : FidBvaMatrixInv c F_cur s (best_k.toNat + 1) bump)
    (hlay : Step7BvaLayout c s (best_k.toNat + 1))
    (hres : s.scratch.res_sz = BitVec.ofNat 64 best_k.toNat)
    (hcv_lt : s.core.cur_vars < c.max_vars)
    (hsc_eq : sc.toNat = fidStepsCap c.scratch_cap)
    (hdm_bv : dm_bv.toNat = best_k.toNat + 1)
    (hbo_getD : (s.scratch.scratch_buf[sc.toNat + best_k.toNat]?.getD 0#32).toNat = brow_off.toNat)
    (hmn_getD : (s.scratch.scratch_buf[2 * sc.toNat + best_k.toNat]?.getD 0#32).toNat = mn_bv.toNat)
    (hmd : (FullMem c sd ⋆ R) md) (hsd : S7PreOk c F0 F_cur s sd)
    (hQ : ∀ ok s' m', FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) →
      (ok = true → Step7BvaCommittedOk c s' best_k.toNat) → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (s7PostDefragExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec
      best_k sc dm_bv brow_off mn_bv) md := by
  obtain ⟨hinvd, hcvd, hfueld, hard, hald, hsbd, htmd, htrd, hresd⟩ := hsd
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hsb_len := hsc.scratch_buf_len
  have hsc_pos := hmat.1; have hbump_ge := hmat.2.2.2.1; have hbump_le := hmat.2.2.2.2.1
  have hsc4 := fidStepsCap_mul4_le c.scratch_cap
  have hbk_row := hmat.2.2.2.2.2 best_k.toNat (by omega)
  obtain ⟨hfbk_lt, hro_ge, hmn_lo, hro_mn, _, hbk_entries⟩ := hbk_row
  rw [← hsc_eq] at hro_ge hmn_lo hro_mn hbk_entries
  rw [hbo_getD] at hro_ge hro_mn hbk_entries
  rw [hmn_getD] at hmn_lo hro_mn hbk_entries
  let dm := best_k.toNat + 1
  unfold s7PostDefragExpr s7MidExpr s7PreMidExpr s7HdrExpr
  dsimp only [sSteps, sStep,
    sLet32, sLd64, sLd32, sCall32, sGrp0, sGrp64_32, sGrp64_64_32, sThen, sElse, sDummyTup,
    sDummyVal, i64, i32, FullFidelityStep7.full_bva_commit_body]
  have hcld := hinvd.1.core_ok; have hscd := hinvd.1.scratch_ok; let old_cv := s.core.cur_vars
  have hfv_nat : (BitVec.setWidth 32 (BitVec.ofNat 64 sd.core.cur_vars)).toNat = old_cv := by
    rw [hcvd]; c0_bound
  have hcv1_nat : (BitVec.ofNat 64 sd.core.cur_vars + 1).toNat = old_cv + 1 := by
    change (BitVec.ofNat 64 sd.core.cur_vars + 1#64).toNat = _; rw [hcvd]; c0_bound
  c0_hsteps
  let sd_inc : FullState := { sd with core := { sd.core with cur_vars := old_cv + 1 } }
  have hmd_inc : (FullMem c sd_inc ⋆ R) m := by dsimp only [sd_inc]; rw [hcv1_nat] at hm; exact hm
  c0_call hInitFresh; refine ⟨c, sd_inc, R, rfl, ⟨{ hcld with
         cur_vars_ge := by have := hcld.cur_vars_ge; dsimp only [sd_inc, old_cv]; omega
         cur_vars_le := by dsimp only [sd_inc, old_cv]; omega
         trail_end_le := by have := hcld.trail_end_le; dsimp only [sd_inc, old_cv]; omega },
     hscd⟩,
    by dsimp only [sd_inc, old_cv]; rw [hfv_nat]; omega, hmd_inc,
    fun vals' mrk' fl' lvl' rsns' wvec' unass' sc' m1 hlen1 hext1 hsb1 hws1 htm1 htr1 hss1 hres1
      hv0 hv1 hv_oth hm0 hm_oth hl0 hl_oth hr0 hr_oth hw0 hw_oth hm1 => ?_⟩
  let L : List Nat := (List.range dm).map fun t => (s.scratch.scratch_buf[t]?.getD 0#32).toNat
  let resAt (idx : Nat) : List Nat :=
    if h : idx < mn_bv.toNat then Classical.choose (hbk_entries idx h) else []
  let Qs : List (List Nat) := (List.range mn_bv.toNat).map resAt
  have hL_lt : ∀ f ∈ L, f < 2 * old_cv := by
    intro f hf; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hf
    rw [List.mem_range] at ht; exact (hmat.2.2.2.2.2 t (by omega)).1
  have hQ_lt : ∀ C ∈ Qs, ∀ l ∈ C, l < 2 * old_cv := by
    intro C hC l hl; obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hC
    rw [List.mem_range] at hidx; dsimp only [resAt] at hl; rw [dite_eq_left hidx] at hl
    exact (Classical.choose_spec (hbk_entries idx hidx)).1 l hl
  have hprod : ∀ f ∈ L, ∀ C ∈ Qs, (cnfOfClauses F_cur).EntailsClause (cnfClause (f :: C)) := by
    intro f hf C hC; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hf; rw [List.mem_range] at ht
    obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hC; rw [List.mem_range] at hidx
    dsimp only [resAt]; rw [dite_eq_left hidx]
    exact (Classical.choose_spec (hbk_entries idx hidx)).2.2.2.1 t (by omega)
  let F_next := bvaExtendGen old_cv L Qs F_cur
  let s1 : FullState :=
    { sd_inc with core := { sd_inc.core with vals := vals', mrk := mrk', flags := fl', lvl := lvl',
                                             rsns := rsns', wvec := wvec', unassigned := unass' }
                  scratch := sc' }
  have hcore1 : s1.core =
      { sd.core with cur_vars := sd.core.cur_vars + 1, vals := vals', mrk := mrk',
                     flags := fl', lvl := lvl', rsns := rsns', wvec := wvec',
                     unassigned := unass' } := by dsimp only [s1, sd_inc, old_cv]; rw [hcvd]
  have ⟨hw1, hd1⟩ := fullDenseInv_add_fresh_var_gen (s := sd) (s' := s1)
    hinvd.1 hinvd.2.1 hinvd.2.2.1 hinvd.2.2.2.1 hinvd.2.2.2.2.1 hinvd.2.2.2.2.2.1
    hinvd.2.2.2.2.2.2 (by rw [hcvd]; exact hcv_lt)
    (by rw [hcvd]; exact hL_lt) (by rw [hcvd]; exact hQ_lt) hprod hlen1 hcore1
    (by rw [hfv_nat] at hv0; rwa [hcvd]) (by rw [hfv_nat] at hv1; rwa [hcvd])
    (by intro l hl hne; exact hv_oth l hl (by rw [hfv_nat]; dsimp only [old_cv]; rwa [← hcvd]))
    (by rw [hfv_nat] at hm0; rwa [hcvd])
    (by intro v hv hne; exact hm_oth v hv (by rw [hfv_nat]; dsimp only [old_cv]; rwa [← hcvd]))
    (by intro v hv hne; exact hl_oth v hv (by rw [hfv_nat]; dsimp only [old_cv]; rwa [← hcvd]))
    (by intro v hv hne; exact hr_oth v hv (by rw [hfv_nat]; dsimp only [old_cv]; rwa [← hcvd]))
    (by intro k hk; rw [hfv_nat] at hw0; rw [hcvd]; exact hw0 k hk)
    (by intro i hi hne; exact hw_oth i hi (by rw [hfv_nat]; dsimp only [old_cv]; rwa [← hcvd]))
    hext1.1 hext1.2
  have hinv1 : FullDenseInvW c F0 F_next s1 :=
    ⟨hlen1, by rwa [hcvd] at hw1, hd1.2.1, hd1.2.2.1, hd1.2.2.2.1, hd1.2.2.2.2.1, hd1.2.2.2.2.2⟩
  have hpos_ent : ∀ f ∈ L, (cnfOfClauses F_next).EntailsClause (cnfClause [2 * old_cv, f]) :=
    fun _ hf => bvaExtendGen_entails_pos hf
  have hneg_ent : ∀ R ∈ Qs, (cnfOfClauses F_next).EntailsClause (cnfClause ((2 * old_cv + 1) ::
    R)) :=
    fun _ hR => bvaExtendGen_entails_neg hR
  let fv_bv := BitVec.setWidth 32 (BitVec.ofNat 64 sd.core.cur_vars)
  have hfresh_nat : (fv_bv <<< (1 : Nat)).toNat = 2 * old_cv := by
    rw [bv32_shl1_nat, hfv_nat, Nat.mod_eq_of_lt (by omega)]
  have hfresh_bv : (fv_bv <<< (1 : BitVec 32)).toNat = 2 * old_cv := by
    rw [bv32_shl1_bv, hfv_nat, Nat.mod_eq_of_lt (by omega)]
  have hfresh1_nat : ((fv_bv <<< (1 : Nat)) ^^^ 1#32).toNat = 2 * old_cv + 1 := by
    rw [bv32_shl1_xor1 (by rw [hfv_nat]; omega), hfv_nat]
  have hfresh1_bv : ((fv_bv <<< (1 : BitVec 32)) ^^^ (1 : BitVec 32)).toNat = 2 * old_cv + 1 := by
    have hev : (fv_bv <<< (1 : BitVec 32)) = fv_bv <<< (1 : Nat) := by
      apply BitVec.eq_of_toNat_eq; rw [bv32_shl1_bv, bv32_shl1_nat]
    rw [hev]; exact hfresh1_nat
  have hfv2_rp_bv : (BitVec.setWidth 64 (fv_bv <<< (1 : BitVec 32))).toNat <
      sd.core.repr.length := by
    rw [bv64_setWidth_32, hfresh_bv, hcld.repr_len]; omega
  have hfv2_rp_n : (BitVec.setWidth 64 (fv_bv <<< (1 : Nat))).toNat < sd.core.repr.length := by
    rw [bv64_setWidth_32, hfresh_nat, hcld.repr_len]; omega
  have hfv21_rp :
      (BitVec.setWidth 64 ((fv_bv <<< (1 : BitVec 32)) ||| 1#32)).toNat < sd.core.repr.length := by
    have hev : (fv_bv <<< (1 : BitVec 32)) = fv_bv <<< (1 : Nat) := by
      apply BitVec.eq_of_toNat_eq; rw [bv32_shl1_bv, bv32_shl1_nat]
    rw [hev, bv64_setWidth_32, bv32_shl1_or1 (by rw [hfv_nat]; omega), hfv_nat, hcld.repr_len]
    omega
  have hfv21_rp_n :
      (BitVec.setWidth 64 ((fv_bv <<< (1 : Nat)) ||| 1#32)).toNat < sd.core.repr.length := by
    rw [bv64_setWidth_32, bv32_shl1_or1 (by rw [hfv_nat]; omega), hfv_nat, hcld.repr_len]; omega
  have hfv2_ws : (BitVec.setWidth 64 (fv_bv <<< (1 : BitVec 32))).toNat < sc'.wsort.length := by
    rw [bv64_setWidth_32, hfresh_bv, hlen1.scratch_ok.wsort_len]; omega
  have hfv2_ws_n : (BitVec.setWidth 64 (fv_bv <<< (1 : Nat))).toNat < sc'.wsort.length := by
    rw [bv64_setWidth_32, hfresh_nat, hlen1.scratch_ok.wsort_len]; omega
  have hfv21_ws :
      (BitVec.setWidth 64 ((fv_bv <<< (1 : BitVec 32)) ||| 1#32)).toNat < sc'.wsort.length := by
    have hev : (fv_bv <<< (1 : BitVec 32)) = fv_bv <<< (1 : Nat) := by
      apply BitVec.eq_of_toNat_eq; rw [bv32_shl1_bv, bv32_shl1_nat]
    rw [hev, bv64_setWidth_32, bv32_shl1_or1 (by rw [hfv_nat]; omega), hfv_nat,
      hlen1.scratch_ok.wsort_len]
    omega
  have hfv21_ws_n :
      (BitVec.setWidth 64 ((fv_bv <<< (1 : Nat)) ||| 1#32)).toNat < sc'.wsort.length := by
    rw [bv64_setWidth_32, bv32_shl1_or1 (by rw [hfv_nat]; omega), hfv_nat,
      hlen1.scratch_ok.wsort_len]
    omega
  c0_hsteps_nogrp
  let repr0 :=
    (sd.core.repr.set (BitVec.setWidth 64 (fv_bv <<< (OfNat.ofNat 1 : BitVec 32))).toNat 0#32).set
      (BitVec.setWidth 64 ((fv_bv <<< (OfNat.ofNat 1 : BitVec 32)) ||| 1#32)).toNat 0#32
  let wsort0 :=
    (sc'.wsort.set (BitVec.setWidth 64 (fv_bv <<< (OfNat.ofNat 1 : BitVec 32))).toNat 0#32).set
      (BitVec.setWidth 64 ((fv_bv <<< (OfNat.ofNat 1 : BitVec 32)) ||| 1#32)).toNat 0#32
  let st0 : FullState :=
    { core := { sd.core with cur_vars := old_cv + 1, vals := vals', mrk := mrk', flags := fl',
                             lvl := lvl', rsns := rsns', wvec := wvec', unassigned := unass',
                             repr := repr0 }
      scratch := { sc' with wsort := wsort0 } }
  have hrp0_len : repr0.length = 2 * c.max_vars := by
    dsimp only [repr0]; simp [hcld.repr_len]
  have hws0_len : wsort0.length = 2 * c.max_vars := by
    dsimp only [wsort0]; simp [hlen1.scratch_ok.wsort_len]
  have hinv0 : FullDenseInvW c F0 F_next st0 :=
    fullDenseInv_with_core_aux (tc' := sd.core.tmp_cnt) (tl' := sd.core.tmp_len)
      hinv1 hrp0_len hcld.min_clr_len_arr hcld.tmp_len_arr hlen1.core_ok.flags_len hcld.tmp_len_le
      { hlen1.scratch_ok with wsort_len := hws0_len } rfl rfl
  have hmono0 : FidBvaArenaMono s.core st0.core := fun r hr => by
    change r ∈ fullArenaClauseRefsCore { sd.core with arena := sd.core.arena } ∧ _
    have h1 : fullArenaClauseRefsCore { sd.core with arena := sd.core.arena } =
        fullArenaClauseRefsCore s.core := by unfold fullArenaClauseRefsCore; rw [hard, hald]
    refine ⟨by rw [h1]; exact hr, ?_, ?_⟩
    · unfold fullArenaClauseSizeCore; rw [hard]
    · unfold fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [hard]
  refine wp_join_group (ts := [i32, .bool])
    (fun (_, ok1a, ()) m1a => ∃ st1a : FullState,
      S7StOk c F0 F_next s st1a ∧ (FullMem c st1a ⋆ R) m1a)
    (fun _ (_, ok1a, ()) m1a ⟨st1a, hst1a, hm1a⟩ => ?_) (fun J1a hJ1a => ?_)
  · have hp1b := s7_phase1b_wp (Γ := Γ) (Q := Q) (X := X)
      hAddBin hAllocCl hWPush hDelBin hUnwatch (F_next := F_next)
      (dm_bv := dm_bv) (brow_off := brow_off) (mn_bv := mn_bv)
      (fresh := fv_bv <<< (OfNat.ofNat 1 : BitVec 32)) (ok1a := ok1a)
      hinv hbk1 hbk_sc hmat hlay hres hsc_eq hbo_getD hmn_getD hfresh_bv hfresh1_bv resAt
      (fun idx hidx => by
        have hspec := Classical.choose_spec (hbk_entries idx hidx)
        have heq : resAt idx = Classical.choose (hbk_entries idx hidx) := by
          dsimp only [resAt]; rw [dite_eq_left hidx]
        rw [heq]; refine ⟨hspec.1, hspec.2.1, hspec.2.2.1, ?_⟩
        have hmem : resAt idx ∈ Qs := List.mem_map.mpr ⟨idx, List.mem_range.mpr hidx, rfl⟩
        have h1 := hneg_ent (resAt idx) hmem; rwa [heq] at h1)
      hst1a hm1a hQ
    unfold s7Phase1bExpr s7PostDefragExpr s7MidExpr s7PreMidExpr s7HdrExpr
      at hp1b
    dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrp0, sGrp64_32, sGrp64_64_32,
      sGrp32b, sThen, sElse, sDummyTup, sDummyVal, i64, i32,
      FullFidelityStep7.full_bva_commit_body] at hp1b
    exact hp1b
  · refine wp_loop_inv
      (fun (si, ()) msi => ∃ sts : FullState, si.toNat ≤ dm ∧
        S7StOk c F0 F_next s sts ∧ (FullMem c sts ⋆ R) msi)
      (fun (si, _) _ => dm - si.toNat) (fun Js hJs => by
        c0_hfast; exact hJs (0#32, ()) m ⟨st0, Nat.zero_le _,
          ⟨hinv0, rfl, hfueld, hsb1.trans hsbd, htm1.trans htmd, htr1.trans htrd, hmono0,
            hres1.trans hresd⟩, hm⟩)
      (fun Js (si, ()) msi ⟨sts, hsi_le, hsts, hmsi⟩ ihs => ?_)
    obtain ⟨hinvs, hcvs, hfuels, hsbs, htms, htrs, hmonos, hress⟩ := hsts
    have hcls := hinvs.1.core_ok; have hscs := hinvs.1.scratch_ok; c0_hsplit
    · have hsi_lt : si.toNat < dm := by
        have h1 : si.toNat < dm_bv.toNat := (by assumption); omega
      have hsi1 : (si + 1#32).toNat = si.toNat + 1 := by simp only [bv_c0]; omega
      have hfs_sb : (BitVec.setWidth 64 si).toNat < sts.scratch.scratch_buf.length := by
        rw [bv64_setWidth_32, hscs.scratch_buf_len]; omega
      have hfs_getD : (sts.scratch.scratch_buf[(BitVec.setWidth 64 si).toNat]'hfs_sb).toNat =
          (s.scratch.scratch_buf[si.toNat]?.getD 0#32).toNat := by
        have h1 : sts.scratch.scratch_buf[(BitVec.setWidth 64 si).toNat]? =
            s.scratch.scratch_buf[si.toNat]? := by rw [hsbs, bv64_setWidth_32]
        rw [← h1, List.getElem?_eq_getElem hfs_sb, Option.getD_some]
      have hfs_lt : (sts.scratch.scratch_buf[(BitVec.setWidth 64 si).toNat]'hfs_sb).toNat <
          2 * old_cv := by
        rw [hfs_getD]; exact hL_lt _ (List.mem_map.mpr ⟨si.toNat, List.mem_range.mpr hsi_lt, rfl⟩)
      c0_hfast; c0_call hAddBin
      refine ⟨c, F0, F_next, sts, R, rfl, hinvs.1, hinvs.2.1, hinvs.2.2.2.2.2.1,
        fun _ _ => by
          have hfr_g : (BitVec.setWidth 32 (BitVec.ofNat 64 sd.core.cur_vars) <<<
              OfNat.ofNat 1).toNat = 2 * old_cv := hfresh_bv
          rw [hfr_g, hfs_getD]
          exact hpos_ent _ (List.mem_map.mpr ⟨si.toNat, List.mem_range.mpr hsi_lt, rfl⟩),
        hmsi, fun _ _ fl_s1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ms1 hlen_s1 hw_s1 _ _ _ hms1 => ?_⟩
      have hinv_s1 := fullDenseInvW_of_addBin hinvs hlen_s1 hw_s1
      have hfl_s1 : fl_s1.length = c.max_vars := hlen_s1.core_ok.flags_len
      have hfs_shr : (BitVec.setWidth 64 ((sts.scratch.scratch_buf[(BitVec.setWidth 64
          si).toNat]'hfs_sb) >>> (1 : BitVec 32))).toNat < fl_s1.length := by
        rw [bv64_setWidth_32, bv32_lshr1_bv, hfl_s1]; omega
      have hfs_shr_n : (BitVec.setWidth 64 ((sts.scratch.scratch_buf[(BitVec.setWidth 64
          si).toNat]'hfs_sb) >>> (1 : Nat))).toNat < fl_s1.length := by
        rw [bv64_setWidth_32, bv32_lshr1_nat, hfl_s1]; omega
      have hfr_shr : (BitVec.setWidth 64 ((fv_bv <<< (OfNat.ofNat 1 : BitVec 32)) >>>
          (1 : BitVec 32))).toNat < c.max_vars := by
        rw [bv64_setWidth_32, bv32_lshr1_bv, hfresh_bv]; omega
      have hfr_shr_n : (BitVec.setWidth 64 ((fv_bv <<< (OfNat.ofNat 1 : BitVec 32)) >>>
          (1 : Nat))).toNat < c.max_vars := by
        rw [bv64_setWidth_32, bv32_lshr1_nat, hfresh_bv]; omega
      c0_hfast
      all_goals first
        | exact hJ1a (si, false, ()) ms1
            ⟨_, ⟨hinv_s1, hcvs, hfuels, hsbs, htms, htrs, hmonos, hress⟩, hms1⟩
        | exact ihs (si + 1#32, ()) m (by dsimp only; rw [hsi1]; omega)
            ⟨_, by rw [hsi1]; omega,
             ⟨fullDenseInvW_set_flags hinv_s1 (by simp [hfl_s1]),
              hcvs, hfuels, hsbs, htms, htrs, hmonos, hress⟩, hm⟩
    · exact hJ1a (si, true, ()) msi
        ⟨sts, ⟨hinvs, hcvs, hfuels, hsbs, htms, htrs, hmonos, hress⟩, hmsi⟩

/-! ## 4. Top-Level Exported `full_bva_commit_step7_wp` (`step7BvaCommitSpec`) -/

private theorem s7_pre_exit_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hDefrag : ∀ args m Q X, Full.fullWstackDefragSpec args m Q X →
      Γ "full_wstack_defrag" [i64] [] args m Q X)
    (hInitFresh : ∀ args m Q X, step7InitFreshVarSpec args m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] args m Q X)
    (hAddBin : FidAddBinHyp Γ) (hAllocCl : FidAllocClHyp Γ) (hWPush : FidWPushHyp Γ)
    (hDelBin : FidDelBinHyp Γ) (hUnwatch : FidUnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv : Val i32}
    {need_ar need_w : Val i64} {m : Mem 64} {bump : Nat}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hbk1 : 1 ≤ best_k.toNat) (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hmat : FidBvaMatrixInv c F_cur s (best_k.toNat + 1) bump)
    (hlay : Step7BvaLayout c s (best_k.toNat + 1))
    (hres : s.scratch.res_sz = BitVec.ofNat 64 best_k.toNat)
    (hsc_eq : sc.toNat = fidStepsCap c.scratch_cap)
    (hdm_bv : dm_bv.toNat = best_k.toNat + 1)
    (hbo_getD :
      (s.scratch.scratch_buf[sc.toNat + best_k.toNat]?.getD 0#32).toNat = brow_off.toNat)
    (hmn_getD :
      (s.scratch.scratch_buf[2 * sc.toNat + best_k.toNat]?.getD 0#32).toNat = mn_bv.toNat)
    (hm : (FullMem c s ⋆ R) m) (hcv_lt : s.core.cur_vars < c.max_vars)
    (hQ : ∀ ok s' m', FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) →
      (ok = true → Step7BvaCommittedOk c s' best_k.toNat) → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (s7PreExitExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec
      best_k sc dm_bv brow_off mn_bv need_ar need_w) m := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  unfold s7PreExitExpr s7PreMidExpr s7HdrExpr
  dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrp0, sGrp64_32,
    sGrp64_64_32, sGrp64_64_32v, sThen, sElse, sDummyTup, sDummyVal, i64, i32,
    FullFidelityStep7.full_bva_commit_body]
  refine wp_join_state0 (α := FullState) (fun sd md => (FullMem c sd ⋆ R) md ∧
    S7PreOk c F0 F_cur s sd)
    (fun _ sd md ⟨hmd, hsd⟩ => ?_) (fun Jdef hJdef => ?_)
  · have hpd := s7_post_defrag_wp (Γ := Γ) (Q := Q) (X := X)
      hInitFresh hAddBin hAllocCl hWPush hDelBin hUnwatch
      (sc := sc) (dm_bv := dm_bv) (brow_off := brow_off) (mn_bv := mn_bv)
      hinv hbk1 hbk_sc hmat hlay hres hcv_lt hsc_eq hdm_bv hbo_getD hmn_getD hmd hsd hQ
    unfold s7PostDefragExpr s7MidExpr s7PreMidExpr s7HdrExpr at hpd
    dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrp0, sGrp64_32,
      sGrp64_64_32, sThen, sElse, sDummyTup, sDummyVal, i64, i32,
      FullFidelityStep7.full_bva_commit_body] at hpd
    exact hpd
  · refine wp_join_state0 (α := Unit) (fun _ md => md = m)
      (fun _ _ md hmd => ?_) (fun Jneed hJneed => ?_)
    · subst md; refine wp_join_state0 (α := FullState)
        (fun sd md => (FullMem c sd ⋆ R) md ∧ S7PreOk c F0 F_cur s sd)
        (fun _ sd md ⟨hmd, hinvd, hcvd, hfueld, hard, hald, hsbd, htmd, htrd, hresd⟩ => ?_)
        (fun Jd1 hJd1 => ?_)
      · refine wp_join_state0 (α := Unit) (fun _ mf => mf = md)
          (fun _ _ mf hmf => ?_) (fun Jfail hJfail => ?_)
        · subst mf; c0_hsteps_nogrp
          have h2cv : (BitVec.ofNat 64 sd.core.cur_vars <<< (1 : Nat)).toNat =
              2 * s.core.cur_vars := by rw [hcvd]; simp only [bv_c0]; omega
          refine wp_loop_inv
            (fun (zi, ()) mzi => ∃ wsz : List (BitVec 32),
              zi.toNat ≤ 2 * s.core.cur_vars ∧ wsz.length = 2 * c.max_vars ∧
              (FullMem c { sd with scratch := { sd.scratch with wsort := wsz } } ⋆ R) mzi)
            (fun (zi, _) _ => 2 * s.core.cur_vars - zi.toNat) (fun Jz hJz => ?_)
            (fun Jz (zi, ()) mzi ⟨wsz, hzi_le, hwsz_l, hmzi⟩ ihz => ?_)
          · c0_hstep; exact hJz (0#64, ()) md
              ⟨sd.scratch.wsort, Nat.zero_le _, hinvd.1.scratch_ok.wsort_len, hmd⟩
          c0_hsplit
          · have hzi_lt : zi.toNat < 2 * s.core.cur_vars := by
              have h1 : zi.toNat < (BitVec.ofNat 64 sd.core.cur_vars <<< (1 :
                Nat)).toNat :=
                by assumption
              rwa [h2cv] at h1
            have hzi1 : (zi + 1#64).toNat = zi.toNat + 1 := by c0_bound
            c0_hfast; exact ihz (zi + 1#64, ()) m (by dsimp only; rw [hzi1]; omega)
              ⟨_, by rw [hzi1]; omega, by simp [hwsz_l], hm⟩
          · c0_hfast
            exact hQ false _ mzi (fullDenseInvW_set_wsort hinvd hwsz_l).toDense
              (by dsimp only; omega) (fun h => absurd h (by decide))
              (fun h => absurd h (by decide))
              hfueld htmd htrd hmzi
        · c0_hfast
          · exact hJfail () md rfl
          · exact hJfail () md rfl
          · exact hJdef sd md
              ⟨hmd, hinvd, hcvd, hfueld, hard, hald, hsbd, htmd, htrd, hresd⟩
      · c0_hsplit
        · c0_call hDefrag
          refine ⟨c, s, R, rfl, hinv.1, hinv.2.1.watches.layout, hm,
            fun wvec' wstk' wlen' wsort' md hlen' hlay' _ hsl' hmd =>
              hJd1 _ md ⟨hmd, fullDenseInvW_of_defrag hinv hlen' hlay' hsl',
                rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
        · c0_hstep
          exact hJd1 s m ⟨hm, hinv, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · c0_hsplit
      · c0_hstep
        exact hJneed () m rfl
      · c0_hsplit
        · c0_hstep
          exact hJneed () m rfl
        · c0_hstep
          exact hJdef s m ⟨hm, hinv, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Step-7 `full_bva_commit` (row compaction + per-row deletion sweep, `FL_FACT_P` / `FL_FACT_N`
flag updates) satisfies `step7BvaCommitSpec` parametrically in `Γ`; `full_init_fresh_var` must
satisfy the `res_sz`-preserving `step7InitFreshVarSpec`. -/
theorem full_bva_commit_step7_wp (Γ : Env)
    (hStepsCap : ∀ args m Q X, fidBvaStepsCapSpec args m Q X →
      Γ "full_bva_steps_cap_fid" [i64] [i32] args m Q X)
    (hDefrag : ∀ args m Q X, Full.fullWstackDefragSpec args m Q X →
      Γ "full_wstack_defrag" [i64] [] args m Q X)
    (hInitFresh : ∀ args m Q X, step7InitFreshVarSpec args m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] args m Q X)
    (hAddBin : ∀ args m Q X, Full.fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X)
    (hAllocCl : ∀ args m Q X, Full.fullAllocClSpec args m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] args m Q X)
    (hWPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hDelBin : ∀ args m Q X, Full.fullDeleteBinarySpec args m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] args m Q X)
    (hUnwatch : ∀ args m Q X, Full.fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, step7BvaCommitSpec args m Q X →
      Func.wp Γ FullFidelityStep7.full_bva_commit_body args m Q X := by
  rintro ⟨h, best_k, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, bump, rfl, hinv, hbk1, hbk_sc, ⟨hmat, hlay⟩, hres, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hsb_len := hsc.scratch_buf_len; have hwv_len := hcl.wvec_len
  have hsc_pos := hmat.1; have hsc_le256 := fidStepsCap_le_256 c.scratch_cap
  have hsc4 := fidStepsCap_mul4_le c.scratch_cap
  have hbump_ge := hmat.2.2.2.1; have hbump_le := hmat.2.2.2.2.1
  have hbk_row := hmat.2.2.2.2.2 best_k.toNat (by omega)
  obtain ⟨hfbk_lt, hro_ge, hmn_lo, hro_mn, _, hbk_entries⟩ := hbk_row
  c0_hsteps_nogrp
  · exact hQ false s m hinv.toDense (Nat.le_refl _) (fun h => absurd h (by decide))
          (fun h => absurd h (by decide)) rfl rfl rfl hm
  · apply wp_call_of_spec; apply hStepsCap; unfold fidBvaStepsCapSpec; dsimp only [vals, Arg.val]
    have hcap64 : (BitVec.ofNat 64 c.scratch_cap).toNat = c.scratch_cap := by c0_bound
    generalize hsc_def :
      BitVec.ofNat 32 (fidStepsCap (BitVec.ofNat 64 c.scratch_cap).toNat) = sc
    have hsc_nat : sc.toNat = fidStepsCap c.scratch_cap := by
      rw [← hsc_def, hcap64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hbk_sc_bv : best_k.toNat < sc.toNat := by omega
    have hsc_ne0 : sc ≠ 0#32 := by
      intro h; have := congrArg BitVec.toNat h
      rw [hsc_nat, show (0#32 : BitVec 32).toNat = 0 from rfl] at this; omega
    have hdm_bv : (best_k + 1#32).toNat = best_k.toNat + 1 := by simp only [bv_c0]; omega
    have hsc_bk : (sc + best_k).toNat = sc.toNat + best_k.toNat := by c0_bound
    have h2sc_bk : (2 * sc + best_k).toNat = 2 * sc.toNat + best_k.toNat := by
      have h2 : (2 * sc).toNat = 2 * sc.toNat := by
        change ((2#32 : BitVec 32) * sc).toNat = _; rw [BitVec.toNat_mul]
        have : (2#32 : BitVec 32).toNat = 2 := rfl; rw [this]; apply Nat.mod_eq_of_lt; omega
      change (2 * sc + best_k : BitVec 32).toNat = _; rw [BitVec.toNat_add, h2]
      apply Nat.mod_eq_of_lt; omega
    let brow_off := s.scratch.scratch_buf[sc.toNat + best_k.toNat]'(by omega)
    let mn_bv := s.scratch.scratch_buf[2 * sc.toNat + best_k.toNat]'(by omega)
    have hbo_getD :
        (s.scratch.scratch_buf[sc.toNat + best_k.toNat]?.getD 0#32).toNat = brow_off.toNat := by
      dsimp only [brow_off]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hmn_getD :
        (s.scratch.scratch_buf[2 * sc.toNat + best_k.toNat]?.getD 0#32).toNat = mn_bv.toNat := by
      dsimp only [mn_bv]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [← hsc_nat] at hro_ge hmn_lo hro_mn hbk_entries
    rw [hbo_getD] at hro_ge hro_mn hbk_entries
    rw [hmn_getD] at hmn_lo hro_mn hbk_entries
    have hbo_eq : s.scratch.scratch_buf[(BitVec.setWidth 64 (sc + best_k)).toNat]'(by
        rw [bv64_setWidth_32, hsc_bk]; omega) = brow_off := by
      dsimp only [brow_off]; simp only [bv64_setWidth_32, hsc_bk]
    have hmn_eq : s.scratch.scratch_buf[(BitVec.setWidth 64 (2 * sc + best_k)).toNat]'(by
        rw [bv64_setWidth_32, h2sc_bk]; omega) = mn_bv := by
      dsimp only [mn_bv]; simp only [bv64_setWidth_32, h2sc_bk]
    have h2sc_bk_mod : (2 * sc.toNat + best_k.toNat) % 2 ^ 32 = 2 * sc.toNat + best_k.toNat := by
      omega
    have h2sc_mod : (BitVec.toNat (2 : BitVec 32) * sc.toNat + best_k.toNat) % 2 ^ 32 =
        2 * sc.toNat + best_k.toNat := by
      rw [show BitVec.toNat (2 : BitVec 32) = 2 from rfl]; omega
    let dm := best_k.toNat + 1
    c0_hsteps_nogrp
    · refine wp_loop_inv (fun (_need_w, si, ()) msi => m = msi ∧ si.toNat ≤ dm)
        (fun (_, si, _) _ => dm - si.toNat)
        (fun Jsi hJsi => by c0_hsteps; exact hJsi (_, 0#32, ()) m ⟨rfl, Nat.zero_le _⟩)
        (fun Jsi (need_w0, si, ()) msi ⟨hmsi, hsi_le⟩ ihsi => ?_)
      rcases hmsi with rfl; c0_hsteps_nogrp
      · have hsi_lt : si.toNat < dm := by
          have h1 : si.toNat < (best_k + 1#32).toNat := (by assumption); omega
        have hsi1 : (si + 1#32).toNat = si.toNat + 1 := by c0_bound
        have hfs_sb : (BitVec.setWidth 64 si).toNat < s.scratch.scratch_buf.length := by
          rw [bv64_setWidth_32, hsb_len]; omega
        have hfs_lt : (s.scratch.scratch_buf[si.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
          have h1 := (hmat.2.2.2.2.2 si.toNat (by omega)).1
          simpa only [List.getElem?_eq_getElem (by omega : si.toNat < s.scratch.scratch_buf.length),
            Option.getD_some] using h1
        have hfs_wv : ((BitVec.setWidth 64
            (s.scratch.scratch_buf[(BitVec.setWidth 64 si).toNat]'hfs_sb) <<< (1 : Nat)) +
            1).toNat < s.core.wvec.length := by
          rw [hwv_len]; simp only [bv_c0, show (1 : BitVec 64).toNat = 1 from rfl]; omega
        c0_hsteps; exact ihsi (_, si + 1#32, ()) m (by dsimp only; rw [hsi1]; omega)
          ⟨rfl, by rw [hsi1]; omega⟩
      · refine wp_loop_inv
          (fun (_need_ar, _need_w, mi, ()) mm => m = mm ∧ mi.toNat ≤ mn_bv.toNat)
          (fun (_, _, mi, _) _ => mn_bv.toNat - mi.toNat) (fun Jpre hJpre => by
            c0_hsteps; exact hJpre (16#64, need_w0, 0#32, ()) m ⟨rfl, Nat.zero_le _⟩)
          (fun Jpre (need_ar, need_w, mi, ()) mm ⟨hmm, hmi_le⟩ ihpre => ?_)
        rcases hmm with rfl; c0_hsteps_nogrp
        · have hmi_lt : mi.toNat < mn_bv.toNat := by
            have h1 : mi.toNat < (s.scratch.scratch_buf[(BitVec.toNat (2 : BitVec 32) *
                sc.toNat + best_k.toNat) % 2 ^ 32]'(by rw [h2sc_mod]; omega)).toNat :=
              by assumption
            simpa only [mn_bv, h2sc_mod] using h1
          have hmi1 : (mi + 1#32).toNat = mi.toNat + 1 := by c0_bound
          have hctop_idx : (brow_off + mi).toNat = brow_off.toNat + mi.toNat := by
            have h1 : (brow_off + mi).toNat = (brow_off + mi : BitVec 32).toNat := rfl
            rw [h1, BitVec.toNat_add]; apply Nat.mod_eq_of_lt; omega
          have hctop_sb : (BitVec.setWidth 64 (brow_off + mi)).toNat <
              s.scratch.scratch_buf.length := by rw [bv64_setWidth_32, hctop_idx, hsb_len]; omega
          let c_top := s.scratch.scratch_buf[brow_off.toNat + mi.toNat]'(by omega)
          have hctop_eq : s.scratch.scratch_buf[(BitVec.setWidth 64
              (brow_off + mi)).toNat]'hctop_sb = c_top := by
            dsimp only [c_top]; simp only [bv64_setWidth_32, hctop_idx]
          have hctop_mod_n : (brow_off.toNat + mi.toNat) % 2 ^ 32 =
              brow_off.toNat + mi.toNat := Nat.mod_eq_of_lt (by omega)
          have hctop_mod : s.scratch.scratch_buf[(brow_off.toNat + mi.toNat) % 2 ^ 32]'(by
              rw [hctop_mod_n, hsb_len]; omega) = c_top := by
            dsimp only [c_top]; simp only [hctop_mod_n]
          obtain ⟨_, _, _, hctop_ok, _, _⟩ := hbk_entries mi.toNat hmi_lt
          have hctop_getD : s.scratch.scratch_buf[brow_off.toNat + mi.toNat]?.getD 0#32 =
              c_top := by
            dsimp only [c_top]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          rw [hctop_getD] at hctop_ok; try simp only [hbo_eq]
          c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [i64, i64]) (α := BitVec 64 × BitVec 64)
            (fun p => (p.1, p.2, ())) (fun _ => True) (fun _ ⟨na', nw'⟩ _ => ?_)
            (fun Jpn hJpn => ?_)
          · c0_hsteps; exact ihpre (na', nw', mi + 1#32, ()) m (by dsimp only; rw [hmi1]; omega)
              ⟨rfl, by rw [hmi1]; omega⟩
          c0_hsplit
          · have hbin_ct : (c_top &&& 0x80000000#32) ≠ 0#32 := by
              simpa only [← hctop_mod] using (by assumption : _)
            unfold FidBvaRowEntryOk at hctop_ok; rw [ite_eq_left hbin_ct] at hctop_ok
            have hq_lt : (c_top &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars := hctop_ok.1
            have hq_wv : ((BitVec.setWidth 64 (s.scratch.scratch_buf[(BitVec.setWidth 64
                (brow_off + mi)).toNat]'hctop_sb &&& 0x7FFFFFFF#32) <<< (1 : Nat)) +
                1).toNat < s.core.wvec.length := by
              rw [hctop_eq, hwv_len]; simp only [bv_c0, show (1 : BitVec 64).toNat = 1 from rfl]
              omega
            c0_hfast; exact hJpn (need_ar, _) trivial
          · have hbin_ct : (c_top &&& 0x80000000#32) = 0#32 := by
              simpa only [← hctop_mod] using (by assumption : _)
            unfold FidBvaRowEntryOk at hctop_ok
            rw [ite_eq_right (fun h' => h' hbin_ct)] at hctop_ok
            obtain ⟨hct_ref0, hct_ng0, _, _, _, _, _⟩ := hctop_ok
            have hct_wf := hinv.2.1.arena.refs_wf c_top.toNat hct_ref0
            have hct2_n : (BitVec.setWidth 64 c_top + 2).toNat = c_top.toNat + 2 := by
              change (BitVec.setWidth 64 c_top + 2#64).toNat = _; c0_bound
            have hct2_ar : (BitVec.setWidth 64 (s.scratch.scratch_buf[(BitVec.setWidth 64
                (brow_off + mi)).toNat]'hctop_sb) + 2).toNat < s.core.arena.length := by
              rw [hctop_eq, hct2_n]; have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
            let csz_bv := s.core.arena[c_top.toNat + 2]'(by
              have := hcl.arena_len_le; have := hcl.arena_len_arr; omega)
            have hcsz_eq : csz_bv.toNat = fullArenaClauseSizeCore s.core c_top.toNat := by
              dsimp only [csz_bv]; unfold fullArenaClauseSizeCore
              rw [List.getElem?_eq_getElem (by
                have := hcl.arena_len_le; have := hcl.arena_len_arr; omega), Option.getD_some]
            have hbk_sb : (BitVec.setWidth 64 best_k).toNat < s.scratch.scratch_buf.length := by
              rw [bv64_setWidth_32, hsb_len]; omega
            c0_hsteps_nogrp
            refine wp_loop_inv (fun (_nw, ji, ()) mji => m = mji ∧ ji.toNat ≤ csz_bv.toNat)
              (fun (_, ji, _) _ => csz_bv.toNat - ji.toNat)
              (fun Jj hJj => by c0_hsteps; exact hJj (need_w, 0#32, ()) m ⟨rfl, Nat.zero_le _⟩)
              (fun Jj (nwj, ji, ()) mji ⟨hmji, hji_le⟩ ihj => ?_)
            rcases hmji with rfl; c0_hsteps_nogrp
            · have hct2_mod : (c_top.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
                  c_top.toNat + 2 := by rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
              have hji_lt : ji.toNat < csz_bv.toNat := by
                dsimp only [csz_bv]
                have h1 : ji.toNat < (s.core.arena[(c_top.toNat + BitVec.toNat (2 : BitVec 64)) %
                    2 ^ 64]'(by rw [hct2_mod]; have := hcl.arena_len_le
                                have := hcl.arena_len_arr; omega)).toNat := by
                  simpa only [← hctop_mod] using (by assumption : _)
                simpa only [hct2_mod] using h1
              have hji1 : (ji + 1#32).toNat = ji.toNat + 1 := by c0_bound
              have hctj_n : (BitVec.setWidth 64 c_top + 3 + BitVec.setWidth 64 ji).toNat =
                  c_top.toNat + 3 + ji.toNat := by
                change (BitVec.setWidth 64 c_top + 3#64 + BitVec.setWidth 64 ji).toNat = _; c0_bound
              have hctj_ar : c_top.toNat + 3 + ji.toNat < s.core.arena.length := by
                have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
              have hctj_ar_sb : (BitVec.setWidth 64 (s.scratch.scratch_buf[(BitVec.setWidth 64
                  (brow_off + mi)).toNat]'hctop_sb) + 3 + BitVec.setWidth 64 ji).toNat <
                  s.core.arena.length := by rw [hctop_eq, hctj_n]; exact hctj_ar
              have hlj_lt : (s.core.arena[c_top.toNat + 3 + ji.toNat]'hctj_ar).toNat <
                  2 * s.core.cur_vars := by
                have h1 := FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (k := s.core)
                  (r := c_top.toNat) (j := ji.toNat) (by rw [← hcsz_eq]; exact hji_lt) hctj_ar
                exact hinv.2.1.arena.lits_lt c_top.toNat hct_ref0 hct_ng0 _
                  (List.mem_of_getElem? h1)
              c0_hsteps_nogrp; refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                (fun x => (x, ())) (fun _ => True) (fun _ nw' _ => by
                  c0_hsteps; exact ihj (nw', ji + 1#32, ()) m (by dsimp only; rw [hji1]; omega)
                    ⟨rfl, by rw [hji1]; omega⟩)
                (fun Jlf hJlf => ?_)
              c0_hsplit
              · have hlj_wv : ((BitVec.setWidth 64 (s.core.arena[(BitVec.setWidth 64
                    (s.scratch.scratch_buf[(BitVec.setWidth 64
                      (brow_off + mi)).toNat]'hctop_sb) +
                    3 + BitVec.setWidth 64 ji).toNat]'hctj_ar_sb) <<< (1 : Nat)) + 1).toNat <
                    s.core.wvec.length := by
                  have hlj_eq : s.core.arena[(BitVec.setWidth 64
                      (s.scratch.scratch_buf[(BitVec.setWidth 64
                        (brow_off + mi)).toNat]'hctop_sb) + 3 +
                      BitVec.setWidth 64 ji).toNat]'hctj_ar_sb =
                      s.core.arena[c_top.toNat + 3 + ji.toNat]'hctj_ar := by
                    simp only [hctop_eq, hctj_n]
                  rw [hlj_eq, hwv_len]; simp only [bv_c0, show (1 : BitVec 64).toNat = 1 from rfl]
                  omega
                c0_hsteps; exact hJlf _ trivial
              · c0_hsteps; exact hJlf nwj trivial
            · exact hJpn (_, nwj) trivial
        · exact hQ false s m hinv.toDense (Nat.le_refl _) (fun h => absurd h (by decide))
            (fun h => absurd h (by decide))
            rfl rfl rfl hm
        · exact hQ false s m hinv.toDense (Nat.le_refl _) (fun h => absurd h (by decide))
            (fun h => absurd h (by decide))
            rfl rfl rfl hm
        · exact hQ false s m hinv.toDense (Nat.le_refl _) (fun h => absurd h (by decide))
            (fun h => absurd h (by decide))
            rfl rfl rfl hm
        · have hcv_lt : s.core.cur_vars < c.max_vars := by c0_bound
          have htail := s7_pre_exit_wp (Γ := Γ) (Q := Q) (X := X)
            hDefrag hInitFresh hAddBin hAllocCl hWPush hDelBin hUnwatch
            (sc := sc) (dm_bv := best_k + 1#32) (brow_off := brow_off) (mn_bv := mn_bv)
            (need_ar := need_ar) (need_w := need_w) (bump := bump)
            hinv hbk1 hbk_sc hmat hlay hres hsc_nat hdm_bv hbo_getD hmn_getD hm hcv_lt hQ
          unfold s7PreExitExpr s7PreMidExpr s7HdrExpr at htail
          rw [← hbo_eq, ← hmn_eq] at htail
          exact htail

end LeanQbe.T.Examples.Kissat.FullFidelityStep7

end
