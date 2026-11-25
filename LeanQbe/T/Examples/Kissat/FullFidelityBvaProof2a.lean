/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof2a0
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
# Kissat Fidelity BVA Commit WP Proof (`FullFidelityBvaProof2a`)

M1-clean UNSAT-only parametric `Func.wp` proof (`public section`, `XPost`-polymorphic) for
`full_bva_commit_fid_wp` certifying `fidBvaCommitSpec` for `full_bva_commit_body` with:
- dynamic `sc = full_bva_steps_cap_fid(h->scratch_cap)` packed matrix indexing,
- `h->repr` literal watch-degree updates (`deg[fresh] = dm`, `deg[fresh ^ 1] = mn`) and
  `h->bva_cnt` increment,
- `h->wsort` (`cnt`) workspace zeroing on both commit and rollback paths,
- `fid_bva_large_top_wp` rollback & `FidBvaMatrixInv` preservation across dynamic rows.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBva

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullArenaTactics
open FullBvaHeap FullBvaHeap.FullBvaHeapHelpers FullBvaHeap.FullBvaHeapTactics
open FullBvaHeap.FullBvaHeapScanHelpers FullM4Bva
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

private abbrev FidBvaPreOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sd : FullState) : Prop :=
  FullDenseInvW c F0 F_cur sd ∧ sd.core.cur_vars = s.core.cur_vars ∧
  sd.core.fuel = s.core.fuel ∧ sd.core.arena = s.core.arena ∧
  sd.core.arena_len = s.core.arena_len ∧ sd.scratch.scratch_buf = s.scratch.scratch_buf ∧
  sd.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  sd.scratch.tarjan_reach = s.scratch.tarjan_reach

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

@[irreducible] private def fidBvaHdrExpr (h pAr pScr : Val i64) (best_k sc : Val i32) :
    Expr Val Cont [.bool] :=
  full_bva_commit_body Val Cont (h, best_k, ())
    |> sSteps 3 |> sElse |> sSteps 2 |> sCall32 sc |> sStep |> sElse |> sStep |> sElse |> sStep
    |> sLd64 pAr |> sStep |> sLd64 pScr

@[irreducible] private def fidBvaPreMidExpr (h pAr pScr pCnt pFl pWv : Val i64)
    (best_k sc dm brow_off mn : Val i32) : Expr Val Cont [.bool] :=
  fidBvaHdrExpr h pAr pScr best_k sc |> sStep |> sLd64 pCnt |> sStep |> sLd64 pFl
    |> sStep |> sLd64 pWv |> sLet32 dm |> sSteps 4 |> sLd32 brow_off
    |> sSteps 5 |> sLd32 mn |> sSteps 6

@[irreducible] private def fidBvaMidExpr (e : Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  e |> sGrp64_32 (fun (_ : Tup Val [i64, i32]) (_ : Mem 64) => True) |> sStep |> sElse
    |> sGrp64_64_32 (fun (_ : Tup Val [i64, i64, i32]) (_ : Mem 64) => True) |> sStep |> sElse
    |> sSteps 5 |> sElse |> sSteps 5 |> sElse |> sSteps 6 |> sElse
    |> sGrp0 (fun (_ : Tup Val []) (_ : Mem 64) => True)

@[irreducible] private def fidBvaPreExitExpr (h pAr pScr pCnt pFl pWv : Val i64)
    (best_k sc dm brow_off mn : Val i32) (need_ar need_w : Val i64) :
    Expr Val Cont [.bool] :=
  fidBvaPreMidExpr h pAr pScr pCnt pFl pWv best_k sc dm brow_off mn
    |> sGrp64_32 (fun (_ : Tup Val [i64, i32]) (_ : Mem 64) => True) |> sStep |> sElse
    |> sGrp64_64_32v (fun (_ : Tup Val [i64, i64, i32]) (_ : Mem 64) => True) need_ar need_w
    |> sStep |> sElse |> sSteps 5 |> sElse |> sSteps 5 |> sElse |> sSteps 6 |> sElse

@[irreducible] private def fidBvaPostDefragExpr (h pAr pScr pCnt pFl pWv : Val i64)
    (best_k sc dm brow_off mn : Val i32) : Expr Val Cont [.bool] :=
  fidBvaPreMidExpr h pAr pScr pCnt pFl pWv best_k sc dm brow_off mn |> fidBvaMidExpr

@[irreducible] private def fidBvaPhase1bExpr (h pAr pScr pCnt pFl pWv pDeg pTmp : Val i64)
    (best_k sc dm brow_off mn fresh : Val i32) (ok1a : Val .bool) : Expr Val Cont [.bool] :=
  fidBvaPostDefragExpr h pAr pScr pCnt pFl pWv best_k sc dm brow_off mn
    |> sSteps 10 |> sLd64 pDeg |> sSteps 22 |> sLet32 fresh |> sStep |> sLd64 pTmp
    |> sGrp32b (fun (_ : Tup Val [i32, .bool]) (_ : Mem 64) => True) 0#32 ok1a

@[irreducible] private def fidBvaPhase2Expr (h pAr pScr pCnt pFl pWv pDeg pTmp : Val i64)
    (best_k sc dm brow_off mn fresh : Val i32) : Expr Val Cont [.bool] :=
  fidBvaPhase1bExpr h pAr pScr pCnt pFl pWv pDeg pTmp best_k sc dm brow_off mn fresh true
    |> sGrp32b (fun (_ : Tup Val [i32, .bool]) (_ : Mem 64) => True) 0#32 true |> sThen

@[irreducible] private def fidBvaDelColExpr (h pAr pScr pCnt pFl pWv pDeg pTmp : Val i64)
    (best_k sc dm brow_off mn fresh mi : Val i32) (Jm : Cont [i32]) :
    Expr Val Cont [.bool] :=
  fidBvaPhase2Expr h pAr pScr pCnt pFl pWv pDeg pTmp best_k sc dm brow_off mn fresh
    |> sGrp1 Jm mi |> sStep |> sThen

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

/-! ## 2. Phase 2 Column Deletion & Cleanup (`fid_bva_del_col_wp`, `fid_bva_phase2_wp`) -/

private theorem fid_bva_del_col_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hDelBin : FidDelBinHyp Γ) (hUnwatch : FidUnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s st1 : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv fresh mi : Val i32}
    {Jm : Cont [i32]} {m1 : Mem 64} {bump : Nat}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hbk1 : 1 ≤ best_k.toNat) (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hmat : FidBvaMatrixInv c F_cur s (best_k.toNat + 1) bump)
    (hsc_eq : sc.toNat = fidStepsCap c.scratch_cap)
    (hmi_lt : mi.toNat < (s.scratch.scratch_buf[2 * sc.toNat + best_k.toNat]?.getD 0#32).toNat)
    (hm1 : (FullMem c st1 ⋆ R) m1)
    (hst1 : FidBvaStOk c F0 F_next s st1)
    (hNext : ∀ st2 m2, FidBvaStOk c F0 F_next s st2 → (FullMem c st2 ⋆ R) m2 →
      Jm (mi + 1#32, ()) m2) :
    wp Γ Q X (fidBvaDelColExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr
      c.pTmp best_k sc dm_bv brow_off mn_bv fresh mi Jm) m1 := by
  have hmx : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have har_b : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hscr_b : c.scratch_cap < 2 ^ 28 := c.hscr
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hsb_len := hsc.scratch_buf_len
  let old_cv := s.core.cur_vars
  have hsc_pos : 0 < fidStepsCap c.scratch_cap := hmat.1
  have hbump_ge : 4 * fidStepsCap c.scratch_cap ≤ bump := hmat.2.2.2.1
  have hbump_le : bump ≤ c.scratch_cap := hmat.2.2.2.2.1
  have hmat_rows := hmat.2.2.2.2.2
  have hsc_lt_cap : sc.toNat < c.scratch_cap := by
    have := fidStepsCap_mul4_le c.scratch_cap; omega
  unfold fidBvaDelColExpr fidBvaPhase2Expr fidBvaPhase1bExpr fidBvaPostDefragExpr fidBvaMidExpr
    fidBvaPreMidExpr fidBvaHdrExpr
  dsimp only [sStep, sLd64, sLd32, sCall32, sLet32,
    sGrp0, sGrp1, sGrp64_32, sGrp64_64_32, sGrp32b, sThen, sElse, sDummyTup, sDummyVal, i64, i32,
    full_bva_commit_body]
  refine wp_join_group (ts := [i32, i32])
    (fun (_ : Tup Val [i32, i32]) m2 => ∃ st2 : FullState,
      (FullMem c st2 ⋆ R) m2 ∧ FidBvaStOk c F0 F_next s st2)
    (fun _ _ m2 ⟨st2, hm2, hst2⟩ => by c0_hstep; c0_hstep; exact hNext st2 m2 hst2 hm2)
    (fun Jdel hJdel => ?_)
  refine wp_loop_inv
    (fun (idx, sv, ()) msv => ∃ stv : FullState,
      sv.toNat ≤ best_k.toNat ∧
      idx.toNat < (s.scratch.scratch_buf[2 * sc.toNat + sv.toNat]?.getD 0#32).toNat ∧
      FidBvaStOk c F0 F_next s stv ∧ (FullMem c stv ⋆ R) msv)
    (fun (_, sv, _) _ => sv.toNat)
    (fun Jd hJd => by
      c0_hstep
      exact hJd (mi, best_k, ()) m1 ⟨st1, Nat.le_refl _, hmi_lt, hst1, hm1⟩)
    (fun Jd (idx, sv, ()) msv ⟨stv, hsv_le, hidx_lt, hstv, hmsv⟩ ihd => ?_)
  obtain ⟨hinvv, hcvv, hfuelv, hsbv, htmv, htrv, hmonov⟩ := hstv
  have hclv := hinvv.1.core_ok
  have hscv := hinvv.1.scratch_ok
  have hsv_sc : sv.toNat < fidStepsCap c.scratch_cap := by omega
  have hsv_mat := hmat_rows sv.toNat (by omega)
  obtain ⟨hfr_lt, hro_ge, hqn_ge, hro_qn, hpo_prop, hsv_entries⟩ := hsv_mat
  have hidx_lt_s :
      idx.toNat < (s.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + sv.toNat]?.getD
        0#32).toNat := by
    rw [← hsc_eq]; exact hidx_lt
  obtain ⟨resv, hres_lt, hres_nd, hcs_ok, hent, hpar_ok⟩ := hsv_entries idx.toNat hidx_lt_s
  have hsc_sv : (sc + sv).toNat = sc.toNat + sv.toNat := by
    have h1 : (sc + sv).toNat = (sc + sv : BitVec 32).toNat := rfl
    rw [h1, BitVec.toNat_add]; apply Nat.mod_eq_of_lt
    rw [hsc_eq]; have := fidStepsCap_mul4_le c.scratch_cap; omega
  have hsc_sb : (BitVec.setWidth 64 (sc + sv)).toNat < stv.scratch.scratch_buf.length := by
    rw [bv64_setWidth_32, hsc_sv, hscv.scratch_buf_len, hsc_eq]
    have := fidStepsCap_mul4_le c.scratch_cap; omega
  let ro_bv := s.scratch.scratch_buf[sc.toNat + sv.toNat]'(by
    rw [hsc_eq, hsb_len]; have := fidStepsCap_mul4_le c.scratch_cap; omega)
  have hro_eq : stv.scratch.scratch_buf[(BitVec.setWidth 64 (sc + sv)).toNat]'hsc_sb = ro_bv := by
    dsimp only [ro_bv]; simp only [hsbv, bv64_setWidth_32, hsc_sv]
  have hro_getD : s.scratch.scratch_buf[sc.toNat + sv.toNat]?.getD 0#32 = ro_bv := by
    dsimp only [ro_bv]; rw [List.getElem?_eq_getElem (by
      rw [hsc_eq, hsb_len]; have := fidStepsCap_mul4_le c.scratch_cap; omega), Option.getD_some]
  have hro_bv_val :
      ro_bv.toNat = (s.scratch.scratch_buf[fidStepsCap c.scratch_cap + sv.toNat]?.getD
        0#32).toNat := by
    rw [← hsc_eq, hro_getD]
  have hcs_idx : (ro_bv + idx).toNat = ro_bv.toNat + idx.toNat := by
    have h1 : (ro_bv + idx).toNat = (ro_bv + idx : BitVec 32).toNat := rfl
    rw [h1, BitVec.toNat_add]; apply Nat.mod_eq_of_lt; rw [hro_bv_val]; omega
  have hcs_sb : (BitVec.setWidth 64
      (stv.scratch.scratch_buf[(BitVec.setWidth 64 (sc + sv)).toNat]'hsc_sb + idx)).toNat <
      stv.scratch.scratch_buf.length := by
    rw [hro_eq, bv64_setWidth_32, hcs_idx, hscv.scratch_buf_len, hro_bv_val]; omega
  let cs := s.scratch.scratch_buf[ro_bv.toNat + idx.toNat]'(by
    rw [hro_bv_val, hsb_len]; omega)
  have hcs_idx_bv : (BitVec.setWidth 64
      (stv.scratch.scratch_buf[(BitVec.setWidth 64 (sc + sv)).toNat]'hsc_sb + idx)).toNat =
      (ro_bv + idx).toNat := by
    rw [hro_eq, bv64_setWidth_32]
  have hcs_eq : stv.scratch.scratch_buf[(BitVec.setWidth 64
      (stv.scratch.scratch_buf[(BitVec.setWidth 64 (sc + sv)).toNat]'hsc_sb + idx)).toNat]'hcs_sb =
      cs := by
    have h1 : stv.scratch.scratch_buf[(BitVec.setWidth 64
        (stv.scratch.scratch_buf[(BitVec.setWidth 64 (sc + sv)).toNat]'hsc_sb + idx)).toNat]? =
        s.scratch.scratch_buf[ro_bv.toNat + idx.toNat]? := by
      have heq : stv.scratch.scratch_buf[(ro_bv + idx).toNat]? =
          s.scratch.scratch_buf[ro_bv.toNat + idx.toNat]? := by
        rw [hsbv, hcs_idx]
      rw [hcs_idx_bv, heq]
    dsimp only [cs]
    rw [← Option.some_inj, ← List.getElem?_eq_getElem hcs_sb, h1,
      List.getElem?_eq_getElem (by rw [hro_bv_val, hsb_len]; omega)]
  have hcs_getD : s.scratch.scratch_buf[ro_bv.toNat + idx.toNat]?.getD 0#32 = cs := by
    dsimp only [cs]; rw [List.getElem?_eq_getElem (by
      rw [hro_bv_val, hsb_len]; omega), Option.getD_some]
  have hcs_ok_rw :
      FidBvaRowEntryOk F_cur s (s.scratch.scratch_buf[sv.toNat]?.getD 0#32).toNat cs resv := by
    have h1 :
        (s.scratch.scratch_buf[fidStepsCap c.scratch_cap + sv.toNat]?.getD 0#32).toNat +
          idx.toNat =
        ro_bv.toNat + idx.toNat := by rw [hro_bv_val]
    rw [h1, hcs_getD] at hcs_ok; exact hcs_ok
  have hsv_sb : (BitVec.setWidth 64 sv).toNat < stv.scratch.scratch_buf.length := by
    rw [bv64_setWidth_32, hscv.scratch_buf_len]; have := fidStepsCap_mul4_le c.scratch_cap; omega
  let fs := s.scratch.scratch_buf[sv.toNat]'(by
    rw [hsb_len]; have := fidStepsCap_mul4_le c.scratch_cap; omega)
  have hfs_eq : stv.scratch.scratch_buf[(BitVec.setWidth 64 sv).toNat]'hsv_sb = fs := by
    dsimp only [fs]; simp only [hsbv, bv64_setWidth_32]
  c0_hstep
  rotate_left
  · exact absurd (by assumption : true = false) (by decide)
  c0_hstep; c0_hstep; c0_hstep; c0_hstep
  c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
  c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
  refine wp_join_state0 (α := FullState)
    (fun stc mc => (FullMem c stc ⋆ R) mc ∧ FidBvaStOk c F0 F_next s stc)
    (fun _ stc mc ⟨hmc, hstc⟩ => ?_) (fun Jcs hJcs => ?_)
  · have hscc := hstc.1.1.scratch_ok
    c0_hstep; c0_hstep
    · exact hJdel (idx, sv, ()) mc ⟨stc, hmc, hstc⟩
    · have hsv_pos : 0 < sv.toNat := by
        cases h0 : sv.toNat with
        | zero =>
          have : sv = 0#32 := BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
          subst this; contradiction
        | succ n => omega
      have hsv1 : (sv - 1#32).toNat = sv.toNat - 1 := by
        have h1 : (1#32 : BitVec 32).toNat ≤ sv.toNat := by
          have : (1#32 : BitVec 32).toNat = 1 := rfl
          rw [this]; omega
        exact BitVec.toNat_sub_of_le h1
      have h3sc_sv : (3 * sc + sv).toNat = 3 * sc.toNat + sv.toNat := by
        have h3 : (3 * sc).toNat = 3 * sc.toNat := by
          have h1 : (3 * sc).toNat = ((3#32 : BitVec 32) * sc).toNat := rfl
          rw [h1, BitVec.toNat_mul]
          have : (3#32 : BitVec 32).toNat = 3 := rfl
          rw [this, hsc_eq]
          apply Nat.mod_eq_of_lt
          have := fidStepsCap_mul4_le c.scratch_cap
          omega
        have h1 : (3 * sc + sv).toNat = (3 * sc + sv : BitVec 32).toNat := rfl
        rw [h1, BitVec.toNat_add, h3]
        apply Nat.mod_eq_of_lt
        rw [hsc_eq]
        have := fidStepsCap_mul4_le c.scratch_cap
        omega
      have h3sc_sv_sb :
          (BitVec.setWidth 64 (3 * sc + sv)).toNat < stc.scratch.scratch_buf.length := by
        rw [bv64_setWidth_32, h3sc_sv, hscc.scratch_buf_len, hsc_eq]
        have := fidStepsCap_mul4_le c.scratch_cap; omega
      let po_bv := s.scratch.scratch_buf[3 * sc.toNat + sv.toNat]'(by
        rw [hsc_eq, hsb_len]; have := fidStepsCap_mul4_le c.scratch_cap; omega)
      have hpo_eq :
          stc.scratch.scratch_buf[(BitVec.setWidth 64 (3 * sc + sv)).toNat]'h3sc_sv_sb =
            po_bv := by
        dsimp only [po_bv]; simp only [hstc.2.2.2.1, bv64_setWidth_32, h3sc_sv]
      have hpo_getD : s.scratch.scratch_buf[3 * sc.toNat + sv.toNat]?.getD 0#32 = po_bv := by
        dsimp only [po_bv]; rw [List.getElem?_eq_getElem (by
          rw [hsc_eq, hsb_len]; have := fidStepsCap_mul4_le c.scratch_cap; omega), Option.getD_some]
      have hpo_bv_val :
          po_bv.toNat = (s.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap + sv.toNat]?.getD
            0#32).toNat := by
        rw [← hsc_eq, hpo_getD]
      have hpo_idx : (po_bv + idx).toNat = po_bv.toNat + idx.toNat := by
        have h1 : (po_bv + idx).toNat = (po_bv + idx : BitVec 32).toNat := rfl
        rw [h1, BitVec.toNat_add]; apply Nat.mod_eq_of_lt
        have hpo_p := (hpo_prop hsv_pos).2
        rw [hpo_bv_val]; omega
      have hpar_sb : (BitVec.setWidth 64
          (stc.scratch.scratch_buf[(BitVec.setWidth 64 (3 * sc + sv)).toNat]'h3sc_sv_sb +
            idx)).toNat <
          stc.scratch.scratch_buf.length := by
        rw [hpo_eq, bv64_setWidth_32, hpo_idx, hscc.scratch_buf_len, hpo_bv_val]
        have hpo_p := (hpo_prop hsv_pos).2
        omega
      have hpi_lt := (hpar_ok hsv_pos).1
      c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
      c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
      c0_hstep; c0_hstep; c0_hstep
      refine ihd (_, sv - 1#32, ()) mc (by dsimp only; rw [hsv1]; omega)
        ⟨stc, by rw [hsv1]; omega, ?_, hstc, hmc⟩
      rw [hsv1]
      have hpi_eq : stc.scratch.scratch_buf[(BitVec.setWidth 64
          (stc.scratch.scratch_buf[(BitVec.setWidth 64 (3 * sc + sv)).toNat]'h3sc_sv_sb +
            idx)).toNat]'hpar_sb =
          s.scratch.scratch_buf[(s.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap +
            sv.toNat]?.getD 0#32).toNat + idx.toNat]?.getD 0#32 := by
        have heq : stc.scratch.scratch_buf[(BitVec.setWidth 64
            (stc.scratch.scratch_buf[(BitVec.setWidth 64 (3 * sc + sv)).toNat]'h3sc_sv_sb +
              idx)).toNat]? =
            s.scratch.scratch_buf[(s.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap +
              sv.toNat]?.getD 0#32).toNat + idx.toNat]? := by
          rw [hpo_eq, bv64_setWidth_32, hpo_idx, hstc.2.2.2.1, hpo_bv_val]
        rw [← heq, List.getElem?_eq_getElem hpar_sb, Option.getD_some]
      rw [hpi_eq, hsc_eq]; exact hpi_lt
  · have hcs_mod : stv.scratch.scratch_buf[(stv.scratch.scratch_buf[(sc.toNat +
        sv.toNat) % 2 ^ 32].toNat + idx.toNat) % 2 ^ 32] = cs := by
      have h1 : (sc.toNat + sv.toNat) % 2 ^ 32 = (BitVec.setWidth 64 (sc + sv)).toNat := by
        rw [bv64_setWidth_32, hsc_sv]; apply Nat.mod_eq_of_lt
        rw [hsc_eq]; have := fidStepsCap_mul4_le c.scratch_cap; omega
      have h_arg : stv.scratch.scratch_buf[(sc.toNat + sv.toNat) % 2 ^ 32] =
          stv.scratch.scratch_buf[(BitVec.setWidth 64 (sc + sv)).toNat]'hsc_sb := by
        have heq : stv.scratch.scratch_buf[(sc.toNat + sv.toNat) % 2 ^ 32]? =
            stv.scratch.scratch_buf[(BitVec.setWidth 64 (sc + sv)).toNat]? := by rw [h1]
        rw [← Option.some_inj, ← List.getElem?_eq_getElem (by rw [h1]; exact hsc_sb), heq,
          List.getElem?_eq_getElem hsc_sb]
      have h2 : (stv.scratch.scratch_buf[(sc.toNat + sv.toNat) % 2 ^ 32].toNat +
          idx.toNat) % 2 ^ 32 =
          (BitVec.setWidth 64 (stv.scratch.scratch_buf[(BitVec.setWidth 64
            (sc + sv)).toNat]'hsc_sb + idx)).toNat := by
        rw [h_arg]
        exact (bv64_setWidth_32 (stv.scratch.scratch_buf[(BitVec.setWidth 64
          (sc + sv)).toNat]'hsc_sb + idx)).symm.trans (BitVec.toNat_add _ _).symm
      have heq : stv.scratch.scratch_buf[(stv.scratch.scratch_buf[(sc.toNat +
          sv.toNat) % 2 ^ 32].toNat + idx.toNat) % 2 ^ 32]? =
          stv.scratch.scratch_buf[(BitVec.setWidth 64
            (stv.scratch.scratch_buf[(BitVec.setWidth 64 (sc + sv)).toNat]'hsc_sb +
              idx)).toNat]? := by
        rw [h2]
      rw [← Option.some_inj, ← List.getElem?_eq_getElem (by rw [h2]; exact hcs_sb), heq,
        List.getElem?_eq_getElem hcs_sb, hcs_eq]
    c0_hstep; c0_hstep; c0_hstep
    · have hbin_cs : (cs &&& 0x80000000#32) ≠ 0#32 := by
        rw [← hcs_mod]; exact hc
      unfold FidBvaRowEntryOk at hcs_ok_rw; rw [ite_eq_left hbin_cs] at hcs_ok_rw
      have hq_lt : (cs &&& 0x7FFFFFFF#32).toNat < 2 * old_cv := hcs_ok_rw.1
      c0_call hDelBin
      refine ⟨c, stv, R, rfl, hinvv.1, hinvv.2.1.watches.layout, hmsv,
        fun wvec' wstk' wu' nb' md1 hlen_d _ hwat_d hmd1 => ?_⟩
      have hinv_d := fullDenseInvW_of_delBin hinvv hlen_d (hwat_d F_next hinvv.2.1.watches)
      have hq_shr : (BitVec.setWidth 64 ((stv.scratch.scratch_buf[(BitVec.setWidth 64
          (stv.scratch.scratch_buf[(BitVec.setWidth 64 (sc + sv)).toNat]'hsc_sb +
            idx)).toNat]'hcs_sb &&& 0x7FFFFFFF#32) >>> (1 : BitVec 32))).toNat <
          stv.core.flags.length := by
        rw [bv64_setWidth_32, hcs_eq, bv32_lshr1_bv, hclv.flags_len]; omega
      have hq_shr_n : (BitVec.setWidth 64 ((stv.scratch.scratch_buf[(BitVec.setWidth 64
          (stv.scratch.scratch_buf[(BitVec.setWidth 64 (sc + sv)).toNat]'hsc_sb +
            idx)).toNat]'hcs_sb &&& 0x7FFFFFFF#32) >>> (1 : Nat))).toNat <
          stv.core.flags.length := by
        rw [bv64_setWidth_32, hcs_eq, bv32_lshr1_nat, hclv.flags_len]; omega
      have hfl_len_d : ∀ i v, (stv.core.flags.set i v).length = c.max_vars := fun _ _ => by
        rw [List.length_set, hlen_d.core_ok.flags_len]
      c0_hstep_np; c0_hstep_np; c0_hstep_np; c0_hstep_np; c0_hstep_np
      c0_hstep_np; c0_hstep_np; c0_hstep_np
      · c0_hstep_np; c0_hstep_np
        exact hJcs _ _ ⟨by assumption, fullDenseInvW_set_flags hinv_d (hfl_len_d _ _),
          hcvv, hfuelv, hsbv, htmv, htrv, hmonov⟩
      · c0_hstep_np; c0_hstep_np
        exact hJcs _ _ ⟨by assumption, fullDenseInvW_set_flags hinv_d (hfl_len_d _ _),
          hcvv, hfuelv, hsbv, htmv, htrv, hmonov⟩
    · have hbin_cs : (cs &&& 0x80000000#32) = 0#32 := by
        rw [← hcs_mod]; exact hc
      unfold FidBvaRowEntryOk at hcs_ok_rw
      rw [ite_eq_right (fun h' => h' hbin_cs)] at hcs_ok_rw
      obtain ⟨hcs_ref0, hcs_ng0, hcs_sz3, hcs_sz5, _, _, _⟩ := hcs_ok_rw
      obtain ⟨hcs_refv, hcs_szv, hcs_litsv⟩ := hmonov cs.toNat hcs_ref0
      have hcs_wfv := hinvv.2.1.arena.refs_wf cs.toNat hcs_refv
      have hcs2_n : (BitVec.setWidth 64 cs + 2).toNat = cs.toNat + 2 := by
        change (BitVec.setWidth 64 cs + 2#64).toNat = _; c0_bound
      have hcs_b2_sb : (BitVec.setWidth 64 (stv.scratch.scratch_buf[(BitVec.setWidth 64
          (stv.scratch.scratch_buf[(BitVec.setWidth 64 (sc + sv)).toNat]'hsc_sb +
            idx)).toNat]'hcs_sb) + 2).toNat < stv.core.arena.length := by
        rw [hcs_eq, hcs2_n]; have := hclv.arena_len_le; have := hclv.arena_len_arr; omega
      have hcsz_eq : (stv.core.arena[cs.toNat + 2]'(by
          have := hclv.arena_len_le; have := hclv.arena_len_arr; omega)).toNat =
          fullArenaClauseSizeCore s.core cs.toNat := by
        rw [← hcs_szv]; unfold fullArenaClauseSizeCore
        rw [List.getElem?_eq_getElem (by
          have := hclv.arena_len_le; have := hclv.arena_len_arr; omega), Option.getD_some]
      let csz_bv := stv.core.arena[cs.toNat + 2]'(by
        have := hclv.arena_len_le; have := hclv.arena_len_arr; omega)
      have hcsz_s : csz_bv.toNat = fullArenaClauseSizeCore s.core cs.toNat := hcsz_eq
      c0_hstep_np; c0_hstep_np; c0_hstep_np; c0_hstep_np; c0_hstep_np
      refine wp_loop_inv
        (fun (k, ()) mk => ∃ stk : FullState,
          k.toNat ≤ csz_bv.toNat ∧ FullDenseInvW c F0 F_next stk ∧
          stk.core.cur_vars = old_cv + 1 ∧ stk.core.fuel = s.core.fuel ∧
          stk.core.arena = stv.core.arena ∧ stk.core.arena_len = stv.core.arena_len ∧
          stk.scratch.scratch_buf = s.scratch.scratch_buf ∧
          stk.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
          stk.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
          FidBvaArenaMono s.core stk.core ∧ (FullMem c stk ⋆ R) mk)
        (fun (k, _) _ => csz_bv.toNat - k.toNat)
        (fun Jk hJk => by
          c0_hstep_np
          exact hJk (0#32, ()) msv ⟨stv, Nat.zero_le _, hinvv, hcvv, hfuelv, rfl, rfl,
            hsbv, htmv, htrv, hmonov, hmsv⟩)
        (fun Jk (k, ()) mk ⟨stk, hk_le, hinvk, hcvk, hfuelk, hark, halk, hsbk, htmk, htrk,
            hmonok, hmk⟩ ihk => ?_)
      have hclk := hinvk.1.core_ok
      c0_hstep_np; c0_hstep_np
      · have hcs2_mod : (cs.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = cs.toNat + 2 := by
          rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
        have hk_lt : k.toNat < csz_bv.toNat := by
          dsimp only [csz_bv]
          have h1 : k.toNat < (stv.core.arena[(cs.toNat + BitVec.toNat (2 : BitVec 64)) %
              2 ^ 64]'(by
                rw [hcs2_mod]
                have := hclv.arena_len_le; have := hclv.arena_len_arr; omega)).toNat :=
            by simpa only [← hcs_mod] using (by assumption : _)
          simpa only [hcs2_mod] using h1
        have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
        have hcsk_n : (BitVec.setWidth 64 cs + 3 + BitVec.setWidth 64 k).toNat =
            cs.toNat + 3 + k.toNat := by
          change (BitVec.setWidth 64 cs + 3#64 + BitVec.setWidth 64 k).toNat = _; c0_bound
        have hdl_ar : cs.toNat + 3 + k.toNat < stk.core.arena.length := by
          have := hclv.arena_len_le; have := hclv.arena_len_arr; rw [hark]; omega
        have hdl_ar_sb : (BitVec.setWidth 64 (stv.scratch.scratch_buf[(BitVec.setWidth 64
            (stv.scratch.scratch_buf[(BitVec.setWidth 64 (sc + sv)).toNat]'hsc_sb +
              idx)).toNat]'hcs_sb) + 3 + BitVec.setWidth 64 k).toNat <
            stk.core.arena.length := by rw [hcs_eq, hcsk_n]; exact hdl_ar
        have hdl_mem : (stk.core.arena[cs.toNat + 3 + k.toNat]'hdl_ar).toNat ∈
            fullArenaClauseLitsCore s.core cs.toNat := by
          rw [← hcs_litsv]
          have h1 := FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (k := stv.core)
            (r := cs.toNat) (j := k.toNat) (by rw [hcs_szv]; omega)
            (by rw [← hark]; exact hdl_ar)
          have h2 := List.mem_of_getElem? h1
          simpa only [hark] using h2
        have hdl_lt : (stk.core.arena[cs.toNat + 3 + k.toNat]'hdl_ar).toNat < 2 * old_cv :=
          hinv.2.1.arena.lits_lt cs.toNat hcs_ref0 hcs_ng0 _ hdl_mem
        c0_hstep_np; c0_hstep_np; c0_hstep_np; c0_hstep_np; c0_hstep_np
        c0_hstep_np; c0_hstep_np
        c0_call hUnwatch
        refine ⟨c, stk, R, rfl, hinvk.1, hinvk.2.1.watches.layout, hmk,
          fun wvec' wstk' wu' mu hlen_u _ hwat_u hmu => ?_⟩
        have hinv_u := fullDenseInvW_of_unwatchLarge hinvk hlen_u
          (hwat_u F_next hinvk.2.1.watches)
        have hdl_shr : (BitVec.setWidth 64 ((stk.core.arena[(BitVec.setWidth 64
            (stv.scratch.scratch_buf[(BitVec.setWidth 64
              (stv.scratch.scratch_buf[(BitVec.setWidth 64 (sc + sv)).toNat]'hsc_sb +
                idx)).toNat]'hcs_sb) +
            3 + BitVec.setWidth 64 k).toNat]'hdl_ar_sb) >>> (1 : BitVec 32))).toNat <
            stk.core.flags.length := by
          rw [bv64_setWidth_32, hclk.flags_len]
          simp only [hcs_eq, hcsk_n, bv32_lshr1_bv]; omega
        have hdl_shr_n : (BitVec.setWidth 64 ((stk.core.arena[(BitVec.setWidth 64
            (stv.scratch.scratch_buf[(BitVec.setWidth 64
              (stv.scratch.scratch_buf[(BitVec.setWidth 64 (sc + sv)).toNat]'hsc_sb +
                idx)).toNat]'hcs_sb) +
            3 + BitVec.setWidth 64 k).toNat]'hdl_ar_sb) >>> (1 : Nat))).toNat <
            stk.core.flags.length := by
          rw [bv64_setWidth_32, hclk.flags_len]
          simp only [hcs_eq, hcsk_n, bv32_lshr1_nat]; omega
        have hfl_len : ∀ i v, (stk.core.flags.set i v).length = c.max_vars := fun _ _ => by
          rw [List.length_set, hclk.flags_len]
        c0_hstep_np; c0_hstep_np; c0_hstep_np; c0_hstep_np; c0_hstep_np
        c0_hstep_np; c0_hstep_np; c0_hstep_np
        · c0_hstep_np; c0_hstep_np; c0_hstep_np
          exact ihk (k + 1#32, ()) m (by dsimp only; rw [hk1]; omega)
            ⟨_, by rw [hk1]; omega,
             fullDenseInvW_set_flags hinv_u (hfl_len _ _),
             hcvk, hfuelk, hark, halk, hsbk, htmk, htrk, hmonok, by assumption⟩
        · c0_hstep_np; c0_hstep_np; c0_hstep_np
          exact ihk (k + 1#32, ()) m (by dsimp only; rw [hk1]; omega)
            ⟨_, by rw [hk1]; omega,
             fullDenseInvW_set_flags hinv_u (hfl_len _ _),
             hcvk, hfuelk, hark, halk, hsbk, htmk, htrk, hmonok, by assumption⟩
      · have hcs_refk : cs.toNat ∈ fullArenaClauseRefsCore stk.core :=
          (hmonok cs.toNat hcs_ref0).1
        have hcs_lt_k : cs.toNat < stk.core.arena.length := by
          have := hclv.arena_len_le; have := hclv.arena_len_arr; rw [hark]; omega
        have hcs_lt_sb : (BitVec.setWidth 64 (stv.scratch.scratch_buf[(BitVec.setWidth 64
            (stv.scratch.scratch_buf[(BitVec.setWidth 64 (sc + sv)).toNat]'hsc_sb +
              idx)).toNat]'hcs_sb)).toNat < stk.core.arena.length := by
          rw [hcs_eq, bv64_setWidth_32]; exact hcs_lt_k
        c0_hstep_np; c0_hstep_np; c0_hstep_np; c0_hstep_np; c0_hstep_np
        c0_hstep_np; c0_hstep_np; c0_hstep_np; c0_hstep_np; c0_hstep_np
        c0_hstep_np; c0_hstep_np; c0_hstep_np; c0_hstep_np; c0_hstep_np
        c0_hstep_np
        let ag_g := stk.core.arena_garbage + 3#64 + BitVec.setWidth 64
          (stv.core.arena[(BitVec.setWidth 64 (stv.scratch.scratch_buf[(BitVec.setWidth 64
            (stv.scratch.scratch_buf[(BitVec.setWidth 64 (sc + sv)).toNat]'hsc_sb +
              idx)).toNat]'hcs_sb) + 2).toNat]'hcs_b2_sb)
        have ⟨hinv_g, hmono_g⟩ := fullDenseInvW_of_markGarb hinvk hcs_refk ag_g
        have hhdr : fullArenaHdrCore stk.core cs.toNat =
            stk.core.arena[cs.toNat]'hcs_lt_k := by
          unfold fullArenaHdrCore
          rw [List.getElem?_eq_getElem hcs_lt_k, Option.getD_some]
        have hcs_sb_val :
            (BitVec.setWidth 64 (stv.scratch.scratch_buf[(BitVec.setWidth 64
              (stv.scratch.scratch_buf[(BitVec.setWidth 64 (sc + sv)).toNat]'hsc_sb +
                idx)).toNat]'hcs_sb)).toNat = cs.toNat := by
          rw [hcs_eq, bv64_setWidth_32]
        have har_g :
            stk.core.arena.set (BitVec.setWidth 64 (stv.scratch.scratch_buf[(BitVec.setWidth 64
              (stv.scratch.scratch_buf[(BitVec.setWidth 64 (sc + sv)).toNat]'hsc_sb +
                idx)).toNat]'hcs_sb)).toNat
              (stk.core.arena[(BitVec.setWidth 64 (stv.scratch.scratch_buf[(BitVec.setWidth 64
                (stv.scratch.scratch_buf[(BitVec.setWidth 64 (sc + sv)).toNat]'hsc_sb +
                  idx)).toNat]'hcs_sb)).toNat]'hcs_lt_sb ||| 0x00080000#32) =
            stk.core.arena.set cs.toNat (fullArenaHdrCore stk.core cs.toNat ||| 0x00080000#32) := by
          rw [hhdr]; simp only [hcs_sb_val]
        have hm_g : (FullMem c { stk with
            core := { stk.core with
              arena := stk.core.arena.set cs.toNat
                (fullArenaHdrCore stk.core cs.toNat ||| 0x00080000#32)
              arena_garbage := ag_g } } ⋆ R) m := by
          rw [← har_g]
          exact by assumption
        exact hJcs _ m ⟨hm_g, hinv_g, hcvk, hfuelk, hsbk, htmk, htrk,
          fidBvaArenaMono_trans hmonok hmono_g⟩

private theorem fid_bva_phase2_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hDelBin : FidDelBinHyp Γ) (hUnwatch : FidUnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s st0 : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv fresh : Val i32} {m0 : Mem 64}
    {bump : Nat}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hbk1 : 1 ≤ best_k.toNat) (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hmat : FidBvaMatrixInv c F_cur s (best_k.toNat + 1) bump)
    (hsc_eq : sc.toNat = fidStepsCap c.scratch_cap)
    (hmn_getD : (s.scratch.scratch_buf[2 * sc.toNat + best_k.toNat]?.getD 0#32).toNat = mn_bv.toNat)
    (hfresh_nat : fresh.toNat = 2 * s.core.cur_vars)
    (hfresh1 : (fresh ^^^ 1#32).toNat = 2 * s.core.cur_vars + 1)
    (hst0 : FidBvaStOk c F0 F_next s st0) (hm0 : (FullMem c st0 ⋆ R) m0)
    (hQ : ∀ ok s' m', FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (fidBvaPhase2Expr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr
      c.pTmp best_k sc dm_bv brow_off mn_bv fresh) m0 := by
  have hmx := c.hmaxv; have hscr_b := c.hscr; unfold dimacsBound at hmx hscr_b
  let old_cv := s.core.cur_vars
  have hmn_hi : mn_bv.toNat ≤ c.scratch_cap := by
    have h1 := (hmat.2.2.2.2.2 best_k.toNat (by omega)).2.2.2.1
    have h2 := hmat.2.2.2.2.1
    rw [← hsc_eq, hmn_getD] at h1; omega
  unfold fidBvaPhase2Expr fidBvaPhase1bExpr fidBvaPostDefragExpr fidBvaMidExpr fidBvaPreMidExpr
    fidBvaHdrExpr
  dsimp only [sSteps, sStep, sLd64, sLd32, sCall32, sLet32, sGrp0,
    sGrp64_32, sGrp64_64_32, sGrp32b, sThen, sElse, sDummyTup, sDummyVal, i64, i32,
    full_bva_commit_body]
  refine wp_loop_inv
    (fun (mi, ()) mm => ∃ stm : FullState, mi.toNat ≤ mn_bv.toNat ∧
      FidBvaStOk c F0 F_next s stm ∧ (FullMem c stm ⋆ R) mm)
    (fun (mi, _) _ => mn_bv.toNat - mi.toNat)
    (fun Jm hJm => ?_) (fun Jm (mi, ()) mm ⟨stm, hmi_le, hstm, hmm⟩ ihm => ?_)
  · c0_hstep; exact hJm (0#32, ()) m0 ⟨st0, Nat.zero_le _, hst0, hm0⟩
  c0_hsteps_nogrp
  · have hmi_lt : mi.toNat < mn_bv.toNat := by c0_bound
    have hmi1 : (mi + 1#32).toNat = mi.toNat + 1 := by c0_bound
    have hdel := fid_bva_del_col_wp (Γ := Γ) (Q := Q) (X := X) hDelBin hUnwatch
      (F_next := F_next) (dm_bv := dm_bv) (brow_off := brow_off) (mn_bv := mn_bv)
      (fresh := fresh) (Jm := Jm) hinv hbk1 hbk_sc hmat hsc_eq
      (by rw [hmn_getD]; exact hmi_lt) hmm hstm (fun st2 m2 hst2 hm2 =>
        ihm (mi + 1#32, ()) m2 (by dsimp only; rw [hmi1]; omega)
          ⟨st2, by rw [hmi1]; omega, hst2, hm2⟩)
    unfold fidBvaDelColExpr fidBvaPhase2Expr fidBvaPhase1bExpr fidBvaPostDefragExpr fidBvaMidExpr
      fidBvaPreMidExpr fidBvaHdrExpr at hdel
    dsimp only [sStep, sLd64, sLd32, sCall32, sLet32,
      sGrp0, sGrp1, sGrp64_32, sGrp64_64_32, sGrp32b, sThen, sElse, sDummyTup, sDummyVal, i64, i32,
      full_bva_commit_body] at hdel
    exact hdel
  · obtain ⟨hinvm, hcvm, hfuelm, _, htmm, htrm, _⟩ := hstm
    have hclm := hinvm.1.core_ok; have hscm := hinvm.1.scratch_ok; have hcv_le := hclm.cur_vars_le
    have h2cv : (BitVec.ofNat 64 stm.core.cur_vars <<< (1 : Nat)).toNat = 2 * (old_cv + 1) := by
      rw [hcvm]; simp only [bv_c0]; omega
    refine wp_loop_inv
      (fun (zi, ()) mzi => ∃ wsz : List (BitVec 32), zi.toNat ≤ 2 * (old_cv + 1) ∧
        wsz.length = 2 * c.max_vars ∧
        (FullMem c { stm with scratch := { stm.scratch with wsort := wsz } } ⋆ R) mzi)
      (fun (zi, _) _ => 2 * (old_cv + 1) - zi.toNat) (fun Jz hJz => ?_)
      (fun Jz (zi, ()) mzi ⟨wsz, hzi_le, hwsz_l, hmzi⟩ ihz => ?_)
    · c0_hstep; exact hJz (0#64, ()) mm ⟨stm.scratch.wsort, Nat.zero_le _, hscm.wsort_len, hmm⟩
    c0_hsplit
    · have hzi_lt : zi.toNat < 2 * (old_cv + 1) := by
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
        (fun _ => by dsimp only [old_cv]; rw [hcvm]; omega) hfuelm htmm htrm hm

/-! ## 3. Phase 1b Negative Clauses & Phase 1a Binary Propagation -/

private theorem fid_bva_phase1b_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hAddBin : FidAddBinHyp Γ) (hAllocCl : FidAllocClHyp Γ) (hWPush : FidWPushHyp Γ)
    (hDelBin : FidDelBinHyp Γ) (hUnwatch : FidUnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s st1a : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv fresh : Val i32}
    {ok1a : Val .bool} {m1a : Mem 64} {bump : Nat}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hbk1 : 1 ≤ best_k.toNat) (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hmat : FidBvaMatrixInv c F_cur s (best_k.toNat + 1) bump)
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
    (hst1a : FidBvaStOk c F0 F_next s st1a) (hm1a : (FullMem c st1a ⋆ R) m1a)
    (hQ : ∀ ok s' m', FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (fidBvaPhase1bExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr
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
  unfold fidBvaPhase1bExpr fidBvaPostDefragExpr fidBvaMidExpr fidBvaPreMidExpr fidBvaHdrExpr
  dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrp0, sGrp64_32, sGrp64_64_32,
    sGrp32b, sThen, sElse, sDummyTup, sDummyVal, i64, i32, full_bva_commit_body]
  refine wp_join_group (ts := [i32, .bool])
    (fun (_, ok1b, ()) m1b => ∃ st1b : FullState,
      FidBvaStOk c F0 F_next s st1b ∧ (FullMem c st1b ⋆ R) m1b)
    (fun _ (_, ok1b, ()) m1b ⟨st1b, hst1b, hm1b⟩ => ?_) (fun J1b hJ1b => ?_)
  · c0_hsteps_nogrp
    · have hp2 := fid_bva_phase2_wp (Γ := Γ) (Q := Q) (X := X) hDelBin hUnwatch
        (F_next := F_next) (dm_bv := dm_bv) (brow_off := brow_off) (mn_bv := mn_bv)
        (fresh := fresh) hinv hbk1 hbk_sc hmat hsc_eq hmn_getD hfresh_nat hfresh1 hst1b hm1b hQ
      unfold fidBvaPhase2Expr fidBvaPhase1bExpr fidBvaPostDefragExpr fidBvaMidExpr
        fidBvaPreMidExpr fidBvaHdrExpr at hp2
      dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrp0,
        sGrp64_32, sGrp64_64_32, sGrp32b, sThen, sElse, sDummyTup, sDummyVal, i64, i32,
        full_bva_commit_body] at hp2
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
          (by dsimp only; omega) (fun h => absurd h (by decide)) hfuel1b htm1b htr1b hmzi
  · refine wp_loop_inv
      (fun (mi, okm, ()) mm => ∃ stm : FullState, mi.toNat ≤ mn_bv.toNat ∧
        FidBvaStOk c F0 F_next s stm ∧ (FullMem c stm ⋆ R) mm)
      (fun (mi, _, _) _ => mn_bv.toNat - mi.toNat) (fun J1bl hJ1bl => by
        c0_hsteps; exact hJ1bl (0#32, ok1a, ()) m1a ⟨st1a, Nat.zero_le _, hst1a, hm1a⟩)
      (fun J1bl (mi, okm, ()) mm ⟨stm, hmi_le, hstm, hmm⟩ ihm => ?_)
    obtain ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono⟩ := hstm
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
          FidBvaStOk c F0 F_next s st1)
        (fun _ (ok', ()) m1 ⟨st1, hm1, hst1⟩ => by
          c0_hsteps; exact ihm (mi + 1#32, ok', ()) m1 (by dsimp only; rw [hmi1]; omega)
            ⟨st1, by rw [hmi1]; omega, hst1, hm1⟩)
        (fun Jtop hJtop => ?_)
      c0_hsplit
      · c0_hsteps
        have hbin_ct : (c_top &&& 0x80000000#32) ≠ 0#32 := by
          simpa only [← hctop_mod] using (by assumption : _)
        unfold FidBvaRowEntryOk at hctop_ok; rw [ite_eq_left hbin_ct] at hctop_ok
        obtain ⟨_, hres_q, _⟩ := hctop_ok; c0_call hAddBin
        refine ⟨c, F0, F_next, stm, R, rfl, hinvm.1, hinvm.2.1, hinvm.2.2.2.2.2.1,
          fun _ _ => ?_, hmm,
          fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 hlen1' hw1' _ _ _ hms1' => ?_⟩
        · rw [hctop_eq]; dsimp only [resm] at hres_q; rw [hres_q] at hresm_ent
          simpa only [show (1 : BitVec 32) = 1#32 from rfl, hfresh1,
            show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl] using hresm_ent
        · have hinv1' := fullDenseInvW_of_addBin hinvm hlen1' hw1'; c0_hsteps
          · exact hJ1b (mi, false, ()) m1 ⟨_, ⟨hinv1', hcvm, hfuelm, hsbm, htmm, htrm, hmono⟩,
            hms1'⟩
          · exact hJ1b (mi, false, ()) m1 ⟨_, ⟨hinv1', hcvm, hfuelm, hsbm, htmm, htrm, hmono⟩,
            hms1'⟩
          · exact hJ1b (mi, false, ()) m1 ⟨_, ⟨hinv1', hcvm, hfuelm, hsbm, htmm, htrm, hmono⟩,
            hms1'⟩
          · exact hJtop (true, ()) m1 ⟨_, hms1', hinv1', hcvm, hfuelm, hsbm, htmm, htrm, hmono⟩
      · have hbin_ct : (c_top &&& 0x80000000#32) = 0#32 := by
          simpa only [← hctop_mod] using (by assumption : _)
        unfold FidBvaRowEntryOk at hctop_ok
        rw [ite_eq_right (fun h' => h' hbin_ct)] at hctop_ok
        obtain ⟨hct_ref0, hct_ng0, hct_sz3, _, hfbk_mem, hres_perm_f, _⟩ := hctop_ok
        have hlt := fid_bva_large_top_wp (Γ := Γ) (Q := Q) (X := X) hAllocCl hWPush hUnwatch
          (F_next := F_next) (best_k := best_k) (mi := mi) (resm := resm)
          (c_top := stm.scratch.scratch_buf[(BitVec.setWidth 64
            (brow_off + mi)).toNat]'hctop_sb)
          (fresh := fresh) (J4 := J1b) (J6 := Jtop) hinv (by omega) hfresh1 hresm_lt
          hresm_nd hresm_ent (by rwa [hctop_eq]) (by rwa [hctop_eq]) (by rwa [hctop_eq])
          (by rwa [hctop_eq]) (by rwa [hctop_eq]) hmm
          ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono⟩
          (fun st1 m1 hm1 hst1 => hJ1b (mi, false, ()) m1 ⟨st1, hst1, hm1⟩)
          (fun ok' st1 m1 hm1 hst1 => hJtop (ok', ()) m1 ⟨st1, hm1, hst1⟩)
        unfold fidBvaLargeTopExpr fidBvaLargeWatchExpr fidBZext fidBOp64 fidBOp32 fidBCmp32
          fidBPtr32 fidBLd32 at hlt
        exact hlt
    · exact hJ1b (mi, okm, ()) mm ⟨stm, ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono⟩, hmm⟩
    · exact hJ1b (mi, okm, ()) mm ⟨stm, ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono⟩, hmm⟩

private theorem fid_bva_post_defrag_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hInitFresh : ∀ args m Q X, fullInitFreshVarHeapSpec args m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] args m Q X)
    (hAddBin : FidAddBinHyp Γ) (hAllocCl : FidAllocClHyp Γ) (hWPush : FidWPushHyp Γ)
    (hDelBin : FidDelBinHyp Γ) (hUnwatch : FidUnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sd : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv : Val i32} {md : Mem 64} {bump : Nat}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hbk1 : 1 ≤ best_k.toNat) (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hmat : FidBvaMatrixInv c F_cur s (best_k.toNat + 1) bump)
    (hcv_lt : s.core.cur_vars < c.max_vars)
    (hsc_eq : sc.toNat = fidStepsCap c.scratch_cap)
    (hdm_bv : dm_bv.toNat = best_k.toNat + 1)
    (hbo_getD : (s.scratch.scratch_buf[sc.toNat + best_k.toNat]?.getD 0#32).toNat = brow_off.toNat)
    (hmn_getD : (s.scratch.scratch_buf[2 * sc.toNat + best_k.toNat]?.getD 0#32).toNat = mn_bv.toNat)
    (hmd : (FullMem c sd ⋆ R) md) (hsd : FidBvaPreOk c F0 F_cur s sd)
    (hQ : ∀ ok s' m', FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (fidBvaPostDefragExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec
      best_k sc dm_bv brow_off mn_bv) md := by
  obtain ⟨hinvd, hcvd, hfueld, hard, hald, hsbd, htmd, htrd⟩ := hsd
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
  unfold fidBvaPostDefragExpr fidBvaMidExpr fidBvaPreMidExpr fidBvaHdrExpr
  dsimp only [sSteps, sStep,
    sLet32, sLd64, sLd32, sCall32, sGrp0, sGrp64_32, sGrp64_64_32, sThen, sElse, sDummyTup,
    sDummyVal, i64, i32, full_bva_commit_body]
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
    fun vals' mrk' fl' lvl' rsns' wvec' unass' sc' m1 hlen1 hext1 hsb1 hws1 htm1 htr1 hss1
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
      FidBvaStOk c F0 F_next s st1a ∧ (FullMem c st1a ⋆ R) m1a)
    (fun _ (_, ok1a, ()) m1a ⟨st1a, hst1a, hm1a⟩ => ?_) (fun J1a hJ1a => ?_)
  · have hp1b := fid_bva_phase1b_wp (Γ := Γ) (Q := Q) (X := X)
      hAddBin hAllocCl hWPush hDelBin hUnwatch (F_next := F_next)
      (dm_bv := dm_bv) (brow_off := brow_off) (mn_bv := mn_bv)
      (fresh := fv_bv <<< (OfNat.ofNat 1 : BitVec 32)) (ok1a := ok1a)
      hinv hbk1 hbk_sc hmat hsc_eq hbo_getD hmn_getD hfresh_bv hfresh1_bv resAt
      (fun idx hidx => by
        have hspec := Classical.choose_spec (hbk_entries idx hidx)
        have heq : resAt idx = Classical.choose (hbk_entries idx hidx) := by
          dsimp only [resAt]; rw [dite_eq_left hidx]
        rw [heq]; refine ⟨hspec.1, hspec.2.1, hspec.2.2.1, ?_⟩
        have hmem : resAt idx ∈ Qs := List.mem_map.mpr ⟨idx, List.mem_range.mpr hidx, rfl⟩
        have h1 := hneg_ent (resAt idx) hmem; rwa [heq] at h1)
      hst1a hm1a hQ
    unfold fidBvaPhase1bExpr fidBvaPostDefragExpr fidBvaMidExpr fidBvaPreMidExpr fidBvaHdrExpr
      at hp1b
    dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrp0, sGrp64_32, sGrp64_64_32,
      sGrp32b, sThen, sElse, sDummyTup, sDummyVal, i64, i32, full_bva_commit_body] at hp1b
    exact hp1b
  · refine wp_loop_inv
      (fun (si, ()) msi => ∃ sts : FullState, si.toNat ≤ dm ∧
        FidBvaStOk c F0 F_next s sts ∧ (FullMem c sts ⋆ R) msi)
      (fun (si, _) _ => dm - si.toNat) (fun Js hJs => by
        c0_hfast; exact hJs (0#32, ()) m ⟨st0, Nat.zero_le _,
          ⟨hinv0, rfl, hfueld, hsb1.trans hsbd, htm1.trans htmd, htr1.trans htrd, hmono0⟩, hm⟩)
      (fun Js (si, ()) msi ⟨sts, hsi_le, hsts, hmsi⟩ ihs => ?_)
    obtain ⟨hinvs, hcvs, hfuels, hsbs, htms, htrs, hmonos⟩ := hsts
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
      have hfs_shr : (BitVec.setWidth 64 ((sts.scratch.scratch_buf[(BitVec.setWidth 64
          si).toNat]'hfs_sb) >>> (1 : BitVec 32))).toNat < fl_s1.length := by
        rw [bv64_setWidth_32, bv32_lshr1_bv, hlen_s1.core_ok.flags_len]; omega
      have hfs_shr_n : (BitVec.setWidth 64 ((sts.scratch.scratch_buf[(BitVec.setWidth 64
          si).toNat]'hfs_sb) >>> (1 : Nat))).toNat < fl_s1.length := by
        rw [bv64_setWidth_32, bv32_lshr1_nat, hlen_s1.core_ok.flags_len]; omega
      c0_hfast
      · exact hJ1a (si, false, ()) ms1 ⟨_, ⟨hinv_s1, hcvs, hfuels, hsbs, htms, htrs, hmonos⟩, hms1⟩
      · exact hJ1a (si, false, ()) ms1 ⟨_, ⟨hinv_s1, hcvs, hfuels, hsbs, htms, htrs, hmonos⟩, hms1⟩
      · exact hJ1a (si, false, ()) ms1 ⟨_, ⟨hinv_s1, hcvs, hfuels, hsbs, htms, htrs, hmonos⟩, hms1⟩
      · exact ihs (si + 1#32, ()) m (by dsimp only; rw [hsi1]; omega)
          ⟨_, by rw [hsi1]; omega,
           ⟨fullDenseInvW_set_flags hinv_s1 (by simp [hlen_s1.core_ok.flags_len]),
            hcvs, hfuels, hsbs, htms, htrs, hmonos⟩, hm⟩
    · exact hJ1a (si, true, ()) msi ⟨sts, ⟨hinvs, hcvs, hfuels, hsbs, htms, htrs, hmonos⟩, hmsi⟩

/-! ## 4. Top-Level Exported `full_bva_commit_fid_wp` (`fidBvaCommitSpec`) -/

private theorem fid_bva_pre_exit_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hDefrag : ∀ args m Q X, Full.fullWstackDefragSpec args m Q X →
      Γ "full_wstack_defrag" [i64] [] args m Q X)
    (hInitFresh : ∀ args m Q X, fullInitFreshVarHeapSpec args m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] args m Q X)
    (hAddBin : FidAddBinHyp Γ) (hAllocCl : FidAllocClHyp Γ) (hWPush : FidWPushHyp Γ)
    (hDelBin : FidDelBinHyp Γ) (hUnwatch : FidUnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv : Val i32}
    {need_ar need_w : Val i64} {m : Mem 64} {bump : Nat}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hbk1 : 1 ≤ best_k.toNat) (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hmat : FidBvaMatrixInv c F_cur s (best_k.toNat + 1) bump)
    (hsc_eq : sc.toNat = fidStepsCap c.scratch_cap)
    (hdm_bv : dm_bv.toNat = best_k.toNat + 1)
    (hbo_getD :
      (s.scratch.scratch_buf[sc.toNat + best_k.toNat]?.getD 0#32).toNat = brow_off.toNat)
    (hmn_getD :
      (s.scratch.scratch_buf[2 * sc.toNat + best_k.toNat]?.getD 0#32).toNat = mn_bv.toNat)
    (hm : (FullMem c s ⋆ R) m) (hcv_lt : s.core.cur_vars < c.max_vars)
    (hQ : ∀ ok s' m', FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (fidBvaPreExitExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec
      best_k sc dm_bv brow_off mn_bv need_ar need_w) m := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  unfold fidBvaPreExitExpr fidBvaPreMidExpr fidBvaHdrExpr
  dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrp0, sGrp64_32,
    sGrp64_64_32, sGrp64_64_32v, sThen, sElse, sDummyTup, sDummyVal, i64, i32,
    full_bva_commit_body]
  refine wp_join_state0 (α := FullState) (fun sd md => (FullMem c sd ⋆ R) md ∧
    FidBvaPreOk c F0 F_cur s sd)
    (fun _ sd md ⟨hmd, hsd⟩ => ?_) (fun Jdef hJdef => ?_)
  · have hpd := fid_bva_post_defrag_wp (Γ := Γ) (Q := Q) (X := X)
      hInitFresh hAddBin hAllocCl hWPush hDelBin hUnwatch
      (sc := sc) (dm_bv := dm_bv) (brow_off := brow_off) (mn_bv := mn_bv)
      hinv hbk1 hbk_sc hmat hcv_lt hsc_eq hdm_bv hbo_getD hmn_getD hmd hsd hQ
    unfold fidBvaPostDefragExpr fidBvaMidExpr fidBvaPreMidExpr fidBvaHdrExpr at hpd
    dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrp0, sGrp64_32,
      sGrp64_64_32, sThen, sElse, sDummyTup, sDummyVal, i64, i32,
      full_bva_commit_body] at hpd
    exact hpd
  · refine wp_join_state0 (α := Unit) (fun _ md => md = m)
      (fun _ _ md hmd => ?_) (fun Jneed hJneed => ?_)
    · subst md; refine wp_join_state0 (α := FullState)
        (fun sd md => (FullMem c sd ⋆ R) md ∧ FidBvaPreOk c F0 F_cur s sd)
        (fun _ sd md ⟨hmd, hinvd, hcvd, hfueld, hard, hald, hsbd, htmd, htrd⟩ => ?_)
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
              hfueld htmd htrd hmzi
        · c0_hfast
          · exact hJfail () md rfl
          · exact hJfail () md rfl
          · exact hJdef sd md
              ⟨hmd, hinvd, hcvd, hfueld, hard, hald, hsbd, htmd, htrd⟩
      · c0_hsplit
        · c0_call hDefrag
          refine ⟨c, s, R, rfl, hinv.1, hinv.2.1.watches.layout, hm,
            fun wvec' wstk' wlen' wsort' md hlen' hlay' _ hsl' hmd =>
              hJd1 _ md ⟨hmd, fullDenseInvW_of_defrag hinv hlen' hlay' hsl',
                rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
        · c0_hstep
          exact hJd1 s m ⟨hm, hinv, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · c0_hsplit
      · c0_hstep
        exact hJneed () m rfl
      · c0_hsplit
        · c0_hstep
          exact hJneed () m rfl
        · c0_hstep
          exact hJdef s m ⟨hm, hinv, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `full_bva_commit` (`fidBvaStepsCap`, dynamic scratch-scaled matrix, `deg` updates)
satisfies `fidBvaCommitSpec` parametrically in `Γ`. -/
theorem full_bva_commit_fid_wp (Γ : Env)
    (hStepsCap : ∀ args m Q X, fidBvaStepsCapSpec args m Q X →
      Γ "full_bva_steps_cap_fid" [i64] [i32] args m Q X)
    (hDefrag : ∀ args m Q X, Full.fullWstackDefragSpec args m Q X →
      Γ "full_wstack_defrag" [i64] [] args m Q X)
    (hInitFresh : ∀ args m Q X, fullInitFreshVarHeapSpec args m Q X →
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
    ∀ args m Q X, fidBvaCommitSpec args m Q X → Func.wp Γ full_bva_commit_body args m Q X := by
  rintro ⟨h, best_k, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, bump, rfl, hinv, hbk1, hbk_sc, hmat, hm, hQ⟩
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
  · exact hQ false s m hinv.toDense (Nat.le_refl _) (fun h => absurd h (by decide)) rfl rfl rfl hm
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
            rfl rfl rfl hm
        · exact hQ false s m hinv.toDense (Nat.le_refl _) (fun h => absurd h (by decide))
            rfl rfl rfl hm
        · exact hQ false s m hinv.toDense (Nat.le_refl _) (fun h => absurd h (by decide))
            rfl rfl rfl hm
        · have hcv_lt : s.core.cur_vars < c.max_vars := by c0_bound
          have htail := fid_bva_pre_exit_wp (Γ := Γ) (Q := Q) (X := X)
            hDefrag hInitFresh hAddBin hAllocCl hWPush hDelBin hUnwatch
            (sc := sc) (dm_bv := best_k + 1#32) (brow_off := brow_off) (mn_bv := mn_bv)
            (need_ar := need_ar) (need_w := need_w) (bump := bump)
            hinv hbk1 hbk_sc hmat hsc_nat hdm_bv hbo_getD hmn_getD hm hcv_lt hQ
          unfold fidBvaPreExitExpr fidBvaPreMidExpr fidBvaHdrExpr at htail
          dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrp0, sGrp64_32,
            sGrp64_64_32, sGrp64_64_32v, sThen, sElse, sDummyTup, sDummyVal, i64, i32,
            full_bva_commit_body] at htail
          rw [← hbo_eq, ← hmn_eq] at htail
          exact htail

end LeanQbe.T.Examples.Kissat.FullFidelityBva
