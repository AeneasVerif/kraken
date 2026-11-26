/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep8
public import LeanQbe.T.Examples.Kissat.FullFidelityStep8ProofBva0
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
# Kissat Fidelity Step-8 BVA Commit WP Proof (`FullFidelityStep8ProofBva`)

Parametric `(Γ : Env)` WP proof (`0` `import all`, `public section`, `XPost`-polymorphic) of
`full_bva_commit_step8_wp`: Step-8 `FullFidelityStep8.full_bva_commit_body` satisfies
`FullFidelityStep7.step7BvaCommitSpec`, threading `defrag_dirty` to skip redundant `wsort` (`cnt`)
wipes when defrag could not run while preserving every state & matrix invariant.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep8

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullArenaTactics
open FullBvaHeap FullBvaHeap.FullBvaHeapHelpers FullBvaHeap.FullBvaHeapTactics
open FullBvaHeap.FullBvaHeapScanHelpers FullM4Bva
open LeanQbe.T.Examples.Kissat.FullFidelityBva
open LeanQbe.T.Examples.Kissat.FullFidelityStep7
open LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof2a
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

theorem bv32_shl1_xor1 {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
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

theorem bv32_shl1_or1 {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    ((x <<< (1 : Nat)) ||| 1#32).toNat = 2 * x.toNat + 1 := by
  have hev : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
    rw [bv32_shl1_nat, Nat.mod_eq_of_lt (by omega)]
  rw [FullBvaFwdTactics.bv32_or1_of_even (by rw [hev]; omega), hev]

theorem fullDenseInvW_set_wsort {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {ws' : List (BitVec 32)} (hws : ws'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with wsort := ws' } } :=
  fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len)
    (sc' := { s.scratch with wsort := ws' }) hinv hinv.1.core_ok.repr_len
    hinv.1.core_ok.min_clr_len_arr hinv.1.core_ok.tmp_len_arr hinv.1.core_ok.flags_len
    hinv.1.core_ok.tmp_len_le { hinv.1.scratch_ok with wsort_len := hws } rfl rfl

theorem fullDenseInvW_set_sb {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {sb' : List (BitVec 32)} (hsb : sb'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with scratch_buf := sb' } } :=
  fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len)
    (sc' := { s.scratch with scratch_buf := sb' }) hinv hinv.1.core_ok.repr_len
    hinv.1.core_ok.min_clr_len_arr hinv.1.core_ok.tmp_len_arr hinv.1.core_ok.flags_len
    hinv.1.core_ok.tmp_len_le { hinv.1.scratch_ok with scratch_buf_len := hsb } rfl rfl

/-! ## 1. Invariant Preservation Helpers & Commit AST Navigators -/

abbrev S8PreOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sd : FullState) : Prop :=
  FullDenseInvW c F0 F_cur sd ∧ sd.core.cur_vars = s.core.cur_vars ∧
  sd.core.fuel = s.core.fuel ∧ sd.core.arena = s.core.arena ∧
  sd.core.arena_len = s.core.arena_len ∧ sd.scratch.scratch_buf = s.scratch.scratch_buf ∧
  sd.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  sd.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ sd.scratch.res_sz = s.scratch.res_sz

abbrev S8DelOk (c : FullCfg) (F0 : CNF Nat) (F_next : List (List Nat))
    (stF st : FullState) : Prop :=
  FullDenseInvW c F0 F_next st ∧ st.core.cur_vars = stF.core.cur_vars ∧
  st.core.fuel = stF.core.fuel ∧ st.scratch = stF.scratch ∧
  st.core.arena_len = stF.core.arena_len ∧ FidBvaArenaMono stF.core st.core

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

theorem fullDenseInvW_of_defrag {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

theorem fullDenseInvW_of_addBin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

@[expose] def sDummyVal : (t : Ty) → Val t
  | .bits _ => 0 | .bool => true | .float _ => 0 | .pair a b => (sDummyVal a, sDummyVal b)
@[expose] def sDummyTup : (ts : List Ty) → Tup Val ts
  | [] => () | t :: ts => (sDummyVal t, sDummyTup ts)

@[expose] def sStep {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := ts) _ k => k (sDummyTup ts) | .load t _ k => k (sDummyVal t)
  | .store _ _ k => k | .call (bs := bs) _ _ k => k (sDummyTup bs) | _ => .hlt
@[expose] def sSteps {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e | n + 1, e => sSteps n (sStep e)

@[expose] def sLd64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 64) _ k => k v | _ => .hlt
@[expose] def sLd32 {rs : List Ty} (v : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 32) _ k => k v | _ => .hlt
@[expose] def sCall32 {rs : List Ty} (v : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .call (bs := [.bits 32]) _ _ k => k (v, ()) | _ => .hlt
@[expose] def sLet32 {rs : List Ty} (v : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := [.bits 32]) _ k => k (v, ()) | _ => .hlt
@[expose] def sThen {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ t _ => t | _ => .hlt
@[expose] def sElse {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ _ e => e | _ => .hlt
@[expose] def sGrp1 {rs : List Ty} (J : Cont [i32]) (x : Val i32) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32]]) bs _ =>
    (match bs (J, ()) with | .cons f .nil => f (x, ())) | _ => .hlt
@[expose] def sGrpb {rs : List Ty} (J : Cont [.bool]) (b : Val .bool) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bool]]) bs _ =>
    (match bs (J, ()) with | .cons f .nil => f (b, ())) | _ => .hlt
@[expose] def sGrp64_32 {rs : List Ty} (J : Cont [i64, i32]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64, .bits 32]]) bs _ =>
    (match bs (J, ()) with | .cons f .nil => f (0#64, 0#32, ())) | _ => .hlt
@[expose] def sGrp64_32v {rs : List Ty} (J : Cont [i64, i32]) (w : Val i64) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64, .bits 32]]) bs _ =>
    (match bs (J, ()) with | .cons f .nil => f (w, 0#32, ())) | _ => .hlt
@[expose] def sGrp64_64_32 {rs : List Ty} (J : Cont [i64, i64, i32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64, .bits 64, .bits 32]]) bs _ =>
    (match bs (J, ()) with | .cons f .nil => f (0#64, 0#64, 0#32, ())) | _ => .hlt
@[expose] def sGrp64_64_32v {rs : List Ty} (J : Cont [i64, i64, i32])
    (a b : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64, .bits 64, .bits 32]]) bs _ =>
    (match bs (J, ()) with | .cons f .nil => f (a, b, 0#32, ())) | _ => .hlt
@[expose] def sGrp32bb {rs : List Ty} (J : Cont [i32, .bool, .bool])
    (a : Val i32) (b c : Val .bool) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bool, .bool]]) bs _ =>
    (match bs (J, ()) with | .cons f .nil => f (a, b, c, ())) | _ => .hlt
@[expose] def sGrp32_32 {rs : List Ty} (J : Cont [i32, i32]) (a b : Val i32) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32]]) bs _ =>
    (match bs (J, ()) with | .cons f .nil => f (a, b, ())) | _ => .hlt

@[expose, irreducible] def s8HdrExpr (h pAr pScr : Val i64) (best_k sc : Val i32) :
    Expr Val Cont [.bool] :=
  FullFidelityStep8.full_bva_commit_body Val Cont (h, best_k, ())
    |> sSteps 3 |> sElse |> sSteps 2 |> sCall32 sc |> sStep |> sElse |> sStep |> sElse |> sStep
    |> sLd64 pAr |> sStep |> sLd64 pScr

@[expose, irreducible] def s8PreMidExpr (h pAr pScr pCnt pFl pWv : Val i64)
    (best_k sc dm brow_off mn : Val i32) : Expr Val Cont [.bool] :=
  s8HdrExpr h pAr pScr best_k sc |> sStep |> sLd64 pCnt |> sStep |> sLd64 pFl
    |> sStep |> sLd64 pWv |> sLet32 dm |> sSteps 4 |> sLd32 brow_off
    |> sSteps 5 |> sLd32 mn |> sSteps 6

@[expose, irreducible] def s8MidExpr (dd : Val .bool) (e : Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  e |> sGrp64_32 (fun (_ : Tup Val [i64, i32]) (_ : Mem 64) => True) |> sStep |> sElse
    |> sGrp64_64_32 (fun (_ : Tup Val [i64, i64, i32]) (_ : Mem 64) => True) |> sStep |> sElse
    |> sSteps 5 |> sElse |> sSteps 5 |> sElse |> sSteps 6 |> sElse
    |> sGrpb (fun (_ : Tup Val [.bool]) (_ : Mem 64) => True) dd

@[expose, irreducible] def s8PreExitExpr (h pAr pScr pCnt pFl pWv : Val i64)
    (best_k sc dm brow_off mn : Val i32) (need_ar need_w : Val i64) :
    Expr Val Cont [.bool] :=
  s8PreMidExpr h pAr pScr pCnt pFl pWv best_k sc dm brow_off mn
    |> sGrp64_32 (fun (_ : Tup Val [i64, i32]) (_ : Mem 64) => True) |> sStep |> sElse
    |> sGrp64_64_32v (fun (_ : Tup Val [i64, i64, i32]) (_ : Mem 64) => True) need_ar need_w
    |> sStep |> sElse |> sSteps 5 |> sElse |> sSteps 5 |> sElse |> sSteps 6 |> sElse

@[expose, irreducible] def s8PostDefragExpr (h pAr pScr pCnt pFl pWv : Val i64)
    (best_k sc dm brow_off mn : Val i32) (dd : Val .bool) : Expr Val Cont [.bool] :=
  s8PreMidExpr h pAr pScr pCnt pFl pWv best_k sc dm brow_off mn |> s8MidExpr dd

@[expose, irreducible] def s8Phase1bExpr (h pAr pScr pCnt pFl pWv pDeg pTmp : Val i64)
    (best_k sc dm brow_off mn fresh : Val i32) (dd ok1a : Val .bool) : Expr Val Cont [.bool] :=
  s8PostDefragExpr h pAr pScr pCnt pFl pWv best_k sc dm brow_off mn dd
    |> sSteps 10 |> sLd64 pDeg |> sSteps 22 |> sLet32 fresh |> sStep |> sLd64 pTmp
    |> sGrp32bb (fun (_ : Tup Val [i32, .bool, .bool]) (_ : Mem 64) => True) 0#32 dd ok1a

@[expose, irreducible] def s8Phase2Expr (h pAr pScr pCnt pFl pWv pDeg pTmp : Val i64)
    (best_k sc dm brow_off mn fresh mi0 : Val i32) (dd1a dd1b : Val .bool) :
    Expr Val Cont [.bool] :=
  s8Phase1bExpr h pAr pScr pCnt pFl pWv pDeg pTmp best_k sc dm brow_off mn fresh dd1a true
    |> sGrp32bb (fun (_ : Tup Val [i32, .bool, .bool]) (_ : Mem 64) => True) mi0 dd1b true
    |> sThen

@[expose, irreducible] def s8DelExpr (h pAr pScr pCnt pFl pWv pDeg pTmp : Val i64)
    (best_k sc dm brow_off mn fresh mi0 : Val i32) (dd1a dd1b : Val .bool) :
    Expr Val Cont [.bool] :=
  s8Phase2Expr h pAr pScr pCnt pFl pWv pDeg pTmp best_k sc dm brow_off mn fresh mi0 dd1a dd1b
    |> sGrp1 (fun (_ : Tup Val [i32]) (_ : Mem 64) => True) 0#32 |> sStep |> sElse

@[expose, irreducible] def s8DelRowExpr (h pAr pScr pCnt pFl pWv pDeg pTmp : Val i64)
    (best_k sc dm brow_off mn fresh mi0 mv qsv : Val i32) (dd1a dd1b : Val .bool)
    (Jq : Cont [i32, i32]) : Expr Val Cont [.bool] :=
  s8DelExpr h pAr pScr pCnt pFl pWv pDeg pTmp best_k sc dm brow_off mn fresh mi0 dd1a dd1b
    |> sStep |> sGrp32_32 Jq mv qsv |> sStep |> sThen

@[expose, irreducible] def s8FinalExpr (h pAr pScr pCnt pFl pWv pDeg pTmp : Val i64)
    (best_k sc dm brow_off mn fresh mi0 mv qsv : Val i32) (dd1a dd1b : Val .bool) :
    Expr Val Cont [.bool] :=
  s8DelExpr h pAr pScr pCnt pFl pWv pDeg pTmp best_k sc dm brow_off mn fresh mi0 dd1a dd1b
    |> sStep |> sGrp32_32 (fun (_ : Tup Val [i32, i32]) (_ : Mem 64) => True) mv qsv
    |> sStep |> sElse

abbrev FidDelBinHyp (Γ : Env) :=
  ∀ a m Q X, Full.fullDeleteBinarySpec a m Q X → Γ "full_delete_binary" [i64, i32, i32] [] a m Q X
abbrev FidUnwatchHyp (Γ : Env) :=
  ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X → Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X
abbrev FidAddBinHyp (Γ : Env) :=
  ∀ a m Q X, Full.fullAddBinSpec a m Q X → Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X
abbrev FidAllocClHyp (Γ : Env) :=
  ∀ a m Q X, Full.fullAllocClSpec a m Q X → Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X
abbrev FidWPushHyp (Γ : Env) :=
  ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
    Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X

/-! ## 2. Phase 2: Row Compaction, Per-Row Deletion Sweep & Conditional Wipe -/

private theorem s8_del_row_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hDelBin : FidDelBinHyp Γ) (hUnwatch : FidUnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_next : List (List Nat)} {stF std : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv fresh mi0 mv qsv : Val i32}
    {dd1a dd1b : Val .bool} {Jq : Cont [i32, i32]} {m0 : Mem 64}
    (hsc_eq : sc.toNat = fidStepsCap c.scratch_cap)
    (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hqs_pos : 0 < qsv.toNat) (hqs_le : qsv.toNat ≤ best_k.toNat + 1)
    (hro : ∀ q ≤ best_k.toNat, s7Ro (fidStepsCap c.scratch_cap) stF.scratch.scratch_buf q +
      mn_bv.toNat ≤ c.scratch_cap)
    (hval : ∀ q ≤ best_k.toNat, ∀ j < mn_bv.toNat, Step7RowRefOk stF
      (stF.scratch.scratch_buf[s7Ro (fidStepsCap c.scratch_cap) stF.scratch.scratch_buf q +
        j]?.getD 0#32))
    (hstd : S8DelOk c F0 F_next stF std) (hm0 : (FullMem c std ⋆ R) m0)
    (hJq : ∀ (mv : Val i32) (st' : FullState) (mm : Mem 64), S8DelOk c F0 F_next stF st' →
      (FullMem c st' ⋆ R) mm → Jq (mv, qsv - 1, ()) mm) :
    wp Γ Q X (s8DelRowExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp
      best_k sc dm_bv brow_off mn_bv fresh mi0 mv qsv dd1a dd1b Jq) m0 := by
  have hscr_b : c.scratch_cap < 2 ^ 28 := c.hscr
  have hsc4 := fidStepsCap_mul4_le c.scratch_cap
  have hsbd : std.scratch.scratch_buf = stF.scratch.scratch_buf := by rw [hstd.2.2.2.1]
  have hsbF_len : stF.scratch.scratch_buf.length = c.scratch_cap := by
    rw [← hsbd]; exact hstd.1.1.scratch_ok.scratch_buf_len
  unfold s8DelRowExpr s8DelExpr s8Phase2Expr s8Phase1bExpr s8PostDefragExpr s8MidExpr
    s8PreMidExpr s8HdrExpr
  delta FullFidelityStep8.full_bva_commit_body
  dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrpb, sGrp1, sGrp64_32,
    sGrp64_64_32, sGrp32bb, sGrp32_32, sThen, sElse, sDummyTup, sDummyVal, i64, i32]
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
      S8DelOk c F0 F_next stF st' ∧ (FullMem c st' ⋆ R) mm)
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
        (fun stc mc => (FullMem c stc ⋆ R) mc ∧ S8DelOk c F0 F_next stF stc)
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
              S8DelOk c F0 F_next stF stk ∧ stk.core.arena = st'.core.arena ∧
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
              have hgen : ∀ ag' : BitVec 64, S8DelOk c F0 F_next stF { stk with
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

private theorem s8_final_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_next : List (List Nat)} {s stF stm : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv fresh mi0 mv qsv : Val i32}
    {dd1a dd1b : Val .bool} {mm : Mem 64}
    (hfresh_nat : fresh.toNat = 2 * s.core.cur_vars)
    (hfresh1 : (fresh ^^^ 1#32).toNat = 2 * s.core.cur_vars + 1)
    (hcvF : stF.core.cur_vars = s.core.cur_vars + 1) (hfuelF : stF.core.fuel = s.core.fuel)
    (htmF : stF.scratch.tarjan_mark = s.scratch.tarjan_mark)
    (htrF : stF.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hcommF : ∀ st', S8DelOk c F0 F_next stF st' → Step7BvaCommittedOk c st' best_k.toNat)
    (hstm : S8DelOk c F0 F_next stF stm) (hmm : (FullMem c stm ⋆ R) mm)
    (hQ : ∀ ok s' m', FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) →
      (ok = true → Step7BvaCommittedOk c s' best_k.toNat) → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (s8FinalExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp
      best_k sc dm_bv brow_off mn_bv fresh mi0 mv qsv dd1a dd1b) mm := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcomm := hcommF stm hstm
  obtain ⟨hinvm, hcvm, hfuelm, hscm', _, _⟩ := hstm
  have hclm := hinvm.1.core_ok; have hscm := hinvm.1.scratch_ok; have hcv_le := hclm.cur_vars_le
  have htmm : stm.scratch.tarjan_mark = s.scratch.tarjan_mark := by rw [hscm']; exact htmF
  have htrm : stm.scratch.tarjan_reach = s.scratch.tarjan_reach := by rw [hscm']; exact htrF
  have h2cv : (BitVec.ofNat 64 stm.core.cur_vars <<< (1 : Nat)).toNat =
      2 * (s.core.cur_vars + 1) := by
    rw [hcvm, hcvF]; simp only [bv_c0]; omega
  unfold s8FinalExpr s8DelExpr s8Phase2Expr s8Phase1bExpr s8PostDefragExpr s8MidExpr
    s8PreMidExpr s8HdrExpr
  delta FullFidelityStep8.full_bva_commit_body
  dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrpb, sGrp1, sGrp64_32,
    sGrp64_64_32, sGrp32bb, sGrp32_32, sThen, sElse, sDummyTup, sDummyVal, i64, i32]
  refine wp_join_state0 (α := List (BitVec 32))
    (fun wsz mzi => wsz.length = 2 * c.max_vars ∧
      (FullMem c { stm with scratch := { stm.scratch with wsort := wsz } } ⋆ R) mzi)
    (fun _ wsz mzi ⟨hwsz_l, hmzi⟩ => ?_) (fun Jw hJw => ?_)
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
  · c0_hsplit
    · c0_hsteps_nogrp
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
      · c0_hstep; exact hJw wsz mzi ⟨hwsz_l, hmzi⟩
    · c0_hstep; exact hJw stm.scratch.wsort mm ⟨hscm.wsort_len, hmm⟩

private theorem s8_del_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hDelBin : FidDelBinHyp Γ) (hUnwatch : FidUnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_next : List (List Nat)} {stF : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv fresh mi0 : Val i32}
    {dd1a dd1b : Val .bool} {m0 : Mem 64}
    (hsc_eq : sc.toNat = fidStepsCap c.scratch_cap)
    (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hro : ∀ q ≤ best_k.toNat, s7Ro (fidStepsCap c.scratch_cap) stF.scratch.scratch_buf q +
      mn_bv.toNat ≤ c.scratch_cap)
    (hval : ∀ q ≤ best_k.toNat, ∀ j < mn_bv.toNat, Step7RowRefOk stF
      (stF.scratch.scratch_buf[s7Ro (fidStepsCap c.scratch_cap) stF.scratch.scratch_buf q +
        j]?.getD 0#32))
    (hinvF : FullDenseInvW c F0 F_next stF) (hm0 : (FullMem c stF ⋆ R) m0)
    (hfin : ∀ (mv qsv : Val i32) (st' : FullState) (mm : Mem 64), S8DelOk c F0 F_next stF st' →
      (FullMem c st' ⋆ R) mm → wp Γ Q X (s8FinalExpr c.hdr c.pArena c.pScratchBuf c.pWsort
        c.pFlags c.pWvec c.pRepr c.pTmp best_k sc dm_bv brow_off mn_bv fresh mi0 mv qsv
        dd1a dd1b) mm) :
    wp Γ Q X (s8DelExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp
      best_k sc dm_bv brow_off mn_bv fresh mi0 dd1a dd1b) m0 := by
  have hscr_b : c.scratch_cap < 2 ^ 28 := c.hscr
  have hsc4 := fidStepsCap_mul4_le c.scratch_cap
  have hbk1 : (best_k + 1).toNat = best_k.toNat + 1 := by
    rw [BitVec.toNat_add]; simp only [show (1 : BitVec 32).toNat = 1 from rfl]; omega
  have heq : s8DelExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp
      best_k sc dm_bv brow_off mn_bv fresh mi0 dd1a dd1b = s8DelExpr c.hdr c.pArena c.pScratchBuf
      c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp best_k sc dm_bv brow_off mn_bv fresh mi0
      dd1a dd1b := rfl
  conv at heq =>
    rhs
    unfold s8DelExpr s8Phase2Expr s8Phase1bExpr s8PostDefragExpr s8MidExpr s8PreMidExpr
      s8HdrExpr
    delta FullFidelityStep8.full_bva_commit_body
    dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrpb, sGrp1, sGrp64_32,
      sGrp64_64_32, sGrp32bb, sThen, sElse, sDummyTup, sDummyVal, i64, i32]
  rw [heq]
  c0_hstep
  refine wp_loop_inv
    (fun (_, qsv, ()) mm => ∃ st' : FullState, qsv.toNat ≤ best_k.toNat + 1 ∧
      S8DelOk c F0 F_next stF st' ∧ (FullMem c st' ⋆ R) mm)
    (fun (_, qsv, ()) _ => qsv.toNat)
    (fun J hJ => ?_) (fun J (mv, qsv, ()) mm ⟨st', hqs_le, hst', hmm⟩ ih => ?_)
  · c0_hstep
    exact hJ (_, best_k + 1, ()) m0 ⟨stF, by omega,
      ⟨hinvF, rfl, rfl, rfl, rfl, fidBvaArenaMono_refl _⟩, hm0⟩
  · c0_hsplit
    · have hqs_pos : 0 < qsv.toNat := by simpa using hc
      have hq1 : (qsv - 1).toNat = qsv.toNat - 1 := by
        rw [BitVec.toNat_sub_of_le (by simp only [bv_c0]; omega)]; rfl
      have h := s8_del_row_wp (Γ := Γ) (Q := Q) (X := X) hDelBin hUnwatch (dm_bv := dm_bv)
        (brow_off := brow_off) (fresh := fresh) (mi0 := mi0) (mv := mv) (dd1a := dd1a)
        (dd1b := dd1b) (Jq := J) hsc_eq hbk_sc hqs_pos hqs_le hro hval hst' hmm
        (fun mv' st'' mm' hst'' hmm' =>
          ih (mv', qsv - 1, ()) mm' (by dsimp only; omega) ⟨st'', by omega, hst'', hmm'⟩)
      unfold s8DelRowExpr at h; rw [heq] at h; exact h
    · have h := hfin mv qsv st' mm hst' hmm
      unfold s8FinalExpr at h; rw [heq] at h; exact h

theorem s8_phase2_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hDelBin : FidDelBinHyp Γ) (hUnwatch : FidUnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s st0 : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv fresh mi0 : Val i32}
    {dd1a dd1b : Val .bool} {m0 : Mem 64} {bump : Nat}
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
    wp Γ Q X (s8Phase2Expr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr
      c.pTmp best_k sc dm_bv brow_off mn_bv fresh mi0 dd1a dd1b) m0 := by
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
  have heq2 : s8Phase2Expr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp
      best_k sc dm_bv brow_off mn_bv fresh mi0 dd1a dd1b = s8Phase2Expr c.hdr c.pArena
      c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp best_k sc dm_bv brow_off mn_bv fresh
      mi0 dd1a dd1b := rfl
  conv at heq2 =>
    rhs
    unfold s8Phase2Expr s8Phase1bExpr s8PostDefragExpr s8MidExpr s8PreMidExpr s8HdrExpr
    delta FullFidelityStep8.full_bva_commit_body
    dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrpb, sGrp64_32, sGrp64_64_32,
      sGrp32bb, sThen, sElse, sDummyTup, sDummyVal, i64, i32]
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
      have hcommF : ∀ st', S8DelOk c F0 F_next
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
      have hd := s8_del_wp (Γ := Γ) (Q := Q) (X := X) hDelBin hUnwatch
        (stF := { st0 with scratch := { st0.scratch with scratch_buf := sbv } })
        (dm_bv := dm_bv) (brow_off := brow_off) (fresh := fresh) (mi0 := mi0)
        (dd1a := dd1a) (dd1b := dd1b) hsc_eq hbk_sc
        (fun q hq => by
          obtain ⟨_, hro1, _, hrob, _⟩ := hz q hq
          show s7Ro _ sbv q + _ ≤ _
          rw [hro1]; exact hrob)
        (fun q hq j hj => ((hz q hq).2.2.2.2 j hj).congr rfl rfl rfl)
        (fullDenseInvW_set_sb hinv0 hcomp.1) hmv
        (fun _ _ st' mm hst' hmm => s8_final_wp (s := s)
          (stF := { st0 with scratch := { st0.scratch with scratch_buf := sbv } }) hfresh_nat
          hfresh1 hcv0 hfuel0 htm0 htr0 hcommF hst' hmm hQ)
      unfold s8DelExpr at hd
      rw [heq2] at hd
      dsimp only [sGrp1, sStep, sElse, sDummyTup, sDummyVal, i64, i32] at hd
      exact hd


end LeanQbe.T.Examples.Kissat.FullFidelityStep8

end
