/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof2a0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep8
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas5
import LeanQbe.T.Examples.Kissat.FullBridgeLemmas3
import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas1
import LeanQbe.T.Examples.Kissat.FullIngestLemmas2
import LeanQbe.T.Examples.Kissat.FullM4BvaLemmas2
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Logic.C0Agrees

/-!
# Kissat Fidelity Step-8 BVA Large-Clause Helpers (`FullFidelityStep8ProofBva0`)

Parametric `(Γ : Env)` helper module (`0` `import all`, `public section`) for Step-8
`FullFidelityStep8.full_bva_commit_body` (`FullFidelityStep8ProofBva`):
1. `s8BvaLargeWatchExpr` & `s8_bva_large_watch_wp`: Step-8 large-clause watch-push / unwatch
   rollback subtree jumping to `Jtop (dd, ok', ())` (`Cont [.bool, .bool]`).
2. `s8BvaLargeTopExpr` & `s8_bva_large_top_wp`: Step-8 large-clause filter-copy / `full_alloc_cl`
   subtree jumping to `J1b (mi, dd, false, ())` (`Cont [i32, .bool, .bool]`) on alloc failure or
   `Jtop (dd, ok', ())` on exit, over `FullFidelityStep7Proof2a.S7StOk`.
-/

set_option autoImplicit false

local elab "c0_hsteps_np" : tactic => LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local elab "c0_hsteps_nogrp_np" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep8

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullBvaHeap FullBvaHeap.FullBvaHeapHelpers FullBvaHeap.FullBvaHeapTactics
open FullBvaHeap.FullBvaHeapScanHelpers FullM4Bva
open LeanQbe.T.Examples.Kissat.FullFidelityBva
open LeanQbe.T.Examples.Kissat.FullFidelityStep7
open LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof2a
open scoped FullArenaTactics FullBvaHeapTactics

/-! ## 1. Local Shared Helpers (`S7StOk` Transitions) -/

private theorem s8_nodup_lt_length_le : ∀ {n : Nat} {xs : List Nat},
    xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n
  | 0, [], _, _ => Nat.zero_le _
  | 0, x :: _, _, hlt => absurd (hlt x (by simp)) (by omega)
  | n + 1, xs, hnd, hlt => by
    by_cases hn : n ∈ xs
    · have hperm := List.perm_cons_erase hn; have hnd' := List.nodup_cons.mp (hnd.perm hperm)
      have hlt' : ∀ y ∈ xs.erase n, y < n := fun y hy => by
        have hmem := List.mem_of_mem_erase hy
        have hne : y ≠ n := fun he => by subst he; exact hnd'.1 hy
        have := hlt y hmem; omega
      have ih := s8_nodup_lt_length_le hnd'.2 hlt'
      have hlen := hperm.length_eq; simp only [List.length_cons] at hlen; omega
    · have hlt' : ∀ y ∈ xs, y < n := fun y hy => by
        have hne : y ≠ n := fun he => by subst he; exact hn hy
        have := hlt y hy; omega
      exact Nat.le_trans (s8_nodup_lt_length_le hnd hlt') (Nat.le_succ _)

theorem s8_fullDenseInvW_of_append_clause {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s) {sz : Nat}
    (hsz3 : 3 ≤ sz) {ar' wvec' wstk' fl' wsort' : List (BitVec 32)} {wlen' : Nat}
    {wu' ni' : BitVec 64}
    (hlen' : let k' := { s.core with
      arena := ar', arena_len := s.core.arena_len + 3 + sz, wvec := wvec', wstk := wstk',
      wlen := wlen', wusable := wu', flags := fl', num_irred := ni' }
      ({ s with core := k', scratch := { s.scratch with wsort := wsort' } } :
        FullState).LengthsOk c)
    (hhold : ∀ i < s.core.arena_len, ar'[i]? = s.core.arena[i]?)
    (hns : (ar'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hsz_new : (ar'[s.core.arena_len + 2]?.getD 0#32).toNat = sz)
    (hlits_lt : ∀ l ∈ fullArenaClauseLitsCore { s.core with arena := ar' } s.core.arena_len,
      l < 2 * s.core.cur_vars)
    (hlits_nd : ((fullArenaClauseLitsCore { s.core with arena := ar' }
      s.core.arena_len).map (· / 2)).Nodup)
    (hlits_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { s.core with arena := ar' } s.core.arena_len)))
    (hwat' : ModeWatchesInv F_cur { s.core with
      arena := ar', arena_len := s.core.arena_len + 3 + sz, wvec := wvec', wstk := wstk',
      wlen := wlen', wusable := wu', flags := fl', num_irred := ni' }) :
    let s' : FullState := { s with
      core := { s.core with
        arena := ar', arena_len := s.core.arena_len + 3 + sz, wvec := wvec', wstk := wstk',
        wlen := wlen', wusable := wu', flags := fl', num_irred := ni' },
      scratch := { s.scratch with wsort := wsort' } }
    FullDenseInvW c F0 F_cur s' ∧ FidBvaArenaMono s.core s'.core := by
  intro s'; have hw := hinv.2.1; have hcl := hinv.1.core_ok
  have hnxt_hold := hw.arena.arenaNextOff_extend (alen' := s.core.arena_len + 3 + sz)
    (by omega) hhold
  have hrefs :
      fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
    fullArenaClauseRefsCore_append hw.arena hsz3 rfl hhold hns hsz_new
  have hold_garb : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1; unfold fullArenaClauseGarbCore fullArenaHdrCore s'
    simp [hhold r (by omega)]
  have hold_sz : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1; unfold fullArenaClauseSizeCore s'
    simp [hhold (r + 2) (by omega)]
  have hold_lits : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr => by
    have hwf := hw.arena.refs_wf r hr
    exact fullArenaClauseLitsCore_congr (hold_sz r hr) fun j hj => hhold (r + 3 + j) (by omega)
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨Or.inr (by dsimp [s']; omega), ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hwf := hw.arena.refs_wf r hr; rw [hnxt_hold r hr, hold_sz r hr]
        refine ⟨by dsimp [s']; omega, hwf.2.1, hwf.2.2.1, by dsimp [s']; omega, ?_⟩
        rcases hwf.2.2.2.2 with he | h3 <;> right <;> dsimp [s'] <;> omega
      · have hnxt_new : fullArenaNextOff s'.core.arena s'.core.arena_len s.core.arena_len =
            s.core.arena_len + 3 + sz := by unfold fullArenaNextOff s'; simp [hsz_new, hns]
        rw [hnxt_new, show fullArenaClauseSizeCore s'.core s.core.arena_len = sz from hsz_new]
        refine ⟨by dsimp [s']; omega, hsz3, by omega, by dsimp [s']; omega, Or.inl (by dsimp [s'])⟩
    · intro r hr hsh; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hr3 := (hw.arena.refs_wf r hr).1
        have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢; dsimp only [s'] at hsh; rwa [hhold r (by omega)] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
        exact ⟨t, by rw [hold_sz r hr]; exact ht1, by dsimp only [s']; omega,
          by dsimp only [s']; rw [hhold t ht2]; exact hsent⟩
      · unfold fullArenaHdrCore at hsh; dsimp only [s'] at hsh; exact absurd hns hsh
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.lits_lt r hr hng
      · exact hlits_lt
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.entails r hr hng
      · exact hlits_ent
  have hno_rsn : ∀ idx < s.core.trail_end,
      s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun idx hidx => hw.level0_rsn_none idx hidx (by
      have := hw.lvl_le idx hidx; have := hinv.2.2.2.2.2.1; omega)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := harena', watches := hwat',
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne,
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne }
  have hnodup' : FullArenaVarsNodup s' := fun r hr hng => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr
    rw [hrefs, List.mem_append, List.mem_singleton] at hr; rcases hr with hr | rfl
    · change fullArenaClauseGarbCore s'.core r = false at hng; rw [hold_garb r hr] at hng
      change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
      rw [hold_lits r hr]; exact hinv.2.2.2.1 r hr hng
    · exact hlits_nd
  have hext' : FullExtScratchOk c s' := ⟨(fun i hi => by
    rcases hinv.2.2.2.2.1.1 i hi with h1 | h2
    · exact Or.inl h1
    · refine Or.inr ?_
      change _ ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact List.mem_append_left _ h2),
    hinv.2.2.2.2.1.2⟩
  exact ⟨⟨hlen', hw', hinv.2.2.1, hnodup', hext', hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩,
    fun r hr => ⟨by rw [hrefs]; exact List.mem_append_left _ hr, hold_sz r hr, hold_lits r hr⟩⟩

theorem s8_fullDenseInvW_with_num_irred {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    (ni' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with num_irred := ni' } } :=
  ⟨⟨{ hinv.1.core_ok with vals_len := hinv.1.core_ok.vals_len }, hinv.1.scratch_ok⟩,
   { hinv.2.1 with
     arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
     watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

theorem s8_fullDenseInvW_set_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {tmp' : List (BitVec 32)} (htmp : tmp'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with tmp := tmp' } } :=
  fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len) (sc' := s.scratch)
    hinv hinv.1.core_ok.repr_len hinv.1.core_ok.min_clr_len_arr htmp hinv.1.core_ok.flags_len
    hinv.1.core_ok.tmp_len_le hinv.1.scratch_ok rfl rfl

theorem s8_fullArenaLitsCore_eq_map {k : FullCoreState} {r sz : Nat}
    (hsz : fullArenaClauseSizeCore k r = sz) (hb : r + 3 + sz ≤ k.arena.length) :
    fullArenaClauseLitsCore k r =
      (List.range sz).map (fun j => (k.arena[r + 3 + j]?.getD 0#32).toNat) := by
  apply List.ext_getElem?; intro j; by_cases hj : j < sz
  · rw [FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (by omega) (by omega),
      List.getElem?_map, List.getElem?_range hj, Option.map_some,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  · rw [List.getElem?_eq_none (by
        rw [FullBvaFwdHelpers.fullArenaClauseLitsCore_length (by omega), hsz]; omega),
      List.getElem?_eq_none (by simp; omega)]

theorem s8_bv32_lit_mask_eq {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    (x &&& 0x7FFFFFFF#32) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

private theorem s8_wp_jump_eq {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    {L : Cont ts} {args : Tup (Arg Val) ts} {m : Mem 64} :
    wp Γ Q X (.jump L args) m = L (vals args) m := rfl

private theorem s8_is_wp_goal {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {e : Expr Val Cont rs} {m : Mem 64} (h : wp Γ Q X e m) : wp Γ Q X e m := h

local macro "s8_hsteps_to_jump" : tactic =>
  `(tactic| repeat (
    apply s8_is_wp_goal
    first | (rw [s8_wp_jump_eq]; dsimp only [vals, Arg.val]) | c0_hstep))

/-! ## 2. Step-8 Large-Clause Watch-Push & Top Subtree Expressions -/

@[expose] def s8BZext (a : Arg Val i32) (k : Val i64 → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (a, ()) } fun p => k p.fst
@[expose] def s8BOp64 (op : OpCode [i64, i64] [i64]) (a b : Arg Val i64)
    (k : Val i64 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.let_ { sig := [i64, i64], code := op, args := (a, b, ()) } fun p => k p.fst
@[expose] def s8BOp32 (op : OpCode [i32, i32] [i32]) (a b : Arg Val i32)
    (k : Val i32 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.let_ { sig := [i32, i32], code := op, args := (a, b, ()) } fun p => k p.fst
@[expose] def s8BCmp32 (op : CmpOp) (a b : Arg Val i32)
    (k : Val .bool → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.let_ { sig := [i32, i32], code := OpCode.cmp op i32, args := (a, b, ()) } fun p => k p.fst
@[expose] def s8BPtr32 (base idx : Val i64) (k : Val i64 → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  s8BOp64 (.mul i64) (Arg.var idx) (Arg.imm 4) fun off =>
    s8BOp64 (.add i64) (Arg.var base) (Arg.var off) k
@[expose] def s8BLd32 (base idx : Val i64) (k : Val i32 → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] := s8BPtr32 base idx fun ptr => Expr.load i32 (Arg.var ptr) k

@[expose] def s8BvaLargeWatchExpr (h pAr pFl pTmp : Val i64) (tk : Val i32) (ncr : Val i64)
    (dd : Val .bool) (Jtop : Cont [.bool, .bool]) : Expr Val Cont [.bool] :=
  Expr.group (fun _ => Blocks.cons (fun (p : Tup Val [.bool, i32]) =>
    Expr.group (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
      Expr.jump Jtop (Arg.var dd, Arg.var p.fst, ())) Blocks.nil) fun Jni =>
    Expr.jnz (Arg.var p.fst)
      (s8BOp64 (.add i64) (Arg.var h) (Arg.imm 488) fun p1 => Expr.load i64 (Arg.var p1)
        fun ld => s8BOp64 (.add i64) (Arg.var ld) (Arg.imm 1) fun p2 =>
        s8BOp64 (.add i64) (Arg.var h) (Arg.imm 488) fun p3 =>
        Expr.store (Arg.var p2) (Arg.var p3) (Expr.jump Jni.fst ()))
      (Expr.jump Jni.fst ())) Blocks.nil) fun Jw_exit =>
  Expr.group (fun Jw => Blocks.cons (fun (pj : Tup Val [i32]) =>
    s8BCmp32 .ult (Arg.var pj.fst) (Arg.var tk) fun c => Expr.jnz (Arg.var c)
      (s8BZext (Arg.var pj.fst) fun j64 => s8BLd32 pTmp j64 fun lj =>
       s8BOp32 (.and i32) (Arg.var tk) (Arg.imm 2147483647) fun tkm =>
       Expr.let_ { sig := [i64], code := OpCode.trunc 64 32, args := (Arg.var ncr, ()) } fun n32 =>
       Expr.call "full_watch_push" (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
         (Arg.var h, Arg.var lj, Arg.var tkm, Arg.var n32.fst, Arg.imm 2, ()) fun okw =>
       Expr.jnz (Arg.var okw.fst)
         (s8BZext (Arg.var pj.fst) fun j64b => s8BLd32 pTmp j64b fun ljb =>
          s8BOp32 (.lshr i32) (Arg.var ljb) (Arg.imm 1) fun tv =>
          s8BZext (Arg.var tv) fun tv64 => s8BPtr32 pFl tv64 fun pfv =>
          s8BZext (Arg.var tv) fun tv64b => s8BLd32 pFl tv64b fun flv =>
          Expr.group (fun _ => Blocks.cons (fun (pf : Tup Val [i32]) =>
            s8BOp32 (.or i32) (Arg.var flv) (Arg.var pf.fst) fun nfl =>
            Expr.store (Arg.var nfl) (Arg.var pfv) (s8BOp32 (.add i32) (Arg.var pj.fst)
              (Arg.imm 1) fun j1 => Expr.jump Jw.fst (Arg.var j1, ()))) Blocks.nil) fun Jt =>
          s8BZext (Arg.var pj.fst) fun j64c => s8BLd32 pTmp j64c fun ljc =>
          s8BOp32 (.and i32) (Arg.var ljc) (Arg.imm 1) fun b1 =>
          s8BCmp32 .ne (Arg.var b1) (Arg.imm 0) fun c1 =>
          Expr.jnz (Arg.var c1) (Expr.jump Jt.fst (Arg.imm 64, ()))
            (Expr.jump Jt.fst (Arg.imm 32, ())))
         (Expr.group (fun Juk => Blocks.cons (fun (pu : Tup Val [i32]) =>
            s8BCmp32 .ult (Arg.var pu.fst) (Arg.var pj.fst) fun cu => Expr.jnz (Arg.var cu)
              (s8BZext (Arg.var pu.fst) fun u64 => s8BLd32 pTmp u64 fun lu =>
               Expr.let_ { sig := [i64], code := OpCode.trunc 64 32, args := (Arg.var ncr, ()) }
                 fun n32u => Expr.call "full_unwatch_large" (as := [i64, i32, i32]) (bs := [])
                 (Arg.var h, Arg.var lu, Arg.var n32u.fst, ()) fun _ =>
               s8BOp32 (.add i32) (Arg.var pu.fst) (Arg.imm 1) fun u1 =>
               Expr.jump Juk.fst (Arg.var u1, ()))
              (s8BPtr32 pAr ncr fun par1 => s8BLd32 pAr ncr fun hdrv => s8BOp32 (.or i32)
                 (Arg.var hdrv) (Arg.imm 524288) fun nhdr => Expr.store (Arg.var nhdr)
                 (Arg.var par1) (s8BOp64 (.add i64) (Arg.var h) (Arg.imm 472) fun pg1 =>
                  Expr.load i64 (Arg.var pg1) fun ag => s8BOp64 (.add i64) (Arg.var ag)
                    (Arg.imm 3) fun ag3 => s8BZext (Arg.var tk) fun tk64 =>
                    s8BOp64 (.add i64) (Arg.var ag3) (Arg.var tk64) fun agn =>
                    s8BOp64 (.add i64) (Arg.var h) (Arg.imm 472) fun pg2 =>
                  Expr.store (Arg.var agn) (Arg.var pg2)
                    (Expr.jump Jw_exit.fst (Arg.imm false, Arg.var pj.fst, ()))))) Blocks.nil)
          fun Juk => Expr.jump Juk.fst (Arg.imm 0, ())))
      (Expr.jump Jw_exit.fst (Arg.var true, Arg.var pj.fst, ()))) Blocks.nil)
  fun Jw => Expr.jump Jw.fst (Arg.imm 0, ())

@[expose] def s8BvaLargeTopExpr (h pAr pFl pTmp : Val i64)
    (mi c_top csz flit fresh : Val i32) (dd : Val .bool)
    (J1b : Cont [i32, .bool, .bool]) (Jtop : Cont [.bool, .bool]) : Expr Val Cont [.bool] :=
  Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 0, ()) } fun z64 =>
  s8BPtr32 pTmp z64.fst fun ptmp0 => s8BOp32 (.xor i32) (Arg.var fresh) (Arg.imm 1) fun f1 =>
  Expr.store (Arg.var f1) (Arg.var ptmp0)
    (Expr.group (fun Jf => Blocks.cons (fun (pf : Tup Val [i32, i32]) =>
      s8BCmp32 .ult (Arg.var pf.snd.fst) (Arg.var csz) fun c => Expr.jnz (Arg.var c)
        (s8BZext (Arg.var c_top) fun ct64b => s8BOp64 (.add i64) (Arg.var ct64b) (Arg.imm 3)
           fun ct3 => s8BZext (Arg.var pf.snd.fst) fun j64 => s8BOp64 (.add i64) (Arg.var ct3)
           (Arg.var j64) fun idx => s8BLd32 pAr idx fun l => Expr.group (fun _ => Blocks.cons
           (fun (ptk : Tup Val [i32]) => s8BOp32 (.add i32) (Arg.var pf.snd.fst) (Arg.imm 1)
             fun j1 => Expr.jump Jf.fst (Arg.var ptk.fst, Arg.var j1, ())) Blocks.nil) fun Jif =>
         s8BCmp32 .ne (Arg.var l) (Arg.var flit) fun cne => Expr.jnz (Arg.var cne)
           (s8BZext (Arg.var pf.fst) fun tk64 => s8BPtr32 pTmp tk64 fun ptmpt => Expr.store
              (Arg.var l) (Arg.var ptmpt) (s8BOp32 (.add i32) (Arg.var pf.fst) (Arg.imm 1)
                fun tk1 => Expr.jump Jif.fst (Arg.var tk1, ())))
           (Expr.jump Jif.fst (Arg.var pf.fst, ())))
        (Expr.call "full_alloc_cl" (as := [i64, i32, i32, .bool]) (bs := [i64])
           (Arg.var h, Arg.var pf.fst, Arg.imm 0, Arg.imm false, ()) fun pncr =>
         Expr.let_ { sig := [i64, i64], code := OpCode.cmp .eq i64,
                     args := (Arg.var pncr.fst, Arg.imm 4294967295, ()) } fun ceq =>
         Expr.jnz (Arg.var ceq.fst) (Expr.jump J1b (Arg.var mi, Arg.var dd, Arg.imm false, ()))
           (Expr.group (fun Jcp => Blocks.cons (fun (pjc : Tup Val [i32]) =>
             s8BCmp32 .ult (Arg.var pjc.fst) (Arg.var pf.fst) fun cjc => Expr.jnz (Arg.var cjc)
               (s8BOp64 (.add i64) (Arg.var pncr.fst) (Arg.imm 3) fun n3 =>
                s8BZext (Arg.var pjc.fst) fun jc64 => s8BOp64 (.add i64) (Arg.var n3)
                  (Arg.var jc64) fun n3j => s8BPtr32 pAr n3j fun parj =>
                s8BZext (Arg.var pjc.fst) fun jc64b => s8BLd32 pTmp jc64b fun tv =>
                Expr.store (Arg.var tv) (Arg.var parj) (s8BOp32 (.add i32) (Arg.var pjc.fst)
                  (Arg.imm 1) fun jc1 => Expr.jump Jcp.fst (Arg.var jc1, ())))
               (s8BvaLargeWatchExpr h pAr pFl pTmp pf.fst pncr.fst dd Jtop)) Blocks.nil)
            fun Jcp => Expr.jump Jcp.fst (Arg.imm 0, ())))) Blocks.nil)
     fun Jf => Expr.jump Jf.fst (Arg.imm 1, Arg.imm 0, ()))

/-! ## 3. Large-Clause Copy / Watch-Push / Rollback over `S7StOk` -/

theorem s8_bva_large_watch_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hWPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hUnwatch : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_next : List (List Nat)} {s stm : FullState}
    {R : Mem 64 → Prop} {tk : Val i32} {dd : Val .bool} {Jtop : Cont [.bool, .bool]}
    {tmpj arj : List (BitVec 32)} {mjc : Mem 64} (hstm : S7StOk c F0 F_next s stm)
    (htmpj_l : tmpj.length = c.max_vars)
    (htk_ge3 : 3 ≤ tk.toNat) (htk_le_mv : tk.toNat ≤ c.max_vars)
    (hncr_cap : stm.core.arena_len + 3 + tk.toNat ≤ c.arena_cap)
    (hhold_j : ∀ i < stm.core.arena_len, arj[i]? = stm.core.arena[i]?)
    (hns_cp : (arj[stm.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hsz_cp : (arj[stm.core.arena_len + 2]?.getD 0#32).toNat = tk.toNat)
    (hnew_lt : ∀ l ∈ fullArenaClauseLitsCore { stm.core with arena := arj } stm.core.arena_len,
      l < 2 * stm.core.cur_vars)
    (hnew_nd : ((fullArenaClauseLitsCore { stm.core with arena := arj }
      stm.core.arena_len).map (· / 2)).Nodup)
    (hnew_ent : (cnfOfClauses F_next).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { stm.core with arena := arj } stm.core.arena_len)))
    (htmp_lt : ∀ t (ht : t < tk.toNat),
      (tmpj[t]'(by rw [htmpj_l]; omega)).toNat < 2 * (s.core.cur_vars + 1))
    (hlen_cp : ({ stm with core := { stm.core with
        tmp := tmpj, arena := arj, arena_len := stm.core.arena_len + 3 + tk.toNat } } :
      FullState).LengthsOk c)
    (hrefs_cp : fullArenaClauseRefsCore
        { stm.core with
          tmp := tmpj, arena := arj, arena_len := stm.core.arena_len + 3 + tk.toNat } =
      fullArenaClauseRefsCore stm.core ++ [stm.core.arena_len])
    (hwat_cp : ModeWatchesInv F_next
      { stm.core with tmp := tmpj, arena := arj, arena_len := stm.core.arena_len + 3 + tk.toNat })
    (hmjc : (FullMem c { stm with core := { stm.core with
      tmp := tmpj, arena := arj, arena_len := stm.core.arena_len + 3 + tk.toNat } } ⋆ R) mjc)
    (hDone : ∀ (ok' : Bool) st1 m1, (FullMem c st1 ⋆ R) m1 →
      S7StOk c F0 F_next s st1 → Jtop (dd, ok', ()) m1) :
    wp Γ Q X (s8BvaLargeWatchExpr c.hdr c.pArena c.pFlags c.pTmp tk
      (BitVec.ofNat 64 stm.core.arena_len) dd Jtop) mjc := by
  obtain ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩ := hstm
  have hmx := c.hmaxv; have har_b := c.harena; unfold dimacsBound at hmx har_b
  have hclm := hinvm.1.core_ok; let old_cv := s.core.cur_vars; let ncr0 := stm.core.arena_len
  let st_tmp : FullState := { stm with core := { stm.core with tmp := tmpj } }
  have hinv_tmp : FullDenseInvW c F0 F_next st_tmp := s8_fullDenseInvW_set_tmp hinvm htmpj_l
  let st_cp : FullState :=
    { st_tmp with core := { st_tmp.core with arena := arj, arena_len := ncr0 + 3 + tk.toNat } }
  have hncr_nat : (BitVec.ofNat 64 ncr0).toNat = ncr0 := by have := hclm.arena_len_le; c0_bound
  have hcv_le := hclm.cur_vars_le
  have htk_lt31 : tk.toNat < 2 ^ 31 := by omega
  dsimp only [s8BvaLargeWatchExpr, s8BZext, s8BOp64, s8BOp32, s8BCmp32, s8BPtr32, s8BLd32]
  refine wp_join_group (ts := [.bool, i32])
    (fun (ok', _, ()) mw => ∃ stw : FullState,
      (FullMem c stw ⋆ R) mw ∧ S7StOk c F0 F_next s stw)
    (fun _ (ok', _, ()) mw ⟨stw, hmw, hstw⟩ => by
      refine wp_join_state0 (α := FullState)
        (fun stf mf => (FullMem c stf ⋆ R) mf ∧ S7StOk c F0 F_next s stf)
        (fun _ stf mf ⟨hmf, hstf⟩ => by s8_hsteps_to_jump; exact hDone ok' stf mf hmf hstf)
        (fun Jni hJni => by
          obtain ⟨hinvw, hcvw, hfuelw, hsbw, htmw, htrw, hmonow, hresw⟩ := hstw; c0_hsplit
          · s8_hsteps_to_jump
            exact hJni _ m ⟨hm, s8_fullDenseInvW_with_num_irred hinvw _, hcvw, hfuelw,
              hsbw, htmw, htrw, hmonow, hresw⟩
          · s8_hsteps_to_jump
            exact hJni _ mw ⟨hmw, hinvw, hcvw, hfuelw, hsbw, htmw, htrw, hmonow, hresw⟩))
    (fun Jw_exit hJw_exit => ?_)
  refine wp_loop_inv
    (fun (jw, ()) mjw => ∃ wvecw wstkw flw wsortw wlenw wuw, jw.toNat ≤ tk.toNat ∧
      let sw : FullState :=
        { st_cp with core := { st_cp.core with wvec := wvecw, wstk := wstkw, wlen := wlenw,
                                               wusable := wuw, flags := flw }
                     scratch := { st_cp.scratch with wsort := wsortw } }
      sw.LengthsOk c ∧ ModeWatchesInv F_next sw.core ∧ (FullMem c sw ⋆ R) mjw)
    (fun (jw, _) _ => tk.toNat - jw.toNat) (fun Jw hJw => by
      s8_hsteps_to_jump; exact hJw (0#32, ()) mjc
        ⟨st_cp.core.wvec, st_cp.core.wstk, st_cp.core.flags,
         st_cp.scratch.wsort, st_cp.core.wlen, st_cp.core.wusable, Nat.zero_le _,
         hlen_cp, hwat_cp, hmjc⟩)
    (fun Jw (jw, ()) mjw ⟨wvecw, wstkw, flw, wsortw, wlenw, wuw, hjw_le, hlenw,
        hwatw, hmjw⟩ ihw => ?_)
  let sw : FullState :=
    { st_cp with core := { st_cp.core with wvec := wvecw, wstk := wstkw, wlen := wlenw,
                                           wusable := wuw, flags := flw }
                 scratch := { st_cp.scratch with wsort := wsortw } }
  c0_hsplit
  · have hjw_lt : jw.toNat < tk.toNat := by c0_bound
    have hjw1 : (jw + 1#32).toNat = jw.toNat + 1 := by c0_bound
    have hjw_tmp : jw.toNat < tmpj.length := by omega
    have hjw_tmp_sw : (BitVec.setWidth 64 jw).toNat < sw.core.tmp.length := by
      rw [bv64_setWidth_32]; exact hjw_tmp
    have htk_mask : (tk &&& (2147483647 : BitVec 32)) = tk := s8_bv32_lit_mask_eq htk_lt31
    have htk_ne : (tk &&& (2147483647 : BitVec 32)) ≠ 0xFFFFFFFF#32 := by
      rw [htk_mask]; intro h; have := congrArg BitVec.toNat h
      have : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
    have hncr32_nat : (BitVec.setWidth 32 (BitVec.ofNat 64 ncr0)).toNat = ncr0 := by
      have := hclm.arena_len_le; c0_bound
    have hncr32_ne : BitVec.setWidth 32 (BitVec.ofNat 64 ncr0) ≠ 0xFFFFFFFF#32 := by
      intro h; have := congrArg BitVec.toNat h; rw [hncr32_nat] at this
      have := hclm.arena_len_le; have : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
    c0_hsteps; c0_call hWPush
    refine ⟨c, sw, R, rfl, hlenw, hwatw.layout, (fun h => absurd h (by decide)),
      (fun _ => ⟨htk_ne, hncr32_ne⟩), hmjw,
      fun okw wvec' wstk' wlen' wu' wsort' mw' hlenw' hlayw' hothw hokt hokf hmw' => ?_⟩
    have hwatw' : ModeWatchesInv F_next
        { sw.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } := by
      refine fullWatchPush_preserves_modeWatchesInv (cnt := 2#32) hwatw hlayw'
        rfl rfl (fun _ hr => hr) (fun h => absurd h (by decide)) ?_ hothw hokt
        (fun hf => (hokf hf).1)
      intro _; have htk_nb : (tk &&& 0x80000000#32) = 0#32 :=
        bv32_bin_flag_zero_of_lt htk_lt31
      refine ⟨by rw [htk_mask]; exact htk_nb, fun _ => by rw [htk_mask]; omega,
        by rw [hncr32_nat]; have := hclm.arena_len_le; omega, ?_⟩
      change (BitVec.setWidth 32 (BitVec.ofNat 64 ncr0)).toNat ∈ fullArenaClauseRefsCore st_cp.core
      rw [hncr32_nat, hrefs_cp]; exact List.mem_append_right _ (by dsimp only [ncr0]; simp)
    have htv_shr : (BitVec.setWidth 64 ((tmpj[(BitVec.setWidth 64 jw).toNat]'(by
        rw [bv64_setWidth_32]; exact hjw_tmp)) >>> (1 : BitVec 32))).toNat < flw.length := by
      rw [bv64_setWidth_32, bv32_lshr1_bv, hlenw'.core_ok.flags_len]
      simp only [bv64_setWidth_32]; have := htmp_lt jw.toNat hjw_lt; omega
    have htv_shr_n : (BitVec.setWidth 64 ((tmpj[(BitVec.setWidth 64 jw).toNat]'(by
        rw [bv64_setWidth_32]; exact hjw_tmp)) >>> (1 : Nat))).toNat < flw.length := by
      rw [bv64_setWidth_32, bv32_lshr1_nat, hlenw'.core_ok.flags_len]
      simp only [bv64_setWidth_32]; have := htmp_lt jw.toNat hjw_lt; omega
    c0_hsteps_nogrp
    · c0_hsteps_nogrp
      refine wp_join_group (ts := [i32]) (fun (_ : Tup Val [i32]) mf => mf = mw')
        (fun _ _ mf hmf => by
          subst mf; s8_hsteps_to_jump
          refine ihw (jw + 1#32, ()) m (by dsimp only; rw [hjw1]; omega)
            ⟨wvec', wstk', _, wsort', wlen', wu', by rw [hjw1]; omega, ?_, ?_, hm⟩
          · exact ⟨{ hlenw'.core_ok with flags_len := by simp [hlenw'.core_ok.flags_len] },
              hlenw'.scratch_ok⟩
          · exact hwatw'.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr))
        (fun Jt hJt => by
          c0_hsplit
          · s8_hsteps_to_jump; exact hJt (64#32, ()) mw' rfl
          · s8_hsteps_to_jump; exact hJt (32#32, ()) mw' rfl)
    · let sw_fail : FullState :=
        { sw with core := { sw.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                         wusable := wu' }
                  scratch := { sw.scratch with wsort := wsort' } }
      refine wp_loop_inv
        (fun (uk, ()) muk => ∃ wvecu wstku wuu, uk.toNat ≤ jw.toNat ∧ let su : FullState :=
            { sw_fail with core := { sw_fail.core with wvec := wvecu, wstk := wstku,
                                                       wusable := wuu } }
          su.LengthsOk c ∧ ModeWatchesInv F_next su.core ∧ (FullMem c su ⋆ R) muk)
        (fun (uk, _) _ => jw.toNat - uk.toNat) (fun Juk hJuk => by
          s8_hsteps_to_jump
          exact hJuk (0#32, ()) mw' ⟨wvec', wstk', wu', Nat.zero_le _, hlenw', hwatw', hmw'⟩)
        (fun Juk (uk, ()) muk ⟨wvecu, wstku, wuu, huk_le, hlenu, hwatu, hmuk⟩ ihuk => ?_)
      let su : FullState :=
        { sw_fail with core := { sw_fail.core with wvec := wvecu, wstk := wstku, wusable := wuu } }
      c0_hsplit
      · have huk_lt : uk.toNat < jw.toNat := by c0_bound
        have huk1 : (uk + 1#32).toNat = uk.toNat + 1 := by c0_bound
        have huk_tmp : (BitVec.setWidth 64 uk).toNat < su.core.tmp.length := by
          rw [bv64_setWidth_32, hlenu.core_ok.tmp_len_arr]; omega
        c0_hsteps; c0_call hUnwatch; refine ⟨c, su, R, rfl, hlenu, hwatu.layout, hmuk,
          fun wvecu' wstku' wuu' mu' hlenu' _ hwatu' hmu' => ?_⟩
        s8_hsteps_to_jump; exact ihuk (uk + 1#32, ()) mu' (by dsimp only; rw [huk1]; omega)
          ⟨wvecu', wstku', wuu', by rw [huk1]; omega, hlenu', hwatu' F_next hwatu, hmu'⟩
      · have hncr_ar_u : (BitVec.ofNat 64 ncr0).toNat < su.core.arena.length := by
          rw [hncr_nat, hlenu.core_ok.arena_len_arr]; omega
        s8_hsteps_to_jump; have ⟨hinv_app, hmono_app⟩ := s8_fullDenseInvW_of_append_clause hinv_tmp
          htk_ge3 hlenu hhold_j hns_cp hsz_cp hnew_lt hnew_nd hnew_ent hwatu
        have hncr_ref : ncr0 ∈ fullArenaClauseRefsCore su.core := by
          change ncr0 ∈ fullArenaClauseRefsCore st_cp.core
          rw [hrefs_cp]; exact List.mem_append_right _ (by dsimp only [ncr0]; simp)
        have ⟨hinv_mg, hmono_mg⟩ := fullDenseInvW_of_markGarb hinv_app hncr_ref
          (su.core.arena_garbage + 3#64 + BitVec.setWidth 64 tk)
        have hm_mg : (FullMem c { su with core := { su.core with
            arena := su.core.arena.set ncr0 (fullArenaHdrCore su.core ncr0 ||| 0x00080000#32)
            arena_garbage := su.core.arena_garbage + 3#64 + BitVec.setWidth 64 tk } } ⋆ R) m := by
          have hhdr : fullArenaHdrCore su.core ncr0 =
              su.core.arena[ncr0]'(by rw [hlenu.core_ok.arena_len_arr]; omega) := by
            unfold fullArenaHdrCore
            rw [List.getElem?_eq_getElem (by rw [hlenu.core_ok.arena_len_arr]; omega),
              Option.getD_some]
          rw [hhdr]; dsimp only [ncr0] at hncr_nat ⊢
          simp only [hncr_nat, show (524288 : BitVec 32) = 0x00080000#32 from rfl,
            show (3 : BitVec 64) = 3#64 from rfl] at hm ⊢
          exact hm
        exact hJw_exit (false, jw, ()) m ⟨_, hm_mg, hinv_mg, hcvm, hfuelm, hsbm, htmm, htrm,
          fidBvaArenaMono_trans hmono (fidBvaArenaMono_trans hmono_app hmono_mg), hresm⟩
  · s8_hsteps_to_jump
    have ⟨hinv_app, hmono_app⟩ := s8_fullDenseInvW_of_append_clause hinv_tmp
      htk_ge3 hlenw hhold_j hns_cp hsz_cp hnew_lt hnew_nd hnew_ent hwatw
    exact hJw_exit (true, jw, ()) mjw ⟨sw, hmjw, hinv_app, hcvm, hfuelm, hsbm, htmm, htrm,
      fidBvaArenaMono_trans hmono hmono_app, hresm⟩

theorem s8_bva_large_top_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hAllocCl : ∀ a m Q X, Full.fullAllocClSpec a m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X)
    (hWPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hUnwatch : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s stm : FullState}
    {R : Mem 64 → Prop} {best_k mi c_top csz flit fresh : Val i32} {dd : Val .bool}
    {J1b : Cont [i32, .bool, .bool]} {Jtop : Cont [.bool, .bool]} {mm : Mem 64}
    {resm : List Nat}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hcsz_eq : csz.toNat = fullArenaClauseSizeCore s.core c_top.toNat)
    (hflit_eq : flit = s.scratch.scratch_buf[best_k.toNat]?.getD 0#32)
    (hfresh1 : (fresh ^^^ 1#32).toNat = 2 * s.core.cur_vars + 1)
    (hresm_lt : ∀ x ∈ resm, x < 2 * s.core.cur_vars) (hresm_nd : (resm.map (· / 2)).Nodup)
    (hresm_ent : (cnfOfClauses F_next).EntailsClause (cnfClause ((2 * s.core.cur_vars + 1) ::
      resm)))
    (hct_ref0 : c_top.toNat ∈ fullArenaClauseRefsCore s.core)
    (hct_ng0 : fullArenaClauseGarbCore s.core c_top.toNat = false)
    (hct_sz3 : 3 ≤ fullArenaClauseSizeCore s.core c_top.toNat)
    (hfbk_mem : (s.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat ∈
      fullArenaClauseLitsCore s.core c_top.toNat)
    (hres_perm_f : resm.Perm ((fullArenaClauseLitsCore s.core c_top.toNat).filter
      (· != (s.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat)))
    (hmm : (FullMem c stm ⋆ R) mm) (hstm : S7StOk c F0 F_next s stm)
    (hAbort : ∀ st1 m1, (FullMem c st1 ⋆ R) m1 → S7StOk c F0 F_next s st1 →
      J1b (mi, dd, false, ()) m1)
    (hDone : ∀ (ok' : Bool) st1 m1, (FullMem c st1 ⋆ R) m1 →
      S7StOk c F0 F_next s st1 → Jtop (dd, ok', ()) m1) :
    wp Γ Q X (s8BvaLargeTopExpr c.hdr c.pArena c.pFlags c.pTmp
      mi c_top csz flit fresh dd J1b Jtop) mm := by
  obtain ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩ := hstm
  have hmx := c.hmaxv; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx har_b hscr_b; have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hclm := hinvm.1.core_ok; have hscm := hinvm.1.scratch_ok; have hcv_le :=
    hclm.cur_vars_le; have hsb_len := hsc.scratch_buf_len; let old_cv := s.core.cur_vars
  obtain ⟨hct_refm, hct_szm, hct_litsm⟩ := hmono c_top.toNat hct_ref0
  have hct_wfm := hinvm.2.1.arena.refs_wf c_top.toNat hct_refm
  have hcsz_s : csz.toNat = fullArenaClauseSizeCore s.core c_top.toNat := hcsz_eq
  let C_lits := fullArenaClauseLitsCore s.core c_top.toNat
  have hC_len : C_lits.length = csz.toNat := by
    rw [hcsz_s]; exact FullBvaFwdHelpers.fullArenaClauseLitsCore_length (by
      have := (hinv.2.1.arena.refs_wf c_top.toNat hct_ref0).2.2.1
      have := (hinv.2.1.arena.refs_wf c_top.toNat hct_ref0).2.2.2.1
      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega)
  have hC_nd_vars : (C_lits.map (· / 2)).Nodup := hinv.2.2.2.1 c_top.toNat hct_ref0 hct_ng0
  have hC_nd : C_lits.Nodup := nodup_of_map_div2 hC_nd_vars
  have hC_len_le_cv : csz.toNat ≤ old_cv := by
    rw [← hC_len, ← List.length_map (· / 2)]
    exact s8_nodup_lt_length_le hC_nd_vars fun v hv => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
      have := hinv.2.1.arena.lits_lt c_top.toNat hct_ref0 hct_ng0 l hl; omega
  have hfbk_mem' : flit.toNat ∈ C_lits := by rwa [hflit_eq]
  have hfilt_len : (C_lits.filter (· != flit.toNat)).length + 1 = csz.toNat := by
    rw [← hC_len]; exact filter_ne_nodup_length hC_nd hfbk_mem'
  have htmp0_lt : 0 < stm.core.tmp.length := by rw [hclm.tmp_len_arr]; omega
  dsimp only [s8BvaLargeTopExpr, s8BZext, s8BOp64, s8BOp32, s8BCmp32, s8BPtr32, s8BLd32]
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (tk, j, ()) mj => ∃ tmpj : List (BitVec 32),
      j.toNat ≤ csz.toNat ∧ tmpj.length = c.max_vars ∧
      tk.toNat = 1 + ((C_lits.take j.toNat).filter (· != flit.toNat)).length ∧
      tmpj[0]? = some (fresh ^^^ 1#32) ∧ (∀ t, 1 ≤ t → t < tk.toNat →
        (tmpj[t]?.getD 0#32).toNat = ((C_lits.take j.toNat).filter (· != flit.toNat))[t - 1]?.getD
          0) ∧
      (FullMem c { stm with core := { stm.core with tmp := tmpj } } ⋆ R) mj)
    (fun (_, j, _) _ => csz.toNat - j.toNat) (fun Jf hJf => by
      dsimp only [wp, vals, Arg.val]
      exact hJf (1#32, 0#32, ()) m ⟨_, Nat.zero_le _, by simp [hclm.tmp_len_arr], rfl,
        by rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat = 0 from rfl,
          List.getElem?_set_self (by rw [hclm.tmp_len_arr]; omega)]; rfl,
        fun _ h1 h2 => by simp only [bv_c0] at h2; omega, hm⟩)
    (fun Jf (tk, j, ()) mj ⟨tmpj, hj_le, htmpj_l, htk_eq, htmp0, htmp_rest, hmj⟩ ihf => ?_)
  c0_hsteps
  · have hj_lt : j.toNat < csz.toNat := by assumption
    have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
    have hctj_n : (BitVec.setWidth 64 c_top + 3 + BitVec.setWidth 64 j).toNat =
        c_top.toNat + 3 + j.toNat := by
      change (BitVec.setWidth 64 c_top + 3#64 + BitVec.setWidth 64 j).toNat = _; c0_bound
    have hctj_ar : c_top.toNat + 3 + j.toNat < stm.core.arena.length := by
      have := hclm.arena_len_le; have := hclm.arena_len_arr; omega
    have hCj_eq : C_lits[j.toNat]'(by rw [hC_len]; exact hj_lt) =
        (stm.core.arena[c_top.toNat + 3 + j.toNat]'hctj_ar).toNat := by
      have h1 := FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (k := stm.core)
        (r := c_top.toNat) (j := j.toNat) (by rw [hct_szm]; omega) hctj_ar
      rw [hct_litsm, List.getElem?_eq_getElem (by rw [hC_len]; exact hj_lt)] at h1
      exact Option.some.inj h1
    have htake_succ := FullBvaFwdHelpers.take_succ_filter_eq (l := C_lits)
      (i := j.toNat) (x := flit.toNat) (by rw [hC_len]; exact hj_lt)
    have hsub_len : ((C_lits.take (j.toNat + 1)).filter (· != flit.toNat)).length ≤
        (C_lits.filter (· != flit.toNat)).length :=
      List.Sublist.length_le (List.Sublist.filter _ (List.take_sublist _ _))
    have hctj_mod : (c_top.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64 =
        c_top.toNat + 3 + j.toNat := by
      rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
    c0_hsteps_nogrp; refine wp_join_group (ts := [i32])
      (fun (tk', ()) m' => ∃ tmp' : List (BitVec 32), tmp'.length = c.max_vars ∧
        tk'.toNat = 1 + ((C_lits.take (j.toNat + 1)).filter (· != flit.toNat)).length ∧
        tmp'[0]? = some (fresh ^^^ 1#32) ∧
        (∀ t, 1 ≤ t → t < tk'.toNat → (tmp'[t]?.getD 0#32).toNat =
          ((C_lits.take (j.toNat + 1)).filter (· != flit.toNat))[t - 1]?.getD 0) ∧
        (FullMem c { stm with core := { stm.core with tmp := tmp' } } ⋆ R) m')
      (fun _ (tk', ()) m' ⟨tmp', htl', htk', h0', hrest', hm'⟩ => by
        s8_hsteps_to_jump; exact ihf (tk', j + 1#32, ()) m' (by dsimp only; rw [hj1]; omega)
          ⟨tmp', by rw [hj1]; omega, htl', by rw [hj1]; exact htk', h0',
           fun t ht1 ht2 => by rw [hj1]; exact hrest' t ht1 ht2, hm'⟩)
      (fun Jif hJif => ?_)
    c0_hsplit
    · have hne_bv : stm.core.arena[c_top.toNat + 3 + j.toNat]'hctj_ar ≠ flit := by
        have h1 : ¬ stm.core.arena[(c_top.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) %
            2 ^ 64]'(by rw [hctj_mod]; exact hctj_ar) = flit := by assumption
        simpa only [hctj_mod] using h1
      have hne_nat : C_lits[j.toNat]'(by rw [hC_len]; exact hj_lt) ≠ flit.toNat := by
        rw [hCj_eq]; intro h; exact hne_bv (BitVec.eq_of_toNat_eq h)
      have htk_succ_eq : ((C_lits.take (j.toNat + 1)).filter (· != flit.toNat)).length =
          ((C_lits.take j.toNat).filter (· != flit.toNat)).length + 1 := by
        rw [htake_succ, ite_eq_left (bne_iff_ne.mpr hne_nat), List.length_append]; rfl
      have htk_lt_tmp : tk.toNat < tmpj.length := by omega
      have htk1 : (tk + 1#32).toNat = tk.toNat + 1 := by c0_bound
      s8_hsteps_to_jump; refine hJif (tk + 1#32, ()) m
        ⟨tmpj.set tk.toNat (stm.core.arena[c_top.toNat + 3 + j.toNat]'hctj_ar),
         by simp [htmpj_l], by rw [htk1, htk_succ_eq]; omega,
         by rw [List.getElem?_set_ne (by omega)]; exact htmp0, fun t ht1 ht2 => ?_, ?_⟩
      · rw [htk1] at ht2; rw [htake_succ, ite_eq_left (bne_iff_ne.mpr hne_nat)]
        by_cases hte : t = tk.toNat
        · subst hte
          rw [List.getElem?_set_self htk_lt_tmp, Option.getD_some,
            List.getElem?_append_right (by omega),
            show tk.toNat - 1 - ((C_lits.take j.toNat).filter (· != flit.toNat)).length = 0 by
              omega]
          simp [hCj_eq]
        · rw [List.getElem?_set_ne (Ne.symm hte), List.getElem?_append_left (by omega)]
          exact htmp_rest t ht1 (by omega)
      · simp only [hctj_n, bv64_setWidth_32] at hm; exact hm
    · have heq_bv : stm.core.arena[c_top.toNat + 3 + j.toNat]'hctj_ar = flit := by
        have h1 : stm.core.arena[(c_top.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) %
            2 ^ 64]'(by rw [hctj_mod]; exact hctj_ar) = flit := by assumption
        simpa only [hctj_mod] using h1
      have heq_nat : (C_lits[j.toNat]'(by rw [hC_len]; exact hj_lt) != flit.toNat) = false := by
        rw [hCj_eq, heq_bv]; simp
      have htake_eq : (C_lits.take (j.toNat + 1)).filter (· != flit.toNat) =
          (C_lits.take j.toNat).filter (· != flit.toNat) := by
        rw [htake_succ, heq_nat]; simp
      dsimp only [wp, vals, Arg.val]; exact hJif (tk, ()) mj
        ⟨tmpj, htmpj_l, by rw [htake_eq]; exact htk_eq, htmp0,
         fun t ht1 ht2 => by rw [htake_eq]; exact htmp_rest t ht1 ht2, hmj⟩
  · have hj_eq : j.toNat = csz.toNat := by
      have h1 : ¬ j.toNat < csz.toNat := by assumption
      omega
    rw [hj_eq, ← hC_len, List.take_length] at htk_eq htmp_rest
    have htk_csz : tk.toNat = csz.toNat := by omega
    let st_tmp : FullState := { stm with core := { stm.core with tmp := tmpj } }
    have hinv_tmp : FullDenseInvW c F0 F_next st_tmp := s8_fullDenseInvW_set_tmp hinvm htmpj_l
    c0_call hAllocCl; refine ⟨c, st_tmp, R, rfl, hinv_tmp.1, hmj, ?_⟩; split
    · s8_hsteps_to_jump; exact hAbort st_tmp mj hmj ⟨hinv_tmp, hcvm, hfuelm, hsbm, htmm, htrm,
        hmono, hresm⟩
    · intro ar1 ma1; dsimp only; intro hlen_a1 hhold_a1 hns_a1 hng_a1 _ hsz_a1 hma1
      have hncr_nat : (BitVec.ofNat 64 stm.core.arena_len).toNat = stm.core.arena_len := by
        have := hclm.arena_len_le; c0_bound
      c0_hsteps_nogrp
      · let ncr0 := stm.core.arena_len
        have hncr_cap : ncr0 + 3 + tk.toNat ≤ c.arena_cap := hlen_a1.core_ok.arena_len_le
        refine wp_loop_inv
          (fun (jc, ()) mjc => ∃ arj : List (BitVec 32), jc.toNat ≤ tk.toNat ∧
            arj.length = c.arena_cap ∧ (∀ i < ncr0, arj[i]? = stm.core.arena[i]?) ∧
            arj[ncr0]? = ar1[ncr0]? ∧ arj[ncr0 + 2]? = ar1[ncr0 + 2]? ∧
            (∀ t < jc.toNat, arj[ncr0 + 3 + t]? = tmpj[t]?) ∧
            (FullMem c { st_tmp with core := { st_tmp.core with
              arena := arj, arena_len := ncr0 + 3 + tk.toNat } } ⋆ R) mjc)
          (fun (jc, _) _ => tk.toNat - jc.toNat) (fun Jcp hJcp => by
            s8_hsteps_to_jump
            exact hJcp (0#32, ()) ma1 ⟨ar1, Nat.zero_le _, hlen_a1.core_ok.arena_len_arr,
              hhold_a1, rfl, rfl, fun _ h => by simp only [bv_c0] at h; omega, hma1⟩)
          (fun Jcp (jc, ()) mjc ⟨arj, hjc_le, harj_l, hhold_j, harj0, harj2, hcp_j, hmjc⟩ ihcp =>
            ?_)
        c0_hsteps_nogrp
        · have hjc_lt : jc.toNat < tk.toNat := by c0_bound
          have hjc1 : (jc + 1#32).toNat = jc.toNat + 1 := by c0_bound
          have hncr_jc : (BitVec.ofNat 64 st_tmp.core.arena_len + 3 +
              BitVec.setWidth 64 jc).toNat = ncr0 + 3 + jc.toNat := by
            change (BitVec.ofNat 64 ncr0 + 3#64 + BitVec.setWidth 64 jc).toNat = _; c0_bound
          have hjc_tmp : jc.toNat < tmpj.length := by omega
          s8_hsteps_to_jump; refine ihcp (jc + 1#32, ()) m (by dsimp only; rw [hjc1]; omega)
            ⟨arj.set (ncr0 + 3 + jc.toNat) (tmpj[jc.toNat]'hjc_tmp),
             by rw [hjc1]; omega, by simp [harj_l],
             fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hhold_j i hi,
             by rw [List.getElem?_set_ne (by omega)]; exact harj0,
             by rw [List.getElem?_set_ne (by omega)]; exact harj2, fun t ht => by
               rw [hjc1] at ht; by_cases hte : t = jc.toNat
               · subst hte; rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem hjc_tmp]
               · rw [List.getElem?_set_ne (by omega)]; exact hcp_j t (by omega),
             by simp only [hncr_jc, bv64_setWidth_32] at hm; exact hm⟩
        · have hjc_eq : jc.toNat = tk.toNat := by c0_bound
          rw [hjc_eq] at hcp_j
          let st_cp : FullState :=
            { st_tmp with core := { st_tmp.core with arena := arj,
                                                     arena_len := ncr0 + 3 + tk.toNat } }
          have hlen_cp : st_cp.LengthsOk c :=
            ⟨{ hlen_a1.core_ok with arena_len_arr := harj_l }, hlen_a1.scratch_ok⟩
          have hns_cp : (arj[ncr0]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
            rw [harj0]; exact hns_a1
          have hsz_cp : (arj[ncr0 + 2]?.getD 0#32).toNat = tk.toNat := by
            rw [harj2]; exact hsz_a1
          have hrefs_cp : fullArenaClauseRefsCore st_cp.core =
              fullArenaClauseRefsCore stm.core ++ [ncr0] :=
            fullArenaClauseRefsCore_append hinvm.2.1.arena (by omega) rfl hhold_j hns_cp hsz_cp
          have hwat_cp : ModeWatchesInv F_next st_cp.core :=
            hinvm.2.1.watches.with_wstk rfl rfl rfl rfl rfl
              (fun r hr => by rw [hrefs_cp]; exact List.mem_append_left _ hr)
          have hnew_lits_eq : fullArenaClauseLitsCore { stm.core with arena := arj } ncr0 =
              (2 * old_cv + 1) :: C_lits.filter (· != flit.toNat) := by
            rw [s8_fullArenaLitsCore_eq_map (sz := tk.toNat)
              (by unfold fullArenaClauseSizeCore; exact hsz_cp) (by dsimp only; omega)]
            apply List.ext_getElem?; intro t; cases t with
            | zero =>
              rw [List.getElem?_map, List.getElem?_range (by omega), Option.map_some,
                Nat.add_zero, hcp_j 0 (by omega), htmp0, Option.getD_some, hfresh1]; rfl
            | succ t' =>
              by_cases ht : t' + 1 < tk.toNat
              · rw [List.getElem?_map, List.getElem?_range ht, Option.map_some,
                  hcp_j (t' + 1) ht, htmp_rest (t' + 1) (by omega) ht, Nat.add_sub_cancel,
                  List.getElem?_cons_succ,
                  List.getElem?_eq_getElem (by omega : t' < (C_lits.filter (· !=
                    flit.toNat)).length),
                  Option.getD_some]
              · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
          have hnew_perm : (fullArenaClauseLitsCore { stm.core with arena := arj }
              ncr0).Perm ((2 * old_cv + 1) :: resm) := by
            rw [hnew_lits_eq]; have hf' : resm.Perm (C_lits.filter (· != flit.toNat)) := by
              rw [hflit_eq]; exact hres_perm_f
            exact List.Perm.cons _ hf'.symm
          have hnew_lt :
              ∀ l ∈ fullArenaClauseLitsCore { stm.core with arena := arj } ncr0,
              l < 2 * stm.core.cur_vars := by
            intro l hl; rw [hcvm]; rcases List.mem_cons.mp (hnew_perm.subset hl) with rfl | hr
            · omega
            · have := hresm_lt l hr; omega
          have hnew_nd : ((fullArenaClauseLitsCore { stm.core with arena := arj }
              ncr0).map (· / 2)).Nodup := by
            have hp := hnew_perm.map (· / 2)
            refine (List.nodup_cons.mpr ⟨?_, hresm_nd⟩).perm hp.symm
            intro hmem; obtain ⟨x, hx, hdiv⟩ := List.mem_map.mp hmem
            have := hresm_lt x hx; dsimp only [old_cv] at *; omega
          have hnew_ent : (cnfOfClauses F_next).EntailsClause
              (cnfClause (fullArenaClauseLitsCore { stm.core with arena := arj } ncr0)) :=
            clause_entails_of_perm hnew_perm.symm hresm_ent
          have htmp_lt :
              ∀ t (ht : t < tk.toNat), (tmpj[t]'(by omega)).toNat < 2 * (old_cv + 1) := by
            intro t ht; have hmem : (tmpj[t]'(by omega)).toNat ∈
                fullArenaClauseLitsCore { stm.core with arena := arj } ncr0 := by
              rw [s8_fullArenaLitsCore_eq_map (sz := tk.toNat)
                (by unfold fullArenaClauseSizeCore; exact hsz_cp) (by dsimp only; omega)]
              refine List.mem_map.mpr ⟨t, List.mem_range.mpr ht, ?_⟩
              rw [hcp_j t ht, List.getElem?_eq_getElem (by omega), Option.getD_some]
            simpa only [hcvm] using hnew_lt _ hmem
          exact s8_bva_large_watch_wp (stm := stm) hWPush hUnwatch
            ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩ htmpj_l (by omega) (by omega)
            hncr_cap hhold_j hns_cp hsz_cp hnew_lt hnew_nd hnew_ent (fun t ht => htmp_lt t ht)
            hlen_cp hrefs_cp hwat_cp hmjc hDone

end LeanQbe.T.Examples.Kissat.FullFidelityStep8

end
