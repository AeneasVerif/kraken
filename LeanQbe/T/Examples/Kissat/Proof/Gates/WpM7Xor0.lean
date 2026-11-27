/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Gates.WpHelpers

/-!
# Kissat Gates WP Proofs — M7 XOR Helpers & Neg-Scan (`WpM7Xor0`)

Shared sub-expressions, invariants, mask-bit lemmas, and inner loop WP proofs
(`m7_xor_clean_lm_wp`, `m7_xor_commit_wp`, `m7_xor_neg_scan_wp`) for
`full_bve_find_xor_m7` (`0` legacy `Full*` imports; every decl `<= 450` LOC).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Gates

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Gates
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "gates_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

@[expose] public section

abbrev m7XorState (s : FullState) (lm : List (BitVec 8))
    (scr : List (BitVec 32)) : FullState :=
  { s with
    core := { s.core with lit_mark := lm }
    scratch := { s.scratch with scratch_buf := scr } }

def XorMaskEntriesOk (scr : List (BitVec 32)) (base lim : Nat)
    (mask : BitVec 32) : Prop :=
  mask.toNat < 65536 ∧
  ∀ t < 16, (mask &&& (1#32 <<< t)) ≠ 0#32 → (scr[base + t]?.getD 0#32).toNat < lim

def XorCollectInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (sz k ci : BitVec 32) (mc : Mem 64) : Prop :=
  ∃ (lmc : List (BitVec 8)) (scrc : List (BitVec 32)),
    ci.toNat ≤ sz.toNat ∧ k.toNat ≤ 4 ∧
    lmc.length = 2 * c.max_vars ∧ scrc.length = c.scratch_cap ∧
    (∀ idx < c.scratch_cap, (idx < 1024 ∨ 1096 ≤ idx) →
      scrc[idx]? = s.scratch.scratch_buf[idx]?) ∧
    (∀ j < k.toNat, (scrc[1092 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (∀ y < lmc.length, lmc[y]?.getD 0#8 ≠ 0#8 →
      ∃ j < k.toNat,
        y = (scrc[1092 + j]?.getD 0#32).toNat ∨
        y = ((scrc[1092 + j]?.getD 0#32) ^^^ 1#32).toNat) ∧
    (FullMem c (m7XorState s lmc scrc) ⋆ R) mc

def m7XorLmClearExpr (pScr pLm : BitVec 64) (k : BitVec 32)
    (after : Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.group (sig := [[i32]])
    (fun lbls =>
      Blocks.cons (fun c_idx =>
        Expr.let_ ⟨OpCode.ult i32, (Arg.var c_idx.fst, Arg.var k, ())⟩ fun b =>
        Expr.jnz (Arg.var b.fst)
          (Expr.let_ ⟨OpCode.add i32, (Arg.imm 1092, Arg.var c_idx.fst, ())⟩ fun p0 =>
           Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p0.fst, ())⟩ fun p1 =>
           Expr.let_ ⟨OpCode.mul i64, (Arg.var p1.fst, Arg.imm 4, ())⟩ fun p2 =>
           Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p2.fst, ())⟩ fun p3 =>
           Expr.load i32 (Arg.var p3.fst) fun l =>
           Expr.let_ ⟨OpCode.zext 32 64, (Arg.var l, ())⟩ fun q0 =>
           Expr.let_ ⟨OpCode.add i64, (Arg.var pLm, Arg.var q0.fst, ())⟩ fun q1 =>
           Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm (t := i32) 0, ())⟩ fun z0 =>
           Expr.store (Arg.var z0.fst) (Arg.var q1.fst) (
           Expr.let_ ⟨OpCode.xor i32, (Arg.var l, Arg.imm 1, ())⟩ fun lx =>
           Expr.let_ ⟨OpCode.zext 32 64, (Arg.var lx.fst, ())⟩ fun r0 =>
           Expr.let_ ⟨OpCode.add i64, (Arg.var pLm, Arg.var r0.fst, ())⟩ fun r1 =>
           Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm (t := i32) 0, ())⟩ fun z1 =>
           Expr.store (Arg.var z1.fst) (Arg.var r1.fst) (
           Expr.let_ ⟨OpCode.add i32, (Arg.var c_idx.fst, Arg.imm 1, ())⟩ fun nx =>
           Expr.jump lbls.1 (Arg.var nx.fst, ()))))
          after)
        Blocks.nil)
    (fun lbls => Expr.jump lbls.1 (Arg.imm (t := i32) 0, ()))

def m7XorCommitExpr (pScr : BitVec 64) (k fullPmask fullNmask : BitVec 32) :
    Expr Val Cont [.bool] :=
  Expr.let_ ⟨OpCode.shl i32, (Arg.imm 1, Arg.var k, ())⟩ fun need =>
  Expr.group (sig := [[i32]])
    (fun lbl69 =>
      Blocks.cons (fun p =>
        Expr.let_ ⟨OpCode.ult i32, (Arg.var p.fst, Arg.var need.fst, ())⟩ fun cond =>
        Expr.jnz (Arg.var cond.fst)
          (Expr.group (sig := [[]])
            (fun _lbl72 =>
              Blocks.cons (fun _ =>
                Expr.group (sig := [[]])
                  (fun _lbl73 =>
                    Blocks.cons (fun _ =>
                      Expr.let_ ⟨OpCode.add i32, (Arg.var p.fst, Arg.imm 1, ())⟩ fun np =>
                      Expr.jump lbl69.1 (Arg.var np.fst, ())) Blocks.nil)
                  (fun lbl73 =>
                    Expr.let_ ⟨OpCode.lshr i32, (Arg.var fullNmask, Arg.var p.fst, ())⟩ fun s =>
                    Expr.let_ ⟨OpCode.and i32, (Arg.var s.fst, Arg.imm 1, ())⟩ fun b =>
                    Expr.let_ ⟨OpCode.ne i32, (Arg.var b.fst, Arg.imm 0, ())⟩ fun c0 =>
                    Expr.jnz (Arg.var c0.fst)
                      (Expr.let_ ⟨OpCode.add i32, (Arg.imm 1076, Arg.var p.fst, ())⟩ fun a0 =>
                       Expr.let_ ⟨OpCode.zext 32 64, (Arg.var a0.fst, ())⟩ fun a1 =>
                       Expr.let_ ⟨OpCode.mul i64, (Arg.var a1.fst, Arg.imm 4, ())⟩ fun a2 =>
                       Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var a2.fst, ())⟩ fun a3 =>
                       Expr.load i32 (Arg.var a3.fst) fun idx =>
                       m7SetMaskBitExpr pScr 1040#32 idx (Expr.jump lbl73.1 ()))
                      (Expr.jump lbl73.1 ()))) Blocks.nil)
            (fun lbl72 =>
              Expr.let_ ⟨OpCode.lshr i32, (Arg.var fullPmask, Arg.var p.fst, ())⟩ fun s =>
              Expr.let_ ⟨OpCode.and i32, (Arg.var s.fst, Arg.imm 1, ())⟩ fun b =>
              Expr.let_ ⟨OpCode.ne i32, (Arg.var b.fst, Arg.imm 0, ())⟩ fun c0 =>
              Expr.jnz (Arg.var c0.fst)
                (Expr.let_ ⟨OpCode.add i32, (Arg.imm 1060, Arg.var p.fst, ())⟩ fun a0 =>
                 Expr.let_ ⟨OpCode.zext 32 64, (Arg.var a0.fst, ())⟩ fun a1 =>
                 Expr.let_ ⟨OpCode.mul i64, (Arg.var a1.fst, Arg.imm 4, ())⟩ fun a2 =>
                 Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var a2.fst, ())⟩ fun a3 =>
                 Expr.load i32 (Arg.var a3.fst) fun idx =>
                 m7SetMaskBitExpr pScr 1024#32 idx (Expr.jump lbl72.1 ()))
                (Expr.jump lbl72.1 ())))
          (Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm (t := i32) 1056, ())⟩ fun w0 =>
           Expr.let_ ⟨OpCode.mul i64, (Arg.var w0.fst, Arg.imm 4, ())⟩ fun w1 =>
           Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var w1.fst, ())⟩ fun w2 =>
           Expr.store (Arg.imm (t := i32) 1) (Arg.var w2.fst) (
           Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm (t := i32) 1057, ())⟩ fun y0 =>
           Expr.let_ ⟨OpCode.mul i64, (Arg.var y0.fst, Arg.imm 4, ())⟩ fun y1 =>
           Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var y1.fst, ())⟩ fun y2 =>
           Expr.store (Arg.imm (t := i32) 0) (Arg.var y2.fst) (
           Expr.ret (Arg.imm (t := .bool) true, ())))))
        Blocks.nil)
    (fun lbl69 => Expr.jump lbl69.1 (Arg.imm (t := i32) 0, ()))

def m7XorNegScanExpr (h pScr : Val i64) (nn nl k otgt : Val i32)
    (onDone : Val i32 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.group (sig := [[i32, i32]])
    (fun Js7 =>
      Blocks.cons
        (fun p41 =>
          Expr.let_ ⟨OpCode.ult i32, (Arg.var p41.snd.fst, Arg.var nn, ())⟩ fun p42 =>
          Expr.jnz (Arg.var p42.fst)
            (Expr.let_ ⟨OpCode.ne i32, (Arg.var p41.fst, Arg.var otgt, ())⟩ fun p43 =>
             Expr.jnz (Arg.var p43.fst)
               (Expr.let_ ⟨OpCode.add i32, (Arg.imm 512, Arg.var p41.snd.fst, ())⟩ fun p44 =>
                Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p44.fst, ())⟩ fun p45 =>
                Expr.let_ ⟨OpCode.mul i64, (Arg.var p45.fst, Arg.imm 4, ())⟩ fun p46 =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p46.fst, ())⟩ fun p47 =>
                Expr.load i32 (Arg.var p47.fst) fun ld =>
                Expr.group (sig := [[i32]])
                  (fun _JsNext =>
                    Blocks.cons
                      (fun pNext =>
                        Expr.let_ ⟨OpCode.add i32, (Arg.var p41.snd.fst, Arg.imm 1, ())⟩ fun p48 =>
                        Expr.jump Js7.fst (Arg.var pNext.fst, Arg.var p48.fst, ()))
                      Blocks.nil)
                  (fun Js =>
                    Expr.let_ ⟨OpCode.and i32, (Arg.var ld, Arg.imm 2147483648, ())⟩ fun p48 =>
                    Expr.let_ ⟨OpCode.eq i32, (Arg.var p48.fst, Arg.imm 0, ())⟩ fun p49 =>
                    Expr.jnz (Arg.var p49.fst)
                      (Expr.call "full_bve_xor_pat_m7" (as := [i64, i32, i32, i32]) (bs := [i32])
                        (Arg.var h, Arg.var nl, Arg.var ld, Arg.var k, ())
                        fun pat =>
                        Expr.group (sig := [[i32]])
                          (fun _Js8 =>
                            Blocks.cons
                              (fun px => Expr.jump Js.fst (Arg.var px.fst, ()))
                              Blocks.nil)
                          (fun JsJoin =>
                            Expr.let_ ⟨OpCode.ult i32, (Arg.var pat.fst, Arg.imm 16, ())⟩
                              fun p50 =>
                            Expr.jnz (Arg.var p50.fst)
                              (Expr.let_ ⟨OpCode.lshr i32, (Arg.var otgt, Arg.var pat.fst, ())⟩
                                fun p51 =>
                               Expr.let_ ⟨OpCode.and i32, (Arg.var p51.fst, Arg.imm 1, ())⟩
                                 fun p52 =>
                               Expr.let_ ⟨OpCode.ne i32, (Arg.var p52.fst, Arg.imm 0, ())⟩
                                 fun p53 =>
                               Expr.jnz (Arg.var p53.fst)
                                 (Expr.let_ ⟨OpCode.lshr i32,
                                     (Arg.var p41.fst, Arg.var pat.fst, ())⟩ fun p54 =>
                                  Expr.let_ ⟨OpCode.and i32, (Arg.var p54.fst, Arg.imm 1, ())⟩
                                    fun p55 =>
                                  Expr.let_ ⟨OpCode.eq i32, (Arg.var p55.fst, Arg.imm 0, ())⟩
                                    fun p56 =>
                                  Expr.jnz (Arg.var p56.fst)
                                    (Expr.let_ ⟨OpCode.shl i32, (Arg.imm 1, Arg.var pat.fst, ())⟩
                                      fun p57 =>
                                     Expr.let_ ⟨OpCode.or i32,
                                         (Arg.var p41.fst, Arg.var p57.fst, ())⟩ fun p58 =>
                                     Expr.let_ ⟨OpCode.add i32,
                                         (Arg.imm 1076, Arg.var pat.fst, ())⟩ fun q0 =>
                                     Expr.let_ ⟨OpCode.zext 32 64, (Arg.var q0.fst, ())⟩ fun q1 =>
                                     Expr.let_ ⟨OpCode.mul i64, (Arg.var q1.fst, Arg.imm 4, ())⟩
                                       fun q2 =>
                                     Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var q2.fst, ())⟩
                                       fun q3 =>
                                     Expr.store (Arg.var p41.snd.fst) (Arg.var q3.fst)
                                       (Expr.jump JsJoin.fst (Arg.var p58.fst, ())))
                                    (Expr.jump JsJoin.fst (Arg.var p41.fst, ())))
                                 (Expr.jump JsJoin.fst (Arg.var p41.fst, ())))
                              (Expr.jump JsJoin.fst (Arg.var p41.fst, ()))))
                      (Expr.jump Js.fst (Arg.var p41.fst, ()))))
               (onDone p41.fst))
            (onDone p41.fst))
        Blocks.nil)
    (fun Js => Expr.jump Js.fst (Arg.imm (t := i32) 0, Arg.imm (t := i32) 0, ()))

end

public section

theorem m7_shl16_toNat {p : BitVec 32} (hp : p.toNat < 16) :
    (1#32 <<< p).toNat = 2 ^ p.toNat := by
  change (1#32 <<< p.toNat).toNat = 2 ^ p.toNat
  rw [BitVec.toNat_shiftLeft, show (1#32).toNat = 1 from rfl, Nat.one_shiftLeft]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.pow_lt_pow_right (by omega) hp) (by omega))

theorem xorMaskEntriesOk_init {scr : List (BitVec 32)} {base lim : Nat}
    (hlen : base + 16 ≤ scr.length) {idx : BitVec 32} (hidx : idx.toNat < lim) :
    XorMaskEntriesOk (scr.set base idx) base lim 1#32 := by
  refine ⟨by decide, fun t ht hbit => ?_⟩
  have ht0 : t = 0 := by
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · rfl
    · exfalso; apply hbit
      apply BitVec.eq_of_getLsbD_eq; intro k
      by_cases hk : k = 0 <;> simp [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft] <;> omega
  subst ht0
  rw [show base + 0 = base from Nat.add_zero _, List.getElem?_set_self (by omega),
    Option.getD_some]
  exact hidx

theorem xorMaskEntriesOk_zero (scr : List (BitVec 32)) (base lim : Nat) :
    XorMaskEntriesOk scr base lim 0#32 :=
  ⟨by decide, fun _ _ h => by simp at h⟩

theorem xorMaskEntriesOk_set {scr : List (BitVec 32)} {base lim : Nat}
    {mask pat j : BitVec 32} (hm : XorMaskEntriesOk scr base lim mask)
    (hlen : base + 16 ≤ scr.length) (hpat : pat.toNat < 16) (hj : j.toNat < lim) :
    XorMaskEntriesOk (scr.set (base + pat.toNat) j) base lim (mask ||| (1#32 <<< pat)) := by
  have hshl := m7_shl16_toNat hpat
  have hshl_lt : (1#32 <<< pat).toNat < 2 ^ 16 := by
    rw [hshl]; exact Nat.pow_lt_pow_right (by omega) hpat
  refine ⟨?_, fun t ht hbit => ?_⟩
  · rw [BitVec.toNat_or]
    exact Nat.or_lt_two_pow hm.1 hshl_lt
  · by_cases htp : t = pat.toNat
    · subst htp
      rw [List.getElem?_set_self (by omega), Option.getD_some]
      exact hj
    · rw [List.getElem?_set_ne (by omega)]
      refine hm.2 t ht fun h0 => hbit ?_
      have hmk : mask.getLsbD t = false := by
        have := congrArg (fun x => x.getLsbD t) h0
        simpa [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, show t < 32 by omega] using this
      have hpk : (1#32 <<< pat).getLsbD t = false := by
        change (1#32 <<< pat.toNat).getLsbD t = false
        simp [BitVec.getLsbD_shiftLeft]; intro _ _ _; omega
      apply BitVec.eq_of_getLsbD_eq; intro k
      by_cases hk : k = t
      · rw [hk]; simp [BitVec.getLsbD_and, BitVec.getLsbD_or, hmk]; intro _ _ _; omega
      · simp [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]; intro _ _; omega

theorem m7_xor_clean_lm_wp (Γ : Env) (c : FullCfg) (s0 : FullState)
    (lm : List (BitVec 8)) (scr : List (BitVec 32)) (R : Mem 64 → Prop)
    (k : BitVec 32) (m : Mem 64) (Q : Post [.bool]) (X : XPost)
    (after : Expr Val Cont [.bool])
    (hlm : lm.length = 2 * c.max_vars) (hsc : scr.length = c.scratch_cap)
    (h1096 : 1096 ≤ c.scratch_cap) (hk4 : k.toNat ≤ 4)
    (hcv_le : s0.core.cur_vars ≤ c.max_vars)
    (hrec : ∀ j < k.toNat, (scr[1092 + j]?.getD 0#32).toNat < 2 * s0.core.cur_vars)
    (hnz : ∀ y < 2 * c.max_vars, lm[y]?.getD 0#8 ≠ 0#8 →
      ∃ j < k.toNat, y = (scr[1092 + j]?.getD 0#32).toNat ∨
        y = ((scr[1092 + j]?.getD 0#32) ^^^ 1#32).toNat)
    (hm : (FullMem c (m7XorState s0 lm scr) ⋆ R) m)
    (hafter : ∀ (lm' : List (BitVec 8)), lm'.length = 2 * c.max_vars →
      (∀ y < 2 * c.max_vars, lm'[y]?.getD 0#8 = 0#8) →
      ∀ m', (FullMem c (m7XorState s0 lm' scr) ⋆ R) m' →
        wp Γ Q X after m') :
    wp Γ Q X (m7XorLmClearExpr c.pScratchBuf c.pLitMark k after) m := by
  unfold m7XorLmClearExpr
  refine wp_loop_group (ts := [i32])
    (fun rem (ci, ()) mc => ∃ lmc : List (BitVec 8),
      lmc.length = 2 * c.max_vars ∧ ci.toNat ≤ k.toNat ∧ rem = k.toNat - ci.toNat ∧
      (∀ y < 2 * c.max_vars, lmc[y]?.getD 0#8 ≠ 0#8 →
        ∃ j, ci.toNat ≤ j ∧ j < k.toNat ∧
          (y = (scr[1092 + j]?.getD 0#32).toNat ∨
            y = ((scr[1092 + j]?.getD 0#32) ^^^ 1#32).toNat)) ∧
      (FullMem c (m7XorState s0 lmc scr) ⋆ R) mc)
    ?_ ?_
  · rintro L rem ⟨ci, ⟨⟩⟩ mc hL ⟨lmc, hlmc, hci_le, rfl, hnz_c, hmc⟩
    c0_hsplit
    · have hc_ci : ci.toNat < k.toNat := hc
      have hsc_idx : ((1092#32 + ci).setWidth 64).toNat < scr.length := by
        rw [hsc, zext32_toNat]; c0_bound
      have hsc_eq : ((1092#32 + ci).setWidth 64).toNat = 1092 + ci.toNat := by
        rw [zext32_toNat]; c0_bound
      let l := scr[((1092#32 + ci).setWidth 64).toNat]'hsc_idx
      have hl_orig : l = scr[1092 + ci.toNat]?.getD 0#32 := by
        have hlt : 1092 + ci.toNat < scr.length := by omega
        rw [List.getElem?_eq_getElem hlt, Option.getD_some]
        exact getElem_congr hsc_eq hsc_idx hlt
      have hl_lt : l.toNat < 2 * c.max_vars := by
        have := hrec ci.toNat hc_ci; rw [← hl_orig] at this; omega
      have hl1_lt : (l ^^^ 1#32).toNat < 2 * c.max_vars := by
        have := xor1_lt l (by rw [hl_orig]; exact hrec ci.toNat hc_ci)
        omega
      have hl_sc : (l.setWidth 64).toNat < lmc.length := by
        rw [hlmc, zext32_toNat]; exact hl_lt
      have hl1_sc : ((l ^^^ 1#32).setWidth 64).toNat < lmc.length := by
        rw [hlmc, zext32_toNat]; exact hl1_lt
      have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      dsimp only [m7XorState] at hm ⊢
      have hl1_set : (((l ^^^ 1#32).setWidth 64).toNat) <
          (lmc.set (l.setWidth 64).toNat 0#8).length := by
        rw [List.length_set]; exact hl1_sc
      c0_hsteps_nogrp
      refine hL (k.toNat - (ci + 1#32).toNat) (ci + 1#32, ()) _ (by rw [hci1]; omega)
        ⟨_, ?_, by rw [hci1]; omega, rfl, ?_, by assumption⟩
      · rw [List.length_set, List.length_set, hlmc]
      · dsimp only
        refine lm_clear2_step hlmc (by rw [zext32_toNat]; exact hl_lt)
          (by rw [zext32_toNat]; exact hl1_lt) (fun y hy hy_nz => ?_)
        obtain ⟨j, hj_ge, hj_lt, hy_eq⟩ := hnz_c y hy hy_nz
        by_cases hjeq : j = ci.toNat
        · subst hjeq; rw [← hl_orig] at hy_eq
          rcases hy_eq with h0 | h1
          · exact Or.inl (h0.trans (zext32_toNat _).symm)
          · exact Or.inr (Or.inl (h1.trans (zext32_toNat _).symm))
        · exact Or.inr (Or.inr ⟨j, by omega, hj_lt, hy_eq⟩)
    · have hclr : ∀ y < 2 * c.max_vars, lmc[y]?.getD 0#8 = 0#8 := fun y hy =>
        Classical.byContradiction fun hy_nz => by
          obtain ⟨j, hj_ge, hj_lt, _⟩ := hnz_c y hy hy_nz
          omega
      exact hafter lmc hlmc hclr mc hmc
  · intro L hL; c0_hsteps!
    exact hL k.toNat (0#32, ()) m
      ⟨lm, hlm, Nat.zero_le _, by simp,
        fun y hy hy_nz => let ⟨j, hj, hy_eq⟩ := hnz y hy hy_nz; ⟨j, Nat.zero_le _, hj, hy_eq⟩,
        hm⟩

theorem m7_xor_commit_wp (Γ : Env) (c : FullCfg) (s0 : FullState)
    (scr_in : List (BitVec 32)) (R : Mem 64 → Prop)
    (k fullPmask fullNmask : BitVec 32)
    (m_in : Mem 64) (Q : Post [.bool]) (X : XPost)
    (hsc_in : scr_in.length = c.scratch_cap)
    (hout_in : ∀ i < c.scratch_cap, (i < 1024 ∨ 1096 ≤ i) →
      scr_in[i]? = s0.scratch.scratch_buf[i]?)
    (hsc1096 : 1096 ≤ c.scratch_cap) (hk1 : 1 ≤ k.toNat) (hk4 : k.toNat ≤ 4)
    (hpm_ok : ∀ b < 16, (fullPmask &&& (1#32 <<< b)) ≠ 0#32 →
      (scr_in[1060 + b]?.getD 0#32).toNat < 512)
    (hnm_ok : ∀ b < 16, (fullNmask &&& (1#32 <<< b)) ≠ 0#32 →
      (scr_in[1076 + b]?.getD 0#32).toNat < 512)
    (hm_in : (FullMem c { s0 with scratch := { s0.scratch with scratch_buf := scr_in } } ⋆ R)
      m_in)
    (hQ : ∀ (ok : Bool) (scr' : List (BitVec 32)) (m' : Mem 64),
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1096 ≤ i) →
        scr'[i]? = s0.scratch.scratch_buf[i]?) →
      (FullMem c { s0 with scratch := { s0.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q (ok, ()) m') :
    wp Γ Q X (m7XorCommitExpr c.pScratchBuf k fullPmask fullNmask) m_in := by
  have hneed_le : (1#32 <<< k).toNat ≤ 16 := by
    change (1#32 <<< k.toNat).toNat ≤ 16
    have hpow : 2 ^ k.toNat ≤ 2 ^ 4 := Nat.pow_le_pow_right (by omega) hk4
    rw [BitVec.toNat_shiftLeft, show (1#32).toNat = 1 from rfl, Nat.one_shiftLeft,
      Nat.mod_eq_of_lt (by omega)]
    exact hpow
  unfold m7XorCommitExpr
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32])
    (fun rem (p, ()) mc => ∃ scr_c : List (BitVec 32),
      let sc : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr_c } }
      scr_c.length = c.scratch_cap ∧ p.toNat ≤ (1#32 <<< k).toNat ∧
      rem = (1#32 <<< k).toNat - p.toNat ∧
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1056 ≤ i) → scr_c[i]? = scr_in[i]?) ∧
      (FullMem c sc ⋆ R) mc)
    ?_ ?_
  · rintro L rem ⟨p, ⟨⟩⟩ mc hL ⟨scr_c, hsc_c, hp_le, rfl, hout_c, hm_c⟩
    c0_hsplit
    · have hp_lt : p.toNat < (1#32 <<< k).toNat := by
        rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
      have hp16 : p.toNat < 16 := by omega
      have hp1 : (p + 1#32).toNat = p.toNat + 1 := by c0_bound
      refine wp_join_group (ts := [])
        (fun _ m72 => ∃ scr_d : List (BitVec 32),
          let sd : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr_d } }
          scr_d.length = c.scratch_cap ∧
          (∀ i < c.scratch_cap, (i < 1024 ∨ 1056 ≤ i) → scr_d[i]? = scr_in[i]?) ∧
          (FullMem c sd ⋆ R) m72)
        (fun _ _ m72 ⟨scr_d, hsc_d, hout_d, hm_d⟩ => by
          refine wp_join_group (ts := [])
            (fun _ m73 => ∃ scr_e : List (BitVec 32),
              let se : FullState :=
                { s0 with scratch := { s0.scratch with scratch_buf := scr_e } }
              scr_e.length = c.scratch_cap ∧
              (∀ i < c.scratch_cap, (i < 1024 ∨ 1056 ≤ i) → scr_e[i]? = scr_in[i]?) ∧
              (FullMem c se ⋆ R) m73)
            (fun _ _ m73 ⟨scr_e, hsc_e, hout_e, hm_e⟩ => by
              c0_hsteps!
              exact hL ((1#32 <<< k).toNat - (p + 1#32).toNat) (p + 1#32, ()) m73
                (by rw [hp1]; omega) ⟨scr_e, hsc_e, by rw [hp1]; omega, rfl, hout_e, hm_e⟩)
            ?_
          intro _ hJ73
          c0_hsteps_nogrp
          c0_hsplit
          · have hnm_b : ((fullNmask >>> p.toNat) &&& 1#32) ≠ 0#32 := by
              rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
            have hnm_bit := m7_bit_test_imp fullNmask p hp16 hnm_b
            have h1076_lt : ((1076#32 + p).setWidth 64).toNat < scr_d.length := by
              rw [hsc_d, zext32_toNat]; c0_bound
            have h1076_eq : ((1076#32 + p).setWidth 64).toNat = 1076 + p.toNat := by
              rw [zext32_toNat]; c0_bound
            let idx := scr_d[((1076#32 + p).setWidth 64).toNat]'h1076_lt
            have hidx_orig : idx = scr_in[1076 + p.toNat]?.getD 0#32 := by
              have hlt : 1076 + p.toNat < scr_d.length := by omega
              have hg := hout_d (1076 + p.toNat) (by omega) (Or.inr (by omega))
              rw [List.getElem?_eq_getElem hlt] at hg
              rw [← hg, Option.getD_some]
              exact getElem_congr h1076_eq h1076_lt hlt
            have hidx_lt : idx.toNat < 512 := by
              have := hnm_ok p.toNat hp16 hnm_bit; rw [← hidx_orig] at this; exact this
            c0_hsteps_nogrp
            refine m7_setMaskBit_wp Γ c s0 scr_d R 1040#32 idx m72 Q X _
              hsc_d (by omega) (by decide) (by decide) hidx_lt hm_d ?_
            intro scr_e hsc_e hout_e me hm_e
            have hout_e' : ∀ i < c.scratch_cap, (i < 1024 ∨ 1056 ≤ i) →
                scr_e[i]? = scr_in[i]? :=
              fun i hi hor => (hout_e i hi hor).trans (hout_d i hi hor)
            c0_hsteps!
            exact hJ73 () me ⟨scr_e, hsc_e, hout_e', hm_e⟩
          · c0_hsteps!
            exact hJ73 () m72 ⟨scr_d, hsc_d, hout_d, hm_d⟩)
        ?_
      intro _ hJ72
      c0_hsteps_nogrp
      c0_hsplit
      · have hpm_b : ((fullPmask >>> p.toNat) &&& 1#32) ≠ 0#32 := by
          rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
        have hpm_bit := m7_bit_test_imp fullPmask p hp16 hpm_b
        have h1060_lt : ((1060#32 + p).setWidth 64).toNat < scr_c.length := by
          rw [hsc_c, zext32_toNat]; c0_bound
        have h1060_eq : ((1060#32 + p).setWidth 64).toNat = 1060 + p.toNat := by
          rw [zext32_toNat]; c0_bound
        let idx := scr_c[((1060#32 + p).setWidth 64).toNat]'h1060_lt
        have hidx_orig : idx = scr_in[1060 + p.toNat]?.getD 0#32 := by
          have hlt : 1060 + p.toNat < scr_c.length := by omega
          have hg := hout_c (1060 + p.toNat) (by omega) (Or.inr (by omega))
          rw [List.getElem?_eq_getElem hlt] at hg
          rw [← hg, Option.getD_some]
          exact getElem_congr h1060_eq h1060_lt hlt
        have hidx_lt : idx.toNat < 512 := by
          have := hpm_ok p.toNat hp16 hpm_bit; rw [← hidx_orig] at this; exact this
        c0_hsteps_nogrp
        refine m7_setMaskBit_wp Γ c s0 scr_c R 1024#32 idx mc Q X _
          hsc_c (by omega) (by decide) (by decide) hidx_lt hm_c ?_
        intro scr_d hsc_d hout_d md hm_d
        have hout_d' : ∀ i < c.scratch_cap, (i < 1024 ∨ 1056 ≤ i) →
            scr_d[i]? = scr_in[i]? :=
          fun i hi hor => (hout_d i hi hor).trans (hout_c i hi hor)
        c0_hsteps!
        exact hJ72 () md ⟨scr_d, hsc_d, hout_d', hm_d⟩
      · c0_hsteps!
        exact hJ72 () mc ⟨scr_c, hsc_c, hout_c, hm_c⟩
    · have h1056' : 1056 < scr_c.length := by rw [hsc_c]; omega
      have h1057' : 1057 < scr_c.length := by rw [hsc_c]; omega
      c0_hsteps!
      refine hQ true ((scr_c.set (1056#64).toNat 1#32).set (1057#64).toNat 0#32) m ?_ ?_ hm
      · simp [hsc_c]
      · intro idx hidx hor
        rw [List.getElem?_set_ne (by rw [show (1057#64).toNat = 1057 from rfl]; omega),
          List.getElem?_set_ne (by rw [show (1056#64).toNat = 1056 from rfl]; omega)]
        exact (hout_c idx hidx (by rcases hor with h | h <;> omega)).trans
          (hout_in idx hidx hor)
  · intro L hL; c0_hsteps!
    exact hL (1#32 <<< k).toNat (0#32, ()) m_in
      ⟨scr_in, hsc_in, Nat.zero_le _, by simp, fun _ _ _ => rfl, hm_in⟩

theorem m7_xor_neg_scan_wp (Γ : Env) (c : FullCfg) (F0 : CNF Nat)
    (F_cur : List (List Nat)) (s : FullState) (lmc : List (BitVec 8))
    (scrp' : List (BitVec 32)) (R : Mem 64 → Prop)
    (nn nl k_b full_nm : BitVec 32) (mp' : Mem 64) (Q : Post [.bool]) (X : XPost)
    (onDone : Val i32 → Expr Val Cont [.bool])
    (hXorPat : Γ.Has "full_bve_xor_pat_m7" fullBveXorPatM7Spec)
    (hdw0 : FullDenseInvW c F0 F_cur s)
    (hlmc_len : lmc.length = 2 * c.max_vars)
    (hscrp'_len : scrp'.length = c.scratch_cap)
    (hnn512 : nn.toNat ≤ 512) (hsc1096 : 1096 ≤ c.scratch_cap)
    (hk1 : 1 ≤ k_b.toNat) (hk4 : k_b.toNat ≤ 4)
    (hn_ok : ∀ j < nn.toNat, FullBveEntryOkW F_cur s nl.toNat
      (s.scratch.scratch_buf[512 + j]?.getD 0#32))
    (hscr_512 : ∀ j < nn.toNat, scrp'[512 + j]? = s.scratch.scratch_buf[512 + j]?)
    (hmp' : (FullMem c (m7XorState s lmc scrp') ⋆ R) mp')
    (honDone : ∀ (nmask : BitVec 32) (scrn : List (BitVec 32)) (mn : Mem 64),
      scrn.length = c.scratch_cap →
      (∀ idx < c.scratch_cap, (idx < 1076 ∨ 1092 ≤ idx) → scrn[idx]? = scrp'[idx]?) →
      XorMaskEntriesOk scrn 1076 nn.toNat nmask →
      (FullMem c (m7XorState s lmc scrn) ⋆ R) mn →
      wp Γ Q X (onDone nmask) mn) :
    wp Γ Q X (m7XorNegScanExpr c.hdr c.pScratchBuf nn nl k_b full_nm onDone) mp' := by
  have hlen0 := hdw0.1
  have hmx := c.hmaxv; have hsc := c.hscr; unfold dimacsBound at hmx hsc
  have hcv_le := hlen0.core_ok.cur_vars_le
  have hscr_len0 := hlen0.scratch_ok.scratch_buf_len
  unfold m7XorNegScanExpr
  refine wp_loop_group (ts := [i32, i32])
    (fun remn (nmask, j2, ()) mn =>
      ∃ scrn : List (BitVec 32),
        j2.toNat ≤ nn.toNat ∧ remn = nn.toNat - j2.toNat ∧ scrn.length = c.scratch_cap ∧
        (∀ idx < c.scratch_cap, (idx < 1076 ∨ 1092 ≤ idx) → scrn[idx]? = scrp'[idx]?) ∧
        XorMaskEntriesOk scrn 1076 nn.toNat nmask ∧
        (FullMem c (m7XorState s lmc scrn) ⋆ R) mn)
    ?_ ?_
  · rintro Ln remn ⟨nmask, j2, ⟨⟩⟩ mn hLn ⟨scrn, hj2_le, rfl, hscrn_len, hscrn_o, hnm_ok, hmn⟩
    c0_hsplit
    · have hj2_lt : j2.toNat < nn.toNat := hc
      c0_hsplit
      · have hj2_sc : (512#64 + j2.setWidth 64).toNat < scrn.length := by
          rw [hscrn_len]; c0_bound
        let c2j := scrn[(512#64 + j2.setWidth 64).toNat]'hj2_sc
        have hc2j_orig :
            c2j = s.scratch.scratch_buf[512 + j2.toNat]'(by rw [hscr_len0]; omega) := by
          have := (hscrn_o (512 + j2.toNat) (by omega) (Or.inl (by omega))).trans
            (hscr_512 j2.toNat hj2_lt)
          rw [List.getElem?_eq_getElem (by rw [hscrn_len]; omega),
            List.getElem?_eq_getElem (by rw [hscr_len0]; omega)] at this
          exact (getElem_congr (by c0_bound)
            (by rw [hscrn_len]; c0_bound) (by rw [hscrn_len]; omega)).trans
            (Option.some.inj this)
        have hj21 : (j2 + 1#32).toNat = j2.toNat + 1 := by c0_bound
        c0_hsteps_nogrp
        refine wp_join_state (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
          (fun nm' mn' =>
            ∃ scr_k : List (BitVec 32),
              scr_k.length = c.scratch_cap ∧
              (∀ idx < c.scratch_cap, (idx < 1076 ∨ 1092 ≤ idx) →
                scr_k[idx]? = scrp'[idx]?) ∧
              XorMaskEntriesOk scr_k 1076 nn.toNat nm' ∧
              (FullMem c (m7XorState s lmc scr_k) ⋆ R) mn')
          (fun _ nm' mn' ⟨scr_k, h1, h2, h3, h4⟩ => by
            c0_hsteps!
            exact hLn (nn.toNat - (j2 + 1#32).toNat) (nm', j2 + 1#32, ()) mn' (by omega)
              ⟨scr_k, by omega, rfl, h1, h2, h3, h4⟩)
          (fun Jnm hJnm => by
            c0_hsplit
            · have hc2j_and : c2j &&& 0x80000000#32 = 0#32 := by
                have hidx_eq : (512#64 + j2.setWidth 64).toNat =
                    (BitVec.toNat 512#32 + j2.toNat) % 2 ^ 32 := by c0_bound
                dsimp only [c2j]
                rw [getElem_congr hidx_eq
                  (by rw [hscrn_len]; c0_bound) (by rw [hscrn_len]; omega)]
                exact hc
              have hent_j2 := hn_ok j2.toNat hj2_lt
              rw [List.getElem?_eq_getElem (by rw [hscr_len0]; omega),
                Option.getD_some, ← hc2j_orig] at hent_j2
              unfold FullBveEntryOkW at hent_j2
              rw [ite_eq_right fun h => h hc2j_and] at hent_j2
              have ⟨hlen_n, hw_n⟩ := lengths_witness_lm_scr hdw0 hlmc_len hscrn_len
              have hc2j_eq (hpf) :
                  scrn[(BitVec.setWidth 64 ((512 : BitVec 32) + j2)).toNat]'hpf = c2j :=
                getElem_congr (by c0_bound) hpf hj2_sc
              c0_hsteps_nogrp
              gates_call hXorPat
              refine fullBveXorPatM7Spec_intro rfl hlen_n hw_n
                (by dsimp only [m7XorState, Arg.var]; rw [hc2j_eq _]; exact hent_j2.1)
                (by dsimp only [m7XorState, Arg.var]; rw [hc2j_eq _]; exact hent_j2.2)
                hk1 hk4 hmn ?_
              intro pat hpat
              c0_hsteps_nogrp
              refine wp_join_state (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
                (fun nm' mn' =>
                  ∃ scr_k : List (BitVec 32),
                    scr_k.length = c.scratch_cap ∧
                    (∀ idx < c.scratch_cap, (idx < 1076 ∨ 1092 ≤ idx) →
                      scr_k[idx]? = scrp'[idx]?) ∧
                    XorMaskEntriesOk scr_k 1076 nn.toNat nm' ∧
                    (FullMem c (m7XorState s lmc scr_k) ⋆ R) mn')
                (fun _ nm' mn' ⟨scr_k, h1, h2, h3, h4⟩ => by
                  c0_hsteps!; exact hJnm nm' mn' ⟨scr_k, h1, h2, h3, h4⟩)
                (fun Jp2 hJp2 => by
                  c0_hsplit
                  · have hpat_lt : pat.toNat < 16 := hc
                    c0_hsplit
                    · c0_hsplit
                      · have hst : (1076#64 + pat.setWidth 64).toNat < scrn.length := by
                          rw [hscrn_len]; c0_bound
                        have hnm_s := xorMaskEntriesOk_set hnm_ok (by omega) hpat_lt hj2_lt
                        have hscr_o_s : ∀ idx < c.scratch_cap, (idx < 1076 ∨ 1092 ≤ idx) →
                            (scrn.set (1076 + pat.toNat) j2)[idx]? = scrp'[idx]? :=
                          fun idx hi hor => by
                            rw [List.getElem?_set_ne (by omega)]
                            exact hscrn_o idx hi hor
                        c0_hsteps!
                        dsimp only [m7XorState] at hm ⊢
                        rw [show scrn.set _ j2 = scrn.set (1076 + pat.toNat) j2 from
                          congrArg (fun k => scrn.set k j2) (by c0_bound)] at hm
                        have hsh : (1 : BitVec 32) <<< (pat.toNat % 32) = 1#32 <<< pat := by
                          change 1#32 <<< (pat.toNat % 32) = 1#32 <<< pat.toNat
                          rw [Nat.mod_eq_of_lt (by omega)]
                        rw [hsh]
                        exact hJp2 (nmask ||| (1#32 <<< pat)) _
                          ⟨scrn.set (1076 + pat.toNat) j2,
                            by rw [List.length_set, hscrn_len], hscr_o_s, hnm_s, hm⟩
                      · c0_hsteps!; exact hJp2 nmask mn ⟨scrn, hscrn_len, hscrn_o, hnm_ok, hmn⟩
                    · c0_hsteps!; exact hJp2 nmask mn ⟨scrn, hscrn_len, hscrn_o, hnm_ok, hmn⟩
                  · c0_hsteps!; exact hJp2 nmask mn ⟨scrn, hscrn_len, hscrn_o, hnm_ok, hmn⟩)
            · c0_hsteps!; exact hJnm nmask mn ⟨scrn, hscrn_len, hscrn_o, hnm_ok, hmn⟩)
      · c0_hsteps!; dsimp only; exact honDone nmask scrn mn hscrn_len hscrn_o hnm_ok hmn
    · c0_hsteps!; dsimp only; exact honDone nmask scrn mn hscrn_len hscrn_o hnm_ok hmn
  · intro Ln hLn; c0_hsteps!
    exact hLn nn.toNat (0#32, 0#32, ()) mp'
      ⟨scrp', Nat.zero_le _, by simp, hscrp'_len, fun _ _ _ => rfl,
        xorMaskEntriesOk_zero _ _ _, hmp'⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Gates
