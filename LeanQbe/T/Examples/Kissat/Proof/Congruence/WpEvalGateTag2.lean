/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpEvalGate0

/-!
# Congruence Gate Re-Evaluation ITE-Gate WP Proof (`WpEvalGateTag2`)

Proves `ev_tag2_wp` for `evTag2Expr` (ITE gate simplification, constant/branch/polarity
folding, ITE-to-XOR and 8-case ITE-to-AND2 normalization, and hash-gate preparation
in `full_cong_eval_gate`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open Std Std.Sat
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics

attribute [local c0_load] ev_c0_load_full_tmp0 ev_c0_load_full_tmp1 ev_c0_load_full_tmp2
attribute [local c0_store] ev_c0_store_full_tmp0 ev_c0_store_full_tmp1 ev_c0_store_full_tmp2

local macro "ev_u" : tactic =>
  `(tactic| try dsimp only [evL2, evCmp32, evCmp64, evLd32, evLdK32, evLd8, evSgn0])

local macro "ev_steps" : tactic =>
  `(tactic| (ev_u; c0_hsteps!))

local macro "ev_steps_ng" : tactic =>
  `(tactic| (ev_u; c0_hsteps_nogrp))

local macro "ev_split" : tactic =>
  `(tactic| (ev_u; c0_hsplit))

/-! ## 1. Pure ITE Semantic & Normalization Lemmas -/

private theorem t2_ite_8cases_ok {F : CNF Nat} {vals : List (BitVec 8)} {cv : Nat}
    (hw_dom : ∀ l < 2 * cv,
      vals[l]?.getD 0#8 = 0#8 ∨ vals[l]?.getD 0#8 = 1#8 ∨ vals[l]?.getD 0#8 = 0xFF#8)
    (heval_1 : ∀ l < 2 * cv, vals[l]?.getD 0#8 = 1#8 → ∀ α, F.Sat α → evalLitVal α l = true)
    (heval_ff : ∀ l < 2 * cv, vals[l]?.getD 0#8 = 0xFF#8 → ∀ α, F.Sat α → evalLitVal α l = false)
    {lhs c t e : BitVec 32} (ht : t.toNat < 2 * cv) (he : e.toNat < 2 * cv)
    (hite : ∀ α, F.Sat α → evalLitVal α lhs.toNat =
      if evalLitVal α c.toNat then evalLitVal α t.toNat else evalLitVal α e.toNat) :
    ((0#32 : BitVec 32).slt ((vals[t.toNat]?.getD 0#8).signExtend 32) = true → ∀ α, F.Sat α →
      evalLitVal α (lhs ^^^ 1#32).toNat =
        (evalLitVal α (c ^^^ 1#32).toNat && evalLitVal α (e ^^^ 1#32).toNat)) ∧
    (((vals[t.toNat]?.getD 0#8).signExtend 32).slt 0#32 = true → ∀ α, F.Sat α →
      evalLitVal α lhs.toNat = (evalLitVal α (c ^^^ 1#32).toNat && evalLitVal α e.toNat)) ∧
    ((0#32 : BitVec 32).slt ((vals[e.toNat]?.getD 0#8).signExtend 32) = true → ∀ α, F.Sat α →
      evalLitVal α (lhs ^^^ 1#32).toNat =
        (evalLitVal α c.toNat && evalLitVal α (t ^^^ 1#32).toNat)) ∧
    (((vals[e.toNat]?.getD 0#8).signExtend 32).slt 0#32 = true → ∀ α, F.Sat α →
      evalLitVal α lhs.toNat = (evalLitVal α c.toNat && evalLitVal α t.toNat)) ∧
    (c = t → ∀ α, F.Sat α → evalLitVal α (lhs ^^^ 1#32).toNat =
      (evalLitVal α (c ^^^ 1#32).toNat && evalLitVal α (e ^^^ 1#32).toNat)) ∧
    (c = t ^^^ 1#32 → ∀ α, F.Sat α →
      evalLitVal α lhs.toNat = (evalLitVal α (c ^^^ 1#32).toNat && evalLitVal α e.toNat)) ∧
    (c = e ^^^ 1#32 → ∀ α, F.Sat α → evalLitVal α (lhs ^^^ 1#32).toNat =
      (evalLitVal α c.toNat && evalLitVal α (t ^^^ 1#32).toNat)) ∧
    (c = e → ∀ α, F.Sat α →
      evalLitVal α lhs.toNat = (evalLitVal α c.toNat && evalLitVal α t.toNat)) := by
  refine ⟨fun h1 α hα => ?_, fun h2 α hα => ?_, fun h3 α hα => ?_, fun h4 α hα => ?_,
    fun h5 α hα => ?_, fun h6 α hα => ?_, fun h7 α hα => ?_, fun h8 α hα => ?_⟩
  · have ht1 := heval_1 t.toNat ht (bv8_eq1_of_signExtend32_sgt0 (hw_dom t.toNat ht) h1) α hα
    rw [bv32_xor1_eq_litNeg, bv32_xor1_eq_litNeg, bv32_xor1_eq_litNeg, evalLitVal_litNeg,
      evalLitVal_litNeg, evalLitVal_litNeg, hite α hα, ht1]
    cases evalLitVal α c.toNat <;> cases evalLitVal α e.toNat <;> rfl
  · have htf : vals[t.toNat]?.getD 0#8 = 0xFF#8 := by
      rcases hw_dom t.toNat ht with hd | hd | hd <;> rw [hd] at h2 ⊢ <;>
        first | rfl | exact absurd h2 (by decide)
    have htv := heval_ff t.toNat ht htf α hα
    rw [bv32_xor1_eq_litNeg, evalLitVal_litNeg, hite α hα, htv]
    cases evalLitVal α c.toNat <;> cases evalLitVal α e.toNat <;> rfl
  · have he1 := heval_1 e.toNat he (bv8_eq1_of_signExtend32_sgt0 (hw_dom e.toNat he) h3) α hα
    rw [bv32_xor1_eq_litNeg, bv32_xor1_eq_litNeg, evalLitVal_litNeg, evalLitVal_litNeg,
      hite α hα, he1]
    cases evalLitVal α c.toNat <;> cases evalLitVal α t.toNat <;> rfl
  · have hef : vals[e.toNat]?.getD 0#8 = 0xFF#8 := by
      rcases hw_dom e.toNat he with hd | hd | hd <;> rw [hd] at h4 ⊢ <;>
        first | rfl | exact absurd h4 (by decide)
    have hev := heval_ff e.toNat he hef α hα
    rw [hite α hα, hev]
    cases evalLitVal α c.toNat <;> cases evalLitVal α t.toNat <;> rfl
  · rw [bv32_xor1_eq_litNeg, bv32_xor1_eq_litNeg, bv32_xor1_eq_litNeg, evalLitVal_litNeg,
      evalLitVal_litNeg, evalLitVal_litNeg, hite α hα, ← h5]
    cases evalLitVal α c.toNat <;> cases evalLitVal α e.toNat <;> rfl
  · rw [bv32_xor1_eq_litNeg, evalLitVal_litNeg, hite α hα]
    have hct : evalLitVal α t.toNat = !(evalLitVal α c.toNat) := by
      have : t = c ^^^ 1#32 := by rw [h6, BitVec.xor_assoc]; simp
      rw [this, bv32_xor1_eq_litNeg, evalLitVal_litNeg]
    rw [hct]; cases evalLitVal α c.toNat <;> cases evalLitVal α e.toNat <;> rfl
  · rw [bv32_xor1_eq_litNeg, bv32_xor1_eq_litNeg, evalLitVal_litNeg, evalLitVal_litNeg, hite α hα]
    have hce : evalLitVal α e.toNat = !(evalLitVal α c.toNat) := by
      have : e = c ^^^ 1#32 := by rw [h7, BitVec.xor_assoc]; simp
      rw [this, bv32_xor1_eq_litNeg, evalLitVal_litNeg]
    rw [hce]; cases evalLitVal α c.toNat <;> cases evalLitVal α t.toNat <;> rfl
  · rw [hite α hα, ← h8]; cases evalLitVal α c.toNat <;> cases evalLitVal α t.toNat <;> rfl

private theorem t2_ite_xor_eval (lhs c t e : BitVec 32) (hte : t = e ^^^ 1#32)
    (F : CNF Nat)
    (hite : ∀ α, F.Sat α → evalLitVal α lhs.toNat =
      if evalLitVal α c.toNat then evalLitVal α t.toNat else evalLitVal α e.toNat) :
    ((1#32 ^^^ c ^^^ t) &&& 1#32 = 0#32 ∨ (1#32 ^^^ c ^^^ t) &&& 1#32 = 1#32) ∧
    ∀ α, F.Sat α →
      evalLitVal α (lhs ^^^ ((1#32 ^^^ c ^^^ t) &&& 1#32)).toNat =
        (evalLitVal α (c &&& ~~~1#32).toNat != evalLitVal α (t &&& ~~~1#32).toNat) := by
  refine ⟨ev_bv32_and1_eq01 _, fun α hα => ?_⟩
  have he_eval : evalLitVal α e.toNat = !(evalLitVal α t.toNat) := by
    have : e = t ^^^ 1#32 := by rw [hte, BitVec.xor_assoc]; simp
    rw [this, bv32_xor1_eq_litNeg, evalLitVal_litNeg]
  have h1 : evalLitVal α lhs.toNat = !(evalLitVal α c.toNat != evalLitVal α t.toNat) := by
    rw [hite α hα, he_eval]
    cases evalLitVal α c.toNat <;> cases evalLitVal α t.toNat <;> rfl
  have hbit : ((1#32 ^^^ c ^^^ t) &&& 1#32 = 1#32) ↔
      ((c &&& 1#32 = 1#32) = (t &&& 1#32 = 1#32)) := by
    have hdist : ∀ a b : BitVec 32, (a ^^^ b) &&& 1#32 = (a &&& 1#32) ^^^ (b &&& 1#32) := by
      intro a b; apply BitVec.eq_of_toNat_eq; apply Nat.eq_of_testBit_eq; intro i
      rw [BitVec.toNat_and, BitVec.toNat_xor, BitVec.toNat_xor, BitVec.toNat_and,
        BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl]
      simp only [Nat.testBit_and, Nat.testBit_xor]
      cases (1 : Nat).testBit i <;> cases a.toNat.testBit i <;> cases b.toNat.testBit i <;> rfl
    rcases ev_bv32_and1_eq01 c with hc0 | hc1 <;> rcases ev_bv32_and1_eq01 t with ht0 | ht1
    · have hxor : (1#32 ^^^ c ^^^ t) &&& 1#32 = 1#32 := by
        rw [hdist, hdist, hc0, ht0]; decide
      simp [hxor, hc0, ht0]
    · have hxor : (1#32 ^^^ c ^^^ t) &&& 1#32 = 0#32 := by
        rw [hdist, hdist, hc0, ht1]; decide
      simp [hxor, hc0, ht1]
    · have hxor : (1#32 ^^^ c ^^^ t) &&& 1#32 = 0#32 := by
        rw [hdist, hdist, hc1, ht0]; decide
      simp [hxor, hc1, ht0]
    · have hxor : (1#32 ^^^ c ^^^ t) &&& 1#32 = 1#32 := by
        rw [hdist, hdist, hc1, ht1]; decide
      simp [hxor, hc1, ht1]
  have hlhs_f : evalLitVal α (lhs ^^^ ((1#32 ^^^ c ^^^ t) &&& 1#32)).toNat =
      (evalLitVal α lhs.toNat != decide ((1#32 ^^^ c ^^^ t) &&& 1#32 = 1#32)) := by
    rcases ev_bv32_and1_eq01 (1#32 ^^^ c ^^^ t) with h0 | h1'
    · simp [h0]
    · rw [h1', bv32_xor1_eq_litNeg, evalLitVal_litNeg]; simp
  rw [hlhs_f, h1, ev_xor_bit0_eval, ev_xor_bit0_eval]
  have hd : decide ((1#32 ^^^ c ^^^ t) &&& 1#32 = 1#32) =
      !(decide (c &&& 1#32 = 1#32) != decide (t &&& 1#32 = 1#32)) := by
    cases hdc : decide (c &&& 1#32 = 1#32) <;> cases hdt : decide (t &&& 1#32 = 1#32) <;>
      simp_all
  rw [hd]
  cases evalLitVal α c.toNat <;> cases evalLitVal α t.toNat <;>
    cases decide (c &&& 1#32 = 1#32) <;> cases decide (t &&& 1#32 = 1#32) <;> rfl

private theorem t2_bv32_and_not1_lt {x : BitVec 32} {n : Nat} (hx : x.toNat < n) :
    (x &&& ~~~1#32).toNat < n := by
  rw [m6_bv32_and_not1_toNat]; omega

private theorem t2_bv8_eqff_of_sext_slt0 {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hslt : (v.signExtend 32).slt 0#32 = true) :
    v = 0xFF#8 := by
  rcases hdom with rfl | rfl | rfl
  · cases hslt
  · cases hslt
  · rfl

private theorem t2_and2_unit_neg_of_eq {F : CNF Nat} {lhs a0 a1 : BitVec 32}
    (hand : ∀ α, F.Sat α →
      evalLitVal α lhs.toNat = (evalLitVal α a0.toNat && evalLitVal α a1.toNat))
    (hcase : a0 = a1 ^^^ 1#32 ∨ a0 = lhs ^^^ 1#32 ∨ a1 = lhs ^^^ 1#32) :
    F.EntailsClause (cnfClause [(lhs ^^^ 1#32).toNat]) := by
  refine ev_entails_of_eval fun α hα => ?_
  rw [bv32_xor1_eq_litNeg, evalLitVal_litNeg]
  have h1 := hand α hα
  rcases hcase with rfl | rfl | rfl
  · rw [bv32_xor1_eq_litNeg, evalLitVal_litNeg] at h1
    cases h : evalLitVal α a1.toNat <;> simp [h] at h1 <;> (rw [h1]; rfl)
  · rw [bv32_xor1_eq_litNeg, evalLitVal_litNeg] at h1
    cases hl : evalLitVal α lhs.toNat
    · rfl
    · simp [hl] at h1
  · rw [bv32_xor1_eq_litNeg, evalLitVal_litNeg] at h1
    cases hl : evalLitVal α lhs.toNat
    · rfl
    · cases ha : evalLitVal α a0.toNat <;> simp [hl, ha] at h1

private theorem t2_take_two {α : Type} (xs : List α) (h0 : 0 < xs.length) (h1 : 1 < xs.length) :
    xs.take 2 = [xs[0]'h0, xs[1]'h1] := by
  rcases xs with _ | ⟨a, _ | ⟨b, cs⟩⟩
  · cases h0
  · simp at h1
  · rfl

/-! ## 2. Main ITE-Gate WP Theorem (`ev_tag2_wp`) -/

private abbrev T2Out (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cv0 : Nat) (fl0 : BitVec 64) (ar0 : List (BitVec 32))
    (arl0 g_len ctrl_off ht_off ht_sz : Nat) (scr0 scr_in : List (BitVec 32))
    (gtype : BitVec 32) (R : Mem 64 → Prop) :
    Tup Val [i32, i32, i32, .bool, .bool] → Mem 64 → Prop :=
  fun (lhs', htag', har', nh', _, ()) mj => ∃ stj : FullState,
    EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in stj ∧
    (nh' = true → EvHashGateOk maxA F_cur cv0 gtype htag' har' lhs' stj.core.tmp) ∧
    (FullMem c stj ⋆ R) mj

private abbrev T2Mid (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cv0 : Nat) (fl0 : BitVec 64) (ar0 : List (BitVec 32))
    (arl0 g_len ctrl_off ht_off ht_sz : Nat) (scr0 scr_in : List (BitVec 32))
    (gtype : BitVec 32) (R : Mem 64 → Prop) :
    Tup Val [i32, i32, i32, .bool, .bool, i32, i32, i32] → Mem 64 → Prop :=
  fun (lhs', htag', har', nh', ch', _, _, _, ()) mj =>
    T2Out maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in gtype R
      (lhs', htag', har', nh', ch', ()) mj

private abbrev T2And2P (cv0 : Nat) (F_cur : List (List Nat)) (lhs : BitVec 32) (m0 : Mem 64) :
    Tup Val [i32, .bool, i32, i32] → Mem 64 → Prop :=
  fun x m' => m0 = m' ∧ (x.2.1 = false → x.1 = lhs) ∧ (x.2.1 = true →
    x.1.toNat < 2 * cv0 ∧ x.2.2.1.toNat < 2 * cv0 ∧ x.2.2.2.1.toNat < 2 * cv0 ∧
    ∀ α, (cnfOfClauses F_cur).Sat α → evalLitVal α x.1.toNat =
      (evalLitVal α x.2.2.1.toNat && evalLitVal α x.2.2.2.1.toNat))

private def t2And2NormExpr {V : Ty → Type} {L : List Ty → Type}
    (h ctrl_off ld5 ld7 : V i64) (next_ep p19 p21 ld47 ld51 ld55 p83 p85 p86 : V i32)
    (p84 : V .bool) (J80 : L [i32, i32, i32, .bool, .bool, i32, i32, i32]) : Expr V L [i64] :=
  .group (sig := [[i32, i32, i32, .bool, .bool, i32, i32, i32]]) (fun (_J87, ()) => .cons (fun
    (p88, (p89, (p90, (p91, (p92, (p93, (p94, (p95, ())))))))) =>
  .jump J80 (.var p88, (.var p89, (.var p90, (.var p91, (.var p92, (.var p93, (.var p94, (.var
    p95, ())))))))) ) .nil) fun (J87, ()) => .jnz (.var p84) (
  .group (sig := [[i32, i32, .bool, .bool]]) (fun (_J88, ()) => .cons (fun (p89, (p90, (p91,
    (p92, ())))) =>
  .jump J87 (.var p83, (.var p89, (.var p90, (.var p91, (.var p92, (.var ld47, (.var ld51, (.var
    ld55, ())))))))) ) .nil) fun (J88, ()) => evCmp32 .eq (.var p85) (.var p86) fun v89 =>
  .jnz (.var v89) ( evEquivEnq2Expr h ctrl_off p83 p85 next_ep (.imm false) (fun p93 =>
  .jump J88 (.var p21, (.var p19, (.imm false, (.var p93, ())))) ) ) (
  .group (sig := [[i32, i32, .bool, .bool]]) (fun (_J90, ()) => .cons (fun (p91, (p92, (p93,
    (p94, ())))) => .jump J88 (.var p91, (.var p92, (.var p93, (.var p94, ()))))
  ) .nil) fun (J90, ()) => .group (sig := [[]]) (fun (_J91, ()) => .cons (fun () =>
  evL2 (.xor i32) (.var p83) (.imm 1) fun v92 => evUnitExpr h v92 next_ep (.imm false) (fun p96 =>
  .jump J90 (.var p21, (.var p19, (.imm false, (.var p96, ())))) ) ) .nil) fun (J91, ()) =>
  evL2 (.xor i32) (.var p86) (.imm 1) fun v92 => evCmp32 .eq (.var p85) (.var v92) fun v93 =>
  .jnz (.var v93) ( .jump J91 () ) ( evL2 (.xor i32) (.var p83) (.imm 1) fun v94 =>
  evCmp32 .eq (.var p85) (.var v94) fun v95 => .jnz (.var v95) ( .jump J91 () ) (
  evL2 (.xor i32) (.var p83) (.imm 1) fun v96 => evCmp32 .eq (.var p86) (.var v96) fun v97 =>
  .jnz (.var v97) ( .jump J91 () ) (
  .group (sig := [[i32, i32, .bool, .bool]]) (fun (_J98, ()) => .cons (fun (p99, (p100, (p101,
    (p102, ())))) => .jump J90 (.var p99, (.var p100, (.var p101, (.var p102, ()))))
  ) .nil) fun (J98, ()) => evLd8 ld7 p83 fun ld101 => evSgn0 .sgt ld101 fun v105 =>
  .jnz (.var v105) ( evUnitExpr h p85 next_ep (.imm false) (fun p109 =>
  evUnitExpr h p86 next_ep (.var p109) (fun p113 =>
  .jump J98 (.var p21, (.var p19, (.imm false, (.var p113, ())))) ) ) ) (
  .let_ ⟨.sext 32 64, (.imm 0, ())⟩ fun (v106, ()) =>
  evL2 (.mul i64) (.var v106) (.imm 4) fun v107 =>
  evL2 (.add i64) (.var ld5) (.var v107) fun v108 =>
  .group (sig := [[i32]]) (fun (_J109, ()) => .cons (fun (p110, ()) =>
  .store (t := i32) (.var p110) (.var v108) ( .let_ ⟨.sext 32 64, (.imm 1, ())⟩ fun (v111, ()) =>
  evL2 (.mul i64) (.var v111) (.imm 4) fun v112 =>
  evL2 (.add i64) (.var ld5) (.var v112) fun v113 =>
  .group (sig := [[i32]]) (fun (_J114, ()) => .cons (fun (p115, ()) =>
  .store (t := i32) (.var p115) (.var v113) (
  .jump J98 (.imm 0, (.imm 2, (.imm true, (.imm false, ()))))) ) .nil) fun (J114, ()) =>
  evCmp32 .ult (.var p85) (.var p86) fun v115 => .jnz (.var v115) ( .jump J114 (.var p86, ()) ) (
  .jump J114 (.var p85, ()) )) ) .nil) fun (J109, ()) =>
  evCmp32 .ult (.var p85) (.var p86) fun v110 => .jnz (.var v110) ( .jump J109 (.var p85, ()) ) (
  .jump J109 (.var p86, ()) ) ) ) ) ) ) ) (
  .group (sig := [[i32, i32, i32]]) (fun (_J88, ()) => .cons (fun (p89, (p90, (p91, ()))) =>
  .group (sig := [[i32, i32, i32]]) (fun (_J92, ()) => .cons (fun (p93, (p94, (p95, ()))) =>
  .let_ ⟨.sext 32 64, (.imm 0, ())⟩ fun (v96, ()) =>
  evL2 (.mul i64) (.var v96) (.imm 4) fun v97 => evL2 (.add i64) (.var ld5) (.var v97) fun v98 =>
  .store (t := i32) (.var p89) (.var v98) ( .let_ ⟨.sext 32 64, (.imm 1, ())⟩ fun (v99, ()) =>
  evL2 (.mul i64) (.var v99) (.imm 4) fun v100 =>
  evL2 (.add i64) (.var ld5) (.var v100) fun v101 => .store (t := i32) (.var p94) (.var v101) (
  .let_ ⟨.sext 32 64, (.imm 2, ())⟩ fun (v102, ()) =>
  evL2 (.mul i64) (.var v102) (.imm 4) fun v103 =>
  evL2 (.add i64) (.var ld5) (.var v103) fun v104 => .store (t := i32) (.var p95) (.var v104) (
  .jump J87 (.var p93, (.var p21, (.var p19, (.imm true, (.imm false, (.var p89, (.var p94, (.var
    p95, ()))))))))))) ) .nil) fun (J92, ()) => evL2 (.and i32) (.var p90) (.imm 1) fun v93 =>
  evCmp32 .ne (.var v93) (.imm 0) fun v94 => .jnz (.var v94) (
  evL2 (.xor i32) (.var p83) (.imm 1) fun v95 => evL2 (.xor i32) (.var p90) (.imm 1) fun v96 =>
  evL2 (.xor i32) (.var p91) (.imm 1) fun v97 => .jump J92 (.var v95, (.var v96, (.var v97, ())))
  ) ( .jump J92 (.var p83, (.var p90, (.var p91, ()))) ) ) .nil) fun (J88, ()) =>
  evL2 (.and i32) (.var ld47) (.imm 1) fun v89 => evCmp32 .ne (.var v89) (.imm 0) fun v90 =>
  .jnz (.var v90) ( evL2 (.xor i32) (.var ld47) (.imm 1) fun v91 =>
  .jump J88 (.var v91, (.var ld55, (.var ld51, ()))) ) (
  .jump J88 (.var ld47, (.var ld51, (.var ld55, ()))) ) )

private theorem ev_tag2_and2_norm_wp (Γ : Env)
    (hUnit : Γ.Has "full_cong_unit_fold" Spec.fullCongUnitFoldSpec)
    (hEquiv : Γ.Has "full_cong_equiv_fold" Spec.fullCongEquivFoldSpec)
    (hEnq : Γ.Has "full_cong_enq_var" Spec.fullCongEnqVarSpec)
    {maxA : Nat} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 : Nat}
    {fl0 : BitVec 64} {ar0 : List (BitVec 32)} {arl0 g_len ht_off ht_sz : Nat}
    {scr0 scr_in : List (BitVec 32)} {s0 : FullState} {m0 : Mem 64}
    {ctrl_off : BitVec 64} {next_ep arity gtype lhs lc lt le lhs' a0 a1 : BitVec 32}
    {is_and2 : Bool} {J80 : Cont [i32, i32, i32, .bool, .bool, i32, i32, i32]}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    (hg_ht : g_len ≤ ht_off) (hgtype : gtype = 2#32) (har3 : arity = 3#32)
    (har_cv : arity.toNat ≤ cv0) (har_max : arity.toNat ≤ maxA)
    (hlhs_lt : lhs.toNat < 2 * cv0) (hlc_lt : lc.toNat < 2 * cv0)
    (hlt_lt : lt.toNat < 2 * cv0) (hle_lt : le.toNat < 2 * cv0)
    (hite : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α → evalLitVal α lhs.toNat =
      if evalLitVal α lc.toNat then evalLitVal α lt.toNat else evalLitVal α le.toNat)
    (hlhs_f : is_and2 = false → lhs' = lhs)
    (hand2 : is_and2 = true → lhs'.toNat < 2 * cv0 ∧ a0.toNat < 2 * cv0 ∧ a1.toNat < 2 * cv0 ∧
      ∀ α, (cnfOfClauses F_cur).Sat α →
        evalLitVal α lhs'.toNat = (evalLitVal α a0.toNat && evalLitVal α a1.toNat))
    (hok0 : EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
      scr0 scr_in s0)
    (hm0 : (FullMem c s0 ⋆ R) m0)
    (hQ2 : ∀ s' m', EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
      scr0 scr_in s' → F0.Unsat → (FullMem c s' ⋆ R) m' → Q (2#64, ()) m')
    (hJ80 : ∀ xs mj,
      T2Mid maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz scr0 scr_in
        gtype R xs mj → J80 xs mj) :
    wp Γ Q X (t2And2NormExpr c.hdr ctrl_off c.pTmp c.pVals next_ep arity gtype lc lt le
      lhs' a0 a1 is_and2 J80) m0 := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hw0 := hok0.1.2.1; have hcl0 := hok0.1.2.2.2.2.2.1
  have hcv_eq := hok0.2.1; have hcv_le : cv0 ≤ c.max_vars := hcv_eq ▸ hok0.1.1.core_ok.cur_vars_le
  have htmpl0 := hok0.1.1.core_ok.tmp_len_arr; have hvlen0 := hok0.1.1.core_ok.vals_len
  have har3n : arity.toNat = 3 := by rw [har3]; decide
  have h3_tmp : 3 ≤ s0.core.tmp.length := by
    have := hok0.1.1.core_ok.cur_vars_le; omega
  have h0_tmp : 0 < s0.core.tmp.length := by omega
  have h1_tmp : 1 < s0.core.tmp.length := by omega
  have h2_tmp : 2 < s0.core.tmp.length := by omega
  have hdom_all : ∀ l < 2 * cv0, s0.core.vals[l]?.getD 0#8 = 0#8 ∨
      s0.core.vals[l]?.getD 0#8 = 1#8 ∨ s0.core.vals[l]?.getD 0#8 = 0xFF#8 := fun l hl =>
    hw0.vals_domain l (hcv_eq.symm ▸ hl)
  have hev1_all : ∀ l < 2 * cv0, s0.core.vals[l]?.getD 0#8 = 1#8 →
      ∀ α, (cnfOfClauses F_cur).Sat α → evalLitVal α l = true := fun l hl hv _ hα =>
    entails_eval_true (vals1_entails hw0 hcl0 (hcv_eq.symm ▸ hl) hv) hα
  unfold t2And2NormExpr; ev_steps_ng
  refine wp_join_group (T2Mid maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
      scr0 scr_in gtype R)
    (fun _ ⟨lhs'', htag', har', nh', ch', p6, p7, p8, ⟨⟩⟩ mj h => by
      ev_steps; exact hJ80 (lhs'', htag', har', nh', ch', p6, p7, p8, ()) mj h) ?_
  intro J87 hJ87; ev_split
  · obtain ⟨hlhs'_lt, ha0_lt, ha1_lt, hand_ev⟩ := hand2 hc
    clear hc; ev_steps_ng
    refine wp_join_group (ts := [i32, i32, .bool, .bool])
      (fun (htag', har', nh', ch', ()) mj => ∃ sj : FullState,
        EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
          scr0 scr_in sj ∧
        (nh' = true → EvHashGateOk maxA F_cur cv0 gtype htag' har' lhs' sj.core.tmp) ∧
        (FullMem c sj ⋆ R) mj)
      (fun _ ⟨htag', har', nh', ch', ⟨⟩⟩ mj ⟨sj, hokj, hgj, hmj⟩ => by
        ev_steps; exact hJ87 (lhs', htag', har', nh', ch', _, _, _, ()) mj ⟨sj, hokj, hgj, hmj⟩) ?_
    intro J88 hJ88; ev_split
    · have heq_a : a0 = a1 := hc
      have heqv : LitEquiv (cnfOfClauses F_cur) lhs'.toNat a0.toNat :=
        ev_litEquiv_of_eval fun α hα => by
          rw [hand_ev α hα, heq_a]; cases evalLitVal α a1.toNat <;> rfl
      clear hc; ev_steps
      refine ev_equiv_enq2_wp Γ hEquiv hEnq hg_ht rfl hok0 hlhs'_lt ha0_lt heqv hm0 hQ2
        fun ch' s' m' _ hok' hm' => by
          ev_steps; exact hJ88 (gtype, arity, false, ch', ()) m'
            ⟨s', hok', (fun h => False.elim (Bool.noConfusion h)), hm'⟩
    clear hc; ev_steps_ng
    refine wp_join_group (ts := [i32, i32, .bool, .bool])
      (fun (htag', har', nh', ch', ()) mj => ∃ sj : FullState,
        EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
          scr0 scr_in sj ∧
        (nh' = true → EvHashGateOk maxA F_cur cv0 gtype htag' har' lhs' sj.core.tmp) ∧
        (FullMem c sj ⋆ R) mj)
      (fun _ ⟨htag', har', nh', ch', ⟨⟩⟩ mj h => by
        ev_steps; exact hJ88 (htag', har', nh', ch', ()) mj h) ?_
    intro J90 hJ90; ev_steps_ng
    refine wp_join_group (ts := []) (fun () m91 => m0 = m91 ∧
        (a0 = a1 ^^^ 1#32 ∨ a0 = lhs' ^^^ 1#32 ∨ a1 = lhs' ^^^ 1#32))
      (fun _ ⟨⟩ m91 ⟨rfl, hcase⟩ => by
        have hent := t2_and2_unit_neg_of_eq hand_ev hcase
        ev_steps
        refine ev_unit_wp Γ hUnit hok0 (ev_bv32_xor1_lt_cv hlhs'_lt) hent hm0 hQ2
          fun ch' s' m' _ _ hok' hm' => by
            ev_steps; exact hJ90 (gtype, arity, false, ch', ()) m'
              ⟨s', hok', (fun h => False.elim (Bool.noConfusion h)), hm'⟩) ?_
    intro J91 hJ91; ev_split
    · exact hJ91 () m0 ⟨rfl, Or.inl hc⟩
    clear hc; ev_split
    · exact hJ91 () m0 ⟨rfl, Or.inr (Or.inl hc)⟩
    clear hc; ev_split
    · exact hJ91 () m0 ⟨rfl, Or.inr (Or.inr hc)⟩
    clear hc; ev_steps_ng
    refine wp_join_group (ts := [i32, i32, .bool, .bool])
      (fun (htag', har', nh', ch', ()) mj => ∃ sj : FullState,
        EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
          scr0 scr_in sj ∧
        (nh' = true → EvHashGateOk maxA F_cur cv0 gtype htag' har' lhs' sj.core.tmp) ∧
        (FullMem c sj ⋆ R) mj)
      (fun _ ⟨htag', har', nh', ch', ⟨⟩⟩ mj h => by
        ev_steps; exact hJ90 (htag', har', nh', ch', ()) mj h) ?_
    intro J98 hJ98
    have hlhs'_v : (lhs'.setWidth 64).toNat < s0.core.vals.length := by
      rw [bv_zext32_toNat, hvlen0]; omega
    have hlhs'_g : s0.core.vals[(lhs'.setWidth 64).toNat]'hlhs'_v =
        s0.core.vals[lhs'.toNat]?.getD 0#8 := by
      rw [List.getElem?_eq_getElem (by rw [hvlen0]; omega), Option.getD_some]
      exact list_getElem_congr (bv_zext32_toNat lhs') _ _
    ev_split
    · have hv1 := hev1_all lhs'.toNat hlhs'_lt
        (bv8_eq1_of_signExtend32_sgt0 (hdom_all lhs'.toNat hlhs'_lt)
          (by rw [← hlhs'_g]; exact hc))
      have ha0_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [a0.toNat]) :=
        ev_entails_of_eval fun α hα => by
          have h1 := hand_ev α hα; rw [hv1 α hα] at h1
          cases ha : evalLitVal α a0.toNat <;> cases hb : evalLitVal α a1.toNat <;>
            rw [ha, hb] at h1 <;> first | rfl | (exfalso; revert h1; decide)
      have ha1_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [a1.toNat]) :=
        ev_entails_of_eval fun α hα => by
          have h1 := hand_ev α hα; rw [hv1 α hα] at h1
          cases ha : evalLitVal α a0.toNat <;> cases hb : evalLitVal α a1.toNat <;>
            rw [ha, hb] at h1 <;> first | rfl | (exfalso; revert h1; decide)
      clear hc; ev_steps
      refine ev_unit_wp Γ hUnit hok0 ha0_lt ha0_ent hm0 hQ2
        fun ch1 s1 m1 _ _ hok1 hm1 => by
          ev_steps
          refine ev_unit_wp Γ hUnit hok1 ha1_lt ha1_ent hm1 hQ2
            fun ch2 s2 m2 _ _ hok2 hm2 => by
              ev_steps; exact hJ98 (gtype, arity, false, ch2, ()) m2
                ⟨s2, hok2, (fun h => False.elim (Bool.noConfusion h)), hm2⟩
    · clear hc; ev_steps_ng
      refine wp_join_group (ts := [i32]) (fun (m0v, ()) mj => m0 = mj ∧
          (m0v = a0 ∧ a0.toNat < a1.toNat ∨ m0v = a1 ∧ a1.toNat ≤ a0.toNat)) ?_ ?_
      · rintro _ ⟨m0v, ⟨⟩⟩ mj ⟨rfl, hm0v⟩
        ev_steps_ng
        refine wp_join_group (ts := [i32]) (fun (m1v, ()) mk =>
            (m0v = a0 ∧ m1v = a1 ∨ m0v = a1 ∧ m1v = a0) ∧
            (FullMem c { s0 with core := { s0.core with tmp := s0.core.tmp.set 0 m0v } } ⋆ R)
              mk) ?_ ?_
        · rintro _ ⟨m1v, ⟨⟩⟩ mk ⟨hpair, hmk⟩
          ev_steps
          let tmp' := (s0.core.tmp.set 0 m0v).set 1 m1v
          let s' : FullState := { s0 with core := { s0.core with tmp := tmp' } }
          have htl' : tmp'.length = c.max_vars := by simp [tmp', htmpl0]
          have hok' := evCoreOk_tmp hok0 htl'
          have h0_s : tmp'[0]?.getD 0#32 = m0v := by
            simp [tmp', show 0 < s0.core.tmp.length by omega]
          have h1_s : tmp'[1]?.getD 0#32 = m1v := by
            simp [tmp', show 1 < s0.core.tmp.length by omega]
          have htmp'_lt : ∀ k < 2, (tmp'[k]?.getD 0#32).toNat < 2 * cv0 := by
            intro k hk; rcases k with _ | _ | _
            · rw [h0_s]; rcases hpair with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> assumption
            · rw [h1_s]; rcases hpair with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption
            · omega
          have hev' : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
              evalLitVal α lhs'.toNat = (List.range 2).all fun k =>
                evalLitVal α (tmp'[k]?.getD 0#32).toNat := fun α hα => by
            rw [List.range_succ, List.all_append, List.range_one, List.all_cons, List.all_nil,
              List.all_cons, List.all_nil, Bool.and_true, Bool.and_true, h0_s, h1_s, hand_ev α hα]
            rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · rfl
            · exact Bool.and_comm ..
          exact hJ98 (0#32, 2#32, true, false, ()) m
            ⟨s', hok', fun _ => ⟨hlhs'_lt,
              by rw [show (2#32 : BitVec 32).toNat = 2 from rfl]; omega,
              by rw [show (2#32 : BitVec 32).toNat = 2 from rfl]; omega,
              by decide, htmp'_lt, Or.inr (Or.inl rfl), fun _ => hev',
              fun h => absurd h (by decide), fun h => absurd h (by decide), Or.inl rfl⟩, hm⟩
        · intro J114 hJ114; ev_split
          · ev_steps; exact hJ114 (a1, ()) m
              ⟨Or.inl ⟨(hm0v.resolve_right fun h => by omega).1, rfl⟩, hm⟩
          · ev_steps; exact hJ114 (a0, ()) m
              ⟨Or.inr ⟨(hm0v.resolve_left fun h => by omega).1, rfl⟩, hm⟩
      · intro J109 hJ109; ev_split
        · ev_steps; exact hJ109 (a0, ()) m0 ⟨rfl, Or.inl ⟨rfl, hc⟩⟩
        · ev_steps; exact hJ109 (a1, ()) m0 ⟨rfl, Or.inr ⟨rfl, by omega⟩⟩
  · have hlhs'_eq : lhs' = lhs := hlhs_f hc
    clear hc; ev_steps_ng
    refine wp_join_group (ts := [i32, i32, i32])
      (fun (c1, t1, e1, ()) m88 => m0 = m88 ∧ c1.toNat < 2 * cv0 ∧ t1.toNat < 2 * cv0 ∧
        e1.toNat < 2 * cv0 ∧ ∀ α, (cnfOfClauses F_cur).Sat α → evalLitVal α lhs.toNat =
          if evalLitVal α c1.toNat then evalLitVal α t1.toNat else evalLitVal α e1.toNat) ?_ ?_
    · rintro _ ⟨c1, t1, e1, ⟨⟩⟩ m88 ⟨rfl, hc1_lt, ht1_lt, he1_lt, hite1⟩
      ev_steps_ng
      refine wp_join_group (ts := [i32, i32, i32])
        (fun (lhs2, t2, e2, ()) m92 => m0 = m92 ∧ lhs2.toNat < 2 * cv0 ∧ t2.toNat < 2 * cv0 ∧
          e2.toNat < 2 * cv0 ∧ ∀ α, (cnfOfClauses F_cur).Sat α → evalLitVal α lhs2.toNat =
            if evalLitVal α c1.toNat then evalLitVal α t2.toNat
            else evalLitVal α e2.toNat) ?_ ?_
      · rintro _ ⟨lhs2, t2, e2, ⟨⟩⟩ m92 ⟨rfl, hl2_lt, ht2_lt, he2_lt, hite2⟩
        ev_steps
        let tmp' := ((s0.core.tmp.set 0 c1).set 1 t2).set 2 e2
        let s' : FullState := { s0 with core := { s0.core with tmp := tmp' } }
        have htl' : tmp'.length = c.max_vars := by simp [tmp', htmpl0]
        have hok' := evCoreOk_tmp hok0 htl'
        have h0_s : tmp'[0]?.getD 0#32 = c1 := by
          simp [tmp', show 0 < s0.core.tmp.length by omega]
        have h1_s : tmp'[1]?.getD 0#32 = t2 := by
          simp [tmp', show 1 < s0.core.tmp.length by omega]
        have h2_s : tmp'[2]?.getD 0#32 = e2 := by
          simp [tmp', show 2 < s0.core.tmp.length by omega]
        have htmp'_lt : ∀ k < arity.toNat, (tmp'[k]?.getD 0#32).toNat < 2 * cv0 := by
          intro k hk; rcases k with _ | _ | _ | _
          · rw [h0_s]; exact hc1_lt
          · rw [h1_s]; exact ht2_lt
          · rw [h2_s]; exact he2_lt
          · omega
        have hev' : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
            evalLitVal α lhs2.toNat =
              if evalLitVal α (tmp'[0]?.getD 0#32).toNat
              then evalLitVal α (tmp'[1]?.getD 0#32).toNat
              else evalLitVal α (tmp'[2]?.getD 0#32).toNat := fun α hα => by
          rw [h0_s, h1_s, h2_s]; exact hite2 α hα
        exact hJ87 (lhs2, gtype, arity, true, false, c1, t2, e2, ()) m
          ⟨s', hok', fun _ => ⟨hl2_lt, har_cv, har_max, by omega, htmp'_lt,
            Or.inl rfl, fun h => absurd (hgtype.symm.trans h) (by decide),
            fun h => absurd (hgtype.symm.trans h) (by decide),
            fun _ => ⟨har3, hev'⟩, Or.inr (Or.inr hgtype)⟩, hm⟩
      · intro J92 hJ92; rw [hlhs'_eq]; ev_split
        · ev_steps; refine hJ92 (lhs ^^^ 1#32, t1 ^^^ 1#32, e1 ^^^ 1#32, ()) m0
            ⟨rfl, ev_bv32_xor1_lt_cv hlhs_lt, ev_bv32_xor1_lt_cv ht1_lt,
             ev_bv32_xor1_lt_cv he1_lt, fun α hα => ?_⟩
          rw [bv32_xor1_eq_litNeg, bv32_xor1_eq_litNeg, bv32_xor1_eq_litNeg,
            evalLitVal_litNeg, evalLitVal_litNeg, evalLitVal_litNeg, hite1 α hα]
          cases evalLitVal α c1.toNat <;> rfl
        · ev_steps; exact hJ92 (lhs, t1, e1, ()) m0 ⟨rfl, hlhs_lt, ht1_lt, he1_lt, hite1⟩
    · intro J88 hJ88; ev_split
      · ev_steps; refine hJ88 (lc ^^^ 1#32, le, lt, ()) m0
          ⟨rfl, ev_bv32_xor1_lt_cv hlc_lt, hle_lt, hlt_lt, fun α hα => ?_⟩
        rw [bv32_xor1_eq_litNeg, evalLitVal_litNeg, hite α hα]
        cases evalLitVal α lc.toNat <;> rfl
      · ev_steps; exact hJ88 (lc, lt, le, ()) m0 ⟨rfl, hlc_lt, hlt_lt, hle_lt, hite⟩

private def t2Case7Expr {V : Ty → Type} {L : List Ty → Type}
    (h ctrl_off ld5 ld7 : V i64) (next_ep p19 p21 r28 ld47 ld51 ld55 : V i32)
    (ld61 ld64 : V i8) (J80 : L [i32, i32, i32, .bool, .bool, i32, i32, i32])
    (J81 : L []) : Expr V L [i64] :=
  evSgn0 .eq ld61 fun v85 => .jnz (.var v85) ( evSgn0 .eq ld64 fun v89 => .jnz (.var v89) (
  evL2 (.xor i32) (.var ld55) (.imm 1) fun v90 => evCmp32 .eq (.var ld51) (.var v90) fun v91 =>
  .jnz (.var v91) ( evL2 (.xor i32) (.imm 1) (.var ld47) fun v92 =>
  evL2 (.xor i32) (.var v92) (.var ld51) fun v93 => evL2 (.and i32) (.var v93) (.imm 1) fun v94 =>
  evL2 (.xor i32) (.var r28) (.var v94) fun v95 => .let_ ⟨.not i32, (.imm 1, ())⟩ fun (v96, ()) =>
  evL2 (.and i32) (.var ld47) (.var v96) fun v97 =>
  .let_ ⟨.not i32, (.imm 1, ())⟩ fun (v98, ()) =>
  evL2 (.and i32) (.var ld51) (.var v98) fun v99 =>
  .group (sig := [[i32, i32, .bool, .bool]]) (fun (_J100, ()) => .cons (fun (p101, (p102, (p103,
    (p104, ())))) =>
  .jump J80 (.var v95, (.var p101, (.var p102, (.var p103, (.var p104, (.var ld47, (.var ld51,
    (.var ld55, ())))))))) ) .nil) fun (J100, ()) => evCmp32 .eq (.var v97) (.var v99) fun v101 =>
  .jnz (.var v101) ( evL2 (.xor i32) (.var v95) (.imm 1) fun v102 =>
  evUnitExpr h v102 next_ep (.imm false) (fun p106 =>
  .jump J100 (.var p21, (.var p19, (.imm false, (.var p106, ())))) ) ) (
  .group (sig := [[i32, i32, .bool, .bool]]) (fun (_J102, ()) => .cons (fun (p103, (p104, (p105,
    (p106, ())))) => .jump J100 (.var p103, (.var p104, (.var p105, (.var p106, ()))))
  ) .nil) fun (J102, ()) => evLd8 ld7 v95 fun ld105 => evSgn0 .ne ld105 fun v109 =>
  .jnz (.var v109) (
  .group (sig := [[i32]]) (fun (_J110, ()) => .cons (fun (p111, ()) =>
  evEquivEnq2Expr h ctrl_off p111 v99 next_ep (.imm false) (fun p115 =>
  .jump J102 (.var p21, (.var p19, (.imm false, (.var p115, ())))) ) ) .nil) fun (J110, ()) =>
  evLd8 ld7 v95 fun ld113 => evSgn0 .sgt ld113 fun v117 => .jnz (.var v117) (
  evL2 (.xor i32) (.var v97) (.imm 1) fun v118 => .jump J110 (.var v118, ()) ) (
  .jump J110 (.var v97, ()) ) ) ( .let_ ⟨.sext 32 64, (.imm 0, ())⟩ fun (v110, ()) =>
  evL2 (.mul i64) (.var v110) (.imm 4) fun v111 =>
  evL2 (.add i64) (.var ld5) (.var v111) fun v112 =>
  .group (sig := [[i32]]) (fun (_J113, ()) => .cons (fun (p114, ()) =>
  .store (t := i32) (.var p114) (.var v112) ( .let_ ⟨.sext 32 64, (.imm 1, ())⟩ fun (v115, ()) =>
  evL2 (.mul i64) (.var v115) (.imm 4) fun v116 =>
  evL2 (.add i64) (.var ld5) (.var v116) fun v117 =>
  .group (sig := [[i32]]) (fun (_J118, ()) => .cons (fun (p119, ()) =>
  .store (t := i32) (.var p119) (.var v117) (
  .jump J102 (.imm 1, (.imm 2, (.imm true, (.imm false, ()))))) ) .nil) fun (J118, ()) =>
  evCmp32 .ult (.var v97) (.var v99) fun v119 => .jnz (.var v119) ( .jump J118 (.var v99, ()) ) (
  .jump J118 (.var v97, ()) )) ) .nil) fun (J113, ()) =>
  evCmp32 .ult (.var v97) (.var v99) fun v114 => .jnz (.var v114) ( .jump J113 (.var v97, ()) ) (
  .jump J113 (.var v99, ()) ) ) ) ) ( .jump J81 () ) ) ( .jump J81 () ) ) ( .jump J81 () )

private theorem ev_tag2_case7_wp (Γ : Env)
    (hUnit : Γ.Has "full_cong_unit_fold" Spec.fullCongUnitFoldSpec)
    (hEquiv : Γ.Has "full_cong_equiv_fold" Spec.fullCongEquivFoldSpec)
    (hEnq : Γ.Has "full_cong_enq_var" Spec.fullCongEnqVarSpec)
    {maxA : Nat} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 : Nat}
    {fl0 : BitVec 64} {ar0 : List (BitVec 32)} {arl0 g_len ht_off ht_sz : Nat}
    {scr0 scr_in : List (BitVec 32)} {s0 : FullState} {m0 : Mem 64}
    {ctrl_off : BitVec 64} {next_ep arity gtype lhs lc lt le : BitVec 32}
    {vt ve : BitVec 8}
    {J80 : Cont [i32, i32, i32, .bool, .bool, i32, i32, i32]} {J81 : Cont []}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    (hg_ht : g_len ≤ ht_off)
    (h3_tmp : 3 ≤ s0.core.tmp.length) (h2_cv : 2 ≤ cv0) (h2_max : 2 ≤ maxA)
    (hlhs_lt : lhs.toNat < 2 * cv0) (hlc_lt : lc.toNat < 2 * cv0) (hlt_lt : lt.toNat < 2 * cv0)
    (hite : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α → evalLitVal α lhs.toNat =
      if evalLitVal α lc.toNat then evalLitVal α lt.toNat else evalLitVal α le.toNat)
    (hok0 : EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
      scr0 scr_in s0)
    (hm0 : (FullMem c s0 ⋆ R) m0)
    (hQ2 : ∀ s' m', EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
      scr0 scr_in s' → F0.Unsat → (FullMem c s' ⋆ R) m' → Q (2#64, ()) m')
    (hJ80 : ∀ xs mj,
      T2Mid maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz scr0 scr_in
        gtype R xs mj → J80 xs mj)
    (hJ81 : J81 () m0) :
    wp Γ Q X (t2Case7Expr c.hdr ctrl_off c.pTmp c.pVals next_ep arity gtype lhs lc lt le
      vt ve J80 J81) m0 := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hw0 := hok0.1.2.1; have hcl0 := hok0.1.2.2.2.2.2.1
  have hcv_eq := hok0.2.1; have hcv_le : cv0 ≤ c.max_vars := hcv_eq ▸ hok0.1.1.core_ok.cur_vars_le
  have htmpl0 := hok0.1.1.core_ok.tmp_len_arr; have hvlen0 := hok0.1.1.core_ok.vals_len
  have h0_tmp : 0 < s0.core.tmp.length := by omega
  have h1_tmp : 1 < s0.core.tmp.length := by omega
  have h2_tmp : 2 < s0.core.tmp.length := by omega
  have hdom_all : ∀ l < 2 * cv0, s0.core.vals[l]?.getD 0#8 = 0#8 ∨
      s0.core.vals[l]?.getD 0#8 = 1#8 ∨ s0.core.vals[l]?.getD 0#8 = 0xFF#8 := fun l hl =>
    hw0.vals_domain l (hcv_eq.symm ▸ hl)
  have hev1_all : ∀ l < 2 * cv0, s0.core.vals[l]?.getD 0#8 = 1#8 →
      ∀ α, (cnfOfClauses F_cur).Sat α → evalLitVal α l = true := fun l hl hv _ hα =>
    entails_eval_true (vals1_entails hw0 hcl0 (hcv_eq.symm ▸ hl) hv) hα
  have hevff_all : ∀ l < 2 * cv0, s0.core.vals[l]?.getD 0#8 = 0xFF#8 →
      ∀ α, (cnfOfClauses F_cur).Sat α → evalLitVal α l = false := fun l hl hv _ hα =>
    entails_neg_eval_false (valsff_entails_neg hw0 hcl0 (hcv_eq.symm ▸ hl) hv) hα
  unfold t2Case7Expr; ev_split
  rotate_left; · ev_steps; exact hJ81
  clear hc; ev_split
  rotate_left; · ev_steps; exact hJ81
  clear hc; ev_split
  rotate_left; · ev_steps; exact hJ81
  have hte_xor : lt = le ^^^ 1#32 := hc
  obtain ⟨hbit01, hlhs_xor⟩ := t2_ite_xor_eval lhs lc lt le hte_xor (cnfOfClauses F_cur) hite
  let lhs' := lhs ^^^ ((1#32 ^^^ lc ^^^ lt) &&& 1#32)
  let r0 := lc &&& ~~~1#32
  let r1 := lt &&& ~~~1#32
  have hlhs'_lt : lhs'.toNat < 2 * cv0 := ev_xor1_bit01_lt hlhs_lt hbit01
  have hr0_lt : r0.toNat < 2 * cv0 := t2_bv32_and_not1_lt hlc_lt
  have hr1_lt : r1.toNat < 2 * cv0 := t2_bv32_and_not1_lt hlt_lt
  clear hc; ev_steps_ng
  refine wp_join_group (ts := [i32, i32, .bool, .bool])
    (fun (htag', har', nh', ch', ()) mj => ∃ sj : FullState,
      EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
        scr0 scr_in sj ∧
      (nh' = true → EvHashGateOk maxA F_cur cv0 gtype htag' har' lhs' sj.core.tmp) ∧
      (FullMem c sj ⋆ R) mj)
    (fun _ ⟨htag', har', nh', ch', ⟨⟩⟩ mj ⟨sj, hokj, hgj, hmj⟩ => by
      ev_steps; exact hJ80 (lhs', htag', har', nh', ch', _, _, _, ()) mj ⟨sj, hokj, hgj, hmj⟩) ?_
  intro J100 hJ100; ev_split
  · have hr_eq : r0 = r1 := hc
    have hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [(lhs' ^^^ 1#32).toNat]) :=
      ev_entails_of_eval fun α hα => by
        have h1 := hlhs_xor α hα
        change evalLitVal α lhs'.toNat = (evalLitVal α r0.toNat != evalLitVal α r1.toNat) at h1
        rw [hr_eq] at h1; simp only [bne_self_eq_false] at h1
        rw [bv32_xor1_eq_litNeg, evalLitVal_litNeg, h1]; rfl
    clear hc; ev_steps
    refine ev_unit_wp Γ hUnit hok0 (ev_bv32_xor1_lt_cv hlhs'_lt) hent hm0 hQ2
      fun ch' s' m' _ _ hok' hm' => by
        ev_steps; exact hJ100 (gtype, arity, false, ch', ()) m'
          ⟨s', hok', (fun h => False.elim (Bool.noConfusion h)), hm'⟩
  clear hc; ev_steps_ng
  refine wp_join_group (ts := [i32, i32, .bool, .bool])
    (fun (htag', har', nh', ch', ()) mj => ∃ sj : FullState,
      EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
        scr0 scr_in sj ∧
      (nh' = true → EvHashGateOk maxA F_cur cv0 gtype htag' har' lhs' sj.core.tmp) ∧
      (FullMem c sj ⋆ R) mj)
    (fun _ ⟨htag', har', nh', ch', ⟨⟩⟩ mj h => by
      ev_steps; exact hJ100 (htag', har', nh', ch', ()) mj h) ?_
  intro J102 hJ102
  have hlhs'_v : (lhs'.setWidth 64).toNat < s0.core.vals.length := by
    rw [bv_zext32_toNat, hvlen0]; omega
  have hlhs'_g : s0.core.vals[(lhs'.setWidth 64).toNat]'hlhs'_v =
      s0.core.vals[lhs'.toNat]?.getD 0#8 := by
    rw [List.getElem?_eq_getElem (by rw [hvlen0]; omega), Option.getD_some]
    exact list_getElem_congr (bv_zext32_toNat lhs') _ _
  ev_split
  · have hv_ne0 := bv8_ne0_of_signExtend32 (hdom_all lhs'.toNat hlhs'_lt)
      (by rw [← hlhs'_g]; exact hc)
    clear hc; ev_steps_ng
    refine wp_join_group (ts := [i32])
      (fun (a0, ()) ma => m0 = ma ∧ a0.toNat < 2 * cv0 ∧
        LitEquiv (cnfOfClauses F_cur) a0.toNat r1.toNat)
      (fun _ ⟨a0, ⟨⟩⟩ ma ⟨rfl, ha0_lt, heqv⟩ => by
        ev_steps
        refine ev_equiv_enq2_wp Γ hEquiv hEnq hg_ht rfl hok0 ha0_lt hr1_lt heqv hm0 hQ2
          fun ch' s' m' _ hok' hm' => by
            ev_steps; exact hJ102 (gtype, arity, false, ch', ()) m'
              ⟨s', hok', (fun h => False.elim (Bool.noConfusion h)), hm'⟩) ?_
    intro J110 hJ110; ev_split
    · have hv1 := hev1_all lhs'.toNat hlhs'_lt
        (bv8_eq1_of_signExtend32_sgt0 (hdom_all lhs'.toNat hlhs'_lt)
          (by rw [← hlhs'_g]; exact hc))
      ev_steps; refine hJ110 (r0 ^^^ 1#32, ()) m0
        ⟨rfl, ev_bv32_xor1_lt_cv hr0_lt, ev_litEquiv_of_eval fun α hα => ?_⟩
      have h1 := hlhs_xor α hα
      rw [hv1 α hα] at h1
      rw [bv32_xor1_eq_litNeg, evalLitVal_litNeg]
      cases h0e : evalLitVal α r0.toNat <;> cases h1e : evalLitVal α r1.toNat <;>
        rw [h0e, h1e] at h1 <;> first | rfl | (exfalso; revert h1; decide)
    · have hnsgt : ¬ (0#32 : BitVec 32).slt
          ((s0.core.vals[lhs'.toNat]?.getD 0#8).signExtend 32) = true := by
        intro h; rw [← hlhs'_g] at h
        have h2 : s0.core.vals[(lhs'.setWidth 64).toNat]'hlhs'_v =
            s0.core.vals[lhs'.toNat]'(by rw [hvlen0]; omega) :=
          list_getElem_congr (bv_zext32_toNat lhs') _ _
        rw [h2, show (0#32 : BitVec 32) = BitVec.ofNat 32 0 from rfl] at h
        change (BitVec.ofNat 32 0).slt (BitVec.signExtend 32 s0.core.vals[lhs'.toNat]) = true at h
        have hc' : (BitVec.ofNat 32 0).slt
            (BitVec.signExtend 32 s0.core.vals[lhs'.toNat]) = false := by
          simpa only [lhs', show (1#32 : BitVec 32) = 1 from rfl] using hc
        rw [h] at hc'; cases hc'
      have hvff := hevff_all lhs'.toNat hlhs'_lt
        (bv8_ne0_not_signExtend32_sgt0_eqff (hdom_all lhs'.toNat hlhs'_lt) hv_ne0 hnsgt)
      ev_steps; refine hJ110 (r0, ()) m0 ⟨rfl, hr0_lt, ev_litEquiv_of_eval fun α hα => ?_⟩
      have h1 := hlhs_xor α hα
      rw [hvff α hα] at h1
      cases h0e : evalLitVal α r0.toNat <;> cases h1e : evalLitVal α r1.toNat <;>
        rw [h0e, h1e] at h1 <;> first | rfl | (exfalso; revert h1; decide)
  · clear hc; ev_steps_ng
    refine wp_join_group (ts := [i32]) (fun (m0v, ()) mj => m0 = mj ∧
        (m0v = r0 ∧ r0.toNat < r1.toNat ∨ m0v = r1 ∧ r1.toNat ≤ r0.toNat)) ?_ ?_
    · rintro _ ⟨m0v, ⟨⟩⟩ mj ⟨rfl, hm0v⟩
      ev_steps_ng
      refine wp_join_group (ts := [i32]) (fun (m1v, ()) mk =>
          (m0v = r0 ∧ m1v = r1 ∨ m0v = r1 ∧ m1v = r0) ∧
          (FullMem c { s0 with core := { s0.core with tmp := s0.core.tmp.set 0 m0v } } ⋆ R)
            mk) ?_ ?_
      · rintro _ ⟨m1v, ⟨⟩⟩ mk ⟨hpair, hmk⟩
        ev_steps
        let tmp' := (s0.core.tmp.set 0 m0v).set 1 m1v
        let s' : FullState := { s0 with core := { s0.core with tmp := tmp' } }
        have htl' : tmp'.length = c.max_vars := by simp [tmp', htmpl0]
        have hok' := evCoreOk_tmp hok0 htl'
        have h0_tl : 0 < tmp'.length := by omega
        have h1_tl : 1 < tmp'.length := by omega
        have h0_s : tmp'[0]'h0_tl = m0v := by simp [tmp']
        have h1_s : tmp'[1]'h1_tl = m1v := by simp [tmp']
        have h0_g : tmp'[0]?.getD 0#32 = m0v := by
          rw [List.getElem?_eq_getElem h0_tl, Option.getD_some, h0_s]
        have h1_g : tmp'[1]?.getD 0#32 = m1v := by
          rw [List.getElem?_eq_getElem h1_tl, Option.getD_some, h1_s]
        have htmp'_lt : ∀ k < 2, (tmp'[k]?.getD 0#32).toNat < 2 * cv0 := by
          intro k hk; rcases k with _ | _ | _
          · rw [h0_g]; rcases hpair with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> assumption
          · rw [h1_g]; rcases hpair with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption
          · omega
        have hev' : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
            evalLitVal α lhs'.toNat = xorEvalList α ((tmp'.take 2).map BitVec.toNat) :=
          fun α hα => by
            rw [t2_take_two tmp' h0_tl h1_tl, h0_s, h1_s, List.map_cons,
              List.map_singleton, xorEvalList_pair, hlhs_xor α hα]
            rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · rfl
            · cases evalLitVal α r0.toNat <;> cases evalLitVal α r1.toNat <;> rfl
        exact hJ102 (1#32, 2#32, true, false, ()) m
          ⟨s', hok', fun _ => ⟨hlhs'_lt,
            by rw [show (2#32 : BitVec 32).toNat = 2 from rfl]; omega,
            by rw [show (2#32 : BitVec 32).toNat = 2 from rfl]; omega,
            by decide, htmp'_lt, Or.inr (Or.inr rfl), fun h => absurd h (by decide),
            fun _ => ⟨by decide, hev'⟩, fun h => absurd h (by decide), Or.inr (Or.inl rfl)⟩, hm⟩
      · intro J118 hJ118; ev_split
        · have hc' : r0.toNat < r1.toNat := by
            simpa only [r0, r1, show (~~~1 : BitVec 32) = ~~~1#32 from rfl] using hc
          ev_steps; exact hJ118 (r1, ()) m
            ⟨Or.inl ⟨(hm0v.resolve_right fun h => by omega).1, rfl⟩, hm⟩
        · have hc' : ¬ r0.toNat < r1.toNat := by
            simpa only [r0, r1, show (~~~1 : BitVec 32) = ~~~1#32 from rfl] using hc
          ev_steps; exact hJ118 (r0, ()) m
            ⟨Or.inr ⟨(hm0v.resolve_left fun h => by omega).1, rfl⟩, hm⟩
    · intro J113 hJ113; ev_split
      · have hc' : r0.toNat < r1.toNat := by
          simpa only [r0, r1, show (~~~1 : BitVec 32) = ~~~1#32 from rfl] using hc
        ev_steps; exact hJ113 (r0, ()) m0 ⟨rfl, Or.inl ⟨rfl, hc'⟩⟩
      · have hc' : ¬ r0.toNat < r1.toNat := by
          simpa only [r0, r1, show (~~~1 : BitVec 32) = ~~~1#32 from rfl] using hc
        ev_steps; exact hJ113 (r1, ()) m0 ⟨rfl, Or.inr ⟨rfl, by omega⟩⟩

public section

/-- Canonical WP proof for the ITE gate branch `evTag2Expr`. -/
theorem ev_tag2_wp (Γ : Env)
    (hUnit : Γ.Has "full_cong_unit_fold" Spec.fullCongUnitFoldSpec)
    (hEquiv : Γ.Has "full_cong_equiv_fold" Spec.fullCongEquivFoldSpec)
    (hEnq : Γ.Has "full_cong_enq_var" Spec.fullCongEnqVarSpec)
    {maxA : Nat} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 : Nat}
    {fl0 : BitVec 64} {ar0 : List (BitVec 32)} {arl0 g_len ht_off ht_sz g_n : Nat}
    {scr0 scr_in : List (BitVec 32)} {s0 : FullState} {m0 : Mem 64}
    {ctrl_off : BitVec 64} {next_ep arity gtype lhs lhs0 iw : BitVec 32}
    {J39 : Cont [i32, i32, i32, i32, .bool, .bool]}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    (hg_ht : g_len ≤ ht_off) (har_cv : arity.toNat ≤ cv0) (har_max : arity.toNat ≤ maxA)
    (hlhs_lt : lhs.toNat < 2 * cv0) (hlhs_eqv : LitEquiv (cnfOfClauses F_cur) lhs0.toNat lhs.toNat)
    (hite0 : gtype = 2#32 → arity = 3#32 →
      IteGateDef (cnfOfClauses F_cur) lhs0.toNat
        (scr0[g_n + 2]?.getD 0#32).toNat (scr0[g_n + 3]?.getD 0#32).toNat
        (scr0[g_n + 4]?.getD 0#32).toNat)
    (htmp_i : ∀ k < arity.toNat, (s0.core.tmp[k]?.getD 0#32).toNat < 2 * cv0 ∧
      LitEquiv (cnfOfClauses F_cur) (scr0[g_n + 2 + k]?.getD 0#32).toNat
        (s0.core.tmp[k]?.getD 0#32).toNat)
    (hok0 : EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
      scr0 scr_in s0)
    (hm0 : (FullMem c s0 ⋆ R) m0)
    (hQ2 : ∀ s' m', EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
      scr0 scr_in s' → F0.Unsat → (FullMem c s' ⋆ R) m' → Q (2#64, ()) m')
    (hJ39 : ∀ lhs' htag' har' nh' ch' s' m',
      EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz scr0 scr_in s' →
      (nh' = true → EvHashGateOk maxA F_cur cv0 gtype htag' har' lhs' s'.core.tmp) →
      (FullMem c s' ⋆ R) m' → J39 (lhs', iw, htag', har', nh', ch', ()) m') :
    wp Γ Q X (evTag2Expr c.hdr ctrl_off c.pTmp c.pVals next_ep arity gtype lhs iw J39) m0 := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hw0 := hok0.1.2.1; have hcl0 := hok0.1.2.2.2.2.2.1
  have hcv_eq := hok0.2.1; have hcv_le : cv0 ≤ c.max_vars := hcv_eq ▸ hok0.1.1.core_ok.cur_vars_le
  have htmpl0 := hok0.1.1.core_ok.tmp_len_arr; have hvlen0 := hok0.1.1.core_ok.vals_len
  let P_out := T2Out maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz scr0 scr_in
    gtype R
  let P_mid := T2Mid maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz scr0 scr_in
    gtype R
  unfold evTag2Expr; ev_steps_ng
  refine wp_join_group P_out (fun _ ⟨lhs', htag', har', nh', ch', ⟨⟩⟩ mj ⟨sj, hokj, hgj, hmj⟩ => by
    ev_steps; exact hJ39 lhs' htag' har' nh' ch' sj mj hokj hgj hmj) ?_
  intro J41 hJ41; ev_split
  rotate_left
  · ev_steps
    exact hJ41 (lhs, gtype, arity, false, false, ()) m0
      ⟨s0, hok0, (fun h => False.elim (Bool.noConfusion h)), hm0⟩
  have hgtype : gtype = 2#32 := hc; clear hc; ev_split
  rotate_left
  · ev_steps
    exact hJ41 (lhs, gtype, arity, false, false, ()) m0
      ⟨s0, hok0, (fun h => False.elim (Bool.noConfusion h)), hm0⟩
  have har3 : arity = 3#32 := hc; have har_n : arity.toNat = 3 := by rw [har3]; decide
  have h3_tmp : 3 ≤ s0.core.tmp.length := by omega
  have h0_tmp : 0 < s0.core.tmp.length := by omega
  have h1_tmp : 1 < s0.core.tmp.length := by omega
  have h2_tmp : 2 < s0.core.tmp.length := by omega
  let lc := s0.core.tmp[0]'h0_tmp
  let lt := s0.core.tmp[1]'h1_tmp
  let le := s0.core.tmp[2]'h2_tmp
  have hlc_lt : lc.toNat < 2 * cv0 := by
    simpa [lc, List.getElem?_eq_getElem h0_tmp] using (htmp_i 0 (by omega)).1
  have hlt_lt : lt.toNat < 2 * cv0 := by
    simpa [lt, List.getElem?_eq_getElem h1_tmp] using (htmp_i 1 (by omega)).1
  have hle_lt : le.toNat < 2 * cv0 := by
    simpa [le, List.getElem?_eq_getElem h2_tmp] using (htmp_i 2 (by omega)).1
  have hite : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α → evalLitVal α lhs.toNat =
      if evalLitVal α lc.toNat then evalLitVal α lt.toNat else evalLitVal α le.toNat := by
    intro α hα
    have h0 := (litEquiv_eval hα hlhs_eqv).symm.trans (iteGateDef_eval hα (hite0 hgtype har3))
    have hc_e := litEquiv_eval hα (by simpa using (htmp_i 0 (by omega)).2)
    have ht_e := litEquiv_eval hα (by simpa using (htmp_i 1 (by omega)).2)
    have he_e := litEquiv_eval hα (by simpa using (htmp_i 2 (by omega)).2)
    rw [List.getElem?_eq_getElem h0_tmp, Option.getD_some] at hc_e
    rw [List.getElem?_eq_getElem h1_tmp, Option.getD_some] at ht_e
    rw [List.getElem?_eq_getElem h2_tmp, Option.getD_some] at he_e
    rw [h0, hc_e, ht_e, he_e]
  have hdom_all : ∀ l < 2 * cv0, s0.core.vals[l]?.getD 0#8 = 0#8 ∨
      s0.core.vals[l]?.getD 0#8 = 1#8 ∨ s0.core.vals[l]?.getD 0#8 = 0xFF#8 := fun l hl =>
    hw0.vals_domain l (hcv_eq.symm ▸ hl)
  have hev1_all : ∀ l < 2 * cv0, s0.core.vals[l]?.getD 0#8 = 1#8 →
      ∀ α, (cnfOfClauses F_cur).Sat α → evalLitVal α l = true := fun l hl hv _ hα =>
    entails_eval_true (vals1_entails hw0 hcl0 (hcv_eq.symm ▸ hl) hv) hα
  have hevff_all : ∀ l < 2 * cv0, s0.core.vals[l]?.getD 0#8 = 0xFF#8 →
      ∀ α, (cnfOfClauses F_cur).Sat α → evalLitVal α l = false := fun l hl hv _ hα =>
    entails_neg_eval_false (valsff_entails_neg hw0 hcl0 (hcv_eq.symm ▸ hl) hv) hα
  have hvc_arr : (lc.setWidth 64).toNat < s0.core.vals.length := by
    rw [bv_zext32_toNat, hvlen0]; omega
  have hvt_arr : (lt.setWidth 64).toNat < s0.core.vals.length := by
    rw [bv_zext32_toNat, hvlen0]; omega
  have hve_arr : (le.setWidth 64).toNat < s0.core.vals.length := by
    rw [bv_zext32_toNat, hvlen0]; omega
  have hvc_get : s0.core.vals[(lc.setWidth 64).toNat]'hvc_arr =
      s0.core.vals[lc.toNat]?.getD 0#8 := by
    rw [List.getElem?_eq_getElem (by rw [hvlen0]; omega), Option.getD_some]
    exact list_getElem_congr (bv_zext32_toNat lc) _ _
  have hvt_get : s0.core.vals[(lt.setWidth 64).toNat]'hvt_arr =
      s0.core.vals[lt.toNat]?.getD 0#8 := by
    rw [List.getElem?_eq_getElem (by rw [hvlen0]; omega), Option.getD_some]
    exact list_getElem_congr (bv_zext32_toNat lt) _ _
  have hve_get : s0.core.vals[(le.setWidth 64).toNat]'hve_arr =
      s0.core.vals[le.toNat]?.getD 0#8 := by
    rw [List.getElem?_eq_getElem (by rw [hvlen0]; omega), Option.getD_some]
    exact list_getElem_congr (bv_zext32_toNat le) _ _
  clear hc; ev_steps_ng
  refine wp_join_group P_mid (fun _ ⟨lhs', htag', har', nh', ch', _, _, _, ⟨⟩⟩ mj h => by
    ev_steps; exact hJ41 (lhs', htag', har', nh', ch', ()) mj h) ?_
  intro J65 hJ65; ev_split
  · -- Case 1: `vc != 0`
    have hvc_ne0 := bv8_ne0_of_signExtend32 (hdom_all lc.toNat hlc_lt)
      (by rw [← hvc_get]; exact hc)
    clear hc; ev_steps_ng
    refine wp_join_group (ts := [i32])
      (fun (br, ()) mbr => m0 = mbr ∧ br.toNat < 2 * cv0 ∧
        LitEquiv (cnfOfClauses F_cur) lhs.toNat br.toNat)
      (fun _ ⟨br, ⟨⟩⟩ mbr ⟨rfl, hbr_lt, heqv⟩ => by
        ev_steps
        refine ev_equiv_enq2_wp Γ hEquiv hEnq hg_ht rfl hok0 hlhs_lt hbr_lt heqv hm0 hQ2
          fun ch' s' m' _ hok' hm' => by
            ev_steps; exact hJ65 (lhs, gtype, arity, false, ch', _, _, _, ()) m'
              ⟨s', hok', (fun h => False.elim (Bool.noConfusion h)), hm'⟩) ?_
    intro J70 hJ70; ev_split
    · have hc1 := hev1_all lc.toNat hlc_lt
        (bv8_eq1_of_signExtend32_sgt0 (hdom_all lc.toNat hlc_lt) (by rw [← hvc_get]; exact hc))
      ev_steps; exact hJ70 (lt, ()) m0 ⟨rfl, hlt_lt, ev_litEquiv_of_eval fun α hα => by
        rw [hite α hα, hc1 α hα]; rfl⟩
    · have hnsgt : ¬ (0#32 : BitVec 32).slt
          ((s0.core.vals[lc.toNat]?.getD 0#8).signExtend 32) = true := by
        intro h; rw [← hvc_get] at h
        have h1 : s0.core.vals[(lc.setWidth 64).toNat]'hvc_arr =
            s0.core.vals[s0.core.tmp[0 % 2 ^ 64].toNat]'(by
              simp only [lc, bv_zext32_toNat, Nat.zero_mod] at hvc_arr ⊢; exact hvc_arr) := by
          simp only [lc, bv_zext32_toNat, Nat.zero_mod]
        rw [h1, show (0#32 : BitVec 32) = BitVec.ofNat 32 0 from rfl] at h
        rw [h] at hc; cases hc
      have hcff := hevff_all lc.toNat hlc_lt
        (bv8_ne0_not_signExtend32_sgt0_eqff (hdom_all lc.toNat hlc_lt) hvc_ne0 hnsgt)
      ev_steps; exact hJ70 (le, ()) m0 ⟨rfl, hle_lt, ev_litEquiv_of_eval fun α hα => by
        rw [hite α hα, hcff α hα]; rfl⟩
  have hvc_eq0 : s0.core.vals[lc.toNat]?.getD 0#8 = 0#8 :=
    bv8_eq0_of_signExtend32 (hdom_all lc.toNat hlc_lt) (by rw [← hvc_get]; exact hc)
  clear hc; ev_steps_ng
  refine wp_join_group P_mid (fun _ ⟨lhs', htag', har', nh', ch', p6, p7, p8, ⟨⟩⟩ mj h => by
    ev_steps; exact hJ65 (lhs', htag', har', nh', ch', p6, p7, p8, ()) mj h) ?_
  intro J70 hJ70; ev_split
  · -- Case 2: `t == e`
    have heq_te : lt = le := hc
    have heqv : LitEquiv (cnfOfClauses F_cur) lhs.toNat lt.toNat :=
      ev_litEquiv_of_eval fun α hα => by
        rw [hite α hα, heq_te]; cases evalLitVal α lc.toNat <;> rfl
    clear hc; ev_steps
    refine ev_equiv_enq2_wp Γ hEquiv hEnq hg_ht rfl hok0 hlhs_lt hlt_lt heqv hm0 hQ2
      fun ch' s' m' _ hok' hm' => by
        ev_steps; exact hJ70 (lhs, gtype, arity, false, ch', _, _, _, ()) m'
          ⟨s', hok', (fun h => False.elim (Bool.noConfusion h)), hm'⟩
  clear hc; ev_steps_ng
  refine wp_join_group P_mid (fun _ ⟨lhs', htag', har', nh', ch', p6, p7, p8, ⟨⟩⟩ mj h => by
    ev_steps; exact hJ70 (lhs', htag', har', nh', ch', p6, p7, p8, ()) mj h) ?_
  intro J72 hJ72; ev_steps_ng
  refine wp_join_group (ts := []) (fun () m73 => m0 = m73) ?_ ?_
  · rintro _ ⟨⟩ m73 rfl; ev_steps_ng
    refine wp_join_group P_mid (fun _ ⟨lhs', htag', har', nh', ch', p6, p7, p8, ⟨⟩⟩ mj h => by
      ev_steps; exact hJ72 (lhs', htag', har', nh', ch', p6, p7, p8, ()) mj h) ?_
    intro J74 hJ74; ev_steps_ng
    refine wp_join_group (ts := []) (fun () m75 => m0 = m75) ?_ ?_
    · rintro _ ⟨⟩ m75 rfl; ev_steps_ng
      refine wp_join_group P_mid (fun _ ⟨lhs', htag', har', nh', ch', p6, p7, p8, ⟨⟩⟩ mj h => by
        ev_steps; exact hJ74 (lhs', htag', har', nh', ch', p6, p7, p8, ()) mj h) ?_
      intro J76 hJ76; ev_steps_ng
      refine wp_join_group (ts := []) (fun () m77 => m0 = m77) ?_ ?_
      · rintro _ ⟨⟩ m77 rfl; ev_steps_ng
        refine wp_join_group P_mid (fun _ ⟨lhs', htag', har', nh', ch', p6, p7, p8, ⟨⟩⟩ mj h => by
          ev_steps; exact hJ76 (lhs', htag', har', nh', ch', p6, p7, p8, ()) mj h) ?_
        intro J78 hJ78; ev_steps_ng
        refine wp_join_group (ts := []) (fun () m79 => m0 = m79) ?_ ?_
        · rintro _ ⟨⟩ m79 rfl; ev_steps_ng
          refine wp_join_group P_mid (fun _ ⟨lhs', htag', har', nh', ch', p6, p7, p8, ⟨⟩⟩ mj h => by
            ev_steps; exact hJ78 (lhs', htag', har', nh', ch', p6, p7, p8, ()) mj h) ?_
          intro J80 hJ80; ev_steps_ng
          refine wp_join_group (ts := []) (fun () m81 => m0 = m81) ?_ ?_
          · -- `J81` fallback: 8 cases + normal ITE-3
            rintro _ ⟨⟩ m81 rfl
            have h8 := t2_ite_8cases_ok hdom_all hev1_all hevff_all hlt_lt hle_lt hite
            ev_steps_ng
            refine wp_join_group (ts := [i32, .bool, i32, i32]) (T2And2P cv0 F_cur lhs m0) ?_ ?_
            · rintro _ ⟨lhs', is_and2, a0, a1, ⟨⟩⟩ m82 ⟨rfl, hlhs_f, hand2⟩
              ev_steps_ng
              exact ev_tag2_and2_norm_wp Γ hUnit hEquiv hEnq hg_ht hgtype har3 har_cv har_max
                hlhs_lt hlc_lt hlt_lt hle_lt hite hlhs_f hand2 hok0 hm0 hQ2 hJ80
            · -- Dispatching the 8 normalization guards for `J82`
              intro J82 hJ82; ev_split
              · ev_steps; exact hJ82 (lhs ^^^ 1#32, true, lc ^^^ 1#32, le ^^^ 1#32, ()) m0
                  ⟨rfl, fun h => False.elim (Bool.noConfusion h),
                    fun _ => ⟨ev_bv32_xor1_lt_cv hlhs_lt, ev_bv32_xor1_lt_cv hlc_lt,
                      ev_bv32_xor1_lt_cv hle_lt, h8.1 (by rw [← hvt_get]; exact hc)⟩⟩
              clear hc; ev_steps_ng
              refine wp_join_group (ts := [i32, .bool, i32, i32]) (T2And2P cv0 F_cur lhs m0)
                (fun _ ⟨p1, p2, p3, p4, ⟨⟩⟩ m' h => by
                  ev_steps; exact hJ82 (p1, p2, p3, p4, ()) m' h) ?_
              intro J87 hJ87; ev_split
              · ev_steps; exact hJ87 (lhs, true, lc ^^^ 1#32, le, ()) m0
                  ⟨rfl, fun h => False.elim (Bool.noConfusion h),
                    fun _ => ⟨hlhs_lt, ev_bv32_xor1_lt_cv hlc_lt, hle_lt,
                      h8.2.1 (by rw [← hvt_get]; exact hc)⟩⟩
              clear hc; ev_steps_ng
              refine wp_join_group (ts := [i32, .bool, i32, i32]) (T2And2P cv0 F_cur lhs m0)
                (fun _ ⟨p1, p2, p3, p4, ⟨⟩⟩ m' h => by
                  ev_steps; exact hJ87 (p1, p2, p3, p4, ()) m' h) ?_
              intro J92 hJ92; ev_split
              · ev_steps; exact hJ92 (lhs ^^^ 1#32, true, lc, lt ^^^ 1#32, ()) m0
                  ⟨rfl, fun h => False.elim (Bool.noConfusion h),
                    fun _ => ⟨ev_bv32_xor1_lt_cv hlhs_lt, hlc_lt, ev_bv32_xor1_lt_cv hlt_lt,
                      h8.2.2.1 (by rw [← hve_get]; exact hc)⟩⟩
              clear hc; ev_steps_ng
              refine wp_join_group (ts := [i32, .bool, i32, i32]) (T2And2P cv0 F_cur lhs m0)
                (fun _ ⟨p1, p2, p3, p4, ⟨⟩⟩ m' h => by
                  ev_steps; exact hJ92 (p1, p2, p3, p4, ()) m' h) ?_
              intro J97 hJ97; ev_split
              · ev_steps; exact hJ97 (lhs, true, lc, lt, ()) m0
                  ⟨rfl, fun h => False.elim (Bool.noConfusion h),
                    fun _ => ⟨hlhs_lt, hlc_lt, hlt_lt, h8.2.2.2.1 (by rw [← hve_get]; exact hc)⟩⟩
              clear hc; ev_steps_ng
              refine wp_join_group (ts := [i32, .bool, i32, i32]) (T2And2P cv0 F_cur lhs m0)
                (fun _ ⟨p1, p2, p3, p4, ⟨⟩⟩ m' h => by
                  ev_steps; exact hJ97 (p1, p2, p3, p4, ()) m' h) ?_
              intro J102 hJ102; ev_split
              · ev_steps; exact hJ102 (lhs ^^^ 1#32, true, lc ^^^ 1#32, le ^^^ 1#32, ()) m0
                  ⟨rfl, fun h => False.elim (Bool.noConfusion h),
                    fun _ => ⟨ev_bv32_xor1_lt_cv hlhs_lt, ev_bv32_xor1_lt_cv hlc_lt,
                      ev_bv32_xor1_lt_cv hle_lt, h8.2.2.2.2.1 hc⟩⟩
              clear hc; ev_steps_ng
              refine wp_join_group (ts := [i32, .bool, i32, i32]) (T2And2P cv0 F_cur lhs m0)
                (fun _ ⟨p1, p2, p3, p4, ⟨⟩⟩ m' h => by
                  ev_steps; exact hJ102 (p1, p2, p3, p4, ()) m' h) ?_
              intro J104 hJ104; ev_split
              · ev_steps; exact hJ104 (lhs, true, lc ^^^ 1#32, le, ()) m0
                  ⟨rfl, fun h => False.elim (Bool.noConfusion h),
                    fun _ => ⟨hlhs_lt, ev_bv32_xor1_lt_cv hlc_lt, hle_lt, h8.2.2.2.2.2.1 hc⟩⟩
              clear hc; ev_steps_ng
              refine wp_join_group (ts := [i32, .bool, i32, i32]) (T2And2P cv0 F_cur lhs m0)
                (fun _ ⟨p1, p2, p3, p4, ⟨⟩⟩ m' h => by
                  ev_steps; exact hJ104 (p1, p2, p3, p4, ()) m' h) ?_
              intro J107 hJ107; ev_split
              · ev_steps; exact hJ107 (lhs ^^^ 1#32, true, lc, lt ^^^ 1#32, ()) m0
                  ⟨rfl, fun h => False.elim (Bool.noConfusion h),
                    fun _ => ⟨ev_bv32_xor1_lt_cv hlhs_lt, hlc_lt, ev_bv32_xor1_lt_cv hlt_lt,
                      h8.2.2.2.2.2.2.1 hc⟩⟩
              clear hc; ev_steps_ng
              refine wp_join_group (ts := [.bool, i32, i32])
                (fun x m' => T2And2P cv0 F_cur lhs m0 (lhs, x.1, x.2.1, x.2.2.1, ()) m')
                (fun _ ⟨p1, p2, p3, ⟨⟩⟩ m' h => by
                  ev_steps; exact hJ107 (lhs, p1, p2, p3, ()) m' h) ?_
              intro J110 hJ110; ev_split
              · ev_steps; exact hJ110 (true, lc, lt, ()) m0
                  ⟨rfl, fun h => False.elim (Bool.noConfusion h),
                    fun _ => ⟨hlhs_lt, hlc_lt, hlt_lt, h8.2.2.2.2.2.2.2 hc⟩⟩
              · ev_steps; exact hJ110 (false, 0#32, 0#32, ()) m0
                  ⟨rfl, fun _ => rfl, fun h => False.elim (Bool.noConfusion h)⟩
          · -- Case 7 (`J81`): `vt == 0 ∧ ve == 0 ∧ t == e ^^^ 1` (ITE-as-XOR)
            intro J81 hJ81
            exact ev_tag2_case7_wp Γ hUnit hEquiv hEnq hg_ht h3_tmp (by omega) (by omega)
              hlhs_lt hlc_lt hlt_lt hite hok0 hm0 hQ2 hJ80 (hJ81 () m0 rfl)
        · -- Case 6 (`J79`): `vt < 0 ∧ ve < 0`
          intro J79 hJ79; ev_split
          rotate_left; · ev_steps; exact hJ79 () m0 rfl
          have hvt_c := hc; clear hc; ev_split
          rotate_left; · ev_steps; exact hJ79 () m0 rfl
          have htf : s0.core.vals[lt.toNat]?.getD 0#8 = 0xFF#8 :=
            t2_bv8_eqff_of_sext_slt0 (hdom_all lt.toNat hlt_lt) (by rw [← hvt_get]; exact hvt_c)
          have hef : s0.core.vals[le.toNat]?.getD 0#8 = 0xFF#8 :=
            t2_bv8_eqff_of_sext_slt0 (hdom_all le.toNat hle_lt) (by rw [← hve_get]; exact hc)
          have hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [(lhs ^^^ 1#32).toNat]) :=
            ev_entails_of_eval fun α hα => by
              rw [bv32_xor1_eq_litNeg, evalLitVal_litNeg, hite α hα,
                hevff_all lt.toNat hlt_lt htf α hα, hevff_all le.toNat hle_lt hef α hα]
              cases evalLitVal α lc.toNat <;> rfl
          clear hc; ev_steps
          refine ev_unit_wp Γ hUnit hok0 (ev_bv32_xor1_lt_cv hlhs_lt) hent hm0 hQ2
            fun ch' s' m' _ _ hok' hm' => by
              ev_steps; exact hJ78 (lhs, gtype, arity, false, ch', _, _, _, ()) m'
                ⟨s', hok', (fun h => False.elim (Bool.noConfusion h)), hm'⟩
      · -- Case 5 (`J77`): `vt > 0 ∧ ve > 0`
        intro J77 hJ77; ev_split
        rotate_left; · ev_steps; exact hJ77 () m0 rfl
        have hvt_c := hc; clear hc; ev_split
        rotate_left; · ev_steps; exact hJ77 () m0 rfl
        have ht1 := hev1_all lt.toNat hlt_lt
          (bv8_eq1_of_signExtend32_sgt0 (hdom_all lt.toNat hlt_lt) (by rw [← hvt_get]; exact hvt_c))
        have he1 := hev1_all le.toNat hle_lt
          (bv8_eq1_of_signExtend32_sgt0 (hdom_all le.toNat hle_lt) (by rw [← hve_get]; exact hc))
        have hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lhs.toNat]) :=
          ev_entails_of_eval fun α hα => by
            rw [hite α hα, ht1 α hα, he1 α hα]; cases evalLitVal α lc.toNat <;> rfl
        clear hc; ev_steps
        refine ev_unit_wp Γ hUnit hok0 hlhs_lt hent hm0 hQ2 fun ch' s' m' _ _ hok' hm' => by
          ev_steps; exact hJ76 (lhs, gtype, arity, false, ch', _, _, _, ()) m'
            ⟨s', hok', (fun h => False.elim (Bool.noConfusion h)), hm'⟩
    · -- Case 4 (`J75`): `vt < 0 ∧ ve > 0`
      intro J75 hJ75; ev_split
      rotate_left; · ev_steps; exact hJ75 () m0 rfl
      have hvt_c := hc; clear hc; ev_split
      rotate_left; · ev_steps; exact hJ75 () m0 rfl
      have htf : s0.core.vals[lt.toNat]?.getD 0#8 = 0xFF#8 :=
        t2_bv8_eqff_of_sext_slt0 (hdom_all lt.toNat hlt_lt) (by rw [← hvt_get]; exact hvt_c)
      have he1 := hev1_all le.toNat hle_lt
        (bv8_eq1_of_signExtend32_sgt0 (hdom_all le.toNat hle_lt) (by rw [← hve_get]; exact hc))
      have heqv : LitEquiv (cnfOfClauses F_cur) lhs.toNat (lc ^^^ 1#32).toNat :=
        ev_litEquiv_of_eval fun α hα => by
          rw [hite α hα, hevff_all lt.toNat hlt_lt htf α hα, he1 α hα, bv32_xor1_eq_litNeg,
            evalLitVal_litNeg]
          cases evalLitVal α lc.toNat <;> rfl
      clear hc; ev_steps
      refine ev_equiv_enq2b_wp Γ hEquiv hEnq hg_ht rfl hok0 hlhs_lt (ev_bv32_xor1_lt_cv hlc_lt)
        heqv hm0 hQ2 fun ch' s' m' _ hok' hm' => by
          ev_steps; exact hJ74 (lhs, gtype, arity, false, ch', _, _, _, ()) m'
            ⟨s', hok', (fun h => False.elim (Bool.noConfusion h)), hm'⟩
  · -- Case 3 (`J73`): `vt > 0 ∧ ve < 0`
    intro J73 hJ73; ev_split
    rotate_left; · ev_steps; exact hJ73 () m0 rfl
    have hvt_c := hc; clear hc; ev_split
    rotate_left; · ev_steps; exact hJ73 () m0 rfl
    have ht1 := hev1_all lt.toNat hlt_lt
      (bv8_eq1_of_signExtend32_sgt0 (hdom_all lt.toNat hlt_lt) (by rw [← hvt_get]; exact hvt_c))
    have hef : s0.core.vals[le.toNat]?.getD 0#8 = 0xFF#8 :=
      t2_bv8_eqff_of_sext_slt0 (hdom_all le.toNat hle_lt) (by rw [← hve_get]; exact hc)
    have heqv : LitEquiv (cnfOfClauses F_cur) lhs.toNat lc.toNat :=
      ev_litEquiv_of_eval fun α hα => by
        rw [hite α hα, ht1 α hα, hevff_all le.toNat hle_lt hef α hα]
        cases evalLitVal α lc.toNat <;> rfl
    clear hc; ev_steps
    refine ev_equiv_enq2_wp Γ hEquiv hEnq hg_ht rfl hok0 hlhs_lt hlc_lt heqv hm0 hQ2
      fun ch' s' m' _ hok' hm' => by
        ev_steps; exact hJ72 (lhs, gtype, arity, false, ch', _, _, _, ()) m'
          ⟨s', hok', (fun h => False.elim (Bool.noConfusion h)), hm'⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence
