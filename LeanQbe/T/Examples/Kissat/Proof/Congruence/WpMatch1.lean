/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Inv
public import LeanQbe.T.Examples.Kissat.Src.Congruence

/-!
# Congruence AND / XOR Pattern-Match WP Proofs

Canonical `Func.wp` proofs for `full_cong_and_match` (`Spec.fullCongAndMatchSpec`)
and `full_cong_xor_match` (`Spec.fullCongXorMatchSpec`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics


private theorem bv32_and_not1_xor_eq (r : BitVec 32) :
    ((r &&& ~~~1#32).toNat = r.toNat ∧ (r &&& 1#32) = 0#32) ∨
    ((r &&& ~~~1#32).toNat = litNeg r.toNat ∧ (r &&& 1#32) = 1#32) := by
  have hbit : r &&& 1#32 = 0#32 ∨ r &&& 1#32 = 1#32 := by
    have h1 : (r &&& 1#32).toNat = r.toNat % 2 := by
      rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl]
      exact Nat.and_two_pow_sub_one_eq_mod r.toNat 1
    by_cases hp : r.toNat % 2 = 0
    · left; apply BitVec.eq_of_toNat_eq; rw [h1, hp]; rfl
    · right; apply BitVec.eq_of_toNat_eq; rw [h1]; simp [BitVec.toNat_ofNat]; omega
  have h1z : ∀ k : Nat, (1#32 : BitVec 32).getLsbD (k + 1) = false := by
    intro k; rw [BitVec.getLsbD_ofNat, Nat.testBit_succ, Nat.zero_testBit]; simp
  have hnz : ∀ k : Nat, k + 1 < 32 → (~~~1#32 : BitVec 32).getLsbD (k + 1) = true := by
    intro k hk; rw [BitVec.getLsbD_not, h1z k]; simp [hk]
  rcases hbit with h0 | h1
  · left
    have hlsb : r.getLsbD 0 = false := by
      have := congrArg (fun x => x.getLsbD 0) h0; simpa using this
    have heq : r &&& ~~~1#32 = r := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      cases i with
      | zero => rw [BitVec.getLsbD_and, hlsb]; rfl
      | succ k => rw [BitVec.getLsbD_and, hnz k hi, Bool.and_true]
    exact ⟨by rw [heq], h0⟩
  · right
    have hlsb : r.getLsbD 0 = true := by
      have := congrArg (fun x => x.getLsbD 0) h1; simpa using this
    have heq : r &&& ~~~1#32 = r ^^^ 1#32 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      cases i with
      | zero => rw [BitVec.getLsbD_and, BitVec.getLsbD_xor, hlsb]; rfl
      | succ k =>
        rw [BitVec.getLsbD_and, BitVec.getLsbD_xor, hnz k hi, h1z k, Bool.and_true,
          Bool.xor_false]
    rw [heq, bv32_xor1_eq_litNeg]
    exact ⟨rfl, h1⟩

private theorem xorEvalList_even_step (α : Nat → Bool) (r : BitVec 32)
    (xs : List Nat) :
    ((r &&& 1#32 == 1#32) !=
      xorEvalList α (xs ++ [(r &&& ~~~1#32).toNat])) =
      xorEvalList α (xs ++ [r.toNat]) := by
  rw [xorEvalList_append, xorEvalList_append, xorEvalList_cons, xorEvalList_nil,
    xorEvalList_cons, xorEvalList_nil, Bool.bne_false, Bool.bne_false]
  rcases bv32_and_not1_xor_eq r with ⟨he, h0⟩ | ⟨he, h1⟩
  · rw [he, h0]
    cases evalLitVal α r.toNat <;> cases xorEvalList α xs <;> rfl
  · rw [he, h1, evalLitVal_litNeg]
    cases evalLitVal α r.toNat <;> cases xorEvalList α xs <;> rfl

private theorem xorEvalList_dedup_step (α : Nat → Bool)
    (pref suf : List Nat) (x : Nat) :
    xorEvalList α (pref ++ (x :: x :: suf)) =
      xorEvalList α (pref ++ suf) := by
  rw [xorEvalList_append, xorEvalList_append, xorEvalList_dedup_adj]

private theorem list_take_set_append {α : Type _} (l : List α) {i : Nat}
    (hi : i < l.length) (v : α) :
    List.take (i + 1) (l.set i v) = List.take i l ++ [v] := by
  have hi2 : i < (l.set i v).length := by simp [hi]
  rw [List.take_succ_eq_append_getElem hi2, List.take_set_of_le (Nat.le_refl _)]
  simp

private theorem xorMatch_gate_facts {maxA : Nat} {F_cur : List (List Nat)}
    {cur_vars g_len ent : Nat} {scr0 : List (BitVec 32)}
    (hgat : CongGateAt maxA F_cur cur_vars scr0 g_len ent)
    (htag_mword : scr0[ent + 1]?.getD 0#32 >>> 28 = 1#32) :
    ∃ lhs mword, scr0[ent]? = some lhs ∧ scr0[ent + 1]? = some mword ∧
      lhs.toNat < 2 * cur_vars ∧ ent + 2 + congGateArity mword ≤ g_len ∧
      congGateArity mword ≤ cur_vars ∧
      2 ≤ congGateArity mword ∧ congGateArity mword ≤ 4 ∧
      ent + 2 + congGateArity mword ≤ scr0.length ∧
      (mword &&& 255#32).toNat = congGateArity mword ∧
      (∀ k, k < congGateArity mword → ∃ r, scr0[ent + 2 + k]? = some r ∧ r.toNat < 2 * cur_vars) ∧
      XorListGateDef (cnfOfClauses F_cur) lhs.toNat
        (List.map BitVec.toNat (List.take (congGateArity mword) (List.drop (ent + 2) scr0))) := by
  rcases hgat with ⟨lhs, mword, hlhs, hmword, hlhs_lt, hge_g, har_le, _, hrhs, hcase⟩
  have hmw_get : scr0[ent + 1]?.getD 0#32 = mword := by rw [hmword, Option.getD_some]
  have ht1 : (mword >>> 28).toNat = 1 := by rw [← hmw_get, htag_mword]; rfl
  have h2_xor : (2 ≤ congGateArity mword ∧ congGateArity mword ≤ 4) ∧
      XorListGateDef (cnfOfClauses F_cur) lhs.toNat
        (List.map BitVec.toNat (List.take (congGateArity mword) (List.drop (ent + 2) scr0))) := by
    rcases hcase with h03 | ⟨_, h2, h4, hx⟩ | h2
    · rcases h03 with ⟨⟨ht0, _⟩ | ⟨ht3, _⟩, _⟩ <;> exact absurd ht1 (by omega)
    · exact ⟨⟨h2, h4⟩, hx⟩
    · exact absurd ht1 (by omega)
  have hscr_len : ent + 2 + congGateArity mword ≤ scr0.length := by
    obtain ⟨_, hr, _⟩ := hrhs (congGateArity mword - 1) (by omega)
    by_cases hb : ent + 2 + (congGateArity mword - 1) < scr0.length
    · omega
    · rw [List.getElem?_eq_none (by omega)] at hr; cases hr
  have har_bv : (mword &&& 255#32).toNat = congGateArity mword := by
    rw [congGateArity_of_ne3 (by rw [← hmw_get, htag_mword]; decide)]
  exact ⟨lhs, mword, hlhs, hmword, hlhs_lt, hge_g, har_le, h2_xor.1.1, h2_xor.1.2,
    hscr_len, har_bv, hrhs, h2_xor.2⟩

private theorem xorMatch_dedup_push_inv {mclr3 mclr2 : List (BitVec 32)}
    {k w ua_out max_vars : Nat}
    (hmcl3 : mclr3.length = max_vars) (hwk : w ≤ k) (hw_lt : w < max_vars)
    (hk_lt : k < ua_out) (hua_le : ua_out ≤ mclr2.length) (hua_m3 : ua_out ≤ max_vars)
    (htail3 : ∀ j, k ≤ j → j < ua_out → mclr3[j]? = mclr2[j]?)
    (hxor3 : ∀ α, xorEvalList α (List.map BitVec.toNat
      (List.take w mclr3 ++ List.take (ua_out - k) (List.drop k mclr2))) =
      xorEvalList α (List.map BitVec.toNat (List.take ua_out mclr2))) :
    let mclr3' := mclr3.set w (mclr3[k]'(by omega))
    (∀ j, k + 1 ≤ j → j < ua_out → mclr3'[j]? = mclr2[j]?) ∧
    (∀ α, xorEvalList α (List.map BitVec.toNat
      (List.take (w + 1) mclr3' ++ List.take (ua_out - (k + 1)) (List.drop (k + 1) mclr2))) =
      xorEvalList α (List.map BitVec.toNat (List.take ua_out mclr2))) := by
  have hk_len : k < mclr3.length := by omega
  refine ⟨fun j hj1 hj2 => ?_, fun α => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact htail3 j (by omega) hj2
  · rw [list_take_set_append mclr3 (by omega), ← hxor3 α]
    have hdk : List.take (ua_out - k) (List.drop k mclr2) =
        mclr2[k]'(by omega) :: List.take (ua_out - (k + 1)) (List.drop (k + 1) mclr2) := by
      rw [show ua_out - k = (ua_out - (k + 1)) + 1 by omega,
        List.drop_eq_getElem_cons (by omega), List.take_succ_cons]
    have hvk_eq : mclr3[k]'(by omega) = mclr2[k]'(by omega) := by
      have hq := htail3 k (Nat.le_refl _) hk_lt
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
        Option.some.injEq] at hq
      exact hq
    rw [hdk, hvk_eq]
    congr 1
    simp only [List.map_append, List.map_cons, List.append_assoc, List.singleton_append]

private theorem xorMatch_dedup_skip_inv {mclr3 mclr2 : List (BitVec 32)}
    {k w ua_out : Nat}
    (hk1_lt : k + 1 < ua_out) (hua_le : ua_out ≤ mclr2.length) (hk1_m3 : k + 1 < mclr3.length)
    (htail3 : ∀ j, k ≤ j → j < ua_out → mclr3[j]? = mclr2[j]?)
    (heq_c : mclr3[k]'(by omega) = mclr3[k + 1]'hk1_m3)
    (hxor3 : ∀ α, xorEvalList α (List.map BitVec.toNat
      (List.take w mclr3 ++ List.take (ua_out - k) (List.drop k mclr2))) =
      xorEvalList α (List.map BitVec.toNat (List.take ua_out mclr2))) :
    ∀ α, xorEvalList α (List.map BitVec.toNat
      (List.take w mclr3 ++ List.take (ua_out - (k + 2)) (List.drop (k + 2) mclr2))) =
      xorEvalList α (List.map BitVec.toNat (List.take ua_out mclr2)) := by
  intro α
  have h1 := htail3 k (Nat.le_refl _) (by omega)
  have h2 := htail3 (k + 1) (by omega) hk1_lt
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
    Option.some.injEq] at h1 h2
  have heq_k : mclr2[k]'(by omega) = mclr2[k + 1]'(by omega) := by rw [← h1, ← h2, heq_c]
  rw [← hxor3 α]
  have hdk : List.take (ua_out - k) (List.drop k mclr2) =
      mclr2[k]'(by omega) :: mclr2[k]'(by omega) ::
        List.take (ua_out - (k + 2)) (List.drop (k + 2) mclr2) := by
    rw [show ua_out - k = (ua_out - (k + 2)) + 2 by omega,
      List.drop_eq_getElem_cons (by omega), List.take_succ_cons,
      List.drop_eq_getElem_cons (by omega), List.take_succ_cons, heq_k]
  rw [hdk, List.map_append, List.map_append, List.map_cons, List.map_cons, xorEvalList_dedup_step]

private theorem xorMatch_lit_xor_flip_lt {r f : BitVec 32} {n : Nat}
    (hr : r.toNat < 2 * n) (hf : f = 0#32 ∨ f = 1#32) : (r ^^^ f).toNat < 2 * n := by
  rcases hf with rfl | rfl
  · simpa using hr
  · have h1 : (r ^^^ 1#32) >>> 1 = r >>> 1 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]
      have hb : (1#32 : BitVec 32).getLsbD (1 + i) = false := by
        simp [BitVec.getLsbD_ofNat, Nat.testBit, Nat.shiftRight_add]
      rw [hb, Bool.xor_false]
    have ha : ((r ^^^ 1#32) >>> 1).toNat = (r ^^^ 1#32).toNat / 2 := by
      rw [BitVec.toNat_ushiftRight]; simp [Nat.shiftRight_eq_div_pow]
    have hb : (r >>> 1).toNat = r.toNat / 2 := by
      rw [BitVec.toNat_ushiftRight]; simp [Nat.shiftRight_eq_div_pow]
    have h2 : (r ^^^ 1#32).toNat / 2 = r.toNat / 2 := by rw [← ha, h1, hb]
    omega

private theorem xorMatch_evalLitVal_xor_flip (α : Nat → Bool) {r f : BitVec 32}
    (hf : f = 0#32 ∨ f = 1#32) :
    evalLitVal α (r ^^^ f).toNat = ((f == 1#32) != evalLitVal α r.toNat) := by
  rcases hf with rfl | rfl
  · simp
  · have h := xorEvalList_litNeg_head α r.toNat []
    simp only [xorEvalList, litNeg, List.foldr_cons, List.foldr_nil, Bool.bne_false] at h
    rw [BitVec.toNat_xor r 1#32, show (1#32 : BitVec 32).toNat = 1 from rfl, h]; simp

private theorem xorMatch_evalList_append_step (α : Nat → Bool) (xs : List Nat) (y : Nat) :
    xorEvalList α (xs ++ [y]) = (xorEvalList α xs != evalLitVal α y) := by
  induction xs with
  | nil => simp [xorEvalList]
  | cons x xs ih =>
    change (evalLitVal α x != xorEvalList α (xs ++ [y])) =
      ((evalLitVal α x != xorEvalList α xs) != evalLitVal α y)
    rw [ih, Bool.bne_assoc]

private theorem xorMatch_take_succ_map {scr0 : List (BitVec 32)} {ent j : Nat} {gl : BitVec 32}
    (hj : ent + 2 + j < scr0.length) (hgl : scr0[ent + 2 + j]? = some gl) :
    List.map BitVec.toNat (List.take (j + 1) (List.drop (ent + 2) scr0)) =
      List.map BitVec.toNat (List.take j (List.drop (ent + 2) scr0)) ++ [gl.toNat] := by
  have hj' : j < (List.drop (ent + 2) scr0).length := by simp; omega
  rw [List.take_succ_eq_append_getElem hj', List.getElem_drop,
    show scr0[ent + 2 + j]'(by omega) = gl from
      Option.some.inj (by rw [← List.getElem?_eq_getElem, hgl]), List.map_append]; rfl

private theorem xorMatch_par_cases (r : BitVec 32) : r &&& 1#32 = 0#32 ∨ r &&& 1#32 = 1#32 := by
  have hle : (r &&& 1#32).toNat ≤ 1 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl]
    exact Nat.and_le_right
  rcases (by omega : (r &&& 1#32).toNat = 0 ∨ (r &&& 1#32).toNat = 1) with h0 | h0
  · exact Or.inl (BitVec.eq_of_toNat_eq h0)
  · exact Or.inr (BitVec.eq_of_toNat_eq h0)

private theorem bv_get_eq {α : Type _} {l : List α} {i1 i2 : Nat} (h1 : i1 < l.length)
    (h2 : i2 < l.length) (hi : i1 = i2) : l[i1]'h1 = l[i2]'h2 := by subst hi; rfl

private theorem xorMatch_step_unassigned {scr0 mclr : List (BitVec 32)} {ent j ua_out : Nat}
    {flip_neg gl r : BitVec 32} {F_cur : List (List Nat)}
    (hj : ent + 2 + j < scr0.length) (hgl : scr0[ent + 2 + j]? = some gl)
    (hua_m : ua_out < mclr.length) (heq : LitEquiv (cnfOfClauses F_cur) gl.toNat r.toNat)
    (hf : flip_neg = 0#32 ∨ flip_neg = 1#32)
    (hinv : ∀ α, Std.Sat.CNF.Sat α (cnfOfClauses F_cur) →
      ((flip_neg == 1#32) != xorEvalList α (List.map BitVec.toNat (List.take ua_out mclr))) =
      xorEvalList α (List.map BitVec.toNat (List.take j (List.drop (ent + 2) scr0)))) :
    (((flip_neg ^^^ (r &&& 1#32)) = 0#32 ∨ (flip_neg ^^^ (r &&& 1#32)) = 1#32) ∧
     ∀ α, Std.Sat.CNF.Sat α (cnfOfClauses F_cur) →
       (((flip_neg ^^^ (r &&& 1#32)) == 1#32) != xorEvalList α (List.map BitVec.toNat
           (List.take (ua_out + 1) (mclr.set ua_out (r &&& ~~~1#32))))) =
       xorEvalList α (List.map BitVec.toNat (List.take (j + 1) (List.drop (ent + 2) scr0)))) := by
  have hpar := xorMatch_par_cases r
  refine ⟨by rcases hf with rfl | rfl <;> rcases hpar with h0 | h0 <;> rw [h0] <;> simp, ?_⟩
  intro α hα
  have hev0 := xorEvalList_even_step α r []
  simp only [List.nil_append, xorEvalList, List.foldr_cons, List.foldr_nil, Bool.bne_false] at hev0
  have hf1 : ((flip_neg ^^^ (r &&& 1#32)) == 1#32) =
      ((flip_neg == 1#32) != (r &&& 1#32 == 1#32)) := by
    rcases hf with rfl | rfl <;> rcases hpar with h0 | h0 <;> rw [h0] <;> decide
  rw [list_take_set_append mclr hua_m, List.map_append, List.map_cons, List.map_nil,
    xorMatch_evalList_append_step, xorMatch_take_succ_map hj hgl, xorMatch_evalList_append_step,
    ← hinv α hα, litEquiv_eval hα heq, ← hev0, hf1]
  cases (flip_neg == 1#32) <;> cases (r &&& 1#32 == 1#32) <;>
    cases xorEvalList α (List.map BitVec.toNat (List.take ua_out mclr)) <;>
    cases evalLitVal α (r &&& ~~~1#32).toNat <;> rfl

private theorem xorMatch_step_const {scr0 mclr : List (BitVec 32)} {ent j ua_out : Nat}
    {flip_neg gl r flip' : BitVec 32} {F_cur : List (List Nat)}
    (hj : ent + 2 + j < scr0.length) (hgl : scr0[ent + 2 + j]? = some gl)
    (heq : LitEquiv (cnfOfClauses F_cur) gl.toNat r.toNat)
    (hstep : ∀ α, Std.Sat.CNF.Sat α (cnfOfClauses F_cur) →
      (flip' == 1#32) = ((flip_neg == 1#32) != evalLitVal α r.toNat))
    (hinv : ∀ α, Std.Sat.CNF.Sat α (cnfOfClauses F_cur) →
      ((flip_neg == 1#32) != xorEvalList α (List.map BitVec.toNat (List.take ua_out mclr))) =
      xorEvalList α (List.map BitVec.toNat (List.take j (List.drop (ent + 2) scr0)))) :
    ∀ α, Std.Sat.CNF.Sat α (cnfOfClauses F_cur) →
      ((flip' == 1#32) != xorEvalList α (List.map BitVec.toNat (List.take ua_out mclr))) =
      xorEvalList α (List.map BitVec.toNat (List.take (j + 1) (List.drop (ent + 2) scr0))) := by
  intro α hα
  rw [xorMatch_take_succ_map hj hgl, xorMatch_evalList_append_step, ← hinv α hα,
    litEquiv_eval hα heq, hstep α hα]
  cases (flip_neg == 1#32) <;> cases evalLitVal α r.toNat <;>
    cases xorEvalList α (List.map BitVec.toNat (List.take ua_out mclr)) <;> rfl

private theorem xorMatch_mem_set_rm {c : FullCfg} {s : FullState} {repr : List (BitVec 32)}
    {mclr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {idx1 idx2 : Nat}
    {v1 v2 : BitVec 32}
    (hm : (FullMem c { s with core := { s.core with
      repr := repr, min_clr := mclr.set idx1 v1 } } ⋆ R) m)
    (hidx : idx1 = idx2) (hv : v1 = v2) :
    (FullMem c { s with core := { s.core with
      repr := repr, min_clr := mclr.set idx2 v2 } } ⋆ R) m :=
  hidx ▸ hv ▸ hm

private def xorMatchLoop1Inv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (scr0 : List (BitVec 32)) (ent : Nat) (R : Mem 64 → Prop)
    (j ua_out : Nat) (flip_neg : BitVec 32) (mc : Mem 64) : Prop :=
  ua_out ≤ j ∧ ∃ (repr1 mclr1 : List (BitVec 32)),
    repr1.length = 2 * c.max_vars ∧ mclr1.length = c.max_vars ∧
    FullCongReprInv F_cur (2 * s.core.cur_vars) repr1 ∧ (flip_neg = 0#32 ∨ flip_neg = 1#32) ∧
    (∀ k, k < ua_out → (mclr1[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (∀ α, Std.Sat.CNF.Sat α (cnfOfClauses F_cur) → ((flip_neg == 1#32) !=
        xorEvalList α (List.map BitVec.toNat (List.take ua_out mclr1))) =
      xorEvalList α (List.map BitVec.toNat (List.take j (List.drop (ent + 2) scr0)))) ∧
    (FullMem c { s with core := { s.core with repr := repr1, min_clr := mclr1 } } ⋆ R) mc

private def xorMatchDedupInv (c : FullCfg) (s1 : FullState) (mclr2 : List (BitVec 32))
    (ua_out : Nat) (R : Mem 64 → Prop) (k w : Nat) (mc : Mem 64) : Prop :=
  k ≤ ua_out ∧ w ≤ k ∧ ∃ mclr3 : List (BitVec 32), mclr3.length = c.max_vars ∧
    (∀ j, k ≤ j → j < ua_out → mclr3[j]? = mclr2[j]?) ∧
    (∀ j, j < w → (mclr3[j]?.getD 0#32).toNat < 2 * s1.core.cur_vars) ∧
    (∀ α, xorEvalList α (List.map BitVec.toNat
        (List.take w mclr3 ++ List.take (ua_out - k) (List.drop k mclr2))) =
      xorEvalList α (List.map BitVec.toNat (List.take ua_out mclr2))) ∧
    (FullMem c { s1 with core := { s1.core with min_clr := mclr3 } } ⋆ R) mc

private theorem xorMatch_sound_post {F_cur : List (List Nat)}
    {scr0 mclr1 mclr2 mclr3 tmp : List (BitVec 32)} {lhs lhs_rep flip_neg mword : BitVec 32}
    {ent ua ua_out cur_vars : Nat}
    (hxor : XorListGateDef (cnfOfClauses F_cur) lhs.toNat
      (List.map BitVec.toNat (List.take (congGateArity mword) (List.drop (ent + 2) scr0))))
    (heq_lhs : LitEquiv (cnfOfClauses F_cur) lhs.toNat lhs_rep.toNat)
    (hf : flip_neg = 0#32 ∨ flip_neg = 1#32)
    (hl1 : ∀ α, Std.Sat.CNF.Sat α (cnfOfClauses F_cur) →
      ((flip_neg == 1#32) != xorEvalList α (List.map BitVec.toNat (List.take ua_out mclr1))) =
      xorEvalList α (List.map BitVec.toNat
        (List.take (congGateArity mword) (List.drop (ent + 2) scr0))))
    (hperm : (List.take ua_out mclr2).Perm (List.take ua_out mclr1))
    (hdedup : ∀ α, xorEvalList α (List.map BitVec.toNat
        (List.take ua mclr3 ++ List.take (ua_out - ua_out) (List.drop ua_out mclr2))) =
      xorEvalList α (List.map BitVec.toNat (List.take ua_out mclr2)))
    (hua_m3 : ua ≤ mclr3.length) (hua_tmp : ua ≤ tmp.length)
    (heq_tmp : ∀ j, j < ua → mclr3[j]?.getD 0#32 = tmp[j]?.getD 0#32)
    (hlhs_lt : lhs_rep.toNat < 2 * cur_vars) :
    (lhs_rep ^^^ flip_neg).toNat < 2 * cur_vars ∧
    ∀ α, Std.Sat.CNF.Sat α (cnfOfClauses F_cur) →
      evalLitVal α (lhs_rep ^^^ flip_neg).toNat =
        xorEvalList α (List.map BitVec.toNat (List.take ua tmp)) := by
  refine ⟨xorMatch_lit_xor_flip_lt hlhs_lt hf, fun α hα => ?_⟩
  have htake : List.take ua mclr3 = List.take ua tmp := by
    apply List.ext_getElem (by simp; omega)
    intro j hj1 hj2
    have hju : j < ua := by simp only [List.length_take] at hj1; omega
    have hq := heq_tmp j hju
    simp only [List.getElem_take] at hj1 hj2 ⊢
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
      Option.getD_some, Option.getD_some] at hq
    exact hq
  have hdd := hdedup α
  simp only [Nat.sub_self, List.take_zero, List.append_nil, htake] at hdd
  have hp := xorEvalList_perm α (hperm.map BitVec.toNat)
  have h1 := hl1 α hα; have hx := hxor α hα; have heql := litEquiv_eval hα heq_lhs
  rw [xorMatch_evalLitVal_xor_flip α hf, ← heql, hx, ← h1, ← hp, ← hdd]
  cases (flip_neg == 1#32) <;>
    cases xorEvalList α (List.map BitVec.toNat (List.take ua tmp)) <;> rfl

public section

theorem full_cong_xor_match_wp {Γ : Env}
    (hFind : Γ.Has "full_cong_find" Spec.fullCongFindSpec)
    (hSort : Γ.Has "full_sort_u32" Proof.Spec.fullSortU32Spec) :
    ∀ args m Q X,
      Spec.fullCongXorMatchSpec args m Q X → Func.wp Γ full_cong_xor_match_body args m Q X := by
  rintro ⟨h_arg, ent, ua, ⟨⟩⟩ m0 Q X ⟨maxA, c, F0, F_cur, s, scr0, g_len, R,
    _, rfl, hlen, hwit, hclv0, hrepr, hcv2, hg_le, hscr_eq, hgat, htag,
    hua_le, _, hm0, hQ⟩
  obtain ⟨lhs, mword, hlhs, hmword, hlhs_lt, hge_g, har_le, har_ge2, har_le4, hscr_len,
    har_bv, hrhs, hxor⟩ := xorMatch_gate_facts hgat htag
  have hcv_le := hlen.core_ok.cur_vars_le; have hrl := hlen.core_ok.repr_len
  have hml := hlen.core_ok.min_clr_len_arr; have htl := hlen.core_ok.tmp_len_arr
  have hvl := hlen.core_ok.vals_len; have hsl := hlen.scratch_ok.scratch_buf_len
  have hmaxv := c.hmaxv
  have hcv_u64 : s.core.cur_vars < 2 ^ 64 := by unfold dimacsBound at hmaxv; omega
  have hent0_idx : (BitVec.setWidth 64 ent).toNat = ent.toNat := by bv_omega
  have hent1_idx : (BitVec.setWidth 64 ent + 1#64).toNat = ent.toNat + 1 := by bv_omega
  have hent1_scr : (BitVec.setWidth 64 ent + 1#64).toNat < s.scratch.scratch_buf.length := by
    omega
  have hmword_buf : s.scratch.scratch_buf[(BitVec.setWidth 64 ent + 1#64).toNat]'hent1_scr =
      mword := by
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem hent1_scr, hent1_idx, hscr_eq _ (by omega), hmword]
  have hmword_buf2 : s.scratch.scratch_buf[(ent.toNat +
      BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by bv_omega) = mword := by
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem (by bv_omega),
      show (ent.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = ent.toNat + 1 by bv_omega,
      hscr_eq _ (by omega), hmword]
  have hfail : ∀ (repr' mclr' : List (BitVec 32)) (m' : Mem 64),
      repr'.length = 2 * c.max_vars → mclr'.length = c.max_vars →
      FullCongReprInv F_cur (2 * s.core.cur_vars) repr' →
      (FullMem c { s with core := { s.core with repr := repr', min_clr := mclr' } } ⋆ R) m' →
      Q (4294967295#32, ()) m' := fun r' mc' m' hr' hmc' hinv' hm' =>
    hQ 4294967295#32 r' mc' m' hr' hmc' hinv' (fun h => absurd rfl h) hm'
  dsimp only [Func.wp, full_cong_xor_match_body]
  c0_hstraight!; c0_hsplit
  · clear hc; c0_hstraight!; exact hfail s.core.repr s.core.min_clr m0 hrl hml hrepr hm0
  have hua2 := hc; clear hc; c0_hstraight!; c0_hsplit
  · clear hc; c0_hstraight!; exact hfail s.core.repr s.core.min_clr m0 hrl hml hrepr hm0
  have hua4 := hc; clear hc; c0_hstraight!; c0_hsplit
  · exfalso; rw [Nat.mod_eq_of_lt hcv_u64] at hc; bv_omega
  clear hc; c0_hstraight!; c0_hsplit
  · exfalso; rw [Nat.mod_eq_of_lt hcv_u64] at hc; bv_omega
  clear hc; c0_hstraight!; c0_hsplit
  · exfalso; rw [hmword_buf2] at hc; bv_omega
  clear hc; c0_hstraight!; c0_hsplit
  · exfalso; rw [hmword_buf2] at hc; bv_omega
  clear hc; c0_hstraight!; c0_hsplit
  · exfalso; rw [hmword_buf2, Nat.mod_eq_of_lt hcv_u64] at hc; bv_omega
  clear hc
  have hua_ge2 : 2 ≤ ua.toNat := by bv_omega
  have hua_le4 : ua.toNat ≤ 4 := by bv_omega
  c0_hstraight!
  refine wp_loop_group
    (fun n xs mc => n = congGateArity mword - xs.snd.snd.fst.toNat ∧
      xs.snd.snd.fst.toNat ≤ congGateArity mword ∧
      xorMatchLoop1Inv c F_cur s scr0 ent.toNat R
        xs.snd.snd.fst.toNat xs.snd.fst.toNat xs.fst mc) ?_ ?_
  · rintro L1 n ⟨flip_neg, ua_out, j, ⟨⟩⟩ mc hL1
      ⟨rfl, hj_le, hua_j, repr1, mclr1, hrl1, hmcl1, hrepr1, hf1, hm1_lt, hinv1, hmc⟩
    dsimp only [Blocks.get, Member.here]; dsimp only at hj_le hua_j hm1_lt hinv1
    c0_hstraight!; c0_hsplit
    · have hj_lt := hc; clear hc; rw [hmword_buf2] at hj_lt
      have hj_nat : j.toNat < congGateArity mword := by rw [← har_bv]; bv_omega
      have hgl_idx : (BitVec.setWidth 64 ent + 2#64 + BitVec.setWidth 64 j).toNat =
          ent.toNat + 2 + j.toNat := by bv_omega
      have hgl_buf_lt : (BitVec.setWidth 64 ent + 2#64 + BitVec.setWidth 64 j).toNat <
          s.scratch.scratch_buf.length := by omega
      obtain ⟨gl, hgl_eq, hgl_cv⟩ := hrhs j.toNat hj_nat
      have hgl_buf : s.scratch.scratch_buf[(BitVec.setWidth 64 ent + 2#64 +
          BitVec.setWidth 64 j).toNat]'hgl_buf_lt = gl := by
        apply Option.some.inj
        rw [← List.getElem?_eq_getElem hgl_buf_lt, hgl_idx, hscr_eq _ (by omega), hgl_eq]
      c0_hstraight!; have hm_focus := ArrayField.repr.focus hmc
      c0_hcall hFind
      · exact ⟨F_cur, 2 * s.core.cur_vars, repr1, _, hrepr1,
          by change (s.scratch.scratch_buf[(BitVec.setWidth 64 ent + 2#64 +
               BitVec.setWidth 64 j).toNat]'hgl_buf_lt).toNat < 2 * s.core.cur_vars
             rw [hgl_buf]; exact hgl_cv,
          hm_focus, fun r repr2 m2 hrl2 hrepr2 _ hr_lt heq_gl hm2 => by
            change LitEquiv (cnfOfClauses F_cur)
              (s.scratch.scratch_buf[(BitVec.setWidth 64 ent + 2#64 +
                BitVec.setWidth 64 j).toNat]'hgl_buf_lt).toNat r.toNat at heq_gl
            rw [hgl_buf] at heq_gl
            have hmc2 := ArrayField.repr.unfocus hm2
            change (FullMem c { s with core := { s.core with repr := repr2, min_clr := mclr1 } } ⋆
              R) m2 at hmc2
            have hr_vl : r.toNat < s.core.vals.length := by bv_omega
            have hr_ev : (r &&& ~~~1#32).toNat < 2 * s.core.cur_vars := by
              have hle : (r &&& ~~~1#32).toNat ≤ r.toNat := by
                rw [BitVec.toNat_and]; exact Nat.and_le_left
              omega
            c0_hstraight!
            refine wp_join_group
              (fun xs mj => xs.snd.snd = () ∧
                xorMatchLoop1Inv c F_cur s scr0 ent.toNat R
                  (j.toNat + 1) xs.snd.fst.toNat xs.fst mj) ?_ ?_
            · rintro _ ⟨fn', uao', ⟨⟩⟩ mj ⟨_, hinvj⟩
              dsimp only [Blocks.get, Member.here]; c0_hstraight!
              have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
              exact hL1 (congGateArity mword - (j + 1#32).toNat) (fn', uao', j + 1#32, ()) mj
                (by bv_omega) ⟨rfl, by bv_omega, hj1 ▸ hinvj⟩
            · intro J1 hJ1; c0_hsplit
              · have hv_ne0 := hc; clear hc; c0_hstraight!
                refine wp_join_group
                  (fun (xs : Tup Val [i32]) mk => xs.snd = () ∧
                    xorMatchLoop1Inv c F_cur s scr0 ent.toNat R
                      (j.toNat + 1) ua_out.toNat xs.fst mk) ?_ ?_
                · rintro _ ⟨fn', ⟨⟩⟩ mk ⟨_, hinvk⟩
                  dsimp only [Blocks.get, Member.here]; c0_hstraight!
                  exact hJ1 (fn', ua_out, ()) mk ⟨rfl, hinvk⟩
                · intro J2 hJ2
                  have hv_dom := hwit.vals_domain r.toNat hr_lt
                  rw [List.getElem?_eq_getElem hr_vl, Option.getD_some] at hv_dom
                  have hv_ne0' : BitVec.signExtend 32 (s.core.vals[r.toNat]'hr_vl) ≠ 0#32 :=
                    fun h => hv_ne0 h
                  have hv_ne0b := bv8_ne0_of_signExtend32 hv_dom hv_ne0'
                  c0_hsplit
                  · have hsgt := hc; clear hc; c0_hstraight!
                    have hv1 : s.core.vals[r.toNat]?.getD 0#8 = 1#8 := by
                      rw [List.getElem?_eq_getElem hr_vl, Option.getD_some]
                      exact bv8_eq1_of_signExtend32_sgt0 hv_dom hsgt
                    refine hJ2 (flip_neg ^^^ 1#32, ()) m2 ⟨rfl, by omega, repr2, mclr1, by omega,
                      hmcl1, hrepr2, by rcases hf1 with rfl | rfl <;> decide, hm1_lt,
                      xorMatch_step_const (by omega) hgl_eq heq_gl (fun α hα => by
                          rw [entails_eval_true (vals1_entails hwit hclv0 hr_lt hv1) hα]
                          rcases hf1 with rfl | rfl <;> decide) hinv1, hmc2⟩
                  · have hsgt := hc; clear hc; c0_hstraight!
                    have hvff : s.core.vals[r.toNat]?.getD 0#8 = 255#8 := by
                      rw [List.getElem?_eq_getElem hr_vl, Option.getD_some]
                      exact bv8_ne0_not_signExtend32_sgt0_eqff hv_dom hv_ne0b (by rw [hsgt]; decide)
                    exact hJ2 (flip_neg, ()) m2 ⟨rfl, by omega, repr2, mclr1, by omega, hmcl1,
                      hrepr2, hf1, hm1_lt, xorMatch_step_const (by omega) hgl_eq heq_gl
                        (fun α hα => by
                          rw [entails_neg_eval_false (valsff_entails_neg hwit hclv0 hr_lt hvff) hα]
                          rcases hf1 with rfl | rfl <;> decide) hinv1, hmc2⟩
              · have hv0 := hc; clear hc
                have hua_m : (BitVec.setWidth 64 ua_out).toNat < mclr1.length := by bv_omega
                c0_hstraight!
                have hstep := xorMatch_step_unassigned (by omega) hgl_eq (by omega) heq_gl hf1 hinv1
                have hmc_s := xorMatch_mem_set_rm (c := c) (s := s) (repr := repr2) (mclr := mclr1)
                  (idx1 := (BitVec.setWidth 64 ua_out).toNat) (idx2 := ua_out.toNat)
                  (v2 := r &&& ~~~1#32) (by assumption) (by bv_omega) (by bv_omega)
                refine hJ1 (flip_neg ^^^ (r &&& 1#32), ua_out + 1#32, ()) _ ⟨rfl, by bv_omega,
                  repr2, mclr1.set ua_out.toNat (r &&& ~~~1#32), by omega, by simp [hmcl1],
                  hrepr2, hstep.1, fun k hk => ?_, ?_, hmc_s⟩
                · by_cases hku : k = ua_out.toNat
                  · subst hku; rw [List.getElem?_eq_getElem (by simp [hmcl1]; omega),
                      Option.getD_some, List.getElem_set_self]; exact hr_ev
                  · rw [List.getElem?_set_ne (by omega)]; exact hm1_lt k (by bv_omega)
                · rw [show (ua_out + 1#32).toNat = ua_out.toNat + 1 by bv_omega]; exact hstep.2
        ⟩
    · have hj_not := hc; clear hc; rw [hmword_buf2] at hj_not
      have hj_eq : j.toNat = congGateArity mword := by rw [← har_bv]; bv_omega
      rw [hj_eq] at hua_j hinv1; c0_hstraight!; c0_hsplit
      · clear hc; c0_hstraight!; exact hfail repr1 mclr1 mc hrl1 hmcl1 hrepr1 hmc
      have hua_le_out := hc; clear hc
      let s1 : FullState := { s with core := { s.core with repr := repr1, min_clr := mclr1 } }
      c0_hstraight!
      refine wp_join_group
        (fun xs m2 => xs = () ∧ ∃ mclr2 : List (BitVec 32), mclr2.length = c.max_vars ∧
          (List.take ua_out.toNat mclr2).Perm (List.take ua_out.toNat mclr1) ∧
          (∀ k, k < ua_out.toNat → (mclr2[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
          (FullMem c { s1 with core := { s1.core with min_clr := mclr2 } } ⋆ R) m2) ?_ ?_
      · rintro _ ⟨⟩ m2 ⟨_, mclr2, hmcl2, hperm, hm2_lt, hm2⟩
        dsimp only [Blocks.get, Member.here]; c0_hstraight!
        refine wp_loop_group
          (fun nk xsk mk => nk = ua_out.toNat - xsk.fst.toNat ∧
            xorMatchDedupInv c s1 mclr2 ua_out.toNat R xsk.fst.toNat xsk.snd.fst.toNat mk) ?_ ?_
        · rintro L2 nk ⟨k, w, ⟨⟩⟩ mk hL2
            ⟨rfl, hk_le, hwk, mclr3, hmcl3, htail3, hm3_lt, hxor3, hmk⟩
          dsimp only [Blocks.get, Member.here]; dsimp only at hk_le hwk htail3 hm3_lt hxor3
          c0_hstraight!; c0_hsplit
          · have hk_lt := hc; clear hc; have hk_nat : k.toNat < ua_out.toNat := by bv_omega
            refine wp_join_group
              (fun xs mj => k.toNat < xs.fst.toNat ∧
                xorMatchDedupInv c s1 mclr2 ua_out.toNat R xs.fst.toNat xs.snd.fst.toNat mj) ?_ ?_
            · rintro _ ⟨k', w', ⟨⟩⟩ mj ⟨hk_lt', hinv2⟩
              c0_hstraight!
              exact hL2 (ua_out.toNat - k'.toNat) (k', w', ()) mj (by bv_omega) ⟨rfl, hinv2⟩
            · intro Jd1 hJd1
              refine wp_join_group
                (fun xs mj => xs = () ∧ xorMatchDedupInv c s1 mclr2 ua_out.toNat R
                  k.toNat w.toNat mj) ?_ ?_
              · rintro _ ⟨⟩ mj ⟨_, _, hwk4, mclr4, hmcl4, htail4, hm4_lt, hxor4, hmj⟩
                dsimp only [Blocks.get, Member.here]
                have hw_m4 : (BitVec.setWidth 64 w).toNat < mclr4.length := by bv_omega
                have hk_m4 : (BitVec.setWidth 64 k).toNat < mclr4.length := by bv_omega
                c0_hstraight!
                have hpush := xorMatch_dedup_push_inv hmcl4 hwk4 (by omega) hk_nat
                  (by omega) (by omega) htail4 hxor4
                have hm_s := xorMatch_mem_set_rm (c := c) (s := s1) (repr := s1.core.repr)
                  (mclr := mclr4) (idx1 := (BitVec.setWidth 64 w).toNat) (idx2 := w.toNat)
                  (v2 := mclr4[k.toNat]'(by omega)) (by assumption) (by bv_omega) rfl
                refine hJd1 (k + 1#32, w + 1#32, ()) _ ⟨by bv_omega, by bv_omega, by bv_omega,
                  mclr4.set w.toNat (mclr4[k.toNat]'(by omega)), by simp [hmcl4],
                  fun j hj1 hj2 => hpush.1 j (by bv_omega) hj2, fun j hj => ?_,
                  by rw [show (k + 1#32).toNat = k.toNat + 1 by bv_omega,
                    show (w + 1#32).toNat = w.toNat + 1 by bv_omega]; exact hpush.2, hm_s⟩
                by_cases hjw : j = w.toNat
                · subst hjw; rw [List.getElem?_eq_getElem (by simp [hmcl4]; omega),
                    Option.getD_some, List.getElem_set_self]
                  have hq := htail4 k.toNat (Nat.le_refl _) hk_nat
                  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
                    Option.some_inj] at hq
                  rw [hq]; have hm2k := hm2_lt k.toNat hk_nat
                  rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hm2k
                · rw [List.getElem?_set_ne (by omega)]; exact hm4_lt j (by bv_omega)
              · intro Jd2 hJd2; c0_hstraight!; c0_hsplit
                · have hk1_lt := hc; clear hc
                  have hk1_nat : k.toNat + 1 < ua_out.toNat := by bv_omega
                  have hk_m3 : (BitVec.setWidth 64 k).toNat < mclr3.length := by bv_omega
                  have hk1_m3 : (BitVec.setWidth 64 (k + 1#32)).toNat < mclr3.length := by bv_omega
                  c0_hstraight!; c0_hsplit
                  · have heq_pair := hc; clear hc; c0_hstraight!
                    have heq_p' : mclr3[k.toNat]'(by omega) = mclr3[k.toNat + 1]'(by omega) :=
                      (bv_get_eq _ _ (by bv_omega)).trans
                        (heq_pair.trans (bv_get_eq _ _ (by bv_omega)))
                    have hskip := xorMatch_dedup_skip_inv hk1_nat (by omega) (by omega)
                      htail3 heq_p' hxor3
                    exact hJd1 (k + 2#32, w, ()) mk ⟨by bv_omega, by bv_omega, by bv_omega,
                      mclr3, hmcl3, fun j hj1 hj2 => htail3 j (by bv_omega) hj2, hm3_lt,
                      by rw [show (k + 2#32).toNat = k.toNat + 2 by bv_omega]; exact hskip, hmk⟩
                  · clear hc; c0_hstraight!
                    exact hJd2 () mk ⟨rfl, hk_le, hwk, mclr3, hmcl3, htail3, hm3_lt, hxor3, hmk⟩
                · clear hc; c0_hstraight!
                  exact hJd2 () mk ⟨rfl, hk_le, hwk, mclr3, hmcl3, htail3, hm3_lt, hxor3, hmk⟩
          · have hk_not := hc; clear hc; have hk_eq : k.toNat = ua_out.toNat := by bv_omega
            c0_hstraight!; c0_hsplit
            · clear hc; c0_hstraight!; exact hfail repr1 mclr3 mk hrl1 hmcl3 hrepr1 hmk
            have hw_eq := hc; clear hc; have hw_nat : w.toNat = ua.toNat := by bv_omega
            c0_hstraight!
            refine wp_loop_group
              (fun nc xsc mc3 => mc3 = mk ∧ xsc.fst.toNat ≤ ua.toNat ∧
                nc = ua.toNat - xsc.fst.toNat ∧
                ∀ j, j < xsc.fst.toNat → mclr3[j]?.getD 0#32 = s.core.tmp[j]?.getD 0#32) ?_ ?_
            · rintro L3 nc ⟨jc, ⟨⟩⟩ mc3 hL3 ⟨rfl, hjc_le, rfl, heq_jc⟩
              dsimp only [Blocks.get, Member.here]; dsimp only at hjc_le heq_jc; c0_hstraight!
              c0_hsplit
              · have hjc_lt := hc; clear hc; have hjc_nat : jc.toNat < ua.toNat := by bv_omega
                have hjc_m3 : (BitVec.setWidth 64 jc).toNat < mclr3.length := by bv_omega
                have hjc_tm : (BitVec.setWidth 64 jc).toNat < s.core.tmp.length := by bv_omega
                c0_hstraight!; c0_hsplit
                · clear hc; c0_hstraight!; exact hfail repr1 mclr3 mc3 hrl1 hmcl3 hrepr1 hmk
                · have heq_j := hc; clear hc; c0_hstraight!
                  refine hL3 (ua.toNat - (jc + 1#32).toNat) (jc + 1#32, ()) mc3 (by bv_omega)
                    ⟨rfl, by bv_omega, rfl, fun j hj => ?_⟩
                  by_cases hjc : j = jc.toNat
                  · subst hjc
                    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
                      Option.getD_some, Option.getD_some]
                    exact (bv_get_eq _ _ (by bv_omega)).trans
                      (heq_j.trans (bv_get_eq _ _ (by bv_omega)))
                  · exact heq_jc j (by bv_omega)
              · have hjc_not := hc; clear hc; have hjc_eq : jc.toNat = ua.toNat := by bv_omega
                rw [hjc_eq] at heq_jc
                have hent_scr : (BitVec.setWidth 64 ent).toNat < s.scratch.scratch_buf.length := by
                  omega
                have hlhs_buf : s.scratch.scratch_buf[(BitVec.setWidth 64 ent).toNat]'hent_scr =
                    lhs := by
                  apply Option.some.inj
                  rw [← List.getElem?_eq_getElem hent_scr, hent0_idx, hscr_eq _ (by omega), hlhs]
                c0_hstraight!; have hm_focus := ArrayField.repr.focus hmk
                c0_hcall hFind
                · exact ⟨F_cur, 2 * s.core.cur_vars, repr1, _, hrepr1,
                    by change (s.scratch.scratch_buf[(BitVec.setWidth 64
                         ent).toNat]'hent_scr).toNat < 2 * s.core.cur_vars
                       rw [hlhs_buf]; exact hlhs_lt,
                    hm_focus, fun lhs_rep repr' m' hrl' hrepr' _ hr_lt heq_lhs hm' => by
                      change LitEquiv (cnfOfClauses F_cur)
                        (s.scratch.scratch_buf[(BitVec.setWidth 64 ent).toNat]'hent_scr).toNat
                        lhs_rep.toNat at heq_lhs
                      rw [hlhs_buf] at heq_lhs
                      have hm_uf := ArrayField.repr.unfocus hm'
                      change (FullMem c { s with core := { s.core with
                        repr := repr', min_clr := mclr3 } } ⋆ R) m' at hm_uf
                      c0_hstraight!
                      have hdd_eq : ∀ α, xorEvalList α (List.map BitVec.toNat (List.take ua.toNat
                          mclr3 ++ List.take (ua_out.toNat - ua_out.toNat) (List.drop ua_out.toNat
                          mclr2))) = xorEvalList α (List.map BitVec.toNat (List.take ua_out.toNat
                          mclr2)) := by
                        intro α; have h := hxor3 α; rw [hk_eq, hw_nat] at h; exact h
                      have hsound := xorMatch_sound_post hxor heq_lhs hf1 hinv1 hperm
                        hdd_eq (by omega) (by omega) heq_jc hr_lt
                      refine hQ (lhs_rep ^^^ flip_neg) repr' mclr3 m' (by omega) hmcl3 hrepr'
                        (fun _ => ⟨hua_ge2, hua_le4, hsound⟩) ?_
                      exact hm_uf⟩
            · intro J3 hJ3; exact hJ3 ua.toNat (0#32, ()) mk ⟨rfl, Nat.zero_le _, rfl,
                fun _ h => absurd h (Nat.not_lt_zero _)⟩
        · intro J2 hJ2; c0_hstraight!
          exact hJ2 ua_out.toNat (0#32, 0#32, ()) m2 ⟨rfl, Nat.zero_le _, Nat.zero_le _,
            mclr2, hmcl2, fun _ _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _),
            fun _ => rfl, hm2⟩
      · intro Js hJs; c0_hstraight!; c0_hsplit
        · clear hc; have hm_focus := ArrayField.min_clr.focus hmc
          c0_hcall hSort
          · exact ⟨mclr1, _, by omega, hm_focus, fun mclr2 m2 hmcl2 hperm _ hm2 => by
              have hm_uf := ArrayField.min_clr.unfocus hm2
              change (FullMem c { s1 with core := { s1.core with min_clr := mclr2 } } ⋆ R) m2
                at hm_uf
              c0_hstraight!
              refine hJs () m2 ⟨rfl, mclr2, by omega, hperm, fun k hk => ?_, hm_uf⟩
              have hmem : mclr2[k]'(by omega) ∈ List.take ua_out.toNat mclr2 := by
                have ht : (List.take ua_out.toNat mclr2)[k]'(by simp; omega) =
                    mclr2[k]'(by omega) := List.getElem_take
                rw [← ht]; exact List.getElem_mem _
              obtain ⟨idx, hidx1, hidx2⟩ := List.mem_iff_getElem.mp (hperm.mem_iff.mp hmem)
              simp only [List.length_take, List.getElem_take] at hidx1 hidx2
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hidx2]
              have q := hm1_lt idx (by omega)
              rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at q⟩
        · exfalso; bv_omega
  · intro J hJ; c0_hstraight!; exact hJ (congGateArity mword) (0#32, 0#32, 0#32, ()) m0
      ⟨rfl, Nat.zero_le _, Nat.zero_le _, s.core.repr, s.core.min_clr, hrl, hml, hrepr,
        Or.inl rfl, fun _ h => absurd h (Nat.not_lt_zero _),
        fun α _ => by simp [xorEvalList], hm0⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence
