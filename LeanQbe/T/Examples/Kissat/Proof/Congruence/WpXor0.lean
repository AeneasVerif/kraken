/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Inv
public import LeanQbe.T.Examples.Kissat.Src.Congruence

/-!
# Canonical WP Proofs for Congruence XOR Helpers (`#6–#8`)

Proves `Func.wp` against flat `CanonicalEnv` for:
- `6. full_cong_emit_xor` (`Spec.fullCongEmitXorSpec`)
- `7. full_cong_has_clause_k` (`Spec.fullCongHasClauseKSpec`)
- `8. full_cong_emit_xor4` (`Spec.fullCongEmitXor4Spec`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open Std Std.Sat
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics

local macro "cong_split" : tactic =>
  `(tactic| (
    c0_hsteps_nogrp
    repeat (
      refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
      c0_hsteps_nogrp)
    c0_hsplit))

public section

/-! ## Shared XOR Semantic Helpers -/

private theorem nat_xor1_cases (l : Nat) :
    (l ^^^ 1) / 2 = l / 2 ∧ (l ^^^ 1) % 2 = 1 - l % 2 := by
  have h1 : ∀ k, (1 : Nat).testBit (k + 1) = false := fun k => by
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
    have hp : 2 ≤ 2 ^ (k + 1) :=
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hd : 1 / 2 ^ (k + 1) = 0 := Nat.div_eq_of_lt (by omega)
    simp [hd]
  have hdiv : (l ^^^ 1) / 2 = l / 2 := by
    apply Nat.eq_of_testBit_eq; intro k
    rw [Nat.testBit_div_two, Nat.testBit_div_two, Nat.testBit_xor, h1, Bool.xor_false]
  have hmod : (l ^^^ 1) % 2 = 1 - l % 2 := by
    have h0 : (l ^^^ 1).testBit 0 = !l.testBit 0 := by
      rw [Nat.testBit_xor, show Nat.testBit 1 0 = true from rfl, Bool.xor_true]
    simp only [Nat.testBit_zero] at h0
    rcases Nat.mod_two_eq_zero_or_one l with hm | hm <;>
      rcases Nat.mod_two_eq_zero_or_one (l ^^^ 1) with hn | hn <;> simp_all
  exact ⟨hdiv, hmod⟩

private theorem evalLitVal_litNeg (α : Nat → Bool) (l : Nat) :
    evalLitVal α (litNeg l) = !evalLitVal α l := by
  unfold evalLitVal litNeg litVar litSign
  obtain ⟨hdiv, hmod⟩ := nat_xor1_cases l
  rw [hdiv, hmod]
  cases α (l / 2) <;> rcases Nat.mod_two_eq_zero_or_one l with hm | hm <;> simp [hm]

private theorem xorGateDef_eval {f : CNF Nat} {g a b : Nat}
    (hxor : XorGateDef f g a b) {α : Nat → Bool} (hα : f.Sat α) :
    evalLitVal α g = (evalLitVal α a != evalLitVal α b) := by
  rcases hxor with ⟨h1, h2, h3, h4⟩
  have c1 : (evalLitVal α g || evalLitVal α (litNeg a) || evalLitVal α b) = true := by
    have := (CNF.entails_clause_def.mp h1) α hα
    rw [← clauseEvalVal_iff] at this; simpa [clauseEvalVal, Bool.or_assoc] using this
  have c2 : (evalLitVal α g || evalLitVal α a || evalLitVal α (litNeg b)) = true := by
    have := (CNF.entails_clause_def.mp h2) α hα
    rw [← clauseEvalVal_iff] at this; simpa [clauseEvalVal, Bool.or_assoc] using this
  have c3 : (evalLitVal α (litNeg g) || evalLitVal α a || evalLitVal α b) = true := by
    have := (CNF.entails_clause_def.mp h3) α hα
    rw [← clauseEvalVal_iff] at this; simpa [clauseEvalVal, Bool.or_assoc] using this
  have c4 : (evalLitVal α (litNeg g) || evalLitVal α (litNeg a) ||
      evalLitVal α (litNeg b)) = true := by
    have := (CNF.entails_clause_def.mp h4) α hα
    rw [← clauseEvalVal_iff] at this; simpa [clauseEvalVal, Bool.or_assoc] using this
  rw [evalLitVal_litNeg] at c1 c2 c3 c4
  cases hg : evalLitVal α g <;> cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;>
    simp_all

private theorem xorEvalList_cons_pair (α : Nat → Bool) (a b : Nat) :
    xorEvalList α [a, b] = (evalLitVal α a != evalLitVal α b) := by
  unfold xorEvalList
  simp only [List.foldr_cons, List.foldr_nil]
  cases evalLitVal α a <;> cases evalLitVal α b <;> rfl

private theorem bv32_bit0_eval (α : Nat → Bool) (x : BitVec 32) :
    evalLitVal α x.toNat =
      (evalLitVal α (x &&& ~~~1#32).toNat != decide ((x &&& 1#32) ≠ 0#32)) := by
  have hev := m6_bv32_and_not1_toNat x
  rw [hev]
  unfold evalLitVal litVar litSign
  have hdiv : (2 * (x.toNat / 2)) / 2 = x.toNat / 2 := by omega
  have hmod0 : (2 * (x.toNat / 2)) % 2 = 0 := by omega
  have hb0 : decide ((x &&& 1#32) ≠ 0#32) = decide (x.toNat % 2 = 1) := by
    have h1 : (x &&& 1#32).toNat = x.toNat % 2 := by
      rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
    by_cases hm : x.toNat % 2 = 0
    · have hz : (x &&& 1#32) = 0#32 := BitVec.eq_of_toNat_eq (by rw [h1, hm]; rfl)
      simp [hz, hm]
    · have ho : x.toNat % 2 = 1 := by omega
      have hnz : (x &&& 1#32) ≠ 0#32 := fun hz => by
        have := congrArg BitVec.toNat hz; rw [h1, ho] at this; cases this
      simp [hnz, ho]
  rw [hdiv, hmod0, hb0]
  cases α (x.toNat / 2) <;> rcases Nat.mod_two_eq_zero_or_one x.toNat with hm | hm <;> simp [hm]

private theorem bv32_getLsb0_eq_and1 (y : BitVec 32) :
    decide ((y &&& 1#32) ≠ 0#32) = y.getLsbD 0 := by
  have h0 : (y &&& 1#32).toNat = if y.getLsbD 0 then 1 else 0 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod,
      BitVec.getLsbD, Nat.testBit_zero]
    cases hm : y.toNat % 2 == 1 <;> simp_all <;> omega
  cases hg : y.getLsbD 0
  · simp only [hg, Bool.false_eq_true, ↓reduceIte] at h0
    have hz : (y &&& 1#32) = 0#32 := BitVec.eq_of_toNat_eq h0
    simp [hz]
  · simp only [hg, ↓reduceIte] at h0
    have hnz : (y &&& 1#32) ≠ 0#32 := fun hz => by
      have := congrArg BitVec.toNat hz; rw [h0] at this; cases this
    simp [hnz]

private theorem bool_xor3_norm :
    ∀ a0 a1 a2 b0 b1 b2 : Bool,
      ((a0 != b0) = ((a1 != b1) != (a2 != b2))) →
      (a0 != ((b0 != b1) != b2)) = (a1 != a2) := by
  decide

private theorem emit_xor_sem {F_cur : List (List Nat)} {x0 x1 x2 : BitVec 32}
    (hxor : XorGateDef (cnfOfClauses F_cur) (litNeg x0.toNat) x1.toNat x2.toNat) :
    let nx0 := x0 ^^^ 1#32
    let lhs := (nx0 &&& ~~~1#32) ||| ((nx0 ^^^ x1 ^^^ x2) &&& 1#32)
    let r0 := x1 &&& ~~~1#32
    let r1 := x2 &&& ~~~1#32
    XorListGateDef (cnfOfClauses F_cur) lhs.toNat [r0.toNat, r1.toNat] := by
  intro nx0 lhs r0 r1 α hα
  have hx := xorGateDef_eval hxor hα
  rw [← bv32_xor1_eq_litNeg x0] at hx
  rw [bv32_bit0_eval α nx0, bv32_bit0_eval α x1, bv32_bit0_eval α x2] at hx
  rw [xorEvalList_cons_pair]
  have hev_lhs :
      evalLitVal α lhs.toNat =
        (evalLitVal α (nx0 &&& ~~~1#32).toNat != decide ((lhs &&& 1#32) ≠ 0#32)) := by
    rw [bv32_bit0_eval α lhs]
    have hln : (lhs &&& ~~~1#32).toNat = (nx0 &&& ~~~1#32).toNat := by
      dsimp only [lhs]; rw [m6_bv32_and_not1_toNat, m6_bv32_and_not1_toNat]
      have hl : lhs.toNat / 2 = nx0.toNat / 2 := by
        dsimp only [lhs]; rw [bv32_even_or_bit_toNat]; omega
      rw [hl]
    rw [hln]
  rw [hev_lhs]
  simp only [bv32_getLsb0_eq_and1] at hx ⊢
  have hbit_lhs : lhs.getLsbD 0 = ((nx0.getLsbD 0 != x1.getLsbD 0) != x2.getLsbD 0) := by
    dsimp only [lhs]; simp
  rw [hbit_lhs]; exact bool_xor3_norm _ _ _ _ _ _ hx

private theorem bool_xor4_norm :
    ∀ a0 a1 a2 a3 b0 b1 b2 b3 : Bool,
      ((!(a0 != b0)) = ((a1 != b1) != ((a2 != b2) != (a3 != b3)))) →
      (a0 != ((((true != b0) != b1) != b2) != b3)) = (a1 != (a2 != a3)) := by
  decide

private theorem fid_emit_xor4_sem {F_cur : List (List Nat)} {x0 x1 x2 x3 : BitVec 32}
    (hxor : XorListGateDef (cnfOfClauses F_cur) (litNeg x0.toNat) [x1.toNat, x2.toNat, x3.toNat]) :
    let lhs := (x0 &&& ~~~1#32) ||| ((1#32 ^^^ x0 ^^^ x1 ^^^ x2 ^^^ x3) &&& 1#32)
    let r0 := x1 &&& ~~~1#32; let r1 := x2 &&& ~~~1#32; let r2 := x3 &&& ~~~1#32
    XorListGateDef (cnfOfClauses F_cur) lhs.toNat [r0.toNat, r1.toNat, r2.toNat] := by
  intro lhs r0 r1 r2 α hα
  have hx := hxor α hα
  rw [evalLitVal_litNeg, xorEvalList_triple] at hx
  rw [xorEvalList_triple]
  have hev_lhs :
      evalLitVal α lhs.toNat =
        (evalLitVal α (x0 &&& ~~~1#32).toNat != decide ((lhs &&& 1#32) ≠ 0#32)) := by
    rw [bv32_bit0_eval α lhs]
    have hln : (lhs &&& ~~~1#32).toNat = (x0 &&& ~~~1#32).toNat := by
      rw [m6_bv32_and_not1_toNat, m6_bv32_and_not1_toNat]
      have hl : lhs.toNat / 2 = x0.toNat / 2 := by
        dsimp only [lhs]; rw [bv32_even_or_bit_toNat]; omega
      rw [hl]
    rw [hln]
  rw [bv32_bit0_eval α x0, bv32_bit0_eval α x1, bv32_bit0_eval α x2, bv32_bit0_eval α x3] at hx
  rw [hev_lhs]
  simp only [bv32_getLsb0_eq_and1] at hx ⊢
  have hbit_lhs :
      lhs.getLsbD 0 =
        ((((true != x0.getLsbD 0) != x1.getLsbD 0) != x2.getLsbD 0) != x3.getLsbD 0) := by
    dsimp only [lhs]; simp
  rw [hbit_lhs]; exact bool_xor4_norm _ _ _ _ _ _ _ _ hx

private theorem sort3_perm (r0 r1 r2 : BitVec 32) :
    let p1 := if r1 < r0 then (r1, r0) else (r0, r1)
    let p2 := if r2 < p1.2 then (r2, p1.2) else (p1.2, r2)
    let p3 := if p2.1 < p1.1 then (p2.1, p1.1) else (p1.1, p2.1)
    List.Perm [p3.1, p3.2, p2.2] [r0, r1, r2] := by
  have h2 : ∀ x y : BitVec 32,
      List.Perm [(if y < x then (y, x) else (x, y)).1, (if y < x then (y, x) else (x, y)).2]
        [x, y] := fun x y => by
    split
    · exact .swap _ _ _
    · exact .refl _
  dsimp only
  exact (List.Perm.append_right [_] (h2 _ _)).trans
    ((List.Perm.cons _ (h2 _ _)).trans (List.Perm.append_right [_] (h2 _ _)))

/-! ## 6. `full_cong_emit_xor_wp` (`Spec.fullCongEmitXorSpec`) -/

private theorem emit_xor_post {maxA cur_vars : Nat} {F_cur : List (List Nat)}
    {scr : List (BitVec 32)} {g_len : BitVec 64} {x0 x1 x2 s0 s1 : BitVec 32}
    (hmax2 : 2 ≤ maxA) (hcv2 : 2 ≤ cur_vars)
    (hglen : g_len.toNat + 4 ≤ scr.length) (_hscr : scr.length < 2 ^ 32)
    (hx0 : x0.toNat < 2 * cur_vars) (hx1 : x1.toNat < 2 * cur_vars) (hx2 : x2.toNat < 2 * cur_vars)
    (hxor : XorGateDef (cnfOfClauses F_cur) (litNeg x0.toNat) x1.toNat x2.toNat)
    (hseq0 : CongGateSeqOk maxA F_cur cur_vars scr g_len.toNat 0)
    (hs_perm : List.Perm [s0, s1] [x1 &&& ~~~1#32, x2 &&& ~~~1#32]) :
    let nx0 := x0 ^^^ 1#32
    let lhs := (nx0 &&& ~~~1#32) ||| ((nx0 ^^^ x1 ^^^ x2) &&& 1#32)
    let mword := (1#32 <<< 28) ||| 2#32
    let scr' := (((scr.set g_len.toNat lhs).set (g_len.toNat + 1) mword).set
      (g_len.toNat + 2) s0).set (g_len.toNat + 3) s1
    scr'.length = scr.length ∧
    (∀ idx < g_len.toNat, scr'[idx]? = scr[idx]?) ∧
    CongGateSeqOk maxA F_cur cur_vars scr' (g_len.toNat + 4) 0 := by
  intro nx0 lhs mword scr'
  have hlen' : scr'.length = scr.length := by simp [scr']
  have hpres : ∀ idx < g_len.toNat, scr'[idx]? = scr[idx]? := fun idx hidx => by
    dsimp only [scr']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have h1 : scr'[g_len.toNat + 1]? = some mword := by
    dsimp only [scr']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by simp; omega)]
  have har : congGateArity mword = 2 := by decide
  have hg_at : CongGateAt maxA F_cur cur_vars scr' (g_len.toNat + 4) g_len.toNat := by
    have h0 : scr'[g_len.toNat]? = some lhs := by
      dsimp only [scr']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
    have h2 : scr'[g_len.toNat + 2]? = some s0 := by
      dsimp only [scr']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
    have h3 : scr'[g_len.toNat + 3]? = some s1 := by
      dsimp only [scr']; exact List.getElem?_set_self (by simp; omega)
    have htag : (mword >>> 28).toNat = 1 := by decide
    have hlhs_lt : lhs.toNat < 2 * cur_vars := by
      dsimp only [lhs]; rw [bv32_even_or_bit_toNat]
      have hnx0 : nx0.toNat < 2 * cur_vars := by
        dsimp only [nx0]; rw [bv32_xor1_eq_litNeg]; exact litNeg_lt_two_mul hx0
      omega
    have hr_lt : ∀ b ∈ [x1 &&& ~~~1#32, x2 &&& ~~~1#32], b.toNat < 2 * cur_vars := fun b hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> rw [m6_bv32_and_not1_toNat] <;> omega
    have hs0_lt : s0.toNat < 2 * cur_vars := hr_lt s0 (hs_perm.mem_iff.mp (by simp))
    have hs1_lt : s1.toNat < 2 * cur_vars := hr_lt s1 (hs_perm.mem_iff.mp (by simp))
    have hs0_eq : scr'[g_len.toNat + 2]'(by omega) = s0 := by
      rw [← Option.some_inj, ← List.getElem?_eq_getElem (by omega)]; exact h2
    have hs1_eq : scr'[g_len.toNat + 3]'(by omega) = s1 := by
      rw [← Option.some_inj, ← List.getElem?_eq_getElem (by omega)]; exact h3
    have hmin : min 2 (scr'.length - (g_len.toNat + 2)) = 2 := by rw [hlen']; omega
    have hdrop :
        ((scr'.drop (g_len.toNat + 2)).take 2).map BitVec.toNat = [s0.toNat, s1.toNat] := by
      apply List.ext_getElem
      · simp [List.length_take, List.length_drop, hmin]
      · intro k hk _
        simp only [List.length_map, List.length_take, List.length_drop, hmin] at hk
        simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
        rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
        · simp [hs0_eq]
        · simpa [Nat.add_assoc] using congrArg BitVec.toNat hs1_eq
    have hsem := emit_xor_sem hxor
    have hperm_xor :
        XorListGateDef (cnfOfClauses F_cur) lhs.toNat [s0.toNat, s1.toNat] := by
      intro α hα; rw [hsem α hα]
      exact xorEvalList_perm α (hs_perm.map BitVec.toNat).symm
    refine ⟨lhs, mword, h0, h1, hlhs_lt, ?_, ?_, ?_, ?_, Or.inr (Or.inl ⟨htag, ?_, ?_, ?_⟩)⟩
    · rw [har]; omega
    · rw [har]; exact hcv2
    · rw [har]; exact hmax2
    · rw [har]; intro k hk; rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · exact ⟨s0, h2, hs0_lt⟩
      · exact ⟨s1, h3, hs1_lt⟩
    · rw [har]; decide
    · rw [har]; decide
    · rw [har, hdrop]; exact hperm_xor
  exact ⟨hlen', hpres, congGateSeqOk_append_gate hpres hseq0
    (.step hg_at (by rw [h1, Option.getD_some, har]; exact .done))
    (by omega)⟩

/-- Canonical `Func.wp` proof for `full_cong_emit_xor`. -/
theorem full_cong_emit_xor_wp (Γ : Env) :
    ∀ args m Q X, Spec.fullCongEmitXorSpec args m Q X →
      Func.wp Γ full_cong_emit_xor_body args m Q X := by
  rintro ⟨scr_ptr, g_len, x0, x1, x2, ⟨⟩⟩ m0 Q X
    ⟨maxA, F_cur, cur_vars, scr, R, hmax2, hmax64, hx0, hx1, hx2, hcv2,
      hglen, hscr_len, hxor, hseq0, hm0, hQ⟩
  unfold Func.wp full_cong_emit_xor_body
  have hg0 : g_len.toNat < scr.length := by omega
  have hg1 : (g_len + 1#64).toNat < scr.length := by bv_omega
  have hg2 : (g_len + 2#64).toNat < scr.length := by bv_omega
  have hg3 : (g_len + 3#64).toNat < scr.length := by bv_omega
  have ha1 : (g_len + (1 : BitVec 64)).toNat = g_len.toNat + 1 := by bv_omega
  have ha2 : (g_len + (2 : BitVec 64)).toNat = g_len.toNat + 2 := by bv_omega
  have ha3 : (g_len + (3 : BitVec 64)).toNat = g_len.toNat + 3 := by bv_omega
  cong_split
  · have hr_lt : (x1 &&& ~~~1#32) < (x2 &&& ~~~1#32) := hc
    c0_hsteps!
    obtain ⟨hlen', hpres, hseq'⟩ := emit_xor_post hmax2 hcv2 hglen hscr_len hx0 hx1 hx2 hxor hseq0
      (.refl _)
    refine hQ _ m hlen' hpres hseq' ?_
    rw [ha1, ha2, ha3] at hm; exact hm
  · have hr_ge : ¬((x1 &&& ~~~1#32) < (x2 &&& ~~~1#32)) := hc
    clear hc; cong_split
    c0_hsteps!
    obtain ⟨hlen', hpres, hseq'⟩ := emit_xor_post hmax2 hcv2 hglen hscr_len hx0 hx1 hx2 hxor
      hseq0 (.swap _ _ _)
    refine hQ _ m hlen' hpres hseq' ?_
    rw [ha1, ha2, ha3] at hm; exact hm

/-! ## 8. `full_cong_emit_xor4_wp` (`Spec.fullCongEmitXor4Spec`) -/

private theorem emit_xor4_post {maxA cur_vars : Nat} {F_cur : List (List Nat)}
    {scr : List (BitVec 32)} {g_len : BitVec 64} {x0 x1 x2 x3 s0 s1 s2 : BitVec 32}
    (hmax3 : 3 ≤ maxA) (hcv3 : 3 ≤ cur_vars)
    (hglen : g_len.toNat + 5 ≤ scr.length) (_hscr : scr.length < 2 ^ 32)
    (hx0 : x0.toNat < 2 * cur_vars) (hx1 : x1.toNat < 2 * cur_vars)
    (hx2 : x2.toNat < 2 * cur_vars) (hx3 : x3.toNat < 2 * cur_vars)
    (hxor : XorListGateDef (cnfOfClauses F_cur) (litNeg x0.toNat) [x1.toNat, x2.toNat, x3.toNat])
    (hseq0 : CongGateSeqOk maxA F_cur cur_vars scr g_len.toNat 0)
    (hs_perm : List.Perm [s0, s1, s2] [x1 &&& ~~~1#32, x2 &&& ~~~1#32, x3 &&& ~~~1#32]) :
    let lhs := (x0 &&& ~~~1#32) ||| ((1#32 ^^^ x0 ^^^ x1 ^^^ x2 ^^^ x3) &&& 1#32)
    let mword := (1#32 <<< 28) ||| 3#32
    let scr' := ((((scr.set g_len.toNat lhs).set (g_len.toNat + 1) mword).set
      (g_len.toNat + 2) s0).set (g_len.toNat + 3) s1).set (g_len.toNat + 4) s2
    scr'.length = scr.length ∧
    (∀ idx < g_len.toNat, scr'[idx]? = scr[idx]?) ∧
    CongGateSeqOk maxA F_cur cur_vars scr' (g_len.toNat + 5) 0 := by
  intro lhs mword scr'
  have hlen' : scr'.length = scr.length := by simp [scr']
  have hpres : ∀ idx < g_len.toNat, scr'[idx]? = scr[idx]? := fun idx hidx => by
    dsimp only [scr']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have h1 : scr'[g_len.toNat + 1]? = some mword := by
    dsimp only [scr']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
  have har : congGateArity mword = 3 := by decide
  have hg_at : CongGateAt maxA F_cur cur_vars scr' (g_len.toNat + 5) g_len.toNat := by
    have h0 : scr'[g_len.toNat]? = some lhs := by
      dsimp only [scr']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by omega)]
    have h2 : scr'[g_len.toNat + 2]? = some s0 := by
      dsimp only [scr']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simp; omega)]
    have h3 : scr'[g_len.toNat + 3]? = some s1 := by
      dsimp only [scr']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
    have h4 : scr'[g_len.toNat + 4]? = some s2 := by
      dsimp only [scr']; exact List.getElem?_set_self (by simp; omega)
    have htag : (mword >>> 28).toNat = 1 := by decide
    have hlhs_lt : lhs.toNat < 2 * cur_vars := by
      dsimp only [lhs]; rw [bv32_even_or_bit_toNat]; omega
    have hr_lt : ∀ b ∈ [x1 &&& ~~~1#32, x2 &&& ~~~1#32, x3 &&& ~~~1#32],
        b.toNat < 2 * cur_vars := fun b hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl <;> rw [m6_bv32_and_not1_toNat] <;> omega
    have hs0_lt : s0.toNat < 2 * cur_vars := hr_lt s0 (hs_perm.mem_iff.mp (by simp))
    have hs1_lt : s1.toNat < 2 * cur_vars := hr_lt s1 (hs_perm.mem_iff.mp (by simp))
    have hs2_lt : s2.toNat < 2 * cur_vars := hr_lt s2 (hs_perm.mem_iff.mp (by simp))
    have hs0_eq : scr'[g_len.toNat + 2]'(by omega) = s0 := by
      rw [← Option.some_inj, ← List.getElem?_eq_getElem (by omega)]; exact h2
    have hs1_eq : scr'[g_len.toNat + 3]'(by omega) = s1 := by
      rw [← Option.some_inj, ← List.getElem?_eq_getElem (by omega)]; exact h3
    have hs2_eq : scr'[g_len.toNat + 4]'(by omega) = s2 := by
      rw [← Option.some_inj, ← List.getElem?_eq_getElem (by omega)]; exact h4
    have hmin : min 3 (scr'.length - (g_len.toNat + 2)) = 3 := by rw [hlen']; omega
    have hdrop :
        ((scr'.drop (g_len.toNat + 2)).take 3).map BitVec.toNat =
          [s0.toNat, s1.toNat, s2.toNat] := by
      apply List.ext_getElem
      · simp [List.length_take, List.length_drop, hmin]
      · intro k hk _
        simp only [List.length_map, List.length_take, List.length_drop, hmin] at hk
        simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
        · simp [hs0_eq]
        · simpa [Nat.add_assoc] using congrArg BitVec.toNat hs1_eq
        · simpa [Nat.add_assoc] using congrArg BitVec.toNat hs2_eq
    have hsem := fid_emit_xor4_sem hxor
    have hperm_xor :
        XorListGateDef (cnfOfClauses F_cur) lhs.toNat [s0.toNat, s1.toNat, s2.toNat] := by
      intro α hα; rw [hsem α hα]
      exact xorEvalList_perm α (hs_perm.map BitVec.toNat).symm
    refine ⟨lhs, mword, h0, h1, hlhs_lt, ?_, ?_, ?_, ?_, Or.inr (Or.inl ⟨htag, ?_, ?_, ?_⟩)⟩
    · rw [har]; omega
    · rw [har]; exact hcv3
    · rw [har]; exact hmax3
    · rw [har]; intro k hk; rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
      · exact ⟨s0, h2, hs0_lt⟩
      · exact ⟨s1, h3, hs1_lt⟩
      · exact ⟨s2, h4, hs2_lt⟩
    · rw [har]; decide
    · rw [har]; decide
    · rw [har, hdrop]; exact hperm_xor
  exact ⟨hlen', hpres, congGateSeqOk_append_gate hpres hseq0
    (.step hg_at (by rw [h1, Option.getD_some, har]; exact .done))
    (by omega)⟩

/-- Canonical `Func.wp` proof for `full_cong_emit_xor4`. -/
theorem full_cong_emit_xor4_wp (Γ : Env) :
    ∀ args m Q X, Spec.fullCongEmitXor4Spec args m Q X →
      Func.wp Γ full_cong_emit_xor4_body args m Q X := by
  rintro ⟨scr_ptr, g_len, x0, x1, x2, x3, ⟨⟩⟩ m0 Q X
    ⟨maxA, F_cur, cur_vars, scr, R, hmax3, hmax64, hx0, hx1, hx2, hx3, hcv3,
      hglen, hscr_len, hxor, hseq0, hm0, hQ⟩
  unfold Func.wp full_cong_emit_xor4_body
  have hg0 : g_len.toNat < scr.length := by omega
  have hg1 : (g_len + 1#64).toNat < scr.length := by bv_omega
  have hg2 : (g_len + 2#64).toNat < scr.length := by bv_omega
  have hg3 : (g_len + 3#64).toNat < scr.length := by bv_omega
  have hg4 : (g_len + 4#64).toNat < scr.length := by bv_omega
  have ha1 : (g_len + (1 : BitVec 64)).toNat = g_len.toNat + 1 := by bv_omega
  have ha2 : (g_len + (2 : BitVec 64)).toNat = g_len.toNat + 2 := by bv_omega
  have ha3 : (g_len + (3 : BitVec 64)).toNat = g_len.toNat + 3 := by bv_omega
  have ha4 : (g_len + (4 : BitVec 64)).toNat = g_len.toNat + 4 := by bv_omega
  let r0 := x1 &&& ~~~1#32; let r1 := x2 &&& ~~~1#32; let r2 := x3 &&& ~~~1#32
  c0_hsteps_nogrp
  refine LeanQbe.T.wp_join_group (ts := [i32, i32])
    (fun (a0, a1, ()) m1 => m0 = m1 ∧ (a0, a1) = if r1 < r0 then (r1, r0) else (r0, r1)) ?_ ?_
  · rintro _ ⟨a0, a1, ⟨⟩⟩ m1 ⟨rfl, hp1⟩
    c0_hsteps_nogrp
    refine LeanQbe.T.wp_join_group (ts := [i32, i32])
      (fun (b1, b2, ()) m2 => m0 = m2 ∧
        (b1, b2) = if r2 < a1 then (r2, a1) else (a1, r2)) ?_ ?_
    · rintro _ ⟨b1, b2, ⟨⟩⟩ m2 ⟨hm2, hp2⟩
      subst m2
      c0_hsteps_nogrp
      refine LeanQbe.T.wp_join_group (ts := [i32, i32])
        (fun (c0, c1, ()) m3 => m0 = m3 ∧
          (c0, c1) = if b1 < a0 then (b1, a0) else (a0, b1)) ?_ ?_
      · rintro _ ⟨c0, c1, ⟨⟩⟩ m3 ⟨hm3, hp3⟩
        subst m3
        c0_hsteps!
        have hp_all := sort3_perm r0 r1 r2
        have hperm : List.Perm [c0, c1, b2] [r0, r1, r2] := by
          have h1 : c0 = (if b1 < a0 then (b1, a0) else (a0, b1)).1 :=
            congrArg Prod.fst hp3
          have h2 : c1 = (if b1 < a0 then (b1, a0) else (a0, b1)).2 :=
            congrArg Prod.snd hp3
          have h3 : b1 = (if r2 < a1 then (r2, a1) else (a1, r2)).1 :=
            congrArg Prod.fst hp2
          have h4 : b2 = (if r2 < a1 then (r2, a1) else (a1, r2)).2 :=
            congrArg Prod.snd hp2
          have h5 : a0 = (if r1 < r0 then (r1, r0) else (r0, r1)).1 :=
            congrArg Prod.fst hp1
          have h6 : a1 = (if r1 < r0 then (r1, r0) else (r0, r1)).2 :=
            congrArg Prod.snd hp1
          rw [h1, h2, h3, h4, h5, h6]; exact hp_all
        obtain ⟨hlen', hpres, hseq'⟩ := emit_xor4_post hmax3 hcv3 hglen hscr_len hx0 hx1 hx2 hx3
          hxor hseq0 hperm
        refine hQ _ m hlen' hpres hseq' ?_
        rw [ha1, ha2, ha3, ha4] at hm; exact hm
      · intro J3 hJ3; cong_split
        · have hlt : b1 < a0 := BitVec.lt_def.mpr hc
          c0_hsteps!; exact hJ3 (b1, a0, ()) m0 ⟨rfl, by simp [hlt]⟩
        · have hnlt : ¬b1 < a0 := fun h => hc (BitVec.lt_def.mp h)
          c0_hsteps!; exact hJ3 (a0, b1, ()) m0 ⟨rfl, by simp [hnlt]⟩
    · intro J2 hJ2; cong_split
      · have hlt : r2 < a1 := BitVec.lt_def.mpr hc
        c0_hsteps!; exact hJ2 (r2, a1, ()) m0 ⟨rfl, by simp [hlt]⟩
      · have hnlt : ¬r2 < a1 := fun h => hc (BitVec.lt_def.mp h)
        c0_hsteps!; exact hJ2 (a1, r2, ()) m0 ⟨rfl, by simp [hnlt]⟩
  · intro J1 hJ1; cong_split
    · have hlt : r1 < r0 := BitVec.lt_def.mpr hc
      c0_hsteps!; exact hJ1 (r1, r0, ()) m0 ⟨rfl, by simp [hlt]⟩
    · have hnlt : ¬r1 < r0 := fun h => hc (BitVec.lt_def.mp h)
      c0_hsteps!; exact hJ1 (r0, r1, ()) m0 ⟨rfl, by simp [hnlt]⟩

/-! ## 7. `full_cong_has_clause_k_wp` (`Spec.fullCongHasClauseKSpec`) -/

private def hckUnass (tmp : List (BitVec 32)) (k : Nat) : List Nat :=
  (List.range k).map fun j => (tmp[j]?.getD 0#32).toNat

private theorem hck_bv32_shl1_lt {x : BitVec 32} (hx : x.toNat < 2 ^ 30) :
    (x.setWidth 64 <<< (1 : BitVec 64)).toNat = 2 * x.toNat ∧
    (x.setWidth 64 <<< (1 : BitVec 64) + (1 : BitVec 64)).toNat = 2 * x.toNat + 1 := by
  have hof : x.setWidth 64 = BitVec.ofNat 64 x.toNat := by
    apply BitVec.eq_of_toNat_eq; rw [bv_zext32_toNat, bv64_ofNat_toNat_lt (by omega)]
  have h1 : (x.setWidth 64 <<< (1 : BitVec 64)).toNat = 2 * x.toNat := by
    rw [hof]
    change (BitVec.ofNat 64 x.toNat <<< (1 : Nat)).toNat = 2 * x.toNat
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 64), Nat.mul_comm]
    simp [Nat.mod_eq_of_lt (by omega : 2 * x.toNat < 2 ^ 64)]
  have h2 : (x.setWidth 64 <<< (1 : BitVec 64) + (1 : BitVec 64)).toNat = 2 * x.toNat + 1 := by
    rw [BitVec.toNat_add, h1, show ((1 : BitVec 64)).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  exact ⟨h1, h2⟩

private theorem hck_nat_shl1_lt {x : Nat} (hx : x < 2 ^ 63) :
    (BitVec.ofNat 64 x <<< (1 : BitVec 64)).toNat = 2 * x := by
  change (BitVec.ofNat 64 x <<< (1 : Nat)).toNat = 2 * x
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : x < 2 ^ 64), Nat.mul_comm]
  simp [Nat.mod_eq_of_lt (by omega : 2 * x < 2 ^ 64)]

private theorem hck_lm_mark_agree_step {tmp : List (BitVec 32)} {lm s_lm : List (BitVec 8)}
    {i : Nat} {val : BitVec 8}
    (hagree : ∀ q, (∀ j < i, q ≠ (tmp[j]?.getD 0#32).toNat) → lm[q]? = s_lm[q]?)
    {li : BitVec 32} (hli_eq : li = tmp[i]?.getD 0#32) :
    ∀ q, (∀ j < i + 1, q ≠ (tmp[j]?.getD 0#32).toNat) →
      (lm.set li.toNat val)[q]? = s_lm[q]? := by
  intro q hq
  have hq_i : q ≠ li.toNat := by rw [hli_eq]; exact hq i (by omega)
  rw [List.getElem?_set_ne (Ne.symm hq_i)]
  exact hagree q (fun j hj => hq j (by omega))

private theorem hck_lm_clear_agree_step {max_vars : Nat} {tmp : List (BitVec 32)}
    {lm s_lm : List (BitVec 8)} {j k : Nat}
    (hlen : lm.length = 2 * max_vars) (hslen : s_lm.length = 2 * max_vars)
    (hs_clr : ∀ l < 2 * max_vars, s_lm[l]?.getD 0#8 = 0#8)
    (hagree : ∀ q, (∀ r, j ≤ r → r < k → q ≠ (tmp[r]?.getD 0#32).toNat) → lm[q]? = s_lm[q]?)
    {lj : BitVec 32} (hlj_eq : lj = tmp[j]?.getD 0#32) (hlj_bd : lj.toNat < 2 * max_vars) :
    ∀ q, (∀ r, j + 1 ≤ r → r < k → q ≠ (tmp[r]?.getD 0#32).toNat) →
      (lm.set lj.toNat 0#8)[q]? = s_lm[q]? := by
  intro q hq
  by_cases hqj : q = lj.toNat
  · subst hqj
    rw [List.getElem?_set_self (by omega)]
    exact (getElem?_eq_some_of_getD (by omega) (hs_clr lj.toNat hlj_bd)).symm
  · rw [List.getElem?_set_ne (Ne.symm hqj)]
    refine hagree q fun r hr1 hr2 => ?_
    by_cases hrj : r = j
    · subst hrj; rw [← hlj_eq]; exact hqj
    · exact hq r (by omega) hr2

private theorem hck_unass_mem_of_litMark_ne0 {max_vars cur_vars : Nat}
    {tmp : List (BitVec 32)} {lm s_lm : List (BitVec 8)} {k : Nat}
    (hcv : cur_vars ≤ max_vars)
    (hs_clr : ∀ l < 2 * max_vars, s_lm[l]?.getD 0#8 = 0#8)
    (hagree : ∀ q, q ∉ hckUnass tmp k → lm[q]? = s_lm[q]?)
    {cl : Nat} (hcl_lt : cl < 2 * cur_vars) (hne0 : lm[cl]?.getD 0#8 ≠ 0#8) :
    cl ∈ hckUnass tmp k := by
  by_cases hmem : cl ∈ hckUnass tmp k
  · exact hmem
  · exfalso; rw [hagree cl hmem] at hne0
    exact hne0 (hs_clr cl (by omega))

private theorem hck_garb_false_of_and {hdr : BitVec 32}
    (h : (hdr &&& (524288 ||| 4194304 : BitVec 32)) = 0#32) :
    ((hdr &&& 0x00080000#32) != 0#32) = false := by
  have hm : (524288 ||| 4194304 : BitVec 32) = 0x00480000#32 := by decide
  rw [hm] at h; exact garb_false_of_and_480000 h

private theorem hck_bv8_eqff_of_sext_slt0 {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (h : (BitVec.signExtend 32 v).slt 0#32 = true) : v = 0xFF#8 := by
  rcases hdom with rfl | rfl | rfl
  · cases h
  · cases h
  · rfl

private theorem hck_bv8_ne0_not_sext_sgt0_eqff {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (hnsgt : ¬ (0#32 : BitVec 32).slt (BitVec.signExtend 32 v) = true)
    (hneq0 : ¬ BitVec.signExtend 32 v = 0#32) : v = 0xFF#8 := by
  rcases hdom with rfl | rfl | rfl
  · exact absurd (by decide) hneq0
  · exact absurd (by decide) hnsgt
  · rfl

private theorem hck_arena_entails_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core)
    (hcl0 : s.core.cur_level = 0) {cr sz : BitVec 32}
    (hcr : cr.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cr.toNat = false)
    (hsz_nat : sz.toNat = fullArenaClauseSize s cr.toNat)
    (hbd : cr.toNat + 3 + sz.toNat ≤ s.core.arena.length)
    {unass : List Nat}
    (hcov : ∀ q < sz.toNat,
      let cl := (s.core.arena[cr.toNat + 3 + q]?.getD 0#32).toNat
      s.core.vals[cl]?.getD 0#8 = 0xFF#8 ∨ cl ∈ unass) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause unass) := by
  refine unassigned_clause_entails hw hcl0 hcr hng fun l hl => ?_
  unfold fullArenaClauseLits fullArenaClauseLitsCore at hl
  rw [show fullArenaClauseSizeCore s.core cr.toNat = sz.toNat from hsz_nat.symm] at hl
  rw [List.mem_map] at hl
  obtain ⟨bv, hbv_mem, rfl⟩ := hl
  have htake_len : ((s.core.arena.drop (cr.toNat + 3)).take sz.toNat).length = sz.toNat := by
    simp [List.length_take, List.length_drop]; omega
  obtain ⟨q, hq, hbq⟩ := List.getElem_of_mem hbv_mem
  rw [htake_len] at hq
  rw [List.getElem_take, List.getElem_drop] at hbq
  have hcl_eq : s.core.arena[cr.toNat + 3 + q]?.getD 0#32 = bv := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hbq]
  simpa [hcl_eq] using hcov q hq

private theorem hck_cl_elem_bounds {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hlen : FullState.LengthsOk c s)
    {cr sz wv j : BitVec 32} (hcr : cr.toNat ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cr.toNat = false)
    (hsz : sz.toNat = fullArenaClauseSize s cr.toNat)
    (hbd : cr.toNat + 3 + sz.toNat ≤ s.core.arena.length)
    (hj : j.toNat < sz.toNat) (hwv : wv = cr) :
    (BitVec.setWidth 64 wv + (3 : BitVec 64) + BitVec.setWidth 64 j).toNat =
      cr.toNat + 3 + j.toNat ∧
    (BitVec.setWidth 64 wv + (3 : BitVec 64) + BitVec.setWidth 64 j).toNat <
      s.core.arena.length ∧
    ((s.core.arena[cr.toNat + 3 + j.toNat]?.getD 0#32).setWidth 64).toNat =
      (s.core.arena[cr.toNat + 3 + j.toNat]?.getD 0#32).toNat ∧
    (s.core.arena[cr.toNat + 3 + j.toNat]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
    (s.core.arena[cr.toNat + 3 + j.toNat]?.getD 0#32).toNat < s.core.vals.length ∧
    (s.core.arena[cr.toNat + 3 + j.toNat]?.getD 0#32).toNat < 2 * c.max_vars := by
  subst hwv
  have hcr3j : (BitVec.setWidth 64 wv + (3 : BitVec 64) + BitVec.setWidth 64 j).toNat =
      wv.toNat + 3 + j.toNat := by bv_omega
  have hlt_a : wv.toNat + 3 + j.toNat < s.core.arena.length := by omega
  let cl := s.core.arena[wv.toNat + 3 + j.toNat]?.getD 0#32
  have hcl_mem : cl.toNat ∈ fullArenaClauseLits s wv.toNat := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    have hszc : sz.toNat = fullArenaClauseSizeCore s.core wv.toNat := hsz
    rw [← hszc, List.mem_map]
    refine ⟨cl, ?_, rfl⟩
    have htake : ((s.core.arena.drop (wv.toNat + 3)).take sz.toNat)[j.toNat]'(by
        simp [List.length_take, List.length_drop]; omega) = cl := by
      simp only [List.getElem_take, List.getElem_drop, cl]
      rw [List.getElem?_eq_getElem hlt_a, Option.getD_some]
    rw [← htake]; exact List.getElem_mem _
  have hcl_lt : cl.toNat < 2 * s.core.cur_vars :=
    hw.arena.lits_lt wv.toNat hcr hng cl.toNat hcl_mem
  have hcv := hlen.core_ok.cur_vars_le
  have hvl := hlen.core_ok.vals_len
  refine ⟨hcr3j, by rw [hcr3j]; exact hlt_a, bv_zext32_toNat cl, hcl_lt,
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hcl_lt (Nat.mul_le_mul_left 2 hcv))
      (Nat.le_of_eq hvl.symm),
    Nat.lt_of_lt_of_le hcl_lt (Nat.mul_le_mul_left 2 hcv)⟩

/-- Canonical `Func.wp` proof for `full_cong_has_clause_k`. -/
theorem full_cong_has_clause_k_wp (Γ : Env) :
    ∀ args m Q X, Spec.fullCongHasClauseKSpec args m Q X →
      Func.wp Γ full_cong_has_clause_k_body args m Q X := by
  rintro ⟨h, k, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hmk, hnd, hcl0, hk3, hk5, hkcv, htmp_lt, _htmp_inj,
      hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; unfold dimacsBound at hmx hwc
  have hcv_le := hlen.core_ok.cur_vars_le; have htmpl := hlen.core_ok.tmp_len_arr
  have hwvl := hlen.core_ok.wvec_len; have hwsl := hlen.core_ok.wstk_len_arr
  have hvalsl := hlen.core_ok.vals_len; have hlml := hlen.core_ok.lit_mark_len
  have harl := hlen.core_ok.arena_len_arr; have hall := hlen.core_ok.arena_len_le
  have htmp_mem : ∀ j < k.toNat,
      (s.core.tmp[j]?.getD 0#32).toNat ∈ hckUnass s.core.tmp k.toNat := fun j hj => by
    unfold hckUnass; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  unfold Func.wp full_cong_has_clause_k_body
  c0_hsplit
  · exfalso; change k.toNat < 3 at hc; omega
  clear hc; c0_hsplit
  · exfalso; change 5 < k.toNat at hc; omega
  clear hc; c0_hsplit
  · exfalso
    have hcv_mod : s.core.cur_vars % 2 ^ 64 = s.core.cur_vars := Nat.mod_eq_of_lt (by omega)
    omega
  clear hc
  have h0_lt : (BitVec.signExtend 64 (0 : BitVec 32)).toNat < s.core.tmp.length := by
    have : (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 := by decide
    omega
  have hl0_lt : (s.core.tmp[(BitVec.signExtend 64 (0 : BitVec 32)).toNat]'h0_lt).toNat <
      2 * s.core.cur_vars := by
    have hz : (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 := by decide
    have h1 := htmp_lt 0 (by omega)
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
    rwa [list_getElem_congr hz h0_lt (by omega)]
  have hwvec0_lt :
      ((s.core.tmp[(BitVec.signExtend 64 (0 : BitVec 32)).toNat]'h0_lt).setWidth 64 <<<
        (1 : BitVec 64) + (1 : BitVec 64)).toNat < s.core.wvec.length := by
    rw [(hck_bv32_shl1_lt (by omega)).2]; omega
  c0_hsteps_nogrp
  refine LeanQbe.T.wp_loop_inv (ts := [i32, i32, i32])
    (fun (min_l, _min_wsz, i, ()) mi =>
      i.toNat ≤ k.toNat ∧ min_l.toNat < 2 * s.core.cur_vars ∧
      min_l.toNat ∈ hckUnass s.core.tmp k.toNat ∧
      ∃ lm' : List (BitVec 8), lm'.length = 2 * c.max_vars ∧
        (∀ q, (∀ j < i.toNat, q ≠ (s.core.tmp[j]?.getD 0#32).toNat) →
          lm'[q]? = s.core.lit_mark[q]?) ∧
        (FullMem c { s with core := { s.core with lit_mark := lm' } } ⋆ R) mi)
    (fun (_min_l, _min_wsz, i, ()) _ => k.toNat - i.toNat)
    (fun Jl hJl => by
      c0_hsteps!
      exact hJl (_, _, 0#32, ()) m0 ⟨Nat.zero_le _, hl0_lt, by
        have h1 : s.core.tmp[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat]'(by
            change 0 < s.core.tmp.length; omega) = s.core.tmp[0]?.getD 0#32 := by
          rw [list_getElem_congr (by rfl :
            (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat = 0) (by
            change 0 < s.core.tmp.length; omega) (by omega),
            List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [h1]; exact htmp_mem 0 (by omega),
        s.core.lit_mark, hlml, fun _ _ => rfl, hm0⟩)
    (fun Jl (min_l, min_wsz, i, ()) mi ⟨hi_le, hmin_lt, hmin_in, lm', hlml', hagree, hmi⟩ ihl =>
      ?_)
  c0_hsplit
  · have hi_lt : i.toNat < k.toNat := hc
    have hi_tmp : (i.setWidth 64).toNat < s.core.tmp.length := by
      rw [bv_zext32_toNat]; omega
    let li := s.core.tmp[(i.setWidth 64).toNat]'hi_tmp
    have hli_eq : li = s.core.tmp[i.toNat]?.getD 0#32 := by
      dsimp only [li]
      rw [list_getElem_congr (bv_zext32_toNat i) hi_tmp (by omega),
        List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hli_lt : li.toNat < 2 * s.core.cur_vars := by rw [hli_eq]; exact htmp_lt i.toNat hi_lt
    have hli_in : li.toNat ∈ hckUnass s.core.tmp k.toNat := by
      rw [hli_eq]; exact htmp_mem i.toNat hi_lt
    have hli_lm : (li.setWidth 64).toNat < lm'.length := by rw [bv_zext32_toNat]; omega
    have hwvec_li : (li.setWidth 64 <<< (1 : BitVec 64) + (1 : BitVec 64)).toNat <
        s.core.wvec.length := by
      rw [(hck_bv32_shl1_lt (by omega)).2]; omega
    have hi1 : (i + (1 : BitVec 32)).toNat = i.toNat + 1 := by bv_omega
    have hagree'' := hck_lm_mark_agree_step (val := BitVec.setWidth 8 (i + (1 : BitVec 32)))
      hagree hli_eq
    clear hc; cong_split
    · c0_hsteps!
      refine ihl (li, _, i + (1 : BitVec 32), ()) m (by dsimp only; omega)
        ⟨by omega, hli_lt, hli_in, lm'.set li.toNat (BitVec.setWidth 8 (i + (1 : BitVec 32))),
          by simp [hlml'], by rw [hi1]; exact hagree'', ?_⟩
      rwa [bv_zext32_toNat] at hm
    · c0_hsteps!
      refine ihl (min_l, min_wsz, i + (1 : BitVec 32), ()) m (by dsimp only; omega)
        ⟨by omega, hmin_lt, hmin_in, lm'.set li.toNat (BitVec.setWidth 8 (i + (1 : BitVec 32))),
          by simp [hlml'], by rw [hi1]; exact hagree'', ?_⟩
      rwa [bv_zext32_toNat] at hm
  · have hi_ge : ¬ i.toNat < k.toNat := hc
    have hi_eq : i.toNat = k.toNat := by omega
    have hagree_unass : ∀ q, q ∉ hckUnass s.core.tmp k.toNat →
        lm'[q]? = s.core.lit_mark[q]? := fun q hq => by
      refine hagree q fun j hj => ?_
      have hj_k : j < k.toNat := by omega
      intro hqj; apply hq; rw [hqj]; exact htmp_mem j hj_k
    have hwbd : fullWatchOffCore s.core min_l.toNat +
        fullWatchSizeCore s.core min_l.toNat ≤ c.wcap := by
      have hw_le := hlen.core_ok.wlen_le; have hwt := hw.watches
      unfold ModeWatchesInv at hwt; split at hwt
      · exact Nat.le_trans (hwt.layout.bounds min_l.toNat hmin_lt) hw_le
      · exact Nat.le_trans (hwt.layout.bounds min_l.toNat hmin_lt) hw_le
    have hslice0 : if s.core.dense_mode = 0#64 then
          WatchSliceOk F_cur s.core min_l.toNat (fullWatchOffCore s.core min_l.toNat)
            (fullWatchSizeCore s.core min_l.toNat)
        else DenseWatchSliceOk F_cur s.core min_l.toNat
            (fullWatchOffCore s.core min_l.toNat) (fullWatchSizeCore s.core min_l.toNat) := by
      have hwt := hw.watches; unfold ModeWatchesInv at hwt; split at hwt
      · simpa [*] using hwt.slices min_l.toNat hmin_lt
      · simpa [*] using hwt.slices min_l.toNat hmin_lt
    obtain ⟨hmw0_n, hmw1_n⟩ := hck_bv32_shl1_lt (x := min_l) (by omega)
    have hmw0_lt : (min_l.setWidth 64 <<< (1 : BitVec 64)).toNat < s.core.wvec.length := by
      omega
    have hmw1_lt : (min_l.setWidth 64 <<< (1 : BitVec 64) + (1 : BitVec 64)).toNat <
        s.core.wvec.length := by omega
    let off := (s.core.wvec[(min_l.setWidth 64 <<< (1 : BitVec 64)).toNat]'hmw0_lt).setWidth 64
    let wsz :=
      (s.core.wvec[(min_l.setWidth 64 <<< (1 : BitVec 64) +
        (1 : BitVec 64)).toNat]'hmw1_lt).setWidth 64
    have hoff_eq : off.toNat = fullWatchOffCore s.core min_l.toNat := by
      dsimp only [off]; unfold fullWatchOffCore
      rw [bv_zext32_toNat, list_getElem_congr hmw0_n hmw0_lt (by omega),
        List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hwsz_eq : wsz.toNat = fullWatchSizeCore s.core min_l.toNat := by
      dsimp only [wsz]; unfold fullWatchSizeCore
      rw [bv_zext32_toNat, list_getElem_congr hmw1_n hmw1_lt (by omega),
        List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hend_eq : (off + wsz).toNat = off.toNat + wsz.toNat := by
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hm0_w : (2 * min_l.toNat) % 2 ^ 64 = 2 * min_l.toNat := Nat.mod_eq_of_lt (by omega)
    have hm1_w : (2 * min_l.toNat + 1) % 2 ^ 64 = 2 * min_l.toNat + 1 :=
      Nat.mod_eq_of_lt (by omega)
    have hcur2 : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : BitVec 64)).toNat =
        2 * s.core.cur_vars := hck_nat_shl1_lt (by omega)
    clear hc; c0_hsteps_nogrp
    refine LeanQbe.T.wp_join_group (ts := [.bool, i64])
      (fun (ok, _dp, ()) mc => mc = mi ∧
        (ok = true →
          (cnfOfClauses F_cur).EntailsClause (cnfClause (hckUnass s.core.tmp k.toNat)))) ?_ ?_
    · rintro _ ⟨ok, _dp, ⟨⟩⟩ mc ⟨hmc, hok⟩
      subst mc
      c0_hsteps_nogrp
      refine LeanQbe.T.wp_loop_inv (ts := [i32])
        (fun (j, ()) mj => j.toNat ≤ k.toNat ∧ ∃ lmc : List (BitVec 8),
          lmc.length = 2 * c.max_vars ∧
          (∀ q, (∀ r, j.toNat ≤ r → r < k.toNat → q ≠ (s.core.tmp[r]?.getD 0#32).toNat) →
            lmc[q]? = s.core.lit_mark[q]?) ∧
          (FullMem c { s with core := { s.core with lit_mark := lmc } } ⋆ R) mj)
        (fun (j, ()) _ => k.toNat - j.toNat)
        (fun Jc hJc => by
          c0_hsteps!; exact hJc (0#32, ()) mi ⟨Nat.zero_le _, lm', hlml',
            fun q hq => hagree_unass q fun hm => by
              unfold hckUnass at hm; obtain ⟨r, hr, hqr⟩ := List.mem_map.mp hm
              rw [List.mem_range] at hr; exact hq r (Nat.zero_le _) hr hqr.symm, hmi⟩)
        (fun Jc (j, ()) mj ⟨hj_le, lmc, hlmcl, hagr_j, hmj⟩ ihc => ?_)
      c0_hsplit
      · have hj_lt : j.toNat < k.toNat := hc
        have hj_tmp : (j.setWidth 64).toNat < s.core.tmp.length := by
          rw [bv_zext32_toNat]; omega
        let lj := s.core.tmp[(j.setWidth 64).toNat]'hj_tmp
        have hlj_eq : lj = s.core.tmp[j.toNat]?.getD 0#32 := by
          dsimp only [lj]
          rw [list_getElem_congr (bv_zext32_toNat j) hj_tmp (by omega),
            List.getElem?_eq_getElem (by omega), Option.getD_some]
        have hlj_lt : lj.toNat < 2 * s.core.cur_vars := by rw [hlj_eq]; exact htmp_lt j.toNat hj_lt
        have hlj_lm : (lj.setWidth 64).toNat < lmc.length := by rw [bv_zext32_toNat]; omega
        have hj1 : (j + (1 : BitVec 32)).toNat = j.toNat + 1 := by bv_omega
        have hagr' := hck_lm_clear_agree_step hlmcl hlml hmk.2 hagr_j hlj_eq (by omega)
        c0_hsteps!
        refine ihc (j + (1 : BitVec 32), ()) m (by dsimp only; omega)
          ⟨by omega, lmc.set lj.toNat 0#8, by simp [hlmcl], by rw [hj1]; exact hagr', ?_⟩
        rwa [bv_zext32_toNat] at hm
      · have hj_ge : ¬ j.toNat < k.toNat := hc
        have hj_eq : j.toNat = k.toNat := by omega
        have hlm_eq : lmc = s.core.lit_mark := by
          apply List.ext_getElem (by omega)
          intro q hq1 hq2
          rw [← Option.some_inj, ← List.getElem?_eq_getElem hq1, ← List.getElem?_eq_getElem hq2]
          exact hagr_j q fun r hr1 hr2 => by omega
        have hmj' : (FullMem c s ⋆ R) mj := by rwa [hlm_eq] at hmj
        c0_hsteps!; exact hQ ok s mj hlen rfl rfl hmk hok hmj'
    · intro Jclean hJclean
      c0_hsteps_nogrp
      refine LeanQbe.T.wp_loop_inv (ts := [i64])
        (fun (p, ()) mp => mp = mi ∧ off.toNat ≤ p.toNat ∧ p.toNat ≤ (off + wsz).toNat ∧
          ∃ rem : Nat, p.toNat + rem = (off + wsz).toNat ∧
            (if s.core.dense_mode = 0#64 then WatchSliceOk F_cur s.core min_l.toNat p.toNat rem
             else DenseWatchSliceOk F_cur s.core min_l.toNat p.toNat rem))
        (fun (p, ()) _ => (off + wsz).toNat - p.toNat)
        (fun Jp hJp => by
          c0_hsteps!; exact hJp (off, ()) mi ⟨rfl, Nat.le_refl _, by omega,
            wsz.toNat, by omega, by rwa [hoff_eq, hwsz_eq]⟩)
        (fun Jp (p, ()) mp ⟨hmp, hp_lo, hp_hi, rem, hrem_eq, hslice⟩ ihp => ?_)
      have hm_p :
          (FullMem c { s with core := { s.core with lit_mark := lm' } } ⋆ R) mp := hmp ▸ hmi
      c0_hsplit
      · have hp_lt : p.toNat < (off + wsz).toNat := by
          dsimp only [off, wsz]
          rw [BitVec.toNat_add, bv_zext32_toNat, bv_zext32_toNat,
            list_getElem_congr hmw0_n hmw0_lt (by omega),
            list_getElem_congr hmw1_n hmw1_lt (by omega)]
          simpa [hm0_w, hm1_w] using hc
        have hrem_pos : 0 < rem := by omega
        obtain ⟨w0, hw0_get, hpop⟩ := slice_pop_step hslice hrem_pos
        have hp_w : p.toNat < s.core.wstk.length := by omega
        have hw0_eq : s.core.wstk[p.toNat]'hp_w = w0 := by
          rw [List.getElem?_eq_getElem hp_w] at hw0_get; exact Option.some.inj hw0_get
        have hp1 : (p + (1 : BitVec 64)).toNat = p.toNat + 1 := by bv_omega
        clear hc; c0_hsplit
        · rcases hpop with ⟨hf_ne, hent_bin, hrest⟩ | ⟨hf0, _⟩
          · let other := s.core.wstk[p.toNat]'hp_w &&& 0x7FFFFFFF#32
            clear hc; c0_hsteps_nogrp
            refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
            c0_hsplit
            · have hoth_lt : other.toNat < 2 * s.core.cur_vars := by
                dsimp only [other]
                simpa [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
                  Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] using hc
              have hoth_idx : (s.core.wstk[p.toNat]'hp_w &&& 0x7FFFFFFF#32).toNat = other.toNat :=
                rfl
              have hdom_o : s.core.vals[other.toNat]'(by omega) = 0#8 ∨
                  s.core.vals[other.toNat]'(by omega) = 1#8 ∨
                  s.core.vals[other.toNat]'(by omega) = 0xFF#8 := by
                have := hw.vals_domain other.toNat hoth_lt
                rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
              have hoth_vals : other.toNat < s.core.vals.length := by omega
              have hoth_lm : other.toNat < lm'.length := by omega
              clear hc; c0_hsplit
              · have h_slt : (BitVec.signExtend 32 (s.core.vals[other.toNat]'(by omega))).slt 0#32 =
                    true := hc
                have hv_ff : s.core.vals[other.toNat]?.getD 0#8 = 0xFF#8 := by
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  exact hck_bv8_eqff_of_sext_slt0 hdom_o h_slt
                c0_hsteps!; refine hJclean (true, _, ()) mp ⟨hmp, fun _ => ?_⟩
                exact bin_subsumes_unass hw hcl0 hoth_lt
                  (by dsimp only [other]; rw [hw0_eq]; exact hent_bin) hmin_in (Or.inl hv_ff)
              · clear hc; c0_hsplit
                · clear hc; c0_hsplit
                  · have hoth_in : other.toNat ∈ hckUnass s.core.tmp k.toNat := by
                      refine hck_unass_mem_of_litMark_ne0 hcv_le hmk.2 hagree_unass hoth_lt ?_
                      intro h0; revert hc
                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
                      change ¬ (BitVec.setWidth 32
                        (lm'[(s.core.wstk[p.toNat]'hp_w &&& 0x7FFFFFFF#32).toNat]'
                          (by omega)) ≠ 0#32)
                      rw [list_getElem_congr hoth_idx (by omega) hoth_lm, h0]; decide
                    c0_hsteps!; refine hJclean (true, _, ()) mp ⟨hmp, fun _ => ?_⟩
                    exact bin_subsumes_unass hw hcl0 hoth_lt
                      (by dsimp only [other]; rw [hw0_eq]; exact hent_bin) hmin_in (Or.inr hoth_in)
                  · c0_hsteps!; exact ihp (p + (1 : BitVec 64), ()) mp (by dsimp only; omega)
                      ⟨hmp, by omega, by omega, rem - 1, by omega, by rwa [hp1]⟩
                · c0_hsteps!; exact ihp (p + (1 : BitVec 64), ()) mp (by dsimp only; omega)
                    ⟨hmp, by omega, by omega, rem - 1, by omega, by rwa [hp1]⟩
            · c0_hsteps!; exact ihp (p + (1 : BitVec 64), ()) mp (by dsimp only; omega)
                ⟨hmp, by omega, by omega, rem - 1, by omega, by rwa [hp1]⟩
          · exfalso; apply hc; rw [hw0_eq]; exact hf0
        · rcases hpop with ⟨hf_ne, _⟩ | ⟨_, hrem2, cr, hcr_get, hcr_mem, hrest⟩
          · exfalso; exact hf_ne (by simpa [hw0_eq] using hc)
          · have hp11 : (p + (1 : BitVec 64) + (1 : BitVec 64)).toNat = p.toNat + 2 := by bv_omega
            clear hc; c0_hsplit
            · exfalso
              have hge : (off + wsz).toNat ≤ (p + (1 : BitVec 64)).toNat := by
                dsimp only [off, wsz]
                rw [BitVec.toNat_add, bv_zext32_toNat, bv_zext32_toNat,
                  list_getElem_congr hmw0_n hmw0_lt (by omega),
                  list_getElem_congr hmw1_n hmw1_lt (by omega)]
                simpa [hm0_w, hm1_w] using hc
              omega
            · have hp1_w : (p + (1 : BitVec 64)).toNat < s.core.wstk.length := by omega
              have hcr_eq : s.core.wstk[(p + (1 : BitVec 64)).toNat]'hp1_w = cr := by
                rw [list_getElem_congr hp1 hp1_w (by omega)]
                rw [List.getElem?_eq_getElem (by omega)] at hcr_get
                exact Option.some.inj hcr_get
              have hwf := hw.arena.refs_wf cr.toNat hcr_mem
              have hcr_arr : (cr.setWidth 64).toNat < s.core.arena.length := by
                rw [bv_zext32_toNat]; omega
              have hcr2_arr : ((cr.setWidth 64) + (2 : BitVec 64)).toNat <
                  s.core.arena.length := by
                have : ((cr.setWidth 64) + (2 : BitVec 64)).toNat = cr.toNat + 2 := by bv_omega
                omega
              clear hc; c0_hsplit
              · c0_hsteps!
                exact ihp (p + (1 : BitVec 64) + (1 : BitVec 64), ()) mp (by dsimp only; omega)
                  ⟨hmp, by omega, by omega, rem - 2, by omega, by rwa [hp11]⟩
              · have hp1_mod :
                    (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
                      (p + (1 : BitVec 64)).toNat := by
                  have h1 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
                  rw [h1, hp1, Nat.mod_eq_of_lt]; omega
                have hcr_toNat :
                    (s.core.wstk[(p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                      rw [hp1_mod]; exact hp1_w)).toNat = cr.toNat := by
                  have h := list_getElem_congr hp1_mod (by rw [hp1_mod]; exact hp1_w) hp1_w
                  rw [hcr_eq] at h; exact congrArg BitVec.toNat h
                have hng_raw :
                    s.core.arena[cr.toNat]'(by omega) &&& (524288#32 ||| 4194304#32) = 0#32 := by
                  rw [← list_getElem_congr hcr_toNat (by omega) (by omega)]; exact hc
                have hng : fullArenaClauseGarb s cr.toNat = false := by
                  unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  exact hck_garb_false_of_and hng_raw
                let sz := s.core.arena[((cr.setWidth 64) + (2 : BitVec 64)).toNat]'hcr2_arr
                have hsz_nat : sz.toNat = fullArenaClauseSize s cr.toNat := by
                  dsimp only [sz]; unfold fullArenaClauseSize fullArenaClauseSizeCore
                  have h2 : ((cr.setWidth 64) + (2 : BitVec 64)).toNat = cr.toNat + 2 := by
                    bv_omega
                  rw [list_getElem_congr h2 hcr2_arr (by omega),
                    List.getElem?_eq_getElem (by omega), Option.getD_some]
                have hsz_mod :
                    ((s.core.wstk[(p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                      rw [hp1_mod]; exact hp1_w)).toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
                      ((cr.setWidth 64) + (2 : BitVec 64)).toNat := by
                  have h2 : BitVec.toNat (2 : BitVec 64) = 2 := rfl
                  have h2' : ((cr.setWidth 64) + (2 : BitVec 64)).toNat = cr.toNat + 2 := by
                    bv_omega
                  rw [hcr_toNat, h2, h2', Nat.mod_eq_of_lt (by omega)]
                have hsz_unfold :
                    (s.core.arena[((s.core.wstk[(p.toNat + BitVec.toNat (1 : BitVec 64)) %
                      2 ^ 64]'(by rw [hp1_mod]; exact hp1_w)).toNat +
                      BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                        rw [hsz_mod]; exact hcr2_arr)).toNat = sz.toNat :=
                  congrArg BitVec.toNat
                    (list_getElem_congr hsz_mod (by rw [hsz_mod]; exact hcr2_arr) hcr2_arr)
                have hbd : cr.toNat + 3 + sz.toNat ≤ s.core.arena.length := by
                  rw [hsz_nat]; exact Nat.le_trans hwf.2.2.1 (Nat.le_trans hwf.2.2.2.1 (by omega))
                clear hc; c0_hsteps_nogrp
                refine LeanQbe.T.wp_join_group (ts := [.bool, i32, i32])
                  (fun (ok_m, _cnt, _dj, ()) mj => mj = mp ∧
                    (ok_m = true → (cnfOfClauses F_cur).EntailsClause
                      (cnfClause (hckUnass s.core.tmp k.toNat)))) ?_ ?_
                · rintro _ ⟨ok_m, cnt, _dj, ⟨⟩⟩ mj ⟨hmj, hokm⟩
                  c0_hsplit
                  · have hok_true : ok_m = true := hc; clear hc; c0_hsplit
                    · c0_hsteps!
                      exact hJclean (true, _, ()) mj ⟨hmj.trans hmp, fun _ => hokm hok_true⟩
                    · c0_hsteps!
                      exact ihp (p + (1 : BitVec 64) + (1 : BitVec 64), ()) mj
                        (by dsimp only; omega)
                        ⟨hmj.trans hmp, by omega, by omega, rem - 2, by omega, by rwa [hp11]⟩
                  · c0_hsteps!
                    exact ihp (p + (1 : BitVec 64) + (1 : BitVec 64), ()) mj (by dsimp only; omega)
                      ⟨hmj.trans hmp, by omega, by omega, rem - 2, by omega, by rwa [hp11]⟩
                · intro Jm hJm
                  c0_hsteps_nogrp
                  refine LeanQbe.T.wp_loop_inv (ts := [i32, i32])
                    (fun (cnt, j, ()) mj3 => mj3 = mp ∧ j.toNat ≤ sz.toNat ∧
                      ∀ q < j.toNat,
                        let cl := (s.core.arena[cr.toNat + 3 + q]?.getD 0#32).toNat
                        s.core.vals[cl]?.getD 0#8 = 0xFF#8 ∨ cl ∈ hckUnass s.core.tmp k.toNat)
                    (fun (_cnt, j, ()) _ => sz.toNat - j.toNat)
                    (fun J3 hJ3 => by
                      c0_hsteps!; exact hJ3 (0#32, 0#32, ()) mp ⟨rfl, Nat.zero_le _,
                        fun _ h => by simp at h⟩)
                    (fun J3 (cnt, j, ()) mj3 ⟨hmj3, hj_le, hcov_j⟩ ihj => ?_)
                  have hm_j3 : (FullMem c { s with core := { s.core with lit_mark := lm' } } ⋆ R)
                      mj3 := hmj3 ▸ hm_p
                  c0_hsplit
                  · have hj_lt : j.toNat < sz.toNat := by rw [← hsz_unfold]; exact hc
                    obtain ⟨hcr3j, hcl_arr, hcl_ze, hcl_lt, hcl_vals, hcl_lm_bd⟩ :=
                      hck_cl_elem_bounds hw hlen hcr_mem hng hsz_nat hbd hj_lt hcr_eq
                    let cl := s.core.arena[(BitVec.setWidth 64
                      (s.core.wstk[(p + (1 : BitVec 64)).toNat]'hp1_w) + (3 : BitVec 64) +
                      BitVec.setWidth 64 j).toNat]'hcl_arr
                    have hcl_eq : cl = s.core.arena[cr.toNat + 3 + j.toNat]?.getD 0#32 := by
                      dsimp only [cl]
                      rw [list_getElem_congr hcr3j hcl_arr (by omega),
                        List.getElem?_eq_getElem (by omega), Option.getD_some]
                    have hcl_lt' : cl.toNat < 2 * s.core.cur_vars := by rw [hcl_eq]; exact hcl_lt
                    have hcl_vals' : (BitVec.setWidth 64 cl).toNat < s.core.vals.length := by
                      rw [bv_zext32_toNat, hcl_eq]; exact hcl_vals
                    have hcl_lm : (BitVec.setWidth 64 cl).toNat < lm'.length := by
                      rw [bv_zext32_toNat, hcl_eq]; omega
                    have hcl_v : cl.toNat < s.core.vals.length := by
                      rw [← bv_zext32_toNat]; exact hcl_vals'
                    have hp1m : (p.toNat + 1) % 2 ^ 64 = (p + (1 : BitVec 64)).toNat := by
                      rw [hp1, Nat.mod_eq_of_lt]; omega
                    have hmod3j : ((s.core.wstk[(p.toNat + 1) % 2 ^ 64]'(by
                        rw [hp1m]; exact hp1_w)).toNat + 3 + j.toNat) % 2 ^ 64 =
                          (BitVec.setWidth 64 (s.core.wstk[(p + (1 : BitVec 64)).toNat]'hp1_w) +
                            (3 : BitVec 64) + BitVec.setWidth 64 j).toNat := by
                      rw [list_getElem_congr hp1m (by rw [hp1m]; exact hp1_w) hp1_w,
                        hcr3j, hcr_eq, Nat.mod_eq_of_lt (by omega)]
                    have hcl_m : (s.core.arena[((s.core.wstk[(p.toNat + 1) % 2 ^ 64]'(by
                        rw [hp1m]; exact hp1_w)).toNat + 3 + j.toNat) % 2 ^ 64]'(by
                          rw [hmod3j]; exact hcl_arr)).toNat = cl.toNat :=
                      congrArg BitVec.toNat (list_getElem_congr hmod3j _ hcl_arr)
                    have hj1 : (j + (1 : BitVec 32)).toNat = j.toNat + 1 := by bv_omega
                    clear hc; c0_hsplit
                    · c0_hsteps!; exact hJm (false, cnt, j, ()) mj3 ⟨hmj3, fun h => by cases h⟩
                    · have hnsgt : ¬ (0#32 : BitVec 32).slt
                          (BitVec.signExtend 32 (s.core.vals[cl.toNat]'hcl_v)) = true := by
                        intro hs
                        have heqv := list_getElem_congr hcl_m (by rw [hcl_m]; exact hcl_v) hcl_v
                        erw [← heqv] at hs; erw [hc] at hs; cases hs
                      clear hc; c0_hsteps_nogrp
                      refine LeanQbe.T.wp_join_group (ts := [.bool, i32])
                        (fun (_ok, cnt', ()) mj3' => mj3' = mj3 ∧
                          (s.core.vals[cl.toNat]?.getD 0#8 = 0xFF#8 ∨
                           cl.toNat ∈ hckUnass s.core.tmp k.toNat)) ?_ ?_
                      · rintro _ ⟨_ok, cnt', ⟨⟩⟩ mj3' ⟨hmj3', hcov_cl⟩
                        c0_hsteps!
                        refine ihj (cnt', j + (1 : BitVec 32), ()) mj3' (by dsimp only; omega)
                          ⟨hmj3'.trans hmj3, by omega, fun q hq => ?_⟩
                        by_cases hqj : q = j.toNat
                        · subst hqj; rw [← hcl_eq]; exact hcov_cl
                        · exact hcov_j q (by omega)
                      · intro J_add hJ_add
                        c0_hsplit
                        · clear hc; c0_hsplit
                          · c0_hsteps!
                            exact hJm (false, cnt, j, ()) mj3 ⟨hmj3, fun h => by cases h⟩
                          · have hcl_in : cl.toNat ∈ hckUnass s.core.tmp k.toNat := by
                              refine hck_unass_mem_of_litMark_ne0 hcv_le hmk.2
                                hagree_unass hcl_lt' ?_
                              intro h0; apply hc
                              rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
                              have hlm_b : cl.toNat < lm'.length :=
                                bv_zext32_toNat cl ▸ hcl_lm
                              erw [list_getElem_congr hcl_m (by rw [hcl_m]; exact hlm_b)
                                hlm_b, h0]; rfl
                            c0_hsteps!
                            exact hJ_add (true, cnt + (1 : BitVec 32), ()) mj3 ⟨rfl, Or.inr hcl_in⟩
                        · have hv_ff : s.core.vals[cl.toNat]?.getD 0#8 = 0xFF#8 := by
                            have hdom_cl : s.core.vals[cl.toNat]'hcl_v = 0#8 ∨
                                s.core.vals[cl.toNat]'hcl_v = 1#8 ∨
                                s.core.vals[cl.toNat]'hcl_v = 0xFF#8 := by
                              have hd := hw.vals_domain cl.toNat hcl_lt'
                              rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hd
                            have hneq0 : ¬ BitVec.signExtend 32 (s.core.vals[cl.toNat]'hcl_v) =
                                0#32 := by
                              intro heq; apply hc
                              erw [list_getElem_congr hcl_m (by rw [hcl_m]; exact hcl_v) hcl_v]
                              exact heq
                            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                            exact hck_bv8_ne0_not_sext_sgt0_eqff hdom_cl hnsgt hneq0
                          c0_hsteps!; exact hJ_add (true, cnt, ()) mj3 ⟨rfl, Or.inl hv_ff⟩
                  · have hj_ge : ¬ j.toNat < sz.toNat := by rw [← hsz_unfold]; exact hc
                    have hj_eq : j.toNat = sz.toNat := by omega
                    have hent_cl := hck_arena_entails_step hw hcl0 hcr_mem hng hsz_nat hbd
                      (fun q hq => hcov_j q (by omega))
                    c0_hsteps!; exact hJm (true, cnt, j, ()) mj3 ⟨hmj3, fun _ => hent_cl⟩
      · c0_hsteps!; exact hJclean (false, _, ()) mp ⟨hmp, fun h => by cases h⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence
