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


private theorem litEquiv_eval_eq {f : Std.Sat.CNF Nat} {a b : Nat}
    (h : LitEquiv f a b) {α : Nat → Bool} (hα : Std.Sat.CNF.Sat α f) :
    evalLitVal α a = evalLitVal α b :=
  litEquiv_eval hα h

private theorem andGateDef_eval_iff {f : Std.Sat.CNF Nat} {g : Nat} {xs : List Nat}
    (h : AndGateDef f g xs) {α : Nat → Bool} (hα : Std.Sat.CNF.Sat α f) :
    evalLitVal α g = xs.all (evalLitVal α) :=
  andGateDef_eval hα h

private theorem countP_range_set_delta (f g : Nat → Bool) (n x : Nat)
    (hx : x < n) (hother : ∀ i, i < n → i ≠ x → g i = f i) :
    (List.range n).countP g + (if f x then 1 else 0) =
      (List.range n).countP f + (if g x then 1 else 0) := by
  induction n with
  | zero => omega
  | succ k ih =>
    rw [List.range_succ, List.countP_append, List.countP_append]
    simp only [List.countP_cons, List.countP_nil, Nat.zero_add]
    by_cases hxk : x = k
    · subst hxk
      have hc : (List.range x).countP g = (List.range x).countP f := by
        apply List.countP_congr
        intro i hi
        rw [List.mem_range] at hi
        rw [hother i (by omega) (by omega)]
      rw [hc]
      omega
    · have hk : g k = f k := hother k (by omega) (Ne.symm hxk)
      have hrec := ih (by omega) (fun i hi hne => hother i (by omega) hne)
      rw [hk]
      omega

private def lmCount (lm : List (BitVec 8)) (n : Nat) (tgt : BitVec 8) : Nat :=
  (List.range n).countP (fun i => lm[i]?.getD 0#8 == tgt)

private theorem lmCount_set_zero_one {lm : List (BitVec 8)} {n x : Nat}
    (hx : x < n) (hnl : n ≤ lm.length) (h0 : lm[x]?.getD 0#8 = 0#8) :
    lmCount (lm.set x 1#8) n 1#8 = lmCount lm n 1#8 + 1 := by
  unfold lmCount
  have hx_len : x < lm.length := by omega
  have hd := countP_range_set_delta
    (fun i => lm[i]?.getD 0#8 == 1#8)
    (fun i => (lm.set x 1#8)[i]?.getD 0#8 == 1#8)
    n x hx (fun i _ hne => by rw [List.getElem?_set_ne (Ne.symm hne)])
  have hfx : (lm[x]?.getD 0#8 == 1#8) = false := by rw [h0]; decide
  have hgx : ((lm.set x 1#8)[x]?.getD 0#8 == 1#8) = true := by
    rw [List.getElem?_set_self hx_len, Option.getD_some]; decide
  simp only [hfx, hgx, Bool.false_eq_true, ↓reduceIte] at hd
  omega

private theorem lmCount_set_one_two {lm : List (BitVec 8)} {n x : Nat}
    (hx : x < n) (hnl : n ≤ lm.length) (h1 : lm[x]?.getD 0#8 = 1#8) :
    lmCount (lm.set x 2#8) n 1#8 + 1 = lmCount lm n 1#8 := by
  unfold lmCount
  have hx_len : x < lm.length := by omega
  have hd := countP_range_set_delta
    (fun i => lm[i]?.getD 0#8 == 1#8)
    (fun i => (lm.set x 2#8)[i]?.getD 0#8 == 1#8)
    n x hx (fun i _ hne => by rw [List.getElem?_set_ne (Ne.symm hne)])
  have hfx : (lm[x]?.getD 0#8 == 1#8) = true := by rw [h1]; decide
  have hgx : ((lm.set x 2#8)[x]?.getD 0#8 == 1#8) = false := by
    rw [List.getElem?_set_self hx_len, Option.getD_some]; decide
  simp only [hfx, hgx, Bool.false_eq_true, ↓reduceIte] at hd
  omega

private theorem lmCount_eq_zero_of_all {lm : List (BitVec 8)} {n : Nat}
    (h0 : lmCount lm n 1#8 = 0) {x : Nat} (hx : x < n) :
    lm[x]?.getD 0#8 ≠ 1#8 := by
  unfold lmCount at h0
  rw [List.countP_eq_zero] at h0
  have h := h0 x (List.mem_range.mpr hx)
  simp only [beq_iff_eq] at h
  exact h

private theorem andMatch_sound_post {F_cur : List (List Nat)}
    {scr0 : List (BitVec 32)} {ent : Nat} {arity ua lhs : Nat}
    {tmp : List (BitVec 32)} {lm : List (BitVec 8)} {n : Nat}
    (hmrk : lmCount lm n 1#8 = 0)
    (hand : AndGateDef (cnfOfClauses F_cur) lhs
      (List.map BitVec.toNat (List.take arity (List.drop (ent + 2) scr0))))
    (hscr_len : ent + 2 + arity ≤ scr0.length)
    (hclosed : ∀ idx, idx < arity → ∀ α, Std.Sat.CNF.Sat α (cnfOfClauses F_cur) →
      evalLitVal α (scr0[ent + 2 + idx]?.getD 0#32).toNat = true ∨
      ∃ k, k < ua ∧ LitEquiv (cnfOfClauses F_cur)
        (scr0[ent + 2 + idx]?.getD 0#32).toNat (tmp[k]?.getD 0#32).toNat)
    (h2_rev : ∀ x, x < n → lm[x]?.getD 0#8 = 2#8 →
      ∃ idx, idx < arity ∧ LitEquiv (cnfOfClauses F_cur)
        (scr0[ent + 2 + idx]?.getD 0#32).toNat x)
    (htmp_ok : ∀ k, k < ua → (tmp[k]?.getD 0#32).toNat < n ∧
      (lm[(tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
       lm[(tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 2#8)) :
    ∀ α, Std.Sat.CNF.Sat α (cnfOfClauses F_cur) →
      evalLitVal α lhs =
        (List.range ua).all (fun k => evalLitVal α (tmp[k]?.getD 0#32).toNat) := by
  intro α hα
  rw [andGateDef_eval_iff hand hα]
  by_cases hall : (List.range ua).all (fun k => evalLitVal α (tmp[k]?.getD 0#32).toNat) = true
  · rw [hall, List.all_eq_true]
    intro l hl
    rw [List.mem_map] at hl
    rcases hl with ⟨bv, hbv, rfl⟩
    rw [List.mem_iff_getElem] at hbv
    rcases hbv with ⟨idx, hidx_lt, hbv_eq⟩
    simp only [List.length_take, List.length_drop] at hidx_lt
    have hidx : idx < arity := by omega
    have hget : bv = scr0[ent + 2 + idx]?.getD 0#32 := by
      rw [← hbv_eq]; simp [List.getElem_take, List.getElem_drop]
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [hget]
    rcases hclosed idx hidx α hα with ht | ⟨k, hk, heq⟩
    · exact ht
    · rw [litEquiv_eval_eq heq hα]
      rw [List.all_eq_true] at hall
      exact hall k (List.mem_range.mpr hk)
  · have hallf : (List.range ua).all
        (fun k => evalLitVal α (tmp[k]?.getD 0#32).toNat) = false :=
      Bool.eq_false_iff.mpr hall
    rw [hallf]
    rw [List.all_eq_true] at hall
    simp only [List.mem_range] at hall
    have hk_ex : ∃ k, k < ua ∧ evalLitVal α (tmp[k]?.getD 0#32).toNat = false := by
      by_cases hmem : ∃ k, k < ua ∧ evalLitVal α (tmp[k]?.getD 0#32).toNat = false
      · exact hmem
      · exfalso; apply hall; intro k hk
        cases hv : evalLitVal α (tmp[k]?.getD 0#32).toNat
        · exact absurd ⟨k, hk, hv⟩ hmem
        · rfl
    rcases hk_ex with ⟨k, hk, hkf⟩
    obtain ⟨hx_lt, hlmo⟩ := htmp_ok k hk
    have hne1 := lmCount_eq_zero_of_all hmrk hx_lt
    have h2 : lm[(tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 2#8 := by
      rcases hlmo with h1 | h2
      · exact absurd h1 hne1
      · exact h2
    obtain ⟨idx, hidx, heq⟩ := h2_rev _ hx_lt h2
    have hmem : (scr0[ent + 2 + idx]?.getD 0#32).toNat ∈
        List.map BitVec.toNat (List.take arity (List.drop (ent + 2) scr0)) := by
      rw [List.mem_map]
      refine ⟨scr0[ent + 2 + idx]'(by omega), ?_, ?_⟩
      · rw [List.mem_iff_getElem]
        refine ⟨idx, ?_, ?_⟩
        · simp [List.length_take, List.length_drop]; omega
        · simp [List.getElem_take, List.getElem_drop]
      · rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    by_cases hall2 : (List.map BitVec.toNat
        (List.take arity (List.drop (ent + 2) scr0))).all (evalLitVal α) = true
    · rw [List.all_eq_true] at hall2
      have ht := hall2 _ hmem
      rw [litEquiv_eval_eq heq hα, hkf] at ht
      cases ht
    · exact Bool.eq_false_iff.mpr hall2

private theorem clear_lit_marks_nz_step {lmc : List (BitVec 8)}
    {tmp : List (BitVec 32)} {k upper x : Nat}
    (hk : k < upper) (htk : (tmp[k]?.getD 0#32).toNat < lmc.length)
    (hnzc : ∀ y, lmc[y]?.getD 0#8 ≠ 0#8 →
      ∃ p, k ≤ p ∧ p < upper ∧ (tmp[p]?.getD 0#32).toNat = y ∧ y < lmc.length)
    (hx : (lmc.set (tmp[k]?.getD 0#32).toNat 0#8)[x]?.getD 0#8 ≠ 0#8) :
    ∃ p, k + 1 ≤ p ∧ p < upper ∧ (tmp[p]?.getD 0#32).toNat = x ∧ x < lmc.length := by
  by_cases hxe : x = (tmp[k]?.getD 0#32).toNat
  · subst hxe
    rw [List.getElem?_set_self htk, Option.getD_some] at hx
    exact absurd rfl hx
  · rw [List.getElem?_set_ne (Ne.symm hxe)] at hx
    obtain ⟨p, hkp, hpu, hpx, hxl⟩ := hnzc x hx
    have hne : p ≠ k := by rintro rfl; exact hxe hpx.symm
    exact ⟨p, by omega, hpu, hpx, hxl⟩

private theorem andMatch_loop1_mark_inv {lm1 : List (BitVec 8)}
    {tmp : List (BitVec 32)} {i cur_vars max_vars : Nat} {marked l : BitVec 32}
    (hlml1 : lm1.length = 2 * max_vars) (hcv_le : cur_vars ≤ max_vars)
    (hi_lt : i < cur_vars) (hl_lt : l.toNat < 2 * cur_vars) (hl_eq : l = tmp[i]?.getD 0#32)
    (hl0 : lm1[l.toNat]?.getD 0#8 = 0#8) (hcnt1 : lmCount lm1 (2 * cur_vars) 1#8 = marked.toNat)
    (hdom1 : ∀ x, x < 2 * max_vars → lm1[x]?.getD 0#8 = 0#8 ∨ lm1[x]?.getD 0#8 = 1#8)
    (hnz1 : ∀ x, lm1[x]?.getD 0#8 ≠ 0#8 →
      ∃ k, k < i ∧ (tmp[k]?.getD 0#32).toNat = x ∧ x < 2 * cur_vars)
    (htmp1 : ∀ k, k < i → (tmp[k]?.getD 0#32).toNat < 2 * cur_vars ∧
      lm1[(tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8) :
    let lm1' := lm1.set l.toNat 1#8
    (∀ x, x < 2 * max_vars → lm1'[x]?.getD 0#8 = 0#8 ∨ lm1'[x]?.getD 0#8 = 1#8) ∧
    (∀ x, lm1'[x]?.getD 0#8 ≠ 0#8 →
      ∃ k, k < i + 1 ∧ (tmp[k]?.getD 0#32).toNat = x ∧ x < 2 * cur_vars) ∧
    (∀ k, k < i + 1 → (tmp[k]?.getD 0#32).toNat < 2 * cur_vars ∧
      lm1'[(tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8) ∧
    lmCount lm1' (2 * cur_vars) 1#8 = marked.toNat + 1 := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun k hk => ?_, ?_⟩
  · by_cases hxe : x = l.toNat
    · subst hxe; right; rw [List.getElem?_set_self (by omega), Option.getD_some]
    · rw [List.getElem?_set_ne (Ne.symm hxe)]; exact hdom1 x hx
  · by_cases hxe : x = l.toNat
    · subst hxe; exact ⟨i, by omega, by rw [hl_eq], hl_lt⟩
    · rw [List.getElem?_set_ne (Ne.symm hxe)] at hx
      obtain ⟨k, hk, hkx⟩ := hnz1 x hx
      exact ⟨k, by omega, hkx⟩
  · by_cases hki : k = i
    · subst hki; rw [← hl_eq]
      exact ⟨hl_lt, by rw [List.getElem?_set_self (by omega), Option.getD_some]⟩
    · obtain ⟨hk_lt, hk1⟩ := htmp1 k (by omega)
      refine ⟨hk_lt, ?_⟩
      by_cases hke : (tmp[k]?.getD 0#32).toNat = l.toNat
      · rw [hke, List.getElem?_set_self (by omega), Option.getD_some]
      · rw [List.getElem?_set_ne (Ne.symm hke)]; exact hk1
  · rw [lmCount_set_zero_one hl_lt (by omega) hl0, hcnt1]

private theorem andMatch_loop2_mark_inv {lm2 : List (BitVec 8)}
    {tmp scr0 : List (BitVec 32)} {F_cur : List (List Nat)}
    {ent j arity ua cur_vars max_vars : Nat} {cnt r gl : BitVec 32}
    (hlml2 : lm2.length = 2 * max_vars) (hcv_le : cur_vars ≤ max_vars)
    (hj_lt : j < arity) (hr_lt : r.toNat < 2 * cur_vars)
    (hgl_eq : gl = scr0[ent + 2 + j]?.getD 0#32)
    (heq_gl : LitEquiv (cnfOfClauses F_cur) gl.toNat r.toNat)
    (hrlm1 : lm2[r.toNat]?.getD 0#8 = 1#8)
    {marked_nat : Nat} (hcnt_eq : lmCount lm2 (2 * cur_vars) 1#8 + cnt.toNat = marked_nat)
    {kr : Nat} (hkr_ua : kr < ua) (hkr_eq : (tmp[kr]?.getD 0#32).toNat = r.toNat)
    (hdom2 : ∀ x, x < 2 * max_vars →
      lm2[x]?.getD 0#8 = 0#8 ∨ lm2[x]?.getD 0#8 = 1#8 ∨ lm2[x]?.getD 0#8 = 2#8)
    (hnz2 : ∀ x, lm2[x]?.getD 0#8 ≠ 0#8 →
      ∃ k, k < ua ∧ (tmp[k]?.getD 0#32).toNat = x)
    (htmp2 : ∀ k, k < ua →
      lm2[(tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
      lm2[(tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 2#8)
    (h2_rev : ∀ x, x < 2 * cur_vars → lm2[x]?.getD 0#8 = 2#8 →
      ∃ idx, idx < arity ∧ LitEquiv (cnfOfClauses F_cur)
        (scr0[ent + 2 + idx]?.getD 0#32).toNat x) :
    let lm2' := lm2.set r.toNat 2#8
    (0 < lmCount lm2 (2 * cur_vars) 1#8) ∧
    (∀ x, x < 2 * max_vars →
      lm2'[x]?.getD 0#8 = 0#8 ∨ lm2'[x]?.getD 0#8 = 1#8 ∨ lm2'[x]?.getD 0#8 = 2#8) ∧
    (∀ x, lm2'[x]?.getD 0#8 ≠ 0#8 → ∃ k, k < ua ∧ (tmp[k]?.getD 0#32).toNat = x) ∧
    (lmCount lm2' (2 * cur_vars) 1#8 + (cnt.toNat + 1) = marked_nat) ∧
    (∀ k, k < ua →
      lm2'[(tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
      lm2'[(tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 2#8) ∧
    (∀ x, x < 2 * cur_vars → lm2'[x]?.getD 0#8 = 2#8 →
      ∃ idx, idx < arity ∧ LitEquiv (cnfOfClauses F_cur)
        (scr0[ent + 2 + idx]?.getD 0#32).toNat x) := by
  have hpos : 0 < lmCount lm2 (2 * cur_vars) 1#8 := by
    unfold lmCount
    by_cases hz : (List.range (2 * cur_vars)).countP
        (fun i => lm2[i]?.getD 0#8 == 1#8) = 0
    · exfalso
      rw [List.countP_eq_zero] at hz
      have hmem := hz r.toNat (List.mem_range.mpr hr_lt)
      simp only [hrlm1, beq_self_eq_true] at hmem
      exact hmem trivial
    · omega
  refine ⟨hpos, fun x hx => ?_, fun x hx => ?_, ?_, fun k hk => ?_, fun x hx h2 => ?_⟩
  · by_cases hxe : x = r.toNat
    · subst hxe; right; right; rw [List.getElem?_set_self (by omega), Option.getD_some]
    · rw [List.getElem?_set_ne (Ne.symm hxe)]; exact hdom2 x hx
  · by_cases hxe : x = r.toNat
    · subst hxe; exact ⟨kr, hkr_ua, hkr_eq⟩
    · rw [List.getElem?_set_ne (Ne.symm hxe)] at hx; exact hnz2 x hx
  · have hsub := lmCount_set_one_two hr_lt (by omega) hrlm1
    omega
  · by_cases hke : (tmp[k]?.getD 0#32).toNat = r.toNat
    · rw [hke]; right; rw [List.getElem?_set_self (by omega), Option.getD_some]
    · rw [List.getElem?_set_ne (Ne.symm hke)]; exact htmp2 k hk
  · by_cases hxe : x = r.toNat
    · subst hxe; exact ⟨j, hj_lt, by rw [← hgl_eq]; exact heq_gl⟩
    · rw [List.getElem?_set_ne (Ne.symm hxe)] at h2; exact h2_rev x hx h2

private theorem andMatch_gate_facts {maxA : Nat} {F_cur : List (List Nat)}
    {cur_vars g_len ent : Nat} {scr0 : List (BitVec 32)}
    (hgat : CongGateAt maxA F_cur cur_vars scr0 g_len ent)
    (htag_mword : scr0[ent + 1]?.getD 0#32 >>> 28 = 0#32 ∨
      scr0[ent + 1]?.getD 0#32 >>> 28 = 3#32) :
    ∃ lhs mword, scr0[ent]? = some lhs ∧ scr0[ent + 1]? = some mword ∧
      lhs.toNat < 2 * cur_vars ∧ ent + 2 + congGateArity mword ≤ g_len ∧
      congGateArity mword ≤ cur_vars ∧ congGateArity mword ≤ maxA ∧
      2 ≤ congGateArity mword ∧ ent + 2 + congGateArity mword ≤ scr0.length ∧
      (∀ k, k < congGateArity mword → ∃ r, scr0[ent + 2 + k]? = some r ∧ r.toNat < 2 * cur_vars) ∧
      AndGateDef (cnfOfClauses F_cur) lhs.toNat
        (List.map BitVec.toNat (List.take (congGateArity mword) (List.drop (ent + 2) scr0))) := by
  rcases hgat with ⟨lhs, mword, hlhs, hmword, hlhs_lt, hge_g, har_le, har_max, hrhs, hcase⟩
  have hmw_get : scr0[ent + 1]?.getD 0#32 = mword := by rw [hmword, Option.getD_some]
  have ht03 : (mword >>> 28).toNat = 0 ∨ (mword >>> 28).toNat = 3 := by
    rcases htag_mword with h0 | h3
    · left; rw [← hmw_get, h0]; rfl
    · right; rw [← hmw_get, h3]; rfl
  have h2_and : 2 ≤ congGateArity mword ∧ AndGateDef (cnfOfClauses F_cur) lhs.toNat
      (List.map BitVec.toNat (List.take (congGateArity mword) (List.drop (ent + 2) scr0))) := by
    rcases hcase with h03 | h1 | h2
    · rcases h03 with ⟨h0 | h3, ha⟩
      · exact ⟨h0.2.1, ha⟩
      · exact ⟨by omega, ha⟩
    · exact absurd ht03 (by omega)
    · exact absurd ht03 (by omega)
  have hscr_len : ent + 2 + congGateArity mword ≤ scr0.length := by
    obtain ⟨_, hr, _⟩ := hrhs (congGateArity mword - 1) (by omega)
    by_cases hb : ent + 2 + (congGateArity mword - 1) < scr0.length
    · omega
    · rw [List.getElem?_eq_none (by omega)] at hr; cases hr
  exact ⟨lhs, mword, hlhs, hmword, hlhs_lt, hge_g, har_le, har_max, h2_and.1,
    hscr_len, hrhs, h2_and.2⟩

private theorem fullCongReprInv_of_andMatch {F_cur : List (List Nat)}
    {s : FullState} {scr0 : List (BitVec 32)} {lhs mword ent ua : Nat}
    {marked cnt : BitVec 32} {lm2 : List (BitVec 8)}
    (hlhs : scr0[ent]? = some (BitVec.ofNat 32 lhs))
    (hmrk : lmCount lm2 (2 * s.core.cur_vars) 1#8 + cnt.toNat = marked.toNat)
    (hcnt_eq : cnt.toNat = marked.toNat)
    (hand : AndGateDef (cnfOfClauses F_cur) lhs
      (List.map BitVec.toNat (List.take (congGateArity mword) (List.drop (ent + 2) scr0))))
    (hscr_len : ent + 2 + congGateArity mword ≤ scr0.length)
    (hclosed : ∀ idx, idx < congGateArity mword → ∀ α, Std.Sat.CNF.Sat α (cnfOfClauses F_cur) →
      evalLitVal α (scr0[ent + 2 + idx]?.getD 0#32).toNat = true ∨
      ∃ k, k < ua ∧ LitEquiv (cnfOfClauses F_cur)
        (scr0[ent + 2 + idx]?.getD 0#32).toNat (s.core.tmp[k]?.getD 0#32).toNat)
    (h2_rev : ∀ x, x < 2 * s.core.cur_vars → lm2[x]?.getD 0#8 = 2#8 →
      ∃ idx, idx < congGateArity mword ∧ LitEquiv (cnfOfClauses F_cur)
        (scr0[ent + 2 + idx]?.getD 0#32).toNat x)
    (htmp_ok : ∀ k, k < ua → (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      (lm2[(s.core.tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
       lm2[(s.core.tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 2#8))
    (hlhs_lt : lhs < 2 ^ 32) :
    ∀ α, Std.Sat.CNF.Sat α (cnfOfClauses F_cur) →
      evalLitVal α (scr0[ent]?.getD 0#32).toNat =
        (List.range ua).all (fun k => evalLitVal α (s.core.tmp[k]?.getD 0#32).toNat) := by
  have h1_0 : lmCount lm2 (2 * s.core.cur_vars) 1#8 = 0 := by omega
  have hres := andMatch_sound_post h1_0 hand hscr_len hclosed h2_rev htmp_ok
  intro α hα
  rw [hlhs, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlhs_lt]
  exact hres α hα

private def andMatchLoop2Inv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (scr0 : List (BitVec 32)) (ent ua marked mword : BitVec 32)
    (R : Mem 64 → Prop) (cnt_nat bound_idx : Nat) (mc : Mem 64) : Prop :=
  cnt_nat ≤ marked.toNat ∧
  ∃ (repr2 : List (BitVec 32)) (lm2 : List (BitVec 8)),
    repr2.length = 2 * c.max_vars ∧ lm2.length = 2 * c.max_vars ∧
    FullCongReprInv F_cur (2 * s.core.cur_vars) repr2 ∧
    lmCount lm2 (2 * s.core.cur_vars) 1#8 + cnt_nat = marked.toNat ∧
    (∀ x, x < 2 * c.max_vars →
      lm2[x]?.getD 0#8 = 0#8 ∨ lm2[x]?.getD 0#8 = 1#8 ∨ lm2[x]?.getD 0#8 = 2#8) ∧
    (∀ x, lm2[x]?.getD 0#8 ≠ 0#8 →
      ∃ k, k < ua.toNat ∧ (s.core.tmp[k]?.getD 0#32).toNat = x) ∧
    (∀ k, k < ua.toNat → (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      (lm2[(s.core.tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
       lm2[(s.core.tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 2#8)) ∧
    (∀ idx, idx < bound_idx → ∀ α, Std.Sat.CNF.Sat α (cnfOfClauses F_cur) →
      evalLitVal α (scr0[ent.toNat + 2 + idx]?.getD 0#32).toNat = true ∨
      ∃ k, k < ua.toNat ∧ LitEquiv (cnfOfClauses F_cur)
        (scr0[ent.toNat + 2 + idx]?.getD 0#32).toNat (s.core.tmp[k]?.getD 0#32).toNat) ∧
    (∀ x, x < 2 * s.core.cur_vars → lm2[x]?.getD 0#8 = 2#8 →
      ∃ idx, idx < congGateArity mword ∧ LitEquiv (cnfOfClauses F_cur)
        (scr0[ent.toNat + 2 + idx]?.getD 0#32).toNat x) ∧
    (FullMem c { s with core := { s.core with lit_mark := lm2, repr := repr2 } } ⋆ R) mc

private theorem fullLitMarksClear_of_clear {c : FullCfg} {s : FullState}
    {lm : List (BitVec 8)} {repr : List (BitVec 32)} {upper : Nat}
    (hmrk0 : FullMrkZero c s)
    (hnz : ∀ y, lm[y]?.getD 0#8 ≠ 0#8 →
      ∃ p, upper ≤ p ∧ p < upper ∧ (s.core.tmp[p]?.getD 0#32).toNat = y ∧ y < 2 * c.max_vars) :
    FullLitMarksClear c { s with core := { s.core with lit_mark := lm, repr := repr } } := by
  refine ⟨hmrk0, fun x _ => ?_⟩
  by_cases h0 : lm[x]?.getD 0#8 = 0#8
  · exact h0
  · obtain ⟨_, hp1, hp2, _⟩ := hnz x h0; omega

private theorem andMatch_mem_set_lm {c : FullCfg} {s : FullState}
    {lm : List (BitVec 8)} {repr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {idx1 idx2 : Nat} (hidx : idx1 = idx2) {v : BitVec 8}
    (hm : (FullMem c { s with core := { s.core with
        lit_mark := lm.set idx1 v, repr := repr } } ⋆ R) m) :
    (FullMem c { s with core := { s.core with
        lit_mark := lm.set idx2 v, repr := repr } } ⋆ R) m :=
  hidx ▸ hm

private theorem lm_ne0_of_zext_ne {lm : List (BitVec 8)} {k : Nat} (hk : k < lm.length)
    (h : BitVec.setWidth 32 (lm[k]'hk) ≠ BitVec.ofNat 32 0) :
    lm[k]?.getD 0#8 ≠ 0#8 := by
  intro hz; apply h
  rw [List.getElem?_eq_getElem hk, Option.getD_some] at hz
  rw [hz]; rfl

private theorem andMatch_closed_step {F_cur : List (List Nat)} {scr0 tmp : List (BitVec 32)}
    {ent ua j : BitVec 32} {gl r : BitVec 32}
    (hgl_eq : scr0[ent.toNat + 2 + j.toNat]? = some gl)
    (heq_gl : LitEquiv (cnfOfClauses F_cur) gl.toNat r.toNat)
    (hclosed2 : ∀ idx, idx < j.toNat → ∀ α, Std.Sat.CNF.Sat α (cnfOfClauses F_cur) →
      evalLitVal α (scr0[ent.toNat + 2 + idx]?.getD 0#32).toNat = true ∨
      ∃ k, k < ua.toNat ∧ LitEquiv (cnfOfClauses F_cur)
        (scr0[ent.toNat + 2 + idx]?.getD 0#32).toNat (tmp[k]?.getD 0#32).toNat)
    (kr : Nat) (hkr_ua : kr < ua.toNat) (hkr_eq : (tmp[kr]?.getD 0#32).toNat = r.toNat) :
    ∀ idx, idx < j.toNat + 1 → ∀ α, Std.Sat.CNF.Sat α (cnfOfClauses F_cur) →
      evalLitVal α (scr0[ent.toNat + 2 + idx]?.getD 0#32).toNat = true ∨
      ∃ k, k < ua.toNat ∧ LitEquiv (cnfOfClauses F_cur)
        (scr0[ent.toNat + 2 + idx]?.getD 0#32).toNat (tmp[k]?.getD 0#32).toNat := by
  intro idx hidx α hα
  by_cases hij : idx = j.toNat
  · subst hij; right; refine ⟨kr, hkr_ua, ?_⟩
    rw [hgl_eq, Option.getD_some, hkr_eq]; exact heq_gl
  · exact hclosed2 idx (by omega) α hα

private theorem andMatch_closed_true_step {c : FullCfg} {F0 : Std.Sat.CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {scr0 tmp : List (BitVec 32)}
    {ent ua j : BitVec 32} {gl r : BitVec 32}
    (hwit : FullWitnessInv c F0 F_cur s.core) (hclv0 : s.core.cur_level = 0)
    (hr_lt : r.toNat < 2 * s.core.cur_vars) (hr_vl : r.toNat < s.core.vals.length)
    (hdom_v : s.core.vals[r.toNat]?.getD 0#8 = 0#8 ∨ s.core.vals[r.toNat]?.getD 0#8 = 1#8 ∨
      s.core.vals[r.toNat]?.getD 0#8 = 255#8)
    (hv_ne0 : BitVec.signExtend 32 (s.core.vals[r.toNat]'hr_vl) ≠ 0#32)
    (h_slt0 : BitVec.slt (BitVec.signExtend 32 (s.core.vals[r.toNat]'hr_vl)) 0#32 = false)
    (hgl_eq : scr0[ent.toNat + 2 + j.toNat]? = some gl)
    (heq_gl : LitEquiv (cnfOfClauses F_cur) gl.toNat r.toNat)
    (hclosed2 : ∀ idx, idx < j.toNat → ∀ α, Std.Sat.CNF.Sat α (cnfOfClauses F_cur) →
      evalLitVal α (scr0[ent.toNat + 2 + idx]?.getD 0#32).toNat = true ∨
      ∃ k, k < ua.toNat ∧ LitEquiv (cnfOfClauses F_cur)
        (scr0[ent.toNat + 2 + idx]?.getD 0#32).toNat (tmp[k]?.getD 0#32).toNat) :
    ∀ idx, idx < j.toNat + 1 → ∀ α, Std.Sat.CNF.Sat α (cnfOfClauses F_cur) →
      evalLitVal α (scr0[ent.toNat + 2 + idx]?.getD 0#32).toNat = true ∨
      ∃ k, k < ua.toNat ∧ LitEquiv (cnfOfClauses F_cur)
        (scr0[ent.toNat + 2 + idx]?.getD 0#32).toNat (tmp[k]?.getD 0#32).toNat := by
  have hv_eq1 : s.core.vals[r.toNat]?.getD 0#8 = 1#8 := by
    rw [List.getElem?_eq_getElem hr_vl, Option.getD_some] at hdom_v ⊢
    rcases hdom_v with h | h | h <;> rw [h] at hv_ne0 h_slt0
    · exact absurd rfl hv_ne0
    · exact h
    · exact absurd h_slt0 (by decide)
  intro idx hidx α hα
  by_cases hij : idx = j.toNat
  · subst hij; left
    have hval_t := entails_eval_true (vals1_entails hwit hclv0 hr_lt hv_eq1) hα
    rw [hgl_eq, Option.getD_some, litEquiv_eval hα heq_gl, hval_t]
  · exact hclosed2 idx (by omega) α hα

private def andMatchLoop2Post (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (scr0 : List (BitVec 32)) (ent ua marked mword : BitVec 32) (R : Mem 64 → Prop)
    (xs : Tup Val [Ty.bool, i32, i32]) (mc : Mem 64) : Prop :=
  ∃ (repr2 : List (BitVec 32)) (lm2 : List (BitVec 8)),
    repr2.length = 2 * c.max_vars ∧ lm2.length = 2 * c.max_vars ∧
    FullCongReprInv F_cur (2 * s.core.cur_vars) repr2 ∧
    (∀ x, lm2[x]?.getD 0#8 ≠ 0#8 → ∃ k, k < ua.toNat ∧ (s.core.tmp[k]?.getD 0#32).toNat = x) ∧
    (xs.fst = true →
      lmCount lm2 (2 * s.core.cur_vars) 1#8 + xs.snd.fst.toNat = marked.toNat ∧
      (∀ idx, idx < congGateArity mword → ∀ α, Std.Sat.CNF.Sat α (cnfOfClauses F_cur) →
        evalLitVal α (scr0[ent.toNat + 2 + idx]?.getD 0#32).toNat = true ∨
        ∃ k, k < ua.toNat ∧ LitEquiv (cnfOfClauses F_cur)
          (scr0[ent.toNat + 2 + idx]?.getD 0#32).toNat (s.core.tmp[k]?.getD 0#32).toNat) ∧
      (∀ x, x < 2 * s.core.cur_vars → lm2[x]?.getD 0#8 = 2#8 →
        ∃ idx, idx < congGateArity mword ∧ LitEquiv (cnfOfClauses F_cur)
          (scr0[ent.toNat + 2 + idx]?.getD 0#32).toNat x) ∧
      (∀ k, k < ua.toNat → (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
        (lm2[(s.core.tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
         lm2[(s.core.tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 2#8))) ∧
    (FullMem c { s with core := { s.core with lit_mark := lm2, repr := repr2 } } ⋆ R) mc

private theorem andMatch_sound_wrap {F_cur : List (List Nat)} {s : FullState}
    {scr0 : List (BitVec 32)} {lhs mword marked cnt : BitVec 32} {ent ua : Nat}
    {lm2 : List (BitVec 8)}
    (hlhs : scr0[ent]? = some lhs)
    (hcnt_m : lmCount lm2 (2 * s.core.cur_vars) 1#8 + cnt.toNat = marked.toNat)
    (hcnt_eq : cnt.toNat = marked.toNat)
    (hand : AndGateDef (cnfOfClauses F_cur) lhs.toNat
      (List.map BitVec.toNat (List.take (congGateArity mword) (List.drop (ent + 2) scr0))))
    (hscr_len : ent + 2 + congGateArity mword ≤ scr0.length)
    (hclosed : ∀ idx, idx < congGateArity mword → ∀ α, Std.Sat.CNF.Sat α (cnfOfClauses F_cur) →
      evalLitVal α (scr0[ent + 2 + idx]?.getD 0#32).toNat = true ∨
      ∃ k, k < ua ∧ LitEquiv (cnfOfClauses F_cur)
        (scr0[ent + 2 + idx]?.getD 0#32).toNat (s.core.tmp[k]?.getD 0#32).toNat)
    (h2_rev : ∀ x, x < 2 * s.core.cur_vars → lm2[x]?.getD 0#8 = 2#8 →
      ∃ idx, idx < congGateArity mword ∧
        LitEquiv (cnfOfClauses F_cur) (scr0[ent + 2 + idx]?.getD 0#32).toNat x)
    (htmp_ok : ∀ k, k < ua → (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      (lm2[(s.core.tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
       lm2[(s.core.tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 2#8))
    (hlhs_u32 : lhs.toNat < 2 ^ 32) :
    ∀ α, Std.Sat.CNF.Sat α (cnfOfClauses F_cur) →
      evalLitVal α (scr0[ent]?.getD 0#32).toNat =
        (List.range ua).all fun k => evalLitVal α (s.core.tmp[k]?.getD 0#32).toNat := by
  have hlhs' : scr0[ent]? = some (BitVec.ofNat 32 lhs.toNat) := by
    rw [show BitVec.ofNat 32 lhs.toNat = lhs by bv_omega]; exact hlhs
  have hmw : (↑mword.toNat : BitVec 32) = mword := by
    apply BitVec.eq_of_toNat_eq; simp
  exact fullCongReprInv_of_andMatch (mword := mword.toNat) hlhs' hcnt_m hcnt_eq
    (by rw [hmw]; exact hand) (by rw [hmw]; exact hscr_len)
    (by rw [hmw]; exact hclosed) (by rw [hmw]; exact h2_rev)
    htmp_ok hlhs_u32

public section

theorem full_cong_and_match_wp {Γ : Env}
    (hFind : Γ.Has "full_cong_find" Spec.fullCongFindSpec) :
    ∀ args m Q X,
      Spec.fullCongAndMatchSpec args m Q X → Func.wp Γ full_cong_and_match_body args m Q X := by
  rintro ⟨h_arg, ent, ua, ⟨⟩⟩ m0 Q X ⟨maxA, c, F0, F_cur, s, scr0, g_len, R,
    hmaxA, rfl, hlen, hwit, hlm_clr, hclv0, hrepr, hg_le, hscr_eq, hgat, htag,
    hua_le, hm0, hQ⟩
  obtain ⟨lhs, mword, hlhs, hmword, hlhs_lt, hge_g, har_le_cv, har_le_max, har_ge2,
    hscr_len, hrhs, hand⟩ := andMatch_gate_facts hgat htag
  have hcv_le := hlen.core_ok.cur_vars_le
  have hlml := hlen.core_ok.lit_mark_len
  have hrl := hlen.core_ok.repr_len
  have htl := hlen.core_ok.tmp_len_arr
  have hvl := hlen.core_ok.vals_len
  have hsl := hlen.scratch_ok.scratch_buf_len
  have hmaxv := c.hmaxv
  have hcv_u64 : s.core.cur_vars < 2 ^ 64 := by unfold dimacsBound at hmaxv; omega
  have h2cv_u64 : 2 * s.core.cur_vars < 2 ^ 64 := by unfold dimacsBound at hmaxv; omega
  have hlhs_u32 : lhs.toNat < 2 ^ 32 := lhs.isLt
  have hent1_lt : ent.toNat + 1 < g_len := by omega
  have hent1_idx : (BitVec.setWidth 64 ent + 1#64).toNat = ent.toNat + 1 := by bv_omega
  have hent1_scr : (BitVec.setWidth 64 ent + 1#64).toNat < s.scratch.scratch_buf.length := by
    omega
  have hmword_buf : s.scratch.scratch_buf[(BitVec.setWidth 64 ent + 1#64).toNat]'hent1_scr =
      mword := by
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem hent1_scr, hent1_idx, hscr_eq _ hent1_lt, hmword]
  dsimp only [Func.wp, full_cong_and_match_body]
  c0_hstraight!
  c0_hsplit
  · clear hc; c0_hstraight!
    exact hQ false s.core.repr s.core.lit_mark m0 hrl hlml hlm_clr hrepr (by simp) hm0
  have hua2 := hc; clear hc; c0_hstraight!
  c0_hsplit
  · clear hc; c0_hstraight!
    exact hQ false s.core.repr s.core.lit_mark m0 hrl hlml hlm_clr hrepr (by simp) hm0
  have hua1m := hc; clear hc; c0_hstraight!
  c0_hsplit
  · clear hc; c0_hstraight!
    exact hQ false s.core.repr s.core.lit_mark m0 hrl hlml hlm_clr hrepr (by simp) hm0
  clear hc
  have hua_ge2 : 2 ≤ ua.toNat := by bv_omega
  have hua_le_max : ua.toNat ≤ congAndArityMax := by unfold congAndArityMax; bv_omega
  c0_hstraight!
  refine wp_join_group
    (fun xs ml => xs.fst.toNat = congGateArity mword ∧ xs.snd = () ∧ ml = m0) ?_ ?_
  · rintro _ ⟨arity_bv, ⟨⟩⟩ ml_j ⟨har_eq, _, hm_eq⟩
    subst ml_j
    dsimp only [Blocks.get, Member.here] at har_eq ⊢
    c0_hstraight!
    c0_hsplit
    · exfalso; bv_omega
    clear hc; c0_hstraight!
    c0_hsplit
    · exfalso; unfold congAndArityMax at hmaxA; bv_omega
    clear hc; c0_hstraight!
    c0_hsplit
    · exfalso; rw [Nat.mod_eq_of_lt hcv_u64] at hc; bv_omega
    clear hc; c0_hstraight!
    refine wp_loop_group
      (fun n xs ml => n = ua.toNat - xs.snd.fst.toNat ∧ xs.snd.fst.toNat ≤ ua.toNat ∧
        xs.fst.toNat ≤ xs.snd.fst.toNat ∧ ∃ lm1 : List (BitVec 8),
        lm1.length = 2 * c.max_vars ∧
        (∀ x, x < 2 * c.max_vars → lm1[x]?.getD 0#8 = 0#8 ∨ lm1[x]?.getD 0#8 = 1#8) ∧
        (∀ x, lm1[x]?.getD 0#8 ≠ 0#8 →
          ∃ k, k < xs.snd.fst.toNat ∧ (s.core.tmp[k]?.getD 0#32).toNat = x ∧
            x < 2 * s.core.cur_vars) ∧
        (∀ k, k < xs.snd.fst.toNat → (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
          lm1[(s.core.tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8) ∧
        lmCount lm1 (2 * s.core.cur_vars) 1#8 = xs.fst.toNat ∧
        (FullMem c { s with core := { s.core with lit_mark := lm1 } } ⋆ R) ml) ?_ ?_
    · rintro L n ⟨marked, i, ⟨⟩⟩ ml hL ⟨rfl, hi_le, hmr_le, lm1, hlml1, hdom1, hnz1,
        htmp1, hcnt1, hml⟩
      dsimp only [Blocks.get, Member.here]
      dsimp only at hi_le hmr_le hnz1 htmp1 hcnt1
      c0_hstraight!
      c0_hsplit
      · have hi_lt := hc; clear hc
        have hi_nat : i.toNat < ua.toNat := by bv_omega
        have hi_tmp : i.toNat < s.core.tmp.length := by omega
        have hi_tl : (BitVec.setWidth 64 i).toNat < s.core.tmp.length := by bv_omega
        c0_hstraight!
        c0_hsplit
        · have hoob := hc; clear hc
          rw [Nat.mod_eq_of_lt hcv_u64, Nat.mod_eq_of_lt h2cv_u64] at hoob
          have hoob_ge : 2 * s.core.cur_vars ≤ (s.core.tmp[i.toNat]'hi_tmp).toNat := by bv_omega
          refine wp_loop_group
            (fun nc xsc mc => nc = i.toNat - xsc.fst.toNat ∧ xsc.fst.toNat ≤ i.toNat ∧
              ∃ lmc : List (BitVec 8), lmc.length = 2 * c.max_vars ∧
              (∀ y, lmc[y]?.getD 0#8 ≠ 0#8 → ∃ p, xsc.fst.toNat ≤ p ∧ p < i.toNat ∧
                (s.core.tmp[p]?.getD 0#32).toNat = y ∧ y < 2 * s.core.cur_vars) ∧
              (∀ p, xsc.fst.toNat ≤ p → p < i.toNat →
                (s.core.tmp[p]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
              (FullMem c { s with core := { s.core with lit_mark := lmc } } ⋆ R) mc) ?_ ?_
          · rintro Lc nc ⟨jc, ⟨⟩⟩ mc hLc ⟨rfl, hjc_le, lmc, hlmlc, hnzc, hltc, hmc⟩
            dsimp only [Blocks.get, Member.here]
            dsimp only at hjc_le hnzc hltc
            c0_hstraight!
            c0_hsplit
            · have hjc_lt := hc; clear hc
              have hjc_nat : jc.toNat < i.toNat := by bv_omega
              have hjc_tmp : jc.toNat < s.core.tmp.length := by omega
              have hjc_tl : (BitVec.setWidth 64 jc).toNat < s.core.tmp.length := by bv_omega
              have hval_lt : (s.core.tmp[jc.toNat]'hjc_tmp).toNat < 2 * s.core.cur_vars := by
                have h := hltc jc.toNat (Nat.le_refl _) hjc_nat
                rwa [List.getElem?_eq_getElem hjc_tmp, Option.getD_some] at h
              have hjc_lm : (BitVec.setWidth 64 (s.core.tmp[jc.toNat]'hjc_tmp)).toNat <
                  lmc.length := by bv_omega
              c0_hstraight!
              have hnz_step : ∀ x,
                  (lmc.set (s.core.tmp[jc.toNat]?.getD 0#32).toNat 0#8)[x]?.getD 0#8 ≠ 0#8 →
                    ∃ p, (jc + 1#32).toNat ≤ p ∧ p < i.toNat ∧
                      (s.core.tmp[p]?.getD 0#32).toNat = x ∧
                      x < 2 * s.core.cur_vars := fun x hx => by
                obtain ⟨p, hp1, hp2, hpx, _⟩ := clear_lit_marks_nz_step hjc_nat
                  (by rw [List.getElem?_eq_getElem hjc_tmp, Option.getD_some]; omega)
                  (fun y hy => by
                    obtain ⟨q, hq1, hq2, hqy, hyl⟩ := hnzc y hy
                    exact ⟨q, hq1, hq2, hqy, by omega⟩) hx
                have hpx_lt := hltc p (by omega) hp2
                rw [hpx] at hpx_lt
                exact ⟨p, by bv_omega, hp2, hpx, hpx_lt⟩
              have hmc' := andMatch_mem_set_lm (idx1 := (BitVec.setWidth 64
                (s.core.tmp[jc.toNat]'hjc_tmp)).toNat)
                (idx2 := (s.core.tmp[jc.toNat]?.getD 0#32).toNat) (v := 0#8)
                (by rw [List.getElem?_eq_getElem hjc_tmp, Option.getD_some]; bv_omega)
                (by assumption)
              exact hLc (i.toNat - (jc + 1#32).toNat) (jc + 1#32, ()) _ (by bv_omega)
                ⟨rfl, by bv_omega, lmc.set (s.core.tmp[jc.toNat]?.getD 0#32).toNat 0#8,
                  by simp [hlmlc], hnz_step, fun p hp1 hp2 => hltc p (by bv_omega) hp2, hmc'⟩
            · have hjc_not := hc; clear hc; c0_hstraight!
              have hjc_eq : jc.toNat = i.toNat := by bv_omega
              have hclr_lm : FullLitMarksClear c
                  { s with core := { s.core with lit_mark := lmc } } :=
                fullLitMarksClear_of_clear (upper := i.toNat) hlm_clr.1 (fun y hy => by
                  obtain ⟨p, hp1, hp2, hpy, hyl⟩ := hnzc y hy
                  exact ⟨p, by omega, by omega, hpy, by omega⟩)
              exact hQ false s.core.repr lmc mc hrl hlmlc hclr_lm hrepr
                (fun h => Bool.noConfusion h) hmc
          · intro Jc hJc
            exact hJc i.toNat (0#32, ()) ml ⟨rfl, Nat.zero_le _, lm1, hlml1, fun y hy => by
              obtain ⟨p, hp, hpy, hyl⟩ := hnz1 y hy; exact ⟨p, Nat.zero_le _, hp, hpy, hyl⟩,
              fun p _ hp => (htmp1 p hp).1, hml⟩
        · have hoob := hc; clear hc
          rw [Nat.mod_eq_of_lt hcv_u64, Nat.mod_eq_of_lt h2cv_u64] at hoob
          have hl_lt : (s.core.tmp[i.toNat]'hi_tmp).toNat < 2 * s.core.cur_vars := by bv_omega
          have hl_lm : (BitVec.setWidth 64 (s.core.tmp[i.toNat]'hi_tmp)).toNat < lm1.length := by
            bv_omega
          c0_hstraight!
          refine wp_join_group
            (fun xs ml' => xs.snd = () ∧ xs.fst.toNat ≤ i.toNat + 1 ∧
              ∃ lm1' : List (BitVec 8), lm1'.length = 2 * c.max_vars ∧
              (∀ x, x < 2 * c.max_vars → lm1'[x]?.getD 0#8 = 0#8 ∨ lm1'[x]?.getD 0#8 = 1#8) ∧
              (∀ x, lm1'[x]?.getD 0#8 ≠ 0#8 →
                ∃ k, k < i.toNat + 1 ∧ (s.core.tmp[k]?.getD 0#32).toNat = x ∧
                  x < 2 * s.core.cur_vars) ∧
              (∀ k, k < i.toNat + 1 → (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
                lm1'[(s.core.tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8) ∧
              lmCount lm1' (2 * s.core.cur_vars) 1#8 = xs.fst.toNat ∧
              (FullMem c { s with core := { s.core with lit_mark := lm1' } } ⋆ R) ml') ?_ ?_
          · rintro _ ⟨marked', ⟨⟩⟩ ml' ⟨_, hmr', lm1', hlml1', hdom1', hnz1', htmp1', hcnt1', hml'⟩
            dsimp only [Blocks.get, Member.here]
            dsimp only at hmr' hcnt1'
            c0_hstraight!
            have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
            rw [← hi1] at hmr' hnz1' htmp1'
            exact hL (ua.toNat - (i + 1#32).toNat) (marked', i + 1#32, ()) ml' (by bv_omega)
              ⟨rfl, by bv_omega, hmr', lm1', hlml1', hdom1', hnz1', htmp1', hcnt1', hml'⟩
          · intro J1 hJ1
            c0_hsplit
            · have h_eq0 := hc; clear hc
              have hl0 : lm1[(s.core.tmp[i.toNat]'hi_tmp).toNat]?.getD 0#8 = 0#8 := by
                have hzx : BitVec.setWidth 32 (lm1[(BitVec.setWidth 64
                    (s.core.tmp[i.toNat]'hi_tmp)).toNat]'hl_lm) =
                    BitVec.setWidth 32 (BitVec.truncate 8 0#32) := h_eq0
                rw [bv8_zext32_eq] at hzx
                have hidx : (BitVec.setWidth 64 (s.core.tmp[i.toNat]'hi_tmp)).toNat =
                    (s.core.tmp[i.toNat]'hi_tmp).toNat := by bv_omega
                exact (congrArg (fun k => lm1[k]?.getD 0#8) hidx.symm).trans
                  (by rw [List.getElem?_eq_getElem hl_lm, Option.getD_some, hzx]; rfl)
              c0_hstraight!
              have hinv1 := andMatch_loop1_mark_inv hlml1 hcv_le (by omega) hl_lt
                (by rw [List.getElem?_eq_getElem hi_tmp, Option.getD_some])
                hl0 hcnt1 hdom1 hnz1 htmp1
              have hml_s := andMatch_mem_set_lm (lm := lm1) (idx1 := (BitVec.setWidth 64
                (s.core.tmp[i.toNat]'hi_tmp)).toNat)
                (idx2 := (s.core.tmp[i.toNat]'hi_tmp).toNat) (v := 1#8)
                (by bv_omega) (by assumption)
              refine hJ1 (marked + 1#32, ()) _ ⟨rfl, by bv_omega,
                lm1.set (s.core.tmp[i.toNat]'hi_tmp).toNat 1#8, by simp [hlml1],
                hinv1.1, hinv1.2.1, hinv1.2.2.1, ?_, hml_s⟩
              rw [hinv1.2.2.2]; bv_omega
            · have h_eq0 := hc; clear hc; c0_hstraight!
              have hne0 := lm_ne0_of_zext_ne (show (s.core.tmp[i.toNat]'hi_tmp).toNat <
                lm1.length by omega) h_eq0
              have h1v : lm1[(s.core.tmp[i.toNat]'hi_tmp).toNat]?.getD 0#8 = 1#8 := by
                rcases hdom1 _ (show (s.core.tmp[i.toNat]'hi_tmp).toNat < 2 * c.max_vars by omega)
                  with h0 | h1v
                · exact absurd h0 hne0
                · exact h1v
              refine hJ1 (marked, ()) ml ⟨rfl, by bv_omega, lm1, hlml1, hdom1,
                fun x hx => by obtain ⟨k, hk, hkx⟩ := hnz1 x hx; exact ⟨k, by omega, hkx⟩,
                fun k hk => by
                  by_cases hki : k = i.toNat
                  · subst hki; rw [List.getElem?_eq_getElem hi_tmp, Option.getD_some]
                    exact ⟨hl_lt, h1v⟩
                  · exact htmp1 k (by omega),
                hcnt1, hml⟩
      · have hi_not := hc; clear hc; have hi_eq : i.toNat = ua.toNat := by bv_omega
        rw [hi_eq] at hnz1 htmp1
        refine wp_loop_break_group (andMatchLoop2Post c F_cur s scr0 ent ua marked mword R)
          (fun n xs mc => n = congGateArity mword - xs.snd.fst.toNat ∧
            xs.snd.fst.toNat ≤ congGateArity mword ∧
            andMatchLoop2Inv c F_cur s scr0 ent ua marked mword R
              xs.fst.toNat xs.snd.fst.toNat mc) ?_ ?_ ?_
        · rintro _ ⟨ok, cnt, _, ⟨⟩⟩ mc ⟨repr2, lm2, hrl2, hlml2, hrepr2, hnz2, hpok, hmc⟩
          dsimp only [Blocks.get, Member.here]; c0_hstraight!
          refine wp_loop_group
            (fun nc xsc mcc => nc = ua.toNat - xsc.fst.toNat ∧ xsc.fst.toNat ≤ ua.toNat ∧
              ∃ lmc : List (BitVec 8), lmc.length = 2 * c.max_vars ∧
              (∀ y, lmc[y]?.getD 0#8 ≠ 0#8 → ∃ p, xsc.fst.toNat ≤ p ∧ p < ua.toNat ∧
                (s.core.tmp[p]?.getD 0#32).toNat = y ∧ y < 2 * c.max_vars) ∧
              (FullMem c { s with core := { s.core with lit_mark := lmc, repr := repr2 } } ⋆ R) mcc)
            ?_ ?_
          · rintro Lc nc ⟨jc, ⟨⟩⟩ mcc hLc ⟨rfl, hjc_le, lmc, hlmlc, hnzc, hmcc⟩
            dsimp only [Blocks.get, Member.here]; dsimp only at hjc_le hnzc; c0_hstraight!
            c0_hsplit
            · have hjc_lt := hc; clear hc
              have hjc_nat : jc.toNat < ua.toNat := by bv_omega
              have hjc_tmp : jc.toNat < s.core.tmp.length := by omega
              have hjc_tl : (BitVec.setWidth 64 jc).toNat < s.core.tmp.length := by bv_omega
              have hval_lt : (s.core.tmp[jc.toNat]'hjc_tmp).toNat < 2 * s.core.cur_vars := by
                have h := (htmp1 jc.toNat hjc_nat).1
                rwa [List.getElem?_eq_getElem hjc_tmp, Option.getD_some] at h
              have hjc_lm : (BitVec.setWidth 64 (s.core.tmp[jc.toNat]'hjc_tmp)).toNat <
                  lmc.length := by bv_omega
              c0_hstraight!
              have hnz_step : ∀ x,
                  (lmc.set (s.core.tmp[jc.toNat]?.getD 0#32).toNat 0#8)[x]?.getD 0#8 ≠ 0#8 →
                    ∃ p, (jc + 1#32).toNat ≤ p ∧ p < ua.toNat ∧
                      (s.core.tmp[p]?.getD 0#32).toNat = x ∧
                      x < 2 * c.max_vars := fun x hx => by
                obtain ⟨p, hp1, hp2, hpx, _⟩ := clear_lit_marks_nz_step hjc_nat
                  (by rw [List.getElem?_eq_getElem hjc_tmp, Option.getD_some]; omega)
                  (fun y hy => by
                    obtain ⟨p, hp1, hp2, hpy, _⟩ := hnzc y hy; exact ⟨p, hp1, hp2, hpy, by omega⟩)
                  hx
                exact ⟨p, by bv_omega, hp2, hpx, hpx ▸ by have := (htmp1 p hp2).1; omega⟩
              have hmcc' := andMatch_mem_set_lm (lm := lmc) (repr := repr2)
                (idx1 := (BitVec.setWidth 64 (s.core.tmp[jc.toNat]'hjc_tmp)).toNat)
                (idx2 := (s.core.tmp[jc.toNat]?.getD 0#32).toNat) (v := 0#8)
                (by rw [List.getElem?_eq_getElem hjc_tmp, Option.getD_some]; bv_omega)
                (by assumption)
              exact hLc (ua.toNat - (jc + 1#32).toNat) (jc + 1#32, ()) _ (by bv_omega)
                ⟨rfl, by bv_omega, lmc.set (s.core.tmp[jc.toNat]?.getD 0#32).toNat 0#8,
                  by simp [hlmlc], hnz_step, hmcc'⟩
            · have hjc_not := hc; clear hc
              have hjc_eq : jc.toNat = ua.toNat := by bv_omega
              have hclr := fullLitMarksClear_of_clear (repr := repr2) (upper := ua.toNat)
                hlm_clr.1 (fun y hy => by
                  obtain ⟨p, hp1, hp2, hpy, hyl⟩ := hnzc y hy
                  exact ⟨p, by omega, by omega, hpy, hyl⟩)
              refine wp_join_group
                (fun xs mr => mr = mcc ∧ (xs.fst = true → ok = true ∧ cnt = marked)) ?_ ?_
              · rintro _ ⟨res, ⟨⟩⟩ mr ⟨rfl, hres⟩
                c0_hstraight!
                by_cases hrb : res = true
                · subst hrb; obtain ⟨rfl, rfl⟩ := hres rfl
                  obtain ⟨hcnt_m, hclosed, h2_rev, htmp_ok⟩ := hpok rfl
                  refine hQ true repr2 lmc mr hrl2 hlmlc hclr hrepr2 ?_ hmcc
                  intro _
                  exact ⟨hua_ge2, hua_le_max, andMatch_sound_wrap hlhs hcnt_m rfl
                    hand hscr_len hclosed h2_rev htmp_ok hlhs_u32⟩
                · have hrf : res = false := Bool.eq_false_iff.mpr hrb
                  subst hrf
                  exact hQ false repr2 lmc mr hrl2 hlmlc hclr hrepr2
                    (fun h => Bool.noConfusion h) hmcc
              · intro Js hJs
                c0_hstraight!; c0_hsplit
                · have hok_b := hc; clear hc; c0_hstraight!; c0_hsplit
                  · have hcnt_eq := hc; clear hc; c0_hstraight!
                    exact hJs (true, ()) mcc ⟨rfl, fun _ => ⟨hok_b, hcnt_eq⟩⟩
                  · clear hc; c0_hstraight!
                    exact hJs (false, ()) mcc ⟨rfl, fun h => Bool.noConfusion h⟩
                · clear hc; c0_hstraight!
                  exact hJs (false, ()) mcc ⟨rfl, fun h => Bool.noConfusion h⟩
          · intro Jc hJc
            exact hJc ua.toNat (0#32, ()) mc ⟨rfl, Nat.zero_le _, lm2, hlml2, fun y hy => by
              obtain ⟨p, hp, hpy⟩ := hnz2 y hy
              exact ⟨p, Nat.zero_le _, hp, hpy, by have := (htmp1 p hp).1; omega⟩, hmc⟩
        · rintro B L2 n ⟨cnt, j, ⟨⟩⟩ mc hB hL2 ⟨rfl, hj_le, hcnt_le, repr2, lm2, hrl2, hlml2,
            hrepr2, hmrk2, hdom2, hnz2, htmp2, hclosed2, h2_rev2, hmc⟩
          dsimp only [Blocks.get, Member.here]
          dsimp only at hj_le hcnt_le hmrk2 hclosed2
          c0_hstraight!
          c0_hsplit
          · have hj_lt := hc; clear hc
            have hj_nat : j.toNat < congGateArity mword := by bv_omega
            have hgl_lt : ent.toNat + 2 + j.toNat < g_len := by omega
            have hgl_idx : (BitVec.setWidth 64 ent + 2#64 + BitVec.setWidth 64 j).toNat =
                ent.toNat + 2 + j.toNat := by bv_omega
            have hgl_buf_lt : (BitVec.setWidth 64 ent + 2#64 + BitVec.setWidth 64 j).toNat <
                s.scratch.scratch_buf.length := by omega
            obtain ⟨gl, hgl_eq, hgl_cv⟩ := hrhs j.toNat hj_nat
            have hgl_buf : s.scratch.scratch_buf[(BitVec.setWidth 64 ent + 2#64 +
                BitVec.setWidth 64 j).toNat]'hgl_buf_lt = gl := by
              apply Option.some.inj
              rw [← List.getElem?_eq_getElem hgl_buf_lt, hgl_idx, hscr_eq _ hgl_lt, hgl_eq]
            c0_hstraight!
            have hm_focus := ArrayField.repr.focus hmc
            c0_hcall hFind
            · exact ⟨F_cur, 2 * s.core.cur_vars, repr2, _, hrepr2,
                by change (s.scratch.scratch_buf[(BitVec.setWidth 64 ent + 2#64 +
                     BitVec.setWidth 64 j).toNat]'hgl_buf_lt).toNat < 2 * s.core.cur_vars
                   rw [hgl_buf]; exact hgl_cv,
                hm_focus, fun r repr3 m3 hrl3 hrepr3 hr_le hr_lt heq_gl hm3 => by
                  change LitEquiv (cnfOfClauses F_cur)
                    (s.scratch.scratch_buf[(BitVec.setWidth 64 ent + 2#64 +
                      BitVec.setWidth 64 j).toNat]'hgl_buf_lt).toNat r.toNat at heq_gl
                  rw [hgl_buf] at heq_gl
                  have hmc3 := ArrayField.repr.unfocus hm3
                  have hr_vl : r.toNat < s.core.vals.length := by bv_omega
                  c0_hstraight!
                  c0_hsplit
                  · clear hc; c0_hstraight!
                    exact hB (false, cnt, j, ()) m3 ⟨repr3, lm2, by omega, hlml2, hrepr3, hnz2,
                      fun h => Bool.noConfusion h, hmc3⟩
                  · have h_slt0 := hc; clear hc
                    change BitVec.slt (BitVec.signExtend 32 (s.core.vals[r.toNat]'hr_vl))
                      0#32 = false at h_slt0
                    refine wp_join_group
                      (fun xj mj => xj.fst = true ∧ xj.snd.snd = () ∧
                        andMatchLoop2Inv c F_cur s scr0 ent ua marked mword R
                          xj.snd.fst.toNat (j.toNat + 1) mj) ?_ ?_
                    · rintro _ ⟨_, cnt', ⟨⟩⟩ mj ⟨rfl, _, hinvj⟩
                      dsimp only [Blocks.get, Member.here]; c0_hstraight!
                      have hj1_nat : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
                      exact hL2 (congGateArity mword - (j + 1#32).toNat)
                        (cnt', j + 1#32, ()) mj (by bv_omega) ⟨rfl, by bv_omega, hj1_nat ▸ hinvj⟩
                    · intro J2 hJ2
                      c0_hsplit
                      · clear hc
                        have hr_lm : (BitVec.setWidth 64 r).toNat < lm2.length := by bv_omega
                        c0_hstraight!
                        c0_hsplit
                        · clear hc; c0_hstraight!
                          exact hB (false, cnt, j, ()) m3 ⟨repr3, lm2, by omega, hlml2,
                            hrepr3, hnz2, fun h => Bool.noConfusion h, hmc3⟩
                        · have hm_eq0 := hc; clear hc
                          have hr_lm2 : r.toNat < lm2.length := by bv_omega
                          change BitVec.setWidth 32 (lm2[r.toNat]'hr_lm2) ≠
                            BitVec.ofNat 32 0 at hm_eq0
                          have hm_ne0 := lm_ne0_of_zext_ne hr_lm2 hm_eq0
                          obtain ⟨kr, hkr_ua, hkr_eq⟩ := hnz2 r.toNat hm_ne0
                          have hclosed_j := andMatch_closed_step hgl_eq heq_gl hclosed2
                            kr hkr_ua hkr_eq
                          refine wp_join_group
                            (fun xk mk => xk.snd = () ∧
                              andMatchLoop2Inv c F_cur s scr0 ent ua marked mword R
                                xk.fst.toNat (j.toNat + 1) mk) ?_ ?_
                          · rintro _ ⟨cnt', ⟨⟩⟩ mk ⟨_, hinvk⟩
                            dsimp only [Blocks.get, Member.here]; c0_hstraight!
                            exact hJ2 (true, cnt', ()) mk ⟨rfl, rfl, hinvk⟩
                          · intro J3 hJ3
                            c0_hsplit
                            · have hm_eq1 := hc; clear hc
                              have hrlm1 : lm2[r.toNat]?.getD 0#8 = 1#8 := by
                                have hzx : BitVec.setWidth 32
                                    (lm2[(BitVec.setWidth 64 r).toNat]'hr_lm) =
                                    BitVec.setWidth 32 (BitVec.truncate 8 1#32) := hm_eq1
                                rw [bv8_zext32_eq] at hzx
                                have hidx : (BitVec.setWidth 64 r).toNat = r.toNat := by bv_omega
                                exact (congrArg (fun k => lm2[k]?.getD 0#8) hidx.symm).trans
                                  (by rw [List.getElem?_eq_getElem hr_lm, Option.getD_some, hzx]
                                      rfl)
                              c0_hstraight!
                              have heq_gl' : LitEquiv (cnfOfClauses F_cur)
                                  (scr0[ent.toNat + 2 + j.toNat]?.getD 0#32).toNat r.toNat := by
                                rw [hgl_eq, Option.getD_some]; exact heq_gl
                              have hinv2 := andMatch_loop2_mark_inv hlml2 hcv_le hj_nat hr_lt rfl
                                heq_gl' hrlm1 hmrk2 hkr_ua hkr_eq hdom2 hnz2
                                (fun k hk => (htmp2 k hk).2) h2_rev2
                              have hm_s := andMatch_mem_set_lm (lm := lm2) (repr := repr3)
                                (idx1 := (BitVec.setWidth 64 r).toNat) (idx2 := r.toNat) (v := 2#8)
                                (by bv_omega) (by assumption)
                              refine hJ3 (cnt + 1#32, ()) _
                                ⟨rfl, by have := hinv2.1; bv_omega, repr3,
                                  lm2.set r.toNat 2#8, by omega, by simp [hlml2], hrepr3,
                                  by have := hinv2.2.2.2.1; rw [← this]; bv_omega,
                                  hinv2.2.1, hinv2.2.2.1,
                                  fun k hk => ⟨(htmp2 k hk).1, hinv2.2.2.2.2.1 k hk⟩,
                                  hclosed_j, hinv2.2.2.2.2.2, hm_s⟩
                            · clear hc; c0_hstraight!
                              exact hJ3 (cnt, ()) m3 ⟨rfl, hcnt_le, repr3, lm2, by omega, hlml2,
                                hrepr3, hmrk2, hdom2, hnz2, htmp2, hclosed_j, h2_rev2, hmc3⟩
                      · have hv_eq0 := hc; clear hc; c0_hstraight!
                        have hclosed_j := andMatch_closed_true_step hwit hclv0 hr_lt hr_vl
                          (hwit.vals_domain r.toNat hr_lt) (fun heq => hv_eq0 heq) h_slt0
                          hgl_eq heq_gl hclosed2
                        exact hJ2 (true, cnt, ()) m3 ⟨rfl, rfl, hcnt_le, repr3, lm2, by omega,
                          hlml2, hrepr3, hmrk2, hdom2, hnz2, htmp2, hclosed_j, h2_rev2, hmc3⟩
              ⟩
          · c0_hstraight!
            have hj_eq : j.toNat = congGateArity mword := by bv_omega
            rw [hj_eq] at hclosed2
            exact hB (true, cnt, j, ()) mc ⟨repr2, lm2, hrl2, hlml2, hrepr2, hnz2,
              fun _ => ⟨hmrk2, hclosed2, h2_rev2, htmp2⟩, hmc⟩
        · intro B L2 hB hL2; c0_hstraight!
          refine hL2 (congGateArity mword) (0#32, 0#32, ()) ml ⟨rfl, Nat.zero_le _,
            by dsimp only; exact Nat.zero_le _, s.core.repr, lm1, hrl, hlml1, hrepr,
            by dsimp only; rw [hcnt1]; bv_omega,
            fun x hx => by
              rcases hdom1 x hx with h0 | h1; exact Or.inl h0; exact Or.inr (Or.inl h1),
            fun x hx => by obtain ⟨k, hk, hkx, _⟩ := hnz1 x hx; exact ⟨k, hk, hkx⟩,
            fun k hk => ⟨(htmp1 k hk).1, Or.inl (htmp1 k hk).2⟩,
            fun _ hidx => absurd hidx (Nat.not_lt_zero _), fun x hx h2 => by
              exfalso; rcases hdom1 x (by omega) with h0 | h1 <;>
                (first | rw [h0] at h2 | rw [h1] at h2) <;> exact absurd h2 (by decide), hml⟩
    · intro J hJ; c0_hstraight!
      refine hJ ua.toNat (0#32, 0#32, ()) m0 ⟨rfl, Nat.zero_le _, Nat.zero_le _, s.core.lit_mark,
        hlml, fun x hx => Or.inl (hlm_clr.2 x hx), fun x hx => absurd (hlm_clr.2 x (by
          by_cases hlt : x < 2 * c.max_vars
          · exact hlt
          · exfalso; rw [List.getElem?_eq_none (by omega), Option.getD_none] at hx; exact hx rfl))
          hx, fun k hk => absurd hk (Nat.not_lt_zero _), ?_, hm0⟩
      change List.countP (fun i => s.core.lit_mark[i]?.getD 0#8 == 1#8)
        (List.range (2 * s.core.cur_vars)) = 0
      rw [List.countP_eq_zero]
      intro x hx; rw [List.mem_range] at hx; rw [hlm_clr.2 x (by omega)]; decide
  · intro J hJ; c0_hstraight!
    have hm_idx' : s.scratch.scratch_buf[(ent.toNat +
        BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by bv_omega) = mword := by
      apply Option.some.inj
      rw [← List.getElem?_eq_getElem (by bv_omega),
        show (ent.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = ent.toNat + 1 by bv_omega,
        hscr_eq _ hent1_lt, hmword]
    c0_hsplit
    · have htag3 := hc; clear hc; rw [hm_idx'] at htag3; c0_hstraight!
      change J (s.scratch.scratch_buf[(BitVec.setWidth 64 ent + 1#64).toNat] &&&
        268435455#32, ()) m0; rw [hmword_buf]
      exact hJ (mword &&& 268435455#32, ()) m0 ⟨(congGateArity_of_eq3 htag3).symm, rfl, rfl⟩
    · have htag3 := hc; clear hc; rw [hm_idx'] at htag3; c0_hstraight!
      change J (s.scratch.scratch_buf[(BitVec.setWidth 64 ent + 1#64).toNat] &&&
        255#32, ()) m0; rw [hmword_buf]
      exact hJ (mword &&& 255#32, ()) m0 ⟨(congGateArity_of_ne3 htag3).symm, rfl, rfl⟩


end

end LeanQbe.T.Examples.Kissat.Proof.Congruence
