/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityCongProof0
public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof2a
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat 4.0.4 Congruence Parity Proofs — Part 1a (`GAP-CONG-01..02` Extraction Helpers)

Proves parametric `(Γ : Env)` `Func.wp` contracts for the 5 XOR / clause-lookup congruence helpers
in `FullFidelityCong.lean`:
1. `full_cong_emit_xor` (`full_cong_emit_xor_wp`, `fidCongEmitXorSpec`)
2. `full_cong_emit_xor4` (`full_cong_emit_xor4_wp`, `fidCongEmitXor4Spec`)
3. `full_cong_has_clause_k` (`full_cong_has_clause_k_wp`, `m6CongHasClauseKSpec`)
4. `full_cong_extract_xor_k` (`full_cong_extract_xor_k_wp`, `fidCongExtractXorKSpec`)
5. `full_cong_try_xor_ite` (`full_cong_try_xor_ite_wp`, `fidCongTryXorIteSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityCong

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open scoped LeanQbe.T.Examples.Kissat.FullM3CongBva.M3HeadTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6CongSubst.M6HeadTactics
open scoped FullArenaTactics Full.FullCongTactics
open Kraken.Bedrock2.Test

/-! ## 1. Local Helpers (`Proof1a`) -/

section Helpers

private theorem fullWitnessInv_with_tmp_lm {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (tmp' : List (BitVec 32)) (lm' : List (BitVec 8)) :
    FullWitnessInv c F0 F_cur { k with tmp := tmp', lit_mark := lm' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

private theorem bv32_even_or_bit_toNat (y b : BitVec 32) :
    ((y &&& ~~~1#32) ||| (b &&& 1#32)).toNat = 2 * (y.toNat / 2) + b.toNat % 2 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [BitVec.toNat_or, Nat.testBit_or, m6_bv32_and_not1_toNat, BitVec.toNat_and, Nat.testBit_and]
  cases i with
  | zero =>
    have h1 : (1#32 : BitVec 32).toNat.testBit 0 = true := by decide
    rw [h1, Bool.and_true, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one b.toNat with hb | hb <;> simp [hb] <;> omega
  | succ k =>
    have h0 : (1#32 : BitVec 32).toNat.testBit (k + 1) = false := by
      rw [show (1#32 : BitVec 32).toNat = 1 from rfl]
      exact m6_testBit_false_of_lt (Nat.lt_of_lt_of_le (by omega)
        (Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ k + 1)))
    rw [h0, Bool.and_false, Bool.or_false, Nat.testBit_succ, Nat.testBit_succ]
    congr 1; omega

private theorem litNeg_div2 (n : Nat) : litNeg n / 2 = n / 2 := litVar_litNeg n

private theorem litSign_of_mod2 (n : Nat) : litSign n = decide (n % 2 = 1) := by
  unfold litSign; rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

private theorem xor_emit_sound {f : CNF Nat} {cur_vars : Nat} {x0 x1 x2 : BitVec 32}
    (hx0 : x0.toNat < 2 * cur_vars) (hx1 : x1.toNat < 2 * cur_vars)
    (hx2 : x2.toNat < 2 * cur_vars)
    (hxor : XorGateDef f (litNeg x0.toNat) x1.toNat x2.toNat) :
    let lhs := ((x0 ^^^ 1#32) &&& ~~~1#32) ||| ((((x0 ^^^ 1#32) ^^^ x1) ^^^ x2) &&& 1#32)
    let r0 := x1 &&& ~~~1#32; let r1 := x2 &&& ~~~1#32
    lhs.toNat < 2 * cur_vars ∧ r0.toNat < 2 * cur_vars ∧ r1.toNat < 2 * cur_vars ∧
    XorListGateDef f lhs.toNat [r0.toNat, r1.toNat] ∧
    XorListGateDef f lhs.toNat [r1.toNat, r0.toNat] := by
  intro lhs r0 r1
  have hlhs_n : lhs.toNat =
      2 * ((x0 ^^^ 1#32).toNat / 2) + (((x0 ^^^ 1#32) ^^^ x1) ^^^ x2).toNat % 2 :=
    bv32_even_or_bit_toNat (x0 ^^^ 1#32) (((x0 ^^^ 1#32) ^^^ x1) ^^^ x2)
  have hr0_n : r0.toNat = 2 * (x1.toNat / 2) := m6_bv32_and_not1_toNat x1
  have hr1_n : r1.toNat = 2 * (x2.toNat / 2) := m6_bv32_and_not1_toNat x2
  have hx0n_div : (x0 ^^^ 1#32).toNat / 2 = x0.toNat / 2 := by
    rw [FullCongHelpers.bv32_xor1_eq_litNeg, litNeg_div2]
  have heval_eq : ∀ α : Nat → Bool, f.Sat α →
      evalLitVal α lhs.toNat = (evalLitVal α r0.toNat != evalLitVal α r1.toNat) := by
    intro α hα
    have hv := xorGateDef_eval hα hxor
    have hx0_ev : evalLitVal α (litNeg x0.toNat) =
        (α (x0.toNat / 2) != litSign (litNeg x0.toNat)) := by
      simp [evalLitVal, litVar, litNeg_div2]
    have hx1_ev : evalLitVal α x1.toNat = (α (x1.toNat / 2) != litSign x1.toNat) := rfl
    have hx2_ev : evalLitVal α x2.toNat = (α (x2.toNat / 2) != litSign x2.toNat) := rfl
    have hr0_ev : evalLitVal α r0.toNat = α (x1.toNat / 2) := by
      simp [evalLitVal, litVar, litSign, hr0_n]
    have hr1_ev : evalLitVal α r1.toNat = α (x2.toNat / 2) := by
      simp [evalLitVal, litVar, litSign, hr1_n]
    have hvar_lhs : litVar lhs.toNat = x0.toNat / 2 := by
      simp only [litVar, hlhs_n, hx0n_div]; omega
    have hmod_xor : (((x0 ^^^ 1#32) ^^^ x1) ^^^ x2).toNat % 2 =
        (((litNeg x0.toNat) % 2 ^^^ x1.toNat % 2) ^^^ x2.toNat % 2) := by
      rw [BitVec.toNat_xor, BitVec.toNat_xor, FullCongHelpers.bv32_xor1_eq_litNeg]
      have h1 := Nat.xor_mod_two_pow (a := (litNeg x0.toNat) ^^^ x1.toNat) (b := x2.toNat) (n := 1)
      have h2 := Nat.xor_mod_two_pow (a := litNeg x0.toNat) (b := x1.toNat) (n := 1)
      simpa using h1.trans (by rw [h2])
    have hsign_lhs : litSign lhs.toNat =
        ((litSign (litNeg x0.toNat) != litSign x1.toNat) != litSign x2.toNat) := by
      rw [litSign_of_mod2, litSign_of_mod2, litSign_of_mod2, litSign_of_mod2, hlhs_n]
      have hlm : (2 * ((x0 ^^^ 1#32).toNat / 2) +
          (((x0 ^^^ 1#32) ^^^ x1) ^^^ x2).toNat % 2) % 2 =
          (((x0 ^^^ 1#32) ^^^ x1) ^^^ x2).toNat % 2 := by omega
      rw [hlm, hmod_xor]
      rcases Nat.mod_two_eq_zero_or_one (litNeg x0.toNat) with h0 | h0 <;>
        rcases Nat.mod_two_eq_zero_or_one x1.toNat with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one x2.toNat with h2 | h2 <;>
        simp [h0, h1, h2]
    rw [evalLitVal, hvar_lhs, hsign_lhs, hr0_ev, hr1_ev]
    rw [hx0_ev, hx1_ev, hx2_ev] at hv
    cases ha0 : α (x0.toNat / 2) <;> cases ha1 : α (x1.toNat / 2) <;>
      cases ha2 : α (x2.toNat / 2) <;> cases hs0 : litSign (litNeg x0.toNat) <;>
      cases hs1 : litSign x1.toNat <;> cases hs2 : litSign x2.toNat <;> simp_all
  refine ⟨by omega, by omega, by omega,
    (fun α hα => by rw [xorEvalList_pair]; exact heval_eq α hα),
    (fun α hα => by
      rw [xorEvalList_pair, heval_eq α hα]
      cases evalLitVal α r0.toNat <;> cases evalLitVal α r1.toNat <;> rfl)⟩

private theorem xorGateDef_of_four {f : CNF Nat} {a b c : Nat}
    (h1 : f.EntailsClause (cnfClause [a, b, c]))
    (h2 : f.EntailsClause (cnfClause [a, litNeg b, litNeg c]))
    (h3 : f.EntailsClause (cnfClause [litNeg a, b, litNeg c]))
    (h4 : f.EntailsClause (cnfClause [litNeg a, litNeg b, c])) :
    XorGateDef f (litNeg a) b c ∧ XorGateDef f (litNeg b) a c ∧ XorGateDef f (litNeg c) a b := by
  have h1' : XorGateDef f (litNeg a) b c :=
    ⟨entails_perm_clause (fun x hx => by
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
       rcases hx with rfl | rfl | rfl <;> simp) h4,
     entails_perm_clause (fun x hx => by
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
       rcases hx with rfl | rfl | rfl <;> simp) h3,
     by simpa [litNeg_litNeg] using h1,
     by simpa [litNeg_litNeg] using h2⟩
  refine ⟨h1', xorGateDef_of_eval_eq fun α hα => ?_, xorGateDef_of_eval_eq fun α hα => ?_⟩
  · have hv := xorGateDef_eval hα h1'; rw [evalLitVal_litNeg] at hv ⊢
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;> cases hc : evalLitVal α c <;>
      simp_all
  · have hv := xorGateDef_eval hα h1'; rw [evalLitVal_litNeg] at hv ⊢
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;> cases hc : evalLitVal α c <;>
      simp_all

private theorem xor_bit01_lt_div2 {cv : Nat} (x m : BitVec 32) (hx : x.toNat < 2 * cv) :
    (x ^^^ (m &&& 1#32)).toNat < 2 * cv ∧ (x ^^^ (m &&& 1#32)).toNat / 2 = x.toNat / 2 := by
  have hm_lt : (m &&& 1#32).toNat < 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
    exact Nat.mod_lt _ (by decide)
  rcases (by omega : (m &&& 1#32).toNat = 0 ∨ (m &&& 1#32).toNat = 1) with h0 | h1
  · have hb : (m &&& 1#32) = 0#32 := BitVec.eq_of_toNat_eq h0
    rw [hb]; simp [hx]
  · have hb : (m &&& 1#32) = 1#32 := BitVec.eq_of_toNat_eq h1
    rw [hb, FullCongHelpers.bv32_xor1_eq_litNeg]
    exact ⟨bv32_xor1_lt_even hx, litNeg_div2 _⟩

private theorem slice_pop_step_fid {F_cur : List (List Nat)} {k : FullCoreState} {a p rem : Nat}
    (hslice : if k.dense_mode = 0#64 then WatchSliceOk F_cur k a p rem
      else DenseWatchSliceOk F_cur k a p rem) (hpos : 0 < rem) :
    ∃ w0 : BitVec 32, k.wstk[p]? = some w0 ∧
      ((w0 &&& 0x80000000#32) ≠ 0#32 ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [a, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k a (p + 1) (rem - 1)
         else DenseWatchSliceOk F_cur k a (p + 1) (rem - 1)) ∨
       (w0 &&& 0x80000000#32) = 0#32 ∧ 2 ≤ rem ∧
        ∃ cr : BitVec 32, k.wstk[p + 1]? = some cr ∧ cr.toNat ∈ fullArenaClauseRefsCore k ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k a (p + 2) (rem - 2)
         else DenseWatchSliceOk F_cur k a (p + 2) (rem - 2))) := by
  by_cases hdm : k.dense_mode = 0#64 <;> simp only [hdm, ↓reduceIte] at hslice ⊢
  · cases hslice with
    | empty => omega
    | bin hp hf _ _ hent hrest => exact ⟨_, hp, Or.inl ⟨hf, hent, hrest⟩⟩
    | large hp hp1 hf _ href hrest => exact ⟨_, hp, Or.inr ⟨hf, by omega, _, hp1, href, hrest⟩⟩
  · cases hslice with
    | empty => omega
    | bin hp hf _ _ hent hrest => exact ⟨_, hp, Or.inl ⟨hf, hent, hrest⟩⟩
    | occ hp hp1 hf _ _ href hrest => exact ⟨_, hp, Or.inr ⟨hf, by omega, _, hp1, href, hrest⟩⟩

private theorem bin_subsumes_unass {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hcl0 : s.core.cur_level = 0)
    {a b : Nat} {unass : List Nat} (hb_lt : b < 2 * s.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [a, b]))
    (ha_in : a ∈ unass) (hb_cov : s.core.vals[b]?.getD 0#8 = 0xFF#8 ∨ b ∈ unass) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause unass) := by
  refine entails_of_eval_mem fun α hα => ?_
  have hs := (clauseEvalVal_iff α _).mpr ((CNF.entails_clause_def.mp hent) α hα)
  rw [clauseEvalVal] at hs
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hs
  rcases hs with ha_t | hb_t
  · exact ⟨a, ha_in, ha_t⟩
  · rcases hb_cov with hff | hb_in
    · exfalso
      obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff b hb_lt).mp hff
      have hlvl0 : (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
        have := hw.lvl_le i hi; omega
      have hunit := hw.level0_sound i hi hlvl0; rw [heq] at hunit
      have hsu := (CNF.entails_clause_def.mp hunit) α hα
      rw [← clauseEvalVal_iff, clauseEvalVal] at hsu
      simp only [List.any_cons, List.any_nil, Bool.or_false,
        show b ^^^ 1 = litNeg b from rfl, evalLitVal_litNeg, hb_t] at hsu
      cases hsu
    · exact ⟨b, hb_in, hb_t⟩

private theorem bv32_div2_eq_of_shr1_eq {x y : BitVec 32}
    (h : ((x >>> 1) == (y >>> 1)) = true) : x.toNat / 2 = y.toNat / 2 := by
  have ht := congrArg BitVec.toNat (beq_iff_eq.mp h)
  simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using ht

private theorem bv32_ne_of_div2_ne {x y : BitVec 32} (h : x.toNat / 2 ≠ y.toNat / 2) : x ≠ y :=
  fun heq => h (heq ▸ rfl)

private theorem div2_ne_of_xor1 {x y : BitVec 32} (h : x.toNat / 2 ≠ y.toNat / 2) :
    x.toNat / 2 ≠ (y ^^^ 1).toNat / 2 := by rw [bv32_xor1_litNeg, litNeg_div2]; exact h

private theorem div2_ne_of_xor1_l {x y : BitVec 32} (h : x.toNat / 2 ≠ y.toNat / 2) :
    (x ^^^ 1).toNat / 2 ≠ y.toNat / 2 := by rw [bv32_xor1_litNeg, litNeg_div2]; exact h

private theorem div2_ne_of_xor1_both {x y : BitVec 32} (h : x.toNat / 2 ≠ y.toNat / 2) :
    (x ^^^ 1).toNat / 2 ≠ (y ^^^ 1).toNat / 2 := by
  rw [bv32_xor1_litNeg, bv32_xor1_litNeg, litNeg_div2, litNeg_div2]; exact h

private theorem cur_vars_ge3_of_distinct {v0 v1 v2 n : Nat}
    (h0 : v0 < n) (h1 : v1 < n) (h2 : v2 < n)
    (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h12 : v1 ≠ v2) : 3 ≤ n := by
  have hle := nodup_lt_length_le (n := n) (xs := [v0, v1, v2])
    (by simp [h01, h02, h12])
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption)
  simpa using hle

private theorem bool_xor4_from_norm :
    ∀ a0 a1 a2 a3 s0 s1 s2 s3 : Bool,
      (a0 != ((((true != s0) != s1) != s2) != s3)) = (a1 != (a2 != a3)) →
      ((!(a0 != s0)) = ((a1 != s1) != ((a2 != s2) != (a3 != s3)))) ∧
      ((!(a1 != s1)) = ((a0 != s0) != ((a2 != s2) != (a3 != s3)))) ∧
      ((!(a2 != s2)) = ((a0 != s0) != ((a1 != s1) != (a3 != s3)))) ∧
      ((!(a3 != s3)) = ((a0 != s0) != ((a1 != s1) != (a2 != s2)))) := by
  decide

private theorem xor4_rotations_of_norm {f : CNF Nat} {b0 b1 b2 b3 : BitVec 32}
    (h : let np := (((0 ^^^ b0.toNat % 2) ^^^ b1.toNat % 2) ^^^ b2.toNat % 2) ^^^ b3.toNat % 2
      XorListGateDef f
        (((b0 &&& ~~~1#32) ||| BitVec.ofNat 32 (1 ^^^ np % 2)).toNat)
        [(b1 &&& ~~~1#32).toNat, (b2 &&& ~~~1#32).toNat, (b3 &&& ~~~1#32).toNat]) :
    XorListGateDef f (litNeg b0.toNat) [b1.toNat, b2.toNat, b3.toNat] ∧
    XorListGateDef f (litNeg b1.toNat) [b0.toNat, b2.toNat, b3.toNat] ∧
    XorListGateDef f (litNeg b2.toNat) [b0.toNat, b1.toNat, b3.toNat] ∧
    XorListGateDef f (litNeg b3.toNat) [b0.toNat, b1.toNat, b2.toNat] := by
  dsimp only at h
  let np := (((0 ^^^ b0.toNat % 2) ^^^ b1.toNat % 2) ^^^ b2.toNat % 2) ^^^ b3.toNat % 2
  have hnp_lt : np < 2 := by
    have hm0 : b0.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
    have hm1 : b1.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
    have hm2 : b2.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
    have hm3 : b3.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
    rcases (by omega : b0.toNat % 2 = 0 ∨ b0.toNat % 2 = 1) with h0 | h0 <;>
      rcases (by omega : b1.toNat % 2 = 0 ∨ b1.toNat % 2 = 1) with h1 | h1 <;>
      rcases (by omega : b2.toNat % 2 = 0 ∨ b2.toNat % 2 = 1) with h2 | h2 <;>
      rcases (by omega : b3.toNat % 2 = 0 ∨ b3.toNat % 2 = 1) with h3 | h3 <;>
      simp [np, h0, h1, h2, h3]
  have hbit_eq : BitVec.ofNat 32 (1 ^^^ np % 2) = BitVec.ofNat 32 (1 ^^^ np % 2) &&& 1#32 := by
    rcases Nat.mod_two_eq_zero_or_one np with hn | hn <;> simp [hn] <;> decide
  have hlhs_n : ((b0 &&& ~~~1#32) ||| BitVec.ofNat 32 (1 ^^^ np % 2)).toNat =
      2 * (b0.toNat / 2) + (1 ^^^ np % 2) := by
    conv => lhs; arg 1; rhs; rw [hbit_eq]
    rw [bv32_even_or_bit_toNat, BitVec.toNat_ofNat]
    rcases Nat.mod_two_eq_zero_or_one np with hn | hn <;> simp [hn]
  have hsign_lhs : decide (((1 ^^^ np % 2) % 2) = 1) =
      ((((true != decide (b0.toNat % 2 = 1)) != decide (b1.toNat % 2 = 1)) !=
        decide (b2.toNat % 2 = 1)) != decide (b3.toNat % 2 = 1)) := by
    rcases Nat.mod_two_eq_zero_or_one b0.toNat with h0 | h0 <;>
      rcases Nat.mod_two_eq_zero_or_one b1.toNat with h1 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one b2.toNat with h2 | h2 <;>
      rcases Nat.mod_two_eq_zero_or_one b3.toNat with h3 | h3 <;>
      simp [np, h0, h1, h2, h3]
  have hall : ∀ α, f.Sat α →
      ((!(evalLitVal α b0.toNat)) =
        (evalLitVal α b1.toNat != (evalLitVal α b2.toNat != evalLitVal α b3.toNat))) ∧
      ((!(evalLitVal α b1.toNat)) =
        (evalLitVal α b0.toNat != (evalLitVal α b2.toNat != evalLitVal α b3.toNat))) ∧
      ((!(evalLitVal α b2.toNat)) =
        (evalLitVal α b0.toNat != (evalLitVal α b1.toNat != evalLitVal α b3.toNat))) ∧
      ((!(evalLitVal α b3.toNat)) =
        (evalLitVal α b0.toNat != (evalLitVal α b1.toNat != evalLitVal α b2.toNat))) := by
    intro α hα
    have hv := h α hα
    rw [xorEvalList_triple] at hv
    have hev_even : ∀ x : BitVec 32, evalLitVal α (x &&& ~~~1#32).toNat = α (x.toNat / 2) :=
      fun x => by rw [m6_bv32_and_not1_toNat]; simp [evalLitVal, litVar, litSign]
    have hev_lit : ∀ x : BitVec 32,
        evalLitVal α x.toNat = (α (x.toNat / 2) != decide (x.toNat % 2 = 1)) :=
      fun x => by simp [evalLitVal, litVar, litSign_of_mod2]
    have hev_lhs : evalLitVal α ((b0 &&& ~~~1#32) ||| BitVec.ofNat 32 (1 ^^^ np % 2)).toNat =
        (α (b0.toNat / 2) != ((((true != decide (b0.toNat % 2 = 1)) !=
          decide (b1.toNat % 2 = 1)) != decide (b2.toNat % 2 = 1)) !=
          decide (b3.toNat % 2 = 1))) := by
      rw [evalLitVal, litVar, litSign_of_mod2, hlhs_n]
      have hdiv : (2 * (b0.toNat / 2) + (1 ^^^ np % 2)) / 2 = b0.toNat / 2 := by
        rcases Nat.mod_two_eq_zero_or_one np with hn | hn <;> simp [hn] <;> omega
      have hmod : (2 * (b0.toNat / 2) + (1 ^^^ np % 2)) % 2 = (1 ^^^ np % 2) % 2 := by
        rcases Nat.mod_two_eq_zero_or_one np with hn | hn <;> simp [hn] <;> omega
      rw [hdiv, hmod, hsign_lhs]
    rw [hev_lhs, hev_even, hev_even, hev_even] at hv
    rw [hev_lit b0, hev_lit b1, hev_lit b2, hev_lit b3]
    exact bool_xor4_from_norm _ _ _ _ _ _ _ _ hv
  refine ⟨fun α hα => ?_, fun α hα => ?_, fun α hα => ?_, fun α hα => ?_⟩
  · rw [evalLitVal_litNeg, xorEvalList_triple]; exact (hall α hα).1
  · rw [evalLitVal_litNeg, xorEvalList_triple]; exact (hall α hα).2.1
  · rw [evalLitVal_litNeg, xorEvalList_triple]; exact (hall α hα).2.2.1
  · rw [evalLitVal_litNeg, xorEvalList_triple]; exact (hall α hα).2.2.2

private theorem c0_load_full_tmp0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMem c s ⋆ R) m) (h0 : 0 < s.core.tmp.length) :
    loadVal m i32 c.pTmp = some (s.core.tmp[0]'h0) := by
  simpa using FullArenaTactics.load_full_tmp (i := 0) h0 hm

private theorem c0_load_full_tmp0_add {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMem c s ⋆ R) m) (h0 : 0 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 0#64) = some (s.core.tmp[0]'h0) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 0#64) (by simpa using h0) hm

end Helpers

attribute [local c0_load] c0_load_full_tmp0 c0_load_full_tmp0_add

/-! ## 2. `full_cong_emit_xor_wp` & `full_cong_emit_xor4_wp` -/

theorem full_cong_emit_xor_wp (Γ : Env) :
    ∀ args m Q X, fidCongEmitXorSpec args m Q X →
      Func.wp Γ full_cong_emit_xor_body args m Q X := by
  rintro ⟨scr_ptr, g_len, x0, x1, x2, ⟨⟩⟩ m0 Q X
    ⟨maxA, F_cur, cur_vars, scr, R, hmax2, hmax64, hx0, hx1, hx2, hcv2, hg_le, hscr_lt, hxor,
     hseq0, hm0, hQ⟩
  have hxs := xor_emit_sound hx0 hx1 hx2 hxor
  have hi32 : i32.bytes = 4 := rfl
  have hg1 : (g_len + 1).toNat = g_len.toNat + 1 := by bv_omega
  have hg2 : (g_len + 2).toNat = g_len.toNat + 2 := by bv_omega
  have hg3 : (g_len + 3).toNat = g_len.toNat + 3 := by bv_omega
  let lhs := ((x0 ^^^ 1#32) &&& ~~~1#32) ||| ((((x0 ^^^ 1#32) ^^^ x1) ^^^ x2) &&& 1#32)
  let r0 := x1 &&& ~~~1#32
  let r1 := x2 &&& ~~~1#32
  have hfinish : ∀ (a0 a1 : BitVec 32) (m : Mem 64),
      ((a0 = r0 ∧ a1 = r1) ∨ (a0 = r1 ∧ a1 = r0)) →
      let scr1 := scr.set g_len.toNat lhs
      let scr2 := scr1.set (g_len.toNat + 1) ((1#32 <<< 28) ||| 2#32)
      let scr3 := scr2.set (g_len.toNat + 2) a0
      let scr4 := scr3.set (g_len.toNat + 3) a1
      (array (t := i32) scr_ptr scr4 ⋆ R) m → Q (g_len + 4#64, ()) m := by
    intro a0 a1 m hpair scr1 scr2 scr3 scr4 hm4
    have hlen4 : scr4.length = scr.length := by simp [scr4, scr3, scr2, scr1]
    have hpref : ∀ idx < g_len.toNat, scr4[idx]? = scr[idx]? := fun idx hi => by
      simp only [scr4, scr3, scr2, scr1]
      repeat rw [List.getElem?_set_ne (by omega)]
    have h0 : scr4[g_len.toNat]? = some lhs := by
      simp only [scr4, scr3, scr2, scr1]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
    have h1 : scr4[g_len.toNat + 1]? = some ((1#32 <<< 28) ||| 2#32) := by
      simp only [scr4, scr3, scr2, scr1]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simp; omega)]
    have h2 : scr4[g_len.toNat + 2]? = some a0 := by
      simp only [scr4, scr3, scr2, scr1]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
    have h3 : scr4[g_len.toNat + 3]? = some a1 := by
      simp only [scr4, scr3, scr2, scr1]; rw [List.getElem?_set_self (by simp; omega)]
    have hg_at : FidGateAt maxA F_cur cur_vars scr4 (g_len.toNat + 4) g_len.toNat := by
      refine ⟨lhs, (1#32 <<< 28) ||| 2#32, h0, h1, hxs.1,
        by show g_len.toNat + 2 + 2 ≤ g_len.toNat + 4; omega, hcv2, by show 2 ≤ maxA; omega,
        ?_, ?_⟩
      · intro k hk; have hk2 : k < 2 := hk
        match k with
        | 0 => exact ⟨a0, h2, by
            rcases hpair with ⟨rfl, _⟩ | ⟨rfl, _⟩; exact hxs.2.1; exact hxs.2.2.1⟩
        | 1 => exact ⟨a1, h3, by
            rcases hpair with ⟨_, rfl⟩ | ⟨_, rfl⟩; exact hxs.2.2.1; exact hxs.2.1⟩
        | _ + 2 => omega
      · right; left; refine ⟨rfl, by decide, by decide, ?_⟩
        have hslc2 : ((scr4.drop (g_len.toNat + 2)).take 2).map BitVec.toNat =
            [a0.toNat, a1.toNat] := by
          apply List.ext_getElem
          · simp [List.length_take, List.length_drop, hlen4]; omega
          · intro j hj1 _
            simp only [List.length_map, List.length_take, List.length_drop] at hj1
            simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
            rcases j with _ | _ | j'
            · rw [List.getElem?_eq_getElem (by omega)] at h2
              exact congrArg BitVec.toNat (Option.some.inj h2)
            · rw [List.getElem?_eq_getElem (by omega)] at h3
              exact congrArg BitVec.toNat (Option.some.inj h3)
            · omega
        have hlen_m : (((1#32 <<< 28) ||| 2#32 : BitVec 32) &&& 0xFF#32).toNat = 2 := by decide
        rw [hlen_m, hslc2]
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hxs.2.2.2.1
        · exact hxs.2.2.2.2
    have hseq4 : FidGateSeqOk maxA F_cur cur_vars scr4 (g_len.toNat + 4) 0 := by
      refine fidGateSeqOk_append_gate hpref hseq0 (.step hg_at ?_) (by omega)
      simpa [h1] using FidGateSeqOk.done
    exact hQ scr4 m hlen4 hpref hseq4 hm4
  fc_steps
  · exact hfinish r0 r1 m (Or.inl ⟨rfl, rfl⟩) (by rw [hg1, hg2, hg3] at hm; exact hm)
  · exact hfinish r1 r0 m (Or.inr ⟨rfl, rfl⟩) (by rw [hg1, hg2, hg3] at hm; exact hm)

theorem full_cong_emit_xor4_wp (Γ : Env) :
    ∀ args m Q X, fidCongEmitXor4Spec args m Q X →
      Func.wp Γ full_cong_emit_xor4_body args m Q X := by
  rintro ⟨scr_ptr, g_len, x0, x1, x2, x3, ⟨⟩⟩ m0 Q X
    ⟨maxA, F_cur, cur_vars, scr, R, hmax3, hmax64, hx0, hx1, hx2, hx3, hcv3, hg_le, hscr_lt,
     hxor, hseq0, hm0, hQ⟩
  let lhs := (x0 &&& ~~~1#32) ||| (((((1#32 ^^^ x0) ^^^ x1) ^^^ x2) ^^^ x3) &&& 1#32)
  let r0 := x1 &&& ~~~1#32
  let r1 := x2 &&& ~~~1#32
  let r2 := x3 &&& ~~~1#32
  have hlhs_lt : lhs.toNat < 2 * cur_vars := by
    have hn : lhs.toNat =
        2 * (x0.toNat / 2) + ((((1#32 ^^^ x0) ^^^ x1) ^^^ x2) ^^^ x3).toNat % 2 :=
      bv32_even_or_bit_toNat x0 ((((1#32 ^^^ x0) ^^^ x1) ^^^ x2) ^^^ x3)
    have hm : ((((1#32 ^^^ x0) ^^^ x1) ^^^ x2) ^^^ x3).toNat % 2 < 2 := Nat.mod_lt _ (by decide)
    omega
  have hr0_lt : r0.toNat < 2 * cur_vars := by
    rw [show r0.toNat = 2 * (x1.toNat / 2) from m6_bv32_and_not1_toNat x1]; omega
  have hr1_lt : r1.toNat < 2 * cur_vars := by
    rw [show r1.toNat = 2 * (x2.toNat / 2) from m6_bv32_and_not1_toNat x2]; omega
  have hr2_lt : r2.toNat < 2 * cur_vars := by
    rw [show r2.toNat = 2 * (x3.toNat / 2) from m6_bv32_and_not1_toNat x3]; omega
  have hsem0 : XorListGateDef (cnfOfClauses F_cur) lhs.toNat [r0.toNat, r1.toNat, r2.toNat] :=
    fid_emit_xor4_sem hxor
  have hi32 : i32.bytes = 4 := rfl
  have hg1 : (g_len + 1).toNat = g_len.toNat + 1 := by bv_omega
  have hg2 : (g_len + 2).toNat = g_len.toNat + 2 := by bv_omega
  have hg3 : (g_len + 3).toNat = g_len.toNat + 3 := by bv_omega
  have hg4 : (g_len + 4).toNat = g_len.toNat + 4 := by bv_omega
  fc_to_group
  refine wp_join_group (ts := [i32, i32])
    (fun (a0, a1, ()) m1 => m1 = m0 ∧ List.Perm [a0, a1, r2] [r0, r1, r2]) ?_ ?_
  · rintro _ ⟨a0, a1, ⟨⟩⟩ m1 ⟨hm1, hp1⟩; rw [hm1]; fc_to_group
    refine wp_join_group (ts := [i32, i32])
      (fun (b1, b2, ()) m2 => m2 = m0 ∧ List.Perm [a0, b1, b2] [r0, r1, r2]) ?_ ?_
    · rintro _ ⟨b1, b2, ⟨⟩⟩ m2 ⟨hm2, hp2⟩; rw [hm2]; fc_to_group
      refine wp_join_group (ts := [i32, i32])
        (fun (c0, c1, ()) m3 => m3 = m0 ∧ List.Perm [c0, c1, b2] [r0, r1, r2]) ?_ ?_
      · rintro _ ⟨c0, c1, ⟨⟩⟩ m3 ⟨hm3, hp3⟩; rw [hm3]
        have hlt_mem : ∀ v ∈ [c0, c1, b2], v.toNat < 2 * cur_vars := fun v hv => by
          have hm := hp3.mem_iff.mp hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with rfl | rfl | rfl <;> assumption
        have hc0_lt : c0.toNat < 2 * cur_vars := hlt_mem c0 (by simp)
        have hc1_lt : c1.toNat < 2 * cur_vars := hlt_mem c1 (by simp)
        have hb2_lt : b2.toNat < 2 * cur_vars := hlt_mem b2 (by simp)
        have h0_lt : g_len.toNat < scr.length := by omega
        have h1_lt : (g_len + 1).toNat < scr.length := by omega
        have h2_lt : (g_len + 2).toNat < scr.length := by omega
        have h3_lt : (g_len + 3).toNat < scr.length := by omega
        have h4_lt : (g_len + 4).toNat < scr.length := by omega
        fc_steps
        let scr5 := ((((scr.set g_len.toNat lhs).set (g_len.toNat + 1) ((1#32 <<< 28) ||| 3#32)).set
          (g_len.toNat + 2) c0).set (g_len.toNat + 3) c1).set (g_len.toNat + 4) b2
        have hm5 : (array (t := i32) scr_ptr scr5 ⋆ R) m := by
          dsimp only [scr5]; rw [hg1, hg2, hg3, hg4] at hm; exact hm
        have hlen5 : scr5.length = scr.length := by simp [scr5]
        have hpref : ∀ idx < g_len.toNat, scr5[idx]? = scr[idx]? := fun idx hi => by
          simp only [scr5]; repeat rw [List.getElem?_set_ne (by omega)]
        have hs0 : scr5[g_len.toNat]? = some lhs := by
          simp only [scr5]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_self (by omega)]
        have hs1 : scr5[g_len.toNat + 1]? = some ((1#32 <<< 28) ||| 3#32) := by
          simp only [scr5]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
        have hs2 : scr5[g_len.toNat + 2]? = some c0 := by
          simp only [scr5]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_self (by simp; omega)]
        have hs3 : scr5[g_len.toNat + 3]? = some c1 := by
          simp only [scr5]; rw [List.getElem?_set_ne (by omega),
            List.getElem?_set_self (by simp; omega)]
        have hs4 : scr5[g_len.toNat + 4]? = some b2 := by
          simp only [scr5]; rw [List.getElem?_set_self (by simp; omega)]
        have hgat : FidGateAt maxA F_cur cur_vars scr5 (g_len.toNat + 5) g_len.toNat := by
          refine ⟨lhs, (1#32 <<< 28) ||| 3#32, hs0, hs1, hlhs_lt,
            by show g_len.toNat + 2 + 3 ≤ g_len.toNat + 5; omega, hcv3, by show 3 ≤ maxA; omega,
            ?_, ?_⟩
          · intro k hk; have hk3 : k < 3 := hk
            match k with
            | 0 => exact ⟨c0, hs2, hc0_lt⟩
            | 1 => exact ⟨c1, hs3, hc1_lt⟩
            | 2 => exact ⟨b2, hs4, hb2_lt⟩
            | _ + 3 => omega
          · right; left; refine ⟨rfl, by decide, by decide, ?_⟩
            have hslc3 : ((scr5.drop (g_len.toNat + 2)).take 3).map BitVec.toNat =
                [c0.toNat, c1.toNat, b2.toNat] := by
              apply List.ext_getElem
              · simp [List.length_take, List.length_drop, hlen5]; omega
              · intro j hj1 _
                simp only [List.length_map, List.length_take, List.length_drop] at hj1
                simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
                rcases j with _ | _ | _ | j'
                · rw [List.getElem?_eq_getElem (by omega)] at hs2
                  exact congrArg BitVec.toNat (Option.some.inj hs2)
                · rw [List.getElem?_eq_getElem (by omega)] at hs3
                  exact congrArg BitVec.toNat (Option.some.inj hs3)
                · rw [List.getElem?_eq_getElem (by omega)] at hs4
                  exact congrArg BitVec.toNat (Option.some.inj hs4)
                · omega
            have hlen_m : (((1#32 <<< 28) ||| 3#32 : BitVec 32) &&& 0xFF#32).toNat = 3 := by
              decide
            rw [hlen_m, hslc3]
            intro α hα
            have hp3' : List.Perm [c0.toNat, c1.toNat, b2.toNat]
                [r0.toNat, r1.toNat, r2.toNat] := hp3.map BitVec.toNat
            rw [xorEvalList_perm α hp3']
            exact hsem0 α hα
        have hseq5 : FidGateSeqOk maxA F_cur cur_vars scr5 (g_len.toNat + 5) 0 := by
          refine fidGateSeqOk_append_gate hpref hseq0 (.step hgat ?_) (by omega)
          simpa [hs1] using FidGateSeqOk.done
        exact hQ scr5 m hlen5 hpref hseq5 hm5
      · intro J3 hJ3; fc_split_fast
        · fc_let; exact hJ3 (b1, a0, ()) m0 ⟨rfl, (List.Perm.swap a0 b1 [b2]).trans hp2⟩
        · fc_let; exact hJ3 (a0, b1, ()) m0 ⟨rfl, hp2⟩
    · intro J2 hJ2; fc_split_fast
      · fc_let
        exact hJ2 (r2, a1, ()) m0 ⟨rfl, (List.Perm.cons a0 (List.Perm.swap a1 r2 [])).trans hp1⟩
      · fc_let; exact hJ2 (a1, r2, ()) m0 ⟨rfl, hp1⟩
  · intro J1 hJ1; fc_split_fast
    · fc_let; exact hJ1 (r1, r0, ()) m0 ⟨rfl, List.Perm.swap r0 r1 [r2]⟩
    · fc_let; exact hJ1 (r0, r1, ()) m0 ⟨rfl, List.Perm.refl _⟩

/-! ## 3. `full_cong_has_clause_k_wp` (`m6CongHasClauseKSpec`) -/

theorem full_cong_has_clause_k_wp (Γ : Env) :
    ∀ args m Q X, m6CongHasClauseKSpec args m Q X →
      Func.wp Γ full_cong_has_clause_k_body args m Q X := by
  rintro ⟨h, k, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hmk, hnd, hcl0, hk3, hk5, hkcv, htmp_lt, htmp_dis, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; have hac := c.harena
  unfold dimacsBound at hmx hwc hac
  have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have hcv_le := hcl.cur_vars_le; have htmpl := hcl.tmp_len_arr; have hlml := hcl.lit_mark_len
  have hwvl := hcl.wvec_len; have hwsl := hcl.wstk_len_arr; have hwle := hcl.wlen_le
  have harl := hcl.arena_len_arr; have hale := hcl.arena_len_le; have hvl := hcl.vals_len
  have h0_tmp : 0 < s.core.tmp.length := by omega
  let min_l0 := s.core.tmp[0]'h0_tmp
  have hmin0_lt : min_l0.toNat < 2 * s.core.cur_vars := by
    have := htmp_lt 0 (by omega)
    rwa [List.getElem?_eq_getElem h0_tmp, Option.getD_some] at this
  have hshl0_1 : (min_l0.setWidth 64 <<< (1 : Nat) + 1#64).toNat = 2 * min_l0.toNat + 1 := by
    rw [BitVec.toNat_add, FullCongHelpers.bv64_shl1_toNat, bv_zext32_toNat]
    show (2 * min_l0.toNat % 2 ^ 64 + 1) % 2 ^ 64 = 2 * min_l0.toNat + 1; omega
  have hmin0_wvec : (min_l0.setWidth 64 <<< (1 : Nat) + 1#64).toNat < s.core.wvec.length := by
    omega
  have hmin0_wvec_se :
      (min_l0.setWidth 64 <<< ((1#32 : BitVec 32).signExtend 64).toNat + 1#64).toNat <
        s.core.wvec.length := hmin0_wvec
  have hmin0_wvec_bv :
      (min_l0.setWidth 64 <<< ((1#32 : BitVec 32).signExtend 64) + 1#64).toNat <
        s.core.wvec.length := hmin0_wvec
  let unassLits := (List.range k.toNat).map fun idx => (s.core.tmp[idx]?.getD 0#32).toNat
  have hmin0_in : min_l0.toNat ∈ unassLits := by
    refine List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), ?_⟩
    rw [List.getElem?_eq_getElem h0_tmp, Option.getD_some]
  have hnl_eq : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]
  fc_split_fast
  · exfalso
    have : k.toNat < 3 := by simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
    omega
  clear hc; fc_split_fast
  · exfalso
    have : 5 < k.toNat := by simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
    omega
  clear hc; fc_split_fast
  · exfalso
    have : s.core.cur_vars < k.toNat := by
      simp only [BitVec.ult, decide_eq_true_eq] at hc; bv_omega
    omega
  · clear hc; fc_steps
    refine wp_loop_inv (ts := [i32, i32, i32])
      (fun (min_l, _min_d, i, ()) mi => ∃ lm' : List (BitVec 8),
        lm'.length = 2 * c.max_vars ∧ i.toNat ≤ k.toNat ∧ min_l.toNat < 2 * s.core.cur_vars ∧
        min_l.toNat ∈ unassLits ∧
        (∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 = 0#8 ∨ l ∈ unassLits) ∧
        (FullMem c { s with core := { s.core with lit_mark := lm' } } ⋆ R) mi)
      (fun (_, _, i, ()) _ => k.toNat - i.toNat)
      (fun J1 hJ1 => by
        fc_let; refine hJ1 (min_l0, _, 0#32, ()) m0
          ⟨s.core.lit_mark, hlml, Nat.zero_le _, hmin0_lt, hmin0_in,
           fun l hl => Or.inl (hmk.2 l hl), hm0⟩)
      (fun J1 (min_l, min_d, i, ()) mi ⟨lm', hlml', hi_le, hmin_lt, hmin_in, hlm_inv, hmi⟩
        ih1 => ?_)
    let si : FullState := { s with core := { s.core with lit_mark := lm' } }
    fc_split_fast
    · have hi_lt : i.toNat < k.toNat := by
        simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
      have hi1_n : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
      have hi_tmp : (i.setWidth 64).toNat < si.core.tmp.length := by
        rw [bv_zext32_toNat]; change i.toNat < s.core.tmp.length; omega
      let tl := si.core.tmp[(i.setWidth 64).toNat]'hi_tmp
      have htl_eq : tl = s.core.tmp[i.toNat]?.getD 0#32 := by
        dsimp only [tl, si]; rw [List.getElem?_eq_getElem (by omega : i.toNat < s.core.tmp.length),
          Option.getD_some]; exact list_getElem_congr (bv_zext32_toNat i) _ _
      have htl_lt : tl.toNat < 2 * s.core.cur_vars := by rw [htl_eq]; exact htmp_lt i.toNat hi_lt
      have htl_in : tl.toNat ∈ unassLits := by
        rw [htl_eq]; exact List.mem_map.mpr ⟨i.toNat, List.mem_range.mpr hi_lt, rfl⟩
      have htl_lm : (tl.setWidth 64).toNat < si.core.lit_mark.length := by
        rw [bv_zext32_toNat]; change tl.toNat < lm'.length; omega
      have htl_wv : (tl.setWidth 64 <<< (1 : Nat) + 1#64).toNat < si.core.wvec.length := by
        rw [BitVec.toNat_add, FullCongHelpers.bv64_shl1_toNat, bv_zext32_toNat]
        change (2 * tl.toNat % 2 ^ 64 + 1) % 2 ^ 64 < s.core.wvec.length; omega
      have htl_wv_se :
          (tl.setWidth 64 <<< ((1#32 : BitVec 32).signExtend 64).toNat + 1#64).toNat <
            si.core.wvec.length := htl_wv
      have htl_wv_bv :
          (tl.setWidth 64 <<< ((1#32 : BitVec 32).signExtend 64) + 1#64).toNat <
            si.core.wvec.length := htl_wv
      fc_to_group
      let lm'' := lm'.set (tl.setWidth 64).toNat ((i + 1#32).setWidth 8)
      have hlm''_len : lm''.length = 2 * c.max_vars := by simp [lm'', hlml']
      have hlm''_inv : ∀ l < 2 * c.max_vars, lm''[l]?.getD 0#8 = 0#8 ∨ l ∈ unassLits := by
        intro l hl; dsimp only [lm'']
        by_cases hltl : l = (tl.setWidth 64).toNat
        · right; rw [hltl, bv_zext32_toNat]; exact htl_in
        · rw [List.getElem?_set_ne (Ne.symm hltl)]; exact hlm_inv l hl
      have hmi' : (FullMem c { s with core := { s.core with lit_mark := lm'' } } ⋆ R) m := hm
      refine wp_join_group (ts := [i32, i32])
        (fun (min_l', _min_d', ()) m' =>
          m' = m ∧ min_l'.toNat < 2 * s.core.cur_vars ∧ min_l'.toNat ∈ unassLits) ?_ ?_
      · rintro _ ⟨min_l', min_d', ⟨⟩⟩ m' ⟨hm', hml'_lt, hml'_in⟩
        subst m'; fc_let
        exact ih1 (min_l', min_d', i + 1#32, ()) m (by dsimp only; omega)
          ⟨lm'', hlm''_len, by omega, hml'_lt, hml'_in, hlm''_inv, hmi'⟩
      · intro Jd hJd; fc_steps
        · exact hJd (tl, _, ()) m ⟨rfl, htl_lt, htl_in⟩
        · exact hJd (min_l, min_d, ()) m ⟨rfl, hmin_lt, hmin_in⟩
    · clear hc
      have hw_bd := hw.watches.bounds min_l.toNat hmin_lt
      have hshl_m : (min_l.setWidth 64 <<< (1 : Nat)).toNat = 2 * min_l.toNat := by
        rw [FullCongHelpers.bv64_shl1_toNat, bv_zext32_toNat]; omega
      have hshl1_m : (min_l.setWidth 64 <<< (1 : Nat) + 1#64).toNat = 2 * min_l.toNat + 1 := by
        rw [BitVec.toNat_add, hshl_m]
        show (2 * min_l.toNat + 1) % 2 ^ 64 = 2 * min_l.toNat + 1; omega
      have hslice0 : if s.core.dense_mode = 0#64 then
            WatchSliceOk F_cur s.core min_l.toNat (fullWatchOffCore s.core min_l.toNat)
              (fullWatchSizeCore s.core min_l.toNat)
          else DenseWatchSliceOk F_cur s.core min_l.toNat (fullWatchOffCore s.core min_l.toNat)
              (fullWatchSizeCore s.core min_l.toNat) := by
        have hwat := hw.watches; unfold ModeWatchesInv at hwat
        by_cases hdm : s.core.dense_mode = 0#64 <;> simp only [hdm, ↓reduceIte] at hwat ⊢
        · exact hwat.slices min_l.toNat hmin_lt
        · exact hwat.slices min_l.toNat hmin_lt
      have hml_wv0 : (min_l.setWidth 64 <<< (1 : Nat)).toNat < si.core.wvec.length := by
        change _ < s.core.wvec.length; omega
      have hml_wv1 : (min_l.setWidth 64 <<< (1 : Nat) + 1#64).toNat < si.core.wvec.length := by
        change _ < s.core.wvec.length; omega
      fc_to_group
      generalize hoff_v :
        (si.core.wvec[(min_l.setWidth 64 <<< (1 : Nat)).toNat]'hml_wv0).setWidth 64 = off
      generalize hwsz_v :
        (si.core.wvec[(min_l.setWidth 64 <<< (1 : Nat) + 1#64).toNat]'hml_wv1).setWidth 64 = wsz
      have hoff_n : off.toNat = fullWatchOffCore s.core min_l.toNat := by
        rw [← hoff_v, bv_zext32_toNat]; unfold fullWatchOffCore
        rw [List.getElem?_eq_getElem (by omega : 2 * min_l.toNat < s.core.wvec.length),
          Option.getD_some]
        exact congrArg BitVec.toNat (list_getElem_congr hshl_m (by omega) (by omega))
      have hwsz_n : wsz.toNat = fullWatchSizeCore s.core min_l.toNat := by
        rw [← hwsz_v, bv_zext32_toNat]; unfold fullWatchSizeCore
        rw [List.getElem?_eq_getElem (by omega : 2 * min_l.toNat + 1 < s.core.wvec.length),
          Option.getD_some]
        exact congrArg BitVec.toNat (list_getElem_congr hshl1_m (by omega) (by omega))
      have hend_n : (off + wsz).toNat = off.toNat + wsz.toNat := by bv_omega
      refine wp_loop_break_group (brkTs := [.bool, i64]) (lpTs := [i64])
        (fun (res, _, ()) mb => mb = mi ∧
          (res = true → (cnfOfClauses F_cur).EntailsClause (cnfClause unassLits)))
        (fun rem (p, ()) mp =>
          mp = mi ∧ p.toNat ≤ (off + wsz).toNat ∧ rem = (off + wsz).toNat - p.toNat ∧
          (if s.core.dense_mode = 0#64 then
             WatchSliceOk F_cur s.core min_l.toNat p.toNat ((off + wsz).toNat - p.toNat)
           else DenseWatchSliceOk F_cur s.core min_l.toNat p.toNat ((off + wsz).toNat - p.toNat)))
        ?_ ?_ ?_
      · rintro _ ⟨res, _, ⟨⟩⟩ mb ⟨hmb, hres⟩
        rw [hmb]; fc_steps
        refine wp_loop_inv
          (fun (i3, ()) mc => ∃ lm3 : List (BitVec 8),
            lm3.length = 2 * c.max_vars ∧ i3.toNat ≤ k.toNat ∧
            (∀ l < 2 * c.max_vars, lm3[l]?.getD 0#8 = 0#8 ∨
              ∃ idx, i3.toNat ≤ idx ∧ idx < k.toNat ∧
                (s.core.tmp[idx]?.getD 0#32).toNat = l) ∧
            (FullMem c { s with core := { s.core with lit_mark := lm3 } } ⋆ R) mc)
          (fun (i3, ()) _ => k.toNat - i3.toNat)
          (fun J3 hJ3 => by
            fc_let; refine hJ3 (0#32, ()) mi ⟨lm', hlml', Nat.zero_le _, fun l hl => ?_, hmi⟩
            rcases hlm_inv l hl with h0 | hmem
            · exact Or.inl h0
            · obtain ⟨idx, hrng, heq⟩ := List.mem_map.mp hmem
              exact Or.inr ⟨idx, Nat.zero_le _, List.mem_range.mp hrng, heq⟩)
          (fun J3 (i3, ()) mc ⟨lm3, hlml3, hi3_le, hlm3_inv, hmc⟩ ih3 => ?_)
        fc_split_fast
        · have hi3_lt : i3.toNat < k.toNat := by
            simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
          have hi3_1 : (i3 + 1#32).toNat = i3.toNat + 1 := by bv_omega
          have hi3_tmp : (i3.setWidth 64).toNat < s.core.tmp.length := by
            rw [bv_zext32_toNat]; omega
          let tl := s.core.tmp[(i3.setWidth 64).toNat]'hi3_tmp
          have htl_eq : tl = s.core.tmp[i3.toNat]?.getD 0#32 := by
            dsimp only [tl]; rw [List.getElem?_eq_getElem (by omega : i3.toNat < s.core.tmp.length),
              Option.getD_some]; exact list_getElem_congr (bv_zext32_toNat i3) _ _
          have htl_lt : tl.toNat < 2 * s.core.cur_vars := by
            rw [htl_eq]; exact htmp_lt i3.toNat hi3_lt
          have htl_lm : (tl.setWidth 64).toNat < lm3.length := by rw [bv_zext32_toNat]; omega
          fc_steps
          let lm3' := lm3.set (tl.setWidth 64).toNat 0#8
          have hlm3'_inv : ∀ l < 2 * c.max_vars, lm3'[l]?.getD 0#8 = 0#8 ∨
              ∃ idx, (i3 + 1#32).toNat ≤ idx ∧ idx < k.toNat ∧
                (s.core.tmp[idx]?.getD 0#32).toNat = l := by
            intro l hl; dsimp only [lm3']
            by_cases hltl : l = (tl.setWidth 64).toNat
            · left; rw [hltl, List.getElem?_set_self htl_lm, Option.getD_some]
            · rw [List.getElem?_set_ne (Ne.symm hltl)]
              rcases hlm3_inv l hl with h0 | ⟨idx, h1, h2, h3⟩
              · exact Or.inl h0
              · right; refine ⟨idx, ?_, h2, h3⟩
                have hne : idx ≠ i3.toNat := fun he => by
                  subst he; apply hltl; rw [bv_zext32_toNat, htl_eq, h3]
                omega
          exact ih3 (i3 + 1#32, ()) m (by dsimp only; omega)
            ⟨lm3', by simp [lm3', hlml3], by omega, hlm3'_inv, hm⟩
        · have hi3_eq : i3.toNat = k.toNat := by
            simp only [BitVec.ult, decide_eq_false_iff_not] at hc; omega
          have hclear : FullLitMarksClear c { s with core := { s.core with lit_mark := lm3 } } :=
            ⟨hmk.1, fun l hl => by
              rcases hlm3_inv l hl with h0 | ⟨idx, h1, h2, _⟩
              · exact h0
              · omega⟩
          fc_steps
          exact hQ res { s with core := { s.core with lit_mark := lm3 } } mc
            ⟨{ hcl with lit_mark_len := hlml3 }, hsl⟩ rfl rfl hclear hres hmc
      · rintro B L rem ⟨p, ⟨⟩⟩ mp hB hL ⟨hmp, hp_le, rfl, hslice⟩
        rw [hmp]; fc_split_fast
        · have hp_lt : p.toNat < (off + wsz).toNat := by
            simp only [BitVec.ult, decide_eq_true_eq] at hc; bv_omega
          have hp_w : p.toNat < s.core.wstk.length := by omega
          obtain ⟨w0, hw0_get, hcase⟩ := slice_pop_step_fid hslice (by omega)
          have hw0_eq : s.core.wstk[p.toNat]'hp_w = w0 := by
            rw [List.getElem?_eq_getElem hp_w] at hw0_get; exact Option.some.inj hw0_get
          have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
          fc_split_fast
          · rcases hcase with ⟨_, hent_bin, hrest⟩ | ⟨hf0, _⟩
            · have hcont1 : L (p + 1#64, ()) mi :=
                hL ((off + wsz).toNat - (p + 1#64).toNat) (p + 1#64, ()) mi (by omega)
                  ⟨rfl, by omega, rfl, by simpa [hp1_n, Nat.sub_sub] using hrest⟩
              let ot := w0 &&& 0x7FFFFFFF#32
              fc_split_fast
              · have hot_lt : ot.toNat < 2 * s.core.cur_vars := by
                  simp only [BitVec.ult, decide_eq_true_eq] at hc
                  rw [hw0_eq, bv_zext32_toNat, hnl_eq] at hc; exact hc
                have hot_v : (ot.setWidth 64).toNat < si.core.vals.length := by
                  rw [bv_zext32_toNat]; change ot.toNat < s.core.vals.length; omega
                have hot_v_w :
                    ((s.core.wstk[p.toNat]'hp_w &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                      si.core.vals.length := by rw [hw0_eq]; exact hot_v
                have hot_v' : ot.toNat < s.core.vals.length := by
                  rw [bv_zext32_toNat] at hot_v; exact hot_v
                have hot_lm : (ot.setWidth 64).toNat < si.core.lit_mark.length := by
                  rw [bv_zext32_toNat]; change ot.toNat < lm'.length; omega
                have hot_lm_w :
                    ((s.core.wstk[p.toNat]'hp_w &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                      si.core.lit_mark.length := by rw [hw0_eq]; exact hot_lm
                have hdom_ot : s.core.vals[ot.toNat]'hot_v' = 0#8 ∨
                    s.core.vals[ot.toNat]'hot_v' = 1#8 ∨
                    s.core.vals[ot.toNat]'hot_v' = 0xFF#8 := by
                  have h := hw.vals_domain ot.toNat hot_lt
                  rwa [List.getElem?_eq_getElem hot_v', Option.getD_some] at h
                clear hc; fc_split_fast
                · have hov_ff : s.core.vals[ot.toNat]?.getD 0#8 = 0xFF#8 := by
                    rw [List.getElem?_eq_getElem hot_v', Option.getD_some]
                    have hidx :
                        ((s.core.wstk[p.toNat]'hp_w &&& 2147483647).setWidth 64).toNat =
                          ot.toNat := by rw [hw0_eq, bv_zext32_toNat]; rfl
                    rw [list_getElem_congr hidx _ hot_v'] at hc
                    rcases hdom_ot with hv | hv | hv
                    · exfalso; rw [hv] at hc; cases hc
                    · exfalso; rw [hv] at hc; cases hc
                    · exact hv
                  fc_steps
                  exact hB (true, p + 1#64, ()) mi ⟨rfl, fun _ =>
                    bin_subsumes_unass hw hcl0 hot_lt hent_bin hmin_in (Or.inl hov_ff)⟩
                · clear hc; fc_split_fast
                  · clear hc; fc_split_fast
                    · have hot_in : ot.toNat ∈ unassLits := by
                        have hne0 : lm'[ot.toNat]?.getD 0#8 ≠ 0#8 := by
                          intro h0
                          have hidx :
                              ((s.core.wstk[p.toNat]'hp_w &&& 2147483647).setWidth 64).toNat =
                                ot.toNat := by rw [hw0_eq, bv_zext32_toNat]; rfl
                          rw [List.getElem?_eq_getElem (by omega : ot.toNat < lm'.length),
                            Option.getD_some] at h0
                          change (BitVec.setWidth 32 (lm'[_]'_) != 0#32) = true at hc
                          rw [list_getElem_congr hidx _ (by omega), h0] at hc; cases hc
                        exact (hlm_inv ot.toNat (by omega)).resolve_left hne0
                      fc_steps
                      exact hB (true, p + 1#64, ()) mi ⟨rfl, fun _ =>
                        bin_subsumes_unass hw hcl0 hot_lt hent_bin hmin_in (Or.inr hot_in)⟩
                    · fc_steps; exact hcont1
                  · fc_steps; exact hcont1
              · fc_steps; exact hcont1
            · exfalso; rw [hw0_eq] at hc
              rw [show (w0 &&& 2147483648 : BitVec 32) = w0 &&& 2147483648#32 from rfl, hf0] at hc
              revert hc; decide
          · rcases hcase with ⟨hf1, _⟩ | ⟨_, hrem2, cr, hcr_get, hcr_ref, hrest2⟩
            · exfalso; rw [hw0_eq] at hc; exact hf1 (by grind)
            · have hp1_n' : (p + 1).toNat = p.toNat + 1 := hp1_n
              have hp1_w : (p + 1).toNat < s.core.wstk.length := by omega
              have hcr_eq : s.core.wstk[(p + 1).toNat]'hp1_w = cr := by
                rw [list_getElem_congr hp1_n' hp1_w (by omega)]
                rw [List.getElem?_eq_getElem (by omega)] at hcr_get
                exact Option.some.inj hcr_get
              have hcr_wf := hw.arena.refs_wf cr.toNat hcr_ref
              have hp2_n : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by bv_omega
              have hcont2 : L (p + 1 + 1, ()) mi :=
                hL ((off + wsz).toNat - (p + 1#64 + 1#64).toNat) (p + 1#64 + 1#64, ()) mi
                  (by omega) ⟨rfl, by omega, rfl, by simpa [hp2_n, Nat.sub_sub] using hrest2⟩
              fc_split_fast
              · exfalso; simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
              · clear hc
                have hcr_arr : cr.toNat < s.core.arena.length := by omega
                have hcr2_arr : cr.toNat + 2 < s.core.arena.length := by omega
                have hcr_z : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64).toNat <
                    s.core.arena.length := by rw [hcr_eq, bv_zext32_toNat]; exact hcr_arr
                have hcr2_n : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 2).toNat =
                    cr.toNat + 2 := by
                  rw [hcr_eq, BitVec.toNat_add, bv_zext32_toNat,
                    show (2 : BitVec 64).toNat = 2 from rfl]
                  exact Nat.mod_eq_of_lt (by omega)
                have hcr2_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 2).toNat <
                    s.core.arena.length := by rw [hcr2_n]; omega
                fc_split_fast
                · fc_steps; exact hcont2
                · have hng_red :
                      (s.core.arena[((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth
                        64).toNat]'hcr_z &&& 0x00480000#32) = 0#32 := by simpa using hc
                  clear hc
                  have hng : fullArenaClauseGarb s cr.toNat = false := by
                    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                    rw [List.getElem?_eq_getElem hcr_arr, Option.getD_some]
                    exact garb_false_of_and_480000
                      (by rwa [list_getElem_congr (by rw [hcr_eq, bv_zext32_toNat]) hcr_z hcr_arr]
                        at hng_red)
                  let sz_bv := s.core.arena[cr.toNat + 2]'(by omega)
                  have hsz_eq : sz_bv.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
                    unfold fullArenaClauseSizeCore
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  have hsz_cv : sz_bv.toNat ≤ s.core.cur_vars := by
                    rw [hsz_eq]; exact fullArenaClauseSize_le_cur_vars hlen hw hnd hcr_ref hng
                  have hbd_ar : cr.toNat + 3 + sz_bv.toNat ≤ s.core.arena.length := by omega
                  fc_to_group
                  refine wp_loop_break_group (brkTs := [.bool, i32]) (lpTs := [i32])
                    (fun (ok, _, ()) mb2 => mb2 = mi ∧
                      (ok = true → ∀ q < sz_bv.toNat,
                        let cl := (s.core.arena[cr.toNat + 3 + q]?.getD 0#32).toNat
                        s.core.vals[cl]?.getD 0#8 = 0xFF#8 ∨ cl ∈ unassLits))
                    (fun rem2 (j, ()) mj => mj = mi ∧ j.toNat ≤ sz_bv.toNat ∧
                      rem2 = sz_bv.toNat - j.toNat ∧
                      ∀ q < j.toNat,
                        let cl := (s.core.arena[cr.toNat + 3 + q]?.getD 0#32).toNat
                        s.core.vals[cl]?.getD 0#8 = 0xFF#8 ∨ cl ∈ unassLits)
                    ?_ ?_ ?_
                  · rintro _ ⟨ok, _, ⟨⟩⟩ mb2 ⟨hmb2, hok⟩
                    rw [hmb2]; fc_split_fast
                    · have hok_t : ok = true := hc
                      have hcov : ∀ l ∈ fullArenaClauseLits s cr.toNat,
                            s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨ l ∈ unassLits := fun l hl => by
                        obtain ⟨q, hq, hql⟩ :=
                          (mem_fullArenaClauseLitsCore_iff (hsz_eq ▸ hbd_ar)).mp hl
                        rw [← hsz_eq] at hq
                        have h := hok hok_t q hq; dsimp only at h
                        rw [List.getElem?_eq_getElem (by omega :
                          cr.toNat + 3 + q < s.core.arena.length), Option.getD_some, hql] at h
                        exact h
                      fc_steps
                      exact hB (true, p + 1 + 1, ()) mi
                        ⟨rfl, fun _ => unassigned_clause_entails hw hcl0 hcr_ref hng hcov⟩
                    · fc_steps; exact hcont2
                  · rintro B2 L2 rem2 ⟨j, ⟨⟩⟩ mj hB2 hL2 ⟨hmj, hj_le, rfl, hcov_j⟩
                    rw [hmj]; fc_split_fast
                    · have hj_lt : j.toNat < sz_bv.toNat := by
                        rw [list_getElem_congr hcr2_n hcr2_w hcr2_arr] at hc
                        simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                      have hj1_n : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
                      have hcr3j_n : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 3 +
                          j.setWidth 64).toNat = cr.toNat + 3 + j.toNat := by
                        have h3 : (cr.toNat + 3) % 2 ^ 64 = cr.toNat + 3 :=
                          Nat.mod_eq_of_lt (by omega)
                        rw [hcr_eq, BitVec.toNat_add, BitVec.toNat_add, bv_zext32_toNat,
                          bv_zext32_toNat, show (3 : BitVec 64).toNat = 3 from rfl, h3,
                          Nat.mod_eq_of_lt (by omega)]
                      have hcr3j_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 3 +
                          j.setWidth 64).toNat < s.core.arena.length := by rw [hcr3j_n]; omega
                      let cl := s.core.arena[cr.toNat + 3 + j.toNat]'(by omega)
                      have hcl_get : cl = s.core.arena[cr.toNat + 3 + j.toNat]?.getD 0#32 := by
                        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                      have hcl_mem : cl.toNat ∈ fullArenaClauseLits s cr.toNat := by
                        rw [mem_fullArenaClauseLitsCore_iff (hsz_eq ▸ hbd_ar)]
                        exact ⟨j.toNat, by rw [← hsz_eq]; exact hj_lt, rfl⟩
                      have hcl_lt : cl.toNat < 2 * s.core.cur_vars :=
                        hw.arena.lits_lt cr.toNat hcr_ref hng cl.toNat hcl_mem
                      have hcl_eq : s.core.arena[((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 +
                          3 + j.setWidth 64).toNat]'hcr3j_w = cl :=
                        list_getElem_congr hcr3j_n hcr3j_w (by omega)
                      have hcl_v : (cl.setWidth 64).toNat < si.core.vals.length := by
                        rw [bv_zext32_toNat]; change cl.toNat < s.core.vals.length; omega
                      have hcl_lm : (cl.setWidth 64).toNat < si.core.lit_mark.length := by
                        rw [bv_zext32_toNat]; change cl.toNat < lm'.length; omega
                      fc_split_fast
                      · fc_steps; exact hB2 (false, j, ()) mi ⟨rfl, fun h => by cases h⟩
                      · have hne1_cl : s.core.vals[cl.toNat]?.getD 0#8 ≠ 1#8 := by
                          intro h1
                          have hdom : s.core.vals[cl.toNat]'(by omega) = 1#8 := by
                            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
                            exact h1
                          have hidx : ((s.core.arena[((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth
                              64 + 3 + j.setWidth 64).toNat]'hcr3j_w).setWidth 64).toNat =
                              cl.toNat := by rw [hcl_eq, bv_zext32_toNat]
                          change (0#32).slt
                            (BitVec.signExtend 32 (s.core.vals[_]'_)) = false at hc
                          rw [list_getElem_congr hidx _ (by omega), hdom] at hc; cases hc
                        clear hc; fc_to_group
                        refine wp_join_group (ts := [])
                          (fun () mj' => mj' = mi ∧
                            (s.core.vals[cl.toNat]?.getD 0#8 = 0xFF#8 ∨ cl.toNat ∈ unassLits))
                          ?_ ?_
                        · rintro _ ⟨⟩ mj' ⟨hmj', hcl_cov⟩
                          rw [hmj']; fc_steps
                          refine hL2 (sz_bv.toNat - (j + 1#32).toNat) (j + 1#32, ()) mi
                            (by omega) ⟨rfl, by omega, rfl, fun q hq => ?_⟩
                          rw [hj1_n] at hq
                          by_cases hqj : q = j.toNat
                          · subst hqj; rw [← congrArg BitVec.toNat hcl_get]; exact hcl_cov
                          · exact hcov_j q (by omega)
                        · intro Js hJs; fc_split_fast
                          · clear hc; fc_split_fast
                            · fc_steps; exact hB2 (false, j, ()) mi ⟨rfl, fun h => by cases h⟩
                            · have hcl_in : cl.toNat ∈ unassLits := by
                                have hne0 : lm'[cl.toNat]?.getD 0#8 ≠ 0#8 := by
                                  intro h0
                                  have hidx : ((s.core.arena[((s.core.wstk[(p + 1).toNat]'
                                      hp1_w).setWidth 64 + 3 + j.setWidth 64).toNat]'
                                      hcr3j_w).setWidth 64).toNat = cl.toNat := by
                                    rw [hcl_eq, bv_zext32_toNat]
                                  change (BitVec.setWidth 32 (lm'[_]'_) == 0#32) = false at hc
                                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
                                  rw [list_getElem_congr hidx _ (by omega), h0] at hc; cases hc
                                exact (hlm_inv cl.toNat (by omega)).resolve_left hne0
                              fc_steps; exact hJs () mi ⟨rfl, Or.inr hcl_in⟩
                          · have hval_ff : s.core.vals[cl.toNat]?.getD 0#8 = 0xFF#8 := by
                              have hne0 : s.core.vals[cl.toNat]?.getD 0#8 ≠ 0#8 := by
                                intro h0
                                have hidx : ((s.core.arena[((s.core.wstk[(p + 1).toNat]'
                                    hp1_w).setWidth 64 + 3 + j.setWidth 64).toNat]'
                                    hcr3j_w).setWidth 64).toNat = cl.toNat := by
                                  rw [hcl_eq, bv_zext32_toNat]
                                change (BitVec.signExtend 32 (s.core.vals[_]'_) == 0#32) =
                                  false at hc
                                rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
                                rw [list_getElem_congr hidx _ (by omega), h0] at hc; cases hc
                              rcases hw.vals_domain cl.toNat hcl_lt with hv | hv | hv
                              · exact absurd hv hne0
                              · exact absurd hv hne1_cl
                              · exact hv
                            fc_steps; exact hJs () mi ⟨rfl, Or.inl hval_ff⟩
                    · have hj_ge : sz_bv.toNat ≤ j.toNat := by
                        rw [list_getElem_congr hcr2_n hcr2_w hcr2_arr] at hc
                        simp only [BitVec.ult, decide_eq_false_iff_not] at hc
                        exact Nat.le_of_not_lt hc
                      have hj_eq : j.toNat = sz_bv.toNat := by omega
                      rw [hj_eq] at hcov_j; fc_steps
                      exact hB2 (true, j, ()) mi ⟨rfl, fun _ => hcov_j⟩
                  · intro _ L2 _ hL2; fc_steps
                    exact hL2 (sz_bv.toNat - 0) (0#32, ()) mi
                      ⟨rfl, Nat.zero_le _, rfl, fun _ h => by simp at h⟩
        · fc_steps; exact hB (false, p, ()) mi ⟨rfl, fun h => by cases h⟩
      · intro _ L _ hL; fc_steps
        refine hL ((off + wsz).toNat - off.toNat) (off, ()) mi ⟨rfl, by omega, rfl, ?_⟩
        simpa [hend_n, hoff_n, hwsz_n] using hslice0

/-! ## 4. `full_cong_extract_xor_k_wp` (`fidCongExtractXorKSpec`) -/

private theorem xor_k_emit_gate_pure {maxA : Nat} (hmax4 : 4 ≤ maxA)
    {F_cur : List (List Nat)} {cur_vars np_base : Nat}
    {k j neg_p base_j lhs_j mword_j : BitVec 32} {g_cur : BitVec 64}
    {s_ws2 base stj_scr scr_c tmp_s : List (BitVec 32)}
    (hk3 : 3 ≤ k.toNat) (hk5 : k.toNat ≤ 5) (hkcv : k.toNat ≤ cur_vars)
    (hj_lt : j.toNat < k.toNat) (hk_cases : k = 3#32 ∨ k = 4#32 ∨ k = 5#32)
    (hbase_len : base.length = k.toNat)
    (hbase_get : ∀ b < k.toNat, base[b]?.getD 0#32 = s_ws2[b]?.getD 0#32)
    (hbase_lt : ∀ i < k.toNat, (s_ws2[i]?.getD 0#32).toNat < 2 * cur_vars)
    (hbase_cl' : (cnfOfClauses F_cur).EntailsClause (cnfClause (base.map BitVec.toNat)))
    (heven' : ∀ mask : BitVec 32, 1 ≤ mask.toNat → mask.toNat < 2 ^ k.toNat →
      m6MaskParity mask k.toNat = 0#32 →
      (cnfOfClauses F_cur).EntailsClause (cnfClause ((List.range k.toNat).map
        fun b => ((base[b]?.getD 0#32) ^^^ ((mask >>> b) &&& 1#32)).toNat)))
    (hnp_base : np_base = (List.range k.toNat).foldl
      (fun acc b => acc ^^^ ((base[b]?.getD 0#32).toNat % 2)) 0)
    (hsign_eq' : BitVec.ofNat 32 (1 ^^^ (np_base % 2)) = 1#32 ^^^ (neg_p &&& 1#32))
    (harity_n : (k - 1#32).toNat = k.toNat - 1)
    (hbj_eq : base_j = s_ws2[j.toNat]?.getD 0#32)
    (hlhs_def : lhs_j = (base_j &&& ~~~1#32) ||| (1#32 ^^^ (neg_p &&& 1#32)))
    (hmw_def : mword_j = (1#32 <<< 28) ||| (k - 1#32))
    (hscrc_l : scr_c.length = stj_scr.length) (htmpi_l : tmp_s.length ≥ (k - 1#32).toNat)
    (hpc_pref : ∀ idx < g_cur.toNat, scr_c[idx]? = stj_scr[idx]?)
    (hpc0 : scr_c[g_cur.toNat]? = some lhs_j)
    (hpc1 : scr_c[g_cur.toNat + 1]? = some mword_j)
    (hpc_rhs : ∀ q < (k - 1#32).toNat, scr_c[g_cur.toNat + 2 + q]? = tmp_s[q]?)
    (hperm_all : List.Perm (tmp_s.take (k - 1#32).toNat)
      (((List.range k.toNat).filter (· != j.toNat)).map fun idx =>
        ((s_ws2[idx]?.getD 0#32) &&& ~~~1#32)))
    (hgcur_len : g_cur.toNat + (k.toNat + 1) ≤ stj_scr.length)
    (hseqj : FidGateSeqOk maxA F_cur cur_vars stj_scr g_cur.toNat 0) :
    FidGateSeqOk maxA F_cur cur_vars scr_c (g_cur.toNat + (k.toNat + 1)) 0 := by
  have hmword_tag : (mword_j >>> 28).toNat = 1 := by
    rw [hmw_def]; rcases hk_cases with h | h | h <;> rw [h] <;> decide
  have hmword_ar : (mword_j &&& 0xFF#32).toNat = k.toNat - 1 := by
    rw [hmw_def]; rcases hk_cases with h | h | h <;> rw [h] <;> decide
  have hlhs_eq : lhs_j =
      ((base[j.toNat]?.getD 0#32) &&& ~~~1#32) ||| BitVec.ofNat 32 (1 ^^^ (np_base % 2)) := by
    rw [hlhs_def, hbj_eq, ← hbase_get j.toNat hj_lt, hsign_eq']
  have hlhs_bit : (1#32 ^^^ (neg_p &&& 1#32)) = ((1#32 ^^^ (neg_p &&& 1#32)) &&& 1#32) := by
    rw [← hsign_eq']
    rcases Nat.mod_two_eq_zero_or_one np_base with hn | hn <;> simp [hn] <;> decide
  have hlhs_lt : lhs_j.toNat < 2 * cur_vars := by
    have hlt_b : base_j.toNat < 2 * cur_vars := by rw [hbj_eq]; exact hbase_lt j.toNat hj_lt
    have hmod_lt : (1#32 ^^^ (neg_p &&& 1#32)).toNat % 2 < 2 := Nat.mod_lt _ (by decide)
    have hn : lhs_j.toNat =
        2 * (base_j.toNat / 2) + (1#32 ^^^ (neg_p &&& 1#32)).toNat % 2 := by
      rw [hlhs_def]; conv => lhs; rhs; rw [hlhs_bit]
      exact bv32_even_or_bit_toNat base_j _
    omega
  have harity_eq : (mword_j &&& 0xFF#32).toNat = (k - 1#32).toNat := by omega
  have hrhs_lt : ∀ r < (mword_j &&& 0xFF#32).toNat, ∃ v : BitVec 32,
      scr_c[g_cur.toNat + 2 + r]? = some v ∧ v.toNat < 2 * cur_vars := by
    intro r hr
    have hr_ar : r < (k - 1#32).toNat := by omega
    have hget := hpc_rhs r hr_ar
    have hr_tmps : r < tmp_s.length := by omega
    rw [List.getElem?_eq_getElem hr_tmps] at hget
    have hmem_tk : (tmp_s.take (k - 1#32).toNat)[r]'(
        by rw [List.length_take]; exact Nat.lt_min.mpr ⟨hr_ar, hr_tmps⟩) ∈
        tmp_s.take (k - 1#32).toNat := List.getElem_mem _
    rw [List.getElem_take] at hmem_tk
    have hmem_f := hperm_all.mem_iff.mp hmem_tk
    rw [List.mem_map] at hmem_f; obtain ⟨idx, hidx_f, hidx_eq⟩ := hmem_f
    have hidx_k : idx < k.toNat := List.mem_range.mp (List.mem_filter.mp hidx_f).1
    have hlt_i := hbase_lt idx hidx_k
    have hn_even : ((s_ws2[idx]?.getD 0#32) &&& ~~~1#32).toNat =
        2 * ((s_ws2[idx]?.getD 0#32).toNat / 2) := m6_bv32_and_not1_toNat _
    refine ⟨tmp_s[r]'hr_tmps, hget, ?_⟩; rw [← hidx_eq]; omega
  have hslc_eq_tmps :
      (scr_c.drop (g_cur.toNat + 2)).take (k - 1#32).toNat = tmp_s.take (k - 1#32).toNat := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, hscrc_l]
      rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
    · intro q hq1 _
      simp only [List.length_take, List.length_drop, hscrc_l] at hq1
      have hqk : q < (k - 1#32).toNat := by omega
      simp only [List.getElem_take, List.getElem_drop]
      have hget := hpc_rhs q hqk
      rw [List.getElem?_eq_getElem (by omega : g_cur.toNat + 2 + q < scr_c.length),
        List.getElem?_eq_getElem (by omega : q < tmp_s.length)] at hget
      exact Option.some.inj hget
  have hrhs_map_eq : ((((List.range k.toNat).filter (· != j.toNat)).map
      fun idx => (s_ws2[idx]?.getD 0#32) &&& ~~~1#32).map BitVec.toNat) =
      (((List.range k.toNat).filter (· != j.toNat)).map fun i =>
        ((base[i]?.getD 0#32) &&& ~~~1#32).toNat) := by
    rw [List.map_map]; refine List.map_congr_left fun i hi => ?_
    have hi_k : i < k.toNat := List.mem_range.mp (List.mem_filter.mp hi).1
    dsimp only [Function.comp_def]; rw [hbase_get i hi_k]
  have hperm_rhs : List.Perm
      (((scr_c.drop (g_cur.toNat + 2)).take (mword_j &&& 0xFF#32).toNat).map BitVec.toNat)
      (((List.range k.toNat).filter (· != j.toNat)).map fun i =>
        ((base[i]?.getD 0#32) &&& ~~~1#32).toNat) := by
    rw [harity_eq, hslc_eq_tmps]; exact hrhs_map_eq ▸ hperm_all.map BitVec.toNat
  have hxor_j : XorListGateDef (cnfOfClauses F_cur) lhs_j.toNat
      (((scr_c.drop (g_cur.toNat + 2)).take (mword_j &&& 0xFF#32).toNat).map BitVec.toNat) := by
    have hbase_xor := xorListGateDef_of_all_even_clauses hk5 hbase_len hbase_cl' heven'
      hnp_base hj_lt
    intro α hα; rw [hlhs_eq, xorEvalList_perm α hperm_rhs]; exact hbase_xor α hα
  have hgat_j : FidGateAt maxA F_cur cur_vars scr_c (g_cur.toNat + (k.toNat + 1)) g_cur.toNat :=
    ⟨lhs_j, mword_j, hpc0, hpc1, hlhs_lt, by omega, by omega, by omega,
      hrhs_lt, Or.inr (Or.inl ⟨hmword_tag, by omega, by omega, hxor_j⟩)⟩
  refine fidGateSeqOk_append_gate hpc_pref hseqj (.step hgat_j ?_) (by omega)
  rw [hpc1, Option.getD_some, hmword_ar,
    show g_cur.toNat + 2 + (k.toNat - 1) = g_cur.toNat + (k.toNat + 1) by omega]
  exact FidGateSeqOk.done

theorem full_cong_extract_xor_k_wp (Γ : Env)
    (hSort : ∀ args m Q X, FullCongSpecs.fullSortU32Spec args m Q X →
      Γ "full_sort_u32" [i64, i32] [] args m Q X)
    (hHasClK : ∀ args m Q X, m6CongHasClauseKSpec args m Q X →
      Γ "full_cong_has_clause_k" [i64, i32] [.bool] args m Q X)
    (hEmitXor4 : ∀ args m Q X, fidCongEmitXor4Spec args m Q X →
      Γ "full_cong_emit_xor4" [i64, i64, i32, i32, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fidCongExtractXorKSpec args m Q X →
      Func.wp Γ full_cong_extract_xor_k_body args m Q X := by
  rintro ⟨h, k, neg_p, g_len, g_cap, ⟨⟩⟩ m0 Q X
    ⟨maxA, c, F0, F_cur, s, R, hmax4, hmax64, rfl, hlen, hw, hmk, hnd, hcl0, hk3, hk5, hkcv,
     hgl_le, hgc_le, hseq0, hbase_lt, hnp, hbase_cl, hm0, hQ⟩
  have hmx := c.hmaxv; have hsc := c.hscr; unfold dimacsBound at hmx hsc
  have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have hcv_le := hcl.cur_vars_le; have htmpl := hcl.tmp_len_arr
  have hwvl := hcl.wvec_len; have hws1l := hsl.work_stk1_len; have hws2l := hsl.work_stk2_len
  have hscrl := hsl.scratch_buf_len
  have hret_same : ∀ (st : FullState) (m : Mem 64),
      st.LengthsOk c →
      { st.core with tmp := s.core.tmp, lit_mark := s.core.lit_mark } = s.core →
      { st.scratch with scratch_buf := s.scratch.scratch_buf } = s.scratch →
      FullLitMarksClear c st →
      (∀ idx < g_len.toNat, st.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) →
      FidGateSeqOk maxA F_cur s.core.cur_vars st.scratch.scratch_buf g_len.toNat 0 →
      (FullMem c st ⋆ R) m → Q (g_len, ()) m :=
    fun st m hlen_t hc_t hs_t hmk_t hpref hseq hmt =>
      hQ g_len st m hlen_t hc_t hs_t hmk_t (Nat.le_refl _) hgl_le hpref hseq hmt
  fc_split_fast
  · exfalso
    have : k.toNat < 3 := by simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
    omega
  clear hc; fc_split_fast
  · exfalso
    have : 5 < k.toNat := by simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
    omega
  clear hc; fc_split_fast
  · exfalso
    have : s.core.cur_vars < k.toNat := by
      simp only [BitVec.ult, decide_eq_true_eq] at hc; bv_omega
    omega
  · clear hc; fc_split_fast
    · m3_let; exact hret_same s m0 hlen rfl rfl hmk (fun _ _ => rfl) hseq0 hm0
    · have hmul_le : k.toNat * (k.toNat + 1) ≤ 30 := Nat.mul_le_mul hk5 (by omega : k.toNat + 1 ≤ 6)
      have hneed_le : g_len.toNat + k.toNat * (k.toNat + 1) ≤ g_cap.toNat := by
        have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
        have hkm : ((k.setWidth 64) * ((k + 1#32).setWidth 64)).toNat =
            k.toNat * (k.toNat + 1) := by
          rw [BitVec.toNat_mul, bv_zext32_toNat, bv_zext32_toNat, hk1]
          exact Nat.mod_eq_of_lt (by omega)
        have hsum : (g_len + (k.setWidth 64) * ((k + 1#32).setWidth 64)).toNat =
            g_len.toNat + k.toNat * (k.toNat + 1) := by
          rw [BitVec.toNat_add, hkm]; exact Nat.mod_eq_of_lt (by omega)
        simp only [BitVec.ult, decide_eq_false_iff_not] at hc
        have hle : (g_len + (k.setWidth 64) * ((k + 1#32).setWidth 64)).toNat ≤ g_cap.toNat :=
          Nat.le_of_not_lt fun hlt => hc (BitVec.lt_def.mpr hlt)
        rwa [hsum] at hle
      clear hc; fc_steps
      refine wp_loop_inv (ts := [i32, i32])
        (fun (_mx, j, ()) mj => mj = m0 ∧ j.toNat ≤ k.toNat ∧
          ∀ a b, a < b → b < j.toNat →
            (s.scratch.work_stk2[a]?.getD 0#32).toNat / 2 ≠
              (s.scratch.work_stk2[b]?.getD 0#32).toNat / 2)
        (fun (_, j, ()) _ => k.toNat - j.toNat)
        (fun J1 hJ1 => by
          m3_let; exact hJ1 (0#32, 0#32, ()) m0
            ⟨rfl, Nat.zero_le _, fun _ _ _ h => by simp at h⟩)
        (fun J1 (mx, j, ()) mj ⟨hmj, hj_le, hdis_j⟩ ih1 => ?_)
      subst mj; fc_split_fast
      · have hj_lt : j.toNat < k.toNat := by
          simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
        have hj1_n : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
        have hj_ws2 : (j.setWidth 64).toNat < s.scratch.work_stk2.length := by
          rw [hws2l, bv_zext32_toNat]; omega
        let bj := s.scratch.work_stk2[(j.setWidth 64).toNat]'hj_ws2
        fc_to_group; refine wp_join_group (ts := [i32]) (fun (_mx', ()) mj' => mj' = m0) ?_ ?_
        · rintro _ ⟨mx', ⟨⟩⟩ mj' hmj'
          subst mj'; m3_let
          refine wp_loop_inv (ts := [i32])
            (fun (bi, ()) mi => mi = m0 ∧ bi.toNat ≤ j.toNat ∧
              ∀ a < bi.toNat,
                (s.scratch.work_stk2[a]?.getD 0#32).toNat / 2 ≠
                  (s.scratch.work_stk2[j.toNat]?.getD 0#32).toNat / 2)
            (fun (bi, ()) _ => j.toNat - bi.toNat)
            (fun Ji hJi => by
              m3_let; exact hJi (0#32, ()) m0 ⟨rfl, Nat.zero_le _, fun _ h => by simp at h⟩)
            (fun Ji (bi, ()) mi ⟨hmi, hbi_le, hdis_bi⟩ ihi => ?_)
          subst mi; fc_split_fast
          · have hbi_lt : bi.toNat < j.toNat := by
              simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
            have hbi1_n : (bi + 1#32).toNat = bi.toNat + 1 := by bv_omega
            have hbi_ws2 : (bi.setWidth 64).toNat < s.scratch.work_stk2.length := by
              rw [hws2l, bv_zext32_toNat]; omega
            fc_split_fast
            · m3_let; exact hret_same s m0 hlen rfl rfl hmk (fun _ _ => rfl) hseq0 hm0
            · have hne_bi : (s.scratch.work_stk2[bi.toNat]?.getD 0#32).toNat / 2 ≠
                  (s.scratch.work_stk2[j.toNat]?.getD 0#32).toNat / 2 := by
                intro he
                have hbj_j : bj = s.scratch.work_stk2[j.toNat]'(by omega) :=
                  list_getElem_congr (bv_zext32_toNat j) hj_ws2 (by omega)
                have h1 : (s.scratch.work_stk2[(bi.setWidth 64).toNat]'hbi_ws2).toNat / 2 =
                    bj.toNat / 2 := by
                  rw [list_getElem_congr (bv_zext32_toNat bi) hbi_ws2 (by omega), hbj_j]
                  rw [List.getElem?_eq_getElem (by omega : bi.toNat < s.scratch.work_stk2.length),
                    Option.getD_some,
                    List.getElem?_eq_getElem (by omega : j.toNat < s.scratch.work_stk2.length),
                    Option.getD_some] at he
                  exact he
                have h2 : (s.scratch.work_stk2[(bi.setWidth 64).toNat]'hbi_ws2 >>> 1) =
                    (bj >>> 1) := by
                  apply BitVec.eq_of_toNat_eq
                  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight,
                    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.pow_one]
                  exact h1
                rw [beq_iff_eq.mpr h2] at hc; cases hc
              m3_let; refine ihi (bi + 1#32, ()) m0 (by dsimp only; omega)
                ⟨rfl, by omega, fun a ha => ?_⟩
              rw [hbi1_n] at ha
              rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ha) with hlt | heq
              · exact hdis_bi a hlt
              · subst heq; exact hne_bi
          · have hbi_eq : bi.toNat = j.toNat := by
              simp only [BitVec.ult, decide_eq_false_iff_not] at hc; omega
            rw [hbi_eq] at hdis_bi
            m3_let; refine ih1 (mx', j + 1#32, ()) m0 (by dsimp only; omega)
              ⟨rfl, by omega, fun a b hab hb => ?_⟩
            rw [hj1_n] at hb
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hb) with hlt | heq
            · exact hdis_j a b hab hlt
            · subst heq; exact hdis_bi a hab
        · intro Jmx hJmx; fc_split_fast
          · m3_let; exact hJmx (bj, ()) m0 rfl
          · m3_let; exact hJmx (mx, ()) m0 rfl
      · have hj_eq : j.toNat = k.toNat := by
          simp only [BitVec.ult, decide_eq_false_iff_not] at hc; omega
        rw [hj_eq] at hdis_j; clear hc
        m3_let
        refine wp_loop_inv (ts := [i32])
          (fun (j, ()) mj2 => mj2 = m0 ∧ j.toNat ≤ k.toNat)
          (fun (j, ()) _ => k.toNat - j.toNat)
          (fun J2 hJ2 => by m3_let; exact hJ2 (0#32, ()) m0 ⟨rfl, Nat.zero_le _⟩)
          (fun J2 (j, ()) mj2 ⟨hmj2, hj_le⟩ ih2 => ?_)
        subst mj2; fc_split_fast
        · have hj_lt : j.toNat < k.toNat := by
            simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
          have hj1_n : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
          have hj_ws2 : (j.setWidth 64).toNat < s.scratch.work_stk2.length := by
            rw [hws2l, bv_zext32_toNat]; omega
          fc_to_group; refine wp_join_group (ts := []) (fun () mj2' => mj2' = m0) ?_ ?_
          · rintro _ ⟨⟩ mj2' hmj2'
            subst mj2'; m3_let; exact ih2 (j + 1#32, ()) m0 (by dsimp only; omega) ⟨rfl, by omega⟩
          · intro J2n hJ2n; fc_split_fast
            · fc_split_fast
              · m3_let; exact hret_same s m0 hlen rfl rfl hmk (fun _ _ => rfl) hseq0 hm0
              · m3_let; exact hJ2n () m0 rfl
            · m3_let; exact hJ2n () m0 rfl
        · clear hc; m3_let
          refine wp_loop_inv (ts := [i32])
            (fun (j, ()) mj3 => mj3 = m0 ∧ j.toNat ≤ k.toNat)
            (fun (j, ()) _ => k.toNat - j.toNat)
            (fun J3 hJ3 => by fc_let; exact hJ3 (0#32, ()) m0 ⟨rfl, Nat.zero_le _⟩)
            (fun J3 (j, ()) mj3 ⟨hmj3, hj_le⟩ ih3 => ?_)
          subst mj3; fc_split_fast
          · have hj_lt : j.toNat < k.toNat := by
              simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
            have hj1_n : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
            have hj_ws2 : (j.setWidth 64).toNat < s.scratch.work_stk2.length := by
              rw [hws2l, bv_zext32_toNat]; omega
            have hbj_lt : (s.scratch.work_stk2[(j.setWidth 64).toNat]'hj_ws2).toNat <
                2 * s.core.cur_vars := by
              have h := hbase_lt j.toNat hj_lt
              rw [List.getElem?_eq_getElem (by omega : j.toNat < s.scratch.work_stk2.length),
                Option.getD_some] at h
              rwa [list_getElem_congr (bv_zext32_toNat j) hj_ws2 (by omega)]
            let bj := s.scratch.work_stk2[(j.setWidth 64).toNat]'hj_ws2
            have hbj_n' : bj.toNat < 2 * s.core.cur_vars := hbj_lt
            let pl := bj &&& ~~~1#32
            let nl := pl ||| 1#32
            have hpl_n : pl.toNat = 2 * (bj.toNat / 2) := m6_bv32_and_not1_toNat bj
            have hpl_lt : pl.toNat < 2 * s.core.cur_vars := by
              rw [hpl_n]; exact Nat.lt_of_le_of_lt (Nat.mul_div_le bj.toNat 2) hbj_n'
            have hnl_n : nl.toNat = pl.toNat + 1 := by
              have hb1 : (1#32 : BitVec 32) = (1#32 &&& 1#32) := by decide
              have h := bv32_even_or_bit_toNat bj 1#32
              change ((bj &&& ~~~1#32) ||| (1#32 &&& 1#32)).toNat =
                2 * (bj.toNat / 2) + (1#32).toNat % 2 at h
              rw [← hb1] at h; change nl.toNat = 2 * (bj.toNat / 2) + 1 at h; omega
            have hnl_lt : nl.toNat < 2 * s.core.cur_vars := by
              have hpl_ev : pl.toNat % 2 = 0 := by rw [hpl_n]; omega
              omega
            have hpl_wv : (pl.setWidth 64 <<< (1 : Nat) + 1#64).toNat < s.core.wvec.length := by
              rw [BitVec.toNat_add, FullCongHelpers.bv64_shl1_toNat, bv_zext32_toNat,
                show (1#64 : BitVec 64).toNat = 1 from rfl]
              have : 2 * pl.toNat < 2 ^ 64 := by omega
              rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega)]; omega
            have hpl_wv_se :
                (pl.setWidth 64 <<< ((1#32 : BitVec 32).signExtend 64).toNat + 1#64).toNat <
                  s.core.wvec.length := hpl_wv
            have hpl_wv_bv :
                (pl.setWidth 64 <<< ((1#32 : BitVec 32).signExtend 64) + 1#64).toNat <
                  s.core.wvec.length := hpl_wv
            have hnl_wv : (nl.setWidth 64 <<< (1 : Nat) + 1#64).toNat < s.core.wvec.length := by
              rw [BitVec.toNat_add, FullCongHelpers.bv64_shl1_toNat, bv_zext32_toNat,
                show (1#64 : BitVec 64).toNat = 1 from rfl]
              have : 2 * nl.toNat < 2 ^ 64 := by omega
              rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega)]; omega
            have hnl_wv_se :
                (nl.setWidth 64 <<< ((1#32 : BitVec 32).signExtend 64).toNat + 1#64).toNat <
                  s.core.wvec.length := hnl_wv
            have hnl_wv_bv :
                (nl.setWidth 64 <<< ((1#32 : BitVec 32).signExtend 64) + 1#64).toNat <
                  s.core.wvec.length := hnl_wv
            have hpx_ws1 : ((pl ^^^ 1#32).setWidth 64).toNat < s.scratch.work_stk1.length := by
              rw [bv_zext32_toNat, FullCongHelpers.bv32_xor1_eq_litNeg, hws1l]
              exact Nat.lt_of_lt_of_le (litNeg_lt_two_mul hpl_lt) (by omega)
            have hnx_ws1 : ((nl ^^^ 1#32).setWidth 64).toNat < s.scratch.work_stk1.length := by
              rw [bv_zext32_toNat, FullCongHelpers.bv32_xor1_eq_litNeg, hws1l]
              exact Nat.lt_of_lt_of_le (litNeg_lt_two_mul hnl_lt) (by omega)
            fc_to_group; refine wp_join_group (ts := [i32]) (fun (_, ()) mlp => mlp = m0) ?_ ?_
            · rintro _ ⟨lp, ⟨⟩⟩ mlp hmlp
              subst mlp; fc_to_group
              refine wp_join_group (ts := [i32]) (fun (_, ()) mln => mln = m0) ?_ ?_
              · rintro _ ⟨ln, ⟨⟩⟩ mln hmln
                subst mln; fc_split_fast
                · m3_let; exact hret_same s m0 hlen rfl rfl hmk (fun _ _ => rfl) hseq0 hm0
                · fc_split_fast
                  · m3_let; exact hret_same s m0 hlen rfl rfl hmk (fun _ _ => rfl) hseq0 hm0
                  · m3_let; exact ih3 (j + 1#32, ()) m0 (by dsimp only; omega) ⟨rfl, by omega⟩
              · intro Jln hJln; fc_split_fast
                · m3_let; exact hJln (_, ()) m0 rfl
                · m3_let; exact hJln (0#32, ()) m0 rfl
            · intro Jlp hJlp; fc_split_fast
              · m3_let; exact hJlp (_, ()) m0 rfl
              · m3_let; exact hJlp (0#32, ()) m0 rfl
          · clear hc; m3_let
            have hk_cases : k = 3#32 ∨ k = 4#32 ∨ k = 5#32 := by
              have h : k.toNat = 3 ∨ k.toNat = 4 ∨ k.toNat = 5 := by omega
              rcases h with h | h | h
              · left; exact BitVec.eq_of_toNat_eq h
              · right; left; exact BitVec.eq_of_toNat_eq h
              · right; right; exact BitVec.eq_of_toNat_eq h
            have hlim_n : ((1 : BitVec 32) <<< (k.toNat % 32)).toNat = 2 ^ k.toNat := by
              rcases hk_cases with h | h | h <;> rw [h] <;> decide
            refine wp_loop_inv (ts := [i32])
              (fun (mask, ()) m4 => ∃ st4 : FullState,
                1 ≤ mask.toNat ∧ mask.toNat ≤ 2 ^ k.toNat ∧
                st4.LengthsOk c ∧
                { st4.core with tmp := s.core.tmp, lit_mark := s.core.lit_mark } = s.core ∧
                st4.scratch = s.scratch ∧ FullLitMarksClear c st4 ∧
                (∀ m' : BitVec 32, 1 ≤ m'.toNat → m'.toNat < mask.toNat →
                  m6MaskParity m' k.toNat = 0#32 →
                  (cnfOfClauses F_cur).EntailsClause (cnfClause ((List.range k.toNat).map
                    fun b => ((s.scratch.work_stk2[b]?.getD 0#32) ^^^
                      ((m' >>> b) &&& 1#32)).toNat))) ∧
                (FullMem c st4 ⋆ R) m4)
              (fun (mask, ()) _ => 2 ^ k.toNat - mask.toNat)
              (fun J4 hJ4 => by
                fc_let; exact hJ4 (1#32, ()) m0
                  ⟨s, by decide, Nat.one_le_two_pow, hlen, rfl, rfl, hmk,
                   fun _ h1 h2 => by
                     rw [show (1#32 : BitVec 32).toNat = 1 from rfl] at h2; omega, hm0⟩)
              (fun J4 (mask, ()) m4 ⟨st4, hm1, hmle, hlen4, hc4, hs4, hmk4, heven_m, hm4⟩
                ih4 => ?_)
            fc_split_fast
            · have hm_lt : mask.toNat < 2 ^ k.toNat := by
                simp only [BitVec.ult, decide_eq_true_eq] at hc; rwa [hlim_n] at hc
              have hm1_n : (mask + 1#32).toNat = mask.toNat + 1 := by bv_omega
              clear hc; fc_let
              refine wp_loop_inv (ts := [i32, i32])
                (fun (pop, b, ()) mpop => mpop = m4 ∧ b.toNat ≤ k.toNat ∧
                  pop = m6MaskParity mask b.toNat)
                (fun (_, b, ()) _ => k.toNat - b.toNat)
                (fun Jp hJp => by
                  fc_let; exact hJp (0#32, 0#32, ()) m4 ⟨rfl, Nat.zero_le _, rfl⟩)
                (fun Jp (pop, b, ()) mpop ⟨hmpop, hb_le, hpop_eq⟩ ihp => ?_)
              subst mpop; fc_split_fast
              · have hb_lt : b.toNat < k.toNat := by
                  simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                have hb1_n : (b + 1#32).toNat = b.toNat + 1 := by bv_omega
                fc_let; refine ihp (_, b + 1#32, ()) m4 (by dsimp only; omega)
                  ⟨rfl, by omega, ?_⟩
                rw [hb1_n, m6MaskParity_succ, hpop_eq, Nat.mod_eq_of_lt (by omega : b.toNat < 32)]
                rfl
              · have hb_eq : b.toNat = k.toNat := by
                  simp only [BitVec.ult, decide_eq_false_iff_not] at hc; omega
                rw [hb_eq] at hpop_eq; clear hc
                fc_to_group; refine wp_join_group (ts := [i32])
                  (fun _ m4' => ∃ st4' : FullState,
                    st4'.LengthsOk c ∧
                    { st4'.core with tmp := s.core.tmp, lit_mark := s.core.lit_mark } = s.core ∧
                    st4'.scratch = s.scratch ∧ FullLitMarksClear c st4' ∧
                    (∀ m' : BitVec 32, 1 ≤ m'.toNat → m'.toNat < (mask + 1#32).toNat →
                      m6MaskParity m' k.toNat = 0#32 →
                      (cnfOfClauses F_cur).EntailsClause (cnfClause ((List.range k.toNat).map
                        fun b => ((s.scratch.work_stk2[b]?.getD 0#32) ^^^
                          ((m' >>> b) &&& 1#32)).toNat))) ∧
                    (FullMem c st4' ⋆ R) m4')
                  ?_ ?_
                · rintro _ ⟨_, ⟨⟩⟩ m4' ⟨st4', hlen4', hc4', hs4', hmk4', heven', hm4'⟩
                  m3_let; exact ih4 (mask + 1#32, ()) m4' (by dsimp only; omega)
                    ⟨st4', by omega, by omega, hlen4', hc4', hs4', hmk4', heven', hm4'⟩
                · intro Jm4 hJm4; fc_split_fast
                  · have hpar0 : m6MaskParity mask k.toNat = 0#32 := by
                      rw [← hpop_eq]; exact beq_iff_eq.mp hc
                    clear hc; fc_steps
                    refine wp_loop_inv (ts := [i32])
                      (fun (bi, ()) mbi => ∃ tmpi : List (BitVec 32),
                        tmpi.length = c.max_vars ∧ bi.toNat ≤ k.toNat ∧
                        (∀ q < bi.toNat, tmpi[q]?.getD 0#32 =
                          ((s.scratch.work_stk2[q]?.getD 0#32) ^^^ ((mask >>> q) &&& 1#32))) ∧
                        (FullMem c { st4 with core := { st4.core with tmp := tmpi } } ⋆ R) mbi)
                      (fun (bi, ()) _ => k.toNat - bi.toNat)
                      (fun Jbi hJbi => by
                        fc_let; exact hJbi (0#32, ()) m4
                          ⟨st4.core.tmp, hlen4.core_ok.tmp_len_arr, Nat.zero_le _,
                           fun _ h => by simp at h, hm4⟩)
                      (fun Jbi (bi, ()) mbi ⟨tmpi, htmpl_i, hbi_le, htmp_bi, hmbi⟩ ihbi => ?_)
                    fc_split_fast
                    · have hbi_lt : bi.toNat < k.toNat := by
                        simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                      have hbi1_n : (bi + 1#32).toNat = bi.toNat + 1 := by bv_omega
                      have hbi_ws2 :
                          (bi.setWidth 64).toNat < st4.scratch.work_stk2.length := by
                        rw [hs4, hws2l, bv_zext32_toNat]; omega
                      have hbi_tmp : (bi.setWidth 64).toNat < tmpi.length := by
                        rw [bv_zext32_toNat]; omega
                      fc_steps
                      let v_bi := (st4.scratch.work_stk2[(bi.setWidth 64).toNat]'hbi_ws2) ^^^
                        ((mask >>> (bi.toNat % 32)) &&& 1#32)
                      let tmpi' := tmpi.set (bi.setWidth 64).toNat v_bi
                      have hbi_z : (bi.setWidth 64).toNat = bi.toNat := bv_zext32_toNat bi
                      have hget_st4 :
                          st4.scratch.work_stk2[(bi.setWidth 64).toNat]'hbi_ws2 =
                            s.scratch.work_stk2[bi.toNat]'(by omega) :=
                        (list_getElem_congr hbi_z hbi_ws2 (by omega :
                            bi.toNat < st4.scratch.work_stk2.length)).trans (by simp [hs4])
                      have hv_bi : v_bi = ((s.scratch.work_stk2[bi.toNat]?.getD 0#32) ^^^
                          ((mask >>> bi.toNat) &&& 1#32)) := by
                        dsimp only [v_bi]
                        rw [Nat.mod_eq_of_lt (by omega : bi.toNat < 32), hget_st4,
                          List.getElem?_eq_getElem (by omega :
                            bi.toNat < s.scratch.work_stk2.length), Option.getD_some]
                      refine ihbi (bi + 1#32, ()) m (by dsimp only; omega)
                        ⟨tmpi', by simp [tmpi', htmpl_i], by omega, fun q hq => ?_,
                         by dsimp only [tmpi', v_bi]; exact hm⟩
                      rw [hbi1_n] at hq
                      by_cases hq_b : q = bi.toNat
                      · subst hq_b; dsimp only [tmpi']
                        rw [hbi_z, List.getElem?_set_self (by omega), Option.getD_some, hv_bi]
                      · dsimp only [tmpi']
                        rw [hbi_z, List.getElem?_set_ne (Ne.symm hq_b)]
                        exact htmp_bi q (by omega)
                    · have hbi_eq : bi.toNat = k.toNat := by
                        simp only [BitVec.ult, decide_eq_false_iff_not] at hc; omega
                      rw [hbi_eq] at htmp_bi
                      let st4b : FullState := { st4 with core := { st4.core with tmp := tmpi } }
                      have hlen4b : st4b.LengthsOk c :=
                        ⟨{ hlen4.core_ok with tmp_len_arr := htmpl_i }, hlen4.scratch_ok⟩
                      have hst4b_core :
                          st4b.core =
                            { s.core with tmp := tmpi, lit_mark := st4.core.lit_mark } := by
                        dsimp only [st4b]; rw [← hc4]
                      have hw4b : FullWitnessInv c F0 F_cur st4b.core :=
                        hst4b_core ▸ fullWitnessInv_with_tmp_lm hw tmpi st4.core.lit_mark
                      have hnd4b : FullArenaVarsNodup st4b :=
                        fullArenaVarsNodup_of_eq hnd (by rw [hst4b_core]) (by rw [hst4b_core])
                      have hcl4b : st4b.core.cur_level = 0 := by rw [hst4b_core]; exact hcl0
                      have hkcv4b : k.toNat ≤ st4b.core.cur_vars := by
                        rw [hst4b_core]; exact hkcv
                      have htmp_lt4b : ∀ i < k.toNat,
                          (st4b.core.tmp[i]?.getD 0#32).toNat < 2 * st4b.core.cur_vars := by
                        intro q hq; rw [hst4b_core]; dsimp only; rw [htmp_bi q hq]
                        exact (xor_bit01_lt_div2 _ _ (hbase_lt q hq)).1
                      have htmp_dis4b : ∀ a b, a < b → b < k.toNat →
                          (st4b.core.tmp[a]?.getD 0#32).toNat / 2 ≠
                            (st4b.core.tmp[b]?.getD 0#32).toNat / 2 := by
                        intro a b hab hb
                        show (tmpi[a]?.getD 0#32).toNat / 2 ≠ (tmpi[b]?.getD 0#32).toNat / 2
                        rw [htmp_bi a (by omega), htmp_bi b hb,
                          (xor_bit01_lt_div2 _ (mask >>> a) (hbase_lt a (by omega))).2,
                          (xor_bit01_lt_div2 _ (mask >>> b) (hbase_lt b hb)).2]
                        exact hdis_j a b hab hb
                      fc_steps; c0_call hHasClK
                      refine ⟨c, F0, F_cur, st4b, R, rfl, hlen4b, hw4b, hmk4, hnd4b, hcl4b,
                        hk3, hk5, hkcv4b, htmp_lt4b, htmp_dis4b, hmbi,
                        fun ok st5 m5 hlen5 h5c h5s hmk5 hok hm5 => ?_⟩
                      have hc5 :
                          { st5.core with tmp := s.core.tmp, lit_mark := s.core.lit_mark } =
                            s.core :=
                        (congrArg (fun x =>
                          { x with tmp := s.core.tmp, lit_mark := s.core.lit_mark }) h5c).trans hc4
                      have hs5 : st5.scratch = s.scratch := h5s.trans hs4
                      fc_split_fast
                      · have hok_true : ok = true := hc
                        have hcl_m := hok hok_true
                        have hcl_m' : (cnfOfClauses F_cur).EntailsClause (cnfClause
                            ((List.range k.toNat).map fun b =>
                              ((s.scratch.work_stk2[b]?.getD 0#32) ^^^
                                ((mask >>> b) &&& 1#32)).toNat)) := by
                          refine entails_perm_clause (fun x hx => ?_) hcl_m
                          rw [List.mem_map] at hx ⊢; obtain ⟨b, hb, rfl⟩ := hx
                          refine ⟨b, hb, ?_⟩
                          rw [show st4b.core.tmp[b]?.getD 0#32 = tmpi[b]?.getD 0#32 from rfl,
                            htmp_bi b (List.mem_range.mp hb)]
                        fc_let
                        refine hJm4 (_, ()) m5
                          ⟨st5, hlen5, hc5, hs5, hmk5, fun m' h1 h2 hmpar => ?_, hm5⟩
                        rw [hm1_n] at h2
                        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp h2) with hlt | heq
                        · exact heven_m m' h1 hlt hmpar
                        · have heqm : m' = mask := BitVec.eq_of_toNat_eq heq
                          subst heqm; exact hcl_m'
                      · fc_let
                        exact hret_same st5 m5 hlen5 hc5 (by rw [hs5]) hmk5
                          (by rw [hs5]; exact fun _ _ => rfl) (by rw [hs5]; exact hseq0) hm5
                  · have hpar_ne0 : m6MaskParity mask k.toNat ≠ 0#32 := by
                      intro h0; revert hc; rw [hpop_eq, h0]; decide
                    fc_let
                    refine hJm4 (_, ()) m4 ⟨st4, hlen4, hc4, hs4, hmk4,
                      fun m' h1 h2 hmpar => ?_, hm4⟩
                    rw [hm1_n] at h2
                    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp h2) with hlt | heq
                    · exact heven_m m' h1 hlt hmpar
                    · exfalso; apply hpar_ne0; rw [← BitVec.eq_of_toNat_eq heq]; exact hmpar
            · have hm_eq : mask.toNat = 2 ^ k.toNat := by
                simp only [BitVec.ult, decide_eq_false_iff_not] at hc
                rw [hlim_n] at hc; omega
              rw [hm_eq] at heven_m; clear hc
              have heven_ok := heven_m
              let base := List.ofFn (fun idx : Fin k.toNat => s.scratch.work_stk2[idx.1]?.getD 0#32)
              have hbase_len : base.length = k.toNat := by simp [base]
              have hbase_get : ∀ b < k.toNat,
                  base[b]?.getD 0#32 = s.scratch.work_stk2[b]?.getD 0#32 := fun b hb => by
                dsimp only [base]
                rw [List.getElem?_eq_getElem (by simp [hb]), Option.getD_some, List.getElem_ofFn]
              have hbase_map : base.map BitVec.toNat =
                  (List.range k.toNat).map fun i => (s.scratch.work_stk2[i]?.getD 0#32).toNat := by
                apply List.ext_getElem
                · simp [hbase_len]
                · intro b hb1 _
                  simp only [hbase_len, List.length_map] at hb1
                  simp only [List.getElem_map, List.getElem_range]
                  have h := hbase_get b hb1
                  rw [← congrArg BitVec.toNat h,
                    List.getElem?_eq_getElem (by simp [base, hb1]), Option.getD_some,
                    List.getElem_ofFn]
              have harity_n : (k - 1#32).toNat = k.toNat - 1 := by bv_omega
              have hbase_cl' : (cnfOfClauses F_cur).EntailsClause
                  (cnfClause (base.map BitVec.toNat)) := by rw [hbase_map]; exact hbase_cl
              have heven' : ∀ mask : BitVec 32, 1 ≤ mask.toNat → mask.toNat < 2 ^ k.toNat →
                  m6MaskParity mask k.toNat = 0#32 →
                  (cnfOfClauses F_cur).EntailsClause (cnfClause ((List.range k.toNat).map
                    fun b => ((base[b]?.getD 0#32) ^^^ ((mask >>> b) &&& 1#32)).toNat)) :=
                fun mask hm1 hm2 hmpar => by
                  have hcl := heven_ok mask hm1 hm2 hmpar
                  refine entails_perm_clause (fun x hx => ?_) hcl
                  rw [List.mem_map] at hx ⊢; obtain ⟨b, hb, rfl⟩ := hx
                  exact ⟨b, hb, by rw [hbase_get b (List.mem_range.mp hb)]⟩
              let np_base : Nat := (List.range k.toNat).foldl
                (fun acc b => acc ^^^ ((base[b]?.getD 0#32).toNat % 2)) 0
              have hnp_base : np_base = (List.range k.toNat).foldl
                  (fun acc b => acc ^^^ ((base[b]?.getD 0#32).toNat % 2)) 0 := rfl
              have hfold_list : ∀ (xs : List Nat) (init : Nat), (∀ b ∈ xs, b < k.toNat) →
                  xs.foldl (fun acc b => acc ^^^ ((base[b]?.getD 0#32).toNat % 2)) init =
                  xs.foldl (fun acc b =>
                    acc ^^^ ((s.scratch.work_stk2[b]?.getD 0#32).toNat % 2)) init := by
                intro xs; induction xs with
                | nil => intro init _; rfl
                | cons x xs ih =>
                  intro init hxs; simp only [List.foldl_cons]
                  rw [hbase_get x (hxs x (by simp))]
                  exact ih _ (fun b hb => hxs b (by simp [hb]))
              have hnp_eq_ws : np_base = (neg_p &&& 1#32).toNat := by
                rw [hnp]
                exact hfold_list (List.range k.toNat) 0 fun b hb => List.mem_range.mp hb
              have hnp_mod2 : np_base % 2 = (neg_p &&& 1#32).toNat := by
                have hlt2 : np_base < 2 := by
                  rw [hnp_eq_ws, BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl,
                    Nat.and_one_is_mod]
                  exact Nat.mod_lt _ (by decide)
                exact (Nat.mod_eq_of_lt hlt2).trans hnp_eq_ws
              have hsign_eq' : BitVec.ofNat 32 (1 ^^^ (np_base % 2)) =
                  1#32 ^^^ (neg_p &&& 1#32) := by
                apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_xor, show (1#32 : BitVec 32).toNat = 1 from rfl,
                  ← hnp_mod2, bv32_ofNat_toNat]
                rcases Nat.mod_two_eq_zero_or_one np_base with h | h <;> simp [h]
              clear heven_ok hbase_map hfold_list hnp_eq_ws hm1 hmle hlim_n hHasClK
              fc_split_fast
              · have hk4 : k = 4#32 := beq_iff_eq.mp hc
                have hk4_n : k.toNat = 4 := congrArg BitVec.toNat hk4
                have hws2_0 : 0 < st4.scratch.work_stk2.length := by rw [hs4, hws2l]; omega
                have hws2_1 : 1 < st4.scratch.work_stk2.length := by rw [hs4, hws2l]; omega
                have hws2_2 : 2 < st4.scratch.work_stk2.length := by rw [hs4, hws2l]; omega
                have hws2_3 : 3 < st4.scratch.work_stk2.length := by rw [hs4, hws2l]; omega
                let b0 := st4.scratch.work_stk2[0]'hws2_0
                let b1 := st4.scratch.work_stk2[1]'hws2_1
                let b2 := st4.scratch.work_stk2[2]'hws2_2
                let b3 := st4.scratch.work_stk2[3]'hws2_3
                have hb0_e : b0 = s.scratch.work_stk2[0]?.getD 0#32 := by
                  simp [b0, hs4, List.getElem?_eq_getElem (hs4 ▸ hws2_0)]
                have hb1_e : b1 = s.scratch.work_stk2[1]?.getD 0#32 := by
                  simp [b1, hs4, List.getElem?_eq_getElem (hs4 ▸ hws2_1)]
                have hb2_e : b2 = s.scratch.work_stk2[2]?.getD 0#32 := by
                  simp [b2, hs4, List.getElem?_eq_getElem (hs4 ▸ hws2_2)]
                have hb3_e : b3 = s.scratch.work_stk2[3]?.getD 0#32 := by
                  simp [b3, hs4, List.getElem?_eq_getElem (hs4 ▸ hws2_3)]
                have hb0_lt : b0.toNat < 2 * s.core.cur_vars := by
                  rw [hb0_e]; exact hbase_lt 0 (by omega)
                have hb1_lt : b1.toNat < 2 * s.core.cur_vars := by
                  rw [hb1_e]; exact hbase_lt 1 (by omega)
                have hb2_lt : b2.toNat < 2 * s.core.cur_vars := by
                  rw [hb2_e]; exact hbase_lt 2 (by omega)
                have hb3_lt : b3.toNat < 2 * s.core.cur_vars := by
                  rw [hb3_e]; exact hbase_lt 3 (by omega)
                have hxor0_norm : XorListGateDef (cnfOfClauses F_cur)
                    (((b0 &&& ~~~1#32) ||| BitVec.ofNat 32 (1 ^^^ np_base % 2)).toNat)
                    [(b1 &&& ~~~1#32).toNat, (b2 &&& ~~~1#32).toNat, (b3 &&& ~~~1#32).toNat] := by
                  have h0 := xorListGateDef_of_all_even_clauses hk5 hbase_len hbase_cl' heven'
                    hnp_base (j := 0) (by omega)
                  have hbg0 : base[0]?.getD 0#32 = b0 := by
                    rw [hbase_get 0 (by omega), ← hb0_e]
                  have hbg1 : base[1]?.getD 0#32 = b1 := by
                    rw [hbase_get 1 (by omega), ← hb1_e]
                  have hbg2 : base[2]?.getD 0#32 = b2 := by
                    rw [hbase_get 2 (by omega), ← hb2_e]
                  have hbg3 : base[3]?.getD 0#32 = b3 := by
                    rw [hbase_get 3 (by omega), ← hb3_e]
                  rw [hk4_n] at h0
                  simpa [hbg0, hbg1, hbg2, hbg3, List.range_succ] using h0
                have hnp_eq4 : np_base =
                    (((0 ^^^ b0.toNat % 2) ^^^ b1.toNat % 2) ^^^ b2.toNat % 2) ^^^
                      b3.toNat % 2 := by
                  have hbg0 : base[0]?.getD 0#32 = b0 := by
                    rw [hbase_get 0 (by omega), ← hb0_e]
                  have hbg1 : base[1]?.getD 0#32 = b1 := by
                    rw [hbase_get 1 (by omega), ← hb1_e]
                  have hbg2 : base[2]?.getD 0#32 = b2 := by
                    rw [hbase_get 2 (by omega), ← hb2_e]
                  have hbg3 : base[3]?.getD 0#32 = b3 := by
                    rw [hbase_get 3 (by omega), ← hb3_e]
                  rw [hnp_base, hk4_n]
                  simp [List.range_succ, hbg0, hbg1, hbg2, hbg3]
                rw [hnp_eq4] at hxor0_norm
                obtain ⟨hx4_0, hx4_1, hx4_2, hx4_3⟩ := xor4_rotations_of_norm hxor0_norm
                have h20_le : g_len.toNat + 20 ≤ g_cap.toNat := by
                  rw [hk4_n] at hneed_le; omega
                have hg5 : (g_len + 5#64).toNat = g_len.toNat + 5 := by bv_omega
                have hg10 : (g_len + 5#64 + 5#64).toNat = g_len.toNat + 10 := by bv_omega
                have hg15 : (g_len + 5#64 + 5#64 + 5#64).toNat = g_len.toNat + 15 := by bv_omega
                have hg20 : (g_len + 5#64 + 5#64 + 5#64 + 5#64).toNat = g_len.toNat + 20 := by
                  bv_omega
                have hld0 : loadVal m4 i32 (c.pWorkStk2 + 0#64) = some b0 := by
                  simpa [b0] using FullArenaTactics.load_full_work_stk2 (i := 0) hws2_0 hm4
                have hld1 : loadVal m4 i32 (c.pWorkStk2 + 4#64) = some b1 := by
                  simpa [b1] using FullArenaTactics.load_full_work_stk2 (i := 1) hws2_1 hm4
                have hld2 : loadVal m4 i32 (c.pWorkStk2 + 8#64) = some b2 := by
                  simpa [b2] using FullArenaTactics.load_full_work_stk2 (i := 2) hws2_2 hm4
                have hld3 : loadVal m4 i32 (c.pWorkStk2 + 12#64) = some b3 := by
                  simpa [b3] using FullArenaTactics.load_full_work_stk2 (i := 3) hws2_3 hm4
                fc_steps
                refine wp_load_of hld0 ?_; m3_let
                refine wp_load_of hld1 ?_; m3_let
                refine wp_load_of hld2 ?_; m3_let
                refine wp_load_of hld3 ?_; fc_steps
                c0_call hEmitXor4
                refine ⟨maxA, F_cur, s.core.cur_vars, st4.scratch.scratch_buf,
                  FullScrBufRest c st4 ⋆ R, by omega, hmax64, hb0_lt, hb1_lt, hb2_lt, hb3_lt,
                  by omega, by rw [hs4, hscrl]; omega, by rw [hs4, hscrl]; omega,
                  hx4_0, by rw [hs4]; exact hseq0, focus_full_scratch_buf hm4,
                  fun scr1 m1 hlen1 hpref1 hseq1 hm1 => ?_⟩
                fc_steps; c0_call hEmitXor4
                refine ⟨maxA, F_cur, s.core.cur_vars, scr1, FullScrBufRest c st4 ⋆ R,
                  by omega, hmax64, hb1_lt, hb0_lt, hb2_lt, hb3_lt, by omega,
                  by rw [hlen1, hs4, hscrl]; omega, by rw [hlen1, hs4, hscrl]; omega,
                  hx4_1, hg5 ▸ hseq1, hm1, fun scr2 m2 hlen2 hpref2 hseq2 hm2 => ?_⟩
                fc_steps; c0_call hEmitXor4
                refine ⟨maxA, F_cur, s.core.cur_vars, scr2, FullScrBufRest c st4 ⋆ R,
                  by omega, hmax64, hb2_lt, hb0_lt, hb1_lt, hb3_lt, by omega,
                  by rw [hlen2, hlen1, hs4, hscrl]; omega, by rw [hlen2, hlen1, hs4, hscrl]; omega,
                  hx4_2, by rw [hg10]; rw [hg5, Nat.add_assoc] at hseq2; exact hseq2, hm2,
                  fun scr3 m3 hlen3 hpref3 hseq3 hm3 => ?_⟩
                fc_steps; c0_call hEmitXor4
                refine ⟨maxA, F_cur, s.core.cur_vars, scr3, FullScrBufRest c st4 ⋆ R,
                  by omega, hmax64, hb3_lt, hb0_lt, hb1_lt, hb2_lt, by omega,
                  by rw [hlen3, hlen2, hlen1, hs4, hscrl]; omega,
                  by rw [hlen3, hlen2, hlen1, hs4, hscrl]; omega,
                  hx4_3, by rw [hg15]; rw [hg10, Nat.add_assoc] at hseq3; exact hseq3, hm3,
                  fun scr4 m4' hlen4' hpref4 hseq4 hm4' => ?_⟩
                fc_steps
                exact hQ (g_len + 5#64 + 5#64 + 5#64 + 5#64)
                  { st4 with scratch := { st4.scratch with scratch_buf := scr4 } } m4'
                  ⟨hlen4.core_ok, { hlen4.scratch_ok with
                    scratch_buf_len := by rw [hlen4', hlen3, hlen2, hlen1, hs4, hscrl] }⟩
                  hc4 (by rw [hs4]) hmk4 (by omega) (by omega)
                  (fun idx hi => (hpref4 idx (by omega)).trans
                    ((hpref3 idx (by omega)).trans
                      ((hpref2 idx (by omega)).trans
                        ((hpref1 idx hi).trans (by rw [hs4])))))
                  (by rw [hg20]; rw [hg15, Nat.add_assoc] at hseq4; exact hseq4)
                  (unfocus_full_scratch_buf hm4')
              · clear hc hEmitXor4; fc_let
                refine wp_loop_inv (ts := [i64, i32])
                  (fun (g_cur, j, ()) mj => ∃ stj : FullState,
                    j.toNat ≤ k.toNat ∧
                    g_cur.toNat = g_len.toNat + j.toNat * (k.toNat + 1) ∧
                    stj.LengthsOk c ∧
                    { stj.core with tmp := s.core.tmp, lit_mark := s.core.lit_mark } = s.core ∧
                    { stj.scratch with scratch_buf := s.scratch.scratch_buf } = s.scratch ∧
                    FullLitMarksClear c stj ∧
                    (∀ idx < g_len.toNat,
                      stj.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) ∧
                    FidGateSeqOk maxA F_cur s.core.cur_vars stj.scratch.scratch_buf g_cur.toNat 0 ∧
                    (FullMem c stj ⋆ R) mj)
                  (fun (_, j, ()) _ => k.toNat - j.toNat)
                  (fun J5 hJ5 => by
                    fc_let; exact hJ5 (g_len, 0#32, ()) m4
                      ⟨st4, Nat.zero_le _, by show g_len.toNat = g_len.toNat + 0 * _; omega,
                       hlen4, hc4, by rw [hs4], hmk4,
                       by rw [hs4]; exact fun _ _ => rfl, by rw [hs4]; exact hseq0, hm4⟩)
                  (fun J5 (g_cur, j, ()) mj
                    ⟨stj, hj_le, hgcur_eq, hlenj, hcj, hsj, hmkj, hprefj, hseqj, hmj⟩ ih5 => ?_)
                fc_split_fast
                · have hj_lt : j.toNat < k.toNat := by
                    simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                  have hj1_n : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
                  have hws2_j : (j.setWidth 64).toNat < stj.scratch.work_stk2.length := by
                    rw [hlenj.scratch_ok.work_stk2_len, bv_zext32_toNat]; omega
                  have hgcur_bd : g_cur.toNat + (k.toNat + 1) ≤ c.scratch_cap := by
                    have hk_step : (j.toNat + 1) * (k.toNat + 1) ≤ k.toNat * (k.toNat + 1) :=
                      Nat.mul_le_mul_right _ hj_lt
                    have hgadd : g_len.toNat + j.toNat * (k.toNat + 1) + (k.toNat + 1) =
                        g_len.toNat + (j.toNat + 1) * (k.toNat + 1) := by
                      rw [Nat.add_assoc, ← Nat.succ_mul]
                    omega
                  have hg0_lt : g_cur.toNat < stj.scratch.scratch_buf.length := by
                    rw [hlenj.scratch_ok.scratch_buf_len]; omega
                  have hg1_n : (g_cur + 1).toNat = g_cur.toNat + 1 := by bv_omega
                  have hg1_lt : (g_cur + 1).toNat < stj.scratch.scratch_buf.length := by
                    rw [hlenj.scratch_ok.scratch_buf_len]; omega
                  have hj_ws2 : (j.setWidth 64).toNat = j.toNat := bv_zext32_toNat j
                  let base_j := stj.scratch.work_stk2[(j.setWidth 64).toNat]'hws2_j
                  have hbj_eq : base_j = s.scratch.work_stk2[j.toNat]?.getD 0#32 := by
                    dsimp only [base_j]
                    have hws : stj.scratch.work_stk2 = s.scratch.work_stk2 :=
                      congrArg (·.work_stk2) hsj
                    rw [List.getElem?_eq_getElem (by omega : j.toNat < s.scratch.work_stk2.length),
                      Option.getD_some]
                    exact (list_getElem_congr hj_ws2 hws2_j (by rw [hws]; omega)).trans
                      (by simp [hws])
                  let lhs_j := (base_j &&& ~~~1#32) ||| (1#32 ^^^ (neg_p &&& 1#32))
                  let mword_j := (1#32 <<< 28) ||| (k - 1#32)
                  fc_steps
                  let scr_j1 := (stj.scratch.scratch_buf.set g_cur.toNat lhs_j).set
                    (g_cur.toNat + 1) mword_j
                  let stj1 : FullState := { stj with scratch :=
                    { stj.scratch with scratch_buf := scr_j1 } }
                  have hm_j1 : (FullMem c stj1 ⋆ R) m := by
                    dsimp only [stj1, scr_j1]; rw [hg1_n] at hm; exact hm
                  have hsj1 :
                      { stj1.scratch with scratch_buf := s.scratch.scratch_buf } = s.scratch := hsj
                  have hws2_stj1 : stj1.scratch.work_stk2 = s.scratch.work_stk2 :=
                    congrArg (·.work_stk2) hsj1
                  refine wp_loop_inv (ts := [i32, i32])
                    (fun (rk, i, ()) mi => ∃ tmpi : List (BitVec 32),
                      i.toNat ≤ k.toNat ∧
                      rk.toNat = (if i.toNat ≤ j.toNat then i.toNat else i.toNat - 1) ∧
                      tmpi.length = c.max_vars ∧
                      List.Perm (tmpi.take rk.toNat)
                        (((List.range i.toNat).filter (· != j.toNat)).map fun idx =>
                          ((s.scratch.work_stk2[idx]?.getD 0#32) &&& ~~~1#32)) ∧
                      (FullMem c { stj1 with core := { stj1.core with tmp := tmpi } } ⋆ R) mi)
                    (fun (_, i, ()) _ => k.toNat - i.toNat)
                    (fun Ji hJi => by
                      fc_let; refine hJi (0#32, 0#32, ()) m
                        ⟨stj1.core.tmp, Nat.zero_le _, by simp, hlenj.core_ok.tmp_len_arr,
                         by simp, hm_j1⟩)
                    (fun Ji (rk, i, ()) mi ⟨tmpi, hi_le, hrk_eq, htmpi_l, hperm_i, hmi⟩ ihi => ?_)
                  fc_split_fast
                  · have hi_lt : i.toNat < k.toNat := by
                      simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                    have hi1_n : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
                    have hrng_step : (List.range (i.toNat + 1)).filter (· != j.toNat) =
                        (List.range i.toNat).filter (· != j.toNat) ++
                          if i.toNat != j.toNat then [i.toNat] else [] := by
                      rw [List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]
                    fc_to_group; refine wp_join_group (ts := [i32])
                      (fun (rk', ()) mi' => ∃ tmpi' : List (BitVec 32),
                        rk'.toNat = (if i.toNat + 1 ≤ j.toNat then i.toNat + 1 else i.toNat) ∧
                        tmpi'.length = c.max_vars ∧
                        List.Perm (tmpi'.take rk'.toNat)
                          (((List.range (i.toNat + 1)).filter (· != j.toNat)).map fun idx =>
                            ((s.scratch.work_stk2[idx]?.getD 0#32) &&& ~~~1#32)) ∧
                        (FullMem c { stj1 with core := { stj1.core with tmp := tmpi' } } ⋆ R) mi')
                      (fun _ ⟨rk', ⟨⟩⟩ mi' ⟨tmpi', hrk', htl', hp', hmi'⟩ => by
                        fc_let; exact ihi (rk', i + 1#32, ()) mi' (by dsimp only; omega)
                          ⟨tmpi', by omega, by rw [hi1_n]; exact hrk', htl',
                           by rw [hi1_n]; exact hp', hmi'⟩) ?_
                    intro Jif hJif; fc_split_fast
                    · have hij_ne : i.toNat ≠ j.toNat := fun h =>
                        (bne_iff_ne.mp hc) (BitVec.eq_of_toNat_eq h)
                      have hrk_lt : rk.toNat < k.toNat - 1 := by
                        rw [hrk_eq]; split <;> omega
                      have hi_ws2 :
                          (i.setWidth 64).toNat < stj1.scratch.work_stk2.length := by
                        rw [hws2_stj1, hws2l, bv_zext32_toNat]; omega
                      have hrk_tmp : (rk.setWidth 64).toNat < tmpi.length := by
                        rw [bv_zext32_toNat]; omega
                      have hrk1_n : (rk + 1#32).toNat = rk.toNat + 1 := by bv_omega
                      fc_steps
                      let wi := (stj1.scratch.work_stk2[(i.setWidth 64).toNat]'hi_ws2) &&& ~~~1#32
                      have hwi_eq : wi =
                          ((s.scratch.work_stk2[i.toNat]?.getD 0#32) &&& ~~~1#32) := by
                        dsimp only [wi]; congr 1
                        rw [List.getElem?_eq_getElem
                          (by omega : i.toNat < s.scratch.work_stk2.length), Option.getD_some]
                        exact (list_getElem_congr (bv_zext32_toNat i) hi_ws2
                          (by rw [hws2_stj1]; omega)).trans (by simp [hws2_stj1])
                      let tmpi' := tmpi.set (rk.setWidth 64).toNat wi
                      have hrk_z : (rk.setWidth 64).toNat = rk.toNat := bv_zext32_toNat rk
                      have hrk_len : rk.toNat < tmpi.length := hrk_z ▸ hrk_tmp
                      have htk_step : tmpi'.take (rk.toNat + 1) = tmpi.take rk.toNat ++ [wi] := by
                        dsimp only [tmpi']; rw [hrk_z]
                        have h1 : (tmpi.set rk.toNat wi).take rk.toNat = tmpi.take rk.toNat := by
                          apply List.ext_getElem
                          · rw [List.length_take, List.length_set, List.length_take]
                          · intro q hq _
                            rw [List.length_take] at hq
                            rw [List.getElem_take, List.getElem_take,
                              List.getElem_set_ne (by omega)]
                        rw [List.take_succ_eq_append_getElem (by simp [hrk_len]),
                          h1, List.getElem_set_self (by simp [hrk_len])]
                      refine hJif (rk + 1#32, ()) m
                        ⟨tmpi', by rw [hrk1_n, hrk_eq]; split <;> split <;> omega,
                         by simp [tmpi', htmpi_l], ?_, by dsimp only [tmpi']; exact hm⟩
                      rw [hrk1_n, htk_step, hrng_step]
                      simp [hij_ne, hwi_eq]
                      exact hperm_i.append_right _
                    · have hij_eq : i.toNat = j.toNat :=
                        congrArg BitVec.toNat (by simpa using hc : i = j)
                      m3_let; refine hJif (rk, ()) mi
                        ⟨tmpi, by rw [hrk_eq]; split <;> split <;> omega, htmpi_l, ?_, hmi⟩
                      simp only [hrng_step,
                        show (i.toNat != j.toNat) = false from by simp [hij_eq],
                        Bool.false_eq_true, ↓reduceIte, List.append_nil]
                      exact hperm_i
                  · have hi_eq : i.toNat = k.toNat := by
                      simp only [BitVec.ult, decide_eq_false_iff_not] at hc; omega
                    have hrk_eq_ar : rk.toNat = (k - 1#32).toNat := by
                      rw [hrk_eq, hi_eq, harity_n]; split <;> omega
                    rw [hi_eq] at hperm_i; rw [hrk_eq_ar] at hperm_i
                    fc_steps; c0_call hSort
                    refine ⟨tmpi, FullTmpRest c stj1 ⋆ R,
                      by rw [show (k - 1 : BitVec 32).toNat = k.toNat - 1 by bv_omega]; omega,
                      focus_full_tmp hmi, fun tmp_s ms hlen_s hperm_s hsuf_s hms => ?_⟩
                    have hms' : (FullMem c { stj1 with core :=
                        { stj1.core with tmp := tmp_s } } ⋆ R) ms := unfocus_full_tmp hms
                    have hperm_all : List.Perm (tmp_s.take (k - 1#32).toNat)
                        (((List.range k.toNat).filter (· != j.toNat)).map fun idx =>
                          ((s.scratch.work_stk2[idx]?.getD 0#32) &&& ~~~1#32)) :=
                      hperm_s.trans hperm_i
                    let stj2 : FullState := { stj1 with core := { stj1.core with tmp := tmp_s } }
                    fc_let
                    refine wp_loop_inv (ts := [i32])
                      (fun (ic, ()) mc => ∃ scr_c : List (BitVec 32),
                        ic.toNat ≤ (k - 1#32).toNat ∧ scr_c.length = c.scratch_cap ∧
                        (∀ idx < g_cur.toNat, scr_c[idx]? = stj.scratch.scratch_buf[idx]?) ∧
                        scr_c[g_cur.toNat]? = some lhs_j ∧
                        scr_c[g_cur.toNat + 1]? = some mword_j ∧
                        (∀ q < ic.toNat, scr_c[g_cur.toNat + 2 + q]? = tmp_s[q]?) ∧
                        (FullMem c { stj2 with scratch :=
                          { stj2.scratch with scratch_buf := scr_c } } ⋆ R) mc)
                      (fun (ic, ()) _ => (k - 1#32).toNat - ic.toNat)
                      (fun Jc hJc => by
                        fc_let; refine hJc (0#32, ()) ms ⟨scr_j1, Nat.zero_le _,
                          by simp [scr_j1, hlenj.scratch_ok.scratch_buf_len],
                          fun idx hi => by
                            dsimp only [scr_j1]
                            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)],
                          by dsimp only [scr_j1]
                             rw [List.getElem?_set_ne (by omega),
                               List.getElem?_set_self (by omega)],
                          by dsimp only [scr_j1]
                             rw [List.getElem?_set_self (by simp [
                               hlenj.scratch_ok.scratch_buf_len]; omega)],
                          fun _ h => by simp at h, hms'⟩)
                      (fun Jc (ic, ()) mc ⟨scr_c, hic_le, hscrc_l, hpc_pref, hpc0, hpc1,
                        hpc_rhs, hmc⟩ ihc => ?_)
                    fc_split_fast
                    · have hic_lt : ic.toNat < (k - 1#32).toNat := by
                        simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                      have hic1_n : (ic + 1#32).toNat = ic.toNat + 1 := by bv_omega
                      have hic_tmp : (ic.setWidth 64).toNat < tmp_s.length := by
                        rw [bv_zext32_toNat]; omega
                      have hgcur_lt2 : g_cur.toNat < 2 ^ 29 := by
                        have := hg1_lt; rw [hlenj.scratch_ok.scratch_buf_len] at this; omega
                      have hdst_n : (g_cur + 2 + ic.setWidth 64).toNat =
                          g_cur.toNat + 2 + ic.toNat :=
                        bv64_add_zext32 (k := 2) (by omega)
                      have hdst_lt : (g_cur + 2 + ic.setWidth 64).toNat < scr_c.length := by
                        rw [hdst_n, hscrc_l]; omega
                      fc_steps
                      let scr_c' := scr_c.set (g_cur.toNat + 2 + ic.toNat)
                        (tmp_s[(ic.setWidth 64).toNat]'hic_tmp)
                      have hm_c' : (FullMem c { stj2 with scratch :=
                          { stj2.scratch with scratch_buf := scr_c' } } ⋆ R) m := by
                        dsimp only [scr_c']; rw [hdst_n] at hm; exact hm
                      refine ihc (ic + 1#32, ()) m (by dsimp only; omega)
                        ⟨scr_c', by omega, by simp [scr_c', hscrc_l],
                         fun idx hi => by
                            dsimp only [scr_c']; rw [List.getElem?_set_ne (by omega)]
                            exact hpc_pref idx hi,
                         by dsimp only [scr_c']; rw [List.getElem?_set_ne (by omega)]; exact hpc0,
                         by dsimp only [scr_c']; rw [List.getElem?_set_ne (by omega)]; exact hpc1,
                         fun q hq => ?_, hm_c'⟩
                      rw [hic1_n] at hq
                      by_cases hqi : q = ic.toNat
                      · subst hqi; dsimp only [scr_c']
                        rw [List.getElem?_set_self (by rw [hscrc_l]; omega),
                          List.getElem?_eq_getElem (by omega : ic.toNat < tmp_s.length)]
                        exact congrArg some
                          (list_getElem_congr (bv_zext32_toNat ic) hic_tmp (by omega))
                      · dsimp only [scr_c']; rw [List.getElem?_set_ne (by omega)]
                        exact hpc_rhs q (by omega)
                    · have hic_eq : ic.toNat = (k - 1#32).toNat := by
                        simp only [BitVec.ult, decide_eq_false_iff_not] at hc
                        have hk1_s : (k - 1 : BitVec 32).toNat = k.toNat - 1 := by bv_omega
                        omega
                      rw [hic_eq] at hpc_rhs
                      have hgcur_bd2 : g_cur.toNat + 2 + (k - 1#32).toNat < 2 ^ 29 := by
                        have := hsc; omega
                      have hgnext_n : (g_cur + 2#64 + (k - 1#32).setWidth 64).toNat =
                          g_cur.toNat + (k.toNat + 1) := by
                        rw [bv64_add_zext32 (k := 2) (by omega), harity_n]; omega
                      have hseq_j' : FidGateSeqOk maxA F_cur s.core.cur_vars scr_c
                          (g_cur.toNat + (k.toNat + 1)) 0 :=
                        xor_k_emit_gate_pure hmax4 hk3 hk5 hkcv hj_lt hk_cases hbase_len hbase_get
                          hbase_lt hbase_cl' heven' hnp_base hsign_eq' harity_n hbj_eq rfl rfl
                          (hscrc_l.trans hlenj.scratch_ok.scratch_buf_len.symm)
                          (by omega) hpc_pref hpc0 hpc1 hpc_rhs hperm_all
                          (by rw [hlenj.scratch_ok.scratch_buf_len]; exact hgcur_bd) hseqj
                      m3_let
                      refine ih5 (g_cur + 2#64 + (k - 1#32).setWidth 64, j + 1#32, ()) mc
                        (by dsimp only; omega)
                        ⟨{ stj2 with scratch := { stj2.scratch with scratch_buf := scr_c } },
                         by omega,
                         by rw [hgnext_n, hgcur_eq, hj1_n, Nat.add_mul, Nat.one_mul, Nat.add_assoc],
                         ⟨{ hlenj.core_ok with tmp_len_arr := hlen_s.trans htmpi_l },
                          { hlenj.scratch_ok with scratch_buf_len := hscrc_l }⟩,
                         hcj, hsj, hmkj,
                         fun idx hi => (hpc_pref idx (by omega)).trans (hprefj idx hi),
                         by change FidGateSeqOk maxA F_cur s.core.cur_vars scr_c
                              (g_cur + 2#64 + (k - 1#32).setWidth 64).toNat 0
                            rw [hgnext_n]; exact hseq_j',
                         hmc⟩
                · have hj_eq : j.toNat = k.toNat := by
                    simp only [BitVec.ult, decide_eq_false_iff_not] at hc; omega
                  m3_let
                  exact hQ g_cur stj mj hlenj hcj hsj hmkj (by omega)
                    (by rw [hgcur_eq, hj_eq]; exact hneed_le) hprefj hseqj hmj

/-! ## 5. `full_cong_try_xor_ite_wp` (`fidCongTryXorIteSpec`) -/

theorem full_cong_try_xor_ite_wp (Γ : Env)
    (hHasTern : ∀ args m Q X, FullCongSpecs.fullHasTernarySpec args m Q X →
      Γ "full_has_ternary" [i64, i32, i32, i32] [.bool] args m Q X)
    (hEmitXor : ∀ args m Q X, fidCongEmitXorSpec args m Q X →
      Γ "full_cong_emit_xor" [i64, i64, i32, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fidCongTryXorIteSpec args m Q X →
      Func.wp Γ full_cong_try_xor_ite_body args m Q X := by
  rintro ⟨h, a, b, cl, g_len, g_cap, ⟨⟩⟩ m0 Q X
    ⟨maxA, c, F0, F_cur, s, R, hmax2, hmax64, rfl, hlen, hw, hnd, hcl0, ha_lt, hb_lt, hc_lt,
     hab_v, hac_v, hbc_v, hcl0_ent, hg_le, hgc_le, hseq0, hm0, hQ⟩
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hscrl := hlen.scratch_ok.scratch_buf_len
  have hcv3 : 3 ≤ s.core.cur_vars :=
    cur_vars_ge3_of_distinct (by omega) (by omega) (by omega) hab_v hac_v hbc_v
  have hna_lt : (a ^^^ 1).toNat < 2 * s.core.cur_vars := by
    rw [bv32_xor1_litNeg]; exact bv32_xor1_lt_even ha_lt
  have hdis_lit : ∀ x y : BitVec 32, x.toNat / 2 ≠ y.toNat / 2 → x ≠ y :=
    fun _ _ => bv32_ne_of_div2_ne
  have hret0 : Q (g_len, ()) m0 :=
    hQ g_len s.scratch.scratch_buf m0 hscrl (Nat.le_refl _) (by omega) (fun _ _ => rfl) hseq0 hm0
  fc_split_fast
  · exfalso; exact hab_v (bv32_div2_eq_of_shr1_eq hc)
  · clear hc; fc_split_fast
    · exfalso; exact hac_v (bv32_div2_eq_of_shr1_eq hc)
    · clear hc; fc_split_fast
      · exfalso; exact hbc_v (bv32_div2_eq_of_shr1_eq hc)
      · clear hc; fc_to_group
        refine wp_join_group (ts := [i32]) (fun _ mj => mj = m0) ?_ ?_
        · rintro _ ⟨_, ⟨⟩⟩ mj hmj; subst mj; fc_to_group
          refine wp_join_group (ts := [i32]) (fun _ mj => mj = m0) ?_ ?_
          · rintro _ ⟨_, ⟨⟩⟩ mj hmj; subst mj; fc_to_group
            refine wp_join_group (ts := []) (fun () mj => mj = m0) ?_ ?_
            · rintro _ ⟨⟩ mj hmj; subst mj; fc_to_group
              refine wp_join_group (ts := []) (fun () mj => mj = m0) ?_ ?_
              · rintro _ ⟨⟩ mj hmj; subst mj; fc_to_group
                refine wp_join_group (ts := []) (fun () mj => mj = m0) ?_ ?_
                · rintro _ ⟨⟩ mj hmj; subst mj; fc_steps; c0_call hHasTern
                  refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, ha_lt, hm0,
                    fun ok1 hok1 => ?_⟩
                  fc_split_fast
                  · have ht1 : (cnfOfClauses F_cur).EntailsClause
                        (cnfClause [a.toNat, litNeg b.toNat, litNeg cl.toNat]) := by
                      simpa only [bv32_xor1_litNeg] using hok1 hc
                        (hdis_lit _ _ (div2_ne_of_xor1 hab_v))
                        (hdis_lit _ _ (div2_ne_of_xor1 hac_v))
                        (hdis_lit _ _ (div2_ne_of_xor1_both hbc_v))
                    fc_steps; c0_call hHasTern
                    refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, hna_lt, hm0,
                      fun ok2 hok2 => ?_⟩
                    fc_split_fast
                    · have ht2 : (cnfOfClauses F_cur).EntailsClause
                          (cnfClause [litNeg a.toNat, b.toNat, litNeg cl.toNat]) := by
                        simpa only [bv32_xor1_litNeg] using hok2 hc
                          (hdis_lit _ _ (div2_ne_of_xor1_l hab_v))
                          (hdis_lit _ _ (div2_ne_of_xor1_both hac_v))
                          (hdis_lit _ _ (div2_ne_of_xor1 hbc_v))
                      fc_steps; c0_call hHasTern
                      refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, hna_lt, hm0,
                        fun ok3 hok3 => ?_⟩
                      fc_split_fast
                      · have ht3 : (cnfOfClauses F_cur).EntailsClause
                            (cnfClause [litNeg a.toNat, litNeg b.toNat, cl.toNat]) := by
                          simpa only [bv32_xor1_litNeg] using hok3 hc
                            (hdis_lit _ _ (div2_ne_of_xor1_both hab_v))
                            (hdis_lit _ _ (div2_ne_of_xor1_l hac_v))
                            (hdis_lit _ _ (div2_ne_of_xor1_l hbc_v))
                        obtain ⟨hx1, hx2, hx3⟩ := xorGateDef_of_four hcl0_ent ht1 ht2 ht3
                        fc_to_group
                        refine wp_join_group (ts := [i64])
                          (fun (ret, ()) mr => ∃ scr' : List (BitVec 32),
                            scr'.length = c.scratch_cap ∧ g_len.toNat ≤ ret.toNat ∧
                            ret.toNat ≤ g_cap.toNat ∧
                            (∀ idx < g_len.toNat, scr'[idx]? = s.scratch.scratch_buf[idx]?) ∧
                            FidGateSeqOk maxA F_cur s.core.cur_vars scr' ret.toNat 0 ∧
                            (FullMem c { s with scratch :=
                              { s.scratch with scratch_buf := scr' } } ⋆ R) mr)
                          ?_ ?_
                        · rintro _ ⟨ret, ⟨⟩⟩ mr ⟨scr', hlen', hlo, hhi, hpref', hseq', hmr⟩
                          fc_let; exact hQ ret scr' mr hlen' hlo hhi hpref' hseq' hmr
                        · intro Jret hJret; fc_split_fast
                          · have h12 : g_len.toNat + 12 ≤ g_cap.toNat := by
                              simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                            have hg4 : (g_len + 4#64).toNat = g_len.toNat + 4 := by bv_omega
                            have hg8 : (g_len + 4#64 + 4#64).toNat = g_len.toNat + 8 := by bv_omega
                            have hg12 : (g_len + 4#64 + 4#64 + 4#64).toNat = g_len.toNat + 12 := by
                              bv_omega
                            fc_steps; c0_call hEmitXor
                            refine ⟨maxA, F_cur, s.core.cur_vars, s.scratch.scratch_buf,
                              FullScrBufRest c s ⋆ R, hmax2, hmax64, ha_lt, hb_lt, hc_lt,
                              by omega, by omega, by omega, hx1, hseq0,
                              focus_full_scratch_buf hm0,
                              fun scr1 m1 hlen1 hpref1 hseq1 hm1 => ?_⟩
                            fc_steps; c0_call hEmitXor
                            refine ⟨maxA, F_cur, s.core.cur_vars, scr1, FullScrBufRest c s ⋆ R,
                              hmax2, hmax64, hb_lt, ha_lt, hc_lt, by omega, by omega, by omega,
                              hx2, hg4 ▸ hseq1, hm1, fun scr2 m2 hlen2 hpref2 hseq2 hm2 => ?_⟩
                            fc_steps; c0_call hEmitXor
                            refine ⟨maxA, F_cur, s.core.cur_vars, scr2, FullScrBufRest c s ⋆ R,
                              hmax2, hmax64, hc_lt, ha_lt, hb_lt, by omega, by omega, by omega,
                              hx3, by rw [hg8]; rw [hg4, Nat.add_assoc] at hseq2; exact hseq2,
                              hm2, fun scr3 m3 hlen3 hpref3 hseq3 hm3 => ?_⟩
                            fc_let
                            exact hJret (g_len + 4#64 + 4#64 + 4#64, ()) m3
                              ⟨scr3, by omega, by omega, by omega,
                               fun idx hi => (hpref3 idx (by omega)).trans
                                 ((hpref2 idx (by omega)).trans (hpref1 idx hi)),
                               by rw [hg12]; rw [hg8, Nat.add_assoc] at hseq3; exact hseq3,
                               unfocus_full_scratch_buf hm3⟩
                          · fc_let
                            exact hJret (g_len, ()) m0
                              ⟨s.scratch.scratch_buf, hscrl, Nat.le_refl _, by omega,
                               fun _ _ => rfl, hseq0, hm0⟩
                      · fc_let; exact hret0
                    · fc_let; exact hret0
                  · fc_let; exact hret0
                · intro J3 hJ3; fc_split_fast
                  · exact hJ3 () m0 rfl
                  · clear hc; fc_split_fast
                    · exact hJ3 () m0 rfl
                    · exact hret0
              · intro J2 hJ2; fc_split_fast
                · exact hJ2 () m0 rfl
                · clear hc; fc_split_fast
                  · exact hJ2 () m0 rfl
                  · exact hret0
            · intro J1 hJ1; fc_split_fast
              · exact hJ1 () m0 rfl
              · clear hc; fc_split_fast
                · exact hJ1 () m0 rfl
                · exact hret0
          · intro Jmx hJmx; fc_split_fast
            · fc_let; exact hJmx (cl, ()) m0 rfl
            · fc_let; exact hJmx (_, ()) m0 rfl
        · intro Jmx1 hJmx1; fc_split_fast
          · fc_let; exact hJmx1 (a, ()) m0 rfl
          · fc_let; exact hJmx1 (b, ()) m0 rfl

end LeanQbe.T.Examples.Kissat.FullFidelityCong
