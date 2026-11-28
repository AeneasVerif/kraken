module
public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Inv
public import LeanQbe.T.Examples.Kissat.Src.Congruence

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Spec LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics

public section

/-! ### Shared pure BitVec, clause, and layout helpers -/

private theorem bv32_and1_eq0_iff (x : BitVec 32) :
    x &&& 1#32 = 0#32 ↔ x.toNat % 2 = 0 := by
  constructor
  · intro h
    have h0 := congrArg BitVec.toNat h
    rw [BitVec.toNat_and] at h0
    simp only [BitVec.toNat_ofNat] at h0
    rwa [Nat.and_one_is_mod] at h0
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]; simp only [BitVec.toNat_ofNat]
    rw [Nat.and_one_is_mod]; exact h

private theorem bv32_or1_eq_xor1 (x : BitVec 32) (hx : x &&& 1#32 = 0#32) :
    x ||| 1#32 = x ^^^ 1#32 := by
  have hx0 : x.toNat % 2 = 0 := (bv32_and1_eq0_iff x).mp hx
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_or, BitVec.getElem_xor]
  rcases i with _ | i
  · have h0 : x[0] = false := by rw [BitVec.getElem_eq_testBit_toNat]; simp [hx0]
    have h1 : (1#32 : BitVec 32)[0] = true := by simp [BitVec.getElem_eq_testBit_toNat]
    simp [h0, h1]
  · have h1 : (1#32 : BitVec 32)[i + 1] = false := by
      rw [BitVec.getElem_eq_testBit_toNat]
      simp only [BitVec.toNat_ofNat, Nat.testBit, Nat.shiftRight_eq_div_pow]
      have hlt : 1 < 2 ^ (i + 1) := Nat.one_lt_two_pow (Nat.succ_ne_zero i)
      simp [Nat.div_eq_of_lt hlt]
    simp [h1]

private theorem u64_pack32_hi (a b : BitVec 32) :
    ((BitVec.setWidth 64 a <<< 32 ||| BitVec.setWidth 64 b) >>> 32).toNat = a.toNat := by
  have heq :
      (BitVec.setWidth 64 a <<< 32 ||| BitVec.setWidth 64 b) >>> 32 = BitVec.setWidth 64 a := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth]
    by_cases h32 : i < 32
    · have hadd : i + 32 < 64 := by omega
      have hge : ¬ (i + 32 < 32) := by omega
      simp [h32, hadd, hge, hi, Nat.add_comm]
    · have ha : a.getLsbD i = false := BitVec.getLsbD_of_ge a i (by omega)
      simp [ha, hi]
  rw [heq, bv_zext32_toNat]

private theorem u64_pack32_lo (a b : BitVec 32) :
    ((BitVec.setWidth 64 a <<< 32 ||| BitVec.setWidth 64 b) &&& 4294967295#64).toNat =
      b.toNat := by
  have heq :
      (BitVec.setWidth 64 a <<< 32 ||| BitVec.setWidth 64 b) &&& 4294967295#64 =
        BitVec.setWidth 64 b := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hm : (4294967295#64 : BitVec 64).getLsbD i = decide (i < 32) := by
      rw [BitVec.getLsbD_ofNat, decide_eq_true hi, Bool.true_and]
      have hval : (4294967295 : Nat) = 2 ^ 32 - 1 := by decide
      rw [hval, Nat.testBit_two_pow_sub_one]
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, hm]
    by_cases h32 : i < 32
    · simp [h32, hi]
    · have hb : b.getLsbD i = false := BitVec.getLsbD_of_ge b i (by omega)
      simp [h32, hi, hb]
  rw [heq, bv_zext32_toNat]

private theorem u64_trunc_shr32 (w : BitVec 64) :
    (BitVec.setWidth 32 (w >>> 32#64)).toNat = (w >>> 32).toNat := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
  have hlt : w.toNat >>> 32 < 2 ^ 32 := by
    rw [Nat.shiftRight_eq_div_pow]; have := w.isLt; omega
  exact Nat.mod_eq_of_lt hlt

private theorem u64_trunc_toNat (w : BitVec 64) :
    (BitVec.setWidth 32 w).toNat = (w &&& 4294967295#64).toNat := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_and]
  have h1 : (4294967295#64 : BitVec 64).toNat = 2 ^ 32 - 1 := by decide
  rw [h1, Nat.and_two_pow_sub_one_eq_mod]

private theorem sortedRange64_sub {xs : List (BitVec 64)} {lo hi m : Nat}
    (hs : SortedRange64 xs 0 m) (_hlo : lo ≤ hi) (hhi : hi ≤ m) :
    SortedRange64 xs lo hi :=
  fun i j _ hij _ => hs i j (by omega) hij (by omega)

private theorem cnf_clause_three_eval {f : Std.Sat.CNF Nat} {a b c : Nat}
    (h : f.EntailsClause (cnfClause [a, b, c]))
    {α : Nat → Bool} (hα : Std.Sat.CNF.Sat α f) :
    evalLitVal α a = true ∨ evalLitVal α b = true ∨ evalLitVal α c = true := by
  rw [Std.Sat.CNF.entails_clause_def] at h
  have hs : Std.Sat.CNF.Clause.Sat α (cnfClause [a, b, c]) := h α hα
  rw [Std.Sat.CNF.Clause.sat_iff_exists_mem_eq] at hs
  rcases hs with ⟨⟨v, pol⟩, hmem, heq⟩
  have hmem' : (v, pol) ∈ Std.Sat.CNF.Clause.literals (cnfClause [a, b, c]) := hmem
  rw [cnfClause, Std.Sat.CNF.Clause.literals_ofLiterals] at hmem'
  simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hmem'
  rcases hmem' with ⟨l, hl, hpair⟩
  cases hpair
  rcases hl with rfl | rfl | rfl
  · exact Or.inl (by simp only [evalLitVal] at *; rw [heq]; cases litSign l <;> decide)
  · exact Or.inr (Or.inl (by simp only [evalLitVal] at *; rw [heq]; cases litSign l <;> decide))
  · exact Or.inr (Or.inr (by simp only [evalLitVal] at *; rw [heq]; cases litSign l <;> decide))

private theorem condEqElemOk_of_clauses {F_cur : List (List Nat)} {cv lit : Nat}
    {a b : BitVec 32}
    (ha : a.toNat < 2 * cv) (hb : b.toNat < 2 * cv)
    (hab : a.toNat / 2 ≠ b.toNat / 2)
    (hal : a.toNat / 2 ≠ lit / 2) (hbl : b.toNat / 2 ≠ lit / 2)
    (hc1 : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, a.toNat, litNeg b.toNat]))
    (hc2 : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, litNeg a.toNat, b.toNat])) :
    CondEqElemOk F_cur cv lit (BitVec.setWidth 64 a <<< 32 ||| BitVec.setWidth 64 b) := by
  simp only [CondEqElemOk, u64_pack32_hi, u64_pack32_lo]
  exact ⟨ha, hb, hab, hal, hbl, hc1, hc2⟩

private theorem condEqElemOk_flip {F_cur : List (List Nat)} {cv lit : Nat}
    {a b : BitVec 32}
    (hw : CondEqElemOk F_cur cv lit
      (BitVec.setWidth 64 a <<< 32 ||| BitVec.setWidth 64 b)) :
    CondEqElemOk F_cur cv lit
      (BitVec.setWidth 64 (b ^^^ 1#32) <<< 32 ||| BitVec.setWidth 64 (a ^^^ 1#32)) := by
  simp only [CondEqElemOk, u64_pack32_hi, u64_pack32_lo] at hw ⊢
  rcases hw with ⟨ha, hb, hab, hal, hbl, hc1, hc2⟩
  refine ⟨bv32_xor1_lt_even hb, bv32_xor1_lt_even ha, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bv32_xor1_eq_litNeg, bv32_xor1_eq_litNeg, litNeg_div2, litNeg_div2]
    exact fun h => hab h.symm
  · rw [bv32_xor1_eq_litNeg, litNeg_div2]; exact hbl
  · rw [bv32_xor1_eq_litNeg, litNeg_div2]; exact hal
  · rw [bv32_xor1_eq_litNeg, bv32_xor1_eq_litNeg, litNeg_litNeg]
    refine entails_perm_clause (fun x hx => ?_) hc1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with rfl | rfl | rfl <;> simp
  · rw [bv32_xor1_eq_litNeg, bv32_xor1_eq_litNeg, litNeg_litNeg]
    refine entails_perm_clause (fun x hx => ?_) hc2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with rfl | rfl | rfl <;> simp

private theorem condEqElemOk_swap {F_cur : List (List Nat)} {cv lit : Nat}
    {a b : BitVec 32}
    (hw : CondEqElemOk F_cur cv lit
      (BitVec.setWidth 64 a <<< 32 ||| BitVec.setWidth 64 b)) :
    CondEqElemOk F_cur cv lit (BitVec.setWidth 64 b <<< 32 ||| BitVec.setWidth 64 a) := by
  simp only [CondEqElemOk, u64_pack32_hi, u64_pack32_lo] at hw ⊢
  rcases hw with ⟨ha, hb, hab, hal, hbl, hc1, hc2⟩
  refine ⟨hb, ha, fun h => hab h.symm, hbl, hal, ?_, ?_⟩
  · refine entails_perm_clause (fun x hx => ?_) hc2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with rfl | rfl | rfl <;> simp
  · refine entails_perm_clause (fun x hx => ?_) hc1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with rfl | rfl | rfl <;> simp

private theorem condEqElemOk_emit2 {F_cur : List (List Nat)} {cv lit : Nat}
    {a b v520 v12 : BitVec 32}
    (hv12_even : v12 &&& 1#32 = 0#32) (hv520 : v520 = v12 ||| 1#32) (ha : a = v12)
    (hw1 : CondEqElemOk F_cur cv lit
      (BitVec.setWidth 64 a <<< 32 ||| BitVec.setWidth 64 b)) :
    CondEqElemOk F_cur cv lit
      (BitVec.setWidth 64 (if b &&& 1#32 ≠ 0#32 then b ^^^ 1#32 else b) <<< 32 |||
        BitVec.setWidth 64 (if b &&& 1#32 ≠ 0#32 then v520 else v12)) := by
  by_cases h : b &&& 1#32 ≠ 0#32
  · have h1 : (if b &&& 1#32 ≠ 0#32 then b ^^^ 1#32 else b) = b ^^^ 1#32 := by simp [h]
    have h2 : (if b &&& 1#32 ≠ 0#32 then v520 else v12) = v520 := by simp [h]
    have hneg : v520 = a ^^^ 1#32 := by rw [hv520, ha, bv32_or1_eq_xor1 v12 hv12_even]
    rw [h1, h2, hneg]; exact condEqElemOk_flip hw1
  · have h1 : (if b &&& 1#32 ≠ 0#32 then b ^^^ 1#32 else b) = b := by simp [h]
    have h2 : (if b &&& 1#32 ≠ 0#32 then v520 else v12) = v12 := by simp [h]
    rw [h1, h2, ← ha]; exact condEqElemOk_swap hw1

/-! ### `extract_condeq_m7` invariants & loop helpers -/

private def ExtractCondeqOuterInv (F_cur : List (List Nat)) (cur_vars lit : Nat)
    (cb ceq cap : BitVec 64) (cb_xs : List (BitVec 64)) (m : BitVec 64)
    (R : Mem 64 → Prop) (u i : BitVec 64) (mem : Mem 64) : Prop :=
  ∃ ceq_c,
    u.toNat ≤ cap.toNat ∧
      i.toNat ≤ m.toNat ∧
      ceq_c.length = cap.toNat ∧
      (∀ k, k < u.toNat → CondEqElemOk F_cur cur_vars lit (ceq_c[k]?.getD 0#64)) ∧
      (array64 cb cb_xs ⋆ array64 ceq ceq_c ⋆ R) mem

private def ExtractCondeqRunInv (cb_xs : List (BitVec 64)) (m : BitVec 64)
    (target : BitVec 32) (lo j : BitVec 64) : Prop :=
  lo.toNat ≤ j.toNat ∧
    j.toNat ≤ m.toNat ∧
    ∀ t, lo.toNat ≤ t → t < j.toNat → (cb_xs[t]?.getD 0#64 >>> 32).toNat = target.toNat

private def ExtractCondeqScanInv (F_cur : List (List Nat)) (cur_vars lit : Nat)
    (cb ceq cap : BitVec 64) (cb_xs : List (BitVec 64)) (lo hi : BitVec 64)
    (R : Mem 64 → Prop) (u idx : BitVec 64) (mem : Mem 64) : Prop :=
  ∃ ceq_c,
    u.toNat ≤ cap.toNat ∧
      lo.toNat ≤ idx.toNat ∧
      idx.toNat ≤ hi.toNat ∧
      ceq_c.length = cap.toNat ∧
      (∀ k, k < u.toNat → CondEqElemOk F_cur cur_vars lit (ceq_c[k]?.getD 0#64)) ∧
      (array64 cb cb_xs ⋆ array64 ceq ceq_c ⋆ R) mem

private def ExtractCondeqDedupInv (F_cur : List (List Nat)) (cur_vars lit : Nat)
    (cb ceq cap : BitVec 64) (cb_xs : List (BitVec 64)) (u : BitVec 64)
    (R : Mem 64 → Prop) (v10 v11 : BitVec 64) (mem : Mem 64) : Prop :=
  ∃ ceq_c,
    1 ≤ v10.toNat ∧
      v10.toNat ≤ v11.toNat ∧
      v11.toNat ≤ u.toNat ∧
      u.toNat ≤ cap.toNat ∧
      ceq_c.length = cap.toNat ∧
      (∀ k, k < u.toNat → CondEqElemOk F_cur cur_vars lit (ceq_c[k]?.getD 0#64)) ∧
      (array64 cb cb_xs ⋆ array64 ceq ceq_c ⋆ R) mem

private theorem extract_condeq_emit_le_ok {F_cur : List (List Nat)} {cv lit : Nat}
    {cb_xs : List (BitVec 64)} {v12 v520 : BitVec 32} {idx1 idx2 : Nat}
    (hidx1 : idx1 < cb_xs.length)
    (hbin1 : CondBinElemOk F_cur cv lit (cb_xs[idx1]?.getD 0#64))
    (hbin2 : CondBinElemOk F_cur cv lit (cb_xs[idx2]?.getD 0#64))
    (hv12_even : v12 &&& 1#32 = 0#32) (hv520 : v520 = v12 ||| 1#32)
    (hhi1 : (cb_xs[idx1]?.getD 0#64 >>> 32).toNat = v12.toNat)
    (hkey2 : cb_xs[idx2]? = some (BitVec.setWidth 64 v520 <<< 32 |||
      BitVec.setWidth 64 (BitVec.setWidth 32 cb_xs[idx1] ^^^ 1#32))) :
    let nb := BitVec.setWidth 32 cb_xs[idx1] ^^^ 1#32
    CondEqElemOk F_cur cv lit (BitVec.setWidth 64 v12 <<< 32 ||| BitVec.setWidth 64 nb) := by
  intro nb
  have h1 := hbin1; have h2 := hbin2
  simp only [CondBinElemOk] at h1 h2
  rw [List.getElem?_eq_getElem hidx1, Option.getD_some] at h1 hhi1
  rw [hkey2, Option.getD_some, u64_pack32_hi, u64_pack32_lo] at h2
  have hb_eq : (BitVec.setWidth 32 cb_xs[idx1]).toNat = (cb_xs[idx1] &&& 4294967295#64).toNat :=
    u64_trunc_toNat _
  refine condEqElemOk_of_clauses (by rw [← hhi1]; exact h1.1) h2.2.1
    (by rw [← hhi1, bv32_xor1_eq_litNeg, litNeg_div2, hb_eq]; exact h1.2.2.1)
    (by rw [← hhi1]; exact h1.2.2.2.1)
    (by rw [bv32_xor1_eq_litNeg, litNeg_div2, hb_eq]; exact h1.2.2.2.2.1) ?_ ?_
  · rw [bv32_xor1_eq_litNeg, litNeg_litNeg, ← hhi1, hb_eq]; exact h1.2.2.2.2.2
  · have hneg : v520.toNat = litNeg v12.toNat := by
      rw [hv520, bv32_or1_eq_xor1 v12 hv12_even, bv32_xor1_eq_litNeg]
    rw [← hneg]; exact h2.2.2.2.2.2

private theorem extract_condeq_emit_gt_ok {F_cur : List (List Nat)} {cv lit : Nat}
    {cb_xs : List (BitVec 64)} {v12 v520 : BitVec 32} {idx1 idx2 : Nat}
    (hidx1 : idx1 < cb_xs.length)
    (hbin1 : CondBinElemOk F_cur cv lit (cb_xs[idx1]?.getD 0#64))
    (hbin2 : CondBinElemOk F_cur cv lit (cb_xs[idx2]?.getD 0#64))
    (hv12_even : v12 &&& 1#32 = 0#32) (hv520 : v520 = v12 ||| 1#32)
    (hhi1 : (cb_xs[idx1]?.getD 0#64 >>> 32).toNat = v520.toNat)
    (hkey2 : cb_xs[idx2]? = some (BitVec.setWidth 64 v12 <<< 32 |||
      BitVec.setWidth 64 (BitVec.setWidth 32 cb_xs[idx1] ^^^ 1#32))) :
    let c := BitVec.setWidth 32 cb_xs[idx1]
    CondEqElemOk F_cur cv lit (BitVec.setWidth 64 v12 <<< 32 ||| BitVec.setWidth 64 c) := by
  intro c
  have h1 := hbin1; have h2 := hbin2
  simp only [CondBinElemOk] at h1 h2
  rw [List.getElem?_eq_getElem hidx1, Option.getD_some] at h1 hhi1
  rw [hkey2, Option.getD_some, u64_pack32_hi, u64_pack32_lo] at h2
  have hc_eq : c.toNat = (cb_xs[idx1] &&& 4294967295#64).toNat := u64_trunc_toNat _
  have hneg : v520.toNat = litNeg v12.toNat := by
    rw [hv520, bv32_or1_eq_xor1 v12 hv12_even, bv32_xor1_eq_litNeg]
  refine condEqElemOk_of_clauses h2.1 (by rw [hc_eq]; exact h1.2.1)
    (by rw [← litNeg_div2 v12.toNat, ← hneg, ← hhi1, hc_eq]; exact h1.2.2.1)
    h2.2.2.2.1 (by rw [hc_eq]; exact h1.2.2.2.2.1) ?_ ?_
  · rw [← bv32_xor1_eq_litNeg]; exact h2.2.2.2.2.2
  · rw [← hneg, ← hhi1, hc_eq]; exact h1.2.2.2.2.2

private theorem extract_condeq_scan_step_mem {F_cur : List (List Nat)} {cv lit : Nat}
    {cb ceq cap : BitVec 64} {cb_xs ceq_c : List (BitVec 64)} {R : Mem 64 → Prop}
    {u lo idx hi : BitVec 64} {mem : Mem 64} {w1 w2 : BitVec 64}
    (hcap_lt : cap.toNat < 2 ^ 61) (hadd2 : u.toNat + 2 ≤ cap.toNat)
    (hlo_idx : lo.toNat ≤ (idx + 1#64).toNat) (hidx_hi : (idx + 1#64).toNat ≤ hi.toNat)
    (hlen : ceq_c.length = cap.toNat)
    (hok : ∀ k, k < u.toNat → CondEqElemOk F_cur cv lit (ceq_c[k]?.getD 0#64))
    (hw1 : CondEqElemOk F_cur cv lit w1) (hw2 : CondEqElemOk F_cur cv lit w2)
    (hmem : (array64 cb cb_xs ⋆
      array64 ceq ((ceq_c.set u.toNat w1).set (u.toNat + 1) w2) ⋆ R) mem) :
    ExtractCondeqScanInv F_cur cv lit cb ceq cap cb_xs lo hi R
      (u + 2#64) (idx + 1#64) mem := by
  have hu2 : (u + 2#64).toNat = u.toNat + 2 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨(ceq_c.set u.toNat w1).set (u.toNat + 1) w2, by omega, hlo_idx, hidx_hi,
    by simp [hlen], ?_, hmem⟩
  intro k hk; rw [hu2] at hk
  have hu1_lt : u.toNat + 1 < (ceq_c.set u.toNat w1).length := by simp [hlen]; omega
  by_cases hk2 : k = u.toNat + 1
  · subst hk2; rw [List.getElem?_set_self hu1_lt, Option.getD_some]; exact hw2
  · rw [List.getElem?_set_ne (by omega)]
    by_cases hk1 : k = u.toNat
    · subst hk1; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hw1
    · rw [List.getElem?_set_ne (by omega)]; exact hok k (by omega)

private theorem extract_condeq_sort_ok {F_cur : List (List Nat)} {cv lit u : Nat}
    {ceq0 ceq_s : List (BitVec 64)}
    (hok : ∀ k, k < u → CondEqElemOk F_cur cv lit (ceq0[k]?.getD 0#64))
    (hperm : ∀ k, k < u → ∃ j, j < u ∧ ceq_s[k]? = ceq0[j]?) :
    ∀ k, k < u → CondEqElemOk F_cur cv lit (ceq_s[k]?.getD 0#64) := by
  intro k hk; rcases hperm k hk with ⟨j, hj, heq⟩; rw [heq]; exact hok j hj

private theorem extract_condeq_dedup_set {F_cur : List (List Nat)} {cv lit u cap : Nat}
    {ceq_c : List (BitVec 64)} {v10 v11 : Nat}
    (hv10_lt : v10 < u) (hv11_lt : v11 < u) (_hu_le : u ≤ cap) (hlen : ceq_c.length = cap)
    (hok : ∀ k, k < u → CondEqElemOk F_cur cv lit (ceq_c[k]?.getD 0#64)) :
    (ceq_c.set v10 (ceq_c[v11]'(by omega))).length = cap ∧
      ∀ k, k < u → CondEqElemOk F_cur cv lit
        (((ceq_c.set v10 (ceq_c[v11]'(by omega)))[k]?).getD 0#64) := by
  refine ⟨by simp [hlen], fun k hk => ?_⟩
  by_cases hkv : k = v10
  · subst hkv
    rw [List.getElem?_set_self (by omega), Option.getD_some]
    have := hok v11 hv11_lt
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
  · rw [List.getElem?_set_ne (by omega)]; exact hok k hk

/-! ### `full_cong_extract_condeq_m7_wp` -/

theorem full_cong_extract_condeq_m7_wp (Γ : Env)
    (hBs : Γ.Has "full_cong_bsearch_u64_m7" Spec.fullCongBsearchU64M7Spec)
    (hSort : Γ.Has "full_cong_u64_sort_m7" Spec.fullCongU64SortM7Spec) :
    ∀ a m Q X, Spec.fullCongExtractCondeqM7Spec a m Q X →
      Func.wp Γ full_cong_extract_condeq_m7_body a m Q X := by
  rintro ⟨cb, m, ceq, cap, ⟨⟩⟩ mem0 Q X
    ⟨F_cur, cur_vars, lit, cb_xs, ceq0, R, hm_le, hcb_len, hsorted, hbins,
      hceq0_len, hcap_lt, hmem0, hQ⟩
  c0_hsteps_nogrp
  refine wp_loop_inv
    (Inv := fun (u, i, ()) mem =>
      ExtractCondeqOuterInv F_cur cur_vars lit cb ceq cap cb_xs m R u i mem)
    (μ := fun (_, i, ()) _ => m.toNat - i.toNat)
    (fun J hJ => by
      c0_hsteps!
      exact hJ (0#64, 0#64, ()) mem0 ⟨ceq0, Nat.zero_le _, Nat.zero_le _, hceq0_len,
        fun _ hk => absurd hk (Nat.not_lt_zero _), hmem0⟩)
    (fun J ⟨u, i, ⟨⟩⟩ mg ⟨ceq_c, hu_le, hi_le, hceq_len, hok, hmg⟩ ih => ?_)
  c0_hsteps_nogrp
  c0_hsplit
  · have hi_lt : i.toNat < m.toNat := hc
    have hi_cb : i.toNat < cb_xs.length := Nat.lt_of_lt_of_le hi_lt hm_le
    c0_hsteps_nogrp
    refine wp_join_group
      (fun (u', i', ()) mem' =>
        i.toNat < i'.toNat ∧
          ExtractCondeqOuterInv F_cur cur_vars lit cb ceq cap cb_xs m R u' i' mem')
      (fun J13 ⟨u', i', ⟨⟩⟩ mem' ⟨hlt, hinv'⟩ => by
        c0_hsteps!; exact ih (u', i', ()) mem' (by dsimp only; omega) hinv')
      (fun J13 hJ13 => ?_)
    c0_hsteps_nogrp
    c0_hsplit
    · have hi1_lt : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_lt (by omega)
      c0_hsteps_nogrp
      refine wp_loop_inv
        (Inv := fun (j, ()) mem' =>
          i.toNat < j.toNat ∧ j.toNat ≤ m.toNat ∧
            (array64 cb cb_xs ⋆ array64 ceq ceq_c ⋆ R) mem')
        (μ := fun (j, ()) _ => m.toNat - j.toNat)
        (fun J517 hJ517 => by c0_hsteps!; exact hJ517 (i + 1#64, ()) mg ⟨by omega, by omega, hmg⟩)
        (fun J517 ⟨j, ⟨⟩⟩ mj ⟨hij_lt, hj_le, hmj⟩ ih517 => ?_)
      c0_hsteps_nogrp
      c0_hsplit
      · have hj1_nat : (j + 1#64).toNat = j.toNat + 1 := bv64_add1_lt (by omega)
        c0_hsteps!; exact ih517 (j + 1#64, ()) mj (by dsimp only; omega) ⟨by omega, by omega, hmj⟩
      · c0_hsteps!; exact hJ13 (u, j, ()) mj ⟨hij_lt, ceq_c, hu_le, hj_le, hceq_len, hok, hmj⟩
      · c0_hsteps!; exact hJ13 (u, j, ()) mj ⟨hij_lt, ceq_c, hu_le, hj_le, hceq_len, hok, hmj⟩
    · have hv12_even : BitVec.setWidth 32 (cb_xs[i.toNat] >>> 32#64) &&& 1#32 = 0#32 := by
        simpa using hc
      have hi1_lt : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_lt (by omega)
      let v12 : BitVec 32 := BitVec.setWidth 32 (cb_xs[i.toNat] >>> 32#64)
      have hhi_i : (cb_xs[i.toNat]?.getD 0#64 >>> 32).toNat = v12.toNat := by
        rw [List.getElem?_eq_getElem hi_cb, Option.getD_some]; exact (u64_trunc_shr32 _).symm
      c0_hsteps_nogrp
      refine wp_loop_inv
        (Inv := fun (j, ()) mem' =>
          i.toNat < j.toNat ∧ ExtractCondeqRunInv cb_xs m v12 i j ∧
            (array64 cb cb_xs ⋆ array64 ceq ceq_c ⋆ R) mem')
        (μ := fun (j, ()) _ => m.toNat - j.toNat)
        (fun J517 hJ517 => by
          c0_hsteps!
          exact hJ517 (i + 1#64, ()) mg ⟨by omega, ⟨by omega, by omega,
            fun t _ _ => by rcases (by omega : t = i.toNat) with rfl; exact hhi_i⟩, hmg⟩)
        (fun J517 ⟨j, ⟨⟩⟩ mj ⟨hij_lt, ⟨hji_le, hj_le, hrun1⟩, hmj⟩ ih517 => ?_)
      c0_hsteps_nogrp
      refine wp_join_group
        (fun () mem' =>
          i.toNat < j.toNat ∧ ExtractCondeqRunInv cb_xs m v12 i j ∧
            (array64 cb cb_xs ⋆ array64 ceq ceq_c ⋆ R) mem')
        (fun J519 ⟨⟩ m519 ⟨hij519, hrun1', hm519⟩ => ?_)
        (fun J519 hJ519 => ?_)
      · let v520 : BitVec 32 := v12 ||| 1#32
        c0_hsteps_nogrp
        refine wp_loop_inv
          (Inv := fun (k, ()) mem' =>
            ExtractCondeqRunInv cb_xs m v520 j k ∧
              (array64 cb cb_xs ⋆ array64 ceq ceq_c ⋆ R) mem')
          (μ := fun (k, ()) _ => m.toNat - k.toNat)
          (fun J521 hJ521 => by
            c0_hsteps!
            exact hJ521 (j, ()) m519 ⟨⟨Nat.le_refl _, hj_le, fun _ _ _ => by omega⟩, hm519⟩)
          (fun J521 ⟨k, ⟨⟩⟩ mk ⟨⟨hjk_le, hk_le, hrun2⟩, hmk⟩ ih521 => ?_)
        c0_hsteps_nogrp
        refine wp_join_group
          (fun () mem' => (array64 cb cb_xs ⋆ array64 ceq ceq_c ⋆ R) mem')
          (fun J523 ⟨⟩ m523 hm523 => ?_)
          (fun J523 hJ523 => ?_)
        · c0_hsteps_nogrp
          refine wp_join_group
            (fun (u', ()) mem' =>
              ExtractCondeqOuterInv F_cur cur_vars lit cb ceq cap cb_xs m R u' k mem')
            (fun J526 ⟨u', ⟨⟩⟩ m526 hinv526 => by
              c0_hsteps!; exact hJ13 (u', k, ()) m526 ⟨by omega, hinv526⟩)
            (fun J526 hJ526 => ?_)
          c0_hsteps_nogrp
          c0_hsplit
          · c0_hsteps_nogrp
            refine wp_join_group
              (fun (u', ()) mem' =>
                ExtractCondeqOuterInv F_cur cur_vars lit cb ceq cap cb_xs m R u' k mem')
              (fun J1028 ⟨u', ⟨⟩⟩ m1028 hinv1028 => by
                c0_hsteps!; exact hJ526 (u', ()) m1028 hinv1028)
              (fun J1028 hJ1028 => ?_)
            c0_hsteps_nogrp
            c0_hsplit
            · c0_hsteps_nogrp
              refine wp_loop_inv
                (Inv := fun (u1, idx, ()) mem' =>
                  ExtractCondeqScanInv F_cur cur_vars lit cb ceq cap cb_xs i j R u1 idx mem')
                (μ := fun (_, idx, ()) _ => j.toNat - idx.toNat)
                (fun J1530 hJ1530 => by
                  c0_hsteps!
                  exact hJ1530 (u, i, ()) m523 ⟨ceq_c, hu_le, Nat.le_refl _, by omega,
                    hceq_len, hok, hm523⟩)
                (fun J1530 ⟨u1, idx, ⟨⟩⟩ ms ⟨ceq_s, hu1_le, hi_idx, hidx_j, hlen_s, hok_s, hms⟩
                  ihs => ?_)
              c0_hsteps_nogrp
              c0_hsplit
              · have hidx_lt : idx.toNat < j.toNat := hc
                have hidx_cb : idx.toNat < cb_xs.length := by omega
                have hidx1_nat : (idx + 1#64).toNat = idx.toNat + 1 := bv64_add1_lt (by omega)
                c0_hsteps_nogrp
                refine wp_join_group
                  (fun (u2, ()) mem' =>
                    ExtractCondeqScanInv F_cur cur_vars lit cb ceq cap cb_xs i j R
                      u2 (idx + 1#64) mem')
                  (fun J1543 ⟨u2, ⟨⟩⟩ m1543 hinv => by
                    c0_hsteps!; exact ihs (u2, idx + 1#64, ()) m1543 (by dsimp only; omega) hinv)
                  (fun J1543 hJ1543 => ?_)
                c0_hsteps_nogrp
                c0_hcall hBs
                · refine ⟨cb_xs, array64 ceq ceq_s ⋆ R, hjk_le, by omega, hcb_len,
                    sortedRange64_sub hsorted hjk_le (by omega), by simpa [sep_assoc] using hms,
                    fun r hr => ?_⟩
                  c0_hsteps_nogrp
                  c0_hsplit
                  · rcases hr.mp hc with ⟨idx2, _, hidx2_k, hcb_idx2⟩
                    have hw1 := extract_condeq_emit_le_ok hidx_cb
                      (hbins idx.toNat (by omega)) (hbins idx2 (by omega))
                      hv12_even rfl (hrun1 idx.toNat hi_idx hidx_lt) hcb_idx2
                    let nb : BitVec 32 := BitVec.setWidth 32 cb_xs[idx.toNat] ^^^ 1#32
                    c0_hsteps_nogrp
                    refine wp_join_group
                      (fun (u2, ()) mem' =>
                        ExtractCondeqScanInv F_cur cur_vars lit cb ceq cap cb_xs i j R
                          u2 (idx + 1#64) mem')
                      (fun J2045 ⟨u2, ⟨⟩⟩ m2045 hinv => by
                        c0_hsteps!; exact hJ1543 (u2, ()) m2045 hinv)
                      (fun J2045 hJ2045 => ?_)
                    c0_hsteps_nogrp
                    c0_hsplit
                    · have hadd2_le : u1.toNat + 2 ≤ cap.toNat := by
                        have hle : (u1 + 2#64).toNat ≤ cap.toNat := hc
                        rwa [BitVec.toNat_add, BitVec.toNat_ofNat,
                          Nat.mod_eq_of_lt (by omega)] at hle
                      have hu1_ceq : u1.toNat < ceq_s.length := by omega
                      have hu1_1_nat : (u1 + 1 : BitVec 64).toNat = u1.toNat + 1 :=
                        bv64_add1_lt (by omega)
                      have hu1_p1 : u1.toNat + 1 < (ceq_s.set u1.toNat
                          (BitVec.setWidth 64 v12 <<< 32 ||| BitVec.setWidth 64 nb)).length := by
                        simp [hlen_s]; omega
                      have hms' : (array64 ceq ceq_s ⋆ (array64 cb cb_xs ⋆ R)) ms := by
                        rw [← sep_assoc, sep_comm (array64 ceq ceq_s)]; exact hms
                      c0_hsteps_nogrp
                      refine wp_join_group
                        (fun (v2549, ()) mem' =>
                          mem' = ms ∧
                            v2549 = if nb &&& 1#32 ≠ 0#32 then nb ^^^ 1#32 else nb)
                        (fun J2548 ⟨v2549, ⟨⟩⟩ m2548 ⟨hm2548, hv2549⟩ => ?_)
                        (fun J2548 hJ2548 => ?_)
                      · rw [hm2548]
                        c0_hsteps_nogrp
                        refine wp_join_group
                          (fun (v2551, ()) mem' =>
                            mem' = ms ∧
                              v2551 = if nb &&& 1#32 ≠ 0#32 then v520 else v12)
                          (fun J2550 ⟨v2551, ⟨⟩⟩ m2550 ⟨hm2550, hv2551⟩ => by
                            have hw2 := condEqElemOk_emit2 hv12_even rfl rfl hw1
                            rw [← hv2549, ← hv2551] at hw2
                            rw [hm2550]
                            c0_hsteps!
                            refine hJ2045 (u1 + 2#64, ()) _
                              (extract_condeq_scan_step_mem hcap_lt hadd2_le
                                (hidx1_nat ▸ by omega) (hidx1_nat ▸ by omega)
                                hlen_s hok_s hw1 hw2 ?_)
                            rw [hu1_1_nat] at *
                            rw [sep_comm (array64 cb cb_xs), sep_assoc]; assumption)
                          (fun J2550 hJ2550 => ?_)
                        c0_hsplit
                        · have h1 : nb &&& 1#32 ≠ 0#32 := by simpa using hc
                          c0_hsteps!; exact hJ2550 (v520, ()) ms ⟨rfl, by simp [h1]⟩
                        · have h0 : nb &&& 1#32 = 0#32 := by simpa using hc
                          c0_hsteps!; exact hJ2550 (v12, ()) ms ⟨rfl, by simp [h0]⟩
                      · c0_hsplit
                        · c0_hsteps!
                          have h1 : nb &&& 1#32 ≠ 0#32 := by simpa using hc
                          have hxx : nb ^^^ 1#32 = BitVec.setWidth 32 cb_xs[idx.toNat] := by
                            apply BitVec.eq_of_toNat_eq
                            simp only [nb, bv32_xor1_eq_litNeg, litNeg_litNeg]
                          have hif : (if nb &&& 1#32 ≠ 0#32 then nb ^^^ 1#32 else nb) =
                              BitVec.setWidth 32 cb_xs[idx.toNat] := by simp [h1, hxx]
                          exact hJ2548 (BitVec.setWidth 32 cb_xs[idx.toNat], ()) ms ⟨rfl, hif.symm⟩
                        · have h0 : nb &&& 1#32 = 0#32 := by simpa using hc
                          c0_hsteps!; exact hJ2548 (nb, ()) ms ⟨rfl, by simp [h0]⟩
                    · c0_hsteps!
                      exact hJ2045 (u1, ()) ms ⟨ceq_s, hu1_le, hidx1_nat ▸ by omega,
                        hidx1_nat ▸ by omega, hlen_s, hok_s, hms⟩
                  · c0_hsteps!
                    exact hJ1543 (u1, ()) ms ⟨ceq_s, hu1_le, hidx1_nat ▸ by omega,
                      hidx1_nat ▸ by omega, hlen_s, hok_s, hms⟩
              · c0_hsteps!; exact hJ1028 (u1, ()) ms ⟨ceq_s, hu1_le, by omega, hlen_s, hok_s, hms⟩
            · c0_hsteps_nogrp
              refine wp_loop_inv
                (Inv := fun (u1, idx, ()) mem' =>
                  ExtractCondeqScanInv F_cur cur_vars lit cb ceq cap cb_xs j k R u1 idx mem')
                (μ := fun (_, idx, ()) _ => k.toNat - idx.toNat)
                (fun J1530 hJ1530 => by
                  c0_hsteps!
                  exact hJ1530 (u, j, ()) m523 ⟨ceq_c, hu_le, Nat.le_refl _, hjk_le,
                    hceq_len, hok, hm523⟩)
                (fun J1530 ⟨u1, idx, ⟨⟩⟩ ms ⟨ceq_s, hu1_le, hj_idx, hidx_k, hlen_s, hok_s, hms⟩
                  ihs => ?_)
              c0_hsteps_nogrp
              c0_hsplit
              · have hidx_lt : idx.toNat < k.toNat := hc
                have hidx_cb : idx.toNat < cb_xs.length := by omega
                have hidx1_nat : (idx + 1#64).toNat = idx.toNat + 1 := bv64_add1_lt (by omega)
                c0_hsteps_nogrp
                refine wp_join_group
                  (fun (u2, ()) mem' =>
                    ExtractCondeqScanInv F_cur cur_vars lit cb ceq cap cb_xs j k R
                      u2 (idx + 1#64) mem')
                  (fun J1543 ⟨u2, ⟨⟩⟩ m1543 hinv => by
                    c0_hsteps!; exact ihs (u2, idx + 1#64, ()) m1543 (by dsimp only; omega) hinv)
                  (fun J1543 hJ1543 => ?_)
                c0_hsteps_nogrp
                c0_hcall hBs
                · refine ⟨cb_xs, array64 ceq ceq_s ⋆ R, Nat.le_of_lt hij519, by omega, hcb_len,
                    sortedRange64_sub hsorted (Nat.le_of_lt hij519) (by omega),
                    by simpa [sep_assoc] using hms, fun r hr => ?_⟩
                  c0_hsteps_nogrp
                  c0_hsplit
                  · rcases hr.mp hc with ⟨idx2, _, hidx2_j, hcb_idx2⟩
                    have hw1 := extract_condeq_emit_gt_ok hidx_cb
                      (hbins idx.toNat (by omega)) (hbins idx2 (by omega))
                      hv12_even rfl (hrun2 idx.toNat hj_idx hidx_lt) hcb_idx2
                    let c0 : BitVec 32 := BitVec.setWidth 32 cb_xs[idx.toNat]
                    c0_hsteps_nogrp
                    refine wp_join_group
                      (fun (u2, ()) mem' =>
                        ExtractCondeqScanInv F_cur cur_vars lit cb ceq cap cb_xs j k R
                          u2 (idx + 1#64) mem')
                      (fun J2045 ⟨u2, ⟨⟩⟩ m2045 hinv => by
                        c0_hsteps!; exact hJ1543 (u2, ()) m2045 hinv)
                      (fun J2045 hJ2045 => ?_)
                    c0_hsteps_nogrp
                    c0_hsplit
                    · have hadd2_le : u1.toNat + 2 ≤ cap.toNat := by
                        have hle : (u1 + 2#64).toNat ≤ cap.toNat := hc
                        rwa [BitVec.toNat_add, BitVec.toNat_ofNat,
                          Nat.mod_eq_of_lt (by omega)] at hle
                      have hu1_ceq : u1.toNat < ceq_s.length := by omega
                      have hu1_1_nat : (u1 + 1 : BitVec 64).toNat = u1.toNat + 1 :=
                        bv64_add1_lt (by omega)
                      have hu1_p1 : u1.toNat + 1 < (ceq_s.set u1.toNat
                          (BitVec.setWidth 64 v12 <<< 32 ||| BitVec.setWidth 64 c0)).length := by
                        simp [hlen_s]; omega
                      have hms' : (array64 ceq ceq_s ⋆ (array64 cb cb_xs ⋆ R)) ms := by
                        rw [← sep_assoc, sep_comm (array64 ceq ceq_s)]; exact hms
                      c0_hsteps_nogrp
                      refine wp_join_group
                        (fun (v2549, ()) mem' =>
                          mem' = ms ∧
                            v2549 = if c0 &&& 1#32 ≠ 0#32 then c0 ^^^ 1#32 else c0)
                        (fun J2548 ⟨v2549, ⟨⟩⟩ m2548 ⟨hm2548, hv2549⟩ => ?_)
                        (fun J2548 hJ2548 => ?_)
                      · rw [hm2548]
                        c0_hsteps_nogrp
                        refine wp_join_group
                          (fun (v2551, ()) mem' =>
                            mem' = ms ∧
                              v2551 = if c0 &&& 1#32 ≠ 0#32 then v520 else v12)
                          (fun J2550 ⟨v2551, ⟨⟩⟩ m2550 ⟨hm2550, hv2551⟩ => by
                            have hw2 := condEqElemOk_emit2 hv12_even rfl rfl hw1
                            rw [← hv2549, ← hv2551] at hw2
                            rw [hm2550]
                            c0_hsteps!
                            refine hJ2045 (u1 + 2#64, ()) _
                              (extract_condeq_scan_step_mem hcap_lt hadd2_le
                                (hidx1_nat ▸ by omega) (hidx1_nat ▸ by omega)
                                hlen_s hok_s hw1 hw2 ?_)
                            rw [hu1_1_nat] at *
                            rw [sep_comm (array64 cb cb_xs), sep_assoc]; assumption)
                          (fun J2550 hJ2550 => ?_)
                        c0_hsplit
                        · have h1 : c0 &&& 1#32 ≠ 0#32 := by simpa using hc
                          c0_hsteps!; exact hJ2550 (v520, ()) ms ⟨rfl, by simp [h1]⟩
                        · have h0 : c0 &&& 1#32 = 0#32 := by simpa using hc
                          c0_hsteps!; exact hJ2550 (v12, ()) ms ⟨rfl, by simp [h0]⟩
                      · c0_hsplit
                        · c0_hsteps!
                          have h1 : c0 &&& 1#32 ≠ 0#32 := by simpa using hc
                          exact hJ2548 (c0 ^^^ 1#32, ()) ms ⟨rfl, by simp [h1]⟩
                        · have h0 : c0 &&& 1#32 = 0#32 := by simpa using hc
                          c0_hsteps!; exact hJ2548 (c0, ()) ms ⟨rfl, by simp [h0]⟩
                    · c0_hsteps!
                      exact hJ2045 (u1, ()) ms ⟨ceq_s, hu1_le, hidx1_nat ▸ by omega,
                        hidx1_nat ▸ by omega, hlen_s, hok_s, hms⟩
                  · c0_hsteps!
                    exact hJ1543 (u1, ()) ms ⟨ceq_s, hu1_le, hidx1_nat ▸ by omega,
                      hidx1_nat ▸ by omega, hlen_s, hok_s, hms⟩
              · c0_hsteps!; exact hJ1028 (u1, ()) ms ⟨ceq_s, hu1_le, by omega, hlen_s, hok_s, hms⟩
          · c0_hsteps!; exact hJ526 (u, ()) m523 ⟨ceq_c, hu_le, hk_le, hceq_len, hok, hm523⟩
        · c0_hsteps_nogrp
          c0_hsplit
          · have hk_lt : k.toNat < m.toNat := by assumption
            have hk_cb : k.toNat < cb_xs.length := by omega
            have hk1_nat : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_lt (by omega)
            have hk_hi : (cb_xs[k.toNat]?.getD 0#64 >>> 32).toNat = v520.toNat := by
              rw [List.getElem?_eq_getElem hk_cb, Option.getD_some, ← u64_trunc_shr32]
              exact congrArg BitVec.toNat hc
            c0_hsteps!
            exact ih521 (k + 1#64, ()) mk (by dsimp only; omega)
              ⟨⟨by omega, by omega, fun t h1 h2 => by
                by_cases htk : t = k.toNat
                · subst htk; exact hk_hi
                · exact hrun2 t h1 (by omega)⟩, hmk⟩
          · c0_hsteps!; exact hJ523 () mk hmk
          · c0_hsteps!; exact hJ523 () mk hmk
      · c0_hsteps_nogrp
        c0_hsplit
        · have hj_lt : j.toNat < m.toNat := by assumption
          have hj_cb : j.toNat < cb_xs.length := by omega
          have hj1_nat : (j + 1#64).toNat = j.toNat + 1 := bv64_add1_lt (by omega)
          have hj_hi : (cb_xs[j.toNat]?.getD 0#64 >>> 32).toNat = v12.toNat := by
            rw [List.getElem?_eq_getElem hj_cb, Option.getD_some, ← u64_trunc_shr32]
            exact congrArg BitVec.toNat hc
          c0_hsteps!
          exact ih517 (j + 1#64, ()) mj (by dsimp only; omega)
            ⟨by omega, ⟨by omega, by omega, fun t h1 h2 => by
              by_cases htj : t = j.toNat
              · subst htj; exact hj_hi
              · exact hrun1 t h1 (by omega)⟩, hmj⟩
        · c0_hsteps!; exact hJ519 () mj ⟨hij_lt, ⟨hji_le, hj_le, hrun1⟩, hmj⟩
        · c0_hsteps!; exact hJ519 () mj ⟨hij_lt, ⟨hji_le, hj_le, hrun1⟩, hmj⟩
  · c0_hsteps!; exact hQ u ceq_c mg hceq_len hu_le hok hmg
  · have hu_gt1 : 1 < u.toNat := by
      have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
      have hnot : ¬ u.toNat ≤ (1#64 : BitVec 64).toNat := by assumption
      rw [h1] at hnot; omega
    have hmg_swap : (array64 ceq ceq_c ⋆ (array64 cb cb_xs ⋆ R)) mg := by
      rw [← sep_assoc, sep_comm (array64 ceq ceq_c)]; exact hmg
    c0_hsteps_nogrp
    c0_hcall hSort
    · refine ⟨ceq_c, array64 cb cb_xs ⋆ R, by omega, by omega, hmg_swap, ?_⟩
      intro ceq_s ms hlen_s _ hperm _ hms
      have hok_s := extract_condeq_sort_ok hok hperm
      have hms_rest : (array64 cb cb_xs ⋆ array64 ceq ceq_s ⋆ R) ms := by
        rw [sep_comm (array64 cb cb_xs), sep_assoc]; exact hms
      c0_hsteps_nogrp
      refine wp_loop_inv
        (Inv := fun (v10, v11, ()) mem' =>
          ExtractCondeqDedupInv F_cur cur_vars lit cb ceq cap cb_xs u R v10 v11 mem')
        (μ := fun (_, v11, ()) _ => u.toNat - v11.toNat)
        (fun J9 hJ9 => by
          c0_hsteps!
          exact hJ9 (1#64, 1#64, ()) ms ⟨ceq_s, by decide, Nat.le_refl _,
            by change 1 ≤ u.toNat; omega, hu_le, hlen_s.trans hceq_len, hok_s, hms_rest⟩)
        (fun J9 ⟨v10, v11, ⟨⟩⟩ m9 ⟨ceq_d, h1_v10, hv10_v11, hv11_u, hu_le', hlen_d, hok_d, hm9⟩
          ih9 => ?_)
      c0_hsteps_nogrp
      c0_hsplit
      · have hv11_lt : v11.toNat < u.toNat := hc
        have hv11_len : v11.toNat < ceq_d.length := by omega
        have hv10m1_nat : (v10 - 1#64).toNat = v10.toNat - 1 := by
          have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
          rw [BitVec.toNat_sub, h1]; have := v10.isLt; omega
        have hv10m1_len : (v10 - 1#64).toNat < ceq_d.length := by omega
        have hv11_1 : (v11 + 1#64).toNat = v11.toNat + 1 := bv64_add1_lt (by omega)
        have hm9_swap : (array64 ceq ceq_d ⋆ (array64 cb cb_xs ⋆ R)) m9 := by
          rw [← sep_assoc, sep_comm (array64 ceq ceq_d)]; exact hm9
        c0_hsteps_nogrp
        refine wp_join_group
          (fun (v14, ()) mem' =>
            ExtractCondeqDedupInv F_cur cur_vars lit cb ceq cap cb_xs u R
              v14 (v11 + 1#64) mem')
          (fun J13 ⟨v14, ⟨⟩⟩ m13 hinv13 => by
            c0_hsteps!; exact ih9 (v14, v11 + 1#64, ()) m13 (by dsimp only; omega) hinv13)
          (fun J13 hJ13 => ?_)
        c0_hsteps!
        c0_hsplit
        · have hv10_lt_u : v10.toNat < u.toNat := by omega
          have hv10_len : v10.toNat < ceq_d.length := by omega
          have hv10_1 : (v10 + 1#64).toNat = v10.toNat + 1 := bv64_add1_lt (by omega)
          have hset := extract_condeq_dedup_set hv10_lt_u hv11_lt hu_le' hlen_d hok_d
          c0_hsteps!
          refine hJ13 (v10 + 1#64, ()) _
            ⟨ceq_d.set v10.toNat ceq_d[v11.toNat], by omega, by omega, by omega, hu_le',
              hset.1, hset.2, ?_⟩
          rw [sep_comm (array64 cb cb_xs), sep_assoc]; assumption
        · c0_hsteps!
          exact hJ13 (v10, ()) m9
            ⟨ceq_d, h1_v10, by omega, by omega, hu_le', hlen_d, hok_d, hm9⟩
      · c0_hsteps!
        exact hQ v10 ceq_d m9 hlen_d (by omega) (fun k hk => hok_d k (by omega)) hm9

/-! ### `merge_condeq_m7` pure helpers & invariant -/

private theorem iteGateDef_of_condEq {F_cur : List (List Nat)} {cv : Nat} {cond : BitVec 32}
    {w1 w2 : BitVec 64}
    (hw1 : CondEqElemOk F_cur cv (litNeg cond.toNat) w1)
    (hw2 : CondEqElemOk F_cur cv cond.toNat w2)
    (hlhs : BitVec.setWidth 32 (w2 >>> 32#64) = BitVec.setWidth 32 (w1 >>> 32#64)) :
    let l := BitVec.setWidth 32 (w1 >>> 32#64)
    let rhs1 := BitVec.setWidth 32 w1
    let rhs2 := BitVec.setWidth 32 w2
    IteGateDef (cnfOfClauses F_cur) l.toNat cond.toNat rhs1.toNat rhs2.toNat ∧
      IteGateDef (cnfOfClauses F_cur) (l ^^^ 1#32).toNat cond.toNat
        (rhs1 ^^^ 1#32).toNat (rhs2 ^^^ 1#32).toNat := by
  intro l rhs1 rhs2
  have hl1 : l.toNat = (w1 >>> 32).toNat := u64_trunc_shr32 w1
  have hl2 : l.toNat = (w2 >>> 32).toNat := by
    dsimp only [l]; rw [← hlhs, u64_trunc_shr32 w2]
  have hr1 : rhs1.toNat = (w1 &&& 4294967295#64).toNat := u64_trunc_toNat w1
  have hr2 : rhs2.toNat = (w2 &&& 4294967295#64).toNat := u64_trunc_toNat w2
  have heq : ∀ α : Nat → Bool, Std.Sat.CNF.Sat α (cnfOfClauses F_cur) →
      evalLitVal α l.toNat =
        if evalLitVal α cond.toNat = true then evalLitVal α rhs1.toNat
        else evalLitVal α rhs2.toNat := by
    intro α hα
    by_cases hcond : evalLitVal α cond.toNat = true
    · have hite : (if evalLitVal α cond.toNat = true then evalLitVal α rhs1.toNat
          else evalLitVal α rhs2.toNat) = evalLitVal α rhs1.toNat := by simp [hcond]
      rw [hite]
      have hc1 := cnf_clause_three_eval hw1.2.2.2.2.2.1 hα
      have hc2 := cnf_clause_three_eval hw1.2.2.2.2.2.2 hα
      rw [evalLitVal_litNeg, hcond] at hc1 hc2
      simp only [← hl1, ← hr1, evalLitVal_litNeg] at hc1 hc2
      cases hl_val : evalLitVal α l.toNat <;> cases hr_val : evalLitVal α rhs1.toNat <;>
        simp_all
    · have hite : (if evalLitVal α cond.toNat = true then evalLitVal α rhs1.toNat
          else evalLitVal α rhs2.toNat) = evalLitVal α rhs2.toNat := by simp [hcond]
      rw [hite]
      have hcf : evalLitVal α cond.toNat = false := Bool.eq_false_iff.mpr hcond
      have hc1 := cnf_clause_three_eval hw2.2.2.2.2.2.1 hα
      have hc2 := cnf_clause_three_eval hw2.2.2.2.2.2.2 hα
      simp only [hcf, ← hl2, ← hr2, evalLitVal_litNeg] at hc1 hc2
      cases hl_val : evalLitVal α l.toNat <;> cases hr_val : evalLitVal α rhs2.toNat <;>
        simp_all
  refine ⟨iteGateDef_of_eval_eq heq, iteGateDef_of_eval_eq (fun α hα => ?_)⟩
  rw [bv32_xor1_eq_litNeg, bv32_xor1_eq_litNeg, bv32_xor1_eq_litNeg,
    evalLitVal_litNeg, evalLitVal_litNeg, evalLitVal_litNeg, heq α hα]
  cases evalLitVal α cond.toNat <;> rfl

private theorem merge_condeq_append_gate_ok {maxA : Nat} {F_cur : List (List Nat)}
    {c : FullCfg} {s : FullState} {scr : List (BitVec 32)}
    {g_len g_cap gl : BitVec 32} {cond g_w t_w e_w : BitVec 32}
    (hmax3 : 3 ≤ maxA) (hcv3 : 3 ≤ s.core.cur_vars)
    (hcond : cond.toNat < 2 * s.core.cur_vars) (hg : g_w.toNat < 2 * s.core.cur_vars)
    (ht : t_w.toNat < 2 * s.core.cur_vars) (he : e_w.toNat < 2 * s.core.cur_vars)
    (hite : IteGateDef (cnfOfClauses F_cur) g_w.toNat cond.toNat t_w.toNat e_w.toNat)
    (hgl_ge : g_len.toNat ≤ gl.toNat) (hgl5_le : gl.toNat + 5 ≤ g_cap.toNat)
    (_hcap_scr : g_cap.toNat ≤ c.scratch_cap) (hlen : scr.length = c.scratch_cap)
    (hpref : ∀ idx, idx < g_len.toNat → scr[idx]? = s.scratch.scratch_buf[idx]?)
    (hseq : CongGateSeqOk maxA F_cur s.core.cur_vars scr gl.toNat 0) :
    let mw : BitVec 32 := (2#32 <<< 28#32) ||| 3#32
    let scr' :=
      ((((scr.set gl.toNat g_w).set (gl.toNat + 1) mw).set
        (gl.toNat + 2) cond).set (gl.toNat + 3) t_w).set (gl.toNat + 4) e_w
    (gl + 5#32).toNat = gl.toNat + 5 ∧
      g_len.toNat ≤ (gl + 5#32).toNat ∧
      (gl + 5#32).toNat ≤ g_cap.toNat ∧
      scr'.length = c.scratch_cap ∧
      (∀ idx, idx < g_len.toNat → scr'[idx]? = s.scratch.scratch_buf[idx]?) ∧
      CongGateSeqOk maxA F_cur s.core.cur_vars scr' (gl + 5#32).toNat 0 := by
  intro mw scr'
  have hgl5_nat : (gl + 5#32).toNat = gl.toNat + 5 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hgcap_lt := g_cap.isLt; exact Nat.mod_eq_of_lt (by omega)
  have hlen1 : (scr.set gl.toNat g_w).length = c.scratch_cap := by simp [hlen]
  have hlen2 : ((scr.set gl.toNat g_w).set (gl.toNat + 1) mw).length = c.scratch_cap := by
    simp [hlen]
  have hlen3 : (((scr.set gl.toNat g_w).set (gl.toNat + 1) mw).set
      (gl.toNat + 2) cond).length = c.scratch_cap := by simp [hlen]
  have hlen4 : ((((scr.set gl.toNat g_w).set (gl.toNat + 1) mw).set
      (gl.toNat + 2) cond).set (gl.toNat + 3) t_w).length = c.scratch_cap := by simp [hlen]
  have hlen' : scr'.length = c.scratch_cap := by simp [scr', hlen]
  have hpref_gl : ∀ idx, idx < gl.toNat → scr'[idx]? = scr[idx]? := by
    intro idx hidx; simp only [scr']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have hs0 : scr'[gl.toNat]? = some g_w := by
    simp only [scr']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by omega)]
  have hs1 : scr'[gl.toNat + 1]? = some mw := by
    simp only [scr']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_self (by rw [hlen1]; omega)]
  have hs2 : scr'[gl.toNat + 2]? = some cond := by
    simp only [scr']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by rw [hlen2]; omega)]
  have hs3 : scr'[gl.toNat + 3]? = some t_w := by
    simp only [scr']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by rw [hlen3]; omega)]
  have hs4 : scr'[gl.toNat + 4]? = some e_w := by
    simp only [scr']
    rw [List.getElem?_set_self (by rw [hlen4]; omega)]
  have hmw_tag : (mw >>> 28).toNat = 2 := by decide
  have hmw_ar : congGateArity mw = 3 := by decide
  have hgat : CongGateAt maxA F_cur s.core.cur_vars scr' (gl.toNat + 5) gl.toNat := by
    refine ⟨g_w, mw, hs0, hs1, hg, by rw [hmw_ar]; omega, by rw [hmw_ar]; exact hcv3,
      by rw [hmw_ar]; exact hmax3, ?_, Or.inr (Or.inr ⟨hmw_tag, hmw_ar, ?_⟩)⟩
    · intro k hk; rw [hmw_ar] at hk
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
      · exact ⟨cond, hs2, hcond⟩
      · exact ⟨t_w, hs3, ht⟩
      · exact ⟨e_w, hs4, he⟩
    · rw [hs2, hs3, hs4, Option.getD_some, Option.getD_some, Option.getD_some]; exact hite
  have htail : CongGateSeqOk maxA F_cur s.core.cur_vars scr' (gl.toNat + 5)
      (gl.toNat + 2 + congGateArity (scr'[gl.toNat + 1]?.getD 0#32)) := by
    rw [hs1, Option.getD_some, hmw_ar]; exact CongGateSeqOk.done
  refine ⟨hgl5_nat, by omega, by omega, hlen', ?_, ?_⟩
  · intro idx hidx; rw [hpref_gl idx (by omega)]; exact hpref idx hidx
  · rw [hgl5_nat]
    exact congGateSeqOk_append_gate hpref_gl hseq (CongGateSeqOk.step hgat htail) (by omega)

private def MergeCondeqState (s : FullState) (scr : List (BitVec 32)) : FullState :=
  { core := s.core, scratch := { s.scratch with scratch_buf := scr } }

private def MergeCondeqInv (maxA : Nat) (F_cur : List (List Nat)) (c : FullCfg) (s : FullState)
    (wk1 wk2 : List (BitVec 64)) (pos_n neg_n : BitVec 64) (g_len g_cap : BitVec 32)
    (R : Mem 64 → Prop) (gl : BitVec 32) (i j : BitVec 64) (mem : Mem 64) : Prop :=
  ∃ scr,
    g_len.toNat ≤ gl.toNat ∧ gl.toNat ≤ g_cap.toNat ∧
      i.toNat ≤ pos_n.toNat ∧ j.toNat ≤ neg_n.toNat ∧ scr.length = c.scratch_cap ∧
      (∀ idx, idx < g_len.toNat → scr[idx]? = s.scratch.scratch_buf[idx]?) ∧
      CongGateSeqOk maxA F_cur s.core.cur_vars scr gl.toNat 0 ∧
      (FullMemNoWks3 c (MergeCondeqState s scr) ⋆
        (array64 c.pWorkStk1 wk1 ⋆ (array64 c.pWorkStk2 wk2 ⋆ R))) mem

/-! ### `full_cong_merge_condeq_m7_wp` -/

theorem full_cong_merge_condeq_m7_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullCongMergeCondeqM7Spec a m Q X →
      Func.wp Γ full_cong_merge_condeq_m7_body a m Q X := by
  rintro ⟨h, cond, pos_n, neg_n, g_len, g_cap, ⟨⟩⟩ m0 Q X
    ⟨maxA, c, F0, F_cur, s, wk1, wk2, R, hmax3, _hmax64, hh, hlen_ok, _hw, hcv3, hcond,
      hcap_scr, hpos_len, hneg_len, hwk1_len, hwk2_len, hwk1_ok, hwk2_ok, hseq0, hm0, hQ⟩
  subst hh
  have hscr_lt64 : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by decide)
  have hm0_r : (FullMemNoWks3 c s ⋆
      (array64 c.pWorkStk1 wk1 ⋆ (array64 c.pWorkStk2 wk2 ⋆ R))) m0 := by
    simpa [sep_assoc] using hm0
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps!; exact hQ g_len s.scratch.scratch_buf m0 hlen_ok.scratch_ok.scratch_buf_len
      (fun h => ⟨Nat.le_refl _, h⟩) (fun _ _ => rfl) hseq0 hm0
  · c0_hsteps!; exact hQ g_len s.scratch.scratch_buf m0 hlen_ok.scratch_ok.scratch_buf_len
      (fun h => ⟨Nat.le_refl _, h⟩) (fun _ _ => rfl) hseq0 hm0
  · have hnot : ¬ g_len.toNat ≤ g_cap.toNat := by omega
    c0_hsteps!; exact hQ g_len s.scratch.scratch_buf m0 hlen_ok.scratch_ok.scratch_buf_len
      (fun h => absurd h hnot) (fun _ _ => rfl) hseq0 hm0
  · have hg_le : g_len.toNat ≤ g_cap.toNat := by omega
    c0_hsteps_nogrp
    refine wp_loop_inv
      (Inv := fun (gl, i, j, ()) mem' =>
        MergeCondeqInv maxA F_cur c s wk1 wk2 pos_n neg_n g_len g_cap R gl i j mem')
      (μ := fun (_, i, j, ()) _ => (pos_n.toNat - i.toNat) + (neg_n.toNat - j.toNat))
      (fun J19 hJ19 => by
        c0_hsteps!
        exact hJ19 (g_len, 0#64, 0#64, ()) m0 ⟨s.scratch.scratch_buf, Nat.le_refl _, hg_le,
          Nat.zero_le _, Nat.zero_le _, hlen_ok.scratch_ok.scratch_buf_len,
          fun _ _ => rfl, hseq0, hm0_r⟩)
      (fun J19 ⟨gl, i, j, ⟨⟩⟩ m19 ⟨scr, hgl_ge, hgl_le, hi_pos, hj_neg, hscr_len, hpref,
        hseq, hm19⟩ ih19 => ?_)
    c0_hsteps_nogrp
    c0_hsplit
    · have hi_lt : i.toNat < pos_n.toNat := by assumption
      have hj_lt : j.toNat < neg_n.toNat := by assumption
      have hi_wk1 : i.toNat < wk1.length := Nat.lt_of_lt_of_le hi_lt hpos_len
      have hj_wk2 : j.toNat < wk2.length := Nat.lt_of_lt_of_le hj_lt hneg_len
      have hm19_wk1 : (array64 c.pWorkStk1 wk1 ⋆
          (FullMemNoWks3 c (MergeCondeqState s scr) ⋆ (array64 c.pWorkStk2 wk2 ⋆ R))) m19 := by
        rw [← sep_assoc, sep_comm (array64 c.pWorkStk1 wk1), sep_assoc]
        exact hm19
      have hm19_wk2 : (array64 c.pWorkStk2 wk2 ⋆
          (FullMemNoWks3 c (MergeCondeqState s scr) ⋆ (array64 c.pWorkStk1 wk1 ⋆ R))) m19 := by
        rw [← sep_assoc, sep_comm (array64 c.pWorkStk2 wk2), sep_assoc]
        rw [← sep_assoc (array64 c.pWorkStk2 wk2), sep_comm (array64 c.pWorkStk2 wk2), sep_assoc]
        exact hm19
      c0_hsteps_nogrp
      refine wp_join_group
        (fun (gl', i', j', ()) mem' =>
          (pos_n.toNat - i'.toNat) + (neg_n.toNat - j'.toNat) <
            (pos_n.toNat - i.toNat) + (neg_n.toNat - j.toNat) ∧
            MergeCondeqInv maxA F_cur c s wk1 wk2 pos_n neg_n g_len g_cap R gl' i' j' mem')
        (fun J39 ⟨gl', i', j', ⟨⟩⟩ m39 ⟨hdec, hinv39⟩ => by
          c0_hsteps!; exact ih19 (gl', i', j', ()) m39 hdec hinv39)
        (fun J39 hJ39 => ?_)
      c0_hsteps_nogrp
      c0_hsplit
      · have hi1_nat : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_lt (by omega)
        c0_hsteps!
        exact hJ39 (gl, i + 1#64, j, ()) m19 ⟨by omega, scr, hgl_ge, hgl_le, by omega,
          hj_neg, hscr_len, hpref, hseq, hm19⟩
      · refine wp_join_group
          (fun (gl', i', j', ()) mem' =>
            (pos_n.toNat - i'.toNat) + (neg_n.toNat - j'.toNat) <
              (pos_n.toNat - i.toNat) + (neg_n.toNat - j.toNat) ∧
              MergeCondeqInv maxA F_cur c s wk1 wk2 pos_n neg_n g_len g_cap R gl' i' j' mem')
          (fun J541 ⟨gl', i', j', ⟨⟩⟩ m541 ⟨hdec, hinv541⟩ => by
            c0_hsteps!; exact hJ39 (gl', i', j', ()) m541 ⟨hdec, hinv541⟩)
          (fun J541 hJ541 => ?_)
        c0_hsteps_nogrp
        c0_hsplit
        · have hj1_nat : (j + 1#64).toNat = j.toNat + 1 := bv64_add1_lt (by omega)
          c0_hsteps!
          exact hJ541 (gl, i, j + 1#64, ()) m19 ⟨by omega, scr, hgl_ge, hgl_le, hi_pos,
            by omega, hscr_len, hpref, hseq, hm19⟩
        · c0_hsteps_nogrp
          refine wp_join_group
            (fun (gl', j', ()) mem' =>
              MergeCondeqInv maxA F_cur c s wk1 wk2 pos_n neg_n g_len g_cap R gl' i j' mem')
            (fun J1043 ⟨gl', _j', ⟨⟩⟩ m1043 hinv1043 => by
              have hi1_nat : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_lt (by omega)
              c0_hsteps!
              rcases hinv1043 with ⟨scr', hgl'_ge, hgl'_le, _, _, hscr'_len, hpref', hseq', hm'⟩
              exact hJ541 (gl', i + 1#64, j, ()) m1043
                ⟨by omega, scr', hgl'_ge, hgl'_le, by omega, hj_neg,
                  hscr'_len, hpref', hseq', hm'⟩)
            (fun J1043 hJ1043 => ?_)
          c0_hsteps_nogrp
          refine wp_loop_inv
            (Inv := fun (gl_in, j_in, ()) mem' =>
              j.toNat ≤ j_in.toNat ∧
                MergeCondeqInv maxA F_cur c s wk1 wk2 pos_n neg_n g_len g_cap R
                  gl_in i j_in mem')
            (μ := fun (_, j_in, ()) _ => neg_n.toNat - j_in.toNat)
            (fun J1544 hJ1544 => by
              c0_hsteps!
              exact hJ1544 (gl, j, ()) m19 ⟨Nat.le_refl _, scr, hgl_ge, hgl_le, hi_pos,
                hj_neg, hscr_len, hpref, hseq, hm19⟩)
            (fun J1544 ⟨gl_in, j_in, ⟨⟩⟩ m_in ⟨hjj_in, scr_in, hglin_ge, hglin_le,
              _, hjin_neg, hscrin_len, hpref_in, hseq_in, hm_in⟩ ih1544 => ?_)
          c0_hsteps_nogrp
          c0_hsplit
          · c0_hsteps!
            exact hJ1043 (gl_in, j_in, ()) m_in ⟨scr_in, hglin_ge, hglin_le, hi_pos,
              hjin_neg, hscrin_len, hpref_in, hseq_in, hm_in⟩
          · have hjin_lt : j_in.toNat < neg_n.toNat := by assumption
            have hjin_wk2 : j_in.toNat < wk2.length := Nat.lt_of_lt_of_le hjin_lt hneg_len
            have hglin5_le : gl_in.toNat + 5 ≤ g_cap.toNat := by
              have hle : (BitVec.setWidth 64 gl_in + 5#64).toNat ≤
                  (BitVec.setWidth 64 g_cap).toNat := by assumption
              rw [BitVec.toNat_add, BitVec.toNat_ofNat, bv_zext32_toNat, bv_zext32_toNat] at hle
              have := gl_in.isLt
              rwa [Nat.mod_eq_of_lt (by omega)] at hle
            have hm_in_wk2 : (array64 c.pWorkStk2 wk2 ⋆
                (FullMemNoWks3 c (MergeCondeqState s scr_in) ⋆ (array64 c.pWorkStk1 wk1 ⋆ R)))
                m_in := by
              rw [← sep_assoc, sep_comm (array64 c.pWorkStk2 wk2), sep_assoc]
              rw [← sep_assoc (array64 c.pWorkStk2 wk2), sep_comm (array64 c.pWorkStk2 wk2),
                sep_assoc]
              exact hm_in
            have hlhs_eq_in : BitVec.setWidth 32 (wk2[j_in.toNat] >>> 32#64) =
                BitVec.setWidth 32 (wk1[i.toNat] >>> 32#64) := by simpa using hc
            have hjin1_nat : (j_in + 1#64).toNat = j_in.toNat + 1 := bv64_add1_lt (by omega)
            c0_hsteps_nogrp
            refine wp_join_group
              (fun (gl_n, ()) mem' =>
                MergeCondeqInv maxA F_cur c s wk1 wk2 pos_n neg_n g_len g_cap R
                  gl_n i j_in mem')
              (fun J1560 ⟨gl_n, ⟨⟩⟩ m1560 hinv1560 => by
                c0_hsteps!
                rcases hinv1560 with
                  ⟨scr_n, hgln_ge, hgln_le, _, _, hscrn_len, hpref_n, hseq_n, hm_n⟩
                exact ih1544 (gl_n, j_in + 1#64, ()) m1560 (by dsimp only; omega)
                  ⟨by omega, scr_n, hgln_ge, hgln_le, hi_pos, by omega,
                    hscrn_len, hpref_n, hseq_n, hm_n⟩)
              (fun J1560 hJ1560 => ?_)
            c0_hsteps_nogrp
            c0_hsplit
            · have hw1_el : CondEqElemOk F_cur s.core.cur_vars (litNeg cond.toNat)
                  wk1[i.toNat] := by
                have := hwk1_ok i.toNat hi_lt
                rwa [List.getElem?_eq_getElem hi_wk1, Option.getD_some] at this
              have hw2_el : CondEqElemOk F_cur s.core.cur_vars cond.toNat wk2[j_in.toNat] := by
                have := hwk2_ok j_in.toNat hjin_lt
                rwa [List.getElem?_eq_getElem hjin_wk2, Option.getD_some] at this
              have hite_pair := iteGateDef_of_condEq hw1_el hw2_el hlhs_eq_in
              have hl_lt : (BitVec.setWidth 32 (wk1[i.toNat] >>> 32#64)).toNat <
                  2 * s.core.cur_vars := by rw [u64_trunc_shr32]; exact hw1_el.1
              have hr1_lt : (BitVec.setWidth 32 wk1[i.toNat]).toNat <
                  2 * s.core.cur_vars := by rw [u64_trunc_toNat]; exact hw1_el.2.1
              have hr2_lt : (BitVec.setWidth 32 wk2[j_in.toNat]).toNat <
                  2 * s.core.cur_vars := by rw [u64_trunc_toNat]; exact hw2_el.2.1
              c0_hsteps_nogrp
              refine wp_join_group
                (fun (g_w, t_w, e_w, ()) mem' =>
                  mem' = m_in ∧ g_w.toNat < 2 * s.core.cur_vars ∧
                    t_w.toNat < 2 * s.core.cur_vars ∧ e_w.toNat < 2 * s.core.cur_vars ∧
                    IteGateDef (cnfOfClauses F_cur) g_w.toNat cond.toNat t_w.toNat e_w.toNat)
                (fun J2063 ⟨g_w, t_w, e_w, ⟨⟩⟩ m2063 ⟨hm2063, hgw, htw, hew, hite⟩ => ?_)
                (fun J2063 hJ2063 => ?_)
              · rw [← hm2063] at hm_in
                dsimp only [MergeCondeqState] at hm_in
                have hs0_lt : (BitVec.setWidth 64 gl_in).toNat < scr_in.length := by
                  rw [bv_zext32_toNat]; omega
                have hs1_lt : (BitVec.setWidth 64 gl_in + 1#64).toNat <
                    (scr_in.set gl_in.toNat g_w).length := by simp [hscrin_len]; omega
                have hs2_lt : (BitVec.setWidth 64 gl_in + 2#64).toNat < ((scr_in.set gl_in.toNat
                    g_w).set (gl_in.toNat + 1) ((2#32 <<< 28#32) ||| 3#32)).length := by
                  simp [hscrin_len]; omega
                have hs3_lt : (BitVec.setWidth 64 gl_in + 3#64).toNat < (((scr_in.set gl_in.toNat
                    g_w).set (gl_in.toNat + 1) ((2#32 <<< 28#32) ||| 3#32)).set (gl_in.toNat + 2)
                    cond).length := by simp [hscrin_len]; omega
                have hs4_lt : (BitVec.setWidth 64 gl_in + 4#64).toNat < ((((scr_in.set gl_in.toNat
                    g_w).set (gl_in.toNat + 1) ((2#32 <<< 28#32) ||| 3#32)).set (gl_in.toNat + 2)
                    cond).set (gl_in.toNat + 3) t_w).length := by simp [hscrin_len]; omega
                c0_hsteps!
                have happ := merge_condeq_append_gate_ok hmax3 hcv3 hcond hgw htw hew
                  hite hglin_ge hglin5_le hcap_scr hscrin_len hpref_in hseq_in
                have hz : ∀ (k : BitVec 64) (n : Nat), k.toNat = n → n < 5 →
                    (BitVec.setWidth 64 gl_in + k).toNat = gl_in.toNat + n := by
                  rintro k n rfl hn; rw [BitVec.toNat_add, bv_zext32_toNat]
                  have := g_cap.isLt; exact Nat.mod_eq_of_lt (by omega)
                refine hJ1560 (gl_in + 5#32, ()) _
                  ⟨_, happ.2.1, happ.2.2.1, hi_pos, hjin_neg, happ.2.2.2.1,
                    happ.2.2.2.2.1, happ.2.2.2.2.2, ?_⟩
                dsimp only [MergeCondeqState] at hm ⊢
                rw [bv_zext32_toNat gl_in, hz 1 1 rfl (by omega), hz 2 2 rfl (by omega),
                  hz 3 3 rfl (by omega), hz 4 4 rfl (by omega)] at hm
                exact hm
              · c0_hsplit
                · c0_hsteps!
                  exact hJ2063 (BitVec.setWidth 32 (wk1[i.toNat] >>> 32#64) ^^^ 1#32,
                    BitVec.setWidth 32 wk1[i.toNat] ^^^ 1#32,
                    BitVec.setWidth 32 wk2[j_in.toNat] ^^^ 1#32, ()) m_in
                    ⟨rfl, bv32_xor1_lt_even hl_lt, bv32_xor1_lt_even hr1_lt,
                      bv32_xor1_lt_even hr2_lt, hite_pair.2⟩
                · c0_hsteps!
                  exact hJ2063 (BitVec.setWidth 32 (wk1[i.toNat] >>> 32#64),
                    BitVec.setWidth 32 wk1[i.toNat],
                    BitVec.setWidth 32 wk2[j_in.toNat], ()) m_in
                    ⟨rfl, hl_lt, hr1_lt, hr2_lt, hite_pair.1⟩
            · c0_hsteps!
              exact hJ1560 (gl_in, ()) m_in ⟨scr_in, hglin_ge, hglin_le, hi_pos,
                hjin_neg, hscrin_len, hpref_in, hseq_in, hm_in⟩
          · c0_hsteps!
            exact hJ1043 (gl_in, j_in, ()) m_in ⟨scr_in, hglin_ge,
              hglin_le, hi_pos, hjin_neg, hscrin_len, hpref_in, hseq_in, hm_in⟩
          · c0_hsteps!
            exact hJ1043 (gl_in, j_in, ()) m_in ⟨scr_in, hglin_ge,
              hglin_le, hi_pos, hjin_neg, hscrin_len, hpref_in, hseq_in, hm_in⟩
    · c0_hsteps!
      exact hQ gl scr m19 hscr_len (fun _ => ⟨hgl_ge, hgl_le⟩) hpref hseq
        (by simpa [MergeCondeqState, sep_assoc] using hm19)
    · c0_hsteps!
      exact hQ gl scr m19 hscr_len (fun _ => ⟨hgl_ge, hgl_le⟩) hpref hseq
        (by simpa [MergeCondeqState, sep_assoc] using hm19)
    · c0_hsteps!
      exact hQ gl scr m19 hscr_len (fun _ => ⟨hgl_ge, hgl_le⟩) hpref hseq
        (by simpa [MergeCondeqState, sep_assoc] using hm19)

/-! ### `extract_ite_all_m7` invariants & helpers -/

private theorem fullDenseInvW_with_wks3_scr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {ws32 k1 k2 scr' : List (BitVec 32)}
    (hws : ws32.length = 2 * c.max_vars) (hk1 : k1.length = 2 * c.max_vars)
    (hk2 : k2.length = 2 * c.max_vars) (hscr : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur
      { core := s.core
        scratch := { s.scratch with
          wsort := ws32, work_stk1 := k1, work_stk2 := k2, scratch_buf := scr' } } := by
  have h1 := fullDenseInvW_with_ws1 hd hk1
  have h2 := fullDenseInvW_with_ws2 h1 hk2
  have h3 := fullDenseInvW_with_scr h2 hscr
  refine ⟨⟨hd.1.core_ok, { h3.1.scratch_ok with wsort_len := hws }⟩,
    hd.2.1, hd.2.2.1, hd.2.2.2.1,
    fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
    hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private def ExtractIteAllInv (maxA : Nat) (F0 : CNF Nat) (F_cur : List (List Nat))
    (c : FullCfg) (s : FullState) (g_len g_cap : BitVec 32) (R : Mem 64 → Prop)
    (v : BitVec 64) (gl : BitVec 32) (m : Mem 64) : Prop :=
  ∃ s',
    FullDenseInvW c F0 F_cur s' ∧ s'.core = s.core ∧
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
      s'.scratch.extend_stk = s.scratch.extend_stk ∧
      s'.scratch.extend_len = s.scratch.extend_len ∧
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.ant_sz = s.scratch.ant_sz ∧
      s'.scratch.res_sz = s.scratch.res_sz ∧
      v.toNat ≤ s.core.cur_vars ∧ g_len.toNat ≤ gl.toNat ∧ gl.toNat ≤ g_cap.toNat ∧
      (∀ idx, idx < g_len.toNat → s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) ∧
      CongGateSeqOk maxA F_cur s.core.cur_vars s'.scratch.scratch_buf gl.toNat 0 ∧
      (FullMem c s' ⋆ R) m

private def ExtractItePairPre (c : FullCfg) (s' : FullState) (v552 v553 : BitVec 32)
    (R : Mem 64 → Prop) (l1 l2 : BitVec 32) (stk1 stk2 : BitVec 64) (swapped : Bool)
    (m : Mem 64) : Prop :=
  ∃ ws64 sa sb,
    ws64.length = c.max_vars ∧ sa.length = c.max_vars ∧ sb.length = c.max_vars ∧
      (if swapped then l1 = v553 ∧ l2 = v552 ∧ stk1 = c.pWorkStk1 ∧ stk2 = c.pWorkStk2
      else l1 = v552 ∧ l2 = v553 ∧ stk1 = c.pWorkStk2 ∧ stk2 = c.pWorkStk1) ∧
      (FullMemNoWks3 c s' ⋆ array64 c.pWsort ws64 ⋆ array64 stk1 sa ⋆ array64 stk2 sb ⋆ R) m

private theorem sep_s12 {A B C : Mem 64 → Prop} {m : Mem 64} (h : (A ⋆ (B ⋆ C)) m) :
    (B ⋆ (A ⋆ C)) m := by rw [← sep_assoc, sep_comm B A, sep_assoc]; exact h
private theorem sep_s23 {A B C D : Mem 64 → Prop} {m : Mem 64} (h : (A ⋆ (B ⋆ (C ⋆ D))) m) :
    (A ⋆ (C ⋆ (B ⋆ D))) m := by rw [← sep_assoc C, sep_comm C B, sep_assoc B]; exact h
private theorem sep_s34 {A B C D E : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ (C ⋆ (D ⋆ E)))) m) : (A ⋆ (B ⋆ (D ⋆ (C ⋆ E)))) m := by
  rw [← sep_assoc D, sep_comm D C, sep_assoc C]; exact h
private theorem sep5_r2l {A B C D E : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ (C ⋆ (D ⋆ E)))) m) : (A ⋆ B ⋆ C ⋆ D ⋆ E) m := by
  rw [sep_assoc, sep_assoc, sep_assoc]; exact h
private theorem sep5_l2r {A B C D E : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ C ⋆ D ⋆ E) m) : (A ⋆ (B ⋆ (C ⋆ (D ⋆ E)))) m := by
  rw [← sep_assoc, ← sep_assoc, ← sep_assoc]; exact h
private theorem sep4_l2r {A B C D : Mem 64 → Prop} {m : Mem 64} (h : (A ⋆ B ⋆ C ⋆ D) m) :
    (A ⋆ (B ⋆ (C ⋆ D))) m := by rw [← sep_assoc, ← sep_assoc]; exact h
private theorem sep3_l2r {A B C : Mem 64 → Prop} {m : Mem 64} (h : ((A ⋆ B) ⋆ C) m) :
    (A ⋆ (B ⋆ C)) m := by rw [← sep_assoc]; exact h

private def ExtractItePairPost (maxA : Nat) (F_cur : List (List Nat)) (c : FullCfg)
    (s s' : FullState) (g_len g_cap : BitVec 32) (stk1 stk2 : BitVec 64) (R : Mem 64 → Prop)
    (gl' : BitVec 32) (mem' : Mem 64) : Prop :=
  ∃ scr' ws64' sa' sb',
    ws64'.length = c.max_vars ∧ sa'.length = c.max_vars ∧ sb'.length = c.max_vars ∧
      scr'.length = c.scratch_cap ∧ g_len.toNat ≤ gl'.toNat ∧ gl'.toNat ≤ g_cap.toNat ∧
      (∀ idx, idx < g_len.toNat → scr'[idx]? = s.scratch.scratch_buf[idx]?) ∧
      CongGateSeqOk maxA F_cur s.core.cur_vars scr' gl'.toNat 0 ∧
      (FullMemNoWks3 c { core := s'.core, scratch := { s'.scratch with scratch_buf := scr' } } ⋆
        array64 c.pWsort ws64' ⋆ array64 stk1 sa' ⋆ array64 stk2 sb' ⋆ R) mem'

private theorem extract_ite_post_merge {maxA : Nat} {F_cur : List (List Nat)} {c : FullCfg}
    {s s' : FullState} {g_len g_cap : BitVec 32} {ws64 sa sb : List (BitVec 64)}
    {scr' : List (BitVec 32)} {stk1 stk2 : BitVec 64} {R : Mem 64 → Prop} {gl' : BitVec 32}
    {m' : Mem 64}
    (hws : ws64.length = c.max_vars) (hsa : sa.length = c.max_vars) (hsb : sb.length = c.max_vars)
    (hscr : scr'.length = c.scratch_cap) (hgl1 : g_len.toNat ≤ gl'.toNat)
    (hgl2 : gl'.toNat ≤ g_cap.toNat)
    (hpref : ∀ idx, idx < g_len.toNat → scr'[idx]? = s.scratch.scratch_buf[idx]?)
    (hseq : CongGateSeqOk maxA F_cur s.core.cur_vars scr' gl'.toNat 0)
    (hm : (FullMemNoWks3 c { core := s'.core, scratch := { s'.scratch with scratch_buf := scr' } } ⋆
      array64 c.pWsort ws64 ⋆ array64 stk1 sa ⋆ array64 stk2 sb ⋆ R) m') :
    ExtractItePairPost maxA F_cur c s s' g_len g_cap stk1 stk2 R gl' m' :=
  ⟨scr', ws64, sa, sb, hws, hsa, hsb, hscr, hgl1, hgl2, hpref, hseq, hm⟩

/-! ### `full_cong_extract_ite_all_m7_wp` -/

theorem full_cong_extract_ite_all_m7_wp (Γ : Env)
    (hCopy : Γ.Has "full_cong_copy_condbin_m7" Spec.fullCongCopyCondbinM7Spec)
    (hExt : Γ.Has "full_cong_extract_condeq_m7" Spec.fullCongExtractCondeqM7Spec)
    (hMerge : Γ.Has "full_cong_merge_condeq_m7" Spec.fullCongMergeCondeqM7Spec) :
    ∀ a m Q X, Spec.fullCongExtractIteAllM7Spec a m Q X →
      Func.wp Γ full_cong_extract_ite_all_m7_body a m Q X := by
  rintro ⟨h, g_len, g_cap, _tick_lim, ⟨⟩⟩ m0 Q X
    ⟨maxA, c, F0, F_cur, s, R, hmax3, hmax64, hh, hd0, hg_le, hcap_scr, hseq0, hm0, hQ⟩
  subst hh
  have hmax_lt31 : c.max_vars < 2 ^ 31 := Nat.lt_trans c.hmaxv (by decide)
  have hmax_lt61 : c.max_vars < 2 ^ 61 := Nat.lt_trans c.hmaxv (by decide)
  have hmax_lt64 : c.max_vars < 2 ^ 64 := Nat.lt_trans hmax_lt61 (by decide)
  have hmax_ofNat : (BitVec.ofNat 64 c.max_vars).toNat = c.max_vars := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hmax_lt64
  have hscr_lt64 : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by decide)
  have hcv_le_max : s.core.cur_vars ≤ c.max_vars := hd0.1.core_ok.cur_vars_le
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := Nat.lt_of_le_of_lt hcv_le_max hmax_lt64
  c0_hsteps_nogrp
  c0_hsplit
  · exact hQ g_len s m0 hd0 rfl rfl rfl rfl rfl rfl rfl rfl (Nat.le_refl _) hg_le
      (fun _ _ => rfl) hseq0 hm0
  · exact hQ g_len s m0 hd0 rfl rfl rfl rfl rfl rfl rfl rfl (Nat.le_refl _) hg_le
      (fun _ _ => rfl) hseq0 hm0
  · have hcv3 : 3 ≤ s.core.cur_vars := by
      have hnot : ¬ s.core.cur_vars % 2 ^ 64 < (3#64 : BitVec 64).toNat := by assumption
      rw [Nat.mod_eq_of_lt hcv_lt64, BitVec.toNat_ofNat] at hnot
      exact Nat.le_of_not_lt hnot
    c0_hsteps_nogrp
    refine wp_loop_inv
      (Inv := fun (v, _ticks, gl, ()) mem' =>
        ExtractIteAllInv maxA F0 F_cur c s g_len g_cap R v gl mem')
      (μ := fun (v, _, _, ()) _ => s.core.cur_vars - v.toNat)
      (fun J28 hJ28 => by
        c0_hsteps!
        exact hJ28 (0#64, 0#64, g_len, ()) m0 ⟨s, hd0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          Nat.zero_le _, Nat.le_refl _, hg_le, fun _ _ => rfl, hseq0, hm0⟩)
      (fun J28 ⟨v, ticks, gl, ⟨⟩⟩ m28
        ⟨s', hd', hcore, htm, htr, hes, hel, hll, hasz, hrsz, hv_le,
          hgl_ge, hgl_le, hpref, hseq, hm28⟩ ih28 => ?_)
    c0_hsteps_nogrp
    c0_hsplit
    · have hv_lt : v.toNat < s.core.cur_vars := by
        have hlt : v.toNat < s.core.cur_vars % 2 ^ 64 := by assumption
        rwa [Nat.mod_eq_of_lt hcv_lt64] at hlt
      have hv_flags : v.toNat < s'.core.flags.length := by
        rw [hd'.1.core_ok.flags_len]; omega
      have hv1_nat : (v + 1#64).toNat = v.toNat + 1 := bv64_add1_lt (by omega)
      have h2v_nat : (v <<< 1#64).toNat = 2 * v.toNat := bv64_shl1_lt (by omega)
      have h2v_vals : (v <<< 1#64).toNat < s'.core.vals.length := by
        rw [hd'.1.core_ok.vals_len]; omega
      let v552 : BitVec 32 := BitVec.setWidth 32 (v <<< 1#64)
      have hv552_nat : v552.toNat = 2 * v.toNat := by
        dsimp only [v552]; rw [BitVec.toNat_setWidth, h2v_nat]; exact Nat.mod_eq_of_lt (by omega)
      have hv552_even : v552 &&& 1#32 = 0#32 :=
        (bv32_and1_eq0_iff v552).mpr (by rw [hv552_nat]; omega)
      let v553 : BitVec 32 := v552 ||| 1#32
      have hv553_lt : v553.toNat < 2 * s.core.cur_vars := by
        dsimp only [v553]; rw [bv32_or1_eq_xor1 v552 hv552_even]
        exact bv32_xor1_lt_even (by omega)
      have hv553_lit : v553.toNat = litNeg v552.toNat := by
        dsimp only [v553]; rw [bv32_or1_eq_xor1 v552 hv552_even, bv32_xor1_eq_litNeg]
      have hwv0_nat : ((BitVec.setWidth 64 v552) <<< 1#64 + 1#64).toNat = 2 * v552.toNat + 1 :=
        bv64_shl1_add1_lt (by rw [bv_zext32_toNat]; omega)
      have hwv1_nat : ((BitVec.setWidth 64 v553) <<< 1#64 + 1#64).toNat = 2 * v553.toNat + 1 :=
        bv64_shl1_add1_lt (by rw [bv_zext32_toNat]; omega)
      have hwv0_len : ((BitVec.setWidth 64 v552) <<< 1#64 + 1#64).toNat <
          s'.core.wvec.length := by
        rw [hwv0_nat, hv552_nat, hd'.1.core_ok.wvec_len]; omega
      have hwv1_len : ((BitVec.setWidth 64 v553) <<< 1#64 + 1#64).toNat <
          s'.core.wvec.length := by
        rw [hwv1_nat, hd'.1.core_ok.wvec_len]; omega
      c0_hsteps_nogrp
      refine wp_join_group
        (fun (ticks', gl', ()) mem' =>
          ExtractIteAllInv maxA F0 F_cur c s g_len g_cap R (v + 1#64) gl' mem')
        (fun J38 ⟨ticks', gl', ⟨⟩⟩ m38 hinv38 => by
          c0_hsteps!; exact ih28 (v + 1#64, ticks', gl', ()) m38 (by dsimp only; omega) hinv38)
        (fun J38 hJ38 => ?_)
      c0_hsteps_nogrp
      c0_hsplit
      · c0_hsteps_nogrp
        refine wp_join_group
          (fun (ticks', gl', ()) mem' =>
            ExtractIteAllInv maxA F0 F_cur c s g_len g_cap R (v + 1#64) gl' mem')
          (fun J566 ⟨ticks', gl', ⟨⟩⟩ m566 hinv566 => by
            c0_hsteps!; exact hJ38 (ticks', gl', ()) m566 hinv566)
          (fun J566 hJ566 => ?_)
        c0_hsteps_nogrp
        refine wp_join_group (fun () mem' => mem' = m28)
          (fun J1067 ⟨⟩ m1067 hm1067 => by
            rw [hm1067]
            c0_hsteps!
            exact hJ566 (ticks + 1#64, gl, ()) m28 ⟨s', hd', hcore, htm, htr, hes,
              hel, hll, hasz, hrsz, by omega, hgl_ge, hgl_le, hpref, hseq, hm28⟩)
          (fun J1067 hJ1067 => ?_)
        c0_hsteps_nogrp
        c0_hsplit
        · c0_hsteps!; exact hJ1067 () m28 rfl
        · c0_hsteps!; exact hJ1067 () m28 rfl
        · c0_hsteps_nogrp
          refine wp_join_group
            (fun (l1, l2, stk1, stk2, sw, ()) mem' =>
              ExtractItePairPre c s' v552 v553 R l1 l2 stk1 stk2 sw mem')
            (fun J1575 ⟨l1, l2, stk1, stk2, sw, ⟨⟩⟩ m1575
              ⟨ws64, sa, sb, hws_len, hsa_len, hsb_len, hargs, hm1575⟩ => ?_)
            (fun J1575 hJ1575 => ?_)
          · have hl1_lt : l1.toNat < 2 * s'.core.cur_vars := by
              cases sw <;> simp at hargs <;> rcases hargs with ⟨rfl, _⟩ <;> rw [hcore] <;> omega
            have hl2_lt : l2.toNat < 2 * s'.core.cur_vars := by
              cases sw <;> simp at hargs <;> rcases hargs with ⟨_, rfl, _⟩ <;> rw [hcore] <;> omega
            have hv552_lt : (BitVec.setWidth 32 (v <<< (1 : BitVec 64))).toNat <
                2 * s'.core.cur_vars := by
              rw [hcore, show BitVec.setWidth 32 (v <<< (1 : BitVec 64)) = v552 from rfl,
                hv552_nat]; omega
            have hm_cp1 : (FullMemNoWks3 c s' ⋆ array64 c.pWsort ws64 ⋆
                (array64 stk1 sa ⋆ (array64 stk2 sb ⋆ R))) m1575 := by
              rw [sep_assoc (FullMemNoWks3 c s')]; exact sep5_l2r hm1575
            c0_hsteps_nogrp
            c0_hcall hCopy
            · refine ⟨c, F0, F_cur, s', ws64, array64 stk1 sa ⋆ (array64 stk2 sb ⋆ R),
                  rfl, hd'.1, hd'.2.1, hd'.2.2.2.2.2.1, hd'.2.2.2.2.2.2, hl1_lt,
                  hws_len.trans hmax_ofNat.symm, by rw [hmax_ofNat]; exact hmax_lt61,
                  hm_cp1, fun cnt1 ws64_1 m_cp1 hws1_len hcnt1_le hsort1 hbins1 hm1 => ?_⟩
              rw [hmax_ofNat] at hws1_len hcnt1_le
              c0_hsteps_nogrp
              refine wp_join_group
                (fun (gl', ()) mem' =>
                  ExtractItePairPost maxA F_cur c s s' g_len g_cap stk1 stk2 R gl' mem')
                (fun J1582 ⟨gl', ⟨⟩⟩ m1582
                  ⟨scr', ws64', sa', sb', hws', hsa', hsb', hscr'', hgl'1, hgl'2,
                    hpref', hseq', hm1582⟩ => ?_)
                (fun J1582 hJ1582 => ?_)
              · have hm_reord : (FullMemNoWks3 c
                      { core := s'.core, scratch := { s'.scratch with scratch_buf := scr' } } ⋆
                    array64 c.pWsort ws64' ⋆
                    array64 c.pWorkStk1 (if sw then sa' else sb') ⋆
                    array64 c.pWorkStk2 (if sw then sb' else sa') ⋆ R) m1582 := by
                  cases sw
                  · rcases (by simpa using hargs : l1 = v552 ∧ l2 = v553 ∧ stk1 = c.pWorkStk2 ∧
                        stk2 = c.pWorkStk1) with ⟨_, _, rfl, rfl⟩
                    simpa using sep5_r2l (sep_s34 (sep5_l2r hm1582))
                  · rcases (by simpa using hargs : l1 = v553 ∧ l2 = v552 ∧ stk1 = c.pWorkStk1 ∧
                        stk2 = c.pWorkStk2) with ⟨_, _, rfl, rfl⟩
                    simpa using hm1582
                rcases unfocus_full_wks3_u64 hws' (by cases sw <;> simp [hsa', hsb'])
                  (by cases sw <;> simp [hsa', hsb']) hm_reord with
                  ⟨ws32, k1, k2, hws32, hk1, hk2, hm_unf⟩
                let s_f : FullState :=
                  { core := s'.core, scratch := { s'.scratch with
                    wsort := ws32, work_stk1 := k1, work_stk2 := k2, scratch_buf := scr' } }
                have hd_f := fullDenseInvW_with_wks3_scr hd' hws32 hk1 hk2 hscr''
                c0_hsteps!; exact hJ566 (ticks + 1#64 + BitVec.setWidth 64
                  s'.core.wvec[(BitVec.setWidth 64 v552 <<< 1#64 + 1#64).toNat] + BitVec.setWidth 64
                  s'.core.wvec[(BitVec.setWidth 64 v553 <<< 1#64 + 1#64).toNat], gl', ()) m1582
                  ⟨s_f, hd_f, hcore, htm, htr, hes, hel, hll, hasz, hrsz, by omega, hgl'1, hgl'2,
                    hpref', hseq', hm_unf⟩
              · c0_hsteps_nogrp
                c0_hsplit
                · have hm_ext1 : (array64 c.pWsort ws64_1 ⋆ array64 stk1 sa ⋆
                      (FullMemNoWks3 c s' ⋆ (array64 stk2 sb ⋆ R))) m_cp1 := by
                    rw [sep_assoc (array64 c.pWsort ws64_1)]; exact sep_s23 (sep_s12 (sep3_l2r hm1))
                  c0_hsteps_nogrp
                  c0_hcall hExt
                  · refine ⟨F_cur, s'.core.cur_vars, l1.toNat, ws64_1, sa,
                        FullMemNoWks3 c s' ⋆ (array64 stk2 sb ⋆ R), by omega, by omega, hsort1,
                        hbins1, hsa_len.trans hmax_ofNat.symm, by rw [hmax_ofNat]; exact hmax_lt61,
                        hm_ext1, fun u1 sa_1 m_ext1 hsa1_len hu1_le hceq1 hm_e1 => ?_⟩
                    rw [hmax_ofNat] at hsa1_len hu1_le
                    c0_hsteps_nogrp
                    refine wp_join_group
                      (fun (gl', ()) mem' =>
                        ExtractItePairPost maxA F_cur c s s' g_len g_cap stk1 stk2 R gl' mem')
                      (fun J2085 ⟨gl', ⟨⟩⟩ m2085 hinv2085 => by
                        c0_hsteps!; exact hJ1582 (gl', ()) m2085 hinv2085)
                      (fun J2085 hJ2085 => ?_)
                    c0_hsteps_nogrp
                    c0_hsplit
                    · have hm_cp2 : (FullMemNoWks3 c s' ⋆ array64 c.pWsort ws64_1 ⋆
                          (array64 stk1 sa_1 ⋆ (array64 stk2 sb ⋆ R))) m_ext1 := by
                        rw [sep_assoc (FullMemNoWks3 c s')]
                        exact sep_s12 (sep_s23 (sep3_l2r hm_e1))
                      c0_hcall hCopy
                      · refine ⟨c, F0, F_cur, s', ws64_1, array64 stk1 sa_1 ⋆ (array64 stk2 sb ⋆ R),
                            rfl, hd'.1, hd'.2.1, hd'.2.2.2.2.2.1, hd'.2.2.2.2.2.2, hl2_lt,
                            hws1_len.trans hmax_ofNat.symm, by rw [hmax_ofNat]; exact hmax_lt61,
                            hm_cp2, fun cnt2 ws64_2 m_cp2 hws2_len hcnt2_le hsort2 hbins2 hm2 => ?_⟩
                        rw [hmax_ofNat] at hws2_len hcnt2_le
                        c0_hsteps_nogrp
                        refine wp_join_group
                          (fun (gl', ()) mem' =>
                            ExtractItePairPost maxA F_cur c s s' g_len g_cap stk1 stk2 R gl' mem')
                          (fun J2588 ⟨gl', ⟨⟩⟩ m2588 hinv2588 => by
                            c0_hsteps!; exact hJ2085 (gl', ()) m2588 hinv2588)
                          (fun J2588 hJ2588 => ?_)
                        c0_hsteps_nogrp
                        c0_hsplit
                        · have hm_ext2 : (array64 c.pWsort ws64_2 ⋆ array64 stk2 sb ⋆
                              (FullMemNoWks3 c s' ⋆ (array64 stk1 sa_1 ⋆ R))) m_cp2 := by
                            rw [sep_assoc (array64 c.pWsort ws64_2)]
                            exact sep_s23 (sep_s34 (sep_s12 (sep3_l2r hm2)))
                          c0_hsteps_nogrp
                          c0_hcall hExt
                          · refine ⟨F_cur, s'.core.cur_vars, l2.toNat, ws64_2, sb,
                                FullMemNoWks3 c s' ⋆ (array64 stk1 sa_1 ⋆ R), by omega, by omega,
                                hsort2, hbins2, hsb_len.trans hmax_ofNat.symm,
                                by rw [hmax_ofNat]; exact hmax_lt61, hm_ext2,
                                fun u2 sb_1 m_ext2 hsb1_len hu2_le hceq2 hm_e2 => ?_⟩
                            rw [hmax_ofNat] at hsb1_len hu2_le
                            c0_hsteps_nogrp
                            refine wp_join_group
                              (fun (gl', ()) mem' => ExtractItePairPost maxA F_cur c s s' g_len
                                g_cap stk1 stk2 R gl' mem')
                              (fun J3091 ⟨gl', ⟨⟩⟩ m3091 hinv3091 => by
                                c0_hsteps!; exact hJ2588 (gl', ()) m3091 hinv3091)
                              (fun J3091 hJ3091 => ?_)
                            c0_hsteps_nogrp
                            c0_hsplit
                            · refine wp_join_group
                                (fun (gl', ()) mem' => ExtractItePairPost maxA F_cur c s s' g_len
                                  g_cap stk1 stk2 R gl' mem')
                                (fun J3593 ⟨gl', ⟨⟩⟩ m3593 hinv3593 => by
                                  c0_hsteps!; exact hJ3091 (gl', ()) m3593 hinv3593)
                                (fun J3593 hJ3593 => ?_)
                              c0_hsplit
                              · have hsw : sw = true := hc; subst hsw
                                have hargs' : l1 = v553 ∧ l2 = v552 ∧ stk1 = c.pWorkStk1 ∧
                                    stk2 = c.pWorkStk2 := by simpa using hargs
                                rcases hargs' with ⟨rfl, rfl, rfl, rfl⟩
                                have hm_mg : (FullMemNoWks3 c s' ⋆ array64 c.pWorkStk1 sa_1 ⋆
                                    array64 c.pWorkStk2 sb_1 ⋆ (array64 c.pWsort ws64_2 ⋆ R))
                                    m_ext2 := by
                                  rw [sep_assoc (FullMemNoWks3 c s' ⋆ array64 c.pWorkStk1 sa_1),
                                    sep_assoc (FullMemNoWks3 c s')]
                                  exact sep_s34 (sep_s23 (sep_s34 (sep_s12 (sep_s23
                                    (sep3_l2r hm_e2)))))
                                c0_hcall hMerge
                                · refine ⟨maxA, c, F0, F_cur, s', sa_1, sb_1,
                                    array64 c.pWsort ws64_2 ⋆ R, hmax3, hmax64, rfl, hd'.1, hd'.2.1,
                                    hcore ▸ hcv3, hv552_lt, hcap_scr, by omega, by omega, by omega,
                                    by omega, by rwa [hv553_lit] at hceq1, hceq2, hcore ▸ hseq,
                                    hm_mg, fun ret scr' m_mg hscr' hret_rng hpref' hseq' hm_m => ?_⟩
                                  rcases hret_rng hgl_le with ⟨hret1, hret2⟩; c0_hsteps!
                                  refine hJ3593 (ret, ()) m_mg (extract_ite_post_merge hws2_len
                                    hsa1_len hsb1_len hscr' (by omega) hret2
                                    (fun k hk => by rw [hpref' k (by omega)]; exact hpref k hk)
                                    (hcore ▸ hseq')
                                    (sep5_r2l (sep_s23 (sep_s34 (sep4_l2r hm_m)))))
                              · have hsw_f : sw = false := hc; subst hsw_f
                                have hargs' : l1 = v552 ∧ l2 = v553 ∧ stk1 = c.pWorkStk2 ∧
                                    stk2 = c.pWorkStk1 := by simpa using hargs
                                rcases hargs' with ⟨rfl, rfl, rfl, rfl⟩
                                have hm_mg : (FullMemNoWks3 c s' ⋆ array64 c.pWorkStk1 sb_1 ⋆
                                    array64 c.pWorkStk2 sa_1 ⋆ (array64 c.pWsort ws64_2 ⋆ R))
                                    m_ext2 := by
                                  rw [sep_assoc (FullMemNoWks3 c s' ⋆ array64 c.pWorkStk1 sb_1),
                                    sep_assoc (FullMemNoWks3 c s')]
                                  exact sep_s34 (sep_s23 (sep_s12 (sep_s23 (sep3_l2r hm_e2))))
                                c0_hcall hMerge
                                · refine ⟨maxA, c, F0, F_cur, s', sb_1, sa_1,
                                    array64 c.pWsort ws64_2 ⋆ R, hmax3, hmax64, rfl, hd'.1, hd'.2.1,
                                    hcore ▸ hcv3, hv552_lt, hcap_scr, by omega, by omega, by omega,
                                    by omega, by rwa [hv553_lit] at hceq2, hceq1, hcore ▸ hseq,
                                    hm_mg, fun ret scr' m_mg hscr' hret_rng hpref' hseq' hm_m => ?_⟩
                                  rcases hret_rng hgl_le with ⟨hret1, hret2⟩; c0_hsteps!
                                  refine hJ3593 (ret, ()) m_mg (extract_ite_post_merge hws2_len
                                    hsa1_len hsb1_len hscr' (by omega) hret2
                                    (fun k hk => by rw [hpref' k (by omega)]; exact hpref k hk)
                                    (hcore ▸ hseq')
                                    (sep5_r2l (sep_s34 (sep_s23 (sep_s34 (sep4_l2r hm_m))))))
                            · c0_hsteps!
                              exact hJ3091 (gl, ()) m_ext2 ⟨s'.scratch.scratch_buf, ws64_2, sa_1,
                                sb_1, hws2_len, hsa1_len, hsb1_len,
                                hd'.1.scratch_ok.scratch_buf_len, hgl_ge, hgl_le, hpref,
                                hcore ▸ hseq,
                                sep5_r2l (sep_s34 (sep_s12 (sep_s23 (sep3_l2r hm_e2))))⟩
                        · c0_hsteps!
                          exact hJ2588 (gl, ()) m_cp2 ⟨s'.scratch.scratch_buf, ws64_2, sa_1, sb,
                            hws2_len, hsa1_len, hsb_len, hd'.1.scratch_ok.scratch_buf_len, hgl_ge,
                            hgl_le, hpref, hcore ▸ hseq, sep5_r2l (sep3_l2r hm2)⟩
                    · c0_hsteps!; exact hJ2085 (gl, ()) m_ext1 ⟨s'.scratch.scratch_buf, ws64_1,
                        sa_1, sb, hws1_len, hsa1_len, hsb_len, hd'.1.scratch_ok.scratch_buf_len,
                        hgl_ge, hgl_le, hpref, hcore ▸ hseq,
                        sep5_r2l (sep_s12 (sep_s23 (sep3_l2r hm_e1)))⟩
                · c0_hsteps!; exact hJ1582 (gl, ()) m_cp1 ⟨s'.scratch.scratch_buf, ws64_1, sa, sb,
                    hws1_len, hsa_len, hsb_len, hd'.1.scratch_ok.scratch_buf_len, hgl_ge, hgl_le,
                    hpref, hcore ▸ hseq, sep5_r2l (sep3_l2r hm1)⟩
          · rcases focus_full_wks3_u64 hd'.1 hm28 with ⟨ws64, s1, s2, hws, hs1, hs2, hm_foc⟩
            c0_hsteps_nogrp; c0_hsplit
            · c0_hsteps!; exact hJ1575 (v553, v552, c.pWorkStk1, c.pWorkStk2, true, ()) _
                ⟨ws64, s1, s2, hws, hs1, hs2, by simp, hm_foc⟩
            · c0_hsteps!; refine hJ1575 (v552, v553, c.pWorkStk2, c.pWorkStk1, false, ()) _
                ⟨ws64, s2, s1, hws, hs2, hs1, by simp, ?_⟩
              rw [sep_assoc (FullMemNoWks3 c s' ⋆ array64 c.pWsort ws64), sep_comm
                (array64 c.pWorkStk2 s2), ← sep_assoc (FullMemNoWks3 c s' ⋆ array64 c.pWsort ws64)]
              exact hm_foc
      · c0_hsteps!; exact hJ38 (ticks, gl, ()) m28 ⟨s', hd', hcore, htm, htr, hes, hel, hll,
          hasz, hrsz, by omega, hgl_ge, hgl_le, hpref, hseq, hm28⟩
      · c0_hsteps!; exact hJ38 (ticks, gl, ()) m28 ⟨s', hd', hcore, htm, htr, hes, hel, hll,
          hasz, hrsz, by omega, hgl_ge, hgl_le, hpref, hseq, hm28⟩
    · c0_hsteps!; exact hQ gl s' m28 hd' hcore htm htr hes hel hll hasz hrsz hgl_ge hgl_le
        hpref hseq hm28
    · c0_hsteps!; exact hQ gl s' m28 hd' hcore htm htr hes hel hll hasz hrsz hgl_ge hgl_le
        hpref hseq hm28
    · c0_hsteps!; exact hQ gl s' m28 hd' hcore htm htr hes hel hll hasz hrsz hgl_ge hgl_le
        hpref hseq hm28

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence
