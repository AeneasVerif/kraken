module

public import LeanQbe.T.Examples.Kissat.FullM6SweepProofVar1b

/-!
# Kissat `D-Full` M6 — Equivalent-Literal Substitution (ELS) Proofs (`29..30/39`)

Parametric `(Γ : Env)` `Func.wp` proofs for `2/39` owned functions (`30/39` cumulative):
- `29/39`: `full_m6_els_ar_wp` (`m6ElsArSpec`)
- `30/39`: `full_m6_els_lit_wp` (`m6ElsLitSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullArenaTactics
open scoped FullArenaTactics M6SweepTactics

/-! ## 1. BitVector, Pigeonhole, Entailment, & `FullDenseInvW` Transition Helpers -/

namespace M6ElsBv

@[scoped bv_c0] theorem m6_els_bv32_xor1_toNat (x : BitVec 32) :
    (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by simp

@[scoped bv_c0] theorem m6_els_bv32_xor1_ofnat (x : BitVec 32) :
    (x ^^^ (1 : BitVec 32)).toNat = x.toNat ^^^ 1 := by simp

@[scoped bv_c0] theorem m6_els_bv64_shl1_bv (x : BitVec 64) :
    (x <<< 1#64).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem m6_els_bv64_shl1_ofnat (x : BitVec 64) :
    (x <<< (1 : BitVec 64)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem m6_els_bv64_shl1_nat (x : BitVec 64) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem m6_els_bv32_shl1_bv (x : BitVec 32) :
    (x <<< 1#32).toNat = (2 * x.toNat) % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem m6_els_bv32_shl1_ofnat (x : BitVec 32) :
    (x <<< (1 : BitVec 32)).toNat = (2 * x.toNat) % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem m6_els_bv32_shl1_nat (x : BitVec 32) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem m6_els_bv32_shr1_nat (x : BitVec 32) :
    (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem m6_bv8_bounds (v : BitVec 8) : -128 ≤ v.toInt ∧ v.toInt < 128 := by
  unfold BitVec.toInt; have := v.isLt; split <;> omega

private theorem m6_toInt_sext32 (v : BitVec 8) : (v.signExtend 32).toInt = v.toInt := by
  rw [BitVec.toInt_signExtend, show min 32 8 = 8 from rfl]
  have ⟨h1, h2⟩ := m6_bv8_bounds v
  unfold Int.bmod; dsimp only; split <;> omega

@[scoped bv_c0] theorem m6_els_bv8_sgt0 (v : BitVec 8) :
    (0#32).slt (v.signExtend 32) = (0#8).slt v := by
  simp only [BitVec.slt, m6_toInt_sext32]; rfl

@[scoped bv_c0] theorem m6_els_bv8_eq0 (v : BitVec 8) :
    (v.signExtend 32 == 0#32) = (v == 0#8) := by
  by_cases h : v = 0#8
  · subst h; decide
  · simp only [beq_false_of_ne h]
    apply beq_false_of_ne; intro heq
    have h1 : v.toInt = 0 := by rw [← m6_toInt_sext32, heq]; rfl
    apply h; unfold BitVec.toInt at h1
    apply BitVec.eq_of_toNat_eq
    change v.toNat = 0; split at h1 <;> omega

end M6ElsBv

open M6ElsBv

private theorem nodup_nat_lt_len :
    ∀ {N : Nat} {xs : List Nat}, xs.Nodup → (∀ x ∈ xs, x < N) → xs.length ≤ N
  | 0, xs, _, hlt => by
    cases xs with
    | nil => exact Nat.zero_le 0
    | cons x _ => exfalso; have := hlt x List.mem_cons_self; omega
  | M + 1, xs, hnd, hlt => by
    have hnd' : (xs.erase M).Nodup := hnd.erase M
    have hlt' : ∀ x ∈ xs.erase M, x < M := by
      intro x hx
      have hxm : x ∈ xs := List.mem_of_mem_erase hx
      have hne : x ≠ M := fun heq => by
        subst heq; exact absurd hx (List.Nodup.not_mem_erase hnd)
      have := hlt x hxm; omega
    have ih := nodup_nat_lt_len hnd' hlt'
    by_cases hm : M ∈ xs
    · have hl := List.length_erase_of_mem hm; omega
    · rw [List.erase_of_not_mem hm] at ih; omega

private theorem list_take_set_succ {α : Type _} (xs : List α) {n : Nat} (hn : n < xs.length)
    (x : α) : (xs.set n x).take (n + 1) = xs.take n ++ [x] := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_set]; omega
  · intro i hi1 hi2
    simp only [List.length_take, List.length_set] at hi1
    have hi : i < n + 1 := by omega
    rw [List.getElem_take]
    by_cases hin : i < n
    · rw [List.getElem_set_ne (by omega), List.getElem_append_left (by
        rw [List.length_take]; omega), List.getElem_take]
    · have hie : i = n := by omega
      subst hie
      rw [List.getElem_set_self (by rw [List.length_set]; exact hn),
        List.getElem_append_right (by rw [List.length_take]; omega)]
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)]

theorem m6_getElem_congr {α : Type _} {xs : List α} {i j : Nat} (h : i = j)
    (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

theorem m6_unsat_of_nil_entails {f : CNF Nat} (h : f.EntailsClause (cnfClause [])) :
    f.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp h α hα)
  simp [clauseEvalVal] at this

private theorem nodup_of_map_div2 {xs : List (BitVec 32)}
    (h : (xs.map fun x => x.toNat / 2).Nodup) : (xs.map BitVec.toNat).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h ⊢
    refine ⟨?_, ih h.2⟩
    rintro ⟨y, hy, hyx⟩
    exact h.1 ⟨y, hy, by omega⟩

private theorem nat_xor1_cases (x : Nat) : x ^^^ 1 = if x % 2 = 0 then x + 1 else x - 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor]
  rcases i with _ | i
  · simp only [Nat.testBit_zero, show (1 : Nat) % 2 = 1 from rfl, decide_true, Bool.xor_true]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h] <;> omega
  · simp only [Nat.testBit_succ, show (1 : Nat) / 2 = 0 from rfl, Nat.zero_testBit,
      Bool.xor_false]
    split <;> rename_i h
    · have : (x + 1) / 2 = x / 2 := by omega
      rw [this]
    · have : (x - 1) / 2 = x / 2 := by omega
      rw [this]

private theorem m6_nodup_getElem_ne {α : Type _} :
    ∀ {xs : List α}, xs.Nodup → ∀ {i j : Nat} (hi : i < xs.length) (hj : j < xs.length),
      i ≠ j → xs[i]'hi ≠ xs[j]'hj
  | [], _, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: xs, hnd, 0, j + 1, _, hj, _ => fun heq => by
    simp only [List.nodup_cons] at hnd
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
    exact hnd.1 (heq ▸ List.getElem_mem _)
  | _ :: xs, hnd, i + 1, 0, hi, _, _ => fun heq => by
    simp only [List.nodup_cons] at hnd
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at heq
    exact hnd.1 (heq.symm ▸ List.getElem_mem _)
  | _ :: xs, hnd, i + 1, j + 1, hi, hj, hne => by
    simp only [List.nodup_cons] at hnd
    exact m6_nodup_getElem_ne hnd.2 (by simp at hi; exact hi) (by simp at hj; exact hj)
      (by omega)
  | _ :: _, _, 0, 0, _, _, hne => absurd rfl hne

private theorem m6_list_set2_eq {α : Type _} (xs : List α) {i1 j1 i2 j2 : Nat}
    {v1 v2 w1 w2 : α} (hi : i1 = j1) (hj : i2 = j2) (hv1 : v1 = w1) (hv2 : v2 = w2) :
    (xs.set i1 v1).set i2 v2 = (xs.set j1 w1).set j2 w2 := by
  subst hi hj hv1 hv2; rfl

private theorem bv8_zext32_eq0_iff (v : BitVec 8) :
    BitVec.setWidth 32 v = 0#32 ↔ v = 0#8 := by
  constructor <;> intro h <;> apply BitVec.eq_of_toNat_eq <;>
    have h1 := congrArg BitVec.toNat h
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h1
    have := v.isLt; rw [Nat.mod_eq_of_lt (by omega)] at h1; exact h1
  · simp only [h1, BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem m6_bv32_lit_or1 (x : BitVec 32) (he : x.toNat % 2 = 0) :
    x ||| 1#32 = x ^^^ 1#32 := by
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_xor]
  by_cases h0 : i = 0
  · subst h0
    have hx : x[0] = false := by
      rw [BitVec.getElem_eq_testBit_toNat]; simp [Nat.testBit_zero, he]
    simp [hx]
  · have h1 : (1#32 : BitVec 32)[i] = false := by
      rw [BitVec.getElem_eq_testBit_toNat, show (1#32 : BitVec 32).toNat = 1 from rfl]
      have hp : 2 ≤ 2 ^ i := Nat.le_self_pow (by omega) 2
      exact Nat.testBit_lt_two_pow (by omega)
    simp [h1]

theorem m6_bv32_shl1_even (v : BitVec 64) (hv : 2 * v.toNat < 2 ^ 32) :
    (BitVec.setWidth 32 (v <<< 1#64)).toNat = 2 * v.toNat ∧
    (BitVec.setWidth 32 (v <<< 1#64)).toNat % 2 = 0 := by
  have hs : (v <<< 1#64).toNat = 2 * v.toNat := by
    rw [m6_els_bv64_shl1_bv, Nat.mod_eq_of_lt (by omega)]
  have ht : (BitVec.setWidth 32 (v <<< 1#64)).toNat = 2 * v.toNat := by
    rw [BitVec.toNat_setWidth, hs, Nat.mod_eq_of_lt hv]
  exact ⟨ht, by omega⟩

private theorem m6_bv32_mask7f_props {sz : BitVec 32} (h3 : 3 ≤ sz.toNat)
    (hlt : sz.toNat < 2 ^ 31) :
    let w := sz &&& 0x7FFFFFFF#32
    w ≠ 0xFFFFFFFF#32 ∧ (w &&& 0x80000000#32) = 0#32 ∧ 3 ≤ w.toNat := by
  have hbit : ((sz &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 := by
    rw [BitVec.and_assoc, show (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 by decide,
      BitVec.and_zero]
  have hne : (sz &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 := by
    intro heq; rw [heq] at hbit; revert hbit; decide
  have hto : (sz &&& 0x7FFFFFFF#32).toNat = sz.toNat := by
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]
  exact ⟨hne, hbit, by omega⟩

private theorem m6_els_bit19_or_garb (x : BitVec 32) :
    ((x ||| 0x00080000#32) &&& 0x00080000#32) ≠ 0#32 := by
  intro h; have := congrArg (·[19]) h; simp at this

private theorem m6_els_bit23_or_shrk (x : BitVec 32) :
    ((x ||| 0x00800000#32) &&& 0x00800000#32) ≠ 0#32 := by
  intro h; have := congrArg (·[23]) h; simp at this

private theorem m6_els_bit19_or_shrk (x : BitVec 32) :
    ((x ||| 0x00800000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or]
  have h19 : (0x00080000#32)[i] = true → (0x00800000#32)[i] = false := by revert i hi; decide
  cases h : (0x00080000#32)[i] <;> simp [h19, h]

theorem m6_entails_bin_subst {f : CNF Nat} {a b a' b' : Nat}
    (ha : LitEquiv f a a') (hb : LitEquiv f b b')
    (hc : f.EntailsClause (cnfClause [a, b])) :
    f.EntailsClause (cnfClause [a', b']) := by
  rw [CNF.entails_clause_def] at hc ⊢
  intro α hα
  have h1 := (clauseEvalVal_iff α _).mpr (hc α hα)
  rw [← clauseEvalVal_iff]
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at h1 ⊢
  rw [← litEquiv_eval hα ha, ← litEquiv_eval hα hb]; exact h1

theorem m6_entails_unit_of_dup {f : CNF Nat} {a : Nat}
    (hc : f.EntailsClause (cnfClause [a, a])) : f.EntailsClause (cnfClause [a]) := by
  rw [CNF.entails_clause_def] at hc ⊢
  intro α hα
  have h1 := (clauseEvalVal_iff α _).mpr (hc α hα)
  rw [← clauseEvalVal_iff]
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at h1 ⊢
  simpa using h1

private theorem m6_entails_clause_subst {f : CNF Nat} {cs cs' : List Nat}
    (hmap : ∀ l ∈ cs, ∃ l' ∈ cs', LitEquiv f l l')
    (hc : f.EntailsClause (cnfClause cs)) : f.EntailsClause (cnfClause cs') := by
  rw [CNF.entails_clause_def] at hc ⊢
  intro α hα
  have h1 := (clauseEvalVal_iff α _).mpr (hc α hα)
  rw [← clauseEvalVal_iff]
  rw [clauseEvalVal, List.any_eq_true] at h1 ⊢
  obtain ⟨l, hl, hsat⟩ := h1
  obtain ⟨l', hl', heq⟩ := hmap l hl
  exact ⟨l', hl', by rw [← litEquiv_eval hα heq]; exact hsat⟩

theorem m6_litEquiv_neg {f : CNF Nat} {a b : Nat} (h : LitEquiv f a b) :
    LitEquiv f (a ^^^ 1) (b ^^^ 1) := by
  constructor
  · have h1 := h.2
    rw [CNF.entails_clause_def] at h1 ⊢; intro α hα
    have h2 := (clauseEvalVal_iff α _).mpr (h1 α hα)
    rw [← clauseEvalVal_iff]
    simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
      show a ^^^ 1 = litNeg a from rfl, show b ^^^ 1 = litNeg b from rfl,
      litNeg_litNeg] at h2 ⊢
    simpa [Bool.or_comm] using h2
  · have h1 := h.1
    rw [CNF.entails_clause_def] at h1 ⊢; intro α hα
    have h2 := (clauseEvalVal_iff α _).mpr (h1 α hα)
    rw [← clauseEvalVal_iff]
    simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
      show a ^^^ 1 = litNeg a from rfl, show b ^^^ 1 = litNeg b from rfl,
      litNeg_litNeg] at h2 ⊢
    simpa [Bool.or_comm] using h2

theorem m6_litEquiv_unsat_contra {f : CNF Nat} {a b : Nat}
    (heq : LitEquiv f a b) (ha : f.EntailsClause (cnfClause [a]))
    (hb : f.EntailsClause (cnfClause [b ^^^ 1])) : f.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro β hβ
  have h1 := litEquiv_eval hβ heq
  have h2 := (clauseEvalVal_iff β _).mpr (CNF.entails_clause_def.mp ha β hβ)
  have h3 := (clauseEvalVal_iff β _).mpr (CNF.entails_clause_def.mp hb β hβ)
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
    show b ^^^ 1 = litNeg b from rfl, evalLitVal_litNeg] at h2 h3
  rw [h1] at h2; rw [h2] at h3; cases h3

theorem m6_lvl0_false_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {l : Nat} (hlt : l < 2 * k.cur_vars) (hf : k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1]) := by
  obtain ⟨i, hi, htrl⟩ := (hw.vals_false_iff l hlt).mp hf
  have hl0 : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le i hi; omega
  have hent := hw.level0_sound i hi hl0; rwa [htrl] at hent

theorem m6_lvl0_true_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {l : Nat} (hlt : l < 2 * k.cur_vars) (ht : k.vals[l]?.getD 0#8 = 1#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l]) := by
  obtain ⟨i, hi, htrl⟩ := (hw.vals_true_iff l hlt).mp ht
  have hl0 : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le i hi; omega
  have hent := hw.level0_sound i hi hl0; rwa [htrl] at hent

private theorem m6_denseSlice_step_bin {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} {w0 : BitVec 32} (hs : DenseWatchSliceOk F_cur k lit p rem)
    (hpos : 0 < rem) (hp : k.wstk[p]? = some w0)
    (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) :
    w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
    DenseWatchSliceOk F_cur k lit (p + 1) (rem - 1) := by
  cases hs with
  | empty => omega
  | bin hp' _ hne hlt hent hrest =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact ⟨hne, hlt, hent, hrest⟩
  | occ hp' _ hflag _ _ _ _ =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact absurd hflag hbin

private theorem m6_denseSlice_step_occ {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} {w0 : BitVec 32} (hs : DenseWatchSliceOk F_cur k lit p rem)
    (hpos : 0 < rem) (hp : k.wstk[p]? = some w0)
    (hocc : (w0 &&& 0x80000000#32) = 0#32) :
    2 ≤ rem ∧ 3 ≤ w0.toNat ∧
    ∃ cr, k.wstk[p + 1]? = some cr ∧ cr.toNat < 0x80000000 ∧
      cr.toNat ∈ fullArenaClauseRefsCore k ∧
      DenseWatchSliceOk F_cur k lit (p + 2) (rem - 2) := by
  cases hs with
  | empty => omega
  | bin hp' hflag _ _ _ _ =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact absurd hocc hflag
  | occ hp' hp1 _ h3 hlt href hrest =>
    rw [hp] at hp'; cases Option.some.inj hp'
    exact ⟨by omega, h3, _, hp1, hlt, href, hrest⟩

private theorem m6_arenaVarsNodup_eq {s s' : FullState}
    (ha : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (h : FullArenaVarsNodup s) : FullArenaVarsNodup s' := by
  intro r hr hng
  have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [ha, hal]
  have hgarb : fullArenaClauseGarb s' r = fullArenaClauseGarb s r := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [ha]
  have hlits : fullArenaClauseLits s' r = fullArenaClauseLits s r := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [ha]
  rw [hrefs] at hr; rw [hgarb] at hng; rw [hlits]; exact h r hr hng

private theorem m6_lits_eq_of_hold {ar1 ar2 : List (BitVec 32)} {cr sz : Nat}
    (hb1 : cr + 3 + sz ≤ ar1.length) (hb2 : cr + 3 + sz ≤ ar2.length)
    (h : ∀ j < sz, ar2[cr + 3 + j]? = ar1[cr + 3 + j]?) :
    ((ar2.drop (cr + 3)).take sz).map BitVec.toNat =
      ((ar1.drop (cr + 3)).take sz).map BitVec.toNat := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop]; omega
  · intro j hj1 _
    simp only [List.length_map, List.length_take, List.length_drop] at hj1
    have hj : j < sz := by omega
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
    have hq := h j hj
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hq
    exact congrArg BitVec.toNat (Option.some.inj hq)

theorem m6_denseInvW_set_inconsistent {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    (huns : (cnfOfClauses F_cur).Unsat) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with inconsistent := 1#64 } } := by
  have hcl := hinv.1.core_ok; have hw := hinv.2.1
  refine ⟨⟨{ hcl with vals_len := hcl.vals_len }, hinv.1.scratch_ok⟩,
    { hw with
      inconsistent_sound := fun _ => huns
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
    hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem m6_denseInvW_set_oom {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with oom := 1#64 } } :=
  ⟨⟨{ hinv.1.core_ok with vals_len := hinv.1.core_ok.vals_len }, hinv.1.scratch_ok⟩,
   { hinv.2.1 with
     arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
     watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

theorem m6_denseInvW_set_repr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {repr' : List (BitVec 32)} (hl : repr'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with repr := repr' } } :=
  ⟨⟨{ hinv.1.core_ok with repr_len := hl }, hinv.1.scratch_ok⟩,
   { hinv.2.1 with
     arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
     watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   hinv.2.2.1, m6_arenaVarsNodup_eq rfl rfl hinv.2.2.2.1,
   hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem m6_denseInvW_set_litMark_clear {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {lm' : List (BitVec 8)} {tmp' : List (BitVec 32)}
    (hlm : lm'.length = 2 * c.max_vars) (htmp : tmp'.length = c.max_vars)
    (hclear : ∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 = 0#8) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with lit_mark := lm', tmp := tmp' } } :=
  ⟨⟨{ hinv.1.core_ok with lit_mark_len := hlm, tmp_len_arr := htmp }, hinv.1.scratch_ok⟩,
   { hinv.2.1 with
     arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
     watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   ⟨hinv.2.2.1.1, hclear⟩, m6_arenaVarsNodup_eq rfl rfl hinv.2.2.2.1,
   hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

theorem m6_denseInvW_after_addUnit {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
      phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss'}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te',
                            propagated := prop', cur_level := cl', unassigned := unass',
                            unflushed := unfl', inconsistent := inc' }
      scratch := { s.scratch with phases := phases', target_assigned := ta',
                                  best_assigned := ba', phases_target := pt',
                                  phases_best := pb', heap := hp', pos := ps',
                                  heap_len := hl', q_search_idx := qsi',
                                  q_search_stamp := qss' } } : FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                    trl := trl', trail_pos := tp', trail_end := te',
                    propagated := prop', cur_level := cl', unassigned := unass',
                    unflushed := unfl', inconsistent := inc' })
    (hcl0 : cl' = 0) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              propagated := prop', cur_level := cl', unassigned := unass',
                              unflushed := unfl', inconsistent := inc' }
        scratch := { s.scratch with phases := phases', target_assigned := ta',
                                    best_assigned := ba', phases_target := pt',
                                    phases_best := pb', heap := hp', pos := ps',
                                    heap_len := hl', q_search_idx := qsi',
                                    q_search_stamp := qss' } } :=
  ⟨hlen', hw', hinv.2.2.1, m6_arenaVarsNodup_eq rfl rfl hinv.2.2.2.1,
   ⟨fun i hi => hinv.2.2.2.2.1.1 i hi, hinv.2.2.2.2.1.2⟩, hcl0, hinv.2.2.2.2.2.2⟩

private theorem m6_denseInvW_after_addBin {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb' oom' inc'
      phases' wsort'}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                            oom := oom', inconsistent := inc' }
      scratch := { s.scratch with phases := phases', wsort := wsort' } } : FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                    trl := trl', trail_pos := tp', trail_end := te',
                    unassigned := unass', unflushed := unfl', wvec := wvec',
                    wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                    oom := oom', inconsistent := inc' }) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                              oom := oom', inconsistent := inc' }
        scratch := { s.scratch with phases := phases', wsort := wsort' } } :=
  ⟨hlen', hw', hinv.2.2.1, m6_arenaVarsNodup_eq rfl rfl hinv.2.2.2.1,
   ⟨fun i hi => hinv.2.2.2.2.1.1 i hi, hinv.2.2.2.2.1.2⟩,
   hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

theorem m6_denseInvW_after_extPush2 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    (hsok : s'.LengthsOk c) (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hext : s'.scratch.extend_len ≤ c.extend_cap) :
    FullDenseInvW c F0 F_cur s' ∧ s'.core = s.core := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [heq]
  have hext_ok : FullExtScratchOk c s' :=
    ⟨fun i hi => by
      dsimp only [FullLastLearnedWf]
      rw [hll]
      rcases hinv.2.2.2.2.1.1 i hi with h | h
      · exact Or.inl h
      · exact Or.inr (hrefs ▸ h),
     hext⟩
  exact ⟨⟨hsok, heq ▸ hinv.2.1, by unfold FullLitMarksClear FullMrkZero; rw [heq]; exact hinv.2.2.1,
    m6_arenaVarsNodup_eq (by rw [heq]) (by rw [heq]) hinv.2.2.2.1,
    hext_ok, by rw [heq]; exact hinv.2.2.2.2.2.1, by rw [heq]; exact hinv.2.2.2.2.2.2⟩, heq⟩

theorem m6_denseInvW_set_flags_unass {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {flags' : List (BitVec 32)} {unass' : BitVec 64} (hfll : flags'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with flags := flags', unassigned := unass' } } :=
  ⟨⟨{ hinv.1.core_ok with flags_len := hfll }, hinv.1.scratch_ok⟩,
   { hinv.2.1 with
     arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
     watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   hinv.2.2.1, m6_arenaVarsNodup_eq rfl rfl hinv.2.2.2.1,
   hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

theorem m6_denseInvW_set_fl_subst {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {flags' : List (BitVec 32)} {sc' : BitVec 64} (hfll : flags'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with flags := flags' }
               scratch := { s.scratch with subst_cnt := sc' } } :=
  ⟨⟨{ hinv.1.core_ok with flags_len := hfll },
    { hinv.1.scratch_ok with scratch_buf_len := hinv.1.scratch_ok.scratch_buf_len }⟩,
   { hinv.2.1 with
     arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
     watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   hinv.2.2.1, m6_arenaVarsNodup_eq rfl rfl hinv.2.2.2.1,
   hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem m6_denseInvW_markGarb {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (ag' : BitVec 64) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullDenseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have hcl := hinv.1.core_ok; have hw := hinv.2.1; have hcl0 := hinv.2.2.2.2.2.1
  have hmg := hw.arena.markGarb hcl href ag'
  have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := hmg.1
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with arena_len_arr := by simp [s', hcl.arena_len_arr] }, hinv.1.scratch_ok⟩
  have hnd' : FullArenaVarsNodup s' :=
    FullArenaVarsNodup.of_markGarb ⟨hinv.1, F_cur, hw⟩ hinv.2.2.2.1 href ag'
  have hno_rsn : ∀ idx < s.core.trail_end,
      s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun idx hidx => hw.level0_rsn_none idx hidx (by have := hw.lvl_le idx hidx; omega)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := hmg.2
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl
        fun r hr => by change r ∈ fullArenaClauseRefs s'; rw [hrefs]; exact hr
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne }
  exact ⟨⟨hlen', hw', hinv.2.2.1, hnd',
    FullExtScratchOk.of_pres hinv.2.2.2.2.1 ⟨rfl, rfl⟩ (fun r hr => hrefs ▸ hr),
    hcl0, hinv.2.2.2.2.2.2⟩, hrefs⟩

private def mkWatchCore (core : FullCoreState) (wvec' wstk' : List (BitVec 32))
    (wlen' : Nat) (wu' : BitVec 64) : FullCoreState :=
  { core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }

private theorem m6_denseInvW_watchPush {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {rl w0 w1 : BitVec 32} {ok : Bool}
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wu' : BitVec 64} {wsort' : List (BitVec 32)}
    (hsok' : ({ s with
      core := mkWatchCore s.core wvec' wstk' wlen' wu'
      scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hlay' : WatchStackLayout (mkWatchCore s.core wvec' wstk' wlen' wu'))
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hsz : 3 ≤ w0.toNat)
    (hlt : w1.toNat < 0x80000000) (href : w1.toNat ∈ fullArenaClauseRefs s)
    (hother : ∀ l < 2 * s.core.cur_vars, l ≠ rl.toNat →
      fullWatchSizeCore (mkWatchCore s.core wvec' wstk' wlen' wu') l = fullWatchSize s l ∧
      ∀ k < fullWatchSize s l,
        wstk'[fullWatchOffCore (mkWatchCore s.core wvec' wstk' wlen' wu') l + k]? =
          s.core.wstk[fullWatchOff s l + k]?)
    (hok_t : ok = true →
      rl.toNat < 2 * s.core.cur_vars ∧
      fullWatchSizeCore (mkWatchCore s.core wvec' wstk' wlen' wu') rl.toNat =
        fullWatchSize s rl.toNat + 2 ∧
      (∀ k < fullWatchSize s rl.toNat,
        wstk'[fullWatchOffCore (mkWatchCore s.core wvec' wstk' wlen' wu') rl.toNat + k]? =
          s.core.wstk[fullWatchOff s rl.toNat + k]?) ∧
      wstk'[fullWatchOffCore (mkWatchCore s.core wvec' wstk' wlen' wu') rl.toNat +
        fullWatchSize s rl.toNat]? = some w0 ∧
      wstk'[fullWatchOffCore (mkWatchCore s.core wvec' wstk' wlen' wu') rl.toNat +
        fullWatchSize s rl.toNat + 1]? = some w1)
    (hok_f : ok = false → rl.toNat < 2 * s.core.cur_vars →
      fullWatchSizeCore (mkWatchCore s.core wvec' wstk' wlen' wu') rl.toNat =
        fullWatchSize s rl.toNat ∧
      ∀ k < fullWatchSize s rl.toNat,
        wstk'[fullWatchOffCore (mkWatchCore s.core wvec' wstk' wlen' wu') rl.toNat + k]? =
          s.core.wstk[fullWatchOff s rl.toNat + k]?) :
    FullDenseInvW c F0 F_cur
      { s with
        core := mkWatchCore s.core wvec' wstk' wlen' wu'
        scratch := { s.scratch with wsort := wsort' } } := by
  have hw := hinv.2.1
  have hwm := hw.watches
  unfold ModeWatchesInv at hwm
  rw [ite_eq_right (fun h0 => hinv.2.2.2.2.2.2 h0)] at hwm
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  let k' : FullCoreState := mkWatchCore s.core wvec' wstk' wlen' wu'
  have hdm' : k'.dense_mode ≠ 0#64 := hinv.2.2.2.2.2.2
  have hwat' : ModeWatchesInv F_cur k' := by
    unfold ModeWatchesInv
    rw [ite_eq_right (fun h0 => absurd h0 hdm')]
    dsimp only [k', mkWatchCore]
    refine ⟨hlay', fun l hl => ?_⟩
    by_cases hle : l = rl.toNat
    · subst hle
      cases ok with
      | false =>
        obtain ⟨hs, hslice⟩ := hok_f rfl hl
        change DenseWatchSliceOk F_cur k' rl.toNat (fullWatchOffCore k' rl.toNat)
          (fullWatchSizeCore k' rl.toNat)
        rw [hs]
        exact DenseWatchSliceOk.relocate (k := s.core) (k' := k') hrefl (le_refl _)
          (fun _ r => r) hslice (hwm.slices rl.toNat hl)
      | true =>
        obtain ⟨_, hs, hpre, hw0, hw1⟩ := hok_t rfl
        change DenseWatchSliceOk F_cur k' rl.toNat (fullWatchOffCore k' rl.toNat)
          (fullWatchSizeCore k' rl.toNat)
        rw [hs]
        exact DenseWatchSliceOk.append_occ (k := s.core) (k' := k') (le_refl _)
          (fun _ r => r) hpre (hwm.slices rl.toNat hl) hw0 hw1 hflag hsz hlt href
    · obtain ⟨hs, hslice⟩ := hother l hl hle
      change DenseWatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l)
      rw [hs]
      exact DenseWatchSliceOk.relocate (k := s.core) (k' := k') hrefl (le_refl _)
        (fun _ r => r) hslice (hwm.slices l hl)
  exact ⟨hsok', { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat' },
    hinv.2.2.1, m6_arenaVarsNodup_eq rfl rfl hinv.2.2.2.1,
    hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem m6_denseInvW_watchPop {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {l popK : Nat} (hl : l < 2 * s.core.cur_vars)
    (hpop : popK ≤ fullWatchSize s l) (wu' : BitVec 64)
    (hsl' : DenseWatchSliceOk F_cur s.core l (fullWatchOff s l + popK) (fullWatchSize s l - popK)) :
    let off := fullWatchOff s l
    let sz := fullWatchSize s l
    let wvec' := (s.core.wvec.set (2 * l) (BitVec.ofNat 32 (off + popK))).set (2 * l + 1)
      (BitVec.ofNat 32 (sz - popK))
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with wvec := wvec', wusable := wu' } } := by
  intro off sz wvec'
  let s' : FullState := { s with core := { s.core with wvec := wvec', wusable := wu' } }
  have hcl := hinv.1.core_ok; have hw := hinv.2.1
  have hwm := hw.watches; unfold ModeWatchesInv at hwm
  rw [ite_eq_right (fun h0 => hinv.2.2.2.2.2.2 h0)] at hwm
  have hcv_le := hcl.cur_vars_le; have hwvl := hcl.wvec_len
  have hbd_l := hwm.layout.bounds l hl
  have hoff_eq : off = fullWatchOffCore s.core l := rfl
  have hsz_eq : sz = fullWatchSizeCore s.core l := rfl
  have hpop_c : popK ≤ fullWatchSizeCore s.core l := hpop
  have hwc := c.hwcap; unfold dimacsBound at hwc
  have hwlen_le := hcl.wlen_le
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with wvec_len := by simp [s', wvec', hwvl] }, hinv.1.scratch_ok⟩
  have hlt32_o : off + popK < 2 ^ 32 := by rw [hoff_eq]; omega
  have hlt32_s : sz - popK < 2 ^ 32 := by rw [hsz_eq]; omega
  have hoff_l' : fullWatchOffCore s'.core l = off + popK := by
    unfold fullWatchOffCore; dsimp only [s', wvec']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32_o]
  have hsz_l' : fullWatchSizeCore s'.core l = sz - popK := by
    unfold fullWatchSizeCore; dsimp only [s', wvec']
    rw [List.getElem?_set_self (by rw [List.length_set]; omega), Option.getD_some,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32_s]
  have hoth : ∀ l' ≠ l,
      fullWatchOffCore s'.core l' = fullWatchOffCore s.core l' ∧
      fullWatchSizeCore s'.core l' = fullWatchSizeCore s.core l' := fun l' hne => by
    unfold fullWatchOffCore fullWatchSizeCore; dsimp only [s', wvec']
    exact ⟨by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)],
           by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]⟩
  have hlay' : WatchStackLayout s'.core := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro l' hl'
      by_cases hll : l' = l
      · rw [hll, hoff_l', hsz_l', hoff_eq, hsz_eq]
        change fullWatchOffCore s.core l + popK + (fullWatchSizeCore s.core l - popK) ≤
          s.core.wlen
        omega
      · obtain ⟨ho, hs⟩ := hoth l' hll; rw [ho, hs]; exact hwm.layout.bounds l' hl'
    · intro l' hl' hpos
      by_cases hll : l' = l
      · rw [hll, hoff_l', hoff_eq]; rw [hll, hsz_l', hsz_eq] at hpos
        have := hwm.layout.pos_off l hl (by omega); omega
      · obtain ⟨ho, hs⟩ := hoth l' hll; rw [ho]; rw [hs] at hpos
        exact hwm.layout.pos_off l' hl' hpos
    · intro l1 l2 h1 h2 hne hp1 hp2
      have hb1 : fullWatchOffCore s.core l1 ≤ fullWatchOffCore s'.core l1 ∧
          fullWatchOffCore s'.core l1 + fullWatchSizeCore s'.core l1 =
            fullWatchOffCore s.core l1 + fullWatchSizeCore s.core l1 ∧
          0 < fullWatchSizeCore s.core l1 := by
        by_cases h1l : l1 = l
        · rw [h1l, hoff_l', hsz_l', hoff_eq, hsz_eq]; rw [h1l, hsz_l', hsz_eq] at hp1
          exact ⟨by omega, by omega, by omega⟩
        · obtain ⟨ho, hs⟩ := hoth l1 h1l; rw [ho, hs]; exact ⟨le_refl _, rfl, hs ▸ hp1⟩
      have hb2 : fullWatchOffCore s.core l2 ≤ fullWatchOffCore s'.core l2 ∧
          fullWatchOffCore s'.core l2 + fullWatchSizeCore s'.core l2 =
            fullWatchOffCore s.core l2 + fullWatchSizeCore s.core l2 ∧
          0 < fullWatchSizeCore s.core l2 := by
        by_cases h2l : l2 = l
        · rw [h2l, hoff_l', hsz_l', hoff_eq, hsz_eq]; rw [h2l, hsz_l', hsz_eq] at hp2
          exact ⟨by omega, by omega, by omega⟩
        · obtain ⟨ho, hs⟩ := hoth l2 h2l; rw [ho, hs]; exact ⟨le_refl _, rfl, hs ▸ hp2⟩
      have hd := hwm.layout.disjoint l1 l2 h1 h2 hne hb1.2.2 hb2.2.2
      omega
    · intro l' hl' idx hidx
      by_cases hll : l' = l
      · rw [hll, hoff_l', hoff_eq]; rw [hll, hsz_l', hsz_eq] at hidx
        simpa [s', show fullWatchOffCore s.core l + popK + idx =
          fullWatchOffCore s.core l + (popK + idx) by omega] using
          hwm.layout.no_sentinel l hl (popK + idx) (by omega)
      · obtain ⟨ho, hs⟩ := hoth l' hll; rw [ho]; rw [hs] at hidx
        exact hwm.layout.no_sentinel l' hl' idx hidx
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  have hwat' : ModeWatchesInv F_cur s'.core := by
    unfold ModeWatchesInv; rw [ite_eq_right (fun h0 => hinv.2.2.2.2.2.2 h0)]
    refine ⟨hlay', fun l' hl' => ?_⟩
    by_cases hll : l' = l
    · rw [hll, hoff_l', hsz_l']
      exact DenseWatchSliceOk.relocate (k := s.core) (k' := s'.core) hrefl (le_refl _)
        (fun _ r => r) (fun _ _ => rfl) hsl'
    · obtain ⟨ho, hs⟩ := hoth l' hll; rw [ho, hs]
      exact DenseWatchSliceOk.relocate (k := s.core) (k' := s'.core) hrefl (le_refl _)
        (fun _ r => r) (fun _ _ => rfl) (hwm.slices l' hl')
  exact ⟨hlen', { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat' },
    hinv.2.2.1, m6_arenaVarsNodup_eq rfl rfl hinv.2.2.2.1,
    hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem m6_denseInvW_replaceSameLen {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (_hng : fullArenaClauseGarb s cref = false)
    {arena' : List (BitVec 32)} (har_len : arena'.length = c.arena_cap)
    (hout : ∀ i, i < cref + 3 ∨ cref + 3 + fullArenaClauseSize s cref ≤ i →
      arena'[i]? = s.core.arena[i]?)
    (hlits_lt' : ∀ l ∈ fullArenaClauseLits { s with core := { s.core with arena := arena' } } cref,
      l < 2 * s.core.cur_vars)
    (hnd_cr' : ((fullArenaClauseLits { s with core := { s.core with arena := arena' } } cref).map
      (· / 2)).Nodup)
    (hent' : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLits { s with core := { s.core with arena := arena' } } cref))) :
    let s' := { s with core := { s.core with arena := arena' } }
    FullDenseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have hcl := hinv.1.core_ok; have hw := hinv.2.1; have hcl0 := hinv.2.2.2.2.2.1
  let old_sz := fullArenaClauseSizeCore s.core cref
  have hsz0 : fullArenaClauseSize s cref = old_sz := rfl
  have hwf := hw.arena.refs_wf cref href
  have hbd_wf := hwf.2.2.1; have hal_le := hcl.arena_len_le; have haa := hcl.arena_len_arr
  have hbd_ar : cref + 3 + old_sz ≤ s.core.arena.length := by omega
  have hbd_ar' : cref + 3 + old_sz ≤ arena'.length := by rw [har_len]; omega
  have hout_c : ∀ i, i < cref + 3 ∨ cref + 3 + old_sz ≤ i → arena'[i]? = s.core.arena[i]? :=
    hout
  have hout_ref : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len r ≤ cref) ∨
      cref + 3 + old_sz ≤ r := by
    intro r hr hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨hw.arena.disjoint hr href hlt, fullArenaScanRefs_disjoint hr href hlt⟩
    · exact Or.inr (hw.arena.disjoint href hr hgt)
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff arena' s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr
    by_cases hrc : r = cref
    · subst r
      exact fullArenaNextOff_congr_block (hout_c cref (Or.inl (by omega)))
        (hout_c (cref + 2) (Or.inl (by omega))) fun k hk _ => hout_c k (Or.inr hk)
    · rcases hout_ref r hr hrc with ⟨hlt, _⟩ | hgt
      · have hr3 := (hw.arena.refs_wf r hr).2.1
        exact fullArenaNextOff_congr_block (hout_c r (Or.inl (by omega)))
          (hout_c (r + 2) (Or.inl (by omega))) fun i _ _ => hout_c i (Or.inl (by omega))
      · exact fullArenaNextOff_congr_block (hout_c r (Or.inr hgt))
          (hout_c (r + 2) (Or.inr (by omega))) fun i _ _ => hout_c i (Or.inr (by omega))
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hother : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := by
    intro r hr hne
    have hrwf := hw.arena.refs_wf r hr
    have hbd_r : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have := hrwf.2.2.1; omega
    have hbd_r' : r + 3 + fullArenaClauseSizeCore s.core r ≤ arena'.length := by
      rw [har_len]; have := hrwf.2.2.1; omega
    rcases hout_ref r hr hne with ⟨hlt, _⟩ | hgt
    · have hszr : fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := by
        unfold fullArenaClauseSizeCore; dsimp only [s']; rw [hout_c (r + 2) (Or.inl (by omega))]
      have hgar : fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
        rw [hout_c r (Or.inl (by omega))]
      refine ⟨hszr, hgar, ?_⟩
      unfold fullArenaClauseLitsCore; rw [hszr]
      exact m6_lits_eq_of_hold hbd_r hbd_r' fun j hj => hout_c (r + 3 + j) (Or.inl (by omega))
    · have hszr : fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := by
        unfold fullArenaClauseSizeCore; dsimp only [s']
        rw [hout_c (r + 2) (Or.inr (by omega))]
      have hgar : fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
        rw [hout_c r (Or.inr hgt)]
      refine ⟨hszr, hgar, ?_⟩
      unfold fullArenaClauseLitsCore; rw [hszr]
      exact m6_lits_eq_of_hold hbd_r hbd_r' fun j hj => hout_c (r + 3 + j) (Or.inr (by omega))
  have hsz_cref : fullArenaClauseSizeCore s'.core cref = old_sz := by
    dsimp only [old_sz]; unfold fullArenaClauseSizeCore; dsimp only [s']
    rw [hout_c (cref + 2) (Or.inl (by omega))]
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; rw [hnxt r hr]
      by_cases hrc : r = cref
      · subst r; rw [hsz_cref]; exact hwf
      · rw [(hother r hr hrc).1]; exact hw.arena.refs_wf r hr
    · intro r hr hsh; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r
        have hsh0 : (fullArenaHdrCore s.core cref &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢
          change (arena'[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 at hsh
          rwa [hout_c cref (Or.inl (by omega))] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term cref hr hsh0
        change cref + 3 + old_sz ≤ t at ht1
        rw [hsz_cref]
        exact ⟨t, ht1, ht2, (by
          change arena'[t]? = some 0xFFFFFFFF#32
          rw [hout_c t (Or.inr ht1)]
          exact hsent)⟩
      · rcases hout_ref r hr hrc with ⟨hlt, hlt_nxt⟩ | hgt
        · have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
            unfold fullArenaHdrCore at hsh ⊢
            change (arena'[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 at hsh
            rwa [hout_c r (Or.inl (by omega))] at hsh
          obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
          obtain ⟨t0, ht0_lo, ht0_hi, ht0_nxt, ht0_sent⟩ :=
            fullArenaNextOff_hits_sentinel (hw.arena.refs_wf r hr).1 hsh0 ht1 ht2 hsent
          rw [(hother r hr hrc).1]
          exact ⟨t0, ht0_lo, Nat.lt_of_le_of_lt ht0_hi ht2, (by
            change arena'[t0]? = some 0xFFFFFFFF#32
            rw [hout_c t0 (Or.inl (by omega))]
            exact ht0_sent)⟩
        · have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
            unfold fullArenaHdrCore at hsh ⊢
            change (arena'[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 at hsh
            rwa [hout_c r (Or.inr hgt)] at hsh
          obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
          rw [(hother r hr hrc).1]
          exact ⟨t, ht1, ht2, (by
            change arena'[t]? = some 0xFFFFFFFF#32
            rw [hout_c t (Or.inr (by omega))]
            exact hsent)⟩
    · intro r hr hng'; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; exact hlits_lt'
      · rw [(hother r hr hrc).2.1] at hng'; rw [(hother r hr hrc).2.2]
        exact hw.arena.lits_lt r hr hng'
    · intro r hr hng'; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; exact hent'
      · rw [(hother r hr hrc).2.1] at hng'; rw [(hother r hr hrc).2.2]
        exact hw.arena.entails r hr hng'
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with arena_len_arr := har_len }, hinv.1.scratch_ok⟩
  have hnd' : FullArenaVarsNodup s' := by
    intro r hr hng'; change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs] at hr
    by_cases hrc : r = cref
    · subst r; exact hnd_cr'
    · have hg0 : fullArenaClauseGarb s r = false := by
        change fullArenaClauseGarbCore s'.core r = false at hng'
        rwa [(hother r hr hrc).2.1] at hng'
      change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
      rw [(hother r hr hrc).2.2]; exact hinv.2.2.2.1 r hr hg0
  have hno_rsn : ∀ idx < s.core.trail_end,
      s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun idx hidx => hw.level0_rsn_none idx hidx (by have := hw.lvl_le idx hidx; omega)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := harena'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => by
        change r ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact hr)
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne }
  exact ⟨⟨hlen', hw', hinv.2.2.1, hnd',
    FullExtScratchOk.of_pres hinv.2.2.2.2.1 ⟨rfl, rfl⟩ fun r hr => by
      change r ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact hr,
    hcl0, hinv.2.2.2.2.2.2⟩, hrefs⟩

private theorem m6_denseInvW_inPlaceShrink {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {cref nsz : Nat} (href : cref ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cref = false) (h3 : 3 ≤ nsz)
    (hlt : nsz < fullArenaClauseSize s cref) {arena' : List (BitVec 32)}
    (har_len : arena'.length = c.arena_cap)
    (hhdr' : arena'[cref]? = some
      (if (fullArenaHdr s cref &&& 0x00800000#32) = 0#32 then
        fullArenaHdr s cref ||| 0x00800000#32
      else fullArenaHdr s cref))
    (hsz' : arena'[cref + 2]? = some (BitVec.ofNat 32 nsz))
    (hpad_old : ∀ j, nsz ≤ j → j < fullArenaClauseSize s cref - 1 →
      arena'[cref + 3 + j]? = s.core.arena[cref + 3 + j]?)
    (hlast_sent : (fullArenaHdr s cref &&& 0x00800000#32) = 0#32 →
      arena'[cref + 3 + fullArenaClauseSize s cref - 1]? = some 0xFFFFFFFF#32)
    (hlast_keep : (fullArenaHdr s cref &&& 0x00800000#32) ≠ 0#32 →
      arena'[cref + 3 + fullArenaClauseSize s cref - 1]? =
        s.core.arena[cref + 3 + fullArenaClauseSize s cref - 1]?)
    (hout : ∀ i, i < cref ∨ cref + 3 + fullArenaClauseSize s cref ≤ i →
      arena'[i]? = s.core.arena[i]?)
    (hlits_lt' : ∀ l ∈ fullArenaClauseLits { s with core := { s.core with arena := arena' } } cref,
      l < 2 * s.core.cur_vars)
    (hnd_cr' : ((fullArenaClauseLits { s with core := { s.core with arena := arena' } } cref).map
      (· / 2)).Nodup)
    (hent' : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLits { s with core := { s.core with arena := arena' } } cref))) :
    let s' := { s with core := { s.core with arena := arena' } }
    FullDenseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have hcl := hinv.1.core_ok; have hw := hinv.2.1; have hcl0 := hinv.2.2.2.2.2.1
  have hsh := inPlaceShrink_preserves_arena hw.arena hcl href hng h3 hlt har_len hhdr' hsz'
    hpad_old hlast_sent hlast_keep hout hlits_lt' hent'
  obtain ⟨hrefs, hother, _, _, harena'⟩ := hsh
  have hlen' : s'.LengthsOk c := ⟨{ hcl with arena_len_arr := har_len }, hinv.1.scratch_ok⟩
  have hnd' : FullArenaVarsNodup s' := by
    intro r hr hng'; change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs] at hr
    by_cases hrc : r = cref
    · subst r; exact hnd_cr'
    · have hg0 : fullArenaClauseGarb s r = false := by
        change fullArenaClauseGarbCore s'.core r = false at hng'
        rwa [(hother r hr hrc).2.1] at hng'
      change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
      rw [(hother r hr hrc).2.2]; exact hinv.2.2.2.1 r hr hg0
  have hno_rsn : ∀ idx < s.core.trail_end,
      s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun idx hidx => hw.level0_rsn_none idx hidx (by have := hw.lvl_le idx hidx; omega)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := harena'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => by
        change r ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact hr)
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne }
  exact ⟨⟨hlen', hw', hinv.2.2.1, hnd',
    FullExtScratchOk.of_pres hinv.2.2.2.2.1 ⟨rfl, rfl⟩ fun r hr => by
      change r ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact hr,
    hcl0, hinv.2.2.2.2.2.2⟩, hrefs⟩

/-! ## 2. `M6ReprFlatInv` & `m6ElsLitMapOk` Helpers -/

theorem m6_reprFlat_lt {F_cur : List (List Nat)} {nlits : Nat}
    {repr : List (BitVec 32)} (h : M6ReprFlatInv F_cur nlits repr) {l : Nat} (hl : l < nlits) :
    (repr[l]?.getD 0#32).toNat < nlits := by
  have := h.1.1.2 l hl; omega

theorem m6_reprFlat_equiv {F_cur : List (List Nat)} {nlits : Nat}
    {repr : List (BitVec 32)} (h : M6ReprFlatInv F_cur nlits repr) {l : Nat} (hl : l < nlits) :
    LitEquiv (cnfOfClauses F_cur) l (repr[l]?.getD 0#32).toNat :=
  h.1.2 l hl

theorem m6_reprFlat_neg {F_cur : List (List Nat)} {nlits : Nat}
    {repr : List (BitVec 32)} (h : M6ReprFlatInv F_cur nlits repr) {l : Nat} (hl : l < nlits) :
    (repr[l ^^^ 1]?.getD 0#32).toNat = (repr[l]?.getD 0#32).toNat ^^^ 1 :=
  h.2.2 l hl

theorem m6_reprFlat_idem {F_cur : List (List Nat)} {nlits : Nat}
    {repr : List (BitVec 32)} (h : M6ReprFlatInv F_cur nlits repr) {l : Nat} (hl : l < nlits) :
    repr[(repr[l]?.getD 0#32).toNat]? = repr[l]? :=
  h.2.1 l hl

private structure M6ElsLitMapOk (c : FullCfg) (s : FullState) (lm : List (BitVec 8))
    (tmp : List (BitVec 32)) (nsz : Nat) : Prop where
  lm_len : lm.length = 2 * c.max_vars
  tmp_len : tmp.length = c.max_vars
  cv_le : s.core.cur_vars ≤ c.max_vars
  nsz_le : nsz ≤ s.core.cur_vars
  tmp_lt : ∀ j < nsz, (tmp[j]?.getD 0#32).toNat < 2 * s.core.cur_vars
  nodup : ((tmp.take nsz).map fun x => x.toNat / 2).Nodup
  map : ∀ l < 2 * c.max_vars,
    lm[l]?.getD 0#8 = if decide (∃ j < nsz, (tmp[j]?.getD 0#32).toNat = l) then 1#8 else 0#8

private theorem m6_elsLitMapOk_init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s) :
    M6ElsLitMapOk c s s.core.lit_mark s.core.tmp 0 :=
  ⟨hinv.1.core_ok.lit_mark_len, hinv.1.core_ok.tmp_len_arr,
   hinv.1.core_ok.cur_vars_le, Nat.zero_le _,
   (fun _ hj => by cases hj), by simp,
   fun l hl => by
     rw [decide_eq_false (by intro ⟨j, hj, _⟩; exact Nat.not_lt_zero j hj)]
     simpa using hinv.2.2.1.2 l hl⟩

private theorem m6_elsLitMapOk_push {c : FullCfg} {s : FullState}
    {lm : List (BitVec 8)} {tmp : List (BitVec 32)} {nsz : Nat}
    (h : M6ElsLitMapOk c s lm tmp nsz) {rx : BitVec 32}
    (hrx_lt : rx.toNat < 2 * s.core.cur_vars)
    (h0 : lm[rx.toNat]?.getD 0#8 = 0#8)
    (h1 : lm[(rx ^^^ 1#32).toNat]?.getD 0#8 = 0#8) :
    nsz < c.max_vars ∧
    M6ElsLitMapOk c s (lm.set rx.toNat 1#8) (tmp.set nsz rx) (nsz + 1) := by
  rcases h with ⟨hlm, htmp, hcv, hnsz, hlt, hnd, hmap⟩
  have hrx1 : (rx ^^^ 1#32).toNat = rx.toNat ^^^ 1 := by simp
  have hnot_var : rx.toNat / 2 ∉ (tmp.take nsz).map (fun x => x.toNat / 2) := by
    intro hmem
    rw [List.mem_map] at hmem; obtain ⟨x, hx, hxv⟩ := hmem
    rw [List.mem_iff_getElem] at hx; obtain ⟨j, hj, rfl⟩ := hx
    have hj' : j < nsz := by simp only [List.length_take] at hj; omega
    rw [List.getElem_take] at hxv
    have hx_eq : (tmp[j]?.getD 0#32).toNat = (tmp[j]'(by omega)).toNat := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hcases : (tmp[j]?.getD 0#32).toNat = rx.toNat ∨
        (tmp[j]?.getD 0#32).toNat = rx.toNat ^^^ 1 := by
      rw [show rx.toNat ^^^ 1 = litNeg rx.toNat from rfl, litNeg_eq]; split <;> omega
    rcases hcases with he | he
    · have hl := hmap rx.toNat (by omega)
      rw [decide_eq_true ⟨j, hj', he⟩] at hl; simp only [ite_true] at hl
      rw [h0] at hl; cases hl
    · have hl := hmap (rx.toNat ^^^ 1) (by omega)
      rw [decide_eq_true ⟨j, hj', he⟩] at hl; simp only [ite_true] at hl
      rw [← hrx1, h1] at hl; cases hl
  have hlen_take : ((tmp.take nsz).map fun x => x.toNat / 2).length = nsz := by
    simp [List.length_take]; omega
  have hpig : nsz + 1 ≤ s.core.cur_vars := by
    have hnd' : (rx.toNat / 2 :: (tmp.take nsz).map fun x => x.toNat / 2).Nodup :=
      List.nodup_cons.mpr ⟨hnot_var, hnd⟩
    have hlt' : ∀ v ∈ rx.toNat / 2 :: (tmp.take nsz).map fun x => x.toNat / 2,
        v < s.core.cur_vars := by
      intro v hv; rcases List.mem_cons.mp hv with rfl | hm
      · omega
      · rw [List.mem_map] at hm; obtain ⟨x, hx, rfl⟩ := hm
        rw [List.mem_iff_getElem] at hx; obtain ⟨j, hj, rfl⟩ := hx
        have hj' : j < nsz := by simp only [List.length_take] at hj; omega
        rw [List.getElem_take]
        have := hlt j hj'
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at this; omega
    have hl := nodup_nat_lt_len hnd' hlt'
    simp only [List.length_cons, hlen_take] at hl; exact hl
  have hnsz_mx : nsz < c.max_vars := by omega
  refine ⟨hnsz_mx, by simp [hlm], by simp [htmp], hcv, hpig, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hjn : j = nsz
    · subst hjn; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hrx_lt
    · rw [List.getElem?_set_ne (Ne.symm hjn)]; exact hlt j (by omega)
  · rw [list_take_set_succ tmp (by omega) rx, List.map_append, List.map_singleton,
      List.nodup_append]
    refine ⟨hnd, by simp, fun a ha b hb => ?_⟩
    simp only [List.mem_singleton] at hb; subst hb; rintro rfl; exact hnot_var ha
  · intro l hl
    by_cases hlx : l = rx.toNat
    · subst hlx
      rw [List.getElem?_set_self (by omega), Option.getD_some,
        decide_eq_true ⟨nsz, by omega, by
          rw [List.getElem?_set_self (by omega), Option.getD_some]⟩]
      rfl
    · rw [List.getElem?_set_ne (Ne.symm hlx)]
      have hmem_iff : (∃ j < nsz + 1, ((tmp.set nsz rx)[j]?.getD 0#32).toNat = l) ↔
          (∃ j < nsz, (tmp[j]?.getD 0#32).toNat = l) := by
        constructor
        · rintro ⟨j, hj, hje⟩
          by_cases hjn : j = nsz
          · subst hjn; rw [List.getElem?_set_self (by omega), Option.getD_some] at hje
            exact absurd hje.symm hlx
          · rw [List.getElem?_set_ne (Ne.symm hjn)] at hje; exact ⟨j, by omega, hje⟩
        · rintro ⟨j, hj, hje⟩
          exact ⟨j, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hje⟩
      rw [hmap l hl]
      by_cases hex : ∃ j < nsz, (tmp[j]?.getD 0#32).toNat = l
      · have hex' := hmem_iff.mpr hex
        rw [decide_eq_true hex, decide_eq_true hex']
      · have hex' : ¬ ∃ j < nsz + 1, ((tmp.set nsz rx)[j]?.getD 0#32).toNat = l :=
          fun h' => hex (hmem_iff.mp h')
        rw [decide_eq_false hex, decide_eq_false hex']

/-! ## 3. `full_m6_els_ar_wp` (`29/39`) -/

private theorem m6_els_ar_ret_noop {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [.bool]}
    (hinv : FullDenseInvW c F0 F_cur s) (hm' : (FullMem c s ⋆ R) m')
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.repr = s.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Q (true, ()) m' :=
  hQ true s m' hinv rfl rfl rfl rfl rfl rfl rfl rfl (fun h => Bool.noConfusion h) hm'

private theorem m6_els_ar_loop3_step_ok {c : FullCfg} {s : FullState}
    {lm2 : List (BitVec 8)} {lm3 : List (BitVec 8)} {tmp2 : List (BitVec 32)}
    {nsz2 k3 : BitVec 32} (hmap2 : M6ElsLitMapOk c s lm2 tmp2 nsz2.toNat)
    (hk3 : k3.toNat < nsz2.toNat) (hlm3 : lm3.length = 2 * c.max_vars)
    (hmap3 : ∀ l < 2 * c.max_vars,
      lm3[l]?.getD 0#8 =
        if decide (∃ j < nsz2.toNat, k3.toNat ≤ j ∧
          (tmp2[j]?.getD 0#32).toNat = l) then 1#8 else 0#8) :
    let tk := (tmp2[k3.toNat]'(by
      have := hmap2.nsz_le; have := hmap2.cv_le; have := hmap2.tmp_len; omega)).toNat
    ∀ l < 2 * c.max_vars,
      (lm3.set tk 0#8)[l]?.getD 0#8 =
        if decide (∃ j < nsz2.toNat, k3.toNat + 1 ≤ j ∧
          (tmp2[j]?.getD 0#32).toNat = l) then 1#8 else 0#8 := by
  intro tk l hl
  have hnsz_le := hmap2.nsz_le; have hcv_le := hmap2.cv_le; have htl := hmap2.tmp_len
  have htk_lt : tk < 2 * s.core.cur_vars := by
    dsimp only [tk]; have := hmap2.tmp_lt k3.toNat hk3
    rwa [List.getElem?_eq_getElem (by have := hmap2.tmp_len; omega), Option.getD_some] at this
  have htk_lm : tk < lm3.length := by rw [hlm3]; omega
  have hnd_t := nodup_of_map_div2 hmap2.nodup
  have hinj : ∀ j, k3.toNat + 1 ≤ j → j < nsz2.toNat → (tmp2[j]?.getD 0#32).toNat ≠ tk := by
    intro j hj1 hj2 heq
    have hlen_tk : (tmp2.take nsz2.toNat).length = nsz2.toNat := by
      rw [List.length_take_of_le (by have := hmap2.tmp_len; omega)]
    have hk_map : ((tmp2.take nsz2.toNat).map BitVec.toNat)[k3.toNat]'(by
        rw [List.length_map, hlen_tk]; exact hk3) = tk := by
      rw [List.getElem_map, List.getElem_take]
    have hj_map : ((tmp2.take nsz2.toNat).map BitVec.toNat)[j]'(by
        rw [List.length_map, hlen_tk]; exact hj2) = (tmp2[j]?.getD 0#32).toNat := by
      rw [List.getElem_map, List.getElem_take,
        List.getElem?_eq_getElem (by have := hmap2.tmp_len; omega), Option.getD_some]
    have hne_get := m6_nodup_getElem_ne hnd_t
      (by rw [List.length_map, hlen_tk]; exact hk3)
      (by rw [List.length_map, hlen_tk]; exact hj2) (by omega)
    rw [hk_map, hj_map] at hne_get; exact hne_get heq.symm
  by_cases hlt_tk : l = tk
  · rw [hlt_tk, List.getElem?_set_self htk_lm, Option.getD_some,
      decide_eq_false (by rintro ⟨j, hj2, hj1, hjeq⟩; exact hinj j hj1 hj2 hjeq)]
    rfl
  · rw [List.getElem?_set_ne (Ne.symm hlt_tk), hmap3 l hl]
    have hex_iff : (∃ j < nsz2.toNat, k3.toNat + 1 ≤ j ∧ (tmp2[j]?.getD 0#32).toNat = l) ↔
        (∃ j < nsz2.toNat, k3.toNat ≤ j ∧ (tmp2[j]?.getD 0#32).toNat = l) := by
      constructor
      · rintro ⟨j, h2, h1, h3⟩; exact ⟨j, h2, by omega, h3⟩
      · rintro ⟨j, h2, h1, h3⟩
        by_cases hjk : j = k3.toNat
        · subst hjk; exfalso; apply hlt_tk
          rw [← h3, List.getElem?_eq_getElem (by have := hmap2.tmp_len; omega), Option.getD_some]
        · exact ⟨j, h2, by omega, h3⟩
    by_cases hex : ∃ j < nsz2.toNat, k3.toNat ≤ j ∧ (tmp2[j]?.getD 0#32).toNat = l
    · have hex' := hex_iff.mpr hex; rw [decide_eq_true hex, decide_eq_true hex']
    · have hex' : ¬ ∃ j < nsz2.toNat, k3.toNat + 1 ≤ j ∧ (tmp2[j]?.getD 0#32).toNat = l :=
        fun h => hex (hex_iff.mp h)
      rw [decide_eq_false hex, decide_eq_false hex']

private theorem m6_els_ar_push_watched {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hWatch : M6EnvSpec Γ "full_watch_push" Full.fullWatchPushSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s5 : FullState}
    {rl cr sz : BitVec 32} {R : Mem 64 → Prop} {m5 : Mem 64}
    {aH : Arg Val i64} {aRl aSz aCr aK : Arg Val i32}
    {cont : Tup Val [.bool] → Expr Val Cont rs}
    (haH : aH.val = c.hdr) (haRl : aRl.val = rl)
    (haSz : aSz.val = sz &&& 0x7FFFFFFF#32) (haCr : aCr.val = cr) (haK : aK.val = 2#32)
    (hinv5 : FullDenseInvW c F0 F_cur s5) (hcv5 : s5.core.cur_vars = s.core.cur_vars)
    (hfl5 : s5.core.fuel = s.core.fuel) (hrp5 : s5.core.repr = s.core.repr)
    (htmk5 : s5.scratch.tarjan_mark = s.scratch.tarjan_mark)
    (htrh5 : s5.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hscr5 : s5.scratch.scratch_buf = s.scratch.scratch_buf)
    (hws15 : s5.scratch.work_stk1 = s.scratch.work_stk1)
    (hws25 : s5.scratch.work_stk2 = s.scratch.work_stk2)
    (hsz3 : 3 ≤ sz.toNat) (hsz_lt : sz.toNat < 2 ^ 31)
    (hcr_lt : cr.toNat < 0x80000000) (hcr_ne : cr ≠ 0xFFFFFFFF#32)
    (hcr5 : cr.toNat ∈ fullArenaClauseRefs s5) (hm5 : (FullMem c s5 ⋆ R) m5)
    (hk : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.repr = s.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (cont (ok, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
      "full_watch_push" (aH, aRl, aSz, aCr, aK, ()) cont) m5 := by
  obtain ⟨hw0_ne, hw0_f, hw0_3⟩ := m6_bv32_mask7f_props hsz3 hsz_lt
  have hwm5 := hinv5.2.1.watches; unfold ModeWatchesInv at hwm5
  rw [ite_eq_right (fun h0 => hinv5.2.2.2.2.2.2 h0)] at hwm5
  refine wp_call_of_spec _ cont ?_
  dsimp only [vals]; rw [haH, haRl, haSz, haCr, haK]
  refine hWatch _ m5 (fun r m' => wp Γ Q X (cont r) m') X
    ⟨c, s5, R, rfl, hinv5.1, hwm5.layout, (fun h => by cases h),
      (fun _ => ⟨hw0_ne, hcr_ne⟩), hm5, ?_⟩
  intro ok wvec' wstk' wlen' wu' wsort' m' s' hlen' hlay' hother hok_t hok_f hm'
  have hinv' := m6_denseInvW_watchPush hinv5 hlen' hlay' hw0_f hw0_3 hcr_lt hcr5 hother
    (fun ht => by
      obtain ⟨h1, _, h2, h3, h4, h5⟩ := hok_t ht
      exact ⟨h1, by simpa [mkWatchCore, fullWatchSize, fullWatchOff] using h2,
        h3, by simpa [mkWatchCore, fullWatchSize, fullWatchOff] using h4,
        by simpa [mkWatchCore, fullWatchSize, fullWatchOff] using h5⟩)
    (fun hf hl => (hok_f hf).1 hl)
  exact hk ok s' m' hinv' hcv5 hfl5 hrp5 htmk5 htrh5 hscr5 hws15 hws25 hm'

private theorem m6_els_ar_shrink0_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sC : FullState} {lm2 : List (BitVec 8)} {tmp2 ar4 : List (BitVec 32)}
    {cr sz32 nsz2 : BitVec 32} (hinvC : FullDenseInvW c F0 F_cur sC)
    (hcr_ref : cr.toNat ∈ fullArenaClauseRefs sC) (hng_cr : fullArenaClauseGarb s cr.toNat = false)
    (hcr_bd : cr.toNat < s.core.arena.length) (har4 : ar4.length = c.arena_cap)
    (_hcr2_bd : cr.toNat + 2 < s.core.arena.length)
    (hcr_bd2 : cr.toNat + 2 < ar4.length) (_hcr_bd1 : cr.toNat + 1 < ar4.length)
    (har_set_sz : ((ar4.set (cr.toNat + 2) nsz2).set (cr.toNat + 1) 2#32)[cr.toNat + 2]? =
      some nsz2)
    (hsC_ar : sC.core.arena = s.core.arena) (hsC_cv : sC.core.cur_vars = s.core.cur_vars)
    (hsz_def : sz32.toNat = fullArenaClauseSize s cr.toNat)
    (h3n : 3 ≤ nsz2.toNat) (hlt_sz : nsz2.toNat < sz32.toNat)
    (hhdr_sh0 : (s.core.arena[cr.toNat]'hcr_bd &&& 0x00800000#32) = 0#32)
    (hout4 : ∀ i, i < cr.toNat + 3 ∨ cr.toNat + 3 + nsz2.toNat ≤ i →
      ar4[i]? = sC.core.arena[i]?)
    (htmp_cp : ∀ j < nsz2.toNat, ar4[cr.toNat + 3 + j]? = tmp2[j]?)
    (hmap2 : M6ElsLitMapOk c s lm2 tmp2 nsz2.toNat)
    (hhent4 : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((tmp2.take nsz2.toNat).map BitVec.toNat))) :
    let ar5 := (((ar4.set (cr.toNat + 2) nsz2).set (cr.toNat + 1) 2#32).set
      cr.toNat (fullArenaHdr sC cr.toNat ||| 0x00800000#32)).set
      (cr.toNat + 3 + sz32.toNat - 1) 0xFFFFFFFF#32
    let s5 : FullState := { sC with core := { sC.core with arena := ar5 } }
    ar5[cr.toNat + 2]? = some nsz2 ∧
    FullDenseInvW c F0 F_cur s5 ∧ fullArenaClauseRefs s5 = fullArenaClauseRefs sC := by
  intro ar5 s5
  have hhdr_sh0' : (fullArenaHdr sC cr.toNat &&& 0x00800000#32) = 0#32 := by
    unfold fullArenaHdr fullArenaHdrCore; rw [hsC_ar]
    change (s.core.arena[cr.toNat]?.getD 0#32 &&& 0x00800000#32) = 0#32
    rw [List.getElem?_eq_getElem hcr_bd, Option.getD_some]; exact hhdr_sh0
  have hlt_sz_ar : nsz2.toNat < fullArenaClauseSize sC cr.toNat := by
    change nsz2.toNat < fullArenaClauseSize sC cr.toNat
    unfold fullArenaClauseSize fullArenaClauseSizeCore at hsz_def ⊢
    rw [hsC_ar]; rw [← hsz_def]; exact hlt_sz
  have hsz5 : ar5[cr.toNat + 2]? = some nsz2 := by
    dsimp only [ar5]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      har_set_sz]
  have hl5 : ∀ j < nsz2.toNat, ar5[cr.toNat + 3 + j]? = tmp2[j]? := by
    intro j hj; dsimp only [ar5]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact htmp_cp j hj
  have hlen5 : ar5.length = c.arena_cap := by simp [ar5, har4]
  have hng_sC : fullArenaClauseGarb sC cr.toNat = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng_cr ⊢
    rw [hsC_ar]; exact hng_cr
  have hsz_eq_sC : fullArenaClauseSize sC cr.toNat = sz32.toNat := by
    unfold fullArenaClauseSize fullArenaClauseSizeCore at hsz_def ⊢; rw [hsC_ar, ← hsz_def]
  have hwf_cr := hinvC.2.1.arena.refs_wf cr.toNat hcr_ref
  have hal := hinvC.1.core_ok.arena_len_le
  have hsz_bd : cr.toNat + 3 + sz32.toNat ≤ c.arena_cap := by
    have h1 := hwf_cr.2.2.1; have h2 := hwf_cr.2.2.2.1
    have h3 : fullArenaClauseSize sC cr.toNat = fullArenaClauseSizeCore sC.core cr.toNat := rfl
    rw [hsz_eq_sC] at h3; rw [← h3] at h1; omega
  have htmp_l := hmap2.tmp_len; have hnsz_l := hmap2.nsz_le; have hcv_l := hmap2.cv_le
  have heq_lits : fullArenaClauseLits s5 cr.toNat = ((tmp2.take nsz2.toNat).map BitVec.toNat) := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; dsimp only [s5]
    rw [hsz5, Option.getD_some,
      show nsz2.toNat = (tmp2.take nsz2.toNat).length by
        rw [List.length_take_of_le (by omega)]]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_take, List.length_drop, hlen5]; omega
    · intro j hj1 _; simp only [List.length_map, List.length_take] at hj1
      have hj : j < nsz2.toNat := by omega
      simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
      have hq := hl5 j hj
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hq
      exact congrArg BitVec.toNat (Option.some.inj hq)
  obtain ⟨hinv5, hrefs5⟩ := m6_denseInvW_inPlaceShrink hinvC (cref := cr.toNat) (nsz := nsz2.toNat)
    hcr_ref hng_sC h3n hlt_sz_ar hlen5
    (by dsimp only [ar5]
        rw [ite_eq_left hhdr_sh0', List.getElem?_set_ne (by omega),
          List.getElem?_set_self (by simp [har4]; omega)])
    (by rw [hsz5, show BitVec.ofNat 32 nsz2.toNat = nsz2 from by simp])
    (fun j hj1 hj2 => by
      dsimp only [ar5]; rw [hsz_eq_sC] at hj2
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hout4 (cr.toNat + 3 + j) (Or.inr (by omega)))
    (fun _ => by
      dsimp only [ar5]; change ar5[cr.toNat + 3 + fullArenaClauseSize sC cr.toNat - 1]? = _
      rw [hsz_eq_sC]; exact List.getElem?_set_self (by simp [har4]; omega))
    (fun h => absurd hhdr_sh0' h)
    (fun i hi => by
      change i < cr.toNat ∨ cr.toNat + 3 + fullArenaClauseSize sC cr.toNat ≤ i at hi
      rw [hsz_eq_sC] at hi; dsimp only [ar5]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      cases hi with
      | inl h => exact hout4 i (Or.inl (by omega))
      | inr h => exact hout4 i (Or.inr (by omega)))
    (fun l hl => by
      rw [heq_lits, List.mem_iff_getElem] at hl; obtain ⟨j, hj, rfl⟩ := hl
      have hj' : j < nsz2.toNat := by simp only [List.length_map, List.length_take] at hj; omega
      simp only [List.getElem_map, List.getElem_take]
      have := hsC_cv ▸ hmap2.tmp_lt j hj'
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this)
    (by rw [heq_lits, List.map_map]; exact hmap2.nodup)
    (by rw [heq_lits]; exact hhent4)
  exact ⟨hsz5, hinv5, hrefs5⟩

private theorem m6_els_ar_shrink1_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sC : FullState} {lm2 : List (BitVec 8)} {tmp2 ar4 : List (BitVec 32)}
    {cr sz32 nsz2 : BitVec 32} (hinvC : FullDenseInvW c F0 F_cur sC)
    (hcr_ref : cr.toNat ∈ fullArenaClauseRefs sC) (hng_cr : fullArenaClauseGarb s cr.toNat = false)
    (hcr_bd : cr.toNat < s.core.arena.length) (har4 : ar4.length = c.arena_cap)
    (hcr_bd2 : cr.toNat + 2 < ar4.length) (_hcr_bd1 : cr.toNat + 1 < ar4.length)
    (har_set_sz : ((ar4.set (cr.toNat + 2) nsz2).set (cr.toNat + 1) 2#32)[cr.toNat + 2]? =
      some nsz2)
    (hsC_ar : sC.core.arena = s.core.arena) (hsC_cv : sC.core.cur_vars = s.core.cur_vars)
    (hsz_def : sz32.toNat = fullArenaClauseSize s cr.toNat)
    (h3n : 3 ≤ nsz2.toNat) (hlt_sz : nsz2.toNat < sz32.toNat)
    (hhdr_sh1 : (s.core.arena[cr.toNat]'hcr_bd &&& 0x00800000#32) ≠ 0#32)
    (hout4 : ∀ i, i < cr.toNat + 3 ∨ cr.toNat + 3 + nsz2.toNat ≤ i →
      ar4[i]? = sC.core.arena[i]?)
    (htmp_cp : ∀ j < nsz2.toNat, ar4[cr.toNat + 3 + j]? = tmp2[j]?)
    (hmap2 : M6ElsLitMapOk c s lm2 tmp2 nsz2.toNat)
    (hhent4 : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((tmp2.take nsz2.toNat).map BitVec.toNat))) :
    let ar5 := (ar4.set (cr.toNat + 2) nsz2).set (cr.toNat + 1) 2#32
    let s5 : FullState := { sC with core := { sC.core with arena := ar5 } }
    ar5[cr.toNat + 2]? = some nsz2 ∧
    FullDenseInvW c F0 F_cur s5 ∧ fullArenaClauseRefs s5 = fullArenaClauseRefs sC := by
  intro ar5 s5
  have hhdr_sh1' : (fullArenaHdr sC cr.toNat &&& 0x00800000#32) ≠ 0#32 := by
    unfold fullArenaHdr fullArenaHdrCore; rw [hsC_ar]
    change (s.core.arena[cr.toNat]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32
    rw [List.getElem?_eq_getElem hcr_bd, Option.getD_some]; exact hhdr_sh1
  have hsz_eq_sC : fullArenaClauseSize sC cr.toNat = sz32.toNat := by
    unfold fullArenaClauseSize fullArenaClauseSizeCore at hsz_def ⊢; rw [hsC_ar, ← hsz_def]
  have hlt_sz_ar : nsz2.toNat < fullArenaClauseSize sC cr.toNat := by omega
  have hwf_cr := hinvC.2.1.arena.refs_wf cr.toNat hcr_ref
  have hal := hinvC.1.core_ok.arena_len_le
  have hsz_bd : cr.toNat + 3 + sz32.toNat ≤ c.arena_cap := by
    have h1 := hwf_cr.2.2.1; have h2 := hwf_cr.2.2.2.1
    have h3 : fullArenaClauseSize sC cr.toNat = fullArenaClauseSizeCore sC.core cr.toNat := rfl
    rw [hsz_eq_sC] at h3; rw [← h3] at h1; omega
  have htmp_l := hmap2.tmp_len; have hnsz_l := hmap2.nsz_le; have hcv_l := hmap2.cv_le
  have hsz5 : ar5[cr.toNat + 2]? = some nsz2 := by dsimp only [ar5]; exact har_set_sz
  have hl5 : ∀ j < nsz2.toNat, ar5[cr.toNat + 3 + j]? = tmp2[j]? := by
    intro j hj; dsimp only [ar5]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact htmp_cp j hj
  have hlen5 : ar5.length = c.arena_cap := by simp [ar5, har4]
  have heq_lits : fullArenaClauseLits s5 cr.toNat = ((tmp2.take nsz2.toNat).map BitVec.toNat) := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; dsimp only [s5]
    rw [hsz5, Option.getD_some,
      show nsz2.toNat = (tmp2.take nsz2.toNat).length by
        rw [List.length_take_of_le (by omega)]]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_take, List.length_drop, hlen5]; omega
    · intro j hj1 _; simp only [List.length_map, List.length_take] at hj1
      have hj : j < nsz2.toNat := by omega
      simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
      have hq := hl5 j hj
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hq
      exact congrArg BitVec.toNat (Option.some.inj hq)
  have hng_sC : fullArenaClauseGarb sC cr.toNat = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng_cr ⊢
    rw [hsC_ar]; exact hng_cr
  obtain ⟨hinv5, hrefs5⟩ := m6_denseInvW_inPlaceShrink hinvC (cref := cr.toNat) (nsz := nsz2.toNat)
    hcr_ref hng_sC h3n hlt_sz_ar hlen5
    (by dsimp only [ar5]
        rw [ite_eq_right hhdr_sh1', List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega)]
        change ar4[cr.toNat]? = some (sC.core.arena[cr.toNat]?.getD 0#32)
        rw [hout4 cr.toNat (Or.inl (by omega)), hsC_ar]
        change s.core.arena[cr.toNat]? = some (s.core.arena[cr.toNat]?.getD 0#32)
        rw [List.getElem?_eq_getElem hcr_bd, Option.getD_some])
    (by rw [hsz5, show BitVec.ofNat 32 nsz2.toNat = nsz2 from by simp])
    (fun j hj1 hj2 => by
      dsimp only [ar5]; rw [hsz_eq_sC] at hj2
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hout4 (cr.toNat + 3 + j) (Or.inr (by omega)))
    (fun h => absurd h hhdr_sh1')
    (fun _ => by
      dsimp only [ar5]; change ar5[cr.toNat + 3 + fullArenaClauseSize sC cr.toNat - 1]? = _
      rw [hsz_eq_sC, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hout4 (cr.toNat + 3 + sz32.toNat - 1) (Or.inr (by omega)))
    (fun i hi => by
      change i < cr.toNat ∨ cr.toNat + 3 + fullArenaClauseSize sC cr.toNat ≤ i at hi
      rw [hsz_eq_sC] at hi; dsimp only [ar5]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      cases hi with
      | inl h => exact hout4 i (Or.inl (by omega))
      | inr h => exact hout4 i (Or.inr (by omega)))
    (fun l hl => by
      rw [heq_lits, List.mem_iff_getElem] at hl; obtain ⟨j, hj, rfl⟩ := hl
      have hj' : j < nsz2.toNat := by simp only [List.length_map, List.length_take] at hj; omega
      simp only [List.getElem_map, List.getElem_take]
      have := hsC_cv ▸ hmap2.tmp_lt j hj'
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this)
    (by rw [heq_lits, List.map_map]; exact hmap2.nodup)
    (by rw [heq_lits]; exact hhent4)
  exact ⟨hsz5, hinv5, hrefs5⟩

private theorem m6_els_ar_same_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sC : FullState} {lm2 : List (BitVec 8)} {tmp2 ar4 : List (BitVec 32)}
    {cr sz32 nsz2 : BitVec 32} (hinvC : FullDenseInvW c F0 F_cur sC)
    (hcr_ref : cr.toNat ∈ fullArenaClauseRefs sC) (hng_cr : fullArenaClauseGarb s cr.toNat = false)
    (har4 : ar4.length = c.arena_cap) (hcr_bd2 : cr.toNat + 2 < ar4.length)
    (hsC_ar : sC.core.arena = s.core.arena) (hsC_cv : sC.core.cur_vars = s.core.cur_vars)
    (hsz_def : sz32.toNat = fullArenaClauseSize s cr.toNat)
    (hnsz_eq : nsz2.toNat = sz32.toNat)
    (hout4 : ∀ i, i < cr.toNat + 3 ∨ cr.toNat + 3 + nsz2.toNat ≤ i →
      ar4[i]? = sC.core.arena[i]?)
    (htmp_cp : ∀ j < nsz2.toNat, ar4[cr.toNat + 3 + j]? = tmp2[j]?)
    (hmap2 : M6ElsLitMapOk c s lm2 tmp2 nsz2.toNat)
    (hhent4 : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((tmp2.take nsz2.toNat).map BitVec.toNat))) :
    let s4 : FullState := { sC with core := { sC.core with arena := ar4 } }
    ar4[cr.toNat + 2]? = some sz32 ∧
    FullDenseInvW c F0 F_cur s4 ∧ fullArenaClauseRefs s4 = fullArenaClauseRefs sC := by
  intro s4
  have hsz_cr4 : fullArenaClauseSize sC cr.toNat = sz32.toNat := by
    unfold fullArenaClauseSize fullArenaClauseSizeCore at hsz_def ⊢; rw [hsC_ar, ← hsz_def]
  have hng_sC : fullArenaClauseGarb sC cr.toNat = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng_cr ⊢
    rw [hsC_ar]; exact hng_cr
  have hwf_cr := hinvC.2.1.arena.refs_wf cr.toNat hcr_ref
  have hal := hinvC.1.core_ok.arena_len_le
  have hsz_bd : cr.toNat + 3 + sz32.toNat ≤ c.arena_cap := by
    have h1 := hwf_cr.2.2.1; have h2 := hwf_cr.2.2.2.1
    have h3 : fullArenaClauseSize sC cr.toNat = fullArenaClauseSizeCore sC.core cr.toNat := rfl
    rw [hsz_cr4] at h3; rw [← h3] at h1; omega
  have htmp_l := hmap2.tmp_len; have hnsz_l := hmap2.nsz_le; have hcv_l := hmap2.cv_le
  have hsz_sC_get : sC.core.arena[cr.toNat + 2]? = some sz32 := by
    unfold fullArenaClauseSize fullArenaClauseSizeCore at hsz_cr4
    have harC_l : cr.toNat + 2 < sC.core.arena.length := by
      rw [hinvC.1.core_ok.arena_len_arr, ← har4]; exact hcr_bd2
    rw [List.getElem?_eq_getElem harC_l, Option.getD_some] at hsz_cr4
    rw [List.getElem?_eq_getElem harC_l]; congr 1; exact BitVec.eq_of_toNat_eq hsz_cr4
  have har4_sz : ar4[cr.toNat + 2]? = some sz32 := by
    rw [hout4 (cr.toNat + 2) (Or.inl (by omega))]; exact hsz_sC_get
  have hlits_eq : fullArenaClauseLits s4 cr.toNat = ((tmp2.take nsz2.toNat).map BitVec.toNat) := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; dsimp only [s4]
    rw [hout4 (cr.toNat + 2) (Or.inl (by omega))]
    have hsz_ar4 : (sC.core.arena[cr.toNat + 2]?.getD 0#32).toNat = sz32.toNat := hsz_cr4
    rw [hsz_ar4, ← hnsz_eq,
      show nsz2.toNat = (tmp2.take nsz2.toNat).length by
        rw [List.length_take_of_le (by omega)]]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_take, List.length_drop, har4]; omega
    · intro j hj1 _; simp only [List.length_map, List.length_take] at hj1
      have hj : j < nsz2.toNat := by omega
      simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
      have hq := htmp_cp j hj
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hq
      exact congrArg BitVec.toNat (Option.some.inj hq)
  obtain ⟨hinv4, hrefs4⟩ := m6_denseInvW_replaceSameLen hinvC hcr_ref hng_sC har4
    (fun i hi => by rw [hsz_cr4, ← hnsz_eq] at hi; exact hout4 i hi)
    (fun l hl => by
      rw [hlits_eq, List.mem_iff_getElem] at hl; obtain ⟨j, hj, rfl⟩ := hl
      have hj' : j < nsz2.toNat := by simp only [List.length_map, List.length_take] at hj; omega
      simp only [List.getElem_map, List.getElem_take]
      have := hsC_cv ▸ hmap2.tmp_lt j hj'
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this)
    (by rw [hlits_eq, List.map_map]; exact hmap2.nodup)
    (by rw [hlits_eq]; exact hhent4)
  exact ⟨har4_sz, hinv4, hrefs4⟩

/-- `29/39`: Parametric `Func.wp` proof for `full_m6_els_ar`. -/
theorem full_m6_els_ar_wp (Γ : Env)
    (hWatch : M6EnvSpec Γ "full_watch_push" Full.fullWatchPushSpec)
    (hAddUnit : M6EnvSpec Γ "full_add_unit" Full.fullAddUnitSpec)
    (hAddBin : M6EnvSpec Γ "full_add_bin" Full.fullAddBinSpec) :
    ∀ args m Q X, m6ElsArSpec args m Q X →
      Func.wp Γ full_m6_els_ar_body args m Q X := by
  rintro ⟨h, cr, rl, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hcr_ref, hrl_lt, hrepr_inv, hm, hQ⟩
  have hcl := hinv.1.core_ok; have hw := hinv.2.1; have hcl0 := hinv.2.2.2.2.2.1
  have hmx := c.hmaxv; have har := c.harena; have hwc := c.hwcap
  unfold dimacsBound at hmx har hwc
  have hcv_le := hcl.cur_vars_le; have hal_le := hcl.arena_len_le
  have har_len := hcl.arena_len_arr; have hrp_len := hcl.repr_len
  have hlm_len := hinv.1.core_ok.lit_mark_len; have htmp_len := hinv.1.core_ok.tmp_len_arr
  have hwf_cr := hw.arena.refs_wf cr.toNat hcr_ref
  have hcr_bd : cr.toNat < s.core.arena.length := by
    have := hwf_cr.2.2.1; have := hwf_cr.2.2.2.1; omega
  have hcr2_bd : cr.toNat + 2 < s.core.arena.length := by
    have := hwf_cr.2.2.1; have := hwf_cr.2.2.2.1; omega
  have hcr1_eq : (cr.setWidth 64 + 1#64).toNat = cr.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hcr2_eq : (cr.setWidth 64 + 2#64).toNat = cr.toNat + 2 := by
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, show (2#64 : BitVec 64).toNat = 2 from rfl,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hcr2_mod : (cr.toNat + 2) % 2 ^ 64 = cr.toNat + 2 := Nat.mod_eq_of_lt (by omega)
  have hsz_core : fullArenaClauseSizeCore s.core cr.toNat =
      (s.core.arena[cr.toNat + 2]'hcr2_bd).toNat := by
    unfold fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem hcr2_bd, Option.getD_some]
  have hsz_core_3 : 3 ≤ (s.core.arena[cr.toNat + 2]'hcr2_bd).toNat := by
    simpa [hsz_core] using hwf_cr.2.1
  have hsz_core_bd : cr.toNat + 3 + (s.core.arena[cr.toNat + 2]'hcr2_bd).toNat ≤
      s.core.arena_len := by
    have h1 : cr.toNat + 3 + fullArenaClauseSizeCore s.core cr.toNat ≤
        fullArenaNextOff s.core.arena s.core.arena_len cr.toNat := hwf_cr.2.2.1
    have h2 : fullArenaNextOff s.core.arena s.core.arena_len cr.toNat ≤ s.core.arena_len :=
      hwf_cr.2.2.2.1
    omega
  have hsz32_mod : s.core.arena[(cr.toNat + 2) % 2 ^ 64]'(by
      rw [hcr2_mod]; exact hcr2_bd) = s.core.arena[cr.toNat + 2]'hcr2_bd :=
    m6_getElem_congr hcr2_mod (by rw [hcr2_mod]; exact hcr2_bd) hcr2_bd
  c0_hsplit
  · exfalso; bv_omega
  c0_hsplit
  · c0_hsteps!; exact m6_els_ar_ret_noop hinv hm hQ
  c0_hsplit
  · exfalso
    have h2 : (s.core.arena[(cr.toNat + 2) % 2 ^ 64]'(by
        rw [hcr2_mod]; exact hcr2_bd)).toNat < 3 := by assumption
    rw [congrArg BitVec.toNat hsz32_mod] at h2; omega
  c0_hsplit
  · exfalso
    have hlt : s.core.arena_len % 2 ^ 64 < (cr.toNat + 3 +
        (s.core.arena[(cr.toNat + 2) % 2 ^ 64]'(by
          rw [hcr2_mod]; exact hcr2_bd)).toNat) % 2 ^ 64 := by assumption
    rw [congrArg BitVec.toNat hsz32_mod] at hlt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hlt
    omega
  -- Now `cr.toNat ∈ fullArenaClauseRefs s` is non-garbage (`PH_GARB = 0`).
  have hng_cr : fullArenaClauseGarb s cr.toNat = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
    rw [List.getElem?_eq_getElem hcr_bd, Option.getD_some]
    simpa [BitVec.toNat_and, show (0x00080000#32).toNat = 0x80000 from rfl] using
      (by assumption : (s.core.arena[cr.toNat]'hcr_bd &&& 0x00080000#32) = 0#32)
  let sz32 := s.core.arena[cr.toNat + 2]'hcr2_bd
  have hsz32_eq : sz32.toNat = (s.core.arena[cr.toNat + 2]'hcr2_bd).toNat := rfl
  have hsz_c : fullArenaClauseSizeCore s.core cr.toNat = sz32.toNat := hsz_core
  have hsz_def : sz32.toNat = fullArenaClauseSize s cr.toNat := hsz_core.symm
  have hsz3 : 3 ≤ sz32.toNat := hsz_core_3
  have hsz_bd : cr.toNat + 3 + sz32.toNat ≤ s.core.arena_len := hsz_core_bd
  have hsz_ar_bd : cr.toNat + 3 + sz32.toNat ≤ s.core.arena.length := by omega
  have hsz_lt_dim : sz32.toNat < 2 ^ 31 := by omega
  have hcr_lt_dim : cr.toNat < 0x80000000 := by omega
  have hcr_ne : cr ≠ 0xFFFFFFFF#32 := by
    intro h'; rw [h'] at hcr_lt_dim; revert hcr_lt_dim; decide
  have hlits_lt_k : ∀ i (hi : i < sz32.toNat),
      (s.core.arena[cr.toNat + 3 + i]'(by omega)).toNat < 2 * s.core.cur_vars := by
    intro i hi
    have hmem : (s.core.arena[cr.toNat + 3 + i]'(by omega)).toNat ∈
        fullArenaClauseLits s cr.toNat := by
      unfold fullArenaClauseLits
      rw [mem_fullArenaClauseLitsCore_iff (by rw [hsz_c]; exact hsz_ar_bd)]
      exact ⟨i, by rw [hsz_c]; exact hi, rfl⟩
    exact hw.arena.lits_lt cr.toNat hcr_ref hng_cr _ hmem
  have hmaxv_pos : 0 < c.max_vars := by
    have := hlits_lt_k 0 (by omega); omega
  have hent_cr : (cnfOfClauses F_cur).EntailsClause (cnfClause (fullArenaClauseLits s cr.toNat)) :=
    hw.arena.entails cr.toNat hcr_ref hng_cr
  have hlits_all_repr : ∀ i (hi : i < sz32.toNat),
      let x := (s.core.arena[cr.toNat + 3 + i]'(by omega)).toNat
      LitEquiv (cnfOfClauses F_cur) x (s.core.repr[x]?.getD 0#32).toNat := fun i hi =>
    m6_reprFlat_equiv hrepr_inv (hlits_lt_k i hi)
  -- Loop 1 (`while (k < sz)` check if any literal changes under `repr`)
  c0_hsteps_nogrp
  refine wp_join_state (ts := [.bool, i32])
    (proj := fun p : Bool × BitVec 32 => (p.1, p.2, ()))
    (fun (_chg, _k) m1 => m1 = m) ?_ ?_
  · rintro _ ⟨chg1, _k1⟩ m1 hm1
    subst m1
    c0_hsplit
    · -- `chg = true`: Loop 2 (`_k2, taut2, nsz2`) -> Loop 3 -> GARB / Unit / Bin / Replace+Shrink
      c0_hsteps_nogrp
      refine wp_join_state (ts := [i32, .bool, i32])
        (proj := fun p : BitVec 32 × Bool × BitVec 32 => (p.1, p.2.1, p.2.2, ()))
        (fun (_k2, taut2, nsz2) m2 => ∃ (lm2 : List (BitVec 8)) (tmp2 : List (BitVec 32)),
          nsz2.toNat ≤ sz32.toNat ∧
          M6ElsLitMapOk c s lm2 tmp2 nsz2.toNat ∧
          (taut2 = false →
            ∀ i (hi : i < sz32.toNat),
              let x := (s.core.arena[cr.toNat + 3 + i]'(by omega)).toNat
              ∃ j < nsz2.toNat,
                (tmp2[j]?.getD 0#32).toNat = (s.core.repr[x]?.getD 0#32).toNat) ∧
          (FullMem c { s with core := { s.core with lit_mark := lm2, tmp := tmp2 } } ⋆ R) m2)
        ?_ ?_
      · rintro _ ⟨_k2, taut2, nsz2⟩ m2 ⟨lm2, tmp2, hnsz_sz, hmap2, hcov2, hm2⟩
        dsimp only at hm2
        -- Loop 3: `k = 0; while (k < nsz) { lm[tmp[k]] = 0; k++; }`
        c0_hsteps_nogrp
        refine wp_while_state (ts := [i32]) (proj := fun k : BitVec 32 => (k, ()))
          (μ := fun k => nsz2.toNat - k.toNat)
          (Inv := fun k ml => k.toNat ≤ nsz2.toNat ∧ ∃ lmL : List (BitVec 8),
            lmL.length = 2 * c.max_vars ∧
            (∀ l < 2 * c.max_vars,
              lmL[l]?.getD 0#8 =
                if decide (∃ j < nsz2.toNat, k.toNat ≤ j ∧
                  (tmp2[j]?.getD 0#32).toNat = l) then 1#8 else 0#8) ∧
            (FullMem c { s with core := { s.core with lit_mark := lmL, tmp := tmp2 } } ⋆ R) ml)
          ?_ ?_
        · intro J3 hJ3; c0_hsteps!
          exact hJ3 0#32 m2 ⟨Nat.zero_le _, lm2, hmap2.lm_len, fun l hl => by
            rw [hmap2.map l hl]
            simp only [show (0#32 : BitVec 32).toNat = 0 from rfl, Nat.zero_le, true_and], hm2⟩
        · rintro J3 k3 ml ⟨hk3, lm3, hlm3, hmap3, hml⟩ ih3
          c0_hsplit
          · have hk_lt : k3.toNat < nsz2.toNat := ‹_›
            have hk1 : (k3 + 1#32).toNat = k3.toNat + 1 := by bv_omega
            have hnsz_le := hmap2.nsz_le
            have htk_lt : (tmp2[k3.toNat]'(by have := hmap2.tmp_len; omega)).toNat <
                2 * s.core.cur_vars := by
              have := hmap2.tmp_lt k3.toNat hk_lt
              rwa [List.getElem?_eq_getElem (by have := hmap2.tmp_len; omega),
                Option.getD_some] at this
            have htk_lm : (tmp2[k3.toNat]'(by have := hmap2.tmp_len; omega)).toNat <
                lm3.length := by rw [hlm3]; omega
            have htk_bd64 : (BitVec.setWidth 64 k3).toNat < tmp2.length := by
              rw [bv_c0_zext32_64]; have htl := hmap2.tmp_len; omega
            have htk_lm64 : (BitVec.setWidth 64
                (tmp2[(BitVec.setWidth 64 k3).toNat]'htk_bd64)).toNat < lm3.length := by
              rw [bv_c0_zext32_64, m6_getElem_congr (bv_c0_zext32_64 k3) htk_bd64
                (by have htl := hmap2.tmp_len; omega)]
              exact htk_lm
            dsimp only [Prod.fst]
            c0_hsteps_nogrp
            have hm3_nxt : (FullMem c { s with core := { s.core with
                lit_mark := lm3.set (tmp2[k3.toNat]'(by have htl := hmap2.tmp_len; omega)).toNat
                  0#8,
                tmp := tmp2 } } ⋆ R) m := by
              have hidx_tk : (BitVec.setWidth 64
                  (tmp2[(BitVec.setWidth 64 k3).toNat]'htk_bd64)).toNat =
                  (tmp2[k3.toNat]'(by have htl := hmap2.tmp_len; omega)).toNat := by
                rw [bv_c0_zext32_64, m6_getElem_congr (bv_c0_zext32_64 k3) htk_bd64
                  (by have htl := hmap2.tmp_len; omega)]
              dsimp only at hm
              rwa [← hidx_tk]
            refine ih3 (k3 + 1#32) _ (by rw [hk1]; omega) ⟨by omega,
              lm3.set (tmp2[k3.toNat]'(by have := hmap2.tmp_len; omega)).toNat 0#8,
              by simp [hlm3], by rw [hk1]; exact m6_els_ar_loop3_step_ok hmap2 hk_lt hlm3 hmap3,
              hm3_nxt⟩
          · -- Exit Loop 3: `lm` is cleared -> `FullDenseInvW` restored on `sC`!
            have hk_eq : k3.toNat = nsz2.toNat := by
              have hle : ¬ k3.toNat < nsz2.toNat := by assumption
              omega
            let sC : FullState := { s with core := { s.core with lit_mark := lm3, tmp := tmp2 } }
            have hlm_zero : ∀ l < 2 * c.max_vars, lm3[l]?.getD 0#8 = 0#8 := fun l hl => by
              rw [hmap3 l hl, hk_eq]
              rw [decide_eq_false (by rintro ⟨j, h1, h2, _⟩; omega)]; rfl
            have hinvC : FullDenseInvW c F0 F_cur sC :=
              m6_denseInvW_set_litMark_clear hinv hlm3 hmap2.tmp_len hlm_zero
            have hsc_refs : fullArenaClauseRefs sC = fullArenaClauseRefs s := by
              unfold fullArenaClauseRefs fullArenaClauseRefsCore; rfl
            have hent_tmp : taut2 = false →
                (cnfOfClauses F_cur).EntailsClause
                  (cnfClause ((tmp2.take nsz2.toNat).map BitVec.toNat)) := by
              intro htf
              refine m6_entails_clause_subst (cs := fullArenaClauseLits s cr.toNat) ?_ hent_cr
              intro lit hl
              unfold fullArenaClauseLits at hl
              rw [mem_fullArenaClauseLitsCore_iff (by rw [hsz_c]; exact hsz_ar_bd)] at hl
              obtain ⟨i, hi, hig⟩ := hl
              have hi' : i < sz32.toNat := by rwa [hsz_c] at hi
              have hlig : lit = (s.core.arena[cr.toNat + 3 + i]'(by omega)).toNat := hig.symm
              obtain ⟨j, hj, hje⟩ := hcov2 htf i hi'
              refine ⟨(tmp2[j]?.getD 0#32).toNat, ?_, ?_⟩
              · have htmp2_l := hmap2.tmp_len
                have hnsz2_l := hmap2.nsz_le
                rw [List.mem_map]
                refine ⟨tmp2[j]'(by omega), ?_, ?_⟩
                · rw [List.mem_iff_getElem]
                  exact ⟨j, by simp only [List.length_take]; omega, by rw [List.getElem_take]⟩
                · rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              · rw [hje, hlig]; exact hlits_all_repr i hi'
            -- Branch: `if (taut || nsz <= 2)` (`J3` runs GARB path) vs `else` (Loop 4 + push)
            c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun () m_garb =>
                (taut2 = true ∨ nsz2.toNat ≤ 2) ∧ (FullMem c sC ⋆ R) m_garb)
              ?_ ?_
            · rintro _ ⟨⟩ m_garb ⟨htg, hm_g0⟩
              have hcr64_eq : (BitVec.setWidth 64 cr).toNat = cr.toNat := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
              let ag' := sC.core.arena_garbage + 3#64 + sz32.setWidth 64
              obtain ⟨hinvG, _hrefsG⟩ := m6_denseInvW_markGarb hinvC (hsc_refs ▸ hcr_ref) ag'
              let sG : FullState :=
                { sC with core :=
                  { sC.core with
                    arena := sC.core.arena.set cr.toNat
                      (fullArenaHdr sC cr.toNat ||| 0x00080000#32)
                    arena_garbage := ag' } }
              have hhd_sC : s.core.arena[cr.toNat]'hcr_bd = fullArenaHdr sC cr.toNat := by
                unfold fullArenaHdr fullArenaHdrCore
                change s.core.arena[cr.toNat]'hcr_bd = s.core.arena[cr.toNat]?.getD 0#32
                rw [List.getElem?_eq_getElem hcr_bd, Option.getD_some]
              have hag_eq : sC.core.arena_garbage + 3#64 +
                  (s.core.arena[(cr.toNat + 2) % 2 ^ 64]'(by
                    rw [hcr2_mod]; exact hcr2_bd)).setWidth 64 = ag' := by
                dsimp only [ag']; rw [hsz32_mod]
              c0_hsteps_nogrp
              refine wp_join_group (ts := []) (fun () mU =>
                  (FullMem c sG ⋆ R) mU ∧ ¬ (taut2 = false ∧ nsz2.toNat = 0)) ?_ ?_
              · rintro _ ⟨⟩ mU ⟨hmU, _⟩
                refine wp_join_group (ts := []) (fun () mB =>
                    ∃ sB : FullState,
                      FullDenseInvW c F0 F_cur sB ∧ sB.core.cur_vars = s.core.cur_vars ∧
                      sB.core.fuel = s.core.fuel ∧ sB.core.repr = s.core.repr ∧
                      sB.core.tmp = tmp2 ∧
                      sB.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
                      sB.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
                      sB.scratch.scratch_buf = s.scratch.scratch_buf ∧
                      sB.scratch.work_stk1 = s.scratch.work_stk1 ∧
                      sB.scratch.work_stk2 = s.scratch.work_stk2 ∧ (FullMem c sB ⋆ R) mB) ?_ ?_
                · rintro _ ⟨⟩ mB ⟨sB, hinvB, hcvB, hflB, hrpB, htmpB, htmkB, htrhB, hscrB,
                      hws1B, hws2B, hmB⟩
                  refine wp_join_group (ts := []) (fun () mRet =>
                      ∃ sR : FullState,
                        FullDenseInvW c F0 F_cur sR ∧ sR.core.cur_vars = s.core.cur_vars ∧
                        sR.core.fuel = s.core.fuel ∧ sR.core.repr = s.core.repr ∧
                        sR.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
                        sR.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
                        sR.scratch.scratch_buf = s.scratch.scratch_buf ∧
                        sR.scratch.work_stk1 = s.scratch.work_stk1 ∧
                        sR.scratch.work_stk2 = s.scratch.work_stk2 ∧ (FullMem c sR ⋆ R) mRet) ?_ ?_
                  · rintro _ ⟨⟩ mRet ⟨sR, hinvR, hcvR, hflR, hrpR, htmkR, htrhR, hscrR,
                        hws1R, hws2R, hmR⟩
                    c0_hsteps!
                    exact hQ true sR mRet hinvR hcvR hflR hrpR htmkR htrhR hscrR hws1R hws2R
                      (fun h => Bool.noConfusion h) hmR
                  · intro J6 hJ6
                    c0_hsplit
                    · c0_hsteps!
                      exact hJ6 () mB ⟨sB, hinvB, hcvB, hflB, hrpB, htmkB, htrhB, hscrB,
                        hws1B, hws2B, hmB⟩
                    · have htf : taut2 = false := by
                        cases taut2 <;> first | rfl | contradiction | exact absurd rfl ‹_›
                      c0_hsplit
                      · -- `!taut && nsz == 2`: `full_add_bin`
                        have hn2 : nsz2.toNat = 2 := by bv_omega
                        have htmp2_l := hmap2.tmp_len
                        have hnsz2_l := hmap2.nsz_le
                        have hent2 := hent_tmp htf
                        have htmp0_lt : (tmp2[0]'(by omega)).toNat < 2 * sB.core.cur_vars := by
                          rw [hcvB]; have := hmap2.tmp_lt 0 (by omega)
                          rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
                        have htmp1_lt : (tmp2[1]'(by omega)).toNat < 2 * sB.core.cur_vars := by
                          rw [hcvB]; have := hmap2.tmp_lt 1 (by omega)
                          rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
                        have htake2 : (tmp2.take 2).map BitVec.toNat =
                            [(tmp2[0]'(by omega)).toNat, (tmp2[1]'(by omega)).toNat] := by
                          have hl2 : 2 ≤ tmp2.length := by omega
                          rcases tmp2 with _ | ⟨a, _ | ⟨b, _⟩⟩
                          · exfalso; simp only [List.length_nil] at hl2; omega
                          · exfalso; simp only [List.length_cons, List.length_nil] at hl2; omega
                          · rfl
                        rw [hn2, htake2] at hent2
                        have htmp_lenB : sB.core.tmp.length = c.max_vars :=
                          hinvB.1.core_ok.tmp_len_arr
                        have htmp_posB : 0 < sB.core.tmp.length := by omega
                        have htmp1_posB : 1 < sB.core.tmp.length := by omega
                        c0_hsteps_nogrp
                        c0_call hAddBin
                        refine ⟨c, F0, F_cur, sB, R, rfl, hinvB.1, hinvB.2.1, hinvB.2.2.2.2.2.1,
                          fun _ _ => by
                            simpa only [htmpB, BitVec.toNat_ofNat, Nat.zero_mod,
                              Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64)] using hent2,
                          hmB, ?_⟩
                        intro rB vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec'
                          wstk' wlen' wu' nb' oom' inc' phases' wsort' mBn sBn hlenBn hwBn _
                          hr20 _ hmBn
                        have hinvBn := m6_denseInvW_after_addBin hinvB hlenBn hwBn
                        c0_hsplit
                        · have hrB : rB = 20#64 := by bv_omega
                          c0_hsteps!
                          exact hQ false sBn mBn hinvBn hcvB hflB hrpB htmkB htrhB hscrB
                            hws1B hws2B (fun _ => hr20 hrB) hmBn
                        · c0_hsteps!
                          exact hJ6 () mBn ⟨sBn, hinvBn, hcvB, hflB, hrpB, htmkB, htrhB,
                            hscrB, hws1B, hws2B, hmBn⟩
                      · c0_hsteps!
                        exact hJ6 () mB ⟨sB, hinvB, hcvB, hflB, hrpB, htmkB, htrhB, hscrB,
                          hws1B, hws2B, hmB⟩
                · intro J5 hJ5
                  c0_hsplit
                  · c0_hsteps!
                    exact hJ5 () mU ⟨sG, hinvG, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hmU⟩
                  · have htf : taut2 = false := by
                      cases taut2 <;> first | rfl | contradiction | exact absurd rfl ‹_›
                    c0_hsplit
                    · -- `!taut && nsz == 1`: `full_add_unit`
                      have hn1 : nsz2.toNat = 1 := by bv_omega
                      have htmp2_l := hmap2.tmp_len
                      have hnsz2_l := hmap2.nsz_le
                      have hent1 := hent_tmp htf
                      have htake1 : (tmp2.take 1).map BitVec.toNat =
                          [(tmp2[0]'(by omega)).toNat] := by
                        have hl1 : 1 ≤ tmp2.length := by omega
                        rcases tmp2 with _ | ⟨a, _⟩
                        · exfalso; simp only [List.length_nil] at hl1; omega
                        · rfl
                      rw [hn1, htake1] at hent1
                      have htmp0_lt : (tmp2[0]'(by omega)).toNat < 2 * sG.core.cur_vars := by
                        have := hmap2.tmp_lt 0 (by omega)
                        rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
                      have htmp_lenG : sG.core.tmp.length = c.max_vars :=
                        hinvG.1.core_ok.tmp_len_arr
                      have htmp_posG : 0 < sG.core.tmp.length := by omega
                      c0_hsteps_nogrp
                      c0_call hAddUnit
                      refine ⟨c, F0, F_cur, sG, R, rfl, hinvG.1, hinvG.2.1, fun _ => hent1,
                        hmU, ?_⟩
                      intro okU vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl'
                        inc' phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' mUn sU hlenU hwU
                        hclU hfail _ hmUn
                      have hinvU := m6_denseInvW_after_addUnit hinvG hlenU hwU hclU
                      c0_hsplit
                      · c0_hsteps!
                        exact hJ5 () mUn
                          ⟨sU, hinvU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hmUn⟩
                      · have hokf : okU = false := by
                          cases okU <;> first | rfl | contradiction | exact absurd rfl ‹_›
                        c0_hsteps!
                        exact hQ false sU mUn hinvU rfl rfl rfl rfl rfl rfl rfl rfl
                          (fun _ => hfail htmp0_lt hokf) hmUn
                    · c0_hsteps!
                      exact hJ5 () mU
                        ⟨sG, hinvG, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hmU⟩
              · intro J4 hJ4
                c0_hsplit
                · c0_hsteps!
                  refine hJ4 () _ ⟨?_, fun h => Bool.noConfusion (h.1.symm.trans ‹_›)⟩
                  dsimp only [sG]; rw [← hhd_sC, ← hag_eq]; assumption
                · have htf : taut2 = false := by
                    cases taut2 <;> first | rfl | contradiction | exact absurd rfl ‹_›
                  c0_hsplit
                  · -- `!taut && nsz == 0`: UNSAT!
                    have hnz : nsz2.toNat = 0 := by bv_omega
                    have hent0 := hent_tmp htf; rw [hnz, List.take_zero, List.map_nil] at hent0
                    have huns : (cnfOfClauses F_cur).Unsat := m6_unsat_of_nil_entails hent0
                    c0_hsteps!
                    refine hQ false { sG with core := { sG.core with inconsistent := 1#64 } } _
                      (m6_denseInvW_set_inconsistent hinvG huns) rfl rfl rfl rfl rfl rfl rfl rfl
                      (fun _ => ⟨hinvG.2.1.ext_sound.2 huns, by simp⟩) ?_
                    dsimp only [sG]; rw [← hhd_sC, ← hag_eq]; assumption
                  · c0_hsteps!
                    refine hJ4 () _ ⟨?_, fun h => by bv_omega⟩
                    dsimp only [sG]; rw [← hhd_sC, ← hag_eq]; assumption
            · -- Caller `K` of `J3`: `taut2` vs `nsz2 <= 2` vs Loop 4 -> `watch_push`!
              intro J3 hJ3
              c0_hsplit
              · -- `taut2 = true`: jump `J3`
                c0_hsteps!
                exact hJ3 () _ ⟨Or.inl ‹_›, hml⟩
              c0_hsplit
              · -- `nsz2 ≤ 2`: jump `J3`
                c0_hsteps!
                exact hJ3 () _ ⟨Or.inr ‹_›, hml⟩
              · -- `¬ taut ∧ 3 ≤ nsz2`: copy `tmp2` to `arena`, shrink if `<`, push!
                have htf : taut2 = false := by
                  cases taut2 <;> first | rfl | contradiction | exact absurd rfl ‹_›
                have h3n : 3 ≤ nsz2.toNat := by bv_omega
                have hnsz_le := hmap2.nsz_le
                c0_hsteps_nogrp
                -- Loop 4: `k = 0; while (k < nsz2) { ar[cr + 3 + k] = tmp[k]; k++; }`
                refine wp_while_state (ts := [i32]) (proj := fun k : BitVec 32 => (k, ()))
                  (μ := fun k => nsz2.toNat - k.toNat)
                  (Inv := fun k ml => k.toNat ≤ nsz2.toNat ∧ ∃ ar4 : List (BitVec 32),
                    ar4.length = c.arena_cap ∧
                    (∀ i, i < cr.toNat + 3 ∨ cr.toNat + 3 + k.toNat ≤ i →
                      ar4[i]? = sC.core.arena[i]?) ∧
                    (∀ j < k.toNat, ar4[cr.toNat + 3 + j]? = tmp2[j]?) ∧
                    (FullMem c { sC with core := { sC.core with arena := ar4 } } ⋆ R) ml)
                  ?_ ?_
                · intro J4 hJ4; c0_hsteps!
                  exact hJ4 0#32 _ ⟨Nat.zero_le _, sC.core.arena, hcl.arena_len_arr,
                    fun _ _ => rfl, (fun _ hj => by cases hj), hml⟩
                · rintro J4 k4 ml ⟨hk4, ar4, har4, hout4, hcp4, hml⟩ ih4
                  c0_hsplit
                  · have hk4_lt : k4.toNat < nsz2.toNat := ‹_›
                    have hk1 : (k4 + 1#32).toNat = k4.toNat + 1 := by bv_omega
                    have htk_bd : k4.toNat < tmp2.length := by have := hmap2.tmp_len; omega
                    have htk_bd64 : (BitVec.setWidth 64 k4).toNat < tmp2.length := by
                      rw [bv_c0_zext32_64]; exact htk_bd
                    have hidx_4_mod : (cr.toNat + 3 + k4.toNat) % 2 ^ 64 =
                        cr.toNat + 3 + k4.toNat := Nat.mod_eq_of_lt (by omega)
                    have har_bd : cr.toNat + 3 + k4.toNat < ar4.length := by rw [har4]; omega
                    dsimp only [Prod.fst]
                    c0_hsteps_nogrp
                    have htmp_eq : tmp2[(BitVec.setWidth 64 k4).toNat]'htk_bd64 =
                        tmp2[k4.toNat]'htk_bd :=
                      m6_getElem_congr (bv_c0_zext32_64 k4) htk_bd64 htk_bd
                    refine ih4 (k4 + 1#32) _ (by rw [hk1]; omega) ⟨by omega,
                      ar4.set (cr.toNat + 3 + k4.toNat) (tmp2[k4.toNat]'htk_bd),
                      by simp [har4], fun i hi => ?_, fun j hj => ?_, ?_⟩
                    · rw [List.getElem?_set_ne (by omega)]
                      refine hout4 i ?_
                      rcases hi with h | h
                      · exact Or.inl h
                      · exact Or.inr (by rw [hk1] at h; omega)
                    · by_cases hjk : j = k4.toNat
                      · subst hjk
                        rw [List.getElem?_set_self har_bd, List.getElem?_eq_getElem htk_bd]
                      · rw [List.getElem?_set_ne (by omega)]; exact hcp4 j (by omega)
                    · have hidx_4_c0 :
                          (BitVec.setWidth 64 cr + (3 : BitVec 64) +
                            BitVec.setWidth 64 k4).toNat = cr.toNat + 3 + k4.toNat := by
                        simp only [bv_c0, bv_c0_zext32_64,
                          show ((3 : BitVec 64)).toNat = 3 from rfl]
                        exact Nat.mod_eq_of_lt (by omega)
                      first | (rw [← hidx_4_c0]; assumption)
                            | (rw [← hidx_4_c0, ← htmp_eq]; assumption)
                  · -- Exit Loop 4: check `if (nsz < sz)`, preserve `FullDenseInvW`, watch_push
                    have hk_eq : k4.toNat = nsz2.toNat := by
                      have hle : ¬ k4.toNat < nsz2.toNat := by assumption
                      omega
                    rw [hk_eq] at hout4 hcp4
                    let s4 : FullState := { sC with core := { sC.core with arena := ar4 } }
                    have htmp_cp : ∀ j < nsz2.toNat, ar4[cr.toNat + 3 + j]? = tmp2[j]? := hcp4
                    have hhent4 := hent_tmp htf
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := []) (fun () m5 => ∃ ar5 : List (BitVec 32),
                        let s5 : FullState := { sC with core := { sC.core with arena := ar5 } }
                        FullDenseInvW c F0 F_cur s5 ∧
                        fullArenaClauseRefs s5 = fullArenaClauseRefs sC ∧
                        (FullMem c s5 ⋆ R) m5)
                      ?_ ?_
                    · rintro _ ⟨⟩ m5 ⟨ar5, hinv5, hrefs5, hm5⟩
                      have hnsz_lt_dim : nsz2.toNat < 2 ^ 31 := by omega
                      have hcr5 : cr.toNat ∈ fullArenaClauseRefs
                          { sC with core := { sC.core with arena := ar5 } } := by
                        rw [hrefs5, hsc_refs]; exact hcr_ref
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := []) (fun () mRet =>
                          ∃ sR : FullState,
                            FullDenseInvW c F0 F_cur sR ∧ sR.core.cur_vars = s.core.cur_vars ∧
                            sR.core.fuel = s.core.fuel ∧ sR.core.repr = s.core.repr ∧
                            sR.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
                            sR.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
                            sR.scratch.scratch_buf = s.scratch.scratch_buf ∧
                            sR.scratch.work_stk1 = s.scratch.work_stk1 ∧
                            sR.scratch.work_stk2 = s.scratch.work_stk2 ∧
                            (FullMem c sR ⋆ R) mRet) ?_ ?_
                      · rintro _ ⟨⟩ mRet ⟨sR, hinvR, hcvR, hflR, hrpR, htmkR, htrhR, hscrR,
                            hws1R, hws2R, hmR⟩
                        c0_hsteps!
                        exact hQ true sR mRet hinvR hcvR hflR hrpR htmkR htrhR hscrR hws1R hws2R
                          (fun h => Bool.noConfusion h) hmR
                      · intro JW hJW
                        refine m6_els_ar_push_watched hWatch rfl rfl rfl rfl rfl hinv5 rfl rfl rfl
                          rfl rfl rfl rfl rfl h3n hnsz_lt_dim hcr_lt_dim hcr_ne hcr5 hm5
                          fun ok s' m' hinv' hcv' hfl' hrp' htmk' htrh' hscr' hws1' hws2'
                            hm' => ?_
                        c0_hsplit
                        · c0_hsteps!
                          exact hJW () m' ⟨s', hinv', hcv', hfl', hrp', htmk', htrh', hscr',
                            hws1', hws2', hm'⟩
                        · c0_hsteps!
                          exact hJW () _ ⟨{ s' with core := { s'.core with oom := 1#64 } },
                            m6_denseInvW_set_oom hinv', hcv', hfl', hrp', htmk', htrh', hscr',
                            hws1', hws2', by assumption⟩
                    · intro J5 hJ5
                      c0_hsplit
                      · -- `nsz2 < sz32`: shrink!
                        have hlt_sz : nsz2.toNat < sz32.toNat := by
                          have hlt' : nsz2.toNat < (s.core.arena[(cr.toNat + 2) % 2 ^ 64]'(by
                              rw [hcr2_mod]; exact hcr2_bd)).toNat := by assumption
                          rwa [congrArg BitVec.toNat hsz32_mod] at hlt'
                        have hcr_bd2 : cr.toNat + 2 < ar4.length := by rw [har4]; omega
                        have hcr_bd1 : cr.toNat + 1 < ar4.length := by rw [har4]; omega
                        have har_set_sz :
                            ((ar4.set (cr.toNat + 2) nsz2).set
                              (cr.toNat + 1) 2#32)[cr.toNat + 2]? = some nsz2 := by
                          rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hcr_bd2]
                        c0_hsteps_nogrp
                        rw [hcr2_eq, hcr1_eq] at *
                        refine wp_join_group (ts := []) (fun () m6 => ∃ ar5 : List (BitVec 32),
                            let s5 : FullState := { sC with core := { sC.core with arena := ar5 } }
                            FullDenseInvW c F0 F_cur s5 ∧
                            fullArenaClauseRefs s5 = fullArenaClauseRefs sC ∧
                            (FullMem c s5 ⋆ R) m6) ?_ ?_
                        · rintro _ ⟨⟩ m6 ⟨ar5, hinv5, hrefs5, hm6⟩
                          c0_hsteps!; exact hJ5 () m6 ⟨ar5, hinv5, hrefs5, hm6⟩
                        · intro J6 hJ6
                          c0_hsplit
                          · -- `(hdr &&& PH_SHRK) = 0#32`
                            have hhd0 : (s.core.arena[cr.toNat]'hcr_bd &&& 0x00800000#32) = 0#32 :=
                              ‹_›
                            obtain ⟨_, hinv5, hrefs5⟩ := m6_els_ar_shrink0_ok hinvC
                              (hsc_refs ▸ hcr_ref) hng_cr hcr_bd har4 hcr2_bd hcr_bd2 hcr_bd1
                              har_set_sz rfl rfl hsz_def h3n hlt_sz hhd0 hout4 htmp_cp hmap2 hhent4
                            have hhd_sC' : s.core.arena[cr.toNat]'hcr_bd =
                                fullArenaHdr sC cr.toNat := by
                              unfold fullArenaHdr fullArenaHdrCore
                              change s.core.arena[cr.toNat]'hcr_bd =
                                s.core.arena[cr.toNat]?.getD 0#32
                              rw [List.getElem?_eq_getElem hcr_bd, Option.getD_some]
                            have hcr2_bv : (BitVec.setWidth 64 cr + (2 : BitVec 64)).toNat =
                                cr.toNat + 2 := by
                              simp only [bv_c0, bv_c0_zext32_64,
                                show ((2 : BitVec 64)).toNat = 2 from rfl]
                              exact Nat.mod_eq_of_lt (by omega)
                            have hcr1_bv : (BitVec.setWidth 64 cr + (1 : BitVec 64)).toNat =
                                cr.toNat + 1 := by
                              simp only [bv_c0, bv_c0_zext32_64,
                                show ((1 : BitVec 64)).toNat = 1 from rfl]
                              exact Nat.mod_eq_of_lt (by omega)
                            have hcr3_bv : (BitVec.setWidth 64 cr + (3 : BitVec 64) +
                                  BitVec.setWidth 64 sz32 - (1 : BitVec 64)).toNat =
                                cr.toNat + 3 + sz32.toNat - 1 := by bv_omega
                            have hcr3_bv_mod : (BitVec.setWidth 64 cr + (3 : BitVec 64) +
                                  BitVec.setWidth 64 (s.core.arena[(cr.toNat + 2) % 2 ^ 64]'(by
                                    rw [hcr2_mod]; exact hcr2_bd)) - (1 : BitVec 64)).toNat =
                                cr.toNat + 3 + sz32.toNat - 1 := by
                              rw [m6_getElem_congr hcr2_mod _ hcr2_bd]; exact hcr3_bv
                            c0_hsteps!
                            refine hJ6 () _ ⟨_, hinv5, hrefs5, ?_⟩
                            dsimp only
                            rw [← hhd_sC', ← hcr2_bv, ← hcr1_bv]
                            first
                            | (rw [← hcr3_bv]; assumption)
                            | (rw [← hcr3_bv_mod]; assumption)
                            | (rw [← hcr3_bv, ← bv_c0_zext32_64 cr]; assumption)
                            | (rw [← hcr3_bv_mod, ← bv_c0_zext32_64 cr]; assumption)
                          · -- `(hdr &&& PH_SHRK) ≠ 0#32`
                            have hhd1 : (s.core.arena[cr.toNat]'hcr_bd &&& 0x00800000#32) ≠ 0#32 :=
                              ‹_›
                            obtain ⟨_, hinv5, hrefs5⟩ := m6_els_ar_shrink1_ok hinvC
                              (hsc_refs ▸ hcr_ref) hng_cr hcr_bd har4 hcr_bd2 hcr_bd1 har_set_sz
                              rfl rfl hsz_def h3n hlt_sz hhd1 hout4 htmp_cp hmap2 hhent4
                            have hcr2_bv : (BitVec.setWidth 64 cr + (2 : BitVec 64)).toNat =
                                cr.toNat + 2 := by
                              simp only [bv_c0, bv_c0_zext32_64,
                                show ((2 : BitVec 64)).toNat = 2 from rfl]
                              exact Nat.mod_eq_of_lt (by omega)
                            have hcr1_bv : (BitVec.setWidth 64 cr + (1 : BitVec 64)).toNat =
                                cr.toNat + 1 := by
                              simp only [bv_c0, bv_c0_zext32_64,
                                show ((1 : BitVec 64)).toNat = 1 from rfl]
                              exact Nat.mod_eq_of_lt (by omega)
                            c0_hsteps!
                            refine hJ6 () _ ⟨_, hinv5, hrefs5, ?_⟩
                            dsimp only; rw [← hcr2_bv, ← hcr1_bv]; assumption
                      · -- `nsz2 = sz32`: exact in-place replacement!
                        have hnsz_eq : nsz2.toNat = sz32.toNat := by
                          have hle : ¬ nsz2.toNat < (s.core.arena[(cr.toNat + 2) % 2 ^ 64]'(by
                              rw [hcr2_mod]; exact hcr2_bd)).toNat := by assumption
                          rw [congrArg BitVec.toNat hsz32_mod] at hle; omega
                        have hcr_bd2 : cr.toNat + 2 < ar4.length := by rw [har4]; omega
                        obtain ⟨_, hinv4, hrefs4⟩ := m6_els_ar_same_ok hinvC
                          (hsc_refs ▸ hcr_ref) hng_cr har4 hcr_bd2 rfl rfl hsz_def hnsz_eq hout4
                          htmp_cp hmap2 hhent4
                        c0_hsteps!
                        exact hJ5 () ml ⟨ar4, hinv4, hrefs4, by assumption⟩
      · -- Loop 2 (`group(J2) [[i32, i32]]`: `(kL, nszL)`):
        intro J2 hJ2
        c0_hsteps_nogrp
        refine wp_while_state (ts := [i32, i32])
          (proj := fun p : BitVec 32 × BitVec 32 => (p.1, p.2, ()))
          (μ := fun p => sz32.toNat - p.1.toNat)
          (Inv := fun p ml => p.1.toNat ≤ sz32.toNat ∧ p.2.toNat ≤ p.1.toNat ∧
            ∃ (lm2 : List (BitVec 8)) (tmp2 : List (BitVec 32)),
              M6ElsLitMapOk c s lm2 tmp2 p.2.toNat ∧
              (∀ i < p.1.toNat,
                let x := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
                ∃ j < p.2.toNat,
                  (tmp2[j]?.getD 0#32).toNat = (s.core.repr[x]?.getD 0#32).toNat) ∧
              (FullMem c { s with core := { s.core with lit_mark := lm2, tmp := tmp2 } } ⋆ R) ml)
          ?_ ?_
        · intro L2 hL2
          c0_hsteps!
          exact hL2 (0#32, 0#32) m ⟨Nat.zero_le _, Nat.zero_le _, s.core.lit_mark, s.core.tmp,
            m6_elsLitMapOk_init hinv, (fun _ hi => by cases hi), hm⟩
        · rintro L2 ⟨kL, nszL⟩ ml ⟨hk_le, hnk, lmL, tmpL, hmapL, hcovL, hml⟩ ih2
          dsimp only at *
          c0_hsplit
          · have hk_lt : kL.toNat < sz32.toNat := by
              have hlt' : kL.toNat < (s.core.arena[(cr.toNat + 2) % 2 ^ 64]'(by
                  rw [hcr2_mod]; exact hcr2_bd)).toNat := by assumption
              rwa [congrArg BitVec.toNat hsz32_mod] at hlt'
            have hk1 : (kL + 1#32).toNat = kL.toNat + 1 := by bv_omega
            have hnszL := hmapL.nsz_le
            have hlmL := hmapL.lm_len
            have htmpL := hmapL.tmp_len
            have hidx_k_mod : (cr.toNat + 3 + kL.toNat) % 2 ^ 64 = cr.toNat + 3 + kL.toNat :=
              Nat.mod_eq_of_lt (by omega)
            have hx_lt : (s.core.arena[cr.toNat + 3 + kL.toNat]'(by omega)).toNat <
                2 * s.core.cur_vars := hlits_lt_k kL.toNat hk_lt
            have hx_rp : (s.core.arena[cr.toNat + 3 + kL.toNat]'(by omega)).toNat <
                s.core.repr.length := by rw [hrp_len]; omega
            dsimp only [Prod.fst]
            c0_hsteps_nogrp
            refine wp_join_state (ts := [i32]) (proj := fun rx : BitVec 32 => (rx, ()))
              (fun rx ml' => ml' = ml ∧
                rx = s.core.repr[(s.core.arena[cr.toNat + 3 + kL.toNat]'(by omega)).toNat]'hx_rp)
              ?_ ?_
            · rintro _ rx ml1 ⟨hml1, hrx_eq⟩
              subst ml1
              have hrx_lt : rx.toNat < 2 * s.core.cur_vars := by
                rw [hrx_eq]
                have := m6_reprFlat_lt hrepr_inv hx_lt
                rwa [List.getElem?_eq_getElem hx_rp, Option.getD_some] at this
              have hrx_xor : (rx ^^^ 1#32).toNat < 2 * s.core.cur_vars := by
                rw [m6_els_bv32_xor1_toNat, nat_xor1_cases]; split <;> omega
              c0_hsteps_nogrp
              refine wp_join_state (ts := [.bool, i32])
                (proj := fun p : Bool × BitVec 32 => (p.1, p.2, ()))
                (fun (_tb, nsz') ml' => nsz'.toNat ≤ kL.toNat + 1 ∧
                  ∃ lm' tmp', M6ElsLitMapOk c s lm' tmp' nsz'.toNat ∧
                    (∀ i < kL.toNat + 1,
                      let x := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
                      ∃ j < nsz'.toNat,
                        (tmp'[j]?.getD 0#32).toNat = (s.core.repr[x]?.getD 0#32).toNat) ∧
                    (FullMem c { s with core := { s.core with lit_mark := lm', tmp := tmp' } }
                      ⋆ R) ml')
                ?_ ?_
              · rintro _ ⟨_tb, nsz'⟩ ml' ⟨hnk', lm', tmp', hmap', hcov', hm'⟩
                c0_hsteps!
                exact @ih2 (kL + 1#32, nsz') ml' (by dsimp only; rw [hk1]; omega)
                  ⟨by dsimp only; rw [hk1]; omega, by dsimp only; rw [hk1]; exact hnk',
                   lm', tmp', hmap', (by simpa only [hk1] using hcov'), hm'⟩
              · intro J4 hJ4
                c0_hsplit; rotate_left
                · exfalso
                  simp only [bv_c0] at *
                  have : 2 * s.core.cur_vars < 2 ^ 64 := by omega
                  omega
                c0_hsplit
                · -- `lm[rx ^ 1] != 0`: `taut = true; break` -> jump `J2 (kL, true, nszL)`
                  c0_hsteps!
                  exact hJ2 (kL, true, nszL) ml ⟨lmL, tmpL, by dsimp only; omega, hmapL,
                    (fun h => Bool.noConfusion h), hml⟩
                · -- `lm[rx ^ 1] == 0`
                  have h1_zero : lmL[(rx ^^^ 1#32).toNat]?.getD 0#8 = 0#8 := by
                    have hlm_bd1 : rx.toNat ^^^ 1 < lmL.length := by
                      rw [← m6_els_bv32_xor1_toNat, hlmL]; omega
                    rw [← m6_els_bv32_xor1_toNat] at hlm_bd1
                    rw [List.getElem?_eq_getElem hlm_bd1, Option.getD_some,
                      ← bv8_zext32_eq0_iff]
                    simpa only [m6_els_bv32_xor1_toNat] using (‹_› :
                      BitVec.setWidth 32 (lmL[rx.toNat ^^^ 1]'(by
                        rwa [← m6_els_bv32_xor1_toNat])) = 0#32)
                  refine wp_join_state (ts := [i32]) (proj := fun n : BitVec 32 => (n, ()))
                    (fun nsz' ml' => nsz'.toNat ≤ kL.toNat + 1 ∧
                      ∃ lm' tmp', M6ElsLitMapOk c s lm' tmp' nsz'.toNat ∧
                        (∀ i < kL.toNat + 1,
                          let x := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
                          ∃ j < nsz'.toNat,
                            (tmp'[j]?.getD 0#32).toNat = (s.core.repr[x]?.getD 0#32).toNat) ∧
                        (FullMem c { s with core := { s.core with lit_mark := lm', tmp := tmp' } }
                          ⋆ R) ml')
                    ?_ ?_
                  · rintro _ nsz' ml' hst
                    c0_hsteps!; exact hJ4 (false, nsz') ml' hst
                  · intro J5 hJ5
                    c0_hsplit
                    · have h0_zero : lmL[rx.toNat]?.getD 0#8 = 0#8 := by
                        rw [List.getElem?_eq_getElem (by rw [hlmL]; omega),
                          Option.getD_some, ← bv8_zext32_eq0_iff]
                        exact ‹_›
                      obtain ⟨hnsz_mx, hmap'⟩ := m6_elsLitMapOk_push hmapL hrx_lt h0_zero h1_zero
                      have hnsz_lt_tl : (BitVec.setWidth 64 nszL).toNat < tmpL.length := by
                        rw [htmpL, bv_c0_zext32_64]; omega
                      c0_hsplit; rotate_left
                      · exfalso
                        rw [bv_c0_zext32_64] at *; omega
                      have hnsz1 : (nszL + 1#32).toNat = nszL.toNat + 1 := by bv_omega
                      c0_hsteps!
                      refine hJ5 (nszL + 1#32) _ ⟨by rw [hnsz1]; omega, _, _,
                        by rw [hnsz1]; exact hmap', fun i hi => ?_, by assumption⟩
                      by_cases hik : i = kL.toNat
                      · subst hik
                        refine ⟨nszL.toNat, by rw [hnsz1]; omega, ?_⟩
                        rw [List.getElem?_set_self (by rw [htmpL]; omega), Option.getD_some,
                          List.getElem?_eq_getElem
                            (by omega : cr.toNat + 3 + kL.toNat < s.core.arena.length),
                          Option.getD_some,
                          List.getElem?_eq_getElem hx_rp, Option.getD_some, ← hrx_eq]
                      · obtain ⟨j, hj, hje⟩ := hcovL i (by omega)
                        refine ⟨j, by rw [hnsz1]; omega, ?_⟩
                        rw [List.getElem?_set_ne (by omega)]; exact hje
                    · have h0_nz : lmL[rx.toNat]?.getD 0#8 ≠ 0#8 := by
                        rw [List.getElem?_eq_getElem (by rw [hlmL]; omega), Option.getD_some]
                        intro he0
                        apply (‹_› : ¬ BitVec.setWidth 32
                          (lmL[rx.toNat]'(by rw [hlmL]; omega)) = 0#32)
                        exact (bv8_zext32_eq0_iff _).mpr he0
                      have hrx_cov : ∃ j < nszL.toNat,
                          (tmpL[j]?.getD 0#32).toNat = (s.core.repr[(s.core.arena[cr.toNat + 3 +
                            kL.toNat]'(by omega)).toNat]?.getD 0#32).toNat := by
                        have hml' := hmapL.map rx.toNat (by omega)
                        rw [List.getElem?_eq_getElem hx_rp, Option.getD_some, ← hrx_eq]
                        by_cases hex : ∃ j < nszL.toNat, (tmpL[j]?.getD 0#32).toNat = rx.toNat
                        · exact hex
                        · exfalso; rw [decide_eq_false hex] at hml'; exact h0_nz hml'
                      c0_hsteps!
                      refine hJ5 nszL ml ⟨by omega, lmL, tmpL, hmapL, fun i hi => ?_, hml⟩
                      by_cases hik : i = kL.toNat
                      · subst hik; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                        exact hrx_cov
                      · exact hcovL i (by omega)
            · intro J3 hJ3
              have hidx_k_c0 : (BitVec.setWidth 64 cr + (3 : BitVec 64) +
                  BitVec.setWidth 64 kL).toNat = cr.toNat + 3 + kL.toNat := by
                simp only [bv_c0, bv_c0_zext32_64, show ((3 : BitVec 64)).toNat = 3 from rfl]
                exact Nat.mod_eq_of_lt (by omega)
              rw [hidx_k_mod] at *
              c0_hsplit
              · c0_hsteps!
                refine hJ3 _ ml ⟨rfl, ?_⟩
                dsimp only
                refine m6_getElem_congr ?_ _ hx_rp
                rw [bv_c0_zext32_64]
                exact congrArg BitVec.toNat (m6_getElem_congr hidx_k_c0 _ (by omega))
              · exfalso
                have h3_64 : ((3 : BitVec 64)).toNat = 3 := rfl
                have hidx_l' : (cr.toNat + ((3 : BitVec 64)).toNat + kL.toNat) % 2 ^ 64 =
                    cr.toNat + 3 + kL.toNat := by
                  rw [h3_64]; exact Nat.mod_eq_of_lt (by omega)
                have hcv_lt : s.core.cur_vars < 2 ^ 64 := by omega
                have hcv2_lt : 2 * s.core.cur_vars < 2 ^ 64 := by omega
                simp only [bv_c0, hidx_l', Nat.mod_eq_of_lt hcv_lt,
                  Nat.mod_eq_of_lt hcv2_lt] at hc
                omega
          · -- Natural exit `kL = sz32` with `taut = false`:
            have hk_eq : kL.toNat = sz32.toNat := by
              have hle : ¬ kL.toNat < (s.core.arena[(cr.toNat + 2) % 2 ^ 64]'(by
                  rw [hcr2_mod]; exact hcr2_bd)).toNat := by assumption
              rw [congrArg BitVec.toNat hsz32_mod] at hle; omega
            c0_hsteps!
            refine hJ2 (kL, false, nszL) ml ⟨lmL, tmpL, by dsimp only; omega, hmapL,
              (fun _ i hi => ?_), hml⟩
            rw [← hk_eq] at hi
            obtain ⟨j, hj, hje⟩ := hcovL i hi
            refine ⟨j, hj, ?_⟩
            rw [List.getElem?_eq_getElem
              (by omega : cr.toNat + 3 + i < s.core.arena.length), Option.getD_some] at hje
            exact hje
    · -- `chg1 = false`: push original clause `(sz & PW_LIT_MASK, cr)` & return `true`!
      c0_hsteps_nogrp
      refine wp_join_group (ts := []) (fun () mRet =>
          ∃ sR : FullState,
            FullDenseInvW c F0 F_cur sR ∧ sR.core.cur_vars = s.core.cur_vars ∧
            sR.core.fuel = s.core.fuel ∧ sR.core.repr = s.core.repr ∧
            sR.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
            sR.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
            sR.scratch.scratch_buf = s.scratch.scratch_buf ∧
            sR.scratch.work_stk1 = s.scratch.work_stk1 ∧
            sR.scratch.work_stk2 = s.scratch.work_stk2 ∧ (FullMem c sR ⋆ R) mRet) ?_ ?_
      · rintro _ ⟨⟩ mRet ⟨sR, hinvR, hcvR, hflR, hrpR, htmkR, htrhR, hscrR, hws1R, hws2R, hmR⟩
        c0_hsteps!
        exact hQ true sR mRet hinvR hcvR hflR hrpR htmkR htrhR hscrR hws1R hws2R
          (fun h => Bool.noConfusion h) hmR
      · intro JW hJW
        refine m6_els_ar_push_watched hWatch rfl rfl (by
            dsimp only [Arg.val]
            first
            | exact congrArg (· &&& 0x7FFFFFFF#32) hsz32_mod
            | (rw [m6_getElem_congr hcr2_eq _ hcr2_bd]; rfl)
            | rfl)
          rfl rfl hinv rfl rfl rfl rfl rfl rfl rfl rfl hsz3 hsz_lt_dim hcr_lt_dim hcr_ne
          hcr_ref hm fun ok s' m' hinv' hcv' hfl' hrp' htmk' htrh' hscr' hws1' hws2' hm' => ?_
        c0_hsplit
        · c0_hsteps!
          exact hJW () m' ⟨s', hinv', hcv', hfl', hrp', htmk', htrh', hscr', hws1', hws2', hm'⟩
        · c0_hsteps!
          exact hJW () _ ⟨{ s' with core := { s'.core with oom := 1#64 } },
            m6_denseInvW_set_oom hinv', hcv', hfl', hrp', htmk', htrh', hscr', hws1', hws2',
            by assumption⟩
  · -- Loop 1 (`group(J1) [[i32]]`):
    intro J1 hJ1
    c0_hsteps_nogrp
    refine wp_while_state (ts := [i32]) (proj := fun k : BitVec 32 => (k, ()))
      (μ := fun k => sz32.toNat - k.toNat)
      (Inv := fun k ml => k.toNat ≤ sz32.toNat ∧ ml = m) ?_ ?_
    · intro L1 hL1; c0_hsteps!; exact hL1 0#32 m ⟨Nat.zero_le _, rfl⟩
    · rintro L1 kL ml ⟨hk_le, hml_eq⟩ ih1
      c0_hsplit
      · have hk_lt : kL.toNat < sz32.toNat := by
          have hlt' : kL.toNat < (s.core.arena[(cr.toNat + 2) % 2 ^ 64]'(by
              rw [hcr2_mod]; exact hcr2_bd)).toNat := by assumption
          rwa [congrArg BitVec.toNat hsz32_mod] at hlt'
        have hk1 : (kL + 1#32).toNat = kL.toNat + 1 := by bv_omega
        have hidx_k_mod : (cr.toNat + 3 + kL.toNat) % 2 ^ 64 = cr.toNat + 3 + kL.toNat :=
          Nat.mod_eq_of_lt (by omega)
        have hidx_k_ar : (BitVec.setWidth 64 cr + (3 : BitVec 64) +
            BitVec.setWidth 64 kL).toNat < s.core.arena.length := by
          simp only [bv_c0, bv_c0_zext32_64, show ((3 : BitVec 64)).toNat = 3 from rfl]
          rw [Nat.mod_eq_of_lt (by omega)]; exact Nat.lt_of_lt_of_le (by omega) hsz_ar_bd
        have hl_lt : (s.core.arena[cr.toNat + 3 + kL.toNat]'(by omega)).toNat <
            2 * s.core.cur_vars := hlits_lt_k kL.toNat hk_lt
        have hm_ml : (FullMem c s ⋆ R) ml := hml_eq ▸ hm
        c0_hsteps_nogrp; dsimp only [Prod.fst]; c0_hsteps_nogrp
        refine wp_join_group (ts := []) (fun () ml' => ml' = m) ?_ ?_
        · rintro _ ⟨⟩ ml' hme
          c0_hsteps!; exact ih1 (kL + 1#32) ml' (by omega) ⟨by omega, hme⟩
        · intro J2 hJ2
          have h3_64 : ((3 : BitVec 64)).toNat = 3 := rfl
          have hidx_k_c0' : (cr.toNat + (3 : BitVec 64).toNat + kL.toNat) % 2 ^ 64 =
              cr.toNat + 3 + kL.toNat := by
            rw [h3_64]; exact Nat.mod_eq_of_lt (by omega)
          have hcv_lt : s.core.cur_vars < 2 ^ 64 := by omega
          have hcv2_lt : 2 * s.core.cur_vars < 2 ^ 64 := by omega
          c0_hsplit
          · c0_hsplit
            · c0_hsteps!; exact hJ1 (true, kL) ml hml_eq
            · c0_hsteps!; exact hJ2 () ml hml_eq
          · exfalso
            simp only [bv_c0, hidx_k_c0', Nat.mod_eq_of_lt hcv_lt,
              Nat.mod_eq_of_lt hcv2_lt] at hc
            omega
      · c0_hsteps!; exact hJ1 (false, kL) ml hml_eq

/-! ## 4. `full_m6_els_lit_wp` (`30/39`) -/

private structure M6ElsLitLoop (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sL : FullState) : Prop where
  dinv : FullDenseInvW c F0 F_cur sL
  cv : sL.core.cur_vars = s.core.cur_vars
  fuel : sL.core.fuel = s.core.fuel
  repr : sL.core.repr = s.core.repr
  tmk : sL.scratch.tarjan_mark = s.scratch.tarjan_mark
  trh : sL.scratch.tarjan_reach = s.scratch.tarjan_reach
  scr : sL.scratch.scratch_buf = s.scratch.scratch_buf
  ws1 : sL.scratch.work_stk1 = s.scratch.work_stk1
  ws2 : sL.scratch.work_stk2 = s.scratch.work_stk2

private theorem m6_elsLitLoop_exit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} {R : Mem 64 → Prop} {mL : Mem 64} {Q : Post [.bool]}
    (h : M6ElsLitLoop c F0 F_cur s sL) (hmL : (FullMem c sL ⋆ R) mL)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.repr = s.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Q (decide (sL.core.inconsistent = 0#64), ()) mL := by
  by_cases hinc : sL.core.inconsistent = 0#64
  · rw [decide_eq_true hinc]
    exact hQ true sL mL h.dinv h.cv h.fuel h.repr h.tmk h.trh h.scr h.ws1 h.ws2
      (fun hn => Bool.noConfusion hn) hmL
  · rw [decide_eq_false hinc]
    exact hQ false sL mL h.dinv h.cv h.fuel h.repr h.tmk h.trh h.scr h.ws1 h.ws2
      (fun _ => ⟨h.dinv.2.1.ext_sound.2 (h.dinv.2.1.inconsistent_sound hinc), hinc⟩) hmL

/-- `30/39`: Parametric `Func.wp` proof for `full_m6_els_lit`. -/
theorem full_m6_els_lit_wp (Γ : Env)
    (hAddUnit : M6EnvSpec Γ "full_add_unit" Full.fullAddUnitSpec)
    (hAddBin : M6EnvSpec Γ "full_add_bin" Full.fullAddBinSpec)
    (hElsAr : M6EnvSpec Γ "full_m6_els_ar" m6ElsArSpec) :
    ∀ args m Q X, m6ElsLitSpec args m Q X →
      Func.wp Γ full_m6_els_lit_body args m Q X := by
  rintro ⟨h, l, rl, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hl_lt, hrl_lt, hlr_eq, hrepr_inv, hm, hQ⟩
  have hcl := hinv.1.core_ok; have hmx := c.hmaxv; have hwc := c.hwcap
  unfold dimacsBound at hmx hwc
  have hcv_le := hcl.cur_vars_le
  have h2l_bd : 2 * l.toNat + 1 < s.core.wvec.length := by rw [hcl.wvec_len]; omega
  c0_hsteps_nogrp
  refine wp_while_break_state (brkTs := [i64]) (lpTs := [i64]) (β := BitVec 64 × FullState)
    (fun p => (p.1, ())) (fun p mB => M6ElsLitLoop c F0 F_cur s p.2 ∧ (FullMem c p.2 ⋆ R) mB)
    (α := BitVec 64 × FullState) (fun p => (p.1, ())) (fun p => p.1.toNat)
    (fun p ml => M6ElsLitLoop c F0 F_cur s p.2 ∧ (FullMem c p.2 ⋆ R) ml) ?_ ?_ ?_
  · rintro B ⟨_gB, sB⟩ mB ⟨hB, hmB⟩; c0_hsteps!
    exact m6_elsLitLoop_exit hB hmB hQ
  · rintro B L ⟨gL, sL⟩ ml hB hL ⟨hLoop, hmL⟩
    dsimp only at *
    have hinvL := hLoop.dinv; have hclL := hinvL.1.core_ok; have hwL := hinvL.2.1
    have hcvL_le := hclL.cur_vars_le; have hl_ltL : l.toNat < 2 * sL.core.cur_vars := by
      rw [hLoop.cv]; exact hl_lt
    have h2l_bdL : 2 * l.toNat + 1 < sL.core.wvec.length := by rw [hclL.wvec_len]; omega
    have h2l_mod : (2 * l.toNat + 1) % 2 ^ 64 = 2 * l.toNat + 1 :=
      Nat.mod_eq_of_lt (by omega)
    c0_hsplit; rotate_left; · c0_hsteps!; exact hB (gL, sL) ml ⟨hLoop, hmL⟩
    c0_hsplit; rotate_left; · c0_hsteps!; exact hB (gL, sL) ml ⟨hLoop, hmL⟩
    c0_hsplit; rotate_left; · c0_hsteps!; exact hB (gL, sL) ml ⟨hLoop, hmL⟩
    c0_hsplit; rotate_left; · c0_hsteps!; exact hB (gL, sL) ml ⟨hLoop, hmL⟩
    -- Guard > 0, sz > 0, oom == 0, inconsistent == 0
    have hg_pos : 0 < gL.toNat := by bv_omega
    have hsz_pos : 0 < fullWatchSize sL l.toNat := by
      unfold fullWatchSize fullWatchSizeCore
      rw [List.getElem?_eq_getElem h2l_bdL, Option.getD_some]
      have hpc : 0 < (sL.core.wvec[(2 * l.toNat + 1) % 2 ^ 64]'(by
          rw [h2l_mod]; exact h2l_bdL)).toNat := by assumption
      rwa [← congrArg BitVec.toNat (m6_getElem_congr h2l_mod (by
        rw [h2l_mod]; exact h2l_bdL) h2l_bdL)]
    have hwmL := hwL.watches; unfold ModeWatchesInv at hwmL
    rw [ite_eq_right (fun h0 => hinvL.2.2.2.2.2.2 h0)] at hwmL
    have hbd_l := hwmL.layout.bounds l.toNat hl_ltL
    have hslice_l := hwmL.slices l.toNat hl_ltL
    let offL := fullWatchOff sL l.toNat
    let szL := fullWatchSize sL l.toNat
    have hoff_def : offL = fullWatchOffCore sL.core l.toNat := rfl
    have hsz_def : szL = fullWatchSizeCore sL.core l.toNat := rfl
    have hoffL_lt : offL < sL.core.wstk.length := by
      have := hclL.wstk_len_arr; have := hclL.wlen_le; rw [hoff_def]; omega
    have h2l0_c0 : (BitVec.setWidth 64 l <<< (1 : Nat)).toNat = 2 * l.toNat := by
      rw [m6_els_bv64_shl1_nat, bv_c0_zext32_64, Nat.mod_eq_of_lt (by omega)]
    have h2l1_c0 : (BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat =
        2 * l.toNat + 1 := by
      rw [BitVec.toNat_add, m6_els_bv64_shl1_nat, bv_c0_zext32_64,
        show ((1 : BitVec 64)).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hoffL_bv : (BitVec.setWidth 64
        (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'(by
          rw [h2l0_c0, hclL.wvec_len]; omega))).toNat = offL := by
      rw [bv_c0_zext32_64, m6_getElem_congr h2l0_c0
        (by rw [h2l0_c0, hclL.wvec_len]; omega) (by rw [hclL.wvec_len]; omega)]
      unfold offL fullWatchOff fullWatchOffCore
      rw [List.getElem?_eq_getElem (by rw [hclL.wvec_len]; omega), Option.getD_some]
    have hszL_bv : (BitVec.setWidth 64
        (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat]'(by
          rw [h2l1_c0, hclL.wvec_len]; omega))).toNat = szL := by
      rw [bv_c0_zext32_64, m6_getElem_congr h2l1_c0
        (by rw [h2l1_c0, hclL.wvec_len]; omega) h2l_bdL]
      unfold szL fullWatchSize fullWatchSizeCore
      rw [List.getElem?_eq_getElem h2l_bdL, Option.getD_some]
    have hws_off_lt : (BitVec.setWidth 64
        (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'(by
          rw [h2l0_c0, hclL.wvec_len]; omega))).toNat < sL.core.wstk.length := by
      rw [hoffL_bv]; exact hoffL_lt
    have hw0_c0_eq : ∀ (h1 : (BitVec.setWidth 64 l <<< (1 : Nat)).toNat < sL.core.wvec.length)
        (h2 : (BitVec.setWidth 64
            (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'h1)).toNat <
          sL.core.wstk.length),
        sL.core.wstk[(BitVec.setWidth 64
          (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'h1)).toNat]'h2 =
        sL.core.wstk[offL]'hoffL_lt := fun h1 h2 => m6_getElem_congr hoffL_bv h2 hoffL_lt
    have hg1 : (gL - 1#64).toNat = gL.toNat - 1 := by bv_omega
    have h2l0_mod : (2 * l.toNat) % 2 ^ 64 = 2 * l.toNat := Nat.mod_eq_of_lt (by omega)
    have h2l0_bdL : 2 * l.toNat < sL.core.wvec.length := by rw [hclL.wvec_len]; omega
    have hwv0_eq : (sL.core.wvec[(2 * l.toNat) % 2 ^ 64]'(by
        rw [h2l0_mod]; exact h2l0_bdL)).toNat = offL := by
      rw [m6_getElem_congr h2l0_mod (by rw [h2l0_mod]; exact h2l0_bdL) h2l0_bdL]
      unfold offL fullWatchOff fullWatchOffCore
      rw [List.getElem?_eq_getElem h2l0_bdL, Option.getD_some]
    have hwstk_len_L := hclL.wstk_len_arr
    have hwlen_le_L := hclL.wlen_le
    c0_hsplit
    · -- Binary watch (`(w0 &&& 0x80000000#32) ≠ 0#32`)
      have hw0_some : sL.core.wstk[offL]? = some (sL.core.wstk[offL]'hoffL_lt) :=
        List.getElem?_eq_getElem hoffL_lt
      have hw0_bin : (sL.core.wstk[offL]'hoffL_lt &&& 0x80000000#32) ≠ 0#32 := by
        have hnc : ¬ (sL.core.wstk[offL]'hoffL_lt &&& (2147483648 : BitVec 32)) = 0#32 := by
          first
          | exact ‹¬ (sL.core.wstk[offL]'hoffL_lt &&& (2147483648 : BitVec 32)) = 0#32›
          | (have hh := ‹¬ sL.core.wstk[(BitVec.setWidth 64
                (sL.core.wvec[(BitVec.setWidth 64 l <<< 1).toNat]'(by
                  rw [h2l0_c0, hclL.wvec_len]; omega))).toNat] &&&
                (2147483648 : BitVec 32) = 0#32›
             rwa [hw0_c0_eq] at hh)
          | (have hh := ‹¬ sL.core.wstk[(sL.core.wvec[(2 * l.toNat) % 2 ^ 64]'(by
                rw [h2l0_mod]; exact h2l0_bdL)).toNat] &&&
                (2147483648 : BitVec 32) = 0#32›
             rwa [hwv0_eq] at hh)
        simpa only [show (2147483648 : BitVec 32) = 0x80000000#32 from rfl] using hnc
      obtain ⟨_, hot_lt, hent_bin, hsl_nxt⟩ := m6_denseSlice_step_bin hslice_l hsz_pos hw0_some
        hw0_bin
      have hot_lt_s :
          (sL.core.wstk[offL]'hoffL_lt &&& 0x7FFFFFFF#32).toNat < 2 * sL.core.cur_vars :=
        hot_lt
      have hot_rp :
          (sL.core.wstk[offL]'hoffL_lt &&& 0x7FFFFFFF#32).toNat < sL.core.repr.length := by
        rw [hclL.repr_len]; omega
      let ot := sL.core.wstk[offL]'hoffL_lt &&& 0x7FFFFFFF#32
      let wvec1 := (sL.core.wvec.set (2 * l.toNat) (BitVec.ofNat 32 (offL + 1))).set
        (2 * l.toNat + 1) (BitVec.ofNat 32 (szL - 1))
      let s1 : FullState := { sL with core := { sL.core with
        wvec := wvec1, wusable := sL.core.wusable + 1#64 } }
      have hinv1 := m6_denseInvW_watchPop hinvL hl_ltL (by omega : 1 ≤ szL)
        (sL.core.wusable + 1#64) hsl_nxt
      have hrepr1 : M6ReprFlatInv F_cur (2 * sL.core.cur_vars) sL.core.repr := by
        rw [hLoop.repr, hLoop.cv]; exact hrepr_inv
      have hrot_lt : (sL.core.repr[ot.toNat]'hot_rp).toNat < 2 * sL.core.cur_vars := by
        have := m6_reprFlat_lt hrepr1 hot_lt_s
        rwa [List.getElem?_eq_getElem hot_rp, Option.getD_some] at this
      have hrot_eqv : LitEquiv (cnfOfClauses F_cur) ot.toNat
          (sL.core.repr[ot.toNat]'hot_rp).toNat := by
        have := m6_reprFlat_equiv hrepr1 hot_lt_s
        rwa [List.getElem?_eq_getElem hot_rp, Option.getD_some] at this
      have hent_rep : (cnfOfClauses F_cur).EntailsClause
          (cnfClause [rl.toNat, (sL.core.repr[ot.toNat]'hot_rp).toNat]) :=
        m6_entails_bin_subst hlr_eq hrot_eqv hent_bin
      have hwv_pop1 :
          (sL.core.wvec.set (BitVec.setWidth 64 l <<< (1 : Nat)).toNat
            (BitVec.setWidth 32 (BitVec.setWidth 64
              (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'(by
                rw [h2l0_c0, hclL.wvec_len]; omega)) + (1 : BitVec 64)))).set
            (BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat
            (BitVec.setWidth 32 (BitVec.setWidth 64
              (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat]'(by
                rw [h2l1_c0, hclL.wvec_len]; omega)) - (1 : BitVec 64))) = wvec1 := by
        refine m6_list_set2_eq sL.core.wvec h2l0_c0 h2l1_c0 ?_ ?_
        · apply BitVec.eq_of_toNat_eq
          have h0_bv : BitVec.setWidth 64
              (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'(by
                rw [h2l0_c0, hclL.wvec_len]; omega)) = BitVec.ofNat 64 offL :=
            BitVec.eq_of_toNat_eq (by
              rw [hoffL_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
          rw [h0_bv, BitVec.toNat_setWidth,
            show (BitVec.ofNat 64 offL + (1 : BitVec 64)).toNat = offL + 1 by bv_omega,
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        · apply BitVec.eq_of_toNat_eq
          have h1_bv : BitVec.setWidth 64
              (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat]'(by
                rw [h2l1_c0, hclL.wvec_len]; omega)) = BitVec.ofNat 64 szL :=
            BitVec.eq_of_toNat_eq (by
              rw [hszL_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
          rw [h1_bv, BitVec.toNat_setWidth,
            show (BitVec.ofNat 64 szL - (1 : BitVec 64)).toNat = szL - 1 by bv_omega,
            BitVec.toNat_ofNat]
      c0_hsteps_nogrp
      refine wp_join_state (ts := [i32]) (proj := fun rot : BitVec 32 => (rot, ()))
        (fun rot m1 => rot = sL.core.repr[ot.toNat]'hot_rp ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
      · rintro _ rot m1 ⟨rfl, hm1⟩
        c0_hsteps_nogrp
        c0_hsplit
        · exfalso
          simp only [bv_c0, bv_c0_zext32_64, BitVec.toNat_ofNat] at *
          have hcv_eq := hLoop.cv
          have : 2 * sL.core.cur_vars < 2 ^ 64 := by omega
          omega
        c0_hsplit
        · -- `rl == (rot ^ 1)`: tautology, continue!
          c0_hsteps!
          exact hL (gL - 1#64, s1) m1 (by dsimp only; omega)
            ⟨⟨hinv1, hLoop.cv, hLoop.fuel, hLoop.repr, hLoop.tmk, hLoop.trh, hLoop.scr,
              hLoop.ws1, hLoop.ws2⟩, hm1⟩
        c0_hsplit
        · -- `rl == rot`: `full_add_unit(h, rl)`!
          have hrr : rl.toNat = (sL.core.repr[ot.toNat]'hot_rp).toNat := by
            have : rl = sL.core.repr[ot.toNat]'hot_rp := ‹_›
            rw [this]
          rw [← hrr] at hent_rep
          have hent_u := m6_entails_unit_of_dup hent_rep
          c0_hsteps_nogrp
          c0_call hAddUnit
          refine ⟨c, F0, F_cur, s1, R, rfl, hinv1.1, hinv1.2.1, fun _ => hent_u, hm1, ?_⟩
          intro okU vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
            phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' mU sU hlenU hwU hclU hfail _ hmU
          have hinvU := m6_denseInvW_after_addUnit hinv1 hlenU hwU hclU
          c0_hsplit
          · c0_hsteps!
            exact hL (gL - 1#64, sU) mU (by dsimp only; omega)
              ⟨⟨hinvU, hLoop.cv, hLoop.fuel, hLoop.repr, hLoop.tmk, hLoop.trh, hLoop.scr,
                hLoop.ws1, hLoop.ws2⟩, hmU⟩
          · have hokf : okU = false := by
              cases okU <;> first | rfl | contradiction | exact absurd rfl ‹_›
            c0_hsteps!
            exact hQ false sU mU hinvU hLoop.cv hLoop.fuel hLoop.repr hLoop.tmk hLoop.trh hLoop.scr
              hLoop.ws1 hLoop.ws2 (fun _ => hfail (by rw [hLoop.cv]; exact hrl_lt) hokf) hmU
        · -- `full_add_bin(h, rl, rot)`!
          c0_hsteps_nogrp
          c0_call hAddBin
          refine ⟨c, F0, F_cur, s1, R, rfl, hinv1.1, hinv1.2.1, hinv1.2.2.2.2.2.1,
            fun _ _ => hent_rep, hm1, ?_⟩
          intro rB vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu'
            nb' oom' inc' phases' wsort' mB sB hlenB hwB _ hr20 _ hmB
          have hinvB := m6_denseInvW_after_addBin hinv1 hlenB hwB
          c0_hsplit
          · have hrB : rB = 20#64 := by bv_omega
            c0_hsteps!
            exact hQ false sB mB hinvB hLoop.cv hLoop.fuel hLoop.repr hLoop.tmk hLoop.trh hLoop.scr
              hLoop.ws1 hLoop.ws2 (fun _ => hr20 hrB) hmB
          c0_hsplit
          · c0_hsteps!
            exact hQ true sB mB hinvB hLoop.cv hLoop.fuel hLoop.repr hLoop.tmk hLoop.trh hLoop.scr
              hLoop.ws1 hLoop.ws2 (fun h => Bool.noConfusion h) hmB
          · c0_hsteps!
            exact hL (gL - 1#64, sB) mB (by dsimp only; omega)
              ⟨⟨hinvB, hLoop.cv, hLoop.fuel, hLoop.repr, hLoop.tmk, hLoop.trh, hLoop.scr,
                hLoop.ws1, hLoop.ws2⟩, hmB⟩
      · intro Jr hJr
        c0_hsplit
        · simp only [hw0_c0_eq]
          c0_hsteps!
          refine hJr (sL.core.repr[ot.toNat]'hot_rp) _ ⟨rfl, ?_⟩
          dsimp only [s1]; rw [← hwv_pop1]; assumption
        · exfalso
          simp only [bv_c0] at *
          have hcv_eq := hLoop.cv
          have hm1 : (sL.core.wstk[offL]'hoffL_lt &&& (2147483647 : BitVec 32)).toNat =
              (sL.core.wstk[offL]'hoffL_lt &&& 0x7FFFFFFF#32).toNat := rfl
          simp only [hwv0_eq, hm1] at *
          have : 2 * sL.core.cur_vars < 2 ^ 64 := by omega
          omega
    · -- Occurrence watch (`(w0 &&& 0x80000000#32) = 0#32`)
      have hw0_some : sL.core.wstk[offL]? = some (sL.core.wstk[offL]'hoffL_lt) :=
        List.getElem?_eq_getElem hoffL_lt
      have hw0_occ : (sL.core.wstk[offL]'hoffL_lt &&& 0x80000000#32) = 0#32 := by
        have hc0 : (sL.core.wstk[offL]'hoffL_lt &&& (2147483648 : BitVec 32)) = 0#32 := by
          first
          | exact ‹(sL.core.wstk[offL]'hoffL_lt &&& (2147483648 : BitVec 32)) = 0#32›
          | (have hh := ‹sL.core.wstk[(BitVec.setWidth 64
                (sL.core.wvec[(BitVec.setWidth 64 l <<< 1).toNat]'(by
                  rw [h2l0_c0, hclL.wvec_len]; omega))).toNat] &&&
                (2147483648 : BitVec 32) = 0#32›
             rwa [hw0_c0_eq] at hh)
          | (have hh := ‹sL.core.wstk[(sL.core.wvec[(2 * l.toNat) % 2 ^ 64]'(by
                rw [h2l0_mod]; exact h2l0_bdL)).toNat] &&&
                (2147483648 : BitVec 32) = 0#32›
             rwa [hwv0_eq] at hh)
        simpa only [show (2147483648 : BitVec 32) = 0x80000000#32 from rfl] using hc0
      obtain ⟨hsz2, _, cr, hw1_some, _, hcr_ref, hsl_nxt⟩ :=
        m6_denseSlice_step_occ hslice_l hsz_pos hw0_some hw0_occ
      c0_hsplit
      · exfalso
        have hlt2 : (sL.core.wvec[(2 * l.toNat + 1) % 2 ^ 64]'(by
            rw [h2l_mod]; exact h2l_bdL)).toNat < 2 := by
          have : sL.core.wvec[(2 * l.toNat + 1) % 2 ^ 64].toNat < (2#32).toNat := by assumption
          exact this
        rw [m6_getElem_congr h2l_mod (by rw [h2l_mod]; exact h2l_bdL) h2l_bdL] at hlt2
        have hszL_eq : (sL.core.wvec[2 * l.toNat + 1]'h2l_bdL).toNat = szL := by
          unfold szL fullWatchSize fullWatchSizeCore
          rw [List.getElem?_eq_getElem h2l_bdL, Option.getD_some]
        omega
      · have hsz2_l : 2 ≤ szL := by omega
        have hoff1_lt : offL + 1 < sL.core.wstk.length := by
          have := hclL.wstk_len_arr; have := hclL.wlen_le; rw [hoff_def]; omega
        have hcr_eq : sL.core.wstk[offL + 1]'hoff1_lt = cr := by
          have hq := hw1_some; rw [List.getElem?_eq_getElem hoff1_lt] at hq
          exact Option.some.inj hq
        let wvec1 := (sL.core.wvec.set (2 * l.toNat) (BitVec.ofNat 32 (offL + 2))).set
          (2 * l.toNat + 1) (BitVec.ofNat 32 (szL - 2))
        let s1 : FullState := { sL with core := { sL.core with
          wvec := wvec1, wusable := sL.core.wusable + 2#64 } }
        have hinv1 := m6_denseInvW_watchPop hinvL hl_ltL hsz2 (sL.core.wusable + 2#64) hsl_nxt
        have hrepr1 : M6ReprFlatInv F_cur (2 * s1.core.cur_vars) s1.core.repr := by
          rw [show s1.core.cur_vars = s.core.cur_vars from hLoop.cv,
            show s1.core.repr = s.core.repr from hLoop.repr]; exact hrepr_inv
        have hcr_ref1 : cr.toNat ∈ fullArenaClauseRefs s1 := hcr_ref
        have hwv_pop2 :
            (sL.core.wvec.set (BitVec.setWidth 64 l <<< (1 : Nat)).toNat
              (BitVec.setWidth 32 (BitVec.setWidth 64
                (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'(by
                  rw [h2l0_c0, hclL.wvec_len]; omega)) + (2 : BitVec 64)))).set
              (BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat
              (BitVec.setWidth 32 (BitVec.setWidth 64
                (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat]'(by
                  rw [h2l1_c0, hclL.wvec_len]; omega)) - (2 : BitVec 64))) = wvec1 := by
          refine m6_list_set2_eq sL.core.wvec h2l0_c0 h2l1_c0 ?_ ?_
          · apply BitVec.eq_of_toNat_eq
            have h0_bv : BitVec.setWidth 64
                (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'(by
                  rw [h2l0_c0, hclL.wvec_len]; omega)) = BitVec.ofNat 64 offL :=
              BitVec.eq_of_toNat_eq (by
                rw [hoffL_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
            rw [h0_bv, BitVec.toNat_setWidth,
              show (BitVec.ofNat 64 offL + (2 : BitVec 64)).toNat = offL + 2 by bv_omega,
              BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          · apply BitVec.eq_of_toNat_eq
            have h1_bv : BitVec.setWidth 64
                (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat]'(by
                  rw [h2l1_c0, hclL.wvec_len]; omega)) = BitVec.ofNat 64 szL :=
              BitVec.eq_of_toNat_eq (by
                rw [hszL_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
            rw [h1_bv, BitVec.toNat_setWidth,
              show (BitVec.ofNat 64 szL - (2 : BitVec 64)).toNat = szL - 2 by bv_omega,
              BitVec.toNat_ofNat]
        have hws_off1_lt : (BitVec.setWidth 64
            (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'(by
              rw [h2l0_c0, hclL.wvec_len]; omega)) + (1 : BitVec 64)).toNat <
            sL.core.wstk.length := by
          rw [BitVec.toNat_add, hoffL_bv, show ((1 : BitVec 64)).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega)]; exact hoff1_lt
        have hcr_c0_eq : sL.core.wstk[(BitVec.setWidth 64
            (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'(by
              rw [h2l0_c0, hclL.wvec_len]; omega)) + (1 : BitVec 64)).toNat]'hws_off1_lt = cr := by
          have hoff1_c0 : (BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<<
              (1 : Nat)).toNat]'(by rw [h2l0_c0, hclL.wvec_len]; omega)) +
              (1 : BitVec 64)).toNat = offL + 1 := by
            rw [BitVec.toNat_add, hoffL_bv, show ((1 : BitVec 64)).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega)]
          rw [m6_getElem_congr hoff1_c0 hws_off1_lt hoff1_lt]; exact hcr_eq
        dsimp only [Prod.fst]
        c0_hsteps_nogrp
        c0_call hElsAr
        refine ⟨c, F0, F_cur, s1, R, rfl, hinv1, hcr_c0_eq.symm ▸ hcr_eq ▸ hcr_ref1,
          (by rw [show s1.core.cur_vars = s.core.cur_vars from hLoop.cv]; exact hrl_lt),
          hrepr1, ?_, ?_⟩
        · dsimp only [s1]; rw [← hwv_pop2]; assumption
        intro okA sA mA hinvA hcvA hflA hrpA htmkA htrhA hscrA hws1A hws2A hokfA hmA
        c0_hsplit
        · c0_hsteps!
          exact hL (gL - 1#64, sA) mA (by dsimp only; omega)
            ⟨⟨hinvA, hcvA.trans hLoop.cv, hflA.trans hLoop.fuel, hrpA.trans hLoop.repr,
              htmkA.trans hLoop.tmk, htrhA.trans hLoop.trh, hscrA.trans hLoop.scr,
              hws1A.trans hLoop.ws1, hws2A.trans hLoop.ws2⟩, hmA⟩
        · have hokf : okA = false := by
            cases okA <;> first | rfl | contradiction | exact absurd rfl ‹_›
          c0_hsteps!
          exact hQ false sA mA hinvA (hcvA.trans hLoop.cv) (hflA.trans hLoop.fuel)
            (hrpA.trans hLoop.repr) (htmkA.trans hLoop.tmk) (htrhA.trans hLoop.trh)
            (hscrA.trans hLoop.scr) (hws1A.trans hLoop.ws1) (hws2A.trans hLoop.ws2)
            (fun _ => hokfA hokf) hmA
  · intro B L hB hL; c0_hsteps!
    have h2l_c0 : (BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat =
        2 * l.toNat + 1 := by
      rw [BitVec.toNat_add, m6_els_bv64_shl1_nat, bv_c0_zext32_64,
        show ((1 : BitVec 64)).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [m6_getElem_congr h2l_c0 (by rw [h2l_c0]; exact h2l_bd) h2l_bd,
      ← @Option.getD_some _ (s.core.wvec[2 * l.toNat + 1]'h2l_bd) 0#32,
      ← List.getElem?_eq_getElem h2l_bd]
    exact hL (s.core.wvec[2 * l.toNat + 1]?.getD 0#32 |>.setWidth 64, s) m
      ⟨⟨hinv, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hm⟩

end LeanQbe.T.Examples.Kissat.FullM6Sweep

