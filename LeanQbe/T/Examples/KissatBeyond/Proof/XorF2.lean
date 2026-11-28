/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.KissatBeyond.Ref.XorF2
public import LeanQbe.T.Examples.Kissat.Proof.Ref.Cdcl
public import LeanQbe.T.Examples.Kissat.Proof.Ref.Substitute

/-!
# Soundness Proofs for `XorF2`

Extracted pure-Lean proofs for `XorF2` (zero `Kraken.*` imports).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.KissatBeyond.Ref

open LeanQbe.T.Examples.Kissat.Ref
open Std.Sat

/-! ## 1. Boolean XOR algebra and list XOR evaluation -/

@[simp] theorem xorEvalVars_nil (α : Nat → Bool) : xorEvalVars α [] = false := rfl

theorem xorEvalVars_foldl_shift (α : Nat → Bool) (b : Bool) (vs : List Nat) :
    vs.foldl (fun acc v => acc != α v) b = (b != xorEvalVars α vs) := by
  induction vs generalizing b with
  | nil => simp [xorEvalVars]
  | cons v vs ih =>
    simp only [xorEvalVars, List.foldl_cons, Bool.false_bne] at ih ⊢
    rw [ih (b != α v), ih (α v), Bool.bne_assoc]

@[simp] theorem xorEvalVars_cons (α : Nat → Bool) (v : Nat) (vs : List Nat) :
    xorEvalVars α (v :: vs) = (α v != xorEvalVars α vs) := by
  unfold xorEvalVars
  rw [List.foldl_cons, Bool.false_bne]
  exact xorEvalVars_foldl_shift α (α v) vs

@[simp] theorem xorEvalVars_append (α : Nat → Bool) (vs1 vs2 : List Nat) :
    xorEvalVars α (vs1 ++ vs2) = (xorEvalVars α vs1 != xorEvalVars α vs2) := by
  unfold xorEvalVars
  rw [List.foldl_append]
  exact xorEvalVars_foldl_shift α (xorEvalVars α vs1) vs2

theorem xorEvalVars_singleton (α : Nat → Bool) (v : Nat) :
    xorEvalVars α [v] = α v := by
  simp

theorem xorEvalVars_perm {α : Nat → Bool} {vs1 vs2 : List Nat} (h : vs1.Perm vs2) :
    xorEvalVars α vs1 = xorEvalVars α vs2 := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap x y l =>
    simp only [xorEvalVars_cons]
    cases α x <;> cases α y <;> cases xorEvalVars α l <;> rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem xorVarsSound_perm {F : CNF Nat} {vs1 vs2 : List Nat} {rhs : Bool}
    (hp : vs1.Perm vs2) (h : XorVarsSound F vs1 rhs) : XorVarsSound F vs2 rhs :=
  fun α hα => (xorEvalVars_perm hp).symm.trans (h α hα)

theorem xorEvalVars_symDiffSorted (α : Nat → Bool) (xs ys : List Nat) :
    xorEvalVars α (symDiffSorted xs ys) = (xorEvalVars α xs != xorEvalVars α ys) := by
  fun_induction symDiffSorted xs ys with
  | case1 ys => simp
  | case2 x xs => simp
  | case3 x xs y ys _ ih =>
    simp only [xorEvalVars_cons, ih, Bool.bne_assoc]
  | case4 x xs y ys _ _ ih =>
    simp only [xorEvalVars_cons, ih]
    cases α x <;> cases α y <;> cases xorEvalVars α xs <;> cases xorEvalVars α ys <;> rfl
  | case5 x xs y ys _ _ ih =>
    have hxy : x = y := by omega
    subst hxy
    simp only [xorEvalVars_cons, ih]
    cases α x <;> cases xorEvalVars α xs <;> cases xorEvalVars α ys <;> rfl

private theorem mem_symDiffSorted {xs ys : List Nat} {u : Nat}
    (hu : u ∈ symDiffSorted xs ys) : u ∈ xs ∨ u ∈ ys := by
  fun_induction symDiffSorted xs ys with
  | case1 ys => exact Or.inr hu
  | case2 x xs => exact Or.inl hu
  | case3 x xs y ys _ ih =>
    simp only [List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact Or.inl (by simp)
    · rcases ih hu with h1 | h2
      · exact Or.inl (by simp [h1])
      · exact Or.inr h2
  | case4 x xs y ys _ _ ih =>
    simp only [List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact Or.inr (by simp)
    · rcases ih hu with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (by simp [h2])
  | case5 x xs y ys _ _ ih =>
    rcases ih hu with h1 | h2
    · exact Or.inl (by simp [h1])
    · exact Or.inr (by simp [h2])

theorem symDiffSorted_strictSorted {xs ys : List Nat}
    (hx : xs.Pairwise (· < ·)) (hy : ys.Pairwise (· < ·)) :
    (symDiffSorted xs ys).Pairwise (· < ·) := by
  fun_induction symDiffSorted xs ys with
  | case1 ys => exact hy
  | case2 x xs => exact hx
  | case3 x xs y ys hlt ih =>
    have hx' := List.pairwise_cons.mp hx
    refine List.pairwise_cons.mpr ⟨fun z hz => ?_, ih hx'.2 hy⟩
    rcases mem_symDiffSorted hz with hzx | hzy
    · exact hx'.1 z hzx
    · rcases List.mem_cons.mp hzy with rfl | hzy'
      · exact hlt
      · exact Nat.lt_trans hlt ((List.pairwise_cons.mp hy).1 z hzy')
  | case4 x xs y ys _ hlt ih =>
    have hy' := List.pairwise_cons.mp hy
    refine List.pairwise_cons.mpr ⟨fun z hz => ?_, ih hx hy'.2⟩
    rcases mem_symDiffSorted hz with hzx | hzy
    · rcases List.mem_cons.mp hzx with rfl | hzx'
      · exact hlt
      · exact Nat.lt_trans hlt ((List.pairwise_cons.mp hx).1 z hzx')
    · exact hy'.1 z hzy
  | case5 x xs y ys _ _ ih =>
    exact ih (List.pairwise_cons.mp hx).2 (List.pairwise_cons.mp hy).2

theorem xorVarsSound_symDiffSorted {F : CNF Nat} {xs ys : List Nat} {rx ry : Bool}
    (hx : XorVarsSound F xs rx) (hy : XorVarsSound F ys ry) :
    XorVarsSound F (symDiffSorted xs ys) (rx != ry) := fun α hα => by
  rw [xorEvalVars_symDiffSorted, hx α hα, hy α hα]

/-- Empty XOR row with `rhs = true` (`0 = 1`) directly witnesses UNSAT. -/
theorem unsat_of_xorVars_nil {F : CNF Nat} (h : XorVarsSound F [] true) : F.Unsat := by
  refine CNF.unsat_iff_entails_clause_empty.mpr (CNF.entails_clause_def.mpr fun α hα => ?_)
  have h1 := h α hα
  simp at h1

/-! ## 2. Clause materialization & CNF extraction truth-table soundness -/

private theorem take_succ_eq_append' {α : Type} {xs : List α} {k : Nat} (hk : k < xs.length) :
    xs.take (k + 1) = xs.take k ++ [xs[k]] := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => simp [List.take]
    | succ k =>
      simp only [List.take, ih (Nat.lt_of_succ_lt_succ hk), List.cons_append,
        List.getElem_cons_succ]

theorem xorEvalVars_eq_maskParity_of_clause_unsat {α : Nat → Bool} {vs : List Nat} {mask : Nat}
    (hunsat : ¬(cnfClause (xorMaskClause vs mask)).Sat α) :
    xorEvalVars α vs = maskParity vs.length mask := by
  have hmatch : ∀ i (hi : i < vs.length), α vs[i] = ((mask >>> i) % 2 == 1) := by
    intro i hi
    refine Classical.byContradiction fun hne => hunsat ?_
    rw [clause_sat_cnfClause_iff]
    refine ⟨mkLit vs[i] (!((mask >>> i) % 2 == 1)), ?_, ?_⟩
    · simp only [xorMaskClause, List.mem_map, List.mem_range]
      exact ⟨i, hi, by simp [List.getElem?_eq_getElem hi]⟩
    · rw [litVar_mkLit, litSign_mkLit]
      cases hv : α vs[i] <;> cases hm : ((mask >>> i) % 2 == 1) <;> simp_all
  clear hunsat
  suffices ∀ (k : Nat) (hk : k ≤ vs.length),
      xorEvalVars α (vs.take k) = maskParity k mask by
    simpa [List.take_length] using this vs.length (Nat.le_refl _)
  intro k hk
  induction k with
  | zero => simp [maskParity]
  | succ k ih =>
    have hk_lt : k < vs.length := hk
    have htake : vs.take (k + 1) = vs.take k ++ [vs[k]] := take_succ_eq_append' hk_lt
    rw [htake, xorEvalVars_append, ih (Nat.le_of_lt hk_lt), xorEvalVars_singleton,
      hmatch k hk_lt]
    unfold maskParity
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Materializing any mask clause whose parity equals `!rhs` is entailed by
`XorVarsSound F vs rhs`. -/
theorem entails_xorMaskClause_of_xorVarsSound {F : CNF Nat} {vs : List Nat} {rhs : Bool}
    (hx : XorVarsSound F vs rhs) {mask : Nat} (hp : maskParity vs.length mask = !rhs) :
    F.EntailsClause (cnfClause (xorMaskClause vs mask)) := by
  rw [CNF.entails_clause_def]
  intro α hα
  refine Classical.byContradiction fun hns => ?_
  have heq := xorEvalVars_eq_maskParity_of_clause_unsat hns
  rw [hx α hα, hp] at heq
  cases rhs <;> exact Bool.noConfusion heq

/-- Weight-1 XOR equation (`[v] = rhs`) entails the unit literal `mkLit v rhs`. -/
theorem entails_unit_of_xorVarsSound {F : CNF Nat} {v : Nat} {rhs : Bool}
    (hx : XorVarsSound F [v] rhs) :
    F.EntailsClause (cnfClause [mkLit v rhs]) := by
  rw [CNF.entails_clause_def]
  intro α hα
  rw [sat_cnfClause_singleton]
  have h1 := hx α hα
  simp only [xorEvalVars_singleton] at h1
  cases rhs
  · simp [mkLit, litVar, litSign, show (2 * v + 1) / 2 = v by omega, h1]
  · simp [mkLit, litVar, litSign, h1]

/-- Weight-2 XOR equation (`[v0, v1] = rhs`) entails both binary equivalence clauses. -/
theorem entails_bins_of_xorVarsSound {F : CNF Nat} {v0 v1 : Nat} {rhs : Bool}
    (hx : XorVarsSound F [v0, v1] rhs) :
    F.EntailsClause (cnfClause [mkLit v0 (!rhs), mkLit v1 false]) ∧
    F.EntailsClause (cnfClause [mkLit v0 rhs, mkLit v1 true]) := by
  have hlen2 : ([v0, v1] : List Nat).length = 2 := rfl
  cases rhs
  · constructor
    · have h1 := entails_xorMaskClause_of_xorVarsSound hx (mask := 2)
        (by rw [hlen2]; exact by decide)
      simpa [xorMaskClause, List.range_succ] using h1
    · have h2 := entails_xorMaskClause_of_xorVarsSound hx (mask := 1)
        (by rw [hlen2]; exact by decide)
      simpa [xorMaskClause, List.range_succ] using h2
  · constructor
    · have h1 := entails_xorMaskClause_of_xorVarsSound hx (mask := 3)
        (by rw [hlen2]; exact by decide)
      simpa [xorMaskClause, List.range_succ] using h1
    · have h2 := entails_xorMaskClause_of_xorVarsSound hx (mask := 0)
        (by rw [hlen2]; exact by decide)
      simpa [xorMaskClause, List.range_succ] using h2

/-- Binary pair `(a ∨ b) ∧ (¬a ∨ ¬b)` (same/opposite polarity) witnesses `2`-XOR soundness. -/
theorem xorVarsSound_of_binPair {F : CNF Nat} {a b : Nat}
    (h1 : F.EntailsClause (cnfClause [a, b]))
    (h2 : F.EntailsClause (cnfClause [litNeg a, litNeg b])) :
    XorVarsSound F [litVar a, litVar b] (litSign a == litSign b) := by
  intro α hα
  have s1 := (clause_sat_cnfClause_iff α [a, b]).mp (CNF.entails_clause_def.mp h1 α hα)
  have s2 := (clause_sat_cnfClause_iff α [litNeg a, litNeg b]).mp
    (CNF.entails_clause_def.mp h2 α hα)
  simp only [xorEvalVars_cons, xorEvalVars_nil, Bool.bne_false]
  rcases s1 with ⟨x, hx, hsx⟩
  rcases s2 with ⟨y, hy, hsy⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with hxa | hxb <;> rcases hy with hya | hyb
  · rw [hxa] at hsx; rw [hya, litVar_litNeg, litSign_litNeg] at hsy
    cases hs : litSign a <;> simp_all
  · rw [hxa] at hsx; rw [hyb, litVar_litNeg, litSign_litNeg] at hsy
    cases hsa : litSign a <;> cases hsb : litSign b <;> simp_all
  · rw [hxb] at hsx; rw [hya, litVar_litNeg, litSign_litNeg] at hsy
    cases hsa : litSign a <;> cases hsb : litSign b <;> simp_all
  · rw [hxb] at hsx; rw [hyb, litVar_litNeg, litSign_litNeg] at hsy
    cases hs : litSign b <;> simp_all

theorem parityMask_getLsbD_iff {k : Nat} {p : Bool} (hk3 : 3 ≤ k) (hk5 : k ≤ 5)
    {m : Nat} (hm : m < 2 ^ k) :
    (parityMask k p).getLsbD m = true ↔ maskParity k m = p := by
  have hk : k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases hk with rfl | rfl | rfl <;> cases p
  · revert m; decide
  · revert m; decide
  · revert m; decide
  · revert m; decide
  · revert m; decide
  · revert m; decide

theorem eval_alpha_mask_match {α : Nat → Bool} {vs : List Nat} :
    ∃ m < 2 ^ vs.length, ∀ i (hi : i < vs.length),
      α vs[i] = ((m >>> i) % 2 == 1) := by
  induction vs with
  | nil => exact ⟨0, by decide, fun i hi => by simp at hi⟩
  | cons v vs ih =>
    obtain ⟨m, hm, hmatch⟩ := ih
    let bit := if α v then 1 else 0
    have hbit_le : bit ≤ 1 := by dsimp [bit]; cases α v <;> decide
    refine ⟨bit + 2 * m, by simp only [List.length_cons, Nat.pow_succ]; omega, fun i hi => ?_⟩
    cases i with
    | zero =>
      cases hv : α v <;> simp [bit, hv]
    | succ i =>
      have hi' : i < vs.length := Nat.lt_of_succ_lt_succ hi
      have hsh : (bit + 2 * m) >>> (i + 1) = m >>> i := by
        simp only [Nat.shiftRight_eq_div_pow, Nat.pow_succ', ← Nat.div_div_eq_div_mul]
        have hdiv2 : (bit + 2 * m) / 2 = m := by omega
        rw [hdiv2]
      simpa [hsh] using hmatch i hi'

theorem xorEvalVars_eq_maskParity_of_match {α : Nat → Bool} {vs : List Nat} {m : Nat}
    (hm : ∀ i (hi : i < vs.length), α vs[i] = ((m >>> i) % 2 == 1)) :
    xorEvalVars α vs = maskParity vs.length m := by
  refine Classical.byContradiction fun hne => ?_
  have hns : ¬(cnfClause (xorMaskClause vs m)).Sat α := by
    rw [clause_sat_cnfClause_iff]
    rintro ⟨l, hl, hsl⟩
    simp only [xorMaskClause, List.mem_map, List.mem_range] at hl
    rcases hl with ⟨i, hi, rfl⟩
    rw [List.getElem?_eq_getElem hi, Option.getD_some, litVar_mkLit, litSign_mkLit, hm i hi] at hsl
    cases hb : ((m >>> i) % 2 == 1) <;> simp_all
  exact hne (xorEvalVars_eq_maskParity_of_clause_unsat hns)

/-- A `u32` seen-bitmask matching `parityMask vs.length p` across `k ∈ 3..5` entails
`XorVarsSound F vs (!p)`. -/
theorem xorVarsSound_of_parityMask {F : CNF Nat} {vs : List Nat} {seen : BitVec 32}
    {p : Bool} (hk3 : 3 ≤ vs.length) (hk5 : vs.length ≤ 5)
    (hpm : (seen &&& parityMask vs.length p) = parityMask vs.length p)
    (hent : ∀ m < 2 ^ vs.length, seen.getLsbD m = true →
      F.EntailsClause (cnfClause (xorMaskClause vs m))) :
    XorVarsSound F vs (!p) := by
  intro α hα
  obtain ⟨m, hm, hmatch⟩ := eval_alpha_mask_match (α := α) (vs := vs)
  rw [xorEvalVars_eq_maskParity_of_match hmatch]
  refine Classical.byContradiction fun hne => ?_
  have hmp : maskParity vs.length m = p := by
    cases p <;> cases h : maskParity vs.length m <;> simp_all
  have hbit_pm : (parityMask vs.length p).getLsbD m = true :=
    (parityMask_getLsbD_iff hk3 hk5 hm).mpr hmp
  have hbit_seen : seen.getLsbD m = true := by
    have h0 := congrArg (fun bv : BitVec 32 => bv.getLsbD m) hpm
    simp only [BitVec.getLsbD_and, hbit_pm, Bool.and_true] at h0
    exact h0
  have hsat := CNF.entails_clause_def.mp (hent m hm hbit_seen) α hα
  rw [clause_sat_cnfClause_iff] at hsat
  rcases hsat with ⟨l, hl, hsl⟩
  simp only [xorMaskClause, List.mem_map, List.mem_range] at hl
  rcases hl with ⟨i, hi, rfl⟩
  rw [List.getElem?_eq_getElem hi, Option.getD_some, litVar_mkLit, litSign_mkLit,
    hmatch i hi] at hsl
  cases hb : ((m >>> i) % 2 == 1) <;> simp_all

/-! ## 3. Packed `u64`-word row semantics (stored as `u32` pairs in `scratch_buf`) -/

theorem rowU64_lo_hi {lo hi : BitVec 32} {i : Nat} :
    (lo.setWidth 64 ||| (hi.setWidth 64 <<< 32)).getLsbD i =
      if i < 32 then lo.getLsbD i else hi.getLsbD (i - 32) := by
  by_cases h64 : i < 64
  · rw [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth]
    by_cases h32 : i < 32
    · simp [h64, h32]
    · have h32le : 32 ≤ i := by omega
      have him32 : i - 32 < 64 := by omega
      simp [h64, h32, h32le, him32]
  · have hge64 : 64 ≤ i := by omega
    have h1 : (lo.setWidth 64 ||| (hi.setWidth 64 <<< 32)).getLsbD i = false :=
      BitVec.getLsbD_of_ge _ _ hge64
    by_cases h32 : i < 32
    · omega
    · have h2 : hi.getLsbD (i - 32) = false := BitVec.getLsbD_of_ge _ _ (by omega)
      simp [h1, h2, h32]

theorem rowBit_xor_eq {scr1 scr2 scr' : List (BitVec 32)} {b1 b2 b' ncols words64 c : Nat}
    (hw : words64 = (ncols + 64) / 64) (hc : c ≤ ncols)
    (hxor : ∀ w < words64, rowU64 scr' b' w = rowU64 scr1 b1 w ^^^ rowU64 scr2 b2 w) :
    rowBit scr' b' c = (rowBit scr1 b1 c != rowBit scr2 b2 c) := by
  have hw_lt : c / 64 < words64 := by rw [hw]; omega
  unfold rowBit
  rw [hxor (c / 64) hw_lt, BitVec.getLsbD_xor]

/-- Row-XOR preservation: `row[i] ^= row[j]` preserves `XorPackedRowSound F`. -/
theorem xorPackedRowSound_xor {F : CNF Nat} {c2v scr1 scr2 scr' : List (BitVec 32)}
    {b1 b2 b' ncols words64 : Nat}
    (hw : words64 = (ncols + 64) / 64)
    (h1 : XorPackedRowSound F c2v scr1 b1 ncols)
    (h2 : XorPackedRowSound F c2v scr2 b2 ncols)
    (hxor : ∀ w < words64, rowU64 scr' b' w = rowU64 scr1 b1 w ^^^ rowU64 scr2 b2 w) :
    XorPackedRowSound F c2v scr' b' ncols := by
  intro α hα
  have h1α := h1 α hα
  have h2α := h2 α hα
  suffices hsum : ∀ k ≤ ncols,
      ((List.range k).foldl
        (fun acc c => if rowBit scr' b' c then acc != α (c2v[c]?.getD 0#32).toNat else acc)
        false) =
      (((List.range k).foldl
        (fun acc c => if rowBit scr1 b1 c then acc != α (c2v[c]?.getD 0#32).toNat else acc)
        false) !=
       ((List.range k).foldl
        (fun acc c => if rowBit scr2 b2 c then acc != α (c2v[c]?.getD 0#32).toNat else acc)
        false)) by
    unfold xorEvalPacked at h1α h2α ⊢
    rw [hsum ncols (Nat.le_refl _), rowBit_xor_eq hw (Nat.le_refl _) hxor]
    cases hs1 : (List.range ncols).foldl
      (fun acc c => if rowBit scr1 b1 c then acc != α (c2v[c]?.getD 0#32).toNat else acc) false <;>
      cases hr1 : rowBit scr1 b1 ncols <;>
      cases hs2 : (List.range ncols).foldl
        (fun acc c => if rowBit scr2 b2 c then acc != α (c2v[c]?.getD 0#32).toNat else acc)
        false <;>
      cases hr2 : rowBit scr2 b2 ncols <;> simp_all
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldl_append, List.foldl_cons, List.foldl_nil,
      ih (Nat.le_of_lt hk), rowBit_xor_eq hw (Nat.le_of_lt hk) hxor]
    cases rowBit scr1 b1 k <;> cases rowBit scr2 b2 k <;>
      cases α (c2v[k]?.getD 0#32).toNat <;> simp <;>
      cases (List.range k).foldl
        (fun acc c => if rowBit scr1 b1 c then acc != α (c2v[c]?.getD 0#32).toNat else acc)
        false <;>
      cases (List.range k).foldl
        (fun acc c => if rowBit scr2 b2 c then acc != α (c2v[c]?.getD 0#32).toNat else acc)
        false <;>
      rfl

/-- Weight-0 row with RHS = `true` (`0 = 1`) yields `F.Unsat`. -/
theorem unsat_of_zero_packed_row {F : CNF Nat} {c2v scr : List (BitVec 32)}
    {rbase ncols : Nat}
    (hzero : ∀ c < ncols, rowBit scr rbase c = false)
    (hrhs : rowBit scr rbase ncols = true)
    (hsound : XorPackedRowSound F c2v scr rbase ncols) : F.Unsat := by
  refine CNF.unsat_iff_entails_clause_empty.mpr (CNF.entails_clause_def.mpr fun α hα => ?_)
  have h1 := hsound α hα
  have hlhs : (List.range ncols).foldl
      (fun acc c => if rowBit scr rbase c then acc != α (c2v[c]?.getD 0#32).toNat else acc)
      false = false := by
    suffices ∀ k ≤ ncols, (List.range k).foldl
        (fun acc c => if rowBit scr rbase c then acc != α (c2v[c]?.getD 0#32).toNat else acc)
        false = false from this ncols (Nat.le_refl _)
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih (Nat.le_of_lt hk), hzero k hk]
      rfl
  unfold xorEvalPacked at h1
  rw [hlhs, hrhs] at h1
  exact Bool.noConfusion h1

private theorem filter_lt_zero_eq_nil (cols : List Nat) :
    cols.filter (fun x => decide (x < 0)) = [] :=
  List.filter_eq_nil_iff.mpr (by simp)

private theorem filter_lt_succ_perm_mem {cols : List Nat} {k : Nat}
    (hn : cols.Nodup) (hk : k ∈ cols) :
    (cols.filter (· < k + 1)).Perm (k :: cols.filter (· < k)) := by
  induction cols with
  | nil => simp at hk
  | cons x xs ih =>
    have hnx := List.nodup_cons.mp hn
    simp only [List.filter_cons, List.mem_cons] at hk ⊢
    rcases hk with rfl | hmem
    · have hk_not : ¬k ∈ xs := hnx.1
      have hfilt_eq :
          xs.filter (fun y => decide (y < k + 1)) = xs.filter (fun y => decide (y < k)) := by
        refine List.filter_congr fun y hy => ?_
        have hyk : y ≠ k := fun h => hk_not (h ▸ hy)
        by_cases hy1 : y < k + 1 <;> by_cases hy2 : y < k <;> simp_all <;> omega
      simp [hfilt_eq]
    · have hxk : x ≠ k := fun h => hnx.1 (h ▸ hmem)
      have ih' := ih hnx.2 hmem
      by_cases hlt : x < k
      · have hlt1 : x < k + 1 := Nat.lt_succ_of_lt hlt
        simp only [hlt1, hlt, decide_true, ↓reduceIte]
        exact (ih'.cons x).trans (List.Perm.swap k x _)
      · have hn1 : ¬ (x < k + 1) := by omega
        simp only [hn1, hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact ih'

private theorem filter_lt_succ_eq_of_nmem {cols : List Nat} {k : Nat} (hk : k ∉ cols) :
    cols.filter (· < k + 1) = cols.filter (· < k) := by
  refine List.filter_congr fun x hx => ?_
  have hxk : x ≠ k := fun h => hk (h ▸ hx)
  by_cases h1 : x < k + 1 <;> by_cases h2 : x < k <;> simp_all <;> omega

/-- Reading a packed row via set column bits yields `XorVarsSound` over `c2v`. -/
theorem xorVarsSound_of_packedRow {F : CNF Nat} {c2v scr : List (BitVec 32)}
    {rbase ncols : Nat} {cols : List Nat}
    (hcol_lt : ∀ c ∈ cols, c < ncols)
    (hnodup : cols.Nodup)
    (hbits : ∀ c < ncols, rowBit scr rbase c = true ↔ c ∈ cols)
    (hsound : XorPackedRowSound F c2v scr rbase ncols) :
    XorVarsSound F (cols.map fun c => (c2v[c]?.getD 0#32).toNat) (rowBit scr rbase ncols) := by
  intro α hα
  have hp := hsound α hα
  unfold xorEvalPacked at hp
  have hrhs : (List.range ncols).foldl
      (fun acc c => if rowBit scr rbase c then acc != α (c2v[c]?.getD 0#32).toNat else acc)
      false = rowBit scr rbase ncols := by
    cases h1 : rowBit scr rbase ncols <;>
      cases h2 : (List.range ncols).foldl
        (fun acc c => if rowBit scr rbase c then acc != α (c2v[c]?.getD 0#32).toNat else acc)
        false <;> simp_all
  clear hp
  rw [← hrhs]
  suffices hstep : ∀ (k : Nat) (hk : k ≤ ncols),
      (List.range k).foldl
        (fun acc c => if rowBit scr rbase c then acc != α (c2v[c]?.getD 0#32).toNat else acc)
        false =
      xorEvalVars α ((cols.filter (· < k)).map fun c => (c2v[c]?.getD 0#32).toNat) by
    have hfilt : cols.filter (· < ncols) = cols := List.filter_eq_self.mpr fun c hc => by
      simpa using hcol_lt c hc
    simpa [hfilt] using (hstep ncols (Nat.le_refl _)).symm
  intro k hk
  induction k with
  | zero => simp only [List.range_zero, List.foldl_nil]; rw [filter_lt_zero_eq_nil]; rfl
  | succ k ih =>
    have hk_lt : k < ncols := hk
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ih (Nat.le_of_lt hk_lt)]
    by_cases hrb : rowBit scr rbase k = true
    · have hk_mem : k ∈ cols := (hbits k hk_lt).mp hrb
      have hperm := filter_lt_succ_perm_mem hnodup hk_mem
      have hxperm := xorEvalVars_perm (α := α)
        (hperm.map fun c => (c2v[c]?.getD 0#32).toNat)
      rw [hrb, ite_eq_left rfl, hxperm, List.map_cons, xorEvalVars_cons]
      cases α (c2v[k]?.getD 0#32).toNat <;>
        cases xorEvalVars α ((cols.filter (· < k)).map fun c => (c2v[c]?.getD 0#32).toNat) <;>
        rfl
    · have hk_nmem : k ∉ cols := fun h => hrb ((hbits k hk_lt).mpr h)
      have hfilt_eq := filter_lt_succ_eq_of_nmem hk_nmem
      have hrb_f : rowBit scr rbase k = false := by cases h : rowBit scr rbase k <;> simp_all
      rw [hrb_f, ite_eq_right Bool.false_ne_true, hfilt_eq]

/-- Low bit properties for `c0_ctz64` (`w.reverse.clz = w.ctz`) and Kernighan bit-stripping
`w &&& (w - 1#64)`. -/
theorem ctz64_lt (w : BitVec 64) (hne : w ≠ 0#64) : w.reverse.clz.toNat < 64 := by
  have hlt := (BitVec.ctz_lt_iff_ne_zero (x := w)).mpr hne
  rw [BitVec.ctz_eq_reverse_clz] at hlt
  simpa [BitVec.lt_def] using hlt

theorem ctz64_getLsbD_true (w : BitVec 64) (hne : w ≠ 0#64) :
    w.getLsbD w.reverse.clz.toNat = true := by
  have ht := BitVec.getLsbD_true_ctz_of_ne_zero (x := w) hne
  rwa [BitVec.ctz_eq_reverse_clz] at ht

theorem ctz64_getLsbD_false_lt (w : BitVec 64) {k : Nat} (hk : k < w.reverse.clz.toNat) :
    w.getLsbD k = false := by
  rw [← BitVec.ctz_eq_reverse_clz] at hk
  exact BitVec.getLsbD_false_of_lt_ctz hk

private theorem mod_pow2_eq_zero_of_getLsbD_false (w : BitVec 64) {k : Nat} (hk64 : k ≤ 64)
    (hk : ∀ j < k, w.getLsbD j = false) : w.toNat % 2 ^ k = 0 := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    have h0 := ih (Nat.le_of_lt hk64) fun j hj => hk j (Nat.lt_succ_of_lt hj)
    have hbit := hk k (Nat.lt_succ_self k)
    rw [BitVec.getLsbD_eq_getElem (by omega), BitVec.getElem_eq_testBit_toNat,
      Nat.testBit_eq_decide_div_mod_eq] at hbit
    have hq : w.toNat / 2 ^ k % 2 = 0 := by
      cases hrem : w.toNat / 2 ^ k % 2 <;> simp_all <;> omega
    have hdiv : w.toNat = (w.toNat / 2 ^ k) * 2 ^ k + w.toNat % 2 ^ k := (Nat.div_add_mod' _ _).symm
    have h2 : w.toNat / 2 ^ k = (w.toNat / 2 ^ k / 2) * 2 := by
      have := Nat.div_add_mod' (w.toNat / 2 ^ k) 2
      omega
    rw [h0, Nat.add_zero, h2] at hdiv
    rw [hdiv, Nat.pow_succ', Nat.mul_assoc, Nat.mul_mod_left]

theorem kernighan_clear_lsb (w : BitVec 64) (hne : w ≠ 0#64) :
    (w &&& (w - 1#64)) = w ^^^ (1#64 <<< w.reverse.clz.toNat) := by
  let b := w.reverse.clz.toNat
  change (w &&& (w - 1#64)) = w ^^^ (1#64 <<< b)
  have hlt : b < 64 := ctz64_lt w hne
  have hb : w.getLsbD b = true := ctz64_getLsbD_true w hne
  have hlt_false : ∀ j < b, w.getLsbD j = false := fun _ hj => ctz64_getLsbD_false_lt w hj
  have hmod : w.toNat % 2 ^ b = 0 :=
    mod_pow2_eq_zero_of_getLsbD_false w (Nat.le_of_lt hlt) hlt_false
  have hpos_b : 0 < 2 ^ b := Nat.pow_pos (by decide)
  have hbit_b : (w.toNat / 2 ^ b) % 2 = 1 := by
    rw [BitVec.getLsbD_eq_getElem hlt, BitVec.getElem_eq_testBit_toNat,
      Nat.testBit_eq_decide_div_mod_eq] at hb
    simpa using hb
  let q := w.toNat / 2 ^ (b + 1)
  have hw_eq : w.toNat = 2 ^ b + 2 ^ (b + 1) * q := by
    have h1 := (Nat.div_add_mod' w.toNat (2 ^ b)).symm
    have h2 := (Nat.div_add_mod' (w.toNat / 2 ^ b) 2).symm
    have hq_eq : w.toNat / 2 ^ b / 2 = q := by
      dsimp [q]; rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    rw [hmod, Nat.add_zero] at h1
    rw [hbit_b, hq_eq] at h2
    rw [h2] at h1
    rw [h1, Nat.pow_succ, Nat.add_mul, Nat.one_mul, Nat.add_comm]
    simp only [Nat.mul_assoc, Nat.mul_comm]
    rw [Nat.mul_left_comm]
  have hw_ge1 : 1 ≤ w.toNat := by omega
  have hwsub : (w - 1#64).toNat = (2 ^ b - 1) + 2 ^ (b + 1) * q := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by simpa using hw_ge1)), BitVec.toNat_ofNat]
    change w.toNat - 1 = (2 ^ b - 1) + 2 ^ (b + 1) * q
    omega
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_one]
  by_cases hib : i < b
  · have hwf : w.getLsbD i = false := hlt_false i hib
    have hne_bi : ¬ (b ≤ i) := by omega
    simp [hwf, hne_bi]
  · by_cases heq : i = b
    · subst heq
      have hm1_b : (w - 1#64).getLsbD b = false := by
        rw [BitVec.getLsbD_eq_getElem hlt, BitVec.getElem_eq_testBit_toNat,
          Nat.testBit_eq_decide_div_mod_eq, hwsub, decide_eq_false_iff_not]
        have hdiv : ((2 ^ b - 1) + 2 ^ (b + 1) * q) / 2 ^ b = 2 * q := by
          rw [Nat.pow_succ, show 2 ^ b * 2 * q = (2 * q) * 2 ^ b by
              rw [Nat.mul_comm (2 ^ b) 2, Nat.mul_assoc, Nat.mul_comm (2 ^ b) q, ← Nat.mul_assoc],
            Nat.add_mul_div_right _ _ hpos_b, Nat.div_eq_of_lt (by omega), Nat.zero_add]
        rw [hdiv]; omega
      rw [hb, hm1_b]
      simp [hlt]
    · let t := i - (b + 1)
      have hi_eq : i = b + 1 + t := by omega
      have hpos_b1 : 0 < 2 ^ (b + 1) := Nat.pow_pos (by decide)
      have hm1_eq : (w - 1#64).getLsbD i = w.getLsbD i := by
        rw [BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD_eq_getElem hi,
          BitVec.getElem_eq_testBit_toNat, BitVec.getElem_eq_testBit_toNat,
          Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, hwsub, hw_eq]
        rw [hi_eq, Nat.pow_add (2 : Nat) (b + 1) t, ← Nat.div_div_eq_div_mul,
          ← Nat.div_div_eq_div_mul]
        have h1 : ((2 ^ b - 1) + 2 ^ (b + 1) * q) / 2 ^ (b + 1) = q := by
          rw [Nat.mul_comm (2 ^ (b + 1)) q, Nat.add_mul_div_right _ _ hpos_b1,
            Nat.div_eq_of_lt (by rw [Nat.pow_succ]; omega), Nat.zero_add]
        have h2 : (2 ^ b + 2 ^ (b + 1) * q) / 2 ^ (b + 1) = q := by
          rw [Nat.mul_comm (2 ^ (b + 1)) q, Nat.add_mul_div_right _ _ hpos_b1,
            Nat.div_eq_of_lt (by rw [Nat.pow_succ]; omega), Nat.zero_add]
        rw [h1, h2]
      have hzero : ¬ (i - b = 0) := by omega
      simp [hm1_eq, hzero]

end LeanQbe.T.Examples.KissatBeyond.Ref
