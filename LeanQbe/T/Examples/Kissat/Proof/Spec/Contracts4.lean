/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Logic.C0Step
public import Kraken.Mem
public import Kraken.Separation

/-!
# Kissat `D-Full` BVA, Forward-Subsumption & Heap Specs (`Proof.Spec.Contracts4`)

1. `FullBvaFwdTactics` bitvector helpers and `FullBvaFwdHelpers` (`bvaExtendFormula`,
   `fullDenseInv_add_fresh_var`).
2. `FullBvaHeapHelpers` (`bvaExtendGen`, `extUnsatSound_bvaExtendGen`, `bv32_viv_roundtrip`).
3. Canonical 3-hop BVA & binary-heap specs (`fullBvaHop*Spec`, `fullFheap*Spec`,
   `fullBvaCommitSpec`, `fullBvaTryLitHeapSpec`, `fullFactorHeapSpec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Spec

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

namespace FullBvaFwdTactics

private theorem nat_or1_of_even {n : Nat} (he : n % 2 = 0) : n ||| 1 = n + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => simp [Nat.testBit_zero, he]; omega
  | succ j =>
    rw [Nat.testBit_or, show Nat.testBit 1 (j + 1) = false by rw [Nat.testBit_succ]; simp,
      Bool.or_false, Nat.testBit_succ, Nat.testBit_succ, show (n + 1) / 2 = n / 2 by omega]

theorem bv32_or1_of_even {x : BitVec 32} (he : x.toNat % 2 = 0) :
    (x ||| 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_or, show (1#32).toNat = 1 from rfl]; exact nat_or1_of_even he

theorem bv64_or1_of_even {x : BitVec 64} (he : x.toNat % 2 = 0) :
    (x ||| 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_or, show (1#64).toNat = 1 from rfl]; exact nat_or1_of_even he

theorem bv32_and_mask_eq {x : BitVec 32} (hlt : x.toNat < 2 ^ 31) :
    (x &&& 0x7FFFFFFF#32) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]

theorem bv32_and_bin_eq_zero_of_lt {x : BitVec 32} (hlt : x.toNat < 0x80000000) :
    (x &&& 0x80000000#32) = 0#32 := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_zero]
  by_cases h31 : i = 31
  · subst h31
    have hf : x[31] = false := by
      rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
      simp [show x.toNat / 2 ^ 31 = 0 by omega]
    simp [hf]
  · have hmask : (0x80000000#32 : BitVec 32)[i] = false := by
      rw [BitVec.getElem_eq_testBit_toNat]
      change Nat.testBit (2 ^ 31) i = false
      rw [Nat.testBit_two_pow]; exact decide_eq_false (Ne.symm h31)
    simp [hmask]

private theorem bit31_bin : (0x80000000#32 : BitVec 32)[31] = true := by decide
private theorem bit19_garb : (0x00080000#32 : BitVec 32)[19] = true := by decide
private theorem bit23_shrk : (0x00800000#32 : BitVec 32)[23] = true := by decide

theorem bv32_and_bin_ne_zero_iff (x : BitVec 32) :
    (x &&& 0x80000000#32) ≠ 0#32 ↔ 0x80000000 ≤ x.toNat := by
  constructor
  · intro hne
    exact Classical.byContradiction fun hlt =>
      hne (bv32_and_bin_eq_zero_of_lt (Nat.lt_of_not_ge hlt))
  · intro hge heq
    have h31 := congrArg (·[31]) heq
    have hx31 : x[31] = true := by
      rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
      have hlt : x.toNat < 2 ^ 32 := x.isLt
      simp [show x.toNat / 2 ^ 31 = 1 by omega]
    simp [BitVec.getElem_and, hx31, bit31_bin] at h31

theorem bv32_xor1_toNat (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by
  rw [BitVec.toNat_xor]; rfl

theorem bv8_slt0_iff_eq_ff {b : BitVec 8}
    (hd : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8) :
    (b.signExtend 32).slt 0#32 = true ↔ b = 0xFF#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

theorem bv8_sge0_iff_ne_ff {b : BitVec 8}
    (hd : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8) :
    (0#32).sle (b.signExtend 32) = true ↔ b ≠ 0xFF#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

end FullBvaFwdTactics

open FullBvaFwdTactics

namespace FullBvaFwdHelpers

/-- Hyper-unary resolution on binary watches: `F ⊨ [l, ot]` and `F ⊨ [l, ot ^ 1]` entail `[l]`. -/
theorem entails_unit_of_bin_pair {f : CNF Nat} {l ot : Nat}
    (h1 : f.EntailsClause (cnfClause [l, ot]))
    (h2 : f.EntailsClause (cnfClause [l, ot ^^^ 1])) :
    f.EntailsClause (cnfClause [l]) := by
  rw [CNF.entails_clause_def]
  intro α hα
  have s1 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp h1 α hα)
  have s2 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp h2 α hα)
  rw [← clauseEvalVal_iff]
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at s1 s2 ⊢
  have hneg : evalLitVal α (ot ^^^ 1) = !(evalLitVal α ot) := by
    simpa [litNeg] using evalLitVal_litNeg α ot
  rw [hneg] at s2
  cases hl : evalLitVal α l <;> cases hot : evalLitVal α ot <;> simp_all

/-- Binary self-subsuming strengthening: `l ∈ C`, `drop ≠ l`, `F ⊨ C`, `F ⊨ [l, drop ^ 1]`
entail `C.filter (· ≠ drop)`. -/
theorem entails_strengthen_of_bin {f : CNF Nat} {C : List Nat} {l drop : Nat}
    (hl : l ∈ C) (hne : drop ≠ l)
    (hC : f.EntailsClause (cnfClause C))
    (hbin : f.EntailsClause (cnfClause [l, drop ^^^ 1])) :
    f.EntailsClause (cnfClause (C.filter (· != drop))) := by
  rw [CNF.entails_clause_def]
  intro α hα
  rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]
  by_cases hd : evalLitVal α drop = true
  · have hb := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hbin α hα)
    simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at hb
    have hneg : evalLitVal α (drop ^^^ 1) = false := by
      have h := evalLitVal_litNeg α drop
      simp only [litNeg] at h; rw [h, hd]; rfl
    rw [hneg, Bool.or_false] at hb
    exact ⟨l, List.mem_filter.mpr ⟨hl, by simp [Ne.symm hne]⟩, hb⟩
  · have hcs := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hC α hα)
    simp only [clauseEvalVal, List.any_eq_true] at hcs
    obtain ⟨x, hx, hxt⟩ := hcs
    have hxd : x ≠ drop := fun he => by subst he; exact hd hxt
    exact ⟨x, List.mem_filter.mpr ⟨hx, by simp [hxd]⟩, hxt⟩

/-- Clause self-subsuming strengthening: given `F ⊨ C`, `F ⊨ D`, variable-distinct `D`
(`(D.map (· / 2)).Nodup`), `cand ^ 1 ∈ D`, and every `dl ∈ D` either in `C`, falsified at level 0
(`F ⊨ [dl ^ 1]`), or equal to `cand ^ 1`, we have `F ⊨ C.filter (· ≠ cand)`. -/
theorem entails_strengthen_of_clause {f : CNF Nat} {C D : List Nat} {cand : Nat}
    (hC : f.EntailsClause (cnfClause C))
    (hD : f.EntailsClause (cnfClause D))
    (hnd : (D.map (· / 2)).Nodup)
    (hneg_mem : (cand ^^^ 1) ∈ D)
    (hsub : ∀ dl ∈ D, dl ∈ C ∨ f.EntailsClause (cnfClause [dl ^^^ 1]) ∨ dl = cand ^^^ 1) :
    f.EntailsClause (cnfClause (C.filter (· != cand))) := by
  have hcand_not_D : cand ∉ D := by
    intro hcm
    obtain ⟨i, hi, heqi⟩ := List.mem_iff_getElem.mp hcm
    obtain ⟨j, hj, heqj⟩ := List.mem_iff_getElem.mp hneg_mem
    have hij : i = j := by
      have hm := List.pairwise_iff_getElem.mp hnd
      by_cases hlt : i < j
      · have hne := hm i j (by simp [hi]) (by simp [hj]) hlt
        simp only [List.getElem_map, heqi, heqj, fullInv_var_xor1] at hne
        exact absurd rfl hne
      · by_cases hgt : j < i
        · have hne := hm j i (by simp [hj]) (by simp [hi]) hgt
          simp only [List.getElem_map, heqi, heqj, fullInv_var_xor1] at hne
          exact absurd rfl hne
        · omega
    subst hij
    rw [heqi] at heqj
    exact absurd heqj.symm (litNeg_ne_self cand)
  rw [CNF.entails_clause_def]
  intro α hα
  rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]
  by_cases hc : evalLitVal α cand = true
  · have hDs := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hD α hα)
    simp only [clauseEvalVal, List.any_eq_true] at hDs
    obtain ⟨dl, hdlD, hdlt⟩ := hDs
    rcases hsub dl hdlD with hdlC | hfals | hdlneg
    · have hne : dl ≠ cand := fun h => hcand_not_D (h ▸ hdlD)
      exact ⟨dl, List.mem_filter.mpr ⟨hdlC, by simp [hne]⟩, hdlt⟩
    · have hns := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hfals α hα)
      simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at hns
      have hneg := evalLitVal_litNeg α dl
      simp only [litNeg] at hneg
      rw [hneg, hdlt] at hns; cases hns
    · subst hdlneg
      have hneg := evalLitVal_litNeg α cand
      simp only [litNeg] at hneg
      rw [hneg, hc] at hdlt; cases hdlt
  · have hCs := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hC α hα)
    simp only [clauseEvalVal, List.any_eq_true] at hCs
    obtain ⟨x, hx, hxt⟩ := hCs
    have hne : x ≠ cand := fun h => by subst h; exact hc hxt
    exact ⟨x, List.mem_filter.mpr ⟨hx, by simp [hne]⟩, hxt⟩

/-- Fresh-variable BVA binary extension formula: keeps `F_cur` verbatim and adjoins
`[2 * fv, f]` (`f ∈ L`) and `[2 * fv + 1, q]` (`q ∈ Q`). -/
@[expose]
def bvaExtendFormula (fv : Nat) (L Q : List Nat) (F_cur : List (List Nat)) : List (List Nat) :=
  L.map (fun f => [2 * fv, f]) ++ Q.map (fun q => [2 * fv + 1, q]) ++ F_cur

theorem bvaExtendFormula_entails_orig (fv : Nat) (L Q : List Nat) (F_cur : List (List Nat)) :
    (cnfOfClauses (bvaExtendFormula fv L Q F_cur)).Entails (cnfOfClauses F_cur) := by
  rw [CNF.entails_def]
  intro α hα
  rw [cnf_sat_cnfOfClauses_iff] at hα ⊢
  intro cl hcl
  exact hα cl (List.mem_append_right _ hcl)

theorem bvaExtendFormula_entails_pos {fv : Nat} {L Q : List Nat} {F_cur : List (List Nat)}
    {f : Nat} (hf : f ∈ L) :
    (cnfOfClauses (bvaExtendFormula fv L Q F_cur)).EntailsClause (cnfClause [2 * fv, f]) :=
  entails_mem_cnfOfClauses
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨f, hf, rfl⟩)))

theorem bvaExtendFormula_entails_neg {fv : Nat} {L Q : List Nat} {F_cur : List (List Nat)}
    {q : Nat} (hq : q ∈ Q) :
    (cnfOfClauses (bvaExtendFormula fv L Q F_cur)).EntailsClause (cnfClause [2 * fv + 1, q]) :=
  entails_mem_cnfOfClauses
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨q, hq, rfl⟩)))

/-- Fresh-variable BVA UNSAT soundness for `bvaExtendFormula`: any model `α` of `F_cur` extends
to a model `substUpdate α fv b` of `bvaExtendFormula fv L Q F_cur` by setting `fv := true` when
all `q ∈ Q` are true under `α`, and `fv := false` otherwise (in which case all `f ∈ L` are true
via `F_cur ⊨ [f, q0]`). -/
theorem extUnsatSound_bvaExtendFormula {F0 : CNF Nat} {mv_cur : Nat} {F_cur : List (List Nat)}
    {L Q : List Nat} (hs : ExtUnsatSound F0 mv_cur F_cur)
    (hL : ∀ f ∈ L, f < 2 * mv_cur) (hQ : ∀ q ∈ Q, q < 2 * mv_cur)
    (hprod : ∀ f ∈ L, ∀ q ∈ Q, (cnfOfClauses F_cur).EntailsClause (cnfClause [f, q])) :
    ExtUnsatSound F0 (mv_cur + 1) (bvaExtendFormula mv_cur L Q F_cur) := by
  refine ⟨fun c hc l hl => ?_, fun hu => hs.2 ?_⟩
  · unfold bvaExtendFormula at hc
    simp only [List.mem_append, List.mem_map] at hc
    rcases hc with (⟨f, hf, rfl⟩ | ⟨q, hq, rfl⟩) | hmem
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · simp [litVar]
      · have := hL l hf; simp [litVar]; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · simp [litVar]; omega
      · have := hQ l hq; simp [litVar]; omega
    · exact Nat.lt_succ_of_lt (hs.1 c hmem l hl)
  · rw [CNF.unsat_iff_not_sat] at hu ⊢
    intro α hα
    let b : Bool := Q.all (evalLitVal α)
    let α' : Nat → Bool := substUpdate α mv_cur b
    have hfresh_lit : ∀ x < 2 * mv_cur, evalLitVal α' x = evalLitVal α x := fun x hx => by
      have hne : litVar x ≠ mv_cur := by simp [litVar]; omega
      simp [evalLitVal, α', substUpdate_ne α b hne]
    apply hu α'
    rw [cnf_sat_cnfOfClauses_iff]
    intro c hc
    unfold bvaExtendFormula at hc
    simp only [List.mem_append, List.mem_map] at hc
    rcases hc with (⟨f, hf, rfl⟩ | ⟨q, hq, rfl⟩) | hmem
    · rw [← clauseEvalVal_iff, clauseEvalVal]
      simp only [List.any_cons, List.any_nil, Bool.or_false, hfresh_lit f (hL f hf)]
      have hpos : evalLitVal α' (2 * mv_cur) = b := by
        simp [evalLitVal, litVar, litSign, α']
      rw [hpos]
      cases hb : b
      · simp only [Bool.false_or]
        have hex : ∃ q0 ∈ Q, evalLitVal α q0 = false := by
          have := List.all_eq_false.mp hb
          obtain ⟨q0, hq0, hq0f⟩ := this; exact ⟨q0, hq0, Bool.eq_false_iff.mpr hq0f⟩
        obtain ⟨q0, hq0, hq0f⟩ := hex
        have hfq := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp (hprod f hf q0 hq0) α hα)
        simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false, hq0f,
          Bool.or_false] at hfq
        exact hfq
      · simp
    · rw [← clauseEvalVal_iff, clauseEvalVal]
      simp only [List.any_cons, List.any_nil, Bool.or_false, hfresh_lit q (hQ q hq)]
      have hneg : evalLitVal α' (2 * mv_cur + 1) = !b := by
        have hv : litVar (2 * mv_cur + 1) = mv_cur := by simp [litVar]; omega
        have hs : litSign (2 * mv_cur + 1) = true := by simp [litSign]
        simp [evalLitVal, hv, hs, α']
      rw [hneg]
      cases hb : b
      · simp
      · simp only [Bool.not_true, Bool.false_or]
        exact List.all_eq_true.mp hb q hq
    · have hcs := (cnf_sat_cnfOfClauses_iff α F_cur).mp hα c hmem
      exact (clause_sat_substUpdate_fresh b fun x hx hv => by
        have hlt := hs.1 c hmem x hx; omega).mpr hcs


end FullBvaFwdHelpers

namespace FullBvaFwdHelpers

/-- Introducing fresh variable `fv = s.core.cur_vars` (`< c.max_vars`) via `cur_vars += 1` +
`full_init_fresh_var` transitions `FullWitnessInv c F0 F_cur` to
`FullWitnessInv c F0 (bvaExtendFormula fv L Q F_cur)` and preserves `FullDenseInv`. -/
theorem fullDenseInv_add_fresh_var {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} {L Q : List Nat}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hmrk : FullLitMarksClear c s) (hnodup : FullArenaVarsNodup s)
    (hext : FullExtScratchOk c s) (hl0 : s.core.cur_level = 0) (hdm : s.core.dense_mode ≠ 0#64)
    (hcv_lt : s.core.cur_vars < c.max_vars)
    (hL : ∀ f ∈ L, f < 2 * s.core.cur_vars) (hQ : ∀ q ∈ Q, q < 2 * s.core.cur_vars)
    (hprod : ∀ f ∈ L, ∀ q ∈ Q, (cnfOfClauses F_cur).EntailsClause (cnfClause [f, q]))
    (hlen' : s'.LengthsOk c)
    {vals' mrk' flags' lvl' rsns' wvec' : _} {unass' : BitVec 64}
    (hcore' : s'.core =
      { s.core with
        cur_vars := s.core.cur_vars + 1, vals := vals', mrk := mrk', flags := flags',
        lvl := lvl', rsns := rsns', wvec := wvec', unassigned := unass' })
    (hv0 : vals'[2 * s.core.cur_vars]?.getD 1#8 = 0#8)
    (hv1 : vals'[2 * s.core.cur_vars + 1]?.getD 1#8 = 0#8)
    (hv_oth : ∀ l < 2 * c.max_vars, l / 2 ≠ s.core.cur_vars → vals'[l]? = s.core.vals[l]?)
    (hmrk_fv : mrk'[s.core.cur_vars]?.getD 1#8 = 0#8)
    (hmrk_oth : ∀ v < c.max_vars, v ≠ s.core.cur_vars → mrk'[v]? = s.core.mrk[v]?)
    (hlvl_oth : ∀ v < c.max_vars, v ≠ s.core.cur_vars → lvl'[v]? = s.core.lvl[v]?)
    (hrsns_oth : ∀ v < c.max_vars, v ≠ s.core.cur_vars → rsns'[v]? = s.core.rsns[v]?)
    (hwvec_0 : ∀ k < 4, wvec'[4 * s.core.cur_vars + k]?.getD 1#32 = 0#32)
    (hwvec_oth : ∀ i < 4 * c.max_vars, i / 4 ≠ s.core.cur_vars → wvec'[i]? = s.core.wvec[i]?)
    (hll' : s'.scratch.last_learned = s.scratch.last_learned)
    (hext' : s'.scratch.extend_len = s.scratch.extend_len) :
    let F_next := bvaExtendFormula s.core.cur_vars L Q F_cur
    FullWitnessInv c F0 F_next s'.core ∧ FullDenseInv c F0 s' := by
  intro F_next
  let fv := s.core.cur_vars
  have hcl := hlen.core_ok; have hcl' := hlen'.core_ok
  have hent_orig : (cnfOfClauses F_next).Entails (cnfOfClauses F_cur) :=
    bvaExtendFormula_entails_orig fv L Q F_cur
  have hext_next : ExtUnsatSound F0 (fv + 1) F_next :=
    extUnsatSound_bvaExtendFormula hw.ext_sound hL hQ hprod
  have hdw : DenseWatchesInv F_cur s.core := by
    have h := hw.watches; unfold ModeWatchesInv at h; rwa [ite_eq_right hdm] at h
  have hwvec'_len : wvec'.length = 4 * c.max_vars := by simpa only [hcore'] using hcl'.wvec_len
  have hvals'_len : vals'.length = 2 * c.max_vars := by simpa only [hcore'] using hcl'.vals_len
  have hmrk'_len : mrk'.length = c.max_vars := by simpa only [hcore'] using hcl'.mrk_len
  have hwvec_get : ∀ idx < 4 * c.max_vars,
      s'.core.wvec[idx]?.getD 0#32 =
        if 4 * fv ≤ idx ∧ idx < 4 * fv + 4 then 0#32 else s.core.wvec[idx]?.getD 0#32 :=
    fun idx hidx => by
      rw [hcore']; dsimp only
      by_cases hin : 4 * fv ≤ idx ∧ idx < 4 * fv + 4
      · simp only [hin]
        have hltw : idx < wvec'.length := by rw [hwvec'_len]; exact hidx
        have hz := hwvec_0 (idx - 4 * fv) (by omega)
        rw [show 4 * fv + (idx - 4 * fv) = idx by omega, List.getElem?_eq_getElem hltw,
          Option.getD_some] at hz
        rw [List.getElem?_eq_getElem hltw, Option.getD_some, hz]; rfl
      · simp only [hin, ↓reduceIte]; rw [hwvec_oth idx hidx (by omega)]
  have hoff_eq : ∀ l < 2 * (fv + 1),
      fullWatchOffCore s'.core l = if l < 2 * fv then fullWatchOffCore s.core l else 0 :=
    fun l hl => by
      unfold fullWatchOffCore; rw [hwvec_get (2 * l) (by omega)]
      by_cases hlt : l < 2 * fv
      · have hnot : ¬ (4 * fv ≤ 2 * l ∧ 2 * l < 4 * fv + 4) := by omega
        rw [ite_eq_right hnot, ite_eq_left hlt]
      · have hin : 4 * fv ≤ 2 * l ∧ 2 * l < 4 * fv + 4 := by omega
        rw [ite_eq_left hin, ite_eq_right hlt]; rfl
  have hsz_eq : ∀ l < 2 * (fv + 1),
      fullWatchSizeCore s'.core l = if l < 2 * fv then fullWatchSizeCore s.core l else 0 :=
    fun l hl => by
      unfold fullWatchSizeCore; rw [hwvec_get (2 * l + 1) (by omega)]
      by_cases hlt : l < 2 * fv
      · have hnot : ¬ (4 * fv ≤ 2 * l + 1 ∧ 2 * l + 1 < 4 * fv + 4) := by omega
        rw [ite_eq_right hnot, ite_eq_left hlt]
      · have hin : 4 * fv ≤ 2 * l + 1 ∧ 2 * l + 1 < 4 * fv + 4 := by omega
        rw [ite_eq_left hin, ite_eq_right hlt]; rfl
  have hvals_get : ∀ l < 2 * (fv + 1),
      s'.core.vals[l]?.getD 0#8 = if l < 2 * fv then s.core.vals[l]?.getD 0#8 else 0#8 :=
    fun l hl => by
      rw [hcore']; dsimp only
      have hltv : l < vals'.length := by rw [hvals'_len]; omega
      by_cases hlt : l < 2 * fv
      · simp only [hlt, ↓reduceIte]; rw [hv_oth l (by omega) (by omega)]
      · simp only [hlt, ↓reduceIte]
        by_cases h0 : l = 2 * fv
        · subst h0; rw [List.getElem?_eq_getElem hltv, Option.getD_some] at hv0 ⊢; exact hv0
        · have h1 : l = 2 * fv + 1 := by omega
          subst h1; rw [List.getElem?_eq_getElem hltv, Option.getD_some] at hv1 ⊢; exact hv1
  have hcv' : s'.core.cur_vars = fv + 1 := by rw [hcore']
  have hte' : s'.core.trail_end = s.core.trail_end := by rw [hcore']
  have htrl' : s'.core.trl = s.core.trl := by rw [hcore']
  have har' : s'.core.arena = s.core.arena := by rw [hcore']
  have hal' : s'.core.arena_len = s.core.arena_len := by rw [hcore']
  have hdm' : s'.core.dense_mode = s.core.dense_mode := by rw [hcore']
  have hcl_0 : s'.core.cur_level = 0 := by rw [hcore']; exact hl0
  have hrefs' : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core := by
    unfold fullArenaClauseRefsCore; rw [har', hal']
  have hlvl_old : ∀ i < s.core.trail_end,
      (s'.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := fun i hi => by
    have hlt := hw.trail_lits_lt i hi
    rw [hcore']; dsimp only; rw [hlvl_oth _ (by omega) (by omega)]
    have := hw.lvl_le i hi; omega
  have hrsn_old : ∀ i < s.core.trail_end,
      s'.core.rsns[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun i hi => by
      have hlt := hw.trail_lits_lt i hi
      rw [hcore']; dsimp only; rw [hrsns_oth _ (by omega) (by omega)]
      exact hw.level0_rsn_none i hi (by have := hw.lvl_le i hi; omega)
  have hdw' : DenseWatchesInv F_next s'.core := by
    refine DenseWatchesInv.of_slices ?_ ?_ ?_ ?_
    · intro l hl; rw [hcv'] at hl; rw [hoff_eq l hl, hsz_eq l hl]
      split
      · rename_i hlt; rw [hcore']; exact hdw.layout.bounds l hlt
      · omega
    · intro l hl hpos; rw [hcv'] at hl; rw [hoff_eq l hl]; rw [hsz_eq l hl] at hpos
      split at hpos
      · rename_i hlt; simp only [hlt, ↓reduceIte]; exact hdw.layout.pos_off l hlt hpos
      · omega
    · intro l1 l2 h1 h2 hne hp1 hp2
      rw [hcv'] at h1 h2; rw [hoff_eq l1 h1, hoff_eq l2 h2, hsz_eq l1 h1, hsz_eq l2 h2]
      rw [hsz_eq l1 h1] at hp1; rw [hsz_eq l2 h2] at hp2
      split at hp1
      · rename_i h1lt
        split at hp2
        · rename_i h2lt
          simp only [h1lt, h2lt, ↓reduceIte]
          exact hdw.layout.disjoint l1 l2 h1lt h2lt hne hp1 hp2
        · omega
      · omega
    · intro l hl; rw [hcv'] at hl; rw [hoff_eq l hl, hsz_eq l hl]
      by_cases hlt : l < 2 * fv
      · simp only [hlt, ↓reduceIte]
        exact (hdw.slices l hlt).mono hent_orig (by rw [hcv']; omega) (fun _ hr => hrefs' ▸ hr)
          (fun _ _ _ => by rw [hcore'])
      · simp only [hlt, ↓reduceIte]; exact .empty
  have harena' : FullArenaClausesInv c F_next s'.core := by
    refine ⟨by rw [hal']; exact hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs'] at hr
      simpa only [har', hal', fullArenaClauseSizeCore] using hw.arena.refs_wf r hr
    · intro r hr hsh; rw [hrefs'] at hr
      simpa only [har', hal', fullArenaHdrCore, fullArenaClauseSizeCore] using
        hw.arena.shrk_term r hr (by simpa only [har', fullArenaHdrCore] using hsh)
    · intro r hr hng l hl; rw [hrefs'] at hr
      have hng0 : fullArenaClauseGarbCore s.core r = false := by
        simpa only [har', fullArenaClauseGarbCore, fullArenaHdrCore] using hng
      have hl0' : l ∈ fullArenaClauseLitsCore s.core r := by
        simpa only [har', fullArenaClauseLitsCore, fullArenaClauseSizeCore] using hl
      have := hw.arena.lits_lt r hr hng0 l hl0'
      rw [hcv']; omega
    · intro r hr hng; rw [hrefs'] at hr
      have hng0 : fullArenaClauseGarbCore s.core r = false := by
        simpa only [har', fullArenaClauseGarbCore, fullArenaHdrCore] using hng
      have heq : fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := by
        unfold fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har']
      rw [heq]
      exact CNF.entails_clause_trans hent_orig (hw.arena.entails r hr hng0)
  have hw' : FullWitnessInv c F0 F_next s'.core :=
    { ext_sound := hcv'.symm ▸ hext_next
      inconsistent_sound := fun hinc => by
        have hinc0 : s.core.inconsistent ≠ 0#64 := by rwa [hcore'] at hinc
        have hu := hw.inconsistent_sound hinc0
        rw [CNF.unsat_iff_not_sat] at hu ⊢; rw [CNF.entails_def] at hent_orig
        intro α hα; exact hu α (hent_orig α hα)
      arena := harena'
      watches := by unfold ModeWatchesInv; rw [hdm', ite_eq_right hdm]; exact hdw'
      cur_level_le := by rw [hcl_0]; exact Nat.zero_le _
      trail_lits_lt := fun i hi => by
        rw [hte'] at hi; rw [htrl', hcv']; have := hw.trail_lits_lt i hi; omega
      trail_vars_nodup := fun i j hi hj => by
        rw [hte'] at hi hj; rw [htrl']; exact hw.trail_vars_nodup i j hi hj
      vals_domain := fun l hl => by
        rw [hcv'] at hl; rw [hvals_get l hl]
        split; exact hw.vals_domain l ‹_›; exact Or.inl rfl
      vals_true_iff := fun l hl => by
        rw [hcv'] at hl; rw [hvals_get l hl, hte', htrl']
        by_cases hlt : l < 2 * fv
        · simp only [hlt, ↓reduceIte]; exact hw.vals_true_iff l hlt
        · simp only [hlt, ↓reduceIte]; constructor
          · intro h; cases h
          · rintro ⟨i, hi, heq⟩; have := hw.trail_lits_lt i hi; omega
      vals_false_iff := fun l hl => by
        rw [hcv'] at hl; rw [hvals_get l hl, hte', htrl']
        by_cases hlt : l < 2 * fv
        · simp only [hlt, ↓reduceIte]; exact hw.vals_false_iff l hlt
        · simp only [hlt, ↓reduceIte]; constructor
          · intro h; cases h
          · rintro ⟨i, hi, heq⟩
            have := hw.trail_lits_lt i hi; rw [heq] at this
            have hlt2 := litNeg_lt_two_mul this
            rw [show (l ^^^ 1) ^^^ 1 = l from litNeg_litNeg l] at hlt2; omega
      lvl_le := fun i hi => by rw [hte'] at hi; rw [htrl', hlvl_old i hi]; exact Nat.zero_le _
      dec_earliest := fun i j hi hj _ hdec => by
        rw [hte'] at hj; rw [htrl', hlvl_old j hj] at hdec; omega
      levels_inhabited := fun L h1 hle => by rw [hcl_0] at hle; omega
      level0_sound := fun i hi _ => by
        rw [hte'] at hi; rw [htrl']
        exact CNF.entails_clause_trans hent_orig
          (hw.level0_sound i hi (by have := hw.lvl_le i hi; omega))
      trail_pos_inv := fun i hi => by
        rw [hte'] at hi; rw [htrl', show s'.core.trail_pos = s.core.trail_pos by rw [hcore']]
        exact hw.trail_pos_inv i hi
      level0_rsn_none := fun idx hidx _ => by
        rw [hte'] at hidx; rw [htrl']; exact hrsn_old idx hidx
      frame_trail_lt := fun L hL => by
        rw [hcl_0] at hL; rw [hte', show s'.core.frame_trail = s.core.frame_trail by rw [hcore']]
        exact hw.frame_trail_lt L (by omega)
      frame_trail_mono := fun L1 L2 h1 h2 => by
        rw [hcl_0] at h2; rw [show s'.core.frame_trail = s.core.frame_trail by rw [hcore']]
        exact hw.frame_trail_mono L1 L2 h1 (by omega)
      frame_trail_before_lt := fun L h1 h2 => by rw [hcl_0] at h2; omega
      frame_dec_lt := fun L h1 h2 => by rw [hcl_0] at h2; omega
      reason_inv := fun idx hidx hne => by
        rw [hte'] at hidx; rw [htrl'] at hne; exact absurd (hrsn_old idx hidx) hne
      reason_lit_mem := fun idx hidx hne _ => by
        rw [hte'] at hidx; rw [htrl'] at hne; exact absurd (hrsn_old idx hidx) hne }
  have hmrk' : FullLitMarksClear c s' := by
    refine ⟨fun v hv => ?_, fun l hl => ?_⟩
    · rw [hcore']; dsimp only
      by_cases hve : v = fv
      · subst hve; have hltm : fv < mrk'.length := by rw [hmrk'_len]; exact hv
        rw [List.getElem?_eq_getElem hltm, Option.getD_some] at hmrk_fv ⊢; exact hmrk_fv
      · rw [hmrk_oth v hv hve]; exact hmrk.1 v hv
    · rw [show s'.core.lit_mark = s.core.lit_mark by rw [hcore']]; exact hmrk.2 l hl
  have hnodup' : FullArenaVarsNodup s' := by
    intro r hr hng; change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs'] at hr
    have hng0 : fullArenaClauseGarb s r = false := by
      simpa only [fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore, har'] using hng
    have hlits_eq : fullArenaClauseLits s' r = fullArenaClauseLits s r := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har']
    rw [hlits_eq]; exact hnodup r hr hng0
  have hext_ok' : FullExtScratchOk c s' :=
    ⟨fun i hi => by
      dsimp only; unfold fullArenaClauseRefs; rw [hll', hrefs']; exact hext.1 i hi,
     by rw [hext']; exact hext.2⟩
  exact ⟨hw', ⟨⟨hlen', F_next, hw'⟩, hmrk', hnodup', hext_ok', hcl_0, hdm' ▸ hdm⟩⟩

private theorem fwd_bit23_shrk : (0x00800000#32 : BitVec 32)[23] = true := by decide

/-- Skipping a prefix of non-sentinel words in `fullArenaSkipShrk`. -/
theorem fullArenaSkipShrk_skip_prefix {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {d fuel p : Nat}, p + d ≤ alen → d ≤ fuel →
      (∀ i, p ≤ i → i < p + d → ar[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) →
      fullArenaSkipShrk ar alen p fuel = fullArenaSkipShrk ar alen (p + d) (fuel - d)
  | 0, fuel, p, _, _, _ => by rw [Nat.add_zero, Nat.sub_zero]
  | d + 1, 0, _, _, hf, _ => by omega
  | d + 1, fuel + 1, p, hle, hf, hne => by
    have hp : p < alen := by omega
    have h0 : ar[p]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := hne p (Nat.le_refl _) (by omega)
    have hstep :
        fullArenaSkipShrk ar alen p (fuel + 1) = fullArenaSkipShrk ar alen (p + 1) fuel := by
      rw [fullArenaSkipShrk]; simp only [hp, ↓reduceIte, h0, ne_eq, not_false_eq_true]
    rw [hstep, show p + (d + 1) = p + 1 + d by omega, show fuel + 1 - (d + 1) = fuel - d by omega]
    exact fullArenaSkipShrk_skip_prefix (ar := ar) (alen := alen) (d := d) (fuel := fuel)
      (p := p + 1) (by omega) (by omega) fun i hi1 hi2 => hne i (by omega) (by omega)

/-- Shrinking live clause `cref` in place (`3 ≤ nsz < sz`) at `cur_level = 0` preserves
`fullArenaClauseRefsCore` and `FullWitnessInv c F0 F_cur`. -/
theorem fullWitnessInv_shrink_at_root {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c) (hw : FullWitnessInv c F0 F_cur k)
    (hl0 : k.cur_level = 0) {cref nsz : Nat} (href : cref ∈ fullArenaClauseRefsCore k)
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < fullArenaClauseSizeCore k cref)
    {arena' : List (BitVec 32)}
    (hal : arena'.length = c.arena_cap)
    (hhdr' : arena'[cref]? = some (if (fullArenaHdrCore k cref &&& 0x00800000#32) = 0#32
      then fullArenaHdrCore k cref ||| 0x00800000#32 else fullArenaHdrCore k cref))
    (hsz' : arena'[cref + 2]? = some (BitVec.ofNat 32 nsz))
    (hpad_new : (fullArenaHdrCore k cref &&& 0x00800000#32) = 0#32 →
      arena'[cref + 3 + fullArenaClauseSizeCore k cref - 1]? = some 0xFFFFFFFF#32 ∧
      ∀ i, cref + 3 + nsz ≤ i → i < cref + 3 + fullArenaClauseSizeCore k cref - 1 →
        arena'[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hpad_old : (fullArenaHdrCore k cref &&& 0x00800000#32) ≠ 0#32 →
      ∀ i, cref + 3 + nsz ≤ i → i < cref + 3 + fullArenaClauseSizeCore k cref →
        arena'[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hout : ∀ i, i < cref ∨ cref + 3 + fullArenaClauseSizeCore k cref ≤ i →
      arena'[i]? = k.arena[i]?)
    (hnew_lits_lt : ∀ l ∈ fullArenaClauseLitsCore { k with arena := arena' } cref,
      l < 2 * k.cur_vars)
    (hnew_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { k with arena := arena' } cref))) :
    let k' : FullCoreState := { k with arena := arena' }
    k'.LengthsOk c ∧
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    FullWitnessInv c F0 F_cur k' ∧
    (∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) := by
  intro k'
  have hcref_wf := hw.arena.refs_wf cref href
  have hsz_lt32 : nsz < 2 ^ 32 := by
    have := hlen.arena_len_le; have := c.harena; unfold dimacsBound at *; omega
  have har_len : cref < k.arena.length := by
    have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
  have hget_cref : k.arena[cref]? = some (fullArenaHdrCore k cref) := by
    unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem har_len, Option.getD_some]
  have hbit23_or : ∀ x : BitVec 32, ((x ||| 0x00800000#32) &&& 0x00800000#32) ≠ 0#32 :=
    fun x h => by have h23 := congrArg (·[23]) h; revert h23; simp [fwd_bit23_shrk]
  have hne_outside : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore k r ≤ cref ∧ fullArenaNextOff k.arena k.arena_len r ≤ cref) ∨
      (cref + 3 + fullArenaClauseSizeCore k cref ≤ r ∧
        fullArenaNextOff k.arena k.arena_len cref ≤ r) := by
    intro r hr hne; rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have := fullArenaScanRefs_disjoint hr href hlt
      have := (hw.arena.refs_wf r hr).2.2.1; exact Or.inl ⟨by omega, by omega⟩
    · have := fullArenaScanRefs_disjoint href hr hgt; exact Or.inr ⟨by omega, by omega⟩
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff arena' k.arena_len r = fullArenaNextOff k.arena k.arena_len r := by
    intro r hr
    by_cases hrc : r = cref
    · subst r
      have h1 : ¬ (cref + 3 > k.arena_len) := by omega
      have h2_old : ¬ (cref + 3 + (k.arena[cref + 2]?.getD 0#32).toNat > k.arena_len) := by
        unfold fullArenaClauseSizeCore at hcref_wf; omega
      have h2_new : ¬ (cref + 3 + nsz > k.arena_len) := by omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2_old, hhdr', hsz', Option.getD_some,
        bv32_ofNat_toNat hsz_lt32, h2_new]
      by_cases hsh : (fullArenaHdrCore k cref &&& 0x00800000#32) = 0#32
      · have hsh_ar : (k.arena[cref]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
          rw [hget_cref, Option.getD_some]; exact hsh
        simp only [hsh, ↓reduceIte, hbit23_or, ne_eq, not_false_eq_true, hsh_ar]
        obtain ⟨hsent, hskip⟩ := hpad_new hsh
        rw [show (k.arena[cref + 2]?.getD 0#32).toNat = fullArenaClauseSizeCore k cref from rfl,
          fullArenaSkipShrk_skip_prefix (ar := arena') (alen := k.arena_len)
            (d := fullArenaClauseSizeCore k cref - 1 - nsz)
            (fuel := k.arena_len - (cref + 3 + nsz)) (p := cref + 3 + nsz)
            (by omega) (by omega) fun i hi1 hi2 => hskip i hi1 (by omega),
          show cref + 3 + nsz + (fullArenaClauseSizeCore k cref - 1 - nsz) =
            cref + 3 + fullArenaClauseSizeCore k cref - 1 by omega,
          show k.arena_len - (cref + 3 + nsz) - (fullArenaClauseSizeCore k cref - 1 - nsz) =
            (k.arena_len - (cref + 3 + fullArenaClauseSizeCore k cref)) + 1 by omega]
        unfold fullArenaSkipShrk
        have hlt_a : cref + 3 + fullArenaClauseSizeCore k cref - 1 < k.arena_len := by omega
        simp only [hlt_a, ↓reduceIte, hsent, Option.getD_some, ne_eq, not_true_eq_false]; omega
      · have hsh_ar : (k.arena[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
          rw [hget_cref, Option.getD_some]; exact hsh
        simp only [hsh, ↓reduceIte, ne_eq, not_false_eq_true, hsh_ar]
        have hskip := hpad_old hsh
        rw [show (k.arena[cref + 2]?.getD 0#32).toNat = fullArenaClauseSizeCore k cref from rfl,
          fullArenaSkipShrk_skip_prefix (ar := arena') (alen := k.arena_len)
            (d := fullArenaClauseSizeCore k cref - nsz)
            (fuel := k.arena_len - (cref + 3 + nsz)) (p := cref + 3 + nsz)
            (by omega) (by omega) fun i hi1 hi2 => hskip i hi1 (by omega),
          show cref + 3 + nsz + (fullArenaClauseSizeCore k cref - nsz) =
            cref + 3 + fullArenaClauseSizeCore k cref by omega,
          show k.arena_len - (cref + 3 + nsz) - (fullArenaClauseSizeCore k cref - nsz) =
            k.arena_len - (cref + 3 + fullArenaClauseSizeCore k cref) by omega]
        exact fullArenaSkipShrk_congr fun i hi _ => hout i (Or.inr hi)
    · have hne := hne_outside r hr hrc; have := (hw.arena.refs_wf r hr).2.1
      refine fullArenaNextOff_congr_block
        (hout r (hne.imp (fun _ => by omega) (fun _ => by omega)))
        (hout (r + 2) (hne.imp (fun _ => by omega) (fun _ => by omega)))
        fun i hi1 hi2 => hout i (hne.imp (fun _ => by omega) (fun _ => by omega))
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hsz_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = if r = cref then nsz else fullArenaClauseSizeCore k r :=
    fun r hr => by
      unfold fullArenaClauseSizeCore; dsimp only [k']
      by_cases hrc : r = cref
      · subst r; simp [hsz', bv32_ofNat_toNat hsz_lt32]
      · simp only [hrc, ↓reduceIte]; have := (hw.arena.refs_wf r hr).2.1
        rw [hout (r + 2) ((hne_outside r hr hrc).imp (fun _ => by omega) (fun _ => by omega))]
  have hgarb_eq : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := fun r hr hne => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [k']
    rw [hout r ((hne_outside r hr hne).imp (fun _ => by omega) (fun _ => by omega))]
  have hlits_eq : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := fun r hr hne => by
    have hwf := hw.arena.refs_wf r hr; have := hlen.arena_len_le; have := hlen.arena_len_arr
    refine fullArenaClauseLitsCore_eq_of_hold (by omega) (by dsimp only [k']; omega)
      (by simpa [hne] using hsz_eq r hr) fun j hj => by
        dsimp only [k']
        exact hout (r + 3 + j) ((hne_outside r hr hne).imp (fun _ => by omega) (fun _ => by omega))
  have harena' : FullArenaClausesInv c F_cur k' := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := hw.arena.refs_wf r hr
      dsimp only [k'] at hnxt ⊢; rw [hnxt r hr, hsz_eq r hr]
      split
      · subst r; exact ⟨hwf.1, hnsz3, by omega, hwf.2.2.2.1, hwf.2.2.2.2⟩
      · exact hwf
    · intro r hr hsh; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r
        by_cases hsh0 : (fullArenaHdrCore k cref &&& 0x00800000#32) = 0#32
        · obtain ⟨hsent, _⟩ := hpad_new hsh0
          refine ⟨cref + 3 + fullArenaClauseSizeCore k cref - 1,
            by rw [hsz_eq cref hr]; simp only [↓reduceIte]; omega, by dsimp only [k']; omega, hsent⟩
        · obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term cref hr hsh0
          refine ⟨t, by rw [hsz_eq cref hr]; simp only [↓reduceIte]; omega,
            by dsimp only [k']; omega, by dsimp only [k']; rw [hout t (Or.inr ht1)]; exact hsent⟩
      · have hsh0 : (fullArenaHdrCore k r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢; dsimp only [k'] at hsh
          rwa [hout r ((hne_outside r hr hrc).imp (fun _ => by omega) (fun _ => by omega))] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
        have hsh_ar : (k.arena[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := hsh0
        obtain ⟨t0, ht0_lo, _, _, ht0_sent⟩ :=
          fullArenaNextOff_hits_sentinel (hw.arena.refs_wf r hr).1 hsh_ar ht1 ht2 hsent
        refine ⟨t0, by rw [hsz_eq r hr, ite_eq_right hrc]; exact ht0_lo,
          by dsimp only [k']; omega, ?_⟩
        dsimp only [k']
        rw [hout t0 ((hne_outside r hr hrc).imp (fun _ => by omega) (fun _ => by omega))]
        exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; exact hnew_lits_lt l hl
      · rw [hgarb_eq r hr hrc] at hng; rw [hlits_eq r hr hrc] at hl
        exact hw.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; exact hnew_ent
      · rw [hgarb_eq r hr hrc] at hng; rw [hlits_eq r hr hrc]
        exact hw.arena.entails r hr hng
  have hno_rsn : ∀ idx < k.trail_end,
      k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun idx hidx => hw.level0_rsn_none idx hidx (by have := hw.lvl_le idx hidx; omega)
  refine ⟨{ hlen with arena_len_arr := hal }, hrefs,
    { hw with
      arena := harena'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hrefs ▸ hr)
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne },
    fun r hr hne => ⟨hgarb_eq r hr hne, hlits_eq r hr hne⟩⟩

/-- Setting `inconsistent := 1#64` when `(cnfOfClauses F_cur).Unsat` preserves `FullWitnessInv`. -/
theorem fullWitnessInv_set_inconsistent {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hu : (cnfOfClauses F_cur).Unsat) :
    FullWitnessInv c F0 F_cur { k with inconsistent := 1#64 } :=
  { hw with
    inconsistent_sound := fun _ => hu, arena := { hw.arena with len_ok := hw.arena.len_ok },
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

/-- `(setWidth 32 (ofNat 64 v) <<< 1) ^^^ 1#32` equals `2 * v + 1` when in 32-bit range. -/
theorem bva_bv32_shl1_xor1 {v : Nat} (hv : 2 * v + 1 < 2 ^ 32) :
    ((BitVec.setWidth 32 (BitVec.ofNat 64 v) <<< (1 : Nat)) ^^^ 1#32).toNat = 2 * v + 1 := by
  have hshl : (BitVec.setWidth 32 (BitVec.ofNat 64 v) <<< (1 : Nat)).toNat = 2 * v := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt
      (by omega), Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
    omega
  have heq : (BitVec.setWidth 32 (BitVec.ofNat 64 v) <<< (1 : Nat)) ^^^ 1#32 =
      (BitVec.setWidth 32 (BitVec.ofNat 64 v) <<< (1 : Nat)) ||| 1#32 := by
    ext i hi; simp only [BitVec.getElem_xor, BitVec.getElem_or]
    cases i with
    | zero => simp [BitVec.getElem_shiftLeft]
    | succ n => simp [BitVec.getElem_eq_testBit_toNat, Nat.testBit_succ]
  rw [heq, FullBvaFwdTactics.bv32_or1_of_even (by rw [hshl]; omega), hshl]

end FullBvaFwdHelpers

open FullBvaFwdHelpers

/-! ## 2. Pure Generalized BVA Soundness, `PH_VIV`, & Clause-Matching Lemmas -/

namespace FullBvaHeapHelpers

/-- Generalized fresh-variable BVA extension formula over multi-literal residue clauses `Qs`:
adjoins `[2 * fv, f]` (`f ∈ L`) and `(2 * fv + 1) :: R` (`R ∈ Qs`) to `F_cur`. -/
@[expose] def bvaExtendGen (fv : Nat) (L : List Nat) (Qs : List (List Nat))
    (F_cur : List (List Nat)) : List (List Nat) :=
  L.map (fun f => [2 * fv, f]) ++ Qs.map (fun R => (2 * fv + 1) :: R) ++ F_cur

theorem bvaExtendGen_entails_orig (fv : Nat) (L : List Nat) (Qs : List (List Nat))
    (F_cur : List (List Nat)) :
    (cnfOfClauses (bvaExtendGen fv L Qs F_cur)).Entails (cnfOfClauses F_cur) := by
  rw [CNF.entails_def]; intro α hα; rw [cnf_sat_cnfOfClauses_iff] at hα ⊢
  exact fun cl hcl => hα cl (List.mem_append_right _ hcl)

theorem bvaExtendGen_entails_pos {fv : Nat} {L : List Nat} {Qs : List (List Nat)}
    {F_cur : List (List Nat)} {f : Nat} (hf : f ∈ L) :
    (cnfOfClauses (bvaExtendGen fv L Qs F_cur)).EntailsClause (cnfClause [2 * fv, f]) :=
  entails_mem_cnfOfClauses
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨f, hf, rfl⟩)))

theorem bvaExtendGen_entails_neg {fv : Nat} {L : List Nat} {Qs : List (List Nat)}
    {F_cur : List (List Nat)} {R : List Nat} (hR : R ∈ Qs) :
    (cnfOfClauses (bvaExtendGen fv L Qs F_cur)).EntailsClause (cnfClause ((2 * fv + 1) :: R)) :=
  entails_mem_cnfOfClauses
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨R, hR, rfl⟩)))

/-- Generalized fresh-variable BVA UNSAT soundness: any model `α` of `F_cur` extends to a model
of `bvaExtendGen mv_cur L Qs F_cur` by setting `mv_cur := true` iff `α` satisfies every residue
clause `R ∈ Qs`. -/
theorem extUnsatSound_bvaExtendGen {F0 : CNF Nat} {mv_cur : Nat} {F_cur : List (List Nat)}
    {L : List Nat} {Qs : List (List Nat)} (hs : ExtUnsatSound F0 mv_cur F_cur)
    (hL : ∀ f ∈ L, f < 2 * mv_cur) (hQ : ∀ R ∈ Qs, ∀ q ∈ R, q < 2 * mv_cur)
    (hprod : ∀ f ∈ L, ∀ R ∈ Qs, (cnfOfClauses F_cur).EntailsClause (cnfClause (f :: R))) :
    ExtUnsatSound F0 (mv_cur + 1) (bvaExtendGen mv_cur L Qs F_cur) := by
  refine ⟨fun c hc l hl => ?_, fun hu => hs.2 ?_⟩
  · unfold bvaExtendGen at hc
    simp only [List.mem_append, List.mem_map] at hc
    rcases hc with (⟨f, hf, rfl⟩ | ⟨R, hR, rfl⟩) | hmem
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · simp [litVar]
      · have := hL l hf; simp [litVar]; omega
    · simp only [List.mem_cons] at hl
      rcases hl with rfl | hmemR
      · simp [litVar]; omega
      · have := hQ R hR l hmemR; simp [litVar]; omega
    · exact Nat.lt_succ_of_lt (hs.1 c hmem l hl)
  · rw [CNF.unsat_iff_not_sat] at hu ⊢
    intro α hα
    let b : Bool := Qs.all (clauseEvalVal α)
    let α' : Nat → Bool := substUpdate α mv_cur b
    have hfresh_lit : ∀ x < 2 * mv_cur, evalLitVal α' x = evalLitVal α x := fun x hx => by
      have hne : litVar x ≠ mv_cur := by simp [litVar]; omega
      simp [evalLitVal, α', substUpdate_ne α b hne]
    have hfresh_cl : ∀ R : List Nat, (∀ x ∈ R, x < 2 * mv_cur) →
        clauseEvalVal α' R = clauseEvalVal α R := fun R hR => by
      unfold clauseEvalVal; induction R with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.any_cons, hfresh_lit x (hR x (by simp)),
          ih (fun y hy => hR y (by simp [hy]))]
    apply hu α'
    rw [cnf_sat_cnfOfClauses_iff]
    intro c hc
    unfold bvaExtendGen at hc
    simp only [List.mem_append, List.mem_map] at hc
    rcases hc with (⟨f, hf, rfl⟩ | ⟨R, hR, rfl⟩) | hmem
    · rw [← clauseEvalVal_iff, clauseEvalVal]
      simp only [List.any_cons, List.any_nil, Bool.or_false, hfresh_lit f (hL f hf)]
      have hpos : evalLitVal α' (2 * mv_cur) = b := by simp [evalLitVal, litVar, litSign, α']
      rw [hpos]
      cases hb : b
      · simp only [Bool.false_or]
        obtain ⟨R0, hR0, hR0f⟩ := List.all_eq_false.mp hb
        have hR0_eq : clauseEvalVal α R0 = false := Bool.eq_false_iff.mpr hR0f
        have hcl := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp (hprod f hf R0 hR0) α hα)
        simp only [clauseEvalVal, List.any_cons] at hcl
        change (evalLitVal α f || clauseEvalVal α R0) = true at hcl
        rwa [hR0_eq, Bool.or_false] at hcl
      · simp
    · rw [← clauseEvalVal_iff, clauseEvalVal, List.any_cons]
      have hneg : evalLitVal α' (2 * mv_cur + 1) = !b := by
        have hv : litVar (2 * mv_cur + 1) = mv_cur := by simp [litVar]; omega
        have hs' : litSign (2 * mv_cur + 1) = true := by simp [litSign]
        simp [evalLitVal, hv, hs', α']
      change (evalLitVal α' (2 * mv_cur + 1) || clauseEvalVal α' R) = true
      rw [hneg, hfresh_cl R (hQ R hR)]
      cases hb : b
      · simp
      · simp only [Bool.not_true, Bool.false_or]
        exact List.all_eq_true.mp hb R hR
    · have hcs := (cnf_sat_cnfOfClauses_iff α F_cur).mp hα c hmem
      exact (clause_sat_substUpdate_fresh b fun x hx hv => by
        have hlt := hs.1 c hmem x hx; omega).mpr hcs

/-- Generalized fresh-variable introduction for `bvaExtendGen` preserving `FullWitnessInv` and
`FullDenseInv`. -/
theorem fullDenseInv_add_fresh_var_gen {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} {L : List Nat} {Qs : List (List Nat)}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hmrk : FullLitMarksClear c s) (hnodup : FullArenaVarsNodup s)
    (hext : FullExtScratchOk c s) (hl0 : s.core.cur_level = 0) (hdm : s.core.dense_mode ≠ 0#64)
    (hcv_lt : s.core.cur_vars < c.max_vars)
    (hL : ∀ f ∈ L, f < 2 * s.core.cur_vars)
    (hQs : ∀ R ∈ Qs, ∀ q ∈ R, q < 2 * s.core.cur_vars)
    (hprod : ∀ f ∈ L, ∀ R ∈ Qs, (cnfOfClauses F_cur).EntailsClause (cnfClause (f :: R)))
    (hlen' : s'.LengthsOk c)
    {vals' mrk' flags' lvl' rsns' wvec' : _} {unass' : BitVec 64}
    (hcore' : s'.core =
      { s.core with
        cur_vars := s.core.cur_vars + 1, vals := vals', mrk := mrk', flags := flags',
        lvl := lvl', rsns := rsns', wvec := wvec', unassigned := unass' })
    (hv0 : vals'[2 * s.core.cur_vars]?.getD 1#8 = 0#8)
    (hv1 : vals'[2 * s.core.cur_vars + 1]?.getD 1#8 = 0#8)
    (hv_oth : ∀ l < 2 * c.max_vars, l / 2 ≠ s.core.cur_vars → vals'[l]? = s.core.vals[l]?)
    (hmrk_fv : mrk'[s.core.cur_vars]?.getD 1#8 = 0#8)
    (hmrk_oth : ∀ v < c.max_vars, v ≠ s.core.cur_vars → mrk'[v]? = s.core.mrk[v]?)
    (hlvl_oth : ∀ v < c.max_vars, v ≠ s.core.cur_vars → lvl'[v]? = s.core.lvl[v]?)
    (hrsns_oth : ∀ v < c.max_vars, v ≠ s.core.cur_vars → rsns'[v]? = s.core.rsns[v]?)
    (hwvec_0 : ∀ k < 4, wvec'[4 * s.core.cur_vars + k]?.getD 1#32 = 0#32)
    (hwvec_oth : ∀ i < 4 * c.max_vars, i / 4 ≠ s.core.cur_vars → wvec'[i]? = s.core.wvec[i]?)
    (hll' : s'.scratch.last_learned = s.scratch.last_learned)
    (hext' : s'.scratch.extend_len = s.scratch.extend_len) :
    let F_next := bvaExtendGen s.core.cur_vars L Qs F_cur
    FullWitnessInv c F0 F_next s'.core ∧ FullDenseInv c F0 s' := by
  intro F_next
  let fv := s.core.cur_vars
  have ⟨hw0, hd0⟩ := FullBvaFwdHelpers.fullDenseInv_add_fresh_var (L := []) (Q := [])
    hlen hw hmrk hnodup hext hl0 hdm hcv_lt (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) hlen' hcore' hv0 hv1 hv_oth hmrk_fv hmrk_oth hlvl_oth hrsns_oth
    hwvec_0 hwvec_oth hll' hext'
  have hcv' : s'.core.cur_vars = fv + 1 := by rw [hcore']
  have hext_next : ExtUnsatSound F0 s'.core.cur_vars F_next :=
    hcv'.symm ▸ extUnsatSound_bvaExtendGen hw.ext_sound hL hQs hprod
  have hent_gen : (cnfOfClauses F_next).Entails
      (cnfOfClauses (FullBvaFwdHelpers.bvaExtendFormula fv [] [] F_cur)) := by
    simpa [FullBvaFwdHelpers.bvaExtendFormula] using bvaExtendGen_entails_orig fv L Qs F_cur
  have hw' : FullWitnessInv c F0 F_next s'.core := hw0.replace_extSound hext_next hent_gen
  exact ⟨hw', ⟨⟨hlen', F_next, hw'⟩, hd0.2.1, hd0.2.2.1, hd0.2.2.2.1, hd0.2.2.2.2.1,
    hd0.2.2.2.2.2⟩⟩

/-- Bit-20 (`PH_VIV = 0x00100000`) updates on arena clause headers leave `PH_GARB` (bit 19) and
`PH_SHRK` (bit 23) unchanged, hence preserve `fullArenaClauseRefsCore`, `FullWitnessInv`, and
`FullDenseInv`. -/
theorem bv32_or_viv_garb (x : BitVec 32) :
    ((x ||| 0x00100000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) := by
  rw [BitVec.and_or_distrib_right,
    show (0x00100000#32 &&& 0x00080000#32) = 0#32 from rfl, BitVec.or_zero]

theorem bv32_or_viv_shrk (x : BitVec 32) :
    ((x ||| 0x00100000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  rw [BitVec.and_or_distrib_right,
    show (0x00100000#32 &&& 0x00800000#32) = 0#32 from rfl, BitVec.or_zero]

theorem bv32_and_not_viv_garb (x : BitVec 32) :
    ((x &&& ~~~0x00100000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) := by
  rw [BitVec.and_assoc, show (~~~0x00100000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl]

theorem bv32_and_not_viv_shrk (x : BitVec 32) :
    ((x &&& ~~~0x00100000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  rw [BitVec.and_assoc, show (~~~0x00100000#32 &&& 0x00800000#32) = 0x00800000#32 from rfl]

theorem bv32_viv_roundtrip {x : BitVec 32} (h : (x &&& 0x00100000#32) = 0#32) :
    ((x ||| 0x00100000#32) &&& ~~~0x00100000#32) = x := by
  rw [BitVec.and_or_distrib_right,
    show (0x00100000#32 &&& ~~~0x00100000#32) = 0#32 from rfl, BitVec.or_zero]
  have h1 : x = x &&& (~~~0x00100000#32 ||| 0x00100000#32) := by
    rw [show (~~~0x00100000#32 ||| 0x00100000#32) = BitVec.allOnes 32 from rfl, BitVec.and_allOnes]
  conv => rhs; rw [h1, BitVec.and_or_distrib_left, h, BitVec.or_zero]

theorem fullWitnessInv_set_hdr_bit20 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c) (hw : FullWitnessInv c F0 F_cur k)
    (hl0 : k.cur_level = 0) {cref : Nat} (href : cref ∈ fullArenaClauseRefsCore k) (v : BitVec 32)
    (h19 : (v &&& 0x00080000#32) = (fullArenaHdrCore k cref &&& 0x00080000#32))
    (h23 : (v &&& 0x00800000#32) = (fullArenaHdrCore k cref &&& 0x00800000#32)) :
    let k' : FullCoreState := { k with arena := k.arena.set cref v }
    k'.LengthsOk c ∧ fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    FullWitnessInv c F0 F_cur k' ∧
    (∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) := by
  intro k'
  have hcref_wf := hw.arena.refs_wf cref href
  have har_len : cref < k.arena.length := by
    have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
  have ha_cref : k'.arena[cref]? = some v := List.getElem?_set_self har_len
  have hne_out : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore k r ≤ cref ∧ fullArenaNextOff k.arena k.arena_len r ≤ cref) ∨
      (cref + 3 ≤ fullArenaNextOff k.arena k.arena_len cref ∧
        fullArenaNextOff k.arena k.arena_len cref ≤ r) := fun r hr hne => by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨by have := fullArenaScanRefs_disjoint hr href hlt
                       have := (hw.arena.refs_wf r hr).2.2.1; omega,
        fullArenaScanRefs_disjoint hr href hlt⟩
    · exact Or.inr ⟨by omega, fullArenaScanRefs_disjoint href hr hgt⟩
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff k'.arena k.arena_len r = fullArenaNextOff k.arena k.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r
      have h2eq : k'.arena[cref + 2]? = k.arena[cref + 2]? := List.getElem?_set_ne (by omega)
      have h1 : ¬ (cref + 3 > k.arena_len) := by omega
      have h2 : ¬ (cref + 3 + (k.arena[cref + 2]?.getD 0#32).toNat > k.arena_len) := by
        unfold fullArenaClauseSizeCore at hcref_wf; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2, ha_cref, Option.getD_some]
      rw [h23, show fullArenaHdrCore k cref = k.arena[cref]?.getD 0#32 from rfl]
      split
      · exact fullArenaSkipShrk_congr fun i hi _ => List.getElem?_set_ne (by omega)
      · rfl
    · refine fullArenaNextOff_congr_block (List.getElem?_set_ne (Ne.symm hrc)) ?_ ?_
      · rcases hne_out r hr hrc with ⟨hlt, _⟩ | ⟨h3, hgt⟩
        · have := (hw.arena.refs_wf r hr).2.1; exact List.getElem?_set_ne (by omega)
        · exact List.getElem?_set_ne (by omega)
      · intro i hi1 _
        rcases hne_out r hr hrc with ⟨_, hle⟩ | ⟨h3, hgt⟩
        · exact List.getElem?_set_ne (by omega)
        · have := (hw.arena.refs_wf r hr).2.2.1; exact List.getElem?_set_ne (by omega)
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hsz_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := fun r hr => by
    unfold fullArenaClauseSizeCore; dsimp only [k']
    by_cases hrc : r = cref
    · subst r; rw [List.getElem?_set_ne (by omega)]
    · rcases hne_out r hr hrc with ⟨hlt, _⟩ | ⟨h3, hgt⟩
      · have := (hw.arena.refs_wf r hr).2.1; rw [List.getElem?_set_ne (by omega)]
      · rw [List.getElem?_set_ne (by omega)]
  have hgarb_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := fun r hr => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [k']
    by_cases hrc : r = cref
    · subst r; rw [List.getElem?_set_self har_len, Option.getD_some, h19]; rfl
    · rw [List.getElem?_set_ne (Ne.symm hrc)]
  have hlits_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := fun r hr => by
    have hwf := hw.arena.refs_wf r hr
    have hk_bd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := by
      have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
    refine fullArenaClauseLitsCore_eq_of_hold hk_bd (by simpa [k'] using hk_bd) (hsz_eq r hr) ?_
    intro j hj; dsimp only [k']; apply List.getElem?_set_ne
    by_cases hrc : r = cref
    · subst r; omega
    · rcases hne_out r hr hrc with ⟨h1, _⟩ | ⟨h3, h2⟩ <;> omega
  have harena' : FullArenaClausesInv c F_cur k' := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; dsimp only [k'] at hnxt ⊢
      rw [hnxt r hr, hsz_eq r hr]; exact hw.arena.refs_wf r hr
    · intro r hr hsh; rw [hrefs] at hr
      have hsh0 : (fullArenaHdrCore k r &&& 0x00800000#32) ≠ 0#32 := by
        by_cases hrc : r = cref
        · subst r; unfold fullArenaHdrCore at hsh h23 ⊢; simpa [ha_cref, h23] using hsh
        · unfold fullArenaHdrCore at hsh ⊢
          simpa [k', List.getElem?_set_ne (Ne.symm hrc)] using hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
      have hget_r : k.arena[r]? = some (fullArenaHdrCore k r) := by
        have hr3 := (hw.arena.refs_wf r hr).1
        have : r < k.arena.length := by have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      obtain ⟨t0, ht0_lo, _, ht0_nxt, ht0_sent⟩ :=
        fullArenaNextOff_hits_sentinel (hw.arena.refs_wf r hr).1
          (by rw [hget_r, Option.getD_some]; exact hsh0) ht1 ht2 hsent
      have ht0_ne : t0 ≠ cref := by
        by_cases hrc : r = cref
        · subst r; have := (hw.arena.refs_wf cref hr).2.1; omega
        · rcases hne_out r hr hrc with ⟨_, hle⟩ | ⟨h3, hgt⟩
          · omega
          · have := (hw.arena.refs_wf r hr).2.1; omega
      have hnxt_le : fullArenaNextOff k.arena k.arena_len r ≤ k.arena_len :=
        (hw.arena.refs_wf r hr).2.2.2.1
      refine ⟨t0, by rw [hsz_eq r hr]; exact ht0_lo, by dsimp only [k']; omega, ?_⟩
      dsimp only [k']; rw [List.getElem?_set_ne ht0_ne.symm]; exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [hgarb_eq r hr] at hng; rw [hlits_eq r hr] at hl
      exact hw.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      rw [hgarb_eq r hr] at hng; rw [hlits_eq r hr]
      exact hw.arena.entails r hr hng
  have hno_rsn : ∀ idx < k.trail_end,
      k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun idx hidx => hw.level0_rsn_none idx hidx (by have := hw.lvl_le idx hidx; omega)
  refine ⟨{ hlen with arena_len_arr := by simp [k', hlen.arena_len_arr] }, hrefs,
    { hw with
      arena := harena'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hrefs ▸ hr)
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne },
    fun r hr => ⟨hgarb_eq r hr, hsz_eq r hr, hlits_eq r hr⟩⟩

/-- Updating only non-soundness core scratch (`repr`, `min_clr`, `tmp`, `tmp_cnt`, `tmp_len`,
`flags`) preserves `FullWitnessInv`. -/
theorem fullWitnessInv_with_core_aux {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    {repr' min_clr' tmp' flags' : List (BitVec 32)} {tc' tl' : Nat} :
    FullWitnessInv c F0 F_cur
      { k with repr := repr', min_clr := min_clr', tmp := tmp', flags := flags',
               tmp_cnt := tc', tmp_len := tl' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem fullDenseInv_with_core_aux {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {repr' min_clr' tmp' flags' : List (BitVec 32)} {tc' tl' : Nat} {sc' : FullScratch}
    (hr : repr'.length = 2 * c.max_vars) (hmc : min_clr'.length = c.max_vars)
    (htmp : tmp'.length = c.max_vars) (hfl : flags'.length = c.max_vars)
    (htl : tl' ≤ c.max_vars) (hsc : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullDenseInvW c F0 F_cur
      { core := { s.core with repr := repr', min_clr := min_clr', tmp := tmp', flags := flags',
                              tmp_cnt := tc', tmp_len := tl' }
        scratch := sc' } :=
  ⟨⟨{ hinv.1.core_ok with repr_len := hr, min_clr_len_arr := hmc, tmp_len_arr := htmp,
                          flags_len := hfl, tmp_len_le := htl }, hsc⟩,
   fullWitnessInv_with_core_aux hinv.2.1,
   hinv.2.2.1, hinv.2.2.2.1,
   ⟨fun i hi => by dsimp only; rw [hll]; exact hinv.2.2.2.2.1.1 i hi,
    by dsimp only; rw [hext]; exact hinv.2.2.2.2.1.2⟩,
   hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

/-- `FullDenseInvW` without `FullLitMarksClear`, for helpers (`hop1`..`hop3`, `pick_cand`) that do
not read or modify `lit_mark` and are called while `full_bva_try_lit` holds bit-0 factor marks. -/
@[expose] def FullDenseInvNoLm (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64

theorem FullDenseInvW.toNoLm {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    (h : FullDenseInvW c F0 F_cur s) : FullDenseInvNoLm c F0 F_cur s :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fullDenseInvNoLm_with_core_aux {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvNoLm c F0 F_cur s)
    {repr' min_clr' tmp' flags' : List (BitVec 32)} {tc' tl' : Nat} {sc' : FullScratch}
    (hr : repr'.length = 2 * c.max_vars) (hmc : min_clr'.length = c.max_vars)
    (htmp : tmp'.length = c.max_vars) (hfl : flags'.length = c.max_vars)
    (htl : tl' ≤ c.max_vars) (hsc : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullDenseInvNoLm c F0 F_cur
      { core := { s.core with repr := repr', min_clr := min_clr', tmp := tmp', flags := flags',
                              tmp_cnt := tc', tmp_len := tl' }
        scratch := sc' } :=
  ⟨⟨{ hinv.1.core_ok with repr_len := hr, min_clr_len_arr := hmc, tmp_len_arr := htmp,
                          flags_len := hfl, tmp_len_le := htl }, hsc⟩,
   fullWitnessInv_with_core_aux hinv.2.1,
   hinv.2.2.1,
   ⟨fun i hi => by dsimp only; rw [hll]; exact hinv.2.2.2.1.1 i hi,
    by dsimp only; rw [hext]; exact hinv.2.2.2.1.2⟩,
   hinv.2.2.2.2.1, hinv.2.2.2.2.2⟩

/-- Pigeonhole permutation lemma for `full_bva_match_large`: if `R` and `D` are `Nodup`,
`f ∈ D`, `f ∉ R`, `D.length = R.length + 1`, and every element of `D` is either `f` or in `R`,
then `D` is a permutation of `f :: R` (so `D` and `f :: R` are semantically equivalent clauses). -/
theorem nodup_sublist_perm_of_length {α : Type} [DecidableEq α] :
    ∀ {xs ys : List α}, xs.Nodup → ys.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length = ys.length →
      xs.Perm ys
  | [], [], _, _, _, _ => List.Perm.nil
  | [], _ :: _, _, _, _, hlen => by simp at hlen
  | x :: xs, ys, hnx, hny, hsub, hlen => by
    have hx_mem : x ∈ ys := hsub x (by simp)
    have ⟨hx_notin, hnx'⟩ := List.nodup_cons.mp hnx
    have hperm_y : ys.Perm (x :: ys.erase x) := List.perm_cons_erase hx_mem
    have hny' : (ys.erase x).Nodup := (List.nodup_cons.mp (hny.perm hperm_y)).2
    have hlen' : xs.length = (ys.erase x).length := by
      have h1 := hperm_y.length_eq; simp only [List.length_cons] at h1 hlen; omega
    have hsub' : ∀ z ∈ xs, z ∈ ys.erase x := fun z hz => by
      have hzy : z ∈ ys := hsub z (by simp [hz])
      have hzx : z ≠ x := fun h => hx_notin (h ▸ hz)
      exact (List.mem_erase_of_ne hzx).mpr hzy
    exact (List.Perm.cons x (nodup_sublist_perm_of_length hnx' hny' hsub' hlen')).trans
      hperm_y.symm

theorem clause_entails_of_perm {F : CNF Nat} {C1 C2 : List Nat} (hp : C1.Perm C2)
    (h1 : F.EntailsClause (cnfClause C1)) : F.EntailsClause (cnfClause C2) := by
  rw [CNF.entails_clause_def] at h1 ⊢
  intro α hα
  have h1' := (clauseEvalVal_iff α C1).mpr (h1 α hα)
  rw [← clauseEvalVal_iff]
  simp only [clauseEvalVal, List.any_eq_true] at h1' ⊢
  obtain ⟨x, hx, hxt⟩ := h1'
  exact ⟨x, hp.subset hx, hxt⟩

theorem filter_ne_nodup_length {l : List Nat} {x : Nat} (hnd : l.Nodup) (hx : x ∈ l) :
    (l.filter (· != x)).length + 1 = l.length := by
  have hperm := (List.perm_cons_erase hx).filter (· != x)
  have he : (x :: l.erase x).filter (· != x) = l.erase x := by
    simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact List.filter_eq_self.mpr fun y hy => by
      have hne : y ≠ x := fun h => by
        subst h; exact (List.nodup_cons.mp (hnd.perm (List.perm_cons_erase hx))).1 hy
      simp [hne]
  rw [he] at hperm
  have h1 := hperm.length_eq
  have h2 := (List.perm_cons_erase hx).length_eq
  simp only [List.length_cons] at h2; omega

theorem bva_match_large_perm {R D : List Nat} {f : Nat}
    (hR_nd : R.Nodup) (hD_nd : D.Nodup) (hf_in : f ∈ D)
    (hlen : D.length = R.length + 1) (hsub : ∀ x ∈ D, x ≠ f → x ∈ R) :
    D.Perm (f :: R) ∧ (D.filter (· != f)).Perm R := by
  have hD'_nd : (D.filter (· != f)).Nodup := hD_nd.filter _
  have hD'_len : (D.filter (· != f)).length = R.length := by
    have := filter_ne_nodup_length hD_nd hf_in; omega
  have hD'_sub : ∀ x ∈ D.filter (· != f), x ∈ R := fun x hx => by
    simp only [List.mem_filter, bne_iff_ne, ne_eq] at hx
    exact hsub x hx.1 hx.2
  have hfilt : (D.filter (· != f)).Perm R :=
    nodup_sublist_perm_of_length hD'_nd hR_nd hD'_sub hD'_len
  have herase : (D.filter (· != f)).Perm (D.erase f) := by
    have hperm := (List.perm_cons_erase hf_in).filter (· != f)
    have he : (f :: D.erase f).filter (· != f) = D.erase f := by
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact List.filter_eq_self.mpr fun y hy => by
        have hne : y ≠ f := fun h => by
          subst h; exact (List.nodup_cons.mp (hD_nd.perm (List.perm_cons_erase hf_in))).1 hy
        simp [hne]
    rwa [he] at hperm
  have hD_perm : D.Perm (f :: R) :=
    (List.perm_cons_erase hf_in).trans ((herase.symm.trans hfilt).cons f)
  exact ⟨hD_perm, hfilt⟩

theorem bva_bin_swap_entails {F_cur : List (List Nat)} {a b : Nat}
    (h : (cnfOfClauses F_cur).EntailsClause (cnfClause [a, b])) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [b, a]) :=
  clause_entails_of_perm (List.Perm.swap b a []) h

theorem nodup_of_map_div2 {l : List Nat} (h : (l.map (· / 2)).Nodup) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    exact List.nodup_cons.mpr ⟨fun hx => h.1 ⟨x, hx, rfl⟩, ih h.2⟩

end FullBvaHeapHelpers

open FullBvaHeapHelpers

/-! ## 3. Specifications for All `13` `FullBvaHeap` Functions -/

/-- Stronger fresh-var spec preserving `tarjan_mark`, `tarjan_reach`, `sim_sig` alongside all
canonical `Full.fullInitFreshVarSpec` guarantees. -/
@[expose] def fullInitFreshVarHeapSpec : Spec [i64, i32] [] := fun (h, fv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ fv.toNat < s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ vals' mrk' flags' lvl' rsns' wvec' unass' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', mrk := mrk', flags := flags', lvl := lvl',
                                rsns := rsns', wvec := wvec', unassigned := unass' }
          scratch := sc' }
      s'.LengthsOk c → FullExtScratchPres s s' →
      sc'.scratch_buf = s.scratch.scratch_buf →
      sc'.wsort = s.scratch.wsort →
      sc'.tarjan_mark = s.scratch.tarjan_mark →
      sc'.tarjan_reach = s.scratch.tarjan_reach →
      sc'.sim_sig = s.scratch.sim_sig →
      vals'[2 * fv.toNat]?.getD 1#8 = 0#8 → vals'[2 * fv.toNat + 1]?.getD 1#8 = 0#8 →
      (∀ l < 2 * c.max_vars, l / 2 ≠ fv.toNat → vals'[l]? = s.core.vals[l]?) →
      mrk'[fv.toNat]?.getD 1#8 = 0#8 →
      (∀ v < c.max_vars, v ≠ fv.toNat → mrk'[v]? = s.core.mrk[v]?) →
      lvl'[fv.toNat]?.getD 1#32 = 0#32 →
      (∀ v < c.max_vars, v ≠ fv.toNat → lvl'[v]? = s.core.lvl[v]?) →
      rsns'[fv.toNat]?.getD 0#32 = 0xFFFFFFFF#32 →
      (∀ v < c.max_vars, v ≠ fv.toNat → rsns'[v]? = s.core.rsns[v]?) →
      (∀ k < 4, wvec'[4 * fv.toNat + k]?.getD 1#32 = 0#32) →
      (∀ i < 4 * c.max_vars, i / 4 ≠ fv.toNat → wvec'[i]? = s.core.wvec[i]?) →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose]
def fullBvaHop1Spec : Spec [i64, i32, i32] [i64] := fun (h, src_lit, _dst_idx, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvNoLm c F0 F_cur s ∧ src_lit.toNat < 2 * s.core.cur_vars ∧
    s.core.tmp_cnt ≤ s.core.cur_vars ∧
    (∀ i < s.core.tmp_cnt, (s.core.min_clr[i]?.getD 0#32).toNat < c.max_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) repr' mclr' tc' ant' m',
      let s' : FullState :=
        { core := { s.core with repr := repr', min_clr := mclr', tmp_cnt := tc' }
          scratch := { s.scratch with ant_sz := ant' } }
      FullDenseInvNoLm c F0 F_cur s' → tc' ≤ s.core.cur_vars →
      (∀ i < tc', (mclr'[i]?.getD 0#32).toNat < c.max_vars) →
      ant'.toNat ≤ s.scratch.ant_sz.toNat →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose]
def fullBvaHop2Spec : Spec [i64, i32, i32] [i64] := fun (h, src_lit, _dst_idx, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvNoLm c F0 F_cur s ∧ src_lit.toNat < 2 * s.core.cur_vars ∧
    s.core.tmp_cnt ≤ s.core.cur_vars ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
    (∀ i < s.core.tmp_cnt, (s.core.min_clr[i]?.getD 0#32).toNat < c.max_vars) ∧
    (∀ i < s.core.tmp_len, (s.scratch.shrink_stk[i]?.getD 0#32).toNat < c.max_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) repr' mclr' tc' tl' ant' sig' shrk' m',
      let s' : FullState :=
        { core := { s.core with repr := repr', min_clr := mclr', tmp_cnt := tc', tmp_len := tl' }
          scratch := { s.scratch with ant_sz := ant', sim_sig := sig', shrink_stk := shrk' } }
      FullDenseInvNoLm c F0 F_cur s' → tc' ≤ s.core.cur_vars → tl' ≤ s.core.cur_vars →
      (∀ i < tc', (mclr'[i]?.getD 0#32).toNat < c.max_vars) →
      (∀ i < tl', (shrk'[i]?.getD 0#32).toNat < c.max_vars) →
      ant'.toNat ≤ s.scratch.ant_sz.toNat →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose]
def fullBvaHop3Spec : Spec [i64, i32, i32] [i64] := fun (h, src_lit, _dst_idx, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvNoLm c F0 F_cur s ∧ src_lit.toNat < 2 * s.core.cur_vars ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) repr' mclr' ant' sig' shrk' m',
      let s' : FullState :=
        { core := { s.core with repr := repr', min_clr := mclr', tmp_cnt := 0, tmp_len := 0 }
          scratch := { s.scratch with ant_sz := ant', sim_sig := sig', shrink_stk := shrk' } }
      FullDenseInvNoLm c F0 F_cur s' → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullFheapUpSpec : Spec [i64, i64, i64, i32] [] :=
  fun (hp_ptr, ps_ptr, wvec_ptr, p, ()) m Q _ =>
    ∃ (nlits : Nat) (hp ps wvec : List (BitVec 32)) (R : Mem 64 → Prop),
      nlits ≤ hp.length ∧ nlits ≤ ps.length ∧ 2 * nlits ≤ wvec.length ∧ nlits < 2 ^ 30 ∧
      p.toNat < nlits ∧
      (∀ i ≤ p.toNat, (hp[i]?.getD 0#32).toNat < nlits) ∧
      (array (t := i32) hp_ptr hp ⋆ array (t := i32) ps_ptr ps ⋆
        array (t := i32) wvec_ptr wvec ⋆ R) m ∧
      ∀ hp' ps' m',
        hp'.length = hp.length → ps'.length = ps.length →
        (∀ i ≤ p.toNat, ∃ j ≤ p.toNat, hp'[i]? = hp[j]?) →
        (∀ i, p.toNat < i → hp'[i]? = hp[i]?) →
        (array (t := i32) hp_ptr hp' ⋆ array (t := i32) ps_ptr ps' ⋆
          array (t := i32) wvec_ptr wvec ⋆ R) m' → Q () m'

@[expose] def fullFheapDownSpec : Spec [i64, i64, i64, i32, i32] [] :=
  fun (hp_ptr, ps_ptr, wvec_ptr, p, n, ()) m Q _ =>
    ∃ (nlits : Nat) (hp ps wvec : List (BitVec 32)) (R : Mem 64 → Prop),
      nlits ≤ hp.length ∧ nlits ≤ ps.length ∧ 2 * nlits ≤ wvec.length ∧ nlits < 2 ^ 30 ∧
      p.toNat < n.toNat ∧ n.toNat ≤ nlits ∧
      (∀ i < n.toNat, (hp[i]?.getD 0#32).toNat < nlits) ∧
      (array (t := i32) hp_ptr hp ⋆ array (t := i32) ps_ptr ps ⋆
        array (t := i32) wvec_ptr wvec ⋆ R) m ∧
      ∀ hp' ps' m',
        hp'.length = hp.length → ps'.length = ps.length →
        (∀ i < n.toNat, ∃ j < n.toNat, hp'[i]? = hp[j]?) →
        (∀ i, n.toNat ≤ i → hp'[i]? = hp[i]?) →
        (array (t := i32) hp_ptr hp' ⋆ array (t := i32) ps_ptr ps' ⋆
          array (t := i32) wvec_ptr wvec ⋆ R) m' → Q () m'

/-- Soundness invariant for one entry `w` in BVA row `r` with factor literal `fr`:
either a binary watch word `w = PW_BIN_FLAG | q` with residue `[q]`, or a live irredundant size
`3..5` arena clause ref containing `fr` with residue `(lits w).filter (· != fr)`. -/
@[expose] def BvaRowEntryOk (F_cur : List (List Nat)) (s : FullState) (fr : Nat) (w : BitVec 32)
    (res : List Nat) : Prop :=
  if (w &&& 0x80000000#32) ≠ 0#32 then
    let q := (w &&& 0x7FFFFFFF#32).toNat
    q < 2 * s.core.cur_vars ∧ res = [q] ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [fr, q])
  else
    w.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s w.toNat = false ∧
    3 ≤ fullArenaClauseSize s w.toNat ∧ fullArenaClauseSize s w.toNat ≤ 5 ∧
    fr ∈ fullArenaClauseLits s w.toNat ∧
    res.Perm ((fullArenaClauseLits s w.toNat).filter (· != fr)) ∧
    (fullArenaClauseLits s w.toNat).Perm (fr :: res)

/-- Complete inductive invariant for the BVA scratch matrix over steps `0 ..< step` (`1 ≤ step`):
tracks `scr[0..step)` factor literals, `scr[16..16+step)` row lengths `2..64`, `scr[64+r*64+m]`
clauses, `scr[1088+r*64+m]` parent indices, and residue lists `res` whose full Cartesian product
with `scr[0..r]` is entailed by `F_cur`. -/
@[expose]
def BvaMatrixInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState) (step : Nat) : Prop :=
  2304 ≤ c.scratch_cap ∧ 1 ≤ step ∧ step ≤ 16 ∧
  (∀ r < step,
    let fr := (s.scratch.scratch_buf[r]?.getD 0#32).toNat
    let qn := (s.scratch.scratch_buf[16 + r]?.getD 0#32).toNat
    fr < 2 * s.core.cur_vars ∧ 2 ≤ qn ∧ qn ≤ 64 ∧
    ∀ m < qn, ∃ res : List Nat,
      (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
      BvaRowEntryOk F_cur s fr (s.scratch.scratch_buf[64 + r * 64 + m]?.getD 0#32) res ∧
      (∀ t ≤ r,
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res))) ∧
      (0 < r →
        let pi := (s.scratch.scratch_buf[1088 + r * 64 + m]?.getD 0#32).toNat
        pi < (s.scratch.scratch_buf[16 + (r - 1)]?.getD 0#32).toNat ∧
        BvaRowEntryOk F_cur s (s.scratch.scratch_buf[r - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[64 + (r - 1) * 64 + pi]?.getD 0#32) res))

@[expose] def fullBvaMatchLargeSpec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, cur_cr, next_lit, d_ref, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R_mem : Mem 64 → Prop) (R_set : List Nat),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧
      cur_cr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cur_cr.toNat = false ∧
      d_ref.toNat ∈ fullArenaClauseRefs s ∧
      R_set.Nodup ∧ (∀ x ∈ R_set, x < 2 * s.core.cur_vars) ∧
      fullArenaClauseSize s cur_cr.toNat = R_set.length + 1 ∧
      (∀ l < 2 * s.core.cur_vars,
        (s.core.lit_mark[l]?.getD 0#8 &&& 2#8) ≠ 0#8 → l ∈ R_set) ∧
      (FullMem c s ⋆ R_mem) m ∧
      ∀ ok : Bool,
        (ok = true →
          fullArenaClauseGarb s d_ref.toNat = false ∧
          (fullArenaHdr s d_ref.toNat &&& 0x00100000#32) = 0#32 ∧
          fullArenaClauseSize s d_ref.toNat = fullArenaClauseSize s cur_cr.toNat ∧
          next_lit.toNat ∈ fullArenaClauseLits s d_ref.toNat ∧
          (fullArenaClauseLits s d_ref.toNat).Perm (next_lit.toNat :: R_set) ∧
          ((fullArenaClauseLits s d_ref.toNat).filter (· != next_lit.toNat)).Perm R_set ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause (next_lit.toNat :: R_set))) →
        Q (ok, ()) m

@[expose] def fullBvaScanCandsSpec : Spec [i64, i32, i32, i64] [i32] :=
  fun (h, row_off, cur_qn, init_lits, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧
      s.core.dense_mode ≠ 0#64 ∧
      init_lits.toNat ≤ 2 * s.core.cur_vars ∧
      (∀ l < 2 * c.max_vars, (s.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
      row_off.toNat + cur_qn.toNat ≤ c.scratch_cap ∧ cur_qn.toNat ≤ 64 ∧
      (∀ qi < cur_qn.toNat,
        let w := s.scratch.scratch_buf[row_off.toNat + qi]?.getD 0#32
        if (w &&& 0x80000000#32) ≠ 0#32 then (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars
        else w.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s w.toNat = false) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ncntd : BitVec 32) wsort' ws1' ws2' m',
        let s' : FullState :=
          { s with scratch :=
            { s.scratch with wsort := wsort', work_stk1 := ws1', work_stk2 := ws2' } }
        s'.LengthsOk c →
        ncntd.toNat ≤ init_lits.toNat →
        (∀ i < ncntd.toNat, (ws1'[i]?.getD 0#32).toNat < init_lits.toNat) →
        (FullMem c s' ⋆ R) m' → Q (ncntd, ()) m'

@[expose] def fullBvaPickCandSpec : Spec [i64, i32, i32] [i32] :=
  fun (h, ncntd, f0, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvNoLm c F0 F_cur s ∧
      f0.toNat < 2 * s.core.cur_vars ∧ ncntd.toNat ≤ 2 * s.core.cur_vars ∧
      (∀ i < ncntd.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 32) repr' mclr' tc' tl' wsort' ant' sig' shrk' m',
        let s' : FullState :=
          { core := { s.core with repr := repr', min_clr := mclr', tmp_cnt := tc', tmp_len := tl' }
            scratch := { s.scratch with wsort := wsort', ant_sz := ant', sim_sig := sig',
                                        shrink_stk := shrk' } }
        FullDenseInvNoLm c F0 F_cur s' →
        (r = 0xFFFFFFFF#32 ∨ r.toNat < 2 * s.core.cur_vars) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullBvaFilterRowSpec : Spec [i64, i32, i32, i32, i32, i32] [i32] :=
  fun (h, row_off, nrow_off, par_off, cur_qn, best_lit, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop) (step : Nat),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧
      s.core.dense_mode ≠ 0#64 ∧
      1 ≤ step ∧ step < 16 ∧ 2304 ≤ c.scratch_cap ∧
      row_off.toNat = 64 + (step - 1) * 64 ∧
      nrow_off.toNat = 64 + step * 64 ∧
      par_off.toNat = 1088 + step * 64 ∧
      cur_qn.toNat = (s.scratch.scratch_buf[16 + (step - 1)]?.getD 0#32).toNat ∧
      best_lit.toNat < 2 * s.core.cur_vars ∧
      BvaMatrixInv c F_cur s step ∧
      (∀ l < 2 * c.max_vars, (s.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
      (∀ r < step, (s.core.lit_mark[(s.scratch.scratch_buf[r]?.getD 0#32).toNat]?.getD 0#8 &&&
        1#8) ≠ 0#8) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (new_qn : BitVec 32) sb' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := sb' } }
        s'.LengthsOk c → new_qn.toNat ≤ 64 →
        (∀ idx < c.scratch_cap,
          ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 64) →
          ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 64) →
          sb'[idx]? = s.scratch.scratch_buf[idx]?) →
        (∀ nm < new_qn.toNat,
          let pi := (sb'[par_off.toNat + nm]?.getD 0#32).toNat
          pi < cur_qn.toNat ∧
          ∃ res : List Nat,
            (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
            BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
              (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res ∧
            BvaRowEntryOk F_cur s best_lit.toNat (sb'[nrow_off.toNat + nm]?.getD 0#32) res ∧
            (∀ t < step, (cnfOfClauses F_cur).EntailsClause
              (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res))) ∧
            (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res))) →
        (FullMem c s' ⋆ R) m' → Q (new_qn, ()) m'

@[expose] def fullBvaCommitSpec : Spec [i64, i32] [.bool] := fun (h, best_k, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
    1 ≤ best_k.toNat ∧ best_k.toNat < 16 ∧
    BvaMatrixInv c F_cur s (best_k.toNat + 1) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose]
def fullBvaTryLitHeapSpec : Spec [i64, i32, i64] [.bool] := fun (h, f0, _init_cv, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ f0.toNat < 2 * s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullFactorHeapSpec : Spec [i64, i64] [i64] := fun (h, _budget, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars → s'.core.fuel = s.core.fuel →
      r = 1#64 → (FullMem c s' ⋆ R) m' → Q (r, ()) m'


end LeanQbe.T.Examples.Kissat.Proof.Spec
