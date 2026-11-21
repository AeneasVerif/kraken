module

public import LeanQbe.T.Examples.Kissat.FullKittenSpec1
public import LeanQbe.T.Examples.Kissat.CoreLemmas1

/-!
# Kissat `D-Full` Scratch `kitten` Helper Lemmas & Preservation Proofs (`Part 1`)

Provides pure and invariant-preservation lemmas for `FullKitten` (`Func.wp` proofs for the `6`
leaf helpers live in `FullKittenLemmas2.lean`):
1. Pure bitvector, list-swap permutation, `KittenCnfPermEquiv`, and `CNF` entailment helpers.
2. `FullState.LengthsOk` scratch helper, equality transport, `kittenState_ext`, and O(1)
   non-expanding `putHdr`/`putArr` projections (`kp_field`).
3. Semantic trail entailment (`kitten_trail_entails`), level-0 / assumption UNSAT refutation
   (`kitten_conflict_unsat_lvl0`, `kitten_conflict_unsat_assumps`,
   `kitten_falsified_assump_unsat`).
4. Structural invariant preservation for `watch`, `assign`, `mtf`, `backtrack`, `init`, and
   `add_clause`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

open scoped KittenMemTactics KittenMemATactics

/-! ## 1. Bitvector, List-Swap, `KittenCnfPermEquiv`, & CNF Helpers -/

theorem bv32_one_eq : (1 : BitVec 32) = 1#32 := rfl

theorem slab_drop_exact {α : Type _} (p s : List α) {k : Nat} (hk : p.length = k) :
    (p ++ s).drop k = s := by
  rw [List.drop_append_of_le_length (by omega), ← hk, List.drop_length, List.nil_append]

private theorem bv32_bit2_not_bit1 :
    ∀ j : Fin 32, (2#32 : BitVec 32)[j.1] = true → (1#32 : BitVec 32)[j.1] = false := by
  decide

theorem nat_xor1_cases (l : Nat) :
    (l = 2 * (l / 2) ∧ (l ^^^ 1) = 2 * (l / 2) + 1) ∨
    (l = 2 * (l / 2) + 1 ∧ (l ^^^ 1) = 2 * (l / 2)) := by
  have h := litNeg_eq l
  unfold litNeg at h
  rcases Nat.mod_two_eq_zero_or_one l with hm | hm
  · left; simp [hm] at h; omega
  · right; simp [hm] at h; omega

theorem bv32_lit_div2_bv {nv : Nat} {l : BitVec 32} (hl : l.toNat < 2 * nv) :
    (l >>> (1 : Nat)).toNat = l.toNat / 2 ∧ (l >>> (1 : Nat)).toNat < nv := by
  have h1 : (l >>> (1 : Nat)).toNat = l.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact ⟨h1, by omega⟩

theorem bv32_lit_div2_u {nv : Nat} {l : BitVec 32} (hl : l.toNat < 2 * nv) :
    (l >>> (1 : BitVec 32)).toNat = l.toNat / 2 ∧ (l >>> (1 : BitVec 32)).toNat < nv := by
  change (l >>> (1 : Nat)).toNat = l.toNat / 2 ∧ (l >>> (1 : Nat)).toNat < nv
  exact bv32_lit_div2_bv hl

theorem bv32_cid_w0 {nc : Nat} {cid : BitVec 32} (hc : cid.toNat < nc) (hnc : nc ≤ 896) :
    (cid <<< (1 : Nat)).toNat = 2 * cid.toNat ∧ (cid <<< (1 : Nat)).toNat < 2 * nc :=
  bv32_cid_to_w0_lt hc hnc

theorem bv32_cid_w1 {nc : Nat} {cid : BitVec 32} (hc : cid.toNat < nc) (hnc : nc ≤ 896) :
    ((cid <<< (1 : Nat)) ||| (1 : BitVec 32)).toNat = 2 * cid.toNat + 1 ∧
      ((cid <<< (1 : Nat)) ||| (1 : BitVec 32)).toNat < 2 * nc :=
  bv32_cid_to_w1_lt hc hnc

theorem litNeg_eq_xor1 (l : Nat) : l ^^^ 1 = litNeg l := rfl

theorem bv32_xor1_eq_litNeg {nv : Nat} {l : BitVec 32} (hl : l.toNat < 2 * nv) :
    (l ^^^ (1 : BitVec 32)).toNat = litNeg l.toNat ∧
      (l ^^^ (1 : BitVec 32)).toNat < 2 * nv := by
  have hlt := bv32_lit_xor1_lt hl
  have h1 : (l ^^^ 1#32).toNat = l.toNat ^^^ 1 := by simp
  rw [bv32_one_eq]; exact ⟨h1, hlt⟩

private theorem count_set_eq {α : Type} [BEq α] [LawfulBEq α] (xs : List α) {i : Nat}
    (hi : i < xs.length) (v a : α) :
    (xs.set i v).count a + (if xs[i] == a then 1 else 0) =
      xs.count a + (if v == a then 1 else 0) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x tl ih =>
    cases i with
    | zero => simp [List.count_cons]; omega
    | succ i' =>
      simp only [List.set_cons_succ, List.count_cons, List.getElem_cons_succ]
      have := ih (i := i') (by simp at hi; omega)
      omega

theorem list_swap_perm {α : Type} [BEq α] [LawfulBEq α] (xs : List α) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    ((xs.set i xs[j]).set j xs[i]).Perm xs := by
  rw [List.perm_iff_count]; intro a
  have h1 := count_set_eq xs hi xs[j] a
  have h2 := count_set_eq (xs.set i xs[j]) (i := j) (by simp [hj]) xs[i] a
  by_cases hij : i = j
  · subst hij; simp only [List.getElem_set_self] at h2; omega
  · simp only [List.getElem_set_ne hij] at h2; omega

theorem drop_take_set_swap {α : Type} [BEq α] [LawfulBEq α] (xs : List α) {off sz p q : Nat}
    (hp : p < sz) (hq : q < sz) (hbd : off + sz ≤ xs.length) :
    (((xs.set (off + p) (xs[off + q]'(by omega))).set (off + q)
        (xs[off + p]'(by omega))).drop off |>.take sz).Perm ((xs.drop off).take sz) := by
  have hlen : ((xs.drop off).take sz).length = sz := by simp; omega
  have hp_lt : off + p < xs.length := by omega
  have hq_lt : off + q < xs.length := by omega
  have h1 : (((xs.set (off + p) (xs[off + q]'hq_lt)).set (off + q)
      (xs[off + p]'hp_lt)).drop off).take sz =
      (((xs.drop off).take sz).set p (((xs.drop off).take sz)[q]'(by omega))).set q
        (((xs.drop off).take sz)[p]'(by omega)) := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < sz
    · have hlenL :
          (((xs.set (off + p) xs[off + q]).set (off + q) xs[off + p]).drop off).length =
            xs.length - off := by simp
      have hlen1 : k < xs.length - off := by omega
      have hk_take1 : k < (((xs.set (off + p) xs[off + q]).set (off + q) xs[off + p]).drop off
          |>.take sz).length := by simp [hlenL]; omega
      have hk_take2 : k < ((((xs.drop off).take sz).set p ((xs.drop off).take sz)[q]).set q
          ((xs.drop off).take sz)[p]).length := by simp [hlen]; exact hk
      rw [List.getElem?_eq_getElem hk_take1, List.getElem?_eq_getElem hk_take2]
      simp only [List.getElem_take, List.getElem_drop, Option.some.injEq]
      by_cases hkq : k = q
      · subst hkq
        rw [List.getElem_set_self (by simp; omega),
          List.getElem_set_self (by simp [hlen, hq])]
      · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (Ne.symm hkq)]
        by_cases hkp : k = p
        · subst hkp
          rw [List.getElem_set_self (by simp; omega),
            List.getElem_set_self (by simp [hlen, hp])]
        · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (Ne.symm hkp)]
          simp [List.getElem_take, List.getElem_drop]
    · have hk1 : (((xs.set (off + p) xs[off + q]).set (off + q) xs[off + p]).drop off
          |>.take sz).length ≤ k := by simp; omega
      have hk2 : ((((xs.drop off).take sz).set p ((xs.drop off).take sz)[q]).set q
          ((xs.drop off).take sz)[p]).length ≤ k := by simp [hlen]; omega
      rw [List.getElem?_eq_none hk1, List.getElem?_eq_none hk2]
  rw [h1]
  exact list_swap_perm ((xs.drop off).take sz) (by omega) (by omega)

theorem drop_take_set_out {α : Type} (xs : List α) {off sz idx : Nat} (v : α)
    (hout : idx < off ∨ off + sz ≤ idx) :
    ((xs.set idx v).drop off).take sz = (xs.drop off).take sz := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop, List.length_set]
  · intro k hk1 hk2
    have hkd : k < sz ∧ off + k < xs.length := by simp at hk1; omega
    simp only [List.getElem_take, List.getElem_drop]
    rw [List.getElem_set_ne (by omega)]

theorem list_take_set_out {α : Type} (xs : List α) {n idx : Nat} (v : α) (hn : n ≤ idx) :
    (xs.set idx v).take n = xs.take n := by
  simpa using drop_take_set_out xs (off := 0) (sz := n) (idx := idx) v (Or.inr (by omega))

theorem KittenCnfPermEquiv.refl (F : List (List Nat)) : KittenCnfPermEquiv F F :=
  ⟨rfl, fun _ _ => List.Perm.refl _⟩

theorem KittenCnfPermEquiv.symm {F1 F2 : List (List Nat)} (h : KittenCnfPermEquiv F1 F2) :
    KittenCnfPermEquiv F2 F1 :=
  ⟨h.1.symm, fun i hi => (h.2 i (h.1 ▸ hi)).symm⟩

theorem KittenCnfPermEquiv.trans {F1 F2 F3 : List (List Nat)}
    (h12 : KittenCnfPermEquiv F1 F2) (h23 : KittenCnfPermEquiv F2 F3) :
    KittenCnfPermEquiv F1 F3 :=
  ⟨h12.1.trans h23.1, fun i hi => (h12.2 i hi).trans (h23.2 i (h12.1 ▸ hi))⟩

theorem cnfClause_sat_perm (α : Nat → Bool) {c1 c2 : List Nat} (hp : c1.Perm c2) :
    (cnfClause c1).Sat α ↔ (cnfClause c2).Sat α := by
  simp only [clause_sat_cnfClause_iff]
  constructor
  · rintro ⟨l, hl, hs⟩; exact ⟨l, hp.mem_iff.mp hl, hs⟩
  · rintro ⟨l, hl, hs⟩; exact ⟨l, hp.mem_iff.mpr hl, hs⟩

theorem KittenCnfPermEquiv.sat_iff {F1 F2 : List (List Nat)}
    (h : KittenCnfPermEquiv F1 F2) (α : Nat → Bool) :
    (cnfOfClauses F1).Sat α ↔ (cnfOfClauses F2).Sat α := by
  simp only [cnf_sat_cnfOfClauses_iff]
  constructor
  · intro hs c hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have hi1 : i < F1.length := h.1.symm ▸ hi
    have hpe : F1[i].Perm F2[i] := by
      have hp := h.2 i hi1
      simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi1,
        List.getElem?_eq_getElem hi] using hp
    exact (cnfClause_sat_perm α hpe).mp (hs _ (List.getElem_mem hi1))
  · intro hs c hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have hi2 : i < F2.length := h.1 ▸ hi
    have hpe : F1[i].Perm F2[i] := by
      have hp := h.2 i hi
      simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem hi2] using hp
    exact (cnfClause_sat_perm α hpe).mpr (hs _ (List.getElem_mem hi2))

theorem KittenCnfPermEquiv.entailsClause {F1 F2 : List (List Nat)}
    (h : KittenCnfPermEquiv F1 F2) {c : CNF.Clause Nat}
    (he : (cnfOfClauses F1).EntailsClause c) : (cnfOfClauses F2).EntailsClause c := by
  rw [CNF.entails_clause_def] at he ⊢
  intro α hα; exact he α ((h.sat_iff α).mpr hα)

theorem KittenCnfPermEquiv.unsat_iff {F1 F2 : List (List Nat)}
    (h : KittenCnfPermEquiv F1 F2) (cs : CNF Nat) :
    (cnfOfClauses F1 ++ cs).Unsat ↔ (cnfOfClauses F2 ++ cs).Unsat := by
  simp only [CNF.unsat_iff_not_sat, CNF.sat_append, h.sat_iff]

theorem cnfOfClauses_append (F1 F2 : List (List Nat)) (α : Nat → Bool) :
    (cnfOfClauses (F1 ++ F2)).Sat α ↔ (cnfOfClauses F1).Sat α ∧ (cnfOfClauses F2).Sat α := by
  simp only [cnf_sat_cnfOfClauses_iff, List.mem_append]
  exact ⟨fun h => ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩,
    fun ⟨h1, h2⟩ c hc => hc.elim (h1 c) (h2 c)⟩

theorem cnfOfClauses_entailsClause_append_left {F1 F2 : List (List Nat)} {c : CNF.Clause Nat}
    (h : (cnfOfClauses F1).EntailsClause c) : (cnfOfClauses (F1 ++ F2)).EntailsClause c := by
  rw [CNF.entails_clause_def] at h ⊢
  intro α hα; exact h α ((cnfOfClauses_append F1 F2 α).mp hα).1

theorem cnfOfClauses_entailsClause_of_mem {F : List (List Nat)} {c : List Nat} (hc : c ∈ F) :
    (cnfOfClauses F).EntailsClause (cnfClause c) := by
  rw [CNF.entails_clause_def]
  intro α hα; exact (cnf_sat_cnfOfClauses_iff α F).mp hα c hc

theorem cnfOfClauses_unsat_append_left {F1 : List (List Nat)} (F2 : CNF Nat)
    (h : (cnfOfClauses F1).Unsat) : (cnfOfClauses F1 ++ F2).Unsat := by
  rw [CNF.unsat_iff_not_sat] at h ⊢
  intro α hα; exact h α (CNF.sat_append.mp hα).1

theorem cnfOfClauses_unsat_sublist {F1 F2 : List (List Nat)}
    (hsub : ∀ c ∈ F1, c ∈ F2) (h : (cnfOfClauses F1).Unsat) : (cnfOfClauses F2).Unsat := by
  rw [CNF.unsat_iff_not_sat] at h ⊢
  intro α hα
  apply h
  rw [cnf_sat_cnfOfClauses_iff] at hα ⊢
  exact fun c hc => hα c (hsub c hc)

theorem cnfOfClauses_entailsClause_of_core_eq {F1 F2 : List (List Nat)}
    (heq : F1 = F2) {c : CNF.Clause Nat} (h : (cnfOfClauses F1).EntailsClause c) :
    (cnfOfClauses F2).EntailsClause c := heq ▸ h

/-! ## 2. `FullState.LengthsOk`, Transport Helpers, & `KittenState` O(1) Projections -/

theorem fullState_lengthsOk_scratch {c : FullCfg} {s : FullState} {scr' : List (BitVec 32)}
    (hlen : s.LengthsOk c) (hscr : scr'.length = c.scratch_cap) :
    ({ s with scratch := { s.scratch with scratch_buf := scr' } } : FullState).LengthsOk c := by
  have hs := hlen.scratch_ok
  exact ⟨hlen.core_ok, { hs with scratch_buf_len := hscr }⟩

theorem kittenOrigClauses_eq_of {ks1 ks2 : KittenState}
    (hnc : ks1.orig_nc = ks2.orig_nc)
    (hcl : ∀ i < ks1.orig_nc.toNat, kittenClauseLits ks1 i = kittenClauseLits ks2 i) :
    kittenOrigClauses ks1 = kittenOrigClauses ks2 := by
  unfold kittenOrigClauses; rw [hnc]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range, ← hnc] at hi
  exact hcl i hi

theorem kittenAssumpLits_eq_of {ks1 ks2 : KittenState}
    (hl1 : ks1.nassump.toNat ≤ ks1.assump.length)
    (hl2 : ks2.nassump.toNat ≤ ks2.assump.length)
    (hna : ks1.nassump = ks2.nassump)
    (hass : ∀ i < ks1.nassump.toNat, ks1.assump[i]? = ks2.assump[i]?) :
    kittenAssumpLits ks1 = kittenAssumpLits ks2 := by
  unfold kittenAssumpLits
  congr 1
  apply List.ext_getElem
  · rw [List.length_take, List.length_take, Nat.min_eq_left hl1, Nat.min_eq_left hl2, hna]
  · intro i hi1 hi2
    have hlt1 : i < ks1.nassump.toNat := by simp at hi1; omega
    have h1 : i < ks1.assump.length := by simp at hi1; omega
    have h2 : i < ks2.assump.length := by simp at hi2; omega
    simp only [List.getElem_take]
    have hg := hass i hlt1
    rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at hg
    exact Option.some.inj hg

theorem mem_kittenTrailLits_of_lt {ks : KittenState} {i : Nat}
    (hi : i < ks.trl_end.toNat) (hle : ks.trl_end.toNat ≤ ks.trl.length) :
    (ks.trl[i]?.getD 0#32).toNat ∈ kittenTrailLits ks := by
  unfold kittenTrailLits
  rw [List.mem_map]
  refine ⟨ks.trl[i]'(by omega), ?_, ?_⟩
  · rw [List.mem_iff_getElem]
    exact ⟨i, by simp [List.length_take]; omega, by simp⟩
  · simp [List.getElem?_eq_getElem (by omega : i < ks.trl.length)]

theorem mem_kittenTrailDecisions_iff {ks : KittenState} {d : Nat}
    (hle : ks.trl_end.toNat ≤ ks.trl.length) :
    d ∈ kittenTrailDecisions ks ↔
      ∃ i < ks.trl_end.toNat,
        (ks.trl[i]?.getD 0#32).toNat = d ∧
        ks.rsn[d / 2]?.getD 0#32 = 0xFFFFFFFF#32 := by
  unfold kittenTrailDecisions
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨l, hl, hif⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    have hlt : i < ks.trl_end.toNat := by simp at hi; omega
    simp only [List.getElem_take] at hif
    have h1 : i < ks.trl.length := by omega
    split at hif
    · rename_i hrs
      simp only [Option.some.injEq] at hif
      refine ⟨i, hlt, ?_, ?_⟩
      · rw [List.getElem?_eq_getElem h1, Option.getD_some]; exact hif
      · rw [← hif]; exact hrs
    · simp at hif
  · rintro ⟨i, hi, hteq, hrs⟩
    have h1 : i < ks.trl.length := by omega
    refine ⟨ks.trl[i], ?_, ?_⟩
    · rw [List.mem_iff_getElem]
      exact ⟨i, by simp [List.length_take]; omega, by simp⟩
    · rw [List.getElem?_eq_getElem h1, Option.getD_some] at hteq
      rw [hteq]
      simp [hrs]

private theorem list_filterMap_congr_mem {α β : Type} {xs : List α} {f g : α → Option β}
    (h : ∀ x ∈ xs, f x = g x) : xs.filterMap f = xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.filterMap_cons, h x List.mem_cons_self]
    rw [ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem kittenTrailDecisions_eq_of_trl {ks1 ks2 : KittenState}
    (hle1 : ks1.trl_end.toNat ≤ ks1.trl.length) (hle2 : ks2.trl_end.toNat ≤ ks2.trl.length)
    (hte : ks1.trl_end = ks2.trl_end)
    (htrl : ∀ i < ks1.trl_end.toNat,
      ks1.trl[i]? = ks2.trl[i]? ∧
      ks1.rsn[(ks1.trl[i]?.getD 0#32).toNat / 2]? =
        ks2.rsn[(ks1.trl[i]?.getD 0#32).toNat / 2]?) :
    kittenTrailDecisions ks1 = kittenTrailDecisions ks2 := by
  unfold kittenTrailDecisions
  have hmap1 : ks1.trl.take ks1.trl_end.toNat =
      (List.range ks1.trl_end.toNat).map (fun i => ks1.trl[i]?.getD 0#32) := by
    apply List.ext_getElem (by simp [List.length_take]; omega)
    intro i hi1 hi2
    have hlt : i < ks1.trl_end.toNat := by simp at hi2; exact hi2
    simp only [List.getElem_take, List.getElem_map, List.getElem_range]
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hmap2 : ks2.trl.take ks2.trl_end.toNat =
      (List.range ks2.trl_end.toNat).map (fun i => ks2.trl[i]?.getD 0#32) := by
    apply List.ext_getElem (by simp [List.length_take]; omega)
    intro i hi1 hi2
    have hlt : i < ks2.trl_end.toNat := by simp at hi2; exact hi2
    simp only [List.getElem_take, List.getElem_map, List.getElem_range]
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  rw [hmap1, hmap2, ← hte, List.filterMap_map, List.filterMap_map]
  refine list_filterMap_congr_mem fun i hi => ?_
  rw [List.mem_range] at hi
  have ht := htrl i hi
  have hr : ks1.rsn[(ks2.trl[i]?.getD 0#32).toNat / 2]? =
      ks2.rsn[(ks2.trl[i]?.getD 0#32).toNat / 2]? := by
    rw [← ht.1]; exact ht.2
  simp only [Function.comp_def, ht.1, hr]

theorem kittenState_ext {a b : KittenState}
    (h1 : a.nv = b.nv) (h2 : a.nc = b.nc) (h3 : a.orig_nc = b.orig_nc)
    (h4 : a.lvl = b.lvl) (h5 : a.prop = b.prop) (h6 : a.trl_end = b.trl_end)
    (h7 : a.unass = b.unass) (h8 : a.incons = b.incons) (h9 : a.failing = b.failing)
    (h10 : a.ante = b.ante) (h11 : a.qfirst = b.qfirst) (h12 : a.qlast = b.qlast)
    (h13 : a.qsearch = b.qsearch) (h14 : a.qstamp = b.qstamp) (h15 : a.ticks = b.ticks)
    (h16 : a.tick_lim = b.tick_lim) (h17 : a.alen = b.alen) (h18 : a.acap = b.acap)
    (h19 : a.nassump = b.nassump) (h20 : a.nunits = b.nunits) (h21 : a.nres = b.nres)
    (h22 : a.nkl = b.nkl) (h23 : a.nana = b.nana) (h24 : a.status = b.status)
    (h25 : a.phase = b.phase) (h26 : a.hdrTail = b.hdrTail)
    (h27 : a.lvlArr = b.lvlArr) (h28 : a.rsn = b.rsn) (h29 : a.qprev = b.qprev)
    (h30 : a.qnext = b.qnext) (h31 : a.qstampArr = b.qstampArr) (h32 : a.trl = b.trl)
    (h33 : a.flags = b.flags) (h34 : a.vals = b.vals) (h35 : a.assump = b.assump)
    (h36 : a.ana = b.ana) (h37 : a.kl = b.kl) (h38 : a.units = b.units)
    (h39 : a.res = b.res) (h40 : a.whead = b.whead) (h41 : a.wnext = b.wnext)
    (h42 : a.wblit = b.wblit) (h43 : a.clOff = b.clOff) (h44 : a.clMeta = b.clMeta)
    (h45 : a.clAux = b.clAux) (h46 : a.arena = b.arena) : a = b := by
  cases a; cases b
  simp only [KittenState.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36,
    h37, h38, h39, h40, h41, h42, h43, h44, h45, h46⟩

theorem putHdr_nv (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).nv = if f = .nv then v else ks.nv := by cases f <;> rfl
theorem putHdr_nc (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).nc = if f = .nc then v else ks.nc := by cases f <;> rfl
theorem putHdr_orig_nc (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).orig_nc = if f = .orig_nc then v else ks.orig_nc := by cases f <;> rfl
theorem putHdr_lvl (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).lvl = if f = .lvl then v else ks.lvl := by cases f <;> rfl
theorem putHdr_prop (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).prop = if f = .prop then v else ks.prop := by cases f <;> rfl
theorem putHdr_trl_end (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).trl_end = if f = .trl_end then v else ks.trl_end := by cases f <;> rfl
theorem putHdr_unass (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).unass = if f = .unass then v else ks.unass := by cases f <;> rfl
theorem putHdr_incons (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).incons = if f = .incons then v else ks.incons := by cases f <;> rfl
theorem putHdr_failing (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).failing = if f = .failing then v else ks.failing := by cases f <;> rfl
theorem putHdr_ante (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).ante = if f = .ante then v else ks.ante := by cases f <;> rfl
theorem putHdr_qfirst (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).qfirst = if f = .qfirst then v else ks.qfirst := by cases f <;> rfl
theorem putHdr_qlast (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).qlast = if f = .qlast then v else ks.qlast := by cases f <;> rfl
theorem putHdr_qsearch (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).qsearch = if f = .qsearch then v else ks.qsearch := by cases f <;> rfl
theorem putHdr_qstamp (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).qstamp = if f = .qstamp then v else ks.qstamp := by cases f <;> rfl
theorem putHdr_ticks (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).ticks = if f = .ticks then v else ks.ticks := by cases f <;> rfl
theorem putHdr_tick_lim (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).tick_lim = if f = .tick_lim then v else ks.tick_lim := by cases f <;> rfl
theorem putHdr_alen (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).alen = if f = .alen then v else ks.alen := by cases f <;> rfl
theorem putHdr_acap (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).acap = if f = .acap then v else ks.acap := by cases f <;> rfl
theorem putHdr_nassump (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).nassump = if f = .nassump then v else ks.nassump := by cases f <;> rfl
theorem putHdr_nunits (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).nunits = if f = .nunits then v else ks.nunits := by cases f <;> rfl
theorem putHdr_nres (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).nres = if f = .nres then v else ks.nres := by cases f <;> rfl
theorem putHdr_nkl (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).nkl = if f = .nkl then v else ks.nkl := by cases f <;> rfl
theorem putHdr_nana (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).nana = if f = .nana then v else ks.nana := by cases f <;> rfl
theorem putHdr_status (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).status = if f = .status then v else ks.status := by cases f <;> rfl
theorem putHdr_phase (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).phase = if f = .phase then v else ks.phase := by cases f <;> rfl
theorem putHdr_hdrTail (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).hdrTail = ks.hdrTail := by cases f <;> rfl
theorem putArr_hdrTail (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).hdrTail = ks.hdrTail := by cases f <;> rfl
theorem putArr_lvlArr (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).lvlArr =
      if f = .lvlArr then ks.lvlArr.set i v else ks.lvlArr := by cases f <;> rfl
theorem putArr_rsn (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).rsn =
      if f = .rsn then ks.rsn.set i v else ks.rsn := by cases f <;> rfl
theorem putArr_qprev (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).qprev =
      if f = .qprev then ks.qprev.set i v else ks.qprev := by cases f <;> rfl
theorem putArr_qnext (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).qnext =
      if f = .qnext then ks.qnext.set i v else ks.qnext := by cases f <;> rfl
theorem putArr_qstampArr (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).qstampArr =
      if f = .qstampArr then ks.qstampArr.set i v else ks.qstampArr := by cases f <;> rfl
theorem putArr_trl (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).trl =
      if f = .trl then ks.trl.set i v else ks.trl := by cases f <;> rfl
theorem putArr_flags (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).flags =
      if f = .flags then ks.flags.set i v else ks.flags := by cases f <;> rfl
theorem putArr_vals (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).vals =
      if f = .vals then ks.vals.set i v else ks.vals := by cases f <;> rfl
theorem putArr_assump (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).assump =
      if f = .assump then ks.assump.set i v else ks.assump := by cases f <;> rfl
theorem putArr_ana (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).ana =
      if f = .ana then ks.ana.set i v else ks.ana := by cases f <;> rfl
theorem putArr_kl (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).kl =
      if f = .kl then ks.kl.set i v else ks.kl := by cases f <;> rfl
theorem putArr_units (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).units =
      if f = .units then ks.units.set i v else ks.units := by cases f <;> rfl
theorem putArr_res (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).res =
      if f = .res then ks.res.set i v else ks.res := by cases f <;> rfl
theorem putArr_whead (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).whead =
      if f = .whead then ks.whead.set i v else ks.whead := by cases f <;> rfl
theorem putArr_wnext (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).wnext =
      if f = .wnext then ks.wnext.set i v else ks.wnext := by cases f <;> rfl
theorem putArr_wblit (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).wblit =
      if f = .wblit then ks.wblit.set i v else ks.wblit := by cases f <;> rfl
theorem putArr_clOff (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).clOff =
      if f = .clOff then ks.clOff.set i v else ks.clOff := by cases f <;> rfl
theorem putArr_clMeta (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).clMeta =
      if f = .clMeta then ks.clMeta.set i v else ks.clMeta := by cases f <;> rfl
theorem putArr_clAux (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).clAux =
      if f = .clAux then ks.clAux.set i v else ks.clAux := by cases f <;> rfl
theorem putArr_arena (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).arena =
      if f = .arena then ks.arena.set i v else ks.arena := by cases f <;> rfl

namespace KittenProjTactics

scoped macro "kp_field" : tactic => `(tactic|
  simp only [
    putHdr_nv, putHdr_nc, putHdr_orig_nc, putHdr_lvl, putHdr_prop, putHdr_trl_end,
    putHdr_unass, putHdr_incons, putHdr_failing, putHdr_ante, putHdr_qfirst, putHdr_qlast,
    putHdr_qsearch, putHdr_qstamp, putHdr_ticks, putHdr_tick_lim, putHdr_alen, putHdr_acap,
    putHdr_nassump, putHdr_nunits, putHdr_nres, putHdr_nkl, putHdr_nana, putHdr_status,
    putHdr_phase, putHdr_hdrTail, putArr_hdrTail,
    putArr_lvlArr, putArr_rsn, putArr_qprev, putArr_qnext, putArr_qstampArr, putArr_trl,
    putArr_flags, putArr_vals, putArr_assump, putArr_ana, putArr_kl, putArr_units,
    putArr_res, putArr_whead, putArr_wnext, putArr_wblit, putArr_clOff, putArr_clMeta,
    putArr_clAux, putArr_arena,
    KittenMemTactics.putArr_nv, KittenMemTactics.putArr_nc, KittenMemTactics.putArr_orig_nc,
    KittenMemTactics.putArr_lvl, KittenMemTactics.putArr_prop, KittenMemTactics.putArr_trl_end,
    KittenMemTactics.putArr_unass, KittenMemTactics.putArr_incons,
    KittenMemTactics.putArr_failing, KittenMemTactics.putArr_ante, KittenMemTactics.putArr_qfirst,
    KittenMemTactics.putArr_qlast, KittenMemTactics.putArr_qsearch, KittenMemTactics.putArr_qstamp,
    KittenMemTactics.putArr_ticks, KittenMemTactics.putArr_tick_lim, KittenMemTactics.putArr_alen,
    KittenMemTactics.putArr_acap, KittenMemTactics.putArr_nassump, KittenMemTactics.putArr_nunits,
    KittenMemTactics.putArr_nres, KittenMemTactics.putArr_nkl, KittenMemTactics.putArr_nana,
    KittenMemTactics.putArr_status, KittenMemTactics.putArr_phase,
    KittenMemTactics.putHdr_lvlArr, KittenMemTactics.putHdr_rsn, KittenMemTactics.putHdr_qprev,
    KittenMemTactics.putHdr_qnext, KittenMemTactics.putHdr_qstampArr, KittenMemTactics.putHdr_trl,
    KittenMemTactics.putHdr_flags, KittenMemTactics.putHdr_vals, KittenMemTactics.putHdr_assump,
    KittenMemTactics.putHdr_ana, KittenMemTactics.putHdr_kl, KittenMemTactics.putHdr_units,
    KittenMemTactics.putHdr_res, KittenMemTactics.putHdr_whead, KittenMemTactics.putHdr_wnext,
    KittenMemTactics.putHdr_wblit, KittenMemTactics.putHdr_clOff, KittenMemTactics.putHdr_clMeta,
    KittenMemTactics.putHdr_clAux, KittenMemTactics.putHdr_arena,
    eq_self, reduceCtorEq, ite_true, ite_false])

scoped macro "kstate_ext" : tactic => `(tactic| (apply kittenState_ext <;> kp_field))

end KittenProjTactics

open scoped KittenProjTactics

/-! ## 3. Semantic Trail Entailment & UNSAT Refutation -/

/-- Every literal `trl[i]` on the `kitten` trail is entailed by `orig ++ unitsCnf (decisions)`. -/
theorem kitten_trail_entails {acap : Nat} {ks : KittenState}
    (hsh : ks.ShapesOk acap) (hcl : KittenClausesOk acap ks)
    (hba : KittenBaseAssignOk ks) (hrsn : ReasonOk ks) :
    ∀ i < ks.trl_end.toNat,
      (cnfOfClauses (kittenOrigClauses ks) ++ unitsCnf (kittenTrailDecisions ks)).EntailsClause
        (cnfClause [(ks.trl[i]?.getD 0#32).toNat]) := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi
    have hte_len : ks.trl_end.toNat ≤ ks.trl.length := by
      rw [hsh.trl_len]; exact Nat.le_trans hba.trl_end_le hcl.nv_le
    have hro := hrsn i hi
    dsimp only at hro
    let l := (ks.trl[i]?.getD 0#32).toNat
    let r := ks.rsn[l / 2]?.getD 0#32
    rcases hro with hr_dec | ⟨hr_lt, hl_mem, hall⟩
    · refine CNF.entails_clause_def.mpr fun α hα => ?_
      rw [CNF.sat_append, sat_unitsCnf_iff] at hα
      exact hα.2 l ((mem_kittenTrailDecisions_iff hte_len).mpr ⟨i, hi, rfl, hr_dec⟩)
    · have hc_ent := (hcl.cl_wf r.toNat hr_lt).2.2.2.2.1
      refine CNF.entails_clause_def.mpr fun α hα => ?_
      have hα_orig := (CNF.sat_append.mp hα).1
      obtain ⟨x, hx_mem, hsat⟩ := (clause_sat_cnfClause_iff α (kittenClauseLits ks r.toNat)).mp
        (CNF.entails_clause_def.mp hc_ent α hα_orig)
      by_cases hxl : x = l
      · rw [hxl] at hsat; exact (sat_cnfClause_singleton α l).mpr hsat
      · obtain ⟨j, hj_lt, hj_eq⟩ := hall x hx_mem hxl
        have hent_j := ih j hj_lt (Nat.lt_trans hj_lt hi)
        have hent_neg : (cnfOfClauses (kittenOrigClauses ks) ++
            unitsCnf (kittenTrailDecisions ks)).EntailsClause (cnfClause [litNeg x]) := by
          simpa [hj_eq, litNeg_eq_xor1] using hent_j
        have hneg_sat := CNF.entails_clause_def.mp hent_neg α hα
        exact absurd ((sat_cnfClause_singleton α x).mpr hsat)
          ((sat_cnfClause_litNeg_iff α x).mp hneg_sat)

theorem kitten_trail_entails_with_assumps {acap : Nat} {ks : KittenState}
    (hsh : ks.ShapesOk acap) (hcl : KittenClausesOk acap ks)
    (hba : KittenBaseAssignOk ks) (hrsn : ReasonOk ks)
    (hdec : KittenAllDecisionsInAssumps ks) :
    ∀ i < ks.trl_end.toNat,
      (cnfOfClauses (kittenOrigClauses ks) ++ unitsCnf (kittenAssumpLits ks)).EntailsClause
        (cnfClause [(ks.trl[i]?.getD 0#32).toNat]) := by
  intro i hi
  have hent := kitten_trail_entails hsh hcl hba hrsn i hi
  refine CNF.entails_clause_def.mpr fun α hα => ?_
  rw [CNF.sat_append, sat_unitsCnf_iff] at hα
  apply CNF.entails_clause_def.mp hent α
  rw [CNF.sat_append, sat_unitsCnf_iff]
  exact ⟨hα.1, fun d hd => hα.2 d (hdec d hd)⟩

theorem kitten_falsified_to_trail {acap : Nat} {ks : KittenState}
    (hsh : ks.ShapesOk acap) (hnv : ks.nv.toNat ≤ kMaxV)
    (hba : KittenBaseAssignOk ks) (hsync : KittenTrailSynced ks)
    {l : Nat} (hl_lt : l < 2 * ks.nv.toNat) (hval : ks.vals[l]? = some 2#32) :
    ∃ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat = litNeg l := by
  have h1 : ks.vals[l]?.getD 0#32 ≠ 0#32 := by simp [hval]
  obtain ⟨i, hi, hveq⟩ := (hba.vals_nz_iff_trl l hl_lt).mp h1
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hsh.trl_len]; have := hba.trl_end_le; unfold kMaxV at hnv; omega
  let tl := (ks.trl[i]?.getD 0#32).toNat
  have htl_lt : tl < 2 * ks.nv.toNat := hba.trl_lt tl (mem_kittenTrailLits_of_lt hi htrl_len)
  have hs := hsync i hi
  dsimp only at hs
  change ks.vals[tl]? = some 1#32 ∧ ks.vals[tl ^^^ 1]? = some 2#32 at hs
  rcases (litVar_eq_iff tl l).mp (by simpa [litVar] using hveq) with heq | heq
  · rw [heq, hval] at hs; cases hs.1
  · exact ⟨i, hi, heq⟩

/-- Level-0 falsified clause refutes `kittenOrigClauses ks` alone. -/
theorem kitten_conflict_unsat_lvl0 {acap : Nat} {ks : KittenState}
    (hsh : ks.ShapesOk acap) (hcl : KittenClausesOk acap ks) (hba : KittenBaseAssignOk ks)
    (hlvl0 : ks.lvl = 0#32) {cid : Nat} (hcid : cid < ks.nc.toNat)
    (hfals : ∀ l ∈ kittenClauseLits ks cid, ks.vals[l]? = some 2#32) :
    (cnfOfClauses (kittenOrigClauses ks)).Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have hce := (hcl.cl_wf cid hcid).2.2.2.2.1
  obtain ⟨l, hl_mem, hlsat⟩ :=
    (clause_sat_cnfClause_iff α (kittenClauseLits ks cid)).mp
      (CNF.entails_clause_def.mp hce α hα)
  have hl_lt := (hcl.cl_wf cid hcid).2.2.2.1 l hl_mem
  have hnz : ks.vals[l]?.getD 0#32 ≠ 0#32 := by simp [hfals l hl_mem]
  obtain ⟨i, hi, hveq⟩ := (hba.vals_nz_iff_trl l hl_lt).mp hnz
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hsh.trl_len]; have := hba.trl_end_le; have := hcl.nv_le; unfold kMaxV at *; omega
  have htl_lt : (ks.trl[i]?.getD 0#32).toNat < 2 * ks.nv.toNat :=
    hba.trl_lt _ (mem_kittenTrailLits_of_lt hi htrl_len)
  have hlvl_v : ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = 0#32 := by
    have hle := hba.trl_lvl_le ((ks.trl[i]?.getD 0#32).toNat / 2) (by omega)
    rw [hlvl0] at hle
    exact BitVec.eq_of_toNat_eq (Nat.eq_zero_of_le_zero hle)
  have h0 := hba.lvl0_ok i hi hlvl_v
  let tl := (ks.trl[i]?.getD 0#32).toNat
  change ks.rsn[tl / 2]?.getD 0#32 ≠ 0xFFFFFFFF#32 ∧ ks.vals[tl]? = some 1#32 ∧
    ks.vals[tl ^^^ 1]? = some 2#32 ∧
    (cnfOfClauses (kittenOrigClauses ks)).EntailsClause (cnfClause [tl]) ∧
    (ks.ante ≠ 0#32 →
      let r := (ks.rsn[tl / 2]?.getD 0xFFFFFFFF#32).toNat
      r < ks.nc.toNat ∧ kittenClauseLits ks r = [tl]) at h0
  rcases (litVar_eq_iff tl l).mp (by simpa [litVar] using hveq) with heq | heq
  · rw [heq, hfals l hl_mem] at h0; cases h0.2.1
  · have hent := h0.2.2.2.1; rw [heq] at hent
    exact (sat_cnfClause_litNeg_iff α l).mp (CNF.entails_clause_def.mp hent α hα)
      ((sat_cnfClause_singleton α l).mpr hlsat)

/-- Conflict under assumption decisions refutes `orig ++ unitsCnf assumps`. -/
theorem kitten_conflict_unsat_assumps {acap : Nat} {ks : KittenState}
    (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks)
    (hdec : KittenAllDecisionsInAssumps ks)
    {cid : Nat} (hcid : cid < ks.nc.toNat)
    (hfals : ∀ l ∈ kittenClauseLits ks cid, ks.vals[l]? = some 2#32) :
    (cnfOfClauses (kittenOrigClauses ks) ++ unitsCnf (kittenAssumpLits ks)).Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have hce := (hinv.clauses.cl_wf cid hcid).2.2.2.2.1
  obtain ⟨l, hl_mem, hlsat⟩ :=
    (clause_sat_cnfClause_iff α (kittenClauseLits ks cid)).mp
      (CNF.entails_clause_def.mp hce α (CNF.sat_append.mp hα).1)
  have hl_lt := (hinv.clauses.cl_wf cid hcid).2.2.2.1 l hl_mem
  obtain ⟨i, hi, hieq⟩ :=
    kitten_falsified_to_trail hinv.shapes hinv.clauses.nv_le hinv.assign hsync hl_lt
      (hfals l hl_mem)
  have hent := kitten_trail_entails_with_assumps
    hinv.shapes hinv.clauses hinv.assign hinv.reasons hdec i hi
  rw [hieq] at hent
  exact (sat_cnfClause_litNeg_iff α l).mp (CNF.entails_clause_def.mp hent α hα)
    ((sat_cnfClause_singleton α l).mpr hlsat)

/-- A single falsified assumption literal under `KittenAllDecisionsInAssumps` proves UNSAT. -/
theorem kitten_falsified_assump_unsat {acap : Nat} {ks : KittenState}
    (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks)
    (hdec : KittenAllDecisionsInAssumps ks)
    {i : Nat} (hi : i < ks.nassump.toNat)
    (hfals : ks.vals[(ks.assump[i]?.getD 0#32).toNat]? = some 2#32) :
    (cnfOfClauses (kittenOrigClauses ks) ++ unitsCnf (kittenAssumpLits ks)).Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  let a := (ks.assump[i]?.getD 0#32).toNat
  have ha_lt : a < 2 * ks.nv.toNat := hinv.clauses.assump_ok i hi
  have ha_mem : a ∈ kittenAssumpLits ks := by
    unfold kittenAssumpLits
    rw [List.mem_map]
    have hlen : ks.nassump.toNat ≤ ks.assump.length := by
      rw [hinv.shapes.assump_len]; exact hinv.clauses.nassump_le
    refine ⟨ks.assump[i]?.getD 0#32, ?_, rfl⟩
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [List.length_take]; omega,
      by simp [List.getElem?_eq_getElem (by omega : i < ks.assump.length)]⟩
  have hsat_a := (sat_unitsCnf_iff α (kittenAssumpLits ks)).mp (CNF.sat_append.mp hα).2 a ha_mem
  obtain ⟨j, hj, hjeq⟩ :=
    kitten_falsified_to_trail hinv.shapes hinv.clauses.nv_le hinv.assign hsync ha_lt hfals
  have hent := kitten_trail_entails_with_assumps
    hinv.shapes hinv.clauses hinv.assign hinv.reasons hdec j hj
  rw [hjeq] at hent
  exact (sat_cnfClause_litNeg_iff α a).mp (CNF.entails_clause_def.mp hent α hα) hsat_a

/-! ## 4. Structural Preservation Helpers (`watch`, `assign`, `mtf`, `bt`, `init`, `add_clause`) -/

theorem WChain.congr {wn1 wn2 : List (BitVec 32)} {hd : BitVec 32} {ws : List Nat}
    (hc : WChain wn1 hd ws) (hcongr : ∀ w ∈ ws, wn1[w]? = wn2[w]?) :
    WChain wn2 hd ws := by
  induction hc with
  | nil => exact WChain.nil
  | @cons w ws hw _ ih =>
    have hw2 : w < wn2.length := by
      have heq := hcongr w List.mem_cons_self
      rw [List.getElem?_eq_getElem hw] at heq
      exact (List.getElem?_eq_some_iff.mp heq.symm).1
    have hnxt : wn1[w]'hw = wn2[w]'hw2 := by
      have heq := hcongr w List.mem_cons_self
      rw [List.getElem?_eq_getElem hw, List.getElem?_eq_getElem hw2] at heq
      exact Option.some.inj heq
    have ih' := ih fun x hx => hcongr x (List.mem_cons_of_mem _ hx)
    rw [hnxt] at ih'
    exact WChain.cons hw2 ih'

theorem WChain.lt_length {wn : List (BitVec 32)} {hd : BitVec 32} {ws : List Nat}
    (hc : WChain wn hd ws) : ∀ w ∈ ws, w < wn.length := by
  induction hc with
  | nil => intro _ hm; nomatch hm
  | @cons w ws hw _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact hw
    · exact ih x hmem

theorem WChain_cases {wn : List (BitVec 32)} {hd : BitVec 32} {ws : List Nat}
    (hc : WChain wn hd ws) :
    (hd = 0xFFFFFFFF#32 ∧ ws = []) ∨
    (∃ w ws', ∃ (hw : w < wn.length),
      hd = BitVec.ofNat 32 w ∧ ws = w :: ws' ∧ WChain wn (wn[w]'hw) ws') := by
  cases hc with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | @cons w ws' hw ht => exact Or.inr ⟨w, ws', hw, rfl, rfl, ht⟩

theorem WChain.unique {wn : List (BitVec 32)} {hd : BitVec 32} {ws1 ws2 : List Nat}
    (hwn : wn.length < 2 ^ 32) (h1 : WChain wn hd ws1) (h2 : WChain wn hd ws2) :
    ws1 = ws2 := by
  induction h1 generalizing ws2 with
  | nil =>
    rcases WChain_cases h2 with ⟨_, rfl⟩ | ⟨w, _, hw, h2eq, _, _⟩
    · rfl
    · exfalso
      have h2 := congrArg BitVec.toNat h2eq
      simp [Nat.mod_eq_of_lt (Nat.lt_trans hw hwn)] at h2
      omega
  | @cons w1 ws1' hw1 _ ih =>
    rcases WChain_cases h2 with ⟨h2eq, _⟩ | ⟨w2, ws2', hw2, h2eq, rfl, ht2⟩
    · exfalso
      have h2 := congrArg BitVec.toNat h2eq
      simp [Nat.mod_eq_of_lt (Nat.lt_trans hw1 hwn)] at h2
      omega
    · have h12 : w1 = w2 := by
        have ht := congrArg BitVec.toNat h2eq
        rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (Nat.lt_trans hw1 hwn),
          Nat.mod_eq_of_lt (Nat.lt_trans hw2 hwn)] at ht
      subst h12
      exact congrArg (w1 :: ·) (ih ht2)

theorem WChain_getElem_of_eq {wn : List (BitVec 32)} {hd : BitVec 32} {ws : List Nat}
    (hc : WChain wn hd ws) (hne : hd ≠ 0xFFFFFFFF#32) :
    ∃ w ws', ∃ (hw : w < wn.length), ws = w :: ws' ∧ hd = BitVec.ofNat 32 w ∧
      WChain wn (wn[w]'hw) ws' := by
  rcases WChain_cases hc with ⟨heq, _⟩ | ⟨w, ws', hw, rfl, rfl, htail⟩
  · exact absurd heq hne
  · exact ⟨w, ws', hw, rfl, rfl, htail⟩

theorem WChain_nil_iff {wn : List (BitVec 32)} {hd : BitVec 32} {ws : List Nat}
    (hwn : wn.length < 2 ^ 32) (hc : WChain wn hd ws) : hd = 0xFFFFFFFF#32 → ws = [] := by
  intro heq
  rcases WChain_cases hc with ⟨_, rfl⟩ | ⟨w, _, hw, h2eq, _, _⟩
  · rfl
  · exfalso
    have h2 : (BitVec.ofNat 32 w).toNat = (0xFFFFFFFF#32 : BitVec 32).toNat :=
      congrArg BitVec.toNat (h2eq.symm.trans heq)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hw hwn),
      show (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 by decide] at h2
    omega

theorem list_flatten_set_perm {α : Type} (xs : List (List α)) {i : Nat} (hi : i < xs.length)
    (a : α) :
    (xs.set i (a :: xs[i])).flatten.Perm (a :: xs.flatten) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x tl ih =>
    cases i with
    | zero => simp
    | succ i' =>
      simp only [List.set_cons_succ, List.flatten_cons, List.getElem_cons_succ]
      exact (List.Perm.append_left x (ih (by simp at hi; omega))).trans List.perm_middle

theorem kittenWatchStep0_preserves_shapes {acap : Nat} {ks : KittenState}
    (h : ks.ShapesOk acap) (w l vo : BitVec 32) :
    (kittenWatchStep0 ks w l vo).ShapesOk acap := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20⟩
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    by simp [kittenWatchStep0, h14], by simp [kittenWatchStep0, h15],
    by simp [kittenWatchStep0, h16], h17, h18, h19, h20⟩

theorem kittenWatchStep_preserves_shapes {acap : Nat} {ks : KittenState}
    (h : ks.ShapesOk acap) (cid l0 l1 : BitVec 32) :
    (kittenWatchStep ks cid l0 l1).ShapesOk acap :=
  kittenWatchStep0_preserves_shapes
    (kittenWatchStep0_preserves_shapes h _ _ _) _ _ _

theorem kittenWatchStep0_preserves_watches_with {acap : Nat} {ks : KittenState}
    (hsh : ks.ShapesOk acap)
    {chains : List (List Nat)} (hlen : chains.length = 2 * ks.nv.toNat)
    (hnd : chains.flatten.Nodup)
    (hwc : ∀ x < 2 * ks.nv.toNat,
      WChain ks.wnext (ks.whead[x]?.getD 0xFFFFFFFF#32) (chains[x]?.getD []))
    (hbnd : ∀ x < 2 * ks.nv.toNat, ∀ u ∈ chains[x]?.getD [],
      u < 2 * ks.nc.toNat ∧ 2 ≤ kittenClauseSize ks (u / 2) ∧
      (ks.arena[kittenClauseOff ks (u / 2) + (u % 2)]?.getD 0#32).toNat = x ∧
      (ks.wblit[u]?.getD 0#32).toNat < 2 * ks.nv.toNat)
    {w l vo : BitVec 32} (hw_nc : w.toNat < 2 * ks.nc.toNat)
    (hw_max : ks.nc.toNat ≤ kMaxCl) (hnv : ks.nv.toNat ≤ kMaxV)
    (hl : l.toNat < 2 * ks.nv.toNat) (hvo : vo.toNat < 2 * ks.nv.toNat)
    (hsz : 2 ≤ kittenClauseSize ks (w.toNat / 2))
    (hlit : (ks.arena[kittenClauseOff ks (w.toNat / 2) + (w.toNat % 2)]?.getD 0#32).toNat =
      l.toNat)
    (hfresh : w.toNat ∉ chains.flatten) :
    let ks' := kittenWatchStep0 ks w l vo
    let chains' := chains.set l.toNat (w.toNat :: chains[l.toNat]'(by omega))
    chains'.length = 2 * ks'.nv.toNat ∧ chains'.flatten.Nodup ∧
    (∀ x < 2 * ks'.nv.toNat,
      WChain ks'.wnext (ks'.whead[x]?.getD 0xFFFFFFFF#32) (chains'[x]?.getD [])) ∧
    (∀ x < 2 * ks'.nv.toNat, ∀ u ∈ chains'[x]?.getD [],
      u < 2 * ks'.nc.toNat ∧ 2 ≤ kittenClauseSize ks' (u / 2) ∧
      (ks'.arena[kittenClauseOff ks' (u / 2) + (u % 2)]?.getD 0#32).toNat = x ∧
      (ks'.wblit[u]?.getD 0#32).toNat < 2 * ks'.nv.toNat) ∧
    (∀ u, u ∈ chains'.flatten ↔ u = w.toNat ∨ u ∈ chains.flatten) := by
  intro ks' chains'
  have hl_ch : l.toNat < chains.length := by omega
  have hwi_len : w.toNat < ks.wnext.length := by
    rw [hsh.wnext_len]; unfold kMaxCl at hw_max; omega
  have hwbi_len : w.toNat < ks.wblit.length := by
    rw [hsh.wblit_len]; unfold kMaxCl at hw_max; omega
  have hwh_len : l.toNat < ks.whead.length := by
    rw [hsh.whead_len]; unfold kMaxV at hnv; omega
  have hcl_len : chains'.length = 2 * ks'.nv.toNat := by
    simp [chains', ks', kittenWatchStep0, hlen]
  have hnd' : chains'.flatten.Nodup :=
    (list_flatten_set_perm chains hl_ch w.toNat).nodup_iff.mpr
      (List.nodup_cons.mpr ⟨hfresh, hnd⟩)
  have hperm : ∀ u, u ∈ chains'.flatten ↔ u = w.toNat ∨ u ∈ chains.flatten := by
    intro u; rw [(list_flatten_set_perm chains hl_ch w.toNat).mem_iff, List.mem_cons]
  refine ⟨hcl_len, hnd', ?_, ?_, hperm⟩
  · intro x hx
    have hx_nv : x < 2 * ks.nv.toNat := hx
    have hx_ch : x < chains.length := by omega
    have hch_old := hwc x hx_nv
    rw [List.getElem?_eq_getElem hx_ch, Option.getD_some] at hch_old
    have hcl_x : x < chains'.length := by simp [chains', hx_ch]
    by_cases hxl : x = l.toNat
    · subst hxl
      rw [List.getElem?_eq_getElem hcl_x, Option.getD_some]
      simp only [chains', List.getElem_set_self]
      have hwh' : ks'.whead[l.toNat]?.getD 0xFFFFFFFF#32 = w := by
        simp [ks', kittenWatchStep0, List.getElem?_set_self hwh_len]
      rw [hwh']
      have hw_lt' : w.toNat < ks'.wnext.length := by simp [ks', kittenWatchStep0, hwi_len]
      have hget : ks'.wnext[w.toNat]'hw_lt' = ks.whead[l.toNat]?.getD 0xFFFFFFFF#32 := by
        simp [ks', kittenWatchStep0, List.getElem?_eq_getElem hwh_len]
      have htail : WChain ks'.wnext (ks'.wnext[w.toNat]'hw_lt') chains[l.toNat] := by
        rw [hget]
        refine hch_old.congr fun u hu => ?_
        have hune : u ≠ w.toNat := fun heq => hfresh (by
          rw [← heq]
          exact List.mem_flatten.mpr ⟨chains[l.toNat], List.getElem_mem hx_ch, hu⟩)
        exact (List.getElem?_set_ne hune.symm).symm
      simpa [BitVec.ofNat_toNat] using WChain.cons hw_lt' htail
    · rw [List.getElem?_eq_getElem hcl_x, Option.getD_some]
      simp only [chains', List.getElem_set_ne (Ne.symm hxl)]
      have hwh' : ks'.whead[x]?.getD 0xFFFFFFFF#32 = ks.whead[x]?.getD 0xFFFFFFFF#32 := by
        simp [ks', kittenWatchStep0, List.getElem?_set_ne (Ne.symm hxl)]
      rw [hwh']
      refine hch_old.congr fun u hu => ?_
      have hune : u ≠ w.toNat := fun heq => hfresh (by
        rw [← heq]; exact List.mem_flatten.mpr ⟨chains[x], List.getElem_mem hx_ch, hu⟩)
      exact (List.getElem?_set_ne hune.symm).symm
  · intro x hx u hu
    have hx_nv : x < 2 * ks.nv.toNat := hx
    have hx_ch : x < chains.length := by omega
    have hcl_x : x < chains'.length := by simp [chains', hx_ch]
    rw [List.getElem?_eq_getElem hcl_x, Option.getD_some] at hu
    by_cases hxl : x = l.toNat
    · subst hxl
      simp only [chains', List.getElem_set_self] at hu
      rcases List.mem_cons.mp hu with rfl | hu_old
      · refine ⟨hw_nc, hsz, hlit, ?_⟩
        simp [ks', kittenWatchStep0, List.getElem?_set_self hwbi_len, hvo]
      · obtain ⟨h1, h2, h3, h4⟩ := hbnd l.toNat hx_nv u
          (by simpa [List.getElem?_eq_getElem hx_ch] using hu_old)
        have hune : u ≠ w.toNat := fun heq => hfresh (by
          rw [← heq]
          exact List.mem_flatten.mpr ⟨chains[l.toNat], List.getElem_mem hx_ch, hu_old⟩)
        refine ⟨h1, h2, h3, ?_⟩
        have hwb : ks'.wblit[u]? = ks.wblit[u]? := List.getElem?_set_ne hune.symm
        rw [hwb]; exact h4
    · simp only [chains', List.getElem_set_ne (Ne.symm hxl)] at hu
      obtain ⟨h1, h2, h3, h4⟩ := hbnd x hx_nv u
        (by simpa [List.getElem?_eq_getElem hx_ch] using hu)
      have hune : u ≠ w.toNat := fun heq => hfresh (by
        rw [← heq]; exact List.mem_flatten.mpr ⟨chains[x], List.getElem_mem hx_ch, hu⟩)
      refine ⟨h1, h2, h3, ?_⟩
      have hwb : ks'.wblit[u]? = ks.wblit[u]? := List.getElem?_set_ne hune.symm
      rw [hwb]; exact h4

/-- Adding a single fresh watch node `(w, l, vo)` preserves `KittenWatchesOk`. -/
theorem kittenWatchStep0_preserves_watches {acap : Nat} {ks : KittenState}
    (hsh : ks.ShapesOk acap) (hw : KittenWatchesOk ks)
    {w l vo : BitVec 32} (hw_nc : w.toNat < 2 * ks.nc.toNat)
    (hw_max : ks.nc.toNat ≤ kMaxCl) (hnv : ks.nv.toNat ≤ kMaxV)
    (hl : l.toNat < 2 * ks.nv.toNat) (hvo : vo.toNat < 2 * ks.nv.toNat)
    (hsz : 2 ≤ kittenClauseSize ks (w.toNat / 2))
    (hlit : (ks.arena[kittenClauseOff ks (w.toNat / 2) + (w.toNat % 2)]?.getD 0#32).toNat =
      l.toNat)
    (hfwd : ∀ chains : List (List Nat),
      chains.length = 2 * ks.nv.toNat → chains.flatten.Nodup →
      (∀ x < 2 * ks.nv.toNat,
        WChain ks.wnext (ks.whead[x]?.getD 0xFFFFFFFF#32) (chains[x]?.getD [])) →
      w.toNat ∉ chains.flatten) :
    KittenWatchesOk (kittenWatchStep0 ks w l vo) := by
  obtain ⟨chains, hlen, hnd, hwc, hbnd⟩ := hw
  have h := kittenWatchStep0_preserves_watches_with hsh hlen hnd hwc hbnd hw_nc hw_max hnv
    hl hvo hsz hlit (hfwd chains hlen hnd hwc)
  exact ⟨_, h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- Watching both `(cid <<< 1, l0, l1)` and `((cid <<< 1) ||| 1, l1, l0)` preserves watches. -/
theorem kittenWatchStep_preserves_watches {acap : Nat} {ks : KittenState}
    (hsh : ks.ShapesOk acap) (hw : KittenWatchesOk ks)
    {cid l0 l1 : BitVec 32} (hc_lt : cid.toNat < ks.nc.toNat) (hc_max : ks.nc.toNat ≤ kMaxCl)
    (hnv : ks.nv.toNat ≤ kMaxV)
    (hl0 : l0.toNat < 2 * ks.nv.toNat) (hl1 : l1.toNat < 2 * ks.nv.toNat)
    (hsz : 2 ≤ kittenClauseSize ks cid.toNat)
    (hlit0 : (ks.arena[kittenClauseOff ks cid.toNat]?.getD 0#32).toNat = l0.toNat)
    (hlit1 : (ks.arena[kittenClauseOff ks cid.toNat + 1]?.getD 0#32).toNat = l1.toNat)
    (hfwd : ∀ chains : List (List Nat),
      chains.length = 2 * ks.nv.toNat → chains.flatten.Nodup →
      (∀ x < 2 * ks.nv.toNat,
        WChain ks.wnext (ks.whead[x]?.getD 0xFFFFFFFF#32) (chains[x]?.getD [])) →
      2 * cid.toNat ∉ chains.flatten ∧ 2 * cid.toNat + 1 ∉ chains.flatten) :
    KittenWatchesOk (kittenWatchStep ks cid l0 l1) := by
  obtain ⟨chains, hlen, hnd, hwc, hbnd⟩ := hw
  have ⟨hf0, hf1⟩ := hfwd chains hlen hnd hwc
  have hmc : kMaxCl ≤ 896 := Nat.le_refl _
  have hw0 := bv32_cid_w0 hc_lt (by omega)
  have hw1 := bv32_cid_w1 hc_lt (by omega)
  let w0 := cid <<< 1
  let w1 := w0 ||| 1#32
  have hw0_toNat : w0.toNat = 2 * cid.toNat := hw0.1
  have hw1_toNat : w1.toNat = 2 * cid.toNat + 1 := hw1.1
  have hstep0 := kittenWatchStep0_preserves_watches_with hsh hlen hnd hwc hbnd
    (w := w0) (l := l0) (vo := l1) (by omega) hc_max hnv hl0 hl1
    (by rw [hw0_toNat, show 2 * cid.toNat / 2 = cid.toNat by omega]; exact hsz)
    (by rw [hw0_toNat, show 2 * cid.toNat / 2 = cid.toNat by omega,
        show 2 * cid.toNat % 2 = 0 by omega]; exact hlit0)
    (by rw [hw0_toNat]; exact hf0)
  have hsh0 := kittenWatchStep0_preserves_shapes hsh w0 l0 l1
  have hnc0 : (kittenWatchStep0 ks w0 l0 l1).nc = ks.nc := rfl
  have hnv0 : (kittenWatchStep0 ks w0 l0 l1).nv = ks.nv := rfl
  have h1 := kittenWatchStep0_preserves_watches_with hsh0 hstep0.1 hstep0.2.1 hstep0.2.2.1
    hstep0.2.2.2.1 (w := w1) (l := l1) (vo := l0) (by rw [hnc0]; omega)
    (by rw [hnc0]; exact hc_max) (by rw [hnv0]; exact hnv) (by rw [hnv0]; exact hl1)
    (by rw [hnv0]; exact hl0)
    (by dsimp only [kittenWatchStep0, kittenClauseSize, kittenClauseMeta]
        rw [hw1_toNat, show (2 * cid.toNat + 1) / 2 = cid.toNat by omega]; exact hsz)
    (by dsimp only [kittenWatchStep0, kittenClauseOff]
        rw [hw1_toNat, show (2 * cid.toNat + 1) / 2 = cid.toNat by omega,
          show (2 * cid.toNat + 1) % 2 = 1 by omega]; exact hlit1)
    (fun hm => by
      rcases (hstep0.2.2.2.2 w1.toNat).mp hm with heq | hmem
      · omega
      · exact hf1 (by rwa [← hw1_toNat]))
  exact ⟨_, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1⟩

theorem kittenAssignStep_preserves_shapes {acap : Nat} {ks : KittenState}
    (h : ks.ShapesOk acap) (lit rsn : BitVec 32) :
    (kittenAssignStep ks lit rsn).ShapesOk acap := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20⟩
  exact ⟨h0, by simp [kittenAssignStep, h1], by simp [kittenAssignStep, h2], h3, h4, h5,
    by simp [kittenAssignStep, h6], by simp [kittenAssignStep, h7],
    by simp [kittenAssignStep, h8], h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩

theorem kittenState_setQueue_preserves_clauses {acap : Nat} {ks : KittenState}
    (h : KittenClausesOk acap ks) (qf ql qs qst : BitVec 32) (qp qn qsa : List (BitVec 32)) :
    KittenClausesOk acap
      { ks with qfirst := qf, qlast := ql, qsearch := qs, qstamp := qst,
                qprev := qp, qnext := qn, qstampArr := qsa } :=
  ⟨h.acap_ge, h.acap_lt, h.acap_eq, h.nv_le, h.nc_le, h.orig_nc_le, h.orig_nc_max, h.alen_le,
    h.nassump_le, h.nunits_le, h.nres_le, h.nkl_le, h.nana_le, h.cl_wf, h.cl_mono, h.units_ok,
    h.incons_ok, h.failing_ok, h.assump_ok, h.flags_clean⟩

theorem kittenState_setQueue_preserves_watches {ks : KittenState} (h : KittenWatchesOk ks)
    (qf ql qs qst : BitVec 32) (qp qn qsa : List (BitVec 32)) :
    KittenWatchesOk
      { ks with qfirst := qf, qlast := ql, qsearch := qs, qstamp := qst,
                qprev := qp, qnext := qn, qstampArr := qsa } := h

theorem kittenState_setQueue_preserves_assign {ks : KittenState} (h : KittenBaseAssignOk ks)
    (qf ql qs qst : BitVec 32) (qp qn qsa : List (BitVec 32)) :
    KittenBaseAssignOk
      { ks with qfirst := qf, qlast := ql, qsearch := qs, qstamp := qst,
                qprev := qp, qnext := qn, qstampArr := qsa } :=
  ⟨h.trl_end_le, h.prop_le, h.unass_eq, h.vals_dom, h.vals_neg_iff, h.vals_nz_iff_trl,
    h.trl_nodup, h.trl_lt, h.trl_lvl_le, h.unass_lvl_zero, h.trl_lvl_mono, h.dec_earliest,
    h.lvl0_ok⟩

theorem kittenState_setQueue_preserves_reasons {ks : KittenState} (h : ReasonOk ks)
    (qf ql qs qst : BitVec 32) (qp qn qsa : List (BitVec 32)) :
    ReasonOk
      { ks with qfirst := qf, qlast := ql, qsearch := qs, qstamp := qst,
                qprev := qp, qnext := qn, qstampArr := qsa } := h

theorem kittenState_setQueue_preserves_inv {acap : Nat} {ks : KittenState}
    (hinv : ks.Inv acap) {qf ql qs qst : BitVec 32} {qp qn qsa : List (BitVec 32)}
    (hp : qp.length = 128) (hn : qn.length = 128) (hs : qsa.length = 128) :
    ({ ks with qfirst := qf, qlast := ql, qsearch := qs, qstamp := qst,
               qprev := qp, qnext := qn, qstampArr := qsa } : KittenState).Inv acap :=
  ⟨⟨hinv.shapes.hdrTail_len, hinv.shapes.lvlArr_len, hinv.shapes.rsn_len, hp, hn, hs,
      hinv.shapes.trl_len, hinv.shapes.flags_len, hinv.shapes.vals_len, hinv.shapes.assump_len,
      hinv.shapes.ana_len, hinv.shapes.kl_len, hinv.shapes.units_len, hinv.shapes.res_len,
      hinv.shapes.whead_len, hinv.shapes.wnext_len, hinv.shapes.wblit_len, hinv.shapes.clOff_len,
      hinv.shapes.clMeta_len, hinv.shapes.clAux_len, hinv.shapes.arena_len⟩,
    kittenState_setQueue_preserves_clauses hinv.clauses qf ql qs qst qp qn qsa,
    kittenState_setQueue_preserves_watches hinv.watches qf ql qs qst qp qn qsa,
    kittenState_setQueue_preserves_assign hinv.assign qf ql qs qst qp qn qsa,
    kittenState_setQueue_preserves_reasons hinv.reasons qf ql qs qst qp qn qsa⟩

/-! ### Backtrack Loop Invariant & Finish Lemmas -/

structure BtLoopInv (acap : Nat) (ks : KittenState) (target_lvl te : BitVec 32)
    (st : KittenState) : Prop where
  sh : st.ShapesOk acap
  te_le : te.toNat ≤ ks.trl_end.toNat
  unass_eq : st.unass.toNat + te.toNat = ks.nv.toNat
  nv_eq : st.nv = ks.nv
  nc_eq : st.nc = ks.nc
  orig_eq : st.orig_nc = ks.orig_nc
  lvl_eq : st.lvl = ks.lvl
  prop_eq : st.prop = ks.prop
  te_hdr : st.trl_end = ks.trl_end
  inc_eq : st.incons = ks.incons
  fail_eq : st.failing = ks.failing
  ante_eq : st.ante = ks.ante
  alen_eq : st.alen = ks.alen
  acap_eq : st.acap = ks.acap
  na_eq : st.nassump = ks.nassump
  nu_eq : st.nunits = ks.nunits
  nr_eq : st.nres = ks.nres
  nk_eq : st.nkl = ks.nkl
  nan_eq : st.nana = ks.nana
  st_eq : st.status = ks.status
  ph_eq : st.phase = ks.phase
  ht_eq : st.hdrTail = ks.hdrTail
  qs_eq : st.qstampArr = ks.qstampArr
  trl_eq : st.trl = ks.trl
  fl_eq : st.flags = ks.flags
  ass_eq : st.assump = ks.assump
  ana_eq : st.ana = ks.ana
  kl_eq : st.kl = ks.kl
  uni_eq : st.units = ks.units
  res_eq : st.res = ks.res
  wh_eq : st.whead = ks.whead
  wn_eq : st.wnext = ks.wnext
  wb_eq : st.wblit = ks.wblit
  co_eq : st.clOff = ks.clOff
  cm_eq : st.clMeta = ks.clMeta
  ca_eq : st.clAux = ks.clAux
  ar_eq : st.arena = ks.arena
  kept_var : ∀ v < ks.nv.toNat,
    (∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = v) →
    st.lvlArr[v]? = ks.lvlArr[v]? ∧ st.rsn[v]? = ks.rsn[v]? ∧
    st.vals[2 * v]? = ks.vals[2 * v]? ∧ st.vals[2 * v + 1]? = ks.vals[2 * v + 1]?
  cleared_var : ∀ v < ks.nv.toNat,
    (¬ ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = v) →
    st.lvlArr[v]? = some 0#32 ∧ st.rsn[v]? = some 0xFFFFFFFF#32 ∧
    st.vals[2 * v]? = some 0#32 ∧ st.vals[2 * v + 1]? = some 0#32
  popped_gt : ∀ i, te.toNat ≤ i → i < ks.trl_end.toNat →
    target_lvl.toNat < (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat

theorem bt_loopInv_init {acap : Nat} {ks : KittenState} {target_lvl : BitVec 32}
    (hinv : ks.Inv acap) : BtLoopInv acap ks target_lvl ks.trl_end ks := by
  refine ⟨hinv.shapes, Nat.le_refl _, hinv.assign.unass_eq, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, fun i h1 h2 => by omega⟩
  · intro v _ _; exact ⟨rfl, rfl, rfl, rfl⟩
  · intro v hv hnone
    have h0 : ks.vals[2 * v]?.getD 0#32 = 0#32 := by
      by_cases hnz : ks.vals[2 * v]?.getD 0#32 = 0#32
      · exact hnz
      · exfalso
        obtain ⟨i, hi, hiv⟩ := (hinv.assign.vals_nz_iff_trl (2 * v) (by omega)).mp hnz
        exact hnone ⟨i, hi, by omega⟩
    have h1 : ks.vals[2 * v + 1]?.getD 0#32 = 0#32 := by
      by_cases hnz : ks.vals[2 * v + 1]?.getD 0#32 = 0#32
      · exact hnz
      · exfalso
        obtain ⟨i, hi, hiv⟩ := (hinv.assign.vals_nz_iff_trl (2 * v + 1) (by omega)).mp hnz
        exact hnone ⟨i, hi, by omega⟩
    have hun := hinv.assign.unass_lvl_zero v hv h0
    have hnv := hinv.clauses.nv_le
    unfold kMaxV at hnv
    have hlv : v < ks.lvlArr.length := by rw [hinv.shapes.lvlArr_len]; omega
    have hrs : v < ks.rsn.length := by rw [hinv.shapes.rsn_len]; omega
    have hv0 : 2 * v < ks.vals.length := by rw [hinv.shapes.vals_len]; omega
    have hv1 : 2 * v + 1 < ks.vals.length := by rw [hinv.shapes.vals_len]; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [List.getElem?_eq_getElem hlv] at hun ⊢; exact congrArg some hun.1
    · rw [List.getElem?_eq_getElem hrs] at hun ⊢; exact congrArg some hun.2
    · rw [List.getElem?_eq_getElem hv0] at h0 ⊢; exact congrArg some h0
    · rw [List.getElem?_eq_getElem hv1] at h1 ⊢; exact congrArg some h1

theorem list_nodup_getElem_inj {α : Type} {xs : List α} (hnd : xs.Nodup)
    {i j : Nat} (hi : i < xs.length) (hj : j < xs.length) (hij : xs[i] = xs[j]) :
    i = j := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons x tl ih =>
    rcases List.nodup_cons.mp hnd with ⟨hnot, hnd_tl⟩
    cases i <;> cases j
    · rfl
    · exfalso; simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hij
      exact hnot (hij ▸ List.getElem_mem (by simp at hj; omega))
    · exfalso; simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hij
      exact hnot (hij ▸ List.getElem_mem (by simp at hi; omega))
    · simp only [List.getElem_cons_succ] at hij
      exact congrArg Nat.succ (ih hnd_tl (by simp at hi; omega) (by simp at hj; omega) hij)

private theorem trl_nodup_var_ne {acap : Nat} {ks : KittenState} (hsh : ks.ShapesOk acap)
    (hnv : ks.nv.toNat ≤ kMaxV) (hba : KittenBaseAssignOk ks)
    {i j : Nat} (hi : i < ks.trl_end.toNat) (hj : j < ks.trl_end.toNat) (hne : i ≠ j) :
    (ks.trl[i]?.getD 0#32).toNat / 2 ≠ (ks.trl[j]?.getD 0#32).toNat / 2 := by
  have hlen : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hsh.trl_len]; have := hba.trl_end_le; unfold kMaxV at hnv; omega
  have hnd := hba.trl_nodup
  unfold kittenTrailLits at hnd
  rw [List.map_map] at hnd
  have hm_len : (List.map ((fun x => x / 2) ∘ BitVec.toNat)
      (ks.trl.take ks.trl_end.toNat)).length = ks.trl_end.toNat := by
    simp [List.length_take]; omega
  intro heq
  have hinj := list_nodup_getElem_inj hnd (by omega) (by omega)
    (show (List.map ((fun x => x / 2) ∘ BitVec.toNat) (ks.trl.take ks.trl_end.toNat))[i] =
        (List.map ((fun x => x / 2) ∘ BitVec.toNat) (ks.trl.take ks.trl_end.toNat))[j] by
      simp only [List.getElem_map, List.getElem_take, Function.comp_def]
      rw [List.getElem?_eq_getElem (by omega : i < ks.trl.length),
        List.getElem?_eq_getElem (by omega : j < ks.trl.length), Option.getD_some,
        Option.getD_some] at heq
      exact heq)
  exact hne hinj

theorem bt_loopInv_step {acap : Nat} {ks : KittenState} {target_lvl te : BitVec 32}
    {st : KittenState} (hinv : ks.Inv acap) (hbt : BtLoopInv acap ks target_lvl te st)
    (hpos : 0 < te.toNat)
    (hpop : target_lvl.toNat <
      (st.lvlArr[(ks.trl[te.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) :
    let lit := ks.trl[te.toNat - 1]'(by
      rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; have := hinv.clauses.nv_le
      have := hbt.te_le; unfold kMaxV at *; omega)
    let v := lit.toNat / 2
    let st' := (((((st.putArr .vals lit.toNat 0#32).putArr .vals (lit ^^^ 1#32).toNat 0#32).putArr
      .lvlArr v 0#32).putArr .rsn v 0xFFFFFFFF#32).putHdr .unass (st.unass + 1#32))
    BtLoopInv acap ks target_lvl (te - 1#32) st' ∧
    (∀ qs, BtLoopInv acap ks target_lvl (te - 1#32) (st'.putHdr .qsearch qs)) := by
  intro lit v st'
  have hnv := hinv.clauses.nv_le
  have hte := hbt.te_le
  have hte1_lt : te.toNat - 1 < ks.trl_end.toNat := by omega
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; unfold kMaxV at hnv; omega
  have hlit_lt : lit.toNat < 2 * ks.nv.toNat := by
    have hm := mem_kittenTrailLits_of_lt hte1_lt htrl_len
    rw [List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length), Option.getD_some] at hm
    exact hinv.assign.trl_lt lit.toNat hm
  have hv_lt : v < ks.nv.toNat := by omega
  have hnl_eq : (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 := by simp
  have hsh' : st'.ShapesOk acap :=
    ((((hbt.sh.putArr .vals _ _).putArr .vals _ _).putArr .lvlArr _ _).putArr
      .rsn _ _).putHdr .unass _
  have hun_lt : st.unass.toNat + 1 < 2 ^ 32 := by
    have := hbt.unass_eq; unfold kMaxV at hnv; omega
  have hmk : ∀ qOpt : Option (BitVec 32),
      BtLoopInv acap ks target_lvl (te - 1#32)
        (match qOpt with | none => st' | some qs => st'.putHdr .qsearch qs) := by
    intro qOpt
    let finSt := match qOpt with | none => st' | some qs => st'.putHdr .qsearch qs
    have hshF : finSt.ShapesOk acap := by
      cases qOpt with
      | none => exact hsh'
      | some qs => exact hsh'.putHdr .qsearch qs
    have hte_sub : (te - 1#32).toNat = te.toNat - 1 := by bv_omega
    have hunF : finSt.unass.toNat + (te - 1#32).toNat = ks.nv.toNat := by
      have hun_st : finSt.unass = st.unass + 1#32 := by
        cases qOpt <;> dsimp only [finSt, st'] <;> kp_field
      rw [hun_st, hte_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have := hbt.unass_eq; omega
    have f_nv : finSt.nv = ks.nv := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.nv_eq
    have f_nc : finSt.nc = ks.nc := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.nc_eq
    have f_on : finSt.orig_nc = ks.orig_nc := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.orig_eq
    have f_lv : finSt.lvl = ks.lvl := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.lvl_eq
    have f_pr : finSt.prop = ks.prop := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.prop_eq
    have f_te : finSt.trl_end = ks.trl_end := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.te_hdr
    have f_in : finSt.incons = ks.incons := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.inc_eq
    have f_fa : finSt.failing = ks.failing := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.fail_eq
    have f_an : finSt.ante = ks.ante := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.ante_eq
    have f_al : finSt.alen = ks.alen := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.alen_eq
    have f_ac : finSt.acap = ks.acap := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.acap_eq
    have f_na : finSt.nassump = ks.nassump := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.na_eq
    have f_nu : finSt.nunits = ks.nunits := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.nu_eq
    have f_nr : finSt.nres = ks.nres := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.nr_eq
    have f_nk : finSt.nkl = ks.nkl := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.nk_eq
    have f_nn : finSt.nana = ks.nana := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.nan_eq
    have f_st : finSt.status = ks.status := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.st_eq
    have f_ph : finSt.phase = ks.phase := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.ph_eq
    have f_ht : finSt.hdrTail = ks.hdrTail := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.ht_eq
    have f_qs : finSt.qstampArr = ks.qstampArr := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.qs_eq
    have f_tr : finSt.trl = ks.trl := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.trl_eq
    have f_fl : finSt.flags = ks.flags := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.fl_eq
    have f_as : finSt.assump = ks.assump := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.ass_eq
    have f_aa : finSt.ana = ks.ana := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.ana_eq
    have f_kl : finSt.kl = ks.kl := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.kl_eq
    have f_un : finSt.units = ks.units := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.uni_eq
    have f_re : finSt.res = ks.res := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.res_eq
    have f_wh : finSt.whead = ks.whead := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.wh_eq
    have f_wn : finSt.wnext = ks.wnext := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.wn_eq
    have f_wb : finSt.wblit = ks.wblit := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.wb_eq
    have f_co : finSt.clOff = ks.clOff := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.co_eq
    have f_cm : finSt.clMeta = ks.clMeta := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.cm_eq
    have f_ca : finSt.clAux = ks.clAux := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.ca_eq
    have f_ar : finSt.arena = ks.arena := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> exact hbt.ar_eq
    have hlvl_st : finSt.lvlArr = st.lvlArr.set v 0#32 := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field
    have hrsn_st : finSt.rsn = st.rsn.set v 0xFFFFFFFF#32 := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field
    have hvals_st : finSt.vals = (st.vals.set lit.toNat 0#32).set (lit.toNat ^^^ 1) 0#32 := by
      cases qOpt <;> dsimp only [finSt, st'] <;> kp_field <;> rw [hnl_eq]
    have hl_xor := nat_xor1_cases lit.toNat
    refine ⟨hshF, by rw [hte_sub]; omega, hunF, f_nv, f_nc, f_on, f_lv, f_pr, f_te, f_in, f_fa,
      f_an, f_al, f_ac, f_na, f_nu, f_nr, f_nk, f_nn, f_st, f_ph, f_ht, f_qs, f_tr, f_fl,
      f_as, f_aa, f_kl, f_un, f_re, f_wh, f_wn, f_wb, f_co, f_cm, f_ca, f_ar, ?_, ?_, ?_⟩
    · intro w hw ⟨i, hi, hiw⟩
      have hi' : i < te.toNat - 1 := by rw [hte_sub] at hi; exact hi
      have hne_v : w ≠ v := by
        rw [← hiw]
        have hnd := trl_nodup_var_ne (i := i) (j := te.toNat - 1) hinv.shapes hnv hinv.assign
          (Nat.lt_trans hi' (by omega)) hte1_lt (by omega)
        rw [List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length), Option.getD_some]
          at hnd
        exact hnd
      have hold := hbt.kept_var w hw ⟨i, by omega, hiw⟩
      rcases hl_xor with ⟨h0a, h1a⟩ | ⟨h0a, h1a⟩ <;>
        · have hl_v0 : lit.toNat ≠ 2 * w := by omega
          have hl_v1 : lit.toNat ≠ 2 * w + 1 := by omega
          have hnl_v0 : lit.toNat ^^^ 1 ≠ 2 * w := by omega
          have hnl_v1 : lit.toNat ^^^ 1 ≠ 2 * w + 1 := by omega
          rw [hlvl_st, hrsn_st, hvals_st, List.getElem?_set_ne (Ne.symm hne_v),
            List.getElem?_set_ne (Ne.symm hne_v),
            List.getElem?_set_ne hnl_v0, List.getElem?_set_ne hl_v0,
            List.getElem?_set_ne hnl_v1, List.getElem?_set_ne hl_v1]
          exact hold
    · intro w hw hnone
      rw [hte_sub] at hnone
      by_cases hwv : w = v
      · subst hwv
        unfold kMaxV at hnv
        have h1 : v < st.lvlArr.length := by rw [hbt.sh.lvlArr_len]; omega
        have h2 : v < st.rsn.length := by rw [hbt.sh.rsn_len]; omega
        have h3 : 2 * v < st.vals.length := by rw [hbt.sh.vals_len]; omega
        have h4 : 2 * v + 1 < st.vals.length := by rw [hbt.sh.vals_len]; omega
        rw [hlvl_st, hrsn_st, hvals_st, List.getElem?_set_self h1, List.getElem?_set_self h2]
        rcases hl_xor with ⟨h0a, h1a⟩ | ⟨h0a, h1a⟩
        · have hs0 : (st.vals.set lit.toNat 0#32).set (lit.toNat ^^^ 1) 0#32 =
              (st.vals.set (2 * v) 0#32).set (2 * v + 1) 0#32 := by
            rw [h1a]; exact congrArg (fun a => (st.vals.set a 0#32).set (2 * v + 1) 0#32) h0a
          rw [hs0]
          refine ⟨rfl, rfl, ?_, ?_⟩
          · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self h3]
          · rw [List.getElem?_set_self (by simp [h4])]
        · have hs0 : (st.vals.set lit.toNat 0#32).set (lit.toNat ^^^ 1) 0#32 =
              (st.vals.set (2 * v + 1) 0#32).set (2 * v) 0#32 := by
            rw [h1a]; exact congrArg (fun a => (st.vals.set a 0#32).set (2 * v) 0#32) h0a
          rw [hs0]
          refine ⟨rfl, rfl, ?_, ?_⟩
          · rw [List.getElem?_set_self (by simp [h3])]
          · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self h4]
      · have hnone_old : ¬ ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = w := by
          rintro ⟨i, hi, hiw⟩
          by_cases hil : i < te.toNat - 1
          · exact hnone ⟨i, hil, hiw⟩
          · have hieq : i = te.toNat - 1 := by omega
            subst hieq
            rw [List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length),
              Option.getD_some] at hiw
            exact hwv hiw.symm
        have hold := hbt.cleared_var w hw hnone_old
        rcases hl_xor with ⟨h0a, h1a⟩ | ⟨h0a, h1a⟩ <;>
          · have hl_v0 : lit.toNat ≠ 2 * w := by omega
            have hl_v1 : lit.toNat ≠ 2 * w + 1 := by omega
            have hnl_v0 : lit.toNat ^^^ 1 ≠ 2 * w := by omega
            have hnl_v1 : lit.toNat ^^^ 1 ≠ 2 * w + 1 := by omega
            rw [hlvl_st, hrsn_st, hvals_st, List.getElem?_set_ne (Ne.symm hwv),
              List.getElem?_set_ne (Ne.symm hwv),
              List.getElem?_set_ne hnl_v0, List.getElem?_set_ne hl_v0,
              List.getElem?_set_ne hnl_v1, List.getElem?_set_ne hl_v1]
            exact hold
    · intro i hi1 hi2
      rw [hte_sub] at hi1
      by_cases hie : i = te.toNat - 1
      · subst hie
        have htrl1 : (ks.trl[te.toNat - 1]?.getD 0#32).toNat / 2 = v := by
          rw [List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length),
            Option.getD_some]
        have hk := hbt.kept_var v hv_lt ⟨te.toNat - 1, Nat.sub_lt hpos Nat.one_pos, htrl1⟩
        rw [htrl1] at hpop
        rw [htrl1, ← hk.1]
        exact hpop
      · exact hbt.popped_gt i (by omega) hi2
  exact ⟨hmk none, fun qs => hmk (some qs)⟩

theorem bt_loopInv_finish {acap : Nat} {ks : KittenState} {target_lvl te : BitVec 32}
    {st : KittenState} (hinv : ks.Inv acap) (hbt : BtLoopInv acap ks target_lvl te st)
    (hsync_below : ∀ i < ks.trl_end.toNat,
      (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat →
      let l := (ks.trl[i]?.getD 0#32).toNat
      ks.vals[l]? = some 1#32 ∧ ks.vals[l ^^^ 1]? = some 2#32)
    (hexit : te = 0#32 ∨
      ∃ i < te.toNat, i = te.toNat - 1 ∧
        (st.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat) :
    let prop' := if te.toNat < st.prop.toNat then te else st.prop
    let ks' := ((st.putHdr .trl_end te).putHdr .prop prop').putHdr .lvl target_lvl
    ks'.Inv acap ∧ KittenTrailSynced ks' ∧ ks'.lvl = target_lvl ∧
    ks'.trl_end.toNat ≤ ks.trl_end.toNat ∧
    ks'.trl.take ks'.trl_end.toNat = ks.trl.take ks'.trl_end.toNat ∧
    KittenBtPreserved ks ks' ∧
    (∀ d ∈ kittenTrailDecisions ks', ∃ i < ks'.trl_end.toNat,
      (ks.trl[i]?.getD 0#32).toNat = d ∧ d ∈ kittenTrailDecisions ks) := by
  intro prop' ks'
  have hnv := hinv.clauses.nv_le
  have hsh' : ks'.ShapesOk acap := ((hbt.sh.putHdr .trl_end _).putHdr .prop _).putHdr .lvl _
  have hte := hbt.te_le
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; unfold kMaxV at hnv; omega
  have hlvl_le_all : ∀ i < te.toNat,
      (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat := by
    intro i hi
    rcases hexit with rfl | ⟨j, hj, hj_eq, hlv⟩
    · simp at hi
    · have hk := hbt.kept_var ((ks.trl[j]?.getD 0#32).toNat / 2)
        (by
          have hmem := mem_kittenTrailLits_of_lt (i := j) (by omega) htrl_len
          have := hinv.assign.trl_lt _ hmem; omega)
        ⟨j, hj, rfl⟩
      have hm := hinv.assign.trl_lvl_mono i j (by omega) (by omega)
      rw [hk.1] at hlv; omega
  have e_te : ks'.trl_end = te := by dsimp only [ks']; kp_field
  have e_lvl : ks'.lvl = target_lvl := by dsimp only [ks']; kp_field
  have e_pr : ks'.prop = prop' := by dsimp only [ks']; kp_field
  have e_nv : ks'.nv = ks.nv := by dsimp only [ks']; kp_field; exact hbt.nv_eq
  have e_nc : ks'.nc = ks.nc := by dsimp only [ks']; kp_field; exact hbt.nc_eq
  have e_on : ks'.orig_nc = ks.orig_nc := by dsimp only [ks']; kp_field; exact hbt.orig_eq
  have e_inc : ks'.incons = ks.incons := by dsimp only [ks']; kp_field; exact hbt.inc_eq
  have e_fail : ks'.failing = ks.failing := by dsimp only [ks']; kp_field; exact hbt.fail_eq
  have e_ant : ks'.ante = ks.ante := by dsimp only [ks']; kp_field; exact hbt.ante_eq
  have e_al : ks'.alen = ks.alen := by dsimp only [ks']; kp_field; exact hbt.alen_eq
  have e_ac : ks'.acap = ks.acap := by dsimp only [ks']; kp_field; exact hbt.acap_eq
  have e_na : ks'.nassump = ks.nassump := by dsimp only [ks']; kp_field; exact hbt.na_eq
  have e_nu : ks'.nunits = ks.nunits := by dsimp only [ks']; kp_field; exact hbt.nu_eq
  have e_nr : ks'.nres = ks.nres := by dsimp only [ks']; kp_field; exact hbt.nr_eq
  have e_nk : ks'.nkl = ks.nkl := by dsimp only [ks']; kp_field; exact hbt.nk_eq
  have e_nan : ks'.nana = ks.nana := by dsimp only [ks']; kp_field; exact hbt.nan_eq
  have e_st : ks'.status = ks.status := by dsimp only [ks']; kp_field; exact hbt.st_eq
  have e_ph : ks'.phase = ks.phase := by dsimp only [ks']; kp_field; exact hbt.ph_eq
  have e_ht : ks'.hdrTail = ks.hdrTail := by dsimp only [ks']; kp_field; exact hbt.ht_eq
  have e_trl : ks'.trl = ks.trl := by dsimp only [ks']; kp_field; exact hbt.trl_eq
  have e_fl : ks'.flags = ks.flags := by dsimp only [ks']; kp_field; exact hbt.fl_eq
  have e_ass : ks'.assump = ks.assump := by dsimp only [ks']; kp_field; exact hbt.ass_eq
  have e_ana : ks'.ana = ks.ana := by dsimp only [ks']; kp_field; exact hbt.ana_eq
  have e_kl : ks'.kl = ks.kl := by dsimp only [ks']; kp_field; exact hbt.kl_eq
  have e_uni : ks'.units = ks.units := by dsimp only [ks']; kp_field; exact hbt.uni_eq
  have e_res : ks'.res = ks.res := by dsimp only [ks']; kp_field; exact hbt.res_eq
  have e_wh : ks'.whead = ks.whead := by dsimp only [ks']; kp_field; exact hbt.wh_eq
  have e_wn : ks'.wnext = ks.wnext := by dsimp only [ks']; kp_field; exact hbt.wn_eq
  have e_wb : ks'.wblit = ks.wblit := by dsimp only [ks']; kp_field; exact hbt.wb_eq
  have e_co : ks'.clOff = ks.clOff := by dsimp only [ks']; kp_field; exact hbt.co_eq
  have e_cm : ks'.clMeta = ks.clMeta := by dsimp only [ks']; kp_field; exact hbt.cm_eq
  have e_ca : ks'.clAux = ks.clAux := by dsimp only [ks']; kp_field; exact hbt.ca_eq
  have e_ar : ks'.arena = ks.arena := by dsimp only [ks']; kp_field; exact hbt.ar_eq
  have e_un : ks'.unass = st.unass := by dsimp only [ks']; kp_field
  have e_la : ks'.lvlArr = st.lvlArr := by dsimp only [ks']; kp_field
  have e_rs : ks'.rsn = st.rsn := by dsimp only [ks']; kp_field
  have e_va : ks'.vals = st.vals := by dsimp only [ks']; kp_field
  have horig_eq : kittenOrigClauses ks' = kittenOrigClauses ks :=
    kittenOrigClauses_eq_of e_on fun ci _ => by
      simp only [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta,
        e_co, e_cm, e_ar]
  have hcl_eq : ∀ cid,
      kittenClauseOff ks' cid = kittenClauseOff ks cid ∧
      kittenClauseMeta ks' cid = kittenClauseMeta ks cid ∧
      kittenClauseSize ks' cid = kittenClauseSize ks cid ∧
      kittenClauseIsLrn ks' cid = kittenClauseIsLrn ks cid ∧
      kittenClauseAux ks' cid = kittenClauseAux ks cid ∧
      kittenClauseSpan ks' cid = kittenClauseSpan ks cid ∧
      kittenClauseLits ks' cid = kittenClauseLits ks cid := fun cid =>
    ⟨by simp [kittenClauseOff, e_co], by simp [kittenClauseMeta, e_cm],
     by simp [kittenClauseSize, kittenClauseMeta, e_cm],
     by simp [kittenClauseIsLrn, kittenClauseMeta, e_cm],
     by simp [kittenClauseAux, e_ca],
     by simp [kittenClauseSpan, kittenClauseSize, kittenClauseIsLrn, kittenClauseAux,
       kittenClauseMeta, e_cm, e_ca],
     by simp [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta,
       e_co, e_cm, e_ar]⟩
  have hcl_ants : ∀ cid, kittenClauseAnts ks' cid = kittenClauseAnts ks cid := fun cid => by
    simp [kittenClauseAnts, (hcl_eq cid).2.2.2.1, (hcl_eq cid).1, (hcl_eq cid).2.2.1,
      (hcl_eq cid).2.2.2.2.1, e_ar]
  have hcl' : KittenClausesOk acap ks' :=
    ⟨hinv.clauses.acap_ge, hinv.clauses.acap_lt, by rw [e_ac]; exact hinv.clauses.acap_eq,
      by rw [e_nv]; exact hinv.clauses.nv_le, by rw [e_nc]; exact hinv.clauses.nc_le,
      by rw [e_on, e_nc]; exact hinv.clauses.orig_nc_le,
      by rw [e_on]; exact hinv.clauses.orig_nc_max, by rw [e_al]; exact hinv.clauses.alen_le,
      by rw [e_na]; exact hinv.clauses.nassump_le, by rw [e_nu]; exact hinv.clauses.nunits_le,
      by rw [e_nr]; exact hinv.clauses.nres_le, by rw [e_nk]; exact hinv.clauses.nkl_le,
      by rw [e_nan]; exact hinv.clauses.nana_le,
      by intro cid hcid
         have hw := hinv.clauses.cl_wf cid (by rw [e_nc] at hcid; exact hcid)
         have heq := hcl_eq cid
         rw [heq.2.2.2.1, heq.2.2.1, heq.1, heq.2.2.2.2.2.1, heq.2.2.2.2.2.2, hcl_ants cid,
           List.map_congr_left (fun a _ => (hcl_eq a).2.2.2.2.2.2), e_on, e_al, e_nv, e_ant,
           horig_eq]
         exact hw,
      by intro c1 c2 h12 hc2
         have hcm := hinv.clauses.cl_mono c1 c2 h12 (by rw [← e_nc]; exact hc2)
         rw [(hcl_eq c1).1, (hcl_eq c1).2.2.2.2.2.1, (hcl_eq c2).1]; exact hcm,
      by intro ui hui
         have hu := hinv.clauses.units_ok ui (by rw [e_nu] at hui; exact hui)
         dsimp only; rw [e_uni, e_nc, (hcl_eq _).2.2.1]; exact hu,
      by intro hi
         have hinc := hinv.clauses.incons_ok (by rw [e_inc] at hi; exact hi)
         refine ⟨by rw [e_inc, e_nc]; exact hinc.1, by rw [horig_eq]; exact hinc.2.1,
           fun l hl => ?_⟩
         rw [e_inc, (hcl_eq _).2.2.2.2.2.2] at hl
         have hll := hinc.2.2 l hl
         have hl_lt : l < 2 * ks.nv.toNat :=
           (hinv.clauses.cl_wf _ hinc.1).2.2.2.1 l hl
         have hnz : ks.vals[l]?.getD 0#32 ≠ 0#32 := by simp [hll.1]
         obtain ⟨i, hi_end, hvi⟩ := (hinv.assign.vals_nz_iff_trl l hl_lt).mp hnz
         have hi_te : i < te.toNat := by
           rcases Nat.lt_or_ge i te.toNat with hi_lt | hge
           · exact hi_lt
           · exfalso
             have hgt := hbt.popped_gt i hge hi_end
             rw [hvi] at hgt
             have h0 : ks.lvlArr[l / 2]?.getD 0#32 = 0#32 := hll.2.1
             simp [h0] at hgt
         have hk := hbt.kept_var (l / 2) (by omega) ⟨i, hi_te, hvi⟩
         have hev : st.vals[l]? = ks.vals[l]? := by
           rcases nat_xor1_cases l with ⟨ha, _⟩ | ⟨ha, _⟩
           · exact (congrArg (fun k => st.vals[k]?) ha).trans
               (hk.2.2.1.trans (congrArg (fun k => ks.vals[k]?) ha.symm))
           · exact (congrArg (fun k => st.vals[k]?) ha).trans
               (hk.2.2.2.trans (congrArg (fun k => ks.vals[k]?) ha.symm))
         rw [e_va, hev, e_la, hk.1, e_rs, hk.2.1]
         refine ⟨hll.1, hll.2.1, fun ha => ?_⟩
         have hr := hll.2.2 (by rwa [← e_ant])
         dsimp only at hr ⊢
         rw [e_nc, (hcl_eq _).2.2.2.2.2.2]; exact hr,
      by intro ha hf
         have hfa := hinv.clauses.failing_ok (by rwa [← e_ant]) (by rw [e_fail] at hf; exact hf)
         have hcm_eq : (fun ci => (kittenClauseMeta ks' ci &&& kmCore) != 0#32) =
             (fun ci => (kittenClauseMeta ks ci &&& kmCore) != 0#32) :=
           funext fun ci => by rw [(hcl_eq ci).2.1]
         have hmap_eq : List.map (kittenClauseLits ks') = List.map (kittenClauseLits ks) :=
           congrArg List.map (funext fun ci => (hcl_eq ci).2.2.2.2.2.2)
         unfold kittenAssumpLits at hfa ⊢
         rwa [e_nc, hcm_eq, hmap_eq, e_na, e_ass],
      by intro i hi
         rw [e_ass, e_nv]; exact hinv.clauses.assump_ok i (by rw [e_na] at hi; exact hi),
      by intro v hv
         rw [e_fl]; exact hinv.clauses.flags_clean v (by rw [e_nv] at hv; exact hv)⟩
  have hw' : KittenWatchesOk ks' := by
    obtain ⟨ch, hch1, hch2, hch3, hch4⟩ := hinv.watches
    refine ⟨ch, by rw [e_nv]; exact hch1, hch2, ?_, ?_⟩
    · intro l hl; rw [e_wn, e_wh]; exact hch3 l (by rw [e_nv] at hl; exact hl)
    · intro l hl w hw
      have hb := hch4 l (by rw [e_nv] at hl; exact hl) w hw
      rw [e_nc, e_nv, e_ar, e_wb, (hcl_eq (w / 2)).2.2.1, (hcl_eq (w / 2)).1]; exact hb
  have hsync' : KittenTrailSynced ks' := by
    intro i hi
    rw [e_te] at hi
    rw [e_trl, e_va]
    let l := (ks.trl[i]?.getD 0#32).toNat
    have hl_lt : l < 2 * ks.nv.toNat := hinv.assign.trl_lt l
      (mem_kittenTrailLits_of_lt (i := i) (by omega) htrl_len)
    have hlv := hlvl_le_all i hi
    have hsy := hsync_below i (by omega) hlv
    have hk := hbt.kept_var (l / 2) (by omega) ⟨i, hi, rfl⟩
    change st.vals[l]? = some 1#32 ∧ st.vals[l ^^^ 1]? = some 2#32
    have he1 : st.vals[l]? = ks.vals[l]? := by
      rcases nat_xor1_cases l with ⟨ha, _⟩ | ⟨ha, _⟩
      · exact (congrArg (fun k => st.vals[k]?) ha).trans
          (hk.2.2.1.trans (congrArg (fun k => ks.vals[k]?) ha.symm))
      · exact (congrArg (fun k => st.vals[k]?) ha).trans
          (hk.2.2.2.trans (congrArg (fun k => ks.vals[k]?) ha.symm))
    have he2 : st.vals[l ^^^ 1]? = ks.vals[l ^^^ 1]? := by
      rcases nat_xor1_cases l with ⟨_, hb⟩ | ⟨_, hb⟩
      · exact (congrArg (fun k => st.vals[k]?) hb).trans
          (hk.2.2.2.trans (congrArg (fun k => ks.vals[k]?) hb.symm))
      · exact (congrArg (fun k => st.vals[k]?) hb).trans
          (hk.2.2.1.trans (congrArg (fun k => ks.vals[k]?) hb.symm))
    rw [he1, he2]; exact hsy
  have hba' : KittenBaseAssignOk ks' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e_te, e_nv]; exact Nat.le_trans hte hinv.assign.trl_end_le
    · rw [e_pr, e_te]; dsimp only [prop']; split <;> omega
    · rw [e_un, e_te, e_nv]; exact hbt.unass_eq
    · intro l hl
      rw [e_nv] at hl; rw [e_va]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2
      · have hk := hbt.kept_var (l / 2) (by omega) hex
        have he1 : st.vals[l]? = ks.vals[l]? := by
          rcases nat_xor1_cases l with ⟨ha, _⟩ | ⟨ha, _⟩
          · exact (congrArg (fun k => st.vals[k]?) ha).trans
              (hk.2.2.1.trans (congrArg (fun k => ks.vals[k]?) ha.symm))
          · exact (congrArg (fun k => st.vals[k]?) ha).trans
              (hk.2.2.2.trans (congrArg (fun k => ks.vals[k]?) ha.symm))
        rw [he1]; exact hinv.assign.vals_dom l hl
      · have hc := hbt.cleared_var (l / 2) (by omega) hex
        rcases nat_xor1_cases l with ⟨ha, _⟩ | ⟨ha, _⟩
        · rw [ha, hc.2.2.1]; exact Or.inl rfl
        · rw [ha, hc.2.2.2]; exact Or.inl rfl
    · intro l hl
      rw [e_nv] at hl; rw [e_va]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2
      · have hk := hbt.kept_var (l / 2) (by omega) hex
        have he1 : st.vals[l]? = ks.vals[l]? := by
          rcases nat_xor1_cases l with ⟨ha, _⟩ | ⟨ha, _⟩
          · exact (congrArg (fun k => st.vals[k]?) ha).trans
              (hk.2.2.1.trans (congrArg (fun k => ks.vals[k]?) ha.symm))
          · exact (congrArg (fun k => st.vals[k]?) ha).trans
              (hk.2.2.2.trans (congrArg (fun k => ks.vals[k]?) ha.symm))
        have he2 : st.vals[l ^^^ 1]? = ks.vals[l ^^^ 1]? := by
          rcases nat_xor1_cases l with ⟨_, hb⟩ | ⟨_, hb⟩
          · exact (congrArg (fun k => st.vals[k]?) hb).trans
              (hk.2.2.2.trans (congrArg (fun k => ks.vals[k]?) hb.symm))
          · exact (congrArg (fun k => st.vals[k]?) hb).trans
              (hk.2.2.1.trans (congrArg (fun k => ks.vals[k]?) hb.symm))
        rw [he1, he2]; exact hinv.assign.vals_neg_iff l hl
      · have hc := hbt.cleared_var (l / 2) (by omega) hex
        rcases nat_xor1_cases l with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · have he1 : st.vals[l]? = some 0#32 :=
            (congrArg (fun k => st.vals[k]?) ha).trans hc.2.2.1
          have he2 : st.vals[l ^^^ 1]? = some 0#32 :=
            (congrArg (fun k => st.vals[k]?) hb).trans hc.2.2.2
          simp [he1, he2]
        · have he1 : st.vals[l]? = some 0#32 :=
            (congrArg (fun k => st.vals[k]?) ha).trans hc.2.2.2
          have he2 : st.vals[l ^^^ 1]? = some 0#32 :=
            (congrArg (fun k => st.vals[k]?) hb).trans hc.2.2.1
          simp [he1, he2]
    · intro l hl
      rw [e_nv] at hl; rw [e_va, e_te, e_trl]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2
      · constructor
        · intro _; exact hex
        · intro _
          obtain ⟨i, hi, hiv⟩ := hex
          have hsync_i := hsync' i (by rw [e_te]; exact hi)
          rw [e_va, e_trl] at hsync_i
          let li := (ks.trl[i]?.getD 0#32).toNat
          have hli_lt : li < 2 * ks.nv.toNat := hinv.assign.trl_lt li
            (mem_kittenTrailLits_of_lt (i := i) (by omega) htrl_len)
          have hll : l = li ∨ l = li ^^^ 1 := by
            rcases nat_xor1_cases l with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>
              rcases nat_xor1_cases li with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ <;> omega
          rcases hll with rfl | rfl
          · rw [hsync_i.1]; simp
          · rw [hsync_i.2]; simp
      · have hc := hbt.cleared_var (l / 2) (by omega) hex
        constructor
        · intro hnz
          rcases nat_xor1_cases l with ⟨ha, _⟩ | ⟨ha, _⟩
          · rw [ha, hc.2.2.1] at hnz; simp at hnz
          · rw [ha, hc.2.2.2] at hnz; simp at hnz
        · intro hx; exact absurd hx hex
    · unfold kittenTrailLits
      rw [e_te, e_trl]
      have htake : ks.trl.take te.toNat = (ks.trl.take ks.trl_end.toNat).take te.toNat := by
        rw [List.take_take, Nat.min_eq_left hte]
      rw [htake, List.map_take, List.map_take]
      exact List.Nodup.sublist (List.take_sublist _ _) hinv.assign.trl_nodup
    · intro l hl
      unfold kittenTrailLits at hl
      rw [e_nv]; rw [e_te, e_trl] at hl
      rw [List.mem_map] at hl
      obtain ⟨b, hb, rfl⟩ := hl
      rw [List.mem_take_iff_getElem] at hb
      obtain ⟨i, hi, hget⟩ := hb
      have hi1 : i < ks.trl_end.toNat := by omega
      have hb' : b ∈ ks.trl.take ks.trl_end.toNat := by
        rw [List.mem_take_iff_getElem]; exact ⟨i, by omega, hget⟩
      exact hinv.assign.trl_lt _ (List.mem_map.mpr ⟨b, hb', rfl⟩)
    · intro v hv
      rw [e_nv] at hv; rw [e_la, e_lvl]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = v
      · obtain ⟨i, hi, hiv⟩ := hex
        have hk := hbt.kept_var v hv ⟨i, hi, hiv⟩
        rw [hk.1, ← hiv]; exact hlvl_le_all i hi
      · rw [(hbt.cleared_var v hv hex).1]; simp
    · intro v hv hv0
      rw [e_nv] at hv; rw [e_va] at hv0; rw [e_la, e_rs]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = v
      · exfalso
        obtain ⟨i, hi, hiv⟩ := hex
        have hsy := hsync' i (by rw [e_te]; exact hi)
        rw [e_va, e_trl] at hsy
        let li := (ks.trl[i]?.getD 0#32).toNat
        have hli_lt : li < 2 * ks.nv.toNat := hinv.assign.trl_lt li
          (mem_kittenTrailLits_of_lt (i := i) (by omega) htrl_len)
        rcases nat_xor1_cases li with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · have h2v : 2 * v = li := by omega
          rw [h2v, hsy.1] at hv0; cases hv0
        · have h2v : 2 * v = li ^^^ 1 := by omega
          rw [h2v, hsy.2] at hv0; cases hv0
      · have hc := hbt.cleared_var v hv hex
        exact ⟨by rw [hc.1]; rfl, by rw [hc.2.1]; rfl⟩
    · intro i j hij hj
      rw [e_te] at hj; rw [e_trl, e_la]
      have hli := hinv.assign.trl_lt _ (mem_kittenTrailLits_of_lt (i := i) (by omega) htrl_len)
      have hlj := hinv.assign.trl_lt _ (mem_kittenTrailLits_of_lt (i := j) (by omega) htrl_len)
      have hki := hbt.kept_var ((ks.trl[i]?.getD 0#32).toNat / 2) (by omega) ⟨i, by omega, rfl⟩
      have hkj := hbt.kept_var ((ks.trl[j]?.getD 0#32).toNat / 2) (by omega) ⟨j, by omega, rfl⟩
      rw [hki.1, hkj.1]
      exact hinv.assign.trl_lvl_mono i j hij (by omega)
    · intro i j hji hi heq
      rw [e_te] at hi; rw [e_trl, e_la] at heq; rw [e_trl, e_rs]
      have hli := hinv.assign.trl_lt _ (mem_kittenTrailLits_of_lt (i := i) (by omega) htrl_len)
      have hlj := hinv.assign.trl_lt _ (mem_kittenTrailLits_of_lt (i := j) (by omega) htrl_len)
      have hki := hbt.kept_var ((ks.trl[i]?.getD 0#32).toNat / 2) (by omega) ⟨i, by omega, rfl⟩
      have hkj := hbt.kept_var ((ks.trl[j]?.getD 0#32).toNat / 2) (by omega) ⟨j, by omega, rfl⟩
      rw [hki.1, hkj.1] at heq; rw [hki.2.1]
      exact hinv.assign.dec_earliest i j hji (by omega) heq
    · intro i hi l hlv
      rw [e_te] at hi
      dsimp only [l] at hlv ⊢
      rw [e_trl, e_la] at hlv
      rw [e_trl, e_rs, e_va]
      have hli := hinv.assign.trl_lt _ (mem_kittenTrailLits_of_lt (i := i) (by omega) htrl_len)
      let li := (ks.trl[i]?.getD 0#32).toNat
      have hk := hbt.kept_var (li / 2) (by omega) ⟨i, hi, rfl⟩
      rw [hk.1] at hlv
      have h0 := hinv.assign.lvl0_ok i (by omega) hlv
      have he1 : st.vals[li]? = ks.vals[li]? := by
        rcases nat_xor1_cases li with ⟨ha, _⟩ | ⟨ha, _⟩
        · exact (congrArg (fun k => st.vals[k]?) ha).trans
            (hk.2.2.1.trans (congrArg (fun k => ks.vals[k]?) ha.symm))
        · exact (congrArg (fun k => st.vals[k]?) ha).trans
            (hk.2.2.2.trans (congrArg (fun k => ks.vals[k]?) ha.symm))
      have he2 : st.vals[li ^^^ 1]? = ks.vals[li ^^^ 1]? := by
        rcases nat_xor1_cases li with ⟨_, hb⟩ | ⟨_, hb⟩
        · exact (congrArg (fun k => st.vals[k]?) hb).trans
            (hk.2.2.2.trans (congrArg (fun k => ks.vals[k]?) hb.symm))
        · exact (congrArg (fun k => st.vals[k]?) hb).trans
            (hk.2.2.1.trans (congrArg (fun k => ks.vals[k]?) hb.symm))
      rw [hk.2.1, horig_eq, he1, he2]
      refine ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1, fun ha => ?_⟩
      have hr := h0.2.2.2.2 (by rwa [← e_ant])
      dsimp only at hr ⊢
      rw [e_nc, (hcl_eq _).2.2.2.2.2.2]; exact hr
  have hrsn' : ReasonOk ks' := by
    intro i hi
    rw [e_te] at hi
    change _ = 0xFFFFFFFF#32 ∨ _
    rw [e_trl, e_rs, e_nc]
    have hli := hinv.assign.trl_lt _ (mem_kittenTrailLits_of_lt (i := i) (by omega) htrl_len)
    have hk := hbt.kept_var ((ks.trl[i]?.getD 0#32).toNat / 2) (by omega) ⟨i, hi, rfl⟩
    have hro := hinv.reasons i (by omega)
    dsimp only at hro
    have hr_eq : ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 =
        st.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 := by rw [hk.2.1]
    rw [← hr_eq]
    simpa only [(hcl_eq _).2.2.2.2.2.2] using hro
  have hpres : KittenBtPreserved ks ks' :=
    ⟨e_nv, e_nc, e_on, e_inc, e_fail, e_ant, e_al, e_ac, e_na, e_nu, e_nr, e_nk, e_nan,
      e_st, e_ph, e_ht, e_ass, e_ana, e_kl, e_uni, e_res, e_wh, e_wn, e_wb, e_co, e_cm, e_ca,
      e_ar, (fun v _ => by rw [e_fl]), fun i hi => by
        rw [e_te] at hi; rw [e_trl, e_la]
        have hli := hinv.assign.trl_lt _ (mem_kittenTrailLits_of_lt (i := i) (by omega) htrl_len)
        exact (hbt.kept_var ((ks.trl[i]?.getD 0#32).toNat / 2) (by omega) ⟨i, hi, rfl⟩).1⟩
  refine ⟨⟨hsh', hcl', hw', hba', hrsn'⟩, hsync', e_lvl, by rw [e_te]; exact hte, ?_, hpres, ?_⟩
  · rw [e_te, e_trl]
  · intro d hd
    have hte_len' : ks'.trl_end.toNat ≤ ks'.trl.length := by
      rw [hsh'.trl_len]; have := hba'.trl_end_le; rw [← e_nv] at hnv; unfold kMaxV at hnv; omega
    obtain ⟨i, hi, rfl, hdr⟩ := (mem_kittenTrailDecisions_iff hte_len').mp hd
    rw [e_te] at hi; rw [e_trl] at hdr ⊢
    have hli := hinv.assign.trl_lt _ (mem_kittenTrailLits_of_lt (i := i) (by omega) htrl_len)
    have hk := hbt.kept_var ((ks.trl[i]?.getD 0#32).toNat / 2) (by omega) ⟨i, hi, rfl⟩
    rw [e_rs, hk.2.1] at hdr
    exact ⟨i, by rw [e_te]; exact hi, rfl,
      (mem_kittenTrailDecisions_iff htrl_len).mpr ⟨i, by omega, rfl, hdr⟩⟩

/-! ### Init Preservation Lemma -/

theorem init_finish_inv {acap : Nat} {ks : KittenState} {nv : BitVec 32}
    (hsh : ks.ShapesOk acap) (hge : kMinScratchCap - kBase - kSlabFixed ≤ acap)
    (hlt : acap < dimacsBound) (hnv_le : nv.toNat ≤ kMaxV)
    (e_nv : ks.nv = nv) (e_nc : ks.nc = 0#32) (e_on : ks.orig_nc = 0#32)
    (_e_lvl : ks.lvl = 0#32) (e_pr : ks.prop = 0#32) (e_te : ks.trl_end = 0#32)
    (e_un : ks.unass = nv) (e_ac : ks.acap = BitVec.ofNat 32 acap)
    (e_al : ks.alen = 0#32) (e_inc : ks.incons = 0xFFFFFFFF#32)
    (e_fail : ks.failing = 0xFFFFFFFF#32)
    (e_na : ks.nassump = 0#32) (e_nu : ks.nunits = 0#32) (e_nr : ks.nres = 0#32)
    (e_nk : ks.nkl = 0#32) (e_nan : ks.nana = 0#32)
    (hvars : ∀ v < nv.toNat, ks.lvlArr[v]? = some 0#32 ∧
      ks.rsn[v]? = some 0xFFFFFFFF#32 ∧ ks.flags[v]? = some 0#32)
    (hlits : ∀ l < 2 * nv.toNat, ks.vals[l]? = some 0#32 ∧ ks.whead[l]? = some 0xFFFFFFFF#32) :
    ks.Inv acap ∧ KittenTrailSynced ks ∧
    kittenOrigClauses ks = [] ∧ kittenAssumpLits ks = [] := by
  have hcl : KittenClausesOk acap ks := by
    refine ⟨hge, hlt, e_ac, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e_nv]; exact hnv_le
    · rw [e_nc]; decide
    · rw [e_on, e_nc]; exact Nat.le_refl _
    · rw [e_on]; decide
    · rw [e_al]; simp
    · rw [e_na]; decide
    · rw [e_nu]; decide
    · rw [e_nr]; decide
    · rw [e_nk]; decide
    · rw [e_nan]; decide
    · intro cid hc; rw [e_nc] at hc; simp at hc
    · intro _ _ _ hc; rw [e_nc] at hc; simp at hc
    · intro ui hu; rw [e_nu] at hu; simp at hu
    · intro hi; exact absurd e_inc hi
    · intro _ hf; exact absurd e_fail hf
    · intro i hi; rw [e_na] at hi; simp at hi
    · intro v hv; rw [e_nv] at hv; simp [(hvars v hv).2.2]
  have hw : KittenWatchesOk ks := by
    let ch : List (List Nat) := List.replicate (2 * nv.toNat) []
    refine ⟨ch, by simp [ch, e_nv], ?_, ?_, ?_⟩
    · simp only [ch, List.flatten_replicate_nil]; exact List.nodup_nil
    · intro l hl
      rw [e_nv] at hl
      have hch_l : l < ch.length := by simp only [ch, List.length_replicate]; exact hl
      have hch_e : ch[l]'hch_l = [] := by simp [ch]
      rw [List.getElem?_eq_getElem hch_l, Option.getD_some, hch_e]
      rw [(hlits l hl).2]
      exact WChain.nil
    · intro l hl w hw
      rw [e_nv] at hl
      have hch_l : l < ch.length := by simp only [ch, List.length_replicate]; exact hl
      have hch_e : ch[l]'hch_l = [] := by simp [ch]
      rw [List.getElem?_eq_getElem hch_l, Option.getD_some, hch_e] at hw
      nomatch hw
  have hba : KittenBaseAssignOk ks := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e_te]; simp
    · rw [e_pr, e_te]; exact Nat.le_refl _
    · rw [e_un, e_te, e_nv]; simp
    · intro l hl; rw [e_nv] at hl; rw [(hlits l hl).1]; exact Or.inl rfl
    · intro l hl; rw [e_nv] at hl
      have hnl : (l ^^^ 1) < 2 * nv.toNat := by
        rcases nat_xor1_cases l with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
      rw [(hlits l hl).1, (hlits (l ^^^ 1) hnl).1]; simp
    · intro l hl; rw [e_nv] at hl; rw [(hlits l hl).1, e_te]; simp
    · unfold kittenTrailLits; rw [e_te]; simp
    · intro l hl; unfold kittenTrailLits at hl; rw [e_te] at hl; simp at hl
    · intro v hv; rw [e_nv] at hv; rw [(hvars v hv).1]; simp
    · intro v hv _; rw [e_nv] at hv; exact ⟨by rw [(hvars v hv).1]; rfl,
        by rw [(hvars v hv).2.1]; rfl⟩
    · intro i j _ hj; rw [e_te] at hj; simp at hj
    · intro i _ _ hi; rw [e_te] at hi; simp at hi
    · intro i hi; rw [e_te] at hi; simp at hi
  have hsync : KittenTrailSynced ks := fun i hi => by rw [e_te] at hi; simp at hi
  have hrsn : ReasonOk ks := fun i hi => by rw [e_te] at hi; simp at hi
  have ho : kittenOrigClauses ks = [] := by unfold kittenOrigClauses; rw [e_on]; simp
  have ha : kittenAssumpLits ks = [] := by unfold kittenAssumpLits; rw [e_na]; simp
  exact ⟨⟨hsh, hcl, hw, hba, hrsn⟩, hsync, ho, ha⟩

/-! ### `add_clause` & `assign` Preservation Lemmas -/

private theorem flags_or1_clean (x : BitVec 32) (h : (x &&& 2#32) = 0#32) :
    ((x ||| 1#32) &&& 2#32) = 0#32 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have h1 := congrArg (fun b : BitVec 32 => b[i]) h
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero] at h1 ⊢
  by_cases hbi : (2#32 : BitVec 32)[i] = true
  · have hxi : x[i] = false := by simpa [hbi] using h1
    simp [hxi, bv32_bit2_not_bit1 ⟨i, hi⟩ hbi]
  · simp [Bool.eq_false_iff.mpr hbi]

private theorem flags_andnot1_clean (x : BitVec 32) (h : (x &&& 2#32) = 0#32) :
    ((x &&& ~~~1#32) &&& 2#32) = 0#32 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have h1 := congrArg (fun b : BitVec 32 => b[i]) h
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero] at h1 ⊢
  by_cases hbi : (2#32 : BitVec 32)[i] = true
  · have hxi : x[i] = false := by simpa [hbi] using h1
    simp [hxi]
  · simp [Bool.eq_false_iff.mpr hbi]

private theorem bv32_lt2p16_and_core_zero (sz : BitVec 32) (h : sz.toNat < 2 ^ 16) :
    (sz &&& kmCore) = 0#32 := by
  unfold kmCore
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_zero]
  by_cases hi16 : i = 16
  · subst hi16
    have hs16 : sz[16] = false := by
      rw [BitVec.getElem_eq_testBit_toNat]
      exact Nat.testBit_lt_two_pow h
    simp [hs16]
  · have hk16 : (0x10000#32 : BitVec 32)[i] = false := by revert i hi16; decide
    simp [hk16]

theorem failingOk_append_nonCore {ks ks' : KittenState}
    (hnc : ks'.nc.toNat = ks.nc.toNat + 1)
    (hfail : ks'.failing = ks.failing) (hna : ks'.nassump = ks.nassump)
    (hass : ks'.assump = ks.assump)
    (hcm_new : (kittenClauseMeta ks' ks.nc.toNat &&& kmCore) = 0#32)
    (hold : ∀ c < ks.nc.toNat,
      kittenClauseMeta ks' c = kittenClauseMeta ks c ∧
      kittenClauseLits ks' c = kittenClauseLits ks c)
    (hprev : ks.failing ≠ 0xFFFFFFFF#32 →
      (cnfOfClauses (((List.range ks.nc.toNat).filter fun ci =>
        (kittenClauseMeta ks ci &&& kmCore) != 0#32).map (kittenClauseLits ks)) ++
        unitsCnf (kittenAssumpLits ks)).Unsat) :
    ks'.failing ≠ 0xFFFFFFFF#32 →
    (cnfOfClauses (((List.range ks'.nc.toNat).filter fun ci =>
      (kittenClauseMeta ks' ci &&& kmCore) != 0#32).map (kittenClauseLits ks')) ++
      unitsCnf (kittenAssumpLits ks')).Unsat := by
  intro hf
  have hf0 := hprev (by rwa [← hfail])
  have hr : (List.range ks'.nc.toNat).filter
      (fun ci => (kittenClauseMeta ks' ci &&& kmCore) != 0#32) =
      (List.range ks.nc.toNat).filter
        (fun ci => (kittenClauseMeta ks ci &&& kmCore) != 0#32) := by
    rw [hnc, List.range_succ, List.filter_append, List.filter_cons]
    simp only [hcm_new, bne_self_eq_false, Bool.false_eq_true, ite_false, List.filter_nil,
      List.append_nil]
    exact List.filter_congr fun i hi => by rw [List.mem_range] at hi; rw [(hold i hi).1]
  have hm : ((List.range ks'.nc.toNat).filter
      (fun ci => (kittenClauseMeta ks' ci &&& kmCore) != 0#32)).map (kittenClauseLits ks') =
      ((List.range ks.nc.toNat).filter
        (fun ci => (kittenClauseMeta ks ci &&& kmCore) != 0#32)).map (kittenClauseLits ks) := by
    rw [hr]
    refine List.map_congr_left fun i hi => ?_
    rw [List.mem_filter, List.mem_range] at hi
    exact (hold i hi.1).2
  unfold kittenAssumpLits at *
  rwa [hm, hna, hass]

theorem kittenAssignStep_preserves_clauses {acap : Nat} {ks : KittenState}
    (hsh : ks.ShapesOk acap) (hcl : KittenClausesOk acap ks)
    (hinc : ks.incons = 0xFFFFFFFF#32)
    {lit rsn : BitVec 32} (hlit : lit.toNat < 2 * ks.nv.toNat) :
    KittenClausesOk acap (kittenAssignStep ks lit rsn) := by
  have hnv := hcl.nv_le
  unfold kMaxV at hnv
  have hv_lt : (lit >>> 1).toNat < ks.nv.toNat := (bv32_lit_div2_bv hlit).2
  have hfl : (lit >>> 1).toNat < ks.flags.length := by
    rw [hsh.flags_len]; omega
  refine ⟨hcl.acap_ge, hcl.acap_lt, hcl.acap_eq, hcl.nv_le, hcl.nc_le, hcl.orig_nc_le,
    hcl.orig_nc_max, hcl.alen_le, hcl.nassump_le, hcl.nunits_le, hcl.nres_le, hcl.nkl_le,
    hcl.nana_le, hcl.cl_wf, hcl.cl_mono, hcl.units_ok, fun hi => absurd hinc hi,
    hcl.failing_ok, hcl.assump_ok, ?_⟩
  intro v hv
  dsimp only [kittenAssignStep]
  change (ks.flags.set (lit >>> 1).toNat
    (if (lit &&& 1#32) ≠ 0#32 then ks.flags[(lit >>> 1).toNat]?.getD 0#32 ||| 1#32
      else ks.flags[(lit >>> 1).toNat]?.getD 0#32 &&& ~~~1#32))[v]?.getD 0#32 &&& 2#32 = 0#32
  by_cases hvq : v = (lit >>> 1).toNat
  · subst hvq
    have hclean := hcl.flags_clean _ hv
    rw [List.getElem?_set_self hfl, Option.getD_some]
    split
    · exact flags_or1_clean _ hclean
    · exact flags_andnot1_clean _ hclean
  · rw [List.getElem?_set_ne (Ne.symm hvq)]; exact hcl.flags_clean v hv

theorem kittenAssignStep_preserves_watches {ks : KittenState}
    (hw : KittenWatchesOk ks) (lit rsn : BitVec 32) :
    KittenWatchesOk (kittenAssignStep ks lit rsn) := hw

theorem addClause_empty_preserves {acap : Nat} {ks : KittenState} {cid : BitVec 32}
    (hinv : ks.Inv acap) (_hsync : KittenTrailSynced ks)
    (hlvl0 : ks.lvl = 0#32) (hte0 : ks.trl_end = 0#32) (heq_nc : ks.nc = ks.orig_nc)
    (hnc : ks.nc.toNat < kMaxOrig) :
    let nc := ks.nc
    let off := ks.alen
    let st0 := ((ks.putArr .clOff nc.toNat off).putArr .clMeta nc.toNat 0#32).putArr
      .clAux nc.toNat cid
    let st1 := if ks.incons == 0xFFFFFFFF#32 then st0.putHdr .incons nc else st0
    let ks' := (st1.putHdr .nc (nc + 1#32)).putHdr .orig_nc (nc + 1#32)
    ks'.Inv acap ∧ KittenTrailSynced ks' ∧ ks'.lvl = 0#32 ∧ ks'.trl_end = 0#32 ∧
    ks'.nc = ks'.orig_nc ∧ ks'.orig_nc = ks.orig_nc + 1#32 ∧
    ks'.clAux[ks.orig_nc.toNat]? = some cid ∧
    (ks'.clMeta[ks.orig_nc.toNat]?.getD 0#32 &&& 0xFFFF#32) = 0#32 ∧
    kittenOrigClauses ks' = kittenOrigClauses ks ++ [[]] ∧
    kittenAssumpLits ks' = kittenAssumpLits ks ∧
    (∀ ci < ks.orig_nc.toNat, ks'.clAux[ci]? = ks.clAux[ci]?) := by
  intro nc off st0 st1 ks'
  have hsh' : ks'.ShapesOk acap := by
    have h0 := ((hinv.shapes.putArr .clOff nc.toNat off).putArr .clMeta nc.toNat 0#32).putArr
      .clAux nc.toNat cid
    have h1 : st1.ShapesOk acap := by
      dsimp only [st1]; split
      · exact h0.putHdr .incons nc
      · exact h0
    exact (h1.putHdr .nc (nc + 1#32)).putHdr .orig_nc (nc + 1#32)
  have hnc_lt : nc.toNat < kMaxCl := by
    dsimp only [nc]; unfold kMaxOrig kMaxCl at *; omega
  have hco_len : nc.toNat < ks.clOff.length := by rw [hinv.shapes.clOff_len]; exact hnc_lt
  have hcm_len : nc.toNat < ks.clMeta.length := by rw [hinv.shapes.clMeta_len]; exact hnc_lt
  have hca_len : nc.toNat < ks.clAux.length := by rw [hinv.shapes.clAux_len]; exact hnc_lt
  have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := by
    unfold kMaxCl at hnc_lt; bv_omega
  have e_nc : ks'.nc = nc + 1#32 := by
    dsimp only [ks', st1, st0]; split <;> kp_field
  have e_on : ks'.orig_nc = nc + 1#32 := by
    dsimp only [ks', st1, st0]; split <;> kp_field
  have e_nv : ks'.nv = ks.nv := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_lvl : ks'.lvl = 0#32 := by
    rw [show ks'.lvl = ks.lvl from by dsimp only [ks', st1, st0]; split <;> kp_field]; exact hlvl0
  have e_pr : ks'.prop = ks.prop := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_te : ks'.trl_end = 0#32 := by
    rw [show ks'.trl_end = ks.trl_end from by dsimp only [ks', st1, st0]; split <;> kp_field]
    exact hte0
  have e_un : ks'.unass = ks.unass := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_ant : ks'.ante = ks.ante := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_al : ks'.alen = ks.alen := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_ac : ks'.acap = ks.acap := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_na : ks'.nassump = ks.nassump := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_nu : ks'.nunits = ks.nunits := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_nr : ks'.nres = ks.nres := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_nk : ks'.nkl = ks.nkl := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_nan : ks'.nana = ks.nana := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_la : ks'.lvlArr = ks.lvlArr := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_rs : ks'.rsn = ks.rsn := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_trl : ks'.trl = ks.trl := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_fl : ks'.flags = ks.flags := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_va : ks'.vals = ks.vals := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_ass : ks'.assump = ks.assump := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_uni : ks'.units = ks.units := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_wh : ks'.whead = ks.whead := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_wn : ks'.wnext = ks.wnext := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_wb : ks'.wblit = ks.wblit := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_ar : ks'.arena = ks.arena := by dsimp only [ks', st1, st0]; split <;> kp_field
  have e_co : ks'.clOff = ks.clOff.set nc.toNat off := by
    dsimp only [ks', st1, st0]; split <;> kp_field
  have e_cm : ks'.clMeta = ks.clMeta.set nc.toNat 0#32 := by
    dsimp only [ks', st1, st0]; split <;> kp_field
  have e_ca : ks'.clAux = ks.clAux.set nc.toNat cid := by
    dsimp only [ks', st1, st0]; split <;> kp_field
  have e_inc : ks'.incons = (if ks.incons == 0xFFFFFFFF#32 then nc else ks.incons) := by
    by_cases h : ks.incons = 0xFFFFFFFF#32
    · have hb : (ks.incons == 0xFFFFFFFF#32) = true := beq_iff_eq.mpr h
      dsimp only [ks', st1, st0]; simp only [hb, ite_true]; kp_field
    · have hb : (ks.incons == 0xFFFFFFFF#32) = false := beq_false_of_ne h
      dsimp only [ks', st1, st0]; simp only [hb, Bool.false_eq_true, ite_false]; kp_field
  have e_fail : ks'.failing = ks.failing := by dsimp only [ks', st1, st0]; split <;> kp_field
  have hcl_old : ∀ c < nc.toNat, kittenClauseOff ks' c = kittenClauseOff ks c ∧
      kittenClauseMeta ks' c = kittenClauseMeta ks c ∧
      kittenClauseSize ks' c = kittenClauseSize ks c ∧
      kittenClauseIsLrn ks' c = kittenClauseIsLrn ks c ∧
      kittenClauseAux ks' c = kittenClauseAux ks c ∧
      kittenClauseSpan ks' c = kittenClauseSpan ks c ∧
      kittenClauseLits ks' c = kittenClauseLits ks c := by
    intro c hc
    have hne : nc.toNat ≠ c := by omega
    simp [kittenClauseOff, kittenClauseMeta, kittenClauseSize, kittenClauseIsLrn,
      kittenClauseAux, kittenClauseSpan, kittenClauseLits, e_co, e_cm, e_ca, e_ar,
      List.getElem?_set_ne hne]
  have hcl_new : kittenClauseOff ks' nc.toNat = off.toNat ∧
      kittenClauseMeta ks' nc.toNat = 0#32 ∧
      kittenClauseSize ks' nc.toNat = 0 ∧
      kittenClauseIsLrn ks' nc.toNat = false ∧
      kittenClauseSpan ks' nc.toNat = 0 ∧
      kittenClauseLits ks' nc.toNat = [] := by
    have hco : ks'.clOff[nc.toNat]? = some off := by
      rw [e_co, List.getElem?_set_self hco_len]
    have hcm : ks'.clMeta[nc.toNat]? = some 0#32 := by
      rw [e_cm, List.getElem?_set_self hcm_len]
    simp [kittenClauseOff, kittenClauseMeta, kittenClauseSize, kittenClauseIsLrn,
      kittenClauseSpan, kittenClauseLits, hco, hcm]
  have horig : kittenOrigClauses ks' = kittenOrigClauses ks ++ [[]] := by
    unfold kittenOrigClauses
    rw [e_on, hnc1, List.range_succ, List.map_append, List.map_singleton, ← heq_nc]
    have hm1 : (List.range nc.toNat).map (kittenClauseLits ks') =
        (List.range nc.toNat).map (kittenClauseLits ks) := by
      refine List.map_congr_left fun i hi => ?_
      rw [List.mem_range] at hi; exact (hcl_old i hi).2.2.2.2.2.2
    rw [hm1, hcl_new.2.2.2.2.2]
  have hass : kittenAssumpLits ks' = kittenAssumpLits ks := by
    unfold kittenAssumpLits; rw [e_na, e_ass]
  have hnc_def : nc = ks.nc := rfl
  have hoff_def : off = ks.alen := rfl
  have hcl' : KittenClausesOk acap ks' := by
    refine ⟨hinv.clauses.acap_ge, hinv.clauses.acap_lt, by rw [e_ac]; exact hinv.clauses.acap_eq,
      by rw [e_nv]; exact hinv.clauses.nv_le,
      (by rw [e_nc, hnc1]; unfold kMaxOrig kMaxCl at *; omega),
      by rw [e_on, e_nc]; exact Nat.le_refl _, by rw [e_on, hnc1]; exact hnc,
      by rw [e_al]; exact hinv.clauses.alen_le, by rw [e_na]; exact hinv.clauses.nassump_le,
      by rw [e_nu]; exact hinv.clauses.nunits_le, by rw [e_nr]; exact hinv.clauses.nres_le,
      by rw [e_nk]; exact hinv.clauses.nkl_le, by rw [e_nan]; exact hinv.clauses.nana_le,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rw [e_nc, hnc1] at hc
      by_cases hcn : c = nc.toNat
      · subst hcn
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hcl_new.2.2.2.1, e_on, hnc1]; simp
        · intro hge; rw [e_on, hnc1] at hge; omega
        · rw [hcl_new.1, hcl_new.2.2.2.2.1, e_al, hoff_def]; omega
        · intro l hl; rw [hcl_new.2.2.2.2.2] at hl; nomatch hl
        · rw [hcl_new.2.2.2.2.2, horig]
          exact cnfOfClauses_entailsClause_of_mem (by simp)
        · intro _ hge; rw [e_on, hnc1] at hge; omega
      · have hc' : c < ks.nc.toNat := by rw [← hnc_def]; omega
        have hw := hinv.clauses.cl_wf c hc'
        have ho := hcl_old c (by rw [hnc_def]; exact hc')
        refine ⟨?_, fun hge => by rw [e_on, hnc1] at hge; omega,
          by rw [ho.1, ho.2.2.2.2.2.1, e_al]; exact hw.2.2.1,
          fun l hl => by rw [ho.2.2.2.2.2.2] at hl; rw [e_nv]; exact hw.2.2.2.1 l hl,
          ?_, fun _ hge => by rw [e_on, hnc1] at hge; omega⟩
        · rw [ho.2.2.2.1, hw.1, e_on, hnc1]
          have hno1 : ¬ (ks.orig_nc.toNat ≤ c) := by rw [← heq_nc]; omega
          have hno2 : ¬ (nc.toNat + 1 ≤ c) := by rw [hnc_def]; omega
          rw [decide_eq_false hno1, decide_eq_false hno2]
        · rw [ho.2.2.2.2.2.2, horig]
          exact cnfOfClauses_entailsClause_append_left hw.2.2.2.2.1
    · intro c1 c2 h12 hc2
      rw [e_nc, hnc1] at hc2
      have ho1 := hcl_old c1 (by omega)
      by_cases hc2n : c2 = nc.toNat
      · subst hc2n
        rw [ho1.1, ho1.2.2.2.2.2.1, hcl_new.1, hoff_def]
        exact (hinv.clauses.cl_wf c1 (by rw [← hnc_def]; omega)).2.2.1
      · have ho2 := hcl_old c2 (by omega)
        rw [ho1.1, ho1.2.2.2.2.2.1, ho2.1]
        exact hinv.clauses.cl_mono c1 c2 h12 (by rw [← hnc_def]; omega)
    · intro ui hui
      rw [e_nu] at hui
      have hu := hinv.clauses.units_ok ui hui
      rw [e_uni, e_nc, hnc1]
      have ho := hcl_old (ks.units[ui]?.getD 0#32).toNat (by rw [hnc_def]; exact hu.1)
      exact ⟨by rw [hnc_def]; omega, by rw [ho.2.2.1]; exact hu.2⟩
    · intro hi
      have ho_unsat : (cnfOfClauses (kittenOrigClauses ks')).Unsat := by
        rw [horig, CNF.unsat_iff_not_sat]
        intro α hα
        have hc := (cnf_sat_cnfOfClauses_iff α _).mp hα [] (by simp)
        rw [clause_sat_cnfClause_iff] at hc
        obtain ⟨_, hl, _⟩ := hc; nomatch hl
      by_cases hinc0 : ks.incons = 0xFFFFFFFF#32
      · have hb : (ks.incons == 0xFFFFFFFF#32) = true := beq_iff_eq.mpr hinc0
        rw [e_inc, hb, show (if (true = true) then nc else ks.incons) = nc from rfl,
          e_nc, hnc1, hnc_def]
        refine ⟨by omega, ho_unsat, fun l hl => ?_⟩
        rw [hcl_new.2.2.2.2.2] at hl; nomatch hl
      · have hb : (ks.incons == 0xFFFFFFFF#32) = false := beq_false_of_ne hinc0
        rw [e_inc, hb] at hi ⊢; simp only [ite_false, Bool.false_eq_true] at hi ⊢
        have hinc := hinv.clauses.incons_ok hi
        rw [e_nc, hnc1, hnc_def]
        refine ⟨by omega, ho_unsat, fun l hl => ?_⟩
        have ho := hcl_old ks.incons.toNat hinc.1
        rw [ho.2.2.2.2.2.2] at hl
        have hr := hinc.2.2 l hl
        dsimp only at hr ⊢
        rw [e_va, e_la, e_rs]
        refine ⟨hr.1, hr.2.1, fun ha => ?_⟩
        have hrr := hr.2.2 (by rwa [← e_ant])
        rw [(hcl_old _ hrr.1).2.2.2.2.2.2]
        exact ⟨by omega, hrr.2⟩
    · intro ha
      exact failingOk_append_nonCore (by rw [e_nc, hnc1]) e_fail e_na e_ass
        (by rw [hcl_new.2.1]; decide)
        (fun c hc => ⟨(hcl_old c hc).2.1, (hcl_old c hc).2.2.2.2.2.2⟩)
        (hinv.clauses.failing_ok (by rwa [← e_ant]))
    · intro i hi; rw [e_ass, e_nv]; exact hinv.clauses.assump_ok i (by rw [e_na] at hi; exact hi)
    · intro v hv; rw [e_fl]; exact hinv.clauses.flags_clean v (by rw [e_nv] at hv; exact hv)
  have hw' : KittenWatchesOk ks' := by
    obtain ⟨ch, h1, h2, h3, h4⟩ := hinv.watches
    refine ⟨ch, by rw [e_nv]; exact h1, h2, fun l hl => by
        rw [e_wn, e_wh]; exact h3 l (by rw [e_nv] at hl; exact hl),
      fun l hl w hw => ?_⟩
    have hb := h4 l (by rw [e_nv] at hl; exact hl) w hw
    have ho := hcl_old (w / 2) (by rw [hnc_def]; omega)
    rw [e_wb, e_nc, hnc1, e_nv, ho.1, ho.2.2.1, e_ar]
    exact ⟨by rw [hnc_def]; omega, hb.2.1, hb.2.2.1, hb.2.2.2⟩
  have hba' : KittenBaseAssignOk ks' :=
    ⟨by rw [e_te]; simp,
      by rw [e_pr, e_te]; have := hinv.assign.prop_le; rw [hte0] at this; exact this,
      by rw [e_un, e_te, e_nv]; simpa [hte0] using hinv.assign.unass_eq,
      by rw [e_nv, e_va]; exact hinv.assign.vals_dom,
      by rw [e_nv, e_va]; exact hinv.assign.vals_neg_iff,
      by intro l hl; rw [e_nv] at hl; rw [e_va, e_te]; simpa [hte0] using
        hinv.assign.vals_nz_iff_trl l hl,
      by unfold kittenTrailLits; rw [e_te]; simp,
      by intro l hl; unfold kittenTrailLits at hl; rw [e_te] at hl; simp at hl,
      by intro v hv; rw [e_nv] at hv; rw [e_la, e_lvl]; simpa [hlvl0] using
        hinv.assign.trl_lvl_le v hv,
      by intro v hv hv0; rw [e_nv] at hv; rw [e_va] at hv0; rw [e_la, e_rs]
         exact hinv.assign.unass_lvl_zero v hv hv0,
      by intro i j _ hj; rw [e_te] at hj; simp at hj,
      by intro i _ _ hi; rw [e_te] at hi; simp at hi,
      by intro i hi; rw [e_te] at hi; simp at hi⟩
  have hsync' : KittenTrailSynced ks' := fun i hi => by rw [e_te] at hi; simp at hi
  have hrsn' : ReasonOk ks' := fun i hi => by rw [e_te] at hi; simp at hi
  have hca_fin : ks'.clAux[ks.orig_nc.toNat]? = some cid := by
    rw [← heq_nc, e_ca, List.getElem?_set_self hca_len]
  have hcm_fin : (ks'.clMeta[ks.orig_nc.toNat]?.getD 0#32 &&& 0xFFFF#32) = 0#32 := by
    rw [← heq_nc]
    change (kittenClauseMeta ks' nc.toNat &&& 0xFFFF#32) = 0#32
    rw [hcl_new.2.1]; decide
  exact ⟨⟨hsh', hcl', hw', hba', hrsn'⟩, hsync', e_lvl, e_te,
    by rw [e_nc, e_on], by rw [e_on, ← heq_nc], hca_fin, hcm_fin, horig, hass,
    fun ci hci => by rw [e_ca, List.getElem?_set_ne (by dsimp only [nc]; rw [heq_nc]; omega)]⟩

theorem addClause_nonempty_preserves {acap : Nat} {ks : KittenState} {cid : BitVec 32}
    {xs : List (BitVec 32)} {sz : BitVec 32} {ar' : List (BitVec 32)}
    (hinv : ks.Inv acap) (hlvl0 : ks.lvl = 0#32) (hte0 : ks.trl_end = 0#32)
    (heq_nc : ks.nc = ks.orig_nc) (hnc : ks.nc.toNat < kMaxOrig)
    (hsz_pos : 1 ≤ sz.toNat) (hsz_max : sz.toNat < 2 ^ 16) (hsz_xs : sz.toNat ≤ xs.length)
    (hfit : ks.alen.toNat + sz.toNat ≤ ks.acap.toNat)
    (har_len : ar'.length = acap)
    (har_old : ∀ i < ks.alen.toNat, ar'[i]? = ks.arena[i]?)
    (har_new : ∀ i < sz.toNat, ar'[ks.alen.toNat + i]? = xs[i]?)
    (hxlits : ∀ i < sz.toNat, (xs[i]?.getD 0#32).toNat < 2 * ks.nv.toNat) :
    let nc := ks.nc
    let off := ks.alen
    let stBase := { ks with arena := ar' }
    let stMeta := (((((stBase.putHdr .alen (off + sz)).putArr .clOff nc.toNat off).putArr
      .clMeta nc.toNat sz).putArr .clAux nc.toNat cid).putHdr .nc (nc + 1#32)).putHdr
      .orig_nc (nc + 1#32)
    let stUnit := if sz == 1#32 ∧ stMeta.nunits.toNat < 256 then
      (stMeta.putArr .units stMeta.nunits.toNat nc).putHdr .nunits (stMeta.nunits + 1#32)
      else if sz == 1#32 then stMeta else kittenWatchStep stMeta nc (xs[0]!) (xs[1]!)
    stUnit.Inv acap ∧ KittenTrailSynced stUnit ∧ stUnit.lvl = 0#32 ∧ stUnit.trl_end = 0#32 ∧
    stUnit.nc = stUnit.orig_nc ∧ stUnit.orig_nc = ks.orig_nc + 1#32 ∧
    stUnit.ante = ks.ante ∧ stUnit.nassump = ks.nassump ∧
    stUnit.clAux[ks.orig_nc.toNat]? = some cid ∧
    (stUnit.clMeta[ks.orig_nc.toNat]?.getD 0#32 &&& 0xFFFF#32) = sz ∧
    kittenOrigClauses stUnit = kittenOrigClauses ks ++ [(xs.take sz.toNat).map BitVec.toNat] ∧
    kittenAssumpLits stUnit = kittenAssumpLits ks ∧
    (∀ ci < ks.orig_nc.toNat, stUnit.clAux[ci]? = ks.clAux[ci]?) := by
  intro nc off stBase stMeta stUnit
  have hnv := hinv.clauses.nv_le
  have hnc_lt : nc.toNat < kMaxCl := by
    dsimp only [nc]; unfold kMaxOrig kMaxCl at *; omega
  have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := by unfold kMaxCl at hnc_lt; bv_omega
  have har_old_len := hinv.shapes.arena_len
  have hco_len : nc.toNat < ks.clOff.length := by rw [hinv.shapes.clOff_len]; exact hnc_lt
  have hcm_len : nc.toNat < ks.clMeta.length := by rw [hinv.shapes.clMeta_len]; exact hnc_lt
  have hca_len : nc.toNat < ks.clAux.length := by rw [hinv.shapes.clAux_len]; exact hnc_lt
  have hacap_32 : acap < 2 ^ 32 := Nat.lt_trans hinv.clauses.acap_lt (by decide)
  have hca : ks.acap.toNat = acap := by
    rw [hinv.clauses.acap_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hacap_32]
  have hoff_add : (off + sz).toNat = off.toNat + sz.toNat := by
    have hal := hinv.clauses.alen_le
    change (ks.alen + sz).toNat = ks.alen.toNat + sz.toNat; bv_omega
  have hal_le' : off.toNat + sz.toNat ≤ acap := by
    dsimp only [off]; have hal := hinv.clauses.alen_le; omega
  have har_slice_old : ∀ c < nc.toNat,
      kittenClauseLits stBase c = kittenClauseLits ks c := by
    intro c hc
    have hwf := hinv.clauses.cl_wf c hc
    have hal := hinv.clauses.alen_le
    have hspan_bd : kittenClauseOff ks c + kittenClauseSize ks c ≤ ks.alen.toNat := by
      have := hwf.2.2.1; unfold kittenClauseSpan at this; omega
    unfold kittenClauseLits; congr 1
    apply List.ext_getElem
    · have hc1 : kittenClauseOff ks c + kittenClauseSize ks c ≤ ar'.length := by omega
      have hc2 : kittenClauseOff ks c + kittenClauseSize ks c ≤ ks.arena.length := by omega
      simp only [List.length_take, List.length_drop,
        show stBase.clOff = ks.clOff from rfl,
        show stBase.clMeta = ks.clMeta from rfl, show stBase.arena = ar' from rfl,
        kittenClauseOff, kittenClauseSize, kittenClauseMeta]
      omega
    · intro j hj1 hj2
      have hj_sz : j < kittenClauseSize ks c := by simp at hj2; omega
      simp only [List.getElem_take, List.getElem_drop]
      have hidx : kittenClauseOff ks c + j < ks.alen.toNat := by omega
      have ha1 := har_old (kittenClauseOff ks c + j) hidx
      rw [List.getElem?_eq_getElem (by omega : kittenClauseOff ks c + j < ar'.length),
        List.getElem?_eq_getElem (by omega : kittenClauseOff ks c + j < ks.arena.length)] at ha1
      exact Option.some.inj ha1
  have har_slice_new :
      ((ar'.drop off.toNat).take sz.toNat).map BitVec.toNat =
        (xs.take sz.toNat).map BitVec.toNat := by
    congr 1
    apply List.ext_getElem
    · simp [List.length_take, har_len]; omega
    · intro j hj1 _
      have hj : j < sz.toNat := by simp at hj1; omega
      simp only [List.getElem_take, List.getElem_drop]
      have ha1 := har_new j hj
      rw [List.getElem?_eq_getElem (by omega : off.toNat + j < ar'.length),
        List.getElem?_eq_getElem (by omega : j < xs.length)] at ha1
      exact Option.some.inj ha1
  have hsh_meta : stMeta.ShapesOk acap := by
    have h0 : stBase.ShapesOk acap := ⟨hinv.shapes.hdrTail_len, hinv.shapes.lvlArr_len,
      hinv.shapes.rsn_len, hinv.shapes.qprev_len, hinv.shapes.qnext_len, hinv.shapes.qstampArr_len,
      hinv.shapes.trl_len, hinv.shapes.flags_len, hinv.shapes.vals_len, hinv.shapes.assump_len,
      hinv.shapes.ana_len, hinv.shapes.kl_len, hinv.shapes.units_len, hinv.shapes.res_len,
      hinv.shapes.whead_len, hinv.shapes.wnext_len, hinv.shapes.wblit_len, hinv.shapes.clOff_len,
      hinv.shapes.clMeta_len, hinv.shapes.clAux_len, har_len⟩
    exact (((((h0.putHdr .alen (off + sz)).putArr .clOff nc.toNat off).putArr .clMeta nc.toNat sz
      ).putArr .clAux nc.toNat cid).putHdr .nc (nc + 1#32)).putHdr .orig_nc (nc + 1#32)
  have m_nc : stMeta.nc = nc + 1#32 := by dsimp only [stMeta, stBase]; kp_field
  have m_on : stMeta.orig_nc = nc + 1#32 := by dsimp only [stMeta, stBase]; kp_field
  have m_nv : stMeta.nv = ks.nv := by dsimp only [stMeta, stBase]; kp_field
  have m_lvl : stMeta.lvl = ks.lvl := by dsimp only [stMeta, stBase]; kp_field
  have m_pr : stMeta.prop = ks.prop := by dsimp only [stMeta, stBase]; kp_field
  have m_te : stMeta.trl_end = ks.trl_end := by dsimp only [stMeta, stBase]; kp_field
  have m_un : stMeta.unass = ks.unass := by dsimp only [stMeta, stBase]; kp_field
  have m_in : stMeta.incons = ks.incons := by dsimp only [stMeta, stBase]; kp_field
  have m_fa : stMeta.failing = ks.failing := by dsimp only [stMeta, stBase]; kp_field
  have m_an : stMeta.ante = ks.ante := by dsimp only [stMeta, stBase]; kp_field
  have m_al : stMeta.alen = off + sz := by dsimp only [stMeta, stBase]; kp_field
  have m_ac : stMeta.acap = ks.acap := by dsimp only [stMeta, stBase]; kp_field
  have m_na : stMeta.nassump = ks.nassump := by dsimp only [stMeta, stBase]; kp_field
  have m_nu : stMeta.nunits = ks.nunits := by dsimp only [stMeta, stBase]; kp_field
  have m_nr : stMeta.nres = ks.nres := by dsimp only [stMeta, stBase]; kp_field
  have m_nk : stMeta.nkl = ks.nkl := by dsimp only [stMeta, stBase]; kp_field
  have m_nn : stMeta.nana = ks.nana := by dsimp only [stMeta, stBase]; kp_field
  have m_la : stMeta.lvlArr = ks.lvlArr := by dsimp only [stMeta, stBase]; kp_field
  have m_rs : stMeta.rsn = ks.rsn := by dsimp only [stMeta, stBase]; kp_field
  have m_tr : stMeta.trl = ks.trl := by dsimp only [stMeta, stBase]; kp_field
  have m_fl : stMeta.flags = ks.flags := by dsimp only [stMeta, stBase]; kp_field
  have m_va : stMeta.vals = ks.vals := by dsimp only [stMeta, stBase]; kp_field
  have m_as : stMeta.assump = ks.assump := by dsimp only [stMeta, stBase]; kp_field
  have m_un_arr : stMeta.units = ks.units := by dsimp only [stMeta, stBase]; kp_field
  have m_wh : stMeta.whead = ks.whead := by dsimp only [stMeta, stBase]; kp_field
  have m_wn : stMeta.wnext = ks.wnext := by dsimp only [stMeta, stBase]; kp_field
  have m_wb : stMeta.wblit = ks.wblit := by dsimp only [stMeta, stBase]; kp_field
  have m_co : stMeta.clOff = ks.clOff.set nc.toNat off := by
    dsimp only [stMeta, stBase]; kp_field
  have m_cm : stMeta.clMeta = ks.clMeta.set nc.toNat sz := by
    dsimp only [stMeta, stBase]; kp_field
  have m_ca : stMeta.clAux = ks.clAux.set nc.toNat cid := by
    dsimp only [stMeta, stBase]; kp_field
  have m_ar : stMeta.arena = ar' := by dsimp only [stMeta, stBase]; kp_field
  have hcl_old : ∀ c < nc.toNat, kittenClauseOff stMeta c = kittenClauseOff ks c ∧
      kittenClauseMeta stMeta c = kittenClauseMeta ks c ∧
      kittenClauseSize stMeta c = kittenClauseSize ks c ∧
      kittenClauseIsLrn stMeta c = kittenClauseIsLrn ks c ∧
      kittenClauseAux stMeta c = kittenClauseAux ks c ∧
      kittenClauseSpan stMeta c = kittenClauseSpan ks c ∧
      kittenClauseLits stMeta c = kittenClauseLits ks c := by
    intro c hc
    have hne : nc.toNat ≠ c := by omega
    have ho := har_slice_old c hc
    have hco : stMeta.clOff[c]? = ks.clOff[c]? := by rw [m_co, List.getElem?_set_ne hne]
    have hcm : stMeta.clMeta[c]? = ks.clMeta[c]? := by rw [m_cm, List.getElem?_set_ne hne]
    have hca : stMeta.clAux[c]? = ks.clAux[c]? := by rw [m_ca, List.getElem?_set_ne hne]
    refine ⟨by simp [kittenClauseOff, hco], by simp [kittenClauseMeta, hcm],
      by simp [kittenClauseSize, kittenClauseMeta, hcm],
      by simp [kittenClauseIsLrn, kittenClauseMeta, hcm],
      by simp [kittenClauseAux, hca],
      by simp [kittenClauseSpan, kittenClauseSize, kittenClauseIsLrn, kittenClauseAux,
        kittenClauseMeta, hcm, hca],
      by simp only [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta,
        hco, hcm, m_ar] at ⊢; exact ho⟩
  have hsz_mask : (sz &&& 0xFFFF#32) = sz := by
    apply BitVec.eq_of_toNat_eq
    have : (sz &&& 0xFFFF#32).toNat = sz.toNat % 2 ^ 16 := by
      rw [BitVec.toNat_and, show (0xFFFF#32 : BitVec 32).toNat = 2 ^ 16 - 1 by decide]
      simpa using Nat.and_two_pow_sub_one_eq_mod sz.toNat 16
    rw [this, Nat.mod_eq_of_lt hsz_max]
  have hcl_new : kittenClauseOff stMeta nc.toNat = off.toNat ∧
      kittenClauseMeta stMeta nc.toNat = sz ∧
      kittenClauseSize stMeta nc.toNat = sz.toNat ∧
      kittenClauseIsLrn stMeta nc.toNat = false ∧
      kittenClauseSpan stMeta nc.toNat = sz.toNat ∧
      kittenClauseLits stMeta nc.toNat = (xs.take sz.toNat).map BitVec.toNat := by
    have hco : stMeta.clOff[nc.toNat]? = some off := by rw [m_co, List.getElem?_set_self hco_len]
    have hcm : stMeta.clMeta[nc.toNat]? = some sz := by rw [m_cm, List.getElem?_set_self hcm_len]
    have hlrn : (sz &&& kmLrn) = 0#32 := by
      unfold kmLrn
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simp only [BitVec.getElem_and, BitVec.getElem_zero]
      by_cases hi17 : i = 17
      · subst hi17
        have hs17 : sz[17] = false := by
          rw [BitVec.getElem_eq_testBit_toNat]
          exact Nat.testBit_lt_two_pow (Nat.lt_trans hsz_max (by decide))
        simp [hs17]
      · have hk17 : (0x20000#32 : BitVec 32)[i] = false := by revert i hi17; decide
        simp [hk17]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [kittenClauseOff, hco]
    · simp [kittenClauseMeta, hcm]
    · simp [kittenClauseSize, kittenClauseMeta, hcm, hsz_mask]
    · simp [kittenClauseIsLrn, kittenClauseMeta, hcm, hlrn]
    · simp [kittenClauseSpan, kittenClauseSize, kittenClauseIsLrn, kittenClauseMeta, hcm,
        hsz_mask, hlrn]
    · simp only [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta, hco, hcm,
        Option.getD_some, hsz_mask, m_ar]
      exact har_slice_new
  have horig_meta : kittenOrigClauses stMeta =
      kittenOrigClauses ks ++ [(xs.take sz.toNat).map BitVec.toNat] := by
    unfold kittenOrigClauses
    rw [m_on, hnc1, List.range_succ, List.map_append, List.map_singleton, ← heq_nc]
    have hm1 : (List.range nc.toNat).map (kittenClauseLits stMeta) =
        (List.range nc.toNat).map (kittenClauseLits ks) := by
      refine List.map_congr_left fun i hi => ?_
      rw [List.mem_range] at hi; exact (hcl_old i hi).2.2.2.2.2.2
    rw [hm1, hcl_new.2.2.2.2.2]
  have hw_meta : KittenWatchesOk stMeta := by
    obtain ⟨ch, h1, h2, h3, h4⟩ := hinv.watches
    refine ⟨ch, by rw [m_nv]; exact h1, h2, fun l hl => by
        rw [m_wn, m_wh]; exact h3 l (by rw [m_nv] at hl; exact hl),
      fun l hl w hw => ?_⟩
    have hb := h4 l (by rw [m_nv] at hl; exact hl) w hw
    have hw_div : w / 2 < nc.toNat := Nat.div_lt_of_lt_mul hb.1
    have ho := hcl_old (w / 2) hw_div
    have hwf := hinv.clauses.cl_wf (w / 2) hw_div
    have hlt_a : kittenClauseOff ks (w / 2) + w % 2 < ks.alen.toNat := by
      have := hwf.2.2.1; unfold kittenClauseSpan at this; omega
    have har_c : stMeta.arena[kittenClauseOff stMeta (w / 2) + w % 2]? =
        ks.arena[kittenClauseOff ks (w / 2) + w % 2]? := by
      rw [ho.1, m_ar]; exact har_old _ hlt_a
    have hwb_c : stMeta.wblit[w]? = ks.wblit[w]? := by rw [m_wb]
    refine ⟨by rw [m_nc, hnc1]; omega, by rw [ho.2.2.1]; exact hb.2.1,
      by rw [har_c]; exact hb.2.2.1, by rw [hwb_c, m_nv]; exact hb.2.2.2⟩
  have hcl_meta : KittenClausesOk acap stMeta := by
    have hnc_def : nc = ks.nc := rfl
    refine ⟨hinv.clauses.acap_ge, hinv.clauses.acap_lt, by rw [m_ac]; exact hinv.clauses.acap_eq,
      by rw [m_nv]; exact hinv.clauses.nv_le,
      by rw [m_nc, hnc1]; dsimp only [nc]; unfold kMaxOrig kMaxCl at *; omega,
      by rw [m_on, m_nc]; exact Nat.le_refl _,
      by rw [m_on, hnc1]; dsimp only [nc]; exact hnc,
      by rw [m_al, hoff_add]; exact hal_le',
      by rw [m_na]; exact hinv.clauses.nassump_le,
      by rw [m_nu]; exact hinv.clauses.nunits_le,
      by rw [m_nr]; exact hinv.clauses.nres_le,
      by rw [m_nk]; exact hinv.clauses.nkl_le,
      by rw [m_nn]; exact hinv.clauses.nana_le,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rw [m_nc, hnc1] at hc
      by_cases hcn : c = nc.toNat
      · subst hcn
        refine ⟨by rw [hcl_new.2.2.2.1, m_on, hnc1]; simp,
          fun hge => by rw [m_on, hnc1] at hge; omega,
          by rw [hcl_new.1, hcl_new.2.2.2.2.1, m_al, hoff_add]; exact Nat.le_refl _,
          ?_, ?_, fun _ hge => by rw [m_on, hnc1] at hge; omega⟩
        · intro l hl
          rw [hcl_new.2.2.2.2.2, List.mem_map] at hl
          obtain ⟨b, hb, rfl⟩ := hl
          rw [List.mem_take_iff_getElem] at hb
          obtain ⟨i, hi, rfl⟩ := hb
          have hhi := hxlits i (by omega)
          rw [m_nv]; rwa [List.getElem?_eq_getElem (by omega : i < xs.length), Option.getD_some]
            at hhi
        · rw [hcl_new.2.2.2.2.2, horig_meta]
          exact cnfOfClauses_entailsClause_of_mem (by simp)
      · have hc' : c < nc.toNat := by omega
        have hw := hinv.clauses.cl_wf c hc'
        have ho := hcl_old c hc'
        refine ⟨?_, fun hge => by rw [m_on, hnc1] at hge; omega,
          by rw [ho.1, ho.2.2.2.2.2.1, m_al, hoff_add]
             have hbd : kittenClauseOff ks c + kittenClauseSpan ks c ≤ ks.alen.toNat :=
               hw.2.2.1
             dsimp only [off]; omega,
          fun l hl => by rw [ho.2.2.2.2.2.2] at hl; rw [m_nv]; exact hw.2.2.2.1 l hl,
          by rw [ho.2.2.2.2.2.2, horig_meta]
             exact cnfOfClauses_entailsClause_append_left hw.2.2.2.2.1,
          fun _ hge => by rw [m_on, hnc1] at hge; omega⟩
        · rw [ho.2.2.2.1, hw.1, m_on, hnc1]
          have hno1 : ¬ (ks.orig_nc.toNat ≤ c) := by dsimp only [nc] at hc'; rw [← heq_nc]; omega
          have hno2 : ¬ (nc.toNat + 1 ≤ c) := by omega
          rw [decide_eq_false hno1, decide_eq_false hno2]
    · intro c1 c2 h12 hc2
      rw [m_nc, hnc1] at hc2
      have ho1 := hcl_old c1 (by omega)
      by_cases hc2n : c2 = nc.toNat
      · subst hc2n; rw [ho1.1, ho1.2.2.2.2.2.1, hcl_new.1]
        exact (hinv.clauses.cl_wf c1 (by omega)).2.2.1
      · have ho2 := hcl_old c2 (by omega)
        rw [ho1.1, ho1.2.2.2.2.2.1, ho2.1]
        exact hinv.clauses.cl_mono c1 c2 h12 (by rw [← hnc_def]; omega)
    · intro ui hui
      rw [m_nu] at hui
      have hu := hinv.clauses.units_ok ui hui
      rw [m_un_arr]
      have ho := hcl_old (ks.units[ui]?.getD 0#32).toNat hu.1
      exact ⟨by rw [m_nc, hnc1, hnc_def]; omega, by rw [ho.2.2.1]; exact hu.2⟩
    · intro hi
      rw [m_in] at hi
      have hinc := hinv.clauses.incons_ok hi
      refine ⟨by rw [m_in, m_nc, hnc1, hnc_def]; omega, ?_, fun l hl => ?_⟩
      · rw [horig_meta]; exact cnfOfClauses_unsat_sublist (fun c hc => by simp [hc]) hinc.2.1
      · rw [m_in, (hcl_old _ hinc.1).2.2.2.2.2.2] at hl
        have hr := hinc.2.2 l hl
        dsimp only at hr ⊢
        rw [m_va, m_la, m_rs, m_nc, hnc1]
        refine ⟨hr.1, hr.2.1, fun ha => ?_⟩
        have hrr := hr.2.2 (by rwa [← m_an])
        rw [(hcl_old _ hrr.1).2.2.2.2.2.2]
        exact ⟨by rw [hnc_def]; omega, hrr.2⟩
    · intro ha
      exact failingOk_append_nonCore (by rw [m_nc, hnc1]) m_fa m_na m_as
        (by rw [hcl_new.2.1]; exact bv32_lt2p16_and_core_zero sz hsz_max)
        (fun c hc => ⟨(hcl_old c hc).2.1, (hcl_old c hc).2.2.2.2.2.2⟩)
        (hinv.clauses.failing_ok (by rwa [← m_an]))
    · intro i hi; rw [m_as, m_nv]; exact hinv.clauses.assump_ok i (by rw [m_na] at hi; exact hi)
    · intro v hv; rw [m_fl]; exact hinv.clauses.flags_clean v (by rw [m_nv] at hv; exact hv)
  have hba_meta : KittenBaseAssignOk stMeta :=
    ⟨by rw [m_te, hte0]; exact Nat.zero_le _,
      by rw [m_pr, m_te]; simpa [hte0] using hinv.assign.prop_le,
      by rw [m_un, m_te, m_nv]; simpa [hte0] using hinv.assign.unass_eq,
      by rw [m_nv, m_va]; exact hinv.assign.vals_dom,
      by rw [m_nv, m_va]; exact hinv.assign.vals_neg_iff,
      by intro l hl; rw [m_nv] at hl; rw [m_va, m_te]; simpa [hte0] using
        hinv.assign.vals_nz_iff_trl l hl,
      by unfold kittenTrailLits; rw [m_te, hte0]; simp,
      by intro l hl; unfold kittenTrailLits at hl; rw [m_te, hte0] at hl; simp at hl,
      by intro v hv; rw [m_nv] at hv; rw [m_la, m_lvl]; simpa [hlvl0] using
        hinv.assign.trl_lvl_le v hv,
      by intro v hv hv0
         rw [m_nv] at hv; rw [m_va] at hv0; rw [m_la, m_rs]
         exact hinv.assign.unass_lvl_zero v hv hv0,
      by intro i j _ hj; rw [m_te, hte0] at hj; simp at hj,
      by intro i _ _ hi; rw [m_te, hte0] at hi; simp at hi,
      by intro i hi; rw [m_te, hte0] at hi; simp at hi⟩
  have hsync_meta : KittenTrailSynced stMeta := fun i hi => by rw [m_te, hte0] at hi; simp at hi
  have hrsn_meta : ReasonOk stMeta := fun i hi => by rw [m_te, hte0] at hi; simp at hi
  have hass_meta : kittenAssumpLits stMeta = kittenAssumpLits ks := by
    unfold kittenAssumpLits; rw [m_na, m_as]
  have hca_fin : stMeta.clAux[ks.orig_nc.toNat]? = some cid := by
    rw [← heq_nc, m_ca, List.getElem?_set_self hca_len]
  have hcm_fin : (stMeta.clMeta[ks.orig_nc.toNat]?.getD 0#32 &&& 0xFFFF#32) = sz := by
    rw [← heq_nc]
    change (kittenClauseMeta stMeta nc.toNat &&& 0xFFFF#32) = sz
    rw [hcl_new.2.1, hsz_mask]
  have hca_old : ∀ ci < ks.orig_nc.toNat, stMeta.clAux[ci]? = ks.clAux[ci]? := fun ci hci => by
    rw [m_ca, List.getElem?_set_ne (by dsimp only [nc]; rw [heq_nc]; omega)]
  by_cases h1 : sz == 1#32
  · by_cases hnu : stMeta.nunits.toNat < 256
    · let stU := (stMeta.putArr .units stMeta.nunits.toNat nc).putHdr .nunits
        (stMeta.nunits + 1#32)
      have hif : stUnit = stU := by simp only [stUnit, stU, h1, hnu, and_self, ite_true]
      rw [hif]
      have hsh' := (hsh_meta.putArr .units stMeta.nunits.toNat nc).putHdr .nunits
        (stMeta.nunits + 1#32)
      have hun_len : stMeta.nunits.toNat < stMeta.units.length := by
        rw [hsh_meta.units_len]; exact hnu
      have hun1 : (stMeta.nunits + 1#32).toNat = stMeta.nunits.toNat + 1 := by bv_omega
      have u_nv : stU.nv = stMeta.nv := by dsimp only [stU]; kp_field
      have u_on : stU.orig_nc = ks.orig_nc + 1#32 := by
        dsimp only [stU]; kp_field; rw [m_on, ← heq_nc]
      have u_on' : stU.orig_nc = stMeta.orig_nc := by dsimp only [stU]; kp_field
      have u_nc : stU.nc = stMeta.nc := by dsimp only [stU]; kp_field
      have u_lvl : stU.lvl = stMeta.lvl := by dsimp only [stU]; kp_field
      have u_pr : stU.prop = stMeta.prop := by dsimp only [stU]; kp_field
      have u_te : stU.trl_end = stMeta.trl_end := by dsimp only [stU]; kp_field
      have u_un : stU.unass = stMeta.unass := by dsimp only [stU]; kp_field
      have u_in : stU.incons = stMeta.incons := by dsimp only [stU]; kp_field
      have u_fa : stU.failing = stMeta.failing := by dsimp only [stU]; kp_field
      have u_an : stU.ante = stMeta.ante := by dsimp only [stU]; kp_field
      have u_al : stU.alen = stMeta.alen := by dsimp only [stU]; kp_field
      have u_ac : stU.acap = stMeta.acap := by dsimp only [stU]; kp_field
      have u_na : stU.nassump = stMeta.nassump := by dsimp only [stU]; kp_field
      have u_nu : stU.nunits = stMeta.nunits + 1#32 := by dsimp only [stU]; kp_field
      have u_nr : stU.nres = stMeta.nres := by dsimp only [stU]; kp_field
      have u_nk : stU.nkl = stMeta.nkl := by dsimp only [stU]; kp_field
      have u_nn : stU.nana = stMeta.nana := by dsimp only [stU]; kp_field
      have u_la : stU.lvlArr = stMeta.lvlArr := by dsimp only [stU]; kp_field
      have u_rs : stU.rsn = stMeta.rsn := by dsimp only [stU]; kp_field
      have u_tr : stU.trl = stMeta.trl := by dsimp only [stU]; kp_field
      have u_fl : stU.flags = stMeta.flags := by dsimp only [stU]; kp_field
      have u_va : stU.vals = stMeta.vals := by dsimp only [stU]; kp_field
      have u_as : stU.assump = stMeta.assump := by dsimp only [stU]; kp_field
      have u_uni : stU.units = stMeta.units.set stMeta.nunits.toNat nc := by
        dsimp only [stU]; kp_field
      have u_wh : stU.whead = stMeta.whead := by dsimp only [stU]; kp_field
      have u_wn : stU.wnext = stMeta.wnext := by dsimp only [stU]; kp_field
      have u_wb : stU.wblit = stMeta.wblit := by dsimp only [stU]; kp_field
      have u_ca : stU.clAux = stMeta.clAux := by dsimp only [stU]; kp_field
      have u_cm : stU.clMeta = stMeta.clMeta := by dsimp only [stU]; kp_field
      have u_co : stU.clOff = stMeta.clOff := by dsimp only [stU]; kp_field
      have u_ar : stU.arena = stMeta.arena := by dsimp only [stU]; kp_field
      have u_orig : kittenOrigClauses stU = kittenOrigClauses stMeta :=
        kittenOrigClauses_eq_of u_on' fun c _ => by
          simp only [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta,
            u_co, u_cm, u_ar]
      have hcl' : KittenClausesOk acap stU := by
        refine ⟨hcl_meta.acap_ge, hcl_meta.acap_lt, by rw [u_ac]; exact hcl_meta.acap_eq,
          by rw [u_nv]; exact hcl_meta.nv_le, by rw [u_nc]; exact hcl_meta.nc_le,
          by rw [u_on', u_nc]; exact hcl_meta.orig_nc_le,
          by rw [u_on']; exact hcl_meta.orig_nc_max,
          by rw [u_al]; exact hcl_meta.alen_le, by rw [u_na]; exact hcl_meta.nassump_le,
          by rw [u_nu, hun1]; unfold kMaxL; exact hnu,
          by rw [u_nr]; exact hcl_meta.nres_le, by rw [u_nk]; exact hcl_meta.nkl_le,
          by rw [u_nn]; exact hcl_meta.nana_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro c hc
          rw [u_nc] at hc
          have hw := hcl_meta.cl_wf c hc
          have hz_is : kittenClauseIsLrn stU c = kittenClauseIsLrn stMeta c := by
            simp [kittenClauseIsLrn, kittenClauseMeta, u_cm]
          have hz_sz : kittenClauseSize stU c = kittenClauseSize stMeta c := by
            simp [kittenClauseSize, kittenClauseMeta, u_cm]
          have hz_sp : kittenClauseSpan stU c = kittenClauseSpan stMeta c := by
            simp [kittenClauseSpan, kittenClauseSize, kittenClauseIsLrn, kittenClauseAux,
              kittenClauseMeta, u_cm, u_ca]
          have hz_off : kittenClauseOff stU c = kittenClauseOff stMeta c := by
            simp [kittenClauseOff, u_co]
          have hz_lits : kittenClauseLits stU c = kittenClauseLits stMeta c := by
            simp [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta,
              u_co, u_cm, u_ar]
          have hz_ants : kittenClauseAnts stU c = kittenClauseAnts stMeta c := by
            simp only [kittenClauseAnts, kittenClauseAux, hz_is, hz_off, hz_sz, u_ca, u_ar]
          have hz_lits_fn : ∀ a, kittenClauseLits stU a = kittenClauseLits stMeta a := fun a => by
            simp only [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta,
              u_co, u_cm, u_ar]
          rw [hz_is, hz_sz, hz_sp, hz_off, hz_lits, hz_ants,
            List.map_congr_left (fun a _ => hz_lits_fn a),
            u_orig, u_on', u_al, u_nv, u_an]
          exact hw
        · intro c1 c2 h12 hc2
          rw [u_nc] at hc2
          have hm := hcl_meta.cl_mono c1 c2 h12 hc2
          simp only [kittenClauseOff, kittenClauseSpan, kittenClauseSize, kittenClauseIsLrn,
            kittenClauseAux, kittenClauseMeta, u_co, u_cm, u_ca]
          exact hm
        · intro ui hui
          rw [u_nu, hun1] at hui
          by_cases huin : ui = stMeta.nunits.toNat
          · subst huin
            have hget : stU.units[stMeta.nunits.toNat]? = some nc := by
              rw [u_uni, List.getElem?_set_self hun_len]
            dsimp only; rw [hget, Option.getD_some]
            have hsz1 : sz = 1#32 := beq_iff_eq.mp h1
            have hsz1_nat : kittenClauseSize stU nc.toNat = 1 := by
              simpa [kittenClauseSize, kittenClauseMeta, u_cm, hsz1] using hcl_new.2.2.1
            refine ⟨?_, hsz1_nat⟩
            rw [u_nc, m_nc, hnc1]; dsimp only [nc]; omega
          · have hget : stU.units[ui]? = stMeta.units[ui]? := by
              rw [u_uni, List.getElem?_set_ne (Ne.symm huin)]
            dsimp only; rw [hget]
            have ho := hcl_meta.units_ok ui (by omega)
            rw [u_nc]
            simpa only [kittenClauseSize, kittenClauseMeta, u_cm] using ho
        · intro hi
          rw [u_in] at hi
          have hinc := hcl_meta.incons_ok hi
          refine ⟨by rw [u_in, u_nc]; exact hinc.1, by rw [u_orig]; exact hinc.2.1,
            fun l hl => ?_⟩
          rw [u_in] at hl
          have hl' : l ∈ kittenClauseLits stMeta stMeta.incons.toNat := by
            simpa [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta,
              u_co, u_cm, u_ar] using hl
          have hr := hinc.2.2 l hl'
          dsimp only at hr ⊢
          rw [u_va, u_la, u_rs, u_nc]
          refine ⟨hr.1, hr.2.1, fun ha => ?_⟩
          have hrr := hr.2.2 (by rwa [← u_an])
          simpa only [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta,
            u_co, u_cm, u_ar] using hrr
        · intro ha hf
          have hfa0 := hcl_meta.failing_ok (by rwa [← u_an]) (by rwa [← u_fa])
          have hcm_eq : (fun ci => (kittenClauseMeta stU ci &&& kmCore) != 0#32) =
              (fun ci => (kittenClauseMeta stMeta ci &&& kmCore) != 0#32) :=
            funext fun ci => by simp only [kittenClauseMeta, u_cm]
          have hmap_eq : List.map (kittenClauseLits stU) = List.map (kittenClauseLits stMeta) :=
            congrArg List.map (funext fun ci => by
              simp only [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta,
                u_co, u_cm, u_ar])
          unfold kittenAssumpLits at hfa0 ⊢
          rwa [u_nc, hcm_eq, hmap_eq, u_na, u_as]
        · intro i hi
          rw [u_na] at hi
          rw [u_as, u_nv]; exact hcl_meta.assump_ok i hi
        · intro v hv
          rw [u_nv] at hv
          rw [u_fl]; exact hcl_meta.flags_clean v hv
      have hw_u : KittenWatchesOk stU := by
        obtain ⟨ch, h1', h2', h3', h4'⟩ := hw_meta
        refine ⟨ch, by rw [u_nv]; exact h1', h2',
          fun l hl => by rw [u_wn, u_wh]; exact h3' l (by rw [u_nv] at hl; exact hl),
          fun l hl w hw => ?_⟩
        have hb := h4' l (by rw [u_nv] at hl; exact hl) w hw
        have hz_sz : kittenClauseSize stU (w / 2) = kittenClauseSize stMeta (w / 2) := by
          simp [kittenClauseSize, kittenClauseMeta, u_cm]
        have hz_off : kittenClauseOff stU (w / 2) = kittenClauseOff stMeta (w / 2) := by
          simp [kittenClauseOff, u_co]
        rw [u_nc, u_nv, u_ar, u_wb, hz_sz, hz_off]; exact hb
      have hba_u : KittenBaseAssignOk stU :=
        ⟨by rw [u_te]; exact hba_meta.trl_end_le,
          by rw [u_pr, u_te]; exact hba_meta.prop_le,
          by rw [u_un, u_te, u_nv]; exact hba_meta.unass_eq,
          by rw [u_nv, u_va]; exact hba_meta.vals_dom,
          by rw [u_nv, u_va]; exact hba_meta.vals_neg_iff,
          by rw [u_nv, u_va, u_te, u_tr]; exact hba_meta.vals_nz_iff_trl,
          by unfold kittenTrailLits; rw [u_te, u_tr]; exact hba_meta.trl_nodup,
          by unfold kittenTrailLits; rw [u_nv, u_te, u_tr]; exact hba_meta.trl_lt,
          by rw [u_nv, u_la, u_lvl]; exact hba_meta.trl_lvl_le,
          by rw [u_nv, u_va, u_la, u_rs]; exact hba_meta.unass_lvl_zero,
          by rw [u_te, u_la, u_tr]; exact hba_meta.trl_lvl_mono,
          by rw [u_te, u_la, u_tr, u_rs]; exact hba_meta.dec_earliest,
          by rw [u_te, u_la, u_tr, u_rs, u_va, u_orig]; exact hba_meta.lvl0_ok⟩
      have hsync_u : KittenTrailSynced stU := by
        unfold KittenTrailSynced; rw [u_te, u_tr, u_va]; exact hsync_meta
      have hrsn_u : ReasonOk stU := by
        intro i hi; rw [u_te] at hi; rw [u_tr, u_rs, u_nc]
        dsimp only
        have hro := hrsn_meta i hi; dsimp only at hro
        have heq_l : ∀ c, kittenClauseLits stU c = kittenClauseLits stMeta c := fun c => by
          simp [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta,
            u_co, u_cm, u_ar]
        simpa only [heq_l] using hro
      refine ⟨⟨hsh', hcl', hw_u, hba_u, hrsn_u⟩, hsync_u,
        by rw [u_lvl, m_lvl]; exact hlvl0, by rw [u_te, m_te]; exact hte0,
        by rw [u_nc, u_on', m_nc, m_on], u_on, by rw [u_an]; exact m_an,
        by rw [u_na]; exact m_na, by rw [u_ca]; exact hca_fin,
        by rw [u_cm]; exact hcm_fin, by rw [u_orig]; exact horig_meta,
        by unfold kittenAssumpLits; rw [u_na, u_as]; exact hass_meta,
        by intro ci hci; rw [u_ca]; exact hca_old ci hci⟩
    · have hif : stUnit = stMeta := by dsimp only [stUnit]; simp [h1, hnu]
      rw [hif]
      refine ⟨⟨hsh_meta, hcl_meta, hw_meta, hba_meta, hrsn_meta⟩, hsync_meta,
        by rw [m_lvl]; exact hlvl0, by rw [m_te]; exact hte0, by rw [m_nc, m_on],
        by rw [m_on, ← heq_nc], m_an, m_na, hca_fin, hcm_fin, horig_meta, hass_meta, hca_old⟩
  · have hsz2 : 2 ≤ sz.toNat := by
      have : sz ≠ 1#32 := fun he => absurd (beq_iff_eq.mpr he) h1
      have : sz.toNat ≠ 1 := fun hn => this (BitVec.eq_of_toNat_eq hn)
      omega
    have hif : stUnit = kittenWatchStep stMeta nc (xs[0]!) (xs[1]!) := by
      dsimp only [stUnit]; simp [h1]
    rw [hif]
    have h0_lt : 0 < xs.length := by omega
    have h1_lt : 1 < xs.length := by omega
    have hx0 : (xs[0]!).toNat < 2 * ks.nv.toNat := by
      have h := hxlits 0 (by omega)
      simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h0_lt] using h
    have hx1 : (xs[1]!).toNat < 2 * ks.nv.toNat := by
      have h := hxlits 1 (by omega)
      simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h1_lt] using h
    have hwn_lt : stMeta.wnext.length < 2 ^ 32 := by
      rw [hsh_meta.wnext_len]; decide
    have hw_old : ∀ ch : List (List Nat), ch.length = 2 * stMeta.nv.toNat → ch.flatten.Nodup →
        (∀ x < 2 * stMeta.nv.toNat,
          WChain stMeta.wnext (stMeta.whead[x]?.getD 0xFFFFFFFF#32) (ch[x]?.getD [])) →
        2 * nc.toNat ∉ ch.flatten ∧ 2 * nc.toNat + 1 ∉ ch.flatten := by
      intro ch hchl _ hwc
      obtain ⟨ch0, hch0_len, _, hwc0, hbnd0⟩ := hinv.watches
      have hmem_lt : ∀ w ∈ ch.flatten, w < 2 * nc.toNat := by
        intro w hw
        rw [List.mem_flatten] at hw
        obtain ⟨c, hc, hwc'⟩ := hw
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
        have hk_nv : k < 2 * stMeta.nv.toNat := by omega
        have hk_ks : k < 2 * ks.nv.toNat := by rw [← m_nv]; exact hk_nv
        have hk_ch0 : k < ch0.length := by rw [hch0_len]; exact hk_ks
        have hc1 := hwc k hk_nv
        rw [List.getElem?_eq_getElem hk, Option.getD_some] at hc1
        have hc0 := hwc0 k hk_ks
        rw [List.getElem?_eq_getElem hk_ch0, Option.getD_some, ← m_wh, ← m_wn] at hc0
        have heq_ch : ch[k] = ch0[k] := WChain.unique hwn_lt hc1 hc0
        rw [heq_ch] at hwc'
        exact (hbnd0 k hk_ks w (by simpa [List.getElem?_eq_getElem hk_ch0] using hwc')).1
      exact ⟨fun h => absurd (hmem_lt _ h) (by omega),
        fun h => absurd (hmem_lt _ h) (by omega)⟩
    have har_c0 : (stMeta.arena[kittenClauseOff stMeta nc.toNat]?.getD 0#32).toNat =
        (xs[0]!).toNat := by
      have ha := har_new 0 (by omega)
      rw [hcl_new.1, show off.toNat = ks.alen.toNat from rfl, m_ar]
      rw [Nat.add_zero] at ha
      rw [ha, List.getElem?_eq_getElem h0_lt, Option.getD_some]
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h0_lt]
    have har_c1 : (stMeta.arena[kittenClauseOff stMeta nc.toNat + 1]?.getD 0#32).toNat =
        (xs[1]!).toNat := by
      have ha := har_new 1 (by omega)
      rw [hcl_new.1, show off.toNat = ks.alen.toNat from rfl, m_ar, ha,
        List.getElem?_eq_getElem h1_lt, Option.getD_some]
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h1_lt]
    let stW := kittenWatchStep stMeta nc (xs[0]!) (xs[1]!)
    have hsh_w : stW.ShapesOk acap := kittenWatchStep_preserves_shapes hsh_meta _ _ _
    have hw_w : KittenWatchesOk stW := kittenWatchStep_preserves_watches hsh_meta hw_meta
      (by rw [m_nc, hnc1]; omega) hcl_meta.nc_le hcl_meta.nv_le
      (by rw [m_nv]; exact hx0) (by rw [m_nv]; exact hx1)
      (by rw [hcl_new.2.2.1]; exact hsz2) har_c0 har_c1 hw_old
    have hcl_w : KittenClausesOk acap stW := by
      have hn : stW.nv = stMeta.nv := rfl
      have hc : stW.nc = stMeta.nc := rfl
      have ho : stW.orig_nc = stMeta.orig_nc := rfl
      have ha : stW.alen = stMeta.alen := rfl
      have hac : stW.acap = stMeta.acap := rfl
      have hna : stW.nassump = stMeta.nassump := rfl
      have hnu : stW.nunits = stMeta.nunits := rfl
      have hnr : stW.nres = stMeta.nres := rfl
      have hnk : stW.nkl = stMeta.nkl := rfl
      have hnn : stW.nana = stMeta.nana := rfl
      have hin : stW.incons = stMeta.incons := rfl
      have hfa : stW.failing = stMeta.failing := rfl
      have hant : stW.ante = stMeta.ante := rfl
      have hrs : stW.rsn = stMeta.rsn := rfl
      have hva : stW.vals = stMeta.vals := rfl
      have hla : stW.lvlArr = stMeta.lvlArr := rfl
      have hfl : stW.flags = stMeta.flags := rfl
      have has : stW.assump = stMeta.assump := rfl
      have hun : stW.units = stMeta.units := rfl
      have hco : stW.clOff = stMeta.clOff := rfl
      have hcm : stW.clMeta = stMeta.clMeta := rfl
      have hca : stW.clAux = stMeta.clAux := rfl
      have har : stW.arena = stMeta.arena := rfl
      have horig_w : kittenOrigClauses stW = kittenOrigClauses stMeta :=
        kittenOrigClauses_eq_of ho fun c _ => by
          simp only [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta,
            hco, hcm, har]
      refine ⟨hcl_meta.acap_ge, hcl_meta.acap_lt, by rw [hac]; exact hcl_meta.acap_eq,
        by rw [hn]; exact hcl_meta.nv_le, by rw [hc]; exact hcl_meta.nc_le,
        by rw [ho, hc]; exact hcl_meta.orig_nc_le, by rw [ho]; exact hcl_meta.orig_nc_max,
        by rw [ha]; exact hcl_meta.alen_le, by rw [hna]; exact hcl_meta.nassump_le,
        by rw [hnu]; exact hcl_meta.nunits_le, by rw [hnr]; exact hcl_meta.nres_le,
        by rw [hnk]; exact hcl_meta.nkl_le, by rw [hnn]; exact hcl_meta.nana_le, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
      · intro c hlt
        rw [hc] at hlt
        have hw := hcl_meta.cl_wf c hlt
        simp only [kittenClauseIsLrn, kittenClauseSize, kittenClauseSpan, kittenClauseOff,
          kittenClauseLits, kittenClauseAnts, kittenClauseAux, kittenClauseMeta, hcm, hca, hco,
          har, ho, ha, hn, hant, horig_w]
        exact hw
      · intro c1 c2 h12 h2
        rw [hc] at h2
        have hm := hcl_meta.cl_mono c1 c2 h12 h2
        simp only [kittenClauseOff, kittenClauseSpan, kittenClauseSize, kittenClauseIsLrn,
          kittenClauseAux, kittenClauseMeta, hco, hcm, hca]
        exact hm
      · intro ui hui
        rw [hnu] at hui
        have hu := hcl_meta.units_ok ui hui
        simp only [hun, hc, kittenClauseSize, kittenClauseMeta, hcm]
        exact hu
      · intro hi
        rw [hin] at hi
        rw [hin, hc, horig_w, hva, hla, hant, hrs]
        simpa only [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta,
          hco, hcm, har] using hcl_meta.incons_ok hi
      · intro han hf
        have hfa0 := hcl_meta.failing_ok (by rwa [← hant]) (by rwa [← hfa])
        have hcm_eq : (fun ci => (kittenClauseMeta stW ci &&& kmCore) != 0#32) =
            (fun ci => (kittenClauseMeta stMeta ci &&& kmCore) != 0#32) :=
          funext fun ci => by simp only [kittenClauseMeta, hcm]
        have hmap_eq : List.map (kittenClauseLits stW) = List.map (kittenClauseLits stMeta) :=
          congrArg List.map (funext fun ci => by
            simp only [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta,
              hco, hcm, har])
        unfold kittenAssumpLits at hfa0 ⊢
        rwa [hc, hcm_eq, hmap_eq, hna, has]
      · intro i hi
        rw [hna] at hi
        rw [has, hn]
        exact hcl_meta.assump_ok i hi
      · intro v hv
        rw [hn] at hv
        rw [hfl]
        exact hcl_meta.flags_clean v hv
    have hba_w : KittenBaseAssignOk stW :=
      ⟨hcl_w.nv_le |> fun _ => hba_meta.trl_end_le, hba_meta.prop_le, hba_meta.unass_eq,
        hba_meta.vals_dom, hba_meta.vals_neg_iff, hba_meta.vals_nz_iff_trl, hba_meta.trl_nodup,
        hba_meta.trl_lt, hba_meta.trl_lvl_le, hba_meta.unass_lvl_zero, hba_meta.trl_lvl_mono,
        hba_meta.dec_earliest, by
          dsimp only [stW, kittenWatchStep, kittenWatchStep0]; exact hba_meta.lvl0_ok⟩
    have hsync_w : KittenTrailSynced stW := hsync_meta
    have hrsn_w : ReasonOk stW := hrsn_meta
    exact ⟨⟨hsh_w, hcl_w, hw_w, hba_w, hrsn_w⟩, hsync_w,
      by rw [show stW.lvl = stMeta.lvl from rfl, m_lvl]; exact hlvl0,
      by rw [show stW.trl_end = stMeta.trl_end from rfl, m_te]; exact hte0,
      by rw [show stW.nc = stMeta.nc from rfl, show stW.orig_nc = stMeta.orig_nc from rfl,
          m_nc, m_on],
      by rw [show stW.orig_nc = stMeta.orig_nc from rfl, m_on, ← heq_nc],
      m_an, m_na, hca_fin, hcm_fin, horig_meta, hass_meta,
      fun ci hci => by rw [show stW.clAux = stMeta.clAux from rfl]; exact hca_old ci hci⟩

end LeanQbe.T.Examples.Kissat.Full
