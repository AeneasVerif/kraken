module

public import LeanQbe.Examples.LratTrim
public import LeanQbe.Examples.LratRupLemmas
public import Kraken.Bedrock2.Test.LratTrimStrictProof
public import Kraken.SeparationTactics
public import LeanQbe.Wf
import all Kraken.Mem
import all Kraken.Separation
import all Std.Sat.CNF.Entails

/-!
# The strict resolution check: correctness

The specification `strictSpec` is the one of Kraken's `call_br_check_clause_strictly_by_resolution`
(`LratTrimStrictProof.lean`), with `lrat_fail` an `exit` (decision D5). The pure resolution metatheory
(`MarksWF`, `marksCount`, `MarksSat`, `MarksEntailed`, `InnerInv`, `ValidAntecedent`, …) is imported
from `LratTrimStrictProof.lean` unchanged. The memory and bit-level helpers are in `LeanQbe/Logic/`;
what is specific to LRAT literals and the kernel state (`abs_eq`, `negif_eq`, `loadl_kfield`,
`KernelFields_toList_length`, `nvK`) is reused from `LratRupLemmas.lean`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.LratTrim

open Std Std.Sat
open Std.Tactic.BVDecide.LRAT.Internal
open Kraken.Bedrock2.Test
open LeanQbe.LratRup

/-! ## Helpers -/

theorem map_take_succ {α β : Type} (f : α → β) (xs : List α) {i : Nat} (hi : i < xs.length) :
    (xs.take (i + 1)).map f = (xs.take i).map f ++ [f xs[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.map_append]; rfl

theorem exists_pol_of_ne_zero {marks : List Val} (hwf : MarksWF marks)
    {idx : Nat} (hlt : idx < marks.length) (hne : marks[idx] ≠ 0) :
    ∃ pol, marks[idx]? = some (encodePol pol) ∧ marks[idx] = encodePol pol := by
  have h := hwf idx hlt
  grind

theorem store_stat_resolved {st v : Val} {k : KernelFields} {P R : Mem 64 → Prop} {m : Mem 64}
    (h : (P ⋆ (kernelState st k ⋆ R)) m) :
    storeOk m .l (st + 144) ∧
      (P ⋆ (kernelState st { k with stat_resolved := v } ⋆ R)) (storeMem m .l (st + 144) v) := by
  unfold kernelState at h ⊢
  have hm0 : (word8Array st k.toList ⋆ (P ⋆ R)) m := sep_cast h (by ac_rfl)
  have ⟨ok, hm⟩ := storel_word8Array (i := 18) v (by simp [KernelFields.toList]) hm0
  have hset : k.toList.set 18 v = { k with stat_resolved := v }.toList := rfl
  rw [hset] at hm
  exact ⟨ok, sep_cast hm (by ac_rfl)⟩

theorem storeOk_stat_resolved {st : Val} {k : KernelFields} {P R : Mem 64 → Prop} {m : Mem 64}
    (h : (P ⋆ (kernelState st k ⋆ R)) m) : storeOk m .l (st + 144) :=
  (store_stat_resolved (v := 0) h).1

theorem mpol_eq_of_zero_slt {b mpol : Bool} {lit : Val}
    (h : (0 : Val).slt (evalAssignedLit (encodePol mpol) lit) = b) :
    mpol = if b then (toLiteral lit).2 else !(toLiteral lit).2 := by
  rw [evalAssignedLit_encodePol_eq] at h; generalize (toLiteral lit).2 = p at h ⊢
  cases b <;> cases mpol <;> cases p <;> revert h <;> decide

theorem mpol_eq_of_eval_slt_false {mpol : Bool} {lit : Val}
    (h : (evalAssignedLit (encodePol mpol) lit).slt 0 = false) :
    mpol = (toLiteral lit).2 := by
  rw [evalAssignedLit_encodePol_eq] at h; generalize (toLiteral lit).2 = p at h ⊢
  cases mpol <;> cases p <;> revert h <;> decide

/-! ## Loop 1: `strictScan` -/

theorem strictScan_spec {Γ : Env} {Q : Post} {X : XPost} {scanned : Cont}
    {id ants : Val} {aids : List Val} {R : Mem 64 → Prop} {m : Mem 64}
    (hants : ∀ x ∈ aids, IsInt32 x ∧ x ≠ 0)
    (hm : (ZeroTermInts ants aids ⋆ R) m)
    (hX : ∀ as m', X "lrat_fail" as m')
    (hscan : (∀ x ∈ aids, x.slt 0 = false) →
      scanned [ants + BitVec.ofNat 64 (4 * aids.length)] m) :
    wp Γ Q X (strictScan id scanned ants) [] [] m := by
  unfold strictScan
  have h32 : ∀ x ∈ aids, IsInt32 x := fun x hx => (hants x hx).1
  have hne0 : ∀ x ∈ aids, x ≠ 0 := fun x hx => (hants x hx).2
  apply wp_loop (fun r as m' => ∃ i, i ≤ aids.length ∧ r = aids.length - i ∧
    as = [ants + BitVec.ofNat 64 (4 * i)] ∧ m' = m ∧
    ∀ x ∈ aids.take i, x.slt 0 = false)
  · rintro J r as m' ⟨i, hi, rfl, rfl, rfl, hinv⟩ ih
    wp_unfold
    refine zeroTerm_jnz_step hi h32 hne0 hm (fun hlt => ?_) (fun hlen => ?_)
    · refine ⟨fun _ => hX _ _, fun hneg => ih _ _ _ (by omega)
        ⟨i + 1, hlt, rfl, by rw [ptr4], rfl, ?_⟩⟩
      intro x hx
      rw [List.take_add_one, List.getElem?_eq_getElem hlt] at hx
      grind
    · grind
  · intro J hJ
    wp_unfold
    exact hJ _ _ _ ⟨0, Nat.zero_le _, rfl, by simp, rfl, by simp⟩

/-! ## Loop 2, inner: `strictInner` -/

theorem strictInner_spec {Γ : Env} {Q : Post} {X : XPost} {done : Cont}
    {st id aid mb sr als : Val} {mv : Nat} {marks₀ clits : List Val} {k : KernelFields}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hwf0 : MarksWF marks₀) (hlen0 : mv < marks₀.length)
    (hvalid : ∀ x ∈ clits, IsValidLit mv x)
    (hm : (byte1Array mb marks₀ ⋆ (ZeroTermInts als clits ⋆ (kernelState st k ⋆ R))) m)
    (hX : ∀ as m', X "lrat_fail" as m')
    (hdone : ∀ m' marks unit,
      InnerInv mv marks₀ (toClause clits).literals marks unit →
      (byte1Array mb marks ⋆ (ZeroTermInts als clits ⋆ (kernelState st k ⋆ R))) m' →
      done [unit, BitVec.ofNat 64 (marksCount marks)] m') :
    wp Γ Q X (strictInner st id aid mb sr done als (BitVec.ofNat 64 (marksCount marks₀))) [] [] m := by
  unfold strictInner
  have h32 : ∀ x ∈ clits, IsInt32 x := fun x hx => (hvalid x hx).1
  have hne0 : ∀ x ∈ clits, x ≠ 0 := fun x hx => (hvalid x hx).2.1
  apply wp_loop (fun r as m' => ∃ i marks unit,
    as = [als + BitVec.ofNat 64 (4 * i), unit, BitVec.ofNat 64 (marksCount marks)] ∧
    i ≤ clits.length ∧ r = clits.length - i ∧
    InnerInv mv marks₀ ((clits.take i).map toLiteral) marks unit ∧
    (byte1Array mb marks ⋆ (ZeroTermInts als clits ⋆ (kernelState st k ⋆ R))) m')
  · rintro J r as m' ⟨i, marks, unit, rfl, hi, rfl, hinv, hm⟩ ih
    wp_unfold
    refine zeroTerm_jnz_step hi h32 hne0 (by ecancel) (fun hlt => ?_) (fun hlen => ?_)
    · have hlit := hvalid clits[i] (List.getElem_mem hlt)
      have hatom_lt : (toLiteral clits[i]).1 < marks.length := by
        rw [hinv.len_eq]; exact Nat.lt_of_le_of_lt hlit.2.2.1 hlen0
      rw [abs_eq, bvAbs_eq_ofNat_toLiteral_fst]
      refine ⟨_, loadsb_byte1Array hatom_lt (hinv.wf.isInt8 hatom_lt) hm, fun hmz => ?_, fun hmz => ?_⟩
      · have hm0 : marks[(toLiteral clits[i]).1]? = some 0 := by
          rw [List.getElem?_eq_getElem hatom_lt, hmz]
        rw [show (clits[i].sshiftRight 63 ||| 1) = encodePol (toLiteral clits[i]).2 by
          rw [← bvSignByte_eq_encodePol]; rfl]
        have ⟨ok, hm'⟩ := storeb_byte1Array (encodePol (toLiteral clits[i]).2) hatom_lt hm
        refine ⟨ok, ih _ _ _ (by omega) ⟨i + 1, _, unit, ?_, hlt, rfl, ?_, hm'⟩⟩
        · rw [ptr4, ofNat_add_one, marksCount_set_of_eq_zero hm0 (encodePol_ne_zero _)]
        · rw [map_take_succ _ _ hlt]; exact hinv.step_mark_zero hlit hatom_lt hm0
      · obtain ⟨mpol, hmpol, hmark_eq⟩ := exists_pol_of_ne_zero hinv.wf hatom_lt hmz
        rw [negif_eq, hmark_eq]
        refine ⟨fun hpos => ?_, fun hpos => ?_⟩
        · obtain rfl := mpol_eq_of_zero_slt hpos
          refine ih _ _ _ (by omega) ⟨i + 1, marks, unit, by rw [ptr4], hlt, rfl, ?_, hm⟩
          rw [map_take_succ _ _ hlt]; exact hinv.step_mark_same hlit hatom_lt hmpol
        · obtain rfl := mpol_eq_of_zero_slt hpos
          have hu32 : IsInt32 unit := hinv.unit_spec.elim (· ▸ isInt32_zero) (·.1.1)
          rw [truthy_iff _ hu32]
          refine ⟨fun _ => ⟨storeOk_stat_resolved (P := byte1Array mb marks ⋆ ZeroTermInts als clits) (k := k) (R := R)
            (sep_cast hm (by ac_rfl)), hX _ _⟩, fun hu0 => ?_⟩
          rw [Classical.not_not] at hu0; subst hu0
          refine ih _ _ _ (by omega) ⟨i + 1, marks, clits[i], by rw [ptr4], hlt, rfl, ?_, hm⟩
          rw [map_take_succ _ _ hlt]; exact hinv.step_mark_opp hlit hatom_lt hmpol
    · rw [hlen, List.take_length, ← literals_toClause] at hinv
      exact hdone m' marks unit hinv hm
  · intro J hJ
    wp_unfold
    exact hJ _ _ _ ⟨0, marks₀, 0, by simp, Nat.zero_le _, rfl, InnerInv.init hwf0, hm⟩

/-! ## Loop 2, outer: `strictOuter` -/

theorem strictOuter_spec {Γ : Env} {Q : Post} {X : XPost} {resolved : Cont}
    {st id lb mb ants sr0 : Val} {mv n : Nat} {f : CNF Nat} {aids : List Val}
    {k : KernelFields} {R_ro : Mem 64 → Prop} {m : Mem 64}
    (hlen : mv < n) (hbound : 4 * aids.length < 2 ^ 64)
    (hants_int : ∀ x ∈ aids, IsInt32 x ∧ x ≠ 0)
    (hants_pos : ∀ x ∈ aids, x.slt 0 = false)
    (hants_valid : ∀ aid ∈ aids, aid.slt 0 = false → ValidAntecedent mv f lb R_ro aid)
    (hsub_ants : ∃ R', R_ro = (ZeroTermInts ants aids ⋆ R'))
    (hm : (byte1Array mb (List.replicate n 0) ⋆ (kernelState st k ⋆ R_ro)) m)
    (hX : ∀ as m', X "lrat_fail" as m')
    (hres : ∀ m' marks first,
      marks.length = n → MarksWF marks → (first = 0 ∨ first = 1) →
      (first = 0 → MarksEntailed f marks) →
      (byte1Array mb marks ⋆ (kernelState st k ⋆ R_ro)) m' →
      resolved [sr0 + BitVec.ofNat 64 aids.length, BitVec.ofNat 64 (marksCount marks), first] m') :
    wp Γ Q X (strictOuter st id lb mb ants resolved
      (ants + BitVec.ofNat 64 (4 * aids.length)) sr0) [] [] m := by
  unfold strictOuter
  obtain ⟨R_ants, hR_ants⟩ := hsub_ants
  have h32 : ∀ x ∈ aids, IsInt32 x := fun x hx => (hants_int x hx).1
  apply wp_loop (fun j as m' => ∃ marks first,
    j ≤ aids.length ∧
    as = [ants + BitVec.ofNat 64 (4 * j), sr0 + BitVec.ofNat 64 (aids.length - j),
      BitVec.ofNat 64 (marksCount marks), first] ∧
    marks.length = n ∧ MarksWF marks ∧ (first = 0 ∨ first = 1) ∧
    (first = 0 → MarksEntailed f marks) ∧
    (byte1Array mb marks ⋆ (kernelState st k ⋆ R_ro)) m')
  · rintro J j as m' ⟨marks, first, hj, rfl, hmlen, hwf, hfirst_or, hent_init, hm⟩ ih
    wp_unfold
    refine ⟨fun heq => ?_, fun hne => ?_⟩
    · grind
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 :=
        Nat.exists_eq_succ_of_ne_zero fun h0 => hne (by subst h0; simp)
      have hj' : j' < aids.length := hj
      rw [ptr4_sub]
      have hm_ants : (ZeroTermInts ants aids ⋆ (byte1Array mb marks ⋆ (kernelState st k ⋆ R_ants))) m' := by
        rw [hR_ants] at hm; ecancel
      have hld_aid := loadsw_zeroTerm (Nat.le_of_lt hj') h32 hm_ants
      simp only [zeroTermGet, hj', ↓reduceDIte] at hld_aid
      have haid_mem := List.getElem_mem hj'
      obtain ⟨als, clits, ⟨R_als, hR_als⟩, ⟨R_clits, hR_clits⟩, hclits_valid, hclits_nontaut, hclits_ent⟩ :=
        hants_valid aids[j'] haid_mem (hants_pos aids[j'] haid_mem)
      have hld_als := loadl_word8 (a := lb + BitVec.ofNat 64 (8 * aids[j'].toNat)) (v := als) (sg := true)
        (R := byte1Array mb marks ⋆ (kernelState st k ⋆ R_als))
        (by rw [bitVec_ofNat_eight_mul_toNat]; rw [hR_als] at hm; ecancel)
      refine ⟨_, hld_aid, _, hld_als, ?_⟩
      have hsr_step : sr0 + BitVec.ofNat 64 (aids.length - (j' + 1)) + 1 =
          sr0 + BitVec.ofNat 64 (aids.length - j') := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
      rw [hsr_step]
      apply wp_join (fun as m1 => ∃ marks1 unit,
        as = [unit, BitVec.ofNat 64 (marksCount marks1)] ∧
        InnerInv mv marks (toClause clits).literals marks1 unit ∧
        (byte1Array mb marks1 ⋆ (kernelState st k ⋆ R_ro)) m1)
      · rintro _ m1 ⟨marks1, unit, rfl, hinv1, hm1⟩
        wp_unfold
        have hu32 : IsInt32 unit := hinv1.unit_spec.elim (· ▸ isInt32_zero) (·.1.1)
        rw [truthy_iff _ hu32]
        refine ⟨fun _ => ?_, fun hfirst0 => ?_⟩
        · refine ⟨fun _ => ⟨storeOk_stat_resolved hm1, hX _ _⟩, fun hu0 => ?_⟩
          rw [Classical.not_not] at hu0; subst hu0
          exact ih j' _ _ (Nat.lt_succ_self j') ⟨marks1, 0, Nat.le_of_lt hj', rfl,
            hinv1.len_eq.trans hmlen, hinv1.wf, Or.inl rfl,
            fun _ a hfa => hinv1.finish_first (hclits_ent a hfa), hm1⟩
        · obtain rfl := first_eq_zero hfirst_or hfirst0
          refine ⟨fun hu_ne => ?_,
            fun _ => ⟨storeOk_stat_resolved hm1, hX _ _⟩⟩
          rcases hinv1.unit_spec with rfl | ⟨hu_valid, _, hu_mark⟩
          · exact absurd rfl hu_ne
          · have hu_lt : (toLiteral unit).1 < marks1.length := by
              rw [hinv1.len_eq, hmlen]; exact Nat.lt_of_le_of_lt hu_valid.2.2.1 hlen
            rw [abs_eq, bvAbs_eq_ofNat_toLiteral_fst]
            have ⟨ok, hm2⟩ := storeb_byte1Array 0 hu_lt hm1
            refine ⟨ok, ih j' _ _ (Nat.lt_succ_self j') ⟨marks1.set (toLiteral unit).1 0, 0,
              Nat.le_of_lt hj', ?_, by simp [hinv1.len_eq, hmlen],
              marksWF_set_zero hinv1.wf hu_lt, Or.inl rfl,
              fun _ a hfa => hinv1.finish_resolve hclits_nontaut hu_ne (hent_init rfl a hfa)
                (hclits_ent a hfa), hm2⟩⟩
            rw [ofNat_sub_one_of_succ (marksCount_set_zero_of_ne_zero hu_mark (encodePol_ne_zero _))]
      · intro K hK
        exact strictInner_spec hwf (by omega) hclits_valid (by rw [hR_clits] at hm; ecancel) hX
          fun m1 marks1 unit hinv1 hm1 => hK _ _ ⟨marks1, unit, rfl, hinv1, by rw [hR_clits]; ecancel⟩
  · intro J hJ
    wp_unfold
    refine hJ aids.length _ _ ⟨List.replicate n 0, 1, Nat.le_refl _, ?_,
      List.length_replicate, marksWF_replicate n, Or.inr rfl, fun h => absurd h (by decide), hm⟩
    rw [Nat.sub_self, marksCount_replicate_zero]; simp

/-! ## Loop 3: `strictFinal` -/

theorem strictFinal_spec {Γ : Env} {Q : Post} {X : XPost} {checked : Cont}
    {id mb lits : Val} {mv : Nat} {marks₀ ls : List Val} {R : Mem 64 → Prop} {m : Mem 64}
    (hwf0 : MarksWF marks₀) (hlen0 : mv < marks₀.length)
    (hvalid : ∀ x ∈ ls, IsValidLit mv x)
    (hm : (byte1Array mb marks₀ ⋆ (ZeroTermInts lits ls ⋆ R)) m)
    (hX : ∀ as m', X "lrat_fail" as m')
    (hchk : ∀ m' marks,
      marks.length = marks₀.length →
      (∀ a, MarksSat a marks₀ → MarksSat a marks ∨ (toClause ls).Sat a) →
      (byte1Array mb marks ⋆ (ZeroTermInts lits ls ⋆ R)) m' →
      checked [BitVec.ofNat 64 (marksCount marks)] m') :
    wp Γ Q X (strictFinal id mb checked lits (BitVec.ofNat 64 (marksCount marks₀))) [] [] m := by
  unfold strictFinal
  have h32 : ∀ x ∈ ls, IsInt32 x := fun x hx => (hvalid x hx).1
  have hne0 : ∀ x ∈ ls, x ≠ 0 := fun x hx => (hvalid x hx).2.1
  apply wp_loop (fun r as m' => ∃ i marks,
    as = [lits + BitVec.ofNat 64 (4 * i), BitVec.ofNat 64 (marksCount marks)] ∧
    i ≤ ls.length ∧ r = ls.length - i ∧
    marks.length = marks₀.length ∧ MarksWF marks ∧
    (∀ a, MarksSat a marks₀ → MarksSat a marks ∨ (toClause ls).Sat a) ∧
    (byte1Array mb marks ⋆ (ZeroTermInts lits ls ⋆ R)) m')
  · rintro J r as m' ⟨i, marks, rfl, hi, rfl, hmlen, hwf, hsat, hm⟩ ih
    wp_unfold
    refine zeroTerm_jnz_step hi h32 hne0 (by ecancel) (fun hlt => ?_) (fun hlen => ?_)
    · have hlit := hvalid ls[i] (List.getElem_mem hlt)
      have hatom_lt : (toLiteral ls[i]).1 < marks.length := by
        rw [hmlen]; exact Nat.lt_of_le_of_lt hlit.2.2.1 hlen0
      rw [abs_eq, bvAbs_eq_ofNat_toLiteral_fst]
      refine ⟨_, loadsb_byte1Array hatom_lt (hwf.isInt8 hatom_lt) hm, fun _ => hX _ _, fun hmz => ?_⟩
      obtain ⟨mpol, hmpol, hmark_eq⟩ := exists_pol_of_ne_zero hwf hatom_lt hmz
      rw [negif_eq, hmark_eq]
      refine ⟨fun _ => hX _ _, fun hneg => ?_⟩
      obtain rfl := mpol_eq_of_eval_slt_false hneg
      have ⟨ok, hm'⟩ := storeb_byte1Array 0 hatom_lt hm
      refine ⟨ok, ih _ _ _ (by omega) ⟨i + 1, _, ?_, hlt, rfl, by simp [hmlen],
        marksWF_set_zero hwf hatom_lt, ?_, hm'⟩⟩
      · rw [ptr4, ofNat_sub_one_of_succ (marksCount_set_zero_of_ne_zero hmpol (encodePol_ne_zero _))]
      · intro a hsa
        refine (hsat a hsa).elim (fun hms => marksSat_clear_step ?_ hmpol hms) Or.inr
        rw [literals_toClause]; exact List.mem_map_of_mem (List.getElem_mem hlt)
    · exact hchk m' marks hmlen hsat hm
  · intro J hJ
    wp_unfold
    exact hJ _ _ _ ⟨0, marks₀, by simp, Nat.zero_le _, rfl, rfl, hwf0, fun _ => Or.inl, hm⟩

/-! ## The function: `strictCheck` -/

theorem strictCheck_correct (Γ : Env) :
    ∀ args m Q X, strictSpec args m Q X → Func.spec Γ strictCheck args m Q X := by
  rintro _ m Q X ⟨st, id, lits_ptr, ant_ptr, mv, n, f, k, clause_lits, ants, R_ro, rfl,
    hlen, hn_bound, hants_bound, hants_int, hants_valid, hclause_valid, hsep,
    hsub_ants, ⟨R_lits, hR_lits⟩, hQ, hX⟩
  unfold strictCheck Func.spec
  wp_unfold
  -- `@scanned`: after Loop 1
  apply wp_join (fun as m' => as = [ant_ptr + BitVec.ofNat 64 (4 * ants.length)] ∧
    m' = m ∧ ∀ x ∈ ants, x.slt 0 = false)
  · rintro _ m ⟨rfl, rfl, hants_pos⟩
    wp_unfold
    refine ⟨_, loadl_kfield 2 (by decide) (by ecancel) rfl, _, loadl_kfield 4 (by decide) (by ecancel) rfl,
      _, loadl_kfield 18 (by decide) (by ecancel) rfl, ?_⟩
    simp only [KernelFields.toList, List.getElem_cons_succ, List.getElem_cons_zero]
    -- `@resolved`: after Loop 2
    apply wp_join (fun as m1 => ∃ marks1 first,
      as = [k.stat_resolved + BitVec.ofNat 64 ants.length, BitVec.ofNat 64 (marksCount marks1), first] ∧
      marks1.length = n ∧ MarksWF marks1 ∧ (first = 0 ∨ first = 1) ∧
      (first = 0 → MarksEntailed f marks1) ∧
      (byte1Array k.marks_begin marks1 ⋆ (kernelState st k ⋆ R_ro)) m1)
    · rintro _ m1 ⟨marks1, first, rfl, hlen1, hwf1, hfirst_or, hent1, hm1⟩
      wp_unfold
      have ⟨ok, hm2⟩ := store_stat_resolved (v := k.stat_resolved + BitVec.ofNat 64 ants.length) hm1
      refine ⟨ok, fun _ => hX _ _, fun hfirst0 => ?_⟩
      have hent_marks1 := hent1 (first_eq_zero hfirst_or hfirst0)
      -- `@checked`: after Loop 3
      apply wp_join (fun as m3 => ∃ marks2,
        as = [BitVec.ofNat 64 (marksCount marks2)] ∧
        marks2.length = n ∧
        (∀ a, MarksSat a marks1 → MarksSat a marks2 ∨ (toClause clause_lits).Sat a) ∧
        (byte1Array k.marks_begin marks2 ⋆
          (kernelState st { k with stat_resolved := k.stat_resolved + BitVec.ofNat 64 ants.length } ⋆
            R_ro)) m3)
      · rintro _ m3 ⟨marks2, rfl, hlen2, hsat2, hm3⟩
        wp_unfold
        refine ⟨fun _ => hX _ _, fun hz => ?_⟩
        rw [Classical.not_not] at hz
        have hcnt_le : marksCount marks2 ≤ n := hlen2 ▸ marksCount_le_length marks2
        have hcnt0 : marksCount marks2 = 0 := by
          grind
        have hmarks2_eq : marks2 = List.replicate n 0 :=
          hlen2 ▸ eq_replicate_zero_of_marksCount_eq_zero hcnt0
        rw [hmarks2_eq] at hm3
        refine hQ (fun a hfa => ?_) m3 hm3
        exact (hsat2 a (hent_marks1 a hfa)).elim
          (fun hms => False.elim (not_marksSat_of_marksCount_eq_zero hcnt0 a hms)) fun h => h
      · intro K hK
        have hm2_in : (byte1Array k.marks_begin marks1 ⋆ (ZeroTermInts lits_ptr clause_lits ⋆
            (kernelState st { k with stat_resolved := k.stat_resolved + BitVec.ofNat 64 ants.length } ⋆
              R_lits))) (storeMem m1 .l (st + 144) (k.stat_resolved + BitVec.ofNat 64 ants.length)) := by
          rw [hR_lits] at hm2; ecancel
        exact strictFinal_spec hwf1 (by omega) hclause_valid hm2_in hX fun m3 marks2 hlen2 hsat2 hm3 =>
          hK _ _ ⟨marks2, rfl, hlen2.trans hlen1, hsat2, by rw [hR_lits]; ecancel⟩
    · intro K hK
      exact strictOuter_spec hlen hants_bound hants_int hants_pos hants_valid hsub_ants hsep hX
        fun m1 marks1 first hlen1 hwf1 hfo hent1 hm1 =>
          hK _ _ ⟨marks1, first, rfl, hlen1, hwf1, hfo, hent1, hm1⟩
  · intro K hK
    obtain ⟨R_ants, hR_ants⟩ := hsub_ants
    exact strictScan_spec (R := byte1Array k.marks_begin (List.replicate n 0) ⋆ (kernelState st k ⋆ R_ants))
      hants_int (by rw [hR_ants] at hsep; ecancel) hX fun hpos => hK _ _ ⟨rfl, rfl, hpos⟩

theorem strictCheck_wf : Func.Wf strictCheck := by
  unfold strictCheck strictScan strictOuter strictInner strictFinal; wf_tac

/-! ## Non-vacuity -/

def nvStrictK : KernelFields := { nvK with marks_begin := 0x10a0 }

def nvStrictBytes : List UInt8 :=
  bytesN 8 nvStrictK.toList ++ (bytesN 1 [0, 0] ++ (bytesN 4 [1, 0] ++ bytesN 4 [0]))

theorem strictCheck_nonvacuous :
    strictSpec [0x1000, 7, 0x10a2, 0x10aa] (nvStrictBytes.At 0x1000)
      (fun rs _ => rs = []) (fun f _ _ => f = "lrat_fail") := by
  refine ⟨0x1000, 7, 0x10a2, 0x10aa, 1, 2, .empty, nvStrictK, [1], [],
    ZeroTermInts 0x10aa [] ⋆ ZeroTermInts 0x10a2 [1],
    rfl, by decide, by decide, by decide, by simp, by simp,
    by intro x hx; rw [List.mem_singleton.1 hx]; unfold IsValidLit bvAbs; decide,
    ?_, ⟨_, rfl⟩, ⟨ZeroTermInts 0x10aa [], by ac_rfl⟩, fun _ _ _ => rfl, fun _ _ => rfl⟩
  unfold kernelState ZeroTermInts nvStrictBytes
  rw [show List.replicate 2 (0 : Val) = [0, 0] from rfl]
  solve_bytes_at [KernelFields_toList_length]

end LeanQbe.LratTrim
