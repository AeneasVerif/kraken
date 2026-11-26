/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityTumbleSpec
import LeanQbe.T.Examples.Kissat.FullDimacsBodyLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 11 PR 2 Tumble & Lazy-Activation Clause Ingestion Proof

Proves `full_ingest_cl_tum_wp` (`FullFidelityTumble.full_ingest_cl_tum_body`) against
`fullIngestClTumSpec`:
1. Parse-local variable renaming (`frame_dec[ev] = extend_len++`) when `c.mv < c.extend_cap`,
   maintaining `TumbleInv`, `TumbleCovers`, relabeled `FullSparseInvW` + `Entails`, and
   `TumbleValsRel` + `TumbleUnusedZero` for `UnitUnsatTrace` preservation.
2. S11-3 lazy activation (`full_activate_lit_fid`) of kept literals after unit pruning.
3. UNSAT lifting via `cnf_unsat_of_relabel_tumble` on `keep = 0`, unit assignment on `keep = 1`,
   and clause addition on `keep ≥ 2`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityTumble

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

section IngestClTumProof

open scoped FullArenaTactics FullDimacsBodyTactics
open FullArenaTactics FullDimacsBodyTactics

/-! ## 1. Pure BitVec, Relabeling & Witness Helpers -/

private theorem bv32_tumble_lit_eq {iv l : Nat} (hiv : iv < 2 ^ 31) (hl : l < 2 ^ 32) :
    ((BitVec.ofNat 32 iv <<< (1 : Nat)) ||| (BitVec.ofNat 32 l &&& (1 : BitVec 32))) =
      BitVec.ofNat 32 (2 * iv + l % 2) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (BitVec.ofNat 32 iv <<< (1 : Nat)).toNat = 2 * iv := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]; omega
  have h2 : (BitVec.ofNat 32 l &&& (1 : BitVec 32)).toNat = l % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt hl, Nat.and_one_is_mod]
  rw [BitVec.toNat_or, h1, h2, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 2 * iv + l % 2 < 2 ^ 32)]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  cases i with
  | zero =>
    simp only [Nat.testBit_zero, show (2 * iv) % 2 = 0 from by omega]
    have hm : (2 * iv + l % 2) % 2 = l % 2 := by omega
    rw [hm]; cases Nat.mod_two_eq_zero_or_one l with
    | inl h => simp [h]
    | inr h => simp [h]
  | succ k =>
    have hlo : Nat.testBit (l % 2) (k + 1) = false := by
      rw [Nat.testBit_succ]; have : (l % 2) / 2 = 0 := by omega
      rw [this]; exact Nat.zero_testBit k
    rw [hlo, Bool.or_false, Nat.testBit_succ, Nat.testBit_succ,
      show (2 * iv) / 2 = iv from by omega, show (2 * iv + l % 2) / 2 = iv from by omega]

private theorem bv32_trunc64_ofNat_lt {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n :=
  bv64_trunc32_ofNat hn

private theorem bv64_add1_nat {n : Nat} (hn : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 n + (1 : BitVec 64) = BitVec.ofNat 64 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), Nat.mod_eq_of_lt hn]

private theorem bv32_add1_nat {n : Nat} (hn : n + 1 < 2 ^ 32) :
    BitVec.ofNat 32 n + (1 : BitVec 32) = BitVec.ofNat 32 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 32), Nat.mod_eq_of_lt hn]

private theorem fullIngestTum_unit_rev {revLits : List Nat} {l : Nat}
    (hcleq : CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral) =
      CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l]) : revLits = [l] := by
  have hlits_eq := congrArg CNF.Clause.literals hcleq
  simp only [CNF.Clause.literals_ofLiterals] at hlits_eq
  cases hr : revLits.reverse with
  | nil => rw [hr] at hlits_eq; simp at hlits_eq
  | cons a rest_r =>
    rw [hr] at hlits_eq
    cases rest_r with
    | nil =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hlits_eq
      have ha := kissatLitToDimacsLiteral_inj hlits_eq; subst ha
      simpa using congrArg List.reverse hr
    | cons _ _ => simp at hlits_eq

private theorem relabel_entails_add (π : Nat → Nat) (accCnf : CNF Nat) (cl : CNF.Clause Nat) :
    (CNF.relabel π (shiftDownCnf (accCnf.add cl))).Entails
      (CNF.relabel π (shiftDownCnf accCnf)) := by
  have h := shiftDownCnf_entails_add accCnf cl
  rw [CNF.entails_def] at h ⊢
  intro α hα
  rw [CNF.Sat, CNF.eval_relabel] at hα ⊢
  exact h (α ∘ π) hα

private theorem relabel_entails_added (π : Nat → Nat) (accCnf : CNF Nat) (cl : CNF.Clause Nat) :
    (CNF.relabel π (shiftDownCnf (accCnf.add cl))).EntailsClause
      (CNF.Clause.relabel π (shiftDownClause cl)) := by
  have h := shiftDownCnf_entails_added accCnf cl
  rw [CNF.entails_clause_def] at h ⊢
  intro α hα
  rw [CNF.Sat, CNF.eval_relabel] at hα
  have h1 := h (α ∘ π) hα
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h1 ⊢
  obtain ⟨l, hl, heq⟩ := h1
  refine ⟨(π l.1, l.2), ?_, heq⟩
  change (π l.1, l.2) ∈ (CNF.Clause.relabel π (shiftDownClause cl)).literals
  rw [CNF.Clause.literals_relabel, List.mem_map]
  exact ⟨l, hl, rfl⟩

private theorem entails_cnfOfClauses_cons_tum {F0 : CNF Nat} {cl : List Nat} {F : List (List Nat)}
    (hF : F0.Entails (cnfOfClauses F)) (hcl : F0.EntailsClause (cnfClause cl)) :
    F0.Entails (cnfOfClauses (cl :: F)) := by
  rw [CNF.entails_def] at hF ⊢
  rw [CNF.entails_clause_def] at hcl
  intro α hα
  rw [cnf_sat_cnfOfClauses_iff]
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc'
  · exact hcl α hα
  · exact (cnf_sat_cnfOfClauses_iff α F).mp (hF α hα) c hc'

private theorem cnfOfClauses_cons_entails_tum (cl : List Nat) (F : List (List Nat)) :
    (cnfOfClauses (cl :: F)).Entails (cnfOfClauses F) := by
  rw [CNF.entails_def]
  intro α hα
  rw [cnf_sat_cnfOfClauses_iff] at hα ⊢
  intro c hc; exact hα c (List.mem_cons_of_mem _ hc)

private theorem cnfOfClauses_cons_entails_head_tum (cl : List Nat) (F : List (List Nat)) :
    (cnfOfClauses (cl :: F)).EntailsClause (cnfClause cl) := by
  rw [CNF.entails_clause_def]
  intro α hα
  rw [cnf_sat_cnfOfClauses_iff] at hα
  exact hα cl List.mem_cons_self

private theorem extUnsatSound_of_entails_tum {F0 : CNF Nat} {mv : Nat} {F : List (List Nat)}
    (hb : VarsBounded mv F) (hent : F0.Entails (cnfOfClauses F)) : ExtUnsatSound F0 mv F := by
  refine ⟨hb, fun hu => ?_⟩
  rw [CNF.entails_def] at hent
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα; exact hu α (hent α hα)

private theorem varsBounded_cons_tum {mv : Nat} {cl : List Nat} {F : List (List Nat)}
    (hcl : ∀ l ∈ cl, l < 2 * mv) (hb : VarsBounded mv F) : VarsBounded mv (cl :: F) := by
  intro c hc l hl
  rcases List.mem_cons.mp hc with rfl | hc'
  · exact Nat.div_lt_of_lt_mul (hcl l hl)
  · exact hb c hc' l hl

private theorem nodup_of_pairwise_div2_tum {xs : List (BitVec 32)} {n : Nat} (hn : n ≤ xs.length)
    (hnd : ∀ k1 k2, k1 < n → k2 < n →
      (xs[k1]?.getD 0#32).toNat / 2 = (xs[k2]?.getD 0#32).toNat / 2 → k1 = k2) :
    ((xs.take n).map fun x => x.toNat / 2).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [List.length_map, List.length_take] at hi hj
  have hi' : i < n := by omega
  have hj' : j < n := by omega
  simp only [List.getElem_map, List.getElem_take]
  intro heq
  have hget : (xs[i]?.getD 0#32).toNat / 2 = (xs[j]?.getD 0#32).toNat / 2 := by
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
    exact heq
  have hij_eq := hnd i j hi' hj' hget
  omega

private theorem addUnit_preserves_witness_tum {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState}
    (hcl : k.LengthsOk c) (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lit : BitVec 32} {flags' : List (BitVec 32)} {unassigned' unflushed' : BitVec 64}
    (_hfll : flags'.length = c.max_vars)
    (hlit : lit.toNat < 2 * k.cur_vars) (hun : k.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hl0 : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat])) :
    let v := lit.toNat / 2
    FullWitnessInv c F0 F_cur
      { k with
        vals := (k.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        flags := flags', lvl := k.lvl.set v 0#32
        rsns := k.rsns.set v 0xFFFFFFFF#32, trl := k.trl.set k.trail_end lit
        trail_pos := k.trail_pos.set v (BitVec.ofNat 32 k.trail_end)
        trail_end := k.trail_end + 1
        unassigned := unassigned', unflushed := unflushed' } := by
  intro v
  let k' : FullCoreState :=
    { k with
      vals := (k.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
      flags := flags', lvl := k.lvl.set v 0#32
      rsns := k.rsns.set v 0xFFFFFFFF#32, trl := k.trl.set k.trail_end lit
      trail_pos := k.trail_pos.set v (BitVec.ofNat 32 k.trail_end)
      trail_end := k.trail_end + 1
      unassigned := unassigned', unflushed := unflushed' }
  have hcv' : k'.cur_vars = k.cur_vars := rfl
  have hte' : k'.trail_end = k.trail_end + 1 := rfl
  have hclv' : k'.cur_level = k.cur_level := rfl
  have hv_lt : v < k.cur_vars := Nat.div_lt_of_lt_mul hlit
  have hv_mv : v < c.max_vars := Nat.lt_of_lt_of_le hv_lt hcl.cur_vars_le
  have hcv_mv : k.cur_vars ≤ c.max_vars := hcl.cur_vars_le
  have hlit_neg : lit.toNat ^^^ 1 < 2 * k.cur_vars := litNeg_lt_two_mul hlit
  have hte_lt : k.trail_end < k.cur_vars := hw.trail_end_lt_of_unassigned hlit hun
  have hte_mv : k.trail_end < c.max_vars := Nat.lt_of_lt_of_le hte_lt hcv_mv
  have hte_lt32 : k.trail_end < 2 ^ 32 := by
    have := c.hmaxv; unfold dimacsBound at this; omega
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hnot_var : ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hw.vals_zero_iff hlit).mp hun
  have hvals_get : ∀ l < 2 * k.cur_vars,
      k'.vals[l]?.getD 0#8 =
        if l = lit.toNat ^^^ 1 then 0xFF#8
        else if l = lit.toNat then 1#8
        else k.vals[l]?.getD 0#8 := fun l hl => by
    have hl1 : lit.toNat < k.vals.length := by rw [hcl.vals_len]; omega
    have hl2 : lit.toNat ^^^ 1 < (k.vals.set lit.toNat 1#8).length := by
      rw [List.length_set, hcl.vals_len]; omega
    by_cases hneg : l = lit.toNat ^^^ 1
    · subst hneg; dsimp only [k']; rw [List.getElem?_set_self hl2]; simp
    · dsimp only [k']; rw [List.getElem?_set_ne (Ne.symm hneg)]
      by_cases hpos : l = lit.toNat
      · subst hpos; rw [List.getElem?_set_self hl1]; simp [hneg]
      · rw [List.getElem?_set_ne (Ne.symm hpos)]; simp [hneg, hpos]
  have htrl_get : ∀ i < k.trail_end + 1,
      (k'.trl[i]?.getD 0#32).toNat =
        if i = k.trail_end then lit.toNat else (k.trl[i]?.getD 0#32).toNat := fun i _ => by
    by_cases hie : i = k.trail_end
    · subst hie; simp [k', List.getElem?_set_self (by rw [hcl.trl_len]; exact hte_mv)]
    · simp [k', hie, List.getElem?_set_ne (Ne.symm hie)]
  have hlvl_get : ∀ u < c.max_vars,
      (k'.lvl[u]?.getD 0#32).toNat =
        if u = v then 0 else (k.lvl[u]?.getD 0#32).toNat := fun u _ => by
    by_cases huv : u = v
    · subst huv; simp [k', List.getElem?_set_self (by rw [hcl.lvl_len]; exact hv_mv)]
    · simp [k', huv, List.getElem?_set_ne (Ne.symm huv)]
  have hrsn_get : ∀ u < c.max_vars,
      k'.rsns[u]?.getD 0xFFFFFFFF#32 =
        if u = v then 0xFFFFFFFF#32 else k.rsns[u]?.getD 0xFFFFFFFF#32 := fun u _ => by
    by_cases huv : u = v
    · subst huv; simp [k', List.getElem?_set_self (by rw [hcl.rsns_len]; exact hv_mv)]
    · simp [k', huv, List.getElem?_set_ne (Ne.symm huv)]
  refine
    { ext_sound := hw.ext_sound
      inconsistent_sound := hw.inconsistent_sound
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
      cur_level_le := by rw [hclv', hcl0]; exact Nat.zero_le _
      trail_lits_lt := fun i hi => by
        rw [hte'] at hi; rw [hcv', htrl_get i hi]; split
        · exact hlit
        · exact hw.trail_lits_lt i (by omega)
      trail_vars_nodup := fun i j hi hj heq => by
        rw [hte'] at hi hj; rw [htrl_get i hi, htrl_get j hj] at heq
        by_cases hie : i = k.trail_end <;> by_cases hje : j = k.trail_end
        · omega
        · subst hie; simp only [↓reduceIte, hje] at heq
          exact absurd heq.symm (hnot_var j (by omega))
        · subst hje; simp only [↓reduceIte, hie] at heq
          exact absurd heq (hnot_var i (by omega))
        · simp only [hie, hje, ↓reduceIte] at heq
          exact hw.trail_vars_nodup i j (by omega) (by omega) heq
      vals_domain := fun l hl => by
        rw [hcv'] at hl; rw [hvals_get l hl]; split
        · exact Or.inr (Or.inr rfl)
        · split
          · exact Or.inr (Or.inl rfl)
          · exact hw.vals_domain l hl
      vals_true_iff := fun l hl => by
        rw [hcv'] at hl; rw [hvals_get l hl, hte']
        constructor
        · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
          · simp [hneg] at h1
          · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
            · exact ⟨k.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hpos]⟩
            · simp only [hpos, ↓reduceIte] at h1
              obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
              have hne_i : i ≠ k.trail_end := by omega
              exact ⟨i, by omega, by rw [htrl_get i (by omega)]; simp [hne_i, heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
          by_cases hie : i = k.trail_end
          · simp only [hie, ↓reduceIte] at heq; subst heq; simp [hne_lit.symm]
          · simp only [hie, ↓reduceIte] at heq
            have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
            have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
            have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
            simp only [h1, h2, ↓reduceIte]; exact (hw.vals_true_iff l hl).mpr ⟨i, by omega, heq⟩
      vals_false_iff := fun l hl => by
        rw [hcv'] at hl; rw [hvals_get l hl, hte']
        constructor
        · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
          · refine ⟨k.trail_end, by omega, ?_⟩
            rw [htrl_get _ (by omega)]; simp [hneg]; exact (litNeg_litNeg _).symm
          · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
            · simp [hpos] at h1
            · simp only [hpos, ↓reduceIte] at h1
              obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h1
              have hne_i : i ≠ k.trail_end := by omega
              exact ⟨i, by omega, by rw [htrl_get i (by omega)]; simp [hne_i, heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
          by_cases hie : i = k.trail_end
          · simp only [hie, ↓reduceIte] at heq
            have hl_eq : l = lit.toNat ^^^ 1 := by
              have h := congrArg litNeg heq; have h1 : litNeg (l ^^^ 1) = l := litNeg_litNeg l
              rw [h1] at h; exact h.symm
            simp [hl_eq]
          · simp only [hie, ↓reduceIte] at heq
            have hlv : l / 2 ≠ v := by
              have h := hnot_var i (by omega); rw [heq] at h; rwa [fullInv_var_xor1] at h
            have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
            have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
            simp only [h1, h2, ↓reduceIte]; exact (hw.vals_false_iff l hl).mpr ⟨i, by omega, heq⟩
      lvl_le := fun i hi => by
        rw [hte'] at hi; rw [hclv', hcl0, htrl_get i hi]
        by_cases hie : i = k.trail_end
        · simp only [hie, ↓reduceIte]; rw [hlvl_get v hv_mv]; simp
        · have hilt : i < k.trail_end := by omega
          simp only [hie, ↓reduceIte]
          rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)]
          simp only [hnot_var i hilt, ↓reduceIte]
          have := hw.lvl_le i hilt; omega
      dec_earliest := fun i j hi hj _ hdec => by
        rw [hte'] at hi hj
        have hpos : 0 < (k'.lvl[(k'.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := hdec.1
        have hlv_eq : (k'.lvl[(k'.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
          rw [htrl_get j hj]
          by_cases hje : j = k.trail_end
          · simp only [hje, ↓reduceIte]; rw [hlvl_get v hv_mv]; simp
          · have hjlt : j < k.trail_end := by omega
            simp only [hje, ↓reduceIte]
            rw [hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega)]
            simp only [hnot_var j hjlt, ↓reduceIte]
            have := hw.lvl_le j hjlt; omega
        omega
      levels_inhabited := fun L hL1 hLle => by rw [hclv', hcl0] at hLle; omega
      level0_sound := fun i hi _ => by
        rw [hte'] at hi; rw [htrl_get i hi]
        by_cases hie : i = k.trail_end
        · simp only [hie, ↓reduceIte]; exact hl0
        · have hilt : i < k.trail_end := by omega
          simp only [hie, ↓reduceIte]
          exact hw.level0_sound i hilt (by have := hw.lvl_le i hilt; omega)
      trail_pos_inv := fun i hi => by
        rw [hte'] at hi; rw [htrl_get i hi]
        by_cases hie : i = k.trail_end
        · subst hie; simp only [↓reduceIte]
          change ((k'.trail_pos)[v]?.getD 0#32).toNat = k.trail_end
          rw [List.getElem?_set_self (by rw [hcl.trail_pos_len]; exact hv_mv),
            Option.getD_some, bv32_ofNat_toNat hte_lt32]
        · have hilt : i < k.trail_end := by omega
          simp only [hie, ↓reduceIte]
          change ((k'.trail_pos)[_]?.getD 0#32).toNat = i
          rw [List.getElem?_set_ne (hnot_var i hilt).symm]
          exact hw.trail_pos_inv i hilt
      level0_rsn_none := fun idx hidx _ => by
        rw [hte'] at hidx; rw [htrl_get idx hidx]
        by_cases hie : idx = k.trail_end
        · simp only [hie, ↓reduceIte]; rw [hrsn_get v hv_mv]; simp
        · have hilt : idx < k.trail_end := by omega
          simp only [hie, ↓reduceIte]
          rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)]
          simp only [hnot_var idx hilt, ↓reduceIte]
          exact hw.level0_rsn_none idx hilt (by have := hw.lvl_le idx hilt; omega)
      frame_trail_lt := fun L hL => by
        rw [hclv', hcl0] at hL; have hLz : L = 0 := by omega
        subst hLz; change (k.frame_trail[0]?.getD 0#32).toNat ≤ k'.trail_end
        rw [hte']; have := hw.frame_trail_lt 0 (by omega); omega
      frame_trail_mono := fun L1 L2 h1 h2 => by
        rw [hclv', hcl0] at h2; have h1z : L1 = 0 := by omega
        have h2z : L2 = 0 := by omega
        subst h1z h2z; exact Nat.le_refl _
      frame_trail_before_lt := fun L hL1 hLle => by rw [hclv', hcl0] at hLle; omega
      frame_dec_lt := fun L hL1 hLle => by rw [hclv', hcl0] at hLle; omega
      reason_inv := fun idx hidx hne => by
        rw [hte'] at hidx; exfalso; apply hne
        rw [htrl_get idx hidx]
        by_cases hie : idx = k.trail_end
        · simp only [hie, ↓reduceIte]; rw [hrsn_get v hv_mv]; simp
        · have hilt : idx < k.trail_end := by omega
          simp only [hie, ↓reduceIte]
          rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)]
          simp only [hnot_var idx hilt, ↓reduceIte]
          exact hw.level0_rsn_none idx hilt (by have := hw.lvl_le idx hilt; omega)
      reason_lit_mem := fun idx hidx hne => by
        rw [hte'] at hidx; exfalso; apply hne
        rw [htrl_get idx hidx]
        by_cases hie : idx = k.trail_end
        · simp only [hie, ↓reduceIte]; rw [hrsn_get v hv_mv]; simp
        · have hilt : idx < k.trail_end := by omega
          simp only [hie, ↓reduceIte]
          rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)]
          simp only [hnot_var idx hilt, ↓reduceIte]
          exact hw.level0_rsn_none idx hilt (by have := hw.lvl_le idx hilt; omega) }

/-! ## 2. Tumble Read-Loop & Prune-Loop Invariants -/

private def IngestTumReadInv (c : FullCfg) (accCnf : CNF Nat) (s : FullState)
    (cnfBytes : List UInt8) (i0 idx tlen elen : Nat) (taut : Bool) (revLits : List Nat)
    (mrk' : List (BitVec 8)) (tmp' fd' : List (BitVec 32)) : Prop :=
  let tum := decide (c.mv < c.extend_cap)
  i0 ≤ idx ∧ idx ≤ cnfBytes.length ∧ tlen ≤ c.mv ∧
  mrk'.length = c.max_vars ∧ tmp'.length = c.max_vars ∧ fd'.length = c.max_vars + 1 ∧
  s.scratch.extend_len ≤ elen ∧ elen ≤ c.extend_cap ∧
  TumbleInv tum c.mv elen fd' ∧
  TumbleCovers tum fd' (shiftDownCnf accCnf) ∧
  CNF.relabel (tumblePi tum fd') (shiftDownCnf accCnf) =
    CNF.relabel (tumblePi tum s.core.frame_dec) (shiftDownCnf accCnf) ∧
  (∀ e < c.mv, s.core.frame_dec[e]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    fd'[e]?.getD 0xFFFFFFFF#32 = s.core.frame_dec[e]?.getD 0xFFFFFFFF#32) ∧
  (∀ vext, TumbleValsRel tum c.mv s.core.frame_dec vext s.core.vals →
    TumbleUnusedZero tum c.mv s.scratch.extend_len s.core.vals →
    TumbleValsRel tum c.mv fd' vext s.core.vals) ∧
  (∀ l ∈ revLits, l < 2 * c.mv) ∧
  (tum = true → ∀ l ∈ revLits, fd'[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
  (∀ k < tlen, (tmp'[k]?.getD 0#32).toNat < 2 * c.mv) ∧
  (∀ k1 k2, k1 < tlen → k2 < tlen →
    (tmp'[k1]?.getD 0#32).toNat / 2 = (tmp'[k2]?.getD 0#32).toNat / 2 → k1 = k2) ∧
  (∀ v < c.max_vars, (∀ k < tlen, (tmp'[k]?.getD 0#32).toNat / 2 ≠ v) →
    mrk'[v]?.getD 0#8 = 0#8) ∧
  (∀ k < tlen, mrk'[(tmp'[k]?.getD 0#32).toNat / 2]?.getD 0#8 =
    BitVec.ofNat 8 ((tmp'[k]?.getD 0#32).toNat % 2 + 1)) ∧
  (taut = false → ∀ l ∈ revLits, ∃ k < tlen, (tmp'[k]?.getD 0#32).toNat = tumbleLit tum fd' l) ∧
  (∀ k < tlen, (tmp'[k]?.getD 0#32).toNat ∈ revLits.map (tumbleLit tum fd')) ∧
  (revLits = [] → taut = false) ∧
  (∀ l, revLits = [l] → taut = false ∧ tlen = 1 ∧ (tmp'[0]?.getD 0#32).toNat = tumbleLit tum fd' l)

private theorem ingestTumReadInv_with_fd {c : FullCfg} {accCnf : CNF Nat} {s : FullState}
    {cnfBytes : List UInt8} {i0 idx tlen elen ev : Nat} {taut : Bool} {revLits : List Nat}
    {mrk' : List (BitVec 8)} {tmp' fd' : List (BitVec 32)}
    (htum : decide (c.mv < c.extend_cap) = true)
    (hc_mv : c.mv ≤ c.max_vars) (hev : ev < c.mv)
    (hun : fd'[ev]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hri : IngestTumReadInv c accCnf s cnfBytes i0 idx tlen elen taut revLits mrk' tmp' fd') :
    let fd_n := fd'.set ev (BitVec.ofNat 32 elen)
    elen < c.mv ∧
    IngestTumReadInv c accCnf s cnfBytes i0 idx tlen (elen + 1) taut revLits mrk' tmp' fd_n := by
  intro fd_n
  rcases hri with ⟨hi0, hidx, htl, hmkl, htmpl, hfdl, hel_ge, hel_le, hti, htc, hrel_eq,
    hfd_mono, hvals_lift, hrev_lt, hrev_cov, htmp_lt, htmp_nd, hmrk_zero, hmrk_pos,
    hcov, hsub_rev, hnil_taut, hunit_r⟩
  have hmv_bd := c.hmv; unfold dimacsBound at hmv_bd
  have hlt_ec : c.mv < c.extend_cap := of_decide_eq_true htum
  have hnxt_lt : elen < c.mv := tumbleMapInv_next_lt (hti htum) hev hun
  have hfd_len_ge : c.mv ≤ fd'.length := by omega
  have hmap_eq : ∀ x ∈ revLits, tumbleLit (decide (c.mv < c.extend_cap)) fd_n x =
      tumbleLit (decide (c.mv < c.extend_cap)) fd' x := fun x hx =>
    tumbleLit_set_eq hun (fun ht => hrev_cov ht x hx)
  refine ⟨hnxt_lt, hi0, hidx, htl, hmkl, htmpl, by simp [fd_n, hfdl], by omega, by omega,
    fun ht => tumbleMapInv_set (hti ht) hev hfd_len_ge (by omega) hun,
    tumbleCovers_set htc hun,
    (cnf_relabel_tumble_set htc hun).trans hrel_eq,
    fun e he hne => by
      have hne_ev : ev ≠ e := fun heq => by
        subst heq; exact hne ((hfd_mono ev hev hne).symm.trans hun)
      rw [List.getElem?_set_ne hne_ev]; exact hfd_mono e he hne,
    fun vext hvr hunz =>
      tumbleValsRel_set_unmapped (hvals_lift vext hvr hunz)
        (tumbleUnusedZero_mono hunz hel_ge) hev hfd_len_ge hnxt_lt (by omega) hun,
    hrev_lt,
    fun ht x hx => by
      have hcovx := hrev_cov ht x hx
      have hne : ev ≠ x / 2 := fun heq => by subst heq; exact hcovx hun
      rw [List.getElem?_set_ne hne]; exact hcovx,
    htmp_lt, htmp_nd, hmrk_zero, hmrk_pos,
    fun hnt x hx => by rw [hmap_eq x hx]; exact hcov hnt x hx,
    fun k hk => by
      have hm := hsub_rev k hk
      rw [List.mem_map] at hm ⊢
      obtain ⟨x, hx, hxe⟩ := hm
      exact ⟨x, hx, (hmap_eq x hx).trans hxe⟩,
    hnil_taut,
    fun l hl => by
      obtain ⟨h1, h2, h3⟩ := hunit_r l hl
      exact ⟨h1, h2, h3.trans (hmap_eq l (by rw [hl]; exact List.mem_cons_self)).symm⟩⟩

private theorem ingestTumReadInv_push {c : FullCfg} {accCnf : CNF Nat} {s : FullState}
    {cnfBytes : List UInt8} {i0 idx j tlen elen l : Nat} {taut : Bool} {revLits : List Nat}
    {mrk' : List (BitVec 8)} {tmp' fd' : List (BitVec 32)}
    (hc_mv : c.mv ≤ c.max_vars) (hi_j : i0 ≤ j) (hj : j ≤ cnfBytes.length) (htl : tlen < c.mv)
    (hl_mv : l < 2 * c.mv)
    (hl_cov : decide (c.mv < c.extend_cap) = true →
      fd'[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hri : IngestTumReadInv c accCnf s cnfBytes i0 idx tlen elen taut revLits mrk' tmp' fd')
    (hmiss_v : ∀ k < tlen,
      (tmp'[k]?.getD 0#32).toNat / 2 ≠ tumbleLit (decide (c.mv < c.extend_cap)) fd' l / 2) :
    let tl := tumbleLit (decide (c.mv < c.extend_cap)) fd' l
    IngestTumReadInv c accCnf s cnfBytes i0 j (tlen + 1) elen taut (l :: revLits)
      (mrk'.set (tl / 2) (BitVec.ofNat 8 (tl % 2 + 1)))
      (tmp'.set tlen (BitVec.ofNat 32 tl)) fd' := by
  intro tl
  rcases hri with ⟨_, _, _, hmkl, htmpl, hfdl, hel_ge, hel_le, hti, htc, hrel_eq,
    hfd_mono, hvals_lift, hrev_lt, hrev_cov, htmp_lt, htmp_nd, hmrk_zero, hmrk_pos,
    hcov, hsub_rev, hnil_taut, _⟩
  have hmv_bd := c.hmv; unfold dimacsBound at hmv_bd
  have htl_mv : tl < 2 * c.mv := tumbleLit_lt hti hl_mv hl_cov
  have htl32 : tl < 2 ^ 32 := by omega
  have hn_lt : tlen < tmp'.length := by rw [htmpl]; omega
  have hm_lt : tl / 2 < mrk'.length := by rw [hmkl]; omega
  refine ⟨hi_j, hj, by omega, by simp [hmkl], by simp [htmpl], hfdl, hel_ge, hel_le,
    hti, htc, hrel_eq, hfd_mono, hvals_lift,
    (fun x hx => (List.mem_cons.mp hx).elim (fun h => h ▸ hl_mv) (hrev_lt x)),
    (fun ht x hx => (List.mem_cons.mp hx).elim (fun h => h ▸ hl_cov ht) (hrev_cov ht x)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk; by_cases hkt : k = tlen
    · subst k; simp [List.getElem?_set_self hn_lt, bv32_ofNat_toNat htl32, htl_mv]
    · simp [List.getElem?_set_ne (Ne.symm hkt), htmp_lt k (by omega)]
  · intro k1 k2 h1 h2 heq; by_cases hk1 : k1 = tlen <;> by_cases hk2 : k2 = tlen
    · omega
    · subst hk1; simp [List.getElem?_set_self hn_lt, List.getElem?_set_ne (Ne.symm hk2),
        bv32_ofNat_toNat htl32] at heq; exact absurd heq.symm (hmiss_v k2 (by omega))
    · subst hk2; simp [List.getElem?_set_self hn_lt, List.getElem?_set_ne (Ne.symm hk1),
        bv32_ofNat_toNat htl32] at heq; exact absurd heq (hmiss_v k1 (by omega))
    · simp [List.getElem?_set_ne (Ne.symm hk1), List.getElem?_set_ne (Ne.symm hk2)] at heq
      exact htmp_nd k1 k2 (by omega) (by omega) heq
  · intro v hv hmiss
    have hne : v ≠ tl / 2 := by
      have h := hmiss tlen (by omega)
      simp [List.getElem?_set_self hn_lt, bv32_ofNat_toNat htl32] at h; exact Ne.symm h
    rw [List.getElem?_set_ne (Ne.symm hne)]
    exact hmrk_zero v hv fun k hk => by
      have h := hmiss k (by omega); simpa [List.getElem?_set_ne (by omega : tlen ≠ k)] using h
  · intro k hk; by_cases hkt : k = tlen
    · subst k; simp [List.getElem?_set_self hn_lt, List.getElem?_set_self hm_lt,
        bv32_ofNat_toNat htl32]
    · have hne_k : tl / 2 ≠ (tmp'[k]?.getD 0#32).toNat / 2 := Ne.symm (hmiss_v k (by omega))
      rw [List.getElem?_set_ne (Ne.symm hkt), List.getElem?_set_ne hne_k]
      exact hmrk_pos k (by omega)
  · intro ht x hx; rcases List.mem_cons.mp hx with hxl | hx'
    · rw [hxl]
      exact ⟨tlen, by omega, by simp [List.getElem?_set_self hn_lt, bv32_ofNat_toNat htl32, tl]⟩
    · obtain ⟨k, hk, hget⟩ := hcov ht x hx'
      exact ⟨k, by omega, by simpa [List.getElem?_set_ne (by omega : tlen ≠ k)] using hget⟩
  · intro k hk; by_cases hkt : k = tlen
    · subst k
      simp only [List.getElem?_set_self hn_lt, Option.getD_some, bv32_ofNat_toNat htl32,
        List.map_cons]
      exact List.mem_cons_self
    · simp only [List.getElem?_set_ne (Ne.symm hkt), List.map_cons]
      exact List.mem_cons_of_mem tl (hsub_rev k (by omega))
  · intro hc; cases hc
  · intro l' hl'; rcases List.cons.inj hl' with ⟨hl_eq, rfl⟩
    have ht0 : tlen = 0 := by
      cases tlen with | zero => rfl | succ k => exact absurd (hsub_rev 0 (by omega)) (by simp)
    subst ht0
    refine ⟨hnil_taut rfl, rfl, ?_⟩
    rw [← hl_eq]; simp [List.getElem?_set_self hn_lt, bv32_ofNat_toNat htl32, tl]

private theorem ingestTum_dup_cov {tum : Bool} {mv tlen : Nat} {tmp' fd' : List (BitVec 32)}
    {mrk' : List (BitVec 8)} {revLits : List Nat} {taut' taut_v : Bool} {l k0 : Nat}
    {mv_b : BitVec 8}
    (hmkl : mv ≤ mrk'.length) (hv_lt : tumbleLit tum fd' l / 2 < mv) (hk0 : k0 < tlen)
    (htaut' : taut' = if mv_b = BitVec.ofNat 8 (tumbleLit tum fd' l % 2 + 1) then taut_v else true)
    (hmv_b : mv_b = mrk'[tumbleLit tum fd' l / 2]'(by omega))
    (hmv_pos : mrk'[tumbleLit tum fd' l / 2]'(by omega) =
      BitVec.ofNat 8 ((tmp'[k0]?.getD 0#32).toNat % 2 + 1))
    (hcov : taut_v = false → ∀ x ∈ revLits,
      ∃ k < tlen, (tmp'[k]?.getD 0#32).toNat = tumbleLit tum fd' x)
    (hk0_v : (tmp'[k0]?.getD 0#32).toNat / 2 = tumbleLit tum fd' l / 2) :
    taut' = false → ∀ x ∈ l :: revLits,
      ∃ k < tlen, (tmp'[k]?.getD 0#32).toNat = tumbleLit tum fd' x := by
  intro hnt' x hx
  by_cases hmeq : mv_b = BitVec.ofNat 8 (tumbleLit tum fd' l % 2 + 1)
  · simp only [hmeq, ↓reduceIte] at htaut'
    rcases List.mem_cons.mp hx with rfl | hx'
    · refine ⟨k0, hk0, ?_⟩
      have h1 := hmv_pos.symm.trans (hmv_b.symm.trans hmeq)
      have hmod := congrArg BitVec.toNat h1
      simp only [BitVec.toNat_ofNat] at hmod; omega
    · exact hcov (htaut' ▸ hnt') x hx'
  · simp only [hmeq, ↓reduceIte] at htaut'; rw [htaut'] at hnt'; cases hnt'

private def IngestTumPruneInv (c : FullCfg) (s : FullState) (tmp' fd' : List (BitVec 32))
    (revLits : List Nat) (tlen keep i : Nat) (tmp'' : List (BitVec 32)) : Prop :=
  let tum := decide (c.mv < c.extend_cap)
  keep ≤ i ∧ i ≤ tlen ∧ tmp''.length = c.max_vars ∧
  (∀ k, i ≤ k → k < tlen → tmp''[k]? = tmp'[k]?) ∧
  (∀ k < keep, (tmp''[k]?.getD 0#32).toNat < 2 * c.mv ∧
    s.core.vals[(tmp''[k]?.getD 0#32).toNat]?.getD 0#8 = 0#8) ∧
  (∀ k < keep, ∃ m < i, tmp''[k]? = tmp'[m]?) ∧
  (∀ k1 k2, k1 < keep → k2 < keep →
    (tmp''[k1]?.getD 0#32).toNat / 2 = (tmp''[k2]?.getD 0#32).toNat / 2 → k1 = k2) ∧
  (∀ k < i, (∃ j < keep, tmp''[j]? = tmp'[k]?) ∨
    s.core.vals[(tmp'[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
  (∀ l < 2 * c.mv, revLits = [l] → s.core.vals[tumbleLit tum fd' l]?.getD 0#8 = 0#8 →
    i = 1 → keep = 1 ∧ (tmp''[0]?.getD 0#32).toNat = tumbleLit tum fd' l) ∧
  (∀ l < 2 * c.mv, revLits = [l] → s.core.vals[tumbleLit tum fd' l]?.getD 0#8 = 0xFF#8 →
    i = 1 → keep = 0)

private theorem ingestTumPruneInv_push {c : FullCfg} {s : FullState}
    {tmp' tmp'' fd' : List (BitVec 32)} {revLits : List Nat} {tlen keep i : Nat} {li : BitVec 32}
    (hc_mv : c.mv ≤ c.max_vars)
    (hlt : i < tlen) (htlen_le : tlen ≤ c.mv) (htmpl : tmp'.length = c.max_vars)
    (htmp_nd : ∀ k1 k2, k1 < tlen → k2 < tlen →
      (tmp'[k1]?.getD 0#32).toNat / 2 = (tmp'[k2]?.getD 0#32).toNat / 2 → k1 = k2)
    (hli_eq : li = tmp'[i]'(by rw [htmpl]; omega)) (hli_lt : li.toNat < 2 * c.mv)
    (hlv_getD : s.core.vals[li.toNat]?.getD 0#8 = 0#8)
    (hunit0 : ∀ l, revLits = [l] →
      (tmp'[0]?.getD 0#32).toNat = tumbleLit (decide (c.mv < c.extend_cap)) fd' l)
    (hpi : IngestTumPruneInv c s tmp' fd' revLits tlen keep i tmp'') :
    IngestTumPruneInv c s tmp' fd' revLits tlen (keep + 1) (i + 1) (tmp''.set keep li) := by
  rcases hpi with ⟨hk_le, hi_le, htmp'l, htail, hkeep_un, hkeep_src, hkeep_nd, hpruned, _, _⟩
  have htmv : tlen ≤ c.max_vars := Nat.le_trans htlen_le hc_mv
  have hk_bd : keep < tmp''.length := by rw [htmp'l]; omega
  refine ⟨by omega, by omega, by simp [htmp'l], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk1 hk2; rw [List.getElem?_set_ne (by omega)]; exact htail k (by omega) hk2
  · intro k hk; by_cases hkk : k = keep
    · subst k; rw [List.getElem?_set_self hk_bd, Option.getD_some]
      exact ⟨hli_lt, hlv_getD⟩
    · rw [List.getElem?_set_ne (Ne.symm hkk)]; exact hkeep_un k (by omega)
  · intro k hk; by_cases hkk : k = keep
    · subst k; refine ⟨i, by omega, ?_⟩
      rw [List.getElem?_set_self hk_bd, List.getElem?_eq_getElem (by rw [htmpl]; omega), hli_eq]
    · rw [List.getElem?_set_ne (Ne.symm hkk)]
      obtain ⟨m, hm, hmeq⟩ := hkeep_src k (by omega)
      exact ⟨m, by omega, hmeq⟩
  · have hmiss_li : ∀ k < keep, (tmp''[k]?.getD 0#32).toNat / 2 ≠ li.toNat / 2 := by
      intro k hk heq
      obtain ⟨m, hm, hmeq⟩ := hkeep_src k hk
      rw [hmeq] at heq
      have hli_get : li.toNat = (tmp'[i]?.getD 0#32).toNat := by
        rw [List.getElem?_eq_getElem (by rw [htmpl]; omega), Option.getD_some, ← hli_eq]
      rw [hli_get] at heq
      have := htmp_nd m i (by omega) hlt heq; omega
    intro k1 k2 h1 h2 heq
    by_cases hk1 : k1 = keep <;> by_cases hk2 : k2 = keep
    · omega
    · subst hk1; rw [List.getElem?_set_self hk_bd, Option.getD_some,
        List.getElem?_set_ne (Ne.symm hk2)] at heq
      exact absurd heq.symm (hmiss_li k2 (by omega))
    · subst hk2; rw [List.getElem?_set_self hk_bd, Option.getD_some,
        List.getElem?_set_ne (Ne.symm hk1)] at heq
      exact absurd heq (hmiss_li k1 (by omega))
    · rw [List.getElem?_set_ne (Ne.symm hk1), List.getElem?_set_ne (Ne.symm hk2)] at heq
      exact hkeep_nd k1 k2 (by omega) (by omega) heq
  · intro k hk; by_cases hki : k = i
    · subst k; refine Or.inl ⟨keep, by omega, ?_⟩
      rw [List.getElem?_set_self hk_bd, List.getElem?_eq_getElem (by rw [htmpl]; omega), hli_eq]
    · rcases hpruned k (by omega) with ⟨j, hj, hjeq⟩ | hfl
      · exact Or.inl ⟨j, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hjeq⟩
      · exact Or.inr hfl
  · intro l _ hrev _ hi1
    have hi0 : i = 0 := by omega
    have hk0 : keep = 0 := by omega
    subst hi0 hk0; refine ⟨rfl, ?_⟩
    rw [List.getElem?_set_self (by rw [htmp'l]; omega), Option.getD_some, hli_eq]
    simpa [List.getElem?_eq_getElem (l := tmp') (i := 0) (by rw [htmpl]; omega)] using hunit0 l hrev
  · intro l _ hrev hvf hi1
    have hi0 : i = 0 := by omega
    subst hi0; have hl0 := hunit0 l hrev
    rw [List.getElem?_eq_getElem (l := tmp') (i := 0) (by rw [htmpl]; omega), Option.getD_some,
      ← hli_eq] at hl0
    rw [← hl0] at hvf; exact absurd (hlv_getD.symm.trans hvf) (by decide)

private theorem ingestTumPruneInv_skip {c : FullCfg} {s : FullState}
    {tmp' tmp'' fd' : List (BitVec 32)} {revLits : List Nat} {tlen keep i : Nat} {li : BitVec 32}
    (hc_mv : c.mv ≤ c.max_vars)
    (hlt : i < tlen) (htlen_le : tlen ≤ c.mv) (htmpl : tmp'.length = c.max_vars)
    (hli_eq : li = tmp'[i]'(by rw [htmpl]; have htmv := Nat.le_trans htlen_le hc_mv; omega))
    (hlv_ff : s.core.vals[li.toNat]?.getD 0#8 = 0xFF#8)
    (hunit0 : ∀ l, revLits = [l] →
      (tmp'[0]?.getD 0#32).toNat = tumbleLit (decide (c.mv < c.extend_cap)) fd' l)
    (hpi : IngestTumPruneInv c s tmp' fd' revLits tlen keep i tmp'') :
    IngestTumPruneInv c s tmp' fd' revLits tlen keep (i + 1) tmp'' := by
  rcases hpi with ⟨hk_le, hi_le, htmp'l, htail, hkeep_un, hkeep_src, hkeep_nd, hpruned, _, _⟩
  have htmv : tlen ≤ c.max_vars := Nat.le_trans htlen_le hc_mv
  refine ⟨by omega, by omega, htmp'l, fun k hk1 hk2 => htail k (by omega) hk2, hkeep_un,
    (fun k hk => let ⟨m, hm, hm_eq⟩ := hkeep_src k hk; ⟨m, by omega, hm_eq⟩), hkeep_nd, ?_, ?_, ?_⟩
  · intro k hk; by_cases hki : k = i
    · subst k; refine Or.inr ?_
      rw [List.getElem?_eq_getElem (i := i) (by rw [htmpl]; omega), Option.getD_some, ← hli_eq]
      exact hlv_ff
    · exact hpruned k (by omega)
  · intro l _ hrev hv0 hi1
    have hi0 : i = 0 := by omega
    subst hi0; have hl0 := hunit0 l hrev
    rw [List.getElem?_eq_getElem (l := tmp') (i := 0) (by rw [htmpl]; omega), Option.getD_some,
      ← hli_eq] at hl0
    rw [← hl0] at hv0; exact absurd (hlv_ff.symm.trans hv0) (by decide)
  · intro _ _ _ _ _; omega

private theorem ingestTum_keep_entails {c : FullCfg} {F0 F1_rel : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {tmp' tmp'' fd' : List (BitVec 32)}
    {revLits : List Nat} {tlen keep : Nat}
    (hcv : s.core.cur_vars = c.mv)
    (hw : FullWitnessInv c F0 F_cur s.core) (hcl0 : s.core.cur_level = 0)
    (htlen_le : tlen ≤ c.mv) (htmpl : tmp'.length = c.max_vars) (hc_mv : c.mv ≤ c.max_vars)
    (htmp_lt : ∀ k < tlen, (tmp'[k]?.getD 0#32).toNat < 2 * c.mv)
    (hF1_ent : F1_rel.Entails (cnfOfClauses F_cur))
    (hF1_cl : F1_rel.EntailsClause (cnfClause ((tmp'.take tlen).map BitVec.toNat)))
    (hpi : IngestTumPruneInv c s tmp' fd' revLits tlen keep tlen tmp'') :
    F1_rel.EntailsClause (cnfClause ((tmp''.take keep).map BitVec.toNat)) := by
  rcases hpi with ⟨hk_le, _, htmp'l, _, _, _, _, hpruned, _, _⟩
  refine entails_of_mem_or_false hF1_cl fun l hl => ?_
  rw [List.mem_map] at hl; obtain ⟨x, hx, rfl⟩ := hl
  rw [List.mem_iff_getElem] at hx; obtain ⟨k, hk, hxk⟩ := hx
  have hklt : k < tlen := by rw [List.length_take] at hk; omega
  rw [List.getElem_take] at hxk
  rcases hpruned k hklt with ⟨j, hj, hjeq⟩ | hfl
  · refine Or.inl (List.mem_map.mpr ⟨x, ?_, rfl⟩)
    rw [List.mem_iff_getElem]; refine ⟨j, by rw [List.length_take]; omega, ?_⟩
    rw [List.getElem_take]; rw [List.getElem?_eq_getElem (by rw [htmp'l]; omega),
      List.getElem?_eq_getElem (by rw [htmpl]; omega)] at hjeq
    exact (Option.some.inj hjeq).trans hxk
  · refine Or.inr ?_
    have hxk_get : (tmp'[k]?.getD 0#32).toNat = x.toNat := by
      rw [List.getElem?_eq_getElem (by rw [htmpl]; omega), Option.getD_some, hxk]
    rw [hxk_get] at hfl
    have hx_lt : x.toNat < 2 * s.core.cur_vars := by
      have := htmp_lt k hklt; rw [hcv, ← hxk_get]; exact this
    obtain ⟨ti, hti, htr_eq⟩ := (hw.vals_false_iff x.toNat hx_lt).mp hfl
    have hlvl0 : (s.core.lvl[(s.core.trl[ti]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
      have := hw.lvl_le ti hti; omega
    have hent0 := hw.level0_sound ti hti hlvl0
    have hent_F1 : F1_rel.EntailsClause
        (cnfClause [(s.core.trl[ti]?.getD 0#32).toNat]) :=
      CNF.entails_clause_trans hF1_ent hent0
    rwa [htr_eq] at hent_F1

private theorem ingestTum_st3_inv {c : FullCfg} {F0 F1 : CNF Nat} {F_cur : List (List Nat)}
    {st2 st3 : FullState}
    (hinv : FullSparseInvW c F0 F_cur st2) (hent : F1.Entails (cnfOfClauses F_cur))
    (hlen3 : st3.LengthsOk c) (hmrk : st3.core.mrk = st2.core.mrk)
    (hs1 : st3 = { st2 with core := { st2.core with tmp := st3.core.tmp } }) :
    FullSparseInvW c F1 F_cur st3 := by
  obtain ⟨_, hw0, hltm0, hnd0, hext0, hdm0⟩ := hinv
  have hltm : FullLitMarksClear c st3 := by
    refine ⟨fun v hv => by rw [hmrk]; exact hltm0.1 v hv, ?_⟩
    rw [hs1]; exact hltm0.2
  have hnd : FullArenaVarsNodup st3 := by rw [hs1]; exact hnd0
  have hext_sc : FullExtScratchOk c st3 := by rw [hs1]; exact hext0
  rw [hs1] at hlen3 ⊢
  refine ⟨hlen3,
    { hw0 with
      ext_sound := extUnsatSound_of_entails_tum hw0.ext_sound.1 hent
      arena := { hw0.arena with len_ok := hw0.arena.len_ok }
      watches := hw0.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
    ?_, ?_, ?_, hdm0⟩
  · simpa [← hs1] using hltm
  · simpa [← hs1] using hnd
  · simpa [← hs1] using hext_sc

private theorem tumbleValsRel_vals_of_vext_zero {tum : Bool} {mv l : Nat}
    {fd : List (BitVec 32)} {vext vint : List (BitVec 8)}
    (hrel : TumbleValsRel tum mv fd vext vint) (hl : l < 2 * mv)
    (hmap : tum = true → fd[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hv0 : vext[l]?.getD 0#8 = 0#8) :
    vint[tumbleLit tum fd l]?.getD 0#8 = 0#8 := by
  have h := hrel l hl
  have hnotun : ¬ (tum = true ∧ fd[l / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) := by
    rintro ⟨ht, hff⟩; exact hmap ht hff
  simp only [hnotun, ↓reduceIte] at h
  exact h.symm.trans hv0

private theorem tumbleValsRel_vals_of_vext_ff {tum : Bool} {mv l : Nat}
    {fd0 fd' : List (BitVec 32)} {vext vint : List (BitVec 8)}
    (hrel0 : TumbleValsRel tum mv fd0 vext vint)
    (hmono : ∀ e < mv, fd0[e]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      fd'[e]?.getD 0xFFFFFFFF#32 = fd0[e]?.getD 0xFFFFFFFF#32)
    (hl : l < 2 * mv) (hvf : vext[l]?.getD 0#8 = 0xFF#8) :
    vint[tumbleLit tum fd' l]?.getD 0#8 = 0xFF#8 := by
  have h := hrel0 l hl
  rw [hvf] at h
  have hnotun : ¬ (tum = true ∧ fd0[l / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) := by
    rintro ⟨ht, hff⟩; simp [ht, hff] at h
  simp only [hnotun, ↓reduceIte] at h
  have hlit_eq : tumbleLit tum fd' l = tumbleLit tum fd0 l := by
    cases tum with
    | false => rfl
    | true =>
      have hne0 : fd0[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 :=
        fun hff => hnotun ⟨rfl, hff⟩
      unfold tumbleLit tumblePi
      simp only [↓reduceIte, hmono (l / 2) (by omega) hne0]
  rw [hlit_eq]; exact h.symm

/-! ## 3. Main Theorem: `full_ingest_cl_tum_wp` -/

/-- Tumble + S11-3 lazy-activation clause ingestion satisfies `fullIngestClTumSpec`. -/
theorem full_ingest_cl_tum_wp (Γ : Env)
    (hLit : ∀ args m Q X, kissatNextLitSpec args m Q X →
      Γ "kissat_next_lit" [i64, i64] [i64] args m Q X)
    (hAct : ∀ args m Q X, fullActivateLitFidSpec args m Q X →
      Γ "full_activate_lit_fid" [i64, i32] [] args m Q X)
    (hAssign : ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hAddCl : ∀ args m Q X, fullAddClauseSpec args m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] args m Q X) :
    ∀ args m Q X, fullIngestClTumSpec args m Q X →
      Func.wp Γ full_ingest_cl_tum_body args m Q X := by
  rintro ⟨h, cend, ⟨⟩⟩ m Q X
    ⟨c, accCnf, F_cur, s, cnf_ptr, cnfBytes, i0, R, rfl, rfl, hfit, hi0,
      hcv, hdcur, hcl0, hti0, htc0, hvb0, hinv, hent_init, hm, hQ⟩
  let tum : Bool := decide (c.mv < c.extend_cap)
  have hmv := c.hmv; have hmaxv := c.hmaxv; have hext_bd := c.hext
  unfold dimacsBound at hmv hmaxv hext_bd
  have hlen := hinv.1; have hcok := hlen.core_ok; have hw0 := hinv.2.1
  have hc_mv : c.mv ≤ c.max_vars := by rw [← hcv]; exact hcok.cur_vars_le
  have htum_ult : (BitVec.ofNat 64 c.mv).ult (BitVec.ofNat 64 c.extend_cap) = tum := by
    rw [bv_ult_eq (by omega) (by omega)]
  unfold Func.wp full_ingest_cl_tum_body
  have hm0 : (FullMem c s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
  c0_hsteps_nogrp
  let st_r (dc dv : BitVec 64) (mk : List (BitVec 8)) (tp fd : List (BitVec 32))
      (elen : Nat) : FullState :=
    { core := { s.core with d_cur := dc, d_val := dv, mrk := mk, tmp := tp, frame_dec := fd }
      scratch := { s.scratch with extend_len := elen } }
  have hst0 : st_r (cnf_ptr + BitVec.ofNat 64 i0) s.core.d_val s.core.mrk s.core.tmp
      s.core.frame_dec s.scratch.extend_len = s := by
    cases s with
    | mk core scratch =>
      dsimp only [st_r]; dsimp only at hdcur; rw [← hdcur]
  refine wp_loop_break_group (brkTs := [i32, .bool, .bool]) (lpTs := [i32, .bool])
    (fun (tlen_v, taut_v, err_v, ()) mb => ∃ idx tlen elen revLits mrk' tmp' fd' dcur dval,
      let st := st_r dcur dval mrk' tmp' fd' elen
      (FullMem c st ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) mb ∧
      tlen_v = BitVec.ofNat 32 tlen ∧
      IngestTumReadInv c accCnf s cnfBytes i0 idx tlen elen taut_v revLits mrk' tmp' fd' ∧
      (err_v = true → parseClause c.mv (cnfBytes.drop i0) = none) ∧
      (err_v = false → i0 < idx ∧ dcur = cnf_ptr + BitVec.ofNat 64 idx ∧
        parseClause c.mv (cnfBytes.drop i0) =
          some (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral),
            cnfBytes.drop idx)))
    (fun r (tlen_v, taut_v, ()) ml => ∃ idx tlen elen revLits mrk' tmp' fd' dval,
      let st := st_r (cnf_ptr + BitVec.ofNat 64 idx) dval mrk' tmp' fd' elen
      (FullMem c st ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) ml ∧
      r = cnfBytes.length - idx ∧ tlen_v = BitVec.ofNat 32 tlen ∧
      IngestTumReadInv c accCnf s cnfBytes i0 idx tlen elen taut_v revLits mrk' tmp' fd' ∧
      parseClauseAux ((cnfBytes.drop idx).length + 1) c.mv
        (revLits.map kissatLitToDimacsLiteral) (cnfBytes.drop idx) =
        parseClause c.mv (cnfBytes.drop i0))
    ?_ ?_ ?_
  · -- Post-read-loop continuation (mark-clear, prune, activate, commit)
    rintro _ ⟨tlen_v, taut_v, err_v, ⟨⟩⟩ mb
      ⟨idx, tlen, elen, revLits, mrk', tmp', fd', dcur, dval, hmb, rfl, hri, herr_p, hok_p⟩
    obtain ⟨hi_le, hidx, htlen_le, hmkl, htmpl, hfdl, hel_ge, hel_le, hti_r, htc_r, hrel_eq,
      hfd_mono, hvals_lift, hrev_lt, hrev_cov, htmp_lt, htmp_nd,
      hmrk_zero, hmrk_pos, hcov, hsub_rev, hnil_taut, hunit_r⟩ := hri
    p_lets
    -- Mark-clear loop (`while (k < tlen)`)
    refine wp_loop_group (ts := [i32])
      (fun r2 (kv, ()) m2 => ∃ k mrk'',
        (FullMem c (st_r dcur dval mrk'' tmp' fd' elen) ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m2 ∧
        k ≤ tlen ∧ r2 = tlen - k ∧ kv = BitVec.ofNat 32 k ∧ mrk''.length = c.max_vars ∧
        (∀ v < c.max_vars, (∀ j, k ≤ j → j < tlen → (tmp'[j]?.getD 0#32).toNat / 2 ≠ v) →
          mrk''[v]?.getD 0#8 = 0#8)) ?_ ?_
    · rintro L2 r2 ⟨kv, ⟨⟩⟩ m2 ih2 ⟨k, mrk'', hm2, hkle, rfl, rfl, hmk''l, hclr⟩
      p_lets
      have hult_k := bv32_ult_eq (a := k) (b := tlen) (by omega) (by omega)
      refine wp_head_jnz_iff (b := decide (k < tlen)) (by simpa [Arg.val_var] using hult_k) ?_
      rw [decide_eq_true_eq, decide_eq_false_iff_not]
      refine ⟨fun hklt => ?_, fun hkge => ?_⟩
      · p_lets
        rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega), bv64_mul4_nat]
        have htm_bd_k : k < (st_r dcur dval mrk'' tmp' fd' elen).core.tmp.length := by
          dsimp [st_r]; rw [htmpl]; omega
        refine wp_load_of (load_full_tmp (i := k) htm_bd_k hm2) ?_; p_lets
        let kv32 := tmp'[k]'(by rw [htmpl]; omega)
        have hkv32_st : (st_r dcur dval mrk'' tmp' fd' elen).core.tmp[k]'htm_bd_k = kv32 := rfl
        rw [hkv32_st]
        have hkvar_lt : kv32.toNat / 2 < c.mv := by
          have := htmp_lt k hklt
          rw [List.getElem?_eq_getElem (by rw [htmpl]; omega), Option.getD_some] at this
          change kv32.toNat < 2 * c.mv at this; omega
        refine wp_join_group (ts := [])
          (fun () m_in => ∃ mrk''',
            (FullMem c (st_r dcur dval mrk''' tmp' fd' elen) ⋆
              (bytes cnf_ptr cnfBytes ⋆ R)) m_in ∧
            mrk'''.length = c.max_vars ∧
            (∀ v < c.max_vars,
              (∀ j, k + 1 ≤ j → j < tlen → (tmp'[j]?.getD 0#32).toNat / 2 ≠ v) →
              mrk'''[v]?.getD 0#8 = 0#8))
          (fun _ ⟨⟩ m_in ⟨mrk''', hm_in, hmk'''l, hclr'''⟩ => by
            p_lets
            rw [bv32_add1_nat (by omega)]
            exact ih2 (tlen - (k + 1)) _ m_in (by omega)
              ⟨k + 1, mrk''', hm_in, by omega, rfl, rfl, hmk'''l, hclr'''⟩)
          (fun Jk hJk => by
            p_lets; refine wp_load_of (load_full_mv hm2) ?_; p_lets
            rw [bv32_zext64_eq, bv32_lshr1]
            have hult_kv : (BitVec.ofNat 64 (kv32.toNat / 2)).ult (BitVec.ofNat 64 c.mv) =
                true := by rw [bv_ult_eq (by omega) (by omega)]; simp [hkvar_lt]
            refine wp_head_jnz_iff (b := true) (by simpa [Arg.val_var] using hult_kv) ?_
            refine ⟨fun _ => ?_, fun h => (by cases h)⟩
            p_lets; rw [bv32_zext64_eq, bv32_lshr1]
            have hmk_bd_kv : kv32.toNat / 2 <
                (st_r dcur dval mrk'' tmp' fd' elen).core.mrk.length := by
              dsimp [st_r]; rw [hmk''l]; omega
            obtain ⟨okm, hmm⟩ := store_full_mrk (i := kv32.toNat / 2) 0#8 hmk_bd_kv hm2
            refine ⟨okm, ?_⟩; p_lets
            have heq : ({ st_r dcur dval mrk'' tmp' fd' elen with core :=
                { (st_r dcur dval mrk'' tmp' fd' elen).core with
                  mrk := mrk''.set (kv32.toNat / 2) 0#8 } } : FullState) =
                st_r dcur dval (mrk''.set (kv32.toNat / 2) 0#8) tmp' fd' elen := rfl
            rw [heq] at hmm
            refine hJk () _ ⟨mrk''.set (kv32.toNat / 2) 0#8, hmm, by simp [hmk''l],
              fun v hv hmiss => by
                by_cases hveq : v = kv32.toNat / 2
                · subst v; rw [List.getElem?_set_self (by rw [hmk''l]; omega)]; rfl
                · rw [List.getElem?_set_ne (Ne.symm hveq)]
                  exact hclr v hv fun j hj1 hj2 => if hj_eq : j = k then by
                    subst j
                    rw [List.getElem?_eq_getElem (l := tmp') (by rw [htmpl]; omega),
                      Option.getD_some]
                    exact Ne.symm hveq
                  else hmiss j (by omega) hj2⟩)
      · -- Mark-clear loop done (`k = tlen`)
        have hkeq : k = tlen := by omega
        subst k
        let st2 := st_r dcur dval mrk'' tmp' fd' elen
        have hlen2 : st2.LengthsOk c :=
          ⟨{ hcok with mrk_len := hmk''l, tmp_len_arr := htmpl, frame_dec_len := hfdl },
           { hlen.scratch_ok with extend_stk_len := hlen.scratch_ok.extend_stk_len }⟩
        have hmrk_clr : FullLitMarksClear c st2 :=
          ⟨fun v hv => hclr v hv (fun j hj1 hj2 => by omega), hinv.2.2.1.2⟩
        have hinv2 : FullSparseInvW c
            (CNF.relabel (tumblePi tum fd') (shiftDownCnf accCnf)) F_cur st2 := by
          rw [hrel_eq]
          exact ⟨hlen2,
            { hw0 with
              arena := { hw0.arena with len_ok := hw0.arena.len_ok }
              watches := hw0.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
              frame_dec_lt := fun L hL1 hLle => by change L ≤ s.core.cur_level at hLle; omega },
            hmrk_clr, hinv.2.2.2.1, ⟨hinv.2.2.2.2.1.1, hel_le⟩, hinv.2.2.2.2.2⟩
        p_lets; refine wp_head_jnz_iff (b := err_v) (by c0_val_eq) ?_
        refine ⟨fun herr => ?_, fun hnoerr => ?_⟩
        · have hnone := herr_p herr; rw [hnone] at hQ; p_lets
          exact hQ st2 m2 hlen2 rfl rfl rfl (sep_ac hm2)
        · obtain ⟨hi0_lt, hdcur_eq, hpc_some⟩ := hok_p hnoerr
          subst hdcur_eq
          let cl := CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral)
          have hcl_pos : ∀ lit ∈ cl.literals, 1 ≤ lit.1 := by
            intro lit hlit; simp only [cl, CNF.Clause.literals_ofLiterals, List.mem_map] at hlit
            rcases hlit with ⟨l, _, rfl⟩; simp [kissatLitToDimacsLiteral]
          rw [hpc_some] at hQ
          let F1 := shiftDownCnf (accCnf.add cl)
          let F1_rel := CNF.relabel (tumblePi tum fd') F1
          have htc_f : TumbleCovers tum fd' F1 :=
            tumbleCovers_add_clause htc_r fun ht l hl =>
              hrev_cov ht l (List.mem_reverse.mp hl)
          have hvb_f : CnfVarsLt c.mv F1 :=
            cnfVarsLt_add_clause hvb0 fun l hl => hrev_lt l (List.mem_reverse.mp hl)
          have hF1_ent : F1_rel.Entails (cnfOfClauses F_cur) := by
            have h1 := relabel_entails_add (tumblePi tum fd') accCnf cl
            rw [hrel_eq] at h1
            exact CNF.entails_trans h1 hent_init
          have hinv2_F1 : FullSparseInvW c F1_rel F_cur st2 :=
            ingestTum_st3_inv hinv2 hF1_ent hlen2 rfl rfl
          have hq_ret : ∀ (r_out : BitVec 64) (st_out : FullState) (m_out : Mem 64),
              st_out.LengthsOk c → st_out.core.cur_vars = c.mv →
              st_out.core.d_cur = cnf_ptr + BitVec.ofNat 64 idx →
              st_out.core.cur_level = 0 → st_out.core.fuel = s.core.fuel →
              st_out.core.oom = s.core.oom → st_out.core.probing = s.core.probing →
              st_out.core.frame_dec = fd' → st_out.scratch.extend_len = elen →
              (r_out = 1#64 ∨ r_out = 2#64 ∨ r_out = 3#64) →
              (r_out = 1#64 → ∃ F_cur', FullSparseInvW c F1_rel F_cur' st_out ∧
                F1_rel.Entails (cnfOfClauses F_cur')) →
              (r_out = 2#64 → F1.Unsat) →
              (∀ vext l, 2 * c.mv ≤ vext.length → l < 2 * c.mv →
                TumbleValsRel tum c.mv s.core.frame_dec vext s.core.vals →
                TumbleUnusedZero tum c.mv s.scratch.extend_len s.core.vals →
                revLits = [l] → vext[l]?.getD 0#8 = 0#8 →
                r_out = 1#64 ∧
                TumbleValsRel tum c.mv fd' ((vext.set l 1#8).set (l ^^^ 1) 0xFF#8)
                  st_out.core.vals ∧
                TumbleUnusedZero tum c.mv elen st_out.core.vals ∧
                st_out.core.trail_end = s.core.trail_end + 1 ∧
                st_out.core.propagated = s.core.propagated) →
              (∀ vext l, 2 * c.mv ≤ vext.length → l < 2 * c.mv →
                TumbleValsRel tum c.mv s.core.frame_dec vext s.core.vals →
                revLits = [l] → vext[l]?.getD 0#8 = 0xFF#8 → r_out = 2#64) →
              (FullMem c st_out ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m_out →
              Q (r_out, ()) m_out := by
            intro r_out st_out m_out hlo hcv_o hd_o hcl_o hfu_o hoom_o hpr_o hfd_o hel_o
              hdom hi1 hi2 hu0_o hu1_o hm_o
            refine hQ r_out st_out idx m_out hcl_pos hi0_lt hidx rfl hlo hcv_o hd_o hcl_o
              hfu_o hoom_o hpr_o (by rw [hfd_o, hel_o]; exact hti_r)
              (by rw [hfd_o]; exact htc_f) hvb_f hdom
              (by rw [hfd_o]; exact hi1) hi2
              (fun vext l hvl hl hvr hunz hcleq hv0 => by
                rw [hfd_o, hel_o]
                exact hu0_o vext l hvl hl hvr hunz (fullIngestTum_unit_rev hcleq) hv0)
              (fun vext l hvl hl hvr hcleq hvf =>
                hu1_o vext l hvl hl hvr (fullIngestTum_unit_rev hcleq) hvf)
              (sep_ac hm_o)
          refine wp_head_jnz_iff (b := taut_v) (by c0_val_eq) ?_
          refine ⟨fun htaut => ?_, fun hntaut => ?_⟩
          · p_lets
            exact hq_ret 1#64 st2 m2 hlen2 hcv rfl hcl0 rfl rfl rfl rfl rfl (Or.inl rfl)
              (fun _ => ⟨F_cur, hinv2_F1, hF1_ent⟩) (fun h => by cases h)
              (fun _ l _ _ _ _ hr _ => by have := (hunit_r l hr).1; rw [htaut] at this; cases this)
              (fun _ l _ _ _ hr _ => by have := (hunit_r l hr).1; rw [htaut] at this; cases this)
              hm2
          · have hF1_cl : F1_rel.EntailsClause
                (cnfClause ((tmp'.take tlen).map BitVec.toNat)) := by
              have hcl_ent : F1_rel.EntailsClause
                  (cnfClause (revLits.reverse.map (tumbleLit tum fd'))) := by
                have h1 := relabel_entails_added (tumblePi tum fd') accCnf cl
                rwa [cnfClause_relabel_eq] at h1
              refine entails_of_mem_or_false hcl_ent fun tl_x htl_x => Or.inl ?_
              rw [List.mem_map] at htl_x
              obtain ⟨l, hl, rfl⟩ := htl_x
              obtain ⟨k, hk, hget⟩ := hcov hntaut l (List.mem_reverse.mp hl)
              rw [List.mem_map]; refine ⟨tmp'[k]'(by rw [htmpl]; omega), ?_, ?_⟩
              · rw [List.mem_iff_getElem]
                exact ⟨k, by rw [List.length_take, htmpl]; omega, by rw [List.getElem_take]⟩
              · rwa [List.getElem?_eq_getElem (by rw [htmpl]; omega), Option.getD_some] at hget
            p_lets
            -- Prune loop (`while (i < tlen)`)
            refine wp_loop_group (ts := [i32, i32])
              (fun r3 (kp_v, iv, ()) m3 => ∃ keep i tmp'',
                (FullMem c (st_r (cnf_ptr + BitVec.ofNat 64 idx) dval mrk'' tmp'' fd' elen) ⋆
                  (bytes cnf_ptr cnfBytes ⋆ R)) m3 ∧
                r3 = tlen - i ∧ kp_v = BitVec.ofNat 32 keep ∧ iv = BitVec.ofNat 32 i ∧
                IngestTumPruneInv c s tmp' fd' revLits tlen keep i tmp'')
              ?_ ?_
            · rintro L3 r3 ⟨kp_v, iv, ⟨⟩⟩ m3 ih3 ⟨keep, i, tmp'', hm3, rfl, rfl, rfl, hpi⟩
              have ⟨hk_le, hi_le3, htmp'l, htail, hkeep_un, _, _, _, hu0, hu1⟩ := hpi
              p_lets
              refine wp_head_jnz_iff (b := decide (i < tlen))
                (by simp only [Arg.val_var]; exact bv32_ult_eq (by omega) (by omega)) ?_
              rw [decide_eq_true_eq, decide_eq_false_iff_not]
              refine ⟨fun hilt => ?_, fun hige => ?_⟩
              · p_lets
                rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega), bv64_mul4_nat]
                have htm_bd_i : i < (st_r (cnf_ptr + BitVec.ofNat 64 idx)
                    dval mrk'' tmp'' fd' elen).core.tmp.length := by
                  dsimp [st_r]; rw [htmp'l]; omega
                refine wp_load_of (load_full_tmp (i := i) htm_bd_i hm3) ?_; p_lets
                let li := tmp''[i]'(by rw [htmp'l]; omega)
                have hli_st : (st_r (cnf_ptr + BitVec.ofNat 64 idx)
                    dval mrk'' tmp'' fd' elen).core.tmp[i]'htm_bd_i = li := rfl
                rw [hli_st]
                have hli_eq : li = tmp'[i]'(by rw [htmpl]; omega) := by
                  have h1 := htail i (Nat.le_refl _) hilt
                  rw [List.getElem?_eq_getElem (by rw [htmp'l]; omega),
                    List.getElem?_eq_getElem (by rw [htmpl]; omega)] at h1; exact Option.some.inj h1
                have hli_lt : li.toNat < 2 * c.mv := by
                  have := htmp_lt i hilt
                  rwa [List.getElem?_eq_getElem (by rw [htmpl]; omega),
                    Option.getD_some, ← hli_eq] at this
                rw [bv32_zext64_eq]
                have hv_bd_li : li.toNat < (st_r (cnf_ptr + BitVec.ofNat 64 idx)
                    dval mrk'' tmp'' fd' elen).core.vals.length := by
                  dsimp [st_r]; rw [hcok.vals_len]; omega
                refine wp_load_of (load_full_vals hv_bd_li hm3) ?_; p_lets
                let lv := s.core.vals[li.toNat]'(by rw [hcok.vals_len]; omega)
                have hlv_eq : (st_r (cnf_ptr + BitVec.ofNat 64 idx)
                    dval mrk'' tmp'' fd' elen).core.vals[li.toNat]'hv_bd_li = lv := rfl
                have hlv_dom : lv = 0#8 ∨ lv = 1#8 ∨ lv = 0xFF#8 := by
                  have := hw0.vals_domain li.toNat (by rw [hcv]; exact hli_lt)
                  rwa [List.getElem?_eq_getElem (by rw [hcok.vals_len]; omega),
                    Option.getD_some] at this
                have hlv_getD : s.core.vals[li.toNat]?.getD 0#8 = lv := by
                  rw [List.getElem?_eq_getElem (l := s.core.vals) (by rw [hcok.vals_len]; omega),
                    Option.getD_some]
                have hsgt : (0#32).slt (lv.signExtend 32) = true ↔ lv = 1#8 :=
                  i8_vals_sgt0 hlv_dom
                rw [wp_jnz]; dsimp only [Arg.val_var]; rw [hlv_eq]
                refine ⟨fun hpos => ?_, fun hnpos => ?_⟩
                · have hlv1 : lv = 1#8 := hsgt.mp hpos
                  let st3 := st_r (cnf_ptr + BitVec.ofNat 64 idx) dval mrk'' tmp'' fd' elen
                  have hlen3 : st3.LengthsOk c :=
                    ⟨{ hlen2.core_ok with tmp_len_arr := htmp'l }, hlen2.scratch_ok⟩
                  have hinv3 := ingestTum_st3_inv hinv2 hF1_ent hlen3 rfl rfl
                  have hli_abs : ∀ l, revLits = [l] →
                      s.core.vals[tumbleLit tum fd' l]?.getD 0#8 = 1#8 := fun l hrev => by
                    obtain ⟨_, _, htmp0⟩ := hunit_r l hrev
                    have hi0_eq : i = 0 := by omega
                    subst hi0_eq
                    have hl_eq : li.toNat = tumbleLit tum fd' l := by
                      rw [hli_eq]; rwa [List.getElem?_eq_getElem (by rw [htmpl]; omega),
                        Option.getD_some] at htmp0
                    rw [hl_eq] at hlv_getD; exact hlv_getD.trans hlv1
                  p_lets
                  exact hq_ret 1#64 st3 m3 hlen3 hcv rfl hcl0 rfl rfl rfl rfl rfl (Or.inl rfl)
                    (fun _ => ⟨F_cur, hinv3, hF1_ent⟩) (fun h => by cases h)
                    (fun vext l _ hl hvr hunz hr hv0 => by
                      have h1 := hli_abs l hr
                      have h0 := tumbleValsRel_vals_of_vext_zero (hvals_lift vext hvr hunz) hl
                        (fun ht => hrev_cov ht l (by rw [hr]; exact List.mem_cons_self)) hv0
                      rw [h1] at h0; cases h0)
                    (fun vext l _ hl hvr hr hvf => by
                      have h1 := hli_abs l hr
                      have hf := tumbleValsRel_vals_of_vext_ff hvr hfd_mono hl hvf
                      rw [h1] at hf; cases hf)
                    hm3
                · have hlv_ne1 : lv ≠ 1#8 := fun h => by rw [hsgt.mpr h] at hnpos; cases hnpos
                  refine wp_join_group
                    (fun (kp', ()) m3' => ∃ keep' tmp''',
                      (FullMem c (st_r (cnf_ptr + BitVec.ofNat 64 idx) dval mrk'' tmp''' fd' elen) ⋆
                        (bytes cnf_ptr cnfBytes ⋆ R)) m3' ∧
                      kp' = BitVec.ofNat 32 keep' ∧
                      IngestTumPruneInv c s tmp' fd' revLits tlen keep' (i + 1) tmp''')
                    (fun _ ⟨kp', ⟨⟩⟩ m3' ⟨keep', tmp''', hm3', hkp', hpi'⟩ => by
                      subst hkp'; p_lets
                      rw [bv32_add1_nat (by omega)]
                      exact ih3 (tlen - (i + 1)) _ m3' (by omega)
                        ⟨keep', i + 1, tmp''', hm3', rfl, rfl, rfl, hpi'⟩)
                    (fun Jp hJp => by
                      p_lets; refine wp_head_jnz_iff (b := decide (lv = 0#8)) (by
                        simp only [Arg.val_var]; exact i8_vals_beq0 hlv_dom) ?_
                      rw [decide_eq_true_eq, decide_eq_false_iff_not]
                      refine ⟨fun hlv0 => ?_, fun hlvne0 => ?_⟩
                      · p_lets
                        rw [bv32_zext64_eq, bv32_ofNat_toNat (n := keep) (by omega), bv64_mul4_nat]
                        have htm_bd_kp : keep < (st_r (cnf_ptr + BitVec.ofNat 64 idx)
                            dval mrk'' tmp'' fd' elen).core.tmp.length := by
                          dsimp [st_r]; rw [htmp'l]; omega
                        obtain ⟨okt, hmt⟩ := store_full_tmp (i := keep) li htm_bd_kp hm3
                        refine ⟨okt, ?_⟩; p_lets
                        rw [bv32_add1_nat (by omega)]
                        exact hJp _ _ ⟨keep + 1, tmp''.set keep li, hmt, rfl,
                          ingestTumPruneInv_push hc_mv hilt htlen_le htmpl htmp_nd
                            hli_eq hli_lt (hlv_getD.trans hlv0) (fun l hr => (hunit_r l hr).2.2)
                            hpi⟩
                      · have hlv_ff : lv = 0xFF#8 := by
                          rcases hlv_dom with h | h | h
                          · exact absurd h hlvne0
                          · exact absurd h hlv_ne1
                          · exact h
                        exact hJp _ m3 ⟨keep, tmp'', hm3, rfl,
                          ingestTumPruneInv_skip hc_mv hilt htlen_le htmpl hli_eq
                            (hlv_getD.trans hlv_ff) (fun l hr => (hunit_r l hr).2.2) hpi⟩)
              · -- Prune loop done (`i = tlen`); run S11-3 activation loop (`while (a < keep)`)
                have hieq : i = tlen := by omega
                subst i
                have hF1_keep := ingestTum_keep_entails hcv hw0 hcl0 htlen_le htmpl hc_mv htmp_lt
                  hF1_ent hF1_cl hpi
                let st3 := st_r (cnf_ptr + BitVec.ofNat 64 idx) dval mrk'' tmp'' fd' elen
                have hlen3 : st3.LengthsOk c :=
                  ⟨{ hlen2.core_ok with tmp_len_arr := htmp'l }, hlen2.scratch_ok⟩
                have hinv3 := ingestTum_st3_inv hinv2 hF1_ent hlen3 rfl rfl
                p_lets
                refine wp_loop_group (ts := [i32])
                  (fun r4 (av, ()) m4 => ∃ a fl_a un_a sc_a,
                    let st_a : FullState :=
                      { core := { st3.core with flags := fl_a, unassigned := un_a }
                        scratch := sc_a }
                    (FullMem c st_a ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m4 ∧
                    a ≤ keep ∧ r4 = keep - a ∧ av = BitVec.ofNat 32 a ∧
                    st_a.LengthsOk c ∧ Full.FullExtScratchPres st3 st_a)
                  ?_ ?_
                · rintro L4 r4 ⟨av, ⟨⟩⟩ m4 ih4
                    ⟨a, fl_a, un_a, sc_a, hm4, hale, rfl, rfl, hlen_a, hpres_a⟩
                  let st_a : FullState :=
                    { core := { st3.core with flags := fl_a, unassigned := un_a }
                      scratch := sc_a }
                  p_lets
                  refine wp_head_jnz_iff (b := decide (a < keep))
                    (by simp only [Arg.val_var]; exact bv32_ult_eq (by omega) (by omega)) ?_
                  rw [decide_eq_true_eq, decide_eq_false_iff_not]
                  refine ⟨fun halt => ?_, fun hage => ?_⟩
                  · p_lets
                    rw [bv32_zext64_eq, bv32_ofNat_toNat (n := a) (by omega), bv64_mul4_nat]
                    have htm_bd_a : a < st_a.core.tmp.length := by
                      change a < tmp''.length; rw [htmp'l]; omega
                    refine wp_load_of (load_full_tmp (i := a) htm_bd_a hm4) ?_; p_lets
                    apply wp_call_of_spec; apply hAct
                    dsimp only [fullActivateLitFidSpec, vals_nil, vals_cons, Arg.val_var]
                    refine ⟨c, st_a, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen_a, hm4,
                      fun fl_b un_b sc_b m5 hlen_b hpres_b hm5 => ?_⟩
                    p_lets
                    rw [bv32_add1_nat (by omega)]
                    exact ih4 (keep - (a + 1)) _ m5 (by omega)
                      ⟨a + 1, fl_b, un_b, sc_b, hm5, by omega, rfl, rfl, hlen_b,
                        ⟨hpres_b.1.trans hpres_a.1, hpres_b.2.trans hpres_a.2⟩⟩
                  · -- Activation loop done (`a = keep`): `keep == 0 / 1 / >= 2`
                    have hinv4 : FullSparseInvW c F1_rel F_cur st_a :=
                      fullSparseInvW_with_act hinv3 hlen_a hpres_a
                    have hel_a : st_a.scratch.extend_len = elen := hpres_a.2
                    p_lets
                    have hkeep0 : (BitVec.ofNat 32 keep == 0#32) = decide (keep = 0) := by
                      rw [show (0#32 : BitVec 32) = BitVec.ofNat 32 0 from rfl,
                        bv32_beq_nat_eq (by decide), bv32_ofNat_toNat (n := keep) (by omega)]
                    refine wp_head_jnz_iff (b := decide (keep = 0))
                      (by simpa [Arg.val_var] using hkeep0) ?_
                    rw [decide_eq_true_eq, decide_eq_false_iff_not]
                    refine ⟨fun hk0 => ?_, fun _ => ?_⟩
                    · subst hk0; p_lets
                      have hunsat_rel : F1_rel.Unsat :=
                        unsat_of_entails_nil (by simpa using hF1_keep)
                      have hunsat : F1.Unsat :=
                        cnf_unsat_of_relabel_tumble hti_r htc_f hvb_f hunsat_rel
                      exact hq_ret 2#64 st_a m4 hlen_a hcv rfl hcl0 rfl rfl rfl rfl hel_a
                        (Or.inr (Or.inl rfl)) (fun h => by cases h) (fun _ => hunsat)
                        (fun vext l _ hl hvr hunz hr hv0 => by
                          have ⟨_, ht1, _⟩ := hunit_r l hr
                          have h0 := tumbleValsRel_vals_of_vext_zero (hvals_lift vext hvr hunz) hl
                            (fun ht => hrev_cov ht l (by rw [hr]; exact List.mem_cons_self)) hv0
                          have ⟨h1, _⟩ := hu0 l hl hr h0 ht1; omega)
                        (fun _ _ _ _ _ _ _ => rfl) hm4
                    · p_lets
                      have hkeep1 : (BitVec.ofNat 32 keep == 1#32) = decide (keep = 1) := by
                        rw [show (1#32 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
                          bv32_beq_nat_eq (by decide), bv32_ofNat_toNat (n := keep) (by omega)]
                      refine wp_head_jnz_iff (b := decide (keep = 1))
                        (by simpa [Arg.val_var] using hkeep1) ?_
                      rw [decide_eq_true_eq, decide_eq_false_iff_not]
                      refine ⟨fun hk1 => ?_, fun _ => ?_⟩
                      · subst hk1; p_lets
                        have htm_bd0 : 0 < st_a.core.tmp.length := by
                          change 0 < tmp''.length; rw [htmp'l]; omega
                        refine wp_load_of (load_full_tmp (i := 0) htm_bd0 hm4) ?_; p_lets
                        let l0 := tmp''[0]'(by rw [htmp'l]; omega)
                        have hl0_st : st_a.core.tmp[0]'htm_bd0 = l0 := rfl
                        rw [hl0_st]
                        have ⟨hl0_lt, hl0_un⟩ := hkeep_un 0 (by decide)
                        rw [List.getElem?_eq_getElem (i := 0) (by rw [htmp'l]; omega),
                          Option.getD_some] at hl0_lt hl0_un
                        have hl0_lt' : l0.toNat < 2 * c.mv := hl0_lt
                        have hl0_ent : F1_rel.EntailsClause (cnfClause [l0.toNat]) := by
                          have htk : tmp''.take 1 = [l0] := by
                            cases tmp'' with
                            | nil => simp at htmp'l; omega
                            | cons _ _ => rfl
                          simpa [htk] using hF1_keep
                        let F_next := [l0.toNat] :: F_cur
                        have hFn_ent : F1_rel.Entails (cnfOfClauses F_next) :=
                          entails_cnfOfClauses_cons_tum hF1_ent hl0_ent
                        have hext_n : ExtUnsatSound F1_rel st_a.core.cur_vars F_next :=
                          extUnsatSound_of_entails_tum
                            (varsBounded_cons_tum (fun q hq => by
                              simp only [List.mem_singleton] at hq; rw [hq, hcv]; exact hl0_lt')
                              hinv4.2.1.ext_sound.1) hFn_ent
                        have hw4_n : FullWitnessInv c F1_rel F_next st_a.core :=
                          hinv4.2.1.replace_extSound hext_n (cnfOfClauses_cons_entails_tum _ _)
                        apply wp_call_of_spec; apply hAssign
                        dsimp only [fullAssignLvlSpec, vals_nil, vals_cons, Arg.val_var,
                          Arg.val_imm]
                        refine ⟨c, st_a, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen_a, hm4, ?_⟩
                        have hte_lt := hw4_n.trail_end_lt_of_unassigned
                          (by rw [hcv]; exact hl0_lt') hl0_un
                        have hte_mv : st_a.core.trail_end < c.max_vars :=
                          Nat.lt_of_lt_of_le hte_lt (by rw [hcv]; exact hc_mv)
                        have hguard_f : ¬ (st_a.core.cur_vars ≤ l0.toNat / 2 ∨
                            c.max_vars ≤ st_a.core.trail_end ∨
                            st_a.core.vals[l0.toNat]?.getD 0#8 ≠ 0#8) := by
                          rw [hcv]; refine not_or.mpr ⟨by omega, not_or.mpr ⟨by omega, ?_⟩⟩
                          change ¬ (s.core.vals[l0.toNat]?.getD 0#8 ≠ 0#8)
                          exact fun h => h hl0_un
                        rw [ite_eq_right hguard_f]
                        intro flags' unass' phases' m5 hfl' hph' hm5; p_lets
                        have h_alvl : ((0 : BitVec 32) = 0#32) = True := eq_true rfl
                        simp only [h_alvl, ↓reduceIte] at hm5
                        let sf : FullState :=
                          { st_a with
                            core :=
                              { st_a.core with
                                vals := (st_a.core.vals.set l0.toNat 1#8).set
                                  (l0.toNat ^^^ 1) 0xFF#8
                                flags := flags', lvl := st_a.core.lvl.set (l0.toNat / 2) 0#32
                                rsns := st_a.core.rsns.set (l0.toNat / 2) 0xFFFFFFFF#32
                                trl := st_a.core.trl.set st_a.core.trail_end l0
                                trail_pos := st_a.core.trail_pos.set (l0.toNat / 2)
                                  (BitVec.ofNat 32 st_a.core.trail_end)
                                trail_end := st_a.core.trail_end + 1
                                unassigned := unass', unflushed := st_a.core.unflushed + 1#64 }
                            scratch := { st_a.scratch with phases := phases' } }
                        have hlen_sf : sf.LengthsOk c :=
                          ⟨{ hlen_a.core_ok with
                              vals_len := by
                                change ((st_a.core.vals.set l0.toNat 1#8).set
                                  (l0.toNat ^^^ 1) 0xFF#8).length = 2 * c.max_vars
                                rw [List.length_set, List.length_set]
                                exact hlen_a.core_ok.vals_len
                              flags_len := hfl'
                              lvl_len := by
                                change (st_a.core.lvl.set (l0.toNat / 2) 0#32).length = c.max_vars
                                rw [List.length_set]; exact hlen_a.core_ok.lvl_len
                              rsns_len := by
                                change (st_a.core.rsns.set (l0.toNat / 2) 0xFFFFFFFF#32).length =
                                  c.max_vars
                                rw [List.length_set]; exact hlen_a.core_ok.rsns_len
                              trl_len := by
                                change (st_a.core.trl.set st_a.core.trail_end l0).length =
                                  c.max_vars
                                rw [List.length_set]; exact hlen_a.core_ok.trl_len
                              trail_pos_len := by
                                change (st_a.core.trail_pos.set (l0.toNat / 2)
                                  (BitVec.ofNat 32 st_a.core.trail_end)).length = c.max_vars
                                rw [List.length_set]; exact hlen_a.core_ok.trail_pos_len
                              trail_end_le := by
                                change st_a.core.trail_end + 1 ≤ st_a.core.cur_vars; exact hte_lt
                              propagated_le :=
                                Nat.le_succ_of_le hlen_a.core_ok.propagated_le },
                            { hlen_a.scratch_ok with phases_len := hph' }⟩
                        have hw_sf : FullWitnessInv c F1_rel F_next sf.core :=
                          addUnit_preserves_witness_tum hlen_a.core_ok hw4_n hcl0 hfl'
                            (unassigned' := unass') (unflushed' := st_a.core.unflushed + 1#64)
                            (by rw [hcv]; exact hl0_lt') hl0_un
                            (cnfOfClauses_cons_entails_head_tum _ _)
                        have hinv_sf : FullSparseInvW c F1_rel F_next sf :=
                          ⟨hlen_sf, hw_sf, hinv4.2.2.1, hinv4.2.2.2.1, hinv4.2.2.2.2.1,
                            hinv4.2.2.2.2.2⟩
                        exact hq_ret 1#64 sf m5 hlen_sf hcv rfl hcl0 rfl rfl rfl rfl hel_a
                          (Or.inl rfl) (fun _ => ⟨F_next, hinv_sf, hFn_ent⟩)
                          (fun h => by cases h)
                          (fun vext l hvl hl hvr hunz hrev hv0 => by
                            have ⟨_, ht1, _⟩ := hunit_r l hrev
                            have hmap_l : tum = true →
                                fd'[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 :=
                              fun ht => hrev_cov ht l (by rw [hrev]; exact List.mem_cons_self)
                            have hvr' := hvals_lift vext hvr hunz
                            have hs0 := tumbleValsRel_vals_of_vext_zero hvr' hl hmap_l hv0
                            have ⟨_, hl0eq⟩ := hu0 l hl hrev hs0 ht1
                            rw [List.getElem?_eq_getElem (i := 0) (by rw [htmp'l]; omega),
                              Option.getD_some] at hl0eq
                            have hl0eq' : l0.toNat = tumbleLit tum fd' l := hl0eq
                            have htl_lt_el : tum = true → l0.toNat < 2 * elen := fun ht => by
                              rw [hl0eq']
                              have hm := hti_r ht
                              rcases hm.2.2.1 (l / 2) (by omega) with hff | hlt
                              · exact absurd hff (hmap_l ht)
                              · unfold tumbleLit tumblePi; simp only [ht, ↓reduceIte]; omega
                            refine ⟨rfl, ?_, ?_, rfl, rfl⟩
                            · change TumbleValsRel tum c.mv fd'
                                ((vext.set l 1#8).set (l ^^^ 1) 0xFF#8)
                                ((s.core.vals.set l0.toNat 1#8).set (l0.toNat ^^^ 1) 0xFF#8)
                              rw [hl0eq']
                              exact tumbleValsRel_assign_unit hti_r hvr' hvl
                                (by rw [hcok.vals_len]; omega) hl hmap_l
                            · change TumbleUnusedZero tum c.mv elen
                                ((s.core.vals.set l0.toNat 1#8).set (l0.toNat ^^^ 1) 0xFF#8)
                              exact tumbleUnusedZero_assign
                                (tumbleUnusedZero_mono hunz hel_ge) htl_lt_el)
                          (fun vext l _ hl hvr hrev hvf => by
                            have ⟨_, ht1, _⟩ := hunit_r l hrev
                            have hsf := tumbleValsRel_vals_of_vext_ff hvr hfd_mono hl hvf
                            have := hu1 l hl hrev hsf ht1; omega)
                          hm5
                      · -- `keep >= 2`: call `full_add_clause`
                        have hkp_ge2 : 2 ≤ keep := by omega
                        have hkp_le_mv : keep ≤ c.max_vars := Nat.le_trans hk_le (by omega)
                        let clLits := (tmp''.take keep).map BitVec.toNat
                        have hlits_bd : ∀ l ∈ clLits, l < 2 * c.mv := by
                          intro l hl; rw [List.mem_map] at hl; obtain ⟨x, hx, rfl⟩ := hl
                          rw [List.mem_iff_getElem] at hx; obtain ⟨k, hk, hxk⟩ := hx
                          rw [List.length_take] at hk; rw [List.getElem_take] at hxk
                          have hlt := (hkeep_un k (by omega)).1
                          rwa [List.getElem?_eq_getElem (by rw [htmp'l]; omega),
                            Option.getD_some, hxk] at hlt
                        have hcl_nd : ((tmp''.take keep).map fun x => x.toNat / 2).Nodup :=
                          nodup_of_pairwise_div2_tum
                            (by rw [htmp'l]; exact Nat.le_trans hk_le (Nat.le_trans htlen_le hc_mv))
                            hpi.2.2.2.2.2.2.1
                        let F_next := clLits :: F_cur
                        have hFn_ent : F1_rel.Entails (cnfOfClauses F_next) :=
                          entails_cnfOfClauses_cons_tum hF1_ent hF1_keep
                        have hext_n : ExtUnsatSound F1_rel st_a.core.cur_vars F_next :=
                          extUnsatSound_of_entails_tum
                            (varsBounded_cons_tum (fun l hl => by rw [hcv]; exact hlits_bd l hl)
                              hinv4.2.1.ext_sound.1) hFn_ent
                        have hw4_n : FullWitnessInv c F1_rel F_next st_a.core :=
                          hinv4.2.1.replace_extSound hext_n (cnfOfClauses_cons_entails_tum _ _)
                        have hq_add : ∀ (r_out : BitVec 64) (sf : FullState) (m5 : Mem 64),
                            (r_out = 1#64 ∨ r_out = 3#64) → sf.LengthsOk c →
                            sf.core.cur_vars = c.mv →
                            sf.core.d_cur = cnf_ptr + BitVec.ofNat 64 idx →
                            sf.core.cur_level = 0 → sf.core.fuel = s.core.fuel →
                            sf.core.oom = s.core.oom → sf.core.probing = s.core.probing →
                            sf.core.frame_dec = fd' → sf.scratch.extend_len = elen →
                            (r_out = 1#64 → ∃ F_cur', FullSparseInvW c F1_rel F_cur' sf ∧
                              F1_rel.Entails (cnfOfClauses F_cur')) →
                            (FullMem c sf ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m5 →
                            Q (r_out, ()) m5 :=
                          fun r_out sf m5 hdom hlens hcv_f hd hcl hfu hoom hpr hfd_f hel_f hi1
                              hm5 =>
                            hq_ret r_out sf m5 hlens hcv_f hd hcl hfu hoom hpr hfd_f hel_f
                              (hdom.elim Or.inl (fun h => Or.inr (Or.inr h))) hi1
                              (fun h => by rcases hdom with rfl | rfl <;> cases h)
                              (fun vext l _ hl hvr hunz hr hv0 => by
                                have ⟨_, ht1, _⟩ := hunit_r l hr
                                have h0 := tumbleValsRel_vals_of_vext_zero
                                  (hvals_lift vext hvr hunz) hl
                                  (fun ht => hrev_cov ht l (by rw [hr]; exact List.mem_cons_self))
                                  hv0
                                have ⟨h1, _⟩ := hu0 l hl hr h0 ht1; omega)
                              (fun vext l _ hl hvr hr hvf => by
                                have ⟨_, ht1, _⟩ := hunit_r l hr
                                have hf := tumbleValsRel_vals_of_vext_ff hvr hfd_mono hl hvf
                                have := hu1 l hl hr hf ht1; omega)
                              hm5
                        apply wp_call_of_spec; apply hAddCl
                        dsimp only [fullAddClauseSpec, vals_nil, vals_cons, Arg.val_var,
                          Arg.val_imm]
                        refine ⟨c, F1_rel, F_next, st_a, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen_a,
                          hw4_n, hinv4.2.2.2.2.2,
                          by rw [bv32_ofNat_toNat (by omega)]; exact hkp_le_mv,
                          (fun _ => by
                            rw [bv32_ofNat_toNat (by omega)]
                            refine ⟨fun l hl => by rw [hcv]; exact hlits_bd l hl, hcl_nd, ?_⟩
                            exact cnfOfClauses_cons_entails_head_tum clLits F_cur),
                          hm4, ?_⟩
                        simp only [bv32_ofNat_toNat (n := keep) (by omega),
                          show ¬ (keep < 2) by omega, ↓reduceIte]
                        by_cases hkp2 : keep = 2
                        · simp only [hkp2, ↓reduceIte]
                          intro cid wvec' wstk' wlen' wu' nb' wsort' m5 _ hlen5 hw5 hm5
                          let sf : FullState := { st_a with
                            core := { st_a.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                                     wusable := wu', num_binary := nb' }
                            scratch := { st_a.scratch with wsort := wsort' } }
                          have hinv5 : FullSparseInvW c F1_rel F_next sf :=
                            ⟨hlen5, hw5, hinv4.2.2.1, hinv4.2.2.2.1, hinv4.2.2.2.2.1,
                              hinv4.2.2.2.2.2⟩
                          p_lets; refine wp_head_jnz_iff (b := decide (cid = 0xFFFFFFFF#64))
                            (by simp only [Arg.val_var]; exact bv64_beq_eq) ?_
                          rw [decide_eq_true_eq, decide_eq_false_iff_not]
                          refine ⟨fun _ => ?_, fun _ => ?_⟩
                          · p_lets; exact hq_add 3#64 sf m5 (Or.inr rfl) hlen5 hcv rfl hcl0 rfl
                              rfl rfl rfl hel_a (fun h => by cases h) hm5
                          · p_lets; exact hq_add 1#64 sf m5 (Or.inl rfl) hlen5 hcv rfl hcl0 rfl
                              rfl rfl rfl hel_a (fun _ => ⟨F_next, hinv5, hFn_ent⟩) hm5
                        · simp only [hkp2, ↓reduceIte]
                          intro cid arena' alen' wvec' wstk' wlen' wu' fred' ni' nr' wsort' m5
                            _ hlen5 hw5 hsub5 hnd5 _ hm5
                          let sf : FullState := { st_a with
                            core := { st_a.core with arena := arena', arena_len := alen',
                                                     wvec := wvec', wstk := wstk', wlen := wlen',
                                                     wusable := wu', first_reducible := fred',
                                                     num_irred := ni', num_redundant := nr' }
                            scratch := { st_a.scratch with wsort := wsort' } }
                          have hinv5 : FullSparseInvW c F1_rel F_next sf :=
                            ⟨hlen5, hw5, hinv4.2.2.1, hnd5 hinv4.2.2.2.1,
                              ⟨hinv4.2.2.2.2.1.1.of_refs_subset rfl hsub5, hinv4.2.2.2.2.1.2⟩,
                              hinv4.2.2.2.2.2⟩
                          p_lets; refine wp_head_jnz_iff (b := decide (cid = 0xFFFFFFFF#64))
                            (by simp only [Arg.val_var]; exact bv64_beq_eq) ?_
                          rw [decide_eq_true_eq, decide_eq_false_iff_not]
                          refine ⟨fun _ => ?_, fun _ => ?_⟩
                          · p_lets; exact hq_add 3#64 sf m5 (Or.inr rfl) hlen5 hcv rfl hcl0 rfl
                              rfl rfl rfl hel_a (fun h => by cases h) hm5
                          · p_lets; exact hq_add 1#64 sf m5 (Or.inl rfl) hlen5 hcv rfl hcl0 rfl
                              rfl rfl rfl hel_a (fun _ => ⟨F_next, hinv5, hFn_ent⟩) hm5
                · intro L4 hL4; p_lets
                  exact hL4 keep _ m3
                    ⟨0, st3.core.flags, st3.core.unassigned, st3.scratch, hm3,
                      Nat.zero_le _, by simp, rfl, hlen3, ⟨rfl, rfl⟩⟩
            · intro L3 hL3; p_lets
              exact hL3 tlen _ m2
                ⟨0, 0, tmp', hm2, by simp, rfl, rfl,
                  ⟨Nat.le_refl _, Nat.zero_le _, htmpl, fun _ _ _ => rfl,
                    fun _ h => by omega, fun _ h => by omega, fun _ _ h => by omega,
                    fun _ h => by omega, fun _ _ _ _ h => by omega, fun _ _ _ _ h => by omega⟩⟩
    · intro L2 hL2; p_lets
      exact hL2 tlen _ mb
        ⟨0, mrk', hmb, Nat.zero_le _, by simp, rfl, hmkl,
          fun v hv hmiss => hmrk_zero v hv (fun j hj => hmiss j (Nat.zero_le _) hj)⟩
  · -- Read-loop body (`while (true)`)
    rintro B1 L1 r ⟨tlen_v, taut_v, ⟨⟩⟩ ml hB1 ih1
      ⟨idx, tlen, elen, revLits, mrk', tmp', fd', dval, hml, rfl, rfl, hri, hpc_inv⟩
    let st := st_r (cnf_ptr + BitVec.ofNat 64 idx) dval mrk' tmp' fd' elen
    have hri_copy := hri
    obtain ⟨hi_le, hidx, htlen_le, hmkl, htmpl, hfdl, hel_ge, hel_le, hti_r, htc_r, hrel_eq,
      hfd_mono, hvals_lift, hrev_lt, hrev_cov, htmp_lt, htmp_nd,
      hmrk_zero, hmrk_pos, hcov, hsub_rev, hnil_taut, hunit_r⟩ := hri
    p_lets
    refine wp_head_jnz_iff (b := true) (by c0_val_eq) ?_
    refine ⟨fun _ => ?_, fun h => (by cases h)⟩
    p_lets
    have hml_d : (bytes cnf_ptr cnfBytes ⋆
        dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
          (cnf_ptr + BitVec.ofNat 64 idx) dval ⋆ (FullRest c st ⋆ R)) ml :=
      sep_ac (focus_dimacs hml)
    apply wp_call_of_spec; apply hLit
    change kissatNextLitSpec (cnf_ptr + BitVec.ofNat 64 cnfBytes.length, c.hdr, ()) ml _ _
    refine ⟨cnf_ptr, BitVec.ofNat 64 c.nc, dval, c.mv, cnfBytes, idx, FullRest c st ⋆ R,
      rfl, hfit, by omega, hidx, hml_d, ?_⟩
    cases hnl : nextLitPure c.mv (cnfBytes.drop idx) with
    | err =>
      intro cur' val' m' hm'; p_lets; refine wp_head_jnz_iff (by c0_val_eq) ?_
      refine ⟨fun _ => ?_, fun h => (by cases h)⟩
      let st_d := { st with core := { st.core with d_cur := cur', d_val := val' } }
      have hm'_a : (FullMem c st_d ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m' :=
        unfocus_dimacs (R := bytes cnf_ptr cnfBytes ⋆ R) (sep_ac hm')
      p_lets
      exact hB1 (BitVec.ofNat 32 tlen, taut_v, true, ()) m'
        ⟨idx, tlen, elen, revLits, mrk', tmp', fd', cur', val', hm'_a, rfl, hri_copy,
          fun _ => by rw [← hpc_inv, parseClauseAux_eq_nextLitPure, hnl],
          fun hc => by cases hc⟩
    | endClause rest =>
      intro j m' hij hj hdrop hm'; p_lets; refine wp_head_jnz_iff (by c0_val_eq) ?_
      refine ⟨fun h => (by cases h), fun _ => ?_⟩
      p_lets; refine wp_head_jnz_iff (by c0_val_eq) ?_
      refine ⟨fun _ => ?_, fun h => (by cases h)⟩
      let st_d := { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j,
                                                   d_val := 0#64 } }
      have hm'_a : (FullMem c st_d ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m' :=
        unfocus_dimacs (R := bytes cnf_ptr cnfBytes ⋆ R) (sep_ac hm')
      p_lets
      refine hB1 (BitVec.ofNat 32 tlen, taut_v, false, ()) m'
        ⟨j, tlen, elen, revLits, mrk', tmp', fd', cnf_ptr + BitVec.ofNat 64 j, 0#64, hm'_a, rfl,
          ⟨by omega, hj, htlen_le, hmkl, htmpl, hfdl, hel_ge, hel_le, hti_r, htc_r, hrel_eq,
            hfd_mono, hvals_lift, hrev_lt, hrev_cov, htmp_lt, htmp_nd,
            hmrk_zero, hmrk_pos, hcov, hsub_rev, hnil_taut, hunit_r⟩,
          (fun hc => by cases hc),
          fun _ => ⟨by omega, rfl, by
            rw [← hpc_inv, parseClauseAux_eq_nextLitPure, hnl, List.map_reverse, hdrop]⟩⟩
    | lit l rest =>
      intro j m' hl_mv hl_bd hij hj hdrop hm'; p_lets
      refine wp_head_jnz_iff (by c0_val_eq) ?_
      refine ⟨fun h => (by cases h), fun _ => ?_⟩
      p_lets; refine wp_head_jnz_iff (by c0_val_eq) ?_
      refine ⟨fun h => (by cases h), fun _ => ?_⟩
      let st_d := { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j,
                                                   d_val := BitVec.ofNat 64 l } }
      have hm'_a : (FullMem c st_d ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m' :=
        unfocus_dimacs (R := bytes cnf_ptr cnfBytes ⋆ R) (sep_ac hm')
      p_lets
      refine wp_load_of (load_full_val hm'_a) ?_; p_lets
      refine wp_load_of (load_full_mv hm'_a) ?_; p_lets
      have hl32 : l < 2 ^ 32 := by omega
      have hv_lt : l / 2 < c.mv := by omega
      have hmvd : st_d.core.d_val = BitVec.ofNat 64 l := rfl
      rw [hmvd, bv64_trunc32_ofNat hl32, bv32_zext64_eq, bv32_lshr1, bv32_ofNat_toNat hl32]
      have hgd_v : (BitVec.ofNat 64 c.mv).ule (BitVec.ofNat 64 (l / 2)) =
          decide (c.mv ≤ l / 2) := bv_ule_eq (by omega) (by omega)
      refine wp_head_jnz_iff (b := false)
        (by simp only [Arg.val_var, hgd_v]; simp [hv_lt]) ?_
      refine ⟨fun h => (by cases h), fun _ => ?_⟩
      p_lets
      -- Join after `if (tum) { ... }` producing `(err_t, lit_t, v_t, ())`
      refine wp_join_group
        (fun (_err_t, lit_t, v_t, ()) m_t =>
          ∃ fd_t elen_t,
            let st_t := st_r (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 l) mrk' tmp' fd_t elen_t
            (FullMem c st_t ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m_t ∧
            lit_t = BitVec.ofNat 32 (tumbleLit tum fd_t l) ∧
            v_t = BitVec.ofNat 32 (tumbleLit tum fd_t l / 2) ∧
            (tum = true → fd_t[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
            IngestTumReadInv c accCnf s cnfBytes i0 idx tlen elen_t taut_v revLits mrk' tmp' fd_t)
        ?_ ?_
      · -- Continuation after `if (tum)` with renamed literal `tl := tumbleLit tum fd_t l`
        rintro _ ⟨_err_t, lit_t, v_t, ⟨⟩⟩ m_t
          ⟨fd_t, elen_t, hm_t, rfl, rfl, hl_cov_t, hri_t⟩
        let tl := tumbleLit tum fd_t l
        let st_t := st_r (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 l) mrk' tmp' fd_t elen_t
        have hri_t_copy := hri_t
        obtain ⟨_, _, _, _, _, hfdl_t, hel_ge_t, hel_le_t, hti_t, htc_t, hrel_eq_t,
          hfd_mono_t, hvals_lift_t, _, hrev_cov_t, _, _, _, _, hcov_t, hsub_rev_t,
          _, _⟩ := hri_t
        have htl_mv : tl < 2 * c.mv := tumbleLit_lt hti_t hl_mv hl_cov_t
        have htl32 : tl < 2 ^ 32 := by omega
        have htv_lt : tl / 2 < c.mv := by omega
        have htv32 : tl / 2 < 2 ^ 32 := by omega
        p_lets
        rw [bv32_zext64_eq, bv32_ofNat_toNat htv32]
        have hmkl_t : tl / 2 < st_t.core.mrk.length := by
          dsimp [st_t, st_r]; rw [hmkl]; omega
        refine wp_load_of (load_full_mrk hmkl_t hm_t) ?_; p_lets
        let mv_b := mrk'[tl / 2]'(by rw [hmkl]; omega)
        have hmv_b_eq : st_t.core.mrk[tl / 2]'hmkl_t = mv_b := rfl
        rw [hmv_b_eq]
        have hpc_next : parseClauseAux ((cnfBytes.drop j).length + 1) c.mv
            ((l :: revLits).map kissatLitToDimacsLiteral) (cnfBytes.drop j) =
            parseClause c.mv (cnfBytes.drop i0) := by
          have hstep : parseClauseAux ((cnfBytes.drop idx).length + 1) c.mv
              (revLits.map kissatLitToDimacsLiteral) (cnfBytes.drop idx) =
              parseClauseAux (cnfBytes.drop idx).length c.mv
                ((l :: revLits).map kissatLitToDimacsLiteral) (cnfBytes.drop j) := by
            rw [parseClauseAux_eq_nextLitPure, hnl, ← hdrop]; rfl
          rw [← hpc_inv, hstep]
          exact parseClauseAux_fuel_irrel (by simp only [List.length_drop]; omega)
            (by simp only [List.length_drop]; omega)
        refine wp_join_group
          (fun (tl', taut', _err', ()) m_s =>
            ∃ tlen' mrk_n tmp_n,
              let st_n := st_r (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 l)
                mrk_n tmp_n fd_t elen_t
              (FullMem c st_n ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m_s ∧
              tl' = BitVec.ofNat 32 tlen' ∧
              IngestTumReadInv c accCnf s cnfBytes i0 j tlen' elen_t taut' (l :: revLits)
                mrk_n tmp_n fd_t)
          (fun _ ⟨tl', taut', _err', ⟨⟩⟩ m_s ⟨tlen', mrk_n, tmp_n, hm_n, htl', hinv_n⟩ => by
            subst htl'; p_lets
            exact ih1 (cnfBytes.length - j) _ m_s (by omega)
              ⟨j, tlen', elen_t, l :: revLits, mrk_n, tmp_n, fd_t, BitVec.ofNat 64 l,
                hm_n, rfl, rfl, hinv_n, hpc_next⟩)
          (fun Js hJs => by
            p_lets; rw [wp_jnz]
            simp only [Arg.val_var, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, bv8_zext32_eq_zero]
            refine ⟨fun hm0 => ?_, fun hmne0 => ?_⟩
            · have hm0' : mrk'[tl / 2]'(by rw [hmkl]; omega) = 0#8 := hm0
              have hmiss_v : ∀ k < tlen, (tmp'[k]?.getD 0#32).toNat / 2 ≠ tl / 2 := by
                intro k hk heq
                have hpos := hmrk_pos k hk
                rw [heq, List.getElem?_eq_getElem (by rw [hmkl]; omega),
                  Option.getD_some, hm0'] at hpos
                have h1 := congrArg BitVec.toNat hpos
                simp only [BitVec.toNat_ofNat] at h1; omega
              have htlen_lt : tlen < c.mv :=
                inj_lt_of_missing (fun k => (tmp'[k]?.getD 0#32).toNat / 2)
                  htmp_nd (fun k hk => by have := htmp_lt k hk; omega) htv_lt hmiss_v
              p_lets; refine wp_load_of (load_full_mv hm_t) ?_; p_lets
              rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega)]
              have hgd_t : (BitVec.ofNat 64 c.mv).ule (BitVec.ofNat 64 tlen) =
                  decide (c.mv ≤ tlen) := bv_ule_eq (by omega) (by omega)
              refine wp_head_jnz_iff (b := false)
                (by simp only [Arg.val_var, hgd_t]; simp [htlen_lt]) ?_
              refine ⟨fun h => (by cases h), fun _ => ?_⟩
              p_lets
              rw [bv32_zext64_eq, bv32_ofNat_toNat htv32, bv32_ptag_ofNat htl32]
              obtain ⟨okm, hmm⟩ := store_full_mrk (i := tl / 2) (BitVec.ofNat 8 (tl % 2 + 1))
                hmkl_t hm_t
              refine ⟨okm, ?_⟩; p_lets
              rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega), bv64_mul4_nat]
              have htmpl_t : tlen < ({ st_t with core := { st_t.core with
                  mrk := st_t.core.mrk.set (tl / 2)
                    (BitVec.ofNat 8 (tl % 2 + 1)) } }).core.tmp.length := by
                dsimp [st_t, st_r]; rw [htmpl]; omega
              obtain ⟨okt, hmt⟩ := store_full_tmp (i := tlen) (BitVec.ofNat 32 tl) htmpl_t hmm
              refine ⟨okt, ?_⟩; p_lets
              rw [bv32_add1_nat (by omega)]
              let mrk_n := mrk'.set (tl / 2) (BitVec.ofNat 8 (tl % 2 + 1))
              let tmp_n := tmp'.set tlen (BitVec.ofNat 32 tl)
              have heq_st : ({ st_t with core := { st_t.core with
                  mrk := st_t.core.mrk.set (tl / 2) (BitVec.ofNat 8 (tl % 2 + 1)),
                  tmp := st_t.core.tmp.set tlen (BitVec.ofNat 32 tl) } } : FullState) =
                  st_r (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 l) mrk_n tmp_n fd_t elen_t :=
                rfl
              rw [heq_st] at hmt
              exact hJs _ _ ⟨tlen + 1, mrk_n, tmp_n, hmt, rfl,
                ingestTumReadInv_push hc_mv (by omega) hj htlen_lt hl_mv hl_cov_t hri_t_copy
                  hmiss_v⟩
            · have hex : ∃ k0 < tlen, (tmp'[k0]?.getD 0#32).toNat / 2 = tl / 2 := by
                by_cases h : ∃ k0 < tlen, (tmp'[k0]?.getD 0#32).toNat / 2 = tl / 2
                · exact h
                · exfalso
                  have h0 := hmrk_zero (tl / 2) (by omega) (fun k hk heq => h ⟨k, hk, heq⟩)
                  rw [List.getElem?_eq_getElem (by rw [hmkl]; omega),
                    Option.getD_some] at h0; exact hmne0 h0
              obtain ⟨k0, hk0, hk0_v⟩ := hex
              have hmv_pos := hmrk_pos k0 hk0
              rw [hk0_v, List.getElem?_eq_getElem (by rw [hmkl]; omega),
                Option.getD_some] at hmv_pos
              refine wp_join_group
                (fun (taut', ()) m_j =>
                  (taut' = if mv_b = BitVec.ofNat 8 (tl % 2 + 1) then taut_v else true) ∧
                  m_j = m_t)
                (fun _ ⟨taut', ⟨⟩⟩ m_j ⟨htaut', hm_j⟩ => by
                  subst m_j; p_lets
                  refine hJs _ m_t ⟨tlen, mrk', tmp', hm_t, rfl,
                    ⟨by omega, hj, htlen_le, hmkl, htmpl, hfdl_t, hel_ge_t, hel_le_t, hti_t,
                      htc_t, hrel_eq_t, hfd_mono_t, hvals_lift_t,
                      (fun x hx => (List.mem_cons.mp hx).elim (fun h => h ▸ hl_mv) (hrev_lt x)),
                      (fun ht x hx => (List.mem_cons.mp hx).elim (fun h => h ▸ hl_cov_t ht)
                        (hrev_cov_t ht x)),
                      htmp_lt, htmp_nd, hmrk_zero, hmrk_pos,
                      ingestTum_dup_cov (by rw [hmkl]; exact hc_mv) htv_lt hk0 htaut' rfl hmv_pos
                        hcov_t hk0_v,
                      (fun k hk => by
                        rw [List.map_cons]; exact List.mem_cons_of_mem tl (hsub_rev_t k hk)),
                      (fun hc => by cases hc),
                      fun l' hl' => by
                        rcases List.cons.inj hl' with ⟨_, rfl⟩
                        exact absurd (hsub_rev_t k0 hk0) (by simp)⟩⟩)
                (fun Jt hJt => by
                  p_lets; rw [wp_jnz]
                  have hptag : BitVec.setWidth 8
                      ((BitVec.ofNat 32 (tumbleLit tum fd_t l) &&& (1 : BitVec 32)) +
                        (1 : BitVec 32)) = BitVec.ofNat 8 (tl % 2 + 1) :=
                    bv32_ptag_ofNat htl32
                  simp only [Arg.val_var, hptag, bv8_zext32_bne,
                    decide_eq_true_eq, decide_eq_false_iff_not, Classical.not_not]
                  refine ⟨fun hne => hJt (true, ()) m_t ⟨by simp [hne], rfl⟩,
                    fun heq => hJt (taut_v, ()) m_t ⟨by simp [heq], rfl⟩⟩))
      · -- Body of `if (tum)`
        intro Jtum hJtum
        p_lets
        refine wp_head_jnz_iff (b := tum) (by simpa [Arg.val_var] using htum_ult) ?_
        refine ⟨fun htum_t => ?_, fun htum_f => ?_⟩
        · -- `tum = true`: look up `iv = fd[ev]`
          p_lets
          rw [bv32_zext64_eq, bv32_lshr1, bv32_ofNat_toNat hl32, bv64_mul4_nat]
          have hfd_bd : l / 2 < st_d.core.frame_dec.length := by
            dsimp [st_d, st, st_r]; rw [hfdl]; omega
          refine wp_load_of (load_full_frame_dec (i := l / 2) hfd_bd hm'_a) ?_; p_lets
          let iv0 := fd'[l / 2]'(by rw [hfdl]; omega)
          have hiv0_st : st_d.core.frame_dec[l / 2]'hfd_bd = iv0 := rfl
          rw [hiv0_st]
          apply wp_unroll_group
          intro Jiv hJiv
          p_lets
          refine wp_head_jnz_iff (b := decide (iv0 = 0xFFFFFFFF#32))
            (by simp only [Arg.val_var]; by_cases h : iv0 = 0xFFFFFFFF#32 <;> simp [h]) ?_
          rw [decide_eq_true_eq, decide_eq_false_iff_not]
          refine ⟨fun hiv_ff => ?_, fun hiv_ne => ?_⟩
          · -- `iv == 0xFFFFFFFFu`: allocate `nxt = h->extend_len`, write `fd[ev] = nxt`
            have hun_ev : fd'[l / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
              rw [List.getElem?_eq_getElem (by rw [hfdl]; omega), Option.getD_some]; exact hiv_ff
            obtain ⟨hnxt_lt, hri_n⟩ := ingestTumReadInv_with_fd htum_t hc_mv hv_lt hun_ev hri_copy
            p_lets
            refine wp_load_of (load_full_extend_len hm'_a) ?_; p_lets
            have hel_d : st_d.scratch.extend_len = elen := rfl
            rw [hel_d]
            refine wp_load_of (load_full_mv hm'_a) ?_; p_lets
            have hgd_nxt : (BitVec.ofNat 64 c.mv).ule (BitVec.ofNat 64 elen) =
                decide (c.mv ≤ elen) := bv_ule_eq (by omega) (by omega)
            refine wp_head_jnz_iff (b := false)
              (by simp only [Arg.val_var, hgd_nxt]; simp [hnxt_lt]) ?_
            refine ⟨fun h => (by cases h), fun _ => ?_⟩
            p_lets
            rw [bv32_trunc64_ofNat_lt (by omega), bv32_zext64_eq, bv32_lshr1,
              bv32_ofNat_toNat hl32, bv64_mul4_nat]
            obtain ⟨okfd, hmfd⟩ := store_full_frame_dec (i := l / 2) (BitVec.ofNat 32 elen)
              hfd_bd hm'_a
            refine ⟨okfd, ?_⟩; p_lets
            rw [bv64_add1_nat (by omega)]
            obtain ⟨okel, hmel⟩ := store_full_extend_len (v := elen + 1) (by omega) hmfd
            refine ⟨okel, ?_⟩; p_lets
            -- Step through `hJiv` continuation: `v = iv; lit = (iv << 1) | (lit & 1u); jump Jtum`
            apply hJiv; p_lets
            let fd_n := fd'.set (l / 2) (BitVec.ofNat 32 elen)
            have hst_n : ({ { st_d with core := { st_d.core with frame_dec := fd_n } } with
                scratch := { st_d.scratch with extend_len := elen + 1 } } : FullState) =
                st_r (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 l)
                  mrk' tmp' fd_n (elen + 1) := rfl
            rw [hst_n] at hmel
            have htl_eq : tumbleLit tum fd_n l = 2 * elen + l % 2 := by
              unfold tumbleLit tumblePi
              rw [htum_t, List.getElem?_set_self (by rw [hfdl]; omega)]
              simp only [Option.getD_some, ↓reduceIte]
              rw [bv32_ofNat_toNat (by omega)]
            have htl_div : tumbleLit tum fd_n l / 2 = elen := by rw [htl_eq]; omega
            have hne_ff_el : fd_n[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
              rw [List.getElem?_set_self (by rw [hfdl]; omega), Option.getD_some]
              intro h; have := congrArg BitVec.toNat h
              rw [bv32_ofNat_toNat (by omega)] at this
              change elen = 2 ^ 32 - 1 at this; omega
            rw [bv32_tumble_lit_eq (by omega) hl32, ← htl_eq]
            exact hJtum (false, BitVec.ofNat 32 (tumbleLit tum fd_n l),
                BitVec.ofNat 32 elen, ()) _
              ⟨fd_n, elen + 1, hmel, rfl, by rw [htl_div], (fun _ => hne_ff_el), hri_n⟩
          · -- `iv != 0xFFFFFFFFu`: already mapped!
            p_lets; apply hJiv; p_lets
            have hmap_ev : fd'[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
              rw [List.getElem?_eq_getElem (by rw [hfdl]; omega), Option.getD_some]; exact hiv_ne
            have hiv0_lt : iv0.toNat < c.mv := by
              have hm := hti_r htum_t
              rcases hm.2.2.1 (l / 2) hv_lt with hff | hlt
              · exact absurd hff hmap_ev
              · rw [List.getElem?_eq_getElem (by rw [hfdl]; omega), Option.getD_some] at hlt
                exact Nat.lt_of_lt_of_le hlt hm.1
            have htl_eq : tumbleLit tum fd' l = 2 * iv0.toNat + l % 2 := by
              unfold tumbleLit tumblePi
              rw [htum_t, List.getElem?_eq_getElem (by rw [hfdl]; omega)]
              simp only [Option.getD_some, ↓reduceIte]; rfl
            have htl_div : tumbleLit tum fd' l / 2 = iv0.toNat := by rw [htl_eq]; omega
            have hiv0_of : BitVec.ofNat 32 iv0.toNat = iv0 :=
              BitVec.eq_of_toNat_eq (bv32_ofNat_toNat iv0.isLt)
            rw [← hiv0_of, bv32_tumble_lit_eq (by omega) hl32, ← htl_eq]
            exact hJtum (false, BitVec.ofNat 32 (tumbleLit tum fd' l),
                BitVec.ofNat 32 iv0.toNat, ()) m'
              ⟨fd', elen, hm'_a, rfl, by rw [htl_div], (fun _ => hmap_ev), hri_copy⟩
        · -- `tum = false`: identity (`v = ev`, `lit = l`)
          p_lets
          have htl_eq : tumbleLit tum fd' l = l := by rw [htum_f]; exact tumbleLit_false fd' l
          have hv_eq : BitVec.ofNat 32 l >>> (1 : Nat) = BitVec.ofNat 32 (l / 2) := by
            apply BitVec.eq_of_toNat_eq
            rw [bv32_lshr1, bv32_ofNat_toNat hl32, bv32_ofNat_toNat (by omega)]
          rw [hv_eq]
          exact hJtum (false, BitVec.ofNat 32 l, BitVec.ofNat 32 (l / 2), ()) m'
            ⟨fd', elen, hm'_a, by rw [htl_eq], by rw [htl_eq],
              (fun ht => by rw [htum_f] at ht; cases ht), hri_copy⟩
  · -- Read-loop entry
    intro B1 L1 _ hL1; p_lets
    exact hL1 (cnfBytes.length - i0) _ m
      ⟨i0, 0, s.scratch.extend_len, [], s.core.mrk, s.core.tmp, s.core.frame_dec, s.core.d_val,
        by rw [hst0]; exact hm0, rfl, rfl,
        ⟨Nat.le_refl _, hi0, Nat.zero_le _, hcok.mrk_len, hcok.tmp_len_arr, hcok.frame_dec_len,
          Nat.le_refl _, hinv.2.2.2.2.1.2, hti0, htc0, rfl, fun _ _ _ => rfl,
          fun _ hvr _ => hvr,
          (fun _ h => by cases h), (fun _ _ h => by cases h),
          fun _ h => by omega, fun _ _ h => by omega,
          fun v hv _ => hinv.2.2.1.1 v hv, fun _ h => by omega,
          (fun _ _ h => by cases h), (fun _ h => by omega), (fun _ => rfl),
          (fun _ h => by cases h)⟩,
        by unfold parseClause; simp⟩

end IngestClTumProof

end LeanQbe.T.Examples.Kissat.FullFidelityTumble

end
