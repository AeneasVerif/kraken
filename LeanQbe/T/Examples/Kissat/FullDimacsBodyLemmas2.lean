module

public import LeanQbe.T.Examples.Kissat.FullDimacsBodyLemmas1

/-!
# Soundness Proofs for Kissat `D-Full` DIMACS Clause Ingestion (`Stage 4`, Part 2)

Proves `full_ingest_cl_wp` (`Full1.full_ingest_cl`), UNSAT-only with `UnitUnsatTrace` unit
postconditions, witness-entailment threading (`FullSparseInvW` + `Entails`), and `probing` framing.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap LeanQbe.T.C0Step
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

section IngestClProof

open scoped FullArenaTactics FullDimacsBodyTactics
open FullArenaTactics FullDimacsBodyTactics FullDimacsBodySpecs

/-! ## 1. Pure & witness helpers for `full_ingest_cl` -/

private theorem fullIngest_unit_rev {revLits : List Nat} {l : Nat}
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

private theorem entails_cnfOfClauses_cons {F0 : CNF Nat} {cl : List Nat} {F : List (List Nat)}
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

private theorem cnfOfClauses_cons_entails (cl : List Nat) (F : List (List Nat)) :
    (cnfOfClauses (cl :: F)).Entails (cnfOfClauses F) := by
  rw [CNF.entails_def]
  intro α hα
  rw [cnf_sat_cnfOfClauses_iff] at hα ⊢
  intro c hc; exact hα c (List.mem_cons_of_mem _ hc)

private theorem cnfOfClauses_cons_entails_head (cl : List Nat) (F : List (List Nat)) :
    (cnfOfClauses (cl :: F)).EntailsClause (cnfClause cl) := by
  rw [CNF.entails_clause_def]
  intro α hα
  rw [cnf_sat_cnfOfClauses_iff] at hα
  exact hα cl (List.mem_cons_self)

private theorem extUnsatSound_of_entails {F0 : CNF Nat} {mv : Nat} {F : List (List Nat)}
    (hb : VarsBounded mv F) (hent : F0.Entails (cnfOfClauses F)) : ExtUnsatSound F0 mv F := by
  refine ⟨hb, fun hu => ?_⟩
  rw [CNF.entails_def] at hent
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα; exact hu α (hent α hα)

private theorem varsBounded_cons {mv : Nat} {cl : List Nat} {F : List (List Nat)}
    (hcl : ∀ l ∈ cl, l < 2 * mv) (hb : VarsBounded mv F) : VarsBounded mv (cl :: F) := by
  intro c hc l hl
  rcases List.mem_cons.mp hc with rfl | hc'
  · exact Nat.div_lt_of_lt_mul (hcl l hl)
  · exact hb c hc' l hl

private theorem nodup_of_pairwise_div2 {xs : List (BitVec 32)} {n : Nat} (hn : n ≤ xs.length)
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

private theorem addUnit_preserves_witness {c : FullCfg} {F0 : CNF Nat}
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

/-! ## 2. Read-loop & prune-loop invariants for `full_ingest_cl` -/

private def IngestReadInv (c : FullCfg) (cnfBytes : List UInt8) (i0 idx tlen : Nat)
    (taut : Bool) (revLits : List Nat) (st : FullState) : Prop :=
  i0 ≤ idx ∧ idx ≤ cnfBytes.length ∧ tlen ≤ c.mv ∧
  st.core.mrk.length = c.max_vars ∧ st.core.tmp.length = c.max_vars ∧
  (∀ k < tlen, (st.core.tmp[k]?.getD 0#32).toNat < 2 * c.mv) ∧
  (∀ k1 k2, k1 < tlen → k2 < tlen →
    (st.core.tmp[k1]?.getD 0#32).toNat / 2 = (st.core.tmp[k2]?.getD 0#32).toNat / 2 → k1 = k2) ∧
  (∀ v < c.max_vars, (∀ k < tlen, (st.core.tmp[k]?.getD 0#32).toNat / 2 ≠ v) →
    st.core.mrk[v]?.getD 0#8 = 0#8) ∧
  (∀ k < tlen, st.core.mrk[(st.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#8 =
    BitVec.ofNat 8 ((st.core.tmp[k]?.getD 0#32).toNat % 2 + 1)) ∧
  (taut = false → ∀ l ∈ revLits, ∃ k < tlen, (st.core.tmp[k]?.getD 0#32).toNat = l) ∧
  (∀ k < tlen, (st.core.tmp[k]?.getD 0#32).toNat ∈ revLits) ∧ (revLits = [] → taut = false) ∧
  (∀ l, revLits = [l] → taut = false ∧ tlen = 1 ∧ (st.core.tmp[0]?.getD 0#32).toNat = l)

private theorem ingestReadInv_push {c : FullCfg} {cnfBytes : List UInt8}
    {i0 idx j tlen l : Nat} {taut : Bool} {revLits : List Nat} {s : FullState}
    {mrk' : List (BitVec 8)} {tmp' : List (BitVec 32)} {cnf_ptr dcur_n dv_n : BitVec 64}
    (hc_mv : c.mv ≤ c.max_vars)
    (hi_j : i0 ≤ j) (hj : j ≤ cnfBytes.length) (htl : tlen < c.mv)
    (hmkl : mrk'.length = c.max_vars) (htmpl : tmp'.length = c.max_vars)
    (hl_mv : l < 2 * c.mv) (hl32 : l < 2 ^ 32) (hv_lt : l / 2 < c.mv)
    (hmiss_v : ∀ k < tlen, (tmp'[k]?.getD 0#32).toNat / 2 ≠ l / 2)
    (hri : IngestReadInv c cnfBytes i0 idx tlen taut revLits
      { s with core := { s.core with d_cur := cnf_ptr + BitVec.ofNat 64 idx,
                                     mrk := mrk', tmp := tmp' } }) :
    IngestReadInv c cnfBytes i0 j (tlen + 1) taut (l :: revLits)
      { s with core :=
        { s.core with d_cur := dcur_n, d_val := dv_n,
                      mrk := mrk'.set (l / 2) (BitVec.ofNat 8 (l % 2 + 1)),
                      tmp := tmp'.set tlen (BitVec.ofNat 32 l) } } := by
  rcases hri with ⟨_, _, _, _, _, htmp_lt, htmp_nd, hmrk_zero, hmrk_pos, hcov, hsub_rev,
    hnil_taut, _⟩
  have hn_lt : tlen < tmp'.length := by rw [htmpl]; omega
  have hm_lt : l / 2 < mrk'.length := by rw [hmkl]; omega
  refine ⟨hi_j, hj, by omega, by simp [hmkl], by simp [htmpl], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk; by_cases hkt : k = tlen
    · subst k; simp [List.getElem?_set_self hn_lt, bv32_ofNat_toNat hl32, hl_mv]
    · simp [List.getElem?_set_ne (Ne.symm hkt), htmp_lt k (by omega)]
  · intro k1 k2 h1 h2 heq; by_cases hk1 : k1 = tlen <;> by_cases hk2 : k2 = tlen
    · omega
    · subst hk1; simp [List.getElem?_set_self hn_lt, List.getElem?_set_ne (Ne.symm hk2),
        bv32_ofNat_toNat hl32] at heq; exact absurd heq.symm (hmiss_v k2 (by omega))
    · subst hk2; simp [List.getElem?_set_self hn_lt, List.getElem?_set_ne (Ne.symm hk1),
        bv32_ofNat_toNat hl32] at heq; exact absurd heq (hmiss_v k1 (by omega))
    · simp [List.getElem?_set_ne (Ne.symm hk1), List.getElem?_set_ne (Ne.symm hk2)] at heq
      exact htmp_nd k1 k2 (by omega) (by omega) heq
  · intro v hv hmiss
    have hne : v ≠ l / 2 := by
      have h := hmiss tlen (by omega)
      simp [List.getElem?_set_self hn_lt, bv32_ofNat_toNat hl32] at h; exact Ne.symm h
    rw [List.getElem?_set_ne (Ne.symm hne)]
    exact hmrk_zero v hv fun k hk => by
      have h := hmiss k (by omega); simpa [List.getElem?_set_ne (by omega : tlen ≠ k)] using h
  · intro k hk; by_cases hkt : k = tlen
    · subst k; simp [List.getElem?_set_self hn_lt, List.getElem?_set_self hm_lt,
        bv32_ofNat_toNat hl32]
    · simp [List.getElem?_set_ne (Ne.symm hkt),
        List.getElem?_set_ne (Ne.symm (hmiss_v k (by omega))), hmrk_pos k (by omega)]
  · intro ht x hx; rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨tlen, by omega, by simp [List.getElem?_set_self hn_lt, bv32_ofNat_toNat hl32]⟩
    · obtain ⟨k, hk, hget⟩ := hcov ht x hx'
      exact ⟨k, by omega, by simpa [List.getElem?_set_ne (by omega : tlen ≠ k)] using hget⟩
  · intro k hk; by_cases hkt : k = tlen
    · subst k; simp [List.getElem?_set_self hn_lt, bv32_ofNat_toNat hl32]
    · simp only [List.getElem?_set_ne (Ne.symm hkt)]
      exact List.mem_cons_of_mem l (hsub_rev k (by omega))
  · intro hc; cases hc
  · intro l' hl'; rcases List.cons.inj hl' with ⟨rfl, rfl⟩
    have ht0 : tlen = 0 := by
      cases tlen with | zero => rfl | succ k => exact absurd (hsub_rev 0 (by omega)) (by simp)
    subst ht0
    exact ⟨hnil_taut rfl, rfl, by simp [List.getElem?_set_self hn_lt, bv32_ofNat_toNat hl32]⟩

private def IngestPruneInv (c : FullCfg) (s : FullState) (tmp' : List (BitVec 32))
    (revLits : List Nat) (tlen keep i : Nat) (tmp'' : List (BitVec 32)) : Prop :=
  keep ≤ i ∧ i ≤ tlen ∧ tmp''.length = c.max_vars ∧
  (∀ k, i ≤ k → k < tlen → tmp''[k]? = tmp'[k]?) ∧
  (∀ k < keep, (tmp''[k]?.getD 0#32).toNat < 2 * c.mv ∧
    s.core.vals[(tmp''[k]?.getD 0#32).toNat]?.getD 0#8 = 0#8) ∧
  (∀ k < keep, ∃ m < i, tmp''[k]? = tmp'[m]?) ∧
  (∀ k1 k2, k1 < keep → k2 < keep →
    (tmp''[k1]?.getD 0#32).toNat / 2 = (tmp''[k2]?.getD 0#32).toNat / 2 → k1 = k2) ∧
  (∀ k < i, (∃ j < keep, tmp''[j]? = tmp'[k]?) ∨
    s.core.vals[(tmp'[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
  (∀ l < 2 * c.mv, revLits = [l] → s.core.vals[l]?.getD 0#8 = 0#8 →
    i = 1 → keep = 1 ∧ (tmp''[0]?.getD 0#32).toNat = l) ∧
  (∀ l < 2 * c.mv, revLits = [l] → s.core.vals[l]?.getD 0#8 = 0xFF#8 → i = 1 → keep = 0)

private theorem ingestPruneInv_push {c : FullCfg} {s : FullState} {tmp' tmp'' : List (BitVec 32)}
    {revLits : List Nat} {tlen keep i : Nat} {li : BitVec 32}
    (hc_mv : c.mv ≤ c.max_vars)
    (hlt : i < tlen) (htlen_le : tlen ≤ c.mv) (htmpl : tmp'.length = c.max_vars)
    (htmp_nd : ∀ k1 k2, k1 < tlen → k2 < tlen →
      (tmp'[k1]?.getD 0#32).toNat / 2 = (tmp'[k2]?.getD 0#32).toNat / 2 → k1 = k2)
    (hli_eq : li = tmp'[i]'(by rw [htmpl]; omega)) (hli_lt : li.toNat < 2 * c.mv)
    (hlv_getD : s.core.vals[li.toNat]?.getD 0#8 = 0#8)
    (hunit0 : ∀ l, revLits = [l] → (tmp'[0]?.getD 0#32).toNat = l)
    (hpi : IngestPruneInv c s tmp' revLits tlen keep i tmp'') :
    IngestPruneInv c s tmp' revLits tlen (keep + 1) (i + 1) (tmp''.set keep li) := by
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
      have := htmp_nd m i (by omega) hlt heq
      omega
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
  · intro l hl_lt hrev _ hi1
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

private theorem ingestPruneInv_skip {c : FullCfg} {s : FullState} {tmp' tmp'' : List (BitVec 32)}
    {revLits : List Nat} {tlen keep i : Nat} {li : BitVec 32}
    (hc_mv : c.mv ≤ c.max_vars)
    (hlt : i < tlen) (htlen_le : tlen ≤ c.mv) (htmpl : tmp'.length = c.max_vars)
    (hli_eq : li = tmp'[i]'(by rw [htmpl]; have htmv := Nat.le_trans htlen_le hc_mv; omega))
    (hlv_ff : s.core.vals[li.toNat]?.getD 0#8 = 0xFF#8)
    (hunit0 : ∀ l, revLits = [l] → (tmp'[0]?.getD 0#32).toNat = l)
    (hpi : IngestPruneInv c s tmp' revLits tlen keep i tmp'') :
    IngestPruneInv c s tmp' revLits tlen keep (i + 1) tmp'' := by
  rcases hpi with ⟨hk_le, hi_le, htmp'l, htail, hkeep_un, hkeep_src, hkeep_nd, hpruned, _, _⟩
  have htmv : tlen ≤ c.max_vars := Nat.le_trans htlen_le hc_mv
  refine ⟨by omega, by omega, htmp'l, fun k hk1 hk2 => htail k (by omega) hk2, hkeep_un,
    (fun k hk => let ⟨m, hm, hm_eq⟩ := hkeep_src k hk; ⟨m, by omega, hm_eq⟩), hkeep_nd, ?_, ?_, ?_⟩
  · intro k hk; by_cases hki : k = i
    · subst k; refine Or.inr ?_
      rw [List.getElem?_eq_getElem (i := i) (by rw [htmpl]; omega), Option.getD_some, ← hli_eq]
      exact hlv_ff
    · exact hpruned k (by omega)
  · intro l hl_lt hrev hv0 hi1
    have hi0 : i = 0 := by omega
    subst hi0; have hl0 := hunit0 l hrev
    rw [List.getElem?_eq_getElem (l := tmp') (i := 0) (by rw [htmpl]; omega), Option.getD_some,
      ← hli_eq] at hl0
    rw [← hl0] at hv0; exact absurd (hlv_ff.symm.trans hv0) (by decide)
  · intro _ _ _ _ _; omega

private theorem ingest_keep_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {accCnf : CNF Nat} {cl : CNF.Clause Nat}
    {s : FullState} {tmp' tmp'' : List (BitVec 32)} {revLits : List Nat} {tlen keep : Nat}
    (hcv : s.core.cur_vars = c.mv)
    (hw : FullWitnessInv c F0 F_cur s.core) (hcl0 : s.core.cur_level = 0)
    (htlen_le : tlen ≤ c.mv) (htmpl : tmp'.length = c.max_vars)
    (hc_mv : c.mv ≤ c.max_vars)
    (htmp_lt : ∀ k < tlen, (tmp'[k]?.getD 0#32).toNat < 2 * c.mv)
    (hF1_ent : (shiftDownCnf (accCnf.add cl)).Entails (cnfOfClauses F_cur))
    (hF1_cl : (shiftDownCnf (accCnf.add cl)).EntailsClause
      (cnfClause ((tmp'.take tlen).map BitVec.toNat)))
    (hpi : IngestPruneInv c s tmp' revLits tlen keep tlen tmp'') :
    (shiftDownCnf (accCnf.add cl)).EntailsClause
      (cnfClause ((tmp''.take keep).map BitVec.toNat)) := by
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
    have hent_F1 : (shiftDownCnf (accCnf.add cl)).EntailsClause
        (cnfClause [(s.core.trl[ti]?.getD 0#32).toNat]) :=
      CNF.entails_clause_trans hF1_ent hent0
    rwa [htr_eq] at hent_F1

private abbrev FullIngestPost (c : FullCfg) (accCnf : CNF Nat) (s : FullState)
    (cnf_ptr : BitVec 64) (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop)
    (Q : Post [i64]) (cl : CNF.Clause Nat) (rest : List UInt8) : Prop :=
  ∀ r s' j m', (∀ lit ∈ cl.literals, 1 ≤ lit.1) → i0 < j → j ≤ cnfBytes.length →
    cnfBytes.drop j = rest → s'.LengthsOk c → s'.core.cur_vars = c.mv →
    s'.core.d_cur = cnf_ptr + BitVec.ofNat 64 j → s'.core.cur_level = 0 →
    s'.core.fuel = s.core.fuel → s'.core.oom = s.core.oom → s'.core.probing = s.core.probing →
    (r = 1#64 ∨ r = 2#64 ∨ r = 3#64) →
    (r = 1#64 → ∃ F_cur', FullSparseInvW c (shiftDownCnf (accCnf.add cl)) F_cur' s' ∧
      (shiftDownCnf (accCnf.add cl)).Entails (cnfOfClauses F_cur')) →
    (r = 2#64 → (shiftDownCnf (accCnf.add cl)).Unsat) →
    (∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
      s.core.vals[l]?.getD 0#8 = 0#8 → r = 1#64 ∧
      (∀ k < 2 * c.mv, s'.core.vals[k]?.getD 0#8 =
        ((s.core.vals.set l 1#8).set (l ^^^ 1) 0xFF#8)[k]?.getD 0#8) ∧
      s'.core.trail_end = s.core.trail_end + 1 ∧ s'.core.propagated = s.core.propagated) →
    (∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
      s.core.vals[l]?.getD 0#8 = 0xFF#8 → r = 2#64) →
    (bytes cnf_ptr cnfBytes ⋆ FullMem c s' ⋆ R) m' → Q (r, ()) m'

private theorem ingest_st3_inv {c : FullCfg} {F0 F1 : CNF Nat} {F_cur : List (List Nat)}
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
  have hdm : st3.core.dense_mode = 0#64 := by rw [hs1]; exact hdm0
  rw [hs1] at hlen3 ⊢
  refine ⟨hlen3,
    { hw0 with
      ext_sound := extUnsatSound_of_entails hw0.ext_sound.1 hent
      arena := { hw0.arena with len_ok := hw0.arena.len_ok }
      watches := hw0.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
    ?_, ?_, ?_, ?_⟩
  · simpa [← hs1] using hltm
  · simpa [← hs1] using hnd
  · simpa [← hs1] using hext_sc
  · exact hdm0

private theorem ingest_ret_exit {c : FullCfg} {accCnf : CNF Nat} {s st_out : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 idx : Nat} {revLits : List Nat}
    {r_out : BitVec 64} {R : Mem 64 → Prop} {m_out : Mem 64} {Q : Post [i64]}
    (hcl_pos : ∀ lit ∈ (CNF.Clause.ofLiterals
      (revLits.reverse.map kissatLitToDimacsLiteral)).literals, 1 ≤ lit.1)
    (hi0 : i0 < idx) (hidx : idx ≤ cnfBytes.length) (hlens : st_out.LengthsOk c)
    (hcv : st_out.core.cur_vars = c.mv)
    (hd : st_out.core.d_cur = cnf_ptr + BitVec.ofNat 64 idx) (hcl : st_out.core.cur_level = 0)
    (hfu : st_out.core.fuel = s.core.fuel) (hoom : st_out.core.oom = s.core.oom)
    (hpr : st_out.core.probing = s.core.probing)
    (hdom : r_out = 1#64 ∨ r_out = 2#64 ∨ r_out = 3#64)
    (hi1 : r_out = 1#64 → ∃ F_cur', FullSparseInvW c (shiftDownCnf (accCnf.add
      (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral)))) F_cur' st_out ∧
      (shiftDownCnf (accCnf.add
        (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral)))).Entails
          (cnfOfClauses F_cur'))
    (hi2 : r_out = 2#64 → (shiftDownCnf (accCnf.add
      (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral)))).Unsat)
    (hno_u0 : ∀ l < 2 * c.mv, revLits = [l] → s.core.vals[l]?.getD 0#8 = 0#8 →
      r_out = 1#64 ∧
      (∀ k < 2 * c.mv, st_out.core.vals[k]?.getD 0#8 =
        ((s.core.vals.set l 1#8).set (l ^^^ 1) 0xFF#8)[k]?.getD 0#8) ∧
      st_out.core.trail_end = s.core.trail_end + 1 ∧
      st_out.core.propagated = s.core.propagated)
    (hno_u1 : ∀ l < 2 * c.mv, revLits = [l] → s.core.vals[l]?.getD 0#8 = 0xFF#8 → r_out = 2#64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ FullMem c st_out ⋆ R) m_out)
    (hQ : FullIngestPost c accCnf s cnf_ptr cnfBytes i0 R Q
      (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral))
      (cnfBytes.drop idx)) : Q (r_out, ()) m_out :=
  hQ r_out st_out idx m_out hcl_pos hi0 hidx rfl hlens hcv hd hcl hfu hoom hpr hdom hi1 hi2
    (fun l hl hcleq => hno_u0 l hl (fullIngest_unit_rev hcleq))
    (fun l hl hcleq => hno_u1 l hl (fullIngest_unit_rev hcleq)) hm

private theorem ingest_dup_cov {mv tlen : Nat} {tmp' : List (BitVec 32)} {mrk' : List (BitVec 8)}
    {revLits : List Nat} {taut' taut_v : Bool} {l k0 : Nat} {mv_b : BitVec 8}
    (hmkl : mv ≤ mrk'.length) (hv_lt : l / 2 < mv) (hk0 : k0 < tlen)
    (htaut' : taut' = if mv_b = BitVec.ofNat 8 (l % 2 + 1) then taut_v else true)
    (hmv_b : mv_b = mrk'[l / 2]'(by omega))
    (hmv_pos : mrk'[l / 2]'(by omega) = BitVec.ofNat 8 ((tmp'[k0]?.getD 0#32).toNat % 2 + 1))
    (hcov : taut_v = false → ∀ x ∈ revLits, ∃ k < tlen, (tmp'[k]?.getD 0#32).toNat = x)
    (hk0_v : (tmp'[k0]?.getD 0#32).toNat / 2 = l / 2) :
    taut' = false → ∀ x ∈ l :: revLits, ∃ k < tlen, (tmp'[k]?.getD 0#32).toNat = x := by
  intro hnt' x hx
  by_cases hmeq : mv_b = BitVec.ofNat 8 (l % 2 + 1)
  · simp only [hmeq, ↓reduceIte] at htaut'
    rcases List.mem_cons.mp hx with rfl | hx'
    · refine ⟨k0, hk0, ?_⟩
      have h1 := hmv_pos.symm.trans (hmv_b.symm.trans hmeq)
      have hmod := congrArg BitVec.toNat h1
      simp only [BitVec.toNat_ofNat] at hmod; omega
    · exact hcov (htaut' ▸ hnt') x hx'
  · simp only [hmeq, ↓reduceIte] at htaut'; rw [htaut'] at hnt'; cases hnt'

/-! ## 3. `full_ingest_cl` proof -/

theorem full_ingest_cl_wp (Γ : Env)
    (hLit : ∀ args m Q X, kissatNextLitSpec args m Q X →
      Γ "kissat_next_lit" [i64, i64] [i64] args m Q X)
    (hAssign : ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hAddCl : ∀ args m Q X, fullAddClauseSpec args m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] args m Q X) :
    ∀ args m Q X, fullIngestClSpec args m Q X → Func.wp Γ full_ingest_cl_body args m Q X := by
  rintro ⟨h, cend, ⟨⟩⟩ m Q X
    ⟨c, accCnf, F_cur, s, cnf_ptr, cnfBytes, i0, R, rfl, rfl, hfit, hi0,
      hcv, hdcur, hcl0, hinv, hent_init, hm, hQ⟩
  have hmv := c.hmv; have hmaxv := c.hmaxv; unfold dimacsBound at hmv hmaxv
  have hlen := hinv.1; have hcok := hlen.core_ok; have hw0 := hinv.2.1
  have hc_mv : c.mv ≤ c.max_vars := by rw [← hcv]; exact hcok.cur_vars_le
  unfold Func.wp full_ingest_cl_body; p_lets
  have hm0 : (FullMem c s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
  refine wp_load_of (load_full_tmp_lits_ptr hm0) ?_; p_lets
  refine wp_load_of (load_full_mark_ptr hm0) ?_; p_lets
  refine wp_load_of (load_full_values_ptr hm0) ?_; p_lets
  let st_r (dc dv : BitVec 64) (mk : List (BitVec 8)) (tp : List (BitVec 32)) : FullState :=
    { s with core := { s.core with d_cur := dc, d_val := dv, mrk := mk, tmp := tp } }
  have hst0 : st_r (cnf_ptr + BitVec.ofNat 64 i0) s.core.d_val s.core.mrk s.core.tmp = s := by
    rw [← hdcur]
  refine wp_loop_break_group (brkTs := [i32, .bool, .bool]) (lpTs := [i32, .bool])
    (fun (tlen_v, taut_v, err_v, ()) mb => ∃ idx tlen revLits mrk' tmp' dcur dval,
      let st := st_r dcur dval mrk' tmp'
      tlen_v = BitVec.ofNat 32 tlen ∧ IngestReadInv c cnfBytes i0 idx tlen taut_v revLits st ∧
      (err_v = true → parseClause c.mv (cnfBytes.drop i0) = none) ∧
      (err_v = false → i0 < idx ∧ dcur = cnf_ptr + BitVec.ofNat 64 idx ∧
        parseClause c.mv (cnfBytes.drop i0) =
          some (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral),
            cnfBytes.drop idx)) ∧
      (bytes cnf_ptr cnfBytes ⋆ FullMem c st ⋆ R) mb)
    (fun r (tlen_v, taut_v, ()) ml => ∃ idx tlen revLits mrk' tmp' dval,
      let st := st_r (cnf_ptr + BitVec.ofNat 64 idx) dval mrk' tmp'
      r = cnfBytes.length - idx ∧ tlen_v = BitVec.ofNat 32 tlen ∧
      IngestReadInv c cnfBytes i0 idx tlen taut_v revLits st ∧
      parseClauseAux ((cnfBytes.drop idx).length + 1) c.mv
        (revLits.map kissatLitToDimacsLiteral) (cnfBytes.drop idx) =
        parseClause c.mv (cnfBytes.drop i0) ∧
      (bytes cnf_ptr cnfBytes ⋆ FullMem c st ⋆ R) ml)
    ?_ ?_ ?_
  · rintro _ ⟨tlen_v, taut_v, err_v, ⟨⟩⟩ mb
      ⟨idx, tlen, revLits, mrk', tmp', dcur, dval, rfl, hri, herr_p, hok_p, hmb⟩
    obtain ⟨hi_le, hidx, htlen_le, hmkl, htmpl, htmp_lt, htmp_nd,
      hmrk_zero, hmrk_pos, hcov, hsub_rev, hnil_taut, hunit_r⟩ := hri
    p_lets
    refine wp_loop_group (ts := [i32])
      (fun r2 (kv, ()) m2 => ∃ k mrk'',
        k ≤ tlen ∧ r2 = tlen - k ∧ kv = BitVec.ofNat 32 k ∧ mrk''.length = c.max_vars ∧
        (∀ v < c.max_vars, (∀ j, k ≤ j → j < tlen → (tmp'[j]?.getD 0#32).toNat / 2 ≠ v) →
          mrk''[v]?.getD 0#8 = 0#8) ∧
        (bytes cnf_ptr cnfBytes ⋆ FullMem c (st_r dcur dval mrk'' tmp') ⋆ R) m2) ?_ ?_
    · rintro L2 r2 ⟨kv, ⟨⟩⟩ m2 ih2 ⟨k, mrk'', hkle, rfl, rfl, hmk''l, hclr, hm2⟩
      p_lets
      have hult_k := bv32_ult_eq (a := k) (b := tlen) (by omega) (by omega)
      refine wp_head_jnz_iff (b := decide (k < tlen)) (by simpa [Arg.val_var] using hult_k) ?_
      rw [decide_eq_true_eq, decide_eq_false_iff_not]
      refine ⟨fun hklt => ?_, fun hkge => ?_⟩
      · p_lets
        have hm2a : (FullMem c (st_r dcur dval mrk'' tmp') ⋆
            (bytes cnf_ptr cnfBytes ⋆ R)) m2 := sep_ac hm2
        rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega), bv64_mul4_nat]
        have htm_bd_k : k < (st_r dcur dval mrk'' tmp').core.tmp.length := by
          dsimp [st_r]; rw [htmpl]; omega
        refine wp_load_of (load_full_tmp (i := k) htm_bd_k hm2a) ?_; p_lets
        let kv32 := tmp'[k]'(by rw [htmpl]; omega)
        have hkv32_st : (st_r dcur dval mrk'' tmp').core.tmp[k]'htm_bd_k = kv32 := rfl
        rw [hkv32_st]
        have hkvar_lt : kv32.toNat / 2 < c.mv := by
          have := htmp_lt k hklt
          dsimp only [st_r] at this
          rw [List.getElem?_eq_getElem (by rw [htmpl]; omega), Option.getD_some] at this
          change kv32.toNat < 2 * c.mv at this; omega
        refine wp_join_group (ts := [])
          (fun () m_in => ∃ mrk''', mrk'''.length = c.max_vars ∧
            (∀ v < c.max_vars,
              (∀ j, k + 1 ≤ j → j < tlen → (tmp'[j]?.getD 0#32).toNat / 2 ≠ v) →
              mrk'''[v]?.getD 0#8 = 0#8) ∧
            (bytes cnf_ptr cnfBytes ⋆ FullMem c (st_r dcur dval mrk''' tmp') ⋆ R) m_in)
          (fun _ ⟨⟩ m_in ⟨mrk''', hmk'''l, hclr''', hm_in⟩ => by
            p_lets; rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
              show BitVec.ofNat 32 k + BitVec.ofNat 32 1 = BitVec.ofNat 32 (k + 1) by bv_omega]
            exact ih2 (tlen - (k + 1)) _ m_in (by omega)
              ⟨k + 1, mrk''', by omega, rfl, rfl, hmk'''l, hclr''', hm_in⟩)
          (fun Jk hJk => by
            p_lets; refine wp_load_of (load_full_mv hm2a) ?_; p_lets
            rw [bv32_zext64_eq, bv32_lshr1]
            have hult_kv : (BitVec.ofNat 64 (kv32.toNat / 2)).ult (BitVec.ofNat 64 c.mv) =
                true := by rw [bv_ult_eq (by omega) (by omega)]; simp [hkvar_lt]
            refine wp_head_jnz_iff (b := true) (by simpa [Arg.val_var] using hult_kv) ?_
            refine ⟨fun _ => ?_, fun h => (by cases h)⟩
            p_lets; rw [bv32_zext64_eq, bv32_lshr1]
            have hmk_bd_kv : kv32.toNat / 2 < (st_r dcur dval mrk'' tmp').core.mrk.length := by
              dsimp [st_r]; rw [hmk''l]; omega
            obtain ⟨okm, hmm⟩ := store_full_mrk (i := kv32.toNat / 2) 0#8 hmk_bd_kv hm2a
            refine ⟨okm, ?_⟩; p_lets
            have heq : ({ st_r dcur dval mrk'' tmp' with core :=
                { (st_r dcur dval mrk'' tmp').core with
                  mrk := mrk''.set (kv32.toNat / 2) 0#8 } } : FullState) =
                st_r dcur dval (mrk''.set (kv32.toNat / 2) 0#8) tmp' := rfl
            rw [heq] at hmm
            refine hJk () _ ⟨mrk''.set (kv32.toNat / 2) 0#8, by simp [hmk''l],
              fun v hv hmiss => by
                by_cases hveq : v = kv32.toNat / 2
                · subst v
                  rw [List.getElem?_set_self (by rw [hmk''l]; omega)]; rfl
                · rw [List.getElem?_set_ne (Ne.symm hveq)]
                  exact hclr v hv fun j hj1 hj2 => if hj_eq : j = k then by
                    subst j
                    rw [List.getElem?_eq_getElem (l := tmp') (by rw [htmpl]; omega),
                      Option.getD_some]
                    exact Ne.symm hveq
                  else hmiss j (by omega) hj2, sep_ac hmm⟩)
      · have hkeq : k = tlen := by omega
        subst k
        let st2 := st_r dcur dval mrk'' tmp'
        have hlen2 : st2.LengthsOk c :=
          ⟨{ hcok with mrk_len := hmk''l, tmp_len_arr := htmpl }, hlen.scratch_ok⟩
        have hmrk_clr : FullLitMarksClear c st2 :=
          ⟨fun v hv => hclr v hv (fun j hj1 hj2 => by omega), hinv.2.2.1.2⟩
        have hinv2 : FullSparseInvW c (shiftDownCnf accCnf) F_cur st2 :=
          ⟨hlen2,
            { hw0 with
              arena := { hw0.arena with len_ok := hw0.arena.len_ok }
              watches := hw0.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
            hmrk_clr, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2⟩
        p_lets; refine wp_head_jnz_iff (b := err_v) (by c0_val_eq) ?_
        refine ⟨fun herr => ?_, fun hnoerr => ?_⟩
        · have hnone := herr_p herr; rw [hnone] at hQ; p_lets
          exact hQ st2 m2 hlen2 rfl rfl rfl hm2
        · obtain ⟨hi0_lt, hdcur_eq, hpc_some⟩ := hok_p hnoerr
          subst hdcur_eq
          let cl := CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral)
          have hcl_pos : ∀ lit ∈ cl.literals, 1 ≤ lit.1 := by
            intro lit hlit; simp only [cl, CNF.Clause.literals_ofLiterals, List.mem_map] at hlit
            rcases hlit with ⟨l, _, rfl⟩; simp [kissatLitToDimacsLiteral]
          rw [hpc_some] at hQ
          let F1 := shiftDownCnf (accCnf.add cl)
          have hF1_ent : F1.Entails (cnfOfClauses F_cur) :=
            CNF.entails_trans (shiftDownCnf_entails_add accCnf cl) hent_init
          have hinv2_F1 : FullSparseInvW c F1 F_cur st2 :=
            ingest_st3_inv hinv2 hF1_ent hlen2 rfl rfl
          refine wp_head_jnz_iff (b := taut_v) (by c0_val_eq) ?_
          refine ⟨fun htaut => ?_, fun hntaut => ?_⟩
          · p_lets
            exact ingest_ret_exit hcl_pos hi0_lt hidx hlen2 hcv rfl hcl0 rfl rfl rfl (Or.inl rfl)
              (fun _ => ⟨F_cur, hinv2_F1, hF1_ent⟩) (fun h => by cases h)
              (fun l _ hr _ => by have := (hunit_r l hr).1; rw [htaut] at this; cases this)
              (fun l _ hr _ => by have := (hunit_r l hr).1; rw [htaut] at this; cases this)
              hm2 hQ
          · have hF1_cl : F1.EntailsClause (cnfClause ((tmp'.take tlen).map BitVec.toNat)) := by
              have hcl_ent : F1.EntailsClause (cnfClause revLits.reverse) := by
                have h1 := shiftDownCnf_entails_added accCnf cl
                rwa [show shiftDownClause cl = cnfClause revLits.reverse from
                  shiftDownClause_kissatLits revLits.reverse] at h1
              refine entails_of_mem_or_false hcl_ent fun l hl => Or.inl ?_
              obtain ⟨k, hk, hget⟩ := hcov hntaut l (List.mem_reverse.mp hl)
              rw [List.mem_map]; refine ⟨tmp'[k]'(by rw [htmpl]; omega), ?_, ?_⟩
              · rw [List.mem_iff_getElem]
                exact ⟨k, by rw [List.length_take, htmpl]; omega, by rw [List.getElem_take]⟩
              · dsimp only [st_r] at hget
                rwa [List.getElem?_eq_getElem (by rw [htmpl]; omega), Option.getD_some] at hget
            p_lets
            refine wp_loop_group (ts := [i32, i32])
              (fun r3 (kp_v, iv, ()) m3 => ∃ keep i tmp'',
                r3 = tlen - i ∧ kp_v = BitVec.ofNat 32 keep ∧ iv = BitVec.ofNat 32 i ∧
                IngestPruneInv c s tmp' revLits tlen keep i tmp'' ∧
                (bytes cnf_ptr cnfBytes ⋆
                  FullMem c (st_r (cnf_ptr + BitVec.ofNat 64 idx) dval mrk'' tmp'') ⋆ R) m3)
              ?_ ?_
            · rintro L3 r3 ⟨kp_v, iv, ⟨⟩⟩ m3 ih3 ⟨keep, i, tmp'', rfl, rfl, rfl, hpi, hm3⟩
              have ⟨hk_le, hi_le3, htmp'l, htail, hkeep_un, _, _, _, hu0, hu1⟩ := hpi
              p_lets
              refine wp_head_jnz_iff (b := decide (i < tlen))
                (by simp only [Arg.val_var]; exact bv32_ult_eq (by omega) (by omega)) ?_
              rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun hilt => ?_,
                  fun hige => ?_⟩
              · p_lets
                have hm3a : (FullMem c (st_r (cnf_ptr + BitVec.ofNat 64 idx) dval mrk'' tmp'') ⋆
                    (bytes cnf_ptr cnfBytes ⋆ R)) m3 := sep_ac hm3
                rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega), bv64_mul4_nat]
                have htm_bd_i : i < (st_r (cnf_ptr + BitVec.ofNat 64 idx)
                    dval mrk'' tmp'').core.tmp.length := by dsimp [st_r]; rw [htmp'l]; omega
                refine wp_load_of (load_full_tmp (i := i) htm_bd_i hm3a) ?_; p_lets
                let li := tmp''[i]'(by rw [htmp'l]; omega)
                have hli_st : (st_r (cnf_ptr + BitVec.ofNat 64 idx)
                    dval mrk'' tmp'').core.tmp[i]'htm_bd_i = li := rfl
                rw [hli_st]
                have hli_eq : li = tmp'[i]'(by rw [htmpl]; omega) := by
                  have h1 := htail i (Nat.le_refl _) hilt
                  rw [List.getElem?_eq_getElem (by rw [htmp'l]; omega),
                    List.getElem?_eq_getElem (by rw [htmpl]; omega)] at h1; exact Option.some.inj h1
                have hli_lt : li.toNat < 2 * c.mv := by
                  have := htmp_lt i hilt; dsimp only [st_r] at this
                  rwa [List.getElem?_eq_getElem (by rw [htmpl]; omega),
                    Option.getD_some, ← hli_eq] at this
                rw [bv32_zext64_eq]
                have hv_bd_li : li.toNat < (st_r (cnf_ptr + BitVec.ofNat 64 idx)
                    dval mrk'' tmp'').core.vals.length := by
                  dsimp [st_r]; rw [hcok.vals_len]; omega
                refine wp_load_of (load_full_vals hv_bd_li hm3a) ?_; p_lets
                let lv := s.core.vals[li.toNat]'(by rw [hcok.vals_len]; omega)
                have hlv_eq : (st_r (cnf_ptr + BitVec.ofNat 64 idx)
                    dval mrk'' tmp'').core.vals[li.toNat]'hv_bd_li = lv := rfl
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
                  let st3 := st_r (cnf_ptr + BitVec.ofNat 64 idx) dval mrk'' tmp''
                  have hlen3 : st3.LengthsOk c :=
                    ⟨{ hlen2.core_ok with tmp_len_arr := htmp'l }, hlen2.scratch_ok⟩
                  have hinv3 := ingest_st3_inv hinv2 hF1_ent hlen3 rfl rfl
                  have hli_abs : ∀ l, revLits = [l] → s.core.vals[l]?.getD 0#8 = 1#8 :=
                    fun l hrev => by
                    obtain ⟨_, _, htmp0⟩ := hunit_r l hrev; dsimp only [st_r] at htmp0
                    have hi0_eq : i = 0 := by omega
                    subst hi0_eq
                    have hl_eq : li.toNat = l := by
                      rw [hli_eq]; rwa [List.getElem?_eq_getElem (by rw [htmpl]; omega),
                        Option.getD_some] at htmp0
                    rw [hl_eq] at hlv_getD; exact hlv_getD.trans hlv1
                  p_lets
                  exact ingest_ret_exit hcl_pos hi0_lt hidx hlen3 hcv rfl hcl0 rfl rfl rfl
                    (Or.inl rfl) (fun _ => ⟨F_cur, hinv3, hF1_ent⟩) (fun h => by cases h)
                    (fun l _ hr hv0 => by have h1 := hli_abs l hr; rw [h1] at hv0; cases hv0)
                    (fun l _ hr hvf => by have h1 := hli_abs l hr; rw [h1] at hvf; cases hvf)
                    hm3 hQ
                · have hlv_ne1 : lv ≠ 1#8 := fun h => by rw [hsgt.mpr h] at hnpos; cases hnpos
                  refine wp_join_group
                    (fun (kp', ()) m3' => ∃ keep' tmp''', kp' = BitVec.ofNat 32 keep' ∧
                      IngestPruneInv c s tmp' revLits tlen keep' (i + 1) tmp''' ∧
                      (bytes cnf_ptr cnfBytes ⋆
                        FullMem c (st_r (cnf_ptr + BitVec.ofNat 64 idx) dval mrk'' tmp''') ⋆ R)
                        m3')
                    (fun _ ⟨kp', ⟨⟩⟩ m3' ⟨keep', tmp''', hkp', hpi', hm3'⟩ => by
                      subst hkp'; p_lets
                      rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
                        show BitVec.ofNat 32 i + BitVec.ofNat 32 1 = BitVec.ofNat 32 (i + 1)
                          by bv_omega]
                      exact ih3 (tlen - (i + 1)) _ m3' (by omega)
                        ⟨keep', i + 1, tmp''', rfl, rfl, rfl, hpi', hm3'⟩)
                    (fun Jp hJp => by
                      p_lets; refine wp_head_jnz_iff (b := decide (lv = 0#8)) (by
                        simp only [Arg.val_var]; exact i8_vals_beq0 hlv_dom) ?_
                      rw [decide_eq_true_eq, decide_eq_false_iff_not]
                      refine ⟨fun hlv0 => ?_, fun hlvne0 => ?_⟩
                      · p_lets
                        rw [bv32_zext64_eq, bv32_ofNat_toNat (n := keep) (by omega), bv64_mul4_nat]
                        have htm_bd_kp : keep < (st_r (cnf_ptr + BitVec.ofNat 64 idx)
                            dval mrk'' tmp'').core.tmp.length := by
                          dsimp [st_r]; rw [htmp'l]; omega
                        obtain ⟨okt, hmt⟩ := store_full_tmp (i := keep) li htm_bd_kp hm3a
                        refine ⟨okt, ?_⟩; p_lets
                        rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
                          show BitVec.ofNat 32 keep + BitVec.ofNat 32 1 =
                            BitVec.ofNat 32 (keep + 1) by bv_omega]
                        exact hJp _ _ ⟨keep + 1, tmp''.set keep li, rfl,
                          ingestPruneInv_push hc_mv hilt htlen_le htmpl
                            (fun k1 k2 h1 h2 heq => htmp_nd k1 k2 h1 h2 heq)
                            hli_eq hli_lt (hlv_getD.trans hlv0) (fun l hr => (hunit_r l hr).2.2)
                            hpi, sep_ac hmt⟩
                      · have hlv_ff : lv = 0xFF#8 := by
                          rcases hlv_dom with h | h | h
                          · exact absurd h hlvne0
                          · exact absurd h hlv_ne1
                          · exact h
                        exact hJp _ m3 ⟨keep, tmp'', rfl,
                          ingestPruneInv_skip hc_mv hilt htlen_le htmpl hli_eq
                            (hlv_getD.trans hlv_ff) (fun l hr => (hunit_r l hr).2.2) hpi, hm3⟩)
              · have hieq : i = tlen := by omega
                subst i
                have hF1_keep := ingest_keep_entails hcv hw0 hcl0 htlen_le htmpl hc_mv htmp_lt
                  hF1_ent hF1_cl hpi
                let st3 := st_r (cnf_ptr + BitVec.ofNat 64 idx) dval mrk'' tmp''
                have hlen3 : st3.LengthsOk c :=
                  ⟨{ hlen2.core_ok with tmp_len_arr := htmp'l }, hlen2.scratch_ok⟩
                have hinv3 := ingest_st3_inv hinv2 hF1_ent hlen3 rfl rfl
                p_lets
                have hkeep0 : (BitVec.ofNat 32 keep == 0#32) = decide (keep = 0) := by
                  rw [show (0#32 : BitVec 32) = BitVec.ofNat 32 0 from rfl,
                    bv32_beq_nat_eq (by decide), bv32_ofNat_toNat (n := keep) (by omega)]
                refine wp_head_jnz_iff (b := decide (keep = 0))
                  (by simpa [Arg.val_var] using hkeep0) ?_
                rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun hk0 => ?_, fun _ => ?_⟩
                · subst hk0; p_lets
                  have hunsat : F1.Unsat := unsat_of_entails_nil (by simpa using hF1_keep)
                  exact ingest_ret_exit hcl_pos hi0_lt hidx hlen3 hcv rfl hcl0 rfl rfl rfl
                    (Or.inr (Or.inl rfl)) (fun h => by cases h) (fun _ => hunsat)
                    (fun l hl hr hv0 => by
                      have ⟨_, ht1, _⟩ := hunit_r l hr; have ⟨h1, _⟩ := hu0 l hl hr hv0 ht1; omega)
                    (fun _ _ _ _ => rfl) hm3 hQ
                · p_lets
                  have hkeep1 : (BitVec.ofNat 32 keep == 1#32) = decide (keep = 1) := by
                    rw [show (1#32 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
                      bv32_beq_nat_eq (by decide), bv32_ofNat_toNat (n := keep) (by omega)]
                  refine wp_head_jnz_iff (b := decide (keep = 1))
                    (by simpa [Arg.val_var] using hkeep1) ?_
                  rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun hk1 => ?_,
                      fun _ => ?_⟩
                  · subst hk1; p_lets
                    have hm3a : (FullMem c st3 ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m3 := sep_ac hm3
                    have htm_bd0 : 0 < st3.core.tmp.length := by
                      dsimp [st3, st_r]; rw [htmp'l]; omega
                    refine wp_load_of (load_full_tmp (i := 0) htm_bd0 hm3a) ?_; p_lets
                    let l0 := tmp''[0]'(by rw [htmp'l]; omega)
                    have hl0_st : st3.core.tmp[0]'htm_bd0 = l0 := rfl
                    rw [hl0_st]
                    have ⟨hl0_lt, hl0_un⟩ := hkeep_un 0 (by decide)
                    rw [List.getElem?_eq_getElem (i := 0) (by rw [htmp'l]; omega),
                      Option.getD_some] at hl0_lt hl0_un
                    have hl0_lt' : l0.toNat < 2 * c.mv := hl0_lt
                    have hl0_ent : F1.EntailsClause (cnfClause [l0.toNat]) := by
                      have htk : tmp''.take 1 = [l0] := by
                        cases tmp'' with
                        | nil => simp at htmp'l; omega
                        | cons _ _ => rfl
                      simpa [htk] using hF1_keep
                    let F_next := [l0.toNat] :: F_cur
                    have hFn_ent : F1.Entails (cnfOfClauses F_next) :=
                      entails_cnfOfClauses_cons hF1_ent hl0_ent
                    have hext_n : ExtUnsatSound F1 st3.core.cur_vars F_next :=
                      extUnsatSound_of_entails
                        (varsBounded_cons (fun q hq => by
                          simp only [List.mem_singleton] at hq; rw [hq, hcv]; exact hl0_lt')
                          hinv3.2.1.ext_sound.1) hFn_ent
                    have hw3_n : FullWitnessInv c F1 F_next st3.core :=
                      hinv3.2.1.replace_extSound hext_n (cnfOfClauses_cons_entails _ _)
                    apply wp_call_of_spec; apply hAssign
                    dsimp only [fullAssignLvlSpec, vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
                    refine ⟨c, st3, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen3, hm3a, ?_⟩
                    have hte_lt := hw3_n.trail_end_lt_of_unassigned (by rw [hcv]; exact hl0_lt')
                      hl0_un
                    have hte_mv : st3.core.trail_end < c.max_vars :=
                      Nat.lt_of_lt_of_le hte_lt (by rw [hcv]; exact hc_mv)
                    have hguard_f : ¬ (st3.core.cur_vars ≤ l0.toNat / 2 ∨
                        c.max_vars ≤ st3.core.trail_end ∨
                        st3.core.vals[l0.toNat]?.getD 0#8 ≠ 0#8) := by
                      rw [hcv]; refine not_or.mpr ⟨by omega, not_or.mpr ⟨by omega, ?_⟩⟩
                      change ¬ (s.core.vals[l0.toNat]?.getD 0#8 ≠ 0#8)
                      exact fun h => h hl0_un
                    rw [ite_eq_right hguard_f]
                    intro flags' unass' phases' m4 hfl' hph' hlen_sf hm4; p_lets
                    have h_alvl : ((0 : BitVec 32) = 0#32) = True := eq_true rfl
                    simp only [h_alvl, ↓reduceIte] at hlen_sf hm4
                    let sf : FullState :=
                      { st3 with
                        core :=
                          { st3.core with
                            vals := (st3.core.vals.set l0.toNat 1#8).set (l0.toNat ^^^ 1) 0xFF#8
                            flags := flags', lvl := st3.core.lvl.set (l0.toNat / 2) 0#32
                            rsns := st3.core.rsns.set (l0.toNat / 2) 0xFFFFFFFF#32
                            trl := st3.core.trl.set st3.core.trail_end l0
                            trail_pos := st3.core.trail_pos.set (l0.toNat / 2)
                              (BitVec.ofNat 32 st3.core.trail_end)
                            trail_end := st3.core.trail_end + 1
                            unassigned := unass', unflushed := st3.core.unflushed + 1#64 }
                        scratch := { st3.scratch with phases := phases' } }
                    have hw_sf : FullWitnessInv c F1 F_next sf.core :=
                      addUnit_preserves_witness hlen3.core_ok hw3_n hcl0 hfl'
                        (unassigned' := unass') (unflushed' := st3.core.unflushed + 1#64)
                        (by rw [hcv]; exact hl0_lt') hl0_un (cnfOfClauses_cons_entails_head _ _)
                    have hinv_sf : FullSparseInvW c F1 F_next sf :=
                      ⟨hlen_sf, hw_sf, hinv3.2.2.1, hinv3.2.2.2.1, hinv3.2.2.2.2.1,
                        hinv3.2.2.2.2.2⟩
                    exact hQ 1#64 sf idx m4 hcl_pos hi0_lt hidx rfl hlen_sf hcv rfl hcl0 rfl rfl
                      rfl (Or.inl rfl) (fun _ => ⟨F_next, hinv_sf, hFn_ent⟩)
                      (fun h => by cases h) (fun l hl hcleq hv0 => by
                        have hrev := fullIngest_unit_rev hcleq
                        have ⟨_, ht1, _⟩ := hunit_r l hrev
                        have ⟨_, hl0eq⟩ := hu0 l hl hrev hv0 ht1
                        rw [List.getElem?_eq_getElem (i := 0) (by rw [htmp'l]; omega),
                          Option.getD_some] at hl0eq
                        have hl0eq' : l0.toNat = l := hl0eq
                        refine ⟨rfl, fun kk hkk => ?_, rfl, rfl⟩
                        change ((st3.core.vals.set l0.toNat 1#8).set
                          (l0.toNat ^^^ 1) 0xFF#8)[kk]?.getD 0#8 =
                          ((s.core.vals.set l 1#8).set (l ^^^ 1) 0xFF#8)[kk]?.getD 0#8
                        rw [hl0eq'])
                      (fun l hl hcleq hvf => by
                        have hrev := fullIngest_unit_rev hcleq
                        have ⟨_, ht1, _⟩ := hunit_r l hrev
                        have := hu1 l hl hrev hvf ht1; omega)
                      (sep_ac hm4)
                  · have hkp_ge2 : 2 ≤ keep := by omega
                    have hkp_le_mv : keep ≤ c.max_vars := Nat.le_trans hk_le (by omega)
                    have hm3a : (FullMem c st3 ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m3 := sep_ac hm3
                    let clLits := (tmp''.take keep).map BitVec.toNat
                    have hlits_bd : ∀ l ∈ clLits, l < 2 * c.mv := by
                      intro l hl; rw [List.mem_map] at hl; obtain ⟨x, hx, rfl⟩ := hl
                      rw [List.mem_iff_getElem] at hx; obtain ⟨k, hk, hxk⟩ := hx
                      rw [List.length_take] at hk; rw [List.getElem_take] at hxk
                      have hlt := (hkeep_un k (by omega)).1
                      rwa [List.getElem?_eq_getElem (by rw [htmp'l]; omega),
                        Option.getD_some, hxk] at hlt
                    have hcl_nd : ((tmp''.take keep).map fun x => x.toNat / 2).Nodup :=
                      nodup_of_pairwise_div2
                        (by rw [htmp'l]; exact Nat.le_trans hk_le (Nat.le_trans htlen_le hc_mv))
                        hpi.2.2.2.2.2.2.1
                    let F_next := clLits :: F_cur
                    have hFn_ent : F1.Entails (cnfOfClauses F_next) :=
                      entails_cnfOfClauses_cons hF1_ent hF1_keep
                    have hext_n : ExtUnsatSound F1 st3.core.cur_vars F_next :=
                      extUnsatSound_of_entails
                        (varsBounded_cons (fun l hl => by rw [hcv]; exact hlits_bd l hl)
                          hinv3.2.1.ext_sound.1) hFn_ent
                    have hw3_n : FullWitnessInv c F1 F_next st3.core :=
                      hinv3.2.1.replace_extSound hext_n (cnfOfClauses_cons_entails _ _)
                    have hq_ret : ∀ (r_out : BitVec 64) (sf : FullState) m4
                        (hdom : r_out = 1#64 ∨ r_out = 3#64) (hlens : sf.LengthsOk c)
                        (hcv_f : sf.core.cur_vars = c.mv)
                        (hd : sf.core.d_cur = cnf_ptr + BitVec.ofNat 64 idx)
                        (hcl : sf.core.cur_level = 0)
                        (hfu : sf.core.fuel = s.core.fuel) (hoom : sf.core.oom = s.core.oom)
                        (hpr : sf.core.probing = s.core.probing)
                        (hi1 : r_out = 1#64 → ∃ F_cur', FullSparseInvW c F1 F_cur' sf ∧
                          F1.Entails (cnfOfClauses F_cur'))
                        (hm4 : (FullMem c sf ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m4),
                        Q (r_out, ()) m4 :=
                      fun r_out sf m4 hdom hlens hcv_f hd hcl hfu hoom hpr hi1 hm4 =>
                        ingest_ret_exit hcl_pos hi0_lt hidx hlens hcv_f hd hcl hfu hoom hpr
                          (hdom.elim Or.inl (fun h => Or.inr (Or.inr h))) hi1
                          (fun h => by rcases hdom with rfl | rfl <;> cases h)
                          (fun l hl hr hv0 => by
                            have ⟨_, ht1, _⟩ := hunit_r l hr
                            have ⟨h1, _⟩ := hu0 l hl hr hv0 ht1; omega)
                          (fun l hl hr hvf => by
                            have ⟨_, ht1, _⟩ := hunit_r l hr; have := hu1 l hl hr hvf ht1; omega)
                          (sep_ac hm4) hQ
                    apply wp_call_of_spec; apply hAddCl
                    dsimp only [fullAddClauseSpec, vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
                    refine ⟨c, F1, F_next, st3, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen3, hw3_n,
                      hinv3.2.2.2.2.2, by rw [bv32_ofNat_toNat (by omega)]; exact hkp_le_mv,
                      (fun _ => by
                        rw [bv32_ofNat_toNat (by omega)]
                        refine ⟨fun l hl => by rw [hcv]; exact hlits_bd l hl, hcl_nd, ?_⟩
                        exact cnfOfClauses_cons_entails_head clLits F_cur),
                      hm3a, ?_⟩
                    simp only [bv32_ofNat_toNat (n := keep) (by omega),
                      show ¬ (keep < 2) by omega, ↓reduceIte]
                    by_cases hkp2 : keep = 2
                    · simp only [hkp2, ↓reduceIte]
                      intro cid wvec' wstk' wlen' wu' nb' wsort' m4 hr_dom hlen4 hw4 hm4
                      let sf : FullState := { st3 with
                        core := { st3.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                                wusable := wu', num_binary := nb' }
                        scratch := { st3.scratch with wsort := wsort' } }
                      have hinv4 : FullSparseInvW c F1 F_next sf :=
                        ⟨hlen4, hw4, hinv3.2.2.1, hinv3.2.2.2.1, hinv3.2.2.2.2.1, hinv3.2.2.2.2.2⟩
                      p_lets; refine wp_head_jnz_iff (b := decide (cid = 0xFFFFFFFF#64))
                        (by simp only [Arg.val_var]; exact bv64_beq_eq) ?_
                      rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun _ => ?_,
                          fun _ => ?_⟩
                      · p_lets; exact hq_ret 3#64 sf m4 (Or.inr rfl) hlen4 hcv rfl hcl0 rfl rfl rfl
                          (fun h => by cases h) hm4
                      · p_lets; exact hq_ret 1#64 sf m4 (Or.inl rfl) hlen4 hcv rfl hcl0 rfl rfl rfl
                          (fun _ => ⟨F_next, hinv4, hFn_ent⟩) hm4
                    · simp only [hkp2, ↓reduceIte]
                      intro cid arena' alen' wvec' wstk' wlen' wu' fred' ni' nr' wsort' m4
                        hr_dom hlen4 hw4 hsub4 hnd4 _ hm4
                      let sf : FullState := { st3 with
                        core := { st3.core with arena := arena', arena_len := alen', wvec := wvec',
                                                wstk := wstk', wlen := wlen', wusable := wu',
                                                first_reducible := fred', num_irred := ni',
                                                num_redundant := nr' }
                        scratch := { st3.scratch with wsort := wsort' } }
                      have hinv4 : FullSparseInvW c F1 F_next sf :=
                        ⟨hlen4, hw4, hinv3.2.2.1, hnd4 hinv3.2.2.2.1,
                          ⟨hinv3.2.2.2.2.1.1.of_refs_subset rfl hsub4, hinv3.2.2.2.2.1.2⟩,
                          hinv3.2.2.2.2.2⟩
                      p_lets; refine wp_head_jnz_iff (b := decide (cid = 0xFFFFFFFF#64))
                        (by simp only [Arg.val_var]; exact bv64_beq_eq) ?_
                      rw [decide_eq_true_eq, decide_eq_false_iff_not]
                      refine ⟨fun _ => ?_, fun _ => ?_⟩
                      · p_lets; exact hq_ret 3#64 sf m4 (Or.inr rfl) hlen4 hcv rfl hcl0 rfl rfl rfl
                          (fun h => by cases h) hm4
                      · p_lets; exact hq_ret 1#64 sf m4 (Or.inl rfl) hlen4 hcv rfl hcl0 rfl rfl rfl
                          (fun _ => ⟨F_next, hinv4, hFn_ent⟩) hm4
            · intro L3 hL3; p_lets
              exact hL3 tlen _ m2
                ⟨0, 0, tmp', by simp, rfl, rfl,
                  ⟨Nat.le_refl _, Nat.zero_le _, htmpl, fun _ _ _ => rfl,
                    fun _ h => by omega, fun _ h => by omega, fun _ _ h => by omega,
                    fun _ h => by omega, fun _ _ _ _ h => by omega, fun _ _ _ _ h => by omega⟩, hm2⟩
    · intro L2 hL2; p_lets
      exact hL2 tlen _ mb
        ⟨0, mrk', Nat.zero_le _, by simp, rfl, hmkl,
          fun v hv hmiss => hmrk_zero v hv (fun j hj => hmiss j (Nat.zero_le _) hj), hmb⟩
  · rintro B1 L1 r ⟨tlen_v, taut_v, ⟨⟩⟩ ml hB1 ih1
      ⟨idx, tlen, revLits, mrk', tmp', dval, rfl, rfl, hri, hpc_inv, hml⟩
    let st := st_r (cnf_ptr + BitVec.ofNat 64 idx) dval mrk' tmp'
    obtain ⟨hi_le, hidx, htlen_le, hmkl, htmpl, htmp_lt, htmp_nd,
      hmrk_zero, hmrk_pos, hcov, hsub_rev, hnil_taut, hunit_r⟩ := hri
    p_lets
    refine wp_head_jnz_iff (b := true) (by c0_val_eq) ?_
    refine ⟨fun _ => ?_, fun h => (by cases h)⟩
    p_lets
    have hml_d : (bytes cnf_ptr cnfBytes ⋆
        dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
          (cnf_ptr + BitVec.ofNat 64 idx) dval ⋆ (FullRest c st ⋆ R)) ml := by
      have h1 := focus_dimacs (sep_ac hml : (FullMem c st ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) ml)
      exact sep_ac h1
    apply wp_call_of_spec; apply hLit
    change kissatNextLitSpec (cnf_ptr + BitVec.ofNat 64 cnfBytes.length, c.hdr, ()) ml _ _
    refine ⟨cnf_ptr, BitVec.ofNat 64 c.nc, dval, c.mv, cnfBytes, idx, FullRest c st ⋆ R,
      rfl, hfit, by omega, hidx, hml_d, ?_⟩
    cases hnl : nextLitPure c.mv (cnfBytes.drop idx) with
    | err =>
      intro cur' val' m' hm'; p_lets; refine wp_head_jnz_iff (by c0_val_eq) ?_
      refine ⟨fun _ => ?_, fun h => (by cases h)⟩
      let st_d := { st with core := { st.core with d_cur := cur', d_val := val' } }
      have hm'_a : (bytes cnf_ptr cnfBytes ⋆ FullMem c st_d ⋆ R) m' :=
        sep_ac (unfocus_dimacs (R := bytes cnf_ptr cnfBytes ⋆ R) (sep_ac hm'))
      p_lets
      exact hB1 (BitVec.ofNat 32 tlen, taut_v, true, ()) m'
        ⟨idx, tlen, revLits, mrk', tmp', cur', val', rfl,
          ⟨hi_le, hidx, htlen_le, hmkl, htmpl, htmp_lt, htmp_nd,
            hmrk_zero, hmrk_pos, hcov, hsub_rev, hnil_taut, hunit_r⟩,
          fun _ => by rw [← hpc_inv, parseClauseAux_eq_nextLitPure, hnl],
          (fun hc => by cases hc), hm'_a⟩
    | endClause rest =>
      intro j m' hij hj hdrop hm'; p_lets; refine wp_head_jnz_iff (by c0_val_eq) ?_
      refine ⟨fun h => (by cases h), fun _ => ?_⟩
      p_lets; refine wp_head_jnz_iff (by c0_val_eq) ?_
      refine ⟨fun _ => ?_, fun h => (by cases h)⟩
      let st_d := { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j,
                                                   d_val := 0#64 } }
      have hm'_a : (bytes cnf_ptr cnfBytes ⋆ FullMem c st_d ⋆ R) m' :=
        sep_ac (unfocus_dimacs (R := bytes cnf_ptr cnfBytes ⋆ R) (sep_ac hm'))
      p_lets
      refine hB1 (BitVec.ofNat 32 tlen, taut_v, false, ()) m'
        ⟨j, tlen, revLits, mrk', tmp', cnf_ptr + BitVec.ofNat 64 j, 0#64, rfl,
          ⟨by omega, hj, htlen_le, hmkl, htmpl, htmp_lt, htmp_nd,
            hmrk_zero, hmrk_pos, hcov, hsub_rev, hnil_taut, hunit_r⟩,
          (fun hc => by cases hc),
          fun _ => ⟨by omega, rfl, by
            rw [← hpc_inv, parseClauseAux_eq_nextLitPure, hnl, List.map_reverse, hdrop]⟩,
          hm'_a⟩
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
      rw [bv32_zext64_eq, bv32_lshr1, bv32_ofNat_toNat hl32]
      have hmkl_d : l / 2 < st_d.core.mrk.length := by
        dsimp [st_d, st, st_r]; rw [hmkl]; omega
      refine wp_load_of (load_full_mrk hmkl_d hm'_a) ?_; p_lets
      let mv_b := mrk'[l / 2]'(by rw [hmkl]; omega)
      have hmv_b_eq : st_d.core.mrk[l / 2]'hmkl_d = mv_b := rfl
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
          ∃ tlen' mrk_n tmp_n, tl' = BitVec.ofNat 32 tlen' ∧
            let st_n := st_r (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 l) mrk_n tmp_n
            IngestReadInv c cnfBytes i0 j tlen' taut' (l :: revLits) st_n ∧
            (bytes cnf_ptr cnfBytes ⋆ FullMem c st_n ⋆ R) m_s)
        (fun _ ⟨tl', taut', _err', ⟨⟩⟩ m_s ⟨tlen', mrk_n, tmp_n, htl', hinv_n, hm_n⟩ => by
          subst htl'; p_lets
          exact ih1 (cnfBytes.length - j) _ m_s (by omega)
            ⟨j, tlen', l :: revLits, mrk_n, tmp_n, BitVec.ofNat 64 l, rfl, rfl,
              hinv_n, hpc_next, hm_n⟩)
        (fun Js hJs => by
          p_lets; rw [wp_jnz]
          simp only [Arg.val_var, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, bv8_zext32_eq_zero]
          refine ⟨fun hm0 => ?_, fun hmne0 => ?_⟩
          · have hm0' : mrk'[l / 2]'(by rw [hmkl]; omega) = 0#8 := hm0
            have hmiss_v : ∀ k < tlen, (tmp'[k]?.getD 0#32).toNat / 2 ≠ l / 2 := by
              intro k hk heq
              have hpos := hmrk_pos k hk
              dsimp only [st_r] at heq hpos
              rw [heq, List.getElem?_eq_getElem (by rw [hmkl]; omega),
                Option.getD_some, hm0'] at hpos
              have h1 := congrArg BitVec.toNat hpos
              simp only [BitVec.toNat_ofNat] at h1; omega
            have htlen_lt : tlen < c.mv :=
              inj_lt_of_missing (fun k => (tmp'[k]?.getD 0#32).toNat / 2)
                htmp_nd (fun k hk => by
                  have := htmp_lt k hk; dsimp only [st_r] at this; omega)
                hv_lt hmiss_v
            p_lets; refine wp_load_of (load_full_mv hm'_a) ?_; p_lets
            rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega)]
            have hgd_t : (BitVec.ofNat 64 c.mv).ule (BitVec.ofNat 64 tlen) =
                decide (c.mv ≤ tlen) := bv_ule_eq (by omega) (by omega)
            refine wp_head_jnz_iff (b := false)
              (by simp only [Arg.val_var, hgd_t]; simp [htlen_lt]) ?_
            refine ⟨fun h => (by cases h), fun _ => ?_⟩
            p_lets
            rw [bv32_zext64_eq, bv32_lshr1, bv32_ofNat_toNat hl32, bv32_ptag_ofNat hl32]
            have hmkl_d2 : l / 2 < st_d.core.mrk.length := hmkl_d
            obtain ⟨okm, hmm⟩ := store_full_mrk (i := l / 2) (BitVec.ofNat 8 (l % 2 + 1))
              hmkl_d2 hm'_a
            refine ⟨okm, ?_⟩; p_lets
            rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega), bv64_mul4_nat]
            have htmpl_d : tlen < ({ st_d with core := { st_d.core with
                mrk := st_d.core.mrk.set (l / 2) (BitVec.ofNat 8 (l % 2 + 1)) } }).core.tmp.length
                := by dsimp [st_d, st, st_r]; rw [htmpl]; omega
            obtain ⟨okt, hmt⟩ := store_full_tmp (i := tlen) (BitVec.ofNat 32 l) htmpl_d hmm
            refine ⟨okt, ?_⟩; p_lets
            rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
              show BitVec.ofNat 32 tlen + BitVec.ofNat 32 1 =
                BitVec.ofNat 32 (tlen + 1) by bv_omega]
            let mrk_n := mrk'.set (l / 2) (BitVec.ofNat 8 (l % 2 + 1))
            let tmp_n := tmp'.set tlen (BitVec.ofNat 32 l)
            have heq_st : ({ st_d with core := { st_d.core with
                mrk := st_d.core.mrk.set (l / 2) (BitVec.ofNat 8 (l % 2 + 1)),
                tmp := st_d.core.tmp.set tlen (BitVec.ofNat 32 l) } } : FullState) =
                st_r (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 l) mrk_n tmp_n := rfl
            rw [heq_st] at hmt
            exact hJs _ _ ⟨tlen + 1, mrk_n, tmp_n, rfl,
              ingestReadInv_push (cnf_ptr := cnf_ptr) hc_mv (by omega) hj htlen_lt hmkl htmpl
                hl_mv hl32 hv_lt hmiss_v
                ⟨hi_le, hidx, htlen_le, hmkl, htmpl, htmp_lt, htmp_nd, hmrk_zero, hmrk_pos,
                  hcov, hsub_rev, hnil_taut, hunit_r⟩,
              sep_ac hmt⟩
          · have hex : ∃ k0 < tlen, (tmp'[k0]?.getD 0#32).toNat / 2 = l / 2 := by
              by_cases h : ∃ k0 < tlen, (tmp'[k0]?.getD 0#32).toNat / 2 = l / 2
              · exact h
              · exfalso
                have h0 := hmrk_zero (l / 2) (by omega) (fun k hk heq => by
                  dsimp only [st_r] at heq; exact h ⟨k, hk, heq⟩)
                dsimp only [st_r] at h0
                rw [List.getElem?_eq_getElem (by rw [hmkl]; omega),
                  Option.getD_some] at h0; exact hmne0 h0
            obtain ⟨k0, hk0, hk0_v⟩ := hex
            have hmv_pos := hmrk_pos k0 hk0
            dsimp only [st_r] at hmv_pos
            rw [hk0_v, List.getElem?_eq_getElem (by rw [hmkl]; omega),
              Option.getD_some] at hmv_pos
            refine wp_join_group
              (fun (taut', ()) m_j =>
                (taut' = if mv_b = BitVec.ofNat 8 (l % 2 + 1) then taut_v else true) ∧ m_j = m')
              (fun _ ⟨taut', ⟨⟩⟩ m_j ⟨htaut', hm_j⟩ => by
                subst m_j; p_lets
                refine hJs _ m' ⟨tlen, mrk', tmp', rfl,
                    ⟨by omega, hj, htlen_le, hmkl, htmpl, htmp_lt, htmp_nd, hmrk_zero, hmrk_pos,
                      ingest_dup_cov (by rw [hmkl]; exact hc_mv) hv_lt hk0 htaut' rfl hmv_pos hcov
                        hk0_v,
                      (fun k hk => List.mem_cons_of_mem _ (hsub_rev k hk)), (fun hc => by cases hc),
                      fun l' hl' => by
                        rcases List.cons.inj hl' with ⟨_, rfl⟩
                        dsimp only [st_r] at hsub_rev; exact absurd (hsub_rev k0 hk0) (by simp)⟩,
                    sep_ac hm'_a⟩)
              (fun Jt hJt => by
                p_lets; rw [wp_jnz]
                simp only [Arg.val_var, bv32_ptag_ofNat hl32, bv8_zext32_bne,
                  decide_eq_true_eq, decide_eq_false_iff_not, Classical.not_not]
                refine ⟨fun hne => hJt (true, ()) m' ⟨by simp [hne], rfl⟩,
                  fun heq => hJt (taut_v, ()) m' ⟨by simp [heq], rfl⟩⟩))
  · intro B1 L1 _ hL1; p_lets
    exact hL1 (cnfBytes.length - i0) _ m
      ⟨i0, 0, [], s.core.mrk, s.core.tmp, s.core.d_val, rfl, rfl,
        ⟨Nat.le_refl _, hi0, Nat.zero_le _, hcok.mrk_len, hcok.tmp_len_arr,
          fun _ h => by omega, fun _ _ h => by omega,
          fun v hv _ => hinv.2.2.1.1 v hv, fun _ h => by omega,
          (fun _ _ h => by cases h), (fun _ h => by omega), (fun _ => rfl),
          (fun _ h => by cases h)⟩,
        by unfold parseClause; simp, by rw [hst0]; exact hm⟩

end IngestClProof

end LeanQbe.T.Examples.Kissat.Full
