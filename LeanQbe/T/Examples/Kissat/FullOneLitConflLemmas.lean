module

public import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas3
public import LeanQbe.T.Examples.Kissat.FullSpec
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Chronological One-Literal Conflict (`full_one_lit_confl`)

Proves:
1. `chronoAssign_preserves_fullWitness_sameLvl` and `full_one_lit_confl_wp` directly against
   canonical `FullSpec2.fullOneLitConflSpec` and canonical `FullSpec2` callee contracts.
2. Index-verified `SpecEntry.Impl fullEnv` bridge (`full_one_lit_confl_mk_ok`,
   `full_one_lit_confl_bridge_wp` at `fullFns[78]?` / `fullSpecTable[78]?`).
3. Concrete `Mem 64` UNSAT non-vacuity (`nv_full_one_lit_confl`, `XPost := fun _ _ _ _ => False`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.C0Step
open Kraken.Bedrock2.Test

open FullAnalyzeTactics FullAnalyzeHelpers
open scoped FullArenaTactics FullAnalyzeTactics

/-! ## 0. Canonical `FullWitnessCutInv` / `FullOtfsWitnessInv` adapters -/

private theorem canonCut_to_fa {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k) :
    FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut k :=
  { ext_sound := h.ext_sound, inconsistent_sound := h.inconsistent_sound
    arena := h.arena, watches := h.watches, cur_level_le := h.cur_level_le
    trail_lits_lt := h.trail_lits_lt, trail_vars_nodup := h.trail_vars_nodup
    vals_domain := h.vals_domain, vals_true_iff := h.vals_true_iff
    vals_false_iff := h.vals_false_iff, lvl_le := h.lvl_le, dec_earliest := h.dec_earliest
    levels_inhabited := h.levels_inhabited, level0_sound := h.level0_sound
    trail_pos_inv := h.trail_pos_inv, level0_rsn_none := h.level0_rsn_none
    frame_trail_lt := h.frame_trail_lt, frame_trail_mono := h.frame_trail_mono
    frame_trail_before_lt := h.frame_trail_before_lt, frame_dec_lt := h.frame_dec_lt
    reason_inv := fun idx hidx hc hne =>
      hc.elim (fun h1 => h.reason_inv_cut idx h1 hne)
        (fun h2 => h.reason_inv_below idx hidx h2 hne)
    reason_lit_mem := fun idx hidx hc hne hlg =>
      hc.elim (fun h1 => h.reason_lit_mem_cut idx h1 hne hlg)
        (fun h2 => h.reason_lit_mem_below idx hidx h2 hne hlg) }

private theorem faCut_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hcut : cut ≤ k.trail_end)
    (h : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut k) :
    FullWitnessCutInv c F0 F_cur cut k :=
  { ext_sound := h.ext_sound, inconsistent_sound := h.inconsistent_sound
    arena := h.arena, watches := h.watches, cur_level_le := h.cur_level_le
    trail_lits_lt := h.trail_lits_lt, trail_vars_nodup := h.trail_vars_nodup
    vals_domain := h.vals_domain, vals_true_iff := h.vals_true_iff
    vals_false_iff := h.vals_false_iff, lvl_le := h.lvl_le, dec_earliest := h.dec_earliest
    levels_inhabited := h.levels_inhabited, level0_sound := h.level0_sound
    trail_pos_inv := h.trail_pos_inv, level0_rsn_none := h.level0_rsn_none
    frame_trail_lt := h.frame_trail_lt, frame_trail_mono := h.frame_trail_mono
    frame_trail_before_lt := h.frame_trail_before_lt, frame_dec_lt := h.frame_dec_lt
    reason_inv_below := fun idx hidx hlt hne => h.reason_inv idx hidx (Or.inr hlt) hne
    reason_lit_mem_below := fun idx hidx hlt hne hlg =>
      h.reason_lit_mem idx hidx (Or.inr hlt) hne hlg
    cut_le := hcut
    reason_inv_cut := fun idx hi hne =>
      h.reason_inv idx (Nat.lt_of_lt_of_le hi hcut) (Or.inl hi) hne
    reason_lit_mem_cut := fun idx hi hne hlg =>
      h.reason_lit_mem idx (Nat.lt_of_lt_of_le hi hcut) (Or.inl hi) hne hlg }

private theorem cutInv_with_watches {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k)
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wu' : BitVec 64}
    (hw : ModeWatchesInv F_cur
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }) :
    FullWitnessCutInv c F0 F_cur cut
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } :=
  { h with arena := { h.arena with len_ok := h.arena.len_ok }, watches := hw }

private theorem otfsInv_with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullOtfsWitnessInv c F0 F_cur k) (oom' : BitVec 64) :
    FullOtfsWitnessInv c F0 F_cur { k with oom := oom' } :=
  { h with
    arena := { h.arena with len_ok := h.arena.len_ok }
    watches := h.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr }

/-! ## 1. Fixed-`F_cur` chronological unit-assignment & backtrack helpers -/

private theorem chronoAssign_preserves_fullWitness_sameLvl {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) {lit rsn : BitVec 32} {alvl : Nat}
    {flags' : List (BitVec 32)} {unassigned' unflushed' : BitVec 64}
    (hlit : lit.toNat < 2 * s.core.cur_vars) (hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    (halvl_le : alvl ≤ s.core.cur_level) (hrsn_ne_ff : rsn ≠ 0xFFFFFFFF#32)
    (hl0 : alvl = 0 → (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hrsn : 0 < alvl →
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * s.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, ot]) ∧
        ∃ m < s.core.trail_end, (s.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
          (s.core.lvl[ot / 2]?.getD 0#32).toNat ≤ alvl
      else
        rsn.toNat ∈ fullArenaClauseRefsCore s.core ∧
        fullArenaClauseGarbCore s.core rsn.toNat = false ∧
        ∀ q ∈ fullArenaClauseLitsCore s.core rsn.toNat,
          q = lit.toNat ∨ ∃ m < s.core.trail_end, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
            (s.core.lvl[q / 2]?.getD 0#32).toNat ≤ alvl)
    (hrsn_mem : 0 < alvl → (rsn &&& 0x80000000#32) = 0#32 →
      lit.toNat ∈ fullArenaClauseLitsCore s.core rsn.toNat) :
    let v := lit.toNat / 2
    let rsn' := if alvl = 0 then 0xFFFFFFFF#32 else rsn
    FullWitnessInv c F0 F_cur
      { s.core with
        vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        flags := flags', lvl := s.core.lvl.set v (BitVec.ofNat 32 alvl)
        rsns := s.core.rsns.set v rsn', trl := s.core.trl.set s.core.trail_end lit
        trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
        trail_end := s.core.trail_end + 1
        unassigned := unassigned', unflushed := unflushed' } := by
  intro v rsn'
  let k' : FullCoreState :=
    { s.core with
      vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
      flags := flags', lvl := s.core.lvl.set v (BitVec.ofNat 32 alvl)
      rsns := s.core.rsns.set v rsn', trl := s.core.trl.set s.core.trail_end lit
      trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
      trail_end := s.core.trail_end + 1, unassigned := unassigned', unflushed := unflushed' }
  have hcl := hlen.core_ok
  have hte_lt : s.core.trail_end < s.core.cur_vars := hw.trail_end_lt_of_unassigned hlit hun
  have hnot_var : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hw.vals_zero_iff hlit).mp hun
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hv_lt : v < c.max_vars := by have := hcl.cur_vars_le; omega
  have hte_max : s.core.trail_end < c.max_vars := by have := hcl.cur_vars_le; omega
  have halvl_lt32 : alvl < 2 ^ 32 := by
    have := fullInv_max_vars_lt32 c; have := hw.cur_level_le; have := hcl.cur_vars_le; omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by have := fullInv_max_vars_lt32 c; omega
  have htrl_get : ∀ i < s.core.trail_end + 1, (k'.trl[i]?.getD 0#32).toNat =
      if i = s.core.trail_end then lit.toNat else (s.core.trl[i]?.getD 0#32).toNat := fun i _ => by
    by_cases he : i = s.core.trail_end
    · subst he; simp [k', List.getElem?_set_self (by rw [hcl.trl_len]; exact hte_max)]
    · simp [k', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_get : ∀ w < s.core.cur_vars, (k'.lvl[w]?.getD 0#32).toNat =
      if w = v then alvl else (s.core.lvl[w]?.getD 0#32).toNat := fun w _ => by
    by_cases he : w = v
    · subst he; simp [k', List.getElem?_set_self (by rw [hcl.lvl_len]; exact hv_lt),
        bv32_ofNat_toNat halvl_lt32]
    · simp [k', he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * s.core.cur_vars, k'.vals[l]?.getD 0#8 =
      if l = lit.toNat ^^^ 1 then 0xFF#8 else if l = lit.toNat then 1#8
      else s.core.vals[l]?.getD 0#8 := fun l hl => by
    have hcm := hcl.cur_vars_le
    by_cases h1 : l = lit.toNat ^^^ 1
    · subst h1; simp only [k', ↓reduceIte]
      rw [List.getElem?_set_self (by simp [hcl.vals_len]; omega)]; rfl
    · simp only [k', h1, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = lit.toNat
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hcl.vals_len]; omega)]; rfl
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  have hrsn_get : ∀ w < s.core.cur_vars, k'.rsns[w]?.getD 0xFFFFFFFF#32 =
      if w = v then rsn' else s.core.rsns[w]?.getD 0xFFFFFFFF#32 := fun w _ => by
    by_cases he : w = v
    · subst he; simp [k', List.getElem?_set_self (by rw [hcl.rsns_len]; exact hv_lt)]
    · simp [k', he, List.getElem?_set_ne (Ne.symm he)]
  have hlt_w : ∀ i, i < s.core.trail_end → (s.core.trl[i]?.getD 0#32).toNat / 2 < s.core.cur_vars :=
    fun i hi => by have := hw.trail_lits_lt i hi; omega
  have hlift_rsn : ∀ {up p0 : Nat} {rv : BitVec 32} {p_lvl : Nat}, up ≤ s.core.trail_end →
      (rv &&& 0x80000000#32) ≠ 0#32 → p0 / 2 < s.core.cur_vars →
      (k'.lvl[p0 / 2]?.getD 0#32).toNat = p_lvl →
      ((let ot := (rv &&& 0x7FFFFFFF#32).toNat
        ot < 2 * s.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [p0, ot]) ∧
        ∃ m < up, (s.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
          (s.core.lvl[ot / 2]?.getD 0#32).toNat ≤ p_lvl) →
      let ot := (rv &&& 0x7FFFFFFF#32).toNat
      ot < 2 * k'.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [p0, ot]) ∧
      ∃ m < up, (k'.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
        (k'.lvl[ot / 2]?.getD 0#32).toNat ≤ (k'.lvl[p0 / 2]?.getD 0#32).toNat) := by
    rintro up p0 rv p_lvl hup _ _ hpl ⟨hlt, hent, m, hm, hmeq, hlvl_le⟩
    have hm' : m < s.core.trail_end := Nat.lt_of_lt_of_le hm hup
    have hot_v : (rv &&& 0x7FFFFFFF#32).toNat / 2 ≠ v := fun heqv => by
      have hme := hnot_var m hm'; rw [hmeq] at hme
      exact hme (by simpa [fullInv_var_xor1] using heqv)
    exact ⟨hlt, hent, m, hm,
      by rw [htrl_get m (by omega)]; simp [show m ≠ s.core.trail_end by omega, hmeq],
      by rw [hpl, hlvl_get _ (by omega), ite_eq_right hot_v]; exact hlvl_le⟩
  have hlift_lg : ∀ {up p0 : Nat} {rv : BitVec 32} {p_lvl : Nat}, up ≤ s.core.trail_end →
      p0 / 2 < s.core.cur_vars → (k'.lvl[p0 / 2]?.getD 0#32).toNat = p_lvl →
      (rv.toNat ∈ fullArenaClauseRefsCore s.core ∧ fullArenaClauseGarbCore s.core rv.toNat = false ∧
        ∀ q ∈ fullArenaClauseLitsCore s.core rv.toNat,
          q = p0 ∨ ∃ m < up, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
            (s.core.lvl[q / 2]?.getD 0#32).toNat ≤ p_lvl) →
      rv.toNat ∈ fullArenaClauseRefsCore k' ∧ fullArenaClauseGarbCore k' rv.toNat = false ∧
      ∀ q ∈ fullArenaClauseLitsCore k' rv.toNat,
        q = p0 ∨ ∃ m < up, (k'.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
          (k'.lvl[q / 2]?.getD 0#32).toNat ≤ (k'.lvl[p0 / 2]?.getD 0#32).toNat := by
    rintro up p0 rv p_lvl hup _ hpl ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun q hq => ?_⟩
    have hq' : q ∈ fullArenaClauseLitsCore s.core rv.toNat := by
      simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore] using hq
    exact (h3 q hq').elim Or.inl fun ⟨m, hm, hmeq, hlvl_le⟩ => Or.inr ⟨m, hm,
      by rw [htrl_get m (by omega)]; simp [show m ≠ s.core.trail_end by omega, hmeq], by
        have hm' : m < s.core.trail_end := Nat.lt_of_lt_of_le hm hup
        have hq_lt := hw.arena.lits_lt _ h1 h2 q hq'
        have hqv : q / 2 ≠ v := fun heqv => by
          have hme := hnot_var m hm'; rw [hmeq] at hme
          exact hme (by simpa [fullInv_var_xor1] using heqv)
        rw [hpl, hlvl_get _ (by omega), ite_eq_right hqv]; exact hlvl_le⟩
  exact {
    ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr
    cur_level_le := Nat.le_trans hw.cur_level_le (Nat.le_succ _)
    trail_lits_lt := fun i hi => by
      dsimp only at hi ⊢; rw [htrl_get i hi]
      split <;> (first | exact hlit | exact hw.trail_lits_lt i (by omega))
    trail_vars_nodup := fun i j hi hj hveq => by
      dsimp only at hi hj ⊢; rw [htrl_get i hi, htrl_get j hj] at hveq
      split at hveq <;> split at hveq
      · omega
      · exact absurd hveq.symm (hnot_var j (by omega))
      · exact absurd hveq (hnot_var i (by omega))
      · exact hw.trail_vars_nodup i j (by omega) (by omega) hveq
    vals_domain := fun l hl => by
      dsimp only at hl ⊢; rw [hvals_get l hl]
      split; exact Or.inr (Or.inr rfl); split; exact Or.inr (Or.inl rfl); exact hw.vals_domain l hl
    vals_true_iff := fun l hl => by
      dsimp only at hl ⊢; rw [hvals_get l hl]; constructor
      · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
        · simp [hneg] at h1
        · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
          · exact ⟨s.core.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hpos]⟩
          · simp only [hpos, ↓reduceIte] at h1
            obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
            exact ⟨i, by omega, by
              rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
      · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq; by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte] at heq; subst heq; simp [Ne.symm hne_lit]
        · simp only [hie, ↓reduceIte] at heq
          have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
          simp only [show l ≠ lit.toNat ^^^ 1 from fun h => hlv (by rw [h, fullInv_var_xor1]),
            show l ≠ lit.toNat from fun h => hlv (by rw [h]), ↓reduceIte]
          exact (hw.vals_true_iff l hl).mpr ⟨i, by omega, heq⟩
    vals_false_iff := fun l hl => by
      dsimp only at hl ⊢; rw [hvals_get l hl]; constructor
      · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
        · exact ⟨s.core.trail_end, by omega, by
            rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hneg]; exact (litNeg_litNeg _).symm⟩
        · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
          · simp [hpos] at h1
          · simp only [hpos, ↓reduceIte] at h1
            obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h1
            exact ⟨i, by omega, by
              rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
      · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq; by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte] at heq
          have hl_eq : l = lit.toNat ^^^ 1 := by
            have h := congrArg litNeg heq
            change lit.toNat ^^^ 1 = litNeg (litNeg l) at h
            rw [litNeg_litNeg] at h; exact h.symm
          simp [hl_eq]
        · simp only [hie, ↓reduceIte] at heq
          have hlv : l / 2 ≠ v := by
            have h := hnot_var i (by omega); rw [heq] at h; rwa [fullInv_var_xor1] at h
          simp only [show l ≠ lit.toNat ^^^ 1 from fun h => hlv (by rw [h, fullInv_var_xor1]),
            show l ≠ lit.toNat from fun h => hlv (by rw [h]), ↓reduceIte]
          exact (hw.vals_false_iff l hl).mpr ⟨i, by omega, heq⟩
    lvl_le := fun i hi => by
      dsimp only at hi ⊢; change (k'.lvl[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ _
      rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
      · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simpa using halvl_le
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte]
        rw [hlvl_get _ (hlt_w i hilt), ite_eq_right (hnot_var i hilt)]; exact hw.lvl_le i hilt
    dec_earliest := fun i j hi hj hleq hdec => by
      dsimp only at hi hj hleq hdec ⊢; change _ ≤ _ at ⊢
      rw [htrl_get i hi] at hleq; rw [htrl_get j hj] at hleq hdec
      by_cases hje : j = s.core.trail_end
      · subst hje; simp only [↓reduceIte] at hleq hdec
        rw [hlvl_get v (by omega), hrsn_get v (by omega)] at hdec; simp only [↓reduceIte] at hdec
        have hal0 : alvl ≠ 0 := by omega
        simp [rsn', hal0, hrsn_ne_ff] at hdec
      · by_cases hie : i = s.core.trail_end
        · omega
        · have hilt : i < s.core.trail_end := by omega
          have hjlt : j < s.core.trail_end := by omega
          simp only [hie, hje, ↓reduceIte] at hleq hdec
          rw [hlvl_get _ (hlt_w i hilt), hlvl_get _ (hlt_w j hjlt)] at hleq
          rw [hlvl_get _ (hlt_w j hjlt), hrsn_get _ (hlt_w j hjlt)] at hdec
          simp only [hnot_var i hilt, hnot_var j hjlt, ↓reduceIte] at hleq hdec
          exact hw.dec_earliest i j hilt hjlt hleq hdec
    levels_inhabited := fun L hL1 hLle => by
      dsimp only at hL1 hLle ⊢; obtain ⟨i, hi, hli⟩ := hw.levels_inhabited L hL1 hLle
      exact ⟨i, by omega, by
        rw [htrl_get i (by omega), ite_eq_right (by omega), hlvl_get _ (hlt_w i hi),
          ite_eq_right (hnot_var i hi)]; exact hli⟩
    level0_sound := fun i hi hli => by
      dsimp only at hi hli ⊢; rw [htrl_get i hi] at hli ⊢; by_cases hie : i = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hli ⊢; rw [hlvl_get v (by omega)] at hli
        simp only [↓reduceIte] at hli; exact hl0 hli
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte] at hli ⊢
        rw [hlvl_get _ (hlt_w i hilt), ite_eq_right (hnot_var i hilt)] at hli
        exact hw.level0_sound i hilt hli
    trail_pos_inv := fun i hi => by
      dsimp only at hi ⊢; rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
      · subst hie; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hcl.trail_pos_len]; exact hv_lt),
          Option.getD_some, bv32_ofNat_toNat hte_lt32]
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte, List.getElem?_set_ne (Ne.symm (hnot_var i hilt))]
        exact hw.trail_pos_inv i hilt
    level0_rsn_none := fun idx hidx hli => by
      dsimp only at hidx hli ⊢; rw [htrl_get idx hidx] at hli ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hli ⊢; rw [hlvl_get v (by omega)] at hli
        simp only [↓reduceIte] at hli; rw [hrsn_get v (by omega)]; simp [rsn', hli]
      · have hilt : idx < s.core.trail_end := by omega
        have hnv := hnot_var idx hilt
        simp only [hie, ↓reduceIte] at hli ⊢
        rw [hlvl_get _ (hlt_w idx hilt), ite_eq_right hnv] at hli
        rw [hrsn_get _ (hlt_w idx hilt), ite_eq_right hnv]; exact hw.level0_rsn_none idx hilt hli
    frame_trail_lt := fun L hL => Nat.le_trans (hw.frame_trail_lt L hL) (Nat.le_succ _)
    frame_trail_mono := hw.frame_trail_mono
    frame_trail_before_lt := fun L hL1 hLle i hi => by
      dsimp only at hL1 hLle hi ⊢
      have hi_le : i < s.core.trail_end := Nat.lt_of_lt_of_le hi (hw.frame_trail_lt L hLle)
      rw [htrl_get i (by omega), ite_eq_right (by omega), hlvl_get _ (hlt_w i hi_le),
        ite_eq_right (hnot_var i hi_le)]
      exact hw.frame_trail_before_lt L hL1 hLle i hi
    frame_dec_lt := hw.frame_dec_lt
    reason_inv := fun idx hidx hne => by
      dsimp only at hidx hne ⊢; rw [htrl_get idx hidx] at hne ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hne ⊢; rw [hrsn_get v (by omega)] at hne ⊢
        simp only [↓reduceIte] at hne ⊢; by_cases hal0 : alvl = 0
        · simp [rsn', hal0] at hne
        · have hrs := hrsn (Nat.zero_lt_of_ne_zero hal0)
          simp only [rsn', hal0, ↓reduceIte] at hne hrs ⊢
          have hkv : (k'.lvl[lit.toNat / 2]?.getD 0#32).toNat = alvl := by
            change (k'.lvl[v]?.getD 0#32).toNat = alvl
            rw [hlvl_get v (by omega), ite_eq_left rfl]
          by_cases hbin : (rsn &&& 0x80000000#32) ≠ 0#32
          · rw [ite_eq_left hbin] at hrs ⊢
            exact hlift_rsn (by omega) hbin (by omega) hkv hrs
          · rw [ite_eq_right hbin] at hrs ⊢
            exact hlift_lg (by omega) (by omega) hkv hrs
      · have hilt : idx < s.core.trail_end := by omega
        have hnv := hnot_var idx hilt
        simp only [hie, ↓reduceIte] at hne ⊢
        rw [hrsn_get _ (hlt_w idx hilt), ite_eq_right hnv] at hne ⊢
        have hrs := hw.reason_inv idx hilt hne
        have hl_eq : (k'.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
            (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
          rw [hlvl_get _ (hlt_w idx hilt), ite_eq_right hnv]
        by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hbin] at hrs ⊢; exact hlift_rsn (by omega) hbin (hlt_w idx hilt) hl_eq hrs
        · rw [ite_eq_right hbin] at hrs ⊢; exact hlift_lg (by omega) (hlt_w idx hilt) hl_eq hrs
    reason_lit_mem := fun idx hidx hne hlg => by
      dsimp only at hidx hne hlg ⊢; rw [htrl_get idx hidx] at hne hlg ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hne hlg ⊢; rw [hrsn_get v (by omega)] at hne hlg ⊢
        simp only [↓reduceIte] at hne hlg ⊢; by_cases hal0 : alvl = 0
        · simp [rsn', hal0] at hne
        · simp only [rsn', hal0, ↓reduceIte] at hne hlg ⊢
          simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore] using
            hrsn_mem (Nat.zero_lt_of_ne_zero hal0) hlg
      · have hilt : idx < s.core.trail_end := by omega
        have hnv := hnot_var idx hilt
        simp only [hie, ↓reduceIte] at hne hlg ⊢
        rw [hrsn_get _ (hlt_w idx hilt), ite_eq_right hnv] at hne hlg ⊢
        simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore] using
          hw.reason_lit_mem idx hilt hne hlg }

private structure OneLitBtInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s1 : FullState) (cut1 clvl : Nat) : Prop where
  cut1_le : cut1 ≤ s1.core.trail_end
  hw1 : FullWitnessCutInv c F0 F_cur cut1 s1.core
  len1 : s1.LengthsOk c
  cl1_eq : s1.core.cur_level = clvl
  cl_pos : 0 < clvl
  cl_le : clvl ≤ s.core.cur_level
  cv_eq : s1.core.cur_vars = s.core.cur_vars
  fuel_eq : s1.core.fuel = s.core.fuel
  ws2_eq : s1.scratch.work_stk2 = s.scratch.work_stk2
  dm0 : s1.core.dense_mode = 0#64
  prob_eq : s1.core.probing = s.core.probing
  wvec_eq : s1.core.wvec = s.core.wvec
  wstk_eq : s1.core.wstk = s.core.wstk
  wlen_eq : s1.core.wlen = s.core.wlen
  wus_eq : s1.core.wusable = s.core.wusable
  marks1 : FullLitMarksClear c s1
  nodup1 : FullArenaVarsNodup s1
  ext1 : FullExtScratchOk c s1
  confl1 : FullConflictOkCut F_cur cut1 s1
  vals_keep : ∀ l < 2 * s.core.cur_vars,
    (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ clvl →
    s1.core.vals[l]?.getD 0#8 = s.core.vals[l]?.getD 0#8
  lvl_keep : ∀ l < 2 * s.core.cur_vars,
    s.core.vals[l]?.getD 0#8 = 0xFF#8 →
    (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ clvl →
    s1.core.lvl[l / 2]?.getD 0#32 = s.core.lvl[l / 2]?.getD 0#32
  arena_eq : s1.core.arena = s.core.arena
  arena_len_eq : s1.core.arena_len = s.core.arena_len

private theorem oneLit_after_bt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut clvl : Nat} {s s1 : FullState} (hlen : s.LengthsOk c) (hdm : s.core.dense_mode = 0#64)
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hmarks : FullLitMarksClear c s)
    (hnd : FullArenaVarsNodup s) (hext : FullExtScratchOk c s) (hcut_le : cut ≤ s.core.trail_end)
    (hconfl : FullConflictOkCut F_cur cut s) (hcl_pos : 0 < clvl) (hcl_le : clvl ≤ s.core.cur_level)
    (hbt_lt : ∀ l, (s.core.confl_type = 1#64 ∧
        (l = s.core.confl_lit0.toNat ∨ l = s.core.confl_lit1.toNat)) ∨
      (s.core.confl_type ≠ 1#64 ∧ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat) →
      (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ clvl)
    (hs1 : s.core.cur_level ≤ clvl ∧ s1 = s ∨
      clvl < s.core.cur_level ∧ s1.LengthsOk c ∧ s1.core.cur_level = clvl ∧
      s1.core.fuel = s.core.fuel ∧ s1.scratch.work_stk2 = s.scratch.work_stk2 ∧
      s1.scratch.last_learned = s.scratch.last_learned ∧
      s1.scratch.extend_len = s.scratch.extend_len ∧
      s1.core.dense_mode = 0#64 ∧ s1.core.probing = s.core.probing ∧
      s1.core.cur_vars = s.core.cur_vars ∧ s1.core.wvec = s.core.wvec ∧
      s1.core.wstk = s.core.wstk ∧ s1.core.wlen = s.core.wlen ∧ s1.core.wusable = s.core.wusable ∧
      s1.core.mrk = s.core.mrk ∧ s1.core.lit_mark = s.core.lit_mark ∧
      s1.core.arena = s.core.arena ∧ s1.core.arena_len = s.core.arena_len ∧
      s1.core.confl_type = s.core.confl_type ∧ s1.core.confl_lit0 = s.core.confl_lit0 ∧
      s1.core.confl_lit1 = s.core.confl_lit1 ∧ s1.core.confl_ref = s.core.confl_ref ∧
      (∀ l < 2 * s.core.cur_vars, s1.core.vals[l]?.getD 0#8 =
        if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ clvl then s.core.vals[l]?.getD 0#8 else 0#8) ∧
      (∀ i < s.core.trail_end, let v := (s.core.trl[i]?.getD 0#32).toNat / 2
        s1.core.lvl[v]?.getD 0#32 =
          if (s.core.lvl[v]?.getD 0#32).toNat ≤ clvl then s.core.lvl[v]?.getD 0#32 else 0#32) ∧
      FullWitnessInv c F0 F_cur s1.core) :
    ∃ cut1, OneLitBtInv c F0 F_cur s s1 cut1 clvl := by
  rcases hs1 with ⟨hle, rfl⟩ | ⟨_, hlen1, hcl1, hfu1, hws2, hll1, hel1, hdm1, hpr1, hcv1, hwv1,
      hws1, hwl1, hwu1, hmk1, hlm1, har1, hal1, hct1, hc01, hc11, hcr1, hvals1, hlvl1, hw1⟩
  · exact ⟨cut, hcut_le, hw, hlen, by omega, hcl_pos, hcl_le, rfl, rfl, rfl, hdm, rfl, rfl, rfl,
      rfl, rfl, hmarks, hnd, hext, hconfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl⟩
  · have hrefs : fullArenaClauseRefsCore s1.core = fullArenaClauseRefsCore s.core := by
      simp [fullArenaClauseRefsCore, har1, hal1]
    have hmarks1 : FullLitMarksClear c s1 :=
      ⟨fun v hv => by rw [hmk1]; exact hmarks.1 v hv, fun l hl => by rw [hlm1]; exact hmarks.2 l hl⟩
    have hnd1 : FullArenaVarsNodup s1 := fun r hr hng => by
      change r ∈ fullArenaClauseRefsCore s1.core at hr; rw [hrefs] at hr
      change ((fullArenaClauseLitsCore s1.core r).map (· / 2)).Nodup
      simp only [fullArenaClauseLitsCore, fullArenaClauseSizeCore, har1]
      exact hnd r hr (by simpa [fullArenaClauseGarbCore, fullArenaHdrCore, har1] using hng)
    have hext1 : FullExtScratchOk c s1 := ⟨fun i hi => by
      change _ = _ ∨ _ ∈ fullArenaClauseRefsCore s1.core
      rw [hrefs, hll1]; exact hext.1 i hi, by rw [hel1]; exact hext.2⟩
    have hconfl1 : FullConflictOkCut F_cur s1.core.trail_end s1 := by
      refine FullConflictOkW.toCut hw1 ?_
      rcases hconfl.1 with ⟨hbin, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨hct2, href, hng, hf⟩
      · left; rw [hct1, hc01, hc11, hcv1]
        have hf0' : s1.core.vals[s.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 := by
          rw [hvals1 _ h0lt, ite_eq_left (hbt_lt _ (Or.inl ⟨hbin, Or.inl rfl⟩)), hf0]
        have hf1' : s1.core.vals[s.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8 := by
          rw [hvals1 _ h1lt, ite_eq_left (hbt_lt _ (Or.inl ⟨hbin, Or.inr rfl⟩)), hf1]
        exact ⟨hbin, h0lt, h1lt, hf0', hf1', hent⟩
      · right
        have hne1 : s.core.confl_type ≠ 1#64 := by rw [hct2]; decide
        have hgarb : fullArenaClauseGarb s1 s.core.confl_ref.toNat =
            fullArenaClauseGarb s s.core.confl_ref.toNat := by
          simp [fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore, har1]
        have hlits : fullArenaClauseLits s1 s.core.confl_ref.toNat =
            fullArenaClauseLits s s.core.confl_ref.toNat := by
          simp [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, har1]
        rw [hct1, hcr1, show fullArenaClauseRefs s1 = fullArenaClauseRefs s from hrefs,
          hgarb, hlits]
        refine ⟨hct2, href, hng, fun l hl => ?_⟩
        have hllt := hw.arena.lits_lt _ href hng l hl
        rw [hvals1 l hllt, ite_eq_left (hbt_lt l (Or.inr ⟨hne1, hl⟩)), hf l hl]
    refine ⟨s1.core.trail_end, Nat.le_refl _, hw1.toCut, hlen1, hcl1, hcl_pos,
      hcl_le, hcv1, hfu1, hws2, hdm1, hpr1, hwv1, hws1, hwl1, hwu1, hmarks1, hnd1, hext1, hconfl1,
      fun l hl hle => by rw [hvals1 l hl, ite_eq_left hle], fun l hl hfl hle => ?_, har1, hal1⟩
    obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l hl).mp hfl
    have hv := hlvl1 i hi; dsimp only at hv; rw [hieq, fullInv_var_xor1] at hv
    rw [hv, ite_eq_left hle]

private theorem oneLit_swap_arena_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut1 : Nat} {s_in : FullState} {cref : BitVec 32} {csz_val i j : Nat}
    (hlen : s_in.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut1 s_in.core)
    (hnd : FullArenaVarsNodup s_in) (hext : FullExtScratchOk c s_in)
    (href : cref.toNat ∈ fullArenaClauseRefsCore s_in.core)
    (hng : fullArenaClauseGarbCore s_in.core cref.toNat = false)
    (hsz : fullArenaClauseSizeCore s_in.core cref.toNat = csz_val)
    (hi : i < csz_val) (hj : j < csz_val) (li lj : BitVec 32)
    (hli : li = s_in.core.arena[cref.toNat + 3 + i]?.getD 0#32)
    (hlj : lj = s_in.core.arena[cref.toNat + 3 + j]?.getD 0#32) :
    let ar' := (s_in.core.arena.set (cref.toNat + 3 + i) lj).set (cref.toNat + 3 + j) li
    let s' : FullState := { s_in with core := { s_in.core with arena := ar' } }
    s'.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut1 s'.core ∧
    FullArenaVarsNodup s' ∧ FullExtScratchOk c s' ∧
    fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s_in.core ∧
    cref.toNat ∈ fullArenaClauseRefsCore s'.core ∧
    fullArenaClauseGarbCore s'.core cref.toNat = false ∧
    fullArenaClauseSizeCore s'.core cref.toNat = csz_val ∧
    (fullArenaClauseLitsCore s'.core cref.toNat).Perm
      (fullArenaClauseLitsCore s_in.core cref.toNat) := by
  intro ar' s'
  have har_len := hlen.core_ok.arena_len_arr
  obtain ⟨hw', hrefs', hsz', hng', hperm', hother'⟩ :=
    fa_swapCl_preserves_fullWitnessCut hlen.core_ok (canonCut_to_fa hw) href (i := i) (j := j)
      (by rw [hsz]; exact hi) (by rw [hsz]; exact hj)
  have har_sym : (s_in.core.arena.set (cref.toNat + 3 + i)
      (s_in.core.arena[cref.toNat + 3 + j]?.getD 0#32)).set (cref.toNat + 3 + j)
      (s_in.core.arena[cref.toNat + 3 + i]?.getD 0#32) = ar' := by
    dsimp only [ar']; rw [← hli, ← hlj]
  have hw_s' : FullWitnessCutInv c F0 F_cur cut1 s'.core :=
    faCut_to_canon hw.cut_le (by simpa only [s', ← har_sym] using hw')
  have hrefs_s' : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s_in.core := by
    simpa only [s', ← har_sym] using hrefs'
  have hperm_s' : (fullArenaClauseLitsCore s'.core cref.toNat).Perm
      (fullArenaClauseLitsCore s_in.core cref.toNat) := by
    simpa only [s', ← har_sym] using hperm'
  have hsz_s' : fullArenaClauseSizeCore s'.core cref.toNat = csz_val := by
    rw [show fullArenaClauseSizeCore s'.core cref.toNat =
      fullArenaClauseSizeCore s_in.core cref.toNat from by simpa only [s', ← har_sym] using hsz',
      hsz]
  have hng_s' : fullArenaClauseGarbCore s'.core cref.toNat = false := by
    simpa only [s', ← har_sym, hng] using hng'
  have hnd_s' : FullArenaVarsNodup s' := fun r hr hngr => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs_s'] at hr
    by_cases hrc : r = cref.toNat
    · subst r; exact (hperm_s'.map (· / 2)).nodup_iff.mpr (hnd _ hr hng)
    · have ho := hother' r hr hrc; change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
      rw [show fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s_in.core r from by
        simpa only [s', ← har_sym] using ho.2.2]
      change fullArenaClauseGarbCore s'.core r = false at hngr
      simp only [s', ← har_sym] at hngr; rw [ho.2.1] at hngr; exact hnd r hr hngr
  exact ⟨⟨{ hlen.core_ok with arena_len_arr := by simp [s', ar', har_len] }, hlen.scratch_ok⟩,
    hw_s', hnd_s', ⟨fun k hk => by
      change _ = _ ∨ _ ∈ fullArenaClauseRefsCore s'.core
      rw [hrefs_s']; exact hext.1 k hk, hext.2⟩,
    hrefs_s', by rw [hrefs_s']; exact href, hng_s', hsz_s', hperm_s'⟩

private def OneLitPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ r s' m',
    s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
    s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
    s'.scratch.work_stk2 = s.scratch.work_stk2 →
    s'.core.dense_mode = 0#64 → s'.core.probing = s.core.probing →
    FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
    (s.core.confl_type = 1#64 → r ≠ 2#64) →
    (r = 20#64 → F0.Unsat ∧ s' = s) →
    (r = 1#64 → FullWitnessInv c F0 F_cur s'.core ∧ s'.core.cur_level < s.core.cur_level) →
    (r = 2#64 → FullOtfsWitnessInv c F0 F_cur s'.core) →
    (r = 0#64 → ∃ cut' ≤ s'.core.trail_end,
      FullWitnessCutInv c F0 F_cur cut' s'.core ∧ 0 < s'.core.cur_level ∧
      s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.wvec = s.core.wvec ∧
      s'.core.wstk = s.core.wstk ∧ s'.core.wlen = s.core.wlen ∧
      s'.core.wusable = s.core.wusable ∧ FullConflictOkCut F_cur cut' s') →
    (FullMem c s' ⋆ R) m' → Q (r, ()) m'

private structure OneLitTailPre (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sb : FullState) (cut1 clvl jlvl : Nat) (forced rsn : BitVec 32) : Prop where
  len : sb.LengthsOk c
  hw : FullWitnessCutInv c F0 F_cur cut1 sb.core
  marks : FullLitMarksClear c sb
  nd : FullArenaVarsNodup sb
  ext : FullExtScratchOk c sb
  cl_eq : sb.core.cur_level = clvl
  cl_le : clvl ≤ s.core.cur_level
  cv_eq : sb.core.cur_vars = s.core.cur_vars
  fu_eq : sb.core.fuel = s.core.fuel
  ws2_eq : sb.scratch.work_stk2 = s.scratch.work_stk2
  dm0 : sb.core.dense_mode = 0#64
  prob_eq : sb.core.probing = s.core.probing
  forced_lt : forced.toNat < 2 * sb.core.cur_vars
  forced_lvl : (sb.core.lvl[forced.toNat / 2]?.getD 0#32).toNat = clvl
  rsn_ne : rsn ≠ 0xFFFFFFFF#32
  rsn_pre :
    if (rsn &&& 0x80000000#32) ≠ 0#32 then
      let ot := (rsn &&& 0x7FFFFFFF#32).toNat
      ot < 2 * sb.core.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [forced.toNat, ot]) ∧
      sb.core.vals[ot]?.getD 0#8 = 0xFF#8 ∧ (sb.core.lvl[ot / 2]?.getD 0#32).toNat ≤ jlvl
    else
      rsn.toNat ∈ fullArenaClauseRefsCore sb.core ∧
      fullArenaClauseGarbCore sb.core rsn.toNat = false ∧
      forced.toNat ∈ fullArenaClauseLitsCore sb.core rsn.toNat ∧
      ∀ q ∈ fullArenaClauseLitsCore sb.core rsn.toNat,
        q = forced.toNat ∨ (sb.core.vals[q]?.getD 0#8 = 0xFF#8 ∧
          (sb.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvl)

private theorem oneLit_after_bt_assign_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut1 clvl jlvl nlvl : Nat} {s s1 s2 : FullState}
    {forced rsn : BitVec 32} {jlvlv : BitVec 64} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {m2 : Mem 64}
    (hAss : ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hpre : OneLitTailPre c F0 F_cur s s1 cut1 clvl jlvl forced rsn)
    (hjv_eq : jlvlv.toNat = jlvl) (hj_lt32 : jlvl < 2 ^ 32)
    (hjlvl_le : jlvl ≤ nlvl) (hnlvl_lt : nlvl < clvl)
    (hs2_len : s2.LengthsOk c) (hs2_cl : s2.core.cur_level = nlvl)
    (hs2_fu : s2.core.fuel = s1.core.fuel) (hs2_ws2 : s2.scratch.work_stk2 = s1.scratch.work_stk2)
    (hs2_ll : s2.scratch.last_learned = s1.scratch.last_learned)
    (hs2_el : s2.scratch.extend_len = s1.scratch.extend_len)
    (hs2_dm : s2.core.dense_mode = 0#64) (hs2_pr : s2.core.probing = s1.core.probing)
    (hs2_cv : s2.core.cur_vars = s1.core.cur_vars)
    (hs2_mk : s2.core.mrk = s1.core.mrk) (hs2_lm : s2.core.lit_mark = s1.core.lit_mark)
    (hs2_ar : s2.core.arena = s1.core.arena) (hs2_al : s2.core.arena_len = s1.core.arena_len)
    (hs2_vals : ∀ l < 2 * s1.core.cur_vars, s2.core.vals[l]?.getD 0#8 =
      if (s1.core.lvl[l / 2]?.getD 0#32).toNat ≤ nlvl then s1.core.vals[l]?.getD 0#8 else 0#8)
    (hs2_lvl : ∀ i < s1.core.trail_end, let v := (s1.core.trl[i]?.getD 0#32).toNat / 2
      s2.core.lvl[v]?.getD 0#32 =
        if (s1.core.lvl[v]?.getD 0#32).toNat ≤ nlvl then s1.core.lvl[v]?.getD 0#32 else 0#32)
    (hw2 : FullWitnessInv c F0 F_cur s2.core) (hm2 : (FullMem c s2 ⋆ R) m2)
    (hQ : OneLitPost c F0 F_cur s R Q) :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i32, i32]) "full_assign_lvl"
        (Arg.var c.hdr, Arg.var forced, Arg.var rsn, Arg.var (jlvlv.setWidth 32), ())
        fun (_ : Tup Val []) => Expr.ret (Arg.imm 1#64, ())) m2 := by
  have htr_eq : jlvlv.setWidth 32 = BitVec.ofNat 32 jlvl := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_setWidth, hjv_eq, bv32_ofNat_toNat hj_lt32, Nat.mod_eq_of_lt hj_lt32])
  have hf_un : s2.core.vals[forced.toNat]?.getD 0#8 = 0#8 := by
    rw [hs2_vals _ hpre.forced_lt, ite_eq_right (by have := hpre.forced_lvl; omega)]
  have hte2_lt : s2.core.trail_end < s2.core.cur_vars :=
    hw2.trail_end_lt_of_unassigned (hs2_cv ▸ hpre.forced_lt) hf_un
  have hng_guard : ¬ (s2.core.cur_vars ≤ forced.toNat / 2 ∨
      c.max_vars ≤ s2.core.trail_end ∨ s2.core.vals[forced.toNat]?.getD 0#8 ≠ 0#8) :=
    not_or.mpr ⟨Nat.not_le.mpr (Nat.div_lt_of_lt_mul (hs2_cv ▸ hpre.forced_lt)), not_or.mpr
      ⟨Nat.not_le.mpr (by have := hs2_len.core_ok.cur_vars_le; omega), fun h => h hf_un⟩⟩
  c0_call hAss
  refine ⟨c, s2, R, rfl, hs2_len, hm2, ?_⟩
  simp only [hng_guard, ↓reduceIte]
  intro fl' unass3 ph' m3 hfl3 hph3 hm3
  let v := forced.toNat / 2
  let rsn' := if jlvl = 0 then 0xFFFFFFFF#32 else rsn
  let s3 : FullState :=
    { s2 with
      core :=
        { s2.core with
          vals := (s2.core.vals.set forced.toNat 1#8).set (forced.toNat ^^^ 1) 0xFF#8
          flags := fl', lvl := s2.core.lvl.set v (BitVec.ofNat 32 jlvl)
          rsns := s2.core.rsns.set v rsn', trl := s2.core.trl.set s2.core.trail_end forced
          trail_pos := s2.core.trail_pos.set v (BitVec.ofNat 32 s2.core.trail_end)
          trail_end := s2.core.trail_end + 1, unassigned := unass3
          unflushed := if jlvlv.setWidth 32 = 0#32
            then s2.core.unflushed + 1#64 else s2.core.unflushed }
      scratch := { s2.scratch with phases := ph' } }
  have hcv2 := hs2_len.core_ok.cur_vars_le
  have hlen3 : s3.LengthsOk c :=
    ⟨{ hs2_len.core_ok with
        vals_len := by simp [s3, hs2_len.core_ok.vals_len], flags_len := hfl3,
        lvl_len := by simp [s3, hs2_len.core_ok.lvl_len],
        rsns_len := by simp [s3, hs2_len.core_ok.rsns_len],
        trl_len := by simp [s3, hs2_len.core_ok.trl_len],
        trail_pos_len := by simp [s3, hs2_len.core_ok.trail_pos_len],
        trail_end_le := by dsimp [s3]; omega,
        propagated_le := Nat.le_trans hs2_len.core_ok.propagated_le (Nat.le_succ _) },
     { hs2_len.scratch_ok with phases_len := by dsimp [s3]; exact hph3 }⟩
  have hmarks3 : FullLitMarksClear c s3 := ⟨fun w hw => by
    change s2.core.mrk[w]?.getD 0#8 = 0#8; rw [hs2_mk]; exact hpre.marks.1 w hw,
    fun l hl => by change s2.core.lit_mark[l]?.getD 0#8 = 0#8; rw [hs2_lm]; exact hpre.marks.2 l hl⟩
  have hrefs : fullArenaClauseRefsCore s3.core = fullArenaClauseRefsCore s1.core := by
    simp [fullArenaClauseRefsCore, s3, hs2_ar, hs2_al]
  have hnd3 : FullArenaVarsNodup s3 := fun r hr hng => by
    change r ∈ fullArenaClauseRefsCore s3.core at hr; rw [hrefs] at hr
    change ((fullArenaClauseLitsCore s3.core r).map (· / 2)).Nodup
    simp only [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s3, hs2_ar]
    exact hpre.nd r hr (by simpa [fullArenaClauseGarbCore, fullArenaHdrCore, s3, hs2_ar] using hng)
  have hext3 : FullExtScratchOk c s3 := ⟨fun i hi => by
    change _ = _ ∨ _ ∈ fullArenaClauseRefsCore s3.core; rw [hrefs, hs2_ll]; exact hpre.ext.1 i hi,
    by change s2.scratch.extend_len ≤ c.extend_cap; rw [hs2_el]; exact hpre.ext.2⟩
  have h_s2_false : ∀ q < 2 * s1.core.cur_vars, s1.core.vals[q]?.getD 0#8 = 0xFF#8 →
      (s1.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvl →
      ∃ m < s2.core.trail_end, (s2.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
        (s2.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvl := fun q hq hqf hql => by
    have hqf2 : s2.core.vals[q]?.getD 0#8 = 0xFF#8 := by
      rw [hs2_vals q hq, ite_eq_left (by omega), hqf]
    obtain ⟨m, hm, hmeq⟩ := (hw2.vals_false_iff q (hs2_cv ▸ hq)).mp hqf2
    obtain ⟨i, hi, hieq⟩ := (hpre.hw.vals_false_iff q hq).mp hqf
    have hlv := hs2_lvl i hi; dsimp only at hlv; rw [hieq, fullInv_var_xor1] at hlv
    exact ⟨m, hm, hmeq, by rw [hlv, ite_eq_left (by omega)]; exact hql⟩
  have hrsn_pre := hpre.rsn_pre
  have hl0 : jlvl = 0 → (cnfOfClauses F_cur).EntailsClause (cnfClause [forced.toNat]) := by
    intro hj0; subst hj0; by_cases hbin : (rsn &&& 0x80000000#32) ≠ 0#32
    · rw [ite_eq_left hbin] at hrsn_pre; obtain ⟨hot_lt, hent, hot_f, hot_lv⟩ := hrsn_pre
      obtain ⟨m, hm, hmeq, hml0⟩ := h_s2_false _ hot_lt hot_f hot_lv
      have htr0 : (s2.core.lvl[(s2.core.trl[m]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
        rw [hmeq, fullInv_var_xor1]; omega
      exact entails_of_mem_or_false hent fun l hl => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        exact hl.elim (fun h => h ▸ Or.inl List.mem_cons_self) fun h =>
          Or.inr (h ▸ by have hs := hw2.level0_sound m hm htr0; rwa [hmeq] at hs)
    · rw [ite_eq_right hbin] at hrsn_pre; obtain ⟨h1, h2, _, h4⟩ := hrsn_pre
      have h1' : rsn.toNat ∈ fullArenaClauseRefsCore s2.core := by
        simpa [fullArenaClauseRefsCore, hs2_ar, hs2_al] using h1
      have h2' : fullArenaClauseGarbCore s2.core rsn.toNat = false := by
        simpa [fullArenaClauseGarbCore, fullArenaHdrCore, hs2_ar] using h2
      exact entails_of_mem_or_false (hw2.arena.entails rsn.toNat h1' h2') fun q hq => by
        have hq1 : q ∈ fullArenaClauseLitsCore s1.core rsn.toNat := by
          simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, hs2_ar] using hq
        rcases h4 q hq1 with rfl | ⟨hqf, hql⟩
        · exact Or.inl List.mem_cons_self
        · obtain ⟨m, hm, hmeq, hml⟩ := h_s2_false q (hs2_cv ▸ hw2.arena.lits_lt _ h1' h2' q hq)
            hqf hql
          have htr0 : (s2.core.lvl[(s2.core.trl[m]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0
              := by rw [hmeq, fullInv_var_xor1]; omega
          exact Or.inr (by have hs := hw2.level0_sound m hm htr0; rwa [hmeq] at hs)
  have hrsn2 : 0 < jlvl → if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * s2.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause
          (cnfClause [forced.toNat, ot]) ∧
        ∃ m < s2.core.trail_end, (s2.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
          (s2.core.lvl[ot / 2]?.getD 0#32).toNat ≤ jlvl
      else
        rsn.toNat ∈ fullArenaClauseRefsCore s2.core ∧
        fullArenaClauseGarbCore s2.core rsn.toNat = false ∧
        ∀ q ∈ fullArenaClauseLitsCore s2.core rsn.toNat,
          q = forced.toNat ∨ ∃ m < s2.core.trail_end, (s2.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
            (s2.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvl := by
    intro _; by_cases hbin : (rsn &&& 0x80000000#32) ≠ 0#32
    · rw [ite_eq_left hbin] at hrsn_pre ⊢; obtain ⟨hot_lt, hent, hot_f, hot_lv⟩ := hrsn_pre
      exact ⟨hs2_cv ▸ hot_lt, hent, h_s2_false _ hot_lt hot_f hot_lv⟩
    · rw [ite_eq_right hbin] at hrsn_pre ⊢; obtain ⟨h1, h2, _, h4⟩ := hrsn_pre
      have h1' : rsn.toNat ∈ fullArenaClauseRefsCore s2.core := by
        simpa [fullArenaClauseRefsCore, hs2_ar, hs2_al] using h1
      have h2' : fullArenaClauseGarbCore s2.core rsn.toNat = false := by
        simpa [fullArenaClauseGarbCore, fullArenaHdrCore, hs2_ar] using h2
      refine ⟨h1', h2', fun q hq => ?_⟩
      have hq1 : q ∈ fullArenaClauseLitsCore s1.core rsn.toNat := by
        simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, hs2_ar] using hq
      exact (h4 q hq1).elim Or.inl fun ⟨hqf, hql⟩ =>
        Or.inr (h_s2_false q (hs2_cv ▸ hw2.arena.lits_lt _ h1' h2' q hq) hqf hql)
  have hrsn_mem2 : 0 < jlvl → (rsn &&& 0x80000000#32) = 0#32 →
      forced.toNat ∈ fullArenaClauseLitsCore s2.core rsn.toNat := fun _ hlg => by
    rw [ite_eq_right (fun h => absurd hlg h)] at hrsn_pre
    simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, hs2_ar] using hrsn_pre.2.2.1
  have hw3 := chronoAssign_preserves_fullWitness_sameLvl hs2_len hw2 (hs2_cv ▸ hpre.forced_lt)
    hf_un (hs2_cl ▸ hjlvl_le) hpre.rsn_ne hl0 hrsn2 hrsn_mem2 (flags' := fl')
    (unassigned' := unass3) (unflushed' := s3.core.unflushed)
  have hj_z : (jlvlv.setWidth 32 = 0#32) ↔ jlvl = 0 := by
    rw [htr_eq]; constructor
    · intro h; simpa [bv32_ofNat_toNat hj_lt32] using congrArg BitVec.toNat h
    · intro h; simp [h]
  have hrsn_eq : (if jlvlv.setWidth 32 = 0#32 then 0xFFFFFFFF#32 else rsn) =
      if jlvl = 0 then 0xFFFFFFFF#32 else rsn := by
    by_cases hj : jlvl = 0
    · rw [ite_eq_left (hj_z.mpr hj), ite_eq_left hj]
    · rw [ite_eq_right (fun h => hj (hj_z.mp h)), ite_eq_right hj]
  fa_fast_steps
  exact hQ 1#64 s3 m3 hlen3 (Or.inr (Or.inl rfl)) (hs2_cv.trans hpre.cv_eq)
    (hs2_fu.trans hpre.fu_eq) (hs2_ws2.trans hpre.ws2_eq) hs2_dm (hs2_pr.trans hpre.prob_eq)
    hmarks3 hnd3 hext3 (fun _ h => by cases h) (fun h => by cases h)
    (fun _ => ⟨hw3, by dsimp [s3]; have := hpre.cl_le; omega⟩)
    (fun h => by cases h) (fun h => by cases h)
    (fullMem_of_eq hm3 (by dsimp only [s3, rsn', v]; rw [hrsn_eq, htr_eq]) rfl)

private theorem oneLit_bin_swap_if {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut1 clvl : Nat} {s s1 : FullState} {a b : BitVec 32} {la lb : BitVec 32}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m1 : Mem 64}
    (_hDet : ∀ args m Q X, fullDetNewLevelSpec args m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] args m Q X)
    (hBt : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hAss : ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hobt : OneLitBtInv c F0 F_cur s s1 cut1 clvl)
    (ha_lt : a.toNat < 2 * s.core.cur_vars) (hb_lt : b.toNat < 2 * s.core.cur_vars)
    (hla_val : la.toNat = (s.core.lvl[a.toNat / 2]?.getD 0#32).toNat)
    (hlb_val : lb.toNat = (s.core.lvl[b.toNat / 2]?.getD 0#32).toNat)
    (hmax : clvl = max la.toNat lb.toNat) (hne : la ≠ lb)
    (hfa : s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8)
    (hfb : s.core.vals[b.toNat]?.getD 0#8 = 0xFF#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat]))
    (hm1 : (FullMem c s1 ⋆ R) m1) (hQ : OneLitPost c F0 F_cur s R Q) :
    let forced := if la > lb then a else b
    let other := if la > lb then b else a
    let jlvl : Nat := if la > lb then lb.toNat else la.toNat
    ∀ nlvl : BitVec 64,
      (0 < s1.core.cur_level → jlvl < s1.core.cur_level →
        jlvl ≤ nlvl.toNat ∧ nlvl.toNat < s1.core.cur_level) →
      wp Γ Q X
        (Expr.call (as := [i64, i64]) "full_backtrack"
            (Arg.var c.hdr, Arg.var nlvl, ()) fun (_ : Tup Val []) =>
          Expr.let_ {
            sig := [i32, i32], code := OpCode.and i32,
            args := (Arg.var other, Arg.imm 2147483647#32, ()) } fun p_26 =>
          Expr.let_ {
            sig := [i32, i32], code := OpCode.or i32,
            args := (Arg.var p_26.fst, Arg.imm 2147483648#32, ()) } fun p_27 =>
          Expr.let_ {
            sig := [i64], code := OpCode.trunc 64 32,
            args := (Arg.var (BitVec.ofNat 64 jlvl), ()) } fun p_28 =>
          Expr.call (as := [i64, i32, i32, i32]) "full_assign_lvl"
            (Arg.var c.hdr, Arg.var forced, Arg.var p_27.fst, Arg.var p_28.fst, ())
            fun (_ : Tup Val []) => Expr.ret (Arg.imm 1#64, ())) m1 := by
  intro forced other jlvl nlvl hnlvl
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv; have hcv := hobt.len1.core_ok.cur_vars_le
  have h2cv : 2 * s.core.cur_vars < 2 ^ 31 - 1 := by have := hobt.cv_eq; omega
  have hjlt : jlvl < clvl := by
    dsimp only [jlvl]; split <;> rename_i hgt
    · have : lb.toNat < la.toNat := hgt; omega
    · have : la.toNat ≤ lb.toNat := Nat.not_lt.mp hgt
      have hneq : la.toNat ≠ lb.toNat := fun he => hne (BitVec.eq_of_toNat_eq he); omega
  obtain ⟨hjl_le_nl, hnl_lt⟩ := hnlvl (hobt.cl1_eq ▸ hobt.cl_pos) (hobt.cl1_eq ▸ hjlt)
  rw [hobt.cl1_eq] at hnl_lt
  c0_call hBt
  refine ⟨c, s1, R, rfl, hobt.len1, by
    have := hobt.hw1.cur_level_le; have := hobt.len1.core_ok.trail_end_le; omega,
    fun h => by have := hobt.hw1.cur_level_le; have := hobt.len1.core_ok.trail_end_le; omega,
    hobt.hw1.trail_lits_lt, hm1, ?_⟩
  dsimp only
  intro vals2 lvl2 rsns2 trl2 tp2 te2 prop2 cl2 unass2 sc2 m2 hlen2 _ _ hcl2 hpres _ _ hvl2 _ hw2
    hm2
  have hcl2_eq : cl2 = nlvl.toNat := by rw [hcl2, hobt.cl1_eq]; omega
  have hw2' := hw2 F0 F_cur hobt.hw1.toFullOtfsWitnessInv (by rw [hobt.cl1_eq]; exact hnl_lt)
  obtain ⟨hvals2, hlvl2⟩ := hvl2 ⟨F0, F_cur, Or.inr hobt.hw1.toFullOtfsWitnessInv⟩
  have hforced_lt : forced.toNat < 2 * s1.core.cur_vars := by
    rw [hobt.cv_eq]; dsimp only [forced]; split <;> assumption
  have hother_lt : other.toNat < 2 * s1.core.cur_vars := by
    rw [hobt.cv_eq]; dsimp only [other]; split <;> assumption
  have hforced_lvl : (s1.core.lvl[forced.toNat / 2]?.getD 0#32).toNat = clvl := by
    dsimp only [forced]; split
    · have : lb.toNat < la.toNat := ‹la > lb›
      rw [hobt.lvl_keep _ ha_lt hfa (by omega), ← hla_val]; omega
    · have : la.toNat ≤ lb.toNat := Nat.not_lt.mp ‹¬ la > lb›
      rw [hobt.lvl_keep _ hb_lt hfb (by omega), ← hlb_val]; omega
  have hother_lvl : (s1.core.lvl[other.toNat / 2]?.getD 0#32).toNat = jlvl := by
    dsimp only [other, jlvl]; split
    · rw [hobt.lvl_keep _ hb_lt hfb (by rw [← hlb_val]; omega), hlb_val]
    · rw [hobt.lvl_keep _ ha_lt hfa (by rw [← hla_val]; omega), hla_val]
  have hother_f : s1.core.vals[other.toNat]?.getD 0#8 = 0xFF#8 := by
    dsimp only [other]; split
    · rw [hobt.vals_keep _ hb_lt (by rw [← hlb_val]; omega)]; exact hfb
    · rw [hobt.vals_keep _ ha_lt (by rw [← hla_val]; omega)]; exact hfa
  let bin_rsn := (other &&& 0x7FFFFFFF#32) ||| 0x80000000#32
  have hbin_p := bin_rsn_mask_props (l := other) (by have := hobt.cv_eq; have := hother_lt; omega)
  have hent_fo : (cnfOfClauses F_cur).EntailsClause (cnfClause [forced.toNat, other.toNat]) := by
    dsimp only [forced, other]; split
    · exact hent
    · exact entails_of_mem_or_false hent fun l hl => Or.inl (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
        rcases hl with rfl | rfl <;> simp)
  have hj_lt32 : jlvl < 2 ^ 32 := by
    have := fullInv_max_vars_lt32 c; have := hobt.hw1.cur_level_le
    have := hobt.len1.core_ok.trail_end_le; have := hobt.cl1_eq; omega
  have hrsn_pre :
      if (bin_rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (bin_rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * s1.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [forced.toNat, ot]) ∧
        s1.core.vals[ot]?.getD 0#8 = 0xFF#8 ∧ (s1.core.lvl[ot / 2]?.getD 0#32).toNat ≤ jlvl
      else
        bin_rsn.toNat ∈ fullArenaClauseRefsCore s1.core ∧
        fullArenaClauseGarbCore s1.core bin_rsn.toNat = false ∧
        forced.toNat ∈ fullArenaClauseLitsCore s1.core bin_rsn.toNat ∧
        ∀ q ∈ fullArenaClauseLitsCore s1.core bin_rsn.toNat,
          q = forced.toNat ∨ (s1.core.vals[q]?.getD 0#8 = 0xFF#8 ∧
            (s1.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvl) := by
    dsimp only [bin_rsn]; rw [ite_eq_left hbin_p.2.1, hbin_p.2.2]
    exact ⟨hother_lt, hent_fo, hother_f, Nat.le_of_eq hother_lvl⟩
  let hpre : OneLitTailPre c F0 F_cur s s1 cut1 clvl jlvl forced bin_rsn :=
    ⟨hobt.len1, hobt.hw1, hobt.marks1, hobt.nodup1, hobt.ext1, hobt.cl1_eq, hobt.cl_le,
      hobt.cv_eq, hobt.fuel_eq, hobt.ws2_eq, hobt.dm0, hobt.prob_eq, hforced_lt, hforced_lvl,
      hbin_p.1, hrsn_pre⟩
  fa_fast_steps_nogrp
  exact oneLit_after_bt_assign_wp hAss hpre (bv64_ofNat_toNat (lt_trans hj_lt32 (by decide)))
    hj_lt32 hjl_le_nl hnl_lt hlen2 hcl2_eq rfl hpres.2.2.1 hpres.1.1 hpres.1.2 hobt.dm0 rfl rfl
    rfl rfl rfl rfl hvals2 hlvl2 hw2' hm2 hQ

private def OneLitScanInv (s : FullState) (cref forcedv : BitVec 32)
    (csz_val i : Nat) (clvlv jlvlv cntv : BitVec 64) : Prop :=
  i ≤ csz_val ∧ clvlv.toNat ≤ s.core.cur_level ∧ jlvlv.toNat ≤ s.core.cur_level ∧
  cntv.toNat ≤ i ∧
  (i = 0 → clvlv = 0#64 ∧ jlvlv = 0#64 ∧ cntv = 0#64 ∧ forcedv = 0xFFFFFFFF#32) ∧
  (0 < i → 1 ≤ cntv.toNat ∧
    (∀ q < i, (s.core.lvl[(s.core.arena[cref.toNat + 3 + q]?.getD 0#32).toNat / 2]?.getD
      0#32).toNat ≤ clvlv.toNat) ∧
    (∃ q < i, (s.core.lvl[(s.core.arena[cref.toNat + 3 + q]?.getD 0#32).toNat / 2]?.getD
      0#32).toNat = clvlv.toNat)) ∧
  (0 < i → cntv = 1#64 → ∃ q_f < i,
    forcedv = s.core.arena[cref.toNat + 3 + q_f]?.getD 0#32 ∧
    (s.core.lvl[forcedv.toNat / 2]?.getD 0#32).toNat = clvlv.toNat ∧
    (0 < clvlv.toNat → jlvlv.toNat < clvlv.toNat) ∧
    ∀ q' < i, q' ≠ q_f →
      (s.core.lvl[(s.core.arena[cref.toNat + 3 + q']?.getD 0#32).toNat / 2]?.getD
        0#32).toNat ≤ jlvlv.toNat)

private theorem oneLit_scan_bds {c : FullCfg} {s : FullState} {cref : BitVec 32}
    {csz_val i : Nat} (hlen : s.LengthsOk c) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hcap : c.arena_cap < 2 ^ 31 - 1) (hcsz_bd : cref.toNat + 3 + csz_val ≤ s.core.arena_len)
    (hilt : i < csz_val) (hl_lt : (s.core.arena[cref.toNat + 3 + i]?.getD 0#32).toNat <
      2 * s.core.cur_vars) (hcref_eq : cref = s.core.confl_ref.setWidth 32) :
    let li := s.core.arena[cref.toNat + 3 + i]'(by
      have := hlen.core_ok.arena_len_arr; have := hlen.core_ok.arena_len_le; omega)
    let ll : BitVec 64 := (s.core.lvl[li.toNat / 2]?.getD 0#32).setWidth 64
    ∃ (hz_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i).setWidth 64).toNat <
        s.core.arena.length)
      (hc_bd : (s.core.confl_ref.toNat % 2 ^ 32 + BitVec.toNat (3 : BitVec 64) +
        i % 2 ^ 32) % 2 ^ 64 < s.core.arena.length),
      (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i).setWidth 64).toNat = cref.toNat + 3 + i ∧
      s.core.arena[cref.toNat + 3 + i]?.getD 0#32 = li ∧
      ll.toNat = (s.core.lvl[(s.core.arena[cref.toNat + 3 + i]?.getD 0#32).toNat / 2]?.getD
        0#32).toNat ∧
      s.core.arena[(cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i).setWidth 64).toNat]'hz_bd = li ∧
      ((s.core.arena[(cref.setWidth 64 + 3#64 +
        (BitVec.ofNat 32 i).setWidth 64).toNat]'hz_bd >>> 1).setWidth 64).toNat <
        s.core.lvl.length ∧
      (s.core.arena[(s.core.confl_ref.toNat % 2 ^ 32 + BitVec.toNat (3 : BitVec 64) +
        i % 2 ^ 32) % 2 ^ 64]'hc_bd).toNat / 2 < s.core.lvl.length ∧
      (∀ pf1 pf2, BitVec.setWidth 64 (s.core.lvl[(BitVec.setWidth 64
        (s.core.arena[((s.core.confl_ref.setWidth 32).setWidth 64 + 3 +
          (BitVec.ofNat 32 i).setWidth 64).toNat]'pf1 >>> 1)).toNat]'pf2) = ll) := by
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hlvl_len := hlen.core_ok.lvl_len
  have hcr_i_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i).setWidth 64).toNat =
      cref.toNat + 3 + i := by
    have : cref.toNat < 2 ^ 31 - 1 := by omega
    rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat cref (by decide),
      zext_toNat (BitVec.ofNat 32 i) (by decide), bv32_ofNat_toNat (by omega)]
    simp only [BitVec.reduceToNat]; omega
  have hcr_eq : cref.toNat = s.core.confl_ref.toNat % 2 ^ 32 := by
    rw [hcref_eq, BitVec.toNat_setWidth]
  have hc_idx : (s.core.confl_ref.toNat % 2 ^ 32 + BitVec.toNat (3 : BitVec 64) +
      i % 2 ^ 32) % 2 ^ 64 = cref.toNat + 3 + i := by
    rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl, ← hcr_eq]; omega
  have hz_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i).setWidth 64).toNat <
      s.core.arena.length := by rw [hcr_i_bd]; omega
  have hc_bd : (s.core.confl_ref.toNat % 2 ^ 32 + BitVec.toNat (3 : BitVec 64) +
      i % 2 ^ 32) % 2 ^ 64 < s.core.arena.length := by rw [hc_idx]; omega
  intro li ll
  have hli_get : s.core.arena[cref.toNat + 3 + i]?.getD 0#32 = li := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hll_val : ll.toNat = (s.core.lvl[(s.core.arena[cref.toNat + 3 + i]?.getD
      0#32).toNat / 2]?.getD 0#32).toNat := by
    dsimp only [ll, li]; rw [hli_get, BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
    exact Nat.lt_trans (BitVec.isLt _) (by decide)
  have hli_idx : ∀ pf, s.core.arena[(cref.setWidth 64 + 3#64 +
      (BitVec.ofNat 32 i).setWidth 64).toNat]'pf = li := fun _ => getElem_eq_of_idx hcr_i_bd
  have hli_var : li.toNat / 2 < s.core.cur_vars := by
    rw [← hli_get]; exact Nat.div_lt_of_lt_mul hl_lt
  have hbd_lvl : li.toNat / 2 < s.core.lvl.length := by
    rw [hlvl_len]; exact Nat.lt_of_lt_of_le hli_var hcv_le
  refine ⟨hz_bd, hc_bd, hcr_i_bd, hli_get, hll_val, hli_idx hz_bd, ?_, ?_, fun pf1 pf2 => ?_⟩
  · rw [bv_c0_zext32_64, bv32_lshr_1, hli_idx hz_bd]; exact hbd_lvl
  · rw [getElem_eq_of_idx hc_idx]; exact hbd_lvl
  · dsimp only [ll]; congr 1; rw [List.getElem?_eq_getElem hbd_lvl, Option.getD_some]
    exact getElem_eq_of_idx (by
      rw [bv_c0_zext32_64, bv32_lshr_1]
      have ha_li : s.core.arena[((s.core.confl_ref.setWidth 32).setWidth 64 + 3 +
          (BitVec.ofNat 32 i).setWidth 64).toNat]'pf1 = li :=
        (getElem_eq_of_idx (hj := hz_bd)
          (by rw [← hcref_eq, show (3 : BitVec 64) = 3#64 from rfl])).trans (hli_idx hz_bd)
      rw [ha_li])

private theorem oneLit_large_push_inv_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut1 clvl jlvl : Nat} {s s1 s2 s3 : FullState} {wv4 ws4 wso4 : List (BitVec 32)}
    {wu4 : BitVec 64} {wl4 : Nat} {cref forcedv l1 : BitVec 32}
    (hobt : OneLitBtInv c F0 F_cur s s1 cut1 clvl)
    (hs2_base : ∃ wv2 ws2 wu2, s2.core = { s1.core with wvec := wv2, wstk := ws2, wusable := wu2 })
    (hs3_c : s3.core = { s2.core with arena := s3.core.arena }) (hs3_sc : s3.scratch = s1.scratch)
    (hdm3 : s3.core.dense_mode = 0#64) (hcv3 : s3.core.cur_vars = s1.core.cur_vars)
    (hw3' : FullWitnessCutInv c F0 F_cur cut1 s3.core) (hnd3 : FullArenaVarsNodup s3)
    (hext3 : FullExtScratchOk c s3) (hcref3 : cref.toNat ∈ fullArenaClauseRefsCore s3.core)
    (hng3 : fullArenaClauseGarbCore s3.core cref.toNat = false)
    (hperm3 : (fullArenaClauseLitsCore s3.core cref.toNat).Perm
      (fullArenaClauseLitsCore s1.core cref.toNat))
    (hforced_m : forcedv.toNat ∈ fullArenaClauseLits s cref.toNat ∧
      forcedv.toNat < 2 * s.core.cur_vars)
    (hm_s1 : forcedv.toNat ∈ fullArenaClauseLitsCore s1.core cref.toNat)
    (hconfl_other : ∀ s_c : FullState,
      (∀ q ∈ fullArenaClauseLitsCore s_c.core cref.toNat,
        q ∈ fullArenaClauseLitsCore s1.core cref.toNat) →
      ∀ q ∈ fullArenaClauseLitsCore s_c.core cref.toNat, q = forcedv.toNat ∨
        (s1.core.vals[q]?.getD 0#8 = 0xFF#8 ∧ (s1.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvl))
    (hcr32 : cref.toNat < 2 ^ 31 - 1) (hw0_and : ((l1 &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32)
    (hlen4 : ({ s3 with
      core := { s3.core with wvec := wv4, wstk := ws4, wlen := wl4, wusable := wu4 }
      scratch := { s3.scratch with wsort := wso4 } } : FullState).LengthsOk c)
    (hlay4 : WatchStackLayout
      { s3.core with wvec := wv4, wstk := ws4, wlen := wl4, wusable := wu4 })
    (hother4 : ∀ l < 2 * s3.core.cur_vars, l ≠ forcedv.toNat →
      let k' : FullCoreState :=
        { s3.core with wvec := wv4, wstk := ws4, wlen := wl4, wusable := wu4 }
      fullWatchSizeCore k' l = fullWatchSizeCore s3.core l ∧
      ∀ k < fullWatchSizeCore s3.core l,
        ws4[fullWatchOffCore k' l + k]? = s3.core.wstk[fullWatchOffCore s3.core l + k]?)
    (ok4 : Bool)
    (hok4t : ok4 = true →
      let k' : FullCoreState :=
        { s3.core with wvec := wv4, wstk := ws4, wlen := wl4, wusable := wu4 }
      forcedv.toNat < 2 * s3.core.cur_vars ∧
      ((2 : BitVec 32).toNat = 1 ∨ (2 : BitVec 32).toNat = 2) ∧
      fullWatchSizeCore k' forcedv.toNat =
        fullWatchSizeCore s3.core forcedv.toNat + (2 : BitVec 32).toNat ∧
      (∀ k < fullWatchSizeCore s3.core forcedv.toNat,
        ws4[fullWatchOffCore k' forcedv.toNat + k]? =
          s3.core.wstk[fullWatchOffCore s3.core forcedv.toNat + k]?) ∧
      ws4[fullWatchOffCore k' forcedv.toNat + fullWatchSizeCore s3.core forcedv.toNat]? =
        some (l1 &&& 0x7FFFFFFF#32) ∧
      ((2 : BitVec 32).toNat = 2 →
        ws4[fullWatchOffCore k' forcedv.toNat + fullWatchSizeCore s3.core forcedv.toNat + 1]? =
          some cref))
    (hok4f : ok4 = false →
      let k' : FullCoreState :=
        { s3.core with wvec := wv4, wstk := ws4, wlen := wl4, wusable := wu4 }
      (forcedv.toNat < 2 * s3.core.cur_vars →
        fullWatchSizeCore k' forcedv.toNat = fullWatchSizeCore s3.core forcedv.toNat ∧
        ∀ k < fullWatchSizeCore s3.core forcedv.toNat,
          ws4[fullWatchOffCore k' forcedv.toNat + k]? =
            s3.core.wstk[fullWatchOffCore s3.core forcedv.toNat + k]?) ∧
      (2 * s3.core.cur_vars ≤ forcedv.toNat ∨
        ((2 : BitVec 32).toNat ≠ 1 ∧ (2 : BitVec 32).toNat ≠ 2) ∨
        ({ s3 with core := k', scratch := { s3.scratch with wsort := wso4 } } : FullState) = s3 ∨
        wu4 = 0#64)) :
    let s4_r : FullState :=
      { s3 with
        core := { s3.core with wvec := wv4, wstk := ws4, wlen := wl4, wusable := wu4 }
        scratch := { s3.scratch with wsort := wso4 } }
    (ok4 = true → s4_r.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut1 s4_r.core ∧
      FullLitMarksClear c s4_r ∧ FullArenaVarsNodup s4_r ∧ FullExtScratchOk c s4_r ∧
      s4_r.core.cur_level = clvl ∧ s4_r.core.cur_vars = s.core.cur_vars ∧
      s4_r.core.fuel = s.core.fuel ∧ s4_r.scratch.work_stk2 = s.scratch.work_stk2 ∧
      s4_r.core.dense_mode = 0#64 ∧ s4_r.core.probing = s.core.probing ∧
      s4_r.core.lvl = s1.core.lvl ∧ cref.toNat ∈ fullArenaClauseRefsCore s4_r.core ∧
      fullArenaClauseGarbCore s4_r.core cref.toNat = false ∧
      forcedv.toNat ∈ fullArenaClauseLitsCore s4_r.core cref.toNat ∧
      ∀ q ∈ fullArenaClauseLitsCore s4_r.core cref.toNat, q = forcedv.toNat ∨
        (s4_r.core.vals[q]?.getD 0#8 = 0xFF#8 ∧ (s4_r.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvl)) ∧
    (ok4 = false → let s4_o : FullState := { s4_r with core := { s4_r.core with oom := 1#64 } }
      s4_o.LengthsOk c ∧ s4_o.core.cur_vars = s.core.cur_vars ∧ s4_o.core.fuel = s.core.fuel ∧
      s4_o.scratch.work_stk2 = s.scratch.work_stk2 ∧ s4_o.core.dense_mode = 0#64 ∧
      s4_o.core.probing = s.core.probing ∧ FullLitMarksClear c s4_o ∧ FullArenaVarsNodup s4_o ∧
      FullExtScratchOk c s4_o ∧ FullOtfsWitnessInv c F0 F_cur s4_o.core) := by
  intro s4_r; obtain ⟨wv2, ws2, wu2, hs2_c⟩ := hs2_base
  have hnd4 : FullArenaVarsNodup s4_r := fun r hr hgr => by
    change r ∈ fullArenaClauseRefsCore s4_r.core at hr
    change fullArenaClauseGarbCore s4_r.core r = false at hgr
    change ((fullArenaClauseLitsCore s4_r.core r).map (· / 2)).Nodup
    exact hnd3 r hr hgr
  have hext4 : FullExtScratchOk c s4_r := hext3
  refine ⟨fun ht => ?_, fun hf => ?_⟩
  · obtain ⟨_, _, hsz4, hsame4, hw04, hw14⟩ := hok4t ht
    have hw_k4 : ModeWatchesInv F_cur s4_r.core :=
      fa_watchPush_large_preserves hdm3 hw3'.watches
        (by rw [hcv3, hobt.cv_eq]; exact hforced_m.2) hlay4 hother4 hsz4 hsame4 hw04
        (hw14 rfl) hw0_and (by omega) hcref3
    have hperm4 : (fullArenaClauseLitsCore s4_r.core cref.toNat).Perm
        (fullArenaClauseLitsCore s1.core cref.toNat) := hperm3
    have hs4_r_vals : s4_r.core.vals = s1.core.vals := by dsimp [s4_r]; rw [hs3_c, hs2_c]
    have hs4_r_lvl : s4_r.core.lvl = s1.core.lvl := by dsimp [s4_r]; rw [hs3_c, hs2_c]
    refine ⟨⟨{ hlen4.core_ok with }, hlen4.scratch_ok⟩, cutInv_with_watches hw3' hw_k4,
      ⟨fun v hv => by
         change s3.core.mrk[v]?.getD 0#8 = 0#8; rw [hs3_c, hs2_c]; exact hobt.marks1.1 v hv,
       fun l hl => by
         change s3.core.lit_mark[l]?.getD 0#8 = 0#8; rw [hs3_c, hs2_c]; exact hobt.marks1.2 l hl⟩,
      hnd4, hext4, by rw [show s4_r.core.cur_level = s3.core.cur_level from rfl, hs3_c, hs2_c]
                      exact hobt.cl1_eq,
      by rw [show s4_r.core.cur_vars = s3.core.cur_vars from rfl, hcv3]; exact hobt.cv_eq,
      by rw [show s4_r.core.fuel = s3.core.fuel from rfl, hs3_c, hs2_c]; exact hobt.fuel_eq,
      by rw [show s4_r.scratch.work_stk2 = s3.scratch.work_stk2 from rfl, hs3_sc]
         exact hobt.ws2_eq,
      hdm3,
      by rw [show s4_r.core.probing = s3.core.probing from rfl, hs3_c, hs2_c]; exact hobt.prob_eq,
      by rw [show s4_r.core.lvl = s3.core.lvl from rfl, hs3_c, hs2_c], hcref3, hng3,
      hperm4.symm.mem_iff.mp hm_s1,
      fun q hq => by
        simpa only [hs4_r_vals, hs4_r_lvl] using
          hconfl_other s4_r (fun q hq => hperm4.mem_iff.mp hq) q hq⟩
  · obtain ⟨hsame4, _⟩ := hok4f hf
    have hw_k4 := fa_watchPush_fail_preserves hdm3 hw3'.watches hlay4 fun l hl =>
      if hle : l = forcedv.toNat then
        by subst l; exact hsame4 (by rw [hcv3, hobt.cv_eq]; exact hforced_m.2)
      else hother4 l hl hle
    exact ⟨⟨{ hlen4.core_ok with }, hlen4.scratch_ok⟩,
      by dsimp [s4_r]; rw [hcv3]; exact hobt.cv_eq,
      by dsimp [s4_r]; rw [hs3_c, hs2_c]; exact hobt.fuel_eq,
      by dsimp [s4_r]; rw [hs3_sc]; exact hobt.ws2_eq, hdm3,
      by dsimp [s4_r]; rw [hs3_c, hs2_c]; exact hobt.prob_eq,
      ⟨fun v hv => by dsimp [s4_r]; rw [hs3_c, hs2_c]; exact hobt.marks1.1 v hv,
       fun l hl => by dsimp [s4_r]; rw [hs3_c, hs2_c]; exact hobt.marks1.2 l hl⟩,
      hnd4, hext4,
      otfsInv_with_oom (cutInv_with_watches hw3' (by simpa [s4_r] using hw_k4)).toFullOtfsWitnessInv
        1#64⟩

private def oneLitTailExpr (hdr jlvlv : BitVec 64) (forcedv cref : BitVec 32) :
    Expr Val Cont [i64] :=
  Expr.call (as := [i64, i64]) "full_det_new_level" (Arg.var hdr, Arg.var jlvlv, ())
    fun (p_29 : Tup Val [i64]) =>
      Expr.call (as := [i64, i64]) "full_backtrack" (Arg.var hdr, Arg.var p_29.fst, ())
        fun (_ : Tup Val []) =>
          Expr.let_ (Op.mk (.trunc 64 32) (Arg.var jlvlv, ())) fun p_31 =>
            Expr.call (as := [i64, i32, i32, i32]) "full_assign_lvl"
              (Arg.var hdr, Arg.var forcedv, Arg.var cref, Arg.var p_31.fst, ())
              fun (_ : Tup Val []) => Expr.ret (Arg.imm 1#64, ())

private theorem oneLit_large_tail_exec_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut1 clvl : Nat} {s sb : FullState}
    {cref forcedv : BitVec 32} {jlvlv : BitVec 64} {R : Mem 64 → Prop} {Q : Post [i64]}
    {X : XPost} {mb : Mem 64}
    (hDet : ∀ args m Q X, fullDetNewLevelSpec args m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] args m Q X)
    (hBt : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hAss : ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hobt_le : clvl ≤ s.core.cur_level) (hcl_pos : 0 < clvl) (hjl_lt : jlvlv.toNat < clvl)
    (hcr32 : cref.toNat < 2 ^ 31 - 1)
    (hbref : cref.toNat ∈ fullArenaClauseRefsCore sb.core)
    (hbng : fullArenaClauseGarbCore sb.core cref.toNat = false)
    (hbfmem : forcedv.toNat ∈ fullArenaClauseLitsCore sb.core cref.toNat)
    (hbfoth : ∀ q ∈ fullArenaClauseLitsCore sb.core cref.toNat,
      q = forcedv.toNat ∨ (sb.core.vals[q]?.getD 0#8 = 0xFF#8 ∧
        (sb.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvlv.toNat))
    (hblen : sb.LengthsOk c) (hbw : FullWitnessCutInv c F0 F_cur cut1 sb.core)
    (hbmk : FullLitMarksClear c sb) (hbnd : FullArenaVarsNodup sb)
    (hbext : FullExtScratchOk c sb) (hbcl : sb.core.cur_level = clvl)
    (hbcv : sb.core.cur_vars = s.core.cur_vars) (hbfu : sb.core.fuel = s.core.fuel)
    (hbws2 : sb.scratch.work_stk2 = s.scratch.work_stk2) (hbdm : sb.core.dense_mode = 0#64)
    (hbpr : sb.core.probing = s.core.probing)
    (hf_lvl_sb : (sb.core.lvl[forcedv.toNat / 2]?.getD 0#32).toNat = clvl)
    (hf_lt : forcedv.toNat < 2 * s.core.cur_vars)
    (hmb : (FullMem c sb ⋆ R) mb) (hQ : OneLitPost c F0 F_cur s R Q) :
    wp Γ Q X (oneLitTailExpr c.hdr jlvlv forcedv cref) mb := by
  have hj_lt_cl : jlvlv.toNat < sb.core.cur_level := by rw [hbcl]; exact hjl_lt
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  unfold oneLitTailExpr; c0_call hDet
  refine ⟨c, sb, R, rfl, hblen, by
    have := hbw.cur_level_le; have := hblen.core_ok.trail_end_le
    have := hblen.core_ok.cur_vars_le; omega,
    hmb, fun nlvl _ hnlvl => ?_⟩
  obtain ⟨hjl_le_nl, hnl_lt⟩ := hnlvl (by omega) hj_lt_cl; rw [hbcl] at hnl_lt
  c0_call hBt
  refine ⟨c, sb, R, rfl, hblen, by
    have := hbw.cur_level_le; have := hblen.core_ok.trail_end_le
    have := hblen.core_ok.cur_vars_le; omega,
    fun h => by have := hbw.cur_level_le; have := hblen.core_ok.trail_end_le
                have := hblen.core_ok.cur_vars_le; omega,
    hbw.trail_lits_lt, hmb, ?_⟩
  dsimp only
  intro vals2 lvl2 rsns2 trl2 tp2 te2 prop2 cl2 unass2 sc2 m2 hlen2 _ _ hcl2 hpres _ _ hvl2 _ hw2
    hm2
  have hcl2_eq : cl2 = nlvl.toNat := by rw [hcl2, hbcl]; omega
  have hw2' := hw2 F0 F_cur hbw.toFullOtfsWitnessInv (by rw [hbcl]; exact hnl_lt)
  obtain ⟨hvals2, hlvl2⟩ := hvl2 ⟨F0, F_cur, Or.inr hbw.toFullOtfsWitnessInv⟩
  have hcref_ne : cref ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff hcr32
  have hcref_lg : (cref &&& 0x80000000#32) = 0#32 :=
    (bv32_lit_lo31_props (Nat.lt_trans hcr32 (by omega))).2.2
  have hrsn_pre :
      if (cref &&& 0x80000000#32) ≠ 0#32 then
        let ot := (cref &&& 0x7FFFFFFF#32).toNat
        ot < 2 * sb.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause
          (cnfClause [forcedv.toNat, ot]) ∧
        sb.core.vals[ot]?.getD 0#8 = 0xFF#8 ∧ (sb.core.lvl[ot / 2]?.getD 0#32).toNat ≤ jlvlv.toNat
      else
        cref.toNat ∈ fullArenaClauseRefsCore sb.core ∧
        fullArenaClauseGarbCore sb.core cref.toNat = false ∧
        forcedv.toNat ∈ fullArenaClauseLitsCore sb.core cref.toNat ∧
        ∀ q ∈ fullArenaClauseLitsCore sb.core cref.toNat,
          q = forcedv.toNat ∨ (sb.core.vals[q]?.getD 0#8 = 0xFF#8 ∧
            (sb.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvlv.toNat) := by
    rw [ite_eq_right (fun h => absurd hcref_lg h)]; exact ⟨hbref, hbng, hbfmem, hbfoth⟩
  let hpre : OneLitTailPre c F0 F_cur s sb cut1 clvl jlvlv.toNat forcedv cref :=
    ⟨hblen, hbw, hbmk, hbnd, hbext, hbcl, hobt_le, hbcv, hbfu, hbws2, hbdm, hbpr,
      hbcv ▸ hf_lt, hf_lvl_sb, hcref_ne, hrsn_pre⟩
  fa_fast_steps_nogrp
  exact oneLit_after_bt_assign_wp hAss hpre rfl
    (by have := fullInv_max_vars_lt32 c; have := hbw.cur_level_le
        have := hblen.core_ok.trail_end_le; omega)
    hjl_le_nl hnl_lt hlen2 hcl2_eq rfl hpres.2.2.1 hpres.1.1 hpres.1.2 hbdm rfl rfl rfl rfl rfl
    rfl hvals2 hlvl2 hw2' hm2 hQ

private def oneLitPushExpr (hdr pAr : BitVec 64) (l0 cref forcedv qf32 : BitVec 32)
    (Jtail : Cont []) : Expr Val Cont [i64] :=
  Expr.call (as := [i64, i32, i32]) "full_unwatch_large"
      (Arg.var hdr, Arg.var l0, Arg.var cref, ()) fun (_ : Tup Val []) =>
    Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p_34 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var p_34.fst, Arg.imm 3, ())) fun p_35 =>
    Expr.let_ (Op.mk (.mul i64) (Arg.var p_35.fst, Arg.imm 4, ())) fun p_36 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var pAr, Arg.var p_36.fst, ())) fun p_37 =>
    Expr.store (t := i32) (Arg.var forcedv) (Arg.var p_37.fst)
      (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p_38 =>
      Expr.let_ (Op.mk (.add i64) (Arg.var p_38.fst, Arg.imm 3, ())) fun p_39 =>
      Expr.let_ (Op.mk (.zext 32 64) (Arg.var qf32, ())) fun p_40 =>
      Expr.let_ (Op.mk (.add i64) (Arg.var p_39.fst, Arg.var p_40.fst, ())) fun p_41 =>
      Expr.let_ (Op.mk (.mul i64) (Arg.var p_41.fst, Arg.imm 4, ())) fun p_42 =>
      Expr.let_ (Op.mk (.add i64) (Arg.var pAr, Arg.var p_42.fst, ())) fun p_43 =>
      Expr.store (t := i32) (Arg.var l0) (Arg.var p_43.fst)
        (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p_44 =>
        Expr.let_ (Op.mk (.add i64) (Arg.var p_44.fst, Arg.imm 4, ())) fun p_45 =>
        Expr.let_ (Op.mk (.mul i64) (Arg.var p_45.fst, Arg.imm 4, ())) fun p_46 =>
        Expr.let_ (Op.mk (.add i64) (Arg.var pAr, Arg.var p_46.fst, ())) fun p_47 =>
        Expr.load i32 (Arg.var p_47.fst) fun ld =>
        Expr.let_ (Op.mk (.and i32) (Arg.var ld, Arg.imm 2147483647, ())) fun p_48 =>
        Expr.call (as := [i64, i32, i32, i32, i32]) "full_watch_push"
          (Arg.var hdr, Arg.var forcedv, Arg.var p_48.fst, Arg.var cref, Arg.imm 2, ())
          fun (p_49 : Tup Val [.bool]) =>
        Expr.jnz (Arg.var p_49.fst) (Expr.jump Jtail ())
          (Expr.let_ (Op.mk (.add i64) (Arg.var hdr, Arg.imm 760, ())) fun p =>
          Expr.store (t := i64) (Arg.imm 1) (Arg.var p.fst) (Expr.ret (Arg.imm 2, ())))))

private theorem oneLit_large_push_branch_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut1 clvl jlvl q_f csz_val : Nat} {s s1 : FullState}
    {cref l0 l1 forcedv : BitVec 32} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {Jtail : Cont []} {m1 : Mem 64}
    (hUnw : ∀ args m Q X, fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X)
    (hPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hobt : OneLitBtInv c F0 F_cur s s1 cut1 clvl)
    (hbin : s.core.confl_type ≠ 1#64)
    (hcr32 : cref.toNat < 2 ^ 31 - 1) (hcsz_ge3 : 3 ≤ csz_val)
    (hqf_ge2 : 2 ≤ q_f) (hqf_lt : q_f < csz_val)
    (hcsz_bd : cref.toNat + 3 + csz_val ≤ s.core.arena_len)
    (hcref1_ref : cref.toNat ∈ fullArenaClauseRefsCore s1.core)
    (hcref1_ng : fullArenaClauseGarbCore s1.core cref.toNat = false)
    (hcref1_sz : fullArenaClauseSizeCore s1.core cref.toNat = csz_val)
    (hl0 : l0 = s1.core.arena[cref.toNat + 3]?.getD 0#32)
    (hl1 : l1 = s1.core.arena[cref.toNat + 4]?.getD 0#32)
    (hfq_eq : forcedv = s.core.arena[cref.toNat + 3 + q_f]?.getD 0#32)
    (hf_m : forcedv.toNat < 2 * s.core.cur_vars)
    (hm_s1 : forcedv.toNat ∈ fullArenaClauseLitsCore s1.core cref.toNat)
    (hconfl_lits_other : ∀ s_c : FullState,
      (∀ q ∈ fullArenaClauseLitsCore s_c.core cref.toNat,
        q ∈ fullArenaClauseLitsCore s1.core cref.toNat) →
      ∀ q ∈ fullArenaClauseLitsCore s_c.core cref.toNat,
        q = forcedv.toNat ∨ (s1.core.vals[q]?.getD 0#8 = 0xFF#8 ∧
          (s1.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvl))
    (hm1 : (FullMem c s1 ⋆ R) m1) (hQ : OneLitPost c F0 F_cur s R Q)
    (hJtail : ∀ mb,
      (∃ sb : FullState, sb.core.lvl = s1.core.lvl ∧
        cref.toNat ∈ fullArenaClauseRefsCore sb.core ∧
        fullArenaClauseGarbCore sb.core cref.toNat = false ∧
        forcedv.toNat ∈ fullArenaClauseLitsCore sb.core cref.toNat ∧
        (∀ q ∈ fullArenaClauseLitsCore sb.core cref.toNat,
          q = forcedv.toNat ∨ (sb.core.vals[q]?.getD 0#8 = 0xFF#8 ∧
            (sb.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvl)) ∧
        sb.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut1 sb.core ∧
        FullLitMarksClear c sb ∧ FullArenaVarsNodup sb ∧ FullExtScratchOk c sb ∧
        sb.core.cur_level = clvl ∧ sb.core.cur_vars = s.core.cur_vars ∧
        sb.core.fuel = s.core.fuel ∧ sb.scratch.work_stk2 = s.scratch.work_stk2 ∧
        sb.core.dense_mode = 0#64 ∧ sb.core.probing = s.core.probing ∧ (FullMem c sb ⋆ R) mb) →
      Jtail () mb) :
    wp Γ Q X (oneLitPushExpr c.hdr c.pArena l0 cref forcedv (BitVec.ofNat 32 q_f) Jtail) m1 := by
  have har_cap := c.harena; unfold dimacsBound at har_cap
  have har1_len := hobt.len1.core_ok.arena_len_arr
  have har1_le := hobt.len1.core_ok.arena_len_le
  have hcsz_cap : cref.toNat + 3 + csz_val ≤ c.arena_cap := by
    have := hobt.arena_len_eq; omega
  have hcr3_bd : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3 := by
    rw [BitVec.toNat_add, zext_toNat cref (by decide)]; simp only [BitVec.reduceToNat]; omega
  have hcr4_bd : (cref.setWidth 64 + 4#64).toNat = cref.toNat + 4 := by
    rw [BitVec.toNat_add, zext_toNat cref (by decide)]; simp only [BitVec.reduceToNat]; omega
  have hcr_qf_z : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 q_f).setWidth 64).toNat =
      cref.toNat + 3 + q_f := by
    rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat cref (by decide),
      zext_toNat (BitVec.ofNat 32 q_f) (by decide), bv32_ofNat_toNat (by omega)]
    simp only [BitVec.reduceToNat]; omega
  have hlay1 : WatchStackLayout s1.core := by
    have h := hobt.hw1.watches; unfold ModeWatchesInv at h
    simp only [hobt.dm0, ↓reduceIte] at h; exact h.layout
  unfold oneLitPushExpr; c0_call hUnw
  refine ⟨c, s1, R, rfl, hobt.len1, hlay1, hm1, fun wv2 ws2 wu2 m2 hlen2 _ hmw2 hm2 => ?_⟩
  obtain ⟨s2, hs2_eq, hm2'⟩ : ∃ s2 : FullState,
      s2 = { s1 with core := { s1.core with wvec := wv2, wstk := ws2, wusable := wu2 } } ∧
      (FullMem c s2 ⋆ R) m2 := ⟨_, rfl, hm2⟩
  clear hm1 hm2
  have hs2_c : s2.core = { s1.core with wvec := wv2, wstk := ws2, wusable := wu2 } :=
    congrArg FullState.core hs2_eq
  have hs2_sc : s2.scratch = s1.scratch := by rw [hs2_eq]
  have hlen2' : s2.LengthsOk c := by
    rw [hs2_eq]; exact ⟨{ hlen2.core_ok with }, hlen2.scratch_ok⟩
  have hw2 : FullWitnessCutInv c F0 F_cur cut1 s2.core := by
    rw [hs2_eq]; exact cutInv_with_watches hobt.hw1 (hmw2 F_cur hobt.hw1.watches)
  have hnd2 : FullArenaVarsNodup s2 := by rw [hs2_eq]; exact hobt.nodup1
  have hext2 : FullExtScratchOk c s2 := by rw [hs2_eq]; exact hobt.ext1
  have hcref2_ref : cref.toNat ∈ fullArenaClauseRefsCore s2.core := by
    rw [hs2_c]; exact hcref1_ref
  have hcref2_ng : fullArenaClauseGarbCore s2.core cref.toNat = false := by
    rw [hs2_c]; exact hcref1_ng
  have hcref2_sz : fullArenaClauseSizeCore s2.core cref.toNat = csz_val := by
    rw [hs2_c]; exact hcref1_sz
  obtain ⟨hlen3_r, hw3_r, hnd3_r, hext3_r, _, hcref3_r, hng3_r, _, hperm3⟩ :=
    oneLit_swap_arena_inv hlen2' hw2 hnd2 hext2 hcref2_ref hcref2_ng hcref2_sz
      (i := 0) (j := q_f) (by omega) hqf_lt l0 forcedv
      (by rw [hs2_c]; exact hl0) (by rw [hs2_c, hobt.arena_eq, hfq_eq])
  let ar3_raw := (s2.core.arena.set (cref.setWidth 64 + 3).toNat forcedv).set
    (cref.setWidth 64 + 3 + (BitVec.ofNat 32 q_f).setWidth 64).toNat l0
  let ar3 := (s2.core.arena.set (cref.toNat + 3) forcedv).set (cref.toNat + 3 + q_f) l0
  have har3_eq : ar3_raw = ar3 := by
    dsimp only [ar3_raw, ar3]
    rw [list_set_congr (show (cref.setWidth 64 + 3 + (BitVec.ofNat 32 q_f).setWidth 64).toNat =
          cref.toNat + 3 + q_f from hcr_qf_z) rfl,
        list_set_congr (show (cref.setWidth 64 + 3).toNat = cref.toNat + 3 from hcr3_bd) rfl]
  let s3 : FullState := { s2 with core := { s2.core with arena := ar3 } }
  clear hlen2
  have hs3_c : s3.core = { s2.core with arena := ar3 } := rfl
  have hs3_sc : s3.scratch = s1.scratch := by rw [hs2_sc]
  have hperm3_s : (fullArenaClauseLitsCore s3.core cref.toNat).Perm
      (fullArenaClauseLitsCore s1.core cref.toNat) := by
    rw [hs3_c]; dsimp only [ar3]
    simpa only [hs2_c, Nat.add_zero, fullArenaClauseLitsCore, fullArenaClauseSizeCore] using hperm3
  have har3_len : ar3.length = c.arena_cap := by simp [ar3, hs2_c, har1_len]
  have hcr4_cap : cref.toNat + 4 < c.arena_cap := by
    have := hobt.arena_len_eq; omega
  have hcr_qf_cap : cref.toNat + 3 + q_f < c.arena_cap := by
    have := hobt.arena_len_eq; omega
  have hw1_mask : l1 &&& 0x7FFFFFFF#32 ≠ 0xFFFFFFFF#32 := fun he => by
    have h1 := congrArg BitVec.toNat he; rw [BitVec.toNat_and] at h1
    have h2 := Nat.and_lt_two_pow l1.toNat (n := 31) (by decide : (0x7FFFFFFF#32).toNat < 2 ^ 31)
    change _ = (0xFFFFFFFF#32).toNat at h1; simp only [BitVec.reduceToNat] at h1 h2; omega
  have hcref_ne : cref ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff hcr32
  have hdm2 : s2.core.dense_mode = 0#64 := by rw [hs2_c]; exact hobt.dm0
  have hdm3 : s3.core.dense_mode = 0#64 := by rw [hs3_c]; exact hdm2
  have hlay3 : WatchStackLayout s3.core := by
    have h := hw3_r.watches; unfold ModeWatchesInv at h
    rw [ite_eq_left hdm2] at h; simpa only [s3, ar3, Nat.add_zero] using h.layout
  have hw0_and : ((l1 &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 := by
    rw [BitVec.and_assoc, show (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 from rfl, BitVec.and_zero]
  have hcr3_s2 : (cref.setWidth 64 + 3).toNat < s2.core.arena.length := by
    rw [show (cref.setWidth 64 + 3).toNat = cref.toNat + 3 from hcr3_bd, hs2_c]
    dsimp only; rw [har1_len]; omega
  have hcr_qf_s2 : (cref.setWidth 64 + 3 + (BitVec.ofNat 32 q_f).setWidth 64).toNat <
      (s2.core.arena.set (cref.setWidth 64 + 3).toNat forcedv).length := by
    simp only [List.length_set]
    rw [show (cref.setWidth 64 + 3 + (BitVec.ofNat 32 q_f).setWidth 64).toNat =
      cref.toNat + 3 + q_f from hcr_qf_z, hs2_c]
    dsimp only; rw [har1_len]; exact hcr_qf_cap
  have hcr4_raw_bd : (cref.setWidth 64 + 4).toNat < ar3_raw.length := by
    rw [har3_eq, har3_len, show (cref.setWidth 64 + 4).toNat = cref.toNat + 4 from hcr4_bd]
    exact hcr4_cap
  have hl1_goal : ∀ {pf}, ar3_raw[(cref.setWidth 64 + 4).toNat]'pf = l1 := fun {pf} =>
    Option.some.inj ((List.getElem?_eq_getElem pf).symm.trans (by
      dsimp only [ar3_raw]
      rw [show (cref.setWidth 64 + 4).toNat = cref.toNat + 4 from hcr4_bd,
        show (cref.setWidth 64 + 3).toNat = cref.toNat + 3 from hcr3_bd,
        show (cref.setWidth 64 + 3 + (BitVec.ofNat 32 q_f).setWidth 64).toNat =
          cref.toNat + 3 + q_f from hcr_qf_z,
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), hs2_c, hl1,
        List.getElem?_eq_getElem (by rw [har1_len]; exact hcr4_cap), Option.getD_some]))
  fa_fast_steps_nogrp; rw [hl1_goal]; c0_call hPush
  refine ⟨c, s3, R, rfl, hlen3_r, hlay3, fun h1 => absurd h1 (by decide),
    fun _ => ⟨hw1_mask, hcref_ne⟩,
    fullMem_of_eq hm (by rw [hs3_c]; exact congrArg (fun a => { s2.core with arena := a }) har3_eq)
      rfl,
    fun ok4 wv4 ws4 wl4 wu4 wso4 m4 hlen4 hlay4 hother4 hok4t hok4f hm4 => ?_⟩
  have hpush := oneLit_large_push_inv_ok hobt ⟨wv2, ws2, wu2, hs2_c⟩ hs3_c hs3_sc hdm3
    (by rw [hs3_c, hs2_c]) hw3_r hnd3_r hext3_r hcref3_r hng3_r hperm3_s
    ⟨by simpa only [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore,
          ← hobt.arena_eq] using hm_s1, hf_m⟩
    hm_s1 hconfl_lits_other hcr32 hw0_and hlen4 hlay4 hother4 ok4 hok4t hok4f
  dsimp only
  by_cases hok4 : ok4 = true
  · subst hok4
    obtain ⟨s4, hs4_eq, hm4'⟩ : ∃ s4 : FullState, s4 =
        { s3 with core := { s3.core with wvec := wv4, wstk := ws4, wlen := wl4, wusable := wu4 }
                  scratch := { s3.scratch with wsort := wso4 } } ∧
        (FullMem c s4 ⋆ R) m4 := ⟨_, rfl, hm4⟩
    clear hm4; obtain ⟨hlen4', hw4, hm4_k, hnd4, hext4, hcl4, hcv4, hfu4, hws4, hdm4, hpr4,
      hlvl4, hcref4, hng4, hmem4, hoth4⟩ := hpush.1 rfl
    fa_fast_steps; refine hJtail m4 ⟨s4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, hm4'⟩ <;> rw [hs4_eq] <;> assumption
  · have hok4_eq : ok4 = false := Bool.eq_false_iff.mpr hok4
    subst hok4_eq
    obtain ⟨s4, hs4_eq, hm4'⟩ : ∃ s4 : FullState, s4 =
        { s3 with core := { s3.core with wvec := wv4, wstk := ws4, wlen := wl4, wusable := wu4 }
                  scratch := { s3.scratch with wsort := wso4 } } ∧
        (FullMem c s4 ⋆ R) m4 := ⟨_, rfl, hm4⟩
    clear hm4; obtain ⟨hlen4', hcv4, hfu4, hws4, hdm4, hpr4, hm4_k, hnd4, hext4, hw4⟩ :=
      hpush.2 rfl
    fa_fast_steps
    let s4o : FullState := { s4 with core := { s4.core with oom := 1#64 } }
    have hs4o_eq : s4o = { s3 with
        core := { s3.core with wvec := wv4, wstk := ws4, wlen := wl4, wusable := wu4, oom := 1#64 }
        scratch := { s3.scratch with wsort := wso4 } } := by
      dsimp only [s4o]; rw [hs4_eq]
    refine hQ 2#64 s4o m ?_ (Or.inr (Or.inr (Or.inl rfl))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (fun h => absurd h hbin) (fun h => by cases h) (fun h => by cases h) (fun _ => ?_)
      (fun h => by cases h) hm <;> rw [hs4o_eq] <;> assumption

private theorem oneLit_bin_branch_wp (Γ : Env)
    (hDet : ∀ args m Q X, fullDetNewLevelSpec args m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] args m Q X)
    (hBt : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hAss : ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    (hlen : s.LengthsOk c) (hdm : s.core.dense_mode = 0#64)
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hmarks : FullLitMarksClear c s)
    (hnd : FullArenaVarsNodup s) (hext : FullExtScratchOk c s) (hcut_le : cut ≤ s.core.trail_end)
    (hconfl : FullConflictOkCut F_cur cut s) (hbin : s.core.confl_type = 1#64)
    (hm : (FullMem c s ⋆ R) m) (hQ : OneLitPost c F0 F_cur s R Q) :
    Func.wp Γ full_one_lit_confl_body (c.hdr, ()) m Q X := by
  have hmax32 := fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have hlvl_len := hlen.core_ok.lvl_len
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
    have := hw.cur_level_le; have := hlen.core_ok.trail_end_le; omega
  have hret_bt0 {cut1 clvl : Nat} {s1 : FullState} {m1 : Mem 64}
      (hobt : OneLitBtInv c F0 F_cur s s1 cut1 clvl)
      (hm1 : (FullMem c s1 ⋆ R) m1) : Q (0#64, ()) m1 :=
    hQ 0#64 s1 m1 hobt.len1 (Or.inl rfl) hobt.cv_eq hobt.fuel_eq hobt.ws2_eq hobt.dm0 hobt.prob_eq
      hobt.marks1 hobt.nodup1 hobt.ext1 (fun _ h => by cases h) (fun h => by cases h)
      (fun h => by cases h) (fun h => by cases h)
      (fun _ => ⟨cut1, hobt.cut1_le, hobt.hw1, hobt.cl1_eq ▸ hobt.cl_pos,
        hobt.cl1_eq ▸ hobt.cl_le, hobt.wvec_eq, hobt.wstk_eq, hobt.wlen_eq, hobt.wus_eq,
        hobt.confl1⟩) hm1
  have hconfl0 : FullConflictOkCut F_cur cut s := hconfl
  have hbin_cf : s.core.confl_lit0.toNat < 2 * s.core.cur_vars ∧
      s.core.confl_lit1.toNat < 2 * s.core.cur_vars ∧
      s.core.vals[s.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
      s.core.vals[s.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8 ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [s.core.confl_lit0.toNat, s.core.confl_lit1.toNat]) := by
    rcases hconfl.1 with ⟨_, h0, h1, fa, fb, he⟩ | ⟨hbad, _⟩
    · exact ⟨h0, h1, fa, fb, he⟩
    · exact absurd (hbin.symm.trans hbad) (by decide)
  obtain ⟨h0lt, h1lt, hfa, hfb, hent⟩ := hbin_cf
  fa_fast_steps_nogrp
  · have h0_32 : s.core.confl_lit0.toNat < 2 ^ 32 := by omega
    have h1_32 : s.core.confl_lit1.toNat < 2 ^ 32 := by omega
    let a := s.core.confl_lit0.setWidth 32; let b := s.core.confl_lit1.setWidth 32
    have ha_eq : a.toNat = s.core.confl_lit0.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h0_32]
    have hb_eq : b.toNat = s.core.confl_lit1.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h1_32]
    have ha_bd : (BitVec.setWidth 64 (a >>> 1)).toNat < s.core.lvl.length := by
      rw [bv_c0_zext32_64, bv32_lshr_1, hlvl_len, ha_eq]; omega
    have hb_bd : (BitVec.setWidth 64 (b >>> 1)).toNat < s.core.lvl.length := by
      rw [bv_c0_zext32_64, bv32_lshr_1, hlvl_len, hb_eq]; omega
    let la := s.core.lvl[(BitVec.setWidth 64 (a >>> 1)).toNat]'ha_bd
    let lb := s.core.lvl[(BitVec.setWidth 64 (b >>> 1)).toNat]'hb_bd
    have hla_64 : la.setWidth 64 = BitVec.ofNat 64 la.toNat := BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_setWidth, bv64_ofNat_toNat (by omega), Nat.mod_eq_of_lt (by omega)])
    have hlb_64 : lb.setWidth 64 = BitVec.ofNat 64 lb.toNat := BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_setWidth, bv64_ofNat_toNat (by omega), Nat.mod_eq_of_lt (by omega)])
    have hla_val : la.toNat = (s.core.lvl[a.toNat / 2]?.getD 0#32).toNat := by
      dsimp only [la]; rw [List.getElem?_eq_getElem (by rw [hlvl_len]; omega), Option.getD_some]
      exact congrArg BitVec.toNat (getElem_eq_of_idx (by rw [bv_c0_zext32_64, bv32_lshr_1]))
    have hlb_val : lb.toNat = (s.core.lvl[b.toNat / 2]?.getD 0#32).toNat := by
      dsimp only [lb]; rw [List.getElem?_eq_getElem (by rw [hlvl_len]; omega), Option.getD_some]
      exact congrArg BitVec.toNat (getElem_eq_of_idx (by rw [bv_c0_zext32_64, bv32_lshr_1]))
    have hla_le : la.toNat ≤ s.core.cur_level := by
      obtain ⟨ma, hma, hma_eq⟩ := (hw.vals_false_iff _ h0lt).mp hfa
      have h1 := hw.lvl_le ma hma; rw [hma_eq, fullInv_var_xor1, ← ha_eq] at h1; omega
    have hlb_le : lb.toNat ≤ s.core.cur_level := by
      obtain ⟨mb, hmb, hmb_eq⟩ := (hw.vals_false_iff _ h1lt).mp hfb
      have h1 := hw.lvl_le mb hmb; rw [hmb_eq, fullInv_var_xor1, ← hb_eq] at h1; omega
    fa_fast_steps_nogrp
    refine wp_join_group (ts := [i64]) (fun (clvlv, ()) m0 =>
        m0 = m ∧ clvlv = BitVec.ofNat 64 (max la.toNat lb.toNat)) ?_ ?_
    · rintro _ ⟨clvlv, ⟨⟩⟩ m0 ⟨rfl, rfl⟩
      let clvl := max la.toNat lb.toNat
      have hcl_le : clvl ≤ s.core.cur_level := Nat.max_le.mpr ⟨hla_le, hlb_le⟩
      fa_fast_steps_nogrp
      · have hcl0 : clvl = 0 := ofNat64_eq_zero (by omega) ‹_›
        have hl0a : (s.core.lvl[a.toNat / 2]?.getD 0#32).toNat = 0 := by omega
        have hl0b : (s.core.lvl[b.toNat / 2]?.getD 0#32).toNat = 0 := by omega
        exact hQ 20#64 s m0 hlen (Or.inr (Or.inr (Or.inr rfl))) rfl rfl rfl hdm rfl hmarks hnd
          hext (fun _ h => by cases h)
          (fun _ => ⟨unsat_of_level0_bin_conflict (canonCut_to_fa hw) h0lt h1lt
            (ha_eq ▸ hl0a) (hb_eq ▸ hl0b) hfa hfb hent, rfl⟩)
          (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm
      · have hcl_pos : 0 < clvl := ofNat64_pos ‹_›
        have hbt_lt : ∀ l, (s.core.confl_type = 1#64 ∧
            (l = s.core.confl_lit0.toNat ∨ l = s.core.confl_lit1.toNat)) ∨
            (s.core.confl_type ≠ 1#64 ∧ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat) →
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ clvl := fun l hl => by
          rcases hl with ⟨_, rfl | rfl⟩ | ⟨hbad, _⟩
          · rw [← ha_eq, ← hla_val]; exact Nat.le_max_left _ _
          · rw [← hb_eq, ← hlb_val]; exact Nat.le_max_right _ _
          · exact absurd hbin hbad
        refine wp_join_group (ts := []) (fun () m1 =>
            ∃ s1 cut1, OneLitBtInv c F0 F_cur s s1 cut1 clvl ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
        · rintro _ ⟨⟩ m1 ⟨s1, cut1, hobt, hm1⟩
          fa_fast_steps_nogrp
          · exact hret_bt0 hobt hm1
          · have hne : la ≠ lb := ‹_›
            refine wp_join_group (ts := [i32]) (fun (fc, ()) mf =>
                mf = m1 ∧ fc = if la > lb then a else b) ?_ ?_
            · rintro _ ⟨fc, ⟨⟩⟩ mf ⟨rfl, rfl⟩
              refine wp_join_group (ts := [i32]) (fun (oc, ()) mo =>
                  mo = mf ∧ oc = if la > lb then b else a) ?_ ?_
              · rintro _ ⟨oc, ⟨⟩⟩ mo ⟨rfl, rfl⟩
                refine wp_join_group (ts := [i64]) (fun (jc, ()) mj =>
                    mj = mo ∧ jc = BitVec.ofNat 64
                      (if la > lb then lb.toNat else la.toNat)) ?_ ?_
                · rintro _ ⟨jc, ⟨⟩⟩ mj ⟨rfl, rfl⟩
                  fa_fast_steps_nogrp; c0_call hDet
                  refine ⟨c, s1, R, rfl, hobt.len1, by
                    have := hobt.hw1.cur_level_le; have := hobt.len1.core_ok.trail_end_le
                    have := hobt.len1.core_ok.cur_vars_le; omega,
                    hm1, fun nlvl _ hnlvl => ?_⟩
                  have hjl_lt64 : (if la > lb then lb.toNat else la.toNat) < 2 ^ 64 := by
                    split <;> omega
                  exact oneLit_bin_swap_if hDet hBt hAss hobt (ha_eq ▸ h0lt) (hb_eq ▸ h1lt)
                    hla_val hlb_val rfl hne (ha_eq ▸ hfa) (hb_eq ▸ hfb)
                    (ha_eq ▸ hb_eq ▸ hent) hm1 hQ nlvl
                    (by simpa only [bv64_ofNat_toNat hjl_lt64] using hnlvl)
                · intro Jj hJj; fa_fast_steps
                  · have hgt : la > lb := BitVec.lt_def.mpr (by dsimp only [la, lb]; assumption)
                    exact hJj _ _ ⟨rfl, by rw [ite_eq_left hgt]; exact hlb_64⟩
                  · have hng : ¬ la > lb := fun h =>
                      (by dsimp only [la, lb]; assumption : ¬ lb.toNat < la.toNat)
                        (BitVec.lt_def.mp h)
                    exact hJj _ _ ⟨rfl, by rw [ite_eq_right hng]; exact hla_64⟩
              · intro Jo hJo; fa_fast_steps
                · have hgt : la > lb := BitVec.lt_def.mpr (by dsimp only [la, lb]; assumption)
                  exact hJo _ _ ⟨rfl, by simp [hgt, b]⟩
                · have hng : ¬ la > lb := fun h =>
                    (by dsimp only [la, lb]; assumption : ¬ lb.toNat < la.toNat)
                      (BitVec.lt_def.mp h)
                  exact hJo _ _ ⟨rfl, by simp [hng, a]⟩
            · intro Jf hJf; fa_fast_steps
              · have hgt : la > lb := BitVec.lt_def.mpr (by dsimp only [la, lb]; assumption)
                exact hJf _ _ ⟨rfl, by simp [hgt, a]⟩
              · have hng : ¬ la > lb := fun h =>
                  (by dsimp only [la, lb]; assumption : ¬ lb.toNat < la.toNat) (BitVec.lt_def.mp h)
                exact hJf _ _ ⟨rfl, by simp [hng, b]⟩
        · intro Jbt hJbt; fa_fast_steps_nogrp
          · have hlt_cl : s.core.cur_level > clvl := by
              have hb : clvl % 2 ^ 64 < s.core.cur_level % 2 ^ 64 := ‹_›
              rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hcl_lt64] at hb; exact hb
            c0_call hBt
            refine ⟨c, s, R, rfl, hlen, hcl_lt64,
              fun _ => by have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
                          rw [bv64_ofNat_toNat (by omega)]; omega,
              hw.trail_lits_lt, hm, ?_⟩
            have hcl_lt64' : clvl < 2 ^ 64 := by omega
            dsimp only
            intro vals1 lvl1 rsns1 trl1 tp1 te1 prop1 cl1 unass1 sc1 m1 hlen1 _ _ hcl1 hpres _ _
              hvl1 _ hw1 hm1
            have hcl1_eq : cl1 = clvl := by
              rw [hcl1, bv64_ofNat_toNat hcl_lt64']; omega
            obtain ⟨hvs1, hls1⟩ := hvl1 ⟨F0, F_cur, Or.inr hw.toFullOtfsWitnessInv⟩
            obtain ⟨cut1, hobt⟩ := oneLit_after_bt hlen hdm hw hmarks hnd hext hcut_le hconfl0
              hcl_pos hcl_le hbt_lt (Or.inr ⟨hlt_cl, hlen1, hcl1_eq,
                rfl, hpres.2.2.1, hpres.1.1, hpres.1.2, hdm, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                fun l hl => by have h := hvs1 l hl; rw [bv64_ofNat_toNat hcl_lt64'] at h; exact h,
                fun i hi => by have h := hls1 i hi; rw [bv64_ofNat_toNat hcl_lt64'] at h; exact h,
                hw1 F0 F_cur hw.toFullOtfsWitnessInv (by rw [bv64_ofNat_toNat hcl_lt64']; omega)⟩)
            exact hJbt () m1 ⟨_, cut1, hobt, hm1⟩
          · have hle_cl : s.core.cur_level ≤ clvl := by
              have hb : ¬ clvl % 2 ^ 64 < s.core.cur_level % 2 ^ 64 := ‹_›
              rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hcl_lt64] at hb; omega
            obtain ⟨cut1, hobt⟩ := oneLit_after_bt hlen hdm hw hmarks hnd hext hcut_le hconfl0
              hcl_pos hcl_le hbt_lt (Or.inl ⟨hle_cl, rfl⟩)
            exact hJbt () m0 ⟨s, cut1, hobt, hm⟩
    · intro Jmx hJmx
      have ha_i : s.core.confl_lit0.toNat % 2 ^ 32 / 2 = (BitVec.setWidth 64 (a >>> 1)).toNat := by
        rw [bv_c0_zext32_64, bv32_lshr_1, ha_eq, Nat.mod_eq_of_lt h0_32]
      have hb_i : s.core.confl_lit1.toNat % 2 ^ 32 / 2 = (BitVec.setWidth 64 (b >>> 1)).toNat := by
        rw [bv_c0_zext32_64, bv32_lshr_1, hb_eq, Nat.mod_eq_of_lt h1_32]
      fa_fast_steps
      · have hle : lb.toNat ≤ la.toNat := by
          have hc : (s.core.lvl[s.core.confl_lit1.toNat % 2 ^ 32 / 2]'(by
              rw [hlvl_len]; omega)).toNat ≤
              (s.core.lvl[s.core.confl_lit0.toNat % 2 ^ 32 / 2]'(by
              rw [hlvl_len]; omega)).toNat := ‹_›
          dsimp only [la, lb]
          rwa [getElem_eq_of_idx (hj := hb_bd) hb_i, getElem_eq_of_idx (hj := ha_bd) ha_i] at hc
        refine hJmx _ _ ⟨rfl, ?_⟩; rw [Nat.max_eq_left hle]; exact hla_64
      · have hlt : la.toNat < lb.toNat := by
          have hc : (s.core.lvl[s.core.confl_lit0.toNat % 2 ^ 32 / 2]'(by
              rw [hlvl_len]; omega)).toNat <
              (s.core.lvl[s.core.confl_lit1.toNat % 2 ^ 32 / 2]'(by
              rw [hlvl_len]; omega)).toNat :=
            Nat.lt_of_not_le ‹_›
          dsimp only [la, lb]
          rwa [getElem_eq_of_idx (hj := ha_bd) ha_i, getElem_eq_of_idx (hj := hb_bd) hb_i] at hc
        refine hJmx _ _ ⟨rfl, ?_⟩; rw [Nat.max_eq_right (Nat.le_of_lt hlt)]; exact hlb_64
  · exfalso; exact ‹¬ s.core.confl_type = 1› (by simp [hbin])
  · exfalso; exact ‹¬ s.core.confl_type = 1› (by simp [hbin])

private theorem oneLit_large_branch_wp (Γ : Env)
    (hDet : ∀ args m Q X, fullDetNewLevelSpec args m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] args m Q X)
    (hBt : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hAss : ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hUnw : ∀ args m Q X, fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X)
    (hPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    (hlen : s.LengthsOk c) (hdm : s.core.dense_mode = 0#64)
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hmarks : FullLitMarksClear c s)
    (hnd : FullArenaVarsNodup s) (hext : FullExtScratchOk c s) (hcut_le : cut ≤ s.core.trail_end)
    (hconfl : FullConflictOkCut F_cur cut s) (hbin : s.core.confl_type ≠ 1#64)
    (hm : (FullMem c s ⋆ R) m) (hQ : OneLitPost c F0 F_cur s R Q) :
    Func.wp Γ full_one_lit_confl_body (c.hdr, ()) m Q X := by
  have hmax32 := fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hlvl_len := hlen.core_ok.lvl_len
  have hmaxv := c.hmaxv; have harena := c.harena; unfold dimacsBound at hmaxv harena
  have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
    have := hw.cur_level_le; have := hlen.core_ok.trail_end_le; omega
  have hret_bt0 {cut1 clvl : Nat} {s1 : FullState} {m1 : Mem 64}
      (hobt : OneLitBtInv c F0 F_cur s s1 cut1 clvl)
      (hm1 : (FullMem c s1 ⋆ R) m1) : Q (0#64, ()) m1 :=
    hQ 0#64 s1 m1 hobt.len1 (Or.inl rfl) hobt.cv_eq hobt.fuel_eq hobt.ws2_eq hobt.dm0 hobt.prob_eq
      hobt.marks1 hobt.nodup1 hobt.ext1 (fun _ h => by cases h) (fun h => by cases h)
      (fun h => by cases h) (fun h => by cases h)
      (fun _ => ⟨cut1, hobt.cut1_le, hobt.hw1, hobt.cl1_eq ▸ hobt.cl_pos,
        hobt.cl1_eq ▸ hobt.cl_le, hobt.wvec_eq, hobt.wstk_eq, hobt.wlen_eq, hobt.wus_eq,
        hobt.confl1⟩) hm1
  have hconfl0 : FullConflictOkCut F_cur cut s := hconfl
  have hcr_lg : s.core.confl_ref.toNat ∈ fullArenaClauseRefs s ∧
      fullArenaClauseGarb s s.core.confl_ref.toNat = false ∧
      ∀ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8 := by
    rcases hconfl.1 with ⟨h1, _⟩ | ⟨_, href, hng, hf⟩
    · exact absurd h1 hbin
    · exact ⟨href, hng, hf⟩
  obtain ⟨hcr_ref, hcr_ng, hcr_f⟩ := hcr_lg
  have hwf := hw.arena.refs_wf s.core.confl_ref.toNat hcr_ref
  have hcr_lt : s.core.confl_ref.toNat < 2 ^ 31 - 1 := by have := hwf.1; omega
  fa_fast_steps_nogrp
  · exfalso; exact hbin (by simpa using ‹s.core.confl_type = 1›)
  · exfalso
    have hc : s.core.arena_len % 2 ^ 64 <
        (s.core.confl_ref.toNat % 2 ^ 32 + BitVec.toNat 3) % 2 ^ 64 := ‹_›
    simp only [BitVec.reduceToNat] at hc
    have := hwf.1
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at hc; omega
  · -- Large conflict branch
    let cref := s.core.confl_ref.setWidth 32
    have hcref_eq : cref.toNat = s.core.confl_ref.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    have hcr32 : cref.toNat < 2 ^ 31 - 1 := by omega
    have hcsz_ge3 : 3 ≤ fullArenaClauseSize s cref.toNat := by
      unfold fullArenaClauseSize; rw [hcref_eq]; exact hwf.2.1
    let csz_val := fullArenaClauseSize s cref.toNat
    have hcsz_bd : cref.toNat + 3 + csz_val ≤ s.core.arena_len := by
      dsimp only [csz_val]; unfold fullArenaClauseSize; rw [hcref_eq]
      have := hwf.2.2.1; have := hwf.2.2.2.1; omega
    have hcsz_lt32 : csz_val < 2 ^ 32 := by
      dsimp only [csz_val]; unfold fullArenaClauseSize fullArenaClauseSizeCore
      exact (s.core.arena[cref.toNat + 2]?.getD 0#32).isLt
    have hcref_bd2 : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by
      rw [BitVec.toNat_add, zext_toNat cref (by decide)]; simp only [BitVec.reduceToNat]; omega
    have hcsz_get : s.core.arena[(cref.setWidth 64 + 2#64).toNat]'(by omega) =
        BitVec.ofNat 32 csz_val := by
      apply BitVec.eq_of_toNat_eq
      rw [bv32_ofNat_toNat hcsz_lt32, getElem_eq_of_idx (hj := by omega) hcref_bd2]
      unfold csz_val fullArenaClauseSize fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hscan_lits : ∀ q < csz_val,
        let l := s.core.arena[cref.toNat + 3 + q]?.getD 0#32
        l.toNat ∈ fullArenaClauseLits s cref.toNat ∧ l.toNat < 2 * s.core.cur_vars ∧
        (s.core.lvl[l.toNat / 2]?.getD 0#32).toNat ≤ s.core.cur_level := fun q hq => by
      dsimp only [csz_val] at hq
      have hbd_q : cref.toNat + 3 + q < s.core.arena.length := by
        dsimp only [csz_val] at hcsz_bd; omega
      have hm' : (s.core.arena[cref.toNat + 3 + q]?.getD 0#32).toNat ∈
          fullArenaClauseLitsCore s.core cref.toNat := by
        rw [mem_fullArenaClauseLitsCore_iff (by rw [hcref_eq]; omega)]
        exact ⟨q, hq, by rw [List.getElem?_eq_getElem hbd_q, Option.getD_some]⟩
      have hlt := hw.arena.lits_lt s.core.confl_ref.toNat hcr_ref hcr_ng _
        (by simpa [hcref_eq] using hm')
      obtain ⟨m0, hm0, hm0_eq⟩ := (hw.vals_false_iff _ hlt).mp
        (hcr_f _ (by simpa [fullArenaClauseLits, hcref_eq] using hm'))
      have hlvl_le := hw.lvl_le m0 hm0; rw [hm0_eq, fullInv_var_xor1] at hlvl_le
      rw [← hcref_eq] at hlt hlvl_le
      exact ⟨by simpa [fullArenaClauseLits, hcref_eq] using hm', hlt, hlvl_le⟩
    refine wp_loop_group (fun rem (clvlv, jlvlv, cntv, forcedv, iv, ()) ml => ∃ i : Nat,
      ml = m ∧ rem = csz_val - i ∧ iv = BitVec.ofNat 32 i ∧
      OneLitScanInv s cref forcedv csz_val i clvlv jlvlv cntv) ?_ ?_
    · rintro L rem ⟨clvlv, jlvlv, cntv, forcedv, iv, ⟨⟩⟩ ml ih
        ⟨i, rfl, rfl, rfl, hile, hcl_le, hjl_le, hcnt_le, hi0, hipos, huniq⟩
      fa_fast_steps_nogrp
      · have hilt : i < csz_val := by
          have hb : (BitVec.ofNat 32 i).toNat <
              (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'(by omega)).toNat := ‹_›
          rw [hcsz_get, bv32_ofNat_toNat (by omega), bv32_ofNat_toNat (by omega)] at hb; exact hb
        obtain ⟨hl_mem, hl_lt, hl_le⟩ := hscan_lits i hilt
        let li := s.core.arena[cref.toNat + 3 + i]'(by omega)
        let ll : BitVec 64 := (s.core.lvl[li.toNat / 2]?.getD 0#32).setWidth 64
        obtain ⟨hz_bd, hc_bd, hcr_i_bd, hli_get, hll_val, hli_idx, hli_lvl, hc0_lvl, hll_at'⟩ :=
          oneLit_scan_bds hlen hcv_le (by omega) hcsz_bd hilt hl_lt rfl
        fa_fast_steps_nogrp
        refine wp_join_group (ts := [i64, i64, i64, i32]) (fun (cl', jl', cnt', f', ()) ml2 =>
          ml2 = ml ∧ cl'.toNat ≤ s.core.cur_level ∧ jl'.toNat ≤ s.core.cur_level ∧
          1 ≤ cnt'.toNat ∧ cnt'.toNat ≤ i + 1 ∧
          (∀ q < i + 1, (s.core.lvl[(s.core.arena[cref.toNat + 3 + q]?.getD 0#32).toNat /
            2]?.getD 0#32).toNat ≤ cl'.toNat) ∧
          (∃ q < i + 1, (s.core.lvl[(s.core.arena[cref.toNat + 3 + q]?.getD 0#32).toNat /
            2]?.getD 0#32).toNat = cl'.toNat) ∧
          (cnt' = 1#64 → ∃ q_f < i + 1, f' = s.core.arena[cref.toNat + 3 + q_f]?.getD 0#32 ∧
            (s.core.lvl[f'.toNat / 2]?.getD 0#32).toNat = cl'.toNat ∧
            (0 < cl'.toNat → jl'.toNat < cl'.toNat) ∧
            ∀ q' < i + 1, q' ≠ q_f →
              (s.core.lvl[(s.core.arena[cref.toNat + 3 + q']?.getD 0#32).toNat / 2]?.getD
                0#32).toNat ≤ jl'.toNat)) ?_ ?_
        · rintro _ ⟨cl', jl', cnt', f', ⟨⟩⟩ ml2
            ⟨rfl, hcl', hjl', hcnt1, hcnt_le', hall', hex', hu'⟩
          fa_fast_steps
          rw [show BitVec.ofNat 32 i + 1 = BitVec.ofNat 32 (i + 1) from
            BitVec.eq_of_toNat_eq (by bv_omega)]
          exact ih (csz_val - (i + 1)) _ ml2 (by omega)
            ⟨i + 1, rfl, rfl, rfl, by omega, hcl', hjl', hcnt_le', fun h0 => by omega,
              fun _ => ⟨hcnt1, hall', hex'⟩, fun _ => hu'⟩
        · intro Js1 hJs1
          have hll_c0_lt : ll.toNat ≤ s.core.cur_level := by rw [hll_val]; exact hl_le
          have htake_hi (hjcond : cntv = 0#64 ∨ (cntv ≠ 0#64 ∧ clvlv.toNat < ll.toNat)) :
              let jl' := if cntv = 0#64 then 0#64 else clvlv
              ml = ml ∧ ll.toNat ≤ s.core.cur_level ∧ jl'.toNat ≤ s.core.cur_level ∧
              1 ≤ (1#64 : BitVec 64).toNat ∧ (1#64 : BitVec 64).toNat ≤ i + 1 ∧
              (∀ q < i + 1, (s.core.lvl[(s.core.arena[cref.toNat + 3 + q]?.getD
                0#32).toNat / 2]?.getD 0#32).toNat ≤ ll.toNat) ∧
              (∃ q < i + 1, (s.core.lvl[(s.core.arena[cref.toNat + 3 + q]?.getD
                0#32).toNat / 2]?.getD 0#32).toNat = ll.toNat) ∧
              ((1#64 : BitVec 64) = 1#64 → ∃ q_f < i + 1,
                li = s.core.arena[cref.toNat + 3 + q_f]?.getD 0#32 ∧
                (s.core.lvl[li.toNat / 2]?.getD 0#32).toNat = ll.toNat ∧
                (0 < ll.toNat → jl'.toNat < ll.toNat) ∧
                ∀ q' < i + 1, q' ≠ q_f →
                  (s.core.lvl[(s.core.arena[cref.toNat + 3 + q']?.getD 0#32).toNat /
                    2]?.getD 0#32).toNat ≤ jl'.toNat) := by
            intro jl'
            have hall_i : ∀ q < i + 1, (s.core.lvl[(s.core.arena[cref.toNat + 3 + q]?.getD
                0#32).toNat / 2]?.getD 0#32).toNat ≤ ll.toNat := fun q hq => by
              by_cases hqi : q = i
              · subst hqi; exact Nat.le_of_eq hll_val.symm
              · rcases hjcond with hc0 | hlt_c
                · cases Nat.eq_zero_or_pos i with
                  | inl hi => subst hi; omega
                  | inr hip => have := (hipos hip).1; rw [hc0] at this; simp at this
                · have hpi : 0 < i := Nat.lt_of_le_of_ne (Nat.zero_le _) fun he =>
                    hlt_c.1 (hi0 he.symm).2.2.1
                  exact Nat.le_trans ((hipos hpi).2.1 q (by omega)) (Nat.le_of_lt hlt_c.2)
            refine ⟨rfl, hll_c0_lt, by dsimp only [jl']; split; simp; exact hcl_le, Nat.le_refl 1,
              Nat.le_trans (by decide) (Nat.le_add_left 1 i), hall_i,
              ⟨i, Nat.lt_succ_self i, by rw [← hll_val]⟩, fun _ => ⟨i, Nat.lt_succ_self i,
                hli_get.symm, by dsimp only [li]; rw [← hli_get]; exact hll_val.symm,
                fun _ => ?_, fun q' hq' _ => ?_⟩⟩
            · dsimp only [jl']; split; simp [‹0 < ll.toNat›]; exact (hjcond.resolve_left ‹_›).2
            · dsimp only [jl']; split
              · rename_i hc0; cases Nat.eq_zero_or_pos i with
                | inl hi => subst hi; omega
                | inr hip => have := (hipos hip).1; rw [hc0] at this; simp at this
              · rename_i hne0
                have hpi : 0 < i := Nat.lt_of_le_of_ne (Nat.zero_le _) fun he =>
                  hne0 (hi0 he.symm).2.2.1
                exact (hipos hpi).2.1 q' (by omega)
          have hll_c0 {hpa hpl} :
              (s.core.lvl[(s.core.arena[(s.core.confl_ref.toNat % 2 ^ 32 +
                BitVec.toNat (3 : BitVec 64) + i % 2 ^ 32) % 2 ^ 64]'hpa).toNat /
                2]'hpl).toNat = ll.toNat := by
            have hbd : li.toNat / 2 < s.core.lvl.length := by
              have h := hli_lvl; rw [bv_c0_zext32_64, bv32_lshr_1, hli_idx] at h; exact h
            have hc_idx : (s.core.confl_ref.toNat % 2 ^ 32 +
                BitVec.toNat (3 : BitVec 64) + i % 2 ^ 32) % 2 ^ 64 = cref.toNat + 3 + i := by
              simp only [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
            have har_eq : s.core.arena[(s.core.confl_ref.toNat % 2 ^ 32 +
                BitVec.toNat (3 : BitVec 64) + i % 2 ^ 32) % 2 ^ 64]'hpa = li := by
              rw [getElem_eq_of_idx (hj := by omega) hc_idx, ← hli_get,
                List.getElem?_eq_getElem (by omega), Option.getD_some]
            rw [hll_val, hli_get, List.getElem?_eq_getElem hbd, Option.getD_some]
            exact congrArg BitVec.toNat (getElem_eq_of_idx (congrArg (·.toNat / 2) har_eq))
          have hll_bv_c0 {hpa hpl} : BitVec.setWidth 64 (s.core.lvl[(s.core.arena[(
              s.core.confl_ref.toNat % 2 ^ 32 + BitVec.toNat (3 : BitVec 64) +
              i % 2 ^ 32) % 2 ^ 64]'hpa).toNat / 2]'hpl) = ll := by
            apply BitVec.eq_of_toNat_eq; rw [zext_toNat _ (by decide), hll_c0]
          fa_fast_steps_nogrp
          refine wp_join_group (ts := []) (fun () ml2 =>
            ml = ml2 ∧ (cntv = 0#64 ∨ (cntv ≠ 0#64 ∧ clvlv.toNat < ll.toNat))) ?_ ?_
          · rintro _ ⟨⟩ ml2 ⟨rfl, hjcond⟩
            refine wp_join_group (ts := [i64]) (fun (jl', ()) ml2 =>
              ml = ml2 ∧ jl' = if cntv = 0#64 then 0#64 else clvlv) ?_ ?_
            · rintro _ ⟨jl', ⟨⟩⟩ ml2 ⟨rfl, rfl⟩
              have hli_at' : ∀ pf, s.core.arena[((s.core.confl_ref.setWidth 32).setWidth 64 + 3 +
                  (BitVec.ofNat 32 i).setWidth 64).toNat]'pf = li := fun _ =>
                (getElem_eq_of_idx (hj := hz_bd) rfl).trans hli_idx
              fa_fast_steps; rw [hll_at', hli_at']; exact hJs1 _ ml (htake_hi hjcond)
            · intro Jjl hJjl; fa_fast_steps
              · exact hJjl (0#64, ()) ml ⟨rfl, by rw [ite_eq_left (by simpa using ‹cntv = 0›)]⟩
              · exact hJjl (clvlv, ()) ml
                  ⟨rfl, by rw [ite_eq_right (fun h => ‹¬ cntv = 0› (by simpa using h))]⟩
          · intro Jif hJif; fa_fast_steps_nogrp
            · exact hJif () ml ⟨rfl, Or.inl (by simpa using ‹cntv = 0›)⟩
            · exact hJif () ml ⟨rfl, Or.inr ⟨fun h => ‹¬ cntv = 0› (by simpa using h),
                by rw [hll_c0] at hc; exact hc⟩⟩
            · have hne0 : cntv ≠ 0#64 := fun h => ‹¬ cntv = 0› (by simpa using h)
              have hpi : 0 < i := Nat.lt_of_le_of_ne (Nat.zero_le _) fun he =>
                hne0 (hi0 he.symm).2.2.1
              have hle_ll : ll.toNat ≤ clvlv.toNat := by rw [hll_c0] at hc; exact Nat.not_lt.mp hc
              refine wp_join_group (ts := [i64, i64]) (fun (jl', cnt', ()) ml2 =>
                ml = ml2 ∧ jl'.toNat ≤ s.core.cur_level ∧ 1 ≤ cnt'.toNat ∧
                cnt'.toNat ≤ i + 1 ∧
                (cnt' = 1#64 → ∃ q_f < i + 1,
                  forcedv = s.core.arena[cref.toNat + 3 + q_f]?.getD 0#32 ∧
                  (s.core.lvl[forcedv.toNat / 2]?.getD 0#32).toNat = clvlv.toNat ∧
                  (0 < clvlv.toNat → jl'.toNat < clvlv.toNat) ∧
                  ∀ q' < i + 1, q' ≠ q_f →
                    (s.core.lvl[(s.core.arena[cref.toNat + 3 + q']?.getD 0#32).toNat / 2]?.getD
                      0#32).toNat ≤ jl'.toNat)) ?_ ?_
              · rintro _ ⟨jl', cnt', ⟨⟩⟩ ml2 ⟨rfl, hjl', hcnt1', hcnt_le', hu'⟩
                fa_fast_steps
                exact hJs1 (clvlv, jl', cnt', forcedv, ()) ml
                  ⟨rfl, hcl_le, hjl', hcnt1', hcnt_le', fun q hq => by
                      by_cases hqi : q = i
                      · subst hqi; rw [← hll_val]; exact hle_ll
                      · exact (hipos hpi).2.1 q (by omega),
                    (hipos hpi).2.2.imp fun q ⟨hq, hqe⟩ => ⟨by omega, hqe⟩, hu'⟩
              · intro Js2 hJs2; fa_fast_steps_nogrp
                · have heq_ll : ll = clvlv := by rw [hll_bv_c0] at hc; exact hc
                  refine wp_join_group (ts := [i64]) (fun (jl', ()) ml2 =>
                    ml = ml2 ∧ jl'.toNat ≤ s.core.cur_level) ?_ ?_
                  · rintro _ ⟨jl', ⟨⟩⟩ ml2 ⟨rfl, hjl'⟩; fa_fast_steps
                    have hcnt_lt64 : cntv.toNat + 1 < 2 ^ 64 := by have := hw.cur_level_le; omega
                    have h1 := (hipos hpi).1
                    refine hJs2 _ ml ⟨rfl, hjl',
                      by rw [BitVec.toNat_add]; simp only [BitVec.reduceToNat]
                         rw [Nat.mod_eq_of_lt (by omega)]; omega,
                      by rw [BitVec.toNat_add]; simp only [BitVec.reduceToNat]
                         rw [Nat.mod_eq_of_lt (by omega)]; omega,
                      fun heq => by
                        have := congrArg BitVec.toNat heq; rw [BitVec.toNat_add] at this
                        simp only [BitVec.reduceToNat] at this
                        rw [Nat.mod_eq_of_lt (by omega)] at this; omega⟩
                  · intro Jj hJj; fa_fast_steps
                    · rw [hll_at']; exact hJj (ll, ()) ml ⟨rfl, hll_c0_lt⟩
                    · exact hJj (jlvlv, ()) ml ⟨rfl, hjl_le⟩
                · have hlt_ll : ll.toNat < clvlv.toNat := Nat.lt_of_le_of_ne hle_ll fun h =>
                    (fun hn => by rw [hll_bv_c0] at hc; exact hc hn) (BitVec.eq_of_toNat_eq h)
                  refine wp_join_group (ts := [i64]) (fun (jl', ()) ml2 =>
                    ml = ml2 ∧ jl'.toNat ≤ s.core.cur_level ∧
                    (cntv = 1#64 → 0 < clvlv.toNat → jl'.toNat < clvlv.toNat) ∧
                    ll.toNat ≤ jl'.toNat ∧ jlvlv.toNat ≤ jl'.toNat) ?_ ?_
                  · rintro _ ⟨jl', ⟨⟩⟩ ml2 ⟨rfl, hjl', hj_lt, hll_j, hj_j⟩; fa_fast_steps
                    refine hJs2 _ ml ⟨rfl, hjl', (hipos hpi).1, by omega, fun h1 => ?_⟩
                    obtain ⟨q_f, hqf_lt, hf_eq, hf_lv, _, hoth⟩ := huniq hpi h1
                    refine ⟨q_f, by omega, hf_eq, hf_lv, hj_lt h1, fun q' hq' hq'n => ?_⟩
                    by_cases hqi : q' = i
                    · subst hqi; rw [← hll_val]; exact hll_j
                    · exact Nat.le_trans (hoth q' (by omega) hq'n) hj_j
                  · intro Jj hJj; fa_fast_steps
                    · rw [hll_at']
                      exact hJj (ll, ()) ml ⟨rfl, hll_c0_lt, fun _ _ => hlt_ll, Nat.le_refl _,
                        by have hgt : jlvlv.toNat < ll.toNat := by rw [hll_c0] at hc; exact hc
                           omega⟩
                    · exact hJj (jlvlv, ()) ml ⟨rfl, hjl_le,
                        fun h1 hpos => let ⟨_, _, _, _, hjl_lt, _⟩ := huniq hpi h1; hjl_lt hpos,
                        by rw [hll_c0] at hc; exact Nat.not_lt.mp hc, Nat.le_refl _⟩
      · have hi_ge : csz_val ≤ i := by
          have hnot : ¬ (BitVec.ofNat 32 i).toNat <
              (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'(by omega)).toNat := ‹_›
          rw [hcsz_get, bv32_ofNat_toNat (by omega), bv32_ofNat_toNat (by omega)] at hnot
          exact Nat.not_lt.mp hnot
        have hieq : i = csz_val := Nat.le_antisymm hile hi_ge; subst hieq
        have hcsz_pos : 0 < csz_val := by omega
        obtain ⟨_, hall_le, _⟩ := hipos hcsz_pos
        have hcl0 : clvlv = 0#64 := ‹_›
        have hunsat : F0.Unsat := by
          refine unsat_of_level0_conflict (canonCut_to_fa hw) (hcref_eq ▸ hcr_ref)
            (hcref_eq ▸ hcr_ng) fun l hl => ?_
          rw [mem_fullArenaClauseLitsCore_iff (by
            rw [hcref_eq]; have := hwf.2.2.1; have := hwf.2.2.2.1; omega)] at hl
          obtain ⟨q, hq, hql⟩ := hl
          have hq' : q < csz_val := by simpa only [csz_val, fullArenaClauseSize, hcref_eq] using hq
          have hbd_q : cref.toNat + 3 + q < s.core.arena.length := by
            dsimp only [csz_val] at hcsz_bd; omega
          have hql' : (s.core.arena[cref.toNat + 3 + q]?.getD 0#32).toNat = l := by
            rw [List.getElem?_eq_getElem hbd_q, Option.getD_some]; exact hql
          have hlv0 := hall_le q hq'; rw [hcl0] at hlv0
          exact ⟨hcr_f l (by rw [← hql']; exact hcref_eq ▸ (hscan_lits q hq').1),
            by rw [← hql']; simpa using hlv0⟩
        exact hQ 20#64 s ml hlen (Or.inr (Or.inr (Or.inr rfl))) rfl rfl rfl hdm rfl hmarks hnd
          hext (fun _ h => by cases h) (fun _ => ⟨hunsat, rfl⟩) (fun h => by cases h)
          (fun h => by cases h) (fun h => by cases h) hm
      · have hi_ge : csz_val ≤ i := by
          have hnot : ¬ (BitVec.ofNat 32 i).toNat <
              (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'(by omega)).toNat := ‹_›
          rw [hcsz_get, bv32_ofNat_toNat (by omega), bv32_ofNat_toNat (by omega)] at hnot
          exact Nat.not_lt.mp hnot
        have hieq : i = csz_val := Nat.le_antisymm hile hi_ge; subst hieq
        have hcsz_pos : 0 < csz_val := by omega
        obtain ⟨_, hall_le, _⟩ := hipos hcsz_pos
        have hcl_pos : 0 < clvlv.toNat := Nat.pos_of_ne_zero fun h0 =>
          ‹¬ clvlv = 0› (BitVec.eq_of_toNat_eq (by simpa using h0))
        have hbt_lt : ∀ l, (s.core.confl_type = 1#64 ∧
            (l = s.core.confl_lit0.toNat ∨ l = s.core.confl_lit1.toNat)) ∨
            (s.core.confl_type ≠ 1#64 ∧ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat) →
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ clvlv.toNat := fun l hl => by
          rcases hl with ⟨hbad, _⟩ | ⟨_, hl⟩
          · exact absurd hbad hbin
          · rw [fullArenaClauseLits, mem_fullArenaClauseLitsCore_iff (by
              have := hwf.2.2.1; have := hwf.2.2.2.1; omega)] at hl
            obtain ⟨q, hq, rfl⟩ := hl
            have hq_lt : q < csz_val := by
              simpa only [csz_val, fullArenaClauseSize, hcref_eq] using hq
            have hget_q : s.core.arena[cref.toNat + 3 + q]?.getD 0#32 =
                s.core.arena[s.core.confl_ref.toNat + 3 + q]'(by
                  dsimp only [csz_val] at hcsz_bd; omega) := by
              rw [List.getElem?_eq_getElem (by dsimp only [csz_val] at hcsz_bd; omega),
                Option.getD_some]; exact getElem_eq_of_idx (by rw [hcref_eq])
            rw [← hget_q]; exact hall_le q hq_lt
        refine wp_join_group (ts := []) (fun () m1 =>
            ∃ s1 cut1, OneLitBtInv c F0 F_cur s s1 cut1 clvlv.toNat ∧
              (FullMem c s1 ⋆ R) m1) ?_ ?_
        · rintro _ ⟨⟩ m1 ⟨s1, cut1, hobt, hm1⟩
          fa_fast_steps_nogrp
          · exact hret_bt0 hobt hm1
          · have hcnt_eq1 : cntv = 1#64 := by
              have hnot : ¬ 1 < cntv.toNat := by simpa only [BitVec.reduceToNat] using ‹_›
              exact BitVec.eq_of_toNat_eq (by simp only [BitVec.reduceToNat]; omega)
            obtain ⟨q_f, hqf_lt, hfq_eq, hfq_lv, hjl_lt, hoth⟩ := huniq hcsz_pos hcnt_eq1
            have hforced_m := hscan_lits q_f hqf_lt; rw [← hfq_eq] at hforced_m
            have hcref1_ref : cref.toNat ∈ fullArenaClauseRefsCore s1.core := by
              simpa only [fullArenaClauseRefsCore, hobt.arena_eq, hobt.arena_len_eq,
                hcref_eq] using hcr_ref
            have hcref1_ng : fullArenaClauseGarbCore s1.core cref.toNat = false := by
              simpa only [fullArenaClauseGarbCore, fullArenaHdrCore, hobt.arena_eq,
                hcref_eq] using hcr_ng
            have hcref1_sz : fullArenaClauseSizeCore s1.core cref.toNat = csz_val := by
              dsimp only [csz_val]; unfold fullArenaClauseSize fullArenaClauseSizeCore
              rw [hobt.arena_eq, hcref_eq]
            have hs1_lits_nodup : ∀ p1 p2, p1 < csz_val → p2 < csz_val → p1 ≠ p2 →
                s1.core.arena[cref.toNat + 3 + p1]?.getD 0#32 ≠
                s1.core.arena[cref.toNat + 3 + p2]?.getD 0#32 := fun p1 p2 hp1 hp2 hpne he => by
              have hndc := hobt.nodup1 cref.toNat hcref1_ref hcref1_ng
              let raw := (s1.core.arena.drop (cref.toNat + 3)).take csz_val
              have hraw_len : raw.length = csz_val := by
                have := hobt.len1.core_ok.arena_len_arr; have := hobt.len1.core_ok.arena_len_le
                have := (hobt.hw1.arena.refs_wf _ hcref1_ref).2.2.1
                simp [raw, List.length_take, List.length_drop]; omega
              have hnd_raw : (raw.map fun l : BitVec 32 => l.toNat / 2).Nodup := by
                simpa [fullArenaClauseLitsCore, hcref1_sz, raw, List.map_map, Function.comp_def]
                  using hndc
              have hp_idx {p} (hp : p < csz_val) :
                  raw[p]'(hraw_len ▸ hp) = s1.core.arena[cref.toNat + 3 + p]?.getD 0#32 := by
                have := hobt.len1.core_ok.arena_len_arr; have := hobt.len1.core_ok.arena_len_le
                have := (hobt.hw1.arena.refs_wf _ hcref1_ref).2.2.1
                simp only [raw, List.getElem_take, List.getElem_drop]
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              exact hpne (nodup_map_getElem_inj (fun l : BitVec 32 => l.toNat / 2)
                (hraw_len ▸ hp1) (hraw_len ▸ hp2) hnd_raw (by rw [hp_idx hp1, hp_idx hp2, he]))
            have har1_len := hobt.len1.core_ok.arena_len_arr
            have har1_le := hobt.len1.core_ok.arena_len_le
            have hcr3_bd : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3 := by
              rw [BitVec.toNat_add, zext_toNat cref (by decide)]
              simp only [BitVec.reduceToNat]; omega
            have hcr4_bd : (cref.setWidth 64 + 4#64).toNat = cref.toNat + 4 := by
              rw [BitVec.toNat_add, zext_toNat cref (by decide)]
              simp only [BitVec.reduceToNat]; omega
            let l0 := s1.core.arena[cref.toNat + 3]?.getD 0#32
            let l1 := s1.core.arena[cref.toNat + 4]?.getD 0#32
            have hl0_idx : s1.core.arena[(cref.setWidth 64 + 3#64).toNat]'(by
                rw [hcr3_bd]; omega) = l0 := by
              dsimp only [l0]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              exact getElem_eq_of_idx hcr3_bd
            have hl1_idx : s1.core.arena[(cref.setWidth 64 + 4#64).toNat]'(by
                rw [hcr4_bd]; omega) = l1 := by
              dsimp only [l1]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              exact getElem_eq_of_idx hcr4_bd
            have hl0_hc {hp} : s1.core.arena[(s.core.confl_ref.toNat % 2 ^ 32 +
                BitVec.toNat (3 : BitVec 64)) % 2 ^ 64]'hp = l0 := by
              have hi : (s.core.confl_ref.toNat % 2 ^ 32 + BitVec.toNat (3 : BitVec 64)) %
                  2 ^ 64 = cref.toNat + 3 := by
                rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
              dsimp only [l0]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              exact getElem_eq_of_idx hi
            have hl1_hc {hp} : s1.core.arena[(s.core.confl_ref.toNat % 2 ^ 32 +
                BitVec.toNat (4 : BitVec 64)) % 2 ^ 64]'hp = l1 := by
              have hi : (s.core.confl_ref.toNat % 2 ^ 32 + BitVec.toNat (4 : BitVec 64)) %
                  2 ^ 64 = cref.toNat + 4 := by
                rw [show BitVec.toNat (4 : BitVec 64) = 4 from rfl]; omega
              dsimp only [l1]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              exact getElem_eq_of_idx hi
            have hconfl_lits_other : ∀ s_c : FullState,
                (∀ q ∈ fullArenaClauseLitsCore s_c.core cref.toNat,
                  q ∈ fullArenaClauseLitsCore s1.core cref.toNat) →
                ∀ q ∈ fullArenaClauseLitsCore s_c.core cref.toNat,
                  q = forcedv.toNat ∨ (s1.core.vals[q]?.getD 0#8 = 0xFF#8 ∧
                    (s1.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvlv.toNat) := fun s_c hsub q hq => by
              have hq1 := hsub q hq
              have := (hobt.hw1.arena.refs_wf _ hcref1_ref).2.2.1
              rw [mem_fullArenaClauseLitsCore_iff (by omega)] at hq1
              obtain ⟨p, hp, hpeq⟩ := hq1
              have hp_lt : p < csz_val := by rwa [hcref1_sz] at hp
              have hqp : (s.core.arena[cref.toNat + 3 + p]?.getD 0#32).toNat = q := by
                rw [← hobt.arena_eq, List.getElem?_eq_getElem (by omega), Option.getD_some, hpeq]
              by_cases hpf : p = q_f
              · left; subst hpf; rw [← hqp, ← hfq_eq]
              · right
                have hq_lt2 : q < 2 * s.core.cur_vars := by
                  rw [← hqp]; exact (hscan_lits p hp_lt).2.1
                have hle_j : (s.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvlv.toNat := by
                  rw [← hqp]; exact hoth p hp_lt hpf
                have hql_le : (s.core.lvl[q / 2]?.getD 0#32).toNat ≤ clvlv.toNat :=
                  Nat.le_trans hle_j (Nat.le_of_lt (hjl_lt hcl_pos))
                have hqf_s : s.core.vals[q]?.getD 0#8 = 0xFF#8 :=
                  hcr_f q (by rw [← hqp]
                              simpa [fullArenaClauseLits, hcref_eq] using (hscan_lits p hp_lt).1)
                refine ⟨(hobt.vals_keep q hq_lt2 hql_le).trans hqf_s,
                  by rw [hobt.lvl_keep q hq_lt2 hqf_s hql_le]; exact hle_j⟩
            have hm_s1 : forcedv.toNat ∈ fullArenaClauseLitsCore s1.core cref.toNat := by
              simpa only [fullArenaClauseLits, fullArenaClauseLitsCore,
                fullArenaClauseSizeCore, hobt.arena_eq] using hforced_m.1
            let TailPred : Tup Val [] → Mem 64 → Prop := fun () mb =>
              ∃ sb : FullState, sb.core.lvl = s1.core.lvl ∧
                cref.toNat ∈ fullArenaClauseRefsCore sb.core ∧
                fullArenaClauseGarbCore sb.core cref.toNat = false ∧
                forcedv.toNat ∈ fullArenaClauseLitsCore sb.core cref.toNat ∧
                (∀ q ∈ fullArenaClauseLitsCore sb.core cref.toNat,
                  q = forcedv.toNat ∨ (sb.core.vals[q]?.getD 0#8 = 0xFF#8 ∧
                    (sb.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvlv.toNat)) ∧
                sb.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut1 sb.core ∧
                FullLitMarksClear c sb ∧ FullArenaVarsNodup sb ∧ FullExtScratchOk c sb ∧
                sb.core.cur_level = clvlv.toNat ∧ sb.core.cur_vars = s.core.cur_vars ∧
                sb.core.fuel = s.core.fuel ∧ sb.scratch.work_stk2 = s.scratch.work_stk2 ∧
                sb.core.dense_mode = 0#64 ∧ sb.core.probing = s.core.probing ∧
                (FullMem c sb ⋆ R) mb
            fa_fast_steps_nogrp
            refine wp_join_group (ts := []) TailPred ?_ ?_
            · rintro _ ⟨⟩ mb ⟨sb, hblvl, hbref, hbng, hbfmem, hbfoth, hblen, hbw, hbmk, hbnd,
                hbext, hbcl, hbcv, hbfu, hbws2, hbdm, hbpr, hmb⟩
              have hff_s : s.core.vals[forcedv.toNat]?.getD 0#8 = 0xFF#8 :=
                hcr_f _ (hcref_eq ▸ hforced_m.1)
              exact oneLit_large_tail_exec_wp hDet hBt hAss hobt.cl_le hcl_pos
                (hjl_lt hcl_pos) hcr32 hbref hbng hbfmem hbfoth hblen hbw
                hbmk hbnd hbext hbcl hbcv hbfu hbws2 hbdm hbpr
                (by rw [hblvl, hobt.lvl_keep _ hforced_m.2.1 hff_s (by omega)]
                    exact hfq_lv)
                hforced_m.2.1 hmb hQ
            · intro Jtail hJtail
              refine wp_join_group (ts := []) (fun () mb =>
                mb = m1 ∧ (l0 = forcedv ∨ l1 = forcedv)) ?_ ?_
              · rintro _ ⟨⟩ m_el ⟨hm_eq, _hor⟩; subst m_el
                refine wp_join_group (ts := []) TailPred ?_ ?_
                · rintro _ ⟨⟩ mb hmb; exact hJtail () mb hmb
                · intro Jsw hJsw; fa_fast_steps_nogrp
                  · fa_fast_steps
                    have hl1_eq : l1 = forcedv := by rw [hl1_hc] at hc; exact hc
                    obtain ⟨hlen2, hw2, hnd2, hext2, _, hcref2, hng2, _, hperm2⟩ :=
                      oneLit_swap_arena_inv hobt.len1 hobt.hw1 hobt.nodup1 hobt.ext1 hcref1_ref
                        hcref1_ng hcref1_sz (i := 0) (j := 1) (by omega) (by omega) l0 l1 rfl rfl
                    let ar2_raw := (s1.core.arena.set (cref.setWidth 64 + 3#64).toNat l1).set
                      (cref.setWidth 64 + 4#64).toNat l0
                    let ar2 := (s1.core.arena.set (cref.toNat + 3) l1).set (cref.toNat + 4) l0
                    let s2 : FullState := { s1 with core := { s1.core with arena := ar2 } }
                    have hm_raw : (FullMem c
                        { s1 with core := { s1.core with arena := ar2_raw } } ⋆ R) m := by
                      dsimp only [ar2_raw]; rw [← hl1_idx, ← hl0_idx]; assumption
                    have har2_eq : ar2_raw = ar2 := by
                      dsimp only [ar2_raw, ar2]; rw [hcr3_bd, hcr4_bd]
                    exact hJsw () m ⟨s2, rfl, hcref2, hng2, hperm2.symm.mem_iff.mp hm_s1,
                      hconfl_lits_other s2 fun q hq => hperm2.mem_iff.mp hq,
                      hlen2, hw2, hobt.marks1, hnd2, hext2, hobt.cl1_eq, hobt.cv_eq, hobt.fuel_eq,
                      hobt.ws2_eq, hobt.dm0, hobt.prob_eq, fullMem_of_eq hm_raw
                        (congrArg (fun a => { s1.core with arena := a }) har2_eq) rfl⟩
                  · exact hJsw () m1 ⟨s1, rfl, hcref1_ref, hcref1_ng, hm_s1,
                      hconfl_lits_other s1 fun _ h => h, hobt.len1, hobt.hw1, hobt.marks1,
                      hobt.nodup1, hobt.ext1, hobt.cl1_eq, hobt.cv_eq, hobt.fuel_eq, hobt.ws2_eq,
                      hobt.dm0, hobt.prob_eq, hm1⟩
              · intro Jelse hJelse; fa_fast_steps_nogrp
                · rename_i hc0
                  have hl0_ne : l0 ≠ forcedv := by rw [hl0_hc] at hc0; exact hc0
                  have hl1_ne : l1 ≠ forcedv := by rw [hl1_hc] at hc; exact hc
                  have hqf_ge2 : 2 ≤ q_f := by
                    cases q_f with
                    | zero =>
                      exfalso; apply hl0_ne; dsimp only [l0]
                      rw [hobt.arena_eq, ← Nat.add_zero (cref.toNat + 3), ← hfq_eq]
                    | succ n => cases n with
                      | zero =>
                        exfalso; apply hl1_ne; dsimp only [l1]
                        rw [hobt.arena_eq, show cref.toNat + 4 = cref.toNat + 3 + 1 from rfl,
                          ← hfq_eq]
                      | succ _ => omega
                  refine wp_loop_group (fun rem (jv, ()) ml2 => ∃ j : Nat,
                    m1 = ml2 ∧ rem = q_f - j ∧ 2 ≤ j ∧ j ≤ q_f ∧ jv = BitVec.ofNat 32 j) ?_ ?_
                  · rintro L rem ⟨jv, ⟨⟩⟩ ml2 ih ⟨j, rfl, rfl, hj2, hjle, rfl⟩
                    have hj_lt : j < csz_val := Nat.lt_of_le_of_lt hjle hqf_lt
                    have hcr_j_z : (cref.setWidth 64 + 3#64 +
                        (BitVec.ofNat 32 j).setWidth 64).toNat = cref.toNat + 3 + j := by
                      rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat cref (by decide),
                        zext_toNat (BitVec.ofNat 32 j) (by decide), bv32_ofNat_toNat (by omega)]
                      simp only [BitVec.reduceToNat]; omega
                    have hc_idx2 : (s.core.confl_ref.toNat % 2 ^ 32 +
                        BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = cref.toNat + 2 := by
                      simp only [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
                    have hcsz_get_c0 {hpa} : (s.core.arena[(s.core.confl_ref.toNat % 2 ^ 32 +
                        BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'hpa).toNat = csz_val := by
                      rw [getElem_eq_of_idx (hj := by omega) hc_idx2]
                      unfold csz_val fullArenaClauseSize fullArenaClauseSizeCore
                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                    fa_fast_steps_nogrp
                    refine wp_join_group (ts := []) (fun () ml2 => m1 = ml2 ∧ j = q_f) ?_ ?_
                    · rintro _ ⟨⟩ ml2 ⟨rfl, hjqf⟩; subst j; fa_fast_steps_nogrp
                      refine wp_join_group (ts := []) TailPred ?_ ?_
                      · rintro _ ⟨⟩ mb hmb; exact hJtail () mb hmb
                      · intro Jtail' hJtail'; fa_fast_steps_nogrp
                        · have hl0_rw {pf} : s1.core.arena[(BitVec.setWidth 64
                              (BitVec.setWidth 32 s.core.confl_ref) + 3).toNat]'pf = l0 :=
                            (getElem_eq_of_idx (hj := by
                              change (cref.setWidth 64 + 3#64).toNat < _
                              rw [hcr3_bd]; omega) rfl).trans hl0_idx
                          rw [hl0_rw]
                          refine oneLit_large_push_branch_wp (X := X) hUnw hPush hobt hbin hcr32
                            hcsz_ge3 hqf_ge2 hqf_lt hcsz_bd hcref1_ref hcref1_ng hcref1_sz rfl rfl
                            hfq_eq hforced_m.2.1 hm_s1 hconfl_lits_other hm1 hQ fun _ hp =>
                            hJtail' () _ hp
                        · exfalso
                          have hnot_lt : ¬ q_f < csz_val := by
                            have hraw : ¬ q_f % 2 ^ 32 < (s.core.arena[(s.core.confl_ref.toNat %
                                2 ^ 32 + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                                  rw [har_len]; omega)).toNat := ‹_›
                            simpa only [Nat.mod_eq_of_lt (by omega : q_f < 2 ^ 32), hcsz_get_c0]
                              using hraw
                          exact hnot_lt hqf_lt
                    · intro J_exit hJ_exit
                      have hcr_j_cap : cref.toNat + 3 + j < c.arena_cap := by omega
                      have hc_j_idx : (s.core.confl_ref.toNat % 2 ^ 32 +
                          BitVec.toNat (3 : BitVec 64) + j % 2 ^ 32) % 2 ^ 64 =
                          cref.toNat + 3 + j := by
                        have h32 : s.core.confl_ref.toNat % 2 ^ 32 = cref.toNat := by
                          dsimp only [cref]; rw [BitVec.toNat_setWidth]
                        rw [h32, show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
                      fa_fast_steps
                      · have hjne : j ≠ q_f := fun h => by
                          subst h
                          have hnot_f : ¬ s1.core.arena[(s.core.confl_ref.toNat % 2 ^ 32 +
                              BitVec.toNat (3 : BitVec 64) + j % 2 ^ 32) % 2 ^ 64]'(by
                                rw [hc_j_idx, har1_len]; exact hcr_j_cap) = forcedv := ‹_›
                          have hbd_j1 : cref.toNat + 3 + j < s1.core.arena.length := by
                            rw [har1_len]; exact hcr_j_cap
                          have h_s1_s := Option.some.inj
                            ((List.getElem?_eq_getElem hbd_j1).symm.trans (by
                              rw [hobt.arena_eq,
                                List.getElem?_eq_getElem (by rw [har_len]; exact hcr_j_cap)]))
                          have h_at_j : s.core.arena[cref.toNat + 3 + j]'(by
                              rw [har_len]; exact hcr_j_cap) = forcedv := by
                            rw [hfq_eq, List.getElem?_eq_getElem (by rw [har_len]; exact hcr_j_cap),
                              Option.getD_some]
                          exact hnot_f ((getElem_eq_of_idx hc_j_idx).trans (h_s1_s.trans h_at_j))
                        have hj1 : BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) := by
                          apply BitVec.eq_of_toNat_eq; bv_omega
                        rw [hj1]
                        exact ih (q_f - (j + 1)) _ m1 (by omega)
                          ⟨j + 1, rfl, rfl, by omega, by omega, rfl⟩
                      · have h_eq_f : s1.core.arena[(s.core.confl_ref.toNat % 2 ^ 32 +
                            BitVec.toNat (3 : BitVec 64) + j % 2 ^ 32) % 2 ^ 64]'(by
                              rw [hc_j_idx, har1_len]; exact hcr_j_cap) = forcedv := by
                          first | exact ‹_› | exact Classical.not_not.mp ‹_›
                        have h_at_j1 : s1.core.arena[cref.toNat + 3 + j]'(by
                            rw [har1_len]; exact hcr_j_cap) = forcedv :=
                          (getElem_eq_of_idx hc_j_idx.symm).trans h_eq_f
                        have hjeq : j = q_f := Classical.byContradiction fun hne => by
                          have heq : s1.core.arena[cref.toNat + 3 + j]?.getD 0#32 =
                              s1.core.arena[cref.toNat + 3 + q_f]?.getD 0#32 := by
                            rw [List.getElem?_eq_getElem (by rw [har1_len]; exact hcr_j_cap),
                              Option.getD_some, h_at_j1, hfq_eq, hobt.arena_eq]
                          exact hs1_lits_nodup j q_f hj_lt hqf_lt hne heq
                        exact hJ_exit () m1 ⟨rfl, hjeq⟩
                      · exfalso
                        have hnot_lt : ¬ j < csz_val := by
                          have hraw : ¬ j % 2 ^ 32 < (s.core.arena[(s.core.confl_ref.toNat %
                              2 ^ 32 + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                                rw [har_len]; omega)).toNat := ‹_›
                          simpa only [Nat.mod_eq_of_lt (by omega : j < 2 ^ 32), hcsz_get_c0]
                            using hraw
                        exact hnot_lt hj_lt
                  · intro L hL; fa_fast_steps
                    exact hL (q_f - 2) (2#32, ()) m1 ⟨2, rfl, rfl, Nat.le_refl _, hqf_ge2, rfl⟩
                · refine hJelse () m1 ⟨rfl, Or.inr ?_⟩
                  rw [hl1_hc] at hc; first | exact hc | exact Classical.not_not.mp hc
                · refine hJelse () m1 ⟨rfl, Or.inl ?_⟩
                  rw [hl0_hc] at hc; first | exact hc | exact Classical.not_not.mp hc
        · intro Jbt hJbt; fa_fast_steps_nogrp
          · have hlt_cl : s.core.cur_level > clvlv.toNat := by
              have hb : clvlv.toNat < (BitVec.ofNat 64 s.core.cur_level).toNat := ‹_›
              rw [bv64_ofNat_toNat hcl_lt64] at hb; exact hb
            c0_call hBt
            refine ⟨c, s, R, rfl, hlen, hcl_lt64,
              fun _ => by have := hw.cur_level_le; have := hlen.core_ok.trail_end_le; omega,
              hw.trail_lits_lt, hm, ?_⟩
            dsimp only
            intro vals1 lvl1 rsns1 trl1 tp1 te1 prop1 cl1 unass1 sc1 m1 hlen1 _ _ hcl1 hpres _ _
              hvl1 _ hw1 hm1
            have hcl1_eq : cl1 = clvlv.toNat := by rw [hcl1]; omega
            obtain ⟨hvs1, hls1⟩ := hvl1 ⟨F0, F_cur, Or.inr hw.toFullOtfsWitnessInv⟩
            obtain ⟨cut1, hobt⟩ := oneLit_after_bt hlen hdm hw hmarks hnd hext hcut_le hconfl0
              hcl_pos (Nat.le_trans (le_refl _) hcl_le) hbt_lt
              (Or.inr ⟨hlt_cl, hlen1, hcl1_eq, rfl, hpres.2.2.1, hpres.1.1, hpres.1.2, hdm, rfl,
                rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hvs1, hls1,
                hw1 F0 F_cur hw.toFullOtfsWitnessInv (by omega)⟩)
            exact hJbt () m1 ⟨_, cut1, hobt, hm1⟩
          · have hle_cl : s.core.cur_level ≤ clvlv.toNat := by
              have hnot : ¬ clvlv.toNat < (BitVec.ofNat 64 s.core.cur_level).toNat := ‹_›
              rw [bv64_ofNat_toNat hcl_lt64] at hnot; omega
            obtain ⟨cut1, hobt⟩ := oneLit_after_bt hlen hdm hw hmarks hnd hext hcut_le hconfl0
              hcl_pos hcl_le hbt_lt (Or.inl ⟨hle_cl, rfl⟩)
            exact hJbt () ml ⟨s, cut1, hobt, hm⟩
    · intro Jscan hJscan; fa_fast_steps
      exact hJscan csz_val (0#64, 0#64, 0#64, 0xFFFFFFFF#32, 0#32, ()) m
        ⟨0, rfl, rfl, rfl, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.le_refl _,
          fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun h => by omega, fun h => by omega⟩

theorem full_one_lit_confl_wp (Γ : Env)
    (hDet : ∀ args m Q X, fullDetNewLevelSpec args m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] args m Q X)
    (hBt : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hAss : ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hUnw : ∀ args m Q X, fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X)
    (hPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullOneLitConflSpec args m Q X →
      Func.wp Γ full_one_lit_confl_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, cut, s, R, rfl, hcutInv, hconfl, hm, hQ⟩
  obtain ⟨hlen, hw, hmarks, hnd, hext, hdm⟩ := hcutInv
  have hQ' : OneLitPost c F0 F_cur s R Q :=
    fun r s' m' hlen' hr hcv hfu hws2 hdm' _ hmk' hnd' hext' _ h20 h1 h2 h0 hm' =>
      hQ r s' m' hlen' hr hcv hfu hws2
        (fun h20r => let ⟨hu, heq⟩ := h20 h20r
          ⟨hu, heq ▸ ⟨hlen, hw.toFullOtfsWitnessInv, hmarks, hnd, hext, hdm⟩,
            by rw [heq]; exact Nat.le_refl _, by rw [heq]⟩)
        (fun h1r => let ⟨hw', hlt⟩ := h1 h1r
          ⟨⟨hlen', hw', hmk', hnd', hext', hdm'⟩, hlt⟩)
        (fun h2r => ⟨hlen', h2 h2r, hmk', hnd', hext', hdm'⟩)
        (fun h0r => let ⟨cut', hcut'le, hw', hpos, hle, _, _, _, _, hcf'⟩ := h0 h0r
          ⟨cut', hcut'le, ⟨hlen', hw', hmk', hnd', hext', hdm'⟩, hpos, hle, hcf'⟩)
        hm'
  by_cases hbin : s.core.confl_type = 1#64
  · exact oneLit_bin_branch_wp Γ hDet hBt hAss hlen hdm hw hmarks hnd hext hw.cut_le hconfl hbin
      hm hQ'
  · exact oneLit_large_branch_wp Γ hDet hBt hAss hUnw hPush hlen hdm hw hmarks hnd hext hw.cut_le
      hconfl hbin hm hQ'

/-! ## 2. Index-verified `SpecEntry.Impl fullEnv` bridge (`fullFns[78]?`) -/

private theorem fullFns_nodup_ol : (fullFns.map Fn.name).Nodup := by
  have hchk := full_acyclic
  simp only [fullModule, Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

private theorem fullSpecTable_nodup_ol (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((fullSpecTable mainSpec).map SpecEntry.name).Nodup := by
  have h : (fullSpecTable mainSpec).map SpecEntry.name = fullFns.map Fn.name := by
    have hm := congrArg (List.map Prod.fst) (fullSpecTable_sigs mainSpec)
    simpa only [List.map_map, Function.comp_def] using hm
  rw [h]
  exact fullFns_nodup_ol

private theorem mkFullEnv_row_at_ol {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry)
    (hi : (fullSpecTable mainSpec)[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkFullEnv mainSpec e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) (fullSpecTable_nodup_ol mainSpec) (hno xs m Q X h)

/-- Parametric `SpecEntry.Impl (mkFullEnv mainSpec)` bridge for `full_one_lit_confl`
at index `78`. -/
theorem full_one_lit_confl_mk_ok (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∃ fn' row', fullFns[78]? = some fn' ∧
      (fullSpecTable mainSpec)[78]? = some row' ∧
      SpecEntry.Impl (mkFullEnv mainSpec) fn' row' := by
  let Γ := mkFullEnv mainSpec
  let hPush := mkFullEnv_row_at_ol (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let hAss := mkFullEnv_row_at_ol (mainSpec := mainSpec) 27
    ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
  let hBt := mkFullEnv_row_at_ol (mainSpec := mainSpec) 30
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let hUnw := mkFullEnv_row_at_ol (mainSpec := mainSpec) 56
    ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  let hDet := mkFullEnv_row_at_ol (mainSpec := mainSpec) 77
    ⟨"full_det_new_level", [i64, i64], [i64], fullDetNewLevelSpec, true⟩
  exact ⟨full_one_lit_confl, _, rfl, rfl,
    .of (full_one_lit_confl_wp Γ hDet hBt hAss hUnw hPush)⟩

/-- Index-verified `SpecEntry.Impl fullEnv` bridge for `full_one_lit_confl` at index `78`. -/
theorem full_one_lit_confl_bridge_wp :
    ∃ fn' row', fullFns[78]? = some fn' ∧
      (fullSpecTable fullSolveBytesSpec)[78]? = some row' ∧
      SpecEntry.Impl fullEnv fn' row' :=
  full_one_lit_confl_mk_ok fullSolveBytesSpec

/-! ## 3. Concrete `Mem 64` UNSAT non-vacuity (`nv_full_one_lit_confl`, `XPost := False`) -/

/-- Minimal 1-variable UNSAT formula `{(x0), (¬x0)}` for concrete `full_one_lit_confl` execution. -/
def nvOneLitF0 : CNF Nat := cnfOfClauses [[0], [1]]

/-- Concrete `FullCfg` (`max_vars = 1`, `wcap = 1`, `avail = 1756`, `slack = 0`). -/
def nvOneLitCfg : FullCfg where
  hdr := 0x1000#64
  avail := 1756
  mv := 1
  max_vars := 1
  bva_cap := 0
  nc := 2
  arena_cap := 0
  wcap := 1
  delayed_cap := 0
  red_cap := 0
  extend_cap := 0
  scratch_cap := 0
  hbva := rfl
  hmv := by decide
  hmaxv := by decide
  hnc := by decide
  harena := by decide
  hwcap := by decide
  hdel := by decide
  hred := by decide
  hext := by decide
  hscr := by decide
  havail_fit := by decide
  hsize := by decide

/-- Zero-initialized concrete `FullScratch` for `nvOneLitCfg` (`last_learned = 0xFFFFFFFF`). -/
def nvOneLitScratch : FullScratch where
  heap_len := 0
  scinc := 0#64; rel_period := 0#64; rel_limit := 0#64; rel_wait := 0#64
  rel_u := 0#64; rel_v := 0#64; rel_trigger := 0#64; conflicts := 0#64
  learned_lits := 0#64; min_removed := 0#64; delayed_len := 0; stable := 0#64
  switched := 0#64; mode_count := 0#64; mode_confl_lim := 0#64; mode_tick_lim := 0#64
  mode_saved_ticks := 0#64; search_ticks := 0#64; q_first := 0#64; q_last := 0#64
  q_search_idx := 0#64; q_search_stamp := 0#64; q_cur_stamp := 0#64
  target_assigned := 0#64; best_assigned := 0#64; rephase_limit := 0#64; rephased := 0#64
  reduce_limit := 0#64; reductions := 0#64; tier1 := 0#64; tier2 := 0#64
  restarts := 0#64; restart_limit := 0#64; ema_fast_biased := 0#64; ema_fast_exp := 0#64
  ema_slow_biased := 0#64; ema_slow_exp := 0#64; extend_len := 0; rng_state := 0#64
  chrono_levels := 0#64; otfs_cnt := 0#64; eager_sub_cnt := 0#64; probe_limit := 0#64
  probings := 0#64; elim_limit := 0#64; eliminations := 0#64; elim_bound := 0#64
  iterating := 0#64; hbr_cnt := 0#64; trans_cnt := 0#64; viv_cnt := 0#64
  subst_cnt := 0#64; cong_cnt := 0#64; sweep_cnt := 0#64; bve_cnt := 0#64
  bce_cnt := 0#64; bva_cnt := 0#64; walk_cnt_stat := 0#64; fwd_sub_cnt := 0#64
  fwd_str_cnt := 0#64; ant_sz := 0#64; res_sz := 0#64
  walk_vals := List.replicate 2 0#8
  phases := List.replicate 1 0#8
  phases_target := List.replicate 1 0#8
  phases_best := List.replicate 1 0#8
  walk_best := List.replicate 1 0#8
  heap := List.replicate 1 0#32
  pos := List.replicate 1 0#32
  shrink_stk := List.replicate 1 0#32
  q_prev := List.replicate 1 0#32
  q_next := List.replicate 1 0#32
  q_stamp := List.replicate 1 0#32
  wsort := List.replicate 2 0#32
  work_stk1 := List.replicate 2 0#32
  work_stk2 := List.replicate 2 0#32
  tarjan_mark := List.replicate 2 0#32
  tarjan_reach := List.replicate 2 0#32
  score := List.replicate 1 0#64
  sim_sig := List.replicate 1 0#64
  glue_used := List.replicate 64 0#32
  last_learned := List.replicate 16 0xFFFFFFFF#32
  delayed := []
  red_refs := []
  extend_stk := []
  scratch_buf := []

/-- Concrete level-0 binary-conflict `FullState`: `x0` assigned true at level 0 with falsified
binary conflict `(¬x0 ∨ ¬x0)` entailed by `nvOneLitF0 = {(x0), (¬x0)}`. -/
def nvOneLitState : FullState where
  core :=
    { d_cur := 0#64, d_val := 0#64, cur_vars := 1, unassigned := 0#64
      arena_len := 0, wlen := 1, wusable := 0#64, arena_garbage := 0#64
      first_reducible := 0#64, num_irred := 0#64, num_redundant := 0#64, num_binary := 0#64
      unflushed := 0#64, probing := 0#64, trail_end := 1, propagated := 0
      cur_level := 0, fuel := 0#64, confl_ref := 0#64, confl_type := 1#64
      confl_lit0 := 1#64, confl_lit1 := 1#64, tmp_cnt := 0, tmp_len := 0
      min_clr_len := 0, min_clr_full := 0#64, oom := 0#64, dense_mode := 0#64
      inconsistent := 0#64
      vals := [1#8, 0xFF#8]
      lit_mark := [0#8, 0#8]
      mrk := [0#8]
      flags := [0#32]
      lvl := [0#32]
      rsns := [0xFFFFFFFF#32]
      trl := [0#32]
      trail_pos := [0#32]
      tmp := [0#32]
      min_clr := [0#32]
      frame_trail := [0#32, 0#32]
      frame_dec := [0#32, 0#32]
      wvec := [0#32, 0#32, 0#32, 0#32]
      repr := [0#32, 0#32]
      min_stk := [0#32, 0#32, 0#32, 0#32]
      arena := []
      wstk := [0#32] }
  scratch := nvOneLitScratch

def nvBlockHdr : List UInt8 :=
  bytes64 [1#64, 2#64, 0#64, 0#64] ++ bytes64 (hdrTailWords nvOneLitCfg nvOneLitState)

def nvBlockBytes : List UInt8 :=
  (bytesOf (t := i8) nvOneLitState.core.vals ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvOneLitState.scratch.walk_vals ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvOneLitState.core.lit_mark ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvOneLitState.core.mrk ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvOneLitState.scratch.phases ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvOneLitState.scratch.phases_target ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvOneLitState.scratch.phases_best ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvOneLitState.scratch.walk_best ++ List.replicate 7 0)

def nvBlockU32A : List UInt8 :=
  (bytesOf (t := i32) nvOneLitState.core.flags ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvOneLitState.core.lvl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvOneLitState.core.rsns ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvOneLitState.core.trl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvOneLitState.core.trail_pos ++ List.replicate 4 0)

def nvBlockU32B : List UInt8 :=
  (bytesOf (t := i32) nvOneLitState.core.tmp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvOneLitState.scratch.heap ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvOneLitState.scratch.pos ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvOneLitState.core.min_clr ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvOneLitState.scratch.shrink_stk ++ List.replicate 4 0)

def nvBlockU32C : List UInt8 :=
  (bytesOf (t := i32) nvOneLitState.scratch.q_prev ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvOneLitState.scratch.q_next ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvOneLitState.scratch.q_stamp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvOneLitState.core.frame_trail ++ List.replicate 0 0) ++
  (bytesOf (t := i32) nvOneLitState.core.frame_dec ++ List.replicate 0 0)

def nvBlockWvec : List UInt8 :=
  bytesOf (t := i32) nvOneLitState.core.wvec ++
  bytesOf (t := i32) nvOneLitState.core.repr ++
  bytesOf (t := i32) nvOneLitState.scratch.wsort ++
  bytesOf (t := i32) nvOneLitState.scratch.work_stk1 ++
  bytesOf (t := i32) nvOneLitState.scratch.work_stk2 ++
  bytesOf (t := i32) nvOneLitState.scratch.tarjan_mark ++
  bytesOf (t := i32) nvOneLitState.scratch.tarjan_reach ++
  bytes64 nvOneLitState.scratch.score ++
  bytes64 nvOneLitState.scratch.sim_sig

def nvBlockTail : List UInt8 :=
  bytesOf (t := i32) nvOneLitState.core.min_stk ++
  bytesOf (t := i32) nvOneLitState.scratch.glue_used ++
  bytesOf (t := i32) nvOneLitState.scratch.last_learned ++
  bytesOf (t := i32) nvOneLitState.core.arena ++
  bytesOf (t := i32) nvOneLitState.core.wstk ++
  bytesOf (t := i32) nvOneLitState.scratch.delayed ++
  bytesOf (t := i32) nvOneLitState.scratch.red_refs ++
  bytesOf (t := i32) nvOneLitState.scratch.extend_stk ++
  bytesOf (t := i32) nvOneLitState.scratch.scratch_buf ++
  List.replicate 0 0

/-- Concrete `1756`-byte arena image encoding `nvOneLitCfg` and `nvOneLitState`. -/
def nvOneLitBytes : List UInt8 :=
  nvBlockHdr ++ nvBlockBytes ++ nvBlockU32A ++ nvBlockU32B ++
  nvBlockU32C ++ nvBlockWvec ++ nvBlockTail

/-- Concrete `Mem 64` heap mapped at `nvOneLitCfg.hdr` (`0x1000`). -/
def nvOneLitMem : Mem 64 := nvOneLitBytes.At nvOneLitCfg.hdr

theorem nv_sep_append {P Q : Mem 64 → Prop} {a b : BitVec 64} {bs1 bs2 : List UInt8}
    (hb : b = a + BitVec.ofNat 64 bs1.length) (hlen : bs1.length + bs2.length ≤ 2 ^ 64)
    (h1 : P (bs1.At a)) (h2 : Q (bs2.At b)) : (P ⋆ Q) ((bs1 ++ bs2).At a) := by
  have heq := congrFun (Mem.At_append_sep bs1 bs2 a hlen) ((bs1 ++ bs2).At a)
  rw [← hb] at heq
  exact sep_mono2 (fun _ h => h ▸ h1) (fun _ h => h ▸ h2) _ (heq.mp rfl)

theorem nv_arr_pad {t : Ty} {a : BitVec 64} {xs : List (Val t)} {n pad : Nat}
    (hn : t.bytes * xs.length = n) (hbd : n + pad ≤ 2 ^ 64) :
    (array (t := t) a xs ⋆ region (a + BitVec.ofNat 64 n) pad)
      ((bytesOf xs ++ List.replicate pad 0).At a) :=
  nv_sep_append (by rw [bytesOf_length, hn])
    (by rw [bytesOf_length, List.length_replicate]; omega)
    (array_bytes a xs (by omega)) ⟨List.replicate pad 0, List.length_replicate, rfl⟩

theorem nv_arr_pad_p {t : Ty} {a : BitVec 64} {xs : List (Val t)} (n pad : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n + pad ≤ 2 ^ 64) :
    (bytesOf xs ++ List.replicate pad 0).length = n + pad ∧
    (array (t := t) a xs ⋆ region (a + BitVec.ofNat 64 n) pad)
      ((bytesOf xs ++ List.replicate pad 0).At a) :=
  ⟨by rw [List.length_append, bytesOf_length, List.length_replicate, hn],
    nv_arr_pad hn hbd⟩

theorem nv_arr_p {t : Ty} {a : BitVec 64} {xs : List (Val t)} (n : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytesOf xs).length = n ∧ array (t := t) a xs ((bytesOf xs).At a) :=
  ⟨by rw [bytesOf_length, hn], array_bytes a xs (by omega)⟩

theorem nv_arr64_p {a : BitVec 64} {xs : List (BitVec 64)} (n : Nat)
    (hn : 8 * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytes64 xs).length = n ∧ array64 a xs ((bytes64 xs).At a) :=
  ⟨by rw [bytes64_length, hn], array64_bytes a xs (by omega)⟩

theorem nv_join_pair {P Q : Mem 64 → Prop} {a b : BitVec 64} {bs1 bs2 : List UInt8}
    {n1 n2 : Nat} (h1 : bs1.length = n1 ∧ P (bs1.At a))
    (h2 : bs2.length = n2 ∧ Q (bs2.At b))
    (hb : b = a + BitVec.ofNat 64 n1) (hbd : n1 + n2 ≤ 2 ^ 64) :
    (bs1 ++ bs2).length = n1 + n2 ∧ (P ⋆ Q) ((bs1 ++ bs2).At a) :=
  ⟨by rw [List.length_append, h1.1, h2.1], nv_sep_append (h1.1 ▸ hb) (by omega) h1.2 h2.2⟩

theorem nv_sep_reorg {P Q : Mem 64 → Prop} {bs : List UInt8} {a : BitVec 64} {n : Nat}
    (h : bs.length = n ∧ P (bs.At a)) (himp : ∀ m, P m → Q m) : bs.length = n ∧ Q (bs.At a) :=
  ⟨h.1, himp _ h.2⟩

theorem nv_zip4 {A1 B1 A2 B2 A3 B3 A4 B4 : Mem 64 → Prop} {m : Mem 64}
    (h : ((((A1 ⋆ B1) ⋆ (A2 ⋆ B2)) ⋆ (A3 ⋆ B3)) ⋆ (A4 ⋆ B4)) m) :
    (((A1 ⋆ A3 ⋆ A4) ⋆ A2) ⋆ (B1 ⋆ B2 ⋆ B3 ⋆ B4)) m := sep_ac h

theorem nv_zip4_tail {C A2 P1 A5 B5 A6 B6 A7 B7 A8 B8 : Mem 64 → Prop} {m : Mem 64}
    (h : ((((((C ⋆ A2) ⋆ P1) ⋆ (A5 ⋆ B5)) ⋆ (A6 ⋆ B6)) ⋆ (A7 ⋆ B7)) ⋆ (A8 ⋆ B8)) m) :
    (C ⋆ (A2 ⋆ A5 ⋆ A6 ⋆ A7 ⋆ A8) ⋆ (P1 ⋆ B5 ⋆ B6 ⋆ B7 ⋆ B8)) m := sep_ac h

theorem nvOneLitMem_ok : FullMem nvOneLitCfg nvOneLitState nvOneLitMem := by
  let c := nvOneLitCfg; let s := nvOneLitState
  have hvb : valsBytes c.max_vars - 2 * c.max_vars = 6 := by decide
  have hmb : markBytes c.max_vars - c.max_vars = 7 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 0 := by decide
  have hmv1 : BitVec.ofNat 64 c.max_vars = 1#64 := rfl
  have hmv2 : BitVec.ofNat 64 (2 * c.max_vars) = 2#64 := rfl
  have hmv4 : BitVec.ofNat 64 (4 * c.max_vars) = 4#64 := rfl
  have hmv8 : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 8#64 := rfl
  have hHdr : nvBlockHdr.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (hdrTailWords c s))
        (nvBlockHdr.At c.hdr) :=
    nv_join_pair
      (nv_arr64_p (a := c.hdr) (xs := [1#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
      (nv_arr64_p (a := c.hdr + 32) (xs := hdrTailWords c s) 1120
        (by rw [hdrTailWords_length]) (by decide))
      (by decide) (by decide)
  have hBytes : nvBlockBytes.length = 64 ∧
      (FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ c.padBytes)
        (nvBlockBytes.At c.pVals) := by
    have h1 := nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 2 6 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 2 6 rfl
      (by decide)
    have h3 := nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 2 6 rfl
      (by decide)
    have h4 := nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 1 7 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 1 7 rfl
      (by decide)
    have h6 := nv_arr_pad_p (t := i8) (a := c.pPhasesTarget) (xs := s.scratch.phases_target) 1 7
      rfl (by decide)
    have h7 := nv_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best) 1 7 rfl
      (by decide)
    have h8 := nv_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best) 1 7 rfl
      (by decide)
    let pB1 : Mem 64 → Prop :=
      region (c.pVals + 2#64) 6 ⋆ region (c.pWalkVals + 2#64) 6 ⋆
      region (c.pLitMark + 2#64) 6 ⋆ region (c.pMark + 1#64) 7
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_sep_reorg (nv_join_pair h123 h4 (by decide) (by decide))
      (Q := (FullCoreByteArrs c s.core ⋆ array (t := i8) c.pWalkVals s.scratch.walk_vals) ⋆ pB1)
      fun _ hm => nv_zip4 hm
    have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
    have hall := nv_join_pair h1234567 h8 (by decide) (by decide)
    exact nv_sep_reorg hall fun _ hm => by
      have hfin := nv_zip4_tail hm
      unfold FullScrByteArrs FullCfg.padBytes
      rw [hvb, hmb, hmv2, hmv1]
      simpa only [pB1, sep_assoc] using hfin
  have hU32A : nvBlockU32A.length = 40 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        (nvBlockU32A.At c.pFlags) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 4 4 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 4 4 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 4 4 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 4 4 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 4 4 rfl
      (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu4, hmv4]; exact sep_ac hm
  have hU32B : nvBlockU32B.length = 40 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
        (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
         array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        (nvBlockU32B.At c.pTmp) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 4 4 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 4 4 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 4 4 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 4 4 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk) 4 4 rfl
      (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu4, hmv4]; exact sep_ac hm
  have hU32C : nvBlockU32C.length = 40 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        (nvBlockU32C.At c.pQPrev) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 4 4 rfl
      (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 4 4 rfl
      (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 4 4 rfl
      (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 8 0 rfl
      (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 8 0 rfl
      (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu4, hu8, hmv4, hmv8]; exact sep_ac hm
  have hWvec : nvBlockWvec.length = 80 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        (nvBlockWvec.At c.pWvec) := by
    have h1 := nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 16 rfl (by decide)
    have h2 := nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 8 rfl (by decide)
    have h3 := nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 8 rfl (by decide)
    have h4 := nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 8 rfl
      (by decide)
    have h5 := nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 8 rfl
      (by decide)
    have h6 := nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 8 rfl
      (by decide)
    have h7 := nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 8 rfl
      (by decide)
    have h8 := nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 8 rfl (by decide)
    have h9 := nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 8 rfl (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := nv_join_pair h1234567 h8 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail : nvBlockTail.length = 340 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        (nvBlockTail.At c.pMinStk) := by
    have h1 := nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 16 rfl (by decide)
    have h2 := nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256 rfl
      (by decide)
    have h3 := nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned) 64 rfl
      (by decide)
    have h4 := nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 0 rfl (by decide)
    have h5 := nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 4 rfl (by decide)
    have h6 := nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl (by decide)
    have h7 := nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl (by decide)
    have h8 := nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl
      (by decide)
    have h9 := nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 0 rfl
      (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 0).At c.pSlack) :=
      ⟨rfl, ⟨List.replicate 0 0, by decide, rfl⟩⟩
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := nv_join_pair h1234567 h8 (by decide) (by decide)
    have h123456789 := nv_join_pair h12345678 h9 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h123456789 h10 (by decide) (by decide)) fun _ hm => by
      unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := nv_join_pair hHdr hBytes (by decide) (by decide)
  have h02 := nv_join_pair h01 hU32A (by decide) (by decide)
  have h03 := nv_join_pair h02 hU32B (by decide) (by decide)
  have h04 := nv_join_pair h03 hU32C (by decide) (by decide)
  have h05 := nv_join_pair h04 hWvec (by decide) (by decide)
  exact (nv_sep_reorg (nv_join_pair h05 hTail (by decide) (by decide)) fun _ hm => by
    unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
      FullScrMetaArrs FullCfg.pad
    exact sep_ac hm).2

theorem nvOneLit_lengths : nvOneLitState.LengthsOk nvOneLitCfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem nvOneLit_entails_0 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) := by
  rw [CNF.entails_clause_def]; intro α hα
  exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))

private theorem nvOneLit_entails_11 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [1, 1]) := by
  rw [CNF.entails_clause_def]; intro α hα
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h1 ⊢
  obtain ⟨lit, hm, heq⟩ := h1
  refine ⟨lit, ?_, heq⟩
  rw [mem_cnfClause_iff] at hm ⊢; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
  exact Or.inl hm

private theorem nvOneLit_witness :
    FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState.core := by
  have hrefs : fullArenaClauseRefsCore nvOneLitState.core = [] := rfl
  have hcv : nvOneLitState.core.cur_vars = 1 := rfl
  have hte : nvOneLitState.core.trail_end = 1 := rfl
  have hcl : nvOneLitState.core.cur_level = 0 := rfl
  have hdm : nvOneLitState.core.dense_mode = 0#64 := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvOneLitState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvOneLitState] at hp)
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvOneLitState] at hp)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        exact WatchSliceOk.empty
  exact
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩
      watches := hwat
      cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hte] at hi hj; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · constructor
          · intro h; cases h
          · rintro ⟨i, hi, h⟩; rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · constructor
          · intro h; cases h
          · rintro ⟨i, hi, h⟩; rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact Nat.le_refl 0
      dec_earliest := fun _ j _ hj _ hpos => by
        rw [hte] at hj; obtain rfl : j = 0 := (by omega); exact absurd hpos.1 (by decide)
      levels_inhabited := fun L h1 h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact nvOneLit_entails_0
      trail_pos_inv := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      level0_rsn_none := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      frame_trail_lt := fun L hL => by rw [hcl] at hL; obtain rfl : L = 0 := (by omega); decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega)
        obtain rfl : L2 = 0 := (by omega); exact Nat.le_refl _
      frame_trail_before_lt := fun L h1 h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun L h1 h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne }

/-- Concrete `Mem 64` UNSAT non-vacuity for `full_one_lit_confl` under `fullEnv` with
`XPost := False`: on the level-0 binary conflict in `nvOneLitMem`, `full_one_lit_confl_body`
returns `20#64`, certifies `nvOneLitF0.Unsat`, and preserves `FullMem nvOneLitCfg nvOneLitState`. -/
theorem nv_full_one_lit_confl :
    Func.wp fullEnv full_one_lit_confl_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' =>
        r = 20#64 ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg nvOneLitState m')
      (fun _ _ _ _ => False) := by
  let hAss := mkFullEnv_row_at_ol (mainSpec := fullSolveBytesSpec) 27
    ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
  let hBt := mkFullEnv_row_at_ol (mainSpec := fullSolveBytesSpec) 30
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let hDet := mkFullEnv_row_at_ol (mainSpec := fullSolveBytesSpec) 77
    ⟨"full_det_new_level", [i64, i64], [i64], fullDetNewLevelSpec, true⟩
  have hmv : nvOneLitCfg.max_vars = 1 := rfl
  have hcl : nvOneLitState.core.cur_level = 0 := rfl
  have hconflW : FullConflictOkW [[0], [1]] nvOneLitState :=
    Or.inl ⟨rfl, by decide, by decide, rfl, rfl, nvOneLit_entails_11⟩
  have hmarks : FullLitMarksClear nvOneLitCfg nvOneLitState := by
    refine ⟨fun v hv => ?_, fun l hl => ?_⟩
    · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
    · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  have hnd : FullArenaVarsNodup nvOneLitState := fun r hr => by
    have : fullArenaClauseRefs nvOneLitState = [] := rfl
    simp [this] at hr
  have hext : FullExtScratchOk nvOneLitCfg nvOneLitState :=
    ⟨FullLastLearnedWf.of_cleared fun i hi => by
      simp only [nvOneLitState, nvOneLitScratch, List.getElem?_replicate, show i < 16 by omega,
        ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  refine oneLit_bin_branch_wp fullEnv hDet hBt hAss nvOneLit_lengths rfl nvOneLit_witness.toCut
    hmarks hnd hext (Nat.le_refl _) (hconflW.toCut nvOneLit_witness) rfl hm ?_
  intro r s' m' _ hr _ _ _ _ _ _ _ _ hnb h20 h1 _ h0 hm'
  rw [sep_emp] at hm'
  rcases hr with rfl | rfl | rfl | rfl
  · obtain ⟨_, _, _, hpos, hle, _⟩ := h0 rfl
    rw [hcl] at hle; omega
  · obtain ⟨_, hlt⟩ := h1 rfl
    rw [hcl] at hlt; omega
  · exact absurd rfl (hnb rfl)
  · obtain ⟨hu, rfl⟩ := h20 rfl
    exact ⟨rfl, hu, hm'⟩

end LeanQbe.T.Examples.Kissat.Full
