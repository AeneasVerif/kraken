module

public import LeanQbe.T.Examples.Kissat.FullSweepFwdLemmas1
public import LeanQbe.T.Examples.Kissat.FullSweepFwdLemmas2
meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat `D-Full` Bounded Cone SAT Sweeping — Part 3 (`Stage 4`)

Parametric `(Γ : Env)` `Func.wp` proof for:
4. `full_sweep_dpll` (`full_sweep_dpll_wp`, `Full.lean` #13)

Re-exports all 4 shard theorems (`full_sweep_add_cl_wp`, `full_sweep_cone_wp`,
`full_sweep_dpll_wp`, `full_sweep_refine_wp`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test
open FullSweepFwdSpecs FullSweepFwdHelpers

section
open scoped FullArenaTactics FullSweepFwdTactics FullSweepFwdFast

/-! ## 1. Pure DPLL state model and soundness transitions -/

private abbrev dArr (off : Nat) (scr : List (BitVec 32)) (i : Nat) : BitVec 32 :=
  scr[off + i]?.getD 0#32
private abbrev dVal (scr : List (BitVec 32)) (v : Nat) : BitVec 32 := dArr 1024 scr v
private abbrev dDv (scr : List (BitVec 32)) (k : Nat) : BitVec 32 := dArr 1048 scr k
private abbrev dDph (scr : List (BitVec 32)) (k : Nat) : BitVec 32 := dArr 1072 scr k
private abbrev dTrl (scr : List (BitVec 32)) (j : Nat) : BitVec 32 := dArr 1096 scr j
private abbrev dDt (scr : List (BitVec 32)) (k : Nat) : BitVec 32 := dArr 1120 scr k

private def dValMatch (v : Nat) (w : BitVec 32) (α : Nat → Bool) : Prop := α v = decide (w = 1#32)
private def dTrailAgrees (scr : List (BitVec 32)) (len : Nat) (α : Nat → Bool) : Prop :=
  ∀ j < len, dValMatch (dTrl scr j).toNat (dVal scr (dTrl scr j).toNat) α
private def dBranchPrefix (scr : List (BitVec 32)) (lvl : Nat) (α : Nat → Bool) : Prop :=
  ∀ k < lvl, dValMatch (dDv scr k).toNat (dVal scr (dDv scr k).toNat) α
private def dWant (l : Nat) : BitVec 32 := BitVec.ofNat 32 (l % 2 + 1)

private structure DpllStateOk (s0 : FullState) (scr : List (BitVec 32))
    (nv nc a0 a1 tn sp : Nat) : Prop where
  len_eq : scr.length = s0.scratch.scratch_buf.length
  prefix_eq : ∀ i < 1024, scr[i]? = s0.scratch.scratch_buf[i]?
  sp_le_tn : sp ≤ tn
  tn_le_nv : tn ≤ nv
  val_dom : ∀ v < nv, dVal scr v = 0#32 ∨ dVal scr v = 1#32 ∨ dVal scr v = 2#32
  trl_lt : ∀ j < tn, (dTrl scr j).toNat < nv
  trl_nz : ∀ j < tn, dVal scr (dTrl scr j).toNat ≠ 0#32
  trl_inj : ∀ j1 j2, j1 < tn → j2 < tn → (dTrl scr j1).toNat = (dTrl scr j2).toNat → j1 = j2
  val_on_trl : ∀ v < nv, dVal scr v ≠ 0#32 → ∃ j < tn, (dTrl scr j).toNat = v
  dph_dom : ∀ k < sp, dDph scr k = 0#32 ∨ dDph scr k = 1#32
  dt_lt : ∀ k < sp, (dDt scr k).toNat < tn
  dt_mono : ∀ k1 k2, k1 < k2 → k2 < sp → (dDt scr k1).toNat < (dDt scr k2).toNat
  dv_eq_trl : ∀ k < sp, dDv scr k = dTrl scr (dDt scr k).toNat
  trail_sound : ∀ α, DpllSubprobSat s0 nv nc a0 a1 α → ∀ lvl ≤ sp, dBranchPrefix scr lvl α →
    dTrailAgrees scr (if lvl = sp then tn else (dDt scr lvl).toNat) α
  search_sound : ∀ α, DpllSubprobSat s0 nv nc a0 a1 α →
    dBranchPrefix scr sp α ∨
    ∃ k < sp, dDph scr k = 0#32 ∧ dBranchPrefix scr k α ∧
      ¬ dValMatch (dDv scr k).toNat (dVal scr (dDv scr k).toNat) α

private theorem dLit_sat_iff_dValMatch {l : Nat} {α : Nat → Bool} :
    (cnfClause [l]).Sat α ↔ dValMatch (l / 2) (dWant l) α := by
  simp only [sat_cnfClause_singleton, dValMatch, dWant, litVar, litSign]
  rcases Nat.mod_two_eq_zero_or_one l with h | h <;> simp [h]

private theorem dWant_eq_bv (l : BitVec 32) : (l &&& 1#32) + 1#32 = dWant l.toNat := by
  have ha : (l &&& 1#32).toNat = l.toNat % 2 := by
    rw [BitVec.toNat_and, show (1#32).toNat = 1 from rfl]
    simp [Nat.and_two_pow_sub_one_eq_mod l.toNat 1]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, ha, show (1#32).toNat = 1 from rfl, dWant, BitVec.toNat_ofNat]

private theorem dWant_dom (l : Nat) : dWant l = 1#32 ∨ dWant l = 2#32 := by
  unfold dWant; rcases Nat.mod_two_eq_zero_or_one l with h | h <;> simp [h]

private theorem dValMatch_flip {v : Nat} {w : BitVec 32} {α : Nat → Bool}
    (hw : w = 1#32 ∨ w = 2#32) : dValMatch v (3#32 - w) α ↔ ¬ dValMatch v w α := by
  unfold dValMatch; rcases hw with rfl | rfl <;> cases h : α v <;> decide

private theorem dValMatch_ne_contra {v : Nat} {w1 w2 : BitVec 32} {α : Nat → Bool}
    (h1 : w1 = 1#32 ∨ w1 = 2#32) (h2 : w2 = 1#32 ∨ w2 = 2#32) (hne : w1 ≠ w2)
    (hm1 : dValMatch v w1 α) (hm2 : dValMatch v w2 α) : False := by
  unfold dValMatch at hm1 hm2
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    first | exact hne rfl | exact absurd (hm1 ▸ hm2) (by decide)

private theorem dArr_set_self {off i : Nat} {scr : List (BitVec 32)} {w : BitVec 32}
    (h : off + i < scr.length) : dArr off (scr.set (off + i) w) i = w := by
  unfold dArr; rw [List.getElem?_set_self h, Option.getD_some]

private theorem dArr_set_ne {off i idx : Nat} {scr : List (BitVec 32)} {w : BitVec 32}
    (hne : idx ≠ off + i) : dArr off (scr.set idx w) i = dArr off scr i := by
  unfold dArr; rw [List.getElem?_set_ne hne]

private theorem dBranchPrefix_congr {scr1 scr2 : List (BitVec 32)} {lvl : Nat} {α : Nat → Bool}
    (hdv : ∀ k < lvl, dDv scr1 k = dDv scr2 k)
    (hval : ∀ k < lvl, dVal scr1 (dDv scr2 k).toNat = dVal scr2 (dDv scr2 k).toNat) :
    dBranchPrefix scr1 lvl α ↔ dBranchPrefix scr2 lvl α :=
  ⟨fun h k hk => by simpa only [hdv k hk, hval k hk] using h k hk,
   fun h k hk => by simpa only [hdv k hk, hval k hk] using h k hk⟩

private theorem dpll_state_zero_ok {s0 : FullState} {scr : List (BitVec 32)} {nv nc a0 a1 : Nat}
    (hlen : scr.length = s0.scratch.scratch_buf.length)
    (hpre : ∀ i < 1024, scr[i]? = s0.scratch.scratch_buf[i]?)
    (hval0 : ∀ v < nv, dVal scr v = 0#32) : DpllStateOk s0 scr nv nc a0 a1 0 0 :=
  ⟨hlen, hpre, Nat.le_refl 0, Nat.zero_le nv, fun v hv => Or.inl (hval0 v hv),
   fun _ h => by omega, fun _ h => by omega, fun _ _ h => by omega,
   fun v hv hnz => absurd (hval0 v hv) hnz, fun _ h => by omega, fun _ h => by omega,
   fun _ _ _ h => by omega, fun _ h => by omega,
   fun _ _ lvl hlvl _ j hj => by cases Nat.le_zero.mp hlvl; simp at hj,
   fun _ _ => Or.inl fun _ h => by omega⟩

private theorem dpll_tn_lt_of_unassigned {s0 : FullState} {scr : List (BitVec 32)}
    {nv nc a0 a1 tn sp v : Nat} (hd : DpllStateOk s0 scr nv nc a0 a1 tn sp)
    (hv : v < nv) (h0 : dVal scr v = 0#32) : tn < nv :=
  inj_lt_of_missing (fun j => (dTrl scr j).toNat)
    (fun j1 j2 h1 h2 heq => hd.trl_inj j1 j2 h1 h2 heq)
    (fun j hj => hd.trl_lt j hj) hv (fun j hj heq => hd.trl_nz j hj (heq ▸ h0))

/-- Push an implied unassigned literal `(u, w)` onto the trail at decision level `sp`. -/
private theorem dpll_push_implied {s0 : FullState} {scr : List (BitVec 32)}
    {nv nc a0 a1 tn sp : Nat} {u w : BitVec 32}
    (hcap : 1152 ≤ s0.scratch.scratch_buf.length) (hnv24 : nv ≤ 24)
    (hd : DpllStateOk s0 scr nv nc a0 a1 tn sp)
    (hu : u.toNat < nv) (hval0 : dVal scr u.toNat = 0#32) (hw : w = 1#32 ∨ w = 2#32)
    (himp : ∀ α, DpllSubprobSat s0 nv nc a0 a1 α → dBranchPrefix scr sp α → dValMatch u.toNat w α) :
    let scr' := (scr.set (1024 + u.toNat) w).set (1096 + tn) u
    tn < nv ∧ DpllStateOk s0 scr' nv nc a0 a1 (tn + 1) sp := by
  intro scr'
  have htn_lt : tn < nv := dpll_tn_lt_of_unassigned hd hu hval0
  have hlen := hd.len_eq; have hsp_le := hd.sp_le_tn; have htn_le := hd.tn_le_nv
  have hne_trl : ∀ j < tn, (dTrl scr j).toNat ≠ u.toNat :=
    fun j hj heq => hd.trl_nz j hj (heq ▸ hval0)
  have hdv_lt : ∀ k < sp, (dDv scr k).toNat < nv ∧ (dDv scr k).toNat ≠ u.toNat := fun k hk => by
    have he := congrArg BitVec.toNat (hd.dv_eq_trl k hk)
    exact ⟨he ▸ hd.trl_lt _ (hd.dt_lt k hk), he ▸ hne_trl _ (hd.dt_lt k hk)⟩
  have hval_u : dVal scr' u.toNat = w := by
    dsimp only [scr', dVal]; rw [dArr_set_ne (by omega), dArr_set_self (by omega)]
  have hval_ne : ∀ v < nv, v ≠ u.toNat → dVal scr' v = dVal scr v := fun v hv hne => by
    dsimp only [scr', dVal]; rw [dArr_set_ne (by omega), dArr_set_ne (by omega)]
  have htrl_old : ∀ j < tn, dTrl scr' j = dTrl scr j := fun j hj => by
    dsimp only [scr', dTrl]; rw [dArr_set_ne (by omega), dArr_set_ne (by omega)]
  have htrl_new : dTrl scr' tn = u := by
    dsimp only [scr', dTrl]; rw [dArr_set_self (by simp; omega)]
  have hdv_eq : ∀ k < sp, dDv scr' k = dDv scr k := fun k hk => by
    dsimp only [scr', dDv]; rw [dArr_set_ne (by omega), dArr_set_ne (by omega)]
  have hdph_eq : ∀ k < sp, dDph scr' k = dDph scr k := fun k hk => by
    dsimp only [scr', dDph]; rw [dArr_set_ne (by omega), dArr_set_ne (by omega)]
  have hdt_eq : ∀ k < sp, dDt scr' k = dDt scr k := fun k hk => by
    dsimp only [scr', dDt]; rw [dArr_set_ne (by omega), dArr_set_ne (by omega)]
  have hbp_iff : ∀ lvl ≤ sp, ∀ α, dBranchPrefix scr' lvl α ↔ dBranchPrefix scr lvl α :=
    fun lvl hlvl _ => dBranchPrefix_congr (fun k hk => hdv_eq k (by omega))
      (fun k hk => hval_ne _ (hdv_lt k (by omega)).1 (hdv_lt k (by omega)).2)
  refine ⟨htn_lt, {
    len_eq := by simp [scr', hlen]
    prefix_eq := fun i hi => by
      dsimp only [scr']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hd.prefix_eq i hi
    sp_le_tn := by omega
    tn_le_nv := by omega
    val_dom := fun v hv => by
      by_cases hvu : v = u.toNat
      · subst hvu; rw [hval_u]; exact Or.inr hw
      · rw [hval_ne v hv hvu]; exact hd.val_dom v hv
    trl_lt := fun j hj => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · exact htrl_old j hlt ▸ hd.trl_lt j hlt
      · exact htrl_new ▸ hu
    trl_nz := fun j hj => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · rw [htrl_old j hlt, hval_ne _ (hd.trl_lt j hlt) (hne_trl j hlt)]; exact hd.trl_nz j hlt
      · rw [htrl_new, hval_u]; rcases hw with rfl | rfl <;> decide
    trl_inj := fun j1 j2 h1 h2 heq => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h1' | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2' | rfl
      · rw [htrl_old j1 h1', htrl_old j2 h2'] at heq; exact hd.trl_inj j1 j2 h1' h2' heq
      · exact absurd (htrl_old j1 h1' ▸ htrl_new ▸ heq) (hne_trl j1 h1')
      · exact absurd (htrl_new ▸ htrl_old j2 h2' ▸ heq).symm (hne_trl j2 h2')
      · rfl
    val_on_trl := fun v hv hnz => by
      by_cases hvu : v = u.toNat
      · exact ⟨tn, by omega, by rw [htrl_new, hvu]⟩
      · rw [hval_ne v hv hvu] at hnz; obtain ⟨j, hj, htr⟩ := hd.val_on_trl v hv hnz
        exact ⟨j, by omega, by rw [htrl_old j hj]; exact htr⟩
    dph_dom := fun k hk => by rw [hdph_eq k hk]; exact hd.dph_dom k hk
    dt_lt := fun k hk => by rw [hdt_eq k hk]; have := hd.dt_lt k hk; omega
    dt_mono := fun k1 k2 h12 h2 => by
      rw [hdt_eq k1 (by omega), hdt_eq k2 h2]; exact hd.dt_mono k1 k2 h12 h2
    dv_eq_trl := fun k hk => by
      rw [hdv_eq k hk, hdt_eq k hk, htrl_old _ (hd.dt_lt k hk)]; exact hd.dv_eq_trl k hk
    trail_sound := fun α hα lvl hlvl hbp => by
      have hbp0 := (hbp_iff lvl hlvl α).mp hbp; have hts0 := hd.trail_sound α hα lvl hlvl hbp0
      by_cases hls : lvl = sp
      · simp only [hls, ↓reduceIte] at hts0 ⊢; intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
        · rw [htrl_old j hlt, hval_ne _ (hd.trl_lt j hlt) (hne_trl j hlt)]; exact hts0 j hlt
        · rw [htrl_new, hval_u]; exact himp α hα (hls ▸ hbp0)
      · simp only [hls, ↓reduceIte] at hts0 ⊢; rw [hdt_eq lvl (by omega)]; intro j hj
        have hj_tn := Nat.lt_trans hj (hd.dt_lt lvl (by omega))
        rw [htrl_old j hj_tn, hval_ne _ (hd.trl_lt j hj_tn) (hne_trl j hj_tn)]; exact hts0 j hj
    search_sound := fun α hα => by
      rcases hd.search_sound α hα with hbp | ⟨k, hk, hdph0, hbpk, hneg⟩
      · exact Or.inl ((hbp_iff sp (Nat.le_refl _) α).mpr hbp)
      · refine Or.inr ⟨k, hk, hdph_eq k hk ▸ hdph0, (hbp_iff k (by omega) α).mpr hbpk, ?_⟩
        rw [hdv_eq k hk, hval_ne _ (hdv_lt k hk).1 (hdv_lt k hk).2]; exact hneg
  }⟩

/-- Conflict on `a1` against already-assigned `a0` implies subproblem UNSAT. -/
private theorem dpll_assump_confl_unsat {s0 : FullState} {scr : List (BitVec 32)}
    {nv nc a0 tn : Nat} {a1 : BitVec 32} (hd : DpllStateOk s0 scr nv nc a0 a1.toNat tn 0)
    (ha1 : a1.toNat < 2 * nv) (hnz : dVal scr (a1.toNat / 2) ≠ 0#32)
    (hne : dVal scr (a1.toNat / 2) ≠ dWant a1.toNat) :
    ∀ α, ¬ DpllSubprobSat s0 nv nc a0 a1.toNat α := by
  intro α hα
  have hts := hd.trail_sound α hα 0 (Nat.le_refl 0) (fun _ h => by omega)
  simp only [↓reduceIte] at hts
  have hv_lt : a1.toNat / 2 < nv := by omega
  obtain ⟨j, hj, htr⟩ := hd.val_on_trl _ hv_lt hnz
  have hm1 : dValMatch (a1.toNat / 2) (dVal scr (a1.toNat / 2)) α := htr ▸ hts j hj
  have hm2 : dValMatch (a1.toNat / 2) (dWant a1.toNat) α :=
    dLit_sat_iff_dValMatch.mp (hα.1.2 ha1)
  have hdom1 : dVal scr (a1.toNat / 2) = 1#32 ∨ dVal scr (a1.toNat / 2) = 2#32 :=
    (hd.val_dom _ hv_lt).elim (fun h0 => absurd h0 hnz) id
  exact dValMatch_ne_contra hdom1 (dWant_dom a1.toNat) hne hm1 hm2

private theorem dpll_lit_false_contra {s0 : FullState} {scr : List (BitVec 32)}
    {nv nc a0 a1 tn sp l : Nat} (hd : DpllStateOk s0 scr nv nc a0 a1 tn sp) {α : Nat → Bool}
    (hts : dTrailAgrees scr tn α) (hl_lt : l < 2 * nv) (hl_sat : (cnfClause [l]).Sat α)
    (hnz : dVal scr (l / 2) ≠ 0#32) (hne : dVal scr (l / 2) ≠ dWant l) : False := by
  obtain ⟨j, hj, htr⟩ := hd.val_on_trl _ (by omega) hnz
  have hdom1 : dVal scr (l / 2) = 1#32 ∨ dVal scr (l / 2) = 2#32 :=
    (hd.val_dom _ (by omega)).elim (fun h0 => absurd h0 hnz) id
  exact dValMatch_ne_contra hdom1 (dWant_dom l) hne (htr ▸ hts j hj)
    (dLit_sat_iff_dValMatch.mp hl_sat)

private theorem dpll_clause_confl {s0 : FullState} {scr : List (BitVec 32)}
    {nv nc a0 a1 tn sp ci : Nat} (hcap : 1152 ≤ s0.scratch.scratch_buf.length)
    (hbuf : SweepBufClausesOk s0 nv nc) (hd : DpllStateOk s0 scr nv nc a0 a1 tn sp)
    (hci : ci < nc)
    (hfals : ∀ k < (s0.scratch.scratch_buf[64 + ci]?.getD 0#32).toNat,
      let l := (s0.scratch.scratch_buf[(s0.scratch.scratch_buf[ci]?.getD 0#32).toNat + k]?.getD
        0#32).toNat
      dVal scr (l / 2) ≠ 0#32 ∧ dVal scr (l / 2) ≠ dWant l) :
    ∀ α, DpllSubprobSat s0 nv nc a0 a1 α → ¬ dBranchPrefix scr sp α := by
  intro α hα hbp
  have hts := hd.trail_sound α hα sp (Nat.le_refl sp) hbp; simp only [↓reduceIte] at hts
  have hci_ok := hbuf.2.2.2.2 ci hci; have hres := hbuf.2.2.2.1
  obtain ⟨l, hl_mem, hl_sat⟩ := (clause_sat_cnfClause_iff _ _).mp (hα.2 ci hci)
  have hl_lt : l < 2 * nv := hci_ok.2.2 l hl_mem
  rw [sweepClauseLits_eq_range (by omega)] at hl_mem
  obtain ⟨k, hk_r, rfl⟩ := List.mem_map.mp hl_mem
  obtain ⟨hnz, hne⟩ := hfals k (List.mem_range.mp hk_r)
  exact dpll_lit_false_contra hd hts hl_lt ((sat_cnfClause_singleton _ _).mpr hl_sat) hnz hne

private theorem dpll_clause_unit_imp {s0 : FullState} {scr : List (BitVec 32)}
    {nv nc a0 a1 tn sp ci : Nat} {ul : BitVec 32} (hcap : 1152 ≤ s0.scratch.scratch_buf.length)
    (hbuf : SweepBufClausesOk s0 nv nc) (hd : DpllStateOk s0 scr nv nc a0 a1 tn sp)
    (hci : ci < nc)
    (hunit : ∀ k < (s0.scratch.scratch_buf[64 + ci]?.getD 0#32).toNat,
      let l := (s0.scratch.scratch_buf[(s0.scratch.scratch_buf[ci]?.getD 0#32).toNat + k]?.getD
        0#32).toNat
      l = ul.toNat ∨ (dVal scr (l / 2) ≠ 0#32 ∧ dVal scr (l / 2) ≠ dWant l)) :
    ∀ α, DpllSubprobSat s0 nv nc a0 a1 α → dBranchPrefix scr sp α →
      dValMatch (ul.toNat / 2) (dWant ul.toNat) α := by
  intro α hα hbp
  have hts := hd.trail_sound α hα sp (Nat.le_refl sp) hbp; simp only [↓reduceIte] at hts
  have hci_ok := hbuf.2.2.2.2 ci hci; have hres := hbuf.2.2.2.1
  obtain ⟨l, hl_mem, hl_sat⟩ := (clause_sat_cnfClause_iff _ _).mp (hα.2 ci hci)
  have hl_lt : l < 2 * nv := hci_ok.2.2 l hl_mem
  rw [sweepClauseLits_eq_range (by omega)] at hl_mem
  obtain ⟨k, hk_r, rfl⟩ := List.mem_map.mp hl_mem
  rcases hunit k (List.mem_range.mp hk_r) with heq | ⟨hnz, hne⟩
  · exact heq ▸ dLit_sat_iff_dValMatch.mp ((sat_cnfClause_singleton _ _).mpr hl_sat)
  · exact absurd (dpll_lit_false_contra hd hts hl_lt
      ((sat_cnfClause_singleton _ _).mpr hl_sat) hnz hne) False.elim

private theorem dpll_sp_le_dt {s0 : FullState} {scr : List (BitVec 32)}
    {nv nc a0 a1 tn sp k : Nat} (hd : DpllStateOk s0 scr nv nc a0 a1 tn sp) (hk : k < sp) :
    k ≤ (dDt scr k).toNat := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    have hm_lt : m < m + 1 := Nat.lt_succ_self m
    have := hd.dt_mono m (m + 1) hm_lt hk; have := ih (Nat.lt_trans hm_lt hk); omega

/-- After stripping `dph = 1` decisions down to `sp'`, unwinding trail to `target = dt[sp']`,
and flipping `dv[sp']` with `dph = 1`, `DpllStateOk` is restored at `(target + 1, sp' + 1)`. -/
private theorem dpll_backtrack_flip_ok {s0 : FullState} {scr0 scr_u : List (BitVec 32)}
    {nv nc a0 a1 tn0 sp0 sp' : Nat} (hcap : 1152 ≤ s0.scratch.scratch_buf.length) (hnv24 : nv ≤ 24)
    (hd : DpllStateOk s0 scr0 nv nc a0 a1 tn0 sp0) (hsp' : sp' < sp0)
    (hdph0 : dDph scr0 sp' = 0#32)
    (hsearch : ∀ α, DpllSubprobSat s0 nv nc a0 a1 α →
      ∃ k ≤ sp', dDph scr0 k = 0#32 ∧ dBranchPrefix scr0 k α ∧
        ¬ dValMatch (dDv scr0 k).toNat (dVal scr0 (dDv scr0 k).toNat) α)
    (hlen_u : scr_u.length = scr0.length)
    (hnonval : ∀ i, ¬ (1024 ≤ i ∧ i < 1048) → scr_u[i]? = scr0[i]?)
    (hval_uz : ∀ v < nv,
      (∃ j, (dDt scr0 sp').toNat ≤ j ∧ j < tn0 ∧ (dTrl scr0 j).toNat = v) → dVal scr_u v = 0#32)
    (hval_up : ∀ v < nv,
      (∀ j, (dDt scr0 sp').toNat ≤ j → j < tn0 → (dTrl scr0 j).toNat ≠ v) →
      dVal scr_u v = dVal scr0 v) :
    let v := dDv scr0 sp'
    let nv_w := 3#32 - dVal scr0 v.toNat
    let target := (dDt scr0 sp').toNat
    let scr1 := scr_u.set (1072 + sp') 1#32
    let scr2 := scr1.set (1120 + sp') (BitVec.ofNat 32 target)
    let scr3 := scr2.set (1024 + v.toNat) nv_w
    let scr4 := scr3.set (1096 + target) v
    target < tn0 ∧ v.toNat < nv ∧ DpllStateOk s0 scr4 nv nc a0 a1 (target + 1) (sp' + 1) := by
  intro v nv_w target scr1 scr2 scr3 scr4
  have hlen0 := hd.len_eq; have hsp0_le := hd.sp_le_tn; have htn0_le := hd.tn_le_nv
  have htg_lt : target < tn0 := hd.dt_lt sp' hsp'
  have hv_eq_trl : v = dTrl scr0 target := hd.dv_eq_trl sp' hsp'
  have hv_lt : v.toNat < nv := congrArg BitVec.toNat hv_eq_trl ▸ hd.trl_lt target htg_lt
  have hv_nz : dVal scr0 v.toNat ≠ 0#32 :=
    congrArg BitVec.toNat hv_eq_trl ▸ hd.trl_nz target htg_lt
  have hv_dom : dVal scr0 v.toNat = 1#32 ∨ dVal scr0 v.toNat = 2#32 :=
    (hd.val_dom v.toNat hv_lt).elim (fun h0 => absurd h0 hv_nz) id
  have hnw_dom : nv_w = 1#32 ∨ nv_w = 2#32 := by
    dsimp only [nv_w]; rcases hv_dom with h | h <;> rw [h] <;> decide
  have hsp_le_tg : sp' ≤ target := dpll_sp_le_dt hd hsp'
  have htrl_pre : ∀ j < target, (dTrl scr0 j).toNat ≠ v.toNat := fun j hj heq => by
    have := hd.trl_inj j target (by omega) htg_lt (heq.trans (congrArg BitVec.toNat hv_eq_trl))
    omega
  have hval_u_pre : ∀ j < target, dVal scr_u (dTrl scr0 j).toNat = dVal scr0 (dTrl scr0 j).toNat :=
    fun j hj => hval_up _ (hd.trl_lt j (by omega)) fun j' hj'1 hj'2 heq => by
      have := hd.trl_inj j' j hj'2 (by omega) heq; omega
  have hdv_eq : ∀ k < sp' + 1, dDv scr4 k = dDv scr0 k := fun k hk => by
    dsimp only [scr4, scr3, scr2, scr1, dDv]
    rw [dArr_set_ne (by omega), dArr_set_ne (by omega), dArr_set_ne (by omega),
      dArr_set_ne (by omega)]; exact (congrArg (·.getD 0#32) (hnonval (1048 + k) (by omega)))
  have hdt_lt_sp' : ∀ k < sp', (dDt scr0 k).toNat < target := fun k hk => hd.dt_mono k sp' hk hsp'
  have hdt_eq : ∀ k < sp' + 1, (dDt scr4 k).toNat = (dDt scr0 k).toNat := fun k hk => by
    dsimp only [scr4, scr3, scr2, scr1, dDt]
    rw [dArr_set_ne (by omega), dArr_set_ne (by omega)]
    by_cases hks : k = sp'
    · subst hks; rw [dArr_set_self (by simp [hlen_u, hlen0]; omega), BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : target < 2 ^ 32)]
    · rw [dArr_set_ne (by omega), dArr_set_ne (by omega)]
      unfold dArr; rw [hnonval (1120 + k) (by omega)]
  have hdph_lt : ∀ k < sp', dDph scr4 k = dDph scr0 k := fun k hk => by
    dsimp only [scr4, scr3, scr2, scr1, dDph]
    rw [dArr_set_ne (by omega), dArr_set_ne (by omega), dArr_set_ne (by omega),
      dArr_set_ne (by omega)]; exact congrArg (·.getD 0#32) (hnonval (1072 + k) (by omega))
  have hdph_sp' : dDph scr4 sp' = 1#32 := by
    dsimp only [scr4, scr3, scr2, scr1, dDph]
    rw [dArr_set_ne (by omega), dArr_set_ne (by omega), dArr_set_ne (by omega),
      dArr_set_self (by simp [hlen_u, hlen0]; omega)]
  have htrl_lt_tg : ∀ j < target, dTrl scr4 j = dTrl scr0 j := fun j hj => by
    dsimp only [scr4, scr3, scr2, scr1, dTrl]
    rw [dArr_set_ne (by omega), dArr_set_ne (by omega), dArr_set_ne (by omega),
      dArr_set_ne (by omega)]; exact congrArg (·.getD 0#32) (hnonval (1096 + j) (by omega))
  have htrl_tg : dTrl scr4 target = v := by
    dsimp only [scr4, scr3, scr2, scr1, dTrl]; rw [dArr_set_self (by simp [hlen_u, hlen0]; omega)]
  have hval4_v : dVal scr4 v.toNat = nv_w := by
    dsimp only [scr4, scr3, scr2, scr1, dVal]
    rw [dArr_set_ne (by omega), dArr_set_self (by simp [hlen_u, hlen0]; omega)]
  have hval4_ne : ∀ w < nv, w ≠ v.toNat → dVal scr4 w = dVal scr_u w := fun w hw hne => by
    dsimp only [scr4, scr3, scr2, scr1, dVal]
    rw [dArr_set_ne (by omega), dArr_set_ne (by omega), dArr_set_ne (by omega),
      dArr_set_ne (by omega)]
  have hval4_pre : ∀ j < target, dVal scr4 (dTrl scr0 j).toNat = dVal scr0 (dTrl scr0 j).toNat :=
    fun j hj => by rw [hval4_ne _ (hd.trl_lt j (by omega)) (htrl_pre j hj), hval_u_pre j hj]
  have hbp_iff : ∀ lvl ≤ sp', ∀ α, dBranchPrefix scr4 lvl α ↔ dBranchPrefix scr0 lvl α :=
    fun lvl hlvl _ => dBranchPrefix_congr (fun k hk => hdv_eq k (by omega)) fun k hk => by
      have h1 := congrArg BitVec.toNat (hd.dv_eq_trl k (by omega))
      rw [h1]; exact hval4_pre _ (hdt_lt_sp' k (by omega))
  refine ⟨htg_lt, hv_lt, {
    len_eq := by simp [scr4, scr3, scr2, scr1, hlen_u, hlen0]
    prefix_eq := fun i hi => by
      dsimp only [scr4, scr3, scr2, scr1]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), hnonval i (by omega)]
      exact hd.prefix_eq i hi
    sp_le_tn := by omega
    tn_le_nv := by omega
    val_dom := fun w hw => by
      by_cases hwv : w = v.toNat
      · subst hwv; rw [hval4_v]; exact Or.inr hnw_dom
      · rw [hval4_ne w hw hwv]
        by_cases hex : ∃ j, target ≤ j ∧ j < tn0 ∧ (dTrl scr0 j).toNat = w
        · rw [hval_uz w hw hex]; exact Or.inl rfl
        · rw [hval_up w hw fun j h1 h2 heq => hex ⟨j, h1, h2, heq⟩]; exact hd.val_dom w hw
    trl_lt := fun j hj => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · rw [htrl_lt_tg j hlt]; exact hd.trl_lt j (by omega)
      · exact htrl_tg ▸ hv_lt
    trl_nz := fun j hj => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · rw [htrl_lt_tg j hlt, hval4_pre j hlt]; exact hd.trl_nz j (by omega)
      · rw [htrl_tg, hval4_v]; rcases hnw_dom with h | h <;> rw [h] <;> decide
    trl_inj := fun j1 j2 h1 h2 heq => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h1' | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2' | rfl
      · exact hd.trl_inj j1 j2 (by omega) (by omega) (htrl_lt_tg j1 h1' ▸ htrl_lt_tg j2 h2' ▸ heq)
      · exact absurd (htrl_lt_tg j1 h1' ▸ htrl_tg ▸ heq) (htrl_pre j1 h1')
      · exact absurd (htrl_tg ▸ htrl_lt_tg j2 h2' ▸ heq).symm (htrl_pre j2 h2')
      · rfl
    val_on_trl := fun w hw hnz => by
      by_cases hwv : w = v.toNat
      · exact ⟨target, by omega, by rw [htrl_tg, hwv]⟩
      · rw [hval4_ne w hw hwv] at hnz
        by_cases hex : ∃ j, target ≤ j ∧ j < tn0 ∧ (dTrl scr0 j).toNat = w
        · exact absurd (hval_uz w hw hex) hnz
        · rw [hval_up w hw fun j h1 h2 heq => hex ⟨j, h1, h2, heq⟩] at hnz
          obtain ⟨j, hj, htr⟩ := hd.val_on_trl w hw hnz
          have hj_lt : j < target := Nat.lt_of_not_le fun hge => hex ⟨j, hge, hj, htr⟩
          exact ⟨j, by omega, by rw [htrl_lt_tg j hj_lt]; exact htr⟩
    dph_dom := fun k hk => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · exact hdph_lt k hlt ▸ hd.dph_dom k (by omega)
      · rw [hdph_sp']; exact Or.inr rfl
    dt_lt := fun k hk => by
      rw [hdt_eq k hk]; rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · have := hdt_lt_sp' k hlt; omega
      · omega
    dt_mono := fun k1 k2 h12 h2 => by
      rw [hdt_eq k1 (by omega), hdt_eq k2 h2]; exact hd.dt_mono k1 k2 h12 (by omega)
    dv_eq_trl := fun k hk => by
      rw [hdv_eq k hk, hdt_eq k hk]; rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · rw [htrl_lt_tg _ (hdt_lt_sp' k hlt)]; exact hd.dv_eq_trl k (by omega)
      · rw [htrl_tg]
    trail_sound := fun α hα lvl hlvl hbp => by
      rcases Nat.lt_or_eq_of_le hlvl with hlt | rfl
      · have hlvl_le : lvl ≤ sp' := by omega
        have hbp0 := (hbp_iff lvl hlvl_le α).mp hbp
        have hts0 := hd.trail_sound α hα lvl (by omega) hbp0
        have hne_sp0 : lvl ≠ sp0 := by omega
        have hne_sp1 : lvl ≠ sp' + 1 := by omega
        simp only [hne_sp0, hne_sp1, ↓reduceIte] at hts0 ⊢; rw [hdt_eq lvl hlt]; intro j hj
        have hj_tg : j < target := by
          rcases Nat.lt_or_eq_of_le hlvl_le with h1 | rfl
          · exact Nat.lt_trans hj (hdt_lt_sp' lvl h1)
          · exact hj
        rw [htrl_lt_tg j hj_tg, hval4_pre j hj_tg]; exact hts0 j hj
      · simp only [↓reduceIte]
        have hts0 := hd.trail_sound α hα sp' (by omega)
          ((hbp_iff sp' (Nat.le_refl _) α).mp fun k hk => hbp k (by omega))
        have hne_sp0 : sp' ≠ sp0 := by omega
        simp only [hne_sp0, ↓reduceIte] at hts0; intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
        · rw [htrl_lt_tg j hlt, hval4_pre j hlt]; exact hts0 j hlt
        · rw [htrl_tg]; have hv_sat := hbp sp' (Nat.lt_succ_self _)
          rwa [hdv_eq sp' (Nat.lt_succ_self _)] at hv_sat
    search_sound := fun α hα => by
      obtain ⟨k, hk_le, hdphk, hbpk, hneg⟩ := hsearch α hα
      rcases Nat.lt_or_eq_of_le hk_le with hk_lt | hkeq
      · refine Or.inr ⟨k, by omega, hdph_lt k hk_lt ▸ hdphk, (hbp_iff k (by omega) α).mpr hbpk, ?_⟩
        rw [hdv_eq k (by omega)]
        have h1 := congrArg BitVec.toNat (hd.dv_eq_trl k (by omega))
        rw [h1, hval4_pre _ (hdt_lt_sp' k hk_lt), ← h1]; exact hneg
      · refine Or.inl fun j hj => ?_; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | hjeq
        · exact (hbp_iff sp' (Nat.le_refl _) α).mpr (hkeq ▸ hbpk) j hlt
        · rw [hjeq, hdv_eq sp' (Nat.lt_succ_self _), hval4_v]
          exact (dValMatch_flip hv_dom).mpr (by dsimp only [v]; rw [← hkeq]; exact hneg)
  }⟩

/-- Branching on an unassigned variable `pick` with phase `0` and value `w ∈ {1, 2}`
preserves `DpllStateOk` at `(tn + 1, sp + 1)`. -/
private theorem dpll_decide_push_ok {s0 : FullState} {scr : List (BitVec 32)}
    {nv nc a0 a1 tn sp : Nat} {pick w : BitVec 32}
    (hcap : 1152 ≤ s0.scratch.scratch_buf.length) (hnv24 : nv ≤ 24)
    (hd : DpllStateOk s0 scr nv nc a0 a1 tn sp)
    (hpick : pick.toNat < nv) (hval0 : dVal scr pick.toNat = 0#32) (hw : w = 1#32 ∨ w = 2#32) :
    let scr1 := scr.set (1048 + sp) pick
    let scr2 := scr1.set (1072 + sp) 0#32
    let scr3 := scr2.set (1120 + sp) (BitVec.ofNat 32 tn)
    let scr4 := scr3.set (1024 + pick.toNat) w
    let scr5 := scr4.set (1096 + tn) pick
    tn < nv ∧ DpllStateOk s0 scr5 nv nc a0 a1 (tn + 1) (sp + 1) := by
  intro scr1 scr2 scr3 scr4 scr5
  have htn_lt : tn < nv := dpll_tn_lt_of_unassigned hd hpick hval0
  have hlen0 := hd.len_eq; have hsp_le := hd.sp_le_tn; have htn_le := hd.tn_le_nv
  have hne_trl : ∀ j < tn, (dTrl scr j).toNat ≠ pick.toNat :=
    fun j hj heq => hd.trl_nz j hj (heq ▸ hval0)
  have hdv_lt : ∀ k < sp, (dDv scr k).toNat < nv ∧ (dDv scr k).toNat ≠ pick.toNat := fun k hk => by
    have he := congrArg BitVec.toNat (hd.dv_eq_trl k hk)
    exact ⟨he ▸ hd.trl_lt _ (hd.dt_lt k hk), he ▸ hne_trl _ (hd.dt_lt k hk)⟩
  have hval5_p : dVal scr5 pick.toNat = w := by
    dsimp only [scr5, scr4, scr3, scr2, scr1, dVal]
    rw [dArr_set_ne (by omega), dArr_set_self (by simp [hlen0]; omega)]
  have hval5_ne : ∀ v < nv, v ≠ pick.toNat → dVal scr5 v = dVal scr v := fun v hv hne => by
    dsimp only [scr5, scr4, scr3, scr2, scr1, dVal]
    rw [dArr_set_ne (by omega), dArr_set_ne (by omega), dArr_set_ne (by omega),
      dArr_set_ne (by omega), dArr_set_ne (by omega)]
  have htrl5_old : ∀ j < tn, dTrl scr5 j = dTrl scr j := fun j hj => by
    dsimp only [scr5, scr4, scr3, scr2, scr1, dTrl]
    rw [dArr_set_ne (by omega), dArr_set_ne (by omega), dArr_set_ne (by omega),
      dArr_set_ne (by omega), dArr_set_ne (by omega)]
  have htrl5_tn : dTrl scr5 tn = pick := by
    dsimp only [scr5, scr4, scr3, scr2, scr1, dTrl]; rw [dArr_set_self (by simp [hlen0]; omega)]
  have hdv5_old : ∀ k < sp, dDv scr5 k = dDv scr k := fun k hk => by
    dsimp only [scr5, scr4, scr3, scr2, scr1, dDv]
    rw [dArr_set_ne (by omega), dArr_set_ne (by omega), dArr_set_ne (by omega),
      dArr_set_ne (by omega), dArr_set_ne (by omega)]
  have hdv5_sp : dDv scr5 sp = pick := by
    dsimp only [scr5, scr4, scr3, scr2, scr1, dDv]
    rw [dArr_set_ne (by omega), dArr_set_ne (by omega), dArr_set_ne (by omega),
      dArr_set_ne (by omega), dArr_set_self (by simp [hlen0]; omega)]
  have hdph5_old : ∀ k < sp, dDph scr5 k = dDph scr k := fun k hk => by
    dsimp only [scr5, scr4, scr3, scr2, scr1, dDph]
    rw [dArr_set_ne (by omega), dArr_set_ne (by omega), dArr_set_ne (by omega),
      dArr_set_ne (by omega), dArr_set_ne (by omega)]
  have hdph5_sp : dDph scr5 sp = 0#32 := by
    dsimp only [scr5, scr4, scr3, scr2, scr1, dDph]
    rw [dArr_set_ne (by omega), dArr_set_ne (by omega), dArr_set_ne (by omega),
      dArr_set_self (by simp [hlen0]; omega)]
  have hdt5_old : ∀ k < sp, dDt scr5 k = dDt scr k := fun k hk => by
    dsimp only [scr5, scr4, scr3, scr2, scr1, dDt]
    rw [dArr_set_ne (by omega), dArr_set_ne (by omega), dArr_set_ne (by omega),
      dArr_set_ne (by omega), dArr_set_ne (by omega)]
  have hdt5_sp : (dDt scr5 sp).toNat = tn := by
    dsimp only [scr5, scr4, scr3, scr2, scr1, dDt]
    rw [dArr_set_ne (by omega), dArr_set_ne (by omega), dArr_set_self (by simp [hlen0]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : tn < 2 ^ 32)]
  have hbp_iff : ∀ lvl ≤ sp, ∀ α, dBranchPrefix scr5 lvl α ↔ dBranchPrefix scr lvl α :=
    fun lvl hlvl _ => dBranchPrefix_congr (fun k hk => hdv5_old k (by omega))
      (fun k hk => hval5_ne _ (hdv_lt k (by omega)).1 (hdv_lt k (by omega)).2)
  refine ⟨htn_lt, {
    len_eq := by simp [scr5, scr4, scr3, scr2, scr1, hlen0]
    prefix_eq := fun i hi => by
      dsimp only [scr5, scr4, scr3, scr2, scr1]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega)]; exact hd.prefix_eq i hi
    sp_le_tn := by omega
    tn_le_nv := by omega
    val_dom := fun v hv => by
      by_cases hvp : v = pick.toNat
      · subst hvp; rw [hval5_p]; exact Or.inr hw
      · rw [hval5_ne v hv hvp]; exact hd.val_dom v hv
    trl_lt := fun j hj => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · exact htrl5_old j hlt ▸ hd.trl_lt j hlt
      · exact htrl5_tn ▸ hpick
    trl_nz := fun j hj => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · rw [htrl5_old j hlt, hval5_ne _ (hd.trl_lt j hlt) (hne_trl j hlt)]; exact hd.trl_nz j hlt
      · rw [htrl5_tn, hval5_p]; rcases hw with rfl | rfl <;> decide
    trl_inj := fun j1 j2 h1 h2 heq => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h1' | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2' | rfl
      · exact hd.trl_inj j1 j2 h1' h2' (htrl5_old j1 h1' ▸ htrl5_old j2 h2' ▸ heq)
      · exact absurd (htrl5_old j1 h1' ▸ htrl5_tn ▸ heq) (hne_trl j1 h1')
      · exact absurd (htrl5_tn ▸ htrl5_old j2 h2' ▸ heq).symm (hne_trl j2 h2')
      · rfl
    val_on_trl := fun v hv hnz => by
      by_cases hvp : v = pick.toNat
      · exact ⟨tn, by omega, by rw [htrl5_tn, hvp]⟩
      · rw [hval5_ne v hv hvp] at hnz; obtain ⟨j, hj, htr⟩ := hd.val_on_trl v hv hnz
        exact ⟨j, by omega, by rw [htrl5_old j hj]; exact htr⟩
    dph_dom := fun k hk => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · exact hdph5_old k hlt ▸ hd.dph_dom k hlt
      · rw [hdph5_sp]; exact Or.inl rfl
    dt_lt := fun k hk => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · rw [hdt5_old k hlt]; have := hd.dt_lt k hlt; omega
      · rw [hdt5_sp]; omega
    dt_mono := fun k1 k2 h12 h2 => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2' | rfl
      · rw [hdt5_old k1 (by omega), hdt5_old k2 h2']; exact hd.dt_mono k1 k2 h12 h2'
      · rw [hdt5_old k1 h12, hdt5_sp]; exact hd.dt_lt k1 h12
    dv_eq_trl := fun k hk => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · rw [hdv5_old k hlt, hdt5_old k hlt, htrl5_old _ (hd.dt_lt k hlt)]; exact hd.dv_eq_trl k hlt
      · rw [hdv5_sp, hdt5_sp, htrl5_tn]
    trail_sound := fun α hα lvl hlvl hbp => by
      rcases Nat.lt_or_eq_of_le hlvl with hlt | rfl
      · have hlvl_le : lvl ≤ sp := by omega
        have hts0 := hd.trail_sound α hα lvl hlvl_le ((hbp_iff lvl hlvl_le α).mp hbp)
        have hne1 : lvl ≠ sp + 1 := by omega
        simp only [hne1, ↓reduceIte]
        rcases Nat.lt_or_eq_of_le hlvl_le with h1 | rfl
        · have hne0 : lvl ≠ sp := by omega
          simp only [hne0, ↓reduceIte] at hts0; rw [hdt5_old lvl h1]; intro j hj
          have hj_tn := Nat.lt_trans hj (hd.dt_lt lvl h1)
          rw [htrl5_old j hj_tn, hval5_ne _ (hd.trl_lt j hj_tn) (hne_trl j hj_tn)]; exact hts0 j hj
        · simp only [↓reduceIte] at hts0; rw [hdt5_sp]; intro j hj
          rw [htrl5_old j hj, hval5_ne _ (hd.trl_lt j hj) (hne_trl j hj)]; exact hts0 j hj
      · simp only [↓reduceIte]
        have hts0 := hd.trail_sound α hα sp (Nat.le_refl _)
          ((hbp_iff sp (Nat.le_refl _) α).mp fun k hk => hbp k (by omega))
        simp only [↓reduceIte] at hts0; intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
        · rw [htrl5_old j hlt, hval5_ne _ (hd.trl_lt j hlt) (hne_trl j hlt)]; exact hts0 j hlt
        · rw [htrl5_tn]; have hp_sat := hbp sp (Nat.lt_succ_self _); rwa [hdv5_sp] at hp_sat
    search_sound := fun α hα => by
      rcases hd.search_sound α hα with hbp | ⟨k, hk, hdph0, hbpk, hneg⟩
      · by_cases hm : dValMatch pick.toNat w α
        · refine Or.inl fun k hk => ?_; rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
          · exact (hbp_iff sp (Nat.le_refl _) α).mpr hbp k hlt
          · rw [hdv5_sp, hval5_p]; exact hm
        · refine Or.inr ⟨sp, Nat.lt_succ_self _, hdph5_sp,
            (hbp_iff sp (Nat.le_refl _) α).mpr hbp, by rw [hdv5_sp, hval5_p]; exact hm⟩
      · refine Or.inr ⟨k, by omega, hdph5_old k hk ▸ hdph0, (hbp_iff k (by omega) α).mpr hbpk, ?_⟩
        rw [hdv5_old k hk, hval5_ne _ (hdv_lt k hk).1 (hdv_lt k hk).2]; exact hneg
  }⟩

/-! ## 2. `full_sweep_dpll_wp` (`Full.lean` #13) -/

private theorem bv32_shr1_toNat' (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
private theorem bv32_add1_nat {a : BitVec 32} (h : a.toNat + 1 < 2 ^ 32) :
    (a + 1#32).toNat = a.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]
private theorem bv32_add64_nat {a : BitVec 32} (h : 64 + a.toNat < 2 ^ 32) :
    (64#32 + a).toNat = 64 + a.toNat := by
  rw [BitVec.toNat_add, show (64#32).toNat = 64 from rfl, Nat.mod_eq_of_lt h]
private theorem bv32_sub1_nat {a : BitVec 32} (h : 0 < a.toNat) : (a - 1#32).toNat = a.toNat - 1 :=
  by bv_omega

private theorem dpll_rng_val_dom (r : BitVec 64) :
    (r &&& 1#64).setWidth 32 + 1#32 = 1#32 ∨ (r &&& 1#64).setWidth 32 + 1#32 = 2#32 := by
  have ha : (r &&& 1#64).toNat = r.toNat % 2 := by
    rw [BitVec.toNat_and, show (1#64).toNat = 1 from rfl]
    simp [Nat.and_two_pow_sub_one_eq_mod r.toNat 1]
  rcases Nat.mod_two_eq_zero_or_one r.toNat with h0 | h1
  · left; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_setWidth, ha, h0]; decide
  · right; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_setWidth, ha, h1]; decide

theorem full_sweep_dpll_wp (Γ : Env)
    (hRng : ∀ args m Q X, fullRngNextSpec args m Q X →
      Γ "full_rng_next" [i64] [i64] args m Q X) :
    ∀ args m Q X, fullSweepDpllSpec args m Q X → Func.wp Γ full_sweep_dpll_body args m Q X := by
  rintro ⟨h, nv, nc, a0, a1, ⟨⟩⟩ m Q X ⟨c, F_cur, s, R, rfl, hlen, hcap, hcone, hm, hQ⟩
  have hscr_len0 := hlen.scratch_ok.scratch_buf_len
  have hnv24 : nv.toNat ≤ 24 := hcone.1; have hnc64 : nc.toNat ≤ 64 := hcone.2.2.1
  have hbuf : SweepBufClausesOk s nv.toNat nc.toNat := fullSweepConeOk_to_buf hlen hcap hcone
  have hret : ∀ (r fuel' rng' : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
      scr'.length = s.scratch.scratch_buf.length →
      (∀ i < 1024, scr'[i]? = s.scratch.scratch_buf[i]?) →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → ∀ α, ¬ DpllSubprobSat s nv.toNat nc.toNat a0.toNat a1.toNat α) →
      (FullMem c { s with
        core := { s.core with fuel := fuel' }
        scratch := { s.scratch with scratch_buf := scr', rng_state := rng' } } ⋆ R) m' →
        Q (r, ()) m' :=
    fun r fuel' rng' scr' m' hsl hpre hfl hrc hnu hm' => hQ r fuel' scr' rng' m'
      ⟨{ hlen.core_ok with cur_vars_le := hlen.core_ok.cur_vars_le },
       { hlen.scratch_ok with scratch_buf_len := hsl.trans hscr_len0 }⟩ hfl hpre
      (fullSweepConeOk_of_prefix hcone rfl rfl rfl hpre) hrc
      (fun hr => fullSweepDpllUnsat_of_not_subprob hlen hcap hcone (hnu hr)) hm'
  unfold Func.wp full_sweep_dpll_body; dsimp only; sw_fast
  rw [show (BitVec.signExtend 64 (1024 : BitVec 32)) * (4 : BitVec 64) = 4096#64 from rfl,
    show (BitVec.signExtend 64 (1048 : BitVec 32)) * (4 : BitVec 64) = 4192#64 from rfl,
    show (BitVec.signExtend 64 (1072 : BitVec 32)) * (4 : BitVec 64) = 4288#64 from rfl,
    show (BitVec.signExtend 64 (1096 : BitVec 32)) * (4 : BitVec 64) = 4384#64 from rfl,
    show (BitVec.signExtend 64 (1120 : BitVec 32)) * (4 : BitVec 64) = 4480#64 from rfl]
  refine wp_loop_inv (ts := [i32]) (fun (i, ()) m1 => i.toNat ≤ nv.toNat ∧
      ∃ scr : List (BitVec 32), scr.length = s.scratch.scratch_buf.length ∧
      (∀ idx < 1024, scr[idx]? = s.scratch.scratch_buf[idx]?) ∧ (∀ v < i.toNat, dVal scr v = 0#32) ∧
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr } } ⋆ R) m1)
    (fun (i, ()) _ => nv.toNat - i.toNat) ?_ ?_
  · intro J_z hJ_z; sw_fast; exact hJ_z (0#32, ()) m
      ⟨Nat.zero_le _, s.scratch.scratch_buf, rfl, fun _ _ => rfl, fun _ hv => by simp at hv, hm⟩
  · intro J_z; rintro ⟨i, ⟨⟩⟩ m1 ⟨hi_le, scr, hsl, hpre, hval0, hm1⟩ hJ_z; sw_split
    · have hi_lt : i.toNat < nv.toNat := by sw_bd
      generalize hst_eq : ({ s with scratch := { s.scratch with scratch_buf := scr } } : FullState)
        = st at hm1
      have hlen_st : st.scratch.scratch_buf.length = c.scratch_cap := by
        rw [← hst_eq]; dsimp only; omega
      sw_fast; have hi1 : (i + 1#32).toNat = i.toNat + 1 := bv32_add1_nat (by omega); subst hst_eq
      have hm1' : (FullMem c { s with scratch :=
          { s.scratch with scratch_buf := scr.set (1024 + i.toNat) 0#32 } } ⋆ R) m := by
        simpa only [bv32_zext64_eq, BitVec.toNat_ofNat, show (0 : BitVec 32) = 0#32 from rfl,
          Nat.mod_eq_of_lt (by have := i.isLt; omega : i.toNat < 2 ^ 64)] using hm
      refine hJ_z (i + 1#32, ()) m (by dsimp only; omega)
        ⟨by omega, scr.set (1024 + i.toNat) 0#32, by simp [hsl],
          fun idx hidx => by rw [List.getElem?_set_ne (by omega)]; exact hpre idx hidx,
          fun v hv => ?_, hm1'⟩
      rw [hi1] at hv; dsimp only [dVal]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hlt | rfl
      · rw [dArr_set_ne (by omega)]; exact hval0 v hlt
      · exact dArr_set_self (by omega)
    have hi_eq : i.toNat = nv.toNat := by sw_bd
    clear hJ_z hi_le hc
    have hd0 : DpllStateOk s scr nv.toNat nc.toNat a0.toNat a1.toNat 0 0 :=
      dpll_state_zero_ok hsl hpre (hi_eq ▸ hval0)
    sw_fast
    refine wp_join_group (ts := [i32])
      (fun (tn0, ()) m_a0 => ∃ scr0 : List (BitVec 32),
        DpllStateOk s scr0 nv.toNat nc.toNat a0.toNat a1.toNat tn0.toNat 0 ∧
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr0 } } ⋆ R) m_a0) ?_ ?_
    · rintro _ ⟨tn0, ⟨⟩⟩ m_a0 ⟨scr0, hd_a0, hm_a0⟩; clear hm1 hval0 hpre hsl hi_eq; sw_fast
      refine wp_join_group (ts := [i32])
        (fun (tn1, ()) m_a1 => ∃ scr1 : List (BitVec 32),
          DpllStateOk s scr1 nv.toNat nc.toNat a0.toNat a1.toNat tn1.toNat 0 ∧
          (FullMem c { s with scratch := { s.scratch with scratch_buf := scr1 } } ⋆ R) m_a1) ?_ ?_
      · rintro _ ⟨tn1, ⟨⟩⟩ m_a1 ⟨scr1, hd_a1, hm_a1⟩; clear hd_a0 hm_a0; sw_fast
        refine wp_loop_inv (ts := [i32, i32, i64])
          (fun (tn, sp, budget, ()) mb =>
            ∃ (scr_b : List (BitVec 32)) (fuel_b rng_b : BitVec 64),
              fuel_b.toNat ≤ s.core.fuel.toNat ∧
              DpllStateOk s scr_b nv.toNat nc.toNat a0.toNat a1.toNat tn.toNat sp.toNat ∧
              (FullMem c { s with
                core := { s.core with fuel := fuel_b }
                scratch := { s.scratch with scratch_buf := scr_b, rng_state := rng_b } } ⋆ R) mb)
          (fun (_, _, budget, ()) _ => budget.toNat) ?_ ?_
        · intro J_b hJ_b; sw_fast; exact hJ_b (tn1, 0#32, 256#64, ()) m_a1
            ⟨scr1, s.core.fuel, s.scratch.rng_state, Nat.le_refl _, hd_a1, hm_a1⟩
        · intro J_b; rintro ⟨tn, sp, budget, ⟨⟩⟩ mb ⟨scr_b, fuel_b, rng_b, hfl_b, hd_b, hmb⟩ hJ_b
          clear hd_a1 hm_a1; sw_split; rotate_left
          · sw_fast; exact hret 0#64 fuel_b rng_b scr_b mb hd_b.len_eq hd_b.prefix_eq hfl_b
              (Or.inl rfl) (fun h => absurd h (by decide)) hmb
          have hbud_pos : 0 < budget.toNat := by sw_bd
          have hbud1 : (budget - 1#64).toNat = budget.toNat - 1 := by
            rw [BitVec.toNat_sub, show (1#64).toNat = 1 from rfl]; omega
          generalize hstb_eq : ({ s with
            core := { s.core with fuel := fuel_b }
            scratch := { s.scratch with scratch_buf := scr_b, rng_state := rng_b } } : FullState)
            = st_b at hmb
          have hfuel_eq : st_b.core.fuel = fuel_b := by rw [← hstb_eq]
          sw_fast; sw_split
          · sw_fast; subst hstb_eq; exact hret 0#64 fuel_b rng_b scr_b mb hd_b.len_eq
              hd_b.prefix_eq hfl_b (Or.inl rfl) (fun h => absurd h (by decide)) hmb
          have hfl_pos : 0 < fuel_b.toNat := by rw [hfuel_eq] at hc; bv_omega
          have hfl_dec : (fuel_b - 1#64).toNat ≤ s.core.fuel.toNat := by
            have hsub : (fuel_b - 1#64).toNat = fuel_b.toNat - 1 := by bv_omega
            omega
          sw_fast; subst hstb_eq; let fuel_1 : BitVec 64 := fuel_b - 1#64
          refine wp_loop_inv (ts := [i32, .bool, .bool])
            (fun (tn_p, confl, chg, ()) mp =>
              ∃ scr_p : List (BitVec 32),
                DpllStateOk s scr_p nv.toNat nc.toNat a0.toNat a1.toNat tn_p.toNat sp.toNat ∧
                (confl = true → ∀ α, DpllSubprobSat s nv.toNat nc.toNat a0.toNat a1.toNat α →
                  ¬ dBranchPrefix scr_p sp.toNat α) ∧
                (FullMem c { s with
                  core := { s.core with fuel := fuel_1 }
                  scratch := { s.scratch with scratch_buf := scr_p, rng_state := rng_b } } ⋆ R) mp)
            (fun (tn_p, confl, chg, ()) _ =>
              (nv.toNat - tn_p.toNat) * 2 + (if chg && !confl then 1 else 0)) ?_ ?_
          · intro J_p hJ_p; sw_fast
            exact hJ_p (tn, false, true, ()) m ⟨scr_b, hd_b, fun h => Bool.noConfusion h, hm⟩
          · intro J_p; rintro ⟨tn_p, confl, chg, ⟨⟩⟩ mp ⟨scr_p, hd_p, hcf_p, hmp⟩ hJ_p
            clear hd_b; sw_fast
            refine wp_join_group (ts := [])
              (fun () m_pe => m_pe = mp ∧ (chg = false ∨ confl = true)) ?_ ?_
            · rintro _ ⟨⟩ m_pe ⟨hmpe, _⟩; subst m_pe; clear hJ_p; sw_split
              · have hcf_t : confl = true := by sw_bd
                have hnot_bp := hcf_p hcf_t
                have hsearch0 : ∀ α, DpllSubprobSat s nv.toNat nc.toNat a0.toNat a1.toNat α →
                    ∃ k < sp.toNat, dDph scr_p k = 0#32 ∧ dBranchPrefix scr_p k α ∧
                      ¬ dValMatch (dDv scr_p k).toNat (dVal scr_p (dDv scr_p k).toNat) α :=
                  fun α hα => (hd_p.search_sound α hα).elim (fun h => absurd h (hnot_bp α hα)) id
                have hsp_le_nv : sp.toNat ≤ nv.toNat := Nat.le_trans hd_p.sp_le_tn hd_p.tn_le_nv
                sw_fast
                refine wp_loop_inv (ts := [i32])
                  (fun (sp_s, ()) ms => ms = mp ∧ sp_s.toNat ≤ sp.toNat ∧
                    ∀ α, DpllSubprobSat s nv.toNat nc.toNat a0.toNat a1.toNat α →
                      ∃ k < sp_s.toNat, dDph scr_p k = 0#32 ∧ dBranchPrefix scr_p k α ∧
                        ¬ dValMatch (dDv scr_p k).toNat (dVal scr_p (dDv scr_p k).toNat) α)
                  (fun (sp_s, ()) _ => sp_s.toNat) ?_ ?_
                · intro J_sp hJ_sp; sw_fast
                  exact hJ_sp (sp, ()) mp ⟨rfl, Nat.le_refl _, hsearch0⟩
                · intro J_sp; rintro ⟨sp_s, ⟨⟩⟩ ms ⟨hms, hsps_le, hs_inv⟩ hJ_sp; subst ms
                  sw_fast
                  refine wp_join_group (ts := [])
                    (fun () m_s => m_s = mp ∧ (sp_s.toNat = 0 ∨
                      (0 < sp_s.toNat ∧ dDph scr_p (sp_s.toNat - 1) = 0#32))) ?_ ?_
                  · rintro _ ⟨⟩ m_s ⟨hms', hsp_done⟩; subst m_s; clear hJ_sp
                    sw_split
                    · have hsp0 : sp_s.toNat = 0 := by bv_omega
                      sw_fast
                      refine hret 20#64 fuel_1 rng_b scr_p mp hd_p.len_eq hd_p.prefix_eq hfl_dec
                        (Or.inr (Or.inr rfl)) (fun _ α hα => ?_) hmp
                      obtain ⟨k, hk, _⟩ := hs_inv α hα; omega
                    have hsp_pos : 0 < sp_s.toNat := by bv_omega
                    have hdph_top : dDph scr_p (sp_s.toNat - 1) = 0#32 :=
                      hsp_done.elim (fun h => by omega) (·.2)
                    have hsp_sub : (sp_s - 1#32).toNat = sp_s.toNat - 1 := bv32_sub1_nat hsp_pos
                    let sp' : BitVec 32 := sp_s - 1#32
                    have hsp'_lt : sp'.toNat < sp.toNat := by dsimp only [sp']; omega
                    generalize hstp_eq : ({ s with
                      core := { s.core with fuel := fuel_1 }
                      scratch := { s.scratch with scratch_buf := scr_p, rng_state := rng_b } }
                      : FullState) = st_p at hmp
                    have hscrp_eq : st_p.scratch.scratch_buf = scr_p := by rw [← hstp_eq]
                    have hlen_stp : st_p.scratch.scratch_buf.length = c.scratch_cap := by
                      rw [hscrp_eq, hd_p.len_eq, hscr_len0]
                    have hsp'_z : (sp'.setWidth 64).toNat = sp'.toNat := by
                      dsimp only [sp']; simp only [bv_c0]
                    have hdt_sp'_lt : (dDt scr_p sp'.toNat).toNat < tn_p.toNat :=
                      hd_p.dt_lt sp'.toNat hsp'_lt
                    have hv_load : st_p.scratch.scratch_buf[1048 + (sp'.setWidth 64).toNat]'(by
                        rw [hsp'_z]; omega) = dDv scr_p sp'.toNat := by
                      have hl : 1048 + sp'.toNat < scr_p.length := by have := hd_p.len_eq; omega
                      simp only [hscrp_eq, hsp'_z]; unfold dDv dArr
                      rw [List.getElem?_eq_getElem hl, Option.getD_some]
                    have hv_lt' : (dDv scr_p sp'.toNat).toNat < nv.toNat := by
                      rw [congrArg BitVec.toNat (hd_p.dv_eq_trl sp'.toNat hsp'_lt)]
                      exact hd_p.trl_lt _ hdt_sp'_lt
                    have hz_dv : ((st_p.scratch.scratch_buf[1048 + (sp'.setWidth 64).toNat]'(by
                        rw [hsp'_z]; omega)).setWidth 64).toNat = (dDv scr_p sp'.toNat).toNat := by
                      rw [hv_load]; simp only [bv_c0]
                    have hvw_load : st_p.scratch.scratch_buf[1024 +
                        ((st_p.scratch.scratch_buf[1048 + (sp'.setWidth 64).toNat]'(by
                          rw [hsp'_z]; omega)).setWidth 64).toNat]'(by rw [hz_dv]; omega) =
                        dVal scr_p (dDv scr_p sp'.toNat).toNat := by
                      have hl : 1024 + (dDv scr_p sp'.toNat).toNat < scr_p.length := by
                        have := hd_p.len_eq; omega
                      simp only [hz_dv]; simp only [hscrp_eq]; unfold dVal dArr
                      rw [List.getElem?_eq_getElem hl, Option.getD_some]
                    sw_fast
                    refine wp_load_of (FullSweepFwdTactics.load_full_scr_val (by
                      change 1024 + ((st_p.scratch.scratch_buf[1048 + (sp'.setWidth 64).toNat]'_
                        ).setWidth 64).toNat < _; rw [hz_dv]; omega) hmp) ?_
                    sw_fast; subst hstp_eq
                    -- Unwind trail: `while (tn > dt[sp']) { tn--; val[trl[tn]] = 0; }`
                    refine wp_loop_inv (ts := [i32])
                      (fun (tn_u, ()) mu => (dDt scr_p sp'.toNat).toNat ≤ tn_u.toNat ∧
                        tn_u.toNat ≤ tn_p.toNat ∧ ∃ scr_u : List (BitVec 32),
                          scr_u.length = scr_p.length ∧
                          (∀ idx, ¬ (1024 ≤ idx ∧ idx < 1048) → scr_u[idx]? = scr_p[idx]?) ∧
                          (∀ v < nv.toNat, (∃ j, tn_u.toNat ≤ j ∧ j < tn_p.toNat ∧
                            (dTrl scr_p j).toNat = v) → dVal scr_u v = 0#32) ∧
                          (∀ v < nv.toNat, (∀ j, tn_u.toNat ≤ j → j < tn_p.toNat →
                            (dTrl scr_p j).toNat ≠ v) → dVal scr_u v = dVal scr_p v) ∧
                          (FullMem c { s with
                            core := { s.core with fuel := fuel_1 }
                            scratch := { s.scratch with
                              scratch_buf := scr_u, rng_state := rng_b } } ⋆ R) mu)
                      (fun (tn_u, ()) _ => tn_u.toNat) ?_ ?_
                    · intro J_u hJ_u; sw_fast
                      exact hJ_u (tn_p, ()) mp ⟨Nat.le_of_lt hdt_sp'_lt, Nat.le_refl _, scr_p, rfl,
                        fun _ _ => rfl, fun _ _ ⟨j, h1, h2, _⟩ => by omega, fun _ _ _ => rfl, hmp⟩
                    · intro J_u; rintro ⟨tn_u, ⟨⟩⟩ mu
                        ⟨htnu_lo, htnu_hi, scr_u, hsl_u, hnv_u, hval_uz, hval_up, hmu⟩ hJ_u
                      generalize hstu_eq : ({ s with
                        core := { s.core with fuel := fuel_1 }
                        scratch := { s.scratch with scratch_buf := scr_u, rng_state := rng_b } }
                        : FullState) = st_u at hmu
                      have hscru_eq : st_u.scratch.scratch_buf = scr_u := by rw [← hstu_eq]
                      have hlen_stu : st_u.scratch.scratch_buf.length = c.scratch_cap := by
                        rw [hscru_eq, hsl_u, hd_p.len_eq, hscr_len0]
                      have hdt_u : st_u.scratch.scratch_buf[1120 + sp'.toNat]'(by omega) =
                          dDt scr_p sp'.toNat := by
                        have hl : 1120 + sp'.toNat < scr_u.length := by
                          rw [hsl_u, hd_p.len_eq]; omega
                        simp only [hscru_eq]; unfold dDt dArr
                        rw [← hnv_u (1120 + sp'.toNat) (by omega),
                          List.getElem?_eq_getElem hl, Option.getD_some]
                      have htnp_le := hd_p.tn_le_nv
                      have hidx_u : (2 ^ 32 - (1 : BitVec 32).toNat + sp_s.toNat) % 2 ^ 32 =
                          sp'.toNat := by dsimp only [sp']; bv_omega
                      sw_fast; sw_split
                      · have htnu_gt : (dDt scr_p sp'.toNat).toNat < tn_u.toNat := by
                          (try simp only [bv_c0, hidx_u] at hc); rw [hdt_u] at hc; sw_bd
                        have htnu_sub : (tn_u - 1#32).toNat = tn_u.toNat - 1 :=
                          bv32_sub1_nat (by omega)
                        have htrl_u_eq : st_u.scratch.scratch_buf[1096 + (tn_u - 1#32).toNat]'(by
                            rw [htnu_sub]; omega) = dTrl scr_p (tn_u.toNat - 1) := by
                          have hl : 1096 + (tn_u.toNat - 1) < scr_u.length := by
                            rw [hsl_u, hd_p.len_eq]; omega
                          simp only [hscru_eq, htnu_sub]; unfold dTrl dArr
                          rw [← hnv_u (1096 + (tn_u.toNat - 1)) (by omega),
                            List.getElem?_eq_getElem hl, Option.getD_some]
                        have hu_pop_lt : (dTrl scr_p (tn_u.toNat - 1)).toNat < nv.toNat :=
                          hd_p.trl_lt (tn_u.toNat - 1) (by omega)
                        have hz_u : ((st_u.scratch.scratch_buf[1096 +
                            ((tn_u - 1#32).setWidth 64).toNat]'(by
                              simp only [bv_c0]; omega)).setWidth 64).toNat =
                            (dTrl scr_p (tn_u.toNat - 1)).toNat := by
                          have h1 : ((tn_u - 1#32).setWidth 64).toNat = (tn_u - 1#32).toNat := by
                            simp only [bv_c0]
                          simp only [h1]; rw [htrl_u_eq]; simp only [bv_c0]
                        sw_fast; subst hstu_eq
                        let u_pop := (dTrl scr_p (tn_u.toNat - 1)).toNat
                        have hm_u' : (FullMem c { s with
                          core := { s.core with fuel := fuel_1 }
                          scratch := { s.scratch with
                            scratch_buf := scr_u.set (1024 + u_pop) 0#32
                            rng_state := rng_b } } ⋆ R) m := by
                          simpa only [show (1 : BitVec 32) = 1#32 from rfl, hz_u,
                            show (0 : BitVec 32) = 0#32 from rfl] using hm
                        refine hJ_u (tn_u - 1#32, ()) m (by dsimp only; omega)
                          ⟨by omega, by omega, scr_u.set (1024 + u_pop) 0#32, by simp [hsl_u],
                            fun idx hidx => by
                              rw [List.getElem?_set_ne (by omega)]; exact hnv_u _ hidx,
                            fun v hv ⟨j, h1, h2, h3⟩ => ?_, fun v hv hall => ?_, hm_u'⟩
                        · dsimp only [dVal]; by_cases hvu : v = u_pop
                          · subst hvu; rw [dArr_set_self (by have := hd_p.len_eq; omega)]
                          · rw [dArr_set_ne (by omega)]
                            have hj_ne : j ≠ tn_u.toNat - 1 := fun h => hvu (h ▸ h3).symm
                            exact hval_uz v hv ⟨j, by omega, h2, h3⟩
                        · dsimp only [dVal]; have hvu : v ≠ u_pop :=
                            fun h => hall (tn_u.toNat - 1) (by omega) (by omega) h.symm
                          rw [dArr_set_ne (by omega)]
                          exact hval_up v hv fun j h1 h2 => hall j (by omega) h2
                      clear hJ_u
                      have htnu_eq : tn_u.toNat = (dDt scr_p sp'.toNat).toNat := by
                        (try simp only [bv_c0, hidx_u] at hc); rw [hdt_u] at hc; sw_bd
                      have hsearch' : ∀ α, DpllSubprobSat s nv.toNat nc.toNat a0.toNat a1.toNat α →
                          ∃ k ≤ sp'.toNat, dDph scr_p k = 0#32 ∧ dBranchPrefix scr_p k α ∧
                            ¬ dValMatch (dDv scr_p k).toNat (dVal scr_p (dDv scr_p k).toNat) α :=
                        fun α hα => by
                          obtain ⟨k, hk, h1, h2, h3⟩ := hs_inv α hα
                          exact ⟨k, by dsimp only [sp']; omega, h1, h2, h3⟩
                      obtain ⟨htg_lt, hv_lt, hd_next⟩ :=
                        dpll_backtrack_flip_ok (by omega) hnv24 hd_p hsp'_lt (hsp_sub ▸ hdph_top)
                          hsearch' hsl_u hnv_u (htnu_eq ▸ hval_uz) (htnu_eq ▸ hval_up)
                      have htnu_z : (tn_u.setWidth 64).toNat = (dDt scr_p sp'.toNat).toNat := by
                        rw [← htnu_eq]; simp only [bv_c0]
                      have htnu_ofNat : tn_u = BitVec.ofNat 32 (dDt scr_p sp'.toNat).toNat := by
                        rw [← htnu_eq, bv_ofNat_toNat_eq]
                      have htnu1 : (tn_u + 1#32).toNat = (dDt scr_p sp'.toNat).toNat + 1 := by
                        rw [bv32_add1_nat (by omega), htnu_eq]
                      have hsp'1 : (sp' + 1#32).toNat = sp'.toNat + 1 := by
                        have := hd_p.sp_le_tn; exact bv32_add1_nat (by omega)
                      sw_fast
                      refine wp_store_sep (FullSweepFwdTactics.store_full_scr_val _ (by
                        change 1024 + _ < _; simp only [List.length_set, hlen_stu]
                        dsimp only [sp'] at hv_lt' hz_dv ⊢
                        simp only [show (1 : BitVec 32) = 1#32 from rfl]; rw [hz_dv]; omega) hm)
                        fun m hm => ?_
                      sw_fast; subst hstu_eq
                      have hm_next : (FullMem c { s with
                        core := { s.core with fuel := fuel_1 }
                        scratch := { s.scratch with
                          scratch_buf := (((scr_u.set (1072 + sp'.toNat) 1#32).set
                            (1120 + sp'.toNat) (BitVec.ofNat 32 (dDt scr_p sp'.toNat).toNat)).set
                            (1024 + (dDv scr_p sp'.toNat).toNat)
                            (3#32 - dVal scr_p (dDv scr_p sp'.toNat).toNat)).set
                            (1096 + (dDt scr_p sp'.toNat).toNat) (dDv scr_p sp'.toNat)
                          rng_state := rng_b } } ⋆ R) m := by
                        dsimp only [sp'] at hsp'_z htnu_z htnu_ofNat hv_load hvw_load hz_dv ⊢
                        simp only [show (1 : BitVec 32) = 1#32 from rfl,
                          show (3 : BitVec 32) = 3#32 from rfl] at hm
                        rw [htnu_z, htnu_ofNat, hvw_load, hz_dv, hv_load, hsp'_z] at hm; exact hm
                      exact hJ_b (tn_u + 1#32, sp' + 1#32, budget - 1#64, ()) m
                        (by dsimp only; omega)
                        ⟨_, fuel_1, rng_b, hfl_dec, by rw [htnu1, hsp'1]; exact hd_next, hm_next⟩
                  intro J_se hJ_se
                  sw_split; rotate_left
                  · sw_fast; exact hJ_se () mp ⟨rfl, Or.inl (by sw_bd)⟩
                  have hsps_pos : 0 < sp_s.toNat := by sw_bd
                  have hsp_m1 : (sp_s - 1#32).toNat = sp_s.toNat - 1 := bv32_sub1_nat hsps_pos
                  generalize hst_eq : ({ s with
                    core := { s.core with fuel := fuel_1 }
                    scratch := { s.scratch with scratch_buf := scr_p, rng_state := rng_b } }
                    : FullState) = st_s at hmp
                  have hscrs_eq : st_s.scratch.scratch_buf = scr_p := by rw [← hst_eq]
                  have hlen_sts : st_s.scratch.scratch_buf.length = c.scratch_cap := by
                    rw [hscrs_eq, hd_p.len_eq, hscr_len0]
                  have hdph_s : st_s.scratch.scratch_buf[1072 + (sp_s - 1#32).toNat]'(by
                      have := hd_p.sp_le_tn; have := hd_p.tn_le_nv; rw [hsp_m1]; omega) =
                      dDph scr_p (sp_s.toNat - 1) := by
                    have hl : 1072 + (sp_s.toNat - 1) < scr_p.length := by
                      have := hd_p.len_eq; omega
                    simp only [hscrs_eq, hsp_m1]; unfold dDph dArr
                    rw [List.getElem?_eq_getElem hl, Option.getD_some]
                  have hidx_s : (2 ^ 32 - (1 : BitVec 32).toNat + sp_s.toNat) % 2 ^ 32 =
                      (sp_s - 1#32).toNat := by bv_omega
                  sw_fast; sw_split
                  · have hdph_nz : dDph scr_p (sp_s.toNat - 1) ≠ 0#32 := by
                      (try simp only [hidx_s] at hc)
                      rw [hdph_s, show (0 : BitVec 32) = 0#32 from rfl] at hc; sw_bd
                    sw_fast; refine hJ_sp (sp_s - 1#32, ()) mp (by dsimp only; omega)
                      ⟨rfl, by omega, fun α hα => ?_⟩
                    obtain ⟨k, hk, h0, hbp, hneg⟩ := hs_inv α hα
                    exact ⟨k, by have : k ≠ sp_s.toNat - 1 := fun h => hdph_nz (h ▸ h0); omega,
                      h0, hbp, hneg⟩
                  · have hdph_z : dDph scr_p (sp_s.toNat - 1) = 0#32 := by
                      (try simp only [hidx_s] at hc)
                      rw [hdph_s, show (0 : BitVec 32) = 0#32 from rfl] at hc; sw_bd
                    sw_fast; exact hJ_se () mp ⟨rfl, Or.inr ⟨hsps_pos, hdph_z⟩⟩
              · sw_fast
                refine wp_loop_inv (ts := [i32])
                  (fun (pick, ()) mpk => mpk = mp ∧ pick.toNat ≤ nv.toNat)
                  (fun (pick, ()) _ => nv.toNat - pick.toNat) ?_ ?_
                · intro J_pk hJ_pk; sw_fast; exact hJ_pk (0#32, ()) mp ⟨rfl, Nat.zero_le _⟩
                · intro J_pk; rintro ⟨pick, ⟨⟩⟩ mpk ⟨hmpk, hpk_le⟩ hJ_pk; subst mpk
                  sw_fast
                  refine wp_join_group (ts := [])
                    (fun () m_pk => m_pk = mp ∧ (pick.toNat = nv.toNat ∨
                      (pick.toNat < nv.toNat ∧ dVal scr_p pick.toNat = 0#32))) ?_ ?_
                  · rintro _ ⟨⟩ m_pk ⟨hmpk', hpk_done⟩; subst m_pk; clear hJ_pk
                    sw_split
                    · sw_fast
                      exact hret 10#64 fuel_1 rng_b scr_p mp hd_p.len_eq hd_p.prefix_eq hfl_dec
                        (Or.inr (Or.inl rfl)) (fun h => absurd h (by decide)) hmp
                    have hpk_lt : pick.toNat < nv.toNat := by
                      have hne : pick.toNat ≠ nv.toNat := by bv_omega
                      omega
                    have hpk_val0 : dVal scr_p pick.toNat = 0#32 :=
                      hpk_done.elim (fun h => by omega) (·.2)
                    have htnp_lt : tn_p.toNat < nv.toNat :=
                      dpll_tn_lt_of_unassigned hd_p hpk_lt hpk_val0
                    have hsp_lt : sp.toNat < nv.toNat := by have := hd_p.sp_le_tn; omega
                    generalize hst_eq : ({ s with
                      core := { s.core with fuel := fuel_1 }
                      scratch := { s.scratch with scratch_buf := scr_p, rng_state := rng_b } }
                      : FullState) = st_d at hmp
                    have hscrd_eq : st_d.scratch.scratch_buf = scr_p := by rw [← hst_eq]
                    have hlen_std : st_d.scratch.scratch_buf.length = c.scratch_cap := by
                      rw [hscrd_eq, hd_p.len_eq, hscr_len0]
                    sw_fast
                    refine wp_call_of_spec _ _ ?_; simp only [vals, Arg.val_var]
                    let scr_pre := ((st_d.scratch.scratch_buf.set (1048 + (sp.setWidth 64).toNat)
                      pick).set (1072 + (sp.setWidth 64).toNat) 0#32).set
                      (1120 + (sp.setWidth 64).toNat) tn_p
                    let st_d3 : FullState :=
                      { st_d with scratch := { st_d.scratch with scratch_buf := scr_pre } }
                    have hlen_d3 : st_d3.LengthsOk c := by
                      dsimp only [st_d3]; rw [← hst_eq]
                      exact ⟨{ hlen.core_ok with cur_vars_le := hlen.core_ok.cur_vars_le },
                        { hlen.scratch_ok with scratch_buf_len := by simp [scr_pre, hlen_std] }⟩
                    refine hRng (c.hdr, ()) m _ X ⟨c, st_d3, R, rfl, hlen_d3, hm, ?_⟩
                    rintro ⟨r, ⟨⟩⟩ st_r mr hcore_r _ hscr_r hmr
                    dsimp only [fullSafetySlice] at hcore_r hmr
                    generalize st_r.scratch.rng_state = rng' at hscr_r
                    have hst_r_eq : ({ st_d3 with
                        scratch := { st_d3.scratch with rng_state := rng' } } : FullState) =
                        st_r := by
                      cases st_r
                      exact congr (congrArg FullState.mk hcore_r.symm) hscr_r.symm
                    clear hcore_r hscr_r
                    have hlen_str : st_r.scratch.scratch_buf.length = c.scratch_cap := by
                      rw [← hst_r_eq]; simp [st_d3, scr_pre, hlen_std]
                    sw_fast
                    have hw_dom := dpll_rng_val_dom r
                    obtain ⟨_, hd_dec⟩ :=
                      dpll_decide_push_ok (by omega) hnv24 hd_p hpk_lt hpk_val0 hw_dom
                    have htnp1 : (tn_p + 1#32).toNat = tn_p.toNat + 1 := bv32_add1_nat (by omega)
                    have hsp1 : (sp + 1#32).toNat = sp.toNat + 1 := bv32_add1_nat (by omega)
                    have hsp_z : (sp.setWidth 64).toNat = sp.toNat := by simp only [bv_c0]
                    have hpk_z : (pick.setWidth 64).toNat = pick.toNat := by simp only [bv_c0]
                    have htnp_z : (tn_p.setWidth 64).toNat = tn_p.toNat := by simp only [bv_c0]
                    subst hst_r_eq; subst hst_eq
                    have hscr_dec_eq : ((((scr_p.set (1048 + sp.toNat) pick).set (1072 +
                        sp.toNat) 0#32).set (1120 + sp.toNat) tn_p).set (1024 + pick.toNat)
                        ((r &&& 1#64).setWidth 32 + 1#32)).set (1096 + tn_p.toNat) pick =
                      ((((scr_p.set (1048 + sp.toNat) pick).set (1072 + sp.toNat) 0#32).set
                        (1120 + sp.toNat) (BitVec.ofNat 32 tn_p.toNat)).set (1024 + pick.toNat)
                        ((r &&& 1#64).setWidth 32 + 1#32)).set (1096 + tn_p.toNat) pick := by
                      congr 4; exact (bv_ofNat_toNat_eq tn_p).symm
                    have heq_st : ({ st_d3 with scratch := { st_d3.scratch with
                        rng_state := rng', scratch_buf := ((st_d3.scratch.scratch_buf.set
                          (1024 + (pick.setWidth 64).toNat) ((r &&& 1#64).setWidth 32 + 1#32)).set
                          (1096 + (tn_p.setWidth 64).toNat) pick) } } : FullState) =
                      { s with
                        core := { s.core with fuel := fuel_1 }
                        scratch := { s.scratch with
                          scratch_buf := ((((scr_p.set (1048 + sp.toNat) pick).set (1072 +
                            sp.toNat) 0#32).set (1120 + sp.toNat) (BitVec.ofNat 32 tn_p.toNat)).set
                            (1024 + pick.toNat) ((r &&& 1#64).setWidth 32 + 1#32)).set
                            (1096 + tn_p.toNat) pick
                          rng_state := rng' } } := by
                      dsimp only [st_d3, scr_pre]; rw [hsp_z, hpk_z, htnp_z, hscr_dec_eq]
                    have hm_dec : (FullMem c { s with
                      core := { s.core with fuel := fuel_1 }
                      scratch := { s.scratch with
                        scratch_buf := ((((scr_p.set (1048 + sp.toNat) pick).set (1072 +
                          sp.toNat) 0#32).set (1120 + sp.toNat) (BitVec.ofNat 32 tn_p.toNat)).set
                          (1024 + pick.toNat) ((r &&& 1#64).setWidth 32 + 1#32)).set
                          (1096 + tn_p.toNat) pick
                        rng_state := rng' } } ⋆ R) m :=
                      by rw [show (1 : BitVec 64) = 1#64 from rfl] at *; exact heq_st ▸ hm
                    exact hJ_b (tn_p + 1#32, sp + 1#32, budget - 1#64, ()) m
                      (by dsimp only; omega) ⟨_, fuel_1, rng', hfl_dec,
                        by rw [htnp1, hsp1]; exact hd_dec, hm_dec⟩
                  intro J_pke hJ_pke
                  sw_split; rotate_left
                  · sw_fast; exact hJ_pke () mp ⟨rfl, Or.inl (by sw_bd)⟩
                  have hpk_lt : pick.toNat < nv.toNat := by sw_bd
                  generalize hst_eq : ({ s with
                    core := { s.core with fuel := fuel_1 }
                    scratch := { s.scratch with scratch_buf := scr_p, rng_state := rng_b } }
                    : FullState) = st_pk at hmp
                  have hscrpk_eq : st_pk.scratch.scratch_buf = scr_p := by rw [← hst_eq]
                  have hlen_stpk : st_pk.scratch.scratch_buf.length = c.scratch_cap := by
                    rw [hscrpk_eq, hd_p.len_eq, hscr_len0]
                  have hval_pk : st_pk.scratch.scratch_buf[1024 + pick.toNat]'(by omega) =
                      dVal scr_p pick.toNat := by
                    have hl : 1024 + pick.toNat < scr_p.length := by have := hd_p.len_eq; omega
                    simp only [hscrpk_eq]; unfold dVal dArr
                    rw [List.getElem?_eq_getElem hl, Option.getD_some]
                  sw_fast; sw_split
                  · have hpk1 : (pick + 1#32).toNat = pick.toNat + 1 := bv32_add1_nat (by omega)
                    sw_fast
                    exact hJ_pk (pick + 1#32, ()) mp (by dsimp only; omega) ⟨rfl, by omega⟩
                  · have hval0 : dVal scr_p pick.toNat = 0#32 := by
                      (try simp only [bv_c0] at hc)
                      rw [hval_pk, show (0 : BitVec 32) = 0#32 from rfl] at hc; sw_bd
                    sw_fast; exact hJ_pke () mp ⟨rfl, Or.inr ⟨hpk_lt, hval0⟩⟩
            intro J_pe hJ_pe
            clear hJ_b hret hRng hQ hfl_b hfl_dec hfl_pos hbud_pos hbud1
            sw_split; rotate_left
            · sw_fast; exact hJ_pe () mp ⟨rfl, Or.inl (by cases chg <;> simp at hc ⊢)⟩
            have hchg_t : chg = true := by cases chg <;> simp at hc ⊢
            sw_split
            · sw_fast; exact hJ_pe () mp ⟨rfl, Or.inr (by cases confl <;> simp at hc ⊢)⟩
            have hconfl_f : confl = false := by cases confl <;> simp at hc ⊢
            sw_fast
            refine wp_join_group (ts := [i32, .bool, .bool, i32])
              (fun (tn_e, confl_e, chg_e, _, ()) m_ce =>
                tn_p.toNat ≤ tn_e.toNat ∧ (chg_e = true → tn_p.toNat < tn_e.toNat) ∧
                ∃ scr_e : List (BitVec 32),
                  DpllStateOk s scr_e nv.toNat nc.toNat a0.toNat a1.toNat tn_e.toNat sp.toNat ∧
                  (confl_e = true → ∀ α, DpllSubprobSat s nv.toNat nc.toNat a0.toNat a1.toNat α →
                    ¬ dBranchPrefix scr_e sp.toNat α) ∧
                  (FullMem c { s with
                    core := { s.core with fuel := fuel_1 }
                    scratch := { s.scratch with scratch_buf := scr_e, rng_state := rng_b } } ⋆ R)
                    m_ce) ?_ ?_
            · rintro _ ⟨tn_e, confl_e, chg_e, _, ⟨⟩⟩ m_ce
                ⟨htne_ge, hchg_inc, scr_e, hd_e, hcf_e, hm_ce⟩; sw_fast
              refine hJ_p (tn_e, confl_e, chg_e, ()) m_ce ?_ ⟨scr_e, hd_e, hcf_e, hm_ce⟩
              dsimp only; rw [hchg_t, hconfl_f]
              have htn_nv := hd_e.tn_le_nv
              cases hce : chg_e <;> cases hcf : confl_e <;> simp
              · omega
              · omega
              · have := hchg_inc hce; omega
              · have := hchg_inc hce; omega
            intro J_ce hJ_ce; clear hJ_p hJ_pe hcf_p; sw_fast
            refine wp_loop_inv (ts := [i32, .bool, i32])
              (fun (tn_c, chg_c, ci, ()) mc =>
                ci.toNat ≤ nc.toNat ∧ tn_p.toNat ≤ tn_c.toNat ∧
                (chg_c = true → tn_p.toNat < tn_c.toNat) ∧ ∃ scr_c : List (BitVec 32),
                  DpllStateOk s scr_c nv.toNat nc.toNat a0.toNat a1.toNat tn_c.toNat sp.toNat ∧
                  (FullMem c { s with
                    core := { s.core with fuel := fuel_1 }
                    scratch := { s.scratch with scratch_buf := scr_c, rng_state := rng_b } } ⋆ R)
                    mc)
              (fun (_, _, ci, ()) _ => nc.toNat - ci.toNat) ?_ ?_
            · intro J_c hJ_c; sw_fast; exact hJ_c (tn_p, false, 0#32, ()) mp
                ⟨Nat.zero_le _, Nat.le_refl _, fun h => Bool.noConfusion h, scr_p, hd_p, hmp⟩
            · intro J_c; rintro ⟨tn_c, chg_c, ci, ⟨⟩⟩ mc ⟨hci_le, htnc_ge, hchg_c, scr_c, hd_c, hmc⟩
                hJ_c; clear hd_p hmp; sw_split; rotate_left
              · sw_fast; exact hconfl_f ▸ hJ_ce (tn_c, false, chg_c, ci, ()) mc
                  ⟨htnc_ge, hchg_c, scr_c, hd_c, fun h => Bool.noConfusion h, hmc⟩
              have hci_lt : ci.toNat < nc.toNat := by sw_bd
              have hci_ok := hbuf.2.2.2.2 ci.toNat hci_lt; have hres_hi := hbuf.2.2.2.1
              have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := bv32_add1_nat (by omega)
              have hci64 : (64#32 + ci).toNat = 64 + ci.toNat := bv32_add64_nat (by omega)
              generalize hstc_eq : ({ s with
                core := { s.core with fuel := fuel_1 }
                scratch := { s.scratch with scratch_buf := scr_c, rng_state := rng_b } }
                : FullState) = st_c at hmc
              have hscrc_eq : st_c.scratch.scratch_buf = scr_c := by rw [← hstc_eq]
              have hlen_stc : st_c.scratch.scratch_buf.length = c.scratch_cap := by
                rw [hscrc_eq, hd_c.len_eq, hscr_len0]
              have hci_z : (ci.setWidth 64).toNat = ci.toNat := by simp only [bv_c0]
              have hci64_z : ((64#32 + ci).setWidth 64).toNat = 64 + ci.toNat := by
                rw [← hci64]; simp only [bv_c0]
              sw_fast
              have hoff_eq : st_c.scratch.scratch_buf[(ci.setWidth 64).toNat]'(by omega) =
                  s.scratch.scratch_buf[ci.toNat]?.getD 0#32 := by
                have hl : ci.toNat < scr_c.length := by have := hd_c.len_eq; omega
                simp only [hscrc_eq, hci_z]; rw [← hd_c.prefix_eq ci.toNat (by omega),
                  List.getElem?_eq_getElem hl, Option.getD_some]
              have hsz_eq : st_c.scratch.scratch_buf[((64#32 + ci).setWidth 64).toNat]'(by omega) =
                  s.scratch.scratch_buf[64 + ci.toNat]?.getD 0#32 := by
                have hl : 64 + ci.toNat < scr_c.length := by have := hd_c.len_eq; omega
                simp only [hscrc_eq, hci64_z]; rw [← hd_c.prefix_eq (64 + ci.toNat) (by omega),
                  List.getElem?_eq_getElem hl, Option.getD_some]
              let off_v := st_c.scratch.scratch_buf[(ci.setWidth 64).toNat]'(by omega)
              let sz_v := st_c.scratch.scratch_buf[((64#32 + ci).setWidth 64).toNat]'(by omega)
              have hoff_n : off_v.toNat = (s.scratch.scratch_buf[ci.toNat]?.getD 0#32).toNat :=
                congrArg BitVec.toNat hoff_eq
              have hsz_n : sz_v.toNat = (s.scratch.scratch_buf[64 + ci.toNat]?.getD 0#32).toNat :=
                congrArg BitVec.toNat hsz_eq
              refine wp_join_group (ts := [.bool, i32, i32, i32])
                (fun (sat_e, un_e, ul_e, _, ()) m_ke => m_ke = mc ∧
                  (sat_e = false → un_e = 0#32 → ∀ j < sz_v.toNat,
                    let l := (s.scratch.scratch_buf[off_v.toNat + j]?.getD 0#32).toNat
                    dVal scr_c (l / 2) ≠ 0#32 ∧ dVal scr_c (l / 2) ≠ dWant l) ∧
                  (sat_e = false → un_e = 1#32 →
                    ul_e.toNat < 2 * nv.toNat ∧ dVal scr_c (ul_e.toNat / 2) = 0#32 ∧
                    ∀ j < sz_v.toNat,
                      let l := (s.scratch.scratch_buf[off_v.toNat + j]?.getD 0#32).toNat
                      l = ul_e.toNat ∨ (dVal scr_c (l / 2) ≠ 0#32 ∧ dVal scr_c (l / 2) ≠ dWant l)))
                ?_ ?_
              · rintro _ ⟨sat_e, un_e, ul_e, _, ⟨⟩⟩ m_ke ⟨hmke, hcf_k, hun_k⟩; subst m_ke
                sw_unroll; sw_split
                · have hsat_t : sat_e = true := by cases sat_e <;> simp at hc ⊢
                  sw_unroll; sw_split
                  · sw_unroll; subst hstc_eq; exact hJ_c (tn_c, chg_c, ci + 1#32, ()) mc
                      (by dsimp only; omega) ⟨by omega, htnc_ge, hchg_c, scr_c, hd_c, hmc⟩
                  · exfalso; rw [hsat_t] at hc; exact Bool.noConfusion hc
                · have hsat_f : sat_e = false := by cases sat_e <;> simp at hc ⊢
                  sw_split
                  · have hun0 : un_e = 0#32 := by sw_bd
                    have hfls := hcf_k hsat_f hun0; rw [hoff_n, hsz_n] at hfls
                    sw_fast; subst hstc_eq
                    exact hJ_ce (tn_c, true, chg_c, ci, ()) mc ⟨htnc_ge, hchg_c, scr_c, hd_c,
                      fun _ => dpll_clause_confl (by omega) hbuf hd_c hci_lt hfls, hmc⟩
                  · sw_unroll; sw_split
                    · exfalso; rw [hsat_f] at hc; exact Bool.noConfusion hc
                    · sw_split
                      · have hun1 : un_e = 1#32 := by sw_bd
                        obtain ⟨hul_lt, hul_z, hun_all⟩ := hun_k hsat_f hun1
                        rw [hoff_n, hsz_n] at hun_all
                        have himp := dpll_clause_unit_imp (by omega) hbuf hd_c hci_lt hun_all
                        have hu_lt : (ul_e >>> (1 : Nat)).toNat < nv.toNat := by
                          rw [bv32_shr1_toNat']; omega
                        have hval0_u : dVal scr_c (ul_e >>> (1 : Nat)).toNat = 0#32 := by
                          rw [bv32_shr1_toNat']; exact hul_z
                        have hw_eq : (ul_e &&& 1#32) + 1#32 = dWant ul_e.toNat := dWant_eq_bv ul_e
                        obtain ⟨htnc_lt, hd_c'⟩ := dpll_push_implied (by omega) hnv24 hd_c hu_lt
                          hval0_u (hw_eq ▸ dWant_dom ul_e.toNat)
                          (by rw [bv32_shr1_toNat', hw_eq]; exact himp)
                        have htnc1 : (tn_c + 1#32).toNat = tn_c.toNat + 1 :=
                          bv32_add1_nat (by omega)
                        sw_unroll; subst hstc_eq
                        have hmc' : (FullMem c { s with
                          core := { s.core with fuel := fuel_1 }
                          scratch := { s.scratch with
                            scratch_buf := (scr_c.set (1024 + (ul_e >>> (1 : Nat)).toNat)
                              ((ul_e &&& 1#32) + 1#32)).set (1096 + tn_c.toNat)
                              (ul_e >>> (1 : Nat))
                            rng_state := rng_b } } ⋆ R) m := by
                          simp only [show ((ul_e >>> (1 : Nat)).setWidth 64).toNat =
                              (ul_e >>> (1 : Nat)).toNat by simp only [bv_c0],
                            show (tn_c.setWidth 64).toNat = tn_c.toNat by simp only [bv_c0],
                            show (1 : BitVec 32) = 1#32 from rfl] at hm; exact hm
                        exact hJ_c (tn_c + 1#32, true, ci + 1#32, ()) m (by dsimp only; omega)
                          ⟨by omega, by omega, fun _ => by omega, _, by rw [htnc1]; exact hd_c',
                            hmc'⟩
                      · sw_unroll; subst hstc_eq; exact hJ_c (tn_c, chg_c, ci + 1#32, ()) mc
                          (by dsimp only; omega) ⟨by omega, htnc_ge, hchg_c, scr_c, hd_c, hmc⟩
              intro J_ke hJ_ke; clear hJ_ce hJ_c hchg_c htnc_ge hci_le; sw_fast
              refine wp_loop_inv (ts := [i32, i32, i32])
                (fun (un, ul, k, ()) mk => mk = mc ∧ k.toNat ≤ sz_v.toNat ∧ un.toNat ≤ k.toNat ∧
                  (un = 0#32 → ∀ j < k.toNat,
                    let l := (s.scratch.scratch_buf[off_v.toNat + j]?.getD 0#32).toNat
                    dVal scr_c (l / 2) ≠ 0#32 ∧ dVal scr_c (l / 2) ≠ dWant l) ∧
                  (un = 1#32 → ul.toNat < 2 * nv.toNat ∧ dVal scr_c (ul.toNat / 2) = 0#32 ∧
                    ∀ j < k.toNat,
                      let l := (s.scratch.scratch_buf[off_v.toNat + j]?.getD 0#32).toNat
                      l = ul.toNat ∨ (dVal scr_c (l / 2) ≠ 0#32 ∧ dVal scr_c (l / 2) ≠ dWant l)))
                (fun (_, _, k, ()) _ => sz_v.toNat - k.toNat) ?_ ?_
              · intro J_k hJ_k; sw_fast; exact hJ_k (0#32, 0#32, 0#32, ()) mc
                  ⟨rfl, Nat.zero_le _, Nat.zero_le _, fun _ _ hj => by simp at hj,
                    fun h => absurd h (by decide)⟩
              · intro J_k; rintro ⟨un, ul, k, ⟨⟩⟩ mk ⟨hmk, hk_le, hun_le, hu0, hu1⟩ hJ_k; subst mk
                sw_split; rotate_left
                · have hk_eq : k.toNat = sz_v.toNat := by
                    dsimp only [sz_v] at hk_le ⊢
                    simp only [bv_c0, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat] at hc hk_le ⊢
                    omega
                  sw_fast; exact hJ_ke (false, un, ul, k, ()) mc
                    ⟨rfl, fun _ h0 => hk_eq ▸ hu0 h0, fun _ h1 => hk_eq ▸ hu1 h1⟩
                have hk_lt : k.toNat < sz_v.toNat := by
                  dsimp only [sz_v]; sw_bd
                have hidx_ok : (off_v.setWidth 64 + k.setWidth 64).toNat = off_v.toNat + k.toNat :=
                  by simp only [bv_c0]; omega
                have hl_eq : st_c.scratch.scratch_buf[(off_v.setWidth 64 + k.setWidth 64).toNat]'(by
                    omega) = s.scratch.scratch_buf[off_v.toNat + k.toNat]?.getD 0#32 := by
                  have hl : off_v.toNat + k.toNat < scr_c.length := by have := hd_c.len_eq; omega
                  simp only [hscrc_eq, hidx_ok]; rw [← hd_c.prefix_eq (off_v.toNat + k.toNat)
                    (by omega), List.getElem?_eq_getElem hl, Option.getD_some]
                have hl_lt : (st_c.scratch.scratch_buf[(off_v.setWidth 64 + k.setWidth 64).toNat]'(
                    by omega)).toNat < 2 * nv.toNat := by
                  rw [hl_eq]
                  have hmem : (s.scratch.scratch_buf[off_v.toNat + k.toNat]?.getD 0#32).toNat ∈
                      sweepClauseLits s ci.toNat := by
                    rw [sweepClauseLits_eq_range (by omega)]
                    exact List.mem_map.mpr ⟨k.toNat, List.mem_range.mpr (by omega), by rw [hoff_n]⟩
                  exact hci_ok.2.2 _ hmem
                have hlv_lt : (st_c.scratch.scratch_buf[(off_v.setWidth 64 + k.setWidth 64).toNat]'(
                    by omega) >>> (1 : Nat)).toNat < nv.toNat := by rw [bv32_shr1_toNat']; omega
                sw_fast
                generalize hl_v_eq :
                  st_c.scratch.scratch_buf[(off_v.setWidth 64 + k.setWidth 64).toNat]'(by omega) =
                  lit_c at hl_eq hl_lt hlv_lt ⊢
                have hvw_eq : st_c.scratch.scratch_buf[1024 + lit_c.toNat / 2]'(by omega) =
                    dVal scr_c (lit_c.toNat / 2) := by
                  have hl : 1024 + lit_c.toNat / 2 < scr_c.length := by have := hd_c.len_eq; omega
                  simp only [hscrc_eq]; unfold dVal dArr
                  rw [List.getElem?_eq_getElem hl, Option.getD_some]
                have hk1 : (k + 1#32).toNat = k.toNat + 1 := bv32_add1_nat (by omega)
                sw_split
                · sw_fast; exact hJ_ke (true, un, ul, k, ()) mc
                    ⟨rfl, fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩
                have hne_want : dVal scr_c (lit_c.toNat / 2) ≠ dWant lit_c.toNat := by
                  (try simp only [bv_c0] at hc)
                  rw [hvw_eq, show (1 : BitVec 32) = 1#32 from rfl, dWant_eq_bv] at hc; exact hc
                sw_unroll; sw_split
                · have hvw0 : dVal scr_c (lit_c.toNat / 2) = 0#32 := by
                    (try simp only [bv_c0] at hc)
                    rw [hvw_eq, show (0 : BitVec 32) = 0#32 from rfl] at hc; exact hc
                  have hun1 : (un + 1#32).toNat = un.toNat + 1 := bv32_add1_nat (by omega)
                  sw_fast
                  refine hJ_k (un + 1#32, lit_c, k + 1#32, ()) mc (by dsimp only; omega)
                    ⟨rfl, by omega, by omega, fun h0 => ?_, fun h1 => ?_⟩
                  · exfalso; have := congrArg BitVec.toNat h0; simp [hun1] at this
                  · have hun0 : un = 0#32 := by
                      apply BitVec.eq_of_toNat_eq
                      have := congrArg BitVec.toNat h1; simp [hun1] at this; exact this
                    refine ⟨hl_lt, hvw0, fun j hj => ?_⟩; rw [hk1] at hj
                    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
                    · exact Or.inr (hu0 hun0 j hlt)
                    · left; exact congrArg BitVec.toNat hl_eq.symm
                · have hvw_nz : dVal scr_c (lit_c.toNat / 2) ≠ 0#32 := by
                    (try simp only [bv_c0] at hc)
                    rw [hvw_eq, show (0 : BitVec 32) = 0#32 from rfl] at hc; exact hc
                  sw_fast
                  refine hJ_k (un, ul, k + 1#32, ()) mc (by dsimp only; omega)
                    ⟨rfl, by omega, by omega, fun h0 j hj => ?_, fun h1 => ?_⟩
                  · rw [hk1] at hj; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
                    · exact hu0 h0 j hlt
                    · rw [← congrArg BitVec.toNat hl_eq]; exact ⟨hvw_nz, hne_want⟩
                  · obtain ⟨hul_lt, hul_z, hall⟩ := hu1 h1
                    refine ⟨hul_lt, hul_z, fun j hj => ?_⟩; rw [hk1] at hj
                    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
                    · exact hall j hlt
                    · right; rw [← congrArg BitVec.toNat hl_eq]; exact ⟨hvw_nz, hne_want⟩
      intro J_a1 hJ_a1; sw_split; rotate_left
      · sw_fast; exact hJ_a1 (tn0, ()) m_a0 ⟨scr0, hd_a0, hm_a0⟩
      have ha1_lt : a1.toNat < 2 * nv.toNat := by
        rw [← (by simp only [bv_c0]; omega : (nv <<< (1 : Nat)).toNat = 2 * nv.toNat)]; sw_bd
      have hv1_lt : (a1 >>> (1 : Nat)).toNat < nv.toNat := by rw [bv32_shr1_toNat']; omega
      generalize hst0_eq : ({ s with scratch := { s.scratch with scratch_buf := scr0 } }
        : FullState) = st0 at hm_a0
      have hscr0_eq : st0.scratch.scratch_buf = scr0 := by rw [← hst0_eq]
      have hlen_st0 : st0.scratch.scratch_buf.length = c.scratch_cap := by
        rw [hscr0_eq, hd_a0.len_eq, hscr_len0]
      have hval_v1 : st0.scratch.scratch_buf[1024 + a1.toNat / 2]'(by omega) =
          dVal scr0 (a1.toNat / 2) := by
        have hl : 1024 + a1.toNat / 2 < scr0.length := by have := hd_a0.len_eq; omega
        simp only [hscr0_eq]; unfold dVal dArr; rw [List.getElem?_eq_getElem hl, Option.getD_some]
      sw_fast
      refine wp_join_group (ts := []) (fun () m_c1 => m_c1 = m_a0 ∧
        (dVal scr0 (a1.toNat / 2) = 0#32 ∨ dVal scr0 (a1.toNat / 2) = dWant a1.toNat)) ?_ ?_
      · rintro _ ⟨⟩ m_c1 ⟨hmc1, _⟩; subst m_c1; sw_unroll; sw_split
        · have hv1_z : dVal scr0 (a1.toNat / 2) = 0#32 := by
            rw [hval_v1, show (0 : BitVec 32) = 0#32 from rfl] at hc; exact hc
          have hw1_eq : (a1 &&& 1#32) + 1#32 = dWant a1.toNat := dWant_eq_bv a1
          obtain ⟨htn0_lt, hd_a1⟩ := dpll_push_implied (by omega) hnv24 hd_a0 hv1_lt
            (by rw [bv32_shr1_toNat']; exact hv1_z) (hw1_eq ▸ dWant_dom a1.toNat)
            (fun α hα _ => by
              rw [bv32_shr1_toNat', hw1_eq]; exact dLit_sat_iff_dValMatch.mp (hα.1.2 ha1_lt))
          have htn01 : (tn0 + 1#32).toNat = tn0.toNat + 1 := bv32_add1_nat (by omega)
          sw_fast; subst hst0_eq
          have hm1' : (FullMem c { s with scratch := { s.scratch with
            scratch_buf := (scr0.set (1024 + (a1 >>> (1 : Nat)).toNat) ((a1 &&& 1#32) + 1#32)).set
              (1096 + tn0.toNat) (a1 >>> (1 : Nat)) } } ⋆ R) m := by
            simp only [show ((a1 >>> (1 : Nat)).setWidth 64).toNat = (a1 >>> (1 : Nat)).toNat by
              simp only [bv_c0], show (tn0.setWidth 64).toNat = tn0.toNat by simp only [bv_c0],
              show (1 : BitVec 32) = 1#32 from rfl] at hm; exact hm
          exact hJ_a1 (tn0 + 1#32, ()) m ⟨_, by rw [htn01]; exact hd_a1, hm1'⟩
        · sw_fast; subst hst0_eq; exact hJ_a1 (tn0, ()) m_a0 ⟨scr0, hd_a0, hm_a0⟩
      intro J_c1 hJ_c1; sw_split; rotate_left
      · have hz : dVal scr0 (a1.toNat / 2) = 0#32 := by
          rw [hval_v1, show (0 : BitVec 32) = 0#32 from rfl] at hc; exact hc
        sw_fast; exact hJ_c1 () m_a0 ⟨rfl, Or.inl hz⟩
      have hnz : dVal scr0 (a1.toNat / 2) ≠ 0#32 := by
        rw [hval_v1, show (0 : BitVec 32) = 0#32 from rfl] at hc; exact hc
      sw_split; rotate_left
      · have heq : dVal scr0 (a1.toNat / 2) = dWant a1.toNat := by
          rw [hval_v1, show (1 : BitVec 32) = 1#32 from rfl, dWant_eq_bv] at hc; exact hc
        sw_fast; exact hJ_c1 () m_a0 ⟨rfl, Or.inr heq⟩
      have hne : dVal scr0 (a1.toNat / 2) ≠ dWant a1.toNat := by
        rw [hval_v1, show (1 : BitVec 32) = 1#32 from rfl, dWant_eq_bv] at hc; exact hc
      sw_fast; subst hst0_eq
      exact hret 20#64 s.core.fuel s.scratch.rng_state scr0 m_a0 hd_a0.len_eq hd_a0.prefix_eq
        (Nat.le_refl _) (Or.inr (Or.inr rfl))
        (fun _ => dpll_assump_confl_unsat hd_a0 ha1_lt hnz hne) hm_a0
    intro J_a0 hJ_a0; sw_split; rotate_left
    · sw_fast; exact hJ_a0 (0#32, ()) m1 ⟨scr, hd0, hm1⟩
    have ha0_lt : a0.toNat < 2 * nv.toNat := by
      rw [← (by simp only [bv_c0]; omega : (nv <<< (1 : Nat)).toNat = 2 * nv.toNat)]; sw_bd
    have hv0_lt : (a0 >>> (1 : Nat)).toNat < nv.toNat := by rw [bv32_shr1_toNat']; omega
    have hw0_eq : (a0 &&& 1#32) + 1#32 = dWant a0.toNat := dWant_eq_bv a0
    obtain ⟨_, hd_a0⟩ := dpll_push_implied (by omega) hnv24 hd0 hv0_lt
      (by rw [bv32_shr1_toNat']; exact hval0 _ (by omega)) (hw0_eq ▸ dWant_dom a0.toNat)
      (fun α hα _ => by
        rw [bv32_shr1_toNat', hw0_eq]; exact dLit_sat_iff_dValMatch.mp (hα.1.1 ha0_lt))
    generalize hst_eq : ({ s with scratch := { s.scratch with scratch_buf := scr } } : FullState)
      = st_a0 at hm1
    have hlen_sta0 : st_a0.scratch.scratch_buf.length = c.scratch_cap := by
      rw [← hst_eq]; dsimp only; omega
    sw_fast; subst hst_eq
    have hm_a0' : (FullMem c { s with scratch := { s.scratch with
      scratch_buf := (scr.set (1024 + (a0 >>> (1 : Nat)).toNat) ((a0 &&& 1#32) + 1#32)).set
        1096 (a0 >>> (1 : Nat)) } } ⋆ R) m := by
      simp only [show ((a0 >>> (1 : Nat)).setWidth 64).toNat = (a0 >>> (1 : Nat)).toNat by
        simp only [bv_c0], show (0 : BitVec 32) = 0#32 from rfl,
        show ((0#32 : BitVec 32).setWidth 64).toNat = 0 from rfl, Nat.add_zero,
        show (1 : BitVec 32) = 1#32 from rfl] at hm; exact hm
    exact hJ_a0 (1#32, ()) m ⟨_, by simpa [show (1#32 : BitVec 32).toNat = 1 from rfl] using hd_a0,
      hm_a0'⟩
end
end LeanQbe.T.Examples.Kissat.Full
