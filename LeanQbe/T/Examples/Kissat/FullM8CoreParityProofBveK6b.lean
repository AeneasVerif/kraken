/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBveK6b0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M8 Core Parity (`FullM8CoreParity`) Rank #8 Proofs — Part K6b (`Analyze`, `Solve`)

UNSAT-only `Func.wp` proofs (`public section`, strictly `std3` axioms):
1. `full_k6_analyze_m8_wp`: certifies `m8K6AnalyzeSpec` for `full_k6_analyze_m8_body`.
2. `full_k6_solve_m8_wp`: certifies `m8K6SolveSpec` for `full_k6_solve_m8_body`.
Re-exports `full_k6_prop_m8_wp` via `FullM8CoreParityProofBveK6b0`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8CoreParity

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

open scoped M8K6bTactics

local macro "m8k6_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. Analyze & Solve Frame Invariants (`M8AnaKeep`, `M8AnaPost`, `M8SolveKeep`) -/

/-- Pre-append frame invariant for `full_k6_analyze_m8`. -/
private def M8AnaKeep (scr0 scr : List (BitVec 32)) : Prop :=
  M8K6BufOk scr ∧ scr.length = scr0.length ∧
  (∀ i < 4195, scr[i]? = scr0[i]?) ∧
  scr[4199]? = scr0[4199]? ∧ scr[4205]? = scr0[4205]? ∧
  scr[4206]? = scr0[4206]? ∧ scr[4207]? = scr0[4207]? ∧
  scr[4211]? = scr0[4211]? ∧ scr[4213]? = scr0[4213]? ∧
  (∀ i, 11648 ≤ i → i < 15232 → scr[i]? = scr0[i]?)

/-- Post-append frame invariant matching all postconditions of `m8K6AnalyzeSpec`. -/
private def M8AnaPost (scr0 scr : List (BitVec 32)) : Prop :=
  M8K6BufOk scr ∧ scr.length = scr0.length ∧
  (∀ i < 4193, scr[i]? = scr0[i]?) ∧
  scr[4194]? = scr0[4194]? ∧
  (scr0[4193]?.getD 0#32).toNat ≤ (scr[4193]?.getD 0#32).toNat ∧
  (∀ cid < (scr0[4193]?.getD 0#32).toNat, scr[13696 + cid]? = scr0[13696 + cid]?) ∧
  scr[4199]? = scr0[4199]? ∧ scr[4205]? = scr0[4205]? ∧
  scr[4207]? = scr0[4207]? ∧ scr[4211]? = scr0[4211]? ∧
  scr[4213]? = scr0[4213]? ∧
  (∀ i, 14720 ≤ i → i < 15232 → scr[i]? = scr0[i]?)

private theorem m8AnaKeep_refl {scr0 : List (BitVec 32)} (h : M8K6BufOk scr0) :
    M8AnaKeep scr0 scr0 :=
  ⟨h, rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

private theorem m8AnaKeep_to_post {scr0 scr : List (BitVec 32)} (hk : M8AnaKeep scr0 scr) :
    M8AnaPost scr0 scr := by
  have h1 : scr[4193]? = scr0[4193]? := hk.2.2.1 4193 (by decide)
  have hnc_le : (scr0[4193]?.getD 0#32).toNat ≤ 1024 := by
    rw [← h1]; exact hk.1.nc_le
  refine ⟨hk.1, hk.2.1, fun i hi => hk.2.2.1 i (by omega), hk.2.2.1 4194 (by decide),
    by rw [h1]; exact Nat.le_refl _,
    fun cid hcid => hk.2.2.2.2.2.2.2.2.2 (13696 + cid) (by omega) (by omega),
    hk.2.2.2.1, hk.2.2.2.2.1, hk.2.2.2.2.2.2.1, hk.2.2.2.2.2.2.2.1,
    hk.2.2.2.2.2.2.2.2.1, fun i h1 h2 => hk.2.2.2.2.2.2.2.2.2 i (by omega) h2⟩

private theorem m8AnaKeep_of_frame {scr0 scr scr' : List (BitVec 32)} (hk : M8AnaKeep scr0 scr)
    (hlen : scr'.length = scr.length)
    (hlo : ∀ i < 4195, scr'[i]? = scr[i]?)
    (h199 : scr'[4199]? = scr[4199]?) (h205 : scr'[4205]? = scr[4205]?)
    (h206 : scr'[4206]? = scr[4206]?) (h207 : scr'[4207]? = scr[4207]?)
    (h211 : scr'[4211]? = scr[4211]?) (h213 : scr'[4213]? = scr[4213]?)
    (hmet : ∀ i, 11648 ≤ i → i < 15232 → scr'[i]? = scr[i]?) :
    M8AnaKeep scr0 scr' := by
  have hok := m8K6BufOk_of_frame hk.1 hlen fun idx _ hor => by
    rcases hor with rfl | rfl | rfl | ⟨ha, hb⟩
    · exact hlo 4193 (by decide)
    · exact h206
    · exact h207
    · exact hmet idx ha (by omega)
  exact ⟨hok, hlen.trans hk.2.1, fun i hi => (hlo i hi).trans (hk.2.2.1 i hi),
    h199.trans hk.2.2.2.1, h205.trans hk.2.2.2.2.1, h206.trans hk.2.2.2.2.2.1,
    h207.trans hk.2.2.2.2.2.2.1, h211.trans hk.2.2.2.2.2.2.2.1,
    h213.trans hk.2.2.2.2.2.2.2.2.1,
    fun i h1 h2 => (hmet i h1 h2).trans (hk.2.2.2.2.2.2.2.2.2 i h1 h2)⟩

private theorem m8AnaKeep_of_set {scr0 scr : List (BitVec 32)} (hk : M8AnaKeep scr0 scr)
    (idx : Nat) (v : BitVec 32)
    (hlo : 4195 ≤ idx) (h199 : idx ≠ 4199) (h205 : idx ≠ 4205) (h206 : idx ≠ 4206)
    (h207 : idx ≠ 4207) (h211 : idx ≠ 4211) (h213 : idx ≠ 4213)
    (hmet : idx < 11648 ∨ 15232 ≤ idx) :
    M8AnaKeep scr0 (scr.set idx v) :=
  m8AnaKeep_of_frame hk List.length_set
    (fun _ hi => List.getElem?_set_ne (by omega))
    (List.getElem?_set_ne h199) (List.getElem?_set_ne h205)
    (List.getElem?_set_ne h206) (List.getElem?_set_ne h207)
    (List.getElem?_set_ne h211) (List.getElem?_set_ne h213)
    (fun _ h1 h2 => List.getElem?_set_ne (by omega))

private theorem m8AnaKeep_of_ana_cl {scr0 scr scr' : List (BitVec 32)} (hk : M8AnaKeep scr0 scr)
    (hlen : scr'.length = scr.length)
    (hkeep : ∀ idx < scr.length,
      idx ≠ 4208 → idx ≠ 4209 → idx ≠ 4210 → idx ≠ 4212 →
      (idx < 5760 ∨ 6528 ≤ idx) → (idx < 15232 ∨ 15744 ≤ idx) → scr'[idx]? = scr[idx]?) :
    M8AnaKeep scr0 scr' := by
  have hb := hk.1.base_ge
  have hat : ∀ i, i < 4224 → i ≠ 4208 → i ≠ 4209 → i ≠ 4210 → i ≠ 4212 → scr'[i]? = scr[i]? :=
    fun i hi h8 h9 h10 h12 => hkeep i (by omega) h8 h9 h10 h12 (Or.inl (by omega))
      (Or.inl (by omega))
  exact m8AnaKeep_of_frame hk hlen
    (fun i hi => hat i (by omega) (by omega) (by omega) (by omega) (by omega))
    (hat 4199 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hat 4205 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hat 4206 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hat 4207 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hat 4211 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hat 4213 (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun i h1 h2 => hkeep i (by omega) (by omega) (by omega) (by omega) (by omega)
      (Or.inr (by omega)) (Or.inl h2))

private theorem m8AnaKeep_of_backtrack {scr0 scr scr' : List (BitVec 32)} (hk : M8AnaKeep scr0 scr)
    (hlen : scr'.length = scr.length)
    (hkeep : ∀ idx < scr.length,
      (idx < 4195 ∨ (4199 ≤ idx ∧ idx < 4224) ∨ (4736 ≤ idx ∧ idx < 6528) ∨ 7040 ≤ idx) →
      scr'[idx]? = scr[idx]?) :
    M8AnaKeep scr0 scr' := by
  have hb := hk.1.base_ge
  exact m8AnaKeep_of_frame hk hlen
    (fun i hi => hkeep i (by omega) (Or.inl hi))
    (hkeep 4199 (by omega) (Or.inr (Or.inl ⟨by decide, by decide⟩)))
    (hkeep 4205 (by omega) (Or.inr (Or.inl ⟨by decide, by decide⟩)))
    (hkeep 4206 (by omega) (Or.inr (Or.inl ⟨by decide, by decide⟩)))
    (hkeep 4207 (by omega) (Or.inr (Or.inl ⟨by decide, by decide⟩)))
    (hkeep 4211 (by omega) (Or.inr (Or.inl ⟨by decide, by decide⟩)))
    (hkeep 4213 (by omega) (Or.inr (Or.inl ⟨by decide, by decide⟩)))
    (fun i h1 h2 => hkeep i (by omega) (Or.inr (Or.inr (Or.inr (by omega)))))

private theorem m8AnaKeep_of_mtf {scr0 scr scr' : List (BitVec 32)} (hk : M8AnaKeep scr0 scr)
    (hlen : scr'.length = scr.length)
    (hkeep : ∀ idx < scr.length, (idx < 4200 ∨ (4204 ≤ idx ∧ idx < 4736) ∨ 5504 ≤ idx) →
      scr'[idx]? = scr[idx]?) :
    M8AnaKeep scr0 scr' := by
  have hb := hk.1.base_ge
  exact m8AnaKeep_of_frame hk hlen
    (fun i hi => hkeep i (by omega) (Or.inl (by omega)))
    (hkeep 4199 (by omega) (Or.inl (by decide)))
    (hkeep 4205 (by omega) (Or.inr (Or.inl ⟨by decide, by decide⟩)))
    (hkeep 4206 (by omega) (Or.inr (Or.inl ⟨by decide, by decide⟩)))
    (hkeep 4207 (by omega) (Or.inr (Or.inl ⟨by decide, by decide⟩)))
    (hkeep 4211 (by omega) (Or.inr (Or.inl ⟨by decide, by decide⟩)))
    (hkeep 4213 (by omega) (Or.inr (Or.inl ⟨by decide, by decide⟩)))
    (fun i h1 h2 => hkeep i (by omega) (Or.inr (Or.inr (by omega))))

private theorem m8AnaPost_of_watch {scr0 scr scr' : List (BitVec 32)} (hp : M8AnaPost scr0 scr)
    (hlen : scr'.length = scr.length)
    (hkeep : ∀ idx < scr.length, (idx < 7040 ∨ 11648 ≤ idx) → scr'[idx]? = scr[idx]?) :
    M8AnaPost scr0 scr' := by
  have hb := hp.1.base_ge
  have hok := m8_k6BufOk_watch_frame hp.1 hlen hkeep
  have hnc_le : (scr0[4193]?.getD 0#32).toNat ≤ 1024 := Nat.le_trans hp.2.2.2.2.1 hp.1.nc_le
  refine ⟨hok, hlen.trans hp.2.1,
    fun i hi => (hkeep i (by omega) (Or.inl (by omega))).trans (hp.2.2.1 i hi),
    (hkeep 4194 (by omega) (Or.inl (by decide))).trans hp.2.2.2.1,
    by rw [hkeep 4193 (by omega) (Or.inl (by decide))]; exact hp.2.2.2.2.1,
    fun cid hcid => (hkeep (13696 + cid) (by omega) (Or.inr (by omega))).trans
      (hp.2.2.2.2.2.1 cid hcid),
    (hkeep 4199 (by omega) (Or.inl (by decide))).trans hp.2.2.2.2.2.2.1,
    (hkeep 4205 (by omega) (Or.inl (by decide))).trans hp.2.2.2.2.2.2.2.1,
    (hkeep 4207 (by omega) (Or.inl (by decide))).trans hp.2.2.2.2.2.2.2.2.1,
    (hkeep 4211 (by omega) (Or.inl (by decide))).trans hp.2.2.2.2.2.2.2.2.2.1,
    (hkeep 4213 (by omega) (Or.inl (by decide))).trans hp.2.2.2.2.2.2.2.2.2.2.1,
    fun i h1 h2 => (hkeep i (by omega) (Or.inr (by omega))).trans
      (hp.2.2.2.2.2.2.2.2.2.2.2 i h1 h2)⟩

private theorem m8AnaPost_of_assign {scr0 scr scr' : List (BitVec 32)} (hp : M8AnaPost scr0 scr)
    (hlen : scr'.length = scr.length)
    (hkeep : ∀ idx < scr.length, idx ≠ 4197 → idx ≠ 4198 →
      (idx < 4224 ∨ 4736 ≤ idx) → (idx < 5504 ∨ 6016 ≤ idx) →
      (idx < 6528 ∨ 7040 ≤ idx) → scr'[idx]? = scr[idx]?) :
    M8AnaPost scr0 scr' := by
  have hb := hp.1.base_ge
  have hat : ∀ i, i < 4224 → i ≠ 4197 → i ≠ 4198 → scr'[i]? = scr[i]? :=
    fun i hi h7 h8 => hkeep i (by omega) h7 h8 (Or.inl hi) (Or.inl (by omega)) (Or.inl (by omega))
  have hhi : ∀ i, 11648 ≤ i → i < 15232 → scr'[i]? = scr[i]? :=
    fun i h1 h2 => hkeep i (by omega) (by omega) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  have hok := m8K6BufOk_of_frame hp.1 hlen fun idx _ hor => by
    rcases hor with rfl | rfl | rfl | ⟨ha, hb'⟩
    · exact hat 4193 (by decide) (by decide) (by decide)
    · exact hat 4206 (by decide) (by decide) (by decide)
    · exact hat 4207 (by decide) (by decide) (by decide)
    · exact hhi idx ha (by omega)
  have hnc_le : (scr0[4193]?.getD 0#32).toNat ≤ 1024 := Nat.le_trans hp.2.2.2.2.1 hp.1.nc_le
  refine ⟨hok, hlen.trans hp.2.1,
    fun i hi => (hat i (by omega) (by omega) (by omega)).trans (hp.2.2.1 i hi),
    (hat 4194 (by decide) (by decide) (by decide)).trans hp.2.2.2.1,
    by rw [hat 4193 (by decide) (by decide) (by decide)]; exact hp.2.2.2.2.1,
    fun cid hcid => (hhi (13696 + cid) (by omega) (by omega)).trans (hp.2.2.2.2.2.1 cid hcid),
    (hat 4199 (by decide) (by decide) (by decide)).trans hp.2.2.2.2.2.2.1,
    (hat 4205 (by decide) (by decide) (by decide)).trans hp.2.2.2.2.2.2.2.1,
    (hat 4207 (by decide) (by decide) (by decide)).trans hp.2.2.2.2.2.2.2.2.1,
    (hat 4211 (by decide) (by decide) (by decide)).trans hp.2.2.2.2.2.2.2.2.2.1,
    (hat 4213 (by decide) (by decide) (by decide)).trans hp.2.2.2.2.2.2.2.2.2.2.1,
    fun i h1 h2 => (hhi i (by omega) h2).trans (hp.2.2.2.2.2.2.2.2.2.2.2 i h1 h2)⟩

private theorem m8Analyze_append {scr0 scr : List (BitVec 32)} (hk : M8AnaKeep scr0 scr)
    {nc_old alen lsz n_ant : BitVec 32}
    (hnc_eq : scr[4193]?.getD 0#32 = nc_old) (hnc_lt : nc_old.toNat < 1024)
    (hl_le : lsz.toNat ≤ 256) (ha_le : n_ant.toNat ≤ 512)
    (hfit : alen.toNat + lsz.toNat + n_ant.toNat ≤ (scr[4207]?.getD 0#32).toNat)
    (hle : 15744 ≤ scr.length) :
    let scr1 := scr.set 4206 (alen + lsz + n_ant)
    let scr2 := scr1.set (11648 + nc_old.toNat) alen
    let scr3 := scr2.set (12672 + nc_old.toNat) (lsz ||| 0x40000000#32)
    let scr4 := scr3.set (13696 + nc_old.toNat) n_ant
    let scr5 := scr4.set 4193 (nc_old + 1#32)
    M8AnaPost scr0 scr5 := by
  intro scr1 scr2 scr3 scr4 scr5
  have hok := hk.1
  have hnc1 : (nc_old + 1#32).toNat = nc_old.toNat + 1 := m8_bv32_add1_toNat hnc_lt (by omega)
  have hal_lt : alen.toNat + lsz.toNat + n_ant.toNat < 2 ^ 32 := by
    have := hok.length_ge; have := hok.length_lt; omega
  have hal_add : (alen + lsz + n_ant).toNat = alen.toNat + lsz.toNat + n_ant.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hlen5 : scr5.length = scr.length := by simp [scr5, scr4, scr3, scr2, scr1, List.length_set]
  have hne5 : ∀ idx, idx ≠ 4193 → idx ≠ 4206 → idx ≠ 11648 + nc_old.toNat →
      idx ≠ 12672 + nc_old.toNat → idx ≠ 13696 + nc_old.toNat → scr5[idx]? = scr[idx]? := by
    intro idx h1 h2 h3 h4 h5
    dsimp only [scr5, scr4, scr3, scr2, scr1]
    rw [List.getElem?_set_ne (Ne.symm h1), List.getElem?_set_ne (Ne.symm h5),
      List.getElem?_set_ne (Ne.symm h4), List.getElem?_set_ne (Ne.symm h3),
      List.getElem?_set_ne (Ne.symm h2)]
  have hk1 : scr5[4193]? = some (nc_old + 1#32) := by
    dsimp only [scr5, scr4, scr3, scr2, scr1]
    apply List.getElem?_set_self; simp [List.length_set]; omega
  have hk14 : scr5[4206]? = some (alen + lsz + n_ant) := by
    dsimp only [scr5, scr4, scr3, scr2, scr1]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    apply List.getElem?_set_self; omega
  have hk15 : scr5[4207]? = scr[4207]? :=
    hne5 4207 (by omega) (by omega) (by omega) (by omega) (by omega)
  have hok5 : M8K6BufOk scr5 := by
    refine M8K6BufOk.mk_of (by rw [hlen5, hk15]; exact hok.length_ge)
      (by rw [hlen5]; exact hok.length_lt)
      (by rw [hk1, Option.getD_some, hnc1]; omega)
      (by rw [hk14, hk15, Option.getD_some, hal_add]; exact hfit) fun cid hcid => ?_
    rw [hk1, Option.getD_some, hnc1] at hcid
    by_cases hcur : cid = nc_old.toNat
    · subst hcur
      have ho_c : scr5[11648 + nc_old.toNat]? = some alen := by
        dsimp only [scr5, scr4, scr3, scr2, scr1]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega)]
        apply List.getElem?_set_self; simp [List.length_set]; omega
      have hm_c : scr5[12672 + nc_old.toNat]? = some (lsz ||| 0x40000000#32) := by
        dsimp only [scr5, scr4, scr3, scr2, scr1]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        apply List.getElem?_set_self; simp [List.length_set]; omega
      have ha_c : scr5[13696 + nc_old.toNat]? = some n_ant := by
        dsimp only [scr5, scr4, scr3, scr2, scr1]
        rw [List.getElem?_set_ne (by omega)]
        apply List.getElem?_set_self; simp [List.length_set]; omega
      have hsz_msk := m8k6_or_lrn_and_ffff (lsz := lsz) (by omega)
      rw [ho_c, hm_c, ha_c]
      refine ⟨?_, fun _ => ?_⟩
      · show alen.toNat + ((lsz ||| 0x40000000#32) &&& 0xFFFF#32).toNat ≤
            (scr5[4207]?.getD 0#32).toNat
        rw [hsz_msk, hk15]; omega
      · show alen.toNat + ((lsz ||| 0x40000000#32) &&& 0xFFFF#32).toNat + n_ant.toNat ≤
            (scr5[4207]?.getD 0#32).toNat
        rw [hsz_msk, hk15]; omega
    · have hcid_lt : cid < (scr[4193]?.getD 0#32).toNat := by rw [hnc_eq]; omega
      have ho_c : scr5[11648 + cid]? = scr[11648 + cid]? :=
        hne5 (11648 + cid) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hm_c : scr5[12672 + cid]? = scr[12672 + cid]? :=
        hne5 (12672 + cid) (by omega) (by omega) (by omega) (by omega) (by omega)
      have ha_c : scr5[13696 + cid]? = scr[13696 + cid]? :=
        hne5 (13696 + cid) (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [ho_c, hm_c, ha_c, hk15]; exact hok.clause_ok hcid_lt
  have h4193_0 : scr[4193]? = scr0[4193]? := hk.2.2.1 4193 (by decide)
  refine ⟨hok5, hlen5.trans hk.2.1,
    fun i hi => (hne5 i (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (hk.2.2.1 i (by omega)),
    (hne5 4194 (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (hk.2.2.1 4194 (by decide)),
    by rw [← h4193_0, hnc_eq, hk1, Option.getD_some, hnc1]; omega,
    fun cid hcid => by
      rw [← h4193_0, hnc_eq] at hcid
      exact (hne5 (13696 + cid) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        (hk.2.2.2.2.2.2.2.2.2 (13696 + cid) (by omega) (by omega)),
    (hne5 4199 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hk.2.2.2.1,
    (hne5 4205 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hk.2.2.2.2.1,
    hk15.trans hk.2.2.2.2.2.2.1,
    (hne5 4211 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hk.2.2.2.2.2.2.2.1,
    (hne5 4213 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hk.2.2.2.2.2.2.2.2.1,
    fun i h1 h2 => (hne5 i (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (hk.2.2.2.2.2.2.2.2.2 i (by omega) h2)⟩

/-- Solve-loop invariant preserving `M8K6BufOk`, length, `[0..4193)`, `4194`, `4207`,
monotonic `4193`, and `KO_CL_AUX` for all `cid < orig_nc`. -/
private def M8SolveKeep (scr0 scr : List (BitVec 32)) : Prop :=
  M8K6BufOk scr ∧ scr.length = scr0.length ∧
  (∀ i < 4193, scr[i]? = scr0[i]?) ∧
  scr[4194]? = scr0[4194]? ∧
  scr[4207]? = scr0[4207]? ∧
  (scr0[4193]?.getD 0#32).toNat ≤ (scr[4193]?.getD 0#32).toNat ∧
  (∀ cid < (scr0[4194]?.getD 0#32).toNat, scr[13696 + cid]? = scr0[13696 + cid]?)

private theorem m8SolveKeep_refl {scr0 : List (BitVec 32)} (h : M8K6BufOk scr0) :
    M8SolveKeep scr0 scr0 :=
  ⟨h, rfl, fun _ _ => rfl, rfl, rfl, Nat.le_refl _, fun _ _ => rfl⟩

private theorem m8SolveKeep_of_set_lo {scr0 scr : List (BitVec 32)} (hs : M8SolveKeep scr0 scr)
    (idx : Nat) (v : BitVec 32)
    (hlo : 4195 ≤ idx) (hhi : idx < 11648) (h206 : idx ≠ 4206) (h207 : idx ≠ 4207) :
    M8SolveKeep scr0 (scr.set idx v) := by
  have hok : M8K6BufOk (scr.set idx v) :=
    m8K6BufOk_of_frame hs.1 List.length_set fun i _ hor => by
      rcases hor with rfl | rfl | rfl | ⟨ha, hb⟩ <;> exact List.getElem?_set_ne (by omega)
  refine ⟨hok, List.length_set.trans hs.2.1,
    fun i hi => (List.getElem?_set_ne (by omega)).trans (hs.2.2.1 i hi),
    (List.getElem?_set_ne (by omega)).trans hs.2.2.2.1,
    (List.getElem?_set_ne (by omega)).trans hs.2.2.2.2.1,
    by rw [List.getElem?_set_ne (by omega)]; exact hs.2.2.2.2.2.1,
    fun cid hcid => (List.getElem?_set_ne (by omega)).trans (hs.2.2.2.2.2.2 cid hcid)⟩

private theorem m8SolveKeep_of_backtrack {scr0 scr scr' : List (BitVec 32)}
    (hs : M8SolveKeep scr0 scr)
    (honc : (scr0[4194]?.getD 0#32).toNat ≤ (scr0[4193]?.getD 0#32).toNat)
    (hlen : scr'.length = scr.length)
    (hkeep : ∀ idx < scr.length,
      (idx < 4195 ∨ (4199 ≤ idx ∧ idx < 4224) ∨ (4736 ≤ idx ∧ idx < 6528) ∨ 7040 ≤ idx) →
      scr'[idx]? = scr[idx]?) :
    M8SolveKeep scr0 scr' := by
  have hb := hs.1.base_ge
  have honc_le : (scr0[4194]?.getD 0#32).toNat ≤ 1024 :=
    Nat.le_trans honc (Nat.le_trans hs.2.2.2.2.2.1 hs.1.nc_le)
  have hok := m8K6BufOk_of_frame hs.1 hlen fun idx _ hor => by
    rcases hor with rfl | rfl | rfl | ⟨ha, hb'⟩
    · exact hkeep 4193 (by omega) (Or.inl (by decide))
    · exact hkeep 4206 (by omega) (Or.inr (Or.inl ⟨by decide, by decide⟩))
    · exact hkeep 4207 (by omega) (Or.inr (Or.inl ⟨by decide, by decide⟩))
    · exact hkeep idx (by omega) (Or.inr (Or.inr (Or.inr (by omega))))
  refine ⟨hok, hlen.trans hs.2.1,
    fun i hi => (hkeep i (by omega) (Or.inl (by omega))).trans (hs.2.2.1 i hi),
    (hkeep 4194 (by omega) (Or.inl (by decide))).trans hs.2.2.2.1,
    (hkeep 4207 (by omega) (Or.inr (Or.inl ⟨by decide, by decide⟩))).trans hs.2.2.2.2.1,
    by rw [hkeep 4193 (by omega) (Or.inl (by decide))]; exact hs.2.2.2.2.2.1,
    fun cid hcid => (hkeep (13696 + cid) (by omega) (Or.inr (Or.inr (Or.inr (by omega))))).trans
      (hs.2.2.2.2.2.2 cid hcid)⟩

private theorem m8SolveKeep_of_assign {scr0 scr scr' : List (BitVec 32)}
    (hs : M8SolveKeep scr0 scr)
    (honc : (scr0[4194]?.getD 0#32).toNat ≤ (scr0[4193]?.getD 0#32).toNat)
    (hlen : scr'.length = scr.length)
    (hkeep : ∀ idx < scr.length, idx ≠ 4197 → idx ≠ 4198 →
      (idx < 4224 ∨ 4736 ≤ idx) → (idx < 5504 ∨ 6016 ≤ idx) →
      (idx < 6528 ∨ 7040 ≤ idx) → scr'[idx]? = scr[idx]?) :
    M8SolveKeep scr0 scr' := by
  have hb := hs.1.base_ge
  have honc_le : (scr0[4194]?.getD 0#32).toNat ≤ 1024 :=
    Nat.le_trans honc (Nat.le_trans hs.2.2.2.2.2.1 hs.1.nc_le)
  have hat : ∀ i, i < 4224 → i ≠ 4197 → i ≠ 4198 → scr'[i]? = scr[i]? :=
    fun i hi h7 h8 => hkeep i (by omega) h7 h8 (Or.inl hi) (Or.inl (by omega)) (Or.inl (by omega))
  have hhi : ∀ i, 11648 ≤ i → i < 14720 → scr'[i]? = scr[i]? :=
    fun i h1 h2 => hkeep i (by omega) (by omega) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  have hok := m8K6BufOk_of_frame hs.1 hlen fun idx _ hor => by
    rcases hor with rfl | rfl | rfl | ⟨ha, hb'⟩
    · exact hat 4193 (by decide) (by decide) (by decide)
    · exact hat 4206 (by decide) (by decide) (by decide)
    · exact hat 4207 (by decide) (by decide) (by decide)
    · exact hhi idx ha hb'
  refine ⟨hok, hlen.trans hs.2.1,
    fun i hi => (hat i (by omega) (by omega) (by omega)).trans (hs.2.2.1 i hi),
    (hat 4194 (by decide) (by decide) (by decide)).trans hs.2.2.2.1,
    (hat 4207 (by decide) (by decide) (by decide)).trans hs.2.2.2.2.1,
    by rw [hat 4193 (by decide) (by decide) (by decide)]; exact hs.2.2.2.2.2.1,
    fun cid hcid => (hhi (13696 + cid) (by omega) (by omega)).trans (hs.2.2.2.2.2.2 cid hcid)⟩

private theorem m8SolveKeep_of_prop {scr0 scr scr' : List (BitVec 32)}
    (hs : M8SolveKeep scr0 scr)
    (honc : (scr0[4194]?.getD 0#32).toNat ≤ (scr0[4193]?.getD 0#32).toNat)
    (hok : M8K6BufOk scr') (hlen : scr'.length = scr.length)
    (hlo : ∀ i < 4195, scr'[i]? = scr[i]?)
    (h205 : ∀ i, 4205 ≤ i → i < 4224 → scr'[i]? = scr[i]?)
    (hhi : ∀ i, 11648 ≤ i → i < 15744 → scr'[i]? = scr[i]?) :
    M8SolveKeep scr0 scr' := by
  have honc_le : (scr0[4194]?.getD 0#32).toNat ≤ 1024 :=
    Nat.le_trans honc (Nat.le_trans hs.2.2.2.2.2.1 hs.1.nc_le)
  exact ⟨hok, hlen.trans hs.2.1,
    fun i hi => (hlo i (by omega)).trans (hs.2.2.1 i hi),
    (hlo 4194 (by decide)).trans hs.2.2.2.1,
    (h205 4207 (by decide) (by decide)).trans hs.2.2.2.2.1,
    by rw [hlo 4193 (by decide)]; exact hs.2.2.2.2.2.1,
    fun cid hcid => (hhi (13696 + cid) (by omega) (by omega)).trans (hs.2.2.2.2.2.2 cid hcid)⟩

private theorem m8SolveKeep_of_analyze {scr0 scr scr' : List (BitVec 32)}
    (hs : M8SolveKeep scr0 scr)
    (honc : (scr0[4194]?.getD 0#32).toNat ≤ (scr0[4193]?.getD 0#32).toNat)
    (hok : M8K6BufOk scr') (hlen : scr'.length = scr.length)
    (hlo : ∀ i < 4193, scr'[i]? = scr[i]?)
    (h4194 : scr'[4194]? = scr[4194]?)
    (hnc : (scr[4193]?.getD 0#32).toNat ≤ (scr'[4193]?.getD 0#32).toNat)
    (haux : ∀ cid < (scr[4193]?.getD 0#32).toNat, scr'[13696 + cid]? = scr[13696 + cid]?)
    (h4207 : scr'[4207]? = scr[4207]?) :
    M8SolveKeep scr0 scr' :=
  ⟨hok, hlen.trans hs.2.1,
    fun i hi => (hlo i hi).trans (hs.2.2.1 i hi),
    h4194.trans hs.2.2.2.1,
    h4207.trans hs.2.2.2.2.1,
    Nat.le_trans hs.2.2.2.2.2.1 hnc,
    fun cid hcid => (haux cid (Nat.lt_of_lt_of_le hcid (Nat.le_trans honc hs.2.2.2.2.2.1))).trans
      (hs.2.2.2.2.2.2 cid hcid)⟩

private theorem m8k6_pick_bounds {scr : List (BitVec 32)} {nv cur : BitVec 32}
    (hlen : 15744 ≤ scr.length) (hnv : nv.toNat ≤ 256) (hcur : cur.toNat < nv.toNat) :
    (BitVec.setWidth 64 ((6528 : BitVec 32) + (cur <<< (1 : Nat)))).toNat < scr.length ∧
    (BitVec.setWidth 64 ((4736 : BitVec 32) + cur)).toNat < scr.length := by
  have hsh : (cur <<< (1 : Nat)).toNat = 2 * cur.toNat := m8_bv32_shl1_toNat (by omega)
  have h6528n : (6528 : BitVec 32).toNat = 6528 := rfl
  have h4736n : (4736 : BitVec 32).toNat = 4736 := rfl
  constructor
  · rw [m8k6_bv64_add2_lt (by rw [h6528n, hsh]; omega), h6528n, hsh]; omega
  · rw [m8k6_bv64_add2_lt (by rw [h4736n]; omega), h4736n]; omega

/-! ## 2. `full_k6_analyze_m8_wp` -/

/-- Certifies `m8K6AnalyzeSpec` for `full_k6_analyze_m8_body`. -/
theorem full_k6_analyze_m8_wp (Γ : Env)
    (hAnaCl : ∀ a m Q X, m8K6AnaClSpec a m Q X →
      Γ "full_k6_ana_cl_m8" [i64, i32, i32] [] a m Q X)
    (hBt : ∀ a m Q X, m8K6BacktrackSpec a m Q X →
      Γ "full_k6_backtrack_m8" [i64, i32] [] a m Q X)
    (hMtf : ∀ a m Q X, m8K6MtfSpec a m Q X →
      Γ "full_k6_mtf_m8" [i64, i32] [] a m Q X)
    (hWatch : ∀ a m Q X, m8K6WatchSpec a m Q X →
      Γ "full_k6_watch_m8" [i64, i32, i32, i32, i32] [] a m Q X)
    (hAssign : ∀ a m Q X, m8K6AssignSpec a m Q X →
      Γ "full_k6_assign_m8" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, m8K6AnalyzeSpec a m Q X →
      Func.wp Γ full_k6_analyze_m8_body a m Q X := by
  rintro ⟨hp, confl_cid, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen0, hsc, hok0, hm0, hQ⟩ := m8K6AnalyzeSpec_elim hSpec
  let scr0 := s.scratch.scratch_buf
  have hscr0_l : scr0.length = c.scratch_cap := hlen0.scratch_ok.scratch_buf_len
  have hbase : 15744 ≤ scr0.length := hok0.base_ge
  have hlt30 : scr0.length < 2 ^ 30 := hok0.length_lt
  have hm0' : (FullMem c (m8ScrSt s scr0) ⋆ R) m0 := by
    simpa only [m8ScrSt_self, scr0] using hm0
  clear hm0
  let nv : BitVec 32 := scr0[4192]'(by omega)
  let nc : BitVec 32 := scr0[4193]'(by omega)
  let acap : BitVec 32 := scr0[4207]'(by omega)
  have hnc_le : nc.toNat ≤ 1024 := by
    simpa [nc, scr0, m8_k6_get_eq (by omega : 4193 < scr0.length)] using hok0.nc_le
  have hretPost : ∀ (ok : Bool) (scr' : List (BitVec 32)) (m' : Mem 64),
      M8AnaPost scr0 scr' → (FullMem c (m8ScrSt s scr') ⋆ R) m' → Q (ok, ()) m' :=
    fun ok scr' m' hp' hm' =>
      hQ ok scr' m' hp'.1 (hp'.2.1.trans hscr0_l) hp'.2.2.1 hp'.2.2.2.1 hp'.2.2.2.2.1
        hp'.2.2.2.2.2.1 hp'.2.2.2.2.2.2.1 hp'.2.2.2.2.2.2.2.1 hp'.2.2.2.2.2.2.2.2.1
        hp'.2.2.2.2.2.2.2.2.2.1 hp'.2.2.2.2.2.2.2.2.2.2.1 hp'.2.2.2.2.2.2.2.2.2.2.2
        (m8ScrSt_eq s scr' ▸ hm')
  unfold Func.wp full_k6_analyze_m8_body
  c0_hsplit
  · c0_hsteps!
    exact hretPost false scr0 m0 (m8AnaKeep_to_post (m8AnaKeep_refl hok0)) hm0'
  · have hnv_le : nv.toNat ≤ 256 := Nat.le_of_not_lt (show ¬256 < nv.toNat from hc)
    clear hc
    have hpk0 := m8AnaKeep_of_set (m8AnaKeep_refl hok0) 4209 1#32 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))
    have hpk1 := m8AnaKeep_of_set hpk0 4208 0#32 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))
    have hpk2 := m8AnaKeep_of_set hpk1 4210 0#32 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))
    have hpk3 := m8AnaKeep_of_set hpk2 4212 0#32 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))
    c0_hsteps_nogrp
    m8k6_call hAnaCl
    dsimp only [vals, Arg.val]
    refine m8K6AnaClSpec_intro rfl (m8ScrSt_lengthsOk hlen0 (hpk3.2.1.trans hscr0_l))
      hsc (by rw [m8ScrSt_buf]; exact hpk3.1) hm ?_
    intro scr4 m4 hlen4 hkeep4 hm4
    rw [m8ScrSt_buf] at hkeep4
    rw [m8ScrSt_upd] at hm4
    have hpk4 := m8AnaKeep_of_ana_cl hpk3 (hlen4.trans (hpk3.2.1.trans hscr0_l).symm)
      (fun idx hi => hkeep4 idx (by rw [hpk3.2.1, hscr0_l] at hi; exact hi))
    have hl4 : 15744 ≤ scr4.length := by rw [hpk4.2.1]; exact hbase
    c0_hsteps_nogrp
    let clvl := scr4[4195]'(by omega)
    refine wp_join_state1 (t := i32)
      (fun st : BitVec 32 × List (BitVec 32) => (st.1 : Val i32))
      (fun (idx, scr) mi =>
        M8AnaKeep scr0 scr ∧ idx.toNat ≤ 256 ∧ (FullMem c (m8ScrSt s scr) ⋆ R) mi)
      ?_ ?_
    · rintro _ ⟨idx0, scri0⟩ mi0 ⟨hki0, hidx0_le, hmi0⟩
      refine wp_while_break_state
        (brkTs := [i32, i32]) (lpTs := [i32])
        (fun st : BitVec 32 × BitVec 32 × List (BitVec 32) => (st.1, st.2.1, ()))
        (fun (_, _, scr) mb => M8AnaKeep scr0 scr ∧ (FullMem c (m8ScrSt s scr) ⋆ R) mb)
        (fun st : BitVec 32 × List (BitVec 32) => (st.1, ()))
        (fun st => st.1.toNat)
        (fun (idx, scr) mi =>
          M8AnaKeep scr0 scr ∧ idx.toNat ≤ 256 ∧ (FullMem c (m8ScrSt s scr) ⋆ R) mi)
        ?_ ?_ ?_
      · rintro _ ⟨_, uip, scrb⟩ mb ⟨hkb, hmb⟩
        have hkb_l := hkb.2.1
        have hkb_l2 : 15744 ≤ scrb.length := by rw [hkb_l]; exact hbase
        c0_hsteps_nogrp
        refine wp_join_state1 (t := i32)
          (fun st : BitVec 32 × List (BitVec 32) => (st.1 : Val i32))
          (fun (nana, scr) mn =>
            M8AnaKeep scr0 scr ∧ nana.toNat ≤ 256 ∧ (FullMem c (m8ScrSt s scr) ⋆ R) mn)
          ?_ ?_
        · rintro _ ⟨nana, scrc⟩ mc ⟨hkc, hnana_le, hmc⟩
          refine wp_while_state1 (t := i32)
            (fun st : BitVec 32 × List (BitVec 32) => (st.1 : Val i32))
            (fun st => nana.toNat - st.1.toNat)
            (fun (ai, scr) mi =>
              ai.toNat ≤ nana.toNat ∧ M8AnaKeep scr0 scr ∧ (FullMem c (m8ScrSt s scr) ⋆ R) mi)
            ?_ ?_
          · intro L2 hL2
            c0_hsteps!
            exact hL2 (0#32, scrc) mc ⟨Nat.zero_le _, hkc, hmc⟩
          · rintro _ ⟨ai, scrd⟩ md ⟨hai_le, hkd, hmd⟩ ih2
            have hkd_l := hkd.2.1
            have hkd_l2 : 15744 ≤ scrd.length := by rw [hkd_l]; exact hbase
            have hret_false : Q (false, ()) md :=
              hretPost false scrd md (m8AnaKeep_to_post hkd) hmd
            c0_hsteps_nogrp
            · have hai_lt : ai.toNat < nana.toNat := hc
              have hai1_eq : (ai + 1#32).toNat = ai.toNat + 1 :=
                m8_bv32_add1_toNat hai_lt (by omega)
              have h6016n : (6016#32).toNat = 6016 := rfl
              have h6016_nat : (BitVec.setWidth 64 (6016#32 + ai)).toNat = 6016 + ai.toNat := by
                rw [m8k6_bv64_add2_lt (by rw [h6016n]; omega), h6016n]
              have h6016_bd : (BitVec.setWidth 64 (6016#32 + ai)).toNat < scrd.length := by
                rw [h6016_nat]; omega
              refine wp_join0 (fun mj => ∃ scrj, M8AnaKeep scr0 scrj ∧
                  (FullMem c (m8ScrSt s scrj) ⋆ R) mj) ?_ ?_
              · intro _ mj ⟨scrj, hkj, hmj⟩
                c0_hsteps!
                exact ih2 (ai + 1#32, scrj) mj (by dsimp only; rw [hai1_eq]; omega)
                  ⟨by rw [hai1_eq]; omega, hkj, hmj⟩
              · intro _ hJ2
                c0_hsplit
                · let av := scrd[(BitVec.setWidth 64 (6016#32 + ai)).toNat]'h6016_bd
                  have hav_lt : av.toNat < nv.toNat := by
                    have hidx : (6016 + ai.toNat) % 4294967296 =
                        (BitVec.setWidth 64 (6016#32 + ai)).toNat := by rw [h6016_nat]; omega
                    have hav' : scrd[(6016 + ai.toNat) % 4294967296]'(by
                        rw [hidx]; exact h6016_bd) = av := m8_k6_get_congr hidx _ h6016_bd
                    simpa [nv, hav'] using hc
                  clear hc
                  have h5760n : (5760#32).toNat = 5760 := rfl
                  have h5760_nat : (BitVec.setWidth 64 (5760#32 + av)).toNat =
                      5760 + av.toNat := by
                    rw [m8k6_bv64_add2_lt (by rw [h5760n]; omega), h5760n]
                  have h5760_bd : (BitVec.setWidth 64 (5760#32 + av)).toNat < scrd.length := by
                    rw [h5760_nat]; omega
                  c0_hsteps!
                  exact hJ2 m ⟨_, m8AnaKeep_of_set hkd (BitVec.setWidth 64 (5760#32 + av)).toNat _
                    (by rw [h5760_nat]; omega) (by rw [h5760_nat]; omega) (by rw [h5760_nat]; omega)
                    (by rw [h5760_nat]; omega) (by rw [h5760_nat]; omega) (by rw [h5760_nat]; omega)
                    (by rw [h5760_nat]; omega) (Or.inl (by rw [h5760_nat]; omega)), hm⟩
                · clear hc
                  c0_hsteps!
                  exact hJ2 md ⟨scrd, hkd, hmd⟩
            · exact hret_false
            · exact hret_false
            · exact hret_false
            · exact hret_false
            · exact hret_false
            · let nres := scrd[4210]'(by omega)
              let nkl := scrd[4209]'(by omega)
              have hnres_le : nres.toNat ≤ 512 := by
                have hnot : ¬512 < (scrd[4210]'(by omega)).toNat := by assumption
                exact Nat.le_of_not_lt hnot
              have hnkl_pos : 0 < nkl.toNat := by
                have hnot : ¬(scrd[4209]'(by omega)) = 0#32 := by assumption
                exact Nat.pos_of_ne_zero fun h =>
                  hnot (BitVec.eq_of_toNat_eq (by simpa using h))
              have hnkl_le : nkl.toNat ≤ 256 := by
                have hnot : ¬256 < (scrd[4209]'(by omega)).toNat := by assumption
                exact Nat.le_of_not_lt hnot
              have hpk_kl0 := m8AnaKeep_of_set hkd 6272 uip (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))
              have hkl0_len : 15744 ≤ (scrd.set 6272 uip).length := by
                rw [hpk_kl0.2.1]; exact hbase
              focus
                refine wp_while_state_pure
                  (ts := [i32, i32, i32])
                  (fun st : BitVec 32 × BitVec 32 × BitVec 32 => (st.1, st.2.1, st.2.2, ()))
                  (fun st => nkl.toNat - st.2.2.toNat)
                  (fun (jlvl, wi, i) =>
                    1 ≤ wi.toNat ∧ wi.toNat ≤ 256 ∧
                    (wi.toNat < nkl.toNat ∨ (nkl.toNat = 1 ∧ wi = 1#32)) ∧
                    1 ≤ i.toNat ∧ i.toNat ≤ nkl.toNat)
                  ?_ ?_
                · intro L3 hL3
                  c0_hsteps!
                  have hw_disj :
                      (1 : Nat) < nkl.toNat ∨ (nkl.toNat = 1 ∧ (1#32 : BitVec 32) = 1#32) := by
                    rcases Nat.eq_or_lt_of_le hnkl_pos with h1 | hgt
                    · exact Or.inr ⟨h1.symm, rfl⟩
                    · exact Or.inl hgt
                  exact hL3 (0#32, 1#32, 1#32) ⟨by decide, by decide, hw_disj, by decide, hnkl_pos⟩
                · rintro L3 ⟨jlvl, wi, i⟩ ⟨hwi_ge, hwi_256, hwi_disj, hi_ge, hi_le⟩ ih3
                  c0_hsplit
                  · have hi_lt : i.toNat < nkl.toNat := hc
                    clear hc
                    have h6272n : (6272#32).toNat = 6272 := rfl
                    have h6272_nat : (BitVec.setWidth 64 (6272#32 + i)).toNat = 6272 + i.toNat := by
                      rw [m8k6_bv64_add2_lt (by rw [h6272n]; omega), h6272n]
                    have h6272_bd :
                        (BitVec.setWidth 64 (6272#32 + i)).toNat < (scrd.set 6272 uip).length := by
                      rw [h6272_nat, hpk_kl0.2.1]; omega
                    have hi1_eq : (i + 1#32).toNat = i.toNat + 1 :=
                      m8_bv32_add1_toNat hi_lt (by omega)
                    c0_hsteps_nogrp
                    refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
                      (fun st => (st.1, st.2, ()))
                      (fun (j', w') => 1 ≤ w'.toNat ∧ w'.toNat ≤ 256 ∧
                        (w'.toNat < nkl.toNat ∨ (nkl.toNat = 1 ∧ w' = 1#32)))
                      (fun _ (j', w') hgw => by
                        c0_hsteps!
                        exact ih3 (j', w', i + 1#32) (by dsimp only; rw [hi1_eq]; omega)
                          ⟨hgw.1, hgw.2.1, hgw.2.2, by rw [hi1_eq]; omega, by rw [hi1_eq]; omega⟩)
                      (fun _ hJ3a => by
                        c0_hsplit
                        · let kv := ((scrd.set 6272 uip)[(BitVec.setWidth 64
                            (6272#32 + i)).toNat]'h6272_bd) >>> (1 : Nat)
                          have hkv_bd : kv.toNat < nv.toNat := by
                            have hidx : (6272 + i.toNat) % 4294967296 =
                                (BitVec.setWidth 64 (6272#32 + i)).toNat := by
                              rw [h6272_nat]; omega
                            have hkv' : (scrd.set 6272 uip)[(6272 + i.toNat) % 4294967296]'(by
                                rw [hidx]; exact h6272_bd) =
                                (scrd.set 6272 uip)[(BitVec.setWidth 64
                                  (6272#32 + i)).toNat]'h6272_bd :=
                              m8_k6_get_congr hidx _ h6272_bd
                            have hsh : kv.toNat = ((scrd.set 6272 uip)[(BitVec.setWidth 64
                                (6272#32 + i)).toNat]'h6272_bd).toNat / 2 := bv32_lshr_1 _
                            rw [hsh, ← hkv']; simpa [nv] using hc
                          clear hc
                          have h4224n : (4224#32).toNat = 4224 := rfl
                          have h4224_bd : (BitVec.setWidth 64 (4224#32 + kv)).toNat <
                              (scrd.set 6272 uip).length := by
                            rw [m8k6_bv64_add2_lt (by rw [h4224n]; omega), h4224n, hpk_kl0.2.1]
                            omega
                          c0_hsteps_nogrp
                          refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
                            (fun st => (st.1, st.2, ()))
                            (fun (j', w') => 1 ≤ w'.toNat ∧ w'.toNat ≤ 256 ∧
                              (w'.toNat < nkl.toNat ∨ (nkl.toNat = 1 ∧ w' = 1#32)))
                            (fun _ (j', w') hgw => by c0_hsteps!; exact hJ3a (j', w') hgw)
                            (fun _ hJ3b => by
                              c0_hsplit
                              · c0_hsteps!; exact hJ3b (_, i) ⟨hi_ge, by omega, Or.inl hi_lt⟩
                              · c0_hsteps!; exact hJ3b (jlvl, wi) ⟨hwi_ge, hwi_256, hwi_disj⟩)
                        · clear hc; c0_hsteps!; exact hJ3a (jlvl, wi) ⟨hwi_ge, hwi_256, hwi_disj⟩)
                  · clear hc
                    refine wp_join0 (fun msw => ∃ scrsw, M8AnaKeep scr0 scrsw ∧
                        (FullMem c (m8ScrSt s scrsw) ⋆ R) msw) ?_ ?_
                    · intro _ msw ⟨scrsw, hksw, hmsw⟩
                      have hksw_l := hksw.2.1
                      have hksw_l2 : 15744 ≤ scrsw.length := by rw [hksw_l]; exact hbase
                      c0_hsteps_nogrp
                      m8k6_call hBt
                      dsimp only [vals, Arg.val]
                      refine m8K6BacktrackSpec_intro rfl
                        (m8ScrSt_lengthsOk hlen0 (hksw_l.trans hscr0_l)) hsc hmsw ?_
                      intro scrb' mbb hlenb hkeepb hmbb
                      rw [m8ScrSt_buf] at hkeepb
                      rw [m8ScrSt_upd] at hmbb
                      have hkpb := m8AnaKeep_of_backtrack hksw
                        (hlenb.trans (hksw_l.trans hscr0_l).symm)
                        (fun idx hi => hkeepb idx (by rw [hksw_l, hscr0_l] at hi; exact hi))
                      have hkpb_l := hkpb.2.1
                      have hkpb_l2 : 15744 ≤ scrb'.length := by rw [hkpb_l]; exact hbase
                      refine wp_while_state1 (t := i32)
                        (fun st : BitVec 32 × List (BitVec 32) => (st.1 : Val i32))
                        (fun st => nana.toNat - st.1.toNat)
                        (fun (ai, scrm) mm =>
                          ai.toNat ≤ nana.toNat ∧ M8AnaKeep scr0 scrm ∧
                          (FullMem c (m8ScrSt s scrm) ⋆ R) mm)
                        ?_ ?_
                      · intro L4 hL4
                        c0_hsteps!
                        exact hL4 (0#32, scrb') mbb ⟨Nat.zero_le _, hkpb, hmbb⟩
                      · rintro L4 ⟨ai, scrm⟩ mm ⟨hai_le, hkbm, hmm⟩ ih4
                        have hkbm_l := hkbm.2.1
                        have hkbm_l2 : 15744 ≤ scrm.length := by rw [hkbm_l]; exact hbase
                        c0_hsplit
                        · have hai_lt : ai.toNat < nana.toNat := hc
                          clear hc
                          have hai1_eq : (ai + 1#32).toNat = ai.toNat + 1 :=
                            m8_bv32_add1_toNat hai_lt (by omega)
                          have h6016n : (6016#32).toNat = 6016 := rfl
                          have h6016_bd : (BitVec.setWidth 64 (6016#32 + ai)).toNat <
                              scrm.length := by
                            rw [m8k6_bv64_add2_lt (by rw [h6016n]; omega), h6016n]; omega
                          c0_hsteps_nogrp
                          m8k6_call hMtf
                          dsimp only [vals, Arg.val]
                          refine m8K6MtfSpec_intro rfl
                            (m8ScrSt_lengthsOk hlen0 (hkbm_l.trans hscr0_l)) hsc hmm ?_
                          intro scrm' mm' hlenm hkeepm hmm'
                          rw [m8ScrSt_buf] at hkeepm
                          rw [m8ScrSt_upd] at hmm'
                          c0_hsteps!
                          exact ih4 (ai + 1#32, scrm') mm' (by dsimp only; rw [hai1_eq]; omega)
                            ⟨by rw [hai1_eq]; omega,
                              m8AnaKeep_of_mtf hkbm (hlenm.trans (hkbm_l.trans hscr0_l).symm)
                                (fun idx hi => hkeepm idx (by
                                  rw [hkbm_l, hscr0_l] at hi; exact hi)),
                              hmm'⟩
                        · clear hc
                          have hkbm_ok := hkbm.1
                          have hbm_ge := hkbm_ok.base_ge
                          have hbm_lt30 := hkbm_ok.length_lt
                          have hscrm15 : scrm[4207]'(by omega) = acap :=
                            m8_k6_elem_of_opt hkbm.2.2.2.2.2.2.1 (by omega) (by omega)
                          have hscrm1 : scrm[4193]'(by omega) = nc :=
                            m8_k6_elem_of_opt (hkbm.2.2.1 4193 (by decide)) (by omega) (by omega)
                          have hbm_cap : 15744 + acap.toNat ≤ scrm.length := by
                            simpa [hscrm15, m8_k6_get_eq (by omega : 4207 < scrm.length)] using
                              hkbm_ok.length_ge
                          let alen_m := scrm[4206]'(by omega)
                          have halen_le : alen_m.toNat ≤ acap.toNat := by
                            simpa [alen_m, hscrm15, m8_k6_get_eq (by omega : 4206 < scrm.length),
                              m8_k6_get_eq (by omega : 4207 < scrm.length)] using hkbm_ok.alen_le
                          have hret_false_m : Q (false, ()) mm :=
                            hretPost false scrm mm (m8AnaKeep_to_post hkbm) hmm
                          c0_hsplit
                          · c0_hsteps!
                            exact hret_false_m
                          · have hnc_lt1024 : (scrm[4193]'(by omega)).toNat < 1024 := by
                              have h1024n : (1024#32 : BitVec 32).toNat = 1024 := rfl
                              have hnot : ¬(1024#32 : BitVec 32).toNat ≤
                                  (scrm[4193]'(by omega)).toNat := hc
                              omega
                            clear hc
                            c0_hsplit
                            · c0_hsteps!
                              exact hret_false_m
                            · have hfit : alen_m.toNat + nkl.toNat + nres.toNat ≤ acap.toNat := by
                                have hlt_a : alen_m.toNat + nkl.toNat + nres.toNat < 2 ^ 32 := by
                                  omega
                                have h1 : (alen_m.toNat + nkl.toNat) % 2 ^ 32 =
                                    alen_m.toNat + nkl.toNat := Nat.mod_eq_of_lt (by omega)
                                have h2 : (alen_m.toNat + nkl.toNat + nres.toNat) % 2 ^ 32 =
                                    alen_m.toNat + nkl.toNat + nres.toNat := Nat.mod_eq_of_lt hlt_a
                                have hnot : ¬acap.toNat < ((alen_m.toNat + nkl.toNat) % 2 ^ 32 +
                                    nres.toNat) % 2 ^ 32 := by
                                  simpa [alen_m, nkl, nres, hscrm15] using hc
                                rw [h1, h2] at hnot; omega
                              clear hc
                              c0_hsteps_nogrp
                              refine wp_while_state1 (t := i32)
                                (fun st : BitVec 32 × List (BitVec 32) => (st.1 : Val i32))
                                (fun st => nkl.toNat - st.1.toNat)
                                (fun (ci, scrc5) mc5 =>
                                  ci.toNat ≤ nkl.toNat ∧ M8AnaKeep scr0 scrc5 ∧
                                  (FullMem c (m8ScrSt s scrc5) ⋆ R) mc5)
                                ?_ ?_
                              · intro L5 hL5
                                c0_hsteps!
                                exact hL5 (0#32, scrm) mm ⟨Nat.zero_le _, hkbm, hmm⟩
                              · rintro L5 ⟨ci, scrc5⟩ mc5 ⟨hci_le, hkc5, hmc5⟩ ih5
                                have hkc5_l := hkc5.2.1
                                have hkc5_l2 : 15744 ≤ scrc5.length := by rw [hkc5_l]; exact hbase
                                c0_hsplit
                                · have hci_lt : ci.toNat < nkl.toNat := hc
                                  clear hc
                                  have hci1_eq : (ci + 1#32).toNat = ci.toNat + 1 :=
                                    m8_bv32_add1_toNat hci_lt (by omega)
                                  have h6272n : (6272 : BitVec 32).toNat = 6272 := rfl
                                  have h6272_bd :
                                      (BitVec.setWidth 64 ((6272 : BitVec 32) + ci)).toNat <
                                      scrc5.length := by
                                    rw [m8k6_bv64_add2_lt (by rw [h6272n]; omega), h6272n]; omega
                                  have h15744n : (15744 : BitVec 32).toNat = 15744 := rfl
                                  have h15744_a : ((15744 : BitVec 32) + alen_m).toNat =
                                      15744 + alen_m.toNat := by
                                    rw [BitVec.toNat_add, h15744n, Nat.mod_eq_of_lt (by omega)]
                                  have hdst_nat :
                                      (BitVec.setWidth 64
                                        ((15744 : BitVec 32) + alen_m + ci)).toNat =
                                      15744 + alen_m.toNat + ci.toNat := by
                                    rw [m8k6_bv64_add2_lt (by rw [h15744_a]; omega), h15744_a]
                                  have hdst_bd :
                                      (BitVec.setWidth 64
                                        ((15744 : BitVec 32) + alen_m + ci)).toNat <
                                      scrc5.length := by
                                    rw [hdst_nat]; omega
                                  c0_hsteps!
                                  let v5 := scrc5[(BitVec.setWidth 64
                                    ((6272 : BitVec 32) + ci)).toNat]'h6272_bd
                                  have hkc5' := m8AnaKeep_of_set hkc5
                                    (BitVec.setWidth 64
                                      ((15744 : BitVec 32) + alen_m + ci)).toNat v5
                                    (by rw [hdst_nat]; omega) (by rw [hdst_nat]; omega)
                                    (by rw [hdst_nat]; omega) (by rw [hdst_nat]; omega)
                                    (by rw [hdst_nat]; omega) (by rw [hdst_nat]; omega)
                                    (by rw [hdst_nat]; omega) (Or.inr (by rw [hdst_nat]; omega))
                                  exact ih5 (ci + 1#32, _) m (by dsimp only; rw [hci1_eq]; omega)
                                    ⟨by rw [hci1_eq]; omega, hkc5', hm⟩
                                · clear hc
                                  refine wp_while_state1 (t := i32)
                                    (fun st : BitVec 32 × List (BitVec 32) => (st.1 : Val i32))
                                    (fun st => nres.toNat - st.1.toNat)
                                    (fun (ri, scrc6) mc6 =>
                                      ri.toNat ≤ nres.toNat ∧ M8AnaKeep scr0 scrc6 ∧
                                      (FullMem c (m8ScrSt s scrc6) ⋆ R) mc6)
                                    ?_ ?_
                                  · intro L6 hL6
                                    c0_hsteps!
                                    exact hL6 (0#32, scrc5) mc5 ⟨Nat.zero_le _, hkc5, hmc5⟩
                                  · rintro L6 ⟨ri, scrc6⟩ mc6 ⟨hri_le, hkc6, hmc6⟩ ih6
                                    have hkc6_l := hkc6.2.1
                                    have hkc6_l2 : 15744 ≤ scrc6.length := by
                                      rw [hkc6_l]; exact hbase
                                    c0_hsplit
                                    · have hri_lt : ri.toNat < nres.toNat := hc
                                      clear hc
                                      have hri1_eq : (ri + 1#32).toNat = ri.toNat + 1 :=
                                        m8_bv32_add1_toNat hri_lt (by omega)
                                      have h15232n : (15232 : BitVec 32).toNat = 15232 := rfl
                                      have h15232_bd :
                                          (BitVec.setWidth 64 ((15232 : BitVec 32) + ri)).toNat <
                                          scrc6.length := by
                                        rw [m8k6_bv64_add2_lt (by rw [h15232n]; omega), h15232n]
                                        omega
                                      have h15744n : (15744#32).toNat = 15744 := rfl
                                      have h15744_a : (15744#32 + alen_m).toNat =
                                          15744 + alen_m.toNat := by
                                        rw [BitVec.toNat_add, h15744n, Nat.mod_eq_of_lt (by omega)]
                                      have h15744_b : (15744#32 + alen_m + nkl).toNat =
                                          15744 + alen_m.toNat + nkl.toNat := by
                                        rw [BitVec.toNat_add, h15744_a, Nat.mod_eq_of_lt (by omega)]
                                      have hdst_nat : (BitVec.setWidth 64
                                          (15744#32 + alen_m + nkl + ri)).toNat =
                                          15744 + alen_m.toNat + nkl.toNat + ri.toNat := by
                                        rw [m8k6_bv64_add2_lt (by rw [h15744_b]; omega), h15744_b]
                                      have hdst_bd : (BitVec.setWidth 64
                                          (15744#32 + alen_m + nkl + ri)).toNat < scrc6.length := by
                                        rw [hdst_nat]; omega
                                      c0_hsteps!
                                      let v6 := scrc6[(BitVec.setWidth 64
                                        ((15232 : BitVec 32) + ri)).toNat]'h15232_bd
                                      have hkc6' := m8AnaKeep_of_set hkc6
                                        (BitVec.setWidth 64
                                          (15744#32 + alen_m + nkl + ri)).toNat v6
                                        (by rw [hdst_nat]; omega) (by rw [hdst_nat]; omega)
                                        (by rw [hdst_nat]; omega) (by rw [hdst_nat]; omega)
                                        (by rw [hdst_nat]; omega) (by rw [hdst_nat]; omega)
                                        (by rw [hdst_nat]; omega)
                                        (Or.inr (by rw [hdst_nat]; omega))
                                      exact ih6 (ri + 1#32, _) m
                                        (by dsimp only; rw [hri1_eq]; omega)
                                        ⟨by rw [hri1_eq]; omega, hkc6', hm⟩
                                    · clear hc
                                      have hk15_c6 : scrc6[4207]?.getD 0#32 = acap := by
                                        rw [hkc6.2.2.2.2.2.2.1]; exact m8_k6_get_eq (by omega)
                                      have hk1_c6 : scrc6[4193]?.getD 0#32 = nc := by
                                        rw [hkc6.2.2.1 4193 (by decide)]
                                        exact m8_k6_get_eq (by omega)
                                      have hnc_lt1024' : nc.toNat < 1024 := by
                                        rw [← hscrm1]; exact hnc_lt1024
                                      have happ := m8Analyze_append hkc6 hk1_c6
                                        hnc_lt1024' hnkl_le hnres_le
                                        (by rw [hk15_c6]; exact hfit) (by omega)
                                      let scr1 := scrc6.set 4206 (alen_m + nkl + nres)
                                      let scr2 := scr1.set (11648 + nc.toNat) alen_m
                                      let scr3 := scr2.set (12672 + nc.toNat)
                                        (nkl ||| 1073741824#32)
                                      let scr4 := scr3.set (13696 + nc.toNat) nres
                                      let scr5 := scr4.set 4193 (nc + 1#32)
                                      have h11648n : (11648 : BitVec 32).toNat = 11648 := rfl
                                      have h12672n : (12672 : BitVec 32).toNat = 12672 := rfl
                                      have h13696n : (13696 : BitVec 32).toNat = 13696 := rfl
                                      have h11648_nat :
                                          (BitVec.setWidth 64 ((11648 : BitVec 32) + nc)).toNat =
                                          11648 + nc.toNat := by
                                        rw [m8k6_bv64_add2_lt (by rw [h11648n]; omega), h11648n]
                                      have h12672_nat :
                                          (BitVec.setWidth 64 ((12672 : BitVec 32) + nc)).toNat =
                                          12672 + nc.toNat := by
                                        rw [m8k6_bv64_add2_lt (by rw [h12672n]; omega), h12672n]
                                      have h13696_nat :
                                          (BitVec.setWidth 64 ((13696 : BitVec 32) + nc)).toNat =
                                          13696 + nc.toNat := by
                                        rw [m8k6_bv64_add2_lt (by rw [h13696n]; omega), h13696n]
                                      have hlen_scr5 : scr5.length = c.scratch_cap :=
                                        happ.2.1.trans hscr0_l
                                      try clear ih2 ih3 ih4 ih5 ih6 hm4 hmbb hmb hmc hmi0
                                      try clear hmsw hkb hkc hki0 hksw hret_false
                                      try clear hret_false_m
                                      rw [hscrm1]
                                      c0_hsteps_nogrp
                                      · rw [h11648_nat, h12672_nat, h13696_nat] at hm
                                        m8k6_call hAssign
                                        dsimp only [vals, Arg.val]
                                        refine m8K6AssignSpec_intro rfl
                                          (m8ScrSt_lengthsOk hlen0 hlen_scr5) hsc hm ?_
                                        intro scrf mf hlenf hkeepf hmf
                                        rw [m8ScrSt_buf] at hkeepf
                                        rw [m8ScrSt_upd] at hmf
                                        have hp_f := m8AnaPost_of_assign happ
                                          (hlenf.trans hlen_scr5.symm)
                                          (fun idx hi => hkeepf idx (by
                                            rw [hlen_scr5] at hi; exact hi))
                                        c0_hsteps!
                                        exact hretPost true scrf mf hp_f hmf
                                      · rw [h11648_nat, h12672_nat, h13696_nat] at hm
                                        m8k6_call hWatch
                                        dsimp only [vals, Arg.val]
                                        refine m8K6WatchSpec_intro rfl
                                          (m8ScrSt_lengthsOk hlen0 hlen_scr5) hsc hm ?_
                                        intro scrw mw hlenw hkeepw hmw
                                        rw [m8ScrSt_buf] at hkeepw
                                        rw [m8ScrSt_upd] at hmw
                                        have hp_w := m8AnaPost_of_watch happ
                                          (hlenw.trans hlen_scr5.symm)
                                          (fun idx hi => hkeepw idx (by
                                            rw [hlen_scr5] at hi; exact hi))
                                        m8k6_call hAssign
                                        dsimp only [vals, Arg.val]
                                        refine m8K6AssignSpec_intro rfl
                                          (m8ScrSt_lengthsOk hlen0 hlenw) hsc hmw ?_
                                        intro scrf mf hlenf hkeepf hmf
                                        rw [m8ScrSt_buf] at hkeepf
                                        rw [m8ScrSt_upd] at hmf
                                        have hp_f := m8AnaPost_of_assign hp_w
                                          (hlenf.trans hlenw.symm)
                                          (fun idx hi => hkeepf idx (by rw [hlenw] at hi; exact hi))
                                        c0_hsteps!
                                        exact hretPost true scrf mf hp_f hmf
                    · intro Jsw hJsw
                      c0_hsplit
                      · c0_hsplit
                        · have h6272n : (6272 : BitVec 32).toNat = 6272 := rfl
                          have h6273_add :
                              (BitVec.setWidth 64 ((6272 : BitVec 32) + 1)).toNat = 6273 := rfl
                          have h6273_bd : 6273 < (scrd.set 6272 uip).length := by
                            rw [hpk_kl0.2.1]; omega
                          have h6272w_bd :
                              (BitVec.setWidth 64 ((6272 : BitVec 32) + wi)).toNat <
                                (scrd.set 6272 uip).length := by
                            rw [m8k6_bv64_add2_lt (by rw [h6272n]; omega), h6272n, hpk_kl0.2.1]
                            omega
                          have h6272w_nat :
                              (BitVec.setWidth 64 ((6272 : BitVec 32) + wi)).toNat =
                                6272 + wi.toNat := by
                            rw [m8k6_bv64_add2_lt (by rw [h6272n]; omega), h6272n]
                          let wlit := (scrd.set 6272 uip)[(BitVec.setWidth 64
                            ((6272 : BitVec 32) + wi)).toNat]'h6272w_bd
                          let tlit := (scrd.set 6272 uip)[6273]'h6273_bd
                          have hpk_s1 := m8AnaKeep_of_set hpk_kl0 6273 wlit (by decide) (by decide)
                            (by decide) (by decide) (by decide) (by decide) (by decide)
                            (Or.inl (by decide))
                          have hs1_len : 15744 ≤ ((scrd.set 6272 uip).set 6273 wlit).length := by
                            rw [hpk_s1.2.1]; exact hbase
                          c0_hsteps_nogrp
                          have h6273_val : ∀ h, (scrd.set 6272 uip)[(BitVec.setWidth 64
                              ((6272 : BitVec 32) + 1)).toNat]'h = tlit := fun _ => by
                            simp only [tlit, h6273_add]
                          rw [h6273_val, h6273_add] at hm
                          have hpk_s2 := m8AnaKeep_of_set hpk_s1 (6272 + wi.toNat) tlit
                            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                            (by omega) (Or.inl (by omega))
                          rw [← h6272w_nat] at hpk_s2
                          exact hJsw m ⟨_, hpk_s2, hm⟩
                        · c0_hsteps!; exact hJsw _ ⟨_, hpk_kl0, hm⟩
                      · c0_hsteps!; exact hJsw _ ⟨_, hpk_kl0, hm⟩
        · intro Jn hJn
          c0_hsplit
          · c0_hsteps!; exact hJn (256#32, scrb) mb ⟨hkb, by decide, hmb⟩
          · c0_hsteps!
            have hk4208_le : (scrb[4208]'(by omega)).toNat ≤ 256 := by
              have hnot : ¬256 < (scrb[4208]'(by omega)).toNat := by simpa using hc
              exact Nat.le_of_not_lt hnot
            exact hJn (scrb[4208]'(by omega), scrb) mb ⟨hkb, hk4208_le, hmb⟩
      · rintro B L ⟨idx, scri⟩ mi hB ih1 ⟨hki, hidx_le, hmi⟩
        have hki_l := hki.2.1
        have hki_l2 : 15744 ≤ scri.length := by rw [hki_l]; exact hbase
        c0_hsplit
        · clear hc
          c0_hsplit
          · c0_hsteps!
            exact hB (idx, 0xFFFFFFFF#32, scri) mi ⟨hki, hmi⟩
          · have hidx_pos : 0 < idx.toNat :=
              Nat.pos_of_ne_zero fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
            clear hc
            have hidx1_eq : (idx - 1#32).toNat = idx.toNat - 1 := m8_bv32_sub1_toNat hidx_pos
            have h5504n : (5504#32).toNat = 5504 := rfl
            have h5504_nat : (BitVec.setWidth 64 (5504#32 + (idx - 1#32))).toNat =
                5504 + (idx - 1#32).toNat := by
              rw [m8k6_bv64_add2_lt (by rw [h5504n, hidx1_eq]; omega), h5504n]
            have h5504_bd : (BitVec.setWidth 64 (5504#32 + (idx - 1#32))).toNat < scri.length := by
              rw [h5504_nat, hidx1_eq]; omega
            c0_hsteps_nogrp
            let p := scri[(BitVec.setWidth 64 (5504#32 + (idx - 1#32))).toNat]'h5504_bd
            let pv := p >>> (1 : Nat)
            refine wp_join_group
              (fun _ mj => ∃ scrj, M8AnaKeep scr0 scrj ∧ (FullMem c (m8ScrSt s scrj) ⋆ R) mj)
              ?_ ?_
            · rintro _ _ mj ⟨scrj, hkj, hmj⟩
              c0_hsteps!
              exact ih1 (idx - 1#32, scrj) mj (by dsimp only; rw [hidx1_eq]; omega)
                ⟨hkj, by rw [hidx1_eq]; omega, hmj⟩
            · intro J1 hJ1
              c0_hsplit
              · have hpv_lt : pv.toNat < nv.toNat := by
                  have hidx : (5504 + (idx - 1#32).toNat) % 4294967296 =
                      (BitVec.setWidth 64 (5504#32 + (idx - 1#32))).toNat := by
                    rw [h5504_nat, hidx1_eq]; omega
                  have hp' : scri[(5504 + (idx - 1#32).toNat) % 4294967296]'(by
                      rw [hidx]; exact h5504_bd) = p := m8_k6_get_congr hidx _ h5504_bd
                  have hsh : pv.toNat = p.toNat / 2 := bv32_lshr_1 p
                  rw [hsh, ← hp']; simpa [nv] using hc
                clear hc
                have h5760n : (5760#32).toNat = 5760 := rfl
                have h5760_bd : (BitVec.setWidth 64 (5760#32 + pv)).toNat < scri.length := by
                  rw [m8k6_bv64_add2_lt (by rw [h5760n]; omega), h5760n]; omega
                c0_hsplit
                · clear hc
                  have h4224n : (4224#32).toNat = 4224 := rfl
                  have h4224_bd : (BitVec.setWidth 64 (4224#32 + pv)).toNat < scri.length := by
                    rw [m8k6_bv64_add2_lt (by rw [h4224n]; omega), h4224n]; omega
                  c0_hsplit
                  · clear hc
                    let decv := scri[4212]'(by omega) - 1#32
                    have hscri4212_len : 15744 ≤ (scri.set 4212 decv).length := by
                      rw [List.length_set]; exact hki_l2
                    have hpk_dec := m8AnaKeep_of_set hki 4212 decv
                      (by decide) (by decide) (by decide) (by decide) (by decide)
                      (by decide) (by decide) (Or.inl (by decide))
                    c0_hsplit
                    · c0_hsteps!
                      exact hB (idx - 1#32, p ^^^ 1#32, _) m ⟨hpk_dec, hm⟩
                    · clear hc
                      have h4480n : (4480#32).toNat = 4480 := rfl
                      have h4480_bd : (BitVec.setWidth 64 (4480#32 + pv)).toNat <
                          (scri.set 4212 decv).length := by
                        rw [m8k6_bv64_add2_lt (by rw [h4480n]; omega), h4480n]; omega
                      c0_hsplit
                      · c0_hsteps!
                        exact hB (idx - 1#32, p ^^^ 1#32, _) m ⟨hpk_dec, hm⟩
                      · clear hc
                        m8k6_call hAnaCl
                        dsimp only [vals, Arg.val]
                        refine m8K6AnaClSpec_intro rfl
                          (m8ScrSt_lengthsOk hlen0 (hpk_dec.2.1.trans hscr0_l)) hsc
                          (by rw [m8ScrSt_buf]; exact hpk_dec.1) hm ?_
                        intro scra ma hlena hkeepa hma
                        rw [m8ScrSt_buf] at hkeepa
                        rw [m8ScrSt_upd] at hma
                        c0_hsteps!
                        exact hJ1 _ ma ⟨scra,
                          m8AnaKeep_of_ana_cl hpk_dec (hlena.trans (hpk_dec.2.1.trans hscr0_l).symm)
                            (fun idx hi => hkeepa idx (by
                              rw [hpk_dec.2.1, hscr0_l] at hi; exact hi)),
                          hma⟩
                  · clear hc; c0_hsteps!; exact hJ1 _ mi ⟨scri, hki, hmi⟩
                · clear hc; c0_hsteps!; exact hJ1 _ mi ⟨scri, hki, hmi⟩
              · clear hc; c0_hsteps!; exact hJ1 _ mi ⟨scri, hki, hmi⟩
        · clear hc
          c0_hsteps!
          exact hB (idx, 0xFFFFFFFF#32, scri) mi ⟨hki, hmi⟩
      · intro B L _ hL
        c0_hsteps!
        exact hL (idx0, scri0) mi0 ⟨hki0, hidx0_le, hmi0⟩
    · intro J hJ
      c0_hsplit
      · c0_hsteps!
        exact hJ (256#32, scr4) m4 ⟨hpk4, by decide, hm4⟩
      · c0_hsteps!
        have hk4197_le : (scr4[4197]'(by omega)).toNat ≤ 256 := by
          have hnot : ¬256 < (scr4[4197]'(by omega)).toNat := by simpa using hc
          exact Nat.le_of_not_lt hnot
        exact hJ (scr4[4197]'(by omega), scr4) m4 ⟨hpk4, hk4197_le, hm4⟩

/-! ## 3. `full_k6_solve_m8_wp` -/

/-- Certifies `m8K6SolveSpec` for `full_k6_solve_m8_body`. -/
theorem full_k6_solve_m8_wp (Γ : Env)
    (hBt : ∀ a m Q X, m8K6BacktrackSpec a m Q X →
      Γ "full_k6_backtrack_m8" [i64, i32] [] a m Q X)
    (hAssign : ∀ a m Q X, m8K6AssignSpec a m Q X →
      Γ "full_k6_assign_m8" [i64, i32, i32] [] a m Q X)
    (hProp : ∀ a m Q X, m8K6PropSpec a m Q X →
      Γ "full_k6_prop_m8" [i64] [i32] a m Q X)
    (hAnalyze : ∀ a m Q X, m8K6AnalyzeSpec a m Q X →
      Γ "full_k6_analyze_m8" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, m8K6SolveSpec a m Q X →
      Func.wp Γ full_k6_solve_m8_body a m Q X := by
  rintro ⟨hp, tick_lim, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen0, hsc, hok0, honc, hm0, hQ⟩ := m8K6SolveSpec_elim hSpec
  let scr0 := s.scratch.scratch_buf
  have hscr0_l : scr0.length = c.scratch_cap := hlen0.scratch_ok.scratch_buf_len
  have hbase : 15744 ≤ scr0.length := hok0.base_ge
  have hm0' : (FullMem c (m8ScrSt s scr0) ⋆ R) m0 := by
    simpa only [m8ScrSt_self, scr0] using hm0
  clear hm0
  let fuel0 : BitVec 64 := s.core.fuel
  have hfuel0_le : fuel0.toNat ≤ s.core.fuel.toNat := Nat.le_refl _
  have retQ : ∀ (r fuel' : BitVec 64) (scr' : List (BitVec 32)) {m' : Mem 64},
      fuel'.toNat ≤ s.core.fuel.toNat → M8SolveKeep scr0 scr' →
      (FullMem c (m8ScrFuelSt s fuel' scr') ⋆ R) m' → Q (r, ()) m' :=
    fun r fuel' scr' _ hfl' hsk' hm' =>
      hQ r scr' fuel' _ hsk'.1 (hsk'.2.1.trans hscr0_l)
        (fun i hi => hsk'.2.2.1 i (by omega)) hsk'.2.2.2.1
        (Nat.le_trans honc hsk'.2.2.2.2.2.1) hsk'.2.2.2.2.2.2 hfl'
        (m8ScrFuelSt_eq s fuel' scr' ▸ hm')
  have retQ0 : ∀ (r : BitVec 64) (scr' : List (BitVec 32)) {m' : Mem 64},
      M8SolveKeep scr0 scr' → (FullMem c (m8ScrSt s scr') ⋆ R) m' → Q (r, ()) m' :=
    fun r scr' _ hsk' hm' => retQ r fuel0 scr' hfuel0_le hsk' (m8ScrFuelSt_self s scr' ▸ hm')
  unfold Func.wp full_k6_solve_m8_body
  c0_hsteps_nogrp
  m8k6_call hBt
  dsimp only [vals, Arg.val]
  refine m8K6BacktrackSpec_intro rfl (m8ScrSt_lengthsOk hlen0 hscr0_l) hsc hm0' ?_
  intro scr1 m1 hlen1 hkeep1 hm1
  rw [m8ScrSt_buf] at hkeep1
  rw [m8ScrSt_upd] at hm1
  have hs1 := m8SolveKeep_of_backtrack (m8SolveKeep_refl hok0) honc
    (hlen1.trans hscr0_l.symm) (fun idx hi => hkeep1 idx (by rw [hscr0_l] at hi; exact hi))
  have hs1_l : 15744 ≤ scr1.length := by rw [hs1.2.1]; exact hbase
  c0_hsplit
  · c0_hsteps!
    exact retQ0 20#64 scr1 hs1 hm1
  · clear hc
    let scr2 := (scr1.set 4205 tick_lim).set 4204 0#32
    have hs2' := m8SolveKeep_of_set_lo hs1 4205 tick_lim (by decide) (by decide)
      (by decide) (by decide)
    have hs2 := m8SolveKeep_of_set_lo hs2' 4204 0#32 (by decide) (by decide)
      (by decide) (by decide)
    have hs2_l : 15744 ≤ scr2.length := by rw [hs2.2.1]; exact hbase
    let nv := scr2[4192]'(by omega)
    let nc := scr2[4193]'(by omega)
    let acap := scr2[4207]'(by omega)
    let nunits := scr2[4211]'(by omega)
    c0_hsplit
    · c0_hsteps!
      exact retQ0 0#64 scr2 hs2 hm
    · have hnv_le : nv.toNat ≤ 256 := Nat.le_of_not_lt (show ¬256 < nv.toNat from hc)
      clear hc
      c0_hsplit
      · c0_hsteps!
        exact retQ0 0#64 scr2 hs2 hm
      · have hnc_le : nc.toNat ≤ 1024 := Nat.le_of_not_lt (show ¬1024 < nc.toNat from hc)
        clear hc
        c0_hsplit
        · c0_hsteps!
          exact retQ0 0#64 scr2 hs2 hm
        · have hnu_le : nunits.toNat ≤ 512 := Nat.le_of_not_lt (show ¬512 < nunits.toNat from hc)
          clear hc
          refine wp_while_state (ts := [i32])
            (fun st : BitVec 32 × List (BitVec 32) => (st.1, ()))
            (fun st => nunits.toNat - st.1.toNat)
            (fun (ui, scr) mi => ui.toNat ≤ nunits.toNat ∧ M8SolveKeep scr0 scr ∧
              (FullMem c (m8ScrSt s scr) ⋆ R) mi)
            ?_ ?_
          · intro J1 hJ1
            c0_hsteps!
            exact hJ1 (0#32, scr2) m ⟨Nat.zero_le _, hs2, hm⟩
          · rintro J1 ⟨ui, scr⟩ mi ⟨hui_le, hsk, hmi⟩ ih1
            have hscr_l : 15744 ≤ scr.length := by rw [hsk.2.1]; exact hbase
            c0_hsplit
            · have hui_lt : ui.toNat < nunits.toNat := hc
              clear hc
              have hui1_eq : (ui + 1#32).toNat = ui.toNat + 1 :=
                m8_bv32_add1_toNat hui_lt (by omega)
              have h14720n : (14720 : BitVec 32).toNat = 14720 := rfl
              have h14720_nat : (BitVec.setWidth 64 ((14720 : BitVec 32) + ui)).toNat =
                  14720 + ui.toNat := by
                rw [m8k6_bv64_add2_lt (by rw [h14720n]; omega), h14720n]
              have h14720_bd : (BitVec.setWidth 64 ((14720 : BitVec 32) + ui)).toNat <
                  scr.length := by
                rw [h14720_nat]; omega
              have h14720_mod : (14720 + ui.toNat) % 4294967296 =
                  (BitVec.setWidth 64 ((14720 : BitVec 32) + ui)).toNat := by
                rw [h14720_nat]; omega
              let ucid := scr[(BitVec.setWidth 64 ((14720 : BitVec 32) + ui)).toNat]'h14720_bd
              have hucid_c0 : scr[(14720 + ui.toNat) % 4294967296]'(by
                  rw [h14720_mod]; exact h14720_bd) = ucid :=
                m8_k6_get_congr h14720_mod _ h14720_bd
              c0_hsteps_nogrp
              refine wp_join0
                (fun mj => ∃ scrj, M8SolveKeep scr0 scrj ∧
                  (FullMem c (m8ScrSt s scrj) ⋆ R) mj)
                ?_ ?_
              · intro _ mj ⟨scrj, hskj, hmj⟩
                c0_hsteps!
                exact ih1 (ui + 1#32, scrj) mj (by dsimp only; rw [hui1_eq]; omega)
                  ⟨by rw [hui1_eq]; omega, hskj, hmj⟩
              · intro Ju1 hJu1
                c0_hsplit
                · have hucid_lt : ucid.toNat < nc.toNat := by
                    simpa [nc, hucid_c0] using hc
                  clear hc
                  have h11648n : (11648 : BitVec 32).toNat = 11648 := rfl
                  have h11648_nat : (BitVec.setWidth 64 ((11648 : BitVec 32) + ucid)).toNat =
                      11648 + ucid.toNat := by
                    rw [m8k6_bv64_add2_lt (by rw [h11648n]; omega), h11648n]
                  have h11648_bd : (BitVec.setWidth 64 ((11648 : BitVec 32) + ucid)).toNat <
                      scr.length := by
                    rw [h11648_nat]; omega
                  let off := scr[(BitVec.setWidth 64 ((11648 : BitVec 32) + ucid)).toNat]'h11648_bd
                  have h11648_mod : (11648 + (scr[(14720 + ui.toNat) % 4294967296]'(by
                        rw [h14720_mod]; exact h14720_bd)).toNat) % 4294967296 =
                      (BitVec.setWidth 64 ((11648 : BitVec 32) + ucid)).toNat := by
                    rw [hucid_c0, h11648_nat]; omega
                  have hoff_c0 : scr[(11648 + (scr[(14720 + ui.toNat) % 4294967296]'(by
                        rw [h14720_mod]; exact h14720_bd)).toNat) % 4294967296]'(by
                        rw [h11648_mod]; exact h11648_bd) = off :=
                    m8_k6_get_congr h11648_mod _ h11648_bd
                  c0_hsteps_nogrp
                  refine wp_join0
                    (fun mj => ∃ scrj, M8SolveKeep scr0 scrj ∧
                      (FullMem c (m8ScrSt s scrj) ⋆ R) mj)
                    ?_ ?_
                  · intro _ mj ⟨scrj, hskj, hmj⟩; c0_hsteps!; exact hJu1 mj ⟨scrj, hskj, hmj⟩
                  · intro Ju2 hJu2
                    c0_hsplit
                    · have hoff_lt : off.toNat < acap.toNat := by
                        simpa [acap, hoff_c0] using hc
                      clear hc
                      have hscr_lt30 := hsk.1.length_lt
                      have hk15_eq : scr[4207]? = scr2[4207]? :=
                        hsk.2.2.2.2.1.trans hs2.2.2.2.2.1.symm
                      have hscr_cap : 15744 + acap.toNat ≤ scr.length := by
                        have h := hsk.1.length_ge
                        rw [hk15_eq, m8_k6_get_eq (by omega : 4207 < scr2.length)] at h
                        exact h
                      have h15744n : (15744 : BitVec 32).toNat = 15744 := rfl
                      have h15744_nat : (BitVec.setWidth 64 ((15744 : BitVec 32) + off)).toNat =
                          15744 + off.toNat := by
                        rw [m8k6_bv64_add2_lt (by rw [h15744n]; omega), h15744n]
                      have h15744_bd : (BitVec.setWidth 64 ((15744 : BitVec 32) + off)).toNat <
                          scr.length := by
                        rw [h15744_nat]; omega
                      let ul := scr[(BitVec.setWidth 64
                        ((15744 : BitVec 32) + off)).toNat]'h15744_bd
                      have h15744_mod : (15744 +
                          (scr[(11648 +
                            (scr[(14720 + ui.toNat) % 4294967296]'(by
                              rw [h14720_mod]; exact h14720_bd)).toNat) % 4294967296]'(by
                                rw [h11648_mod]; exact h11648_bd)).toNat) % 4294967296 =
                          (BitVec.setWidth 64 ((15744 : BitVec 32) + off)).toNat := by
                        rw [hoff_c0, h15744_nat]; omega
                      have hul_c0 : scr[(15744 +
                          (scr[(11648 +
                            (scr[(14720 + ui.toNat) % 4294967296]'(by
                              rw [h14720_mod]; exact h14720_bd)).toNat) % 4294967296]'(by
                                rw [h11648_mod]; exact h11648_bd)).toNat) % 4294967296]'(by
                          rw [h15744_mod]; exact h15744_bd) = ul :=
                        m8_k6_get_congr h15744_mod _ h15744_bd
                      c0_hsteps_nogrp
                      refine wp_join0
                        (fun mj => ∃ scrj, M8SolveKeep scr0 scrj ∧
                          (FullMem c (m8ScrSt s scrj) ⋆ R) mj)
                        ?_ ?_
                      · intro _ mj ⟨scrj, hskj, hmj⟩; c0_hsteps!; exact hJu2 mj ⟨scrj, hskj, hmj⟩
                      · intro Ju3 hJu3
                        c0_hsplit
                        · have hul_lt : ul.toNat < 2 * nv.toNat := by
                            have hmod : 2 * nv.toNat % 4294967296 = 2 * nv.toNat :=
                              Nat.mod_eq_of_lt (by omega)
                            simpa [nv, scr2, hul_c0, hmod] using hc
                          clear hc
                          have h6528n : (6528 : BitVec 32).toNat = 6528 := rfl
                          have h6528_bd : (BitVec.setWidth 64 ((6528 : BitVec 32) + ul)).toNat <
                              scr.length := by
                            rw [m8k6_bv64_add2_lt (by rw [h6528n]; omega), h6528n]; omega
                          c0_hsplit
                          · c0_hsteps_nogrp
                            have hsk7 := m8SolveKeep_of_set_lo hsk 4199 ucid (by decide)
                              (by decide) (by decide) (by decide)
                            exact retQ0 20#64 (scr.set 4199 ucid) hsk7 hm
                          · clear hc
                            refine wp_join0
                              (fun mj => ∃ scrj, M8SolveKeep scr0 scrj ∧
                                (FullMem c (m8ScrSt s scrj) ⋆ R) mj)
                              ?_ ?_
                            · intro _ mj ⟨scrj, hskj, hmj⟩
                              c0_hsteps!; exact hJu3 mj ⟨scrj, hskj, hmj⟩
                            · intro Ju4 hJu4
                              c0_hsplit
                              · m8k6_call hAssign
                                dsimp only [vals, Arg.val]
                                refine m8K6AssignSpec_intro rfl
                                  (m8ScrSt_lengthsOk hlen0 (hsk.2.1.trans hscr0_l)) hsc hmi ?_
                                intro scra ma hlena hkeepa hma
                                rw [m8ScrSt_buf] at hkeepa
                                rw [m8ScrSt_upd] at hma
                                c0_hsteps!
                                exact hJu4 ma ⟨scra, m8SolveKeep_of_assign hsk honc
                                  (hlena.trans (hsk.2.1.trans hscr0_l).symm)
                                  (fun idx hi => hkeepa idx (by
                                    rw [hsk.2.1, hscr0_l] at hi; exact hi)),
                                  hma⟩
                              · c0_hsteps!; exact hJu4 mi ⟨scr, hsk, hmi⟩
                        · c0_hsteps!; exact hJu3 mi ⟨scr, hsk, hmi⟩
                    · c0_hsteps!; exact hJu2 mi ⟨scr, hsk, hmi⟩
                · c0_hsteps!; exact hJu1 mi ⟨scr, hsk, hmi⟩
            · clear hc
              m8k6_call hProp
              dsimp only [vals, Arg.val]
              refine m8K6PropSpec_intro rfl
                (m8ScrSt_lengthsOk hlen0 (hsk.2.1.trans hscr0_l)) hsc
                (by rw [m8ScrSt_buf]; exact hsk.1) hmi ?_
              intro confl scrp mp; dsimp only
              intro hokp hlenp hp_lo _ hp_205 _ _ hp_hi hmp
              rw [m8ScrSt_buf] at hp_lo hp_205 hp_hi
              rw [m8ScrSt_upd] at hmp
              have hskp := m8SolveKeep_of_prop hsk honc hokp
                (hlenp.trans (hsk.2.1.trans hscr0_l).symm) hp_lo hp_205 hp_hi
              have hkp_l : 15744 ≤ scrp.length := by rw [hskp.2.1]; exact hbase
              c0_hsplit
              · c0_hsteps_nogrp
                have hskp7 := m8SolveKeep_of_set_lo hskp 4199 confl (by decide) (by decide)
                  (by decide) (by decide)
                exact retQ0 20#64 (scrp.set 4199 confl) hskp7 hm
              · clear hc
                refine wp_while_state (ts := [i32])
                  (fun st : BitVec 32 × BitVec 64 × List (BitVec 32) => (st.1, ()))
                  (fun st => st.2.1.toNat)
                  (fun (cf, fl, scr) mi =>
                    fl.toNat ≤ s.core.fuel.toNat ∧ M8SolveKeep scr0 scr ∧
                    (FullMem c (m8ScrFuelSt s fl scr) ⋆ R) mi)
                  ?_ ?_
                · intro Jo hJo
                  c0_hsteps!
                  exact hJo (confl, fuel0, scrp) mp
                    ⟨hfuel0_le, hskp, m8ScrFuelSt_self s scrp ▸ hmp⟩
                · rintro Jo ⟨cf, fl, scr⟩ mi ⟨hfl_le, hsk, hmi⟩ ih
                  have hscr_l : 15744 ≤ scr.length := by rw [hsk.2.1]; exact hbase
                  c0_hsplit
                  · clear hc
                    c0_hsplit
                    · have hfl_pos : 0 < fl.toNat := hc
                      clear hc
                      let fl1 := fl - 1#64
                      have hfl1_eq : fl1.toNat = fl.toNat - 1 := m8_bv64_sub1_toNat hfl_pos
                      have hfl1_lt : fl1.toNat < fl.toNat := by omega
                      have hfl1_le : fl1.toNat ≤ s.core.fuel.toNat := by omega
                      c0_hsplit
                      · clear hc
                        c0_hsplit
                        · c0_hsteps_nogrp
                          have hsk7 := m8SolveKeep_of_set_lo hsk 4199 cf (by decide) (by decide)
                            (by decide) (by decide)
                          exact retQ 20#64 fl1 (scr.set 4199 cf) hfl1_le hsk7 hm
                        · clear hc
                          m8k6_call hAnalyze
                          dsimp only [vals, Arg.val]
                          refine m8K6AnalyzeSpec_intro rfl
                            (m8ScrFuelSt_lengthsOk hlen0 (hsk.2.1.trans hscr0_l) fl1)
                            hsc (by rw [m8ScrFuelSt_buf]; exact hsk.1) hm ?_
                          intro oka scra ma; dsimp only
                          intro hoka hlena ha_lo ha4194 ha_nc ha_aux _ _ ha4207 _ _ _ hma
                          rw [m8ScrFuelSt_buf] at ha_lo ha4194 ha_nc ha_aux ha4207
                          rw [m8ScrFuelSt_upd] at hma
                          have hska := m8SolveKeep_of_analyze hsk honc hoka
                            (hlena.trans (hsk.2.1.trans hscr0_l).symm) ha_lo ha4194 ha_nc ha_aux
                            ha4207
                          c0_hsplit
                          · m8k6_call hProp
                            dsimp only [vals, Arg.val]
                            refine m8K6PropSpec_intro rfl
                              (m8ScrFuelSt_lengthsOk hlen0 hlena fl1) hsc
                              (by rw [m8ScrFuelSt_buf]; exact hska.1) hma ?_
                            intro cf' scrp' mp'; dsimp only
                            intro hokp' hlenp' hp_lo' _ hp_205' _ _ hp_hi' hmp'
                            rw [m8ScrFuelSt_buf] at hp_lo' hp_205' hp_hi'
                            rw [m8ScrFuelSt_upd] at hmp'
                            have hskp' := m8SolveKeep_of_prop hska honc hokp'
                              (hlenp'.trans hlena.symm) hp_lo' hp_205' hp_hi'
                            c0_hsteps!
                            exact ih (cf', fl1, scrp') mp' hfl1_lt ⟨hfl1_le, hskp', hmp'⟩
                          · c0_hsteps!; exact retQ 0#64 fl1 scra hfl1_le hska hma
                      · clear hc
                        c0_hsplit
                        · c0_hsteps!; exact retQ 10#64 fl1 scr hfl1_le hsk hm
                        · clear hc
                          c0_hsteps_nogrp
                          refine wp_while_break_state
                            (brkTs := [i32, i32, i32]) (lpTs := [i32, i32])
                            (fun st : BitVec 32 × BitVec 32 × BitVec 32 =>
                              (st.1, st.2.1, st.2.2, ()))
                            (fun st mp =>
                              (st.2.1 = 0xFFFFFFFF#32 ∨ st.2.1.toNat < nv.toNat) ∧ mp = m)
                            (fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
                            (fun st => nv.toNat - st.2.toNat)
                            (fun st mp => st.2.toNat ≤ nv.toNat ∧ mp = m)
                            ?_ ?_ ?_
                          · rintro _ ⟨cur1, pk1, stp1⟩ mp1 ⟨hpk1, hmp1⟩
                            subst mp1
                            c0_hsteps_nogrp
                            refine wp_join_state (ts := [i32, i32, i32])
                              (α := BitVec 32 × BitVec 32 × BitVec 32)
                              (fun st => (st.1, st.2.1, st.2.2, ()))
                              (fun st mp =>
                                (st.2.1 = 0xFFFFFFFF#32 ∨ st.2.1.toNat < nv.toNat) ∧ mp = m)
                              ?_ ?_
                            · intro _ ⟨c2, pk2, stp2⟩ mp2 ⟨hpk2, hmp2⟩
                              subst mp2
                              c0_hsteps_nogrp
                              refine wp_join_state (ts := [i32, i32])
                                (α := BitVec 32 × BitVec 32) (fun st => (st.1, st.2, ()))
                                (fun st mp =>
                                  (st.2 = 0xFFFFFFFF#32 ∨ st.2.toNat < nv.toNat) ∧ mp = m)
                                ?_ ?_
                              · intro _ ⟨c3, pk3⟩ mp3 ⟨hpk3, hmp3⟩
                                subst mp3
                                c0_hsplit
                                · c0_hsteps!; exact retQ 10#64 fl1 scr hfl1_le hsk hm
                                · have hpk3_lt : pk3.toNat < nv.toNat := by
                                    rcases hpk3 with rfl | hlt
                                    · exact absurd rfl hc
                                    · exact hlt
                                  have h5760n : (5760 : BitVec 32).toNat = 5760 := rfl
                                  have hscr10_l : 15744 ≤ (scr.set 4202 pk3).length := by
                                    rw [List.length_set]; exact hscr_l
                                  have h5760_bd : (BitVec.setWidth 64
                                      ((5760 : BitVec 32) + pk3)).toNat <
                                      (scr.set 4202 pk3).length := by
                                    rw [m8k6_bv64_add2_lt (by rw [h5760n]; have := hnv_le; omega),
                                      h5760n, List.length_set]
                                    have := hnv_le; omega
                                  have hsk10 := m8SolveKeep_of_set_lo hsk 4202 pk3 (by decide)
                                    (by decide) (by decide) (by decide)
                                  c0_hsteps!
                                  m8k6_call hAssign
                                  dsimp only [vals, Arg.val]
                                  refine m8K6AssignSpec_intro rfl
                                    (m8ScrFuelSt_lengthsOk hlen0
                                      (by rw [List.length_set, List.length_set, hsk.2.1, hscr0_l])
                                      fl1)
                                    hsc hm ?_
                                  intro scra ma hlena hkeepa hma
                                  rw [m8ScrFuelSt_buf] at hkeepa
                                  rw [m8ScrFuelSt_upd] at hma
                                  have hska := m8SolveKeep_of_assign
                                    (m8SolveKeep_of_set_lo hsk10 4195 _ (by decide) (by decide)
                                      (by decide) (by decide))
                                    honc
                                    (by rw [hlena, List.length_set, List.length_set, hsk.2.1,
                                      hscr0_l])
                                    (fun idx hi => hkeepa idx (by
                                      rw [List.length_set, List.length_set, hsk.2.1, hscr0_l] at hi
                                      exact hi))
                                  m8k6_call hProp
                                  dsimp only [vals, Arg.val]
                                  refine m8K6PropSpec_intro rfl
                                    (m8ScrFuelSt_lengthsOk hlen0 hlena fl1) hsc
                                    (by rw [m8ScrFuelSt_buf]; exact hska.1) hma ?_
                                  intro cf' scrp' mp'; dsimp only
                                  intro hokp' hlenp' hp_lo' _ hp_205' _ _ hp_hi' hmp'
                                  rw [m8ScrFuelSt_buf] at hp_lo' hp_205' hp_hi'
                                  rw [m8ScrFuelSt_upd] at hmp'
                                  have hskp' := m8SolveKeep_of_prop hska honc hokp'
                                    (hlenp'.trans hlena.symm) hp_lo' hp_205' hp_hi'
                                  c0_hsteps!
                                  exact ih (cf', fl1, scrp') mp' hfl1_lt ⟨hfl1_le, hskp', hmp'⟩
                              · intro J3 hJ3
                                c0_hsplit
                                · c0_hsteps_nogrp
                                  refine wp_while_break_state
                                    (brkTs := [i32, i32]) (lpTs := [i32])
                                    (fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
                                    (fun st mp =>
                                      (st.2 = 0xFFFFFFFF#32 ∨ st.2.toNat < nv.toNat) ∧ mp = m)
                                    (fun c : BitVec 32 => (c, ()))
                                    (fun c => nv.toNat - c.toNat)
                                    (fun c mp => c.toNat ≤ nv.toNat ∧ mp = m)
                                    ?_ ?_ ?_
                                  · rintro _ ⟨c3, pk3⟩ mp3 ⟨hpk3, hmp3⟩
                                    subst mp3
                                    c0_hsteps!; exact hJ3 (c3, pk3) m ⟨hpk3, rfl⟩
                                  · rintro B3 L3 c3 mp3 hB3 ih3 ⟨hc3_le, hmp3⟩
                                    subst mp3
                                    c0_hsplit
                                    · have hc3_lt : c3.toNat < nv.toNat := hc
                                      obtain ⟨h6528_bd, _⟩ := m8k6_pick_bounds hscr_l hnv_le hc3_lt
                                      c0_hsplit
                                      · c0_hsteps!; exact hB3 (c3, c3) m ⟨Or.inr hc3_lt, rfl⟩
                                      · have hc31 : (c3 + 1#32).toNat = c3.toNat + 1 :=
                                          m8_bv32_add1_toNat hc3_lt (by omega)
                                        c0_hsteps!
                                        exact ih3 (c3 + 1#32) m (by rw [hc31]; omega)
                                          ⟨by rw [hc31]; omega, rfl⟩
                                    · c0_hsteps!; exact hB3 (c3, pk2) m ⟨hpk2, rfl⟩
                                  · intro B3 L3 _ hL3
                                    c0_hsteps!; exact hL3 0#32 m ⟨Nat.zero_le _, rfl⟩
                                · c0_hsteps!; exact hJ3 (c2, pk2) m ⟨hpk2, rfl⟩
                            · intro J2 hJ2
                              c0_hsplit
                              · c0_hsteps_nogrp
                                refine wp_while_break_state
                                  (brkTs := [i32, i32, i32]) (lpTs := [i32, i32])
                                  (fun st : BitVec 32 × BitVec 32 × BitVec 32 =>
                                    (st.1, st.2.1, st.2.2, ()))
                                  (fun st mp =>
                                    (st.2.1 = 0xFFFFFFFF#32 ∨ st.2.1.toNat < nv.toNat) ∧ mp = m)
                                  (fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
                                  (fun st => nv.toNat - st.2.toNat)
                                  (fun st mp => st.2.toNat ≤ nv.toNat ∧ mp = m)
                                  ?_ ?_ ?_
                                · rintro _ ⟨c2, pk2, stp2⟩ mp2 ⟨hpk2, hmp2⟩
                                  subst mp2
                                  c0_hsteps!; exact hJ2 (c2, pk2, stp2) m ⟨hpk2, rfl⟩
                                · rintro B2 L2 ⟨c2, stp2⟩ mp2 hB2 ih2 ⟨hstp2_le, hmp2⟩
                                  subst mp2
                                  c0_hsplit
                                  · have hc2_lt : c2.toNat < nv.toNat := hc
                                    clear hc
                                    c0_hsplit
                                    · have hstp2_lt : stp2.toNat < nv.toNat := hc
                                      obtain ⟨h6528_bd, h4736_bd⟩ :=
                                        m8k6_pick_bounds hscr_l hnv_le hc2_lt
                                      c0_hsplit
                                      · c0_hsteps!
                                        exact hB2 (c2, c2, stp2) m ⟨Or.inr hc2_lt, rfl⟩
                                      · have hstp21 : (stp2 + 1#32).toNat = stp2.toNat + 1 :=
                                          m8_bv32_add1_toNat hstp2_lt (by omega)
                                        let nc2 := scr[(BitVec.setWidth 64
                                          ((4736 : BitVec 32) + c2)).toNat]'h4736_bd
                                        c0_hsteps!
                                        exact ih2 (nc2, stp2 + 1#32) m
                                          (by dsimp only; rw [hstp21]; omega)
                                          ⟨by dsimp only; rw [hstp21]; omega, rfl⟩
                                    · c0_hsteps!; exact hB2 (c2, pk1, stp2) m ⟨hpk1, rfl⟩
                                  · c0_hsteps!; exact hB2 (c2, pk1, stp2) m ⟨hpk1, rfl⟩
                                · intro B2 L2 _ hL2
                                  c0_hsteps!
                                  exact hL2 (_, 0#32) m ⟨Nat.zero_le _, rfl⟩
                              · c0_hsteps!; exact hJ2 (cur1, pk1, stp1) m ⟨hpk1, rfl⟩
                          · rintro B1 L1 ⟨c1, stp1⟩ mp1 hB1 ih1 ⟨hstp1_le, hmp1⟩
                            subst mp1
                            c0_hsplit
                            · have hc1_lt : c1.toNat < nv.toNat := hc
                              clear hc
                              c0_hsplit
                              · have hstp1_lt : stp1.toNat < nv.toNat := hc
                                obtain ⟨h6528_bd, h4736_bd⟩ := m8k6_pick_bounds hscr_l hnv_le hc1_lt
                                c0_hsplit
                                · c0_hsteps!
                                  exact hB1 (c1, c1, stp1) m ⟨Or.inr hc1_lt, rfl⟩
                                · have hstp11 : (stp1 + 1#32).toNat = stp1.toNat + 1 :=
                                    m8_bv32_add1_toNat hstp1_lt (by omega)
                                  let nc1 := scr[(BitVec.setWidth 64
                                    ((4736 : BitVec 32) + c1)).toNat]'h4736_bd
                                  c0_hsteps!
                                  exact ih1 (nc1, stp1 + 1#32) m
                                    (by dsimp only; rw [hstp11]; omega)
                                    ⟨by dsimp only; rw [hstp11]; omega, rfl⟩
                              · c0_hsteps!
                                exact hB1 (c1, 0xFFFFFFFF#32, stp1) m ⟨Or.inl rfl, rfl⟩
                            · c0_hsteps!
                              exact hB1 (c1, 0xFFFFFFFF#32, stp1) m ⟨Or.inl rfl, rfl⟩
                          · intro B1 L1 _ hL1
                            c0_hsteps!
                            exact hL1 (_, 0#32) m ⟨Nat.zero_le _, rfl⟩
                    · c0_hsteps!; exact retQ 0#64 fl scr hfl_le hsk hmi
                  · c0_hsteps!; exact retQ 0#64 fl scr hfl_le hsk hmi

end LeanQbe.T.Examples.Kissat.FullM8CoreParity
