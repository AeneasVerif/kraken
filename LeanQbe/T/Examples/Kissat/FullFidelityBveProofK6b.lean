/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBveProof0
import all LeanQbe.T.Examples.Kissat.FullFidelityBveProof0
import LeanQbe.T.Examples.Kissat.FullFidelityBveTactics
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity BVE Parity Proofs — Dynamic K6 Solver (`FidBveProofK6b`)

UNSAT-only `Func.wp` proofs (`public section`, strictly `std3`, zero expose attrs):
1. `full_k6_prop_fid_wp` (`fidK6PropSpec`).
2. `full_k6_analyze_fid_wp` (`fidK6AnalyzeSpec`).
3. `full_k6_solve_fid_wp` (`fidK6SolveSpec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBve

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open Kraken.Bedrock2.Test

open scoped M8K6bTactics FidK6Tactics

attribute [local bv_c0] List.length_set

local macro_rules
  | `(tactic| c0_bound) => `(tactic| first | assumption | rfl | decide | omega | fid_omega)

private theorem fid_sub1_mod32 (a x : Nat) (hx : 0 < x) (hlt : a + (x - 1) < 4294967296) :
    (a + (4294967296 - 1 + x)) % 4294967296 = a + (x - 1) := by
  rw [show a + (4294967296 - 1 + x) = (a + (x - 1)) + 4294967296 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

/-! ## 1. Frame Invariants (`FidPropKeep`, `FidAnaKeep`, `FidAnaPost`, `FidSolveKeep`) -/

private def FidPropKeep (scr0 scr : List (BitVec 32)) : Prop :=
  let mv := (scr0[4214]?.getD 0#32).toNat
  FidK6BufOk scr ∧ scr.length = scr0.length ∧
  (∀ i < 4195, scr[i]? = scr0[i]?) ∧
  (∀ i, 4199 ≤ i → i < 4204 → scr[i]? = scr0[i]?) ∧
  (∀ i, 4205 ≤ i → i < 4224 → scr[i]? = scr0[i]?) ∧
  (∀ i, 4224 + 2 * mv ≤ i → i < 4224 + 5 * mv → scr[i]? = scr0[i]?) ∧
  (∀ i, 4224 + 7 * mv ≤ i → i < 4224 + 9 * mv → scr[i]? = scr0[i]?) ∧
  (∀ i, 4224 + 29 * mv ≤ i → i < 4224 + 45 * mv → scr[i]? = scr0[i]?)

private theorem fidPropKeep_refl {scr0 : List (BitVec 32)} (h : FidK6BufOk scr0) :
    FidPropKeep scr0 scr0 :=
  ⟨h, rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
   fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

private theorem fidPropKeep_mv {scr0 scr : List (BitVec 32)} (h : FidPropKeep scr0 scr) :
    scr[4214]? = scr0[4214]? :=
  h.2.2.2.2.1 4214 (by decide) (by decide)

private theorem fidPropKeep_of_set {scr0 scr : List (BitVec 32)} (hk : FidPropKeep scr0 scr)
    (idx : Nat) (v : BitVec 32)
    (h1 : 4195 ≤ idx) (h2 : idx < 4199 ∨ 4204 ≤ idx) (h3 : idx < 4205 ∨ 4224 ≤ idx)
    (h4 : idx < 4224 + 2 * (scr0[4214]?.getD 0#32).toNat ∨
      4224 + 5 * (scr0[4214]?.getD 0#32).toNat ≤ idx)
    (h5 : idx < 4224 + 7 * (scr0[4214]?.getD 0#32).toNat ∨
      4224 + 9 * (scr0[4214]?.getD 0#32).toNat ≤ idx)
    (h6 : idx < 4224 + 29 * (scr0[4214]?.getD 0#32).toNat ∨
      4224 + 45 * (scr0[4214]?.getD 0#32).toNat ≤ idx) :
    FidPropKeep scr0 (scr.set idx v) := by
  have hmv_eq := fidPropKeep_mv hk
  have hok' : FidK6BufOk (scr.set idx v) :=
    fidK6BufOk_of_frame hk.1 List.length_set fun j _ hor => by
      rw [hmv_eq] at hor
      rcases hor with rfl | rfl | rfl | rfl | ⟨_, _⟩ <;> exact List.getElem?_set_ne (by fid_ne)
  refine ⟨hok', by simp [hk.2.1],
    fun i hi => by rw [List.getElem?_set_ne (by fid_ne)]; exact hk.2.2.1 i hi,
    fun i ha hb => by rw [List.getElem?_set_ne (by fid_ne)]; exact hk.2.2.2.1 i ha hb,
    fun i ha hb => by rw [List.getElem?_set_ne (by fid_ne)]; exact hk.2.2.2.2.1 i ha hb,
    fun i ha hb => by rw [List.getElem?_set_ne (by fid_ne)]; exact hk.2.2.2.2.2.1 i ha hb,
    fun i ha hb => by rw [List.getElem?_set_ne (by fid_ne)]; exact hk.2.2.2.2.2.2.1 i ha hb,
    fun i ha hb => by rw [List.getElem?_set_ne (by fid_ne)]; exact hk.2.2.2.2.2.2.2 i ha hb⟩

private theorem fidPropKeep_of_assign {scr0 scr scr' : List (BitVec 32)} (hk : FidPropKeep scr0 scr)
    (hlen : scr'.length = scr.length)
    (hkeep : ∀ idx < scr.length,
      let mv := (scr[4214]?.getD 0#32).toNat
      idx ≠ 4197 → idx ≠ 4198 →
      (idx < 4224 ∨ 4224 + 2 * mv ≤ idx) →
      (idx < 4224 + 5 * mv ∨ 4224 + 7 * mv ≤ idx) →
      (idx < 4224 + 9 * mv ∨ 4224 + 11 * mv ≤ idx) →
      scr'[idx]? = scr[idx]?) :
    FidPropKeep scr0 scr' := by
  have hmv_eq := fidPropKeep_mv hk
  have hb := hk.1.base_ge; rw [hmv_eq] at hb
  have hok' : FidK6BufOk scr' := fidK6BufOk_of_frame hk.1 hlen fun idx hi hor =>
      hkeep idx hi (by rcases hor with rfl | rfl | rfl | rfl | ⟨_, _⟩ <;> omega)
        (by rcases hor with rfl | rfl | rfl | rfl | ⟨_, _⟩ <;> omega)
        (by rcases hor with rfl | rfl | rfl | rfl | ⟨_, _⟩ <;> omega)
        (by rcases hor with rfl | rfl | rfl | rfl | ⟨_, _⟩ <;> omega)
        (by rcases hor with rfl | rfl | rfl | rfl | ⟨_, _⟩ <;> omega)
  refine ⟨hok', hlen.trans hk.2.1,
    fun i hi => (hkeep i (by omega) (by omega) (by omega) (Or.inl (by omega))
      (Or.inl (by omega)) (Or.inl (by omega))).trans (hk.2.2.1 i hi),
    fun i ha hb' => (hkeep i (by omega) (by omega) (by omega) (Or.inl (by omega))
      (Or.inl (by omega)) (Or.inl (by omega))).trans (hk.2.2.2.1 i ha hb'),
    fun i ha hb' => (hkeep i (by omega) (by omega) (by omega) (Or.inl (by omega))
      (Or.inl (by omega)) (Or.inl (by omega))).trans (hk.2.2.2.2.1 i ha hb'),
    fun i ha hb' => (hkeep i (by omega) (by omega) (by omega) (Or.inr (by rw [hmv_eq]; omega))
      (Or.inl (by rw [hmv_eq]; omega)) (Or.inl (by rw [hmv_eq]; omega))).trans
      (hk.2.2.2.2.2.1 i ha hb'),
    fun i ha hb' => (hkeep i (by omega) (by omega) (by omega) (Or.inr (by rw [hmv_eq]; omega))
      (Or.inr (by rw [hmv_eq]; omega)) (Or.inl (by rw [hmv_eq]; omega))).trans
      (hk.2.2.2.2.2.2.1 i ha hb'),
    fun i ha hb' => (hkeep i (by omega) (by omega) (by omega) (Or.inr (by rw [hmv_eq]; omega))
      (Or.inr (by rw [hmv_eq]; omega)) (Or.inr (by rw [hmv_eq]; omega))).trans
      (hk.2.2.2.2.2.2.2 i ha hb')⟩

private def FidAnaKeep (scr0 scr : List (BitVec 32)) : Prop :=
  let mv := (scr0[4214]?.getD 0#32).toNat
  FidK6BufOk scr ∧ scr.length = scr0.length ∧
  (∀ i < 4195, scr[i]? = scr0[i]?) ∧
  scr[4199]? = scr0[4199]? ∧ scr[4205]? = scr0[4205]? ∧
  scr[4206]? = scr0[4206]? ∧ scr[4207]? = scr0[4207]? ∧
  scr[4211]? = scr0[4211]? ∧ scr[4213]? = scr0[4213]? ∧
  scr[4214]? = scr0[4214]? ∧ scr[4215]? = scr0[4215]? ∧ scr[4216]? = scr0[4216]? ∧
  (∀ i, 4224 + 29 * mv ≤ i → i < 4224 + 43 * mv → scr[i]? = scr0[i]?)

private def FidAnaPost (scr0 scr : List (BitVec 32)) : Prop :=
  let mv := (scr0[4214]?.getD 0#32).toNat
  FidK6BufOk scr ∧ scr.length = scr0.length ∧
  (∀ i < 4193, scr[i]? = scr0[i]?) ∧
  scr[4194]? = scr0[4194]? ∧
  (scr0[4193]?.getD 0#32).toNat ≤ (scr[4193]?.getD 0#32).toNat ∧
  (∀ cid < (scr0[4193]?.getD 0#32).toNat,
    scr[4224 + 37 * mv + cid]? = scr0[4224 + 37 * mv + cid]?) ∧
  scr[4199]? = scr0[4199]? ∧ scr[4205]? = scr0[4205]? ∧
  scr[4207]? = scr0[4207]? ∧ scr[4211]? = scr0[4211]? ∧
  scr[4213]? = scr0[4213]? ∧ scr[4214]? = scr0[4214]? ∧
  scr[4215]? = scr0[4215]? ∧ scr[4216]? = scr0[4216]? ∧
  (∀ i, 4224 + 41 * mv ≤ i → i < 4224 + 43 * mv → scr[i]? = scr0[i]?)

private theorem fidAnaKeep_refl {scr0 : List (BitVec 32)} (h : FidK6BufOk scr0) :
    FidAnaKeep scr0 scr0 :=
  ⟨h, rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

private theorem fidAnaKeep_to_post {scr0 scr : List (BitVec 32)} (hk : FidAnaKeep scr0 scr) :
    FidAnaPost scr0 scr := by
  have h1 : scr[4193]? = scr0[4193]? := hk.2.2.1 4193 (by decide)
  have h16 : scr[4214]? = scr0[4214]? := hk.2.2.2.2.2.2.2.2.2.1
  have hnc_le : (scr0[4193]?.getD 0#32).toNat ≤ 4 * (scr0[4214]?.getD 0#32).toNat := by
    rw [← h1, ← h16]; exact hk.1.nc_le
  refine ⟨hk.1, hk.2.1, fun i hi => hk.2.2.1 i (by omega), hk.2.2.1 4194 (by decide),
    by rw [h1]; exact Nat.le_refl _,
    fun cid hcid => hk.2.2.2.2.2.2.2.2.2.2.2.2 (4224 + 37 * (scr0[4214]?.getD 0#32).toNat + cid)
      (by omega) (by omega),
    hk.2.2.2.1, hk.2.2.2.2.1, hk.2.2.2.2.2.2.1, hk.2.2.2.2.2.2.2.1,
    hk.2.2.2.2.2.2.2.2.1, h16, hk.2.2.2.2.2.2.2.2.2.2.1, hk.2.2.2.2.2.2.2.2.2.2.2.1,
    fun i ha hb => hk.2.2.2.2.2.2.2.2.2.2.2.2 i (by omega) hb⟩

private theorem fidAnaKeep_of_frame {scr0 scr scr' : List (BitVec 32)} (hk : FidAnaKeep scr0 scr)
    (hlen : scr'.length = scr.length)
    (hlo : ∀ i < 4195, scr'[i]? = scr[i]?)
    (h199 : scr'[4199]? = scr[4199]?) (h205 : scr'[4205]? = scr[4205]?)
    (h206 : scr'[4206]? = scr[4206]?) (h207 : scr'[4207]? = scr[4207]?)
    (h211 : scr'[4211]? = scr[4211]?) (h213 : scr'[4213]? = scr[4213]?)
    (h216 : scr'[4214]? = scr[4214]?) (h217 : scr'[4215]? = scr[4215]?)
    (h218 : scr'[4216]? = scr[4216]?)
    (hmet : ∀ i, 4224 + 29 * (scr0[4214]?.getD 0#32).toNat ≤ i →
      i < 4224 + 43 * (scr0[4214]?.getD 0#32).toNat → scr'[i]? = scr[i]?) :
    FidAnaKeep scr0 scr' := by
  have h16 := hk.2.2.2.2.2.2.2.2.2.1
  have hok' := fidK6BufOk_of_frame hk.1 hlen fun idx _ hor => by
    rw [h16] at hor; rcases hor with rfl | rfl | rfl | rfl | ⟨ha, hb⟩
    · exact hlo 4193 (by decide)
    · exact h206
    · exact h207
    · exact h216
    · exact hmet idx ha (by omega)
  exact ⟨hok', hlen.trans hk.2.1, fun i hi => (hlo i hi).trans (hk.2.2.1 i hi),
    h199.trans hk.2.2.2.1, h205.trans hk.2.2.2.2.1, h206.trans hk.2.2.2.2.2.1,
    h207.trans hk.2.2.2.2.2.2.1, h211.trans hk.2.2.2.2.2.2.2.1, h213.trans hk.2.2.2.2.2.2.2.2.1,
    h216.trans hk.2.2.2.2.2.2.2.2.2.1, h217.trans hk.2.2.2.2.2.2.2.2.2.2.1,
    h218.trans hk.2.2.2.2.2.2.2.2.2.2.2.1,
    fun i ha hb => (hmet i ha hb).trans (hk.2.2.2.2.2.2.2.2.2.2.2.2 i ha hb)⟩

private theorem fidAnaKeep_of_set {scr0 scr : List (BitVec 32)} (hk : FidAnaKeep scr0 scr)
    (idx : Nat) (v : BitVec 32)
    (hlo : 4195 ≤ idx := by decide) (h199 : idx ≠ 4199 := by decide)
    (h205 : idx ≠ 4205 := by decide) (h206 : idx ≠ 4206 := by decide)
    (h207 : idx ≠ 4207 := by decide) (h211 : idx ≠ 4211 := by decide)
    (h213 : idx ≠ 4213 := by decide) (h216 : idx ≠ 4214 := by decide)
    (h217 : idx ≠ 4215 := by decide) (h218 : idx ≠ 4216 := by decide)
    (hmet : idx < 4224 + 29 * (scr0[4214]?.getD 0#32).toNat ∨
      4224 + 43 * (scr0[4214]?.getD 0#32).toNat ≤ idx) :
    FidAnaKeep scr0 (scr.set idx v) :=
  fidAnaKeep_of_frame hk List.length_set (fun _ _ => List.getElem?_set_ne (by fid_ne))
    (List.getElem?_set_ne h199) (List.getElem?_set_ne h205) (List.getElem?_set_ne h206)
    (List.getElem?_set_ne h207) (List.getElem?_set_ne h211) (List.getElem?_set_ne h213)
    (List.getElem?_set_ne h216) (List.getElem?_set_ne h217) (List.getElem?_set_ne h218)
    (fun _ _ _ => List.getElem?_set_ne (by fid_ne))

private theorem fidAnaPost_of_frame {scr0 scr scr' : List (BitVec 32)} (hp : FidAnaPost scr0 scr)
    (hlen : scr'.length = scr.length)
    (hlo : ∀ i < 4195, scr'[i]? = scr[i]?)
    (h199 : scr'[4199]? = scr[4199]?) (h205 : scr'[4205]? = scr[4205]?)
    (h206 : scr'[4206]? = scr[4206]?) (h207 : scr'[4207]? = scr[4207]?)
    (h211 : scr'[4211]? = scr[4211]?) (h213 : scr'[4213]? = scr[4213]?)
    (h216 : scr'[4214]? = scr[4214]?) (h217 : scr'[4215]? = scr[4215]?)
    (h218 : scr'[4216]? = scr[4216]?)
    (hmet : ∀ i, 4224 + 29 * (scr0[4214]?.getD 0#32).toNat ≤ i →
      i < 4224 + 43 * (scr0[4214]?.getD 0#32).toNat → scr'[i]? = scr[i]?) :
    FidAnaPost scr0 scr' := by
  have h16 := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hok' := fidK6BufOk_of_frame hp.1 hlen fun idx _ hor => by
    rw [h16] at hor
    rcases hor with rfl | rfl | rfl | rfl | ⟨ha, hb⟩
    · exact hlo 4193 (by decide)
    · exact h206
    · exact h207
    · exact h216
    · exact hmet idx ha (by omega)
  have hnc_le : (scr0[4193]?.getD 0#32).toNat ≤ 4 * (scr0[4214]?.getD 0#32).toNat := by
    have := hp.1.nc_le; rw [h16] at this; have := hp.2.2.2.2.1; omega
  refine ⟨hok', hlen.trans hp.2.1, fun i hi => (hlo i (by omega)).trans (hp.2.2.1 i hi),
    (hlo 4194 (by decide)).trans hp.2.2.2.1,
    by rw [hlo 4193 (by decide)]; exact hp.2.2.2.2.1,
    fun cid hcid => (hmet (4224 + 37 * (scr0[4214]?.getD 0#32).toNat + cid) (by omega)
      (by omega)).trans (hp.2.2.2.2.2.1 cid hcid),
    h199.trans hp.2.2.2.2.2.2.1, h205.trans hp.2.2.2.2.2.2.2.1,
    h207.trans hp.2.2.2.2.2.2.2.2.1, h211.trans hp.2.2.2.2.2.2.2.2.2.1,
    h213.trans hp.2.2.2.2.2.2.2.2.2.2.1, h216.trans hp.2.2.2.2.2.2.2.2.2.2.2.1,
    h217.trans hp.2.2.2.2.2.2.2.2.2.2.2.2.1, h218.trans hp.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun i ha hb => (hmet i (by omega) hb).trans (hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2 i ha hb)⟩

private theorem fidPropKeep_of_set_lo {scr0 scr : List (BitVec 32)}
    (hk : FidPropKeep scr0 scr) (idx : Nat) (v : BitVec 32)
    (hlo : 4224 + 9 * (scr0[4214]?.getD 0#32).toNat ≤ idx)
    (hhi : idx < 4224 + 29 * (scr0[4214]?.getD 0#32).toNat) :
    FidPropKeep scr0 (scr.set idx v) :=
  fidPropKeep_of_set hk idx v (by omega) (Or.inr (by omega)) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr hlo) (Or.inl hhi)

private theorem fidPropKeep_of_set_ar {scr0 scr : List (BitVec 32)}
    (hk : FidPropKeep scr0 scr) (idx : Nat) (v : BitVec 32)
    (h : 4224 + 45 * (scr0[4214]?.getD 0#32).toNat ≤ idx) :
    FidPropKeep scr0 (scr.set idx v) :=
  fidPropKeep_of_set hk idx v (by omega) (Or.inr (by omega)) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr h)

private theorem fidAnaKeep_of_set_lo {scr0 scr : List (BitVec 32)}
    (hk : FidAnaKeep scr0 scr) (idx : Nat) (v : BitVec 32)
    (hlo : 4224 ≤ idx)
    (hhi : idx < 4224 + 29 * (scr0[4214]?.getD 0#32).toNat) :
    FidAnaKeep scr0 (scr.set idx v) :=
  fidAnaKeep_of_set hk idx v (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inl hhi)

private theorem fidAnaKeep_of_set_ge {scr0 scr : List (BitVec 32)}
    (hk : FidAnaKeep scr0 scr) (idx : Nat) (v : BitVec 32)
    (h : 4224 + 43 * (scr0[4214]?.getD 0#32).toNat ≤ idx) :
    FidAnaKeep scr0 (scr.set idx v) :=
  fidAnaKeep_of_set hk idx v (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inr h)

private theorem fidAnaPost_of_assign {scr0 scr scr' : List (BitVec 32)}
    (hp : FidAnaPost scr0 scr) (hlen : scr'.length = scr.length)
    (hkeep : ∀ idx < scr.length,
      let mv := (scr[4214]?.getD 0#32).toNat
      idx ≠ 4197 → idx ≠ 4198 →
      (idx < 4224 ∨ 4224 + 2 * mv ≤ idx) →
      (idx < 4224 + 5 * mv ∨ 4224 + 7 * mv ≤ idx) →
      (idx < 4224 + 9 * mv ∨ 4224 + 11 * mv ≤ idx) →
      scr'[idx]? = scr[idx]?) :
    FidAnaPost scr0 scr' := by
  have h16 := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hb := hp.1.base_ge; rw [h16] at hb
  exact fidAnaPost_of_frame hp hlen
    (fun i hi => hkeep i (by omega) (by omega) (by omega) (Or.inl (by omega))
      (Or.inl (by omega)) (Or.inl (by omega)))
    (hkeep 4199 (by omega) (by decide) (by decide) (Or.inl (by decide))
      (Or.inl (by omega)) (Or.inl (by omega)))
    (hkeep 4205 (by omega) (by decide) (by decide) (Or.inl (by decide))
      (Or.inl (by omega)) (Or.inl (by omega)))
    (hkeep 4206 (by omega) (by decide) (by decide) (Or.inl (by decide))
      (Or.inl (by omega)) (Or.inl (by omega)))
    (hkeep 4207 (by omega) (by decide) (by decide) (Or.inl (by decide))
      (Or.inl (by omega)) (Or.inl (by omega)))
    (hkeep 4211 (by omega) (by decide) (by decide) (Or.inl (by decide))
      (Or.inl (by omega)) (Or.inl (by omega)))
    (hkeep 4213 (by omega) (by decide) (by decide) (Or.inl (by decide))
      (Or.inl (by omega)) (Or.inl (by omega)))
    (hkeep 4214 (by omega) (by decide) (by decide) (Or.inl (by decide))
      (Or.inl (by omega)) (Or.inl (by omega)))
    (hkeep 4215 (by omega) (by decide) (by decide) (Or.inl (by decide))
      (Or.inl (by omega)) (Or.inl (by omega)))
    (hkeep 4216 (by omega) (by decide) (by decide) (Or.inl (by decide))
      (Or.inl (by omega)) (Or.inl (by omega)))
    (fun i ha hb' => hkeep i (by omega) (by omega) (by omega)
      (Or.inr (by rw [h16]; omega)) (Or.inr (by rw [h16]; omega))
      (Or.inr (by rw [h16]; omega)))

private theorem fidAnaPost_of_watch {scr0 scr scr' : List (BitVec 32)}
    (hp : FidAnaPost scr0 scr) (hlen : scr'.length = scr.length)
    (hkeep : ∀ idx < scr.length,
      let mv := (scr[4214]?.getD 0#32).toNat
      (idx < 4224 + 11 * mv ∨ 4224 + 29 * mv ≤ idx) →
      scr'[idx]? = scr[idx]?) :
    FidAnaPost scr0 scr' := by
  have h16 := hp.2.2.2.2.2.2.2.2.2.2.2.1; have hb := hp.1.base_ge; rw [h16] at hb
  exact fidAnaPost_of_frame hp hlen (fun i _ => hkeep i (by omega) (Or.inl (by omega)))
    (hkeep 4199 (by omega) (Or.inl (by omega))) (hkeep 4205 (by omega) (Or.inl (by omega)))
    (hkeep 4206 (by omega) (Or.inl (by omega))) (hkeep 4207 (by omega) (Or.inl (by omega)))
    (hkeep 4211 (by omega) (Or.inl (by omega))) (hkeep 4213 (by omega) (Or.inl (by omega)))
    (hkeep 4214 (by omega) (Or.inl (by omega))) (hkeep 4215 (by omega) (Or.inl (by omega)))
    (hkeep 4216 (by omega) (Or.inl (by omega)))
    (fun i _ _ => hkeep i (by omega) (Or.inr (by rw [h16]; omega)))

private theorem fidAnaPost_commit {scr0 scrr : List (BitVec 32)}
    {mv nc_m off_m ac_m nkl nres : BitVec 32} (hkr : FidAnaKeep scr0 scrr)
    (hmv_eq : scr0[4214]?.getD 0#32 = mv) (hmv_lo : 256 ≤ mv.toNat) (hmv_hi : mv.toNat ≤ 8192)
    (hncm_eq : scrr[4193]? = some nc_m) (hacr_eq : scrr[4207]? = some ac_m)
    (hncm_lt : nc_m.toNat < 4 * mv.toNat) (hkl_hi : nkl.toNat ≤ mv.toNat)
    (hfit_m : off_m.toNat + nkl.toNat + nres.toNat ≤ ac_m.toNat)
    (hco_e : ((4224 + 29 * mv + nc_m).setWidth 64).toNat = 4224 + 29 * mv.toNat + nc_m.toNat)
    (hcm_e : ((4224 + 33 * mv + nc_m).setWidth 64).toNat = 4224 + 33 * mv.toNat + nc_m.toNat)
    (hca_e : ((4224 + 37 * mv + nc_m).setWidth 64).toNat = 4224 + 37 * mv.toNat + nc_m.toNat) :
    FidAnaPost scr0 (((((scrr.set 4206 (off_m + nkl + nres)).set
      ((4224 + 29 * mv + nc_m).setWidth 64).toNat off_m).set
      ((4224 + 33 * mv + nc_m).setWidth 64).toNat (nkl ||| 0x40000000#32)).set
      ((4224 + 37 * mv + nc_m).setWidth 64).toNat nres).set 4193 (nc_m + 1#32)) := by
  let scr_c := ((((scrr.set 4206 (off_m + nkl + nres)).set
    ((4224 + 29 * mv + nc_m).setWidth 64).toNat off_m).set
    ((4224 + 33 * mv + nc_m).setWidth 64).toNat (nkl ||| 0x40000000#32)).set
    ((4224 + 37 * mv + nc_m).setWidth 64).toNat nres).set 4193 (nc_m + 1#32)
  have hlr : scrr.length = scr0.length := hkr.2.1; have hlt_r := hkr.1.length_lt
  have h16_r := hkr.2.2.2.2.2.2.2.2.2.1; have hlg_r := hkr.1.length_ge
  rw [h16_r, hmv_eq, hacr_eq, Option.getD_some] at hlg_r
  have hnc0_eq : scr0[4193]? = some nc_m := by rw [← hkr.2.2.1 4193 (by decide)]; exact hncm_eq
  have hnc1_n : (nc_m + 1#32).toNat = nc_m.toNat + 1 := m8_bv32_add1_toNat hncm_lt (by omega)
  have hsum_n : (off_m + nkl + nres).toNat = off_m.toNat + nkl.toNat + nres.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hlen_c : scr_c.length = scr0.length := by simp [scr_c, hlr]
  have h16_c : scr_c[4214]? = scr0[4214]? := by
    dsimp only [scr_c]; (repeat rw [List.getElem?_set_ne (by fid_ne)]); exact h16_r
  have h07_c : scr_c[4207]? = some ac_m := by
    dsimp only [scr_c]; (repeat rw [List.getElem?_set_ne (by fid_ne)]); exact hacr_eq
  have h93_c : scr_c[4193]? = some (nc_m + 1#32) := by
    dsimp only [scr_c]; exact List.getElem?_set_self (by simp; omega)
  have h06_c : scr_c[4206]? = some (off_m + nkl + nres) := by
    dsimp only [scr_c]; repeat rw [List.getElem?_set_ne (by fid_ne)]
    exact List.getElem?_set_self (by omega)
  have hok_c : FidK6BufOk scr_c := by
    refine ⟨by rw [h16_c, hmv_eq]; exact hmv_lo, by rw [h16_c, hmv_eq]; exact hmv_hi,
      by rw [h16_c, hmv_eq, h07_c, hlen_c, ← hlr]; exact hlg_r,
      by rw [hlen_c, ← hlr]; exact hlt_r,
      by rw [h93_c, h16_c, hmv_eq, Option.getD_some, hnc1_n]; omega,
      by rw [h06_c, h07_c, Option.getD_some, Option.getD_some, hsum_n]; exact hfit_m,
      fun j hj => ?_⟩
    rw [h93_c, Option.getD_some, hnc1_n] at hj
    dsimp only; rw [h16_c, hmv_eq, h07_c, Option.getD_some]
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj_lt | hj_eq
    · have ho_j : scr_c[4224 + 29 * mv.toNat + j]? = scrr[4224 + 29 * mv.toNat + j]? := by
        dsimp only [scr_c]; repeat rw [List.getElem?_set_ne (by fid_ne)]
      have hm_j : scr_c[4224 + 33 * mv.toNat + j]? = scrr[4224 + 33 * mv.toNat + j]? := by
        dsimp only [scr_c]; repeat rw [List.getElem?_set_ne (by fid_ne)]
      have ha_j : scr_c[4224 + 37 * mv.toNat + j]? = scrr[4224 + 37 * mv.toNat + j]? := by
        dsimp only [scr_c]; repeat rw [List.getElem?_set_ne (by fid_ne)]
      rw [ho_j, hm_j, ha_j]
      have hcl_j := hkr.1.clause_ok (cid := j) (by rw [hncm_eq, Option.getD_some]; exact hj_lt)
      dsimp only at hcl_j
      rwa [h16_r, hmv_eq, hacr_eq, Option.getD_some] at hcl_j
    · subst hj_eq
      have ho_n : scr_c[4224 + 29 * mv.toNat + nc_m.toNat]? = some off_m := by
        dsimp only [scr_c]; rw [List.getElem?_set_ne (by fid_ne), List.getElem?_set_ne (by fid_ne),
          List.getElem?_set_ne (by fid_ne), ← hco_e, List.getElem?_set_self (by simp; omega)]
      have hm_n : scr_c[4224 + 33 * mv.toNat + nc_m.toNat]? = some (nkl ||| 0x40000000#32) := by
        dsimp only [scr_c]
        rw [List.getElem?_set_ne (by fid_ne), List.getElem?_set_ne (by fid_ne), ← hcm_e,
          List.getElem?_set_self (by simp; omega)]
      have ha_n : scr_c[4224 + 37 * mv.toNat + nc_m.toNat]? = some nres := by
        dsimp only [scr_c]
        rw [List.getElem?_set_ne (by fid_ne), ← hca_e, List.getElem?_set_self (by simp; omega)]
      have hsz_n : ((nkl ||| 0x40000000#32) &&& 0xFFFF#32).toNat = nkl.toNat := by
        rw [(m8_bv32_bit_disj nkl 0x40000000#32 0xFFFF#32 (by decide)).1, BitVec.toNat_and,
          show (0xFFFF#32 : BitVec 32).toNat = 2 ^ 16 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
      rw [ho_n, hm_n, ha_n, Option.getD_some, Option.getD_some, Option.getD_some, hsz_n]
      exact ⟨by omega, fun _ => hfit_m⟩
  refine ⟨hok_c, hlen_c,
    fun i hi => by
      repeat rw [List.getElem?_set_ne (by fid_ne)]
      exact hkr.2.2.1 i (by omega),
    by repeat rw [List.getElem?_set_ne (by fid_ne)]
       exact hkr.2.2.1 4194 (by decide),
    by rw [hnc0_eq, h93_c, Option.getD_some, Option.getD_some, hnc1_n]; omega,
    fun cid hc_0 => by
      rw [hnc0_eq, Option.getD_some] at hc_0
      rw [List.getElem?_set_ne (by rw [hmv_eq]; omega),
        List.getElem?_set_ne (by rw [hca_e, hmv_eq]; omega),
        List.getElem?_set_ne (by rw [hcm_e, hmv_eq]; omega),
        List.getElem?_set_ne (by rw [hco_e, hmv_eq]; omega),
        List.getElem?_set_ne (by rw [hmv_eq]; omega)]
      exact hkr.2.2.2.2.2.2.2.2.2.2.2.2 (4224 + 37 * (scr0[4214]?.getD 0#32).toNat + cid)
        (by omega) (by rw [hmv_eq]; omega),
    by repeat rw [List.getElem?_set_ne (by fid_ne)]
       exact hkr.2.2.2.1,
    by repeat rw [List.getElem?_set_ne (by fid_ne)]
       exact hkr.2.2.2.2.1,
    by rw [h07_c, ← hacr_eq]; exact hkr.2.2.2.2.2.2.1,
    by repeat rw [List.getElem?_set_ne (by fid_ne)]
       exact hkr.2.2.2.2.2.2.2.1,
    by repeat rw [List.getElem?_set_ne (by fid_ne)]
       exact hkr.2.2.2.2.2.2.2.2.1,
    h16_c,
    by repeat rw [List.getElem?_set_ne (by fid_ne)]
       exact hkr.2.2.2.2.2.2.2.2.2.2.1,
    by repeat rw [List.getElem?_set_ne (by fid_ne)]
       exact hkr.2.2.2.2.2.2.2.2.2.2.2.1,
    fun i ha hb' => by
      have ha' := ha; have hb2 := hb'
      rw [hmv_eq] at ha' hb2
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by rw [hca_e]; omega),
        List.getElem?_set_ne (by rw [hcm_e]; omega), List.getElem?_set_ne (by rw [hco_e]; omega),
        List.getElem?_set_ne (by omega)]
      exact hkr.2.2.2.2.2.2.2.2.2.2.2.2 i (by omega) hb'⟩

private def FidSolveKeep (scr0 scr : List (BitVec 32)) : Prop :=
  let mv := (scr0[4214]?.getD 0#32).toNat
  FidK6BufOk scr ∧ scr.length = scr0.length ∧
  (∀ i < 4192, scr[i]? = scr0[i]?) ∧
  scr[4194]? = scr0[4194]? ∧ scr[4214]? = scr0[4214]? ∧
  (scr0[4194]?.getD 0#32).toNat ≤ (scr[4193]?.getD 0#32).toNat ∧
  (∀ cid < (scr0[4194]?.getD 0#32).toNat,
    scr[4224 + 37 * mv + cid]? = scr0[4224 + 37 * mv + cid]?) ∧
  scr[4192]? = scr0[4192]? ∧ scr[4207]? = scr0[4207]? ∧
  scr[4211]? = scr0[4211]? ∧ scr[4215]? = scr0[4215]? ∧ scr[4216]? = scr0[4216]? ∧
  (∀ i, 4224 + 41 * mv ≤ i → i < 4224 + 43 * mv → scr[i]? = scr0[i]?)

private theorem fidSolveKeep_refl {scr0 : List (BitVec 32)} (h : FidK6BufOk scr0)
    (honc : (scr0[4194]?.getD 0#32).toNat ≤ (scr0[4193]?.getD 0#32).toNat) :
    FidSolveKeep scr0 scr0 :=
  ⟨h, rfl, fun _ _ => rfl, rfl, rfl, honc, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl,
   fun _ _ _ => rfl⟩

private theorem fidSolveKeep_of_set_hdr {scr0 scr : List (BitVec 32)} (hk : FidSolveKeep scr0 scr)
    (idx : Nat) (v : BitVec 32)
    (hlo : 4195 ≤ idx) (hhi : idx < 4224) (h06 : idx ≠ 4206) (h07 : idx ≠ 4207)
    (h11 : idx ≠ 4211) (h16 : idx ≠ 4214) (h17 : idx ≠ 4215) (h18 : idx ≠ 4216) :
    FidSolveKeep scr0 (scr.set idx v) := by
  have h16e := hk.2.2.2.2.1
  have hmv_lo := hk.1.mv_lo
  rw [h16e] at hmv_lo
  have hok' : FidK6BufOk (scr.set idx v) :=
    fidK6BufOk_of_frame hk.1 (List.length_set (a := v)) fun j _ hor => by
    rw [h16e] at hor
    rcases hor with rfl | rfl | rfl | rfl | ⟨h1, h2⟩ <;> exact List.getElem?_set_ne (by omega)
  refine ⟨hok', by simp [hk.2.1],
    fun i hi => by rw [List.getElem?_set_ne (by fid_ne)]; exact hk.2.2.1 i hi,
    by rw [List.getElem?_set_ne (by fid_ne)]; exact hk.2.2.2.1,
    by rw [List.getElem?_set_ne (by fid_ne)]; exact hk.2.2.2.2.1,
    by rw [List.getElem?_set_ne (by fid_ne)]; exact hk.2.2.2.2.2.1,
    fun cid hc => by rw [List.getElem?_set_ne (by fid_ne)]; exact hk.2.2.2.2.2.2.1 cid hc,
    by rw [List.getElem?_set_ne (by fid_ne)]; exact hk.2.2.2.2.2.2.2.1,
    by rw [List.getElem?_set_ne (by fid_ne)]; exact hk.2.2.2.2.2.2.2.2.1,
    by rw [List.getElem?_set_ne (by fid_ne)]; exact hk.2.2.2.2.2.2.2.2.2.1,
    by rw [List.getElem?_set_ne (by fid_ne)]; exact hk.2.2.2.2.2.2.2.2.2.2.1,
    by rw [List.getElem?_set_ne (by fid_ne)]; exact hk.2.2.2.2.2.2.2.2.2.2.2.1,
    fun i ha hb => by
      rw [List.getElem?_set_ne (by fid_ne)]; exact hk.2.2.2.2.2.2.2.2.2.2.2.2 i ha hb⟩

private theorem fidSolveKeep_of_backtrack {scr0 scr scr' : List (BitVec 32)}
    (hk : FidSolveKeep scr0 scr) (hlen : scr'.length = scr.length)
    (hkeep : ∀ idx < scr.length,
      let mv := (scr[4214]?.getD 0#32).toNat
      (idx < 4195 ∨ (4199 ≤ idx ∧ idx < 4224) ∨
        (4224 + 2 * mv ≤ idx ∧ idx < 4224 + 9 * mv) ∨ 4224 + 11 * mv ≤ idx) →
      scr'[idx]? = scr[idx]?) :
    FidSolveKeep scr0 scr' := by
  have h16 := hk.2.2.2.2.1
  have hb := hk.1.base_ge; rw [h16] at hb
  have hok' := fidK6BufOk_of_frame hk.1 hlen fun idx hi hor => by
    rcases hor with rfl | rfl | rfl | rfl | ⟨_, _⟩
    · exact hkeep 4193 (by omega) (Or.inl (by decide))
    · exact hkeep 4206 (by omega) (Or.inr (Or.inl (by decide)))
    · exact hkeep 4207 (by omega) (Or.inr (Or.inl (by decide)))
    · exact hkeep 4214 (by omega) (Or.inr (Or.inl (by decide)))
    · exact hkeep idx hi (Or.inr (Or.inr (Or.inr (by omega))))
  have honc_le : (scr0[4194]?.getD 0#32).toNat ≤ 4 * (scr0[4214]?.getD 0#32).toNat := by
    have := hk.1.nc_le; rw [h16] at this; have := hk.2.2.2.2.2.1; omega
  refine ⟨hok', hlen.trans hk.2.1,
    fun i hi => (hkeep i (by omega) (Or.inl (by omega))).trans (hk.2.2.1 i hi),
    (hkeep 4194 (by omega) (Or.inl (by decide))).trans hk.2.2.2.1,
    (hkeep 4214 (by omega) (Or.inr (Or.inl (by decide)))).trans hk.2.2.2.2.1,
    by rw [hkeep 4193 (by omega) (Or.inl (by decide))]; exact hk.2.2.2.2.2.1,
    fun cid hc => (hkeep (4224 + 37 * (scr0[4214]?.getD 0#32).toNat + cid) (by omega)
      (Or.inr (Or.inr (Or.inr (by rw [h16]; omega))))).trans (hk.2.2.2.2.2.2.1 cid hc),
    (hkeep 4192 (by omega) (Or.inl (by decide))).trans hk.2.2.2.2.2.2.2.1,
    (hkeep 4207 (by omega) (Or.inr (Or.inl (by decide)))).trans hk.2.2.2.2.2.2.2.2.1,
    (hkeep 4211 (by omega) (Or.inr (Or.inl (by decide)))).trans hk.2.2.2.2.2.2.2.2.2.1,
    (hkeep 4215 (by omega) (Or.inr (Or.inl (by decide)))).trans hk.2.2.2.2.2.2.2.2.2.2.1,
    (hkeep 4216 (by omega) (Or.inr (Or.inl (by decide)))).trans hk.2.2.2.2.2.2.2.2.2.2.2.1,
    fun i ha hb' => (hkeep i (by omega) (Or.inr (Or.inr (Or.inr (by rw [h16]; omega))))).trans
      (hk.2.2.2.2.2.2.2.2.2.2.2.2 i ha hb')⟩

private theorem fidSolveKeep_of_assign {scr0 scr scr' : List (BitVec 32)}
    (hk : FidSolveKeep scr0 scr) (hlen : scr'.length = scr.length)
    (hkeep : ∀ idx < scr.length,
      let mv := (scr[4214]?.getD 0#32).toNat
      idx ≠ 4197 → idx ≠ 4198 →
      (idx < 4224 ∨ 4224 + 2 * mv ≤ idx) →
      (idx < 4224 + 5 * mv ∨ 4224 + 7 * mv ≤ idx) →
      (idx < 4224 + 9 * mv ∨ 4224 + 11 * mv ≤ idx) →
      scr'[idx]? = scr[idx]?) :
    FidSolveKeep scr0 scr' := by
  have h16 := hk.2.2.2.2.1
  have hb := hk.1.base_ge; rw [h16] at hb
  have hok' := fidK6BufOk_of_frame hk.1 hlen fun idx hi hor => hkeep idx hi
      (by rcases hor with rfl | rfl | rfl | rfl | ⟨_, _⟩ <;> omega)
      (by rcases hor with rfl | rfl | rfl | rfl | ⟨_, _⟩ <;> omega)
      (by rcases hor with rfl | rfl | rfl | rfl | ⟨_, _⟩ <;> omega)
      (by rcases hor with rfl | rfl | rfl | rfl | ⟨_, _⟩ <;> omega)
      (by rcases hor with rfl | rfl | rfl | rfl | ⟨_, _⟩ <;> omega)
  have honc_le : (scr0[4194]?.getD 0#32).toNat ≤ 4 * (scr0[4214]?.getD 0#32).toNat := by
    have := hk.1.nc_le; rw [h16] at this; have := hk.2.2.2.2.2.1; omega
  refine ⟨hok', hlen.trans hk.2.1,
    fun i hi => (hkeep i (by omega) (by omega) (by omega) (Or.inl (by omega))
      (Or.inl (by omega)) (Or.inl (by omega))).trans (hk.2.2.1 i hi),
    (hkeep 4194 (by omega) (by omega) (by omega) (Or.inl (by decide))
      (Or.inl (by omega)) (Or.inl (by omega))).trans hk.2.2.2.1,
    (hkeep 4214 (by omega) (by omega) (by omega) (Or.inl (by decide))
      (Or.inl (by omega)) (Or.inl (by omega))).trans hk.2.2.2.2.1,
    by rw [hkeep 4193 (by omega) (by omega) (by omega) (Or.inl (by decide))
      (Or.inl (by omega)) (Or.inl (by omega))]; exact hk.2.2.2.2.2.1,
    fun cid hc => (hkeep (4224 + 37 * (scr0[4214]?.getD 0#32).toNat + cid) (by omega)
      (by omega) (by omega) (Or.inr (by rw [h16]; omega)) (Or.inr (by rw [h16]; omega))
      (Or.inr (by rw [h16]; omega))).trans (hk.2.2.2.2.2.2.1 cid hc),
    (hkeep 4192 (by omega) (by omega) (by omega) (Or.inl (by decide))
      (Or.inl (by omega)) (Or.inl (by omega))).trans hk.2.2.2.2.2.2.2.1,
    (hkeep 4207 (by omega) (by omega) (by omega) (Or.inl (by decide))
      (Or.inl (by omega)) (Or.inl (by omega))).trans hk.2.2.2.2.2.2.2.2.1,
    (hkeep 4211 (by omega) (by omega) (by omega) (Or.inl (by decide))
      (Or.inl (by omega)) (Or.inl (by omega))).trans hk.2.2.2.2.2.2.2.2.2.1,
    (hkeep 4215 (by omega) (by omega) (by omega) (Or.inl (by decide))
      (Or.inl (by omega)) (Or.inl (by omega))).trans hk.2.2.2.2.2.2.2.2.2.2.1,
    (hkeep 4216 (by omega) (by omega) (by omega) (Or.inl (by decide))
      (Or.inl (by omega)) (Or.inl (by omega))).trans hk.2.2.2.2.2.2.2.2.2.2.2.1,
    fun i ha hb' => (hkeep i (by omega) (by omega) (by omega) (Or.inr (by rw [h16]; omega))
      (Or.inr (by rw [h16]; omega)) (Or.inr (by rw [h16]; omega))).trans
      (hk.2.2.2.2.2.2.2.2.2.2.2.2 i ha hb')⟩

private theorem fidSolveKeep_of_prop {scr0 scr scr' : List (BitVec 32)}
    (hk : FidSolveKeep scr0 scr) (hok' : FidK6BufOk scr') (hlen : scr'.length = scr.length)
    (hlo : ∀ i < 4195, scr'[i]? = scr[i]?)
    (hhi : ∀ i, 4205 ≤ i → i < 4224 → scr'[i]? = scr[i]?)
    (hmet : ∀ i, 4224 + 29 * (scr[4214]?.getD 0#32).toNat ≤ i →
      i < 4224 + 45 * (scr[4214]?.getD 0#32).toNat → scr'[i]? = scr[i]?) :
    FidSolveKeep scr0 scr' := by
  have h16 := hk.2.2.2.2.1
  have honc_le : (scr0[4194]?.getD 0#32).toNat ≤ 4 * (scr0[4214]?.getD 0#32).toNat := by
    have := hk.1.nc_le; rw [h16] at this; have := hk.2.2.2.2.2.1; omega
  refine ⟨hok', hlen.trans hk.2.1, fun i hi => (hlo i (by omega)).trans (hk.2.2.1 i hi),
    (hlo 4194 (by decide)).trans hk.2.2.2.1,
    (hhi 4214 (by decide) (by decide)).trans hk.2.2.2.2.1,
    by rw [hlo 4193 (by decide)]; exact hk.2.2.2.2.2.1,
    fun cid hc => (hmet (4224 + 37 * (scr0[4214]?.getD 0#32).toNat + cid)
      (by rw [h16]; omega) (by rw [h16]; omega)).trans (hk.2.2.2.2.2.2.1 cid hc),
    (hlo 4192 (by decide)).trans hk.2.2.2.2.2.2.2.1,
    (hhi 4207 (by decide) (by decide)).trans hk.2.2.2.2.2.2.2.2.1,
    (hhi 4211 (by decide) (by decide)).trans hk.2.2.2.2.2.2.2.2.2.1,
    (hhi 4215 (by decide) (by decide)).trans hk.2.2.2.2.2.2.2.2.2.2.1,
    (hhi 4216 (by decide) (by decide)).trans hk.2.2.2.2.2.2.2.2.2.2.2.1,
    fun i ha hb => (hmet i (by rw [h16]; omega) (by rw [h16]; omega)).trans
      (hk.2.2.2.2.2.2.2.2.2.2.2.2 i ha hb)⟩

private theorem fidSolveKeep_of_analyze {scr0 scr scr' : List (BitVec 32)}
    (hk : FidSolveKeep scr0 scr) (hok' : FidK6BufOk scr') (hlen : scr'.length = scr.length)
    (hlo : ∀ i < 4193, scr'[i]? = scr[i]?) (h194 : scr'[4194]? = scr[4194]?)
    (hnc : (scr[4193]?.getD 0#32).toNat ≤ (scr'[4193]?.getD 0#32).toNat)
    (haux : ∀ cid < (scr[4193]?.getD 0#32).toNat,
      scr'[4224 + 37 * (scr[4214]?.getD 0#32).toNat + cid]? =
        scr[4224 + 37 * (scr[4214]?.getD 0#32).toNat + cid]?)
    (h207 : scr'[4207]? = scr[4207]?) (h211 : scr'[4211]? = scr[4211]?)
    (h216 : scr'[4214]? = scr[4214]?) (h217 : scr'[4215]? = scr[4215]?)
    (h218 : scr'[4216]? = scr[4216]?)
    (hun : ∀ i, 4224 + 41 * (scr[4214]?.getD 0#32).toNat ≤ i →
      i < 4224 + 43 * (scr[4214]?.getD 0#32).toNat → scr'[i]? = scr[i]?) :
    FidSolveKeep scr0 scr' := by
  have h16 := hk.2.2.2.2.1
  refine ⟨hok', hlen.trans hk.2.1, fun i hi => (hlo i (by omega)).trans (hk.2.2.1 i hi),
    h194.trans hk.2.2.2.1, h216.trans hk.2.2.2.2.1,
    Nat.le_trans hk.2.2.2.2.2.1 hnc,
    fun cid hc => by
      have h1 := haux cid (Nat.lt_of_lt_of_le hc hk.2.2.2.2.2.1)
      rw [h16] at h1; exact h1.trans (hk.2.2.2.2.2.2.1 cid hc),
    (hlo 4192 (by decide)).trans hk.2.2.2.2.2.2.2.1,
    h207.trans hk.2.2.2.2.2.2.2.2.1, h211.trans hk.2.2.2.2.2.2.2.2.2.1,
    h217.trans hk.2.2.2.2.2.2.2.2.2.2.1, h218.trans hk.2.2.2.2.2.2.2.2.2.2.2.1,
    fun i ha hb => (hun i (by rw [h16]; exact ha) (by rw [h16]; exact hb)).trans
      (hk.2.2.2.2.2.2.2.2.2.2.2.2 i ha hb)⟩

/-! ## 2. `full_k6_prop_fid_wp` -/

private theorem fidPropKeep_swap3 {scr0 scru : List (BitVec 32)} {mv pr w_w repl other : BitVec 32}
    (hku : FidPropKeep scr0 scru) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (hw_lt : w_w.toNat < 8 * mv.toNat) (hrepl_lt : repl.toNat < 2 * mv.toNat)
    (hwb_e : ((4224 + 21 * mv + w_w).setWidth 64).toNat = 4224 + 21 * mv.toNat + w_w.toNat)
    (hwn_e : ((4224 + 13 * mv + w_w).setWidth 64).toNat = 4224 + 13 * mv.toNat + w_w.toNat)
    (hwh_r : ((4224 + 11 * mv + repl).setWidth 64).toNat = 4224 + 11 * mv.toNat + repl.toNat)
    (hpru : (scru[4196]?.getD 0#32).toNat = pr.toNat + 1) (v2 : BitVec 32) :
    let scru3 := ((scru.set ((4224 + 21 * mv + w_w).setWidth 64).toNat other).set
      ((4224 + 13 * mv + w_w).setWidth 64).toNat v2).set
      ((4224 + 11 * mv + repl).setWidth 64).toNat w_w
    FidPropKeep scr0 scru3 ∧ (scru3[4196]?.getD 0#32).toNat = pr.toNat + 1 := by
  refine ⟨fidPropKeep_of_set_lo (fidPropKeep_of_set_lo (fidPropKeep_of_set_lo hku
    _ other (by rw [hwb_e, hmv_eq]; omega) (by rw [hwb_e, hmv_eq]; omega))
    _ v2 (by rw [hwn_e, hmv_eq]; omega) (by rw [hwn_e, hmv_eq]; omega))
    _ w_w (by rw [hwh_r, hmv_eq]; omega) (by rw [hwh_r, hmv_eq]; omega), ?_⟩
  rw [List.getElem?_set_ne (by rw [hwh_r]; omega), List.getElem?_set_ne (by rw [hwn_e]; omega),
    List.getElem?_set_ne (by rw [hwb_e]; omega)]
  exact hpru

private theorem fidPropKeep_set_lo_pr {scr0 scr : List (BitVec 32)}
    {k c : Nat} {mv off : BitVec 32} (hk : FidPropKeep scr0 scr)
    (hmv_eq : scr0[4214]?.getD 0#32 = mv) (hk_lo : 9 ≤ k) (hk_hi : k + c ≤ 29)
    (hoff : off.toNat < c * mv.toNat)
    (he : ((4224 + k * mv + off).setWidth 64).toNat = 4224 + k * mv.toNat + off.toNat)
    {pr : BitVec 32} (hpr : (scr[4196]?.getD 0#32).toNat = pr.toNat + 1) (nxt : BitVec 32) :
    let scr' := scr.set ((4224 + k * mv + off).setWidth 64).toNat nxt
    FidPropKeep scr0 scr' ∧ (scr'[4196]?.getD 0#32).toNat = pr.toNat + 1 := by
  have h1 := Nat.mul_le_mul_right mv.toNat hk_lo
  have h2 := Nat.mul_le_mul_right mv.toNat hk_hi
  rw [Nat.add_mul] at h2
  refine ⟨fidPropKeep_of_set_lo hk _ nxt (by rw [he, hmv_eq]; omega)
    (by rw [he, hmv_eq]; omega), ?_⟩
  rw [List.getElem?_set_ne (by rw [he]; omega)]; exact hpr

private theorem fidAnaKeep_set_45_2 {scr0 scr : List (BitVec 32)} {mv x y : BitVec 32}
    (hk : FidAnaKeep scr0 scr) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (he : ((4224 + 45 * mv + x + y).setWidth 64).toNat = 4224 + 45 * mv.toNat + x.toNat + y.toNat)
    (v : BitVec 32) :
    FidAnaKeep scr0 (scr.set ((4224 + 45 * mv + x + y).setWidth 64).toNat v) :=
  fidAnaKeep_of_set_ge hk _ v (by rw [he, hmv_eq]; omega)

private theorem fidAnaKeep_set_45_3 {scr0 scr : List (BitVec 32)} {mv x y z : BitVec 32}
    (hk : FidAnaKeep scr0 scr) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (he : ((4224 + 45 * mv + x + y + z).setWidth 64).toNat =
      4224 + 45 * mv.toNat + x.toNat + y.toNat + z.toNat)
    (v : BitVec 32) :
    FidAnaKeep scr0 (scr.set ((4224 + 45 * mv + x + y + z).setWidth 64).toNat v) :=
  fidAnaKeep_of_set_ge hk _ v (by rw [he, hmv_eq]; omega)

private theorem fidAna_commit_bnds {scrr : List (BitVec 32)} {mv nc_m off_m nkl nres : BitVec 32}
    (h4193 : 4193 < scrr.length)
    (hco : ((4224 + 29 * mv + nc_m).setWidth 64).toNat < scrr.length)
    (hcm : ((4224 + 33 * mv + nc_m).setWidth 64).toNat < scrr.length)
    (hca : ((4224 + 37 * mv + nc_m).setWidth 64).toNat < scrr.length) :
    ((4224 + 29 * mv + nc_m).setWidth 64).toNat < (scrr.set 4206 (off_m + nkl + nres)).length ∧
    ((4224 + 33 * mv + nc_m).setWidth 64).toNat < ((scrr.set 4206 (off_m + nkl + nres)).set
        ((4224 + 29 * mv + nc_m).setWidth 64).toNat off_m).length ∧
    ((4224 + 37 * mv + nc_m).setWidth 64).toNat < (((scrr.set 4206 (off_m + nkl + nres)).set
        ((4224 + 29 * mv + nc_m).setWidth 64).toNat off_m).set
        ((4224 + 33 * mv + nc_m).setWidth 64).toNat (nkl ||| 0x40000000#32)).length ∧
    4193 < ((((scrr.set 4206 (off_m + nkl + nres)).set
        ((4224 + 29 * mv + nc_m).setWidth 64).toNat off_m).set
        ((4224 + 33 * mv + nc_m).setWidth 64).toNat (nkl ||| 0x40000000#32)).set
        ((4224 + 37 * mv + nc_m).setWidth 64).toNat nres).length := by
  simp only [List.length_set]; exact ⟨hco, hcm, hca, h4193⟩

private theorem fidPropKeep_set_4196 {scr0 scr : List (BitVec 32)}
    (hk : FidPropKeep scr0 scr) (v : BitVec 32) : FidPropKeep scr0 (scr.set 4196 v) :=
  fidPropKeep_of_set hk 4196 v (by decide) (Or.inl (by decide)) (Or.inl (by decide))
    (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))

private theorem fidPropKeep_set_4204 {scr0 scr : List (BitVec 32)}
    (hk : FidPropKeep scr0 scr) (v : BitVec 32) : FidPropKeep scr0 (scr.set 4204 v) :=
  fidPropKeep_of_set hk 4204 v (by decide) (Or.inr (by decide)) (Or.inl (by decide))
    (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))

private theorem fidProp_clause_ok_bnds {scr0 scrw : List (BitVec 32)}
    {mv nc acap cid off sz : BitVec 32}
    (_h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (_h4193 : 4193 < scr0.length) (hnc_eq : scr0[4193]?.getD 0#32 = nc)
    (_h4207 : 4207 < scr0.length) (hac_eq : scr0[4207]?.getD 0#32 = acap)
    (_hmv_hi : mv.toNat ≤ 8192) (_hnc_le : nc.toNat ≤ 4 * mv.toNat)
    (hkw : FidPropKeep scr0 scrw) (hcid : cid.toNat < nc.toNat)
    (hco_e : ((4224 + 29 * mv + cid).setWidth 64).toNat = 4224 + 29 * mv.toNat + cid.toNat)
    (hcm_e : ((4224 + 33 * mv + cid).setWidth 64).toNat = 4224 + 33 * mv.toNat + cid.toNat)
    (hco_b : ((4224 + 29 * mv + cid).setWidth 64).toNat < scrw.length)
    (hcm_b : ((4224 + 33 * mv + cid).setWidth 64).toNat < scrw.length)
    (hoff_d : scrw[((4224 + 29 * mv + cid).setWidth 64).toNat]'hco_b = off)
    (hsz_d : (scrw[((4224 + 33 * mv + cid).setWidth 64).toNat]'hcm_b) &&& 0xFFFF#32 = sz) :
    off.toNat + sz.toNat ≤ acap.toNat ∧
    4224 + 45 * mv.toNat + acap.toNat ≤ scrw.length := by
  have hlw := hkw.2.1; have hmin := hkw.1.base_ge; have hmv_w := fidPropKeep_mv hkw
  have hnc_w : scrw[4193]?.getD 0#32 = nc := by rw [hkw.2.2.1 4193 (by decide), hnc_eq]
  have hac_w : scrw[4207]?.getD 0#32 = acap := by
    rw [hkw.2.2.2.2.1 4207 (by decide) (by decide), hac_eq]
  have hcl_w := hkw.1.clause_ok (cid := cid.toNat) (by rw [hnc_w]; exact hcid)
  dsimp only at hcl_w; rw [hmv_w, hmv_eq, hac_w] at hcl_w
  have hoff_eq : (scrw[4224 + 29 * mv.toNat + cid.toNat]?.getD 0#32) = off := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hoff_d]
    exact m8_k6_get_congr hco_e.symm _ _
  have hcm_eq : (scrw[4224 + 33 * mv.toNat + cid.toNat]?.getD 0#32) =
      scrw[((4224 + 33 * mv + cid).setWidth 64).toNat]'hcm_b := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact m8_k6_get_congr hcm_e.symm _ _
  rw [hoff_eq, hcm_eq, hsz_d] at hcl_w
  have hlen_w := hkw.1.length_ge; rw [hmv_w, hmv_eq, hac_w] at hlen_w
  exact ⟨hcl_w.1, hlen_w⟩

private theorem fidProp_sz2 {scr0 scrw : List (BitVec 32)} {mv nc w_w cid sz : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv) (_hlw : scrw.length = scr0.length)
    (_hmin : 15744 ≤ scr0.length) (hmv_hi : mv.toNat ≤ 8192) (hnc_le : nc.toNat ≤ 4 * mv.toNat)
    (hw_lt : w_w.toNat < 2 * nc.toNat) (hcid_eq : cid = w_w >>> (1 : Nat))
    (hcm_e : ((4224 + 33 * mv + cid).setWidth 64).toNat = 4224 + 33 * mv.toNat + cid.toNat)
    (hcm_b : ((4224 + 33 * mv + cid).setWidth 64).toNat < scrw.length)
    (hsz_eq : (scrw[((4224 + 33 * mv + cid).setWidth 64).toNat]'hcm_b) &&& 0xFFFF#32 = sz)
    {hb : (4224 + 33 * (scr0[4214]'h4214).toNat + w_w.toNat / 2) % 4294967296 < scrw.length}
    (hc : ¬ (scrw[(4224 + 33 * (scr0[4214]'h4214).toNat + w_w.toNat / 2) %
        4294967296]'hb).toNat % 65536 < 2) :
    2 ≤ sz.toNat := by
  have hcm_get : scrw[(4224 + 33 * (scr0[4214]'h4214).toNat + w_w.toNat / 2) % 4294967296]'hb =
      scrw[((4224 + 33 * mv + cid).setWidth 64).toNat]'hcm_b :=
    m8_k6_get_congr (by
      rw [hmv_d, hcm_e, Nat.mod_eq_of_lt (by omega), hcid_eq, m8_bv32_lshr1_toNat]) hb hcm_b
  rw [hcm_get, show (scrw[((4224 + 33 * mv + cid).setWidth 64).toNat]'hcm_b).toNat % 65536 =
      sz.toNat from by rw [← hsz_eq, FidK6Tactics.fid_bv32_and_ffff_toNat]] at hc
  exact Nat.le_of_not_lt hc

private theorem fidAnaKeep_set_lt4214 {scr0 scr : List (BitVec 32)}
    (hk : FidAnaKeep scr0 scr) (idx : Nat) (v : BitVec 32)
    (hlo : 4195 ≤ idx := by decide) (h1 : idx ≠ 4199 := by decide)
    (h2 : idx ≠ 4205 := by decide) (h3 : idx ≠ 4206 := by decide)
    (h4 : idx ≠ 4207 := by decide) (h5 : idx ≠ 4211 := by decide)
    (h6 : idx ≠ 4213 := by decide) (h7 : idx ≠ 4214 := by decide)
    (h8 : idx ≠ 4215 := by decide) (h9 : idx ≠ 4216 := by decide)
    (hhi : idx < 4224 := by decide) :
    FidAnaKeep scr0 (scr.set idx v) :=
  fidAnaKeep_of_set hk idx v hlo h1 h2 h3 h4 h5 h6 h7 h8 h9 (Or.inl (by omega))

private theorem fidProp_u32 {a : BitVec 32} {b : Nat} (ha : (a.setWidth 64).toNat = b) :
    b < 4294967296 := by
  rw [← ha, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans a.isLt (by decide))]; exact a.isLt

private theorem fidProp_off_g {scr0 scrw : List (BitVec 32)} {w_w off mv cid : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv) (hcid_d : w_w >>> 1 = cid)
    (hco_e : ((4224 + 29 * mv + cid).setWidth 64).toNat = 4224 + 29 * mv.toNat + cid.toNat)
    (hco_b : ((4224 + 29 * mv + cid).setWidth 64).toNat < scrw.length)
    (hoff_d : scrw[((4224 + 29 * mv + cid).setWidth 64).toNat]'hco_b = off)
    {hb1 : (4224 + 29 * (scr0[4214]'h4214).toNat + w_w.toNat / 2) % 4294967296 < scrw.length} :
    scrw[(4224 + 29 * (scr0[4214]'h4214).toNat + w_w.toNat / 2) % 4294967296]'hb1 = off := by
  have hco_u := fidProp_u32 hco_e
  have hoff_i : (4224 + 29 * (scr0[4214]'h4214).toNat + w_w.toNat / 2) % 4294967296 =
      ((4224 + 29 * mv + cid).setWidth 64).toNat := by
    rw [hmv_d, hco_e]; rw [← hcid_d, m8_bv32_lshr1_toNat] at hco_u ⊢; exact Nat.mod_eq_of_lt hco_u
  rw [m8_k6_get_congr hoff_i hb1 hco_b, hoff_d]

private theorem fidProp_other_lt {scr0 scrw : List (BitVec 32)}
    {w_w off other mv cid slot nv : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv)
    (h4192 : 4192 < scr0.length) (hnv_d : scr0[4192]'h4192 = nv)
    (hcid_d : w_w >>> 1 = cid) (hslot_d : w_w &&& 1#32 = slot)
    (hmv_hi : mv.toNat ≤ 8192) (hnv_le : nv.toNat ≤ mv.toNat)
    (hco_e : ((4224 + 29 * mv + cid).setWidth 64).toNat = 4224 + 29 * mv.toNat + cid.toNat)
    (hco_b : ((4224 + 29 * mv + cid).setWidth 64).toNat < scrw.length)
    (hoff_d : scrw[((4224 + 29 * mv + cid).setWidth 64).toNat]'hco_b = off)
    (hoth_e : ((4224 + 45 * mv + off + (slot ^^^ 1#32)).setWidth 64).toNat =
      4224 + 45 * mv.toNat + off.toNat + (slot ^^^ 1#32).toNat)
    (hoth_b : ((4224 + 45 * mv + off + (slot ^^^ 1#32)).setWidth 64).toNat < scrw.length)
    (hoth_d : scrw[((4224 + 45 * mv + off + (slot ^^^ 1#32)).setWidth 64).toNat]'hoth_b = other)
    {hb1 : (4224 + 29 * (scr0[4214]'h4214).toNat + w_w.toNat / 2) % 4294967296 < scrw.length}
    {hb2 : (4224 + 45 * (scr0[4214]'h4214).toNat +
      (scrw[(4224 + 29 * (scr0[4214]'h4214).toNat + w_w.toNat / 2) % 4294967296]'hb1).toNat +
      (w_w.toNat % 2 + 1 - 2 * (w_w.toNat % 2 % 2))) % 4294967296 < scrw.length}
    (hc : (scrw[(4224 + 45 * (scr0[4214]'h4214).toNat +
      (scrw[(4224 + 29 * (scr0[4214]'h4214).toNat + w_w.toNat / 2) % 4294967296]'hb1).toNat +
      (w_w.toNat % 2 + 1 - 2 * (w_w.toNat % 2 % 2))) % 4294967296]'hb2).toNat <
      (scr0[4192]'h4192).toNat * 2 % 4294967296) :
    other.toNat < 2 * nv.toNat := by
  have hoth_u := fidProp_u32 hoth_e
  have hoff_g := fidProp_off_g h4214 hmv_d hcid_d hco_e hco_b hoff_d (hb1 := hb1)
  have hslot_v : (slot ^^^ 1#32).toNat = w_w.toNat % 2 + 1 - 2 * (w_w.toNat % 2 % 2) := by
    rw [← hslot_d, BitVec.toNat_xor, BitVec.toNat_and,
      show (1#32 : BitVec 32).toNat = 2 ^ 1 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, FidK6Tactics.fid_nat_xor1]
  have hoth_i : (4224 + 45 * (scr0[4214]'h4214).toNat +
      (scrw[(4224 + 29 * (scr0[4214]'h4214).toNat + w_w.toNat / 2) % 4294967296]'hb1).toNat +
      (w_w.toNat % 2 + 1 - 2 * (w_w.toNat % 2 % 2))) % 4294967296 =
      ((4224 + 45 * mv + off + (slot ^^^ 1#32)).setWidth 64).toNat := by
    rw [hoff_g, hmv_d, ← hslot_v, hoth_e, Nat.mod_eq_of_lt hoth_u]
  have hoth_g : scrw[(4224 + 45 * (scr0[4214]'h4214).toNat +
      (scrw[(4224 + 29 * (scr0[4214]'h4214).toNat + w_w.toNat / 2) % 4294967296]'hb1).toNat +
      (w_w.toNat % 2 + 1 - 2 * (w_w.toNat % 2 % 2))) % 4294967296]'hb2 = other := by
    rw [m8_k6_get_congr hoth_i hb2 hoth_b, hoth_d]
  rw [hoth_g, hnv_d, Nat.mod_eq_of_lt (by omega)] at hc; omega

private theorem fidProp_ri_lt {scr0 scrw : List (BitVec 32)} {r_i sz w_w mv cid : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv) (hcid_d : w_w >>> 1 = cid)
    (hcm_e : ((4224 + 33 * mv + cid).setWidth 64).toNat = 4224 + 33 * mv.toNat + cid.toNat)
    (hcm_b : ((4224 + 33 * mv + cid).setWidth 64).toNat < scrw.length)
    (hsz_d : (scrw[((4224 + 33 * mv + cid).setWidth 64).toNat]'hcm_b &&& 0xFFFF#32) = sz)
    {hb1 : (4224 + 33 * (scr0[4214]'h4214).toNat + w_w.toNat / 2) % 4294967296 < scrw.length}
    (hc : r_i.toNat < (scrw[(4224 + 33 * (scr0[4214]'h4214).toNat +
      w_w.toNat / 2) % 4294967296]'hb1).toNat % 65536) : r_i.toNat < sz.toNat := by
  have hcm_u := fidProp_u32 hcm_e
  have h1 : (4224 + 33 * (scr0[4214]'h4214).toNat + w_w.toNat / 2) % 4294967296 =
      ((4224 + 33 * mv + cid).setWidth 64).toNat := by
    rw [hmv_d, hcm_e]; rw [← hcid_d, m8_bv32_lshr1_toNat] at hcm_u ⊢; exact Nat.mod_eq_of_lt hcm_u
  have h1_b : (4224 + 33 * (scr0[4214]'h4214).toNat + w_w.toNat / 2) % 4294967296 < scrw.length :=
    h1 ▸ hcm_b
  rw [← hsz_d, FidK6Tactics.fid_bv32_and_ffff_toNat]; rwa [m8_k6_get_congr h1 h1_b hcm_b] at hc

private theorem fidProp_cand_lt {scr0 scrw : List (BitVec 32)}
    {w_w off r_i cand mv cid nv : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv)
    (h4192 : 4192 < scr0.length) (hnv_d : scr0[4192]'h4192 = nv)
    (hcid_d : w_w >>> 1 = cid) (hmv_hi : mv.toNat ≤ 8192) (hnv_le : nv.toNat ≤ mv.toNat)
    (hco_e : ((4224 + 29 * mv + cid).setWidth 64).toNat = 4224 + 29 * mv.toNat + cid.toNat)
    (hco_b : ((4224 + 29 * mv + cid).setWidth 64).toNat < scrw.length)
    (hoff_d : scrw[((4224 + 29 * mv + cid).setWidth 64).toNat]'hco_b = off)
    (har_e : ((4224 + 45 * mv + off + r_i).setWidth 64).toNat =
      4224 + 45 * mv.toNat + off.toNat + r_i.toNat)
    (har_b : ((4224 + 45 * mv + off + r_i).setWidth 64).toNat < scrw.length)
    (hcand_d : scrw[((4224 + 45 * mv + off + r_i).setWidth 64).toNat]'har_b = cand)
    {hb1 : (4224 + 29 * (scr0[4214]'h4214).toNat + w_w.toNat / 2) % 4294967296 < scrw.length}
    {hb2 : (4224 + 45 * (scr0[4214]'h4214).toNat +
      (scrw[(4224 + 29 * (scr0[4214]'h4214).toNat + w_w.toNat / 2) % 4294967296]'hb1).toNat +
      r_i.toNat) % 4294967296 < scrw.length}
    (hc : (scrw[(4224 + 45 * (scr0[4214]'h4214).toNat +
      (scrw[(4224 + 29 * (scr0[4214]'h4214).toNat + w_w.toNat / 2) % 4294967296]'hb1).toNat +
      r_i.toNat) % 4294967296]'hb2).toNat < (scr0[4192]'h4192).toNat * 2 % 4294967296) :
    cand.toNat < 2 * nv.toNat := by
  have har_u := fidProp_u32 har_e
  have hoff_g := fidProp_off_g h4214 hmv_d hcid_d hco_e hco_b hoff_d (hb1 := hb1)
  have hcand_i : (4224 + 45 * (scr0[4214]'h4214).toNat +
      (scrw[(4224 + 29 * (scr0[4214]'h4214).toNat + w_w.toNat / 2) % 4294967296]'hb1).toNat +
      r_i.toNat) % 4294967296 = ((4224 + 45 * mv + off + r_i).setWidth 64).toNat := by
    rw [hoff_g, hmv_d, har_e, Nat.mod_eq_of_lt har_u]
  have hcand_g : scrw[(4224 + 45 * (scr0[4214]'h4214).toNat +
      (scrw[(4224 + 29 * (scr0[4214]'h4214).toNat + w_w.toNat / 2) % 4294967296]'hb1).toNat +
      r_i.toNat) % 4294967296]'hb2 = cand := by rw [m8_k6_get_congr hcand_i hb2 har_b, hcand_d]
  rw [hcand_g, hnv_d, Nat.mod_eq_of_lt (by omega)] at hc; omega

/-- Parametric `Func.wp` proof for `full_k6_prop_fid`, certifying `fidK6PropSpec`. -/
theorem full_k6_prop_fid_wp (Γ : Env) (hTicks : ∀ a m Q X, fidK6AddTicksSpec a m Q X →
      Γ "full_fid_k6_add_ticks" [i64, i64] [] a m Q X)
    (hAssign : ∀ a m Q X, fidK6AssignSpec a m Q X →
      Γ "full_k6_assign_fid" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, fidK6PropSpec a m Q X → Func.wp Γ full_k6_prop_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hok, hm0, hQ⟩ := fidK6PropSpec_elim hSpec
  let scr0 := s.scratch.scratch_buf
  have hscr_len : scr0.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hmin : 15744 ≤ scr0.length := hok.min_len
  have hsc15 : 15744 ≤ c.scratch_cap := by omega
  have hmv_lo : 256 ≤ (scr0[4214]?.getD 0#32).toNat := hok.mv_lo
  have hmv_hi : (scr0[4214]?.getD 0#32).toNat ≤ 8192 := hok.mv_hi
  have hbge : 4224 + 45 * (scr0[4214]?.getD 0#32).toNat ≤ scr0.length := hok.base_ge
  have hlen_ge := hok.length_ge; have hlen_lt := hok.length_lt
  have h4214 : 4214 < scr0.length := by omega
  have h4192 : 4192 < scr0.length := by omega
  have h4193 : 4193 < scr0.length := by omega
  have h4207 : 4207 < scr0.length := by omega
  let mv := scr0[4214]'h4214
  have hmv_o : (scr0[(@OfNat.ofNat Nat 4214 _)]'h4214).toNat = mv.toNat := rfl
  let nv := scr0[4192]'h4192
  have hnv_o : (scr0[(@OfNat.ofNat Nat 4192 _)]'h4192).toNat = nv.toNat := rfl
  let nc := scr0[4193]'h4193
  have hnc_o : (scr0[(@OfNat.ofNat Nat 4193 _)]'h4193).toNat = nc.toNat := rfl
  let acap := scr0[4207]'h4207
  have hacap_o : (scr0[(@OfNat.ofNat Nat 4207 _)]'h4207).toNat = acap.toNat := rfl
  have hmv_eq : (scr0[4214]?.getD 0#32) = mv := m8_k6_get_eq h4214
  have hnc_eq : (scr0[4193]?.getD 0#32) = nc := m8_k6_get_eq h4193
  have hac_eq : (scr0[4207]?.getD 0#32) = acap := m8_k6_get_eq h4207
  rw [hmv_eq] at hmv_lo hmv_hi hbge hlen_ge; rw [hac_eq] at hlen_ge
  have hm0' : (FullMem c (m8ScrSt s scr0) ⋆ R) m0 := by rwa [m8ScrSt_self]
  have hret_noop : Q (0xFFFFFFFF#32, ()) m0 :=
    hQ 0xFFFFFFFF#32 scr0 m0 hok hscr_len (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) hm0
  have hfinish : ∀ (r : BitVec 32) (scrf : List (BitVec 32)) (mf : Mem 64),
      FidPropKeep scr0 scrf → (FullMem c (m8ScrSt s scrf) ⋆ R) mf → Q (r, ()) mf :=
    fun r scrf mf hkf hmf => hQ r scrf mf hkf.1 (hkf.2.1.trans hscr_len) hkf.2.2.1 hkf.2.2.2.1
      hkf.2.2.2.2.1 hkf.2.2.2.2.2.1 hkf.2.2.2.2.2.2.1 hkf.2.2.2.2.2.2.2 (m8ScrSt_eq s scrf ▸ hmf)
  clear hQ hSpec hm0; unfold Func.wp full_k6_prop_fid_body
  c0_hsplit
  · c0_hsteps!; exact hret_noop
  · c0_hsplit
    · c0_hsteps!; exact hret_noop
    · c0_hsplit
      · c0_hsteps!; exact hret_noop
      · have hnv_le : nv.toNat ≤ mv.toNat := Nat.le_of_not_lt hc; clear hc
        c0_hsplit
        · c0_hsteps!; exact hret_noop
        · have hnc_le : nc.toNat ≤ 4 * mv.toNat := by fid_omega
          clear hc
          have hmc_n : (mv <<< (2 : Nat)).toNat = 4 * mv.toNat := fid_bv32_shl2_toNat (by omega)
          have hmc2_n : ((mv <<< (2 : Nat)) <<< (1 : Nat)).toNat = 8 * mv.toNat := by
            rw [m8_bv32_shl1_toNat (by omega), hmc_n]; omega
          have hnc2_n : (nc <<< (1 : Nat)).toNat = 2 * nc.toNat := m8_bv32_shl1_toNat (by omega)
          have hnv2_n : (nv <<< (1 : Nat)).toNat = 2 * nv.toNat := m8_bv32_shl1_toNat (by omega)
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i64])
            (fun rem (ticks, ()) mo => ∃ scro : List (BitVec 32), FidPropKeep scr0 scro ∧
              rem = mv.toNat - (scro[4196]?.getD 0#32).toNat ∧ (FullMem c (m8ScrSt s scro) ⋆ R) mo)
            ?_ ?_
          · rintro Lo rem ⟨ticks, ⟨⟩⟩ mo hLo ⟨scro, hko, rfl, hmo⟩
            clear hm0' hret_noop; have hlo : scro.length = scr0.length := hko.2.1
            have hmin_o : 15744 ≤ scro.length := by omega
            have h4196_o : 4196 < scro.length := by omega
            let pr := scro[4196]'h4196_o
            have hpr_o : (scro[(@OfNat.ofNat Nat 4196 _)]'h4196_o).toNat = pr.toNat := rfl
            have hpr_eq : (scro[4196]?.getD 0#32) = pr := m8_k6_get_eq h4196_o
            c0_hsteps_nogrp
            refine wp_join0 (fun mf => ∃ scrf : List (BitVec 32), FidPropKeep scr0 scrf ∧
                (FullMem c (m8ScrSt s scrf) ⋆ R) mf)
              (fun _ mf ⟨scrf, hkf, hmf⟩ => by
                c0_hsteps_nogrp; fid_call hTicks
                refine fidK6AddTicksSpec_intro rfl
                  (fidScr_lengthsOk hlen (hkf.2.1.trans hscr_len)) hsc15
                  (m8ScrSt_eq s scrf ▸ hmf) ?_
                intro tk' m' scr' hm'
                c0_hsteps!; exact hfinish 0xFFFFFFFF#32 _ m' (fidPropKeep_set_4204 hkf tk')
                  (by rwa [m8ScrSt_eq]))
              ?_
            intro Jex hJex
            c0_hsplit
            · c0_hsplit
              · have hpr_lt : pr.toNat < mv.toNat := hc
                clear hc
                have hpr1 : (pr + 1#32).toNat = pr.toNat + 1 :=
                  m8_bv32_add1_toNat hpr_lt (by omega)
                have htr_e := fid_k6_off_add (mv := mv) (k := 5) (x := pr)
                  hmv_hi (by decide) (by omega)
                have htr_b : ((4224 + 5 * mv + pr).setWidth 64).toNat < scro.length := by
                  rw [hlo, htr_e]; omega
                let lit := scro[((4224 + 5 * mv + pr).setWidth 64).toNat]'htr_b
                let scro1 := scro.set 4196 (pr + 1#32)
                have hko1 : FidPropKeep scr0 scro1 := fidPropKeep_set_4196 hko (pr + 1#32)
                have hlo1 : scro1.length = scr0.length := hko1.2.1
                have hpr_next : (scro1[4196]?.getD 0#32).toNat = pr.toNat + 1 := by
                  dsimp only [scro1]; rw [List.getElem?_set_self h4196_o, Option.getD_some, hpr1]
                c0_hsplit
                · c0_hsteps!
                  exact hLo (mv.toNat - (scro1[4196]?.getD 0#32).toNat) (ticks, ()) _
                    (by rw [hpr_next, hpr_eq]; omega) ⟨scro1, hko1, rfl, hm⟩
                · have hlit_lt : lit.toNat < 2 * nv.toNat := by
                    have hc' := hc
                    fid_norm_ofnat
                    (try simp (disch := omega) only [bv_c0, Nat.reducePow, BitVec.reduceToNat,
                      Nat.mod_eq_of_lt] at hc')
                    have h1 : (scro[4224 + 5 * (scr0[4214]'h4214).toNat +
                          (scro[4196]'(by omega)).toNat]'(by rw [hlo]; omega)).toNat =
                          lit.toNat :=
                      congrArg BitVec.toNat (m8_k6_get_congr htr_e.symm _ _)
                    try rw [h1] at hc'
                    dsimp only [nv]; omega
                  let nl := lit ^^^ 1#32
                  have hnl_lt : nl.toNat < 2 * nv.toNat := (m8_bv32_xor1_lt lit hlit_lt).2
                  have hwh_nl := fid_k6_off_add (mv := mv) (k := 11) (x := nl)
                    hmv_hi (by decide) (by omega)
                  have hwh_nl_b : ((4224 + 11 * mv + nl).setWidth 64).toNat <
                      scro1.length := by rw [hlo1, hwh_nl]; omega
                  c0_hsteps_nogrp
                  -- Inner watch loop: measure `8 * mv - wsteps`
                  refine wp_loop_group (ts := [i64, i64, i32, i32, i32])
                    (fun rem_w (tk_w, vis_w, prev_w, w_w, ws_w, ()) mw =>
                      ∃ scrw : List (BitVec 32), FidPropKeep scr0 scrw ∧
                        (scrw[4196]?.getD 0#32).toNat = pr.toNat + 1 ∧
                        ws_w.toNat ≤ 8 * mv.toNat ∧
                        rem_w = 8 * mv.toNat - ws_w.toNat ∧
                        (FullMem c (m8ScrSt s scrw) ⋆ R) mw)
                    ?_ ?_
                  · rintro Lw rem_w ⟨tk_w, vis_w, prev_w, w_w, ws_w, ⟨⟩⟩ mw hLw
                      ⟨scrw, hkw, hprw, hws_le, rfl, hmw⟩
                    clear hko hJex; have hlw : scrw.length = scr0.length := hkw.2.1
                    have hmin_w : 15744 ≤ scrw.length := by omega
                    c0_hsteps_nogrp
                    refine wp_join0 (fun mw' => ∃ scrw' : List (BitVec 32),
                        FidPropKeep scr0 scrw' ∧
                        (scrw'[4196]?.getD 0#32).toNat = pr.toNat + 1 ∧
                        (FullMem c (m8ScrSt s scrw') ⋆ R) mw')
                      (fun _ mw' ⟨scrw', hkw', hprw', hmw'⟩ => by
                        c0_hsteps!; exact hLo (mv.toNat - (scrw'[4196]?.getD 0#32).toNat) _ mw'
                          (by rw [hprw', hpr_eq]; omega) ⟨scrw', hkw', rfl, hmw'⟩)
                      (fun Js hJs => by
                        c0_hsplit
                        rotate_left
                        · c0_hsteps!; exact hJs mw ⟨scrw, hkw, hprw, hmw⟩
                        have hw_lt : w_w.toNat < 2 * nc.toNat := by
                          have hc' := hc; fid_norm_ofnat
                          simp only [Nat.reducePow,
                            Nat.mod_eq_of_lt (by dsimp only [nc] at hnc_le ⊢; omega :
                              (scr0[4193]'h4193).toNat * 2 < 2 ^ 32)] at hc'
                          dsimp only [nc]; omega
                        clear hc
                        c0_hsplit
                        rotate_left
                        · c0_hsteps!; exact hJs mw ⟨scrw, hkw, hprw, hmw⟩
                        have hws_lt : ws_w.toNat < 8 * mv.toNat := by
                          have hc' := hc; fid_norm_ofnat
                          simp only [Nat.reducePow] at hc'
                          rw [Nat.mod_eq_of_lt (by omega : (scr0[4214]'h4214).toNat * 4 < 2 ^ 32),
                            Nat.mod_eq_of_lt (by omega :
                              (scr0[4214]'h4214).toNat * 4 * 2 < 2 ^ 32)] at hc'
                          dsimp only [mv]; omega
                        clear hc
                        have hws1 : (ws_w + 1#32).toNat = ws_w.toNat + 1 :=
                          m8_bv32_add1_toNat hws_lt (by omega)
                        have hwn_e := fid_k6_off_add (mv := mv) (k := 13) (x := w_w)
                          hmv_hi (by decide) (by omega)
                        have hwb_e := fid_k6_off_add (mv := mv) (k := 21) (x := w_w)
                          hmv_hi (by decide) (by omega)
                        have hwn_b : ((4224 + 13 * mv + w_w).setWidth 64).toNat <
                            scrw.length := by rw [hlw, hwn_e]; omega
                        have hwb_b : ((4224 + 21 * mv + w_w).setWidth 64).toNat <
                            scrw.length := by rw [hlw, hwb_e]; omega
                        let nxt := scrw[((4224 + 13 * mv + w_w).setWidth 64).toNat]'hwn_b
                        let wb := scrw[((4224 + 21 * mv + w_w).setWidth 64).toNat]'hwb_b
                        let bv := wb &&& 0x7FFFFFFF#32
                        c0_hsplit
                        · c0_hsteps!
                          exact hLw (8 * mv.toNat - (ws_w + 1#32).toNat)
                            (tk_w, vis_w + 1#64, w_w, nxt, ws_w + 1#32, ()) mw (by omega)
                            ⟨scrw, hkw, hprw, by omega, rfl, hmw⟩
                        · have hbv_lt : bv.toNat < 2 * nv.toNat := by
                            have hc' := hc; fid_norm_ofnat
                            simp only [Nat.reducePow, BitVec.reduceToNat,
                              Nat.mod_eq_of_lt (by dsimp only [nv] at hnv_le ⊢; omega :
                                (scr0[4192]'h4192).toNat * 2 < 2 ^ 32)] at hc'
                            have hwb_g : scrw[(4224 + 21 * mv.toNat + w_w.toNat) %
                                4294967296]'(by rw [hlw]; omega) = wb :=
                              m8_k6_get_congr (by rw [hwb_e]; omega) _ _
                            try rw [hwb_g] at hc'
                            have hbv_eq : wb.toNat % 2147483648 = bv.toNat := by
                              dsimp only [bv]; rw [BitVec.toNat_and,
                                show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl,
                                Nat.and_two_pow_sub_one_eq_mod]
                            rw [hbv_eq] at hc'; dsimp only [nv]; omega
                          clear hc
                          have hvl_bv := fid_k6_off_add (mv := mv) (k := 9) (x := bv) hmv_hi
                            (by decide) (by omega)
                          have hvl_bvb :
                              ((4224 + 9 * mv + bv).setWidth 64).toNat < scrw.length := by
                            rw [hlw, hvl_bv]; omega
                          c0_hsplit
                          · c0_hsteps!
                            exact hLw (8 * mv.toNat - (ws_w + 1#32).toNat)
                              (tk_w, vis_w + 1#64, w_w, nxt, ws_w + 1#32, ()) mw (by omega)
                              ⟨scrw, hkw, hprw, by omega, rfl, hmw⟩
                          · let cid := w_w >>> (1 : Nat)
                            have hcid_lt : cid.toNat < nc.toNat := by
                              dsimp only [cid]; rw [m8_bv32_lshr1_toNat]; omega
                            c0_hsplit
                            · c0_hsplit
                              · c0_hsteps_nogrp; fid_call hTicks
                                refine fidK6AddTicksSpec_intro rfl
                                  (fidScr_lengthsOk hlen (hlw.trans hscr_len)) hsc15
                                  (m8ScrSt_eq s scrw ▸ hmw) ?_
                                intro tk' m' scr' hm'; c0_hsteps!
                                have hkf' := fidPropKeep_of_set hkw 4204 tk' (by decide)
                                  (Or.inr (by decide)) (Or.inl (by decide)) (Or.inl (by omega))
                                  (Or.inl (by omega)) (Or.inl (by omega))
                                exact hfinish cid _ m' hkf' (by rwa [m8ScrSt_eq])
                              · c0_hsteps_nogrp
                                refine wp_join0
                                  (fun mw' => ∃ scrw' : List (BitVec 32), FidPropKeep scr0 scrw' ∧
                                    (scrw'[4196]?.getD 0#32).toNat = pr.toNat + 1 ∧
                                    (FullMem c (m8ScrSt s scrw') ⋆ R) mw')
                                  (fun _ mw' ⟨scrw', hkw', hprw', hmw'⟩ => by
                                    c0_hsteps!; exact hLw (8 * mv.toNat - (ws_w + 1#32).toNat)
                                      (tk_w, vis_w + 1#64, w_w, nxt, ws_w + 1#32, ()) mw' (by omega)
                                      ⟨scrw', hkw', hprw', by omega, rfl, hmw'⟩)
                                  (fun Js_b hJs_b => by
                                    c0_hsplit
                                    · c0_hsteps_nogrp; fid_call hAssign
                                      refine fidK6AssignSpec_intro rfl
                                        (fidScr_lengthsOk hlen (hlw.trans hscr_len))
                                        (m8ScrSt_buf s scrw ▸ hkw.1) (m8ScrSt_eq s scrw ▸ hmw) ?_
                                      intro scr_a m_a hla hka hm_a
                                      have hkw_a := fidPropKeep_of_assign hkw
                                        (hla.trans (hscr_len.symm.trans hlw.symm))
                                        (fun idx hi => hka idx (by omega))
                                      have hpra :
                                          (scr_a[4196]?.getD 0#32).toNat = pr.toNat + 1 := by
                                        rw [hka 4196 (by omega) (by decide) (by decide)
                                          (Or.inl (by decide)) (Or.inl (by omega))
                                          (Or.inl (by omega))]; exact hprw
                                      c0_hsteps!
                                      exact hJs_b m_a ⟨scr_a, hkw_a, hpra, by rwa [m8ScrSt_eq]⟩
                                    · c0_hsteps!; exact hJs_b mw ⟨scrw, hkw, hprw, hmw⟩)
                            · let slot := w_w &&& 1#32
                              have hco_e := fid_k6_off_add (mv := mv) (k := 29) (x := cid) hmv_hi
                                (by decide) (by omega)
                              have hcm_e := fid_k6_off_add (mv := mv) (k := 33) (x := cid) hmv_hi
                                (by decide) (by omega)
                              have hco_b : ((4224 + 29 * mv + cid).setWidth 64).toNat <
                                  scrw.length := by rw [hlw, hco_e]; omega
                              have hcm_b : ((4224 + 33 * mv + cid).setWidth 64).toNat <
                                  scrw.length := by rw [hlw, hcm_e]; omega
                              let off := scrw[((4224 + 29 * mv + cid).setWidth 64).toNat]'hco_b
                              let sz := (scrw[((4224 + 33 * mv + cid).setWidth 64).toNat]'hcm_b) &&&
                                0xFFFF#32
                              have hsz_le : sz.toNat ≤ 65535 := m8_and_ffff_le _
                              have ⟨hos_le, hlen_w⟩ := fidProp_clause_ok_bnds h4214 hmv_eq h4193
                                hnc_eq h4207 hac_eq hmv_hi hnc_le hkw hcid_lt hco_e hcm_e hco_b
                                hcm_b rfl rfl
                              have hos_bnd : off.toNat + sz.toNat ≤ acap.toNat := hos_le
                              c0_hsplit
                              · c0_hsteps!
                                exact hLw (8 * mv.toNat - (ws_w + 1#32).toNat)
                                  (tk_w, vis_w + 1#64, w_w, nxt, ws_w + 1#32, ()) mw (by omega)
                                  ⟨scrw, hkw, hprw, by omega, rfl, hmw⟩
                              · have hsz2 : 2 ≤ sz.toNat := by
                                  have hc' := hc; fid_norm_ofnat
                                  simp only [Nat.reducePow, BitVec.reduceToNat] at hc'
                                  exact fidProp_sz2 h4214 rfl hlw hmin hmv_hi hnc_le hw_lt rfl
                                    hcm_e hcm_b rfl hc'
                                clear hc
                                c0_hsplit
                                · c0_hsteps!
                                  exact hLw (8 * mv.toNat - (ws_w + 1#32).toNat)
                                    (tk_w, vis_w + 1#64, w_w, nxt, ws_w + 1#32, ()) mw (by omega)
                                    ⟨scrw, hkw, hprw, by omega, rfl, hmw⟩
                                · have hso1_lt : (slot ^^^ 1#32).toNat < 2 := m8k6_slot_xor1_lt
                                  have hsl_lt : slot.toNat < 2 := by
                                    dsimp only [slot]; rw [BitVec.toNat_and,
                                      show (1#32 : BitVec 32).toNat = 1 from rfl]
                                    have := Nat.and_le_right (n := w_w.toNat) (m := 1); omega
                                  have hoth_e := fid_k6_off_add2 (mv := mv) (k := 45)
                                    (x := off) (y := slot ^^^ 1#32) hmv_hi (by decide) (by omega)
                                  have hoth_b : ((4224 + 45 * mv + off + (slot ^^^ 1#32)).setWidth
                                        64).toNat < scrw.length := by rw [hoth_e]; omega
                                  let other :=
                                    scrw[((4224 + 45 * mv + off + (slot ^^^ 1#32)).setWidth
                                      64).toNat]'hoth_b
                                  c0_hsplit
                                  · c0_hsteps!
                                    exact hLw (8 * mv.toNat - (ws_w + 1#32).toNat)
                                      (tk_w, vis_w + 1#64, w_w, nxt, ws_w + 1#32, ()) mw (by omega)
                                      ⟨scrw, hkw, hprw, by omega, rfl, hmw⟩
                                  · have hoth_lt : other.toNat < 2 * nv.toNat := by
                                      have hc' := hc; clear hc; fid_norm_ofnat
                                      simp only [Nat.reducePow, BitVec.reduceToNat] at hc'
                                      exact fidProp_other_lt h4214 rfl h4192 rfl rfl rfl hmv_hi
                                        hnv_le hco_e hco_b rfl hoth_e hoth_b rfl
                                        (Nat.lt_of_not_le hc')
                                    have hv_oth := fid_k6_off_add (mv := mv) (k := 9) (x := other)
                                      hmv_hi (by decide) (by omega)
                                    have hv_othb : ((4224 + 9 * mv + other).setWidth 64).toNat
                                        < scrw.length := by rw [hlw, hv_oth]; omega
                                    c0_hsplit
                                    · c0_hsteps!
                                      have hkw' := fidPropKeep_of_set_lo hkw
                                        ((4224 + 21 * mv + w_w).setWidth 64).toNat other
                                        (by rw [hwb_e, hmv_eq]; omega)
                                        (by rw [hwb_e, hmv_eq]; omega)
                                      exact hLw (8 * mv.toNat - (ws_w + 1#32).toNat)
                                        (tk_w + 1#64, vis_w + 1#64, w_w, nxt, ws_w + 1#32, ()) _
                                        (by omega)
                                        ⟨_, hkw', by
                                          rw [List.getElem?_set_ne (by rw [hwb_e]; omega)]
                                          exact hprw, by omega, rfl, hm⟩
                                    · -- Scan `r = 2 ..< sz` for replacement literal
                                      c0_hsteps_nogrp
                                      refine wp_join_state_pure (ts := [i32, i32, i32])
                                        (α := BitVec 32 × BitVec 32 × BitVec 32)
                                        (fun x => (x.1, x.2.1, x.2.2, ()))
                                        (fun x => x.2.1 = 0xFFFFFFFF#32 ∨
                                          (x.2.1.toNat < sz.toNat ∧ x.2.2.toNat < 2 * nv.toNat))
                                        ?_ ?_
                                      · rintro _ ⟨_, ri, repl⟩ hri
                                        c0_hsplit
                                        · have ⟨hri_lt, hrepl_lt⟩ := hri.resolve_left hc
                                          clear hc; dsimp only at hri_lt hrepl_lt
                                          have hsl_e := fid_k6_off_add2 (mv := mv) (k := 45)
                                            (x := off) (y := slot) hmv_hi (by decide) (by omega)
                                          have hri_e := fid_k6_off_add2 (mv := mv) (k := 45)
                                            (x := off) (y := ri) hmv_hi (by decide) (by omega)
                                          have hwh_r := fid_k6_off_add (mv := mv) (k := 11)
                                            (x := repl) hmv_hi (by decide) (by omega)
                                          have hsl_b : ((4224 + 45 * mv + off + slot).setWidth
                                                64).toNat < scrw.length := by rw [hlw, hsl_e]; omega
                                          have hri_b :
                                              ((4224 + 45 * mv + off + ri).setWidth 64).toNat
                                                < scrw.length := by rw [hlw, hri_e]; omega
                                          have hri_b' :
                                              ((4224 + 45 * mv + off + ri).setWidth 64).toNat <
                                                (scrw.set ((4224 + 45 * mv + off + slot).setWidth
                                                  64).toNat repl).length := by
                                            rw [List.length_set]; exact hri_b
                                          c0_hsteps_nogrp
                                          let scrw2 := (scrw.set
                                            ((4224 + 45 * mv + off + slot).setWidth 64).toNat
                                            repl).set
                                            ((4224 + 45 * mv + off + ri).setWidth 64).toNat nl
                                          have hkw2 : FidPropKeep scr0 scrw2 :=
                                            fidPropKeep_of_set_ar (fidPropKeep_of_set_ar hkw
                                                ((4224 + 45 * mv + off + slot).setWidth 64).toNat
                                                repl (by rw [hsl_e, hmv_eq]; omega))
                                              ((4224 + 45 * mv + off + ri).setWidth 64).toNat nl
                                              (by rw [hri_e, hmv_eq]; omega)
                                          have hprw2 : (scrw2[4196]?.getD 0#32).toNat =
                                              pr.toNat + 1 := by
                                            dsimp only [scrw2]
                                            rw [List.getElem?_set_ne (by rw [hri_e]; omega),
                                              List.getElem?_set_ne (by rw [hsl_e]; omega)]
                                            exact hprw
                                          refine wp_join0 (fun m_u => ∃ scru : List (BitVec 32),
                                              FidPropKeep scr0 scru ∧
                                              (scru[4196]?.getD 0#32).toNat = pr.toNat + 1 ∧
                                              (FullMem c (m8ScrSt s scru) ⋆ R) m_u)
                                            (fun _ m_u ⟨scru, hku, hpru, hmu⟩ => by
                                              clear hkw2 hprw2 hprw hkw hlw hsl_b hri_b hsl_e hri_e
                                              have hlu : scru.length = scr0.length := hku.2.1
                                              have hwb_u :
                                                  ((4224 + 21 * mv + w_w).setWidth 64).toNat <
                                                    scru.length := by rw [hlu, hwb_e]; omega
                                              have hwh_u :
                                                  ((4224 + 11 * mv + repl).setWidth 64).toNat
                                                    < scru.length := by rw [hlu, hwh_r]; omega
                                              have hwn_u :
                                                  ((4224 + 13 * mv + w_w).setWidth 64).toNat <
                                                    scru.length := by rw [hlu, hwn_e]; omega
                                              have hwn_u' :
                                                  ((4224 + 13 * mv + w_w).setWidth 64).toNat <
                                                    (scru.set ((4224 + 21 * mv + w_w).setWidth
                                                      64).toNat other).length := by
                                                rw [List.length_set]; exact hwn_u
                                              have hwh_u0 :
                                                  ((4224 + 11 * mv + repl).setWidth 64).toNat <
                                                    (scru.set ((4224 + 21 * mv + w_w).setWidth
                                                      64).toNat other).length := by
                                                rw [List.length_set]; exact hwh_u
                                              let v2 := (scru.set ((4224 + 21 * mv + w_w).setWidth
                                                  64).toNat other)[((4224 + 11 * mv +
                                                  repl).setWidth 64).toNat]'hwh_u0
                                              have hwh_u' :
                                                  ((4224 + 11 * mv + repl).setWidth 64).toNat <
                                                    ((scru.set ((4224 + 21 * mv + w_w).setWidth
                                                      64).toNat other).set
                                                      ((4224 + 13 * mv + w_w).setWidth 64).toNat
                                                      v2).length := by
                                                simp only [List.length_set]; exact hwh_u
                                              c0_hsteps!
                                              have ⟨hku3, hpru3⟩ := fidPropKeep_swap3
                                                (other := other) hku hmv_eq
                                                (Nat.lt_of_lt_of_le hw_lt (by omega))
                                                (Nat.lt_of_lt_of_le hrepl_lt (by omega))
                                                hwb_e hwn_e hwh_r hpru v2
                                              exact hLw (8 * mv.toNat - (ws_w + 1#32).toNat)
                                                (tk_w + 1#64, vis_w + 1#64, prev_w, nxt,
                                                  ws_w + 1#32, ()) _ (by omega)
                                                ⟨_, hku3, hpru3, by omega, rfl, hm⟩)
                                            (fun Ju hJu => by
                                              have hlu2 : scrw2.length = scr0.length := hkw2.2.1
                                              c0_hsplit
                                              · have hwh_nl2 :
                                                    ((4224 + 11 * mv + nl).setWidth 64).toNat
                                                      < scrw2.length := by rw [hlu2, hwh_nl]; omega
                                                c0_hsteps!
                                                have ⟨hkw3, hprw3⟩ := fidPropKeep_set_lo_pr
                                                  (k := 11) (c := 2) hkw2 hmv_eq (by decide)
                                                  (by decide) (by omega) hwh_nl hprw2 nxt
                                                exact hJu _ ⟨_, hkw3, hprw3, hm⟩
                                              · have hprev_lt : prev_w.toNat < 2 * nc.toNat :=
                                                  by fid_omega
                                                have hwn_p := fid_k6_off_add (mv := mv) (k := 13)
                                                  (x := prev_w) hmv_hi (by decide) (by omega)
                                                have hwn_pb : ((4224 + 13 * mv + prev_w).setWidth
                                                      64).toNat < scrw2.length := by
                                                  rw [hlu2, hwn_p]; omega
                                                c0_hsteps!
                                                have ⟨hkw3, hprw3⟩ := fidPropKeep_set_lo_pr
                                                  (k := 13) (c := 8) hkw2 hmv_eq (by decide)
                                                  (by decide) (by omega) hwn_p hprw2 nxt
                                                exact hJu _ ⟨_, hkw3, hprw3, hm⟩)
                                        · -- No replacement found: conflict or unit propagation
                                          clear hc
                                          let scrw1 := scrw.set
                                            ((4224 + 21 * mv + w_w).setWidth 64).toNat other
                                          have ⟨hkw1, hprw1⟩ := fidPropKeep_set_lo_pr
                                            (k := 21) (c := 8) hkw hmv_eq (by decide) (by decide)
                                            (Nat.lt_of_lt_of_le hw_lt (by omega))
                                            hwb_e hprw other
                                          have hlw1 : scrw1.length = scr0.length := hkw1.2.1
                                          have hv_oth1 : ((4224 + 9 * mv + other).setWidth
                                              64).toNat < scrw1.length := by
                                            rw [hlw1, hv_oth]; omega
                                          c0_hsplit
                                          · c0_hsteps_nogrp; fid_call hTicks
                                            refine fidK6AddTicksSpec_intro rfl
                                              (fidScr_lengthsOk hlen (hlw1.trans hscr_len))
                                              hsc15 (m8ScrSt_eq s scrw1 ▸ hm) ?_
                                            intro tk' m' scr' hm'
                                            c0_hsteps!
                                            have hkf' := fidPropKeep_of_set hkw1 4204 tk'
                                              (by decide) (Or.inr (by decide)) (Or.inl (by decide))
                                              (Or.inl (by omega)) (Or.inl (by omega))
                                              (Or.inl (by omega))
                                            exact hfinish cid _ m' hkf' (by rwa [m8ScrSt_eq])
                                          · refine wp_join0 (fun m' => ∃ scr' : List (BitVec 32),
                                                FidPropKeep scr0 scr' ∧
                                                (scr'[4196]?.getD 0#32).toNat = pr.toNat + 1 ∧
                                                (FullMem c (m8ScrSt s scr') ⋆ R) m')
                                              (fun _ m' ⟨scr', hk', hpr', hm'⟩ => by
                                                c0_hsteps!
                                                exact hLw (8 * mv.toNat - (ws_w + 1#32).toNat)
                                                  (tk_w + 1#64, vis_w + 1#64, w_w, nxt,
                                                    ws_w + 1#32, ()) m' (by omega)
                                                  ⟨scr', hk', hpr', by omega, rfl, hm'⟩)
                                              (fun Js hJs => by
                                                c0_hsplit
                                                · c0_hsteps_nogrp; fid_call hAssign
                                                  refine fidK6AssignSpec_intro rfl
                                                    (fidScr_lengthsOk hlen (hlw1.trans hscr_len))
                                                    hkw1.1 (m8ScrSt_eq s scrw1 ▸ hm) ?_
                                                  intro scr_a m_a hla hka hm_a
                                                  have hkw_a := fidPropKeep_of_assign hkw1
                                                    (hla.trans (hscr_len.symm.trans hlw1.symm))
                                                    (fun idx hi => hka idx (by
                                                      rw [← hscr_len, ← hlw1]; exact hi))
                                                  have hpra : (scr_a[4196]?.getD 0#32).toNat =
                                                      pr.toNat + 1 := by
                                                    rw [hka 4196 (by rw [← hscr_len, ← hlw1]; omega)
                                                      (by decide) (by decide)
                                                      (Or.inl (by decide)) (Or.inl (by omega))
                                                      (Or.inl (by omega))]
                                                    exact hprw1
                                                  c0_hsteps!; exact hJs _ ⟨scr_a, hkw_a, hpra, by
                                                    rwa [m8ScrSt_eq]⟩
                                                · c0_hsteps!
                                                  exact hJs _ ⟨scrw1, hkw1, hprw1, hm⟩)
                                      · intro Jr hJr; c0_hsteps_nogrp
                                        refine wp_loop_group (ts := [i32])
                                          (fun rem_r (r_i, ()) mr =>
                                            mr = mw ∧ r_i.toNat ≤ sz.toNat ∧
                                            rem_r = sz.toNat - r_i.toNat)
                                          ?_ ?_
                                        · rintro Lr rem_r ⟨r_i, ⟨⟩⟩ mr hLr ⟨hmr_eq, hr_le, rfl⟩
                                          subst mr
                                          c0_hsplit
                                          · have hr_lt : r_i.toNat < sz.toNat := by
                                              have hc' := hc; clear hc; fid_norm_ofnat
                                              simp only [Nat.reducePow, BitVec.reduceToNat] at hc'
                                              exact fidProp_ri_lt h4214 rfl rfl hcm_e hcm_b rfl hc'
                                            have hr1 : (r_i + 1#32).toNat = r_i.toNat + 1 :=
                                              m8_bv32_add1_toNat hr_lt
                                                (by clear hm hmw hkw hprw; omega)
                                            have har_e := fid_k6_off_add2 (mv := mv) (k := 45)
                                              (x := off) (y := r_i) hmv_hi (by decide)
                                              (by clear hm hmw hkw hprw; omega)
                                            have har_b : ((4224 + 45 * mv + off + r_i).setWidth
                                                  64).toNat < scrw.length := by
                                              clear hm hmw hkw hprw; rw [hlw, har_e]; omega
                                            let cand := scrw[((4224 + 45 * mv + off + r_i).setWidth
                                                64).toNat]'har_b
                                            c0_hsteps_nogrp
                                            refine wp_join0 (fun mr' => mr' = mw)
                                              (fun _ mr' h => by
                                                subst mr'; c0_hsteps!
                                                exact hLr (sz.toNat - (r_i + 1#32).toNat)
                                                  (r_i + 1#32, ()) mw
                                                  (by clear hm hmw hkw hprw; omega)
                                                  ⟨rfl, by clear hm hmw hkw hprw; omega, rfl⟩)
                                              (fun Js2 hJs2 => by
                                                c0_hsplit
                                                · have hc_lt : cand.toNat < 2 * nv.toNat := by
                                                    have hc' := hc; clear hc; fid_norm_ofnat
                                                    simp only [Nat.reducePow,
                                                      BitVec.reduceToNat] at hc'
                                                    exact fidProp_cand_lt h4214 rfl h4192 rfl rfl
                                                      hmv_hi hnv_le hco_e hco_b rfl har_e har_b rfl
                                                      hc'
                                                  have hvc_e := fid_k6_off_add (mv := mv) (k := 9)
                                                    (x := cand) hmv_hi (by decide)
                                                    (by clear hm hmw hkw hprw; omega)
                                                  have hvc_b :
                                                      ((4224 + 9 * mv + cand).setWidth 64).toNat
                                                        < scrw.length := by
                                                    clear hm hmw hkw hprw; rw [hlw, hvc_e]; omega
                                                  c0_hsplit
                                                  · c0_hsteps!
                                                    exact hJr (r_i, r_i, cand)
                                                      (Or.inr ⟨hr_lt, hc_lt⟩)
                                                  · c0_hsteps!; exact hJs2 _ rfl
                                                · c0_hsteps!; exact hJs2 _ rfl)
                                          · c0_hsteps!
                                            exact hJr (r_i, 0xFFFFFFFF#32, 0#32) (Or.inl rfl)
                                        · intro Lr hLr; c0_hsteps!
                                          exact hLr (sz.toNat - 2) (2#32, ()) mw
                                            ⟨rfl, Nat.le_trans (by decide) hsz2, by simp⟩)
                  · intro Lw hLw; c0_hsteps!
                    exact hLw (8 * mv.toNat) (ticks, 0#64, 0xFFFFFFFF#32, _, 0#32, ()) _
                      ⟨scro1, hko1, hpr_next, Nat.zero_le _, by simp, hm⟩
              · c0_hsteps!; exact hJex mo ⟨scro, hko, hmo⟩
            · c0_hsteps!; exact hJex mo ⟨scro, hko, hmo⟩
          · intro Lo hLo; c0_hsteps!
            exact hLo _ (0#64, ()) m0 ⟨scr0, fidPropKeep_refl hok, rfl, hm0'⟩

/-! ## 3. `full_k6_analyze_fid_wp` -/

/-- Parametric `Func.wp` proof for `full_k6_analyze_fid`, certifying `fidK6AnalyzeSpec`. -/
theorem full_k6_analyze_fid_wp (Γ : Env) (hAnaCl : ∀ a m Q X, fidK6AnaClSpec a m Q X →
      Γ "full_k6_ana_cl_fid" [i64, i32, i32] [] a m Q X)
    (hBt : ∀ a m Q X, fidK6BacktrackSpec a m Q X → Γ "full_k6_backtrack_fid" [i64, i32] [] a m Q X)
    (hMtf : ∀ a m Q X, fidK6MtfSpec a m Q X → Γ "full_k6_mtf_fid" [i64, i32] [] a m Q X)
    (hAssign : ∀ a m Q X, fidK6AssignSpec a m Q X →
      Γ "full_k6_assign_fid" [i64, i32, i32] [] a m Q X)
    (hWatch : ∀ a m Q X, fidK6WatchSpec a m Q X →
      Γ "full_k6_watch_fid" [i64, i32, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, fidK6AnalyzeSpec a m Q X → Func.wp Γ full_k6_analyze_fid_body a m Q X := by
  rintro ⟨h, confl_cid, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hok, hm0, hQ⟩ := fidK6AnalyzeSpec_elim hSpec
  let scr0 := s.scratch.scratch_buf
  have hscr_len : scr0.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hmin : 15744 ≤ scr0.length := hok.min_len
  have hmv_lo : 256 ≤ (scr0[4214]?.getD 0#32).toNat := hok.mv_lo
  have hmv_hi : (scr0[4214]?.getD 0#32).toNat ≤ 8192 := hok.mv_hi
  have hbge : 4224 + 45 * (scr0[4214]?.getD 0#32).toNat ≤ scr0.length := hok.base_ge
  have hlen_ge := hok.length_ge
  have hlen_lt := hok.length_lt
  have h4214 : 4214 < scr0.length := by omega
  have h4192 : 4192 < scr0.length := by omega
  let mv := scr0[4214]'h4214
  have hmv_o : (scr0[(@OfNat.ofNat Nat 4214 _)]'h4214).toNat = mv.toNat := rfl
  let nv := scr0[4192]'h4192
  have hnv_o : (scr0[(@OfNat.ofNat Nat 4192 _)]'h4192).toNat = nv.toNat := rfl
  have hmv_eq : (scr0[4214]?.getD 0#32) = mv := m8_k6_get_eq h4214
  rw [hmv_eq] at hmv_lo hmv_hi hbge hlen_ge
  have hm0' : (FullMem c (m8ScrSt s scr0) ⋆ R) m0 := by rwa [m8ScrSt_self]
  have hret_post : ∀ (ok : Bool) (scrf : List (BitVec 32)) (mf : Mem 64),
      FidAnaPost scr0 scrf → (FullMem c (m8ScrSt s scrf) ⋆ R) mf → Q (ok, ()) mf :=
    fun ok scrf mf hpf hmf =>
      hQ ok scrf mf hpf.1 (hpf.2.1.trans hscr_len) hpf.2.2.1 hpf.2.2.2.1 hpf.2.2.2.2.1
        hpf.2.2.2.2.2.1 hpf.2.2.2.2.2.2.1 hpf.2.2.2.2.2.2.2.1 hpf.2.2.2.2.2.2.2.2.1
        hpf.2.2.2.2.2.2.2.2.2.1 hpf.2.2.2.2.2.2.2.2.2.2.1 hpf.2.2.2.2.2.2.2.2.2.2.2.1
        hpf.2.2.2.2.2.2.2.2.2.2.2.2.1 hpf.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        hpf.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (m8ScrSt_eq s scrf ▸ hmf)
  have hret_keep : ∀ (ok : Bool) (scrf : List (BitVec 32)) (mf : Mem 64),
      FidAnaKeep scr0 scrf → (FullMem c (m8ScrSt s scrf) ⋆ R) mf → Q (ok, ()) mf :=
    fun ok scrf mf hkf hmf => hret_post ok scrf mf (fidAnaKeep_to_post hkf) hmf
  have hana_step : ∀ (scr : List (BitVec 32)) (hk : FidAnaKeep scr0 scr) (scr' : List (BitVec 32)),
      scr'.length = scr.length → (∀ idx < scr.length, let m := (scr[4214]?.getD 0#32).toNat
        idx ≠ 4208 → idx ≠ 4209 → idx ≠ 4210 → idx ≠ 4212 →
        (idx < 4224 + 6 * m ∨ 4224 + 9 * m ≤ idx) →
        (idx < 4224 + 43 * m ∨ 4224 + 45 * m ≤ idx) → scr'[idx]? = scr[idx]?) →
      FidAnaKeep scr0 scr' := fun scr hk scr' hlen' hkeep => by
    have h16 := hk.2.2.2.2.2.2.2.2.2.1; have hb := hk.1.base_ge; rw [h16] at hb
    let f (k : Nat) (h1 : k ≠ 4208 := by decide) (h2 : k ≠ 4209 := by decide)
        (h3 : k ≠ 4210 := by decide) (h4 : k ≠ 4212 := by decide) (hk0 : k < 4224 := by decide) :=
      hkeep k (by omega) h1 h2 h3 h4 (Or.inl (by omega)) (Or.inl (by omega))
    exact fidAnaKeep_of_frame hk hlen'
      (fun i hi => hkeep i (by omega) (by omega) (by omega) (by omega) (by omega)
        (Or.inl (by omega)) (Or.inl (by omega)))
      (f 4199) (f 4205) (f 4206) (f 4207) (f 4211) (f 4213) (f 4214) (f 4215) (f 4216)
      (fun i ha hb' => hkeep i (by omega) (by omega) (by omega) (by omega) (by omega)
        (Or.inr (by rw [h16]; omega)) (Or.inl (by rw [h16]; omega)))
  clear hQ hSpec hm0; unfold Func.wp full_k6_analyze_fid_body
  c0_hsplit
  · c0_hsteps!; exact hret_keep false scr0 m0 (fidAnaKeep_refl hok) hm0'
  · c0_hsplit
    · c0_hsteps!; exact hret_keep false scr0 m0 (fidAnaKeep_refl hok) hm0'
    · c0_hsplit
      · c0_hsteps!; exact hret_keep false scr0 m0 (fidAnaKeep_refl hok) hm0'
      · have hnv_le : nv.toNat ≤ mv.toNat := Nat.le_of_not_lt hc
        have hmc_n : (mv <<< (2 : Nat)).toNat = 4 * mv.toNat := fid_bv32_shl2_toNat (by omega)
        have hmo_n : (mv <<< (1 : Nat)).toNat = 2 * mv.toNat := m8_bv32_shl1_toNat (by omega)
        have hnv2_n : (nv <<< (1 : Nat)).toNat = 2 * nv.toNat := m8_bv32_shl1_toNat (by omega)
        c0_hsteps_nogrp
        let scr_a0 := (((scr0.set 4209 1#32).set 4208 0#32).set 4210 0#32).set 4212 0#32
        have hk0 : FidAnaKeep scr0 scr_a0 := fidAnaKeep_set_lt4214 (fidAnaKeep_set_lt4214
          (fidAnaKeep_set_lt4214 (fidAnaKeep_set_lt4214 (fidAnaKeep_refl hok) 4209 1#32)
            4208 0#32) 4210 0#32) 4212 0#32
        fid_call hAnaCl
        refine fidK6AnaClSpec_intro rfl (fidScr_lengthsOk hlen (hk0.2.1.trans hscr_len)) hk0.1
          (m8ScrSt_eq s scr_a0 ▸ hm) ?_
        intro scr1 m1 hl1 hk1 hm1
        have hk1a : FidAnaKeep scr0 scr1 :=
          hana_step _ hk0 scr1 (hl1.trans (hk0.2.1.trans hscr_len).symm)
            (fun idx hi => hk1 idx (by rw [← hscr_len, ← hk0.2.1]; exact hi))
        have hmin1 : 15744 ≤ scr1.length := by omega
        have hm1' : (FullMem c (m8ScrSt s scr1) ⋆ R) m1 := by rwa [m8ScrSt_eq]
        clear hk1 hm1 hl1
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
          (fun idx => (idx, ())) (fun idx => idx.toNat ≤ mv.toNat)
          ?_ ?_
        · intro _ idx0 hidx0
          -- Resolution loop `while (scr[FKH_OPEN] > 0)`
          c0_hsteps_nogrp
          refine wp_join_state (ts := [i32, i32]) (α := BitVec 32 × BitVec 32 × List (BitVec 32))
            (fun x => (x.1, x.2.1, ()))
            (fun x m_u => FidAnaKeep scr0 x.2.2 ∧ (FullMem c (m8ScrSt s x.2.2) ⋆ R) m_u)
            ?_ ?_
          · rintro _ ⟨_, uip, scru⟩ m_u ⟨hku, hmu⟩
            clear hm1' hidx0 hk1a hk0
            have hlu : scru.length = scr0.length := hku.2.1
            have hmin_u : 15744 ≤ scru.length := by omega
            c0_hsteps_nogrp
            refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
              (fun nana => (nana, ())) (fun nana => nana.toNat ≤ mv.toNat)
              ?_ ?_
            · intro _ nana hnana
              -- Clear seen flags on `0 ..< nana`
              c0_hsteps_nogrp
              refine wp_loop_group (ts := [i32])
                (fun rem_a (ai, ()) ma => ∃ scra : List (BitVec 32),
                  FidAnaKeep scr0 scra ∧ ai.toNat ≤ nana.toNat ∧ rem_a = nana.toNat - ai.toNat ∧
                  (FullMem c (m8ScrSt s scra) ⋆ R) ma)
                ?_ ?_
              · rintro La rem_a ⟨ai, ⟨⟩⟩ ma hLa ⟨scra, hka, hai_le, rfl, hma⟩
                have hla : scra.length = scr0.length := hka.2.1
                have hmin_a : 15744 ≤ scra.length := by omega
                c0_hsplit
                · have hai_lt : ai.toNat < nana.toNat := hc
                  have hai1 : (ai + 1#32).toNat = ai.toNat + 1 :=
                    m8_bv32_add1_toNat hai_lt (by omega)
                  have hana_e := fid_k6_off_add (mv := mv) (k := 7) (x := ai)
                    hmv_hi (by decide) (by omega)
                  have hana_b : ((4224 + 7 * mv + ai).setWidth 64).toNat < scra.length := by
                    rw [hla, hana_e]; omega
                  let av := scra[((4224 + 7 * mv + ai).setWidth 64).toNat]'hana_b
                  c0_hsteps_nogrp
                  refine wp_join0 (fun ma' => ∃ scra' : List (BitVec 32), FidAnaKeep scr0 scra' ∧
                      scra'.length = scra.length ∧ (FullMem c (m8ScrSt s scra') ⋆ R) ma')
                    (fun _ ma' ⟨scra', hka', hla', hma'⟩ => by
                      c0_hsteps!; exact hLa (nana.toNat - (ai + 1#32).toNat) (ai + 1#32, ()) ma'
                        (by omega) ⟨scra', hka', by omega, rfl, hma'⟩)
                    (fun Ja hJa => by
                      c0_hsplit
                      · have hav_lt : av.toNat < nv.toNat := by
                          have hc' := hc; fid_norm_ofnat
                          simp only [Nat.reducePow, BitVec.reduceToNat] at hc'
                          have h1 : (scra[(4224 + 7 * (scr0[4214]'h4214).toNat + ai.toNat) %
                              4294967296]'(by rw [hla]; omega)).toNat = av.toNat :=
                            congrArg BitVec.toNat (m8_k6_get_congr (by rw [hana_e]; omega) _ _)
                          try rw [h1] at hc'
                          dsimp only [nv]; exact hc'
                        have hfl_e := fid_k6_off_add (mv := mv) (k := 6) (x := av) hmv_hi
                          (by decide) (by omega)
                        have hfl_b : ((4224 + 6 * mv + av).setWidth 64).toNat < scra.length := by
                          rw [hla, hfl_e]; omega
                        c0_hsteps!; rw [fid_list_set_idx_eq _ hfl_e] at hm
                        have hka' : FidAnaKeep scr0 (scra.set (4224 + 6 * mv.toNat + av.toNat)
                            ((scra[((4224 + 6 * mv + av).setWidth 64).toNat]'hfl_b) &&&
                              ~~~2#32)) :=
                          fidAnaKeep_of_set_lo hka _ _ (by omega) (by rw [hmv_eq]; omega)
                        exact hJa _ ⟨_, hka', by simp, hm⟩
                      · c0_hsteps!; exact hJa ma ⟨scra, hka, rfl, hma⟩)
                · have h4210 : 4210 < scra.length := by omega
                  have h4209 : 4209 < scra.length := by omega
                  let nres := scra[4210]'h4210; let nkl := scra[4209]'h4209
                  have hnres_o : (scra[(@OfNat.ofNat Nat 4210 _)]'h4210).toNat = nres.toNat := rfl
                  have hnkl_o : (scra[(@OfNat.ofNat Nat 4209 _)]'h4209).toNat = nkl.toNat := rfl
                  c0_hsplit
                  · c0_hsteps!; exact hret_keep false scra ma hka hma
                  · c0_hsplit
                    · c0_hsteps!; exact hret_keep false scra ma hka hma
                    · c0_hsplit
                      · c0_hsteps!; exact hret_keep false scra ma hka hma
                      · have hnres_le : nres.toNat ≤ 2 * mv.toNat := by fid_omega
                        c0_hsplit
                        · c0_hsteps!; exact hret_keep false scra ma hka hma
                        · have hnkl_pos : 0 < nkl.toNat :=
                            Nat.pos_of_ne_zero (fun h => hc (BitVec.eq_of_toNat_eq h))
                          c0_hsplit
                          · c0_hsteps!; exact hret_keep false scra ma hka hma
                          · have hnkl_le : nkl.toNat ≤ mv.toNat := Nat.le_of_not_lt hc
                            have hkl0_e := fid_k6_off_k (mv := mv) (k := 8) hmv_hi (by decide)
                            have hkl0_b : ((4224 + 8 * mv).setWidth 64).toNat < scra.length :=
                              by rw [hla, fid_zext32_toNat, hkl0_e]; omega
                            let scrb := scra.set ((4224 + 8 * mv).setWidth 64).toNat uip
                            have hkb : FidAnaKeep scr0 scrb := fidAnaKeep_of_set_lo hka _ uip
                                (by rw [fid_zext32_toNat, hkl0_e]; omega)
                                (by rw [fid_zext32_toNat, hkl0_e, hmv_eq]; omega)
                            have hlb : scrb.length = scr0.length := hkb.2.1
                            c0_hsteps_nogrp
                            -- Scan `1 ..< nkl` for jump level `jlvl` and watch index `wi`
                            refine wp_loop_group (ts := [i32, i32, i32])
                              (fun rem_j (jlvl, wi, i, ()) mj =>
                                (FullMem c (m8ScrSt s scrb) ⋆ R) mj ∧
                                (wi = 1#32 ∨ wi.toNat < nkl.toNat) ∧
                                i.toNat ≤ nkl.toNat ∧ rem_j = nkl.toNat - i.toNat)
                              ?_ ?_
                            · rintro Lj rem_j ⟨jlvl, wi, i, ⟨⟩⟩ mj hLj ⟨hmj, hwi_lt, hi_le, rfl⟩
                              clear hm
                              c0_hsplit
                              · have hi_lt : i.toNat < nkl.toNat := hc
                                have hi1 : (i + 1#32).toNat = i.toNat + 1 :=
                                  m8_bv32_add1_toNat hi_lt (by omega)
                                have hkli_e := fid_k6_off_add (mv := mv) (k := 8) (x := i)
                                  hmv_hi (by decide) (by omega)
                                have hkli_b : ((4224 + 8 * mv + i).setWidth 64).toNat <
                                    scrb.length := by rw [hlb, hkli_e]; omega
                                let kv := (scrb[((4224 + 8 * mv + i).setWidth 64).toNat]'
                                  hkli_b) >>> (1 : Nat)
                                c0_hsteps_nogrp
                                refine wp_join_state (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
                                  (fun x => (x.1, x.2, ()))
                                  (fun x mj => (FullMem c (m8ScrSt s scrb) ⋆ R) mj ∧
                                    (x.2 = 1#32 ∨ x.2.toNat < nkl.toNat))
                                  (fun _ ⟨jl', wi'⟩ mj ⟨hmj', hwi'⟩ => by
                                    c0_hsteps!; exact hLj (nkl.toNat - (i + 1#32).toNat)
                                      (jl', wi', i + 1#32, ()) _ (by omega)
                                      ⟨hmj', hwi', by omega, rfl⟩)
                                  (fun J5 hJ5 => by
                                    c0_hsplit
                                    · have hkv_lt : kv.toNat < nv.toNat := by
                                        have hc' := hc; fid_norm_ofnat
                                        simp only [Nat.reducePow, BitVec.reduceToNat] at hc'
                                        have hkv_g : scrb[(4224 + 8 * (scr0[4214]'h4214).toNat +
                                              i.toNat) % 4294967296]'(by
                                                rw [hlb, Nat.mod_eq_of_lt (by omega)]; omega) =
                                              scrb[((4224 + 8 * mv + i).setWidth 64).toNat]'
                                                hkli_b :=
                                          m8_k6_get_congr (by rw [hkli_e]; dsimp only [mv]; omega)
                                            _ _
                                        rw [hkv_g] at hc'
                                        dsimp only [kv, nv]; rw [m8_bv32_lshr1_toNat]; exact hc'
                                      have hlv_e := fid_k6_off_add0 (x := kv) (by omega)
                                      have hlv_b : (((4224 : BitVec 32) + kv).setWidth 64).toNat <
                                            scrb.length := by rw [hlb, hlv_e]; omega
                                      c0_hsteps_nogrp
                                      refine wp_join_state (ts := [i32, i32])
                                        (α := BitVec 32 × BitVec 32)
                                        (fun x => (x.1, x.2, ()))
                                        (fun x mj => (FullMem c (m8ScrSt s scrb) ⋆ R) mj ∧
                                          (x.2 = 1#32 ∨ x.2.toNat < nkl.toNat))
                                        (fun _ ⟨jl', wi'⟩ mj ⟨hmj', hwi'⟩ => by
                                          c0_hsteps!; exact hJ5 (jl', wi') _ ⟨hmj', hwi'⟩)
                                        (fun J6 hJ6 => by
                                          c0_hsplit
                                          · c0_hsteps!
                                            exact hJ6 (_, i) _ ⟨hmj, Or.inr hi_lt⟩
                                          · c0_hsteps!
                                            exact hJ6 (jlvl, wi) _ ⟨hmj, hwi_lt⟩)
                                    · c0_hsteps!
                                      exact hJ5 (jlvl, wi) _ ⟨hmj, hwi_lt⟩)
                              · -- Optional swap `kl[1]` <-> `kl[wi]`, then backtrack + MTF + append
                                refine wp_join0 (fun ms => ∃ scrs : List (BitVec 32),
                                    FidAnaKeep scr0 scrs ∧ (FullMem c (m8ScrSt s scrs) ⋆ R) ms)
                                  ?_ ?_
                                · rintro _ ms ⟨scrs, hks, hms⟩
                                  clear hLj hmj hkb hwi_lt hka hLa hku hmu
                                  have hls : scrs.length = scr0.length := hks.2.1
                                  c0_hsteps_nogrp; fid_call hBt
                                  refine fidK6BacktrackSpec_intro rfl
                                    (fidScr_lengthsOk hlen (hls.trans hscr_len))
                                    (m8ScrSt_buf s scrs ▸ hks.1) (m8ScrSt_eq s scrs ▸ hms) ?_
                                  intro scr_bt m_bt hl_bt hk_bt hm_bt
                                  have h16_s := hks.2.2.2.2.2.2.2.2.2.1
                                  have hbs := hks.1.base_ge; rw [h16_s] at hbs
                                  have hk_bt_a : FidAnaKeep scr0 scr_bt :=
                                    fidAnaKeep_of_frame hks (hl_bt.trans (hls.trans hscr_len).symm)
                                      (fun i hi => hk_bt i (by omega) (Or.inl hi))
                                      (hk_bt 4199 (by omega) (Or.inr (Or.inl (by decide))))
                                      (hk_bt 4205 (by omega) (Or.inr (Or.inl (by decide))))
                                      (hk_bt 4206 (by omega) (Or.inr (Or.inl (by decide))))
                                      (hk_bt 4207 (by omega) (Or.inr (Or.inl (by decide))))
                                      (hk_bt 4211 (by omega) (Or.inr (Or.inl (by decide))))
                                      (hk_bt 4213 (by omega) (Or.inr (Or.inl (by decide))))
                                      (hk_bt 4214 (by omega) (Or.inr (Or.inl (by decide))))
                                      (hk_bt 4215 (by omega) (Or.inr (Or.inl (by decide))))
                                      (hk_bt 4216 (by omega) (Or.inr (Or.inl (by decide))))
                                      (fun i ha hb' => hk_bt i (by omega)
                                        (Or.inr (Or.inr (Or.inr (by rw [h16_s]; omega)))))
                                  have hm_bt' : (FullMem c (m8ScrSt s scr_bt) ⋆ R) m_bt := by
                                    rwa [m8ScrSt_eq]
                                  clear hk_bt hm_bt hl_bt
                                  -- MTF loop over `0 ..< nana`
                                  c0_hsteps_nogrp
                                  refine wp_loop_group (ts := [i32])
                                    (fun rem_m (ai, ()) mm => ∃ scrm : List (BitVec 32),
                                      FidAnaKeep scr0 scrm ∧ ai.toNat ≤ nana.toNat ∧
                                      rem_m = nana.toNat - ai.toNat ∧
                                      (FullMem c (m8ScrSt s scrm) ⋆ R) mm)
                                    ?_ ?_
                                  · rintro Lm rem_m ⟨ai, ⟨⟩⟩ mm hLm ⟨scrm, hkm, hai_le, rfl, hmm⟩
                                    have hlm : scrm.length = scr0.length := hkm.2.1
                                    have hmin_m : 15744 ≤ scrm.length := by omega
                                    c0_hsplit
                                    · have hai_lt : ai.toNat < nana.toNat := hc
                                      have hai1 : (ai + 1#32).toNat = ai.toNat + 1 :=
                                        m8_bv32_add1_toNat hai_lt (by omega)
                                      have hana_e := fid_k6_off_add (mv := mv) (k := 7) (x := ai)
                                        hmv_hi (by decide) (by omega)
                                      have hana_b : ((4224 + 7 * mv + ai).setWidth 64).toNat <
                                          scrm.length := by rw [hlm, hana_e]; omega
                                      c0_hsteps_nogrp; fid_call hMtf
                                      refine fidK6MtfSpec_intro rfl
                                        (fidScr_lengthsOk hlen (hlm.trans hscr_len))
                                        (m8ScrSt_buf s scrm ▸ hkm.1)
                                        (m8ScrSt_eq s scrm ▸ hmm) ?_
                                      intro scr_m m_m hl_m hk_m hm_m
                                      have h16_m := hkm.2.2.2.2.2.2.2.2.2.1
                                      have hbm := hkm.1.base_ge; rw [h16_m] at hbm
                                      have hkm' : FidAnaKeep scr0 scr_m := fidAnaKeep_of_frame hkm
                                          (hl_m.trans (hlm.trans hscr_len).symm)
                                          (fun i hi => hk_m i (by omega) (Or.inl (by omega)))
                                          (hk_m 4199 (by omega) (Or.inl (by decide)))
                                          (hk_m 4205 (by omega) (Or.inr (Or.inl (by omega))))
                                          (hk_m 4206 (by omega) (Or.inr (Or.inl (by omega))))
                                          (hk_m 4207 (by omega) (Or.inr (Or.inl (by omega))))
                                          (hk_m 4211 (by omega) (Or.inr (Or.inl (by omega))))
                                          (hk_m 4213 (by omega) (Or.inr (Or.inl (by omega))))
                                          (hk_m 4214 (by omega) (Or.inr (Or.inl (by omega))))
                                          (hk_m 4215 (by omega) (Or.inr (Or.inl (by omega))))
                                          (hk_m 4216 (by omega) (Or.inr (Or.inl (by omega))))
                                          (fun i ha hb' => hk_m i (by omega)
                                            (Or.inr (Or.inr (by rw [h16_m]; omega))))
                                      c0_hsteps!
                                      exact hLm (nana.toNat - (ai + 1#32).toNat) (ai + 1#32, ()) m_m
                                        (by omega) ⟨scr_m, hkm', by omega, rfl, by
                                          clear hk_m hl_m; rwa [m8ScrSt_eq]⟩
                                    · -- Append learned clause + antecedents to arena
                                      clear hk_bt_a hm_bt' h16_s hbs m_bt scr_bt
                                        hks hms hls ms scrs hkl0_b hlb scrb
                                        hnana hmin_u hlu m_u idx0 hmin1
                                        m1 scr1 scr_a0 hLm hai_le
                                      have h4193_m : 4193 < scrm.length := by omega
                                      have h4206_m : 4206 < scrm.length := by omega
                                      have h4207_m : 4207 < scrm.length := by omega
                                      let nc_m := scrm[4193]'h4193_m
                                      have hnc_m_o :
                                          (scrm[(@OfNat.ofNat Nat 4193 _)]'h4193_m).toNat =
                                            nc_m.toNat := rfl
                                      let off_m := scrm[4206]'h4206_m
                                      have hoff_m_o :
                                          (scrm[(@OfNat.ofNat Nat 4206 _)]'h4206_m).toNat =
                                            off_m.toNat := rfl
                                      let ac_m := scrm[4207]'h4207_m
                                      have hac_m_o :
                                          (scrm[(@OfNat.ofNat Nat 4207 _)]'h4207_m).toNat =
                                            ac_m.toNat := rfl
                                      have h16_m := hkm.2.2.2.2.2.2.2.2.2.1
                                      have hlg_m := hkm.1.length_ge
                                      have hal_m := hkm.1.alen_le
                                      rw [h16_m, hmv_eq, m8_k6_get_eq h4207_m] at hlg_m
                                      rw [m8_k6_get_eq h4206_m, m8_k6_get_eq h4207_m] at hal_m
                                      c0_hsplit
                                      · c0_hsteps!; exact hret_keep false scrm mm hkm hmm
                                      · have hncm_lt : nc_m.toNat < 4 * mv.toNat := by fid_omega
                                        clear hc; have hscr0_lt : scr0.length < 2 ^ 30 := hlen_lt
                                        have h_alen : off_m.toNat ≤ ac_m.toNat := hal_m
                                        have h_lenc :
                                            4224 + 45 * mv.toNat + ac_m.toNat ≤ scr0.length := by
                                          rw [← hlm]; exact hlg_m
                                        have hno_ov : off_m.toNat + nkl.toNat + nres.toNat <
                                            2 ^ 32 := by omega
                                        c0_hsplit
                                        · c0_hsteps!; exact hret_keep false scrm mm hkm hmm
                                        · have hfit_m : off_m.toNat + nkl.toNat + nres.toNat ≤
                                              ac_m.toNat := by
                                            have hc' := hc; fid_norm_ofnat
                                            simp only [Nat.reducePow] at hc'
                                            rw [show (scrm[4206]'h4206_m).toNat = off_m.toNat
                                                from rfl,
                                              show (scra[4209]'h4209).toNat = nkl.toNat from rfl,
                                              show (scra[4210]'h4210).toNat = nres.toNat from rfl,
                                              show (scrm[4207]'h4207_m).toNat = ac_m.toNat
                                                from rfl,
                                              Nat.mod_eq_of_lt (by omega)] at hc'
                                            exact Nat.le_of_not_lt hc'
                                          clear hc
                                          -- Copy `kl[0 ..< nkl)` to `arena[off_m ..)`
                                          c0_hsteps_nogrp
                                          refine wp_loop_group (ts := [i32])
                                            (fun rem_k (i, ()) mk => ∃ scrk : List (BitVec 32),
                                              FidAnaKeep scr0 scrk ∧ i.toNat ≤ nkl.toNat ∧
                                              rem_k = nkl.toNat - i.toNat ∧
                                              (FullMem c (m8ScrSt s scrk) ⋆ R) mk)
                                            ?_ ?_
                                          · rintro Lk rem_k ⟨i, ⟨⟩⟩ mk hLk
                                              ⟨scrk, hkk, hi_le, rfl, hmk⟩
                                            have hlk : scrk.length = scr0.length := hkk.2.1
                                            c0_hsplit
                                            · have hi_lt : i.toNat < nkl.toNat := hc
                                              clear hc
                                              have hi1 : (i + 1#32).toNat = i.toNat + 1 :=
                                                m8_bv32_add1_toNat hi_lt (by omega)
                                              have hkli_e := fid_k6_off_add (mv := mv) (k := 8)
                                                (x := i) hmv_hi (by decide) (by omega)
                                              have har_e := fid_k6_off_add2 (mv := mv) (k := 45)
                                                (x := off_m) (y := i) hmv_hi (by decide) (by omega)
                                              have hkli_b :
                                                  ((4224 + 8 * mv + i).setWidth 64).toNat <
                                                    scrk.length := by rw [hlk, hkli_e]; omega
                                              have har_b : ((4224 + 45 * mv + off_m + i).setWidth
                                                    64).toNat < scrk.length := by
                                                rw [hlk, har_e]; omega
                                              c0_hsteps!
                                              have hkk' := fidAnaKeep_set_45_2 hkk hmv_eq har_e
                                                (scrk[((4224 + 8 * mv + i).setWidth
                                                  64).toNat]'hkli_b)
                                              exact hLk (nkl.toNat - (i + 1#32).toNat)
                                                (i + 1#32, ()) _ (by omega)
                                                ⟨_, hkk', by omega, rfl, hm⟩
                                            · -- Copy `res[0 ..< nres)` to `arena[off_m + nkl ..)`
                                              c0_hsteps_nogrp
                                              refine wp_loop_group (ts := [i32])
                                                (fun rem_r (i, ()) mr => ∃ scrr : List (BitVec 32),
                                                  FidAnaKeep scr0 scrr ∧ i.toNat ≤ nres.toNat ∧
                                                  rem_r = nres.toNat - i.toNat ∧
                                                  (FullMem c (m8ScrSt s scrr) ⋆ R) mr)
                                                ?_ ?_
                                              · rintro Lr rem_r ⟨i, ⟨⟩⟩ mr hLr
                                                  ⟨scrr, hkr, hi_le, rfl, hmr⟩
                                                have hlr : scrr.length = scr0.length := hkr.2.1
                                                have hmin_r : 15744 ≤ scrr.length := by omega
                                                c0_hsplit
                                                · have hi_lt : i.toNat < nres.toNat := hc
                                                  clear hc
                                                  have hi1 : (i + 1#32).toNat = i.toNat + 1 :=
                                                    m8_bv32_add1_toNat hi_lt (by omega)
                                                  have hri_e := fid_k6_off_add (mv := mv) (k := 43)
                                                    (x := i) hmv_hi (by decide) (by omega)
                                                  have har_e := fid_k6_off_add3 (mv := mv) (k := 45)
                                                    (x := off_m) (y := nkl) (z := i)
                                                    hmv_hi (by decide) (by omega)
                                                  have hri_b :
                                                      ((4224 + 43 * mv + i).setWidth 64).toNat
                                                        < scrr.length := by rw [hlr, hri_e]; omega
                                                  have har_b : ((4224 + 45 * mv + off_m + nkl +
                                                        i).setWidth 64).toNat < scrr.length := by
                                                    rw [hlr, har_e]; omega
                                                  c0_hsteps!
                                                  have hkr' := fidAnaKeep_set_45_3 hkr hmv_eq har_e
                                                    (scrr[((4224 + 43 * mv + i).setWidth
                                                      64).toNat]'hri_b)
                                                  exact hLr (nres.toNat - (i + 1#32).toNat)
                                                    (i + 1#32, ()) _ (by omega)
                                                    ⟨_, hkr', by omega, rfl, hm⟩
                                                · -- Commit header: `alen`, `cl_off`, `cl_meta`,
                                                  -- `cl_aux`, `nc = nc_m + 1`
                                                  clear hLr hi_le
                                                  have hco_e := fid_k6_off_add (mv := mv) (k := 29)
                                                    (x := nc_m) hmv_hi (by decide) (by omega)
                                                  have hcm_e := fid_k6_off_add (mv := mv) (k := 33)
                                                    (x := nc_m) hmv_hi (by decide) (by omega)
                                                  have hca_e := fid_k6_off_add (mv := mv) (k := 37)
                                                    (x := nc_m) hmv_hi (by decide) (by omega)
                                                  have hco_b : ((4224 + 29 * mv + nc_m).setWidth
                                                        64).toNat < scrr.length := by
                                                    rw [hlr, hco_e]; omega
                                                  have hcm_b : ((4224 + 33 * mv + nc_m).setWidth
                                                        64).toNat < scrr.length := by
                                                    rw [hlr, hcm_e]; omega
                                                  have hca_b : ((4224 + 37 * mv + nc_m).setWidth
                                                        64).toNat < scrr.length := by
                                                    rw [hlr, hca_e]; omega
                                                  have h4206_r : 4206 < scrr.length := by omega
                                                  have h4193_r : 4193 < scrr.length := by omega
                                                  have ⟨hco_b', hcm_b', hca_b', h4193_b'⟩ :=
                                                    fidAna_commit_bnds (off_m := off_m) (nkl := nkl)
                                                      (nres := nres) h4193_r hco_b hcm_b hca_b
                                                  let scr_c := ((((scrr.set 4206
                                                    (off_m + nkl + nres)).set
                                                    ((4224 + 29 * mv + nc_m).setWidth
                                                      64).toNat off_m).set
                                                    ((4224 + 33 * mv + nc_m).setWidth
                                                      64).toNat (nkl ||| 0x40000000#32)).set
                                                    ((4224 + 37 * mv + nc_m).setWidth
                                                      64).toNat nres).set 4193 (nc_m + 1#32)
                                                  have hncm_eq : scrr[4193]? = some nc_m := by
                                                    rw [hkr.2.2.1 4193 (by decide),
                                                      ← hkm.2.2.1 4193 (by decide),
                                                      List.getElem?_eq_getElem h4193_m]
                                                  have hacr_eq : scrr[4207]? = some ac_m := by
                                                    rw [hkr.2.2.2.2.2.2.1, ← hkm.2.2.2.2.2.2.1,
                                                      List.getElem?_eq_getElem h4207_m]
                                                  have hpost_c : FidAnaPost scr0 scr_c :=
                                                    fidAnaPost_commit hkr hmv_eq hmv_lo hmv_hi
                                                      hncm_eq hacr_eq hncm_lt hnkl_le hfit_m
                                                      hco_e hcm_e hca_e
                                                  have hlc : scr_c.length = scr0.length :=
                                                    hpost_c.2.1
                                                  have h16_c := hpost_c.2.2.2.2.2.2.2.2.2.2.2.1
                                                  have hbc := hpost_c.1.base_ge; rw [h16_c] at hbc
                                                  c0_hsplit
                                                  · c0_hsteps_nogrp; fid_call hAssign
                                                    refine fidK6AssignSpec_intro rfl
                                                      (fidScr_lengthsOk hlen (hlc.trans hscr_len))
                                                      hpost_c.1 (m8ScrSt_eq s scr_c ▸ hm) ?_
                                                    intro scr_f m_f hlf hkf hmf
                                                    have hpf : FidAnaPost scr0 scr_f :=
                                                      fidAnaPost_of_assign hpost_c
                                                        (hlf.trans (hlc.trans hscr_len).symm)
                                                        (fun i hi => hkf i (by omega))
                                                    c0_hsteps!; exact hret_post true scr_f m_f hpf
                                                      (by rwa [m8ScrSt_eq])
                                                  · have hkl0_c :
                                                        ((4224 + 8 * mv).setWidth 64).toNat <
                                                          scr_c.length := by
                                                      rw [hlc, fid_zext32_toNat, hkl0_e]; omega
                                                    have hkl1_e := fid_k6_off_add (mv := mv)
                                                      (k := 8) (x := 1#32) hmv_hi (by decide)
                                                      (by rw [show (1#32 : BitVec 32).toNat = 1
                                                        from rfl]; omega)
                                                    have hkl1_c : ((4224 + 8 * mv + 1#32).setWidth
                                                          64).toNat < scr_c.length := by
                                                      rw [hlc, hkl1_e,
                                                        show (1#32 : BitVec 32).toNat = 1 from rfl]
                                                      omega
                                                    c0_hsteps_nogrp; fid_call hWatch
                                                    refine fidK6WatchSpec_intro rfl
                                                      (fidScr_lengthsOk hlen (hlc.trans hscr_len))
                                                      hpost_c.1 (m8ScrSt_eq s scr_c ▸ hm) ?_
                                                    intro scr_w m_w hlw hkw hmw
                                                    have hpw : FidAnaPost scr0 scr_w :=
                                                      fidAnaPost_of_watch hpost_c
                                                        (hlw.trans (hlc.trans hscr_len).symm)
                                                        (fun i hi => hkw i (by omega))
                                                    c0_hsteps_nogrp; fid_call hAssign
                                                    refine fidK6AssignSpec_intro rfl
                                                      (fidScr_lengthsOk hlen hlw) hpw.1 hmw ?_
                                                    intro scr_f m_f hlf hkf hmf
                                                    have hpf : FidAnaPost scr0 scr_f :=
                                                      fidAnaPost_of_assign hpw (hlf.trans hlw.symm)
                                                        (fun i hi => hkf i (by omega))
                                                    c0_hsteps!; exact hret_post true scr_f m_f hpf
                                                      (by rwa [m8ScrSt_eq])
                                              · intro Lr hLr; c0_hsteps!
                                                exact hLr nres.toNat (0#32, ()) mk
                                                  ⟨scrk, hkk, Nat.zero_le _, by simp, hmk⟩
                                          · intro Lk hLk; c0_hsteps!
                                            exact hLk nkl.toNat (0#32, ()) mm
                                              ⟨scrm, hkm, Nat.zero_le _, by simp, hmm⟩
                                  · intro Lm hLm; c0_hsteps!
                                    exact hLm nana.toNat (0#32, ()) m_bt
                                      ⟨scr_bt, hk_bt_a, Nat.zero_le _, by simp, hm_bt'⟩
                                · intro Js hJs
                                  c0_hsplit
                                  · c0_hsplit
                                    · have hwi_nlt : wi.toNat < nkl.toNat :=
                                        hwi_lt.resolve_left (fun h => by simp [h] at hc)
                                      have h1_nat : (1#32 : BitVec 32).toNat = 1 := rfl
                                      have hkl1_e := fid_k6_off_add (mv := mv) (k := 8) (x := 1#32)
                                        hmv_hi (by decide) (by omega)
                                      have hklw_e := fid_k6_off_add (mv := mv) (k := 8) (x := wi)
                                        hmv_hi (by decide) (by omega)
                                      have hkl1_b : ((4224 + 8 * mv + 1#32).setWidth 64).toNat
                                          < scrb.length := by rw [hlb, hkl1_e, h1_nat]; omega
                                      have hklw_b : ((4224 + 8 * mv + wi).setWidth 64).toNat <
                                          scrb.length := by rw [hlb, hklw_e]; omega
                                      c0_hsteps!
                                      have hks' := fidAnaKeep_of_set_lo (fidAnaKeep_of_set_lo hkb
                                          ((4224 + 8 * mv + 1#32).setWidth 64).toNat
                                          (scrb[((4224 + 8 * mv + wi).setWidth 64).toNat]'hklw_b)
                                          (by rw [hkl1_e, h1_nat]; omega)
                                          (by rw [hkl1_e, h1_nat, hmv_eq]; omega))
                                        ((4224 + 8 * mv + wi).setWidth 64).toNat
                                        (scrb[((4224 + 8 * mv + 1#32).setWidth 64).toNat]'hkl1_b)
                                        (by rw [hklw_e]; omega)
                                        (by rw [hklw_e, hmv_eq]; omega)
                                      exact hJs _ ⟨_, hks', hm⟩
                                    · c0_hsteps!; exact hJs _ ⟨scrb, hkb, hmj⟩
                                  · c0_hsteps!; exact hJs _ ⟨scrb, hkb, hmj⟩
                            · intro Lj hLj; c0_hsteps!
                              exact hLj (nkl.toNat - 1) (0#32, 1#32, 1#32, ()) _
                                ⟨hm, Or.inl rfl, by
                                  rw [show (1#32 : BitVec 32).toNat = 1 from rfl]; omega, by simp⟩
              · intro La hLa; c0_hsteps!
                exact hLa nana.toNat (0#32, ()) m_u ⟨scru, hku, Nat.zero_le _, by simp, hmu⟩
            · intro Jn hJn
              c0_hsplit
              · c0_hsteps!; exact hJn mv (Nat.le_refl _)
              · c0_hsteps!; exact hJn _ (Nat.le_of_not_lt hc)
          · intro Ju hJu; c0_hsteps_nogrp
            refine wp_loop_group (ts := [i32])
              (fun rem_u (idx, ()) ml => ∃ scrl : List (BitVec 32),
                FidAnaKeep scr0 scrl ∧ idx.toNat ≤ mv.toNat ∧ rem_u = idx.toNat ∧
                (FullMem c (m8ScrSt s scrl) ⋆ R) ml)
              ?_ ?_
            · rintro Lu rem_u ⟨idx, ⟨⟩⟩ ml hLu ⟨scrl, hkl, hidx_le, rfl, hml⟩
              have hll : scrl.length = scr0.length := hkl.2.1
              have hmin_l : 15744 ≤ scrl.length := by omega
              c0_hsplit
              · c0_hsplit
                · c0_hsteps!; exact hJu (idx, 0xFFFFFFFF#32, scrl) ml ⟨hkl, hml⟩
                · have hidx_pos : 0 < idx.toNat :=
                    Nat.pos_of_ne_zero (fun h => hc (BitVec.eq_of_toNat_eq h))
                  have hidx1 : (idx - 1#32).toNat = idx.toNat - 1 := m8_bv32_sub1_toNat hidx_pos
                  let idx' := idx - 1#32
                  have htr_e := fid_k6_off_add (mv := mv) (k := 5) (x := idx')
                    hmv_hi (by decide) (by dsimp only [idx']; rw [hidx1]; omega)
                  have htr_b : ((4224 + 5 * mv + idx').setWidth 64).toNat < scrl.length := by
                    rw [hll, htr_e]; dsimp only [idx']; rw [hidx1]; omega
                  let p := scrl[((4224 + 5 * mv + idx').setWidth 64).toNat]'htr_b
                  let pv := p >>> (1 : Nat)
                  c0_hsteps_nogrp
                  refine wp_join_state (ts := [i32]) (α := List (BitVec 32))
                    (fun _ => (0xFFFFFFFF#32, ())) (fun scrl' ml' => FidAnaKeep scr0 scrl' ∧
                      scrl'.length = scrl.length ∧ (FullMem c (m8ScrSt s scrl') ⋆ R) ml')
                    (fun _ scrl' ml' ⟨hkl', hll', hml'⟩ => by
                      c0_hsteps!; exact hLu idx'.toNat (idx', ()) ml'
                        (by dsimp only [idx']; rw [hidx1]; omega)
                        ⟨scrl', hkl', by dsimp only [idx']; rw [hidx1]; omega, rfl, hml'⟩)
                    (fun Jstep hJstep => by
                      c0_hsplit
                      · have hpv_lt : pv.toNat < nv.toNat := by
                          have hc' := hc; fid_norm_ofnat
                          simp only [Nat.reducePow, BitVec.reduceToNat] at hc'
                          have htr_m : (4224 + 5 * (scr0[4214]'h4214).toNat + (4294967296 - 1 +
                              idx.toNat)) % 4294967296 =
                              ((4224 + 5 * mv + idx').setWidth 64).toNat := by
                            rw [fid_sub1_mod32 _ _ hidx_pos (by omega), htr_e]
                            dsimp only [idx']; rw [hidx1]
                          have h1_eq : scrl[(4224 + 5 * (scr0[4214]'h4214).toNat + (4294967296 - 1 +
                              idx.toNat)) % 4294967296]'(by
                            rw [hll, fid_sub1_mod32 _ _ hidx_pos (by omega)]; omega) = p :=
                            m8_k6_get_congr htr_m _ _
                          rw [h1_eq] at hc'; dsimp only [pv, nv]
                          rw [m8_bv32_lshr1_toNat]; exact hc'
                        have hfl_e := fid_k6_off_add (mv := mv) (k := 6) (x := pv) hmv_hi
                          (by decide) (by omega)
                        have hfl_b : ((4224 + 6 * mv + pv).setWidth 64).toNat < scrl.length := by
                          rw [hll, hfl_e]; omega
                        c0_hsplit
                        · have hlv_e := fid_k6_off_add0 (x := pv) (by omega)
                          have hlv_b :
                              (((4224 : BitVec 32) + pv).setWidth 64).toNat < scrl.length := by
                            rw [hll, hlv_e]; omega
                          c0_hsplit
                          · have hkl1 :=
                              fidAnaKeep_set_lt4214 hkl 4212 (scrl[4212]'(by omega) - 1#32)
                            c0_hsplit
                            · c0_hsteps!; exact hJu (idx', p ^^^ 1#32, _) _ ⟨hkl1, hm⟩
                            · have hrs_e := fid_k6_off_add1 (mv := mv) (x := pv) hmv_hi (by omega)
                              have hrs_b : ((4224 + mv + pv).setWidth 64).toNat <
                                  (scrl.set 4212 (scrl[4212]'(by omega) - 1#32)).length := by
                                rw [List.length_set, hll, hrs_e]; omega
                              c0_hsplit
                              · c0_hsteps!; exact hJu (idx', p ^^^ 1#32, _) _ ⟨hkl1, hm⟩
                              · c0_hsteps_nogrp; fid_call hAnaCl
                                refine fidK6AnaClSpec_intro rfl
                                  (fidScr_lengthsOk hlen (hkl1.2.1.trans hscr_len)) hkl1.1
                                  (m8ScrSt_eq s _ ▸ hm) ?_
                                intro scr_a m_a hla hka hm_a
                                have hkl2 := hana_step _ hkl1 scr_a
                                  (hla.trans (hkl1.2.1.trans hscr_len).symm)
                                  (fun idx hi => hka idx (by
                                    rw [← hscr_len, ← hll]; simpa only [List.length_set] using hi))
                                c0_hsteps!; exact hJstep scr_a m_a ⟨hkl2, hla.trans
                                  (hll.trans hscr_len).symm, by rwa [m8ScrSt_eq]⟩
                          · c0_hsteps!; exact hJstep scrl ml ⟨hkl, rfl, hml⟩
                        · c0_hsteps!; exact hJstep scrl ml ⟨hkl, rfl, hml⟩
                      · c0_hsteps!; exact hJstep scrl ml ⟨hkl, rfl, hml⟩)
              · c0_hsteps!; exact hJu (idx, 0xFFFFFFFF#32, scrl) ml ⟨hkl, hml⟩
            · intro Lu hLu; c0_hsteps!
              exact hLu idx0.toNat (idx0, ()) m1 ⟨scr1, hk1a, hidx0, rfl, hm1'⟩
        · intro Ji hJi; c0_hsplit
          · c0_hsteps!; exact hJi mv (Nat.le_refl _)
          · c0_hsteps!; exact hJi _ (Nat.le_of_not_lt hc)

/-! ## 4. `full_k6_solve_fid_wp` -/

private theorem fidSolve_q_bnds {mv cur : BitVec 32} {len : Nat}
    (hmv : mv.toNat ≤ 8192) (hcur : cur.toNat < mv.toNat) (hbge : 4224 + 45 * mv.toNat ≤ len) :
    ((4224 + 9 * mv + (cur <<< (1 : Nat))).setWidth 64).toNat < len ∧
    ((4224 + 2 * mv + cur).setWidth 64).toNat < len := by
  have h1 := fid_k6_off_add (mv := mv) (k := 9) (x := cur <<< (1 : Nat)) hmv (by decide)
    (by rw [m8_bv32_shl1_toNat (by omega)]; omega)
  have h2 := fid_k6_off_add (mv := mv) (k := 2) (x := cur) hmv (by decide) (by omega)
  rw [h1, h2, m8_bv32_shl1_toNat (by omega)]; omega

private theorem fidSolveKeep_hdr {scr0 scr : List (BitVec 32)} (hk : FidSolveKeep scr0 scr)
    (idx : Nat) (v : BitVec 32)
    (hlo : 4195 ≤ idx := by decide) (hhi : idx < 4224 := by decide)
    (h06 : idx ≠ 4206 := by decide) (h07 : idx ≠ 4207 := by decide)
    (h11 : idx ≠ 4211 := by decide) (h16 : idx ≠ 4214 := by decide)
    (h17 : idx ≠ 4215 := by decide) (h18 : idx ≠ 4216 := by decide) :
    FidSolveKeep scr0 (scr.set idx v) :=
  fidSolveKeep_of_set_hdr hk idx v hlo hhi h06 h07 h11 h16 h17 h18

/-- Parametric `Func.wp` proof for `full_k6_solve_fid`, certifying `fidK6SolveSpec`. -/
theorem full_k6_solve_fid_wp (Γ : Env) (hBt : ∀ a m Q X, fidK6BacktrackSpec a m Q X →
      Γ "full_k6_backtrack_fid" [i64, i32] [] a m Q X)
    (hAssign : ∀ a m Q X, fidK6AssignSpec a m Q X →
      Γ "full_k6_assign_fid" [i64, i32, i32] [] a m Q X)
    (hProp : ∀ a m Q X, fidK6PropSpec a m Q X → Γ "full_k6_prop_fid" [i64] [i32] a m Q X)
    (hAnalyze : ∀ a m Q X, fidK6AnalyzeSpec a m Q X →
      Γ "full_k6_analyze_fid" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fidK6SolveSpec a m Q X → Func.wp Γ full_k6_solve_fid_body a m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hok, honc, hm0, hQ⟩ := fidK6SolveSpec_elim hSpec
  let scr0 := s.scratch.scratch_buf
  have hscr_len : scr0.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hmin : 15744 ≤ scr0.length := hok.min_len
  have hmv_lo : 256 ≤ (scr0[4214]?.getD 0#32).toNat := hok.mv_lo
  have hmv_hi : (scr0[4214]?.getD 0#32).toNat ≤ 8192 := hok.mv_hi
  have hbge : 4224 + 45 * (scr0[4214]?.getD 0#32).toNat ≤ scr0.length := hok.base_ge
  have hlen_ge := hok.length_ge; have hlen_lt := hok.length_lt
  have h4214 : 4214 < scr0.length := by omega
  let mv := scr0[4214]'h4214
  have hmv_o : (scr0[(@OfNat.ofNat Nat 4214 _)]'h4214).toNat = mv.toNat := rfl
  have hmv_d : (scr0[4214]'h4214).toNat = mv.toNat := rfl
  have hmv_eq : (scr0[4214]?.getD 0#32) = mv := m8_k6_get_eq h4214
  rw [hmv_eq] at hmv_lo hmv_hi hbge hlen_ge
  have hm0' : (FullMem c (m8ScrSt s scr0) ⋆ R) m0 := by rwa [m8ScrSt_self]
  have hret_f : ∀ (r : BitVec 64) (fl' : BitVec 64) (scrf : List (BitVec 32)) (mf : Mem 64),
      FidSolveKeep scr0 scrf → fl'.toNat ≤ s.core.fuel.toNat →
      (FullMem c (m8ScrFuelSt s fl' scrf) ⋆ R) mf → Q (r, ()) mf :=
    fun r fl' scrf mf hkf hfl hmf =>
      hQ r scrf fl' mf hkf.1 (hkf.2.1.trans hscr_len) hkf.2.2.1 hkf.2.2.2.1 hkf.2.2.2.2.1
        hkf.2.2.2.2.2.1 hkf.2.2.2.2.2.2.1 hfl (m8ScrFuelSt_eq s fl' scrf ▸ hmf)
  have hret_s : ∀ (r : BitVec 64) (scrf : List (BitVec 32)) (mf : Mem 64),
      FidSolveKeep scr0 scrf → (FullMem c (m8ScrSt s scrf) ⋆ R) mf → Q (r, ()) mf :=
    fun r scrf mf hkf hmf =>
      hret_f r s.core.fuel scrf mf hkf (Nat.le_refl _) (by rwa [m8ScrFuelSt_self])
  unfold Func.wp full_k6_solve_fid_body
  c0_hsplit
  · c0_hsteps!; exact hret_s 0#64 scr0 m0 (fidSolveKeep_refl hok honc) hm0'
  · c0_hsplit
    · c0_hsteps!; exact hret_s 0#64 scr0 m0 (fidSolveKeep_refl hok honc) hm0'
    · c0_hsteps_nogrp; fid_call hBt
      refine fidK6BacktrackSpec_intro rfl hlen hok hm0 ?_
      intro scr1 m1 hl1 hk1 hm1
      have hks1 : FidSolveKeep scr0 scr1 := fidSolveKeep_of_backtrack (fidSolveKeep_refl hok honc)
        (hl1.trans hscr_len.symm) (fun idx hi => hk1 idx (by omega))
      have hmin1 : 15744 ≤ scr1.length := by omega
      have hm1' : (FullMem c (m8ScrSt s scr1) ⋆ R) m1 := by rwa [m8ScrSt_eq]
      c0_hsplit
      · c0_hsteps!; exact hret_s 20#64 scr1 m1 hks1 hm1'
      · let scr2 := (scr1.set 4205 tick_lim).set 4204 0#32
        have hks2 : FidSolveKeep scr0 scr2 :=
          fidSolveKeep_hdr (fidSolveKeep_hdr hks1 4205 tick_lim) 4204 0#32
        have hl2 : scr2.length = scr0.length := hks2.2.1
        have h4192_2 : 4192 < scr2.length := by omega
        have h4193_2 : 4193 < scr2.length := by omega
        have h4207_2 : 4207 < scr2.length := by omega
        have h4211_2 : 4211 < scr2.length := by omega
        let nv := scr2[4192]'h4192_2; let nc := scr2[4193]'h4193_2
        let acap := scr2[4207]'h4207_2; let nunits := scr2[4211]'h4211_2
        have hnv_o : (scr2[(@OfNat.ofNat Nat 4192 _)]'h4192_2).toNat = nv.toNat := rfl
        have hnc_o : (scr2[(@OfNat.ofNat Nat 4193 _)]'h4193_2).toNat = nc.toNat := rfl
        have hacap_o : (scr2[(@OfNat.ofNat Nat 4207 _)]'h4207_2).toNat = acap.toNat := rfl
        have hnunits_o : (scr2[(@OfNat.ofNat Nat 4211 _)]'h4211_2).toNat = nunits.toNat := rfl
        have hac_eq2 : (scr2[4207]?.getD 0#32) = acap := m8_k6_get_eq h4207_2
        have hlg2 := hks2.1.length_ge; rw [hks2.2.2.2.2.1, hmv_eq, hac_eq2] at hlg2
        have hscr2_4192 : (((scr1.set 4205 tick_lim).set 4204 (0 : BitVec 32))[4192]'(by
          simp [hl1]; omega)).toNat = nv.toNat := rfl
        have hscr2_4193 : (((scr1.set 4205 tick_lim).set 4204 (0 : BitVec 32))[4193]'(by
          simp [hl1]; omega)).toNat = nc.toNat := rfl
        have hscr2_4207 : (((scr1.set 4205 tick_lim).set 4204 (0 : BitVec 32))[4207]'(by
          simp [hl1]; omega)).toNat = acap.toNat := rfl
        have hscr2_4211 : (((scr1.set 4205 tick_lim).set 4204 (0 : BitVec 32))[4211]'(by
          simp [hl1]; omega)).toNat = nunits.toNat := rfl
        c0_hsplit
        · c0_hsteps!; exact hret_s 0#64 scr2 _ hks2 hm
        · have hnv_le : nv.toNat ≤ mv.toNat := Nat.le_of_not_lt hc
          c0_hsplit
          · c0_hsteps!; exact hret_s 0#64 scr2 _ hks2 hm
          · have hmc_n : (mv <<< (2 : Nat)).toNat = 4 * mv.toNat := fid_bv32_shl2_toNat (by omega)
            have hmo_n : (mv <<< (1 : Nat)).toNat = 2 * mv.toNat := m8_bv32_shl1_toNat (by omega)
            have hnv2_n : (nv <<< (1 : Nat)).toNat = 2 * nv.toNat := m8_bv32_shl1_toNat (by omega)
            have hnc_le : nc.toNat ≤ 4 * mv.toNat := by
              have hc' := hc; fid_norm_ofnat; (try simp only [bv_c0, Nat.reducePow] at hc')
              try rw [hscr2_4193] at hc'; dsimp only [mv]; omega
            c0_hsplit
            · c0_hsteps!; exact hret_s 0#64 scr2 _ hks2 hm
            · have hnu_le : nunits.toNat ≤ 2 * mv.toNat := by
                have hc' := hc; fid_norm_ofnat; (try simp only [bv_c0, Nat.reducePow] at hc')
                try rw [hscr2_4211] at hc'; dsimp only [mv]; omega
              let invU : Mem 64 → Prop := fun mu' => ∃ scru' : List (BitVec 32),
                FidSolveKeep scr0 scru' ∧ scru'[4193]? = scr2[4193]? ∧
                (FullMem c (m8ScrSt s scru') ⋆ R) mu'
              c0_hsteps_nogrp
              refine wp_loop_group (ts := [i32])
                (fun rem_u (ui, ()) mu => ∃ scru : List (BitVec 32), FidSolveKeep scr0 scru ∧
                  ui.toNat ≤ nunits.toNat ∧ rem_u = nunits.toNat - ui.toNat ∧
                  scru[4193]? = scr2[4193]? ∧ (FullMem c (m8ScrSt s scru) ⋆ R) mu) ?_ ?_
              · rintro Lu rem_u ⟨ui, ⟨⟩⟩ mu hLu ⟨scru, hku, hui_le, rfl, h193, hmu⟩
                have hlu : scru.length = scr0.length := hku.2.1
                have hmin_u : 15744 ≤ scru.length := by omega
                c0_hsplit
                · have hui_lt : ui.toNat < nunits.toNat := hc
                  have hui1 : (ui + 1#32).toNat = ui.toNat + 1 :=
                    m8_bv32_add1_toNat hui_lt (by omega)
                  have hun_e := fid_k6_off_add (mv := mv) (k := 41) (x := ui) hmv_hi (by decide)
                    (by omega)
                  have hun_b : ((4224 + 41 * mv + ui).setWidth 64).toNat < scru.length := by
                    rw [hlu, hun_e]; omega
                  let ucid := scru[((4224 + 41 * mv + ui).setWidth 64).toNat]'hun_b
                  c0_hsteps_nogrp
                  refine wp_join0 invU (fun _ mu' ⟨scru', hku', h193', hmu'⟩ => by
                      c0_hsteps!; exact hLu (nunits.toNat - (ui + 1#32).toNat) (ui + 1#32, ()) mu'
                        (by omega) ⟨scru', hku', by omega, rfl, h193', hmu'⟩)
                    (fun Js hJs => by
                      c0_hsplit
                      · have huc_lt : ucid.toNat < nc.toNat := by
                          have hc' := hc; fid_norm_ofnat
                          simp only [Nat.reducePow, BitVec.reduceToNat] at hc'
                          have h1 : (scru[(4224 + 41 * (scr0[4214]'h4214).toNat + ui.toNat) %
                              4294967296]'(by rw [hlu]; omega)).toNat = ucid.toNat :=
                            congrArg BitVec.toNat (m8_k6_get_congr (by rw [hun_e]; omega) _ _)
                          try rw [h1] at hc'
                          try rw [hscr2_4193] at hc'; exact hc'
                        have hco_e := fid_k6_off_add (mv := mv) (k := 29) (x := ucid) hmv_hi
                          (by decide) (by omega)
                        have hco_b : ((4224 + 29 * mv + ucid).setWidth 64).toNat < scru.length := by
                          rw [hlu, hco_e]; omega
                        let off := scru[((4224 + 29 * mv + ucid).setWidth 64).toNat]'hco_b
                        c0_hsteps_nogrp
                        refine wp_join0 invU (fun _ mu' h => by c0_hsteps!; exact hJs mu' h)
                          (fun Js1 hJs1 => by
                            have huc : scru[(4224 + 41 * (scr0[4214]'h4214).toNat + ui.toNat) %
                                4294967296]'(by rw [hmv_d, hlu]; omega) = ucid :=
                              m8_k6_get_congr (by rw [hmv_d, hun_e]; omega) _ _
                            have hoff_g : scru[(4224 + 29 * (scr0[4214]'h4214).toNat +
                                (scru[(4224 + 41 * (scr0[4214]'h4214).toNat + ui.toNat) %
                                  4294967296]'(by rw [hmv_d, hlu]; omega)).toNat) %
                                4294967296]'(by rw [huc, hmv_d, hlu]; omega) = off :=
                              m8_k6_get_congr (by rw [huc, hmv_d, hco_e]; omega) _ _
                            c0_hsplit
                            · have hoff_lt : off.toNat < acap.toNat := by
                                have hc' := hc; fid_norm_ofnat
                                simp only [Nat.reducePow, BitVec.reduceToNat] at hc'
                                rw [congrArg BitVec.toNat hoff_g] at hc'
                                try rw [hscr2_4207] at hc'; exact hc'
                              have hcap_lt : scr2.length < 2 ^ 30 := by rw [hks2.2.1]; exact hlen_lt
                              have har_e := fid_k6_off_add (mv := mv) (k := 45) (x := off) hmv_hi
                                (by decide) (by omega)
                              have har_b :
                                  ((4224 + 45 * mv + off).setWidth 64).toNat < scru.length :=
                                by rw [hlu, har_e]; omega
                              let ul := scru[((4224 + 45 * mv + off).setWidth 64).toNat]'har_b
                              c0_hsteps_nogrp
                              refine wp_join0 invU (fun _ mu' h => by c0_hsteps!; exact hJs1 mu' h)
                                (fun Js2 hJs2 => by
                                  c0_hsplit
                                  · have hul_lt : ul.toNat < 2 * nv.toNat := by
                                      have hc' := hc; fid_norm_ofnat
                                      simp only [Nat.reducePow, BitVec.reduceToNat] at hc'
                                      have hul_g : (scru[(4224 + 45 * (scr0[4214]'h4214).toNat +
                                          (scru[(4224 + 29 * (scr0[4214]'h4214).toNat +
                                            (scru[(4224 + 41 * (scr0[4214]'h4214).toNat +
                                              ui.toNat) % 4294967296]'(by
                                                rw [hmv_d, hlu]; omega)).toNat) % 4294967296]'(by
                                              rw [huc, hmv_d, hlu]; omega)).toNat) %
                                          4294967296]'(by
                                            rw [hoff_g, hmv_d, hlu]; omega)).toNat = ul.toNat :=
                                        congrArg BitVec.toNat (m8_k6_get_congr (by
                                          rw [hoff_g, hmv_d, har_e]; omega) _ _)
                                      rw [hul_g] at hc'; try rw [hscr2_4192] at hc'
                                      rw [Nat.mod_eq_of_lt
                                        (by omega : nv.toNat * 2 < 2 ^ 32)] at hc'
                                      omega
                                    have hvl_e := fid_k6_off_add (mv := mv) (k := 9) (x := ul)
                                      hmv_hi (by decide) (by omega)
                                    have hvl_b : ((4224 + 9 * mv + ul).setWidth 64).toNat <
                                        scru.length := by rw [hlu, hvl_e]; omega
                                    c0_hsplit
                                    · c0_hsteps!
                                      exact hret_s 20#64 _ _ (fidSolveKeep_hdr hku 4199 ucid) hm
                                    · c0_hsteps_nogrp
                                      refine wp_join0 invU
                                        (fun _ mu' h => by c0_hsteps!; exact hJs2 mu' h)
                                        (fun Js3 hJs3 => by
                                          c0_hsplit
                                          · c0_hsteps_nogrp; fid_call hAssign
                                            refine fidK6AssignSpec_intro rfl (fidScr_lengthsOk hlen
                                              (hlu.trans hscr_len)) (m8ScrSt_buf s scru ▸ hku.1)
                                              (m8ScrSt_eq s scru ▸ hmu) ?_
                                            intro scr_a m_a hla hka hm_a
                                            have hku' := fidSolveKeep_of_assign hku
                                              (hla.trans (hlu.trans hscr_len).symm)
                                              (fun idx hi => hka idx (by omega))
                                            have h193' : scr_a[4193]? = scr2[4193]? :=
                                              (hka 4193 (by omega) (by decide) (by decide)
                                                (Or.inl (by decide)) (Or.inl (by omega))
                                                (Or.inl (by omega))).trans h193
                                            c0_hsteps!
                                            exact hJs3 m_a ⟨scr_a, hku', h193', by rwa [m8ScrSt_eq]⟩
                                          · c0_hsteps!; exact hJs3 mu ⟨scru, hku, h193, hmu⟩)
                                  · c0_hsteps!; exact hJs2 mu ⟨scru, hku, h193, hmu⟩)
                            · c0_hsteps!; exact hJs1 mu ⟨scru, hku, h193, hmu⟩)
                      · c0_hsteps!; exact hJs mu ⟨scru, hku, h193, hmu⟩)
                · c0_hsteps_nogrp; fid_call hProp
                  refine fidK6PropSpec_intro rfl (fidScr_lengthsOk hlen (hlu.trans hscr_len))
                    (m8ScrSt_buf s scru ▸ hku.1) (m8ScrSt_eq s scru ▸ hmu) ?_
                  intro confl0 scrp0 mp0 _ _ hokp0 hlp0 hlo0 _ hhi0 _ _ hmet0 hmp0
                  have hksp0 := fidSolveKeep_of_prop hku hokp0
                    (hlp0.trans (hlu.trans hscr_len).symm) hlo0 hhi0 hmet0
                  have hmin_p0 : 15744 ≤ scrp0.length := by omega
                  have hmp0' : (FullMem c (m8ScrSt s scrp0) ⋆ R) mp0 := by rwa [m8ScrSt_eq]
                  c0_hsplit
                  · c0_hsteps!; exact hret_s 20#64 _ _ (fidSolveKeep_hdr hksp0 4199 confl0) hm
                  · have hmp0f : (FullMem c (m8ScrFuelSt s s.core.fuel scrp0) ⋆ R) mp0 := by
                      rwa [m8ScrFuelSt_self]
                    c0_hsteps_nogrp
                    refine wp_loop_group (ts := [i32])
                      (fun rem_f (confl, ()) mf => ∃ (fl_f : BitVec 64) (scrf : List (BitVec 32)),
                        FidSolveKeep scr0 scrf ∧ fl_f.toNat ≤ s.core.fuel.toNat ∧
                        rem_f = fl_f.toNat ∧ (FullMem c (m8ScrFuelSt s fl_f scrf) ⋆ R) mf) ?_ ?_
                    · rintro Lf rem_f ⟨confl, ⟨⟩⟩ mf hLf ⟨fl_f, scrf, hkf, hfl_le, rfl, hmf⟩
                      have hlf : scrf.length = scr0.length := hkf.2.1
                      have hmin_f : 15744 ≤ scrf.length := by omega
                      c0_hsplit
                      · c0_hsplit
                        · have hfl_pos : 0 < fl_f.toNat := hc
                          have hfl1 : (fl_f - 1#64).toNat = fl_f.toNat - 1 :=
                            m8_bv64_sub1_toNat hfl_pos
                          let fl' := fl_f - 1#64; clear hm; c0_hsteps_nogrp
                          c0_hsplit
                          · c0_hsteps!
                            exact hret_f 20#64 fl' _ _ (fidSolveKeep_hdr hkf 4199 confl)
                              (by dsimp only [fl']; omega) hm
                          · c0_hsteps_nogrp; fid_call hAnalyze
                            refine fidK6AnalyzeSpec_intro (s := m8ScrFuelSt s fl' scrf) rfl
                              (m8ScrFuelSt_lengthsOk hlen (hlf.trans hscr_len) fl')
                              (by rw [m8ScrFuelSt_buf]; exact hkf.1) (by assumption) ?_
                            intro ok_a scr_a m_a; dsimp only
                            intro hok_a hl_a hlo_a h194_a hnc_a haux_a _ _ h207_a h211_a _
                              h216_a h217_a h218_a hun_a hm_a
                            rw [m8ScrFuelSt_buf] at hlo_a h194_a hnc_a haux_a h207_a h211_a
                            rw [m8ScrFuelSt_buf] at h216_a h217_a h218_a hun_a
                            rw [m8ScrFuelSt_upd] at hm_a
                            have hka := fidSolveKeep_of_analyze hkf hok_a
                              (hl_a.trans (hlf.trans hscr_len).symm) hlo_a h194_a hnc_a haux_a
                              h207_a h211_a h216_a h217_a h218_a hun_a
                            c0_hsplit
                            · c0_hsteps_nogrp; fid_call hProp
                              refine fidK6PropSpec_intro (s := m8ScrFuelSt s fl' scr_a) rfl
                                (m8ScrFuelSt_lengthsOk hlen hl_a fl')
                                (by rw [m8ScrFuelSt_buf]; exact hok_a) hm_a ?_
                              intro confl' scr_p m_p; dsimp only
                              intro hok_p hl_p hlo_p _ hhi_p _ _ hmet_p hm_p
                              rw [m8ScrFuelSt_buf] at hlo_p hhi_p hmet_p
                              rw [m8ScrFuelSt_upd] at hm_p
                              have hkp := fidSolveKeep_of_prop hka hok_p (hl_p.trans hl_a.symm)
                                hlo_p hhi_p hmet_p
                              c0_hsteps!; exact hLf fl'.toNat (confl', ()) m_p
                                (by dsimp only [fl']; omega)
                                ⟨fl', scr_p, hkp, by dsimp only [fl']; omega, rfl, hm_p⟩
                            · c0_hsteps!
                              exact hret_f 0#64 fl' scr_a m_a hka (by dsimp only [fl']; omega) hm_a
                          · c0_hsteps!
                            exact hret_f 10#64 fl' scrf _ hkf (by dsimp only [fl']; omega)
                              (by assumption)
                          · let invQ := fun pk mp => (pk = 0xFFFFFFFF#32 ∨ pk.toNat < nv.toNat) ∧
                              (FullMem c (m8ScrFuelSt s fl' scrf) ⋆ R) mp
                            c0_hsteps_nogrp
                            refine wp_while_break_state (brkTs := [i32, i32, i32])
                              (lpTs := [i32, i32])
                              (fun st : BitVec 32 × BitVec 32 × BitVec 32 =>
                                (st.1, st.2.1, st.2.2, ())) (fun st mp => invQ st.2.1 mp)
                              (fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
                              (fun st => nv.toNat - st.2.toNat)
                              (fun st mp => st.2.toNat ≤ nv.toNat ∧
                                (FullMem c (m8ScrFuelSt s fl' scrf) ⋆ R) mp) ?_ ?_ ?_
                            · rintro _ ⟨cur1, pk1, stp1⟩ mp1 ⟨hpk1, hm1⟩; c0_hsteps_nogrp
                              refine wp_join_state (ts := [i32, i32, i32])
                                (α := BitVec 32 × BitVec 32 × BitVec 32)
                                (fun st => (st.1, st.2.1, st.2.2, ()))
                                (fun st mp => invQ st.2.1 mp) ?_ ?_
                              · intro _ ⟨c2, pk2, stp2⟩ mp2 ⟨hpk2, hm2⟩; c0_hsteps_nogrp
                                refine wp_join_state (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
                                  (fun st => (st.1, st.2, ())) (fun st mp => invQ st.2 mp) ?_ ?_
                                · intro _ ⟨c3, pk3⟩ mp3 ⟨hpk3, hm3⟩
                                  c0_hsplit
                                  · c0_hsteps!; exact hret_f 10#64 fl' scrf _ hkf
                                      (by dsimp only [fl']; omega) hm3
                                  · have hpk3_lt : pk3.toNat < nv.toNat := hpk3.resolve_left hc
                                    have hfl_e := fid_k6_off_add (mv := mv) (k := 6) (x := pk3)
                                      hmv_hi (by decide) (by omega)
                                    have hfl_b : ((4224 + 6 * mv + pk3).setWidth 64).toNat <
                                        (scrf.set 4202 pk3).length := by
                                      rw [List.length_set, hlf, hfl_e]; omega
                                    have h4195_d : 4195 < (scrf.set 4202 pk3).length := by
                                      simp [hlf]; omega
                                    let scr_d := (scrf.set 4202 pk3).set 4195
                                      ((scrf.set 4202 pk3)[4195]'h4195_d + 1#32)
                                    have hkd : FidSolveKeep scr0 scr_d :=
                                      fidSolveKeep_hdr (fidSolveKeep_hdr hkf 4202 pk3) 4195 _
                                    have hld : scr_d.length = scr0.length := hkd.2.1
                                    c0_hsteps_nogrp; fid_call hAssign
                                    refine fidK6AssignSpec_intro (s := m8ScrFuelSt s fl' scr_d) rfl
                                      (m8ScrFuelSt_lengthsOk hlen (hld.trans hscr_len) fl')
                                      (by rw [m8ScrFuelSt_buf]; exact hkd.1) hm ?_
                                    intro scr_a m_a hla hka hm_a
                                    rw [m8ScrFuelSt_buf] at hka; rw [m8ScrFuelSt_upd] at hm_a
                                    have hka' := fidSolveKeep_of_assign hkd
                                      (hla.trans (hld.trans hscr_len).symm)
                                      (fun idx hi => hka idx (by omega))
                                    c0_hsteps_nogrp; fid_call hProp
                                    refine fidK6PropSpec_intro (s := m8ScrFuelSt s fl' scr_a) rfl
                                      (m8ScrFuelSt_lengthsOk hlen hla fl')
                                      (by rw [m8ScrFuelSt_buf]; exact hka'.1) hm_a ?_
                                    intro confl' scr_p m_p; dsimp only
                                    intro hok_p hl_p hlo_p _ hhi_p _ _ hmet_p hm_p
                                    rw [m8ScrFuelSt_buf] at hlo_p hhi_p hmet_p
                                    rw [m8ScrFuelSt_upd] at hm_p
                                    have hkp := fidSolveKeep_of_prop hka' hok_p
                                      (hl_p.trans hla.symm) hlo_p hhi_p hmet_p
                                    c0_hsteps!; exact hLf fl'.toNat (confl', ()) m_p
                                      (by dsimp only [fl']; omega)
                                      ⟨fl', scr_p, hkp, by dsimp only [fl']; omega, rfl, hm_p⟩
                                · intro J3 hJ3; c0_hsplit
                                  · c0_hsteps_nogrp
                                    refine wp_while_break_state (brkTs := [i32, i32])
                                      (lpTs := [i32])
                                      (fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
                                      (fun st mp => invQ st.2 mp) (fun cur : BitVec 32 => (cur, ()))
                                      (fun cur => nv.toNat - cur.toNat)
                                      (fun cur mp => cur.toNat ≤ nv.toNat ∧
                                        (FullMem c (m8ScrFuelSt s fl' scrf) ⋆ R) mp) ?_ ?_ ?_
                                    · rintro _ ⟨c3, pk3⟩ mp3 ⟨hpk3, hm3⟩
                                      c0_hsteps!; exact hJ3 (c3, pk3) mp3 ⟨hpk3, hm3⟩
                                    · rintro B3 L3 cur mp3 hB3 ih3 ⟨hcur_le, hm3⟩; c0_hsplit
                                      · have hcur_lt : cur.toNat < nv.toNat := hc
                                        have hc1 : (cur + 1#32).toNat = cur.toNat + 1 :=
                                          m8_bv32_add1_toNat hcur_lt (by omega)
                                        have hvl_b := (fidSolve_q_bnds hmv_hi
                                          (Nat.lt_of_lt_of_le hcur_lt hnv_le) (hlf ▸ hbge)).1
                                        c0_hsplit
                                        · c0_hsteps!; exact hB3 (cur, cur) mp3 ⟨Or.inr hcur_lt, hm3⟩
                                        · c0_hsteps!; exact ih3 (cur + 1#32) mp3
                                            (by rw [hc1]; omega) ⟨by rw [hc1]; omega, hm3⟩
                                      · c0_hsteps!; exact hB3 (cur, pk2) mp3 ⟨hpk2, hm3⟩
                                    · intro B3 L3 _ hL3; c0_hsteps!
                                      exact hL3 0#32 mp2 ⟨Nat.zero_le _, hm2⟩
                                  · c0_hsteps!; exact hJ3 (c2, pk2) mp2 ⟨hpk2, hm2⟩
                              · intro J2 hJ2; c0_hsplit
                                · c0_hsteps_nogrp
                                  refine wp_while_break_state (brkTs := [i32, i32, i32])
                                    (lpTs := [i32, i32])
                                    (fun st : BitVec 32 × BitVec 32 × BitVec 32 =>
                                      (st.1, st.2.1, st.2.2, ())) (fun st mp => invQ st.2.1 mp)
                                    (fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
                                    (fun st => nv.toNat - st.2.toNat)
                                    (fun st mp => st.2.toNat ≤ nv.toNat ∧
                                      (FullMem c (m8ScrFuelSt s fl' scrf) ⋆ R) mp) ?_ ?_ ?_
                                  · rintro _ ⟨c2, pk2, stp2⟩ mp2 ⟨hpk2, hm2⟩
                                    c0_hsteps!; exact hJ2 (c2, pk2, stp2) mp2 ⟨hpk2, hm2⟩
                                  · rintro B2 L2 ⟨cur, stp⟩ mp2 hB2 ih2 ⟨hst_le, hm2⟩; c0_hsplit
                                    · have hcur_lt : cur.toNat < nv.toNat := hc; c0_hsplit
                                      · have hst_lt : stp.toNat < nv.toNat := hc
                                        have hs1 : (stp + 1#32).toNat = stp.toNat + 1 :=
                                          m8_bv32_add1_toNat hst_lt (by omega)
                                        obtain ⟨hvl_b, hqp_b⟩ := fidSolve_q_bnds
                                          hmv_hi (Nat.lt_of_lt_of_le hcur_lt hnv_le)
                                          (hlf ▸ hbge)
                                        c0_hsplit
                                        · c0_hsteps!; exact hB2 (cur, cur, stp) mp2
                                            ⟨Or.inr hcur_lt, hm2⟩
                                        · let nc2 :=
                                            scrf[((4224 + 2 * mv + cur).setWidth 64).toNat]'hqp_b
                                          c0_hsteps!; exact ih2 (nc2, stp + 1#32) mp2
                                            (by dsimp only; rw [hs1]; omega)
                                            ⟨by dsimp only; rw [hs1]; omega, hm2⟩
                                      · c0_hsteps!; exact hB2 (cur, pk1, stp) mp2 ⟨hpk1, hm2⟩
                                    · c0_hsteps!; exact hB2 (cur, pk1, stp) mp2 ⟨hpk1, hm2⟩
                                  · intro B2 L2 _ hL2; c0_hsteps!
                                    exact hL2 (_, 0#32) mp1 ⟨Nat.zero_le _, hm1⟩
                                · c0_hsteps!; exact hJ2 (cur1, pk1, stp1) mp1 ⟨hpk1, hm1⟩
                            · rintro B1 L1 ⟨cur, stp⟩ mp1 hB1 ih1 ⟨hst_le, hm1⟩; c0_hsplit
                              · have hcur_lt : cur.toNat < nv.toNat := hc; c0_hsplit
                                · have hst_lt : stp.toNat < nv.toNat := hc
                                  have hs1 : (stp + 1#32).toNat = stp.toNat + 1 :=
                                    m8_bv32_add1_toNat hst_lt (by omega)
                                  obtain ⟨hvl_b, hqp_b⟩ := fidSolve_q_bnds
                                    hmv_hi (Nat.lt_of_lt_of_le hcur_lt hnv_le) (hlf ▸ hbge)
                                  c0_hsplit
                                  · c0_hsteps!; exact hB1 (cur, cur, stp) mp1 ⟨Or.inr hcur_lt, hm1⟩
                                  · let nc1 :=
                                      scrf[((4224 + 2 * mv + cur).setWidth 64).toNat]'hqp_b
                                    c0_hsteps!; exact ih1 (nc1, stp + 1#32) mp1
                                      (by dsimp only; rw [hs1]; omega)
                                      ⟨by dsimp only; rw [hs1]; omega, hm1⟩
                                · c0_hsteps!
                                  exact hB1 (cur, 0xFFFFFFFF#32, stp) mp1 ⟨Or.inl rfl, hm1⟩
                              · c0_hsteps!
                                exact hB1 (cur, 0xFFFFFFFF#32, stp) mp1 ⟨Or.inl rfl, hm1⟩
                            · intro B1 L1 _ hL1; c0_hsteps!
                              exact hL1 (_, 0#32) _ ⟨Nat.zero_le _, by assumption⟩
                        · c0_hsteps!; exact hret_f 0#64 fl_f scrf mf hkf hfl_le hmf
                      · c0_hsteps!; exact hret_f 0#64 fl_f scrf mf hkf hfl_le hmf
                    · intro Lf hLf; c0_hsteps!; exact hLf s.core.fuel.toNat (confl0, ()) mp0
                        ⟨s.core.fuel, scrp0, hksp0, Nat.le_refl _, rfl, hmp0f⟩
              · intro Lu hLu; c0_hsteps!; exact hLu nunits.toNat (0#32, ()) _
                  ⟨scr2, hks2, Nat.zero_le _, by simp, rfl, hm⟩

end LeanQbe.T.Examples.Kissat.FullFidelityBve
