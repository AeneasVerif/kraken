/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpFidBasic

/-!
# Kissat Fidelity BVE WP Proofs — `full_k6_analyze_fid_wp`

`CanonicalEnv`-clean `Func.wp` proof for `full_k6_analyze_fid` (`0` legacy `Full*` imports;
zero `@[expose]` on theorems; every decl `<= 450` LOC; `<= 100` cols).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Definition

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Definition
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open Kraken.Bedrock2.Test

open scoped FidK6Tactics M8K6bTactics FidK6DefTactics

public section

local macro_rules
  | `(tactic| c0_bound) => `(tactic| first | assumption | rfl | decide | omega | fid_omega)

/-! ## 1. `FidAnaInv`, `FidAnaPost` & Callee Helpers -/

private def FidAnaInv (scr0 : List (BitVec 32)) (mv : Nat) (scr : List (BitVec 32)) : Prop :=
  scr.length = scr0.length ∧
  (∀ i, i < 4195 → scr[i]? = scr0[i]?) ∧
  scr[4199]? = scr0[4199]? ∧
  (∀ i, 4204 ≤ i → i < 4208 → scr[i]? = scr0[i]?) ∧
  scr[4211]? = scr0[4211]? ∧
  (∀ i, 4213 ≤ i → i < 4224 → scr[i]? = scr0[i]?) ∧
  (∀ i, 4224 + 29 * mv ≤ i → i < 4224 + 43 * mv → scr[i]? = scr0[i]?)

private def FidAnaPost (scr0 : List (BitVec 32)) (mv : Nat) (scr : List (BitVec 32)) : Prop :=
  scr.length = scr0.length ∧
  (∀ i, i < 4193 → scr[i]? = scr0[i]?) ∧
  scr[4194]? = scr0[4194]? ∧
  (scr0[4193]?.getD 0#32).toNat ≤ (scr[4193]?.getD 0#32).toNat ∧
  (∀ cid < (scr0[4193]?.getD 0#32).toNat,
    scr[4224 + 37 * mv + cid]? = scr0[4224 + 37 * mv + cid]?) ∧
  scr[4199]? = scr0[4199]? ∧ scr[4205]? = scr0[4205]? ∧
  scr[4207]? = scr0[4207]? ∧ scr[4211]? = scr0[4211]? ∧
  scr[4213]? = scr0[4213]? ∧ scr[4214]? = scr0[4214]? ∧
  scr[4215]? = scr0[4215]? ∧ scr[4216]? = scr0[4216]? ∧
  (∀ i, 4224 + 41 * mv ≤ i → i < 4224 + 43 * mv → scr[i]? = scr0[i]?)

private theorem fidAnaInv_refl (scr0 : List (BitVec 32)) (mv : Nat) :
    FidAnaInv scr0 mv scr0 :=
  ⟨rfl, fun _ _ => rfl, rfl, fun _ _ _ => rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

private theorem fidAna_bv32_ofNat_toNat (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by simp)

private theorem fidAna_get_congr {xs : List (BitVec 32)} {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) (h : i = j) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

private theorem fidAnaInv_to_post {scr0 scra : List (BitVec 32)} {mv : Nat}
    (hnc : (scr0[4193]?.getD 0#32).toNat ≤ 4 * mv)
    (hk : FidAnaInv scr0 mv scra) : FidAnaPost scr0 mv scra :=
  ⟨hk.1, fun i hi => hk.2.1 i (by omega), hk.2.1 4194 (by omega),
    by rw [hk.2.1 4193 (by omega)]; exact Nat.le_refl _,
    fun cid hcid => hk.2.2.2.2.2.2 _ (by omega) (by omega),
    hk.2.2.1, hk.2.2.2.1 4205 (by omega) (by omega),
    hk.2.2.2.1 4207 (by omega) (by omega), hk.2.2.2.2.1,
    hk.2.2.2.2.2.1 4213 (by omega) (by omega),
    hk.2.2.2.2.2.1 4214 (by omega) (by omega),
    hk.2.2.2.2.2.1 4215 (by omega) (by omega),
    hk.2.2.2.2.2.1 4216 (by omega) (by omega),
    fun i h1 h2 => hk.2.2.2.2.2.2 i (by omega) h2⟩

private theorem fidAnaInv_set {scr0 scra : List (BitVec 32)} {mv idx : Nat}
    (hk : FidAnaInv scr0 mv scra) (v : BitVec 32)
    (hidx : (4208 ≤ idx ∧ idx < 4211) ∨ idx = 4212 ∨
      (4224 + 6 * mv ≤ idx ∧ idx < 4224 + 9 * mv)) :
    FidAnaInv scr0 mv (scra.set idx v) := by
  refine ⟨by simp [hk.1], fun i hi => ?_, ?_, fun i h1 h2 => ?_, ?_, fun i h1 h2 => ?_,
    fun i h1 h2 => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.1 i hi
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.2.1
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.2.2.1 i h1 h2
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.2.2.2.1
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.2.2.2.2.1 i h1 h2
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.2.2.2.2.2 i h1 h2

private theorem fidK6BufOk_of_pres {scr scrb : List (BitVec 32)} {mv : Nat}
    (hok : FidK6BufOk scr) (h4214 : 4214 < scr.length)
    (hmv : scr[4214]?.getD 0#32 = BitVec.ofNat 32 mv) (hmv_hi : mv ≤ 8192)
    (hlen : scrb.length = scr.length) (h4193 : scrb[4193]? = scr[4193]?)
    (h4206 : scrb[4206]? = scr[4206]?) (h4207 : scrb[4207]? = scr[4207]?)
    (h4214b : scrb[4214]? = scr[4214]?)
    (hcl : ∀ i, 4224 + 29 * mv ≤ i → i < 4224 + 41 * mv → scrb[i]? = scr[i]?) :
    FidK6BufOk scrb := by
  have hnc := hok.nc_le
  have _ := h4214
  have hmv_nat : (scr[4214]?.getD 0#32).toNat = mv := by
    rw [hmv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hmv_nat] at hnc
  refine ⟨by rw [h4214b]; exact hok.mv_lo, by rw [h4214b]; exact hok.mv_hi,
    by rw [h4214b, h4207, hlen]; exact hok.length_ge, by rw [hlen]; exact hok.length_lt,
    by rw [h4193, h4214b]; exact hok.nc_le, by rw [h4206, h4207]; exact hok.alen_le,
    fun cid hcid => ?_⟩
  rw [h4193] at hcid
  have h0 := hok.clause_ok (cid := cid) hcid
  have hcid4 : cid < 4 * mv := Nat.lt_of_lt_of_le hcid hnc
  rw [hmv_nat] at h0
  rw [h4214b, h4207, hmv_nat,
    hcl (4224 + 29 * mv + cid) (by omega) (by omega),
    hcl (4224 + 33 * mv + cid) (by omega) (by omega),
    hcl (4224 + 37 * mv + cid) (by omega) (by omega)]
  exact h0

private theorem fidAnaInv_bufOk {scr0 scra : List (BitVec 32)} {mv : BitVec 32}
    (hok : FidK6BufOk scr0) (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (hmv_hi : mv.toNat ≤ 8192) (hk : FidAnaInv scr0 mv.toNat scra) :
    FidK6BufOk scra :=
  fidK6BufOk_of_pres hok h4214 (by rw [hmv_eq, fidAna_bv32_ofNat_toNat]) hmv_hi hk.1
    (hk.2.1 4193 (by omega)) (hk.2.2.2.1 4206 (by omega) (by omega))
    (hk.2.2.2.1 4207 (by omega) (by omega)) (hk.2.2.2.2.2.1 4214 (by omega) (by omega))
    (fun i h1 h2 => hk.2.2.2.2.2.2 i h1 (by omega))

private theorem fidAnaInv_to_post_ok {scr0 scra : List (BitVec 32)} {mv : BitVec 32}
    (hok : FidK6BufOk scr0) (h4214 : 4214 < scr0.length) (hmv : scr0[4214]?.getD 0#32 = mv)
    (hmv_hi : mv.toNat ≤ 8192) (hk : FidAnaInv scr0 mv.toNat scra) :
    FidAnaPost scr0 mv.toNat scra ∧ FidK6BufOk scra := by
  have hnc : (scr0[4193]?.getD 0#32).toNat ≤ 4 * mv.toNat := by
    have := hok.nc_le; rwa [hmv] at this
  exact ⟨fidAnaInv_to_post hnc hk, fidAnaInv_bufOk hok h4214 hmv hmv_hi hk⟩

private theorem fidAnaInv_of_ana_cl {c : FullCfg} {scr0 scra scrb : List (BitVec 32)} {mv : Nat}
    (hk : FidAnaInv scr0 mv scra) (h4214 : 4214 < scr0.length)
    (hlen_ge : 4224 + 45 * mv ≤ scr0.length)
    (hmv_eq : scr0[4214]?.getD 0#32 = BitVec.ofNat 32 mv) (hmv_hi : mv ≤ 8192)
    (hlen : scr0.length = c.scratch_cap) (hlb : scrb.length = c.scratch_cap)
    (ha : ∀ idx < c.scratch_cap, idx ≠ 4208 → idx ≠ 4209 → idx ≠ 4210 → idx ≠ 4212 →
      (idx < 4224 + 6 * (scra[4214]?.getD 0#32).toNat ∨
        4224 + 9 * (scra[4214]?.getD 0#32).toNat ≤ idx) →
      (idx < 4224 + 43 * (scra[4214]?.getD 0#32).toNat ∨
        4224 + 45 * (scra[4214]?.getD 0#32).toNat ≤ idx) →
      scrb[idx]? = scra[idx]?) :
    FidAnaInv scr0 mv scrb := by
  have _ := h4214
  have hmva : (scra[4214]?.getD 0#32).toNat = mv := by
    rw [hk.2.2.2.2.2.1 4214 (by omega) (by omega), hmv_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  rw [hmva] at ha
  refine ⟨by rw [hlb, ← hlen], fun i hi => ?_, ?_, fun i h1 h2 => ?_, ?_,
    fun i h1 h2 => ?_, fun i h1 h2 => ?_⟩
  · rw [ha i (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
      (Or.inl (by omega))]; exact hk.2.1 i hi
  · rw [ha 4199 (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
      (Or.inl (by omega))]; exact hk.2.2.1
  · rw [ha i (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
      (Or.inl (by omega))]; exact hk.2.2.2.1 i h1 h2
  · rw [ha 4211 (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
      (Or.inl (by omega))]; exact hk.2.2.2.2.1
  · rw [ha i (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
      (Or.inl (by omega))]; exact hk.2.2.2.2.2.1 i h1 h2
  · rw [ha i (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
      (Or.inl (by omega))]; exact hk.2.2.2.2.2.2 i h1 h2

private theorem fidAnaInv_of_backtrack {c : FullCfg} {scr0 scra scrb : List (BitVec 32)} {mv : Nat}
    (hk : FidAnaInv scr0 mv scra) (h4214 : 4214 < scr0.length)
    (hlen_ge : 4224 + 45 * mv ≤ scr0.length)
    (hmv_eq : scr0[4214]?.getD 0#32 = BitVec.ofNat 32 mv) (hmv_hi : mv ≤ 8192)
    (hlen : scr0.length = c.scratch_cap) (hlb : scrb.length = c.scratch_cap)
    (hb : ∀ idx < c.scratch_cap,
      (idx < 4195 ∨ (4199 ≤ idx ∧ idx < 4224) ∨
        (4224 + 2 * (scra[4214]?.getD 0#32).toNat ≤ idx ∧
          idx < 4224 + 9 * (scra[4214]?.getD 0#32).toNat) ∨
        4224 + 11 * (scra[4214]?.getD 0#32).toNat ≤ idx) → scrb[idx]? = scra[idx]?) :
    FidAnaInv scr0 mv scrb := by
  have _ := h4214
  have hmva : (scra[4214]?.getD 0#32).toNat = mv := by
    rw [hk.2.2.2.2.2.1 4214 (by omega) (by omega), hmv_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  rw [hmva] at hb
  refine ⟨by rw [hlb, ← hlen], fun i hi => ?_, ?_, fun i h1 h2 => ?_, ?_,
    fun i h1 h2 => ?_, fun i h1 h2 => ?_⟩
  · rw [hb i (by omega) (Or.inl hi)]; exact hk.2.1 i hi
  · rw [hb 4199 (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hk.2.2.1
  · rw [hb i (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hk.2.2.2.1 i h1 h2
  · rw [hb 4211 (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hk.2.2.2.2.1
  · rw [hb i (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hk.2.2.2.2.2.1 i h1 h2
  · rw [hb i (by omega) (Or.inr (Or.inr (Or.inr (by omega))))]; exact hk.2.2.2.2.2.2 i h1 h2

private theorem fidAnaInv_of_mtf {c : FullCfg} {scr0 scra scrb : List (BitVec 32)} {mv : Nat}
    (hk : FidAnaInv scr0 mv scra) (h4214 : 4214 < scr0.length)
    (hlen_ge : 4224 + 45 * mv ≤ scr0.length)
    (hmv_eq : scr0[4214]?.getD 0#32 = BitVec.ofNat 32 mv) (hmv_hi : mv ≤ 8192)
    (hlen : scr0.length = c.scratch_cap) (hlb : scrb.length = c.scratch_cap)
    (hm : ∀ idx < c.scratch_cap,
      (idx < 4200 ∨ (4204 ≤ idx ∧ idx < 4224 + 2 * (scra[4214]?.getD 0#32).toNat) ∨
        4224 + 5 * (scra[4214]?.getD 0#32).toNat ≤ idx) → scrb[idx]? = scra[idx]?) :
    FidAnaInv scr0 mv scrb := by
  have _ := h4214
  have hmva : (scra[4214]?.getD 0#32).toNat = mv := by
    rw [hk.2.2.2.2.2.1 4214 (by omega) (by omega), hmv_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  rw [hmva] at hm
  refine ⟨by rw [hlb, ← hlen], fun i hi => ?_, ?_, fun i h1 h2 => ?_, ?_,
    fun i h1 h2 => ?_, fun i h1 h2 => ?_⟩
  · rw [hm i (by omega) (Or.inl (by omega))]; exact hk.2.1 i hi
  · rw [hm 4199 (by omega) (Or.inl (by omega))]; exact hk.2.2.1
  · rw [hm i (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hk.2.2.2.1 i h1 h2
  · rw [hm 4211 (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hk.2.2.2.2.1
  · rw [hm i (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hk.2.2.2.2.2.1 i h1 h2
  · rw [hm i (by omega) (Or.inr (Or.inr (by omega)))]; exact hk.2.2.2.2.2.2 i h1 h2

private theorem fidAnaPost_of_watch {c : FullCfg} {scr0 scra scrb : List (BitVec 32)} {mv : Nat}
    (hp : FidAnaPost scr0 mv scra) (hok : FidK6BufOk scra)
    (h4214 : 4214 < scr0.length) (hlen_ge : 4224 + 45 * mv ≤ scr0.length)
    (hmv_eq : scr0[4214]?.getD 0#32 = BitVec.ofNat 32 mv)
    (hmv_hi : mv ≤ 8192) (hlen : scr0.length = c.scratch_cap) (hlb : scrb.length = c.scratch_cap)
    (hw : ∀ idx < c.scratch_cap,
      (idx < 4224 + 11 * (scra[4214]?.getD 0#32).toNat ∨
        4224 + 29 * (scra[4214]?.getD 0#32).toNat ≤ idx) → scrb[idx]? = scra[idx]?) :
    FidAnaPost scr0 mv scrb ∧ FidK6BufOk scrb := by
  have _ := h4214
  have hmva : (scra[4214]?.getD 0#32).toNat = mv := by
    rw [hp.2.2.2.2.2.2.2.2.2.2.1, hmv_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hmva] at hw
  have hla : scra.length = scr0.length := hp.1
  have h4214a : 4214 < scra.length := by omega
  have h1 : FidAnaPost scr0 mv scrb :=
    ⟨by rw [hlb, ← hlen],
      fun i hi => by rw [hw i (by omega) (Or.inl (by omega))]; exact hp.2.1 i hi,
      by rw [hw 4194 (by omega) (Or.inl (by omega))]; exact hp.2.2.1,
      by rw [hw 4193 (by omega) (Or.inl (by omega))]; exact hp.2.2.2.1,
      fun cid hcid => by
        by_cases hlt : 4224 + 37 * mv + cid < c.scratch_cap
        · rw [hw _ hlt (Or.inr (by omega))]; exact hp.2.2.2.2.1 cid hcid
        · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)],
      by rw [hw 4199 (by omega) (Or.inl (by omega))]; exact hp.2.2.2.2.2.1,
      by rw [hw 4205 (by omega) (Or.inl (by omega))]; exact hp.2.2.2.2.2.2.1,
      by rw [hw 4207 (by omega) (Or.inl (by omega))]; exact hp.2.2.2.2.2.2.2.1,
      by rw [hw 4211 (by omega) (Or.inl (by omega))]; exact hp.2.2.2.2.2.2.2.2.1,
      by rw [hw 4213 (by omega) (Or.inl (by omega))]; exact hp.2.2.2.2.2.2.2.2.2.1,
      by rw [hw 4214 (by omega) (Or.inl (by omega))]; exact hp.2.2.2.2.2.2.2.2.2.2.1,
      by rw [hw 4215 (by omega) (Or.inl (by omega))]; exact hp.2.2.2.2.2.2.2.2.2.2.2.1,
      by rw [hw 4216 (by omega) (Or.inl (by omega))]; exact hp.2.2.2.2.2.2.2.2.2.2.2.2.1,
      fun i h1 h2 => by
        rw [hw i (by omega) (Or.inr (by omega))]
        exact hp.2.2.2.2.2.2.2.2.2.2.2.2.2 i h1 h2⟩
  refine ⟨h1, fidK6BufOk_of_pres hok h4214a (by rw [hp.2.2.2.2.2.2.2.2.2.2.1, hmv_eq]) hmv_hi
    (by rw [hlb, ← hlen, ← hp.1]) (hw 4193 (by omega) (Or.inl (by omega)))
    (hw 4206 (by omega) (Or.inl (by omega))) (hw 4207 (by omega) (Or.inl (by omega)))
    (hw 4214 (by omega) (Or.inl (by omega)))
    (fun i h29 h41 => hw i (by omega) (Or.inr (by omega)))⟩

private theorem fidAnaPost_of_assign {c : FullCfg} {scr0 scra scrb : List (BitVec 32)} {mv : Nat}
    (hp : FidAnaPost scr0 mv scra) (hok : FidK6BufOk scra)
    (h4214 : 4214 < scr0.length) (hlen_ge : 4224 + 45 * mv ≤ scr0.length)
    (hmv_eq : scr0[4214]?.getD 0#32 = BitVec.ofNat 32 mv)
    (hmv_hi : mv ≤ 8192) (hlen : scr0.length = c.scratch_cap) (hlb : scrb.length = c.scratch_cap)
    (ha : ∀ idx < c.scratch_cap, idx ≠ 4197 → idx ≠ 4198 →
      (idx < 4224 ∨ 4224 + 2 * (scra[4214]?.getD 0#32).toNat ≤ idx) →
      (idx < 4224 + 5 * (scra[4214]?.getD 0#32).toNat ∨
        4224 + 7 * (scra[4214]?.getD 0#32).toNat ≤ idx) →
      (idx < 4224 + 9 * (scra[4214]?.getD 0#32).toNat ∨
        4224 + 11 * (scra[4214]?.getD 0#32).toNat ≤ idx) → scrb[idx]? = scra[idx]?) :
    FidAnaPost scr0 mv scrb ∧ FidK6BufOk scrb := by
  have _ := h4214
  have hmva : (scra[4214]?.getD 0#32).toNat = mv := by
    rw [hp.2.2.2.2.2.2.2.2.2.2.1, hmv_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hmva] at ha
  have hla : scra.length = scr0.length := hp.1
  have h4214a : 4214 < scra.length := by omega
  have ha' : ∀ idx < c.scratch_cap, (idx < 4197 ∨ (4199 ≤ idx ∧ idx < 4224) ∨
      4224 + 11 * mv ≤ idx) → scrb[idx]? = scra[idx]? := by
    intro idx hlt hr
    rcases hr with h1 | ⟨h1, h2⟩ | h1
    · exact ha idx hlt (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
        (Or.inl (by omega))
    · exact ha idx hlt (by omega) (by omega) (Or.inl h2) (Or.inl (by omega)) (Or.inl (by omega))
    · exact ha idx hlt (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr h1)
  have h1 : FidAnaPost scr0 mv scrb :=
    ⟨by rw [hlb, ← hlen],
      fun i hi => by rw [ha' i (by omega) (Or.inl (by omega))]; exact hp.2.1 i hi,
      by rw [ha' 4194 (by omega) (Or.inl (by omega))]; exact hp.2.2.1,
      by rw [ha' 4193 (by omega) (Or.inl (by omega))]; exact hp.2.2.2.1,
      fun cid hcid => by
        by_cases hlt : 4224 + 37 * mv + cid < c.scratch_cap
        · rw [ha' _ hlt (Or.inr (Or.inr (by omega)))]; exact hp.2.2.2.2.1 cid hcid
        · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)],
      by rw [ha' 4199 (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hp.2.2.2.2.2.1,
      by rw [ha' 4205 (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hp.2.2.2.2.2.2.1,
      by rw [ha' 4207 (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))]
         exact hp.2.2.2.2.2.2.2.1,
      by rw [ha' 4211 (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))]
         exact hp.2.2.2.2.2.2.2.2.1,
      by rw [ha' 4213 (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))]
         exact hp.2.2.2.2.2.2.2.2.2.1,
      by rw [ha' 4214 (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))]
         exact hp.2.2.2.2.2.2.2.2.2.2.1,
      by rw [ha' 4215 (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))]
         exact hp.2.2.2.2.2.2.2.2.2.2.2.1,
      by rw [ha' 4216 (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))]
         exact hp.2.2.2.2.2.2.2.2.2.2.2.2.1,
      fun i h1 h2 => by
        rw [ha' i (by omega) (Or.inr (Or.inr (by omega)))]
        exact hp.2.2.2.2.2.2.2.2.2.2.2.2.2 i h1 h2⟩
  refine ⟨h1, fidK6BufOk_of_pres hok h4214a (by rw [hp.2.2.2.2.2.2.2.2.2.2.1, hmv_eq]) hmv_hi
    (by rw [hlb, ← hlen, ← hp.1]) (ha' 4193 (by omega) (Or.inl (by omega)))
    (ha' 4206 (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    (ha' 4207 (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    (ha' 4214 (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    (fun i h29 h41 => ha' i (by omega) (Or.inr (Or.inr (by omega))))⟩

private theorem fidAnaInv_set_arena {scr0 scra : List (BitVec 32)} {mv idx : Nat}
    (hk : FidAnaInv scr0 mv scra) (v : BitVec 32) (hidx : 4224 + 45 * mv ≤ idx) :
    FidAnaInv scr0 mv (scra.set idx v) := by
  refine ⟨by simp [hk.1], fun i hi => ?_, ?_, fun i h1 h2 => ?_, ?_, fun i h1 h2 => ?_,
    fun i h1 h2 => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.1 i hi
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.2.1
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.2.2.1 i h1 h2
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.2.2.2.1
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.2.2.2.2.1 i h1 h2
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.2.2.2.2.2 i h1 h2

private theorem fidAnaCommit_fin {scr0 scrb : List (BitVec 32)}
    {mv nc alen acap nkl nres : BitVec 32}
    (hok : FidK6BufOk scr0) (hk : FidAnaInv scr0 mv.toNat scrb) (h4214 : 4214 < scr0.length)
    (hmv_eq : scr0[4214]?.getD 0#32 = mv) (hmv_lo : 256 ≤ mv.toNat) (hmv_hi : mv.toNat ≤ 8192)
    (hbge : 4224 + 45 * mv.toNat ≤ scr0.length) (hnc_eq : scr0[4193]? = some nc)
    (hac_eq : scr0[4207]? = some acap) (hnc_lt : nc.toNat < 4 * mv.toNat)
    (hnkl_lo : 1 ≤ nkl.toNat) (hnkl_hi : nkl.toNat ≤ mv.toNat)
    (_hnres_hi : nres.toNat ≤ 2 * mv.toNat)
    (halen_le : alen.toNat + nkl.toNat + nres.toNat ≤ acap.toNat)
    (hof_e : ((4224 + 29 * mv + nc).setWidth 64).toNat = 4224 + 29 * mv.toNat + nc.toNat)
    (hmt_e : ((4224 + 33 * mv + nc).setWidth 64).toNat = 4224 + 33 * mv.toNat + nc.toNat)
    (hax_e : ((4224 + 37 * mv + nc).setWidth 64).toNat = 4224 + 37 * mv.toNat + nc.toNat) :
    let scrc := ((((scrb.set 4206 ((alen + nkl) + nres)).set
      ((4224 + 29 * mv + nc).setWidth 64).toNat alen).set
      ((4224 + 33 * mv + nc).setWidth 64).toNat (nkl ||| 1073741824#32)).set
      ((4224 + 37 * mv + nc).setWidth 64).toNat nres).set 4193 (nc + 1#32)
    FidAnaPost scr0 mv.toNat scrc ∧ FidK6BufOk scrc := by
  intro scrc
  have hlb : scrb.length = scr0.length := hk.1
  have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := m8_bv32_add1_toNat hnc_lt (by omega)
  have hcm_sz : ((nkl ||| 1073741824#32) &&& 65535#32) = nkl := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_or,
      show (1073741824#32 : BitVec 32).toNat = 2 ^ 30 from rfl,
      show (65535#32 : BitVec 32).toNat = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_two_pow]
    rcases Nat.lt_or_ge i 16 with hi | hi
    · simp [hi, show 30 ≠ i from by omega]
    · have hn : nkl.toNat.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by decide) hi))
      simp [Nat.not_lt_of_ge hi, hn]
  have hal_sum : ((alen + nkl) + nres).toNat = alen.toNat + nkl.toNat + nres.toNat := by
    have hlt := hok.length_lt
    have hge := hok.length_ge
    rw [hmv_eq, hac_eq, Option.getD_some] at hge
    rw [BitVec.toNat_add, BitVec.toNat_add]
    have hs1 : alen.toNat + nkl.toNat < 2 ^ 32 := by omega
    rw [Nat.mod_eq_of_lt hs1, Nat.mod_eq_of_lt (by omega)]
  have hpres : ∀ idx, idx ≠ 4206 → idx ≠ 4193 →
      idx ≠ 4224 + 29 * mv.toNat + nc.toNat → idx ≠ 4224 + 33 * mv.toNat + nc.toNat →
      idx ≠ 4224 + 37 * mv.toNat + nc.toNat → scrc[idx]? = scrb[idx]? := by
    intro idx ha hb hc hd he
    dsimp only [scrc]
    rw [List.getElem?_set_ne hb.symm, List.getElem?_set_ne (by rw [hax_e]; exact he.symm),
      List.getElem?_set_ne (by rw [hmt_e]; exact hd.symm),
      List.getElem?_set_ne (by rw [hof_e]; exact hc.symm), List.getElem?_set_ne ha.symm]
  have hlc : scrc.length = scr0.length := by dsimp only [scrc]; simp [hk.1]
  have h4193c : scrc[4193]? = some (nc + 1#32) := by
    dsimp only [scrc]; apply List.getElem?_set_self; simp [hk.1]; omega
  have h4206c : scrc[4206]? = some ((alen + nkl) + nres) := by
    dsimp only [scrc]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by rw [hax_e]; omega),
      List.getElem?_set_ne (by rw [hmt_e]; omega), List.getElem?_set_ne (by rw [hof_e]; omega)]
    apply List.getElem?_set_self; rw [hk.1]; omega
  have h4207c : scrc[4207]? = some acap := by
    rw [hpres 4207 (by omega) (by omega) (by omega) (by omega) (by omega)]
    rw [hk.2.2.2.1 4207 (by omega) (by omega), hac_eq]
  have h4214c : scrc[4214]? = some mv := by
    rw [hpres 4214 (by omega) (by omega) (by omega) (by omega) (by omega)]
    rw [hk.2.2.2.2.2.1 4214 (by omega) (by omega), ← hmv_eq, List.getElem?_eq_getElem h4214,
      Option.getD_some]
  have hpost : FidAnaPost scr0 mv.toNat scrc := by
    refine ⟨hlc, fun i hi => ?_, ?_, ?_, fun cid hcid => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun i h1 h2 => ?_⟩
    · rw [hpres i (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hk.2.1 i (by omega)
    · rw [hpres 4194 (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hk.2.1 4194 (by omega)
    · rw [hnc_eq, h4193c, Option.getD_some, Option.getD_some, hnc1]; omega
    · rw [hnc_eq, Option.getD_some] at hcid
      rw [hpres _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hk.2.2.2.2.2.2 _ (by omega) (by omega)
    · rw [hpres 4199 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hk.2.2.1
    · rw [hpres 4205 (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hk.2.2.2.1 4205 (by omega) (by omega)
    · rw [h4207c, hac_eq]
    · rw [hpres 4211 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hk.2.2.2.2.1
    · rw [hpres 4213 (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hk.2.2.2.2.2.1 4213 (by omega) (by omega)
    · rw [h4214c, List.getElem?_eq_getElem h4214]
      congr 1; simpa [List.getElem?_eq_getElem h4214] using hmv_eq.symm
    · rw [hpres 4215 (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hk.2.2.2.2.2.1 4215 (by omega) (by omega)
    · rw [hpres 4216 (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hk.2.2.2.2.2.1 4216 (by omega) (by omega)
    · rw [hpres i (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hk.2.2.2.2.2.2 i (by omega) h2
  refine ⟨hpost, ⟨?_, ?_, ?_, ?_, ?_, ?_, fun cid hcid => ?_⟩⟩
  · rw [h4214c, Option.getD_some]; exact hmv_lo
  · rw [h4214c, Option.getD_some]; exact hmv_hi
  · rw [h4214c, h4207c, Option.getD_some, Option.getD_some, hlc]
    have := hok.length_ge; rw [hmv_eq, hac_eq, Option.getD_some] at this; exact this
  · rw [hlc]; exact hok.length_lt
  · rw [h4193c, h4214c, Option.getD_some, Option.getD_some, hnc1]; omega
  · rw [h4206c, h4207c, Option.getD_some, Option.getD_some, hal_sum]; exact halen_le
  · rw [h4193c, Option.getD_some, hnc1] at hcid
    rw [h4214c, h4207c, Option.getD_some, Option.getD_some]
    by_cases hlt : cid < nc.toNat
    · have h0 := hok.clause_ok (cid := cid) (by rw [hnc_eq, Option.getD_some]; exact hlt)
      rw [hmv_eq, hac_eq, Option.getD_some] at h0
      rw [hpres _ (by omega) (by omega) (by omega) (by omega) (by omega),
        hpres _ (by omega) (by omega) (by omega) (by omega) (by omega),
        hpres _ (by omega) (by omega) (by omega) (by omega) (by omega),
        hk.2.2.2.2.2.2 _ (by omega) (by omega), hk.2.2.2.2.2.2 _ (by omega) (by omega),
        hk.2.2.2.2.2.2 _ (by omega) (by omega)]
      exact h0
    · have hcid_eq : cid = nc.toNat := by omega
      subst hcid_eq
      have hofc : scrc[4224 + 29 * mv.toNat + nc.toNat]? = some alen := by
        dsimp only [scrc]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by rw [hax_e]; omega),
          List.getElem?_set_ne (by rw [hmt_e]; omega), ← hof_e]
        apply List.getElem?_set_self; simp [hk.1]; omega
      have hmtc : scrc[4224 + 33 * mv.toNat + nc.toNat]? = some (nkl ||| 1073741824#32) := by
        dsimp only [scrc]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by rw [hax_e]; omega), ← hmt_e]
        apply List.getElem?_set_self; simp [hk.1]; omega
      have haxc : scrc[4224 + 37 * mv.toNat + nc.toNat]? = some nres := by
        dsimp only [scrc]
        rw [List.getElem?_set_ne (by omega), ← hax_e]
        apply List.getElem?_set_self; simp [hk.1]; omega
      rw [hofc, hmtc, haxc, Option.getD_some, Option.getD_some, Option.getD_some]
      dsimp only; rw [hcm_sz]; exact ⟨by omega, fun _ => halen_le⟩

private theorem fidAna_call_ana_cl {Γ : Env} {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {scr0 scra : List (BitVec 32)} {mv cid skip_v : BitVec 32} {m : Mem 64}
    {k : Tup Val [] → Expr Val Cont [Ty.bool]} {Q : Post [Ty.bool]} {X : XPost}
    (hAna : Γ.Has "full_k6_ana_cl_fid" fidK6AnaClSpec) (hlen : FullState.LengthsOk c s)
    (hok : FidK6BufOk scr0) (hscr_len : scr0.length = c.scratch_cap)
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv) (hmv_hi : mv.toNat ≤ 8192)
    (hk : FidAnaInv scr0 mv.toNat scra) (hm : (FullMem c (m8ScrSt s scra) ⋆ R) m)
    (hK : ∀ (scrb : List (BitVec 32)) (mb : Mem 64), FidAnaInv scr0 mv.toNat scrb →
      (FullMem c (m8ScrSt s scrb) ⋆ R) mb → wp Γ Q X (k ()) mb) :
    wp Γ Q X (Expr.call (as := [i64, i32, i32]) (bs := []) "full_k6_ana_cl_fid"
      (Arg.var c.hdr, Arg.var cid, Arg.var skip_v, PUnit.unit) k) m := by
  c0_hcall hAna
  have hlena : FullState.LengthsOk c (m8ScrSt s scra) :=
    ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hk.1.trans hscr_len }⟩
  refine fidK6AnaClSpec_intro rfl hlena (fidAnaInv_bufOk hok h4214 hmv_eq hmv_hi hk) hm ?_
  intro scrb mb hlb ha hmb
  have hmv_nat : scr0[4214]?.getD 0#32 = BitVec.ofNat 32 mv.toNat := by
    rw [hmv_eq, fidAna_bv32_ofNat_toNat]
  have hge : 4224 + 45 * mv.toNat ≤ scr0.length := by
    have := hok.length_ge; rw [hmv_eq] at this; omega
  exact hK scrb mb (fidAnaInv_of_ana_cl hk h4214 hge hmv_nat hmv_hi hscr_len hlb ha) hmb

private theorem fidAna_call_backtrack {Γ : Env} {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {scr0 scra : List (BitVec 32)} {mv lvl : BitVec 32} {m : Mem 64}
    {k : Tup Val [] → Expr Val Cont [Ty.bool]} {Q : Post [Ty.bool]} {X : XPost}
    (hBt : Γ.Has "full_k6_backtrack_fid" fidK6BacktrackSpec) (hlen : FullState.LengthsOk c s)
    (hok : FidK6BufOk scr0) (hscr_len : scr0.length = c.scratch_cap)
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv) (hmv_hi : mv.toNat ≤ 8192)
    (hk : FidAnaInv scr0 mv.toNat scra) (hm : (FullMem c (m8ScrSt s scra) ⋆ R) m)
    (hK : ∀ (scrb : List (BitVec 32)) (mb : Mem 64), FidAnaInv scr0 mv.toNat scrb →
      (FullMem c (m8ScrSt s scrb) ⋆ R) mb → wp Γ Q X (k ()) mb) :
    wp Γ Q X (Expr.call (as := [i64, i32]) (bs := []) "full_k6_backtrack_fid"
      (Arg.var c.hdr, Arg.var lvl, PUnit.unit) k) m := by
  c0_hcall hBt
  have hlena : FullState.LengthsOk c (m8ScrSt s scra) :=
    ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hk.1.trans hscr_len }⟩
  refine fidK6BacktrackSpec_intro rfl hlena (fidAnaInv_bufOk hok h4214 hmv_eq hmv_hi hk) hm ?_
  intro scrb mb hlb hb hmb
  have hmv_nat : scr0[4214]?.getD 0#32 = BitVec.ofNat 32 mv.toNat := by
    rw [hmv_eq, fidAna_bv32_ofNat_toNat]
  have hge : 4224 + 45 * mv.toNat ≤ scr0.length := by
    have := hok.length_ge; rw [hmv_eq] at this; omega
  exact hK scrb mb (fidAnaInv_of_backtrack hk h4214 hge hmv_nat hmv_hi hscr_len hlb hb) hmb

private theorem fidAna_call_mtf {Γ : Env} {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {scr0 scra : List (BitVec 32)} {mv v : BitVec 32} {m : Mem 64}
    {k : Tup Val [] → Expr Val Cont [Ty.bool]} {Q : Post [Ty.bool]} {X : XPost}
    (hMtf : Γ.Has "full_k6_mtf_fid" fidK6MtfSpec) (hlen : FullState.LengthsOk c s)
    (hok : FidK6BufOk scr0) (hscr_len : scr0.length = c.scratch_cap)
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv) (hmv_hi : mv.toNat ≤ 8192)
    (hk : FidAnaInv scr0 mv.toNat scra) (hm : (FullMem c (m8ScrSt s scra) ⋆ R) m)
    (hK : ∀ (scrb : List (BitVec 32)) (mb : Mem 64), FidAnaInv scr0 mv.toNat scrb →
      (FullMem c (m8ScrSt s scrb) ⋆ R) mb → wp Γ Q X (k ()) mb) :
    wp Γ Q X (Expr.call (as := [i64, i32]) (bs := []) "full_k6_mtf_fid"
      (Arg.var c.hdr, Arg.var v, PUnit.unit) k) m := by
  c0_hcall hMtf
  have hlena : FullState.LengthsOk c (m8ScrSt s scra) :=
    ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hk.1.trans hscr_len }⟩
  refine fidK6MtfSpec_intro rfl hlena (fidAnaInv_bufOk hok h4214 hmv_eq hmv_hi hk) hm ?_
  intro scrb mb hlb hmt hmb
  have hmv_nat : scr0[4214]?.getD 0#32 = BitVec.ofNat 32 mv.toNat := by
    rw [hmv_eq, fidAna_bv32_ofNat_toNat]
  have hge : 4224 + 45 * mv.toNat ≤ scr0.length := by
    have := hok.length_ge; rw [hmv_eq] at this; omega
  exact hK scrb mb (fidAnaInv_of_mtf hk h4214 hge hmv_nat hmv_hi hscr_len hlb hmt) hmb

private theorem fidAna_call_watch {Γ : Env} {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {scr0 scra : List (BitVec 32)} {mv cid l0 l1 sz : BitVec 32} {m : Mem 64}
    {k : Tup Val [] → Expr Val Cont [Ty.bool]} {Q : Post [Ty.bool]} {X : XPost}
    (hWatch : Γ.Has "full_k6_watch_fid" fidK6WatchSpec) (hlen : FullState.LengthsOk c s)
    (hok : FidK6BufOk scra) (hscr_len : scr0.length = c.scratch_cap)
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv) (hmv_hi : mv.toNat ≤ 8192)
    (hp : FidAnaPost scr0 mv.toNat scra) (hm : (FullMem c (m8ScrSt s scra) ⋆ R) m)
    (hK : ∀ (scrb : List (BitVec 32)) (mb : Mem 64),
      FidAnaPost scr0 mv.toNat scrb → FidK6BufOk scrb → (FullMem c (m8ScrSt s scrb) ⋆ R) mb →
      wp Γ Q X (k ()) mb) :
    wp Γ Q X (Expr.call (as := [i64, i32, i32, i32, i32]) (bs := []) "full_k6_watch_fid"
      (Arg.var c.hdr, Arg.var cid, Arg.var l0, Arg.var l1, Arg.var sz, PUnit.unit) k) m := by
  c0_hcall hWatch
  have hlena : FullState.LengthsOk c (m8ScrSt s scra) :=
    ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hp.1.trans hscr_len }⟩
  refine fidK6WatchSpec_intro rfl hlena hok hm ?_
  intro scrb mb hlb hw hmb
  have hmv_nat : scr0[4214]?.getD 0#32 = BitVec.ofNat 32 mv.toNat := by
    rw [hmv_eq, fidAna_bv32_ofNat_toNat]
  have hge : 4224 + 45 * mv.toNat ≤ scr0.length := by
    have := hok.length_ge
    rw [hp.2.2.2.2.2.2.2.2.2.2.1, hmv_eq] at this; rw [hp.1] at this; omega
  obtain ⟨hp', hok'⟩ := fidAnaPost_of_watch hp hok h4214 hge hmv_nat hmv_hi hscr_len hlb hw
  exact hK scrb mb hp' hok' hmb

private theorem fidAna_call_assign {Γ : Env} {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {scr0 scra : List (BitVec 32)} {mv lit rsn : BitVec 32} {m : Mem 64}
    {k : Tup Val [] → Expr Val Cont [Ty.bool]} {Q : Post [Ty.bool]} {X : XPost}
    (hAssign : Γ.Has "full_k6_assign_fid" fidK6AssignSpec) (hlen : FullState.LengthsOk c s)
    (hok : FidK6BufOk scra) (hscr_len : scr0.length = c.scratch_cap)
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv) (hmv_hi : mv.toNat ≤ 8192)
    (hp : FidAnaPost scr0 mv.toNat scra) (hm : (FullMem c (m8ScrSt s scra) ⋆ R) m)
    (hK : ∀ (scrb : List (BitVec 32)) (mb : Mem 64),
      FidAnaPost scr0 mv.toNat scrb → FidK6BufOk scrb → (FullMem c (m8ScrSt s scrb) ⋆ R) mb →
      wp Γ Q X (k ()) mb) :
    wp Γ Q X (Expr.call (as := [i64, i32, i32]) (bs := []) "full_k6_assign_fid"
      (Arg.var c.hdr, Arg.var lit, Arg.var rsn, PUnit.unit) k) m := by
  c0_hcall hAssign
  have hlena : FullState.LengthsOk c (m8ScrSt s scra) :=
    ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hp.1.trans hscr_len }⟩
  refine fidK6AssignSpec_intro rfl hlena hok hm ?_
  intro scrb mb hlb ha hmb
  have hmv_nat : scr0[4214]?.getD 0#32 = BitVec.ofNat 32 mv.toNat := by
    rw [hmv_eq, fidAna_bv32_ofNat_toNat]
  have hge : 4224 + 45 * mv.toNat ≤ scr0.length := by
    have := hok.length_ge
    rw [hp.2.2.2.2.2.2.2.2.2.2.1, hmv_eq] at this; rw [hp.1] at this; omega
  obtain ⟨hp', hok'⟩ := fidAnaPost_of_assign hp hok h4214 hge hmv_nat hmv_hi hscr_len hlb ha
  exact hK scrb mb hp' hok' hmb

/-! ## 2. Commit Helper (`fidAnaCommitExpr` & `fidAna_commit_wp`) -/

@[reducible] private def fidScrPtr {ts : List Ty} (pScr : Val i64) (idx : Val i32)
    (k : Val i64 → Expr Val Cont ts) : Expr Val Cont ts :=
  Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var idx, ()) } fun p1 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
              args := (Arg.var p1.fst, Arg.imm 4, ()) } fun p2 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
              args := (Arg.var pScr, Arg.var p2.fst, ()) } fun p3 => k p3.fst

@[reducible] private def fidScrOffPtr {ts : List Ty} (pScr : Val i64) (base idx : Val i32)
    (k : Val i64 → Expr Val Cont ts) : Expr Val Cont ts :=
  Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
              args := (Arg.var base, Arg.var idx, ()) } fun p =>
  fidScrPtr pScr p.fst k

@[reducible] private def fidScrImmPtr {ts : List Ty} (pScr : Val i64) (idx : BitVec 32)
    (k : Val i64 → Expr Val Cont ts) : Expr Val Cont ts :=
  Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.imm idx, ()) } fun p1 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
              args := (Arg.var p1.fst, Arg.imm 4, ()) } fun p2 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
              args := (Arg.var pScr, Arg.var p2.fst, ()) } fun p3 => k p3.fst

private def fidAnaCommitExpr (pScr cHdr : BitVec 64)
    (mv nres nkl nc alen uip : BitVec 32) : Expr Val Cont [Ty.bool] :=
  let o_kl := 4224 + 8 * mv; let o_off := 4224 + 29 * mv; let o_mt := 4224 + 33 * mv
  let o_ax := 4224 + 37 * mv; let o_res := 4224 + 43 * mv; let o_ar := 4224 + 45 * mv
  Expr.group (sig := [[i32]]) (fun Js => Blocks.cons (fun p_93 =>
   Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
               args := (Arg.var p_93.fst, Arg.var nkl, ()) } fun p_94 =>
   Expr.jnz (Arg.var p_94.fst)
    (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                 args := (Arg.var o_ar, Arg.var alen, ()) } fun p =>
     fidScrOffPtr pScr p.fst p_93.fst fun pa =>
     fidScrOffPtr pScr o_kl p_93.fst fun pk =>
     Expr.load i32 (Arg.var pk) fun ld =>
     Expr.store (t := i32) (Arg.var ld) (Arg.var pa)
      (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                   args := (Arg.var p_93.fst, Arg.imm 1, ()) } fun p =>
       Expr.jump Js.fst (Arg.var p.fst, ())))
    (Expr.group (sig := [[i32]]) (fun Js => Blocks.cons (fun p_95 =>
      Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                  args := (Arg.var p_95.fst, Arg.var nres, ()) } fun p_96 =>
      Expr.jnz (Arg.var p_96.fst)
       (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                    args := (Arg.var o_ar, Arg.var alen, ()) } fun p =>
        Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                    args := (Arg.var p.fst, Arg.var nkl, ()) } fun p =>
        fidScrOffPtr pScr p.fst p_95.fst fun pa =>
        fidScrOffPtr pScr o_res p_95.fst fun pr =>
        Expr.load i32 (Arg.var pr) fun ld =>
        Expr.store (t := i32) (Arg.var ld) (Arg.var pa)
         (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                      args := (Arg.var p_95.fst, Arg.imm 1, ()) } fun p =>
          Expr.jump Js.fst (Arg.var p.fst, ())))
       (fidScrImmPtr pScr 4206 fun p_99 =>
        Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                    args := (Arg.var alen, Arg.var nkl, ()) } fun p_100 =>
        Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                    args := (Arg.var p_100.fst, Arg.var nres, ()) } fun p_101 =>
        Expr.store (Arg.var p_101.fst) (Arg.var p_99)
         (fidScrOffPtr pScr o_off nc fun p_105 =>
          Expr.store (t := i32) (Arg.var alen) (Arg.var p_105)
           (fidScrOffPtr pScr o_mt nc fun p_109 =>
            Expr.let_ { sig := [i32, i32], code := OpCode.or i32,
                        args := (Arg.var nkl, Arg.imm 1073741824, ()) } fun p_110 =>
            Expr.store (Arg.var p_110.fst) (Arg.var p_109)
             (fidScrOffPtr pScr o_ax nc fun p_114 =>
              Expr.store (t := i32) (Arg.var nres) (Arg.var p_114)
               (fidScrImmPtr pScr 4193 fun p_117 =>
                Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                            args := (Arg.var nc, Arg.imm 1, ()) } fun p_118 =>
                Expr.store (Arg.var p_118.fst) (Arg.var p_117)
                 (Expr.let_ { sig := [i32, i32],
                              code := OpCode.cmp CmpOp.eq i32 Ty.bool (by decide),
                              args := (Arg.var nkl, Arg.imm 1, ()) } fun p_119 =>
                  Expr.jnz (Arg.var p_119.fst)
                   (Expr.call (as := [i64, i32, i32]) (bs := []) "full_k6_assign_fid"
                     (Arg.var cHdr, Arg.var uip, Arg.var nc, PUnit.unit) fun _ =>
                    Expr.ret (rs := [Ty.bool]) (Arg.imm true, ()))
                   (fidScrPtr pScr o_kl fun p_122 =>
                    Expr.load i32 (Arg.var p_122) fun ld_11 =>
                    Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                args := (Arg.var o_kl, Arg.imm 1, ()) } fun p_123 =>
                    fidScrPtr pScr p_123.fst fun p_126 =>
                    Expr.load i32 (Arg.var p_126) fun ld =>
                    Expr.call (as := [i64, i32, i32, i32, i32]) (bs := []) "full_k6_watch_fid"
                     (Arg.var cHdr, Arg.var nc, Arg.var ld_11, Arg.var ld, Arg.var nkl,
                      PUnit.unit) fun _ =>
                    Expr.call (as := [i64, i32, i32]) (bs := []) "full_k6_assign_fid"
                     (Arg.var cHdr, Arg.var uip, Arg.var nc, PUnit.unit) fun _ =>
                    Expr.ret (rs := [Ty.bool]) (Arg.imm true, ())))))))))
      Blocks.nil) fun Js => Expr.jump Js.fst (Arg.imm 0, ()))) Blocks.nil)
  fun Js => Expr.jump Js.fst (Arg.imm 0, ())

private theorem fidAna_commit_wp (Γ : Env) (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (Q : Post [Ty.bool]) (X : XPost) (scr0 scr_in : List (BitVec 32))
    (nres nkl nc alen uip : BitVec 32) (m_in : Mem 64)
    (hWatch : Γ.Has "full_k6_watch_fid" fidK6WatchSpec)
    (hAssign : Γ.Has "full_k6_assign_fid" fidK6AssignSpec)
    (hlen : FullState.LengthsOk c s) (hok : FidK6BufOk scr0)
    (hscr_len : scr0.length = c.scratch_cap) (h4214 : 4214 < scr0.length) :
    let mv := scr0[4214]'h4214
    let acap := scr0[4207]'(by have := hok.base_ge; omega)
    256 ≤ mv.toNat → mv.toNat ≤ 8192 → 4224 + 45 * mv.toNat + acap.toNat ≤ scr0.length →
    scr0.length < 2 ^ 30 → scr0[4193]? = some nc → scr0[4207]? = some acap →
    nc.toNat < 4 * mv.toNat → 1 ≤ nkl.toNat → nkl.toNat ≤ mv.toNat →
    nres.toNat ≤ 2 * mv.toNat → alen.toNat + nkl.toNat + nres.toNat ≤ acap.toNat →
    FidAnaInv scr0 mv.toNat scr_in → (FullMem c (m8ScrSt s scr_in) ⋆ R) m_in →
    (∀ (ok : Bool) (scrb : List (BitVec 32)) (mb : Mem 64),
      FidK6BufOk scrb → FidAnaPost scr0 mv.toNat scrb →
      (FullMem c (m8ScrSt s scrb) ⋆ R) mb → Q (ok, ()) mb) →
    wp Γ Q X (fidAnaCommitExpr c.pScratchBuf c.hdr mv nres nkl nc alen uip) m_in := by
  intro mv acap hmv_lo hmv_hi hlen_scr hcap_lt hnc_eq hac_eq hnc_lt hnkl_lo hnkl_hi
    hnres_hi halen_le hkin hm_in hQret
  have hmv_eq : scr0[4214]?.getD 0#32 = mv := m8_k6_get_eq h4214
  dsimp only [fidAnaCommitExpr, fidScrPtr, fidScrOffPtr, fidScrImmPtr]
  c0_hstraight
  refine wp_loop_group (ts := [i32])
    (fun rem (i, ()) m => ∃ scra, FidAnaInv scr0 mv.toNat scra ∧ i.toNat ≤ nkl.toNat ∧
      rem = nkl.toNat - i.toNat ∧ (FullMem c (m8ScrSt s scra) ⋆ R) m) ?_ ?_
  · rintro L1 rem ⟨i, ⟨⟩⟩ m hL1 ⟨scra, hka, hi_le, rfl, hma⟩
    have hla : scra.length = scr0.length := hka.1
    c0_hstraight; c0_hsplit
    · have hi_lt : i.toNat < nkl.toNat := hc
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := m8_bv32_add1_toNat hi_lt (by omega)
      have har_e := fid_k6_off_add2 (mv := mv) (k := 45) (x := alen) (y := i) hmv_hi
        (by decide) (by omega)
      have hkl_e := fid_k6_off_add (mv := mv) (k := 8) (x := i) hmv_hi (by decide) (by omega)
      have hkl_lt : ((4224 + 8 * mv + i).setWidth 64).toNat < scra.length := by
        rw [hla, hkl_e]; omega
      have har_lt : ((4224 + 45 * mv + alen + i).setWidth 64).toNat < scra.length := by
        rw [hla, har_e]; omega
      c0_hsteps!
      exact hL1 (nkl.toNat - (i + 1#32).toNat) (i + 1#32, ()) _ (by omega)
        ⟨_, fidAnaInv_set_arena hka _ (by rw [har_e]; omega), by omega, rfl, hm⟩
    · c0_hstraight
      refine wp_loop_group (ts := [i32])
        (fun rem (j, ()) mb => ∃ scrb, FidAnaInv scr0 mv.toNat scrb ∧ j.toNat ≤ nres.toNat ∧
          rem = nres.toNat - j.toNat ∧ (FullMem c (m8ScrSt s scrb) ⋆ R) mb) ?_ ?_
      · rintro L2 rem2 ⟨j, ⟨⟩⟩ mb hL2 ⟨scrb, hkb, hj_le, rfl, hmb⟩
        have hlb : scrb.length = scr0.length := hkb.1
        c0_hstraight; c0_hsplit
        · have hj_lt : j.toNat < nres.toNat := hc
          have hj1 : (j + 1#32).toNat = j.toNat + 1 := m8_bv32_add1_toNat hj_lt (by omega)
          have h2_e : (alen + nkl).toNat = alen.toNat + nkl.toNat := by
            rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
          have har_e := fid_k6_off_add2 (mv := mv) (k := 45) (x := alen + nkl) (y := j)
            hmv_hi (by decide) (by rw [h2_e]; omega)
          have hrs_e := fid_k6_off_add (mv := mv) (k := 43) (x := j) hmv_hi (by decide)
            (by omega)
          have har_eq : 4224 + 45 * mv + alen + nkl + j = 4224 + 45 * mv + (alen + nkl) + j := by
            rw [BitVec.add_assoc (4224 + 45 * mv) alen nkl]
          have hrs_lt : ((4224 + 43 * mv + j).setWidth 64).toNat < scrb.length := by
            rw [hlb, hrs_e]; omega
          have har_lt : ((4224 + 45 * mv + alen + nkl + j).setWidth 64).toNat <
              scrb.length := by
            rw [har_eq, hlb, har_e, h2_e]; omega
          c0_hsteps!
          exact hL2 (nres.toNat - (j + 1#32).toNat) (j + 1#32, ()) _ (by omega)
            ⟨_, fidAnaInv_set_arena hkb _ (by rw [har_eq, har_e, h2_e]; omega),
              by omega, rfl, hm⟩
        · have hlb : scrb.length = scr0.length := hkb.1
          have h4206_lt : 4206 < scrb.length := by omega
          have hof_e := fid_k6_off_add (mv := mv) (k := 29) (x := nc) hmv_hi (by decide)
            (by omega)
          have hmt_e := fid_k6_off_add (mv := mv) (k := 33) (x := nc) hmv_hi (by decide)
            (by omega)
          have hax_e := fid_k6_off_add (mv := mv) (k := 37) (x := nc) hmv_hi (by decide)
            (by omega)
          have hof_lt : ((4224 + 29 * mv + nc).setWidth 64).toNat <
              (scrb.set 4206 ((alen + nkl) + nres)).length := by
            rw [List.length_set, hlb, hof_e]; omega
          have hmt_lt : ((4224 + 33 * mv + nc).setWidth 64).toNat <
              ((scrb.set 4206 ((alen + nkl) + nres)).set
                ((4224 + 29 * mv + nc).setWidth 64).toNat alen).length := by
            simp only [List.length_set, hlb, hmt_e]; omega
          have hax_lt : ((4224 + 37 * mv + nc).setWidth 64).toNat <
              (((scrb.set 4206 ((alen + nkl) + nres)).set
                ((4224 + 29 * mv + nc).setWidth 64).toNat alen).set
                ((4224 + 33 * mv + nc).setWidth 64).toNat (nkl ||| 1073741824#32)).length := by
            simp only [List.length_set, hlb, hax_e]; omega
          have h4193_lt : 4193 <
              ((((scrb.set 4206 ((alen + nkl) + nres)).set
                ((4224 + 29 * mv + nc).setWidth 64).toNat alen).set
                ((4224 + 33 * mv + nc).setWidth 64).toNat (nkl ||| 1073741824#32)).set
                ((4224 + 37 * mv + nc).setWidth 64).toNat nres).length := by
            simp only [List.length_set, hlb]; omega
          c0_hstraight
          have hfin := fidAnaCommit_fin hok hkb h4214 hmv_eq hmv_lo hmv_hi (by omega)
            hnc_eq hac_eq hnc_lt hnkl_lo hnkl_hi hnres_hi halen_le hof_e hmt_e hax_e
          c0_hsplit
          · exact fidAna_call_assign hAssign hlen hfin.2 hscr_len h4214 hmv_eq hmv_hi hfin.1 hm
              (fun scrd md hpd hokd hmd => by c0_hsteps!; exact hQret true scrd md hokd hpd hmd)
          · have h2_nkl : 2 ≤ nkl.toNat := by
              have hc' : nkl ≠ 1#32 := hc
              rcases Nat.eq_or_lt_of_le hnkl_lo with h1 | h2
              · exfalso; apply hc'; apply BitVec.eq_of_toNat_eq; simp [← h1]
              · exact h2
            let scrc := ((((scrb.set 4206 ((alen + nkl) + nres)).set
              ((4224 + 29 * mv + nc).setWidth 64).toNat alen).set
              ((4224 + 33 * mv + nc).setWidth 64).toNat (nkl ||| 1073741824#32)).set
              ((4224 + 37 * mv + nc).setWidth 64).toNat nres).set 4193 (nc + 1#32)
            have hl0_e : ((4224 + 8 * mv).setWidth 64).toNat = 4224 + 8 * mv.toNat := by
              have h := fid_k6_off_add (mv := mv) (k := 8) (x := 0#32) hmv_hi (by decide)
                (by decide)
              rw [BitVec.add_zero] at h; simpa using h
            have hl1_e : ((4224 + 8 * mv + 1#32).setWidth 64).toNat = 4224 + 8 * mv.toNat + 1 := by
              simpa using fid_k6_off_add (mv := mv) (k := 8) (x := 1#32) hmv_hi (by decide)
                (by decide)
            have hl0_lt : ((4224 + 8 * mv).setWidth 64).toNat < scrc.length := by
              rw [hl0_e]; simp only [scrc, List.length_set, hlb]; omega
            have hl1_lt : ((4224 + 8 * mv + 1#32).setWidth 64).toNat < scrc.length := by
              rw [hl1_e]; simp only [scrc, List.length_set, hlb]; omega
            c0_hstraight
            refine fidAna_call_watch hWatch hlen hfin.2 hscr_len h4214 hmv_eq hmv_hi hfin.1 hm ?_
            intro scrd md hpd hokd hmd
            exact fidAna_call_assign hAssign hlen hokd hscr_len h4214 hmv_eq hmv_hi hpd hmd
              (fun scre me hpe hoke hme => by c0_hsteps!; exact hQret true scre me hoke hpe hme)
      · intro L2 hL2; c0_hsteps!; exact hL2 nres.toNat (0#32, ()) m ⟨scra, hka, by simp, rfl, hma⟩
  · intro L1 hL1
    c0_hsteps!; exact hL1 nkl.toNat (0#32, ()) m_in ⟨scr_in, hkin, by simp, rfl, hm_in⟩

/-! ## 3. Post-Resolution Helper (`fidAnaPostResExpr` & `fidAna_post_res_wp`) -/

private theorem fidAna_shl1_toNat {x : BitVec 32} (hx : x.toNat ≤ 8192) :
    (x <<< (1 : BitVec 32)).toNat = 2 * x.toNat := by
  change (x <<< 1).toNat = 2 * x.toNat
  rw [BitVec.toNat_shiftLeft]; simp only [Nat.shiftLeft_eq]; omega

private theorem fidAna_shl2_toNat {x : BitVec 32} (hx : x.toNat ≤ 8192) :
    (x <<< (2 : BitVec 32)).toNat = 4 * x.toNat := by
  change (x <<< 2).toNat = 4 * x.toNat
  rw [BitVec.toNat_shiftLeft]; simp only [Nat.shiftLeft_eq]; omega

private def fidAnaPostResExpr (pScr cHdr : BitVec 64)
    (mv nv uip : BitVec 32) : Expr Val Cont [Ty.bool] :=
  let o_mv4 : BitVec 32 := mv <<< 2
  let o_mv2 : BitVec 32 := mv <<< 1
  let o_seen : BitVec 32 := 4224 + 6 * mv
  let o_bump : BitVec 32 := 4224 + 7 * mv
  let o_kl : BitVec 32 := 4224 + 8 * mv
  fidScrImmPtr pScr 4208 fun p_55 => Expr.load i32 (Arg.var p_55) fun ld_5 =>
  Expr.group (sig := [[i32]]) (fun Js => Blocks.cons (fun p_56 =>
   Expr.group (sig := [[i32]]) (fun Js => Blocks.cons (fun p_57 =>
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                args := (Arg.var p_57.fst, Arg.var p_56.fst, ()) } fun p_58 =>
    Expr.jnz (Arg.var p_58.fst)
     (fidScrOffPtr pScr o_bump p_57.fst fun p => Expr.load i32 (Arg.var p) fun ld_6 =>
      Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
       Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                   args := (Arg.var p_57.fst, Arg.imm 1, ()) } fun p =>
       Expr.jump Js.fst (Arg.var p.fst, ())) Blocks.nil) fun Js =>
      Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                  args := (Arg.var ld_6, Arg.var nv, ()) } fun p =>
      Expr.jnz (Arg.var p.fst)
       (fidScrOffPtr pScr o_seen ld_6 fun p =>
        fidScrOffPtr pScr o_seen ld_6 fun p_62 => Expr.load i32 (Arg.var p_62) fun ld =>
        Expr.let_ { sig := [i32], code := OpCode.not i32, args := (Arg.imm 2, ()) } fun p_63 =>
        Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                    args := (Arg.var ld, Arg.var p_63.fst, ()) } fun p_64 =>
        Expr.store (Arg.var p_64.fst) (Arg.var p) (Expr.jump Js.fst ()))
       (Expr.jump Js.fst ()))
     (fidScrImmPtr pScr 4210 fun p_61 => Expr.load i32 (Arg.var p_61) fun ld_6 =>
      fidScrImmPtr pScr 4209 fun p_64 => Expr.load i32 (Arg.var p_64) fun ld_7 =>
      Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool (by decide),
                  args := (Arg.var uip, Arg.imm 4294967295, ()) } fun p_65 =>
      Expr.jnz (Arg.var p_65.fst) (Expr.ret (rs := [Ty.bool]) (Arg.imm false, ()))
       (Expr.let_ { sig := [i32, i32], code := OpCode.shl i32,
                    args := (Arg.var nv, Arg.imm 1, ()) } fun p_66 =>
        Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.uge i32 Ty.bool (by decide),
                    args := (Arg.var uip, Arg.var p_66.fst, ()) } fun p_67 =>
        Expr.jnz (Arg.var p_67.fst) (Expr.ret (rs := [Ty.bool]) (Arg.imm false, ()))
         (Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ugt i32 Ty.bool (by decide),
                      args := (Arg.var ld_6, Arg.var o_mv2, ()) } fun p_68 =>
          Expr.jnz (Arg.var p_68.fst) (Expr.ret (rs := [Ty.bool]) (Arg.imm false, ()))
           (Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool (by decide),
                        args := (Arg.var ld_7, Arg.imm 0, ()) } fun p_69 =>
            Expr.jnz (Arg.var p_69.fst) (Expr.ret (rs := [Ty.bool]) (Arg.imm false, ()))
             (Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ugt i32 Ty.bool (by decide),
                          args := (Arg.var ld_7, Arg.var mv, ()) } fun p_70 =>
              Expr.jnz (Arg.var p_70.fst) (Expr.ret (rs := [Ty.bool]) (Arg.imm false, ()))
               (fidScrPtr pScr o_kl fun p_73 =>
                Expr.store (t := i32) (Arg.var uip) (Arg.var p_73)
                 (Expr.group (sig := [[i32, i32, i32]]) (fun Js => Blocks.cons (fun p_74 =>
                   Expr.let_ { sig := [i32, i32],
                               code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                               args := (Arg.var p_74.snd.snd.fst, Arg.var ld_7, ()) } fun p_75 =>
                   Expr.jnz (Arg.var p_75.fst)
                    (fidScrOffPtr pScr o_kl p_74.snd.snd.fst fun p =>
                     Expr.load i32 (Arg.var p) fun ld_8 =>
                     Expr.let_ { sig := [i32, i32], code := OpCode.lshr i32,
                                 args := (Arg.var ld_8, Arg.imm 1, ()) } fun p =>
                     Expr.group (sig := [[i32, i32]]) (fun _ => Blocks.cons (fun p =>
                      Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                  args := (Arg.var p_74.snd.snd.fst, Arg.imm 1, ()) } fun p_76 =>
                      Expr.jump Js.fst (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p_76.fst, ()))
                      Blocks.nil) fun Js =>
                     Expr.let_ { sig := [i32, i32],
                                 code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                                 args := (Arg.var p.fst, Arg.var nv, ()) } fun p_76 =>
                     Expr.jnz (Arg.var p_76.fst)
                      (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                   args := (Arg.imm 4224, Arg.var p.fst, ()) } fun p =>
                       fidScrPtr pScr p.fst fun p => Expr.load i32 (Arg.var p) fun ld =>
                       Expr.group (sig := [[i32, i32]]) (fun _ => Blocks.cons (fun p =>
                        Expr.jump Js.fst (Arg.var p.fst, Arg.var p.snd.fst, ())) Blocks.nil)
                        fun Js =>
                       Expr.let_ { sig := [i32, i32],
                                   code := OpCode.cmp CmpOp.ugt i32 Ty.bool (by decide),
                                   args := (Arg.var ld, Arg.var p_74.fst, ()) } fun p =>
                       Expr.jnz (Arg.var p.fst)
                        (Expr.jump Js.fst (Arg.var ld, Arg.var p_74.snd.snd.fst, ()))
                        (Expr.jump Js.fst (Arg.var p_74.fst, Arg.var p_74.snd.fst, ())))
                      (Expr.jump Js.fst (Arg.var p_74.fst, Arg.var p_74.snd.fst, ())))
                    (Expr.group (sig := [[]]) (fun Js => Blocks.cons (fun _ =>
                      Expr.call (as := [i64, i32]) (bs := []) "full_k6_backtrack_fid"
                       (Arg.var cHdr, Arg.var p_74.fst, PUnit.unit) fun _ =>
                      Expr.group (sig := [[i32]]) (fun Js => Blocks.cons (fun p_78 =>
                       Expr.let_ { sig := [i32, i32],
                                   code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                                   args := (Arg.var p_78.fst, Arg.var p_56.fst, ()) } fun p_79 =>
                       Expr.jnz (Arg.var p_79.fst)
                        (fidScrOffPtr pScr o_bump p_78.fst fun p_83 =>
                         Expr.load i32 (Arg.var p_83) fun ld =>
                         Expr.call (as := [i64, i32]) (bs := []) "full_k6_mtf_fid"
                          (Arg.var cHdr, Arg.var ld, PUnit.unit) fun _ =>
                         Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                     args := (Arg.var p_78.fst, Arg.imm 1, ()) } fun p =>
                         Expr.jump Js.fst (Arg.var p.fst, ()))
                        (fidScrImmPtr pScr 4193 fun p_82 =>
                         Expr.load i32 (Arg.var p_82) fun ld_8 =>
                         fidScrImmPtr pScr 4206 fun p_85 =>
                         Expr.load i32 (Arg.var p_85) fun ld_9 =>
                         Expr.let_ { sig := [i32, i32],
                                     code := OpCode.cmp CmpOp.uge i32 Ty.bool (by decide),
                                     args := (Arg.var ld_8, Arg.var o_mv4, ()) } fun p_86 =>
                         Expr.jnz (Arg.var p_86.fst)
                          (Expr.ret (rs := [Ty.bool]) (Arg.imm false, ()))
                          (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                       args := (Arg.var ld_9, Arg.var ld_7, ()) } fun p_87 =>
                           Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                       args := (Arg.var p_87.fst, Arg.var ld_6, ()) } fun p_88 =>
                           fidScrImmPtr pScr 4207 fun p_91 =>
                           Expr.load i32 (Arg.var p_91) fun ld_10 =>
                           Expr.let_ { sig := [i32, i32],
                                       code := OpCode.cmp CmpOp.ugt i32 Ty.bool (by decide),
                                       args := (Arg.var p_88.fst, Arg.var ld_10, ()) } fun p_92 =>
                           Expr.jnz (Arg.var p_92.fst)
                            (Expr.ret (rs := [Ty.bool]) (Arg.imm false, ()))
                            (fidAnaCommitExpr pScr cHdr mv ld_6 ld_7 ld_8 ld_9 uip)))) Blocks.nil)
                       fun Js => Expr.jump Js.fst (Arg.imm 0, ())) Blocks.nil) fun Js =>
                     Expr.let_ { sig := [i32, i32],
                                 code := OpCode.cmp CmpOp.uge i32 Ty.bool (by decide),
                                 args := (Arg.var ld_7, Arg.imm 2, ()) } fun p =>
                     Expr.jnz (Arg.var p.fst)
                      (Expr.let_ { sig := [i32, i32],
                                   code := OpCode.cmp CmpOp.ne i32 Ty.bool (by decide),
                                   args := (Arg.var p_74.snd.fst, Arg.imm 1, ()) } fun p =>
                       Expr.jnz (Arg.var p.fst)
                        (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                     args := (Arg.var o_kl, Arg.imm 1, ()) } fun p =>
                         fidScrPtr pScr p.fst fun p => Expr.load i32 (Arg.var p) fun ld_8 =>
                         Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                     args := (Arg.var o_kl, Arg.imm 1, ()) } fun p =>
                         fidScrPtr pScr p.fst fun p =>
                         fidScrOffPtr pScr o_kl p_74.snd.fst fun p_79 =>
                         Expr.load i32 (Arg.var p_79) fun ld_9 =>
                         Expr.store (Arg.var ld_9) (Arg.var p)
                          (fidScrOffPtr pScr o_kl p_74.snd.fst fun p =>
                           Expr.store (Arg.var ld_8) (Arg.var p) (Expr.jump Js.fst ())))
                        (Expr.jump Js.fst ()))
                      (Expr.jump Js.fst ()))) Blocks.nil) fun Js =>
                 Expr.jump Js.fst (Arg.imm 0, Arg.imm 1, Arg.imm 1, ())))))))))
    Blocks.nil) fun Js => Expr.jump Js.fst (Arg.imm 0, ())) Blocks.nil) fun Js =>
  Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ugt i32 Ty.bool (by decide),
              args := (Arg.var ld_5, Arg.var mv, ()) } fun p =>
  Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.var mv, ()))
    (Expr.jump Js.fst (Arg.var ld_5, ()))

private theorem fidAna_post_res_wp (Γ : Env) (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (Q : Post [Ty.bool]) (X : XPost) (scr0 scr_in : List (BitVec 32))
    (nv uip : BitVec 32) (m_in : Mem 64)
    (hBt : Γ.Has "full_k6_backtrack_fid" fidK6BacktrackSpec)
    (hMtf : Γ.Has "full_k6_mtf_fid" fidK6MtfSpec)
    (hWatch : Γ.Has "full_k6_watch_fid" fidK6WatchSpec)
    (hAssign : Γ.Has "full_k6_assign_fid" fidK6AssignSpec)
    (hlen : FullState.LengthsOk c s) (hok : FidK6BufOk scr0)
    (hscr_len : scr0.length = c.scratch_cap) (h4214 : 4214 < scr0.length) :
    let mv := scr0[4214]'h4214
    nv.toNat ≤ mv.toNat → FidAnaInv scr0 mv.toNat scr_in → (FullMem c (m8ScrSt s scr_in) ⋆ R) m_in →
    (∀ (ok : Bool) (scrb : List (BitVec 32)) (mb : Mem 64),
      FidK6BufOk scrb → FidAnaPost scr0 mv.toNat scrb →
      (FullMem c (m8ScrSt s scrb) ⋆ R) mb → Q (ok, ()) mb) →
    wp Γ Q X (fidAnaPostResExpr c.pScratchBuf c.hdr mv nv uip) m_in := by
  intro mv hnv_le hkin hm_in hQret
  have hmv_eq : scr0[4214]?.getD 0#32 = mv := m8_k6_get_eq h4214
  have hmv_lo : 256 ≤ mv.toNat := by have := hok.mv_lo; rw [hmv_eq] at this; exact this
  have hmv_hi : mv.toNat ≤ 8192 := by have := hok.mv_hi; rw [hmv_eq] at this; exact this
  have hcap_lt : scr0.length < 2 ^ 30 := hok.length_lt
  have hlen_scr : 4224 + 45 * mv.toNat ≤ scr0.length := by
    have := hok.length_ge; rw [hmv_eq] at this; omega
  have hlin : scr_in.length = scr0.length := hkin.1
  have h4208_lt : 4208 < scr_in.length := by omega
  let nana_raw := scr_in[4208]'h4208_lt
  dsimp only [fidAnaPostResExpr, fidScrPtr, fidScrOffPtr, fidScrImmPtr]
  c0_hstraight
  refine wp_join_state1 (fun x : Val i32 => x)
    (fun nana m => nana.toNat ≤ mv.toNat ∧ m = m_in) ?_ ?_
  · rintro J nana m ⟨hnana_le, rfl⟩
    refine wp_loop_group (ts := [i32])
      (fun rem (j, ()) ma => ∃ scra, FidAnaInv scr0 mv.toNat scra ∧ j.toNat ≤ nana.toNat ∧
        rem = nana.toNat - j.toNat ∧ (FullMem c (m8ScrSt s scra) ⋆ R) ma) ?_ ?_
    · rintro L1 rem1 ⟨j, ⟨⟩⟩ ma hL1 ⟨scra, hka, hj_le, rfl, hma⟩
      have hla : scra.length = scr0.length := hka.1
      c0_hstraight; c0_hsplit
      · have hj_lt : j.toNat < nana.toNat := hc
        have hj1 : (j + 1#32).toNat = j.toNat + 1 := m8_bv32_add1_toNat hj_lt (by omega)
        have hbp_e : ((4224 + 7 * mv + j).setWidth 64).toNat = 4224 + 7 * mv.toNat + j.toNat :=
          fid_k6_off_add (mv := mv) (k := 7) (x := j) hmv_hi (by decide) (by omega)
        have hbp_lt : ((4224 + 7 * mv + j).setWidth 64).toNat < scra.length := by
          rw [hla, hbp_e]; omega
        let v := scra[((4224 + 7 * mv + j).setWidth 64).toNat]'hbp_lt
        c0_hstraight
        refine wp_join0 (fun mb => ∃ scrb, FidAnaInv scr0 mv.toNat scrb ∧
          (FullMem c (m8ScrSt s scrb) ⋆ R) mb) ?_ ?_
        · rintro _ mb ⟨scrb, hkb, hmb⟩
          c0_hsteps!
          exact hL1 (nana.toNat - (j + 1#32).toNat) (j + 1#32, ()) _ (by omega)
            ⟨scrb, hkb, by omega, rfl, hmb⟩
        · intro J2 hJ2; c0_hstraight; c0_hsplit
          · have hbp_idx : (4224 + 7 * mv.toNat + j.toNat) % 2 ^ 32 =
                ((4224 + 7 * mv + j).setWidth 64).toNat := by
              rw [hbp_e]; omega
            have hv_lt : v.toNat < nv.toNat := by
              change scra[(4224 + 7 * mv.toNat + j.toNat) % 2 ^ 32].toNat < nv.toNat at hc
              rwa [fidAna_get_congr _ hbp_lt hbp_idx] at hc
            have hsn_e : ((4224 + 6 * mv + v).setWidth 64).toNat =
                4224 + 6 * mv.toNat + v.toNat :=
              fid_k6_off_add (mv := mv) (k := 6) (x := v) hmv_hi (by decide) (by omega)
            have hsn_lt : ((4224 + 6 * mv + v).setWidth 64).toNat < scra.length := by
              rw [hla, hsn_e]; omega
            c0_hsteps!
            let scrb := scra.set ((4224 + 6 * mv + v).setWidth 64).toNat
              ((scra[((4224 + 6 * mv + v).setWidth 64).toNat]'hsn_lt) &&& ~~~2#32)
            have hkb : FidAnaInv scr0 mv.toNat scrb :=
              fidAnaInv_set hka _ (Or.inr (Or.inr (by rw [hsn_e]; omega)))
            exact hJ2 _ ⟨scrb, hkb, hm⟩
          · c0_hsteps!; exact hJ2 ma ⟨scra, hka, hma⟩
      · have h4210_lt : 4210 < scra.length := by omega
        have h4209_lt : 4209 < scra.length := by omega
        let nres := scra[4210]'h4210_lt; let nkl := scra[4209]'h4209_lt
        c0_hstraight
        obtain ⟨hpost_a, hbuf_a⟩ := fidAnaInv_to_post_ok hok h4214 hmv_eq hmv_hi hka
        c0_hsplit
        · c0_hsteps!; exact hQret false scra ma hbuf_a hpost_a hma
        · c0_hstraight; c0_hsplit
          · c0_hsteps!; exact hQret false scra ma hbuf_a hpost_a hma
          · c0_hstraight; c0_hsplit
            · c0_hsteps!; exact hQret false scra ma hbuf_a hpost_a hma
            · have hnres_hi : nres.toNat ≤ 2 * mv.toNat := by
                have hc' : scra[OfNat.ofNat 4210].toNat ≤ (mv.toNat * 2 ^ 1) % 2 ^ 32 :=
                  Nat.not_lt.mp hc
                change nres.toNat ≤ _ at hc'
                have h2 : (mv.toNat * 2 ^ 1) % 2 ^ 32 = 2 * mv.toNat := by omega
                omega
              c0_hstraight; c0_hsplit
              · c0_hsteps!; exact hQret false scra ma hbuf_a hpost_a hma
              · have hnkl_lo : 1 ≤ nkl.toNat := by
                  have hc' : nkl ≠ 0#32 := hc
                  exact Nat.pos_of_ne_zero
                    (fun h0 => hc' (BitVec.eq_of_toNat_eq (by simpa using h0)))
                c0_hstraight; c0_hsplit
                · c0_hsteps!; exact hQret false scra ma hbuf_a hpost_a hma
                · have hnkl_hi : nkl.toNat ≤ mv.toNat := by
                    change ¬mv.toNat < nkl.toNat at hc; omega
                  have hkl0_e : ((4224 + 8 * mv).setWidth 64).toNat = 4224 + 8 * mv.toNat := by
                    have h := fid_k6_off_add (mv := mv) (k := 8) (x := 0#32) hmv_hi
                      (by decide) (by decide)
                    rw [BitVec.add_zero] at h; simpa using h
                  have hkl0_lt : ((4224 + 8 * mv).setWidth 64).toNat < scra.length := by
                    rw [hla, hkl0_e]; omega
                  c0_hstraight
                  let scrb0 := scra.set ((4224 + 8 * mv).setWidth 64).toNat uip
                  have hkb : FidAnaInv scr0 mv.toNat scrb0 := fidAnaInv_set hka uip
                    (Or.inr (Or.inr (by rw [hkl0_e]; change 4224 + 6 * mv.toNat ≤ _ ∧ _; omega)))
                  refine wp_loop_group (ts := [i32, i32, i32])
                    (fun rem (_, wi, r_j, ()) mb =>
                      1 ≤ r_j.toNat ∧ r_j.toNat ≤ nkl.toNat ∧ 1 ≤ wi.toNat ∧
                        (2 ≤ nkl.toNat → wi.toNat < nkl.toNat) ∧ rem = nkl.toNat - r_j.toNat ∧
                        (FullMem c (m8ScrSt s scrb0) ⋆ R) mb)
                    ?_ ?_
                  · rintro L2 rem2 ⟨jlvl, wi, r_j, ⟨⟩⟩ mb hL2
                      ⟨hr_lo, hr_le, hwi_lo, hwi_hi, rfl, hmb⟩
                    c0_hstraight; c0_hsplit
                    · have hr_lt : r_j.toNat < nkl.toNat := hc
                      have hr1 : (r_j + 1#32).toNat = r_j.toNat + 1 :=
                        m8_bv32_add1_toNat hr_lt (by omega)
                      have hklr_e : ((4224 + 8 * mv + r_j).setWidth 64).toNat =
                          4224 + 8 * mv.toNat + r_j.toNat :=
                        fid_k6_off_add (mv := mv) (k := 8) (x := r_j) hmv_hi (by decide) (by omega)
                      have hklr_lt : ((4224 + 8 * mv + r_j).setWidth 64).toNat <
                          scrb0.length := by simp only [scrb0, List.length_set, hla, hklr_e]; omega
                      let lit := scrb0[((4224 + 8 * mv + r_j).setWidth 64).toNat]'hklr_lt
                      c0_hstraight
                      refine wp_join_state_pure (ts := [i32, i32])
                        (fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
                        (fun st => 1 ≤ st.2.toNat ∧ (2 ≤ nkl.toNat → st.2.toNat < nkl.toNat))
                        ?_ ?_
                      · rintro _ ⟨jlvl', wi'⟩ ⟨hwi'_lo, hwi'_hi⟩
                        c0_hsteps!
                        exact hL2 (nkl.toNat - (r_j + 1#32).toNat)
                          (jlvl', wi', r_j + 1#32, ()) mb (by omega)
                          ⟨by omega, by omega, hwi'_lo, hwi'_hi, rfl, hmb⟩
                      · intro J3 hJ3; c0_hstraight; c0_hsplit
                        · have hklr_idx : (4224 + 8 * mv.toNat + r_j.toNat) % 2 ^ 32 =
                              ((4224 + 8 * mv + r_j).setWidth 64).toNat := by
                            rw [hklr_e]; omega
                          have hv_lt : lit.toNat / 2 < nv.toNat := by
                            change scrb0[(4224 + 8 * mv.toNat + r_j.toNat) % 2 ^ 32].toNat / 2 <
                              nv.toNat at hc
                            rwa [fidAna_get_congr _ hklr_lt hklr_idx] at hc
                          have hsh : (lit >>> 1).toNat = lit.toNat / 2 := by
                            simp [Nat.shiftRight_eq_div_pow]
                          have h4v_lt : ((4224 + (lit >>> 1)).setWidth 64).toNat <
                              scrb0.length := by
                            have hv0 : ((4224 + (lit >>> 1)).setWidth 64).toNat =
                                4224 + (lit >>> 1).toNat := by
                              have h := fid_k6_off_add (mv := mv) (k := 0) (x := lit >>> 1) hmv_hi
                                (by decide) (by rw [hsh]; omega)
                              simp only [Nat.zero_mul, BitVec.ofNat_eq_ofNat, BitVec.zero_mul,
                                BitVec.add_zero] at h
                              simpa using h
                            simp only [scrb0, List.length_set, hla, hv0, hsh]; omega
                          c0_hstraight
                          refine wp_join_state_pure (ts := [i32, i32])
                            (fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
                            (fun st => 1 ≤ st.2.toNat ∧ (2 ≤ nkl.toNat → st.2.toNat < nkl.toNat))
                            ?_ ?_
                          · rintro _ ⟨jlvl', wi'⟩ hst'; c0_hsteps!; exact hJ3 (jlvl', wi') hst'
                          · intro J4 hJ4; c0_hstraight; c0_hsplit
                            · c0_hsteps!; exact hJ4 (_, r_j) ⟨hr_lo, fun _ => hr_lt⟩
                            · c0_hsteps!; exact hJ4 (jlvl, wi) ⟨hwi_lo, hwi_hi⟩
                        · c0_hsteps!; exact hJ3 (jlvl, wi) ⟨hwi_lo, hwi_hi⟩
                    · have hkb_len : scrb0.length = scr0.length := hkb.1
                      refine wp_join0 (fun mc => ∃ scrc, FidAnaInv scr0 mv.toNat scrc ∧
                        (FullMem c (m8ScrSt s scrc) ⋆ R) mc) ?_ ?_
                      · rintro _ mc ⟨scrc, hkc, hmc⟩
                        refine fidAna_call_backtrack hBt hlen hok hscr_len h4214
                          hmv_eq hmv_hi hkc hmc ?_
                        intro scrd md hkd hmd
                        refine wp_loop_group (ts := [i32])
                          (fun rem (i, ()) me => ∃ scre, FidAnaInv scr0 mv.toNat scre ∧
                            i.toNat ≤ nana.toNat ∧ rem = nana.toNat - i.toNat ∧
                            (FullMem c (m8ScrSt s scre) ⋆ R) me) ?_ ?_
                        · rintro L3 rem3 ⟨i, ⟨⟩⟩ me hL3 ⟨scre, hke, hi_le, rfl, hme⟩
                          have hle : scre.length = scr0.length := hke.1
                          c0_hstraight; c0_hsplit
                          · have hi_lt : i.toNat < nana.toNat := hc
                            have hi1 : (i + 1#32).toNat = i.toNat + 1 :=
                              m8_bv32_add1_toNat hi_lt (by omega)
                            have hbp_e : ((4224 + 7 * mv + i).setWidth 64).toNat =
                                4224 + 7 * mv.toNat + i.toNat :=
                              fid_k6_off_add (mv := mv) (k := 7) (x := i) hmv_hi (by decide)
                                (by omega)
                            have hbp_lt : ((4224 + 7 * mv + i).setWidth 64).toNat <
                                scre.length := by rw [hle, hbp_e]; omega
                            c0_hsteps!
                            refine fidAna_call_mtf hMtf hlen hok hscr_len h4214
                              hmv_eq hmv_hi hke hme ?_
                            intro scrf mf hkf hmf
                            c0_hsteps!
                            exact hL3 (nana.toNat - (i + 1#32).toNat) (i + 1#32, ()) _ (by omega)
                              ⟨scrf, hkf, by omega, rfl, hmf⟩
                          · have h4193_lt : 4193 < scre.length := by omega
                            have h4206_lt : 4206 < scre.length := by omega
                            have h4207_lt : 4207 < scre.length := by omega
                            let nc := scre[4193]'h4193_lt
                            let alen := scre[4206]'h4206_lt
                            let acap := scre[4207]'h4207_lt
                            c0_hstraight
                            obtain ⟨hpost_e, hbuf_e⟩ :=
                              fidAnaInv_to_post_ok hok h4214 hmv_eq hmv_hi hke
                            c0_hsplit
                            · c0_hsteps!; exact hQret false scre me hbuf_e hpost_e hme
                            · c0_hstraight
                              have hnc_lt : nc.toNat < 4 * mv.toNat := by
                                have hc' : scre[OfNat.ofNat 4193].toNat <
                                    (mv.toNat * 2 ^ 2) % 2 ^ 32 := Nat.lt_of_not_ge hc
                                change nc.toNat < _ at hc'
                                have h4 : (mv.toNat * 2 ^ 2) % 2 ^ 32 = 4 * mv.toNat := by omega
                                omega
                              have h4206_e : alen = scre[4206]?.getD 0#32 := by
                                simp only [alen, List.getElem?_eq_getElem h4206_lt,
                                  Option.getD_some]
                              have h4207_e : acap = scre[4207]?.getD 0#32 := by
                                simp only [acap, List.getElem?_eq_getElem h4207_lt,
                                  Option.getD_some]
                              have halen_acap : alen.toNat ≤ acap.toNat := by
                                have := hbuf_e.alen_le; rwa [← h4206_e, ← h4207_e] at this
                              have hacap_lt : acap.toNat + 4224 + 45 * mv.toNat ≤ scr0.length := by
                                have h1 := hok.length_ge
                                rw [hmv_eq, ← hke.2.2.2.1 4207 (by omega) (by omega), ← h4207_e]
                                  at h1
                                omega
                              have hal_sum : ((alen + nkl) + nres).toNat =
                                  alen.toNat + nkl.toNat + nres.toNat := by
                                rw [BitVec.toNat_add, BitVec.toNat_add]
                                have hs1 : alen.toNat + nkl.toNat < 2 ^ 32 := by omega
                                rw [Nat.mod_eq_of_lt hs1, Nat.mod_eq_of_lt (by omega)]
                              c0_hsplit
                              · c0_hsteps!; exact hQret false scre me hbuf_e hpost_e hme
                              · have halen_le : alen.toNat + nkl.toNat + nres.toNat ≤
                                    acap.toNat := by
                                  change ¬ acap.toNat <
                                    (alen.toNat + nkl.toNat + nres.toNat) % 2 ^ 32 at hc
                                  rw [Nat.mod_eq_of_lt (by omega)] at hc
                                  exact Nat.not_lt.mp hc
                                have hnc_eq : scr0[4193]? = some nc := by
                                  rw [← hke.2.1 4193 (by omega)]
                                  exact List.getElem?_eq_getElem h4193_lt
                                have hac_eq : scr0[4207]? = some acap := by
                                  rw [← hke.2.2.2.1 4207 (by omega) (by omega)]
                                  exact List.getElem?_eq_getElem h4207_lt
                                have hac_ge : scr0[4207]'(by have := hok.base_ge; omega) =
                                    acap := Option.some.inj
                                  (by rw [← List.getElem?_eq_getElem, hac_eq])
                                have hac_eq0 : scr0[4207]? =
                                    some (scr0[4207]'(by have := hok.base_ge; omega)) :=
                                  List.getElem?_eq_getElem _
                                rw [← hac_ge] at hacap_lt halen_le
                                have hacap_lt' :
                                    4224 + 45 * (scr0[4214]'h4214).toNat +
                                      (scr0[4207]'(by have := hok.base_ge; omega)).toNat ≤
                                    scr0.length := by
                                  change 4224 + 45 * mv.toNat + _ ≤ scr0.length; omega
                                exact fidAna_commit_wp Γ c s R Q X scr0 scre nres nkl nc alen uip
                                  me hWatch hAssign hlen hok hscr_len h4214 hmv_lo hmv_hi
                                  hacap_lt' hcap_lt hnc_eq hac_eq0 hnc_lt hnkl_lo hnkl_hi
                                  hnres_hi halen_le hke hme hQret
                        · intro L3 hL3; c0_hsteps!
                          exact hL3 nana.toNat (0#32, ()) md ⟨scrd, hkd, by simp, rfl, hmd⟩
                      · intro J4 hJ4; c0_hstraight; c0_hsplit
                        · have h2_nkl : 2 ≤ nkl.toNat := by
                            change (BitVec.toNat 2) ≤ nkl.toNat at hc; simpa using hc
                          have hwi_lt : wi.toNat < nkl.toNat := hwi_hi h2_nkl
                          c0_hstraight; c0_hsplit
                          · have hl1_e : ((4224 + 8 * mv + 1#32).setWidth 64).toNat =
                                4224 + 8 * mv.toNat + 1 := by
                              have h := fid_k6_off_add (mv := mv) (k := 8) (x := 1#32) hmv_hi
                                (by decide) (by decide)
                              simpa using h
                            have hlw_e : ((4224 + 8 * mv + wi).setWidth 64).toNat =
                                4224 + 8 * mv.toNat + wi.toNat :=
                              fid_k6_off_add (mv := mv) (k := 8) (x := wi) hmv_hi (by decide)
                                (by omega)
                            have hl1_lt : ((4224 + 8 * mv + 1#32).setWidth 64).toNat <
                                scrb0.length := by
                              simp only [scrb0, List.length_set, hla, hl1_e]; omega
                            have hlw_lt : ((4224 + 8 * mv + wi).setWidth 64).toNat <
                                scrb0.length := by
                              simp only [scrb0, List.length_set, hla, hlw_e]; omega
                            let v_w := scrb0[((4224 + 8 * mv + wi).setWidth 64).toNat]'hlw_lt
                            let v_1 := scrb0[((4224 + 8 * mv + 1#32).setWidth 64).toNat]'hl1_lt
                            have hlw_lt2 : ((4224 + 8 * mv + wi).setWidth 64).toNat <
                                (scrb0.set ((4224 + 8 * mv + 1#32).setWidth 64).toNat
                                  v_w).length := by
                              simp only [scrb0, List.length_set, hla, hlw_e]; omega
                            c0_hsteps!
                            let scrb1 :=
                              scrb0.set ((4224 + 8 * mv + 1#32).setWidth 64).toNat v_w
                            let scrb2 :=
                              scrb1.set ((4224 + 8 * mv + wi).setWidth 64).toNat v_1
                            have hkb1 : FidAnaInv scr0 mv.toNat scrb1 :=
                              fidAnaInv_set hkb _ (Or.inr (Or.inr (by rw [hl1_e]; omega)))
                            have hkb2 : FidAnaInv scr0 mv.toNat scrb2 :=
                              fidAnaInv_set hkb1 _ (Or.inr (Or.inr (by rw [hlw_e]; omega)))
                            exact hJ4 _ ⟨scrb2, hkb2, hm⟩
                          · c0_hsteps!; exact hJ4 _ ⟨scrb0, hkb, hmb⟩
                        · c0_hsteps!; exact hJ4 _ ⟨scrb0, hkb, hmb⟩
                  · intro L2 hL2; c0_hsteps!
                    exact hL2 (nkl.toNat - 1) (0#32, 1#32, 1#32, ()) _
                      ⟨by simp, hnkl_lo, by simp, fun h2 => by change 1 < nkl.toNat; omega,
                       by simp, hm⟩
    · intro L1 hL1
      c0_hsteps!; exact hL1 nana.toNat (0#32, ()) m ⟨scr_in, hkin, by simp, rfl, hm_in⟩
  · intro J hJ; c0_hstraight; c0_hsplit
    · c0_hsteps!; exact hJ mv m_in ⟨Nat.le_refl _, rfl⟩
    · have hc' : nana_raw.toNat ≤ mv.toNat := by change ¬mv.toNat < nana_raw.toNat at hc; omega
      c0_hsteps!; exact hJ nana_raw m_in ⟨hc', rfl⟩

/-! ## 4. Main `full_k6_analyze_fid_wp` -/

private theorem fidAna_sub1_toNat {i : BitVec 32} (hi : i ≠ 0#32) :
    (i - 1#32).toNat = i.toNat - 1 := by
  have hne : i.toNat ≠ 0 := fun h0 => hi (BitVec.eq_of_toNat_eq (by simpa using h0))
  have h1 : 1 ≤ i.toNat := Nat.pos_of_ne_zero hne
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by simpa using h1))]; simp

theorem full_k6_analyze_fid_wp (Γ : Env)
    (hAnaCl : Γ.Has "full_k6_ana_cl_fid" fidK6AnaClSpec)
    (hBt : Γ.Has "full_k6_backtrack_fid" fidK6BacktrackSpec)
    (hMtf : Γ.Has "full_k6_mtf_fid" fidK6MtfSpec)
    (hWatch : Γ.Has "full_k6_watch_fid" fidK6WatchSpec)
    (hAssign : Γ.Has "full_k6_assign_fid" fidK6AssignSpec) :
    ∀ (a : Tup Val [i64, i32]) (m : Mem 64) (Q : Post [Ty.bool]) (X : XPost),
      fidK6AnalyzeSpec a m Q X → Func.wp Γ full_k6_analyze_fid_body a m Q X := by
  rintro ⟨h, confl_cid, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hok, hm, hK⟩
  change (FullMem c (m8ScrSt s s.scratch.scratch_buf) ⋆ R) m at hm
  dsimp only [Func.wp, full_k6_analyze_fid_body]
  have hscr_len : s.scratch.scratch_buf.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have h4214 : 4214 < s.scratch.scratch_buf.length := by have := hok.base_ge; omega
  have h4192 : 4192 < s.scratch.scratch_buf.length := by omega
  have hmv_eq : s.scratch.scratch_buf[4214]?.getD 0#32 = s.scratch.scratch_buf[4214]'h4214 :=
    m8_k6_get_eq h4214
  have hmv_lo : 256 ≤ (s.scratch.scratch_buf[4214]'h4214).toNat := by
    have := hok.mv_lo; rwa [hmv_eq] at this
  have hmv_hi : (s.scratch.scratch_buf[4214]'h4214).toNat ≤ 8192 := by
    have := hok.mv_hi; rwa [hmv_eq] at this
  have hlen_scr : 4224 + 45 * (s.scratch.scratch_buf[4214]'h4214).toNat ≤
      s.scratch.scratch_buf.length := by
    have := hok.length_ge; rw [hmv_eq] at this; omega
  c0_hstraight; c0_hsplit
  · exfalso; change (s.scratch.scratch_buf[4214]'h4214).toNat < 256 at hc; omega
  · c0_hstraight; c0_hsplit
    · exfalso; change 8192 < (s.scratch.scratch_buf[4214]'h4214).toNat at hc; omega
    · c0_hstraight; c0_hsplit
      · have hk0 := fidAnaInv_refl s.scratch.scratch_buf (s.scratch.scratch_buf[4214]'h4214).toNat
        obtain ⟨hp0, _⟩ := fidAnaInv_to_post_ok hok h4214 hmv_eq hmv_hi hk0
        rw [← hmv_eq] at hp0
        c0_hsteps!
        exact hK false _ m hok hscr_len hp0.2.1 hp0.2.2.1 hp0.2.2.2.1 hp0.2.2.2.2.1
          hp0.2.2.2.2.2.1 hp0.2.2.2.2.2.2.1 hp0.2.2.2.2.2.2.2.1 hp0.2.2.2.2.2.2.2.2.1
          hp0.2.2.2.2.2.2.2.2.2.1 hp0.2.2.2.2.2.2.2.2.2.2.1 hp0.2.2.2.2.2.2.2.2.2.2.2.1
          hp0.2.2.2.2.2.2.2.2.2.2.2.2.1 hp0.2.2.2.2.2.2.2.2.2.2.2.2.2 hm
      · have hnv_le : (s.scratch.scratch_buf[4192]'h4192).toNat ≤
            (s.scratch.scratch_buf[4214]'h4214).toNat := by
          change ¬(s.scratch.scratch_buf[4214]'h4214).toNat <
            (s.scratch.scratch_buf[4192]'h4192).toNat at hc; omega
        have h4209_lt : 4209 < s.scratch.scratch_buf.length := by omega
        have h4208_lt : 4208 < (s.scratch.scratch_buf.set 4209 1#32).length := by simp; omega
        have h4210_lt : 4210 < ((s.scratch.scratch_buf.set 4209 1#32).set 4208 0#32).length := by
          simp; omega
        have h4212_lt : 4212 < (((s.scratch.scratch_buf.set 4209 1#32).set 4208 0#32).set 4210
            0#32).length := by simp; omega
        c0_hstraight
        let scr1 := s.scratch.scratch_buf.set 4209 1#32
        let scr2 := scr1.set 4208 0#32; let scr3 := scr2.set 4210 0#32
        let scr4 := scr3.set 4212 0#32
        have hk1 : FidAnaInv s.scratch.scratch_buf (s.scratch.scratch_buf[4214]'h4214).toNat scr4 :=
          fidAnaInv_set (fidAnaInv_set (fidAnaInv_set (fidAnaInv_set
            (fidAnaInv_refl _ _) 1#32 (Or.inl ⟨by omega, by omega⟩))
            0#32 (Or.inl ⟨by omega, by omega⟩)) 0#32 (Or.inl ⟨by omega, by omega⟩))
            0#32 (Or.inr (Or.inl rfl))
        refine fidAna_call_ana_cl hAnaCl hlen hok hscr_len h4214 hmv_eq hmv_hi hk1 hm ?_
        intro scra ma hka hma
        have hla : scra.length = s.scratch.scratch_buf.length := hka.1
        have h4195_lt : 4195 < scra.length := by omega
        have h4197_lt : 4197 < scra.length := by omega
        let trail_end := scra[4197]'h4197_lt
        c0_hstraight
        refine wp_join_state1 (fun x : Val i32 => x)
          (fun max_b mb => max_b.toNat ≤ (s.scratch.scratch_buf[4214]'h4214).toNat ∧ mb = ma)
          ?_ ?_
        · rintro J0 max_b ma ⟨hmax_le, rfl⟩
          refine wp_join_state (ts := [i32, i32])
            (fun st : BitVec 32 × BitVec 32 × List (BitVec 32) => (st.1, st.2.1, ()))
            (fun st mc => FidAnaInv s.scratch.scratch_buf
              (s.scratch.scratch_buf[4214]'h4214).toNat st.2.2 ∧
              (FullMem c (m8ScrSt s st.2.2) ⋆ R) mc) ?_ ?_
          · rintro _ ⟨d, uip, scrc⟩ mc ⟨hkc, hmc⟩
            dsimp only [Blocks.get]
            change wp Γ Q X (fidAnaPostResExpr c.pScratchBuf c.hdr _ _ uip) mc
            exact fidAna_post_res_wp Γ c s R Q X s.scratch.scratch_buf scrc _ uip mc
              hBt hMtf hWatch hAssign hlen hok hscr_len h4214 hnv_le hkc hmc
              (fun ok scrd md hokd hpd hmd => by
                rw [← hmv_eq] at hpd
                exact hK ok scrd md hokd (hpd.1.trans hscr_len) hpd.2.1 hpd.2.2.1
                  hpd.2.2.2.1 hpd.2.2.2.2.1 hpd.2.2.2.2.2.1 hpd.2.2.2.2.2.2.1
                  hpd.2.2.2.2.2.2.2.1 hpd.2.2.2.2.2.2.2.2.1 hpd.2.2.2.2.2.2.2.2.2.1
                  hpd.2.2.2.2.2.2.2.2.2.2.1 hpd.2.2.2.2.2.2.2.2.2.2.2.1
                  hpd.2.2.2.2.2.2.2.2.2.2.2.2.1 hpd.2.2.2.2.2.2.2.2.2.2.2.2.2 hmd)
          · intro J hJ
            refine wp_loop_group (ts := [i32])
              (fun rem (i, ()) mc => ∃ scrc,
                FidAnaInv s.scratch.scratch_buf (s.scratch.scratch_buf[4214]'h4214).toNat scrc ∧
                i.toNat ≤ (s.scratch.scratch_buf[4214]'h4214).toNat ∧ rem = i.toNat ∧
                (FullMem c (m8ScrSt s scrc) ⋆ R) mc) ?_ ?_
            · rintro L1 rem1 ⟨i, ⟨⟩⟩ mc hL1 ⟨scrc, hkc, hi_le, rfl, hmc⟩
              have hlc : scrc.length = s.scratch.scratch_buf.length := hkc.1
              have h4212_ltc : 4212 < scrc.length := by omega
              c0_hstraight; c0_hsplit
              · c0_hstraight; c0_hsplit
                · c0_hsteps!; exact hJ (i, 4294967295#32, scrc) mc ⟨hkc, hmc⟩
                · have hi1 : (i - 1#32).toNat = i.toNat - 1 := fidAna_sub1_toNat hc
                  have hi_pos : 1 ≤ i.toNat :=
                    Nat.pos_of_ne_zero (fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0)))
                  have hana_e : ((4224 + 5 * (s.scratch.scratch_buf[4214]'h4214) +
                        (i - 1#32)).setWidth 64).toNat =
                      4224 + 5 * (s.scratch.scratch_buf[4214]'h4214).toNat + (i - 1#32).toNat :=
                    fid_k6_off_add (mv := s.scratch.scratch_buf[4214]'h4214) (k := 5)
                      (x := i - 1#32) hmv_hi (by decide) (by rw [hi1]; omega)
                  have hana_lt : ((4224 + 5 * (s.scratch.scratch_buf[4214]'h4214) +
                      (i - 1#32)).setWidth 64).toNat < scrc.length := by
                    rw [hlc, hana_e, hi1]; omega
                  let slit := scrc[((4224 + 5 * (s.scratch.scratch_buf[4214]'h4214) +
                    (i - 1#32)).setWidth 64).toNat]'hana_lt
                  c0_hstraight
                  refine wp_join_group (ts := [i32]) (fun _ md => ∃ scrd,
                    FidAnaInv s.scratch.scratch_buf
                      (s.scratch.scratch_buf[4214]'h4214).toNat scrd ∧
                    (FullMem c (m8ScrSt s scrd) ⋆ R) md) ?_ ?_
                  · rintro _ _ md ⟨scrd, hkd, hmd⟩
                    c0_hsteps!; exact hL1 (i.toNat - 1) (i - 1#32, ()) md (by omega)
                      ⟨scrd, hkd, by omega, hi1.symm, hmd⟩
                  · intro J2 hJ2; c0_hstraight; c0_hsplit
                    · have hana_idx : (4224 + 5 * (s.scratch.scratch_buf[4214]'h4214).toNat +
                            (4294967295 + i.toNat)) % 2 ^ 32 =
                          ((4224 + 5 * (s.scratch.scratch_buf[4214]'h4214) +
                            (i - 1#32)).setWidth 64).toNat := by
                        rw [hana_e, hi1]; omega
                      have hv_lt : slit.toNat / 2 < (s.scratch.scratch_buf[4192]'h4192).toNat := by
                        change scrc[(4224 + 5 * (s.scratch.scratch_buf[4214]'h4214).toNat +
                            (4294967295 + i.toNat)) % 2 ^ 32].toNat / 2 <
                          (s.scratch.scratch_buf[4192]'h4192).toNat at hc
                        rwa [fidAna_get_congr _ hana_lt hana_idx] at hc
                      have hsh : (slit >>> 1).toNat = slit.toNat / 2 := by
                        simp [Nat.shiftRight_eq_div_pow]
                      have hsn_e : ((4224 + 6 * (s.scratch.scratch_buf[4214]'h4214) +
                          (slit >>> 1)).setWidth 64).toNat =
                          4224 + 6 * (s.scratch.scratch_buf[4214]'h4214).toNat +
                            (slit >>> 1).toNat :=
                        fid_k6_off_add (mv := s.scratch.scratch_buf[4214]'h4214)
                          (k := 6) (x := slit >>> 1) hmv_hi (by decide) (by rw [hsh]; omega)
                      have hsn_lt : ((4224 + 6 * (s.scratch.scratch_buf[4214]'h4214) +
                          (slit >>> 1)).setWidth 64).toNat < scrc.length := by
                        rw [hlc, hsn_e, hsh]; omega
                      c0_hstraight; c0_hsplit
                      · have hlvl_e : ((4224 + (slit >>> 1)).setWidth 64).toNat =
                            4224 + (slit >>> 1).toNat := by
                          have h := fid_k6_off_add (mv := s.scratch.scratch_buf[4214]'h4214)
                            (k := 0) (x := slit >>> 1) hmv_hi (by decide) (by rw [hsh]; omega)
                          simp only [Nat.zero_mul, BitVec.ofNat_eq_ofNat, BitVec.zero_mul,
                            BitVec.add_zero] at h
                          simpa using h
                        have hlvl_lt : ((4224 + (slit >>> 1)).setWidth 64).toNat <
                            scrc.length := by rw [hlc, hlvl_e, hsh]; omega
                        c0_hstraight; c0_hsplit
                        · have h4212_lt_set :
                              4212 < (scrc.set 4212 ((scrc[4212]'h4212_ltc) - 1#32)).length := by
                            simp; omega
                          c0_hstraight
                          let scrd := scrc.set 4212 ((scrc[4212]'h4212_ltc) - 1#32)
                          have hkd : FidAnaInv s.scratch.scratch_buf
                              (s.scratch.scratch_buf[4214]'h4214).toNat scrd :=
                            fidAnaInv_set hkc ((scrc[4212]'h4212_ltc) - 1#32) (Or.inr (Or.inl rfl))
                          c0_hsplit
                          · c0_hsteps!; exact hJ (i - 1#32, slit ^^^ 1#32, scrd) _ ⟨hkd, hm⟩
                          · have hrsn_e : ((4224 + (s.scratch.scratch_buf[4214]'h4214) +
                                  (slit >>> 1)).setWidth 64).toNat =
                                4224 + (s.scratch.scratch_buf[4214]'h4214).toNat +
                                  (slit >>> 1).toNat := by
                              have h := fid_k6_off_add
                                (mv := s.scratch.scratch_buf[4214]'h4214) (k := 1)
                                (x := slit >>> 1) hmv_hi (by decide) (by rw [hsh]; omega)
                              simp only [Nat.one_mul, BitVec.ofNat_eq_ofNat, BitVec.one_mul] at h
                              simpa using h
                            have hrsn_lt : ((4224 + (s.scratch.scratch_buf[4214]'h4214) +
                                (slit >>> 1)).setWidth 64).toNat < scrd.length := by
                              simp only [scrd, List.length_set, hlc, hrsn_e, hsh]; omega
                            c0_hstraight; c0_hsplit
                            · c0_hsteps!; exact hJ (i - 1#32, slit ^^^ 1#32, scrd) _ ⟨hkd, hm⟩
                            · refine fidAna_call_ana_cl hAnaCl hlen hok hscr_len h4214
                                hmv_eq hmv_hi hkd hm ?_
                              intro scre me hke hme
                              c0_hsteps!; exact hJ2 (4294967295#32, ()) me ⟨scre, hke, hme⟩
                        · c0_hsteps!; exact hJ2 (4294967295#32, ()) mc ⟨scrc, hkc, hmc⟩
                      · c0_hsteps!; exact hJ2 (4294967295#32, ()) mc ⟨scrc, hkc, hmc⟩
                    · c0_hsteps!; exact hJ2 (4294967295#32, ()) mc ⟨scrc, hkc, hmc⟩
              · c0_hsteps!; exact hJ (i, 4294967295#32, scrc) mc ⟨hkc, hmc⟩
            · intro L1 hL1; c0_hsteps!; exact hL1 max_b.toNat (max_b, ()) ma
                ⟨scra, hka, hmax_le, rfl, hma⟩
        · intro J0 hJ0; c0_hstraight; c0_hsplit
          · c0_hsteps!; exact hJ0 (s.scratch.scratch_buf[4214]'h4214) ma ⟨Nat.le_refl _, rfl⟩
          · have hc' : trail_end.toNat ≤ (s.scratch.scratch_buf[4214]'h4214).toNat := by
              change ¬(s.scratch.scratch_buf[4214]'h4214).toNat < trail_end.toNat at hc; omega
            c0_hsteps!; exact hJ0 trail_end ma ⟨hc', rfl⟩
