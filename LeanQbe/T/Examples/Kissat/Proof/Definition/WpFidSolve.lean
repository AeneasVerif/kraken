/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpFidBasic

/-!
# Kissat Fidelity BVE WP Proofs — `full_k6_solve_fid_wp`

`CanonicalEnv`-clean `Func.wp` proof for `full_k6_solve_fid` (`0` legacy `Full*` imports;
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

/-! ## 1. `FidSolveInv`, Preservation & Callee Helpers -/

private def FidSolveInv (scr0 : List (BitVec 32)) (mv nc0 : Nat)
    (scr : List (BitVec 32)) : Prop :=
  scr.length = scr0.length ∧
  (∀ i, i < 4192 → scr[i]? = scr0[i]?) ∧
  scr[4194]? = scr0[4194]? ∧
  scr[4214]? = scr0[4214]? ∧
  nc0 ≤ (scr[4193]?.getD 0#32).toNat ∧
  (∀ cid, cid < nc0 → scr[4224 + 37 * mv + cid]? = scr0[4224 + 37 * mv + cid]?)

private theorem fidSolveInv_refl (scr0 : List (BitVec 32))
    (hnc : (scr0[4194]?.getD 0#32).toNat ≤ (scr0[4193]?.getD 0#32).toNat) :
    FidSolveInv scr0 (scr0[4214]?.getD 0#32).toNat (scr0[4194]?.getD 0#32).toNat scr0 :=
  ⟨rfl, fun _ _ => rfl, rfl, rfl, hnc, fun _ _ => rfl⟩

private theorem fidSolveInv_set {scr0 scra : List (BitVec 32)} {mv nc0 : Nat}
    (hk : FidSolveInv scr0 mv nc0 scra) (idx : Nat) (v : BitVec 32)
    (h4195 : 4195 ≤ idx) (hlt : idx < 4224) (h4214 : idx ≠ 4214) :
    FidSolveInv scr0 mv nc0 (scra.set idx v) := by
  refine ⟨by simp [hk.1], fun i hi0 => ?_, ?_, ?_, ?_, fun cid hc => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.1 i hi0
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.2.1
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.2.2.1
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.2.2.2.1
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.2.2.2.2 cid hc

private theorem fidSolve_bufOk_set {scra : List (BitVec 32)}
    (hok : FidK6BufOk scra) (idx : Nat) (v : BitVec 32)
    (h4195 : 4195 ≤ idx) (hlt : idx < 4224)
    (h4206 : idx ≠ 4206) (h4207 : idx ≠ 4207) (h4214 : idx ≠ 4214) :
    FidK6BufOk (scra.set idx v) := by
  have hmvs : (scra.set idx v)[4214]? = scra[4214]? := List.getElem?_set_ne (by omega)
  have hncs : (scra.set idx v)[4193]? = scra[4193]? := List.getElem?_set_ne (by omega)
  have hals : (scra.set idx v)[4206]? = scra[4206]? := List.getElem?_set_ne (by omega)
  have hacs : (scra.set idx v)[4207]? = scra[4207]? := List.getElem?_set_ne (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun cid hc => ?_⟩
  · have := hok.mv_lo; rwa [hmvs]
  · have := hok.mv_hi; rwa [hmvs]
  · have := hok.length_ge; simp only [List.length_set, hmvs, hacs]; exact this
  · have := hok.length_lt; simp only [List.length_set]; exact this
  · have := hok.nc_le; rwa [hncs, hmvs]
  · have := hok.alen_le; rwa [hals, hacs]
  · simp only [hmvs] at hc ⊢
    rw [hncs] at hc
    have hmv_get : ((scra.set idx v)[4214]?.getD 0#32).toNat = (scra[4214]?.getD 0#32).toNat := by
      rw [hmvs]
    have hoff : (scra.set idx v)[4224 + 29 * (scra[4214]?.getD 0#32).toNat + cid]? =
        scra[4224 + 29 * (scra[4214]?.getD 0#32).toNat + cid]? :=
      List.getElem?_set_ne (by omega)
    have hmt : (scra.set idx v)[4224 + 33 * (scra[4214]?.getD 0#32).toNat + cid]? =
        scra[4224 + 33 * (scra[4214]?.getD 0#32).toNat + cid]? :=
      List.getElem?_set_ne (by omega)
    have hax : (scra.set idx v)[4224 + 37 * (scra[4214]?.getD 0#32).toNat + cid]? =
        scra[4224 + 37 * (scra[4214]?.getD 0#32).toNat + cid]? :=
      List.getElem?_set_ne (by omega)
    have hcl := hok.2.2.2.2.2.2 cid hc
    simpa only [hmv_get, hoff, hmt, hax, hacs] using hcl

private theorem fidSolve_final_post {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {Q : Post [i64]} {scr0 scr : List (BitVec 32)} {fl : BitVec 64} {m : Mem 64}
    (hscr_len : scr0.length = c.scratch_cap)
    (hok : FidK6BufOk scr) (hk : FidSolveInv scr0 (scr0[4214]?.getD 0#32).toNat
      (scr0[4194]?.getD 0#32).toNat scr)
    (hfl : fl.toNat ≤ s.core.fuel.toNat) (hm : (FullMem c (m8ScrFuelSt s fl scr) ⋆ R) m)
    (hK : ∀ (r : BitVec 64) (scr' : List (BitVec 32)) (fuel' : BitVec 64) (m' : Mem 64),
      FidK6BufOk scr' → scr'.length = c.scratch_cap → (∀ i < 4192, scr'[i]? = scr0[i]?) →
      scr'[4194]? = scr0[4194]? → scr'[4214]? = scr0[4214]? →
      (scr0[4194]?.getD 0#32).toNat ≤ (scr'[4193]?.getD 0#32).toNat →
      (∀ cid < (scr0[4194]?.getD 0#32).toNat,
        scr'[4224 + 37 * (scr0[4214]?.getD 0#32).toNat + cid]? =
          scr0[4224 + 37 * (scr0[4214]?.getD 0#32).toNat + cid]?) →
      fuel'.toNat ≤ s.core.fuel.toNat → (FullMem c (m8ScrFuelSt s fuel' scr') ⋆ R) m' →
      Q (r, ()) m')
    (r : BitVec 64) : Q (r, ()) m :=
  hK r scr fl m hok (hk.1.trans hscr_len) hk.2.1 hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2.1
    hk.2.2.2.2.2 hfl hm

private theorem fidSolve_inv_of_backtrack {c : FullCfg} {scr0 scra scrb : List (BitVec 32)}
    {mv nc0 : Nat}
    (hka : FidSolveInv scr0 mv nc0 scra) (hmv_eq : scra[4214]?.getD 0#32 = scr0[4214]?.getD 0#32)
    (hmv_def : (scr0[4214]?.getD 0#32).toNat = mv)
    (hlen : scrb.length = c.scratch_cap) (hcap : scr0.length = c.scratch_cap)
    (hpres : ∀ idx, idx < c.scratch_cap →
      (idx < 4195 ∨ 4199 ≤ idx ∧ idx < 4224 ∨
        4224 + 2 * (scra[4214]?.getD 0#32).toNat ≤ idx ∧
          idx < 4224 + 9 * (scra[4214]?.getD 0#32).toNat ∨
        4224 + 11 * (scra[4214]?.getD 0#32).toNat ≤ idx) → scrb[idx]? = scra[idx]?)
    (hnc4 : nc0 ≤ 4 * mv) (h45 : 4224 + 45 * mv ≤ scr0.length) :
    FidSolveInv scr0 mv nc0 scrb := by
  have hlen_b : scrb.length = scr0.length := hlen.trans hcap.symm
  have hgt_37 : ∀ cid, cid < nc0 →
      scrb[4224 + 37 * mv + cid]? = scra[4224 + 37 * mv + cid]? := by
    intro cid hcid
    exact hpres _ (by omega) (Or.inr (Or.inr (Or.inr (by rw [hmv_eq, hmv_def]; omega))))
  refine ⟨hlen_b, fun i hi => ?_, ?_, ?_, ?_, fun cid hcid => ?_⟩
  · rw [hpres i (by omega) (Or.inl (by omega))]; exact hka.2.1 i hi
  · rw [hpres 4194 (by omega) (Or.inl (by omega))]; exact hka.2.2.1
  · rw [hpres 4214 (by omega) (Or.inr (Or.inl (by omega)))]; exact hka.2.2.2.1
  · rw [hpres 4193 (by omega) (Or.inl (by omega))]; exact hka.2.2.2.2.1
  · rw [hgt_37 cid hcid]; exact hka.2.2.2.2.2 cid hcid

private theorem fidSolve_inv_of_assign {c : FullCfg} {scr0 scra scrb : List (BitVec 32)}
    {mv nc0 : Nat}
    (hka : FidSolveInv scr0 mv nc0 scra) (hmv_eq : scra[4214]?.getD 0#32 = scr0[4214]?.getD 0#32)
    (hmv_def : (scr0[4214]?.getD 0#32).toNat = mv)
    (hlen : scrb.length = c.scratch_cap) (hcap : scr0.length = c.scratch_cap)
    (hpres : ∀ idx, idx < c.scratch_cap → idx ≠ 4197 → idx ≠ 4198 →
      (idx < 4224 ∨ 4224 + 2 * (scra[4214]?.getD 0#32).toNat ≤ idx) →
      (idx < 4224 + 5 * (scra[4214]?.getD 0#32).toNat ∨
        4224 + 7 * (scra[4214]?.getD 0#32).toNat ≤ idx) →
      (idx < 4224 + 9 * (scra[4214]?.getD 0#32).toNat ∨
        4224 + 11 * (scra[4214]?.getD 0#32).toNat ≤ idx) → scrb[idx]? = scra[idx]?)
    (h45 : 4224 + 45 * mv ≤ scr0.length) :
    FidSolveInv scr0 mv nc0 scrb := by
  have hlen_b : scrb.length = scr0.length := hlen.trans hcap.symm
  have hsub : ∀ idx, idx < 4224 → idx ≠ 4197 → idx ≠ 4198 → scrb[idx]? = scra[idx]? := by
    intro idx hi h97 h98
    exact hpres idx (by omega) h97 h98 (Or.inl hi) (Or.inl (by omega)) (Or.inl (by omega))
  refine ⟨hlen_b, fun i hi => ?_, ?_, ?_, ?_, fun cid hcid => ?_⟩
  · rw [hsub i (by omega) (by omega) (by omega)]; exact hka.2.1 i hi
  · rw [hsub 4194 (by omega) (by omega) (by omega)]; exact hka.2.2.1
  · rw [hsub 4214 (by omega) (by omega) (by omega)]; exact hka.2.2.2.1
  · rw [hsub 4193 (by omega) (by omega) (by omega)]; exact hka.2.2.2.2.1
  · by_cases hlt : 4224 + 37 * mv + cid < c.scratch_cap
    · rw [hpres _ hlt (by omega) (by omega) (Or.inr (by rw [hmv_eq, hmv_def]; omega))
        (Or.inr (by rw [hmv_eq, hmv_def]; omega)) (Or.inr (by rw [hmv_eq, hmv_def]; omega))]
      exact hka.2.2.2.2.2 cid hcid
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

private theorem fidSolve_inv_of_prop {c : FullCfg} {scr0 scra scrb : List (BitVec 32)}
    {mv nc0 : Nat}
    (hka : FidSolveInv scr0 mv nc0 scra) (hmv_eq : scra[4214]?.getD 0#32 = scr0[4214]?.getD 0#32)
    (hmv_def : (scr0[4194]?.getD 0#32).toNat = nc0) (hmv_val : (scr0[4214]?.getD 0#32).toNat = mv)
    (hlen : scrb.length = c.scratch_cap) (hcap : scr0.length = c.scratch_cap)
    (h_lo : ∀ i, i < 4195 → scrb[i]? = scra[i]?)
    (h_mid : ∀ i, 4205 ≤ i → i < 4224 → scrb[i]? = scra[i]?)
    (h_hi : ∀ i, 4224 + 29 * (scra[4214]?.getD 0#32).toNat ≤ i →
      i < 4224 + 45 * (scra[4214]?.getD 0#32).toNat → scrb[i]? = scra[i]?)
    (_h_nc : (scra[4193]?.getD 0#32).toNat ≤ 4 * mv) :
    FidSolveInv scr0 mv nc0 scrb := by
  have hlen_b : scrb.length = scr0.length := hlen.trans hcap.symm
  refine ⟨hlen_b, fun i hi => ?_, ?_, ?_, ?_, fun cid hcid => ?_⟩
  · rw [h_lo i (by omega)]; exact hka.2.1 i hi
  · rw [h_lo 4194 (by omega)]; exact hka.2.2.1
  · rw [h_mid 4214 (by omega) (by omega)]; exact hka.2.2.2.1
  · rw [h_lo 4193 (by omega)]; exact hka.2.2.2.2.1
  · have hc_nc : cid < (scra[4193]?.getD 0#32).toNat := Nat.lt_of_lt_of_le hcid hka.2.2.2.2.1
    rw [h_hi (4224 + 37 * mv + cid) (by rw [hmv_eq, hmv_val]; omega)
      (by rw [hmv_eq, hmv_val]; omega)]
    exact hka.2.2.2.2.2 cid hcid

private theorem fidSolve_inv_of_analyze {c : FullCfg} {scr0 scra scrb : List (BitVec 32)}
    {mv nc0 : Nat}
    (hka : FidSolveInv scr0 mv nc0 scra) (hmv_eq : scra[4214]?.getD 0#32 = scr0[4214]?.getD 0#32)
    (hmv_val : (scr0[4214]?.getD 0#32).toNat = mv)
    (hlen : scrb.length = c.scratch_cap) (hcap : scr0.length = c.scratch_cap)
    (h_lo : ∀ i, i < 4193 → scrb[i]? = scra[i]?)
    (h4194 : scrb[4194]? = scra[4194]?)
    (hnc_le : (scra[4193]?.getD 0#32).toNat ≤ (scrb[4193]?.getD 0#32).toNat)
    (hclauses : ∀ cid, cid < (scra[4193]?.getD 0#32).toNat →
      scrb[4224 + 37 * (scra[4214]?.getD 0#32).toNat + cid]? =
        scra[4224 + 37 * (scra[4214]?.getD 0#32).toNat + cid]?)
    (h4214 : scrb[4214]? = scra[4214]?) :
    FidSolveInv scr0 mv nc0 scrb := by
  refine ⟨hlen.trans hcap.symm, fun i hi => ?_, ?_, ?_, ?_, fun cid hcid => ?_⟩
  · rw [h_lo i (by omega)]; exact hka.2.1 i hi
  · rw [h4194]; exact hka.2.2.1
  · rw [h4214]; exact hka.2.2.2.1
  · exact Nat.le_trans hka.2.2.2.2.1 hnc_le
  · have hc_nc : cid < (scra[4193]?.getD 0#32).toNat := Nat.lt_of_lt_of_le hcid hka.2.2.2.2.1
    have hcl := hclauses cid hc_nc
    rw [hmv_eq, hmv_val] at hcl
    rw [hcl]; exact hka.2.2.2.2.2 cid hcid

private theorem fidSolve_bufOk_of_pres {scra scrb : List (BitVec 32)}
    (hoka : FidK6BufOk scra) (hlen_eq : scrb.length = scra.length)
    (h4193 : scrb[4193]? = scra[4193]?) (h4206 : scrb[4206]? = scra[4206]?)
    (h4207 : scrb[4207]? = scra[4207]?) (h4214 : scrb[4214]? = scra[4214]?)
    (hhi : ∀ i, 4224 + 11 * (scra[4214]?.getD 0#32).toNat ≤ i → scrb[i]? = scra[i]?) :
    FidK6BufOk scrb := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun cid hc => ?_⟩
  · have := hoka.mv_lo; rwa [h4214]
  · have := hoka.mv_hi; rwa [h4214]
  · have := hoka.length_ge; rwa [hlen_eq, h4214, h4207]
  · have := hoka.length_lt; rwa [hlen_eq]
  · have := hoka.nc_le; rwa [h4193, h4214]
  · have := hoka.alen_le; rwa [h4206, h4207]
  · simp only [h4193] at hc
    have hmv_get : (scrb[4214]?.getD 0#32).toNat = (scra[4214]?.getD 0#32).toNat := by
      rw [h4214]
    have hoff := hhi (4224 + 29 * (scra[4214]?.getD 0#32).toNat + cid) (by omega)
    have hmt := hhi (4224 + 33 * (scra[4214]?.getD 0#32).toNat + cid) (by omega)
    have hax := hhi (4224 + 37 * (scra[4214]?.getD 0#32).toNat + cid) (by omega)
    have hcl := hoka.2.2.2.2.2.2 cid hc
    simpa only [hmv_get, hoff, hmt, hax, h4207] using hcl

private theorem fidSolve_call_backtrack {Γ : Env} {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {scr0 scra : List (BitVec 32)}
    {fl : BitVec 64} {ma : Mem 64} {lvl : BitVec 32}
    {k : Tup Val [] → Expr Val Cont [i64]}
    (hBt : Γ.Has "full_k6_backtrack_fid" fidK6BacktrackSpec)
    (hlen : FullState.LengthsOk c s) (hoka : FidK6BufOk scra)
    (hscr_len : scr0.length = c.scratch_cap) (hka : FidSolveInv scr0
      (scr0[4214]?.getD 0#32).toNat (scr0[4194]?.getD 0#32).toNat scra)
    (hm : (FullMem c (m8ScrFuelSt s fl scra) ⋆ R) ma)
    (hk : ∀ scrb mb, FidK6BufOk scrb →
      FidSolveInv scr0 (scr0[4214]?.getD 0#32).toNat (scr0[4194]?.getD 0#32).toNat scrb →
      (FullMem c (m8ScrFuelSt s fl scrb) ⋆ R) mb → wp Γ Q X (k ()) mb) :
    wp Γ Q X (Expr.call (as := [i64, i32]) (bs := []) "full_k6_backtrack_fid"
      (Arg.var c.hdr, Arg.var lvl, PUnit.unit) k) ma := by
  have hmv_eq : scra[4214]?.getD 0#32 = scr0[4214]?.getD 0#32 := by rw [hka.2.2.2.1]
  have h45 : 4224 + 45 * (scr0[4214]?.getD 0#32).toNat ≤ scr0.length := by
    have := hoka.length_ge; rw [hmv_eq, hka.1] at this; omega
  have hnc4 : (scr0[4194]?.getD 0#32).toNat ≤ 4 * (scr0[4214]?.getD 0#32).toNat := by
    have := hoka.nc_le; rw [hmv_eq] at this; exact Nat.le_trans hka.2.2.2.2.1 this
  c0_hcall hBt
  refine fidK6BacktrackSpec_intro
    (s := m8ScrFuelSt s fl scra) rfl (m8ScrFuelSt_lengthsOk hlen (hka.1.trans hscr_len) fl)
    hoka hm ?_
  intro scrb mb hlen_b hpres hmb
  have h4193 : scrb[4193]? = scra[4193]? := hpres 4193 (by omega) (Or.inl (by omega))
  have h4206 : scrb[4206]? = scra[4206]? := hpres 4206 (by omega) (Or.inr (Or.inl (by omega)))
  have h4207 : scrb[4207]? = scra[4207]? := hpres 4207 (by omega) (Or.inr (Or.inl (by omega)))
  have h4214 : scrb[4214]? = scra[4214]? := hpres 4214 (by omega) (Or.inr (Or.inl (by omega)))
  have hhi : ∀ i, 4224 + 11 * (scra[4214]?.getD 0#32).toNat ≤ i → scrb[i]? = scra[i]? := by
    intro i hi
    by_cases hlt : i < c.scratch_cap
    · exact hpres i hlt (Or.inr (Or.inr (Or.inr hi)))
    · rw [List.getElem?_eq_none (by omega),
        List.getElem?_eq_none (by rw [hka.1, hscr_len]; omega)]
  have hokb := fidSolve_bufOk_of_pres hoka (hlen_b.trans (hka.1.trans hscr_len).symm)
    h4193 h4206 h4207 h4214 hhi
  exact hk scrb mb hokb (fidSolve_inv_of_backtrack hka hmv_eq rfl hlen_b hscr_len hpres hnc4 h45)
    hmb

private theorem fidSolve_call_assign {Γ : Env} {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {scr0 scra : List (BitVec 32)}
    {fl : BitVec 64} {ma : Mem 64} {lit rsn : BitVec 32}
    {k : Tup Val [] → Expr Val Cont [i64]}
    (hAssign : Γ.Has "full_k6_assign_fid" fidK6AssignSpec)
    (hlen : FullState.LengthsOk c s) (hoka : FidK6BufOk scra)
    (hscr_len : scr0.length = c.scratch_cap) (hka : FidSolveInv scr0
      (scr0[4214]?.getD 0#32).toNat (scr0[4194]?.getD 0#32).toNat scra)
    (hm : (FullMem c (m8ScrFuelSt s fl scra) ⋆ R) ma)
    (hk : ∀ scrb mb, FidK6BufOk scrb →
      FidSolveInv scr0 (scr0[4214]?.getD 0#32).toNat (scr0[4194]?.getD 0#32).toNat scrb →
      (∀ i, i < 4224 → i ≠ 4197 → i ≠ 4198 → scrb[i]? = scra[i]?) →
      (∀ i, 4224 + 11 * (scr0[4214]?.getD 0#32).toNat ≤ i → scrb[i]? = scra[i]?) →
      (FullMem c (m8ScrFuelSt s fl scrb) ⋆ R) mb → wp Γ Q X (k ()) mb) :
    wp Γ Q X (Expr.call (as := [i64, i32, i32]) (bs := []) "full_k6_assign_fid"
      (Arg.var c.hdr, Arg.var lit, Arg.var rsn, PUnit.unit) k) ma := by
  have hmv_eq : scra[4214]?.getD 0#32 = scr0[4214]?.getD 0#32 := by rw [hka.2.2.2.1]
  have h45 : 4224 + 45 * (scr0[4214]?.getD 0#32).toNat ≤ scr0.length := by
    have := hoka.length_ge; rw [hmv_eq, hka.1] at this; omega
  c0_hcall hAssign
  refine fidK6AssignSpec_intro
    (s := m8ScrFuelSt s fl scra) rfl (m8ScrFuelSt_lengthsOk hlen (hka.1.trans hscr_len) fl)
    hoka hm ?_
  intro scrb mb hlen_b hpres hmb
  dsimp only [m8ScrFuelSt] at hpres
  have hlo : ∀ i, i < 4224 → i ≠ 4197 → i ≠ 4198 → scrb[i]? = scra[i]? := by
    intro i hi h97 h98
    exact hpres i (by omega) h97 h98 (Or.inl hi) (Or.inl (by omega)) (Or.inl (by omega))
  have hhi : ∀ i, 4224 + 11 * (scr0[4214]?.getD 0#32).toNat ≤ i → scrb[i]? = scra[i]? := by
    intro i hi
    by_cases hlt : i < c.scratch_cap
    · exact hpres i hlt (by omega) (by omega) (Or.inr (by rw [hmv_eq]; omega))
        (Or.inr (by rw [hmv_eq]; omega)) (Or.inr (by rw [hmv_eq]; omega))
    · rw [List.getElem?_eq_none (by omega),
        List.getElem?_eq_none (by rw [hka.1, hscr_len]; omega)]
  have hokb := fidSolve_bufOk_of_pres hoka (hlen_b.trans (hka.1.trans hscr_len).symm)
    (hlo 4193 (by omega) (by omega) (by omega)) (hlo 4206 (by omega) (by omega) (by omega))
    (hlo 4207 (by omega) (by omega) (by omega)) (hlo 4214 (by omega) (by omega) (by omega))
    (by rw [hmv_eq]; exact hhi)
  exact hk scrb mb hokb (fidSolve_inv_of_assign hka hmv_eq rfl hlen_b hscr_len hpres h45)
    hlo hhi hmb

private theorem fidSolve_call_prop {Γ : Env} {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {scr0 scra : List (BitVec 32)}
    {fl : BitVec 64} {ma : Mem 64} {k : Tup Val [i32] → Expr Val Cont [i64]}
    (hProp : Γ.Has "full_k6_prop_fid" fidK6PropSpec)
    (hlen : FullState.LengthsOk c s) (hoka : FidK6BufOk scra)
    (hscr_len : scr0.length = c.scratch_cap) (hka : FidSolveInv scr0
      (scr0[4214]?.getD 0#32).toNat (scr0[4194]?.getD 0#32).toNat scra)
    (hm : (FullMem c (m8ScrFuelSt s fl scra) ⋆ R) ma)
    (hk : ∀ confl scrb mb, FidK6BufOk scrb →
      FidSolveInv scr0 (scr0[4214]?.getD 0#32).toNat (scr0[4194]?.getD 0#32).toNat scrb →
      (FullMem c (m8ScrFuelSt s fl scrb) ⋆ R) mb → wp Γ Q X (k (confl, ())) mb) :
    wp Γ Q X (Expr.call (as := [i64]) (bs := [i32]) "full_k6_prop_fid"
      (Arg.var c.hdr, PUnit.unit) k) ma := by
  have hmv_eq : scra[4214]?.getD 0#32 = scr0[4214]?.getD 0#32 := by rw [hka.2.2.2.1]
  have hnc_le : (scra[4193]?.getD 0#32).toNat ≤ 4 * (scr0[4214]?.getD 0#32).toNat := by
    have := hoka.nc_le; rwa [hmv_eq] at this
  c0_hcall hProp
  refine fidK6PropSpec_intro
    (s := m8ScrFuelSt s fl scra) rfl (m8ScrFuelSt_lengthsOk hlen (hka.1.trans hscr_len) fl)
    hoka hm ?_
  rintro confl scrb mb _ _ hokb hlen_b h_lo _ h_mid _ _ h_hi hmb
  exact hk confl scrb mb hokb
    (fidSolve_inv_of_prop hka hmv_eq rfl rfl hlen_b hscr_len h_lo h_mid h_hi hnc_le) hmb

private theorem fidSolve_call_analyze {Γ : Env} {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {scr0 scra : List (BitVec 32)}
    {fl : BitVec 64} {ma : Mem 64} {confl : BitVec 32}
    {k : Tup Val [Ty.bool] → Expr Val Cont [i64]}
    (hAna : Γ.Has "full_k6_analyze_fid" fidK6AnalyzeSpec)
    (hlen : FullState.LengthsOk c s) (hoka : FidK6BufOk scra)
    (hscr_len : scr0.length = c.scratch_cap) (hka : FidSolveInv scr0
      (scr0[4214]?.getD 0#32).toNat (scr0[4194]?.getD 0#32).toNat scra)
    (hm : (FullMem c (m8ScrFuelSt s fl scra) ⋆ R) ma)
    (hk : ∀ ok scrb mb, FidK6BufOk scrb →
      FidSolveInv scr0 (scr0[4214]?.getD 0#32).toNat (scr0[4194]?.getD 0#32).toNat scrb →
      (FullMem c (m8ScrFuelSt s fl scrb) ⋆ R) mb → wp Γ Q X (k (ok, ())) mb) :
    wp Γ Q X (Expr.call (as := [i64, i32]) (bs := [Ty.bool]) "full_k6_analyze_fid"
      (Arg.var c.hdr, Arg.var confl, PUnit.unit) k) ma := by
  have hmv_eq : scra[4214]?.getD 0#32 = scr0[4214]?.getD 0#32 := by rw [hka.2.2.2.1]
  c0_hcall hAna
  refine fidK6AnalyzeSpec_intro
    (s := m8ScrFuelSt s fl scra) rfl (m8ScrFuelSt_lengthsOk hlen (hka.1.trans hscr_len) fl)
    hoka hm ?_
  rintro ok scrb mb _ _ hokb hlen_b h_lo h4194 hnc_mono hclauses _ _ _ _ _ h4214 _ _ _ hmb
  exact hk ok scrb mb hokb
    (fidSolve_inv_of_analyze hka hmv_eq rfl hlen_b hscr_len h_lo h4194 hnc_mono hclauses h4214)
    hmb

private theorem fidSolve_get_congr {xs : List (BitVec 32)} {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) (h : i = j) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

/-! ## 2. Address Helpers & Initial Watch-Unit Scan Loop -/

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

private theorem fidSolve_shl1_toNat {x : BitVec 32} (hx : x.toNat ≤ 8192) :
    (x <<< (1 : BitVec 32)).toNat = 2 * x.toNat := by
  change (x <<< 1).toNat = 2 * x.toNat
  rw [BitVec.toNat_shiftLeft]; simp only [Nat.shiftLeft_eq]; omega

private def fidSolveUnitBodyExpr (pScr cHdr : BitVec 64)
    (mv nv nc acap nuni : BitVec 32) (cont : Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  let o_vals2 : BitVec 32 := 4224 + 9 * mv; let o_off : BitVec 32 := 4224 + 29 * mv
  let o_uni : BitVec 32 := 4224 + 41 * mv; let o_ar : BitVec 32 := 4224 + 45 * mv
  Expr.group (sig := [[i32]]) (fun Js => Blocks.cons (fun p_47 =>
   Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
               args := (Arg.var p_47.fst, Arg.var nuni, ()) } fun p_48 =>
   Expr.jnz (Arg.var p_48.fst)
    (fidScrOffPtr pScr o_uni p_47.fst fun p_52 => Expr.load i32 (Arg.var p_52) fun ld_7 =>
     Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
      Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                  args := (Arg.var p_47.fst, Arg.imm 1, ()) } fun p =>
      Expr.jump Js.fst (Arg.var p.fst, ())) Blocks.nil) fun Js =>
     Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                 args := (Arg.var ld_7, Arg.var nc, ()) } fun p_53 =>
     Expr.jnz (Arg.var p_53.fst)
      (fidScrOffPtr pScr o_off ld_7 fun p_57 => Expr.load i32 (Arg.var p_57) fun ld_8 =>
       Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ => Expr.jump Js.fst ())
        Blocks.nil) fun Js =>
       Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                   args := (Arg.var ld_8, Arg.var acap, ()) } fun p_58 =>
       Expr.jnz (Arg.var p_58.fst)
        (fidScrOffPtr pScr o_ar ld_8 fun p_62 => Expr.load i32 (Arg.var p_62) fun ld_9 =>
         Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ => Expr.jump Js.fst ())
          Blocks.nil) fun Js =>
         Expr.let_ { sig := [i32, i32], code := OpCode.shl i32,
                     args := (Arg.var nv, Arg.imm 1, ()) } fun p_63 =>
         Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                     args := (Arg.var ld_9, Arg.var p_63.fst, ()) } fun p_64 =>
         Expr.jnz (Arg.var p_64.fst)
          (fidScrOffPtr pScr o_vals2 ld_9 fun p_68 => Expr.load i32 (Arg.var p_68) fun ld_10 =>
           Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool (by decide),
                       args := (Arg.var ld_10, Arg.imm 2, ()) } fun p_69 =>
           Expr.jnz (Arg.var p_69.fst)
            (fidScrImmPtr pScr 4199 fun p => Expr.store (Arg.var ld_7) (Arg.var p)
              (Expr.ret (rs := [i64]) (Arg.imm 20, ())))
            (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ => Expr.jump Js.fst ())
              Blocks.nil) fun Js =>
             Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool (by decide),
                         args := (Arg.var ld_10, Arg.imm 0, ()) } fun p_70 =>
             Expr.jnz (Arg.var p_70.fst)
              (Expr.call (as := [i64, i32, i32]) (bs := []) "full_k6_assign_fid"
                (Arg.var cHdr, Arg.var ld_9, Arg.var ld_7, PUnit.unit) fun _ =>
               Expr.jump Js.fst ())
              (Expr.jump Js.fst ())))
          (Expr.jump Js.fst ()))
        (Expr.jump Js.fst ()))
      (Expr.jump Js.fst ()))
    cont) Blocks.nil) fun Js => Expr.jump Js.fst (Arg.imm 0, ())

private theorem fidSolve_unit_loop_wp (Γ : Env) (c : FullCfg) (s : FullState)
    (R : Mem 64 → Prop) (Q : Post [i64]) (X : XPost) (scr0 scr_in : List (BitVec 32))
    (nv nc acap nuni : BitVec 32) (m_in : Mem 64) (cont : Expr Val Cont [i64])
    (hAssign : Γ.Has "full_k6_assign_fid" fidK6AssignSpec)
    (hlen : FullState.LengthsOk c s) (hok_in : FidK6BufOk scr_in)
    (hscr_len : scr0.length = c.scratch_cap) (h4214 : 4214 < scr0.length)
    (_h4193 : 4193 < scr0.length) (_h4207 : 4207 < scr0.length) :
    let mv := scr0[4214]'h4214
    nv.toNat ≤ mv.toNat → nc.toNat ≤ 4 * mv.toNat → nuni.toNat ≤ 2 * mv.toNat →
    scr_in[4214]? = scr0[4214]? → scr_in[4193]? = some nc → scr_in[4207]? = some acap →
    FidSolveInv scr0 (scr0[4214]?.getD 0#32).toNat (scr0[4194]?.getD 0#32).toNat scr_in →
    (FullMem c (m8ScrFuelSt s s.core.fuel scr_in) ⋆ R) m_in →
    (∀ (r : BitVec 64) (scrf : List (BitVec 32)) (mf : Mem 64),
      FidK6BufOk scrf →
      FidSolveInv scr0 (scr0[4214]?.getD 0#32).toNat (scr0[4194]?.getD 0#32).toNat scrf →
      (FullMem c (m8ScrFuelSt s s.core.fuel scrf) ⋆ R) mf → Q (r, ()) mf) →
    (∀ (scrb : List (BitVec 32)) (mb : Mem 64),
      FidK6BufOk scrb →
      FidSolveInv scr0 (scr0[4214]?.getD 0#32).toNat (scr0[4194]?.getD 0#32).toNat scrb →
      (FullMem c (m8ScrFuelSt s s.core.fuel scrb) ⋆ R) mb → wp Γ Q X cont mb) →
    wp Γ Q X (fidSolveUnitBodyExpr c.pScratchBuf c.hdr mv nv nc acap nuni cont) m_in := by
  intro mv hnv_le hnc_le hnuni_le hmv_s hnc_s hacap_s hk_in hm_in hQret hCont
  have hmv_eq : scr0[4214]?.getD 0#32 = mv := m8_k6_get_eq h4214
  have hmv_hi : mv.toNat ≤ 8192 := by
    have := hok_in.mv_hi; rw [hmv_s, hmv_eq] at this; exact this
  have hlen_scr : 4224 + 45 * mv.toNat + acap.toNat ≤ scr0.length := by
    have := hok_in.length_ge
    rw [hmv_s, hmv_eq, hacap_s, hk_in.1] at this; exact this
  dsimp only [fidSolveUnitBodyExpr, fidScrPtr, fidScrOffPtr, fidScrImmPtr]
  refine wp_loop_group (ts := [i32])
    (fun rem (idx, ()) ma => ∃ scra,
      FidK6BufOk scra ∧
      FidSolveInv scr0 (scr0[4214]?.getD 0#32).toNat (scr0[4194]?.getD 0#32).toNat scra ∧
      scra[4193]? = some nc ∧ scra[4207]? = some acap ∧
      idx.toNat ≤ nuni.toNat ∧ rem = nuni.toNat - idx.toNat ∧
      (FullMem c (m8ScrFuelSt s s.core.fuel scra) ⋆ R) ma) ?_ ?_
  · rintro L1 rem1 ⟨idx, ⟨⟩⟩ ma hL1 ⟨scra, hoka, hka, hnca, hacapa, hidx_le, rfl, hma⟩
    have hla : scra.length = scr0.length := hka.1
    c0_hstraight; c0_hsplit
    · have hidx_lt : idx.toNat < nuni.toNat := hc
      have hidx1 : (idx + 1#32).toNat = idx.toNat + 1 := m8_bv32_add1_toNat hidx_lt (by omega)
      have huni_e : ((4224 + 41 * mv + idx).setWidth 64).toNat =
          4224 + 41 * mv.toNat + idx.toNat :=
        fid_k6_off_add (mv := mv) (k := 41) (x := idx) hmv_hi (by decide) (by omega)
      have huni_lt : ((4224 + 41 * mv + idx).setWidth 64).toNat < scra.length := by
        rw [hla, huni_e]; omega
      let cid := scra[((4224 + 41 * mv + idx).setWidth 64).toNat]'huni_lt
      have huni_idx : (4224 + 41 * mv.toNat + idx.toNat) % 4294967296 =
          ((4224 + 41 * mv + idx).setWidth 64).toNat := by
        rw [huni_e]; omega
      have huni_mod_lt : (4224 + 41 * mv.toNat + idx.toNat) % 4294967296 < scra.length := by
        rw [huni_idx]; exact huni_lt
      have hcid_get : scra[(4224 + 41 * mv.toNat + idx.toNat) % 4294967296]'huni_mod_lt = cid :=
        fidSolve_get_congr huni_mod_lt huni_lt huni_idx
      c0_hstraight
      refine wp_join0 (fun mb => ∃ scrb, FidK6BufOk scrb ∧
        FidSolveInv scr0 (scr0[4214]?.getD 0#32).toNat (scr0[4194]?.getD 0#32).toNat scrb ∧
        scrb[4193]? = some nc ∧ scrb[4207]? = some acap ∧
        (FullMem c (m8ScrFuelSt s s.core.fuel scrb) ⋆ R) mb) ?_ ?_
      · rintro _ mb ⟨scrb, hokb, hkb, hncb, hacapb, hmb⟩
        c0_hsteps!
        exact hL1 (nuni.toNat - (idx + 1#32).toNat) (idx + 1#32, ()) _ (by omega)
          ⟨scrb, hokb, hkb, hncb, hacapb, by omega, rfl, hmb⟩
      · intro J1 hJ1; c0_hstraight; c0_hsplit
        · have hcid_lt : cid.toNat < nc.toNat := by
            simp only [Nat.reducePow, BitVec.reduceToNat] at hc
            rw [hcid_get] at hc; exact hc
          have hoff_e : ((4224 + 29 * mv + cid).setWidth 64).toNat =
              4224 + 29 * mv.toNat + cid.toNat :=
            fid_k6_off_add (mv := mv) (k := 29) (x := cid) hmv_hi (by decide) (by omega)
          have hoff_lt : ((4224 + 29 * mv + cid).setWidth 64).toNat < scra.length := by
            rw [hla, hoff_e]; omega
          let off := scra[((4224 + 29 * mv + cid).setWidth 64).toNat]'hoff_lt
          c0_hstraight
          refine wp_join0 (fun mb => ∃ scrb, FidK6BufOk scrb ∧
            FidSolveInv scr0 (scr0[4214]?.getD 0#32).toNat (scr0[4194]?.getD 0#32).toNat scrb ∧
            scrb[4193]? = some nc ∧ scrb[4207]? = some acap ∧
            (FullMem c (m8ScrFuelSt s s.core.fuel scrb) ⋆ R) mb) ?_ ?_
          · rintro _ mb h_pack; c0_hsteps!; exact hJ1 mb h_pack
          · intro J2 hJ2; c0_hstraight; c0_hsplit
            · have hoff_lt_acap : off.toNat < acap.toNat := by
                have hoff_idx : (4224 + 29 * mv.toNat + cid.toNat) % 4294967296 =
                    ((4224 + 29 * mv + cid).setWidth 64).toNat := by
                  rw [hoff_e]; omega
                have hoff_mod_lt : (4224 + 29 * mv.toNat + cid.toNat) % 4294967296 <
                    scra.length := by
                  rw [hoff_idx]; exact hoff_lt
                have hget : scra[(4224 + 29 * mv.toNat + cid.toNat) % 4294967296]'
                    hoff_mod_lt = off :=
                  fidSolve_get_congr hoff_mod_lt hoff_lt hoff_idx
                simp only [Nat.reducePow, BitVec.reduceToNat, hcid_get, hget] at hc
                exact hc
              have hoff_idx : (4224 + 29 * mv.toNat + cid.toNat) % 4294967296 =
                  ((4224 + 29 * mv + cid).setWidth 64).toNat := by
                rw [hoff_e]; omega
              have hoff_mod_lt : (4224 + 29 * mv.toNat + cid.toNat) % 4294967296 <
                  scra.length := by
                rw [hoff_idx]; exact hoff_lt
              have hoff_get : scra[(4224 + 29 * mv.toNat + cid.toNat) % 4294967296]'
                  hoff_mod_lt = off :=
                fidSolve_get_congr hoff_mod_lt hoff_lt hoff_idx
              have har_e : ((4224 + 45 * mv + off).setWidth 64).toNat =
                  4224 + 45 * mv.toNat + off.toNat :=
                fid_k6_off_add (mv := mv) (k := 45) (x := off) hmv_hi (by decide)
                  (by have := hok_in.length_lt; rw [hk_in.1] at this; omega)
              have har_lt : ((4224 + 45 * mv + off).setWidth 64).toNat < scra.length := by
                rw [hla, har_e]; omega
              let lit := scra[((4224 + 45 * mv + off).setWidth 64).toNat]'har_lt
              c0_hstraight
              refine wp_join0 (fun mb => ∃ scrb, FidK6BufOk scrb ∧
                FidSolveInv scr0 (scr0[4214]?.getD 0#32).toNat (scr0[4194]?.getD 0#32).toNat scrb ∧
                scrb[4193]? = some nc ∧ scrb[4207]? = some acap ∧
                (FullMem c (m8ScrFuelSt s s.core.fuel scrb) ⋆ R) mb) ?_ ?_
              · rintro _ mb h_pack; c0_hsteps!; exact hJ2 mb h_pack
              · intro J3 hJ3
                have h2nv : (nv <<< (1 : BitVec 32)).toNat = 2 * nv.toNat :=
                  fidSolve_shl1_toNat (by omega)
                c0_hstraight; c0_hsplit
                · have hlit_lt : lit.toNat < 2 * nv.toNat := by
                    have har_idx : (4224 + 45 * mv.toNat + off.toNat) % 4294967296 =
                        ((4224 + 45 * mv + off).setWidth 64).toNat := by
                      rw [har_e]; have := hoka.length_lt; rw [← hla] at hlen_scr; omega
                    have har_mod_lt : (4224 + 45 * mv.toNat + off.toNat) % 4294967296 <
                        scra.length := by
                      rw [har_idx]; exact har_lt
                    have hget : scra[(4224 + 45 * mv.toNat + off.toNat) % 4294967296]'
                        har_mod_lt = lit :=
                      fidSolve_get_congr har_mod_lt har_lt har_idx
                    simp only [Nat.reducePow, BitVec.reduceToNat, hcid_get, hoff_get, hget] at hc
                    have hc' : lit.toNat < nv.toNat * 2 % 4294967296 := hc
                    omega
                  have hv2_e : ((4224 + 9 * mv + lit).setWidth 64).toNat =
                      4224 + 9 * mv.toNat + lit.toNat :=
                    fid_k6_off_add (mv := mv) (k := 9) (x := lit) hmv_hi (by decide) (by omega)
                  have hv2_lt : ((4224 + 9 * mv + lit).setWidth 64).toNat < scra.length := by
                    rw [hla, hv2_e]; omega
                  have h4199_lt : 4199 < scra.length := by omega
                  c0_hstraight; c0_hsplit
                  · c0_hsteps!
                    let scrb := scra.set 4199 cid
                    have hokb := fidSolve_bufOk_set hoka 4199 cid (by decide) (by decide)
                      (by decide) (by decide) (by decide)
                    have hkb := fidSolveInv_set hka 4199 cid (by decide) (by decide) (by decide)
                    exact hQret 20#64 scrb _ hokb hkb hm
                  · c0_hstraight
                    refine wp_join0 (fun mb => ∃ scrb, FidK6BufOk scrb ∧
                      FidSolveInv scr0 (scr0[4214]?.getD 0#32).toNat
                        (scr0[4194]?.getD 0#32).toNat scrb ∧
                      scrb[4193]? = some nc ∧ scrb[4207]? = some acap ∧
                      (FullMem c (m8ScrFuelSt s s.core.fuel scrb) ⋆ R) mb) ?_ ?_
                    · rintro _ mb h_pack; c0_hsteps!; exact hJ3 mb h_pack
                    · intro J4 hJ4; c0_hstraight; c0_hsplit
                      · refine fidSolve_call_assign hAssign hlen hoka hscr_len hka hma ?_
                        intro scrb mb hokb hkb hlo _ hmb
                        have hncb : scrb[4193]? = some nc := by
                          rw [hlo 4193 (by decide) (by decide) (by decide)]; exact hnca
                        have hacapb : scrb[4207]? = some acap := by
                          rw [hlo 4207 (by decide) (by decide) (by decide)]; exact hacapa
                        c0_hsteps!; exact hJ4 mb ⟨scrb, hokb, hkb, hncb, hacapb, hmb⟩
                      · c0_hsteps!; exact hJ4 ma ⟨scra, hoka, hka, hnca, hacapa, hma⟩
                · c0_hsteps!; exact hJ3 ma ⟨scra, hoka, hka, hnca, hacapa, hma⟩
            · c0_hsteps!; exact hJ2 ma ⟨scra, hoka, hka, hnca, hacapa, hma⟩
        · c0_hsteps!; exact hJ1 ma ⟨scra, hoka, hka, hnca, hacapa, hma⟩
    · exact hCont scra ma hoka hka hma
  · intro L1 hL1; c0_hsteps!
    exact hL1 nuni.toNat (0#32, ()) m_in ⟨scr_in, hok_in, hk_in, hnc_s, hacap_s, by simp, rfl,
      hm_in⟩

/-! ## 3. Decision-Variable Picker (`fidSolvePickExpr` & `fidSolve_pick_wp`) -/

private def fidSolveScanHeapExpr (J_exit : Cont [i32, i32, i32])
    (pScr : BitVec 64) (mv nv miss start : BitVec 32) : Expr Val Cont [i64] :=
  let o_vals : BitVec 32 := 4224 + 2 * mv; let o_vals2 : BitVec 32 := 4224 + 9 * mv
  Expr.group (sig := [[i32, i32]]) (fun Js_h => Blocks.cons (fun p =>
   Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
               args := (Arg.var p.fst, Arg.var nv, ()) } fun p_a =>
   Expr.jnz (Arg.var p_a.fst)
    (Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                 args := (Arg.var p.snd.fst, Arg.var nv, ()) } fun p_b =>
     Expr.jnz (Arg.var p_b.fst)
      (Expr.let_ { sig := [i32, i32], code := OpCode.shl i32,
                   args := (Arg.var p.fst, Arg.imm 1, ()) } fun p_c =>
       fidScrOffPtr pScr o_vals2 p_c.fst fun p_d => Expr.load i32 (Arg.var p_d) fun ld_v =>
       Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool (by decide),
                   args := (Arg.var ld_v, Arg.imm 0, ()) } fun p_e =>
       Expr.jnz (Arg.var p_e.fst)
        (Expr.jump J_exit (Arg.var p.fst, Arg.var p.fst, Arg.var p.snd.fst, ()))
        (fidScrOffPtr pScr o_vals p.fst fun p_f => Expr.load i32 (Arg.var p_f) fun ld_nxt =>
         Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                     args := (Arg.var p.snd.fst, Arg.imm 1, ()) } fun p_g =>
         Expr.jump Js_h.fst (Arg.var ld_nxt, Arg.var p_g.fst, ())))
      (Expr.jump J_exit (Arg.var p.fst, Arg.var miss, Arg.var p.snd.fst, ())))
    (Expr.jump J_exit (Arg.var p.fst, Arg.var miss, Arg.var p.snd.fst, ())))
   Blocks.nil) fun Js => Expr.jump Js.fst (Arg.var start, Arg.imm 0, ())

private def fidSolvePickExpr (J_main : Cont [i32]) (pScr cHdr : BitVec 64)
    (mv nv cur0 : BitVec 32) : Expr Val Cont [i64] :=
  let o_ph : BitVec 32 := 4224 + 6 * mv; let o_vals2 : BitVec 32 := 4224 + 9 * mv
  Expr.group (sig := [[i32, i32, i32]]) (fun Js_1 => Blocks.cons (fun p_72 =>
   Expr.group (sig := [[i32, i32, i32]]) (fun Js_2 => Blocks.cons (fun p_73 =>
    Expr.group (sig := [[i32, i32]]) (fun Js_3 => Blocks.cons (fun p_74 =>
     Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool (by decide),
                 args := (Arg.var p_74.snd.fst, Arg.imm 4294967295, ()) } fun p_75 =>
     Expr.jnz (Arg.var p_75.fst) (Expr.ret (rs := [i64]) (Arg.imm 10, ()))
      (fidScrImmPtr pScr 4202 fun p_78 => Expr.store (Arg.var p_74.snd.fst) (Arg.var p_78)
       (fidScrOffPtr pScr o_ph p_74.snd.fst fun p_82 => Expr.load i32 (Arg.var p_82) fun ld_13 =>
        fidScrImmPtr pScr 4213 fun p_85 => Expr.load i32 (Arg.var p_85) fun ld_14 =>
        Expr.let_ { sig := [i32, i32], code := OpCode.xor i32,
                    args := (Arg.var ld_13, Arg.var ld_14, ()) } fun p_86 =>
        Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                    args := (Arg.var p_86.fst, Arg.imm 1, ()) } fun p_87 =>
        fidScrImmPtr pScr 4195 fun p_90 =>
        fidScrImmPtr pScr 4195 fun p_93 => Expr.load i32 (Arg.var p_93) fun ld =>
        Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                    args := (Arg.var ld, Arg.imm 1, ()) } fun p_94 =>
        Expr.store (Arg.var p_94.fst) (Arg.var p_90)
         (Expr.let_ { sig := [i32, i32], code := OpCode.shl i32,
                      args := (Arg.var p_74.snd.fst, Arg.imm 1, ()) } fun p_95 =>
          Expr.let_ { sig := [i32, i32], code := OpCode.or i32,
                      args := (Arg.var p_95.fst, Arg.var p_87.fst, ()) } fun p_96 =>
          Expr.call (as := [i64, i32, i32]) (bs := []) "full_k6_assign_fid"
            (Arg.var cHdr, Arg.var p_96.fst, Arg.imm 4294967295, PUnit.unit) fun _ =>
          Expr.call (as := [i64]) (bs := [i32]) "full_k6_prop_fid"
            (Arg.var cHdr, PUnit.unit) fun p => Expr.jump J_main (Arg.var p.fst, ())))))
    Blocks.nil) fun Js =>
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool (by decide),
                args := (Arg.var p_73.snd.fst, Arg.imm 4294967295, ()) } fun p =>
    Expr.jnz (Arg.var p.fst)
     (Expr.group (sig := [[i32, i32]]) (fun _ => Blocks.cons (fun p =>
       Expr.jump Js.fst (Arg.var p.fst, Arg.var p.snd.fst, ())) Blocks.nil) fun Js =>
      Expr.group (sig := [[i32]]) (fun Js_3 => Blocks.cons (fun p =>
       Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                   args := (Arg.var p.fst, Arg.var nv, ()) } fun p_74 =>
       Expr.jnz (Arg.var p_74.fst)
        (Expr.let_ { sig := [i32, i32], code := OpCode.shl i32,
                     args := (Arg.var p.fst, Arg.imm 1, ()) } fun p_75 =>
         fidScrOffPtr pScr o_vals2 p_75.fst fun p_79 => Expr.load i32 (Arg.var p_79) fun ld =>
         Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool (by decide),
                     args := (Arg.var ld, Arg.imm 0, ()) } fun p_80 =>
         Expr.jnz (Arg.var p_80.fst)
          (Expr.jump Js.fst (Arg.var p.fst, Arg.var p.fst, ()))
          (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                       args := (Arg.var p.fst, Arg.imm 1, ()) } fun p =>
           Expr.jump Js_3.fst (Arg.var p.fst, ())))
        (Expr.jump Js.fst (Arg.var p.fst, Arg.var p_73.snd.fst, ()))) Blocks.nil) fun Js =>
      Expr.jump Js.fst (Arg.imm 0, ()))
     (Expr.jump Js.fst (Arg.var p_73.fst, Arg.var p_73.snd.fst, ())))
   Blocks.nil) fun Js =>
   Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool (by decide),
               args := (Arg.var p_72.snd.fst, Arg.imm 4294967295, ()) } fun p =>
   Expr.jnz (Arg.var p.fst)
    (fidScrImmPtr pScr 4201 fun p => Expr.load i32 (Arg.var p) fun ld_13 =>
     Expr.group (sig := [[i32, i32, i32]]) (fun _ => Blocks.cons (fun p =>
      Expr.jump Js.fst (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p.snd.snd.fst, ()))
      Blocks.nil) fun Js => fidSolveScanHeapExpr Js.fst pScr mv nv p_72.snd.fst ld_13)
    (Expr.jump Js.fst (Arg.var p_72.fst, Arg.var p_72.snd.fst, Arg.var p_72.snd.snd.fst, ())))
  Blocks.nil) fun Js => fidSolveScanHeapExpr Js.fst pScr mv nv 4294967295 cur0

private theorem fidSolve_scan_heap_wp (Γ : Env) (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (Q : Post [i64]) (X : XPost) (J_exit : Cont [i32, i32, i32])
    (scr : List (BitVec 32)) (fl : BitVec 64) (mv nv miss start : BitVec 32) (m_in : Mem 64)
    (hmv_hi : mv.toNat ≤ 8192) (hnv_le : nv.toNat ≤ mv.toNat)
    (hlen : 4224 + 45 * mv.toNat ≤ scr.length)
    (hm : (FullMem c (m8ScrFuelSt s fl scr) ⋆ R) m_in)
    (hmiss : miss = 4294967295#32)
    (hJ : ∀ cur best cnt, (best ≠ 4294967295#32 → best.toNat < nv.toNat) →
      J_exit (cur, best, cnt, ()) m_in) :
    wp Γ Q X (fidSolveScanHeapExpr J_exit c.pScratchBuf mv nv miss start) m_in := by
  dsimp only [fidSolveScanHeapExpr, fidScrPtr, fidScrOffPtr]
  refine wp_loop_group (ts := [i32, i32])
    (fun rem (cur, cnt, ()) ma => cnt.toNat ≤ nv.toNat ∧ rem = nv.toNat - cnt.toNat ∧ ma = m_in)
    ?_ ?_
  · rintro Lh rem ⟨cur, cnt, ⟨⟩⟩ ma hLh ⟨hcnt_le, rfl, rfl⟩
    c0_hstraight; c0_hsplit
    · have hcur_lt : cur.toNat < nv.toNat := hc
      c0_hstraight; c0_hsplit
      · have hcnt_lt : cnt.toNat < nv.toNat := hc
        have hcnt1 : (cnt + 1#32).toNat = cnt.toNat + 1 :=
          m8_bv32_add1_toNat hcnt_lt (by omega)
        have h2c : (cur <<< 1#32).toNat = 2 * cur.toNat :=
          fidSolve_shl1_toNat (by omega)
        have hv2_e : ((4224 + 9 * mv + (cur <<< 1#32)).setWidth 64).toNat =
            4224 + 9 * mv.toNat + (cur <<< 1#32).toNat :=
          fid_k6_off_add (mv := mv) (k := 9) (x := cur <<< 1#32) hmv_hi (by decide)
            (by rw [h2c]; omega)
        have hv2_lt : ((4224 + 9 * mv + (cur <<< 1#32)).setWidth 64).toNat < scr.length := by
          rw [hv2_e, h2c]; omega
        c0_hstraight; c0_hsplit
        · c0_hsteps!; exact hJ cur cur cnt (fun _ => hcur_lt)
        · have hv_e : ((4224 + 2 * mv + cur).setWidth 64).toNat =
              4224 + 2 * mv.toNat + cur.toNat :=
            fid_k6_off_add (mv := mv) (k := 2) (x := cur) hmv_hi (by decide) (by omega)
          have hv_lt : ((4224 + 2 * mv + cur).setWidth 64).toNat < scr.length := by
            rw [hv_e]; omega
          c0_hsteps!
          exact hLh (nv.toNat - (cnt + 1#32).toNat) (_, cnt + 1#32, ()) _ (by omega)
            ⟨by omega, rfl, rfl⟩
      · c0_hsteps!; exact hJ cur miss cnt (fun h => (h hmiss).elim)
    · c0_hsteps!; exact hJ cur miss cnt (fun h => (h hmiss).elim)
  · intro Lh hLh; c0_hsteps!; exact hLh nv.toNat (start, 0#32, ()) m_in ⟨by simp, by simp, rfl⟩

private theorem fidSolve_pick_wp (Γ : Env) (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (Q : Post [i64]) (X : XPost) (J_main : Cont [i32]) (scr0 scra : List (BitVec 32))
    (fl : BitVec 64) (nv cur0 : BitVec 32) (ma : Mem 64)
    (hAssign : Γ.Has "full_k6_assign_fid" fidK6AssignSpec)
    (hProp : Γ.Has "full_k6_prop_fid" fidK6PropSpec)
    (hlen : FullState.LengthsOk c s) (hoka : FidK6BufOk scra)
    (hscr_len : scr0.length = c.scratch_cap) (h4214 : 4214 < scr0.length) :
    let mv := scr0[4214]'h4214
    nv.toNat ≤ mv.toNat → fl.toNat ≤ s.core.fuel.toNat →
    FidSolveInv scr0 (scr0[4214]?.getD 0#32).toNat (scr0[4194]?.getD 0#32).toNat scra →
    (FullMem c (m8ScrFuelSt s fl scra) ⋆ R) ma →
    (∀ (r : BitVec 64) (scrf : List (BitVec 32)) (mf : Mem 64),
      FidK6BufOk scrf →
      FidSolveInv scr0 (scr0[4214]?.getD 0#32).toNat (scr0[4194]?.getD 0#32).toNat scrf →
      (FullMem c (m8ScrFuelSt s fl scrf) ⋆ R) mf → Q (r, ()) mf) →
    (∀ confl scrb mb, FidK6BufOk scrb →
      FidSolveInv scr0 (scr0[4214]?.getD 0#32).toNat (scr0[4194]?.getD 0#32).toNat scrb →
      (FullMem c (m8ScrFuelSt s fl scrb) ⋆ R) mb → J_main (confl, ()) mb) →
    wp Γ Q X (fidSolvePickExpr J_main c.pScratchBuf c.hdr mv nv cur0) ma := by
  intro mv hnv_le hfl_le hka hma hQret hJmain
  have hmv_eq : scr0[4214]?.getD 0#32 = mv := m8_k6_get_eq h4214
  have hmv_s : scra[4214]?.getD 0#32 = mv := by rw [hka.2.2.2.1, hmv_eq]
  have hmv_hi : mv.toNat ≤ 8192 := by have := hoka.mv_hi; rwa [hmv_s] at this
  have hlen_scr : 4224 + 45 * mv.toNat ≤ scra.length := by
    have := hoka.length_ge; rw [hmv_s] at this; omega
  have h4201_lt : 4201 < scra.length := by omega
  have h4202_lt : 4202 < scra.length := by omega
  have h4213_lt : 4213 < scra.length := by omega
  have h4195_lt : 4195 < scra.length := by omega
  dsimp only [fidSolvePickExpr, fidScrPtr, fidScrOffPtr, fidScrImmPtr]
  refine wp_join_state_pure (ts := [i32, i32, i32])
    (fun st : BitVec 32 × BitVec 32 × BitVec 32 => (st.1, st.2.1, st.2.2, ()))
    (fun st => st.2.1 ≠ 4294967295#32 → st.2.1.toNat < nv.toNat) ?_ ?_
  · rintro _ ⟨cur1, best1, cnt1⟩ hbest1
    refine wp_join_state_pure (ts := [i32, i32, i32])
      (fun st : BitVec 32 × BitVec 32 × BitVec 32 => (st.1, st.2.1, st.2.2, ()))
      (fun st => st.2.1 ≠ 4294967295#32 → st.2.1.toNat < nv.toNat) ?_ ?_
    · rintro _ ⟨cur2, best2, cnt2⟩ hbest2
      refine wp_join_state_pure (ts := [i32, i32])
        (fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
        (fun st => st.2 ≠ 4294967295#32 → st.2.toNat < nv.toNat) ?_ ?_
      · rintro _ ⟨_, best⟩ hbest
        c0_hstraight; c0_hsplit
        · c0_hsteps!; exact hQret 10#64 scra ma hoka hka hma
        · have hbest_lt : best.toNat < nv.toNat := hbest hc
          have hph_e : ((4224 + 6 * mv + best).setWidth 64).toNat =
              4224 + 6 * mv.toNat + best.toNat :=
            fid_k6_off_add (mv := mv) (k := 6) (x := best) hmv_hi (by decide) (by omega)
          have hph_lt : ((4224 + 6 * mv + best).setWidth 64).toNat <
              (scra.set 4202 best).length := by
            simp; omega
          have h4213_lt1 : 4213 < (scra.set 4202 best).length := by simp; omega
          have h4195_lt1 : 4195 < (scra.set 4202 best).length := by simp; omega
          c0_hstraight
          let scrb := (scra.set 4202 best).set 4195
            (((scra.set 4202 best)[4195]'h4195_lt1) + 1#32)
          have hokb : FidK6BufOk scrb :=
            fidSolve_bufOk_set (fidSolve_bufOk_set hoka 4202 best (by decide) (by decide)
              (by decide) (by decide) (by decide)) 4195
              (((scra.set 4202 best)[4195]'h4195_lt1) + 1#32)
              (by decide) (by decide) (by decide) (by decide) (by decide)
          have hkb := fidSolveInv_set (fidSolveInv_set hka 4202 best (by decide)
            (by decide) (by decide)) 4195
            (((scra.set 4202 best)[4195]'h4195_lt1) + 1#32)
            (by decide) (by decide) (by decide)
          refine fidSolve_call_assign hAssign hlen hokb hscr_len hkb hm ?_
          intro scrc mc hokc hkc _ _ hmc
          refine fidSolve_call_prop hProp hlen hokc hscr_len hkc hmc ?_
          intro confl scrd md hokd hkd hmd
          c0_hsteps!; exact hJmain confl scrd md hokd hkd hmd
      · intro J3 hJ3; c0_hstraight; c0_hsplit
        · have hmiss : best2 = 4294967295#32 := hc
          refine wp_join_state_pure (ts := [i32, i32])
            (fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
            (fun st => st.2 ≠ 4294967295#32 → st.2.toNat < nv.toNat) ?_ ?_
          · rintro _ ⟨cur3, best3⟩ h3; c0_hsteps!; exact hJ3 (cur3, best3) h3
          · intro J3i hJ3i
            refine wp_loop_group (ts := [i32])
              (fun rem (cur, ()) m' => cur.toNat ≤ nv.toNat ∧ rem = nv.toNat - cur.toNat ∧
                m' = ma) ?_ ?_
            · rintro L3 rem3 ⟨cur, ⟨⟩⟩ m' hL3 ⟨hcur_le, rfl, rfl⟩
              c0_hstraight; c0_hsplit
              · have hcur_lt : cur.toNat < nv.toNat := hc
                have hcur1 : (cur + 1#32).toNat = cur.toNat + 1 :=
                  m8_bv32_add1_toNat hcur_lt (by omega)
                have h2c : (cur <<< 1#32).toNat = 2 * cur.toNat :=
                  fidSolve_shl1_toNat (by omega)
                have hv2_e : ((4224 + 9 * mv + (cur <<< 1#32)).setWidth 64).toNat =
                    4224 + 9 * mv.toNat + (cur <<< 1#32).toNat :=
                  fid_k6_off_add (mv := mv) (k := 9) (x := cur <<< 1#32) hmv_hi (by decide)
                    (by rw [h2c]; omega)
                have hv2_lt : ((4224 + 9 * mv + (cur <<< 1#32)).setWidth 64).toNat <
                    scra.length := by rw [hv2_e, h2c]; omega
                c0_hstraight; c0_hsplit
                · c0_hsteps!; exact hJ3i (cur, cur) (fun _ => hcur_lt)
                · c0_hsteps!
                  exact hL3 (nv.toNat - (cur + 1#32).toNat) (cur + 1#32, ()) _ (by omega)
                    ⟨by omega, rfl, rfl⟩
              · c0_hsteps!; exact hJ3i (cur, best2) (fun h => (h hmiss).elim)
            · intro L3 hL3; c0_hsteps!; exact hL3 nv.toNat (0#32, ()) ma ⟨by simp, by simp, rfl⟩
        · c0_hsteps!; exact hJ3 (cur2, best2) hbest2
    · intro J2 hJ2; c0_hstraight; c0_hsplit
      · have hmiss : best1 = 4294967295#32 := hc
        c0_hstraight
        refine wp_join_state_pure (ts := [i32, i32, i32])
          (fun st : BitVec 32 × BitVec 32 × BitVec 32 => (st.1, st.2.1, st.2.2, ()))
          (fun st => st.2.1 ≠ 4294967295#32 → st.2.1.toNat < nv.toNat) ?_ ?_
        · rintro _ ⟨cur2, best2, cnt2⟩ h2; c0_hsteps!; exact hJ2 (cur2, best2, cnt2) h2
        · intro J2i hJ2i
          exact fidSolve_scan_heap_wp Γ c s R Q X J2i scra fl mv nv best1
            (scra[4201]'h4201_lt) ma hmv_hi hnv_le hlen_scr hma hmiss
            (fun cur best cnt hb => by c0_hsteps!; exact hJ2i (cur, best, cnt) hb)
      · c0_hsteps!; exact hJ2 (cur1, best1, cnt1) hbest1
  · intro J1 hJ1
    exact fidSolve_scan_heap_wp Γ c s R Q X J1 scra fl mv nv 4294967295#32 cur0 ma
      hmv_hi hnv_le hlen_scr hma rfl
      (fun cur best cnt hb => by c0_hsteps!; exact hJ1 (cur, best, cnt) hb)

/-! ## 4. Main `full_k6_solve_fid_wp` -/

private theorem fidSolve_sub1_toNat {x : BitVec 64} (hx : 0 < x.toNat) :
    (x - 1).toNat = x.toNat - 1 := by
  have hle : (1 : BitVec 64) ≤ x := BitVec.le_def.mpr (by change 1 ≤ x.toNat; omega)
  calc
    (x - 1).toNat = x.toNat - (1 : BitVec 64).toNat := BitVec.toNat_sub_of_le hle
    _ = x.toNat - 1 := rfl

theorem full_k6_solve_fid_wp (Γ : Env)
    (hBt : Γ.Has "full_k6_backtrack_fid" fidK6BacktrackSpec)
    (hAssign : Γ.Has "full_k6_assign_fid" fidK6AssignSpec)
    (hProp : Γ.Has "full_k6_prop_fid" fidK6PropSpec)
    (hAna : Γ.Has "full_k6_analyze_fid" fidK6AnalyzeSpec) :
    ∀ (a : Tup Val [i64, i32]) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      fidK6SolveSpec a m Q X → Func.wp Γ full_k6_solve_fid_body a m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hok, hnc_le, hm, hK⟩
  change (FullMem c (m8ScrFuelSt s s.core.fuel s.scratch.scratch_buf) ⋆ R) m at hm
  dsimp only [Func.wp, full_k6_solve_fid_body]
  have hscr_len : s.scratch.scratch_buf.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have h4214 : 4214 < s.scratch.scratch_buf.length := by have := hok.base_ge; omega
  have h4199 : 4199 < s.scratch.scratch_buf.length := by omega
  have h4205 : 4205 < s.scratch.scratch_buf.length := by omega
  have h4204 : 4204 < s.scratch.scratch_buf.length := by omega
  have h4192 : 4192 < s.scratch.scratch_buf.length := by omega
  have h4193 : 4193 < s.scratch.scratch_buf.length := by omega
  have h4207 : 4207 < s.scratch.scratch_buf.length := by omega
  have h4211 : 4211 < s.scratch.scratch_buf.length := by omega
  have hmv_eq : s.scratch.scratch_buf[4214]?.getD 0#32 = s.scratch.scratch_buf[4214]'h4214 :=
    m8_k6_get_eq h4214
  have hmv_lo : 256 ≤ (s.scratch.scratch_buf[4214]'h4214).toNat := by
    have := hok.mv_lo; rwa [hmv_eq] at this
  have hmv_hi : (s.scratch.scratch_buf[4214]'h4214).toNat ≤ 8192 := by
    have := hok.mv_hi; rwa [hmv_eq] at this
  have hinv0 := fidSolveInv_refl s.scratch.scratch_buf hnc_le
  c0_hstraight; c0_hsplit
  · exfalso; change (s.scratch.scratch_buf[4214]'h4214).toNat < 256 at hc; omega
  · c0_hstraight; c0_hsplit
    · exfalso; change 8192 < (s.scratch.scratch_buf[4214]'h4214).toNat at hc; omega
    · c0_hstraight
      refine fidSolve_call_backtrack hBt hlen hok hscr_len hinv0 hm ?_
      intro scr1 m1 hok1 hinv1 hm1
      have hl1 : scr1.length = s.scratch.scratch_buf.length := hinv1.1
      c0_hstraight; c0_hsplit
      · c0_hsteps!
        exact fidSolve_final_post hscr_len hok1 hinv1 (Nat.le_refl _) hm1 hK 20#64
      · have h4205_1 : 4205 < scr1.length := by omega
        have h4204_1 : 4204 < (scr1.set 4205 tick_lim).length := by simp; omega
        have h4192_2 : 4192 < ((scr1.set 4205 tick_lim).set 4204 0#32).length := by simp; omega
        have h4193_2 : 4193 < ((scr1.set 4205 tick_lim).set 4204 0#32).length := by simp; omega
        have h4207_2 : 4207 < ((scr1.set 4205 tick_lim).set 4204 0#32).length := by simp; omega
        have h4211_2 : 4211 < ((scr1.set 4205 tick_lim).set 4204 0#32).length := by simp; omega
        c0_hstraight
        let scr2 := (scr1.set 4205 tick_lim).set 4204 0#32
        have hok2 : FidK6BufOk scr2 :=
          fidSolve_bufOk_set (fidSolve_bufOk_set hok1 4205 tick_lim (by decide) (by decide)
            (by decide) (by decide) (by decide)) 4204 0#32 (by decide) (by decide)
            (by decide) (by decide) (by decide)
        have hinv2 := fidSolveInv_set (fidSolveInv_set hinv1 4205 tick_lim (by decide)
          (by decide) (by decide)) 4204 0#32 (by decide) (by decide) (by decide)
        let nv := scr2[4192]'h4192_2; let nc := scr2[4193]'h4193_2
        let acap := scr2[4207]'h4207_2; let nuni := scr2[4211]'h4211_2
        have hmv2 : scr2[4214]? = s.scratch.scratch_buf[4214]? := by
          rw [hinv2.2.2.2.1]
        c0_hsplit
        · c0_hsteps!; exact fidSolve_final_post hscr_len hok2 hinv2 (Nat.le_refl _) hm hK 0#64
        · have hnv_le : nv.toNat ≤ (s.scratch.scratch_buf[4214]'h4214).toNat := by
            have hc' : ¬(s.scratch.scratch_buf[4214]'h4214).toNat < nv.toNat := hc
            omega
          c0_hstraight; c0_hsplit
          · c0_hsteps!; exact fidSolve_final_post hscr_len hok2 hinv2 (Nat.le_refl _) hm hK 0#64
          · have hnc_le4 : nc.toNat ≤ 4 * (s.scratch.scratch_buf[4214]'h4214).toNat := by
              have hc' :
                  ¬((s.scratch.scratch_buf[4214]'h4214).toNat * 2 ^ 2) % 2 ^ 32 < nc.toNat :=
                hc
              omega
            c0_hstraight; c0_hsplit
            · c0_hsteps!; exact fidSolve_final_post hscr_len hok2 hinv2 (Nat.le_refl _) hm hK 0#64
            · have hnuni_le : nuni.toNat ≤ 2 * (s.scratch.scratch_buf[4214]'h4214).toNat := by
                have hc' :
                    ¬((s.scratch.scratch_buf[4214]'h4214).toNat * 2 ^ 1) % 2 ^ 32 < nuni.toNat :=
                  hc
                omega
              have hnc2 : scr2[4193]? = some nc := List.getElem?_eq_getElem h4193_2
              have hac2 : scr2[4207]? = some acap := List.getElem?_eq_getElem h4207_2
              c0_hstraight
              refine fidSolve_unit_loop_wp Γ c s R Q X s.scratch.scratch_buf scr2
                nv nc acap nuni _ _ hAssign hlen hok2 hscr_len h4214 h4193 h4207
                hnv_le hnc_le4 hnuni_le hmv2 hnc2 hac2 hinv2 hm
                (fun r scrc mc hokc hkc hmc => fidSolve_final_post hscr_len hokc hkc
                  (Nat.le_refl _) hmc hK r) ?_
              intro scr3 m3 hok3 hinv3 hm3
              refine fidSolve_call_prop hProp hlen hok3 hscr_len hinv3 hm3 ?_
              intro confl0 scr4 m4 hok4 hinv4 hm4
              c0_hstraight; c0_hsplit
              · have hl4 : scr4.length = s.scratch.scratch_buf.length := hinv4.1
                have h4199_4 : 4199 < scr4.length := by omega
                c0_hsteps!
                let scr5 := scr4.set 4199 confl0
                have hok5 := fidSolve_bufOk_set hok4 4199 confl0 (by decide) (by decide)
                  (by decide) (by decide) (by decide)
                have hinv5 := fidSolveInv_set hinv4 4199 confl0 (by decide) (by decide)
                  (by decide)
                exact fidSolve_final_post hscr_len hok5 hinv5 (Nat.le_refl _) hm hK 20#64
              · refine wp_loop_group (ts := [i32])
                  (fun rem (confl, ()) ma => ∃ fl scra,
                    FidK6BufOk scra ∧
                    FidSolveInv s.scratch.scratch_buf (s.scratch.scratch_buf[4214]?.getD 0#32).toNat
                      (s.scratch.scratch_buf[4194]?.getD 0#32).toNat scra ∧
                    fl.toNat ≤ s.core.fuel.toNat ∧ rem = fl.toNat ∧
                    (FullMem c (m8ScrFuelSt s fl scra) ⋆ R) ma) ?_ ?_
                · rintro Jmain rem1 ⟨confl, ⟨⟩⟩ ma hJmain
                    ⟨fl, scra, hoka, hka, hfl_le, rfl, hma⟩
                  have hla : scra.length = s.scratch.scratch_buf.length := hka.1
                  have h4204_a : 4204 < scra.length := by omega
                  have h4205_a : 4205 < scra.length := by omega
                  have h4195_a : 4195 < scra.length := by omega
                  have h4198_a : 4198 < scra.length := by omega
                  have h4199_a : 4199 < scra.length := by omega
                  have h4202_a : 4202 < scra.length := by omega
                  c0_hstraight; c0_hsplit
                  · c0_hstraight; c0_hsplit
                    · have hfl_pos : 0 < fl.toNat := hc
                      have hfl1 : (fl - 1).toNat = fl.toNat - 1 := fidSolve_sub1_toNat hfl_pos
                      c0_hstraight; c0_hsplit
                      · c0_hstraight; c0_hsplit
                        · c0_hsteps!
                          let scrb := scra.set 4199 confl
                          have hokb := fidSolve_bufOk_set hoka 4199 confl (by decide) (by decide)
                            (by decide) (by decide) (by decide)
                          have hkb := fidSolveInv_set hka 4199 confl (by decide) (by decide)
                            (by decide)
                          exact fidSolve_final_post hscr_len hokb hkb
                            (by rw [hfl1]; omega) hm hK 20#64
                        · refine fidSolve_call_analyze hAna hlen hoka hscr_len hka hm ?_
                          intro ok scrb mb hokb hkb hmb
                          c0_hstraight; c0_hsplit
                          · refine fidSolve_call_prop hProp hlen hokb hscr_len hkb hmb ?_
                            intro confl' scrc mc hokc hkc hmc
                            c0_hsteps!
                            exact hJmain (fl.toNat - 1) (confl', ()) mc (by omega)
                              ⟨fl - 1, scrc, hokc, hkc, by rw [hfl1]; omega, hfl1.symm, hmc⟩
                          · c0_hsteps!
                            exact fidSolve_final_post hscr_len hokb hkb
                              (by rw [hfl1]; omega) hmb hK 0#64
                      · c0_hstraight; c0_hsplit
                        · c0_hsteps!
                          exact fidSolve_final_post hscr_len hoka hka
                            (by rw [hfl1]; omega) hm hK 10#64
                        · c0_hstraight
                          refine fidSolve_pick_wp Γ c s R Q X Jmain s.scratch.scratch_buf scra
                            (fl - 1) nv (scra[4202]'h4202_a) _ hAssign hProp hlen hoka
                            hscr_len h4214 hnv_le (by rw [hfl1]; omega) hka hm
                            (fun r scrf mf hokf hkf hmf => fidSolve_final_post hscr_len hokf hkf
                              (by rw [hfl1]; omega) hmf hK r) ?_
                          intro confl' scrb mb hokb hkb hmb
                          exact hJmain (fl.toNat - 1) (confl', ()) mb (by omega)
                            ⟨fl - 1, scrb, hokb, hkb, by rw [hfl1]; omega, hfl1.symm, hmb⟩
                    · c0_hsteps!
                      exact fidSolve_final_post hscr_len hoka hka hfl_le hma hK 0#64
                  · c0_hsteps!
                    exact fidSolve_final_post hscr_len hoka hka hfl_le hma hK 0#64
                · intro Jmain hJmain; c0_hsteps!
                  exact hJmain s.core.fuel.toNat (confl0, ()) m4
                    ⟨s.core.fuel, scr4, hok4, hinv4, Nat.le_refl _, rfl, hm4⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Definition
