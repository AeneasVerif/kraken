/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpFidBasic

/-!
# Kissat Fidelity BVE WP Proofs — `core` Invariants & Traceback Helper

Shared `FidCoreInv`, arithmetic/index bounds lemmas, and the extracted trail-traceback +
flag-clearing helper `fidCore_phase2_trace_wp` for `full_k6_core_fid_wp` (`0` legacy `Full*`
imports; zero `@[expose]` on theorems; every decl `<= 450` LOC; `<= 100` cols).
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

/-! ## 1. `FidCoreInv` & Framing Lemmas -/

/-- Loop invariant for `full_k6_core_fid`: preserves `FidK6BufOk`, everything outside
`o_flags` and `o_cl_meta`, and the low 16 bits + `KM_LRN` bit of `o_cl_meta[0..nc)`. -/
@[expose] def FidCoreInv (scr0 : List (BitVec 32)) (mv nc : BitVec 32)
    (scr : List (BitVec 32)) : Prop :=
  FidK6BufOk scr ∧ scr.length = scr0.length ∧
  (∀ idx < scr0.length,
    (idx < 4224 + 6 * mv.toNat ∨
      (4224 + 7 * mv.toNat ≤ idx ∧ idx < 4224 + 33 * mv.toNat) ∨
      4224 + 37 * mv.toNat ≤ idx) →
    scr[idx]? = scr0[idx]?) ∧
  (∀ cid < nc.toNat,
    let m0 := scr0[4224 + 33 * mv.toNat + cid]?.getD 0#32
    let m1 := scr[4224 + 33 * mv.toNat + cid]?.getD 0#32
    (m1 &&& 0xFFFF#32) = (m0 &&& 0xFFFF#32) ∧
    (m1 &&& 0x40000000#32) = (m0 &&& 0x40000000#32))

theorem fidCoreInv_mv {scr0 scr : List (BitVec 32)} {mv nc : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (h : FidCoreInv scr0 mv nc scr) : scr[4214]?.getD 0#32 = mv := by
  have hk := h.2.2.1 4214 h4214 (Or.inl (by omega))
  rw [hk, hmv_eq]

theorem fidCoreInv_set_meta {scr0 : List (BitVec 32)} {mv nc : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (hnc_le : nc.toNat ≤ 4 * mv.toNat) {scr : List (BitVec 32)} (hik : FidCoreInv scr0 mv nc scr)
    {cid : Nat} (hcid : cid < nc.toNat) {v : BitVec 32}
    (hsz : (v &&& 0xFFFF#32) = ((scr[4224 + 33 * mv.toNat + cid]?.getD 0#32) &&& 0xFFFF#32))
    (hlrn : (v &&& 0x40000000#32) =
      ((scr[4224 + 33 * mv.toNat + cid]?.getD 0#32) &&& 0x40000000#32)) :
    FidCoreInv scr0 mv nc (scr.set (4224 + 33 * mv.toNat + cid) v) := by
  have hmv' := fidCoreInv_mv h4214 hmv_eq hik
  have hb := hik.1.base_ge; rw [hmv'] at hb
  have hok' : FidK6BufOk (scr.set (4224 + 33 * mv.toNat + cid) v) := by
    have h1 := fidK6BufOk_set_core_meta hik.1 (cid := cid) (v := v)
      (by rw [hmv']; omega) (by rw [hmv']; exact hsz) (by rw [hmv']; exact hlrn)
    rwa [hmv'] at h1
  refine ⟨hok', by simp [hik.2.1], fun idx hi hor => ?_, fun j hj => ?_⟩
  · rw [List.getElem?_set_ne (by fid_ne)]; exact hik.2.2.1 idx hi hor
  · by_cases heq : j = cid
    · subst heq
      dsimp only
      rw [List.getElem?_set_self (by omega), Option.getD_some, hsz, hlrn]
      exact hik.2.2.2 j hj
    · rw [List.getElem?_set_ne (by fid_ne)]; exact hik.2.2.2 j hj

theorem fidCoreInv_set_flags {scr0 : List (BitVec 32)} {mv nc : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    {scr : List (BitVec 32)} (hik : FidCoreInv scr0 mv nc scr)
    {v : Nat} (hv : v < mv.toNat) (val : BitVec 32) :
    FidCoreInv scr0 mv nc (scr.set (4224 + 6 * mv.toNat + v) val) := by
  have hmv' := fidCoreInv_mv h4214 hmv_eq hik
  have hok' : FidK6BufOk (scr.set (4224 + 6 * mv.toNat + v) val) := by
    have h1 := fidK6BufOk_set_flags hik.1 (i := v) (by rw [hmv']; exact hv) val
    rwa [hmv'] at h1
  refine ⟨hok', by simp [hik.2.1], fun idx hi hor => ?_, fun j hj => ?_⟩
  · rw [List.getElem?_set_ne (by fid_ne)]; exact hik.2.2.1 idx hi hor
  · rw [List.getElem?_set_ne (by fid_ne)]; exact hik.2.2.2 j hj

theorem fidCoreInv_set_meta_pres {scr0 scr : List (BitVec 32)} {mv nc : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (hnc_le : nc.toNat ≤ 4 * mv.toNat) (hik : FidCoreInv scr0 mv nc scr)
    {cid : BitVec 32} (hcid : cid.toNat < nc.toNat) {v : BitVec 32}
    (he : ((4224 + 33 * mv + cid).setWidth 64).toNat = 4224 + 33 * mv.toNat + cid.toNat)
    (hlt : ((4224 + 33 * mv + cid).setWidth 64).toNat < scr.length)
    (hpres : (v &&& 0xFFFF#32) =
        ((scr[((4224 + 33 * mv + cid).setWidth 64).toNat]'hlt) &&& 0xFFFF#32) ∧
      (v &&& 0x40000000#32) =
        ((scr[((4224 + 33 * mv + cid).setWidth 64).toNat]'hlt) &&& 0x40000000#32)) :
    FidCoreInv scr0 mv nc (scr.set ((4224 + 33 * mv + cid).setWidth 64).toNat v) := by
  have hll := hik.2.1
  have h1 := fidCoreInv_set_meta h4214 hmv_eq hnc_le hik hcid (v := v)
    (by rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
        m8_k6_get_congr he.symm (by omega) hlt]; exact hpres.1)
    (by rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
        m8_k6_get_congr he.symm (by omega) hlt]; exact hpres.2)
  simpa only [he] using h1

theorem fidCoreInv_set_flags_e {scr0 scr : List (BitVec 32)} {mv nc : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (hik : FidCoreInv scr0 mv nc scr) {v : BitVec 32} (hv : v.toNat < mv.toNat)
    (he : ((4224 + 6 * mv + v).setWidth 64).toNat = 4224 + 6 * mv.toNat + v.toNat)
    (val : BitVec 32) :
    FidCoreInv scr0 mv nc (scr.set ((4224 + 6 * mv + v).setWidth 64).toNat val) := by
  simpa only [he] using fidCoreInv_set_flags h4214 hmv_eq hik hv val

/-! ## 2. Arithmetic & Clause Bounds Helpers -/

private theorem fidCore_ne45_aux {m v ti : Nat} (hm : m ≤ 8192) (hv : v < m) (hti : ti ≤ m) :
    (4224 + 6 * m + v) % 4294967296 ≠ (4224 + m + v) % 4294967296 ∧
    4224 + m + v < 4294967296 ∧ 4224 + 6 * m + v ≠ 4224 + m + v ∧
    4224 + 5 * m + (ti - 1) < 4294967296 := by
  have h1 : 4224 + 6 * m + v < 4294967296 := by omega
  have h2 : 4224 + m + v < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
  exact ⟨Nat.ne_of_gt (by omega), h2, Nat.ne_of_gt (by omega), by omega⟩

private theorem fidCore_scrt2_rsz_lt {xs : List (BitVec 32)} {idx : Nat} {hb1 hb2}
    {mr rsz j : BitVec 32} (hmr : xs[idx]'hb1 = mr)
    (hrsz : (mr ||| 0x80000000#32) &&& 0xFFFF#32 = rsz)
    (hc : j.toNat <
      ((xs.set idx (xs[idx]'hb1 ||| 2147483648#32))[idx]'hb2).toNat % 65536) :
    j.toNat < rsz.toNat := by
  have h1 : (xs.set idx (xs[idx]'hb1 ||| 2147483648#32))[idx]'hb2 = mr ||| 0x80000000#32 := by
    rw [List.getElem_set_self, hmr]
  rw [h1, ← FidK6Tactics.fid_bv32_and_ffff_toNat, hrsz] at hc
  exact hc

private abbrev ftTi (scr0 : List (BitVec 32)) (h4214 : 4214 < scr0.length) (ti : BitVec 32) :
    Nat :=
  (4224 + 5 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + ti.toNat)) % 4294967296

private abbrev ftFl (scr0 scrt : List (BitVec 32)) (h4214 : 4214 < scr0.length)
    (ti : BitVec 32) (hb0 : ftTi scr0 h4214 ti < scrt.length) : Nat :=
  (4224 + 6 * (scr0[4214]'h4214).toNat +
    (scrt[ftTi scr0 h4214 ti]'hb0).toNat / 2) % 4294967296

private abbrev ftS1 (scr0 scrt : List (BitVec 32)) (h4214 : 4214 < scr0.length)
    (ti : BitVec 32) (hb0 : ftTi scr0 h4214 ti < scrt.length)
    (hb1 : ftFl scr0 scrt h4214 ti hb0 < scrt.length) : List (BitVec 32) :=
  scrt.set (ftFl scr0 scrt h4214 ti hb0) (scrt[ftFl scr0 scrt h4214 ti hb0]'hb1 &&& ~~~2#32)

private abbrev ftRs (scr0 scrt : List (BitVec 32)) (h4214 : 4214 < scr0.length)
    (ti : BitVec 32) (hb0 : ftTi scr0 h4214 ti < scrt.length) : Nat :=
  (4224 + (scr0[4214]'h4214).toNat + (scrt[ftTi scr0 h4214 ti]'hb0).toNat / 2) % 4294967296

private abbrev ftMr (scr0 scrt : List (BitVec 32)) (h4214 : 4214 < scr0.length)
    (ti : BitVec 32) (hb0 : ftTi scr0 h4214 ti < scrt.length)
    (hb1 : ftFl scr0 scrt h4214 ti hb0 < scrt.length)
    (hb_r : ftRs scr0 scrt h4214 ti hb0 < (ftS1 scr0 scrt h4214 ti hb0 hb1).length) : Nat :=
  (4224 + 33 * (scr0[4214]'h4214).toNat +
    ((ftS1 scr0 scrt h4214 ti hb0 hb1)[ftRs scr0 scrt h4214 ti hb0]'hb_r).toNat) % 4294967296

private abbrev ftS2 (scr0 scrt : List (BitVec 32)) (h4214 : 4214 < scr0.length)
    (ti : BitVec 32) (hb0 : ftTi scr0 h4214 ti < scrt.length)
    (hb1 : ftFl scr0 scrt h4214 ti hb0 < scrt.length)
    (hb_k hb_v : ftRs scr0 scrt h4214 ti hb0 < (ftS1 scr0 scrt h4214 ti hb0 hb1).length)
    (hb4 : ftMr scr0 scrt h4214 ti hb0 hb1 hb_v < (ftS1 scr0 scrt h4214 ti hb0 hb1).length) :
    List (BitVec 32) :=
  let s1 := ftS1 scr0 scrt h4214 ti hb0 hb1
  s1.set (ftMr scr0 scrt h4214 ti hb0 hb1 hb_k)
    (s1[ftMr scr0 scrt h4214 ti hb0 hb1 hb_v]'hb4 ||| 2147483648#32)

private theorem fidCore_trace_hj_lt {scr0 scrt : List (BitVec 32)}
    {mv ti ti' v rsn mr rsz j : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv)
    (hmv_hi : mv.toNat ≤ 8192) (_hlt : scrt.length = scr0.length)
    (hti_pos : 0 < ti.toNat) (hti_le : ti.toNat ≤ mv.toNat) (hti1 : ti'.toNat = ti.toNat - 1)
    (htr_e : ((4224 + 5 * mv + ti').setWidth 64).toNat = 4224 + 5 * mv.toNat + ti'.toNat)
    (htr_b : ((4224 + 5 * mv + ti').setWidth 64).toNat < scrt.length)
    (hv_eq : (scrt[((4224 + 5 * mv + ti').setWidth 64).toNat]'htr_b).toNat / 2 = v.toNat)
    (hv_lt : v.toNat < mv.toNat)
    (hfl_e : ((4224 + 6 * mv + v).setWidth 64).toNat = 4224 + 6 * mv.toNat + v.toNat)
    (hfl_b : ((4224 + 6 * mv + v).setWidth 64).toNat < scrt.length)
    (hrs_e : ((4224 + mv + v).setWidth 64).toNat = 4224 + mv.toNat + v.toNat)
    (hrs_b : ((4224 + mv + v).setWidth 64).toNat <
      (scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat
        (scrt[((4224 + 6 * mv + v).setWidth 64).toNat]'hfl_b &&& ~~~2#32)).length)
    (hrsn : (scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat
      (scrt[((4224 + 6 * mv + v).setWidth 64).toNat]'hfl_b &&& ~~~2#32))[
        ((4224 + mv + v).setWidth 64).toNat]'hrs_b = rsn)
    (hrsn_lt : rsn.toNat < 4 * mv.toNat)
    (hmr_e : ((4224 + 33 * mv + rsn).setWidth 64).toNat = 4224 + 33 * mv.toNat + rsn.toNat)
    (hmr_b : ((4224 + 33 * mv + rsn).setWidth 64).toNat <
      (scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat
        (scrt[((4224 + 6 * mv + v).setWidth 64).toNat]'hfl_b &&& ~~~2#32)).length)
    (hmr_d : (scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat
      (scrt[((4224 + 6 * mv + v).setWidth 64).toNat]'hfl_b &&& ~~~2#32))[
        ((4224 + 33 * mv + rsn).setWidth 64).toNat]'hmr_b = mr)
    (hrsz : ((mr ||| 0x80000000#32) &&& 0xFFFF#32) = rsz)
    {hb0 hb1 hb2 hb3 hb4 hb5 hb6}
    (hc : j.toNat < ((ftS2 scr0 scrt h4214 ti hb0 hb1 hb2 hb3 hb4)[
      (4224 + 33 * (scr0[4214]'h4214).toNat +
        ((ftS1 scr0 scrt h4214 ti hb0 hb1)[ftRs scr0 scrt h4214 ti hb0]'hb5).toNat) %
      4294967296]'hb6).toNat % 65536) :
    j.toNat < rsz.toNat := by
  have hti_u : 4224 + 5 * mv.toNat + (ti.toNat - 1) < 4294967296 := by
    clear hc hmr_d hrsn hmr_b hrs_b hv_eq htr_b hfl_b; omega
  have hfl_u : 4224 + 6 * mv.toNat + v.toNat < 4294967296 := by
    clear hc hmr_d hrsn hmr_b hrs_b hv_eq htr_b hfl_b; omega
  have hrs_u : 4224 + mv.toNat + v.toNat < 4294967296 := by
    clear hc hmr_d hrsn hmr_b hrs_b hv_eq htr_b hfl_b; omega
  have hmr_u : 4224 + 33 * mv.toNat + rsn.toNat < 4294967296 := by
    clear hc hmr_d hrsn hmr_b hrs_b hv_eq htr_b hfl_b; omega
  have htr1 : ftTi scr0 h4214 ti = ((4224 + 5 * mv + ti').setWidth 64).toNat := by
    dsimp only [ftTi]; rw [htr_e, hmv_d, fid_sub1_mod32 _ _ hti_pos hti_u, hti1]
  have hv_g : (scrt[ftTi scr0 h4214 ti]'hb0).toNat / 2 = v.toNat := by
    rw [m8_k6_get_congr htr1 hb0 htr_b, hv_eq]
  have hfl1 : ftFl scr0 scrt h4214 ti hb0 = ((4224 + 6 * mv + v).setWidth 64).toNat := by
    dsimp only [ftFl]; rw [hv_g, hmv_d, hfl_e, Nat.mod_eq_of_lt hfl_u]
  have hrs1 : ftRs scr0 scrt h4214 ti hb0 = ((4224 + mv + v).setWidth 64).toNat := by
    dsimp only [ftRs]; rw [hv_g, hmv_d, hrs_e, Nat.mod_eq_of_lt hrs_u]
  have hne_fl_rs :
      ((4224 + 6 * mv + v).setWidth 64).toNat ≠ ((4224 + mv + v).setWidth 64).toNat := by
    rw [hfl_e, hrs_e]
    clear hc hmr_d hrsn hmr_b hrs_b hv_eq hv_g htr_b hfl_b htr1 hfl1 hrs1; omega
  have hne_fl_mr :
      ((4224 + 6 * mv + v).setWidth 64).toNat ≠ ((4224 + 33 * mv + rsn).setWidth 64).toNat := by
    rw [hfl_e, hmr_e]
    clear hc hmr_d hrsn hmr_b hrs_b hv_eq hv_g htr_b hfl_b htr1 hfl1 hrs1; omega
  have h_rsn : ∀ {w : BitVec 32} {hb_r}, (scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat w)[
      ((4224 + mv + v).setWidth 64).toNat]'hb_r = rsn := by
    intro w hb_r
    rw [← Option.some_inj, ← List.getElem?_eq_getElem, List.getElem?_set_ne hne_fl_rs, ← hrsn,
      ← List.getElem?_eq_getElem, List.getElem?_set_ne hne_fl_rs]
  have hset1 : ftS1 scr0 scrt h4214 ti hb0 hb1 = scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat
      (scrt[((4224 + 6 * mv + v).setWidth 64).toNat]'hfl_b &&& ~~~2#32) := by
    simp only [ftS1, hfl1]
  have hinner : ∀ {hb_r},
      (ftS1 scr0 scrt h4214 ti hb0 hb1)[ftRs scr0 scrt h4214 ti hb0]'hb_r = rsn := by
    intro hb_r
    rw [← Option.some_inj, ← List.getElem?_eq_getElem, hset1, hrs1, ← hrsn,
      ← List.getElem?_eq_getElem]
  refine fidCore_scrt2_rsz_lt (mr := mr) ?_ hrsz hc
  dsimp only [ftS2, ftMr]
  rw [← Option.some_inj, ← List.getElem?_eq_getElem, hinner, hset1, hmv_d,
    Nat.mod_eq_of_lt hmr_u, ← hmr_e, List.getElem?_set_ne hne_fl_mr, ← hmr_d,
    ← List.getElem?_eq_getElem, List.getElem?_set_ne hne_fl_mr]

private theorem fidCore_trace_lv_aux {scr0 scr_raw scrt1 scrt2 scrj : List (BitVec 32)}
    {mv rsn mr roff j nv : BitVec 32} {rsn_a rsn_b rsn_c : Nat}
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv)
    (h4192 : 4192 < scr0.length) (hnv_d : scr0[4192]'h4192 = nv)
    (hset_eq : scr_raw = scrt1)
    (hra : rsn_a = rsn.toNat) (hrb : rsn_b = rsn.toNat) (hrc : rsn_c = rsn.toNat)
    (hmr_u : 4224 + 33 * mv.toNat + rsn.toNat < 4294967296)
    (hor_u : 4224 + 29 * mv.toNat + rsn.toNat < 4294967296)
    (har_u : 4224 + 45 * mv.toNat + roff.toNat + j.toNat < 4294967296)
    (hmr_e : ((4224 + 33 * mv + rsn).setWidth 64).toNat = 4224 + 33 * mv.toNat + rsn.toNat)
    (hmr_b : ((4224 + 33 * mv + rsn).setWidth 64).toNat < scrt1.length)
    (hmr_d : scrt1[((4224 + 33 * mv + rsn).setWidth 64).toNat]'hmr_b = mr)
    (hscrt2 : scrt2 = scrt1.set ((4224 + 33 * mv + rsn).setWidth 64).toNat (mr ||| 0x80000000#32))
    (hor_e : ((4224 + 29 * mv + rsn).setWidth 64).toNat = 4224 + 29 * mv.toNat + rsn.toNat)
    (hor_b2 : ((4224 + 29 * mv + rsn).setWidth 64).toNat < scrt2.length)
    (hroff_d : scrt2[((4224 + 29 * mv + rsn).setWidth 64).toNat]'hor_b2 = roff)
    (har_e : ((4224 + 45 * mv + roff + j).setWidth 64).toNat =
      4224 + 45 * mv.toNat + roff.toNat + j.toNat)
    (har_b : ((4224 + 45 * mv + roff + j).setWidth 64).toNat < scrj.length)
    {hb4 : (4224 + 33 * (scr0[4214]'h4214).toNat + rsn_b) % 4294967296 < scr_raw.length}
    {hb6 : (4224 + 29 * (scr0[4214]'h4214).toNat + rsn_c) % 4294967296 <
      (scr_raw.set ((4224 + 33 * (scr0[4214]'h4214).toNat + rsn_a) % 4294967296)
        (scr_raw[(4224 + 33 * (scr0[4214]'h4214).toNat + rsn_b) % 4294967296]'hb4 |||
          2147483648#32)).length}
    {hb7 : (4224 + 45 * (scr0[4214]'h4214).toNat +
      ((scr_raw.set ((4224 + 33 * (scr0[4214]'h4214).toNat + rsn_a) % 4294967296)
        (scr_raw[(4224 + 33 * (scr0[4214]'h4214).toNat + rsn_b) % 4294967296]'hb4 |||
          2147483648#32))[(4224 + 29 * (scr0[4214]'h4214).toNat + rsn_c) %
        4294967296]'hb6).toNat + j.toNat) % 4294967296 < scrj.length}
    (hc : (scrj[(4224 + 45 * (scr0[4214]'h4214).toNat +
      ((scr_raw.set ((4224 + 33 * (scr0[4214]'h4214).toNat + rsn_a) % 4294967296)
        (scr_raw[(4224 + 33 * (scr0[4214]'h4214).toNat + rsn_b) % 4294967296]'hb4 |||
          2147483648#32))[(4224 + 29 * (scr0[4214]'h4214).toNat + rsn_c) %
        4294967296]'hb6).toNat + j.toNat) % 4294967296]'hb7).toNat / 2 <
      (scr0[4192]'h4192).toNat) :
    ((scrj[((4224 + 45 * mv + roff + j).setWidth 64).toNat]'har_b) >>> (1 : Nat)).toNat <
      nv.toNat := by
  subst hset_eq; subst hra; subst hrb; subst hrc
  have hmr_i : (4224 + 33 * (scr0[4214]'h4214).toNat + rsn.toNat) % 4294967296 =
      ((4224 + 33 * mv + rsn).setWidth 64).toNat := by
    rw [hmv_d, hmr_e, Nat.mod_eq_of_lt hmr_u]
  have hmr_g :
      scr_raw[(4224 + 33 * (scr0[4214]'h4214).toNat + rsn.toNat) % 4294967296]'hb4 = mr := by
    rw [m8_k6_get_congr hmr_i hb4 hmr_b, hmr_d]
  have hor_i : (4224 + 29 * (scr0[4214]'h4214).toNat + rsn.toNat) % 4294967296 =
      ((4224 + 29 * mv + rsn).setWidth 64).toNat := by
    rw [hmv_d, hor_e, Nat.mod_eq_of_lt hor_u]
  have hset2 :
      scr_raw.set ((4224 + 33 * (scr0[4214]'h4214).toNat + rsn.toNat) % 4294967296)
          (scr_raw[(4224 + 33 * (scr0[4214]'h4214).toNat + rsn.toNat) % 4294967296]'hb4 |||
            2147483648#32) =
        scrt2 := by
    rw [hmr_g, hmr_i]; exact hscrt2.symm
  have hroff_g :
      (scr_raw.set ((4224 + 33 * (scr0[4214]'h4214).toNat + rsn.toNat) % 4294967296)
        (scr_raw[(4224 + 33 * (scr0[4214]'h4214).toNat + rsn.toNat) % 4294967296]'hb4 |||
          2147483648#32))[(4224 + 29 * (scr0[4214]'h4214).toNat + rsn.toNat) %
        4294967296]'hb6 = roff := by
    rw [← Option.some_inj, ← List.getElem?_eq_getElem, hset2, hor_i, ← hroff_d,
      ← List.getElem?_eq_getElem]
  have har_i :
      (4224 + 45 * (scr0[4214]'h4214).toNat +
        ((scr_raw.set ((4224 + 33 * (scr0[4214]'h4214).toNat + rsn.toNat) % 4294967296)
          (scr_raw[(4224 + 33 * (scr0[4214]'h4214).toNat + rsn.toNat) % 4294967296]'hb4 |||
            2147483648#32))[(4224 + 29 * (scr0[4214]'h4214).toNat + rsn.toNat) %
          4294967296]'hb6).toNat + j.toNat) % 4294967296 =
        ((4224 + 45 * mv + roff + j).setWidth 64).toNat := by
    rw [hroff_g, hmv_d, har_e, Nat.mod_eq_of_lt har_u]
  rw [m8_k6_get_congr har_i hb7 har_b, ← m8_bv32_lshr1_toNat, hnv_d] at hc
  exact hc

theorem fidCore_b6_lt {mv n len : Nat} (h1 : n < mv) (h2 : 4224 + 45 * mv ≤ len) :
    4224 + 6 * mv + n < len := by omega

private theorem fidCore_trace_lv_lt {scr0 scrt scrt1 scrt2 scrj : List (BitVec 32)}
    {mv ti ti' v rsn mr roff j nv : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv)
    (h4192 : 4192 < scr0.length) (hnv_d : scr0[4192]'h4192 = nv)
    (hmv_hi : mv.toNat ≤ 8192) (_hlt : scrt.length = scr0.length)
    (hti_pos : 0 < ti.toNat) (hti_le : ti.toNat ≤ mv.toNat) (hti1 : ti'.toNat = ti.toNat - 1)
    (htr_e : ((4224 + 5 * mv + ti').setWidth 64).toNat = 4224 + 5 * mv.toNat + ti'.toNat)
    (htr_b : ((4224 + 5 * mv + ti').setWidth 64).toNat < scrt.length)
    (hv_eq : (scrt[((4224 + 5 * mv + ti').setWidth 64).toNat]'htr_b).toNat / 2 = v.toNat)
    (hv_lt : v.toNat < mv.toNat)
    (hfl_e : ((4224 + 6 * mv + v).setWidth 64).toNat = 4224 + 6 * mv.toNat + v.toNat)
    (hfl_b : ((4224 + 6 * mv + v).setWidth 64).toNat < scrt.length)
    (hrs_e : ((4224 + mv + v).setWidth 64).toNat = 4224 + mv.toNat + v.toNat)
    (hrs_b : ((4224 + mv + v).setWidth 64).toNat < scrt1.length)
    (hrsn : scrt1[((4224 + mv + v).setWidth 64).toNat]'hrs_b = rsn)
    (hrsn_lt : rsn.toNat < 8 * mv.toNat)
    (hmr_e : ((4224 + 33 * mv + rsn).setWidth 64).toNat = 4224 + 33 * mv.toNat + rsn.toNat)
    (hmr_b : ((4224 + 33 * mv + rsn).setWidth 64).toNat < scrt1.length)
    (hmr_d : scrt1[((4224 + 33 * mv + rsn).setWidth 64).toNat]'hmr_b = mr)
    (hscrt1 : scrt1 = scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat
      (scrt[((4224 + 6 * mv + v).setWidth 64).toNat]'hfl_b &&& ~~~2#32))
    (hscrt2 : scrt2 = scrt1.set ((4224 + 33 * mv + rsn).setWidth 64).toNat (mr ||| 0x80000000#32))
    (hor_e : ((4224 + 29 * mv + rsn).setWidth 64).toNat = 4224 + 29 * mv.toNat + rsn.toNat)
    (hor_b2 : ((4224 + 29 * mv + rsn).setWidth 64).toNat < scrt2.length)
    (hroff_d : scrt2[((4224 + 29 * mv + rsn).setWidth 64).toNat]'hor_b2 = roff)
    (har_e : ((4224 + 45 * mv + roff + j).setWidth 64).toNat =
      4224 + 45 * mv.toNat + roff.toNat + j.toNat)
    (har_b : ((4224 + 45 * mv + roff + j).setWidth 64).toNat < scrj.length)
    {hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7}
    (hc : (scrj[(4224 + 45 * (scr0[4214]'h4214).toNat +
      ((ftS2 scr0 scrt h4214 ti hb0 hb1 hb3 hb2 hb4)[
        (4224 + 29 * (scr0[4214]'h4214).toNat +
          ((ftS1 scr0 scrt h4214 ti hb0 hb1)[ftRs scr0 scrt h4214 ti hb0]'hb5).toNat) %
        4294967296]'hb6).toNat + j.toNat) % 4294967296]'hb7).toNat / 2 <
      (scr0[4192]'h4192).toNat) :
    ((scrj[((4224 + 45 * mv + roff + j).setWidth 64).toNat]'har_b) >>> (1 : Nat)).toNat <
      nv.toNat := by
  have hti_u : 4224 + 5 * mv.toNat + (ti.toNat - 1) < 4294967296 := by
    clear hc hscrt2 hroff_d hmr_d hrsn hmr_b hrs_b hv_eq htr_b hor_b2 har_b hscrt1 hfl_b; omega
  have hfl_u : 4224 + 6 * mv.toNat + v.toNat < 4294967296 := by
    clear hc hscrt2 hroff_d hmr_d hrsn hmr_b hrs_b hv_eq htr_b hor_b2 har_b hscrt1 hfl_b; omega
  have hrs_u : 4224 + mv.toNat + v.toNat < 4294967296 := by
    clear hc hscrt2 hroff_d hmr_d hrsn hmr_b hrs_b hv_eq htr_b hor_b2 har_b hscrt1 hfl_b; omega
  have hmr_u : 4224 + 33 * mv.toNat + rsn.toNat < 4294967296 := by
    clear hc hscrt2 hroff_d hmr_d hrsn hmr_b hrs_b hv_eq htr_b hor_b2 har_b hscrt1 hfl_b; omega
  have hor_u : 4224 + 29 * mv.toNat + rsn.toNat < 4294967296 := by
    rw [← hor_e, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans (4224 + 29 * mv + rsn).isLt (by decide))]
    exact Nat.lt_of_lt_of_eq (4224 + 29 * mv + rsn).isLt (by decide)
  have har_u : 4224 + 45 * mv.toNat + roff.toNat + j.toNat < 4294967296 := by
    rw [← har_e, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans (4224 + 45 * mv + roff + j).isLt (by decide))]
    exact Nat.lt_of_lt_of_eq (4224 + 45 * mv + roff + j).isLt (by decide)
  have htr1 : ftTi scr0 h4214 ti = ((4224 + 5 * mv + ti').setWidth 64).toNat := by
    dsimp only [ftTi]; rw [htr_e, hmv_d, fid_sub1_mod32 _ _ hti_pos hti_u, hti1]
  have hv_g : (scrt[ftTi scr0 h4214 ti]'hb0).toNat / 2 = v.toNat := by
    rw [m8_k6_get_congr htr1 hb0 htr_b, hv_eq]
  have hfl1 : ftFl scr0 scrt h4214 ti hb0 = ((4224 + 6 * mv + v).setWidth 64).toNat := by
    dsimp only [ftFl]; rw [hv_g, hmv_d, hfl_e, Nat.mod_eq_of_lt hfl_u]
  have hrs1 : ftRs scr0 scrt h4214 ti hb0 = ((4224 + mv + v).setWidth 64).toNat := by
    dsimp only [ftRs]; rw [hv_g, hmv_d, hrs_e, Nat.mod_eq_of_lt hrs_u]
  have hset1 : ftS1 scr0 scrt h4214 ti hb0 hb1 = scrt1 := by
    simp only [ftS1, hfl1]; exact hscrt1.symm
  have hrsn_g : ∀ {hb_r},
      (ftS1 scr0 scrt h4214 ti hb0 hb1)[ftRs scr0 scrt h4214 ti hb0]'hb_r = rsn := by
    intro hb_r
    rw [← Option.some_inj, ← List.getElem?_eq_getElem, hset1, hrs1, ← hrsn,
      ← List.getElem?_eq_getElem]
  exact fidCore_trace_lv_aux h4214 hmv_d h4192 hnv_d hset1 (congrArg BitVec.toNat hrsn_g)
    (congrArg BitVec.toNat hrsn_g) (congrArg BitVec.toNat hrsn_g) hmr_u hor_u har_u
    hmr_e hmr_b hmr_d hscrt2 hor_e hor_b2 hroff_d har_e har_b hc

theorem fidCore_k_lt (k : Nat) {x : Nat} {mv : BitVec 32} {len : Nat}
    (hx : x ≤ 4 * mv.toNat) (hmv : 256 ≤ mv.toNat)
    (hbge : 4224 + 45 * mv.toNat ≤ len) (hk : k ≤ 40 := by decide) :
    4224 + k * mv.toNat + x < len := by
  have hk_le : k * mv.toNat ≤ 40 * mv.toNat := Nat.mul_le_mul_right mv.toNat hk
  omega

theorem fidCore_mv_lt (k : Nat) {x : Nat} {mv : BitVec 32} {len : Nat}
    (hx : x ≤ mv.toNat) (hmv : 256 ≤ mv.toNat)
    (hbge : 4224 + 45 * mv.toNat ≤ len) (hk : k ≤ 40 := by decide) :
    4224 + k * mv.toNat + x < len :=
  fidCore_k_lt k (Nat.le_trans hx (by omega)) hmv hbge hk

theorem fidCore_1_lt {x : Nat} {mv : BitVec 32} {len : Nat}
    (hx : x ≤ mv.toNat) (hmv : 256 ≤ mv.toNat)
    (hbge : 4224 + 45 * mv.toNat ≤ len) :
    4224 + mv.toNat + x < len := by
  have h := fidCore_mv_lt 1 hx hmv hbge; omega

private theorem fidCore_rsn_lt {scr0 scrt scrt1 : List (BitVec 32)}
    {mv ti ti' v rsn nc val1 val_set : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv)
    (h4193 : 4193 < scr0.length) (hnc_d : scr0[4193]'h4193 = nc)
    (hscrt1 : scrt1 = scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat val1)
    (_hlt : scrt.length = scr0.length) (hmv_hi : mv.toNat ≤ 8192)
    (hti_pos : 0 < ti.toNat) (hti_le : ti.toNat ≤ mv.toNat)
    (hti1 : ti'.toNat = ti.toNat - 1)
    (htr_e : ((4224 + 5 * mv + ti').setWidth 64).toNat = 4224 + 5 * mv.toNat + ti'.toNat)
    (htr_b : ((4224 + 5 * mv + ti').setWidth 64).toNat < scrt.length)
    (hv_eq : (scrt[((4224 + 5 * mv + ti').setWidth 64).toNat]'htr_b).toNat / 2 = v.toNat)
    (hv_lt : v.toNat < mv.toNat)
    (hfl_e : ((4224 + 6 * mv + v).setWidth 64).toNat = 4224 + 6 * mv.toNat + v.toNat)
    (hrs_e : ((4224 + mv + v).setWidth 64).toNat = 4224 + mv.toNat + v.toNat)
    (hrs_b : ((4224 + mv + v).setWidth 64).toNat < scrt1.length)
    (hrsn : scrt1[((4224 + mv + v).setWidth 64).toNat]'hrs_b = rsn)
    {hb1 hb2}
    (hc : ¬ (scr0[4193]'h4193).toNat ≤
        ((scrt.set ((4224 + 6 * (scr0[4214]'h4214).toNat +
          (scrt[(4224 + 5 * (scr0[4214]'h4214).toNat +
            (4294967296 - 1 + ti.toNat)) % 4294967296]'hb1).toNat / 2) % 4294967296)
          val_set)[(4224 + (scr0[4214]'h4214).toNat +
            (scrt[(4224 + 5 * (scr0[4214]'h4214).toNat +
              (4294967296 - 1 + ti.toNat)) % 4294967296]'hb1).toNat / 2) %
            4294967296]'hb2).toNat) :
    rsn.toNat < nc.toNat := by
  have ⟨hne_mod, hlt32, hne_raw, hti32⟩ := fidCore_ne45_aux hmv_hi hv_lt hti_le
  have hadd : (4224 + 5 * (scr0[4214]'h4214).toNat +
      (4294967296 - 1 + ti.toNat)) % 4294967296 = 4224 + 5 * mv.toNat + (ti.toNat - 1) := by
    rw [hmv_d]; exact fid_sub1_mod32 _ _ hti_pos hti32
  have hidx_nat : (scrt[(4224 + 5 * (scr0[4214]'h4214).toNat +
      (4294967296 - 1 + ti.toNat)) % 4294967296]'hb1).toNat / 2 = v.toNat := by
    rw [← hv_eq]
    exact congrArg (fun x => x.toNat / 2)
      (m8_k6_get_congr (by rw [hadd, htr_e, hti1]) hb1 htr_b)
  have hset_ne : (4224 + 6 * (scr0[4214]'h4214).toNat +
      (scrt[(4224 + 5 * (scr0[4214]'h4214).toNat +
        (4294967296 - 1 + ti.toNat)) % 4294967296]'hb1).toNat / 2) % 4294967296 ≠
      (4224 + (scr0[4214]'h4214).toNat +
      (scrt[(4224 + 5 * (scr0[4214]'h4214).toNat +
        (4294967296 - 1 + ti.toNat)) % 4294967296]'hb1).toNat / 2) % 4294967296 := by
    rw [hidx_nat, hmv_d]; exact hne_mod
  have hget_b : (4224 + (scr0[4214]'h4214).toNat +
      (scrt[(4224 + 5 * (scr0[4214]'h4214).toNat +
        (4294967296 - 1 + ti.toNat)) % 4294967296]'hb1).toNat / 2) % 4294967296 <
      scrt.length := by
    rw [List.length_set] at hb2; exact hb2
  have hkey : (4224 + (scr0[4214]'h4214).toNat +
      (scrt[(4224 + 5 * (scr0[4214]'h4214).toNat +
        (4294967296 - 1 + ti.toNat)) % 4294967296]'hb1).toNat / 2) % 4294967296 =
      ((4224 + mv + v).setWidth 64).toNat := by
    rw [hidx_nat, hmv_d, hrs_e, Nat.mod_eq_of_lt hlt32]
  have hrs_old_b : ((4224 + mv + v).setWidth 64).toNat < scrt.length := by
    rw [← hkey]; exact hget_b
  have hget_eq : scrt[(4224 + (scr0[4214]'h4214).toNat +
      (scrt[(4224 + 5 * (scr0[4214]'h4214).toNat +
        (4294967296 - 1 + ti.toNat)) % 4294967296]'hb1).toNat / 2) % 4294967296]'hget_b =
      rsn := by
    have h1 := m8_k6_get_congr hkey hget_b hrs_old_b
    have h2 : scrt[((4224 + mv + v).setWidth 64).toNat]'hrs_old_b =
        scrt1[((4224 + mv + v).setWidth 64).toNat]'hrs_b := by
      subst hscrt1
      exact (List.getElem_set_ne (by rw [hfl_e, hrs_e]; exact hne_raw) hrs_b).symm
    exact h1.trans (h2.trans hrsn)
  rw [List.getElem_set_ne hset_ne hb2, hget_eq, hnc_d] at hc
  exact Nat.lt_of_not_le hc

theorem fidCore_clause_ok_bnds {scr0 scrt : List (BitVec 32)} {mv nc acap cid : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (h4193 : 4193 < scr0.length) (hnc_eq : scr0[4193]?.getD 0#32 = nc)
    (h4207 : 4207 < scr0.length) (hac_eq : scr0[4207]?.getD 0#32 = acap)
    (hmv_hi : mv.toNat ≤ 8192) (_hnc_le : nc.toNat ≤ 4 * mv.toNat)
    (hik : FidCoreInv scr0 mv nc scrt) (hcid : cid.toNat < nc.toNat)
    (hor_e : ((4224 + 29 * mv + cid).setWidth 64).toNat = 4224 + 29 * mv.toNat + cid.toNat)
    (hmr_e : ((4224 + 33 * mv + cid).setWidth 64).toNat = 4224 + 33 * mv.toNat + cid.toNat)
    (hor_b : ((4224 + 29 * mv + cid).setWidth 64).toNat < scrt.length)
    (hmr_b : ((4224 + 33 * mv + cid).setWidth 64).toNat < scrt.length) :
    let roff := scrt[((4224 + 29 * mv + cid).setWidth 64).toNat]'hor_b
    let rmeta := scrt[((4224 + 33 * mv + cid).setWidth 64).toNat]'hmr_b
    roff.toNat + (rmeta &&& 0xFFFF#32).toNat ≤ acap.toNat ∧
    (scrt[4224 + 33 * mv.toNat + cid.toNat]?.getD 0#32).toNat % 65536 =
      (rmeta &&& 0xFFFF#32).toNat ∧
    roff.toNat + (rmeta &&& 0xFFFF#32).toNat ≤ 65535 + acap.toNat ∧
    4224 + 45 * mv.toNat + acap.toNat ≤ scrt.length := by
  have hlt := hik.2.1; have hmin := hik.1.base_ge
  have hmv_t := fidCoreInv_mv h4214 hmv_eq hik
  have hnc_t : scrt[4193]?.getD 0#32 = nc := by
    rw [hik.2.2.1 4193 h4193 (Or.inl (by omega)), hnc_eq]
  have hac_t : scrt[4207]?.getD 0#32 = acap := by
    rw [hik.2.2.1 4207 h4207 (Or.inl (by omega)), hac_eq]
  have hcl := hik.1.clause_ok (cid := cid.toNat) (by rw [hnc_t]; exact hcid)
  dsimp only at hcl
  rw [hmv_t, hac_t] at hcl
  have hroff_eq : (scrt[4224 + 29 * mv.toNat + cid.toNat]?.getD 0#32) =
      scrt[((4224 + 29 * mv + cid).setWidth 64).toNat]'hor_b := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact m8_k6_get_congr hor_e.symm _ _
  have hrm_eq : (scrt[4224 + 33 * mv.toNat + cid.toNat]?.getD 0#32) =
      scrt[((4224 + 33 * mv + cid).setWidth 64).toNat]'hmr_b := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact m8_k6_get_congr hmr_e.symm _ _
  rw [hroff_eq, hrm_eq] at hcl
  have hlen_ge := hik.1.length_ge
  rw [hmv_t, hac_t] at hlen_ge
  refine ⟨hcl.1, ?_, ?_, hlen_ge⟩
  · rw [hrm_eq, FidK6Tactics.fid_bv32_and_ffff_toNat]
  · have := m8_and_ffff_le (scrt[((4224 + 33 * mv + cid).setWidth 64).toNat]'hmr_b)
    omega

theorem fidCore_p3_hant_lt {scr0 scrc scrj : List (BitVec 32)}
    {mv nc acap cid cid' off cmeta sz na ant j : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv)
    (hmv_hi : mv.toNat ≤ 8192) (hnc_le : nc.toNat ≤ 4 * mv.toNat)
    (hcid'_lt : cid'.toNat < nc.toNat) (hcid_pos : 0 < cid.toNat)
    (hcid1 : (cid - 1#32).toNat = cid.toNat - 1) (hcid'_d : cid - 1#32 = cid')
    (hlc : scrc.length = scr0.length) (_hsz_le : sz.toNat ≤ 65535) (hj_lt : j.toNat < na.toNat)
    (hosn_le : off.toNat + sz.toNat + na.toNat ≤ acap.toNat)
    (hlen_scr : 4224 + 45 * mv.toNat + acap.toNat ≤ scr0.length)
    (hcap_lt : scr0.length < 2 ^ 30)
    (hco_e : ((4224 + 29 * mv + cid').setWidth 64).toNat = 4224 + 29 * mv.toNat + cid'.toNat)
    (hco_lt : ((4224 + 29 * mv + cid').setWidth 64).toNat < scrc.length)
    (hoff_d : scrc[((4224 + 29 * mv + cid').setWidth 64).toNat]'hco_lt = off)
    (hcm_e : ((4224 + 33 * mv + cid').setWidth 64).toNat = 4224 + 33 * mv.toNat + cid'.toNat)
    (hcm_lt : ((4224 + 33 * mv + cid').setWidth 64).toNat < scrc.length)
    (hcmeta_d : scrc[((4224 + 33 * mv + cid').setWidth 64).toNat]'hcm_lt = cmeta)
    (hsz_d : cmeta &&& 0xFFFF#32 = sz)
    (har_e : ((4224 + 45 * mv + off + sz + j).setWidth 64).toNat =
      4224 + 45 * mv.toNat + off.toNat + sz.toNat + j.toNat)
    (har_lt : ((4224 + 45 * mv + off + sz + j).setWidth 64).toNat < scrj.length)
    (hant_d : scrj[((4224 + 45 * mv + off + sz + j).setWidth 64).toNat]'har_lt = ant)
    {hb1 hb2 hb3}
    (hc : (scrj[(4224 + 45 * (scr0[4214]'h4214).toNat +
      (scrc[(4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) %
        4294967296]'hb1).toNat +
      (scrc[(4224 + 33 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) %
        4294967296]'hb2).toNat % 65536 + j.toNat) % 4294967296]'hb3).toNat < nc.toNat) :
    ant.toNat < nc.toNat := by
  have hcid_sub : cid.toNat - 1 < nc.toNat := by rw [← hcid1, hcid'_d]; exact hcid'_lt
  have h1 : (4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) % 4294967296 =
      ((4224 + 29 * mv + cid').setWidth 64).toNat := by
    rw [hmv_d, hco_e, ← hcid'_d, hcid1, fid_sub1_mod32 _ _ hcid_pos (by omega)]
  have hoff_g : scrc[(4224 + 29 * (scr0[4214]'h4214).toNat +
      (4294967296 - 1 + cid.toNat)) % 4294967296]'hb1 = off := by
    rw [m8_k6_get_congr h1 hb1 hco_lt, hoff_d]
  have h2 : (4224 + 33 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) % 4294967296 =
      ((4224 + 33 * mv + cid').setWidth 64).toNat := by
    rw [hmv_d, hcm_e, ← hcid'_d, hcid1, fid_sub1_mod32 _ _ hcid_pos (by omega)]
  have hsz_g : (scrc[(4224 + 33 * (scr0[4214]'h4214).toNat +
      (4294967296 - 1 + cid.toNat)) % 4294967296]'hb2).toNat % 65536 = sz.toNat := by
    rw [m8_k6_get_congr h2 hb2 hcm_lt, hcmeta_d, ← hsz_d, fid_bv32_and_ffff_toNat]
  have h3 : (4224 + 45 * (scr0[4214]'h4214).toNat +
      (scrc[(4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) %
        4294967296]'hb1).toNat +
      (scrc[(4224 + 33 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) %
        4294967296]'hb2).toNat % 65536 + j.toNat) % 4294967296 =
      ((4224 + 45 * mv + off + sz + j).setWidth 64).toNat := by
    rw [hoff_g, hsz_g, hmv_d, har_e, Nat.mod_eq_of_lt (by omega)]
  rw [m8_k6_get_congr h3 hb3 har_lt, hant_d] at hc
  exact hc

theorem fidCore_p3_hlv_lt {scr0 scrc scrj : List (BitVec 32)}
    {mv nc acap cid cid' off sz j lv nv : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv)
    (h4192 : 4192 < scr0.length) (hnv_d : scr0[4192]'h4192 = nv)
    (_hmv_hi : mv.toNat ≤ 8192) (hnc_le : nc.toNat ≤ 4 * mv.toNat)
    (hcid'_lt : cid'.toNat < nc.toNat) (hcid_pos : 0 < cid.toNat)
    (hcid1 : (cid - 1#32).toNat = cid.toNat - 1) (hcid'_d : cid - 1#32 = cid')
    (hj_lt : j.toNat < sz.toNat) (hos_le : off.toNat + sz.toNat ≤ acap.toNat)
    (hlen_scr : 4224 + 45 * mv.toNat + acap.toNat ≤ scr0.length)
    (hcap_lt : scr0.length < 2 ^ 30)
    (hco_e : ((4224 + 29 * mv + cid').setWidth 64).toNat = 4224 + 29 * mv.toNat + cid'.toNat)
    (hco_lt : ((4224 + 29 * mv + cid').setWidth 64).toNat < scrc.length)
    (hoff_d : scrc[((4224 + 29 * mv + cid').setWidth 64).toNat]'hco_lt = off)
    (har_e : ((4224 + 45 * mv + off + j).setWidth 64).toNat =
      4224 + 45 * mv.toNat + off.toNat + j.toNat)
    (har_lt : ((4224 + 45 * mv + off + j).setWidth 64).toNat < scrj.length)
    (hlv_d :
      scrj[((4224 + 45 * mv + off + j).setWidth 64).toNat]'har_lt >>> (1 : Nat) = lv)
    {hb1 hb2}
    (hc : (scrj[(4224 + 45 * (scr0[4214]'h4214).toNat +
      (scrc[(4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) %
        4294967296]'hb1).toNat + j.toNat) % 4294967296]'hb2).toNat / 2 <
      (scr0[4192]'h4192).toNat) :
    lv.toNat < nv.toNat := by
  have hcid_sub : cid.toNat - 1 < nc.toNat := by rw [← hcid1, hcid'_d]; exact hcid'_lt
  have h1 : (4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) % 4294967296 =
      ((4224 + 29 * mv + cid').setWidth 64).toNat := by
    rw [hmv_d, hco_e, ← hcid'_d, hcid1, fid_sub1_mod32 _ _ hcid_pos (by omega)]
  have hoff_g : scrc[(4224 + 29 * (scr0[4214]'h4214).toNat +
      (4294967296 - 1 + cid.toNat)) % 4294967296]'hb1 = off := by
    rw [m8_k6_get_congr h1 hb1 hco_lt, hoff_d]
  have h2 : (4224 + 45 * (scr0[4214]'h4214).toNat +
      (scrc[(4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) %
        4294967296]'hb1).toNat + j.toNat) % 4294967296 =
      ((4224 + 45 * mv + off + j).setWidth 64).toNat := by
    rw [hoff_g, hmv_d, har_e, Nat.mod_eq_of_lt (by omega)]
  rw [m8_k6_get_congr h2 hb2 har_lt, ← m8_bv32_lshr1_toNat, hlv_d, hnv_d] at hc
  exact hc

theorem fidCore_p4_hc_rw {scra : List (BitVec 32)} {j : BitVec 32} {i_raw i_new : Nat}
    (hi : i_raw = i_new)
    {hb1 : i_raw < scra.length}
    {hb2 : i_raw < (scra.set i_raw (scra[i_raw]'hb1 ||| 2147483648#32)).length}
    {hb1' : i_new < scra.length}
    {hb2' : i_new < (scra.set i_new (scra[i_new]'hb1' ||| 2147483648#32)).length}
    (hc : j.toNat <
      ((scra.set i_raw (scra[i_raw]'hb1 ||| 2147483648#32))[i_raw]'hb2).toNat % 65536) :
    j.toNat <
      ((scra.set i_new (scra[i_new]'hb1' ||| 2147483648#32))[i_new]'hb2').toNat % 65536 := by
  subst hi; exact hc

theorem fidCore_p4_hlv_off {scr0 scrj : List (BitVec 32)}
    {mv off_i j nv lv : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv)
    (h4192 : 4192 < scr0.length) (hnv_d : scr0[4192]'h4192 = nv)
    (har_e : ((4224 + 45 * mv + off_i + j).setWidth 64).toNat =
      4224 + 45 * mv.toNat + off_i.toNat + j.toNat)
    (har_b : ((4224 + 45 * mv + off_i + j).setWidth 64).toNat < scrj.length)
    (hlv_d : scrj[((4224 + 45 * mv + off_i + j).setWidth 64).toNat]'har_b >>> (1 : Nat) = lv)
    {hb : (4224 + 45 * (scr0[4214]'h4214).toNat + off_i.toNat + j.toNat) % 4294967296 <
      scrj.length}
    (hc : (scrj[(4224 + 45 * (scr0[4214]'h4214).toNat + off_i.toNat + j.toNat) %
      4294967296]'hb).toNat / 2 < (scr0[4192]'h4192).toNat) :
    lv.toNat < nv.toNat := by
  have har_u : 4224 + 45 * mv.toNat + off_i.toNat + j.toNat < 4294967296 := by
    rw [← har_e, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans (4224 + 45 * mv + off_i + j).isLt (by decide))]
    exact Nat.lt_of_lt_of_eq (4224 + 45 * mv + off_i + j).isLt (by decide)
  have har_i : (4224 + 45 * (scr0[4214]'h4214).toNat + off_i.toNat + j.toNat) % 4294967296 =
      ((4224 + 45 * mv + off_i + j).setWidth 64).toNat := by
    rw [hmv_d, har_e, Nat.mod_eq_of_lt har_u]
  rw [m8_k6_get_congr har_i hb har_b, ← m8_bv32_lshr1_toNat, hlv_d, hnv_d] at hc
  exact hc

theorem fidCore_p3_hr0_lt {scr0 scrc scrj : List (BitVec 32)}
    {mv nc cid cid' off j lv r0 : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv)
    (h4193 : 4193 < scr0.length) (hnc_d : scr0[4193]'h4193 = nc)
    (hmv_hi : mv.toNat ≤ 8192) (hnc_le : nc.toNat ≤ 4 * mv.toNat)
    (hcid'_lt : cid'.toNat < nc.toNat) (hcid_pos : 0 < cid.toNat)
    (hcid1 : (cid - 1#32).toNat = cid.toNat - 1) (hcid'_d : cid - 1#32 = cid')
    (hco_e : ((4224 + 29 * mv + cid').setWidth 64).toNat = 4224 + 29 * mv.toNat + cid'.toNat)
    (hco_lt : ((4224 + 29 * mv + cid').setWidth 64).toNat < scrc.length)
    (hoff_d : scrc[((4224 + 29 * mv + cid').setWidth 64).toNat]'hco_lt = off)
    (har_e : ((4224 + 45 * mv + off + j).setWidth 64).toNat =
      4224 + 45 * mv.toNat + off.toNat + j.toNat)
    (har_lt : ((4224 + 45 * mv + off + j).setWidth 64).toNat < scrj.length)
    (hlv_d :
      scrj[((4224 + 45 * mv + off + j).setWidth 64).toNat]'har_lt >>> (1 : Nat) = lv)
    (hrs_e : ((4224 + mv + lv).setWidth 64).toNat = 4224 + mv.toNat + lv.toNat)
    (hrs_b : ((4224 + mv + lv).setWidth 64).toNat < scrj.length)
    (hr0_d : scrj[((4224 + mv + lv).setWidth 64).toNat]'hrs_b = r0)
    {hb1 hb2 hb3}
    (hc : (scrj[(4224 + (scr0[4214]'h4214).toNat +
      (scrj[(4224 + 45 * (scr0[4214]'h4214).toNat +
        (scrc[(4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) %
          4294967296]'hb1).toNat + j.toNat) % 4294967296]'hb2).toNat / 2) %
      4294967296]'hb3).toNat < (scr0[4193]'h4193).toNat) :
    r0.toNat < nc.toNat := by
  have hcid_sub : cid.toNat - 1 < nc.toNat := by rw [← hcid1, hcid'_d]; exact hcid'_lt
  have har_u : 4224 + 45 * mv.toNat + off.toNat + j.toNat < 4294967296 := by
    rw [← har_e, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans (4224 + 45 * mv + off + j).isLt (by decide))]
    exact Nat.lt_of_lt_of_eq (4224 + 45 * mv + off + j).isLt (by decide)
  have hrs_u : 4224 + mv.toNat + lv.toNat < 4294967296 := by
    rw [← hrs_e, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans (4224 + mv + lv).isLt (by decide))]
    exact Nat.lt_of_lt_of_eq (4224 + mv + lv).isLt (by decide)
  have h1 : (4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) % 4294967296 =
      ((4224 + 29 * mv + cid').setWidth 64).toNat := by
    rw [hmv_d, hco_e, ← hcid'_d, hcid1, fid_sub1_mod32 _ _ hcid_pos (by omega)]
  have hoff_g : scrc[(4224 + 29 * (scr0[4214]'h4214).toNat +
      (4294967296 - 1 + cid.toNat)) % 4294967296]'hb1 = off := by
    rw [m8_k6_get_congr h1 hb1 hco_lt, hoff_d]
  have h2 : (4224 + 45 * (scr0[4214]'h4214).toNat +
      (scrc[(4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) %
        4294967296]'hb1).toNat + j.toNat) % 4294967296 =
      ((4224 + 45 * mv + off + j).setWidth 64).toNat := by
    rw [hoff_g, hmv_d, har_e, Nat.mod_eq_of_lt har_u]
  have hlv_g : scrj[(4224 + 45 * (scr0[4214]'h4214).toNat +
      (scrc[(4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) %
        4294967296]'hb1).toNat + j.toNat) % 4294967296]'hb2 =
      scrj[((4224 + 45 * mv + off + j).setWidth 64).toNat]'har_lt :=
    m8_k6_get_congr h2 hb2 har_lt
  have h3 : (4224 + (scr0[4214]'h4214).toNat +
      (scrj[(4224 + 45 * (scr0[4214]'h4214).toNat +
        (scrc[(4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) %
          4294967296]'hb1).toNat + j.toNat) % 4294967296]'hb2).toNat / 2) % 4294967296 =
      ((4224 + mv + lv).setWidth 64).toNat := by
    rw [hlv_g, ← m8_bv32_lshr1_toNat, hlv_d, hmv_d, hrs_e, Nat.mod_eq_of_lt hrs_u]
  rw [m8_k6_get_congr h3 hb3 hrs_b, hr0_d, hnc_d] at hc
  exact hc

/-! ## 3. Phase 2 Trail Traceback & Flag-Clear Sub-WP -/

/-- Extracted C0 `Expr` for `full_k6_core_fid` Phase 2 trail traceback + `flags & 2` clear. -/
@[expose] def fidCorePhase2TraceExpr (pScr : BitVec 64)
    (mv nc nv acap ti0 : BitVec 32) (J2 : Cont [i32]) : Expr Val Cont [] :=
  let o_rsn : BitVec 32 := 4224 + mv
  let o_trl : BitVec 32 := 4224 + 5 * mv
  let o_flags : BitVec 32 := 4224 + 6 * mv
  let o_cl_off : BitVec 32 := 4224 + 29 * mv
  let o_cl_meta : BitVec 32 := 4224 + 33 * mv
  let o_arena : BitVec 32 := 4224 + 45 * mv
  Expr.group (sig := [[i32]]) (fun Js_4 =>
    Blocks.cons (fun p_44 =>
      Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ugt i32 Ty.bool (by decide),
                  args := (Arg.var p_44.fst, Arg.imm 0, ()) } fun p_45 =>
      Expr.jnz (Arg.var p_45.fst)
        (Expr.let_ { sig := [i32, i32], code := OpCode.sub i32,
                     args := (Arg.var p_44.fst, Arg.imm 1, ()) } fun p_46 =>
         Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                     args := (Arg.var o_trl, Arg.var p_46.fst, ()) } fun p_47 =>
         Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                     args := (Arg.var p_47.fst, ()) } fun p_48 =>
         Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                     args := (Arg.var p_48.fst, Arg.imm 4, ()) } fun p_49 =>
         Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                     args := (Arg.var pScr, Arg.var p_49.fst, ()) } fun p_50 =>
         Expr.load i32 (Arg.var p_50.fst) fun ld_10 =>
         Expr.let_ { sig := [i32, i32], code := OpCode.lshr i32,
                     args := (Arg.var ld_10, Arg.imm 1, ()) } fun p_51 =>
         Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.uge i32 Ty.bool (by decide),
                     args := (Arg.var p_51.fst, Arg.var nv, ()) } fun p_52 =>
         Expr.jnz (Arg.var p_52.fst)
           (Expr.jump Js_4.fst (Arg.var p_46.fst, ()))
           (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                        args := (Arg.var o_flags, Arg.var p_51.fst, ()) } fun p_53 =>
            Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                        args := (Arg.var p_53.fst, ()) } fun p_54 =>
            Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                        args := (Arg.var p_54.fst, Arg.imm 4, ()) } fun p_55 =>
            Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var pScr, Arg.var p_55.fst, ()) } fun p_56 =>
            Expr.load i32 (Arg.var p_56.fst) fun ld_11 =>
            Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                        args := (Arg.var ld_11, Arg.imm 2, ()) } fun p_57 =>
            Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool (by decide),
                        args := (Arg.var p_57.fst, Arg.imm 0, ()) } fun p_58 =>
            Expr.jnz (Arg.var p_58.fst)
              (Expr.jump Js_4.fst (Arg.var p_46.fst, ()))
              (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                           args := (Arg.var o_flags, Arg.var p_51.fst, ()) } fun p_59 =>
               Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                           args := (Arg.var p_59.fst, ()) } fun p_60 =>
               Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                           args := (Arg.var p_60.fst, Arg.imm 4, ()) } fun p_61 =>
               Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                           args := (Arg.var pScr, Arg.var p_61.fst, ()) } fun p_62 =>
               Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                           args := (Arg.var o_flags, Arg.var p_51.fst, ()) } fun p_63 =>
               Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                           args := (Arg.var p_63.fst, ()) } fun p_64 =>
               Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                           args := (Arg.var p_64.fst, Arg.imm 4, ()) } fun p_65 =>
               Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                           args := (Arg.var pScr, Arg.var p_65.fst, ()) } fun p_66 =>
               Expr.load i32 (Arg.var p_66.fst) fun ld_12 =>
               Expr.let_ { sig := [i32], code := OpCode.not i32,
                           args := (Arg.imm 2, ()) } fun p_67 =>
               Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                           args := (Arg.var ld_12, Arg.var p_67.fst, ()) } fun p_68 =>
               Expr.store (Arg.var p_68.fst) (Arg.var p_62.fst)
                 (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                              args := (Arg.var o_rsn, Arg.var p_51.fst, ()) } fun p =>
                  Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                              args := (Arg.var p.fst, ()) } fun p =>
                  Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                              args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                  Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                              args := (Arg.var pScr, Arg.var p.fst, ()) } fun p =>
                  Expr.load i32 (Arg.var p.fst) fun ld_13 =>
                  Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.uge i32 Ty.bool
                                (by decide),
                              args := (Arg.var ld_13, Arg.var nc, ()) } fun p =>
                  Expr.jnz (Arg.var p.fst)
                    (Expr.jump Js_4.fst (Arg.var p_46.fst, ()))
                    (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                 args := (Arg.var o_cl_meta, Arg.var ld_13, ()) } fun p =>
                     Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                 args := (Arg.var p.fst, ()) } fun p =>
                     Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                 args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                     Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                 args := (Arg.var pScr, Arg.var p.fst, ()) } fun p =>
                     Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                 args := (Arg.var o_cl_meta, Arg.var ld_13, ()) } fun p_69 =>
                     Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                 args := (Arg.var p_69.fst, ()) } fun p_70 =>
                     Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                 args := (Arg.var p_70.fst, Arg.imm 4, ()) } fun p_71 =>
                     Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                 args := (Arg.var pScr, Arg.var p_71.fst, ()) } fun p_72 =>
                     Expr.load i32 (Arg.var p_72.fst) fun ld_14 =>
                     Expr.let_ { sig := [i32, i32], code := OpCode.or i32,
                                 args := (Arg.var ld_14, Arg.imm 2147483648, ()) } fun p_73 =>
                     Expr.store (Arg.var p_73.fst) (Arg.var p.fst)
                       (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                    args := (Arg.var o_cl_off, Arg.var ld_13, ()) } fun p =>
                        Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                    args := (Arg.var p.fst, ()) } fun p =>
                        Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                    args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                        Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                    args := (Arg.var pScr, Arg.var p.fst, ()) } fun p =>
                        Expr.load i32 (Arg.var p.fst) fun ld_15 =>
                        Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                    args := (Arg.var o_cl_meta, Arg.var ld_13, ()) } fun p =>
                        Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                    args := (Arg.var p.fst, ()) } fun p =>
                        Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                    args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                        Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                    args := (Arg.var pScr, Arg.var p.fst, ()) } fun p =>
                        Expr.load i32 (Arg.var p.fst) fun ld_16 =>
                        Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                                    args := (Arg.var ld_16, Arg.imm 65535, ()) } fun p =>
                        Expr.group (sig := [[]]) (fun Js =>
                          Blocks.cons (fun _ =>
                            Expr.jump Js_4.fst (Arg.var p_46.fst, ())) Blocks.nil) fun Js =>
                        Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                    args := (Arg.var ld_15, Arg.var p.fst, ()) } fun p_74 =>
                        Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ule i32 Ty.bool
                                      (by decide),
                                    args := (Arg.var p_74.fst, Arg.var acap, ()) } fun p_75 =>
                        Expr.jnz (Arg.var p_75.fst)
                          (Expr.group (sig := [[i32]]) (fun Js_5 =>
                             Blocks.cons (fun p_76 =>
                               Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32
                                             Ty.bool (by decide),
                                           args := (Arg.var p_76.fst, Arg.var p.fst, ()) } fun p =>
                               Expr.jnz (Arg.var p.fst)
                                 (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                              args := (Arg.var o_arena, Arg.var ld_15, ()) }
                                   fun p =>
                                  Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                              args := (Arg.var p.fst, Arg.var p_76.fst, ()) }
                                    fun p =>
                                  Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                              args := (Arg.var p.fst, ()) } fun p =>
                                  Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                              args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                                  Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                              args := (Arg.var pScr, Arg.var p.fst, ()) } fun p =>
                                  Expr.load i32 (Arg.var p.fst) fun ld_17 =>
                                  Expr.let_ { sig := [i32, i32], code := OpCode.lshr i32,
                                              args := (Arg.var ld_17, Arg.imm 1, ()) } fun p =>
                                  Expr.group (sig := [[]]) (fun Js =>
                                    Blocks.cons (fun _ =>
                                      Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                                  args := (Arg.var p_76.fst, Arg.imm 1, ()) }
                                        fun p =>
                                      Expr.jump Js_5.fst (Arg.var p.fst, ())) Blocks.nil) fun Js =>
                                  Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32
                                                Ty.bool (by decide),
                                              args := (Arg.var p.fst, Arg.var nv, ()) } fun p_77 =>
                                  Expr.jnz (Arg.var p_77.fst)
                                    (Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32
                                                   Ty.bool (by decide),
                                                 args := (Arg.var p.fst, Arg.var p_51.fst, ()) }
                                       fun p_78 =>
                                     Expr.jnz (Arg.var p_78.fst)
                                       (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                                    args := (Arg.var o_flags, Arg.var p.fst, ()) }
                                          fun p_79 =>
                                        Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                                    args := (Arg.var p_79.fst, ()) } fun p_80 =>
                                        Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                                    args := (Arg.var p_80.fst, Arg.imm 4, ()) }
                                          fun p_81 =>
                                        Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                                    args := (Arg.var pScr, Arg.var p_81.fst, ()) }
                                          fun p_82 =>
                                        Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                                    args := (Arg.var o_flags, Arg.var p.fst, ()) }
                                          fun p =>
                                        Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                                    args := (Arg.var p.fst, ()) } fun p =>
                                        Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                                    args := (Arg.var p.fst, Arg.imm 4, ()) }
                                          fun p =>
                                        Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                                    args := (Arg.var pScr, Arg.var p.fst, ()) }
                                          fun p =>
                                        Expr.load i32 (Arg.var p.fst) fun ld =>
                                        Expr.let_ { sig := [i32, i32], code := OpCode.or i32,
                                                    args := (Arg.var ld, Arg.imm 2, ()) }
                                          fun p =>
                                        Expr.store (Arg.var p.fst) (Arg.var p_82.fst)
                                          (Expr.jump Js.fst ()))
                                       (Expr.jump Js.fst ()))
                                    (Expr.jump Js.fst ()))
                                 (Expr.jump Js.fst ())) Blocks.nil) fun Js =>
                           Expr.jump Js.fst (Arg.imm 0, ()))
                          (Expr.jump Js.fst ())))))))
        (Expr.group (sig := [[i32]]) (fun Js_5 =>
           Blocks.cons (fun p =>
             Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                         args := (Arg.var p.fst, Arg.var nv, ()) } fun p_46 =>
             Expr.jnz (Arg.var p_46.fst)
               (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                            args := (Arg.var o_flags, Arg.var p.fst, ()) } fun p_47 =>
                Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                            args := (Arg.var p_47.fst, ()) } fun p_48 =>
                Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                            args := (Arg.var p_48.fst, Arg.imm 4, ()) } fun p_49 =>
                Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                            args := (Arg.var pScr, Arg.var p_49.fst, ()) } fun p_50 =>
                Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                            args := (Arg.var o_flags, Arg.var p.fst, ()) } fun p_51 =>
                Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                            args := (Arg.var p_51.fst, ()) } fun p_52 =>
                Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                            args := (Arg.var p_52.fst, Arg.imm 4, ()) } fun p_53 =>
                Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                            args := (Arg.var pScr, Arg.var p_53.fst, ()) } fun p_54 =>
                Expr.load i32 (Arg.var p_54.fst) fun ld =>
                Expr.let_ { sig := [i32], code := OpCode.not i32,
                            args := (Arg.imm 2, ()) } fun p_55 =>
                Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                            args := (Arg.var ld, Arg.var p_55.fst, ()) } fun p_56 =>
                Expr.store (Arg.var p_56.fst) (Arg.var p_50.fst)
                  (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                               args := (Arg.var p.fst, Arg.imm 1, ()) } fun p =>
                   Expr.jump Js_5.fst (Arg.var p.fst, ())))
               (Expr.jump J2 (Arg.var p.fst, ()))) Blocks.nil) fun Js =>
         Expr.jump Js.fst (Arg.imm 0, ()))) Blocks.nil) fun Js =>
  Expr.jump Js.fst (Arg.var ti0, ())

/-- Extracted WP proof for the trail-traceback loop and `flags & 2` clear in Phase 2. -/
theorem fidCore_phase2_trace_wp (Γ : Env) (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (Q : Post []) (X : XPost) (scr0 scrm : List (BitVec 32)) (ti0 : BitVec 32)
    (J2 : Cont [i32]) (mb : Mem 64)
    (hmin : 15744 ≤ scr0.length)
    (h4214 : 4214 < scr0.length) (h4192 : 4192 < scr0.length)
    (h4193 : 4193 < scr0.length) (h4207 : 4207 < scr0.length) :
    let mv := scr0[4214]'h4214
    let nc := scr0[4193]'h4193
    let nv := scr0[4192]'h4192
    let acap := scr0[4207]'h4207
    256 ≤ mv.toNat → mv.toNat ≤ 8192 →
    nc.toNat ≤ 4 * mv.toNat → nv.toNat ≤ mv.toNat →
    4224 + 45 * mv.toNat ≤ scr0.length →
    ti0.toNat ≤ mv.toNat → FidCoreInv scr0 mv nc scrm →
    (FullMem c (m8ScrSt s scrm) ⋆ R) mb →
    (∀ (x : BitVec 32) (scrf : List (BitVec 32)) (mf : Mem 64),
      FidCoreInv scr0 mv nc scrf → (FullMem c (m8ScrSt s scrf) ⋆ R) mf → J2 (x, ()) mf) →
    wp Γ Q X (fidCorePhase2TraceExpr c.pScratchBuf mv nc nv acap ti0 J2) mb := by
  intro mv nc nv acap hmv_lo hmv_hi hnc_le hnv_le hbge hti0 hikm hmb hJ2
  have hmv_d : scr0[4214]'h4214 = mv := rfl
  have hnv_d : scr0[4192]'h4192 = nv := rfl
  have hnc_d : scr0[4193]'h4193 = nc := rfl
  have hmv_eq : scr0[4214]?.getD 0#32 = mv := m8_k6_get_eq h4214
  have hnc_eq : scr0[4193]?.getD 0#32 = nc := m8_k6_get_eq h4193
  have hac_eq : scr0[4207]?.getD 0#32 = acap := m8_k6_get_eq h4207
  have hcap_lt : scr0.length < 2 ^ 30 := by rw [← hikm.2.1]; exact hikm.1.length_lt
  let invS : Mem 64 → Prop := fun mj =>
    ∃ scrj : List (BitVec 32), FidCoreInv scr0 mv nc scrj ∧ (FullMem c (m8ScrSt s scrj) ⋆ R) mj
  have hmv_o : (scr0[(@OfNat.ofNat Nat 4214 _)]'h4214).toNat = mv.toNat := rfl
  have hnv_o : (scr0[(@OfNat.ofNat Nat 4192 _)]'h4192).toNat = nv.toNat := rfl
  have hnc_o : (scr0[(@OfNat.ofNat Nat 4193 _)]'h4193).toNat = nc.toNat := rfl
  have hacap_o : (scr0[(@OfNat.ofNat Nat 4207 _)]'h4207).toNat = acap.toNat := rfl
  dsimp only [fidCorePhase2TraceExpr]
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32])
    (fun rem_t (ti, ()) mt => ∃ scrt : List (BitVec 32),
      FidCoreInv scr0 mv nc scrt ∧ ti.toNat ≤ mv.toNat ∧
      rem_t = ti.toNat ∧ (FullMem c (m8ScrSt s scrt) ⋆ R) mt) ?_ ?_
  · rintro Lt rem_t ⟨ti, ⟨⟩⟩ mt hLt ⟨scrt, hikt, hti_le, rfl, hmt⟩
    clear hikm hmb
    have hlt : scrt.length = scr0.length := hikt.2.1
    c0_hsplit
    · have hti_pos : 0 < ti.toNat := hc
      have hti1 : (ti - 1#32).toNat = ti.toNat - 1 := m8_bv32_sub1_toNat hti_pos
      let ti' := ti - 1#32
      have htr_e := fid_k6_off_add (mv := mv) (k := 5) (x := ti')
        hmv_hi (by decide) (by dsimp only [ti']; rw [hti1]; omega)
      have htr_b : ((4224 + 5 * mv + ti').setWidth 64).toNat < scrt.length := by
        rw [hlt, htr_e]; dsimp only [ti']; rw [hti1]; omega
      let v := (scrt[((4224 + 5 * mv + ti').setWidth 64).toNat]'htr_b) >>> (1 : Nat)
      c0_hsplit
      · c0_hsteps!; exact hLt ti'.toNat (ti', ()) mt
          (by dsimp only [ti']; rw [hti1]; omega)
          ⟨scrt, hikt, by dsimp only [ti']; rw [hti1]; omega, rfl, hmt⟩
      · have hv_lt : v.toNat < nv.toNat := by
          have hc' := hc; fid_norm_ofnat
          simp (disch := fid_omega) only [bv_c0, Nat.reducePow, BitVec.reduceToNat] at hc'
          try dsimp only [mv, nv] at hc'
          have hsub := fid_sub1_mod32 0 ti.toNat hti_pos (by omega)
          simp only [Nat.zero_add] at hsub
          have hadd : (4224 + 5 * (scr0[4214]'h4214).toNat +
                (4294967296 - 1 + ti.toNat)) % 4294967296 =
                4224 + 5 * mv.toNat + (ti.toNat - 1) := by
            rw [Nat.add_mod, hsub]; dsimp only [mv]; omega
          have hidx_eq : scrt[(4224 + 5 * (scr0[4214]'h4214).toNat +
                (4294967296 - 1 + ti.toNat)) % 4294967296]'(by
                  rw [hadd, hlt]; exact fidCore_mv_lt 5
                    (Nat.le_trans (Nat.sub_le ti.toNat 1) hti_le) hmv_lo hbge) =
                scrt[((4224 + 5 * mv + ti').setWidth 64).toNat]'htr_b :=
            m8_k6_get_congr (by rw [hadd, htr_e]; dsimp only [ti']; rw [hti1]) _ _
          rw [hidx_eq] at hc'; dsimp only [v]
          rw [m8_bv32_lshr1_toNat, ← hnv_d]; exact Nat.lt_of_not_le hc'
        have hfl_e := fid_k6_off_add (mv := mv) (k := 6) (x := v) hmv_hi (by decide) (by omega)
        have hfl_b : ((4224 + 6 * mv + v).setWidth 64).toNat < scrt.length := by
          rw [hlt, hfl_e]
          exact fidCore_mv_lt 6 (Nat.le_trans (Nat.le_of_lt hv_lt) hnv_le) hmv_lo hbge
        c0_hsplit
        · c0_hsteps!; exact hLt ti'.toNat (ti', ()) mt
            (by dsimp only [ti']; rw [hti1]; omega)
            ⟨scrt, hikt, by dsimp only [ti']; rw [hti1]; omega, rfl, hmt⟩
        · have hrs_e := fid_k6_off_add1 (mv := mv) (x := v) hmv_hi (by omega)
          let scrt1 := scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat
            ((scrt[((4224 + 6 * mv + v).setWidth 64).toNat]'hfl_b) &&& ~~~2#32)
          have hikt1 := fidCoreInv_set_flags_e h4214 hmv_eq hikt
            (Nat.lt_of_lt_of_le hv_lt hnv_le) hfl_e
            ((scrt[((4224 + 6 * mv + v).setWidth 64).toNat]'hfl_b) &&& ~~~2#32)
          have hlt1 : scrt1.length = scr0.length := hikt1.2.1
          have hrs_b : ((4224 + mv + v).setWidth 64).toNat < scrt1.length := by
            rw [hlt1, hrs_e]
            exact fidCore_1_lt (Nat.le_trans (Nat.le_of_lt hv_lt) hnv_le) hmv_lo hbge
          c0_hsteps_nogrp; c0_hsplit
          · c0_hsteps!; exact hLt ti'.toNat (ti', ()) _
              (by dsimp only [ti']; rw [hti1]; omega)
              ⟨scrt1, hikt1, by dsimp only [ti']; rw [hti1]; omega, rfl, hm⟩
          · let rsn := scrt1[((4224 + mv + v).setWidth 64).toNat]'hrs_b
            have hrsn_lt : rsn.toNat < nc.toNat := by
              have hc' := hc; fid_norm_ofnat
              simp (disch := fid_omega) only [bv_c0, Nat.reducePow, BitVec.reduceToNat] at hc'
              try dsimp only [mv, nc] at hc'
              exact fidCore_rsn_lt h4214 hmv_d h4193 hnc_d rfl hlt hmv_hi
                hti_pos hti_le hti1 htr_e htr_b
                (by dsimp only [v]; rw [m8_bv32_lshr1_toNat])
                (Nat.lt_of_lt_of_le hv_lt hnv_le) hfl_e hrs_e hrs_b rfl hc'
            clear hc
            have hmr_e := fid_k6_off_add (mv := mv) (k := 33) (x := rsn)
              hmv_hi (by decide) (by omega)
            have hor_e := fid_k6_off_add (mv := mv) (k := 29) (x := rsn)
              hmv_hi (by decide) (by omega)
            have hmr_b : ((4224 + 33 * mv + rsn).setWidth 64).toNat < scrt1.length := by
              rw [hlt1, hmr_e]
              exact fidCore_k_lt 33 (Nat.le_trans (Nat.le_of_lt hrsn_lt) hnc_le) hmv_lo hbge
            have hor_b : ((4224 + 29 * mv + rsn).setWidth 64).toNat < scrt1.length := by
              rw [hlt1, hor_e]
              exact fidCore_k_lt 29 (Nat.le_trans (Nat.le_of_lt hrsn_lt) hnc_le) hmv_lo hbge
            let mr := scrt1[((4224 + 33 * mv + rsn).setWidth 64).toNat]'hmr_b
            let scrt2 := scrt1.set ((4224 + 33 * mv + rsn).setWidth 64).toNat
              (mr ||| 0x80000000#32)
            have hikt2 : FidCoreInv scr0 mv nc scrt2 :=
              fidCoreInv_set_meta_pres h4214 hmv_eq hnc_le hikt1 hrsn_lt
                hmr_e hmr_b (m8_km_core_or_pres _)
            have hlt2 : scrt2.length = scr0.length := hikt2.2.1
            have hor_b2 : ((4224 + 29 * mv + rsn).setWidth 64).toNat < scrt2.length := by
              rw [hlt2, hor_e]
              exact fidCore_k_lt 29 (Nat.le_trans (Nat.le_of_lt hrsn_lt) hnc_le) hmv_lo hbge
            have hmr_b2 : ((4224 + 33 * mv + rsn).setWidth 64).toNat < scrt2.length := by
              rw [hlt2, hmr_e]
              exact fidCore_k_lt 33 (Nat.le_trans (Nat.le_of_lt hrsn_lt) hnc_le) hmv_lo hbge
            have ⟨hcl_t2, _, _, hlen_t2⟩ := fidCore_clause_ok_bnds
              h4214 hmv_eq h4193 hnc_eq h4207 hac_eq hmv_hi hnc_le
              hikt2 hrsn_lt hor_e hmr_e hor_b2 hmr_b2
            c0_hsteps_nogrp
            let roff := scrt2[((4224 + 29 * mv + rsn).setWidth 64).toNat]'hor_b2
            let rsz := (scrt2[((4224 + 33 * mv + rsn).setWidth 64).toNat]'hmr_b2) &&& 0xFFFF#32
            have hrsz_le : rsz.toNat ≤ 65535 := m8_and_ffff_le _
            have hroff_bnd : roff.toNat + rsz.toNat ≤ acap.toNat := hcl_t2
            refine wp_join0 invS
              (fun _ mj ⟨scrj, hikj, hmj⟩ => by
                c0_hsteps!; exact hLt ti'.toNat (ti', ()) mj
                  (by clear hLt hikj hmj; dsimp only [ti']; rw [hti1]; omega)
                  ⟨scrj, hikj, by clear hLt hikj hmj; dsimp only [ti']; rw [hti1]; omega, rfl, hmj⟩)
              (fun Jc hJc => by
                c0_hsteps_nogrp; c0_hsplit
                · clear hc; c0_hsteps_nogrp
                  refine wp_loop_group (ts := [i32])
                    (fun rem_j (j, ()) mj => ∃ scrj : List (BitVec 32),
                      FidCoreInv scr0 mv nc scrj ∧ j.toNat ≤ rsz.toNat ∧
                      rem_j = rsz.toNat - j.toNat ∧
                      (FullMem c (m8ScrSt s scrj) ⋆ R) mj) ?_ ?_
                  · rintro Lj rem_j ⟨j, ⟨⟩⟩ mj hLj ⟨scrj, hikj, hj_le, rfl, hmj⟩
                    have hlj : scrj.length = scr0.length := hikj.2.1
                    c0_hsplit
                    · have hj_lt : j.toNat < rsz.toNat := by
                        have hc' := hc; clear hc; fid_norm_ofnat
                        simp only [bv_c0, Nat.reducePow, BitVec.reduceToNat] at hc'
                        try dsimp only [mv] at hc'
                        exact fidCore_trace_hj_lt h4214 hmv_d hmv_hi hlt
                          hti_pos hti_le hti1 htr_e (hlt ▸ htr_b)
                          (by dsimp only [v]; rw [m8_bv32_lshr1_toNat])
                          (Nat.lt_of_lt_of_le hv_lt hnv_le) hfl_e hfl_b
                          hrs_e hrs_b rfl (Nat.lt_of_lt_of_le hrsn_lt hnc_le) hmr_e hmr_b rfl
                          (by dsimp only [rsz, scrt2]; rw [List.getElem_set_self]) hc'
                      clear hc
                      have hj1 : (j + 1#32).toNat = j.toNat + 1 :=
                        m8_bv32_add1_toNat hj_lt
                          (by clear hikt1 hikt2 hcl_t2 hm hmj hikj hLt hLj; omega)
                      have har_e := fid_k6_off_add2 (mv := mv) (k := 45) (x := roff) (y := j)
                        hmv_hi (by decide) (by clear hikt1 hikt2 hcl_t2 hm hmj hikj hLt hLj; omega)
                      have har_b : ((4224 + 45 * mv + roff + j).setWidth 64).toNat <
                          scrj.length := by
                        clear hikt1 hikt2 hcl_t2 hm hmj hikj; rw [hlj, har_e]; omega
                      let lv := (scrj[((4224 + 45 * mv + roff + j).setWidth 64).toNat]'har_b) >>>
                        (1 : Nat)
                      c0_hsteps_nogrp
                      refine wp_join0 invS
                        (fun _ mj' ⟨scrj', hikj', hmj'⟩ => by
                          c0_hsteps!
                          exact hLj (rsz.toNat - (j + 1#32).toNat) (j + 1#32, ()) mj' (by
                              clear hLj hikj' hmj' hm hmj hikj hikt1 hikt2 hcl_t2 hLt; omega)
                            ⟨scrj', hikj', by
                              clear hLj hikj' hmj' hm hmj hikj hikt1 hikt2 hcl_t2 hLt; omega,
                              rfl, hmj'⟩)
                        (fun Js hJs => by
                          c0_hsplit
                          · have hlv_lt : lv.toNat < nv.toNat := by
                              have hc' := hc; clear hc; fid_norm_ofnat
                              simp only [bv_c0, Nat.reducePow, BitVec.reduceToNat] at hc'
                              try dsimp only [mv, nv] at hc'
                              exact fidCore_trace_lv_lt h4214 hmv_d h4192 hnv_d
                                hmv_hi hlt hti_pos hti_le hti1 htr_e (hlt ▸ htr_b)
                                (by dsimp only [v]; rw [m8_bv32_lshr1_toNat])
                                (Nat.lt_of_lt_of_le hv_lt hnv_le) hfl_e hfl_b hrs_e hrs_b rfl
                                (show rsn.toNat < 8 * mv.toNat from
                                  Nat.lt_of_lt_of_le hrsn_lt
                                    (Nat.le_trans hnc_le (Nat.mul_le_mul_right _ (by decide))))
                                hmr_e hmr_b rfl rfl rfl
                                (fid_k6_off_add (mv := mv) (k := 29) (x := rsn) hmv_hi (by decide)
                                  (Nat.lt_of_lt_of_le hrsn_lt (Nat.le_trans hnc_le
                                    (Nat.le_trans (Nat.mul_le_mul_left 4 hmv_hi) (by decide)))))
                                hor_b2 rfl har_e har_b hc'
                            clear hc
                            c0_hsplit
                            · have hfl_lv := fid_k6_off_add (mv := mv) (k := 6) (x := lv) hmv_hi
                                (by decide) (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlv_lt hnv_le)
                                  (Nat.le_trans hmv_hi (by decide)))
                              have hfl_lvb : ((4224 + 6 * mv + lv).setWidth 64).toNat <
                                  scrj.length := by
                                rw [hlj, hfl_lv]
                                exact fidCore_b6_lt (Nat.lt_of_lt_of_le hlv_lt hnv_le) hbge
                              c0_hsteps!
                              exact hJs _ ⟨_, fidCoreInv_set_flags_e h4214 hmv_eq hikj
                                (Nat.lt_of_lt_of_le hlv_lt hnv_le) hfl_lv _, hm⟩
                            · c0_hsteps!; exact hJs _ ⟨scrj, hikj, hmj⟩
                          · c0_hsteps!; exact hJs _ ⟨scrj, hikj, hmj⟩)
                    · c0_hsteps!; exact hJc mj ⟨scrj, hikj, hmj⟩
                  · intro Lj hLj; c0_hsteps!; exact hLj rsz.toNat (0#32, ())
                      _ ⟨scrt2, hikt2, Nat.zero_le _, by simp, hm⟩
                · c0_hsteps!; exact hJc _ ⟨scrt2, hikt2, hm⟩)
    · -- Clear `flags & 2` on `0 ..< nv` after traceback
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i32])
        (fun rem_f (i, ()) mf => ∃ scrf : List (BitVec 32),
          FidCoreInv scr0 mv nc scrf ∧ i.toNat ≤ nv.toNat ∧
          rem_f = nv.toNat - i.toNat ∧
          (FullMem c (m8ScrSt s scrf) ⋆ R) mf) ?_ ?_
      · rintro Lf rem_f ⟨i, ⟨⟩⟩ mf hLf ⟨scrf, hikf, hi_le, rfl, hmf⟩
        have hlf : scrf.length = scr0.length := hikf.2.1
        c0_hsplit
        · have hi_lt : i.toNat < nv.toNat := hc
          have hi1 : (i + 1#32).toNat = i.toNat + 1 :=
            m8_bv32_add1_toNat hi_lt (by clear hLf hikf hmf; omega)
          have hfl_e := fid_k6_off_add (mv := mv) (k := 6) (x := i) hmv_hi (by decide)
            (by clear hLf hikf hmf; omega)
          have hfl_b : ((4224 + 6 * mv + i).setWidth 64).toNat < scrf.length := by
            rw [hlf, hfl_e]; exact fidCore_mv_lt 6 (Nat.le_trans (Nat.le_of_lt hi_lt) hnv_le)
              hmv_lo hbge
          c0_hsteps!
          exact hLf (nv.toNat - (i + 1#32).toNat) (i + 1#32, ()) _ (by clear hLf hikf; omega)
            ⟨_, fidCoreInv_set_flags_e h4214 hmv_eq hikf (by clear hLf hikf; omega) hfl_e _,
              by clear hLf hikf; omega, rfl, hm⟩
        · c0_hsteps!; exact hJ2 _ scrf mf hikf hmf
      · intro Lf hLf; c0_hsteps!
        exact hLf nv.toNat (0#32, ()) mt ⟨scrt, hikt, Nat.zero_le _, by simp, hmt⟩
  · intro Lt hLt; c0_hsteps!
    exact hLt ti0.toNat (ti0, ()) mb ⟨scrm, hikm, hti0, rfl, hmb⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Definition
