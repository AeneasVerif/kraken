/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1

/-!
# Canonical Specification Helpers (`Proof.Definition.SpecHelpers`)

Provides `_noExit`, `_intro`, `_elim` wrappers for all `24` specs in `Proof.Definition.Spec`,
`TmkZero.congr`, `K6BufOk` structural lemmas, `fidK6MaxV` bounds/bv64 lemmas, `FidK6BufOk`
structural lemmas, and `fid_k6_off_*` dynamic scratch-offset lemmas (`0` legacy imports,
`0` `@[expose]` on theorems/sections, every decl `<= 450` LOC, every line `<= 100` chars).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Definition

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open Kraken.Bedrock2.Test

public section

/-! ## 1. `TmkZero` & M7 `K6BufOk` Lemmas -/

theorem Spec.TmkZero.congr {s s' : FullState} (h : TmkZero s)
    (hcv : s'.core.cur_vars = s.core.cur_vars)
    (ht : s'.scratch.tarjan_mark = s.scratch.tarjan_mark) : TmkZero s' := by
  intro v hv; rw [ht]; exact h v (hcv ▸ hv)

theorem Spec.K6BufOk.mk_of {kbuf : List (BitVec 32)}
    (hlen_ge : 2912 + (kbuf[15]?.getD 0#32).toNat ≤ kbuf.length)
    (hlen_lt : kbuf.length < 2 ^ 28)
    (hnc : (kbuf[1]?.getD 0#32).toNat ≤ 256)
    (halen : (kbuf[14]?.getD 0#32).toNat ≤ (kbuf[15]?.getD 0#32).toNat)
    (hcl : ∀ cid < (kbuf[1]?.getD 0#32).toNat,
      let off := (kbuf[1888 + cid]?.getD 0#32).toNat
      let cm := kbuf[2144 + cid]?.getD 0#32
      let sz := (cm &&& 0xFFFF#32).toNat
      let aux := (kbuf[2400 + cid]?.getD 0#32).toNat
      off + sz ≤ (kbuf[15]?.getD 0#32).toNat ∧
        ((cm &&& 0x40000000#32) ≠ 0#32 → off + sz + aux ≤ (kbuf[15]?.getD 0#32).toNat)) :
    K6BufOk kbuf :=
  ⟨hlen_ge, hlen_lt, hnc, halen, hcl⟩

theorem Spec.K6BufOk.length_ge {kbuf : List (BitVec 32)} (h : K6BufOk kbuf) :
    2912 + (kbuf[15]?.getD 0#32).toNat ≤ kbuf.length := h.1

theorem Spec.K6BufOk.length_lt {kbuf : List (BitVec 32)} (h : K6BufOk kbuf) :
    kbuf.length < 2 ^ 28 := h.2.1

theorem Spec.K6BufOk.nc_le {kbuf : List (BitVec 32)} (h : K6BufOk kbuf) :
    (kbuf[1]?.getD 0#32).toNat ≤ 256 := h.2.2.1

theorem Spec.K6BufOk.alen_le {kbuf : List (BitVec 32)} (h : K6BufOk kbuf) :
    (kbuf[14]?.getD 0#32).toNat ≤ (kbuf[15]?.getD 0#32).toNat := h.2.2.2.1

theorem Spec.K6BufOk.clause_ok {kbuf : List (BitVec 32)} (h : K6BufOk kbuf) {cid : Nat}
    (hcid : cid < (kbuf[1]?.getD 0#32).toNat) :
    let off := (kbuf[1888 + cid]?.getD 0#32).toNat
    let cm := kbuf[2144 + cid]?.getD 0#32
    let sz := (cm &&& 0xFFFF#32).toNat
    let aux := (kbuf[2400 + cid]?.getD 0#32).toNat
    off + sz ≤ (kbuf[15]?.getD 0#32).toNat ∧
      ((cm &&& 0x40000000#32) ≠ 0#32 → off + sz + aux ≤ (kbuf[15]?.getD 0#32).toNat) :=
  h.2.2.2.2 cid hcid

theorem Spec.K6BufOk.base_ge {kbuf : List (BitVec 32)} (h : K6BufOk kbuf) :
    2912 ≤ kbuf.length := by have := h.length_ge; omega

theorem k6BufOk_of_frame {kbuf kbuf' : List (BitVec 32)} (h : K6BufOk kbuf)
    (hlen : kbuf'.length = kbuf.length)
    (hkeep : ∀ idx < kbuf.length,
      (idx = 1 ∨ idx = 14 ∨ idx = 15 ∨ (1888 ≤ idx ∧ idx < 2656)) →
      kbuf'[idx]? = kbuf[idx]?) :
    K6BufOk kbuf' := by
  have hb := h.base_ge
  have hk1 : kbuf'[1]? = kbuf[1]? := hkeep 1 (by omega) (Or.inl rfl)
  have hk14 : kbuf'[14]? = kbuf[14]? := hkeep 14 (by omega) (Or.inr (Or.inl rfl))
  have hk15 : kbuf'[15]? = kbuf[15]? := hkeep 15 (by omega) (Or.inr (Or.inr (Or.inl rfl)))
  refine ⟨by rw [hk15, hlen]; exact h.length_ge, by rw [hlen]; exact h.length_lt,
    by rw [hk1]; exact h.nc_le, by rw [hk14, hk15]; exact h.alen_le, fun cid hcid => ?_⟩
  rw [hk1] at hcid
  have hnc := h.nc_le
  have ho : kbuf'[1888 + cid]? = kbuf[1888 + cid]? :=
    hkeep (1888 + cid) (by omega) (Or.inr (Or.inr (Or.inr (by omega))))
  have hm : kbuf'[2144 + cid]? = kbuf[2144 + cid]? :=
    hkeep (2144 + cid) (by omega) (Or.inr (Or.inr (Or.inr (by omega))))
  have ha : kbuf'[2400 + cid]? = kbuf[2400 + cid]? :=
    hkeep (2400 + cid) (by omega) (Or.inr (Or.inr (Or.inr (by omega))))
  rw [ho, hm, ha, hk15]
  exact h.clause_ok hcid

theorem k6BufOk_set_core_meta {kbuf : List (BitVec 32)} (h : K6BufOk kbuf)
    {cid : Nat} (hcid : cid < 256) {v : BitVec 32}
    (hsz : (v &&& 0xFFFF#32) = ((kbuf[2144 + cid]?.getD 0#32) &&& 0xFFFF#32))
    (hlrn : (v &&& 0x40000000#32) = ((kbuf[2144 + cid]?.getD 0#32) &&& 0x40000000#32)) :
    K6BufOk (kbuf.set (2144 + cid) v) := by
  have hb := h.base_ge
  have hk1 : (kbuf.set (2144 + cid) v)[1]? = kbuf[1]? := List.getElem?_set_ne (by omega)
  have hk14 : (kbuf.set (2144 + cid) v)[14]? = kbuf[14]? := List.getElem?_set_ne (by omega)
  have hk15 : (kbuf.set (2144 + cid) v)[15]? = kbuf[15]? := List.getElem?_set_ne (by omega)
  refine ⟨by rw [hk15, List.length_set]; exact h.length_ge,
    by rw [List.length_set]; exact h.length_lt,
    by rw [hk1]; exact h.nc_le, by rw [hk14, hk15]; exact h.alen_le, fun j hj => ?_⟩
  rw [hk1] at hj
  have hnc := h.nc_le
  have ho : (kbuf.set (2144 + cid) v)[1888 + j]? = kbuf[1888 + j]? :=
    List.getElem?_set_ne (by omega)
  have ha : (kbuf.set (2144 + cid) v)[2400 + j]? = kbuf[2400 + j]? :=
    List.getElem?_set_ne (by omega)
  rw [ho, ha, hk15]
  by_cases heq : j = cid
  · subst heq
    dsimp only
    rw [List.getElem?_set_self (by omega), Option.getD_some, hsz, hlrn]
    exact h.clause_ok hj
  · rw [List.getElem?_set_ne (by omega)]
    exact h.clause_ok hj

theorem k6BufOk_set_flags {kbuf : List (BitVec 32)} (h : K6BufOk kbuf)
    {i : Nat} (hi : i < 64) (v : BitVec 32) :
    K6BufOk (kbuf.set (416 + i) v) :=
  k6BufOk_of_frame h List.length_set fun idx _ hor => by
    rcases hor with rfl | rfl | rfl | ⟨_, _⟩ <;> exact List.getElem?_set_ne (by omega)

/-! ## 2. Fidelity `fidK6MaxV`, `FidK6BufOk`, & Offset Helpers -/

theorem fidK6MaxV_eq_zero {cap : Nat} (h : cap < 16384) : fidK6MaxV cap = 0 := by
  unfold fidK6MaxV; simp [h]

theorem fidK6MaxV_bounds {cap : Nat} (hge : 16384 ≤ cap) :
    256 ≤ fidK6MaxV cap ∧ fidK6MaxV cap ≤ 8192 ∧ 4224 + 45 * fidK6MaxV cap ≤ cap := by
  unfold fidK6MaxV
  have hnot : ¬ cap < 16384 := by omega
  simp only [hnot, ↓reduceIte]
  split
  · exact ⟨by decide, by decide, by omega⟩
  · have h64 : ((cap - 4224) / 64) / 64 * 64 ≤ (cap - 4224) / 64 := by omega
    have hmul : 64 * ((cap - 4224) / 64) ≤ cap - 4224 := Nat.mul_div_le (cap - 4224) 64
    omega

theorem fidK6MaxV_16384 : fidK6MaxV 16384 = 256 := by decide
theorem fidK6MaxV_65536 : fidK6MaxV 65536 = 896 := by decide
theorem fidK6MaxV_524288 : fidK6MaxV 524288 = 8192 := by decide

private theorem fid_bv64_and_not63 (x : BitVec 64) :
    (x &&& 0xFFFFFFFFFFFFFFC0#64).toNat = x.toNat / 64 * 64 := by
  have heq : x &&& 0xFFFFFFFFFFFFFFC0#64 = (x >>> (6 : Nat)) <<< (6 : Nat) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, hi,
      decide_true, Bool.true_and]
    by_cases h6 : i < 6
    · have hf : (0xFFFFFFFFFFFFFFC0#64).getLsbD i = false := by revert i hi h6; decide
      simp [h6, hf]
    · have ht : (0xFFFFFFFFFFFFFFC0#64).getLsbD i = true := by
        have hge : 6 ≤ i := by omega
        revert i hi h6 hge; decide
      simp [h6, ht]; rw [Nat.add_sub_cancel' (by omega)]
  rw [heq]
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  have := x.isLt; rw [Nat.mod_eq_of_lt (by omega)]

theorem fidK6MaxV_bv64_eq {cap : Nat} (hlt : cap < 2 ^ 64) :
    let cap64 := BitVec.ofNat 64 cap
    let r64 : BitVec 64 :=
      if cap64 < 16384#64 then 0#64
      else if 524288#64 ≤ cap64 then 8192#64
      else
        let raw := ((cap64 - 4224#64) / 64#64) &&& 0xFFFFFFFFFFFFFFC0#64
        if raw < 256#64 then 256#64 else if 8192#64 < raw then 8192#64 else raw
    r64 = BitVec.ofNat 64 (fidK6MaxV cap) := by
  dsimp only; unfold fidK6MaxV
  by_cases h1 : cap < 16384
  · have hb1 : BitVec.ofNat 64 cap < 16384#64 := by
      change (BitVec.ofNat 64 cap).toNat < (16384#64).toNat; bv_omega
    simp [h1, hb1]
  · have hb1 : ¬ BitVec.ofNat 64 cap < 16384#64 := by
      change ¬ (BitVec.ofNat 64 cap).toNat < (16384#64).toNat; bv_omega
    simp only [h1, hb1, ↓reduceIte]
    by_cases h2 : 524288 ≤ cap
    · have hb2 : 524288#64 ≤ BitVec.ofNat 64 cap := by
        change (524288#64).toNat ≤ (BitVec.ofNat 64 cap).toNat; bv_omega
      simp [h2, hb2]
    · have hb2 : ¬ 524288#64 ≤ BitVec.ofNat 64 cap := by
        change ¬ (524288#64).toNat ≤ (BitVec.ofNat 64 cap).toNat; bv_omega
      simp only [h2, hb2, ↓reduceIte]
      have hsub : (BitVec.ofNat 64 cap - 4224#64).toNat = cap - 4224 := by bv_omega
      have hdiv : ((BitVec.ofNat 64 cap - 4224#64) / 64#64).toNat = (cap - 4224) / 64 := by
        rw [BitVec.toNat_udiv, hsub]; rfl
      have hraw : (((BitVec.ofNat 64 cap - 4224#64) / 64#64) &&& 0xFFFFFFFFFFFFFFC0#64).toNat =
          ((cap - 4224) / 64) / 64 * 64 := by
        rw [fid_bv64_and_not63, hdiv]
      apply BitVec.eq_of_toNat_eq
      by_cases hr1 : ((cap - 4224) / 64) / 64 * 64 < 256
      · have hb :
            (((BitVec.ofNat 64 cap - 4224#64) / 64#64) &&& 0xFFFFFFFFFFFFFFC0#64) < 256#64 := by
          change (((BitVec.ofNat 64 cap - 4224#64) / 64#64) &&& 0xFFFFFFFFFFFFFFC0#64).toNat < 256
          rw [hraw]; exact hr1
        simp only [hb, ↓reduceIte]
        rw [show max 256 (min 8192 (((cap - 4224) / 64) / 64 * 64)) = 256 by omega]
      · have hb :
            ¬ (((BitVec.ofNat 64 cap - 4224#64) / 64#64) &&& 0xFFFFFFFFFFFFFFC0#64) < 256#64 := by
          change ¬ (((BitVec.ofNat 64 cap - 4224#64) / 64#64) &&&
            0xFFFFFFFFFFFFFFC0#64).toNat < 256
          rw [hraw]; exact hr1
        simp only [hb, ↓reduceIte]
        by_cases hr2 : 8192 < ((cap - 4224) / 64) / 64 * 64
        · have hb2 : (8192#64 : BitVec 64) <
              (((BitVec.ofNat 64 cap - 4224#64) / 64#64) &&& 0xFFFFFFFFFFFFFFC0#64) := by
            change 8192 < (((BitVec.ofNat 64 cap - 4224#64) / 64#64) &&&
              0xFFFFFFFFFFFFFFC0#64).toNat
            rw [hraw]; exact hr2
          simp only [hb2, ↓reduceIte]
          rw [show max 256 (min 8192 (((cap - 4224) / 64) / 64 * 64)) = 8192 by omega]
        · have hb2 : ¬ (8192#64 : BitVec 64) <
              (((BitVec.ofNat 64 cap - 4224#64) / 64#64) &&& 0xFFFFFFFFFFFFFFC0#64) := by
            change ¬ 8192 < (((BitVec.ofNat 64 cap - 4224#64) / 64#64) &&&
              0xFFFFFFFFFFFFFFC0#64).toNat
            rw [hraw]; exact hr2
          simp only [hb2, ↓reduceIte, hraw, BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem Spec.FidK6BufOk.mv_lo {scr : List (BitVec 32)} (h : FidK6BufOk scr) :
    256 ≤ (scr[4214]?.getD 0#32).toNat := h.1

theorem Spec.FidK6BufOk.mv_hi {scr : List (BitVec 32)} (h : FidK6BufOk scr) :
    (scr[4214]?.getD 0#32).toNat ≤ 8192 := h.2.1

theorem Spec.FidK6BufOk.length_ge {scr : List (BitVec 32)} (h : FidK6BufOk scr) :
    4224 + 45 * (scr[4214]?.getD 0#32).toNat + (scr[4207]?.getD 0#32).toNat ≤ scr.length :=
  h.2.2.1

theorem Spec.FidK6BufOk.length_lt {scr : List (BitVec 32)} (h : FidK6BufOk scr) :
    scr.length < 2 ^ 30 := h.2.2.2.1

theorem Spec.FidK6BufOk.nc_le {scr : List (BitVec 32)} (h : FidK6BufOk scr) :
    (scr[4193]?.getD 0#32).toNat ≤ 4 * (scr[4214]?.getD 0#32).toNat := h.2.2.2.2.1

theorem Spec.FidK6BufOk.alen_le {scr : List (BitVec 32)} (h : FidK6BufOk scr) :
    (scr[4206]?.getD 0#32).toNat ≤ (scr[4207]?.getD 0#32).toNat := h.2.2.2.2.2.1

theorem Spec.FidK6BufOk.clause_ok {scr : List (BitVec 32)} (h : FidK6BufOk scr) {cid : Nat}
    (hcid : cid < (scr[4193]?.getD 0#32).toNat) :
    let mv := (scr[4214]?.getD 0#32).toNat
    let off := (scr[4224 + 29 * mv + cid]?.getD 0#32).toNat
    let cm := scr[4224 + 33 * mv + cid]?.getD 0#32
    let sz := (cm &&& 0xFFFF#32).toNat
    let aux := (scr[4224 + 37 * mv + cid]?.getD 0#32).toNat
    off + sz ≤ (scr[4207]?.getD 0#32).toNat ∧
      ((cm &&& 0x40000000#32) ≠ 0#32 → off + sz + aux ≤ (scr[4207]?.getD 0#32).toNat) :=
  h.2.2.2.2.2.2 cid hcid

theorem Spec.FidK6BufOk.base_ge {scr : List (BitVec 32)} (h : FidK6BufOk scr) :
    4224 + 45 * (scr[4214]?.getD 0#32).toNat ≤ scr.length := by
  have := h.length_ge; omega

theorem Spec.FidK6BufOk.min_len {scr : List (BitVec 32)} (h : FidK6BufOk scr) :
    15744 ≤ scr.length := by
  have h1 := h.mv_lo; have h2 := h.base_ge; omega

theorem fidK6BufOk_of_frame {scr scr' : List (BitVec 32)} (h : FidK6BufOk scr)
    (hlen : scr'.length = scr.length)
    (hkeep : ∀ idx < scr.length,
      let mv := (scr[4214]?.getD 0#32).toNat
      (idx = 4193 ∨ idx = 4206 ∨ idx = 4207 ∨ idx = 4214 ∨
        (4224 + 29 * mv ≤ idx ∧ idx < 4224 + 41 * mv)) →
      scr'[idx]? = scr[idx]?) :
    FidK6BufOk scr' := by
  have hmv_lo := h.mv_lo; have hmv_hi := h.mv_hi; have hb := h.base_ge
  have hk16 : scr'[4214]? = scr[4214]? :=
    hkeep 4214 (by omega) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hk1 : scr'[4193]? = scr[4193]? := hkeep 4193 (by omega) (Or.inl rfl)
  have hk14 : scr'[4206]? = scr[4206]? := hkeep 4206 (by omega) (Or.inr (Or.inl rfl))
  have hk15 : scr'[4207]? = scr[4207]? := hkeep 4207 (by omega) (Or.inr (Or.inr (Or.inl rfl)))
  refine ⟨by rw [hk16]; exact hmv_lo, by rw [hk16]; exact hmv_hi,
    by rw [hk16, hk15, hlen]; exact h.length_ge, by rw [hlen]; exact h.length_lt,
    by rw [hk1, hk16]; exact h.nc_le, by rw [hk14, hk15]; exact h.alen_le, fun cid hcid => ?_⟩
  rw [hk1] at hcid
  have hnc := h.nc_le
  let mv := (scr[4214]?.getD 0#32).toNat
  have ho : scr'[4224 + 29 * mv + cid]? = scr[4224 + 29 * mv + cid]? :=
    hkeep (4224 + 29 * mv + cid) (by omega) (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))
  have hm : scr'[4224 + 33 * mv + cid]? = scr[4224 + 33 * mv + cid]? :=
    hkeep (4224 + 33 * mv + cid) (by omega) (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))
  have ha : scr'[4224 + 37 * mv + cid]? = scr[4224 + 37 * mv + cid]? :=
    hkeep (4224 + 37 * mv + cid) (by omega) (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))
  dsimp only; rw [hk16, ho, hm, ha, hk15]
  exact h.clause_ok hcid

theorem fidK6BufOk_set_core_meta {scr : List (BitVec 32)} (h : FidK6BufOk scr)
    {cid : Nat} (hcid : cid < 4 * (scr[4214]?.getD 0#32).toNat) {v : BitVec 32}
    (hsz : (v &&& 0xFFFF#32) =
      ((scr[4224 + 33 * (scr[4214]?.getD 0#32).toNat + cid]?.getD 0#32) &&& 0xFFFF#32))
    (hlrn : (v &&& 0x40000000#32) =
      ((scr[4224 + 33 * (scr[4214]?.getD 0#32).toNat + cid]?.getD 0#32) &&& 0x40000000#32)) :
    FidK6BufOk (scr.set (4224 + 33 * (scr[4214]?.getD 0#32).toNat + cid) v) := by
  let mv := (scr[4214]?.getD 0#32).toNat
  have hmv_lo := h.mv_lo; have hmv_hi := h.mv_hi; have hb := h.base_ge
  have hk16 : (scr.set (4224 + 33 * mv + cid) v)[4214]? = scr[4214]? :=
    List.getElem?_set_ne (by omega)
  have hk1 : (scr.set (4224 + 33 * mv + cid) v)[4193]? = scr[4193]? :=
    List.getElem?_set_ne (by omega)
  have hk14 : (scr.set (4224 + 33 * mv + cid) v)[4206]? = scr[4206]? :=
    List.getElem?_set_ne (by omega)
  have hk15 : (scr.set (4224 + 33 * mv + cid) v)[4207]? = scr[4207]? :=
    List.getElem?_set_ne (by omega)
  refine ⟨by rw [hk16]; exact hmv_lo, by rw [hk16]; exact hmv_hi,
    by rw [hk16, hk15, List.length_set]; exact h.length_ge,
    by rw [List.length_set]; exact h.length_lt,
    by rw [hk1, hk16]; exact h.nc_le, by rw [hk14, hk15]; exact h.alen_le, fun j hj => ?_⟩
  rw [hk1] at hj
  have hnc := h.nc_le
  have ho : (scr.set (4224 + 33 * mv + cid) v)[4224 + 29 * mv + j]? = scr[4224 + 29 * mv + j]? :=
    List.getElem?_set_ne (by omega)
  have ha : (scr.set (4224 + 33 * mv + cid) v)[4224 + 37 * mv + j]? = scr[4224 + 37 * mv + j]? :=
    List.getElem?_set_ne (by omega)
  dsimp only; rw [hk16, ho, ha, hk15]
  by_cases heq : j = cid
  · subst heq
    rw [List.getElem?_set_self (by omega), Option.getD_some, hsz, hlrn]
    exact h.clause_ok hj
  · rw [List.getElem?_set_ne (by omega)]
    exact h.clause_ok hj

theorem fidK6BufOk_set_flags {scr : List (BitVec 32)} (h : FidK6BufOk scr)
    {i : Nat} (hi : i < (scr[4214]?.getD 0#32).toNat) (v : BitVec 32) :
    FidK6BufOk (scr.set (4224 + 6 * (scr[4214]?.getD 0#32).toNat + i) v) := by
  have hmv_lo := h.mv_lo
  refine fidK6BufOk_of_frame h List.length_set fun idx _ hor => ?_
  rcases hor with rfl | rfl | rfl | rfl | ⟨_, _⟩ <;> exact List.getElem?_set_ne (by omega)

theorem fid_bv32_shl2_toNat {x : BitVec 32} (hx : 4 * x.toNat < 2 ^ 32) :
    (x <<< (2 : Nat)).toNat = 4 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega

theorem fid_zext32_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat :=
  bv_c0_zext32_64 x

theorem fid_k6_off_k {mv : BitVec 32} {k : Nat}
    (hmv : mv.toNat ≤ 8192) (hk : k ≤ 45) :
    ((4224 : BitVec 32) + (@OfNat.ofNat (BitVec 32) k (BitVec.instOfNat)) * mv).toNat =
      4224 + k * mv.toNat := by
  have hkm : k * mv.toNat ≤ 45 * 8192 := Nat.mul_le_mul hk hmv
  have hk_nat : (@OfNat.ofNat (BitVec 32) k (BitVec.instOfNat)).toNat = k := by
    change (BitVec.ofNat 32 k).toNat = k
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, BitVec.toNat_mul, show (4224 : BitVec 32).toNat = 4224 from rfl,
    hk_nat, Nat.mod_eq_of_lt (by omega : k * mv.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : 4224 + k * mv.toNat < 2 ^ 32)]

theorem fid_k6_off_add {mv : BitVec 32} {k : Nat} {x : BitVec 32}
    (hmv : mv.toNat ≤ 8192) (hk : k ≤ 45) (hx : x.toNat < 2 ^ 30) :
    (((4224 : BitVec 32) + (@OfNat.ofNat (BitVec 32) k (BitVec.instOfNat)) * mv + x).setWidth
      64).toNat = 4224 + k * mv.toNat + x.toNat := by
  have hkm : k * mv.toNat ≤ 45 * 8192 := Nat.mul_le_mul hk hmv
  rw [bv_c0_zext32_64, BitVec.toNat_add, fid_k6_off_k hmv hk,
    Nat.mod_eq_of_lt (by omega)]

theorem fid_k6_off_add0 {x : BitVec 32} (hx : x.toNat < 2 ^ 30) :
    (((4224 : BitVec 32) + x).setWidth 64).toNat = 4224 + x.toNat := by
  rw [bv_c0_zext32_64, BitVec.toNat_add, show (4224 : BitVec 32).toNat = 4224 from rfl,
    Nat.mod_eq_of_lt (by omega)]

theorem fid_k6_off_add1 {mv x : BitVec 32} (hmv : mv.toNat ≤ 8192) (hx : x.toNat < 2 ^ 30) :
    (((4224 : BitVec 32) + mv + x).setWidth 64).toNat = 4224 + mv.toNat + x.toNat := by
  rw [bv_c0_zext32_64, BitVec.toNat_add, BitVec.toNat_add,
    show (4224 : BitVec 32).toNat = 4224 from rfl,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem fid_k6_off_add2 {mv x y : BitVec 32} {k : Nat}
    (hmv : mv.toNat ≤ 8192) (hk : k ≤ 45) (hxy : x.toNat + y.toNat < 2 ^ 30) :
    (((4224 : BitVec 32) + (@OfNat.ofNat (BitVec 32) k (BitVec.instOfNat)) * mv + x +
      y).setWidth 64).toNat = 4224 + k * mv.toNat + x.toNat + y.toNat := by
  have hkm : k * mv.toNat ≤ 45 * 8192 := Nat.mul_le_mul hk hmv
  rw [bv_c0_zext32_64, BitVec.toNat_add, BitVec.toNat_add, fid_k6_off_k hmv hk,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem fid_k6_off_add3 {mv x y z : BitVec 32} {k : Nat}
    (hmv : mv.toNat ≤ 8192) (hk : k ≤ 45) (hxyz : x.toNat + y.toNat + z.toNat < 2 ^ 30) :
    (((4224 : BitVec 32) + (@OfNat.ofNat (BitVec 32) k (BitVec.instOfNat)) * mv + x + y +
      z).setWidth 64).toNat = 4224 + k * mv.toNat + x.toNat + y.toNat + z.toNat := by
  have hkm : k * mv.toNat ≤ 45 * 8192 := Nat.mul_le_mul hk hmv
  rw [bv_c0_zext32_64, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, fid_k6_off_k hmv hk,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-! ## 3. M7 `intro` / `elim` / `noExit` Wrappers -/

theorem fullK6WatchM7Spec_noExit :
    ∀ xs m Q X, fullK6WatchM7Spec xs m Q X →
      fullK6WatchM7Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullK6WatchM7Spec_intro {pk : BitVec 64} {cid l0 l1 sz : BitVec 32}
    {kbuf : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hlen : 2912 ≤ kbuf.length) (hm : (array (t := i32) pk kbuf ⋆ R) m)
    (hQ : ∀ kbuf' m', kbuf'.length = kbuf.length →
      (∀ idx < kbuf.length, (idx < 736 ∨ 1888 ≤ idx) → kbuf'[idx]? = kbuf[idx]?) →
      (array (t := i32) pk kbuf' ⋆ R) m' → Q () m') :
    fullK6WatchM7Spec (pk, cid, l0, l1, sz, ()) m Q X :=
  ⟨kbuf, R, hlen, hm, hQ⟩

theorem fullK6WatchM7Spec_elim {a m Q X} (h : fullK6WatchM7Spec a m Q X) :
    let (pk, _, _, _, _, _) := a
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      2912 ≤ kbuf.length ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ kbuf' m', kbuf'.length = kbuf.length →
        (∀ idx < kbuf.length, (idx < 736 ∨ 1888 ≤ idx) → kbuf'[idx]? = kbuf[idx]?) →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q () m' := by
  rcases a with ⟨pk, cid, l0, l1, sz, ⟨⟩⟩; exact h

theorem fullK6AssignM7Spec_noExit :
    ∀ xs m Q X, fullK6AssignM7Spec xs m Q X →
      fullK6AssignM7Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullK6AssignM7Spec_intro {pk : BitVec 64} {lit rsn_cid : BitVec 32}
    {kbuf : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hlen : 2912 ≤ kbuf.length) (hm : (array (t := i32) pk kbuf ⋆ R) m)
    (hQ : ∀ kbuf' m', kbuf'.length = kbuf.length →
      (∀ idx < kbuf.length, idx ≠ 5 → idx ≠ 6 → (idx < 32 ∨ 480 ≤ idx) →
        (idx < 608 ∨ 736 ≤ idx) → kbuf'[idx]? = kbuf[idx]?) →
      (array (t := i32) pk kbuf' ⋆ R) m' → Q () m') :
    fullK6AssignM7Spec (pk, lit, rsn_cid, ()) m Q X :=
  ⟨kbuf, R, hlen, hm, hQ⟩

theorem fullK6AssignM7Spec_elim {a m Q X} (h : fullK6AssignM7Spec a m Q X) :
    let (pk, _, _, _) := a
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      2912 ≤ kbuf.length ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ kbuf' m', kbuf'.length = kbuf.length →
        (∀ idx < kbuf.length, idx ≠ 5 → idx ≠ 6 → (idx < 32 ∨ 480 ≤ idx) →
          (idx < 608 ∨ 736 ≤ idx) → kbuf'[idx]? = kbuf[idx]?) →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q () m' := by
  rcases a with ⟨pk, lit, rsn_cid, ⟨⟩⟩; exact h

theorem fullK6MtfM7Spec_noExit :
    ∀ xs m Q X, fullK6MtfM7Spec xs m Q X →
      fullK6MtfM7Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullK6MtfM7Spec_intro {pk : BitVec 64} {v : BitVec 32}
    {kbuf : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hlen : 2912 ≤ kbuf.length) (hm : (array (t := i32) pk kbuf ⋆ R) m)
    (hQ : ∀ kbuf' m', kbuf'.length = kbuf.length →
      (∀ idx < kbuf.length, idx ≠ 8 → idx ≠ 9 → idx ≠ 10 → idx ≠ 11 →
        (idx < 160 ∨ 352 ≤ idx) → kbuf'[idx]? = kbuf[idx]?) →
      (array (t := i32) pk kbuf' ⋆ R) m' → Q () m') :
    fullK6MtfM7Spec (pk, v, ()) m Q X :=
  ⟨kbuf, R, hlen, hm, hQ⟩

theorem fullK6MtfM7Spec_elim {a m Q X} (h : fullK6MtfM7Spec a m Q X) :
    let (pk, _, _) := a
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      2912 ≤ kbuf.length ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ kbuf' m', kbuf'.length = kbuf.length →
        (∀ idx < kbuf.length, idx ≠ 8 → idx ≠ 9 → idx ≠ 10 → idx ≠ 11 →
          (idx < 160 ∨ 352 ≤ idx) → kbuf'[idx]? = kbuf[idx]?) →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q () m' := by
  rcases a with ⟨pk, v, ⟨⟩⟩; exact h

theorem fullK6BacktrackM7Spec_noExit :
    ∀ xs m Q X, fullK6BacktrackM7Spec xs m Q X →
      fullK6BacktrackM7Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullK6BacktrackM7Spec_intro {pk : BitVec 64} {target_lvl : BitVec 32}
    {kbuf : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hlen : 2912 ≤ kbuf.length) (hm : (array (t := i32) pk kbuf ⋆ R) m)
    (hQ : ∀ kbuf' m', kbuf'.length = kbuf.length →
      (∀ idx < kbuf.length, idx ≠ 3 → idx ≠ 4 → idx ≠ 5 → idx ≠ 6 → idx ≠ 10 →
        (idx < 32 ∨ 160 ≤ idx) → (idx < 608 ∨ 736 ≤ idx) → kbuf'[idx]? = kbuf[idx]?) →
      (array (t := i32) pk kbuf' ⋆ R) m' → Q () m') :
    fullK6BacktrackM7Spec (pk, target_lvl, ()) m Q X :=
  ⟨kbuf, R, hlen, hm, hQ⟩

theorem fullK6BacktrackM7Spec_elim {a m Q X} (h : fullK6BacktrackM7Spec a m Q X) :
    let (pk, _, _) := a
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      2912 ≤ kbuf.length ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ kbuf' m', kbuf'.length = kbuf.length →
        (∀ idx < kbuf.length, idx ≠ 3 → idx ≠ 4 → idx ≠ 5 → idx ≠ 6 → idx ≠ 10 →
          (idx < 32 ∨ 160 ≤ idx) → (idx < 608 ∨ 736 ≤ idx) → kbuf'[idx]? = kbuf[idx]?) →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q () m' := by
  rcases a with ⟨pk, tlvl, ⟨⟩⟩; exact h

theorem fullK6PropM7Spec_noExit :
    ∀ xs m Q X, fullK6PropM7Spec xs m Q X →
      fullK6PropM7Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullK6PropM7Spec_intro {pk : BitVec 64}
    {kbuf : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hok : K6BufOk kbuf) (hm : (array (t := i32) pk kbuf ⋆ R) m)
    (hQ : ∀ r kbuf' m',
      K6BufOk kbuf' → kbuf'.length = kbuf.length →
      kbuf'[0]? = kbuf[0]? → kbuf'[1]? = kbuf[1]? →
      kbuf'[2]? = kbuf[2]? → kbuf'[15]? = kbuf[15]? →
      (∀ cid < 256, kbuf'[1888 + cid]? = kbuf[1888 + cid]? ∧
        kbuf'[2144 + cid]? = kbuf[2144 + cid]? ∧
        kbuf'[2400 + cid]? = kbuf[2400 + cid]?) →
      (array (t := i32) pk kbuf' ⋆ R) m' → Q (r, ()) m') :
    fullK6PropM7Spec (pk, ()) m Q X :=
  ⟨kbuf, R, hok, hm, hQ⟩

theorem fullK6PropM7Spec_elim {a m Q X} (h : fullK6PropM7Spec a m Q X) :
    let (pk, _) := a
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      K6BufOk kbuf ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ r kbuf' m',
        K6BufOk kbuf' → kbuf'.length = kbuf.length →
        kbuf'[0]? = kbuf[0]? → kbuf'[1]? = kbuf[1]? →
        kbuf'[2]? = kbuf[2]? → kbuf'[15]? = kbuf[15]? →
        (∀ cid < 256, kbuf'[1888 + cid]? = kbuf[1888 + cid]? ∧
          kbuf'[2144 + cid]? = kbuf[2144 + cid]? ∧
          kbuf'[2400 + cid]? = kbuf[2400 + cid]?) →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q (r, ()) m' := by
  rcases a with ⟨pk, ⟨⟩⟩; exact h

theorem fullK6AnaClM7Spec_noExit :
    ∀ xs m Q X, fullK6AnaClM7Spec xs m Q X →
      fullK6AnaClM7Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullK6AnaClM7Spec_intro {pk : BitVec 64} {cid skip_v : BitVec 32}
    {kbuf : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hok : K6BufOk kbuf) (hm : (array (t := i32) pk kbuf ⋆ R) m)
    (hQ : ∀ kbuf' m', kbuf'.length = kbuf.length →
      (∀ idx < kbuf.length, idx ≠ 16 → idx ≠ 17 → idx ≠ 18 → idx ≠ 20 →
        (idx < 416 ∨ 608 ≤ idx) → (idx < 2784 ∨ 2912 ≤ idx) →
        kbuf'[idx]? = kbuf[idx]?) →
      (array (t := i32) pk kbuf' ⋆ R) m' → Q () m') :
    fullK6AnaClM7Spec (pk, cid, skip_v, ()) m Q X :=
  ⟨kbuf, R, hok, hm, hQ⟩

theorem fullK6AnaClM7Spec_elim {a m Q X} (h : fullK6AnaClM7Spec a m Q X) :
    let (pk, _, _, _) := a
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      K6BufOk kbuf ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ kbuf' m', kbuf'.length = kbuf.length →
        (∀ idx < kbuf.length, idx ≠ 16 → idx ≠ 17 → idx ≠ 18 → idx ≠ 20 →
          (idx < 416 ∨ 608 ≤ idx) → (idx < 2784 ∨ 2912 ≤ idx) →
          kbuf'[idx]? = kbuf[idx]?) →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q () m' := by
  rcases a with ⟨pk, cid, skip_v, ⟨⟩⟩; exact h

theorem fullK6AnalyzeM7Spec_noExit :
    ∀ xs m Q X, fullK6AnalyzeM7Spec xs m Q X →
      fullK6AnalyzeM7Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullK6AnalyzeM7Spec_intro {pk : BitVec 64} {confl_cid : BitVec 32}
    {kbuf : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hok : K6BufOk kbuf) (hm : (array (t := i32) pk kbuf ⋆ R) m)
    (hQ : ∀ (ok : Bool) kbuf' m',
      K6BufOk kbuf' → kbuf'.length = kbuf.length →
      kbuf'[0]? = kbuf[0]? → kbuf'[2]? = kbuf[2]? → kbuf'[15]? = kbuf[15]? →
      (kbuf[1]?.getD 0#32).toNat ≤ (kbuf'[1]?.getD 0#32).toNat →
      (array (t := i32) pk kbuf' ⋆ R) m' → Q (ok, ()) m') :
    fullK6AnalyzeM7Spec (pk, confl_cid, ()) m Q X :=
  ⟨kbuf, R, hok, hm, hQ⟩

theorem fullK6AnalyzeM7Spec_elim {a m Q X} (h : fullK6AnalyzeM7Spec a m Q X) :
    let (pk, _, _) := a
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      K6BufOk kbuf ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ (ok : Bool) kbuf' m',
        K6BufOk kbuf' → kbuf'.length = kbuf.length →
        kbuf'[0]? = kbuf[0]? → kbuf'[2]? = kbuf[2]? → kbuf'[15]? = kbuf[15]? →
        (kbuf[1]?.getD 0#32).toNat ≤ (kbuf'[1]?.getD 0#32).toNat →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨pk, confl_cid, ⟨⟩⟩; exact h

theorem fullK6SolveM7Spec_noExit :
    ∀ xs m Q X, fullK6SolveM7Spec xs m Q X →
      fullK6SolveM7Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullK6SolveM7Spec_intro {h pk : BitVec 64} {tick_lim : BitVec 32}
    {hdr : List (BitVec 64)} {kbuf : List (BitVec 32)} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hh : hdr.length = 140) (hok : K6BufOk kbuf)
    (hm : (array64 (h + 32) hdr ⋆ array (t := i32) pk kbuf ⋆ R) m)
    (hQ : ∀ r fuel' kbuf' m',
      fuel'.toNat ≤ (hdr[17]?.getD 0#64).toNat →
      K6BufOk kbuf' → kbuf'.length = kbuf.length →
      kbuf'[0]? = kbuf[0]? →
      (kbuf[1]?.getD 0#32).toNat ≤ (kbuf'[1]?.getD 0#32).toNat →
      kbuf'[2]? = kbuf[2]? → kbuf'[15]? = kbuf[15]? →
      (array64 (h + 32) (hdr.set 17 fuel') ⋆ array (t := i32) pk kbuf' ⋆ R) m' →
      Q (r, ()) m') :
    fullK6SolveM7Spec (h, pk, tick_lim, ()) m Q X :=
  ⟨hdr, kbuf, R, hh, hok, hm, hQ⟩

theorem fullK6SolveM7Spec_elim {a m Q X} (h : fullK6SolveM7Spec a m Q X) :
    let (hp, pk, _, _) := a
    ∃ (hdr : List (BitVec 64)) (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      hdr.length = 140 ∧ K6BufOk kbuf ∧
      (array64 (hp + 32) hdr ⋆ array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ r fuel' kbuf' m',
        fuel'.toNat ≤ (hdr[17]?.getD 0#64).toNat →
        K6BufOk kbuf' → kbuf'.length = kbuf.length →
        kbuf'[0]? = kbuf[0]? →
        (kbuf[1]?.getD 0#32).toNat ≤ (kbuf'[1]?.getD 0#32).toNat →
        kbuf'[2]? = kbuf[2]? → kbuf'[15]? = kbuf[15]? →
        (array64 (hp + 32) (hdr.set 17 fuel') ⋆ array (t := i32) pk kbuf' ⋆ R) m' →
        Q (r, ()) m' := by
  rcases a with ⟨hp, pk, tl, ⟨⟩⟩; exact h

theorem fullK6CoreM7Spec_noExit :
    ∀ xs m Q X, fullK6CoreM7Spec xs m Q X →
      fullK6CoreM7Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullK6CoreM7Spec_intro {pk : BitVec 64}
    {kbuf : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hok : K6BufOk kbuf) (hm : (array (t := i32) pk kbuf ⋆ R) m)
    (hQ : ∀ kbuf' m', kbuf'.length = kbuf.length →
      (∀ idx < kbuf.length,
        (idx < 416 ∨ (480 ≤ idx ∧ idx < 2144) ∨ 2400 ≤ idx) →
        kbuf'[idx]? = kbuf[idx]?) →
      (∀ cid < (kbuf[1]?.getD 0#32).toNat,
        let m0 := kbuf[2144 + cid]?.getD 0#32
        let m1 := kbuf'[2144 + cid]?.getD 0#32
        (m1 &&& 0xFFFF#32) = (m0 &&& 0xFFFF#32) ∧
          (m1 &&& 0x40000000#32) = (m0 &&& 0x40000000#32)) →
      (array (t := i32) pk kbuf' ⋆ R) m' → Q () m') :
    fullK6CoreM7Spec (pk, ()) m Q X :=
  ⟨kbuf, R, hok, hm, hQ⟩

theorem fullK6CoreM7Spec_elim {a m Q X} (h : fullK6CoreM7Spec a m Q X) :
    let (pk, _) := a
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      K6BufOk kbuf ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ kbuf' m', kbuf'.length = kbuf.length →
        (∀ idx < kbuf.length,
          (idx < 416 ∨ (480 ≤ idx ∧ idx < 2144) ∨ 2400 ≤ idx) →
          kbuf'[idx]? = kbuf[idx]?) →
        (∀ cid < (kbuf[1]?.getD 0#32).toNat,
          let m0 := kbuf[2144 + cid]?.getD 0#32
          let m1 := kbuf'[2144 + cid]?.getD 0#32
          (m1 &&& 0xFFFF#32) = (m0 &&& 0xFFFF#32) ∧
            (m1 &&& 0x40000000#32) = (m0 &&& 0x40000000#32)) →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q () m' := by
  rcases a with ⟨pk, ⟨⟩⟩; exact h

theorem fullBveGatesM7Spec_noExit :
    ∀ xs m Q X, fullBveGatesM7Spec xs m Q X →
      fullBveGatesM7Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullBveGatesM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v np nn : BitVec 32}
    {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s)
    (hsc : 1088 ≤ c.scratch_cap) (hv : v.toNat < s.core.cur_vars)
    (hnp : np.toNat ≤ 512) (hnn : nn.toNat ≤ 512)
    (hp : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hn : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[512 + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ s' m',
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i < np.toNat, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
      (∀ j < nn.toNat, s'.scratch.scratch_buf[512 + j]? = s.scratch.scratch_buf[512 + j]?) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    fullBveGatesM7Spec (h, v, np, nn, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, htmk, hsc, hv, hnp, hnn, hp, hn, hm, hQ⟩

theorem fullBveGatesM7Spec_elim {a m Q X} (h : fullBveGatesM7Spec a m Q X) :
    let (hp, v, np, nn, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧ 1088 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[512 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ s' m',
        FullDenseInvW c F0 F_cur s' → TmkZero s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
        s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (∀ i < np.toNat, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
        (∀ j < nn.toNat, s'.scratch.scratch_buf[512 + j]? = s.scratch.scratch_buf[512 + j]?) →
        (FullMem c s' ⋆ R) m' → Q () m' := by
  rcases a with ⟨hp, v, np, nn, ⟨⟩⟩; exact h

/-! ## 4. Fidelity `intro` / `elim` / `noExit` Wrappers -/

theorem fidBveK6MvSpec_noExit :
    ∀ xs m Q X, fidBveK6MvSpec xs m Q X → fidBveK6MvSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fidBveK6MvSpec_intro {cap : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hQ : Q (BitVec.ofNat 64 (fidK6MaxV cap.toNat), ()) m) :
    fidBveK6MvSpec (cap, ()) m Q X :=
  hQ

theorem fidK6AddTicksSpec_noExit :
    ∀ xs m Q X, fidK6AddTicksSpec xs m Q X → fidK6AddTicksSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fidK6AddTicksSpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h delta : BitVec 64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hsc : 15744 ≤ c.scratch_cap)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ tk' m',
      let scr' := s.scratch.scratch_buf.set 4204 tk'
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m') :
    fidK6AddTicksSpec (h, delta, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hsc, hm, hQ⟩

theorem fidK6AddTicksSpec_elim {a m Q X} (h : fidK6AddTicksSpec a m Q X) :
    let (hp, _, _) := a
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ s.LengthsOk c ∧ 15744 ≤ c.scratch_cap ∧ (FullMem c s ⋆ R) m ∧
      ∀ tk' m',
        let scr' := s.scratch.scratch_buf.set 4204 tk'
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q () m' := by
  rcases a with ⟨hp, delta, ⟨⟩⟩; exact h

theorem fidK6WatchSpec_noExit :
    ∀ xs m Q X, fidK6WatchSpec xs m Q X → fidK6WatchSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fidK6WatchSpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {cid l0 l1 sz : BitVec 32} {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hok : FidK6BufOk s.scratch.scratch_buf)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ scr' m', scr'.length = c.scratch_cap →
      (∀ idx < c.scratch_cap,
        let mv := (s.scratch.scratch_buf[4214]?.getD 0#32).toNat
        (idx < 4224 + 11 * mv ∨ 4224 + 29 * mv ≤ idx) →
        scr'[idx]? = s.scratch.scratch_buf[idx]?) →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m') :
    fidK6WatchSpec (h, cid, l0, l1, sz, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hok, hm, hQ⟩

theorem fidK6WatchSpec_elim {a m Q X} (h : fidK6WatchSpec a m Q X) :
    let (hp, _, _, _, _, _) := a
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      hp = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap, (idx < 4224 + 11 * mv ∨ 4224 + 29 * mv ≤ idx) →
          scr'[idx]? = scr[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q () m' := by
  rcases a with ⟨hp, cid, l0, l1, sz, ⟨⟩⟩; exact h

theorem fidK6AssignSpec_noExit :
    ∀ xs m Q X, fidK6AssignSpec xs m Q X → fidK6AssignSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fidK6AssignSpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {lit rsn_cid : BitVec 32} {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hok : FidK6BufOk s.scratch.scratch_buf)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ scr' m', scr'.length = c.scratch_cap →
      (∀ idx < c.scratch_cap,
        let mv := (s.scratch.scratch_buf[4214]?.getD 0#32).toNat
        idx ≠ 4197 → idx ≠ 4198 →
        (idx < 4224 ∨ 4224 + 2 * mv ≤ idx) →
        (idx < 4224 + 5 * mv ∨ 4224 + 7 * mv ≤ idx) →
        (idx < 4224 + 9 * mv ∨ 4224 + 11 * mv ≤ idx) →
        scr'[idx]? = s.scratch.scratch_buf[idx]?) →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m') :
    fidK6AssignSpec (h, lit, rsn_cid, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hok, hm, hQ⟩

theorem fidK6AssignSpec_elim {a m Q X} (h : fidK6AssignSpec a m Q X) :
    let (hp, _, _, _) := a
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      hp = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap, idx ≠ 4197 → idx ≠ 4198 →
          (idx < 4224 ∨ 4224 + 2 * mv ≤ idx) →
          (idx < 4224 + 5 * mv ∨ 4224 + 7 * mv ≤ idx) →
          (idx < 4224 + 9 * mv ∨ 4224 + 11 * mv ≤ idx) →
          scr'[idx]? = scr[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q () m' := by
  rcases a with ⟨hp, lit, rsn_cid, ⟨⟩⟩; exact h

theorem fidK6MtfSpec_noExit :
    ∀ xs m Q X, fidK6MtfSpec xs m Q X → fidK6MtfSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fidK6MtfSpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {v : BitVec 32} {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hok : FidK6BufOk s.scratch.scratch_buf)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ scr' m', scr'.length = c.scratch_cap →
      (∀ idx < c.scratch_cap,
        let mv := (s.scratch.scratch_buf[4214]?.getD 0#32).toNat
        (idx < 4200 ∨ (4204 ≤ idx ∧ idx < 4224 + 2 * mv) ∨ 4224 + 5 * mv ≤ idx) →
        scr'[idx]? = s.scratch.scratch_buf[idx]?) →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m') :
    fidK6MtfSpec (h, v, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hok, hm, hQ⟩

theorem fidK6MtfSpec_elim {a m Q X} (h : fidK6MtfSpec a m Q X) :
    let (hp, _, _) := a
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      hp = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap,
          (idx < 4200 ∨ (4204 ≤ idx ∧ idx < 4224 + 2 * mv) ∨ 4224 + 5 * mv ≤ idx) →
          scr'[idx]? = scr[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q () m' := by
  rcases a with ⟨hp, v, ⟨⟩⟩; exact h

theorem fidK6BacktrackSpec_noExit :
    ∀ xs m Q X, fidK6BacktrackSpec xs m Q X →
      fidK6BacktrackSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fidK6BacktrackSpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {target_lvl : BitVec 32} {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hok : FidK6BufOk s.scratch.scratch_buf)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ scr' m', scr'.length = c.scratch_cap →
      (∀ idx < c.scratch_cap,
        let mv := (s.scratch.scratch_buf[4214]?.getD 0#32).toNat
        (idx < 4195 ∨ (4199 ≤ idx ∧ idx < 4224) ∨
          (4224 + 2 * mv ≤ idx ∧ idx < 4224 + 9 * mv) ∨ 4224 + 11 * mv ≤ idx) →
        scr'[idx]? = s.scratch.scratch_buf[idx]?) →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m') :
    fidK6BacktrackSpec (h, target_lvl, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hok, hm, hQ⟩

theorem fidK6BacktrackSpec_elim {a m Q X} (h : fidK6BacktrackSpec a m Q X) :
    let (hp, _, _) := a
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      hp = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap,
          (idx < 4195 ∨ (4199 ≤ idx ∧ idx < 4224) ∨
            (4224 + 2 * mv ≤ idx ∧ idx < 4224 + 9 * mv) ∨ 4224 + 11 * mv ≤ idx) →
          scr'[idx]? = scr[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q () m' := by
  rcases a with ⟨hp, target_lvl, ⟨⟩⟩; exact h

theorem fidK6CoreSpec_noExit :
    ∀ xs m Q X, fidK6CoreSpec xs m Q X → fidK6CoreSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fidK6CoreSpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hok : FidK6BufOk s.scratch.scratch_buf)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ scr' m', scr'.length = c.scratch_cap →
      (∀ idx < c.scratch_cap,
        let mv := (s.scratch.scratch_buf[4214]?.getD 0#32).toNat
        (idx < 4224 + 6 * mv ∨ (4224 + 7 * mv ≤ idx ∧ idx < 4224 + 33 * mv) ∨
          4224 + 37 * mv ≤ idx) →
        scr'[idx]? = s.scratch.scratch_buf[idx]?) →
      FidK6BufOk scr' →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m') :
    fidK6CoreSpec (h, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hok, hm, hQ⟩

theorem fidK6CoreSpec_elim {a m Q X} (h : fidK6CoreSpec a m Q X) :
    let (hp, _) := a
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      hp = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap,
          (idx < 4224 + 6 * mv ∨ (4224 + 7 * mv ≤ idx ∧ idx < 4224 + 33 * mv) ∨
            4224 + 37 * mv ≤ idx) →
          scr'[idx]? = scr[idx]?) →
        FidK6BufOk scr' →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q () m' := by
  rcases a with ⟨hp, ⟨⟩⟩; exact h

theorem fidK6PropSpec_noExit :
    ∀ xs m Q X, fidK6PropSpec xs m Q X → fidK6PropSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fidK6PropSpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hok : FidK6BufOk s.scratch.scratch_buf)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (r : BitVec 32) scr' m',
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      FidK6BufOk scr' → scr'.length = c.scratch_cap →
      (∀ i < 4195, scr'[i]? = scr[i]?) →
      (∀ i, 4199 ≤ i → i < 4204 → scr'[i]? = scr[i]?) →
      (∀ i, 4205 ≤ i → i < 4224 → scr'[i]? = scr[i]?) →
      (∀ i, 4224 + 2 * mv ≤ i → i < 4224 + 5 * mv → scr'[i]? = scr[i]?) →
      (∀ i, 4224 + 7 * mv ≤ i → i < 4224 + 9 * mv → scr'[i]? = scr[i]?) →
      (∀ i, 4224 + 29 * mv ≤ i → i < 4224 + 45 * mv → scr'[i]? = scr[i]?) →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
      Q (r, ()) m') :
    fidK6PropSpec (h, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hok, hm, hQ⟩

theorem fidK6PropSpec_elim {a m Q X} (h : fidK6PropSpec a m Q X) :
    let (hp, _) := a
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      hp = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 32) scr' m',
        FidK6BufOk scr' → scr'.length = c.scratch_cap →
        (∀ i < 4195, scr'[i]? = scr[i]?) →
        (∀ i, 4199 ≤ i → i < 4204 → scr'[i]? = scr[i]?) →
        (∀ i, 4205 ≤ i → i < 4224 → scr'[i]? = scr[i]?) →
        (∀ i, 4224 + 2 * mv ≤ i → i < 4224 + 5 * mv → scr'[i]? = scr[i]?) →
        (∀ i, 4224 + 7 * mv ≤ i → i < 4224 + 9 * mv → scr'[i]? = scr[i]?) →
        (∀ i, 4224 + 29 * mv ≤ i → i < 4224 + 45 * mv → scr'[i]? = scr[i]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q (r, ()) m' := by
  rcases a with ⟨hp, ⟨⟩⟩; exact h

theorem fidK6AnaClSpec_noExit :
    ∀ xs m Q X, fidK6AnaClSpec xs m Q X → fidK6AnaClSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fidK6AnaClSpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {cid skip_v : BitVec 32} {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hok : FidK6BufOk s.scratch.scratch_buf)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ scr' m', scr'.length = c.scratch_cap →
      (∀ idx < c.scratch_cap,
        let mv := (s.scratch.scratch_buf[4214]?.getD 0#32).toNat
        idx ≠ 4208 → idx ≠ 4209 → idx ≠ 4210 → idx ≠ 4212 →
        (idx < 4224 + 6 * mv ∨ 4224 + 9 * mv ≤ idx) →
        (idx < 4224 + 43 * mv ∨ 4224 + 45 * mv ≤ idx) →
        scr'[idx]? = s.scratch.scratch_buf[idx]?) →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m') :
    fidK6AnaClSpec (h, cid, skip_v, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hok, hm, hQ⟩

theorem fidK6AnaClSpec_elim {a m Q X} (h : fidK6AnaClSpec a m Q X) :
    let (hp, _, _, _) := a
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      hp = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap,
          idx ≠ 4208 → idx ≠ 4209 → idx ≠ 4210 → idx ≠ 4212 →
          (idx < 4224 + 6 * mv ∨ 4224 + 9 * mv ≤ idx) →
          (idx < 4224 + 43 * mv ∨ 4224 + 45 * mv ≤ idx) →
          scr'[idx]? = scr[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q () m' := by
  rcases a with ⟨hp, cid, skip_v, ⟨⟩⟩; exact h

theorem fidK6AnalyzeSpec_noExit :
    ∀ xs m Q X, fidK6AnalyzeSpec xs m Q X → fidK6AnalyzeSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fidK6AnalyzeSpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {confl_cid : BitVec 32} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hok : FidK6BufOk s.scratch.scratch_buf)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) scr' m',
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      FidK6BufOk scr' → scr'.length = c.scratch_cap →
      (∀ i < 4193, scr'[i]? = scr[i]?) →
      scr'[4194]? = scr[4194]? →
      (scr[4193]?.getD 0#32).toNat ≤ (scr'[4193]?.getD 0#32).toNat →
      (∀ cid < (scr[4193]?.getD 0#32).toNat,
        scr'[4224 + 37 * mv + cid]? = scr[4224 + 37 * mv + cid]?) →
      scr'[4199]? = scr[4199]? → scr'[4205]? = scr[4205]? →
      scr'[4207]? = scr[4207]? → scr'[4211]? = scr[4211]? →
      scr'[4213]? = scr[4213]? → scr'[4214]? = scr[4214]? →
      scr'[4215]? = scr[4215]? → scr'[4216]? = scr[4216]? →
      (∀ i, 4224 + 41 * mv ≤ i → i < 4224 + 43 * mv → scr'[i]? = scr[i]?) →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
      Q (ok, ()) m') :
    fidK6AnalyzeSpec (h, confl_cid, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hok, hm, hQ⟩

theorem fidK6AnalyzeSpec_elim {a m Q X} (h : fidK6AnalyzeSpec a m Q X) :
    let (hp, _, _) := a
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      hp = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) scr' m',
        FidK6BufOk scr' → scr'.length = c.scratch_cap →
        (∀ i < 4193, scr'[i]? = scr[i]?) →
        scr'[4194]? = scr[4194]? →
        (scr[4193]?.getD 0#32).toNat ≤ (scr'[4193]?.getD 0#32).toNat →
        (∀ cid < (scr[4193]?.getD 0#32).toNat,
          scr'[4224 + 37 * mv + cid]? = scr[4224 + 37 * mv + cid]?) →
        scr'[4199]? = scr[4199]? → scr'[4205]? = scr[4205]? →
        scr'[4207]? = scr[4207]? → scr'[4211]? = scr[4211]? →
        scr'[4213]? = scr[4213]? → scr'[4214]? = scr[4214]? →
        scr'[4215]? = scr[4215]? → scr'[4216]? = scr[4216]? →
        (∀ i, 4224 + 41 * mv ≤ i → i < 4224 + 43 * mv → scr'[i]? = scr[i]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q (ok, ()) m' := by
  rcases a with ⟨hp, confl_cid, ⟨⟩⟩; exact h

theorem fidK6SolveSpec_noExit :
    ∀ xs m Q X, fidK6SolveSpec xs m Q X → fidK6SolveSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fidK6SolveSpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {tick_lim : BitVec 32} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hok : FidK6BufOk s.scratch.scratch_buf)
    (honc : (s.scratch.scratch_buf[4194]?.getD 0#32).toNat ≤
      (s.scratch.scratch_buf[4193]?.getD 0#32).toNat)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (r : BitVec 64) scr' fuel' m',
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      let s' : FullState :=
        { s with
          core := { s.core with fuel := fuel' }
          scratch := { s.scratch with scratch_buf := scr' } }
      FidK6BufOk scr' → scr'.length = c.scratch_cap →
      (∀ i < 4192, scr'[i]? = scr[i]?) →
      scr'[4194]? = scr[4194]? → scr'[4214]? = scr[4214]? →
      (scr[4194]?.getD 0#32).toNat ≤ (scr'[4193]?.getD 0#32).toNat →
      (∀ cid < (scr[4194]?.getD 0#32).toNat,
        scr'[4224 + 37 * mv + cid]? = scr[4224 + 37 * mv + cid]?) →
      fuel'.toNat ≤ s.core.fuel.toNat →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    fidK6SolveSpec (h, tick_lim, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hok, honc, hm, hQ⟩

theorem fidK6SolveSpec_elim {a m Q X} (h : fidK6SolveSpec a m Q X) :
    let (hp, _, _) := a
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      hp = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧
      (scr[4194]?.getD 0#32).toNat ≤ (scr[4193]?.getD 0#32).toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) scr' fuel' m',
        let s' : FullState :=
          { s with
            core := { s.core with fuel := fuel' }
            scratch := { s.scratch with scratch_buf := scr' } }
        FidK6BufOk scr' → scr'.length = c.scratch_cap →
        (∀ i < 4192, scr'[i]? = scr[i]?) →
        scr'[4194]? = scr[4194]? → scr'[4214]? = scr[4214]? →
        (scr[4194]?.getD 0#32).toNat ≤ (scr'[4193]?.getD 0#32).toNat →
        (∀ cid < (scr[4194]?.getD 0#32).toNat,
          scr'[4224 + 37 * mv + cid]? = scr[4224 + 37 * mv + cid]?) →
        fuel'.toNat ≤ s.core.fuel.toNat →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m' := by
  rcases a with ⟨hp, tick_lim, ⟨⟩⟩; exact h

theorem fidK6ExtractSolveSpec_noExit :
    ∀ xs m Q X, fidK6ExtractSolveSpec xs m Q X →
      fidK6ExtractSolveSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fidK6ExtractSolveSpec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v np nn tick_lim : BitVec 32}
    {second_pass : Bool} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s)
    (hsc : 16384 ≤ c.scratch_cap) (hv : v.toNat < s.core.cur_vars)
    (hnp : np.toNat ≤ 2001) (hnn : nn.toNat ≤ 2001)
    (hp : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hn : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[2001 + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) s' m',
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i < 4002, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    fidK6ExtractSolveSpec (h, v, np, nn, second_pass, tick_lim, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, htmk, hsc, hv, hnp, hnn, hp, hn, hm, hQ⟩

theorem fidK6ExtractSolveSpec_elim {a m Q X} (h : fidK6ExtractSolveSpec a m Q X) :
    let (hp, v, np, nn, _, _, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧ 16384 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 2001 ∧ nn.toNat ≤ 2001 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[2001 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) s' m',
        FullDenseInvW c F0 F_cur s' → TmkZero s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
        s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (∀ i < 4002, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
        (∀ i, 4132 ≤ i → i < 4192 → s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, v, np, nn, sp, tl, ⟨⟩⟩; exact h

theorem fidBveCertifyUnitSpec_noExit :
    ∀ xs m Q X, fidBveCertifyUnitSpec xs m Q X →
      fidBveCertifyUnitSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fidBveCertifyUnitSpec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64}
    {v unit side_off side_cnt side_mask : BitVec 32} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s)
    (hsc : 16384 ≤ c.scratch_cap) (hu : unit.toNat < 2 * s.core.cur_vars)
    (hcnt : side_cnt.toNat ≤ 2001) (hoff : side_off.toNat + side_cnt.toNat ≤ 4002)
    (hmask : side_mask = 4002#32 ∨ side_mask = 4066#32)
    (hent : ∀ i < side_cnt.toNat, FullBveEntryOkW F_cur s unit.toNat
      (s.scratch.scratch_buf[side_off.toNat + i]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) s' m',
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i < 4192, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    fidBveCertifyUnitSpec (h, v, unit, side_off, side_cnt, side_mask, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, htmk, hsc, hu, hcnt, hoff, hmask, hent, hm, hQ⟩

theorem fidBveCertifyUnitSpec_elim {a m Q X} (h : fidBveCertifyUnitSpec a m Q X) :
    let (hp, _, unit, side_off, side_cnt, side_mask, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧ 16384 ≤ c.scratch_cap ∧
      unit.toNat < 2 * s.core.cur_vars ∧
      side_cnt.toNat ≤ 2001 ∧ side_off.toNat + side_cnt.toNat ≤ 4002 ∧
      (side_mask = 4002#32 ∨ side_mask = 4066#32) ∧
      (∀ i < side_cnt.toNat, FullBveEntryOkW F_cur s unit.toNat
        (s.scratch.scratch_buf[side_off.toNat + i]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) s' m',
        FullDenseInvW c F0 F_cur s' → TmkZero s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
        s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (∀ i < 4192, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, v, unit, side_off, side_cnt, side_mask, ⟨⟩⟩; exact h

theorem m8BveGatesSpec_noExit :
    ∀ xs m Q X, m8BveGatesSpec xs m Q X → m8BveGatesSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem m8BveGatesSpec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v np nn : BitVec 32}
    {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s)
    (hsc : 16384 ≤ c.scratch_cap) (hv : v.toNat < s.core.cur_vars)
    (hnp : np.toNat ≤ 2001) (hnn : nn.toNat ≤ 2001)
    (hp : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hn : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[2001 + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ s' m',
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i < np.toNat, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
      (∀ j < nn.toNat, s'.scratch.scratch_buf[2001 + j]? = s.scratch.scratch_buf[2001 + j]?) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    m8BveGatesSpec (h, v, np, nn, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, htmk, hsc, hv, hnp, hnn, hp, hn, hm, hQ⟩

theorem m8BveGatesSpec_elim {a m Q X} (h : m8BveGatesSpec a m Q X) :
    let (hp, v, np, nn, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧ 16384 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 2001 ∧ nn.toNat ≤ 2001 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[2001 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ s' m',
        FullDenseInvW c F0 F_cur s' → TmkZero s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
        s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (∀ i < np.toNat, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
        (∀ j < nn.toNat, s'.scratch.scratch_buf[2001 + j]? = s.scratch.scratch_buf[2001 + j]?) →
        (FullMem c s' ⋆ R) m' → Q () m' := by
  rcases a with ⟨hp, v, np, nn, ⟨⟩⟩; exact h

end

end LeanQbe.T.Examples.Kissat.Proof.Definition
