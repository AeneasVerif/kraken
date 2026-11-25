/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBve
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBveK6b0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity BVE Parity Proofs — Part 0 (`FidBveProof0`)

UNSAT-only `Func.wp` specifications, dynamic layout invariants, and primitive proofs
(`XPost := False`, strictly `std3`, `0` `@[expose]`, `0` `*Lemmas*` in `public import`):
1. Dynamic `fidK6MaxV`, `fidK6MaxV_bounds`, `fidK6MaxV_bv64_eq`, and `FidK6BufOk`.
2. Dynamic K6 offset arithmetic helpers (`fid_k6_off_add*`).
3. Specifications (`fidBveK6MvSpec`, `fidK6*Spec`, `fidBveCertifyUnitSpec`) with
   `_noExit`, `_intro`, `_elim` (`full_bve_def_k6_fid` and `full_bve_gates_fid` certify
   canonical `FullM8CoreParity.m8BveGatesSpec` directly).
4. `full_bve_k6_mv_fid_wp` and `full_fid_k6_add_ticks_wp`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBve

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open Kraken.Bedrock2.Test

open scoped FullArenaTactics M8K6bTactics

/-! ## 1. Dynamic `fidK6MaxV` & `FidK6BufOk` Invariant -/

/-- Dynamic K6 variable capacity for `FullFidelityBve` inside `scratch_buf[4192..)` (`GAP-BVE-01`),
scaling in `[256, 8192]` (rounded down to multiples of `64`). -/
def fidK6MaxV (cap : Nat) : Nat :=
  if cap < 16384 then 0
  else if 524288 ≤ cap then 8192
  else
    let raw := ((cap - 4224) / 64) / 64 * 64
    max 256 (min 8192 raw)

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
          change ¬ (((BitVec.ofNat 64 cap - 4224#64) / 64#64) &&& 0xFFFFFFFFFFFFFFC0#64).toNat < 256
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

/-- Dynamic structural & arena bounds invariant for the `GAP-BVE-01` K6 solver embedded inside
`scr[4192..)` with `mv = scr[4214] ∈ [256, 8192]`. -/
def FidK6BufOk (scr : List (BitVec 32)) : Prop :=
  let mv := (scr[4214]?.getD 0#32).toNat
  let nc := (scr[4193]?.getD 0#32).toNat
  let alen := (scr[4206]?.getD 0#32).toNat
  let acap := (scr[4207]?.getD 0#32).toNat
  256 ≤ mv ∧ mv ≤ 8192 ∧
  4224 + 45 * mv + acap ≤ scr.length ∧ scr.length < 2 ^ 30 ∧
  nc ≤ 4 * mv ∧ alen ≤ acap ∧
  ∀ cid < nc,
    let off := (scr[4224 + 29 * mv + cid]?.getD 0#32).toNat
    let cm := scr[4224 + 33 * mv + cid]?.getD 0#32
    let sz := (cm &&& 0xFFFF#32).toNat
    let aux := (scr[4224 + 37 * mv + cid]?.getD 0#32).toNat
    off + sz ≤ acap ∧ ((cm &&& 0x40000000#32) ≠ 0#32 → off + sz + aux ≤ acap)

theorem FidK6BufOk.mv_lo {scr : List (BitVec 32)} (h : FidK6BufOk scr) :
    256 ≤ (scr[4214]?.getD 0#32).toNat := h.1

theorem FidK6BufOk.mv_hi {scr : List (BitVec 32)} (h : FidK6BufOk scr) :
    (scr[4214]?.getD 0#32).toNat ≤ 8192 := h.2.1

theorem FidK6BufOk.length_ge {scr : List (BitVec 32)} (h : FidK6BufOk scr) :
    4224 + 45 * (scr[4214]?.getD 0#32).toNat + (scr[4207]?.getD 0#32).toNat ≤ scr.length :=
  h.2.2.1

theorem FidK6BufOk.length_lt {scr : List (BitVec 32)} (h : FidK6BufOk scr) :
    scr.length < 2 ^ 30 := h.2.2.2.1

theorem FidK6BufOk.nc_le {scr : List (BitVec 32)} (h : FidK6BufOk scr) :
    (scr[4193]?.getD 0#32).toNat ≤ 4 * (scr[4214]?.getD 0#32).toNat := h.2.2.2.2.1

theorem FidK6BufOk.alen_le {scr : List (BitVec 32)} (h : FidK6BufOk scr) :
    (scr[4206]?.getD 0#32).toNat ≤ (scr[4207]?.getD 0#32).toNat := h.2.2.2.2.2.1

theorem FidK6BufOk.clause_ok {scr : List (BitVec 32)} (h : FidK6BufOk scr) {cid : Nat}
    (hcid : cid < (scr[4193]?.getD 0#32).toNat) :
    let mv := (scr[4214]?.getD 0#32).toNat
    let off := (scr[4224 + 29 * mv + cid]?.getD 0#32).toNat
    let cm := scr[4224 + 33 * mv + cid]?.getD 0#32
    let sz := (cm &&& 0xFFFF#32).toNat
    let aux := (scr[4224 + 37 * mv + cid]?.getD 0#32).toNat
    off + sz ≤ (scr[4207]?.getD 0#32).toNat ∧
      ((cm &&& 0x40000000#32) ≠ 0#32 → off + sz + aux ≤ (scr[4207]?.getD 0#32).toNat) :=
  h.2.2.2.2.2.2 cid hcid

theorem FidK6BufOk.base_ge {scr : List (BitVec 32)} (h : FidK6BufOk scr) :
    4224 + 45 * (scr[4214]?.getD 0#32).toNat ≤ scr.length := by
  have := h.length_ge; omega

theorem FidK6BufOk.min_len {scr : List (BitVec 32)} (h : FidK6BufOk scr) :
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

/-! ## 2. Dynamic Offset Arithmetic Helpers -/

theorem fid_bv32_shl2_toNat {x : BitVec 32} (hx : 4 * x.toNat < 2 ^ 32) :
    (x <<< (2 : Nat)).toNat = 4 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega

theorem fid_zext32_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat :=
  m6_zext32_toNat x

theorem fid_list_set_idx_eq {α : Type _} (xs : List α) {i j : Nat} (h : i = j) (v : α) :
    xs.set i v = xs.set j v := h ▸ rfl

namespace FidK6Tactics

@[scoped bv_c0] theorem fid_bv32_mul_toNat (a b : BitVec 32) :
    (a * b).toNat = (a.toNat * b.toNat) % 2 ^ 32 :=
  BitVec.toNat_mul a b

@[scoped bv_c0] theorem fid_bv32_zext64_toNat (x : BitVec 32) :
    (x.setWidth 64).toNat = x.toNat :=
  m6_zext32_toNat x

end FidK6Tactics

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
  rw [m6_zext32_toNat, BitVec.toNat_add, fid_k6_off_k hmv hk,
    Nat.mod_eq_of_lt (by omega)]

theorem fid_k6_off_add0 {x : BitVec 32} (hx : x.toNat < 2 ^ 30) :
    (((4224 : BitVec 32) + x).setWidth 64).toNat = 4224 + x.toNat := by
  rw [m6_zext32_toNat, BitVec.toNat_add, show (4224 : BitVec 32).toNat = 4224 from rfl,
    Nat.mod_eq_of_lt (by omega)]

theorem fid_k6_off_add1 {mv x : BitVec 32} (hmv : mv.toNat ≤ 8192) (hx : x.toNat < 2 ^ 30) :
    (((4224 : BitVec 32) + mv + x).setWidth 64).toNat = 4224 + mv.toNat + x.toNat := by
  rw [m6_zext32_toNat, BitVec.toNat_add, BitVec.toNat_add,
    show (4224 : BitVec 32).toNat = 4224 from rfl,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem fid_k6_off_add2 {mv x y : BitVec 32} {k : Nat}
    (hmv : mv.toNat ≤ 8192) (hk : k ≤ 45) (hxy : x.toNat + y.toNat < 2 ^ 30) :
    (((4224 : BitVec 32) + (@OfNat.ofNat (BitVec 32) k (BitVec.instOfNat)) * mv + x + y).setWidth
      64).toNat = 4224 + k * mv.toNat + x.toNat + y.toNat := by
  have hkm : k * mv.toNat ≤ 45 * 8192 := Nat.mul_le_mul hk hmv
  rw [m6_zext32_toNat, BitVec.toNat_add, BitVec.toNat_add, fid_k6_off_k hmv hk,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem fid_k6_off_add3 {mv x y z : BitVec 32} {k : Nat}
    (hmv : mv.toNat ≤ 8192) (hk : k ≤ 45) (hxyz : x.toNat + y.toNat + z.toNat < 2 ^ 30) :
    (((4224 : BitVec 32) + (@OfNat.ofNat (BitVec 32) k (BitVec.instOfNat)) * mv + x + y +
      z).setWidth 64).toNat = 4224 + k * mv.toNat + x.toNat + y.toNat + z.toNat := by
  have hkm : k * mv.toNat ≤ 45 * 8192 := Nat.mul_le_mul hk hmv
  rw [m6_zext32_toNat, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, fid_k6_off_k hmv hk,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-! ## 3. Specifications (`fidBveK6MvSpec`, `fidK6*Spec`, `fidBveCertifyUnitSpec`) -/

/-- Exact pure specification for `full_bve_k6_mv_fid`. -/
def fidBveK6MvSpec : Spec [i64] [i64] := fun (cap, ()) m Q _ =>
  Q (BitVec.ofNat 64 (fidK6MaxV cap.toNat), ()) m

theorem fidBveK6MvSpec_noExit :
    ∀ xs m Q X, fidBveK6MvSpec xs m Q X → fidBveK6MvSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

/-- Contract for `full_fid_k6_add_ticks` (saturating `u32` update at `scr[4204]`). -/
def fidK6AddTicksSpec : Spec [i64, i64] [] := fun (h, _delta, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ 15744 ≤ c.scratch_cap ∧ (FullMem c s ⋆ R) m ∧
    ∀ tk' m',
      let scr' := s.scratch.scratch_buf.set 4204 tk'
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m'

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

/-- Contract for `full_k6_watch_fid` (modifies only watch arrays `[4224+11*mv .. 4224+29*mv)`). -/
def fidK6WatchSpec : Spec [i64, i32, i32, i32, i32] [] :=
  fun (h, _cid, _l0, _l1, _sz, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      h = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap, (idx < 4224 + 11 * mv ∨ 4224 + 29 * mv ≤ idx) →
          scr'[idx]? = scr[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m'

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

/-- Contract for `full_k6_assign_fid`. -/
def fidK6AssignSpec : Spec [i64, i32, i32] [] :=
  fun (h, _lit, _rsn_cid, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      h = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap, idx ≠ 4197 → idx ≠ 4198 →
          (idx < 4224 ∨ 4224 + 2 * mv ≤ idx) →
          (idx < 4224 + 5 * mv ∨ 4224 + 7 * mv ≤ idx) →
          (idx < 4224 + 9 * mv ∨ 4224 + 11 * mv ≤ idx) →
          scr'[idx]? = scr[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m'

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

/-- Contract for `full_k6_mtf_fid`. -/
def fidK6MtfSpec : Spec [i64, i32] [] :=
  fun (h, _v, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      h = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap,
          (idx < 4200 ∨ (4204 ≤ idx ∧ idx < 4224 + 2 * mv) ∨ 4224 + 5 * mv ≤ idx) →
          scr'[idx]? = scr[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m'

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

/-- Contract for `full_k6_backtrack_fid`. -/
def fidK6BacktrackSpec : Spec [i64, i32] [] :=
  fun (h, _target_lvl, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      h = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap,
          (idx < 4195 ∨ (4199 ≤ idx ∧ idx < 4224) ∨
            (4224 + 2 * mv ≤ idx ∧ idx < 4224 + 9 * mv) ∨ 4224 + 11 * mv ≤ idx) →
          scr'[idx]? = scr[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m'

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

/-- Contract for `full_k6_core_fid`. -/
def fidK6CoreSpec : Spec [i64] [] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      h = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap,
          (idx < 4224 + 6 * mv ∨ (4224 + 7 * mv ≤ idx ∧ idx < 4224 + 33 * mv) ∨
            4224 + 37 * mv ≤ idx) →
          scr'[idx]? = scr[idx]?) →
        FidK6BufOk scr' →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m'

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

/-- Contract for `full_k6_prop_fid`. -/
def fidK6PropSpec : Spec [i64] [i32] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      h = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 32) scr' m',
        FidK6BufOk scr' → scr'.length = c.scratch_cap →
        (∀ i < 4195, scr'[i]? = scr[i]?) →
        (∀ i, 4199 ≤ i → i < 4204 → scr'[i]? = scr[i]?) →
        (∀ i, 4205 ≤ i → i < 4224 → scr'[i]? = scr[i]?) →
        (∀ i, 4224 + 2 * mv ≤ i → i < 4224 + 5 * mv → scr'[i]? = scr[i]?) →
        (∀ i, 4224 + 7 * mv ≤ i → i < 4224 + 9 * mv → scr'[i]? = scr[i]?) →
        (∀ i, 4224 + 29 * mv ≤ i → i < 4224 + 45 * mv → scr'[i]? = scr[i]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q (r, ()) m'

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

/-- Contract for `full_k6_ana_cl_fid`. -/
def fidK6AnaClSpec : Spec [i64, i32, i32] [] :=
  fun (h, _cid, _skip_v, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      h = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap,
          idx ≠ 4208 → idx ≠ 4209 → idx ≠ 4210 → idx ≠ 4212 →
          (idx < 4224 + 6 * mv ∨ 4224 + 9 * mv ≤ idx) →
          (idx < 4224 + 43 * mv ∨ 4224 + 45 * mv ≤ idx) →
          scr'[idx]? = scr[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m'

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

/-- Contract for `full_k6_analyze_fid`. -/
def fidK6AnalyzeSpec : Spec [i64, i32] [.bool] :=
  fun (h, _confl_cid, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      h = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
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
        Q (ok, ()) m'

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

/-- Contract for `full_k6_solve_fid`. -/
def fidK6SolveSpec : Spec [i64, i32] [i64] :=
  fun (h, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      h = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧
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
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

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

/-- Contract for `full_k6_extract_and_solve_fid` (accepting dynamic `np, nn ≤ 2001`). -/
def fidK6ExtractSolveSpec : Spec [i64, i32, i32, i32, .bool, i32] [.bool] :=
  fun (h, v, np, nn, _second_pass, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧ 16384 ≤ c.scratch_cap ∧
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
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

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
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
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

/-- Contract for `full_bve_certify_unit_fid` (`GAP-BVE-03`: certifies one-sided gate core
unit entailment via direct entailment or verified `FullM6Sweep` K6 solver, enqueuing `unit` at
level 0 or flagging `inconsistent = 1ULL` while preserving `FullDenseInvW` and `scr[0..4192)`). -/
def fidBveCertifyUnitSpec : Spec [i64, i32, i32, i32, i32, i32] [.bool] :=
  fun (h, _v, unit, side_off, side_cnt, side_mask, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧ 16384 ≤ c.scratch_cap ∧
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
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

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
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
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

/-! ## 4. Primitive Proofs (`full_bve_k6_mv_fid_wp`, `full_fid_k6_add_ticks_wp`) -/

/-- Exact `Func.wp` proof for `full_bve_k6_mv_fid`, certifying `fidBveK6MvSpec`. -/
theorem full_bve_k6_mv_fid_wp (Γ : Env) :
    ∀ a m Q X, fidBveK6MvSpec a m Q X → Func.wp Γ full_bve_k6_mv_fid_body a m Q X := by
  rintro ⟨cap, ⟨⟩⟩ m Q X hQ
  unfold fidBveK6MvSpec at hQ
  have heq := fidK6MaxV_bv64_eq (cap := cap.toNat) cap.isLt
  have hcap : BitVec.ofNat 64 cap.toNat = cap := BitVec.eq_of_toNat_eq (by simp)
  dsimp only at heq; rw [hcap] at heq
  unfold Func.wp full_bve_k6_mv_fid_body
  c0_hsplit
  · c0_hsteps!
    have hlt : cap < 16384#64 := hc
    simp only [hlt, ↓reduceIte] at heq
    simpa [← heq] using hQ
  · have hge1 : ¬ cap < 16384#64 := by intro h; exact hc h
    c0_hsplit
    · c0_hsteps!
      have hge512 : 524288#64 ≤ cap := by
        change (524288#64).toNat ≤ cap.toNat
        change (524288#64).toNat ≤ cap.toNat at hc; exact hc
      simp only [hge1, hge512, ↓reduceIte] at heq
      simpa [← heq] using hQ
    · have hlt512 : ¬ 524288#64 ≤ cap := by
        intro h; exact hc h
      c0_hsplit
      · c0_hsteps!
        have hr1 : ((cap - 4224#64) / 64#64 &&& 0xFFFFFFFFFFFFFFC0#64) < 256#64 := hc
        simp only [hge1, hlt512, hr1, ↓reduceIte] at heq
        simpa [← heq] using hQ
      · have hr1 : ¬ ((cap - 4224#64) / 64#64 &&& 0xFFFFFFFFFFFFFFC0#64) < 256#64 := by
          intro h; exact hc h
        c0_hsplit
        · c0_hsteps!
          have hr2 : 8192#64 < ((cap - 4224#64) / 64#64 &&& 0xFFFFFFFFFFFFFFC0#64) := hc
          simp only [hge1, hlt512, hr1, hr2, ↓reduceIte] at heq
          simpa [← heq] using hQ
        · c0_hsteps!
          have hr2 : ¬ 8192#64 < ((cap - 4224#64) / 64#64 &&& 0xFFFFFFFFFFFFFFC0#64) := by
            intro h; exact hc h
          simp only [hge1, hlt512, hr1, hr2, ↓reduceIte] at heq
          simpa [← heq] using hQ

/-- Parametric `Func.wp` proof for `full_fid_k6_add_ticks`, certifying `fidK6AddTicksSpec`. -/
theorem full_fid_k6_add_ticks_wp (Γ : Env) :
    ∀ a m Q X, fidK6AddTicksSpec a m Q X → Func.wp Γ full_fid_k6_add_ticks_body a m Q X := by
  rintro ⟨h, delta, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hsc16, hm0, hQ⟩ := fidK6AddTicksSpec_elim hSpec
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have h4204 : 4204 < s.scratch.scratch_buf.length := by omega
  unfold Func.wp full_fid_k6_add_ticks_body
  have hm0' : (FullMem c (m8ScrSt s s.scratch.scratch_buf) ⋆ R) m0 := by
    rwa [m8ScrSt_self]
  have h15744 : 15744 ≤ s.scratch.scratch_buf.length := by omega
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun tk => (tk, ())) (fun _ => True)
    (fun _ tk _ => by
      c0_hsteps!
      rw [m8ScrSt_eq] at hm
      exact hQ tk _ hm)
    (fun Jt hJt => by
      c0_hsplit
      · c0_hsteps!; exact hJt 0xFFFFFFFF#32 trivial
      · c0_hsteps!; exact hJt _ trivial)

end LeanQbe.T.Examples.Kissat.FullFidelityBve
