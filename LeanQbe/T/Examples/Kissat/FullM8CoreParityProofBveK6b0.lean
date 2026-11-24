/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M8 Core Parity (`FullM8CoreParity`) Rank #8 Proofs — Part K6b0 (`Prop`)

UNSAT-only `Func.wp` proof (`public section`, strictly `std3` axioms):
1. Opaque `m8ScrSt` / `m8ScrFuelSt` wrappers and scoped `M8K6bTactics` (`O(1)` `FullMem` scratch &
   fuel load/store rules without 70-field `FullScratchState` expansion).
2. Shared `M8K6b` arithmetic and `M8PropKeep` helpers.
3. `full_k6_prop_m8_wp`: certifies `m8K6PropSpec` for `full_k6_prop_m8_body`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8CoreParity

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Opaque `FullState` Scratch/Fuel Wrappers & Scoped `M8K6bTactics` -/

/-- Scratch-buffer-updated `FullState` (kept opaque during symbolic execution). -/
def m8ScrSt (s : FullState) (scr : List (BitVec 32)) : FullState :=
  { s with scratch := { s.scratch with scratch_buf := scr } }

/-- Fuel-and-scratch-updated `FullState` (kept opaque during symbolic execution). -/
def m8ScrFuelSt (s : FullState) (fl : BitVec 64) (scr : List (BitVec 32)) : FullState :=
  { s with core := { s.core with fuel := fl }
           scratch := { s.scratch with scratch_buf := scr } }

theorem m8ScrSt_eq (s : FullState) (scr : List (BitVec 32)) :
    m8ScrSt s scr = { s with scratch := { s.scratch with scratch_buf := scr } } := by rfl

theorem m8ScrSt_self (s : FullState) : m8ScrSt s s.scratch.scratch_buf = s := by rfl

theorem m8ScrFuelSt_eq (s : FullState) (fl : BitVec 64) (scr : List (BitVec 32)) :
    m8ScrFuelSt s fl scr =
      { s with core := { s.core with fuel := fl }
               scratch := { s.scratch with scratch_buf := scr } } := by rfl

theorem m8ScrFuelSt_self (s : FullState) (scr : List (BitVec 32)) :
    m8ScrFuelSt s s.core.fuel scr = m8ScrSt s scr := by rfl

theorem m8ScrSt_lengthsOk {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {scr' : List (BitVec 32)} (hscr : scr'.length = c.scratch_cap) :
    (m8ScrSt s scr').LengthsOk c := by
  exact ⟨h.core_ok, { h.scratch_ok with scratch_buf_len := hscr }⟩

theorem m8ScrFuelSt_lengthsOk {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {scr' : List (BitVec 32)} (hscr : scr'.length = c.scratch_cap) (fl' : BitVec 64) :
    (m8ScrFuelSt s fl' scr').LengthsOk c := by
  exact ⟨{ h.core_ok with arena_len_le := h.core_ok.arena_len_le },
    { h.scratch_ok with scratch_buf_len := hscr }⟩

theorem m8ScrSt_upd (s : FullState) (scr scr' : List (BitVec 32)) :
    { m8ScrSt s scr with scratch := { (m8ScrSt s scr).scratch with scratch_buf := scr' } } =
      m8ScrSt s scr' := by rfl

theorem m8ScrFuelSt_upd (s : FullState) (fl : BitVec 64) (scr scr' : List (BitVec 32)) :
    { m8ScrFuelSt s fl scr with
        scratch := { (m8ScrFuelSt s fl scr).scratch with scratch_buf := scr' } } =
      m8ScrFuelSt s fl scr' := by rfl

theorem m8ScrFuelSt_upd_fuel (s : FullState) (fl fl' : BitVec 64) (scr : List (BitVec 32)) :
    { m8ScrFuelSt s fl scr with core := { (m8ScrFuelSt s fl scr).core with fuel := fl' } } =
      m8ScrFuelSt s fl' scr := by rfl

theorem m8ScrSt_buf (s : FullState) (scr : List (BitVec 32)) :
    (m8ScrSt s scr).scratch.scratch_buf = scr := by rfl

theorem m8ScrFuelSt_buf (s : FullState) (fl : BitVec 64) (scr : List (BitVec 32)) :
    (m8ScrFuelSt s fl scr).scratch.scratch_buf = scr := by rfl

theorem m8ScrFuelSt_fuel (s : FullState) (fl : BitVec 64) (scr : List (BitVec 32)) :
    (m8ScrFuelSt s fl scr).core.fuel = fl := by rfl

namespace M8K6bTactics

attribute [scoped bv_c0 high] bv_c0_zext32_64
attribute [scoped bv_c0] bv32_lshr_1 bv32_and_1 bv32_xor_1 List.length_set Bool.false_eq_true

@[scoped bv_c0] theorem m8k6_bv32_shl1 (x : BitVec 32) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem m8k6_bv32_shl1_or1 (x : BitVec 32) :
    ((x <<< (1 : Nat)) ||| (1 : BitVec 32)).toNat = (2 * x.toNat + 1) % 2 ^ 32 := by
  have h1 : (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 32 := m8k6_bv32_shl1 x
  rw [BitVec.toNat_or, h1, show (1 : BitVec 32).toNat = 1 from rfl]
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero =>
    rw [Nat.testBit_or, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
    have h0 : (2 * x.toNat % 2 ^ 32) % 2 = 0 := by omega
    have h1m : (2 * x.toNat + 1) % 2 ^ 32 % 2 = 1 := by omega
    rw [h0, h1m]; decide
  | succ j =>
    rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    have h1d : (1 : Nat) / 2 = 0 := rfl
    rw [h1d, Nat.zero_testBit, Bool.or_false]
    congr 1; omega

@[scoped c0_load] theorem c0_load_m8ScrSt_ptr {c : FullCfg} {s : FullState}
    {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c (m8ScrSt s scr) ⋆ R) m) :
    loadVal m i64 (c.hdr + 920) = some c.pScratchBuf :=
  FullArenaTactics.load_full_scratch_buf_ptr hm

@[scoped c0_load] theorem c0_load_m8ScrSt_imm {c : FullCfg} {s : FullState}
    {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {k : Nat}
    (hk : k < 15744) (hlen : 15744 ≤ scr.length)
    (hm : (FullMem c (m8ScrSt s scr) ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + BitVec.ofNat 64 k * 4) = some (scr[k]'(by omega)) := by
  have hk_eq : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 := FullArenaTactics.c0_load_full_scratch_buf (i := BitVec.ofNat 64 k)
    (by rw [m8ScrSt_buf, hk_eq]; omega) hm
  simpa only [m8ScrSt_buf, hk_eq] using h1

@[scoped c0_load] theorem c0_load_m8ScrSt {c : FullCfg} {s : FullState}
    {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < scr.length) (hm : (FullMem c (m8ScrSt s scr) ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + i * 4) = some scr[i.toNat] := by
  simpa only [m8ScrSt_buf] using
    FullArenaTactics.c0_load_full_scratch_buf (i := i) (by rw [m8ScrSt_buf]; exact hi) hm

@[scoped c0_store] theorem c0_store_m8ScrSt_imm {c : FullCfg} {s : FullState}
    {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {k : Nat} (v : BitVec 32)
    (hk : k < 15744) (hlen : 15744 ≤ scr.length)
    (hm : (FullMem c (m8ScrSt s scr) ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + BitVec.ofNat 64 k * 4) ∧
      (FullMem c (m8ScrSt s (scr.set k v)) ⋆ R)
        (storeMem m i32 (c.pScratchBuf + BitVec.ofNat 64 k * 4) v) := by
  have hk_eq : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 := FullArenaTactics.c0_store_full_scratch_buf (i := BitVec.ofNat 64 k) v
    (by rw [m8ScrSt_buf, hk_eq]; omega) hm
  simpa only [m8ScrSt_buf, m8ScrSt_upd, hk_eq] using h1

@[scoped c0_store] theorem c0_store_m8ScrSt {c : FullCfg} {s : FullState}
    {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < scr.length) (hm : (FullMem c (m8ScrSt s scr) ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + i * 4) ∧
      (FullMem c (m8ScrSt s (scr.set i.toNat v)) ⋆ R)
        (storeMem m i32 (c.pScratchBuf + i * 4) v) := by
  simpa only [m8ScrSt_buf, m8ScrSt_upd] using
    FullArenaTactics.c0_store_full_scratch_buf (i := i) v (by rw [m8ScrSt_buf]; exact hi) hm

@[scoped c0_load] theorem c0_load_m8ScrFuelSt_ptr {c : FullCfg} {s : FullState}
    {fl : BitVec 64} {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c (m8ScrFuelSt s fl scr) ⋆ R) m) :
    loadVal m i64 (c.hdr + 920) = some c.pScratchBuf :=
  FullArenaTactics.load_full_scratch_buf_ptr hm

@[scoped c0_load] theorem c0_load_m8ScrFuelSt_fuel {c : FullCfg} {s : FullState}
    {fl : BitVec 64} {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c (m8ScrFuelSt s fl scr) ⋆ R) m) :
    loadVal m i64 (c.hdr + 168) = some fl := by
  simpa only [m8ScrFuelSt_fuel] using FullArenaTactics.load_full_fuel hm

@[scoped c0_store] theorem c0_store_m8ScrFuelSt_fuel {c : FullCfg} {s : FullState}
    {fl : BitVec 64} {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hm : (FullMem c (m8ScrFuelSt s fl scr) ⋆ R) m) :
    storeOk m i64 (c.hdr + 168) ∧
      (FullMem c (m8ScrFuelSt s v scr) ⋆ R) (storeMem m i64 (c.hdr + 168) v) := by
  simpa only [m8ScrFuelSt_upd_fuel] using FullArenaTactics.store_full_fuel v hm

@[scoped c0_load] theorem c0_load_m8ScrFuelSt_imm {c : FullCfg} {s : FullState}
    {fl : BitVec 64} {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {k : Nat}
    (hk : k < 15744) (hlen : 15744 ≤ scr.length)
    (hm : (FullMem c (m8ScrFuelSt s fl scr) ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + BitVec.ofNat 64 k * 4) = some (scr[k]'(by omega)) := by
  have hk_eq : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 := FullArenaTactics.c0_load_full_scratch_buf (i := BitVec.ofNat 64 k)
    (by rw [m8ScrFuelSt_buf, hk_eq]; omega) hm
  simpa only [m8ScrFuelSt_buf, hk_eq] using h1

@[scoped c0_load] theorem c0_load_m8ScrFuelSt {c : FullCfg} {s : FullState}
    {fl : BitVec 64} {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < scr.length) (hm : (FullMem c (m8ScrFuelSt s fl scr) ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + i * 4) = some scr[i.toNat] := by
  simpa only [m8ScrFuelSt_buf] using
    FullArenaTactics.c0_load_full_scratch_buf (i := i) (by rw [m8ScrFuelSt_buf]; exact hi) hm

@[scoped c0_store] theorem c0_store_m8ScrFuelSt_imm {c : FullCfg} {s : FullState}
    {fl : BitVec 64} {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {k : Nat}
    (v : BitVec 32) (hk : k < 15744) (hlen : 15744 ≤ scr.length)
    (hm : (FullMem c (m8ScrFuelSt s fl scr) ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + BitVec.ofNat 64 k * 4) ∧
      (FullMem c (m8ScrFuelSt s fl (scr.set k v)) ⋆ R)
        (storeMem m i32 (c.pScratchBuf + BitVec.ofNat 64 k * 4) v) := by
  have hk_eq : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 := FullArenaTactics.c0_store_full_scratch_buf (i := BitVec.ofNat 64 k) v
    (by rw [m8ScrFuelSt_buf, hk_eq]; omega) hm
  simpa only [m8ScrFuelSt_buf, m8ScrFuelSt_upd, hk_eq] using h1

@[scoped c0_store] theorem c0_store_m8ScrFuelSt {c : FullCfg} {s : FullState}
    {fl : BitVec 64} {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (v : BitVec 32) (hi : i.toNat < scr.length)
    (hm : (FullMem c (m8ScrFuelSt s fl scr) ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + i * 4) ∧
      (FullMem c (m8ScrFuelSt s fl (scr.set i.toNat v)) ⋆ R)
        (storeMem m i32 (c.pScratchBuf + i * 4) v) := by
  simpa only [m8ScrFuelSt_buf, m8ScrFuelSt_upd] using
    FullArenaTactics.c0_store_full_scratch_buf (i := i) v (by rw [m8ScrFuelSt_buf]; exact hi) hm

end M8K6bTactics

open scoped M8K6bTactics

local macro "m8k6_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 2. Shared Pure & `M8PropKeep` Helpers -/

theorem m8k6_bv64_add2_lt {a b : BitVec 32} (h : a.toNat + b.toNat < 2 ^ 32) :
    (BitVec.setWidth 64 (a + b)).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (Nat.lt_trans h (by decide))]

theorem m8k6_off_sz_nowrap {o s acap len : Nat} (hos : o + s ≤ acap)
    (hle : 15744 + acap ≤ len) (hlt : len < 2 ^ 30) : o + s < 2 ^ 32 := by
  omega

theorem m8k6_slot_xor1_lt {w : BitVec 32} :
    ((w &&& 1#32) ^^^ 1#32).toNat < 2 := by
  have hlt : (w &&& 1#32).toNat < 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl]
    have := Nat.and_le_right (n := w.toNat) (m := 1); omega
  have h : (w &&& 1#32) = 0#32 ∨ (w &&& 1#32) = 1#32 := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h0 | h1
    · left; apply BitVec.eq_of_toNat_eq
      rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega
    · right; apply BitVec.eq_of_toNat_eq
      rw [show (1#32 : BitVec 32).toNat = 1 from rfl]; exact h1
  rcases h with h0 | h1
  · rw [h0]; decide
  · rw [h1]; decide

theorem m8k6_slot_lt {w : BitVec 32} : (w &&& 1#32).toNat < 2 := by
  rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl]
  have h1 : w.toNat &&& 1 ≤ 1 := Nat.and_le_right
  omega

theorem m8k6_or_lrn_and_ffff {lsz : BitVec 32} (hl : lsz.toNat < 2 ^ 16) :
    ((lsz ||| 0x40000000#32) &&& 0xFFFF#32) = lsz := by
  rw [(m8_bv32_bit_disj lsz 0x40000000#32 0xFFFF#32 (by decide)).1]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0xFFFF#32 : BitVec 32).toNat = 2 ^ 16 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hl]

/-- Frame invariant preserving `M8K6BufOk` and all postcondition slices of `m8K6PropSpec`. -/
private def M8PropKeep (scr0 scr : List (BitVec 32)) : Prop :=
  M8K6BufOk scr ∧ scr.length = scr0.length ∧
  (∀ i < 4195, scr[i]? = scr0[i]?) ∧
  (∀ i, 4199 ≤ i → i < 4204 → scr[i]? = scr0[i]?) ∧
  (∀ i, 4205 ≤ i → i < 4224 → scr[i]? = scr0[i]?) ∧
  (∀ i, 4736 ≤ i → i < 5504 → scr[i]? = scr0[i]?) ∧
  (∀ i, 6016 ≤ i → i < 6528 → scr[i]? = scr0[i]?) ∧
  (∀ i, 11648 ≤ i → i < 15744 → scr[i]? = scr0[i]?)

private theorem m8PropKeep_refl {scr0 : List (BitVec 32)} (h : M8K6BufOk scr0) :
    M8PropKeep scr0 scr0 :=
  ⟨h, rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

private theorem m8PropKeep_of_frame {scr0 scr scr' : List (BitVec 32)} (hk : M8PropKeep scr0 scr)
    (hlen : scr'.length = scr.length)
    (hlo : ∀ i < 4195, scr'[i]? = scr[i]?)
    (hm1 : ∀ i, 4199 ≤ i → i < 4204 → scr'[i]? = scr[i]?)
    (hm2 : ∀ i, 4205 ≤ i → i < 4224 → scr'[i]? = scr[i]?)
    (hm3 : ∀ i, 4736 ≤ i → i < 5504 → scr'[i]? = scr[i]?)
    (hm4 : ∀ i, 6016 ≤ i → i < 6528 → scr'[i]? = scr[i]?)
    (hhi : ∀ i, 11648 ≤ i → i < 15744 → scr'[i]? = scr[i]?) :
    M8PropKeep scr0 scr' := by
  have hok := m8K6BufOk_of_frame hk.1 hlen fun idx _ hor => by
    rcases hor with rfl | rfl | rfl | ⟨ha, hb⟩
    · exact hlo 4193 (by decide)
    · exact hm2 4206 (by decide) (by decide)
    · exact hm2 4207 (by decide) (by decide)
    · exact hhi idx ha (by omega)
  exact ⟨hok, hlen.trans hk.2.1,
    fun i hi => (hlo i hi).trans (hk.2.2.1 i hi),
    fun i h1 h2 => (hm1 i h1 h2).trans (hk.2.2.2.1 i h1 h2),
    fun i h1 h2 => (hm2 i h1 h2).trans (hk.2.2.2.2.1 i h1 h2),
    fun i h1 h2 => (hm3 i h1 h2).trans (hk.2.2.2.2.2.1 i h1 h2),
    fun i h1 h2 => (hm4 i h1 h2).trans (hk.2.2.2.2.2.2.1 i h1 h2),
    fun i h1 h2 => (hhi i h1 h2).trans (hk.2.2.2.2.2.2.2 i h1 h2)⟩

private theorem m8PropKeep_set_4196 {scr0 scr : List (BitVec 32)} (hk : M8PropKeep scr0 scr)
    (v : BitVec 32) : M8PropKeep scr0 (scr.set 4196 v) :=
  m8PropKeep_of_frame hk List.length_set
    (fun _ hi => List.getElem?_set_ne (by omega))
    (fun _ h1 h2 => List.getElem?_set_ne (by omega))
    (fun _ h1 h2 => List.getElem?_set_ne (by omega))
    (fun _ h1 h2 => List.getElem?_set_ne (by omega))
    (fun _ h1 h2 => List.getElem?_set_ne (by omega))
    (fun _ h1 h2 => List.getElem?_set_ne (by omega))

private theorem m8PropKeep_set_4204 {scr0 scr : List (BitVec 32)} (hk : M8PropKeep scr0 scr)
    (v : BitVec 32) : M8PropKeep scr0 (scr.set 4204 v) :=
  m8PropKeep_of_frame hk List.length_set
    (fun _ hi => List.getElem?_set_ne (by omega))
    (fun _ h1 h2 => List.getElem?_set_ne (by omega))
    (fun _ h1 h2 => List.getElem?_set_ne (by omega))
    (fun _ h1 h2 => List.getElem?_set_ne (by omega))
    (fun _ h1 h2 => List.getElem?_set_ne (by omega))
    (fun _ h1 h2 => List.getElem?_set_ne (by omega))

private theorem m8PropKeep_set_watch {scr0 scr : List (BitVec 32)} (hk : M8PropKeep scr0 scr)
    (idx : Nat) (v : BitVec 32) (hlo : 7040 ≤ idx) (hhi : idx < 11648) :
    M8PropKeep scr0 (scr.set idx v) :=
  m8PropKeep_of_frame hk List.length_set
    (fun _ hi => List.getElem?_set_ne (by omega))
    (fun _ h1 h2 => List.getElem?_set_ne (by omega))
    (fun _ h1 h2 => List.getElem?_set_ne (by omega))
    (fun _ h1 h2 => List.getElem?_set_ne (by omega))
    (fun _ h1 h2 => List.getElem?_set_ne (by omega))
    (fun _ h1 h2 => List.getElem?_set_ne (by omega))

private theorem m8PropKeep_set_arena {scr0 scr : List (BitVec 32)} (hk : M8PropKeep scr0 scr)
    (idx : Nat) (v : BitVec 32) (hlo : 15744 ≤ idx) :
    M8PropKeep scr0 (scr.set idx v) :=
  m8PropKeep_of_frame hk List.length_set
    (fun _ hi => List.getElem?_set_ne (by omega))
    (fun _ h1 h2 => List.getElem?_set_ne (by omega))
    (fun _ h1 h2 => List.getElem?_set_ne (by omega))
    (fun _ h1 h2 => List.getElem?_set_ne (by omega))
    (fun _ h1 h2 => List.getElem?_set_ne (by omega))
    (fun _ h1 h2 => List.getElem?_set_ne (by omega))

private theorem m8PropKeep_of_assign {scr0 scr scr' : List (BitVec 32)} (hk : M8PropKeep scr0 scr)
    (hlen : scr'.length = scr.length)
    (hkeep : ∀ idx < scr.length, idx ≠ 4197 → idx ≠ 4198 →
      (idx < 4224 ∨ 4736 ≤ idx) → (idx < 5504 ∨ 6016 ≤ idx) →
      (idx < 6528 ∨ 7040 ≤ idx) → scr'[idx]? = scr[idx]?) :
    M8PropKeep scr0 scr' := by
  have hb := hk.1.base_ge
  exact m8PropKeep_of_frame hk hlen
    (fun i hi => hkeep i (by omega) (by omega) (by omega)
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)))
    (fun i h1 h2 => hkeep i (by omega) (by omega) (by omega)
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)))
    (fun i h1 h2 => hkeep i (by omega) (by omega) (by omega)
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)))
    (fun i h1 h2 => hkeep i (by omega) (by omega) (by omega)
      (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)))
    (fun i h1 h2 => hkeep i (by omega) (by omega) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)))
    (fun i h1 h2 => hkeep i (by omega) (by omega) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)))

/-! ## 3. `full_k6_prop_m8_wp` -/

/-- Certifies `m8K6PropSpec` for `full_k6_prop_m8_body`. -/
theorem full_k6_prop_m8_wp (Γ : Env)
    (hAssign : ∀ a m Q X, m8K6AssignSpec a m Q X →
      Γ "full_k6_assign_m8" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, m8K6PropSpec a m Q X →
      Func.wp Γ full_k6_prop_m8_body a m Q X := by
  rintro ⟨hp, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen0, hsc, hok0, hm0, hQ⟩ := m8K6PropSpec_elim hSpec
  let scr0 := s.scratch.scratch_buf
  have hscr0_l : scr0.length = c.scratch_cap := hlen0.scratch_ok.scratch_buf_len
  have hbase : 15744 ≤ scr0.length := hok0.base_ge
  have hlt30 : scr0.length < 2 ^ 30 := hok0.length_lt
  have hm0' : (FullMem c (m8ScrSt s scr0) ⋆ R) m0 := by
    simpa only [m8ScrSt_self, scr0] using hm0
  clear hm0
  let nv := scr0[4192]'(by omega)
  let nc := scr0[4193]'(by omega)
  let acap := scr0[4207]'(by omega)
  have hretQ : ∀ (r : BitVec 32) (scr' : List (BitVec 32)) (m' : Mem 64),
      M8PropKeep scr0 scr' → (FullMem c (m8ScrSt s scr') ⋆ R) m' → Q (r, ()) m' :=
    fun r scr' m' hk hm' =>
      hQ r scr' m' hk.1 (hk.2.1.trans hscr0_l) hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2.1
        hk.2.2.2.2.2.1 hk.2.2.2.2.2.2.1 hk.2.2.2.2.2.2.2 (m8ScrSt_eq s scr' ▸ hm')
  unfold Func.wp full_k6_prop_m8_body
  c0_hsplit
  · c0_hsteps!
    exact hretQ 0xFFFFFFFF#32 scr0 m0 (m8PropKeep_refl hok0) hm0'
  · have hnv_le : nv.toNat ≤ 256 := Nat.le_of_not_lt (show ¬256 < nv.toNat from hc)
    clear hc
    c0_hsplit
    · c0_hsteps!
      exact hretQ 0xFFFFFFFF#32 scr0 m0 (m8PropKeep_refl hok0) hm0'
    · have hnc_le : nc.toNat ≤ 1024 := Nat.le_of_not_lt (show ¬1024 < nc.toNat from hc)
      clear hc
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i64])
        (fun rem (ticks, ()) mi => ∃ scri, M8PropKeep scr0 scri ∧
          rem = 256 - (scri[4196]?.getD 0#32).toNat ∧
          (FullMem c (m8ScrSt s scri) ⋆ R) mi)
        ?_ ?_
      · rintro Lo remo ⟨ticks, ⟨⟩⟩ mi hLo ⟨scri, hki, rfl, hmi⟩
        have hki_l := hki.2.1
        have hscri_base : 15744 ≤ scri.length := by rw [hki_l]; exact hbase
        rw [m8_k6_get_eq (by omega : 4196 < scri.length)] at hLo
        have hscri0 : scri[4192]'(by omega) = nv :=
          m8_k6_elem_of_opt (hki.2.2.1 4192 (by decide)) (by omega) (by omega)
        have hscri1 : scri[4193]'(by omega) = nc :=
          m8_k6_elem_of_opt (hki.2.2.1 4193 (by decide)) (by omega) (by omega)
        have hscri15 : scri[4207]'(by omega) = acap :=
          m8_k6_elem_of_opt (hki.2.2.2.2.1 4207 (by decide) (by decide)) (by omega) (by omega)
        c0_hsteps_nogrp
        refine wp_join0 (fun me => ∃ scre, M8PropKeep scr0 scre ∧
            (FullMem c (m8ScrSt s scre) ⋆ R) me) ?_ ?_
        · intro _ me ⟨scre, hke, hme⟩
          have hke_l := hke.2.1
          have hscre_base : 15744 ≤ scre.length := by rw [hke_l]; exact hbase
          c0_hsteps!
          exact hretQ 0xFFFFFFFF#32 _ m (m8PropKeep_set_4204 hke _) hm
        · intro Jex hJex
          c0_hsplit
          · c0_hsplit
            · have hk4_lt : (scri[4196]'(by omega)).toNat < 256 := hc
              clear hc
              have hpr_bd : 5504 + (scri[4196]'(by omega)).toNat < scri.length := by omega
              let lit := scri[5504 + (scri[4196]'(by omega)).toNat]'hpr_bd
              have hlit_ar_bd : (BitVec.setWidth 64
                  (5504#32 + scri[4196]'(by omega))).toNat < scri.length := by
                have := hk4_lt; c0_bound
              have hlit_c0 : scri[(BitVec.setWidth 64
                  (5504#32 + scri[4196]'(by omega))).toNat]'hlit_ar_bd = lit :=
                m8_k6_get_congr (by have := hk4_lt; c0_bound) _ hpr_bd
              have hk4_s : (scri[4196]'(by omega) + 1#32).toNat =
                  (scri[4196]'(by omega)).toNat + 1 := m8_bv32_add1_toNat hk4_lt (by decide)
              c0_hsteps_nogrp
              c0_hsplit
              · c0_hsteps!
                have hki1 := m8PropKeep_set_4196 hki (scri[4196]'(by omega) + 1#32)
                let scri1 := scri.set 4196 (scri[4196]'(by omega) + 1#32)
                have hscri1_l : scri1.length = scr0.length := by
                  dsimp only [scri1]; rw [List.length_set, hki_l]
                have hscri1_4 : 4196 < scri1.length := by rw [hscri1_l]; omega
                have h4_scri : 4196 < scri.length := by omega
                have hrem1 : 256 - (scri1[4196]'hscri1_4).toNat <
                    256 - (scri[4196]'h4_scri).toNat := by
                  have he4 : scri1[4196]'hscri1_4 = scri[4196]'h4_scri + 1#32 := by
                    dsimp only [scri1]
                    exact List.getElem_set_self (by rw [List.length_set]; exact h4_scri)
                  rw [he4, hk4_s]; omega
                exact hLo (256 - (scri1[4196]'hscri1_4).toNat) (ticks, ()) m hrem1
                  ⟨scri1, hki1, by rw [m8_k6_get_eq hscri1_4], hm⟩
              · let scri1 := scri.set 4196 (scri[4196]'(by omega) + 1#32)
                have hki1 : M8PropKeep scr0 scri1 := m8PropKeep_set_4196 hki _
                have hscri1_l : scri1.length = scr0.length := by
                  dsimp only [scri1]; rw [List.length_set, hki_l]
                have hscri1_base : 15744 ≤ scri1.length := by rw [hscri1_l]; exact hbase
                have hscri1_4 : 4196 < scri1.length := by rw [hscri1_l]; omega
                have h4_scri : 4196 < scri.length := by omega
                have hrem1 : 256 - (scri1[4196]'hscri1_4).toNat <
                    256 - (scri[4196]'h4_scri).toNat := by
                  have he4 : scri1[4196]'hscri1_4 = scri[4196]'h4_scri + 1#32 := by
                    dsimp only [scri1]
                    exact List.getElem_set_self (by rw [List.length_set]; exact h4_scri)
                  rw [he4, hk4_s]; omega
                have hlit_lt : lit.toNat < 2 * nv.toNat := by
                  have hidx : (5504 + (scri[4196]'(by omega)).toNat) % 4294967296 =
                      5504 + (scri[4196]'(by omega)).toNat := by omega
                  have hlit' : scri[(5504 + (scri[4196]'(by omega)).toNat) % 4294967296]'(by
                      rw [hidx]; exact hpr_bd) = lit := m8_k6_get_congr hidx _ hpr_bd
                  have htw : (2 * nv.toNat) % 4294967296 = 2 * nv.toNat := by omega
                  simpa [nv, hlit', htw] using hc
                clear hc
                have hnl_eq : (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 := by
                  rw [BitVec.toNat_xor, show (1#32 : BitVec 32).toNat = 1 from rfl]
                have hnl_lt : (lit ^^^ 1#32).toNat < 2 * nv.toNat := by
                  rw [hnl_eq]; have := fullInv_var_xor1 lit.toNat; omega
                have hw0_c0_bd : (BitVec.setWidth 64 (7040#32 +
                    (scri[(BitVec.setWidth 64 (5504#32 + scri[4196]'(by omega))).toNat]'hlit_ar_bd
                      ^^^ 1#32))).toNat < scri1.length := by
                  rw [hlit_c0, hscri1_l]; have := hnl_lt; c0_bound
                have hw0_bd : 7040 + (lit ^^^ 1#32).toNat < scri1.length := by
                  rw [hscri1_l]; omega
                c0_hsteps_nogrp
                refine wp_loop_group (ts := [i64, i64, i32, i32, i32])
                  (fun remw (t_w, vis_w, prev_w, w_w, wsteps_w, ()) mw =>
                    ∃ scrw, M8PropKeep scr0 scrw ∧ scrw[4196]? = scri1[4196]? ∧
                    wsteps_w.toNat ≤ 2048 ∧ remw = 2048 - wsteps_w.toNat ∧
                    (FullMem c (m8ScrSt s scrw) ⋆ R) mw)
                  ?_ ?_
                · rintro Li remw ⟨t_w, vis_w, prev_w, w_w, wsteps_w, ⟨⟩⟩ mw hLi
                    ⟨scrw, hkw, hkw4, hws_le, rfl, hmw⟩
                  have hkw_l := hkw.2.1
                  have hscrw_base : 15744 ≤ scrw.length := by rw [hkw_l]; exact hbase
                  have hscrw0 : scrw[4192]'(by omega) = nv :=
                    m8_k6_elem_of_opt (hkw.2.2.1 4192 (by decide)) (by omega) (by omega)
                  have hscrw1 : scrw[4193]'(by omega) = nc :=
                    m8_k6_elem_of_opt (hkw.2.2.1 4193 (by decide)) (by omega) (by omega)
                  have hscrw15 : scrw[4207]'(by omega) = acap :=
                    m8_k6_elem_of_opt (hkw.2.2.2.2.1 4207 (by decide) (by decide))
                      (by omega) (by omega)
                  c0_hsteps_nogrp
                  refine wp_join0 (fun mwi => ∃ scrwi, M8PropKeep scr0 scrwi ∧
                      scrwi[4196]? = scri1[4196]? ∧ (FullMem c (m8ScrSt s scrwi) ⋆ R) mwi) ?_ ?_
                  · intro _ mwi ⟨scrwi, hkwi, hkwi4, hmwi⟩
                    have hkwi_l := hkwi.2.1
                    have h4eqw : scrwi[4196]'(by omega) = scri1[4196]'hscri1_4 :=
                      m8_k6_elem_of_opt hkwi4 (by omega) hscri1_4
                    c0_hsteps!
                    exact hLo (256 - (scrwi[4196]'(by omega)).toNat)
                      (t_w + (vis_w >>> (4 : Nat)) + 1#64, ()) mwi
                      (by rw [h4eqw]; exact hrem1)
                      ⟨scrwi, hkwi, by rw [m8_k6_get_eq (by omega)], hmwi⟩
                  · intro Jwex hJwex
                    c0_hsplit
                    · have hw_lt : w_w.toNat < 2 * nc.toNat := by
                        have htw : (2 * nc.toNat) % 4294967296 = 2 * nc.toNat := by omega
                        simpa [nc, htw] using hc
                      clear hc
                      c0_hsplit
                      · have hws_lt : wsteps_w.toNat < 2048 := hc
                        clear hc
                        have hws1 : (wsteps_w + 1#32).toNat = wsteps_w.toNat + 1 :=
                          m8_bv32_add1_toNat hws_lt (by decide)
                        have hw_bd : w_w.toNat < 2048 := by omega
                        have hnxt_bd : (BitVec.setWidth 64 (7552 + w_w)).toNat <
                            scrw.length := by
                          have := hw_bd; c0_bound
                        let nxt := scrw[7552 + w_w.toNat]'(by omega)
                        have hnxt_eq :
                            scrw[(BitVec.setWidth 64 (7552 + w_w)).toNat]'hnxt_bd = nxt :=
                          m8_k6_get_congr (by have := hw_bd; c0_bound) _ (by omega)
                        have hwb_bd : (BitVec.setWidth 64 (9600 + w_w)).toNat <
                            scrw.length := by
                          have := hw_bd; c0_bound
                        let wb := scrw[9600 + w_w.toNat]'(by omega)
                        have hwb_eq :
                            scrw[(BitVec.setWidth 64 (9600 + w_w)).toNat]'hwb_bd = wb :=
                          m8_k6_get_congr (by have := hw_bd; c0_bound) _ (by omega)
                        let bv := wb &&& 2147483647
                        c0_hsplit
                        · c0_hsteps!
                          rw [hnxt_eq]
                          exact hLi (2048 - (wsteps_w + 1#32).toNat)
                            (t_w, vis_w + 1#64, w_w, nxt, wsteps_w + 1#32, ()) mw
                            (by omega) ⟨scrw, hkw, hkw4, by omega, rfl, hmw⟩
                        · have hbv_lt : bv.toNat < 2 * nv.toNat := by
                            have htw : (2 * nv.toNat) % 4294967296 = 2 * nv.toNat := by omega
                            have hwb_eq' : scrw[(9600 + w_w.toNat) % 4294967296]'(by omega) = wb :=
                              m8_k6_get_congr (by omega) _ (by omega)
                            have hbvv_eq : (wb &&& 2147483647).toNat =
                                wb.toNat &&& 2147483647 := by
                              rw [BitVec.toNat_and]; rfl
                            dsimp only [bv]
                            rw [hbvv_eq]
                            simpa [nv, htw, hwb_eq'] using hc
                          clear hc
                          have hbvv_c0_bd : (BitVec.setWidth 64 (6528 +
                              (scrw[(BitVec.setWidth 64 (9600 + w_w)).toNat]'hwb_bd &&&
                                2147483647))).toNat < scrw.length := by
                            rw [hwb_eq]
                            change (BitVec.setWidth 64 (6528 + bv)).toNat < scrw.length
                            have := hbv_lt; c0_bound
                          let bvv := scrw[6528 + bv.toNat]'(by omega)
                          c0_hsplit
                          · c0_hsteps!
                            rw [hnxt_eq]
                            exact hLi (2048 - (wsteps_w + 1#32).toNat)
                              (t_w, vis_w + 1#64, w_w, nxt, wsteps_w + 1#32, ()) mw
                              (by omega) ⟨scrw, hkw, hkw4, by omega, rfl, hmw⟩
                          · clear hc
                            let cid := w_w >>> (1 : Nat)
                            have hcid_eq : cid.toNat = w_w.toNat / 2 := m8_bv32_lshr1_toNat w_w
                            have hcid_lt : cid.toNat < nc.toNat := by omega
                            have hoff_c0_bd : (BitVec.setWidth 64
                                (11648 + (w_w >>> (1 : Nat)))).toNat < scrw.length := by
                              have : (w_w >>> (1 : Nat)).toNat < nc.toNat :=
                                hcid_eq ▸ hcid_lt
                              c0_bound
                            have hcm_c0_bd : (BitVec.setWidth 64
                                (12672 + (w_w >>> (1 : Nat)))).toNat < scrw.length := by
                              have : (w_w >>> (1 : Nat)).toNat < nc.toNat :=
                                hcid_eq ▸ hcid_lt
                              c0_bound
                            c0_hsplit
                            · clear hc
                              c0_hsplit
                              · c0_hsteps!
                                exact hretQ cid _ m (m8PropKeep_set_4204 hkw _) hm
                              · c0_hsteps_nogrp
                                refine wp_join0 (fun ma => ∃ scra, M8PropKeep scr0 scra ∧
                                    scra[4196]? = scri1[4196]? ∧
                                    (FullMem c (m8ScrSt s scra) ⋆ R) ma) ?_ ?_
                                · intro _ ma ⟨scra, hka, hka4, hma⟩
                                  c0_hsteps!
                                  rw [hnxt_eq]
                                  exact hLi (2048 - (wsteps_w + 1#32).toNat)
                                    (t_w, vis_w + 1#64, w_w, nxt, wsteps_w + 1#32, ()) ma
                                    (by omega) ⟨scra, hka, hka4, by omega, rfl, hma⟩
                                · intro Ja hJa
                                  c0_hsplit
                                  · c0_hsteps_nogrp
                                    m8k6_call hAssign
                                    try rw [hwb_eq]
                                    refine m8K6AssignSpec_intro rfl
                                      (m8ScrSt_lengthsOk hlen0 (hkw_l.trans hscr0_l)) hsc hmw ?_
                                    intro scra ma hlena hkeepa hma
                                    rw [m8ScrSt_buf] at hkeepa
                                    rw [m8ScrSt_upd] at hma
                                    have hka4 : scra[4196]? = scri1[4196]? := by
                                      have := hkeepa 4196 (by omega) (by decide) (by decide)
                                        (Or.inl (by decide)) (Or.inl (by decide))
                                        (Or.inl (by decide))
                                      exact this.trans hkw4
                                    exact hJa ma ⟨scra, m8PropKeep_of_assign hkw
                                      (hlena.trans (hkw_l.trans hscr0_l).symm)
                                      (fun idx hi => hkeepa idx (by omega)), hka4, hma⟩
                                  · c0_hsteps!
                                    exact hJa mw ⟨scrw, hkw, hkw4, hmw⟩
                            · clear hc
                              let slot := w_w &&& 1
                              have hslot_lt : slot.toNat < 2 := m8k6_slot_lt
                              have hslot1_lt : (slot ^^^ 1).toNat < 2 := m8k6_slot_xor1_lt
                              let off := scrw[11648 + cid.toNat]'(by omega)
                              have hoff_eq : scrw[(BitVec.setWidth 64
                                  (11648 + (w_w >>> (1 : Nat)))).toNat]'hoff_c0_bd =
                                  off := by
                                refine m8_k6_get_congr ?_ _ (by omega)
                                change (BitVec.setWidth 64 (11648 + cid)).toNat = 11648 + cid.toNat
                                have := hcid_lt; c0_bound
                              let cm := scrw[12672 + cid.toNat]'(by omega)
                              have hcm_eq : scrw[(BitVec.setWidth 64
                                  (12672 + (w_w >>> (1 : Nat)))).toNat]'hcm_c0_bd =
                                  cm := by
                                refine m8_k6_get_congr ?_ _ (by omega)
                                change (BitVec.setWidth 64 (12672 + cid)).toNat = 12672 + cid.toNat
                                have := hcid_lt; c0_bound
                              let sz := cm &&& 65535
                              have hcl := hkw.1.clause_ok
                                (by rw [m8_k6_get_eq (by omega), hscrw1]; exact hcid_lt)
                              rw [m8_k6_get_eq (by omega : 11648 + cid.toNat < scrw.length),
                                m8_k6_get_eq (by omega : 12672 + cid.toNat < scrw.length),
                                m8_k6_get_eq (by omega : 4207 < scrw.length), hscrw15] at hcl
                              have hos_le : off.toNat + sz.toNat ≤ acap.toNat := hcl.1
                              have hlt30w := hkw.1.length_lt
                              have hgew := hkw.1.length_ge
                              rw [m8_k6_get_eq (by omega : 4207 < scrw.length), hscrw15] at hgew
                              have hos_nw : off.toNat + sz.toNat < 2 ^ 32 :=
                                m8k6_off_sz_nowrap hos_le hgew hlt30w
                              c0_hsplit
                              · c0_hsteps!
                                rw [hnxt_eq]
                                exact hLi (2048 - (wsteps_w + 1#32).toNat)
                                  (t_w, vis_w + 1#64, w_w, nxt, wsteps_w + 1#32, ()) mw
                                  (by omega) ⟨scrw, hkw, hkw4, by omega, rfl, hmw⟩
                              · have hcm_eq' : scrw[(BitVec.toNat 12672 + BitVec.toNat w_w / 2) %
                                    2 ^ 32]'(by
                                    rw [show (BitVec.toNat (12672 : BitVec 32)) = 12672 from rfl,
                                      ← hcid_eq]
                                    have := hcid_lt; omega) = cm :=
                                  m8_k6_get_congr (by
                                    rw [show (BitVec.toNat (12672 : BitVec 32)) = 12672 from rfl,
                                      ← hcid_eq]
                                    have := hcid_lt; omega) _ (by omega)
                                have hsz_ge : 2 ≤ sz.toNat := by
                                  rw [hcm_eq'] at hc
                                  change ¬(cm &&& 65535).toNat < (2 : BitVec 32).toNat at hc
                                  rw [show (2 : BitVec 32).toNat = 2 from rfl] at hc
                                  exact Nat.le_of_not_lt hc
                                clear hc
                                c0_hsplit
                                · c0_hsteps!
                                  rw [hnxt_eq]
                                  exact hLi (2048 - (wsteps_w + 1#32).toNat)
                                    (t_w, vis_w + 1#64, w_w, nxt, wsteps_w + 1#32, ()) mw
                                    (by omega) ⟨scrw, hkw, hkw4, by omega, rfl, hmw⟩
                                · clear hc
                                  have hot_bd : 15744 + off.toNat + (slot ^^^ 1).toNat <
                                      scrw.length := by omega
                                  let other := scrw[15744 + off.toNat + (slot ^^^ 1).toNat]'hot_bd
                                  have hot_c0_bd : (BitVec.setWidth 64 (15744 +
                                      scrw[(BitVec.setWidth 64
                                        (11648 + (w_w >>> (1 : Nat)))).toNat]'hoff_c0_bd +
                                      ((w_w &&& 1) ^^^ 1))).toNat < scrw.length := by
                                    rw [hoff_eq]
                                    change (BitVec.setWidth 64 (15744 + off +
                                      (slot ^^^ 1))).toNat < scrw.length
                                    have := hsz_ge; have := hslot1_lt; c0_bound
                                  have hoeq : scrw[(BitVec.setWidth 64 (15744 +
                                      scrw[(BitVec.setWidth 64
                                        (11648 + (w_w >>> (1 : Nat)))).toNat]'hoff_c0_bd +
                                      ((w_w &&& 1) ^^^ 1))).toNat]'hot_c0_bd = other := by
                                    refine m8_k6_get_congr ?_ _ hot_bd
                                    rw [hoff_eq]
                                    change (BitVec.setWidth 64 (15744 + off +
                                      (slot ^^^ 1))).toNat = _
                                    have := hsz_ge; have := hslot1_lt; c0_bound
                                  c0_hsplit
                                  · c0_hsteps!
                                    rw [hnxt_eq]
                                    exact hLi (2048 - (wsteps_w + 1#32).toNat)
                                      (t_w, vis_w + 1#64, w_w, nxt, wsteps_w + 1#32, ()) mw
                                      (by omega) ⟨scrw, hkw, hkw4, by omega, rfl, hmw⟩
                                  · have hoff_eq' : scrw[(11648 + w_w.toNat / 2) % 4294967296]'(by
                                        rw [← hcid_eq]; have := hcid_lt; omega) = off :=
                                      m8_k6_get_congr (by rw [← hcid_eq]; have := hcid_lt; omega) _
                                        (by omega)
                                    have hslot1_eq : (slot ^^^ 1).toNat = w_w.toNat % 2 ^^^ 1 := by
                                      dsimp only [slot]
                                      rw [BitVec.toNat_xor, BitVec.toNat_and,
                                        show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
                                    have hoeq'_bd : (15744 + (scrw[(11648 + w_w.toNat / 2) %
                                        4294967296]'(by
                                          rw [← hcid_eq]; have := hcid_lt; omega)).toNat +
                                        (w_w.toNat % 2 ^^^ 1)) % 4294967296 < scrw.length := by
                                      rw [hoff_eq', ← hslot1_eq]
                                      have := hsz_ge; have := hslot1_lt; omega
                                    have hoeq' : scrw[(15744 + (scrw[(11648 + w_w.toNat / 2) %
                                        4294967296]'(by
                                          rw [← hcid_eq]; have := hcid_lt; omega)).toNat +
                                        (w_w.toNat % 2 ^^^ 1)) % 4294967296]'hoeq'_bd = other := by
                                      refine m8_k6_get_congr ?_ _ hot_bd
                                      rw [hoff_eq', ← hslot1_eq]
                                      have := hsz_ge; have := hslot1_lt; omega
                                    have hoth_lt : other.toNat < 2 * nv.toNat := by
                                      have htw : (2 * nv.toNat) % 4294967296 = 2 * nv.toNat := by
                                        omega
                                      simpa [nv, hoeq', htw] using hc
                                    clear hc
                                    have hov_c0_bd : (BitVec.setWidth 64 (6528 +
                                        scrw[(BitVec.setWidth 64 (15744 +
                                          scrw[(BitVec.setWidth 64 (11648 +
                                            (w_w >>> (1 : Nat)))).toNat]'hoff_c0_bd +
                                          ((w_w &&& 1) ^^^ 1))).toNat]'hot_c0_bd)).toNat <
                                        scrw.length := by
                                      rw [hoeq]; have := hoth_lt; c0_bound
                                    c0_hsplit
                                    · c0_hsteps!
                                      have hwb_bd_eq : (BitVec.setWidth 64 (9600 + w_w)).toNat =
                                          9600 + w_w.toNat := by
                                        have := hw_bd; c0_bound
                                      rw [hwb_bd_eq, hoeq] at hm
                                      have hkw_wb := m8PropKeep_set_watch hkw (9600 + w_w.toNat)
                                        other (by omega) (by omega)
                                      have h4wb : (scrw.set (9600 + w_w.toNat) other)[4196]? =
                                          scri1[4196]? := by
                                        rw [List.getElem?_set_ne (by omega)]; exact hkw4
                                      rw [hnxt_eq]
                                      exact hLi (2048 - (wsteps_w + 1#32).toNat)
                                        (t_w + 1#64, vis_w + 1#64, w_w, nxt,
                                          wsteps_w + 1#32, ()) m
                                        (by omega) ⟨_, hkw_wb, h4wb, by omega, rfl, hm⟩
                                    · clear hc
                                      c0_hsteps_nogrp
                                      refine wp_loop_break_group
                                        (brkTs := [i32, i32, i32]) (lpTs := [i32])
                                        (fun (_, ri, repl, ()) mr => mw = mr ∧
                                          (ri = 0xFFFFFFFF#32 ∨
                                            (ri.toNat < sz.toNat ∧ repl.toNat < 2 * nv.toNat)))
                                        (fun remr (r, ()) mr => mw = mr ∧
                                          2 ≤ r.toNat ∧ r.toNat ≤ sz.toNat ∧
                                          remr = sz.toNat - r.toNat)
                                        ?_ ?_ ?_
                                      · rintro _ ⟨_, ri, repl, ⟨⟩⟩ mr ⟨hmr, hri⟩
                                        subst mr
                                        c0_hsplit
                                        · rcases hri with hff | ⟨hri_lt, hrep_lt⟩
                                          · exact absurd hff hc
                                          clear hc
                                          have h_nlt : scri1.length = scrw.length := by omega
                                          have hst1_bd : (BitVec.setWidth 64 (15744 +
                                              scrw[(BitVec.setWidth 64 (11648 +
                                                w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                              (w_w &&& 1))).toNat < scrw.length := by
                                            rw [hoff_eq]
                                            change (BitVec.setWidth 64
                                              (15744 + off + slot)).toNat < scrw.length
                                            have := hsz_ge; have := hslot_lt; c0_bound
                                          have hst2_bd : (BitVec.setWidth 64 (15744 +
                                              scrw[(BitVec.setWidth 64 (11648 +
                                                w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                              ri)).toNat <
                                              (scrw.set (BitVec.setWidth 64 (15744 +
                                                scrw[(BitVec.setWidth 64 (11648 +
                                                  w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                                (w_w &&& 1))).toNat repl).length := by
                                            rw [List.length_set, hoff_eq]
                                            have := hri_lt; c0_bound
                                          c0_hsteps_nogrp
                                          refine wp_join0 (fun mpr => ∃ scrp, M8PropKeep scr0 scrp ∧
                                              scrp[4196]? = scri1[4196]? ∧
                                              scrp.length = scrw.length ∧
                                              (FullMem c (m8ScrSt s scrp) ⋆ R) mpr) ?_ ?_
                                          · intro _ mpr ⟨scrp, hkp, hkp4, hkp_l, hmpr⟩
                                            clear hm m
                                            have hkp_9600 : (BitVec.setWidth 64
                                                (9600 + w_w)).toNat < scrp.length := by
                                              rw [hkp_l]; exact hwb_bd
                                            have h9600_eq : (BitVec.setWidth 64
                                                (9600 + w_w)).toNat =
                                                9600 + w_w.toNat := by
                                              have := hw_bd; c0_bound
                                            c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
                                            rw [h9600_eq, hoeq] at hm
                                            have hkp1_7040 : (BitVec.setWidth 64
                                                (7040 + repl)).toNat <
                                                (scrp.set (9600 + w_w.toNat) other).length := by
                                              rw [List.length_set, hkp_l]
                                              have := hrep_lt; c0_bound
                                            have hkp1_7552 : (BitVec.setWidth 64
                                                (7552 + w_w)).toNat <
                                                (scrp.set (9600 + w_w.toNat) other).length := by
                                              rw [List.length_set, hkp_l]
                                              have := hw_bd; c0_bound
                                            c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
                                            c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
                                            have h7552_lt32 : 7552 + w_w.toNat < 2 ^ 32 :=
                                              Nat.lt_trans (Nat.add_lt_add_left hw_bd 7552)
                                                (by decide)
                                            have h7552_eq : (BitVec.setWidth 64
                                                (7552 + w_w)).toNat = 7552 + w_w.toNat := by
                                              rw [BitVec.toNat_setWidth, BitVec.toNat_add]
                                              change (7552 + w_w.toNat) % 2 ^ 32 % 2 ^ 64 = _
                                              rw [Nat.mod_eq_of_lt h7552_lt32, Nat.mod_eq_of_lt
                                                (Nat.lt_trans h7552_lt32 (by decide))]
                                            have h7040_lt32 : 7040 + repl.toNat < 2 ^ 32 :=
                                              Nat.lt_trans (Nat.add_lt_add_left
                                                (Nat.lt_of_lt_of_le hrep_lt
                                                  (Nat.mul_le_mul_left 2 hnv_le)) 7040)
                                                (by decide)
                                            have h7040_eq : (BitVec.setWidth 64
                                                (7040 + repl)).toNat = 7040 + repl.toNat := by
                                              rw [BitVec.toNat_setWidth, BitVec.toNat_add]
                                              change (7040 + repl.toNat) % 2 ^ 32 % 2 ^ 64 = _
                                              rw [Nat.mod_eq_of_lt h7040_lt32, Nat.mod_eq_of_lt
                                                (Nat.lt_trans h7040_lt32 (by decide))]
                                            rw [h7552_eq] at hm
                                            have hkp2_7040 : (BitVec.setWidth 64
                                                (7040 + repl)).toNat <
                                                ((scrp.set (9600 + w_w.toNat) other).set
                                                  (7552 + w_w.toNat)
                                                  ((scrp.set (9600 + w_w.toNat) other)[
                                                    (BitVec.setWidth 64
                                                      (7040 + repl)).toNat]'hkp1_7040)).length := by
                                              rw [List.length_set]; exact hkp1_7040
                                            c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
                                            have h7040_set (xs : List (BitVec 32)) :
                                                xs.set (BitVec.setWidth 64 (7040 + repl)).toNat
                                                  w_w = xs.set (7040 + repl.toNat) w_w := by
                                              rw [h7040_eq]
                                            rw [h7040_set] at hm
                                            c0_hfast
                                            have hkp1 := m8PropKeep_set_watch hkp
                                              (9600 + w_w.toNat) other (by omega) (by omega)
                                            have hkp2 (v : BitVec 32) := m8PropKeep_set_watch hkp1
                                              (7552 + w_w.toNat) v (by omega) (by omega)
                                            have hkp3 (v : BitVec 32) :=
                                              m8PropKeep_set_watch (hkp2 v)
                                                (7040 + repl.toNat) w_w (by omega) (by omega)
                                            have h4fin (v : BitVec 32) :
                                                (((scrp.set (9600 + w_w.toNat) other).set
                                                  (7552 + w_w.toNat) v).set
                                                  (7040 + repl.toNat) w_w)[4196]? =
                                                  scri1[4196]? := by
                                              rw [List.getElem?_set_ne (by omega),
                                                List.getElem?_set_ne (by omega),
                                                List.getElem?_set_ne (by omega)]
                                              exact hkp4
                                            rw [hnxt_eq]
                                            exact hLi (2048 - (wsteps_w + 1#32).toNat)
                                              (t_w + 1#64, vis_w + 1#64, prev_w, nxt,
                                                wsteps_w + 1#32, ())
                                              m (by omega) ⟨_, hkp3 _, h4fin _, by omega, rfl, hm⟩
                                          · intro Jpr hJpr
                                            have hka1 := m8PropKeep_set_arena hkw
                                              (15744 + off.toNat + slot.toNat) repl (by omega)
                                            have hka2 := m8PropKeep_set_arena hka1
                                              (15744 + off.toNat + ri.toNat) (lit ^^^ 1#32)
                                              (by omega)
                                            have hk4a2 : ((scrw.set (15744 + off.toNat + slot.toNat)
                                                repl).set (15744 + off.toNat + ri.toNat)
                                                (lit ^^^ 1#32))[4196]? = scri1[4196]? := by
                                              rw [List.getElem?_set_ne (by omega),
                                                List.getElem?_set_ne (by omega)]
                                              exact hkw4
                                            have hos_lt32 :
                                                15744 + (off.toNat + sz.toNat) < 2 ^ 32 :=
                                              Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.le_trans
                                                (Nat.add_le_add_left hos_le 15744) hgew)
                                                hlt30w) (by decide)
                                            have hst1_lt :
                                                15744 + off.toNat + slot.toNat < 2 ^ 32 := by
                                              refine Nat.lt_trans (Nat.add_lt_add_left
                                                (Nat.lt_of_lt_of_le hslot_lt hsz_ge) _) ?_
                                              rw [Nat.add_assoc]; exact hos_lt32
                                            have hst1_eq : (BitVec.setWidth 64 (15744 +
                                                scrw[(BitVec.setWidth 64 (11648 +
                                                  w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                                (w_w &&& 1))).toNat =
                                                15744 + off.toNat + slot.toNat := by
                                              rw [hoff_eq]
                                              change (BitVec.setWidth 64
                                                (15744 + off + slot)).toNat = _
                                              rw [BitVec.toNat_setWidth, BitVec.toNat_add,
                                                BitVec.toNat_add]
                                              change ((15744 + off.toNat) % 2 ^ 32 +
                                                slot.toNat) % 2 ^ 32 % 2 ^ 64 = _
                                              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
                                                  (Nat.le_add_right _ _) hst1_lt),
                                                Nat.mod_eq_of_lt hst1_lt,
                                                Nat.mod_eq_of_lt
                                                  (Nat.lt_trans hst1_lt (by decide))]
                                            have hst2_lt :
                                                15744 + off.toNat + ri.toNat < 2 ^ 32 := by
                                              refine Nat.lt_trans
                                                (Nat.add_lt_add_left hri_lt _) ?_
                                              rw [Nat.add_assoc]; exact hos_lt32
                                            have hst2_eq : (BitVec.setWidth 64 (15744 +
                                                scrw[(BitVec.setWidth 64 (11648 +
                                                  w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                                ri)).toNat = 15744 + off.toNat + ri.toNat := by
                                              rw [hoff_eq]
                                              rw [BitVec.toNat_setWidth, BitVec.toNat_add,
                                                BitVec.toNat_add]
                                              change ((15744 + off.toNat) % 2 ^ 32 +
                                                ri.toNat) % 2 ^ 32 % 2 ^ 64 = _
                                              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
                                                  (Nat.le_add_right _ _) hst2_lt),
                                                Nat.mod_eq_of_lt hst2_lt,
                                                Nat.mod_eq_of_lt
                                                  (Nat.lt_trans hst2_lt (by decide))]
                                            c0_hsplit
                                            · have hst3a_bd : (BitVec.setWidth 64 (7040#32 +
                                                  (scri[(BitVec.setWidth 64 (5504#32 +
                                                    scri[4196]'(by omega))).toNat]'hlit_ar_bd
                                                    ^^^ 1#32))).toNat <
                                                  ((scrw.set (BitVec.setWidth 64 (15744#32 +
                                                    scrw[(BitVec.setWidth 64 (11648#32 +
                                                      w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                                    (w_w &&& 1#32))).toNat repl).set
                                                    (BitVec.setWidth 64 (15744#32 +
                                                      scrw[(BitVec.setWidth 64 (11648#32 +
                                                        w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                                      ri)).toNat
                                                    (scri[(BitVec.setWidth 64 (5504#32 +
                                                      scri[4196]'(by omega))).toNat]'hlit_ar_bd
                                                      ^^^ 1#32)).length := by
                                                rw [List.length_set, List.length_set, ← h_nlt]
                                                exact hw0_c0_bd
                                              c0_hfast
                                              have hst3a_eq : (BitVec.setWidth 64 (7040#32 +
                                                  (scri[(BitVec.setWidth 64 (5504#32 +
                                                    scri[4196]'(by omega))).toNat]'hlit_ar_bd
                                                    ^^^ 1#32))).toNat =
                                                  7040 + (lit ^^^ 1#32).toNat := by
                                                rw [hlit_c0]
                                                have h7040_lt :
                                                    7040 + (lit ^^^ 1#32).toNat < 2 ^ 32 :=
                                                  Nat.lt_trans (Nat.add_lt_add_left
                                                    (Nat.lt_of_lt_of_le hnl_lt
                                                      (Nat.mul_le_mul_left 2 hnv_le)) 7040)
                                                    (by decide)
                                                rw [BitVec.toNat_setWidth, BitVec.toNat_add]
                                                change (7040 + (lit ^^^ 1#32).toNat) %
                                                  2 ^ 32 % 2 ^ 64 = _
                                                rw [Nat.mod_eq_of_lt h7040_lt,
                                                  Nat.mod_eq_of_lt
                                                    (Nat.lt_trans h7040_lt (by decide))]
                                              have hm' : (FullMem c (m8ScrSt s
                                                  (((scrw.set (15744 + off.toNat + slot.toNat)
                                                    repl).set (15744 + off.toNat + ri.toNat)
                                                    (lit ^^^ 1#32)).set
                                                    (7040 + (lit ^^^ 1#32).toNat) nxt)) ⋆ R) m := by
                                                rw [← hst1_eq, ← hst2_eq, ← hst3a_eq, ← hlit_c0,
                                                  ← hnxt_eq]
                                                exact hm
                                              have hka3 := m8PropKeep_set_watch hka2
                                                (7040 + (lit ^^^ 1#32).toNat) nxt
                                                (by omega) (by omega)
                                              have hk4a3 : (((scrw.set (15744 + off.toNat +
                                                  slot.toNat) repl).set
                                                  (15744 + off.toNat + ri.toNat)
                                                  (lit ^^^ 1#32)).set
                                                  (7040 + (lit ^^^ 1#32).toNat) nxt)[4196]? =
                                                  scri1[4196]? := by
                                                rw [List.getElem?_set_ne (by omega)]; exact hk4a2
                                              exact hJpr m ⟨_, hka3, hk4a3,
                                                by simp only [List.length_set], hm'⟩
                                            · have hprev_lt : prev_w.toNat < 2 * nc.toNat := by
                                                have htw : (2 * nc.toNat) % 4294967296 =
                                                    2 * nc.toNat := by omega
                                                simpa [nc, htw] using hc
                                              have hpv_lt2048 : prev_w.toNat < 2048 :=
                                                Nat.lt_of_lt_of_le hprev_lt
                                                  (Nat.mul_le_mul_left 2 hnc_le)
                                              have h7552p_lt : 7552 + prev_w.toNat < 2 ^ 32 :=
                                                Nat.lt_trans (Nat.add_lt_add_left hpv_lt2048 7552)
                                                  (by decide)
                                              have hst3b_eq : (BitVec.setWidth 64
                                                  (7552 + prev_w)).toNat = 7552 + prev_w.toNat := by
                                                rw [BitVec.toNat_setWidth, BitVec.toNat_add]
                                                change (7552 + prev_w.toNat) % 2 ^ 32 % 2 ^ 64 = _
                                                rw [Nat.mod_eq_of_lt h7552p_lt, Nat.mod_eq_of_lt
                                                  (Nat.lt_trans h7552p_lt (by decide))]
                                              have hst3b_bd : (BitVec.setWidth 64
                                                  (7552 + prev_w)).toNat <
                                                  ((scrw.set (BitVec.setWidth 64 (15744#32 +
                                                    scrw[(BitVec.setWidth 64 (11648#32 +
                                                      w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                                    (w_w &&& 1#32))).toNat repl).set
                                                    (BitVec.setWidth 64 (15744#32 +
                                                      scrw[(BitVec.setWidth 64 (11648#32 +
                                                        w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                                      ri)).toNat
                                                    (scri[(BitVec.setWidth 64 (5504#32 +
                                                      scri[4196]'(by omega))).toNat]'hlit_ar_bd
                                                      ^^^ 1#32)).length := by
                                                rw [List.length_set, List.length_set, hst3b_eq,
                                                  hkw_l]
                                                exact Nat.lt_of_lt_of_le
                                                  (Nat.add_lt_add_left hpv_lt2048 7552)
                                                  (Nat.le_trans (by decide) hbase)
                                              c0_hfast
                                              have hm' : (FullMem c (m8ScrSt s
                                                  (((scrw.set (15744 + off.toNat + slot.toNat)
                                                    repl).set (15744 + off.toNat + ri.toNat)
                                                    (lit ^^^ 1#32)).set
                                                    (7552 + prev_w.toNat) nxt)) ⋆ R) m := by
                                                rw [← hst1_eq, ← hst2_eq, ← hst3b_eq, ← hlit_c0,
                                                  ← hnxt_eq]
                                                exact hm
                                              have hka3 := m8PropKeep_set_watch hka2
                                                (7552 + prev_w.toNat) nxt (by omega) (by omega)
                                              have hk4a3 : (((scrw.set (15744 + off.toNat +
                                                  slot.toNat) repl).set
                                                  (15744 + off.toNat + ri.toNat)
                                                  (lit ^^^ 1#32)).set
                                                  (7552 + prev_w.toNat) nxt)[4196]? =
                                                  scri1[4196]? := by
                                                rw [List.getElem?_set_ne (by omega)]; exact hk4a2
                                              exact hJpr m ⟨_, hka3, hk4a3,
                                                by simp only [List.length_set], hm'⟩
                                        · clear hc
                                          have h9600_lt32 : 9600 + w_w.toNat < 2 ^ 32 :=
                                            Nat.lt_trans (Nat.add_lt_add_left hw_bd 9600)
                                              (by decide)
                                          have hwb_bd_eq : (BitVec.setWidth 64
                                              (9600 + w_w)).toNat = 9600 + w_w.toNat := by
                                            rw [BitVec.toNat_setWidth, BitVec.toNat_add]
                                            change (9600 + w_w.toNat) % 2 ^ 32 % 2 ^ 64 = _
                                            rw [Nat.mod_eq_of_lt h9600_lt32, Nat.mod_eq_of_lt
                                              (Nat.lt_trans h9600_lt32 (by decide))]
                                          have hov_lt32 : 6528 + other.toNat < 2 ^ 32 :=
                                            Nat.lt_trans (Nat.add_lt_add_left
                                              (Nat.lt_of_lt_of_le hoth_lt
                                                (Nat.mul_le_mul_left 2 hnv_le)) 6528) (by decide)
                                          have hov_set_bd : (BitVec.setWidth 64 (6528 +
                                              scrw[(BitVec.setWidth 64 (15744 +
                                                scrw[(BitVec.setWidth 64 (11648 +
                                                  w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                                ((w_w &&& 1) ^^^ 1))).toNat]'hot_c0_bd)).toNat <
                                              (scrw.set (BitVec.setWidth 64 (9600 + w_w)).toNat
                                                (scrw[(BitVec.setWidth 64 (15744 +
                                                  scrw[(BitVec.setWidth 64 (11648 +
                                                    w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                                  ((w_w &&& 1) ^^^
                                                    1))).toNat]'hot_c0_bd)).length := by
                                            rw [List.length_set, hoeq, BitVec.toNat_setWidth,
                                              BitVec.toNat_add]
                                            change (6528 + other.toNat) % 2 ^ 32 % 2 ^ 64 < _
                                            rw [Nat.mod_eq_of_lt hov_lt32, Nat.mod_eq_of_lt
                                              (Nat.lt_trans hov_lt32 (by decide)), hkw_l]
                                            exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left
                                              (Nat.lt_of_lt_of_le hoth_lt
                                                (Nat.mul_le_mul_left 2 hnv_le)) 6528)
                                              (Nat.le_trans (by decide) hbase)
                                          have hkw_wb := m8PropKeep_set_watch hkw (9600 + w_w.toNat)
                                            other (by omega) (by omega)
                                          have h4wb : (scrw.set (9600 + w_w.toNat) other)[4196]? =
                                              scri1[4196]? := by
                                            rw [List.getElem?_set_ne (by omega)]; exact hkw4
                                          c0_hsplit
                                          · rw [hwb_bd_eq, hoeq] at hm
                                            clear hAssign hLo hLi hJwex hJex
                                            have h4204_base : 15744 ≤
                                                (scrw.set (9600 + w_w.toNat) other).length := by
                                              rw [List.length_set]; exact hscrw_base
                                            c0_hfast
                                            exact hretQ cid _ m (m8PropKeep_set_4204 hkw_wb _) hm
                                          · rw [hwb_bd_eq, hoeq] at hm
                                            c0_hsteps_nogrp
                                            refine wp_join0 (fun ma => ∃ scra, M8PropKeep scr0 scra
                                                ∧ scra[4196]? = scri1[4196]? ∧
                                                (FullMem c (m8ScrSt s scra) ⋆ R) ma) ?_ ?_
                                            · intro _ ma ⟨scra, hka, hka4, hma⟩
                                              c0_hfast
                                              rw [hnxt_eq]
                                              exact hLi (2048 - (wsteps_w + 1#32).toNat)
                                                (t_w + 1#64, vis_w + 1#64, w_w, nxt,
                                                  wsteps_w + 1#32, ()) ma (by omega)
                                                ⟨scra, hka, hka4, by omega, rfl, hma⟩
                                            · intro Jao hJao
                                              c0_hsplit
                                              · c0_hsteps_nogrp
                                                m8k6_call hAssign
                                                try rw [hoeq]
                                                refine m8K6AssignSpec_intro rfl
                                                  (m8ScrSt_lengthsOk hlen0
                                                    (by rw [List.length_set, hkw_l, hscr0_l]))
                                                  hsc hm ?_
                                                intro scra ma hlena hkeepa hma
                                                rw [m8ScrSt_buf] at hkeepa
                                                rw [m8ScrSt_upd] at hma
                                                have hka4 : scra[4196]? = scri1[4196]? := by
                                                  have := hkeepa 4196 (by omega)
                                                    (by decide) (by decide)
                                                    (Or.inl (by decide)) (Or.inl (by decide))
                                                    (Or.inl (by decide))
                                                  exact this.trans h4wb
                                                exact hJao ma ⟨scra, m8PropKeep_of_assign hkw_wb
                                                  (by rw [hlena, List.length_set, hkw_l, hscr0_l])
                                                  (fun idx hi => hkeepa idx (by
                                                    rw [List.length_set, hkw_l, hscr0_l] at hi
                                                    exact hi)),
                                                  hka4, hma⟩
                                              · c0_hfast
                                                exact hJao m ⟨_, hkw_wb, h4wb, hm⟩
                                      · rintro Br Lr remr ⟨r, ⟨⟩⟩ mr hBr hLr
                                          ⟨hmr, hr2, hr_le, rfl⟩
                                        subst mr
                                        c0_hsplit
                                        · have hr_lt : r.toNat < sz.toNat := by
                                            rw [hcm_eq'] at hc
                                            change r.toNat < (cm &&& 65535).toNat at hc
                                            exact hc
                                          clear hc
                                          have hca_bd : 15744 + off.toNat + r.toNat <
                                              scrw.length := by omega
                                          let cand := scrw[15744 + off.toNat + r.toNat]'hca_bd
                                          have hos_lt32' :
                                              15744 + (off.toNat + sz.toNat) < 2 ^ 32 :=
                                            Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.le_trans
                                              (Nat.add_le_add_left hos_le 15744) hgew)
                                              hlt30w) (by decide)
                                          have hca_eq : (BitVec.setWidth 64 (15744 +
                                              scrw[(BitVec.setWidth 64
                                                (11648 + (w_w >>> (1 : Nat)))).toNat]'
                                                  hoff_c0_bd +
                                              r)).toNat = 15744 + off.toNat + r.toNat := by
                                            have hca_lt32 :
                                                15744 + off.toNat + r.toNat < 2 ^ 32 := by
                                              refine Nat.lt_trans (Nat.add_lt_add_left hr_lt _) ?_
                                              rw [Nat.add_assoc]; exact hos_lt32'
                                            rw [hoff_eq, BitVec.toNat_setWidth, BitVec.toNat_add,
                                              BitVec.toNat_add]
                                            change ((15744 + off.toNat) % 2 ^ 32 +
                                              r.toNat) % 2 ^ 32 % 2 ^ 64 = _
                                            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
                                                (Nat.le_add_right _ _) hca_lt32),
                                              Nat.mod_eq_of_lt hca_lt32,
                                              Nat.mod_eq_of_lt (Nat.lt_trans hca_lt32 (by decide))]
                                          have hca_c0_bd : (BitVec.setWidth 64 (15744 +
                                              scrw[(BitVec.setWidth 64
                                                (11648 + (w_w >>> (1 : Nat)))).toNat]'
                                                  hoff_c0_bd +
                                              r)).toNat < scrw.length := by
                                            rw [hca_eq]; exact hca_bd
                                          have hceq : scrw[(BitVec.setWidth 64 (15744 +
                                              scrw[(BitVec.setWidth 64
                                                (11648 + (w_w >>> (1 : Nat)))).toNat]'
                                                  hoff_c0_bd +
                                              r)).toNat]'hca_c0_bd = cand :=
                                            m8_k6_get_congr hca_eq _ hca_bd
                                          have hr1 : (r + 1#32).toNat = r.toNat + 1 :=
                                            m8_bv32_add1_toNat hr_lt (by omega)
                                          c0_hsteps_nogrp
                                          refine wp_join0 (fun mj => mw = mj) ?_ ?_
                                          · intro _ mj rfl
                                            c0_hfast
                                            exact hLr (sz.toNat - (r + 1#32).toNat)
                                              (r + 1#32, ()) mw (by omega)
                                              ⟨rfl, by omega, by omega, rfl⟩
                                          · intro Jr hJr
                                            c0_hsplit
                                            · have hca_lt : cand.toNat < 2 * nv.toNat := by
                                                have hc_idx : (15744 + (scrw[(11648 +
                                                    w_w.toNat / 2) % 4294967296]'(by
                                                      rw [← hcid_eq]; have := hcid_lt
                                                      omega)).toNat + r.toNat) % 4294967296 =
                                                    15744 + off.toNat + r.toNat := by
                                                  rw [hoff_eq']
                                                  have hlt32 :
                                                      15744 + off.toNat + r.toNat < 2 ^ 32 := by
                                                    refine Nat.lt_trans
                                                      (Nat.add_lt_add_left hr_lt _) ?_
                                                    rw [Nat.add_assoc]; exact hos_lt32'
                                                  rw [Nat.mod_eq_of_lt hlt32]
                                                have hc' :
                                                    cand.toNat < (2 * nv.toNat) % 4294967296 := by
                                                  have heq := m8_k6_get_congr hc_idx
                                                    (by rw [hc_idx]; exact hca_bd) hca_bd
                                                  dsimp only [cand]; rw [← heq]
                                                  simpa [nv] using hc
                                                rw [Nat.mod_eq_of_lt (by omega)] at hc'
                                                exact hc'
                                              have hcav_c0_bd : (BitVec.setWidth 64 (6528 +
                                                  scrw[(BitVec.setWidth 64 (15744 +
                                                    scrw[(BitVec.setWidth 64 (11648 +
                                                      (w_w >>> (1 : Nat)))).toNat]'
                                                        hoff_c0_bd +
                                                    r)).toNat]'hca_c0_bd)).toNat < scrw.length := by
                                                have hcav_lt32 : 6528 + cand.toNat < 2 ^ 32 :=
                                                  Nat.lt_trans (Nat.add_lt_add_left
                                                    (Nat.lt_of_lt_of_le hca_lt
                                                      (Nat.mul_le_mul_left 2 hnv_le)) 6528)
                                                    (by decide)
                                                rw [hceq, BitVec.toNat_setWidth, BitVec.toNat_add]
                                                change (6528 + cand.toNat) % 2 ^ 32 % 2 ^ 64 < _
                                                rw [Nat.mod_eq_of_lt hcav_lt32, Nat.mod_eq_of_lt
                                                  (Nat.lt_trans hcav_lt32 (by decide)), hkw_l]
                                                exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left
                                                  (Nat.lt_of_lt_of_le hca_lt
                                                    (Nat.mul_le_mul_left 2 hnv_le)) 6528)
                                                  (Nat.le_trans (by decide) hbase)
                                              c0_hsplit
                                              · c0_hfast
                                                rw [hceq]
                                                exact hBr (r, r, cand, ()) mw
                                                  ⟨rfl, Or.inr ⟨hr_lt, hca_lt⟩⟩
                                              · c0_hfast; exact hJr mw rfl
                                            · c0_hfast; exact hJr mw rfl
                                        · c0_hfast
                                          exact hBr (r, 0xFFFFFFFF#32, 0#32, ()) mw
                                            ⟨rfl, Or.inl rfl⟩
                                      · intro Br Lr _ hLr; c0_hfast
                                        exact hLr (sz.toNat - 2) (2#32, ()) mw
                                          ⟨rfl, by decide, hsz_ge, rfl⟩
                      · c0_hfast; exact hJwex mw ⟨scrw, hkw, hkw4, hmw⟩
                    · c0_hfast; exact hJwex mw ⟨scrw, hkw, hkw4, hmw⟩
                · intro Li hLi
                  have hw0_eq' : (scri.set 4196 (scri[4196]'(by omega) + 1))[
                      (BitVec.setWidth 64 (7040#32 + (scri[(BitVec.setWidth 64 (5504#32 +
                        scri[4196]'(by omega))).toNat]'hlit_ar_bd ^^^
                        1#32))).toNat]'hw0_c0_bd =
                      scri1[7040 + (lit ^^^ 1#32).toNat]'hw0_bd := by
                    refine m8_k6_get_congr ?_ _ hw0_bd
                    have hnl32 : 7040 + (lit ^^^ 1#32).toNat < 2 ^ 32 :=
                      Nat.lt_trans (Nat.add_lt_add_left
                        (Nat.lt_of_lt_of_le hnl_lt (Nat.mul_le_mul_left 2 hnv_le)) 7040)
                        (by decide)
                    rw [hlit_c0, BitVec.toNat_setWidth, BitVec.toNat_add]
                    change (7040 + (lit ^^^ 1#32).toNat) % 2 ^ 32 % 2 ^ 64 = _
                    rw [Nat.mod_eq_of_lt hnl32, Nat.mod_eq_of_lt (Nat.lt_trans hnl32 (by decide))]
                  c0_hfast
                  have harg := hLi 2048
                    (ticks, 0#64, 0xFFFFFFFF#32, scri1[7040 + (lit ^^^ 1#32).toNat]'hw0_bd,
                      0#32, ()) m ⟨scri1, hki1, rfl, Nat.zero_le _, by simp, hm⟩
                  rw [← hw0_eq'] at harg; exact harg
            · c0_hfast; exact hJex mi ⟨scri, hki, hmi⟩
          · c0_hfast; exact hJex mi ⟨scri, hki, hmi⟩
      · intro Lo hLo; c0_hfast
        exact hLo (256 - (scr0[4196]'(by omega)).toNat) (0#64, ()) m0
          ⟨scr0, m8PropKeep_refl hok0, by rw [m8_k6_get_eq (by omega)], hm0'⟩

end LeanQbe.T.Examples.Kissat.FullM8CoreParity
