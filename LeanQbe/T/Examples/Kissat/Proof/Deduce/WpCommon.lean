/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.CoreLemmas1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts2
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.ControlComb
public import Kraken.Mem
public import Kraken.Separation

/-!
# Shared Deduction, OTFS & Analysis Helpers (`Proof.Deduce.WpCommon`)

Pure `BitVec`/list/`FullAnaMarksCov`/`FullWitnessCutInv`/`ModeWatchesInv` preservation and
scoped `DeduceTactics` rules over `Proof.Spec` (`0` legacy `Full*` imports, `0` `import all`,
`0` `@[expose]` on theorems/lemmas/sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Deduce

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

/-! ## 1. Scoped `DeduceTactics` (`bv_c0` / `c0_load` / `c0_store`) -/

namespace DeduceTactics

open scoped FullArenaTactics

@[scoped bv_c0] theorem ded_bv32_lshr_1 (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 :=
  bv32_lshr_1 x

@[scoped bv_c0] theorem ded_bv32_mask_lo31_toNat (x : BitVec 32) :
    (x &&& 0x7FFFFFFF#32).toNat = x.toNat % 2 ^ 31 := by
  simpa [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl] using
    Nat.and_two_pow_sub_one_eq_mod x.toNat 31

@[scoped bv_c0] theorem ded_bv32_mask_glue19_toNat (x : BitVec 32) :
    (x &&& 0x7FFFF#32).toNat = x.toNat % 2 ^ 19 := by
  simpa [BitVec.toNat_and, show (0x7FFFF#32).toNat = 2 ^ 19 - 1 from rfl] using
    Nat.and_two_pow_sub_one_eq_mod x.toNat 19

@[scoped bv_c0] theorem ded_i8_sext32_zero : (0#8 : BitVec 8).signExtend 32 = 0#32 := rfl

@[scoped bv_c0] theorem ded_u8_zext32_zero : (0#8 : BitVec 8).setWidth 32 = 0#32 := rfl

@[scoped bv_c0] theorem ded_i8_sext32_eq0_prop (v : BitVec 8) :
    (v.signExtend 32 = 0#32) = (v = 0#8) := propext (by revert v; decide)

@[scoped bv_c0] theorem ded_u8_zext32_eq0_prop (v : BitVec 8) :
    (v.setWidth 32 = 0#32) = (v = 0#8) := propext (by revert v; decide)

@[scoped bv_c0] theorem ded_bv64_add_0 (x : BitVec 64) : x + 0#64 = x :=
  BitVec.add_zero x

@[scoped bv_c0] theorem ded_bv64_0_mul_4 : (0#64 : BitVec 64) * 4#64 = 0#64 := rfl

@[scoped bv_c0] theorem ded_bv64_1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl

@[scoped bv_c0] theorem ded_bv64_3_toNat : (3#64 : BitVec 64).toNat = 3 := rfl

@[scoped bv_c0] theorem ded_bv32_lshr_nat1 (x : BitVec 32) : (x >>> 1).toNat = x.toNat / 2 :=
  bv32_lshr_1 x

@[scoped c0_load] theorem c0_load_full_tmp0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) : loadVal m i32 c.pTmp = some (s.core.tmp[0]'hi) := by
  simpa using FullArenaTactics.load_full_tmp (i := 0) hi hm

@[scoped c0_store] theorem c0_store_full_tmp0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pTmp ∧
    (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
      (storeMem m i32 c.pTmp v) := by
  simpa using FullArenaTactics.store_full_tmp (i := 0) v hi hm

@[scoped c0_load] theorem c0_load_full_tmp1 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 1 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pTmp + 4#64) = some (s.core.tmp[1]'hi) := by
  simpa using FullArenaTactics.load_full_tmp (i := 1) hi hm

@[scoped c0_store] theorem c0_store_full_tmp1 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 1 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 4#64) ∧
    (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 1 v } } ⋆ R)
      (storeMem m i32 (c.pTmp + 4#64) v) := by
  simpa using FullArenaTactics.store_full_tmp (i := 1) v hi hm

@[scoped c0_store] theorem c0_store_full_tmp0_off {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 0#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 0#64) v) := by
  simpa using FullArenaTactics.store_full_tmp (i := 0) v hi hm

@[scoped c0_store] theorem c0_store_full_tmp0_mul {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 0#64 * 4#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 0#64 * 4#64) v) := by
  simpa [ded_bv64_0_mul_4] using FullArenaTactics.store_full_tmp (i := 0) v hi hm

end DeduceTactics

/-! ## 2. Pure `BitVec`, Mask, Index & `List` Helpers -/

private theorem mask27_bit : ∀ i : Fin 32, (0x07FFFFFF#32)[i.val] = decide (i.val < 27) :=
  by decide
private theorem mask19_bit : ∀ i : Fin 32, (0x00080000#32)[i.val] = decide (i.val = 19) :=
  by decide
private theorem maskN22_bit : ∀ i : Fin 32, (0xFFBFFFFF#32)[i.val] = decide (i.val ≠ 22) :=
  by decide
private theorem mask23_bit : ∀ i : Fin 32, (0x00800000#32)[i.val] = decide (i.val = 23) :=
  by decide
private theorem mask31_bit : ∀ i : Fin 32, (0x80000000#32)[i.val] = decide (i.val = 31) :=
  by decide
private theorem maskLo31_bit : ∀ i : Fin 32, (0x7FFFFFFF#32)[i.val] = decide (i.val < 31) :=
  by decide
private theorem maskNGlue_bit : ∀ i : Fin 32, (~~~0x0007FFFF#32)[i.val] = decide (19 ≤ i.val) :=
  by decide

theorem bv32_mask_usage_garb (hdr u : BitVec 32) :
    (((hdr &&& 0x07FFFFFF#32) ||| (u <<< 27)) &&& 0x00080000#32) =
      (hdr &&& 0x00080000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_shiftLeft,
    mask27_bit ⟨i, hi⟩, mask19_bit ⟨i, hi⟩]
  by_cases h19 : i = 19 <;> simp [h19]

theorem bv32_mask_usage_shrk (hdr u : BitVec 32) :
    (((hdr &&& 0x07FFFFFF#32) ||| (u <<< 27)) &&& 0x00800000#32) =
      (hdr &&& 0x00800000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_shiftLeft,
    mask27_bit ⟨i, hi⟩, mask23_bit ⟨i, hi⟩]
  by_cases h23 : i = 23 <;> simp [h23]

theorem bv32_or_shrk_garb (hdr : BitVec 32) :
    ((hdr ||| 0x00800000#32) &&& 0x00080000#32) = (hdr &&& 0x00080000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, mask19_bit ⟨i, hi⟩, mask23_bit ⟨i, hi⟩]
  by_cases h19 : i = 19 <;> simp [h19]

theorem bv32_or_shrk_shrk (hdr : BitVec 32) :
    ((hdr ||| 0x00800000#32) &&& 0x00800000#32) ≠ 0#32 := by
  intro h; have h23 := congrArg (·[23]) h
  revert h23; simp [show (0x00800000#32)[23] = true from rfl]

theorem bv32_or_garb_garb (hdr : BitVec 32) :
    ((hdr ||| 0x00080000#32) &&& 0x00080000#32) ≠ 0#32 := by
  intro h; have h19 := congrArg (·[19]) h
  revert h19; simp [show (0x00080000#32)[19] = true from rfl]

theorem bv32_clear_red_garb (hdr : BitVec 32) :
    ((hdr &&& 0xFFBFFFFF#32) &&& 0x00080000#32) = (hdr &&& 0x00080000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, maskN22_bit ⟨i, hi⟩, mask19_bit ⟨i, hi⟩]
  by_cases h19 : i = 19 <;> simp [h19]

theorem bv32_clear_red_shrk (hdr : BitVec 32) :
    ((hdr &&& 0xFFBFFFFF#32) &&& 0x00800000#32) = (hdr &&& 0x00800000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, maskN22_bit ⟨i, hi⟩, mask23_bit ⟨i, hi⟩]
  by_cases h23 : i = 23 <;> simp [h23]

private theorem bv32_bit_false_of_lt {ng : BitVec 32} (hng : ng.toNat < 2 ^ 19)
    (i : Nat) (hi19 : 19 ≤ i) (hi32 : i < 32) : ng[i] = false := by
  rw [BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hng (Nat.pow_le_pow_right (by decide) hi19))

theorem bv32_setGlue_garb (hdr ng : BitVec 32) (hng : ng.toNat < 2 ^ 19) :
    (((hdr &&& ~~~0x0007FFFF#32) ||| ng) &&& 0x00080000#32) = (hdr &&& 0x00080000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, maskNGlue_bit ⟨i, hi⟩, mask19_bit ⟨i, hi⟩]
  by_cases h19 : i = 19
  · subst h19; simp [bv32_bit_false_of_lt hng 19 (Nat.le_refl 19) (by omega)]
  · simp [h19]

theorem bv32_setGlue_shrk (hdr ng : BitVec 32) (hng : ng.toNat < 2 ^ 19) :
    (((hdr &&& ~~~0x0007FFFF#32) ||| ng) &&& 0x00800000#32) = (hdr &&& 0x00800000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, maskNGlue_bit ⟨i, hi⟩, mask23_bit ⟨i, hi⟩]
  by_cases h23 : i = 23
  · subst h23; simp [bv32_bit_false_of_lt hng 23 (by decide) (by omega)]
  · simp [h23]

theorem bv32_and_glue_lt (x : BitVec 32) : (x &&& 0x0007FFFF#32).toNat < 2 ^ 19 := by
  have h : (x &&& 0x0007FFFF#32).toNat ≤ (0x0007FFFF#32 : BitVec 32).toNat := by
    rw [BitVec.toNat_and]; exact Nat.and_le_right
  exact Nat.lt_of_le_of_lt h (by decide)

theorem bin_rsn_mask_props {l : BitVec 32} (hl : l.toNat < 2 ^ 31 - 1) :
    let rsn : BitVec 32 := (l &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    rsn ≠ 0xFFFFFFFF#32 ∧ (rsn &&& 0x80000000#32) ≠ 0#32 ∧
      (rsn &&& 0x7FFFFFFF#32).toNat = l.toNat := by
  intro rsn
  have hbit31 : l[31] = false := by
    rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (by omega : l.toNat < 2 ^ 31)]; rfl
  have hand_hi : (rsn &&& 0x80000000#32) = 0x80000000#32 := by
    ext i hi; simp only [rsn, BitVec.getElem_and, BitVec.getElem_or, mask31_bit ⟨i, hi⟩]
    by_cases h31 : i = 31 <;> simp [h31]
  have hand_lo : (rsn &&& 0x7FFFFFFF#32) = l := by
    ext i hi
    simp only [rsn, BitVec.getElem_and, BitVec.getElem_or, mask31_bit ⟨i, hi⟩,
      maskLo31_bit ⟨i, hi⟩]
    by_cases h31 : i = 31
    · subst h31; simp [hbit31]
    · simp [h31, show i < 31 by omega]
  refine ⟨?_, ?_, congrArg BitVec.toNat hand_lo⟩
  · intro heq; have hnat := congrArg (fun x => (x &&& 0x7FFFFFFF#32).toNat) heq
    rw [hand_lo] at hnat
    have hff : (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 := rfl
    rw [hff] at hnat; omega
  · rw [hand_hi]; decide

theorem bv32_lit_lo31_props {l : BitVec 32} (hl : l.toNat < 2 ^ 31) :
    (l &&& 0x7FFFFFFF#32) = l ∧ ((l &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 ∧
      (l &&& 0x80000000#32) = 0#32 := by
  have hb31 : l[31] = false := by
    rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt hl]; rfl
  have hlo : (l &&& 0x7FFFFFFF#32) = l := by
    ext i hi; simp only [BitVec.getElem_and, maskLo31_bit ⟨i, hi⟩]
    by_cases h31 : i = 31
    · subst h31; simp [hb31]
    · simp [show i < 31 by omega]
  have hhi : (l &&& 0x80000000#32) = 0#32 := by
    ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_zero, mask31_bit ⟨i, hi⟩]
    by_cases h31 : i = 31
    · subst h31; simp [hb31]
    · simp [h31]
  exact ⟨hlo, by rw [hlo]; exact hhi, hhi⟩

theorem bv64_confl_ref_u32 {r : BitVec 64} (hr : r.toNat < 2 ^ 31 - 1) :
    (r.setWidth 32).toNat = r.toNat ∧ r.setWidth 32 ≠ 0xFFFFFFFF#32 ∧
    (r.setWidth 32 &&& 0x80000000#32) = 0#32 := by
  have hto : (r.setWidth 32).toNat = r.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hto, fun heq => by
    have := congrArg BitVec.toNat heq; rw [hto] at this
    have : (0xFFFFFFFF#32).toNat = 2 ^ 32 - 1 := rfl; omega, ?_⟩
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_zero]
  by_cases h31 : i = 31
  · subst h31
    have hb : (r.setWidth 32)[31] = false := by
      rw [BitVec.getElem_eq_testBit_toNat, hto, Nat.testBit, Nat.shiftRight_eq_div_pow,
        Nat.div_eq_of_lt (by omega : r.toNat < 2 ^ 31)]; rfl
    simp [hb]
  · simp [mask31_bit ⟨i, hi⟩, h31]

theorem bv32_lit_neq_ff {l : BitVec 32} (hl : l.toNat < 2 ^ 31 - 1) :
    l ≠ 0xFFFFFFFF#32 := fun h => by
  have := congrArg BitVec.toNat h
  have : (0xFFFFFFFF#32).toNat = 2 ^ 32 - 1 := rfl; omega

theorem list_set_congr {α : Type} {xs : List α} {i j : Nat} {v w : α}
    (hij : i = j) (hvw : v = w) : xs.set i v = xs.set j w := by subst hij hvw; rfl

theorem bv64_trunc32_ofNat {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, bv64_ofNat_toNat (by omega), bv32_ofNat_toNat hn,
    Nat.mod_eq_of_lt hn]

theorem bv64_sub1_toNat {f : BitVec 64} (hf : f ≠ 0#64) :
    (f - 1#64).toNat = f.toNat - 1 := by
  have hpos : 0 < f.toNat := Nat.pos_of_ne_zero fun hz => hf (BitVec.eq_of_toNat_eq hz)
  have hlt := f.isLt
  rw [BitVec.toNat_sub]
  change (2 ^ 64 - 1 + f.toNat) % 2 ^ 64 = f.toNat - 1
  omega

theorem getElem_eq_of_idx {α : Type} {xs : List α} {i j : Nat}
    {hi : i < xs.length} {hj : j < xs.length} (h : i = j) :
    xs[i]'hi = xs[j]'hj := by subst h; rfl

theorem list_getElem_of_idx {α : Type} {xs : List α} {i j : Nat}
    {hi : i < xs.length} {hj : j < xs.length} (h : i = j) :
    xs[i]'hi = xs[j]'hj := by subst h; rfl

theorem fullMem_of_eq {c : FullCfg} {s1 s2 : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMem c s1 ⋆ R) m)
    (hk : s1.core = s2.core) (hsc : s1.scratch = s2.scratch) : (FullMem c s2 ⋆ R) m := by
  cases s1; cases s2; simp only at hk hsc; subst hk hsc; exact hm

theorem bv64_ite_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (if P then (1#64 : BitVec 64) else 0#64) = BitVec.ofNat 64 (if Q then 1 else 0) := by
  by_cases hp : P
  · have hq : Q := h.mp hp; simp [hp, hq]
  · have hnq : ¬Q := mt h.mpr hp; simp [hp, hnq]

theorem bv64_shl1_nat (x : BitVec 64) (h : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm, Nat.mod_eq_of_lt h]

theorem bv32_ofNat_add1 (n : Nat) : BitVec.ofNat 32 n + 1#32 = BitVec.ofNat 32 (n + 1) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.add_mod]

theorem bv32_lt_highbit_iff (w : BitVec 32) :
    w.toNat < 0x80000000 ↔ (w &&& 0x80000000#32) = 0#32 := by
  constructor
  · intro hlt
    ext i hi
    by_cases h31 : i = 31
    · subst h31
      have hw31 : w[31] = false := by
        rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit, Nat.shiftRight_eq_div_pow,
          Nat.div_eq_of_lt hlt]; rfl
      simp [hw31]
    · simp [mask31_bit ⟨i, hi⟩, h31]
  · intro hand
    have h31 := congrArg (·[31]) hand
    simp only [BitVec.getElem_and, show (0x80000000#32 : BitVec 32)[31] = true from rfl,
      BitVec.getElem_zero, Bool.and_true] at h31
    rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq] at h31
    have hwlt := w.isLt
    have hdiv0 : w.toNat / 2 ^ 31 = 0 := by
      rcases Nat.lt_or_ge (w.toNat / 2 ^ 31) 2 with h01 | hge
      · have hm : (w.toNat / 2 ^ 31) % 2 = w.toNat / 2 ^ 31 := Nat.mod_eq_of_lt h01
        revert h31; rw [hm]; intro h31
        exact Nat.eq_zero_of_le_zero (Nat.le_of_not_lt fun hpos => by
          have : w.toNat / 2 ^ 31 = 1 := by omega
          simp [this] at h31)
      · omega
    omega

theorem bv32_lshr31_nat_cases (w : BitVec 32) :
    ((w &&& 0x80000000#32) = 0#32 → (w >>> (31 : Nat)).toNat = 0) ∧
    ((w &&& 0x80000000#32) ≠ 0#32 → (w >>> (31 : Nat)).toNat = 1) ∧
    (w >>> (31 : Nat)).toNat ≤ 1 := by
  have hsh : (w >>> (31 : Nat)).toNat = w.toNat / 2 ^ 31 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hwlt := w.isLt
  have hiff := bv32_lt_highbit_iff w
  refine ⟨fun h0 => by rw [hsh]; exact Nat.div_eq_of_lt (hiff.mpr h0), fun h1 => ?_, by omega⟩
  have hge : 0x80000000 ≤ w.toNat := Nat.le_of_not_lt (fun hlt => h1 (hiff.mp hlt))
  rw [hsh]; omega

theorem nodup_map_getElem_inj {α β : Type} (f : α → β) :
    ∀ {xs : List α} {j1 j2 : Nat} (h1 : j1 < xs.length) (h2 : j2 < xs.length),
      (xs.map f).Nodup → f (xs[j1]'h1) = f (xs[j2]'h2) → j1 = j2
  | [], _, _, h1, _, _, _ => by simp at h1
  | _ :: _, 0, 0, _, _, _, _ => rfl
  | _ :: xs, 0, j2 + 1, _, h2, hnd, heq => by
    rw [List.map_cons, List.nodup_cons] at hnd
    exact absurd (List.mem_map.mpr ⟨xs[j2]'(by simpa using h2), List.getElem_mem .., heq.symm⟩)
      hnd.1
  | _ :: xs, j1 + 1, 0, h1, _, hnd, heq => by
    rw [List.map_cons, List.nodup_cons] at hnd
    exact absurd (List.mem_map.mpr ⟨xs[j1]'(by simpa using h1), List.getElem_mem .., heq⟩) hnd.1
  | _ :: xs, j1 + 1, j2 + 1, h1, h2, hnd, heq => by
    rw [List.map_cons, List.nodup_cons] at hnd
    exact congrArg Nat.succ (nodup_map_getElem_inj f (by simpa using h1) (by simpa using h2)
      hnd.2 heq)

private theorem list_count_set_eq {α : Type} [DecidableEq α] :
    ∀ (xs : List α) (i : Nat) (v a : α) (hi : i < xs.length),
      (xs.set i v).count a + (if xs[i]'hi = a then 1 else 0) =
        xs.count a + (if v = a then 1 else 0)
  | _ :: _, 0, _, _, _ => by simp [List.count_cons, beq_iff_eq]; split <;> split <;> omega
  | _ :: xs, i + 1, v, a, hi => by
    have ih := list_count_set_eq xs i v a (by simpa using hi)
    simp only [List.set_cons_succ, List.count_cons, List.getElem_cons_succ, beq_iff_eq]
    split <;> omega

private theorem list_swap_perm {α : Type} [DecidableEq α] (xs : List α) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    ((xs.set i (xs[j]'hj)).set j (xs[i]'hi)).Perm xs := by
  by_cases heq : i = j
  · subst heq; simp [List.set_getElem_self, List.Perm.refl]
  · have hj_lt : j < (xs.set i (xs[j]'hj)).length := by simp [hj]
    rw [List.perm_iff_count]; intro a
    have h2 := list_count_set_eq (xs.set i (xs[j]'hj)) j (xs[i]'hi) a hj_lt
    have h1 := list_count_set_eq xs i (xs[j]'hj) a hi
    have hget : (xs.set i (xs[j]'hj))[j]'hj_lt = xs[j]'hj := by
      rw [← Option.some_inj, ← List.getElem?_eq_getElem hj_lt,
        List.getElem?_set_ne heq, List.getElem?_eq_getElem hj]
    rw [hget] at h2; omega

private theorem filter_length_flip_one {α : Type} (p p' : α → Bool) (k : α) :
    ∀ (xs : List α), xs.Nodup → k ∈ xs → p k = false → p' k = true →
      (∀ x ∈ xs, x ≠ k → p' x = p x) → (xs.filter p').length = (xs.filter p).length + 1
  | [], _, hmem, _, _, _ => by simp at hmem
  | x :: xs, hnd, hmem, hpk, hp'k, hagree => by
    rw [List.nodup_cons] at hnd; rcases List.mem_cons.mp hmem with rfl | hmem'
    · have hfeq := List.filter_congr fun y hy =>
        hagree y (List.mem_cons_of_mem _ hy) (fun heq => hnd.1 (heq ▸ hy))
      simp [hpk, hp'k, hfeq]
    · have hx := hagree x List.mem_cons_self (fun heq => hnd.1 (heq ▸ hmem'))
      have ih := filter_length_flip_one p p' k xs hnd.2 hmem' hpk hp'k
        fun y hy => hagree y (List.mem_cons_of_mem _ hy)
      cases hp : p x <;> simp [hx, hp, ih] <;> omega

theorem filter_length_eq_zero_of_false {α : Type} {p : α → Bool} {xs : List α}
    (h : ∀ x ∈ xs, p x = false) : (xs.filter p).length = 0 := by
  have : xs.filter p = [] := List.filter_eq_nil_iff.mpr fun x hx => by simp [h x hx]
  simp [this]

theorem filter_step_of_lit {s_mrk mrk1 mrk2 : List (BitVec 8)} (P : Nat → Bool)
    {mv tc0 tc1 tc2 v : Nat}
    (hmp0 : ∀ w < mv, s_mrk[w]?.getD 0#8 ≠ 0#8 → mrk1[w]?.getD 0#8 = s_mrk[w]?.getD 0#8)
    (hmp1 : ∀ w < mv, mrk1[w]?.getD 0#8 ≠ 0#8 → mrk2[w]?.getD 0#8 = mrk1[w]?.getD 0#8)
    (hnew1 : ∀ w < mv, mrk1[w]?.getD 0#8 = 0#8 → mrk2[w]?.getD 0#8 ≠ 0#8 → v = w)
    (htc_ge : tc0 ≤ tc1) (hcnt1 : tc1 - tc0 = ((List.range mv).filter fun w =>
      decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk1[w]?.getD 0#8 ≠ 0#8) && P w).length)
    (htc2 : tc2 = tc1 + if v < mv ∧ mrk1[v]?.getD 0#8 = 0#8 ∧ mrk2[v]?.getD 0#8 ≠ 0#8 ∧
      P v = true then 1 else 0) : tc2 - tc0 = ((List.range mv).filter fun w =>
      decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk2[w]?.getD 0#8 ≠ 0#8) && P w).length := by
  have hne_iff : ∀ w < mv, w ≠ v → (mrk2[w]?.getD 0#8 ≠ 0#8 ↔ mrk1[w]?.getD 0#8 ≠ 0#8) :=
    fun w hw hne => ⟨fun h2 h1 => hne (hnew1 w hw h1 h2).symm, fun h1 => by rwa [hmp1 w hw h1]⟩
  split at htc2
  · rename_i hC; obtain ⟨hv, hm1, hm2, hcl⟩ := hC
    have hs0 : s_mrk[v]?.getD 0#8 = 0#8 :=
      Classical.byContradiction fun hnz => absurd hm1 (by rwa [hmp0 v hv hnz])
    have hflip := filter_length_flip_one
      (fun w => decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk1[w]?.getD 0#8 ≠ 0#8) && P w)
      (fun w => decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk2[w]?.getD 0#8 ≠ 0#8) && P w)
      v (List.range mv) List.nodup_range (List.mem_range.mpr hv) (by simp [hm1])
      (by simp [hs0, hm2, hcl]) (fun w hw hne => by simp [hne_iff w (List.mem_range.mp hw) hne])
    rw [hflip, ← hcnt1]; omega
  · rename_i hC; rw [Nat.add_zero] at htc2; subst htc2; rw [hcnt1]
    congr 1; apply List.filter_congr; intro w hw; have hwlt := List.mem_range.mp hw
    by_cases hwe : w = v
    · subst w; by_cases hm1 : mrk1[v]?.getD 0#8 = 0#8
      · by_cases hcl : P v = true
        · have hm2 : mrk2[v]?.getD 0#8 = 0#8 :=
            Classical.byContradiction fun hnz => hC ⟨hwlt, hm1, hnz, hcl⟩; simp [hm1, hm2]
        · simp [hcl]
      · rw [hmp1 v hwlt hm1]
    · simp [hne_iff w hwlt hwe]

theorem res_step_of_lit {s_mrk mrk1 mrk2 : List (BitVec 8)} {mv v : Nat}
    {r0 r1 r2 : BitVec 64}
    (hmp0 : ∀ w < mv, s_mrk[w]?.getD 0#8 ≠ 0#8 → mrk1[w]?.getD 0#8 = s_mrk[w]?.getD 0#8)
    (hmp1 : ∀ w < mv, mrk1[w]?.getD 0#8 ≠ 0#8 → mrk2[w]?.getD 0#8 = mrk1[w]?.getD 0#8)
    (hnew1 : ∀ w < mv, mrk1[w]?.getD 0#8 = 0#8 → mrk2[w]?.getD 0#8 ≠ 0#8 → v = w)
    (hr1 : r1 = r0 + BitVec.ofNat 64 ((List.range mv).filter fun w =>
      decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk1[w]?.getD 0#8 ≠ 0#8)).length)
    (hr2 : r2 = r1 + if v < mv ∧ mrk1[v]?.getD 0#8 = 0#8 ∧ mrk2[v]?.getD 0#8 ≠ 0#8
      then 1#64 else 0#64) : r2 = r0 + BitVec.ofNat 64 ((List.range mv).filter fun w =>
      decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk2[w]?.getD 0#8 ≠ 0#8)).length := by
  let c1 := ((List.range mv).filter fun w =>
    decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk1[w]?.getD 0#8 ≠ 0#8)).length
  have hf := filter_step_of_lit (fun _ => true) (tc0 := 0) (tc1 := c1)
    (tc2 := c1 + if v < mv ∧ mrk1[v]?.getD 0#8 = 0#8 ∧ mrk2[v]?.getD 0#8 ≠ 0#8 ∧
      (true : Bool) = true then 1 else 0) hmp0 hmp1 hnew1 (Nat.zero_le _) (by simp [c1]) rfl
  simp only [Nat.sub_zero, Bool.and_true, and_true] at hf
  rw [hr2, hr1, BitVec.add_assoc]; congr 1; dsimp only [c1] at hf; rw [← hf]
  split <;> simp [BitVec.ofNat_add]

/-! ## 3. `FullAnaMarksCov` Step Helpers -/

theorem anaMarksCov_step {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    (hcov : FullAnaMarksCov c s) {v : Nat} (hv : v < s.core.cur_vars)
    (hm0 : s.core.mrk[v]?.getD 0#8 = 0#8) :
    let v32 := BitVec.ofNat 32 v
    let s' : FullState :=
      { s with
        core := { s.core with mrk := s.core.mrk.set v 1#8, min_clr_len := s.core.min_clr_len + 1 }
        scratch := { s.scratch with work_stk1 := s.scratch.work_stk1.set s.core.min_clr_len v32 } }
    s.core.min_clr_len < s.core.cur_vars ∧ FullAnaMarksCov c s' := by
  intro v32 s'
  have ⟨hmcl_le, hnd, hall, hcov_m⟩ := hcov
  have hmax32 := fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have hws_len := hlen.scratch_ok.work_stk1_len; have hm_len := hlen.core_ok.mrk_len
  have hv32 : v32.toNat = v := bv32_ofNat_toNat (by omega)
  let xs := (s.scratch.work_stk1.take s.core.min_clr_len).map BitVec.toNat
  have hxs_len : xs.length = s.core.min_clr_len := by
    simp [xs, List.length_map, List.length_take]; omega
  have hxs_lt : ∀ x ∈ xs, x < s.core.cur_vars := fun x hx => by
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hx
    have hj_m : j < s.core.min_clr_len := by omega
    have hx_eq : x = (s.scratch.work_stk1[j]?.getD 0#32).toNat := by
      rw [← hget]; unfold xs; simp only [List.getElem_map, List.getElem_take]
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [hx_eq]; exact (hall j hj_m).1
  have hv_not_mem : v ∉ xs := fun hx => by
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hx
    have hj_m : j < s.core.min_clr_len := by omega
    have hx_eq : v = (s.scratch.work_stk1[j]?.getD 0#32).toNat := by
      rw [← hget]; unfold xs; simp only [List.getElem_map, List.getElem_take]
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact (hall j hj_m).2 (by rw [← hx_eq]; exact hm0)
  have hmcl_lt : s.core.min_clr_len < s.core.cur_vars := by
    rw [← hxs_len]; exact nodup_lt_of_missing hnd hxs_lt hv hv_not_mem
  have hmcl_ws : s.core.min_clr_len < s.scratch.work_stk1.length := by omega
  have htake_s' : ((s'.scratch.work_stk1.take (s.core.min_clr_len + 1)).map BitVec.toNat) =
      xs ++ [v] := by
    have h2 : s'.scratch.work_stk1.take (s.core.min_clr_len + 1) =
        s.scratch.work_stk1.take s.core.min_clr_len ++ [v32] := by
      apply List.ext_getElem
      · simp [s', List.length_take]; omega
      · intro j hj1 _
        have hj_le : j < s.core.min_clr_len + 1 := by simp [s', List.length_take] at hj1; omega
        by_cases hjm : j = s.core.min_clr_len
        · subst j
          rw [List.getElem_take, List.getElem_append_right (by simp [List.length_take]; omega),
            List.getElem_set_self (by simp [hmcl_ws])]
          simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hmcl_ws)]
        · have hj' : j < s.core.min_clr_len := by omega
          rw [List.getElem_take, List.getElem_append_left (by simp [List.length_take]; omega),
            List.getElem_take, List.getElem_set_ne (Ne.symm hjm)]
    rw [h2, List.map_append]; simp [xs, hv32]
  refine ⟨hmcl_lt, hmcl_lt, ?_, ?_, ?_⟩
  · rw [htake_s', List.nodup_append]
    exact ⟨hnd, by simp, fun a ha b hb => by
      simp only [List.mem_singleton] at hb; subst b; intro heq; subst heq; exact hv_not_mem ha⟩
  · intro k hk
    dsimp only [s'] at hk
    by_cases hkm : k = s.core.min_clr_len
    · subst k
      simp only [s', List.getElem?_set_self hmcl_ws, Option.getD_some, hv32, hv, true_and]
      rw [List.getElem?_set_self (by omega)]; decide
    · have hk' : k < s.core.min_clr_len := by omega
      have hget : (s'.scratch.work_stk1[k]?.getD 0#32).toNat =
          (s.scratch.work_stk1[k]?.getD 0#32).toNat := by
        dsimp only [s']; rw [List.getElem?_set_ne (Ne.symm hkm)]
      rw [hget]; refine ⟨(hall k hk').1, ?_⟩
      by_cases hwe : (s.scratch.work_stk1[k]?.getD 0#32).toNat = v
      · exact absurd hm0 (hwe ▸ (hall k hk').2)
      · dsimp only [s']; rw [List.getElem?_set_ne (Ne.symm hwe)]; exact (hall k hk').2
  · intro w hw hnz
    by_cases hwv : w = v
    · subst w; refine ⟨s.core.min_clr_len, Nat.lt_succ_self _, ?_⟩
      simp only [s', List.getElem?_set_self hmcl_ws, Option.getD_some, hv32]
    · have hnz0 : s.core.mrk[w]?.getD 0#8 ≠ 0#8 := by
        simpa [s', List.getElem?_set_ne (Ne.symm hwv)] using hnz
      obtain ⟨k, hk, hkeq⟩ := hcov_m w hw hnz0
      have hne_km : s.core.min_clr_len ≠ k := by omega
      refine ⟨k, by dsimp only [s']; omega, ?_⟩
      dsimp only [s']; rwa [List.getElem?_set_ne hne_km]

theorem anaMarksCov_step_lshr {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    (hcov : FullAnaMarksCov c s) (lit : BitVec 32) (hv : lit.toNat / 2 < s.core.cur_vars)
    (hm0 : s.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8) :
    let s' : FullState :=
      { s with
        core := { s.core with mrk := s.core.mrk.set (lit.toNat / 2) 1#8,
                              min_clr_len := s.core.min_clr_len + 1 }
        scratch := { s.scratch with
          work_stk1 := s.scratch.work_stk1.set s.core.min_clr_len (lit >>> 1) } }
    s.core.min_clr_len < s.core.cur_vars ∧ FullAnaMarksCov c s' := by
  have hmax32 := fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have hl_eq : BitVec.ofNat 32 (lit.toNat / 2) = lit >>> 1 := by
    apply BitVec.eq_of_toNat_eq; rw [bv32_lshr_1, bv32_ofNat_toNat (by omega)]
  simpa only [hl_eq] using anaMarksCov_step hlen hcov hv hm0

/-! ## 4. `FullWitnessCutInv`, Arena & Watch-Slice Preservation Helpers -/

theorem fcut_to_full {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k)
    (hcut : k.trail_end ≤ cut) : FullWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt,
    fun idx hidx => h.reason_inv_cut idx (by omega),
    fun idx hidx => h.reason_lit_mem_cut idx (by omega)⟩

theorem fcut_shrink_cut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut cut' : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k)
    (hle : cut' ≤ cut) : FullWitnessCutInv c F0 F_cur cut' k :=
  ⟨h.toFullOtfsWitnessInv, Nat.le_trans hle h.cut_le,
    fun idx hidx => h.reason_inv_cut idx (by omega),
    fun idx hidx => h.reason_lit_mem_cut idx (by omega)⟩

theorem fcut_reason_inv_act {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k)
    {idx : Nat} (hidx : idx < k.trail_end)
    (hc : idx < cut ∨ (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < k.cur_level) :
    let p := (k.trl[idx]?.getD 0#32).toNat
    let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
    rsn ≠ 0xFFFFFFFF#32 →
    if (rsn &&& 0x80000000#32) ≠ 0#32 then
      let ot := (rsn &&& 0x7FFFFFFF#32).toNat
      ot < 2 * k.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [p, ot]) ∧
      ∃ m < idx, (k.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
        (k.lvl[ot / 2]?.getD 0#32).toNat ≤ (k.lvl[p / 2]?.getD 0#32).toNat
    else
      rsn.toNat ∈ fullArenaClauseRefsCore k ∧ fullArenaClauseGarbCore k rsn.toNat = false ∧
      ∀ q ∈ fullArenaClauseLitsCore k rsn.toNat,
        q = p ∨ ∃ m < idx, (k.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
          (k.lvl[q / 2]?.getD 0#32).toNat ≤ (k.lvl[p / 2]?.getD 0#32).toNat :=
  hc.elim (fun h1 => h.reason_inv_cut idx h1) (fun h2 => h.reason_inv_below idx hidx h2)

theorem fcut_reason_lit_mem_act {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k)
    {idx : Nat} (hidx : idx < k.trail_end)
    (hc : idx < cut ∨ (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < k.cur_level) :
    let p := (k.trl[idx]?.getD 0#32).toNat
    let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
    rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
    p ∈ fullArenaClauseLitsCore k rsn.toNat :=
  hc.elim (fun h1 => h.reason_lit_mem_cut idx h1) (fun h2 => h.reason_lit_mem_below idx hidx h2)

theorem fcut_vals_zero_iff {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k) {l : Nat}
    (hl : l < 2 * k.cur_vars) :
    k.vals[l]?.getD 0#8 = 0#8 ↔ ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat / 2 ≠ l / 2 := by
  constructor
  · intro hz i hi hvar
    rcases (litVar_eq_iff _ l).mp hvar with h1 | h2
    · have ht := (h.vals_true_iff l hl).mpr ⟨i, hi, h1⟩; rw [hz] at ht; cases ht
    · have hf := (h.vals_false_iff l hl).mpr ⟨i, hi, h2⟩; rw [hz] at hf; cases hf
  · intro hnone
    rcases h.vals_domain l hl with h0 | h1 | h2
    · exact h0
    · obtain ⟨i, hi, heq⟩ := (h.vals_true_iff l hl).mp h1; exact absurd (by rw [heq]) (hnone i hi)
    · obtain ⟨i, hi, heq⟩ := (h.vals_false_iff l hl).mp h2
      exact absurd (by rw [heq, fullInv_var_xor1]) (hnone i hi)

theorem fcut_with_watches {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k)
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wu' : BitVec 64}
    (hw : ModeWatchesInv F_cur
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }) :
    FullWitnessCutInv c F0 F_cur cut
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } :=
  ⟨{ h.toFullOtfsWitnessInv with
      arena := { h.arena with len_ok := h.arena.len_ok }, watches := hw },
    h.cut_le, h.reason_inv_cut, h.reason_lit_mem_cut⟩

theorem fcut_with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k) (oom' : BitVec 64) :
    FullWitnessCutInv c F0 F_cur cut { k with oom := oom' } :=
  ⟨{ h.toFullOtfsWitnessInv with
      arena := { h.arena with len_ok := h.arena.len_ok }
      watches := h.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr },
    h.cut_le, h.reason_inv_cut, h.reason_lit_mem_cut⟩

theorem fcut_with_confl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k)
    (ct' c0' c1' cref' : BitVec 64) :
    FullWitnessCutInv c F0 F_cur cut
      { k with confl_type := ct', confl_lit0 := c0', confl_lit1 := c1', confl_ref := cref' } :=
  ⟨{ h.toFullOtfsWitnessInv with
      arena := { h.arena with len_ok := h.arena.len_ok }
      watches := h.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr },
    h.cut_le, h.reason_inv_cut, h.reason_lit_mem_cut⟩

theorem fcut_with_counts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k)
    (ni' nr' : BitVec 64) :
    FullWitnessCutInv c F0 F_cur cut { k with num_irred := ni', num_redundant := nr' } :=
  ⟨{ h.toFullOtfsWitnessInv with
      arena := { h.arena with len_ok := h.arena.len_ok }
      watches := h.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr },
    h.cut_le, h.reason_inv_cut, h.reason_lit_mem_cut⟩

theorem deduce_same_core_cut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : FullWitnessCutInv c F0 F_cur cut k)
    (mrk' : List (BitVec 8)) (tmp' : List (BitVec 32)) (tc' tl' mcl' : Nat) :
    FullWitnessCutInv c F0 F_cur cut
      { k with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl', min_clr_len := mcl' } :=
  ⟨{ hw.toFullOtfsWitnessInv with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr },
    hw.cut_le, hw.reason_inv_cut, hw.reason_lit_mem_cut⟩

theorem same_core_fullWitnessCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : FullWitnessCutInv c F0 F_cur cut k)
    {mrk' : List (BitVec 8)} {tmp' : List (BitVec 32)} {mcl' tc' tl' : Nat}
    (_hm : mrk'.length = c.max_vars) (_ht : tmp'.length = c.max_vars)
    (_hmcl : mcl' ≤ c.max_vars) (_htl : tl' ≤ k.cur_vars) :
    FullWitnessCutInv c F0 F_cur cut
      { k with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl', min_clr_len := mcl' } :=
  deduce_same_core_cut hw mrk' tmp' tc' tl' mcl'

theorem unsat_of_level0_bin_conflict {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : FullWitnessCutInv c F0 F_cur cut k) {l0 l1 : Nat}
    (h0lt : l0 < 2 * k.cur_vars) (h1lt : l1 < 2 * k.cur_vars)
    (hl0 : (k.lvl[l0 / 2]?.getD 0#32).toNat = 0)
    (hl1 : (k.lvl[l1 / 2]?.getD 0#32).toNat = 0)
    (hf0 : k.vals[l0]?.getD 0#8 = 0xFF#8) (hf1 : k.vals[l1]?.getD 0#8 = 0xFF#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [l0, l1])) : F0.Unsat := by
  refine hw.ext_sound.2
    (unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => Or.inr ?_))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l h0lt).mp hf0
    have hs := hw.level0_sound i hi (by rw [hieq, fullInv_var_xor1]; exact hl0)
    rwa [hieq] at hs
  · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l h1lt).mp hf1
    have hs := hw.level0_sound i hi (by rw [hieq, fullInv_var_xor1]; exact hl1)
    rwa [hieq] at hs

theorem unsat_of_level0_conflict {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : FullWitnessCutInv c F0 F_cur cut k)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefsCore k)
    (hg : fullArenaClauseGarbCore k cref = false)
    (hfals : ∀ l ∈ fullArenaClauseLitsCore k cref,
      k.vals[l]?.getD 0#8 = 0xFF#8 ∧ (k.lvl[l / 2]?.getD 0#32).toNat = 0) : F0.Unsat := by
  refine hw.ext_sound.2 (unsat_of_entails_nil
    (entails_of_mem_or_false (hw.arena.entails cref href hg) fun l hl => Or.inr ?_))
  obtain ⟨hf, hlv⟩ := hfals l hl
  obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l (hw.arena.lits_lt cref href hg l hl)).mp hf
  have hs := hw.level0_sound i hi (by rw [hieq, fullInv_var_xor1]; exact hlv)
  rwa [hieq] at hs

theorem otfs_nonactive_on_trail {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : FullWitnessCutInv c F0 F_cur cut k)
    (hlen : k.LengthsOk c) {cref uip : BitVec 32} {idx_u : Nat} (hiu_cut : idx_u < cut)
    (hiu_te : idx_u < k.trail_end) (ht_u : (k.trl[idx_u]?.getD 0#32).toNat = uip.toNat)
    (hr_u : k.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref)
    (hlev_u : (k.lvl[uip.toNat / 2]?.getD 0#32).toNat = k.cur_level)
    (href : cref.toNat ∈ fullArenaClauseRefsCore k) :
    ∀ idx < k.trail_end,
      (idx < min cut idx_u ∨
        (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < k.cur_level) →
      let rsn := k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cref.toNat := by
  have har_cap := c.harena; have hal_le := hlen.arena_len_le
  have hcref_lt : cref.toNat < 2 ^ 31 - 1 := by
    have := (hw.arena.refs_wf cref.toNat href).1; unfold dimacsBound at har_cap; omega
  have hcref_ne : cref ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff hcref_lt
  have hcref_lg : (cref &&& 0x80000000#32) = 0#32 :=
    (bv32_lit_lo31_props (by omega : cref.toNat < 2 ^ 31)).2.2
  have hmem_u : uip.toNat ∈ fullArenaClauseLitsCore k cref.toNat := by
    have hm := hw.reason_lit_mem_cut idx_u hiu_cut
    dsimp only at hm; rw [ht_u, hr_u] at hm; exact hm hcref_ne hcref_lg
  intro idx hidx hc rsn hne hlg heq
  have hri := fcut_reason_inv_act hw hidx (hc.elim (fun h1 => Or.inl (Nat.lt_of_lt_of_le h1
    (Nat.min_le_left _ _))) Or.inr) hne
  rw [ite_eq_right (fun h => absurd hlg h)] at hri
  obtain ⟨_, _, hl_inv⟩ := hri
  rw [heq] at hl_inv
  obtain h1 | ⟨m, hm, hmeq, _⟩ := hl_inv uip.toNat hmem_u
  · have hveq : (k.trl[idx]?.getD 0#32).toNat / 2 = (k.trl[idx_u]?.getD 0#32).toNat / 2 := by
      rw [← h1, ht_u]
    have hieq := hw.trail_vars_nodup idx idx_u hidx hiu_te hveq
    rcases hc with hlt | hlow
    · omega
    · rw [hieq, ht_u, hlev_u] at hlow; omega
  · have := hw.trail_vars_nodup m idx_u (by omega) hiu_te (by rw [hmeq, fullInv_var_xor1, ht_u])
    rcases hc with h1 | h2 <;> omega

theorem falsified_clause_nonactive {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : FullWitnessCutInv c F0 F_cur cut k) {cref : Nat}
    (hfals : ∀ l ∈ fullArenaClauseLitsCore k cref, k.vals[l]?.getD 0#8 = 0xFF#8) :
    ∀ idx < k.trail_end,
      (idx < cut ∨ (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < k.cur_level) →
      let rsn := k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cref := by
  intro idx hidx hc rsn hne hlg heq
  have hp_t := (hw.vals_true_iff _ (hw.trail_lits_lt idx hidx)).mpr ⟨idx, hidx, rfl⟩
  have hp_mem : (k.trl[idx]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore k cref := by
    rw [← heq]; exact fcut_reason_lit_mem_act hw hidx hc hne hlg
  have hp_f := hfals _ hp_mem; rw [hp_t] at hp_f; cases hp_f

theorem arenaUpdate_preserves_fullWitnessCut {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState}
    (hw : FullWitnessCutInv c F0 F_cur cut k)
    {arena' : List (BitVec 32)} {ag' ni' nr' : BitVec 64}
    (harena : FullArenaClausesInv c F_cur
      { k with arena := arena', arena_garbage := ag', num_irred := ni', num_redundant := nr' })
    (hrefs : fullArenaClauseRefsCore
      { k with arena := arena', arena_garbage := ag', num_irred := ni', num_redundant := nr' } =
      fullArenaClauseRefsCore k)
    (hact : ∀ idx < k.trail_end,
      (idx < cut ∨ (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < k.cur_level) →
      let rsn := k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
      fullArenaClauseGarbCore
        { k with arena := arena', arena_garbage := ag', num_irred := ni', num_redundant := nr' }
        rsn.toNat = false ∧
      List.Perm
        (fullArenaClauseLitsCore
          { k with arena := arena', arena_garbage := ag', num_irred := ni', num_redundant := nr' }
          rsn.toNat)
        (fullArenaClauseLitsCore k rsn.toNat)) :
    FullWitnessCutInv c F0 F_cur cut
      { k with arena := arena', arena_garbage := ag', num_irred := ni', num_redundant := nr' } := by
  let k' : FullCoreState :=
    { k with arena := arena', arena_garbage := ag', num_irred := ni', num_redundant := nr' }
  refine ⟨{ hw.toFullOtfsWitnessInv with
    arena := harena
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
    reason_inv_below := fun idx hidx hlt hne => by
      have hrs := hw.reason_inv_below idx hidx hlt hne
      by_cases hlg : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32
      · rw [ite_eq_right (fun h => h hlg)] at hrs ⊢
        have ha := hact idx hidx (Or.inr hlt) hne hlg
        exact ⟨hrefs ▸ hrs.1, ha.1, fun q hq => hrs.2.2 q (ha.2.mem_iff.mp hq)⟩
      · rw [ite_eq_left (fun h => absurd h hlg)] at hrs ⊢; exact hrs
    reason_lit_mem_below := fun idx hidx hlt hne hlg => by
      have ha := hact idx hidx (Or.inr hlt) hne hlg
      exact ha.2.symm.mem_iff.mp (hw.reason_lit_mem_below idx hidx hlt hne hlg) },
    hw.cut_le,
    fun idx hidx hne => by
      have hrs := hw.reason_inv_cut idx hidx hne
      by_cases hlg : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32
      · rw [ite_eq_right (fun h => h hlg)] at hrs ⊢
        have ha := hact idx (Nat.lt_of_lt_of_le hidx hw.cut_le) (Or.inl hidx) hne hlg
        exact ⟨hrefs ▸ hrs.1, ha.1, fun q hq => hrs.2.2 q (ha.2.mem_iff.mp hq)⟩
      · rw [ite_eq_left (fun h => absurd h hlg)] at hrs ⊢; exact hrs,
    fun idx hidx hne hlg => by
      have ha := hact idx (Nat.lt_of_lt_of_le hidx hw.cut_le) (Or.inl hidx) hne hlg
      exact ha.2.symm.mem_iff.mp (hw.reason_lit_mem_cut idx hidx hne hlg)⟩

theorem hdrBitsUpdate_preserves_fullWitnessCut {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessCutInv c F0 F_cur cut k)
    {cref : Nat} (hcref : cref ∈ fullArenaClauseRefsCore k)
    (f : BitVec 32 → BitVec 32) (ag' ni' nr' : BitVec 64)
    (hgarb : (f (fullArenaHdrCore k cref) &&& 0x00080000#32) =
      (fullArenaHdrCore k cref &&& 0x00080000#32))
    (hshrk : (f (fullArenaHdrCore k cref) &&& 0x00800000#32) =
      (fullArenaHdrCore k cref &&& 0x00800000#32)) :
    let hdr' := f (fullArenaHdrCore k cref)
    let k' : FullCoreState :=
      { k with arena := k.arena.set cref hdr', arena_garbage := ag',
               num_irred := ni', num_redundant := nr' }
    FullWitnessCutInv c F0 F_cur cut k' ∧
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    (∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) := by
  intro hdr' k'
  have hcref_wf := hw.arena.refs_wf cref hcref
  have hcref_lt : cref < k.arena.length := by
    have := hlen.arena_len_arr; have := hlen.arena_len_le; omega
  have har_self : k'.arena[cref]? = some hdr' := List.getElem?_set_self hcref_lt
  have har_ne : ∀ j, j ≠ cref → k'.arena[j]? = k.arena[j]? := fun j hj =>
    List.getElem?_set_ne (Ne.symm hj)
  have hnxt_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff k'.arena k.arena_len r = fullArenaNextOff k.arena k.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r; unfold fullArenaNextOff
      have hnot : ¬ (cref + 3 > k.arena_len) := by omega
      simp only [hnot, ↓reduceIte, har_self, Option.getD_some, har_ne (cref + 2) (by omega)]
      split
      · rfl
      · change (if (hdr' &&& 0x00800000#32) ≠ 0#32 then _ else _) =
          if (fullArenaHdrCore k cref &&& 0x00800000#32) ≠ 0#32 then _ else _
        rw [hshrk]; split
        · exact fullArenaSkipShrk_congr fun j hj1 _ => har_ne j (by omega)
        · rfl
    · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have := fullArenaScanRefs_disjoint hr hcref hlt
        have := (hw.arena.refs_wf r hr).2.1
        have := (hw.arena.refs_wf r hr).2.2.1
        exact fullArenaNextOff_congr_block (har_ne r hrc) (har_ne (r + 2) (by omega))
          fun j _ hk2 => har_ne j (by omega)
      · exact fullArenaNextOff_congr_block (har_ne r hrc) (har_ne (r + 2) (by omega))
          fun j hj1 _ => har_ne j (by omega)
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt_eq
  have hprops : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := by
    intro r hr; have hr_wf := hw.arena.refs_wf r hr
    have hnot_in : ∀ j, r + 2 ≤ j → j < r + 3 + fullArenaClauseSizeCore k r → j ≠ cref := by
      intro j hj1 hj2 heq; subst j; by_cases hrc : r = cref
      · omega
      · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
        · have := hw.arena.disjoint hr hcref hlt; omega
        · omega
    have hsz : fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := by
      unfold fullArenaClauseSizeCore
      rw [har_ne (r + 2) (hnot_in (r + 2) (Nat.le_refl _) (by omega))]
    have hgarb : fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore; by_cases hrc : r = cref
      · subst r; rw [har_self, Option.getD_some]
        change (hdr' &&& 0x00080000#32 != 0#32) = _; rw [hgarb]; rfl
      · rw [har_ne r hrc]
    have hlits : fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := by
      have hbd1 : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := by
        have := hlen.arena_len_arr; have := hlen.arena_len_le; omega
      exact fullArenaClauseLitsCore_eq_of_hold hbd1 (by simpa [k'] using hbd1) hsz
        fun j hj => har_ne (r + 3 + j) (hnot_in (r + 3 + j) (by omega) (by omega))
    exact ⟨hsz, hgarb, hlits⟩
  have harena' : FullArenaClausesInv c F_cur k' := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := hw.arena.refs_wf r hr
      change _ ∧ _ ∧ _ ∧ _ ∧ _; rw [hnxt_eq r hr, (hprops r hr).1]; exact hwf
    · intro r hr hsh; rw [hrefs] at hr
      have hsh0 : (fullArenaHdrCore k r &&& 0x00800000#32) ≠ 0#32 := by
        by_cases hrc : r = cref
        · subst r; unfold fullArenaHdrCore at hsh ⊢; rwa [har_self, Option.getD_some, hshrk] at hsh
        · unfold fullArenaHdrCore at hsh ⊢; rwa [har_ne r hrc] at hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
      have hr3 := (hw.arena.refs_wf r hr).1
      have hget_r : k.arena[r]? = some (fullArenaHdrCore k r) := by
        have : r < k.arena.length := by have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      have hsh_ar : (k.arena[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
        rw [hget_r, Option.getD_some]; exact hsh0
      obtain ⟨t0, ht0_lo, _, _, ht0_sent⟩ :=
        fullArenaNextOff_hits_sentinel hr3 hsh_ar ht1 ht2 hsent
      have ht0_ne : t0 ≠ cref := by
        by_cases hrc : r = cref
        · subst r; omega
        · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
          · have := fullArenaScanRefs_disjoint hr hcref hlt; omega
          · have := (hw.arena.refs_wf r hr).2.1; omega
      refine ⟨t0, by rw [(hprops r hr).1]; exact ht0_lo, by dsimp [k']; omega, ?_⟩
      dsimp only [k']; rw [List.getElem?_set_ne ht0_ne.symm]; exact ht0_sent
    · intro r hr hng; rw [hrefs] at hr; rw [(hprops r hr).2.1] at hng
      rw [(hprops r hr).2.2]; exact hw.arena.lits_lt r hr hng
    · intro r hr hng; rw [hrefs] at hr; rw [(hprops r hr).2.1] at hng
      rw [(hprops r hr).2.2]; exact hw.arena.entails r hr hng
  refine ⟨arenaUpdate_preserves_fullWitnessCut hw harena' hrefs fun idx hidx hc hne hlg => ?_,
    hrefs, hprops⟩
  have hrs := fcut_reason_inv_act hw hidx hc hne
  rw [ite_eq_right (fun h => absurd hlg h)] at hrs
  exact ⟨(hprops _ hrs.1).2.1.trans hrs.2.1, (hprops _ hrs.1).2.2 ▸ List.Perm.refl _⟩

theorem arenaBumpUsage_preserves_fullWitnessCut {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessCutInv c F0 F_cur cut k)
    {cref : Nat} (hcref : cref ∈ fullArenaClauseRefsCore k) (u : BitVec 32) :
    let hdr := fullArenaHdrCore k cref
    let k' : FullCoreState :=
      { k with arena := k.arena.set cref ((hdr &&& 0x07FFFFFF#32) ||| (u <<< 27)) }
    FullWitnessCutInv c F0 F_cur cut k' ∧
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    (∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) :=
  hdrBitsUpdate_preserves_fullWitnessCut hlen hw hcref
    (fun x => (x &&& 0x07FFFFFF#32) ||| (u <<< 27))
    k.arena_garbage k.num_irred k.num_redundant
    (bv32_mask_usage_garb _ u) (bv32_mask_usage_shrk _ u)

theorem clearRed_preserves_fullWitnessCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessCutInv c F0 F_cur cut k)
    {cref : Nat} (hcref : cref ∈ fullArenaClauseRefsCore k) (ni' nr' : BitVec 64) :
    let hdr := fullArenaHdrCore k cref
    let k' : FullCoreState :=
      { k with arena := k.arena.set cref (hdr &&& 0xFFBFFFFF#32)
               num_irred := ni', num_redundant := nr' }
    FullWitnessCutInv c F0 F_cur cut k' ∧
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    (∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) :=
  hdrBitsUpdate_preserves_fullWitnessCut hlen hw hcref (fun x => x &&& 0xFFBFFFFF#32)
    k.arena_garbage ni' nr' (bv32_clear_red_garb _) (bv32_clear_red_shrk _)

theorem arenaSetGlue_preserves_fullWitnessCut {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessCutInv c F0 F_cur cut k)
    {cref : Nat} (hcref : cref ∈ fullArenaClauseRefsCore k) (ng : BitVec 32)
    (hng : ng.toNat < 2 ^ 19) (ni' nr' : BitVec 64) :
    let hdr := fullArenaHdrCore k cref
    let k' : FullCoreState :=
      { k with arena := k.arena.set cref ((hdr &&& ~~~0x0007FFFF#32) ||| ng)
               num_irred := ni', num_redundant := nr' }
    FullWitnessCutInv c F0 F_cur cut k' ∧
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    (∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) :=
  hdrBitsUpdate_preserves_fullWitnessCut hlen hw hcref
    (fun x => (x &&& ~~~0x0007FFFF#32) ||| ng) k.arena_garbage ni' nr'
    (bv32_setGlue_garb _ ng hng) (bv32_setGlue_shrk _ ng hng)

theorem markGarb_preserves_fullWitnessCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessCutInv c F0 F_cur cut k) {cref : Nat}
    (hcref : cref ∈ fullArenaClauseRefsCore k) (ag' : BitVec 64)
    (hnonact : ∀ idx < k.trail_end,
      (idx < cut ∨ (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < k.cur_level) →
      let rsn := k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cref) :
    let k' : FullCoreState :=
      { k with arena := k.arena.set cref (fullArenaHdrCore k cref ||| 0x00080000#32)
               arena_garbage := ag' }
    FullWitnessCutInv c F0 F_cur cut k' ∧
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    (∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r ∧
      (r ≠ cref → fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r)) := by
  intro k'
  have hmg := hw.arena.markGarb hlen hcref ag'
  have hcref_lt : cref < k.arena.length := by
    have := (hw.arena.refs_wf cref hcref).1; have := hlen.arena_len_le
    have := hlen.arena_len_arr; omega
  have hprops : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r ∧
      (r ≠ cref → fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r) := by
    intro r hr
    have hrwf := hw.arena.refs_wf r hr
    have hne_r2 : r + 2 ≠ cref := by
      by_cases hrc : r = cref
      · subst r; omega
      · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
        · have := hw.arena.disjoint hr hcref hlt; omega
        · have := hw.arena.disjoint hcref hr hgt; omega
    have hsz : fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := by
      unfold fullArenaClauseSizeCore k'; rw [List.getElem?_set_ne hne_r2.symm]
    have hne_lits : ∀ j < fullArenaClauseSizeCore k r, r + 3 + j ≠ cref := by
      intro j hj
      by_cases hrc : r = cref
      · subst r; omega
      · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
        · have := hw.arena.disjoint hr hcref hlt; omega
        · have := hw.arena.disjoint hcref hr hgt; omega
    have hbd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := by
      have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
    have hlits : fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r :=
      fullArenaClauseLitsCore_eq_of_hold hbd (by simpa [k'] using hbd) hsz fun j hj =>
        List.getElem?_set_ne (hne_lits j hj).symm
    refine ⟨hsz, hlits, fun hne => ?_⟩
    unfold fullArenaClauseGarbCore fullArenaHdrCore k'
    rw [List.getElem?_set_ne hne.symm]
  refine ⟨arenaUpdate_preserves_fullWitnessCut hw hmg.2 hmg.1 fun idx hidx hc hne hlg => ?_,
    hmg.1, hprops⟩
  have hrs := fcut_reason_inv_act hw hidx hc hne
  rw [ite_eq_right (fun h => absurd hlg h)] at hrs
  have hne_c := hnonact idx hidx hc hne hlg
  have hp := hprops _ hrs.1
  exact ⟨(hp.2.2 hne_c).trans hrs.2.1, hp.2.1 ▸ List.Perm.refl _⟩

theorem fullArenaVarsNodup_markGarb {s : FullState} (hnd : FullArenaVarsNodup s)
    {cref : Nat} {s' : FullState}
    (hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core)
    (hgarb_c : fullArenaClauseGarbCore s'.core cref = true)
    (hother : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r) :
    FullArenaVarsNodup s' := by
  intro r hr hng
  change r ∈ fullArenaClauseRefsCore s'.core at hr
  rw [hrefs] at hr
  change fullArenaClauseGarbCore s'.core r = false at hng
  have hne : r ≠ cref := by rintro rfl; rw [hgarb_c] at hng; cases hng
  have ho := hother r hr hne
  rw [ho.1] at hng
  unfold fullArenaClauseLits
  rw [ho.2]
  exact hnd r hr hng

theorem fa_inPlaceShrink_preserves_fullWitnessCut {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut cut' : Nat} {k : FullCoreState}
    {arena' : List (BitVec 32)} {cref nsz : Nat}
    (hw : FullWitnessCutInv c F0 F_cur cut k) (hlen : k.LengthsOk c)
    (hcut : cut' ≤ cut) (hcref : cref ∈ fullArenaClauseRefsCore k)
    (hng : fullArenaClauseGarbCore k cref = false)
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < fullArenaClauseSizeCore k cref)
    (har_len' : arena'.length = c.arena_cap)
    (hhdr' : arena'[cref]? = some
      (if (fullArenaHdrCore k cref &&& 0x00800000#32) = 0#32 then
        fullArenaHdrCore k cref ||| 0x00800000#32
      else fullArenaHdrCore k cref))
    (hsz' : arena'[cref + 2]? = some (BitVec.ofNat 32 nsz))
    (hpad_old : ∀ j, nsz ≤ j → j < fullArenaClauseSizeCore k cref - 1 →
      arena'[cref + 3 + j]? = k.arena[cref + 3 + j]?)
    (hlast_sent : (fullArenaHdrCore k cref &&& 0x00800000#32) = 0#32 →
      arena'[cref + 3 + fullArenaClauseSizeCore k cref - 1]? = some 0xFFFFFFFF#32)
    (hlast_keep : (fullArenaHdrCore k cref &&& 0x00800000#32) ≠ 0#32 →
      arena'[cref + 3 + fullArenaClauseSizeCore k cref - 1]? =
        k.arena[cref + 3 + fullArenaClauseSizeCore k cref - 1]?)
    (hout : ∀ i, i < cref ∨ cref + 3 + fullArenaClauseSizeCore k cref ≤ i →
      arena'[i]? = k.arena[i]?)
    (hlits_lt' : ∀ l ∈ fullArenaClauseLitsCore { k with arena := arena' } cref,
      l < 2 * k.cur_vars)
    (hent' : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { k with arena := arena' } cref)))
    (hnonact : ∀ idx < k.trail_end,
      (idx < cut' ∨ (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < k.cur_level) →
      let rsn := k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cref) :
    let k' := { k with arena := arena' }
    FullWitnessCutInv c F0 F_cur cut' k' ∧ fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    fullArenaClauseSizeCore k' cref = nsz ∧ fullArenaClauseGarbCore k' cref = false ∧
    (∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) := by
  intro k'
  obtain ⟨hrefs, hother, hsz_c, hng_c, harena'⟩ :=
    inPlaceShrink_preserves_arena hw.arena hlen hcref hng hnsz3 hnsz_lt har_len' hhdr' hsz'
      hpad_old hlast_sent hlast_keep hout hlits_lt' hent'
  have hcw := arenaUpdate_preserves_fullWitnessCut (fcut_shrink_cut hw hcut) harena' hrefs
    fun idx hidx hc hne hlg => by
      have hrs := fcut_reason_inv_act (fcut_shrink_cut hw hcut) hidx hc hne
      rw [ite_eq_right (fun h => absurd hlg h)] at hrs
      have hne_c := hnonact idx hidx hc hne hlg
      have ho := hother _ hrs.1 hne_c
      exact ⟨ho.2.1.trans hrs.2.1, ho.2.2 ▸ List.Perm.refl _⟩
  exact ⟨hcw, hrefs, hsz_c, hng_c, hother⟩

theorem fa_swapCl_preserves_fullWitnessCut {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessCutInv c F0 F_cur cut k) {cref i j : Nat}
    (hcref : cref ∈ fullArenaClauseRefsCore k)
    (hi : i < fullArenaClauseSizeCore k cref) (hj : j < fullArenaClauseSizeCore k cref) :
    let lits := k.arena
    let li := lits[cref + 3 + i]?.getD 0#32
    let lj := lits[cref + 3 + j]?.getD 0#32
    let arena' := (lits.set (cref + 3 + i) lj).set (cref + 3 + j) li
    let k' := { k with arena := arena' }
    FullWitnessCutInv c F0 F_cur cut k' ∧ fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    fullArenaClauseSizeCore k' cref = fullArenaClauseSizeCore k cref ∧
    fullArenaClauseGarbCore k' cref = fullArenaClauseGarbCore k cref ∧
    (fullArenaClauseLitsCore k' cref).Perm (fullArenaClauseLitsCore k cref) ∧
    (∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) := by
  intro lits li lj arena' k'
  have ha := hw.arena
  have hwf := ha.refs_wf cref hcref
  have hk_ar_len : k.arena.length = c.arena_cap := hlen.arena_len_arr
  have hlen_ar : lits.length = c.arena_cap := hlen.arena_len_arr
  have hle_ar : k.arena_len ≤ c.arena_cap := hlen.arena_len_le
  have hbd : cref + 3 + fullArenaClauseSizeCore k cref ≤ lits.length := by omega
  have har'_len : arena'.length = c.arena_cap := by simp [arena', lits, hlen_ar]
  have hout : ∀ idx, idx < cref + 3 ∨ cref + 3 + fullArenaClauseSizeCore k cref ≤ idx →
      arena'[idx]? = lits[idx]? := fun idx hidx => by
    dsimp [arena']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff arena' k.arena_len r = fullArenaNextOff lits k.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r
      exact fullArenaNextOff_congr_block (hout _ (Or.inl (by omega)))
        (hout _ (Or.inl (by omega))) (fun q hq1 _ => hout q (Or.inr hq1))
    · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have := ha.disjoint hr hcref hlt
        have := fullArenaScanRefs_disjoint hr hcref hlt
        have := (ha.refs_wf r hr).2.1
        exact fullArenaNextOff_congr_block (hout _ (Or.inl (by omega)))
          (hout _ (Or.inl (by omega))) fun q _ hq2 => by
            dsimp only [lits] at hq2; exact hout q (Or.inl (by omega))
      · have hgt_d := ha.disjoint hcref hr hgt
        exact fullArenaNextOff_congr_block (hout _ (Or.inr hgt_d))
          (hout _ (Or.inr (by omega))) fun q _ _ => hout q (Or.inr (by omega))
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hsz_c : fullArenaClauseSizeCore k' cref = fullArenaClauseSizeCore k cref := by
    unfold fullArenaClauseSizeCore k'; rw [hout (cref + 2) (Or.inl (by omega))]
  have hng_c : fullArenaClauseGarbCore k' cref = fullArenaClauseGarbCore k cref := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore k'; rw [hout cref (Or.inl (by omega))]
  have hperm : (fullArenaClauseLitsCore k' cref).Perm (fullArenaClauseLitsCore k cref) := by
    let xs := (lits.drop (cref + 3)).take (fullArenaClauseSizeCore k cref)
    have hxs_len : xs.length = fullArenaClauseSizeCore k cref := by
      simp [xs, List.length_take, List.length_drop]; omega
    have hli : li = xs[i]'(by omega) := by
      dsimp only [li]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      simp [xs, List.getElem_take, List.getElem_drop]
    have hlj : lj = xs[j]'(by omega) := by
      dsimp only [lj]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      simp [xs, List.getElem_take, List.getElem_drop]
    have hswap : (arena'.drop (cref + 3)).take (fullArenaClauseSizeCore k cref) =
        (xs.set i lj).set j li := by
      apply List.ext_getElem
      · simp [xs, arena', List.length_take, List.length_drop]
      · intro p hp1 hp2
        have hplt : p < fullArenaClauseSizeCore k cref := by
          simp [List.length_take, List.length_drop] at hp1; omega
        rw [List.getElem_take, List.getElem_drop]
        have hopt : arena'[cref + 3 + p]? = some (((xs.set i lj).set j li)[p]'hp2) := by
          dsimp only [arena']
          by_cases hpj : p = j
          · subst p; rw [List.getElem?_set_self (by simp [List.length_set, hlen_ar]; omega),
              List.getElem_set_self (by simp [List.length_set, hxs_len]; omega), hli]
          · rw [List.getElem?_set_ne (by omega), List.getElem_set_ne (Ne.symm hpj)]
            by_cases hpi : p = i
            · subst p; rw [List.getElem?_set_self (by rw [hlen_ar]; omega),
                List.getElem_set_self (by rw [List.length_set, hxs_len]; exact hi), hlj]
            · rw [List.getElem?_set_ne (by omega), List.getElem_set_ne (Ne.symm hpi),
                List.getElem?_eq_getElem (by omega)]
              simp [xs, List.getElem_take, List.getElem_drop]
        have hopt0 := List.getElem?_eq_getElem (show cref + 3 + p < arena'.length by
          rw [har'_len]; omega)
        rw [hopt0] at hopt; exact Option.some.inj hopt
    unfold fullArenaClauseLitsCore k'; rw [hsz_c, hswap]
    have hsw : ((xs.set i lj).set j li).Perm xs := by
      simpa only [hli, hlj] using list_swap_perm xs (hxs_len ▸ hi) (hxs_len ▸ hj)
    exact hsw.map BitVec.toNat
  have hother : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := by
    intro r hr hne
    have hdisj : r + 3 + fullArenaClauseSizeCore k r ≤ cref ∨
        cref + 3 + fullArenaClauseSizeCore k cref ≤ r := by
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl (ha.disjoint hr hcref hlt)
      · exact Or.inr (ha.disjoint hcref hr hgt)
    have hrwf := ha.refs_wf r hr
    have hszr : fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := by
      unfold fullArenaClauseSizeCore k'
      rcases hdisj with h1 | h2
      · rw [hout (r + 2) (Or.inl (by omega))]
      · rw [hout (r + 2) (Or.inr (by omega))]
    have hgar : fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore k'
      rcases hdisj with h1 | h2
      · rw [hout r (Or.inl (by omega))]
      · rw [hout r (Or.inr h2)]
    refine ⟨hszr, hgar, fullArenaClauseLitsCore_eq_of_hold (by omega)
      (by dsimp [k']; rw [har'_len]; omega) hszr fun q hq => ?_⟩
    rcases hdisj with h1 | h2
    · exact hout (r + 3 + q) (Or.inl (by omega))
    · exact hout (r + 3 + q) (Or.inr (by omega))
  have harena' : FullArenaClausesInv c F_cur k' := by
    refine ⟨ha.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; dsimp [k']; rw [hnxt r hr]
      by_cases hrc : r = cref
      · subst r; rw [hsz_c]; exact ha.refs_wf cref hr
      · rw [(hother r hr hrc).1]; exact ha.refs_wf r hr
    · intro r hr hsh; rw [hrefs] at hr
      have hr_out : r < cref + 3 ∨ cref + 3 + fullArenaClauseSizeCore k cref ≤ r := by
        by_cases hrc : r = cref
        · subst r; exact Or.inl (by omega)
        · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
          · have := ha.disjoint hr hcref hlt; exact Or.inl (by omega)
          · exact Or.inr (ha.disjoint hcref hr hgt)
      have hsh0 : (fullArenaHdrCore k r &&& 0x00800000#32) ≠ 0#32 := by
        unfold fullArenaHdrCore at hsh ⊢; dsimp only [k'] at hsh; rwa [hout r hr_out] at hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term r hr hsh0
      have hr3 := (ha.refs_wf r hr).1
      have hget_r : k.arena[r]? = some (fullArenaHdrCore k r) := by
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hsh_ar : (k.arena[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
        rw [hget_r, Option.getD_some]; exact hsh0
      obtain ⟨t0, ht0_lo, _, _, ht0_sent⟩ := fullArenaNextOff_hits_sentinel hr3 hsh_ar ht1 ht2 hsent
      have ht0_out : t0 < cref + 3 ∨ cref + 3 + fullArenaClauseSizeCore k cref ≤ t0 := by
        by_cases hrc : r = cref
        · subst r; exact Or.inr ht0_lo
        · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
          · have := fullArenaScanRefs_disjoint hr hcref hlt; exact Or.inl (by omega)
          · have := ha.disjoint hcref hr hgt; exact Or.inr (by omega)
      refine ⟨t0, ?_, by dsimp [k']; omega, ?_⟩
      · by_cases hrc : r = cref
        · subst r; rwa [hsz_c]
        · rw [(hother r hr hrc).1]; exact ht0_lo
      · dsimp only [k']; rw [hout t0 ht0_out]; exact ht0_sent
    · intro r hr hng; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; rw [hng_c] at hng
        exact fun l hl => ha.lits_lt cref hr hng l (hperm.mem_iff.mp hl)
      · rw [(hother r hr hrc).2.1] at hng; rw [(hother r hr hrc).2.2]
        exact ha.lits_lt r hr hng
    · intro r hr hng; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; rw [hng_c] at hng
        exact entails_of_mem_or_false (ha.entails cref hr hng)
          fun l hl => Or.inl (hperm.symm.mem_iff.mp hl)
      · rw [(hother r hr hrc).2.1] at hng; rw [(hother r hr hrc).2.2]
        exact ha.entails r hr hng
  refine ⟨arenaUpdate_preserves_fullWitnessCut hw harena' hrefs fun idx hidx hc hne hlg => ?_,
    hrefs, hsz_c, hng_c, hperm, hother⟩
  have hrs := fcut_reason_inv_act hw hidx hc hne
  rw [ite_eq_right (fun h => absurd hlg h)] at hrs
  by_cases hrc : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat = cref
  · rw [hrc] at hrs ⊢; exact ⟨hng_c.trans hrs.2.1, hperm⟩
  · have ho := hother _ hrs.1 hrc; exact ⟨ho.2.1.trans hrs.2.1, ho.2.2 ▸ List.Perm.refl _⟩

/-! ## 5. Watch-Slice & `ModeWatchesInv` Preservation Helpers -/

private theorem modeWatches_eq {F : List (List Nat)} {k : FullCoreState} (h : k.dense_mode = 0#64) :
    ModeWatchesInv F k = WatchesInv F k := by
  unfold ModeWatchesInv; simp [h]

theorem fa_modeWatches_set_in_slice {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p : Nat} {b' : BitVec 32} (hdm : k.dense_mode = 0#64) (hw : ModeWatchesInv F_cur k)
    (hlit : lit < 2 * k.cur_vars) (hp_len : p < k.wstk.length)
    (hlo : fullWatchOffCore k lit ≤ p)
    (hhi : p < fullWatchOffCore k lit + fullWatchSizeCore k lit)
    (hne' : b' ≠ 0xFFFFFFFF#32)
    (hslice' : WatchSliceOk F_cur { k with wstk := k.wstk.set p b' } lit
      (fullWatchOffCore k lit) (fullWatchSizeCore k lit)) :
    ModeWatchesInv F_cur { k with wstk := k.wstk.set p b' } := by
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  rw [modeWatches_eq hdm] at hw
  let k' : FullCoreState := { k with wstk := k.wstk.set p b' }
  change ModeWatchesInv F_cur k'
  rw [modeWatches_eq (k := k') hdm]
  refine ⟨⟨hw.layout.bounds, hw.layout.pos_off, hw.layout.disjoint, fun l hl idx hidx => ?_⟩,
    fun l hl => ?_⟩
  · change (k.wstk.set p b')[fullWatchOffCore k l + idx]? ≠ some 0xFFFFFFFF#32
    by_cases hp : fullWatchOffCore k l + idx = p
    · rw [hp, List.getElem?_set_self hp_len]; exact fun he => hne' (Option.some.inj he)
    · rw [List.getElem?_set_ne (Ne.symm hp)]; exact hw.layout.no_sentinel l hl idx hidx
  · change WatchSliceOk F_cur k' l (fullWatchOffCore k l) (fullWatchSizeCore k l)
    by_cases hll : l = lit
    · subst hll; exact hslice'
    · have hdisj_all := hw.layout.disjoint l lit hl hlit hll
      refine (hw.slices l hl).mono (k' := k') hrefl (Nat.le_refl k.cur_vars) (fun _ r => r)
        fun idx hi1 hi2 => ?_
      have hdisj := hdisj_all (by omega) (by omega)
      change (k.wstk.set p b')[idx]? = k.wstk[idx]?
      rw [List.getElem?_set_ne (by rcases hdisj with h1 | h2 <;> omega)]

theorem fa_watchPush_bin_preserves {F_cur : List (List Nat)} {k : FullCoreState}
    {lit : Nat} {w0 : BitVec 32}
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wu' oom' nb' : BitVec 64}
    (hdm : k.dense_mode = 0#64) (hw : ModeWatchesInv F_cur k)
    (hlit : lit < 2 * k.cur_vars)
    (hlay : WatchStackLayout
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', oom := oom',
               num_binary := nb' })
    (hother : ∀ l < 2 * k.cur_vars, l ≠ lit →
      fullWatchSizeCore { k with wvec := wvec' } l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        wstk'[fullWatchOffCore { k with wvec := wvec' } l + idx]? =
          k.wstk[fullWatchOffCore k l + idx]?)
    (hsz : fullWatchSizeCore { k with wvec := wvec' } lit = fullWatchSizeCore k lit + 1)
    (hsame : ∀ idx < fullWatchSizeCore k lit,
      wstk'[fullWatchOffCore { k with wvec := wvec' } lit + idx]? =
        k.wstk[fullWatchOffCore k lit + idx]?)
    (hw0 : wstk'[fullWatchOffCore { k with wvec := wvec' } lit + fullWatchSizeCore k lit]? =
      some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    ModeWatchesInv F_cur
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', oom := oom',
               num_binary := nb' } := by
  let k' : FullCoreState := { k with wvec := wvec', wstk := wstk', wlen := wlen',
                                     wusable := wu', oom := oom', num_binary := nb' }
  rw [modeWatches_eq hdm] at hw
  change ModeWatchesInv F_cur k'; rw [modeWatches_eq (k := k') hdm]
  refine ⟨hlay, fun l hl => ?_⟩
  by_cases hll : l = lit
  · subst hll; change WatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l)
    rw [show fullWatchSizeCore k' l = fullWatchSizeCore k l + 1 from hsz]
    refine fullWatchSlice_append_bin (k := k) (k' := k') (Nat.le_refl k.cur_vars) (fun _ r => r)
      (fun idx hi => by simpa only [k', fullWatchOffCore] using hsame idx hi)
      (hw.slices l hl) ?_ hflag hne hlt hent
    simpa only [k', fullWatchOffCore] using hw0
  · obtain ⟨hszl, hsl⟩ := hother l hl hll
    have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
      rw [CNF.entails_def]; exact fun _ h => h
    change WatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l)
    rw [show fullWatchSizeCore k' l = fullWatchSizeCore k l from hszl]
    exact fullWatchSlice_relocate (k := k) (k' := k') hrefl (Nat.le_refl k.cur_vars) (fun _ r => r)
      (fun idx hi => by simpa only [k', fullWatchOffCore] using hsl idx hi) (hw.slices l hl)

theorem fa_watchPush_large_preserves {F_cur : List (List Nat)} {k : FullCoreState}
    {lit : Nat} {w0 cref : BitVec 32}
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wu' oom' : BitVec 64}
    (hdm : k.dense_mode = 0#64) (hw : ModeWatchesInv F_cur k)
    (hlit : lit < 2 * k.cur_vars)
    (hlay : WatchStackLayout
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', oom := oom' })
    (hother : ∀ l < 2 * k.cur_vars, l ≠ lit →
      fullWatchSizeCore { k with wvec := wvec' } l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        wstk'[fullWatchOffCore { k with wvec := wvec' } l + idx]? =
          k.wstk[fullWatchOffCore k l + idx]?)
    (hsz : fullWatchSizeCore { k with wvec := wvec' } lit = fullWatchSizeCore k lit + 2)
    (hsame : ∀ idx < fullWatchSizeCore k lit,
      wstk'[fullWatchOffCore { k with wvec := wvec' } lit + idx]? =
        k.wstk[fullWatchOffCore k lit + idx]?)
    (hw0 : wstk'[fullWatchOffCore { k with wvec := wvec' } lit + fullWatchSizeCore k lit]? =
      some w0)
    (hw1 : wstk'[fullWatchOffCore { k with wvec := wvec' } lit + fullWatchSizeCore k lit + 1]? =
      some cref)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hlt : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ fullArenaClauseRefsCore k) :
    ModeWatchesInv F_cur
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', oom := oom' } := by
  let k' : FullCoreState := { k with wvec := wvec', wstk := wstk', wlen := wlen',
                                     wusable := wu', oom := oom' }
  rw [modeWatches_eq hdm] at hw
  change ModeWatchesInv F_cur k'; rw [modeWatches_eq (k := k') hdm]
  refine ⟨hlay, fun l hl => ?_⟩
  by_cases hll : l = lit
  · subst hll; change WatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l)
    rw [show fullWatchSizeCore k' l = fullWatchSizeCore k l + 2 from hsz]
    refine fullWatchSlice_append_large (k := k) (k' := k') (Nat.le_refl k.cur_vars) (fun _ r => r)
      (fun idx hi => by simpa only [k', fullWatchOffCore] using hsame idx hi)
      (hw.slices l hl) ?_ ?_ hflag hlt href
    · simpa only [k', fullWatchOffCore] using hw0
    · simpa only [k', fullWatchOffCore] using hw1
  · obtain ⟨hszl, hsl⟩ := hother l hl hll
    have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
      rw [CNF.entails_def]; exact fun _ h => h
    change WatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l)
    rw [show fullWatchSizeCore k' l = fullWatchSizeCore k l from hszl]
    exact fullWatchSlice_relocate (k := k) (k' := k') hrefl (Nat.le_refl k.cur_vars) (fun _ r => r)
      (fun idx hi => by simpa only [k', fullWatchOffCore] using hsl idx hi) (hw.slices l hl)

theorem fa_watchPush_fail_preserves {F_cur : List (List Nat)} {k : FullCoreState}
    (hdm : k.dense_mode = 0#64) (hw : ModeWatchesInv F_cur k)
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wu' oom' : BitVec 64}
    (hlay : WatchStackLayout
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', oom := oom' })
    (hsame : ∀ l < 2 * k.cur_vars,
      fullWatchSizeCore { k with wvec := wvec' } l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        wstk'[fullWatchOffCore { k with wvec := wvec' } l + idx]? =
          k.wstk[fullWatchOffCore k l + idx]?) :
    ModeWatchesInv F_cur
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', oom := oom' } := by
  let k' : FullCoreState := { k with wvec := wvec', wstk := wstk', wlen := wlen',
                                     wusable := wu', oom := oom' }
  rw [modeWatches_eq hdm] at hw
  change ModeWatchesInv F_cur k'; rw [modeWatches_eq (k := k') hdm]
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  refine ⟨hlay, fun l hl => ?_⟩
  obtain ⟨hszl, hsl⟩ := hsame l hl
  change WatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l)
  rw [show fullWatchSizeCore k' l = fullWatchSizeCore k l from hszl]
  exact fullWatchSlice_relocate (k := k) (k' := k') hrefl (Nat.le_refl k.cur_vars) (fun _ r => r)
    (fun idx hi => by simpa only [k', fullWatchOffCore] using hsl idx hi) (hw.slices l hl)

end LeanQbe.T.Examples.Kissat.Proof.Deduce
