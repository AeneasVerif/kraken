module

public import LeanQbe.T.LeanLCNF.LcnfC0RtSpec
public import LeanQbe.T.Logic.C0Step
import all Kraken.Separation

/-!
# Soundness Proofs for `LcnfC0Rt` (Milestone R0: M0a + M0b)

Proves `Func.wp` contracts against `rtC0Env` for all 5 C0 runtime functions in `LcnfC0Rt.lean`:
- `lcnf_alloc` (`lcnfAllocSpec`)
- `lcnf_free_obj` (`lcnfFreeObjSpec`)
- `lcnf_dec_ref_cold` (`lcnfDecRefColdSpec`)
- `lcnf_mark_persistent` (`lcnfMarkPersistentSpec`)
- `lcnf_clo_under` (`lcnfCloUnderSpec`)

Closes `rtR0Mod_ok : ModuleOk rtC0Env rtR0Mod` across all 5 runtime functions, plus concrete
`Mem 64` non-vacuity DAG theorems (`nv_dec_ref_cold_dag`, `nv_mark_persistent_dag`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T
open LeanQbe.T.C0Step
open Std.ExtHashMap

/-! ## 1. `c0_load` / `c0_store` and BitVec Helpers -/

private theorem ptr_add_nat_p (a : BitVec 64) (m n : Nat) :
    a + BitVec.ofNat 64 m + BitVec.ofNat 64 n = a + BitVec.ofNat 64 (m + n) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

@[local c0_load] theorem c0_load_cell64_add8_imm {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (cell64 (a + 8#64) v ⋆ R) m) : loadVal m i64 (a + 8) = some v :=
  loadVal_cell64 h

@[local c0_store] theorem c0_store_cell64_add8_imm {a v0 : BitVec 64} (v : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (h : (cell64 (a + 8#64) v0 ⋆ R) m) :
    storeOk m i64 (a + 8) ∧ (cell64 (a + 8#64) v ⋆ R) (storeMem m i64 (a + 8) v) :=
  store_cell64 v h

@[local c0_load] theorem c0_load_cell64_add16_imm {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (cell64 (a + 16#64) v ⋆ R) m) : loadVal m i64 (a + 16) = some v :=
  loadVal_cell64 h

@[local c0_store] theorem c0_store_cell64_add16_imm {a v0 : BitVec 64} (v : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (h : (cell64 (a + 16#64) v0 ⋆ R) m) :
    storeOk m i64 (a + 16) ∧ (cell64 (a + 16#64) v ⋆ R) (storeMem m i64 (a + 16) v) :=
  store_cell64 v h

@[local c0_load] theorem c0_load_array64_fl {rt i : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array64 (rt + 33024#64) xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i64 (rt + 33024 + i * 8) = some (xs[i.toNat]'hi) :=
  c0_load_array64 h hi

@[local c0_store] theorem c0_store_array64_fl {rt i : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array64 (rt + 33024#64) xs ⋆ R) m) (hi : i.toNat < xs.length) :
    storeOk m i64 (rt + 33024 + i * 8) ∧
      (array64 (rt + 33024#64) (xs.set i.toNat v) ⋆ R) (storeMem m i64 (rt + 33024 + i * 8) v) :=
  c0_store_array64 v h hi

private theorem shl3_eq_mul8 (i : BitVec 64) : i <<< 3#64 = i * 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mul_comm]

@[local c0_load] theorem c0_load_array64_shl3 {a i : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i64 (a + (i <<< 3#64)) = some (xs[i.toNat]'hi) := by
  rw [shl3_eq_mul8]
  exact c0_load_array64 h hi

@[local c0_store] theorem c0_store_array64_shl3 {a i : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    storeOk m i64 (a + (i <<< 3#64)) ∧
      (array64 a (xs.set i.toNat v) ⋆ R) (storeMem m i64 (a + (i <<< 3#64)) v) := by
  rw [shl3_eq_mul8]
  exact c0_store_array64 v h hi

@[local c0_load] theorem c0_load_array64_mul8 {a i : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i64 (a + 8#64 * i) = some (xs[i.toNat]'hi) := by
  rw [BitVec.mul_comm 8#64 i]
  exact c0_load_array64 h hi

@[local c0_store] theorem c0_store_array64_mul8 {a i : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    storeOk m i64 (a + 8#64 * i) ∧
      (array64 a (xs.set i.toNat v) ⋆ R) (storeMem m i64 (a + 8#64 * i) v) := by
  rw [BitVec.mul_comm 8#64 i]
  exact c0_store_array64 v h hi

private theorem bv64_and_mask8 (x : BitVec 64) :
    x &&& 0xfffffffffffffff8#64 = BitVec.ofNat 64 ((x.toNat / 8) * 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by decide : 0xfffffffffffffff8 < 2 ^ 64)]
  rw [Nat.mod_eq_of_lt (by have := x.isLt; omega : (x.toNat / 8) * 8 < 2 ^ 64)]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have h1 : (0xfffffffffffffff8 : Nat) = (2 ^ 61 - 1) <<< 3 := by decide
  have h2 : (x.toNat / 8) * 8 = (x.toNat >>> 3) <<< 3 := by
    simp [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [h1, h2, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 64
  · by_cases h3 : 3 ≤ i
    · have hsr : (x.toNat >>> 3).testBit (i - 3) = x.toNat.testBit i := by
        rw [Nat.testBit_shiftRight, show 3 + (i - 3) = i by omega]
      simp [h3, show i - 3 < 61 by omega, hsr]
    · simp [h3]
  · have hlt : x.toNat.testBit i = false :=
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))
    by_cases h3 : 3 ≤ i <;> simp [h3, show ¬(i - 3 < 61) by omega, hlt]

private theorem align8_bv_eq (sz : BitVec 64) (hsz : sz.toNat ≤ 268435448) :
    (sz + 7) &&& 18446744073709551608 = BitVec.ofNat 64 (align8 sz.toNat) := by
  change (sz + 7#64) &&& 0xfffffffffffffff8#64 = BitVec.ofNat 64 (align8 sz.toNat)
  rw [bv64_and_mask8]
  unfold align8
  congr 1
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 7 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : sz.toNat + 7 < 2 ^ 64)]

private theorem align8_div8_eq (sz : BitVec 64) (hsz : sz.toNat ≤ 268435448) :
    ((sz + 7) &&& 18446744073709551608) >>> 3 = BitVec.ofNat 64 (align8 sz.toNat / 8) := by
  rw [align8_bv_eq sz hsz]
  apply BitVec.eq_of_toNat_eq
  unfold align8
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  simp [Nat.shiftRight_eq_div_pow]

private theorem align8_div8_mul8 {n : Nat} (h : n % 8 = 0) : 8 * (n / 8) = n := by omega

private theorem bv_and7_eq_zero_of_mod8 {x : BitVec 64} (h : x.toNat % 8 = 0) :
    x &&& 7#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_zero,
    Nat.mod_eq_of_lt (by decide : 7 < 2 ^ 64),
    show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, show 2 ^ 3 = 8 from rfl]
  exact h

private theorem bv_ofNat_div8 {n : Nat} (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> 3 = BitVec.ofNat 64 (n / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]
  simp [Nat.shiftRight_eq_div_pow]

private theorem bump_cur_nz {cur endp : BitVec 64} {bytes : Nat}
    (hcur : cur ≠ 0#64) (hle : cur.toNat ≤ endp.toNat) (hbytes : bytes ≤ endp.toNat - cur.toNat) :
    cur + BitVec.ofNat 64 bytes ≠ 0#64 := by
  intro hzero
  have h1 := congrArg BitVec.toNat hzero
  have hlt : cur.toNat + bytes < 2 ^ 64 := by have := endp.isLt; omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : bytes < 2 ^ 64),
    Nat.mod_eq_of_lt hlt, BitVec.toNat_zero] at h1
  apply hcur
  exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_zero]; omega)

private theorem bump_cur_align {cur endp : BitVec 64} {bytes : Nat}
    (hal : cur.toNat % 8 = 0) (hle : cur.toNat ≤ endp.toNat)
    (hbytes : bytes ≤ endp.toNat - cur.toNat) (hmod : bytes % 8 = 0) :
    (cur + BitVec.ofNat 64 bytes).toNat % 8 = 0 := by
  have hlt : cur.toNat + bytes < 2 ^ 64 := by have := endp.isLt; omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : bytes < 2 ^ 64),
    Nat.mod_eq_of_lt hlt]
  omega

private theorem list_getD_set_self {α : Type} (xs : List α) {i : Nat} (v d : α)
    (hi : i < xs.length) : (xs.set i v).getD i d = v := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega : i < xs.length)]

private theorem list_getD_set_ne {α : Type} (xs : List α) {i j : Nat} (v d : α)
    (hne : j ≠ i) : (xs.set i v).getD j d = xs.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne.symm]

/-! ## 2. Small Freelist, `large_free`, Bump Arena, and `freeObjLayout` Helpers -/

private theorem smallPoolSlot_hd_eq {cls : Nat} {hd : BitVec 64} {nodes : List (BitVec 64)}
    {m : Mem 64} (h2 : 2 ≤ cls) (h : smallPoolSlot cls hd nodes m) :
    hd = listHeadPtr nodes := by
  simp only [smallPoolSlot, h2, ↓reduceIte] at h
  cases nodes with
  | nil => exact h.1
  | cons _ _ => exact h.1

private theorem smallPoolSlot_pop {cls : Nat} {hd : BitVec 64} {nodes : List (BitVec 64)}
    {m : Mem 64} (h2 : 2 ≤ cls) (hne : hd ≠ 0#64) (h : smallPoolSlot cls hd nodes m) :
    ∃ rest, nodes = hd :: rest ∧ hd.toNat % 8 = 0 ∧
      ((region hd 8 ⋆ cell64 (hd + 8#64) (listHeadPtr rest) ⋆ region (hd + 16#64) (8 * cls - 16)) ⋆
        smallFreeList (8 * cls) (listHeadPtr rest) rest) m := by
  simp only [smallPoolSlot, h2, ↓reduceIte] at h
  cases nodes with
  | nil => exact absurd h.1 hne
  | cons p rest =>
    rcases h with ⟨rfl, _, halign, hmem⟩
    exact ⟨rest, rfl, halign, hmem⟩

private theorem smallPoolSlot_nil_of_zero {cls : Nat} {nodes : List (BitVec 64)}
    {m : Mem 64} (h2 : 2 ≤ cls) (h : smallPoolSlot cls 0#64 nodes m) : nodes = [] := by
  simp only [smallPoolSlot, h2, ↓reduceIte] at h
  cases nodes with
  | nil => rfl
  | cons _ _ => exact absurd h.1.symm h.2.1

private theorem smallPoolsAt_zero_empty {fl : List (BitVec 64)} {pools : Nat → List (BitVec 64)}
    {cls : Nat} {Q : Mem 64 → Prop} {m : Mem 64}
    (hflLen : fl.length = rtNumClasses) (h2 : 2 ≤ cls) (hlt : cls < rtNumClasses)
    (hz : fl[cls]'(by omega) = 0#64)
    (h : (smallPoolsAt fl pools rtNumClasses ⋆ Q) m) : pools cls = [] := by
  rw [smallPoolsAt_split rtNumClasses fl pools hlt, sep_assoc] at h
  have hget : fl.getD cls 0#64 = 0#64 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : cls < fl.length), hz]
  rw [hget] at h
  obtain ⟨m1, _, _, _, hs, _⟩ := h
  exact smallPoolSlot_nil_of_zero h2 hs

private theorem smallPoolsAt_pop {fl : List (BitVec 64)} {pools : Nat → List (BitVec 64)}
    {cls : Nat} {Q : Mem 64 → Prop} {m : Mem 64}
    (hflLen : fl.length = rtNumClasses) (h2 : 2 ≤ cls) (hlt : cls < rtNumClasses)
    (hne : fl[cls]'(by omega) ≠ 0#64)
    (h : (smallPoolsAt fl pools rtNumClasses ⋆ Q) m) :
    ∃ rest, pools cls = (fl[cls]'(by omega)) :: rest ∧
      (fl[cls]'(by omega)).toNat % 8 = 0 ∧
      ((region (fl[cls]'(by omega)) 8 ⋆
          cell64 ((fl[cls]'(by omega)) + 8#64) (listHeadPtr rest) ⋆
          region ((fl[cls]'(by omega)) + 16#64) (8 * cls - 16)) ⋆
        smallFreeList (8 * cls) (listHeadPtr rest) rest ⋆
        smallPoolsExcl cls fl pools rtNumClasses ⋆ Q) m := by
  rw [smallPoolsAt_split rtNumClasses fl pools hlt, sep_assoc] at h
  have hget : fl.getD cls 0#64 = fl[cls]'(by omega) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : cls < fl.length)]
  rw [hget] at h
  obtain ⟨m1, m2, rfl, hd, hslot, hrest⟩ := h
  obtain ⟨rest, hp, halign, hlist⟩ := smallPoolSlot_pop h2 hne hslot
  refine ⟨rest, hp, halign, ?_⟩
  have h1 : (((region (fl[cls]'(by omega)) 8 ⋆
      cell64 ((fl[cls]'(by omega)) + 8#64) (listHeadPtr rest) ⋆
      region ((fl[cls]'(by omega)) + 16#64) (8 * cls - 16)) ⋆
      smallFreeList (8 * cls) (listHeadPtr rest) rest) ⋆
      (smallPoolsExcl cls fl pools rtNumClasses ⋆ Q)) (m1.union m2) :=
    ⟨m1, m2, rfl, hd, hlist, hrest⟩
  repeat rw [← sep_assoc] at h1
  exact h1

private theorem smallPoolsAt_pop_head {fl fl' : List (BitVec 64)}
    {pools pools' : Nat → List (BitVec 64)} {cls : Nat} {nxt : BitVec 64}
    {rest : List (BitVec 64)} {Q : Mem 64 → Prop} {m : Mem 64}
    (hlt : cls < rtNumClasses) (h2 : 2 ≤ cls)
    (hget : fl'.getD cls 0#64 = nxt)
    (hpcls : pools' cls = rest)
    (hnxt : nxt = listHeadPtr rest)
    (hfl : ∀ i, i ≠ cls → fl'.getD i 0#64 = fl.getD i 0#64)
    (hp : ∀ i, i ≠ cls → pools' i = pools i)
    (h : ((smallFreeList (8 * cls) nxt rest ⋆ smallPoolsExcl cls fl pools rtNumClasses) ⋆ Q) m) :
    (smallPoolsAt fl' pools' rtNumClasses ⋆ Q) m := by
  subst hpcls hnxt
  rw [← hget] at h
  have hslot : ((smallPoolSlot cls (fl'.getD cls 0#64) (pools' cls) ⋆
      smallPoolsExcl cls fl' pools' rtNumClasses) ⋆ Q) m := by
    rw [smallPoolsExcl_update fl fl' pools pools' hfl hp]
    simpa only [smallPoolSlot, h2, ↓reduceIte] using h
  rwa [← smallPoolsAt_split rtNumClasses fl' pools' hlt] at hslot

private theorem smallPoolsAt_push_head {fl fl' : List (BitVec 64)}
    {pools pools' : Nat → List (BitVec 64)} {cls : Nat} {o oldHd : BitVec 64}
    {Q : Mem 64 → Prop} {m : Mem 64}
    (_hflLen : fl.length = rtNumClasses) (hlt : cls < rtNumClasses) (h2 : 2 ≤ cls)
    (hnz : o ≠ 0#64) (halign : o.toNat % 8 = 0)
    (hgetOld : fl.getD cls 0#64 = oldHd)
    (hgetNew : fl'.getD cls 0#64 = o)
    (hpcls : pools' cls = o :: pools cls)
    (hfl : ∀ i, i ≠ cls → fl'.getD i 0#64 = fl.getD i 0#64)
    (hp : ∀ i, i ≠ cls → pools' i = pools i)
    (h : (((region o 8 ⋆ cell64 (o + 8#64) oldHd) ⋆ region (o + 16#64) (8 * cls - 16)) ⋆
      (smallPoolsAt fl pools rtNumClasses ⋆ Q)) m) :
    (smallPoolsAt fl' pools' rtNumClasses ⋆ Q) m := by
  rw [smallPoolsAt_split rtNumClasses fl pools hlt, hgetOld] at h
  have hhd : oldHd = listHeadPtr (pools cls) := by
    obtain ⟨_, _, _, _, _, hs⟩ := h
    rw [sep_assoc] at hs
    obtain ⟨_, _, _, _, hslot, _⟩ := hs
    exact smallPoolSlot_hd_eq h2 hslot
  rw [hhd] at h
  have h1 : (((((region o 8 ⋆ cell64 (o + 8#64) (listHeadPtr (pools cls))) ⋆
      region (o + 16#64) (8 * cls - 16)) ⋆
      smallFreeList (8 * cls) (listHeadPtr (pools cls)) (pools cls)) ⋆
      smallPoolsExcl cls fl pools rtNumClasses) ⋆ Q) m := by
    rw [sep_assoc (p := smallPoolSlot _ _ _)] at h
    rw [← sep_assoc (p := (region o 8 ⋆ cell64 (o + 8#64) (listHeadPtr (pools cls))) ⋆
      region (o + 16#64) (8 * cls - 16))] at h
    rw [← sep_assoc (q := smallPoolsExcl cls fl pools rtNumClasses)] at h
    have hslotEq : smallPoolSlot cls (listHeadPtr (pools cls)) (pools cls) =
        smallFreeList (8 * cls) (listHeadPtr (pools cls)) (pools cls) := by
      simp [smallPoolSlot, h2]
    simpa only [hslotEq] using h
  have hslot' : ((smallPoolSlot cls o (o :: pools cls) ⋆
      smallPoolsExcl cls fl pools rtNumClasses) ⋆ Q) m := by
    refine sep_mono (fun _ hx => sep_mono (fun _ hy => ?_) hx) h1
    simp only [smallPoolSlot, h2, ↓reduceIte]
    exact ⟨rfl, hnz, halign, hy⟩
  rw [← hpcls, ← hgetNew, ← smallPoolsExcl_update fl fl' pools pools' hfl hp] at hslot'
  rwa [← smallPoolsAt_split rtNumClasses fl' pools' hlt] at hslot'

private def largeSegSplit (hd prev lcur : BitVec 64)
    (pfx sfx : List (BitVec 64 × Nat)) (m : Mem 64) : Prop :=
  lcur = largeSegNext 0#64 sfx ∧
  match pfx.reverse with
  | [] => prev = 0#64 ∧ hd = lcur ∧ largeSeg hd 0#64 sfx m
  | (prv, prvB) :: revMid =>
    prev = prv ∧ prv ≠ 0#64 ∧ prv.toNat % 8 = 0 ∧ 512 ≤ prvB ∧ prvB < rtMaxObjBytes ∧ prvB % 8 = 0 ∧
    ((largeSeg hd prv revMid.reverse ⋆ largeFreeNode prvB prv lcur) ⋆ largeSeg lcur 0#64 sfx) m

private theorem largeSegSplit_init {hd : BitVec 64} {nodes : List (BitVec 64 × Nat)} {m : Mem 64}
    (h : largeFreeList hd nodes m) : largeSegSplit hd 0#64 hd [] nodes m :=
  ⟨largeSeg_hd_eq_next h, rfl, rfl, h⟩

private theorem largeSegSplit_nil {hd prev : BitVec 64}
    {pfx : List (BitVec 64 × Nat)} {m : Mem 64}
    (h : largeSegSplit hd prev 0#64 pfx [] m) : largeFreeList hd pfx m := by
  rcases h with ⟨_, hs⟩
  cases hr : pfx.reverse with
  | nil =>
    rw [hr] at hs
    have hp : pfx = [] := List.reverse_eq_nil_iff.mp hr
    subst hp
    exact hs.2.2
  | cons hdRev tlRev =>
    rw [hr] at hs
    rcases hdRev with ⟨prv, prvB⟩
    rcases hs with ⟨_, hnz, hal, hlo, hhi, hmod, hmem⟩
    have hp : pfx = tlRev.reverse ++ [(prv, prvB)] := by
      rw [← List.reverse_reverse pfx, hr]; simp
    rw [hp]
    change ((largeSeg hd prv tlRev.reverse ⋆ largeFreeNode prvB prv 0#64) ⋆
      (fun m => 0#64 = 0#64 ∧ emp m)) m at hmem
    rw [sep_comm, sep_pure_l, emp_sep] at hmem
    exact largeSeg_split_snoc hnz hal hlo hhi hmod tlRev.reverse hmem.2

private theorem largeSegSplit_step {hd prev lcur nxt : BitVec 64} {b : Nat}
    {pfx rest : List (BitVec 64 × Nat)} {m : Mem 64}
    (hcur : lcur ≠ 0#64) (hal : lcur.toNat % 8 = 0)
    (hlo : 512 ≤ b) (hhi : b < rtMaxObjBytes) (hmod : b % 8 = 0)
    (hnxt : nxt = largeSegNext 0#64 rest)
    (hpfx : match pfx.reverse with
      | [] => prev = 0#64 ∧ hd = lcur ∧
        (largeFreeNode b lcur nxt ⋆ largeSeg nxt 0#64 rest) m
      | (prv, prvB) :: revMid =>
        prev = prv ∧ prv ≠ 0#64 ∧ prv.toNat % 8 = 0 ∧ 512 ≤ prvB ∧ prvB < rtMaxObjBytes ∧ prvB % 8 = 0 ∧
        ((largeSeg hd prv revMid.reverse ⋆ largeFreeNode prvB prv lcur) ⋆
          (largeFreeNode b lcur nxt ⋆ largeSeg nxt 0#64 rest)) m) :
    largeSegSplit hd lcur nxt (pfx ++ [(lcur, b)]) rest m := by
  refine ⟨hnxt, ?_⟩
  have hrev : (pfx ++ [(lcur, b)]).reverse = (lcur, b) :: pfx.reverse := by simp
  rw [hrev]
  dsimp only
  rw [List.reverse_reverse]
  refine ⟨rfl, hcur, hal, hlo, hhi, hmod, ?_⟩
  cases hr : pfx.reverse with
  | nil =>
    rw [hr] at hpfx
    have hp : pfx = [] := List.reverse_eq_nil_iff.mp hr
    subst hp
    rcases hpfx with ⟨_, heq, hmem⟩
    subst heq
    change ((largeSeg hd hd [] ⋆ largeFreeNode b hd nxt) ⋆ largeSeg nxt 0#64 rest) m
    refine sep_mono (fun _ hx => ?_) hmem
    change ((fun m => hd = hd ∧ emp m) ⋆ largeFreeNode b hd nxt) _
    rw [sep_pure_l, emp_sep]
    exact ⟨rfl, hx⟩
  | cons hdRev tlRev =>
    rw [hr] at hpfx
    rcases hdRev with ⟨prv, prvB⟩
    rcases hpfx with ⟨_, hnz, halp, hlop, hhip, hmodp, hmem⟩
    have hp : pfx = tlRev.reverse ++ [(prv, prvB)] := by
      rw [← List.reverse_reverse pfx, hr]; simp
    rw [← sep_assoc] at hmem
    refine sep_mono (fun _ hx => sep_mono (fun _ hy => ?_) hx) hmem
    rw [hp]
    exact largeSeg_split_snoc hnz halp hlop hhip hmodp tlRev.reverse hy

private theorem largeSegSplit_empty_sfx_of_ne {hd : BitVec 64} {nodes : List (BitVec 64 × Nat)}
    {m : Mem 64} (hne : largeSegNext 0#64 nodes ≠ 0#64) (h : largeSeg hd 0#64 nodes m) :
    ∃ p b rest, nodes = (p, b) :: rest ∧ p ≠ 0#64 := by
  cases nodes with
  | nil => simp [largeSegNext] at hne
  | cons x rest =>
    rcases x with ⟨p, b⟩
    rcases h with ⟨_, hnz, _⟩
    exact ⟨p, b, rest, rfl, hnz⟩

private theorem largeSegSplit_sfx_nil_of_zero {hd prev : BitVec 64}
    {pfx sfx : List (BitVec 64 × Nat)} {m : Mem 64}
    (h : largeSegSplit hd prev 0#64 pfx sfx m) : sfx = [] := by
  rcases h with ⟨hnext, hs⟩
  cases sfx with
  | nil => rfl
  | cons x rest =>
    rcases x with ⟨p, b⟩
    dsimp only [largeSegNext] at hnext
    cases hr : pfx.reverse with
    | nil =>
      rw [hr] at hs
      rcases hs with ⟨_, _, hseg⟩
      rcases hseg with ⟨_, hnz, _⟩
      exact absurd hnext.symm hnz
    | cons _ _ =>
      rw [hr] at hs
      rcases hs with ⟨_, _, _, _, _, _, hmem⟩
      rcases hmem with ⟨_, _, _, _, _, hseg⟩
      rcases hseg with ⟨_, hnz, _⟩
      exact absurd hnext.symm hnz

private theorem alloc_small_repack {fl fl' : List (BitVec 64)}
    {pools pools' : Nat → List (BitVec 64)} {cls : Nat} {p nxt : BitVec 64}
    {rest : List (BitVec 64)} {Q : Mem 64 → Prop} {m : Mem 64}
    (hlt : cls < rtNumClasses) (h2 : 2 ≤ cls) (hmax : 8 * cls ≤ 2 ^ 64)
    (hget : fl'.getD cls 0#64 = nxt) (hpcls : pools' cls = rest) (hnxt : nxt = listHeadPtr rest)
    (hfl : ∀ i, i ≠ cls → fl'.getD i 0#64 = fl.getD i 0#64)
    (hp : ∀ i, i ≠ cls → pools' i = pools i)
    (h : (((region p 8 ⋆ cell64 (p + 8#64) nxt) ⋆ region (p + 16#64) (8 * cls - 16)) ⋆
      smallFreeList (8 * cls) nxt rest ⋆ smallPoolsExcl cls fl pools rtNumClasses ⋆ Q) m) :
    (smallPoolsAt fl' pools' rtNumClasses ⋆ region p (8 * cls) ⋆ Q) m := by
  have h1 : (((smallFreeList (8 * cls) nxt rest ⋆ smallPoolsExcl cls fl pools rtNumClasses) ⋆
      ((region p 8 ⋆ cell64 (p + 8#64) nxt) ⋆ region (p + 16#64) (8 * cls - 16))) ⋆ Q) m := by
    refine sep_mono (fun _ x => ?_) h
    rw [sep_comm ((region p 8 ⋆ cell64 (p + 8#64) nxt) ⋆ region (p + 16#64) (8 * cls - 16)),
      sep_assoc,
      sep_comm ((region p 8 ⋆ cell64 (p + 8#64) nxt) ⋆ region (p + 16#64) (8 * cls - 16)),
      ← sep_assoc] at x
    exact x
  rw [sep_assoc] at h1
  have h2' := smallPoolsAt_pop_head hlt h2 hget hpcls hnxt hfl hp h1
  rw [← sep_assoc] at h2'
  exact sep_mono (fun _ x => sep_mono_r (fun _ y => smallFreeNode_to_region (by omega) hmax y) x) h2'

private theorem alloc_bump_split {cur : BitVec 64} {bytes rem : Nat}
    {Q : Mem 64 → Prop} {m : Mem 64}
    (_hle : bytes ≤ rem) (hfit : bytes + (rem - bytes) ≤ 2 ^ 64)
    (h : (region cur rem ⋆ Q) m) :
    (region (cur + BitVec.ofNat 64 bytes) (rem - bytes) ⋆ region cur bytes ⋆ Q) m := by
  have hsplit : region cur rem =
      (region cur bytes ⋆ region (cur + BitVec.ofNat 64 bytes) (rem - bytes)) := by
    have hs := region_split (a := cur) (n1 := bytes) (n2 := rem - bytes) hfit
    rwa [show bytes + (rem - bytes) = rem by omega] at hs
  rw [hsplit] at h
  exact sep_mono (fun _ x => by rw [sep_comm]; exact x) h

private theorem largeSegSplit_unlink_head {hd _lcur nxt : BitVec 64}
    {b : Nat} {rest : List (BitVec 64 × Nat)} {Q : Mem 64 → Prop} {m : Mem 64}
    (h512 : 512 ≤ b) (hmax : b < 2 ^ 64)
    (h : ((largeFreeNode b hd nxt ⋆ largeSeg nxt 0#64 rest) ⋆ Q) m) :
    (largeFreeList nxt rest ⋆ region hd b ⋆ Q) m := by
  have h1 : ((region hd b ⋆ largeSeg nxt 0#64 rest) ⋆ Q) m :=
    sep_mono (fun _ hx => sep_mono (P := largeFreeNode b hd nxt)
      (fun _ hy => largeFreeNode_to_region (bytes := b) (by omega) (by omega) hy) hx) h
  exact sep_mono (fun _ x => by rw [sep_comm]; exact x) h1

private theorem largeSegSplit_unlink_mid {hd prv _lcur nxt : BitVec 64}
    {prvB : Nat} {revMid rest : List (BitVec 64 × Nat)} {m : Mem 64}
    (hnz : prv ≠ 0#64) (hal : prv.toNat % 8 = 0)
    (hlo : 512 ≤ prvB) (hhi : prvB < rtMaxObjBytes) (hmod : prvB % 8 = 0)
    (hm : ((largeSeg hd prv revMid.reverse ⋆ largeFreeNode prvB prv nxt) ⋆
      largeSeg nxt 0#64 rest) m) :
    largeFreeList hd (revMid.reverse ++ (prv, prvB) :: rest) m := by
  rw [show revMid.reverse ++ (prv, prvB) :: rest = (revMid.reverse ++ [(prv, prvB)]) ++ rest by simp]
  refine largeSeg_append (mid := nxt) _ rest ?_
  exact sep_mono (fun _ hx => largeSeg_split_snoc hnz hal hlo hhi hmod revMid.reverse hx) hm

private theorem freeObjLayout_split_small {o : BitVec 64} {bytes : Nat} {hdr : BitVec 64}
    {m : Mem 64} (h16 : 16 ≤ bytes) (hmax : bytes < rtMaxObjBytes)
    (hm : freeObjLayout o bytes hdr m) :
    ∃ v8 : BitVec 64,
      ((cell64 o hdr ⋆ cell64 (o + 8#64) v8) ⋆ region (o + 16#64) (bytes - 16)) m := by
  unfold freeObjLayout at hm
  split at hm
  · rcases hm with ⟨w16, _, _, hmem⟩
    have hm1 : (((cell64 o hdr ⋆ region (o + 8#64) 8) ⋆ region (o + 16#64) 8) ⋆
        region (o + 24#64) (bytes - 24)) m :=
      sep_mono (fun _ hx => sep_mono_r (fun _ hc => cell64_to_region hc) hx) hmem
    rw [sep_assoc] at hm1
    have hm2 : ((cell64 o hdr ⋆ region (o + 8#64) 8) ⋆ region (o + 16#64) (bytes - 16)) m := by
      refine sep_mono_r (fun _ hx => ?_) hm1
      have hmg := region_merge_eq (a := o + 16#64) (n1 := 8) (n2 := bytes - 24) (n := bytes - 16)
        (by omega) (by unfold rtMaxObjBytes at hmax; omega)
      rw [show o + 16#64 + BitVec.ofNat 64 8 = o + 24#64 by rw [ptr_add_nat_p]] at hmg
      exact hmg ▸ hx
    obtain ⟨m1, m2, rfl, hd, h1, h2⟩ := hm2
    obtain ⟨m0, m8, rfl, hd0, hcell, hreg8⟩ := h1
    obtain ⟨v8, hcell8⟩ := region_to_cell64 hreg8
    exact ⟨v8, m0.union m8, m2, rfl, hd, ⟨m0, m8, rfl, hd0, hcell, hcell8⟩, h2⟩
  · split at hm
    · rcases hm with ⟨w16, _, hby, hmem⟩
      have h24 : 24 ≤ bytes := by rw [hby]; exact Nat.le_trans (by omega) (align8_ge _)
      have hm1 : (((cell64 o hdr ⋆ region (o + 8#64) 8) ⋆ region (o + 16#64) 8) ⋆
          region (o + 24#64) (bytes - 24)) m :=
        sep_mono (fun _ hx => sep_mono_r (fun _ hc => cell64_to_region hc) hx) hmem
      rw [sep_assoc] at hm1
      have hm2 : ((cell64 o hdr ⋆ region (o + 8#64) 8) ⋆ region (o + 16#64) (bytes - 16)) m := by
        refine sep_mono_r (fun _ hx => ?_) hm1
        have hmg := region_merge_eq (a := o + 16#64) (n1 := 8) (n2 := bytes - 24) (n := bytes - 16)
          (by omega) (by unfold rtMaxObjBytes at hmax; omega)
        rw [show o + 16#64 + BitVec.ofNat 64 8 = o + 24#64 by rw [ptr_add_nat_p]] at hmg
        exact hmg ▸ hx
      obtain ⟨m1, m2, rfl, hd, h1, h2⟩ := hm2
      obtain ⟨m0, m8, rfl, hd0, hcell, hreg8⟩ := h1
      obtain ⟨v8, hcell8⟩ := region_to_cell64 hreg8
      exact ⟨v8, m0.union m8, m2, rfl, hd, ⟨m0, m8, rfl, hd0, hcell, hcell8⟩, h2⟩
    · split at hm
      · rcases hm with ⟨w16, _, hby, hmem⟩
        have h24 : 24 ≤ bytes := by rw [hby]; exact Nat.le_trans (by omega) (align8_ge _)
        have hm1 : (((cell64 o hdr ⋆ region (o + 8#64) 8) ⋆ region (o + 16#64) 8) ⋆
            region (o + 24#64) (bytes - 24)) m :=
          sep_mono (fun _ hx => sep_mono_r (fun _ hc => cell64_to_region hc) hx) hmem
        rw [sep_assoc] at hm1
        have hm2 : ((cell64 o hdr ⋆ region (o + 8#64) 8) ⋆ region (o + 16#64) (bytes - 16)) m := by
          refine sep_mono_r (fun _ hx => ?_) hm1
          have hmg := region_merge_eq (a := o + 16#64) (n1 := 8) (n2 := bytes - 24) (n := bytes - 16)
            (by omega) (by unfold rtMaxObjBytes at hmax; omega)
          rw [show o + 16#64 + BitVec.ofNat 64 8 = o + 24#64 by rw [ptr_add_nat_p]] at hmg
          exact hmg ▸ hx
        obtain ⟨m1, m2, rfl, hd, h1, h2⟩ := hm2
        obtain ⟨m0, m8, rfl, hd0, hcell, hreg8⟩ := h1
        obtain ⟨v8, hcell8⟩ := region_to_cell64 hreg8
        exact ⟨v8, m0.union m8, m2, rfl, hd, ⟨m0, m8, rfl, hd0, hcell, hcell8⟩, h2⟩
      · split at hm
        · rcases hm with ⟨w8, _, _, hmem⟩
          exact ⟨w8, hmem⟩
        · rcases hm with ⟨_, hmem⟩
          have hsp := region_split (a := o + 8#64) (n1 := 8) (n2 := bytes - 16)
            (by unfold rtMaxObjBytes at hmax; omega)
          rw [show o + 8#64 + BitVec.ofNat 64 8 = o + 16#64 by rw [ptr_add_nat_p],
            show 8 + (bytes - 16) = bytes - 8 by omega] at hsp
          have hm1 : (cell64 o hdr ⋆ (region (o + 8#64) 8 ⋆ region (o + 16#64) (bytes - 16))) m :=
            sep_mono_r (fun _ hx => hsp ▸ hx) hmem
          rw [← sep_assoc] at hm1
          obtain ⟨m1, m2, rfl, hd, h1, h2⟩ := hm1
          obtain ⟨m0, m8, rfl, hd0, hcell, hreg8⟩ := h1
          obtain ⟨v8, hcell8⟩ := region_to_cell64 hreg8
          exact ⟨v8, m0.union m8, m2, rfl, hd, ⟨m0, m8, rfl, hd0, hcell, hcell8⟩, h2⟩

private theorem freeObjLayout_split_large {o : BitVec 64} {bytes : Nat} {hdr : BitVec 64}
    {m : Mem 64} (h24 : 24 ≤ bytes) (hmax : bytes < rtMaxObjBytes)
    (hm : freeObjLayout o bytes hdr m) :
    ∃ v8 v16 : BitVec 64,
      (((cell64 o hdr ⋆ cell64 (o + 8#64) v8) ⋆ cell64 (o + 16#64) v16) ⋆
        region (o + 24#64) (bytes - 24)) m := by
  obtain ⟨v8, hsmall⟩ := freeObjLayout_split_small (by omega) hmax hm
  have hsp := region_split (a := o + 16#64) (n1 := 8) (n2 := bytes - 24)
    (by unfold rtMaxObjBytes at hmax; omega)
  rw [show o + 16#64 + BitVec.ofNat 64 8 = o + 24#64 by rw [ptr_add_nat_p],
    show 8 + (bytes - 24) = bytes - 16 by omega] at hsp
  have hm1 : ((cell64 o hdr ⋆ cell64 (o + 8#64) v8) ⋆
      (region (o + 16#64) 8 ⋆ region (o + 24#64) (bytes - 24))) m :=
    sep_mono_r (fun _ hx => hsp ▸ hx) hsmall
  rw [← sep_assoc] at hm1
  obtain ⟨m1, m2, rfl, hd, h1, h2⟩ := hm1
  obtain ⟨m0, m16, rfl, hd0, hc, hreg16⟩ := h1
  obtain ⟨v16, hcell16⟩ := region_to_cell64 hreg16
  exact ⟨v8, v16, m0.union m16, m2, rfl, hd, ⟨m0, m16, rfl, hd0, hc, hcell16⟩, h2⟩

/-! ## 3. `lcnf_alloc_wp` -/

private theorem bump_curLeEnd {cur sEnd : BitVec 64} {bytes : Nat}
    (hle : cur.toNat ≤ sEnd.toNat) (hmax : bytes < rtMaxObjBytes)
    (hrem : bytes ≤ sEnd.toNat - cur.toNat) :
    (cur + BitVec.ofNat 64 bytes).toNat ≤ sEnd.toNat := by
  have := sEnd.isLt
  have hlt : cur.toNat + bytes < 2 ^ 64 := by omega
  have hmod : (BitVec.ofNat 64 bytes).toNat = bytes := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hmax; omega)]
  rw [BitVec.toNat_add, hmod, Nat.mod_eq_of_lt hlt]
  omega

private theorem bump_rem_eq {cur sEnd : BitVec 64} {bytes : Nat}
    (hle : cur.toNat ≤ sEnd.toNat) (hmax : bytes < rtMaxObjBytes)
    (hrem : bytes ≤ sEnd.toNat - cur.toNat) :
    sEnd.toNat - (cur + BitVec.ofNat 64 bytes).toNat = sEnd.toNat - cur.toNat - bytes := by
  have := sEnd.isLt
  have hlt : cur.toNat + bytes < 2 ^ 64 := by omega
  have hmod : (BitVec.ofNat 64 bytes).toNat = bytes := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hmax; omega)]
  rw [BitVec.toNat_add, hmod, Nat.mod_eq_of_lt hlt]
  omega

private theorem rem_of_not_gt {cur sEnd : BitVec 64} {bytes : Nat}
    (hle : cur.toNat ≤ sEnd.toNat) (hmax : bytes < rtMaxObjBytes)
    (hnot : ¬ BitVec.toNat (sEnd - cur) < (BitVec.ofNat 64 bytes).toNat) :
    bytes ≤ sEnd.toNat - cur.toNat := by
  rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hmax; omega)] at hnot
  omega

private theorem rtC0_intro_largeSplit {rt : BitVec 64} {st : RtC0State}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
      array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
      array64 st.hdr.s_work st.workBuf ⋆
      smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
      largeFreeList st.hdr.s_large_free st.largeNodes ⋆
      region st.hdr.s_cur st.rem ⋆ R) m) :
    (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
      array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
      array64 st.hdr.s_work st.workBuf ⋆
      smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
      largeSegSplit st.hdr.s_large_free 0#64 st.hdr.s_large_free [] st.largeNodes ⋆
      region st.hdr.s_cur st.rem ⋆ R) m := by
  have h1 : (largeFreeList st.hdr.s_large_free st.largeNodes ⋆
      (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
        array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
        array64 st.hdr.s_work st.workBuf ⋆
        smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
        region st.hdr.s_cur st.rem ⋆ R)) m := by c0_frame
  have h2 : (largeSegSplit st.hdr.s_large_free 0#64 st.hdr.s_large_free [] st.largeNodes ⋆
      (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
        array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
        array64 st.hdr.s_work st.workBuf ⋆
        smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
        region st.hdr.s_cur st.rem ⋆ R)) m :=
    sep_mono (fun _ hx => largeSegSplit_init hx) h1
  exact sep_cast h2 (by ac_rfl)

private def RtC0State.withAllocStats (st : RtC0State) (bytesBV : BitVec 64)
    (updPeak : Bool) : RtC0State where
  extraArgs := st.extraArgs
  globals := st.globals
  freeList := st.freeList
  hdr :=
    { st.hdr with
      s_st_allocs := st.hdr.s_st_allocs + 1#64
      s_st_bytes := st.hdr.s_st_bytes + bytesBV
      s_st_live := st.hdr.s_st_live + 1#64
      s_st_peak_live := if updPeak then st.hdr.s_st_live + 1#64 else st.hdr.s_st_peak_live }
  workBuf := st.workBuf
  smallPools := st.smallPools
  largeNodes := st.largeNodes
  extraLen := st.extraLen
  globalsLen := st.globalsLen
  freeListLen := st.freeListLen
  workLen := st.workLen
  curLeEnd := st.curLeEnd
  arenaAlign := st.arenaAlign
  curNz := st.curNz

private def RtC0State.withBump (st : RtC0State) (bytes : Nat) (hmax : bytes < rtMaxObjBytes)
    (hrem : bytes ≤ st.rem) (hmod : bytes % 8 = 0) : RtC0State where
  extraArgs := st.extraArgs
  globals := st.globals
  freeList := st.freeList
  hdr := { st.hdr with s_cur := st.hdr.s_cur + BitVec.ofNat 64 bytes }
  workBuf := st.workBuf
  smallPools := st.smallPools
  largeNodes := st.largeNodes
  extraLen := st.extraLen
  globalsLen := st.globalsLen
  freeListLen := st.freeListLen
  workLen := st.workLen
  curLeEnd := bump_curLeEnd st.curLeEnd hmax hrem
  arenaAlign := bump_cur_align st.arenaAlign st.curLeEnd hrem hmod
  curNz := bump_cur_nz st.curNz st.curLeEnd hrem

private theorem sep_extrude_k {X Y K : Mem 64 → Prop} {m : Mem 64}
    (h : (X ⋆ (Y ⋆ K)) m) : ((X ⋆ Y) ⋆ K) m := by
  rwa [sep_assoc]

private theorem bump_state_split {rt : BitVec 64} {st : RtC0State} {bytes : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hmax : bytes < rtMaxObjBytes) (hrem : bytes ≤ st.rem) (hmod : bytes % 8 = 0)
    (hm : (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
      array64 (rt + 33024#64) st.freeList ⋆
      LcnfC0Rt.At rt { st.hdr with s_cur := st.hdr.s_cur + BitVec.ofNat 64 bytes } ⋆
      array64 st.hdr.s_work st.workBuf ⋆
      smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
      largeFreeList st.hdr.s_large_free st.largeNodes ⋆
      region st.hdr.s_cur st.rem ⋆ R) m) :
    (rtC0Inv rt (st.withBump bytes hmax hrem hmod) ⋆ region st.hdr.s_cur bytes ⋆ R) m := by
  let st1 := st.withBump bytes hmax hrem hmod
  have hrem1 : st1.rem = st.rem - bytes :=
    bump_rem_eq st.curLeEnd hmax hrem
  have hlt264 : st.hdr.s_cur.toNat + bytes < 2 ^ 64 := by
    have := st.hdr.s_end.isLt
    unfold RtC0State.rem at hrem
    omega
  have hsum : bytes + (st.rem - bytes) ≤ 2 ^ 64 := by
    have := st.hdr.s_end.isLt
    unfold RtC0State.rem
    omega
  have h1 : (region st.hdr.s_cur st.rem ⋆
      (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
        array64 (rt + 33024#64) st.freeList ⋆
        LcnfC0Rt.At rt { st.hdr with s_cur := st.hdr.s_cur + BitVec.ofNat 64 bytes } ⋆
        array64 st.hdr.s_work st.workBuf ⋆
        smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
        largeFreeList st.hdr.s_large_free st.largeNodes ⋆ R)) m := by c0_frame
  have h2 := alloc_bump_split hrem hsum h1
  change (rtC0Inv rt st1 ⋆ region st.hdr.s_cur bytes ⋆ R) m
  unfold rtC0Inv
  rw [hrem1]
  dsimp only [st1, RtC0State.withBump]
  exact sep_cast h2 (by ac_rfl)

private theorem sep_mono_r' {P Q Q' : Mem 64 → Prop} {m : Mem 64}
    (hm : (P ⋆ Q) m) (h : ∀ x, Q x → Q' x) : (P ⋆ Q') m :=
  sep_mono_r h hm

private theorem sep_mono_7r {A1 A2 A3 A4 A5 A6 A7 X Y : Mem 64 → Prop} {m : Mem 64}
    (h : ∀ m', X m' → Y m')
    (hm : (A1 ⋆ (A2 ⋆ (A3 ⋆ (A4 ⋆ (A5 ⋆ (A6 ⋆ (A7 ⋆ X))))))) m) :
    (A1 ⋆ (A2 ⋆ (A3 ⋆ (A4 ⋆ (A5 ⋆ (A6 ⋆ (A7 ⋆ Y))))))) m :=
  sep_mono_r' hm fun _ h1 => sep_mono_r' h1 fun _ h2 => sep_mono_r' h2 fun _ h3 =>
    sep_mono_r' h3 fun _ h4 => sep_mono_r' h4 fun _ h5 => sep_mono_r' h5 fun _ h6 =>
      sep_mono_r' h6 h

private theorem rtC0_split_tail_region
    {A1 A2 A3 A4 A5 A6 A7 R : Mem 64 → Prop} {cur : BitVec 64} {rem bytes : Nat} {m : Mem 64}
    (hrem : bytes ≤ rem) (hsum : bytes + (rem - bytes) ≤ 2 ^ 64)
    (hm : (A1 ⋆ (A2 ⋆ (A3 ⋆ (A4 ⋆ (A5 ⋆ (A6 ⋆ (A7 ⋆ (region cur rem ⋆ R)))))))) m) :
    (A1 ⋆ (A2 ⋆ (A3 ⋆ (A4 ⋆ (A5 ⋆ (A6 ⋆ (A7 ⋆
      (region (cur + BitVec.ofNat 64 bytes) (rem - bytes) ⋆ region cur bytes ⋆ R)))))))) m :=
  sep_mono_7r (X := region cur rem ⋆ R)
    (Y := region (cur + BitVec.ofNat 64 bytes) (rem - bytes) ⋆ region cur bytes ⋆ R)
    (fun _ hx => alloc_bump_split hrem hsum hx) hm

private theorem sep_goal1_pull_cell {C1 C2 C3 S1 S2 D : Mem 64 → Prop} {m : Mem 64}
    (h : (C1 ⋆ C2 ⋆ C3 ⋆ S1 ⋆ S2 ⋆ D) m) : (C2 ⋆ (C1 ⋆ C3 ⋆ S1 ⋆ S2 ⋆ D)) m :=
  sep_cast h (by ac_rfl)

private theorem sep_rot4_bump {P1 P2 P3 P4 P5 P6 P7 P8 B R : Mem 64 → Prop} {m : Mem 64}
    (h : (P4 ⋆ (P1 ⋆ (P2 ⋆ (P3 ⋆ (P5 ⋆ (P6 ⋆ (P7 ⋆ (P8 ⋆ B ⋆ R)))))))) m) :
    ((P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6 ⋆ P7 ⋆ P8) ⋆ B ⋆ R) m :=
  sep_cast h (by ac_rfl)

private theorem sep_goal1_rearrange {C1 C2 C3 S1 S2 H1 H2 H3 H4 H5 H7 H8 R : Mem 64 → Prop}
    {m : Mem 64}
    (h : (H4 ⋆ (H3 ⋆ (C2 ⋆ (C1 ⋆ (C3 ⋆ (S1 ⋆ (S2 ⋆ (H1 ⋆ (H2 ⋆ (H5 ⋆ (H7 ⋆ (H8 ⋆ R)))))))))))) m) :
    (((C1 ⋆ C2) ⋆ C3) ⋆ S1 ⋆ S2 ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H7 ⋆ H8 ⋆ R)) m :=
  sep_cast h (by ac_rfl)

private theorem sep_goal1_to_rtC0 {S6 B H1 H2 H3 H4 H5 H7 H8 R : Mem 64 → Prop} {m : Mem 64}
    (h : (S6 ⋆ B ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H7 ⋆ H8 ⋆ R)) m) :
    ((H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ S6 ⋆ H7 ⋆ H8) ⋆ B ⋆ R) m :=
  sep_cast h (by ac_rfl)

private theorem sep_swap_large_for_bump {P1 P2 P3 P4 P5 P6 P7 P8 R : Mem 64 → Prop} {m : Mem 64}
    (h : (P4 ⋆ (P7 ⋆ (P1 ⋆ (P2 ⋆ (P3 ⋆ (P5 ⋆ (P6 ⋆ (P8 ⋆ R)))))))) m) :
    (P4 ⋆ (P1 ⋆ (P2 ⋆ (P3 ⋆ (P5 ⋆ (P6 ⋆ (P7 ⋆ (P8 ⋆ R)))))))) m :=
  sep_cast h (by ac_rfl)

private theorem sep_large_intro {H1 H2 H3 H4 H5 H6 L H8 R : Mem 64 → Prop} {m : Mem 64}
    (h : (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ L ⋆ H8 ⋆ R) m) :
    (L ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R)) m :=
  sep_cast h (by ac_rfl)

private theorem sep_large_extro {H1 H2 H3 H4 H5 H6 L H8 R : Mem 64 → Prop} {m : Mem 64}
    (h : (L ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R)) m) :
    (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ L ⋆ H8 ⋆ R) m :=
  sep_cast h (by ac_rfl)

private theorem sep_lcur_nil {N1 N2 N3 N4 N5 H1 H2 H3 H4 H5 H6 H8 R : Mem 64 → Prop} {m : Mem 64}
    (h : ((N1 ⋆ N2 ⋆ N3 ⋆ N4 ⋆ N5) ⋆
      (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R)) m) :
    (N3 ⋆ (N2 ⋆ (N1 ⋆ (N4 ⋆ (N5 ⋆ (H1 ⋆ (H2 ⋆ (H3 ⋆ (H4 ⋆ (H5 ⋆ (H6 ⋆ (H8 ⋆ R)))))))))))) m :=
  sep_cast h (by ac_rfl)

private theorem sep_lcur_nil_back {N1 N2 N3 N4 N5 H1 H2 H3 H4 H5 H6 H8 R : Mem 64 → Prop}
    {m : Mem 64}
    (h : (N3 ⋆ (N2 ⋆ (N1 ⋆ (N4 ⋆ (N5 ⋆ (H1 ⋆ (H2 ⋆ (H3 ⋆ (H4 ⋆ (H5 ⋆ (H6 ⋆ (H8 ⋆ R)))))))))))) m) :
    (((N1 ⋆ N2 ⋆ N3 ⋆ N4) ⋆ N5) ⋆
      (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R)) m :=
  sep_cast h (by ac_rfl)

private theorem sep_lcur_cons {P1 P2 P3 P4 P5 N1 N2 N3 N4 N5 H1 H2 H3 H4 H5 H6 H8 R :
      Mem 64 → Prop} {m : Mem 64}
    (h : (((P1 ⋆ (P2 ⋆ P3 ⋆ P4 ⋆ P5)) ⋆ (N1 ⋆ N2 ⋆ N3 ⋆ N4 ⋆ N5)) ⋆
      (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R)) m) :
    (N3 ⋆ (N2 ⋆ (P3 ⋆ (P1 ⋆ (P2 ⋆ (P4 ⋆ (P5 ⋆ (N1 ⋆ (N4 ⋆ (N5 ⋆
      (H1 ⋆ (H2 ⋆ (H3 ⋆ (H4 ⋆ (H5 ⋆ (H6 ⋆ (H8 ⋆ R))))))))))))))))) m :=
  sep_cast h (by ac_rfl)

private theorem sep_swap_12 {A B D : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ D)) m) : (B ⋆ (A ⋆ D)) m :=
  sep_cast h (by ac_rfl)

private theorem sep_cons_bring_nxt {A B C D : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ (C ⋆ D))) m) : (B ⋆ (C ⋆ (A ⋆ D))) m :=
  sep_cast h (by ac_rfl)

private theorem sep_lcur_cons_back {P1 P2 P3 P4 P5 N1 N2 N3 N4 N5 H1 H2 H3 H4 H5 H6 H8 R :
      Mem 64 → Prop} {m : Mem 64}
    (h : (N2 ⋆ (P3 ⋆ (N3 ⋆ (P1 ⋆ (P2 ⋆ (P4 ⋆ (P5 ⋆ (N1 ⋆ (N4 ⋆ (N5 ⋆
      (H1 ⋆ (H2 ⋆ (H3 ⋆ (H4 ⋆ (H5 ⋆ (H6 ⋆ (H8 ⋆ R))))))))))))))))) m) :
    (((P1 ⋆ (P2 ⋆ P3 ⋆ P4 ⋆ P5)) ⋆ ((N1 ⋆ N2 ⋆ N3 ⋆ N4) ⋆ N5)) ⋆
      (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R)) m :=
  sep_cast h (by ac_rfl)

private theorem sep_head_repack {N1 N2 N3 N4 N5 H1 H2 H3 H4 H5 H6 H8 R : Mem 64 → Prop}
    {m : Mem 64}
    (h : (H4 ⋆ (N3 ⋆ (N2 ⋆ (N1 ⋆ (N4 ⋆ (N5 ⋆ (H1 ⋆ (H2 ⋆ (H3 ⋆ (H5 ⋆ (H6 ⋆ (H8 ⋆ R)))))))))))) m) :
    (((N1 ⋆ N2 ⋆ N3 ⋆ N4) ⋆ N5) ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R)) m :=
  sep_cast h (by ac_rfl)

private theorem sep_head_to_rtC0 {L B H1 H2 H3 H4 H5 H6 H8 R : Mem 64 → Prop} {m : Mem 64}
    (h : (L ⋆ B ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R)) m) :
    ((H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ L ⋆ H8) ⋆ B ⋆ R) m :=
  sep_cast h (by ac_rfl)

private theorem alloc_large_nil_finish {rt lcur : BitVec 64} {st : RtC0State}
    {b bytes : Nat} {rest : List (BitVec 64 × Nat)} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} (updPeak : Bool) (bytesBV : BitVec 64)
    (hcurNz : lcur ≠ 0#64) (hcurAl : lcur.toNat % 8 = 0)
    (hb512 : 512 ≤ b) (hbMax : b < rtMaxObjBytes) (hbEq : b = bytes)
    (hm : (LcnfC0Rt.At rt
        { st.hdr with
          s_large_free := largeSegNext 0#64 rest
          s_st_allocs := st.hdr.s_st_allocs + 1#64
          s_st_live := st.hdr.s_st_live + 1#64
          s_st_peak_live := if updPeak then st.hdr.s_st_live + 1#64 else st.hdr.s_st_peak_live
          s_st_reused := st.hdr.s_st_reused + 1#64
          s_st_bytes := st.hdr.s_st_bytes + bytesBV } ⋆
      (cell64 (lcur + 16#64) (BitVec.ofNat 64 b) ⋆
      (cell64 (lcur + 8#64) (largeSegNext 0#64 rest) ⋆
      (region lcur 8 ⋆
      (region (lcur + 24#64) (b - 24) ⋆
      (largeSeg (largeSegNext 0#64 rest) 0#64 rest ⋆
      (array64 rt st.extraArgs ⋆
      (array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
      (array64 (rt + 33024#64) st.freeList ⋆
      (array64 st.hdr.s_work st.workBuf ⋆
      (smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
      (region st.hdr.s_cur st.rem ⋆ R)))))))))))) m)
    (hQ : ∀ (p : BitVec 64) (st' : RtC0State) (m' : Mem 64),
      p ≠ 0#64 → p.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
      (rtC0Inv rt st' ⋆ region p bytes ⋆ R) m' → Q (p, ()) m') :
    Q (lcur, ()) m := by
  let st1 : RtC0State :=
    { st with
      hdr :=
        { st.hdr with
          s_large_free := largeSegNext 0#64 rest
          s_st_reused := st.hdr.s_st_reused + 1#64 }
      largeNodes := rest }
  let st2 := st1.withAllocStats bytesBV updPeak
  have hrep : ((largeFreeNode b lcur (largeSegNext 0#64 rest) ⋆
      largeSeg (largeSegNext 0#64 rest) 0#64 rest) ⋆
      (array64 rt st2.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st2.globals ⋆
        array64 (rt + 33024#64) st2.freeList ⋆ LcnfC0Rt.At rt st2.hdr ⋆
        array64 st2.hdr.s_work st2.workBuf ⋆
        smallPoolsAt st2.freeList st2.smallPools rtNumClasses ⋆
        region st2.hdr.s_cur st2.rem ⋆ R)) m := by
    unfold largeFreeNode
    exact sep_head_repack hm
  have hu := largeSegSplit_unlink_head (_lcur := lcur) hb512
    (by unfold rtMaxObjBytes at hbMax; omega) hrep
  rw [hbEq] at hu
  refine hQ lcur st2 m hcurNz hcurAl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (Nat.le_refl _) ?_
  unfold rtC0Inv
  exact sep_head_to_rtC0 hu

private theorem sep_mid_to_unlink {P1 P2 P3 P4 P5 N1 N2 N3 N4 N5 H1 H2 H3 H4 H5 H6 H8 R :
      Mem 64 → Prop} {m : Mem 64}
    (h : (H4 ⋆ (P3 ⋆ (N2 ⋆ (N3 ⋆ (P1 ⋆ (P2 ⋆ (P4 ⋆ (P5 ⋆ (N1 ⋆ (N4 ⋆ (N5 ⋆
      (H1 ⋆ (H2 ⋆ (H3 ⋆ (H5 ⋆ (H6 ⋆ (H8 ⋆ R))))))))))))))))) m) :
    ((N1 ⋆ N2 ⋆ N3 ⋆ N4) ⋆
      (((P1 ⋆ (P2 ⋆ P3 ⋆ P4 ⋆ P5)) ⋆ N5) ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R))) m :=
  sep_cast h (by ac_rfl)

private theorem sep_mid_swap_region {L B D : Mem 64 → Prop} {m : Mem 64}
    (h : (B ⋆ (L ⋆ D)) m) : (L ⋆ (B ⋆ D)) m :=
  sep_cast h (by ac_rfl)

private theorem sep_mid_to_rtC0 {L B H1 H2 H3 H4 H5 H6 H8 R : Mem 64 → Prop} {m : Mem 64}
    (h : (L ⋆ (B ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R))) m) :
    ((H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ L ⋆ H8) ⋆ B ⋆ R) m :=
  sep_cast h (by ac_rfl)

private theorem alloc_large_mid_finish {rt prv lcur : BitVec 64} {st : RtC0State}
    {prvB b bytes : Nat} {revMid rest : List (BitVec 64 × Nat)} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} (updPeak : Bool) (bytesBV : BitVec 64)
    (hprvNz : prv ≠ 0#64) (hprvAl : prv.toNat % 8 = 0)
    (hprvLo : 512 ≤ prvB) (hprvMax : prvB < rtMaxObjBytes) (hprvMod : prvB % 8 = 0)
    (hcurNz : lcur ≠ 0#64) (hcurAl : lcur.toNat % 8 = 0)
    (hb512 : 512 ≤ b) (hbMax : b < rtMaxObjBytes) (hbEq : b = bytes)
    (hm : (LcnfC0Rt.At rt
        { st.hdr with
          s_st_allocs := st.hdr.s_st_allocs + 1#64
          s_st_live := st.hdr.s_st_live + 1#64
          s_st_peak_live := if updPeak then st.hdr.s_st_live + 1#64 else st.hdr.s_st_peak_live
          s_st_reused := st.hdr.s_st_reused + 1#64
          s_st_bytes := st.hdr.s_st_bytes + bytesBV } ⋆
      (cell64 (prv + 8#64) (largeSegNext 0#64 rest) ⋆
      (cell64 (lcur + 8#64) (largeSegNext 0#64 rest) ⋆
      (cell64 (lcur + 16#64) (BitVec.ofNat 64 b) ⋆
      (largeSeg st.hdr.s_large_free prv revMid.reverse ⋆
      (region prv 8 ⋆
      (cell64 (prv + 16#64) (BitVec.ofNat 64 prvB) ⋆
      (region (prv + 24#64) (prvB - 24) ⋆
      (region lcur 8 ⋆
      (region (lcur + 24#64) (b - 24) ⋆
      (largeSeg (largeSegNext 0#64 rest) 0#64 rest ⋆
      (array64 rt st.extraArgs ⋆
      (array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
      (array64 (rt + 33024#64) st.freeList ⋆
      (array64 st.hdr.s_work st.workBuf ⋆
      (smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
      (region st.hdr.s_cur st.rem ⋆ R))))))))))))))))) m)
    (hQ : ∀ (p : BitVec 64) (st' : RtC0State) (m' : Mem 64),
      p ≠ 0#64 → p.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
      (rtC0Inv rt st' ⋆ region p bytes ⋆ R) m' → Q (p, ()) m') :
    Q (lcur, ()) m := by
  let st1 : RtC0State :=
    { st with
      hdr := { st.hdr with s_st_reused := st.hdr.s_st_reused + 1#64 }
      largeNodes := revMid.reverse ++ (prv, prvB) :: rest }
  let st2 := st1.withAllocStats bytesBV updPeak
  have hun : (largeFreeNode b lcur (largeSegNext 0#64 rest) ⋆
      (((largeSeg st2.hdr.s_large_free prv revMid.reverse ⋆
        largeFreeNode prvB prv (largeSegNext 0#64 rest)) ⋆
        largeSeg (largeSegNext 0#64 rest) 0#64 rest) ⋆
        (array64 rt st2.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st2.globals ⋆
          array64 (rt + 33024#64) st2.freeList ⋆ LcnfC0Rt.At rt st2.hdr ⋆
          array64 st2.hdr.s_work st2.workBuf ⋆
          smallPoolsAt st2.freeList st2.smallPools rtNumClasses ⋆
          region st2.hdr.s_cur st2.rem ⋆ R))) m := by
    unfold largeFreeNode
    exact sep_mid_to_unlink hm
  have hreg := sep_mono (fun _ hx => largeFreeNode_to_region (by omega)
    (by unfold rtMaxObjBytes at hbMax; omega) hx) hun
  rw [hbEq] at hreg
  have hu := sep_mono (fun _ hx =>
    largeSegSplit_unlink_mid (_lcur := lcur) hprvNz hprvAl hprvLo hprvMax hprvMod hx)
    (sep_mid_swap_region hreg)
  refine hQ lcur st2 m hcurNz hcurAl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (Nat.le_refl _) ?_
  unfold rtC0Inv
  exact sep_mid_to_rtC0 hu

private theorem alloc_small_finish {rt p : BitVec 64} {st : RtC0State}
    {bytes : Nat} {rest : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} (updPeak : Bool) (bytesBV : BitVec 64)
    (hflLen : st.freeList.length = 64) (hcls2 : 2 ≤ bytes / 8) (hclsLt : bytes / 8 < 64)
    (_hmax : bytes < rtMaxObjBytes) (hpNe : p ≠ 0#64) (hpalign : p.toNat % 8 = 0)
    (hbyEq : 8 * (bytes / 8) = bytes)
    (hm : (LcnfC0Rt.At rt
        { st.hdr with
          s_st_allocs := st.hdr.s_st_allocs + 1#64
          s_st_live := st.hdr.s_st_live + 1#64
          s_st_peak_live := if updPeak then st.hdr.s_st_live + 1#64 else st.hdr.s_st_peak_live
          s_st_reused := st.hdr.s_st_reused + 1#64
          s_st_bytes := st.hdr.s_st_bytes + bytesBV } ⋆
      (array64 (rt + 33024#64) (st.freeList.set (bytes / 8) (listHeadPtr rest)) ⋆
      (cell64 (p + 8#64) (listHeadPtr rest) ⋆
      (region p 8 ⋆
      (region (p + 16#64) (8 * (bytes / 8) - 16) ⋆
      (smallFreeList (8 * (bytes / 8)) (listHeadPtr rest) rest ⋆
      (smallPoolsExcl (bytes / 8) st.freeList st.smallPools rtNumClasses ⋆
      (array64 rt st.extraArgs ⋆
      (array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
      (array64 st.hdr.s_work st.workBuf ⋆
      (largeFreeList st.hdr.s_large_free st.largeNodes ⋆
      (region st.hdr.s_cur st.rem ⋆ R)))))))))))) m)
    (hQ : ∀ (p : BitVec 64) (st' : RtC0State) (m' : Mem 64),
      p ≠ 0#64 → p.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
      (rtC0Inv rt st' ⋆ region p bytes ⋆ R) m' → Q (p, ()) m') :
    Q (p, ()) m := by
  let cls := bytes / 8
  let fl' := st.freeList.set cls (listHeadPtr rest)
  let pools' : Nat → List (BitVec 64) := fun i => if i = cls then rest else st.smallPools i
  let st1 : RtC0State :=
    { st with
      freeList := fl'
      hdr := { st.hdr with s_st_reused := st.hdr.s_st_reused + 1#64 }
      smallPools := pools'
      freeListLen := by dsimp [fl']; rw [List.length_set, hflLen]; rfl }
  let st2 := st1.withAllocStats bytesBV updPeak
  have hf : (((region p 8 ⋆ cell64 (p + 8#64) (listHeadPtr rest)) ⋆
      region (p + 16#64) (8 * cls - 16)) ⋆
      smallFreeList (8 * cls) (listHeadPtr rest) rest ⋆
      smallPoolsExcl cls st.freeList st.smallPools rtNumClasses ⋆
      (array64 rt st2.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st2.globals ⋆
        array64 (rt + 33024#64) st2.freeList ⋆ LcnfC0Rt.At rt st2.hdr ⋆
        array64 st2.hdr.s_work st2.workBuf ⋆
        largeFreeList st2.hdr.s_large_free st2.largeNodes ⋆
        region st2.hdr.s_cur st2.rem ⋆ R)) m :=
    sep_goal1_rearrange hm
  have hre := alloc_small_repack (fl := st.freeList) (fl' := fl') (pools := st.smallPools)
    (pools' := pools') (by unfold rtNumClasses; omega) hcls2
    (by omega)
    (list_getD_set_self st.freeList (listHeadPtr rest) 0#64 (by rw [hflLen]; exact hclsLt))
    (by dsimp only [pools']; split; rfl; contradiction) rfl
    (fun i hi => list_getD_set_ne st.freeList (listHeadPtr rest) 0#64 hi)
    (fun i hi => by dsimp only [pools']; split; contradiction; rfl) hf
  rw [hbyEq] at hre
  refine hQ p st2 m hpNe hpalign ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (Nat.le_refl _) ?_
  unfold rtC0Inv
  exact sep_goal1_to_rtC0 hre

private theorem alloc_bump_finish {rt : BitVec 64} {st : RtC0State}
    {bytes : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} (updPeak : Bool) (bytesBV : BitVec 64)
    (hcurLe : st.hdr.s_cur.toNat ≤ st.hdr.s_end.toNat)
    (hmax : bytes < rtMaxObjBytes) (hrem : bytes ≤ st.rem) (hmod : bytes % 8 = 0)
    (hbyEq : bytesBV = BitVec.ofNat 64 bytes)
    (hm : (LcnfC0Rt.At rt
        { st.hdr with
          s_cur := st.hdr.s_cur + BitVec.ofNat 64 bytes
          s_st_allocs := st.hdr.s_st_allocs + 1#64
          s_st_live := st.hdr.s_st_live + 1#64
          s_st_peak_live := if updPeak then st.hdr.s_st_live + 1#64 else st.hdr.s_st_peak_live
          s_st_bytes := st.hdr.s_st_bytes + BitVec.ofNat 64 bytes } ⋆
      (array64 rt st.extraArgs ⋆
      (array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
      (array64 (rt + 33024#64) st.freeList ⋆
      (array64 st.hdr.s_work st.workBuf ⋆
      (smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
      (largeFreeList st.hdr.s_large_free st.largeNodes ⋆
      (region st.hdr.s_cur st.rem ⋆ R)))))))) m)
    (hQ : ∀ (p : BitVec 64) (st' : RtC0State) (m' : Mem 64),
      p ≠ 0#64 → p.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
      (rtC0Inv rt st' ⋆ region p bytes ⋆ R) m' → Q (p, ()) m') :
    Q (st.hdr.s_cur, ()) m := by
  have hsum : bytes + (st.rem - bytes) ≤ 2 ^ 64 := by
    have := st.hdr.s_end.isLt
    unfold RtC0State.rem at hrem ⊢
    omega
  have hsplit := rtC0_split_tail_region hrem hsum hm
  let st1 := (st.withBump bytes hmax hrem hmod).withAllocStats bytesBV updPeak
  have hst1Rem : st1.rem ≤ st.rem := by
    unfold st1 RtC0State.withAllocStats RtC0State.withBump RtC0State.rem
    rw [bump_rem_eq hcurLe hmax hrem]
    omega
  refine hQ st.hdr.s_cur st1 m st.curNz st.arenaAlign
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hst1Rem ?_
  unfold rtC0Inv
  dsimp only [st1, RtC0State.withAllocStats, RtC0State.withBump, RtC0State.rem]
  rw [hbyEq]
  rw [show (st.hdr.s_end.toNat - (st.hdr.s_cur + BitVec.ofNat 64 bytes).toNat) = st.rem - bytes from
    bump_rem_eq hcurLe hmax hrem]
  exact sep_rot4_bump hsplit

private theorem rtC0_pull_smallPools {rt : BitVec 64} {st : RtC0State}
    {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
      array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
      array64 st.hdr.s_work st.workBuf ⋆
      smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
      largeFreeList st.hdr.s_large_free st.largeNodes ⋆
      region st.hdr.s_cur st.rem ⋆ R) m) :
    (smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
      (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
        array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
        array64 st.hdr.s_work st.workBuf ⋆
        largeFreeList st.hdr.s_large_free st.largeNodes ⋆
        region st.hdr.s_cur st.rem ⋆ R)) m := by
  c0_frame

private theorem lcnf_alloc_small_wp (Γ : Env) (rt sz : Val i64) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) (hsmall : align8 sz.toNat / 8 < 64)
    (hspec : lcnfAllocSpec (rt, sz, ()) m Q X) :
    Func.wp Γ lcnf_alloc_body (rt, sz, ()) m Q X := by
  rcases hspec with ⟨st, R, hsz, hmin, hmax, havail, hm, hQ⟩
  have hflLen : st.freeList.length = 64 := st.freeListLen
  have hcurLe : st.hdr.s_cur.toNat ≤ st.hdr.s_end.toNat := st.curLeEnd
  have hbyBv := align8_bv_eq sz hsz
  have hclsEq := align8_div8_eq sz hsz
  have hbyMod : align8 sz.toNat % 8 = 0 := by unfold align8; omega
  have hby16 : ¬ ((sz + 7) &&& 18446744073709551608).toNat < 16 := by
    rw [hbyBv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hmax; omega)]
    unfold rtMinObjBytes at hmin
    omega
  let bytes := align8 sz.toNat
  let bytesBV : BitVec 64 := BitVec.ofNat 64 bytes
  have hbyBvNat : bytesBV.toNat = bytes := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hmax; omega)]
  unfold rtC0Inv at hm
  change LeanQbe.T.Func.wp _ _ _ _ _ _
  c0_steps
  · -- Goal 1: `cls < 64`, freelist head `p ≠ 0#64`
    have hcls : (((sz + 7) &&& 18446744073709551608) >>> 3).toNat < (64 : BitVec 64).toNat := by
      assumption
    rw [hclsEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hmax; omega)] at hcls
    have hclsLt : bytes / 8 < 64 := hcls
    have hcls2 : 2 ≤ bytes / 8 := by unfold rtMinObjBytes at hmin; omega
    have hbyEq : 8 * (bytes / 8) = bytes := align8_div8_mul8 hbyMod
    let cls := bytes / 8
    have hclsBvNat : (BitVec.ofNat 64 cls).toNat = cls := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cls < 2 ^ 64)]
    have hidxNat : (((sz + 7) &&& 18446744073709551608) >>> 3).toNat = cls := by
      rw [hclsEq, hclsBvNat]
    have hflEq : (st.freeList[(((sz + 7) &&& 18446744073709551608) >>> 3).toNat]'(by
        rw [hflLen, hidxNat]; exact hclsLt)) =
        st.freeList[cls]'(by rw [hflLen]; exact hclsLt) := by
      simp only [hidxNat]
    have hne : st.freeList[cls]'(by rw [hflLen]; exact hclsLt) ≠ 0#64 := by
      rw [← hflEq]
      exact hc
    obtain ⟨p, hpEq⟩ : ∃ p, p = st.freeList[cls]'(by rw [hflLen]; exact hclsLt) := ⟨_, rfl⟩
    have hpNe : p ≠ 0#64 := hpEq ▸ hne
    have hflIdx : (st.freeList[(((sz + 7) &&& 18446744073709551608) >>> 3).toNat]'(by
        rw [hflLen, hidxNat]; exact hclsLt)) = p :=
      hflEq.trans hpEq.symm
    simp only [hflIdx]
    obtain ⟨rest, hpcls, hpalign, hmPop⟩ :=
      smallPoolsAt_pop st.freeListLen hcls2 (by unfold rtNumClasses; omega) hne
        (rtC0_pull_smallPools hm)
    have hpEq' : p = st.freeList[bytes / 8]'(by rw [hflLen]; exact hclsLt) := hpEq
    have hmLoad : (cell64 (p + 8#64) (listHeadPtr rest) ⋆
        (region p 8 ⋆ region (p + 16#64) (8 * cls - 16) ⋆
          smallFreeList (8 * cls) (listHeadPtr rest) rest ⋆
          smallPoolsExcl cls st.freeList st.smallPools rtNumClasses ⋆
          (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
            array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
            array64 st.hdr.s_work st.workBuf ⋆
            largeFreeList st.hdr.s_large_free st.largeNodes ⋆
            region st.hdr.s_cur st.rem ⋆ R))) m := by
      have hmPop0 : (((region p 8 ⋆ cell64 (p + 8#64) (listHeadPtr rest)) ⋆
          region (p + 16#64) (8 * cls - 16)) ⋆
          smallFreeList (8 * cls) (listHeadPtr rest) rest ⋆
          smallPoolsExcl cls st.freeList st.smallPools rtNumClasses ⋆
          (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
            array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
            array64 st.hdr.s_work st.workBuf ⋆
            largeFreeList st.hdr.s_large_free st.largeNodes ⋆
            region st.hdr.s_cur st.rem ⋆ R)) m := by
        simpa only [cls, ← hpEq'] using hmPop
      exact sep_goal1_pull_cell hmPop0
    clear hm hmPop
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    · -- Goal 1a: `live + 1 > peak_live`
      rw [hidxNat, hbyBv] at hm
      dsimp only [cls] at hm
      exact alloc_small_finish true (BitVec.ofNat 64 bytes) hflLen hcls2 hclsLt hmax
        hpNe (hpEq ▸ hpalign) hbyEq hm hQ
    · -- Goal 1b: `¬ (live + 1 > peak_live)`
      rw [hidxNat, hbyBv] at hm
      dsimp only [cls] at hm
      exact alloc_small_finish false (BitVec.ofNat 64 bytes) hflLen hcls2 hclsLt hmax
        hpNe (hpEq ▸ hpalign) hbyEq hm hQ
  · -- Goal 2: `cls < 64`, `p == 0`, impossible panic branch `bytes > end - cur`
    exfalso
    have hcls : (((sz + 7) &&& 18446744073709551608) >>> 3).toNat < (64 : BitVec 64).toNat := by
      assumption
    rw [hclsEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hmax; omega)] at hcls
    have hclsLt : bytes / 8 < 64 := hcls
    have hcls2 : 2 ≤ bytes / 8 := by unfold rtMinObjBytes at hmin; omega
    let cls := bytes / 8
    have hclsBvNat : (BitVec.ofNat 64 cls).toNat = cls := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cls < 2 ^ 64)]
    have hz : st.freeList[(((sz + 7) &&& 18446744073709551608) >>> 3).toNat]'(by
        rw [hflLen, hclsEq, hclsBvNat]; exact hclsLt) = 0#64 := by
      assumption
    have hidxNat : (((sz + 7) &&& 18446744073709551608) >>> 3).toNat = cls := by
      rw [hclsEq, hclsBvNat]
    have hflEq : (st.freeList[(((sz + 7) &&& 18446744073709551608) >>> 3).toNat]'(by
        rw [hflLen, hidxNat]; exact hclsLt)) =
        st.freeList[cls]'(by rw [hflLen]; exact hclsLt) := by
      simp only [hidxNat]
    have hz' : st.freeList[cls]'(by rw [hflLen]; exact hclsLt) = 0#64 := by
      rw [← hflEq]
      exact hz
    have hpoolEmpty := smallPoolsAt_zero_empty hflLen hcls2 (by unfold rtNumClasses; omega) hz'
      (rtC0_pull_smallPools hm)
    have hlt512 : bytes < 512 := by omega
    have hrem : bytes ≤ st.rem := by
      rcases havail with (⟨_, hne⟩ | ⟨hge, _⟩) | hrem
      · exact absurd hpoolEmpty (by simpa [cls] using hne)
      · omega
      · exact hrem
    have hgt : BitVec.toNat (st.hdr.s_end - st.hdr.s_cur) <
        ((sz + 7) &&& 18446744073709551608).toNat := by assumption
    rw [BitVec.toNat_sub_of_le hcurLe, hbyBv, hbyBvNat] at hgt
    unfold RtC0State.rem at hrem
    omega
  · -- Goal 3: `cls < 64`, `p == 0`, bump, `live > peak_live`
    have hnot : ¬ BitVec.toNat (st.hdr.s_end - st.hdr.s_cur) <
        ((sz + 7) &&& 18446744073709551608).toNat := by assumption
    rw [hbyBv] at hnot
    have hrem : bytes ≤ st.rem := rem_of_not_gt hcurLe hmax hnot
    rw [hbyBv] at hm
    exact alloc_bump_finish true bytesBV hcurLe hmax hrem hbyMod rfl hm hQ
  · -- Goal 4: `cls < 64`, `p == 0`, bump, `¬ (live > peak_live)`
    have hnot : ¬ BitVec.toNat (st.hdr.s_end - st.hdr.s_cur) <
        ((sz + 7) &&& 18446744073709551608).toNat := by assumption
    rw [hbyBv] at hnot
    have hrem : bytes ≤ st.rem := rem_of_not_gt hcurLe hmax hnot
    rw [hbyBv] at hm
    exact alloc_bump_finish false bytesBV hcurLe hmax hrem hbyMod rfl hm hQ

private theorem lcnf_alloc_large_wp (Γ : Env) (rt sz : Val i64) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) (hlarge : ¬ align8 sz.toNat / 8 < 64)
    (hspec : lcnfAllocSpec (rt, sz, ()) m Q X) :
    Func.wp Γ lcnf_alloc_body (rt, sz, ()) m Q X := by
  rcases hspec with ⟨st, R, hsz, hmin, hmax, havail, hm, hQ⟩
  have hflLen : st.freeList.length = 64 := st.freeListLen
  have hcurLe : st.hdr.s_cur.toNat ≤ st.hdr.s_end.toNat := st.curLeEnd
  have hbyBv := align8_bv_eq sz hsz
  have hclsEq := align8_div8_eq sz hsz
  have hbyMod : align8 sz.toNat % 8 = 0 := by unfold align8; omega
  have hby16 : ¬ ((sz + 7) &&& 18446744073709551608).toNat < 16 := by
    rw [hbyBv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hmax; omega)]
    unfold rtMinObjBytes at hmin
    omega
  let bytes := align8 sz.toNat
  let bytesBV : BitVec 64 := BitVec.ofNat 64 bytes
  have hbyBvNat : bytesBV.toNat = bytes := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hmax; omega)]
  unfold rtC0Inv at hm
  change LeanQbe.T.Func.wp _ _ _ _ _ _
  c0_steps
  · -- `cls >= 64`, `large_free` loop or bump
    have hcls : ¬ (((sz + 7) &&& 18446744073709551608) >>> 3).toNat < (64 : BitVec 64).toNat := by
      assumption
    rw [hclsEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hmax; omega)] at hcls
    have h64 : (64 : BitVec 64).toNat = 64 := rfl
    rw [h64] at hcls
    have hbyEq : 8 * (bytes / 8) = bytes := align8_div8_mul8 hbyMod
    have hge512 : 512 ≤ bytes := by omega
    let LInv : Nat → Tup Val [i64, i64] → Mem 64 → Prop := fun n (prev, lcur, ()) ml =>
      ∃ pfx sfx, sfx.length = n ∧ st.largeNodes = pfx ++ sfx ∧
        (∀ x ∈ pfx, x.2 ≠ bytes) ∧
        (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
          array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
          array64 st.hdr.s_work st.workBuf ⋆
          smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
          largeSegSplit st.hdr.s_large_free prev lcur pfx sfx ⋆
          region st.hdr.s_cur st.rem ⋆ R) ml
    refine wp_loop_group LInv ?_ ?_
    · intro L n ⟨prev, lcur, ⟨⟩⟩ ml hL ⟨pfx, sfx, hlen, hnodes, hnePfx, hmem⟩
      by_cases hlc0 : lcur = 0#64
      · -- `lcur = 0#64` (exhausted `large_free`, fall through to bump)
        subst hlc0
        have hlg := sep_large_intro hmem
        clear hm hmem
        obtain ⟨m1, m2, rfl, hd, hsp, hrest⟩ := hlg
        have hsfx : sfx = [] := largeSegSplit_sfx_nil_of_zero hsp
        subst hsfx
        have hnil := largeSegSplit_nil hsp
        rw [List.append_nil] at hnodes
        have hallNe : ∀ x ∈ st.largeNodes, x.2 ≠ bytes := by rw [hnodes]; exact hnePfx
        have hrem : bytes ≤ st.rem := by
          rcases havail with (⟨hlt, _⟩ | ⟨_, x, hx, heq⟩) | hrem
          · omega
          · exact absurd heq (hallNe x hx)
          · exact hrem
        have hm : (largeFreeList st.hdr.s_large_free st.largeNodes ⋆
            (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
              array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
              array64 st.hdr.s_work st.workBuf ⋆
              smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
              region st.hdr.s_cur st.rem ⋆ R)) (m1.union m2) := by
          rw [hnodes]; exact ⟨m1, m2, rfl, hd, hnil, hrest⟩
        clear hd hsp hnil hrest
        change LeanQbe.T.wp _ _ _ _ _
        c0_steps
        · exfalso; exact absurd rfl (by assumption)
        · exfalso
          have hgt : (2 ^ 64 - st.hdr.s_cur.toNat + st.hdr.s_end.toNat) % 2 ^ 64 <
              ((sz + 7) &&& 18446744073709551608).toNat := by assumption
          rw [hbyBv, hbyBvNat] at hgt
          have hlt264 := st.hdr.s_end.isLt
          unfold RtC0State.rem at hrem
          omega
        · rw [hbyBv] at hm
          exact alloc_bump_finish true bytesBV hcurLe hmax hrem hbyMod rfl
            (sep_swap_large_for_bump hm) hQ
        · rw [hbyBv] at hm
          exact alloc_bump_finish false bytesBV hcurLe hmax hrem hbyMod rfl
            (sep_swap_large_for_bump hm) hQ
        · exfalso; have htf : true = false := (by assumption); cases htf
        · exfalso; have htf : true = false := (by assumption); cases htf
      · -- `lcur ≠ 0#64`
        have hlg := sep_large_intro hmem
        clear hm hmem
        obtain ⟨m1, m2, rfl, hd, hsp, hrest⟩ := hlg
        cases sfx with
        | nil =>
          rcases hsp with ⟨hnext, _⟩
          simp [largeSegNext] at hnext
          exact absurd hnext hlc0
        | cons x rest =>
          rcases x with ⟨curp, b⟩
          rcases hsp with ⟨hnext, hpfxSplit⟩
          dsimp only [largeSegNext] at hnext
          subst hnext
          cases hr : pfx.reverse with
          | nil =>
            rw [hr] at hpfxSplit
            rcases hpfxSplit with ⟨hprev0, hhdEq, hseg⟩
            rcases hseg with ⟨_, hcurNz, hcurAl, hb512, hbMax, hbMod, hnodeSeg⟩
            rw [hprev0] at *
            unfold largeFreeNode at hnodeSeg
            have hm := sep_lcur_nil ⟨m1, m2, rfl, hd, hnodeSeg, hrest⟩
            clear hd hnodeSeg hrest
            change LeanQbe.T.wp _ _ _ _ _
            c0_steps
            · exfalso; exact absurd rfl (by assumption)
            · -- `b = bytes`, `updPeak = true` (`prev = 0#64`)
              have hbc : BitVec.ofNat 64 b = ((sz + 7) &&& 18446744073709551608) := by assumption
              rw [hbyBv] at hbc
              have hbEq : b = bytes := by
                have hnat := congrArg BitVec.toNat hbc
                rw [BitVec.toNat_ofNat, hbyBvNat,
                  Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hbMax; omega)] at hnat
                exact hnat
              rw [hbyBv] at hm
              exact alloc_large_nil_finish true bytesBV hcurNz hcurAl hb512 hbMax hbEq hm hQ
            · -- `b = bytes`, `updPeak = false` (`prev = 0#64`)
              have hbc : BitVec.ofNat 64 b = ((sz + 7) &&& 18446744073709551608) := by assumption
              rw [hbyBv] at hbc
              have hbEq : b = bytes := by
                have hnat := congrArg BitVec.toNat hbc
                rw [BitVec.toNat_ofNat, hbyBvNat,
                  Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hbMax; omega)] at hnat
                exact hnat
              rw [hbyBv] at hm
              exact alloc_large_nil_finish false bytesBV hcurNz hcurAl hb512 hbMax hbEq hm hQ
            · -- `b ≠ bytes` (`prev = 0#64`)
              have hbc : ¬ BitVec.ofNat 64 b = ((sz + 7) &&& 18446744073709551608) := by assumption
              rw [hbyBv] at hbc
              have hbNe : b ≠ bytes := by
                intro hEq; apply hbc; subst hEq; rfl
              let nxt := largeSegNext 0#64 rest
              have hback := sep_lcur_nil_back hm
              obtain ⟨m1', m2', heq, hd', hm1', hrest'⟩ := hback
              have hmStep : largeSegSplit lcur lcur nxt ([] ++ [(lcur, b)]) rest m1' := by
                refine largeSegSplit_step (prev := 0#64) hcurNz hcurAl hb512 hbMax hbMod rfl ?_
                exact ⟨rfl, rfl, hm1'⟩
              have hmAll : (largeSegSplit st.hdr.s_large_free lcur nxt [(lcur, b)] rest ⋆
                  (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
                    array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
                    array64 st.hdr.s_work st.workBuf ⋆
                    smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
                    region st.hdr.s_cur st.rem ⋆ R)) (m1'.union m2') := by
                rw [hhdEq]
                exact ⟨m1', m2', rfl, hd', by simpa using hmStep, hrest'⟩
              rw [heq] at hmAll
              refine hL rest.length (lcur, nxt, ()) _ (by simp only [List.length_cons] at hlen; omega)
                ⟨[(lcur, b)], rest, rfl, ?_, ?_, sep_large_extro hmAll⟩
              · rw [hnodes]
                have hpNil : pfx = [] := List.reverse_eq_nil_iff.mp hr
                simp [hpNil]
              · intro x hx
                simp only [List.mem_singleton] at hx
                subst hx
                exact hbNe
          | cons hdRev tlRev =>
            rw [hr] at hpfxSplit
            rcases hdRev with ⟨prv, prvB⟩
            rcases hpfxSplit with ⟨hprev, hprvNz, hprvAl, hprvLo, hprvMax, hprvMod, hseg⟩
            rw [hprev] at *
            obtain ⟨m11, m12, rfl, hd1, hprefMem, hsfxMem⟩ := hseg
            rcases hsfxMem with ⟨_, hcurNz, hcurAl, hb512, hbMax, hbMod, hnodeSeg⟩
            unfold largeFreeNode at hprefMem hnodeSeg
            have hm := sep_lcur_cons
              ⟨m11.union m12, m2, rfl, hd, ⟨m11, m12, rfl, hd1, hprefMem, hnodeSeg⟩, hrest⟩
            clear hd hd1 hprefMem hnodeSeg hrest
            change LeanQbe.T.wp _ _ _ _ _
            c0_steps
            · -- `b = bytes` (`prev = prv ≠ 0#64`)
              have hbc : BitVec.ofNat 64 b = ((sz + 7) &&& 18446744073709551608) := by assumption
              rw [hbyBv] at hbc
              have hbEq : b = bytes := by
                have hnat := congrArg BitVec.toNat hbc
                rw [BitVec.toNat_ofNat, hbyBvNat,
                  Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hbMax; omega)] at hnat
                exact hnat
              have hm0 := sep_cons_bring_nxt hm
              clear hm
              have hm := hm0
              clear hm0
              change LeanQbe.T.wp _ _ _ _ _
              c0_steps
              all_goals first
                | (exfalso; exact absurd rfl (by assumption))
                | (exfalso; have htf : true = false := (by assumption); cases htf)
                | (exfalso; exact hcurNz (by assumption))
                | (exfalso; have h0 : ¬ lcur ≠ 0#64 := (by assumption); exact h0 hcurNz)
                | (exfalso; exact hprvNz (by assumption))
                | (have hm1 := sep_swap_12 hm
                   clear hm
                   have hm := hm1
                   clear hm1
                   change LeanQbe.T.wp _ _ _ _ _
                   c0_steps
                   all_goals first
                     | (have hpk : st.hdr.s_st_peak_live.toNat <
                           (st.hdr.s_st_live.toNat + BitVec.toNat 1#64) % 2 ^ 64 := by assumption
                        rw [hbyBv] at hm
                        exact alloc_large_mid_finish true bytesBV hprvNz hprvAl hprvLo hprvMax hprvMod
                          hcurNz hcurAl hb512 hbMax hbEq hm hQ)
                     | (have hnpk : ¬ st.hdr.s_st_peak_live.toNat <
                           (st.hdr.s_st_live.toNat + BitVec.toNat 1#64) % 2 ^ 64 := by assumption
                        rw [hbyBv] at hm
                        exact alloc_large_mid_finish false bytesBV hprvNz hprvAl hprvLo hprvMax hprvMod
                          hcurNz hcurAl hb512 hbMax hbEq hm hQ))
            · -- `b ≠ bytes` (`prev = prv ≠ 0#64`)
              have hbc : ¬ BitVec.ofNat 64 b = ((sz + 7) &&& 18446744073709551608) := by assumption
              rw [hbyBv] at hbc
              have hbNe : b ≠ bytes := by
                intro hEq; apply hbc; subst hEq; rfl
              let nxt := largeSegNext 0#64 rest
              have hm := sep_cons_bring_nxt hm
              change LeanQbe.T.wp _ _ _ _ _
              c0_steps
              have hback := sep_lcur_cons_back hm
              obtain ⟨m12', m2', heq, hd', hm12', hrest'⟩ := hback
              obtain ⟨m11', m12'', heq1, hd1', hp', hn'⟩ := hm12'
              have hmStep : largeSegSplit st.hdr.s_large_free lcur nxt (pfx ++ [(lcur, b)]) rest
                  (m11'.union m12'') := by
                refine largeSegSplit_step (prev := prv) hcurNz hcurAl hb512 hbMax hbMod rfl ?_
                rw [hr]
                exact ⟨rfl, hprvNz, hprvAl, hprvLo, hprvMax, hprvMod,
                  m11', m12'', rfl, hd1', hp', hn'⟩
              rw [heq1] at hmStep
              have hmAll : (largeSegSplit st.hdr.s_large_free lcur nxt (pfx ++ [(lcur, b)]) rest ⋆
                  (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
                    array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
                    array64 st.hdr.s_work st.workBuf ⋆
                    smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
                    region st.hdr.s_cur st.rem ⋆ R)) (m12'.union m2') :=
                ⟨m12', m2', rfl, hd', hmStep, hrest'⟩
              rw [heq] at hmAll
              refine hL rest.length (lcur, nxt, ()) _ (by simp only [List.length_cons] at hlen; omega)
                ⟨pfx ++ [(lcur, b)], rest, rfl,
                  by rw [hnodes]; simp only [List.append_assoc, List.singleton_append],
                  fun x hx => ?_, sep_large_extro hmAll⟩
              · rcases List.mem_append.mp hx with h | h
                · exact hnePfx x h
                · simp only [List.mem_singleton] at h; subst h; exact hbNe
    · intro L hL
      change LeanQbe.T.wp _ _ _ _ _
      c0_steps
      exact hL st.largeNodes.length (0#64, st.hdr.s_large_free, ()) m
        ⟨[], st.largeNodes, rfl, rfl,
          (fun x h => False.elim (List.not_mem_nil h)), rtC0_intro_largeSplit hm⟩

theorem lcnf_alloc_wp (Γ : Env) :
    ∀ xs m Q X, lcnfAllocSpec xs m Q X → Func.wp Γ lcnf_alloc_body xs m Q X := by
  rintro ⟨rt, sz, ⟨⟩⟩ m Q X hspec
  by_cases hsmall : align8 sz.toNat / 8 < 64
  · exact lcnf_alloc_small_wp Γ rt sz m Q X hsmall hspec
  · exact lcnf_alloc_large_wp Γ rt sz m Q X hsmall hspec

/-! ## `lcnf_free_obj` -/

private def RtC0State.withFreeSmall (st : RtC0State) (cls : Nat) (o : BitVec 64) : RtC0State where
  extraArgs := st.extraArgs
  globals := st.globals
  freeList := st.freeList.set cls o
  hdr := st.hdr
  workBuf := st.workBuf
  smallPools := fun i => if i = cls then o :: st.smallPools i else st.smallPools i
  largeNodes := st.largeNodes
  extraLen := st.extraLen
  globalsLen := st.globalsLen
  freeListLen := by rw [List.length_set]; exact st.freeListLen
  workLen := st.workLen
  curLeEnd := st.curLeEnd
  arenaAlign := st.arenaAlign
  curNz := st.curNz

private def RtC0State.withFreeLarge (st : RtC0State) (o : BitVec 64) (bytes : Nat) : RtC0State where
  extraArgs := st.extraArgs
  globals := st.globals
  freeList := st.freeList
  hdr := { st.hdr with s_large_free := o }
  workBuf := st.workBuf
  smallPools := st.smallPools
  largeNodes := (o, bytes) :: st.largeNodes
  extraLen := st.extraLen
  globalsLen := st.globalsLen
  freeListLen := st.freeListLen
  workLen := st.workLen
  curLeEnd := st.curLeEnd
  arenaAlign := st.arenaAlign
  curNz := st.curNz

private def RtC0State.withFreeStats (st : RtC0State) : RtC0State where
  extraArgs := st.extraArgs
  globals := st.globals
  freeList := st.freeList
  hdr :=
    { st.hdr with
      s_st_frees := st.hdr.s_st_frees + 1#64
      s_st_live := st.hdr.s_st_live - 1#64 }
  workBuf := st.workBuf
  smallPools := st.smallPools
  largeNodes := st.largeNodes
  extraLen := st.extraLen
  globalsLen := st.globalsLen
  freeListLen := st.freeListLen
  workLen := st.workLen
  curLeEnd := st.curLeEnd
  arenaAlign := st.arenaAlign
  curNz := st.curNz

private theorem sep_free_small_prep {C0 C8 Robj H1 H2 H3 H4 H5 H6 H7 H8 R : Mem 64 → Prop}
    {m : Mem 64}
    (h : ((H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H7 ⋆ H8) ⋆ (((C0 ⋆ C8) ⋆ Robj) ⋆ R)) m) :
    (C0 ⋆ (H3 ⋆ (C8 ⋆ (H4 ⋆ (H1 ⋆ (H2 ⋆ (H5 ⋆ (H6 ⋆ (H7 ⋆ (H8 ⋆ (Robj ⋆ R))))))))))) m :=
  sep_cast h (by ac_rfl)

private theorem sep_free_small_swap {C0 H3 C8 Rest : Mem 64 → Prop} {m : Mem 64}
    (h : (C0 ⋆ (H3 ⋆ (C8 ⋆ Rest))) m) :
    (H3 ⋆ (C8 ⋆ (C0 ⋆ Rest))) m :=
  sep_cast h (by ac_rfl)

private theorem sep_free_small_to_push {C0 C8 H4 H3 H1 H2 H5 H6 H7 H8 Robj R : Mem 64 → Prop}
    {m : Mem 64}
    (h : (H3 ⋆ (C8 ⋆ (C0 ⋆ (H4 ⋆ (H1 ⋆ (H2 ⋆ (H5 ⋆ (H6 ⋆ (H7 ⋆ (H8 ⋆ (Robj ⋆ R))))))))))) m) :
    (((C0 ⋆ C8) ⋆ Robj) ⋆ (H6 ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H7 ⋆ H8 ⋆ R))) m :=
  sep_cast h (by ac_rfl)

private theorem sep_free_small_to_rtC0 {H6 H1 H2 H3 H4 H5 H7 H8 R : Mem 64 → Prop}
    {m : Mem 64}
    (h : (H6 ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H7 ⋆ H8 ⋆ R)) m) :
    ((H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H7 ⋆ H8) ⋆ R) m :=
  sep_cast h (by ac_rfl)

private theorem sep_free_large_prep {C0 C8 C16 Robj H1 H2 H3 H4 H5 H6 H7 H8 R : Mem 64 → Prop}
    {m : Mem 64}
    (h : ((H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H7 ⋆ H8) ⋆ ((((C0 ⋆ C8) ⋆ C16) ⋆ Robj) ⋆ R)) m) :
    (C0 ⋆ (H4 ⋆ (C8 ⋆ (C16 ⋆ (H1 ⋆ (H2 ⋆ (H3 ⋆ (H5 ⋆ (H6 ⋆ (H7 ⋆ (H8 ⋆ (Robj ⋆ R)))))))))))) m :=
  sep_cast h (by ac_rfl)

private theorem sep_free_large_swap {C0 H4 C8 C16 Rest : Mem 64 → Prop} {m : Mem 64}
    (h : (C0 ⋆ (H4 ⋆ (C8 ⋆ (C16 ⋆ Rest)))) m) :
    (H4 ⋆ (C8 ⋆ (C16 ⋆ (C0 ⋆ Rest)))) m :=
  sep_cast h (by ac_rfl)

private theorem sep_free_large_to_node {H4 C16 C8 C0 H1 H2 H3 H5 H6 H7 H8 Robj R :
      Mem 64 → Prop} {m : Mem 64}
    (h : (H4 ⋆ (C8 ⋆ (C16 ⋆ (C0 ⋆ (H1 ⋆ (H2 ⋆ (H3 ⋆ (H5 ⋆ (H6 ⋆ (H7 ⋆ (H8 ⋆ (Robj ⋆ R)))))))))))) m) :
    (((C0 ⋆ C8 ⋆ C16 ⋆ Robj) ⋆ H7) ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R)) m :=
  sep_cast h (by ac_rfl)

private theorem sep_free_large_to_rtC0 {H7 H1 H2 H3 H4 H5 H6 H8 R : Mem 64 → Prop}
    {m : Mem 64}
    (h : (H7 ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R)) m) :
    ((H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H7 ⋆ H8) ⋆ R) m :=
  sep_cast h (by ac_rfl)

private theorem free_obj_pull_hdr {H1 H2 H3 H4 H5 H6 H7 H8 R : Mem 64 → Prop} {m : Mem 64}
    (h : ((H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H7 ⋆ H8) ⋆ R) m) :
    (H4 ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H5 ⋆ H6 ⋆ H7 ⋆ H8 ⋆ R)) m :=
  sep_cast h (by ac_rfl)

private theorem free_obj_back_hdr {H4 H1 H2 H3 H5 H6 H7 H8 R : Mem 64 → Prop} {m : Mem 64}
    (h : (H4 ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H5 ⋆ H6 ⋆ H7 ⋆ H8 ⋆ R)) m) :
    ((H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H7 ⋆ H8) ⋆ R) m :=
  sep_cast h (by ac_rfl)

private theorem free_obj_put_tag246 {H1 C0 R8 C16 R24 R : Mem 64 → Prop} {m : Mem 64}
    (h : ((H1 ⋆ (C0 ⋆ R8 ⋆ C16 ⋆ R24)) ⋆ R) m) :
    (C16 ⋆ (C0 ⋆ R8 ⋆ R24 ⋆ H1 ⋆ R)) m :=
  sep_cast h (by ac_rfl)

private theorem free_obj_put_tag250 {H1 C0 C8 R16 R : Mem 64 → Prop} {m : Mem 64}
    (h : ((H1 ⋆ (C0 ⋆ C8 ⋆ R16)) ⋆ R) m) :
    (C8 ⋆ (C0 ⋆ R16 ⋆ H1 ⋆ R)) m :=
  sep_cast h (by ac_rfl)

private theorem free_obj_pull_cell0 {H1 C0 Tail R : Mem 64 → Prop} {m : Mem 64}
    (h : ((H1 ⋆ (C0 ⋆ Tail)) ⋆ R) m) :
    (C0 ⋆ (H1 ⋆ (Tail ⋆ R))) m :=
  sep_cast h (by ac_rfl)

private theorem bv64_align8_eq {n : Nat} (hn : n + 7 < 2 ^ 64) :
    (BitVec.ofNat 64 n + 7#64) &&& 18446744073709551608#64 = BitVec.ofNat 64 (align8 n) := by
  have hsum : BitVec.ofNat 64 n + 7#64 = BitVec.ofNat 64 (n + 7) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have : (7 : Nat) % 2 ^ 64 = 7 := by decide
    have : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
    have : (n + 7) % 2 ^ 64 = n + 7 := Nat.mod_eq_of_lt hn
    omega
  have hmask : ∀ x : BitVec 64, x &&& 18446744073709551608#64 = (x >>> 3) <<< 3 := by
    intro x
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h0 : (18446744073709551608#64).getLsbD i = !decide (i < 3) := by
      have hdec : ∀ j : Fin 64, (18446744073709551608#64).getLsbD j.1 = !decide (j.1 < 3) := by decide
      exact hdec ⟨i, hi⟩
    have h1 : ((x >>> 3) <<< 3).getLsbD i = if i < 3 then false else x.getLsbD i := by
      simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
      by_cases h3 : i < 3
      · simp [h3]
      · simp [h3, hi, show 3 + (i - 3) = i by omega]
    simp only [BitVec.getLsbD_and]
    rw [h0, h1]
    by_cases h3 : i < 3 <;> simp [h3]
  rw [hsum, hmask]
  unfold align8
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]

private theorem free_obj_post_small_finish {rt o oldHd : BitVec 64} {st : RtC0State}
    {bytes : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hoNz : o ≠ 0#64) (hoAl : o.toNat % 8 = 0)
    (hmin : rtMinObjBytes ≤ bytes) (_hmax : bytes < rtMaxObjBytes)
    (hmod : bytes % 8 = 0) (hsmall : bytes / 8 < 64)
    (hgetOld : st.freeList.getD (bytes / 8) 0#64 = oldHd)
    (hm : (array64 (rt + 33024#64) (st.freeList.set (bytes / 8) o) ⋆
      (cell64 (o + 8#64) oldHd ⋆
      (cell64 o 0#64 ⋆
      (LcnfC0Rt.At rt st.hdr ⋆
      (array64 rt st.extraArgs ⋆
      (array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
      (array64 st.hdr.s_work st.workBuf ⋆
      (smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
      (largeFreeList st.hdr.s_large_free st.largeNodes ⋆
      (region st.hdr.s_cur st.rem ⋆
      (region (o + 16#64) (bytes - 16) ⋆ R))))))))))) m) :
    (rtC0Inv rt (st.withFreeSmall (bytes / 8) o) ⋆ R) m := by
  let cls := bytes / 8
  let st1 := st.withFreeSmall cls o
  have hflLen : st.freeList.length = rtNumClasses := st.freeListLen
  have hcls2 : 2 ≤ cls := by unfold rtMinObjBytes at hmin; omega
  have hclsLt : cls < rtNumClasses := by unfold rtNumClasses; omega
  have hbyEq : 8 * cls = bytes := align8_div8_mul8 hmod
  have hm0 : (cell64 o 0#64 ⋆
      (array64 (rt + 33024#64) st1.freeList ⋆
      (cell64 (o + 8#64) oldHd ⋆
      (LcnfC0Rt.At rt st1.hdr ⋆
      (array64 rt st1.extraArgs ⋆
      (array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st1.globals ⋆
      (array64 st1.hdr.s_work st1.workBuf ⋆
      (smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
      (largeFreeList st1.hdr.s_large_free st1.largeNodes ⋆
      (region st1.hdr.s_cur st1.rem ⋆
      (region (o + 16#64) (bytes - 16) ⋆ R))))))))))) m :=
    sep_cast hm (by ac_rfl)
  have hmReg : (array64 (rt + 33024#64) st1.freeList ⋆
      (cell64 (o + 8#64) oldHd ⋆
      (region o 8 ⋆
      (LcnfC0Rt.At rt st1.hdr ⋆
      (array64 rt st1.extraArgs ⋆
      (array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st1.globals ⋆
      (array64 st1.hdr.s_work st1.workBuf ⋆
      (smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
      (largeFreeList st1.hdr.s_large_free st1.largeNodes ⋆
      (region st1.hdr.s_cur st1.rem ⋆
      (region (o + 16#64) (bytes - 16) ⋆ R))))))))))) m :=
    sep_cast (sep_mono (P' := region o 8) (fun _ hc => cell64_to_region hc) hm0) (by ac_rfl)
  have hmPush := sep_free_small_to_push hmReg
  rw [← hbyEq] at hmPush
  have hre : (smallPoolsAt st1.freeList st1.smallPools rtNumClasses ⋆
      (array64 rt st1.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st1.globals ⋆
        array64 (rt + 33024#64) st1.freeList ⋆ LcnfC0Rt.At rt st1.hdr ⋆
        array64 st1.hdr.s_work st1.workBuf ⋆
        largeFreeList st1.hdr.s_large_free st1.largeNodes ⋆
        region st1.hdr.s_cur st1.rem ⋆ R)) m :=
    smallPoolsAt_push_head hflLen hclsLt hcls2 hoNz hoAl hgetOld
      (list_getD_set_self st.freeList o 0#64 (by rw [hflLen]; exact hclsLt))
      (by simp [st1, RtC0State.withFreeSmall])
      (fun i hi => list_getD_set_ne st.freeList o 0#64 hi)
      (fun i hi => by simp [st1, RtC0State.withFreeSmall, hi])
      hmPush
  unfold rtC0Inv
  exact sep_free_small_to_rtC0 hre

private theorem free_obj_post_large_finish {rt o oldHd : BitVec 64} {st : RtC0State}
    {bytes : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hoNz : o ≠ 0#64) (hoAl : o.toNat % 8 = 0)
    (h512 : 512 ≤ bytes) (hmax : bytes < rtMaxObjBytes) (hmod : bytes % 8 = 0)
    (hOldHd : oldHd = largeSegNext 0#64 st.largeNodes)
    (hm : (LcnfC0Rt.At rt { st.hdr with s_large_free := o } ⋆
      (cell64 (o + 8#64) oldHd ⋆
      (cell64 (o + 16#64) (BitVec.ofNat 64 bytes) ⋆
      (cell64 o 0#64 ⋆
      (array64 rt st.extraArgs ⋆
      (array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
      (array64 (rt + 33024#64) st.freeList ⋆
      (array64 st.hdr.s_work st.workBuf ⋆
      (smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
      (largeFreeList oldHd st.largeNodes ⋆
      (region st.hdr.s_cur st.rem ⋆
      (region (o + 24#64) (bytes - 24) ⋆ R)))))))))))) m) :
    (rtC0Inv rt (st.withFreeLarge o bytes) ⋆ R) m := by
  let st1 := st.withFreeLarge o bytes
  have hm0 : (cell64 o 0#64 ⋆
      (LcnfC0Rt.At rt st1.hdr ⋆
      (cell64 (o + 8#64) oldHd ⋆
      (cell64 (o + 16#64) (BitVec.ofNat 64 bytes) ⋆
      (array64 rt st1.extraArgs ⋆
      (array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st1.globals ⋆
      (array64 (rt + 33024#64) st1.freeList ⋆
      (array64 st1.hdr.s_work st1.workBuf ⋆
      (smallPoolsAt st1.freeList st1.smallPools rtNumClasses ⋆
      (largeFreeList oldHd st.largeNodes ⋆
      (region st1.hdr.s_cur st1.rem ⋆
      (region (o + 24#64) (bytes - 24) ⋆ R)))))))))))) m :=
    sep_cast hm (by ac_rfl)
  have hmReg : (LcnfC0Rt.At rt st1.hdr ⋆
      (cell64 (o + 8#64) oldHd ⋆
      (cell64 (o + 16#64) (BitVec.ofNat 64 bytes) ⋆
      (region o 8 ⋆
      (array64 rt st1.extraArgs ⋆
      (array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st1.globals ⋆
      (array64 (rt + 33024#64) st1.freeList ⋆
      (array64 st1.hdr.s_work st1.workBuf ⋆
      (smallPoolsAt st1.freeList st1.smallPools rtNumClasses ⋆
      (largeFreeList oldHd st.largeNodes ⋆
      (region st1.hdr.s_cur st1.rem ⋆
      (region (o + 24#64) (bytes - 24) ⋆ R)))))))))))) m :=
    sep_cast (sep_mono (P' := region o 8) (fun _ hc => cell64_to_region hc) hm0) (by ac_rfl)
  have hnd : (((largeFreeNode bytes o oldHd) ⋆ largeFreeList oldHd st.largeNodes) ⋆
      (array64 rt st1.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st1.globals ⋆
        array64 (rt + 33024#64) st1.freeList ⋆ LcnfC0Rt.At rt st1.hdr ⋆
        array64 st1.hdr.s_work st1.workBuf ⋆
        smallPoolsAt st1.freeList st1.smallPools rtNumClasses ⋆
        region st1.hdr.s_cur st1.rem ⋆ R)) m := by
    unfold largeFreeNode
    exact sep_free_large_to_node hmReg
  have hcons : (largeFreeList st1.hdr.s_large_free st1.largeNodes ⋆
      (array64 rt st1.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st1.globals ⋆
        array64 (rt + 33024#64) st1.freeList ⋆ LcnfC0Rt.At rt st1.hdr ⋆
        array64 st1.hdr.s_work st1.workBuf ⋆
        smallPoolsAt st1.freeList st1.smallPools rtNumClasses ⋆
        region st1.hdr.s_cur st1.rem ⋆ R)) m := by
    refine sep_mono (fun _ hx => ?_) hnd
    unfold largeFreeList
    dsimp only [st1, RtC0State.withFreeLarge]
    rw [largeSeg.eq_2]
    exact ⟨rfl, hoNz, hoAl, h512, hmax, hmod, hOldHd ▸ hx⟩
  unfold rtC0Inv
  exact sep_free_large_to_rtC0 hcons

private def freeObjBody (o : BitVec 64) (bytes : Nat) (hdr : BitVec 64) : Mem 64 → Prop :=
  have tag := (hdr >>> 56).toNat
  if tag = arrayTag then fun m =>
    ∃ w16, w16.toNat ≤ 33554428 ∧ bytes = 24 + 8 * w16.toNat ∧
      (region (o + 8#64) 8 ⋆ cell64 (o + 16#64) w16 ⋆ region (o + 24#64) (bytes - 24)) m
  else if tag = sarrayTag then fun m =>
    ∃ w16, w16.toNat ≤ 268435455 ∧
      bytes = align8 (24 + ((hdr >>> 48).toNat % 128) * w16.toNat) ∧
      (region (o + 8#64) 8 ⋆ cell64 (o + 16#64) w16 ⋆ region (o + 24#64) (bytes - 24)) m
  else if tag = stringTag then fun m =>
    ∃ w16, w16.toNat ≤ 268435415 ∧ bytes = align8 (32 + w16.toNat) ∧
      (region (o + 8#64) 8 ⋆ cell64 (o + 16#64) w16 ⋆ region (o + 24#64) (bytes - 24)) m
  else if tag = mpzTag then fun m =>
    ∃ w8, (w8 &&& 4294967295#64).toNat ≤ 33554429 ∧
      bytes = 16 + 8 * (w8 &&& 4294967295#64).toNat ∧
      (cell64 (o + 8#64) w8 ⋆ region (o + 16#64) (bytes - 16)) m
  else fun m =>
    (hdr >>> 32 &&& 65535#64).toNat = bytes ∧ region (o + 8#64) (bytes - 8) m

private theorem freeObjLayout_to_cell_body {o : BitVec 64} {bytes : Nat} {hdr : BitVec 64}
    {m : Mem 64} (hm : freeObjLayout o bytes hdr m) :
    (cell64 o hdr ⋆ freeObjBody o bytes hdr) m := by
  unfold freeObjLayout at hm
  unfold freeObjBody
  split at hm
  · rename_i ht; rw [ite_eq_left ht]
    rcases hm with ⟨w16, hw1, hw2, hmem⟩
    exact sep_mono_r (fun _ hb => ⟨w16, hw1, hw2, hb⟩) (sep_cast hmem (by ac_rfl))
  · split at hm
    · rename_i ht1 ht2; rw [ite_eq_right ht1, ite_eq_left ht2]
      rcases hm with ⟨w16, hw1, hw2, hmem⟩
      exact sep_mono_r (fun _ hb => ⟨w16, hw1, hw2, hb⟩) (sep_cast hmem (by ac_rfl))
    · split at hm
      · rename_i ht1 ht2 ht3; rw [ite_eq_right ht1, ite_eq_right ht2, ite_eq_left ht3]
        rcases hm with ⟨w16, hw1, hw2, hmem⟩
        exact sep_mono_r (fun _ hb => ⟨w16, hw1, hw2, hb⟩) (sep_cast hmem (by ac_rfl))
      · split at hm
        · rename_i ht1 ht2 ht3 ht4
          rw [ite_eq_right ht1, ite_eq_right ht2, ite_eq_right ht3, ite_eq_left ht4]
          rcases hm with ⟨w8, hw1, hw2, hmem⟩
          exact sep_mono_r (fun _ hb => ⟨w8, hw1, hw2, hb⟩) (sep_cast hmem (by ac_rfl))
        · rename_i ht1 ht2 ht3 ht4
          rw [ite_eq_right ht1, ite_eq_right ht2, ite_eq_right ht3, ite_eq_right ht4]
          exact sep_mono_r (fun _ hb => ⟨hm.1, hb⟩) hm.2

private theorem free_obj_tri_split_small {o w16 : BitVec 64} {bytes : Nat} {m : Mem 64}
    (hmax : bytes < rtMaxObjBytes)
    (hm : (region (o + 8#64) 8 ⋆ cell64 (o + 16#64) w16 ⋆ region (o + 24#64) (bytes - 24)) m)
    (h24 : 24 ≤ bytes) :
    ∃ v8 : BitVec 64, (cell64 (o + 8#64) v8 ⋆ region (o + 16#64) (bytes - 16)) m := by
  have h0 : (cell64 (o + 16#64) w16 ⋆ (region (o + 8#64) 8 ⋆ region (o + 24#64) (bytes - 24))) m :=
    sep_cast hm (by ac_rfl)
  have h1 : (region (o + 8#64) 8 ⋆ (region (o + 16#64) 8 ⋆ region (o + 24#64) (bytes - 24))) m :=
    sep_cast (sep_mono (P' := region (o + 16#64) 8) (fun _ hc => cell64_to_region hc) h0) (by ac_rfl)
  have hsp := region_split (a := o + 16#64) (n1 := 8) (n2 := bytes - 24)
    (by unfold rtMaxObjBytes at hmax; omega)
  rw [show o + 16#64 + BitVec.ofNat 64 8 = o + 24#64 by rw [ptr_add_nat_p],
    show 8 + (bytes - 24) = bytes - 16 by omega] at hsp
  have h2 : (region (o + 8#64) 8 ⋆ region (o + 16#64) (bytes - 16)) m :=
    sep_mono_r (fun _ hr => hsp ▸ hr) h1
  obtain ⟨m1, m2, rfl, hd, hr8, hr16⟩ := h2
  obtain ⟨v8, hc8⟩ := region_to_cell64 hr8
  exact ⟨v8, m1, m2, rfl, hd, hc8, hr16⟩

private theorem freeObjBody_split_small {o hdr : BitVec 64} {bytes : Nat} {m : Mem 64}
    (hmin : rtMinObjBytes ≤ bytes) (hmax : bytes < rtMaxObjBytes)
    (hm : freeObjBody o bytes hdr m) :
    ∃ v8 : BitVec 64, (cell64 (o + 8#64) v8 ⋆ region (o + 16#64) (bytes - 16)) m := by
  unfold freeObjBody at hm
  split at hm
  · rcases hm with ⟨w16, _, hby, hmem⟩
    exact free_obj_tri_split_small hmax hmem (by omega)
  · split at hm
    · rcases hm with ⟨w16, _, hby, hmem⟩
      exact free_obj_tri_split_small hmax hmem (by unfold align8 at hby; omega)
    · split at hm
      · rcases hm with ⟨w16, _, hby, hmem⟩
        exact free_obj_tri_split_small hmax hmem (by unfold align8 at hby; omega)
      · split at hm
        · rcases hm with ⟨w8, _, _, hmem⟩
          exact ⟨w8, hmem⟩
        · rcases hm with ⟨_, hmem⟩
          have hsp := region_split (a := o + 8#64) (n1 := 8) (n2 := bytes - 16)
            (by unfold rtMaxObjBytes at hmax; omega)
          rw [show o + 8#64 + BitVec.ofNat 64 8 = o + 16#64 by rw [ptr_add_nat_p],
            show 8 + (bytes - 16) = bytes - 8 by unfold rtMinObjBytes at hmin; omega] at hsp
          obtain ⟨m1, m2, rfl, hd, hr8, hr16⟩ := hsp ▸ hmem
          obtain ⟨v8, hc8⟩ := region_to_cell64 hr8
          exact ⟨v8, m1, m2, rfl, hd, hc8, hr16⟩

private theorem freeObjBody_split_large {o hdr : BitVec 64} {bytes : Nat} {m : Mem 64}
    (h24 : 24 ≤ bytes) (hmax : bytes < rtMaxObjBytes) (hm : freeObjBody o bytes hdr m) :
    ∃ v8 v16 : BitVec 64,
      ((cell64 (o + 8#64) v8 ⋆ cell64 (o + 16#64) v16) ⋆ region (o + 24#64) (bytes - 24)) m := by
  unfold freeObjBody at hm
  split at hm
  · rcases hm with ⟨w16, _, _, hmem⟩
    have h0 : (region (o + 8#64) 8 ⋆ (cell64 (o + 16#64) w16 ⋆ region (o + 24#64) (bytes - 24))) m :=
      sep_cast hmem (by ac_rfl)
    obtain ⟨m1, m2, rfl, hd, hr8, h23⟩ := h0
    obtain ⟨v8, hc8⟩ := region_to_cell64 hr8
    have h1 : (cell64 (o + 8#64) v8 ⋆ (cell64 (o + 16#64) w16 ⋆ region (o + 24#64) (bytes - 24)))
        (m1.union m2) := ⟨m1, m2, rfl, hd, hc8, h23⟩
    have hfin : ((cell64 (o + 8#64) v8 ⋆ cell64 (o + 16#64) w16) ⋆
        region (o + 24#64) (bytes - 24)) (m1.union m2) :=
      sep_cast h1 (by ac_rfl)
    exact ⟨v8, w16, hfin⟩
  · split at hm
    · rcases hm with ⟨w16, _, _, hmem⟩
      have h0 : (region (o + 8#64) 8 ⋆ (cell64 (o + 16#64) w16 ⋆ region (o + 24#64) (bytes - 24))) m :=
        sep_cast hmem (by ac_rfl)
      obtain ⟨m1, m2, rfl, hd, hr8, h23⟩ := h0
      obtain ⟨v8, hc8⟩ := region_to_cell64 hr8
      have h1 : (cell64 (o + 8#64) v8 ⋆ (cell64 (o + 16#64) w16 ⋆ region (o + 24#64) (bytes - 24)))
          (m1.union m2) := ⟨m1, m2, rfl, hd, hc8, h23⟩
      have hfin : ((cell64 (o + 8#64) v8 ⋆ cell64 (o + 16#64) w16) ⋆
          region (o + 24#64) (bytes - 24)) (m1.union m2) :=
        sep_cast h1 (by ac_rfl)
      exact ⟨v8, w16, hfin⟩
    · split at hm
      · rcases hm with ⟨w16, _, _, hmem⟩
        have h0 : (region (o + 8#64) 8 ⋆ (cell64 (o + 16#64) w16 ⋆ region (o + 24#64) (bytes - 24))) m :=
          sep_cast hmem (by ac_rfl)
        obtain ⟨m1, m2, rfl, hd, hr8, h23⟩ := h0
        obtain ⟨v8, hc8⟩ := region_to_cell64 hr8
        have h1 : (cell64 (o + 8#64) v8 ⋆ (cell64 (o + 16#64) w16 ⋆ region (o + 24#64) (bytes - 24)))
            (m1.union m2) := ⟨m1, m2, rfl, hd, hc8, h23⟩
        have hfin : ((cell64 (o + 8#64) v8 ⋆ cell64 (o + 16#64) w16) ⋆
            region (o + 24#64) (bytes - 24)) (m1.union m2) :=
          sep_cast h1 (by ac_rfl)
        exact ⟨v8, w16, hfin⟩
      · split at hm
        · rcases hm with ⟨w8, _, _, hmem⟩
          have hsp := region_split (a := o + 16#64) (n1 := 8) (n2 := bytes - 24)
            (by unfold rtMaxObjBytes at hmax; omega)
          rw [show o + 16#64 + BitVec.ofNat 64 8 = o + 24#64 by rw [ptr_add_nat_p],
            show 8 + (bytes - 24) = bytes - 16 by omega] at hsp
          have h1 : (region (o + 16#64) 8 ⋆ (cell64 (o + 8#64) w8 ⋆ region (o + 24#64) (bytes - 24))) m :=
            sep_cast (sep_mono_r (fun _ hr => hsp ▸ hr) hmem) (by ac_rfl)
          obtain ⟨m1, m2, rfl, hd, hr16, hrest⟩ := h1
          obtain ⟨v16, hc16⟩ := region_to_cell64 hr16
          have h2 : (cell64 (o + 16#64) v16 ⋆ (cell64 (o + 8#64) w8 ⋆ region (o + 24#64) (bytes - 24)))
              (m1.union m2) := ⟨m1, m2, rfl, hd, hc16, hrest⟩
          have hfin : ((cell64 (o + 8#64) w8 ⋆ cell64 (o + 16#64) v16) ⋆
              region (o + 24#64) (bytes - 24)) (m1.union m2) :=
            sep_cast h2 (by ac_rfl)
          exact ⟨w8, v16, hfin⟩
        · rcases hm with ⟨_, hmem⟩
          have hsp1 := region_split (a := o + 8#64) (n1 := 8) (n2 := bytes - 16)
            (by unfold rtMaxObjBytes at hmax; omega)
          rw [show o + 8#64 + BitVec.ofNat 64 8 = o + 16#64 by rw [ptr_add_nat_p],
            show 8 + (bytes - 16) = bytes - 8 by omega] at hsp1
          have hsp2 := region_split (a := o + 16#64) (n1 := 8) (n2 := bytes - 24)
            (by unfold rtMaxObjBytes at hmax; omega)
          rw [show o + 16#64 + BitVec.ofNat 64 8 = o + 24#64 by rw [ptr_add_nat_p],
            show 8 + (bytes - 24) = bytes - 16 by omega] at hsp2
          have h1 : (region (o + 8#64) 8 ⋆ (region (o + 16#64) 8 ⋆ region (o + 24#64) (bytes - 24))) m :=
            sep_mono_r (Q' := region (o + 16#64) 8 ⋆ region (o + 24#64) (bytes - 24))
              (fun _ hr => hsp2 ▸ hr) (hsp1 ▸ hmem)
          obtain ⟨m1, m2, rfl, hd, hr8, hr16⟩ := h1
          obtain ⟨v8, hc8⟩ := region_to_cell64 hr8
          have h1a : (cell64 (o + 8#64) v8 ⋆ (region (o + 16#64) 8 ⋆ region (o + 24#64) (bytes - 24)))
              (m1.union m2) := ⟨m1, m2, rfl, hd, hc8, hr16⟩
          have h2 : (region (o + 16#64) 8 ⋆ (cell64 (o + 8#64) v8 ⋆ region (o + 24#64) (bytes - 24)))
              (m1.union m2) :=
            sep_cast h1a (by ac_rfl)
          obtain ⟨m3, m4, heq, hd2, hr16', hrest⟩ := h2
          obtain ⟨v16, hc16⟩ := region_to_cell64 hr16'
          have h3 : (cell64 (o + 16#64) v16 ⋆ (cell64 (o + 8#64) v8 ⋆ region (o + 24#64) (bytes - 24)))
              (m3.union m4) := ⟨m3, m4, rfl, hd2, hc16, hrest⟩
          have hfin : ((cell64 (o + 8#64) v8 ⋆ cell64 (o + 16#64) v16) ⋆
              region (o + 24#64) (bytes - 24)) (m1.union m2) :=
            heq ▸ sep_cast h3 (by ac_rfl)
          exact ⟨v8, v16, hfin⟩

private theorem free_obj_pull_body {C0' H1 Body R : Mem 64 → Prop} {m : Mem 64}
    (h : (C0' ⋆ (H1 ⋆ (Body ⋆ R))) m) :
    (Body ⋆ (C0' ⋆ (H1 ⋆ R))) m :=
  sep_cast h (by ac_rfl)

private theorem free_obj_prep_small_from_body {C8 R16 C0' H1 H2 H3 H4 H5 H6 H7 H8 R :
      Mem 64 → Prop} {m : Mem 64}
    (h : ((C8 ⋆ R16) ⋆ (C0' ⋆ ((H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H7 ⋆ H8) ⋆ R))) m) :
    (H3 ⋆ (C8 ⋆ (C0' ⋆ (H4 ⋆ (H1 ⋆ (H2 ⋆ (H5 ⋆ (H6 ⋆ (H7 ⋆ (H8 ⋆ (R16 ⋆ R))))))))))) m :=
  sep_cast h (by ac_rfl)

private theorem free_obj_prep_large_from_body {C8 C16 R24 C0' H1 H2 H3 H4 H5 H6 H7 H8 R :
      Mem 64 → Prop} {m : Mem 64}
    (h : (((C8 ⋆ C16) ⋆ R24) ⋆ (C0' ⋆ ((H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H7 ⋆ H8) ⋆ R))) m) :
    (H4 ⋆ (C8 ⋆ (C16 ⋆ (C0' ⋆ (H1 ⋆ (H2 ⋆ (H3 ⋆ (H5 ⋆ (H6 ⋆ (H7 ⋆ (H8 ⋆ (R24 ⋆ R)))))))))))) m :=
  sep_cast h (by ac_rfl)

private theorem free_obj_pull_largeList_pre {H4 C8 C16 C0 H1 H2 H3 H5 H6 H7 H8 Rest :
      Mem 64 → Prop} {m : Mem 64}
    (h : (H4 ⋆ (C8 ⋆ (C16 ⋆ (C0 ⋆ (H1 ⋆ (H2 ⋆ (H3 ⋆ (H5 ⋆ (H6 ⋆ (H7 ⋆ (H8 ⋆ Rest))))))))))) m) :
    (H7 ⋆ (H4 ⋆ (C8 ⋆ (C16 ⋆ (C0 ⋆ (H1 ⋆ (H2 ⋆ (H3 ⋆ (H5 ⋆ (H6 ⋆ (H8 ⋆ Rest))))))))))) m :=
  sep_cast h (by ac_rfl)

private theorem free_obj_restore_largeList_pre {H7 H4 C8 C16 C0 H1 H2 H3 H5 H6 H8 Rest :
      Mem 64 → Prop} {m : Mem 64}
    (h : (H7 ⋆ (H4 ⋆ (C8 ⋆ (C16 ⋆ (C0 ⋆ (H1 ⋆ (H2 ⋆ (H3 ⋆ (H5 ⋆ (H6 ⋆ (H8 ⋆ Rest))))))))))) m) :
    (H4 ⋆ (C8 ⋆ (C16 ⋆ (C0 ⋆ (H1 ⋆ (H2 ⋆ (H3 ⋆ (H5 ⋆ (H6 ⋆ (H7 ⋆ (H8 ⋆ Rest))))))))))) m :=
  sep_cast h (by ac_rfl)

private theorem bv64_tag_eq (hdr : BitVec 64) {t : Nat} (ht : t < 256)
    (h : (hdr >>> 56).toNat = t) :
    (hdr >>> BitVec.signExtend 64 56#32 == BitVec.ofNat 64 t) = true := by
  have hse : BitVec.signExtend 64 56#32 = 56#64 := by decide
  rw [hse, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  have hsh : (hdr >>> 56#64).toNat = (hdr >>> 56).toNat := by
    simp [BitVec.toNat_ushiftRight]
  rw [hsh, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem bv64_tag_ne (hdr : BitVec 64) {t : Nat} (ht : t < 256)
    (h : (hdr >>> 56).toNat ≠ t) :
    (hdr >>> BitVec.signExtend 64 56#32 == BitVec.ofNat 64 t) = false := by
  have hse : BitVec.signExtend 64 56#32 = 56#64 := by decide
  rw [hse, beq_eq_false_iff_ne]
  intro heq
  apply h
  have := congrArg BitVec.toNat heq
  simp [BitVec.toNat_ushiftRight, Nat.mod_eq_of_lt (by omega : t < 2 ^ 64)] at this
  exact this

private theorem bv64_shr3_toNat (bytes : Nat) (hb : bytes < 2 ^ 64) :
    (BitVec.ofNat 64 bytes >>> 3#64).toNat = bytes / 8 := by
  simp [BitVec.toNat_ushiftRight, Nat.mod_eq_of_lt hb, Nat.shiftRight_eq_div_pow]

private theorem bv64_natTag_eq (hdr : BitVec 64) {t : Nat} (ht : t < 256)
    (h : (hdr >>> 56).toNat = t) :
    decide (hdr >>> 56 = BitVec.ofNat 64 t) = true := by
  rw [decide_eq_true_iff]
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem bv64_natTag_ne (hdr : BitVec 64) {t : Nat} (ht : t < 256)
    (h : (hdr >>> 56).toNat ≠ t) :
    decide (hdr >>> 56 = BitVec.ofNat 64 t) = false := by
  rw [decide_eq_false_iff_not]
  intro heq
  apply h
  have := congrArg BitVec.toNat heq
  simpa [Nat.mod_eq_of_lt (by omega : t < 2 ^ 64)] using this

private theorem sep_swap12 {A B Rest : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ Rest)) m) : (B ⋆ (A ⋆ Rest)) m :=
  sep_cast h (by ac_rfl)

private theorem sep_rot23 {A B C Rest : Mem 64 → Prop} {m : Mem 64}
    (h : (B ⋆ (A ⋆ (C ⋆ Rest))) m) : (C ⋆ (A ⋆ (B ⋆ Rest))) m :=
  sep_cast h (by ac_rfl)

private theorem sep_unrot23 {A B C Rest : Mem 64 → Prop} {m : Mem 64}
    (h : (C ⋆ (A ⋆ (B ⋆ Rest))) m) : (A ⋆ (B ⋆ (C ⋆ Rest))) m :=
  sep_cast h (by ac_rfl)

theorem lcnf_free_obj_wp (Γ : Env) :
    ∀ (xs : Tup Val lcnf_free_obj.as) (m : Mem 64) (Q : Post lcnf_free_obj.rs) (X : XPost),
      lcnfFreeObjSpec xs m Q X → Func.wp Γ lcnf_free_obj.body xs m Q X := by
  dsimp [lcnf_free_obj]
  intro xs m Q X hspec
  rcases xs with ⟨rt, o, ⟨⟩⟩
  dsimp [lcnfFreeObjSpec] at hspec
  split at hspec
  · rename_i hodd
    rcases hspec with ⟨st, R, hm, hQ⟩
    dsimp [Func.wp, lcnf_free_obj_body]
    c0_steps
    exact hQ
  · rename_i _heven
    rcases hspec with ⟨st, hdr, bytes, R, hoNz, hoAl, hmin, hmax, hmod, hm, hQ⟩
    dsimp [Func.wp, lcnf_free_obj_body]
    c0_steps
    have hmLoad : (cell64 o hdr ⋆ (rtC0Inv rt st ⋆ (freeObjBody o bytes hdr ⋆ R))) m :=
      free_obj_pull_cell0
        (sep_mono (fun _ hm' => sep_mono_r (Q' := cell64 o hdr ⋆ freeObjBody o bytes hdr)
          (fun _ hf => freeObjLayout_to_cell_body hf) hm') hm)
    refine wp_load_cell64 hmLoad ?_
    c0_step
    · clear hmLoad
      let FreePost : Tup Val [i64] → Mem 64 → Prop := fun xs m' =>
        xs.fst = BitVec.ofNat 64 bytes ∧
        (rtC0Inv rt st ⋆ freeObjLayout o bytes hdr ⋆ R) m'
      refine wp_join_group FreePost ?_ ?_
      · intro _ xs m1 ⟨hBy, hm1⟩
        rcases xs with ⟨bytesBV, ⟨⟩⟩
        dsimp at hBy
        subst hBy
        refine wp_join_group (fun _ _ => False) (fun _ _ _ h => h.elim) ?_
        intro Jpanic hJpanic
        c0_steps
        · refine hJpanic () m1 ?_
          exfalso
          have h7 : ((BitVec.ofNat 64 bytes) &&& 7#64) = 0#64 := by
            apply BitVec.eq_of_toNat_eq
            have hb : bytes < 2 ^ 64 := by unfold rtMaxObjBytes at hmax; omega
            rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
            have h7m : (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 := by decide
            have h0m : (0#64).toNat = 0 := by decide
            rw [h7m, Nat.and_two_pow_sub_one_eq_mod, h0m]
            exact hmod
          have hnot7 : ¬ BitVec.ofNat 64 bytes &&& 7#64 = 0#64 := by assumption
          exact hnot7 h7
        · refine hJpanic () m1 ?_
          exfalso
          unfold rtMinObjBytes at hmin; unfold rtMaxObjBytes at hmax; omega
        · refine hJpanic () m1 ?_
          exfalso
          unfold rtMaxObjBytes at hmax; omega
        · clear hJpanic Jpanic
          have hm0 : (cell64 o hdr ⋆ (rtC0Inv rt st ⋆ (freeObjBody o bytes hdr ⋆ R))) m1 :=
            free_obj_pull_cell0
              (sep_mono (fun _ hm' => sep_mono_r (Q' := cell64 o hdr ⋆ freeObjBody o bytes hdr)
                (fun _ hf => freeObjLayout_to_cell_body hf) hm') hm1)
          clear hm1
          refine wp_store_cell64 hm0 ?_
          intro m1' hm1'
          clear hm0
          let EpiPost : Tup Val [] → Mem 64 → Prop := fun _ m2 =>
            ∃ stTmp : RtC0State, stTmp.PreservesMeta st ∧ stTmp.rem = st.rem ∧
              stTmp.workBuf = st.workBuf ∧ (rtC0Inv rt stTmp ⋆ R) m2
          refine wp_join_group EpiPost ?_ ?_
          · intro _ ⟨⟩ m2 ⟨stTmp, hMeta, hRem, hWb, hmem⟩
            unfold rtC0Inv at hmem
            have hHdr := free_obj_pull_hdr hmem
            clear hmem
            dsimp [Blocks.get]
            c0_steps
            refine wp_load_of (LcnfC0Rt.load_s_st_frees hHdr) ?_
            c0_steps
            refine wp_store_sep (LcnfC0Rt.store_s_st_frees _ hHdr) ?_
            intro m2a hm2a
            clear hHdr
            c0_steps
            refine wp_load_of (LcnfC0Rt.load_s_st_live hm2a) ?_
            c0_steps
            refine wp_store_sep (LcnfC0Rt.store_s_st_live _ hm2a) ?_
            intro m2b hm2b
            clear hm2a
            c0_steps
            refine hQ stTmp.withFreeStats m2b
              ⟨hMeta.1, hMeta.2.1, hMeta.2.2.1, hMeta.2.2.2.1, hMeta.2.2.2.2.1,
                hMeta.2.2.2.2.2.1, hMeta.2.2.2.2.2.2.1, hMeta.2.2.2.2.2.2.2.1,
                hMeta.2.2.2.2.2.2.2.2⟩ hRem hWb ?_
            unfold rtC0Inv
            exact free_obj_back_hdr hm2b
          · intro Jepi hJepi
            have hBody := free_obj_pull_body ‹_›
            by_cases hsmall : bytes / 8 < 64
            · obtain ⟨mB, mRest, rfl, hdB, hB, hRest⟩ := hBody
              obtain ⟨v8, hsp8⟩ := freeObjBody_split_small hmin hmax hB
              have hmSm0 : ((cell64 (o + 8#64) v8 ⋆ region (o + 16#64) (bytes - 16)) ⋆
                  (cell64 o 0#64 ⋆ (rtC0Inv rt st ⋆ R))) (mB.union mRest) :=
                ⟨mB, mRest, rfl, hdB, hsp8, hRest⟩
              unfold rtC0Inv at hmSm0
              have hmSm := free_obj_prep_small_from_body hmSm0
              clear hmSm0 hB hsp8 hRest hdB
              have hb : bytes < 2 ^ 64 := by unfold rtMaxObjBytes at hmax; omega
              have hclsLtBV : BitVec.ult (BitVec.ofNat 64 bytes >>> (3 : Nat)) 64#64 = true := by
                simp [BitVec.ult, Nat.mod_eq_of_lt hb, Nat.shiftRight_eq_div_pow]; omega
              have hclsIdxNat : (BitVec.ofNat 64 bytes >>> (3 : Nat)).toNat = bytes / 8 := by
                simp [BitVec.toNat_ushiftRight, Nat.mod_eq_of_lt hb, Nat.shiftRight_eq_div_pow]
              refine wp_let_cmp CmpOp.ult i64 rfl _ _ _ rfl ?_
              dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
              constructor
              · intro _hc
                c0_steps
                have haddr : (rt + 33024#64) + (BitVec.ofNat 64 bytes >>> 3) * 8#64 =
                    (rt + 33024#64) + BitVec.ofNat 64 (8 * (bytes / 8)) := by
                  congr 1
                  apply BitVec.eq_of_toNat_eq
                  have h8 : (8#64).toNat = 8 := by decide
                  rw [BitVec.toNat_mul, h8, hclsIdxNat, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega), Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]
                have hlen : bytes / 8 < st.freeList.length := by rw [st.freeListLen]; exact hsmall
                refine wp_load_array64 haddr hlen hmSm ?_
                have hmSmC := sep_swap12 hmSm
                clear hmSm
                refine wp_store_cell64 hmSmC ?_
                intro m2 hm2
                clear hmSmC
                c0_steps
                have hm2A := sep_swap12 hm2
                clear hm2
                refine wp_store_array64 haddr hlen hm2A ?_
                intro m3 hm3
                clear hm2A
                c0_steps
                have hget : st.freeList[bytes / 8] = st.freeList.getD (bytes / 8) 0#64 := by
                  simp [List.getD_eq_getElem?_getD, hlen]
                dsimp [Arg.val] at hm3
                rw [hget] at hm3
                refine hJepi () m3 ⟨st.withFreeSmall (bytes / 8) o,
                  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, ?_⟩
                exact free_obj_post_small_finish hoNz hoAl hmin hmax hmod hsmall rfl hm3
              · intro hc
                exfalso
                rw [hclsLtBV] at hc
                contradiction
            · have h512 : 512 ≤ bytes := by omega
              obtain ⟨mB, mRest, rfl, hdB, hB, hRest⟩ := hBody
              obtain ⟨v8, v16, hspLg⟩ := freeObjBody_split_large (by omega) hmax hB
              have hmLg0 : (((cell64 (o + 8#64) v8 ⋆ cell64 (o + 16#64) v16) ⋆ region (o + 24#64) (bytes - 24)) ⋆
                  (cell64 o 0#64 ⋆ (rtC0Inv rt st ⋆ R))) (mB.union mRest) :=
                ⟨mB, mRest, rfl, hdB, hspLg, hRest⟩
              unfold rtC0Inv at hmLg0
              have hmLg1 := free_obj_prep_large_from_body hmLg0
              have hmLgPull := free_obj_pull_largeList_pre hmLg1
              have hOldHd : st.hdr.s_large_free = largeSegNext 0#64 st.largeNodes := by
                obtain ⟨_, _, _, _, hLF, _⟩ := hmLgPull
                exact largeSeg_hd_eq_next hLF
              have hmLg := free_obj_restore_largeList_pre hmLgPull
              clear hmLg0 hmLg1 hmLgPull hB hspLg hRest hdB
              have hb : bytes < 2 ^ 64 := by unfold rtMaxObjBytes at hmax; omega
              have hnotSmall : BitVec.ult (BitVec.ofNat 64 bytes >>> (3 : Nat)) 64#64 = false := by
                simp [BitVec.ult, Nat.mod_eq_of_lt hb, Nat.shiftRight_eq_div_pow]; omega
              refine wp_let_cmp CmpOp.ult i64 rfl _ _ _ rfl ?_
              dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
              constructor
              · intro hc; exfalso; rw [hnotSmall] at hc; contradiction
              · intro _hc
                c0_steps
                refine wp_load_of (LcnfC0Rt.load_s_large_free hmLg) ?_
                have hmLgC8 := sep_swap12 hmLg
                clear hmLg
                refine wp_store_cell64 hmLgC8 ?_
                intro m2 hm2
                clear hmLgC8
                c0_steps
                have hm2C16 := sep_rot23 hm2
                clear hm2
                refine wp_store_cell64 hm2C16 ?_
                intro m3 hm3
                clear hm2C16
                c0_steps
                have hm3Hdr := sep_unrot23 hm3
                clear hm3
                refine wp_store_sep (LcnfC0Rt.store_s_large_free o hm3Hdr) ?_
                intro m4 hm4
                clear hm3Hdr
                c0_steps
                refine hJepi () m4 ⟨st.withFreeLarge o bytes,
                  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, ?_⟩
                exact free_obj_post_large_finish hoNz hoAl h512 hmax hmod hOldHd hm4
      · intro Jsw hJsw
        by_cases ht246 : (hdr >>> 56).toNat = arrayTag
        · have hcond : decide (hdr >>> 56 = 246#64) = true :=
            bv64_natTag_eq hdr (by decide) ht246
          obtain ⟨mAF, mR, rfl, hdR, ⟨mA, mF, rfl, hdF, hA, hLay⟩, hR⟩ := hm
          have hLay' := hLay
          unfold freeObjLayout at hLay'
          rw [ite_eq_left ht246] at hLay'
          rcases hLay' with ⟨w16, hw1, hby, hmem⟩
          have hLoad := free_obj_put_tag246 ⟨mA.union mF, mR, rfl, hdR, ⟨mA, mF, rfl, hdF, hA, hmem⟩, hR⟩
          have hmKeep : (rtC0Inv rt st ⋆ freeObjLayout o bytes hdr ⋆ R) ((mA.union mF).union mR) :=
            ⟨mA.union mF, mR, rfl, hdR, ⟨mA, mF, rfl, hdF, hA, hLay⟩, hR⟩
          refine wp_let_cmp CmpOp.eq i64 rfl _ _ _ rfl ?_
          dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
          constructor
          · intro _hc
            c0_step
            refine wp_load_cell64 hLoad ?_
            refine wp_let_cmp CmpOp.ugt i64 rfl _ _ _ rfl ?_
            dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
            constructor
            · intro hc
              exfalso
              have hle : ¬ BitVec.ult 33554428#64 w16 = true := by simp [BitVec.ult]; omega
              exact hle hc
            · intro _hc
              clear hLoad
              c0_steps
              have hEq : 24#64 + 8#64 * w16 = BitVec.ofNat 64 bytes := by
                apply BitVec.eq_of_toNat_eq
                have hlt : bytes < 2 ^ 64 := by unfold rtMaxObjBytes at hmax; omega
                have h8m : (8 : Nat) % 2 ^ 64 = 8 := by decide
                have h24m : (24 : Nat) % 2 ^ 64 = 24 := by decide
                simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
                  h8m, h24m, Nat.mod_eq_of_lt hlt]
                omega
              exact hJsw _ _ ⟨hEq, hmKeep⟩
          · intro hc; exfalso; rw [hcond] at hc; contradiction
        · have hnot246 : decide (hdr >>> 56 = 246#64) = false :=
            bv64_natTag_ne hdr (by decide) ht246
          refine wp_let_cmp CmpOp.eq i64 rfl _ _ _ rfl ?_
          dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
          constructor
          · intro hc; exfalso; rw [hnot246] at hc; contradiction
          · intro _hc
            refine wp_join_group FreePost
              (fun _ xs m' h => by rcases xs with ⟨v, ⟨⟩⟩; exact hJsw (v, ()) m' h) ?_
            intro _ hJsw
            by_cases ht248 : (hdr >>> 56).toNat = sarrayTag
            · have hcond : decide (hdr >>> 56 = 248#64) = true :=
                bv64_natTag_eq hdr (by decide) ht248
              obtain ⟨mAF, mR, rfl, hdR, ⟨mA, mF, rfl, hdF, hA, hLay⟩, hR⟩ := hm
              have hLay' := hLay
              unfold freeObjLayout at hLay'
              rw [ite_eq_right ht246, ite_eq_left ht248] at hLay'
              rcases hLay' with ⟨w16, hw1, hby, hmem⟩
              have hLoad := free_obj_put_tag246 ⟨mA.union mF, mR, rfl, hdR, ⟨mA, mF, rfl, hdF, hA, hmem⟩, hR⟩
              have hmKeep : (rtC0Inv rt st ⋆ freeObjLayout o bytes hdr ⋆ R) ((mA.union mF).union mR) :=
                ⟨mA.union mF, mR, rfl, hdR, ⟨mA, mF, rfl, hdF, hA, hLay⟩, hR⟩
              refine wp_let_cmp CmpOp.eq i64 rfl _ _ _ rfl ?_
              dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
              constructor
              · intro _hc
                c0_step
                refine wp_load_cell64 hLoad ?_
                refine wp_let_cmp CmpOp.ugt i64 rfl _ _ _ rfl ?_
                dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
                constructor
                · intro hc
                  exfalso
                  have hle : ¬ BitVec.ult 268435455#64 w16 = true := by simp [BitVec.ult]; omega
                  exact hle hc
                · intro _hc
                  clear hLoad
                  c0_steps
                  have hbd : (hdr >>> 48).toNat % 128 * w16.toNat ≤ 127 * 268435455 :=
                    Nat.mul_le_mul (by omega) hw1
                  have hesz : ((hdr >>> 48 &&& 127#64) * w16 + 24#64) =
                      BitVec.ofNat 64 (24 + (hdr >>> 48).toNat % 128 * w16.toNat) := by
                    apply BitVec.eq_of_toNat_eq
                    have hlt48 : (hdr >>> 48 &&& 127#64).toNat = (hdr >>> 48).toNat % 128 := by
                      rw [BitVec.toNat_and]
                      have h127 : (127#64).toNat = 2 ^ 7 - 1 := by decide
                      rw [h127, Nat.and_two_pow_sub_one_eq_mod]
                    have hlt : 24 + (hdr >>> 48).toNat % 128 * w16.toNat < 2 ^ 64 := by omega
                    have h24m : (24 : Nat) % 2 ^ 64 = 24 := by decide
                    have hmul : (hdr >>> 48).toNat % 128 * w16.toNat < 2 ^ 64 := by omega
                    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
                      hlt48, h24m, Nat.mod_eq_of_lt hmul, Nat.mod_eq_of_lt hlt]
                    omega
                  have hEq :
                      ((24#64 + ((hdr >>> 48 &&& 127#64) * w16)) + 7#64) &&&
                        18446744073709551608#64 = BitVec.ofNat 64 bytes := by
                    rw [show (24#64 + ((hdr >>> 48 &&& 127#64) * w16)) =
                        ((hdr >>> 48 &&& 127#64) * w16 + 24#64) by ac_rfl]
                    rw [hesz, hby]
                    exact bv64_align8_eq (by omega)
                  exact hJsw _ _ ⟨hEq, hmKeep⟩
              · intro hc; exfalso; rw [hcond] at hc; contradiction
            · have hnot248 : decide (hdr >>> 56 = 248#64) = false :=
                bv64_natTag_ne hdr (by decide) ht248
              refine wp_let_cmp CmpOp.eq i64 rfl _ _ _ rfl ?_
              dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
              constructor
              · intro hc; exfalso; rw [hnot248] at hc; contradiction
              · intro _hc
                refine wp_join_group FreePost
                  (fun _ xs m' h => by rcases xs with ⟨v, ⟨⟩⟩; exact hJsw (v, ()) m' h) ?_
                intro _ hJsw
                by_cases ht249 : (hdr >>> 56).toNat = stringTag
                · have hcond : decide (hdr >>> 56 = 249#64) = true :=
                    bv64_natTag_eq hdr (by decide) ht249
                  obtain ⟨mAF, mR, rfl, hdR, ⟨mA, mF, rfl, hdF, hA, hLay⟩, hR⟩ := hm
                  have hLay' := hLay
                  unfold freeObjLayout at hLay'
                  rw [ite_eq_right ht246, ite_eq_right ht248, ite_eq_left ht249] at hLay'
                  rcases hLay' with ⟨w16, hw1, hby, hmem⟩
                  have hLoad := free_obj_put_tag246 ⟨mA.union mF, mR, rfl, hdR, ⟨mA, mF, rfl, hdF, hA, hmem⟩, hR⟩
                  have hmKeep : (rtC0Inv rt st ⋆ freeObjLayout o bytes hdr ⋆ R) ((mA.union mF).union mR) :=
                    ⟨mA.union mF, mR, rfl, hdR, ⟨mA, mF, rfl, hdF, hA, hLay⟩, hR⟩
                  refine wp_let_cmp CmpOp.eq i64 rfl _ _ _ rfl ?_
                  dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
                  constructor
                  · intro _hc
                    c0_step
                    refine wp_load_cell64 hLoad ?_
                    refine wp_let_cmp CmpOp.ugt i64 rfl _ _ _ rfl ?_
                    dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
                    constructor
                    · intro hc
                      exfalso
                      have hle : ¬ BitVec.ult 268435415#64 w16 = true := by simp [BitVec.ult]; omega
                      exact hle hc
                    · intro _hc
                      clear hLoad
                      c0_steps
                      have h32 : 32#64 + w16 = BitVec.ofNat 64 (32 + w16.toNat) := by
                        apply BitVec.eq_of_toNat_eq
                        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
                      have hEq : ((32#64 + w16) + 7#64) &&& 18446744073709551608#64 =
                          BitVec.ofNat 64 bytes := by
                        rw [h32, hby]
                        exact bv64_align8_eq (by omega)
                      exact hJsw _ _ ⟨hEq, hmKeep⟩
                  · intro hc; exfalso; rw [hcond] at hc; contradiction
                · have hnot249 : decide (hdr >>> 56 = 249#64) = false :=
                    bv64_natTag_ne hdr (by decide) ht249
                  refine wp_let_cmp CmpOp.eq i64 rfl _ _ _ rfl ?_
                  dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
                  constructor
                  · intro hc; exfalso; rw [hnot249] at hc; contradiction
                  · intro _hc
                    refine wp_join_group FreePost
                      (fun _ xs m' h => by rcases xs with ⟨v, ⟨⟩⟩; exact hJsw (v, ()) m' h) ?_
                    intro _ hJsw
                    by_cases ht250 : (hdr >>> 56).toNat = mpzTag
                    · have hcond : decide (hdr >>> 56 = 250#64) = true :=
                        bv64_natTag_eq hdr (by decide) ht250
                      obtain ⟨mAF, mR, rfl, hdR, ⟨mA, mF, rfl, hdF, hA, hLay⟩, hR⟩ := hm
                      have hLay' := hLay
                      unfold freeObjLayout at hLay'
                      rw [ite_eq_right ht246, ite_eq_right ht248, ite_eq_right ht249,
                        ite_eq_left ht250] at hLay'
                      rcases hLay' with ⟨w8, hw1, hby, hmem⟩
                      have hLoad := free_obj_put_tag250 ⟨mA.union mF, mR, rfl, hdR, ⟨mA, mF, rfl, hdF, hA, hmem⟩, hR⟩
                      have hmKeep : (rtC0Inv rt st ⋆ freeObjLayout o bytes hdr ⋆ R) ((mA.union mF).union mR) :=
                        ⟨mA.union mF, mR, rfl, hdR, ⟨mA, mF, rfl, hdF, hA, hLay⟩, hR⟩
                      refine wp_let_cmp CmpOp.eq i64 rfl _ _ _ rfl ?_
                      dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
                      constructor
                      · intro _hc
                        c0_step
                        refine wp_load_cell64 hLoad ?_
                        rw [wp_let_and_eq i64]
                        dsimp [lift2, Arg.val]
                        refine wp_let_cmp CmpOp.ugt i64 rfl _ _ _ rfl ?_
                        dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
                        constructor
                        · intro hc
                          exfalso
                          have hle : ¬ BitVec.ult 33554429#64 (w8 &&& 4294967295#64) = true := by
                            unfold BitVec.ult; rw [decide_eq_true_iff]
                            have h33 : (33554429#64).toNat = 33554429 := by decide
                            rw [h33]; omega
                          exact hle hc
                        · intro _hc
                          clear hLoad
                          c0_steps
                          have hEq : 16#64 + 8#64 * (w8 &&& 4294967295#64) = BitVec.ofNat 64 bytes := by
                            apply BitVec.eq_of_toNat_eq
                            have hlt : bytes < 2 ^ 64 := by unfold rtMaxObjBytes at hmax; omega
                            have hmask : (w8 &&& 4294967295#64).toNat = w8.toNat &&& 4294967295 := by
                              rw [BitVec.toNat_and]; rfl
                            have h8m : (8 : Nat) % 2 ^ 64 = 8 := by decide
                            have h16m : (16 : Nat) % 2 ^ 64 = 16 := by decide
                            simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
                              h8m, h16m, hmask, Nat.mod_eq_of_lt hlt]
                            omega
                          exact hJsw _ _ ⟨hEq, hmKeep⟩
                      · intro hc; exfalso; rw [hcond] at hc; contradiction
                    · have hnot250 : decide (hdr >>> 56 = 250#64) = false :=
                        bv64_natTag_ne hdr (by decide) ht250
                      obtain ⟨mAF, mR, rfl, hdR, ⟨mA, mF, rfl, hdF, hA, hLay⟩, hR⟩ := hm
                      have hLay' := hLay
                      unfold freeObjLayout at hLay'
                      rw [ite_eq_right ht246, ite_eq_right ht248, ite_eq_right ht249,
                        ite_eq_right ht250] at hLay'
                      have hby := hLay'.1
                      have hmKeep : (rtC0Inv rt st ⋆ freeObjLayout o bytes hdr ⋆ R) ((mA.union mF).union mR) :=
                        ⟨mA.union mF, mR, rfl, hdR, ⟨mA, mF, rfl, hdF, hA, hLay⟩, hR⟩
                      refine wp_let_cmp CmpOp.eq i64 rfl _ _ _ rfl ?_
                      dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
                      constructor
                      · intro hc; exfalso; rw [hnot250] at hc; contradiction
                      · intro _hc
                        c0_steps
                        have hEq : (hdr >>> 32 &&& 65535#64) = BitVec.ofNat 64 bytes := by
                          apply BitVec.eq_of_toNat_eq
                          have hlt : bytes < 2 ^ 64 := by unfold rtMaxObjBytes at hmax; omega
                          rw [hby, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
                        exact hJsw _ _ ⟨hEq, hmKeep⟩

/-! ## 4. Helpers & Soundness Proof for `lcnf_clo_under` -/

private theorem cell64_conflict (a v1 v2 : BitVec 64) (R1 R2 : Mem 64 → Prop) (m : Mem 64)
    (h : ((cell64 a v1 ⋆ R1) ⋆ (cell64 a v2 ⋆ R2)) m) : False := by
  obtain ⟨m1, m2, rfl, hd, h1, h2⟩ := h
  have hl1 : loadVal m1 i64 a = some v1 := loadVal_cell64 h1
  have hl2 : loadVal m2 i64 a = some v2 := loadVal_cell64 h2
  have ha1 : a ∈ m1 := by
    by_cases ha : a ∈ m1
    · exact ha
    · exfalso
      have hnone : Std.ExtHashMap.get? m1 (a + BitVec.ofNat 64 0) = none := by
        rw [BitVec.add_zero]
        exact Std.ExtHashMap.getElem?_eq_none ha
      have := loadVal_of_unmapped m1 i64 a ⟨0, by decide, hnone⟩
      rw [this] at hl1; contradiction
  have ha2 : a ∈ m2 := by
    by_cases ha : a ∈ m2
    · exact ha
    · exfalso
      have hnone : Std.ExtHashMap.get? m2 (a + BitVec.ofNat 64 0) = none := by
        rw [BitVec.add_zero]
        exact Std.ExtHashMap.getElem?_eq_none ha
      have := loadVal_of_unmapped m2 i64 a ⟨0, by decide, hnone⟩
      rw [this] at hl2; contradiction
  have hmem : a ∈ m1.inter m2 := Std.ExtHashMap.mem_inter_iff.mpr ⟨ha1, ha2⟩
  rw [hd] at hmem
  exact (Std.ExtHashMap.not_mem_empty (a := a)) hmem

private def lcnfObjBody (o : LcnfObj) : Mem 64 → Prop :=
  if o.tag = closureTag then
    cell64 (o.addr + 8#64) o.funId ⋆ cell64 (o.addr + 16#64) o.cloMeta ⋆
      array64 (o.addr + 24#64) o.fields ⋆
      region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length)) (o.csSz - (24 + 8 * o.fields.length))
  else if o.tag = arrayTag then
    cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.fields.length) ⋆
      cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
      array64 (o.addr + 24#64) o.fields ⋆
      region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length)) (8 * (o.cap - o.fields.length))
  else if o.tag = sarrayTag then
    cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.arrSize) ⋆
      cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
      bytes (o.addr + 24#64) o.scalarData ⋆
      region (o.addr + BitVec.ofNat 64 (24 + o.scalarData.length)) (o.totalBytes - (24 + o.scalarData.length))
  else if o.tag = stringTag then
    cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.arrSize) ⋆
      cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
      cell64 (o.addr + 24#64) (BitVec.ofNat 64 o.strLen) ⋆
      bytes (o.addr + 32#64) o.scalarData ⋆
      region (o.addr + BitVec.ofNat 64 (32 + o.scalarData.length)) (o.totalBytes - (32 + o.scalarData.length))
  else if o.tag = mpzTag then
    cell64 (o.addr + 8#64) o.mpzMeta ⋆ array64 (o.addr + 16#64) o.limbs
  else
    have soff := 8 + 8 * o.fields.length;
    array64 (o.addr + 8#64) o.fields ⋆
      bytes (o.addr + BitVec.ofNat 64 soff) o.scalarData ⋆
      region (o.addr + BitVec.ofNat 64 (soff + o.scalarData.length)) (o.csSz - (soff + o.scalarData.length))

private theorem lcnfObjMem_eq_header_body (o : LcnfObj) :
    lcnfObjMem o = cell64 o.addr o.header ⋆ lcnfObjBody o := by
  unfold lcnfObjMem lcnfObjBody
  split
  · ac_rfl
  · split
    · ac_rfl
    · split
      · ac_rfl
      · split
        · ac_rfl
        · split
          · ac_rfl
          · dsimp only; ac_rfl

private theorem lcnfObjBody_withRc (o : LcnfObj) (rc' : BitVec 32) :
    lcnfObjBody (o.withRc rc') = lcnfObjBody o := by
  unfold lcnfObjBody LcnfObj.withRc LcnfObj.cloMeta LcnfObj.mpzMeta LcnfObj.totalBytes
  rfl

private theorem lcnfObjWf_withRc {o : LcnfObj} {rc' : BitVec 32}
    (h : o.Wf) (hrc : 0 ≤ rc'.toInt) : (o.withRc rc').Wf := by
  unfold LcnfObj.Wf LcnfObj.totalBytes at h ⊢
  dsimp [LcnfObj.withRc] at *
  rcases h with ⟨h1, h2, _, h4, h5, h6, h7, h8, h9, hrest⟩
  exact ⟨h1, h2, hrc, h4, h5, h6, h7, h8, h9, hrest⟩

private theorem bv32_ofNat_and_hi_zero (rc : Nat) (hrc : rc < 2 ^ 32) (hi : BitVec 64)
    (hlo : (hi &&& 4294967295#64) = 0#64) :
    BitVec.ofNat 64 rc &&& hi = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi64
  rw [BitVec.getLsbD_and, BitVec.getLsbD_zero]
  by_cases hi32 : i < 32
  · have hget := congrArg (fun bv : BitVec 64 => bv.getLsbD i) hlo
    rw [BitVec.getLsbD_and, BitVec.getLsbD_zero] at hget
    have hmask : (4294967295#64).getLsbD i = true := by
      rw [BitVec.getLsbD_ofNat, show (4294967295 : Nat) = 2 ^ 32 - 1 by decide,
        Nat.testBit_two_pow_sub_one]
      simp [hi64, hi32]
    rw [hmask, Bool.and_true] at hget
    rw [hget, Bool.and_false]
  · have : (BitVec.ofNat 64 rc).getLsbD i = false := by
      rw [BitVec.getLsbD_ofNat]
      simp [hi64]
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hrc (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [this, Bool.false_and]

private theorem obj_hi_lo_zero (o : LcnfObj)
    (hcs : o.csSz < 65536) (hoth : o.other < 256) (ht : o.tag < 256) :
    ((o.withRc 0#32).header &&& 4294967295#64) = 0#64 := by
  have hc : (o.withRc 0#32).header &&& 18446744069414584320#64 = (o.withRc 0#32).header := by
    simpa [LcnfObj.withRc] using LcnfObj.header_clear_rc (o.withRc 0#32) hcs hoth ht
  rw [← hc, BitVec.and_assoc]
  have hz : (18446744069414584320#64 &&& 4294967295#64) = 0#64 := by decide
  rw [hz, BitVec.and_zero]

private theorem obj_header_eq_add (o : LcnfObj)
    (hcs : o.csSz < 65536) (hoth : o.other < 256) (ht : o.tag < 256) :
    o.header = BitVec.ofNat 64 o.rc.toNat + (o.withRc 0#32).header := by
  have hlo := obj_hi_lo_zero o hcs hoth ht
  have hzero : BitVec.ofNat 64 o.rc.toNat &&& (o.withRc 0#32).header = 0#64 :=
    bv32_ofNat_and_hi_zero o.rc.toNat o.rc.isLt _ hlo
  have hadd := BitVec.add_eq_or_of_and_eq_zero _ _ hzero
  rw [hadd]
  unfold LcnfObj.header LcnfObj.withRc
  dsimp
  simp [BitVec.zero_or, BitVec.or_assoc]

private theorem lcnfObjHeader_add1 (o : LcnfObj)
    (hcs : o.csSz < 65536) (hoth : o.other < 256) (ht : o.tag < 256)
    (h0 : 0 ≤ o.rc.toInt) (hlt : o.rc.toInt < 2147483647) :
    o.header + 1#64 = (o.withRc (o.rc + 1#32)).header := by
  have hrc : o.rc.toNat < 2147483647 := by
    rw [BitVec.toInt_eq_toNat_cond] at h0 hlt
    split at hlt <;> omega
  have hw := obj_header_eq_add (o.withRc (o.rc + 1#32)) hcs hoth ht
  have hw1 : (o.withRc (o.rc + 1#32)).header =
      BitVec.ofNat 64 (o.rc + 1#32).toNat + (o.withRc 0#32).header := by
    simpa [LcnfObj.withRc] using hw
  have hrc1 : BitVec.ofNat 64 (o.rc + 1#32).toNat = BitVec.ofNat 64 o.rc.toNat + 1#64 := by
    apply BitVec.eq_of_toNat_eq; simp; omega
  rw [obj_header_eq_add o hcs hoth ht, hw1, hrc1]; ac_rfl

private theorem lcnfObjHeader_sub1 (o : LcnfObj)
    (hcs : o.csSz < 65536) (hoth : o.other < 256) (ht : o.tag < 256)
    (h0 : 0 ≤ o.rc.toInt) (hgt : 1 < o.rc.toNat) :
    o.header - 1#64 = (o.withRc (o.rc - 1#32)).header := by
  have hrc : o.rc.toNat < 2147483648 := by
    rw [BitVec.toInt_eq_toNat_cond] at h0; split at h0 <;> omega
  have hw := obj_header_eq_add (o.withRc (o.rc - 1#32)) hcs hoth ht
  have hw1 : (o.withRc (o.rc - 1#32)).header =
      BitVec.ofNat 64 (o.rc - 1#32).toNat + (o.withRc 0#32).header := by
    simpa [LcnfObj.withRc] using hw
  have hrc1 : BitVec.ofNat 64 (o.rc - 1#32).toNat = BitVec.ofNat 64 o.rc.toNat - 1#64 := by
    apply BitVec.eq_of_toNat_eq
    have hsub : (o.rc - 1#32).toNat = o.rc.toNat - 1 := by bv_omega
    rw [hsub]
    bv_omega
  rw [obj_header_eq_add o hcs hoth ht, hw1, hrc1]
  bv_omega

private theorem lcnfHeap_addr_lt {objs : List LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (lcnfHeap objs ⋆ R) m) {i j : Nat} (hij : i < j) (hj : j < objs.length) :
    objs[i].addr ≠ objs[j].addr := by
  intro heq
  have hi : i < objs.length := Nat.lt_trans hij hj
  rw [lcnfHeap_focus objs hi] at h
  have hj' : j - (i + 1) < (objs.drop (i + 1)).length := by
    rw [List.length_drop]; omega
  rw [lcnfHeap_focus (objs.drop (i + 1)) hj'] at h
  have hget : (objs.drop (i + 1))[j - (i + 1)] = objs[j] := by
    rw [List.getElem_drop]; congr 1; omega
  rw [hget, lcnfObjMem_eq_header_body objs[i], lcnfObjMem_eq_header_body objs[j]] at h
  have hcon :
      ((cell64 objs[i].addr objs[i].header ⋆ lcnfObjBody objs[i]) ⋆
        (cell64 objs[j].addr objs[j].header ⋆
          (lcnfObjBody objs[j] ⋆
            (lcnfHeap (objs.take i) ⋆
              (lcnfHeap ((objs.drop (i + 1)).take (j - (i + 1))) ⋆
                lcnfHeap ((objs.drop (i + 1)).drop (j - (i + 1) + 1))) ⋆ R)))) m :=
    sep_cast h (by ac_rfl)
  rw [heq] at hcon
  exact cell64_conflict _ _ _ _ _ m hcon

private theorem lcnfHeap_addr_ne {objs : List LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (lcnfHeap objs ⋆ R) m) {i j : Nat} (hi : i < objs.length) (hj : j < objs.length)
    (hne : i ≠ j) : objs[i].addr ≠ objs[j].addr := by
  by_cases hij : i < j
  · exact lcnfHeap_addr_lt h hij hj
  · exact Ne.symm (lcnfHeap_addr_lt h (by omega) hi)

private theorem lcnfHeapClosed_set_withRc {objs : List LcnfObj} (hCl : lcnfHeapClosed objs)
    {idx : Nat} (hidx : idx < objs.length) (rc' : BitVec 32) :
    lcnfHeapClosed (objs.set idx (objs[idx].withRc rc')) := by
  intro o ho f hf hf0
  rw [List.mem_iff_getElem] at ho
  obtain ⟨k, hk, rfl⟩ := ho
  have hk0 : k < objs.length := by rw [List.length_set] at hk; exact hk
  have hchild : (objs.set idx (objs[idx].withRc rc'))[k].childFields = objs[k].childFields := by
    by_cases hki : k = idx
    · subst hki
      rw [List.getElem_set_self]
      rfl
    · have hset_k : (objs.set idx (objs[idx].withRc rc'))[k] = objs[k] :=
        List.getElem_set_ne (Ne.symm hki) (by simp [hk0])
      rw [hset_k]
  rw [hchild] at hf
  obtain ⟨o', ho', had'⟩ := hCl objs[k] (List.getElem_mem hk0) f hf hf0
  rw [List.mem_iff_getElem] at ho'
  obtain ⟨k', hk', hk'eq⟩ := ho'
  have hk's : k' < (objs.set idx (objs[idx].withRc rc')).length := by
    rw [List.length_set]; exact hk'
  have had_k' : (objs.set idx (objs[idx].withRc rc'))[k'].addr = f := by
    by_cases hki : k' = idx
    · subst hki
      rw [List.getElem_set_self]
      simp [LcnfObj.withRc, hk'eq, had']
    · have hset_k' : (objs.set idx (objs[idx].withRc rc'))[k'] = objs[k'] :=
        List.getElem_set_ne (Ne.symm hki) (by simp [hk'])
      rw [hset_k', hk'eq, had']
  exact ⟨(objs.set idx (objs[idx].withRc rc'))[k'], List.getElem_mem hk's, had_k'⟩

private theorem zip_mem_elim {α β : Type _} {xs : List α} {ys : List β}
    (hlen : ys.length = xs.length) {p : α × β} (hp : p ∈ xs.zip ys) :
    ∃ k : Nat, ∃ hk : k < xs.length, ∃ _ : k < ys.length, p = (xs[k], ys[k]) := by
  rw [List.mem_iff_getElem] at hp
  obtain ⟨k, hk, rfl⟩ := hp
  have hk1 : k < xs.length := by rw [List.length_zip, hlen, Nat.min_self] at hk; exact hk
  have hk2 : k < ys.length := by omega
  exact ⟨k, hk1, hk2, by simp [List.getElem_zip]⟩

private theorem zip_mem_pair {α β : Type _} {xs : List α} {ys : List β}
    (hlen : ys.length = xs.length) {k : Nat} (hk : k < xs.length) (hk2 : k < ys.length) :
    (xs[k], ys[k]) ∈ xs.zip ys := by
  rw [List.mem_iff_getElem]
  exact ⟨k, by rw [List.length_zip, hlen, Nat.min_self]; exact hk, by simp [List.getElem_zip]⟩

private theorem cloUnderIncRel_init {objs : List LcnfObj}
    (hWf : ∀ obj ∈ objs, obj.Wf) (hCl : lcnfHeapClosed objs) :
    CloUnderIncRel [] objs objs := by
  refine ⟨rfl, hCl, ?_⟩
  intro p hp
  obtain ⟨k, hk, _, hpeq⟩ := zip_mem_elim rfl hp
  rw [hpeq]
  dsimp only
  have hw := hWf objs[k] (List.getElem_mem hk)
  refine ⟨hw, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  by_cases h0 : objs[k].rc = 0#32
  · exact Or.inl ⟨h0, h0⟩
  · right
    have hnn := hw.2.2.1
    have hpos : 0 < objs[k].rc.toInt := by
      rw [BitVec.toInt_eq_toNat_cond] at hnn ⊢
      have hne0 : objs[k].rc.toNat ≠ 0 := fun hz => h0 (BitVec.eq_of_toNat_eq hz)
      split at hnn <;> simp_all <;> omega
    exact ⟨hpos, by simp⟩

private theorem cloUnderIncRel_step_skip {pref : List (BitVec 64)} {p : BitVec 64}
    {objs curObjs : List LcnfObj}
    (hrel : CloUnderIncRel pref objs curObjs)
    (hp : p &&& 1#64 ≠ 0#64) :
    CloUnderIncRel (pref ++ [p]) objs curObjs := by
  rcases hrel with ⟨hlen, hCl, hforall⟩
  refine ⟨hlen, hCl, ?_⟩
  intro pr hpr
  obtain ⟨k, hk, hk_cur, hpeq⟩ := zip_mem_elim hlen hpr
  rw [hpeq]
  dsimp only
  have hrow := hforall (objs[k], curObjs[k]) (zip_mem_pair hlen hk hk_cur)
  dsimp only at hrow
  obtain ⟨hw, ha, hrest⟩ := hrow
  refine ⟨hw, ha, ?_⟩
  have hne : objs[k].addr ≠ p := by
    intro heq
    have hcurWf : curObjs[k].Wf := hw
    have hal : curObjs[k].addr.toNat % 8 = 0 := hcurWf.2.1
    rw [ha, heq] at hal
    apply hp
    apply BitVec.eq_of_toNat_eq
    have h1m : (1#64).toNat = 1 := by decide
    have h0m : (0#64).toNat = 0 := by decide
    rw [BitVec.toNat_and, h1m, Nat.and_one_is_mod, h0m]
    omega
  have hcnt : [p].count objs[k].addr = 0 := by
    simp [Ne.symm hne]
  simpa [List.count_append, hcnt] using hrest

private theorem cloUnderIncRel_step_zero {pref : List (BitVec 64)} {p : BitVec 64}
    {objs curObjs : List LcnfObj} {idx : Nat}
    (hrel : CloUnderIncRel pref objs curObjs)
    (hidx : idx < curObjs.length) (haddr : curObjs[idx].addr = p)
    (hrc0 : curObjs[idx].rc = 0#32)
    (huniq : ∀ j (hj : j < curObjs.length), j ≠ idx → curObjs[j].addr ≠ p) :
    CloUnderIncRel (pref ++ [p]) objs curObjs := by
  rcases hrel with ⟨hlen, hCl, hforall⟩
  refine ⟨hlen, hCl, ?_⟩
  intro pr hpr
  obtain ⟨k, hk, hk_cur, hpeq⟩ := zip_mem_elim hlen hpr
  rw [hpeq]
  dsimp only
  have hrow := hforall (objs[k], curObjs[k]) (zip_mem_pair hlen hk hk_cur)
  dsimp only at hrow
  by_cases hki : k = idx
  · subst hki
    rcases hrow with ⟨hw, ha, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, hrc⟩
    refine ⟨hw, ha, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, ?_⟩
    rcases hrc with ⟨hz1, _⟩ | ⟨_, heq⟩
    · exact Or.inl ⟨hz1, hrc0⟩
    · exfalso
      have hzNat : curObjs[k].rc.toInt = 0 := by rw [hrc0]; decide
      rw [hzNat] at heq; omega
  · obtain ⟨hw, ha, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, hrc⟩ := hrow
    have hne : objs[k].addr ≠ p := by rw [← ha]; exact huniq k hk_cur hki
    have hcnt : [p].count objs[k].addr = 0 := by
      simp [Ne.symm hne]
    refine ⟨hw, ha, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, ?_⟩
    simpa [List.count_append, hcnt] using hrc

private theorem cloUnderIncRel_step_pos {pref : List (BitVec 64)} {p : BitVec 64}
    {objs curObjs : List LcnfObj} {idx : Nat}
    (hrel : CloUnderIncRel pref objs curObjs)
    (hidx : idx < curObjs.length) (haddr : curObjs[idx].addr = p)
    (hrcNz : curObjs[idx].rc ≠ 0#32)
    (hbound : curObjs[idx].rc.toInt < 2147483647)
    (huniq : ∀ j (hj : j < curObjs.length), j ≠ idx → curObjs[j].addr ≠ p) :
    CloUnderIncRel (pref ++ [p]) objs (curObjs.set idx (curObjs[idx].withRc (curObjs[idx].rc + 1#32))) := by
  rcases hrel with ⟨hlen, hCl, hforall⟩
  have hlen' : (curObjs.set idx (curObjs[idx].withRc (curObjs[idx].rc + 1#32))).length = objs.length := by
    simp [hlen]
  refine ⟨hlen', lcnfHeapClosed_set_withRc hCl hidx _, ?_⟩
  intro pr hpr
  obtain ⟨k, hk, hk_cur', hpeq⟩ := zip_mem_elim hlen' hpr
  rw [hpeq]
  dsimp only
  have hk_cur : k < curObjs.length := by omega
  have hrow := hforall (objs[k], curObjs[k]) (zip_mem_pair hlen hk hk_cur)
  dsimp only at hrow
  by_cases hki : k = idx
  · subst hki
    obtain ⟨hw, ha, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, hrc⟩ := hrow
    simp only [List.getElem_set_self]
    have hnn := hw.2.2.1
    have hrc_toNat : curObjs[k].rc.toNat < 2147483647 := by
      rw [BitVec.toInt_eq_toNat_cond] at hnn hbound
      split at hbound <;> omega
    have hinc_toInt : (curObjs[k].rc + 1#32).toInt = curObjs[k].rc.toInt + 1 := by
      rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
      have hsum : (curObjs[k].rc + 1#32).toNat = curObjs[k].rc.toNat + 1 := by bv_omega
      rw [hsum]
      split <;> split <;> omega
    have hw' : (curObjs[k].withRc (curObjs[k].rc + 1#32)).Wf :=
      lcnfObjWf_withRc hw (by rw [hinc_toInt]; omega)
    refine ⟨hw', ha, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, ?_⟩
    rcases hrc with ⟨_, hz2⟩ | ⟨hpos, heq⟩
    · exfalso; exact hrcNz hz2
    · right
      refine ⟨hpos, ?_⟩
      have had_eq : objs[k].addr = p := by rw [← ha, haddr]
      have hcnt : [p].count objs[k].addr = 1 := by
        simp [had_eq]
      simp only [LcnfObj.withRc]
      rw [hinc_toInt, heq, List.count_append, hcnt]
      omega
  · obtain ⟨hw, ha, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, hrc⟩ := hrow
    have hset_k : (curObjs.set idx (curObjs[idx].withRc (curObjs[idx].rc + 1#32)))[k] = curObjs[k] :=
      List.getElem_set_ne (Ne.symm hki) hk_cur'
    rw [hset_k]
    have hne : objs[k].addr ≠ p := by rw [← ha]; exact huniq k hk_cur hki
    have hcnt : [p].count objs[k].addr = 0 := by
      simp [Ne.symm hne]
    refine ⟨hw, ha, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, ?_⟩
    simpa [List.count_append, hcnt] using hrc

private theorem split_clo_region {c : BitVec 64} {nfix k : Nat}
    (hb : 24 + 8 * (nfix + k) ≤ 2 ^ 64) {m : Mem 64}
    (hr : region c (24 + 8 * (nfix + k)) m) :
    ∃ (v0 v8 v16 : BitVec 64) (dst : List (BitVec 64)),
      dst.length = nfix ∧
      (cell64 c v0 ⋆ cell64 (c + 8#64) v8 ⋆ cell64 (c + 16#64) v16 ⋆
        array64 (c + 24#64) dst ⋆
        region (c + BitVec.ofNat 64 (24 + 8 * nfix)) (8 * k)) m := by
  have h1 : 24 + 8 * (nfix + k) = (24 + 8 * nfix) + 8 * k := by omega
  rw [h1, region_split (by omega)] at hr
  obtain ⟨m1, mTail, rfl, hd1, h1m, hTail⟩ := hr
  have h2 : (region c 24 ⋆ region (c + 24#64) (8 * nfix)) m1 := by
    rw [← region_split (by omega)]
    exact h1m
  obtain ⟨m24, mArr, rfl, hd24, h24m, hArm⟩ := h2
  obtain ⟨dst, hlen, hDst⟩ := region_to_array64 nfix (by omega) hArm
  have h3 : (region c 8 ⋆ region (c + 8#64) 16) m24 := by
    rw [← region_split (by decide)]
    exact h24m
  obtain ⟨m0, m16, rfl, hd0, h0m, h16m⟩ := h3
  have h4 : (region (c + 8#64) 8 ⋆ region (c + 16#64) 8) m16 := by
    rw [show c + 16#64 = c + 8#64 + 8#64 by bv_omega]
    rw [← region_split (by decide)]
    exact h16m
  obtain ⟨m8, m16', rfl, hd8, h8m, h16m'⟩ := h4
  obtain ⟨v0, hv0⟩ := region_to_cell64 h0m
  obtain ⟨v8, hv8⟩ := region_to_cell64 h8m
  obtain ⟨v16, hv16⟩ := region_to_cell64 h16m'
  refine ⟨v0, v8, v16, dst, hlen, ?_⟩
  have hmAll : (((cell64 c v0 ⋆ (cell64 (c + 8#64) v8 ⋆ cell64 (c + 16#64) v16)) ⋆
      array64 (c + 24#64) dst) ⋆
      region (c + BitVec.ofNat 64 (24 + 8 * nfix)) (8 * k))
      (((m0.union (m8.union m16')).union mArr).union mTail) :=
    ⟨(m0.union (m8.union m16')).union mArr, mTail, rfl, hd1,
      ⟨m0.union (m8.union m16'), mArr, rfl, hd24,
        ⟨m0, m8.union m16', rfl, hd0, hv0, ⟨m8, m16', rfl, hd8, hv8, hv16⟩⟩,
        hDst⟩,
      hTail⟩
  exact sep_cast hmAll (by ac_rfl)

/-! ## `lcnf_clo_under` WP & M0a `ModuleOk` -/

private theorem sep_assoc_lr {A B C : Mem 64 → Prop} {m : Mem 64} :
    ((A ⋆ B) ⋆ C) m → (A ⋆ (B ⋆ C)) m := by
  intro h; exact sep_cast h (by ac_rfl)

private theorem sep_assoc_rl {A B C : Mem 64 → Prop} {m : Mem 64} :
    (A ⋆ (B ⋆ C)) m → ((A ⋆ B) ⋆ C) m := by
  intro h; exact sep_cast h (by ac_rfl)

private theorem sep_comm' {A B : Mem 64 → Prop} {m : Mem 64} :
    (A ⋆ B) m → (B ⋆ A) m := by
  intro h; exact sep_cast h (by ac_rfl)

private theorem sep_pull2 {A B C : Mem 64 → Prop} {m : Mem 64} :
    (A ⋆ (B ⋆ C)) m → (B ⋆ (A ⋆ C)) m := by
  intro h; exact sep_cast h (by ac_rfl)

private theorem sep_pull3 {A B C D : Mem 64 → Prop} {m : Mem 64} :
    (A ⋆ (B ⋆ (C ⋆ D))) m → (C ⋆ (A ⋆ (B ⋆ D))) m := by
  intro h; exact sep_cast h (by ac_rfl)

private theorem sep_map_left {A A' B : Mem 64 → Prop}
    (f : ∀ {m}, A m → A' m) {m : Mem 64} : (A ⋆ B) m → (A' ⋆ B) m
  | ⟨m1, m2, hm, hd, h1, h2⟩ => ⟨m1, m2, hm, hd, f h1, h2⟩

private theorem sep_map_right {A B B' : Mem 64 → Prop}
    (f : ∀ {m}, B m → B' m) {m : Mem 64} : (A ⋆ B) m → (A ⋆ B') m
  | ⟨m1, m2, hm, hd, h1, h2⟩ => ⟨m1, m2, hm, hd, h1, f h2⟩

private theorem wp_let_add64_eq {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (args : Tup (Arg Val) [i64, i64]) (k : Tup Val [i64] → Expr Val Cont rs) :
    wp Γ Q X (Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := args } k) m =
      wp Γ Q X (k (args.fst.val + args.snd.fst.val, ())) m := by
  rw [wp_let_add_eq]; rfl

private theorem wp_let_sub64_eq {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (args : Tup (Arg Val) [i64, i64]) (k : Tup Val [i64] → Expr Val Cont rs) :
    wp Γ Q X (Expr.let_ { sig := [i64, i64], code := OpCode.sub i64, args := args } k) m =
      wp Γ Q X (k (args.fst.val - args.snd.fst.val, ())) m := by
  rw [wp_let_sub_eq]; rfl

private theorem wp_let_mul64_eq {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (args : Tup (Arg Val) [i64, i64]) (k : Tup Val [i64] → Expr Val Cont rs) :
    wp Γ Q X (Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := args } k) m =
      wp Γ Q X (k (args.fst.val * args.snd.fst.val, ())) m := by
  rw [wp_let_mul_eq]; rfl

private theorem wp_let_and64_eq {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (args : Tup (Arg Val) [i64, i64]) (k : Tup Val [i64] → Expr Val Cont rs) :
    wp Γ Q X (Expr.let_ { sig := [i64, i64], code := OpCode.and i64, args := args } k) m =
      wp Γ Q X (k (args.fst.val &&& args.snd.fst.val, ())) m := by
  rw [wp_let_and_eq]; rfl

private theorem wp_let_or64_eq {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (args : Tup (Arg Val) [i64, i64]) (k : Tup Val [i64] → Expr Val Cont rs) :
    wp Γ Q X (Expr.let_ { sig := [i64, i64], code := OpCode.or i64, args := args } k) m =
      wp Γ Q X (k (args.fst.val ||| args.snd.fst.val, ())) m := by
  rw [wp_let_or_eq]; rfl

private theorem wp_let_shl64_eq {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (args : Tup (Arg Val) [i64, i64]) (k : Tup Val [i64] → Expr Val Cont rs) :
    wp Γ Q X (Expr.let_ { sig := [i64, i64], code := OpCode.shl i64, args := args } k) m =
      wp Γ Q X (k (args.fst.val <<< (args.snd.fst.val.toNat % 64), ())) m := by
  rw [wp_let_shl_eq]; rfl

private theorem wp_let_lshr64_eq {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (args : Tup (Arg Val) [i64, i64]) (k : Tup Val [i64] → Expr Val Cont rs) :
    wp Γ Q X (Expr.let_ { sig := [i64, i64], code := OpCode.lshr i64, args := args } k) m =
      wp Γ Q X (k (args.fst.val >>> (args.snd.fst.val.toNat % 64), ())) m := by
  rw [wp_let_lshr_eq]; rfl

private theorem wp_let_sext32_64_eq {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (args : Tup (Arg Val) [Ty.bits 32]) (k : Tup Val [i64] → Expr Val Cont rs) :
    wp Γ Q X (Expr.let_ { sig := [Ty.bits 32], code := OpCode.sext 32 64, args := args } k) m =
      wp Γ Q X (k (BitVec.signExtend 64 args.fst.val, ())) m := by
  rw [wp_let_sext_eq]; simp

local macro "clo_pure_steps" : tactic =>
  `(tactic| (
    repeat (first
      | rw [wp_let_add64_eq]
      | rw [wp_let_sub64_eq]
      | rw [wp_let_mul64_eq]
      | rw [wp_let_and64_eq]
      | rw [wp_let_or64_eq]
      | rw [wp_let_shl64_eq]
      | rw [wp_let_lshr64_eq]
      | rw [wp_let_sext32_64_eq])
    try dsimp [Arg.val]))

private theorem cloMetaWord_arity (a n : Nat) (ha : a < 65536) :
    cloMetaWord a n &&& 65535#64 = BitVec.ofNat 64 a := by
  unfold cloMetaWord
  apply BitVec.eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro i
  have haM : a % 2 ^ 64 = a := Nat.mod_eq_of_lt (by omega)
  have h65 : (65535#64).toNat = 2 ^ 16 - 1 := rfl
  simp only [BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    h65, haM, Nat.testBit_and, Nat.testBit_or, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  by_cases hi : i < 16
  · have hi' : ¬ 16 ≤ i := by omega
    have hlt64 : i < 64 := by omega
    simp [hi, Nat.testBit_shiftLeft, hi', hlt64]
  · have ha0 : a.testBit i = false := Nat.testBit_lt_two_pow (by
      calc a < 2 ^ 16 := ha
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega))
    simp [hi, ha0]

private theorem cloMetaWord_nfix (a n : Nat) (ha : a < 65536) (hn : n < 65536) :
    ((cloMetaWord a n >>> 16) &&& 65535#64) = BitVec.ofNat 64 n := by
  unfold cloMetaWord
  apply BitVec.eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro i
  have haM : a % 2 ^ 64 = a := Nat.mod_eq_of_lt (by omega)
  have hnM : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  have h65 : (65535#64).toNat = 2 ^ 16 - 1 := rfl
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_or, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, h65, haM, hnM, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_or,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  by_cases hi : i < 16
  · have hlt64 : 16 + i < 64 := by omega
    have ha0 : a.testBit (16 + i) = false := Nat.testBit_lt_two_pow (by
      calc a < 2 ^ 16 := ha
        _ ≤ 2 ^ (16 + i) := Nat.pow_le_pow_right (by omega) (by omega))
    have hge : 16 ≤ 16 + i := by omega
    have hsub : 16 + i - 16 = i := by omega
    simp [hi, hlt64, ha0, Nat.testBit_shiftLeft, hge, hsub]
  · have hn0 : n.testBit i = false := Nat.testBit_lt_two_pow (by
      calc n < 2 ^ 16 := hn
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega))
    simp [hi, hn0]

private theorem fc_cloMeta_arity (fc : LcnfObj) (ha : fc.arity < 65536) :
    fc.cloMeta &&& 65535#64 = BitVec.ofNat 64 fc.arity := by
  unfold LcnfObj.cloMeta
  exact cloMetaWord_arity fc.arity fc.fields.length ha

private theorem fc_cloMeta_nfix (fc : LcnfObj) (ha : fc.arity < 65536) (hn : fc.fields.length < 65536) :
    (fc.cloMeta >>> 16) &&& 65535#64 = BitVec.ofNat 64 fc.fields.length := by
  unfold LcnfObj.cloMeta
  exact cloMetaWord_nfix fc.arity fc.fields.length ha hn

private theorem list_count_take_lt {α : Type _} [BEq α] [LawfulBEq α]
    (xs : List α) {i : Nat} (hi : i < xs.length) :
    (xs.take i).count xs[i] + 1 ≤ xs.count xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simp
    | succ i =>
      have hi' : i < xs.length := by simp at hi; omega
      simp only [List.take_succ_cons, List.getElem_cons_succ, List.count_cons]
      have hsub : (xs.take i).count xs[i] + 1 ≤ xs.count xs[i] := ih hi'
      split <;> omega

private theorem clo_take_eq_of_take_eq {α : Type _} {a b : List α} {n : Nat}
    (ha : a.length = n) (hb : b.length = n) (ht : a.take n = b.take n) : a = b := by
  have h1 : a.take n = a := List.take_of_length_le (by omega)
  have h2 : b.take n = b := List.take_of_length_le (by omega)
  rw [h1, h2] at ht
  exact ht

private theorem list_take_set_succ {α : Type _} {dst src : List α} {i : Nat}
    (hi : i < dst.length) (hs : i < src.length) (ht : dst.take i = src.take i) :
    (dst.set i src[i]).take (i + 1) = src.take (i + 1) := by
  apply List.ext_getElem
  · simp; omega
  · intro j hj1 hj2
    have hSetLen : (dst.set i src[i]).length = dst.length := List.length_set
    have hjLt1 : j < i + 1 := by
      have : j < min (i + 1) (dst.set i src[i]).length := by simpa [List.length_take] using hj1
      omega
    by_cases hji : j = i
    · subst hji
      simp [List.getElem_take, List.getElem_set_self]
    · have hlt : j < i := by omega
      have hjSet : j < (dst.set i src[i]).length := by omega
      have hjDst : j < dst.length := by omega
      have hjTakeD : j < (dst.take i).length := by rw [List.length_take]; omega
      have hjTakeS : j < (src.take i).length := by rw [List.length_take]; omega
      have h1 : ((dst.set i src[i]).take (i + 1))[j]'hj1 = (dst.set i src[i])[j]'hjSet := List.getElem_take
      have h2 : (dst.set i src[i])[j]'hjSet = dst[j]'hjDst := List.getElem_set_ne (Ne.symm hji) hjSet
      have h3 : dst[j]'hjDst = (dst.take i)[j]'hjTakeD := (List.getElem_take).symm
      have h4 : (src.take i)[j]'hjTakeS = src[j]'(by omega) := List.getElem_take
      have h5 : (src.take (i + 1))[j]'hj2 = src[j]'(by omega) := List.getElem_take
      rw [h1, h2, h3]
      have hEqJ : (dst.take i)[j]'hjTakeD = (src.take i)[j]'hjTakeS := by congr 1
      rw [hEqJ, h4, h5]

private theorem preservesMeta_trans {a b c : RtC0State}
    (h1 : b.PreservesMeta a) (h2 : c.PreservesMeta b) : c.PreservesMeta a := by
  rcases h1 with ⟨h11, h12, h13, h14, h15, h16, h17, h18, h19⟩
  rcases h2 with ⟨h21, h22, h23, h24, h25, h26, h27, h28, h29⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all

private theorem lcnfObjMem_clo_eq (fc : LcnfObj) (ht : fc.tag = closureTag) :
    lcnfObjMem fc =
      (cell64 fc.addr fc.header ⋆ cell64 (fc.addr + 8#64) fc.funId ⋆
        cell64 (fc.addr + 16#64) fc.cloMeta ⋆ array64 (fc.addr + 24#64) fc.fields ⋆
        region (fc.addr + BitVec.ofNat 64 (24 + 8 * fc.fields.length))
          (fc.csSz - (24 + 8 * fc.fields.length))) := by
  funext m; simp [lcnfObjMem, ht]

private def cloNewObjMem (c : BitVec 64) (fc : LcnfObj) (sz k : Nat)
    (dst : List (BitVec 64)) : Mem 64 → Prop :=
  let nfix := fc.fields.length
  let cHdr := 1#64 ||| BitVec.ofNat 64 sz <<< 32 ||| BitVec.ofNat 64 closureTag <<< 56
  let cMeta := cloMetaWord fc.arity (nfix + k)
  cell64 c cHdr ⋆ cell64 (c + 8#64) fc.funId ⋆ cell64 (c + 16#64) cMeta ⋆
    array64 (c + 24#64) dst ⋆ region (c + BitVec.ofNat 64 (24 + 8 * nfix)) (8 * k)

private def cloNonFieldMem (fc : LcnfObj) : Mem 64 → Prop :=
  cell64 fc.addr fc.header ⋆ cell64 (fc.addr + 8#64) fc.funId ⋆
    cell64 (fc.addr + 16#64) fc.cloMeta ⋆
    region (fc.addr + BitVec.ofNat 64 (24 + 8 * fc.fields.length))
      (fc.csSz - (24 + 8 * fc.fields.length))

private theorem lcnfObjMem_clo_nonfield (fc : LcnfObj) (ht : fc.tag = closureTag) :
    lcnfObjMem fc = (array64 (fc.addr + 24#64) fc.fields ⋆ cloNonFieldMem fc) := by
  funext m; apply propext; constructor
  · intro h; rw [lcnfObjMem_clo_eq fc ht] at h; unfold cloNonFieldMem; exact sep_cast h (by ac_rfl)
  · intro h; rw [lcnfObjMem_clo_eq fc ht]; unfold cloNonFieldMem at h; exact sep_cast h (by ac_rfl)

private theorem sep_clo_post_emp {A F G : Mem 64 → Prop} {c : BitVec 64}
    {fc : LcnfObj} {sz k : Nat} {m : Mem 64}
    (h : (A ⋆ cloNewObjMem c fc sz k fc.fields ⋆ F ⋆ G) m) :
    ((A ⋆ cloNewObjMem c fc sz k fc.fields ⋆ Std.ExtHashMap.emp) ⋆ F ⋆ G) m := by
  rw [Std.ExtHashMap.sep_emp]
  exact sep_cast h (by ac_rfl)

private theorem clo_unpack_post {c : BitVec 64} {fc : LcnfObj} {sz k : Nat}
    {A Tail F G : Mem 64 → Prop} {m : Mem 64}
    (h : ((A ⋆ cloNewObjMem c fc sz k fc.fields ⋆ Tail) ⋆ F ⋆ G) m) :
    ((A ⋆ cell64 c (1#64 ||| BitVec.ofNat 64 sz <<< 32 ||| BitVec.ofNat 64 closureTag <<< 56) ⋆
        cell64 (c + 8#64) fc.funId ⋆ cell64 (c + 16#64) (cloMetaWord fc.arity (fc.fields.length + k)) ⋆
        array64 (c + 24#64) fc.fields ⋆
        region (c + BitVec.ofNat 64 (24 + 8 * fc.fields.length)) (8 * k) ⋆ Tail) ⋆ F ⋆ G) m := by
  unfold cloNewObjMem at h
  exact sep_map_left (sep_map_left (sep_map_left (fun hm => by
    let h1 := sep_assoc_rl hm
    let h2 := sep_map_left sep_assoc_rl h1
    let h3 := sep_map_left (sep_map_left sep_assoc_rl) h2
    exact sep_map_left (sep_map_left (sep_map_left sep_assoc_rl)) h3))) h

private theorem clo_objMem_focus_fields (fc : LcnfObj) (ht : fc.tag = closureTag)
    {P : Mem 64 → Prop} {m : Mem 64}
    (h : (lcnfObjMem fc ⋆ P) m) :
    (array64 (fc.addr + 24#64) fc.fields ⋆ (cloNonFieldMem fc ⋆ P)) m := by
  rw [lcnfObjMem_clo_nonfield fc ht] at h
  exact sep_assoc_lr h

private theorem clo_objMem_unfocus_fields (fc : LcnfObj) (ht : fc.tag = closureTag)
    {P : Mem 64 → Prop} {m : Mem 64}
    (h : (array64 (fc.addr + 24#64) fc.fields ⋆ (cloNonFieldMem fc ⋆ P)) m) :
    (lcnfObjMem fc ⋆ P) m := by
  rw [lcnfObjMem_clo_nonfield fc ht]
  exact sep_assoc_rl h

private theorem clo_objMem_header_sub1 (o : LcnfObj) (hw : o.Wf) (hgt : 1 < o.rc.toNat)
    (_hlt : o.rc.toInt < 2147483648) :
    o.header - 1#64 = (o.withRc (o.rc - 1#32)).header := by
  have hcs := hw.2.2.2.1
  have hoth := hw.2.2.2.2.1
  have ht := hw.2.2.2.2.2.1
  exact lcnfObjHeader_sub1 o hcs hoth ht hw.2.2.1 hgt

private theorem heap_idx_unique {objs : List LcnfObj} {F : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfHeap objs ⋆ F) m) {idx : Nat} (hidx : idx < objs.length) :
    ∀ j (hj : j < objs.length), j ≠ idx → objs[j].addr ≠ objs[idx].addr := by
  intro j hj hji
  exact Ne.symm (lcnfHeap_addr_ne hm hidx hj (Ne.symm hji))

private theorem clo_withRc_zero (fc : LcnfObj) (h0 : fc.rc = 0#32) :
    fc.withRc 0#32 = fc := by
  cases fc
  simp only [LcnfObj.withRc] at h0 ⊢
  subst h0
  rfl

theorem lcnf_clo_under_wp (Γ : Env)
    (hAlloc : ∀ xs m Q X, lcnfAllocSpec xs m Q X → Γ "lcnf_alloc" [i64, i64] [i64] xs m Q X)
    (hFree : ∀ xs m Q X, lcnfFreeObjSpec xs m Q X → Γ "lcnf_free_obj" [i64, i64] [] xs m Q X) :
    ∀ (xs : Tup Val lcnf_clo_under.as) (m : Mem 64) (Q : Post lcnf_clo_under.rs) (X : XPost),
      lcnfCloUnderSpec xs m Q X → Func.wp Γ lcnf_clo_under.body xs m Q X := by
  dsimp [lcnf_clo_under]
  intro ⟨rt, f, k, ⟨⟩⟩ m Q X hSpec
  dsimp [Func.wp, lcnf_clo_under_body]
  rcases hSpec with ⟨st, fc, objs, R, hfcAddr, hfcTag, hfcWf, hObjsWf, hObjsCl, hFieldsMem,
    hRcBound, hkPos, hkLe, hTotLe, hMinSz, hMaxSz, hRoom, hm, hPost⟩
  let nfix : Nat := fc.fields.length
  let sz : Nat := 24 + 8 * (nfix + k.toNat)
  have harity : fc.arity < 65536 := by
    have := hfcWf.2.2.2.2.2.2.2.2.2; simp only [hfcTag, ↓reduceIte] at this; exact this.1
  have hnfix_lt : nfix < 65536 := by
    have := hfcWf.2.2.2.2.2.2.2.2.2; simp only [hfcTag, ↓reduceIte] at this; exact this.2.1
  have hcs_lt : fc.csSz < 65536 := hfcWf.2.2.2.1
  have hoth_lt : fc.other < 256 := hfcWf.2.2.2.2.1
  have htag_lt : fc.tag < 256 := hfcWf.2.2.2.2.2.1
  have hrc_nn : 0 ≤ fc.rc.toInt := hfcWf.2.2.1
  have hf_ne0 : f ≠ 0#64 := by rw [← hfcAddr]; exact hfcWf.1
  have hf_al : f.toNat % 8 = 0 := by rw [← hfcAddr]; exact hfcWf.2.1
  have hmUnpack : (cell64 (f + 16#64) fc.cloMeta ⋆
      (rtC0Inv rt st ⋆ (cell64 f fc.header ⋆ cell64 (f + 8#64) fc.funId ⋆
        array64 (f + 24#64) fc.fields ⋆
        region (f + BitVec.ofNat 64 (24 + 8 * nfix)) (fc.csSz - (24 + 8 * nfix))) ⋆
       (lcnfHeap objs ⋆ R))) m := by
    have h1 : (lcnfObjMem fc ⋆ (rtC0Inv rt st ⋆ (lcnfHeap objs ⋆ R))) m := sep_cast hm (by ac_rfl)
    rw [lcnfObjMem_clo_eq fc hfcTag, hfcAddr] at h1
    let Rest : Mem 64 → Prop := rtC0Inv rt st ⋆ (lcnfHeap objs ⋆ R)
    have h2 : (cell64 (f + 16#64) fc.cloMeta ⋆
        (cell64 f fc.header ⋆ cell64 (f + 8#64) fc.funId ⋆
          array64 (f + 24#64) fc.fields ⋆
          region (f + BitVec.ofNat 64 (24 + 8 * nfix)) (fc.csSz - (24 + 8 * nfix))) ⋆ Rest) m := by
      change ((cell64 f fc.header ⋆ cell64 (f + 8#64) fc.funId ⋆
          cell64 (f + 16#64) fc.cloMeta ⋆ array64 (f + 24#64) fc.fields ⋆
          region (f + BitVec.ofNat 64 (24 + 8 * nfix)) (fc.csSz - (24 + 8 * nfix))) ⋆ Rest) m at h1
      exact sep_cast h1 (by ac_rfl)
    dsimp [Rest] at h2
    exact sep_cast h2 (by ac_rfl)
  clo_pure_steps
  refine wp_load_cell64 (a := Arg.var (f + 16#64)) hmUnpack ?_
  clo_pure_steps
  rw [fc_cloMeta_arity fc harity,
    fc_cloMeta_nfix fc harity hnfix_lt]
  refine wp_join_group (fun _ _ => False) (fun _ _ _ hf => False.elim hf) ?_
  intro _J0 _hJ0
  refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
  dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
  constructor
  · intro hkBad
    exfalso
    have h8188 : (8188#64).toNat = 8188 := by decide
    simp [BitVec.ult, h8188] at hkBad
    omega
  · intro _hkOk
    clo_pure_steps
    refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
    dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
    constructor
    · intro hTotBad
      exfalso
      have h8188 : (8188#64).toNat = 8188 := by decide
      have hn64 : (BitVec.ofNat 64 fc.fields.length + k).toNat = nfix + k.toNat := by
        have h1 : fc.fields.length % 2 ^ 64 = nfix := Nat.mod_eq_of_lt (by omega)
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, h1, Nat.mod_eq_of_lt (by omega)]
      simp [BitVec.ult, h8188, hn64] at hTotBad
      omega
    · intro _hTotOk
      clo_pure_steps
      have hv9 : BitVec.ofNat 64 nfix + k = BitVec.ofNat 64 (nfix + k.toNat) := by
        apply BitVec.eq_of_toNat_eq; simp
      have hv11 : 24#64 + 8#64 * (BitVec.ofNat 64 nfix + k) = BitVec.ofNat 64 sz := by
        rw [hv9]
        apply BitVec.eq_of_toNat_eq
        simp [sz]
      rw [hv11]
      have hmAlloc : (rtC0Inv rt st ⋆ (lcnfObjMem fc ⋆ lcnfHeap objs ⋆ R)) m := sep_cast hm (by ac_rfl)
      refine wp_call_ret1 _ _ (fun c m1 => ∃ st',
          c ≠ 0#64 ∧ c.toNat % 8 = 0 ∧ st'.PreservesMeta st ∧ st'.rem ≤ st.rem ∧
          ((rtC0Inv rt st' ⋆ region c sz) ⋆ (lcnfObjMem fc ⋆ lcnfHeap objs ⋆ R)) m1) ?_ ?_
      · apply hAlloc
        have hal : align8 (BitVec.ofNat 64 sz).toNat = sz := by
          unfold align8
          have hsz : (BitVec.ofNat 64 sz).toNat = sz := Nat.mod_eq_of_lt (by omega)
          rw [hsz]; omega
        refine ⟨st, lcnfObjMem fc ⋆ lcnfHeap objs ⋆ R, ?_, ?_, ?_, ?_, hmAlloc, ?_⟩
        · dsimp only [Arg.val]
          have hsz : (BitVec.ofNat 64 sz).toNat = sz := by
            rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
          rw [hsz]; omega
        · dsimp only [Arg.val]; rw [hal]; exact hMinSz
        · dsimp only [Arg.val]; rw [hal]; exact Nat.lt_trans hMaxSz (by decide : 65536 < rtMaxObjBytes)
        · dsimp only [Arg.val]; rw [hal]; exact hRoom
        · intro c st' m1 hc0 hcAl hmMeta hmRem hm1
          dsimp only [Arg.val] at hm1
          rw [hal] at hm1
          exact ⟨st', hc0, hcAl, hmMeta, hmRem, hm1⟩
      · intro c m1 ⟨st', hcNe0, hcAlign, hMeta1, hRem1, hm1⟩
        let F_obj_rest : Mem 64 → Prop :=
          cell64 f fc.header ⋆ cell64 (f + 16#64) fc.cloMeta ⋆
            region (f + BitVec.ofNat 64 (24 + 8 * nfix)) (fc.csSz - (24 + 8 * nfix))
        let F_base : Mem 64 → Prop := rtC0Inv rt st' ⋆ F_obj_rest ⋆ lcnfHeap objs ⋆ R
        have hm1_split : ∃ v0 v8 v16 dst, dst.length = nfix ∧
            (cell64 c v0 ⋆ (cell64 (c + 8#64) v8 ⋆ (cell64 (c + 16#64) v16 ⋆
              (array64 (c + 24#64) dst ⋆ (region (c + BitVec.ofNat 64 (24 + 8 * nfix)) (8 * k.toNat) ⋆
                (cell64 (f + 8#64) fc.funId ⋆ (array64 (f + 24#64) fc.fields ⋆ F_base))))))) m1 := by
          have hm1_fc : (region c sz ⋆ (cell64 (f + 8#64) fc.funId ⋆ (array64 (f + 24#64) fc.fields ⋆ F_base))) m1 := by
            have h1a : (region c sz ⋆ (lcnfObjMem fc ⋆ (rtC0Inv rt st' ⋆ (lcnfHeap objs ⋆ R)))) m1 :=
              sep_cast hm1 (by ac_rfl)
            refine sep_map_right (fun {m'} hrest => ?_) h1a
            have h1b : ((cell64 (f + 8#64) fc.funId ⋆ (array64 (f + 24#64) fc.fields ⋆ F_obj_rest)) ⋆
                (rtC0Inv rt st' ⋆ (lcnfHeap objs ⋆ R))) m' :=
              sep_map_left (fun hfc => by
                rw [lcnfObjMem_clo_eq fc hfcTag, hfcAddr] at hfc
                dsimp [F_obj_rest]
                exact sep_cast hfc (by ac_rfl)) hrest
            dsimp [F_base]
            exact sep_cast h1b (by ac_rfl)
          rcases hm1_fc with ⟨mr, mfr, hmrEq, hd, hmr, hmfr⟩
          obtain ⟨v0, v8, v16, dst, hdstLen, hsplit⟩ := split_clo_region (by omega) hmr
          refine ⟨v0, v8, v16, dst, hdstLen, ?_⟩
          have hAll : (((((cell64 c v0 ⋆ cell64 (c + 8#64) v8) ⋆ cell64 (c + 16#64) v16) ⋆
              array64 (c + 24#64) dst) ⋆
              region (c + BitVec.ofNat 64 (24 + 8 * nfix)) (8 * k.toNat)) ⋆
              (cell64 (f + 8#64) fc.funId ⋆ (array64 (f + 24#64) fc.fields ⋆ F_base))) m1 :=
            ⟨mr, mfr, hmrEq, hd, hsplit, hmfr⟩
          exact sep_cast hAll (by ac_rfl)
        rcases hm1_split with ⟨v0, v8, v16, dst, hdstLen, hm1'⟩
        let cHdr : BitVec 64 := 1#64 ||| BitVec.ofNat 64 sz <<< 32 ||| BitVec.ofNat 64 closureTag <<< 56
        let cMeta : BitVec 64 := cloMetaWord fc.arity (nfix + k.toNat)
        clo_pure_steps
        refine wp_store_cell64 (v0 := v0) (v := Arg.var _) (a := Arg.var c) hm1' ?_
        intro m2 hm2
        dsimp only [Arg.val] at hm2
        have hv18 : (1#64 ||| BitVec.ofNat 64 sz <<< 32 ||| 17654110539292344320#64) = cHdr := by
          dsimp [cHdr]
          have h245 : (BitVec.ofNat 64 closureTag <<< 56 : BitVec 64) = 17654110539292344320#64 := by decide
          rw [h245]
        rw [hv18] at hm2
        clo_pure_steps
        have hm2_fun : (cell64 (f + 8#64) fc.funId ⋆
            (cell64 (c + 8#64) v8 ⋆ (cell64 c cHdr ⋆ (cell64 (c + 16#64) v16 ⋆
              (array64 (c + 24#64) dst ⋆ (region (c + BitVec.ofNat 64 (24 + 8 * nfix)) (8 * k.toNat) ⋆
                (array64 (f + 24#64) fc.fields ⋆ F_base))))))) m2 :=
          sep_cast hm2 (by ac_rfl)
        refine wp_load_cell64 (a := Arg.var (f + 8#64)) hm2_fun ?_
        have hm2_dst8 : (cell64 (c + 8#64) v8 ⋆
            (cell64 c cHdr ⋆ (cell64 (c + 16#64) v16 ⋆ (array64 (c + 24#64) dst ⋆
              (region (c + BitVec.ofNat 64 (24 + 8 * nfix)) (8 * k.toNat) ⋆
                (cell64 (f + 8#64) fc.funId ⋆ (array64 (f + 24#64) fc.fields ⋆ F_base))))))) m2 := by
          have h1 := sep_pull2 hm2_fun
          have h2 := sep_map_right sep_pull2 h1
          have h3 := sep_map_right (sep_map_right sep_pull2) h2
          have h4 := sep_map_right (sep_map_right (sep_map_right sep_pull2)) h3
          exact sep_map_right (sep_map_right (sep_map_right (sep_map_right sep_pull2))) h4
        refine wp_store_cell64 (v0 := v8) (v := Arg.var fc.funId) (a := Arg.var (c + 8#64)) hm2_dst8 ?_
        intro m3 hm3
        clo_pure_steps
        have hm3_c16 : (cell64 (c + 16#64) v16 ⋆
            (cell64 c cHdr ⋆ (cell64 (c + 8#64) fc.funId ⋆ (array64 (c + 24#64) dst ⋆
              (region (c + BitVec.ofNat 64 (24 + 8 * nfix)) (8 * k.toNat) ⋆
                (cell64 (f + 8#64) fc.funId ⋆ (array64 (f + 24#64) fc.fields ⋆ F_base))))))) m3 := by
          dsimp only [Arg.val] at hm3
          exact sep_cast hm3 (by ac_rfl)
        refine wp_store_cell64 (v0 := v16) (v := Arg.var _) (a := Arg.var (c + 16#64)) hm3_c16 ?_
        intro m4 hm4
        dsimp only [Arg.val] at hm4
        have hv25 : (BitVec.ofNat 64 fc.arity ||| ((BitVec.ofNat 64 nfix + k) <<< 16)) = cMeta := by
          rw [hv9]; rfl
        rw [hv25] at hm4
        let F_L1 : Mem 64 → Prop :=
          cell64 c cHdr ⋆ (cell64 (c + 8#64) fc.funId ⋆ (cell64 (c + 16#64) cMeta ⋆
            (region (c + BitVec.ofNat 64 (24 + 8 * nfix)) (8 * k.toNat) ⋆
              (cell64 (f + 8#64) fc.funId ⋆ F_base))))
        have hm4_L1 : (array64 (c + 24#64) dst ⋆ (array64 (f + 24#64) fc.fields ⋆ F_L1)) m4 := by
          dsimp [F_L1]
          exact sep_cast hm4 (by ac_rfl)
        let Inv1 : Nat → Tup Val [i64] → Mem 64 → Prop := fun rem (iBV, _) curM =>
          ∃ i curDst, rem = nfix - i ∧ i ≤ nfix ∧ iBV = BitVec.ofNat 64 i ∧
            curDst.length = nfix ∧ curDst.take i = fc.fields.take i ∧
            (array64 (c + 24#64) curDst ⋆ (array64 (f + 24#64) fc.fields ⋆ F_L1)) curM
        refine wp_loop_group Inv1 ?_ (fun J1 hJ1 => by
          dsimp
          exact hJ1 nfix (0#64, ()) m4 ⟨0, dst, rfl, Nat.zero_le _, rfl, hdstLen, by simp, hm4_L1⟩)
        intro J1 rem ⟨iBV, ⟨⟩⟩ mL1 hIH1 ⟨i, curDst, hrem1, hiLe, hiBV, hDstLen, hTakeEq, hmL1⟩
        refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
        dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
        constructor
        · intro hiUlt
          have hiLt : i < nfix := by
            rw [hiBV] at hiUlt
            have hi64 : (BitVec.ofNat 64 i).toNat = i := Nat.mod_eq_of_lt (by omega)
            have hn64 : (BitVec.ofNat 64 nfix).toNat = nfix := Nat.mod_eq_of_lt (by omega)
            have : (BitVec.ofNat 64 i).ult (BitVec.ofNat 64 nfix) = decide (i < nfix) := by
              simp [BitVec.ult, hi64, hn64]
            rw [this] at hiUlt
            exact of_decide_eq_true hiUlt
          clo_pure_steps
          have haddrF : (f + 24#64) + 8#64 * iBV = (f + 24#64) + BitVec.ofNat 64 (8 * i) := by
            rw [hiBV]
            congr 1
            apply BitVec.eq_of_toNat_eq; simp
          have haddrC : (c + 24#64) + 8#64 * iBV = (c + 24#64) + BitVec.ofNat 64 (8 * i) := by
            rw [hiBV]
            congr 1
            apply BitVec.eq_of_toNat_eq; simp
          have hmL1_f : (array64 (f + 24#64) fc.fields ⋆ (array64 (c + 24#64) curDst ⋆ F_L1)) mL1 :=
            sep_pull2 hmL1
          refine wp_load_array64 (base := f + 24#64) (xs := fc.fields) (i := i) haddrF hiLt hmL1_f ?_
          have hmL1_c : (array64 (c + 24#64) curDst ⋆ (array64 (f + 24#64) fc.fields ⋆ F_L1)) mL1 :=
            sep_pull2 hmL1_f
          refine wp_store_array64 (base := c + 24#64) (xs := curDst) (i := i)
            (v := Arg.var fc.fields[i]) haddrC (by omega) hmL1_c ?_
          intro mL1' hmL1'
          clo_pure_steps
          have hiBV1 : iBV + 1#64 = BitVec.ofNat 64 (i + 1) := by
            rw [hiBV]; apply BitVec.eq_of_toNat_eq; simp
          rw [hiBV1]
          exact hIH1 (nfix - (i + 1)) (BitVec.ofNat 64 (i + 1), ()) mL1' (by omega)
            ⟨i + 1, curDst.set i fc.fields[i], rfl, by omega, rfl, by simp [hDstLen],
              list_take_set_succ (by omega) hiLt hTakeEq, hmL1'⟩
        · intro hiNotUlt
          have hiEq : i = nfix := by
            rw [hiBV] at hiNotUlt
            have hi64 : (BitVec.ofNat 64 i).toNat = i := Nat.mod_eq_of_lt (by omega)
            have hn64 : (BitVec.ofNat 64 nfix).toNat = nfix := Nat.mod_eq_of_lt (by omega)
            have : (BitVec.ofNat 64 i).ult (BitVec.ofNat 64 nfix) = decide (i < nfix) := by
              simp [BitVec.ult, hi64, hn64]
            rw [this] at hiNotUlt
            have : ¬ i < nfix := of_decide_eq_false hiNotUlt
            omega
          have hCurEq : curDst = fc.fields := by
            subst hiEq
            exact clo_take_eq_of_take_eq hDstLen rfl hTakeEq
          rw [hCurEq] at hmL1
          let C_mem : Mem 64 → Prop := cloNewObjMem c fc sz k.toNat fc.fields
          have hmL1_pack : (lcnfHeap objs ⋆ (lcnfObjMem fc ⋆ (rtC0Inv rt st' ⋆ C_mem ⋆ R))) mL1 := by
            have hb1 : (cell64 c cHdr ⋆ (cell64 (c + 8#64) fc.funId ⋆ (cell64 (c + 16#64) cMeta ⋆
                (array64 (c + 24#64) fc.fields ⋆ (region (c + BitVec.ofNat 64 (24 + 8 * nfix)) (8 * k.toNat) ⋆
                  (array64 (f + 24#64) fc.fields ⋆ (cell64 (f + 8#64) fc.funId ⋆ F_base))))))) mL1 := by
              dsimp [F_L1] at hmL1
              exact sep_cast hmL1 (by ac_rfl)
            have hb1_l := sep_assoc_rl (sep_assoc_rl (sep_assoc_rl (sep_assoc_rl hb1)))
            have hC_step : (C_mem ⋆ (array64 (f + 24#64) fc.fields ⋆ (cell64 (f + 8#64) fc.funId ⋆ F_base))) mL1 := by
              dsimp [C_mem, cloNewObjMem, cHdr, cMeta, nfix] at hb1_l ⊢
              exact hb1_l
            have hfc_step : ((array64 (f + 24#64) fc.fields ⋆ (cell64 (f + 8#64) fc.funId ⋆ F_obj_rest)) ⋆
                (C_mem ⋆ (rtC0Inv rt st' ⋆ (lcnfHeap objs ⋆ R)))) mL1 := by
              dsimp [F_base] at hC_step
              exact sep_cast hC_step (by ac_rfl)
            have hfc_packed : (lcnfObjMem fc ⋆ (C_mem ⋆ (rtC0Inv rt st' ⋆ (lcnfHeap objs ⋆ R)))) mL1 := by
              refine sep_map_left (fun hfc => ?_) hfc_step
              rw [lcnfObjMem_clo_eq fc hfcTag, hfcAddr]
              dsimp [F_obj_rest] at hfc
              exact sep_cast hfc (by ac_rfl)
            exact sep_cast hfc_packed (by ac_rfl)
          have hmL1_hdr : (cell64 f fc.header ⋆ (lcnfObjBody fc ⋆ (lcnfHeap objs ⋆ (rtC0Inv rt st' ⋆ C_mem ⋆ R)))) mL1 := by
            have h1 := sep_pull2 hmL1_pack
            rw [lcnfObjMem_eq_header_body fc, hfcAddr] at h1
            exact sep_assoc_lr h1
          refine wp_load_cell64 (a := Arg.var f) hmL1_hdr ?_
          clo_pure_steps
          rw [LcnfObj.header_rc fc hcs_lt hoth_lt htag_lt]
          refine wp_join_group (fun _ m2 => Q (c, ()) m2) (fun _ _ m2 hQ => by dsimp; exact hQ) ?_
          intro J2 hJ2
          refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
          dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
          constructor
          · intro hrc1Eq
            have hrc1 : fc.rc = 1#32 := by
              have : BitVec.ofNat 64 fc.rc.toNat = 1#64 := of_decide_eq_true hrc1Eq
              apply BitVec.eq_of_toNat_eq
              have := congrArg BitVec.toNat this
              simpa [Nat.mod_eq_of_lt (by omega : fc.rc.toNat < 2 ^ 64)] using this
            have hFreePre : (rtC0Inv rt st' ⋆ freeObjLayout f fc.totalBytes fc.header ⋆
                ((C_mem ⋆ lcnfHeap objs) ⋆ R)) mL1 := by
              have h1 : (rtC0Inv rt st' ⋆ (lcnfObjMem fc ⋆ ((C_mem ⋆ lcnfHeap objs) ⋆ R))) mL1 :=
                sep_cast hmL1_pack (by ac_rfl)
              rw [← hfcAddr]
              exact sep_assoc_rl (sep_map_right (sep_map_left (lcnfObjMem_to_freeObjLayout hfcWf)) h1)
            refine wp_call_of_spec _ _ ?_
            · apply hFree
              have hEven : (f &&& 1#64 ≠ 0#64) = False := by
                apply propext; constructor
                · intro hne; apply hne; apply BitVec.eq_of_toNat_eq
                  have h1m : (1#64).toNat = 1 := by decide
                  have h0m : (0#64).toNat = 0 := by decide
                  rw [BitVec.toNat_and, h1m, Nat.and_one_is_mod, h0m]; omega
                · exact False.elim
              dsimp [lcnfFreeObjSpec]
              simp only [hEven, ↓reduceIte]
              refine ⟨st', fc.header, fc.totalBytes, (C_mem ⋆ lcnfHeap objs) ⋆ R, hf_ne0, hf_al,
                hfcWf.2.2.2.2.2.2.1, hfcWf.2.2.2.2.2.2.2.1, hfcWf.2.2.2.2.2.2.2.2.1,
                hFreePre, ?_⟩
              intro st'' mFree hMeta2 hRem2 _hWb2 hmFree
              apply hJ2 () mFree
              refine hPost c st'' objs mFree hcNe0 hcAlign
                (preservesMeta_trans hMeta1 hMeta2) (by omega) (by simp [hrc1]) ?_
              simp only [hrc1, ↓reduceIte]
              have hmFree_ord : (rtC0Inv rt st'' ⋆ C_mem ⋆ lcnfHeap objs ⋆ R) mFree :=
                sep_cast hmFree (by ac_rfl)
              dsimp [C_mem, sz, nfix] at hmFree_ord
              exact clo_unpack_post (sep_clo_post_emp hmFree_ord)
          · intro hrcNe1Eq
            have hrcNe1 : fc.rc ≠ 1#32 := by
              intro hEq; apply of_decide_eq_false hrcNe1Eq
              rw [hEq]; decide
            let F_L3 : Mem 64 → Prop := rtC0Inv rt st' ⋆ C_mem ⋆ R
            let Inv3 : Nat → Tup Val [i64] → Mem 64 → Prop := fun rem (jBV, _) curM =>
              ∃ j curObjs, rem = nfix - j ∧ j ≤ nfix ∧ jBV = BitVec.ofNat 64 j ∧
                CloUnderIncRel (fc.fields.take j) objs curObjs ∧
                (lcnfHeap curObjs ⋆ (lcnfObjMem fc ⋆ F_L3)) curM
            refine wp_loop_group Inv3 ?_ (fun J3 hJ3 => by
              dsimp
              exact hJ3 nfix (0#64, ()) mL1 ⟨0, objs, rfl, Nat.zero_le _, rfl,
                cloUnderIncRel_init hObjsWf hObjsCl, hmL1_pack⟩)
            intro J3 rem ⟨jBV, ⟨⟩⟩ mL3 hIH3 ⟨j, curObjs, hrem3, hjLe, hjBV, hRel, hmL3⟩
            refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
            dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
            constructor
            · intro hjUlt
              have hjLt : j < nfix := by
                rw [hjBV] at hjUlt
                have hj64 : (BitVec.ofNat 64 j).toNat = j := Nat.mod_eq_of_lt (by omega)
                have hn64 : (BitVec.ofNat 64 nfix).toNat = nfix := Nat.mod_eq_of_lt (by omega)
                have : (BitVec.ofNat 64 j).ult (BitVec.ofNat 64 nfix) = decide (j < nfix) := by
                  simp [BitVec.ult, hj64, hn64]
                rw [this] at hjUlt
                exact of_decide_eq_true hjUlt
              clo_pure_steps
              have haddrJ : (f + 24#64) + 8#64 * jBV = (f + 24#64) + BitVec.ofNat 64 (8 * j) := by
                rw [hjBV]; congr 1; apply BitVec.eq_of_toNat_eq; simp
              have hmL3_fc : (lcnfObjMem fc ⋆ (lcnfHeap curObjs ⋆ F_L3)) mL3 := sep_pull2 hmL3
              have hmL3_arr : (array64 (f + 24#64) fc.fields ⋆
                  (cloNonFieldMem fc ⋆ (lcnfHeap curObjs ⋆ F_L3))) mL3 := by
                rw [← hfcAddr]
                exact clo_objMem_focus_fields fc hfcTag hmL3_fc
              refine wp_load_array64 (base := f + 24#64) (xs := fc.fields) (i := j)
                haddrJ hjLt hmL3_arr ?_
              let p : BitVec 64 := fc.fields[j]
              let P_L4 : Tup Val [] → Mem 64 → Prop := fun _ curM4 =>
                ∃ curObjs', CloUnderIncRel (fc.fields.take (j + 1)) objs curObjs' ∧
                  (lcnfHeap curObjs' ⋆ (lcnfObjMem fc ⋆ F_L3)) curM4
              refine wp_join_group P_L4 (fun J4 _ m4 ⟨curObjs', hRel', hm4'⟩ => by
                t_wp_unfold
                have hjBV1 : jBV + 1#64 = BitVec.ofNat 64 (j + 1) := by
                  rw [hjBV]; apply BitVec.eq_of_toNat_eq; simp
                rw [hjBV1]
                exact hIH3 (nfix - (j + 1)) (BitVec.ofNat 64 (j + 1), ()) m4 (by omega)
                  ⟨j + 1, curObjs', rfl, by omega, rfl, hRel', hm4'⟩) ?_
              intro J4 hJ4
              clo_pure_steps
              refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
              dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
              constructor
              · intro hpEvenEq
                have hpEven : p &&& 1#64 = 0#64 := of_decide_eq_true hpEvenEq
                obtain ⟨o0, ho0Mem, ho0Addr⟩ := hFieldsMem p (List.getElem_mem hjLt) hpEven
                rw [List.mem_iff_getElem] at ho0Mem
                obtain ⟨idx, hidx0, rfl⟩ := ho0Mem
                rcases hRel with ⟨hlenRel, hClRel, hForallRel⟩
                have hidx : idx < curObjs.length := by omega
                have hmemPair : (objs[idx], curObjs[idx]) ∈ objs.zip curObjs := by
                  rw [List.mem_iff_getElem]
                  exact ⟨idx, by rw [List.length_zip, hlenRel, Nat.min_self]; exact hidx0, by simp [List.getElem_zip]⟩
                have hrow := hForallRel _ hmemPair
                dsimp only at hrow
                rcases hrow with ⟨hCurWf, hCurAddr, _, _, _, _, _, _, _, _, _, _, _, hCurRc⟩
                have hCurAddrP : curObjs[idx].addr = p := by rw [hCurAddr, ho0Addr]
                have huniq : ∀ j' (hj' : j' < curObjs.length), j' ≠ idx → curObjs[j'].addr ≠ p := by
                  intro j' hj' hji
                  rw [← hCurAddrP]
                  exact heap_idx_unique hmL3 hidx j' hj' hji
                have hmL3_obj : (cell64 p curObjs[idx].header ⋆
                    ((lcnfObjBody curObjs[idx] ⋆
                      (lcnfHeap (curObjs.take idx) ⋆ lcnfHeap (curObjs.drop (idx + 1)))) ⋆
                      (lcnfObjMem fc ⋆ F_L3))) mL3 := by
                  have h1 := hmL3
                  rw [lcnfHeap_focus curObjs hidx] at h1
                  rw [lcnfObjMem_eq_header_body curObjs[idx], hCurAddrP] at h1
                  exact sep_assoc_lr (sep_map_left sep_assoc_lr h1)
                refine wp_load_cell64 (a := Arg.var p) hmL3_obj ?_
                clo_pure_steps
                have hcurCs := hCurWf.2.2.2.1
                have hcurOth := hCurWf.2.2.2.2.1
                have hcurTag := hCurWf.2.2.2.2.2.1
                have hcurRcNn := hCurWf.2.2.1
                rw [LcnfObj.header_rc curObjs[idx] hcurCs hcurOth hcurTag]
                refine wp_join_group P_L4 (fun _ _ m5 hm5 => by dsimp; exact hJ4 () m5 hm5) ?_
                intro J5 hJ5
                refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
                dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
                constructor
                · intro hRcNzEq
                  have hRcNz64 : BitVec.ofNat 64 curObjs[idx].rc.toNat ≠ 0#64 := of_decide_eq_true hRcNzEq
                  have hRcNz32 : curObjs[idx].rc ≠ 0#32 := by
                    intro h0; apply hRcNz64; rw [h0]; rfl
                  have hbound : curObjs[idx].rc.toInt < 2147483647 := by
                    rcases hCurRc with ⟨_, hz⟩ | ⟨hpos0, hrcSum⟩
                    · exfalso; exact hRcNz32 hz
                    · have hle : (fc.fields.take j).count p + 1 ≤ fc.fields.count p := by
                        simpa [p] using list_count_take_lt fc.fields hjLt
                      have hB := hRcBound objs[idx] (List.getElem_mem hidx0) hpos0
                      rw [ho0Addr] at hB
                      rw [hrcSum, ho0Addr]
                      omega
                  refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
                  dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
                  constructor
                  · intro _hUltBound
                    clo_pure_steps
                    refine wp_store_cell64 (v0 := curObjs[idx].header) (v := Arg.var _)
                      (a := Arg.var p) hmL3_obj ?_
                    intro mL3' hmL3'
                    dsimp only [Arg.val] at hmL3'
                    have hHdrAdd := lcnfObjHeader_add1 curObjs[idx] hcurCs hcurOth hcurTag hcurRcNn hbound
                    rw [hHdrAdd] at hmL3'
                    have hmL3'_heap : (lcnfHeap (curObjs.set idx (curObjs[idx].withRc (curObjs[idx].rc + 1#32))) ⋆
                        (lcnfObjMem fc ⋆ F_L3)) mL3' := by
                      rw [lcnfHeap_set curObjs hidx]
                      have hm1 := sep_map_left sep_assoc_rl (sep_assoc_rl hmL3')
                      have hm2 := sep_map_left (sep_map_left (sep_map_right fun hb => by
                        rw [← lcnfObjBody_withRc curObjs[idx] (curObjs[idx].rc + 1#32)] at hb; exact hb)) hm1
                      have haddr' : (curObjs[idx].withRc (curObjs[idx].rc + 1#32)).addr = p := hCurAddrP
                      rw [← haddr', ← lcnfObjMem_eq_header_body (curObjs[idx].withRc (curObjs[idx].rc + 1#32))] at hm2
                      exact hm2
                    dsimp
                    apply hJ5 () mL3'
                    refine ⟨curObjs.set idx (curObjs[idx].withRc (curObjs[idx].rc + 1#32)), ?_, hmL3'_heap⟩
                    rw [← List.take_append_getElem hjLt]
                    exact cloUnderIncRel_step_pos ⟨hlenRel, hClRel, hForallRel⟩ hidx hCurAddrP
                      hRcNz32 hbound huniq
                  · intro hNotUlt
                    exfalso
                    have hrcNat : curObjs[idx].rc.toNat < 2147483647 := by
                      rw [BitVec.toInt_eq_toNat_cond] at hcurRcNn hbound
                      split at hbound <;> omega
                    have hUltTrue : (BitVec.ofNat 64 curObjs[idx].rc.toNat).ult (2147483647#64) = true := by
                      have hrc64 : (BitVec.ofNat 64 curObjs[idx].rc.toNat).toNat = curObjs[idx].rc.toNat :=
                        Nat.mod_eq_of_lt (by omega)
                      have h214 : (2147483647#64).toNat = 2147483647 := by decide
                      simp only [BitVec.ult, hrc64, h214, decide_eq_true_eq]; omega
                    rw [hUltTrue] at hNotUlt; contradiction
                · intro hRcZEq
                  have hRcZ64 : BitVec.ofNat 64 curObjs[idx].rc.toNat = 0#64 :=
                    Classical.byContradiction (of_decide_eq_false hRcZEq)
                  have hRcZ32 : curObjs[idx].rc = 0#32 := by
                    apply BitVec.eq_of_toNat_eq
                    have := congrArg BitVec.toNat hRcZ64
                    simpa [Nat.mod_eq_of_lt (by omega : curObjs[idx].rc.toNat < 2 ^ 64)] using this
                  apply hJ5 () mL3
                  refine ⟨curObjs, ?_, hmL3⟩
                  rw [← List.take_append_getElem hjLt]
                  exact cloUnderIncRel_step_zero ⟨hlenRel, hClRel, hForallRel⟩ hidx hCurAddrP hRcZ32 huniq
              · intro hpOddEq
                have hpOdd : p &&& 1#64 ≠ 0#64 := of_decide_eq_false hpOddEq
                apply hJ4 () mL3
                refine ⟨curObjs, ?_, hmL3⟩
                rw [← List.take_append_getElem hjLt]
                exact cloUnderIncRel_step_skip hRel hpOdd
            · intro hjNotUlt
              have hjEq : j = nfix := by
                rw [hjBV] at hjNotUlt
                have hj64 : (BitVec.ofNat 64 j).toNat = j := Nat.mod_eq_of_lt (by omega)
                have hn64 : (BitVec.ofNat 64 nfix).toNat = nfix := Nat.mod_eq_of_lt (by omega)
                have : (BitVec.ofNat 64 j).ult (BitVec.ofNat 64 nfix) = decide (j < nfix) := by
                  simp [BitVec.ult, hj64, hn64]
                rw [this] at hjNotUlt
                have : ¬ j < nfix := of_decide_eq_false hjNotUlt
                omega
              subst hjEq
              have hRelFull : CloUnderIncRel fc.fields objs curObjs := by
                have htake : List.take nfix fc.fields = fc.fields :=
                  List.take_of_length_le (Nat.le_refl _)
                rw [htake] at hRel
                exact hRel
              refine wp_join_group (fun _ m6 => Q (c, ()) m6) (fun _ _ m6 hQ => by dsimp; exact hJ2 () m6 hQ) ?_
              intro J6 hJ6
              refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
              dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
              constructor
              · intro hgt1Eq
                have hgt1 : 1 < fc.rc.toNat := by
                  have hlt := hgt1Eq
                  have hrc64 : (BitVec.ofNat 64 fc.rc.toNat).toNat = fc.rc.toNat :=
                    Nat.mod_eq_of_lt (by omega)
                  have h1m : (1#64).toNat = 1 := by decide
                  rw [BitVec.ult, h1m, hrc64] at hlt
                  exact of_decide_eq_true hlt
                refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
                dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
                constructor
                · intro hlt214Eq
                  have hltInt : fc.rc.toInt < 2147483648 := by
                    have hrc64 : (BitVec.ofNat 64 fc.rc.toNat).toNat = fc.rc.toNat :=
                      Nat.mod_eq_of_lt (by omega)
                    have h214 : (2147483648#64).toNat = 2147483648 := by decide
                    rw [BitVec.ult, hrc64, h214] at hlt214Eq
                    have hltNat : fc.rc.toNat < 2147483648 := of_decide_eq_true hlt214Eq
                    rw [BitVec.toInt_eq_toNat_cond]
                    split <;> omega
                  clo_pure_steps
                  have hmL3_hdr : (cell64 f fc.header ⋆
                      (lcnfObjBody fc ⋆ (lcnfHeap curObjs ⋆ F_L3))) mL3 := by
                    have h1 := sep_pull2 hmL3
                    rw [lcnfObjMem_eq_header_body fc, hfcAddr] at h1
                    exact sep_assoc_lr h1
                  refine wp_store_cell64 (v0 := fc.header) (v := Arg.var _)
                    (a := Arg.var f) hmL3_hdr ?_
                  intro mL3' hmL3'
                  rw [clo_objMem_header_sub1 fc hfcWf hgt1 hltInt] at hmL3'
                  have hmL3'_fc : (lcnfHeap curObjs ⋆ (lcnfObjMem (fc.withRc (fc.rc - 1#32)) ⋆ F_L3)) mL3' := by
                    have h1 := sep_assoc_rl hmL3'
                    have h2 : ((cell64 f (fc.withRc (fc.rc - 1#32)).header ⋆
                        lcnfObjBody (fc.withRc (fc.rc - 1#32))) ⋆ (lcnfHeap curObjs ⋆ F_L3)) mL3' :=
                      sep_map_left (sep_map_right (fun hb => by
                        rw [← lcnfObjBody_withRc fc (fc.rc - 1#32)] at hb; exact hb)) h1
                    have haddr' : (fc.withRc (fc.rc - 1#32)).addr = f := hfcAddr
                    rw [← haddr', ← lcnfObjMem_eq_header_body (fc.withRc (fc.rc - 1#32))] at h2
                    exact sep_pull2 h2
                  dsimp
                  apply hJ6 () mL3'
                  refine hPost c st' curObjs mL3' hcNe0 hcAlign hMeta1 hRem1
                    (by simp only [hrcNe1, ↓reduceIte]; exact hRelFull) ?_
                  have hrcNz : fc.rc ≠ 0#32 := by
                    intro h0
                    have hrc0Nat : fc.rc.toNat = 0 := by rw [h0]; rfl
                    omega
                  simp only [hrcNe1, ↓reduceIte, hrcNz]
                  have hmL3'_ord : (rtC0Inv rt st' ⋆ C_mem ⋆ lcnfObjMem (fc.withRc (fc.rc - 1#32)) ⋆
                      lcnfHeap curObjs ⋆ R) mL3' := by
                    dsimp [F_L3] at hmL3'_fc
                    exact sep_cast hmL3'_fc (by ac_rfl)
                  dsimp [C_mem, sz, nfix] at hmL3'_ord
                  exact clo_unpack_post hmL3'_ord
                · intro hNotUlt214
                  exfalso
                  have hrcToNatLt : fc.rc.toNat < 2147483648 := by
                    rw [BitVec.toInt_eq_toNat_cond] at hrc_nn
                    split at hrc_nn <;> omega
                  have hUltTrue : (1#64).ult (BitVec.ofNat 64 fc.rc.toNat) = true ∧
                      (BitVec.ofNat 64 fc.rc.toNat).ult (2147483648#64) = true := by
                    have hrc64 : (BitVec.ofNat 64 fc.rc.toNat).toNat = fc.rc.toNat :=
                      Nat.mod_eq_of_lt (by omega)
                    have h1m : (1#64).toNat = 1 := by decide
                    have h214 : (2147483648#64).toNat = 2147483648 := by decide
                    simp only [BitVec.ult, hrc64, h1m, h214, decide_eq_true_eq]
                    omega
                  rw [hUltTrue.2] at hNotUlt214; contradiction
              · intro hNotGt1
                have hrc0 : fc.rc = 0#32 := by
                  have hrc64 : (BitVec.ofNat 64 fc.rc.toNat).toNat = fc.rc.toNat :=
                    Nat.mod_eq_of_lt (by omega)
                  have h1m : (1#64).toNat = 1 := by decide
                  rw [BitVec.ult, h1m, hrc64] at hNotGt1
                  have hnot1 : ¬ 1 < fc.rc.toNat := of_decide_eq_false hNotGt1
                  have hle1 : fc.rc.toNat ≤ 1 := Nat.le_of_not_lt hnot1
                  have hne1Nat : fc.rc.toNat ≠ 1 := fun h1 => hrcNe1 (BitVec.eq_of_toNat_eq (by simp [h1]))
                  apply BitVec.eq_of_toNat_eq; simp; omega
                apply hJ6 () mL3
                refine hPost c st' curObjs mL3 hcNe0 hcAlign hMeta1 hRem1
                  (by simp only [hrcNe1, ↓reduceIte]; exact hRelFull) ?_
                simp only [↓reduceIte, hrc0]
                have hsub0 : (0#32 - 0#32 : BitVec 32) = 0#32 := rfl
                rw [hsub0, clo_withRc_zero fc hrc0]
                have hmL3_ord : (rtC0Inv rt st' ⋆ C_mem ⋆ lcnfObjMem fc ⋆ lcnfHeap curObjs ⋆ R) mL3 := by
                  dsimp [F_L3] at hmL3
                  exact sep_cast hmL3 (by ac_rfl)
                dsimp [C_mem, sz, nfix] at hmL3_ord
                exact clo_unpack_post hmL3_ord

/-! ## M0a Verified Runtime Table (`rtC0M0aEnv`, `rtR0ModM0a_ok`) -/

def rtC0M0aSpecEntries : List SpecEntry :=
  [ SpecEntry.ofFn lcnf_alloc lcnfAllocSpec true
  , SpecEntry.ofFn lcnf_free_obj lcnfFreeObjSpec true
  , SpecEntry.ofFn lcnf_clo_under lcnfCloUnderSpec true
  ]

theorem rtC0M0aSpecEntries_nodup : (rtC0M0aSpecEntries.map SpecEntry.name).Nodup := by decide

def rtC0M0aEnv : Env := Env.ofTable rtC0M0aSpecEntries

theorem rtC0M0aEnv_alloc : ∀ xs m Q X,
    lcnfAllocSpec xs m Q X → rtC0M0aEnv "lcnf_alloc" [i64, i64] [i64] xs m Q X :=
  fun _ _ _ _ h => Env.ofTable_of_mem (e := SpecEntry.ofFn lcnf_alloc lcnfAllocSpec true)
    (by simp [rtC0M0aSpecEntries]) rtC0M0aSpecEntries_nodup h

theorem rtC0M0aEnv_free_obj : ∀ xs m Q X,
    lcnfFreeObjSpec xs m Q X → rtC0M0aEnv "lcnf_free_obj" [i64, i64] [] xs m Q X :=
  fun _ _ _ _ h => Env.ofTable_of_mem (e := SpecEntry.ofFn lcnf_free_obj lcnfFreeObjSpec true)
    (by simp [rtC0M0aSpecEntries]) rtC0M0aSpecEntries_nodup h

theorem rtC0M0aEnv_clo_under : ∀ xs m Q X,
    lcnfCloUnderSpec xs m Q X → rtC0M0aEnv "lcnf_clo_under" [i64, i64, i64] [i64] xs m Q X :=
  fun _ _ _ _ h => Env.ofTable_of_mem (e := SpecEntry.ofFn lcnf_clo_under lcnfCloUnderSpec true)
    (by simp [rtC0M0aSpecEntries]) rtC0M0aSpecEntries_nodup h

def rtR0ModM0a : Module :=
  { fns := [lcnf_alloc, lcnf_free_obj, lcnf_clo_under], exits := ["lcnf_panic"] }

theorem rtR0ModM0a_checkAcyclic : rtR0ModM0a.checkAcyclic = true := by decide

theorem rtR0ModM0a_ok : ModuleOk rtC0M0aEnv rtR0ModM0a := by
  refine Env.ofTable_moduleOk rtR0ModM0a_checkAcyclic ?_ ?_
  · refine ⟨lcnf_alloc_wf, lcnf_free_obj_wf, lcnf_clo_under_wf, trivial⟩
  · refine ⟨⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h => lcnf_alloc_wp rtC0M0aEnv xs m Q X h⟩,
      ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h => lcnf_free_obj_wp rtC0M0aEnv xs m Q X h⟩,
      ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h =>
        lcnf_clo_under_wp rtC0M0aEnv rtC0M0aEnv_alloc rtC0M0aEnv_free_obj xs m Q X h⟩,
      trivial⟩

theorem rtC0Env_clo_under_wp : ∀ xs m Q X,
    lcnfCloUnderSpec xs m Q X → Func.wp rtC0Env lcnf_clo_under.body xs m Q X :=
  lcnf_clo_under_wp rtC0Env rtC0Env_alloc rtC0Env_free_obj

/-! ## Shared DFS, Worklist, and Heap Helpers -/

private def SameNonRc (a b : LcnfObj) : Prop :=
  b.addr = a.addr ∧ b.csSz = a.csSz ∧ b.other = a.other ∧ b.tag = a.tag ∧
  b.funId = a.funId ∧ b.arity = a.arity ∧ b.cap = a.cap ∧ b.arrSize = a.arrSize ∧
  b.strLen = a.strLen ∧ b.fields = a.fields ∧ b.scalarData = a.scalarData ∧ b.limbs = a.limbs

private theorem SameNonRc.refl (a : LcnfObj) : SameNonRc a a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem SameNonRc.trans {a b c : LcnfObj} (h1 : SameNonRc a b) (h2 : SameNonRc b c) :
    SameNonRc a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
   h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2.2.2.2.2.2⟩

private theorem SameNonRc.withRc_r {a b : LcnfObj} (h : SameNonRc a b) (rc' : BitVec 32) :
    SameNonRc a (b.withRc rc') := h

private theorem SameNonRc.childFields_eq {a b : LcnfObj} (h : SameNonRc a b) :
    b.childFields = a.childFields := by
  unfold LcnfObj.childFields
  rw [h.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1]

private def LcnfObj.fieldsOff (o : LcnfObj) : BitVec 64 :=
  if o.tag = closureTag ∨ o.tag = arrayTag then 24#64 else 8#64

private theorem objWf_childFields_lt {o : LcnfObj} (hwf : o.Wf) :
    o.childFields.length < 2 ^ 64 := by
  unfold LcnfObj.childFields
  rcases hwf with ⟨_, _, _, _, hoth, _, _, _, _, hsp⟩
  by_cases hc : o.tag = closureTag
  · simp only [hc, true_or, or_true, ↓reduceIte] at hsp ⊢; have := hsp.2.1; omega
  · by_cases ha : o.tag = arrayTag
    · simp only [ha, show arrayTag ≠ closureTag by decide, or_true, ↓reduceIte] at hsp ⊢
      have := hsp.1; have := hsp.2; omega
    · by_cases hsa : o.tag = sarrayTag
      · simp [hsa, closureTag, arrayTag, sarrayTag]
      · by_cases hstr : o.tag = stringTag
        · simp [hstr, closureTag, arrayTag, stringTag]
        · by_cases hmpz : o.tag = mpzTag
          · simp [hmpz, closureTag, arrayTag, mpzTag]
          · simp only [hc, ha, hsa, hstr, hmpz, ↓reduceIte] at hsp
            have h1 := hsp.1; have h2 := hsp.2.1
            simp only [h1, true_or, ↓reduceIte]; omega

private theorem objWf_addr_even {o : LcnfObj} (hwf : o.Wf) :
    (o.addr &&& 1#64) = 0#64 := by
  have hal := hwf.2.1
  apply BitVec.eq_of_toNat_eq
  have h1m : (1#64).toNat = 1 := by decide
  have h0m : (0#64).toNat = 0 := by decide
  rw [BitVec.toNat_and, h1m, Nat.and_one_is_mod, h0m]; omega

private theorem objWf_rc_pos {o : LcnfObj} (hwf : o.Wf) (hnz : o.rc ≠ 0#32) :
    0 < o.rc.toInt := by
  have hnn := hwf.2.2.1
  rw [BitVec.toInt_eq_toNat_cond] at hnn ⊢
  have hne0 : o.rc.toNat ≠ 0 := fun hz => hnz (BitVec.eq_of_toNat_eq hz)
  split at hnn <;> simp_all <;> omega

private theorem objWf_rc_lt {o : LcnfObj} (hwf : o.Wf) :
    o.rc.toNat < 2147483648 := by
  have hnn := hwf.2.2.1
  rw [BitVec.toInt_eq_toNat_cond] at hnn
  split at hnn <;> omega

private theorem objWf_withRc_zero {o : LcnfObj} (hwf : o.Wf) :
    (o.withRc 0#32).Wf :=
  lcnfObjWf_withRc hwf (by decide)

private theorem objWf_rc_sub1_toInt {o : LcnfObj} (hwf : o.Wf) (hgt : 1 < o.rc.toNat) :
    (o.rc - 1#32).toInt = o.rc.toInt - 1 := by
  have hlt := objWf_rc_lt hwf
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  have hsub : (o.rc - 1#32).toNat = o.rc.toNat - 1 := by bv_omega
  rw [hsub]
  split <;> split <;> omega

private theorem objRc_sub1_toNat {o : LcnfObj} (hgt : 1 < o.rc.toNat) :
    (o.rc - 1#32).toNat = o.rc.toNat - 1 := by
  bv_omega

private def RtC0State.withWorkBuf (st : RtC0State) (wb : List (BitVec 64))
    (hlen : wb.length = st.hdr.s_work_cap.toNat) : RtC0State where
  extraArgs := st.extraArgs
  globals := st.globals
  freeList := st.freeList
  hdr := st.hdr
  workBuf := wb
  smallPools := st.smallPools
  largeNodes := st.largeNodes
  extraLen := st.extraLen
  globalsLen := st.globalsLen
  freeListLen := st.freeListLen
  workLen := hlen
  curLeEnd := st.curLeEnd
  arenaAlign := st.arenaAlign
  curNz := st.curNz

private def RtC0State.withColdDecsInc (st : RtC0State) : RtC0State where
  extraArgs := st.extraArgs
  globals := st.globals
  freeList := st.freeList
  hdr := { st.hdr with s_st_cold_decs := st.hdr.s_st_cold_decs + 1#64 }
  workBuf := st.workBuf
  smallPools := st.smallPools
  largeNodes := st.largeNodes
  extraLen := st.extraLen
  globalsLen := st.globalsLen
  freeListLen := st.freeListLen
  workLen := st.workLen
  curLeEnd := st.curLeEnd
  arenaAlign := st.arenaAlign
  curNz := st.curNz

private def RtC0State.withPersistInc (st : RtC0State) : RtC0State where
  extraArgs := st.extraArgs
  globals := st.globals
  freeList := st.freeList
  hdr := { st.hdr with s_st_persistent := st.hdr.s_st_persistent + 1#64 }
  workBuf := st.workBuf
  smallPools := st.smallPools
  largeNodes := st.largeNodes
  extraLen := st.extraLen
  globalsLen := st.globalsLen
  freeListLen := st.freeListLen
  workLen := st.workLen
  curLeEnd := st.curLeEnd
  arenaAlign := st.arenaAlign
  curNz := st.curNz

private theorem sep_pull_heap {rt : BitVec 64} {st : RtC0State} {objs : List LcnfObj}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m) :
    (lcnfHeap objs ⋆ (rtC0Inv rt st ⋆ R)) m :=
  sep_cast hm (by ac_rfl)

private theorem rtC0Inv_hdr_focus {rt : BitVec 64} {st : RtC0State} {H R : Mem 64 → Prop}
    {m : Mem 64} (hm : (rtC0Inv rt st ⋆ H ⋆ R) m) :
    (LcnfC0Rt.At rt st.hdr ⋆
      (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
        array64 (rt + 33024#64) st.freeList ⋆ array64 st.hdr.s_work st.workBuf ⋆
        smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
        largeFreeList st.hdr.s_large_free st.largeNodes ⋆
        region st.hdr.s_cur st.rem ⋆ H ⋆ R)) m := by
  unfold rtC0Inv at hm
  exact sep_cast hm (by ac_rfl)

private theorem rtC0Inv_work_focus {rt : BitVec 64} {st : RtC0State} {H R : Mem 64 → Prop}
    {m : Mem 64} (hm : (rtC0Inv rt st ⋆ H ⋆ R) m) :
    (array64 st.hdr.s_work st.workBuf ⋆
      (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
        array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
        smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
        largeFreeList st.hdr.s_large_free st.largeNodes ⋆
        region st.hdr.s_cur st.rem ⋆ H ⋆ R)) m := by
  unfold rtC0Inv at hm
  exact sep_cast hm (by ac_rfl)

private theorem rtC0Inv_load_s_work {rt : BitVec 64} {st : RtC0State} {H R : Mem 64 → Prop}
    {m : Mem 64} (hm : (rtC0Inv rt st ⋆ H ⋆ R) m) :
    loadVal m i64 (rt + 33568#64) = some st.hdr.s_work :=
  LcnfC0Rt.load_s_work (rtC0Inv_hdr_focus hm)

private theorem rtC0Inv_load_s_work_cap {rt : BitVec 64} {st : RtC0State} {H R : Mem 64 → Prop}
    {m : Mem 64} (hm : (rtC0Inv rt st ⋆ H ⋆ R) m) :
    loadVal m i64 (rt + 33576#64) = some st.hdr.s_work_cap :=
  LcnfC0Rt.load_s_work_cap (rtC0Inv_hdr_focus hm)

private theorem rtC0Inv_load_s_st_cold_decs {rt : BitVec 64} {st : RtC0State} {H R : Mem 64 → Prop}
    {m : Mem 64} (hm : (rtC0Inv rt st ⋆ H ⋆ R) m) :
    loadVal m i64 (rt + 33656#64) = some st.hdr.s_st_cold_decs :=
  LcnfC0Rt.load_s_st_cold_decs (rtC0Inv_hdr_focus hm)

private theorem rtC0Inv_store_s_st_cold_decs {rt : BitVec 64} {st : RtC0State}
    {H R : Mem 64 → Prop} {m : Mem 64} (hm : (rtC0Inv rt st ⋆ H ⋆ R) m) :
    storeOk m i64 (rt + 33656#64) ∧
      ((rtC0Inv rt st.withColdDecsInc ⋆ H) ⋆ R)
        (storeMem m i64 (rt + 33656#64) (st.hdr.s_st_cold_decs + 1#64)) := by
  have h1 := LcnfC0Rt.store_s_st_cold_decs (st.hdr.s_st_cold_decs + 1#64) (rtC0Inv_hdr_focus hm)
  refine ⟨h1.1, ?_⟩
  unfold rtC0Inv
  exact sep_cast h1.2 (by ac_rfl)

private theorem rtC0Inv_load_s_st_persistent {rt : BitVec 64} {st : RtC0State}
    {H R : Mem 64 → Prop} {m : Mem 64} (hm : (rtC0Inv rt st ⋆ H ⋆ R) m) :
    loadVal m i64 (rt + 33640#64) = some st.hdr.s_st_persistent :=
  LcnfC0Rt.load_s_st_persistent (rtC0Inv_hdr_focus hm)

private theorem rtC0Inv_store_s_st_persistent {rt : BitVec 64} {st : RtC0State}
    {H R : Mem 64 → Prop} {m : Mem 64} (hm : (rtC0Inv rt st ⋆ H ⋆ R) m) :
    storeOk m i64 (rt + 33640#64) ∧
      ((rtC0Inv rt st.withPersistInc ⋆ H) ⋆ R)
        (storeMem m i64 (rt + 33640#64) (st.hdr.s_st_persistent + 1#64)) := by
  have h1 := LcnfC0Rt.store_s_st_persistent (st.hdr.s_st_persistent + 1#64) (rtC0Inv_hdr_focus hm)
  refine ⟨h1.1, ?_⟩
  unfold rtC0Inv
  exact sep_cast h1.2 (by ac_rfl)

private theorem rtC0Inv_load_work {rt : BitVec 64} {st : RtC0State} {H R : Mem 64 → Prop}
    {m : Mem 64} {i : Nat} (hi : i < st.workBuf.length) (hm : (rtC0Inv rt st ⋆ H ⋆ R) m) :
    loadVal m i64 (st.hdr.s_work + BitVec.ofNat 64 (8 * i)) = some (st.workBuf[i]'hi) :=
  loadVal_array64 hi (rtC0Inv_work_focus hm)

private theorem rtC0Inv_store_work {rt : BitVec 64} {st : RtC0State} {H R : Mem 64 → Prop}
    {m : Mem 64} {i : Nat} (hi : i < st.workBuf.length) (v : BitVec 64)
    (hm : (rtC0Inv rt st ⋆ H ⋆ R) m) :
    storeOk m i64 (st.hdr.s_work + BitVec.ofNat 64 (8 * i)) ∧
      ((rtC0Inv rt (st.withWorkBuf (st.workBuf.set i v) (by rw [List.length_set]; exact st.workLen))
        ⋆ H) ⋆ R) (storeMem m i64 (st.hdr.s_work + BitVec.ofNat 64 (8 * i)) v) := by
  have h1 := store_array64 v hi (rtC0Inv_work_focus hm)
  refine ⟨h1.1, ?_⟩
  unfold rtC0Inv
  exact sep_cast h1.2 (by ac_rfl)

private theorem lcnfObjMem_load_header {o : LcnfObj} {F : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o ⋆ F) m) : loadVal m i64 o.addr = some o.header := by
  rw [lcnfObjMem_eq_header_body] at hm
  exact loadVal_cell64 (sep_assoc_lr hm)

private theorem lcnfObjMem_load_cloMeta {o : LcnfObj} (ht : o.tag = closureTag)
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (lcnfObjMem o ⋆ F) m) :
    loadVal m i64 (o.addr + 16#64) = some o.cloMeta := by
  unfold lcnfObjMem at hm
  rw [ite_eq_left ht] at hm
  have h1 : (cell64 (o.addr + 16#64) o.cloMeta ⋆
      (cell64 o.addr o.header ⋆ cell64 (o.addr + 8#64) o.funId ⋆
        array64 (o.addr + 24#64) o.fields ⋆
        region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
          (o.csSz - (24 + 8 * o.fields.length)) ⋆ F)) m :=
    sep_cast hm (by ac_rfl)
  exact loadVal_cell64 h1

private theorem lcnfObjMem_load_arrSize {o : LcnfObj} (ht : o.tag = arrayTag)
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (lcnfObjMem o ⋆ F) m) :
    loadVal m i64 (o.addr + 8#64) = some (BitVec.ofNat 64 o.fields.length) := by
  unfold lcnfObjMem at hm
  rw [ite_eq_right (by rw [ht]; decide), ite_eq_left ht] at hm
  have h1 : (cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.fields.length) ⋆
      (cell64 o.addr o.header ⋆ cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
        array64 (o.addr + 24#64) o.fields ⋆
        region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
          (8 * (o.cap - o.fields.length)) ⋆ F)) m :=
    sep_cast hm (by ac_rfl)
  exact loadVal_cell64 h1

private theorem lcnfObjMem_load_child {o : LcnfObj} (_hwf : o.Wf) {F : Mem 64 → Prop}
    {m : Mem 64} (hm : (lcnfObjMem o ⋆ F) m) {i : Nat} (hi : i < o.childFields.length) :
    loadVal m i64 ((o.addr + o.fieldsOff) + BitVec.ofNat 64 (8 * i)) =
      some (o.childFields[i]'hi) := by
  unfold lcnfObjMem at hm
  unfold LcnfObj.fieldsOff
  unfold LcnfObj.childFields at hi ⊢
  by_cases hc : o.tag = closureTag
  · simp only [hc, ↓reduceIte, true_or, or_true] at hm hi ⊢
    have h1 : (array64 (o.addr + 24#64) o.fields ⋆
        (cell64 o.addr o.header ⋆ cell64 (o.addr + 8#64) o.funId ⋆
          cell64 (o.addr + 16#64) o.cloMeta ⋆
          region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
            (o.csSz - (24 + 8 * o.fields.length)) ⋆ F)) m :=
      sep_cast hm (by ac_rfl)
    exact loadVal_array64 hi h1
  · by_cases ha : o.tag = arrayTag
    · simp only [ha, show arrayTag ≠ closureTag by decide, ↓reduceIte, or_true] at hm hi ⊢
      have h1 : (array64 (o.addr + 24#64) o.fields ⋆
          (cell64 o.addr o.header ⋆ cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.fields.length) ⋆
            cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
            region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
              (8 * (o.cap - o.fields.length)) ⋆ F)) m :=
        sep_cast hm (by ac_rfl)
      exact loadVal_array64 hi h1
    · by_cases hle : o.tag ≤ 244
      · have hsa : o.tag ≠ sarrayTag := by unfold sarrayTag; omega
        have hstr : o.tag ≠ stringTag := by unfold stringTag; omega
        have hmpz : o.tag ≠ mpzTag := by unfold mpzTag; omega
        simp only [hc, ha, hsa, hstr, hmpz, hle, true_or, or_self, ↓reduceIte] at hm hi ⊢
        have h1 : (array64 (o.addr + 8#64) o.fields ⋆
            (cell64 o.addr o.header ⋆
              bytes (o.addr + BitVec.ofNat 64 (8 + 8 * o.fields.length)) o.scalarData ⋆
              region (o.addr + BitVec.ofNat 64 (8 + 8 * o.fields.length + o.scalarData.length))
                (o.csSz - (8 + 8 * o.fields.length + o.scalarData.length)) ⋆ F)) m :=
          sep_cast hm (by ac_rfl)
        exact loadVal_array64 hi h1
      · simp only [hc, ha, hle, or_self, ↓reduceIte] at hi
        simp at hi

private theorem lcnfObjMem_store_rc {o : LcnfObj} (rc' : BitVec 32) {F : Mem 64 → Prop}
    {m : Mem 64} (hm : (lcnfObjMem o ⋆ F) m) :
    storeOk m i64 o.addr ∧
      (lcnfObjMem (o.withRc rc') ⋆ F) (storeMem m i64 o.addr (o.withRc rc').header) := by
  rw [lcnfObjMem_eq_header_body] at hm
  have h1 := store_cell64 (o.withRc rc').header (sep_assoc_lr hm)
  refine ⟨h1.1, ?_⟩
  rw [lcnfObjMem_eq_header_body, lcnfObjBody_withRc]
  exact sep_assoc_rl h1.2

private theorem lcnfHeap_load_header {objs : List LcnfObj} {idx : Nat} (hidx : idx < objs.length)
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (lcnfHeap objs ⋆ F) m) :
    loadVal m i64 objs[idx].addr = some objs[idx].header := by
  rw [lcnfHeap_focus objs hidx] at hm
  exact lcnfObjMem_load_header (sep_assoc_lr hm)

private theorem lcnfHeap_load_cloMeta {objs : List LcnfObj} {idx : Nat} (hidx : idx < objs.length)
    (ht : objs[idx].tag = closureTag) {F : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfHeap objs ⋆ F) m) :
    loadVal m i64 (objs[idx].addr + 16#64) = some objs[idx].cloMeta := by
  rw [lcnfHeap_focus objs hidx] at hm
  exact lcnfObjMem_load_cloMeta ht (sep_assoc_lr hm)

private theorem lcnfHeap_load_arrSize {objs : List LcnfObj} {idx : Nat} (hidx : idx < objs.length)
    (ht : objs[idx].tag = arrayTag) {F : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfHeap objs ⋆ F) m) :
    loadVal m i64 (objs[idx].addr + 8#64) = some (BitVec.ofNat 64 objs[idx].fields.length) := by
  rw [lcnfHeap_focus objs hidx] at hm
  exact lcnfObjMem_load_arrSize ht (sep_assoc_lr hm)

private theorem lcnfHeap_load_child {objs : List LcnfObj} {idx : Nat} (hidx : idx < objs.length)
    (hwf : objs[idx].Wf) {F : Mem 64 → Prop} {m : Mem 64} (hm : (lcnfHeap objs ⋆ F) m)
    {i : Nat} (hi : i < objs[idx].childFields.length) :
    loadVal m i64 ((objs[idx].addr + objs[idx].fieldsOff) + BitVec.ofNat 64 (8 * i)) =
      some (objs[idx].childFields[i]'hi) := by
  rw [lcnfHeap_focus objs hidx] at hm
  exact lcnfObjMem_load_child hwf (sep_assoc_lr hm) hi

private theorem lcnfHeap_store_rc {objs : List LcnfObj} {idx : Nat} (hidx : idx < objs.length)
    (rc' : BitVec 32) {F : Mem 64 → Prop} {m : Mem 64} (hm : (lcnfHeap objs ⋆ F) m) :
    storeOk m i64 objs[idx].addr ∧
      (lcnfHeap (objs.set idx (objs[idx].withRc rc')) ⋆ F)
        (storeMem m i64 objs[idx].addr (objs[idx].withRc rc').header) := by
  rw [lcnfHeap_focus objs hidx] at hm
  have h1 := lcnfObjMem_store_rc rc' (sep_assoc_lr hm)
  refine ⟨h1.1, ?_⟩
  rw [lcnfHeap_set objs hidx]
  exact sep_assoc_rl h1.2

private theorem nodup_getElem_inj {α : Type _} {xs : List α} (hnd : xs.Nodup)
    {i j : Nat} (hi : i < xs.length) (hj : j < xs.length) (heq : xs[i] = xs[j]) : i = j := by
  have hp := List.pairwise_iff_getElem.mp hnd
  by_cases hlt : i < j
  · exact absurd heq (hp i j hi hj hlt)
  · by_cases hgt : j < i
    · exact absurd heq.symm (hp j i hj hi hgt)
    · omega

private theorem lcnfHeap_nodup_addrs {objs : List LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (lcnfHeap objs ⋆ R) m) : (objs.map LcnfObj.addr).Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.length_map] at hi hj
  simp only [List.getElem_map]
  exact lcnfHeap_addr_lt h hij hj

private theorem nodup_addr_eq_of_mem {objs : List LcnfObj} (hnd : (objs.map LcnfObj.addr).Nodup)
    {a b : LcnfObj} (ha : a ∈ objs) (hb : b ∈ objs) (heq : a.addr = b.addr) : a = b := by
  rw [List.mem_iff_getElem] at ha hb
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := hb
  have hij : i = j :=
    nodup_getElem_inj hnd (by simpa using hi) (by simpa using hj) (by simpa using heq)
  subst hij; rfl

private theorem nodup_addr_idx_eq {objs : List LcnfObj} (hnd : (objs.map LcnfObj.addr).Nodup)
    {i j : Nat} (hi : i < objs.length) (hj : j < objs.length)
    (heq : objs[i].addr = objs[j].addr) : i = j :=
  nodup_getElem_inj hnd (by simpa using hi) (by simpa using hj) (by simpa using heq)

private theorem list_take_set_append {α : Type _} (wb : List α) {len : Nat}
    (hlen : len < wb.length) (v : α) :
    (wb.set len v).take (len + 1) = wb.take len ++ [v] := by
  apply List.ext_getElem
  · simp; omega
  · intro j hj1 hj2
    have hlt : j < len + 1 := by
      have : j < min (len + 1) (wb.set len v).length := by simpa [List.length_take] using hj1
      omega
    by_cases hjl : j = len
    · subst hjl
      rw [List.getElem_take, List.getElem_set_self]
      have hlenT : (wb.take j).length = j := List.length_take_of_le (by omega)
      rw [List.getElem_append_right (by omega)]
      simp [hlenT]
    · have hjlt : j < len := by omega
      have hlenT : (wb.take len).length = len := List.length_take_of_le (by omega)
      rw [List.getElem_take, List.getElem_set_ne (Ne.symm hjl)]
      rw [List.getElem_append_left (by omega), List.getElem_take]

private theorem nodup_length_le_of_subset {α : Type _} [DecidableEq α] :
    ∀ (xs ys : List α), xs.Nodup → (∀ a ∈ xs, a ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have hxMem : x ∈ ys := hsub x List.mem_cons_self
    rw [List.mem_iff_getElem] at hxMem
    obtain ⟨idx, hidx, hxEq⟩ := hxMem
    have hsub' : ∀ a ∈ xs, a ∈ ys.eraseIdx idx := by
      intro a ha
      have hne : a ≠ x := fun h => hnd.1 (h ▸ ha)
      have haMem : a ∈ ys := hsub a (List.mem_cons_of_mem _ ha)
      rw [List.mem_iff_getElem] at haMem
      obtain ⟨j, hj, rfl⟩ := haMem
      have hji : j ≠ idx := fun h => hne (by subst h; exact hxEq)
      rw [List.eraseIdx_eq_take_drop_succ, List.mem_append]
      by_cases hlt : j < idx
      · left; rw [List.mem_iff_getElem]
        exact ⟨j, by rw [List.length_take]; omega, by simp [List.getElem_take]⟩
      · right; rw [List.mem_iff_getElem]
        exact ⟨j - (idx + 1), by rw [List.length_drop]; omega,
          by rw [List.getElem_drop]; congr 1; omega⟩
    have ih := nodup_length_le_of_subset xs (ys.eraseIdx idx) hnd.2 hsub'
    rw [List.length_eraseIdx_of_lt hidx] at ih
    simp only [List.length_cons]
    omega

private theorem nodup_addr_length_le {xs : List (BitVec 64)} {objs : List LcnfObj}
    (hnd : xs.Nodup) (hsub : ∀ a ∈ xs, ∃ o ∈ objs, o.addr = a) : xs.length ≤ objs.length := by
  have h1 := nodup_length_le_of_subset xs (objs.map LcnfObj.addr) hnd fun a ha => by
    obtain ⟨o, ho, rfl⟩ := hsub a ha
    exact List.mem_map_of_mem ho
  simpa using h1

private theorem work_push_lt_cap {wl : List (BitVec 64)} {xAddr c : BitVec 64}
    {curObjs : List LcnfObj} {cap : Nat}
    (hnd : wl.Nodup) (hxNot : xAddr ∉ wl) (hcNot : c ∉ wl) (hne : c ≠ xAddr)
    (hxMem : ∃ o ∈ curObjs, o.addr = xAddr) (hcMem : ∃ o ∈ curObjs, o.addr = c)
    (hwlMem : ∀ a ∈ wl, ∃ o ∈ curObjs, o.addr = a) (hcap : curObjs.length ≤ cap) :
    wl.length < cap := by
  have hnd2 : (c :: xAddr :: wl).Nodup := by
    rw [List.nodup_cons, List.nodup_cons]
    exact ⟨fun h => by rcases List.mem_cons.mp h with rfl | h' <;> contradiction, hxNot, hnd⟩
  have hsub : ∀ a ∈ c :: xAddr :: wl, ∃ o ∈ curObjs, o.addr = a := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact hcMem
    · rcases List.mem_cons.mp ha' with rfl | ha''
      · exact hxMem
      · exact hwlMem a ha''
  have hle := nodup_addr_length_le hnd2 hsub
  simp only [List.length_cons] at hle
  omega

private def unmarkedCount (objs : List LcnfObj) : Nat :=
  (objs.filter (fun o => o.rc != 0#32)).length

private theorem unmarkedCount_set_zero :
    ∀ (objs : List LcnfObj) {idx : Nat} (hidx : idx < objs.length),
      objs[idx].rc ≠ 0#32 →
      unmarkedCount (objs.set idx (objs[idx].withRc 0#32)) + 1 = unmarkedCount objs
  | [], _, hi, _ => by simp at hi
  | o :: os, 0, _, hnz => by
    simp only [List.set_cons_zero, List.getElem_cons_zero] at hnz ⊢
    unfold unmarkedCount
    have h1 : (o.rc != 0#32) = true := bne_iff_ne.mpr hnz
    have h2 : ((o.withRc 0#32).rc != 0#32) = false := by simp [LcnfObj.withRc]
    simp [h1, h2]
  | o :: os, idx + 1, hi, hnz => by
    simp only [List.set_cons_succ, List.getElem_cons_succ] at hnz ⊢
    have ih := unmarkedCount_set_zero os (by simp at hi; omega) hnz
    unfold unmarkedCount at ih ⊢
    by_cases h : (o.rc != 0#32) = true
    · simp only [List.filter_cons, h, ↓reduceIte, List.length_cons]; omega
    · have hf : (o.rc != 0#32) = false := Bool.eq_false_iff.mpr h
      simp only [List.filter_cons, hf, Bool.false_eq_true, ↓reduceIte]; exact ih

private theorem nonPersistRefs_foldl_shift (objs : List LcnfObj) (a : BitVec 64) (init : Nat) :
    objs.foldl (fun acc p => if p.rc = 0#32 then acc else acc + p.childFields.count a) init =
      init + nonPersistRefs objs a := by
  unfold nonPersistRefs
  induction objs generalizing init with
  | nil => simp
  | cons o os ih =>
    simp only [List.foldl_cons]
    by_cases h0 : o.rc = 0#32
    · simp only [h0, ↓reduceIte]; exact ih init
    · simp only [h0, ↓reduceIte]
      rw [ih (init + o.childFields.count a), ih (0 + o.childFields.count a)]
      omega

private theorem nonPersistRefs_cons (o : LcnfObj) (os : List LcnfObj) (a : BitVec 64) :
    nonPersistRefs (o :: os) a =
      (if o.rc = 0#32 then 0 else o.childFields.count a) + nonPersistRefs os a := by
  unfold nonPersistRefs
  simp only [List.foldl_cons]
  split
  · simp
  · rw [nonPersistRefs_foldl_shift]
    change 0 + o.childFields.count a + nonPersistRefs os a = _ + nonPersistRefs os a
    omega

private theorem nonPersistRefs_append (xs ys : List LcnfObj) (a : BitVec 64) :
    nonPersistRefs (xs ++ ys) a = nonPersistRefs xs a + nonPersistRefs ys a := by
  induction xs with
  | nil => simp [nonPersistRefs]
  | cons x xs ih =>
    simp only [List.cons_append, nonPersistRefs_cons, ih]; omega

private theorem nonPersistRefs_focus (objs : List LcnfObj) {idx : Nat} (hidx : idx < objs.length)
    (a : BitVec 64) :
    nonPersistRefs objs a =
      (if objs[idx].rc = 0#32 then 0 else objs[idx].childFields.count a) +
      nonPersistRefs (objs.eraseIdx idx) a := by
  have hsp : objs = objs.take idx ++ objs[idx] :: objs.drop (idx + 1) := by
    have h1 := List.take_append_drop idx objs
    have h2 : objs.drop idx = objs[idx] :: objs.drop (idx + 1) :=
      List.drop_eq_getElem_cons hidx
    rw [h2] at h1; exact h1.symm
  conv => lhs; rw [hsp]
  rw [nonPersistRefs_append, nonPersistRefs_cons, List.eraseIdx_eq_take_drop_succ,
    nonPersistRefs_append]
  omega

private theorem nonPersistRefs_set_same_nz (objs : List LcnfObj) {idx : Nat}
    (hidx : idx < objs.length) {rc' : BitVec 32} (h1 : objs[idx].rc ≠ 0#32) (h2 : rc' ≠ 0#32)
    (a : BitVec 64) :
    nonPersistRefs (objs.set idx (objs[idx].withRc rc')) a = nonPersistRefs objs a := by
  have hsp1 := nonPersistRefs_focus objs hidx a
  have hidx' : idx < (objs.set idx (objs[idx].withRc rc')).length := by simp [hidx]
  have hsp2 := nonPersistRefs_focus (objs.set idx (objs[idx].withRc rc')) hidx' a
  have her : (objs.set idx (objs[idx].withRc rc')).eraseIdx idx = objs.eraseIdx idx := by
    rw [List.eraseIdx_eq_take_drop_succ, List.eraseIdx_eq_take_drop_succ]
    congr 1
    · apply List.ext_getElem
      · simp
      · intro j hj1 hj2
        have hlt : j < idx := by
          have : j < min idx (objs.set idx (objs[idx].withRc rc')).length := by
            simpa [List.length_take] using hj1
          omega
        simp [List.getElem_take, List.getElem_set_ne (by omega : idx ≠ j)]
    · apply List.ext_getElem
      · simp
      · intro j hj1 hj2
        simp only [List.getElem_drop, List.getElem_set_ne (by omega : idx ≠ idx + 1 + j)]
  rw [hsp1, hsp2, her, List.getElem_set_self]
  simp only [LcnfObj.withRc, LcnfObj.childFields, h1, h2, ↓reduceIte]
  rfl

private theorem nonPersistRefs_eq_zero_imp (objs : List LcnfObj) (a : BitVec 64)
    (h0 : nonPersistRefs objs a = 0) :
    ∀ p ∈ objs, p.rc ≠ 0#32 → a ∉ p.childFields := by
  induction objs with
  | nil => intro p hp; nomatch hp
  | cons x xs ih =>
    rw [nonPersistRefs_cons] at h0
    intro p hp hnz
    rcases List.mem_cons.mp hp with rfl | hmem
    · simp only [hnz, ↓reduceIte] at h0
      intro hmemC
      have hpos : 0 < List.count a p.childFields := List.count_pos_iff.mpr hmemC
      omega
    · exact ih (by omega) p hmem hnz

private theorem nonPersistRefs_filter_step :
    ∀ (xs : List LcnfObj) (p q : BitVec 64 → Bool) (xAddr : BitVec 64)
      (xFields : List (BitVec 64)),
      (xs.map LcnfObj.addr).Nodup →
      (∀ a, a ≠ xAddr → p a = q a) →
      p xAddr = false → q xAddr = true →
      (∃ ox ∈ xs, ox.addr = xAddr ∧ ox.rc ≠ 0#32 ∧ ox.childFields = xFields) →
      ∀ y, nonPersistRefs (xs.filter (fun o => q o.addr)) y =
        nonPersistRefs (xs.filter (fun o => p o.addr)) y + xFields.count y
  | [], _, _, _, _, _, _, _, _, ⟨_, h, _⟩, _ => nomatch h
  | o :: os, p, q, xAddr, xFields, hnd, hagree, hp0, hq1, hex, y => by
    rw [List.map_cons, List.nodup_cons] at hnd
    by_cases ho : o.addr = xAddr
    · obtain ⟨ox, hoxMem, hoxAddr, hoxNz, hoxF⟩ := hex
      have hoxEq : ox = o := by
        rcases List.mem_cons.mp hoxMem with rfl | htl
        · rfl
        · exfalso; exact hnd.1 (ho ▸ hoxAddr ▸ List.mem_map_of_mem htl)
      subst hoxEq
      have htlEq : os.filter (fun z => q z.addr) = os.filter (fun z => p z.addr) := by
        refine List.filter_congr fun z hz => ?_
        have hne : z.addr ≠ xAddr := fun h => hnd.1 (ho ▸ h ▸ List.mem_map_of_mem hz)
        exact (hagree z.addr hne).symm
      simp only [List.filter_cons, ho, hp0, hq1, Bool.false_eq_true, ↓reduceIte, htlEq,
        nonPersistRefs_cons, hoxNz, hoxF]
      omega
    · obtain ⟨ox, hoxMem, hoxAddr, hoxNz, hoxF⟩ := hex
      have hoxTl : ox ∈ os := by
        rcases List.mem_cons.mp hoxMem with rfl | htl
        · exact absurd hoxAddr ho
        · exact htl
      have ih := nonPersistRefs_filter_step os p q xAddr xFields hnd.2 hagree hp0 hq1
        ⟨ox, hoxTl, hoxAddr, hoxNz, hoxF⟩ y
      have hpq : q o.addr = p o.addr := (hagree o.addr ho).symm
      simp only [List.filter_cons, hpq]
      cases p o.addr
      · simpa using ih
      · simp only [↓reduceIte, nonPersistRefs_cons, ih]; omega

private theorem freedObjs_self (objs : List LcnfObj) : freedObjs objs objs = [] := by
  unfold freedObjs
  rw [List.filter_eq_nil_iff]
  intro o ho
  simp [List.mem_map_of_mem ho]

private theorem freedObjs_set_rc (objs curObjs : List LcnfObj) {idx : Nat}
    (hidx : idx < curObjs.length) (rc' : BitVec 32) :
    freedObjs objs (curObjs.set idx (curObjs[idx].withRc rc')) = freedObjs objs curObjs := by
  unfold freedObjs
  have hmap : (curObjs.set idx (curObjs[idx].withRc rc')).map LcnfObj.addr =
      curObjs.map LcnfObj.addr := by
    apply List.ext_getElem
    · simp
    · intro j hj1 hj2
      simp only [List.getElem_map]
      by_cases hji : j = idx
      · subst hji; simp [LcnfObj.withRc]
      · simp [List.getElem_set_ne (Ne.symm hji)]
  rw [hmap]

private theorem map_addr_eraseIdx_mem {curObjs : List LcnfObj}
    (hnd : (curObjs.map LcnfObj.addr).Nodup) {idx : Nat} (hidx : idx < curObjs.length)
    (a : BitVec 64) :
    (a ∈ (curObjs.eraseIdx idx).map LcnfObj.addr) ↔
      (a ∈ curObjs.map LcnfObj.addr ∧ a ≠ curObjs[idx].addr) := by
  constructor
  · intro hm
    rw [List.mem_map] at hm
    obtain ⟨o, ho, rfl⟩ := hm
    have ho' : o ∈ curObjs := List.mem_of_mem_eraseIdx ho
    refine ⟨List.mem_map_of_mem ho', ?_⟩
    intro heq
    have hsp := List.eraseIdx_eq_take_drop_succ (l := curObjs) (i := idx)
    rw [hsp, List.mem_append] at ho
    rcases ho with ht | hd
    · rw [List.mem_iff_getElem] at ht
      obtain ⟨j, hj, rfl⟩ := ht
      have hlt : j < idx := by
        have : j < min idx curObjs.length := by simpa [List.length_take] using hj
        omega
      rw [List.getElem_take] at heq
      have : j = idx := nodup_addr_idx_eq hnd (by omega) hidx heq
      omega
    · rw [List.mem_iff_getElem] at hd
      obtain ⟨j, hj, rfl⟩ := hd
      rw [List.getElem_drop] at heq
      have hj' : idx + 1 + j < curObjs.length := by simp [List.length_drop] at hj; omega
      have : idx + 1 + j = idx := nodup_addr_idx_eq hnd hj' hidx heq
      omega
  · intro ⟨hm, hne⟩
    rw [List.mem_map] at hm
    obtain ⟨o, ho, rfl⟩ := hm
    rw [List.mem_iff_getElem] at ho
    obtain ⟨j, hj, rfl⟩ := ho
    have hji : j ≠ idx := fun h => hne (by subst h; rfl)
    rw [List.mem_map]
    refine ⟨curObjs[j], ?_, rfl⟩
    rw [List.eraseIdx_eq_take_drop_succ, List.mem_append]
    by_cases hlt : j < idx
    · left; rw [List.mem_iff_getElem]
      exact ⟨j, by rw [List.length_take]; omega, by simp [List.getElem_take]⟩
    · right; rw [List.mem_iff_getElem]
      exact ⟨j - (idx + 1), by rw [List.length_drop]; omega,
        by rw [List.getElem_drop]; congr 1; omega⟩

private theorem nonPersistRefs_freedObjs_eraseIdx {objs curObjs : List LcnfObj}
    (hndO : (objs.map LcnfObj.addr).Nodup) (hndC : (curObjs.map LcnfObj.addr).Nodup)
    {idx : Nat} (hidx : idx < curObjs.length)
    (horig : ∃ ox ∈ objs, ox.addr = curObjs[idx].addr ∧ ox.rc ≠ 0#32 ∧
      ox.childFields = curObjs[idx].childFields) (y : BitVec 64) :
    nonPersistRefs (freedObjs objs (curObjs.eraseIdx idx)) y =
      nonPersistRefs (freedObjs objs curObjs) y + curObjs[idx].childFields.count y := by
  unfold freedObjs
  refine nonPersistRefs_filter_step objs
    (fun a => !(curObjs.map LcnfObj.addr).contains a)
    (fun a => !((curObjs.eraseIdx idx).map LcnfObj.addr).contains a)
    curObjs[idx].addr curObjs[idx].childFields hndO ?_ ?_ ?_ horig y
  · intro a hne
    have hiff := map_addr_eraseIdx_mem hndC hidx a
    by_cases hm : a ∈ curObjs.map LcnfObj.addr
    · have hm' : a ∈ (curObjs.eraseIdx idx).map LcnfObj.addr := hiff.mpr ⟨hm, hne⟩
      simp [hm, hm']
    · have hm' : a ∉ (curObjs.eraseIdx idx).map LcnfObj.addr := fun h => hm (hiff.mp h).1
      simp [hm, hm']
  · have hm : curObjs[idx].addr ∈ curObjs.map LcnfObj.addr :=
      List.mem_map_of_mem (List.getElem_mem hidx)
    simp [hm]
  · have hm' : curObjs[idx].addr ∉ (curObjs.eraseIdx idx).map LcnfObj.addr := by
      intro h; exact (map_addr_eraseIdx_mem hndC hidx _).mp h |>.2 rfl
    simp [hm']

private theorem wp_let_copy64_eq {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (args : Tup (Arg Val) [i64]) (k : Tup Val [i64] → Expr Val Cont rs) :
    wp Γ Q X (Expr.let_ { sig := [i64], code := OpCode.copy i64, args := args } k) m =
      wp Γ Q X (k (args.fst.val, ())) m := by
  rw [wp_let_copy_eq]

local macro "dfs_pure_steps" : tactic =>
  `(tactic| (
    repeat (first
      | rw [wp_let_copy64_eq]
      | rw [wp_let_add64_eq]
      | rw [wp_let_sub64_eq]
      | rw [wp_let_mul64_eq]
      | rw [wp_let_and64_eq]
      | rw [wp_let_lshr64_eq]
      | rw [wp_let_sext32_64_eq])
    try dsimp [Arg.val]))

private theorem bv64_mul8_comm (n : Nat) :
    BitVec.ofNat 64 n * 8#64 = BitVec.ofNat 64 (8 * n) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.mul_comm]

private theorem bv64_8_mul (n : Nat) :
    8#64 * BitVec.ofNat 64 n = BitVec.ofNat 64 (8 * n) := by
  apply BitVec.eq_of_toNat_eq; simp

private theorem lcnfObjHeader_sub1_wf (o : LcnfObj) (hw : o.Wf) (hgt : 1 < o.rc.toNat) :
    o.header - 1#64 = (o.withRc (o.rc - 1#32)).header :=
  lcnfObjHeader_sub1 o hw.2.2.2.1 hw.2.2.2.2.1 hw.2.2.2.2.2.1 hw.2.2.1 hgt

private theorem nonPersistReach_root_nz {objs : List LcnfObj} {root a : BitVec 64}
    (h : NonPersistReach objs root a) : ∃ o' ∈ objs, o'.addr = root ∧ o'.rc ≠ 0#32 := by
  induction h with
  | refl h0 => exact h0
  | step _ _ _ _ ih => exact ih

private theorem nonPersistReach_mark_complete {objs curObjs : List LcnfObj} {root : BitVec 64}
    (hlen : curObjs.length = objs.length)
    (hnd : (objs.map LcnfObj.addr).Nodup)
    (hroot : ∀ k (hk : k < objs.length) (hk' : k < curObjs.length),
      objs[k].addr = root → curObjs[k].rc = 0#32)
    (haddr : ∀ k (hk : k < objs.length) (hk' : k < curObjs.length),
      SameNonRc objs[k] curObjs[k])
    (hstep : ∀ k (hk : k < objs.length) (hk' : k < curObjs.length),
      objs[k].rc ≠ 0#32 → curObjs[k].rc = 0#32 →
      ∀ f ∈ curObjs[k].childFields, (f &&& 1#64) = 0#64 →
        ∃ q ∈ curObjs, q.addr = f ∧ q.rc = 0#32)
    {a : BitVec 64} (hreach : NonPersistReach objs root a) :
    ∃ k, ∃ hk : k < curObjs.length, curObjs[k].addr = a ∧ curObjs[k].rc = 0#32 := by
  induction hreach with
  | refl h =>
    obtain ⟨obj, hmem, rfl, _⟩ := h
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨k, hk, rfl⟩ := hmem
    have hk' : k < curObjs.length := by omega
    exact ⟨k, hk', (haddr k hk hk').1, hroot k hk hk' rfl⟩
  | @step u v _ hchild hv0 _ ih =>
    obtain ⟨ku, hku', hkuAddr, hkuRc⟩ := ih
    have hku : ku < objs.length := by omega
    obtain ⟨ou, houMem, houAddr, hvIn⟩ := hchild
    have houEq' : ou = objs[ku] := by
      refine nodup_addr_eq_of_mem hnd houMem (List.getElem_mem hku) ?_
      rw [houAddr, ← hkuAddr, (haddr ku hku hku').1]
    subst houEq'
    have hkuOrigNz : objs[ku].rc ≠ 0#32 := by
      cases ‹NonPersistReach objs root u› with
      | refl h =>
        obtain ⟨o0, ho0, ho0Addr, ho0Nz⟩ := h
        have := nodup_addr_eq_of_mem hnd ho0 (List.getElem_mem hku)
          (by rw [ho0Addr, ← hkuAddr, (haddr ku hku hku').1])
        rwa [← this]
      | step _ _ _ h' =>
        obtain ⟨o0, ho0, ho0Addr, ho0Nz⟩ := h'
        have := nodup_addr_eq_of_mem hnd ho0 (List.getElem_mem hku)
          (by rw [ho0Addr, ← hkuAddr, (haddr ku hku hku').1])
        rwa [← this]
    have hvInCur : v ∈ curObjs[ku].childFields := by
      rw [(haddr ku hku hku').childFields_eq]; exact hvIn
    obtain ⟨q, hqMem, hqAddr, hqRc⟩ := hstep ku hku hku' hkuOrigNz hkuRc v hvInCur hv0
    rw [List.mem_iff_getElem] at hqMem
    obtain ⟨kv, hkv', rfl⟩ := hqMem
    exact ⟨kv, hkv', hqAddr, hqRc⟩

/-! ## `lcnf_mark_persistent_wp` -/

theorem lcnf_mark_persistent_wp (Γ : Env) :
    ∀ (xs : Tup Val lcnf_mark_persistent.as) (m : Mem 64)
      (Q : Post lcnf_mark_persistent.rs) (X : XPost),
      lcnfMarkPersistentSpec xs m Q X →
      Func.wp Γ lcnf_mark_persistent.body xs m Q X := by
  dsimp [lcnf_mark_persistent]
  intro ⟨rt, o, ⟨⟩⟩ m Q X hSpec
  dsimp [Func.wp, lcnf_mark_persistent_body]
  dsimp [lcnfMarkPersistentSpec] at hSpec
  split at hSpec
  · rename_i hodd
    rcases hSpec with ⟨st, R, _hm, hQ⟩
    dfs_pure_steps
    refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
    dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
    constructor
    · intro _; exact hQ
    · intro hf; exfalso; exact of_decide_eq_false hf hodd
  · rename_i hevenNot
    have heven : (o &&& 1#64) = 0#64 := Classical.byContradiction hevenNot
    rcases hSpec with ⟨st, objs, R, hCapLe, hm, hRootEx, hObjsWf, hObjsCl, hPost⟩
    have hndO : (objs.map LcnfObj.addr).Nodup :=
      lcnfHeap_nodup_addrs (sep_pull_heap hm)
    obtain ⟨obj0, hobj0Mem, hobj0Addr⟩ := hRootEx
    rw [List.mem_iff_getElem] at hobj0Mem
    obtain ⟨idx0, hidx0, rfl⟩ := hobj0Mem
    have hobj0Wf : objs[idx0].Wf := hObjsWf objs[idx0] (List.getElem_mem hidx0)
    have hcs0 := hobj0Wf.2.2.2.1
    have hoth0 := hobj0Wf.2.2.2.2.1
    have htag0 := hobj0Wf.2.2.2.2.2.1
    dfs_pure_steps
    refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
    dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
    constructor
    · intro ht; exfalso; exact of_decide_eq_true ht heven
    · intro _
      have hld0 : loadVal m i64 o = some objs[idx0].header := by
        rw [← hobj0Addr]
        exact lcnfHeap_load_header hidx0 (sep_pull_heap hm)
      refine wp_load_of hld0 ?_
      dfs_pure_steps
      rw [LcnfObj.header_rc objs[idx0] hcs0 hoth0 htag0]
      refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
      dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
      constructor
      · intro hrc0Eq
        have hrc064 : BitVec.ofNat 64 objs[idx0].rc.toNat = 0#64 := of_decide_eq_true hrc0Eq
        have hrc0 : objs[idx0].rc = 0#32 := by
          apply BitVec.eq_of_toNat_eq
          have := congrArg BitVec.toNat hrc064
          simpa [Nat.mod_eq_of_lt (by omega : objs[idx0].rc.toNat < 2 ^ 64)] using this
        refine hPost st objs m ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl ?_ hm
        refine ⟨rfl, hObjsWf, hObjsCl, hObjsCl, ?_⟩
        intro p hp
        rw [List.mem_iff_getElem] at hp
        obtain ⟨k, hk, rfl⟩ := hp
        have hk0 : k < objs.length := by rw [List.length_zip, Nat.min_self] at hk; exact hk
        rw [List.getElem_zip]
        refine ⟨hObjsWf objs[k] (List.getElem_mem hk0), rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, ?_, Or.inl rfl, ?_⟩
        · intro had
          have heq := nodup_addr_eq_of_mem hndO (List.getElem_mem hk0) (List.getElem_mem hidx0)
            (had.trans hobj0Addr.symm)
          rw [heq, hrc0]
        · intro hknz
          constructor
          · intro hk0'; exact absurd hk0' hknz
          · intro hreach
            exfalso
            obtain ⟨o', ho', ho'Addr, ho'Nz⟩ := nonPersistReach_root_nz hreach
            have heq := nodup_addr_eq_of_mem hndO ho' (List.getElem_mem hidx0)
              (ho'Addr.trans hobj0Addr.symm)
            rw [heq] at ho'Nz
            exact ho'Nz hrc0
      · intro hrc0NeEq
        have hrc0Nz64 : BitVec.ofNat 64 objs[idx0].rc.toNat ≠ 0#64 := of_decide_eq_false hrc0NeEq
        have hrc0Nz : objs[idx0].rc ≠ 0#32 := fun h => hrc0Nz64 (by rw [h]; rfl)
        dfs_pure_steps
        rw [LcnfObj.header_clear_rc objs[idx0] hcs0 hoth0 htag0]
        have hst0 := lcnfHeap_store_rc hidx0 0#32 (sep_pull_heap hm)
        rw [hobj0Addr] at hst0
        refine wp_store_sep (R := rtC0Inv rt st ⋆ R) hst0 ?_
        intro m1 hm1
        let objs1 : List LcnfObj := objs.set idx0 (objs[idx0].withRc 0#32)
        have hm1' : (rtC0Inv rt st ⋆ lcnfHeap objs1 ⋆ R) m1 := sep_cast hm1 (by ac_rfl)
        dfs_pure_steps
        refine wp_load_of (rtC0Inv_load_s_st_persistent hm1') ?_
        dfs_pure_steps
        refine wp_store_sep (rtC0Inv_store_s_st_persistent hm1') ?_
        intro m2 hm2
        let st1 := st.withPersistInc
        dfs_pure_steps
        refine wp_load_of (rtC0Inv_load_s_work hm2) ?_
        dfs_pure_steps
        refine wp_load_of (rtC0Inv_load_s_work_cap hm2) ?_
        refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
        dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
        constructor
        · intro hcap0
          exfalso
          have h0 : st1.hdr.s_work_cap = 0#64 := of_decide_eq_true hcap0
          have h0n : st.workCap = 0 := by
            unfold RtC0State.workCap; change st1.hdr.s_work_cap.toNat = 0; rw [h0]; rfl
          omega
        · intro _hcapNz
          dfs_pure_steps
          have h0lt : 0 < st1.workBuf.length := by
            rw [st1.workLen]; change 0 < st.workCap; omega
          have hstW0 := rtC0Inv_store_work h0lt o hm2
          have hmul0 : (0#64 : BitVec 64) * 8#64 = BitVec.ofNat 64 (8 * 0) := by decide
          rw [← hmul0] at hstW0
          refine wp_store_sep hstW0 ?_
          intro m3 hm3
          let st2 := st1.withWorkBuf (st1.workBuf.set 0 o)
            (by rw [List.length_set]; exact st1.workLen)
          let OuterInv : Nat → Tup Val [i64] → Mem 64 → Prop := fun n (lenBV, _) mCur =>
            ∃ (stCur : RtC0State) (curObjs : List LcnfObj) (len : Nat),
              stCur.PreservesMeta st ∧ stCur.rem = st.rem ∧
              len ≤ st.workCap ∧ lenBV = BitVec.ofNat 64 len ∧
              2 * unmarkedCount curObjs + len = n ∧
              curObjs.length = objs.length ∧ lcnfHeapClosed curObjs ∧
              (rtC0Inv rt stCur ⋆ lcnfHeap curObjs ⋆ R) mCur ∧
              (stCur.workBuf.take len).Nodup ∧
              (∀ a ∈ stCur.workBuf.take len, ∃ k, ∃ hk : k < curObjs.length,
                curObjs[k].addr = a ∧ curObjs[k].rc = 0#32 ∧ NonPersistReach objs o a) ∧
              (∀ k (hk : k < objs.length) (hk' : k < curObjs.length),
                SameNonRc objs[k] curObjs[k] ∧ curObjs[k].Wf ∧
                (objs[k].addr = o → curObjs[k].rc = 0#32) ∧
                (curObjs[k].rc = objs[k].rc ∨ curObjs[k].rc = 0#32) ∧
                (objs[k].rc ≠ 0#32 → curObjs[k].rc = 0#32 → NonPersistReach objs o objs[k].addr) ∧
                (objs[k].rc ≠ 0#32 → curObjs[k].rc = 0#32 →
                  curObjs[k].addr ∉ stCur.workBuf.take len →
                  ∀ f ∈ curObjs[k].childFields, (f &&& 1#64) = 0#64 →
                    ∃ q ∈ curObjs, q.addr = f ∧ q.rc = 0#32))
          refine wp_loop_group OuterInv ?_ (fun J0 hJ0 => by
            dsimp
            have htk1 : st2.workBuf.take 1 = [o] := by
              simpa [st2, RtC0State.withWorkBuf] using list_take_set_append st1.workBuf h0lt o
            have hlen1 : objs1.length = objs.length := List.length_set
            have hcl1 : lcnfHeapClosed objs1 := lcnfHeapClosed_set_withRc hObjsCl hidx0 0#32
            refine hJ0 (2 * unmarkedCount objs1 + 1) (1#64, ()) m3
              ⟨st2, objs1, 1, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl,
                by omega, rfl, rfl, hlen1, hcl1, hm3, by rw [htk1]; simp, ?_, ?_⟩
            · intro a ha
              rw [htk1, List.mem_singleton] at ha; subst ha
              exact ⟨idx0, by omega, by simp [objs1, LcnfObj.withRc, hobj0Addr],
                by simp [objs1, LcnfObj.withRc],
                NonPersistReach.refl ⟨objs[idx0], List.getElem_mem hidx0, hobj0Addr, hrc0Nz⟩⟩
            · intro k hk hk'
              by_cases hki : k = idx0
              · subst hki
                refine ⟨by simp [objs1, SameNonRc.withRc_r (SameNonRc.refl _)],
                  by simp [objs1, objWf_withRc_zero hobj0Wf],
                  fun _ => by simp [objs1, LcnfObj.withRc],
                  Or.inr (by simp [objs1, LcnfObj.withRc]),
                  fun _ _ => hobj0Addr.symm ▸ NonPersistReach.refl
                    ⟨objs[k], List.getElem_mem hk, hobj0Addr, hrc0Nz⟩,
                  fun _ _ hnot => by
                    exfalso; apply hnot; rw [htk1]; simp [objs1, LcnfObj.withRc, hobj0Addr]⟩
              · have hget : objs1[k]'hk' = objs[k]'hk := List.getElem_set_ne (Ne.symm hki) hk'
                rw [hget]
                refine ⟨SameNonRc.refl _, hObjsWf objs[k] (List.getElem_mem hk),
                  fun had => by
                    exfalso
                    exact hki (nodup_addr_idx_eq hndO hk hidx0 (had.trans hobj0Addr.symm)),
                  Or.inl rfl, fun hnz h0 => absurd h0 hnz, fun hnz h0 => absurd h0 hnz⟩)
          intro J0 n ⟨lenBV, ⟨⟩⟩ mCur hIH0
            ⟨stCur, curObjs, len, hMeta, hRem, hLenLe, hLenBV, hMeas, hCurLen, hCurCl, hmCur,
              hWlNd, hWlMem, hCurProp⟩
          have hWorkEq : stCur.hdr.s_work = st.hdr.s_work := hMeta.2.2.2.2.1.symm
          have hCapEq : stCur.hdr.s_work_cap = st.hdr.s_work_cap := hMeta.2.2.2.2.2.1.symm
          have hCapNat : stCur.workBuf.length = st.workCap := by
            rw [stCur.workLen, hCapEq]; rfl
          have hLen64 : (BitVec.ofNat 64 len).toNat = len :=
            Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hLenLe st.hdr.s_work_cap.isLt)
          dfs_pure_steps
          refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
          dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
          constructor
          · intro hLenPosEq
            have hLenPos : 0 < len := by
              rw [hLenBV, BitVec.ult, hLen64] at hLenPosEq
              have h0m : (0#64).toNat = 0 := by decide
              rw [h0m] at hLenPosEq
              exact of_decide_eq_true hLenPosEq
            let len0 : Nat := len - 1
            have hLen0Lt : len0 < stCur.workBuf.length := by omega
            have hSubBV : lenBV - 1#64 = BitVec.ofNat 64 len0 := by
              rw [hLenBV]
              apply BitVec.eq_of_toNat_eq
              have hlt64 : len < 2 ^ 64 := Nat.lt_of_le_of_lt hLenLe st.hdr.s_work_cap.isLt
              bv_omega
            dfs_pure_steps
            rw [hSubBV]
            have hldX : loadVal mCur i64 (st.hdr.s_work + BitVec.ofNat 64 len0 * 8#64) =
                some (stCur.workBuf[len0]'hLen0Lt) := by
              rw [← hWorkEq, bv64_mul8_comm]
              exact rtC0Inv_load_work hLen0Lt hmCur
            refine wp_load_of hldX ?_
            let xAddr : BitVec 64 := stCur.workBuf[len0]'hLen0Lt
            have hTkPop : stCur.workBuf.take len = stCur.workBuf.take len0 ++ [xAddr] := by
              have h1 : len = len0 + 1 := by omega
              rw [h1]
              exact List.take_succ_eq_append_getElem hLen0Lt
            have hxInWl : xAddr ∈ stCur.workBuf.take len := by rw [hTkPop]; simp
            have hWl0Nd : (stCur.workBuf.take len0).Nodup := by
              rw [hTkPop, List.nodup_append] at hWlNd; exact hWlNd.1
            have hxNotWl0 : xAddr ∉ stCur.workBuf.take len0 := by
              rw [hTkPop, List.nodup_append] at hWlNd
              intro hm; exact hWlNd.2.2 xAddr hm xAddr List.mem_cons_self rfl
            obtain ⟨idx_x, hidx_x, hxAddrEq, hxRc0, hxReach⟩ := hWlMem xAddr hxInWl
            let x : LcnfObj := curObjs[idx_x]'hidx_x
            have hxProp := hCurProp idx_x (by omega) hidx_x
            have hxWf : x.Wf := hxProp.2.1
            have hxCs := hxWf.2.2.2.1
            have hxOth := hxWf.2.2.2.2.1
            have hxTag := hxWf.2.2.2.2.2.1
            have hldHdr : loadVal mCur i64 xAddr = some x.header := by
              rw [← hxAddrEq]
              exact lcnfHeap_load_header hidx_x (sep_pull_heap hmCur)
            refine wp_load_of hldHdr ?_
            dfs_pure_steps
            have htagShift : x.header >>> 56 = BitVec.ofNat 64 x.tag :=
              LcnfObj.header_tag x hxCs hxOth hxTag
            let DispPost : Tup Val [i64, i64] → Mem 64 → Prop := fun (nBV, offBV, _) mD =>
              nBV = BitVec.ofNat 64 x.childFields.length ∧ offBV = x.fieldsOff ∧ mD = mCur
            refine wp_join_group DispPost ?_ ?_
            · intro _ ⟨nBV, offBV, ⟨⟩⟩ mD ⟨hnBV, hoffBV, hmD⟩
              subst mD; subst hnBV hoffBV
              let InnerInv : Nat → Tup Val [i64, i64] → Mem 64 → Prop :=
                fun rem (lenBV', iBV, _) mIn =>
                  ∃ (stIn : RtC0State) (inObjs : List LcnfObj) (len' i : Nat),
                    stIn.PreservesMeta st ∧ stIn.rem = st.rem ∧
                    len' ≤ st.workCap ∧ lenBV' = BitVec.ofNat 64 len' ∧
                    i ≤ x.childFields.length ∧ iBV = BitVec.ofNat 64 i ∧
                    rem = x.childFields.length - i ∧
                    2 * unmarkedCount inObjs + len' ≤ 2 * unmarkedCount curObjs + len0 ∧
                    inObjs.length = objs.length ∧ lcnfHeapClosed inObjs ∧
                    inObjs[idx_x]? = some x ∧
                    (rtC0Inv rt stIn ⋆ lcnfHeap inObjs ⋆ R) mIn ∧
                    (stIn.workBuf.take len').Nodup ∧ xAddr ∉ stIn.workBuf.take len' ∧
                    (∀ a ∈ stIn.workBuf.take len', ∃ k, ∃ hk : k < inObjs.length,
                      inObjs[k].addr = a ∧ inObjs[k].rc = 0#32 ∧ NonPersistReach objs o a) ∧
                    (∀ f ∈ x.childFields.take i, (f &&& 1#64) = 0#64 →
                      ∃ q ∈ inObjs, q.addr = f ∧ q.rc = 0#32) ∧
                    (∀ k (hk : k < objs.length) (hk' : k < inObjs.length),
                      SameNonRc objs[k] inObjs[k] ∧ inObjs[k].Wf ∧
                      (objs[k].addr = o → inObjs[k].rc = 0#32) ∧
                      (inObjs[k].rc = objs[k].rc ∨ inObjs[k].rc = 0#32) ∧
                      (objs[k].rc ≠ 0#32 → inObjs[k].rc = 0#32 →
                        NonPersistReach objs o objs[k].addr) ∧
                      (objs[k].rc ≠ 0#32 → inObjs[k].rc = 0#32 →
                        inObjs[k].addr ∉ stIn.workBuf.take len' →
                        inObjs[k].addr ≠ xAddr →
                        ∀ f ∈ inObjs[k].childFields, (f &&& 1#64) = 0#64 →
                          ∃ q ∈ inObjs, q.addr = f ∧ q.rc = 0#32))
              refine wp_loop_group InnerInv ?_ (fun J4 hJ4 => by
                dsimp
                refine hJ4 x.childFields.length (BitVec.ofNat 64 len0, 0#64, ()) mCur
                  ⟨stCur, curObjs, len0, 0, hMeta, hRem, by omega, rfl, Nat.zero_le _, rfl, rfl,
                    Nat.le_refl _, hCurLen, hCurCl, List.getElem?_eq_getElem hidx_x, hmCur,
                    hWl0Nd, hxNotWl0, ?_, by simp, ?_⟩
                · intro a ha
                  exact hWlMem a (by rw [hTkPop]; exact List.mem_append_left _ ha)
                · intro k hk hk'
                  have hp := hCurProp k hk hk'
                  refine ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, ?_⟩
                  intro hnz h0 hnotWl0 hneX
                  have hnotWl : curObjs[k].addr ∉ stCur.workBuf.take len := by
                    rw [hTkPop, List.mem_append, List.mem_singleton]
                    rintro (h | h)
                    · exact hnotWl0 h
                    · exact hneX h
                  exact hp.2.2.2.2.2 hnz h0 hnotWl)
              intro J4 rem ⟨lenBV', iBV, ⟨⟩⟩ mIn hIH4
                ⟨stIn, inObjs, len', i, hMetaIn, hRemIn, hLenInLe, hLenInBV, hiLe, hiBV, hRemEq,
                  hMeasIn, hInLen, hInCl, hInX, hmIn, hWlInNd, hxNotWlIn, hWlInMem, hDoneI,
                  hInProp⟩
              have hidx_x_in : idx_x < inObjs.length := by omega
              have hInX' : inObjs[idx_x]'hidx_x_in = x :=
                Option.some.inj (by rwa [List.getElem?_eq_getElem hidx_x_in] at hInX)
              have hWorkInEq : stIn.hdr.s_work = st.hdr.s_work := hMetaIn.2.2.2.2.1.symm
              have hCapInEq : stIn.hdr.s_work_cap = st.hdr.s_work_cap := hMetaIn.2.2.2.2.2.1.symm
              have hCapInNat : stIn.workBuf.length = st.workCap := by
                rw [stIn.workLen, hCapInEq]; rfl
              have hChildLt : x.childFields.length < 2 ^ 64 := objWf_childFields_lt hxWf
              have hi64 : (BitVec.ofNat 64 i).toNat = i := Nat.mod_eq_of_lt (by omega)
              have hn64 : (BitVec.ofNat 64 x.childFields.length).toNat = x.childFields.length :=
                Nat.mod_eq_of_lt hChildLt
              dfs_pure_steps
              refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
              dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
              constructor
              · intro hiUlt
                have hiLt : i < x.childFields.length := by
                  rw [hiBV, BitVec.ult, hi64, hn64] at hiUlt
                  exact of_decide_eq_true hiUlt
                dfs_pure_steps
                have hldC : loadVal mIn i64 ((xAddr + x.fieldsOff) + 8#64 * iBV) =
                    some (x.childFields[i]'hiLt) := by
                  have h1 := lcnfHeap_load_child hidx_x_in (by rw [hInX']; exact hxWf)
                    (sep_pull_heap hmIn) (by rw [hInX']; exact hiLt)
                  simpa [x, hInX', hxAddrEq, hiBV, bv64_8_mul] using h1
                refine wp_load_of hldC ?_
                let c : BitVec 64 := x.childFields[i]'hiLt
                let StepPost : Tup Val [i64] → Mem 64 → Prop := fun (lenBV'', _) mStep =>
                  ∃ (stOut : RtC0State) (outObjs : List LcnfObj) (len'' : Nat),
                    stOut.PreservesMeta st ∧ stOut.rem = st.rem ∧
                    len'' ≤ st.workCap ∧ lenBV'' = BitVec.ofNat 64 len'' ∧
                    2 * unmarkedCount outObjs + len'' ≤ 2 * unmarkedCount curObjs + len0 ∧
                    outObjs.length = objs.length ∧ lcnfHeapClosed outObjs ∧
                    outObjs[idx_x]? = some x ∧
                    (rtC0Inv rt stOut ⋆ lcnfHeap outObjs ⋆ R) mStep ∧
                    (stOut.workBuf.take len'').Nodup ∧ xAddr ∉ stOut.workBuf.take len'' ∧
                    (∀ a ∈ stOut.workBuf.take len'', ∃ k, ∃ hk : k < outObjs.length,
                      outObjs[k].addr = a ∧ outObjs[k].rc = 0#32 ∧ NonPersistReach objs o a) ∧
                    (∀ f ∈ x.childFields.take (i + 1), (f &&& 1#64) = 0#64 →
                      ∃ q ∈ outObjs, q.addr = f ∧ q.rc = 0#32) ∧
                    (∀ k (hk : k < objs.length) (hk' : k < outObjs.length),
                      SameNonRc objs[k] outObjs[k] ∧ outObjs[k].Wf ∧
                      (objs[k].addr = o → outObjs[k].rc = 0#32) ∧
                      (outObjs[k].rc = objs[k].rc ∨ outObjs[k].rc = 0#32) ∧
                      (objs[k].rc ≠ 0#32 → outObjs[k].rc = 0#32 →
                        NonPersistReach objs o objs[k].addr) ∧
                      (objs[k].rc ≠ 0#32 → outObjs[k].rc = 0#32 →
                        outObjs[k].addr ∉ stOut.workBuf.take len'' →
                        outObjs[k].addr ≠ xAddr →
                        ∀ f ∈ outObjs[k].childFields, (f &&& 1#64) = 0#64 →
                          ∃ q ∈ outObjs, q.addr = f ∧ q.rc = 0#32))
                refine wp_join_group StepPost ?_ ?_
                · intro _ ⟨lenBV'', ⟨⟩⟩ mStep ⟨stOut, outObjs, len'', h1, h2, h3, h4, h5, h6, h7,
                    h8, h9, h10, h11, h12, h13, h14⟩
                  dsimp [Blocks.get]
                  dfs_pure_steps
                  have hi1BV : iBV + 1#64 = BitVec.ofNat 64 (i + 1) := by
                    rw [hiBV]; apply BitVec.eq_of_toNat_eq; simp
                  rw [hi1BV]
                  exact hIH4 (x.childFields.length - (i + 1)) (lenBV'', BitVec.ofNat 64 (i + 1), ())
                    mStep (by omega)
                    ⟨stOut, outObjs, len'', i + 1, h1, h2, h3, h4, by omega, rfl, rfl, h5, h6, h7,
                      h8, h9, h10, h11, h12, h13, h14⟩
                · intro J5 hJ5
                  dfs_pure_steps
                  refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
                  dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
                  constructor
                  · intro hcEvenEq
                    have hcEven : (c &&& 1#64) = 0#64 := of_decide_eq_true hcEvenEq
                    have hcInX : c ∈ inObjs[idx_x].childFields := by
                      rw [hInX']; exact List.getElem_mem hiLt
                    obtain ⟨oc, hocMem, hocAddr⟩ :=
                      hInCl inObjs[idx_x] (List.getElem_mem (by omega))
                      c hcInX hcEven
                    rw [List.mem_iff_getElem] at hocMem
                    obtain ⟨idx_c, hidx_c, rfl⟩ := hocMem
                    have hcProp := hInProp idx_c (by omega) hidx_c
                    have hcWf : inObjs[idx_c].Wf := hcProp.2.1
                    have hldChdr : loadVal mIn i64 c = some inObjs[idx_c].header := by
                      rw [← hocAddr]
                      exact lcnfHeap_load_header hidx_c (sep_pull_heap hmIn)
                    refine wp_load_of hldChdr ?_
                    refine wp_join_group StepPost
                      (fun _ xs m6 h => by rcases xs with ⟨v, ⟨⟩⟩; exact hJ5 (v, ()) m6 h) ?_
                    intro J6 hJ6
                    dfs_pure_steps
                    rw [LcnfObj.header_rc inObjs[idx_c] hcWf.2.2.2.1 hcWf.2.2.2.2.1
                      hcWf.2.2.2.2.2.1]
                    refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
                    dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
                    constructor
                    · intro hCrcNzEq
                      have hCrcNz64 : BitVec.ofNat 64 inObjs[idx_c].rc.toNat ≠ 0#64 :=
                        of_decide_eq_true hCrcNzEq
                      have hCrcNz : inObjs[idx_c].rc ≠ 0#32 := fun h => hCrcNz64 (by rw [h]; rfl)
                      have hOrigCNz : (objs[idx_c]'(by omega)).rc ≠ 0#32 := by
                        rcases hcProp.2.2.2.1 with h | h
                        · rw [← h]; exact hCrcNz
                        · exact absurd h hCrcNz
                      have hneCX : c ≠ xAddr := by
                        intro heq
                        have hndIn : (inObjs.map LcnfObj.addr).Nodup :=
                          lcnfHeap_nodup_addrs (sep_pull_heap hmIn)
                        have hEqObj := nodup_addr_eq_of_mem hndIn (List.getElem_mem hidx_c)
                          (List.getElem_mem (by omega : idx_x < inObjs.length))
                          (by rw [hocAddr, heq, hInX', hxAddrEq])
                        rw [hEqObj, hInX'] at hCrcNz
                        exact hCrcNz hxRc0
                      have hidxNe : idx_c ≠ idx_x := fun h =>
                        hneCX (by subst h; rw [← hocAddr, hInX', hxAddrEq])
                      have hcNotWl : c ∉ stIn.workBuf.take len' := by
                        intro hmem
                        obtain ⟨k, hk, hkAddr, hkRc0, _⟩ := hWlInMem c hmem
                        have hndIn : (inObjs.map LcnfObj.addr).Nodup :=
                          lcnfHeap_nodup_addrs (sep_pull_heap hmIn)
                        have hEqObj := nodup_addr_eq_of_mem hndIn (List.getElem_mem hidx_c)
                          (List.getElem_mem hk) (hocAddr.trans hkAddr.symm)
                        rw [hEqObj] at hCrcNz
                        exact hCrcNz hkRc0
                      have hLenLtCap : len' < st.workCap := by
                        have hle := work_push_lt_cap hWlInNd hxNotWlIn hcNotWl hneCX
                          ⟨inObjs[idx_x]'(by omega), List.getElem_mem (by omega),
                            by rw [hInX']; exact hxAddrEq⟩
                          ⟨inObjs[idx_c], List.getElem_mem hidx_c, hocAddr⟩
                          (fun a ha => by
                            obtain ⟨k, hk, hka, _, _⟩ := hWlInMem a ha
                            exact ⟨inObjs[k], List.getElem_mem hk, hka⟩)
                          (by omega : inObjs.length ≤ st.workCap)
                        simpa [List.length_take, hCapInNat, Nat.min_eq_left hLenInLe] using hle
                      dfs_pure_steps
                      rw [LcnfObj.header_clear_rc inObjs[idx_c] hcWf.2.2.2.1 hcWf.2.2.2.2.1
                        hcWf.2.2.2.2.2.1]
                      have hstC := lcnfHeap_store_rc hidx_c 0#32 (sep_pull_heap hmIn)
                      rw [hocAddr] at hstC
                      refine wp_store_sep (R := rtC0Inv rt stIn ⋆ R) hstC ?_
                      intro mC hmC
                      let inObjs' := inObjs.set idx_c (inObjs[idx_c].withRc 0#32)
                      have hmC' : (rtC0Inv rt stIn ⋆ lcnfHeap inObjs' ⋆ R) mC :=
                        sep_cast hmC (by ac_rfl)
                      dfs_pure_steps
                      refine wp_load_of (rtC0Inv_load_s_st_persistent hmC') ?_
                      dfs_pure_steps
                      refine wp_store_sep (rtC0Inv_store_s_st_persistent hmC') ?_
                      intro mP hmP
                      let stIn1 := stIn.withPersistInc
                      refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
                      dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
                      constructor
                      · intro hEqCap
                        exfalso
                        have heq : BitVec.ofNat 64 len' = st.hdr.s_work_cap := by
                          rw [← hLenInBV]; exact of_decide_eq_true hEqCap
                        have hn := congrArg BitVec.toNat heq
                        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
                          (Nat.lt_of_le_of_lt hLenInLe st.hdr.s_work_cap.isLt)] at hn
                        change len' = st.workCap at hn
                        omega
                      · intro _hNeCap
                        dfs_pure_steps
                        have hLen'Lt : len' < stIn1.workBuf.length := by
                          rw [stIn1.workLen]; change len' < stIn.hdr.s_work_cap.toNat
                          rw [hCapInEq]; exact hLenLtCap
                        have hstW := rtC0Inv_store_work hLen'Lt c hmP
                        have hWorkIn1 : stIn1.hdr.s_work = st.hdr.s_work := hWorkInEq
                        rw [hWorkIn1, ← bv64_mul8_comm len', ← hLenInBV] at hstW
                        refine wp_store_sep hstW ?_
                        intro mW hmW
                        let stIn2 := stIn1.withWorkBuf (stIn1.workBuf.set len' c)
                          (by rw [List.length_set]; exact stIn1.workLen)
                        dfs_pure_steps
                        have hLen1BV : lenBV' + 1#64 = BitVec.ofNat 64 (len' + 1) := by
                          rw [hLenInBV]; apply BitVec.eq_of_toNat_eq; simp
                        rw [hLen1BV]
                        have hTkPush : stIn2.workBuf.take (len' + 1) =
                            stIn.workBuf.take len' ++ [c] :=
                          list_take_set_append stIn.workBuf hLen'Lt c
                        have hcReach : NonPersistReach objs o c := by
                          refine NonPersistReach.step hxReach
                            ⟨objs[idx_x]'(by omega), List.getElem_mem (by omega), ?_, ?_⟩
                            hcEven
                            ⟨objs[idx_c]'(by omega), List.getElem_mem (by omega), ?_, hOrigCNz⟩
                          · rw [← (hInProp idx_x (by omega) (by omega)).1.1, hInX', hxAddrEq]
                          · rw [← (hInProp idx_x (by omega) (by omega)).1.childFields_eq, hInX']
                            exact List.getElem_mem hiLt
                          · rw [← hcProp.1.1, hocAddr]
                        have hUnmDec : unmarkedCount inObjs' + 1 = unmarkedCount inObjs :=
                          unmarkedCount_set_zero inObjs hidx_c hCrcNz
                        have hZeroPres : ∀ q ∈ inObjs, q.rc = 0#32 →
                            ∃ q' ∈ inObjs', q'.addr = q.addr ∧ q'.rc = 0#32 := by
                          intro q hq hq0
                          rw [List.mem_iff_getElem] at hq
                          obtain ⟨kq, hkq, rfl⟩ := hq
                          have hkq' : kq < inObjs'.length := by simp [inObjs', hkq]
                          refine ⟨inObjs'[kq]'hkq', List.getElem_mem hkq', ?_, ?_⟩
                          · by_cases hkqC : kq = idx_c
                            · subst hkqC; simp [inObjs', LcnfObj.withRc]
                            · simp [inObjs', List.getElem_set_ne (Ne.symm hkqC)]
                          · by_cases hkqC : kq = idx_c
                            · subst hkqC; simp [inObjs', LcnfObj.withRc]
                            · simp [inObjs', List.getElem_set_ne (Ne.symm hkqC), hq0]
                        apply hJ6 (BitVec.ofNat 64 (len' + 1), ()) mW
                        refine ⟨stIn2, inObjs', len' + 1,
                          preservesMeta_trans hMetaIn ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
                          hRemIn, by omega, rfl, by omega, by simp [inObjs', hInLen],
                          lcnfHeapClosed_set_withRc hInCl hidx_c 0#32,
                          by rw [List.getElem?_set_ne hidxNe]; exact hInX,
                          hmW, ?_, ?_, ?_, ?_, ?_⟩
                        · rw [hTkPush, List.nodup_append]
                          refine ⟨hWlInNd, by simp, fun a ha b hb => ?_⟩
                          rw [List.mem_singleton] at hb; subst hb
                          exact fun heq => hcNotWl (heq ▸ ha)
                        · rw [hTkPush, List.mem_append, List.mem_singleton]
                          rintro (h | h)
                          · exact hxNotWlIn h
                          · exact hneCX h.symm
                        · intro a ha
                          rw [hTkPush, List.mem_append, List.mem_singleton] at ha
                          rcases ha with haOld | rfl
                          · obtain ⟨k, hk, hkAddr, hkRc, hkReach⟩ := hWlInMem a haOld
                            have hk' : k < inObjs'.length := by simp [inObjs', hk]
                            refine ⟨k, hk', ?_, ?_, hkReach⟩
                            · by_cases hkc : k = idx_c
                              · subst hkc; simp [inObjs', LcnfObj.withRc, hkAddr]
                              · simp [inObjs', List.getElem_set_ne (Ne.symm hkc), hkAddr]
                            · by_cases hkc : k = idx_c
                              · subst hkc; simp [inObjs', LcnfObj.withRc]
                              · simp [inObjs', List.getElem_set_ne (Ne.symm hkc), hkRc]
                          · exact ⟨idx_c, by simp [inObjs', hidx_c],
                              by simp [inObjs', LcnfObj.withRc, hocAddr],
                              by simp [inObjs', LcnfObj.withRc], hcReach⟩
                        · intro f hf hf0
                          rw [List.take_succ_eq_append_getElem hiLt, List.mem_append,
                            List.mem_singleton] at hf
                          rcases hf with hfOld | rfl
                          · obtain ⟨q, hq, hqa, hq0⟩ := hDoneI f hfOld hf0
                            obtain ⟨q', hq', hq'a, hq'0⟩ := hZeroPres q hq hq0
                            exact ⟨q', hq', hq'a.trans hqa, hq'0⟩
                          · exact ⟨inObjs'[idx_c]'(by simp [inObjs', hidx_c]),
                              List.getElem_mem _, by simp [inObjs', LcnfObj.withRc, hocAddr, c],
                              by simp [inObjs', LcnfObj.withRc]⟩
                        · intro k hk hk'
                          have hkin : k < inObjs.length := by simp [inObjs'] at hk'; exact hk'
                          have hp := hInProp k hk hkin
                          by_cases hkc : k = idx_c
                          · subst hkc
                            simp only [inObjs', List.getElem_set_self]
                            refine ⟨hp.1.withRc_r 0#32, objWf_withRc_zero hcWf,
                              fun _ => rfl, Or.inr rfl,
                              fun _ _ => by rw [← hp.1.1, hocAddr]; exact hcReach,
                              fun _ _ hnotWl => by
                                exfalso; apply hnotWl
                                rw [hTkPush]; simp [LcnfObj.withRc, hocAddr]⟩
                          · have hget : inObjs'[k]'hk' = inObjs[k]'hkin :=
                              List.getElem_set_ne (Ne.symm hkc) hk'
                            rw [hget]
                            refine ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, ?_⟩
                            intro hnz h0 hnotWl hneX f hf hf0
                            have hnotOld : inObjs[k].addr ∉ stIn.workBuf.take len' := fun h =>
                              hnotWl (by rw [hTkPush]; exact List.mem_append_left _ h)
                            obtain ⟨q, hq, hqa, hq0⟩ := hp.2.2.2.2.2 hnz h0 hnotOld hneX f hf hf0
                            obtain ⟨q', hq', hq'a, hq'0⟩ := hZeroPres q hq hq0
                            exact ⟨q', hq', hq'a.trans hqa, hq'0⟩
                    · intro hCrc0Eq
                      have hCrc064 : BitVec.ofNat 64 inObjs[idx_c].rc.toNat = 0#64 :=
                        Classical.byContradiction (of_decide_eq_false hCrc0Eq)
                      have hCrc0 : inObjs[idx_c].rc = 0#32 := by
                        apply BitVec.eq_of_toNat_eq
                        have := congrArg BitVec.toNat hCrc064
                        simpa [Nat.mod_eq_of_lt (by omega : inObjs[idx_c].rc.toNat < 2 ^ 64)]
                          using this
                      apply hJ6 (lenBV', ()) mIn
                      refine ⟨stIn, inObjs, len', hMetaIn, hRemIn, hLenInLe, hLenInBV, hMeasIn,
                        hInLen, hInCl, hInX, hmIn, hWlInNd, hxNotWlIn, hWlInMem, ?_, hInProp⟩
                      intro f hf hf0
                      rw [List.take_succ_eq_append_getElem hiLt, List.mem_append,
                        List.mem_singleton] at hf
                      rcases hf with hfOld | rfl
                      · exact hDoneI f hfOld hf0
                      · exact ⟨inObjs[idx_c], List.getElem_mem hidx_c, hocAddr, hCrc0⟩
                  · intro hcOddEq
                    have hcOdd : (c &&& 1#64) ≠ 0#64 := of_decide_eq_false hcOddEq
                    apply hJ5 (lenBV', ()) mIn
                    refine ⟨stIn, inObjs, len', hMetaIn, hRemIn, hLenInLe, hLenInBV, hMeasIn,
                      hInLen, hInCl, hInX, hmIn, hWlInNd, hxNotWlIn, hWlInMem, ?_, hInProp⟩
                    intro f hf hf0
                    rw [List.take_succ_eq_append_getElem hiLt, List.mem_append,
                      List.mem_singleton] at hf
                    rcases hf with hfOld | rfl
                    · exact hDoneI f hfOld hf0
                    · exact absurd hf0 hcOdd
              · intro hiNotUlt
                have hiEq : i = x.childFields.length := by
                  rw [hiBV, BitVec.ult, hi64, hn64] at hiNotUlt
                  have : ¬ i < x.childFields.length := of_decide_eq_false hiNotUlt
                  omega
                subst hiEq
                rw [List.take_of_length_le (Nat.le_refl _)] at hDoneI
                refine hIH0 (2 * unmarkedCount inObjs + len') (lenBV', ()) mIn (by omega)
                  ⟨stIn, inObjs, len', hMetaIn, hRemIn, hLenInLe, hLenInBV, rfl, hInLen, hInCl,
                    hmIn, hWlInNd, hWlInMem, ?_⟩
                intro k hk hk'
                have hp := hInProp k hk hk'
                refine ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, ?_⟩
                intro hnz h0 hnotWl f hf hf0
                by_cases hkx : inObjs[k].addr = xAddr
                · have hndIn : (inObjs.map LcnfObj.addr).Nodup :=
                    lcnfHeap_nodup_addrs (sep_pull_heap hmIn)
                  have hEqObj := nodup_addr_eq_of_mem hndIn (List.getElem_mem hk')
                    (List.getElem_mem (by omega : idx_x < inObjs.length))
                    (by rw [hkx, hInX', hxAddrEq])
                  rw [hEqObj, hInX'] at hf
                  exact hDoneI f hf hf0
                · exact hp.2.2.2.2.2 hnz h0 hnotWl hkx f hf hf0
            · intro J1 hJ1
              rw [htagShift]
              refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
              dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
              constructor
              · intro htCloEq
                have htClo : x.tag = closureTag := by
                  have h := congrArg BitVec.toNat (of_decide_eq_true htCloEq)
                  simpa [closureTag, Nat.mod_eq_of_lt (by omega : x.tag < 2 ^ 64)] using h
                dfs_pure_steps
                have hldM : loadVal mCur i64 (xAddr + 16#64) = some x.cloMeta := by
                  rw [← hxAddrEq]
                  exact lcnfHeap_load_cloMeta hidx_x htClo (sep_pull_heap hmCur)
                refine wp_load_of hldM ?_
                dfs_pure_steps
                have hsp := hxWf.2.2.2.2.2.2.2.2.2
                simp only [htClo, ↓reduceIte] at hsp
                rw [LcnfObj.cloMeta, cloMetaWord_nfix x.arity x.fields.length hsp.1 hsp.2.1]
                exact hJ1 _ mCur ⟨by simp [LcnfObj.childFields, htClo],
                  by simp [LcnfObj.fieldsOff, htClo], rfl⟩
              · intro htCloNe
                have htNotClo : x.tag ≠ closureTag := fun h =>
                  of_decide_eq_false htCloNe (by rw [h]; rfl)
                refine wp_join_group DispPost
                  (fun _ xs mD h => by rcases xs with ⟨a, b, ⟨⟩⟩; exact hJ1 (a, b, ()) mD h) ?_
                intro J2 hJ2
                refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
                dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
                constructor
                · intro htArrEq
                  have htArr : x.tag = arrayTag := by
                    have h := congrArg BitVec.toNat (of_decide_eq_true htArrEq)
                    simpa [arrayTag, Nat.mod_eq_of_lt (by omega : x.tag < 2 ^ 64)] using h
                  dfs_pure_steps
                  have hldA : loadVal mCur i64 (xAddr + 8#64) =
                      some (BitVec.ofNat 64 x.fields.length) := by
                    rw [← hxAddrEq]
                    exact lcnfHeap_load_arrSize hidx_x htArr (sep_pull_heap hmCur)
                  refine wp_load_of hldA ?_
                  exact hJ2 _ mCur ⟨by simp [LcnfObj.childFields, htArr],
                    by simp [LcnfObj.fieldsOff, htArr], rfl⟩
                · intro htArrNe
                  have htNotArr : x.tag ≠ arrayTag := fun h =>
                    of_decide_eq_false htArrNe (by rw [h]; rfl)
                  refine wp_join_group DispPost
                    (fun _ xs mD h => by rcases xs with ⟨a, b, ⟨⟩⟩; exact hJ2 (a, b, ()) mD h) ?_
                  intro J3 hJ3
                  refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
                  dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
                  constructor
                  · intro htCtorEq
                    have htLe : x.tag ≤ 244 := by
                      have h244 : (244#64).toNat = 244 := by decide
                      have htag64 : (BitVec.ofNat 64 x.tag).toNat = x.tag :=
                        Nat.mod_eq_of_lt (by omega)
                      simp only [BitVec.ule, htag64, h244] at htCtorEq
                      exact of_decide_eq_true htCtorEq
                    dfs_pure_steps
                    rw [LcnfObj.header_other x hxCs hxOth hxTag]
                    have hsp := hxWf.2.2.2.2.2.2.2.2.2
                    have hsa : x.tag ≠ sarrayTag := by unfold sarrayTag; omega
                    have hstr : x.tag ≠ stringTag := by unfold stringTag; omega
                    have hmpz : x.tag ≠ mpzTag := by unfold mpzTag; omega
                    simp only [htNotClo, htNotArr, hsa, hstr, hmpz, ↓reduceIte] at hsp
                    exact hJ3 _ mCur ⟨by simp [LcnfObj.childFields, htLe, hsp.2.1],
                      by simp [LcnfObj.fieldsOff, htNotClo, htNotArr], rfl⟩
                  · intro htOtherEq
                    have htGt : ¬ x.tag ≤ 244 := by
                      have h244 : (244#64).toNat = 244 := by decide
                      have htag64 : (BitVec.ofNat 64 x.tag).toNat = x.tag :=
                        Nat.mod_eq_of_lt (by omega)
                      simp only [BitVec.ule, htag64, h244] at htOtherEq
                      exact of_decide_eq_false htOtherEq
                    exact hJ3 _ mCur ⟨by simp [LcnfObj.childFields, htGt, htNotClo, htNotArr],
                      by simp [LcnfObj.fieldsOff, htNotClo, htNotArr], rfl⟩
          · intro hLenZeroEq
            have hLenZero : len = 0 := by
              rw [hLenBV, BitVec.ult, hLen64] at hLenZeroEq
              have h0m : (0#64).toNat = 0 := by decide
              rw [h0m] at hLenZeroEq
              have : ¬ 0 < len := of_decide_eq_false hLenZeroEq
              omega
            subst hLenZero
            refine hPost stCur curObjs mCur hMeta hRem ?_ hmCur
            refine ⟨hCurLen, hObjsWf, hObjsCl, hCurCl, ?_⟩
            intro p hp
            rw [List.mem_iff_getElem] at hp
            obtain ⟨k, hk, rfl⟩ := hp
            have hk0 : k < objs.length := by
              rw [List.length_zip, hCurLen, Nat.min_self] at hk; exact hk
            have hk' : k < curObjs.length := by omega
            simp only [List.getElem_zip]
            have hp0 := hCurProp k hk0 hk'
            refine ⟨hp0.2.1, hp0.1.1, hp0.1.2.1, hp0.1.2.2.1, hp0.1.2.2.2.1, hp0.1.2.2.2.2.1,
              hp0.1.2.2.2.2.2.1, hp0.1.2.2.2.2.2.2.1, hp0.1.2.2.2.2.2.2.2.1,
              hp0.1.2.2.2.2.2.2.2.2.1, hp0.1.2.2.2.2.2.2.2.2.2.1, hp0.1.2.2.2.2.2.2.2.2.2.2.1,
              hp0.1.2.2.2.2.2.2.2.2.2.2.2, hp0.2.2.1, hp0.2.2.2.1, ?_⟩
            intro hknz
            constructor
            · exact hp0.2.2.2.2.1 hknz
            · intro hreach
              obtain ⟨kr, hkr', hkrAddr, hkr0⟩ := nonPersistReach_mark_complete hCurLen hndO
                (fun j hj hj' => (hCurProp j hj hj').2.2.1)
                (fun j hj hj' => (hCurProp j hj hj').1)
                (fun j hj hj' hnz h0 => (hCurProp j hj hj').2.2.2.2.2 hnz h0 (by simp))
                hreach
              have hndCur : (curObjs.map LcnfObj.addr).Nodup :=
                lcnfHeap_nodup_addrs (sep_pull_heap hmCur)
              have hEqObj := nodup_addr_eq_of_mem hndCur (List.getElem_mem hk')
                (List.getElem_mem hkr') (by rw [hp0.1.1, hkrAddr])
              rw [hEqObj]; exact hkr0

/-! ## `lcnf_dec_ref_cold_wp` -/

theorem lcnf_dec_ref_cold_wp (Γ : Env)
    (hFree : ∀ xs m Q X, lcnfFreeObjSpec xs m Q X →
      Γ "lcnf_free_obj" [i64, i64] [] xs m Q X) :
    ∀ (xs : Tup Val lcnf_dec_ref_cold.as) (m : Mem 64)
      (Q : Post lcnf_dec_ref_cold.rs) (X : XPost),
      lcnfDecRefColdSpec xs m Q X →
      Func.wp Γ lcnf_dec_ref_cold.body xs m Q X := by
  dsimp [lcnf_dec_ref_cold]
  intro ⟨rt, o, ⟨⟩⟩ m Q X hSpec
  dsimp [Func.wp, lcnf_dec_ref_cold_body]
  rcases hSpec with ⟨heven, st, objs, R, hCapLe, hm, hRootEx, hObjsWf, hObjsCl, hRcSound, hPost⟩
  have hndO : (objs.map LcnfObj.addr).Nodup := lcnfHeap_nodup_addrs (sep_pull_heap hm)
  obtain ⟨obj0, hobj0Mem, hobj0Addr, hobj0Rc⟩ := hRootEx
  dfs_pure_steps
  refine wp_load_of (rtC0Inv_load_s_st_cold_decs hm) ?_
  dfs_pure_steps
  refine wp_store_sep (rtC0Inv_store_s_st_cold_decs hm) ?_
  intro m1 hm1
  let st1 := st.withColdDecsInc
  dfs_pure_steps
  refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
  dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
  constructor
  · intro ht; exfalso; exact of_decide_eq_true ht heven
  · intro _
    dfs_pure_steps
    refine wp_load_of (rtC0Inv_load_s_work hm1) ?_
    dfs_pure_steps
    refine wp_load_of (rtC0Inv_load_s_work_cap hm1) ?_
    refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
    dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
    constructor
    · intro hcap0
      exfalso
      have h0 : st1.hdr.s_work_cap = 0#64 := of_decide_eq_true hcap0
      have h0n : st.workCap = 0 := by
        unfold RtC0State.workCap; change st1.hdr.s_work_cap.toNat = 0; rw [h0]; rfl
      have hpos : 0 < objs.length := List.length_pos_of_mem hobj0Mem
      omega
    · intro _
      dfs_pure_steps
      have h0lt : 0 < st1.workBuf.length := by
        rw [st1.workLen]; change 0 < st.workCap
        have hpos : 0 < objs.length := List.length_pos_of_mem hobj0Mem
        omega
      have hstW0 := rtC0Inv_store_work h0lt o hm1
      have hmul0 : (0#64 : BitVec 64) * 8#64 = BitVec.ofNat 64 (8 * 0) := by decide
      rw [← hmul0] at hstW0
      refine wp_store_sep hstW0 ?_
      intro m2 hm2
      let st2 := st1.withWorkBuf (st1.workBuf.set 0 o) (by rw [List.length_set]; exact st1.workLen)
      let OuterInv : Nat → Tup Val [i64] → Mem 64 → Prop := fun n (lenBV, _) mCur =>
        ∃ (stCur : RtC0State) (curObjs : List LcnfObj) (len : Nat),
          stCur.PreservesMeta st ∧ stCur.rem = st.rem ∧
          len ≤ st.workCap ∧ lenBV = BitVec.ofNat 64 len ∧
          curObjs.length = n ∧ curObjs.length ≤ objs.length ∧
          (∀ o' ∈ curObjs, o'.Wf) ∧ lcnfHeapClosed curObjs ∧
          (rtC0Inv rt stCur ⋆ lcnfHeap curObjs ⋆ R) mCur ∧
          (stCur.workBuf.take len).Nodup ∧
          (o ∈ stCur.workBuf.take len ∨ ∀ o' ∈ curObjs, o'.addr ≠ o) ∧
          (∀ a ∈ stCur.workBuf.take len,
            ∃ obj ∈ curObjs, obj.addr = a ∧ obj.rc = 1#32 ∧ NonPersistReach objs o a) ∧
          (∀ p ∈ curObjs, p.rc = 0#32 → ∀ f ∈ p.childFields, (f &&& 1#64) = 0#64 →
            ∃ q ∈ curObjs, q.addr = f ∧ q.rc = 0#32) ∧
          (∀ y ∈ curObjs, 0 < y.rc.toInt →
            nonPersistRefs curObjs y.addr + (stCur.workBuf.take len).count y.addr ≤ y.rc.toNat) ∧
          (∀ o' ∈ curObjs, ∃ orig ∈ objs, SameNonRc orig o' ∧
            ((orig.rc = 0#32 ∧ o'.rc = 0#32) ∨
             (0 < orig.rc.toInt ∧ 0 < o'.rc.toInt ∧ o'.rc.toInt ≤ orig.rc.toInt))) ∧
          (∀ orig ∈ objs, orig.rc = 0#32 → ∃ o' ∈ curObjs, o'.addr = orig.addr ∧ o'.rc = 0#32) ∧
          (∀ orig ∈ objs, 0 < orig.rc.toInt →
            let dropped :=
              (if orig.addr = o then 1 else 0) + nonPersistRefs (freedObjs objs curObjs) orig.addr
            (∀ o' ∈ curObjs, o'.addr = orig.addr →
              o'.rc.toNat + dropped = orig.rc.toNat + (stCur.workBuf.take len).count orig.addr) ∧
            (orig ∈ freedObjs objs curObjs →
              orig.rc.toNat = dropped ∧ NonPersistReach objs o orig.addr))
      refine wp_loop_group OuterInv ?_ (fun J0 hJ0 => by
        dsimp
        have htk1 : st2.workBuf.take 1 = [o] := by
          simpa [st2, RtC0State.withWorkBuf] using list_take_set_append st1.workBuf h0lt o
        refine hJ0 objs.length (1#64, ()) m2
          ⟨st2, objs, 1, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl,
            by have := List.length_pos_of_mem hobj0Mem; omega, rfl, rfl, Nat.le_refl _,
            hObjsWf, hObjsCl, hm2, by rw [htk1]; simp, Or.inl (by rw [htk1]; simp), ?_,
            hRcSound.1, ?_, ?_, ?_, ?_⟩
        · intro a ha
          rw [htk1, List.mem_singleton] at ha; subst ha
          exact ⟨obj0, hobj0Mem, hobj0Addr, hobj0Rc,
            NonPersistReach.refl ⟨obj0, hobj0Mem, hobj0Addr, by rw [hobj0Rc]; decide⟩⟩
        · intro y hy hyPos
          have hcnt : (st2.workBuf.take 1).count y.addr = if y.addr = o then 1 else 0 := by
            rw [htk1, List.count_singleton]
            by_cases h : y.addr = o
            · simp [h]
            · simp [h, Ne.symm h]
          rw [hcnt]; exact hRcSound.2 y hy hyPos
        · intro o' ho'
          refine ⟨o', ho', SameNonRc.refl o', ?_⟩
          by_cases h0 : o'.rc = 0#32
          · exact Or.inl ⟨h0, h0⟩
          · exact Or.inr ⟨objWf_rc_pos (hObjsWf o' ho') h0,
              objWf_rc_pos (hObjsWf o' ho') h0, Int.le_refl _⟩
        · intro orig horig h0
          exact ⟨orig, horig, rfl, h0⟩
        · intro orig horig _
          rw [freedObjs_self]
          simp only [nonPersistRefs, List.foldl_nil, Nat.add_zero]
          refine ⟨fun o' ho' had => ?_, fun h => nomatch h⟩
          have heq := nodup_addr_eq_of_mem hndO ho' horig had
          subst heq
          have hcnt : (st2.workBuf.take 1).count o'.addr = if o'.addr = o then 1 else 0 := by
            rw [htk1, List.count_singleton]
            by_cases h : o'.addr = o
            · simp [h]
            · simp [h, Ne.symm h]
          rw [hcnt]
      )
      intro J0 n ⟨lenBV, ⟨⟩⟩ mCur hIH0
        ⟨stCur, curObjs, len, hMeta, hRem, hLenLe, hLenBV, hCurLen, hCurLeO, hCurWf, hCurCl, hmCur,
          hWlNd, hRootState, hWlMem, hPersCl, hRcCur, hCurOrig, hOrigPers, hOrigEq⟩
      have hWorkEq : stCur.hdr.s_work = st.hdr.s_work := hMeta.2.2.2.2.1.symm
      have hCapEq : stCur.hdr.s_work_cap = st.hdr.s_work_cap := hMeta.2.2.2.2.2.1.symm
      have hCapNat : stCur.workBuf.length = st.workCap := by rw [stCur.workLen, hCapEq]; rfl
      have hLen64 : (BitVec.ofNat 64 len).toNat = len :=
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hLenLe st.hdr.s_work_cap.isLt)
      dfs_pure_steps
      refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
      dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
      constructor
      · intro hLenPosEq
        have hLenPos : 0 < len := by
          rw [hLenBV, BitVec.ult, hLen64] at hLenPosEq
          have h0m : (0#64).toNat = 0 := by decide
          rw [h0m] at hLenPosEq
          exact of_decide_eq_true hLenPosEq
        let len0 : Nat := len - 1
        have hLen0Lt : len0 < stCur.workBuf.length := by omega
        have hSubBV : lenBV - 1#64 = BitVec.ofNat 64 len0 := by
          rw [hLenBV]
          apply BitVec.eq_of_toNat_eq
          have hlt64 : len < 2 ^ 64 := Nat.lt_of_le_of_lt hLenLe st.hdr.s_work_cap.isLt
          bv_omega
        dfs_pure_steps
        rw [hSubBV]
        have hldX : loadVal mCur i64 (st.hdr.s_work + BitVec.ofNat 64 len0 * 8#64) =
            some (stCur.workBuf[len0]'hLen0Lt) := by
          rw [← hWorkEq, bv64_mul8_comm]
          exact rtC0Inv_load_work hLen0Lt hmCur
        refine wp_load_of hldX ?_
        let xAddr : BitVec 64 := stCur.workBuf[len0]'hLen0Lt
        have hTkPop : stCur.workBuf.take len = stCur.workBuf.take len0 ++ [xAddr] := by
          have h1 : len = len0 + 1 := by omega
          rw [h1]; exact List.take_succ_eq_append_getElem hLen0Lt
        have hxInWl : xAddr ∈ stCur.workBuf.take len := by rw [hTkPop]; simp
        have hWl0Nd : (stCur.workBuf.take len0).Nodup := by
          rw [hTkPop, List.nodup_append] at hWlNd; exact hWlNd.1
        have hxNotWl0 : xAddr ∉ stCur.workBuf.take len0 := by
          rw [hTkPop, List.nodup_append] at hWlNd
          intro hm; exact hWlNd.2.2 xAddr hm xAddr List.mem_cons_self rfl
        obtain ⟨xObj, hxMem, hxAddrEq, hxRc1, hxReach⟩ := hWlMem xAddr hxInWl
        rw [List.mem_iff_getElem] at hxMem
        obtain ⟨idx_x, hidx_x, rfl⟩ := hxMem
        let x : LcnfObj := curObjs[idx_x]'hidx_x
        have hxWf : x.Wf := hCurWf x (List.getElem_mem hidx_x)
        have hndCur : (curObjs.map LcnfObj.addr).Nodup :=
          lcnfHeap_nodup_addrs (sep_pull_heap hmCur)
        -- Crucial: no object in `curObjs` points to `xAddr`!
        have hxNoRefs : ∀ p ∈ curObjs, xAddr ∉ p.childFields := by
          have hxPos : 0 < x.rc.toInt := by rw [hxRc1]; decide
          have hrcX := hRcCur x (List.getElem_mem hidx_x) hxPos
          rw [hxAddrEq, hxRc1] at hrcX
          have hcnt1 : 1 ≤ (stCur.workBuf.take len).count xAddr := List.count_pos_iff.mpr hxInWl
          have h1n : (1#32).toNat = 1 := rfl
          rw [h1n] at hrcX
          have hnp0 : nonPersistRefs curObjs xAddr = 0 := by omega
          intro p hp hmemC
          by_cases hp0 : p.rc = 0#32
          · obtain ⟨q, hqMem, hqAddr, hq0⟩ :=
              hPersCl p hp hp0 xAddr hmemC (hxAddrEq ▸ objWf_addr_even hxWf)
            have hEq := nodup_addr_eq_of_mem hndCur hqMem (List.getElem_mem hidx_x)
              (hqAddr.trans hxAddrEq.symm)
            rw [hEq] at hq0
            exact absurd (hq0.symm.trans hxRc1) (by decide)
          · exact nonPersistRefs_eq_zero_imp curObjs xAddr hnp0 p hp hp0 hmemC
        -- Exact original object matching `x` and its RC equation:
        obtain ⟨origX, horigXMem, horigXSame, horigXRc⟩ := hCurOrig x (List.getElem_mem hidx_x)
        have horigXPos : 0 < origX.rc.toInt := by
          rcases horigXRc with ⟨_, h0⟩ | ⟨hpos, _, _⟩
          · exact absurd (h0.symm.trans hxRc1) (by decide)
          · exact hpos
        have horigXAddr : origX.addr = xAddr := by rw [← horigXSame.1, hxAddrEq]
        have horigXDrop : origX.rc.toNat =
            (if origX.addr = o then 1 else 0) +
              nonPersistRefs (freedObjs objs curObjs) origX.addr := by
          have hEq := (hOrigEq origX horigXMem horigXPos).1 x (List.getElem_mem hidx_x) horigXSame.1
          have hcntX : (stCur.workBuf.take len).count origX.addr = 1 := by
            rw [horigXAddr, hTkPop, List.count_append, List.count_eq_zero.mpr hxNotWl0]
            simp
          rw [hcntX, hxRc1] at hEq
          have h1n : (1#32).toNat = 1 := rfl
          rw [h1n] at hEq; omega
        have hldHdr : loadVal mCur i64 xAddr = some x.header := by
          rw [← hxAddrEq]; exact lcnfHeap_load_header hidx_x (sep_pull_heap hmCur)
        refine wp_load_of hldHdr ?_
        dfs_pure_steps
        have hxCs := hxWf.2.2.2.1; have hxOth := hxWf.2.2.2.2.1; have hxTag := hxWf.2.2.2.2.2.1
        have htagShift : x.header >>> 56 = BitVec.ofNat 64 x.tag :=
          LcnfObj.header_tag x hxCs hxOth hxTag
        let DispPost : Tup Val [i64, i64] → Mem 64 → Prop := fun (nBV, offBV, _) mD =>
          nBV = BitVec.ofNat 64 x.childFields.length ∧ offBV = x.fieldsOff ∧ mD = mCur
        refine wp_join_group DispPost ?_ ?_
        · intro _ ⟨nBV, offBV, ⟨⟩⟩ mD ⟨hnBV, hoffBV, hmD⟩
          subst mD; subst hnBV hoffBV
          let InnerInv : Nat → Tup Val [i64, i64] → Mem 64 → Prop :=
            fun rem (lenBV', iBV, _) mIn =>
              ∃ (stIn : RtC0State) (inObjs : List LcnfObj) (len' i : Nat),
                stIn.PreservesMeta st ∧ stIn.rem = st.rem ∧
                len' ≤ st.workCap ∧ lenBV' = BitVec.ofNat 64 len' ∧
                i ≤ x.childFields.length ∧ iBV = BitVec.ofNat 64 i ∧
                rem = x.childFields.length - i ∧
                inObjs.length = curObjs.length ∧ inObjs.length ≤ objs.length ∧
                inObjs[idx_x]? = some x ∧
                (∀ o' ∈ inObjs, o'.Wf) ∧ lcnfHeapClosed inObjs ∧
                (∀ p ∈ inObjs, xAddr ∉ p.childFields) ∧
                freedObjs objs inObjs = freedObjs objs curObjs ∧
                (rtC0Inv rt stIn ⋆ lcnfHeap inObjs ⋆ R) mIn ∧
                (stIn.workBuf.take len').Nodup ∧ xAddr ∉ stIn.workBuf.take len' ∧
                (o ∈ stIn.workBuf.take len' ∨ o = xAddr ∨ ∀ o' ∈ inObjs, o'.addr ≠ o) ∧
                (∀ a ∈ stIn.workBuf.take len',
                  ∃ obj ∈ inObjs, obj.addr = a ∧ obj.rc = 1#32 ∧ NonPersistReach objs o a) ∧
                (∀ p ∈ inObjs, p.rc = 0#32 → ∀ f ∈ p.childFields, (f &&& 1#64) = 0#64 →
                  ∃ q ∈ inObjs, q.addr = f ∧ q.rc = 0#32) ∧
                (∀ y ∈ inObjs, y.addr ≠ xAddr → 0 < y.rc.toInt →
                  nonPersistRefs (inObjs.eraseIdx idx_x) y.addr +
                    (x.childFields.drop i).count y.addr +
                    (stIn.workBuf.take len').count y.addr ≤ y.rc.toNat) ∧
                (∀ o' ∈ inObjs, ∃ orig ∈ objs, SameNonRc orig o' ∧
                  ((orig.rc = 0#32 ∧ o'.rc = 0#32) ∨
                   (0 < orig.rc.toInt ∧ 0 < o'.rc.toInt ∧ o'.rc.toInt ≤ orig.rc.toInt))) ∧
                (∀ orig ∈ objs, orig.rc = 0#32 →
                  ∃ o' ∈ inObjs, o'.addr = orig.addr ∧ o'.rc = 0#32) ∧
                (∀ orig ∈ objs, 0 < orig.rc.toInt →
                  let dropped :=
                    (if orig.addr = o then 1 else 0) +
                      nonPersistRefs (freedObjs objs inObjs) orig.addr
                  (∀ o' ∈ inObjs, o'.addr = orig.addr → o'.addr ≠ xAddr →
                    o'.rc.toNat + dropped + (x.childFields.take i).count orig.addr =
                      orig.rc.toNat + (stIn.workBuf.take len').count orig.addr) ∧
                  (orig ∈ freedObjs objs inObjs →
                    orig.rc.toNat = dropped ∧ NonPersistReach objs o orig.addr))
          refine wp_loop_group InnerInv ?_ (fun J4 hJ4 => by
            dsimp
            refine hJ4 x.childFields.length (BitVec.ofNat 64 len0, 0#64, ()) mCur
              ⟨stCur, curObjs, len0, 0, hMeta, hRem, by omega, rfl, Nat.zero_le _, rfl, rfl,
                rfl, hCurLeO, List.getElem?_eq_getElem hidx_x, hCurWf, hCurCl, hxNoRefs, rfl,
                hmCur, hWl0Nd, hxNotWl0, ?_,
                ?_, hPersCl, ?_, hCurOrig, hOrigPers, ?_⟩
            · rcases hRootState with hIn | hOut
              · rw [hTkPop, List.mem_append, List.mem_singleton] at hIn
                rcases hIn with h0 | rfl
                · exact Or.inl h0
                · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr hOut)
            · intro a ha
              exact hWlMem a (by rw [hTkPop]; exact List.mem_append_left _ ha)
            · intro y hy hyNe hyPos
              have hrcY := hRcCur y hy hyPos
              have hsp := nonPersistRefs_focus curObjs hidx_x y.addr
              have hnzX : x.rc ≠ 0#32 := by rw [hxRc1]; decide
              change nonPersistRefs curObjs y.addr =
                (if x.rc = 0#32 then 0 else x.childFields.count y.addr) +
                nonPersistRefs (curObjs.eraseIdx idx_x) y.addr at hsp
              simp only [hnzX, ↓reduceIte] at hsp
              have hcntY : (stCur.workBuf.take len).count y.addr =
                  (stCur.workBuf.take len0).count y.addr := by
                rw [hTkPop, List.count_append, List.count_singleton]
                simp [Ne.symm hyNe]
              rw [hsp, hcntY] at hrcY
              simp only [List.drop_zero]
              omega
            · intro orig horig hpos
              have hEq := hOrigEq orig horig hpos
              refine ⟨fun o' ho' had hneX => ?_, hEq.2⟩
              have h1 := hEq.1 o' ho' had
              have hcntO : (stCur.workBuf.take len).count orig.addr =
                  (stCur.workBuf.take len0).count orig.addr := by
                rw [hTkPop, List.count_append, List.count_singleton]
                have : orig.addr ≠ xAddr := had ▸ hneX
                simp [Ne.symm this]
              rw [hcntO] at h1
              simpa using h1)
          intro J4 rem ⟨lenBV', iBV, ⟨⟩⟩ mIn hIH4
            ⟨stIn, inObjs, len', i, hMetaIn, hRemIn, hLenInLe, hLenInBV, hiLe, hiBV, hRemEq,
              hInLen, hInLeO, hInX, hInWf, hInCl, hNoRefsIn, hFreedEq, hmIn, hWlInNd, hxNotWlIn,
              hRootIn, hWlInMem, hPersIn, hRcIn, hInOrig, hOrigPersIn, hOrigEqIn⟩
          have hidx_x_in : idx_x < inObjs.length := by omega
          have hInX' : inObjs[idx_x]'hidx_x_in = x :=
            Option.some.inj (by rwa [List.getElem?_eq_getElem hidx_x_in] at hInX)
          have hWorkInEq : stIn.hdr.s_work = st.hdr.s_work := hMetaIn.2.2.2.2.1.symm
          have hCapInEq : stIn.hdr.s_work_cap = st.hdr.s_work_cap := hMetaIn.2.2.2.2.2.1.symm
          have hCapInNat : stIn.workBuf.length = st.workCap := by
            rw [stIn.workLen, hCapInEq]; rfl
          have hChildLt : x.childFields.length < 2 ^ 64 := objWf_childFields_lt hxWf
          have hi64 : (BitVec.ofNat 64 i).toNat = i := Nat.mod_eq_of_lt (by omega)
          have hn64 : (BitVec.ofNat 64 x.childFields.length).toNat = x.childFields.length :=
            Nat.mod_eq_of_lt hChildLt
          have hndIn : (inObjs.map LcnfObj.addr).Nodup :=
            lcnfHeap_nodup_addrs (sep_pull_heap hmIn)
          dfs_pure_steps
          refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
          dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
          constructor
          · intro hiUlt
            have hiLt : i < x.childFields.length := by
              rw [hiBV, BitVec.ult, hi64, hn64] at hiUlt; exact of_decide_eq_true hiUlt
            dfs_pure_steps
            have hldC : loadVal mIn i64 ((xAddr + x.fieldsOff) + 8#64 * iBV) =
                some (x.childFields[i]'hiLt) := by
              have h1 := lcnfHeap_load_child hidx_x_in (by rw [hInX']; exact hxWf)
                (sep_pull_heap hmIn) (by rw [hInX']; exact hiLt)
              simpa [x, hInX', hxAddrEq, hiBV, bv64_8_mul] using h1
            refine wp_load_of hldC ?_
            let c : BitVec 64 := x.childFields[i]'hiLt
            have hDropCons : x.childFields.drop i = c :: x.childFields.drop (i + 1) :=
              List.drop_eq_getElem_cons hiLt
            have hTakeSucc : x.childFields.take (i + 1) = x.childFields.take i ++ [c] :=
              List.take_succ_eq_append_getElem hiLt
            let StepPost : Tup Val [i64] → Mem 64 → Prop := fun (lenBV'', _) mStep =>
              ∃ (stOut : RtC0State) (outObjs : List LcnfObj) (len'' : Nat),
                stOut.PreservesMeta st ∧ stOut.rem = st.rem ∧
                len'' ≤ st.workCap ∧ lenBV'' = BitVec.ofNat 64 len'' ∧
                outObjs.length = curObjs.length ∧ outObjs.length ≤ objs.length ∧
                outObjs[idx_x]? = some x ∧
                (∀ o' ∈ outObjs, o'.Wf) ∧ lcnfHeapClosed outObjs ∧
                (∀ p ∈ outObjs, xAddr ∉ p.childFields) ∧
                freedObjs objs outObjs = freedObjs objs curObjs ∧
                (rtC0Inv rt stOut ⋆ lcnfHeap outObjs ⋆ R) mStep ∧
                (stOut.workBuf.take len'').Nodup ∧ xAddr ∉ stOut.workBuf.take len'' ∧
                (o ∈ stOut.workBuf.take len'' ∨ o = xAddr ∨ ∀ o' ∈ outObjs, o'.addr ≠ o) ∧
                (∀ a ∈ stOut.workBuf.take len'',
                  ∃ obj ∈ outObjs, obj.addr = a ∧ obj.rc = 1#32 ∧ NonPersistReach objs o a) ∧
                (∀ p ∈ outObjs, p.rc = 0#32 → ∀ f ∈ p.childFields, (f &&& 1#64) = 0#64 →
                  ∃ q ∈ outObjs, q.addr = f ∧ q.rc = 0#32) ∧
                (∀ y ∈ outObjs, y.addr ≠ xAddr → 0 < y.rc.toInt →
                  nonPersistRefs (outObjs.eraseIdx idx_x) y.addr +
                    (x.childFields.drop (i + 1)).count y.addr +
                    (stOut.workBuf.take len'').count y.addr ≤ y.rc.toNat) ∧
                (∀ o' ∈ outObjs, ∃ orig ∈ objs, SameNonRc orig o' ∧
                  ((orig.rc = 0#32 ∧ o'.rc = 0#32) ∨
                   (0 < orig.rc.toInt ∧ 0 < o'.rc.toInt ∧ o'.rc.toInt ≤ orig.rc.toInt))) ∧
                (∀ orig ∈ objs, orig.rc = 0#32 →
                  ∃ o' ∈ outObjs, o'.addr = orig.addr ∧ o'.rc = 0#32) ∧
                (∀ orig ∈ objs, 0 < orig.rc.toInt →
                  let dropped :=
                    (if orig.addr = o then 1 else 0) +
                      nonPersistRefs (freedObjs objs outObjs) orig.addr
                  (∀ o' ∈ outObjs, o'.addr = orig.addr → o'.addr ≠ xAddr →
                    o'.rc.toNat + dropped + (x.childFields.take (i + 1)).count orig.addr =
                      orig.rc.toNat + (stOut.workBuf.take len'').count orig.addr) ∧
                  (orig ∈ freedObjs objs outObjs →
                    orig.rc.toNat = dropped ∧ NonPersistReach objs o orig.addr))
            refine wp_join_group StepPost ?_ ?_
            · intro _ ⟨lenBV'', ⟨⟩⟩ mStep ⟨stOut, outObjs, len'', h1, h2, h3, h4, h5, h6, h7, h8,
                h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩
              dsimp [Blocks.get]
              dfs_pure_steps
              have hi1BV : iBV + 1#64 = BitVec.ofNat 64 (i + 1) := by
                rw [hiBV]; apply BitVec.eq_of_toNat_eq; simp
              rw [hi1BV]
              exact hIH4 (x.childFields.length - (i + 1)) (lenBV'', BitVec.ofNat 64 (i + 1), ())
                mStep (by omega)
                ⟨stOut, outObjs, len'', i + 1, h1, h2, h3, h4, by omega, rfl, rfl, h5, h6, h7, h8,
                  h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩
            · intro J5 hJ5
              dfs_pure_steps
              refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
              dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
              constructor
              · intro hcEvenEq
                have hcEven : (c &&& 1#64) = 0#64 := of_decide_eq_true hcEvenEq
                have hcInX : c ∈ inObjs[idx_x].childFields := by
                  rw [hInX']; exact List.getElem_mem hiLt
                obtain ⟨oc, hocMem, hocAddr⟩ :=
                  hInCl inObjs[idx_x] (List.getElem_mem (by omega)) c hcInX hcEven
                rw [List.mem_iff_getElem] at hocMem
                obtain ⟨idx_c, hidx_c, rfl⟩ := hocMem
                have hcWf : inObjs[idx_c].Wf := hInWf inObjs[idx_c] (List.getElem_mem hidx_c)
                have hneCX : c ≠ xAddr := fun h =>
                  hNoRefsIn inObjs[idx_x] (List.getElem_mem (by omega)) (h ▸ hcInX)
                have hidxNe : idx_c ≠ idx_x := fun h =>
                  hneCX (by subst h; rw [← hocAddr, hInX', hxAddrEq])
                have hldChdr : loadVal mIn i64 c = some inObjs[idx_c].header := by
                  rw [← hocAddr]; exact lcnfHeap_load_header hidx_c (sep_pull_heap hmIn)
                refine wp_load_of hldChdr ?_
                dfs_pure_steps
                rw [LcnfObj.header_rc inObjs[idx_c] hcWf.2.2.2.1 hcWf.2.2.2.2.1 hcWf.2.2.2.2.2.1]
                refine wp_join_group StepPost
                  (fun _ xs m6 h => by rcases xs with ⟨v, ⟨⟩⟩; exact hJ5 (v, ()) m6 h) ?_
                intro J6 hJ6
                refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
                dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
                constructor
                · intro hCrc1Eq
                  have hCrc164 : BitVec.ofNat 64 inObjs[idx_c].rc.toNat = 1#64 :=
                    of_decide_eq_true hCrc1Eq
                  have hCrc1 : inObjs[idx_c].rc = 1#32 := by
                    apply BitVec.eq_of_toNat_eq
                    have := congrArg BitVec.toNat hCrc164
                    simpa [Nat.mod_eq_of_lt (by omega : inObjs[idx_c].rc.toNat < 2 ^ 64)] using this
                  have hrcC := hRcIn inObjs[idx_c] (List.getElem_mem hidx_c)
                    (hocAddr.symm ▸ hneCX) (by rw [hCrc1]; decide)
                  rw [hocAddr, hDropCons, List.count_cons_self, hCrc1] at hrcC
                  have h1n : (1#32).toNat = 1 := rfl
                  rw [h1n] at hrcC
                  have hcNotWl : c ∉ stIn.workBuf.take len' := by
                    intro hmem
                    have hpos : 1 ≤ (stIn.workBuf.take len').count c := List.count_pos_iff.mpr hmem
                    omega
                  have hLenLtCap : len' < st.workCap := by
                    have hle := work_push_lt_cap hWlInNd hxNotWlIn hcNotWl hneCX
                      ⟨inObjs[idx_x]'(by omega), List.getElem_mem (by omega),
                        by rw [hInX']; exact hxAddrEq⟩
                      ⟨inObjs[idx_c], List.getElem_mem hidx_c, hocAddr⟩
                      (fun a ha => by
                        obtain ⟨obj, hobj, hoba, _, _⟩ := hWlInMem a ha
                        exact ⟨obj, hobj, hoba⟩)
                      (by omega : inObjs.length ≤ st.workCap)
                    simpa [List.length_take, hCapInNat, Nat.min_eq_left hLenInLe] using hle
                  refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
                  dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
                  constructor
                  · intro hEqCap
                    exfalso
                    have heq : BitVec.ofNat 64 len' = st.hdr.s_work_cap := by
                      rw [← hLenInBV]; exact of_decide_eq_true hEqCap
                    have hn := congrArg BitVec.toNat heq
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
                      (Nat.lt_of_le_of_lt hLenInLe st.hdr.s_work_cap.isLt)] at hn
                    change len' = st.workCap at hn
                    omega
                  · intro _
                    dfs_pure_steps
                    have hLen'Lt : len' < stIn.workBuf.length := by rw [hCapInNat]; exact hLenLtCap
                    have hstW := rtC0Inv_store_work hLen'Lt c hmIn
                    rw [hWorkInEq, ← bv64_mul8_comm len', ← hLenInBV] at hstW
                    refine wp_store_sep hstW ?_
                    intro mW hmW
                    let stIn' := stIn.withWorkBuf (stIn.workBuf.set len' c)
                      (by rw [List.length_set]; exact stIn.workLen)
                    dfs_pure_steps
                    have hLen1BV : lenBV' + 1#64 = BitVec.ofNat 64 (len' + 1) := by
                      rw [hLenInBV]; apply BitVec.eq_of_toNat_eq; simp
                    rw [hLen1BV]
                    have hTkPush : stIn'.workBuf.take (len' + 1) =
                        stIn.workBuf.take len' ++ [c] :=
                      list_take_set_append stIn.workBuf hLen'Lt c
                    obtain ⟨origC, horigCMem, horigCSame, horigCRc⟩ :=
                      hInOrig inObjs[idx_c] (List.getElem_mem hidx_c)
                    have horigCNz : origC.rc ≠ 0#32 := by
                      rcases horigCRc with ⟨_, h0⟩ | ⟨hpos, _, _⟩
                      · exact absurd (h0.symm.trans hCrc1) (by decide)
                      · intro h0; rw [h0] at hpos; exact absurd hpos (by decide)
                    have hcReach : NonPersistReach objs o c := by
                      refine NonPersistReach.step hxReach
                        ⟨origX, horigXMem, horigXAddr, ?_⟩ hcEven
                        ⟨origC, horigCMem, by rw [← horigCSame.1, hocAddr], horigCNz⟩
                      rw [← horigXSame.childFields_eq]; exact List.getElem_mem hiLt
                    apply hJ6 (BitVec.ofNat 64 (len' + 1), ()) mW
                    refine ⟨stIn', inObjs, len' + 1,
                      preservesMeta_trans hMetaIn ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
                      hRemIn, by omega, rfl, hInLen, hInLeO, hInX, hInWf, hInCl, hNoRefsIn,
                      hFreedEq, hmW, ?_, ?_, ?_, ?_, hPersIn, ?_, hInOrig, hOrigPersIn, ?_⟩
                    · rw [hTkPush, List.nodup_append]
                      refine ⟨hWlInNd, by simp, fun a ha b hb => ?_⟩
                      rw [List.mem_singleton] at hb; subst hb
                      exact fun heq => hcNotWl (heq ▸ ha)
                    · rw [hTkPush, List.mem_append, List.mem_singleton]
                      rintro (h | h)
                      · exact hxNotWlIn h
                      · exact hneCX h.symm
                    · rcases hRootIn with hIn | hEqX | hOut
                      · exact Or.inl (by rw [hTkPush]; exact List.mem_append_left _ hIn)
                      · exact Or.inr (Or.inl hEqX)
                      · exact Or.inr (Or.inr hOut)
                    · intro a ha
                      rw [hTkPush, List.mem_append, List.mem_singleton] at ha
                      rcases ha with haOld | rfl
                      · exact hWlInMem a haOld
                      · exact ⟨inObjs[idx_c], List.getElem_mem hidx_c, hocAddr, hCrc1, hcReach⟩
                    · intro y hy hyNe hyPos
                      have hrcY := hRcIn y hy hyNe hyPos
                      rw [hDropCons, List.count_cons] at hrcY
                      rw [hTkPush, List.count_append, List.count_singleton]
                      by_cases hyc : c = y.addr
                      · rw [hyc] at hrcY ⊢; simp at hrcY ⊢; omega
                      · simp at hrcY ⊢; omega
                    · intro orig horig hpos
                      have hEq := hOrigEqIn orig horig hpos
                      refine ⟨fun o' ho' had hneX => ?_, hEq.2⟩
                      have h1 := hEq.1 o' ho' had hneX
                      rw [hTakeSucc, hTkPush, List.count_append, List.count_append,
                        List.count_singleton]
                      omega
                · intro hCrcNe1Eq
                  have hCrcNe1 : inObjs[idx_c].rc ≠ 1#32 := fun h =>
                    of_decide_eq_false hCrcNe1Eq (by rw [h]; rfl)
                  refine wp_join_group (fun _ m7 => StepPost (lenBV', ()) m7)
                    (fun _ _ m7 h => by dsimp; exact hJ6 (lenBV', ()) m7 h) ?_
                  intro J7 hJ7
                  have hrc64 : (BitVec.ofNat 64 inObjs[idx_c].rc.toNat).toNat =
                      inObjs[idx_c].rc.toNat :=
                    Nat.mod_eq_of_lt (by omega : inObjs[idx_c].rc.toNat < 2 ^ 64)
                  refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
                  dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
                  constructor
                  · intro hGt1Eq
                    have hGt1 : 1 < inObjs[idx_c].rc.toNat := by
                      have h1m : (1#64).toNat = 1 := by decide
                      rw [BitVec.ult, h1m, hrc64] at hGt1Eq
                      exact of_decide_eq_true hGt1Eq
                    refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
                    dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
                    constructor
                    · intro _hLt214
                      dfs_pure_steps
                      rw [lcnfObjHeader_sub1_wf inObjs[idx_c] hcWf hGt1]
                      have hstC := lcnfHeap_store_rc hidx_c (inObjs[idx_c].rc - 1#32)
                        (sep_pull_heap hmIn)
                      rw [hocAddr] at hstC
                      refine wp_store_sep (R := rtC0Inv rt stIn ⋆ R) hstC ?_
                      intro mC hmC
                      let rc' : BitVec 32 := inObjs[idx_c].rc - 1#32
                      let inObjs' := inObjs.set idx_c (inObjs[idx_c].withRc rc')
                      have hmC' : (rtC0Inv rt stIn ⋆ lcnfHeap inObjs' ⋆ R) mC :=
                        sep_cast hmC (by ac_rfl)
                      have hrc'Int : rc'.toInt = inObjs[idx_c].rc.toInt - 1 :=
                        objWf_rc_sub1_toInt hcWf hGt1
                      have hrc'Pos : 0 < rc'.toInt := by
                        have hpos := objWf_rc_pos hcWf (fun h => by rw [h] at hGt1; simp at hGt1)
                        have hgtI : 1 < inObjs[idx_c].rc.toInt := by
                          have hlt := objWf_rc_lt hcWf
                          rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
                        omega
                      have hrc'Nz : rc' ≠ 0#32 := fun h => by
                        rw [h] at hrc'Pos; exact absurd hrc'Pos (by decide)
                      have hrcOldNz : inObjs[idx_c].rc ≠ 0#32 := fun h => by
                        rw [h] at hGt1; simp at hGt1
                      have hrc'Nat : rc'.toNat = inObjs[idx_c].rc.toNat - 1 :=
                        objRc_sub1_toNat hGt1
                      have hcWf' : (inObjs[idx_c].withRc rc').Wf :=
                        lcnfObjWf_withRc hcWf (by omega)
                      have hFreed' : freedObjs objs inObjs' = freedObjs objs curObjs := by
                        rw [freedObjs_set_rc, hFreedEq]
                      have hErEq : ∀ a, nonPersistRefs (inObjs'.eraseIdx idx_x) a =
                          nonPersistRefs (inObjs.eraseIdx idx_x) a := by
                        intro a
                        have h1 :=
                          nonPersistRefs_focus inObjs' (idx := idx_x) (by simp [inObjs']; omega) a
                        have h2 := nonPersistRefs_focus inObjs (idx := idx_x) hidx_x_in a
                        have hsetX : inObjs'[idx_x]'(by simp [inObjs']; omega) = x := by
                          simp [inObjs', List.getElem_set_ne hidxNe, hInX']
                        have hnpEq := nonPersistRefs_set_same_nz inObjs hidx_c hrcOldNz hrc'Nz a
                        change nonPersistRefs inObjs' a = nonPersistRefs inObjs a at hnpEq
                        rw [hsetX] at h1; rw [hInX'] at h2; omega
                      apply hJ7 () mC
                      refine ⟨stIn, inObjs', len', hMetaIn, hRemIn, hLenInLe, hLenInBV,
                        by simp [inObjs', hInLen], by simp [inObjs', hInLeO],
                        by rw [List.getElem?_set_ne hidxNe]; exact hInX, ?_,
                        lcnfHeapClosed_set_withRc hInCl hidx_c rc', ?_, hFreed', hmC',
                        hWlInNd, hxNotWlIn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                      · intro o' ho'
                        rw [List.mem_iff_getElem] at ho'
                        obtain ⟨k, hk, rfl⟩ := ho'
                        have hkin : k < inObjs.length := by simp [inObjs'] at hk; exact hk
                        by_cases hkc : k = idx_c
                        · subst hkc; simpa [inObjs'] using hcWf'
                        · rw [List.getElem_set_ne (Ne.symm hkc) hk]
                          exact hInWf inObjs[k] (List.getElem_mem hkin)
                      · intro p hp
                        rw [List.mem_iff_getElem] at hp
                        obtain ⟨k, hk, rfl⟩ := hp
                        have hkin : k < inObjs.length := by simp [inObjs'] at hk; exact hk
                        by_cases hkc : k = idx_c
                        · subst hkc; simpa [inObjs', LcnfObj.withRc, LcnfObj.childFields] using
                            hNoRefsIn inObjs[k] (List.getElem_mem hkin)
                        · rw [List.getElem_set_ne (Ne.symm hkc) hk]
                          exact hNoRefsIn inObjs[k] (List.getElem_mem hkin)
                      · rcases hRootIn with hIn | hEqX | hOut
                        · exact Or.inl hIn
                        · exact Or.inr (Or.inl hEqX)
                        · right; right; intro o' ho'
                          rw [List.mem_iff_getElem] at ho'
                          obtain ⟨k, hk, rfl⟩ := ho'
                          have hkin : k < inObjs.length := by simp [inObjs'] at hk; exact hk
                          by_cases hkc : k = idx_c
                          · subst hkc; simpa [inObjs', LcnfObj.withRc] using
                              hOut inObjs[k] (List.getElem_mem hkin)
                          · rw [List.getElem_set_ne (Ne.symm hkc) hk]
                            exact hOut inObjs[k] (List.getElem_mem hkin)
                      · intro a ha
                        obtain ⟨obj, hobjMem, hobjAddr, hobjRc, hobjReach⟩ := hWlInMem a ha
                        rw [List.mem_iff_getElem] at hobjMem
                        obtain ⟨k, hk, rfl⟩ := hobjMem
                        have hkc : k ≠ idx_c := fun h => by
                          subst h; rw [hobjRc] at hGt1; simp at hGt1
                        exact ⟨inObjs'[k]'(by simp [inObjs', hk]), List.getElem_mem _,
                          by simp [inObjs', List.getElem_set_ne (Ne.symm hkc), hobjAddr],
                          by simp [inObjs', List.getElem_set_ne (Ne.symm hkc), hobjRc], hobjReach⟩
                      · intro p hp hp0 f hf hf0
                        rw [List.mem_iff_getElem] at hp
                        obtain ⟨k, hk, rfl⟩ := hp
                        have hkin : k < inObjs.length := by simp [inObjs'] at hk; exact hk
                        have hkc : k ≠ idx_c := fun h => by
                          subst h; simp [inObjs', LcnfObj.withRc] at hp0; exact hrc'Nz hp0
                        rw [List.getElem_set_ne (Ne.symm hkc) hk] at hp0 hf
                        obtain ⟨q, hqMem, hqAddr, hq0⟩ := hPersIn inObjs[k]
                          (List.getElem_mem hkin) hp0 f hf hf0
                        rw [List.mem_iff_getElem] at hqMem
                        obtain ⟨kq, hkq, rfl⟩ := hqMem
                        have hqne : kq ≠ idx_c := fun h => by subst h; exact hrcOldNz hq0
                        exact ⟨inObjs'[kq]'(by simp [inObjs', hkq]), List.getElem_mem _,
                          by simp [inObjs', List.getElem_set_ne (Ne.symm hqne), hqAddr],
                          by simp [inObjs', List.getElem_set_ne (Ne.symm hqne), hq0]⟩
                      · intro y hy hyNe hyPos
                        rw [List.mem_iff_getElem] at hy
                        obtain ⟨k, hk, rfl⟩ := hy
                        have hkin : k < inObjs.length := by simp [inObjs'] at hk; exact hk
                        rw [hErEq]
                        by_cases hkc : k = idx_c
                        · subst hkc
                          simp only [inObjs', List.getElem_set_self, LcnfObj.withRc] at hyNe ⊢
                          have hrcY := hRcIn inObjs[k] (List.getElem_mem hkin) hyNe
                            (objWf_rc_pos hcWf hrcOldNz)
                          rw [hocAddr, hDropCons, List.count_cons_self] at hrcY
                          rw [hocAddr, hrc'Nat]
                          omega
                        · rw [List.getElem_set_ne (Ne.symm hkc) hk] at hyNe hyPos ⊢
                          have hrcY := hRcIn inObjs[k] (List.getElem_mem hkin) hyNe hyPos
                          rw [hDropCons, List.count_cons] at hrcY
                          have hneY : inObjs[k].addr ≠ c := by
                            intro heq
                            exact hkc (nodup_addr_idx_eq hndIn hkin hidx_c (heq.trans hocAddr.symm))
                          have : (c == inObjs[k].addr) = false :=
                            beq_eq_false_iff_ne.mpr (Ne.symm hneY)
                          simp [this] at hrcY; exact hrcY
                      · intro o' ho'
                        rw [List.mem_iff_getElem] at ho'
                        obtain ⟨k, hk, rfl⟩ := ho'
                        have hkin : k < inObjs.length := by simp [inObjs'] at hk; exact hk
                        by_cases hkc : k = idx_c
                        · subst hkc
                          obtain ⟨orig, horig, hsame, hrc⟩ :=
                            hInOrig inObjs[k] (List.getElem_mem hkin)
                          refine ⟨orig, horig, by simpa [inObjs'] using hsame.withRc_r rc', ?_⟩
                          rcases hrc with ⟨_, h0⟩ | ⟨hp1, _, hle⟩
                          · exact absurd h0 hrcOldNz
                          · exact Or.inr ⟨hp1, by simpa [inObjs', LcnfObj.withRc] using hrc'Pos,
                              by simp [inObjs', LcnfObj.withRc]; omega⟩
                        · rw [List.getElem_set_ne (Ne.symm hkc) hk]
                          exact hInOrig inObjs[k] (List.getElem_mem hkin)
                      · intro orig horig h0
                        obtain ⟨o', ho', hoad, ho0⟩ := hOrigPersIn orig horig h0
                        rw [List.mem_iff_getElem] at ho'
                        obtain ⟨k, hk, rfl⟩ := ho'
                        have hkc : k ≠ idx_c := fun h => by subst h; exact hrcOldNz ho0
                        exact ⟨inObjs'[k]'(by simp [inObjs', hk]), List.getElem_mem _,
                          by simp [inObjs', List.getElem_set_ne (Ne.symm hkc), hoad],
                          by simp [inObjs', List.getElem_set_ne (Ne.symm hkc), ho0]⟩
                      · intro orig horig hpos
                        have hEq := hOrigEqIn orig horig hpos
                        rw [freedObjs_set_rc]
                        refine ⟨fun o' ho' had hneX => ?_, hEq.2⟩
                        rw [List.mem_iff_getElem] at ho'
                        obtain ⟨k, hk, rfl⟩ := ho'
                        have hkin : k < inObjs.length := by simp [inObjs'] at hk; exact hk
                        by_cases hkc : k = idx_c
                        · subst hkc
                          simp only [inObjs', List.getElem_set_self, LcnfObj.withRc] at had hneX ⊢
                          have h1 := hEq.1 inObjs[k] (List.getElem_mem hkin) had hneX
                          have hadC : orig.addr = c := had.symm.trans hocAddr
                          rw [hTakeSucc, List.count_append, List.count_singleton, hrc'Nat]
                          rw [hadC] at h1 ⊢
                          simp only [beq_self_eq_true, ↓reduceIte]
                          omega
                        · rw [List.getElem_set_ne (Ne.symm hkc) hk] at had hneX ⊢
                          have h1 := hEq.1 inObjs[k] (List.getElem_mem hkin) had hneX
                          have hneY : orig.addr ≠ c := by
                            intro heq
                            exact hkc (nodup_addr_idx_eq hndIn hkin hidx_c
                              (had.trans (heq.trans hocAddr.symm)))
                          rw [hTakeSucc, List.count_append, List.count_singleton]
                          have : (c == orig.addr) = false := beq_eq_false_iff_ne.mpr (Ne.symm hneY)
                          simp [this, h1]
                    · intro hNotLt214
                      exfalso
                      have hlt := objWf_rc_lt hcWf
                      have h214 : (2147483648#64).toNat = 2147483648 := by decide
                      have hUltTrue :
                          (BitVec.ofNat 64 inObjs[idx_c].rc.toNat).ult 2147483648#64 = true := by
                        simp only [BitVec.ult, hrc64, h214, decide_eq_true_eq]; omega
                      rw [hUltTrue] at hNotLt214; contradiction
                  · intro hNotGt1
                    have hCrc0 : inObjs[idx_c].rc = 0#32 := by
                      have h1m : (1#64).toNat = 1 := by decide
                      rw [BitVec.ult, h1m, hrc64] at hNotGt1
                      have hle1 : inObjs[idx_c].rc.toNat ≤ 1 :=
                        Nat.le_of_not_lt (of_decide_eq_false hNotGt1)
                      have hne1 : inObjs[idx_c].rc.toNat ≠ 1 := fun h =>
                        hCrcNe1 (BitVec.eq_of_toNat_eq (by simp [h]))
                      apply BitVec.eq_of_toNat_eq; simp; omega
                    apply hJ7 () mIn
                    refine ⟨stIn, inObjs, len', hMetaIn, hRemIn, hLenInLe, hLenInBV, hInLen,
                      hInLeO, hInX, hInWf, hInCl, hNoRefsIn, hFreedEq, hmIn, hWlInNd, hxNotWlIn,
                      hRootIn, hWlInMem, hPersIn, ?_, hInOrig, hOrigPersIn, ?_⟩
                    · intro y hy hyNe hyPos
                      have hrcY := hRcIn y hy hyNe hyPos
                      have hneY : y.addr ≠ c := by
                        intro heq
                        have hEq := nodup_addr_eq_of_mem hndIn hy (List.getElem_mem hidx_c)
                          (heq.trans hocAddr.symm)
                        rw [hEq, hCrc0] at hyPos; exact absurd hyPos (by decide)
                      rw [hDropCons, List.count_cons] at hrcY
                      have : (c == y.addr) = false := beq_eq_false_iff_ne.mpr (Ne.symm hneY)
                      simp [this] at hrcY; exact hrcY
                    · intro orig horig hpos
                      have hEq := hOrigEqIn orig horig hpos
                      refine ⟨fun o' ho' had hneX => ?_, hEq.2⟩
                      have h1 := hEq.1 o' ho' had hneX
                      have hneY : orig.addr ≠ c := by
                        intro heq
                        have hEqO := nodup_addr_eq_of_mem hndIn ho' (List.getElem_mem hidx_c)
                          (had.trans (heq.trans hocAddr.symm))
                        obtain ⟨orig', horig', hsame', hrc'⟩ := hInOrig o' ho'
                        have horigEq := nodup_addr_eq_of_mem hndO horig' horig
                          (by rw [← hsame'.1, had])
                        subst horigEq
                        rw [hEqO, hCrc0] at hrc'
                        rcases hrc' with ⟨h0, _⟩ | ⟨_, h0, _⟩
                        · rw [h0] at hpos; exact absurd hpos (by decide)
                        · exact absurd h0 (by decide)
                      rw [hTakeSucc, List.count_append, List.count_singleton]
                      have : (c == orig.addr) = false := beq_eq_false_iff_ne.mpr (Ne.symm hneY)
                      simp [this, h1]
              · intro hcOddEq
                have hcOdd : (c &&& 1#64) ≠ 0#64 := of_decide_eq_false hcOddEq
                apply hJ5 (lenBV', ()) mIn
                refine ⟨stIn, inObjs, len', hMetaIn, hRemIn, hLenInLe, hLenInBV, hInLen,
                  hInLeO, hInX, hInWf, hInCl, hNoRefsIn, hFreedEq, hmIn, hWlInNd, hxNotWlIn,
                  hRootIn, hWlInMem, hPersIn, ?_, hInOrig, hOrigPersIn, ?_⟩
                · intro y hy hyNe hyPos
                  have hrcY := hRcIn y hy hyNe hyPos
                  have hneY : y.addr ≠ c := fun h => hcOdd (h ▸ objWf_addr_even (hInWf y hy))
                  rw [hDropCons, List.count_cons] at hrcY
                  have : (c == y.addr) = false := beq_eq_false_iff_ne.mpr (Ne.symm hneY)
                  simp [this] at hrcY; exact hrcY
                · intro orig horig hpos
                  have hEq := hOrigEqIn orig horig hpos
                  refine ⟨fun o' ho' had hneX => ?_, hEq.2⟩
                  have h1 := hEq.1 o' ho' had hneX
                  have hneY : orig.addr ≠ c := fun h =>
                    hcOdd (h ▸ objWf_addr_even (hObjsWf orig horig))
                  rw [hTakeSucc, List.count_append, List.count_singleton]
                  have : (c == orig.addr) = false := beq_eq_false_iff_ne.mpr (Ne.symm hneY)
                  simp [this, h1]
          · intro hiNotUlt
            have hiEq : i = x.childFields.length := by
              rw [hiBV, BitVec.ult, hi64, hn64] at hiNotUlt
              have : ¬ i < x.childFields.length := of_decide_eq_false hiNotUlt
              omega
            subst hiEq
            -- Free `x` via `lcnf_free_obj`!
            let nextObjs : List LcnfObj := inObjs.eraseIdx idx_x
            have hFreePre : (rtC0Inv rt stIn ⋆ freeObjLayout xAddr x.totalBytes x.header ⋆
                (lcnfHeap nextObjs ⋆ R)) mIn := by
              have h1 := hmIn
              rw [lcnfHeap_focus inObjs hidx_x_in, hInX', ← lcnfHeap_eraseIdx inObjs] at h1
              have h2 : (rtC0Inv rt stIn ⋆ (lcnfObjMem x ⋆ (lcnfHeap nextObjs ⋆ R))) mIn :=
                sep_cast h1 (by ac_rfl)
              have h3 : (rtC0Inv rt stIn ⋆ (freeObjLayout x.addr x.totalBytes x.header ⋆
                  (lcnfHeap nextObjs ⋆ R))) mIn :=
                sep_mono_r (fun _ hz =>
                  sep_mono (fun _ hx => lcnfObjMem_to_freeObjLayout hxWf hx) hz) h2
              rw [hxAddrEq] at h3
              exact sep_cast h3 (by ac_rfl)
            refine wp_call_of_spec _ _ ?_
            apply hFree
            have hxEven : (xAddr &&& 1#64 ≠ 0#64) = False := by
              apply propext; constructor
              · intro hne; exact hne (hxAddrEq ▸ objWf_addr_even hxWf)
              · exact False.elim
            dsimp [lcnfFreeObjSpec, Arg.val]
            change (if (xAddr &&& 1#64) ≠ 0#64 then _ else _)
            simp only [hxEven, ↓reduceIte]
            refine ⟨stIn, x.header, x.totalBytes, lcnfHeap nextObjs ⋆ R,
              (by change xAddr ≠ 0#64; rw [← hxAddrEq]; exact hxWf.1),
              (by change xAddr.toNat % 8 = 0; rw [← hxAddrEq]; exact hxWf.2.1),
              hxWf.2.2.2.2.2.2.1, hxWf.2.2.2.2.2.2.2.1, hxWf.2.2.2.2.2.2.2.2.1, hFreePre, ?_⟩
            intro stOut mOut hMetaOut hRemOut hWbOut hmOut
            have hmOut' : (rtC0Inv rt stOut ⋆ lcnfHeap nextObjs ⋆ R) mOut :=
              sep_cast hmOut (by ac_rfl)
            have hNextLen : nextObjs.length = curObjs.length - 1 := by
              simp [nextObjs, List.length_eraseIdx_of_lt hidx_x_in, hInLen]
            have hMemNext : ∀ o' ∈ nextObjs, o' ∈ inObjs ∧ o'.addr ≠ xAddr := by
              intro o' ho'
              have h1 := List.mem_of_mem_eraseIdx ho'
              have h2 : o'.addr ∈ nextObjs.map LcnfObj.addr := List.mem_map_of_mem ho'
              have h3 := (map_addr_eraseIdx_mem hndIn hidx_x_in o'.addr).mp h2
              rw [hInX', hxAddrEq] at h3
              exact ⟨h1, h3.2⟩
            have hInNext : ∀ o' ∈ inObjs, o'.addr ≠ xAddr → o' ∈ nextObjs := by
              intro o' ho' hne
              have h1 : o'.addr ∈ nextObjs.map LcnfObj.addr :=
                (map_addr_eraseIdx_mem hndIn hidx_x_in o'.addr).mpr
                  ⟨List.mem_map_of_mem ho', by rw [hInX', hxAddrEq]; exact hne⟩
              rw [List.mem_map] at h1
              obtain ⟨o'', ho'', heq⟩ := h1
              have hEq := nodup_addr_eq_of_mem hndIn (List.mem_of_mem_eraseIdx ho'') ho' heq
              rwa [← hEq]
            have hNextCl : lcnfHeapClosed nextObjs := by
              intro p hp f hf hf0
              obtain ⟨hpIn, _⟩ := hMemNext p hp
              obtain ⟨q, hqIn, hqAddr⟩ := hInCl p hpIn f hf hf0
              have hqNe : q.addr ≠ xAddr := fun h =>
                hNoRefsIn p hpIn (by rw [← h, hqAddr]; exact hf)
              exact ⟨q, hInNext q hqIn hqNe, hqAddr⟩
            have hNextFreeEq : ∀ y,
                nonPersistRefs (freedObjs objs nextObjs) y =
                  nonPersistRefs (freedObjs objs inObjs) y + x.childFields.count y := by
              intro y
              have horigX : ∃ ox ∈ objs, ox.addr = inObjs[idx_x].addr ∧ ox.rc ≠ 0#32 ∧
                  ox.childFields = inObjs[idx_x].childFields := by
                refine ⟨origX, horigXMem, by rw [hInX', horigXSame.1],
                  fun h0 => by rw [h0] at horigXPos; exact absurd horigXPos (by decide),
                  by rw [hInX', horigXSame.childFields_eq]⟩
              have hstep := nonPersistRefs_freedObjs_eraseIdx hndO hndIn hidx_x_in horigX y
              simpa [nextObjs, hInX'] using hstep
            refine hIH0 nextObjs.length (lenBV', ()) mOut (by omega)
              ⟨stOut, nextObjs, len', preservesMeta_trans hMetaIn hMetaOut,
                hRemOut.trans hRemIn, hLenInLe, hLenInBV, rfl, by omega,
                fun o' ho' => hInWf o' (hMemNext o' ho').1, hNextCl, hmOut',
                by rw [hWbOut]; exact hWlInNd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hWbOut]
              rcases hRootIn with hIn | rfl | hOut
              · exact Or.inl hIn
              · exact Or.inr fun o' ho' => (hMemNext o' ho').2
              · exact Or.inr fun o' ho' => hOut o' (hMemNext o' ho').1
            · rw [hWbOut]
              intro a ha
              obtain ⟨obj, hobjIn, hobjAddr, hobjRc, hobjReach⟩ := hWlInMem a ha
              have hne : obj.addr ≠ xAddr := fun h => hxNotWlIn (h ▸ hobjAddr ▸ ha)
              exact ⟨obj, hInNext obj hobjIn hne, hobjAddr, hobjRc, hobjReach⟩
            · intro p hp hp0 f hf hf0
              obtain ⟨hpIn, _⟩ := hMemNext p hp
              obtain ⟨q, hqIn, hqAddr, hq0⟩ := hPersIn p hpIn hp0 f hf hf0
              have hne : q.addr ≠ xAddr := fun h => hNoRefsIn p hpIn (by rw [← h, hqAddr]; exact hf)
              exact ⟨q, hInNext q hqIn hne, hqAddr, hq0⟩
            · rw [hWbOut]
              intro y hy hyPos
              obtain ⟨hyIn, hyNe⟩ := hMemNext y hy
              have hrcY := hRcIn y hyIn hyNe hyPos
              simp only [List.drop_length, List.count_nil, Nat.add_zero] at hrcY
              exact hrcY
            · intro o' ho'
              exact hInOrig o' (hMemNext o' ho').1
            · intro orig horig h0
              obtain ⟨o', ho'In, hoad, ho0⟩ := hOrigPersIn orig horig h0
              have hne : o'.addr ≠ xAddr := by
                intro h
                have hEq := nodup_addr_eq_of_mem hndIn ho'In (List.getElem_mem hidx_x_in)
                  (by rw [h, hInX', hxAddrEq])
                rw [hEq, hInX'] at ho0
                exact absurd (ho0.symm.trans hxRc1) (by decide)
              exact ⟨o', hInNext o' ho'In hne, hoad, ho0⟩
            · rw [hWbOut]
              intro orig horig hpos
              have hEq := hOrigEqIn orig horig hpos
              rw [hNextFreeEq]
              refine ⟨fun o' ho' had => ?_, fun hfreeNew => ?_⟩
              · obtain ⟨ho'In, ho'Ne⟩ := hMemNext o' ho'
                have h1 := hEq.1 o' ho'In had ho'Ne
                rw [List.take_of_length_le (Nat.le_refl _)] at h1
                omega
              · simp only [freedObjs, List.mem_filter, Bool.not_eq_true'] at hfreeNew
                have hNotNext : orig.addr ∉ nextObjs.map LcnfObj.addr := by
                  intro hmem
                  have hc : (nextObjs.map LcnfObj.addr).contains orig.addr = true :=
                    List.contains_iff_mem.mpr hmem
                  rw [hc] at hfreeNew; exact absurd hfreeNew.2 (by decide)
                by_cases hadX : orig.addr = xAddr
                · have hEqO :=
                    nodup_addr_eq_of_mem hndO horig horigXMem (hadX.trans horigXAddr.symm)
                  subst hEqO
                  have hxCnt0 : x.childFields.count orig.addr = 0 := by
                    rw [horigXAddr, List.count_eq_zero]
                    have hnr := hNoRefsIn inObjs[idx_x] (List.getElem_mem hidx_x_in)
                    rwa [hInX'] at hnr
                  rw [hxCnt0, hFreedEq, Nat.add_zero]
                  exact ⟨horigXDrop, horigXAddr ▸ hxReach⟩
                · have hNotIn : orig.addr ∉ inObjs.map LcnfObj.addr := by
                    intro hmem
                    exact hNotNext ((map_addr_eraseIdx_mem hndIn hidx_x_in orig.addr).mpr
                      ⟨hmem, by rw [hInX', hxAddrEq]; exact hadX⟩)
                  have hfreeOld : orig ∈ freedObjs objs inObjs := by
                    simp only [freedObjs, List.mem_filter, Bool.not_eq_true']
                    refine ⟨horig, ?_⟩
                    cases hct : (inObjs.map LcnfObj.addr).contains orig.addr
                    · rfl
                    · exact absurd (List.contains_iff_mem.mp hct) hNotIn
                  have h2 := hEq.2 hfreeOld
                  have hxCnt0 : x.childFields.count orig.addr = 0 := by
                    rw [List.count_eq_zero]
                    intro hmemC
                    have hEvenO : (orig.addr &&& 1#64) = 0#64 :=
                      objWf_addr_even (hObjsWf orig horig)
                    obtain ⟨q, hqIn, hqAddr⟩ := hInCl inObjs[idx_x] (List.getElem_mem hidx_x_in)
                      orig.addr (by rw [hInX']; exact hmemC) hEvenO
                    exact hNotIn (hqAddr ▸ List.mem_map_of_mem hqIn)
                  rw [hxCnt0, Nat.add_zero]
                  exact h2
        · intro J1 hJ1
          rw [htagShift]
          refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
          dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
          constructor
          · intro htCloEq
            have htClo : x.tag = closureTag := by
              have h := congrArg BitVec.toNat (of_decide_eq_true htCloEq)
              simpa [closureTag, Nat.mod_eq_of_lt (by omega : x.tag < 2 ^ 64)] using h
            dfs_pure_steps
            have hldM : loadVal mCur i64 (xAddr + 16#64) = some x.cloMeta := by
              rw [← hxAddrEq]
              exact lcnfHeap_load_cloMeta hidx_x htClo (sep_pull_heap hmCur)
            refine wp_load_of hldM ?_
            dfs_pure_steps
            have hsp := hxWf.2.2.2.2.2.2.2.2.2
            simp only [htClo, ↓reduceIte] at hsp
            rw [LcnfObj.cloMeta, cloMetaWord_nfix x.arity x.fields.length hsp.1 hsp.2.1]
            exact hJ1 _ mCur ⟨by simp [LcnfObj.childFields, htClo],
              by simp [LcnfObj.fieldsOff, htClo], rfl⟩
          · intro htCloNe
            have htNotClo : x.tag ≠ closureTag := fun h =>
              of_decide_eq_false htCloNe (by rw [h]; rfl)
            refine wp_join_group DispPost
              (fun _ xs mD h => by rcases xs with ⟨a, b, ⟨⟩⟩; exact hJ1 (a, b, ()) mD h) ?_
            intro J2 hJ2
            refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
            dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
            constructor
            · intro htArrEq
              have htArr : x.tag = arrayTag := by
                have h := congrArg BitVec.toNat (of_decide_eq_true htArrEq)
                simpa [arrayTag, Nat.mod_eq_of_lt (by omega : x.tag < 2 ^ 64)] using h
              dfs_pure_steps
              have hldA : loadVal mCur i64 (xAddr + 8#64) =
                  some (BitVec.ofNat 64 x.fields.length) := by
                rw [← hxAddrEq]
                exact lcnfHeap_load_arrSize hidx_x htArr (sep_pull_heap hmCur)
              refine wp_load_of hldA ?_
              exact hJ2 _ mCur ⟨by simp [LcnfObj.childFields, htArr],
                by simp [LcnfObj.fieldsOff, htArr], rfl⟩
            · intro htArrNe
              have htNotArr : x.tag ≠ arrayTag := fun h =>
                of_decide_eq_false htArrNe (by rw [h]; rfl)
              refine wp_join_group DispPost
                (fun _ xs mD h => by rcases xs with ⟨a, b, ⟨⟩⟩; exact hJ2 (a, b, ()) mD h) ?_
              intro J3 hJ3
              refine wp_let_cmp _ _ rfl _ _ _ rfl ?_
              dsimp [liftCmp, CmpOp.evalBool, CmpOp.evalBits]
              constructor
              · intro htCtorEq
                have htLe : x.tag ≤ 244 := by
                  have h244 : (244#64).toNat = 244 := by decide
                  have htag64 : (BitVec.ofNat 64 x.tag).toNat = x.tag :=
                    Nat.mod_eq_of_lt (by omega)
                  simp only [BitVec.ule, htag64, h244] at htCtorEq
                  exact of_decide_eq_true htCtorEq
                dfs_pure_steps
                rw [LcnfObj.header_other x hxCs hxOth hxTag]
                have hsp := hxWf.2.2.2.2.2.2.2.2.2
                have hsa : x.tag ≠ sarrayTag := by unfold sarrayTag; omega
                have hstr : x.tag ≠ stringTag := by unfold stringTag; omega
                have hmpz : x.tag ≠ mpzTag := by unfold mpzTag; omega
                simp only [htNotClo, htNotArr, hsa, hstr, hmpz, ↓reduceIte] at hsp
                exact hJ3 _ mCur ⟨by simp [LcnfObj.childFields, htLe, hsp.2.1],
                  by simp [LcnfObj.fieldsOff, htNotClo, htNotArr], rfl⟩
              · intro htOtherEq
                have htGt : ¬ x.tag ≤ 244 := by
                  have h244 : (244#64).toNat = 244 := by decide
                  have htag64 : (BitVec.ofNat 64 x.tag).toNat = x.tag :=
                    Nat.mod_eq_of_lt (by omega)
                  simp only [BitVec.ule, htag64, h244] at htOtherEq
                  exact of_decide_eq_false htOtherEq
                exact hJ3 _ mCur ⟨by simp [LcnfObj.childFields, htGt, htNotClo, htNotArr],
                  by simp [LcnfObj.fieldsOff, htNotClo, htNotArr], rfl⟩
      · intro hLenZeroEq
        have hLenZero : len = 0 := by
          rw [hLenBV, BitVec.ult, hLen64] at hLenZeroEq
          have h0m : (0#64).toNat = 0 := by decide
          rw [h0m] at hLenZeroEq
          have : ¬ 0 < len := of_decide_eq_false hLenZeroEq
          omega
        subst hLenZero
        have hRootGone : ∀ o' ∈ curObjs, o'.addr ≠ o := by
          rcases hRootState with hIn | hOut
          · simp at hIn
          · exact hOut
        refine hPost stCur curObjs mCur hMeta hRem ?_ hmCur
        refine ⟨⟨obj0, hobj0Mem, hobj0Addr, hobj0Rc⟩, hObjsWf, hObjsCl, hCurCl, ?_, hPersCl, ?_,
          hOrigPers, ?_⟩
        · intro o' ho'
          obtain ⟨orig, horig, hsame, hrc⟩ := hCurOrig o' ho'
          exact ⟨hCurWf o' ho', hRootGone o' ho', orig, horig, hsame.1.symm, hsame.2.1, hsame.2.2.1,
            hsame.2.2.2.1, hsame.2.2.2.2.1, hsame.2.2.2.2.2.1, hsame.2.2.2.2.2.2.1,
            hsame.2.2.2.2.2.2.2.1, hsame.2.2.2.2.2.2.2.2.1, hsame.2.2.2.2.2.2.2.2.2.1,
            hsame.2.2.2.2.2.2.2.2.2.2.1, hsame.2.2.2.2.2.2.2.2.2.2.2, hrc⟩
        · intro y hy hyPos
          have hrcY := hRcCur y hy hyPos
          simpa using hrcY
        · intro orig horig hpos
          have hEq := hOrigEq orig horig hpos
          simpa using hEq

/-! ## Closed R0 Verified Runtime Table (`rtR0Mod_ok`) -/

theorem rtC0Env_dec_ref_cold_wp : ∀ xs m Q X,
    lcnfDecRefColdSpec xs m Q X → Func.wp rtC0Env lcnf_dec_ref_cold.body xs m Q X :=
  lcnf_dec_ref_cold_wp rtC0Env rtC0Env_free_obj

theorem rtC0Env_mark_persistent_wp : ∀ xs m Q X,
    lcnfMarkPersistentSpec xs m Q X → Func.wp rtC0Env lcnf_mark_persistent.body xs m Q X :=
  lcnf_mark_persistent_wp rtC0Env

theorem rtR0Mod_ok : ModuleOk rtC0Env rtR0Mod := by
  refine Env.ofTable_moduleOk rtR0Mod_checkAcyclic ?_ ?_
  · refine ⟨lcnf_alloc_wf, lcnf_free_obj_wf, lcnf_dec_ref_cold_wf,
      lcnf_mark_persistent_wf, lcnf_clo_under_wf, trivial⟩
  · refine ⟨⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h => lcnf_alloc_wp rtC0Env xs m Q X h⟩,
      ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h => lcnf_free_obj_wp rtC0Env xs m Q X h⟩,
      ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h =>
        lcnf_dec_ref_cold_wp rtC0Env rtC0Env_free_obj xs m Q X h⟩,
      ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h => lcnf_mark_persistent_wp rtC0Env xs m Q X h⟩,
      ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h =>
        lcnf_clo_under_wp rtC0Env rtC0Env_alloc rtC0Env_free_obj xs m Q X h⟩,
      trivial⟩

/-! ## Concrete `Mem 64` Non-Vacuity (`XPost := False`, Multi-Node Ctor/Closure DAG) -/

def nvRtBase : BitVec 64 := 0x10000#64
def nvWorkCap : Nat := 8
def nvRem : Nat := 64

def nvRtState : RtC0State :=
  initRtC0State nvRtBase nvWorkCap nvRem (by decide) (by decide)

def nvDagBase : BitVec 64 := nvRtBase + 33800#64
def nvAddrA : BitVec 64 := nvDagBase
def nvAddrB : BitVec 64 := nvDagBase + 24#64
def nvAddrC : BitVec 64 := nvDagBase + 56#64
def nvAddrP : BitVec 64 := nvDagBase + 80#64
def nvAddrU : BitVec 64 := nvDagBase + 96#64

/-- Root ctor `A` (`rc=1`) referencing exclusive closure `B` and shared ctor `C`. -/
def nvObjA : LcnfObj :=
  { addr := nvAddrA, rc := 1#32, csSz := 24, other := 2, tag := 0,
    fields := [nvAddrB, nvAddrC] }

/-- Exclusive closure `B` (`rc=1`, `arity=2`) capturing shared ctor `C`. -/
def nvObjB : LcnfObj :=
  { addr := nvAddrB, rc := 1#32, csSz := 32, other := 0, tag := closureTag,
    funId := 0x400#64, arity := 2, fields := [nvAddrC] }

/-- Shared ctor `C` (`rc=3`) referencing scalar `7#64` and persistent leaf `P`. -/
def nvObjC : LcnfObj :=
  { addr := nvAddrC, rc := 3#32, csSz := 24, other := 2, tag := 1,
    fields := [7#64, nvAddrP] }

/-- Persistent leaf ctor `P` (`rc=0`) holding scalar `11#64`. -/
def nvObjP : LcnfObj :=
  { addr := nvAddrP, rc := 0#32, csSz := 16, other := 1, tag := 2,
    fields := [11#64] }

/-- Unreachable ctor `U` (`rc=2`) holding scalar `13#64`. -/
def nvObjU : LcnfObj :=
  { addr := nvAddrU, rc := 2#32, csSz := 16, other := 1, tag := 3,
    fields := [13#64] }

def nvDagObjs : List LcnfObj := [nvObjA, nvObjB, nvObjC, nvObjP, nvObjU]

def nvHdrWords (h : LcnfC0Rt) : List (BitVec 64) :=
  [ h.s_large_free, h.s_ba_empty, h.s_cur, h.s_end, h.s_work, h.s_work_cap,
    h.s_chunks, h.s_nchunks, h.s_chunks_cap, h.s_st_allocs, h.s_st_frees,
    h.s_st_live, h.s_st_peak_live, h.s_st_persistent, h.s_st_reused,
    h.s_st_cold_decs, h.s_st_bytes ]

def nvRtBytes : List UInt8 :=
  bytes64 nvRtState.extraArgs ++ bytes64 nvRtState.globals ++
  bytes64 nvRtState.freeList ++ bytes64 (nvHdrWords nvRtState.hdr) ++
  bytes64 nvRtState.workBuf ++ List.replicate nvRem 0

def nvObjABytes : List UInt8 := bytes64 [nvObjA.header, nvAddrB, nvAddrC]
def nvObjBBytes : List UInt8 := bytes64 [nvObjB.header, nvObjB.funId, nvObjB.cloMeta, nvAddrC]
def nvObjCBytes : List UInt8 := bytes64 [nvObjC.header, 7#64, nvAddrP]
def nvObjPBytes : List UInt8 := bytes64 [nvObjP.header, 11#64]
def nvObjUBytes : List UInt8 := bytes64 [nvObjU.header, 13#64]

def nvDagBytes : List UInt8 :=
  nvObjABytes ++ nvObjBBytes ++ nvObjCBytes ++ nvObjPBytes ++ nvObjUBytes

/-- Concrete `Mem 64` image packing the `LcnfC0Rt` slab (`33800B`) + 5-node DAG (`112B`). -/
def nvDagMem : Mem 64 := (nvRtBytes ++ nvDagBytes).At nvRtBase

private theorem nv_sep_append {P Q : Mem 64 → Prop} {a : BitVec 64}
    {bs1 bs2 : List UInt8} {n1 n2 : Nat}
    (h1 : bs1.length = n1) (h2 : bs2.length = n2) (hfit : n1 + n2 ≤ 2 ^ 64)
    (hp : P (bs1.At a)) (hq : Q (bs2.At (a + BitVec.ofNat 64 n1))) :
    (P ⋆ Q) ((bs1 ++ bs2).At a) := by
  have hs := congrFun (Mem.At_append_sep bs1 bs2 a (by omega)) ((bs1 ++ bs2).At a)
  obtain ⟨m1, m2, hu, hd, rfl, rfl⟩ := hs.mp rfl
  refine ⟨bs1.At a, bs2.At (a + BitVec.ofNat 64 bs1.length), hu, hd, hp, ?_⟩
  rwa [h1]

private theorem array64_hdrWords_to_At (rt : BitVec 64) (h : LcnfC0Rt) {m : Mem 64}
    (hm : array64 (rt + 33536#64) (nvHdrWords h) m) : LcnfC0Rt.At rt h m := by
  unfold nvHdrWords at hm
  simp only [array64, cell64_eq_cell, sep_emp, BitVec.add_assoc] at hm
  unfold LcnfC0Rt.At
  exact sep_cast hm (by ac_rfl)

private theorem nvRtBytes_ok :
    nvRtBytes.length = 33800 ∧ rtC0Inv nvRtBase nvRtState (nvRtBytes.At nvRtBase) := by
  let b0 := bytes64 nvRtState.extraArgs
  let b1 := bytes64 nvRtState.globals
  let b2 := bytes64 nvRtState.freeList
  let b3 := bytes64 (nvHdrWords nvRtState.hdr)
  let b4 := bytes64 nvRtState.workBuf
  let b5 := List.replicate nvRem (0 : UInt8)
  have hl0 : b0.length = 256 := by
    simp [b0, bytes64_length, nvRtState.extraLen, rtExtraSlots]
  have hl1 : b1.length = 32768 := by
    simp [b1, bytes64_length, nvRtState.globalsLen, rtGlobalSlots]
  have hl2 : b2.length = 512 := by
    simp [b2, bytes64_length, nvRtState.freeListLen, rtNumClasses]
  have hl3 : b3.length = 136 := by
    simp [b3, bytes64_length, nvHdrWords]
  have hl4 : b4.length = 64 := by
    have hwl : nvRtState.workBuf.length = 8 := by
      simp [nvRtState, initRtC0State, nvWorkCap]
    simp [b4, bytes64_length, hwl]
  have hl5 : b5.length = 64 := by simp [b5, nvRem]
  have htot : nvRtBytes.length = 33800 := by
    change (((((b0 ++ b1) ++ b2) ++ b3) ++ b4) ++ b5).length = 33800
    simp only [List.length_append, hl0, hl1, hl2, hl3, hl4, hl5]
  refine ⟨htot, ?_⟩
  have h0 : array64 nvRtBase nvRtState.extraArgs (b0.At nvRtBase) :=
    array64_bytes nvRtBase nvRtState.extraArgs (by rw [nvRtState.extraLen]; decide)
  have h1 : array64 (nvRtBase + BitVec.ofNat 64 rtGlobalsOff) nvRtState.globals
      (b1.At (nvRtBase + BitVec.ofNat 64 256)) :=
    array64_bytes (nvRtBase + BitVec.ofNat 64 rtGlobalsOff) nvRtState.globals
      (by rw [nvRtState.globalsLen]; decide)
  have h2 : array64 (nvRtBase + 33024#64) nvRtState.freeList
      (b2.At (nvRtBase + BitVec.ofNat 64 33024)) :=
    array64_bytes (nvRtBase + 33024#64) nvRtState.freeList
      (by rw [nvRtState.freeListLen]; decide)
  have h3 : LcnfC0Rt.At nvRtBase nvRtState.hdr (b3.At (nvRtBase + BitVec.ofNat 64 33536)) :=
    array64_hdrWords_to_At nvRtBase nvRtState.hdr
      (array64_bytes (nvRtBase + 33536#64) (nvHdrWords nvRtState.hdr) (by decide))
  have h4 : array64 nvRtState.hdr.s_work nvRtState.workBuf
      (b4.At (nvRtBase + BitVec.ofNat 64 33672)) := by
    have hs : nvRtState.hdr.s_work = nvRtBase + BitVec.ofNat 64 33672 := rfl
    rw [hs]
    exact array64_bytes _ nvRtState.workBuf (by
      have hwl : nvRtState.workBuf.length = 8 := by simp [nvRtState, initRtC0State, nvWorkCap]
      rw [hwl]; decide)
  have h5 : region nvRtState.hdr.s_cur nvRem (b5.At (nvRtBase + BitVec.ofNat 64 33736)) := by
    have hc : nvRtState.hdr.s_cur = nvRtBase + BitVec.ofNat 64 33736 := by
      simp [nvRtState, initRtC0State, nvWorkCap]
    rw [hc]
    exact ⟨b5, hl5, rfl⟩
  have h01 := nv_sep_append hl0 hl1 (by decide) h0 h1
  have h012 := nv_sep_append (by simp [hl0, hl1] : (b0 ++ b1).length = 33024) hl2 (by decide) h01 h2
  have h0123 := nv_sep_append (by simp [hl0, hl1, hl2] : ((b0 ++ b1) ++ b2).length = 33536) hl3
    (by decide) h012 h3
  have h01234 := nv_sep_append
    (by simp [hl0, hl1, hl2, hl3] : (((b0 ++ b1) ++ b2) ++ b3).length = 33672)
    hl4 (by decide) h0123 h4
  have h012345 := nv_sep_append
    (by simp [hl0, hl1, hl2, hl3, hl4] : ((((b0 ++ b1) ++ b2) ++ b3) ++ b4).length = 33736)
    hl5 (by decide) h01234 h5
  exact rtC0Inv_init_satisfiable nvRtBase nvWorkCap nvRem (by decide) (by decide) h012345

private theorem array64_ctor_to_objMem {o : LcnfObj}
    (ht : o.tag ≠ closureTag ∧ o.tag ≠ arrayTag ∧ o.tag ≠ sarrayTag ∧
      o.tag ≠ stringTag ∧ o.tag ≠ mpzTag)
    (hdat : o.scalarData = []) (hcs : o.csSz = 8 + 8 * o.fields.length)
    {m : Mem 64} (hm : array64 o.addr (o.header :: o.fields) m) : lcnfObjMem o m := by
  have hbnil : ∀ a : BitVec 64, bytes a [] = emp := fun a => (eq_nil_At a).symm
  unfold lcnfObjMem
  simp only [ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2, ↓reduceIte, hdat,
    List.length_nil, Nat.add_zero, hcs, Nat.sub_self, hbnil, region_zero, sep_emp]
  exact hm

private theorem array64_clo_to_objMem {o : LcnfObj}
    (ht : o.tag = closureTag) (hcs : o.csSz = 24 + 8 * o.fields.length)
    {m : Mem 64} (hm : array64 o.addr (o.header :: o.funId :: o.cloMeta :: o.fields) m) :
    lcnfObjMem o m := by
  unfold lcnfObjMem
  simp only [ht, ↓reduceIte, hcs, Nat.sub_self, region_zero, sep_emp]
  simp only [array64, BitVec.add_assoc] at hm
  exact sep_cast hm (by ac_rfl)

private theorem nvDagBytes_ok :
    nvDagBytes.length = 112 ∧ lcnfHeap nvDagObjs (nvDagBytes.At nvDagBase) := by
  have hlA : nvObjABytes.length = 24 := by simp [nvObjABytes, bytes64_length]
  have hlB : nvObjBBytes.length = 32 := by simp [nvObjBBytes, bytes64_length]
  have hlC : nvObjCBytes.length = 24 := by simp [nvObjCBytes, bytes64_length]
  have hlP : nvObjPBytes.length = 16 := by simp [nvObjPBytes, bytes64_length]
  have hlU : nvObjUBytes.length = 16 := by simp [nvObjUBytes, bytes64_length]
  have htot : nvDagBytes.length = 112 := by
    simp [nvDagBytes, hlA, hlB, hlC, hlP, hlU]
  refine ⟨htot, ?_⟩
  have hA : lcnfObjMem nvObjA (nvObjABytes.At nvDagBase) :=
    array64_ctor_to_objMem (by decide) rfl rfl
      (array64_bytes nvAddrA [nvObjA.header, nvAddrB, nvAddrC] (by decide))
  have hB : lcnfObjMem nvObjB (nvObjBBytes.At (nvDagBase + BitVec.ofNat 64 24)) :=
    array64_clo_to_objMem rfl rfl
      (array64_bytes nvAddrB [nvObjB.header, nvObjB.funId, nvObjB.cloMeta, nvAddrC] (by decide))
  have hC : lcnfObjMem nvObjC (nvObjCBytes.At (nvDagBase + BitVec.ofNat 64 56)) :=
    array64_ctor_to_objMem (by decide) rfl rfl
      (array64_bytes nvAddrC [nvObjC.header, 7#64, nvAddrP] (by decide))
  have hP : lcnfObjMem nvObjP (nvObjPBytes.At (nvDagBase + BitVec.ofNat 64 80)) :=
    array64_ctor_to_objMem (by decide) rfl rfl
      (array64_bytes nvAddrP [nvObjP.header, 11#64] (by decide))
  have hU : lcnfObjMem nvObjU (nvObjUBytes.At (nvDagBase + BitVec.ofNat 64 96)) :=
    array64_ctor_to_objMem (by decide) rfl rfl
      (array64_bytes nvAddrU [nvObjU.header, 13#64] (by decide))
  have hAB := nv_sep_append hlA hlB (by decide) hA hB
  have hABC := nv_sep_append (by simp [hlA, hlB] : (nvObjABytes ++ nvObjBBytes).length = 56)
    hlC (by decide) hAB hC
  have hABCP := nv_sep_append
    (by simp [hlA, hlB, hlC] : ((nvObjABytes ++ nvObjBBytes) ++ nvObjCBytes).length = 80)
    hlP (by decide) hABC hP
  have hABCPU := nv_sep_append
    (by simp [hlA, hlB, hlC, hlP] :
      (((nvObjABytes ++ nvObjBBytes) ++ nvObjCBytes) ++ nvObjPBytes).length = 96)
    hlU (by decide) hABCP hU
  simp only [nvDagObjs, lcnfHeap, sep_emp]
  exact sep_cast hABCPU (by ac_rfl)

theorem nvDagMem_ok : (rtC0Inv nvRtBase nvRtState ⋆ lcnfHeap nvDagObjs) nvDagMem := by
  have ⟨hlRt, hRt⟩ := nvRtBytes_ok
  have ⟨hlDag, hDag⟩ := nvDagBytes_ok
  exact nv_sep_append hlRt hlDag (by decide) hRt hDag

private theorem nvDagObjs_wf : ∀ o ∈ nvDagObjs, o.Wf := by
  intro o ho
  simp only [nvDagObjs, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl <;>
    (unfold LcnfObj.Wf LcnfObj.totalBytes; decide)

private theorem nvObjA_ch : nvObjA.childFields = [nvAddrB, nvAddrC] := rfl
private theorem nvObjB_ch : nvObjB.childFields = [nvAddrC] := rfl
private theorem nvObjC_ch : nvObjC.childFields = [7#64, nvAddrP] := rfl
private theorem nvObjP_ch : nvObjP.childFields = [11#64] := rfl
private theorem nvObjU_ch : nvObjU.childFields = [13#64] := rfl

private theorem nvDagObjs_closed : lcnfHeapClosed nvDagObjs := by
  intro o ho f hf hf0
  simp only [nvDagObjs, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl
  · rw [nvObjA_ch] at hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact ⟨nvObjB, by simp [nvDagObjs], rfl⟩
    · exact ⟨nvObjC, by simp [nvDagObjs], rfl⟩
  · rw [nvObjB_ch] at hf; simp only [List.mem_singleton] at hf; subst hf
    exact ⟨nvObjC, by simp [nvDagObjs], rfl⟩
  · rw [nvObjC_ch] at hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact absurd hf0 (by decide)
    · exact ⟨nvObjP, by simp [nvDagObjs], rfl⟩
  · rw [nvObjP_ch] at hf; simp only [List.mem_singleton] at hf; subst hf
    exact absurd hf0 (by decide)
  · rw [nvObjU_ch] at hf; simp only [List.mem_singleton] at hf; subst hf
    exact absurd hf0 (by decide)

private theorem nvDagObjs_rcSound : RcSound nvAddrA nvDagObjs := by
  constructor
  · intro p hp hp0 f hf hf0
    simp only [nvDagObjs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact absurd hp0 (by decide)
    · exact absurd hp0 (by decide)
    · exact absurd hp0 (by decide)
    · rw [nvObjP_ch] at hf; simp only [List.mem_singleton] at hf; subst hf
      exact absurd hf0 (by decide)
    · exact absurd hp0 (by decide)
  · intro y hy hyPos
    simp only [nvDagObjs, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · exact absurd hyPos (by decide)
    · decide

private theorem nvDag_not_reach_U : ¬ NonPersistReach nvDagObjs nvAddrA nvAddrU := by
  intro hr
  have hNoU : ∀ a, NonPersistReach nvDagObjs nvAddrA a → a ≠ nvAddrU := by
    intro a h
    induction h with
    | refl _ => decide
    | @step u v _ hch hv0 _ ih =>
      obtain ⟨ou, hou, houa, hv⟩ := hch
      simp only [nvDagObjs, List.mem_cons, List.not_mem_nil, or_false] at hou
      rcases hou with rfl | rfl | rfl | rfl | rfl
      · rw [nvObjA_ch] at hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl <;> decide
      · rw [nvObjB_ch] at hv; simp only [List.mem_singleton] at hv; subst hv; decide
      · rw [nvObjC_ch] at hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl <;> decide
      · rw [nvObjP_ch] at hv; simp only [List.mem_singleton] at hv; subst hv
        exact absurd hv0 (by decide)
      · exact absurd houa.symm ih
  exact hNoU nvAddrU hr rfl

/-- Concrete `Mem 64` non-vacuity (`XPost := False`) for `lcnf_dec_ref_cold`:
dropping root ctor `A` (`rc=1`) cascadingly frees exclusive closure `B` (`rc=1`), decrements
shared ctor `C` from `rc=3` to `rc=1`, and preserves persistent leaf `P` (`rc=0`) and
unreachable ctor `U` (`rc=2`). -/
theorem nv_dec_ref_cold_dag :
    Func.wp rtC0Env lcnf_dec_ref_cold.body (nvRtBase, nvAddrA, ()) nvDagMem
      (fun () m' => ∃ st' objs',
        st'.PreservesMeta nvRtState ∧ st'.rem = nvRtState.rem ∧
        (rtC0Inv nvRtBase st' ⋆ lcnfHeap objs') m' ∧
        (∀ o' ∈ objs', o'.addr ≠ nvAddrA ∧ o'.addr ≠ nvAddrB) ∧
        (∃ oC ∈ objs', oC.addr = nvAddrC ∧ oC.rc = 1#32) ∧
        (∃ oP ∈ objs', oP.addr = nvAddrP ∧ oP.rc = 0#32) ∧
        (∃ oU ∈ objs', oU.addr = nvAddrU ∧ oU.rc = 2#32))
      (fun _ _ _ _ => False) := by
  have hm : (rtC0Inv nvRtBase nvRtState ⋆ lcnfHeap nvDagObjs ⋆ emp) nvDagMem := by
    rw [sep_emp]; exact nvDagMem_ok
  refine rtC0Env_dec_ref_cold_wp (nvRtBase, nvAddrA, ()) nvDagMem _ _
    ⟨by decide, nvRtState, nvDagObjs, emp, by decide, hm,
      ⟨nvObjA, by simp [nvDagObjs], rfl, rfl⟩, nvDagObjs_wf, nvDagObjs_closed,
      nvDagObjs_rcSound, ?_⟩
  intro st' objs' m' hMeta hRem hRel hm'
  rw [sep_emp] at hm'
  rcases hRel with ⟨_, _, _, _, hSurv, _, _, hPersSurv, hExact⟩
  have hNotA : ∀ o' ∈ objs', o'.addr ≠ nvAddrA := fun o' ho' => (hSurv o' ho').2.1
  have hAfree : nvObjA ∈ freedObjs nvDagObjs objs' := by
    simp only [freedObjs, List.mem_filter, Bool.not_eq_true']
    refine ⟨by simp [nvDagObjs], ?_⟩
    change (objs'.map LcnfObj.addr).contains nvAddrA = false
    cases hc : (objs'.map LcnfObj.addr).contains nvAddrA
    · rfl
    · have hmA := List.contains_iff_mem.mp hc
      rw [List.mem_map] at hmA
      obtain ⟨o', ho', heq⟩ := hmA
      exact absurd heq (hNotA o' ho')
  have hNotB : ∀ o' ∈ objs', o'.addr ≠ nvAddrB := by
    intro o' ho' heq
    have hEqB := (hExact nvObjB (by simp [nvDagObjs]) (by decide)).1 o' ho' heq
    have hSurvB := hSurv o' ho'
    have hPosB : 0 < o'.rc.toNat := by
      rcases hSurvB.2.2 with ⟨orig, horig, had, _, _, _, _, _, _, _, _, _, _, _, hrc⟩
      have hOrigB : orig = nvObjB := by
        simp only [nvDagObjs, List.mem_cons, List.not_mem_nil, or_false] at horig
        rcases horig with rfl | rfl | rfl | rfl | rfl <;>
          first | rfl | exact absurd (had.trans heq) (by decide)
      subst hOrigB
      rcases hrc with ⟨h0, _⟩ | ⟨_, hpos, _⟩
      · exact absurd h0 (by decide)
      · have hlt := objWf_rc_lt hSurvB.1
        rw [BitVec.toInt_eq_toNat_cond] at hpos; split at hpos <;> omega
    have hRefB : 1 ≤ nonPersistRefs (freedObjs nvDagObjs objs') nvAddrB := by
      rw [List.mem_iff_getElem] at hAfree
      obtain ⟨i, hi, hAi⟩ := hAfree
      have hsp := nonPersistRefs_focus (freedObjs nvDagObjs objs') hi nvAddrB
      rw [hAi] at hsp
      have h1 : nvObjA.childFields.count nvAddrB = 1 := by decide
      have hnz : nvObjA.rc ≠ 0#32 := by decide
      simp only [hnz, ↓reduceIte, h1] at hsp; omega
    have h1B : nvObjB.rc.toNat = 1 := rfl
    have hba : nvObjB.addr = nvAddrB := rfl
    have hneBA : (if nvAddrB = nvAddrA then 1 else 0) = 0 := by decide
    rw [h1B, hba, hneBA] at hEqB; omega
  have hBfree : nvObjB ∈ freedObjs nvDagObjs objs' := by
    simp only [freedObjs, List.mem_filter, Bool.not_eq_true']
    refine ⟨by simp [nvDagObjs], ?_⟩
    change (objs'.map LcnfObj.addr).contains nvAddrB = false
    cases hc : (objs'.map LcnfObj.addr).contains nvAddrB
    · rfl
    · have hmB := List.contains_iff_mem.mp hc
      rw [List.mem_map] at hmB
      obtain ⟨o', ho', heq⟩ := hmB
      exact absurd heq (hNotB o' ho')
  have hPSurv : ∃ oP ∈ objs', oP.addr = nvAddrP ∧ oP.rc = 0#32 :=
    hPersSurv nvObjP (by simp [nvDagObjs]) rfl
  have hPnotFree : nvObjP ∉ freedObjs nvDagObjs objs' := by
    intro hmem
    simp only [freedObjs, List.mem_filter, Bool.not_eq_true'] at hmem
    obtain ⟨oP, hoP, hoPa, _⟩ := hPSurv
    have hc : (objs'.map LcnfObj.addr).contains nvAddrP = true :=
      List.contains_iff_mem.mpr (hoPa ▸ List.mem_map_of_mem hoP)
    have hpa : nvObjP.addr = nvAddrP := rfl
    rw [hpa, hc] at hmem; exact absurd hmem.2 (by decide)
  have hUnotFree : nvObjU ∉ freedObjs nvDagObjs objs' := fun hmem =>
    nvDag_not_reach_U ((hExact nvObjU (by simp [nvDagObjs]) (by decide)).2 hmem).2
  have hCnotFree : nvObjC ∉ freedObjs nvDagObjs objs' := by
    intro hmem
    have hEqC := ((hExact nvObjC (by simp [nvDagObjs]) (by decide)).2 hmem).1
    have hle : nonPersistRefs (freedObjs nvDagObjs objs') nvAddrC ≤
        nonPersistRefs nvDagObjs nvAddrC := by
      have hsub : ∀ (xs : List LcnfObj) (p : LcnfObj → Bool),
          nonPersistRefs (xs.filter p) nvAddrC ≤ nonPersistRefs xs nvAddrC := by
        intro xs p
        induction xs with
        | nil => simp [nonPersistRefs]
        | cons z zs ih =>
          rw [List.filter_cons, nonPersistRefs_cons]
          cases p z
          · simp only [Bool.false_eq_true, ↓reduceIte]; omega
          · simp only [↓reduceIte, nonPersistRefs_cons]; omega
      exact hsub nvDagObjs _
    have h2 : nonPersistRefs nvDagObjs nvAddrC = 2 := by decide
    have h3 : nvObjC.rc.toNat = 3 := rfl
    have hne : (if nvObjC.addr = nvAddrA then 1 else 0) = 0 := by decide
    have hcAddr : nvObjC.addr = nvAddrC := rfl
    rw [h3, hne, hcAddr] at hEqC; omega
  have hFreeEq : freedObjs nvDagObjs objs' = [nvObjA, nvObjB] := by
    have hfA : (objs'.map LcnfObj.addr).contains nvAddrA = false := by
      simp only [freedObjs, List.mem_filter, Bool.not_eq_true'] at hAfree; exact hAfree.2
    have hfB : (objs'.map LcnfObj.addr).contains nvAddrB = false := by
      simp only [freedObjs, List.mem_filter, Bool.not_eq_true'] at hBfree; exact hBfree.2
    have hfC : (objs'.map LcnfObj.addr).contains nvAddrC = true := by
      cases h : (objs'.map LcnfObj.addr).contains nvAddrC
      · exfalso; apply hCnotFree
        simp only [freedObjs, List.mem_filter, Bool.not_eq_true']
        exact ⟨by simp [nvDagObjs], h⟩
      · rfl
    have hfP : (objs'.map LcnfObj.addr).contains nvAddrP = true := by
      cases h : (objs'.map LcnfObj.addr).contains nvAddrP
      · exfalso; apply hPnotFree
        simp only [freedObjs, List.mem_filter, Bool.not_eq_true']
        exact ⟨by simp [nvDagObjs], h⟩
      · rfl
    have hfU : (objs'.map LcnfObj.addr).contains nvAddrU = true := by
      cases h : (objs'.map LcnfObj.addr).contains nvAddrU
      · exfalso; apply hUnotFree
        simp only [freedObjs, List.mem_filter, Bool.not_eq_true']
        exact ⟨by simp [nvDagObjs], h⟩
      · rfl
    change (nvDagObjs.filter (fun o => !(objs'.map LcnfObj.addr).contains o.addr)) =
      [nvObjA, nvObjB]
    simp only [nvDagObjs, List.filter_cons, List.filter_nil]
    change (if !(objs'.map LcnfObj.addr).contains nvAddrA then nvObjA :: _ else _) = _
    rw [hfA]; simp only [Bool.not_false, ↓reduceIte]
    change _ :: (if !(objs'.map LcnfObj.addr).contains nvAddrB then nvObjB :: _ else _) = _
    rw [hfB]; simp only [Bool.not_false, ↓reduceIte]
    change _ :: _ :: (if !(objs'.map LcnfObj.addr).contains nvAddrC then nvObjC :: _ else _) = _
    rw [hfC]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    change _ :: _ :: (if !(objs'.map LcnfObj.addr).contains nvAddrP then nvObjP :: _ else _) = _
    rw [hfP]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    change _ :: _ :: (if !(objs'.map LcnfObj.addr).contains nvAddrU then nvObjU :: _ else _) = _
    rw [hfU]; simp
  have hCSurv : ∃ oC ∈ objs', oC.addr = nvAddrC ∧ oC.rc = 1#32 := by
    have hIn : nvAddrC ∈ objs'.map LcnfObj.addr := by
      cases hc : (objs'.map LcnfObj.addr).contains nvAddrC
      · exfalso; apply hCnotFree
        simp only [freedObjs, List.mem_filter, Bool.not_eq_true']
        exact ⟨by simp [nvDagObjs], hc⟩
      · exact List.contains_iff_mem.mp hc
    rw [List.mem_map] at hIn
    obtain ⟨oC, hoC, hoCa⟩ := hIn
    have hEqC := (hExact nvObjC (by simp [nvDagObjs]) (by decide)).1 oC hoC hoCa
    rw [hFreeEq] at hEqC
    have hdrop : (if nvObjC.addr = nvAddrA then 1 else 0) +
        nonPersistRefs [nvObjA, nvObjB] nvObjC.addr = 2 := by decide
    have h3 : nvObjC.rc.toNat = 3 := rfl
    rw [hdrop, h3] at hEqC
    exact ⟨oC, hoC, hoCa, BitVec.eq_of_toNat_eq (by change oC.rc.toNat = 1; omega)⟩
  have hUSurv : ∃ oU ∈ objs', oU.addr = nvAddrU ∧ oU.rc = 2#32 := by
    have hIn : nvAddrU ∈ objs'.map LcnfObj.addr := by
      cases hc : (objs'.map LcnfObj.addr).contains nvAddrU
      · exfalso; apply hUnotFree
        simp only [freedObjs, List.mem_filter, Bool.not_eq_true']
        exact ⟨by simp [nvDagObjs], hc⟩
      · exact List.contains_iff_mem.mp hc
    rw [List.mem_map] at hIn
    obtain ⟨oU, hoU, hoUa⟩ := hIn
    have hEqU := (hExact nvObjU (by simp [nvDagObjs]) (by decide)).1 oU hoU hoUa
    rw [hFreeEq] at hEqU
    have hdrop : (if nvObjU.addr = nvAddrA then 1 else 0) +
        nonPersistRefs [nvObjA, nvObjB] nvObjU.addr = 0 := by decide
    have h2 : nvObjU.rc.toNat = 2 := rfl
    rw [hdrop, h2] at hEqU
    exact ⟨oU, hoU, hoUa, BitVec.eq_of_toNat_eq (by change oU.rc.toNat = 2; omega)⟩
  exact ⟨st', objs', hMeta, hRem, hm', fun o' ho' => ⟨hNotA o' ho', hNotB o' ho'⟩,
    hCSurv, hPSurv, hUSurv⟩

/-- Concrete `Mem 64` non-vacuity (`XPost := False`) for `lcnf_mark_persistent`:
marking root ctor `A` recursively marks closure `B` and shared ctor `C` persistent (`rc=0`),
keeps persistent leaf `P` (`rc=0`), and leaves unreachable ctor `U` untouched (`rc=2`). -/
theorem nv_mark_persistent_dag :
    Func.wp rtC0Env lcnf_mark_persistent.body (nvRtBase, nvAddrA, ()) nvDagMem
      (fun () m' => ∃ st' objs',
        st'.PreservesMeta nvRtState ∧ st'.rem = nvRtState.rem ∧
        (rtC0Inv nvRtBase st' ⋆ lcnfHeap objs') m' ∧
        objs'.length = 5 ∧
        (∀ h0 : 0 < objs'.length, objs'[0].addr = nvAddrA ∧ objs'[0].rc = 0#32) ∧
        (∀ h1 : 1 < objs'.length, objs'[1].addr = nvAddrB ∧ objs'[1].rc = 0#32) ∧
        (∀ h2 : 2 < objs'.length, objs'[2].addr = nvAddrC ∧ objs'[2].rc = 0#32) ∧
        (∀ h3 : 3 < objs'.length, objs'[3].addr = nvAddrP ∧ objs'[3].rc = 0#32) ∧
        (∀ h4 : 4 < objs'.length, objs'[4].addr = nvAddrU ∧ objs'[4].rc = 2#32))
      (fun _ _ _ _ => False) := by
  have hm : (rtC0Inv nvRtBase nvRtState ⋆ lcnfHeap nvDagObjs ⋆ emp) nvDagMem := by
    rw [sep_emp]; exact nvDagMem_ok
  refine rtC0Env_mark_persistent_wp (nvRtBase, nvAddrA, ()) nvDagMem _ _ ?_
  dsimp [lcnfMarkPersistentSpec]
  have hEven : (nvAddrA &&& 1#64 ≠ 0#64) = False := by decide
  simp only [hEven, ↓reduceIte]
  refine ⟨nvRtState, nvDagObjs, emp, by decide, hm, ⟨nvObjA, by simp [nvDagObjs], rfl⟩,
    nvDagObjs_wf, nvDagObjs_closed, ?_⟩
  intro st' objs' m' hMeta hRem hRel hm'
  rw [sep_emp] at hm'
  rcases hRel with ⟨hlen, _, _, _, hZip⟩
  have hlen5 : objs'.length = 5 := by simpa [nvDagObjs] using hlen
  have hAt : ∀ k (hk : k < 5), (nvDagObjs[k], objs'[k]'(by omega)) ∈ nvDagObjs.zip objs' := by
    intro k hk
    rw [List.mem_iff_getElem]
    exact ⟨k, by rw [List.length_zip, hlen5]; simp [nvDagObjs]; omega,
      by rw [List.getElem_zip]; rfl⟩
  have hReachA : NonPersistReach nvDagObjs nvAddrA nvAddrA :=
    NonPersistReach.refl ⟨nvObjA, by simp [nvDagObjs], rfl, by decide⟩
  have hReachB : NonPersistReach nvDagObjs nvAddrA nvAddrB :=
    NonPersistReach.step hReachA ⟨nvObjA, by simp [nvDagObjs], rfl, by decide⟩ (by decide)
      ⟨nvObjB, by simp [nvDagObjs], rfl, by decide⟩
  have hReachC : NonPersistReach nvDagObjs nvAddrA nvAddrC :=
    NonPersistReach.step hReachB ⟨nvObjB, by simp [nvDagObjs], rfl, by decide⟩ (by decide)
      ⟨nvObjC, by simp [nvDagObjs], rfl, by decide⟩
  rcases hZip _ (hAt 0 (by decide)) with ⟨_, h0a, _, _, _, _, _, _, _, _, _, _, _, h0r, _, _⟩
  rcases hZip _ (hAt 1 (by decide)) with ⟨_, h1a, _, _, _, _, _, _, _, _, _, _, _, _, _, h1i⟩
  rcases hZip _ (hAt 2 (by decide)) with ⟨_, h2a, _, _, _, _, _, _, _, _, _, _, _, _, _, h2i⟩
  rcases hZip _ (hAt 3 (by decide)) with ⟨_, h3a, _, _, _, _, _, _, _, _, _, _, _, _, h3o, _⟩
  rcases hZip _ (hAt 4 (by decide)) with ⟨_, h4a, _, _, _, _, _, _, _, _, _, _, _, _, h4o, h4i⟩
  refine ⟨st', objs', hMeta, hRem, hm', hlen5, ?_, ?_, ?_, ?_, ?_⟩
  · intro _; exact ⟨h0a, h0r rfl⟩
  · intro _; exact ⟨h1a, (h1i (by dsimp only; decide)).mpr hReachB⟩
  · intro _; exact ⟨h2a, (h2i (by dsimp only; decide)).mpr hReachC⟩
  · intro _; refine ⟨h3a, ?_⟩; rcases h3o with h | h <;> exact h
  · intro _
    refine ⟨h4a, ?_⟩
    rcases h4o with h | h
    · exact h
    · exact absurd ((h4i (by dsimp only; decide)).mp h) nvDag_not_reach_U

end LeanQbe.T.LeanLCNF
