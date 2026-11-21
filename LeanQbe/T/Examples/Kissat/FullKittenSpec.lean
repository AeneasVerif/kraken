module

public import LeanQbe.T.Examples.Kissat.FullKitten
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullInv1
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb
public import LeanQbe.T.Logic.SlabChain
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Scratch `kitten` Memory Layout & Scoped Accessors (`Part 1`)

Defines the memory footprint and accessor infrastructure for `FullKitten` (`Part 2` in
`FullKittenSpec1.lean` adds clause/watch/trail/UNSAT invariants and all `15` `Spec`s):
1. **`KittenState` & `SepTree`-backed `KittenMem`**:
   Partitions `h->scratch_buf[256..)` into `21` disjoint `u32` arrays (`32`-word `KH_*` header plus
   `20` fixed/dynamic tables ending in `arena`), bridged unconditionally to `array (t := i32)` and
   to `FullMem c s = FullKittenFrame c s ⋆ KittenMem (c.pScratchBuf + 1024#64) ks`.
2. **Strictly Scoped `KittenMemTactics` & `KittenMemATactics`**:
   `O(1)` `@[scoped c0_load]` / `@[scoped c0_store]` accessors matching C0 head-stepped addresses
   (zero global attributes).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Layout Constants & Small Bitvector Helpers -/

def kBase : Nat := 256
def kMaxV : Nat := 128
def kMaxL : Nat := 256
def kMaxOrig : Nat := 512
def kMaxCl : Nat := 896
def kSlabFixed : Nat := 8608
def kMinScratchCap : Nat := 10240

abbrev kmCore : BitVec 32 := 0x10000#32
abbrev kmLrn : BitVec 32 := 0x20000#32

theorem bv32_lit_div2_lt {nv : Nat} {l : BitVec 32} (hl : l.toNat < 2 * nv) :
    (l >>> (1 : Nat)).toNat < nv := by
  have h1 : (l >>> (1 : Nat)).toNat = l.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem bv32_lit_xor1_lt {nv : Nat} {l : BitVec 32} (hl : l.toNat < 2 * nv) :
    (l ^^^ 1#32).toNat < 2 * nv := by
  have h1 : (l ^^^ 1#32).toNat = l.toNat ^^^ 1 := by simp
  have h2 : l.toNat ^^^ 1 = litNeg l.toNat := rfl
  rw [h1, h2, litNeg_eq]
  split <;> omega

theorem bv32_cid_to_w0_lt {nc : Nat} {cid : BitVec 32} (hc : cid.toNat < nc)
    (hnc : nc ≤ 896) : (cid <<< (1 : Nat)).toNat = 2 * cid.toNat ∧
    (cid <<< (1 : Nat)).toNat < 2 * nc := by
  have hlt : cid.toNat < 896 := by omega
  have hshl : (cid <<< (1 : Nat)).toNat = 2 * cid.toNat := by bv_omega
  exact ⟨hshl, by omega⟩

theorem bv32_cid_to_w1_lt {nc : Nat} {cid : BitVec 32} (hc : cid.toNat < nc)
    (hnc : nc ≤ 896) : ((cid <<< (1 : Nat)) ||| 1#32).toNat = 2 * cid.toNat + 1 ∧
    ((cid <<< (1 : Nat)) ||| 1#32).toNat < 2 * nc := by
  have hsh : cid <<< (1 : Nat) = BitVec.ofNat 32 (2 * cid.toNat) := by bv_omega
  have h1 : BitVec.ofNat 32 (2 * cid.toNat) ||| 1#32 = BitVec.ofNat 32 (2 * cid.toNat + 1) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and,
      show (1#32).getLsbD i = decide (i = 0) by cases i <;> simp]
    cases i with
    | zero => simp [Nat.testBit_zero]
    | succ k => simp [Nat.testBit_succ, show (2 * cid.toNat + 1) / 2 = cid.toNat by omega]
  have hor : ((cid <<< (1 : Nat)) ||| 1#32).toNat = 2 * cid.toNat + 1 := by
    rw [hsh, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact ⟨hor, by omega⟩

theorem ptr_bv32_nat_mul4 (p : BitVec 64) (idx : Nat) (h : idx < 2 ^ 28) :
    p + BitVec.ofNat 64 idx * 4 = p + BitVec.ofNat 64 (4 * idx) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
  congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), show 4 % 2 ^ 64 = 4 from by decide,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mul_comm]

theorem ptr_kOff_bv32_mul4 (kPtr : BitVec 64) (kOff : Nat) (off32 : BitVec 32)
    (hk : kOff ≤ 8608) (hoff : off32 = BitVec.ofNat 32 kOff)
    {i : BitVec 32} (hi : i.toNat < 2 ^ 28) :
    kPtr + (off32 + i).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * kOff) + BitVec.ofNat 64 (4 * i.toNat) := by
  rw [hoff, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
  have hsum : kOff + i.toNat < 2 ^ 32 := by omega
  have heq : (BitVec.ofNat 32 kOff + i).setWidth 64 * BitVec.ofNat 64 4 =
      BitVec.ofNat 64 (4 * kOff) + BitVec.ofNat 64 (4 * i.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
    have hko : kOff % 2 ^ 32 = kOff := Nat.mod_eq_of_lt (by omega)
    rw [hko, Nat.mod_eq_of_lt hsum]
    have hmod2 : (kOff + i.toNat) % 2 ^ 64 = kOff + i.toNat := Nat.mod_eq_of_lt (by omega)
    rw [hmod2, show 4 % 2 ^ 64 = 4 from by decide]
    have hmul : (kOff + i.toNat) * 4 < 2 ^ 64 := by omega
    have h1 : (4 * kOff) % 2 ^ 64 = 4 * kOff := Nat.mod_eq_of_lt (by omega)
    have h2 : (4 * i.toNat) % 2 ^ 64 = 4 * i.toNat := Nat.mod_eq_of_lt (by omega)
    rw [Nat.mod_eq_of_lt hmul, h1, h2, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [heq, BitVec.add_assoc]

theorem kPtr_base_eq (p : BitVec 64) :
    p + BitVec.ofNat 64 256 * 4 = p + 1024#64 := rfl

private theorem kmCore_bit (i : Nat) : kmCore.getLsbD i = decide (i = 16) := by
  change (BitVec.ofNat 32 65536).getLsbD i = decide (i = 16)
  rw [BitVec.getLsbD_ofNat, show (65536 : Nat) = 2 ^ 16 from by decide, Nat.testBit_two_pow]
  by_cases hi : i = 16 <;> simp [hi, eq_comm]

private theorem kmLrn_bit (i : Nat) : kmLrn.getLsbD i = decide (i = 17) := by
  change (BitVec.ofNat 32 131072).getLsbD i = decide (i = 17)
  rw [BitVec.getLsbD_ofNat, show (131072 : Nat) = 2 ^ 17 from by decide, Nat.testBit_two_pow]
  by_cases hi : i = 17 <;> simp [hi, eq_comm]

private theorem mask16_bit (i : Nat) : (0xFFFF#32).getLsbD i = decide (i < 16) := by
  change (BitVec.ofNat 32 65535).getLsbD i = decide (i < 16)
  rw [BitVec.getLsbD_ofNat, show (65535 : Nat) = 2 ^ 16 - 1 from by decide,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 16 <;> simp [hi, show i < 16 → i < 32 from by omega]

theorem bv32_and_0xffff_or_core (x : BitVec 32) :
    ((x ||| kmCore) &&& 0xFFFF#32) = (x &&& 0xFFFF#32) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, kmCore_bit, mask16_bit]
  by_cases h : i < 16 <;> simp [h, show i < 16 → i ≠ 16 from by omega]

theorem bv32_and_lrn_or_core (x : BitVec 32) :
    ((x ||| kmCore) &&& kmLrn) = (x &&& kmLrn) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, kmCore_bit, kmLrn_bit]
  by_cases h : i = 17 <;> simp [h]

theorem bv32_and_core_or_core (x : BitVec 32) :
    ((x ||| kmCore) &&& kmCore) ≠ 0#32 := by
  intro h
  have h16 := congrArg (fun v => BitVec.getLsbD v 16) h
  rw [BitVec.getLsbD_and, BitVec.getLsbD_or, kmCore_bit, BitVec.getLsbD_zero] at h16
  simp at h16

theorem bv32_and_0xffff_and_not_core (x : BitVec 32) :
    ((x &&& ~~~kmCore) &&& 0xFFFF#32) = (x &&& 0xFFFF#32) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, kmCore_bit, mask16_bit, hi, decide_true,
    Bool.true_and]
  by_cases h : i < 16 <;> simp [h, show i < 16 → i ≠ 16 from by omega]

theorem bv32_and_lrn_and_not_core (x : BitVec 32) :
    ((x &&& ~~~kmCore) &&& kmLrn) = (x &&& kmLrn) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, kmCore_bit, kmLrn_bit, hi, decide_true,
    Bool.true_and]
  by_cases h : i = 17 <;> simp [h]

theorem bv32_and_core_and_not_core (x : BitVec 32) :
    ((x &&& ~~~kmCore) &&& kmCore) = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, kmCore_bit, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_zero]
  by_cases h : i = 16 <;> simp [h]

theorem bv32_and_0xffff_of_lt {x : BitVec 32} (h : x.toNat < 2 ^ 16) :
    x &&& 0xFFFF#32 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_and, mask16_bit]
  by_cases h16 : i < 16
  · simp [h16]
  · have hx : x.getLsbD i = false := by
      rw [← BitVec.testBit_toNat]
      exact Nat.testBit_lt_two_pow (by
        have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 16 ≤ i); omega)
    simp [h16, hx]

/-! ## 2. `KittenState`, `ShapesOk`, & Slab Serialization (`toSlab` / `ofSlab`) -/

/-- Typed representation of `kitten`'s `u32` slab starting at `scratch_buf + K_BASE` (`256`). -/
structure KittenState where
  nv : BitVec 32
  nc : BitVec 32
  orig_nc : BitVec 32
  lvl : BitVec 32
  prop : BitVec 32
  trl_end : BitVec 32
  unass : BitVec 32
  incons : BitVec 32
  failing : BitVec 32
  ante : BitVec 32
  qfirst : BitVec 32
  qlast : BitVec 32
  qsearch : BitVec 32
  qstamp : BitVec 32
  ticks : BitVec 32
  tick_lim : BitVec 32
  alen : BitVec 32
  acap : BitVec 32
  nassump : BitVec 32
  nunits : BitVec 32
  nres : BitVec 32
  nkl : BitVec 32
  nana : BitVec 32
  status : BitVec 32
  phase : BitVec 32
  hdrTail : List (BitVec 32)
  lvlArr : List (BitVec 32)
  rsn : List (BitVec 32)
  qprev : List (BitVec 32)
  qnext : List (BitVec 32)
  qstampArr : List (BitVec 32)
  trl : List (BitVec 32)
  flags : List (BitVec 32)
  vals : List (BitVec 32)
  assump : List (BitVec 32)
  ana : List (BitVec 32)
  kl : List (BitVec 32)
  units : List (BitVec 32)
  res : List (BitVec 32)
  whead : List (BitVec 32)
  wnext : List (BitVec 32)
  wblit : List (BitVec 32)
  clOff : List (BitVec 32)
  clMeta : List (BitVec 32)
  clAux : List (BitVec 32)
  arena : List (BitVec 32)

/-- First `32` `u32` words of `kitten`'s slab (`KH_NV .. KH_PHASE` + `7` unused words). -/
def kittenHdrWords (ks : KittenState) : List (BitVec 32) :=
  [ ks.nv, ks.nc, ks.orig_nc, ks.lvl, ks.prop, ks.trl_end, ks.unass, ks.incons,
    ks.failing, ks.ante, ks.qfirst, ks.qlast, ks.qsearch, ks.qstamp, ks.ticks, ks.tick_lim,
    ks.alen, ks.acap, ks.nassump, ks.nunits, ks.nres, ks.nkl, ks.nana, ks.status,
    ks.phase ] ++ ks.hdrTail

/-- Exact list-length well-formedness of all `21` sub-arrays in `KittenState`. -/
structure KittenState.ShapesOk (acap : Nat) (ks : KittenState) : Prop where
  hdrTail_len : ks.hdrTail.length = 7
  lvlArr_len : ks.lvlArr.length = 128
  rsn_len : ks.rsn.length = 128
  qprev_len : ks.qprev.length = 128
  qnext_len : ks.qnext.length = 128
  qstampArr_len : ks.qstampArr.length = 128
  trl_len : ks.trl.length = 128
  flags_len : ks.flags.length = 128
  vals_len : ks.vals.length = 256
  assump_len : ks.assump.length = 128
  ana_len : ks.ana.length = 128
  kl_len : ks.kl.length = 128
  units_len : ks.units.length = 256
  res_len : ks.res.length = 256
  whead_len : ks.whead.length = 256
  wnext_len : ks.wnext.length = 1792
  wblit_len : ks.wblit.length = 1792
  clOff_len : ks.clOff.length = 896
  clMeta_len : ks.clMeta.length = 896
  clAux_len : ks.clAux.length = 896
  arena_len : ks.arena.length = acap

theorem kittenHdrWords_length {acap : Nat} {ks : KittenState}
    (h : ks.ShapesOk acap) : (kittenHdrWords ks).length = 32 := by
  simp [kittenHdrWords, h.hdrTail_len]

/-- Flatten `KittenState` back into the `8608 + acap`-word `u32` slab starting at `K_BASE`. -/
def KittenState.toSlab (ks : KittenState) : List (BitVec 32) :=
  kittenHdrWords ks ++ (ks.lvlArr ++ (ks.rsn ++ (ks.qprev ++ (ks.qnext ++ (ks.qstampArr ++
  (ks.trl ++ (ks.flags ++ (ks.vals ++ (ks.assump ++ (ks.ana ++ (ks.kl ++ (ks.units ++ (ks.res ++
  (ks.whead ++ (ks.wnext ++ (ks.wblit ++ (ks.clOff ++ (ks.clMeta ++
  (ks.clAux ++ ks.arena)))))))))))))))))))

theorem KittenState.toSlab_length {acap : Nat} {ks : KittenState}
    (h : ks.ShapesOk acap) : ks.toSlab.length = 8608 + acap := by
  have hh := kittenHdrWords_length h
  rcases h with ⟨_, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20⟩
  dsimp only [KittenState.toSlab]
  simp only [List.length_append]
  rw [hh, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
  simp only [← Nat.add_assoc]

/-- Slice a flat `u32` slab starting at `K_BASE` (`scr.drop 256`) into `KittenState`. -/
def KittenState.ofSlab (xs : List (BitVec 32)) : KittenState where
  nv := xs[0]?.getD 0#32
  nc := xs[1]?.getD 0#32
  orig_nc := xs[2]?.getD 0#32
  lvl := xs[3]?.getD 0#32
  prop := xs[4]?.getD 0#32
  trl_end := xs[5]?.getD 0#32
  unass := xs[6]?.getD 0#32
  incons := xs[7]?.getD 0#32
  failing := xs[8]?.getD 0#32
  ante := xs[9]?.getD 0#32
  qfirst := xs[10]?.getD 0#32
  qlast := xs[11]?.getD 0#32
  qsearch := xs[12]?.getD 0#32
  qstamp := xs[13]?.getD 0#32
  ticks := xs[14]?.getD 0#32
  tick_lim := xs[15]?.getD 0#32
  alen := xs[16]?.getD 0#32
  acap := xs[17]?.getD 0#32
  nassump := xs[18]?.getD 0#32
  nunits := xs[19]?.getD 0#32
  nres := xs[20]?.getD 0#32
  nkl := xs[21]?.getD 0#32
  nana := xs[22]?.getD 0#32
  status := xs[23]?.getD 0#32
  phase := xs[24]?.getD 0#32
  hdrTail := (xs.drop 25).take 7
  lvlArr := (xs.drop 32).take 128
  rsn := (xs.drop 160).take 128
  qprev := (xs.drop 288).take 128
  qnext := (xs.drop 416).take 128
  qstampArr := (xs.drop 544).take 128
  trl := (xs.drop 672).take 128
  flags := (xs.drop 800).take 128
  vals := (xs.drop 928).take 256
  assump := (xs.drop 1184).take 128
  ana := (xs.drop 1312).take 128
  kl := (xs.drop 1440).take 128
  units := (xs.drop 1568).take 256
  res := (xs.drop 1824).take 256
  whead := (xs.drop 2080).take 256
  wnext := (xs.drop 2336).take 1792
  wblit := (xs.drop 4128).take 1792
  clOff := (xs.drop 5920).take 896
  clMeta := (xs.drop 6816).take 896
  clAux := (xs.drop 7712).take 896
  arena := xs.drop 8608

theorem KittenState.shapesOk_ofSlab {xs : List (BitVec 32)} (h : 8608 ≤ xs.length) :
    (KittenState.ofSlab xs).ShapesOk (xs.length - 8608) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [KittenState.ofSlab, List.length_take, List.length_drop]; try omega

private theorem slab_slice_append {α : Type _} (xs : List α) (a b : Nat) :
    (xs.drop a).take b ++ xs.drop (a + b) = xs.drop a := by
  rw [← @List.drop_drop _ b a xs, List.take_append_drop]

private theorem slab_getElem_of_lt {xs : List (BitVec 32)} {i : Nat} (hi : i < xs.length) :
    xs[i]?.getD 0#32 = xs[i]'hi := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some]

private theorem slab_hdr_prefix_eq (xs : List (BitVec 32)) (h : 32 ≤ xs.length) :
    [ xs[0]?.getD 0#32, xs[1]?.getD 0#32, xs[2]?.getD 0#32, xs[3]?.getD 0#32,
      xs[4]?.getD 0#32, xs[5]?.getD 0#32, xs[6]?.getD 0#32, xs[7]?.getD 0#32,
      xs[8]?.getD 0#32, xs[9]?.getD 0#32, xs[10]?.getD 0#32, xs[11]?.getD 0#32,
      xs[12]?.getD 0#32, xs[13]?.getD 0#32, xs[14]?.getD 0#32, xs[15]?.getD 0#32,
      xs[16]?.getD 0#32, xs[17]?.getD 0#32, xs[18]?.getD 0#32, xs[19]?.getD 0#32,
      xs[20]?.getD 0#32, xs[21]?.getD 0#32, xs[22]?.getD 0#32, xs[23]?.getD 0#32,
      xs[24]?.getD 0#32 ] = xs.take 25 := by
  apply List.ext_getElem
  · simp only [List.length_cons, List.length_nil, List.length_take]; omega
  · intro i hi1 _
    have hi : i < 25 := by simp at hi1; exact hi1
    rw [List.getElem_take]
    rcases (by omega :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨
      i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨
      i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact slab_getElem_of_lt (by omega)

theorem KittenState.toSlab_ofSlab {xs : List (BitVec 32)} (h : 8608 ≤ xs.length) :
    (KittenState.ofSlab xs).toSlab = xs := by
  have h1 : kittenHdrWords (KittenState.ofSlab xs) = xs.take 32 := by
    simp only [kittenHdrWords, KittenState.ofSlab]
    rw [slab_hdr_prefix_eq xs (by omega)]
    rw [← List.take_append_drop 25 (xs.take 32), List.take_take, Nat.min_eq_left (by omega),
      List.drop_take]
  simp only [KittenState.toSlab, KittenState.ofSlab] at h1 ⊢
  rw [h1]
  rw [slab_slice_append xs 7712 896, slab_slice_append xs 6816 896,
    slab_slice_append xs 5920 896, slab_slice_append xs 4128 1792,
    slab_slice_append xs 2336 1792, slab_slice_append xs 2080 256,
    slab_slice_append xs 1824 256, slab_slice_append xs 1568 256,
    slab_slice_append xs 1440 128, slab_slice_append xs 1312 128,
    slab_slice_append xs 1184 128, slab_slice_append xs 928 256,
    slab_slice_append xs 800 128, slab_slice_append xs 672 128,
    slab_slice_append xs 544 128, slab_slice_append xs 416 128,
    slab_slice_append xs 288 128, slab_slice_append xs 160 128,
    slab_slice_append xs 32 128, List.take_append_drop]

private theorem slab_drop_exact {α : Type _} (p s : List α) {k : Nat} (hk : p.length = k) :
    (p ++ s).drop k = s := by
  rw [List.drop_append_of_le_length (by omega), ← hk, List.drop_length, List.nil_append]

private theorem slab_drop_step {α : Type _} {xs p rest : List α} {k0 k1 n : Nat}
    (hd : xs.drop k0 = p ++ rest) (hp : p.length = n) (hsum : k1 = k0 + n) :
    xs.drop k1 = rest := by
  rw [hsum, ← List.drop_drop, hd]
  exact slab_drop_exact p rest hp

private theorem slab_take_prefix {α : Type _} {xs p rest : List α} {k n : Nat}
    (hd : xs.drop k = p ++ rest) (hp : p.length = n) :
    (xs.drop k).take n = p := by
  rw [hd, List.take_append_of_le_length (by omega), ← hp, List.take_length]

theorem KittenState.ofSlab_toSlab {acap : Nat} {ks : KittenState} (h : ks.ShapesOk acap) :
    KittenState.ofSlab ks.toSlab = ks := by
  rcases ks with ⟨nv, nc, orig_nc, lvl, prop, trl_end, unass, incons, failing, ante, qfirst,
    qlast, qsearch, qstamp, ticks, tick_lim, alen, acapF, nassump, nunits, nres, nkl, nana,
    status, phase, hdrTail, lvlArr, rsn, qprev, qnext, qstampArr, trl, flags, vals, assump,
    ana, kl, units, res, whead, wnext, wblit, clOff, clMeta, clAux, arena⟩
  rcases h with ⟨htl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, _⟩
  have htl' : hdrTail.length = 7 := htl
  let L0 := [nv, nc, orig_nc, lvl, prop, trl_end, unass, incons, failing, ante, qfirst, qlast,
    qsearch, qstamp, ticks, tick_lim, alen, acapF, nassump, nunits, nres, nkl, nana, status, phase]
  let ts : List (BitVec 32) :=
    (L0 ++ hdrTail) ++ (lvlArr ++ (rsn ++ (qprev ++ (qnext ++ (qstampArr ++ (trl ++ (flags ++
    (vals ++ (assump ++ (ana ++ (kl ++ (units ++ (res ++ (whead ++ (wnext ++ (wblit ++
    (clOff ++ (clMeta ++ (clAux ++ arena)))))))))))))))))))
  have hdrop0 : ts.drop 32 =
      lvlArr ++ (rsn ++ (qprev ++ (qnext ++ (qstampArr ++ (trl ++ (flags ++ (vals ++ (assump ++
      (ana ++ (kl ++ (units ++ (res ++ (whead ++ (wnext ++ (wblit ++ (clOff ++ (clMeta ++
      (clAux ++ arena)))))))))))))))))) :=
    slab_drop_exact (L0 ++ hdrTail) _ (by simpa [L0, List.length_append] using htl')
  have hdrop1 := slab_drop_step hdrop0 h1 (by decide : 160 = 32 + 128)
  have hdrop2 := slab_drop_step hdrop1 h2 (by decide : 288 = 160 + 128)
  have hdrop3 := slab_drop_step hdrop2 h3 (by decide : 416 = 288 + 128)
  have hdrop4 := slab_drop_step hdrop3 h4 (by decide : 544 = 416 + 128)
  have hdrop5 := slab_drop_step hdrop4 h5 (by decide : 672 = 544 + 128)
  have hdrop6 := slab_drop_step hdrop5 h6 (by decide : 800 = 672 + 128)
  have hdrop7 := slab_drop_step hdrop6 h7 (by decide : 928 = 800 + 128)
  have hdrop8 := slab_drop_step hdrop7 h8 (by decide : 1184 = 928 + 256)
  have hdrop9 := slab_drop_step hdrop8 h9 (by decide : 1312 = 1184 + 128)
  have hdrop10 := slab_drop_step hdrop9 h10 (by decide : 1440 = 1312 + 128)
  have hdrop11 := slab_drop_step hdrop10 h11 (by decide : 1568 = 1440 + 128)
  have hdrop12 := slab_drop_step hdrop11 h12 (by decide : 1824 = 1568 + 256)
  have hdrop13 := slab_drop_step hdrop12 h13 (by decide : 2080 = 1824 + 256)
  have hdrop14 := slab_drop_step hdrop13 h14 (by decide : 2336 = 2080 + 256)
  have hdrop15 := slab_drop_step hdrop14 h15 (by decide : 4128 = 2336 + 1792)
  have hdrop16 := slab_drop_step hdrop15 h16 (by decide : 5920 = 4128 + 1792)
  have hdrop17 := slab_drop_step hdrop16 h17 (by decide : 6816 = 5920 + 896)
  have hdrop18 := slab_drop_step hdrop17 h18 (by decide : 7712 = 6816 + 896)
  have hdrop19 := slab_drop_step hdrop18 h19 (by decide : 8608 = 7712 + 896)
  have hhdrT : (ts.drop 25).take 7 = hdrTail := by
    simp only [ts, List.append_assoc]
    rw [List.drop_append_of_le_length (by simp [L0])]
    have hnil : L0.drop 25 = [] := by simp [L0]
    rw [hnil, List.nil_append, List.take_append_of_le_length (by rw [htl']; decide),
      ← htl', List.take_length]
  change KittenState.ofSlab ts = _
  simp only [KittenState.ofSlab]
  have hp0 : ts[0]?.getD 0#32 = nv := rfl
  have hp1 : ts[1]?.getD 0#32 = nc := rfl
  have hp2 : ts[2]?.getD 0#32 = orig_nc := rfl
  have hp3 : ts[3]?.getD 0#32 = lvl := rfl
  have hp4 : ts[4]?.getD 0#32 = prop := rfl
  have hp5 : ts[5]?.getD 0#32 = trl_end := rfl
  have hp6 : ts[6]?.getD 0#32 = unass := rfl
  have hp7 : ts[7]?.getD 0#32 = incons := rfl
  have hp8 : ts[8]?.getD 0#32 = failing := rfl
  have hp9 : ts[9]?.getD 0#32 = ante := rfl
  have hp10 : ts[10]?.getD 0#32 = qfirst := rfl
  have hp11 : ts[11]?.getD 0#32 = qlast := rfl
  have hp12 : ts[12]?.getD 0#32 = qsearch := rfl
  have hp13 : ts[13]?.getD 0#32 = qstamp := rfl
  have hp14 : ts[14]?.getD 0#32 = ticks := rfl
  have hp15 : ts[15]?.getD 0#32 = tick_lim := rfl
  have hp16 : ts[16]?.getD 0#32 = alen := rfl
  have hp17 : ts[17]?.getD 0#32 = acapF := rfl
  have hp18 : ts[18]?.getD 0#32 = nassump := rfl
  have hp19 : ts[19]?.getD 0#32 = nunits := rfl
  have hp20 : ts[20]?.getD 0#32 = nres := rfl
  have hp21 : ts[21]?.getD 0#32 = nkl := rfl
  have hp22 : ts[22]?.getD 0#32 = nana := rfl
  have hp23 : ts[23]?.getD 0#32 = status := rfl
  have hp24 : ts[24]?.getD 0#32 = phase := rfl
  rw [hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16,
    hp17, hp18, hp19, hp20, hp21, hp22, hp23, hp24, hhdrT,
    slab_take_prefix hdrop0 h1, slab_take_prefix hdrop1 h2, slab_take_prefix hdrop2 h3,
    slab_take_prefix hdrop3 h4, slab_take_prefix hdrop4 h5, slab_take_prefix hdrop5 h6,
    slab_take_prefix hdrop6 h7, slab_take_prefix hdrop7 h8, slab_take_prefix hdrop8 h9,
    slab_take_prefix hdrop9 h10, slab_take_prefix hdrop10 h11, slab_take_prefix hdrop11 h12,
    slab_take_prefix hdrop12 h13, slab_take_prefix hdrop13 h14, slab_take_prefix hdrop14 h15,
    slab_take_prefix hdrop15 h16, slab_take_prefix hdrop16 h17, slab_take_prefix hdrop17 h18,
    slab_take_prefix hdrop18 h19, hdrop19]

/-! ## 3. Balanced `SepTree` (`KittenTree`, `KittenMem`) & FullMem Bridges -/

def kPath : Nat → List Bool
  | 0 => [false, false, false, false]
  | 1 => [false, false, false, true]
  | 2 => [false, false, true, false]
  | 3 => [false, false, true, true, false]
  | 4 => [false, false, true, true, true]
  | 5 => [false, true, false, false]
  | 6 => [false, true, false, true]
  | 7 => [false, true, true, false]
  | 8 => [false, true, true, true, false]
  | 9 => [false, true, true, true, true]
  | 10 => [true, false, false, false]
  | 11 => [true, false, false, true]
  | 12 => [true, false, true, false]
  | 13 => [true, false, true, true, false]
  | 14 => [true, false, true, true, true]
  | 15 => [true, true, false, false]
  | 16 => [true, true, false, true, false]
  | 17 => [true, true, false, true, true]
  | 18 => [true, true, true, false]
  | 19 => [true, true, true, true, false]
  | _ => [true, true, true, true, true]

/-- Explicit balanced `21`-leaf `SepTree` over `kitten`'s slab starting at `kPtr` (matching
`kPath 0 .. kPath 20` with zero list-splitting reduction overhead). -/
def KittenTree (kPtr : BitVec 64) (ks : KittenState) : SepTree :=
  let t01 := SepTree.node
    (.leaf (array (t := i32) kPtr (kittenHdrWords ks)))
    (.leaf (array (t := i32) (kPtr + 128#64) ks.lvlArr))
  let t34 := SepTree.node
    (.leaf (array (t := i32) (kPtr + 1152#64) ks.qprev))
    (.leaf (array (t := i32) (kPtr + 1664#64) ks.qnext))
  let t24 := SepTree.node (.leaf (array (t := i32) (kPtr + 640#64) ks.rsn)) t34
  let t04 := SepTree.node t01 t24
  let t56 := SepTree.node
    (.leaf (array (t := i32) (kPtr + 2176#64) ks.qstampArr))
    (.leaf (array (t := i32) (kPtr + 2688#64) ks.trl))
  let t89 := SepTree.node
    (.leaf (array (t := i32) (kPtr + 3712#64) ks.vals))
    (.leaf (array (t := i32) (kPtr + 4736#64) ks.assump))
  let t79 := SepTree.node (.leaf (array (t := i32) (kPtr + 3200#64) ks.flags)) t89
  let t59 := SepTree.node t56 t79
  let t1011 := SepTree.node
    (.leaf (array (t := i32) (kPtr + 5248#64) ks.ana))
    (.leaf (array (t := i32) (kPtr + 5760#64) ks.kl))
  let t1314 := SepTree.node
    (.leaf (array (t := i32) (kPtr + 7296#64) ks.res))
    (.leaf (array (t := i32) (kPtr + 8320#64) ks.whead))
  let t1214 := SepTree.node (.leaf (array (t := i32) (kPtr + 6272#64) ks.units)) t1314
  let t1014 := SepTree.node t1011 t1214
  let t1617 := SepTree.node
    (.leaf (array (t := i32) (kPtr + 16512#64) ks.wblit))
    (.leaf (array (t := i32) (kPtr + 23680#64) ks.clOff))
  let t1517 := SepTree.node (.leaf (array (t := i32) (kPtr + 9344#64) ks.wnext)) t1617
  let t1920 := SepTree.node
    (.leaf (array (t := i32) (kPtr + 30848#64) ks.clAux))
    (.leaf (array (t := i32) (kPtr + 34432#64) ks.arena))
  let t1820 := SepTree.node (.leaf (array (t := i32) (kPtr + 27264#64) ks.clMeta)) t1920
  let t1520 := SepTree.node t1517 t1820
  .node (.node t04 t59) (.node t1014 t1520)

/-- `O(log 21)` `SepTree` footprint predicate for `kitten`'s `u32` slab at `kPtr`. -/
def KittenMem (kPtr : BitVec 64) (ks : KittenState) : Mem 64 → Prop :=
  (KittenTree kPtr ks).eval

private theorem array32_append_off (a off : BitVec 64) (xs ys : List (BitVec 32))
    (hs : a + BitVec.ofNat 64 (4 * xs.length) = off) :
    array (t := i32) a (xs ++ ys) =
      (array (t := i32) a xs ⋆ array (t := i32) off ys) := by
  rw [array_append, show (i32 : Ty).bytes = 4 from rfl, hs]

theorem kittenMem_eq_array {acap : Nat} (kPtr : BitVec 64) {ks : KittenState}
    (h : ks.ShapesOk acap) :
    KittenMem kPtr ks = array (t := i32) kPtr ks.toSlab := by
  have hh := kittenHdrWords_length h
  rcases h with ⟨_, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, _⟩
  dsimp only [KittenMem, KittenTree, SepTree.eval, KittenState.toSlab]
  rw [array32_append_off kPtr (kPtr + 128#64) (kittenHdrWords ks) _ (by rw [hh])]
  rw [array32_append_off (kPtr + 128#64) (kPtr + 640#64) ks.lvlArr _
    (by rw [h1, ptr_add_ofNat])]
  rw [array32_append_off (kPtr + 640#64) (kPtr + 1152#64) ks.rsn _
    (by rw [h2, ptr_add_ofNat])]
  rw [array32_append_off (kPtr + 1152#64) (kPtr + 1664#64) ks.qprev _
    (by rw [h3, ptr_add_ofNat])]
  rw [array32_append_off (kPtr + 1664#64) (kPtr + 2176#64) ks.qnext _
    (by rw [h4, ptr_add_ofNat])]
  rw [array32_append_off (kPtr + 2176#64) (kPtr + 2688#64) ks.qstampArr _
    (by rw [h5, ptr_add_ofNat])]
  rw [array32_append_off (kPtr + 2688#64) (kPtr + 3200#64) ks.trl _
    (by rw [h6, ptr_add_ofNat])]
  rw [array32_append_off (kPtr + 3200#64) (kPtr + 3712#64) ks.flags _
    (by rw [h7, ptr_add_ofNat])]
  rw [array32_append_off (kPtr + 3712#64) (kPtr + 4736#64) ks.vals _
    (by rw [h8, ptr_add_ofNat])]
  rw [array32_append_off (kPtr + 4736#64) (kPtr + 5248#64) ks.assump _
    (by rw [h9, ptr_add_ofNat])]
  rw [array32_append_off (kPtr + 5248#64) (kPtr + 5760#64) ks.ana _
    (by rw [h10, ptr_add_ofNat])]
  rw [array32_append_off (kPtr + 5760#64) (kPtr + 6272#64) ks.kl _
    (by rw [h11, ptr_add_ofNat])]
  rw [array32_append_off (kPtr + 6272#64) (kPtr + 7296#64) ks.units _
    (by rw [h12, ptr_add_ofNat])]
  rw [array32_append_off (kPtr + 7296#64) (kPtr + 8320#64) ks.res _
    (by rw [h13, ptr_add_ofNat])]
  rw [array32_append_off (kPtr + 8320#64) (kPtr + 9344#64) ks.whead _
    (by rw [h14, ptr_add_ofNat])]
  rw [array32_append_off (kPtr + 9344#64) (kPtr + 16512#64) ks.wnext _
    (by rw [h15, ptr_add_ofNat])]
  rw [array32_append_off (kPtr + 16512#64) (kPtr + 23680#64) ks.wblit _
    (by rw [h16, ptr_add_ofNat])]
  rw [array32_append_off (kPtr + 23680#64) (kPtr + 27264#64) ks.clOff _
    (by rw [h17, ptr_add_ofNat])]
  rw [array32_append_off (kPtr + 27264#64) (kPtr + 30848#64) ks.clMeta _
    (by rw [h18, ptr_add_ofNat])]
  rw [array32_append_off (kPtr + 30848#64) (kPtr + 34432#64) ks.clAux _
    (by rw [h19, ptr_add_ofNat])]
  ac_rfl

/-- Partition a raw `u32` scratch array `scr` (`scr.length ≥ 8864`) at `p` into the preserved
`256`-word prefix (`scr.take 256`) and `KittenMem (p + 1024#64)`. -/
theorem array_scratch_eq_kitten {p : BitVec 64} {scr : List (BitVec 32)}
    (hlen : 8864 ≤ scr.length) :
    array (t := i32) p scr =
      (array (t := i32) p (scr.take 256) ⋆
        KittenMem (p + 1024#64) (KittenState.ofSlab (scr.drop 256))) := by
  have hsh := KittenState.shapesOk_ofSlab (xs := scr.drop 256) (by simp; omega)
  rw [kittenMem_eq_array (p + 1024#64) hsh, KittenState.toSlab_ofSlab (by simp; omega)]
  have htk : (scr.take 256).length = 256 := List.length_take_of_le (by omega)
  have happ := array32_append_off p (p + 1024#64) (scr.take 256) (scr.drop 256)
    (by rw [htk])
  rw [List.take_append_drop] at happ
  exact happ

/-- Reassemble `scrHead ⋆ KittenMem (p + 1024#64) ks` (`scrHead.length = 256`) back into
`array (t := i32) p (scrHead ++ ks.toSlab)`. -/
theorem kitten_append_eq_array_scratch {p : BitVec 64} {scrHead : List (BitVec 32)}
    {acap : Nat} {ks : KittenState} (hh : scrHead.length = 256) (hsh : ks.ShapesOk acap) :
    (array (t := i32) p scrHead ⋆ KittenMem (p + 1024#64) ks) =
      array (t := i32) p (scrHead ++ ks.toSlab) := by
  rw [kittenMem_eq_array (p + 1024#64) hsh]
  symm
  exact array32_append_off p (p + 1024#64) scrHead ks.toSlab (by rw [hh])

/-- Remainder of `FullMem c s` outside `h->scratch_buf[256..)` (`scr.take 256` stays framed). -/
def FullKittenFrame (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
  FullScrMetaArrs c s.scratch ⋆
  array (t := i32) c.pDelayed s.scratch.delayed ⋆
  array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
  array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
  array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take 256) ⋆
  c.pad

theorem fullMem_eq_kittenFrame {c : FullCfg} {s : FullState}
    (hlen : 8864 ≤ s.scratch.scratch_buf.length) :
    FullMem c s =
      (FullKittenFrame c s ⋆
        KittenMem (c.pScratchBuf + 1024#64)
          (KittenState.ofSlab (s.scratch.scratch_buf.drop 256))) := by
  unfold FullMem FullScratchArrays FullScrDynArrs FullKittenFrame
  rw [array_scratch_eq_kitten hlen]
  ac_rfl

theorem fullKittenFrame_with_kittenSlab {c : FullCfg} {s : FullState}
    {ks' : KittenState} (h256 : 256 ≤ s.scratch.scratch_buf.length) :
    let scr' := s.scratch.scratch_buf.take 256 ++ ks'.toSlab
    FullKittenFrame c { s with scratch := { s.scratch with scratch_buf := scr' } } =
      FullKittenFrame c s := by
  intro scr'
  have htake : scr'.take 256 = s.scratch.scratch_buf.take 256 := by
    simp only [scr']
    rw [List.take_append_of_le_length (by simp; omega), List.take_take, Nat.min_self]
  unfold FullKittenFrame
  have hhdr : hdrTailWords c { s with scratch := { s.scratch with scratch_buf := scr' } } =
      hdrTailWords c s := rfl
  rw [hhdr, htake]; rfl

theorem fullMem_join_kitten {c : FullCfg} {s : FullState} {acap : Nat} {ks' : KittenState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (h256 : 256 ≤ s.scratch.scratch_buf.length) (hsh : ks'.ShapesOk acap)
    (hm : (FullKittenFrame c s ⋆ KittenMem (c.pScratchBuf + 1024#64) ks' ⋆ R) m) :
    let scr' := s.scratch.scratch_buf.take 256 ++ ks'.toSlab
    let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
    (FullMem c s' ⋆ R) m := by
  intro scr' s'
  have h8864 : 8864 ≤ scr'.length := by
    simp only [scr', List.length_append, List.length_take, KittenState.toSlab_length hsh]; omega
  rw [fullMem_eq_kittenFrame h8864]
  have hf := fullKittenFrame_with_kittenSlab (c := c) (s := s) (ks' := ks') h256
  dsimp only [s', scr']
  rw [hf]
  have hof : KittenState.ofSlab (scr'.drop 256) = ks' := by
    simp only [scr']
    rw [slab_drop_exact _ ks'.toSlab (by simp; omega)]
    exact KittenState.ofSlab_toSlab hsh
  rw [hof]
  exact sep_ac hm

theorem fullKittenFrame_fuel_load {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullKittenFrame c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 168) = some s.core.fuel := by
  have h1 : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆
       FullCoreArrays c s.core ⋆ FullScrByteArrs c s.scratch ⋆
       FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
       array (t := i32) c.pDelayed s.scratch.delayed ⋆
       array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
       array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
       array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take 256) ⋆ c.pad ⋆ R)) m := by
    unfold FullKittenFrame at hm; exact sep_ac hm
  have hload := loadVal_array64 (i := 17) (by rw [hdrTailWords_length]; decide) h1
  rwa [show c.hdr + 32 + BitVec.ofNat 64 (8 * 17) = c.hdr + 168 from
    ptr_add_ofNat c.hdr 32 136] at hload

theorem fullKittenFrame_fuel_store {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 64) (hm : (FullKittenFrame c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 168) ∧
      (FullKittenFrame c { s with core := { s.core with fuel := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 168) v) := by
  have h1 : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆
       FullCoreArrays c s.core ⋆ FullScrByteArrs c s.scratch ⋆
       FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
       array (t := i32) c.pDelayed s.scratch.delayed ⋆
       array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
       array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
       array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take 256) ⋆ c.pad ⋆ R)) m := by
    unfold FullKittenFrame at hm; exact sep_ac hm
  obtain ⟨hok, hst⟩ := store_array64 (i := 17) v (by rw [hdrTailWords_length]; decide) h1
  rw [show c.hdr + 32 + BitVec.ofNat 64 (8 * 17) = c.hdr + 168 from
    ptr_add_ofNat c.hdr 32 136] at hok hst
  refine ⟨hok, ?_⟩
  have hset : (hdrTailWords c s).set 17 v =
      hdrTailWords c { s with core := { s.core with fuel := v } } := by
    simp [hdrTailWords, hdrTailWords0, hdrTailWords1, hdrTailWords2, hdrTailWords3, List.set]
  rw [hset] at hst
  unfold FullKittenFrame
  exact sep_ac hst

theorem fullKittenFrame_scratch_cap_load {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullKittenFrame c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 928) = some (BitVec.ofNat 64 c.scratch_cap) := by
  have h1 : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆
       FullCoreArrays c s.core ⋆ FullScrByteArrs c s.scratch ⋆
       FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
       array (t := i32) c.pDelayed s.scratch.delayed ⋆
       array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
       array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
       array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take 256) ⋆ c.pad ⋆ R)) m := by
    unfold FullKittenFrame at hm; exact sep_ac hm
  have hload := loadVal_array64 (i := 112) (by rw [hdrTailWords_length]; decide) h1
  rw [show c.hdr + 32 + BitVec.ofNat 64 (8 * 112) = c.hdr + 928 from
    ptr_add_ofNat c.hdr 32 896] at hload
  simpa [hdrTailWords, hdrTailWords0, hdrTailWords1, hdrTailWords2, hdrTailWords3] using hload

theorem fullKittenFrame_scratch_buf_load {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullKittenFrame c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 920) = some c.pScratchBuf := by
  have h1 : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆
       FullCoreArrays c s.core ⋆ FullScrByteArrs c s.scratch ⋆
       FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
       array (t := i32) c.pDelayed s.scratch.delayed ⋆
       array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
       array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
       array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take 256) ⋆ c.pad ⋆ R)) m := by
    unfold FullKittenFrame at hm; exact sep_ac hm
  have hload := loadVal_array64 (i := 111) (by rw [hdrTailWords_length]; decide) h1
  rw [show c.hdr + 32 + BitVec.ofNat 64 (8 * 111) = c.hdr + 920 from
    ptr_add_ofNat c.hdr 32 888] at hload
  simpa [hdrTailWords, hdrTailWords0, hdrTailWords1, hdrTailWords2, hdrTailWords3] using hload

/-- Header scalar field tag for O(1) non-expanding `KittenState` updates. -/
inductive KHdrField where
  | nv | nc | orig_nc | lvl | prop | trl_end | unass | incons | failing | ante
  | qfirst | qlast | qsearch | qstamp | ticks | tick_lim | alen | acap
  | nassump | nunits | nres | nkl | nana | status | phase
  deriving DecidableEq

/-- Array field tag for O(1) non-expanding `KittenState` element updates. -/
inductive KArrField where
  | lvlArr | rsn | qprev | qnext | qstampArr | trl | flags | vals
  | assump | ana | kl | units | res | whead | wnext | wblit
  | clOff | clMeta | clAux | arena
  deriving DecidableEq

/-- Non-expanding update of a single scalar header word in `KittenState`. -/
def KittenState.putHdr (ks : KittenState) (f : KHdrField) (v : BitVec 32) : KittenState :=
  match f with
  | .nv => { ks with nv := v }
  | .nc => { ks with nc := v }
  | .orig_nc => { ks with orig_nc := v }
  | .lvl => { ks with lvl := v }
  | .prop => { ks with prop := v }
  | .trl_end => { ks with trl_end := v }
  | .unass => { ks with unass := v }
  | .incons => { ks with incons := v }
  | .failing => { ks with failing := v }
  | .ante => { ks with ante := v }
  | .qfirst => { ks with qfirst := v }
  | .qlast => { ks with qlast := v }
  | .qsearch => { ks with qsearch := v }
  | .qstamp => { ks with qstamp := v }
  | .ticks => { ks with ticks := v }
  | .tick_lim => { ks with tick_lim := v }
  | .alen => { ks with alen := v }
  | .acap => { ks with acap := v }
  | .nassump => { ks with nassump := v }
  | .nunits => { ks with nunits := v }
  | .nres => { ks with nres := v }
  | .nkl => { ks with nkl := v }
  | .nana => { ks with nana := v }
  | .status => { ks with status := v }
  | .phase => { ks with phase := v }

/-- Non-expanding update of a single array entry in `KittenState`. -/
def KittenState.putArr (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    KittenState :=
  match f with
  | .lvlArr => { ks with lvlArr := ks.lvlArr.set i v }
  | .rsn => { ks with rsn := ks.rsn.set i v }
  | .qprev => { ks with qprev := ks.qprev.set i v }
  | .qnext => { ks with qnext := ks.qnext.set i v }
  | .qstampArr => { ks with qstampArr := ks.qstampArr.set i v }
  | .trl => { ks with trl := ks.trl.set i v }
  | .flags => { ks with flags := ks.flags.set i v }
  | .vals => { ks with vals := ks.vals.set i v }
  | .assump => { ks with assump := ks.assump.set i v }
  | .ana => { ks with ana := ks.ana.set i v }
  | .kl => { ks with kl := ks.kl.set i v }
  | .units => { ks with units := ks.units.set i v }
  | .res => { ks with res := ks.res.set i v }
  | .whead => { ks with whead := ks.whead.set i v }
  | .wnext => { ks with wnext := ks.wnext.set i v }
  | .wblit => { ks with wblit := ks.wblit.set i v }
  | .clOff => { ks with clOff := ks.clOff.set i v }
  | .clMeta => { ks with clMeta := ks.clMeta.set i v }
  | .clAux => { ks with clAux := ks.clAux.set i v }
  | .arena => { ks with arena := ks.arena.set i v }

theorem KittenState.ShapesOk.putHdr {acap : Nat} {ks : KittenState}
    (h : ks.ShapesOk acap) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).ShapesOk acap := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20⟩
  cases f <;> exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20⟩

theorem KittenState.ShapesOk.putArr {acap : Nat} {ks : KittenState}
    (h : ks.ShapesOk acap) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).ShapesOk acap := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20⟩
  cases f <;> exact ⟨h0,
    by simpa [KittenState.putArr] using h1, by simpa [KittenState.putArr] using h2,
    by simpa [KittenState.putArr] using h3, by simpa [KittenState.putArr] using h4,
    by simpa [KittenState.putArr] using h5, by simpa [KittenState.putArr] using h6,
    by simpa [KittenState.putArr] using h7, by simpa [KittenState.putArr] using h8,
    by simpa [KittenState.putArr] using h9, by simpa [KittenState.putArr] using h10,
    by simpa [KittenState.putArr] using h11, by simpa [KittenState.putArr] using h12,
    by simpa [KittenState.putArr] using h13, by simpa [KittenState.putArr] using h14,
    by simpa [KittenState.putArr] using h15, by simpa [KittenState.putArr] using h16,
    by simpa [KittenState.putArr] using h17, by simpa [KittenState.putArr] using h18,
    by simpa [KittenState.putArr] using h19, by simpa [KittenState.putArr] using h20⟩

/-! ## 4. Strictly Scoped `KittenMemTactics` (`c0_load` / `c0_store`) -/

namespace KittenMemTactics

attribute [scoped bv_c0] bv32_lshr_1 bv32_and_1 bv32_xor_1 List.length_set Bool.false_eq_true

@[scoped bv_c0] theorem putArr_nv (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).nv = ks.nv := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_nc (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).nc = ks.nc := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_orig_nc (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).orig_nc = ks.orig_nc := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_lvl (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).lvl = ks.lvl := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_prop (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).prop = ks.prop := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_trl_end (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).trl_end = ks.trl_end := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_unass (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).unass = ks.unass := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_incons (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).incons = ks.incons := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_failing (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).failing = ks.failing := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_ante (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).ante = ks.ante := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_qfirst (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).qfirst = ks.qfirst := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_qlast (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).qlast = ks.qlast := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_qsearch (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).qsearch = ks.qsearch := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_qstamp (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).qstamp = ks.qstamp := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_ticks (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).ticks = ks.ticks := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_tick_lim (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).tick_lim = ks.tick_lim := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_alen (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).alen = ks.alen := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_acap (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).acap = ks.acap := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_nassump (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).nassump = ks.nassump := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_nunits (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).nunits = ks.nunits := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_nres (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).nres = ks.nres := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_nkl (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).nkl = ks.nkl := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_nana (ks : KittenState) (f : KArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).nana = ks.nana := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_status (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).status = ks.status := by cases f <;> rfl
@[scoped bv_c0] theorem putArr_phase (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).phase = ks.phase := by cases f <;> rfl

@[scoped bv_c0] theorem putHdr_lvlArr (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).lvlArr = ks.lvlArr := by cases f <;> rfl
@[scoped bv_c0] theorem putHdr_rsn (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).rsn = ks.rsn := by cases f <;> rfl
@[scoped bv_c0] theorem putHdr_qprev (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).qprev = ks.qprev := by cases f <;> rfl
@[scoped bv_c0] theorem putHdr_qnext (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).qnext = ks.qnext := by cases f <;> rfl
@[scoped bv_c0] theorem putHdr_qstampArr (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).qstampArr = ks.qstampArr := by cases f <;> rfl
@[scoped bv_c0] theorem putHdr_trl (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).trl = ks.trl := by cases f <;> rfl
@[scoped bv_c0] theorem putHdr_flags (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).flags = ks.flags := by cases f <;> rfl
@[scoped bv_c0] theorem putHdr_vals (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).vals = ks.vals := by cases f <;> rfl
@[scoped bv_c0] theorem putHdr_assump (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).assump = ks.assump := by cases f <;> rfl
@[scoped bv_c0] theorem putHdr_ana (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).ana = ks.ana := by cases f <;> rfl
@[scoped bv_c0] theorem putHdr_kl (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).kl = ks.kl := by cases f <;> rfl
@[scoped bv_c0] theorem putHdr_units (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).units = ks.units := by cases f <;> rfl
@[scoped bv_c0] theorem putHdr_res (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).res = ks.res := by cases f <;> rfl
@[scoped bv_c0] theorem putHdr_whead (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).whead = ks.whead := by cases f <;> rfl
@[scoped bv_c0] theorem putHdr_wnext (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).wnext = ks.wnext := by cases f <;> rfl
@[scoped bv_c0] theorem putHdr_wblit (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).wblit = ks.wblit := by cases f <;> rfl
@[scoped bv_c0] theorem putHdr_clOff (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).clOff = ks.clOff := by cases f <;> rfl
@[scoped bv_c0] theorem putHdr_clMeta (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).clMeta = ks.clMeta := by cases f <;> rfl
@[scoped bv_c0] theorem putHdr_clAux (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).clAux = ks.clAux := by cases f <;> rfl
@[scoped bv_c0] theorem putHdr_arena (ks : KittenState) (f : KHdrField) (v : BitVec 32) :
    (ks.putHdr f v).arena = ks.arena := by cases f <;> rfl

@[scoped bv_c0] theorem putArr_lvlArr_len (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).lvlArr.length = ks.lvlArr.length := by
  cases f <;> simp [KittenState.putArr]
@[scoped bv_c0] theorem putArr_rsn_len (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).rsn.length = ks.rsn.length := by
  cases f <;> simp [KittenState.putArr]
@[scoped bv_c0] theorem putArr_qprev_len (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).qprev.length = ks.qprev.length := by
  cases f <;> simp [KittenState.putArr]
@[scoped bv_c0] theorem putArr_qnext_len (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).qnext.length = ks.qnext.length := by
  cases f <;> simp [KittenState.putArr]
@[scoped bv_c0] theorem putArr_qstampArr_len (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).qstampArr.length = ks.qstampArr.length := by
  cases f <;> simp [KittenState.putArr]
@[scoped bv_c0] theorem putArr_trl_len (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).trl.length = ks.trl.length := by
  cases f <;> simp [KittenState.putArr]
@[scoped bv_c0] theorem putArr_flags_len (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).flags.length = ks.flags.length := by
  cases f <;> simp [KittenState.putArr]
@[scoped bv_c0] theorem putArr_vals_len (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).vals.length = ks.vals.length := by
  cases f <;> simp [KittenState.putArr]
@[scoped bv_c0] theorem putArr_assump_len (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).assump.length = ks.assump.length := by
  cases f <;> simp [KittenState.putArr]
@[scoped bv_c0] theorem putArr_ana_len (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).ana.length = ks.ana.length := by
  cases f <;> simp [KittenState.putArr]
@[scoped bv_c0] theorem putArr_kl_len (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).kl.length = ks.kl.length := by
  cases f <;> simp [KittenState.putArr]
@[scoped bv_c0] theorem putArr_units_len (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).units.length = ks.units.length := by
  cases f <;> simp [KittenState.putArr]
@[scoped bv_c0] theorem putArr_res_len (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).res.length = ks.res.length := by
  cases f <;> simp [KittenState.putArr]
@[scoped bv_c0] theorem putArr_whead_len (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).whead.length = ks.whead.length := by
  cases f <;> simp [KittenState.putArr]
@[scoped bv_c0] theorem putArr_wnext_len (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).wnext.length = ks.wnext.length := by
  cases f <;> simp [KittenState.putArr]
@[scoped bv_c0] theorem putArr_wblit_len (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).wblit.length = ks.wblit.length := by
  cases f <;> simp [KittenState.putArr]
@[scoped bv_c0] theorem putArr_clOff_len (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).clOff.length = ks.clOff.length := by
  cases f <;> simp [KittenState.putArr]
@[scoped bv_c0] theorem putArr_clMeta_len (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).clMeta.length = ks.clMeta.length := by
  cases f <;> simp [KittenState.putArr]
@[scoped bv_c0] theorem putArr_clAux_len (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).clAux.length = ks.clAux.length := by
  cases f <;> simp [KittenState.putArr]
@[scoped bv_c0] theorem putArr_arena_len (ks : KittenState) (f : KArrField) (i : Nat)
    (v : BitVec 32) : (ks.putArr f i v).arena.length = ks.arena.length := by
  cases f <;> simp [KittenState.putArr]

@[scoped c0_load] theorem load_fk_scratch_cap {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 928) = some (BitVec.ofNat 64 c.scratch_cap) :=
  FullArenaTactics.load_full_scratch_cap hm

@[scoped c0_load] theorem load_fkf_scratch_cap {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullKittenFrame c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 928) = some (BitVec.ofNat 64 c.scratch_cap) :=
  fullKittenFrame_scratch_cap_load hm

@[scoped c0_load] theorem load_fk_scratch_buf {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 920) = some c.pScratchBuf :=
  FullArenaTactics.load_full_scratch_buf_ptr hm

@[scoped c0_load] theorem load_fkf_scratch_buf {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullKittenFrame c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 920) = some c.pScratchBuf :=
  fullKittenFrame_scratch_buf_load hm

@[scoped c0_load] theorem load_fk_fuel {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 168) = some s.core.fuel :=
  FullArenaTactics.load_full_fuel hm

@[scoped c0_load] theorem load_fkf_fuel {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullKittenFrame c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 168) = some s.core.fuel :=
  fullKittenFrame_fuel_load hm

@[scoped c0_store] theorem store_fkf_fuel {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hm : (FullKittenFrame c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 168) ∧
      (FullKittenFrame c { s with core := { s.core with fuel := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 168) v) :=
  fullKittenFrame_fuel_store v hm

@[scoped c0_load] theorem load_hdrTail_scratch_buf {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ R) m) :
    loadVal m i64 (c.hdr + 920) = some c.pScratchBuf := by
  have hload := loadVal_array64 (i := 111) (by simp) hm
  rw [show c.hdr + 32 + BitVec.ofNat 64 (8 * 111) = c.hdr + 920 from
    ptr_add_ofNat c.hdr 32 888] at hload
  simpa [hdrTailWords, hdrTailWords0, hdrTailWords1, hdrTailWords2, hdrTailWords3] using hload

@[scoped c0_load] theorem load_arr32_z0 {a : BitVec 64} {xs : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array (t := i32) a xs ⋆ R) m) (hi : 0 < xs.length) :
    loadVal m i32 (a + BitVec.ofNat 64 0 * 4) = some (xs[0]'hi) := by
  rw [ptr_bv32_nat_mul4 a 0 (by decide)]
  exact loadVal_array (t := i32) (by decide) hi h

@[scoped c0_load] theorem load_arr32_z1 {a : BitVec 64} {xs : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array (t := i32) a xs ⋆ R) m) (hi : 1 < xs.length) :
    loadVal m i32 (a + BitVec.ofNat 64 1 * 4) = some (xs[1]'hi) := by
  rw [ptr_bv32_nat_mul4 a 1 (by decide)]
  exact loadVal_array (t := i32) (by decide) hi h

@[scoped c0_load] theorem load_arr32_hdr_u32 {a : BitVec 64} {i : BitVec 32}
    {xs : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array (t := i32) a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i32 (a + i.setWidth 64 * 4) = some (xs[i.toNat]'hi) := by
  rw [show (4 : BitVec 64) = 4#64 from rfl]
  exact c0_load_array32_u32 h hi

@[scoped c0_store] theorem store_arr32_hdr_u32 {a : BitVec 64} {i : BitVec 32}
    {xs : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32)
    (h : (array (t := i32) a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    storeOk m i32 (a + i.setWidth 64 * 4) ∧
      (array (t := i32) a (xs.set i.toNat v) ⋆ R) (storeMem m i32 (a + i.setWidth 64 * 4) v) := by
  rw [show (4 : BitVec 64) = 4#64 from rfl]
  exact c0_store_array32_u32 v h hi

theorem focus_kitten_hdr {kPtr : BitVec 64} {ks : KittenState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    (array (t := i32) kPtr (kittenHdrWords ks) ⋆ ((KittenTree kPtr ks).rest (kPath 0) ⋆ R)) m :=
  SepTree.focus (t := KittenTree kPtr ks) (kPath 0) hm

theorem unfocus_kitten_hdr {kPtr : BitVec 64} {ks ks' : KittenState} {hdr' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (heq : ((KittenTree kPtr ks).set (kPath 0) (array (t := i32) kPtr hdr')).eval =
      KittenMem kPtr ks')
    (hm : (array (t := i32) kPtr hdr' ⋆ ((KittenTree kPtr ks).rest (kPath 0) ⋆ R)) m) :
    (KittenMem kPtr ks' ⋆ R) m :=
  SepTree.unfocus_eq (t := KittenTree kPtr ks) (kPath 0) heq hm

private theorem kHdrGet {kPtr : BitVec 64} {ks : KittenState} {R : Mem 64 → Prop} {m : Mem 64}
    (idx : Nat) (hlt : idx < 32) (hi : idx < (kittenHdrWords ks).length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 idx * 4) =
      some ((kittenHdrWords ks)[idx]'hi) := by
  rw [ptr_bv32_nat_mul4 kPtr idx (by omega)]
  exact sepTree_arr_get (t := KittenTree kPtr ks) (p := kPath 0) rfl (by decide) hi hm

private theorem kHdrPut {kPtr : BitVec 64} {ks : KittenState} (ks' : KittenState)
    {R : Mem 64 → Prop} {m : Mem 64} (idx : Nat) (v : BitVec 32) (hlt : idx < 32)
    (hi : idx < (kittenHdrWords ks).length)
    (hset : (kittenHdrWords ks).set idx v = kittenHdrWords ks')
    (heq : ((KittenTree kPtr ks).set (kPath 0)
      (array (t := i32) kPtr (kittenHdrWords ks'))).eval = KittenMem kPtr ks')
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 idx * 4) ∧
      (KittenMem kPtr ks' ⋆ R) (storeMem m i32 (kPtr + BitVec.ofNat 64 idx * 4) v) := by
  rw [ptr_bv32_nat_mul4 kPtr idx (by omega)]
  exact sepTree_arr_put (t := KittenTree kPtr ks) (p := kPath 0) rfl (by decide) v hi
    (hset ▸ heq) hm

private theorem kArrGet {kPtr : BitVec 64} {ks : KittenState} (p : List Bool) (kOff : Nat)
    (off32 : BitVec 32) (off64 : BitVec 64) (xs : List (BitVec 32)) {R : Mem 64 → Prop}
    {m : Mem 64} (hk : kOff ≤ 8608) (h32 : off32 = BitVec.ofNat 32 kOff)
    (hoff : off64 = BitVec.ofNat 64 (4 * kOff))
    (hget : (KittenTree kPtr ks).get p = array (t := i32) (kPtr + off64) xs)
    {i : BitVec 32} (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < xs.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (off32 + i).setWidth 64 * 4) =
      some (xs[i.toNat]'hi) := by
  rw [ptr_kOff_bv32_mul4 kPtr kOff off32 hk h32 hlt, ← hoff]
  exact sepTree_arr_get (t := KittenTree kPtr ks) (p := p) hget (by decide) hi hm

private theorem kArrPut {kPtr : BitVec 64} {ks : KittenState} (p : List Bool) (kOff : Nat)
    (off32 : BitVec 32) (off64 : BitVec 64) (xs : List (BitVec 32)) (ks' : KittenState)
    {R : Mem 64 → Prop} {m : Mem 64} (hk : kOff ≤ 8608) (h32 : off32 = BitVec.ofNat 32 kOff)
    (hoff : off64 = BitVec.ofNat 64 (4 * kOff))
    (hget : (KittenTree kPtr ks).get p = array (t := i32) (kPtr + off64) xs)
    (v : BitVec 32) {i : BitVec 32} (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < xs.length)
    (heq : ((KittenTree kPtr ks).set p
      (array (t := i32) (kPtr + off64) (xs.set i.toNat v))).eval = KittenMem kPtr ks')
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (off32 + i).setWidth 64 * 4) ∧
      (KittenMem kPtr ks' ⋆ R)
        (storeMem m i32 (kPtr + (off32 + i).setWidth 64 * 4) v) := by
  rw [ptr_kOff_bv32_mul4 kPtr kOff off32 hk h32 hlt, ← hoff]
  exact sepTree_arr_put (t := KittenTree kPtr ks) (p := p) hget (by decide) v hi heq hm

section HdrAccessors
variable {kPtr : BitVec 64} {ks : KittenState} {R : Mem 64 → Prop} {m : Mem 64}

@[scoped c0_load] theorem load_kitten_nv (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 0 * 4) = some ks.nv :=
  kHdrGet 0 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_nv (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 0 * 4) ∧
      (KittenMem kPtr (ks.putHdr .nv v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 0 * 4) v) :=
  kHdrPut (ks.putHdr .nv v) 0 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_nc (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 1 * 4) = some ks.nc :=
  kHdrGet 1 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_nc (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 1 * 4) ∧
      (KittenMem kPtr (ks.putHdr .nc v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 1 * 4) v) :=
  kHdrPut (ks.putHdr .nc v) 1 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_orig_nc (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 2 * 4) = some ks.orig_nc :=
  kHdrGet 2 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_orig_nc (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 2 * 4) ∧
      (KittenMem kPtr (ks.putHdr .orig_nc v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 2 * 4) v) :=
  kHdrPut (ks.putHdr .orig_nc v) 2 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_lvl (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 3 * 4) = some ks.lvl :=
  kHdrGet 3 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_lvl (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 3 * 4) ∧
      (KittenMem kPtr (ks.putHdr .lvl v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 3 * 4) v) :=
  kHdrPut (ks.putHdr .lvl v) 3 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_prop (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 4 * 4) = some ks.prop :=
  kHdrGet 4 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_prop (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 4 * 4) ∧
      (KittenMem kPtr (ks.putHdr .prop v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 4 * 4) v) :=
  kHdrPut (ks.putHdr .prop v) 4 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_trl_end (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 5 * 4) = some ks.trl_end :=
  kHdrGet 5 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_trl_end (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 5 * 4) ∧
      (KittenMem kPtr (ks.putHdr .trl_end v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 5 * 4) v) :=
  kHdrPut (ks.putHdr .trl_end v) 5 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_unass (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 6 * 4) = some ks.unass :=
  kHdrGet 6 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_unass (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 6 * 4) ∧
      (KittenMem kPtr (ks.putHdr .unass v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 6 * 4) v) :=
  kHdrPut (ks.putHdr .unass v) 6 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_incons (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 7 * 4) = some ks.incons :=
  kHdrGet 7 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_incons (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 7 * 4) ∧
      (KittenMem kPtr (ks.putHdr .incons v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 7 * 4) v) :=
  kHdrPut (ks.putHdr .incons v) 7 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_failing (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 8 * 4) = some ks.failing :=
  kHdrGet 8 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_failing (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 8 * 4) ∧
      (KittenMem kPtr (ks.putHdr .failing v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 8 * 4) v) :=
  kHdrPut (ks.putHdr .failing v) 8 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_ante (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 9 * 4) = some ks.ante :=
  kHdrGet 9 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_ante (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 9 * 4) ∧
      (KittenMem kPtr (ks.putHdr .ante v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 9 * 4) v) :=
  kHdrPut (ks.putHdr .ante v) 9 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_qfirst (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 10 * 4) = some ks.qfirst :=
  kHdrGet 10 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_qfirst (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 10 * 4) ∧
      (KittenMem kPtr (ks.putHdr .qfirst v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 10 * 4) v) :=
  kHdrPut (ks.putHdr .qfirst v) 10 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_qlast (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 11 * 4) = some ks.qlast :=
  kHdrGet 11 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_qlast (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 11 * 4) ∧
      (KittenMem kPtr (ks.putHdr .qlast v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 11 * 4) v) :=
  kHdrPut (ks.putHdr .qlast v) 11 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_qsearch (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 12 * 4) = some ks.qsearch :=
  kHdrGet 12 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_qsearch (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 12 * 4) ∧
      (KittenMem kPtr (ks.putHdr .qsearch v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 12 * 4) v) :=
  kHdrPut (ks.putHdr .qsearch v) 12 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_qstamp (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 13 * 4) = some ks.qstamp :=
  kHdrGet 13 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_qstamp (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 13 * 4) ∧
      (KittenMem kPtr (ks.putHdr .qstamp v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 13 * 4) v) :=
  kHdrPut (ks.putHdr .qstamp v) 13 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_ticks (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 14 * 4) = some ks.ticks :=
  kHdrGet 14 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_ticks (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 14 * 4) ∧
      (KittenMem kPtr (ks.putHdr .ticks v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 14 * 4) v) :=
  kHdrPut (ks.putHdr .ticks v) 14 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_tick_lim (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 15 * 4) = some ks.tick_lim :=
  kHdrGet 15 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_tick_lim (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 15 * 4) ∧
      (KittenMem kPtr (ks.putHdr .tick_lim v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 15 * 4) v) :=
  kHdrPut (ks.putHdr .tick_lim v) 15 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_alen (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 16 * 4) = some ks.alen :=
  kHdrGet 16 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_alen (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 16 * 4) ∧
      (KittenMem kPtr (ks.putHdr .alen v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 16 * 4) v) :=
  kHdrPut (ks.putHdr .alen v) 16 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_acap (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 17 * 4) = some ks.acap :=
  kHdrGet 17 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_acap (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 17 * 4) ∧
      (KittenMem kPtr (ks.putHdr .acap v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 17 * 4) v) :=
  kHdrPut (ks.putHdr .acap v) 17 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_nassump (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 18 * 4) = some ks.nassump :=
  kHdrGet 18 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_nassump (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 18 * 4) ∧
      (KittenMem kPtr (ks.putHdr .nassump v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 18 * 4) v) :=
  kHdrPut (ks.putHdr .nassump v) 18 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_nunits (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 19 * 4) = some ks.nunits :=
  kHdrGet 19 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_nunits (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 19 * 4) ∧
      (KittenMem kPtr (ks.putHdr .nunits v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 19 * 4) v) :=
  kHdrPut (ks.putHdr .nunits v) 19 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_nres (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 20 * 4) = some ks.nres :=
  kHdrGet 20 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_nres (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 20 * 4) ∧
      (KittenMem kPtr (ks.putHdr .nres v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 20 * 4) v) :=
  kHdrPut (ks.putHdr .nres v) 20 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_nkl (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 21 * 4) = some ks.nkl :=
  kHdrGet 21 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_nkl (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 21 * 4) ∧
      (KittenMem kPtr (ks.putHdr .nkl v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 21 * 4) v) :=
  kHdrPut (ks.putHdr .nkl v) 21 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_nana (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 22 * 4) = some ks.nana :=
  kHdrGet 22 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_nana (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 22 * 4) ∧
      (KittenMem kPtr (ks.putHdr .nana v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 22 * 4) v) :=
  kHdrPut (ks.putHdr .nana v) 22 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_status (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 23 * 4) = some ks.status :=
  kHdrGet 23 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_status (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 23 * 4) ∧
      (KittenMem kPtr (ks.putHdr .status v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 23 * 4) v) :=
  kHdrPut (ks.putHdr .status v) 23 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

@[scoped c0_load] theorem load_kitten_phase (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 24 * 4) = some ks.phase :=
  kHdrGet 24 (by decide) (by simp [kittenHdrWords]) hm
@[scoped c0_store] theorem store_kitten_phase (v : BitVec 32) (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 24 * 4) ∧
      (KittenMem kPtr (ks.putHdr .phase v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 24 * 4) v) :=
  kHdrPut (ks.putHdr .phase v) 24 v (by decide) (by simp [kittenHdrWords])
    (by simp [kittenHdrWords, KittenState.putHdr])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putHdr]) hm

end HdrAccessors

section ArrAccessors
variable {kPtr : BitVec 64} {ks : KittenState} {R : Mem 64 → Prop} {m : Mem 64}

@[scoped c0_load] theorem load_kitten_lvlArr {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < ks.lvlArr.length) (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (32 + i).setWidth 64 * 4) = some (ks.lvlArr[i.toNat]'hi) :=
  kArrGet (kPath 1) 32 32 128#64 ks.lvlArr (by decide) rfl rfl
    (by simp only [KittenTree, kPath, SepTree.get]) hlt hi hm
@[scoped c0_store] theorem store_kitten_lvlArr (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < ks.lvlArr.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (32 + i).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .lvlArr i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (32 + i).setWidth 64 * 4) v) :=
  kArrPut (kPath 1) 32 32 128#64 ks.lvlArr (ks.putArr .lvlArr i.toNat v)
    (by decide) rfl rfl (by simp only [KittenTree, kPath, SepTree.get]) v hlt hi
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putArr]) hm

@[scoped c0_load] theorem load_kitten_rsn {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < ks.rsn.length) (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (160 + i).setWidth 64 * 4) = some (ks.rsn[i.toNat]'hi) :=
  kArrGet (kPath 2) 160 160 640#64 ks.rsn (by decide) rfl rfl
    (by simp only [KittenTree, kPath, SepTree.get]) hlt hi hm
@[scoped c0_store] theorem store_kitten_rsn (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < ks.rsn.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (160 + i).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .rsn i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (160 + i).setWidth 64 * 4) v) :=
  kArrPut (kPath 2) 160 160 640#64 ks.rsn (ks.putArr .rsn i.toNat v)
    (by decide) rfl rfl (by simp only [KittenTree, kPath, SepTree.get]) v hlt hi
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putArr]) hm

@[scoped c0_load] theorem load_kitten_qprev {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < ks.qprev.length) (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (288 + i).setWidth 64 * 4) = some (ks.qprev[i.toNat]'hi) :=
  kArrGet (kPath 3) 288 288 1152#64 ks.qprev (by decide) rfl rfl
    (by simp only [KittenTree, kPath, SepTree.get]) hlt hi hm
@[scoped c0_store] theorem store_kitten_qprev (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < ks.qprev.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (288 + i).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .qprev i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (288 + i).setWidth 64 * 4) v) :=
  kArrPut (kPath 3) 288 288 1152#64 ks.qprev (ks.putArr .qprev i.toNat v)
    (by decide) rfl rfl (by simp only [KittenTree, kPath, SepTree.get]) v hlt hi
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putArr]) hm

@[scoped c0_load] theorem load_kitten_qnext {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < ks.qnext.length) (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (416 + i).setWidth 64 * 4) = some (ks.qnext[i.toNat]'hi) :=
  kArrGet (kPath 4) 416 416 1664#64 ks.qnext (by decide) rfl rfl
    (by simp only [KittenTree, kPath, SepTree.get]) hlt hi hm
@[scoped c0_store] theorem store_kitten_qnext (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < ks.qnext.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (416 + i).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .qnext i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (416 + i).setWidth 64 * 4) v) :=
  kArrPut (kPath 4) 416 416 1664#64 ks.qnext (ks.putArr .qnext i.toNat v)
    (by decide) rfl rfl (by simp only [KittenTree, kPath, SepTree.get]) v hlt hi
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putArr]) hm

@[scoped c0_load] theorem load_kitten_qstampArr {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < ks.qstampArr.length) (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (544 + i).setWidth 64 * 4) =
      some (ks.qstampArr[i.toNat]'hi) :=
  kArrGet (kPath 5) 544 544 2176#64 ks.qstampArr (by decide) rfl rfl
    (by simp only [KittenTree, kPath, SepTree.get]) hlt hi hm
@[scoped c0_store] theorem store_kitten_qstampArr (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < ks.qstampArr.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (544 + i).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .qstampArr i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (544 + i).setWidth 64 * 4) v) :=
  kArrPut (kPath 5) 544 544 2176#64 ks.qstampArr
    (ks.putArr .qstampArr i.toNat v)
    (by decide) rfl rfl (by simp only [KittenTree, kPath, SepTree.get]) v hlt hi
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putArr]) hm

@[scoped c0_load] theorem load_kitten_trl {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < ks.trl.length) (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (672 + i).setWidth 64 * 4) = some (ks.trl[i.toNat]'hi) :=
  kArrGet (kPath 6) 672 672 2688#64 ks.trl (by decide) rfl rfl
    (by simp only [KittenTree, kPath, SepTree.get]) hlt hi hm
@[scoped c0_load] theorem load_kitten_trl_sub1 {te : BitVec 32} (hpos : 0 < te.toNat)
    (hlt : te.toNat - 1 < 2 ^ 28) (hi : te.toNat - 1 < ks.trl.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + ((672 + te) - 1).setWidth 64 * 4) =
      some (ks.trl[te.toNat - 1]'hi) := by
  have heq : ((672 : BitVec 32) + te) - 1 = 672 + (te - 1#32) := by bv_omega
  have hte1 : (te - 1#32).toNat = te.toNat - 1 := by bv_omega
  rw [heq]
  simpa [hte1] using kArrGet (kPath 6) 672 672 2688#64 ks.trl (i := te - 1#32) (by decide) rfl
    rfl (by simp only [KittenTree, kPath, SepTree.get])
    (by rw [hte1]; exact hlt) (by rw [hte1]; exact hi) hm
@[scoped c0_store] theorem store_kitten_trl (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < ks.trl.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (672 + i).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .trl i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (672 + i).setWidth 64 * 4) v) :=
  kArrPut (kPath 6) 672 672 2688#64 ks.trl (ks.putArr .trl i.toNat v)
    (by decide) rfl rfl (by simp only [KittenTree, kPath, SepTree.get]) v hlt hi
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putArr]) hm

@[scoped c0_load] theorem load_kitten_flags {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < ks.flags.length) (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (800 + i).setWidth 64 * 4) = some (ks.flags[i.toNat]'hi) :=
  kArrGet (kPath 7) 800 800 3200#64 ks.flags (by decide) rfl rfl
    (by simp only [KittenTree, kPath, SepTree.get]) hlt hi hm
@[scoped c0_store] theorem store_kitten_flags (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < ks.flags.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (800 + i).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .flags i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (800 + i).setWidth 64 * 4) v) :=
  kArrPut (kPath 7) 800 800 3200#64 ks.flags (ks.putArr .flags i.toNat v)
    (by decide) rfl rfl (by simp only [KittenTree, kPath, SepTree.get]) v hlt hi
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putArr]) hm

@[scoped c0_load] theorem load_kitten_vals {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < ks.vals.length) (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (928 + i).setWidth 64 * 4) = some (ks.vals[i.toNat]'hi) :=
  kArrGet (kPath 8) 928 928 3712#64 ks.vals (by decide) rfl rfl
    (by simp only [KittenTree, kPath, SepTree.get]) hlt hi hm
@[scoped c0_store] theorem store_kitten_vals (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < ks.vals.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (928 + i).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .vals i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (928 + i).setWidth 64 * 4) v) :=
  kArrPut (kPath 8) 928 928 3712#64 ks.vals (ks.putArr .vals i.toNat v)
    (by decide) rfl rfl (by simp only [KittenTree, kPath, SepTree.get]) v hlt hi
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putArr]) hm

@[scoped c0_load] theorem load_kitten_assump {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < ks.assump.length) (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (1184 + i).setWidth 64 * 4) = some (ks.assump[i.toNat]'hi) :=
  kArrGet (kPath 9) 1184 1184 4736#64 ks.assump (by decide) rfl rfl
    (by simp only [KittenTree, kPath, SepTree.get]) hlt hi hm
@[scoped c0_store] theorem store_kitten_assump (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < ks.assump.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (1184 + i).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .assump i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (1184 + i).setWidth 64 * 4) v) :=
  kArrPut (kPath 9) 1184 1184 4736#64 ks.assump (ks.putArr .assump i.toNat v)
    (by decide) rfl rfl (by simp only [KittenTree, kPath, SepTree.get]) v hlt hi
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putArr]) hm

@[scoped c0_load] theorem load_kitten_ana {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < ks.ana.length) (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (1312 + i).setWidth 64 * 4) = some (ks.ana[i.toNat]'hi) :=
  kArrGet (kPath 10) 1312 1312 5248#64 ks.ana (by decide) rfl rfl
    (by simp only [KittenTree, kPath, SepTree.get]) hlt hi hm
@[scoped c0_store] theorem store_kitten_ana (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < ks.ana.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (1312 + i).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .ana i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (1312 + i).setWidth 64 * 4) v) :=
  kArrPut (kPath 10) 1312 1312 5248#64 ks.ana (ks.putArr .ana i.toNat v)
    (by decide) rfl rfl (by simp only [KittenTree, kPath, SepTree.get]) v hlt hi
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putArr]) hm

@[scoped c0_load] theorem load_kitten_kl {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < ks.kl.length) (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (1440 + i).setWidth 64 * 4) = some (ks.kl[i.toNat]'hi) :=
  kArrGet (kPath 11) 1440 1440 5760#64 ks.kl (by decide) rfl rfl
    (by simp only [KittenTree, kPath, SepTree.get]) hlt hi hm
@[scoped c0_store] theorem store_kitten_kl (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < ks.kl.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (1440 + i).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .kl i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (1440 + i).setWidth 64 * 4) v) :=
  kArrPut (kPath 11) 1440 1440 5760#64 ks.kl (ks.putArr .kl i.toNat v)
    (by decide) rfl rfl (by simp only [KittenTree, kPath, SepTree.get]) v hlt hi
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putArr]) hm
@[scoped c0_load] theorem load_kitten_kl0 (hi : 0 < ks.kl.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 1440 * 4) = some (ks.kl[0]'hi) := by
  have h := load_kitten_kl (i := 0#32) (by decide) hi hm
  simpa [show ((1440 : BitVec 32) + 0#32).setWidth 64 = BitVec.ofNat 64 1440 from rfl] using h
@[scoped c0_store] theorem store_kitten_kl0 (v : BitVec 32) (hi : 0 < ks.kl.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 1440 * 4) ∧
      (KittenMem kPtr (ks.putArr .kl 0 v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 1440 * 4) v) := by
  have h := store_kitten_kl v (i := 0#32) (by decide) hi hm
  simpa [show ((1440 : BitVec 32) + 0#32).setWidth 64 = BitVec.ofNat 64 1440 from rfl] using h
@[scoped c0_load] theorem load_kitten_kl1 (hi : 1 < ks.kl.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 1441 * 4) = some (ks.kl[1]'hi) := by
  have h := load_kitten_kl (i := 1#32) (by decide) hi hm
  simpa [show ((1440 : BitVec 32) + 1#32).setWidth 64 = BitVec.ofNat 64 1441 from rfl] using h
@[scoped c0_store] theorem store_kitten_kl1 (v : BitVec 32) (hi : 1 < ks.kl.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 1441 * 4) ∧
      (KittenMem kPtr (ks.putArr .kl 1 v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 1441 * 4) v) := by
  have h := store_kitten_kl v (i := 1#32) (by decide) hi hm
  simpa [show ((1440 : BitVec 32) + 1#32).setWidth 64 = BitVec.ofNat 64 1441 from rfl] using h

@[scoped c0_load] theorem load_kitten_units {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < ks.units.length) (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (1568 + i).setWidth 64 * 4) = some (ks.units[i.toNat]'hi) :=
  kArrGet (kPath 12) 1568 1568 6272#64 ks.units (by decide) rfl rfl
    (by simp only [KittenTree, kPath, SepTree.get]) hlt hi hm
@[scoped c0_store] theorem store_kitten_units (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < ks.units.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (1568 + i).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .units i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (1568 + i).setWidth 64 * 4) v) :=
  kArrPut (kPath 12) 1568 1568 6272#64 ks.units (ks.putArr .units i.toNat v)
    (by decide) rfl rfl (by simp only [KittenTree, kPath, SepTree.get]) v hlt hi
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putArr]) hm

@[scoped c0_load] theorem load_kitten_res {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < ks.res.length) (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (1824 + i).setWidth 64 * 4) = some (ks.res[i.toNat]'hi) :=
  kArrGet (kPath 13) 1824 1824 7296#64 ks.res (by decide) rfl rfl
    (by simp only [KittenTree, kPath, SepTree.get]) hlt hi hm
@[scoped c0_store] theorem store_kitten_res (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < ks.res.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (1824 + i).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .res i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (1824 + i).setWidth 64 * 4) v) :=
  kArrPut (kPath 13) 1824 1824 7296#64 ks.res (ks.putArr .res i.toNat v)
    (by decide) rfl rfl (by simp only [KittenTree, kPath, SepTree.get]) v hlt hi
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putArr]) hm

@[scoped c0_load] theorem load_kitten_whead {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < ks.whead.length) (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (2080 + i).setWidth 64 * 4) = some (ks.whead[i.toNat]'hi) :=
  kArrGet (kPath 14) 2080 2080 8320#64 ks.whead (by decide) rfl rfl
    (by simp only [KittenTree, kPath, SepTree.get]) hlt hi hm
@[scoped c0_store] theorem store_kitten_whead (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < ks.whead.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (2080 + i).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .whead i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (2080 + i).setWidth 64 * 4) v) :=
  kArrPut (kPath 14) 2080 2080 8320#64 ks.whead (ks.putArr .whead i.toNat v)
    (by decide) rfl rfl (by simp only [KittenTree, kPath, SepTree.get]) v hlt hi
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putArr]) hm

@[scoped c0_load] theorem load_kitten_wnext {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < ks.wnext.length) (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (2336 + i).setWidth 64 * 4) = some (ks.wnext[i.toNat]'hi) :=
  kArrGet (kPath 15) 2336 2336 9344#64 ks.wnext (by decide) rfl rfl
    (by simp only [KittenTree, kPath, SepTree.get]) hlt hi hm
@[scoped c0_store] theorem store_kitten_wnext (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < ks.wnext.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (2336 + i).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .wnext i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (2336 + i).setWidth 64 * 4) v) :=
  kArrPut (kPath 15) 2336 2336 9344#64 ks.wnext (ks.putArr .wnext i.toNat v)
    (by decide) rfl rfl (by simp only [KittenTree, kPath, SepTree.get]) v hlt hi
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putArr]) hm

@[scoped c0_load] theorem load_kitten_wblit {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < ks.wblit.length) (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (4128 + i).setWidth 64 * 4) = some (ks.wblit[i.toNat]'hi) :=
  kArrGet (kPath 16) 4128 4128 16512#64 ks.wblit (by decide) rfl rfl
    (by simp only [KittenTree, kPath, SepTree.get]) hlt hi hm
@[scoped c0_store] theorem store_kitten_wblit (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < ks.wblit.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (4128 + i).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .wblit i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (4128 + i).setWidth 64 * 4) v) :=
  kArrPut (kPath 16) 4128 4128 16512#64 ks.wblit (ks.putArr .wblit i.toNat v)
    (by decide) rfl rfl (by simp only [KittenTree, kPath, SepTree.get]) v hlt hi
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putArr]) hm

@[scoped c0_load] theorem load_kitten_clOff {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < ks.clOff.length) (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (5920 + i).setWidth 64 * 4) = some (ks.clOff[i.toNat]'hi) :=
  kArrGet (kPath 17) 5920 5920 23680#64 ks.clOff (by decide) rfl rfl
    (by simp only [KittenTree, kPath, SepTree.get]) hlt hi hm
@[scoped c0_store] theorem store_kitten_clOff (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < ks.clOff.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (5920 + i).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .clOff i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (5920 + i).setWidth 64 * 4) v) :=
  kArrPut (kPath 17) 5920 5920 23680#64 ks.clOff (ks.putArr .clOff i.toNat v)
    (by decide) rfl rfl (by simp only [KittenTree, kPath, SepTree.get]) v hlt hi
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putArr]) hm

@[scoped c0_load] theorem load_kitten_clMeta {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < ks.clMeta.length) (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (6816 + i).setWidth 64 * 4) = some (ks.clMeta[i.toNat]'hi) :=
  kArrGet (kPath 18) 6816 6816 27264#64 ks.clMeta (by decide) rfl rfl
    (by simp only [KittenTree, kPath, SepTree.get]) hlt hi hm
@[scoped c0_store] theorem store_kitten_clMeta (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < ks.clMeta.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (6816 + i).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .clMeta i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (6816 + i).setWidth 64 * 4) v) :=
  kArrPut (kPath 18) 6816 6816 27264#64 ks.clMeta (ks.putArr .clMeta i.toNat v)
    (by decide) rfl rfl (by simp only [KittenTree, kPath, SepTree.get]) v hlt hi
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putArr]) hm

@[scoped c0_load] theorem load_kitten_clAux {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < ks.clAux.length) (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (7712 + i).setWidth 64 * 4) = some (ks.clAux[i.toNat]'hi) :=
  kArrGet (kPath 19) 7712 7712 30848#64 ks.clAux (by decide) rfl rfl
    (by simp only [KittenTree, kPath, SepTree.get]) hlt hi hm
@[scoped c0_store] theorem store_kitten_clAux (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < ks.clAux.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (7712 + i).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .clAux i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (7712 + i).setWidth 64 * 4) v) :=
  kArrPut (kPath 19) 7712 7712 30848#64 ks.clAux (ks.putArr .clAux i.toNat v)
    (by decide) rfl rfl (by simp only [KittenTree, kPath, SepTree.get]) v hlt hi
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putArr]) hm

@[scoped c0_load] theorem load_kitten_arena {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < ks.arena.length) (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (8608 + i).setWidth 64 * 4) = some (ks.arena[i.toNat]'hi) :=
  kArrGet (kPath 20) 8608 8608 34432#64 ks.arena (by decide) rfl rfl
    (by simp only [KittenTree, kPath, SepTree.get]) hlt hi hm
@[scoped c0_store] theorem store_kitten_arena (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < ks.arena.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (8608 + i).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .arena i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (8608 + i).setWidth 64 * 4) v) :=
  kArrPut (kPath 20) 8608 8608 34432#64 ks.arena (ks.putArr .arena i.toNat v)
    (by decide) rfl rfl (by simp only [KittenTree, kPath, SepTree.get]) v hlt hi
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval,
      kittenHdrWords, KittenState.putArr]) hm

@[scoped c0_load] theorem load_kitten_arena_off {off j : BitVec 32}
    (hwrap : off.toNat + j.toNat < 2 ^ 28) (hi : off.toNat + j.toNat < ks.arena.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + ((8608 + off) + j).setWidth 64 * 4) =
      some (ks.arena[off.toNat + j.toNat]'hi) := by
  have heq : ((8608 : BitVec 32) + off) + j = 8608 + (off + j) := BitVec.add_assoc _ _ _
  have hoj : (off + j).toNat = off.toNat + j.toNat := by bv_omega
  rw [heq]
  simpa [hoj] using load_kitten_arena (i := off + j) (by rw [hoj]; exact hwrap)
    (by rw [hoj]; exact hi) hm

@[scoped c0_store] theorem store_kitten_arena_off (v : BitVec 32) {off j : BitVec 32}
    (hwrap : off.toNat + j.toNat < 2 ^ 28) (hi : off.toNat + j.toNat < ks.arena.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + ((8608 + off) + j).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .arena (off.toNat + j.toNat) v) ⋆ R)
        (storeMem m i32 (kPtr + ((8608 + off) + j).setWidth 64 * 4) v) := by
  have heq : ((8608 : BitVec 32) + off) + j = 8608 + (off + j) := BitVec.add_assoc _ _ _
  have hoj : (off + j).toNat = off.toNat + j.toNat := by bv_omega
  rw [heq]
  simpa [hoj] using store_kitten_arena v (i := off + j) (by rw [hoj]; exact hwrap)
    (by rw [hoj]; exact hi) hm

@[scoped c0_load] theorem load_kitten_arena_off2 {off b c : BitVec 32}
    (hwrap : off.toNat + b.toNat + c.toNat < 2 ^ 28)
    (hi : off.toNat + b.toNat + c.toNat < ks.arena.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + (((8608 + off) + b) + c).setWidth 64 * 4) =
      some (ks.arena[off.toNat + b.toNat + c.toNat]'hi) := by
  have heq : (((8608 : BitVec 32) + off) + b) + c = 8608 + (off + b + c) := by bv_omega
  have hobc : (off + b + c).toNat = off.toNat + b.toNat + c.toNat := by bv_omega
  rw [heq]
  simpa [hobc] using load_kitten_arena (i := off + b + c) (by rw [hobc]; exact hwrap)
    (by rw [hobc]; exact hi) hm

@[scoped c0_store] theorem store_kitten_arena_off2 (v : BitVec 32) {off b c : BitVec 32}
    (hwrap : off.toNat + b.toNat + c.toNat < 2 ^ 28)
    (hi : off.toNat + b.toNat + c.toNat < ks.arena.length)
    (hm : (KittenMem kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + (((8608 + off) + b) + c).setWidth 64 * 4) ∧
      (KittenMem kPtr (ks.putArr .arena (off.toNat + b.toNat + c.toNat) v) ⋆ R)
        (storeMem m i32 (kPtr + (((8608 + off) + b) + c).setWidth 64 * 4) v) := by
  have heq : (((8608 : BitVec 32) + off) + b) + c = 8608 + (off + b + c) := by bv_omega
  have hobc : (off + b + c).toNat = off.toNat + b.toNat + c.toNat := by bv_omega
  rw [heq]
  simpa [hobc] using store_kitten_arena v (i := off + b + c) (by rw [hobc]; exact hwrap)
    (by rw [hobc]; exact hi) hm

end ArrAccessors

end KittenMemTactics

/-- `ShapesOk`-bundled `KittenMem` eliminating `ks.<arr>.length` from C0 load/store bounds
so `closeBoundFast`/`assumption` never triggers `O(46^d)` record eta-expansion. -/
def KittenMemA (kPtr : BitVec 64) (acap : Nat) (ks : KittenState) : Mem 64 → Prop :=
  fun m => KittenMem kPtr ks m ∧ ks.ShapesOk acap

theorem kittenMem_to_amem {kPtr : BitVec 64} {acap : Nat} {ks : KittenState}
    {R : Mem 64 → Prop} {m : Mem 64} (hsh : ks.ShapesOk acap) (hm : (KittenMem kPtr ks ⋆ R) m) :
    (KittenMemA kPtr acap ks ⋆ R) m := by
  rcases hm with ⟨m1, m2, h1, h2, hm1, hm2⟩
  exact ⟨m1, m2, h1, h2, ⟨hm1, hsh⟩, hm2⟩

theorem kittenMemA_to_mem {kPtr : BitVec 64} {acap : Nat} {ks : KittenState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    ks.ShapesOk acap ∧ (KittenMem kPtr ks ⋆ R) m := by
  rcases hm with ⟨m1, m2, h1, h2, ⟨hm1, hsh⟩, hm2⟩
  exact ⟨hsh, m1, m2, h1, h2, hm1, hm2⟩

private theorem kaHdrGet {kPtr : BitVec 64} {acap : Nat} {ks : KittenState} {R : Mem 64 → Prop}
    {m : Mem 64} {addr : BitVec 64} {v : BitVec 32}
    (hload : (KittenMem kPtr ks ⋆ R) m → loadVal m i32 addr = some v)
    (hm : (KittenMemA kPtr acap ks ⋆ R) m) : loadVal m i32 addr = some v :=
  hload (kittenMemA_to_mem hm).2

private theorem kaHdrPut {kPtr : BitVec 64} {acap : Nat} {ks : KittenState} {R : Mem 64 → Prop}
    {m : Mem 64} (f : KHdrField) (v : BitVec 32) {addr : BitVec 64}
    (hstore : (KittenMem kPtr ks ⋆ R) m →
      storeOk m i32 addr ∧ (KittenMem kPtr (ks.putHdr f v) ⋆ R) (storeMem m i32 addr v))
    (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 addr ∧
      (KittenMemA kPtr acap (ks.putHdr f v) ⋆ R) (storeMem m i32 addr v) := by
  obtain ⟨hsh, hm'⟩ := kittenMemA_to_mem hm
  obtain ⟨hok, hst⟩ := hstore hm'
  exact ⟨hok, kittenMem_to_amem (hsh.putHdr f v) hst⟩

private theorem kaArrGet {kPtr : BitVec 64} {acap : Nat} {ks : KittenState} {R : Mem 64 → Prop}
    {m : Mem 64} (n : Nat) (arr : List (BitVec 32)) (hlen : ks.ShapesOk acap → arr.length = n)
    {idx : Nat} {addr : BitVec 64} (hi : idx < n)
    (hload : ∀ (hi' : idx < arr.length), (KittenMem kPtr ks ⋆ R) m →
      loadVal m i32 addr = some (arr[idx]'hi'))
    (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 addr = some (arr[idx]?.getD 0#32) := by
  obtain ⟨hsh, hm'⟩ := kittenMemA_to_mem hm
  have h1 : idx < arr.length := by rw [hlen hsh]; exact hi
  rw [List.getElem?_eq_getElem h1, Option.getD_some]
  exact hload h1 hm'

private theorem kaArrPut {kPtr : BitVec 64} {acap : Nat} {ks : KittenState} {R : Mem 64 → Prop}
    {m : Mem 64} (f : KArrField) (n : Nat) (arr : List (BitVec 32))
    (hlen : ks.ShapesOk acap → arr.length = n) (idx : Nat) (v : BitVec 32) {addr : BitVec 64}
    (hi : idx < n)
    (hstore : ∀ (_hi' : idx < arr.length), (KittenMem kPtr ks ⋆ R) m →
      storeOk m i32 addr ∧ (KittenMem kPtr (ks.putArr f idx v) ⋆ R) (storeMem m i32 addr v))
    (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 addr ∧
      (KittenMemA kPtr acap (ks.putArr f idx v) ⋆ R) (storeMem m i32 addr v) := by
  obtain ⟨hsh, hm'⟩ := kittenMemA_to_mem hm
  have h1 : idx < arr.length := by rw [hlen hsh]; exact hi
  obtain ⟨hok, hst⟩ := hstore h1 hm'
  exact ⟨hok, kittenMem_to_amem (hsh.putArr f idx v) hst⟩

namespace KittenMemATactics

open KittenMemTactics

section HdrAccessorsA
variable {kPtr : BitVec 64} {acap : Nat} {ks : KittenState} {R : Mem 64 → Prop} {m : Mem 64}

@[scoped c0_load] theorem load_ka_nv (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 0 * 4) = some ks.nv := kaHdrGet load_kitten_nv hm
@[scoped c0_store] theorem store_ka_nv (v : BitVec 32) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 0 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .nv v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 0 * 4) v) := kaHdrPut .nv v (store_kitten_nv v) hm
@[scoped c0_load] theorem load_ka_nc (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 1 * 4) = some ks.nc := kaHdrGet load_kitten_nc hm
@[scoped c0_store] theorem store_ka_nc (v : BitVec 32) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 1 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .nc v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 1 * 4) v) := kaHdrPut .nc v (store_kitten_nc v) hm
@[scoped c0_load] theorem load_ka_orig_nc (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 2 * 4) = some ks.orig_nc :=
  kaHdrGet load_kitten_orig_nc hm
@[scoped c0_store] theorem store_ka_orig_nc (v : BitVec 32)
    (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 2 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .orig_nc v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 2 * 4) v) :=
  kaHdrPut .orig_nc v (store_kitten_orig_nc v) hm
@[scoped c0_load] theorem load_ka_lvl (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 3 * 4) = some ks.lvl := kaHdrGet load_kitten_lvl hm
@[scoped c0_store] theorem store_ka_lvl (v : BitVec 32) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 3 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .lvl v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 3 * 4) v) :=
  kaHdrPut .lvl v (store_kitten_lvl v) hm
@[scoped c0_load] theorem load_ka_prop (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 4 * 4) = some ks.prop := kaHdrGet load_kitten_prop hm
@[scoped c0_store] theorem store_ka_prop (v : BitVec 32) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 4 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .prop v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 4 * 4) v) :=
  kaHdrPut .prop v (store_kitten_prop v) hm
@[scoped c0_load] theorem load_ka_trl_end (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 5 * 4) = some ks.trl_end :=
  kaHdrGet load_kitten_trl_end hm
@[scoped c0_store] theorem store_ka_trl_end (v : BitVec 32)
    (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 5 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .trl_end v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 5 * 4) v) :=
  kaHdrPut .trl_end v (store_kitten_trl_end v) hm
@[scoped c0_load] theorem load_ka_unass (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 6 * 4) = some ks.unass := kaHdrGet load_kitten_unass hm
@[scoped c0_store] theorem store_ka_unass (v : BitVec 32) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 6 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .unass v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 6 * 4) v) :=
  kaHdrPut .unass v (store_kitten_unass v) hm
@[scoped c0_load] theorem load_ka_incons (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 7 * 4) = some ks.incons :=
  kaHdrGet load_kitten_incons hm
@[scoped c0_store] theorem store_ka_incons (v : BitVec 32) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 7 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .incons v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 7 * 4) v) :=
  kaHdrPut .incons v (store_kitten_incons v) hm
@[scoped c0_load] theorem load_ka_failing (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 8 * 4) = some ks.failing :=
  kaHdrGet load_kitten_failing hm
@[scoped c0_store] theorem store_ka_failing (v : BitVec 32)
    (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 8 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .failing v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 8 * 4) v) :=
  kaHdrPut .failing v (store_kitten_failing v) hm
@[scoped c0_load] theorem load_ka_ante (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 9 * 4) = some ks.ante := kaHdrGet load_kitten_ante hm
@[scoped c0_store] theorem store_ka_ante (v : BitVec 32) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 9 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .ante v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 9 * 4) v) :=
  kaHdrPut .ante v (store_kitten_ante v) hm
@[scoped c0_load] theorem load_ka_qfirst (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 10 * 4) = some ks.qfirst :=
  kaHdrGet load_kitten_qfirst hm
@[scoped c0_store] theorem store_ka_qfirst (v : BitVec 32) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 10 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .qfirst v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 10 * 4) v) :=
  kaHdrPut .qfirst v (store_kitten_qfirst v) hm
@[scoped c0_load] theorem load_ka_qlast (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 11 * 4) = some ks.qlast := kaHdrGet load_kitten_qlast hm
@[scoped c0_store] theorem store_ka_qlast (v : BitVec 32) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 11 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .qlast v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 11 * 4) v) :=
  kaHdrPut .qlast v (store_kitten_qlast v) hm
@[scoped c0_load] theorem load_ka_qsearch (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 12 * 4) = some ks.qsearch :=
  kaHdrGet load_kitten_qsearch hm
@[scoped c0_store] theorem store_ka_qsearch (v : BitVec 32)
    (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 12 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .qsearch v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 12 * 4) v) :=
  kaHdrPut .qsearch v (store_kitten_qsearch v) hm
@[scoped c0_load] theorem load_ka_qstamp (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 13 * 4) = some ks.qstamp :=
  kaHdrGet load_kitten_qstamp hm
@[scoped c0_store] theorem store_ka_qstamp (v : BitVec 32) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 13 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .qstamp v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 13 * 4) v) :=
  kaHdrPut .qstamp v (store_kitten_qstamp v) hm
@[scoped c0_load] theorem load_ka_ticks (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 14 * 4) = some ks.ticks := kaHdrGet load_kitten_ticks hm
@[scoped c0_store] theorem store_ka_ticks (v : BitVec 32) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 14 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .ticks v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 14 * 4) v) :=
  kaHdrPut .ticks v (store_kitten_ticks v) hm
@[scoped c0_load] theorem load_ka_tick_lim (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 15 * 4) = some ks.tick_lim :=
  kaHdrGet load_kitten_tick_lim hm
@[scoped c0_store] theorem store_ka_tick_lim (v : BitVec 32)
    (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 15 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .tick_lim v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 15 * 4) v) :=
  kaHdrPut .tick_lim v (store_kitten_tick_lim v) hm
@[scoped c0_load] theorem load_ka_alen (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 16 * 4) = some ks.alen := kaHdrGet load_kitten_alen hm
@[scoped c0_store] theorem store_ka_alen (v : BitVec 32) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 16 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .alen v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 16 * 4) v) :=
  kaHdrPut .alen v (store_kitten_alen v) hm
@[scoped c0_load] theorem load_ka_acap (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 17 * 4) = some ks.acap := kaHdrGet load_kitten_acap hm
@[scoped c0_store] theorem store_ka_acap (v : BitVec 32) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 17 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .acap v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 17 * 4) v) :=
  kaHdrPut .acap v (store_kitten_acap v) hm
@[scoped c0_load] theorem load_ka_nassump (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 18 * 4) = some ks.nassump :=
  kaHdrGet load_kitten_nassump hm
@[scoped c0_store] theorem store_ka_nassump (v : BitVec 32)
    (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 18 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .nassump v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 18 * 4) v) :=
  kaHdrPut .nassump v (store_kitten_nassump v) hm
@[scoped c0_load] theorem load_ka_nunits (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 19 * 4) = some ks.nunits :=
  kaHdrGet load_kitten_nunits hm
@[scoped c0_store] theorem store_ka_nunits (v : BitVec 32) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 19 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .nunits v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 19 * 4) v) :=
  kaHdrPut .nunits v (store_kitten_nunits v) hm
@[scoped c0_load] theorem load_ka_nres (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 20 * 4) = some ks.nres := kaHdrGet load_kitten_nres hm
@[scoped c0_store] theorem store_ka_nres (v : BitVec 32) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 20 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .nres v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 20 * 4) v) :=
  kaHdrPut .nres v (store_kitten_nres v) hm
@[scoped c0_load] theorem load_ka_nkl (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 21 * 4) = some ks.nkl := kaHdrGet load_kitten_nkl hm
@[scoped c0_store] theorem store_ka_nkl (v : BitVec 32) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 21 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .nkl v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 21 * 4) v) :=
  kaHdrPut .nkl v (store_kitten_nkl v) hm
@[scoped c0_load] theorem load_ka_nana (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 22 * 4) = some ks.nana := kaHdrGet load_kitten_nana hm
@[scoped c0_store] theorem store_ka_nana (v : BitVec 32) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 22 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .nana v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 22 * 4) v) :=
  kaHdrPut .nana v (store_kitten_nana v) hm
@[scoped c0_load] theorem load_ka_status (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 23 * 4) = some ks.status :=
  kaHdrGet load_kitten_status hm
@[scoped c0_store] theorem store_ka_status (v : BitVec 32) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 23 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .status v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 23 * 4) v) :=
  kaHdrPut .status v (store_kitten_status v) hm
@[scoped c0_load] theorem load_ka_phase (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 24 * 4) = some ks.phase := kaHdrGet load_kitten_phase hm
@[scoped c0_store] theorem store_ka_phase (v : BitVec 32) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 24 * 4) ∧
      (KittenMemA kPtr acap (ks.putHdr .phase v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 24 * 4) v) :=
  kaHdrPut .phase v (store_kitten_phase v) hm

end HdrAccessorsA

section ArrAccessorsA
variable {kPtr : BitVec 64} {acap : Nat} {ks : KittenState} {R : Mem 64 → Prop} {m : Mem 64}

@[scoped c0_load] theorem load_ka_lvlArr {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < 128) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (32 + i).setWidth 64 * 4) = some (ks.lvlArr[i.toNat]?.getD 0#32) :=
  kaArrGet 128 ks.lvlArr (fun h => h.lvlArr_len) hi (load_kitten_lvlArr hlt) hm
@[scoped c0_store] theorem store_ka_lvlArr (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < 128) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (32 + i).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .lvlArr i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (32 + i).setWidth 64 * 4) v) :=
  kaArrPut .lvlArr 128 ks.lvlArr (fun h => h.lvlArr_len) i.toNat v hi
    (store_kitten_lvlArr v hlt) hm

@[scoped c0_load] theorem load_ka_rsn {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < 128) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (160 + i).setWidth 64 * 4) = some (ks.rsn[i.toNat]?.getD 0#32) :=
  kaArrGet 128 ks.rsn (fun h => h.rsn_len) hi (load_kitten_rsn hlt) hm
@[scoped c0_store] theorem store_ka_rsn (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < 128) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (160 + i).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .rsn i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (160 + i).setWidth 64 * 4) v) :=
  kaArrPut .rsn 128 ks.rsn (fun h => h.rsn_len) i.toNat v hi (store_kitten_rsn v hlt) hm

@[scoped c0_load] theorem load_ka_qprev {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < 128) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (288 + i).setWidth 64 * 4) = some (ks.qprev[i.toNat]?.getD 0#32) :=
  kaArrGet 128 ks.qprev (fun h => h.qprev_len) hi (load_kitten_qprev hlt) hm
@[scoped c0_store] theorem store_ka_qprev (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < 128) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (288 + i).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .qprev i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (288 + i).setWidth 64 * 4) v) :=
  kaArrPut .qprev 128 ks.qprev (fun h => h.qprev_len) i.toNat v hi (store_kitten_qprev v hlt) hm

@[scoped c0_load] theorem load_ka_qnext {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < 128) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (416 + i).setWidth 64 * 4) = some (ks.qnext[i.toNat]?.getD 0#32) :=
  kaArrGet 128 ks.qnext (fun h => h.qnext_len) hi (load_kitten_qnext hlt) hm
@[scoped c0_store] theorem store_ka_qnext (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < 128) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (416 + i).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .qnext i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (416 + i).setWidth 64 * 4) v) :=
  kaArrPut .qnext 128 ks.qnext (fun h => h.qnext_len) i.toNat v hi (store_kitten_qnext v hlt) hm

@[scoped c0_load] theorem load_ka_qstampArr {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < 128) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (544 + i).setWidth 64 * 4) = some (ks.qstampArr[i.toNat]?.getD 0#32) :=
  kaArrGet 128 ks.qstampArr (fun h => h.qstampArr_len) hi (load_kitten_qstampArr hlt) hm
@[scoped c0_store] theorem store_ka_qstampArr (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < 128) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (544 + i).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .qstampArr i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (544 + i).setWidth 64 * 4) v) :=
  kaArrPut .qstampArr 128 ks.qstampArr (fun h => h.qstampArr_len) i.toNat v hi
    (store_kitten_qstampArr v hlt) hm

@[scoped c0_load] theorem load_ka_trl {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < 128) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (672 + i).setWidth 64 * 4) = some (ks.trl[i.toNat]?.getD 0#32) :=
  kaArrGet 128 ks.trl (fun h => h.trl_len) hi (load_kitten_trl hlt) hm
@[scoped c0_load] theorem load_ka_trl_sub1 {te : BitVec 32} (hpos : 0 < te.toNat)
    (hlt : te.toNat - 1 < 2 ^ 28) (hi : te.toNat - 1 < 128)
    (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + ((672 + te) - 1).setWidth 64 * 4) =
      some (ks.trl[te.toNat - 1]?.getD 0#32) :=
  kaArrGet 128 ks.trl (fun h => h.trl_len) hi (load_kitten_trl_sub1 hpos hlt) hm
@[scoped c0_store] theorem store_ka_trl (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < 128) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (672 + i).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .trl i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (672 + i).setWidth 64 * 4) v) :=
  kaArrPut .trl 128 ks.trl (fun h => h.trl_len) i.toNat v hi (store_kitten_trl v hlt) hm

@[scoped c0_load] theorem load_ka_flags {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < 128) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (800 + i).setWidth 64 * 4) = some (ks.flags[i.toNat]?.getD 0#32) :=
  kaArrGet 128 ks.flags (fun h => h.flags_len) hi (load_kitten_flags hlt) hm
@[scoped c0_store] theorem store_ka_flags (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < 128) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (800 + i).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .flags i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (800 + i).setWidth 64 * 4) v) :=
  kaArrPut .flags 128 ks.flags (fun h => h.flags_len) i.toNat v hi (store_kitten_flags v hlt) hm

@[scoped c0_load] theorem load_ka_vals {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < 256) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (928 + i).setWidth 64 * 4) = some (ks.vals[i.toNat]?.getD 0#32) :=
  kaArrGet 256 ks.vals (fun h => h.vals_len) hi (load_kitten_vals hlt) hm
@[scoped c0_store] theorem store_ka_vals (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < 256) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (928 + i).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .vals i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (928 + i).setWidth 64 * 4) v) :=
  kaArrPut .vals 256 ks.vals (fun h => h.vals_len) i.toNat v hi (store_kitten_vals v hlt) hm

@[scoped c0_load] theorem load_ka_assump {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < 128) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (1184 + i).setWidth 64 * 4) = some (ks.assump[i.toNat]?.getD 0#32) :=
  kaArrGet 128 ks.assump (fun h => h.assump_len) hi (load_kitten_assump hlt) hm
@[scoped c0_store] theorem store_ka_assump (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < 128) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (1184 + i).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .assump i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (1184 + i).setWidth 64 * 4) v) :=
  kaArrPut .assump 128 ks.assump (fun h => h.assump_len) i.toNat v hi
    (store_kitten_assump v hlt) hm

@[scoped c0_load] theorem load_ka_ana {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < 128) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (1312 + i).setWidth 64 * 4) = some (ks.ana[i.toNat]?.getD 0#32) :=
  kaArrGet 128 ks.ana (fun h => h.ana_len) hi (load_kitten_ana hlt) hm
@[scoped c0_store] theorem store_ka_ana (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < 128) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (1312 + i).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .ana i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (1312 + i).setWidth 64 * 4) v) :=
  kaArrPut .ana 128 ks.ana (fun h => h.ana_len) i.toNat v hi (store_kitten_ana v hlt) hm

@[scoped c0_load] theorem load_ka_kl {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < 128) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (1440 + i).setWidth 64 * 4) = some (ks.kl[i.toNat]?.getD 0#32) :=
  kaArrGet 128 ks.kl (fun h => h.kl_len) hi (load_kitten_kl hlt) hm
@[scoped c0_store] theorem store_ka_kl (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < 128) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (1440 + i).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .kl i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (1440 + i).setWidth 64 * 4) v) :=
  kaArrPut .kl 128 ks.kl (fun h => h.kl_len) i.toNat v hi (store_kitten_kl v hlt) hm
@[scoped c0_load] theorem load_ka_kl0 (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 1440 * 4) = some (ks.kl[0]?.getD 0#32) :=
  kaArrGet 128 ks.kl (fun h => h.kl_len) (by decide) load_kitten_kl0 hm
@[scoped c0_store] theorem store_ka_kl0 (v : BitVec 32) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 1440 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .kl 0 v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 1440 * 4) v) :=
  kaArrPut .kl 128 ks.kl (fun h => h.kl_len) 0 v (by decide) (store_kitten_kl0 v) hm
@[scoped c0_load] theorem load_ka_kl1 (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 1441 * 4) = some (ks.kl[1]?.getD 0#32) :=
  kaArrGet 128 ks.kl (fun h => h.kl_len) (by decide) load_kitten_kl1 hm
@[scoped c0_store] theorem store_ka_kl1 (v : BitVec 32) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 1441 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .kl 1 v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 1441 * 4) v) :=
  kaArrPut .kl 128 ks.kl (fun h => h.kl_len) 1 v (by decide) (store_kitten_kl1 v) hm

@[scoped c0_load] theorem load_ka_units {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < 256) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (1568 + i).setWidth 64 * 4) = some (ks.units[i.toNat]?.getD 0#32) :=
  kaArrGet 256 ks.units (fun h => h.units_len) hi (load_kitten_units hlt) hm
@[scoped c0_store] theorem store_ka_units (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < 256) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (1568 + i).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .units i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (1568 + i).setWidth 64 * 4) v) :=
  kaArrPut .units 256 ks.units (fun h => h.units_len) i.toNat v hi (store_kitten_units v hlt) hm

@[scoped c0_load] theorem load_ka_res {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < 256) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (1824 + i).setWidth 64 * 4) = some (ks.res[i.toNat]?.getD 0#32) :=
  kaArrGet 256 ks.res (fun h => h.res_len) hi (load_kitten_res hlt) hm
@[scoped c0_store] theorem store_ka_res (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < 256) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (1824 + i).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .res i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (1824 + i).setWidth 64 * 4) v) :=
  kaArrPut .res 256 ks.res (fun h => h.res_len) i.toNat v hi (store_kitten_res v hlt) hm

@[scoped c0_load] theorem load_ka_whead {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < 256) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (2080 + i).setWidth 64 * 4) = some (ks.whead[i.toNat]?.getD 0#32) :=
  kaArrGet 256 ks.whead (fun h => h.whead_len) hi (load_kitten_whead hlt) hm
@[scoped c0_store] theorem store_ka_whead (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < 256) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (2080 + i).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .whead i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (2080 + i).setWidth 64 * 4) v) :=
  kaArrPut .whead 256 ks.whead (fun h => h.whead_len) i.toNat v hi (store_kitten_whead v hlt) hm

@[scoped c0_load] theorem load_ka_wnext {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < 1792) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (2336 + i).setWidth 64 * 4) = some (ks.wnext[i.toNat]?.getD 0#32) :=
  kaArrGet 1792 ks.wnext (fun h => h.wnext_len) hi (load_kitten_wnext hlt) hm
@[scoped c0_store] theorem store_ka_wnext (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < 1792) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (2336 + i).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .wnext i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (2336 + i).setWidth 64 * 4) v) :=
  kaArrPut .wnext 1792 ks.wnext (fun h => h.wnext_len) i.toNat v hi (store_kitten_wnext v hlt) hm

@[scoped c0_load] theorem load_ka_wblit {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < 1792) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (4128 + i).setWidth 64 * 4) = some (ks.wblit[i.toNat]?.getD 0#32) :=
  kaArrGet 1792 ks.wblit (fun h => h.wblit_len) hi (load_kitten_wblit hlt) hm
@[scoped c0_store] theorem store_ka_wblit (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < 1792) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (4128 + i).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .wblit i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (4128 + i).setWidth 64 * 4) v) :=
  kaArrPut .wblit 1792 ks.wblit (fun h => h.wblit_len) i.toNat v hi (store_kitten_wblit v hlt) hm

@[scoped c0_load] theorem load_ka_clOff {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < 896) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (5920 + i).setWidth 64 * 4) = some (ks.clOff[i.toNat]?.getD 0#32) :=
  kaArrGet 896 ks.clOff (fun h => h.clOff_len) hi (load_kitten_clOff hlt) hm
@[scoped c0_store] theorem store_ka_clOff (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < 896) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (5920 + i).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .clOff i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (5920 + i).setWidth 64 * 4) v) :=
  kaArrPut .clOff 896 ks.clOff (fun h => h.clOff_len) i.toNat v hi (store_kitten_clOff v hlt) hm

@[scoped c0_load] theorem load_ka_clMeta {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < 896) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (6816 + i).setWidth 64 * 4) = some (ks.clMeta[i.toNat]?.getD 0#32) :=
  kaArrGet 896 ks.clMeta (fun h => h.clMeta_len) hi (load_kitten_clMeta hlt) hm
@[scoped c0_store] theorem store_ka_clMeta (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < 896) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (6816 + i).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .clMeta i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (6816 + i).setWidth 64 * 4) v) :=
  kaArrPut .clMeta 896 ks.clMeta (fun h => h.clMeta_len) i.toNat v hi (store_kitten_clMeta v hlt) hm

@[scoped c0_load] theorem load_ka_clAux {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < 896) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (7712 + i).setWidth 64 * 4) = some (ks.clAux[i.toNat]?.getD 0#32) :=
  kaArrGet 896 ks.clAux (fun h => h.clAux_len) hi (load_kitten_clAux hlt) hm
@[scoped c0_store] theorem store_ka_clAux (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < 896) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (7712 + i).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .clAux i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (7712 + i).setWidth 64 * 4) v) :=
  kaArrPut .clAux 896 ks.clAux (fun h => h.clAux_len) i.toNat v hi (store_kitten_clAux v hlt) hm

@[scoped c0_load] theorem load_ka_arena {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < acap) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (8608 + i).setWidth 64 * 4) = some (ks.arena[i.toNat]?.getD 0#32) :=
  kaArrGet acap ks.arena (fun h => h.arena_len) hi (load_kitten_arena hlt) hm
@[scoped c0_store] theorem store_ka_arena (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < acap) (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (8608 + i).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .arena i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (8608 + i).setWidth 64 * 4) v) :=
  kaArrPut .arena acap ks.arena (fun h => h.arena_len) i.toNat v hi (store_kitten_arena v hlt) hm
@[scoped c0_load] theorem load_ka_arena_off {off j : BitVec 32}
    (hwrap : off.toNat + j.toNat < 2 ^ 28) (hi : off.toNat + j.toNat < acap)
    (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + ((8608 + off) + j).setWidth 64 * 4) =
      some (ks.arena[off.toNat + j.toNat]?.getD 0#32) :=
  kaArrGet acap ks.arena (fun h => h.arena_len) hi (load_kitten_arena_off hwrap) hm
@[scoped c0_store] theorem store_ka_arena_off (v : BitVec 32) {off j : BitVec 32}
    (hwrap : off.toNat + j.toNat < 2 ^ 28) (hi : off.toNat + j.toNat < acap)
    (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + ((8608 + off) + j).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .arena (off.toNat + j.toNat) v) ⋆ R)
        (storeMem m i32 (kPtr + ((8608 + off) + j).setWidth 64 * 4) v) :=
  kaArrPut .arena acap ks.arena (fun h => h.arena_len) (off.toNat + j.toNat) v hi
    (store_kitten_arena_off v hwrap) hm
@[scoped c0_load] theorem load_ka_arena_off2 {off b c : BitVec 32}
    (hwrap : off.toNat + b.toNat + c.toNat < 2 ^ 28) (hi : off.toNat + b.toNat + c.toNat < acap)
    (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (((8608 + off) + b) + c).setWidth 64 * 4) =
      some (ks.arena[off.toNat + b.toNat + c.toNat]?.getD 0#32) :=
  kaArrGet acap ks.arena (fun h => h.arena_len) hi (load_kitten_arena_off2 hwrap) hm
@[scoped c0_store] theorem store_ka_arena_off2 (v : BitVec 32) {off b c : BitVec 32}
    (hwrap : off.toNat + b.toNat + c.toNat < 2 ^ 28) (hi : off.toNat + b.toNat + c.toNat < acap)
    (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (((8608 + off) + b) + c).setWidth 64 * 4) ∧
      (KittenMemA kPtr acap (ks.putArr .arena (off.toNat + b.toNat + c.toNat) v) ⋆ R)
        (storeMem m i32 (kPtr + (((8608 + off) + b) + c).setWidth 64 * 4) v) :=
  kaArrPut .arena acap ks.arena (fun h => h.arena_len) (off.toNat + b.toNat + c.toNat) v hi
    (store_kitten_arena_off2 v hwrap) hm

end ArrAccessorsA

end KittenMemATactics

/-- Direct frame conversion for `full_kitten_add_clause` entry (`array` -> `KittenMemA`). -/
theorem fullAddClause_mem_to_ka {c : FullCfg} {s : FullState} {scr xs : List (BitVec 32)}
    {litsPtr : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64} {acap : Nat} {ks : KittenState}
    (h8864 : 8864 ≤ scr.length) (hsh : ks.ShapesOk acap)
    (hof : KittenState.ofSlab (scr.drop 256) = ks)
    (hm : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      array (t := i32) c.pScratchBuf scr ⋆ array (t := i32) litsPtr xs ⋆ R) m) :
    (KittenMemA (c.pScratchBuf + BitVec.ofNat 64 256 * 4) acap ks ⋆
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
        (array (t := i32) litsPtr xs ⋆
          (array (t := i32) c.pScratchBuf (scr.take 256) ⋆ R)))) m := by
  rw [array_scratch_eq_kitten (p := c.pScratchBuf) (scr := scr) h8864, hof] at hm
  have hm1 : (KittenMem (c.pScratchBuf + BitVec.ofNat 64 256 * 4) ks ⋆
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
        (array (t := i32) litsPtr xs ⋆
          (array (t := i32) c.pScratchBuf (scr.take 256) ⋆ R)))) m := by
    rw [kPtr_base_eq]; exact sep_ac hm
  exact kittenMem_to_amem hsh hm1

/-- Direct frame conversion for `full_kitten_add_clause` exit (`KittenMemA` -> `array`). -/
theorem fullAddClause_ka_to_mem {c : FullCfg} {s : FullState} {scr xs : List (BitVec 32)}
    {litsPtr : BitVec 64} {R : Mem 64 → Prop} {m' : Mem 64} {acap : Nat} {ks' : KittenState}
    (h256 : 256 ≤ scr.length) (hsh' : ks'.ShapesOk acap)
    (hm' : (KittenMemA (c.pScratchBuf + BitVec.ofNat 64 256 * 4) acap ks' ⋆
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
        (array (t := i32) litsPtr xs ⋆
          (array (t := i32) c.pScratchBuf (scr.take 256) ⋆ R)))) m') :
    let scr' := scr.take 256 ++ ks'.toSlab
    let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
    (array64 (c.hdr + 32) (hdrTailWords c s') ⋆
      array (t := i32) c.pScratchBuf scr' ⋆ array (t := i32) litsPtr xs ⋆ R) m' := by
  intro scr' s'
  obtain ⟨_, hm0⟩ := kittenMemA_to_mem hm'
  have htk : (scr.take 256).length = 256 := List.length_take_of_le h256
  have hm1 : (array64 (c.hdr + 32) (hdrTailWords c s') ⋆
      ((array (t := i32) c.pScratchBuf (scr.take 256) ⋆
        KittenMem (c.pScratchBuf + 1024#64) ks') ⋆
      (array (t := i32) litsPtr xs ⋆ R))) m' := by
    have hhdr : hdrTailWords c s' = hdrTailWords c s := rfl
    rw [hhdr]; rw [kPtr_base_eq] at hm0; exact sep_ac hm0
  rw [kitten_append_eq_array_scratch (p := c.pScratchBuf) htk hsh'] at hm1
  exact sep_ac hm1

end LeanQbe.T.Examples.Kissat.Full
