module

public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave-4E (`FullM7BveGates`) Proofs — Part 4a (`K6` Micro-Solver & Core)

M1-clean proof module (`public section`, `0` `@[expose]`, `0` `import all`, `private` helpers):
- Scoped `K6Tactics` for flat `u32 *k` (`kbuf`), `h->fuel` (`array64 (h + 32) hdr`), and
  `scr + 1096`.
- `K6BufOk`: structural & arena-bounds invariant for the K6 micro-solver workspace.
- Direct `Func.wp` proofs for all `9` K6 functions:
  `full_k6_{watch,assign,mtf,backtrack,prop,ana_cl,analyze,solve,core}_m7`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7BveGates

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

/-! ## 1. Scoped K6 Memory Tactics (`K6Tactics`) -/

namespace K6Tactics

private theorem k6_m4 (a i : BitVec 64) :
    a + i * 4 = a + BitVec.ofNat 64 (4 * i.toNat) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]

private theorem k6_m4_base (a i : BitVec 64) :
    a + 1096#64 * 4#64 + i * 4 = a + BitVec.ofNat 64 (4 * (1096 + i.toNat)) := by
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  simp only [Nat.reducePow, Nat.reduceMod]
  rw [show BitVec.toNat 4 = 4 from rfl, Nat.mul_add, Nat.add_mod_mod]
  congr 1; omega

private theorem k6_fuel_addr (h : BitVec 64) :
    h + 168#64 = (h + 32) + BitVec.ofNat 64 (8 * 17) := by
  rw [BitVec.add_assoc]; congr 1

@[scoped c0_load] theorem c0_load_k6_base {pk : BitVec 64} {kbuf : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < 2912) (hlen : 2912 ≤ kbuf.length)
    (hm : (array (t := i32) pk kbuf ⋆ R) m) :
    loadVal m i32 (pk + i * 4) = some (kbuf[i.toNat]'(by omega)) := by
  rw [k6_m4]; exact loadVal_array (t := i32) (by decide) (by omega) hm

@[scoped c0_store] theorem c0_store_k6_base {pk : BitVec 64} {kbuf : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < 2912) (hlen : 2912 ≤ kbuf.length)
    (hm : (array (t := i32) pk kbuf ⋆ R) m) :
    storeOk m i32 (pk + i * 4) ∧
      (array (t := i32) pk (kbuf.set i.toNat v) ⋆ R)
        (storeMem m i32 (pk + i * 4) v) := by
  rw [k6_m4]; exact store_array (t := i32) v (by decide) (by omega) hm

@[scoped c0_load] theorem c0_load_k6 {pk : BitVec 64} {kbuf : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (hi : i.toNat < kbuf.length)
    (hm : (array (t := i32) pk kbuf ⋆ R) m) :
    loadVal m i32 (pk + i * 4) = some kbuf[i.toNat] := by
  rw [k6_m4]; exact loadVal_array (t := i32) (by decide) hi hm

@[scoped c0_store] theorem c0_store_k6 {pk : BitVec 64} {kbuf : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < kbuf.length) (hm : (array (t := i32) pk kbuf ⋆ R) m) :
    storeOk m i32 (pk + i * 4) ∧
      (array (t := i32) pk (kbuf.set i.toNat v) ⋆ R)
        (storeMem m i32 (pk + i * 4) v) := by
  rw [k6_m4]; exact store_array (t := i32) v (by decide) hi hm

@[scoped c0_load] theorem c0_load_k6_fuel {h : BitVec 64} {hdr : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (hh : 17 < hdr.length)
    (hm : (array64 (h + 32) hdr ⋆ R) m) :
    loadVal m i64 (h + 168#64) = some hdr[17] := by
  rw [k6_fuel_addr]; exact loadVal_array64 hh hm

@[scoped c0_store] theorem c0_store_k6_fuel {h : BitVec 64} {hdr : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64) (hh : 17 < hdr.length)
    (hm : (array64 (h + 32) hdr ⋆ R) m) :
    storeOk m i64 (h + 168#64) ∧
      (array64 (h + 32) (hdr.set 17 v) ⋆ R) (storeMem m i64 (h + 168#64) v) := by
  rw [k6_fuel_addr]; exact store_array64 v hh hm

@[scoped c0_load] theorem c0_load_full_scratch_k6 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : 1096 + i.toNat < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + 1096#64 * 4#64 + i * 4) =
      some s.scratch.scratch_buf[1096 + i.toNat] := by
  rw [k6_m4_base]; exact FullArenaTactics.load_full_scratch_buf hi hm

@[scoped c0_store] theorem c0_store_full_scratch_k6 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : 1096 + i.toNat < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + 1096#64 * 4#64 + i * 4) ∧
      (FullMem c
        { s with
          scratch := { s.scratch with
            scratch_buf := s.scratch.scratch_buf.set (1096 + i.toNat) v } } ⋆ R)
        (storeMem m i32 (c.pScratchBuf + 1096#64 * 4#64 + i * 4) v) := by
  rw [k6_m4_base]; exact FullArenaTactics.store_full_scratch_buf v hi hm

@[scoped bv_c0] theorem k6_bv32_shl1 (x : BitVec 32) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem k6_bv32_shl1_or1 (x : BitVec 32) :
    ((x <<< (1 : Nat)) ||| (1 : BitVec 32)).toNat = (2 * x.toNat + 1) % 2 ^ 32 := by
  have h1 : (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 32 := k6_bv32_shl1 x
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

@[scoped bv_c0] theorem k6_bv32_lshr1 (x : BitVec 32) :
    (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

end K6Tactics

open scoped K6Tactics

local macro "k6_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private theorem k6_c0 : (OfNat.ofNat 0 % 18446744073709551616 : Nat) = 0 := rfl
private theorem k6_c1 : (OfNat.ofNat 1 % 18446744073709551616 : Nat) = 1 := rfl
private theorem k6_c3 : (OfNat.ofNat 3 % 18446744073709551616 : Nat) = 3 := rfl
private theorem k6_c4 : (OfNat.ofNat 4 % 18446744073709551616 : Nat) = 4 := rfl
private theorem k6_c5 : (OfNat.ofNat 5 % 18446744073709551616 : Nat) = 5 := rfl
private theorem k6_c6 : (OfNat.ofNat 6 % 18446744073709551616 : Nat) = 6 := rfl
private theorem k6_c7 : (OfNat.ofNat 7 % 18446744073709551616 : Nat) = 7 := rfl
private theorem k6_c8 : (OfNat.ofNat 8 % 18446744073709551616 : Nat) = 8 := rfl
private theorem k6_c9 : (OfNat.ofNat 9 % 18446744073709551616 : Nat) = 9 := rfl
private theorem k6_c10 : (OfNat.ofNat 10 % 18446744073709551616 : Nat) = 10 := rfl
private theorem k6_c11 : (OfNat.ofNat 11 % 18446744073709551616 : Nat) = 11 := rfl
private theorem k6_c15 : (OfNat.ofNat 15 % 18446744073709551616 : Nat) = 15 := rfl
private theorem k6_c16 : (OfNat.ofNat 16 % 18446744073709551616 : Nat) = 16 := rfl
private theorem k6_c17 : (OfNat.ofNat 17 % 18446744073709551616 : Nat) = 17 := rfl
private theorem k6_c18 : (OfNat.ofNat 18 % 18446744073709551616 : Nat) = 18 := rfl
private theorem k6_c20 : (OfNat.ofNat 20 % 18446744073709551616 : Nat) = 20 := rfl

private theorem k6_ne_of_eq {a b x : Nat} (h1 : a = b) (h2 : b ≠ x) : a ≠ x := h1 ▸ h2

local macro "k6_ne" : tactic =>
  `(tactic| repeat rw [List.getElem?_set_ne (by
    first
    | exact @k6_ne_of_eq _ 3 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 4 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 5 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 6 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 7 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 8 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 9 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 10 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 11 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 16 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 17 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 18 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 20 _ rfl (by omega)
    | c0_bound)])

private theorem k6_set_congr {α : Type} {xs : List α} {i j : Nat} {a b : α}
    (hi : i = j) (ha : a = b) : xs.set i a = xs.set j b := by
  subst hi ha; rfl

private theorem k6_get_congr {α : Type} {xs : List α} {i j : Nat}
    (h : i = j) (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

/-! ## 2. Pure BitVec & `K6BufOk` Safety Helpers -/

private theorem k6_w0_lt {n : Nat} {cid : BitVec 32} (hc : cid.toNat < n) (hn : 2 * n ≤ 2 ^ 32) :
    (cid <<< (1 : Nat)).toNat = 2 * cid.toNat ∧ (cid <<< (1 : Nat)).toNat < 2 * n := by
  have h1 : (cid <<< (1 : Nat)).toNat = 2 * cid.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  exact ⟨h1, by omega⟩

private theorem k6_w1_lt {n : Nat} {cid : BitVec 32} (hc : cid.toNat < n) (hn : 2 * n ≤ 2 ^ 32) :
    ((cid <<< (1 : Nat)) ||| 1#32).toNat = 2 * cid.toNat + 1 ∧
      ((cid <<< (1 : Nat)) ||| 1#32).toNat < 2 * n := by
  have h0 := (k6_w0_lt hc hn).1
  have h1 : ((cid <<< (1 : Nat)) ||| 1#32).toNat = 2 * cid.toNat + 1 := by
    rw [BitVec.toNat_or, h0, show (1#32 : BitVec 32).toNat = 1 from rfl]
    apply Nat.eq_of_testBit_eq; intro i
    cases i with
    | zero =>
      rw [Nat.testBit_or, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
      simp [Nat.mul_mod_right, show (2 * cid.toNat + 1) % 2 = 1 by omega]
    | succ j =>
      rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      simp [Nat.mul_add_div (by omega : 0 < 2)]
  exact ⟨h1, by omega⟩

private theorem k6_shr1_lt {n : Nat} (l : BitVec 32) (hl : l.toNat < 2 * n) :
    (l >>> (1 : Nat)).toNat = l.toNat / 2 ∧ (l >>> (1 : Nat)).toNat < n := by
  have h : (l >>> (1 : Nat)).toNat = l.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact ⟨h, by omega⟩

private theorem k6_xor1_lt {n : Nat} (l : BitVec 32) (hl : l.toNat < 2 * n) :
    (l ^^^ 1#32).toNat = l.toNat ^^^ 1 ∧ (l ^^^ 1#32).toNat < 2 * n := by
  have h1 : (l ^^^ 1#32).toNat = l.toNat ^^^ 1 := by
    rw [BitVec.toNat_xor, show (1#32 : BitVec 32).toNat = 1 from rfl]
  have h2 : l.toNat ^^^ 1 < 2 * n := by
    have := fullInv_var_xor1 l.toNat; omega
  exact ⟨h1, h2⟩

private theorem k6_bv32_bit_disj (x mask target : BitVec 32)
    (hm : (mask &&& target) = 0#32) :
    ((x ||| mask) &&& target) = (x &&& target) ∧
    ((x &&& ~~~mask) &&& target) = (x &&& target) := by
  have h1 : ((x ||| mask) &&& target) = (x &&& target) := by
    ext i hi
    have hmi := congrArg (·[i]) hm
    simp only [BitVec.getElem_and, BitVec.getElem_zero] at hmi
    simp only [BitVec.getElem_and, BitVec.getElem_or]
    rw [Bool.and_or_distrib_right, hmi, Bool.or_false]
  have h2 : ((x &&& ~~~mask) &&& target) = (x &&& target) := by
    ext i hi
    have hmi := congrArg (·[i]) hm
    simp only [BitVec.getElem_and, BitVec.getElem_zero] at hmi
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    cases ht : target[i]
    · simp
    · simp only [ht, Bool.and_true] at hmi ⊢
      simp [hmi]
  exact ⟨h1, h2⟩

private theorem k6_km_core_clear_pres (x : BitVec 32) :
    ((x &&& ~~~0x20000000#32) &&& 0xFFFF#32) = (x &&& 0xFFFF#32) ∧
    ((x &&& ~~~0x20000000#32) &&& 0x40000000#32) = (x &&& 0x40000000#32) :=
  ⟨(k6_bv32_bit_disj x 0x20000000#32 0xFFFF#32 (by decide)).2,
   (k6_bv32_bit_disj x 0x20000000#32 0x40000000#32 (by decide)).2⟩

private theorem k6_km_core_or_pres (x : BitVec 32) :
    ((x ||| 0x20000000#32) &&& 0xFFFF#32) = (x &&& 0xFFFF#32) ∧
    ((x ||| 0x20000000#32) &&& 0x40000000#32) = (x &&& 0x40000000#32) :=
  ⟨(k6_bv32_bit_disj x 0x20000000#32 0xFFFF#32 (by decide)).1,
   (k6_bv32_bit_disj x 0x20000000#32 0x40000000#32 (by decide)).1⟩

private theorem k6_km_core_lrn_has_lrn {cm : BitVec 32}
    (h : (cm &&& 0x60000000#32) = 0x60000000#32) :
    (cm &&& 0x40000000#32) ≠ 0#32 := by
  intro hz
  have h1 : ((cm &&& 0x60000000#32) &&& 0x40000000#32) =
      (0x60000000#32 &&& 0x40000000#32) := congrArg (· &&& 0x40000000#32) h
  have h2 : ((cm &&& 0x60000000#32) &&& 0x40000000#32) = (cm &&& 0x40000000#32) := by
    ext i hi; simp only [BitVec.getElem_and]
    have : (0x60000000#32 &&& 0x40000000#32 : BitVec 32)[i] = (0x40000000#32 : BitVec 32)[i] :=
      by revert i; decide
    simp only [BitVec.getElem_and] at this
    rw [Bool.and_assoc, this]
  have h3 : (0x60000000#32 &&& 0x40000000#32 : BitVec 32) = 0x40000000#32 := by decide
  rw [h2, hz, h3] at h1
  exact absurd h1 (by decide)

private theorem k6_and_ffff_le (cm : BitVec 32) : (cm &&& 0xFFFF#32).toNat ≤ 65535 := by
  rw [BitVec.toNat_and, show (0xFFFF#32 : BitVec 32).toNat = 2 ^ 16 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- Structural & arena safety invariant on the K6 micro-solver `u32 *k` slab. -/
def K6BufOk (kbuf : List (BitVec 32)) : Prop :=
  let nc := kbuf[1]?.getD 0#32
  let alen := kbuf[14]?.getD 0#32
  let acap := kbuf[15]?.getD 0#32
  2912 + acap.toNat ≤ kbuf.length ∧ kbuf.length < 2 ^ 28 ∧
  nc.toNat ≤ 256 ∧ alen.toNat ≤ acap.toNat ∧
  ∀ cid < nc.toNat,
    let off := (kbuf[1888 + cid]?.getD 0#32).toNat
    let cm := kbuf[2144 + cid]?.getD 0#32
    let sz := (cm &&& 0xFFFF#32).toNat
    let aux := (kbuf[2400 + cid]?.getD 0#32).toNat
    off + sz ≤ acap.toNat ∧ ((cm &&& 0x40000000#32) ≠ 0#32 → off + sz + aux ≤ acap.toNat)

theorem K6BufOk.mk_of {kbuf : List (BitVec 32)}
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

theorem K6BufOk.length_ge {kbuf : List (BitVec 32)} (h : K6BufOk kbuf) :
    2912 + (kbuf[15]?.getD 0#32).toNat ≤ kbuf.length := h.1

theorem K6BufOk.length_lt {kbuf : List (BitVec 32)} (h : K6BufOk kbuf) :
    kbuf.length < 2 ^ 28 := h.2.1

theorem K6BufOk.nc_le {kbuf : List (BitVec 32)} (h : K6BufOk kbuf) :
    (kbuf[1]?.getD 0#32).toNat ≤ 256 := h.2.2.1

theorem K6BufOk.alen_le {kbuf : List (BitVec 32)} (h : K6BufOk kbuf) :
    (kbuf[14]?.getD 0#32).toNat ≤ (kbuf[15]?.getD 0#32).toNat := h.2.2.2.1

theorem K6BufOk.clause_ok {kbuf : List (BitVec 32)} (h : K6BufOk kbuf) {cid : Nat}
    (hcid : cid < (kbuf[1]?.getD 0#32).toNat) :
    let off := (kbuf[1888 + cid]?.getD 0#32).toNat
    let cm := kbuf[2144 + cid]?.getD 0#32
    let sz := (cm &&& 0xFFFF#32).toNat
    let aux := (kbuf[2400 + cid]?.getD 0#32).toNat
    off + sz ≤ (kbuf[15]?.getD 0#32).toNat ∧
      ((cm &&& 0x40000000#32) ≠ 0#32 → off + sz + aux ≤ (kbuf[15]?.getD 0#32).toNat) :=
  h.2.2.2.2 cid hcid

theorem K6BufOk.base_ge {kbuf : List (BitVec 32)} (h : K6BufOk kbuf) :
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

private theorem k6_buf_get_eq {kbuf : List (BitVec 32)} {i : Nat} (hi : i < kbuf.length) :
    kbuf[i]?.getD 0#32 = kbuf[i]'hi := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some]

private theorem k6BufOk_set_core_meta {kbuf : List (BitVec 32)} (h : K6BufOk kbuf)
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
  have hj256 : j < 256 := by omega
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

private theorem k6BufOk_set_flags {kbuf : List (BitVec 32)} (h : K6BufOk kbuf)
    {i : Nat} (hi : i < 64) (v : BitVec 32) :
    K6BufOk (kbuf.set (416 + i) v) :=
  k6BufOk_of_frame h (List.length_set) fun idx _ hor => by
    rcases hor with rfl | rfl | rfl | ⟨_, _⟩ <;> exact List.getElem?_set_ne (by omega)

/-! ## 3. Specifications & `_noExit`/`_intro`/`_elim` for `9` K6 Functions -/

/-- Contract for `full_k6_watch_m7`. -/
def fullK6WatchM7Spec : Spec [i64, i32, i32, i32, i32] [] :=
  fun (pk, _cid, _l0, _l1, _sz, ()) m Q _ =>
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      2912 ≤ kbuf.length ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ kbuf' m', kbuf'.length = kbuf.length →
        (∀ idx < kbuf.length, (idx < 736 ∨ 1888 ≤ idx) → kbuf'[idx]? = kbuf[idx]?) →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q () m'

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

/-- Contract for `full_k6_assign_m7`. -/
def fullK6AssignM7Spec : Spec [i64, i32, i32] [] :=
  fun (pk, _lit, _rsn_cid, ()) m Q _ =>
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      2912 ≤ kbuf.length ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ kbuf' m', kbuf'.length = kbuf.length →
        (∀ idx < kbuf.length, idx ≠ 5 → idx ≠ 6 → (idx < 32 ∨ 480 ≤ idx) →
          (idx < 608 ∨ 736 ≤ idx) → kbuf'[idx]? = kbuf[idx]?) →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q () m'

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

/-- Contract for `full_k6_mtf_m7`. -/
def fullK6MtfM7Spec : Spec [i64, i32] [] :=
  fun (pk, _v, ()) m Q _ =>
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      2912 ≤ kbuf.length ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ kbuf' m', kbuf'.length = kbuf.length →
        (∀ idx < kbuf.length, idx ≠ 8 → idx ≠ 9 → idx ≠ 10 → idx ≠ 11 →
          (idx < 160 ∨ 352 ≤ idx) → kbuf'[idx]? = kbuf[idx]?) →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q () m'

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

/-- Contract for `full_k6_backtrack_m7`. -/
def fullK6BacktrackM7Spec : Spec [i64, i32] [] :=
  fun (pk, _target_lvl, ()) m Q _ =>
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      2912 ≤ kbuf.length ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ kbuf' m', kbuf'.length = kbuf.length →
        (∀ idx < kbuf.length, idx ≠ 3 → idx ≠ 4 → idx ≠ 5 → idx ≠ 6 → idx ≠ 10 →
          (idx < 32 ∨ 160 ≤ idx) → (idx < 608 ∨ 736 ≤ idx) → kbuf'[idx]? = kbuf[idx]?) →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q () m'

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

/-- Contract for `full_k6_prop_m7`. -/
def fullK6PropM7Spec : Spec [i64] [i32] :=
  fun (pk, ()) m Q _ =>
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      K6BufOk kbuf ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ r kbuf' m',
        K6BufOk kbuf' → kbuf'.length = kbuf.length →
        kbuf'[0]? = kbuf[0]? → kbuf'[1]? = kbuf[1]? →
        kbuf'[2]? = kbuf[2]? → kbuf'[15]? = kbuf[15]? →
        (∀ cid < 256, kbuf'[1888 + cid]? = kbuf[1888 + cid]? ∧
          kbuf'[2144 + cid]? = kbuf[2144 + cid]? ∧
          kbuf'[2400 + cid]? = kbuf[2400 + cid]?) →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q (r, ()) m'

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

/-- Contract for `full_k6_ana_cl_m7`. -/
def fullK6AnaClM7Spec : Spec [i64, i32, i32] [] :=
  fun (pk, _cid, _skip_v, ()) m Q _ =>
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      K6BufOk kbuf ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ kbuf' m', kbuf'.length = kbuf.length →
        (∀ idx < kbuf.length, idx ≠ 16 → idx ≠ 17 → idx ≠ 18 → idx ≠ 20 →
          (idx < 416 ∨ 608 ≤ idx) → (idx < 2784 ∨ 2912 ≤ idx) →
          kbuf'[idx]? = kbuf[idx]?) →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q () m'

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

/-- Contract for `full_k6_analyze_m7`. -/
def fullK6AnalyzeM7Spec : Spec [i64, i32] [.bool] :=
  fun (pk, _confl_cid, ()) m Q _ =>
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      K6BufOk kbuf ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ (ok : Bool) kbuf' m',
        K6BufOk kbuf' → kbuf'.length = kbuf.length →
        kbuf'[0]? = kbuf[0]? → kbuf'[2]? = kbuf[2]? → kbuf'[15]? = kbuf[15]? →
        (kbuf[1]?.getD 0#32).toNat ≤ (kbuf'[1]?.getD 0#32).toNat →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q (ok, ()) m'

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

/-- Contract for `full_k6_solve_m7`. -/
def fullK6SolveM7Spec : Spec [i64, i64, i32] [i64] :=
  fun (h, pk, _tick_lim, ()) m Q _ =>
    ∃ (hdr : List (BitVec 64)) (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      hdr.length = 140 ∧ K6BufOk kbuf ∧
      (array64 (h + 32) hdr ⋆ array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ r fuel' kbuf' m',
        fuel'.toNat ≤ (hdr[17]?.getD 0#64).toNat →
        K6BufOk kbuf' → kbuf'.length = kbuf.length →
        kbuf'[0]? = kbuf[0]? →
        (kbuf[1]?.getD 0#32).toNat ≤ (kbuf'[1]?.getD 0#32).toNat →
        kbuf'[2]? = kbuf[2]? → kbuf'[15]? = kbuf[15]? →
        (array64 (h + 32) (hdr.set 17 fuel') ⋆ array (t := i32) pk kbuf' ⋆ R) m' →
        Q (r, ()) m'

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

/-- Contract for `full_k6_core_m7`. -/
def fullK6CoreM7Spec : Spec [i64] [] :=
  fun (pk, ()) m Q _ =>
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
        (array (t := i32) pk kbuf' ⋆ R) m' → Q () m'

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

/-! ## 4. `full_k6_{watch,assign,mtf,backtrack}_m7_wp` -/

/-- Certifies `fullK6WatchM7Spec` for `full_k6_watch_m7`. -/
theorem full_k6_watch_m7_wp (Γ : Env) :
    ∀ a m Q X, fullK6WatchM7Spec a m Q X →
      Func.wp Γ full_k6_watch_m7_body a m Q X := by
  rintro ⟨pk, cid, l0, l1, sz, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨kbuf, R, hlen, hm0, hQ⟩ := fullK6WatchM7Spec_elim hSpec
  unfold Func.wp full_k6_watch_m7_body
  c0_hsplit
  · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ => rfl) hm0
  · have hcid : cid.toNat < 256 := by c0_bound
    c0_hsplit
    · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ => rfl) hm0
    · have hl0 : l0.toNat < 128 := by c0_bound
      c0_hsplit
      · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ => rfl) hm0
      · have hl1 : l1.toNat < 128 := by c0_bound
        have hw0 := k6_w0_lt hcid (by omega)
        have hw1 := k6_w1_lt hcid (by omega)
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
          (fun bf => (bf, ())) (fun _ => True)
          (fun _ bf _ => by
            c0_hsteps!
            refine hQ _ _ (by simp) (fun idx hi hor => ?_) hm
            repeat rw [List.getElem?_set_ne (by c0_bound)])
          (fun J hJ => by
            c0_hsplit
            · c0_hsteps!; exact hJ 0x80000000#32 trivial
            · c0_hsteps!; exact hJ 0#32 trivial)

/-- Certifies `fullK6AssignM7Spec` for `full_k6_assign_m7`. -/
theorem full_k6_assign_m7_wp (Γ : Env) :
    ∀ a m Q X, fullK6AssignM7Spec a m Q X →
      Func.wp Γ full_k6_assign_m7_body a m Q X := by
  rintro ⟨pk, lit, rsn_cid, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨kbuf, R, hlen, hm0, hQ⟩ := fullK6AssignM7Spec_elim hSpec
  unfold Func.wp full_k6_assign_m7_body
  c0_hsplit
  · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ _ _ _ => rfl) hm0
  · have hlit : lit.toNat < 128 := by c0_bound
    c0_hsplit
    · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ _ _ _ => rfl) hm0
    · have hte : (kbuf[5]'(by omega)).toNat < 64 :=
        Nat.lt_of_not_le (show ¬64 ≤ (kbuf[5]'(by omega)).toNat from hc)
      obtain ⟨hv_eq, hv_lt⟩ := k6_shr1_lt (n := 64) lit (by omega)
      obtain ⟨hln_eq, hln_lt⟩ := k6_xor1_lt (n := 64) lit (by omega)
      c0_hsteps_nogrp
      refine wp_join0
        (fun mj => ∃ kbufj : List (BitVec 32),
          kbufj.length = kbuf.length ∧
          (∀ idx < kbuf.length, idx ≠ 5 → idx ≠ 6 → (idx < 32 ∨ 480 ≤ idx) →
            (idx < 608 ∨ 736 ≤ idx) → kbufj[idx]? = kbuf[idx]?) ∧
          (array (t := i32) pk kbufj ⋆ R) mj)
        (fun _ mj ⟨kbufj, hlj, hkj, hmj⟩ => by
          have hv416 : ((416#32 + (lit >>> (1 : Nat))).setWidth 64).toNat < 2912 := by c0_bound
          c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
            (fun nfl => (nfl, ())) (fun _ => True)
            (fun _ nfl _ => by
              c0_hsteps!
              refine hQ _ _ (by simp [hlj]) (fun idx hi h5 h6 ha hb => ?_) hm
              rw [List.getElem?_set_ne (by c0_bound)]
              exact hkj idx hi h5 h6 ha hb)
            (fun Jf hJf => by
              c0_hsplit
              · c0_hsteps!; exact hJf _ trivial
              · c0_hsteps!; exact hJf _ trivial))
        (fun J0 hJ0 => by
          c0_hsplit
          · c0_hsteps!
            refine hJ0 _ ⟨_, ?_, ?_, hm⟩
            · simp
            · intro idx hi h5 h6 ha hb; k6_ne
          · c0_hsteps!
            refine hJ0 _ ⟨_, ?_, ?_, hm⟩
            · simp
            · intro idx hi h5 h6 ha hb; k6_ne)

/-- Certifies `fullK6MtfM7Spec` for `full_k6_mtf_m7`. -/
theorem full_k6_mtf_m7_wp (Γ : Env) :
    ∀ a m Q X, fullK6MtfM7Spec a m Q X →
      Func.wp Γ full_k6_mtf_m7_body a m Q X := by
  rintro ⟨pk, v, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨kbuf, R, hlen, hm0, hQ⟩ := fullK6MtfM7Spec_elim hSpec
  let nv := kbuf[0]'(by omega)
  unfold Func.wp full_k6_mtf_m7_body
  c0_hsplit
  · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ _ _ _ _ => rfl) hm0
  · have hnv : (kbuf[0]'(by omega)).toNat ≤ 64 :=
      Nat.le_of_not_lt (show ¬64 < (kbuf[0]'(by omega)).toNat from hc)
    have hnv_le : nv.toNat ≤ 64 := hnv
    c0_hsplit
    · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ _ _ _ _ => rfl) hm0
    · have hv_lt : v.toNat < nv.toNat :=
        Nat.lt_of_not_le (show ¬nv.toNat ≤ v.toNat from hc)
      c0_hsplit
      · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ _ _ _ _ => rfl) hm0
      · let pv := kbuf[160 + v.toNat]'(by have := hnv_le; omega)
        let nxt := kbuf[224 + v.toNat]'(by have := hnv_le; omega)
        have hvv : ((608#32 + (v <<< (1 : Nat))).setWidth 64).toNat < kbuf.length := by
          have := k6_w0_lt hv_lt (by have := hnv_le; omega); c0_bound
        let finish := fun (kbuf6 : List (BitVec 32)) (m6 : Mem 64) =>
          (kbuf6.length = kbuf.length) ∧
          (∀ idx < kbuf.length, idx ≠ 8 → idx ≠ 9 → idx ≠ 10 → idx ≠ 11 →
            (idx < 160 ∨ 352 ≤ idx) → kbuf6[idx]? = kbuf[idx]?) ∧
          (array (t := i32) pk kbuf6 ⋆ R) m6
        c0_hsteps_nogrp
        -- Chain the 6 `sig=[]` joins cleanly inside `k6_mtf`
        refine wp_join0 (fun m1 => ∃ kb1, finish kb1 m1) ?_ ?_
        · intro _ m1 ⟨kb1, hl1, hk1, hm1⟩
          c0_hsteps_nogrp
          refine wp_join0 (fun m2 => ∃ kb2, finish kb2 m2) ?_ ?_
          · intro _ m2 ⟨kb2, hl2, hk2, hm2⟩
            c0_hsteps_nogrp
            refine wp_join0 (fun m3 => ∃ kb3, finish kb3 m3) ?_ ?_
            · intro _ m3 ⟨kb3, hl3, hk3, hm3⟩
              c0_hsteps_nogrp
              refine wp_join0 (fun m4 => ∃ kb4, finish kb4 m4) ?_ ?_
              · intro _ m4 ⟨kb4, hl4, hk4, hm4⟩
                c0_hsteps_nogrp
                refine wp_join0 (fun m5 => ∃ kb5, finish kb5 m5) ?_ ?_
                · intro _ m5 ⟨kb5, hl5, hk5, hm5⟩
                  c0_hsteps_nogrp
                  refine wp_join0 (fun m6 => ∃ kb6, finish kb6 m6) ?_ ?_
                  · intro _ m6 ⟨kb6, hl6, hk6, hm6⟩
                    c0_hsteps!
                    exact hQ kb6 m6 hl6 hk6 hm6
                  · intro J6 hJ6
                    c0_hsplit
                    · c0_hsteps!
                      refine hJ6 m ⟨_, ?_, ?_, hm⟩
                      · simp [hl5]
                      · intro idx hi h8 h9 h10 h11 ha
                        k6_ne; exact hk5 idx hi h8 h9 h10 h11 ha
                    · c0_hsteps!; exact hJ6 m5 ⟨kb5, hl5, hk5, hm5⟩
                · intro J5 hJ5
                  c0_hsplit
                  · c0_hsteps!
                    refine hJ5 m ⟨_, ?_, ?_, hm⟩
                    · simp [hl4]
                    · intro idx hi h8 h9 h10 h11 ha
                      k6_ne; exact hk4 idx hi h8 h9 h10 h11 ha
                  · c0_hsteps!; exact hJ5 m4 ⟨kb4, hl4, hk4, hm4⟩
              · intro J4 hJ4
                c0_hsplit
                · c0_hsteps!
                  refine hJ4 m ⟨_, ?_, ?_, hm⟩
                  · simp [hl3]
                  · intro idx hi h8 h9 h10 h11 ha
                    k6_ne; exact hk3 idx hi h8 h9 h10 h11 ha
                · c0_hsteps!
                  refine hJ4 m ⟨_, ?_, ?_, hm⟩
                  · simp [hl3]
                  · intro idx hi h8 h9 h10 h11 ha
                    k6_ne; exact hk3 idx hi h8 h9 h10 h11 ha
            · intro J3 hJ3
              c0_hsplit
              · c0_hsteps!
                refine hJ3 m ⟨_, ?_, ?_, hm⟩
                · simp [hl2]
                · intro idx hi h8 h9 h10 h11 ha
                  k6_ne; exact hk2 idx hi h8 h9 h10 h11 ha
              · have hnxt : nxt.toNat < nv.toNat := by
                  have h1 : (224 + v.toNat) % 4294967296 = 224 + v.toNat := by
                    have := hnv_le; omega
                  exact Nat.lt_of_not_le (by simpa [nxt, k6_c0, h1] using hc)
                c0_hsteps!
                refine hJ3 m ⟨_, ?_, ?_, hm⟩
                · simp [hl2]
                · intro idx hi h8 h9 h10 h11 ha
                  k6_ne; exact hk2 idx hi h8 h9 h10 h11 ha
          · intro J2 hJ2
            c0_hsplit
            · c0_hsteps!
              refine hJ2 m ⟨_, ?_, ?_, hm⟩
              · simp [hl1]
              · intro idx hi h8 h9 h10 h11 ha
                k6_ne; exact hk1 idx hi h8 h9 h10 h11 ha
            · have hpv : pv.toNat < nv.toNat := by
                have h1 : (160 + v.toNat) % 4294967296 = 160 + v.toNat := by
                  have := hnv_le; omega
                exact Nat.lt_of_not_le (by simpa [pv, k6_c0, h1] using hc)
              c0_hsteps!
              refine hJ2 m ⟨_, ?_, ?_, hm⟩
              · simp [hl1]
              · intro idx hi h8 h9 h10 h11 ha
                k6_ne; exact hk1 idx hi h8 h9 h10 h11 ha
        · intro J1 hJ1
          c0_hsplit
          · c0_hsplit
            · c0_hsteps! <;> first
                | exact hJ1 m0 ⟨kbuf, rfl, fun _ _ _ _ _ _ _ => rfl, hm0⟩
                | (refine hJ1 m ⟨_, ?_, ?_, hm⟩
                   · simp
                   · intro idx hi h8 h9 h10 h11 ha; k6_ne)
            · c0_hsteps!; exact hJ1 m0 ⟨kbuf, rfl, fun _ _ _ _ _ _ _ => rfl, hm0⟩
          · c0_hsteps!; exact hJ1 m0 ⟨kbuf, rfl, fun _ _ _ _ _ _ _ => rfl, hm0⟩

/-- Certifies `fullK6BacktrackM7Spec` for `full_k6_backtrack_m7`. -/
theorem full_k6_backtrack_m7_wp (Γ : Env) :
    ∀ a m Q X, fullK6BacktrackM7Spec a m Q X →
      Func.wp Γ full_k6_backtrack_m7_body a m Q X := by
  rintro ⟨pk, target_lvl, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨kbuf, R, hlen, hm0, hQ⟩ := fullK6BacktrackM7Spec_elim hSpec
  let nv := kbuf[0]'(by omega)
  unfold Func.wp full_k6_backtrack_m7_body
  c0_hsplit
  · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ _ _ _ _ _ _ => rfl) hm0
  · have hnv : nv.toNat ≤ 64 :=
      Nat.le_of_not_lt (show ¬64 < nv.toNat from hc)
    c0_hsteps_nogrp
    -- Join for `if (te > K6_MV) te = K6_MV`
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
      (fun te => (te, ())) (fun te => te.toNat ≤ 64)
      (fun _ te hte => by
        c0_hsteps_nogrp
        -- Join for `if (k[KH_QSEARCH] < nv) best_st = k[KO_QST + k[KH_QSEARCH]]`
        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
          (fun bs => (bs, ())) (fun _ => True)
          (fun _ bs _ => by
            let keep := fun (kb : List (BitVec 32)) =>
              kb.length = kbuf.length ∧
              (∀ idx < kbuf.length, idx ≠ 3 → idx ≠ 4 → idx ≠ 5 → idx ≠ 6 → idx ≠ 10 →
                (idx < 32 ∨ 160 ≤ idx) → (idx < 608 ∨ 736 ≤ idx) → kb[idx]? = kbuf[idx]?)
            c0_hsteps_nogrp
            refine wp_loop_break_group (brkTs := [i32, i32]) (lpTs := [i32, i32])
              (fun (te_b, _bs_b, ()) mb => ∃ kbb, keep kbb ∧ te_b.toNat ≤ 64 ∧
                (array (t := i32) pk kbb ⋆ R) mb)
              (fun rem (te_l, bs_l, ()) ml => ∃ kbl, keep kbl ∧ te_l.toNat ≤ 64 ∧
                rem = te_l.toNat ∧ (array (t := i32) pk kbl ⋆ R) ml)
              ?_ ?_ ?_
            · rintro _ ⟨te_b, _bs_b, ⟨⟩⟩ mb ⟨kbb, hkb_k, hte_b, hmb⟩
              have hkb_l := hkb_k.1
              c0_hsteps_nogrp
              refine wp_join0 (fun mj => ∃ kbj, keep kbj ∧ (array (t := i32) pk kbj ⋆ R) mj)
                (fun _ mj ⟨kbj, hkj_k, hmj⟩ => by
                  have hkj_l := hkj_k.1
                  c0_hsteps!
                  refine hQ _ _ (by simp [hkj_l]) (fun idx hi h3 h4 h5 h6 h10 ha hb => ?_) hm
                  k6_ne; exact hkj_k.2 idx hi h3 h4 h5 h6 h10 ha hb)
                (fun Jp hJp => by
                  c0_hsplit
                  · c0_hsteps!
                    refine hJp _ ⟨_, ⟨by simp [hkb_l], fun idx hi h3 h4 h5 h6 h10 ha hb => ?_⟩, hm⟩
                    k6_ne; exact hkb_k.2 idx hi h3 h4 h5 h6 h10 ha hb
                  · c0_hsteps!
                    refine hJp _ ⟨_, ⟨by simp [hkb_l], fun idx hi h3 h4 h5 h6 h10 ha hb => ?_⟩, hm⟩
                    k6_ne; exact hkb_k.2 idx hi h3 h4 h5 h6 h10 ha hb)
            · rintro B L rem ⟨te_l, bs_l, ⟨⟩⟩ ml hB hL ⟨kbl, hkl_k, hte_l, rfl, hml⟩
              have hkl_l := hkl_k.1
              have hkb_nv : kbl[0]'(by omega) = nv := by
                have := hkl_k.2 0 (by omega) (by decide) (by decide) (by decide) (by decide)
                  (by decide) (Or.inl (by decide)) (Or.inl (by decide))
                rw [List.getElem?_eq_getElem (by omega),
                  List.getElem?_eq_getElem (by omega)] at this
                exact Option.some.inj this
              c0_hsplit
              · have hte_pos : 0 < te_l.toNat := by simpa using hc
                clear hc
                have hte1_lt : (te_l - 1#32).toNat < 64 := by
                  rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
                  have := hte_pos; have := hte_l; omega
                have hsub352 : (352#32 + te_l - 1#32).toNat = 351 + te_l.toNat := by
                  rw [BitVec.toNat_sub, BitVec.toNat_add]
                  simp only [BitVec.toNat_ofNat]; have := hte_pos; have := hte_l; omega
                c0_hsplit
                · c0_hsteps!; exact hB (te_l, bs_l, ()) ml ⟨kbl, hkl_k, hte_l, hml⟩
                · have hlit_idx : (BitVec.setWidth 64 (352#32 + te_l - 1#32)).toNat =
                      (4294967295 + (352 + te_l.toNat)) % 4294967296 := by
                    rw [BitVec.toNat_setWidth, hsub352]; have := hte_pos; have := hte_l; omega
                  have hlit_len1 :
                      (BitVec.setWidth 64 (352#32 + te_l - 1#32)).toNat < kbl.length := by
                    rw [BitVec.toNat_setWidth, hsub352]; have := hte_pos; have := hte_l; omega
                  have hlit_len2 : (4294967295 + (352 + te_l.toNat)) % 4294967296 < kbl.length := by
                    have := hte_pos; have := hte_l; omega
                  have hlit_ast :
                      (kbl[(BitVec.setWidth 64
                        (352#32 + te_l - 1#32)).toNat]'hlit_len1).toNat < 2 * nv.toNat := by
                    have htw : (2 * kbuf[0].toNat) % 2 ^ 32 = 2 * nv.toNat := by
                      change (2 * nv.toNat) % 2 ^ 32 = 2 * nv.toNat
                      have := hnv; omega
                    rw [k6_get_congr hlit_idx hlit_len1 hlit_len2]
                    simpa [htw] using hc
                  clear hc
                  have hlit128 :
                      (kbl[(BitVec.setWidth 64 (352#32 + te_l - 1#32)).toNat]'hlit_len1).toNat <
                        128 := by
                    have := hnv; omega
                  let lit := kbl[(BitVec.setWidth 64 (352#32 + te_l - 1#32)).toNat]'hlit_len1
                  obtain ⟨hv_eq, hv_lt⟩ := k6_shr1_lt (n := 64) lit (by omega)
                  obtain ⟨hln_eq, hln_lt⟩ := k6_xor1_lt (n := 64) lit (by omega)
                  have hln_bd :
                      (BitVec.setWidth 64 (608#32 + (lit ^^^ 1#32))).toNat < kbl.length := by
                    have := hln_lt; have := hkl_l; c0_bound
                  have hv_bd1 :
                      (BitVec.setWidth 64 (32#32 + (lit >>> (1 : Nat)))).toNat < kbl.length := by
                    have := hv_lt; have := hkl_l; c0_bound
                  have hv_bd2 :
                      (BitVec.setWidth 64 (96#32 + (lit >>> (1 : Nat)))).toNat < kbl.length := by
                    have := hv_lt; have := hkl_l; c0_bound
                  have hln_bd_raw : (BitVec.setWidth 64
                      (608 + (kbl[(BitVec.setWidth 64
                        (352 + te_l - 1)).toNat]'hlit_len1 ^^^ 1))).toNat < kbl.length :=
                    hln_bd
                  have hv_bd1_raw : (BitVec.setWidth 64
                      (32 + (kbl[(BitVec.setWidth 64 (352 + te_l - 1)).toNat]'hlit_len1 >>>
                        (1 : Nat)))).toNat < kbl.length := hv_bd1
                  have hv_bd2_raw : (BitVec.setWidth 64
                      (96 + (kbl[(BitVec.setWidth 64 (352 + te_l - 1)).toNat]'hlit_len1 >>>
                        (1 : Nat)))).toNat < kbl.length := hv_bd2
                  c0_hsplit
                  · c0_hsteps!; exact hB (te_l, bs_l, ()) ml ⟨kbl, hkl_k, hte_l, hml⟩
                  · c0_hsteps_nogrp
                    refine wp_join_state1 (t := i32) (α := BitVec 32 × List (BitVec 32))
                      (fun x => x.1)
                      (fun x mj => keep x.2 ∧ (array (t := i32) pk x.2 ⋆ R) mj) ?_ ?_
                    · rintro _ ⟨bs', kb'⟩ mj ⟨hk', hmj⟩
                      c0_hsteps!
                      have hsub_lt : (te_l - 1#32).toNat < te_l.toNat := by
                        rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
                        have := hte_pos; have := hte_l; omega
                      exact hL (te_l - 1#32).toNat (te_l - 1#32, bs', ()) mj hsub_lt
                        ⟨kb', hk', by omega, rfl, hmj⟩
                    · intro Js hJs
                      have hln_raw_lt : (BitVec.toNat
                          kbl[(4294967296 - 1 + (352 + BitVec.toNat te_l)) % 4294967296] ^^^ 1) <
                          128 := by
                        have heq352 :
                            (4294967296 - 1 + (352 + BitVec.toNat te_l)) % 4294967296 =
                            (BitVec.setWidth 64 (352#32 + te_l - 1#32)).toNat := by
                          rw [hlit_idx]
                        have hlt : BitVec.toNat
                            kbl[(4294967296 - 1 + (352 + BitVec.toNat te_l)) % 4294967296] <
                            128 := by
                          rw [k6_get_congr heq352 hlit_len2 hlit_len1]
                          exact hlit128
                        exact Nat.xor_lt_two_pow (n := 7) hlt (by decide)
                      c0_hsplit
                      · c0_hsteps!
                        refine hJs (_, _) m ⟨⟨?_, ?_⟩, hm⟩
                        · simp [hkl_l]
                        · intro idx hi h3 h4 h5 h6 h10 ha hb
                          have := hln_raw_lt; k6_ne
                          exact hkl_k.2 idx hi h3 h4 h5 h6 h10 ha hb
                      · c0_hsteps!
                        refine hJs (bs_l, _) m ⟨⟨?_, ?_⟩, hm⟩
                        · simp [hkl_l]
                        · intro idx hi h3 h4 h5 h6 h10 ha hb
                          have := hln_raw_lt; k6_ne
                          exact hkl_k.2 idx hi h3 h4 h5 h6 h10 ha hb
              · c0_hsteps!; exact hB (te_l, bs_l, ()) ml ⟨kbl, hkl_k, hte_l, hml⟩
            · intro _ L _ hL; c0_hsteps!
              exact hL te.toNat (te, bs, ()) m0
                ⟨kbuf, ⟨rfl, fun _ _ _ _ _ _ _ _ _ => rfl⟩, hte, rfl, hm0⟩)
          (fun Jbs hJbs => by
            c0_hsplit
            · c0_hsteps!; exact hJbs _ trivial
            · c0_hsteps!; exact hJbs 0#32 trivial))
      (fun Jte hJte => by
        c0_hsplit
        · c0_hsteps!; exact hJte 64#32 (by decide)
        · c0_hsteps!; exact hJte _ (by c0_bound))

/-! ## 5. `full_k6_ana_cl_m7_wp` and `full_k6_core_m7_wp` -/

/-- Certifies `fullK6AnaClM7Spec` for `full_k6_ana_cl_m7`. -/
theorem full_k6_ana_cl_m7_wp (Γ : Env) :
    ∀ a m Q X, fullK6AnaClM7Spec a m Q X →
      Func.wp Γ full_k6_ana_cl_m7_body a m Q X := by
  rintro ⟨pk, cid, skip_v, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨kbuf, R, hok0, hm0, hQ⟩ := fullK6AnaClM7Spec_elim hSpec
  have hlen := hok0.base_ge
  let nc := kbuf[1]'(by omega)
  let nv := kbuf[0]'(by omega)
  let acap := kbuf[15]'(by omega)
  unfold Func.wp full_k6_ana_cl_m7_body
  c0_hsplit
  · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ _ _ _ _ _ => rfl) hm0
  · have hcid : cid.toNat < nc.toNat :=
      Nat.lt_of_not_le (show ¬nc.toNat ≤ cid.toNat from hc)
    clear hc
    c0_hsplit
    · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ _ _ _ _ _ => rfl) hm0
    · have hnc_le : nc.toNat ≤ 256 :=
        Nat.le_of_not_lt (show ¬256 < nc.toNat from hc)
      clear hc
      c0_hsplit
      · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ _ _ _ _ _ => rfl) hm0
      · have hnv_le : nv.toNat ≤ 64 :=
          Nat.le_of_not_lt (show ¬64 < nv.toNat from hc)
        clear hc
        let off := kbuf[1888 + cid.toNat]'(by omega)
        let cm := kbuf[2144 + cid.toNat]'(by omega)
        let sz := cm &&& 0xFFFF#32
        have hcl_ok := hok0.clause_ok (by rw [k6_buf_get_eq (by omega)]; exact hcid)
        rw [k6_buf_get_eq (by omega : 1888 + cid.toNat < kbuf.length),
          k6_buf_get_eq (by omega : 2144 + cid.toNat < kbuf.length),
          k6_buf_get_eq (by omega : 15 < kbuf.length)] at hcl_ok
        have hoff_sz : off.toNat + sz.toNat ≤ acap.toNat := hcl_ok.1
        have hlt28 := hok0.length_lt
        have hac_le := hok0.length_ge
        rw [k6_buf_get_eq (by omega : 15 < kbuf.length)] at hac_le
        change 2912 + acap.toNat ≤ kbuf.length at hac_le
        have hoff_sz_nowarp : off.toNat + sz.toNat < 2 ^ 32 := by omega
        c0_hsplit
        · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ _ _ _ _ _ => rfl) hm0
        · clear hc
          let keep := fun (kb : List (BitVec 32)) =>
            kb.length = kbuf.length ∧
            (∀ idx < kbuf.length, idx ≠ 16 → idx ≠ 17 → idx ≠ 18 → idx ≠ 20 →
              (idx < 416 ∨ 608 ≤ idx) → (idx < 2784 ∨ 2912 ≤ idx) →
              kb[idx]? = kbuf[idx]?)
          refine wp_join0 (fun m1 => ∃ kb1, keep kb1 ∧ (array (t := i32) pk kb1 ⋆ R) m1) ?_ ?_
          · intro _ m1 ⟨kb1, hk1, hm1⟩
            have hkb1_l := hk1.1
            c0_hsteps_nogrp
            refine wp_loop_group (ts := [i32])
              (fun rem (i, ()) mi => ∃ kbi, keep kbi ∧ i.toNat ≤ sz.toNat ∧
                rem = sz.toNat - i.toNat ∧ (array (t := i32) pk kbi ⋆ R) mi)
              ?_ ?_
            · rintro L rem ⟨i, ⟨⟩⟩ mi hL ⟨kbi, hki, hi_le, rfl, hmi⟩
              have hki_l := hki.1
              c0_hsplit
              · have hi_lt : i.toNat < sz.toNat := by
                  have h1 : (2144 + cid.toNat) % 4294967296 = 2144 + cid.toNat := by
                    have := hcid; have := hnc_le; omega
                  have hsz_nat : sz.toNat = cm.toNat &&& 65535 := by
                    change (cm &&& 65535#32).toNat = cm.toNat &&& 65535
                    rw [BitVec.toNat_and]; rfl
                  rw [hsz_nat]
                  simpa [cm, h1] using hc
                clear hc
                have har_bd : (2912 + off.toNat + i.toNat) < kbi.length := by
                  have := hac_le; have := hoff_sz; have := hki_l; have := hi_lt; omega
                have hi1 : (i + 1#32).toNat = i.toNat + 1 := by
                  have := hlt28; have := hac_le; have := hoff_sz; have := hi_lt; c0_bound
                have h1888_idx : (BitVec.setWidth 64 (1888#32 + cid)).toNat = 1888 + cid.toNat := by
                  have := hcid; have := hnc_le; c0_bound
                have har_c0_bd : (BitVec.setWidth 64
                    (2912#32 + kbuf[(BitVec.setWidth 64 (1888#32 + cid)).toNat]'(by
                      rw [h1888_idx]; have := hcid; have := hnc_le; omega) + i)).toNat <
                    kbi.length := by
                  rw [k6_get_congr h1888_idx _ _]
                  change (BitVec.setWidth 64 (2912#32 + off + i)).toNat < kbi.length
                  have := har_bd; have := hlt28; have := hki_l; c0_bound
                c0_hsteps_nogrp
                refine wp_join0 (fun mj => ∃ kbj, keep kbj ∧ (array (t := i32) pk kbj ⋆ R) mj)
                  ?_ ?_
                · intro _ mj ⟨kbj, hkj, hmj⟩
                  c0_hsteps!
                  exact hL (sz.toNat - (i + 1#32).toNat) (i + 1#32, ()) mj
                    (by have := hlt28; have := hac_le; have := hoff_sz; have := hi_lt; omega)
                    ⟨kbj, hkj, by omega, rfl, hmj⟩
                · intro J349 hJ349
                  let l := kbi[2912 + off.toNat + i.toNat]'(by omega)
                  let v := l >>> (1 : Nat)
                  have h1888_mod :
                      (1888 + cid.toNat) % 4294967296 = 1888 + cid.toNat := by
                    have := hcid; have := hnc_le; omega
                  have h2912_mod :
                      (2912 + off.toNat + i.toNat) % 4294967296 =
                      2912 + off.toNat + i.toNat := by
                    have := hoff_sz_nowarp; have := hi_lt; omega
                  have h1888_bd : (1888 + cid.toNat) % 4294967296 < kbuf.length := by
                    rw [h1888_mod]; have := hcid; have := hnc_le; omega
                  have h2912_c0_idx : (BitVec.setWidth 64
                      (2912#32 + kbuf[(BitVec.setWidth 64 (1888#32 + cid)).toNat]'(by
                        rw [h1888_idx]; have := hcid; have := hnc_le; omega) + i)).toNat =
                      2912 + off.toNat + i.toNat := by
                    rw [k6_get_congr h1888_idx _ _]
                    change (BitVec.setWidth 64 (2912#32 + off + i)).toNat =
                      2912 + off.toNat + i.toNat
                    have := har_bd; have := hlt28; have := hki_l; c0_bound
                  have hl_c0_eq : kbi[(BitVec.setWidth 64
                      (2912#32 + kbuf[(BitVec.setWidth 64 (1888#32 + cid)).toNat]'(by
                        rw [h1888_idx]; have := hcid
                        have := hnc_le; omega) + i)).toNat]'har_c0_bd =
                      l := k6_get_congr h2912_c0_idx har_c0_bd har_bd
                  c0_hsplit
                  · have hget1 : kbuf[(1888 + cid.toNat) % 4294967296]'h1888_bd = off :=
                      k6_get_congr h1888_mod h1888_bd _
                    have h2912_raw_idx : (2912 +
                        (kbuf[(1888 + cid.toNat) % 4294967296]'h1888_bd).toNat +
                        i.toNat) % 4294967296 = 2912 + off.toNat + i.toNat := by
                      rw [hget1]; exact h2912_mod
                    have h2912_bd : (2912 +
                        (kbuf[(1888 + cid.toNat) % 4294967296]'h1888_bd).toNat +
                        i.toNat) % 4294967296 < kbi.length := by
                      rw [h2912_raw_idx]; exact har_bd
                    have hget2 : kbi[(2912 +
                        (kbuf[(1888 + cid.toNat) % 4294967296]'h1888_bd).toNat +
                        i.toNat) % 4294967296]'h2912_bd = l :=
                      k6_get_congr h2912_raw_idx h2912_bd har_bd
                    have hv_div : v.toNat = l.toNat / 2 := by
                      dsimp only [v]; rw [BitVec.toNat_ushiftRight]
                      simp [Nat.shiftRight_eq_div_pow]
                    have hv_lt : v.toNat < nv.toNat := by
                      refine Nat.lt_of_not_le (show ¬nv.toNat ≤ v.toNat from ?_)
                      rw [hv_div]
                      simpa [nv, k6_c0, l, hget2] using hc
                    have hv_raw64 : (kbi[(2912 +
                        (kbuf[(1888 + cid.toNat) % 4294967296]'h1888_bd).toNat +
                        i.toNat) % 4294967296]'h2912_bd).toNat / 2 < 64 := by
                      rw [hget2, ← hv_div]; have := hv_lt; have := hnv_le; omega
                    clear hc
                    have hv416_c0 : (BitVec.setWidth 64 (416#32 +
                        (kbi[(BitVec.setWidth 64 (2912#32 +
                          kbuf[(BitVec.setWidth 64 (1888#32 + cid)).toNat]'(by
                            rw [h1888_idx]; have := hcid; have := hnc_le; omega) +
                          i)).toNat]'har_c0_bd >>> (1 : Nat)))).toNat < kbi.length := by
                      rw [hl_c0_eq]
                      change (BitVec.setWidth 64 (416#32 + v)).toNat < kbi.length
                      have := hv_lt; have := hnv_le; have := hki_l; have := hlen; c0_bound
                    have hv32_c0 : (BitVec.setWidth 64 (32#32 +
                        (kbi[(BitVec.setWidth 64 (2912#32 +
                          kbuf[(BitVec.setWidth 64 (1888#32 + cid)).toNat]'(by
                            rw [h1888_idx]; have := hcid; have := hnc_le; omega) +
                          i)).toNat]'har_c0_bd >>> (1 : Nat)))).toNat < kbi.length := by
                      rw [hl_c0_eq]
                      change (BitVec.setWidth 64 (32#32 + v)).toNat < kbi.length
                      have := hv_lt; have := hnv_le; have := hki_l; have := hlen; c0_bound
                    have hv96_c0 : (BitVec.setWidth 64 (96#32 +
                        (kbi[(BitVec.setWidth 64 (2912#32 +
                          kbuf[(BitVec.setWidth 64 (1888#32 + cid)).toNat]'(by
                            rw [h1888_idx]; have := hcid; have := hnc_le; omega) +
                          i)).toNat]'har_c0_bd >>> (1 : Nat)))).toNat < kbi.length := by
                      rw [hl_c0_eq]
                      change (BitVec.setWidth 64 (96#32 + v)).toNat < kbi.length
                      have := hv_lt; have := hnv_le; have := hki_l; have := hlen; c0_bound
                    c0_hsplit
                    · c0_hsplit
                      · c0_hsteps_nogrp
                        refine wp_join0
                          (fun m361 => ∃ kb361, keep kb361 ∧ (array (t := i32) pk kb361 ⋆ R) m361)
                          ?_ ?_
                        · intro _ m361 ⟨kb361, hk361, hm361⟩
                          have hk361_l := hk361.1
                          c0_hsteps_nogrp
                          refine wp_join0
                            (fun m361b => ∃ kb361b, keep kb361b ∧
                              (array (t := i32) pk kb361b ⋆ R) m361b)
                            ?_ ?_
                          · intro _ m361b ⟨kb361b, hk361b, hm361b⟩
                            c0_hsteps!; exact hJ349 m361b ⟨kb361b, hk361b, hm361b⟩
                          · intro J361b hJ361b
                            c0_hsplit
                            · c0_hsteps_nogrp
                              refine wp_join0
                                (fun m367 => ∃ kb367, keep kb367 ∧
                                  (array (t := i32) pk kb367 ⋆ R) m367)
                                ?_ ?_
                              · intro _ m367 ⟨kb367, hk367, hm367⟩
                                c0_hsteps!; exact hJ361b m367 ⟨kb367, hk367, hm367⟩
                              · intro J367 hJ367
                                c0_hsplit
                                · c0_hsteps_nogrp
                                  refine wp_join0
                                    (fun m367b => ∃ kb367b, keep kb367b ∧
                                      (array (t := i32) pk kb367b ⋆ R) m367b)
                                    ?_ ?_
                                  · intro _ m367b ⟨kb367b, hk367b, hm367b⟩
                                    c0_hsteps!; exact hJ367 m367b ⟨kb367b, hk367b, hm367b⟩
                                  · intro J367b hJ367b
                                    c0_hsplit
                                    · have hnr : (kb361[18]'(by omega)).toNat < 128 := by
                                        simpa [Nat.reducePow, k6_c18] using hc
                                      have h18_eq : (BitVec.ofNat 64 18).toNat = 18 := rfl
                                      have h2784_c0 : (BitVec.setWidth 64 ((2784 : BitVec 32) +
                                          kb361[(BitVec.ofNat 64 18).toNat]'(by
                                            rw [h18_eq]; omega))).toNat < kb361.length := by
                                        rw [k6_get_congr (xs := kb361) h18_eq _ (by omega)]
                                        have := hnr; have := hlen; c0_bound
                                      have h2784_bd : (BitVec.setWidth 64 ((2784 : BitVec 32) +
                                          kb361[(BitVec.ofNat 64 18).toNat]'(by
                                            rw [h18_eq]; omega))).toNat =
                                          2784 + (kb361[18]'(by omega)).toNat := by
                                        rw [k6_get_congr (xs := kb361) h18_eq _ (by omega)]
                                        have := hnr; c0_bound
                                      c0_hsteps!
                                      refine hJ367b m ⟨_, ⟨?_, ?_⟩, hm⟩
                                      · rw [List.length_set, List.length_set, hk361_l]
                                      · intro idx hidx h16 h17 h18 h20 ha hb
                                        rw [List.getElem?_set_ne (by change 18 ≠ idx; omega),
                                          List.getElem?_set_ne (by rw [h2784_bd]; omega)]
                                        exact hk361.2 idx hidx h16 h17 h18 h20 ha hb
                                    · c0_hsteps!
                                      refine hJ367b m ⟨_, ⟨?_, ?_⟩, hm⟩
                                      · rw [List.length_set, hk361_l]
                                      · intro idx hidx h16 h17 h18 h20 ha hb
                                        rw [List.getElem?_set_ne (by change 18 ≠ idx; omega)]
                                        exact hk361.2 idx hidx h16 h17 h18 h20 ha hb
                                · c0_hsteps!; exact hJ367 m361 ⟨kb361, hk361, hm361⟩
                            · refine wp_join0
                                (fun m385 => ∃ kb385, keep kb385 ∧
                                  (array (t := i32) pk kb385 ⋆ R) m385)
                                ?_ ?_
                              · intro _ m385 ⟨kb385, hk385, hm385⟩
                                c0_hsteps!; exact hJ361b m385 ⟨kb385, hk385, hm385⟩
                              · intro J385 hJ385
                                c0_hsplit
                                · c0_hsteps!
                                  refine hJ385 m ⟨_, ⟨?_, ?_⟩, hm⟩
                                  · rw [List.length_set, hk361_l]
                                  · intro idx hidx h16 h17 h18 h20 ha hb
                                    rw [List.getElem?_set_ne (by change 20 ≠ idx; omega)]
                                    exact hk361.2 idx hidx h16 h17 h18 h20 ha hb
                                · c0_hsteps_nogrp
                                  refine wp_join0
                                    (fun m385b => ∃ kb385b, keep kb385b ∧
                                      (array (t := i32) pk kb385b ⋆ R) m385b)
                                    ?_ ?_
                                  · intro _ m385b ⟨kb385b, hk385b, hm385b⟩
                                    c0_hsteps!; exact hJ385 m385b ⟨kb385b, hk385b, hm385b⟩
                                  · intro J385b hJ385b
                                    c0_hsplit
                                    · have hnkl : (kb361[17]'(by omega)).toNat < 64 := by
                                        simpa [Nat.reducePow, k6_c17] using hc
                                      have h17_eq : (BitVec.ofNat 64 17).toNat = 17 := rfl
                                      have h544_c0 : (BitVec.setWidth 64 ((544 : BitVec 32) +
                                          kb361[(BitVec.ofNat 64 17).toNat]'(by
                                            rw [h17_eq]; omega))).toNat < kb361.length := by
                                        rw [k6_get_congr (xs := kb361) h17_eq _ (by omega)]
                                        have := hnkl; have := hlen; c0_bound
                                      have h544_bd : (BitVec.setWidth 64 ((544 : BitVec 32) +
                                          kb361[(BitVec.ofNat 64 17).toNat]'(by
                                            rw [h17_eq]; omega))).toNat =
                                          544 + (kb361[17]'(by omega)).toNat := by
                                        rw [k6_get_congr (xs := kb361) h17_eq _ (by omega)]
                                        have := hnkl; c0_bound
                                      c0_hsteps!
                                      refine hJ385b m ⟨_, ⟨?_, ?_⟩, hm⟩
                                      · rw [List.length_set, List.length_set, hk361_l]
                                      · intro idx hidx h16 h17 h18 h20 ha hb
                                        rw [List.getElem?_set_ne (by change 17 ≠ idx; omega),
                                          List.getElem?_set_ne (by rw [h544_bd]; omega)]
                                        exact hk361.2 idx hidx h16 h17 h18 h20 ha hb
                                    · c0_hsteps!; exact hJ385b m361 ⟨kb361, hk361, hm361⟩
                        · intro J361 hJ361
                          have h416_c0_idx : (BitVec.setWidth 64 ((416 : BitVec 32) +
                              (kbi[(BitVec.setWidth 64 ((2912 : BitVec 32) +
                                kbuf[(BitVec.setWidth 64 ((1888 : BitVec 32) + cid)).toNat]'(by
                                  rw [show (BitVec.setWidth 64 ((1888 : BitVec 32) + cid)).toNat =
                                    1888 + cid.toNat from h1888_idx]; omega) +
                                i)).toNat]'har_c0_bd >>> (1 : Nat)))).toNat =
                              416 + v.toNat := by
                            change (BitVec.setWidth 64 (416#32 +
                              (kbi[(BitVec.setWidth 64 (2912#32 +
                                kbuf[(BitVec.setWidth 64 (1888#32 + cid)).toNat]'(by
                                  rw [h1888_idx]; omega) +
                                i)).toNat]'har_c0_bd >>> (1 : Nat)))).toNat = 416 + v.toNat
                            rw [hl_c0_eq]
                            have := hv_lt; have := hnv_le; c0_bound
                          have hm1_eq := k6_set_congr (xs := kbi) h416_c0_idx
                            (congrArg (· ||| (2 : BitVec 32))
                              (k6_get_congr (xs := kbi) h416_c0_idx hv416_c0
                                (by have := hnv_le; omega)))
                          rw [hm1_eq] at hm
                          have hkbi1_ex : ∃ kbi1 : List (BitVec 32), kbi1.length = kbuf.length ∧
                              keep kbi1 ∧ (array (t := i32) pk kbi1 ⋆ R) m :=
                            ⟨kbi.set (416 + v.toNat)
                                ((kbi[416 + v.toNat]'(by have := hnv_le; omega)) ||| 2#32),
                              by simp [hki_l],
                              ⟨by simp [hki_l], fun idx hidx h16 h17 h18 h20 ha hb => by
                                rw [List.getElem?_set_ne (by have := hv_lt; have := hnv_le; omega)]
                                exact hki.2 idx hidx h16 h17 h18 h20 ha hb⟩, hm⟩
                          obtain ⟨kbi1, hk1_l, hki1, hm_n⟩ := hkbi1_ex
                          clear hm hm1_eq
                          try clear hv416_c0 h416_c0_idx hv32_c0 hv96_c0
                          try clear h2912_bd h1888_bd hget2 h2912_raw_idx hget1 h1888_mod h2912_mod
                          try clear hl_c0_eq h2912_c0_idx har_c0_bd hv_raw64 hv_div
                          try clear hv_lt hki hki_l hmi
                          have hm := hm_n; clear hm_n
                          have hkbi1_ge : 2912 ≤ kbi1.length := by rw [hk1_l]; exact hlen
                          c0_hsplit
                          · have hna : (kbi1[16]'(by omega)).toNat < 64 := by
                              simpa [Nat.reducePow, k6_c16] using hc
                            have h16_eq_c0 : (BitVec.ofNat (OfNat.ofNat 64)
                                (OfNat.ofNat 16)).toNat = 16 := rfl
                            have h16_bd_c0 : (BitVec.ofNat (OfNat.ofNat 64)
                                (OfNat.ofNat 16)).toNat < kbi1.length := by
                              rw [h16_eq_c0]; omega
                            have hk16_c0 : kbi1[(BitVec.ofNat (OfNat.ofNat 64)
                                (OfNat.ofNat 16)).toNat]'h16_bd_c0 = kbi1[16]'(by omega) :=
                              k6_get_congr (xs := kbi1) h16_eq_c0 h16_bd_c0 (by omega)
                            have h480_c0 : (BitVec.setWidth 64 ((480 : BitVec 32) +
                                kbi1[(BitVec.ofNat (OfNat.ofNat 64)
                                  (OfNat.ofNat 16)).toNat]'h16_bd_c0)).toNat < kbi1.length := by
                              rw [hk16_c0]; have := hna; c0_bound
                            have h480_bd : (BitVec.setWidth 64 ((480 : BitVec 32) +
                                kbi1[(BitVec.ofNat (OfNat.ofNat 64)
                                  (OfNat.ofNat 16)).toNat]'h16_bd_c0)).toNat =
                                480 + (kbi1[16]'(by omega)).toNat := by
                              rw [hk16_c0]; have := hna; c0_bound
                            c0_hsteps!
                            refine hJ361 m ⟨_, ⟨?_, ?_⟩, hm⟩
                            · rw [List.length_set, List.length_set, hk1_l]
                            · intro idx hidx h16 h17 h18 h20 ha hb
                              rw [List.getElem?_set_ne (by change 16 ≠ idx; omega),
                                List.getElem?_set_ne (by rw [h480_bd]; omega)]
                              exact hki1.2 idx hidx h16 h17 h18 h20 ha hb
                          · c0_hsteps!; exact hJ361 m ⟨kbi1, hki1, hm⟩
                      · c0_hsteps!; exact hJ349 mi ⟨kbi, hki, hmi⟩
                    · c0_hsteps!; exact hJ349 mi ⟨kbi, hki, hmi⟩
                  · c0_hsteps!; exact hJ349 mi ⟨kbi, hki, hmi⟩
              · c0_hsteps!; exact hQ kbi mi hki.1 hki.2 hmi
            · intro L hL; c0_hsteps!
              exact hL sz.toNat (0#32, ()) m1 ⟨kb1, hk1, Nat.zero_le _, by simp, hm1⟩
          · intro J343 hJ343
            c0_hsplit
            · have hnr : (kbuf[18]'(by omega)).toNat < 128 := by simpa [k6_c18] using hc
              have h18_eq : (BitVec.ofNat 64 18).toNat = 18 := rfl
              have h2784_bd : (BitVec.setWidth 64 ((2784 : BitVec 32) +
                  kbuf[(BitVec.ofNat 64 18).toNat]'(by rw [h18_eq]; omega))).toNat =
                  2784 + (kbuf[18]'(by omega)).toNat := by
                rw [k6_get_congr (xs := kbuf) h18_eq _ (by omega)]
                have := hnr; c0_bound
              c0_hsteps!
              refine hJ343 m ⟨_, ⟨?_, ?_⟩, hm⟩
              · rw [List.length_set, List.length_set]
              · intro idx hidx h16 h17 h18 h20 ha hb
                rw [List.getElem?_set_ne (by change 18 ≠ idx; omega),
                  List.getElem?_set_ne (by rw [h2784_bd]; omega)]
            · c0_hsteps!
              refine hJ343 m ⟨_, ⟨?_, ?_⟩, hm⟩
              · rw [List.length_set]
              · intro idx hidx h16 h17 h18 h20 ha hb
                rw [List.getElem?_set_ne (by change 18 ≠ idx; omega)]

private def CoreInv (kbuf : List (BitVec 32)) (nc : BitVec 32)
    (kb : List (BitVec 32)) : Prop :=
  K6BufOk kb ∧ kb.length = kbuf.length ∧
  (∀ idx < kbuf.length, (idx < 416 ∨ (480 ≤ idx ∧ idx < 2144) ∨ 2400 ≤ idx) →
    kb[idx]? = kbuf[idx]?) ∧
  (∀ cid < nc.toNat,
    let m0 := kbuf[2144 + cid]?.getD 0#32
    let m1 := kb[2144 + cid]?.getD 0#32
    (m1 &&& 0xFFFF#32) = (m0 &&& 0xFFFF#32) ∧
      (m1 &&& 0x40000000#32) = (m0 &&& 0x40000000#32))

private theorem coreInv_set_meta {kbuf : List (BitVec 32)} {nc : BitVec 32}
    (hnc_le : nc.toNat ≤ 256) {kb : List (BitVec 32)} (hik : CoreInv kbuf nc kb)
    {cid : Nat} (hcid : cid < nc.toNat) {v : BitVec 32}
    (hsz : (v &&& 0xFFFF#32) = ((kb[2144 + cid]?.getD 0#32) &&& 0xFFFF#32))
    (hlrn : (v &&& 0x40000000#32) = ((kb[2144 + cid]?.getD 0#32) &&& 0x40000000#32)) :
    CoreInv kbuf nc (kb.set (2144 + cid) v) := by
  refine ⟨k6BufOk_set_core_meta hik.1 (by omega) hsz hlrn, by simp [hik.2.1],
    fun idx hi hor => ?_, fun j hj => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hik.2.2.1 idx hi hor
  · by_cases heq : j = cid
    · subst heq
      have hk_l : 2144 + j < kb.length := by have := hik.1.base_ge; omega
      dsimp only
      rw [List.getElem?_set_self hk_l, Option.getD_some, hsz, hlrn]
      exact hik.2.2.2 j hj
    · rw [List.getElem?_set_ne (by omega)]; exact hik.2.2.2 j hj

private theorem coreInv_set_flags {kbuf : List (BitVec 32)} {nc : BitVec 32}
    {kb : List (BitVec 32)} (hik : CoreInv kbuf nc kb)
    {v : Nat} (hv : v < 64) (val : BitVec 32) :
    CoreInv kbuf nc (kb.set (416 + v) val) := by
  refine ⟨k6BufOk_set_flags hik.1 hv val, by simp [hik.2.1],
    fun idx hi hor => ?_, fun j hj => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hik.2.2.1 idx hi hor
  · rw [List.getElem?_set_ne (by omega)]; exact hik.2.2.2 j hj

private theorem k6_cid_sub_toNat {cid nc : BitVec 32} (hpos : 0 < cid.toNat)
    (hle : cid.toNat ≤ nc.toNat) (hnc : nc.toNat ≤ 256) :
    (cid - 1#32).toNat = cid.toNat - 1 := by
  rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega

private theorem k6_cid_sub_mod {cid nc : BitVec 32} (hpos : 0 < cid.toNat)
    (hle : cid.toNat ≤ nc.toNat) (hnc : nc.toNat ≤ 256) :
    (1888 + (2 ^ 32 - 1 + cid.toNat)) % 2 ^ 32 = 1888 + (cid - 1#32).toNat := by
  rw [k6_cid_sub_toNat hpos hle hnc]; omega

private theorem k6_2912_mod_eq {o s j na acap15 acap len : Nat}
    (hge : 2912 + acap15 ≤ len) (heq : acap15 = acap) (hl28 : len < 2 ^ 28)
    (hna : o + s + na ≤ acap) (hj : j < na) :
    (2912 + o + s + j) % 2 ^ 32 = 2912 + o + s + j :=
  Nat.mod_eq_of_lt (by omega)

private theorem k6_2144_lt {a nc l1 l2 : Nat} (ha : a < nc) (hnc : nc ≤ 256)
    (hl : 2912 ≤ l2) (heq : l1 = l2) : 2144 + a < l1 := by omega

private theorem k6_one_lt {l : Nat} (hl : 2912 ≤ l) : 1 < l := by omega

private theorem k6_sw64_add_2144 {a : BitVec 32} (ha : a.toNat < 256) :
    (BitVec.setWidth 64 (2144#32 + a)).toNat = 2144 + a.toNat := by c0_bound

private theorem k6_sw64_add_1888 {a : BitVec 32} (ha : a.toNat < 256) :
    (BitVec.setWidth 64 (1888#32 + a)).toNat = 1888 + a.toNat := by c0_bound

private theorem k6_1888_len_lt {i nc l : Nat} (hi : i < nc) (hnc : nc ≤ 256)
    (hl : 2912 ≤ l) : 1888 + i < l := by omega

private theorem k6_2144_len_lt {i nc l : Nat} (hi : i < nc) (hnc : nc ≤ 256)
    (hl : 2912 ≤ l) : 2144 + i < l := by omega

private theorem k6_add_mod_lt {c i nc : Nat} (hc : c ≤ 2144) (hi : i < nc)
    (hnc : nc ≤ 256) : (c + i) % 4294967296 = c + i := by omega

private def k6Dflt : (t : Ty) → Val t
  | .bool => false | .bits _ => 0 | .float _ => 0 | .pair a b => (k6Dflt a, k6Dflt b)
private def k6DfltT : (ts : List Ty) → Tup Val ts
  | [] => () | t :: r => (k6Dflt t, k6DfltT r)
private def k6SLet {L rs} : Expr Val L rs → Expr Val L rs
  | .let_ (ts := ts) _ k => k (k6DfltT ts) | _ => .hlt
private def k6SLd {L rs} (v : Val i32) : Expr Val L rs → Expr Val L rs
  | .load (.bits 32) _ k => k v | _ => .hlt
private def k6SJF {L rs} : Expr Val L rs → Expr Val L rs
  | .jnz _ _ e => e | _ => .hlt
private def k6SGrpB {rs} (x : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32]]) bs _ =>
      match bs ((fun _ _ => True), ()) with | .cons b _ => b (x, ())
  | _ => .hlt

private def k6FixpointE (pk : BitVec 64) (nc nv acap : BitVec 32) : Expr Val Cont [] :=
  let e := k6SLd nc (k6SLet (k6SLet (k6SLet (full_k6_core_m7_body Val Cont (pk, ())))))
  let e := k6SJF (k6SLet (k6SJF (k6SLet (k6SLd acap (k6SLet (k6SLet (k6SLet
    (k6SLd nv (k6SLet (k6SLet (k6SLet e)))))))))))
  let e := k6SLd 0#32 (k6SLet (k6SLet (k6SLet (k6SJF (k6SLet (k6SGrpB nc e))))))
  k6SGrpB 0#32 e

private theorem k6_core_fixpoint_wp {Γ : Env} {pk : BitVec 64} {kbuf : List (BitVec 32)}
    {nc nv acap : BitVec 32} {R : Mem 64 → Prop} {Q : Post []} {X : XPost}
    (hlen : 2912 ≤ kbuf.length) (hnc_def : nc = kbuf[1]'(by omega))
    (hacap_def : acap = kbuf[15]'(by omega))
    (hnc_le : nc.toNat ≤ 256) (hnv_le : nv.toNat ≤ 64)
    (hRet : ∀ kbp mp, CoreInv kbuf nc kbp → (array (t := i32) pk kbp ⋆ R) mp → Q () mp)
    {kbj : List (BitVec 32)} {mj : Mem 64}
    (hkj : CoreInv kbuf nc kbj) (hmj : (array (t := i32) pk kbj ⋆ R) mj) :
    wp Γ Q X (k6FixpointE pk nc nv acap) mj := by
  let invCore := CoreInv kbuf nc
  have invCore_set_meta := @coreInv_set_meta kbuf nc hnc_le
  dsimp only [k6FixpointE, k6SLet, k6SLd, k6SJF, k6SGrpB, k6DfltT, k6Dflt]
  {
            c0_hsteps_nogrp
            refine wp_loop_group (ts := [i32, .bool])
              (fun rem (pass, _ch, ()) mp => ∃ kbp, invCore kbp ∧ pass.toNat ≤ nc.toNat ∧
                rem = nc.toNat - pass.toNat ∧ (array (t := i32) pk kbp ⋆ R) mp)
              ?_ ?_
            · rintro Lp remp ⟨pass, ch, ⟨⟩⟩ mp hLp ⟨kbp, hkp, hpass_le, rfl, hmp⟩
              c0_hsplit
              · clear hc
                c0_hsplit
                · have hpass_lt : pass.toNat < nc.toNat := hc
                  clear hc
                  have hpass1 : (pass + 1#32).toNat = pass.toNat + 1 := by
                    have := hnc_le; have := hpass_lt; c0_bound
                  c0_hsteps_nogrp
                  refine wp_loop_group (ts := [.bool, i32])
                    (fun rem (_chc, cid_c, ()) mc => ∃ kbc, invCore kbc ∧
                      cid_c.toNat ≤ nc.toNat ∧ rem = cid_c.toNat ∧
                      (array (t := i32) pk kbc ⋆ R) mc)
                    ?_ ?_
                  · rintro Lc remc ⟨ch_c, cid_c, ⟨⟩⟩ mc hLc ⟨kbc, hkc, hc_le, rfl, hmc⟩
                    have hkc_l := hkc.2.1
                    c0_hsplit
                    · have hcid_pos : 0 < cid_c.toNat := hc
                      clear hc
                      have hcid1_lt : (cid_c - 1#32).toNat < nc.toNat := by
                        rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
                        have := hcid_pos; have := hc_le; have := hnc_le; omega
                      let c_i := cid_c - 1#32
                      have hc_i_lt : c_i.toNat < nc.toNat := hcid1_lt
                      have hbd_c : 2144 + c_i.toNat < kbc.length := by
                        have := hkc_l; have := hlen; have := hnc_le; have := hc_i_lt; omega
                      have hc_2144_idx : (BitVec.setWidth 64
                          ((2144 : BitVec 32) + (cid_c - (1 : BitVec 32)))).toNat =
                          2144 + c_i.toNat :=
                        k6_sw64_add_2144 (Nat.lt_of_lt_of_le hc_i_lt hnc_le)
                      have hbd_c_c0 : (BitVec.setWidth 64
                          ((2144 : BitVec 32) + (cid_c - (1 : BitVec 32)))).toNat <
                          kbc.length := by
                        rw [hc_2144_idx]; exact hbd_c
                      let cm := kbc[2144 + c_i.toNat]'hbd_c
                      c0_hsteps_nogrp
                      refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool)
                        (fun x => x.2)
                        (fun x mc' => invCore x.1 ∧ (array (t := i32) pk x.1 ⋆ R) mc') ?_ ?_
                      · rintro _ ⟨kbc', ch'⟩ mc' ⟨hkc', hmc'⟩
                        c0_hsteps!
                        exact hLc (cid_c - 1#32).toNat (ch', cid_c - 1#32, ()) mc'
                          (by rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
                              have := hcid_pos; have := hc_le; have := hnc_le; omega)
                          ⟨kbc', hkc', by omega, rfl, hmc'⟩
                      · intro Jcid hJcid
                        have hc_2144_mod : (BitVec.toNat (2144 : BitVec 32) +
                            (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + cid_c.toNat)) %
                            2 ^ 32 = 2144 + c_i.toNat := by
                          change (2144 + (2 ^ 32 - 1 + cid_c.toNat)) % 2 ^ 32 =
                            2144 + (cid_c - 1#32).toNat
                          rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
                          have := hcid_pos; have := hc_le; have := hnc_le; omega
                        have hbd_1888 : 1888 + c_i.toNat < kbc.length := by
                          have := hkc_l; have := hlen; have := hnc_le; have := hc_i_lt; omega
                        have hc_1888_idx : (BitVec.setWidth 64
                            ((1888 : BitVec 32) + (cid_c - (1 : BitVec 32)))).toNat =
                            1888 + c_i.toNat :=
                          k6_sw64_add_1888 (Nat.lt_of_lt_of_le hc_i_lt hnc_le)
                        have hbd_1888_c0 : (BitVec.setWidth 64
                            ((1888 : BitVec 32) + (cid_c - (1 : BitVec 32)))).toNat <
                            kbc.length := by
                          rw [hc_1888_idx]; exact hbd_1888
                        c0_hsplit
                        · clear hc
                          let off_c := kbc[1888 + c_i.toNat]'hbd_1888
                          let sz_c := cm &&& 0xFFFF#32
                          have hlt28 := hkc.1.length_lt
                          have hlen_ge := hkc.1.length_ge
                          have h15 := hkc.2.2.1 15 (by omega) (Or.inl (by omega))
                          have h15_eq : kbc[15]'(by omega) = acap := by
                            rw [List.getElem?_eq_getElem (by omega),
                              List.getElem?_eq_getElem (by omega)] at h15
                            rw [hacap_def]; exact Option.some.inj h15
                          have h15' : (kbc[15]?.getD 0#32).toNat = acap.toNat := by
                            rw [k6_buf_get_eq (by omega), h15_eq]
                          have hkcl := hkc.1.clause_ok (by
                            have h1eq := hkc.2.2.1 1 (by omega) (Or.inl (by omega))
                            rw [List.getElem?_eq_getElem (by omega),
                              List.getElem?_eq_getElem (by omega)] at h1eq
                            have : (kbc[1]'(by omega)) = nc := by
                              rw [hnc_def]; exact Option.some.inj h1eq
                            rw [k6_buf_get_eq (by omega), this]; exact hc_i_lt)
                          have hno_ov1 : off_c.toNat + sz_c.toNat < 2 ^ 32 := by
                            have h1 := hkcl.1
                            rw [k6_buf_get_eq hbd_1888, k6_buf_get_eq hbd_c] at h1
                            dsimp only [off_c, sz_c, cm] at h1 ⊢
                            have := hlt28; have := hlen_ge; have := h15'; omega
                          have hc_1888_mod : (BitVec.toNat (1888 : BitVec 32) +
                              (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + cid_c.toNat)) %
                              2 ^ 32 = 1888 + c_i.toNat := by
                            change (1888 + (2 ^ 32 - 1 + cid_c.toNat)) % 2 ^ 32 =
                              1888 + c_i.toNat
                            exact k6_cid_sub_mod hcid_pos hc_le hnc_le
                          have hget_1888 : kbc[(BitVec.toNat (1888 : BitVec 32) +
                              (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + cid_c.toNat)) %
                              2 ^ 32]'(by rw [hc_1888_mod]; exact hbd_1888) = off_c :=
                            k6_get_congr hc_1888_mod _ hbd_1888
                          have hget_2144 : kbc[(BitVec.toNat (2144 : BitVec 32) +
                              (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + cid_c.toNat)) %
                              2 ^ 32]'(by rw [hc_2144_mod]; exact hbd_c) = cm :=
                            k6_get_congr hc_2144_mod _ hbd_c
                          have hget_1888_c0 : kbc[(BitVec.setWidth 64 ((1888 : BitVec 32) +
                              (cid_c - (1 : BitVec 32)))).toNat]'hbd_1888_c0 = off_c :=
                            k6_get_congr hc_1888_idx hbd_1888_c0 hbd_1888
                          have hget_2144_c0 : kbc[(BitVec.setWidth 64 ((2144 : BitVec 32) +
                              (cid_c - (1 : BitVec 32)))).toNat]'hbd_c_c0 = cm :=
                            k6_get_congr hc_2144_idx hbd_c_c0 hbd_c
                          c0_hsteps_nogrp
                          refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool)
                            (fun x => x.2)
                            (fun x mc' => invCore x.1 ∧ (array (t := i32) pk x.1 ⋆ R) mc')
                            ?_ ?_
                          · rintro _ ⟨kbc', ch'⟩ mc' ⟨hkc', hmc'⟩
                            c0_hsteps!; exact hJcid (kbc', ch') mc' ⟨hkc', hmc'⟩
                          · intro Jbr hJbr
                            c0_hsplit
                            · have hlrn_cm :
                                  (kbc[2144 + c_i.toNat]?.getD 0#32 &&& 0x40000000#32) ≠ 0#32 := by
                                have hraw : (kbc[(BitVec.toNat (2144 : BitVec 32) +
                                    (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + cid_c.toNat)) %
                                    2 ^ 32]'(by rw [hc_2144_mod]; exact hbd_c) &&&
                                    1073741824#32) ≠ 0#32 := hc
                                rw [k6_buf_get_eq hbd_c]
                                rw [k6_get_congr hc_2144_mod (by omega) hbd_c] at hraw
                                exact hraw
                              clear hc
                              have hbd_2400 : 2400 + c_i.toNat < kbc.length := by
                                have := hkc_l; have := hlen; have := hnc_le
                                have := hc_i_lt; omega
                              have hc_2400_idx : (BitVec.setWidth 64
                                  ((2400 : BitVec 32) + (cid_c - (1 : BitVec 32)))).toNat =
                                  2400 + c_i.toNat := by
                                change (BitVec.setWidth 64 (2400#32 + c_i)).toNat = 2400 + c_i.toNat
                                have := hnc_le; have := hc_i_lt; c0_bound
                              have hbd_2400_c0 : (BitVec.setWidth 64
                                  ((2400 : BitVec 32) + (cid_c - (1 : BitVec 32)))).toNat <
                                  kbc.length := by
                                rw [hc_2400_idx]; exact hbd_2400
                              let na_c := kbc[2400 + c_i.toNat]'hbd_2400
                              have hoff_na' :
                                  off_c.toNat + sz_c.toNat + na_c.toNat ≤ acap.toNat := by
                                have h2 := hkcl.2 hlrn_cm
                                rw [k6_buf_get_eq hbd_1888, k6_buf_get_eq hbd_c,
                                  k6_buf_get_eq hbd_2400, k6_buf_get_eq (by omega)] at h2
                                dsimp only [off_c, sz_c, na_c, cm] at h2 ⊢
                                rw [h15_eq] at h2; exact h2
                              have hno_ov2 : off_c.toNat + sz_c.toNat + na_c.toNat < 2 ^ 32 := by
                                have := hlt28; have := hlen_ge; have := h15'; omega
                              c0_hsteps_nogrp
                              refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool)
                                (fun x => x.2)
                                (fun x mc' => invCore x.1 ∧ (array (t := i32) pk x.1 ⋆ R) mc')
                                ?_ ?_
                              · rintro _ ⟨kbc', ch'⟩ mc' ⟨hkc', hmc'⟩
                                c0_hsteps!; exact hJbr (kbc', ch') mc' ⟨hkc', hmc'⟩
                              · intro J805 hJ805
                                c0_hsplit
                                · clear hc
                                  have hc_2400_mod :
                                      (BitVec.toNat (2400 : BitVec 32) +
                                        (2 ^ 32 - BitVec.toNat (1 : BitVec 32) +
                                          cid_c.toNat)) % 2 ^ 32 = 2400 + c_i.toNat := by
                                    change (2400 + (2 ^ 32 - 1 + cid_c.toNat)) % 2 ^ 32 =
                                      2400 + (cid_c - 1#32).toNat
                                    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
                                    have := hcid_pos; have := hc_le; have := hnc_le; omega
                                  c0_hsteps_nogrp
                                  refine wp_loop_group (ts := [.bool, i32])
                                    (fun remj (_chj, j_c, ()) mj2 => ∃ kbj2, invCore kbj2 ∧
                                      j_c.toNat ≤ na_c.toNat ∧ remj = na_c.toNat - j_c.toNat ∧
                                      (array (t := i32) pk kbj2 ⋆ R) mj2)
                                    ?_ ?_
                                  · rintro Lj remj ⟨ch_j, j_c, ⟨⟩⟩ mj2 hLj
                                      ⟨kbj2, hkj2, hj_le, rfl, hmj2⟩
                                    have hkj2_l := hkj2.2.1
                                    c0_hsplit
                                    · have hj_lt : j_c.toNat < na_c.toNat := by
                                        rw [k6_get_congr hc_2400_mod (by omega) hbd_2400] at hc
                                        exact hc
                                      clear hc
                                      have hj1 : (j_c + 1#32).toNat = j_c.toNat + 1 := by
                                        have := hlt28; have := hlen_ge; have := h15'
                                        have := hoff_na'; have := hj_lt; c0_bound
                                      have hidx_lt :
                                          2912 + off_c.toNat + sz_c.toNat + j_c.toNat <
                                            kbj2.length := by
                                        have := hkj2_l; have := hlt28; have := hlen_ge; have := h15'
                                        have := hoff_na'; have := hj_lt; omega
                                      have hidx_c0_lt : (BitVec.setWidth 64 ((2912 : BitVec 32) +
                                          kbc[(BitVec.setWidth 64 ((1888 : BitVec 32) +
                                            (cid_c - (1 : BitVec 32)))).toNat]'hbd_1888_c0 +
                                          (kbc[(BitVec.setWidth 64 ((2144 : BitVec 32) +
                                            (cid_c - (1 : BitVec 32)))).toNat]'hbd_c_c0 &&&
                                            (65535 : BitVec 32)) +
                                          j_c)).toNat < kbj2.length := by
                                        rw [hget_1888_c0, hget_2144_c0]
                                        change (BitVec.setWidth 64
                                          (2912#32 + off_c + sz_c + j_c)).toNat < kbj2.length
                                        have := hidx_lt; have := hno_ov1; have := hno_ov2
                                        have := hlt28; have := hlen_ge; have := h15'
                                        have := hoff_na'; have := hj_lt; c0_bound
                                      let ant := kbj2[2912 + off_c.toNat + sz_c.toNat +
                                        j_c.toNat]'hidx_lt
                                      have hant_c0_eq : kbj2[(BitVec.setWidth 64 ((2912 : BitVec 32)
                                          + kbc[(BitVec.setWidth 64 ((1888 : BitVec 32) +
                                            (cid_c - (1 : BitVec 32)))).toNat]'hbd_1888_c0 +
                                          (kbc[(BitVec.setWidth 64 ((2144 : BitVec 32) +
                                            (cid_c - (1 : BitVec 32)))).toNat]'hbd_c_c0 &&&
                                            (65535 : BitVec 32)) +
                                          j_c)).toNat]'hidx_c0_lt = ant := by
                                        refine k6_get_congr ?_ hidx_c0_lt hidx_lt
                                        rw [hget_1888_c0, hget_2144_c0]
                                        change (BitVec.setWidth 64
                                          (2912#32 + off_c + sz_c + j_c)).toNat =
                                          2912 + off_c.toNat + sz_c.toNat + j_c.toNat
                                        have := hidx_lt; have := hno_ov1; have := hno_ov2
                                        have := hlt28; have := hlen_ge; have := h15'
                                        have := hoff_na'; have := hj_lt; c0_bound
                                      c0_hsteps_nogrp
                                      refine wp_join_state1 (t := .bool)
                                        (α := List (BitVec 32) × Bool) (fun x => x.2)
                                        (fun x mj3 => invCore x.1 ∧
                                          (array (t := i32) pk x.1 ⋆ R) mj3)
                                        ?_ ?_
                                      · rintro _ ⟨kbj3, chj3⟩ mj3 ⟨hkj3, hmj3⟩
                                        c0_hsteps!
                                        exact hLj (na_c.toNat - (j_c + 1#32).toNat)
                                          (chj3, j_c + 1#32, ()) mj3 (by have := hj1; omega)
                                          ⟨kbj3, hkj3, by omega, rfl, hmj3⟩
                                      · intro Jant hJant
                                        have hc_2912_mod : (BitVec.toNat (2912 : BitVec 32) +
                                            (kbc[(BitVec.toNat (1888 : BitVec 32) +
                                              (2 ^ 32 - BitVec.toNat (1 : BitVec 32) +
                                                cid_c.toNat)) % 2 ^ 32]'(by
                                                  rw [hc_1888_mod]; exact hbd_1888)).toNat +
                                            ((kbc[(BitVec.toNat (2144 : BitVec 32) +
                                              (2 ^ 32 - BitVec.toNat (1 : BitVec 32) +
                                                cid_c.toNat)) % 2 ^ 32]'(by
                                                  rw [hc_2144_mod]; exact hbd_c) &&& 65535).toNat) +
                                            j_c.toNat) % 2 ^ 32 =
                                            2912 + off_c.toNat + sz_c.toNat + j_c.toNat := by
                                          rw [hget_1888, hget_2144]
                                          change (2912 + off_c.toNat + sz_c.toNat + j_c.toNat) %
                                            2 ^ 32 = 2912 + off_c.toNat + sz_c.toNat + j_c.toNat
                                          exact k6_2912_mod_eq hlen_ge h15' hlt28 hoff_na' hj_lt
                                        have hget_ant : kbj2[(BitVec.toNat (2912 : BitVec 32) +
                                            (kbc[(BitVec.toNat (1888 : BitVec 32) +
                                              (2 ^ 32 - BitVec.toNat (1 : BitVec 32) +
                                                cid_c.toNat)) % 2 ^ 32]'(by
                                                  rw [hc_1888_mod]; exact hbd_1888)).toNat +
                                            ((kbc[(BitVec.toNat (2144 : BitVec 32) +
                                              (2 ^ 32 - BitVec.toNat (1 : BitVec 32) +
                                                cid_c.toNat)) % 2 ^ 32]'(by
                                                  rw [hc_2144_mod]; exact hbd_c) &&& 65535).toNat) +
                                            j_c.toNat) % 2 ^ 32]'(by
                                              rw [hc_2912_mod]; exact hidx_lt) = ant :=
                                          k6_get_congr hc_2912_mod _ hidx_lt
                                        c0_hsplit
                                        · have hant_lt : ant.toNat < nc.toNat := by
                                            rw [← hget_ant]; simpa [k6_c1] using hc
                                          clear hc
                                          let olda := kbj2[2144 + ant.toNat]'(
                                            k6_2144_lt hant_lt hnc_le hlen hkj2_l)
                                          have hpa := k6_km_core_or_pres olda
                                          have h2144_a_idx : (BitVec.setWidth 64
                                              ((2144 : BitVec 32) + kbj2[(BitVec.setWidth 64
                                                ((2912 : BitVec 32) + kbc[(BitVec.setWidth 64
                                                  ((1888 : BitVec 32) +
                                                    (cid_c - (1 : BitVec 32)))).toNat]'hbd_1888_c0
                                                + (kbc[(BitVec.setWidth 64 ((2144 : BitVec 32) +
                                                  (cid_c - (1 : BitVec 32)))).toNat]'hbd_c_c0 &&&
                                                  (65535 : BitVec 32)) +
                                                j_c)).toNat]'hidx_c0_lt)).toNat =
                                              2144 + ant.toNat := by
                                            rw [hant_c0_eq]
                                            exact k6_sw64_add_2144
                                              (Nat.lt_of_lt_of_le hant_lt hnc_le)
                                          have h2144_a_c0 : (BitVec.setWidth 64
                                              ((2144 : BitVec 32) + kbj2[(BitVec.setWidth 64
                                                ((2912 : BitVec 32) + kbc[(BitVec.setWidth 64
                                                  ((1888 : BitVec 32) +
                                                    (cid_c - (1 : BitVec 32)))).toNat]'hbd_1888_c0
                                                + (kbc[(BitVec.setWidth 64 ((2144 : BitVec 32) +
                                                  (cid_c - (1 : BitVec 32)))).toNat]'hbd_c_c0 &&&
                                                  (65535 : BitVec 32)) +
                                                j_c)).toNat]'hidx_c0_lt)).toNat <
                                              kbj2.length := by
                                            rw [h2144_a_idx]
                                            exact k6_2144_lt hant_lt hnc_le hlen hkj2_l
                                          c0_hsplit
                                          · clear hc; c0_hsteps!
                                            have hm_eq := k6_set_congr (xs := kbj2) h2144_a_idx
                                              (congrArg (· ||| (536870912 : BitVec 32))
                                                (k6_get_congr (xs := kbj2) h2144_a_idx h2144_a_c0
                                                  (k6_2144_lt hant_lt hnc_le hlen hkj2_l)))
                                            rw [hm_eq] at hm; dsimp only [olda] at hpa hm
                                            rw [← k6_buf_get_eq (kbuf := kbj2)
                                              (i := 2144 + ant.toNat)
                                              (k6_2144_lt hant_lt hnc_le hlen hkj2_l)] at hpa hm
                                            exact hJant (_, true) m
                                              ⟨invCore_set_meta hkj2 hant_lt hpa.1 hpa.2, hm⟩
                                          · c0_hsteps!; exact hJant (kbj2, ch_j) mj2 ⟨hkj2, hmj2⟩
                                        · c0_hsteps!; exact hJant (kbj2, ch_j) mj2 ⟨hkj2, hmj2⟩
                                    · c0_hsteps!; exact hJ805 (kbj2, ch_j) mj2 ⟨hkj2, hmj2⟩
                                  · intro Lj hLj; c0_hsteps!
                                    exact hLj na_c.toNat (ch_c, 0#32, ()) mc
                                      ⟨kbc, hkc, Nat.zero_le _, by simp, hmc⟩
                                · c0_hsteps!; exact hJ805 (kbc, ch_c) mc ⟨hkc, hmc⟩
                            · clear hc; c0_hsteps_nogrp
                              refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool)
                                (fun x => x.2)
                                (fun x mc' => invCore x.1 ∧ (array (t := i32) pk x.1 ⋆ R) mc')
                                ?_ ?_
                              · rintro _ ⟨kbc', ch'⟩ mc' ⟨hkc', hmc'⟩
                                c0_hsteps!; exact hJbr (kbc', ch') mc' ⟨hkc', hmc'⟩
                              · intro Jelse hJelse; c0_hsplit
                                · clear hc
                                  have hoff_sz : off_c.toNat + sz_c.toNat ≤ acap.toNat := by
                                    have h1 := hkcl.1; dsimp only [off_c, sz_c, cm] at h1 ⊢
                                    rw [k6_buf_get_eq hbd_1888, k6_buf_get_eq hbd_c,
                                      k6_buf_get_eq (by omega), h15_eq] at h1
                                    exact h1
                                  c0_hsteps_nogrp
                                  refine wp_loop_group (ts := [.bool, i32])
                                    (fun remj (_chj, j_c, ()) mj => ∃ kbj, invCore kbj ∧
                                      j_c.toNat ≤ sz_c.toNat ∧ remj = sz_c.toNat - j_c.toNat ∧
                                      (array (t := i32) pk kbj ⋆ R) mj)
                                    ?_ ?_
                                  · rintro Lj remj ⟨ch_j, j_c, ⟨⟩⟩ mj hLj
                                      ⟨kbj, hkj, hj_le, rfl, hmj⟩
                                    have hkj_l := hkj.2.1; c0_hsplit
                                    · have hj_lt : j_c.toNat < sz_c.toNat := by
                                        rw [hget_2144] at hc; exact hc
                                      clear hc
                                      have hsz_lt : sz_c.toNat < 65536 := by
                                        dsimp only [sz_c]; rw [BitVec.toNat_and]
                                        exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                                      have hj1 : (j_c + 1#32).toNat = j_c.toNat + 1 := by
                                        have := hsz_lt; have := hj_lt; c0_bound
                                      have hidx_lt :
                                          2912 + off_c.toNat + j_c.toNat < kbj.length := by
                                        have := hkj_l; have := hlt28; have := hlen_ge
                                        have := h15'; omega
                                      have hidx_c0 : (BitVec.setWidth 64 ((2912 : BitVec 32) +
                                          kbc[(BitVec.setWidth 64 ((1888 : BitVec 32) +
                                            (cid_c - (1 : BitVec 32)))).toNat]'hbd_1888_c0 +
                                          j_c)).toNat = 2912 + off_c.toNat + j_c.toNat := by
                                        rw [hget_1888_c0]; have := hidx_lt; have := hno_ov1
                                        have := hlt28; have := hlen_ge; have := h15'
                                        have := hoff_sz; c0_bound
                                      have hidx_c0_lt : (BitVec.setWidth 64 ((2912 : BitVec 32) +
                                          kbc[(BitVec.setWidth 64 ((1888 : BitVec 32) +
                                            (cid_c - (1 : BitVec 32)))).toNat]'hbd_1888_c0 +
                                          j_c)).toNat < kbj.length := by
                                        rw [hidx_c0]; exact hidx_lt
                                      c0_hsteps_nogrp
                                      refine wp_join_state1 (t := .bool)
                                        (α := List (BitVec 32) × Bool) (fun x => x.2)
                                        (fun x mj' => invCore x.1 ∧
                                          (array (t := i32) pk x.1 ⋆ R) mj') ?_ ?_
                                      · rintro _ ⟨kbj', chj'⟩ mj' ⟨hkj', hmj'⟩; c0_hsteps!
                                        exact hLj (sz_c.toNat - (j_c + 1#32).toNat)
                                          (chj', j_c + 1#32, ()) mj' (by have := hj1; omega)
                                          ⟨kbj', hkj', by omega, rfl, hmj'⟩
                                      · intro Jlv hJlv
                                        let lv := (kbj[2912 + off_c.toNat + j_c.toNat]'hidx_lt) >>>
                                          (1 : Nat)
                                        have hget_lv_c0 : kbj[(BitVec.setWidth 64
                                            ((2912 : BitVec 32) + kbc[(BitVec.setWidth 64
                                              ((1888 : BitVec 32) +
                                                (cid_c - (1 : BitVec 32)))).toNat]'hbd_1888_c0 +
                                            j_c)).toNat]'hidx_c0_lt =
                                            kbj[2912 + off_c.toNat + j_c.toNat]'hidx_lt :=
                                          k6_get_congr hidx_c0 _ _
                                        c0_hsplit
                                        · have har_mod : (BitVec.toNat (2912 : BitVec 32) +
                                              (kbc[(BitVec.toNat (1888 : BitVec 32) +
                                                (2 ^ 32 - BitVec.toNat (1 : BitVec 32) +
                                                  cid_c.toNat)) % 2 ^ 32]'(by
                                                    rw [hc_1888_mod]; exact hbd_1888)).toNat +
                                              j_c.toNat) % 2 ^ 32 =
                                              2912 + off_c.toNat + j_c.toNat := by
                                            rw [hget_1888]; change (2912 + off_c.toNat +
                                              j_c.toNat) % 2 ^ 32 = 2912 + off_c.toNat + j_c.toNat
                                            have := hidx_lt; have := hlt28; omega
                                          have hlv_lt : lv.toNat < nv.toNat := by
                                            dsimp only [lv]; rw [BitVec.toNat_ushiftRight,
                                              Nat.shiftRight_eq_div_pow, ← k6_get_congr har_mod
                                              (by rw [har_mod]; exact hidx_lt) hidx_lt]
                                            simpa [Nat.reducePow] using hc
                                          clear hc
                                          have h32_c0 : (BitVec.setWidth 64 ((32 : BitVec 32) +
                                              ((kbj[(BitVec.setWidth 64 ((2912 : BitVec 32) +
                                                kbc[(BitVec.setWidth 64 ((1888 : BitVec 32) +
                                                  (cid_c - (1 : BitVec 32)))).toNat]'hbd_1888_c0 +
                                                j_c)).toNat]'hidx_c0_lt) >>>
                                              (1 : Nat)))).toNat < kbj.length := by
                                            rw [hget_lv_c0]
                                            change (BitVec.setWidth 64 ((32 : BitVec 32) +
                                              lv)).toNat < kbj.length
                                            have := hlv_lt; have := hnv_le
                                            have := hkj_l; have := hlen; c0_bound
                                          c0_hsplit
                                          · clear hc
                                            have h96_c0 : (BitVec.setWidth 64 ((96 : BitVec 32) +
                                                ((kbj[(BitVec.setWidth 64 ((2912 : BitVec 32) +
                                                  kbc[(BitVec.setWidth 64 ((1888 : BitVec 32) +
                                                    (cid_c - (1 : BitVec 32)))).toNat]'hbd_1888_c0 +
                                                  j_c)).toNat]'hidx_c0_lt) >>>
                                                (1 : Nat)))).toNat < kbj.length := by
                                              rw [hget_lv_c0]
                                              change (BitVec.setWidth 64 ((96 : BitVec 32) +
                                                lv)).toNat < kbj.length
                                              have := hlv_lt; have := hnv_le
                                              have := hkj_l; have := hlen; c0_bound
                                            let r0 := kbj[96 + lv.toNat]'(by
                                              have := hlv_lt; have := hnv_le
                                              have := hkj_l; have := hlen; omega)
                                            have hr0_c0_eq : kbj[(BitVec.setWidth 64 ((96 :
                                                BitVec 32) + ((kbj[(BitVec.setWidth 64
                                                  ((2912 : BitVec 32) + kbc[(BitVec.setWidth 64
                                                    ((1888 : BitVec 32) +
                                                      (cid_c - (1 : BitVec 32)))).toNat]'hbd_1888_c0
                                                    + j_c)).toNat]'hidx_c0_lt) >>>
                                                  (1 : Nat)))).toNat]'h96_c0 = r0 := by
                                              refine k6_get_congr ?_ h96_c0 _
                                              rw [hget_lv_c0]
                                              change (BitVec.setWidth 64 ((96 : BitVec 32) +
                                                lv)).toNat = 96 + lv.toNat
                                              have := hlv_lt; have := hnv_le; c0_bound
                                            c0_hsteps_nogrp
                                            refine wp_join_state1 (t := .bool)
                                              (α := List (BitVec 32) × Bool) (fun x => x.2)
                                              (fun x mj' => invCore x.1 ∧
                                                (array (t := i32) pk x.1 ⋆ R) mj') ?_ ?_
                                            · rintro _ ⟨kbj', chj'⟩ mj' ⟨hkj', hmj'⟩
                                              c0_hsteps!; exact hJlv (kbj', chj') mj' ⟨hkj', hmj'⟩
                                            · intro Jr0 hJr0
                                              have h96_mod : (BitVec.toNat (96 : BitVec 32) +
                                                  (kbj[(BitVec.toNat (2912 : BitVec 32) +
                                                    (kbc[(BitVec.toNat (1888 : BitVec 32) +
                                                      (2 ^ 32 - BitVec.toNat (1 : BitVec 32) +
                                                        cid_c.toNat)) % 2 ^ 32]'(by
                                                          rw [hc_1888_mod]; exact hbd_1888)).toNat +
                                                    j_c.toNat) % 2 ^ 32]'(by
                                                      rw [har_mod]; exact hidx_lt)).toNat / 2) %
                                                  2 ^ 32 = 96 + lv.toNat := by
                                                rw [k6_get_congr har_mod _ hidx_lt]
                                                change (96 + (kbj[2912 + off_c.toNat +
                                                  j_c.toNat]'hidx_lt).toNat / 2) % 2 ^ 32 =
                                                  96 + lv.toNat
                                                dsimp only [lv]; rw [BitVec.toNat_ushiftRight,
                                                  Nat.shiftRight_eq_div_pow]
                                                have := hlv_lt; have := hnv_le; omega
                                              have hget_r0_raw : kbj[(BitVec.toNat (96 :
                                                  BitVec 32) + (kbj[(BitVec.toNat (2912 : BitVec 32)
                                                    + (kbc[(BitVec.toNat (1888 : BitVec 32) +
                                                      (2 ^ 32 - BitVec.toNat (1 : BitVec 32) +
                                                        cid_c.toNat)) % 2 ^ 32]'(by
                                                          rw [hc_1888_mod]; exact hbd_1888)).toNat +
                                                    j_c.toNat) % 2 ^ 32]'(by
                                                      rw [har_mod]; exact hidx_lt)).toNat / 2) %
                                                  2 ^ 32]'(by
                                                    rw [h96_mod]; have := hlv_lt; have := hnv_le
                                                    have := hkj_l; have := hlen; omega) = r0 :=
                                                k6_get_congr h96_mod _ _
                                              c0_hsplit
                                              · have hr0_lt : r0.toNat < nc.toNat := by
                                                  rw [← hget_r0_raw]; simpa [k6_c1] using hc
                                                clear hc
                                                let oldr := kbj[2144 + r0.toNat]'(
                                                  k6_2144_lt hr0_lt hnc_le hlen hkj_l)
                                                have hpr := k6_km_core_or_pres oldr
                                                have h2144_r_idx : (BitVec.setWidth 64
                                                    ((2144 : BitVec 32) + kbj[(BitVec.setWidth 64
                                                      ((96 : BitVec 32) + ((kbj[(BitVec.setWidth 64
                                                        ((2912 : BitVec 32) + kbc[(BitVec.setWidth
                                                          64 ((1888 : BitVec 32) + (cid_c -
                                                            (1 : BitVec 32)))).toNat]'hbd_1888_c0
                                                        + j_c)).toNat]'hidx_c0_lt) >>>
                                                        (1 : Nat)))).toNat]'h96_c0)).toNat =
                                                    2144 + r0.toNat := by
                                                  rw [hr0_c0_eq]
                                                  exact k6_sw64_add_2144
                                                    (Nat.lt_of_lt_of_le hr0_lt hnc_le)
                                                have h2144_r_c0 : (BitVec.setWidth 64
                                                    ((2144 : BitVec 32) + kbj[(BitVec.setWidth 64
                                                      ((96 : BitVec 32) + ((kbj[(BitVec.setWidth 64
                                                        ((2912 : BitVec 32) + kbc[(BitVec.setWidth
                                                          64 ((1888 : BitVec 32) + (cid_c -
                                                            (1 : BitVec 32)))).toNat]'hbd_1888_c0
                                                        + j_c)).toNat]'hidx_c0_lt) >>>
                                                        (1 : Nat)))).toNat]'h96_c0)).toNat <
                                                    kbj.length := by
                                                  rw [h2144_r_idx]
                                                  exact k6_2144_lt hr0_lt hnc_le hlen hkj_l
                                                c0_hsplit
                                                · clear hc; c0_hsteps!
                                                  have hm_eq := k6_set_congr (xs := kbj) h2144_r_idx
                                                    (congrArg (· ||| (536870912 : BitVec 32))
                                                      (k6_get_congr (xs := kbj) h2144_r_idx
                                                        h2144_r_c0
                                                        (k6_2144_lt hr0_lt hnc_le hlen hkj_l)))
                                                  rw [hm_eq] at hm; dsimp only [oldr] at hpr hm
                                                  rw [← k6_buf_get_eq (kbuf := kbj)
                                                    (i := 2144 + r0.toNat)
                                                    (k6_2144_lt hr0_lt hnc_le hlen hkj_l)] at hpr hm
                                                  exact hJr0 (_, true) m
                                                    ⟨invCore_set_meta hkj hr0_lt hpr.1 hpr.2, hm⟩
                                                · c0_hsteps!; exact hJr0 (kbj, ch_j) mj ⟨hkj, hmj⟩
                                              · c0_hsteps!; exact hJr0 (kbj, ch_j) mj ⟨hkj, hmj⟩
                                          · c0_hsteps!; exact hJlv (kbj, ch_j) mj ⟨hkj, hmj⟩
                                        · c0_hsteps!; exact hJlv (kbj, ch_j) mj ⟨hkj, hmj⟩
                                    · c0_hsteps!; exact hJelse (kbj, ch_j) mj ⟨hkj, hmj⟩
                                  · intro Lj hLj; c0_hsteps!
                                    exact hLj sz_c.toNat (ch_c, 0#32, ()) mc
                                      ⟨kbc, hkc, Nat.zero_le _, by simp, hmc⟩
                                · c0_hsteps!; exact hJelse (kbc, ch_c) mc ⟨hkc, hmc⟩
                        · c0_hsteps!; exact hJcid (kbc, ch_c) mc ⟨hkc, hmc⟩
                    · c0_hsteps!; exact hLp (nc.toNat - (pass + 1#32).toNat)
                        (pass + 1#32, ch_c, ()) mc (by omega) ⟨kbc, hkc, by omega, rfl, hmc⟩
                  · intro Lc hLc; c0_hsteps!
                    exact hLc nc.toNat (false, nc, ()) mp ⟨kbp, hkp, Nat.le_refl _, rfl, hmp⟩
                · c0_hsteps!; exact hRet kbp mp hkp hmp
              · c0_hsteps!; exact hRet kbp mp hkp hmp
            · intro Lp hLp; c0_hsteps!
              exact hLp nc.toNat (0#32, true, ()) mj ⟨kbj, hkj, Nat.zero_le _, by simp, hmj⟩
  }

/-- Certifies `fullK6CoreM7Spec` for `full_k6_core_m7`. -/
theorem full_k6_core_m7_wp (Γ : Env) :
    ∀ a m Q X, fullK6CoreM7Spec a m Q X → Func.wp Γ full_k6_core_m7_body a m Q X := by
  rintro ⟨pk, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨kbuf, R, hok0, hm0, hQ⟩ := fullK6CoreM7Spec_elim hSpec
  have hlen := hok0.base_ge
  let nc := kbuf[1]'(by omega); let nv := kbuf[0]'(by omega); let acap := kbuf[15]'(by omega)
  unfold Func.wp full_k6_core_m7_body; c0_hsplit
  · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ => rfl) (fun _ _ => ⟨rfl, rfl⟩) hm0
  · have hnc_raw_le :
        (kbuf[OfNat.ofNat 1 % 2 ^ 64]'(by change 1 % 2 ^ 64 < kbuf.length; omega)).toNat ≤
          256 := Nat.le_of_not_lt hc
    have hnc_le : nc.toNat ≤ 256 := hnc_raw_le; clear hc; c0_hsplit
    · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ => rfl) (fun _ _ => ⟨rfl, rfl⟩) hm0
    · have hnv_raw_le :
          (kbuf[OfNat.ofNat 0 % 2 ^ 64]'(by change 0 % 2 ^ 64 < kbuf.length; omega)).toNat ≤
            64 := Nat.le_of_not_lt hc
      have hnv_le : nv.toNat ≤ 64 := hnv_raw_le; clear hc
      let invCore := CoreInv kbuf nc
      have invCore_set_meta := @coreInv_set_meta kbuf nc hnc_le
      have invCore_set_flags := @coreInv_set_flags kbuf nc
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i32])
        (fun rem (i, ()) mi => ∃ kbi, invCore kbi ∧ i.toNat ≤ nc.toNat ∧
          rem = nc.toNat - i.toNat ∧ (array (t := i32) pk kbi ⋆ R) mi) ?_ ?_
      · rintro L1 rem1 ⟨i1, ⟨⟩⟩ m1 hL1 ⟨kb1, hk1, hi1_le, rfl, hm1⟩
        have hk1_l := hk1.2.1; c0_hsplit
        · have hi1_lt : i1.toNat < nc.toNat := hc; clear hc
          have hi1_succ : (i1 + 1#32).toNat = i1.toNat + 1 := by
            have := hnc_le; have := hi1_lt; c0_bound
          have hbd1 : 2144 + i1.toNat < kb1.length := by
            have := hk1_l; have := hlen; have := hnc_le; have := hi1_lt; omega
          let oldm := kb1[2144 + i1.toNat]'hbd1
          have hpres := k6_km_core_clear_pres oldm; c0_hsteps!
          have hidx1 : (BitVec.setWidth 64 (2144 + i1)).toNat = 2144 + i1.toNat := by
            have := hnc_le; have := hi1_lt; c0_bound
          have hkb1_eq : kb1.set (BitVec.setWidth 64 (2144 + i1)).toNat
                (kb1[(BitVec.setWidth 64 (2144 + i1)).toNat]'(by omega) &&& ~~~536870912) =
              kb1.set (2144 + i1.toNat) (oldm &&& ~~~536870912#32) :=
            k6_set_congr hidx1 (congrArg (· &&& ~~~536870912#32) (k6_get_congr hidx1 _ _))
          rw [hkb1_eq] at hm; dsimp only [oldm] at hpres hm
          rw [← k6_buf_get_eq hbd1] at hpres hm
          exact hL1 (nc.toNat - (i1 + 1#32).toNat) (i1 + 1#32, ()) _
            (by have := hnc_le; have := hi1_lt; have := hi1_succ; omega)
            ⟨_, invCore_set_meta hk1 hi1_lt hpres.1 hpres.2, by omega, rfl, hm⟩
        · have hi1_nc : i1 = nc := BitVec.eq_of_toNat_eq (by
            have : ¬i1.toNat < nc.toNat := hc; omega)
          clear hc; c0_hsteps_nogrp
          refine wp_join_state1 (t := i32) (α := List (BitVec 32) × BitVec 32)
            (fun x => x.2)
            (fun x mj => invCore x.1 ∧ (array (t := i32) pk x.1 ⋆ R) mj) ?_ ?_
          · rintro _ ⟨kbj, _⟩ mj ⟨hkj, hmj⟩
            exact k6_core_fixpoint_wp hlen rfl rfl hnc_le hnv_le
              (fun kbp mp hkp hmp => hQ kbp mp hkp.2.1 hkp.2.2.1
                (fun cid hcid => hkp.2.2.2 cid
                  (by rw [k6_buf_get_eq (by omega)] at hcid; exact hcid))
                hmp)
              hkj hmj
          · intro Jinc hJinc
            let inc := kb1[7]'(by omega)
            c0_hsplit
            · have hinc_raw_lt := hc
              have hinc : inc.toNat < nc.toNat :=
                Nat.lt_of_not_le (by simpa [k6_c1, k6_c7] using hc)
              clear hc
              -- Clear flags loop 1 (`i < nv`)
              refine wp_loop_group (ts := [i32])
                (fun rem (i, ()) mf => ∃ kbf, invCore kbf ∧ i.toNat ≤ nv.toNat ∧
                  rem = nv.toNat - i.toNat ∧ (array (t := i32) pk kbf ⋆ R) mf)
                ?_ ?_
              · rintro Lf remf ⟨if1, ⟨⟩⟩ mf1 hLf ⟨kbf1, hkf1, hif1, rfl, hmf1⟩
                have hkf1_l := hkf1.2.1
                c0_hsplit
                · have hi_lt : if1.toNat < nv.toNat := by
                    simpa [nv, k6_c0] using hc
                  clear hc
                  have hif1_s : (if1 + 1#32).toNat = if1.toNat + 1 := by
                    have := hnv_le; have := hi_lt; c0_bound
                  have h416_i : (BitVec.setWidth 64 ((416 : BitVec 32) + if1)).toNat =
                      416 + if1.toNat := by
                    have := hnv_le; have := hi_lt; c0_bound
                  c0_hsteps!
                  rw [k6_set_congr h416_i rfl] at hm
                  exact hLf (nv.toNat - (if1 + 1#32).toNat) (if1 + 1#32, ()) _
                    (by omega)
                    ⟨_, invCore_set_flags hkf1 (by have := hnv_le; have := hi_lt; omega) _,
                      by omega, rfl, hm⟩
                · have hkb_inc := hkf1.1.clause_ok (by
                    have h1eq := hkf1.2.2.1 1 (by have := hkf1.1.base_ge; omega) (Or.inl (by omega))
                    rw [List.getElem?_eq_getElem (by have := hkf1.1.base_ge; omega),
                      List.getElem?_eq_getElem (by omega)] at h1eq
                    have hnc_e : kbf1[1]'(by have := hkf1.1.base_ge; omega) = nc :=
                      Option.some.inj h1eq
                    rw [k6_buf_get_eq (by have := hkf1.1.base_ge; omega), hnc_e]; exact hinc)
                  clear hc
                  let oldmi := kbf1[2144 + inc.toNat]'(
                    k6_2144_len_lt hinc hnc_le hkf1.1.base_ge)
                  have hpmi := k6_km_core_or_pres oldmi
                  have hlt28 := hkf1.1.length_lt; have hlen_ge := hkf1.1.length_ge
                  have h15 : (kbf1[15]?.getD 0#32).toNat = acap.toNat := by
                    have := hkf1.2.2.1 15 (by omega) (Or.inl (by omega))
                    rw [this, k6_buf_get_eq (by omega)]
                  have hinc_sz_nw : (kbf1[1888 + inc.toNat]'(
                        k6_1888_len_lt hinc hnc_le hkf1.1.base_ge)).toNat +
                      ((oldmi ||| 0x20000000#32) &&& 0xFFFF#32).toNat < 2 ^ 32 := by
                    rw [k6_buf_get_eq (k6_1888_len_lt hinc hnc_le hkf1.1.base_ge),
                      k6_buf_get_eq (k6_2144_len_lt hinc hnc_le hkf1.1.base_ge), h15] at hkb_inc
                    dsimp only [oldmi] at hpmi ⊢; rw [hpmi.1]; have := hkf1.1.base_ge; omega
                  have hk7_bd :
                      (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 7)).toNat < kb1.length := by
                    change 7 % 2 ^ 64 < kb1.length; have := hk1_l; have := hlen; omega
                  have hk7_f_bd :
                      (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 7)).toNat < kbf1.length := by
                    rw [hkf1_l, ← hk1_l]; exact hk7_bd
                  have hinc_c0_lt : (kb1[(BitVec.ofNat (OfNat.ofNat 64)
                      (OfNat.ofNat 7)).toNat]'hk7_bd).toNat < nc.toNat := hinc
                  have h1888_inc_c0 : (BitVec.setWidth 64 ((1888 : BitVec 32) +
                      kb1[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat <
                      kbf1.length := by
                    have := hkf1.1.base_ge; have := hnc_le; have := hinc_c0_lt; c0_bound
                  have h2144_inc_c0 : (BitVec.setWidth 64 ((2144 : BitVec 32) +
                      kb1[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat <
                      kbf1.length := by
                    have := hkf1.1.base_ge; have := hnc_le; have := hinc_c0_lt; c0_bound
                  c0_hsteps_nogrp
                  -- `if (off + sz <= acap)` join before `ti` loop
                  refine wp_join0
                    (fun mj => ∃ kbj, invCore kbj ∧ (array (t := i32) pk kbj ⋆ R) mj) ?_ ?_
                  · intro _ mj ⟨kbj, hkj, hmj⟩
                    try clear h1888_inc_c0 h2144_inc_c0 hinc_c0_lt hkf1_l hkb_inc hinc_sz_nw
                    try clear hpmi h15 hlt28 hlen_ge hkf1 oldmi hk7_f_bd hk7_bd hm hmf1 hm1 hif1
                    have hkj_l := hkj.2.1
                    c0_hsteps_nogrp
                    -- Clamp `ti` (`if (ti > 64) ti = 64`)
                    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
                      (fun ti => (ti, ())) (fun ti => ti.toNat ≤ 64) ?_ ?_
                    · intro _ ti hti
                      c0_hsteps_nogrp
                      -- Loop `ti` down to `0`
                      refine wp_loop_group (ts := [i32])
                        (fun rem (tic, ()) mt => ∃ kbt, invCore kbt ∧ tic.toNat ≤ 64 ∧
                          rem = tic.toNat ∧ (array (t := i32) pk kbt ⋆ R) mt)
                        ?_ ?_
                      · rintro Lt remt ⟨tic, ⟨⟩⟩ mt hLt ⟨kbt, hkt, htic, rfl, hmt⟩
                        try clear hmj hkj hkj_l hti
                        have hkt_l := hkt.2.1
                        c0_hsplit
                        · have ht_pos : 0 < tic.toNat := hc
                          clear hc
                          let t1 := tic - 1#32
                          have ht1_lt : t1.toNat < 64 := by
                            dsimp only [t1]; rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
                            have := ht_pos; have := htic; omega
                          have ht1_dec : t1.toNat < tic.toNat := by
                            dsimp only [t1]; rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
                            have := ht_pos; have := htic; omega
                          c0_hsplit
                          · c0_hsteps!; exact hLt t1.toNat (t1, ()) mt ht1_dec
                              ⟨kbt, hkt, by omega, rfl, hmt⟩
                          · have ht_352_mod : (BitVec.toNat (352 : BitVec 32) +
                                (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + tic.toNat)) %
                                2 ^ 32 = 352 + t1.toNat := by
                              change (352 + (2 ^ 32 - 1 + tic.toNat)) % 2 ^ 32 = 352 + t1.toNat
                              have ht1_sub : t1.toNat = tic.toNat - 1 := by
                                dsimp only [t1]; rw [BitVec.toNat_sub]
                                simp only [BitVec.toNat_ofNat, Nat.reducePow]
                                have := ht_pos; have := htic; omega
                              rw [ht1_sub]; have := ht_pos; have := htic; omega
                            have ht_352_c0 : (BitVec.setWidth 64
                                ((352 : BitVec 32) + (tic - (1 : BitVec 32)))).toNat =
                                352 + t1.toNat := by
                              change (BitVec.setWidth 64 (352#32 + t1)).toNat = 352 + t1.toNat
                              have := ht1_lt; c0_bound
                            have ht_352_bd_mod : (BitVec.toNat (352 : BitVec 32) +
                                (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + tic.toNat)) %
                                2 ^ 32 < kbt.length := by
                              rw [ht_352_mod]; have := hkt_l; have := hlen; omega
                            have ht_352_bd_c0 : (BitVec.setWidth 64
                                ((352 : BitVec 32) + (tic - (1 : BitVec 32)))).toNat <
                                kbt.length := by
                              rw [ht_352_c0]; have := hkt_l; have := hlen; omega
                            let v_t := (kbt[352 + t1.toNat]'(by
                              have := hkt_l; have := hlen; omega)) >>> (1 : Nat)
                            have hvt_lt : v_t.toNat < nv.toNat := by
                              refine Nat.lt_of_not_le (show ¬nv.toNat ≤ v_t.toNat from ?_)
                              dsimp only [v_t]
                              rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                ← k6_get_congr ht_352_mod ht_352_bd_mod (by omega)]
                              simpa [nv, Nat.reducePow, k6_c0] using hc
                            clear hc
                            have hget_352_c0 : kbt[(BitVec.setWidth 64
                                ((352 : BitVec 32) + (tic - (1 : BitVec 32)))).toNat]'ht_352_bd_c0 =
                                kbt[352 + t1.toNat]'(by have := hkt_l; have := hlen; omega) :=
                              k6_get_congr ht_352_c0 ht_352_bd_c0 (by omega)
                            have h416_t_eq : (BitVec.setWidth 64 ((416 : BitVec 32) +
                                (kbt[(BitVec.setWidth 64 ((352 : BitVec 32) +
                                  (tic - (1 : BitVec 32)))).toNat]'ht_352_bd_c0 >>>
                                (1 : Nat)))).toNat = 416 + v_t.toNat := by
                              rw [hget_352_c0]
                              change (BitVec.setWidth 64 (416#32 + v_t)).toNat = 416 + v_t.toNat
                              have := hvt_lt; have := hnv_le; c0_bound
                            have h416_t_c0 : (BitVec.setWidth 64 ((416 : BitVec 32) +
                                (kbt[(BitVec.setWidth 64 ((352 : BitVec 32) +
                                  (tic - (1 : BitVec 32)))).toNat]'ht_352_bd_c0 >>>
                                (1 : Nat)))).toNat < kbt.length := by
                              rw [h416_t_eq]; have := hkt_l; have := hlen; omega
                            have h96_t_eq : (BitVec.setWidth 64 ((96 : BitVec 32) +
                                (kbt[(BitVec.setWidth 64 ((352 : BitVec 32) +
                                  (tic - (1 : BitVec 32)))).toNat]'ht_352_bd_c0 >>>
                                (1 : Nat)))).toNat = 96 + v_t.toNat := by
                              rw [hget_352_c0]
                              change (BitVec.setWidth 64 (96#32 + v_t)).toNat = 96 + v_t.toNat
                              have := hvt_lt; have := hnv_le; c0_bound
                            have h96_t_c0 : (BitVec.setWidth 64 ((96 : BitVec 32) +
                                (kbt[(BitVec.setWidth 64 ((352 : BitVec 32) +
                                  (tic - (1 : BitVec 32)))).toNat]'ht_352_bd_c0 >>>
                                (1 : Nat)))).toNat < kbt.length := by
                              rw [h96_t_eq]; have := hkt_l; have := hlen; omega
                            c0_hsplit
                            · c0_hsteps!; exact hLt t1.toNat (t1, ()) mt ht1_dec
                                ⟨kbt, hkt, by omega, rfl, hmt⟩
                            · clear hc
                              have hm1_eq := k6_set_congr (xs := kbt) h416_t_eq
                                (congrArg (· &&& ~~~(2 : BitVec 32))
                                  (k6_get_congr (xs := kbt) h416_t_eq h416_t_c0
                                    (by have := hkt_l; have := hlen; have := hnv_le; omega)))
                              c0_hsplit
                              · c0_hsteps!
                                rw [hm1_eq] at hm
                                exact hLt t1.toNat (t1, ()) _ ht1_dec
                                  ⟨_, invCore_set_flags hkt (v := v_t.toNat)
                                    (by have := hvt_lt; have := hnv_le; omega) _,
                                    by omega, rfl, hm⟩
                              · rw [hm1_eq] at hm
                                have hkbt1_ex : ∃ kbt1 : List (BitVec 32), invCore kbt1 ∧
                                    kbt1.length = kbuf.length ∧
                                    kbt1[96 + v_t.toNat]? = some (kbt[96 + v_t.toNat]'(by
                                      have := hkt_l; have := hlen; have := hnv_le; omega)) ∧
                                    (array (t := i32) pk kbt1 ⋆ R) m := by
                                  refine ⟨kbt.set (416 + v_t.toNat)
                                      ((kbt[416 + v_t.toNat]'(by
                                        have := hkt_l; have := hlen; have := hnv_le; omega)) &&&
                                        ~~~2#32),
                                    invCore_set_flags hkt (v := v_t.toNat)
                                      (by have := hvt_lt; have := hnv_le; omega) _,
                                    by rw [List.length_set, hkt_l], ?_, hm⟩
                                  rw [List.getElem?_set_ne (by omega),
                                    List.getElem?_eq_getElem (by
                                      have := hkt_l; have := hlen; have := hnv_le; omega)]
                                obtain ⟨kbt1, hkt1, hkt1_l, hkbt1_96q, hm_n1⟩ := hkbt1_ex
                                clear hm
                                have hm := hm_n1; clear hm_n1
                                have hkbt1_96 : kbt1[96 + v_t.toNat]'(by
                                    have := hkt1_l; have := hlen; have := hnv_le; omega) =
                                    kbt[96 + v_t.toNat]'(by
                                      have := hkt_l; have := hlen; have := hnv_le; omega) := by
                                  have hbd : 96 + v_t.toNat < kbt1.length := by
                                    have := hkt1_l; have := hlen; have := hnv_le; omega
                                  rw [List.getElem?_eq_getElem hbd] at hkbt1_96q
                                  exact Option.some.inj hkbt1_96q
                                have h96_ne : 96 + v_t.toNat ≠ 416 + v_t.toNat := by omega
                                have hget_rsn_c0 : kbt1[(BitVec.setWidth 64 ((96 : BitVec 32) +
                                    (kbt[(BitVec.setWidth 64 ((352 : BitVec 32) +
                                      (tic - (1 : BitVec 32)))).toNat]'ht_352_bd_c0 >>>
                                    (1 : Nat)))).toNat]'(by
                                      rw [h96_t_eq]; have := hkt1_l; have := hlen; omega) =
                                    kbt[96 + v_t.toNat]'(by
                                      have := hkt_l; have := hlen; omega) := by
                                  rw [k6_get_congr (xs := kbt1) h96_t_eq _
                                    (by have := hkt1_l; have := hlen; have := hnv_le; omega),
                                    hkbt1_96]
                                have ht_352_raw : (352 + (4294967295 + tic.toNat)) %
                                    4294967296 = 352 + t1.toNat := by
                                  have h352n : BitVec.toNat (352 : BitVec 32) = 352 := rfl
                                  have h1n : BitVec.toNat (1 : BitVec 32) = 1 := rfl
                                  have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
                                  simpa [h352n, h1n, h232] using ht_352_mod
                                have hget_352_raw : kbt[(352 +
                                    (4294967295 + tic.toNat)) % 4294967296]'(by
                                      rw [ht_352_raw]; have := hkt_l; have := hlen; omega) =
                                    kbt[352 + t1.toNat]'(by
                                      have := hkt_l; have := hlen; omega) :=
                                  k6_get_congr ht_352_raw _ _
                                have hrsn : (kbt1[96 + v_t.toNat]'(by
                                    have := hkt1_l; have := hlen; have := hnv_le; omega)).toNat <
                                    nc.toNat := by
                                  have h416n : BitVec.toNat (416 : BitVec 32) = 416 := rfl
                                  have h96n : BitVec.toNat (96 : BitVec 32) = 96 := rfl
                                  have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
                                  have hvt_div : v_t.toNat = (kbt[352 + t1.toNat]'(by
                                      have := hkt_l; have := hlen; omega)).toNat / 2 := by
                                    dsimp only [v_t]
                                    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                                  have hk_raw : (kbt[(BitVec.toNat (352 : BitVec 32) +
                                      (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + tic.toNat)) %
                                      2 ^ 32]'(ht_352_bd_mod)).toNat / 2 = v_t.toNat := by
                                    rw [k6_get_congr ht_352_mod ht_352_bd_mod
                                      (by have := hkt_l; have := hlen; omega)]
                                    exact hvt_div.symm
                                  have h416_ne : (BitVec.toNat (416 : BitVec 32) +
                                      (kbt[(BitVec.toNat (352 : BitVec 32) +
                                        (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + tic.toNat)) %
                                        2 ^ 32]'(ht_352_bd_mod)).toNat / 2) % 2 ^ 32 ≠
                                      (BitVec.toNat (96 : BitVec 32) +
                                        (kbt[(BitVec.toNat (352 : BitVec 32) +
                                          (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + tic.toNat)) %
                                          2 ^ 32]'(ht_352_bd_mod)).toNat / 2) % 2 ^ 32 := by
                                    rw [hk_raw, h416n, h96n, h232]
                                    have := hvt_lt; have := hnv_le; omega
                                  have h96_idx_eq : (BitVec.toNat (96 : BitVec 32) +
                                      (kbt[(BitVec.toNat (352 : BitVec 32) +
                                        (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + tic.toNat)) %
                                        2 ^ 32]'(ht_352_bd_mod)).toNat / 2) % 2 ^ 32 =
                                      96 + v_t.toNat := by
                                    rw [hk_raw, h96n, h232]
                                    have := hvt_lt; have := hnv_le; omega
                                  have hc' := hc
                                  rw [List.getElem_set_ne h416_ne] at hc'
                                  have hget_kbt : kbt[(BitVec.toNat (96 : BitVec 32) +
                                      (kbt[(BitVec.toNat (352 : BitVec 32) +
                                        (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + tic.toNat)) %
                                        2 ^ 32]'(ht_352_bd_mod)).toNat / 2) % 2 ^ 32]'(by
                                        rw [h96_idx_eq]; have := hkt_l; have := hlen; omega) =
                                      kbt[96 + v_t.toNat]'(by
                                        have := hkt_l; have := hlen; omega) :=
                                    k6_get_congr h96_idx_eq _ _
                                  rw [hget_kbt] at hc'
                                  change ¬nc.toNat ≤ (kbt[96 + v_t.toNat]'(by
                                    have := hkt_l; have := hlen; omega)).toNat at hc'
                                  rw [hkbt1_96]
                                  exact Nat.lt_of_not_le hc'
                                try clear hc
                                let rsn := kbt1[96 + v_t.toNat]'(by
                                  have := hkt1_l; have := hlen; have := hnv_le; omega)
                                change rsn.toNat < nc.toNat at hrsn
                                have hkbt_rsn : kbt[96 + v_t.toNat]'(by
                                    have := hkt_l; have := hlen; omega) = rsn :=
                                  hkbt1_96.symm
                                have hget_raw_rsn : ∀ hbd,
                                    (kbt.set (BitVec.setWidth 64 ((416 : BitVec 32) +
                                      (kbt[(BitVec.setWidth 64 ((352 : BitVec 32) +
                                        (tic - (1 : BitVec 32)))).toNat]'ht_352_bd_c0 >>>
                                      (1 : Nat)))).toNat
                                      (kbt[(BitVec.setWidth 64 ((416 : BitVec 32) +
                                        (kbt[(BitVec.setWidth 64 ((352 : BitVec 32) +
                                          (tic - (1 : BitVec 32)))).toNat]'ht_352_bd_c0 >>>
                                        (1 : Nat)))).toNat]'h416_t_c0 &&&
                                        ~~~(2 : BitVec 32)))[(BitVec.setWidth 64
                                      ((96 : BitVec 32) +
                                      (kbt[(BitVec.setWidth 64 ((352 : BitVec 32) +
                                        (tic - (1 : BitVec 32)))).toNat]'ht_352_bd_c0 >>>
                                      (1 : Nat)))).toNat]'hbd = rsn := by
                                  intro hbd
                                  rw [List.getElem_set_ne (by
                                    rw [h416_t_eq, h96_t_eq]; omega)]
                                  exact (k6_get_congr h96_t_eq _ _).trans hkbt_rsn
                                simp only [hget_raw_rsn]
                                clear hm1_eq hget_raw_rsn
                                have hk_rsn := hkt1.1.clause_ok (by
                                  have h1eq := hkt1.2.2.1 1 (by have := hkt1.1.base_ge; omega)
                                    (Or.inl (by omega))
                                  rw [List.getElem?_eq_getElem (by have := hkt1.1.base_ge; omega),
                                    List.getElem?_eq_getElem (by omega)] at h1eq
                                  have hnc_e : kbt1[1]'(by have := hkt1.1.base_ge; omega) = nc :=
                                    Option.some.inj h1eq
                                  rw [k6_buf_get_eq (by have := hkt1.1.base_ge; omega), hnc_e]
                                  exact hrsn)
                                let oldmr := kbt1[2144 + rsn.toNat]'(by
                                  have := hkt1.1.base_ge; have := hnc_le; have := hrsn; omega)
                                have hpr := k6_km_core_or_pres oldmr
                                have h2144_r_eq : (BitVec.setWidth 64
                                    ((2144 : BitVec 32) + rsn)).toNat = 2144 + rsn.toNat := by
                                  have := hrsn; have := hnc_le; c0_bound
                                have h1888_r_eq : (BitVec.setWidth 64
                                    ((1888 : BitVec 32) + rsn)).toNat = 1888 + rsn.toNat := by
                                  have := hrsn; have := hnc_le; c0_bound
                                have h2144_r_c0 : (BitVec.setWidth 64
                                    ((2144 : BitVec 32) + rsn)).toNat < kbt1.length := by
                                  rw [h2144_r_eq]; exact k6_2144_len_lt hrsn hnc_le hkt1.1.base_ge
                                have h1888_r_c0 : (BitVec.setWidth 64
                                    ((1888 : BitVec 32) + rsn)).toNat < kbt1.length := by
                                  rw [h1888_r_eq]; exact k6_1888_len_lt hrsn hnc_le hkt1.1.base_ge
                                have hrsn_nw : (kbt1[1888 + rsn.toNat]'(
                                      k6_1888_len_lt hrsn hnc_le hkt1.1.base_ge)).toNat +
                                    ((oldmr ||| 0x20000000#32) &&& 0xFFFF#32).toNat < 2 ^ 32 := by
                                  have h15 : (kbt1[15]?.getD 0#32).toNat = acap.toNat := by
                                    have := hkt1.2.2.1 15 (by omega) (Or.inl (by omega))
                                    rw [this, k6_buf_get_eq (by omega)]
                                  rw [k6_buf_get_eq (k6_1888_len_lt hrsn hnc_le hkt1.1.base_ge),
                                    k6_buf_get_eq (k6_2144_len_lt hrsn hnc_le hkt1.1.base_ge),
                                    h15] at hk_rsn
                                  rw [hpr.1]; dsimp only [oldmr] at hk_rsn ⊢
                                  have := hkt1.1.length_lt; have := hkt1.1.length_ge; omega
                                have hpr' : ((oldmr ||| 0x20000000#32) &&& 0xFFFF#32 =
                                      (kbt1[2144 + rsn.toNat]?.getD 0#32) &&& 0xFFFF#32) ∧
                                    ((oldmr ||| 0x20000000#32) &&& 0x40000000#32 =
                                      (kbt1[2144 + rsn.toNat]?.getD 0#32) &&& 0x40000000#32) := by
                                  rw [k6_buf_get_eq (k6_2144_len_lt hrsn hnc_le hkt1.1.base_ge)]
                                  exact hpr
                                have hm2_eq := k6_set_congr (xs := kbt1) h2144_r_eq
                                  (congrArg (· ||| (536870912 : BitVec 32))
                                    (k6_get_congr (xs := kbt1) h2144_r_eq h2144_r_c0
                                      (k6_2144_len_lt hrsn hnc_le hkt1.1.base_ge)))
                                let roff := kbt1[1888 + rsn.toNat]'(
                                  k6_1888_len_lt hrsn hnc_le hkt1.1.base_ge)
                                let rsz := (oldmr ||| 0x20000000#32) &&& 0xFFFF#32
                                c0_hsteps_nogrp; rw [hm2_eq] at hm
                                have hkbt2_ex : ∃ kbt2 : List (BitVec 32), invCore kbt2 ∧
                                    kbt2.length = kbuf.length ∧
                                    kbt2[1888 + rsn.toNat]? = some roff ∧
                                    kbt2[2144 + rsn.toNat]? = some (oldmr ||| 0x20000000#32) ∧
                                    (array (t := i32) pk kbt2 ⋆ R) m := by
                                  refine ⟨kbt1.set (2144 + rsn.toNat) (oldmr ||| 0x20000000#32),
                                    invCore_set_meta hkt1 hrsn hpr'.1 hpr'.2,
                                    by rw [List.length_set, hkt1_l], ?_, ?_, hm⟩
                                  · rw [List.getElem?_set_ne (by omega), List.getElem?_eq_getElem
                                      (k6_1888_len_lt hrsn hnc_le hkt1.1.base_ge)]
                                  · rw [List.getElem?_set_self
                                      (k6_2144_len_lt hrsn hnc_le hkt1.1.base_ge)]
                                obtain ⟨kbt2, hkt2, hkbt2_l, h1888_k2q, h2144_k2q, hm_n2⟩ :=
                                  hkbt2_ex
                                clear hm hpr' hkbt1_96q h1888_k2q h2144_k2q
                                have hm := hm_n2; clear hm_n2
                                have hget_raw_roff : ∀ hbd,
                                    (kbt1.set (BitVec.setWidth 64 ((2144 : BitVec 32) +
                                      rsn)).toNat
                                      (kbt1[(BitVec.setWidth 64 ((2144 : BitVec 32) +
                                        rsn)).toNat]'h2144_r_c0 |||
                                        (536870912 : BitVec 32)))[(BitVec.setWidth 64
                                      ((1888 : BitVec 32) + rsn)).toNat]'hbd = roff := by
                                  intro hbd
                                  rw [List.getElem_set_ne (by
                                    rw [h2144_r_eq, h1888_r_eq]; omega)]
                                  exact k6_get_congr h1888_r_eq _ _
                                have hget_raw_newmr : ∀ hbd,
                                    (kbt1.set (BitVec.setWidth 64 ((2144 : BitVec 32) +
                                      rsn)).toNat
                                      (kbt1[(BitVec.setWidth 64 ((2144 : BitVec 32) +
                                        rsn)).toNat]'h2144_r_c0 |||
                                        (536870912 : BitVec 32)))[(BitVec.setWidth 64
                                      ((2144 : BitVec 32) + rsn)).toNat]'hbd =
                                      oldmr ||| (536870912 : BitVec 32) := by
                                  intro hbd
                                  rw [List.getElem_set_self (by
                                    rw [List.length_set]; exact h2144_r_c0)]
                                  exact congrArg (· ||| (536870912 : BitVec 32))
                                    (k6_get_congr h2144_r_eq h2144_r_c0 _)
                                simp only [hget_raw_roff, hget_raw_newmr]
                                clear hm2_eq hget_raw_roff hget_raw_newmr
                                refine wp_join0
                                  (fun mr => ∃ kbr, invCore kbr ∧
                                    (array (t := i32) pk kbr ⋆ R) mr)
                                  ?_ ?_
                                · intro _ mr ⟨kbr, hkr, hmr⟩
                                  c0_hsteps!
                                  exact hLt t1.toNat (t1, ()) mr ht1_dec
                                    ⟨kbr, hkr, by omega, rfl, hmr⟩
                                · intro Jg hJg
                                  c0_hsplit
                                  · have hrsz_bd : roff.toNat + rsz.toNat ≤ acap.toNat := by
                                      have hmod : (roff.toNat + rsz.toNat) % 4294967296 =
                                          roff.toNat + rsz.toNat :=
                                        Nat.mod_eq_of_lt hrsn_nw
                                      have hnw : (oldmr.toNat ||| 536870912) &&& 65535 =
                                          rsz.toNat := by
                                        dsimp only [rsz]
                                        rw [BitVec.toNat_and, BitVec.toNat_or]; rfl
                                      simpa [hmod, hnw, k6_c15, Nat.reducePow] using hc
                                    clear hc
                                    c0_hsteps_nogrp
                                    refine wp_loop_group (ts := [i32])
                                      (fun remj (jr, ()) mr => ∃ kbr, invCore kbr ∧
                                        jr.toNat ≤ rsz.toNat ∧ remj = rsz.toNat - jr.toNat ∧
                                        (array (t := i32) pk kbr ⋆ R) mr)
                                      ?_ ?_
                                    · rintro Lr remr ⟨jr, ⟨⟩⟩ mr hLr ⟨kbr, hkr, hjr_le, rfl, hmr⟩
                                      have hkr_l := hkr.2.1
                                      c0_hsplit
                                      · have hjr_lt : jr.toNat < rsz.toNat := hc
                                        clear hc
                                        have hrsz_lt : rsz.toNat < 65536 := by
                                          dsimp only [rsz]; rw [BitVec.toNat_and]
                                          exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                                        have hj1 : (jr + 1#32).toNat = jr.toNat + 1 := by
                                          have := hrsz_lt; have := hjr_lt; c0_bound
                                        have har_r : 2912 + roff.toNat + jr.toNat < kbr.length := by
                                          have := hkr.1.length_ge
                                          have h15 : (kbr[15]?.getD 0#32).toNat = acap.toNat := by
                                            have := hkr.2.2.1 15 (by omega) (Or.inl (by omega))
                                            rw [this, k6_buf_get_eq (by omega)]
                                          omega
                                        have h2912_r_c0 : (BitVec.setWidth 64
                                            ((2912 : BitVec 32) + roff + jr)).toNat <
                                            kbr.length := by
                                          have := har_r; have := hkr.1.length_lt; c0_bound
                                        c0_hsteps_nogrp
                                        refine wp_join0
                                          (fun mr1 => ∃ kbr1, invCore kbr1 ∧
                                            (array (t := i32) pk kbr1 ⋆ R) mr1)
                                          ?_ ?_
                                        · intro _ mr1 ⟨kbr1, hkr1, hmr1⟩
                                          c0_hsteps!
                                          exact hLr (rsz.toNat - (jr + 1#32).toNat)
                                            (jr + 1#32, ()) mr1 (by have := hj1; omega)
                                            ⟨kbr1, hkr1, by have := hj1; omega, rfl, hmr1⟩
                                        · intro Jlv hJlv
                                          c0_hsplit
                                          · have hlv_lt : ((kbr[2912 + roff.toNat +
                                                  jr.toNat]'(har_r)) >>>
                                                (1 : Nat)).toNat < nv.toNat := by
                                              have har_mod : (BitVec.toNat (2912 : BitVec 32) +
                                                  roff.toNat + jr.toNat) % 2 ^ 32 =
                                                  2912 + roff.toNat + jr.toNat := by
                                                have := har_r; have := hkr.1.length_lt
                                                rw [show BitVec.toNat (2912 : BitVec 32) = 2912
                                                  from rfl, Nat.mod_eq_of_lt (by omega)]
                                              rw [BitVec.toNat_ushiftRight,
                                                Nat.shiftRight_eq_div_pow]
                                              rw [← k6_get_congr har_mod
                                                (by rw [har_mod]; exact har_r) har_r]
                                              simpa [nv, k6_c0, Nat.reducePow] using hc
                                            clear hc
                                            have hget_lr : kbr[(BitVec.setWidth 64
                                                ((2912 : BitVec 32) + roff +
                                                  jr)).toNat]'h2912_r_c0 =
                                                kbr[2912 + roff.toNat + jr.toNat]'har_r :=
                                              k6_get_congr
                                                (by have := har_r; have := hkr.1.length_lt
                                                    c0_bound)
                                                _ _
                                            have h416_r_eq : (BitVec.setWidth 64
                                                ((416 : BitVec 32) +
                                                (kbr[(BitVec.setWidth 64 ((2912 : BitVec 32) +
                                                  roff + jr)).toNat]'h2912_r_c0 >>>
                                                  (1 : Nat)))).toNat =
                                                416 + ((kbr[2912 + roff.toNat + jr.toNat]'har_r) >>>
                                                  (1 : Nat)).toNat := by
                                              rw [hget_lr]; have := hlv_lt; have := hnv_le
                                              c0_bound
                                            have h416_r_c0 : (BitVec.setWidth 64
                                                ((416 : BitVec 32) +
                                                (kbr[(BitVec.setWidth 64 ((2912 : BitVec 32) +
                                                  roff + jr)).toNat]'h2912_r_c0 >>>
                                                  (1 : Nat)))).toNat < kbr.length := by
                                              rw [h416_r_eq]; have := hlv_lt; have := hnv_le
                                              have := hkr_l; have := hlen; omega
                                            c0_hsplit
                                            · c0_hsteps!
                                              have hmr_eq := k6_set_congr (xs := kbr) h416_r_eq
                                                (congrArg (· ||| (2 : BitVec 32))
                                                  (k6_get_congr (xs := kbr) h416_r_eq h416_r_c0
                                                    (by have := hkr_l; have := hlen; omega)))
                                              rw [hmr_eq] at hm
                                              exact hJlv _
                                                ⟨_, invCore_set_flags hkr
                                                  (v := ((kbr[2912 + roff.toNat +
                                                      jr.toNat]'har_r) >>> (1 : Nat)).toNat)
                                                  (by have := hlv_lt; have := hnv_le; omega) _,
                                                  hm⟩
                                            · c0_hsteps!
                                              exact hJlv mr ⟨kbr, hkr, hmr⟩
                                          · c0_hsteps!
                                            exact hJlv mr ⟨kbr, hkr, hmr⟩
                                      · c0_hsteps!; exact hJg mr ⟨kbr, hkr, hmr⟩
                                    · intro Lr hLr; c0_hsteps!
                                      exact hLr rsz.toNat (0#32, ()) _
                                        ⟨kbt2, hkt2, Nat.zero_le _, by simp, hm⟩
                                  · c0_hsteps!; exact hJg m ⟨kbt2, hkt2, hm⟩
                        · -- After `ti` loop: clear flags loop 2 (`i < nv`)
                          c0_hsteps_nogrp
                          refine wp_loop_group (ts := [i32])
                            (fun rem (i2, ()) mf2 => ∃ kbf2, invCore kbf2 ∧ i2.toNat ≤ nv.toNat ∧
                              rem = nv.toNat - i2.toNat ∧ (array (t := i32) pk kbf2 ⋆ R) mf2)
                            ?_ ?_
                          · rintro Lf2 remf2 ⟨if2, ⟨⟩⟩ mf2 hLf2 ⟨kbf2, hkf2, hif2, rfl, hmf2⟩
                            have hkf2_l := hkf2.2.1
                            c0_hsplit
                            · have hi_lt : if2.toNat < nv.toNat := by
                                simpa [nv, k6_c0] using hc
                              clear hc
                              have hif2_s : (if2 + 1#32).toNat = if2.toNat + 1 := by
                                have := hnv_le; have := hi_lt; c0_bound
                              have h416_i2 : (BitVec.setWidth 64 ((416 : BitVec 32) + if2)).toNat =
                                  416 + if2.toNat := by
                                have := hnv_le; have := hi_lt; c0_bound
                              c0_hsteps!
                              rw [k6_set_congr h416_i2 rfl] at hm
                              exact hLf2 (nv.toNat - (if2 + 1#32).toNat) (if2 + 1#32, ()) _
                                (by omega)
                                ⟨_, invCore_set_flags hkf2
                                  (by have := hnv_le; have := hi_lt; omega) _,
                                  by omega, rfl, hm⟩
                            · c0_hsteps!; exact hJinc (kbf2, if2) mf2 ⟨hkf2, hmf2⟩
                          · intro Lf2 hLf2; c0_hsteps!
                            exact hLf2 nv.toNat (0#32, ()) mt
                              ⟨kbt, hkt, Nat.zero_le _, by simp, hmt⟩
                      · intro Lt hLt; c0_hsteps!
                        exact hLt ti.toNat (ti, ()) mj ⟨kbj, hkj, hti, rfl, hmj⟩
                    · intro Jti hJti
                      c0_hsplit
                      · c0_hsteps!; exact hJti 64#32 (by decide)
                      · c0_hsteps!; exact hJti _ (by c0_bound)
                  · intro JincCl hJincCl
                    try clear hL1 hi1_le hm1 hk1_l hk1 hinc_raw_lt hnc_raw_le hnv_raw_le
                    try clear L1 hi1_nc Jinc hJinc hLf hif1 hmf1 Lf
                    let off_i := kbf1[1888 + inc.toNat]'(
                      k6_1888_len_lt hinc hnc_le hkf1.1.base_ge)
                    let sz_i := (oldmi ||| 0x20000000#32) &&& 0xFFFF#32
                    have h2144_idx :
                        (BitVec.setWidth 64 (2144#32 + inc)).toNat = 2144 + inc.toNat :=
                      k6_sw64_add_2144 (Nat.lt_of_lt_of_le hinc hnc_le)
                    have h1888_idx :
                        (BitVec.setWidth 64 (1888#32 + inc)).toNat = 1888 + inc.toNat :=
                      k6_sw64_add_1888 (Nat.lt_of_lt_of_le hinc hnc_le)
                    have hpmi' : ((oldmi ||| 0x20000000#32) &&& 0xFFFF#32 =
                          (kbf1[2144 + inc.toNat]?.getD 0#32) &&& 0xFFFF#32) ∧
                        ((oldmi ||| 0x20000000#32) &&& 0x40000000#32 =
                          (kbf1[2144 + inc.toNat]?.getD 0#32) &&& 0x40000000#32) := by
                      rw [k6_buf_get_eq (k6_2144_len_lt hinc hnc_le hkf1.1.base_ge)]
                      exact hpmi
                    have h2144_inc_eq : (BitVec.setWidth 64 ((2144 : BitVec 32) +
                        kb1[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat =
                        2144 + inc.toNat := by
                      change (BitVec.setWidth 64 (2144#32 + inc)).toNat = 2144 + inc.toNat
                      exact h2144_idx
                    have h1888_inc_eq : (BitVec.setWidth 64 ((1888 : BitVec 32) +
                        kb1[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat =
                        1888 + inc.toNat := by
                      change (BitVec.setWidth 64 (1888#32 + inc)).toNat = 1888 + inc.toNat
                      exact h1888_idx
                    have hm_s_eq := k6_set_congr (xs := kbf1) h2144_inc_eq
                      (congrArg (· ||| (536870912 : BitVec 32))
                        (k6_get_congr (xs := kbf1) h2144_inc_eq h2144_inc_c0
                          (k6_2144_len_lt hinc hnc_le hkf1.1.base_ge)))
                    rw [hm_s_eq] at hm
                    have hkbf1s_ex : ∃ kbf1s : List (BitVec 32), invCore kbf1s ∧
                        kbf1s.length = kbuf.length ∧
                        kbf1s[1888 + inc.toNat]? = some off_i ∧
                        kbf1s[2144 + inc.toNat]? = some (oldmi ||| 0x20000000#32) ∧
                        (array (t := i32) pk kbf1s ⋆ R) m := by
                      refine ⟨kbf1.set (2144 + inc.toNat) (oldmi ||| 0x20000000#32),
                        invCore_set_meta hkf1 hinc hpmi'.1 hpmi'.2, by rw [List.length_set, hkf1_l],
                        ?_, ?_, hm⟩
                      · rw [List.getElem?_set_ne (by omega),
                          List.getElem?_eq_getElem (k6_1888_len_lt hinc hnc_le hkf1.1.base_ge)]
                      · have hbd_s : 2144 + inc.toNat < kbf1.length :=
                          k6_2144_len_lt hinc hnc_le hkf1.1.base_ge
                        rw [List.getElem?_set_self hbd_s]
                    obtain ⟨kbf1s, h_kbf1s, hk1s_l, h1888_sq, h2144_sq, hm_n⟩ := hkbf1s_ex
                    clear hm hpmi' h1888_sq h2144_sq
                    have hm := hm_n; clear hm_n
                    c0_hsplit
                    · have h1888_inc_mod : (BitVec.toNat (1888 : BitVec 32) +
                          kb1[(7 : BitVec 64).toNat].toNat) % 4294967296 =
                          1888 + inc.toNat := by
                        have h7eq : kb1[(7 : BitVec 64).toNat] = inc := rfl
                        rw [h7eq, show BitVec.toNat (1888 : BitVec 32) = 1888 from rfl]
                        exact k6_add_mod_lt (by decide) hinc hnc_le
                      have h2144_inc_mod : (BitVec.toNat (2144 : BitVec 32) +
                          kb1[(7 : BitVec 64).toNat].toNat) % 4294967296 =
                          2144 + inc.toNat := by
                        have h7eq : kb1[(7 : BitVec 64).toNat] = inc := rfl
                        rw [h7eq, show BitVec.toNat (2144 : BitVec 32) = 2144 from rfl]
                        exact k6_add_mod_lt (by decide) hinc hnc_le
                      have hget_1888_s : kbf1[(BitVec.toNat (1888 : BitVec 32) +
                          kb1[(7 : BitVec 64).toNat].toNat) % 4294967296]'(by
                            rw [h1888_inc_mod]
                            exact k6_1888_len_lt hinc hnc_le hkf1.1.base_ge) = off_i :=
                        k6_get_congr h1888_inc_mod _ _
                      have hget_2144_s : kbf1[(BitVec.toNat (2144 : BitVec 32) +
                          kb1[(7 : BitVec 64).toNat].toNat) % 4294967296]'(by
                            rw [h2144_inc_mod]
                            exact k6_2144_len_lt hinc hnc_le hkf1.1.base_ge) = oldmi :=
                        k6_get_congr h2144_inc_mod _ _
                      have hisz_bd : off_i.toNat + sz_i.toNat ≤ acap.toNat := by
                        have h7c0 : (OfNat.ofNat 7 % 2 ^ 64 : Nat) = 7 := rfl
                        have h2144n : BitVec.toNat (2144 : BitVec 32) = 2144 := rfl
                        have h1888n : BitVec.toNat (1888 : BitVec 32) = 1888 := rfl
                        have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
                        simp only [h2144n, h1888n, h232, h7c0] at hc
                        have hbd1 : (1888 + kb1[7].toNat) % 4294967296 < kbf1.length := by
                          change (BitVec.toNat (1888 : BitVec 32) +
                            kb1[(7 : BitVec 64).toNat].toNat) % 4294967296 < kbf1.length
                          rw [h1888_inc_mod]; exact k6_1888_len_lt hinc hnc_le hkf1.1.base_ge
                        have hbd2 : (2144 + kb1[7].toNat) % 4294967296 < kbf1.length := by
                          change (BitVec.toNat (2144 : BitVec 32) +
                            kb1[(7 : BitVec 64).toNat].toNat) % 4294967296 < kbf1.length
                          rw [h2144_inc_mod]; exact k6_2144_len_lt hinc hnc_le hkf1.1.base_ge
                        have hne12 : (2144 + kb1[7].toNat) % 4294967296 ≠
                            (1888 + kb1[7].toNat) % 4294967296 := by
                          rw [show (1888 + kb1[7].toNat) % 4294967296 = 1888 + inc.toNat from
                            h1888_inc_mod, show (2144 + kb1[7].toNat) % 4294967296 =
                            2144 + inc.toNat from h2144_inc_mod]; omega
                        have he1 : kbf1[(1888 + kb1[7].toNat) % 4294967296]'hbd1 = off_i :=
                          hget_1888_s
                        have he2 : kbf1[(2144 + kb1[7].toNat) % 4294967296]'hbd2 = oldmi :=
                          hget_2144_s
                        have hmod : (off_i.toNat + sz_i.toNat) % 4294967296 =
                            off_i.toNat + sz_i.toNat := Nat.mod_eq_of_lt hinc_sz_nw
                        have hnw : (oldmi.toNat ||| 536870912) &&& 65535 = sz_i.toNat := by
                          dsimp only [sz_i]; rw [BitVec.toNat_and, BitVec.toNat_or]; rfl
                        rw [List.getElem_set_ne hne12,
                          List.getElem_set_self (by rw [List.length_set]; exact hbd2),
                          he1, he2, BitVec.toNat_and, BitVec.toNat_or] at hc
                        simpa [hnw, hmod] using hc
                      clear hc
                      have hget_raw_off_i : ∀ hbd,
                          (kbf1.set (BitVec.setWidth 64 ((2144 : BitVec 32) +
                            kb1[(BitVec.ofNat (OfNat.ofNat 64)
                              (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat
                            (kbf1[(BitVec.setWidth 64 ((2144 : BitVec 32) +
                              kb1[(BitVec.ofNat (OfNat.ofNat 64)
                                (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat]'h2144_inc_c0 |||
                              (536870912 : BitVec 32)))[(BitVec.setWidth 64
                            ((1888 : BitVec 32) + kb1[(BitVec.ofNat (OfNat.ofNat 64)
                              (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat]'hbd = off_i := by
                        intro hbd
                        rw [List.getElem_set_ne (by
                          rw [h2144_inc_eq, h1888_inc_eq]; omega)]
                        exact k6_get_congr h1888_inc_eq _ _
                      have hget_raw_newmi : ∀ hbd,
                          (kbf1.set (BitVec.setWidth 64 ((2144 : BitVec 32) +
                            kb1[(BitVec.ofNat (OfNat.ofNat 64)
                              (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat
                            (kbf1[(BitVec.setWidth 64 ((2144 : BitVec 32) +
                              kb1[(BitVec.ofNat (OfNat.ofNat 64)
                                (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat]'h2144_inc_c0 |||
                              (536870912 : BitVec 32)))[(BitVec.setWidth 64
                            ((2144 : BitVec 32) + kb1[(BitVec.ofNat (OfNat.ofNat 64)
                              (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat]'hbd =
                            oldmi ||| (536870912 : BitVec 32) := by
                        intro hbd
                        rw [List.getElem_set_self (by
                          rw [List.length_set]; exact h2144_inc_c0)]
                        exact congrArg (· ||| (536870912 : BitVec 32))
                          (k6_get_congr h2144_inc_eq h2144_inc_c0
                            (k6_2144_len_lt hinc hnc_le hkf1.1.base_ge))
                      simp only [hget_raw_off_i, hget_raw_newmi]
                      clear hm_s_eq hget_raw_off_i hget_raw_newmi
                      c0_hsteps_nogrp
                      refine wp_loop_group (ts := [i32])
                        (fun rem (j, ()) mj1 => ∃ kbj1, invCore kbj1 ∧ j.toNat ≤ sz_i.toNat ∧
                          rem = sz_i.toNat - j.toNat ∧ (array (t := i32) pk kbj1 ⋆ R) mj1)
                        ?_ ?_
                      · rintro Li remi ⟨ji, ⟨⟩⟩ mj1 hLi ⟨kbj1, hkj1, hji, rfl, hmj1⟩
                        have hkj1_l := hkj1.2.1
                        c0_hsplit
                        · have hj_lt : ji.toNat < sz_i.toNat := by
                            have h7c0 : (OfNat.ofNat 7 % 2 ^ 64 : Nat) = 7 := rfl
                            have h2144n : BitVec.toNat (2144 : BitVec 32) = 2144 := rfl
                            have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
                            try simp only [h2144n, h232, h7c0] at hc
                            have hbd2 : (2144 + kb1[7].toNat) % 4294967296 < kbf1.length := by
                              change (BitVec.toNat (2144 : BitVec 32) +
                                kb1[(7 : BitVec 64).toNat].toNat) % 4294967296 < kbf1.length
                              rw [h2144_inc_mod]
                              exact k6_2144_len_lt hinc hnc_le hkf1.1.base_ge
                            have he2 : kbf1[(2144 + kb1[7].toNat) % 4294967296]'hbd2 = oldmi :=
                              hget_2144_s
                            have hnw : (oldmi.toNat ||| 536870912) &&& 65535 = sz_i.toNat := by
                              dsimp only [sz_i]; rw [BitVec.toNat_and, BitVec.toNat_or]; rfl
                            try rw [List.getElem_set_self
                              (by rw [List.length_set]; exact hbd2)] at hc
                            try rw [he2] at hc
                            try rw [BitVec.toNat_and, BitVec.toNat_or] at hc
                            simpa [hnw] using hc
                          clear hc
                          have hsz_lt : sz_i.toNat < 65536 := by
                            dsimp only [sz_i]; rw [BitVec.toNat_and]
                            exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                          have hji1 : (ji + 1#32).toNat = ji.toNat + 1 := by
                            have := hsz_lt; have := hj_lt; c0_bound
                          have har_j : 2912 + off_i.toNat + ji.toNat < kbj1.length := by
                            have := hkj1.1.length_ge
                            have h15_j : (kbj1[15]?.getD 0#32).toNat = acap.toNat := by
                              have := hkj1.2.2.1 15 (by omega) (Or.inl (by omega))
                              rw [this, k6_buf_get_eq (by omega)]
                            omega
                          have har_j_c0 : (BitVec.setWidth 64
                              ((2912 : BitVec 32) + off_i + ji)).toNat < kbj1.length := by
                            have := har_j; have := hkj1.1.length_lt; c0_bound
                          c0_hsteps_nogrp
                          refine wp_join0
                            (fun mj2 => ∃ kbj2, invCore kbj2 ∧ (array (t := i32) pk kbj2 ⋆ R) mj2)
                            ?_ ?_
                          · intro _ mj2 ⟨kbj2, hkj2, hmj2⟩
                            c0_hsteps!
                            exact hLi (sz_i.toNat - (ji + 1#32).toNat) (ji + 1#32, ())
                              mj2 (by have := hji1; omega)
                              ⟨kbj2, hkj2, by have := hji1; omega, rfl, hmj2⟩
                          · intro Jlv hJlv
                            c0_hsplit
                            · have hget_j_c0 : kbj1[(BitVec.setWidth 64
                                    ((2912 : BitVec 32) + off_i + ji)).toNat]'har_j_c0 =
                                  kbj1[2912 + off_i.toNat + ji.toNat]'har_j :=
                                k6_get_congr (by have := har_j; have := hkj1.1.length_lt; c0_bound)
                                  _ _
                              have hj_v_lt : ((kbj1[2912 + off_i.toNat + ji.toNat]'har_j) >>>
                                  (1 : Nat)).toNat < nv.toNat := by
                                have har_mod : (2912 + off_i.toNat + ji.toNat) % 4294967296 =
                                    2912 + off_i.toNat + ji.toNat := by
                                  have := har_j; have := hkj1.1.length_lt; omega
                                have h2912n : BitVec.toNat (2912 : BitVec 32) = 2912 := rfl
                                have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
                                rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                                simp only [h2912n, h232] at hc
                                rw [← k6_get_congr har_mod (by rw [har_mod]; exact har_j) har_j]
                                exact hc
                              clear hc
                              have h416_j_eq : (BitVec.setWidth 64 ((416 : BitVec 32) +
                                  (kbj1[(BitVec.setWidth 64
                                    ((2912 : BitVec 32) + off_i + ji)).toNat]'har_j_c0 >>>
                                  (1 : Nat)))).toNat =
                                  416 + ((kbj1[2912 + off_i.toNat + ji.toNat]'har_j) >>>
                                    (1 : Nat)).toNat := by
                                rw [hget_j_c0]; have := hj_v_lt; have := hnv_le; c0_bound
                              have h416_j_c0 : (BitVec.setWidth 64 ((416 : BitVec 32) +
                                  (kbj1[(BitVec.setWidth 64
                                    ((2912 : BitVec 32) + off_i + ji)).toNat]'har_j_c0 >>>
                                  (1 : Nat)))).toNat < kbj1.length := by
                                rw [h416_j_eq]; have := hj_v_lt; have := hnv_le
                                have := hkj1_l; have := hlen; omega
                              c0_hsteps!
                              have hmj_eq := k6_set_congr (xs := kbj1) h416_j_eq
                                (congrArg (· ||| (2 : BitVec 32))
                                  (k6_get_congr (xs := kbj1) h416_j_eq h416_j_c0
                                    (by have := hkj1_l; have := hlen; omega)))
                              rw [hmj_eq] at hm
                              exact hJlv _
                                ⟨_, invCore_set_flags hkj1
                                  (v := ((kbj1[2912 + off_i.toNat + ji.toNat]'har_j) >>>
                                    (1 : Nat)).toNat)
                                  (by have := hj_v_lt; have := hnv_le; omega) _,
                                  hm⟩
                            · c0_hsteps!; exact hJlv mj1 ⟨kbj1, hkj1, hmj1⟩
                        · c0_hsteps!; exact hJincCl mj1 ⟨kbj1, hkj1, hmj1⟩
                      · intro Li hLi; c0_hsteps!
                        exact hLi sz_i.toNat (0#32, ()) _
                          ⟨kbf1s, h_kbf1s, Nat.zero_le _, by simp, hm⟩
                    · c0_hsteps!
                      exact hJincCl _ ⟨kbf1s, h_kbf1s, hm⟩
              · intro Lf hLf; c0_hsteps!
                exact hLf nv.toNat (0#32, ()) m1 ⟨kb1, hk1, Nat.zero_le _, by simp, hm1⟩
            · c0_hsteps!; rw [hi1_nc]; exact hJinc (kb1, nc) m1 ⟨hk1, hm1⟩
      · intro L1 hL1; c0_hsteps!
        exact hL1 nc.toNat (0#32, ()) m0
          ⟨kbuf, ⟨hok0, rfl, fun _ _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩, Nat.zero_le _, by simp, hm0⟩
