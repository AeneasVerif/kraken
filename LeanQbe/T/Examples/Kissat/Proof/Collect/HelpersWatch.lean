/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges

/-!
# Watch, BitVec & Focus Helpers for `Proof.Collect` (`Proof.Collect.HelpersWatch`)

Pure bitvector lemmas (`bv32_bit21_*`, `bv32_lt_highbit_iff`, `bv8_gt0_of_dom`), watch-slice
invariants (`BinOnlyWatchSliceOk`, `BinOnlyWatchesInv`, `ModeWatchSliceOk`, `WatchSliceLtOk.*`,
`modeWatchesInv_shrink_slice`, `binOnlyWatchesInv_of_pop`), and separation focus helpers.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Collect

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullKissatMath
open LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
open Kraken.Bedrock2.Test

public section

/-! ## 1. BitVector, List & Separation-Focus Helpers -/

theorem bv64_add_nat {x : BitVec 64} (n : Nat) (hn : n < 2 ^ 64)
    (h : x.toNat + n < 2 ^ 64) : (x + BitVec.ofNat 64 n).toNat = x.toNat + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt h]

theorem bv64_add1 {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + (1 : BitVec 64)).toNat = x.toNat + 1 := bv64_add_nat 1 (by decide) h

theorem bv64_add2 {x : BitVec 64} (h : x.toNat + 2 < 2 ^ 64) :
    (x + (2 : BitVec 64)).toNat = x.toNat + 2 := bv64_add_nat 2 (by decide) h

theorem bv64_add3 {x : BitVec 64} (h : x.toNat + 3 < 2 ^ 64) :
    (x + (3 : BitVec 64)).toNat = x.toNat + 3 := bv64_add_nat 3 (by decide) h

theorem bv64_add4 {x : BitVec 64} (h : x.toNat + 4 < 2 ^ 64) :
    (x + (4 : BitVec 64)).toNat = x.toNat + 4 := bv64_add_nat 4 (by decide) h

theorem bv64_add1_lt {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := bv64_add1 h

theorem bv64_add2_lt {x : BitVec 64} (h : x.toNat + 2 < 2 ^ 64) :
    (x + 2#64).toNat = x.toNat + 2 := bv64_add2 h

theorem bv64_add3_lt {x : BitVec 64} (h : x.toNat + 3 < 2 ^ 64) :
    (x + 3#64).toNat = x.toNat + 3 := bv64_add3 h

theorem bv64_add4_lt {x : BitVec 64} (h : x.toNat + 4 < 2 ^ 64) :
    (x + 4#64).toNat = x.toNat + 4 := bv64_add4 h

theorem bv64_ofNat_toNat_id {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem bv32_add1 {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + (1 : BitVec 32)).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

theorem bv32_add1_lt {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := bv32_add1 h

theorem bv32_zext64_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat :=
  zext_toNat x (by decide)

theorem bv64_shl1_toNat_id {x : BitVec 64} (h : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat :=
  bv64_shl1_toNat h

theorem bv64_shr1_toNat (x : BitVec 64) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv32_shr1_toNat (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv64_add3_zext_lt {p : BitVec 64} {sz : BitVec 32}
    (hx : p.toNat + 3 + sz.toNat < 2 ^ 64) :
    (p + 3#64 + sz.setWidth 64).toNat = p.toNat + 3 + sz.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat sz (by decide),
    show (3#64).toNat = 3 from rfl,
    Nat.mod_eq_of_lt (by omega : p.toNat + 3 < 2 ^ 64), Nat.mod_eq_of_lt hx]

theorem bv8_sext32_eq0_of_dom {x : BitVec 8}
    (hd : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) : x.signExtend 32 = 0#32 ↔ x = 0#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

theorem bv8_gt0_of_dom {x : BitVec 8} (hdom : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    ((0#32).slt (x.signExtend 32) = true ↔ x = 1#8) ∧
    ((x.signExtend 32).slt 0#32 = true ↔ x = 0xFF#8) := by
  rcases hdom with rfl | rfl | rfl <;> decide

theorem bv32_bit21_or_pres (x : BitVec 32) :
    ((x ||| 0x00200000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) ∧
    ((x ||| 0x00200000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) ∧
    ((x ||| 0x00200000#32) &&& 0x00200000#32) ≠ 0#32 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i hi
    have h0 : ((0x00200000#32)[i] && (0x00080000#32)[i]) = false := by
      rw [← BitVec.getElem_and]; exact BitVec.getElem_zero hi
    simp [BitVec.getElem_and, BitVec.getElem_or, Bool.and_or_distrib_right, h0]
  · ext i hi
    have h0 : ((0x00200000#32)[i] && (0x00800000#32)[i]) = false := by
      rw [← BitVec.getElem_and]; exact BitVec.getElem_zero hi
    simp [BitVec.getElem_and, BitVec.getElem_or, Bool.and_or_distrib_right, h0]
  · intro h; have h21 := congrArg (·[21]) h
    revert h21; simp [show (0x00200000#32)[21] = true from rfl]

theorem bv32_bit21_clear_pres (x : BitVec 32) :
    ((x &&& ~~~0x00200000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) ∧
    ((x &&& ~~~0x00200000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) :=
  ⟨by rw [BitVec.and_assoc]; rfl, by rw [BitVec.and_assoc]; rfl⟩

theorem bv32_clear_shrk_rsn (x : BitVec 32) (hng : (x &&& 0x00080000#32) = 0#32) :
    ((x &&& ~~~(0x00800000#32 ||| 0x00200000#32)) &&& 0x00800000#32) = 0#32 ∧
    ((x &&& ~~~(0x00800000#32 ||| 0x00200000#32)) &&& 0x00080000#32) = 0#32 :=
  ⟨by rw [BitVec.and_assoc]; exact BitVec.and_zero, by rw [BitVec.and_assoc]; exact hng⟩

theorem bv32_litmask_of_lt {x : BitVec 32} (hx : x.toNat < 0x80000000) :
    x &&& 0x7FFFFFFF#32 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx]

theorem bv32_large_word_props (w : BitVec 32) :
    ((w &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 ∧
    (w &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 := by
  refine ⟨by rw [BitVec.and_assoc]; exact BitVec.and_zero, fun h => ?_⟩
  have h31 := congrArg (·[31]) h
  revert h31; simp [show (0x7FFFFFFF#32)[31] = false from rfl,
    show (0xFFFFFFFF#32)[31] = true from rfl]

theorem bv32_lt_highbit_iff (r : BitVec 32) :
    r.toNat < 0x80000000 ↔ (r &&& 0x80000000#32) = 0#32 := by
  constructor
  · intro h; rw [← bv32_litmask_of_lt h]; exact (bv32_large_word_props r).1
  · intro h
    have h31 : r[31] = false := by
      have hc := congrArg (·[31]) h
      simpa [show (0x80000000#32)[31] = true by decide] using hc
    have htb := BitVec.getElem_eq_testBit_toNat (x := r) (i := 31) (by decide)
    rw [h31] at htb
    have hmod : (r.toNat / 2 ^ 31) % 2 = 0 := by
      simpa [Nat.testBit, Nat.shiftRight_eq_div_pow] using htb.symm
    have hlt := r.isLt
    omega

theorem rw_ite_pos {α : Sort _} {P : Prop} {_ : Decidable P} {a b : α} (h : P) :
    (if P then a else b) = a := ite_eq_left_of_eq_true a b (eq_true h)

theorem rw_ite_neg {α : Sort _} {P : Prop} {_ : Decidable P} {a b : α} (h : ¬ P) :
    (if P then a else b) = b := ite_eq_right_of_eq_false a b (eq_false h)

theorem drop_take_succ {α : Type} {xs : List α} {off n : Nat} (hlt : off + n < xs.length) :
    (xs.drop off).take (n + 1) = (xs.drop off).take n ++ [xs[off + n]'hlt] := by
  have h1 : n < (xs.drop off).length := by simp; omega
  rw [List.take_add_one, List.getElem?_eq_getElem h1, List.getElem_drop]; simp

theorem drop_take_set_append {α : Type} {xs : List α} {off n : Nat} {v : α}
    (hlt : off + n < xs.length) :
    ((xs.set (off + n) v).drop off).take (n + 1) = (xs.drop off).take n ++ [v] := by
  have hlt' : off + n < (xs.set (off + n) v).length := by simp [hlt]
  rw [drop_take_succ hlt', List.getElem_set_self hlt']; congr 1
  refine List.ext_getElem (by simp) fun j hj1 _ => ?_
  have hjn : j < n := by simp at hj1; omega
  simp only [List.getElem_take, List.getElem_drop]; rw [List.getElem_set_ne (by omega)]

@[expose] def FullValsLvlRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  array (t := i8) c.pLitMark s.core.lit_mark ⋆ array (t := i8) c.pMark s.core.mrk ⋆
  array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pReason s.core.rsns ⋆
  array (t := i32) c.pTrail s.core.trl ⋆ array (t := i32) c.pTrailPos s.core.trail_pos ⋆
  array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
  FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆ FullScratchArrays c s.scratch ⋆ c.pad

theorem focus_full_vals_lvl {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i8) c.pVals s.core.vals ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
      (FullValsLvlRest c s ⋆ R)) m := by
  unfold FullMem FullCoreArrays FullCoreByteArrs FullCoreU32A at hm
  unfold FullValsLvlRest; ecancel

theorem unfocus_full_vals_lvl {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i8) c.pVals s.core.vals ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
      (FullValsLvlRest c s ⋆ R)) m) :
    (FullMem c s ⋆ R) m := by
  unfold FullMem FullCoreArrays FullCoreByteArrs FullCoreU32A
  unfold FullValsLvlRest at hm; ecancel

theorem fullWitnessInv_with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {oom' : BitVec 64} (hw : FullWitnessInv c F0 F_cur k) :
    FullWitnessInv c F0 F_cur { k with oom := oom' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

/-! ## 2. Watch-Slice Invariants & `WatchSliceLtOk` Combinators -/

/-- Watch slice containing only valid binary watches (arena-independent). -/
inductive BinOnlyWatchSliceOk (F_cur : List (List Nat)) (k : FullCoreState) (lit : Nat) :
    Nat → Nat → Prop where
  | empty {p} : BinOnlyWatchSliceOk F_cur k lit p 0
  | bin {p rem w0} :
      k.wstk[p]? = some w0 → (w0 &&& 0x80000000#32) ≠ 0#32 → w0 ≠ 0xFFFFFFFF#32 →
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) →
      BinOnlyWatchSliceOk F_cur k lit (p + 1) rem →
      BinOnlyWatchSliceOk F_cur k lit p (rem + 1)

/-- All watch lists contain only valid binary watches. -/
structure BinOnlyWatchesInv (F_cur : List (List Nat)) (k : FullCoreState) : Prop where
  layout : WatchStackLayout k
  slices : ∀ l < 2 * k.cur_vars,
    BinOnlyWatchSliceOk F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l)

/-- Mode-indexed single-literal slice validity (`false` = sparse 2WL, `true` = dense occ). -/
@[expose] def ModeWatchSliceOk (dense : Bool) (F_cur : List (List Nat)) (k : FullCoreState)
    (lit p rem : Nat) : Prop :=
  if dense then DenseWatchSliceOk F_cur k lit p rem else WatchSliceOk F_cur k lit p rem

theorem BinOnlyWatchSliceOk.toWatchSliceOk {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : BinOnlyWatchSliceOk F_cur k lit p rem) :
    WatchSliceOk F_cur k lit p rem := by
  induction h with
  | empty => exact .empty
  | bin hp hf hne hlt hent _ ih => exact .bin hp hf hne hlt hent ih

theorem BinOnlyWatchSliceOk.toDenseWatchSliceOk {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : BinOnlyWatchSliceOk F_cur k lit p rem) :
    DenseWatchSliceOk F_cur k lit p rem := by
  induction h with
  | empty => exact .empty
  | bin hp hf hne hlt hent _ ih => exact .bin hp hf hne hlt hent ih

theorem BinOnlyWatchSliceOk.ne_sentinel {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : BinOnlyWatchSliceOk F_cur k lit p rem) :
    ∀ idx < rem, k.wstk[p + idx]? ≠ some 0xFFFFFFFF#32 := h.toWatchSliceOk.ne_sentinel

theorem BinOnlyWatchSliceOk.forall_elem {F_cur : List (List Nat)} {k : FullCoreState}
    {lit : Nat} : ∀ {p rem : Nat}, BinOnlyWatchSliceOk F_cur k lit p rem →
      ∀ idx < rem,
        let w := k.wstk[p + idx]?.getD 0#32
        (w &&& 0x80000000#32) ≠ 0#32 ∧ (w &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w &&& 0x7FFFFFFF#32).toNat])
  | _, _, .empty, _, hi => absurd hi (Nat.not_lt_zero _)
  | _, _, .bin hp hf _ hlt hent _, 0, _ => by
    simpa [Nat.add_zero, hp] using And.intro hf (And.intro hlt hent)
  | p, _, .bin _ _ _ _ _ hrest, idx + 1, hi => by
    rw [show p + (idx + 1) = (p + 1) + idx by omega]
    exact hrest.forall_elem idx (Nat.lt_of_succ_lt_succ hi)

theorem BinOnlyWatchSliceOk.relocate {F F' : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hF : (cnfOfClauses F').Entails (cnfOfClauses F))
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hwstk : ∀ j < rem, k'.wstk[p' + j]? = k.wstk[p + j]?)
    (h : BinOnlyWatchSliceOk F k lit p rem) : BinOnlyWatchSliceOk F' k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hf hne hlt hent _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hne (by omega)
      (CNF.entails_clause_trans hF hent) (ih (p' := p' + 1) fun j hj => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 1) (by omega))

theorem BinOnlyWatchSliceOk.append_bin {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hwstk : ∀ j < rem, k'.wstk[p' + j]? = k.wstk[p + j]?)
    (h : BinOnlyWatchSliceOk F_cur k lit p rem) (hw0 : k'.wstk[p' + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    BinOnlyWatchSliceOk F_cur k' lit p' (rem + 1) := by
  induction h generalizing p' with
  | empty => exact .bin (by simpa using hw0) hflag hne hlt hent .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he
      (ih (p' := p' + 1)
        (fun j hj => by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 1) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0))

theorem BinOnlyWatchesInv.toWatchesInv {F_cur : List (List Nat)} {k : FullCoreState}
    (h : BinOnlyWatchesInv F_cur k) : WatchesInv F_cur k :=
  ⟨h.layout, fun l hl => (h.slices l hl).toWatchSliceOk⟩

theorem BinOnlyWatchesInv.toDenseWatchesInv {F_cur : List (List Nat)} {k : FullCoreState}
    (h : BinOnlyWatchesInv F_cur k) : DenseWatchesInv F_cur k :=
  ⟨h.layout, fun l hl => (h.slices l hl).toDenseWatchSliceOk⟩

theorem BinOnlyWatchesInv.toFull {F_cur : List (List Nat)} {k : FullCoreState}
    (h : BinOnlyWatchesInv F_cur k) : FullBinOnlyWatchesInv F_cur k :=
  ⟨h.layout, fun l hl i hi => (h.slices l hl).forall_elem i hi⟩

theorem BinOnlyWatchesInv.toModeWatchesInv {F_cur : List (List Nat)} {k : FullCoreState}
    (h : BinOnlyWatchesInv F_cur k) : ModeWatchesInv F_cur k := by
  by_cases hc : k.dense_mode = 0#64 <;> simp only [ModeWatchesInv, hc, ↓reduceIte]
  · exact h.toWatchesInv
  · exact h.toDenseWatchesInv

theorem BinOnlyWatchesInv.with_core {F_cur : List (List Nat)} {k k' : FullCoreState}
    (h : BinOnlyWatchesInv F_cur k) (hvars : k'.cur_vars = k.cur_vars)
    (hw : k'.wvec = k.wvec) (hs : k'.wstk = k.wstk) (hl : k'.wlen = k.wlen) :
    BinOnlyWatchesInv F_cur k' := by
  refine ⟨h.layout.with_wstk hvars hw hs hl, fun l hl' => ?_⟩
  have ho : fullWatchOffCore k' l = fullWatchOffCore k l := by unfold fullWatchOffCore; rw [hw]
  have hsz : fullWatchSizeCore k' l = fullWatchSizeCore k l := by unfold fullWatchSizeCore; rw [hw]
  rw [ho, hsz]
  exact (h.slices l (hvars ▸ hl')).relocate (by rw [CNF.entails_def]; exact fun _ p => p)
    (by omega) (fun _ _ => by rw [hs])

theorem FullBinOnlyWatchesInv.toBinOnly {F_cur : List (List Nat)} {k : FullCoreState}
    (h : FullBinOnlyWatchesInv F_cur k) : BinOnlyWatchesInv F_cur k := by
  refine ⟨h.1, fun l hl => ?_⟩
  let off := fullWatchOffCore k l
  let sz := fullWatchSizeCore k l
  have go : ∀ rem, rem ≤ sz →
      BinOnlyWatchSliceOk F_cur k l (off + (sz - rem)) rem := by
    intro rem hle
    induction rem with
    | zero => exact .empty
    | succ r ih =>
      have hi : sz - (r + 1) < sz := by omega
      obtain ⟨hf, hlt, hent⟩ := h.2 l hl (sz - (r + 1)) hi
      have hsome : ∃ w0, k.wstk[off + (sz - (r + 1))]? = some w0 := by
        cases hw : k.wstk[off + (sz - (r + 1))]? with
        | none => rw [hw, Option.getD_none] at hf; exact absurd rfl hf
        | some w0 => exact ⟨w0, rfl⟩
      obtain ⟨w0, hw0⟩ := hsome
      have hne : w0 ≠ 0xFFFFFFFF#32 := by
        have hns := h.1.no_sentinel l hl (sz - (r + 1)) hi
        rw [hw0] at hns; exact fun heq => hns (congrArg some heq)
      have helem : ∀ P : Prop, (P → P) := fun P h => h
      rw [hw0, Option.getD_some] at hf hlt hent
      have hrest := ih (by omega)
      rw [show off + (sz - r) = off + (sz - (r + 1)) + 1 by omega] at hrest
      exact .bin hw0 hf hne hlt hent hrest
  simpa [off, sz] using go sz (Nat.le_refl _)

theorem WatchSliceLtOk.toBinOnly {F_cur : List (List Nat)} {k : FullCoreState} {lit p rem : Nat}
    (h : WatchSliceLtOk 0 F_cur k lit p rem) : BinOnlyWatchSliceOk F_cur k lit p rem := by
  induction h with
  | empty => exact .empty
  | bin hp hf hne hlt hent _ ih => exact .bin hp hf hne hlt hent ih
  | large _ _ _ _ hk => cases hk

theorem ModeWatchSliceOk.step {dense : Bool} {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} {w0 : BitVec 32} (h : ModeWatchSliceOk dense F_cur k lit p rem)
    (hpos : 0 < rem) (hw0 : k.wstk[p]? = some w0) :
    ((w0 &&& 0x80000000#32) ≠ 0#32 →
      w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      ModeWatchSliceOk dense F_cur k lit (p + 1) (rem - 1)) ∧
    ((w0 &&& 0x80000000#32) = 0#32 →
      2 ≤ rem ∧ ∃ cr, k.wstk[p + 1]? = some cr ∧ (dense = true → 3 ≤ w0.toNat) ∧
        cr.toNat < 0x80000000 ∧ cr.toNat ∈ fullArenaClauseRefsCore k ∧
        ModeWatchSliceOk dense F_cur k lit (p + 2) (rem - 2)) := by
  cases dense <;> simp only [ModeWatchSliceOk, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · cases h with
    | empty => omega
    | bin hp hf hne hlt hent hrest =>
      rw [hp] at hw0; cases hw0
      exact ⟨fun _ => ⟨hne, hlt, hent, by simpa using hrest⟩, fun h0 => absurd h0 hf⟩
    | large hp hp1 hf hlt href hrest =>
      rw [hp] at hw0; cases hw0
      exact ⟨fun hne => absurd hf hne,
        fun _ => ⟨by omega, _, hp1, fun hc => False.elim hc, hlt, href, by simpa using hrest⟩⟩
  · cases h with
    | empty => omega
    | bin hp hf hne hlt hent hrest =>
      rw [hp] at hw0; cases hw0
      exact ⟨fun _ => ⟨hne, hlt, hent, by simpa using hrest⟩, fun h0 => absurd h0 hf⟩
    | occ hp hp1 hf hsz hlt href hrest =>
      rw [hp] at hw0; cases hw0
      exact ⟨fun hne => absurd hf hne,
        fun _ => ⟨by omega, _, hp1, fun _ => hsz, hlt, href, by simpa using hrest⟩⟩

theorem modeWatchesInv_slice_of_lt {F_cur : List (List Nat)} {k : FullCoreState}
    (h : ModeWatchesInv F_cur k) {l : Nat} (hl : l < 2 * k.cur_vars) :
    ModeWatchSliceOk (decide (k.dense_mode ≠ 0#64)) F_cur k l
      (fullWatchOffCore k l) (fullWatchSizeCore k l) := by
  by_cases hc : k.dense_mode = 0#64 <;>
    simp only [ModeWatchesInv, ModeWatchSliceOk, hc, ne_eq, not_true_eq_false, decide_false,
      not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · exact h.slices l hl
  · exact h.slices l hl

theorem watchStackLayout_shrink_slice {c : FullCfg} {k : FullCoreState}
    (hlay : WatchStackLayout k) (hlen : k.LengthsOk c)
    {lit new_sz : Nat} (hlit : lit < 2 * k.cur_vars) (hle : new_sz ≤ fullWatchSizeCore k lit)
    {wstk' : List (BitVec 32)}
    (hout : ∀ i, i < fullWatchOffCore k lit ∨
      fullWatchOffCore k lit + fullWatchSizeCore k lit ≤ i → wstk'[i]? = k.wstk[i]?)
    (hns : ∀ j < new_sz, wstk'[fullWatchOffCore k lit + j]? ≠ some 0xFFFFFFFF#32)
    (wu' nb' : BitVec 64) :
    let k' : FullCoreState :=
      { k with wvec := k.wvec.set (2 * lit + 1) (BitVec.ofNat 32 new_sz),
               wstk := wstk', wusable := wu', num_binary := nb' }
    WatchStackLayout k' ∧ fullWatchOffCore k' lit = fullWatchOffCore k lit ∧
    fullWatchSizeCore k' lit = new_sz ∧
    (∀ l < 2 * k.cur_vars, l ≠ lit →
      fullWatchOffCore k' l = fullWatchOffCore k l ∧
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ j < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k l + j]? = k.wstk[fullWatchOffCore k l + j]?) := by
  intro k'
  have hlt32 : new_sz < 2 ^ 32 := by
    have := (k.wvec[2 * lit + 1]?.getD 0#32).isLt; unfold fullWatchSizeCore at hle; omega
  have hwv_len : 2 * lit + 1 < k.wvec.length := by
    have := hlen.wvec_len; have := hlen.cur_vars_le; omega
  have hoff_eq : ∀ l, fullWatchOffCore k' l = fullWatchOffCore k l := fun l => by
    unfold fullWatchOffCore k'; rw [List.getElem?_set_ne (by omega)]
  have hsz_self : fullWatchSizeCore k' lit = new_sz := by
    unfold fullWatchSizeCore k'; rw [List.getElem?_set_self hwv_len, Option.getD_some,
      bv32_ofNat_toNat hlt32]
  have hsz_ne : ∀ l, l ≠ lit → fullWatchSizeCore k' l = fullWatchSizeCore k l := fun l hne => by
    unfold fullWatchSizeCore k'; rw [List.getElem?_set_ne (by omega)]
  have hother : ∀ l < 2 * k.cur_vars, l ≠ lit →
      fullWatchOffCore k' l = fullWatchOffCore k l ∧
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ j < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k l + j]? = k.wstk[fullWatchOffCore k l + j]? := fun l hl hne =>
    ⟨hoff_eq l, hsz_ne l hne, fun j hj => by
      by_cases hsz0 : fullWatchSizeCore k lit = 0
      · exact hout _ (by omega)
      · rcases hlay.disjoint l lit hl hlit hne (by omega) (by omega) with h1 | h2
        · exact hout _ (Or.inl (by omega))
        · exact hout _ (Or.inr (by omega))⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hoff_eq lit, hsz_self, hother⟩
  · intro l hl; by_cases e : l = lit
    · subst e; rw [hoff_eq, hsz_self]; have := hlay.bounds _ hlit; dsimp [k']; omega
    · rw [hoff_eq, hsz_ne l e]; exact hlay.bounds l hl
  · intro l hl hpos; by_cases e : l = lit
    · subst e; rw [hoff_eq]; rw [hsz_self] at hpos; exact hlay.pos_off _ hlit (by omega)
    · rw [hoff_eq]; rw [hsz_ne l e] at hpos; exact hlay.pos_off l hl hpos
  · intro l1 l2 h1 h2 hne hp1 hp2; rw [hoff_eq, hoff_eq]
    by_cases e1 : l1 = lit
    · subst e1; rw [hsz_self] at hp1 ⊢; rw [hsz_ne l2 (Ne.symm hne)] at hp2 ⊢
      rcases hlay.disjoint _ l2 h1 h2 hne (by omega) hp2 with ha | hb
      · exact Or.inl (by omega)
      · exact Or.inr hb
    · rw [hsz_ne l1 e1] at hp1 ⊢
      by_cases e2 : l2 = lit
      · subst e2; rw [hsz_self] at hp2 ⊢
        rcases hlay.disjoint l1 _ h1 h2 hne hp1 (by omega) with ha | hb
        · exact Or.inl ha
        · exact Or.inr (by omega)
      · rw [hsz_ne l2 e2] at hp2 ⊢; exact hlay.disjoint l1 l2 h1 h2 hne hp1 hp2
  · intro l hl idx hidx; by_cases e : l = lit
    · subst e; rw [hoff_eq]; rw [hsz_self] at hidx; exact hns idx hidx
    · obtain ⟨ho, hs, hw⟩ := hother l hl e
      rw [ho]; rw [hs] at hidx; rw [hw idx hidx]; exact hlay.no_sentinel l hl idx hidx

theorem modeWatchesInv_shrink_slice {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (hw : ModeWatchesInv F_cur k) (hlen : k.LengthsOk c)
    {lit new_sz : Nat} (hlit : lit < 2 * k.cur_vars) (hle : new_sz ≤ fullWatchSizeCore k lit)
    {wstk' : List (BitVec 32)}
    (hout : ∀ i, i < fullWatchOffCore k lit ∨
      fullWatchOffCore k lit + fullWatchSizeCore k lit ≤ i → wstk'[i]? = k.wstk[i]?)
    (wu' nb' : BitVec 64)
    (hslice : ModeWatchSliceOk (decide (k.dense_mode ≠ 0#64)) F_cur
      { k with wstk := wstk' } lit (fullWatchOffCore k lit) new_sz) :
    ModeWatchesInv F_cur
      { k with wvec := k.wvec.set (2 * lit + 1) (BitVec.ofNat 32 new_sz),
               wstk := wstk', wusable := wu', num_binary := nb' } := by
  let k' : FullCoreState :=
    { k with wvec := k.wvec.set (2 * lit + 1) (BitVec.ofNat 32 new_sz),
             wstk := wstk', wusable := wu', num_binary := nb' }
  let kw : FullCoreState := { k with wstk := wstk' }
  change ModeWatchSliceOk (decide (k.dense_mode ≠ 0#64)) F_cur kw lit (fullWatchOffCore k lit)
    new_sz at hslice
  change ModeWatchesInv F_cur k'
  have hslice_ns : ∀ idx < new_sz, wstk'[fullWatchOffCore k lit + idx]? ≠ some 0xFFFFFFFF#32 := by
    cases hd : decide (k.dense_mode ≠ 0#64)
    · simp only [ModeWatchSliceOk, hd, Bool.false_eq_true, ↓reduceIte] at hslice
      exact hslice.ne_sentinel
    · simp only [ModeWatchSliceOk, hd, ↓reduceIte] at hslice
      exact hslice.ne_sentinel
  obtain ⟨hlay', hoff_self, hsz_self, hother⟩ :=
    watchStackLayout_shrink_slice hw.layout hlen hlit hle hout hslice_ns wu' nb'
  have hrefs : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k' := fun _ r => r
  have hrefs2 : ∀ r ∈ fullArenaClauseRefsCore kw, r ∈ fullArenaClauseRefsCore k' := fun _ r => r
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ p => p
  have hcv1 : k.cur_vars ≤ k'.cur_vars := Nat.le_refl _
  have hcv2 : kw.cur_vars ≤ k'.cur_vars := Nat.le_refl _
  by_cases hc : k.dense_mode = 0#64
  · simp only [ModeWatchesInv, ModeWatchSliceOk, show k'.dense_mode = k.dense_mode from rfl,
      hc, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hw hslice ⊢
    refine ⟨hlay', fun l hl => ?_⟩; by_cases e : l = lit
    · subst e; rw [hoff_self, hsz_self]
      exact fullWatchSlice_relocate hrefl hcv2 hrefs2 (fun _ _ => rfl) hslice
    · obtain ⟨ho, hs, hws⟩ := hother l hl e; rw [ho, hs]
      exact fullWatchSlice_relocate hrefl hcv1 hrefs hws (hw.slices l hl)
  · simp only [ModeWatchesInv, ModeWatchSliceOk, show k'.dense_mode = k.dense_mode from rfl,
      hc, decide_eq_true hc, ↓reduceIte] at hw hslice ⊢
    refine ⟨hlay', fun l hl => ?_⟩; by_cases e : l = lit
    · subst e; rw [hoff_self, hsz_self]; exact hslice.relocate hrefl hcv2 hrefs2 (fun _ _ => rfl)
    · obtain ⟨ho, hs, hws⟩ := hother l hl e; rw [ho, hs]
      exact (hw.slices l hl).relocate hrefl hcv1 hrefs hws

theorem fullWstackDefrag_preserves_binOnly {F_cur : List (List Nat)} {k k' : FullCoreState}
    (hw : BinOnlyWatchesInv F_cur k) (hlay : WatchStackLayout k')
    (hvars : k'.cur_vars = k.cur_vars)
    (hpres : ∀ l < 2 * k.cur_vars, fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ j < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + j]? = k.wstk[fullWatchOffCore k l + j]?) :
    BinOnlyWatchesInv F_cur k' := by
  refine ⟨hlay, fun l hl => ?_⟩
  obtain ⟨hsz, hslice⟩ := hpres l (hvars ▸ hl); rw [hsz]
  exact (hw.slices l (hvars ▸ hl)).relocate (by rw [CNF.entails_def]; exact fun _ p => p)
    (by omega) hslice

theorem fullWatchPush_preserves_binOnly {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit w0 : BitVec 32} {ok : Bool} (hw : BinOnlyWatchesInv F_cur k)
    (hlay : WatchStackLayout k') (hvars : k'.cur_vars = k.cur_vars)
    (hbin : (w0 &&& 0x80000000#32) ≠ 0#32 ∧ w0 ≠ 0xFFFFFFFF#32 ∧
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [lit.toNat, (w0 &&& 0x7FFFFFFF#32).toNat]))
    (hother : ∀ l < 2 * k.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ j < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + j]? = k.wstk[fullWatchOffCore k l + j]?)
    (hok_t : ok = true → lit.toNat < 2 * k.cur_vars ∧
      fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat + 1 ∧
      (∀ j < fullWatchSizeCore k lit.toNat,
        k'.wstk[fullWatchOffCore k' lit.toNat + j]? = k.wstk[fullWatchOffCore k lit.toNat + j]?) ∧
      k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat]? = some w0)
    (hok_f : ok = false → lit.toNat < 2 * k.cur_vars →
      fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat ∧
      ∀ j < fullWatchSizeCore k lit.toNat,
        k'.wstk[fullWatchOffCore k' lit.toNat + j]? = k.wstk[fullWatchOffCore k lit.toNat + j]?) :
    BinOnlyWatchesInv F_cur k' := by
  refine ⟨hlay, fun l hl => ?_⟩
  have hl0 : l < 2 * k.cur_vars := hvars ▸ hl
  by_cases hle : l = lit.toNat
  · subst hle; cases ok with
    | false =>
      obtain ⟨hsz, hslice⟩ := hok_f rfl hl0; rw [hsz]
      exact (hw.slices _ hl0).relocate (by rw [CNF.entails_def]; exact fun _ p => p)
        (by omega) hslice
    | true =>
      obtain ⟨_, hsz, hpre, hw0⟩ := hok_t rfl; rw [hsz]
      exact (hw.slices _ hl0).append_bin (by omega) hpre hw0 hbin.1 hbin.2.1 (by omega) hbin.2.2.2
  · obtain ⟨hsz, hslice⟩ := hother l hl0 hle; rw [hsz]
    exact (hw.slices l hl0).relocate (by rw [CNF.entails_def]; exact fun _ p => p)
      (by omega) hslice

theorem binOnlyWatchesInv_of_pop {F_cur : List (List Nat)} {k0 k2 k3 : FullCoreState} {lit : Nat}
    (hb0 : BinOnlyWatchesInv F_cur k0) (hb2 : BinOnlyWatchesInv F_cur k2)
    (hlay3 : WatchStackLayout k3) (hcv2 : k2.cur_vars = k0.cur_vars)
    (hcv3 : k3.cur_vars = k0.cur_vars) (hlit : lit < 2 * k0.cur_vars)
    (hpop_lit : fullWatchSizeCore k3 lit = fullWatchSizeCore k0 lit ∧
      ∀ j < fullWatchSizeCore k0 lit,
        k3.wstk[fullWatchOffCore k3 lit + j]? = k0.wstk[fullWatchOffCore k0 lit + j]?)
    (hpop_oth : ∀ l < 2 * k0.cur_vars, l ≠ lit →
      fullWatchSizeCore k3 l = fullWatchSizeCore k2 l ∧
      ∀ j < fullWatchSizeCore k2 l,
        k3.wstk[fullWatchOffCore k3 l + j]? = k2.wstk[fullWatchOffCore k2 l + j]?) :
    BinOnlyWatchesInv F_cur k3 := by
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  refine ⟨hlay3, fun l hl => ?_⟩
  by_cases hle : l = lit
  · rw [hle, hpop_lit.1]; exact (hb0.slices lit hlit).relocate hrefl (by omega) hpop_lit.2
  · obtain ⟨hs, hslice⟩ := hpop_oth l (hcv3 ▸ hl) hle; rw [hs]
    exact (hb2.slices l (hcv2 ▸ hcv3 ▸ hl)).relocate hrefl (by omega) hslice

end

end LeanQbe.T.Examples.Kissat.Proof.Collect
