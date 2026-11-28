/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMulSpecs
public import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas

/-!
# Shared Bitvector & Separation Helpers (`Bitblast.Proof.OpsShiftMulHelpers`)

Pure `BitVec`/`SliceDenotes`/`SliceLitsWf` lemmas (shift doubling/saturation, `mulRec`,
`clzAuxRec`, pure-lits reindexing), `BVHdr`/`array i32 litsPool` access helpers, and factored
step lemmas keeping all `OpsShiftMul{0,1,2}` WP proofs concise and under `420` lines.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open Std.Tactic.BVDecide
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open Std.ExtHashMap
open LeanQbe.T.Examples.Bitblast.Ref

@[expose] public section

/-! ## 1. Pure Semantic Helper Definitions -/

/-- Evaluates a `w`-literal slice of `litsPool` starting at `off` in AIG `g` under `ρ`. -/
def evalPoolSlice (g : Aig) (ρ : Nat → Bool) (litsPool : List (BitVec 32))
    (off w : Nat) : BitVec w :=
  (BitVec.ofBoolListLE
    ((List.range w).map fun j => g.evalLit ρ (UInt32.ofBitVec (litsPool.getD (off + j) 0#32)))).cast
    (by simp)

/-- Boolean OR scan of `p i` over `[lo, hi)` by structural recursion on `hi`. -/
def anyOrBool (p : Nat → Bool) (lo : Nat) : Nat → Bool
  | 0 => false
  | hi + 1 => if lo ≤ hi then anyOrBool p lo hi || p hi else false

/-- Iterative prefix-recurrence for `BitVec.clz`, indexing the bit position `curr` scanned so
far (`0 .. w`). -/
def clzAux {w : Nat} (x : BitVec w) : Nat → BitVec w
  | 0 => BitVec.ofNat w w
  | k + 1 => if x.getLsbD k = true then BitVec.ofNat w (w - 1 - k) else clzAux x k

/-- Partial shift value denoted by `out` after `pow` doubling stages of `bv_blast_shift_var`. -/
def bvShiftCur {w nw : Nat} (op : BitVec 32) (va : BitVec w) (vb : BitVec nw)
    (pow : Nat) : BitVec w :=
  bvShiftSem op va (BitVec.ofNat nw (vb.toNat % 2 ^ pow))

end

/-! ## 2. AIG Literal, `SliceLitsWf`, and `evalPoolSlice` Lemmas -/

public section

theorem ofBv_shr1_toNat (l : BitVec 32) :
    ((UInt32.ofBitVec l) >>> 1).toNat = (l >>> 1).toNat := by
  rw [UInt32.toNat_shiftRight, show (1 : UInt32).toNat = 1 from rfl,
    show 1 % 32 = 1 from rfl, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  change ((l.toNat / 2) : Nat) = (l >>> 1).toNat
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]

theorem evalLit_ofBv_zero (g : Aig) (ρ : Nat → Bool) :
    g.evalLit ρ (UInt32.ofBitVec 0#32) = false := by
  change g.evalLit ρ 0 = false
  exact Aig.evalLit_zero g ρ

theorem evalLit_ofBv_one (g : Aig) (ρ : Nat → Bool) :
    g.evalLit ρ (UInt32.ofBitVec 1#32) = true := by
  change g.evalLit ρ 1 = true
  exact Aig.evalLit_one g ρ

theorem SliceLitsWf.zero_shr1 (g : Aig) :
    ((0#32 : BitVec 32) >>> 1).toNat < g.A + 1 + g.nodes.size := by
  rw [show ((0#32 : BitVec 32) >>> 1).toNat = 0 from rfl]
  omega

theorem SliceLitsWf.one_shr1 (g : Aig) :
    ((1#32 : BitVec 32) >>> 1).toNat < g.A + 1 + g.nodes.size := by
  rw [show ((1#32 : BitVec 32) >>> 1).toNat = 0 from rfl]
  omega

theorem SliceLitsWf.getD {g : Aig} {litsPool : List (BitVec 32)} {off w j : Nat}
    (hwf : SliceLitsWf g litsPool off w) (hj : j < w) :
    ((litsPool.getD (off + j) 0#32) >>> 1).toNat < g.A + 1 + g.nodes.size :=
  hwf j hj

theorem SliceLitsWf.extend {g g' : Aig} {litsPool : List (BitVec 32)} {off w : Nat}
    (hext : g ≤ g') (hwf : SliceLitsWf g litsPool off w) :
    SliceLitsWf g' litsPool off w := by
  have hsz : g.A + 1 + g.nodes.size ≤ g'.A + 1 + g'.nodes.size := by
    have := hext.1; have := hext.2.1; omega
  exact fun j hj => Nat.lt_of_lt_of_le (hwf j hj) hsz

theorem SliceLitsWf.of_agree {g : Aig} {pool1 pool2 : List (BitVec 32)} {off1 off2 w : Nat}
    (hagree : ∀ j < w, pool2.getD (off2 + j) 0#32 = pool1.getD (off1 + j) 0#32)
    (hwf : SliceLitsWf g pool1 off1 w) :
    SliceLitsWf g pool2 off2 w := by
  intro j hj
  rw [hagree j hj]
  exact hwf j hj

theorem SliceLitsWf.of_prefix {g : Aig} {pool1 pool2 : List (BitVec 32)} {off w n : Nat}
    (hle : off + w ≤ n) (hagree : ∀ p < n, pool2.getD p 0#32 = pool1.getD p 0#32)
    (hwf : SliceLitsWf g pool1 off w) :
    SliceLitsWf g pool2 off w :=
  SliceLitsWf.of_agree (fun j hj => hagree (off + j) (by omega)) hwf

theorem SliceLitsWf.set_at {g : Aig} {pool : List (BitVec 32)} {off w k : Nat} {v : BitVec 32}
    (hk : k < pool.length) (hv : (v >>> 1).toNat < g.A + 1 + g.nodes.size)
    (hwf : SliceLitsWf g pool off w) :
    SliceLitsWf g (pool.set k v) off w := by
  intro j hj
  by_cases hkj : off + j = k
  · rw [hkj, List.getD_eq_getElem?_getD, List.getElem?_set_self hk, Option.getD_some]
    exact hv
  · have hget : (pool.set k v).getD (off + j) 0#32 = pool.getD (off + j) 0#32 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hkj)]
    rw [hget]
    exact hwf j hj

theorem evalPoolSlice_getLsbD {g : Aig} {ρ : Nat → Bool} {litsPool : List (BitVec 32)}
    {off w i : Nat} (hi : i < w) :
    (evalPoolSlice g ρ litsPool off w).getLsbD i =
      g.evalLit ρ (UInt32.ofBitVec (litsPool.getD (off + i) 0#32)) := by
  unfold evalPoolSlice
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]

theorem sliceDenotes_evalPoolSlice {g : Aig} {ρ : Nat → Bool} {litsPool : List (BitVec 32)}
    {off w : Nat} (hle : off + w ≤ litsPool.length) :
    SliceDenotes g ρ (litsSlice litsPool off w) (evalPoolSlice g ρ litsPool off w) := by
  refine ⟨litsSlice_length hle, fun j hj => ?_⟩
  rw [litsSlice_getD hle hj, evalPoolSlice_getLsbD hj]

theorem evalPoolSlice_eq_of_sliceDenotes {g : Aig} {ρ : Nat → Bool} {litsPool : List (BitVec 32)}
    {off w : Nat} {v : BitVec w} (hle : off + w ≤ litsPool.length)
    (hsd : SliceDenotes g ρ (litsSlice litsPool off w) v) :
    evalPoolSlice g ρ litsPool off w = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [evalPoolSlice_getLsbD hj, ← litsSlice_getD hle hj]
  exact hsd.2 j hj

theorem evalPoolSlice_extend {g g' : Aig} {ρ : Nat → Bool} {litsPool : List (BitVec 32)}
    {off w : Nat} (hext : g ≤ g') (hwf : SliceLitsWf g litsPool off w) :
    evalPoolSlice g' ρ litsPool off w = evalPoolSlice g ρ litsPool off w := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [evalPoolSlice_getLsbD hj, evalPoolSlice_getLsbD hj]
  apply Aig.evalLit_extend_node hext
  rw [ofBv_shr1_toNat]
  exact hwf j hj

theorem evalPoolSlice_of_agree {g : Aig} {ρ : Nat → Bool} {pool1 pool2 : List (BitVec 32)}
    {off1 off2 w : Nat}
    (hagree : ∀ j < w, pool2.getD (off2 + j) 0#32 = pool1.getD (off1 + j) 0#32) :
    evalPoolSlice g ρ pool2 off2 w = evalPoolSlice g ρ pool1 off1 w := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [evalPoolSlice_getLsbD hj, evalPoolSlice_getLsbD hj, hagree j hj]

/-! ## 3. Pure-Lits Semantic Bridge Lemmas (`replicate`, `rotl`, `rotr`, `ashrc`, `reverse`) -/

theorem SliceLitsWf_of_idxFn {g : Aig} {pool1 pool2 : List (BitVec 32)}
    {off1 off2 w1 w2 : Nat} {idxFn : Nat → Nat}
    (hbd : ∀ j < w2, off1 ≤ idxFn j ∧ idxFn j < off1 + w1)
    (heq : ∀ j < w2, pool2.getD (off2 + j) 0#32 = pool1.getD (idxFn j) 0#32)
    (hwf : SliceLitsWf g pool1 off1 w1) :
    SliceLitsWf g pool2 off2 w2 := by
  intro j hj
  rw [heq j hj]
  have ⟨h1, h2⟩ := hbd j hj
  have hk : idxFn j - off1 < w1 := by omega
  have hplus : off1 + (idxFn j - off1) = idxFn j := by omega
  simpa [hplus] using hwf (idxFn j - off1) hk

private theorem sliceDenotes_pure_bridge {g : Aig} {ρ : Nat → Bool}
    {pool1 pool2 : List (BitVec 32)} {off1 off2 w1 w2 : Nat}
    {va : BitVec w1} {vr : BitVec w2} {idxFn : Nat → Nat}
    (hle1 : off1 + w1 ≤ pool1.length) (hle2 : off2 + w2 ≤ pool2.length)
    (hsd : SliceDenotes g ρ (litsSlice pool1 off1 w1) va)
    (hpool : ∀ j < w2, pool2.getD (off2 + j) 0#32 = pool1.getD (idxFn j) 0#32)
    (hbd : ∀ j < w2, off1 ≤ idxFn j ∧ idxFn j < off1 + w1)
    (hbit : ∀ j < w2, va.getLsbD (idxFn j - off1) = vr.getLsbD j) :
    SliceDenotes g ρ (litsSlice pool2 off2 w2) vr := by
  refine ⟨litsSlice_length hle2, fun j hj => ?_⟩
  rw [litsSlice_getD hle2 hj, hpool j hj]
  have ⟨h1, h2⟩ := hbd j hj
  have hk : idxFn j - off1 < w1 := by omega
  have hplus : off1 + (idxFn j - off1) = idxFn j := by omega
  have hsd_k := hsd.2 (idxFn j - off1) hk
  rw [litsSlice_getD hle1 hk, hplus] at hsd_k
  rw [hsd_k, hbit j hj]

theorem sliceDenotes_replicate_of_pool {g : Aig} {ρ : Nat → Bool}
    {pool1 pool2 : List (BitVec 32)} {off1 off2 aw n : Nat} {va : BitVec aw}
    (hle1 : off1 + aw ≤ pool1.length) (hle2 : off2 + aw * n ≤ pool2.length)
    (hsd : SliceDenotes g ρ (litsSlice pool1 off1 aw) va)
    (hpool : ∀ j < aw * n, pool2.getD (off2 + j) 0#32 = pool1.getD (off1 + j % aw) 0#32) :
    SliceDenotes g ρ (litsSlice pool2 off2 (aw * n)) (BitVec.replicate n va) := by
  have haw : 0 < aw * n → 0 < aw := fun h => by
    rcases Nat.eq_zero_or_pos aw with h0 | hp
    · subst h0; simp at h
    · exact hp
  refine sliceDenotes_pure_bridge hle1 hle2 hsd hpool ?_ ?_
  · intro j hj
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (Nat.mod_lt _ (haw (by omega))) _⟩
  · intro j hj
    rw [BitVec.getLsbD_replicate, show off1 + j % aw - off1 = j % aw by omega,
      decide_eq_true hj, Bool.true_and]

theorem sliceDenotes_rotl_of_pool {g : Aig} {ρ : Nat → Bool}
    {pool1 pool2 : List (BitVec 32)} {off1 off2 w n : Nat} {va : BitVec w}
    (hle1 : off1 + w ≤ pool1.length) (hle2 : off2 + w ≤ pool2.length)
    (hsd : SliceDenotes g ρ (litsSlice pool1 off1 w) va)
    (hpool : ∀ j < w,
      pool2.getD (off2 + j) 0#32 =
        pool1.getD (off1 + (if j < n % w then w - n % w + j else j - n % w)) 0#32) :
    SliceDenotes g ρ (litsSlice pool2 off2 w) (va.rotateLeft n) := by
  refine sliceDenotes_pure_bridge hle1 hle2 hsd hpool ?_ ?_
  · intro j hj
    split <;> omega
  · intro j hj
    rw [BitVec.getLsbD_rotateLeft]
    split <;> simp [hj, Nat.add_sub_cancel_left]

theorem sliceDenotes_rotr_of_pool {g : Aig} {ρ : Nat → Bool}
    {pool1 pool2 : List (BitVec 32)} {off1 off2 w n : Nat} {va : BitVec w}
    (hle1 : off1 + w ≤ pool1.length) (hle2 : off2 + w ≤ pool2.length)
    (hsd : SliceDenotes g ρ (litsSlice pool1 off1 w) va)
    (hpool : ∀ j < w,
      pool2.getD (off2 + j) 0#32 =
        pool1.getD (off1 + (if j < w - n % w then n % w + j else j - (w - n % w))) 0#32) :
    SliceDenotes g ρ (litsSlice pool2 off2 w) (va.rotateRight n) := by
  refine sliceDenotes_pure_bridge hle1 hle2 hsd hpool ?_ ?_
  · intro j hj
    have hr : n % w < w := Nat.mod_lt _ (by omega)
    split <;> omega
  · intro j hj
    rw [BitVec.getLsbD_rotateRight]
    split <;> simp [hj, Nat.add_sub_cancel_left]

theorem sliceDenotes_ashrc_of_pool {g : Aig} {ρ : Nat → Bool}
    {pool1 pool2 : List (BitVec 32)} {off1 off2 w n : Nat} {va : BitVec w}
    (hle1 : off1 + w ≤ pool1.length) (hle2 : off2 + w ≤ pool2.length)
    (hsd : SliceDenotes g ρ (litsSlice pool1 off1 w) va)
    (hpool : ∀ j < w,
      pool2.getD (off2 + j) 0#32 =
        pool1.getD (off1 + (if n + j < w then n + j else w - 1)) 0#32) :
    SliceDenotes g ρ (litsSlice pool2 off2 w) (va.sshiftRight n) := by
  refine sliceDenotes_pure_bridge hle1 hle2 hsd hpool ?_ ?_
  · intro j hj
    split <;> omega
  · intro j hj
    rw [BitVec.getLsbD_sshiftRight, decide_eq_false (by omega), Bool.not_false, Bool.true_and,
      BitVec.msb_eq_getLsbD_last]
    split <;> simp

theorem sliceDenotes_reverse_of_pool {g : Aig} {ρ : Nat → Bool}
    {pool1 pool2 : List (BitVec 32)} {off1 off2 w : Nat} {va : BitVec w}
    (hle1 : off1 + w ≤ pool1.length) (hle2 : off2 + w ≤ pool2.length)
    (hsd : SliceDenotes g ρ (litsSlice pool1 off1 w) va)
    (hpool : ∀ j < w,
      pool2.getD (off2 + j) 0#32 = pool1.getD (off1 + (w - 1 - j)) 0#32) :
    SliceDenotes g ρ (litsSlice pool2 off2 w) va.reverse := by
  refine sliceDenotes_pure_bridge hle1 hle2 hsd hpool ?_ ?_
  · intro j hj; omega
  · intro j hj
    rw [BitVec.getLsbD_reverse, BitVec.getMsbD, decide_eq_true hj, Bool.true_and]
    simp

/-! ## 4. `sliceOkBool`, `anyOrBool`, Shift, Mul, and Clz Mathematical Lemmas -/

theorem sliceOkBool_true_iff (hdr : BVHdrState) (off w : BitVec 32) :
    sliceOkBool hdr off w = true ↔
      hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
      (0 < w.toNat → hdr.lits_ptr ≠ 0#64) ∧
      off.toNat ≤ hdr.lits_len.toNat ∧
      w.toNat ≤ hdr.lits_len.toNat - off.toNat := by
  unfold sliceOkBool
  rw [decide_eq_true_eq]

theorem sliceOkBool_mono_lits_len {hdr hdr' : BVHdrState} {off w : BitVec 32}
    (hptr : hdr'.lits_ptr = hdr.lits_ptr)
    (hle1 : hdr.lits_len.toNat ≤ hdr'.lits_len.toNat)
    (hle2 : hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat)
    (hok : sliceOkBool hdr off w = true) :
    sliceOkBool hdr' off w = true := by
  rw [sliceOkBool_true_iff] at hok ⊢
  refine ⟨hle2, fun hw => hptr ▸ hok.2.1 hw, by omega, by omega⟩

theorem anyOrBool_le (p : Nat → Bool) {lo hi : Nat} (hle : hi ≤ lo) :
    anyOrBool p lo hi = false := by
  cases hi with
  | zero => rfl
  | succ k =>
    have hnot : ¬ lo ≤ k := by omega
    simp [anyOrBool, hnot]

theorem anyOrBool_step_hi (p : Nat → Bool) {lo hi : Nat} (hle : lo ≤ hi) :
    anyOrBool p lo (hi + 1) = (anyOrBool p lo hi || p hi) := by
  simp [anyOrBool, hle]

theorem anyOrBool_eq_true_iff (p : Nat → Bool) (lo hi : Nat) :
    anyOrBool p lo hi = true ↔ ∃ i, lo ≤ i ∧ i < hi ∧ p i = true := by
  induction hi with
  | zero => simp [anyOrBool]
  | succ k ih =>
    by_cases hle : lo ≤ k
    · rw [anyOrBool_step_hi p hle, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨i, h1, h2, hp⟩ | hp)
        · exact ⟨i, h1, by omega, hp⟩
        · exact ⟨k, hle, by omega, hp⟩
      · rintro ⟨i, h1, h2, hp⟩
        by_cases hik : i = k
        · exact Or.inr (hik ▸ hp)
        · exact Or.inl ⟨i, h1, by omega, hp⟩
    · have hk : k + 1 ≤ lo := by omega
      rw [anyOrBool_le p hk]
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨i, h1, h2, _⟩
      omega

theorem anyOrBool_mono (p : Nat → Bool) {lo hi hi' : Nat}
    (hle : hi ≤ hi') (h : anyOrBool p lo hi = true) :
    anyOrBool p lo hi' = true := by
  rw [anyOrBool_eq_true_iff] at h ⊢
  obtain ⟨i, h1, h2, hp⟩ := h
  exact ⟨i, h1, by omega, hp⟩

theorem bvShiftSem_shl {w nw : Nat} (va : BitVec w) (vb : BitVec nw) :
    bvShiftSem 19#32 va vb = va <<< vb := rfl

theorem bvShiftSem_ushr {w nw : Nat} (va : BitVec w) (vb : BitVec nw) :
    bvShiftSem 20#32 va vb = va >>> vb := rfl

theorem bvShiftSem_ashr {w nw : Nat} (va : BitVec w) (vb : BitVec nw) :
    bvShiftSem 21#32 va vb = va.sshiftRight' vb := rfl

private theorem ushiftRight_add_nat {w : Nat} (x : BitVec w) (m n : Nat) :
    x >>> (m + n) = (x >>> m) >>> n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_ushiftRight, Nat.add_assoc]

theorem bvShiftCur_zero {w nw : Nat} (op : BitVec 32) (va : BitVec w) (vb : BitVec nw) :
    bvShiftCur op va vb 0 = va := by
  unfold bvShiftCur bvShiftSem
  have hzero : BitVec.ofNat nw (vb.toNat % 2 ^ 0) = 0#nw := by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.pow_zero, Nat.mod_one]
  rw [hzero]
  split
  · rw [BitVec.shiftLeft_eq']; simp
  · split
    · rw [BitVec.ushiftRight_eq']; simp
    · change va.sshiftRight (0#nw).toNat = va; simp

private theorem nat_testBit_iff (n p : Nat) :
    n.testBit p = true ↔ n / 2 ^ p % 2 = 1 := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm 1, Nat.and_one_is_mod, bne_iff_ne,
    ne_eq]
  have hlt : n / 2 ^ p % 2 < 2 := Nat.mod_lt _ (by decide)
  omega

private theorem nat_exists_testBit : ∀ (k n : Nat), 0 < n → n < 2 ^ k → ∃ i < k, n.testBit i = true
  | 0, _, hn, hk => by simp at hk; omega
  | k + 1, n, hn, hk => by
    by_cases h0 : n % 2 = 1
    · refine ⟨0, Nat.succ_pos k, ?_⟩
      rw [nat_testBit_iff, Nat.pow_zero, Nat.div_one]
      exact h0
    · have hdiv_lt : n / 2 < 2 ^ k := by
        rw [Nat.div_lt_iff_lt_mul (by decide), ← Nat.pow_succ]
        exact hk
      obtain ⟨i, hi, htb⟩ := nat_exists_testBit k (n / 2) (by omega) hdiv_lt
      have htb' : (n / 2 ^ 1).testBit i = true := htb
      rw [Nat.testBit_div_two_pow (n := 1)] at htb'
      exact ⟨i + 1, Nat.succ_lt_succ hi, htb'⟩

private theorem testBit_mod_two_pow_succ (n p : Nat) :
    n % 2 ^ (p + 1) = n % 2 ^ p + if n.testBit p then 2 ^ p else 0 := by
  have h := Nat.div_add_mod (n % 2 ^ (p + 1)) (2 ^ p)
  have hmod : (n % 2 ^ (p + 1)) % 2 ^ p = n % 2 ^ p :=
    Nat.mod_mod_of_dvd n (by rw [Nat.pow_succ]; exact Nat.dvd_mul_right _ _)
  have hdiv2 : n % 2 ^ (p + 1) / 2 ^ p = n / 2 ^ p % 2 := by
    have hq : n = n % 2 ^ (p + 1) + 2 ^ p * (2 * (n / 2 ^ (p + 1))) := by
      have h0 := (Nat.mod_add_div n (2 ^ (p + 1))).symm
      rw [Nat.pow_succ, Nat.mul_assoc] at h0
      exact h0
    have h1 : n / 2 ^ p = n % 2 ^ (p + 1) / 2 ^ p + 2 * (n / 2 ^ (p + 1)) := by
      conv => lhs; rw [hq, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide : 0 < 2))]
    have hlt : n % 2 ^ (p + 1) / 2 ^ p < 2 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2)), ← Nat.pow_succ']
      exact Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2))
    rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  cases htb : n.testBit p
  · have hmod2 : n / 2 ^ p % 2 ≠ 1 := fun h1 => by
      have ht := (nat_testBit_iff n p).mpr h1
      rw [ht] at htb; cases htb
    have hdiv0 : n % 2 ^ (p + 1) / 2 ^ p = 0 := by
      have hlt : n / 2 ^ p % 2 < 2 := Nat.mod_lt _ (by decide)
      rw [hdiv2]; omega
    rw [hmod, hdiv0] at h
    simp; omega
  · have hmod2 : n / 2 ^ p % 2 = 1 := (nat_testBit_iff n p).mp htb
    have hdiv1 : n % 2 ^ (p + 1) / 2 ^ p = 1 := by rw [hdiv2]; omega
    rw [hmod, hdiv1] at h
    simp; omega

theorem bvShiftCur_step_getLsbD {w nw p j : Nat} {op : BitVec 32} (va : BitVec w) (vb : BitVec nw)
    (hop : op = 19#32 ∨ op = 20#32 ∨ op = 21#32)
    (hp : p < nw) (h2p : 2 ^ p < w) (hj : j < w) :
    (bvShiftCur op va vb (p + 1)).getLsbD j =
      if vb.getLsbD p then
        if op = 19#32 then
          if 2 ^ p ≤ j then (bvShiftCur op va vb p).getLsbD (j - 2 ^ p) else false
        else if op = 20#32 then
          if j < w - 2 ^ p then (bvShiftCur op va vb p).getLsbD (j + 2 ^ p) else false
        else
          if j < w - 2 ^ p then (bvShiftCur op va vb p).getLsbD (j + 2 ^ p)
          else (bvShiftCur op va vb p).getLsbD (w - 1)
      else
        (bvShiftCur op va vb p).getLsbD j := by
  have hm_lt : vb.toNat % 2 ^ p + 2 ^ p < 2 ^ nw := by
    have hp1 : 2 ^ (p + 1) ≤ 2 ^ nw := Nat.pow_le_pow_right (by decide) hp
    have h1 : vb.toNat % 2 ^ p < 2 ^ p := Nat.mod_lt _ (Nat.pow_pos (by decide))
    rw [Nat.pow_succ'] at hp1
    omega
  have hm0_lt : vb.toNat % 2 ^ p < 2 ^ nw := by omega
  have hbit : vb.getLsbD p = vb.toNat.testBit p := by
    rw [BitVec.getLsbD_eq_getElem hp, BitVec.getElem_eq_testBit_toNat]
  have hsplit := testBit_mod_two_pow_succ vb.toNat p
  rw [← hbit] at hsplit
  cases htb : vb.getLsbD p
  · simp only [bvShiftCur, hsplit, htb, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  · simp only [bvShiftCur, hsplit, htb, ↓reduceIte]
    unfold bvShiftSem
    have hto1 : (BitVec.ofNat nw (vb.toNat % 2 ^ p + 2 ^ p)).toNat =
        vb.toNat % 2 ^ p + 2 ^ p := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm_lt]
    have hto0 : (BitVec.ofNat nw (vb.toNat % 2 ^ p)).toNat = vb.toNat % 2 ^ p := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm0_lt]
    rcases hop with rfl | rfl | rfl
    · rw [ite_eq_left rfl, ite_eq_left rfl]
      change (va <<< (BitVec.ofNat nw (vb.toNat % 2 ^ p + 2 ^ p)).toNat).getLsbD j = _
      change _ = if 2 ^ p ≤ j then
          (va <<< (BitVec.ofNat nw (vb.toNat % 2 ^ p)).toNat).getLsbD (j - 2 ^ p)
        else false
      rw [hto1, hto0, BitVec.shiftLeft_add, BitVec.getLsbD_shiftLeft, decide_eq_true hj,
        Bool.true_and]
      by_cases hge : 2 ^ p ≤ j
      · simp [hge]
      · simp [hge, Nat.lt_of_not_le hge]
    · rw [ite_eq_right (by decide), ite_eq_left rfl, ite_eq_right (by decide), ite_eq_left rfl]
      change (va >>> (BitVec.ofNat nw (vb.toNat % 2 ^ p + 2 ^ p)).toNat).getLsbD j = _
      change _ = if j < w - 2 ^ p then
          (va >>> (BitVec.ofNat nw (vb.toNat % 2 ^ p)).toNat).getLsbD (j + 2 ^ p)
        else false
      rw [hto1, hto0, ushiftRight_add_nat, BitVec.getLsbD_ushiftRight, Nat.add_comm j (2 ^ p)]
      by_cases hlt : j < w - 2 ^ p
      · simp [hlt]
      · have hge : w ≤ vb.toNat % 2 ^ p + (2 ^ p + j) := by omega
        simp [hlt, BitVec.getLsbD_of_ge _ _ hge]
    · rw [ite_eq_right (by decide), ite_eq_right (by decide),
        ite_eq_right (by decide), ite_eq_right (by decide)]
      change (va.sshiftRight (BitVec.ofNat nw (vb.toNat % 2 ^ p + 2 ^ p)).toNat).getLsbD j = _
      change _ = if j < w - 2 ^ p then
          (va.sshiftRight (BitVec.ofNat nw (vb.toNat % 2 ^ p)).toNat).getLsbD (j + 2 ^ p)
        else (va.sshiftRight (BitVec.ofNat nw (vb.toNat % 2 ^ p)).toNat).getLsbD (w - 1)
      rw [hto1, hto0, BitVec.sshiftRight_add, BitVec.getLsbD_sshiftRight,
        decide_eq_false (by omega), Bool.not_false, Bool.true_and, BitVec.msb_sshiftRight]
      by_cases hlt : j < w - 2 ^ p
      · rw [ite_eq_left hlt, ite_eq_left (by omega), Nat.add_comm (2 ^ p) j]
      · rw [ite_eq_right hlt, ite_eq_right (by omega), BitVec.getLsbD_sshiftRight,
          decide_eq_false (by omega), Bool.not_false, Bool.true_and]
        split
        · have hzero : vb.toNat % 2 ^ p = 0 := by omega
          rw [hzero, Nat.zero_add, ← BitVec.msb_eq_getLsbD_last]
        · rfl

theorem bvShiftCur_eq_sem_of_no_hi {w nw pow : Nat} {op : BitVec 32} (va : BitVec w)
    (vb : BitVec nw) (hle : pow ≤ nw)
    (hno : anyOrBool (fun i => vb.getLsbD i) pow nw = false) :
    bvShiftCur op va vb pow = bvShiftSem op va vb := by
  have hmod : vb.toNat % 2 ^ pow = vb.toNat := by
    apply Nat.mod_eq_of_lt
    rcases Nat.lt_or_ge vb.toNat (2 ^ pow) with hlt | hge'
    · exact hlt
    · have hex : ∃ i, pow ≤ i ∧ i < nw ∧ vb.getLsbD i = true := by
        have hdiv : 0 < vb.toNat / 2 ^ pow := Nat.div_pos hge' (Nat.pow_pos (by decide))
        have hlt : vb.toNat / 2 ^ pow < 2 ^ (nw - pow) := by
          rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), ← Nat.pow_add,
            Nat.sub_add_cancel hle]
          exact vb.isLt
        obtain ⟨k, hk_lt, hk⟩ := nat_exists_testBit (nw - pow) (vb.toNat / 2 ^ pow) hdiv hlt
        refine ⟨pow + k, by omega, by omega, ?_⟩
        rw [BitVec.getLsbD_eq_getElem (by omega), BitVec.getElem_eq_testBit_toNat,
          Nat.add_comm pow k, Nat.testBit_add]
        exact hk
      have ht : anyOrBool (fun i => vb.getLsbD i) pow nw = true :=
        (anyOrBool_eq_true_iff _ pow nw).mpr hex
      rw [ht] at hno
      cases hno
  unfold bvShiftCur
  rw [hmod]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp

theorem bvShiftCur_sat_of_hi {w nw pow j : Nat} {op : BitVec 32} (va : BitVec w)
    (vb : BitVec nw) (hop : op = 19#32 ∨ op = 20#32 ∨ op = 21#32)
    (hw : 0 < w) (hpw : w ≤ 2 ^ pow)
    (hhi : anyOrBool (fun i => vb.getLsbD i) pow nw = true) (hj : j < w) :
    (bvShiftSem op va vb).getLsbD j =
      (if op = 21#32 then (bvShiftCur op va vb pow).getLsbD (w - 1) else false) := by
  obtain ⟨i, hi_ge, hi_lt, hbit⟩ := (anyOrBool_eq_true_iff _ pow nw).mp hhi
  have hge_pow : 2 ^ pow ≤ vb.toNat := by
    have h2 : 2 ^ i ≤ vb.toNat := by
      rw [BitVec.getLsbD_eq_getElem hi_lt, BitVec.getElem_eq_testBit_toNat] at hbit
      exact Nat.ge_two_pow_of_testBit hbit
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) hi_ge) h2
  have hge_w : w ≤ vb.toNat := Nat.le_trans hpw hge_pow
  rcases hop with rfl | rfl | rfl
  · rw [bvShiftSem, ite_eq_left rfl, ite_eq_right (by decide)]
    change (va <<< vb.toNat).getLsbD j = false
    have hnd : decide (j < vb.toNat) = true := decide_eq_true (Nat.lt_of_lt_of_le hj hge_w)
    rw [BitVec.getLsbD_shiftLeft, hnd]
    simp
  · rw [bvShiftSem, ite_eq_right (by decide), ite_eq_left rfl, ite_eq_right (by decide)]
    change (va >>> vb.toNat).getLsbD j = false
    rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_of_ge _ _ (by omega)]
  · rw [bvShiftSem, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
    change (va.sshiftRight vb.toNat).getLsbD j =
      (bvShiftCur 21#32 va vb pow).getLsbD (w - 1)
    rw [BitVec.getLsbD_sshiftRight, decide_eq_false (by omega), Bool.not_false, Bool.true_and,
      ite_eq_right (by omega), bvShiftCur, bvShiftSem, ite_eq_right (by decide),
      ite_eq_right (by decide)]
    change _ = (va.sshiftRight (BitVec.ofNat nw (vb.toNat % 2 ^ pow)).toNat).getLsbD (w - 1)
    rw [BitVec.getLsbD_sshiftRight, decide_eq_false (by omega), Bool.not_false, Bool.true_and]
    split
    · have hzero : (BitVec.ofNat nw (vb.toNat % 2 ^ pow)).toNat = 0 := by omega
      rw [hzero, Nat.zero_add, ← BitVec.msb_eq_getLsbD_last]
    · rfl

theorem evalPoolSlice_shifted {g : Aig} {ρ : Nat → Bool} {pool0 pool1 : List (BitVec 32)}
    {aOff shiftedOff w s : Nat} (_hs : s < w)
    (h0 : ∀ j < s, pool1.getD (shiftedOff + j) 0#32 = 0#32)
    (h1 : ∀ j, s ≤ j → j < w →
      pool1.getD (shiftedOff + j) 0#32 = pool0.getD (aOff + (j - s)) 0#32) :
    evalPoolSlice g ρ pool1 shiftedOff w = (evalPoolSlice g ρ pool0 aOff w) <<< s := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [evalPoolSlice_getLsbD hj, BitVec.getLsbD_shiftLeft, decide_eq_true hj, Bool.true_and]
  by_cases hjs : j < s
  · rw [h0 j hjs, evalLit_ofBv_zero, decide_eq_true hjs]; simp
  · have hge : s ≤ j := Nat.le_of_not_lt hjs
    rw [h1 j hge hj, evalPoolSlice_getLsbD (by omega), decide_eq_false hjs]
    simp

theorem mulRec_zero_getLsbD {w j : Nat} (va vb : BitVec w) (_hj : j < w) :
    (va.mulRec vb 0).getLsbD j = (vb.getLsbD 0 && va.getLsbD j) := by
  rw [BitVec.mulRec_zero_eq]
  cases h0 : vb.getLsbD 0
  · simp [BitVec.getLsbD_zero]
  · simp

theorem mul_eq_mulRec_last {w : Nat} (va vb : BitVec w) (hw : 0 < w) :
    va * vb = va.mulRec vb (w - 1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_mul]
  have hw1 : w = (w - 1) + 1 := by omega
  have hrec : va.mulRec vb w = va.mulRec vb ((w - 1) + 1) := congrArg (va.mulRec vb) hw1
  rw [hrec, BitVec.mulRec_succ_eq]
  have hge : vb.getLsbD ((w - 1) + 1) = false := BitVec.getLsbD_of_ge vb _ (by omega)
  simp [hge]

theorem evalLit_bitSelect {g : Aig} {ρ : Nat → Bool} {v w j : BitVec 32}
    (hj : j.toNat < w.toNat) :
    g.evalLit ρ (UInt32.ofBitVec (if j < 32#32 then (v >>> j) &&& 1#32 else 0#32)) =
      (BitVec.ofNat w.toNat v.toNat).getLsbD j.toNat := by
  by_cases hj32 : j < 32#32
  · have hbit : ((v >>> j) &&& 1#32) =
        if v.toNat.testBit j.toNat then 1#32 else 0#32 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow, show (1#32 : BitVec 32).toNat = 1 from rfl,
        Nat.and_one_is_mod]
      by_cases h1 : v.toNat / 2 ^ j.toNat % 2 = 1
      · have htb := (nat_testBit_iff v.toNat j.toNat).mpr h1
        simp [h1, htb]
      · have hlt2 : v.toNat / 2 ^ j.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
        have h0 : v.toNat / 2 ^ j.toNat % 2 = 0 := by omega
        have htb : v.toNat.testBit j.toNat = false :=
          Bool.eq_false_iff.mpr fun ht => h1 ((nat_testBit_iff v.toNat j.toNat).mp ht)
        simp [h0, htb]
    rw [ite_eq_left hj32, hbit, BitVec.getLsbD_ofNat, decide_eq_true hj, Bool.true_and]
    cases v.toNat.testBit j.toNat
    · exact evalLit_ofBv_zero g ρ
    · exact evalLit_ofBv_one g ρ
  · have hj32n : 32 ≤ j.toNat := by
      rw [BitVec.lt_def] at hj32; simp only [BitVec.toNat_ofNat] at hj32; omega
    have hlt2 : v.toNat < 2 ^ j.toNat :=
      Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by decide) hj32n)
    rw [ite_eq_right hj32, BitVec.getLsbD_ofNat, decide_eq_true hj, Bool.true_and,
      Nat.testBit_lt_two_pow hlt2]
    exact evalLit_ofBv_zero g ρ

private theorem clzAux_eq_clzAuxRec {w : Nat} (va : BitVec w) :
    ∀ k, clzAux va (k + 1) = va.clzAuxRec k
  | 0 => by rw [BitVec.clzAuxRec_zero, clzAux, clzAux]; simp
  | k + 1 => by rw [BitVec.clzAuxRec_succ, clzAux, clzAux_eq_clzAuxRec va k]

theorem clzAux_final {w : Nat} (va : BitVec w) (hw : 0 < w) :
    clzAux va w = va.clz := by
  rw [BitVec.clz_eq_clzAuxRec]
  have hw1 : w = (w - 1) + 1 := by omega
  have hclz : clzAux va w = clzAux va ((w - 1) + 1) := congrArg (clzAux va) hw1
  rw [hclz, clzAux_eq_clzAuxRec]

/-! ## 5. Separation-Logic Focus & C0 Call Step Helpers -/

theorem ops_lits_only_focus {h : BitVec 64} {hdr : BVHdrState}
    {aigWords : List (BitVec 64)} {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop}
    {m : Mem 64}
    (hm : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m) :
    (bvHdrMem h hdr ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆
      (array64 hdr.aig_ptr aigWords ⋆ array (t := i32) hdr.ht_ptr htSlots ⋆ R)) m :=
  sep_ac hm

theorem ops_aig_frame_unfocus {h : BitVec 64} {hdr hdr' : BVHdrState}
    {aigWords' : List (BitVec 64)} {htSlots' litsPool : List (BitVec 32)} {R : Mem 64 → Prop}
    {m' : Mem 64} (hfr : hdr.OpsFrame hdr')
    (hm' : (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
      array (t := i32) hdr'.ht_ptr htSlots' ⋆
      (array (t := i32) hdr.lits_ptr litsPool ⋆ R)) m') :
    (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
      array (t := i32) hdr'.ht_ptr htSlots' ⋆
      array (t := i32) hdr'.lits_ptr litsPool ⋆ R) m' := by
  rw [hfr.lits_ptr]
  exact sep_ac hm'

theorem ops_hdr_unfocus_aig {h : BitVec 64} {hdr hdr' : BVHdrState}
    {aigWords : List (BitVec 64)} {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop}
    {m' : Mem 64} (hfr : hdr.OpsFrame hdr')
    (hm' : (bvHdrMem h hdr' ⋆ (array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R)) m') :
    (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords ⋆
      array (t := i32) hdr'.ht_ptr htSlots ⋆
      array (t := i32) hdr'.lits_ptr litsPool ⋆ R) m' := by
  rw [hfr.aig_ptr, hfr.ht_ptr, hfr.lits_ptr]
  exact sep_ac hm'

theorem ops_hdr_unfocus_lits {h : BitVec 64} {hdr hdr' : BVHdrState}
    {litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m' : Mem 64} (hfr : hdr.OpsFrame hdr')
    (hm' : (bvHdrMem h hdr' ⋆ (array (t := i32) hdr.lits_ptr litsPool ⋆ R)) m') :
    (bvHdrMem h hdr' ⋆ array (t := i32) hdr'.lits_ptr litsPool ⋆ R) m' := by
  rw [hfr.lits_ptr]
  exact sep_ac hm'

theorem call_bv_slice_ok {Γ : Env} (hSlice : Γ.Has "bv_slice_ok" smBvSliceOkSpec)
    {h : BitVec 64} {off w : BitVec 32} {hdr : BVHdrState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hm : (bvHdrMem h hdr ⋆ R) m)
    (hQ : Q (sliceOkBool hdr off w, ⟨⟩) m) :
    Γ "bv_slice_ok" [i64, i32, i32] [.bool] (h, off, w, ⟨⟩) m Q X :=
  hSlice (h, off, w, ⟨⟩) m Q X ⟨hdr, R, hm, hQ⟩

theorem call_bv_lits_mark {Γ : Env} (hMark : Γ.Has "bv_lits_mark" bvLitsMarkSpec)
    {h : BitVec 64} {hdr : BVHdrState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hm : (bvHdrMem h hdr ⋆ R) m)
    (hQ : Q (hdr.lits_len, ⟨⟩) m) :
    Γ "bv_lits_mark" [i64] [i32] (h, ⟨⟩) m Q X :=
  hMark (h, ⟨⟩) m Q X ⟨hdr, R, hm, hQ⟩

theorem call_bv_lits_release_le {Γ : Env} (hRel : Γ.Has "bv_lits_release" bvLitsReleaseSpec)
    {h : BitVec 64} {mark : BitVec 32} {hdr : BVHdrState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post []} {X : XPost}
    (hle : mark.toNat ≤ hdr.lits_len.toNat) (hm : (bvHdrMem h hdr ⋆ R) m)
    (hQ : ∀ m', (bvHdrMem h { hdr with lits_len := mark } ⋆ R) m' → Q ⟨⟩ m') :
    Γ "bv_lits_release" [i64, i32] [] (h, mark, ⟨⟩) m Q X := by
  refine hRel (h, mark, ⟨⟩) m Q X ⟨hdr, R, hm, ?_⟩
  simp only [hle, ↓reduceIte]
  exact hQ

theorem call_bv_lits_alloc {Γ : Env} (hAlloc : Γ.Has "bv_lits_alloc" bvLitsAllocSpec)
    {h : BitVec 64} {count : BitVec 32} {hdr : BVHdrState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hm : (bvHdrMem h hdr ⋆ R) m)
    (hok : hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
      count.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat →
      ∀ m', (bvHdrMem h { hdr with lits_len := hdr.lits_len + count } ⋆ R) m' →
        Q (hdr.lits_len, ⟨⟩) m')
    (hfail : ¬ (hdr.oom = 0#32 ∧ hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
        count.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat) →
      ∀ m', (bvHdrMem h { hdr with oom := if hdr.oom ≠ 0#32 then hdr.oom else 1#32 } ⋆ R) m' →
        Q (0xFFFFFFFF#32, ⟨⟩) m') :
    Γ "bv_lits_alloc" [i64, i32] [i32] (h, count, ⟨⟩) m Q X := by
  refine hAlloc (h, count, ⟨⟩) m Q X ⟨hdr, R, hm, ?_⟩
  split
  · next hcond => exact hok hcond.1 hcond.2.1 hcond.2.2
  · next hcond => exact hfail hcond

theorem call_bv_mk_and {Γ : Env} (hAnd : Γ.Has "bv_mk_and" bvMkAndSpec)
    {h : BitVec 64} {lhs rhs : BitVec 32} {hdr : BVHdrState} {g : Aig}
    {aigWords : List (BitVec 64)} {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (haig : AigInv hdr g aigWords htSlots)
    (hbd : hdr.oom = 0#32 →
      (lhs >>> 1).toNat < hdr.aig_len.toNat ∧ (rhs >>> 1).toNat < hdr.aig_len.toNat)
    (hm : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig)
      (aigWords' : List (BitVec 64)) (htSlots' : List (BitVec 32)) (m' : Mem 64),
      hdr.OpsFrame hdr' → hdr'.lits_len = hdr.lits_len → g ≤ g' →
      AigInv hdr' g' aigWords' htSlots' →
      (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
      (hdr'.oom = 0#32 →
        (ret >>> 1).toNat < hdr'.aig_len.toNat ∧
        ∀ ρ : Nat → Bool,
          g'.evalLit ρ (UInt32.ofBitVec ret) =
            (g.evalLit ρ (UInt32.ofBitVec lhs) && g.evalLit ρ (UInt32.ofBitVec rhs))) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆
        array (t := i32) hdr'.lits_ptr litsPool ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    Γ "bv_mk_and" [i64, i32, i32] [i32] (h, lhs, rhs, ⟨⟩) m Q X := by
  refine hAnd (h, lhs, rhs, ⟨⟩) m Q X ⟨hdr, g, aigWords, htSlots,
    array (t := i32) hdr.lits_ptr litsPool ⋆ R, haig, hbd, sep_ac hm,
    fun ret hdr' g' aw' ht' m' hfr hext _ haig' hoom _ heval hm' => ?_⟩
  exact hQ ret hdr' g' aw' ht' m' hfr.mono hfr.lits_len hext haig' hoom heval
    (ops_aig_frame_unfocus hfr.mono hm')

theorem call_bv_aig_or {Γ : Env} (hOr : Γ.Has "bv_aig_or" bvAigOrSpec)
    {h : BitVec 64} {lhs rhs : BitVec 32} {hdr : BVHdrState} {g : Aig}
    {aigWords : List (BitVec 64)} {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (haig : AigInv hdr g aigWords htSlots)
    (hbd : hdr.oom = 0#32 →
      (lhs >>> 1).toNat < hdr.aig_len.toNat ∧ (rhs >>> 1).toNat < hdr.aig_len.toNat)
    (hm : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig)
      (aigWords' : List (BitVec 64)) (htSlots' : List (BitVec 32)) (m' : Mem 64),
      hdr.OpsFrame hdr' → hdr'.lits_len = hdr.lits_len → g ≤ g' →
      AigInv hdr' g' aigWords' htSlots' →
      (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
      (hdr'.oom = 0#32 →
        (ret >>> 1).toNat < hdr'.aig_len.toNat ∧
        ∀ ρ : Nat → Bool,
          g'.evalLit ρ (UInt32.ofBitVec ret) =
            (g.evalLit ρ (UInt32.ofBitVec lhs) || g.evalLit ρ (UInt32.ofBitVec rhs))) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆
        array (t := i32) hdr'.lits_ptr litsPool ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    Γ "bv_aig_or" [i64, i32, i32] [i32] (h, lhs, rhs, ⟨⟩) m Q X := by
  refine hOr (h, lhs, rhs, ⟨⟩) m Q X ⟨hdr, g, aigWords, htSlots,
    array (t := i32) hdr.lits_ptr litsPool ⋆ R, haig, hbd, sep_ac hm,
    fun ret hdr' g' aw' ht' m' hfr hext _ haig' hoom _ heval hm' => ?_⟩
  exact hQ ret hdr' g' aw' ht' m' hfr.mono hfr.lits_len hext haig' hoom heval
    (ops_aig_frame_unfocus hfr.mono hm')

theorem call_bv_aig_ite {Γ : Env} (hIte : Γ.Has "bv_aig_ite" bvAigIteSpec)
    {h : BitVec 64} {c t f : BitVec 32} {hdr : BVHdrState} {g : Aig}
    {aigWords : List (BitVec 64)} {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (haig : AigInv hdr g aigWords htSlots)
    (hbd : hdr.oom = 0#32 →
      (c >>> 1).toNat < hdr.aig_len.toNat ∧
      (t >>> 1).toNat < hdr.aig_len.toNat ∧
      (f >>> 1).toNat < hdr.aig_len.toNat)
    (hm : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig)
      (aigWords' : List (BitVec 64)) (htSlots' : List (BitVec 32)) (m' : Mem 64),
      hdr.OpsFrame hdr' → hdr'.lits_len = hdr.lits_len → g ≤ g' →
      AigInv hdr' g' aigWords' htSlots' →
      (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
      (hdr'.oom = 0#32 →
        (ret >>> 1).toNat < hdr'.aig_len.toNat ∧
        ∀ ρ : Nat → Bool,
          g'.evalLit ρ (UInt32.ofBitVec ret) =
            cond (g.evalLit ρ (UInt32.ofBitVec c))
              (g.evalLit ρ (UInt32.ofBitVec t))
              (g.evalLit ρ (UInt32.ofBitVec f))) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆
        array (t := i32) hdr'.lits_ptr litsPool ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    Γ "bv_aig_ite" [i64, i32, i32, i32] [i32] (h, c, t, f, ⟨⟩) m Q X := by
  refine hIte (h, c, t, f, ⟨⟩) m Q X ⟨hdr, g, aigWords, htSlots,
    array (t := i32) hdr.lits_ptr litsPool ⋆ R, haig, hbd, sep_ac hm,
    fun ret hdr' g' aw' ht' m' hfr hext _ haig' hoom _ heval hm' => ?_⟩
  exact hQ ret hdr' g' aw' ht' m' hfr.mono hfr.lits_len hext haig' hoom heval
    (ops_aig_frame_unfocus hfr.mono hm')

theorem call_bv_copy_lits {Γ : Env} (hCopy : Γ.Has "bv_copy_lits" bvCopyLitsSpec)
    {h : BitVec 64} {dstOff srcOff w : BitVec 32} {hdr : BVHdrState}
    {litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hlt : litsPool.length < 2 ^ 32)
    (hdst : dstOff.toNat + w.toNat ≤ litsPool.length)
    (hsrc : srcOff.toNat + w.toNat ≤ litsPool.length)
    (hdisj : dstOff.toNat + w.toNat ≤ srcOff.toNat ∨ srcOff.toNat + w.toNat ≤ dstOff.toNat)
    (hm : (bvHdrMem h hdr ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m)
    (hQ : ∀ (litsPool' : List (BitVec 32)) (m' : Mem 64),
      litsPool'.length = litsPool.length →
      (∀ p, p < dstOff.toNat ∨ dstOff.toNat + w.toNat ≤ p →
        litsPool'.getD p 0#32 = litsPool.getD p 0#32) →
      (∀ j < w.toNat,
        litsPool'.getD (dstOff.toNat + j) 0#32 = litsPool.getD (srcOff.toNat + j) 0#32) →
      (bvHdrMem h hdr ⋆ array (t := i32) hdr.lits_ptr litsPool' ⋆ R) m' →
      Q ⟨⟩ m') :
    Γ "bv_copy_lits" [i64, i32, i32, i32] [] (h, dstOff, srcOff, w, ⟨⟩) m Q X :=
  hCopy (h, dstOff, srcOff, w, ⟨⟩) m Q X ⟨hdr, litsPool, R, hlt, hdst, hsrc, hdisj, hm, hQ⟩

theorem ops_lits_pure_guard_oom (hdr : BVHdrState) :
    { hdr with oom := 1#32 }.aig_len = hdr.aig_len ∧
    { hdr with oom := 1#32 }.lits_len = hdr.lits_len ∧
    { hdr with oom := 1#32 }.oom = 1#32 ∧
    hdr.OpsFrame { hdr with oom := 1#32 } :=
  ⟨rfl, rfl, rfl, Modifies.set_oom _ hdr 1#32⟩

theorem ops_lits_alloc_ok_frame (hdr : BVHdrState) (cnt : BitVec 32) :
    hdr.OpsFrame { hdr with lits_len := hdr.lits_len + cnt } :=
  Modifies.set_lits_len _ hdr _

end

end LeanQbe.T.Examples.Bitblast.Proof
