module

public import LeanQbe.T.Examples.Bitblast.Proof.Specs
public import LeanQbe.T.Examples.Bitblast.Proof.DriverHelpers
public import LeanQbe.T.Examples.Bitblast.Src.OpsDivCpop
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Src.OpsDivCpop

@[expose] public section

/-- Header frame preserved by bitblast ops that may allocate literals, gates, or set `oom`. -/
abbrev BVHdrState.DcBlastFrame (h1 h2 : BVHdrState) : Prop :=
  Modifies [.aig_len, .lits_len, .oom] h1 h2

end

namespace OpsDivCpop

@[expose] public section

/-- All literals in `litsPool[off ..< off + w]` lie within `hdr.lits_len` and `hdr.aig_len`. -/
def SliceLitsWf (hdr : BVHdrState) (litsPool : List (BitVec 32)) (off w : Nat) : Prop :=
  off + w ≤ hdr.lits_len.toNat ∧
    ∀ j, j < w → ((litsPool.getD (off + j) 0#32) >>> 1).toNat < hdr.aig_len.toNat

/-- Two half-open intervals `[off1, off1 + w1)` and `[off2, off2 + w2)` are disjoint. -/
def DisjointSlice (off1 w1 off2 w2 : Nat) : Prop :=
  off1 + w1 ≤ off2 ∨ off2 + w2 ≤ off1

/-- Bitvector value denoted by `litsPool[off ..< off + w]` in `g` under valuation `ρ`. -/
def sliceVal (g : Aig) (ρ : Nat → Bool) (litsPool : List (BitVec 32)) (off w : Nat) :
    BitVec w :=
  BitVec.cast (by simp) (BitVec.ofBoolListLE
    ((List.range w).map fun j => g.evalLit ρ (UInt32.ofBitVec (litsPool.getD (off + j) 0#32))))

/-- Sum modulo `2^w` of `len` contiguous `w`-bit slices starting at `off`. -/
def sliceSum (g : Aig) (ρ : Nat → Bool) (litsPool : List (BitVec 32)) (off len w : Nat) :
    BitVec w :=
  (List.range len).foldl (fun acc i => acc + sliceVal g ρ litsPool (off + i * w) w) 0#w

/-- Canonical spec for `bv_slice_ok` from `OpsCore`. -/
def bvSliceOkSpec : Spec [i64, i32, i32] [Ty.bool] :=
  fun ⟨h, off, w, ⟨⟩⟩ m Q _X =>
    ∃ hdr R, (bvHdrMem h hdr ⋆ R) m ∧
      let ok : Bool :=
        decide (hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
          (0 < w.toNat → hdr.lits_ptr ≠ 0#64) ∧
          off.toNat ≤ hdr.lits_len.toNat ∧
          w.toNat ≤ hdr.lits_len.toNat - off.toNat)
      Q (ok, ⟨⟩) m

/-- Canonical spec for `bv_blast_eq` from `OpsCore`. -/
def bvBlastEqSpec : Spec [i64, i32, i32, i32] [i32] :=
  fun ⟨h, a_off, b_off, w, ⟨⟩⟩ m Q _X =>
    ∃ hdr g aigWords htSlots litsPool R,
      AigInv hdr g aigWords htSlots ∧
      hdr.lits_cap.toNat ≤ litsPool.length ∧
      hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
      (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
        (0 < w.toNat → hdr.lits_ptr ≠ 0#64) →
        a_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        b_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        SliceLitsWf hdr litsPool a_off.toNat w.toNat ∧
          SliceLitsWf hdr litsPool b_off.toNat w.toNat) ∧
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m ∧
      ∀ ret hdr' g' aigWords' htSlots' m',
        hdr.AigFrame hdr' →
        g ≤ g' →
        g'.nodes.size ≤ g.nodes.size + 4 * w.toNat →
        AigInv hdr' g' aigWords' htSlots' →
        (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
        (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
          (0 < w.toNat → hdr.lits_ptr ≠ 0#64) →
          a_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
          b_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
          g.A + 1 + g.nodes.size + 4 * w.toNat ≤ hdr.aig_cap.toNat →
          g.nodes.size + 4 * w.toNat ≤ bvMaxGates → hdr'.oom = 0#32) →
        (hdr'.oom ≠ 0#32 → ret = 0#32) →
        (hdr'.oom = 0#32 →
          hdr.oom = 0#32 ∧ hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
          (0 < w.toNat → hdr.lits_ptr ≠ 0#64) ∧
          a_off.toNat + w.toNat ≤ hdr.lits_len.toNat ∧
          b_off.toNat + w.toNat ≤ hdr.lits_len.toNat ∧
          (ret >>> 1).toNat < hdr'.aig_len.toNat ∧
          ∀ ρ, g'.evalLit ρ (UInt32.ofBitVec ret) =
            decide (sliceVal g ρ litsPool a_off.toNat w.toNat =
              sliceVal g ρ litsPool b_off.toNat w.toNat)) →
        (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
          array (t := i32) hdr'.ht_ptr htSlots' ⋆
          array (t := i32) hdr'.lits_ptr litsPool ⋆ R) m' →
        Q (ret, ⟨⟩) m'

/-- Canonical spec for `bv_blast_ite_into`. -/
def bvBlastIteIntoSpec : Spec [i64, i32, i32, i32, i32, i32] [Ty.bool] :=
  fun ⟨h, cond, t_off, f_off, out_off, w, ⟨⟩⟩ m Q _X =>
    ∃ hdr g aigWords htSlots litsPool R,
      AigInv hdr g aigWords htSlots ∧
      hdr.lits_cap.toNat ≤ litsPool.length ∧
      (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
        (0 < w.toNat → hdr.lits_ptr ≠ 0#64) →
        t_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        f_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        out_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        (0 < w.toNat → (cond >>> 1).toNat < hdr.aig_len.toNat) ∧
          SliceLitsWf hdr litsPool t_off.toNat w.toNat ∧
          SliceLitsWf hdr litsPool f_off.toNat w.toNat ∧
          DisjointSlice out_off.toNat w.toNat t_off.toNat w.toNat ∧
          DisjointSlice out_off.toNat w.toNat f_off.toNat w.toNat) ∧
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m ∧
      ∀ ret hdr' g' aigWords' htSlots' litsPool' m',
        hdr.AigFrame hdr' →
        g ≤ g' →
        g'.nodes.size ≤ g.nodes.size + 3 * w.toNat →
        AigInv hdr' g' aigWords' htSlots' →
        litsPool'.length = litsPool.length →
        (∀ p, p < out_off.toNat ∨ out_off.toNat + w.toNat ≤ p →
          litsPool'.getD p 0#32 = litsPool.getD p 0#32) →
        (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
        (ret = true ↔ hdr'.oom = 0#32) →
        (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
          (0 < w.toNat → hdr.lits_ptr ≠ 0#64) →
          t_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
          f_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
          out_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
          g.A + 1 + g.nodes.size + 3 * w.toNat ≤ hdr.aig_cap.toNat →
          g.nodes.size + 3 * w.toNat ≤ bvMaxGates → hdr'.oom = 0#32) →
        (ret = true →
          SliceLitsWf hdr' litsPool' out_off.toNat w.toNat ∧
          ∀ ρ, sliceVal g' ρ litsPool' out_off.toNat w.toNat =
            if g.evalLit ρ (UInt32.ofBitVec cond) then
              sliceVal g ρ litsPool t_off.toNat w.toNat
            else sliceVal g ρ litsPool f_off.toNat w.toNat) →
        (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
          array (t := i32) hdr'.ht_ptr htSlots' ⋆
          array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
        Q (ret, ⟨⟩) m'

/-- Canonical spec for `bv_blast_ite_slice`. -/
def bvBlastIteSliceSpec : Spec [i64, i32, i32, i32, i32] [i32] :=
  fun ⟨h, cond, t_off, f_off, w, ⟨⟩⟩ m Q _X =>
    ∃ hdr g aigWords htSlots litsPool R,
      AigInv hdr g aigWords htSlots ∧
      hdr.lits_cap.toNat ≤ litsPool.length ∧
      (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
        (0 < w.toNat → hdr.lits_ptr ≠ 0#64) →
        t_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        f_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        (0 < w.toNat → (cond >>> 1).toNat < hdr.aig_len.toNat) ∧
          SliceLitsWf hdr litsPool t_off.toNat w.toNat ∧
          SliceLitsWf hdr litsPool f_off.toNat w.toNat) ∧
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m ∧
      ∀ ret hdr' g' aigWords' htSlots' litsPool' m',
        hdr.DcBlastFrame hdr' →
        g ≤ g' →
        g'.nodes.size ≤ g.nodes.size + 3 * w.toNat →
        AigInv hdr' g' aigWords' htSlots' →
        litsPool'.length = litsPool.length →
        (∀ p, p < hdr.lits_len.toNat → litsPool'.getD p 0#32 = litsPool.getD p 0#32) →
        (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
        (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
          (0 < w.toNat → hdr.lits_ptr ≠ 0#64) →
          t_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
          f_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
          w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat →
          g.A + 1 + g.nodes.size + 3 * w.toNat ≤ hdr.aig_cap.toNat →
          g.nodes.size + 3 * w.toNat ≤ bvMaxGates → hdr'.oom = 0#32) →
        (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32 ∧ hdr'.lits_len = hdr.lits_len) →
        (hdr'.oom = 0#32 →
          ret = hdr.lits_len ∧
          hdr'.lits_len = hdr.lits_len + w ∧
          hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat ∧
          SliceLitsWf hdr' litsPool' ret.toNat w.toNat ∧
          ∀ ρ, sliceVal g' ρ litsPool' ret.toNat w.toNat =
            if g.evalLit ρ (UInt32.ofBitVec cond) then
              sliceVal g ρ litsPool t_off.toNat w.toNat
            else sliceVal g ρ litsPool f_off.toNat w.toNat) →
        (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
          array (t := i32) hdr'.ht_ptr htSlots' ⋆
          array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
        Q (ret, ⟨⟩) m'

/-- Canonical spec for `bv_blast_sub_with_borrow`. -/
def bvBlastSubWithBorrowSpec : Spec [i64, i32, i32, i32, i32] [i32] :=
  fun ⟨h, a_off, b_off, out_off, w, ⟨⟩⟩ m Q _X =>
    ∃ hdr g aigWords htSlots litsPool R,
      AigInv hdr g aigWords htSlots ∧
      hdr.lits_cap.toNat ≤ litsPool.length ∧
      (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
        (0 < w.toNat → hdr.lits_ptr ≠ 0#64) →
        a_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        b_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        out_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        SliceLitsWf hdr litsPool a_off.toNat w.toNat ∧
          SliceLitsWf hdr litsPool b_off.toNat w.toNat ∧
          DisjointSlice out_off.toNat w.toNat a_off.toNat w.toNat ∧
          DisjointSlice out_off.toNat w.toNat b_off.toNat w.toNat) ∧
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m ∧
      ∀ ret hdr' g' aigWords' htSlots' litsPool' m',
        hdr.AigFrame hdr' →
        g ≤ g' →
        g'.nodes.size ≤ g.nodes.size + 9 * w.toNat →
        AigInv hdr' g' aigWords' htSlots' →
        litsPool'.length = litsPool.length →
        (∀ p, p < out_off.toNat ∨ out_off.toNat + w.toNat ≤ p →
          litsPool'.getD p 0#32 = litsPool.getD p 0#32) →
        (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
        (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
          (0 < w.toNat → hdr.lits_ptr ≠ 0#64) →
          a_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
          b_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
          out_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
          g.A + 1 + g.nodes.size + 9 * w.toNat ≤ hdr.aig_cap.toNat →
          g.nodes.size + 9 * w.toNat ≤ bvMaxGates → hdr'.oom = 0#32) →
        (hdr'.oom ≠ 0#32 → ret = 0#32) →
        (hdr'.oom = 0#32 →
          SliceLitsWf hdr' litsPool' out_off.toNat w.toNat ∧
          (ret >>> 1).toNat < hdr'.aig_len.toNat ∧
          ∀ ρ,
            sliceVal g' ρ litsPool' out_off.toNat w.toNat =
              sliceVal g ρ litsPool a_off.toNat w.toNat -
                sliceVal g ρ litsPool b_off.toNat w.toNat ∧
            g'.evalLit ρ (UInt32.ofBitVec ret) =
              (sliceVal g ρ litsPool a_off.toNat w.toNat).ult
                (sliceVal g ρ litsPool b_off.toNat w.toNat)) →
        (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
          array (t := i32) hdr'.ht_ptr htSlots' ⋆
          array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
        Q (ret, ⟨⟩) m'

/-- Canonical spec for `bv_blast_udiv_umod`. -/
def bvBlastUdivUmodSpec : Spec [i64, i32, i32, i32, i32] [i32] :=
  fun ⟨h, n_off, d_off, w, want_rem, ⟨⟩⟩ m Q _X =>
    ∃ hdr g aigWords htSlots litsPool R,
      AigInv hdr g aigWords htSlots ∧
      hdr.lits_cap.toNat ≤ litsPool.length ∧
      (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
        (0 < w.toNat → hdr.lits_ptr ≠ 0#64) →
        n_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        d_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        SliceLitsWf hdr litsPool n_off.toNat w.toNat ∧
          SliceLitsWf hdr litsPool d_off.toNat w.toNat) ∧
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m ∧
      ∀ ret hdr' g' aigWords' htSlots' litsPool' m',
        hdr.DcBlastFrame hdr' →
        g ≤ g' →
        g'.nodes.size ≤ g.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) →
        AigInv hdr' g' aigWords' htSlots' →
        litsPool'.length = litsPool.length →
        (∀ p, p < hdr.lits_len.toNat → litsPool'.getD p 0#32 = litsPool.getD p 0#32) →
        (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
        (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
          (0 < w.toNat → hdr.lits_ptr ≠ 0#64) →
          n_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
          d_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
          5 * w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat →
          g.A + 1 + g.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) ≤ hdr.aig_cap.toNat →
          g.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) ≤ bvMaxGates →
          hdr'.oom = 0#32) →
        (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32 ∧ hdr'.lits_len = hdr.lits_len) →
        (hdr'.oom = 0#32 →
          ret = hdr.lits_len ∧
          hdr'.lits_len = hdr.lits_len + w ∧
          hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat ∧
          SliceLitsWf hdr' litsPool' ret.toNat w.toNat ∧
          ∀ ρ, sliceVal g' ρ litsPool' ret.toNat w.toNat =
            if want_rem ≠ 0#32 then
              sliceVal g ρ litsPool n_off.toNat w.toNat %
                sliceVal g ρ litsPool d_off.toNat w.toNat
            else
              sliceVal g ρ litsPool n_off.toNat w.toNat /
                sliceVal g ρ litsPool d_off.toNat w.toNat) →
        (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
          array (t := i32) hdr'.ht_ptr htSlots' ⋆
          array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
        Q (ret, ⟨⟩) m'

/-- Canonical spec for `bv_blast_udiv`. -/
def bvBlastUdivSpec : Spec [i64, i32, i32, i32] [i32] :=
  fun ⟨h, n_off, d_off, w, ⟨⟩⟩ m Q X =>
    bvBlastUdivUmodSpec ⟨h, n_off, d_off, w, 0#32, ⟨⟩⟩ m Q X

/-- Canonical spec for `bv_blast_umod`. -/
def bvBlastUmodSpec : Spec [i64, i32, i32, i32] [i32] :=
  fun ⟨h, n_off, d_off, w, ⟨⟩⟩ m Q X =>
    bvBlastUdivUmodSpec ⟨h, n_off, d_off, w, 1#32, ⟨⟩⟩ m Q X

/-- Canonical spec for `bv_blast_add_into`. -/
def bvBlastAddIntoSpec : Spec [i64, i32, i32, i32, i32] [Ty.bool] :=
  fun ⟨h, a_off, b_off, out_off, w, ⟨⟩⟩ m Q _X =>
    ∃ hdr g aigWords htSlots litsPool R,
      AigInv hdr g aigWords htSlots ∧
      hdr.lits_cap.toNat ≤ litsPool.length ∧
      (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
        (0 < w.toNat → hdr.lits_ptr ≠ 0#64) →
        a_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        b_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        out_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        SliceLitsWf hdr litsPool a_off.toNat w.toNat ∧
          SliceLitsWf hdr litsPool b_off.toNat w.toNat ∧
          DisjointSlice out_off.toNat w.toNat a_off.toNat w.toNat ∧
          DisjointSlice out_off.toNat w.toNat b_off.toNat w.toNat) ∧
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m ∧
      ∀ ret hdr' g' aigWords' htSlots' litsPool' m',
        hdr.AigFrame hdr' →
        g ≤ g' →
        g'.nodes.size ≤ g.nodes.size + 9 * w.toNat →
        AigInv hdr' g' aigWords' htSlots' →
        litsPool'.length = litsPool.length →
        (∀ p, p < out_off.toNat ∨ out_off.toNat + w.toNat ≤ p →
          litsPool'.getD p 0#32 = litsPool.getD p 0#32) →
        (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
        (ret = true ↔ hdr'.oom = 0#32) →
        (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
          (0 < w.toNat → hdr.lits_ptr ≠ 0#64) →
          a_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
          b_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
          out_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
          g.A + 1 + g.nodes.size + 9 * w.toNat ≤ hdr.aig_cap.toNat →
          g.nodes.size + 9 * w.toNat ≤ bvMaxGates → hdr'.oom = 0#32) →
        (ret = true →
          SliceLitsWf hdr' litsPool' out_off.toNat w.toNat ∧
          ∀ ρ, sliceVal g' ρ litsPool' out_off.toNat w.toNat =
            sliceVal g ρ litsPool a_off.toNat w.toNat +
              sliceVal g ρ litsPool b_off.toNat w.toNat) →
        (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
          array (t := i32) hdr'.ht_ptr htSlots' ⋆
          array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
        Q (ret, ⟨⟩) m'

/-- Canonical spec for `bv_blast_cpop_layer`. -/
def bvBlastCpopLayerSpec : Spec [i64, i32, i32, i32, i32] [Ty.bool] :=
  fun ⟨h, in_off, out_off, in_len, w, ⟨⟩⟩ m Q _X =>
    ∃ hdr g aigWords htSlots litsPool R,
      AigInv hdr g aigWords htSlots ∧
      hdr.lits_cap.toNat ≤ litsPool.length ∧
      (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
        in_len.toNat * w.toNat < 2 ^ 32 →
        (in_len.toNat + 1) / 2 * w.toNat < 2 ^ 32 →
        (0 < in_len.toNat * w.toNat → hdr.lits_ptr ≠ 0#64) →
        (0 < (in_len.toNat + 1) / 2 * w.toNat → hdr.lits_ptr ≠ 0#64) →
        in_off.toNat + in_len.toNat * w.toNat ≤ hdr.lits_len.toNat →
        out_off.toNat + (in_len.toNat + 1) / 2 * w.toNat ≤ hdr.lits_len.toNat →
        SliceLitsWf hdr litsPool in_off.toNat (in_len.toNat * w.toNat) ∧
          DisjointSlice out_off.toNat ((in_len.toNat + 1) / 2 * w.toNat)
            in_off.toNat (in_len.toNat * w.toNat)) ∧
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m ∧
      ∀ ret hdr' g' aigWords' htSlots' litsPool' m',
        hdr.AigFrame hdr' →
        g ≤ g' →
        g'.nodes.size ≤ g.nodes.size + (in_len.toNat / 2) * (9 * w.toNat) →
        AigInv hdr' g' aigWords' htSlots' →
        litsPool'.length = litsPool.length →
        (∀ p, p < out_off.toNat ∨ out_off.toNat + (in_len.toNat + 1) / 2 * w.toNat ≤ p →
          litsPool'.getD p 0#32 = litsPool.getD p 0#32) →
        (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
        (ret = true ↔ hdr'.oom = 0#32) →
        (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
          in_len.toNat * w.toNat < 2 ^ 32 →
          (in_len.toNat + 1) / 2 * w.toNat < 2 ^ 32 →
          (0 < in_len.toNat * w.toNat → hdr.lits_ptr ≠ 0#64) →
          (0 < (in_len.toNat + 1) / 2 * w.toNat → hdr.lits_ptr ≠ 0#64) →
          in_off.toNat + in_len.toNat * w.toNat ≤ hdr.lits_len.toNat →
          out_off.toNat + (in_len.toNat + 1) / 2 * w.toNat ≤ hdr.lits_len.toNat →
          g.A + 1 + g.nodes.size + (in_len.toNat / 2) * (9 * w.toNat) ≤ hdr.aig_cap.toNat →
          g.nodes.size + (in_len.toNat / 2) * (9 * w.toNat) ≤ bvMaxGates → hdr'.oom = 0#32) →
        (ret = true →
          SliceLitsWf hdr' litsPool' out_off.toNat ((in_len.toNat + 1) / 2 * w.toNat) ∧
          ∀ ρ, sliceSum g' ρ litsPool' out_off.toNat ((in_len.toNat + 1) / 2) w.toNat =
            sliceSum g ρ litsPool in_off.toNat in_len.toNat w.toNat) →
        (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
          array (t := i32) hdr'.ht_ptr htSlots' ⋆
          array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
        Q (ret, ⟨⟩) m'

/-- Canonical spec for `bv_blast_cpop`. -/
def bvBlastCpopSpec : Spec [i64, i32, i32] [i32] :=
  fun ⟨h, a_off, w, ⟨⟩⟩ m Q _X =>
    ∃ hdr g aigWords htSlots litsPool R,
      AigInv hdr g aigWords htSlots ∧
      hdr.lits_cap.toNat ≤ litsPool.length ∧
      (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
        (0 < w.toNat → hdr.lits_ptr ≠ 0#64) →
        a_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        SliceLitsWf hdr litsPool a_off.toNat w.toNat) ∧
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m ∧
      ∀ ret hdr' g' aigWords' htSlots' litsPool' m',
        hdr.DcBlastFrame hdr' →
        g ≤ g' →
        g'.nodes.size ≤ g.nodes.size + 9 * w.toNat * w.toNat →
        AigInv hdr' g' aigWords' htSlots' →
        litsPool'.length = litsPool.length →
        (∀ p, p < hdr.lits_len.toNat → litsPool'.getD p 0#32 = litsPool.getD p 0#32) →
        (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
        (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
          (0 < w.toNat → hdr.lits_ptr ≠ 0#64) →
          a_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
          w.toNat * w.toNat < 2 ^ 32 →
          (w.toNat + 1) / 2 * w.toNat < 2 ^ 32 →
          w.toNat + (if w.toNat ≤ 1 then 0 else
            w.toNat * w.toNat + (w.toNat + 1) / 2 * w.toNat) ≤
            hdr.lits_cap.toNat - hdr.lits_len.toNat →
          g.A + 1 + g.nodes.size + 9 * w.toNat * w.toNat ≤ hdr.aig_cap.toNat →
          g.nodes.size + 9 * w.toNat * w.toNat ≤ bvMaxGates → hdr'.oom = 0#32) →
        (hdr'.oom ≠ 0#32 →
          ret = 0xFFFFFFFF#32 ∧ hdr.lits_len.toNat ≤ hdr'.lits_len.toNat ∧
          (w.toNat * w.toNat < 2 ^ 32 → (w.toNat + 1) / 2 * w.toNat < 2 ^ 32 →
            hdr'.lits_len = hdr.lits_len)) →
        (hdr'.oom = 0#32 →
          ret = hdr.lits_len ∧
          hdr'.lits_len = hdr.lits_len + w ∧
          hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat ∧
          SliceLitsWf hdr' litsPool' ret.toNat w.toNat ∧
          ∀ ρ, sliceVal g' ρ litsPool' ret.toNat w.toNat =
            (sliceVal g ρ litsPool a_off.toNat w.toNat).cpop) →
        (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
          array (t := i32) hdr'.ht_ptr htSlots' ⋆
          array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
        Q (ret, ⟨⟩) m'

/-- Extern spec rows matching `opsDivCpopExterns`. -/
def opsDivCpopDeps : List SpecEntry :=
  [ ⟨"bv_mk_and", [i64, i32, i32], [i32], bvMkAndSpec, true⟩
  , ⟨"bv_aig_not", [i32], [i32], bvAigNotSpec, true⟩
  , ⟨"bv_aig_or", [i64, i32, i32], [i32], bvAigOrSpec, true⟩
  , ⟨"bv_aig_xor", [i64, i32, i32], [i32], bvAigXorSpec, true⟩
  , ⟨"bv_aig_ite", [i64, i32, i32, i32], [i32], bvAigIteSpec, true⟩
  , ⟨"bv_lits_mark", [i64], [i32], bvLitsMarkSpec, true⟩
  , ⟨"bv_lits_release", [i64, i32], [], bvLitsReleaseSpec, true⟩
  , ⟨"bv_lits_alloc", [i64, i32], [i32], bvLitsAllocSpec, true⟩
  , ⟨"bv_slice_ok", [i64, i32, i32], [Ty.bool], bvSliceOkSpec, true⟩
  , ⟨"bv_blast_eq", [i64, i32, i32, i32], [i32], bvBlastEqSpec, true⟩
  ]

/-- Canonical spec rows matching `opsDivCpopFns`. -/
def opsDivCpopSpecs : List SpecEntry :=
  [ ⟨"bv_blast_ite_into", [i64, i32, i32, i32, i32, i32], [Ty.bool], bvBlastIteIntoSpec, true⟩
  , ⟨"bv_blast_ite_slice", [i64, i32, i32, i32, i32], [i32], bvBlastIteSliceSpec, true⟩
  , ⟨"bv_blast_sub_with_borrow", [i64, i32, i32, i32, i32], [i32],
      bvBlastSubWithBorrowSpec, true⟩
  , ⟨"bv_blast_udiv_umod", [i64, i32, i32, i32, i32], [i32], bvBlastUdivUmodSpec, true⟩
  , ⟨"bv_blast_udiv", [i64, i32, i32, i32], [i32], bvBlastUdivSpec, true⟩
  , ⟨"bv_blast_umod", [i64, i32, i32, i32], [i32], bvBlastUmodSpec, true⟩
  , ⟨"bv_blast_add_into", [i64, i32, i32, i32, i32], [Ty.bool], bvBlastAddIntoSpec, true⟩
  , ⟨"bv_blast_cpop_layer", [i64, i32, i32, i32, i32], [Ty.bool], bvBlastCpopLayerSpec, true⟩
  , ⟨"bv_blast_cpop", [i64, i32, i32], [i32], bvBlastCpopSpec, true⟩
  ]

end

public section

theorem bvSliceOkSpec_xfree : bvSliceOkSpec.XFree := fun _ _ _ _ _ h => h
theorem bvBlastEqSpec_xfree : bvBlastEqSpec.XFree := fun _ _ _ _ _ h => h
theorem bvBlastIteIntoSpec_xfree : bvBlastIteIntoSpec.XFree := fun _ _ _ _ _ h => h
theorem bvBlastIteSliceSpec_xfree : bvBlastIteSliceSpec.XFree := fun _ _ _ _ _ h => h
theorem bvBlastSubWithBorrowSpec_xfree : bvBlastSubWithBorrowSpec.XFree := fun _ _ _ _ _ h => h
theorem bvBlastUdivUmodSpec_xfree : bvBlastUdivUmodSpec.XFree := fun _ _ _ _ _ h => h
theorem bvBlastUdivSpec_xfree : bvBlastUdivSpec.XFree := fun _ _ _ _ _ h => h
theorem bvBlastUmodSpec_xfree : bvBlastUmodSpec.XFree := fun _ _ _ _ _ h => h
theorem bvBlastAddIntoSpec_xfree : bvBlastAddIntoSpec.XFree := fun _ _ _ _ _ h => h
theorem bvBlastCpopLayerSpec_xfree : bvBlastCpopLayerSpec.XFree := fun _ _ _ _ _ h => h
theorem bvBlastCpopSpec_xfree : bvBlastCpopSpec.XFree := fun _ _ _ _ _ h => h

theorem aigInv_blastFrame {hdr hdr' : BVHdrState} {g : Aig}
    {aigWords : List (BitVec 64)} {htSlots : List (BitVec 32)}
    (hinv : AigInv hdr g aigWords htSlots) (hf : hdr.DcBlastFrame hdr')
    (haig : hdr'.aig_len = hdr.aig_len) : AigInv hdr' g aigWords htSlots :=
  hinv.of_modifies hf haig

theorem bvWorkspaceOk_of_blastFrame {cfg : BVWorkspaceCfg} {hdr hdr' : BVHdrState}
    {g' : Aig} {atomBases sliceOffs : List (BitVec 32)}
    {aigWords aigWords' : List (BitVec 64)} {htSlots htSlots' litsPool litsPool' : List (BitVec 32)}
    (hws : BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool)
    (hf : hdr.DcBlastFrame hdr') (hinv : AigInv hdr' g' aigWords' htSlots')
    (hlp : litsPool'.length = litsPool.length) :
    BVWorkspaceOk cfg hdr' atomBases sliceOffs aigWords' htSlots' litsPool' :=
  hws.of_modifies_aigInv hf hinv hlp

/-! ## `SliceLitsWf`, `DisjointSlice`, and `sliceVal` lemmas -/

theorem disjointSlice_symm {off1 w1 off2 w2 : Nat}
    (h : DisjointSlice off1 w1 off2 w2) : DisjointSlice off2 w2 off1 w1 := by
  unfold DisjointSlice at *; omega

theorem disjointSlice_sub {off1 w1 off2 w2 off1' w1' off2' w2' : Nat}
    (h : DisjointSlice off1 w1 off2 w2)
    (hs1 : off1 ≤ off1' ∧ off1' + w1' ≤ off1 + w1)
    (hs2 : off2 ≤ off2' ∧ off2' + w2' ≤ off2 + w2) :
    DisjointSlice off1' w1' off2' w2' := by
  unfold DisjointSlice at *; omega

theorem sliceLitsWf_mono {hdr hdr' : BVHdrState} {lp lp' : List (BitVec 32)}
    {off w : Nat} (hwf : SliceLitsWf hdr lp off w)
    (haig : hdr.aig_len.toNat ≤ hdr'.aig_len.toNat)
    (hlen : hdr.lits_len.toNat ≤ hdr'.lits_len.toNat)
    (hagree : ∀ p, off ≤ p → p < off + w → lp'.getD p 0#32 = lp.getD p 0#32) :
    SliceLitsWf hdr' lp' off w := by
  rcases hwf with ⟨h1, h2⟩
  refine ⟨by omega, fun j hj => ?_⟩
  rw [hagree (off + j) (by omega) (by omega)]
  exact Nat.lt_of_lt_of_le (h2 j hj) haig

theorem sliceLitsWf_sub {hdr : BVHdrState} {lp : List (BitVec 32)}
    {off w off' w' : Nat} (hwf : SliceLitsWf hdr lp off w)
    (hsub : off ≤ off' ∧ off' + w' ≤ off + w) :
    SliceLitsWf hdr lp off' w' := by
  rcases hwf with ⟨h1, h2⟩
  refine ⟨by omega, fun j hj => ?_⟩
  have hlt := h2 (off' - off + j) (by omega)
  have heq : off + (off' - off + j) = off' + j := by omega
  rw [heq] at hlt
  exact hlt

theorem sliceLitsWf_zero {hdr : BVHdrState} {lp : List (BitVec 32)} (off : Nat)
    (hoff : off ≤ hdr.lits_len.toNat) : SliceLitsWf hdr lp off 0 :=
  ⟨hoff, fun _ hj => False.elim (Nat.not_lt_zero _ hj)⟩

theorem sliceVal_getLsbD {g : Aig} {ρ : Nat → Bool} {lp : List (BitVec 32)}
    {off w j : Nat} (hj : j < w) :
    (sliceVal g ρ lp off w).getLsbD j =
      g.evalLit ρ (UInt32.ofBitVec (lp.getD (off + j) 0#32)) := by
  unfold sliceVal
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]

theorem sliceVal_eq_of_agree {g : Aig} {ρ : Nat → Bool} {lp lp' : List (BitVec 32)}
    {off w : Nat} (hagree : ∀ p, off ≤ p → p < off + w → lp'.getD p 0#32 = lp.getD p 0#32) :
    sliceVal g ρ lp' off w = sliceVal g ρ lp off w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [sliceVal_getLsbD hi, sliceVal_getLsbD hi]
  rw [hagree (off + i) (by omega) (by omega)]

theorem sliceVal_extend_aig {hdr : BVHdrState} {g g' : Aig}
    {aigWords : List (BitVec 64)} {htSlots : List (BitVec 32)}
    {ρ : Nat → Bool} {lp : List (BitVec 32)} {off w : Nat}
    (hinv : AigInv hdr g aigWords htSlots) (hext : g ≤ g')
    (hwf : SliceLitsWf hdr lp off w) :
    sliceVal g' ρ lp off w = sliceVal g ρ lp off w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [sliceVal_getLsbD hi, sliceVal_getLsbD hi]
  have hlt := hwf.2 i hi
  have hlit : (UInt32.ofBitVec (lp.getD (off + i) 0#32)).toNat <
      2 * (g.A + 1 + g.nodes.size) := by
    have haig : ((lp.getD (off + i) 0#32) >>> 1).toNat < g.A + 1 + g.nodes.size := by
      rw [← hinv.aig_len_eq]; exact hlt
    have hdiv : (UInt32.ofBitVec (lp.getD (off + i) 0#32)).toNat / 2 =
        ((lp.getD (off + i) 0#32) >>> 1).toNat := by
      simp [UInt32.toNat, Nat.shiftRight_eq_div_pow]
    omega
  exact Aig.evalLit_extend hext hlit

theorem sliceDenotes_iff_of_le {g : Aig} {ρ : Nat → Bool} {lp : List (BitVec 32)}
    {off w : Nat} {v : BitVec w} (hoff : off + w ≤ lp.length) :
    SliceDenotes g ρ (litsSlice lp off w) v ↔ sliceVal g ρ lp off w = v := by
  constructor
  · intro ⟨_, hbits⟩
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [sliceVal_getLsbD hi]
    have hb := hbits i hi
    rw [litsSlice_getD hoff hi] at hb
    simpa using hb
  · rintro rfl
    refine ⟨litsSlice_length hoff, fun j hj => ?_⟩
    rw [litsSlice_getD hoff hj, sliceVal_getLsbD hj]

theorem sliceDenotes_iff_sliceVal {g : Aig} {ρ : Nat → Bool} {lp : List (BitVec 32)}
    {off w : Nat} {v : BitVec w} (hw : 0 < w) :
    SliceDenotes g ρ (litsSlice lp off w) v ↔ off + w ≤ lp.length ∧ sliceVal g ρ lp off w = v := by
  constructor
  · intro h
    have hlen := h.1
    rw [litsSlice] at hlen
    simp [List.length_take, List.length_drop] at hlen
    have hoff : off + w ≤ lp.length := by omega
    exact ⟨hoff, (sliceDenotes_iff_of_le hoff).mp h⟩
  · rintro ⟨hoff, hval⟩
    exact (sliceDenotes_iff_of_le hoff).mpr hval

/-! ## `BitVec` and arithmetic helper lemmas for `OpsDivCpop` -/

theorem bv_ite_bit_spec (c t f : Bool) :
    (if c then t else f) = ((c && t) || (!c && f)) := by
  cases c <;> simp

theorem bv_sub_step_carry (a b cin : Bool) :
    Bool.atLeastTwo a (!b) cin = ((a && !b) || (cin && (a ^^ !b))) := by
  cases a <;> cases b <;> cases cin <;> rfl

theorem bv_add_step_carry (a b cin : Bool) :
    Bool.atLeastTwo a b cin = ((a && b) || (cin && (a ^^ b))) := by
  cases a <;> cases b <;> cases cin <;> rfl

theorem bv_sub_diff_getLsbD {w : Nat} (x y : BitVec w) {j : Nat} (hj : j < w) :
    (x - y).getLsbD j = ((x.getLsbD j ^^ !(y.getLsbD j)) ^^ BitVec.carry j x (~~~y) true) := by
  have hw1 : BitVec.setWidth w (BitVec.ofBool true) = 1#w := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
  have h1 : x - y = x + ~~~y + BitVec.setWidth w (BitVec.ofBool true) := by
    rw [hw1, BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.add_assoc]
  rw [h1, BitVec.getLsbD_add_add_bool hj, BitVec.getLsbD_not]
  simp only [hj, decide_true, Bool.true_and]
  cases x.getLsbD j <;> cases y.getLsbD j <;> cases BitVec.carry j x (~~~y) true <;> rfl

theorem bv_sub_borrow_done {w : Nat} (x y : BitVec w) :
    !(BitVec.carry w x (~~~y) true) = x.ult y := by
  rw [BitVec.ult_eq_not_carry]
  simp

theorem bv_add_sum_getLsbD {w : Nat} (x y : BitVec w) {j : Nat} (hj : j < w) :
    (x + y).getLsbD j = ((x.getLsbD j ^^ y.getLsbD j) ^^ BitVec.carry j x y false) := by
  have h1 : x + y = x + y + BitVec.setWidth w (BitVec.ofBool false) := by simp
  rw [h1, BitVec.getLsbD_add_add_bool hj]
  cases x.getLsbD j <;> cases y.getLsbD j <;> cases BitVec.carry j x y false <;> rfl

theorem divRec_succ_right {w : Nat} (k : Nat) (qr : BitVec.DivModArgs w)
    (st : BitVec.DivModState w) :
    BitVec.divRec (k + 1) qr st =
      BitVec.divSubtractShift qr (BitVec.divRec k qr st) := by
  induction k generalizing st with
  | zero => simp [BitVec.divRec]
  | succ k ih =>
    rw [BitVec.divRec_succ', ih, ← BitVec.divRec_succ']

theorem divRec_wn {w : Nat} (k : Nat) (hk : k ≤ w) (qr : BitVec.DivModArgs w) :
    (BitVec.divRec k qr (BitVec.DivModState.init w)).wn = w - k := by
  induction k with
  | zero => simp [BitVec.divRec, BitVec.DivModState.init]
  | succ k ih =>
    rw [divRec_succ_right]
    simp [BitVec.divSubtractShift, ih (Nat.le_of_succ_le hk)]
    split <;> simp <;> omega

theorem divRec_rPrime_getLsbD {w : Nat} (r : BitVec w) (nb : Bool) (j : Nat) (hj : j < w) :
    (r.shiftConcat nb).getLsbD j = if j = 0 then nb else r.getLsbD (j - 1) := by
  rw [BitVec.getLsbD_shiftConcat]
  cases j with
  | zero => simp [hj]
  | succ k => simp [hj]

theorem divRec_step_state {w : Nat} (k : Nat) (hk : k < w) (n d : BitVec w) :
    let st := BitVec.divRec k { n := n, d := d } (BitVec.DivModState.init w)
    let st' := BitVec.divRec (k + 1) { n := n, d := d } (BitVec.DivModState.init w)
    let rPrime := st.r.shiftConcat (n.getLsbD (w - 1 - k))
    let borrow := rPrime.ult d
    let diff := rPrime - d
    st'.r = (if borrow then rPrime else diff) ∧
    st'.q = st.q.shiftConcat (!borrow) := by
  intro st st' rPrime borrow diff
  have hwn : st.wn = w - k := divRec_wn k (Nat.le_of_lt hk) { n := n, d := d }
  have hsub : w - k - 1 = w - 1 - k := by omega
  have hlt_eq : rPrime.ult d = decide (rPrime < d) := by
    rw [BitVec.ult]; simp [BitVec.lt_def]
  have hrec : st' = BitVec.divSubtractShift { n := n, d := d } st :=
    divRec_succ_right k { n := n, d := d } (BitVec.DivModState.init w)
  rw [hrec]
  dsimp [BitVec.divSubtractShift]
  rw [hwn, hsub]
  by_cases hlt : rPrime < d
  · have hb : borrow = true := by simp [borrow, hlt_eq, hlt]
    simp [hlt, hb, rPrime]
  · have hb : borrow = false := by simp [borrow, hlt_eq, hlt]
    simp [hlt, hb, rPrime, diff]

theorem udiv_eq_of_divRec {w : Nat} (n d : BitVec w) :
    n / d = if d = 0#w then 0#w else
      (BitVec.divRec w { n := n, d := d } (BitVec.DivModState.init w)).q := by
  by_cases hd : d = 0#w
  · subst hd; simp [BitVec.udiv_zero]
  · simp [hd]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_udiv]
    · simp [hi]
    · rw [BitVec.lt_def]
      exact Nat.pos_of_ne_zero fun h => hd (BitVec.eq_of_toNat_eq (by simpa using h))

theorem umod_eq_of_divRec {w : Nat} (n d : BitVec w) :
    n % d = if d = 0#w then n else
      (BitVec.divRec w { n := n, d := d } (BitVec.DivModState.init w)).r := by
  by_cases hd : d = 0#w
  · subst hd; simp [BitVec.umod_zero]
  · simp [hd]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_umod]
    simp [hi, hd]

theorem sliceSum_zero (g : Aig) (ρ : Nat → Bool) (lp : List (BitVec 32)) (off w : Nat) :
    sliceSum g ρ lp off 0 w = 0#w := rfl

theorem sliceSum_succ (g : Aig) (ρ : Nat → Bool) (lp : List (BitVec 32)) (off len w : Nat) :
    sliceSum g ρ lp off (len + 1) w =
      sliceSum g ρ lp off len w + sliceVal g ρ lp (off + len * w) w := by
  unfold sliceSum
  rw [List.range_succ, List.foldl_append]
  rfl

theorem sliceSum_one (g : Aig) (ρ : Nat → Bool) (lp : List (BitVec 32)) (off w : Nat) :
    sliceSum g ρ lp off 1 w = sliceVal g ρ lp off w := by
  rw [sliceSum_succ, sliceSum_zero, Nat.zero_mul, Nat.add_zero, BitVec.zero_add]

theorem sliceSum_eq_of_agree {g : Aig} {ρ : Nat → Bool} {lp lp' : List (BitVec 32)}
    {off len w : Nat}
    (hagree : ∀ p, off ≤ p → p < off + len * w → lp'.getD p 0#32 = lp.getD p 0#32) :
    sliceSum g ρ lp' off len w = sliceSum g ρ lp off len w := by
  induction len with
  | zero => rfl
  | succ k ih =>
    rw [sliceSum_succ, sliceSum_succ]
    have ih' := ih fun p hp1 hp2 => hagree p hp1 (Nat.lt_of_lt_of_le hp2 (by
      rw [Nat.succ_mul]; omega))
    have hlast : sliceVal g ρ lp' (off + k * w) w = sliceVal g ρ lp (off + k * w) w :=
      sliceVal_eq_of_agree fun p hp1 hp2 => hagree p (by omega) (by rw [Nat.succ_mul]; omega)
    rw [ih', hlast]

theorem sliceSum_extend_aig {hdr : BVHdrState} {g g' : Aig}
    {aigWords : List (BitVec 64)} {htSlots : List (BitVec 32)}
    {ρ : Nat → Bool} {lp : List (BitVec 32)} {off len w : Nat}
    (hinv : AigInv hdr g aigWords htSlots) (hext : g ≤ g')
    (hwf : SliceLitsWf hdr lp off (len * w)) :
    sliceSum g' ρ lp off len w = sliceSum g ρ lp off len w := by
  induction len with
  | zero => rfl
  | succ k ih =>
    rw [sliceSum_succ, sliceSum_succ]
    have hwf1 : SliceLitsWf hdr lp off (k * w) :=
      sliceLitsWf_sub hwf ⟨Nat.le_refl _, by rw [Nat.succ_mul]; omega⟩
    have hwf2 : SliceLitsWf hdr lp (off + k * w) w :=
      sliceLitsWf_sub hwf ⟨Nat.le_add_right _ _, by rw [Nat.succ_mul]; omega⟩
    rw [ih hwf1, sliceVal_extend_aig hinv hext hwf2]

theorem cpop_w0 (x : BitVec 0) : x.cpop = 0#0 := Subsingleton.elim _ _

theorem cpop_w1 (x : BitVec 1) : x.cpop = x := by
  have hnat : x.toNat = 0 ∨ x.toNat = 1 := by have := x.isLt; omega
  rcases hnat with h | h
  · have : x = 0#1 := BitVec.eq_of_toNat_eq (by simpa using h)
    subst this; decide
  · have : x = 1#1 := BitVec.eq_of_toNat_eq (by simpa using h)
    subst this; decide

theorem sliceSum_cpop_init_aux {w : Nat} (x : BitVec w) (k : Nat) :
    (List.range k).foldl (fun acc i => acc + BitVec.ofNat w (x.getLsbD i).toNat) 0#w =
      BitVec.ofNat w (x.cpopNatRec k 0) := by
  have hgen : ∀ (m acc : Nat),
      (List.range m).foldl (fun a i => a + BitVec.ofNat w (x.getLsbD i).toNat)
        (BitVec.ofNat w acc) = BitVec.ofNat w (x.cpopNatRec m acc) := by
    intro m
    induction m with
    | zero =>
      intro acc
      simp
    | succ m ih =>
      intro acc
      rw [List.range_succ, List.foldl_append]
      change List.foldl (fun a i => a + BitVec.ofNat w (x.getLsbD i).toNat)
        (BitVec.ofNat w acc) (List.range m) + BitVec.ofNat w (x.getLsbD m).toNat = _
      rw [ih, BitVec.cpopNatRec_succ]
      have hstep : ∀ n s, BitVec.ofNat w (x.cpopNatRec n s) +
          BitVec.ofNat w (x.getLsbD m).toNat =
          BitVec.ofNat w (x.cpopNatRec n (s + (x.getLsbD m).toNat)) := by
        intro n
        induction n with
        | zero =>
          intro s
          simp [BitVec.ofNat_add]
        | succ n ihn =>
          intro s
          simp only [BitVec.cpopNatRec_succ]
          rw [ihn]
          ac_rfl
      exact hstep m acc
  simpa using hgen k 0

theorem sliceSum_cpop_step_layer {g : Aig} {ρ : Nat → Bool}
    {lpIn lpOut : List (BitVec 32)} {in_off out_off in_len w : Nat}
    (hstep : ∀ i, i < (in_len + 1) / 2 →
      if 2 * i + 1 < in_len then
        sliceVal g ρ lpOut (out_off + i * w) w =
          sliceVal g ρ lpIn (in_off + (2 * i) * w) w +
            sliceVal g ρ lpIn (in_off + (2 * i + 1) * w) w
      else
        sliceVal g ρ lpOut (out_off + i * w) w =
          sliceVal g ρ lpIn (in_off + (2 * i) * w) w) :
    sliceSum g ρ lpOut out_off ((in_len + 1) / 2) w = sliceSum g ρ lpIn in_off in_len w := by
  have hprefix : ∀ k, 2 * k ≤ in_len →
      sliceSum g ρ lpOut out_off k w = sliceSum g ρ lpIn in_off (2 * k) w := by
    intro k hk
    induction k with
    | zero => simp [sliceSum_zero]
    | succ k ih =>
      have hk1 : 2 * k ≤ in_len := by omega
      have hlt_out : k < (in_len + 1) / 2 := by omega
      have hlt_in : 2 * k + 1 < in_len := by omega
      have hpair := hstep k hlt_out
      simp only [hlt_in, ↓reduceIte] at hpair
      rw [sliceSum_succ, ih hk1, hpair]
      have h2 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      rw [h2, sliceSum_succ, sliceSum_succ, BitVec.add_assoc]
  by_cases heven : in_len % 2 = 0
  · have hq : (in_len + 1) / 2 = in_len / 2 := by omega
    have hm : 2 * (in_len / 2) = in_len := by omega
    rw [hq, hprefix (in_len / 2) (by omega), hm]
  · have hodd : in_len = 2 * (in_len / 2) + 1 := by omega
    have hq : (in_len + 1) / 2 = in_len / 2 + 1 := by omega
    have hlt_out : in_len / 2 < (in_len + 1) / 2 := by omega
    have hnot : ¬ (2 * (in_len / 2) + 1 < in_len) := by omega
    have hlast := hstep (in_len / 2) hlt_out
    simp only [hnot, ↓reduceIte] at hlast
    rw [hq, sliceSum_succ, hprefix (in_len / 2) (by omega), hlast]
    have hrhs : sliceSum g ρ lpIn in_off in_len w =
        sliceSum g ρ lpIn in_off (2 * (in_len / 2)) w +
          sliceVal g ρ lpIn (in_off + (2 * (in_len / 2)) * w) w := by
      conv => lhs; rw [hodd, sliceSum_succ]
    exact hrhs.symm

theorem cpop_next_len_lt {len : Nat} (hlen : 1 < len) : (len + 1) / 2 < len := by omega

theorem cpop_gates_halving (len : Nat) (hlen : 1 ≤ len) :
    len / 2 + ((len + 1) / 2 - 1) = len - 1 := by omega

/-! ## Separation-logic focus/unfocus helpers for `OpsDivCpop` -/

theorem hdr_with_oom_with_oom (hdr : BVHdrState) (a b : BitVec 32) :
    { { hdr with oom := a } with oom := b } = { hdr with oom := b } := rfl

theorem hdr_with_oom_aigFrame {hdr : BVHdrState} {noom : BitVec 32} :
    hdr.AigFrame { hdr with oom := noom } :=
  Modifies.set_oom _ hdr noom

theorem opMem_to_hdr {h : BitVec 64} {hdr : BVHdrState} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m) :
    (bvHdrMem h hdr ⋆ (array64 hdr.aig_ptr aigWords ⋆ array (t := i32) hdr.ht_ptr htSlots ⋆
      array (t := i32) hdr.lits_ptr litsPool ⋆ R)) m := by
  simpa [Std.ExtHashMap.sep_assoc] using hm

theorem opMem_of_hdr {h : BitVec 64} {hdr : BVHdrState} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bvHdrMem h hdr ⋆ (array64 hdr.aig_ptr aigWords ⋆ array (t := i32) hdr.ht_ptr htSlots ⋆
      array (t := i32) hdr.lits_ptr litsPool ⋆ R)) m) :
    (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m := by
  simpa [Std.ExtHashMap.sep_assoc] using hm

theorem opMem_of_hdr_emp {h : BitVec 64} {hdr : BVHdrState} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bvHdrMem h hdr ⋆ (array64 hdr.aig_ptr aigWords ⋆ (array (t := i32) hdr.ht_ptr htSlots ⋆
      (array (t := i32) hdr.lits_ptr litsPool ⋆ (R ⋆ Std.ExtHashMap.emp))))) m) :
    (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m := by
  simpa [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_emp] using hm

theorem opMem_to_aig {h : BitVec 64} {hdr : BVHdrState} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m) :
    (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆ array (t := i32) hdr.ht_ptr htSlots ⋆
      (array (t := i32) hdr.lits_ptr litsPool ⋆ R)) m := by
  simpa [Std.ExtHashMap.sep_assoc] using hm

theorem opMem_of_aig {h : BitVec 64} {hdr : BVHdrState} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆ array (t := i32) hdr.ht_ptr htSlots ⋆
      (array (t := i32) hdr.lits_ptr litsPool ⋆ R)) m) :
    (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m := by
  simpa [Std.ExtHashMap.sep_assoc] using hm

theorem opMem_to_lits {h : BitVec 64} {hdr : BVHdrState} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m) :
    (array (t := i32) hdr.lits_ptr litsPool ⋆
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆ R)) m := by
  rw [Std.ExtHashMap.sep_comm]
  rw [Std.ExtHashMap.sep_assoc,
    Std.ExtHashMap.sep_comm (array (t := i32) hdr.lits_ptr litsPool) R,
    ← Std.ExtHashMap.sep_assoc] at hm
  exact hm

theorem opMem_of_lits {h : BitVec 64} {hdr : BVHdrState} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) hdr.lits_ptr litsPool ⋆
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆ R)) m) :
    (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m := by
  rw [Std.ExtHashMap.sep_comm] at hm
  rw [Std.ExtHashMap.sep_assoc,
    Std.ExtHashMap.sep_comm R (array (t := i32) hdr.lits_ptr litsPool),
    ← Std.ExtHashMap.sep_assoc] at hm
  exact hm

theorem opMem_of_lits_emp {h : BitVec 64} {hdr : BVHdrState} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) hdr.lits_ptr litsPool ⋆
      ((bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆ R) ⋆ Std.ExtHashMap.emp)) m) :
    (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m := by
  rw [Std.ExtHashMap.sep_emp] at hm
  exact opMem_of_lits hm

end

end OpsDivCpop

end LeanQbe.T.Examples.Bitblast.Proof
