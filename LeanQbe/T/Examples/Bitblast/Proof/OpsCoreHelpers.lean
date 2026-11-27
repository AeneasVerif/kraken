/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.Specs
public import LeanQbe.T.Examples.Bitblast.Src.OpsCore
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Bitblast.Proof.DriverHelpers
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas

/-!
# Canonical Specifications & Helpers for `Bitblast.Src.OpsCore`

Defines canonical `Spec`s for all 13 C0 functions in `Bitblast/Src/OpsCore.lean`
(`bv_slice_ok`, `bv_blast_extract`, `bv_blast_append`, `bv_blast_not`,
`bv_blast_bin_bitwise`, `bv_blast_and`, `bv_blast_or`, `bv_blast_xor`,
`bv_full_adder_carry`, `bv_blast_add`, `bv_blast_eq`, `bv_blast_ult`,
`bv_blast_get_lsb_d`), together with `Spec.XFree` lemmas, pure `BitVec`/AIG
correspondence lemmas, header/array memory helpers, and call wrappers.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Ref
open Std.Tactic.BVDecide

@[expose] public section

/-- Pure validity predicate matching `bv_slice_ok(h, off, w)`. -/
def sliceBoundsOk (hdr : BVHdrState) (off w : BitVec 32) : Bool :=
  decide (hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
    (0 < w.toNat → hdr.lits_ptr ≠ 0#64) ∧
    off.toNat ≤ hdr.lits_len.toNat ∧
    w.toNat ≤ hdr.lits_len.toNat - off.toNat)

/-- Pure validity predicate matching `bv_blast_extract(h, a_off, aw, start, len)` guards. -/
def extractValidOk (hdr : BVHdrState) (a_off aw len : BitVec 32) : Bool :=
  sliceBoundsOk hdr a_off aw && decide (0 < len.toNat → hdr.lits_ptr ≠ 0#64)

/-- Every AIG literal in `litsPool[off .. off + w)` references a node below `aigLen`. -/
def SliceAigWf (aigLen : Nat) (litsPool : List (BitVec 32)) (off w : Nat) : Prop :=
  ∀ j < w, (litsPool.getD (off + j) 0#32 >>> 1).toNat < aigLen

/-- Header frame preserving every `BVHdrState` field except `aig_len`, `lits_len`, and `oom`. -/
structure BVHdrState.BlastFrame (h1 h2 : BVHdrState) : Prop where
  work_base : h2.work_base = h1.work_base
  work_end : h2.work_end = h1.work_end
  prog_ptr : h2.prog_ptr = h1.prog_ptr
  aig_ptr : h2.aig_ptr = h1.aig_ptr
  ht_ptr : h2.ht_ptr = h1.ht_ptr
  atom_base_ptr : h2.atom_base_ptr = h1.atom_base_ptr
  slice_off_ptr : h2.slice_off_ptr = h1.slice_off_ptr
  lits_ptr : h2.lits_ptr = h1.lits_ptr
  marks_ptr : h2.marks_ptr = h1.marks_ptr
  dimacs_start : h2.dimacs_start = h1.dimacs_start
  n_vars : h2.n_vars = h1.n_vars
  n_nodes : h2.n_nodes = h1.n_nodes
  n_cwords : h2.n_cwords = h1.n_cwords
  root_node : h2.root_node = h1.root_node
  num_atoms : h2.num_atoms = h1.num_atoms
  aig_cap : h2.aig_cap = h1.aig_cap
  ht_mask : h2.ht_mask = h1.ht_mask
  lits_cap : h2.lits_cap = h1.lits_cap
  dimacs_len : h2.dimacs_len = h1.dimacs_len

/-- Opcode semantics for `bv_blast_bin_bitwise`. -/
def bitwiseOpFn (op : BitVec 32) : Bool → Bool → Bool :=
  if op = 3#32 then (· && ·) else if op = 4#32 then (· || ·) else (· ^^ ·)

/-- Per-bit AIG gate upper bound for `bv_blast_bin_bitwise`. -/
def bitwiseUnitGates (op : BitVec 32) : Nat :=
  if op = 5#32 then 3 else 1

/-- Valid opcode check for `bv_blast_bin_bitwise` (`AND`, `OR`, `XOR`). -/
def bitwiseOpValid (op : BitVec 32) : Bool :=
  decide (op = 3#32 ∨ op = 4#32 ∨ op = 5#32)

/-- Canonical spec for `bv_slice_ok(h, off, w)`. -/
def bvSliceOkSpec : Spec [i64, i32, i32] [Ty.bool] :=
  fun (h, off, w, ⟨⟩) m Q _X =>
    ∃ hdr R,
      (bvHdrMem h hdr ⋆ R) m ∧
      Q (sliceBoundsOk hdr off w, ⟨⟩) m

/-- Canonical spec for `bv_blast_extract(h, a_off, aw, start, len)`. -/
def bvBlastExtractSpec : Spec [i64, i32, i32, i32, i32] [i32] :=
  fun (h, a_off, aw, start, len, ⟨⟩) m Q _X =>
    ∃ hdr litsPool R,
      (bvHdrMem h hdr ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m ∧
      hdr.lits_cap.toNat ≤ litsPool.length ∧
      ∀ (ret : BitVec 32) (hdr' : BVHdrState) (litsPool' : List (BitVec 32)) (m' : Mem 64),
        hdr.BlastFrame hdr' →
        hdr'.aig_len = hdr.aig_len →
        litsPool'.length = litsPool.length →
        (∀ i < hdr.lits_len.toNat, litsPool'.getD i 0#32 = litsPool.getD i 0#32) →
        (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
        (hdr.oom = 0#32 → extractValidOk hdr a_off aw len = true →
          len.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat → hdr'.oom = 0#32) →
        (hdr'.oom = 0#32 →
          hdr.oom = 0#32 ∧ extractValidOk hdr a_off aw len = true ∧
          len.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat ∧
          ret = hdr.lits_len ∧ hdr'.lits_len = hdr.lits_len + len ∧
          ∀ j < len.toNat, litsPool'.getD (ret.toNat + j) 0#32 =
            if start.toNat + j < aw.toNat then
              litsPool.getD (a_off.toNat + (start.toNat + j)) 0#32
            else 0#32) →
        (hdr'.oom ≠ 0#32 → hdr'.lits_len = hdr.lits_len ∧ litsPool' = litsPool ∧
          ret = 0xFFFFFFFF#32) →
        (bvHdrMem h hdr' ⋆ array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
        Q (ret, ⟨⟩) m'

/-- Canonical spec for `bv_blast_append(h, lhs_off, lw, rhs_off, rw)`. -/
def bvBlastAppendSpec : Spec [i64, i32, i32, i32, i32] [i32] :=
  fun (h, lhs_off, lw, rhs_off, rw, ⟨⟩) m Q _X =>
    ∃ hdr litsPool R,
      (bvHdrMem h hdr ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m ∧
      hdr.lits_cap.toNat ≤ litsPool.length ∧
      ∀ (ret : BitVec 32) (hdr' : BVHdrState) (litsPool' : List (BitVec 32)) (m' : Mem 64),
        hdr.BlastFrame hdr' →
        hdr'.aig_len = hdr.aig_len →
        litsPool'.length = litsPool.length →
        (∀ i < hdr.lits_len.toNat, litsPool'.getD i 0#32 = litsPool.getD i 0#32) →
        (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
        (hdr.oom = 0#32 → sliceBoundsOk hdr lhs_off lw = true →
          sliceBoundsOk hdr rhs_off rw = true →
          lw.toNat + rw.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat → hdr'.oom = 0#32) →
        (hdr'.oom = 0#32 →
          hdr.oom = 0#32 ∧ sliceBoundsOk hdr lhs_off lw = true ∧
          sliceBoundsOk hdr rhs_off rw = true ∧
          lw.toNat + rw.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat ∧
          ret = hdr.lits_len ∧ hdr'.lits_len = hdr.lits_len + (lw + rw) ∧
          (lw + rw).toNat = lw.toNat + rw.toNat ∧
          (∀ j < rw.toNat,
            litsPool'.getD (ret.toNat + j) 0#32 = litsPool.getD (rhs_off.toNat + j) 0#32) ∧
          (∀ j < lw.toNat,
            litsPool'.getD (ret.toNat + rw.toNat + j) 0#32 =
              litsPool.getD (lhs_off.toNat + j) 0#32)) →
        (hdr'.oom ≠ 0#32 → hdr'.lits_len = hdr.lits_len ∧ litsPool' = litsPool ∧
          ret = 0xFFFFFFFF#32) →
        (bvHdrMem h hdr' ⋆ array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
        Q (ret, ⟨⟩) m'

/-- Canonical spec for `bv_blast_not(h, a_off, w)`. -/
def bvBlastNotSpec : Spec [i64, i32, i32] [i32] :=
  fun (h, a_off, w, ⟨⟩) m Q _X =>
    ∃ hdr litsPool R,
      (bvHdrMem h hdr ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m ∧
      hdr.lits_cap.toNat ≤ litsPool.length ∧
      ∀ (ret : BitVec 32) (hdr' : BVHdrState) (litsPool' : List (BitVec 32)) (m' : Mem 64),
        hdr.BlastFrame hdr' →
        hdr'.aig_len = hdr.aig_len →
        litsPool'.length = litsPool.length →
        (∀ i < hdr.lits_len.toNat, litsPool'.getD i 0#32 = litsPool.getD i 0#32) →
        (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
        (hdr.oom = 0#32 → sliceBoundsOk hdr a_off w = true →
          w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat → hdr'.oom = 0#32) →
        (hdr'.oom = 0#32 →
          hdr.oom = 0#32 ∧ sliceBoundsOk hdr a_off w = true ∧
          w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat ∧
          ret = hdr.lits_len ∧ hdr'.lits_len = hdr.lits_len + w ∧
          ∀ j < w.toNat, litsPool'.getD (ret.toNat + j) 0#32 =
            litsPool.getD (a_off.toNat + j) 0#32 ^^^ 1#32) →
        (hdr'.oom ≠ 0#32 → hdr'.lits_len = hdr.lits_len ∧ litsPool' = litsPool ∧
          ret = 0xFFFFFFFF#32) →
        (bvHdrMem h hdr' ⋆ array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
        Q (ret, ⟨⟩) m'

/-- Shared spec shape for `bv_blast_and`, `bv_blast_or`, `bv_blast_xor`. -/
def bvBlastBitwiseSpec (opFn : Bool → Bool → Bool) (unitGates : Nat) :
    Spec [i64, i32, i32, i32] [i32] :=
  fun (h, a_off, b_off, w, ⟨⟩) m Q _X =>
    ∃ hdr g aigWords htSlots litsPool R,
      AigInv hdr g aigWords htSlots ∧
      hdr.lits_cap.toNat ≤ litsPool.length ∧
      (hdr.oom = 0#32 → sliceBoundsOk hdr a_off w = true → sliceBoundsOk hdr b_off w = true →
        SliceAigWf hdr.aig_len.toNat litsPool a_off.toNat w.toNat ∧
        SliceAigWf hdr.aig_len.toNat litsPool b_off.toNat w.toNat) ∧
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m ∧
      ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Ref.Aig) (aigWords' : List (BitVec 64))
        (htSlots' litsPool' : List (BitVec 32)) (m' : Mem 64),
        hdr.BlastFrame hdr' →
        g ≤ g' →
        g'.nodes.size ≤ g.nodes.size + unitGates * w.toNat →
        AigInv hdr' g' aigWords' htSlots' →
        litsPool'.length = litsPool.length →
        (∀ i < hdr.lits_len.toNat, litsPool'.getD i 0#32 = litsPool.getD i 0#32) →
        hdr.lits_len.toNat ≤ hdr'.lits_len.toNat →
        hdr'.lits_len.toNat ≤ hdr.lits_len.toNat + w.toNat →
        (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
        (hdr.oom = 0#32 → sliceBoundsOk hdr a_off w = true → sliceBoundsOk hdr b_off w = true →
          w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat →
          g.A + 1 + g.nodes.size + unitGates * w.toNat ≤ hdr.aig_cap.toNat →
          g.nodes.size + unitGates * w.toNat ≤ bvMaxGates → hdr'.oom = 0#32) →
        (hdr'.oom = 0#32 →
          hdr.oom = 0#32 ∧ sliceBoundsOk hdr a_off w = true ∧ sliceBoundsOk hdr b_off w = true ∧
          w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat ∧
          ret = hdr.lits_len ∧ hdr'.lits_len = hdr.lits_len + w ∧
          SliceAigWf hdr'.aig_len.toNat litsPool' ret.toNat w.toNat ∧
          ∀ j < w.toNat, ∀ ρ : Nat → Bool,
            g'.evalLit ρ (UInt32.ofBitVec (litsPool'.getD (ret.toNat + j) 0#32)) =
              opFn (g.evalLit ρ (UInt32.ofBitVec (litsPool.getD (a_off.toNat + j) 0#32)))
                (g.evalLit ρ (UInt32.ofBitVec (litsPool.getD (b_off.toNat + j) 0#32)))) →
        (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
        (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
          array (t := i32) hdr'.ht_ptr htSlots' ⋆ array (t := i32) hdr'.lits_ptr litsPool' ⋆
          R) m' →
        Q (ret, ⟨⟩) m'

/-- Canonical spec for `bv_blast_bin_bitwise(h, a_off, b_off, w, op)`. -/
def bvBlastBinBitwiseSpec : Spec [i64, i32, i32, i32, i32] [i32] :=
  fun (h, a_off, b_off, w, op, ⟨⟩) m Q _X =>
    ∃ hdr g aigWords htSlots litsPool R,
      AigInv hdr g aigWords htSlots ∧
      hdr.lits_cap.toNat ≤ litsPool.length ∧
      (hdr.oom = 0#32 → bitwiseOpValid op = true →
        sliceBoundsOk hdr a_off w = true → sliceBoundsOk hdr b_off w = true →
        SliceAigWf hdr.aig_len.toNat litsPool a_off.toNat w.toNat ∧
        SliceAigWf hdr.aig_len.toNat litsPool b_off.toNat w.toNat) ∧
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m ∧
      ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Ref.Aig) (aigWords' : List (BitVec 64))
        (htSlots' litsPool' : List (BitVec 32)) (m' : Mem 64),
        hdr.BlastFrame hdr' →
        g ≤ g' →
        g'.nodes.size ≤ g.nodes.size + bitwiseUnitGates op * w.toNat →
        AigInv hdr' g' aigWords' htSlots' →
        litsPool'.length = litsPool.length →
        (∀ i < hdr.lits_len.toNat, litsPool'.getD i 0#32 = litsPool.getD i 0#32) →
        hdr.lits_len.toNat ≤ hdr'.lits_len.toNat →
        hdr'.lits_len.toNat ≤ hdr.lits_len.toNat + w.toNat →
        (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
        (hdr.oom = 0#32 → bitwiseOpValid op = true →
          sliceBoundsOk hdr a_off w = true → sliceBoundsOk hdr b_off w = true →
          w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat →
          g.A + 1 + g.nodes.size + bitwiseUnitGates op * w.toNat ≤ hdr.aig_cap.toNat →
          g.nodes.size + bitwiseUnitGates op * w.toNat ≤ bvMaxGates → hdr'.oom = 0#32) →
        (hdr'.oom = 0#32 →
          hdr.oom = 0#32 ∧ bitwiseOpValid op = true ∧
          sliceBoundsOk hdr a_off w = true ∧ sliceBoundsOk hdr b_off w = true ∧
          w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat ∧
          ret = hdr.lits_len ∧ hdr'.lits_len = hdr.lits_len + w ∧
          SliceAigWf hdr'.aig_len.toNat litsPool' ret.toNat w.toNat ∧
          ∀ j < w.toNat, ∀ ρ : Nat → Bool,
            g'.evalLit ρ (UInt32.ofBitVec (litsPool'.getD (ret.toNat + j) 0#32)) =
              bitwiseOpFn op
                (g.evalLit ρ (UInt32.ofBitVec (litsPool.getD (a_off.toNat + j) 0#32)))
                (g.evalLit ρ (UInt32.ofBitVec (litsPool.getD (b_off.toNat + j) 0#32)))) →
        (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
        (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
          array (t := i32) hdr'.ht_ptr htSlots' ⋆ array (t := i32) hdr'.lits_ptr litsPool' ⋆
          R) m' →
        Q (ret, ⟨⟩) m'

/-- Canonical spec for `bv_blast_and(h, a_off, b_off, w)`. -/
def bvBlastAndSpec : Spec [i64, i32, i32, i32] [i32] := bvBlastBitwiseSpec (· && ·) 1

/-- Canonical spec for `bv_blast_or(h, a_off, b_off, w)`. -/
def bvBlastOrSpec : Spec [i64, i32, i32, i32] [i32] := bvBlastBitwiseSpec (· || ·) 1

/-- Canonical spec for `bv_blast_xor(h, a_off, b_off, w)`. -/
def bvBlastXorSpec : Spec [i64, i32, i32, i32] [i32] := bvBlastBitwiseSpec (· ^^ ·) 3

/-- Canonical spec for `bv_full_adder_carry(h, a, b, cin)`. -/
def bvFullAdderCarrySpec : Spec [i64, i32, i32, i32] [i32] :=
  fun (h, a, b, cin, ⟨⟩) m Q _X =>
    ∃ hdr g aigWords htSlots R,
      AigInv hdr g aigWords htSlots ∧
      (hdr.oom = 0#32 → (a >>> 1).toNat < hdr.aig_len.toNat ∧
        (b >>> 1).toNat < hdr.aig_len.toNat ∧ (cin >>> 1).toNat < hdr.aig_len.toNat) ∧
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆ R) m ∧
      ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Ref.Aig) (aigWords' : List (BitVec 64))
        (htSlots' : List (BitVec 32)) (m' : Mem 64),
        hdr.AigFrame hdr' →
        g ≤ g' →
        g'.nodes.size ≤ g.nodes.size + 6 →
        AigInv hdr' g' aigWords' htSlots' →
        (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
        (hdr.oom = 0#32 → g.A + 1 + g.nodes.size + 6 ≤ hdr.aig_cap.toNat →
          g.nodes.size + 6 ≤ bvMaxGates → hdr'.oom = 0#32) →
        (hdr'.oom = 0#32 → hdr.oom = 0#32 ∧ (ret >>> 1).toNat < hdr'.aig_len.toNat ∧
          ∀ ρ : Nat → Bool,
            g'.evalLit ρ (UInt32.ofBitVec ret) =
              (g.evalLit ρ (UInt32.ofBitVec a)).atLeastTwo
                (g.evalLit ρ (UInt32.ofBitVec b)) (g.evalLit ρ (UInt32.ofBitVec cin))) →
        (hdr'.oom ≠ 0#32 → ret = 0#32) →
        (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
          array (t := i32) hdr'.ht_ptr htSlots' ⋆ R) m' →
        Q (ret, ⟨⟩) m'

/-- Canonical spec for `bv_blast_add(h, a_off, b_off, w)`. -/
def bvBlastAddSpec : Spec [i64, i32, i32, i32] [i32] :=
  fun (h, a_off, b_off, w, ⟨⟩) m Q _X =>
    ∃ hdr g aigWords htSlots litsPool R,
      AigInv hdr g aigWords htSlots ∧
      hdr.lits_cap.toNat ≤ litsPool.length ∧
      (hdr.oom = 0#32 → sliceBoundsOk hdr a_off w = true → sliceBoundsOk hdr b_off w = true →
        SliceAigWf hdr.aig_len.toNat litsPool a_off.toNat w.toNat ∧
        SliceAigWf hdr.aig_len.toNat litsPool b_off.toNat w.toNat) ∧
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m ∧
      ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Ref.Aig) (aigWords' : List (BitVec 64))
        (htSlots' litsPool' : List (BitVec 32)) (m' : Mem 64),
        hdr.BlastFrame hdr' →
        g ≤ g' →
        g'.nodes.size ≤ g.nodes.size + 12 * w.toNat →
        AigInv hdr' g' aigWords' htSlots' →
        litsPool'.length = litsPool.length →
        (∀ i < hdr.lits_len.toNat, litsPool'.getD i 0#32 = litsPool.getD i 0#32) →
        hdr.lits_len.toNat ≤ hdr'.lits_len.toNat →
        hdr'.lits_len.toNat ≤ hdr.lits_len.toNat + w.toNat →
        (hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
          hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat) →
        (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
        (hdr.oom = 0#32 → sliceBoundsOk hdr a_off w = true → sliceBoundsOk hdr b_off w = true →
          w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat →
          g.A + 1 + g.nodes.size + 12 * w.toNat ≤ hdr.aig_cap.toNat →
          g.nodes.size + 12 * w.toNat ≤ bvMaxGates → hdr'.oom = 0#32) →
        (hdr'.oom = 0#32 →
          hdr.oom = 0#32 ∧ sliceBoundsOk hdr a_off w = true ∧ sliceBoundsOk hdr b_off w = true ∧
          w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat ∧
          ret = hdr.lits_len ∧ hdr'.lits_len = hdr.lits_len + w ∧
          SliceAigWf hdr'.aig_len.toNat litsPool' ret.toNat w.toNat ∧
          ∀ (ρ : Nat → Bool) (vA vB : BitVec w.toNat),
            SliceDenotes g ρ (litsSlice litsPool a_off.toNat w.toNat) vA →
            SliceDenotes g ρ (litsSlice litsPool b_off.toNat w.toNat) vB →
            SliceDenotes g' ρ (litsSlice litsPool' ret.toNat w.toNat) (vA + vB)) →
        (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
        (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
          array (t := i32) hdr'.ht_ptr htSlots' ⋆ array (t := i32) hdr'.lits_ptr litsPool' ⋆
          R) m' →
        Q (ret, ⟨⟩) m'

/-- Canonical spec for `bv_blast_eq(h, a_off, b_off, w)`. -/
def bvBlastEqSpec : Spec [i64, i32, i32, i32] [i32] :=
  fun (h, a_off, b_off, w, ⟨⟩) m Q _X =>
    ∃ hdr g aigWords htSlots litsPool R,
      AigInv hdr g aigWords htSlots ∧
      hdr.lits_len.toNat ≤ litsPool.length ∧
      (hdr.oom = 0#32 → sliceBoundsOk hdr a_off w = true → sliceBoundsOk hdr b_off w = true →
        SliceAigWf hdr.aig_len.toNat litsPool a_off.toNat w.toNat ∧
        SliceAigWf hdr.aig_len.toNat litsPool b_off.toNat w.toNat) ∧
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m ∧
      ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Ref.Aig) (aigWords' : List (BitVec 64))
        (htSlots' : List (BitVec 32)) (m' : Mem 64),
        hdr.AigFrame hdr' →
        g ≤ g' →
        g'.nodes.size ≤ g.nodes.size + 4 * w.toNat →
        AigInv hdr' g' aigWords' htSlots' →
        (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
        (hdr.oom = 0#32 → sliceBoundsOk hdr a_off w = true → sliceBoundsOk hdr b_off w = true →
          g.A + 1 + g.nodes.size + 4 * w.toNat ≤ hdr.aig_cap.toNat →
          g.nodes.size + 4 * w.toNat ≤ bvMaxGates → hdr'.oom = 0#32) →
        (hdr'.oom = 0#32 →
          hdr.oom = 0#32 ∧ sliceBoundsOk hdr a_off w = true ∧ sliceBoundsOk hdr b_off w = true ∧
          (ret >>> 1).toNat < hdr'.aig_len.toNat ∧
          ∀ ρ : Nat → Bool,
            g'.evalLit ρ (UInt32.ofBitVec ret) =
              decide (∀ j < w.toNat,
                g.evalLit ρ (UInt32.ofBitVec (litsPool.getD (a_off.toNat + j) 0#32)) =
                  g.evalLit ρ (UInt32.ofBitVec (litsPool.getD (b_off.toNat + j) 0#32)))) →
        (hdr'.oom ≠ 0#32 → ret = 0#32) →
        (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
          array (t := i32) hdr'.ht_ptr htSlots' ⋆ array (t := i32) hdr'.lits_ptr litsPool ⋆ R) m' →
        Q (ret, ⟨⟩) m'

/-- Canonical spec for `bv_blast_ult(h, a_off, b_off, w)`. -/
def bvBlastUltSpec : Spec [i64, i32, i32, i32] [i32] :=
  fun (h, a_off, b_off, w, ⟨⟩) m Q _X =>
    ∃ hdr g aigWords htSlots litsPool R,
      AigInv hdr g aigWords htSlots ∧
      hdr.lits_len.toNat ≤ litsPool.length ∧
      (hdr.oom = 0#32 → sliceBoundsOk hdr a_off w = true → sliceBoundsOk hdr b_off w = true →
        SliceAigWf hdr.aig_len.toNat litsPool a_off.toNat w.toNat ∧
        SliceAigWf hdr.aig_len.toNat litsPool b_off.toNat w.toNat) ∧
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m ∧
      ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Ref.Aig) (aigWords' : List (BitVec 64))
        (htSlots' : List (BitVec 32)) (m' : Mem 64),
        hdr.AigFrame hdr' →
        g ≤ g' →
        g'.nodes.size ≤ g.nodes.size + 6 * w.toNat →
        AigInv hdr' g' aigWords' htSlots' →
        (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
        (hdr.oom = 0#32 → sliceBoundsOk hdr a_off w = true → sliceBoundsOk hdr b_off w = true →
          g.A + 1 + g.nodes.size + 6 * w.toNat ≤ hdr.aig_cap.toNat →
          g.nodes.size + 6 * w.toNat ≤ bvMaxGates → hdr'.oom = 0#32) →
        (hdr'.oom = 0#32 →
          hdr.oom = 0#32 ∧ sliceBoundsOk hdr a_off w = true ∧ sliceBoundsOk hdr b_off w = true ∧
          (ret >>> 1).toNat < hdr'.aig_len.toNat ∧
          ∀ (ρ : Nat → Bool) (vA vB : BitVec w.toNat),
            SliceDenotes g ρ (litsSlice litsPool a_off.toNat w.toNat) vA →
            SliceDenotes g ρ (litsSlice litsPool b_off.toNat w.toNat) vB →
            g'.evalLit ρ (UInt32.ofBitVec ret) = vA.ult vB) →
        (hdr'.oom ≠ 0#32 → ret = 0#32) →
        (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
          array (t := i32) hdr'.ht_ptr htSlots' ⋆ array (t := i32) hdr'.lits_ptr litsPool ⋆ R) m' →
        Q (ret, ⟨⟩) m'

/-- Canonical spec for `bv_blast_get_lsb_d(h, a_off, aw, idx)`. -/
def bvBlastGetLsbDSpec : Spec [i64, i32, i32, i32] [i32] :=
  fun (h, a_off, aw, idx, ⟨⟩) m Q _X =>
    ∃ hdr litsPool R,
      (bvHdrMem h hdr ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m ∧
      hdr.lits_len.toNat ≤ litsPool.length ∧
      ∀ (ret : BitVec 32) (hdr' : BVHdrState) (m' : Mem 64),
        hdr.AigFrame hdr' →
        hdr'.aig_len = hdr.aig_len →
        (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
        (hdr.oom = 0#32 → sliceBoundsOk hdr a_off aw = true → hdr'.oom = 0#32) →
        (hdr'.oom = 0#32 →
          hdr.oom = 0#32 ∧ sliceBoundsOk hdr a_off aw = true ∧
          ret = if idx < aw then litsPool.getD (a_off.toNat + idx.toNat) 0#32 else 0#32) →
        (hdr'.oom ≠ 0#32 → ret = 0#32) →
        (bvHdrMem h hdr' ⋆ array (t := i32) hdr'.lits_ptr litsPool ⋆ R) m' →
        Q (ret, ⟨⟩) m'

end

public section

/-! ## `Spec.XFree` Lemmas -/

theorem bvSliceOkSpec_xfree : bvSliceOkSpec.XFree := by xfree
theorem bvBlastExtractSpec_xfree : bvBlastExtractSpec.XFree := by xfree
theorem bvBlastAppendSpec_xfree : bvBlastAppendSpec.XFree := by xfree
theorem bvBlastNotSpec_xfree : bvBlastNotSpec.XFree := by xfree
theorem bvBlastBitwiseSpec_xfree {opFn : Bool → Bool → Bool} {u : Nat} :
    (bvBlastBitwiseSpec opFn u).XFree := by xfree
theorem bvBlastBinBitwiseSpec_xfree : bvBlastBinBitwiseSpec.XFree := by xfree
theorem bvBlastAndSpec_xfree : bvBlastAndSpec.XFree := bvBlastBitwiseSpec_xfree
theorem bvBlastOrSpec_xfree : bvBlastOrSpec.XFree := bvBlastBitwiseSpec_xfree
theorem bvBlastXorSpec_xfree : bvBlastXorSpec.XFree := bvBlastBitwiseSpec_xfree
theorem bvFullAdderCarrySpec_xfree : bvFullAdderCarrySpec.XFree := by xfree
theorem bvBlastAddSpec_xfree : bvBlastAddSpec.XFree := by xfree
theorem bvBlastEqSpec_xfree : bvBlastEqSpec.XFree := by xfree
theorem bvBlastUltSpec_xfree : bvBlastUltSpec.XFree := by xfree
theorem bvBlastGetLsbDSpec_xfree : bvBlastGetLsbDSpec.XFree := by xfree

/-! ## Frame & Invariant Preservation Lemmas -/

theorem BVHdrState.BlastFrame.refl (h : BVHdrState) : h.BlastFrame h :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem BVHdrState.BlastFrame.trans {h1 h2 h3 : BVHdrState}
    (h12 : h1.BlastFrame h2) (h23 : h2.BlastFrame h3) : h1.BlastFrame h3 :=
  { work_base := h23.work_base.trans h12.work_base
    work_end := h23.work_end.trans h12.work_end
    prog_ptr := h23.prog_ptr.trans h12.prog_ptr
    aig_ptr := h23.aig_ptr.trans h12.aig_ptr
    ht_ptr := h23.ht_ptr.trans h12.ht_ptr
    atom_base_ptr := h23.atom_base_ptr.trans h12.atom_base_ptr
    slice_off_ptr := h23.slice_off_ptr.trans h12.slice_off_ptr
    lits_ptr := h23.lits_ptr.trans h12.lits_ptr
    marks_ptr := h23.marks_ptr.trans h12.marks_ptr
    dimacs_start := h23.dimacs_start.trans h12.dimacs_start
    n_vars := h23.n_vars.trans h12.n_vars
    n_nodes := h23.n_nodes.trans h12.n_nodes
    n_cwords := h23.n_cwords.trans h12.n_cwords
    root_node := h23.root_node.trans h12.root_node
    num_atoms := h23.num_atoms.trans h12.num_atoms
    aig_cap := h23.aig_cap.trans h12.aig_cap
    ht_mask := h23.ht_mask.trans h12.ht_mask
    lits_cap := h23.lits_cap.trans h12.lits_cap
    dimacs_len := h23.dimacs_len.trans h12.dimacs_len }

theorem BVHdrState.AigFrame.toBlastFrame {h1 h2 : BVHdrState}
    (h : h1.AigFrame h2) : h1.BlastFrame h2 :=
  { work_base := h.work_base, work_end := h.work_end, prog_ptr := h.prog_ptr
    aig_ptr := h.aig_ptr, ht_ptr := h.ht_ptr, atom_base_ptr := h.atom_base_ptr
    slice_off_ptr := h.slice_off_ptr, lits_ptr := h.lits_ptr, marks_ptr := h.marks_ptr
    dimacs_start := h.dimacs_start, n_vars := h.n_vars, n_nodes := h.n_nodes
    n_cwords := h.n_cwords, root_node := h.root_node, num_atoms := h.num_atoms
    aig_cap := h.aig_cap, ht_mask := h.ht_mask, lits_cap := h.lits_cap
    dimacs_len := h.dimacs_len }

theorem BVHdrState.BlastFrame.toAigFrame {h1 h2 : BVHdrState}
    (h : h1.BlastFrame h2) (hlen : h2.lits_len = h1.lits_len) : h1.AigFrame h2 :=
  { work_base := h.work_base, work_end := h.work_end, prog_ptr := h.prog_ptr
    aig_ptr := h.aig_ptr, ht_ptr := h.ht_ptr, atom_base_ptr := h.atom_base_ptr
    slice_off_ptr := h.slice_off_ptr, lits_ptr := h.lits_ptr, marks_ptr := h.marks_ptr
    dimacs_start := h.dimacs_start, n_vars := h.n_vars, n_nodes := h.n_nodes
    n_cwords := h.n_cwords, root_node := h.root_node, num_atoms := h.num_atoms
    aig_cap := h.aig_cap, ht_mask := h.ht_mask, lits_len := hlen,
    lits_cap := h.lits_cap, dimacs_len := h.dimacs_len }

theorem aigInv_zero_lt_aigLen {hdr : BVHdrState} {g : Ref.Aig}
    {aigWords : List (BitVec 64)} {htSlots : List (BitVec 32)}
    (hinv : AigInv hdr g aigWords htSlots) :
    0 < hdr.aig_len.toNat := by
  have := hinv.aig_len_eq
  omega

theorem aigInv_false_lit_bound {hdr : BVHdrState} {g : Ref.Aig}
    {aigWords : List (BitVec 64)} {htSlots : List (BitVec 32)}
    (hinv : AigInv hdr g aigWords htSlots) :
    (0#32 >>> 1).toNat < hdr.aig_len.toNat := by
  have hlt := aigInv_zero_lt_aigLen hinv
  simpa using hlt

theorem aigInv_true_lit_bound {hdr : BVHdrState} {g : Ref.Aig}
    {aigWords : List (BitVec 64)} {htSlots : List (BitVec 32)}
    (hinv : AigInv hdr g aigWords htSlots) :
    (1#32 >>> 1).toNat < hdr.aig_len.toNat := by
  have hlt := aigInv_zero_lt_aigLen hinv
  simpa using hlt

theorem aigInv_aigLen_mono {hdr1 hdr2 : BVHdrState} {g1 g2 : Ref.Aig}
    {a1 a2 : List (BitVec 64)} {ht1 ht2 : List (BitVec 32)}
    (hinv1 : AigInv hdr1 g1 a1 ht1) (hinv2 : AigInv hdr2 g2 a2 ht2) (hle : g1 ≤ g2) :
    hdr1.aig_len.toNat ≤ hdr2.aig_len.toNat := by
  have hA : g1.A = g2.A := hle.1
  have hsz : g1.nodes.size ≤ g2.nodes.size := hle.2.1
  have := hinv1.aig_len_eq
  have := hinv2.aig_len_eq
  omega

theorem sliceAigWf_mono {aig1 aig2 : Nat} {xs : List (BitVec 32)} {off w : Nat}
    (hle : aig1 ≤ aig2) (h : SliceAigWf aig1 xs off w) : SliceAigWf aig2 xs off w :=
  fun j hj => Nat.lt_of_lt_of_le (h j hj) hle

theorem sliceBoundsOk_sum {hdr : BVHdrState} {off w : BitVec 32}
    (hok : sliceBoundsOk hdr off w = true) :
    hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
    (0 < w.toNat → hdr.lits_ptr ≠ 0#64) ∧
    off.toNat + w.toNat ≤ hdr.lits_len.toNat := by
  simp only [sliceBoundsOk, decide_eq_true_eq] at hok
  rcases hok with ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h2, by omega⟩

theorem sliceBoundsOk_of_parts {hdr : BVHdrState} {off w : BitVec 32}
    (hcap : hdr.lits_len.toNat ≤ hdr.lits_cap.toNat)
    (hptr : 0 < w.toNat → hdr.lits_ptr ≠ 0#64)
    (hsum : off.toNat + w.toNat ≤ hdr.lits_len.toNat) :
    sliceBoundsOk hdr off w = true := by
  simp only [sliceBoundsOk, decide_eq_true_eq]
  exact ⟨hcap, hptr, by omega, by omega⟩

theorem evalLit_zero (g : Ref.Aig) (ρ : Nat → Bool) :
    g.evalLit ρ (UInt32.ofBitVec 0#32) = false :=
  Ref.Aig.evalLit_zero g ρ

theorem evalLit_one (g : Ref.Aig) (ρ : Nat → Bool) :
    g.evalLit ρ (UInt32.ofBitVec 1#32) = true :=
  Ref.Aig.evalLit_one g ρ

theorem sliceAigWf_evalLit_extend {g g' : Ref.Aig} {hdr : BVHdrState}
    {aigWords : List (BitVec 64)} {htSlots litsPool : List (BitVec 32)}
    {off w : Nat} (hinv : AigInv hdr g aigWords htSlots) (hle : g ≤ g')
    (hwf : SliceAigWf hdr.aig_len.toNat litsPool off w)
    (ρ : Nat → Bool) {j : Nat} (hj : j < w) :
    g'.evalLit ρ (UInt32.ofBitVec (litsPool.getD (off + j) 0#32)) =
      g.evalLit ρ (UInt32.ofBitVec (litsPool.getD (off + j) 0#32)) := by
  have hlt := hwf j hj
  rw [hinv.aig_len_eq] at hlt
  have hv : (UInt32.ofBitVec (litsPool.getD (off + j) 0#32)).toNat <
      2 * (g.A + 1 + g.nodes.size) := by
    have hs : (litsPool.getD (off + j) 0#32 >>> 1).toNat =
        (UInt32.ofBitVec (litsPool.getD (off + j) 0#32)).toNat / 2 := by
      simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  exact Ref.Aig.evalLit_extend hle hv

theorem evalLit_extend_of_lt {g g' : Ref.Aig} {hdr : BVHdrState}
    {aigWords : List (BitVec 64)} {htSlots : List (BitVec 32)} {l : BitVec 32}
    (hinv : AigInv hdr g aigWords htSlots) (hle : g ≤ g')
    (hlt : (l >>> 1).toNat < hdr.aig_len.toNat) (ρ : Nat → Bool) :
    g'.evalLit ρ (UInt32.ofBitVec l) = g.evalLit ρ (UInt32.ofBitVec l) := by
  rw [hinv.aig_len_eq] at hlt
  have hv : (UInt32.ofBitVec l).toNat < 2 * (g.A + 1 + g.nodes.size) := by
    have hs : (l >>> 1).toNat = (UInt32.ofBitVec l).toNat / 2 := by
      simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  exact Ref.Aig.evalLit_extend hle hv

theorem litsSlice_congr {xs ys : List (BitVec 32)} {off w : Nat}
    (hle_x : off + w ≤ xs.length) (hle_y : off + w ≤ ys.length)
    (heq : ∀ j < w, xs.getD (off + j) 0#32 = ys.getD (off + j) 0#32) :
    litsSlice xs off w = litsSlice ys off w := by
  apply List.ext_getElem
  · rw [litsSlice_length hle_x, litsSlice_length hle_y]
  · intro i hi1' hi2'
    have hi1 : i < w := by simpa [litsSlice_length hle_x] using hi1'
    have hx := litsSlice_getD hle_x hi1
    have hy := litsSlice_getD hle_y hi1
    rw [list_getD_eq_getElem (litsSlice xs off w) 0 hi1',
      list_getD_eq_getElem (litsSlice ys off w) 0 hi2', hx, hy, heq i hi1]

theorem litsSlice_prefix_eq {xs ys : List (BitVec 32)} {lim off w : Nat}
    (hle_x : lim ≤ xs.length) (hle_y : lim ≤ ys.length)
    (hbound : off + w ≤ lim)
    (hpref : ∀ i < lim, ys.getD i 0#32 = xs.getD i 0#32) :
    litsSlice ys off w = litsSlice xs off w :=
  litsSlice_congr (by omega) (by omega) fun j hj => hpref (off + j) (by omega)

/-! ## Pure `BitVec` & `BVExpr` / `BVPred` Correspondence Lemmas -/

theorem sliceDenotes_extract_bits {g : Ref.Aig} {ρ : Nat → Bool}
    {xs ys : List (BitVec 32)} {aOff aw start len out : Nat} {v : BitVec aw}
    (hle_x : aOff + aw ≤ xs.length) (hle_y : out + len ≤ ys.length)
    (hden : SliceDenotes g ρ (litsSlice xs aOff aw) v)
    (hbits : ∀ j < len, ys.getD (out + j) 0#32 =
      if start + j < aw then xs.getD (aOff + (start + j)) 0#32 else 0#32) :
    SliceDenotes g ρ (litsSlice ys out len) (BitVec.extractLsb' start len v) := by
  rw [sliceDenotes_iff hle_y]
  rw [sliceDenotes_iff hle_x] at hden
  intro j hj
  rw [hbits j hj, BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and]
  split
  · next hlt => exact hden (start + j) hlt
  · next hge =>
    have hge' : aw ≤ start + j := by omega
    rw [BitVec.getLsbD_of_ge v (start + j) hge']
    exact evalLit_zero g ρ

theorem sliceDenotes_extract_eval {g : Ref.Aig} {assign : BVExpr.Assignment} {ρ : Nat → Bool}
    {aw : Nat} {e : BVExpr aw} {xs ys : List (BitVec 32)} {aOff start len out : Nat}
    (hle_x : aOff + aw ≤ xs.length) (hle_y : out + len ≤ ys.length)
    (hden : SliceDenotes g ρ (litsSlice xs aOff aw) (e.eval assign))
    (hbits : ∀ j < len, ys.getD (out + j) 0#32 =
      if start + j < aw then xs.getD (aOff + (start + j)) 0#32 else 0#32) :
    SliceDenotes g ρ (litsSlice ys out len) ((BVExpr.extract start len e).eval assign) := by
  simpa [BVExpr.eval_extract] using sliceDenotes_extract_bits hle_x hle_y hden hbits

theorem sliceDenotes_append_bits {g : Ref.Aig} {ρ : Nat → Bool}
    {xs ys : List (BitVec 32)} {lOff lw rOff rw out : Nat}
    {vL : BitVec lw} {vR : BitVec rw}
    (hle_l : lOff + lw ≤ xs.length) (hle_r : rOff + rw ≤ xs.length)
    (hle_y : out + (lw + rw) ≤ ys.length)
    (hdenL : SliceDenotes g ρ (litsSlice xs lOff lw) vL)
    (hdenR : SliceDenotes g ρ (litsSlice xs rOff rw) vR)
    (hbitsR : ∀ j < rw, ys.getD (out + j) 0#32 = xs.getD (rOff + j) 0#32)
    (hbitsL : ∀ j < lw, ys.getD (out + rw + j) 0#32 = xs.getD (lOff + j) 0#32) :
    SliceDenotes g ρ (litsSlice ys out (lw + rw)) (vL ++ vR) := by
  rw [sliceDenotes_iff hle_y]
  rw [sliceDenotes_iff hle_l] at hdenL
  rw [sliceDenotes_iff hle_r] at hdenR
  intro j hj
  rw [BitVec.getLsbD_append]
  split
  · next hlt => rw [hbitsR j hlt]; exact hdenR j hlt
  · next hge =>
    have hsub : j - rw < lw := by omega
    have hadd : out + rw + (j - rw) = out + j := by omega
    have hL := hbitsL (j - rw) hsub
    rw [hadd] at hL
    rw [hL]
    exact hdenL (j - rw) hsub

theorem sliceDenotes_not_bits {g : Ref.Aig} {ρ : Nat → Bool}
    {xs ys : List (BitVec 32)} {aOff w out : Nat} {v : BitVec w}
    (hle_x : aOff + w ≤ xs.length) (hle_y : out + w ≤ ys.length)
    (hden : SliceDenotes g ρ (litsSlice xs aOff w) v)
    (hbits : ∀ j < w, ys.getD (out + j) 0#32 = xs.getD (aOff + j) 0#32 ^^^ 1#32) :
    SliceDenotes g ρ (litsSlice ys out w) (~~~v) := by
  rw [sliceDenotes_iff hle_y]
  rw [sliceDenotes_iff hle_x] at hden
  intro j hj
  rw [hbits j hj, evalLit_xor1, hden j hj, BitVec.getLsbD_not, decide_eq_true hj, Bool.true_and]

theorem sliceDenotes_binop_bits {g g' : Ref.Aig} {ρ : Nat → Bool}
    {xs ys : List (BitVec 32)} {aOff bOff w out : Nat}
    {vA vB vRes : BitVec w} {opFn : Bool → Bool → Bool}
    (hle_a : aOff + w ≤ xs.length) (hle_b : bOff + w ≤ xs.length)
    (hle_y : out + w ≤ ys.length)
    (hdenA : SliceDenotes g ρ (litsSlice xs aOff w) vA)
    (hdenB : SliceDenotes g ρ (litsSlice xs bOff w) vB)
    (hres : ∀ j < w, vRes.getLsbD j = opFn (vA.getLsbD j) (vB.getLsbD j))
    (hbits : ∀ j < w, g'.evalLit ρ (UInt32.ofBitVec (ys.getD (out + j) 0#32)) =
      opFn (g.evalLit ρ (UInt32.ofBitVec (xs.getD (aOff + j) 0#32)))
        (g.evalLit ρ (UInt32.ofBitVec (xs.getD (bOff + j) 0#32)))) :
    SliceDenotes g' ρ (litsSlice ys out w) vRes := by
  rw [sliceDenotes_iff hle_y]
  rw [sliceDenotes_iff hle_a] at hdenA
  rw [sliceDenotes_iff hle_b] at hdenB
  intro j hj
  rw [hbits j hj, hdenA j hj, hdenB j hj, ← hres j hj]

theorem sliceDenotes_getLsbD {g : Ref.Aig} {ρ : Nat → Bool}
    {xs : List (BitVec 32)} {aOff aw idx : Nat} {v : BitVec aw}
    (hle : aOff + aw ≤ xs.length) (hden : SliceDenotes g ρ (litsSlice xs aOff aw) v) :
    g.evalLit ρ (UInt32.ofBitVec (if idx < aw then xs.getD (aOff + idx) 0#32 else 0#32)) =
      v.getLsbD idx := by
  rw [sliceDenotes_iff hle] at hden
  split
  · next hlt => exact hden idx hlt
  · next hge =>
    have hge' : aw ≤ idx := by omega
    rw [BitVec.getLsbD_of_ge v idx hge']
    exact evalLit_zero g ρ

theorem bool_atLeastTwo_eq_adder (a b c : Bool) :
    ((a ^^ b) && c || (a && b)) = a.atLeastTwo b c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem bitvec_eq_iff_getLsbD {w : Nat} (x y : BitVec w) :
    decide (∀ j < w, x.getLsbD j = y.getLsbD j) = (x == y) := by
  by_cases h : x = y
  · subst h; simp
  · have hne : ¬ (∀ j < w, x.getLsbD j = y.getLsbD j) := fun hall =>
      h (BitVec.eq_of_getLsbD_eq hall)
    simp [h, hne]

theorem evalLit_eq_of_slices {g g' : Ref.Aig} {ρ : Nat → Bool}
    {xs : List (BitVec 32)} {aOff bOff w : Nat} {vA vB : BitVec w} {ret : BitVec 32}
    (hle_a : aOff + w ≤ xs.length) (hle_b : bOff + w ≤ xs.length)
    (hdenA : SliceDenotes g ρ (litsSlice xs aOff w) vA)
    (hdenB : SliceDenotes g ρ (litsSlice xs bOff w) vB)
    (heq : g'.evalLit ρ (UInt32.ofBitVec ret) =
      decide (∀ j < w,
        g.evalLit ρ (UInt32.ofBitVec (xs.getD (aOff + j) 0#32)) =
          g.evalLit ρ (UInt32.ofBitVec (xs.getD (bOff + j) 0#32)))) :
    g'.evalLit ρ (UInt32.ofBitVec ret) = (vA == vB) := by
  rw [sliceDenotes_iff hle_a] at hdenA
  rw [sliceDenotes_iff hle_b] at hdenB
  rw [heq, ← bitvec_eq_iff_getLsbD vA vB]
  by_cases h : ∀ j < w, vA.getLsbD j = vB.getLsbD j
  · have h' : ∀ j < w,
        g.evalLit ρ (UInt32.ofBitVec (xs.getD (aOff + j) 0#32)) =
          g.evalLit ρ (UInt32.ofBitVec (xs.getD (bOff + j) 0#32)) := fun j hj => by
      rw [hdenA j hj, hdenB j hj]; exact h j hj
    simp only [decide_eq_true h, decide_eq_true h']
  · have h' : ¬ ∀ j < w,
        g.evalLit ρ (UInt32.ofBitVec (xs.getD (aOff + j) 0#32)) =
          g.evalLit ρ (UInt32.ofBitVec (xs.getD (bOff + j) 0#32)) := fun hall =>
      h fun j hj => by rw [← hdenA j hj, ← hdenB j hj]; exact hall j hj
    simp only [decide_eq_false h, decide_eq_false h']

/-- Any literal slice `[off .. off + w)` denotes a concrete `BitVec w` under `(g, ρ)`. -/
def sliceBitVec (g : Ref.Aig) (ρ : Nat → Bool) (xs : List (BitVec 32)) (off w : Nat) :
    BitVec w :=
  (BitVec.ofBoolListLE
    ((List.range w).map fun i => g.evalLit ρ (UInt32.ofBitVec (xs.getD (off + i) 0#32)))).cast
    (by simp)

theorem sliceDenotes_sliceBitVec {g : Ref.Aig} {ρ : Nat → Bool}
    {xs : List (BitVec 32)} {off w : Nat} (hle : off + w ≤ xs.length) :
    SliceDenotes g ρ (litsSlice xs off w) (sliceBitVec g ρ xs off w) := by
  rw [sliceDenotes_iff hle]
  intro j hj
  simp only [sliceBitVec, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  simp

/-! ## `array (t := i32)` Load/Store Helpers -/

theorem ops_load_array32_u32_add_mul4 {R : Mem 64 → Prop} {m : Mem 64} {a : BitVec 64}
    {off k : BitVec 32} {xs : List (BitVec 32)} (h : (array (t := i32) a xs ⋆ R) m)
    (hwrap : off.toNat + k.toNat < 2 ^ 32) (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i32 (a + BitVec.setWidth 64 (off + k) * 4) =
      some (xs[off.toNat + k.toNat]'hi) := by
  have hsh : BitVec.setWidth 64 (off + k) * (4 : BitVec 64) =
      BitVec.setWidth 64 (off + k) <<< 2 := by
    bv_omega
  rw [hsh]
  exact c0_load_array32_u32_add_shl2 h hwrap hi

theorem ops_store_array32_u32_add_mul4 {R : Mem 64 → Prop} {m : Mem 64} {a : BitVec 64}
    {off k : BitVec 32} {xs : List (BitVec 32)} (v : BitVec 32)
    (h : (array (t := i32) a xs ⋆ R) m)
    (hwrap : off.toNat + k.toNat < 2 ^ 32) (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i32 (a + BitVec.setWidth 64 (off + k) * 4) ∧
      (array (t := i32) a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i32 (a + BitVec.setWidth 64 (off + k) * 4) v) := by
  have hsh : BitVec.setWidth 64 (off + k) * (4 : BitVec 64) =
      BitVec.setWidth 64 (off + k) <<< 2 := by
    bv_omega
  rw [hsh]
  exact c0_store_array32_u32_add_shl2 v h hwrap hi

theorem ops_load_array32_u32_ext_mul4 {R : Mem 64 → Prop} {m : Mem 64} {a : BitVec 64}
    {off : BitVec 32} {pos : BitVec 64} {xs : List (BitVec 32)}
    (h : (array (t := i32) a xs ⋆ R) m)
    (hpos : pos.toNat < 2 ^ 32) (hwrap : off.toNat + pos.toNat < 2 ^ 32)
    (hi : off.toNat + pos.toNat < xs.length) :
    loadVal m i32 (a + BitVec.setWidth 64 (off + BitVec.setWidth 32 pos) * 4) =
      some (xs[off.toNat + pos.toNat]'hi) := by
  have hlen : off.toNat + (BitVec.setWidth 32 pos).toNat < xs.length := by
    simpa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hpos] using hi
  have hwrap' : off.toNat + (BitVec.setWidth 32 pos).toNat < 2 ^ 32 := by
    simpa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hpos] using hwrap
  have hres := ops_load_array32_u32_add_mul4 h hwrap' hlen
  simpa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hpos] using hres

theorem ops_store_array32_u32_add_add_mul4 {R : Mem 64 → Prop} {m : Mem 64} {a : BitVec 64}
    {out rw j : BitVec 32} {xs : List (BitVec 32)} (v : BitVec 32)
    (h : (array (t := i32) a xs ⋆ R) m)
    (hwrap1 : out.toNat + rw.toNat < 2 ^ 32)
    (hwrap2 : out.toNat + rw.toNat + j.toNat < 2 ^ 32)
    (hi : out.toNat + rw.toNat + j.toNat < xs.length) :
    storeOk m i32 (a + BitVec.setWidth 64 (out + rw + j) * 4) ∧
      (array (t := i32) a (xs.set (out.toNat + rw.toNat + j.toNat) v) ⋆ R)
        (storeMem m i32 (a + BitVec.setWidth 64 (out + rw + j) * 4) v) := by
  have hsum : (out + rw).toNat = out.toNat + rw.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hwrap1]
  have hwrap' : (out + rw).toNat + j.toNat < 2 ^ 32 := by omega
  have hi' : (out + rw).toNat + j.toNat < xs.length := by omega
  have hres := ops_store_array32_u32_add_mul4 (off := out + rw) (k := j) v h hwrap' hi'
  simpa [hsum] using hres

/-! ## Separation Framing Helper -/

theorem ops_sep_cast {P Q : Mem 64 → Prop} {m : Mem 64} (h : P m) (heq : P = Q) : Q m :=
  heq ▸ h

theorem ops_sep_emp {P : Mem 64 → Prop} {m : Mem 64}
    (h : (P ⋆ Std.ExtHashMap.emp) m) : P m := by
  simpa only [Std.ExtHashMap.sep_emp] using h

theorem ops_sep_assoc_r {A B C : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ C) m) : (A ⋆ (B ⋆ C)) m :=
  (by ac_rfl : (A ⋆ B ⋆ C) = (A ⋆ (B ⋆ C))) ▸ h

theorem ops_sep_assoc_l {A B C : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ C)) m) : (A ⋆ B ⋆ C) m :=
  (by ac_rfl : (A ⋆ (B ⋆ C)) = (A ⋆ B ⋆ C)) ▸ h

theorem ops_sep_emp3 {A B C : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ (C ⋆ Std.ExtHashMap.emp))) m) : (A ⋆ B ⋆ C) m :=
  (by simp only [Std.ExtHashMap.sep_emp]; ac_rfl :
    (A ⋆ (B ⋆ (C ⋆ Std.ExtHashMap.emp))) = (A ⋆ B ⋆ C)) ▸ h

theorem ops_sep_swap12 {A B C : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ C) m) : (B ⋆ A ⋆ C) m :=
  (by ac_rfl : (A ⋆ B ⋆ C) = (B ⋆ A ⋆ C)) ▸ h

theorem ops_sep_swap12_r {A B C : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ C) m) : (B ⋆ (A ⋆ C)) m :=
  (by ac_rfl : (A ⋆ B ⋆ C) = (B ⋆ (A ⋆ C))) ▸ h

theorem ops_sep_swap12_l {A B C : Mem 64 → Prop} {m : Mem 64}
    (h : (B ⋆ (A ⋆ C)) m) : (A ⋆ B ⋆ C) m :=
  (by ac_rfl : (B ⋆ (A ⋆ C)) = (A ⋆ B ⋆ C)) ▸ h

theorem ops_setWidth64_add_u32 {a b : BitVec 32} (hwrap : a.toNat + b.toNat < 2 ^ 32) :
    (BitVec.setWidth 64 (a + b)).toNat = a.toNat + b.toNat := by
  have h1 : a.toNat + b.toNat < 2 ^ 64 := Nat.lt_trans hwrap (by decide)
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, Nat.mod_eq_of_lt hwrap, Nat.mod_eq_of_lt h1]

theorem ops_setWidth64_add3_u32 {a b c : BitVec 32}
    (h1 : a.toNat + b.toNat < 2 ^ 32) (h2 : a.toNat + b.toNat + c.toNat < 2 ^ 32) :
    (BitVec.setWidth 64 (a + b + c)).toNat = a.toNat + b.toNat + c.toNat := by
  have hlt : a.toNat + b.toNat + c.toNat < 2 ^ 64 := Nat.lt_trans h2 (by decide)
  have hab : (a + b).toNat = a.toNat + b.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt h1]
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, hab, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt hlt]

theorem ops_setWidth64_ext_u32 {off : BitVec 32} {pos : BitVec 64}
    (hpos : pos.toNat < 2 ^ 32) (hwrap : off.toNat + pos.toNat < 2 ^ 32) :
    (BitVec.setWidth 64 (off + BitVec.setWidth 32 pos)).toNat = off.toNat + pos.toNat := by
  have hp : (BitVec.setWidth 32 pos).toNat = pos.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hpos]
  rw [ops_setWidth64_add_u32 (by omega), hp]

theorem ops_list_getElem_eq_getD {α : Type} (xs : List α) (d : α) {i j : Nat}
    (hi : i < xs.length) (heq : i = j) : xs[i]'hi = xs.getD j d := by
  subst heq
  exact list_getD_eq_getElem xs d hi

theorem ops_sep_swap12_emp3 {A B C : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ ((B ⋆ C) ⋆ Std.ExtHashMap.emp)) m) : (B ⋆ A ⋆ C) m :=
  (by simp only [Std.ExtHashMap.sep_emp]; ac_rfl :
    (A ⋆ ((B ⋆ C) ⋆ Std.ExtHashMap.emp)) = (B ⋆ A ⋆ C)) ▸ h

theorem ops_sep_swap12_emp3_r {A B C : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ ((B ⋆ C) ⋆ Std.ExtHashMap.emp)) m) : (B ⋆ (A ⋆ C)) m :=
  (by simp only [Std.ExtHashMap.sep_emp]; ac_rfl :
    (A ⋆ ((B ⋆ C) ⋆ Std.ExtHashMap.emp)) = (B ⋆ (A ⋆ C))) ▸ h

theorem ops_sep_emp_rot12 {A B C : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ (C ⋆ Std.ExtHashMap.emp))) m) : (B ⋆ A ⋆ C) m :=
  ops_sep_swap12 (ops_sep_emp3 h)

theorem ops_sep5_hdr_focus {A B C D R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ C ⋆ D ⋆ R) m) : (A ⋆ (B ⋆ C ⋆ D ⋆ R)) m :=
  (by ac_rfl : (A ⋆ B ⋆ C ⋆ D ⋆ R) = (A ⋆ (B ⋆ C ⋆ D ⋆ R))) ▸ h

theorem ops_sep5_hdr_unfocus {A B C D R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ C ⋆ D ⋆ R)) m) : (A ⋆ B ⋆ C ⋆ D ⋆ R) m :=
  (by ac_rfl : (A ⋆ (B ⋆ C ⋆ D ⋆ R)) = (A ⋆ B ⋆ C ⋆ D ⋆ R)) ▸ h

theorem ops_sep5_aig_focus {A B C D R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ C ⋆ D ⋆ R) m) : (A ⋆ B ⋆ C ⋆ (D ⋆ R)) m :=
  (by ac_rfl : (A ⋆ B ⋆ C ⋆ D ⋆ R) = (A ⋆ B ⋆ C ⋆ (D ⋆ R))) ▸ h

theorem ops_sep5_aig_unfocus {A B C D R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ C ⋆ (D ⋆ R)) m) : (A ⋆ B ⋆ C ⋆ D ⋆ R) m :=
  (by ac_rfl : (A ⋆ B ⋆ C ⋆ (D ⋆ R)) = (A ⋆ B ⋆ C ⋆ D ⋆ R)) ▸ h

theorem ops_sep5_lits_focus {A B C D R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ C ⋆ D ⋆ R) m) : (D ⋆ (A ⋆ B ⋆ C ⋆ R)) m :=
  (by ac_rfl : (A ⋆ B ⋆ C ⋆ D ⋆ R) = (D ⋆ (A ⋆ B ⋆ C ⋆ R))) ▸ h

theorem ops_sep5_lits_unfocus {A B C D R : Mem 64 → Prop} {m : Mem 64}
    (h : (D ⋆ (A ⋆ B ⋆ C ⋆ R)) m) : (A ⋆ B ⋆ C ⋆ D ⋆ R) m :=
  (by ac_rfl : (D ⋆ (A ⋆ B ⋆ C ⋆ R)) = (A ⋆ B ⋆ C ⋆ D ⋆ R)) ▸ h

theorem ops_sep5_emp_lits {A B C D R : Mem 64 → Prop} {m : Mem 64}
    (h : (D ⋆ ((A ⋆ B ⋆ C ⋆ R) ⋆ Std.ExtHashMap.emp)) m) : (A ⋆ B ⋆ C ⋆ D ⋆ R) m :=
  (by simp only [Std.ExtHashMap.sep_emp]; ac_rfl :
    (D ⋆ ((A ⋆ B ⋆ C ⋆ R) ⋆ Std.ExtHashMap.emp)) = (A ⋆ B ⋆ C ⋆ D ⋆ R)) ▸ h

theorem ops_sep5_emp_hdr {A B C D R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ C ⋆ D ⋆ (R ⋆ Std.ExtHashMap.emp))) m) : (A ⋆ B ⋆ C ⋆ D ⋆ R) m :=
  (by simp only [Std.ExtHashMap.sep_emp]; ac_rfl :
    (A ⋆ (B ⋆ C ⋆ D ⋆ (R ⋆ Std.ExtHashMap.emp))) = (A ⋆ B ⋆ C ⋆ D ⋆ R)) ▸ h

/-! ## AIG Call Step Wrapper -/

theorem ops_call_aig_bin {Γ : Env} {nm : Sym} {opFn : Bool → Bool → Bool} {maxG : Nat}
    (hFn : ∀ xs m Q X, bvAigBinSpec opFn maxG xs m Q X →
      Γ nm [i64, i32, i32] [i32] xs m Q X)
    {h : BitVec 64} {lhs rhs : BitVec 32}
    {hdr : BVHdrState} {g : Ref.Aig} {aigWords : List (BitVec 64)}
    {htSlots : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : (BitVec 32 × PUnit) → Mem 64 → Prop} {X : XPost}
    (hinv : AigInv hdr g aigWords htSlots)
    (hbnd : hdr.oom = 0#32 →
      (lhs >>> 1).toNat < hdr.aig_len.toNat ∧ (rhs >>> 1).toNat < hdr.aig_len.toNat)
    (hm : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆ R) m)
    (hk : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Ref.Aig)
      (aigWords' : List (BitVec 64)) (htSlots' : List (BitVec 32)) (m' : Mem 64),
      hdr.AigFrame hdr' → g ≤ g' → g'.nodes.size ≤ g.nodes.size + maxG →
      AigInv hdr' g' aigWords' htSlots' →
      (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
      (hdr.oom = 0#32 → g.A + 1 + g.nodes.size + maxG ≤ hdr.aig_cap.toNat →
        g.nodes.size + maxG ≤ bvMaxGates → hdr'.oom = 0#32) →
      (hdr'.oom = 0#32 → (ret >>> 1).toNat < hdr'.aig_len.toNat ∧
        ∀ ρ : Nat → Bool, g'.evalLit ρ (UInt32.ofBitVec ret) =
          opFn (g.evalLit ρ (UInt32.ofBitVec lhs)) (g.evalLit ρ (UInt32.ofBitVec rhs))) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    Γ nm [i64, i32, i32] [i32] (h, lhs, rhs, ⟨⟩) m Q X :=
  hFn _ _ _ _ ⟨hdr, g, aigWords, htSlots, R, hinv, hbnd, hm, hk⟩

end

end LeanQbe.T.Examples.Bitblast.Proof
