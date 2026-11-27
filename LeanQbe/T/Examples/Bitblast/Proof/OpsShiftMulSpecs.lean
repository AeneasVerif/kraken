/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.Specs
public import LeanQbe.T.Examples.Bitblast.Src.OpsShiftMul
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `OpsShiftMul` (`Bitblast.Proof.OpsShiftMulSpecs`)

Single source of truth for all canonical `LeanQbe.T.Spec` contracts of
`LeanQbe.T.Examples.Bitblast.Src.OpsShiftMul` (`12` defined functions + `8` externs = `20` rows in
`opsShiftMulSpecTable`), all `XPost`-polymorphic (`noExit = true`), plus `BVHdrState.OpsFrame`,
`sliceOkBool`, `SliceLitsWf`, `bvShiftSem`, and `opsShiftMulEnv`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open Std.Tactic.BVDecide
open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Src
open LeanQbe.T.Examples.Bitblast.Src.OpsShiftMul

@[expose] public section

/-! ## 1. Header Frame, Slice Bounds, and Semantic Combinators -/

/-- Framing predicate: `h2` agrees with `h1` on every `BVHdr` field except `aig_len`,
`lits_len`, and `oom`. -/
structure BVHdrState.OpsFrame (h1 h2 : BVHdrState) : Prop where
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

/-- Exact runtime slice validity check matching `OpsCore.bv_slice_ok(h, off, w)`. -/
def sliceOkBool (hdr : BVHdrState) (off w : BitVec 32) : Bool :=
  decide (hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
    (0 < w.toNat → hdr.lits_ptr ≠ 0#64) ∧
    off.toNat ≤ hdr.lits_len.toNat ∧
    w.toNat ≤ hdr.lits_len.toNat - off.toNat)

/-- Well-formedness of a `w`-literal slice at `litsPool[off ..< off + w]` with respect to `g`. -/
def SliceLitsWf (g : Aig) (litsPool : List (BitVec 32)) (off w : Nat) : Prop :=
  ∀ j < w, ((litsPool.getD (off + j) 0#32) >>> 1).toNat < g.A + 1 + g.nodes.size

/-- Variable-shift bitvector semantics indexed by C0 opcode (`19` = shl, `20` = ushr, `21` =
ashr). -/
def bvShiftSem (op : BitVec 32) {w nw : Nat} (va : BitVec w) (vb : BitVec nw) : BitVec w :=
  if op = 19#32 then va <<< vb
  else if op = 20#32 then va >>> vb
  else va.sshiftRight' vb

/-! ## 2. Extern Specifications (`bv_slice_ok`, `bv_blast_add`) -/

/-- Canonical spec for extern `bv_slice_ok(h, off, w)`. -/
def smBvSliceOkSpec : Spec [i64, i32, i32] [.bool] :=
  fun ⟨h, off, w, ⟨⟩⟩ m Q _X =>
    ∃ (hdr : BVHdrState) (R : Mem 64 → Prop),
      (bvHdrMem h hdr ⋆ R) m ∧
      Q (sliceOkBool hdr off w, ⟨⟩) m

/-- Shared canonical body for binary AIG-allocating `lits`-slice operations taking `(h, aOff,
aw, bOff, bw)` with opcode check `opOk`, input WF guard, and output semantic combinator `sem`. -/
def bvBlastBinOpSpecBody (h : BitVec 64) (aOff aw bOff bw : BitVec 32) (opOk : Bool)
    (sem : BitVec aw.toNat → BitVec bw.toNat → BitVec aw.toNat)
    (requireOk : Bool) (m : Mem 64) (Q : Post [i32]) : Prop :=
  ∃ (hdr : BVHdrState) (g : Aig) (aigWords : List (BitVec 64))
    (htSlots litsPool : List (BitVec 32)) (R : Mem 64 → Prop),
    AigInv hdr g aigWords htSlots ∧
    litsPool.length = hdr.lits_cap.toNat ∧
    (requireOk = true →
      hdr.oom = 0#32 ∧ opOk = true ∧
      sliceOkBool hdr aOff aw = true ∧ sliceOkBool hdr bOff bw = true) ∧
    (hdr.oom = 0#32 → opOk = true → sliceOkBool hdr aOff aw = true →
      sliceOkBool hdr bOff bw = true →
      SliceLitsWf g litsPool aOff.toNat aw.toNat ∧
      SliceLitsWf g litsPool bOff.toNat bw.toNat) ∧
    (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆
      array (t := i32) hdr.lits_ptr litsPool ⋆ R) m ∧
    ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig)
      (aigWords' : List (BitVec 64)) (htSlots' litsPool' : List (BitVec 32)) (m' : Mem 64),
      hdr.OpsFrame hdr' →
      g ≤ g' →
      AigInv hdr' g' aigWords' htSlots' →
      litsPool'.length = litsPool.length →
      hdr.lits_len.toNat ≤ hdr'.lits_len.toNat →
      (hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
        hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat) →
      (∀ p < hdr.lits_len.toNat, litsPool'.getD p 0#32 = litsPool.getD p 0#32) →
      (hdr.oom ≠ 0#32 ∨ opOk = false ∨
        sliceOkBool hdr aOff aw = false ∨ sliceOkBool hdr bOff bw = false →
        hdr'.oom ≠ 0#32) →
      (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
      (hdr'.oom = 0#32 →
        hdr.oom = 0#32 ∧ opOk = true ∧
        sliceOkBool hdr aOff aw = true ∧ sliceOkBool hdr bOff bw = true ∧
        ret = hdr.lits_len ∧
        hdr'.lits_len = hdr.lits_len + aw ∧
        SliceLitsWf g' litsPool' ret.toNat aw.toNat ∧
        ∀ (ρ : Nat → Bool) (va : BitVec aw.toNat) (vb : BitVec bw.toNat),
          SliceDenotes g ρ (litsSlice litsPool aOff.toNat aw.toNat) va →
          SliceDenotes g ρ (litsSlice litsPool bOff.toNat bw.toNat) vb →
          SliceDenotes g' ρ (litsSlice litsPool' ret.toNat aw.toNat) (sem va vb)) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆
        array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
      Q (ret, ⟨⟩) m'

/-- Canonical spec for extern `bv_blast_add(h, a_off, b_off, w)`. -/
def smBvBlastAddSpec : Spec [i64, i32, i32, i32] [i32] :=
  fun ⟨h, aOff, bOff, w, ⟨⟩⟩ m Q _X =>
    bvBlastBinOpSpecBody h aOff w bOff w true (· + ·) true m Q

/-! ## 3. Canonical Specifications — `OpsShiftMul` (`12` fns) -/

/-- Canonical spec for `bv_copy_lits(h, dst_off, src_off, w)`. -/
def bvCopyLitsSpec : Spec [i64, i32, i32, i32] [] :=
  fun ⟨h, dstOff, srcOff, w, ⟨⟩⟩ m Q _X =>
    ∃ (hdr : BVHdrState) (litsPool : List (BitVec 32)) (R : Mem 64 → Prop),
      litsPool.length < 2 ^ 32 ∧
      dstOff.toNat + w.toNat ≤ litsPool.length ∧
      srcOff.toNat + w.toNat ≤ litsPool.length ∧
      (dstOff.toNat + w.toNat ≤ srcOff.toNat ∨ srcOff.toNat + w.toNat ≤ dstOff.toNat) ∧
      (bvHdrMem h hdr ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m ∧
      ∀ (litsPool' : List (BitVec 32)) (m' : Mem 64),
        litsPool'.length = litsPool.length →
        (∀ p, p < dstOff.toNat ∨ dstOff.toNat + w.toNat ≤ p →
          litsPool'.getD p 0#32 = litsPool.getD p 0#32) →
        (∀ j < w.toNat,
          litsPool'.getD (dstOff.toNat + j) 0#32 = litsPool.getD (srcOff.toNat + j) 0#32) →
        (bvHdrMem h hdr ⋆ array (t := i32) hdr.lits_ptr litsPool' ⋆ R) m' →
        Q ⟨⟩ m'

/-- Shared canonical spec body for pure `lits`-reindexing operators (`replicate`, `rotl`, `rotr`,
`ashrc`, `reverse`). -/
def bvLitsPureOpBody (h : BitVec 64) (ok : BVHdrState → Bool) (outW : BitVec 32)
    (idxFn : Nat → Nat) (m : Mem 64) (Q : Post [i32]) : Prop :=
  ∃ (hdr : BVHdrState) (litsPool : List (BitVec 32)) (R : Mem 64 → Prop),
    litsPool.length = hdr.lits_cap.toNat ∧
    (bvHdrMem h hdr ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m ∧
    ∀ (ret : BitVec 32) (hdr' : BVHdrState) (litsPool' : List (BitVec 32)) (m' : Mem 64),
      hdr.OpsFrame hdr' →
      hdr'.aig_len = hdr.aig_len →
      litsPool'.length = litsPool.length →
      (∀ p < hdr.lits_len.toNat, litsPool'.getD p 0#32 = litsPool.getD p 0#32) →
      (ok hdr = true →
        hdr'.oom = 0#32 ∧
        ret = hdr.lits_len ∧
        hdr'.lits_len = hdr.lits_len + outW ∧
        ∀ j < outW.toNat,
          litsPool'.getD (ret.toNat + j) 0#32 = litsPool.getD (idxFn j) 0#32) →
      (ok hdr = false →
        hdr'.oom = 1#32 ∧
        hdr'.lits_len = hdr.lits_len ∧
        ret = 0xFFFFFFFF#32 ∧
        litsPool' = litsPool) →
      (bvHdrMem h hdr' ⋆ array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
      Q (ret, ⟨⟩) m'

/-- Canonical spec for `bv_blast_replicate(h, a_off, aw, n)`. -/
def bvBlastReplicateSpec : Spec [i64, i32, i32, i32] [i32] :=
  fun ⟨h, aOff, aw, n, ⟨⟩⟩ m Q _X =>
    bvLitsPureOpBody h
      (fun hdr => decide (hdr.oom = 0#32 ∧ sliceOkBool hdr aOff aw = true ∧
        aw.toNat * n.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat))
      (BitVec.ofNat 32 (aw.toNat * n.toNat))
      (fun j => aOff.toNat + j % aw.toNat) m Q

/-- Canonical spec for `bv_blast_rotl(h, a_off, w, n)`. -/
def bvBlastRotlSpec : Spec [i64, i32, i32, i32] [i32] :=
  fun ⟨h, aOff, w, n, ⟨⟩⟩ m Q _X =>
    bvLitsPureOpBody h
      (fun hdr => decide (hdr.oom = 0#32 ∧ sliceOkBool hdr aOff w = true ∧
        w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat))
      w
      (fun j =>
        let r := n.toNat % w.toNat
        aOff.toNat + (if j < r then w.toNat - r + j else j - r))
      m Q

/-- Canonical spec for `bv_blast_rotr(h, a_off, w, n)`. -/
def bvBlastRotrSpec : Spec [i64, i32, i32, i32] [i32] :=
  fun ⟨h, aOff, w, n, ⟨⟩⟩ m Q _X =>
    bvLitsPureOpBody h
      (fun hdr => decide (hdr.oom = 0#32 ∧ sliceOkBool hdr aOff w = true ∧
        w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat))
      w
      (fun j =>
        let r := n.toNat % w.toNat
        let cut := w.toNat - r
        aOff.toNat + (if j < cut then r + j else j - cut))
      m Q

/-- Canonical spec for `bv_blast_ashrc(h, a_off, w, n)`. -/
def bvBlastAshrcSpec : Spec [i64, i32, i32, i32] [i32] :=
  fun ⟨h, aOff, w, n, ⟨⟩⟩ m Q _X =>
    bvLitsPureOpBody h
      (fun hdr => decide (hdr.oom = 0#32 ∧ sliceOkBool hdr aOff w = true ∧
        w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat))
      w
      (fun j => aOff.toNat + (if n.toNat + j < w.toNat then n.toNat + j else w.toNat - 1))
      m Q

/-- Canonical spec for `bv_blast_reverse(h, a_off, w)`. -/
def bvBlastReverseSpec : Spec [i64, i32, i32] [i32] :=
  fun ⟨h, aOff, w, ⟨⟩⟩ m Q _X =>
    bvLitsPureOpBody h
      (fun hdr => decide (hdr.oom = 0#32 ∧ sliceOkBool hdr aOff w = true ∧
        w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat))
      w
      (fun j => aOff.toNat + (w.toNat - 1 - j))
      m Q

/-- Canonical spec for `bv_blast_shift_var(h, a_off, w, b_off, nw, op)`. -/
def bvBlastShiftVarSpec : Spec [i64, i32, i32, i32, i32, i32] [i32] :=
  fun ⟨h, aOff, w, bOff, nw, op, ⟨⟩⟩ m Q _X =>
    bvBlastBinOpSpecBody h aOff w bOff nw
      (decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32))
      (bvShiftSem op) false m Q

/-- Canonical spec for `bv_blast_shl(h, a_off, w, b_off, nw)`. -/
def bvBlastShlSpec : Spec [i64, i32, i32, i32, i32] [i32] :=
  fun ⟨h, aOff, w, bOff, nw, ⟨⟩⟩ m Q _X =>
    bvBlastBinOpSpecBody h aOff w bOff nw true (· <<< ·) false m Q

/-- Canonical spec for `bv_blast_ushr(h, a_off, w, b_off, nw)`. -/
def bvBlastUshrSpec : Spec [i64, i32, i32, i32, i32] [i32] :=
  fun ⟨h, aOff, w, bOff, nw, ⟨⟩⟩ m Q _X =>
    bvBlastBinOpSpecBody h aOff w bOff nw true (· >>> ·) false m Q

/-- Canonical spec for `bv_blast_ashr(h, a_off, w, b_off, nw)`. -/
def bvBlastAshrSpec : Spec [i64, i32, i32, i32, i32] [i32] :=
  fun ⟨h, aOff, w, bOff, nw, ⟨⟩⟩ m Q _X =>
    bvBlastBinOpSpecBody h aOff w bOff nw true BitVec.sshiftRight' false m Q

/-- Canonical spec for `bv_blast_mul(h, a_off, b_off, w)`. -/
def bvBlastMulSpec : Spec [i64, i32, i32, i32] [i32] :=
  fun ⟨h, aOff, bOff, w, ⟨⟩⟩ m Q _X =>
    bvBlastBinOpSpecBody h aOff w bOff w true (· * ·) false m Q

/-- Canonical spec for `bv_blast_clz(h, a_off, w)`. -/
def bvBlastClzSpec : Spec [i64, i32, i32] [i32] :=
  fun ⟨h, aOff, w, ⟨⟩⟩ m Q _X =>
    ∃ (hdr : BVHdrState) (g : Aig) (aigWords : List (BitVec 64))
      (htSlots litsPool : List (BitVec 32)) (R : Mem 64 → Prop),
      AigInv hdr g aigWords htSlots ∧
      litsPool.length = hdr.lits_cap.toNat ∧
      (hdr.oom = 0#32 → sliceOkBool hdr aOff w = true →
        SliceLitsWf g litsPool aOff.toNat w.toNat) ∧
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆
        array (t := i32) hdr.lits_ptr litsPool ⋆ R) m ∧
      ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig)
        (aigWords' : List (BitVec 64)) (htSlots' litsPool' : List (BitVec 32)) (m' : Mem 64),
        hdr.OpsFrame hdr' →
        g ≤ g' →
        AigInv hdr' g' aigWords' htSlots' →
        litsPool'.length = litsPool.length →
        hdr.lits_len.toNat ≤ hdr'.lits_len.toNat →
        (hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
        hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat) →
        (∀ p < hdr.lits_len.toNat, litsPool'.getD p 0#32 = litsPool.getD p 0#32) →
        (hdr.oom ≠ 0#32 ∨ sliceOkBool hdr aOff w = false → hdr'.oom ≠ 0#32) →
        (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
        (hdr'.oom = 0#32 →
          hdr.oom = 0#32 ∧ sliceOkBool hdr aOff w = true ∧
          ret = hdr.lits_len ∧
          hdr'.lits_len = hdr.lits_len + w ∧
          SliceLitsWf g' litsPool' ret.toNat w.toNat ∧
          ∀ (ρ : Nat → Bool) (va : BitVec w.toNat),
            SliceDenotes g ρ (litsSlice litsPool aOff.toNat w.toNat) va →
            SliceDenotes g' ρ (litsSlice litsPool' ret.toNat w.toNat) va.clz) →
        (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
          array (t := i32) hdr'.ht_ptr htSlots' ⋆
          array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
        Q (ret, ⟨⟩) m'

/-! ## 4. Closed `20`-Row `opsShiftMulSpecTable` and `opsShiftMulEnv` -/

/-- Specification rows for the `12` defined functions of `opsShiftMulFns`. -/
def opsShiftMulFnSpecTable : List SpecEntry :=
  [ ⟨"bv_copy_lits", [i64, i32, i32, i32], [], bvCopyLitsSpec, true⟩
  , ⟨"bv_blast_replicate", [i64, i32, i32, i32], [i32], bvBlastReplicateSpec, true⟩
  , ⟨"bv_blast_rotl", [i64, i32, i32, i32], [i32], bvBlastRotlSpec, true⟩
  , ⟨"bv_blast_rotr", [i64, i32, i32, i32], [i32], bvBlastRotrSpec, true⟩
  , ⟨"bv_blast_ashrc", [i64, i32, i32, i32], [i32], bvBlastAshrcSpec, true⟩
  , ⟨"bv_blast_reverse", [i64, i32, i32], [i32], bvBlastReverseSpec, true⟩
  , ⟨"bv_blast_shift_var", [i64, i32, i32, i32, i32, i32], [i32], bvBlastShiftVarSpec, true⟩
  , ⟨"bv_blast_shl", [i64, i32, i32, i32, i32], [i32], bvBlastShlSpec, true⟩
  , ⟨"bv_blast_ushr", [i64, i32, i32, i32, i32], [i32], bvBlastUshrSpec, true⟩
  , ⟨"bv_blast_ashr", [i64, i32, i32, i32, i32], [i32], bvBlastAshrSpec, true⟩
  , ⟨"bv_blast_mul", [i64, i32, i32, i32], [i32], bvBlastMulSpec, true⟩
  , ⟨"bv_blast_clz", [i64, i32, i32], [i32], bvBlastClzSpec, true⟩ ]

/-- Specification rows for the `8` externs of `opsShiftMulExterns`. -/
def opsShiftMulExternSpecTable : List SpecEntry :=
  [ ⟨"bv_mk_and", [i64, i32, i32], [i32], bvMkAndSpec, true⟩
  , ⟨"bv_aig_or", [i64, i32, i32], [i32], bvAigOrSpec, true⟩
  , ⟨"bv_aig_ite", [i64, i32, i32, i32], [i32], bvAigIteSpec, true⟩
  , ⟨"bv_lits_mark", [i64], [i32], bvLitsMarkSpec, true⟩
  , ⟨"bv_lits_release", [i64, i32], [], bvLitsReleaseSpec, true⟩
  , ⟨"bv_lits_alloc", [i64, i32], [i32], bvLitsAllocSpec, true⟩
  , ⟨"bv_slice_ok", [i64, i32, i32], [.bool], smBvSliceOkSpec, true⟩
  , ⟨"bv_blast_add", [i64, i32, i32, i32], [i32], smBvBlastAddSpec, true⟩ ]

/-- Full `20`-row specification table for `opsShiftMulModule`. -/
def opsShiftMulSpecTable : List SpecEntry :=
  opsShiftMulFnSpecTable ++ opsShiftMulExternSpecTable

/-- Closed canonical `Env` for `opsShiftMulModule`. -/
def opsShiftMulEnv : Env := Env.ofTable opsShiftMulSpecTable

end

/-! ## 5. Exit-Insensitivity (`Spec.XFree`), Frame, and Table Lemmas -/

public section

theorem smBvSliceOkSpec_xfree : smBvSliceOkSpec.XFree := by xfree
theorem smBvBlastAddSpec_xfree : smBvBlastAddSpec.XFree := by xfree
theorem bvCopyLitsSpec_xfree : bvCopyLitsSpec.XFree := by xfree
theorem bvBlastReplicateSpec_xfree : bvBlastReplicateSpec.XFree := by xfree
theorem bvBlastRotlSpec_xfree : bvBlastRotlSpec.XFree := by xfree
theorem bvBlastRotrSpec_xfree : bvBlastRotrSpec.XFree := by xfree
theorem bvBlastAshrcSpec_xfree : bvBlastAshrcSpec.XFree := by xfree
theorem bvBlastReverseSpec_xfree : bvBlastReverseSpec.XFree := by xfree
theorem bvBlastShiftVarSpec_xfree : bvBlastShiftVarSpec.XFree := by xfree
theorem bvBlastShlSpec_xfree : bvBlastShlSpec.XFree := by xfree
theorem bvBlastUshrSpec_xfree : bvBlastUshrSpec.XFree := by xfree
theorem bvBlastAshrSpec_xfree : bvBlastAshrSpec.XFree := by xfree
theorem bvBlastMulSpec_xfree : bvBlastMulSpec.XFree := by xfree
theorem bvBlastClzSpec_xfree : bvBlastClzSpec.XFree := by xfree

theorem BVHdrState.OpsFrame.rfl (h : BVHdrState) : h.OpsFrame h :=
  ⟨_root_.rfl, _root_.rfl, _root_.rfl, _root_.rfl, _root_.rfl, _root_.rfl, _root_.rfl,
    _root_.rfl, _root_.rfl, _root_.rfl, _root_.rfl, _root_.rfl, _root_.rfl, _root_.rfl,
    _root_.rfl, _root_.rfl, _root_.rfl, _root_.rfl, _root_.rfl⟩

theorem BVHdrState.OpsFrame.trans {h1 h2 h3 : BVHdrState}
    (h12 : h1.OpsFrame h2) (h23 : h2.OpsFrame h3) : h1.OpsFrame h3 :=
  ⟨h23.work_base.trans h12.work_base, h23.work_end.trans h12.work_end,
   h23.prog_ptr.trans h12.prog_ptr, h23.aig_ptr.trans h12.aig_ptr,
   h23.ht_ptr.trans h12.ht_ptr, h23.atom_base_ptr.trans h12.atom_base_ptr,
   h23.slice_off_ptr.trans h12.slice_off_ptr, h23.lits_ptr.trans h12.lits_ptr,
   h23.marks_ptr.trans h12.marks_ptr, h23.dimacs_start.trans h12.dimacs_start,
   h23.n_vars.trans h12.n_vars, h23.n_nodes.trans h12.n_nodes,
   h23.n_cwords.trans h12.n_cwords, h23.root_node.trans h12.root_node,
   h23.num_atoms.trans h12.num_atoms, h23.aig_cap.trans h12.aig_cap,
   h23.ht_mask.trans h12.ht_mask, h23.lits_cap.trans h12.lits_cap,
   h23.dimacs_len.trans h12.dimacs_len⟩

theorem BVHdrState.AigFrame.toOpsFrame {h1 h2 : BVHdrState} (h : h1.AigFrame h2) :
    h1.OpsFrame h2 :=
  ⟨h.work_base, h.work_end, h.prog_ptr, h.aig_ptr, h.ht_ptr, h.atom_base_ptr,
   h.slice_off_ptr, h.lits_ptr, h.marks_ptr, h.dimacs_start, h.n_vars, h.n_nodes,
   h.n_cwords, h.root_node, h.num_atoms, h.aig_cap, h.ht_mask, h.lits_cap, h.dimacs_len⟩

theorem BVWorkspaceOk.of_opsFrame {cfg : BVWorkspaceCfg} {hdr hdr' : BVHdrState}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords aigWords' : List (BitVec 64)}
    {htSlots htSlots' litsPool litsPool' : List (BitVec 32)}
    (hok : BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool)
    (hfr : hdr.OpsFrame hdr')
    (haig' : aigWords'.length = cfg.aig_cap) (hht' : htSlots'.length = cfg.ht_slots)
    (hlits' : litsPool'.length = cfg.lits_cap) :
    BVWorkspaceOk cfg hdr' atomBases sliceOffs aigWords' htSlots' litsPool' :=
  { hok with
    hdr_wb := hfr.work_base.trans hok.hdr_wb
    hdr_we := hfr.work_end.trans hok.hdr_we
    hdr_ab := hfr.atom_base_ptr.trans hok.hdr_ab
    hdr_so := hfr.slice_off_ptr.trans hok.hdr_so
    hdr_aig := hfr.aig_ptr.trans hok.hdr_aig
    hdr_ht := hfr.ht_ptr.trans hok.hdr_ht
    hdr_lits := hfr.lits_ptr.trans hok.hdr_lits
    hdr_nv := hfr.n_vars.trans hok.hdr_nv
    hdr_nn := hfr.n_nodes.trans hok.hdr_nn
    hdr_acap := hfr.aig_cap.trans hok.hdr_acap
    hdr_htmask := hfr.ht_mask.trans hok.hdr_htmask
    hdr_lcap := hfr.lits_cap.trans hok.hdr_lcap
    aig_len_eq := haig'
    ht_len := hht'
    lits_len := hlits' }

theorem opsShiftMulSpecTable_nodup : (opsShiftMulSpecTable.map SpecEntry.name).Nodup := by
  show ([ "bv_copy_lits", "bv_blast_replicate", "bv_blast_rotl", "bv_blast_rotr"
    , "bv_blast_ashrc", "bv_blast_reverse", "bv_blast_shift_var", "bv_blast_shl"
    , "bv_blast_ushr", "bv_blast_ashr", "bv_blast_mul", "bv_blast_clz"
    , "bv_mk_and", "bv_aig_or", "bv_aig_ite", "bv_lits_mark"
    , "bv_lits_release", "bv_lits_alloc", "bv_slice_ok", "bv_blast_add" ] : List String).Nodup
  decide

theorem opsShiftMulFnSpecTable_sigs :
    opsShiftMulFnSpecTable.map SpecEntry.sig = opsShiftMulFns.map Fn.sig := by
  rfl

theorem opsShiftMulSpecTable_noExit : ∀ e ∈ opsShiftMulSpecTable, e.noExit = true := by
  intro e he
  simp only [opsShiftMulSpecTable, opsShiftMulFnSpecTable, opsShiftMulExternSpecTable,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem opsShiftMulEnv_sat : opsShiftMulEnv.Sat opsShiftMulSpecTable :=
  Env.Sat.ofTable_self opsShiftMulSpecTable_nodup

end

end LeanQbe.T.Examples.Bitblast.Proof
