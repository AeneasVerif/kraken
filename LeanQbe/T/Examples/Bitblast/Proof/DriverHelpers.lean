/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.Specs
public import LeanQbe.T.Examples.Bitblast.Proof.Validate0
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas

/-!
# Evaluator Proof Helpers (`Bitblast.Proof.DriverHelpers`)

Shared framing, BitVec, `BlastEvalInv`, and `ParsedBVP1` node-decoding helpers used across
`Driver0`, `Driver1`, and `Driver`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open Std Std.Tactic.BVDecide
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Bitblast.Src
open LeanQbe.T.Examples.Bitblast.Src.Driver
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Ref.BVProg

public section
theorem bvBlastMem_hdr_left (cfg : BVWorkspaceCfg) (hdr : BVHdrState)
    (atomBases sliceOffs : List (BitVec 32)) (aigWords : List (BitVec 64))
    (htSlots litsPool : List (BitVec 32)) :
    bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool =
      (bvHdrMem cfg.work_base hdr ⋆
        (array (t := i32) (cfg.work_base + 128) atomBases ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
          (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
        array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) sliceOffs ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
          (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
        array64 cfg.aig_ptr aigWords ⋆
        array (t := i32) cfg.ht_ptr htSlots ⋆
        array (t := i32) cfg.lits_ptr litsPool ⋆
        region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
          (cfg.lits_bytes - 4 * cfg.lits_cap))) := by
  unfold bvBlastMem; ac_rfl

theorem bvBlastMem_aig_frame (cfg : BVWorkspaceCfg) (hdr : BVHdrState)
    (atomBases sliceOffs : List (BitVec 32)) (aigWords : List (BitVec 64))
    (htSlots litsPool : List (BitVec 32)) :
    bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool =
      ((bvHdrMem cfg.work_base hdr ⋆ array64 cfg.aig_ptr aigWords ⋆
          array (t := i32) cfg.ht_ptr htSlots) ⋆
        (array (t := i32) (cfg.work_base + 128) atomBases ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
          (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
        array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) sliceOffs ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
          (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
        array (t := i32) cfg.lits_ptr litsPool ⋆
        region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
          (cfg.lits_bytes - 4 * cfg.lits_cap))) := by
  unfold bvBlastMem; ac_rfl

theorem bvBlastMem_ab_focus (cfg : BVWorkspaceCfg) (hdr : BVHdrState)
    (atomBases sliceOffs : List (BitVec 32)) (aigWords : List (BitVec 64))
    (htSlots litsPool : List (BitVec 32)) :
    bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool =
      (array (t := i32) (cfg.work_base + 128) atomBases ⋆
        (bvHdrMem cfg.work_base hdr ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
          (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
        array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) sliceOffs ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
          (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
        array64 cfg.aig_ptr aigWords ⋆
        array (t := i32) cfg.ht_ptr htSlots ⋆
        array (t := i32) cfg.lits_ptr litsPool ⋆
        region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
          (cfg.lits_bytes - 4 * cfg.lits_cap))) := by
  unfold bvBlastMem; ac_rfl

theorem bvBlastMem_so_focus (cfg : BVWorkspaceCfg) (hdr : BVHdrState)
    (atomBases sliceOffs : List (BitVec 32)) (aigWords : List (BitVec 64))
    (htSlots litsPool : List (BitVec 32)) :
    bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool =
      (array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) sliceOffs ⋆
        (bvHdrMem cfg.work_base hdr ⋆
        array (t := i32) (cfg.work_base + 128) atomBases ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
          (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
          (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
        array64 cfg.aig_ptr aigWords ⋆
        array (t := i32) cfg.ht_ptr htSlots ⋆
        array (t := i32) cfg.lits_ptr litsPool ⋆
        region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
          (cfg.lits_bytes - 4 * cfg.lits_cap))) := by
  unfold bvBlastMem; ac_rfl

theorem bvBlastMem_lits_focus (cfg : BVWorkspaceCfg) (hdr : BVHdrState)
    (atomBases sliceOffs : List (BitVec 32)) (aigWords : List (BitVec 64))
    (htSlots litsPool : List (BitVec 32)) :
    bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool =
      (array (t := i32) cfg.lits_ptr litsPool ⋆
        (bvHdrMem cfg.work_base hdr ⋆
        array (t := i32) (cfg.work_base + 128) atomBases ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
          (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
        array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) sliceOffs ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
          (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
        array64 cfg.aig_ptr aigWords ⋆
        array (t := i32) cfg.ht_ptr htSlots ⋆
        region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
          (cfg.lits_bytes - 4 * cfg.lits_cap))) := by
  unfold bvBlastMem; ac_rfl

abbrev blastRest (cfg : BVWorkspaceCfg) (hdr : BVHdrState) (progPtr : BitVec 64)
    (progBytes : List UInt8) (atomBases sliceOffs : List (BitVec 32))
    (aigWords : List (BitVec 64)) (htSlots : List (BitVec 32)) (R : Mem 64 → Prop) :
    Mem 64 → Prop :=
  bytes progPtr progBytes ⋆ bvHdrMem cfg.work_base hdr ⋆
  array (t := i32) (cfg.work_base + 128) atomBases ⋆
  region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
    (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
  array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) sliceOffs ⋆
  region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
    (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
  array64 cfg.aig_ptr aigWords ⋆ array (t := i32) cfg.ht_ptr htSlots ⋆
  region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
    (cfg.lits_bytes - 4 * cfg.lits_cap) ⋆ R

theorem blast_lits_focus {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {progPtr : BitVec 64} {progBytes : List UInt8}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hlits : hdr.lits_ptr = cfg.lits_ptr)
    (hm : (bytes progPtr progBytes ⋆
      bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m) :
    (array (t := i32) hdr.lits_ptr litsPool ⋆
      blastRest cfg hdr progPtr progBytes atomBases sliceOffs aigWords htSlots R) m := by
  rw [hlits]; rw [bvBlastMem_lits_focus] at hm; unfold blastRest; exact sep_ac hm

theorem blast_lits_unfocus {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {progPtr : BitVec 64} {progBytes : List UInt8}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hlits : hdr.lits_ptr = cfg.lits_ptr)
    (hm : (array (t := i32) hdr.lits_ptr litsPool ⋆
      blastRest cfg hdr progPtr progBytes atomBases sliceOffs aigWords htSlots R) m) :
    (bytes progPtr progBytes ⋆
      bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m := by
  rw [bvBlastMem_lits_focus]; rw [hlits] at hm; unfold blastRest at hm; exact sep_ac hm

abbrev blastSoRest (cfg : BVWorkspaceCfg) (hdr : BVHdrState) (progPtr : BitVec 64)
    (progBytes : List UInt8) (atomBases : List (BitVec 32)) (aigWords : List (BitVec 64))
    (htSlots litsPool : List (BitVec 32)) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  bytes progPtr progBytes ⋆ bvHdrMem cfg.work_base hdr ⋆
  array (t := i32) (cfg.work_base + 128) atomBases ⋆
  region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
    (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
  region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
    (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
  array64 cfg.aig_ptr aigWords ⋆ array (t := i32) cfg.ht_ptr htSlots ⋆
  array (t := i32) cfg.lits_ptr litsPool ⋆
  region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
    (cfg.lits_bytes - 4 * cfg.lits_cap) ⋆ R

theorem blast_so_focus {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {progPtr : BitVec 64} {progBytes : List UInt8}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hso : hdr.slice_off_ptr = cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes))
    (hm : (bytes progPtr progBytes ⋆
      bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m) :
    (array (t := i32) hdr.slice_off_ptr sliceOffs ⋆
      blastSoRest cfg hdr progPtr progBytes atomBases aigWords htSlots litsPool R) m := by
  rw [hso]; rw [bvBlastMem_so_focus] at hm; unfold blastSoRest; exact sep_ac hm

theorem blast_so_unfocus {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {progPtr : BitVec 64} {progBytes : List UInt8}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hso : hdr.slice_off_ptr = cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes))
    (hm : (array (t := i32) hdr.slice_off_ptr sliceOffs ⋆
      blastSoRest cfg hdr progPtr progBytes atomBases aigWords htSlots litsPool R) m) :
    (bytes progPtr progBytes ⋆
      bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m := by
  rw [bvBlastMem_so_focus]; rw [hso] at hm; unfold blastSoRest at hm; exact sep_ac hm

theorem blast_aig_focus {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {progPtr : BitVec 64} {progBytes : List UInt8}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (haig : hdr.aig_ptr = cfg.aig_ptr) (hht : hdr.ht_ptr = cfg.ht_ptr)
    (hm : (bytes progPtr progBytes ⋆
      bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m) :
    ((bvHdrMem cfg.work_base hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots) ⋆
      (bytes progPtr progBytes ⋆
      array (t := i32) (cfg.work_base + 128) atomBases ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
        (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
      array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) sliceOffs ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
        (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
      array (t := i32) cfg.lits_ptr litsPool ⋆
      region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
        (cfg.lits_bytes - 4 * cfg.lits_cap) ⋆ R)) m := by
  rw [haig, hht]; rw [bvBlastMem_aig_frame] at hm; exact sep_ac hm

theorem blast_aig_unfocus {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {progPtr : BitVec 64} {progBytes : List UInt8}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (haig : hdr.aig_ptr = cfg.aig_ptr) (hht : hdr.ht_ptr = cfg.ht_ptr)
    (hm : ((bvHdrMem cfg.work_base hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots) ⋆
      (bytes progPtr progBytes ⋆
      array (t := i32) (cfg.work_base + 128) atomBases ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
        (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
      array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) sliceOffs ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
        (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
      array (t := i32) cfg.lits_ptr litsPool ⋆
      region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
        (cfg.lits_bytes - 4 * cfg.lits_cap) ⋆ R)) m) :
    (bytes progPtr progBytes ⋆
      bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m := by
  rw [bvBlastMem_aig_frame]; rw [haig, hht] at hm; exact sep_ac hm

/-! ## 2. Pure AIG, BitVec & `BlastEvalInv` Helpers -/

theorem bv32_lsr1_toNat (x : BitVec 32) : (x >>> 1).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv32_shl1_atom_lsr1 {x : Nat} (hx : x < 2 ^ 31) :
    ((BitVec.ofNat 32 x <<< (1 : Nat)) >>> 1).toNat = x := by
  rw [bv32_lsr1_toNat, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : x < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : x * 2 ^ 1 < 2 ^ 32)]
  omega

theorem evalLit_shl1_atom (g : Aig) (ρ : Nat → Bool) {x : Nat} (hx : x < 2 ^ 31) :
    g.evalLit ρ (UInt32.ofBitVec (BitVec.ofNat 32 x <<< (1 : Nat))) = g.evalNode ρ x := by
  conv => lhs; unfold Aig.evalLit
  rw [show ((UInt32.ofBitVec (BitVec.ofNat 32 x <<< (1 : Nat))) >>> 1).toNat =
      ((BitVec.ofNat 32 x <<< (1 : Nat)) >>> 1).toNat from rfl, bv32_shl1_atom_lsr1 hx]
  have h1 : (((UInt32.ofBitVec (BitVec.ofNat 32 x <<< (1 : Nat))) &&& 1) != 0) = false := by
    have h0 : (UInt32.ofBitVec (BitVec.ofNat 32 x <<< (1 : Nat)) &&& 1).toNat = 0 := by
      rw [UInt32.toNat_and, show (1 : UInt32).toNat = 1 from rfl,
        show (UInt32.ofBitVec (BitVec.ofNat 32 x <<< (1 : Nat))).toNat =
          (BitVec.ofNat 32 x <<< (1 : Nat)).toNat from rfl,
        BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        Nat.mod_eq_of_lt (by omega : x < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : x * 2 ^ 1 < 2 ^ 32), Nat.and_one_is_mod]
      omega
    have heq : (UInt32.ofBitVec (BitVec.ofNat 32 x <<< (1 : Nat)) &&& 1) = 0 :=
      congrArg UInt32.ofBitVec (BitVec.eq_of_toNat_eq h0)
    rw [heq]; decide
  rw [h1, Bool.xor_false]

theorem evalLit_bit01 (g : Aig) (ρ : Nat → Bool) (b : Bool) :
    g.evalLit ρ (UInt32.ofBitVec (BitVec.ofNat 32 (if b then 1 else 0))) = b := by
  cases b
  · exact Aig.evalLit_zero g ρ
  · exact Aig.evalLit_one g ρ

theorem bv32_bit_word (w : BitVec 32) {j : Nat} :
    ((w >>> j) &&& 1#32) = BitVec.ofNat 32 (if w.toNat.testBit j then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod,
    Nat.testBit_eq_decide_div_mod_eq, BitVec.toNat_ofNat]
  cases h : decide ((w.toNat / 2 ^ j) % 2 = 1)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hne : (w.toNat / 2 ^ j) % 2 ≠ 1 := by simpa using h
    have hm : (w.toNat / 2 ^ j) % 2 = 0 := by omega
    simp [hm]
  · simp only [↓reduceIte]
    have heq : (w.toNat / 2 ^ j) % 2 = 1 := by simpa using h
    simp [heq]

theorem bv32_and31_eq (x : BitVec 32) : (x &&& 31#32).toNat = x.toNat % 32 := by
  rw [BitVec.toNat_and, show (31#32 : BitVec 32).toNat = 31 from rfl]
  simpa using Nat.and_two_pow_sub_one_eq_mod x.toNat 5

theorem bv32_lsr5_eq (x : BitVec 32) : (x >>> (5 : Nat)).toNat = x.toNat / 32 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem sliceDenotes_iff {g : Aig} {ρ : Nat → Bool} {litsPool : List (BitVec 32)}
    {off w : Nat} {v : BitVec w} (hle : off + w ≤ litsPool.length) :
    SliceDenotes g ρ (litsSlice litsPool off w) v ↔
      ∀ j < w, g.evalLit ρ (UInt32.ofBitVec (litsPool.getD (off + j) 0#32)) = v.getLsbD j := by
  unfold SliceDenotes
  rw [litsSlice_length hle]
  refine ⟨fun ⟨_, h⟩ j hj => by simpa only [litsSlice_getD hle hj] using h j hj, fun h => ⟨rfl, ?_⟩⟩
  intro j hj
  rw [litsSlice_getD hle hj]
  exact h j hj

theorem nodeDenotes_set_bv {bs : List UInt8} {nodes : BinTree ProgNode} {g : Aig}
    {sliceOffs litsPool' : List (BitVec 32)} {litsLen' nodeIdx w : Nat}
    {off : BitVec 32} {e : BVExpr w}
    (hnd : nodes.get? nodeIdx = some (.bv w e))
    (hle : off.toNat + w ≤ litsLen')
    (hbd : ∀ j < w,
      ((litsPool'.getD (off.toNat + j) 0#32) >>> 1).toNat < g.A + 1 + g.nodes.size)
    (hsd : ∀ assign : BVExpr.Assignment,
      SliceDenotes g (atomAssign bs assign) (litsSlice litsPool' off.toNat w) (e.eval assign))
    (hso : nodeIdx < sliceOffs.length) :
    NodeDenotes bs nodes g (sliceOffs.set nodeIdx off) litsPool' litsLen' nodeIdx := by
  unfold NodeDenotes
  rw [hnd]
  have hget : (sliceOffs.set nodeIdx off).getD nodeIdx 0#32 = off := by
    simp [List.getD_eq_getElem?_getD, hso]
  simpa only [hget] using ⟨hle, hbd, hsd⟩

theorem nodeDenotes_set_bool {bs : List UInt8} {nodes : BinTree ProgNode} {g : Aig}
    {sliceOffs litsPool : List (BitVec 32)} {litsLen nodeIdx : Nat}
    {lit : BitVec 32} {e : BVLogicalExpr}
    (hnd : nodes.get? nodeIdx = some (.bool e))
    (hbd : (lit >>> 1).toNat < g.A + 1 + g.nodes.size)
    (hev : ∀ assign : BVExpr.Assignment,
      g.evalLit (atomAssign bs assign) (UInt32.ofBitVec lit) = e.eval assign)
    (hso : nodeIdx < sliceOffs.length) :
    NodeDenotes bs nodes g (sliceOffs.set nodeIdx lit) litsPool litsLen nodeIdx := by
  unfold NodeDenotes
  rw [hnd]
  have hget : (sliceOffs.set nodeIdx lit).getD nodeIdx 0#32 = lit := by
    simp [List.getD_eq_getElem?_getD, hso]
  simpa only [hget] using ⟨hbd, hev⟩

theorem list_getD_set_ne {α : Type} (xs : List α) (d : α) {i k : Nat} (v : α)
    (hne : i ≠ k) : (xs.set k v).getD i d = xs.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne.symm]

theorem list_getD_set_self {α : Type} (xs : List α) (d : α) {k : Nat} (v : α)
    (hk : k < xs.length) : (xs.set k v).getD k d = v := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem blastEvalInv_step {cfg : BVWorkspaceCfg} {progPtr : BitVec 64}
    {progBytes : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {hdr hdr' : BVHdrState} {g g' : Aig}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords aigWords' : List (BitVec 64)}
    {htSlots htSlots' litsPool litsPool' : List (BitVec 32)} {k : Nat} {val : BitVec 32}
    (hoom0 : hdr.oom = 0#32)
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      atomBases sliceOffs aigWords htSlots litsPool k)
    (hok' : BVWorkspaceOk cfg hdr' atomBases (sliceOffs.set k val) aigWords' htSlots' litsPool')
    (haig' : AigInv hdr' g' aigWords' htSlots')
    (hext : g ≤ g')
    (hk_lt : k < cfg.n_nodes)
    (hpp : hdr'.prog_ptr = progPtr)
    (hnc : hdr'.n_cwords = hdr.n_cwords)
    (hrt : hdr'.root_node = hdr.root_node)
    (hlits_le : hdr.lits_len.toNat ≤ hdr'.lits_len.toNat)
    (hlits_cap : hdr'.lits_len.toNat ≤ cfg.lits_cap)
    (hagree : ∀ p < hdr.lits_len.toNat, litsPool'.getD p 0#32 = litsPool.getD p 0#32)
    (hnd_k : NodeDenotes progBytes nodes g' (sliceOffs.set k val) litsPool' hdr'.lits_len.toNat k) :
    BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr' g'
      atomBases (sliceOffs.set k val) aigWords' htSlots' litsPool' (k + 1) :=
  { ws_ok := hok'
    parsed := hinv.parsed
    prog_ptr_eq := hpp
    prog_fit := hinv.prog_fit
    nv_eq := hinv.nv_eq
    nn_eq := hinv.nn_eq
    nc_eq := (congrArg BitVec.toNat hnc).trans hinv.nc_eq
    root_eq := (congrArg BitVec.toNat hrt).trans hinv.root_eq
    lits_le_cap := hlits_cap
    aig_inv := haig'
    atoms_eq := hext.1.symm.trans hinv.atoms_eq
    atom_bases_eq := hinv.atom_bases_eq
    k_le := hk_lt
    prefix_ok := fun _ i hi => by
      by_cases hik : i = k
      · subst hik; exact hnd_k
      · have h0 := hinv.prefix_ok hoom0 i (by omega)
        have h1 := NodeDenotes.extend_aig hext
          (by rw [hinv.ws_ok.lits_len]; exact hinv.lits_le_cap) h0
        have h2 := NodeDenotes.extend_lits hlits_le
          (by rw [hinv.ws_ok.lits_len]; exact hinv.lits_le_cap)
          (by rw [hok'.lits_len]; exact hlits_cap) hagree h1
        exact NodeDenotes.extend_slice (list_getD_set_ne sliceOffs 0#32 val hik) h2 }

theorem BVWorkspaceOk.set_sliceOffs {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} (k : Nat) (v : BitVec 32)
    (hok : BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool) :
    BVWorkspaceOk cfg hdr atomBases (sliceOffs.set k v) aigWords htSlots litsPool :=
  { hok with so_len := by simp [hok.so_len] }

theorem BVWorkspaceOk.set_litsPool {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool litsPool' : List (BitVec 32)}
    (hlen : litsPool'.length = cfg.lits_cap)
    (hok : BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool) :
    BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool' :=
  { hok with lits_len := hlen }

theorem bvWorkspaceOk_set_litsLen {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} (nlen : BitVec 32)
    (hok : BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool) :
    BVWorkspaceOk cfg { hdr with lits_len := nlen } atomBases sliceOffs aigWords htSlots litsPool :=
  { hok with }

theorem bvWorkspaceOk_set_oom {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} (noom : BitVec 32)
    (hok : BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool) :
    BVWorkspaceOk cfg { hdr with oom := noom } atomBases sliceOffs aigWords htSlots litsPool :=
  { hok with }

theorem aigInv_set_litsLen {hdr : BVHdrState} {g : Aig} {aigWords : List (BitVec 64)}
    {htSlots : List (BitVec 32)} (nlen : BitVec 32)
    (hinv : AigInv hdr g aigWords htSlots) :
    AigInv { hdr with lits_len := nlen } g aigWords htSlots :=
  { hinv with }

theorem aigInv_set_oom {hdr : BVHdrState} {g : Aig} {aigWords : List (BitVec 64)}
    {htSlots : List (BitVec 32)} (noom : BitVec 32)
    (hinv : AigInv hdr g aigWords htSlots) :
    AigInv { hdr with oom := noom } g aigWords htSlots :=
  { hinv with }

theorem aigInv_aigFrame {hdr hdr' : BVHdrState} {g : Aig} {aigWords : List (BitVec 64)}
    {htSlots : List (BitVec 32)} (hinv : AigInv hdr g aigWords htSlots)
    (hfr : hdr.AigFrame hdr') (hal : hdr'.aig_len = hdr.aig_len) :
    AigInv hdr' g aigWords htSlots :=
  { hinv with
    num_atoms_eq := by rw [hfr.num_atoms]; exact hinv.num_atoms_eq
    aig_len_eq := by rw [hal]; exact hinv.aig_len_eq
    aig_cap_eq := by rw [hfr.aig_cap]; exact hinv.aig_cap_eq
    ht_len := by rw [hfr.ht_mask]; exact hinv.ht_len
    ht_mask_lt := fun x => by rw [hfr.ht_mask]; exact hinv.ht_mask_lt x }

theorem nodes_words_fit {cfg : BVWorkspaceCfg} {progBytes : List UInt8}
    {vars : BinTree VarEntry} {cwords : BinTree Nat} {nodes : BinTree ProgNode}
    {prog : BVLogicalExpr} {hdr : BVHdrState}
    (hp : ParsedBVP1 progBytes vars cwords nodes prog)
    (hnv : cfg.n_vars = u32At progBytes 2)
    (hnn : cfg.n_nodes = u32At progBytes 3)
    (hnc : hdr.n_cwords.toNat = u32At progBytes 4)
    {k : Nat} (hk : k < cfg.n_nodes) :
    4 * (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * (k + 1)) ≤ progBytes.length := by
  have htot := hp.valid.total_len
  unfold nodesOff
  omega

theorem nodesOff_c0_eq {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    (hnv : hdr.n_vars = BitVec.ofNat 32 cfg.n_vars) (hnv_lt : cfg.n_vars < 2 ^ 32) :
    ((8 : BitVec 64) + (hdr.n_vars.setWidth 64 <<< (1 : Nat)) + hdr.n_cwords.setWidth 64).toNat =
      nodesOff cfg.n_vars hdr.n_cwords.toNat := by
  have hnc := hdr.n_cwords.isLt
  unfold nodesOff
  c0_bv_omega [hnv, hnv_lt, hnc]

theorem drv_node_word_ok {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {progBytes : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {nodeIdx : BitVec 32}
    (hp : ParsedBVP1 progBytes vars cwords nodes prog)
    (hnv : cfg.n_vars = u32At progBytes 2)
    (hnn : cfg.n_nodes = u32At progBytes 3)
    (hnc : hdr.n_cwords.toNat = u32At progBytes 4)
    (hnv_hdr : hdr.n_vars = BitVec.ofNat 32 cfg.n_vars)
    (hnv_lt : cfg.n_vars < 2 ^ 32)
    (hni_lt : nodeIdx.toNat < cfg.n_nodes)
    (kv : BitVec 64) (k : Nat) (hkv : kv.toNat = k) (hk : k < 5) :
    let nw := (8 : BitVec 64) + (hdr.n_vars.setWidth 64 <<< (1 : Nat)) + hdr.n_cwords.setWidth 64
    (nw + nodeIdx.setWidth 64 * 5 + kv).toNat =
        nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * nodeIdx.toNat + k ∧
      4 * ((nw + nodeIdx.setWidth 64 * 5 + kv).toNat + 1) ≤ progBytes.length := by
  have hnw := nodesOff_c0_eq hnv_hdr hnv_lt
  have hfit := nodes_words_fit hp hnv hnn hnc hni_lt
  have hi := nodeIdx.isLt
  have hsh : ((8 : BitVec 64) + (hdr.n_vars.setWidth 64 <<< (1 : Nat)) +
      hdr.n_cwords.setWidth 64).toNat =
      nodesOff cfg.n_vars hdr.n_cwords.toNat := hnw
  constructor <;> c0_bv_omega [hsh, hfit, hi, hkv, hk]

theorem drv_node_word0_ok {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {progBytes : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {nodeIdx : BitVec 32}
    (hp : ParsedBVP1 progBytes vars cwords nodes prog)
    (hnv : cfg.n_vars = u32At progBytes 2)
    (hnn : cfg.n_nodes = u32At progBytes 3)
    (hnc : hdr.n_cwords.toNat = u32At progBytes 4)
    (hnv_hdr : hdr.n_vars = BitVec.ofNat 32 cfg.n_vars)
    (hnv_lt : cfg.n_vars < 2 ^ 32)
    (hni_lt : nodeIdx.toNat < cfg.n_nodes) :
    let nw := (8 : BitVec 64) + (hdr.n_vars.setWidth 64 <<< (1 : Nat)) + hdr.n_cwords.setWidth 64
    (nw + nodeIdx.setWidth 64 * 5).toNat =
        nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * nodeIdx.toNat ∧
      4 * ((nw + nodeIdx.setWidth 64 * 5).toNat + 1) ≤ progBytes.length := by
  have h0 := drv_node_word_ok hp hnv hnn hnc hnv_hdr hnv_lt hni_lt 0#64 0 rfl (by decide)
  simpa [BitVec.add_zero] using h0


/-! ## 4. Pure Node-Decoding Helpers for Evaluator -/

theorem bvExpr_not_getLsbD {w : Nat} (e : BVExpr w) (assign : BVExpr.Assignment)
    {j : Nat} (hj : j < w) :
    ((BVExpr.un .not e).eval assign).getLsbD j = !((e.eval assign).getLsbD j) := by
  simp [BVExpr.eval, BVUnOp.eval, hj]

theorem bvLogical_lit_eq_eval {w : Nat} (e1 e2 : BVExpr w) (assign : BVExpr.Assignment) :
    (BVLogicalExpr.literal (.bin e1 .eq e2)).eval assign =
      decide (∀ k < w, (e1.eval assign).getLsbD k = (e2.eval assign).getLsbD k) := by
  simp only [BVLogicalExpr.eval, BVPred.eval, BVBinPred.eval]
  cases h : ((e1.eval assign) == (e2.eval assign))
  · rw [eq_comm, decide_eq_false_iff_not]
    intro hall
    have heq : e1.eval assign = e2.eval assign := BitVec.eq_of_getLsbD_eq hall
    simp [heq] at h
  · rw [eq_comm, decide_eq_true_eq]
    have heq : e1.eval assign = e2.eval assign := beq_iff_eq.mp h
    intro k _; rw [heq]

theorem bvLogical_lit_getLsbD_eval {w : Nat} (e : BVExpr w) (b : Nat)
    (assign : BVExpr.Assignment) :
    (BVLogicalExpr.literal (.getLsbD e b)).eval assign = (e.eval assign).getLsbD b := rfl

theorem bv_decide_eq_ext {w : Nat} (v1 v2 : BitVec w) :
    decide (∀ k < w, v1.getLsbD k = v2.getLsbD k) = (v1 == v2) := by
  cases h : (v1 == v2)
  · rw [decide_eq_false_iff_not]
    intro hall
    have heq : v1 = v2 := BitVec.eq_of_getLsbD_eq hall
    simp [heq] at h
  · rw [decide_eq_true_eq]
    have heq : v1 = v2 := beq_iff_eq.mp h
    intro k _; rw [heq]

theorem nat_blt_eq_decide (a b : Nat) : Nat.blt a b = decide (a < b) := by
  cases h : Nat.blt a b
  · have hnot : ¬ a < b := fun hlt => by rw [Nat.blt_eq.mpr hlt] at h; cases h
    simp [hnot]
  · simp [Nat.blt_eq.mp h]

theorem nat_beq_eq_decide (a b : Nat) : Nat.beq a b = decide (a = b) := by
  cases h : Nat.beq a b
  · have hnot : a ≠ b := fun he => by rw [Nat.beq_eq.mpr he] at h; cases h
    simp [hnot]
  · simp [Nat.beq_eq.mp h]

theorem parsed_node_var {bs : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {k : Nat}
    (hp : ParsedBVP1 bs vars cwords nodes prog) (hk : k < u32At bs 3)
    (hop : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k) = opVar) :
    let nw0 := nodesOff (u32At bs 2) (u32At bs 4)
    let w := u32At bs (nw0 + 5 * k + 1)
    let a := u32At bs (nw0 + 5 * k + 2)
    a < u32At bs 2 ∧ u32At bs (8 + 2 * a + 1) = w ∧
    nodes.get? k = some (.bv w (.var (u32At bs (8 + 2 * a)))) := by
  have hval := hp.valid.nodes_ok k hk
  rw [validNodeAt_var hop] at hval
  dsimp only at hval
  split at hval
  · cases hval
  · have ha : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 2) < u32At bs 2 := by omega
    have hw : u32At bs (8 + 2 * u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 2) + 1) =
        u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) := beq_iff_eq.mp hval
    obtain ⟨nd, hget, hdec, _⟩ := hp.nodes_step k hk
    have hv := hp.vars_get _ ha
    simp only [decodeNode, hop, opVar, nat_blt_eq_decide, nat_beq_eq_decide, hv, hw,
      decide_true] at hdec
    injection hdec with heq
    subst heq
    exact ⟨ha, hw, hget⟩

theorem parsed_node_const {bs : List UInt8} {vars : BinTree VarEntry}
    {cwords : BinTree Nat} {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {k : Nat}
    (hp : ParsedBVP1 bs vars cwords nodes prog) (hk : k < u32At bs 3)
    (hop : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k) = opConst) :
    let nw0 := nodesOff (u32At bs 2) (u32At bs 4)
    let w := u32At bs (nw0 + 5 * k + 1)
    let a := u32At bs (nw0 + 5 * k + 2)
    (0 < (w + 31) / 32 → a ≤ u32At bs 4 ∧ (w + 31) / 32 ≤ u32At bs 4 - a) ∧
    ∃ val : Nat,
      readConstNatAux cwords a ((w + 31) / 32) 0 = some val ∧
      (∀ j < w, (BitVec.ofNat w val).getLsbD j =
        (u32At bs (cwordsOff (u32At bs 2) + a + j / 32)).testBit (j % 32)) ∧
      nodes.get? k = some (.bv w (.const (BitVec.ofNat w val))) := by
  have hval := hp.valid.nodes_ok k hk
  rw [validNodeAt_const hop] at hval
  dsimp only at hval
  have hbound : 0 < (u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) + 31) / 32 →
      u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 2) ≤ u32At bs 4 ∧
      (u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) + 31) / 32 ≤
        u32At bs 4 - u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 2) := by
    intro hpos
    simp only [hpos, ↓reduceIte, decide_eq_true_eq] at hval
    exact hval
  have hcw : ∀ m < (u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) + 31) / 32,
      cwords.get? (u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 2) + m) =
        some (u32At bs (cwordsOff (u32At bs 2) +
          (u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 2) + m))) := by
    intro m hm
    have hb := hbound (by omega)
    exact hp.cwords_get _ (by omega)
  obtain ⟨val, hrc, _⟩ := readConstNatAux_of_cwords
    (cwords := cwords)
    (f := fun m => u32At bs (cwordsOff (u32At bs 2) +
      u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 2) + m))
    (base := u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 2))
    ((u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) + 31) / 32) 0
    (fun m hm => by simpa [Nat.add_assoc] using hcw m hm)
  obtain ⟨nd, hget, hdec, _⟩ := hp.nodes_step k hk
  simp only [decodeNode, hop, opConst, nat_blt_eq_decide, nat_beq_eq_decide, hrc] at hdec
  injection hdec with heq
  subst heq
  refine ⟨hbound, val, hrc, fun j hj => ?_, hget⟩
  exact readConstNatAux_getLsbD (by simpa [Nat.add_assoc] using hcw)
    (fun m _ => u32At_lt ..) hrc hj

theorem parsed_node_not {bs : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {k : Nat}
    (hp : ParsedBVP1 bs vars cwords nodes prog) (hk : k < u32At bs 3)
    (hop : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k) = opNot) :
    let nw0 := nodesOff (u32At bs 2) (u32At bs 4)
    let w := u32At bs (nw0 + 5 * k + 1)
    let a := u32At bs (nw0 + 5 * k + 2)
    a < k ∧ u32At bs (nw0 + 5 * a) < opEq ∧ u32At bs (nw0 + 5 * a + 1) = w ∧
    ∃ ea : BVExpr w,
      nodes.get? a = some (.bv w ea) ∧ nodes.get? k = some (.bv w (.un .not ea)) := by
  have hval := hp.valid.nodes_ok k hk
  rw [validNodeAt_unop (by rw [hop]; unfold opUmod opNot; decide)
    (by rw [hop]; unfold opCpop opNot; decide)] at hval
  dsimp only at hval
  split at hval
  · cases hval
  · rename_i hge
    generalize hw_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) = w
    generalize ha_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 2) = a
    generalize hb_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 3) = b
    generalize hc_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 4) = c
    rw [ha_eq] at hge; rw [ha_eq, hw_eq] at hval
    have ha : a < k := by omega
    simp only [decide_eq_true_eq] at hval
    generalize hwa_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * a + 1) = wa
    rw [hwa_eq] at hval
    obtain ⟨nda, hga, _, hbva, _⟩ := hp.nodes_step a (by omega)
    rw [hwa_eq] at hbva
    obtain ⟨ea, rfl⟩ := hbva hval.1
    have hweq : wa = w := hval.2
    subst hweq
    obtain ⟨nd, hget, hdec, _⟩ := hp.nodes_step k hk
    rw [hw_eq, ha_eq, hb_eq, hc_eq, hop] at hdec
    simp only [decodeNode, mkBvUn, opNot, nat_blt_eq_decide, nat_beq_eq_decide,
      hga, ↓reduceDIte] at hdec
    injection hdec with heq
    subst heq
    subst hw_eq ha_eq
    exact ⟨ha, hval.1, by rw [hwa_eq], ea, hga, hget⟩

theorem parsed_node_getlsbd {bs : List UInt8} {vars : BinTree VarEntry}
    {cwords : BinTree Nat} {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {k : Nat}
    (hp : ParsedBVP1 bs vars cwords nodes prog) (hk : k < u32At bs 3)
    (hop : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k) = opGetLsbD) :
    let nw0 := nodesOff (u32At bs 2) (u32At bs 4)
    let w := u32At bs (nw0 + 5 * k + 1)
    let a := u32At bs (nw0 + 5 * k + 2)
    let b := u32At bs (nw0 + 5 * k + 3)
    let ew := u32At bs (nw0 + 5 * a + 1)
    w = 1 ∧ a < k ∧ u32At bs (nw0 + 5 * a) < opEq ∧
    ∃ ea : BVExpr ew,
      nodes.get? a = some (.bv ew ea) ∧
      nodes.get? k = some (.bool (.literal (.getLsbD ea b))) := by
  have hval := hp.valid.nodes_ok k hk
  have hw1 : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) = 1 := by
    by_cases h : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) = 1
    · exact h
    · rw [validNodeAt_w_ne1 (by rw [hop]; unfold opAshr opGetLsbD; decide)
        (by rw [hop]; unfold opGetLsbD; decide) h] at hval
      cases hval
  rw [validNodeAt_getlsbd hop hw1] at hval
  dsimp only at hval
  split at hval
  · cases hval
  · rename_i hge
    generalize ha_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 2) = a
    generalize hb_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 3) = b
    generalize hc_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 4) = c
    rw [ha_eq] at hge hval
    have ha : a < k := by omega
    simp only [decide_eq_true_eq] at hval
    obtain ⟨nda, hga, _, hbva, _⟩ := hp.nodes_step a (by omega)
    obtain ⟨ea, rfl⟩ := hbva hval
    obtain ⟨nd, hget, hdec, _⟩ := hp.nodes_step k hk
    rw [hop, hw1, ha_eq, hb_eq, hc_eq] at hdec
    simp only [decodeNode, opGetLsbD, nat_blt_eq_decide, nat_beq_eq_decide, hga] at hdec
    injection hdec with heq
    subst heq
    subst ha_eq hb_eq
    exact ⟨hw1, ha, hval, ea, hga, hget⟩

theorem parsed_node_eq {bs : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {k : Nat}
    (hp : ParsedBVP1 bs vars cwords nodes prog) (hk : k < u32At bs 3)
    (hop : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k) = opEq) :
    let nw0 := nodesOff (u32At bs 2) (u32At bs 4)
    let w := u32At bs (nw0 + 5 * k + 1)
    let a := u32At bs (nw0 + 5 * k + 2)
    let b := u32At bs (nw0 + 5 * k + 3)
    let ew := u32At bs (nw0 + 5 * a + 1)
    w = 1 ∧ a < k ∧ b < k ∧ u32At bs (nw0 + 5 * a) < opEq ∧ u32At bs (nw0 + 5 * b) < opEq ∧
    u32At bs (nw0 + 5 * b + 1) = ew ∧
    ∃ (ea eb : BVExpr ew),
      nodes.get? a = some (.bv ew ea) ∧ nodes.get? b = some (.bv ew eb) ∧
      nodes.get? k = some (.bool (.literal (.bin ea .eq eb))) := by
  have hval := hp.valid.nodes_ok k hk
  have hw1 : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) = 1 := by
    by_cases h : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) = 1
    · exact h
    · rw [validNodeAt_w_ne1 (by rw [hop]; unfold opAshr opEq; decide)
        (by rw [hop]; unfold opEq; decide) h] at hval
      cases hval
  rw [validNodeAt_cmp (by rw [hop]; unfold opAshr opEq; decide)
    (by rw [hop]; unfold opUlt opEq; decide) hw1] at hval
  dsimp only at hval
  split at hval
  · cases hval
  · rename_i hor
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at hor
    simp only [decide_eq_true_eq] at hval
    generalize ha_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 2) = a
    generalize hb_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 3) = b
    generalize hc_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 4) = c
    rw [ha_eq, hb_eq] at hor hval
    generalize hewa_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * a + 1) = ewa
    generalize hewb_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * b + 1) = ewb
    rw [hewa_eq, hewb_eq] at hval
    obtain ⟨nda, hga, _, hbva, _⟩ := hp.nodes_step a (by omega)
    rw [hewa_eq] at hbva
    obtain ⟨ea, rfl⟩ := hbva hval.1
    obtain ⟨ndb, hgb, _, hbvb, _⟩ := hp.nodes_step b (by omega)
    rw [hewb_eq] at hbvb
    obtain ⟨eb, rfl⟩ := hbvb hval.2.1
    have hweq : ewb = ewa := hval.2.2.symm
    subst hweq
    obtain ⟨nd, hget, hdec, _⟩ := hp.nodes_step k hk
    rw [hop, hw1, ha_eq, hb_eq, hc_eq] at hdec
    simp only [decodeNode, mkPredBin, opEq, nat_blt_eq_decide, nat_beq_eq_decide,
      hga, hgb, ↓reduceDIte] at hdec
    injection hdec with heq
    subst heq
    subst ha_eq hb_eq hewa_eq
    exact ⟨hw1, hor.1, hor.2, hval.1, hval.2.1, hewb_eq, ea, eb, hga, hgb, hget⟩


theorem bvWorkspaceOk_of_aigFrame {cfg : BVWorkspaceCfg} {hdr hdr' : BVHdrState} {g' : Aig}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords aigWords' : List (BitVec 64)}
    {htSlots htSlots' litsPool : List (BitVec 32)}
    (hok : BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool)
    (hfr : hdr.AigFrame hdr') (haig' : AigInv hdr' g' aigWords' htSlots') :
    BVWorkspaceOk cfg hdr' atomBases sliceOffs aigWords' htSlots' litsPool :=
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
    aig_len_eq := by
      rw [← haig'.aig_cap_eq, hfr.aig_cap, hok.hdr_acap, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by have := hok.acap_lt; omega)
    ht_len := by
      rw [haig'.ht_len, hfr.ht_mask, hok.hdr_htmask, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := hok.ht_lt; omega)]
      have := hok.ht_pos; omega }

theorem bv32_xor1_lsr1 (l : BitVec 32) :
    ((l ^^^ 1#32) >>> (1 : Nat)).toNat = (l >>> (1 : Nat)).toNat := by
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]

theorem evalLit_xor1 (g : Aig) (ρ : Nat → Bool) (l : BitVec 32) :
    g.evalLit ρ (UInt32.ofBitVec (l ^^^ 1#32)) = !(g.evalLit ρ (UInt32.ofBitVec l)) := by
  have hbit0 : ∀ x : BitVec 32, ((x &&& 1#32) != 0#32) = x.getLsbD 0 := by
    intro x
    cases hx : x.getLsbD 0
    · have hzero : x &&& 1#32 = 0#32 := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        by_cases hi0 : i = 0
        · subst hi0; simpa [BitVec.getLsbD_eq_getElem] using hx
        · simp [hi0]
      simp [hzero]
    · have hne : x &&& 1#32 ≠ 0#32 := by
        intro h0
        have := congrArg (fun b : BitVec 32 => b.getLsbD 0) h0
        simp at this
        simp [BitVec.getLsbD_eq_getElem, this] at hx
      simp [hne]
  conv => lhs; unfold Aig.evalLit
  conv => rhs; unfold Aig.evalLit
  have h1 : (((UInt32.ofBitVec (l ^^^ 1#32))) >>> 1).toNat =
      ((UInt32.ofBitVec l) >>> 1).toNat := bv32_xor1_lsr1 l
  have h2 : (((UInt32.ofBitVec (l ^^^ 1#32)) &&& 1) != 0) =
      !(((UInt32.ofBitVec l) &&& 1) != 0) := by
    change (((l ^^^ 1#32) &&& 1#32) != 0#32) = !((l &&& 1#32) != 0#32)
    rw [hbit0, hbit0, BitVec.getLsbD_xor]
    simp
  rw [h1, h2]
  cases g.evalNode ρ ((UInt32.ofBitVec l) >>> 1).toNat <;>
    cases (((UInt32.ofBitVec l) &&& 1) != 0) <;> rfl

theorem list_getD_eq_getElem {α : Type _} (xs : List α) (d : α) {i : Nat}
    (hi : i < xs.length) : xs[i]'hi = xs.getD i d := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem drv_init_post_aigInit {progPtr workBase avail : BitVec 64}
    {progBytes : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {cfg : BVWorkspaceCfg}
    {hdr1 : BVHdrState} {ab so0 lp0 : List (BitVec 32)} {R : Mem 64 → Prop}
    {m' : Mem 64} {Q : Post [.bool]} {nv nn nc rt ac s lcap atomB sliceB litsB : Nat}
    (hp : ParsedBVP1 progBytes vars cwords nodes prog)
    (hprog_fit : progPtr.toNat + progBytes.length < 2 ^ 64)
    (hwb_fit : workBase.toNat + avail.toNat < 2 ^ 64)
    (hcfg_wb : cfg.work_base = workBase) (hcfg_av : cfg.avail = avail.toNat)
    (hcfg_nv : cfg.n_vars = nv) (hcfg_nn : cfg.n_nodes = nn)
    (hcfg_ab_b : cfg.atom_bytes = atomB) (hcfg_sb_b : cfg.slice_bytes = sliceB)
    (hcfg_ac : cfg.aig_cap = ac) (hcfg_hs : cfg.ht_slots = s) (hcfg_lc : cfg.lits_cap = lcap)
    (hcfg_lb : cfg.lits_bytes = litsB)
    (hcfg_ap : cfg.aig_ptr = workBase + BitVec.ofNat 64 (128 + atomB + sliceB))
    (hcfg_hp : cfg.ht_ptr = workBase + BitVec.ofNat 64 (128 + atomB + sliceB) +
      BitVec.ofNat 64 (8 * ac))
    (hcfg_lp : cfg.lits_ptr = workBase + BitVec.ofNat 64 (128 + atomB + sliceB) +
      BitVec.ofNat 64 (8 * ac) + BitVec.ofNat 64 (4 * s))
    (hcfg_tot : 128 + cfg.atom_bytes + cfg.slice_bytes + 8 * cfg.aig_cap + 4 * cfg.ht_slots +
      cfg.lits_bytes = cfg.avail)
    (hatom_al : 4 * nv ≤ atomB) (hslice_al : 4 * nn ≤ sliceB) (hlc_fit : 4 * lcap ≤ litsB)
    (hnv_lt : nv < 2 ^ 32) (hnn_lt : nn < 2 ^ 32) (hnc_lt : nc < 2 ^ 32) (hrt_lt : rt < 2 ^ 32)
    (hac_lt : ac < bvDimacsBound) (hs_pos : 0 < s) (hs_le : s ≤ 2 ^ 30) (hlc_32 : lcap < 2 ^ 32)
    (hnv_def : nv = u32At progBytes 2) (hnn_def : nn = u32At progBytes 3)
    (hnc_def : nc = u32At progBytes 4) (hrt_def : rt = u32At progBytes 5)
    (hcnt_pos : 1 ≤ countAtoms progBytes nv) (hcnt_lt : countAtoms progBytes nv < bvDimacsBound)
    (hnum_lt : countAtoms progBytes nv - 1 < ac)
    (hab_len : ab.length = nv) (hso0_len : so0.length = nn) (hlp0_len : lp0.length = lcap)
    (hpref : ∀ k < nv, (ab.getD k 0#32).toNat = countAtoms progBytes k)
    (hwe_eq : workBase + avail = workBase + BitVec.ofNat 64 cfg.avail)
    (h1_wb : hdr1.work_base = workBase)
    (h1_we : hdr1.work_end = workBase + avail)
    (h1_pp : hdr1.prog_ptr = progPtr) (h1_ab : hdr1.atom_base_ptr = cfg.work_base + 128)
    (h1_so : hdr1.slice_off_ptr = cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes))
    (h1_lp : hdr1.lits_ptr = cfg.lits_ptr) (h1_nv : hdr1.n_vars = BitVec.ofNat 32 nv)
    (h1_nn : hdr1.n_nodes = BitVec.ofNat 32 nn) (h1_nc : hdr1.n_cwords = BitVec.ofNat 32 nc)
    (h1_rt : hdr1.root_node = BitVec.ofNat 32 rt) (h1_lc : hdr1.lits_cap = BitVec.ofNat 32 lcap)
    (h1_ll : hdr1.lits_len = 0#32)
    (ht_mask_lt : ∀ x : BitVec 32,
      (x &&& BitVec.ofNat 32 (s - 1)).toNat < (BitVec.ofNat 32 (s - 1)).toNat + 1)
    (hm' : ((bvHdrMem cfg.work_base { hdr1 with
        aig_ptr := cfg.aig_ptr,
        aig_cap := (BitVec.ofNat 64 ac).setWidth 32,
        ht_ptr := cfg.ht_ptr,
        ht_mask := BitVec.ofNat 32 (s - 1),
        num_atoms := (BitVec.ofNat 64 (countAtoms progBytes
          (BitVec.ofNat 32 (u32At progBytes 2)).toNat) - 1).setWidth 32,
        aig_len := (BitVec.ofNat 64 (countAtoms progBytes
          (BitVec.ofNat 32 (u32At progBytes 2)).toNat) - 1).setWidth 32 + 1#32,
        oom := 0#32 } ⋆
      array (t := i32) cfg.ht_ptr (List.replicate ((BitVec.ofNat 32 (s - 1)).toNat + 1) 0#32)) ⋆
      (bytes progPtr progBytes ⋆
        array (t := i32) (cfg.work_base + 128) ab ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * nv)) (atomB - 4 * nv) ⋆
        array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + atomB)) so0 ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + atomB + 4 * nn)) (sliceB - 4 * nn) ⋆
        region cfg.aig_ptr (8 * ac) ⋆ array (t := i32) cfg.lits_ptr lp0 ⋆
        region (cfg.lits_ptr + BitVec.ofNat 64 (4 * lcap)) (litsB - 4 * lcap) ⋆ R)) m')
    (hFits : bvInitFitsCond progBytes avail.toNat →
      ∀ (cfg' : BVWorkspaceCfg) (hdr' : BVHdrState) (ab' so' : List (BitVec 32))
        (aw' : List (BitVec 64)) (ht' lp' : List (BitVec 32)) (m1 : Mem 64),
        cfg'.work_base = workBase → cfg'.avail = avail.toNat → hdr'.oom = 0#32 →
        BlastEvalInv cfg' progPtr progBytes vars cwords nodes prog hdr'
          ⟨countAtoms progBytes cfg'.n_vars - 1, #[]⟩ ab' so' aw' ht' lp' 0 →
        (bytes progPtr progBytes ⋆ bvBlastMem cfg' hdr' ab' so' aw' ht' lp' ⋆ R) m1 →
        Q (true, ⟨⟩) m1)
    (hNotFits : ¬ bvInitFitsCond progBytes avail.toNat →
      ∀ (cfg' : BVWorkspaceCfg) (hdr' : BVHdrState) (ab' so' : List (BitVec 32))
        (aw' : List (BitVec 64)) (ht' lp' : List (BitVec 32)) (m1 : Mem 64),
        cfg'.work_base = workBase → cfg'.avail = avail.toNat → hdr'.oom = 0#32 →
        BlastEvalInv cfg' progPtr progBytes vars cwords nodes prog hdr'
          ⟨countAtoms progBytes cfg'.n_vars - 1, #[]⟩ ab' so' aw' ht' lp' 0 →
        (bytes progPtr progBytes ⋆ bvBlastMem cfg' hdr' ab' so' aw' ht' lp' ⋆ R) m1 →
        Q (true, ⟨⟩) m1) :
    Q (true, ⟨⟩) m' := by
  have hac_64 : ac < 2 ^ 64 := by unfold bvDimacsBound at hac_lt; omega
  have hcnt_64 : countAtoms progBytes nv < 2 ^ 64 := by unfold bvDimacsBound at hcnt_lt; omega
  have hnv_bv : (BitVec.ofNat 32 (u32At progBytes 2)).toNat = nv := by
    rw [← hnv_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnv_lt]
  have hac_sw : (BitVec.ofNat 64 ac).setWidth 32 = BitVec.ofNat 32 ac := by
    apply BitVec.eq_of_toNat_eq; unfold bvDimacsBound at hac_lt
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hac_64, Nat.mod_eq_of_lt (by omega : ac < 2 ^ 32)]
  have hnum_sw : (BitVec.ofNat 64 (countAtoms progBytes
        (BitVec.ofNat 32 (u32At progBytes 2)).toNat) - 1).setWidth 32 =
      BitVec.ofNat 32 (countAtoms progBytes nv - 1) := by
    rw [hnv_bv]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
        rw [BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt hcnt_64]; exact hcnt_pos)),
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt hcnt_64, Nat.mod_eq_of_lt (by unfold bvDimacsBound at hcnt_lt; omega :
        countAtoms progBytes nv - 1 < 2 ^ 32)]
  let hdr2 : BVHdrState :=
    { hdr1 with
      aig_ptr := cfg.aig_ptr
      aig_cap := BitVec.ofNat 32 ac
      ht_ptr := cfg.ht_ptr
      ht_mask := BitVec.ofNat 32 (s - 1)
      num_atoms := BitVec.ofNat 32 (countAtoms progBytes nv - 1)
      aig_len := BitVec.ofNat 32 (countAtoms progBytes nv - 1) + 1#32
      oom := 0#32 }
  rw [hac_sw, hnum_sw, show { hdr1 with
      aig_ptr := cfg.aig_ptr, aig_cap := BitVec.ofNat 32 ac, ht_ptr := cfg.ht_ptr,
      ht_mask := BitVec.ofNat 32 (s - 1),
      num_atoms := BitVec.ofNat 32 (countAtoms progBytes nv - 1),
      aig_len := BitVec.ofNat 32 (countAtoms progBytes nv - 1) + 1#32,
      oom := 0#32 : BVHdrState } = hdr2 from rfl] at hm'
  have hm_aig_arr : (region cfg.aig_ptr (8 * ac) ⋆
      (bvHdrMem cfg.work_base hdr2 ⋆
        array (t := i32) cfg.ht_ptr (List.replicate ((BitVec.ofNat 32 (s - 1)).toNat + 1) 0#32) ⋆
        bytes progPtr progBytes ⋆ array (t := i32) (cfg.work_base + 128) ab ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * nv)) (atomB - 4 * nv) ⋆
        array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + atomB)) so0 ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + atomB + 4 * nn)) (sliceB - 4 * nn) ⋆
        array (t := i32) cfg.lits_ptr lp0 ⋆
        region (cfg.lits_ptr + BitVec.ofNat 64 (4 * lcap)) (litsB - 4 * lcap) ⋆ R)) m' :=
    sep_ac hm'
  obtain ⟨aw, hx⟩ := sep_ex_l.mp (sep_mono (fun _ h =>
    region_to_array64 ac (by unfold bvDimacsBound at hac_lt; omega) h) hm_aig_arr)
  obtain ⟨haw_len, hm_aw⟩ := sep_pure_l.mp hx
  have hok_fin : BVWorkspaceOk cfg hdr2 ab so0 aw
      (List.replicate ((BitVec.ofNat 32 (s - 1)).toNat + 1) 0#32) lp0 :=
    { fit := by rw [hcfg_wb, hcfg_av]; exact hwb_fit
      hdr_wb := by dsimp only [hdr2]; rw [h1_wb, hcfg_wb]
      hdr_we := by dsimp only [hdr2]; rw [h1_we, hcfg_wb, hwe_eq]
      hdr_ab := by dsimp only [hdr2]; rw [h1_ab]
      hdr_so := by dsimp only [hdr2]; rw [h1_so]
      hdr_aig := rfl
      hdr_ht := rfl
      hdr_lits := by dsimp only [hdr2]; rw [h1_lp]
      hdr_nv := by dsimp only [hdr2]; rw [h1_nv, hcfg_nv]
      hdr_nn := by dsimp only [hdr2]; rw [h1_nn, hcfg_nn]
      hdr_acap := by dsimp only [hdr2]; rw [hcfg_ac]
      hdr_htmask := by dsimp only [hdr2]; rw [hcfg_hs]
      hdr_lcap := by dsimp only [hdr2]; rw [h1_lc, hcfg_lc]
      atom_align := by rw [hcfg_nv, hcfg_ab_b]; exact hatom_al
      slice_align := by rw [hcfg_nn, hcfg_sb_b]; exact hslice_al
      aig_ptr_eq := by rw [hcfg_ap, hcfg_wb, hcfg_ab_b, hcfg_sb_b]
      ht_ptr_eq := by rw [hcfg_hp, hcfg_ap, hcfg_ac]
      lits_ptr_eq := by rw [hcfg_lp, hcfg_hp, hcfg_hs]
      lits_fit := by rw [hcfg_lc, hcfg_lb]; exact hlc_fit
      total_eq := hcfg_tot
      nv_lt := by rw [hcfg_nv]; exact hnv_lt
      nn_lt := by rw [hcfg_nn]; exact hnn_lt
      acap_lt := by rw [hcfg_ac]; exact hac_lt
      ht_pos := by rw [hcfg_hs]; exact hs_pos
      ht_lt := by rw [hcfg_hs]; exact hs_le
      ht_mask_lt := fun x => by
        have h := ht_mask_lt x
        rw [hcfg_hs]
        simp only [BitVec.toNat_and, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : s - 1 < 2 ^ 32)] at h ⊢
        omega
      lcap_lt := by rw [hcfg_lc]; exact hlc_32
      ab_len := by rw [hcfg_nv]; exact hab_len
      so_len := by rw [hcfg_nn]; exact hso0_len
      aig_len_eq := by rw [hcfg_ac]; exact haw_len
      ht_len := by
        rw [List.length_replicate, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : s - 1 < 2 ^ 32), hcfg_hs]; omega
      lits_len := by rw [hcfg_lc]; exact hlp0_len }
  have haig_fin : AigInv hdr2 ⟨countAtoms progBytes cfg.n_vars - 1, #[]⟩ aw
      (List.replicate ((BitVec.ofNat 32 (s - 1)).toNat + 1) 0#32) :=
    { wf := fun _ hi => by cases hi
      num_atoms_eq := by
        rw [hcfg_nv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        unfold bvDimacsBound at hcnt_lt; omega
      aig_len_eq := by
        unfold bvDimacsBound at hcnt_lt
        dsimp only [hdr2]
        rw [hcfg_nv, BitVec.toNat_add, BitVec.toNat_ofNat,
          show (1#32 : BitVec 32).toNat = 1 from rfl,
          show (#[] : Array (UInt32 × UInt32)).size = 0 from rfl,
          Nat.mod_eq_of_lt (by omega : countAtoms progBytes nv - 1 < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : countAtoms progBytes nv - 1 + 1 < 2 ^ 32)]
      aig_len_le_cap := by rw [haw_len, hcfg_nv]; exact hnum_lt
      aig_cap_eq := by
        dsimp only [hdr2]; rw [haw_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        unfold bvDimacsBound at hac_lt; omega
      aig_cap_lt := by rw [haw_len]; exact hac_lt
      gates_bound := by simp
      words_match := ⟨by rw [haw_len, hcfg_nv]; exact hnum_lt, fun _ hi => by cases hi⟩
      ht_len := by dsimp only [hdr2]; simp
      ht_mask_lt := fun x => by
        have h := ht_mask_lt x
        simp only [List.length_replicate, BitVec.toNat_and, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : s - 1 < 2 ^ 32), show hdr2.ht_mask = BitVec.ofNat 32 (s - 1)
            from rfl] at h ⊢
        exact h
      ht_pos := by simp
      ht_bound := by
        rw [List.length_replicate, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : s - 1 < 2 ^ 32)]; omega }
  have hinv_fin : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr2
      ⟨countAtoms progBytes cfg.n_vars - 1, #[]⟩ ab so0 aw
      (List.replicate ((BitVec.ofNat 32 (s - 1)).toNat + 1) 0#32) lp0 0 :=
    { ws_ok := hok_fin
      parsed := hp
      prog_ptr_eq := by dsimp only [hdr2]; rw [h1_pp]
      prog_fit := hprog_fit
      nv_eq := by rw [hcfg_nv, hnv_def]
      nn_eq := by rw [hcfg_nn, hnn_def]
      nc_eq := by
        dsimp only [hdr2]; rw [h1_nc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnc_lt, hnc_def]
      root_eq := by
        dsimp only [hdr2]; rw [h1_rt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrt_lt, hrt_def]
      lits_le_cap := by dsimp only [hdr2]; rw [h1_ll]; simp
      aig_inv := haig_fin
      atoms_eq := rfl
      atom_bases_eq := fun v hv => hpref v (hcfg_nv ▸ hv)
      k_le := Nat.zero_le _
      prefix_ok := fun _ _ hi => absurd hi (Nat.not_lt_zero _) }
  have hm_fin : (bytes progPtr progBytes ⋆ bvBlastMem cfg hdr2 ab so0 aw
      (List.replicate ((BitVec.ofNat 32 (s - 1)).toNat + 1) 0#32) lp0 ⋆ R) m' := by
    rw [bvBlastMem_hdr_left, hcfg_nv, hcfg_nn, hcfg_ab_b, hcfg_sb_b, hcfg_lc, hcfg_lb]
    exact sep_ac hm_aw
  by_cases hfc : bvInitFitsCond progBytes avail.toNat
  · exact hFits hfc cfg hdr2 ab so0 aw
      (List.replicate ((BitVec.ofNat 32 (s - 1)).toNat + 1) 0#32) lp0 m'
      hcfg_wb hcfg_av rfl hinv_fin hm_fin
  · exact hNotFits hfc cfg hdr2 ab so0 aw
      (List.replicate ((BitVec.ofNat 32 (s - 1)).toNat + 1) 0#32) lp0 m'
      hcfg_wb hcfg_av rfl hinv_fin hm_fin

end

end LeanQbe.T.Examples.Bitblast.Proof
