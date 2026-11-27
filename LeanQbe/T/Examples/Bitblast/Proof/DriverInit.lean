/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.Specs
import LeanQbe.T.Examples.Bitblast.Proof.DriverHelpers
import LeanQbe.T.Examples.Bitblast.Proof.Validate0
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas

/-!
# Workspace Initializer WP Proof (`Bitblast.Proof.DriverInit`)

Proves `bv_init_workspace_wp` (`bvInitWorkspaceSpec`), including `bvInitFitsCond` sufficiency,
`ht_slots` budget loop, region partitioning into `bvBlastMem`, `atom_base` prefix-sum
initialization, and `bv_aig_init` handoff into `BlastEvalInv ... 0`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open Std
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Bitblast.Src
open LeanQbe.T.Examples.Bitblast.Src.Driver
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Ref.BVProg

/-! ## 1. Local Memory Access Helpers (`BVHdr`, `array i32`) -/

private def upd_work_base (s : BVHdrState) (v : BitVec 64) : BVHdrState :=
  { s with work_base := v }
private def upd_work_end (s : BVHdrState) (v : BitVec 64) : BVHdrState :=
  { s with work_end := v }
private def upd_prog_ptr (s : BVHdrState) (v : BitVec 64) : BVHdrState :=
  { s with prog_ptr := v }
private def upd_atom_base_ptr (s : BVHdrState) (v : BitVec 64) : BVHdrState :=
  { s with atom_base_ptr := v }
private def upd_slice_off_ptr (s : BVHdrState) (v : BitVec 64) : BVHdrState :=
  { s with slice_off_ptr := v }
private def upd_lits_ptr (s : BVHdrState) (v : BitVec 64) : BVHdrState :=
  { s with lits_ptr := v }
private def upd_marks_ptr (s : BVHdrState) (v : BitVec 64) : BVHdrState :=
  { s with marks_ptr := v }
private def upd_dimacs_start (s : BVHdrState) (v : BitVec 64) : BVHdrState :=
  { s with dimacs_start := v }
private def upd_n_vars (s : BVHdrState) (v : BitVec 32) : BVHdrState :=
  { s with n_vars := v }
private def upd_n_nodes (s : BVHdrState) (v : BitVec 32) : BVHdrState :=
  { s with n_nodes := v }
private def upd_n_cwords (s : BVHdrState) (v : BitVec 32) : BVHdrState :=
  { s with n_cwords := v }
private def upd_root_node (s : BVHdrState) (v : BitVec 32) : BVHdrState :=
  { s with root_node := v }
private def upd_lits_len (s : BVHdrState) (v : BitVec 32) : BVHdrState :=
  { s with lits_len := v }
private def upd_lits_cap (s : BVHdrState) (v : BitVec 32) : BVHdrState :=
  { s with lits_cap := v }
private def upd_dimacs_len (s : BVHdrState) (v : BitVec 32) : BVHdrState :=
  { s with dimacs_len := v }

private def updHdr15 (s : BVHdrState) (wb we pp ab so lp : BitVec 64)
    (nv nn nc rt lc : BitVec 32) : BVHdrState :=
  { work_base := wb, work_end := we, prog_ptr := pp, aig_ptr := s.aig_ptr, ht_ptr := s.ht_ptr,
    atom_base_ptr := ab, slice_off_ptr := so, lits_ptr := lp, marks_ptr := (0 : BitVec 64),
    dimacs_start := (0 : BitVec 64), n_vars := nv, n_nodes := nn, n_cwords := nc,
    root_node := rt, num_atoms := s.num_atoms, aig_len := s.aig_len, aig_cap := s.aig_cap,
    ht_mask := s.ht_mask, lits_len := (0 : BitVec 32), lits_cap := lc, oom := s.oom,
    dimacs_len := (0 : BitVec 32) }

private theorem upd15_eq (s : BVHdrState) (wb we pp ab so lp : BitVec 64)
    (nv nn nc rt lc : BitVec 32) :
    upd_dimacs_len (upd_lits_cap (upd_lits_len (upd_root_node (upd_n_cwords (upd_n_nodes
      (upd_n_vars (upd_dimacs_start (upd_marks_ptr (upd_lits_ptr (upd_slice_off_ptr
        (upd_atom_base_ptr (upd_prog_ptr (upd_work_end (upd_work_base s wb) we) pp)
          ab) so) lp) (0 : BitVec 64)) (0 : BitVec 64)) nv) nn) nc) rt) (0 : BitVec 32))
      lc) (0 : BitVec 32) =
    updHdr15 s wb we pp ab so lp nv nn nc rt lc := by
  cases s; rfl

@[local c0_load] private theorem init_load_atom_base_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 40) = some s.atom_base_ptr := load_hdr_atom_base_ptr hm

@[local c0_store] private theorem init_store_work_base {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i64 h ∧ (bvHdrMem h (upd_work_base s v) ⋆ R) (storeMem m i64 h v) :=
  store_hdr_work_base v hm

@[local c0_store] private theorem init_store_work_end {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i64 (h + 8) ∧
      (bvHdrMem h (upd_work_end s v) ⋆ R) (storeMem m i64 (h + 8) v) :=
  store_hdr_work_end v hm

@[local c0_store] private theorem init_store_prog_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i64 (h + 16) ∧
      (bvHdrMem h (upd_prog_ptr s v) ⋆ R) (storeMem m i64 (h + 16) v) :=
  store_hdr_prog_ptr v hm

@[local c0_store] private theorem init_store_atom_base_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i64 (h + 40) ∧
      (bvHdrMem h (upd_atom_base_ptr s v) ⋆ R) (storeMem m i64 (h + 40) v) :=
  store_hdr_atom_base_ptr v hm

@[local c0_store] private theorem init_store_slice_off_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i64 (h + 48) ∧
      (bvHdrMem h (upd_slice_off_ptr s v) ⋆ R) (storeMem m i64 (h + 48) v) :=
  store_hdr_slice_off_ptr v hm

@[local c0_store] private theorem init_store_lits_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i64 (h + 56) ∧
      (bvHdrMem h (upd_lits_ptr s v) ⋆ R) (storeMem m i64 (h + 56) v) :=
  store_hdr_lits_ptr v hm

@[local c0_store] private theorem init_store_marks_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i64 (h + 64) ∧
      (bvHdrMem h (upd_marks_ptr s v) ⋆ R) (storeMem m i64 (h + 64) v) :=
  store_hdr_marks_ptr v hm

@[local c0_store] private theorem init_store_dimacs_start {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i64 (h + 72) ∧
      (bvHdrMem h (upd_dimacs_start s v) ⋆ R) (storeMem m i64 (h + 72) v) :=
  store_hdr_dimacs_start v hm

@[local c0_store] private theorem init_store_n_vars {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 80) ∧
      (bvHdrMem h (upd_n_vars s v) ⋆ R) (storeMem m i32 (h + 80) v) :=
  store_hdr_n_vars v hm

@[local c0_store] private theorem init_store_n_nodes {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 84) ∧
      (bvHdrMem h (upd_n_nodes s v) ⋆ R) (storeMem m i32 (h + 84) v) :=
  store_hdr_n_nodes v hm

@[local c0_store] private theorem init_store_n_cwords {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 88) ∧
      (bvHdrMem h (upd_n_cwords s v) ⋆ R) (storeMem m i32 (h + 88) v) :=
  store_hdr_n_cwords v hm

@[local c0_store] private theorem init_store_root_node {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 92) ∧
      (bvHdrMem h (upd_root_node s v) ⋆ R) (storeMem m i32 (h + 92) v) :=
  store_hdr_root_node v hm

@[local c0_store] private theorem init_store_lits_len {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 112) ∧
      (bvHdrMem h (upd_lits_len s v) ⋆ R) (storeMem m i32 (h + 112) v) :=
  store_hdr_lits_len v hm

@[local c0_store] private theorem init_store_lits_cap {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 116) ∧
      (bvHdrMem h (upd_lits_cap s v) ⋆ R) (storeMem m i32 (h + 116) v) :=
  store_hdr_lits_cap v hm

@[local c0_store] private theorem init_store_dimacs_len {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 124) ∧
      (bvHdrMem h (upd_dimacs_len s v) ⋆ R) (storeMem m i32 (h + 124) v) :=
  store_hdr_dimacs_len v hm

private theorem init_bv32_shl2_add_eq (base : BitVec 64) (idx : BitVec 32) :
    base + (idx.setWidth 64 <<< (2 : Nat)) = base + BitVec.ofNat 64 (4 * idx.toNat) := by
  congr 1; apply BitVec.eq_of_toNat_eq
  have hi32 := idx.isLt
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : idx.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : idx.toNat * 2 ^ 2 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 4 * idx.toNat < 2 ^ 64)]
  omega

@[local c0_store] private theorem init_store_array32_shl2 {base : BitVec 64} {idx : BitVec 32}
    {sh : Nat} {xs : List (BitVec 32)} (v : BitVec 32) {R : Mem 64 → Prop} {m : Mem 64}
    (hsh : sh = 2) (hi : idx.toNat < xs.length) (hm : (array (t := i32) base xs ⋆ R) m) :
    storeOk m i32 (base + (idx.setWidth 64 <<< sh)) ∧
      (array (t := i32) base (xs.set idx.toNat v) ⋆ R)
        (storeMem m i32 (base + (idx.setWidth 64 <<< sh)) v) := by
  subst hsh; rw [init_bv32_shl2_add_eq]
  exact store_array (t := i32) v (by decide) hi hm

/-! ## 2. Pure BitVec / Alignment / `region` Workspace Partition Helpers -/

private theorem bv64_and_not7_eq (a : BitVec 64) :
    a &&& (~~~7#64) = (a >>> (3 : Nat)) <<< (3 : Nat) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases i with _ | _ | _ | k
  · simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, show (0 : Nat) < 64 by decide, show (0 : Nat) < 3 by decide,
      show (7#64 : BitVec 64).getLsbD 0 = true from rfl, decide_true, Bool.not_true,
      Bool.and_false, Bool.false_and]
  · simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, show (1 : Nat) < 64 by decide, show (1 : Nat) < 3 by decide,
      show (7#64 : BitVec 64).getLsbD 1 = true from rfl, decide_true, Bool.not_true,
      Bool.and_false, Bool.false_and]
  · simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, show (2 : Nat) < 64 by decide, show (2 : Nat) < 3 by decide,
      show (7#64 : BitVec 64).getLsbD 2 = true from rfl, decide_true, Bool.not_true,
      Bool.and_false, Bool.false_and]
  · have h3k : k + 1 + 1 + 1 = 3 + k := by omega
    have hgt : ¬ 3 + k < 3 := by omega
    have hsub : 3 + k - 3 = k := by omega
    have hlt64 : 3 + k < 64 := by omega
    have h7 : (7#64 : BitVec 64).getLsbD (3 + k) = false := by
      rw [BitVec.getLsbD, show (7#64 : BitVec 64).toNat = 7 from rfl,
        Nat.testBit_eq_decide_div_mod_eq,
        Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (by decide : 7 < 2 ^ 3)
          (Nat.pow_le_pow_right (by omega) (by omega : 3 ≤ 3 + k)))]
      decide
    rw [h3k]
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, decide_eq_true hlt64, decide_eq_false hgt, hsub, h7,
      Bool.not_false, Bool.and_true, Bool.true_and]

private theorem bv64_align8_eq (x : BitVec 32) :
    (((x.setWidth 64 <<< (2 : Nat)) + 7#64) &&& (~~~7#64)).toNat = align8 (4 * x.toNat) := by
  have hx := x.isLt
  have hy_lt : 4 * x.toNat + 7 < 2 ^ 64 := by omega
  have hy_eq : ((x.setWidth 64 <<< (2 : Nat)) + 7#64).toNat = 4 * x.toNat + 7 := by
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
      show (7#64 : BitVec 64).toNat = 7 from rfl, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : x.toNat * 2 ^ 2 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : x.toNat * 4 + 7 < 2 ^ 64)]
    omega
  rw [bv64_and_not7_eq, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, hy_eq,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hm_lt : ((4 * x.toNat + 7) / 2 ^ 3) * 2 ^ 3 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hm_lt]
  unfold align8; omega

private theorem bv64_align8_u32 (x : Nat) (hx : x < 2 ^ 32) :
    (BitVec.setWidth 64 (BitVec.ofNat 32 x) <<< 2 + 7#64 &&& ~~~7#64).toNat =
      align8 (4 * x) := by
  rw [bv64_align8_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

private theorem bv64_align8_raw (x : Nat) (hx : x < 2 ^ 32) :
    (BitVec.setWidth 64 (BitVec.ofNat 32 x) <<< OfNat.ofNat 2 + (7 : BitVec 64) &&&
      ~~~(7 : BitVec 64)).toNat = align8 (4 * x) :=
  bv64_align8_u32 x hx

private theorem align8_ge (n : Nat) : n ≤ align8 n := by
  unfold align8; omega

private theorem align8_lt_of_u32 (x : Nat) (hx : x < 2 ^ 32) :
    align8 (4 * x) < 2 ^ 35 := by
  unfold align8; omega

private theorem bv64_pow2_mask_lt {s : Nat} (hs_pow : ∃ p, s = 2 ^ p) (hs_pos : 0 < s)
    (hs_le : s ≤ 2 ^ 30) (x : BitVec 32) :
    (x &&& BitVec.ofNat 32 (s - 1)).toNat < s := by
  obtain ⟨p, rfl⟩ := hs_pow
  have hp_lt : 2 ^ p - 1 < 2 ^ 32 := by omega
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp_lt,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ hs_pos

private theorem bv_ofNat_add_64 (a : BitVec 64) (x y : Nat) :
    a + BitVec.ofNat 64 x + BitVec.ofNat 64 y = a + BitVec.ofNat 64 (x + y) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

private theorem bv_init_fixed_raw (nv nn : Nat) (hnv : nv < 2 ^ 32) (hnn : nn < 2 ^ 32) :
    (BitVec.toNat (128 : BitVec 64) +
      (BitVec.setWidth 64 (BitVec.ofNat 32 nv) <<< OfNat.ofNat 2 + 7 &&& ~~~7).toNat +
      (BitVec.setWidth 64 (BitVec.ofNat 32 nn) <<< OfNat.ofNat 2 + 7 &&& ~~~7).toNat) %
      2 ^ 64 = 128 + align8 (4 * nv) + align8 (4 * nn) := by
  have ha := align8_lt_of_u32 nv hnv
  have hs := align8_lt_of_u32 nn hnn
  rw [show BitVec.toNat (128 : BitVec 64) = 128 from rfl,
    bv64_align8_raw nv hnv, bv64_align8_raw nn hnn,
    Nat.mod_eq_of_lt (by omega : 128 + align8 (4 * nv) + align8 (4 * nn) < 2 ^ 64)]

private theorem bv_init_so_eq (wb : BitVec 64) (nv nn av : Nat)
    (hnv : nv < 2 ^ 32) (hnn : nn < 2 ^ 32)
    (hfit : wb.toNat + av < 2 ^ 64)
    (hrem : 128 + align8 (4 * nv) + align8 (4 * nn) + 64 ≤ av) :
    wb + (128 : BitVec 64) +
      ((BitVec.ofNat 32 nv).setWidth 64 <<< OfNat.ofNat 2 + (7 : BitVec 64) &&&
        ~~~(7 : BitVec 64)) =
    wb + BitVec.ofNat 64 (128 + align8 (4 * nv)) := by
  have ha := align8_lt_of_u32 nv hnv
  have hs := align8_lt_of_u32 nn hnn
  have hwb := wb.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add,
    show (128 : BitVec 64).toNat = 128 from rfl, bv64_align8_raw nv hnv,
    Nat.mod_eq_of_lt (by omega : wb.toNat + 128 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : wb.toNat + 128 + align8 (4 * nv) < 2 ^ 64),
    BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 128 + align8 (4 * nv) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : wb.toNat + (128 + align8 (4 * nv)) < 2 ^ 64)]
  omega

private theorem bv_init_aig_eq (wb : BitVec 64) (nv nn av : Nat)
    (hnv : nv < 2 ^ 32) (hnn : nn < 2 ^ 32)
    (hfit : wb.toNat + av < 2 ^ 64)
    (hrem : 128 + align8 (4 * nv) + align8 (4 * nn) + 64 ≤ av) :
    wb + ((128 : BitVec 64) +
      ((BitVec.ofNat 32 nv).setWidth 64 <<< OfNat.ofNat 2 + (7 : BitVec 64) &&&
        ~~~(7 : BitVec 64)) +
      ((BitVec.ofNat 32 nn).setWidth 64 <<< OfNat.ofNat 2 + (7 : BitVec 64) &&&
        ~~~(7 : BitVec 64))) =
    wb + BitVec.ofNat 64 (128 + align8 (4 * nv) + align8 (4 * nn)) := by
  have ha := align8_lt_of_u32 nv hnv
  have hs := align8_lt_of_u32 nn hnn
  have hwb := wb.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add,
    show (128 : BitVec 64).toNat = 128 from rfl,
    bv64_align8_raw nv hnv, bv64_align8_raw nn hnn,
    Nat.mod_eq_of_lt (by omega : 128 + align8 (4 * nv) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 128 + align8 (4 * nv) + align8 (4 * nn) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : wb.toNat + (128 + align8 (4 * nv) + align8 (4 * nn)) < 2 ^ 64),
    BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 128 + align8 (4 * nv) + align8 (4 * nn) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : wb.toNat + (128 + align8 (4 * nv) + align8 (4 * nn)) < 2 ^ 64)]

private theorem bv_init_lits_eq (aigPtr : BitVec 64) (ac s : Nat)
    (hac : ac < 2 ^ 60) (hs : s < 2 ^ 61) :
    aigPtr + (BitVec.ofNat 64 ac <<< OfNat.ofNat 3) + (BitVec.ofNat 64 s <<< OfNat.ofNat 2) =
    aigPtr + BitVec.ofNat 64 (8 * ac) + BitVec.ofNat 64 (4 * s) := by
  have h1 : BitVec.ofNat 64 ac <<< OfNat.ofNat 3 = BitVec.ofNat 64 (8 * ac) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega : ac < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : ac * 2 ^ 3 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 8 * ac < 2 ^ 64)]
    omega
  have h2 : BitVec.ofNat 64 s <<< OfNat.ofNat 2 = BitVec.ofNat 64 (4 * s) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega : s < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : s * 2 ^ 2 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 4 * s < 2 ^ 64)]
    omega
  rw [h1, h2]

private theorem bv_init_acap_raw (avail : BitVec 64) (nv nn : Nat)
    (hnv : nv < 2 ^ 32) (hnn : nn < 2 ^ 32)
    (hrem : 128 + align8 (4 * nv) + align8 (4 * nn) + 64 ≤ avail.toNat) :
    (avail - ((128 : BitVec 64) +
      (BitVec.setWidth 64 (BitVec.ofNat 32 nv) <<< OfNat.ofNat 2 +
        (7 : BitVec 64) &&& ~~~(7 : BitVec 64)) +
      (BitVec.setWidth 64 (BitVec.ofNat 32 nn) <<< OfNat.ofNat 2 +
        (7 : BitVec 64) &&& ~~~(7 : BitVec 64)))) >>> OfNat.ofNat 4 =
    BitVec.ofNat 64 ((avail.toNat - (128 + align8 (4 * nv) + align8 (4 * nn))) / 16) := by
  have ha := align8_lt_of_u32 nv hnv
  have hs := align8_lt_of_u32 nn hnn
  have hav := avail.isLt
  have hadd_eq : ((128 : BitVec 64) +
      (BitVec.setWidth 64 (BitVec.ofNat 32 nv) <<< OfNat.ofNat 2 +
        (7 : BitVec 64) &&& ~~~(7 : BitVec 64)) +
      (BitVec.setWidth 64 (BitVec.ofNat 32 nn) <<< OfNat.ofNat 2 +
        (7 : BitVec 64) &&& ~~~(7 : BitVec 64))).toNat =
      128 + align8 (4 * nv) + align8 (4 * nn) := by
    rw [BitVec.toNat_add, BitVec.toNat_add,
      show (128 : BitVec 64).toNat = 128 from rfl,
      bv64_align8_raw nv hnv, bv64_align8_raw nn hnn,
      Nat.mod_eq_of_lt (by omega : 128 + align8 (4 * nv) < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 128 + align8 (4 * nv) + align8 (4 * nn) < 2 ^ 64)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hadd_eq]; omega)),
    hadd_eq, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega :
      (avail.toNat - (128 + align8 (4 * nv) + align8 (4 * nn))) / 2 ^ 4 < 2 ^ 64)]

private theorem bv_init_lcap_raw (wb avail : BitVec 64) (nv nn ac s : Nat)
    (hnv : nv < 2 ^ 32) (hnn : nn < 2 ^ 32)
    (hac : ac < 2 ^ 60) (hs : s < 2 ^ 61)
    (hwb : wb.toNat + avail.toNat < 2 ^ 64)
    (hrem : 128 + align8 (4 * nv) + align8 (4 * nn) + 64 ≤ avail.toNat)
    (hle : 8 * ac + 4 * s ≤ avail.toNat - (128 + align8 (4 * nv) + align8 (4 * nn))) :
    (wb + avail -
      (wb + ((128 : BitVec 64) +
        ((BitVec.ofNat 32 nv).setWidth 64 <<< OfNat.ofNat 2 + (7 : BitVec 64) &&&
          ~~~(7 : BitVec 64)) +
        ((BitVec.ofNat 32 nn).setWidth 64 <<< OfNat.ofNat 2 + (7 : BitVec 64) &&&
          ~~~(7 : BitVec 64))) +
        (BitVec.ofNat 64 ac <<< OfNat.ofNat 3) +
        (BitVec.ofNat 64 s <<< OfNat.ofNat 2))) >>> OfNat.ofNat 2 =
    BitVec.ofNat 64 ((avail.toNat - (128 + align8 (4 * nv) + align8 (4 * nn)) -
      (8 * ac + 4 * s)) / 4) := by
  have ha := align8_lt_of_u32 nv hnv
  have hbs := align8_lt_of_u32 nn hnn
  have hwb_lt := wb.isLt
  have hav_lt := avail.isLt
  rw [bv_init_aig_eq wb nv nn avail.toNat hnv hnn hwb hrem,
    bv_init_lits_eq _ ac s hac hs]
  have hwe : (wb + avail).toNat = wb.toNat + avail.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hwb]
  have hlp : (wb + BitVec.ofNat 64 (128 + align8 (4 * nv) + align8 (4 * nn)) +
      BitVec.ofNat 64 (8 * ac) + BitVec.ofNat 64 (4 * s)).toNat =
      wb.toNat + (128 + align8 (4 * nv) + align8 (4 * nn)) + (8 * ac + 4 * s) := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 128 + align8 (4 * nv) + align8 (4 * nn) < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : wb.toNat + (128 + align8 (4 * nv) + align8 (4 * nn)) < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 8 * ac < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega :
        wb.toNat + (128 + align8 (4 * nv) + align8 (4 * nn)) + 8 * ac < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 4 * s < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega :
        wb.toNat + (128 + align8 (4 * nv) + align8 (4 * nn)) + 8 * ac + 4 * s < 2 ^ 64)]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight,
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hwe, hlp]; omega)),
    hwe, hlp, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by
      omega : (avail.toNat - (128 + align8 (4 * nv) + align8 (4 * nn)) -
        (8 * ac + 4 * s)) / 2 ^ 2 < 2 ^ 64)]
  congr 1; omega

private theorem bv_init_lcap_c0_nat (wb avail : BitVec 64) (nv nn ac s : Nat)
    (hnv : nv < 2 ^ 32) (hnn : nn < 2 ^ 32) (hac : ac < 2 ^ 60) (hs : s < 2 ^ 61)
    (hwb : wb.toNat + avail.toNat < 2 ^ 64)
    (hrem : 128 + align8 (4 * nv) + align8 (4 * nn) + 64 ≤ avail.toNat)
    (hle : 8 * ac + 4 * s ≤ avail.toNat - (128 + align8 (4 * nv) + align8 (4 * nn))) :
    (2 ^ 64 - (wb.toNat + (BitVec.toNat (128 : BitVec 64) +
        (BitVec.setWidth 64 (BitVec.ofNat 32 nv) <<< OfNat.ofNat 2 + 7 &&& ~~~7).toNat +
        (BitVec.setWidth 64 (BitVec.ofNat 32 nn) <<< OfNat.ofNat 2 + 7 &&& ~~~7).toNat) +
        ac % 2 ^ 64 * 2 ^ OfNat.ofNat 3 + s % 2 ^ 64 * 2 ^ OfNat.ofNat 2) % 2 ^ 64 +
      (wb.toNat + avail.toNat)) % 2 ^ 64 / 2 ^ OfNat.ofNat 2 =
    (avail.toNat - (128 + align8 (4 * nv) + align8 (4 * nn)) - (8 * ac + 4 * s)) / 4 := by
  have ha := align8_lt_of_u32 nv hnv
  have hbs := align8_lt_of_u32 nn hnn
  have hwb_lt := wb.isLt
  have hav_lt := avail.isLt
  rw [show BitVec.toNat (128 : BitVec 64) = 128 from rfl,
    bv64_align8_raw nv hnv, bv64_align8_raw nn hnn,
    Nat.mod_eq_of_lt (by omega : ac < 2 ^ 64), Nat.mod_eq_of_lt (by omega : s < 2 ^ 64),
    show (2 ^ OfNat.ofNat 3 : Nat) = 8 from rfl,
    show (2 ^ OfNat.ofNat 2 : Nat) = 4 from rfl,
    Nat.mod_eq_of_lt (by omega :
      wb.toNat + (128 + align8 (4 * nv) + align8 (4 * nn)) + ac * 8 + s * 4 < 2 ^ 64)]
  have hdiff : 2 ^ 64 - (wb.toNat + (128 + align8 (4 * nv) + align8 (4 * nn)) + ac * 8 + s * 4) +
      (wb.toNat + avail.toNat) =
      2 ^ 64 + (avail.toNat - (128 + align8 (4 * nv) + align8 (4 * nn)) - (8 * ac + 4 * s)) := by
    omega
  rw [hdiff, Nat.add_mod_left,
    Nat.mod_eq_of_lt (by omega :
      avail.toNat - (128 + align8 (4 * nv) + align8 (4 * nn)) - (8 * ac + 4 * s) < 2 ^ 64)]

private theorem region_split_initWorkspace (cfg : BVWorkspaceCfg) (m : Mem 64)
    (hfit : cfg.work_base.toNat + cfg.avail < 2 ^ 64)
    (htot : 128 + cfg.atom_bytes + cfg.slice_bytes + 8 * cfg.aig_cap +
      4 * cfg.ht_slots + cfg.lits_bytes = cfg.avail)
    (ha_al : 4 * cfg.n_vars ≤ cfg.atom_bytes)
    (hs_al : 4 * cfg.n_nodes ≤ cfg.slice_bytes)
    (hl_fit : 4 * cfg.lits_cap ≤ cfg.lits_bytes)
    (haig_ptr :
      cfg.aig_ptr = cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + cfg.slice_bytes))
    (hht_ptr : cfg.ht_ptr = cfg.aig_ptr + BitVec.ofNat 64 (8 * cfg.aig_cap))
    (hlits_ptr : cfg.lits_ptr = cfg.ht_ptr + BitVec.ofNat 64 (4 * cfg.ht_slots))
    (hnv : cfg.n_vars < 2 ^ 32) (hnn : cfg.n_nodes < 2 ^ 32)
    (hacap : cfg.aig_cap < 2 ^ 28) (hht : cfg.ht_slots ≤ 2 ^ 30)
    (hlcap : cfg.lits_cap < 2 ^ 32)
    (hm : region cfg.work_base cfg.avail m) :
    ∃ (hdr0 : BVHdrState) (ab0 so0 ht0 lp0 : List (BitVec 32)),
      ab0.length = cfg.n_vars ∧ so0.length = cfg.n_nodes ∧
      ht0.length = cfg.ht_slots ∧ lp0.length = cfg.lits_cap ∧
      (bvHdrMem cfg.work_base hdr0 ⋆
        array (t := i32) (cfg.work_base + 128) ab0 ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
          (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
        array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) so0 ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
          (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
        region cfg.aig_ptr (8 * cfg.aig_cap) ⋆
        array (t := i32) cfg.ht_ptr ht0 ⋆
        array (t := i32) cfg.lits_ptr lp0 ⋆
        region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
          (cfg.lits_bytes - 4 * cfg.lits_cap)) m := by
  let tail := cfg.slice_bytes + (8 * cfg.aig_cap + (4 * cfg.ht_slots + cfg.lits_bytes))
  have hm1 : (region cfg.work_base 128 ⋆
      region (cfg.work_base + 128) (cfg.atom_bytes + tail)) m :=
    (congrFun (region_merge_eq (a := cfg.work_base) (n1 := 128)
      (n2 := cfg.atom_bytes + tail) (n := cfg.avail) (by omega) (by omega)) m).mpr hm
  have hm_asa : region (cfg.work_base + 128) (cfg.atom_bytes + tail) =
      (region (cfg.work_base + 128) cfg.atom_bytes ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) tail) := by
    rw [← bv_ofNat_add_64 cfg.work_base 128 cfg.atom_bytes]
    exact (region_merge_eq rfl (by omega)).symm
  have hm_atom : region (cfg.work_base + 128) cfg.atom_bytes =
      (region (cfg.work_base + 128) (4 * cfg.n_vars) ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
          (cfg.atom_bytes - 4 * cfg.n_vars)) := by
    rw [← bv_ofNat_add_64 cfg.work_base 128 (4 * cfg.n_vars)]
    exact (region_merge_eq (n := cfg.atom_bytes) (by omega) (by omega)).symm
  have hm_sa : region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) tail =
      (region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) cfg.slice_bytes ⋆
        region cfg.aig_ptr (8 * cfg.aig_cap + (4 * cfg.ht_slots + cfg.lits_bytes))) := by
    rw [haig_ptr, ← bv_ofNat_add_64 cfg.work_base (128 + cfg.atom_bytes) cfg.slice_bytes]
    exact (region_merge_eq rfl (by omega)).symm
  have hm_slice : region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) cfg.slice_bytes =
      (region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) (4 * cfg.n_nodes) ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
          (cfg.slice_bytes - 4 * cfg.n_nodes)) := by
    rw [← bv_ofNat_add_64 cfg.work_base (128 + cfg.atom_bytes) (4 * cfg.n_nodes)]
    exact (region_merge_eq (n := cfg.slice_bytes) (by omega) (by omega)).symm
  have hm_ahl : region cfg.aig_ptr (8 * cfg.aig_cap + (4 * cfg.ht_slots + cfg.lits_bytes)) =
      (region cfg.aig_ptr (8 * cfg.aig_cap) ⋆
        region cfg.ht_ptr (4 * cfg.ht_slots + cfg.lits_bytes)) := by
    rw [hht_ptr]; exact (region_merge_eq rfl (by omega)).symm
  have hm_hl : region cfg.ht_ptr (4 * cfg.ht_slots + cfg.lits_bytes) =
      (region cfg.ht_ptr (4 * cfg.ht_slots) ⋆ region cfg.lits_ptr cfg.lits_bytes) := by
    rw [hlits_ptr]; exact (region_merge_eq rfl (by omega)).symm
  have hm_lits : region cfg.lits_ptr cfg.lits_bytes =
      (region cfg.lits_ptr (4 * cfg.lits_cap) ⋆
        region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
          (cfg.lits_bytes - 4 * cfg.lits_cap)) :=
    (region_merge_eq (n := cfg.lits_bytes) (by omega) (by omega)).symm
  rw [hm_asa, hm_atom, hm_sa, hm_slice, hm_ahl, hm_hl, hm_lits] at hm1
  obtain ⟨hdr0, h1⟩ := sep_ex_l.mp (sep_mono (fun _ h => region_to_bvHdrMem h) hm1)
  rw [show (fun m => bvHdrMem cfg.work_base hdr0 m) = bvHdrMem cfg.work_base hdr0 from rfl] at h1
  have h1ab : (region (cfg.work_base + 128) (4 * cfg.n_vars) ⋆
      (bvHdrMem cfg.work_base hdr0 ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
          (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) (4 * cfg.n_nodes) ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
          (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
        region cfg.aig_ptr (8 * cfg.aig_cap) ⋆
        region cfg.ht_ptr (4 * cfg.ht_slots) ⋆
        region cfg.lits_ptr (4 * cfg.lits_cap) ⋆
        region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
          (cfg.lits_bytes - 4 * cfg.lits_cap))) m := sep_ac h1
  obtain ⟨ab0, h2⟩ := sep_ex_l.mp (sep_mono (fun _ h => region_to_array32 cfg.n_vars
    (by omega) h) h1ab)
  obtain ⟨hab0, h2m⟩ := sep_pure_l.mp h2
  have hpre : (region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) (4 * cfg.n_nodes) ⋆
      (bvHdrMem cfg.work_base hdr0 ⋆
        array (t := i32) (cfg.work_base + 128) ab0 ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
          (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
          (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
        region cfg.aig_ptr (8 * cfg.aig_cap) ⋆
        region cfg.ht_ptr (4 * cfg.ht_slots) ⋆
        region cfg.lits_ptr (4 * cfg.lits_cap) ⋆
        region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
          (cfg.lits_bytes - 4 * cfg.lits_cap))) m := sep_ac h2m
  obtain ⟨so0, h3⟩ := sep_ex_l.mp (sep_mono (fun _ h => region_to_array32 cfg.n_nodes
    (by omega) h) hpre)
  obtain ⟨hso0, h3m⟩ := sep_pure_l.mp h3
  have h3ht : (region cfg.ht_ptr (4 * cfg.ht_slots) ⋆
      (bvHdrMem cfg.work_base hdr0 ⋆
        array (t := i32) (cfg.work_base + 128) ab0 ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
          (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
        array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) so0 ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
          (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
        region cfg.aig_ptr (8 * cfg.aig_cap) ⋆
        region cfg.lits_ptr (4 * cfg.lits_cap) ⋆
        region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
          (cfg.lits_bytes - 4 * cfg.lits_cap))) m := sep_ac h3m
  obtain ⟨ht0, h4⟩ := sep_ex_l.mp (sep_mono (fun _ h => region_to_array32 cfg.ht_slots
    (by omega) h) h3ht)
  obtain ⟨hht0, h4m⟩ := sep_pure_l.mp h4
  have h4lp : (region cfg.lits_ptr (4 * cfg.lits_cap) ⋆
      (bvHdrMem cfg.work_base hdr0 ⋆
        array (t := i32) (cfg.work_base + 128) ab0 ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
          (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
        array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) so0 ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
          (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
        region cfg.aig_ptr (8 * cfg.aig_cap) ⋆
        array (t := i32) cfg.ht_ptr ht0 ⋆
        region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
          (cfg.lits_bytes - 4 * cfg.lits_cap))) m := sep_ac h4m
  obtain ⟨lp0, h5⟩ := sep_ex_l.mp (sep_mono (fun _ h => region_to_array32 cfg.lits_cap
    (by omega) h) h4lp)
  obtain ⟨hlp0, h5m⟩ := sep_pure_l.mp h5
  exact ⟨hdr0, ab0, so0, ht0, lp0, hab0, hso0, hht0, hlp0, sep_ac h5m⟩

private theorem region_split_initWorkspace_sep (cfg : BVWorkspaceCfg) (S : Mem 64 → Prop)
    (m : Mem 64)
    (hfit : cfg.work_base.toNat + cfg.avail < 2 ^ 64)
    (htot : 128 + cfg.atom_bytes + cfg.slice_bytes + 8 * cfg.aig_cap +
      4 * cfg.ht_slots + cfg.lits_bytes = cfg.avail)
    (ha_al : 4 * cfg.n_vars ≤ cfg.atom_bytes)
    (hs_al : 4 * cfg.n_nodes ≤ cfg.slice_bytes)
    (hl_fit : 4 * cfg.lits_cap ≤ cfg.lits_bytes)
    (haig_ptr :
      cfg.aig_ptr = cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + cfg.slice_bytes))
    (hht_ptr : cfg.ht_ptr = cfg.aig_ptr + BitVec.ofNat 64 (8 * cfg.aig_cap))
    (hlits_ptr : cfg.lits_ptr = cfg.ht_ptr + BitVec.ofNat 64 (4 * cfg.ht_slots))
    (hnv : cfg.n_vars < 2 ^ 32) (hnn : cfg.n_nodes < 2 ^ 32)
    (hacap : cfg.aig_cap < 2 ^ 28) (hht : cfg.ht_slots ≤ 2 ^ 30)
    (hlcap : cfg.lits_cap < 2 ^ 32)
    (hm : (region cfg.work_base cfg.avail ⋆ S) m) :
    ∃ (hdr0 : BVHdrState) (ab0 so0 ht0 lp0 : List (BitVec 32)),
      ab0.length = cfg.n_vars ∧ so0.length = cfg.n_nodes ∧
      ht0.length = cfg.ht_slots ∧ lp0.length = cfg.lits_cap ∧
      (bvHdrMem cfg.work_base hdr0 ⋆
        array (t := i32) (cfg.work_base + 128) ab0 ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
          (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
        array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) so0 ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
          (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
        region cfg.aig_ptr (8 * cfg.aig_cap) ⋆
        array (t := i32) cfg.ht_ptr ht0 ⋆
        array (t := i32) cfg.lits_ptr lp0 ⋆
        region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
          (cfg.lits_bytes - 4 * cfg.lits_cap) ⋆ S) m := by
  have hsp : ((fun m1 => ∃ hdr0 ab0 so0 ht0 lp0,
      ab0.length = cfg.n_vars ∧ so0.length = cfg.n_nodes ∧
      ht0.length = cfg.ht_slots ∧ lp0.length = cfg.lits_cap ∧
      (bvHdrMem cfg.work_base hdr0 ⋆
        array (t := i32) (cfg.work_base + 128) ab0 ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
          (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
        array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) so0 ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
          (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
        region cfg.aig_ptr (8 * cfg.aig_cap) ⋆
        array (t := i32) cfg.ht_ptr ht0 ⋆
        array (t := i32) cfg.lits_ptr lp0 ⋆
        region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
          (cfg.lits_bytes - 4 * cfg.lits_cap)) m1) ⋆ S) m :=
    sep_mono (fun m1 hreg => region_split_initWorkspace cfg m1 hfit htot ha_al hs_al hl_fit
      haig_ptr hht_ptr hlits_ptr hnv hnn hacap hht hlcap hreg) hm
  obtain ⟨hdr0, hsp⟩ := sep_ex_l.mp hsp
  obtain ⟨ab0, hsp⟩ := sep_ex_l.mp hsp
  obtain ⟨so0, hsp⟩ := sep_ex_l.mp hsp
  obtain ⟨ht0, hsp⟩ := sep_ex_l.mp hsp
  obtain ⟨lp0, hsp⟩ := sep_ex_l.mp hsp
  obtain ⟨h1, hsp⟩ := sep_pure_l.mp hsp
  obtain ⟨h2, hsp⟩ := sep_pure_l.mp hsp
  obtain ⟨h3, hsp⟩ := sep_pure_l.mp hsp
  obtain ⟨h4, hws⟩ := sep_pure_l.mp hsp
  exact ⟨hdr0, ab0, so0, ht0, lp0, h1, h2, h3, h4, sep_ac hws⟩

/-! ## 3. `bv_init_workspace_wp` -/

public section

theorem bv_init_workspace_wp (Γ : Env)
    (hRead : ∀ xs m Q X, bvReadU32Spec xs m Q X →
      Γ "bv_read_u32" [i64, i64] [i32] xs m Q X)
    (hCount : ∀ xs m Q X, bvCountAtomsSpec xs m Q X →
      Γ "bv_count_atoms" [i64, i32] [i64] xs m Q X)
    (hAigInit : ∀ xs m Q X, bvAigInitSpec xs m Q X →
      Γ "bv_aig_init" [i64, i64, i32, i64, i32, i32] [] xs m Q X) :
    ∀ xs m Q X, bvInitWorkspaceSpec xs m Q X → Func.wp Γ bv_init_workspace_body xs m Q X := by
  rintro ⟨h, workBase, avail, progPtr, ⟨⟩⟩ m Q X
    ⟨progBytes, vars, cwords, nodes, prog, R, hh_eq, hp, hprog_fit, hwb_fit, hm, hFits,
      hNotFits⟩
  subst h
  have hm_bytes : (bytes progPtr progBytes ⋆ (region workBase avail.toNat ⋆ R)) m := sep_ac hm
  have hlen_ge : 32 ≤ progBytes.length := hp.valid.len_ge
  have htot_len := hp.valid.total_len
  c0_hstraight
  c0_hsplit
  · -- avail < 128
    have hnf : ¬ bvInitFitsCond progBytes avail.toNat := by
      intro ⟨hfix, _⟩
      have hc' : avail.toNat < 128 := hc
      omega
    c0_hstraight
    exact (hNotFits hnf).2
  · have hav_ge : 128 ≤ avail.toNat := by
      have hc' : ¬ avail.toNat < 128 := hc
      omega
    clear hc
    c0_hstraight
    c0_call hRead
    refine ⟨progBytes, _, hprog_fit, by simp [BitVec.toNat_ofNat]; omega, hm_bytes, ?_⟩
    c0_hstraight
    c0_call hRead
    refine ⟨progBytes, _, hprog_fit, by simp [BitVec.toNat_ofNat]; omega, hm_bytes, ?_⟩
    c0_hstraight
    c0_call hRead
    refine ⟨progBytes, _, hprog_fit, by simp [BitVec.toNat_ofNat]; omega, hm_bytes, ?_⟩
    c0_hstraight
    c0_call hRead
    refine ⟨progBytes, _, hprog_fit, by simp [BitVec.toNat_ofNat]; omega, hm_bytes, ?_⟩
    c0_hstraight
    let nv := u32At progBytes 2
    let nn := u32At progBytes 3
    let nc := u32At progBytes 4
    let rt := u32At progBytes 5
    have hnv_lt : nv < 2 ^ 32 := u32At_lt progBytes 2
    have hnn_lt : nn < 2 ^ 32 := u32At_lt progBytes 3
    have hnc_lt : nc < 2 ^ 32 := u32At_lt progBytes 4
    have hrt_lt : rt < 2 ^ 32 := u32At_lt progBytes 5
    c0_call hCount
    refine ⟨progBytes, _, hprog_fit, ?_, hm_bytes, ?_⟩
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnv_lt]; omega
    · c0_hstraight
      c0_hsplit
      · -- atom_end == 0 (impossible from hp.valid.atoms_ok)
        have hc_nat := congrArg BitVec.toNat hc
        have hnv_mod : u32At progBytes 2 % 2 ^ 32 = nv := Nat.mod_eq_of_lt hnv_lt
        have hcnt_lt := countAtoms_lt progBytes nv
        have hcnt_64 : countAtoms progBytes nv < 2 ^ 64 := by unfold bvDimacsBound at *; omega
        have hc' : countAtoms progBytes nv = 0 := by
          dsimp only [nv] at hc_nat hnv_mod ⊢
          rw [hnv_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcnt_64] at hc_nat
          exact hc_nat
        exact absurd hc' hp.valid.atoms_ok
      · clear hc
        have hnv_mod : u32At progBytes 2 % 2 ^ 32 = nv := Nat.mod_eq_of_lt hnv_lt
        have hnn_mod : u32At progBytes 3 % 2 ^ 32 = nn := Nat.mod_eq_of_lt hnn_lt
        have hcnt_pos : 1 ≤ countAtoms progBytes nv :=
          countAtoms_pos_of_ne_zero hp.valid.atoms_ok
        have hcnt_lt : countAtoms progBytes nv < bvDimacsBound := countAtoms_lt progBytes nv
        have hcnt_64 : countAtoms progBytes nv < 2 ^ 64 := by unfold bvDimacsBound at *; omega
        c0_hstraight
        let atomB := align8 (4 * nv)
        let sliceB := align8 (4 * nn)
        have ha_lt35 : atomB < 2 ^ 35 := align8_lt_of_u32 nv hnv_lt
        have hs_lt35 : sliceB < 2 ^ 35 := align8_lt_of_u32 nn hnn_lt
        let fixed := 128 + atomB + sliceB
        have hfix_lt : fixed < 2 ^ 37 := by omega
        have hfb_raw : (BitVec.toNat (128 : BitVec 64) +
            (BitVec.setWidth 64 (BitVec.ofNat 32 (u32At progBytes 2)) <<< OfNat.ofNat 2 + 7 &&&
              ~~~7).toNat +
            (BitVec.setWidth 64 (BitVec.ofNat 32 (u32At progBytes 3)) <<< OfNat.ofNat 2 + 7 &&&
              ~~~7).toNat) % 2 ^ 64 = fixed :=
          bv_init_fixed_raw nv nn hnv_lt hnn_lt
        c0_hstraight
        c0_hsplit
        · -- avail <= fixed_bytes
          have hnf : ¬ bvInitFitsCond progBytes avail.toNat := by
            intro ⟨hfix, _⟩
            have hc' : avail.toNat ≤ fixed := by rw [hfb_raw] at hc; exact hc
            dsimp only [fixed, atomB, sliceB, nv, nn] at hc'
            omega
          c0_hstraight
          exact (hNotFits hnf).2
        · have hc_gt : fixed < avail.toNat := by
            rw [hfb_raw] at hc; omega
          clear hc
          c0_hstraight
          c0_hsplit
          · -- avail - fixed_bytes < 64
            have hnf : ¬ bvInitFitsCond progBytes avail.toNat := by
              intro ⟨hfix, _⟩
              have hsub_nat : (2 ^ 64 - fixed + avail.toNat) % 2 ^ 64 = avail.toNat - fixed := by
                dsimp only [fixed, atomB, sliceB, nv, nn] at hfix_lt hc_gt ⊢; omega
              have hc' : avail.toNat - fixed < 64 := by
                rw [hfb_raw, hsub_nat, show BitVec.toNat (64 : BitVec 64) = 64 from rfl] at hc
                exact hc
              dsimp only [fixed, atomB, sliceB, nv, nn] at hc'
              omega
            c0_hstraight
            exact (hNotFits hnf).2
          · have hrem_ge : fixed + 64 ≤ avail.toNat := by
              have hsub_nat : (2 ^ 64 - fixed + avail.toNat) % 2 ^ 64 = avail.toNat - fixed := by
                omega
              rw [hfb_raw, hsub_nat, show BitVec.toNat (64 : BitVec 64) = 64 from rfl] at hc; omega
            clear hc hc_gt
            c0_hstraight
            refine wp_join_state1 (t := i64) (α := Nat) (fun ac => BitVec.ofNat 64 ac)
              (fun ac ml => ac = min ((avail.toNat - fixed) / 16) (bvDimacsBound - 1) ∧
                ml = m) ?_ ?_
            · intro J ac ml ⟨hac_eq, hml⟩
              subst ml
              have hac_lt : ac < bvDimacsBound := by rw [hac_eq]; unfold bvDimacsBound; omega
              have hac_64 : ac < 2 ^ 64 := by unfold bvDimacsBound at hac_lt; omega
              have hac_le_rem : 16 * ac ≤ avail.toNat - fixed := by rw [hac_eq]; omega
              c0_hstraight
              have hcnt_sub1 : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) +
                  countAtoms progBytes (u32At progBytes 2 % 2 ^ 32)) % 2 ^ 64 % 2 ^ 32 =
                  countAtoms progBytes nv - 1 := by
                rw [hnv_mod, show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
                unfold bvDimacsBound at hcnt_lt; omega
              c0_hsplit
              · -- num_atoms >= acap64
                have hnf : ¬ bvInitFitsCond progBytes avail.toNat := by
                  intro ⟨_, hnat⟩
                  have hc' : ac ≤ countAtoms progBytes nv - 1 := by
                    rw [hcnt_sub1, Nat.mod_eq_of_lt hac_64] at hc
                    exact hc
                  rw [hac_eq] at hc'
                  dsimp only [fixed, atomB, sliceB, nv, nn] at hc' hnat
                  omega
                c0_hstraight
                exact (hNotFits hnf).2
              · have hnum_lt : countAtoms progBytes nv - 1 < ac := by
                  rw [hcnt_sub1, Nat.mod_eq_of_lt hac_64] at hc
                  omega
                clear hc
                c0_hstraight
                let rem := avail.toNat - fixed
                refine wp_while_state (α := Nat)
                  (fun s => (BitVec.ofNat 64 s, ()))
                  (fun s => 0x40000000 - s)
                  (fun s ml => ml = m ∧ (∃ p, s = 2 ^ p) ∧ 0 < s ∧ s ≤ 2 ^ 30 ∧
                    4 * s ≤ rem / 8)
                  ?_ ?_
                · intro J2 hJ2
                  c0_hstraight
                  exact hJ2 1 m ⟨rfl, ⟨0, rfl⟩, by decide, by decide, by omega⟩
                · intro J2 s ml ⟨hml, hs_pow, hs_pos, hs_le, hs_bud⟩ ih
                  subst ml
                  have hs_lt64 : s < 2 ^ 64 := by omega
                  c0_hsteps_nogrp
                  refine wp_join0 (fun ml' => ml' = m) ?_ ?_
                  · intro J_after ml' hml'
                    subst ml'
                    c0_hstraight
                    have haig_ht_le : 8 * ac + 4 * s ≤ rem := by omega
                    c0_hsplit
                    · -- impossible dead check rem < aig_bytes + ht_bytes
                      have hsub_nat :
                          (2 ^ 64 - fixed + avail.toNat) % 2 ^ 64 = rem := by
                        dsimp only [rem, fixed, atomB, sliceB, nv, nn] at hfix_lt hrem_ge ⊢; omega
                      have hlt_c : rem < 8 * ac + 4 * s := by
                        rw [hfb_raw, hsub_nat, Nat.mod_eq_of_lt hac_64, Nat.mod_eq_of_lt hs_lt64,
                          show (2 ^ OfNat.ofNat 3 : Nat) = 8 from rfl,
                          show (2 ^ OfNat.ofNat 2 : Nat) = 4 from rfl,
                          Nat.mod_eq_of_lt (by omega : ac * 8 + s * 4 < 2 ^ 64)] at hc
                        omega
                      omega
                    · -- success path
                      clear hc
                      c0_hsteps_nogrp
                      let litsB := rem - (8 * ac + 4 * s)
                      refine wp_join_state1 (t := i64) (α := Nat) (fun lc => BitVec.ofNat 64 lc)
                        (fun lc ml' => lc = min (litsB / 4) 0xFFFFFFFE ∧ ml' = m) ?_ ?_
                      · intro J3 lcap ml' ⟨hlc_eq, hml'⟩
                        subst ml'
                        have hlc_32 : lcap < 2 ^ 32 := by rw [hlc_eq]; omega
                        have hlc_fit : 4 * lcap ≤ litsB := by rw [hlc_eq]; omega
                        let cfg : BVWorkspaceCfg :=
                          { work_base := workBase
                            avail := avail.toNat
                            n_vars := nv
                            n_nodes := nn
                            aig_cap := ac
                            ht_slots := s
                            lits_cap := lcap
                            atom_bytes := atomB
                            slice_bytes := sliceB
                            aig_ptr := workBase + BitVec.ofNat 64 (128 + atomB + sliceB)
                            ht_ptr := workBase + BitVec.ofNat 64 (128 + atomB + sliceB) +
                              BitVec.ofNat 64 (8 * ac)
                            lits_ptr := workBase + BitVec.ofNat 64 (128 + atomB + sliceB) +
                              BitVec.ofNat 64 (8 * ac) + BitVec.ofNat 64 (4 * s)
                            lits_bytes := litsB }
                        have hcfg_tot : 128 + cfg.atom_bytes + cfg.slice_bytes +
                            8 * cfg.aig_cap + 4 * cfg.ht_slots + cfg.lits_bytes = cfg.avail := by
                          dsimp only [cfg, atomB, sliceB, litsB, rem, fixed]; omega
                        obtain ⟨hdr0, ab0, so0, ht0, lp0, hab0_len, hso0_len, hht0_len,
                            hlp0_len, hm_split⟩ :=
                          region_split_initWorkspace_sep cfg (bytes progPtr progBytes ⋆ R) m
                            hwb_fit hcfg_tot (align8_ge (4 * nv)) (align8_ge (4 * nn)) hlc_fit
                            rfl rfl rfl hnv_lt hnn_lt hac_lt hs_le hlc_32 (sep_ac hm)
                        clear hm
                        c0_hstraight
                        let hdr1 : BVHdrState :=
                          updHdr15 hdr0 workBase (workBase + avail) progPtr (workBase + 128)
                            (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes))
                            cfg.lits_ptr (BitVec.ofNat 32 nv) (BitVec.ofNat 32 nn)
                            (BitVec.ofNat 32 nc) (BitVec.ofNat 32 rt) (BitVec.ofNat 32 lcap)
                        have hlcap_sw :
                            (BitVec.ofNat 64 lcap).setWidth 32 = BitVec.ofNat 32 lcap := by
                          apply BitVec.eq_of_toNat_eq
                          rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt (by omega : lcap < 2 ^ 64),
                            Nat.mod_eq_of_lt hlc_32]
                        have hwe_eq : workBase + avail =
                            workBase + BitVec.ofNat 64 cfg.avail := by
                          congr 1; apply BitVec.eq_of_toNat_eq
                          rw [BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt (by dsimp only [cfg]; exact avail.isLt)]
                        have hso_eq : workBase + (128 : BitVec 64) +
                            ((BitVec.ofNat 32 (u32At progBytes 2)).setWidth 64 <<<
                              OfNat.ofNat 2 + (7 : BitVec 64) &&& ~~~(7 : BitVec 64)) =
                            cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes) :=
                          bv_init_so_eq workBase nv nn avail.toNat hnv_lt hnn_lt hwb_fit hrem_ge
                        have haig_c0 : workBase + ((128 : BitVec 64) +
                            ((BitVec.ofNat 32 (u32At progBytes 2)).setWidth 64 <<<
                              OfNat.ofNat 2 + (7 : BitVec 64) &&& ~~~(7 : BitVec 64)) +
                            ((BitVec.ofNat 32 (u32At progBytes 3)).setWidth 64 <<<
                              OfNat.ofNat 2 + (7 : BitVec 64) &&& ~~~(7 : BitVec 64))) =
                            cfg.aig_ptr :=
                          bv_init_aig_eq workBase nv nn avail.toNat hnv_lt hnn_lt hwb_fit hrem_ge
                        have hht_c0 : cfg.aig_ptr + (BitVec.ofNat 64 ac <<< OfNat.ofNat 3) =
                            cfg.ht_ptr := by
                          dsimp only [cfg]; congr 1; apply BitVec.eq_of_toNat_eq
                          unfold bvDimacsBound at hac_lt
                          rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                            Nat.shiftLeft_eq, Nat.mod_eq_of_lt hac_64,
                            Nat.mod_eq_of_lt (by omega : ac * 2 ^ 3 < 2 ^ 64),
                            Nat.mod_eq_of_lt (by omega : 8 * ac < 2 ^ 64)]
                          omega
                        have hlits_c0 : workBase + ((128 : BitVec 64) +
                            ((BitVec.ofNat 32 (u32At progBytes 2)).setWidth 64 <<<
                              OfNat.ofNat 2 + (7 : BitVec 64) &&& ~~~(7 : BitVec 64)) +
                            ((BitVec.ofNat 32 (u32At progBytes 3)).setWidth 64 <<<
                              OfNat.ofNat 2 + (7 : BitVec 64) &&& ~~~(7 : BitVec 64))) +
                            (BitVec.ofNat 64 ac <<< OfNat.ofNat 3) +
                            (BitVec.ofNat 64 s <<< OfNat.ofNat 2) = cfg.lits_ptr := by
                          rw [haig_c0]
                          exact bv_init_lits_eq cfg.aig_ptr ac s
                            (by unfold bvDimacsBound at hac_lt; omega) (by omega)
                        rw [hso_eq, hlits_c0, hlcap_sw, upd15_eq] at hm ⊢
                        rw [show hdr1.atom_base_ptr = cfg.work_base + 128 from rfl]
                        rw [show BitVec.ofNat 32 (u32At progBytes 2) = BitVec.ofNat 32 nv from rfl,
                          show BitVec.ofNat 32 (u32At progBytes 3) = BitVec.ofNat 32 nn from rfl,
                          show BitVec.ofNat 32 (u32At progBytes 4) = BitVec.ofNat 32 nc from rfl,
                          show BitVec.ofNat 32 (u32At progBytes 5) = BitVec.ofNat 32 rt from rfl,
                          show updHdr15 hdr0 workBase (workBase + avail) progPtr (workBase + 128)
                            (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) cfg.lits_ptr
                            (BitVec.ofNat 32 nv) (BitVec.ofNat 32 nn) (BitVec.ofNat 32 nc)
                            (BitVec.ofNat 32 rt) (BitVec.ofNat 32 lcap) = hdr1 from rfl] at hm
                        -- Initialize atom_base loop
                        refine wp_while_state (α := Nat × List (BitVec 32))
                          (fun st =>
                            (BitVec.ofNat 32 (countAtoms progBytes st.1),
                              BitVec.ofNat 32 st.1, ()))
                          (fun st => nv - st.1)
                          (fun st ml => st.1 ≤ nv ∧ st.2.length = nv ∧
                            (∀ k < st.1,
                              (st.2.getD k 0#32).toNat = countAtoms progBytes k) ∧
                            (bytes progPtr progBytes ⋆
                              bvHdrMem cfg.work_base hdr1 ⋆
                              array (t := i32) (cfg.work_base + 128) st.2 ⋆
                              region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * nv))
                                (atomB - 4 * nv) ⋆
                              array (t := i32)
                                (cfg.work_base + BitVec.ofNat 64 (128 + atomB)) so0 ⋆
                              region (cfg.work_base + BitVec.ofNat 64 (128 + atomB + 4 * nn))
                                (sliceB - 4 * nn) ⋆
                              region cfg.aig_ptr (8 * ac) ⋆
                              array (t := i32) cfg.ht_ptr ht0 ⋆
                              array (t := i32) cfg.lits_ptr lp0 ⋆
                              region (cfg.lits_ptr + BitVec.ofNat 64 (4 * lcap))
                                (litsB - 4 * lcap) ⋆ R) ml)
                          ?_ ?_
                        · intro J4 hJ4
                          c0_hstraight
                          have hm0 : (bytes progPtr progBytes ⋆ bvHdrMem cfg.work_base hdr1 ⋆
                              array (t := i32) (cfg.work_base + 128) ab0 ⋆
                              region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * nv))
                                (atomB - 4 * nv) ⋆
                              array (t := i32)
                                (cfg.work_base + BitVec.ofNat 64 (128 + atomB)) so0 ⋆
                              region (cfg.work_base + BitVec.ofNat 64 (128 + atomB + 4 * nn))
                                (sliceB - 4 * nn) ⋆
                              region cfg.aig_ptr (8 * ac) ⋆
                              array (t := i32) cfg.ht_ptr ht0 ⋆
                              array (t := i32) cfg.lits_ptr lp0 ⋆
                              region (cfg.lits_ptr + BitVec.ofNat 64 (4 * lcap))
                                (litsB - 4 * lcap) ⋆ R) m := sep_ac hm
                          exact hJ4 (0, ab0) m ⟨Nat.zero_le _, hab0_len,
                            fun _ hk => absurd hk (Nat.not_lt_zero _), hm0⟩
                        · rintro J4 ⟨k, ab⟩ ml ⟨hk_le, hab_len, hpref, hm_loop⟩ ih_ab
                          have hk32 : k < 2 ^ 32 := Nat.lt_of_le_of_lt hk_le hnv_lt
                          c0_hstraight
                          c0_hsplit
                          · have hk_lt : k < nv := by
                              have hc' : k % 2 ^ 32 < nv % 2 ^ 32 := hc
                              rw [Nat.mod_eq_of_lt hk32, Nat.mod_eq_of_lt hnv_lt] at hc'
                              exact hc'
                            clear hc
                            have hcnt_k1 := countAtoms_mono_ne_zero (k := k + 1) hk_lt
                              hp.valid.atoms_ok
                            have hcnt_k := countAtoms_prev_ne_zero hcnt_k1.1
                            have hk_w_fit : 4 * (8 + 2 * k + 1 + 1) ≤ progBytes.length := by
                              omega
                            have hk_idx_eq : ((8 : BitVec 64) +
                                ((BitVec.ofNat 32 k).setWidth 64 <<< OfNat.ofNat 1) +
                                (1 : BitVec 64)).toNat = 8 + 2 * k + 1 := by
                              rw [BitVec.toNat_add, BitVec.toNat_add,
                                show (8 : BitVec 64).toNat = 8 from rfl,
                                show (1 : BitVec 64).toNat = 1 from rfl,
                                BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                                Nat.mod_eq_of_lt hk32,
                                Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
                                Nat.shiftLeft_eq, Nat.pow_one,
                                Nat.mod_eq_of_lt (by omega : k * 2 < 2 ^ 64),
                                Nat.mod_eq_of_lt (by omega : 8 + k * 2 < 2 ^ 64),
                                Nat.mod_eq_of_lt (by omega : 8 + k * 2 + 1 < 2 ^ 64)]
                              omega
                            have hm_ab : (array (t := i32) (cfg.work_base + 128) ab ⋆
                                (bytes progPtr progBytes ⋆ bvHdrMem cfg.work_base hdr1 ⋆
                                  region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * nv))
                                    (atomB - 4 * nv) ⋆
                                  array (t := i32)
                                    (cfg.work_base + BitVec.ofNat 64 (128 + atomB)) so0 ⋆
                                  region (cfg.work_base + BitVec.ofNat 64 (128 + atomB + 4 * nn))
                                    (sliceB - 4 * nn) ⋆
                                  region cfg.aig_ptr (8 * ac) ⋆
                                  array (t := i32) cfg.ht_ptr ht0 ⋆
                                  array (t := i32) cfg.lits_ptr lp0 ⋆
                                  region (cfg.lits_ptr + BitVec.ofNat 64 (4 * lcap))
                                    (litsB - 4 * lcap) ⋆ R)) ml := sep_ac hm_loop
                            have hk_len : (BitVec.ofNat 32 k).toNat < ab.length := by
                              rw [hab_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk32]; exact hk_lt
                            c0_hstraight
                            let ab' := ab.set k (BitVec.ofNat 32 (countAtoms progBytes k))
                            have hab_idx :
                                (BitVec.setWidth 64 (BitVec.ofNat 32 (k, ab).fst)).toNat = k := by
                              rw [show (k, ab).fst = k from rfl, BitVec.toNat_setWidth,
                                BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk32,
                                Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
                            rw [show (k, ab).fst = k from rfl, hab_idx] at hm
                            have hm_read : (bytes progPtr progBytes ⋆
                                (bvHdrMem cfg.work_base hdr1 ⋆
                                  array (t := i32) (cfg.work_base + 128) ab' ⋆
                                  region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * nv))
                                    (atomB - 4 * nv) ⋆
                                  array (t := i32)
                                    (cfg.work_base + BitVec.ofNat 64 (128 + atomB)) so0 ⋆
                                  region (cfg.work_base + BitVec.ofNat 64 (128 + atomB + 4 * nn))
                                    (sliceB - 4 * nn) ⋆
                                  region cfg.aig_ptr (8 * ac) ⋆
                                  array (t := i32) cfg.ht_ptr ht0 ⋆
                                  array (t := i32) cfg.lits_ptr lp0 ⋆
                                  region (cfg.lits_ptr + BitVec.ofNat 64 (4 * lcap))
                                    (litsB - 4 * lcap) ⋆ R)) m := sep_ac hm
                            c0_call hRead
                            refine ⟨progBytes, _, hprog_fit,
                              by rw [hk_idx_eq]; exact hk_w_fit, hm_read, ?_⟩
                            c0_hstraight
                            have hk1_32 : k + 1 < 2 ^ 32 := Nat.lt_of_le_of_lt hk_lt hnv_lt
                            have hk_eq32 : BitVec.ofNat 32 k + 1 = BitVec.ofNat 32 (k + 1) := by
                              apply BitVec.eq_of_toNat_eq
                              simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
                                show (1 : BitVec 32).toNat = 1 from rfl,
                                Nat.mod_eq_of_lt hk32, Nat.mod_eq_of_lt hk1_32]
                            have hvw_lt : u32At progBytes (8 + 2 * k + 1) < 2 ^ 32 := by
                              have := u32At_lt progBytes (8 + 2 * k + 1)
                              unfold u32Bound at this; exact this
                            have hca_k1 : BitVec.ofNat 32 (countAtoms progBytes k) +
                                BitVec.ofNat 32 (u32At progBytes (8 + 2 * k + 1)) =
                                BitVec.ofNat 32 (countAtoms progBytes (k + 1)) := by
                              apply BitVec.eq_of_toNat_eq
                              rw [hcnt_k.2.2]
                              unfold bvDimacsBound at hcnt_lt
                              have := hcnt_k1.2
                              rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                                BitVec.toNat_ofNat,
                                Nat.mod_eq_of_lt (by omega : countAtoms progBytes k < 2 ^ 32),
                                Nat.mod_eq_of_lt hvw_lt,
                                Nat.mod_eq_of_lt (by omega : countAtoms progBytes k +
                                  u32At progBytes (8 + 2 * k + 1) < 2 ^ 32)]
                            dsimp only
                            rw [hk_eq32, hk_idx_eq, hca_k1]
                            refine ih_ab (k + 1, ab') m (by omega)
                              ⟨hk_lt, by simp [ab', hab_len], fun p hp_lt => ?_, ?_⟩
                            · by_cases hpk : p = k
                              · subst hpk
                                rw [list_getD_set_self _ _ _ (by rw [hab_len]; exact hk_lt),
                                  BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
                                unfold bvDimacsBound at hcnt_lt
                                have := hcnt_k1.2; have := hcnt_k.2.2; omega
                              · rw [list_getD_set_ne _ _ _ hpk]; exact hpref p (by omega)
                            · exact sep_ac hm
                          · have hk_eq : k = nv := by
                              have hc' : ¬ k % 2 ^ 32 < nv % 2 ^ 32 := hc
                              rw [Nat.mod_eq_of_lt hk32, Nat.mod_eq_of_lt hnv_lt] at hc'
                              exact Nat.le_antisymm hk_le (Nat.le_of_not_lt hc')
                            clear hc
                            subst hk_eq
                            c0_hstraight
                            have hm_aig_call : ((bvHdrMem cfg.work_base hdr1 ⋆
                                array (t := i32) cfg.ht_ptr ht0) ⋆
                              (bytes progPtr progBytes ⋆
                                array (t := i32) (cfg.work_base + 128) ab ⋆
                                region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * nv))
                                  (atomB - 4 * nv) ⋆
                                array (t := i32)
                                  (cfg.work_base + BitVec.ofNat 64 (128 + atomB)) so0 ⋆
                                region (cfg.work_base + BitVec.ofNat 64 (128 + atomB + 4 * nn))
                                  (sliceB - 4 * nn) ⋆
                                region cfg.aig_ptr (8 * ac) ⋆
                                array (t := i32) cfg.lits_ptr lp0 ⋆
                                region (cfg.lits_ptr + BitVec.ofNat 64 (4 * lcap))
                                  (litsB - 4 * lcap) ⋆ R)) ml := sep_ac hm_loop
                            have hmask_lt : (BitVec.ofNat 64 s - (1 : BitVec 64)).setWidth 32 =
                                BitVec.ofNat 32 (s - 1) := by
                              apply BitVec.eq_of_toNat_eq
                              rw [BitVec.toNat_setWidth,
                                BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                                  rw [BitVec.toNat_ofNat,
                                    show (1 : BitVec 64).toNat = 1 from rfl,
                                    Nat.mod_eq_of_lt hs_lt64]; omega))]
                              simp [Nat.mod_eq_of_lt (by omega : s - 1 < 2 ^ 32)]
                            rw [haig_c0, hht_c0, hmask_lt]
                            c0_call hAigInit
                            refine ⟨hdr1, ht0, _, ?_, by rw [hht0_len]; exact hs_le, ?_,
                              hm_aig_call, ?_⟩
                            · rw [hht0_len, BitVec.toNat_ofNat,
                                Nat.mod_eq_of_lt (by omega : s - 1 < 2 ^ 32)]
                              dsimp only [cfg]; omega
                            · unfold bvDimacsBound at hcnt_lt
                              have hnv_bv :
                                  (BitVec.ofNat 32 (u32At progBytes 2)).toNat = nv := by
                                rw [BitVec.toNat_ofNat, hnv_mod]
                              rw [BitVec.toNat_setWidth,
                                BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                                  rw [BitVec.toNat_ofNat,
                                    show (1 : BitVec 64).toNat = 1 from rfl,
                                    hnv_bv, Nat.mod_eq_of_lt hcnt_64]; omega))]
                              rw [BitVec.toNat_ofNat, hnv_bv, Nat.mod_eq_of_lt hcnt_64,
                                show (1 : BitVec 64).toNat = 1 from rfl]
                              simp only [Nat.mod_eq_of_lt
                                (by omega : countAtoms progBytes nv - 1 < 2 ^ 32)]
                              omega
                            · intro m' hm'
                              c0_hstraight
                              have hnv_bv :
                                  (BitVec.ofNat 32 (u32At progBytes 2)).toNat = nv := by
                                rw [BitVec.toNat_ofNat, hnv_mod]
                              have hac_sw :
                                  (BitVec.ofNat 64 ac).setWidth 32 = BitVec.ofNat 32 ac := by
                                apply BitVec.eq_of_toNat_eq
                                unfold bvDimacsBound at hac_lt
                                rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                                  Nat.mod_eq_of_lt hac_64,
                                  Nat.mod_eq_of_lt (by omega : ac < 2 ^ 32)]
                              have hnum_sw :
                                  (BitVec.ofNat 64 (countAtoms progBytes
                                    (BitVec.ofNat 32 (u32At progBytes 2)).toNat) - 1).setWidth
                                    32 = BitVec.ofNat 32 (countAtoms progBytes nv - 1) := by
                                rw [hnv_bv]
                                apply BitVec.eq_of_toNat_eq
                                rw [BitVec.toNat_setWidth,
                                  BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                                    rw [BitVec.toNat_ofNat,
                                      show (1 : BitVec 64).toNat = 1 from rfl,
                                      Nat.mod_eq_of_lt hcnt_64]; exact hcnt_pos)),
                                  BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                                  show (1 : BitVec 64).toNat = 1 from rfl,
                                  Nat.mod_eq_of_lt hcnt_64,
                                  Nat.mod_eq_of_lt (by unfold bvDimacsBound at hcnt_lt; omega :
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
                              rw [hac_sw, hnum_sw,
                                show { hdr1 with
                                  aig_ptr := cfg.aig_ptr
                                  aig_cap := BitVec.ofNat 32 ac
                                  ht_ptr := cfg.ht_ptr
                                  ht_mask := BitVec.ofNat 32 (s - 1)
                                  num_atoms := BitVec.ofNat 32 (countAtoms progBytes nv - 1)
                                  aig_len :=
                                    BitVec.ofNat 32 (countAtoms progBytes nv - 1) + 1#32
                                  oom := 0#32 : BVHdrState } = hdr2 from rfl,
                                show (workBase : BitVec 64) = cfg.work_base from rfl] at hm'
                              have hm_aig_arr : (region cfg.aig_ptr (8 * ac) ⋆
                                  (bvHdrMem cfg.work_base hdr2 ⋆
                                    array (t := i32) cfg.ht_ptr
                                      (List.replicate ((BitVec.ofNat 32 (s - 1)).toNat + 1)
                                        0#32) ⋆
                                    bytes progPtr progBytes ⋆
                                    array (t := i32) (cfg.work_base + 128) ab ⋆
                                    region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * nv))
                                      (atomB - 4 * nv) ⋆
                                    array (t := i32)
                                      (cfg.work_base + BitVec.ofNat 64 (128 + atomB)) so0 ⋆
                                    region (cfg.work_base + BitVec.ofNat 64 (128 + atomB + 4 * nn))
                                      (sliceB - 4 * nn) ⋆
                                    array (t := i32) cfg.lits_ptr lp0 ⋆
                                    region (cfg.lits_ptr + BitVec.ofNat 64 (4 * lcap))
                                      (litsB - 4 * lcap) ⋆ R)) m' := sep_ac hm'
                              obtain ⟨aw, hx⟩ := sep_ex_l.mp (sep_mono (fun _ h =>
                                region_to_array64 ac (by unfold bvDimacsBound at hac_lt; omega) h)
                                hm_aig_arr)
                              obtain ⟨haw_len, hm_aw⟩ := sep_pure_l.mp hx
                              have hok_fin : BVWorkspaceOk cfg hdr2 ab so0 aw
                                  (List.replicate ((BitVec.ofNat 32 (s - 1)).toNat + 1) 0#32)
                                  lp0 :=
                                { fit := hwb_fit
                                  hdr_wb := rfl
                                  hdr_we := hwe_eq
                                  hdr_ab := rfl
                                  hdr_so := rfl
                                  hdr_aig := rfl
                                  hdr_ht := rfl
                                  hdr_lits := rfl
                                  hdr_nv := rfl
                                  hdr_nn := rfl
                                  hdr_acap := rfl
                                  hdr_htmask := rfl
                                  hdr_lcap := rfl
                                  atom_align := align8_ge (4 * nv)
                                  slice_align := align8_ge (4 * nn)
                                  aig_ptr_eq := rfl
                                  ht_ptr_eq := rfl
                                  lits_ptr_eq := rfl
                                  lits_fit := hlc_fit
                                  total_eq := hcfg_tot
                                  nv_lt := hnv_lt
                                  nn_lt := hnn_lt
                                  acap_lt := hac_lt
                                  ht_pos := hs_pos
                                  ht_lt := hs_le
                                  ht_mask_lt := bv64_pow2_mask_lt hs_pow hs_pos hs_le
                                  lcap_lt := hlc_32
                                  ab_len := hab_len
                                  so_len := hso0_len
                                  aig_len_eq := haw_len
                                  ht_len := by
                                    rw [List.length_replicate, BitVec.toNat_ofNat,
                                      Nat.mod_eq_of_lt (by omega : s - 1 < 2 ^ 32)]
                                    dsimp only [cfg]; omega
                                  lits_len := hlp0_len }
                              have haig_fin : AigInv hdr2
                                  ⟨countAtoms progBytes cfg.n_vars - 1, #[]⟩
                                  aw (List.replicate
                                    ((BitVec.ofNat 32 (s - 1)).toNat + 1) 0#32) :=
                                { wf := fun _ hi => by cases hi
                                  num_atoms_eq := by
                                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
                                    unfold bvDimacsBound at hcnt_lt; omega
                                  aig_len_eq := by
                                    unfold bvDimacsBound at hcnt_lt
                                    dsimp only [hdr2, cfg]
                                    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
                                      show (1#32 : BitVec 32).toNat = 1 from rfl,
                                      show (#[] : Array (UInt32 × UInt32)).size = 0 from rfl,
                                      Nat.mod_eq_of_lt (by omega : countAtoms progBytes nv - 1 <
                                        2 ^ 32),
                                      Nat.mod_eq_of_lt (by omega :
                                        countAtoms progBytes nv - 1 + 1 < 2 ^ 32)]
                                  aig_len_le_cap := by rw [haw_len]; exact hnum_lt
                                  aig_cap_eq := by
                                    dsimp only [hdr2]
                                    rw [haw_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
                                    unfold bvDimacsBound at hac_lt; omega
                                  aig_cap_lt := by rw [haw_len]; exact hac_lt
                                  gates_bound := by simp
                                  words_match :=
                                    { bound := by rw [haw_len]; exact hnum_lt
                                      gate_eq := fun _ hi => by cases hi }
                                  ht_len := by dsimp only [hdr2]; simp
                                  ht_mask_lt := fun x => by
                                    simp only [List.length_replicate]
                                    have hm1 := bv64_pow2_mask_lt hs_pow hs_pos hs_le x
                                    have heq_m : BitVec.ofNat 32 (s - 1) = hdr2.ht_mask := rfl
                                    rw [← heq_m]
                                    rw [BitVec.toNat_ofNat,
                                      Nat.mod_eq_of_lt (by omega : s - 1 < 2 ^ 32)]
                                    omega
                                  ht_pos := by simp
                                  ht_bound := by
                                    rw [List.length_replicate, BitVec.toNat_ofNat,
                                      Nat.mod_eq_of_lt (by omega : s - 1 < 2 ^ 32)]
                                    omega }
                              have hinv_fin : BlastEvalInv cfg progPtr progBytes vars cwords nodes
                                  prog hdr2 ⟨countAtoms progBytes cfg.n_vars - 1, #[]⟩
                                  ab so0 aw
                                  (List.replicate ((BitVec.ofNat 32 (s - 1)).toNat + 1) 0#32)
                                  lp0 0 :=
                                { ws_ok := hok_fin
                                  parsed := hp
                                  prog_ptr_eq := rfl
                                  prog_fit := hprog_fit
                                  nv_eq := rfl
                                  nn_eq := rfl
                                  nc_eq := by
                                    dsimp only [hdr2, hdr1, updHdr15]
                                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnc_lt]
                                  root_eq := by
                                    dsimp only [hdr2, hdr1, updHdr15]
                                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrt_lt]
                                  lits_le_cap := by dsimp only [hdr2, hdr1, updHdr15, cfg]; simp
                                  aig_inv := haig_fin
                                  atoms_eq := rfl
                                  atom_bases_eq := fun v hv => hpref v hv
                                  k_le := Nat.zero_le _
                                  prefix_ok := fun _ _ hi => absurd hi (Nat.not_lt_zero _) }
                              have hm_fin : (bytes progPtr progBytes ⋆
                                  bvBlastMem cfg hdr2 ab so0 aw
                                    (List.replicate ((BitVec.ofNat 32 (s - 1)).toNat + 1) 0#32)
                                    lp0 ⋆ R) m' := by
                                rw [bvBlastMem_hdr_left]; exact sep_ac hm_aw
                              by_cases hfc : bvInitFitsCond progBytes avail.toNat
                              · exact hFits hfc cfg hdr2 ab so0 aw
                                  (List.replicate ((BitVec.ofNat 32 (s - 1)).toNat + 1) 0#32)
                                  lp0 m' rfl rfl rfl hinv_fin hm_fin
                              · exact (hNotFits hfc).1 cfg hdr2 ab so0 aw
                                  (List.replicate ((BitVec.ofNat 32 (s - 1)).toNat + 1) 0#32)
                                  lp0 m' rfl rfl rfl hinv_fin hm_fin
                      · -- acap/lcap join
                        intro J3 hJ3
                        c0_hstraight
                        have hlcap_raw := bv_init_lcap_raw workBase avail nv nn ac s
                          hnv_lt hnn_lt (by unfold bvDimacsBound at hac_lt; omega) (by omega)
                          hwb_fit hrem_ge haig_ht_le
                        dsimp only [nv, nn] at hlcap_raw
                        have hlcap_c0 := bv_init_lcap_c0_nat workBase avail nv nn ac s
                          hnv_lt hnn_lt (by unfold bvDimacsBound at hac_lt; omega) (by omega)
                          hwb_fit hrem_ge haig_ht_le
                        dsimp only [nv, nn] at hlcap_c0
                        c0_hsplit
                        · have hc' : 0xFFFFFFFF ≤ litsB / 4 := by
                            rw [hlcap_c0, show BitVec.toNat (4294967295 : BitVec 64) =
                              0xFFFFFFFF from rfl] at hc
                            exact hc
                          c0_hstraight
                          exact hJ3 0xFFFFFFFE _ ⟨by omega, rfl⟩
                        · have hc' : ¬ 0xFFFFFFFF ≤ litsB / 4 := by
                            rw [hlcap_c0, show BitVec.toNat (4294967295 : BitVec 64) =
                              0xFFFFFFFF from rfl] at hc
                            exact hc
                          c0_hstraight
                          rw [hlcap_raw]
                          exact hJ3 (litsB / 4) _ ⟨by omega, rfl⟩
                  · intro J_exit hJ_exit
                    c0_hstraight
                    c0_hsplit
                    · have hc_bud := hc
                      clear hc
                      c0_hstraight
                      c0_hsplit
                      · -- loop step: 8 * s <= rem / 8 ∧ s < 2^30
                        have hsub_nat : (2 ^ 64 - fixed + avail.toNat) % 2 ^ 64 = rem := by
                          dsimp only [rem]; omega
                        have h8s : 8 * s ≤ rem / 8 := by
                          rw [hfb_raw, hsub_nat, Nat.mod_eq_of_lt hs_lt64,
                            show (2 ^ OfNat.ofNat 3 : Nat) = 8 from rfl,
                            Nat.mod_eq_of_lt (by omega : s * 8 < 2 ^ 64)] at hc_bud
                          omega
                        have hs_lt30 : s < 2 ^ 30 := by
                          rw [Nat.mod_eq_of_lt hs_lt64] at hc
                          exact hc
                        have h2s_64 : 2 * s < 2 ^ 64 := by omega
                        have hs2_eq :
                            BitVec.ofNat 64 s <<< (1 : Nat) = BitVec.ofNat 64 (2 * s) := by
                          apply BitVec.eq_of_toNat_eq
                          simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
                            Nat.mod_eq_of_lt hs_lt64, Nat.mod_eq_of_lt h2s_64,
                            Nat.mod_eq_of_lt (by omega : s * 2 ^ 1 < 2 ^ 64)]
                          omega
                        c0_hstraight
                        rw [hs2_eq]
                        obtain ⟨p, rfl⟩ := hs_pow
                        have hp_lt : p < 30 := Nat.lt_of_not_le fun hp =>
                          Nat.not_lt_of_ge (Nat.pow_le_pow_right (by omega) hp) hs_lt30
                        have h2p_le : 2 * 2 ^ p ≤ 2 ^ 30 := by
                          rw [Nat.mul_comm, ← Nat.pow_succ]
                          exact Nat.pow_le_pow_right (by omega) (by omega)
                        exact ih (2 * 2 ^ p) m (by omega)
                          ⟨rfl, ⟨p + 1, by rw [Nat.pow_succ, Nat.mul_comm]⟩, by omega, h2p_le,
                            by omega⟩
                      · exact hJ_exit m rfl
                    · exact hJ_exit m rfl
            · intro J2 hJ2
              c0_hstraight
              c0_hsplit
              · c0_hstraight
                have hge : bvDimacsBound ≤ (avail.toNat - fixed) / 16 := by
                  have hsub_nat : (2 ^ 64 - fixed + avail.toNat) % 2 ^ 64 = avail.toNat - fixed :=
                    by omega
                  rw [hfb_raw, hsub_nat] at hc
                  exact hc
                exact hJ2 (bvDimacsBound - 1) m ⟨by unfold bvDimacsBound at *; omega, rfl⟩
              · c0_hstraight
                have hlt : (avail.toNat - fixed) / 16 < bvDimacsBound := by
                  have hsub_nat : (2 ^ 64 - fixed + avail.toNat) % 2 ^ 64 = avail.toNat - fixed :=
                    by omega
                  rw [hfb_raw, hsub_nat, show (2 ^ OfNat.ofNat 4 : Nat) = 16 from rfl,
                    show BitVec.toNat (268435456 : BitVec 64) = bvDimacsBound from rfl] at hc
                  exact Nat.lt_of_not_le hc
                have hcap_raw : (avail - ((128 : BitVec 64) +
                    (BitVec.setWidth 64 (BitVec.ofNat 32 (u32At progBytes 2)) <<< OfNat.ofNat 2 +
                      (7 : BitVec 64) &&& ~~~(7 : BitVec 64)) +
                    (BitVec.setWidth 64 (BitVec.ofNat 32 (u32At progBytes 3)) <<< OfNat.ofNat 2 +
                      (7 : BitVec 64) &&& ~~~(7 : BitVec 64)))) >>> OfNat.ofNat 4 =
                    BitVec.ofNat 64 ((avail.toNat - fixed) / 16) :=
                  bv_init_acap_raw avail nv nn hnv_lt hnn_lt hrem_ge
                rw [hcap_raw]
                exact hJ2 ((avail.toNat - fixed) / 16) m ⟨by omega, rfl⟩

end

end LeanQbe.T.Examples.Bitblast.Proof
