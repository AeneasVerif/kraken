/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.Specs
import LeanQbe.T.Examples.Bitblast.Proof.Arena
import LeanQbe.T.Examples.Bitblast.Proof.Bvp1
import LeanQbe.T.Examples.Bitblast.Proof.Validate0
import LeanQbe.T.Examples.Bitblast.Proof.DriverHelpers
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas

/-!
# Top-Level Bitblaster Driver WP Proof (`Bitblast.Proof.Driver`)

Proves `bv_solve_bytes_wp` (`bvSolveBytesSpec`), chaining validation, workspace initialization,
evaluation, COI marking, DIMACS emission, `kissat_solve_bytes`, and end-to-end UNSAT soundness
plus concrete trivial-UNSAT completeness (`bvSolveTrivialUnsatCond → r = 20#64`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open Std Std.Sat Std.Tactic.BVDecide
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Bitblast.Src
open LeanQbe.T.Examples.Bitblast.Src.Driver
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Ref.BVProg

local macro "drv_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_) <;>
    try dsimp only [vals, Arg.val, Prod.fst, Prod.snd])

/-! ## 1. Local Memory Helpers and Pure Bridges -/

@[local c0_load] private theorem drv_load_work_end {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 8) = some s.work_end := load_hdr_work_end hm

@[local c0_load] private theorem drv_load_aig_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 24) = some s.aig_ptr := load_hdr_aig_ptr hm

@[local c0_load] private theorem drv_load_slice_off_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 48) = some s.slice_off_ptr := load_hdr_slice_off_ptr hm

@[local c0_load] private theorem drv_load_marks_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 64) = some s.marks_ptr := load_hdr_marks_ptr hm

@[local c0_load] private theorem drv_load_dimacs_start {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 72) = some s.dimacs_start := load_hdr_dimacs_start hm

@[local c0_load] private theorem drv_load_root_node {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 92) = some s.root_node := load_hdr_root_node hm

@[local c0_load] private theorem drv_load_aig_len {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 100) = some s.aig_len := load_hdr_aig_len hm

@[local c0_load] private theorem drv_load_dimacs_len {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 124) = some s.dimacs_len := load_hdr_dimacs_len hm

@[local c0_store] private theorem drv_store_marks_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i64 (h + 64) ∧
      (bvHdrMem h { s with marks_ptr := v } ⋆ R) (storeMem m i64 (h + 64) v) :=
  store_hdr_marks_ptr v hm

private theorem drv_bv32_mul4_add_eq (base : BitVec 64) (idx : BitVec 32) :
    base + idx.setWidth 64 * 4 = base + BitVec.ofNat 64 (4 * idx.toNat) := by
  congr 1; apply BitVec.eq_of_toNat_eq
  have hi := idx.isLt
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    show (4 : BitVec 64).toNat = 4 from rfl,
    Nat.mod_eq_of_lt (by omega : idx.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : idx.toNat * 4 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 4 * idx.toNat < 2 ^ 64)]
  omega

@[local c0_load] private theorem drv_load_array32_mul4 {base : BitVec 64} {idx : BitVec 32}
    {xs : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hi : idx.toNat < xs.length) (hm : (array (t := i32) base xs ⋆ R) m) :
    loadVal m i32 (base + idx.setWidth 64 * 4) = some (xs.getD idx.toNat 0#32) := by
  rw [drv_bv32_mul4_add_eq]
  have hr := loadVal_array (t := i32) (by decide) hi hm
  simpa [Ty.bytes, Ty.size, list_getD_eq_getElem xs 0#32 hi] using hr

@[local c0_store] private theorem drv_store_region_u64 {a v : BitVec 64} {n : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (hn : 8 ≤ n) (hfit : n ≤ 2 ^ 64)
    (hm : (region a n ⋆ R) m) :
    storeOk m i64 a ∧ (region a n ⋆ R) (storeMem m i64 a v) :=
  store_region_u64_head hn hfit hm

private def drvBlastRest (cfg : BVWorkspaceCfg) (progPtr : BitVec 64)
    (progBytes : List UInt8) (atomBases : List (BitVec 32)) (aigWords : List (BitVec 64))
    (htSlots litsPool : List (BitVec 32)) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  bytes progPtr progBytes ⋆
  array (t := i32) (cfg.work_base + 128) atomBases ⋆
  region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
    (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
  region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
    (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
  array64 cfg.aig_ptr aigWords ⋆
  array (t := i32) cfg.ht_ptr htSlots ⋆
  array (t := i32) cfg.lits_ptr litsPool ⋆
  region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
    (cfg.lits_bytes - 4 * cfg.lits_cap) ⋆ R

private theorem drv_blast_focus_hdr_so {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {progPtr : BitVec 64} {progBytes : List UInt8}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hso : hdr.slice_off_ptr = cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes))
    (hm : (bytes progPtr progBytes ⋆
      bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m) :
    (bvHdrMem cfg.work_base hdr ⋆
      array (t := i32) hdr.slice_off_ptr sliceOffs ⋆
      drvBlastRest cfg progPtr progBytes atomBases aigWords htSlots litsPool R) m := by
  rw [hso]; rw [bvBlastMem_hdr_left] at hm; unfold drvBlastRest; exact sep_ac hm

private theorem drv_blast_unfocus_hdr_so {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {progPtr : BitVec 64} {progBytes : List UInt8}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hso : hdr.slice_off_ptr = cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes))
    (hm : (bvHdrMem cfg.work_base hdr ⋆
      array (t := i32) hdr.slice_off_ptr sliceOffs ⋆
      drvBlastRest cfg progPtr progBytes atomBases aigWords htSlots litsPool R) m) :
    (bytes progPtr progBytes ⋆
      bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m := by
  rw [hso] at hm; rw [bvBlastMem_hdr_left]; unfold drvBlastRest at hm; exact sep_ac hm

private theorem bv64_pad_eq (w : BitVec 64) :
    (((8 : BitVec 64) - (w &&& (7 : BitVec 64))) &&& (7 : BitVec 64)).toNat =
      (8 - w.toNat % 8) % 8 := by
  have hm : (w &&& (7 : BitVec 64)).toNat = w.toNat % 8 := by
    rw [BitVec.toNat_and, show (7 : BitVec 64).toNat = 7 from rfl]
    simpa using Nat.and_two_pow_sub_one_eq_mod w.toNat 3
  have hle : w &&& (7 : BitVec 64) ≤ (8 : BitVec 64) := by
    apply BitVec.le_def.mpr; rw [hm, show (8 : BitVec 64).toNat = 8 from rfl]; omega
  rw [BitVec.toNat_and, BitVec.toNat_sub_of_le hle, hm,
    show (7 : BitVec 64).toNat = 7 from rfl, show (8 : BitVec 64).toNat = 8 from rfl]
  simpa using Nat.and_two_pow_sub_one_eq_mod (8 - w.toNat % 8) 3

private theorem aigWordsMatch_take {g : Aig} {aigWords : List (BitVec 64)} {aigLen : Nat}
    (hw : AigWordsMatch g aigWords) (hlen : aigLen = g.A + 1 + g.nodes.size)
    (hcap : aigLen ≤ aigWords.length) : AigWordsMatch g (aigWords.take aigLen) :=
  { bound := by rw [List.length_take_of_le hcap]; omega
    gate_eq := fun i hi => by
      rw [List.getElem_take]
      exact hw.gate_eq i hi }

private theorem drv_split_pad {progPtr workPtr workBase workCap : BitVec 64}
    {progBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (padNat : Nat) (hpad : padNat ≤ workCap.toNat)
    (hwb : workBase = workPtr + BitVec.ofNat 64 padNat)
    (hm : (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ R) m) :
    (bytes progPtr progBytes ⋆ region workBase (workCap.toNat - padNat) ⋆
      (region workPtr padNat ⋆ R)) m := by
  have h1 : (bytes progPtr progBytes ⋆ (region workPtr workCap.toNat ⋆ R)) m := sep_ac hm
  have hfit : workCap.toNat ≤ 2 ^ 64 := Nat.le_of_lt workCap.isLt
  have hsp := sep_mono_r
    (Q' := (region workPtr padNat ⋆ region workBase (workCap.toNat - padNat)) ⋆ R)
    (fun _ h1 => sep_mono (P' := region workPtr padNat ⋆ region workBase (workCap.toNat - padNat))
      (fun _ h => by
        rw [hwb]
        exact region_work_split_pad padNat hpad hfit h) h1) h1
  exact sep_ac hsp

private theorem drv_restore_pad {progPtr workPtr workBase : BitVec 64} {workCap : BitVec 64}
    {progBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (padNat : Nat) (hpad : padNat ≤ workCap.toNat)
    (hwb : workBase = workPtr + BitVec.ofNat 64 padNat)
    (hm : (bytes progPtr progBytes ⋆ region workBase (workCap.toNat - padNat) ⋆
      (region workPtr padNat ⋆ R)) m) :
    (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ R) m := by
  have hm1 : (bytes progPtr progBytes ⋆
      ((region workPtr padNat ⋆ region (workPtr + BitVec.ofNat 64 padNat)
        (workCap.toNat - padNat)) ⋆ R)) m := by
    rw [← hwb]; exact sep_ac hm
  have hfit : workCap.toNat ≤ 2 ^ 64 := Nat.le_of_lt workCap.isLt
  have h2 := sep_mono_r (Q' := region workPtr workCap.toNat ⋆ R)
    (fun _ h1 => sep_mono (P' := region workPtr workCap.toNat)
      (fun _ h => region_work_merge_pad padNat hpad hfit h) h1) hm1
  exact sep_ac h2

private theorem drv_blast_to_pad_reg {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {progPtr workPtr workCap : BitVec 64} {progBytes : List UInt8}
    {ab so : List (BitVec 32)} {aw : List (BitVec 64)} {ht lp : List (BitVec 32)}
    {padNat : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hok : BVWorkspaceOk cfg hdr ab so aw ht lp) (hav : cfg.avail = workCap.toNat - padNat)
    (hm : (bytes progPtr progBytes ⋆
      bvBlastMem cfg hdr ab so aw ht lp ⋆ (region workPtr padNat ⋆ R)) m) :
    (bytes progPtr progBytes ⋆ region cfg.work_base (workCap.toNat - padNat) ⋆
      (region workPtr padNat ⋆ R)) m := by
  rw [← hav]
  have h1 : (bytes progPtr progBytes ⋆
      (bvBlastMem cfg hdr ab so aw ht lp ⋆ (region workPtr padNat ⋆ R))) m := sep_ac hm
  have h2 := sep_mono_r (Q' := region cfg.work_base cfg.avail ⋆ (region workPtr padNat ⋆ R))
    (fun _ h1 => sep_mono (P' := region cfg.work_base cfg.avail)
      (fun _ h => bvBlastMem_to_region hok h) h1) h1
  exact sep_ac h2

private theorem bv64_marksPtr_eq (aigPtr : BitVec 64) (aigLen : BitVec 32)
    (haig_toNat : aigPtr.toNat + 8 * aigLen.toNat < 2 ^ 64) :
    (aigPtr + (aigLen.setWidth 64 <<< OfNat.ofNat 3)).toNat =
      aigPtr.toNat + 8 * aigLen.toNat := by
  have hal := aigLen.isLt
  have haig := aigPtr.isLt
  have hsh : (aigLen.setWidth 64 <<< OfNat.ofNat 3).toNat = 8 * aigLen.toNat := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega : aigLen.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : aigLen.toNat * 2 ^ 3 < 2 ^ 64)]
    omega
  rw [BitVec.toNat_add, hsh, Nat.mod_eq_of_lt haig_toNat]

private theorem bv64_marksPtr_bv (aigPtr : BitVec 64) (aigLen : BitVec 32)
    (haig_toNat : aigPtr.toNat + 8 * aigLen.toNat < 2 ^ 64) :
    aigPtr + (aigLen.setWidth 64 <<< OfNat.ofNat 3) =
      aigPtr + BitVec.ofNat 64 (8 * aigLen.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [bv64_marksPtr_eq aigPtr aigLen haig_toNat, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 8 * aigLen.toNat < 2 ^ 64), Nat.mod_eq_of_lt haig_toNat]

private theorem drv_u32_of_eq0_zero {x : BitVec 32} (hx : x.toNat % 2 = 0) (hx1 : x.toNat < 2) :
    x = 0#32 := by
  apply BitVec.eq_of_toNat_eq; show x.toNat = 0; omega

private theorem drv_blast_to_coi {progPtr : BitVec 64} {progBytes : List UInt8}
    {cfg : BVWorkspaceCfg} {hdr : BVHdrState} {atomBases sliceOffs : List (BitVec 32)}
    {aigWords : List (BitVec 64)} {htSlots litsPool : List (BitVec 32)} {aigLen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hok : BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool)
    (hlen : aigLen ≤ cfg.aig_cap)
    (hm_fit : 128 + cfg.atom_bytes + cfg.slice_bytes + 8 * aigLen + aigLen ≤ cfg.avail)
    (hm : (bytes progPtr progBytes ⋆
      bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m) :
    ∃ marks0 : List UInt8, marks0.length = aigLen ∧
      (bvCoiMem cfg.work_base cfg.aig_ptr (cfg.aig_ptr + BitVec.ofNat 64 (8 * aigLen))
        cfg.avail hdr (aigWords.take aigLen) marks0 ⋆ (bytes progPtr progBytes ⋆ R)) m := by
  have hm1 : (bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆
      (bytes progPtr progBytes ⋆ R)) m := sep_ac hm
  have hsp := sep_mono (fun _ h => bvBlastMem_to_coiMem hok hlen hm_fit h) hm1
  obtain ⟨marks0, h1⟩ := sep_ex_l.mp hsp
  obtain ⟨hm0_len, hm0⟩ := sep_pure_l.mp h1
  exact ⟨marks0, hm0_len, hm0⟩

private theorem drv_coi_focus {workBase aigPtr marksPtr : BitVec 64} {avail : Nat}
    {hdr : BVHdrState} {aigUsed : List (BitVec 64)} {marks : List UInt8}
    {S : Mem 64 → Prop} {m : Mem 64}
    (haig_hdr : hdr.aig_ptr = aigPtr) (hmptr_hdr : hdr.marks_ptr = marksPtr)
    (hm : (bvCoiMem workBase aigPtr marksPtr avail hdr aigUsed marks ⋆ S) m) :
    (bvHdrMem workBase hdr ⋆ array64 hdr.aig_ptr aigUsed ⋆
      bytes hdr.marks_ptr marks ⋆
      (region (workBase + 128) (aigPtr.toNat - (workBase.toNat + 128)) ⋆
        region (marksPtr + BitVec.ofNat 64 marks.length)
          (workBase.toNat + avail - (marksPtr.toNat + marks.length)) ⋆ S)) m := by
  unfold bvCoiMem at hm
  rw [haig_hdr, hmptr_hdr]
  exact sep_ac hm

private theorem drv_coi_unfocus {workBase aigPtr marksPtr : BitVec 64} {avail : Nat}
    {hdr : BVHdrState} {aigUsed : List (BitVec 64)} {marks : List UInt8}
    {S : Mem 64 → Prop} {m : Mem 64}
    (haig_hdr : hdr.aig_ptr = aigPtr) (hmptr_hdr : hdr.marks_ptr = marksPtr)
    (hlen : marks.length = aigUsed.length)
    (hm : (bvHdrMem workBase hdr ⋆ array64 hdr.aig_ptr aigUsed ⋆
      bytes hdr.marks_ptr marks ⋆
      (region (workBase + 128) (aigPtr.toNat - (workBase.toNat + 128)) ⋆
        region (marksPtr + BitVec.ofNat 64 aigUsed.length)
          (workBase.toNat + avail - (marksPtr.toNat + aigUsed.length)) ⋆ S)) m) :
    (bvCoiMem workBase aigPtr marksPtr avail hdr aigUsed marks ⋆ S) m := by
  unfold bvCoiMem
  rw [haig_hdr, hmptr_hdr] at hm
  rw [hlen]
  exact sep_ac hm

private theorem drv_ult_sub_max_toNat (workPtr workCap : BitVec 64)
    (h : ((18446744073709551615 - workPtr).ult workCap) = false) :
    workPtr.toNat + workCap.toNat < 2 ^ 64 := by
  have hw := workPtr.isLt; have hc := workCap.isLt
  have hsub : (18446744073709551615 - workPtr).toNat = 2 ^ 64 - 1 - workPtr.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
      rw [show (18446744073709551615 : BitVec 64).toNat = 2 ^ 64 - 1 by simp]; omega)),
      show (18446744073709551615 : BitVec 64).toNat = 2 ^ 64 - 1 by simp]
  simp only [BitVec.ult, decide_eq_false_iff_not, not_lt, hsub] at h
  omega

private theorem drv_ult_sub_max_contra (workPtr workCap : BitVec 64)
    (h : ((18446744073709551615 - workPtr).ult workCap) = true)
    (hlt : workPtr.toNat + workCap.toNat < 2 ^ 64) : False := by
  have hw := workPtr.isLt
  have hsub : (18446744073709551615 - workPtr).toNat = 2 ^ 64 - 1 - workPtr.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
      rw [show (18446744073709551615 : BitVec 64).toNat = 2 ^ 64 - 1 by simp]; omega)),
      show (18446744073709551615 : BitVec 64).toNat = 2 ^ 64 - 1 by simp]
  simp only [BitVec.ult, decide_eq_true_eq, hsub] at h
  omega

private theorem drv_split_init {A P Q : Prop} (hP : P) (hQ : ¬ A → Q) :
    (A → P) ∧ (¬ A → P ∧ Q) :=
  ⟨fun _ => hP, fun h => ⟨hP, hQ h⟩⟩

private theorem drv_tu_root_zero {progPtr workPtr workCap fuel : BitVec 64}
    {progBytes : List UInt8} {cfg : BVWorkspaceCfg} {hdr hdr' : BVHdrState}
    {ret : Bool} {g' : Aig} {so' : List (BitVec 32)}
    {hrt_lt_nn : hdr'.root_node.toNat < cfg.n_nodes}
    {hinv1_nv : cfg.n_vars = u32At progBytes 2} {hinv1_nn : cfg.n_nodes = u32At progBytes 3}
    {hinv1_nc : hdr.n_cwords.toNat = u32At progBytes 4}
    {hroot_idx : hdr'.root_node.toNat = u32At progBytes 5}
    (hconst : (∀ i < cfg.n_nodes, u32At progBytes
      (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * i) = opBConst) →
      ret = true ∧ g' = { A := countAtoms progBytes cfg.n_vars - 1, nodes := #[] } ∧
      ∀ i < cfg.n_nodes, (so'.getD i 0#32).toNat =
        u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * i + 2) % 2)
    (htu : bvSolveTrivialUnsatCond progPtr progBytes workPtr workCap fuel) :
    so'.getD hdr'.root_node.toNat 0#32 = 0#32 := by
  have hbc : ∀ i < cfg.n_nodes, u32At progBytes
      (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * i) = opBConst := by
    intro i hi; rw [hinv1_nv, hinv1_nc]
    exact htu.2.2.2.2.2.2.2.2.1 i (by rw [← hinv1_nn]; exact hi)
  have hall := (hconst hbc).2.2 hdr'.root_node.toNat hrt_lt_nn
  rw [hinv1_nv, hinv1_nc, hroot_idx] at hall
  rw [hroot_idx]
  exact drv_u32_of_eq0_zero (by rw [hall]; simp [htu.2.2.2.2.2.2.2.2.2])
    (by rw [hall]; exact Nat.mod_lt _ (by decide))

private theorem drv_marksPtr_bounds {cfg : BVWorkspaceCfg} {hdr' : BVHdrState}
    {ab so' : List (BitVec 32)} {aw' : List (BitVec 64)} {hts' lp' : List (BitVec 32)}
    {g' : Aig} (hok' : BVWorkspaceOk cfg hdr' ab so' aw' hts' lp')
    (haig' : AigInv hdr' g' aw' hts')
    (haig_len_eq : hdr'.aig_len.toNat = g'.A + 1 + g'.nodes.size) :
    hdr'.aig_len.toNat ≤ cfg.aig_cap ∧
    hdr'.aig_len.toNat < bvDimacsBound ∧
    128 + cfg.atom_bytes + cfg.slice_bytes + 8 * cfg.aig_cap + 4 * cfg.ht_slots +
      cfg.lits_bytes = cfg.avail ∧
    cfg.aig_ptr.toNat = cfg.work_base.toNat + 128 + cfg.atom_bytes + cfg.slice_bytes ∧
    cfg.aig_ptr.toNat + 8 * hdr'.aig_len.toNat < 2 ^ 64 ∧
    (hdr'.aig_ptr + (hdr'.aig_len.setWidth 64 <<< OfNat.ofNat 3) =
      cfg.aig_ptr + BitVec.ofNat 64 (8 * hdr'.aig_len.toNat)) ∧
    ((cfg.aig_ptr + BitVec.ofNat 64 (8 * hdr'.aig_len.toNat)).toNat =
      cfg.aig_ptr.toNat + 8 * hdr'.aig_len.toNat) ∧
    (hdr'.work_end.toNat = cfg.work_base.toNat + cfg.avail) := by
  have haig_le_cap : hdr'.aig_len.toNat ≤ cfg.aig_cap := by
    rw [haig_len_eq, ← hok'.aig_len_eq]; exact haig'.aig_len_le_cap
  have haig_bd : hdr'.aig_len.toNat < bvDimacsBound :=
    Nat.lt_of_le_of_lt haig_le_cap (by rw [← hok'.aig_len_eq]; exact haig'.aig_cap_lt)
  have hfit_c := hok'.fit
  have htot_c := hok'.total_eq
  have haig_toNat : cfg.aig_ptr.toNat =
      cfg.work_base.toNat + 128 + cfg.atom_bytes + cfg.slice_bytes := by
    have hwb := cfg.work_base.isLt
    have haa := hok'.atom_align; have hsa := hok'.slice_align
    have hnv := hok'.nv_lt; have hnn := hok'.nn_lt
    rw [hok'.aig_ptr_eq, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have hmptr_64 : cfg.aig_ptr.toNat + 8 * hdr'.aig_len.toNat < 2 ^ 64 := by omega
  have hmptr_bv : hdr'.aig_ptr + (hdr'.aig_len.setWidth 64 <<< OfNat.ofNat 3) =
      cfg.aig_ptr + BitVec.ofNat 64 (8 * hdr'.aig_len.toNat) := by
    rw [hok'.hdr_aig]; exact bv64_marksPtr_bv cfg.aig_ptr hdr'.aig_len hmptr_64
  have hmptr_toNat : (cfg.aig_ptr + BitVec.ofNat 64 (8 * hdr'.aig_len.toNat)).toNat =
      cfg.aig_ptr.toNat + 8 * hdr'.aig_len.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8 * hdr'.aig_len.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt hmptr_64]
  have hwe_toNat : hdr'.work_end.toNat = cfg.work_base.toNat + cfg.avail := by
    rw [hok'.hdr_we, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : cfg.avail < 2 ^ 64), Nat.mod_eq_of_lt hfit_c]
  exact ⟨haig_le_cap, haig_bd, htot_c, haig_toNat, hmptr_64, hmptr_bv, hmptr_toNat, hwe_toNat⟩

private theorem drv_dimacs_post_kissat {cfg : BVWorkspaceCfg} {hdr3 : BVHdrState}
    {progPtr workPtr : BitVec 64} {workCap : BitVec 64} {padNat : Nat}
    {progBytes : List UInt8} {R padR : Mem 64 → Prop} {g' : Aig} {marks1 : List UInt8}
    {rootLit : BitVec 32} {m5 : Mem 64}
    (hwb : cfg.work_base = workPtr + BitVec.ofNat 64 padNat)
    (hge : padNat ≤ workCap.toNat)
    (hav : cfg.avail = workCap.toNat - padNat) (hfit : cfg.work_base.toNat + cfg.avail < 2 ^ 64)
    (h128 : cfg.work_base.toNat + 128 ≤ hdr3.dimacs_start.toNat)
    (hdend : hdr3.dimacs_start.toNat +
      (encodeDimacs (Ref.Tseitin.tseitin g' (marksToBool marks1)
        (UInt32.ofBitVec rootLit))).length = cfg.work_base.toNat + cfg.avail)
    (hkcap : (hdr3.dimacs_start - cfg.work_base).toNat =
      hdr3.dimacs_start.toNat - cfg.work_base.toNat)
    (hpadR : padR = region workPtr padNat ⋆ R)
    (hm5 : (bytes hdr3.dimacs_start (encodeDimacs (Ref.Tseitin.tseitin g' (marksToBool marks1)
        (UInt32.ofBitVec rootLit))) ⋆
      region cfg.work_base (hdr3.dimacs_start - cfg.work_base).toNat ⋆
      (bytes progPtr progBytes ⋆ padR)) m5) :
    (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ R) m5 := by
  have hm5_d : (bvDimacsMem cfg.work_base hdr3.dimacs_start cfg.avail
      (encodeDimacs (Ref.Tseitin.tseitin g' (marksToBool marks1) (UInt32.ofBitVec rootLit))) ⋆
      (bytes progPtr progBytes ⋆ padR)) m5 := by
    rw [hkcap] at hm5; unfold bvDimacsMem; exact sep_ac hm5
  have hm5_r := sep_mono (P' := region cfg.work_base cfg.avail)
    (fun _ h => bvDimacsMem_to_region hfit (by omega) hdend h) hm5_d
  rw [hav] at hm5_r
  exact drv_restore_pad padNat hge hwb (by rw [← hpadR]; exact sep_ac hm5_r)

/-! ## 2. `bv_solve_bytes_wp` -/

public section

theorem bv_solve_bytes_wp (Γ : Env)
    (hValidate : ∀ xs m Q X, bvValidateSpec xs m Q X →
      Γ "bv_validate" [i64, i64] [.bool] xs m Q X)
    (hInit : ∀ xs m Q X, bvInitWorkspaceSpec xs m Q X →
      Γ "bv_init_workspace" [i64, i64, i64, i64] [.bool] xs m Q X)
    (hEvalProg : ∀ xs m Q X, bvEvalProgramSpec xs m Q X →
      Γ "bv_eval_program" [i64] [.bool] xs m Q X)
    (hCoi : ∀ xs m Q X, bvCoiMarkSpec xs m Q X →
      Γ "bv_coi_mark" [i64, i32] [] xs m Q X)
    (hDimacs : ∀ xs m Q X, bvDimacsWriteSpec xs m Q X →
      Γ "bv_dimacs_write" [i64, i32] [.bool] xs m Q X)
    (hKissat : ∀ xs m Q X, kissatSolveBytesUnsatSpec xs m Q X →
      Γ "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X) :
    ∀ xs m Q X, bvSolveBytesSpec xs m Q X → Func.wp Γ bv_solve_bytes_body xs m Q X := by
  rintro ⟨progPtr, progLen, workPtr, workCap, fuel, ⟨⟩⟩ m Q X ⟨progBytes, R, hplen, hm, hQ⟩
  c0_hstraight
  c0_hsplit
  · c0_hstraight
    exact hQ 0#64 m hm (fun h => absurd h (by decide)) fun htu => absurd hc htu.1
  · have hfuel : fuel ≠ 0#64 := hc; clear hc
    c0_hstraight
    c0_hsplit
    · c0_hstraight
      exact hQ 0#64 m hm (fun h => absurd h (by decide)) fun htu => absurd hc htu.2.1
    · have hpptr : progPtr ≠ 0#64 := hc; clear hc
      c0_hstraight
      c0_hsplit
      · c0_hstraight
        exact hQ 0#64 m hm (fun h => absurd h (by decide)) fun htu => absurd hc htu.2.2.1
      · have hwptr : workPtr ≠ 0#64 := hc; clear hc
        c0_hstraight
        refine head_wp_jnz rfl (fun hc => ?_) (fun hc => ?_)
        · dsimp only [Arg.val, Prod.fst] at hc
          c0_hstraight
          exact hQ 0#64 m hm (fun h => absurd h (by decide)) fun htu =>
            False.elim (drv_ult_sub_max_contra workPtr workCap hc htu.2.2.2.2.1)
        · dsimp only [Arg.val, Prod.fst] at hc
          have hwc_fit : workPtr.toNat + workCap.toNat < 2 ^ 64 :=
            drv_ult_sub_max_toNat workPtr workCap hc
          clear hc
          c0_hstraight
          let padNat := (8 - workPtr.toNat % 8) % 8
          have hpad_eq : (((8 : BitVec 64) - (workPtr &&& (7 : BitVec 64))) &&&
              (7 : BitVec 64)).toNat = padNat := bv64_pad_eq workPtr
          have hpad_bv : (((8 : BitVec 64) - (workPtr &&& (7 : BitVec 64))) &&&
              (7 : BitVec 64)) = BitVec.ofNat 64 padNat := by
            apply BitVec.eq_of_toNat_eq
            rw [hpad_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : padNat < 2 ^ 64)]
          have hpad128 : ((8 - (workPtr &&& (7 : BitVec 64)) &&& (7 : BitVec 64)).toNat +
              BitVec.toNat (128 : BitVec 64)) % 2 ^ 64 = padNat + 128 := by
            rw [hpad_eq, show BitVec.toNat (128 : BitVec 64) = 128 from rfl,
              Nat.mod_eq_of_lt (by omega : padNat + 128 < 2 ^ 64)]
          c0_hsplit
          · c0_hstraight
            exact hQ 0#64 m hm (fun h => absurd h (by decide)) fun htu => by
              have hc' : workCap.toNat < padNat + 128 := by rw [hpad128] at hc; exact hc
              have hge := htu.2.2.2.2.2.1
              omega
          · have hwc_ge : padNat + 128 ≤ workCap.toNat := by rw [hpad128] at hc; omega
            clear hc
            let workBase := workPtr + BitVec.ofNat 64 padNat
            let avail := workCap.toNat - padNat
            let padR := region workPtr padNat ⋆ R
            have hav_ge : 128 ≤ avail := by omega
            have hwb_toNat : workBase.toNat = workPtr.toNat + padNat := by
              dsimp only [workBase]
              rw [BitVec.toNat_add, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by omega : padNat < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : workPtr.toNat + padNat < 2 ^ 64)]
            have hwb_avail_fit : workBase.toNat + avail < 2 ^ 64 := by omega
            have hm_pad : (bytes progPtr progBytes ⋆ region workBase avail ⋆ padR) m :=
              drv_split_pad padNat (by omega) rfl hm
            clear hm
            c0_hstraight
            rw [hpad_bv]
            have hav_bv : workCap - BitVec.ofNat 64 padNat = BitVec.ofNat 64 avail := by
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : padNat < 2 ^ 64)]; omega)),
                BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by omega : padNat < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : avail < 2 ^ 64)]
            rw [hav_bv]
            drv_call hValidate
            refine ⟨progBytes, region workBase avail ⋆ padR, hplen, sep_ac hm_pad, fun r hr => ?_⟩
            c0_hsplit
            · have hr_t : r = true := hc
              obtain ⟨_, hprog_fit, hv⟩ := hr.mp hr_t
              obtain ⟨vars, cwords, nodes, prog, hp⟩ := validBVP1_parse hv
              drv_call hInit
              have hav64 : (BitVec.ofNat 64 avail).toNat = avail := by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : avail < 2 ^ 64)]
              refine ⟨progBytes, vars, cwords, nodes, prog, padR, rfl, hp, hprog_fit,
                by rw [hav64]; exact hwb_avail_fit,
                by rw [hav64]; exact sep_ac hm_pad, drv_split_init ?_ ?_⟩
              · intro cfg hdr ab so aw ht lp m1 hcfg_wb hcfg_av hoom1 hinv1 hm1
                have hcfg_wb' : cfg.work_base = workPtr + BitVec.ofNat 64 padNat := hcfg_wb
                have hcfg_av' : cfg.avail = avail := by
                  rw [hcfg_av, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : avail < 2 ^ 64)]
                c0_hsplit
                · drv_call hEvalProg
                  refine ⟨cfg, progPtr, progBytes, vars, cwords, nodes, prog, hdr,
                    ⟨countAtoms progBytes cfg.n_vars - 1, #[]⟩, ab, so, aw, ht, lp, padR,
                    hcfg_wb.symm, hoom1, hinv1, hm1,
                    fun ret hdr' g' so' aw' ht' lp' m2 hok' haig' _ hrt' hret_t hconst hm2 => ?_⟩
                  c0_hsplit
                  · have hret : ret = true := hc
                    clear hc
                    obtain ⟨hoom', hinv'⟩ := hret_t hret
                    have hrt_lt_nn : hdr'.root_node.toNat < cfg.n_nodes := by
                      rw [hinv'.root_eq, hinv'.nn_eq]; exact hp.valid.root_lt
                    have hrt_len : hdr'.root_node.toNat < so'.length := by
                      rw [hok'.so_len]; exact hrt_lt_nn
                    have hm2_hso := drv_blast_focus_hdr_so hok'.hdr_so hm2
                    rw [hcfg_wb'] at hm2_hso
                    clear hm2
                    c0_hstraight
                    rw [← hcfg_wb'] at hm2_hso
                    have hm2_bl := drv_blast_unfocus_hdr_so hok'.hdr_so hm2_hso
                    clear hm2_hso
                    let rootLit := so'.getD hdr'.root_node.toNat 0#32
                    have hrt_get : so'[hdr'.root_node.toNat]'hrt_len = rootLit :=
                      list_getD_eq_getElem so' 0#32 hrt_len
                    have hroot_nd : NodeDenotes progBytes nodes g' so' lp' hdr'.lits_len.toNat
                        (u32At progBytes 5) :=
                      hinv'.prefix_ok hoom' _ (by rw [hinv'.nn_eq]; exact hp.valid.root_lt)
                    have hroot_idx : hdr'.root_node.toNat = u32At progBytes 5 := hinv'.root_eq
                    have htu_root0 :
                        bvSolveTrivialUnsatCond progPtr progBytes workPtr workCap fuel →
                        rootLit = 0#32 :=
                      drv_tu_root_zero (cfg := cfg) (hdr := hdr) (hdr' := hdr')
                        (hrt_lt_nn := hrt_lt_nn) (hinv1_nv := hinv1.nv_eq)
                        (hinv1_nn := hinv1.nn_eq) (hinv1_nc := hinv1.nc_eq)
                        (hroot_idx := hroot_idx) hconst
                    c0_hsplit
                    · have hr0 : rootLit = 0#32 := by rw [hrt_get] at hc; exact hc
                      c0_hstraight
                      have hm2_reg := drv_blast_to_pad_reg hok' hcfg_av' hm2_bl
                      exact hQ 20#64 _ (drv_restore_pad padNat (by omega) rfl
                        (by rw [← hcfg_wb]; exact hm2_reg))
                        (fun _ => prog_unsat_of_root_false hp hroot_nd (fun ρ => by
                          rw [← hroot_idx]
                          change g'.evalLit ρ (UInt32.ofBitVec rootLit) = false
                          rw [hr0]; exact Aig.evalLit_zero g' ρ))
                        (fun _ => rfl)
                    · have hr_ne0 : rootLit ≠ 0#32 := by rw [hrt_get] at hc; exact hc
                      clear hc
                      c0_hstraight
                      c0_hsplit
                      · have hr1 : rootLit = 1#32 := by rw [hrt_get] at hc; exact hc
                        have hm2_reg := drv_blast_to_pad_reg hok' hcfg_av' hm2_bl
                        rw [hcfg_wb'] at hm2_reg
                        clear hm2_bl
                        c0_hstraight
                        rw [← hcfg_wb', Std.ExtHashMap.sep_emp] at hm
                        have hm2_st : (bytes progPtr progBytes ⋆
                            region cfg.work_base (workCap.toNat - padNat) ⋆
                            (region workPtr padNat ⋆ R)) _ :=
                          sep_ac hm
                        exact hQ 10#64 _ (drv_restore_pad padNat (by omega) rfl
                          (by rw [← hcfg_wb]; exact hm2_st))
                          (fun h => absurd h (by decide))
                          fun htu => absurd (htu_root0 htu) (by rw [hr1]; decide)
                      · have hr_ne1 : rootLit ≠ 1#32 := by rw [hrt_get] at hc; exact hc
                        clear hc
                        have haig_len_eq : hdr'.aig_len.toNat = g'.A + 1 + g'.nodes.size :=
                          haig'.aig_len_eq
                        obtain ⟨haig_le_cap, haig_bd, htot_c, haig_toNat, hmptr_64,
                            hmptr_bv, hmptr_toNat, hwe_toNat⟩ :=
                          drv_marksPtr_bounds hok' haig' haig_len_eq
                        have hfit_c := hok'.fit
                        let marksPtr := cfg.aig_ptr + BitVec.ofNat 64 (8 * hdr'.aig_len.toNat)
                        change marksPtr.toNat =
                          cfg.aig_ptr.toNat + 8 * hdr'.aig_len.toNat at hmptr_toNat
                        let hdr'' : BVHdrState := { hdr' with marks_ptr := marksPtr }
                        have hok'' : BVWorkspaceOk cfg hdr'' ab so' aw' ht' lp' := { hok' with }
                        have hm2_hso := drv_blast_focus_hdr_so hok'.hdr_so hm2_bl
                        rw [hcfg_wb'] at hm2_hso
                        clear hm2_bl
                        c0_hstraight
                        rw [hmptr_bv, ← hcfg_wb',
                          show { hdr' with marks_ptr := marksPtr } = hdr'' from rfl,
                          Std.ExtHashMap.sep_emp] at hm
                        have hm2_bl' := drv_blast_unfocus_hdr_so hok''.hdr_so (sep_ac hm)
                        clear hm
                        refine wp_join0 (fun ml => (bytes progPtr progBytes ⋆
                            bvBlastMem cfg hdr'' ab so' aw' ht' lp' ⋆ padR) ml) ?_ ?_
                        · intro Js ml hml
                          have hm2_reg := drv_blast_to_pad_reg hok'' hcfg_av' hml
                          rw [hcfg_wb'] at hm2_reg
                          clear hml
                          c0_hstraight
                          rw [← hcfg_wb', Std.ExtHashMap.sep_emp] at hm
                          have hm2_st : (bytes progPtr progBytes ⋆
                              region cfg.work_base (workCap.toNat - padNat) ⋆
                              (region workPtr padNat ⋆ R)) _ :=
                            sep_ac hm
                          exact hQ 0#64 _ (drv_restore_pad padNat (by omega) rfl
                            (by rw [← hcfg_wb]; exact hm2_st))
                            (fun h => absurd h (by decide))
                            fun htu => absurd (htu_root0 htu) hr_ne0
                        · intro Js hJs
                          have hm2_hdr := drv_blast_focus_hdr_so hok''.hdr_so hm2_bl'
                          rw [hcfg_wb'] at hm2_hdr
                          c0_hstraight
                          c0_hsplit
                          · exfalso; have hc' : hdr'.work_end.toNat < marksPtr.toNat := hc; omega
                          · clear hc
                            c0_hstraight
                            c0_hsplit
                            · exact hJs _ hm2_bl'
                            · clear hm2_hdr
                              have hsub_we : (hdr'.work_end - marksPtr).toNat =
                                  hdr'.work_end.toNat - marksPtr.toNat :=
                                BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
                              have hm_fit_coi : 128 + cfg.atom_bytes + cfg.slice_bytes +
                                  8 * hdr'.aig_len.toNat + hdr'.aig_len.toNat ≤ cfg.avail := by
                                have hc' : ¬ hdr'.work_end.toNat - marksPtr.toNat <
                                    (hdr'.aig_len.setWidth 64).toNat := by
                                  rw [← hsub_we]; exact hc
                                rw [BitVec.toNat_setWidth,
                                  Nat.mod_eq_of_lt (by have := hdr'.aig_len.isLt; omega)] at hc'
                                omega
                              clear hc
                              obtain ⟨marks0, hm0_len, hm_coi⟩ :=
                                drv_blast_to_coi hok'' haig_le_cap hm_fit_coi hm2_bl'
                              clear hm2_bl'
                              have hm_coi_focus := drv_coi_focus hok''.hdr_aig rfl hm_coi
                              clear hm_coi
                              drv_call hCoi
                              refine ⟨hdr'', g', aw'.take hdr'.aig_len.toNat, marks0,
                                region (cfg.work_base + 128)
                                    (cfg.aig_ptr.toNat - (cfg.work_base.toNat + 128)) ⋆
                                  region (marksPtr + BitVec.ofNat 64 marks0.length)
                                    (cfg.work_base.toNat + cfg.avail -
                                      (marksPtr.toNat + marks0.length)) ⋆
                                  (bytes progPtr progBytes ⋆ padR),
                                haig'.wf, haig'.num_atoms_eq, haig_len_eq, haig_bd,
                                aigWordsMatch_take haig'.words_match haig_len_eq
                                  (by rw [hok'.aig_len_eq]; exact haig_le_cap),
                                by rw [List.length_take_of_le (by rw [hok'.aig_len_eq]; exact
                                  haig_le_cap)],
                                hm0_len,
                                by
                                  intro h0
                                  have h0' : marksPtr = 0#64 := h0
                                  rw [h0', BitVec.toNat_zero] at hmptr_toNat
                                  omega,
                                by show marksPtr.toNat + marks0.length < 2 ^ 64; omega,
                                by
                                  rw [← hcfg_wb']
                                  exact sep_ac hm_coi_focus,
                                fun marks1 m3 hm1_len hm1_bool hm3 => ?_⟩
                              have hlen_take :
                                  (aw'.take hdr'.aig_len.toNat).length = marks0.length := by
                                rw [hm0_len, List.length_take_of_le
                                  (hok'.aig_len_eq ▸ haig_le_cap)]
                              rw [← hcfg_wb', ← hlen_take] at hm3
                              have hm3_coi := drv_coi_unfocus hok''.hdr_aig rfl
                                (by rw [hm1_len, List.length_take_of_le
                                  (hok'.aig_len_eq ▸ haig_le_cap)]) hm3
                              have hsw : (hdr'.root_node.setWidth 64).toNat =
                                  hdr'.root_node.toNat := by simp [BitVec.toNat_setWidth]
                              have hrt_sw : so'[(hdr'.root_node.setWidth 64).toNat]'(by
                                  rw [hsw]; exact hrt_len) = rootLit := by
                                simp only [hsw, hrt_get]
                              rw [hrt_sw] at hm1_bool
                              have hroot_lt_aig : (so'[(hdr'.root_node.setWidth 64).toNat]'(by
                                  rw [hsw]; exact hrt_len) >>> 1).toNat < hdr''.aig_len.toNat := by
                                rw [hrt_sw, haig_len_eq]
                                unfold NodeDenotes at hroot_nd
                                rw [hp.root_get] at hroot_nd
                                simpa [rootLit, hroot_idx] using hroot_nd.1
                              dsimp only
                              drv_call hDimacs
                              rw [hrt_sw]
                              have hlen_take' : (aw'.take hdr'.aig_len.toNat).length =
                                  hdr'.aig_len.toNat :=
                                List.length_take_of_le (hok'.aig_len_eq ▸ haig_le_cap)
                              have hm1_len' : marks1.length = hdr'.aig_len.toNat := hm1_len
                              refine ⟨cfg.work_base, cfg.aig_ptr, marksPtr, cfg.avail, hdr'', g',
                                aw'.take hdr'.aig_len.toNat, marks1,
                                bytes progPtr progBytes ⋆ padR,
                                hcfg_wb.symm, hfit_c, hok''.hdr_wb, hok''.hdr_we,
                                hok''.hdr_aig, rfl, by omega, by rw [hlen_take'],
                                by rw [hlen_take', hm1_len']; omega,
                                haig'.wf, haig'.num_atoms_eq,
                                haig_len_eq, haig_bd,
                                aigWordsMatch_take haig'.words_match haig_len_eq
                                  (by rw [hok'.aig_len_eq]; exact haig_le_cap),
                                hlen_take',
                                hm1_len,
                                by rw [← hrt_sw]; exact hroot_lt_aig,
                                by
                                  intro h0
                                  have h0' : marksPtr = 0#64 := h0
                                  rw [h0', BitVec.toNat_zero] at hmptr_toNat
                                  omega,
                                hm3_coi, fun ret hdr3 m4 => ⟨?_, ?_⟩⟩
                              · rintro rfl ⟨hvalid, hdend, hdlen, h128, hm4⟩
                                c0_hsplit
                                · clear hc
                                  rw [hcfg_wb'] at hm4
                                  c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
                                  rw [← hcfg_wb'] at hm4
                                  have hm4_dim :
                                      (region cfg.work_base
                                          (hdr3.dimacs_start.toNat - cfg.work_base.toNat) ⋆
                                        bytes hdr3.dimacs_start
                                          (encodeDimacs (Ref.Tseitin.tseitin g' (marksToBool marks1)
                                            (UInt32.ofBitVec rootLit))) ⋆
                                        (bytes progPtr progBytes ⋆ padR)) m4 := by
                                    have hm4' : ((bvHdrMem cfg.work_base hdr3 ⋆
                                        region (cfg.work_base + 128)
                                          (hdr3.dimacs_start.toNat - (cfg.work_base.toNat + 128)) ⋆
                                        bytes hdr3.dimacs_start
                                          (encodeDimacs (Ref.Tseitin.tseitin g' (marksToBool marks1)
                                            (UInt32.ofBitVec rootLit)))) ⋆
                                        (bytes progPtr progBytes ⋆ padR)) m4 := sep_ac hm4
                                    have hsp := sep_mono (P' := bvDimacsMem cfg.work_base
                                        hdr3.dimacs_start cfg.avail _)
                                      (fun _ h => bvHdrDimacs_to_dimacsMem h128 h) hm4'
                                    unfold bvDimacsMem at hsp
                                    exact sep_ac hsp
                                  clear hm4
                                  have hlen64 : (hdr3.dimacs_len.setWidth 64).toNat =
                                      (encodeDimacs (Ref.Tseitin.tseitin g' (marksToBool marks1)
                                        (UInt32.ofBitVec rootLit))).length := by
                                    rw [BitVec.toNat_setWidth,
                                      Nat.mod_eq_of_lt (by have := hdr3.dimacs_len.isLt; omega),
                                      hdlen]
                                  have hkcap : (hdr3.dimacs_start - cfg.work_base).toNat =
                                      hdr3.dimacs_start.toNat - cfg.work_base.toNat :=
                                    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
                                  have hkcap_ge :
                                      8 ≤ (hdr3.dimacs_start - cfg.work_base).toNat := by omega
                                  have hkcap_fit :
                                      (hdr3.dimacs_start - cfg.work_base).toNat ≤ 2 ^ 64 := by
                                    have := (hdr3.dimacs_start - cfg.work_base).isLt; omega
                                  rw [hcfg_wb'] at hm4_dim
                                  c0_hstraight
                                  rw [← hcfg_wb', Std.ExtHashMap.sep_emp] at hm
                                  drv_call hKissat
                                  refine ⟨encodeDimacs (Ref.Tseitin.tseitin g' (marksToBool marks1)
                                      (UInt32.ofBitVec rootLit)),
                                    bytes progPtr progBytes ⋆ padR, hlen64,
                                    by rw [hdend, hcfg_wb', hcfg_av']; exact hwb_avail_fit,
                                    by rw [← hcfg_wb', hkcap]; omega, ?_,
                                    fun r m5 hm5 hr_unsat => ?_⟩
                                  · rw [← hcfg_wb', hkcap]; exact sep_ac hm
                                  exact hQ r m5
                                    (drv_dimacs_post_kissat hcfg_wb' (by omega) hcfg_av'
                                      hfit_c h128 hdend hkcap rfl (by rw [hcfg_wb']; exact hm5))
                                    (fun hr20 => prog_unsat_of_dimacs_unsat haig'.wf hp hroot_nd
                                      (by rw [← hroot_idx]; exact hvalid)
                                      (by rw [← hroot_idx]; exact hr_unsat hr20))
                                    fun htu => absurd (htu_root0 htu) hr_ne0
                                · exact absurd hc (by decide)
                              · rintro rfl hm4
                                c0_hsplit
                                · exact absurd hc (by decide)
                                · clear hc
                                  have hm4_reg : (bytes progPtr progBytes ⋆
                                      region cfg.work_base (workCap.toNat - padNat) ⋆ padR) m4 := by
                                    have h1 : ((bvHdrMem cfg.work_base hdr3 ⋆
                                        region (cfg.work_base + 128) (avail - 128)) ⋆
                                        (bytes progPtr progBytes ⋆ padR)) m4 := by
                                      rw [← hcfg_av']; exact sep_ac hm4
                                    have hm4_r := sep_mono (P' := region cfg.work_base avail)
                                      (fun _ h => bvHdrRegion_to_region hav_ge
                                        (by omega) h) h1
                                    exact sep_ac hm4_r
                                  rw [hcfg_wb'] at hm4_reg
                                  clear hm4
                                  c0_hstraight
                                  rw [← hcfg_wb', Std.ExtHashMap.sep_emp] at hm
                                  dsimp only [padR] at hm
                                  have hm4_st : (bytes progPtr progBytes ⋆
                                      region cfg.work_base (workCap.toNat - padNat) ⋆
                                      (region workPtr padNat ⋆ R)) _ :=
                                    sep_ac hm
                                  exact hQ 0#64 _ (drv_restore_pad padNat (by omega) rfl
                                    (by rw [← hcfg_wb]; exact hm4_st))
                                    (fun h => absurd h (by decide))
                                    fun htu => absurd (htu_root0 htu) hr_ne0
                  · have hret_f : ret = false := by cases ret <;> simp_all
                    have hm2_reg := drv_blast_to_pad_reg hok' hcfg_av' hm2
                    rw [hcfg_wb'] at hm2_reg
                    clear hm2
                    c0_hstraight
                    rw [← hcfg_wb', Std.ExtHashMap.sep_emp] at hm
                    have hm2_st : (bytes progPtr progBytes ⋆
                        region cfg.work_base (workCap.toNat - padNat) ⋆
                        (region workPtr padNat ⋆ R)) _ :=
                      sep_ac hm
                    exact hQ 0#64 _ (drv_restore_pad padNat (by omega) rfl
                      (by rw [← hcfg_wb]; exact hm2_st))
                      (fun h => absurd h (by decide)) fun htu => by
                      have hbc : ∀ i < cfg.n_nodes, u32At progBytes
                          (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * i) = opBConst := by
                        intro i hi
                        rw [hinv1.nv_eq, hinv1.nc_eq]
                        exact htu.2.2.2.2.2.2.2.2.1 i (by rw [← hinv1.nn_eq]; exact hi)
                      exact absurd ((hconst hbc).1 ▸ hret_f) (by decide)
                · exfalso; cases hc
              · intro hnf
                c0_hsplit
                · exfalso; cases hc
                · dsimp only [workBase] at hm_pad
                  have hav_8 : 8 ≤ avail := by omega
                  have hav_64 : avail ≤ 2 ^ 64 := by omega
                  c0_hstraight
                  rw [Std.ExtHashMap.sep_emp] at hm
                  dsimp only [padR] at hm
                  have hm' : (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ R) _ :=
                    drv_restore_pad padNat (by omega) rfl (sep_ac hm)
                  exact hQ 0#64 _ hm' (fun h => absurd h (by decide)) fun htu => by
                    rw [hav64] at hnf
                    exact absurd htu.2.2.2.2.2.2.2.1 hnf
            · have hr_f : r = false := by cases r <;> simp_all
              dsimp only [workBase] at hm_pad
              have hav_8 : 8 ≤ avail := by omega
              have hav_64 : avail ≤ 2 ^ 64 := by omega
              c0_hstraight
              rw [Std.ExtHashMap.sep_emp] at hm
              dsimp only [padR] at hm
              have hm' : (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ R) _ :=
                drv_restore_pad padNat (by omega) rfl (sep_ac hm)
              exact hQ 0#64 _ hm' (fun h => absurd h (by decide)) fun htu => by
                have htrue : false = true := (hr_f ▸ hr).mpr ⟨hpptr, htu.2.2.2.1, htu.2.2.2.2.2.2.1⟩
                cases htrue

end

end LeanQbe.T.Examples.Bitblast.Proof
