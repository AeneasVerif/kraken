/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Src.Header
public import LeanQbe.T.Examples.Bitblast.Ref.Aig
public import LeanQbe.T.Logic.Mem
public import LeanQbe.T.Logic.Bytes
public import LeanQbe.T.Logic.Rules
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.Cells
import LeanQbe.T.Logic.ProofKit
import Kraken.Separation

/-!
# Bitblast Workspace Layout, `BVHdr` Memory Model & Kissat Handoff (`Bitblast.Proof.Arena`)

Defines:
- `BVHdrState` (`128 B`: `10 × u64` + `12 × u32`) and `bvHdrMem` with `O(1)` load/store helpers
- `BVBlastMem` separation invariant for `BVHdr`, `atom_base`, `slice_off`, `aig`, `ht`, `lits`
- `BVCoiMem` and `BVDimacsMem` layouts for backward COI marking and top-down DIMACS emission
- Region split/merge lemmas (`region_to_bvHdrMem`, `bvBlastMem_to_coiMem`,
  `bvCoiMem_to_kissatHandoff`, `bvDimacsMem_to_region`) for the unchanged
  `kissat_solve_bytes` handoff.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.ProofKit
open LeanQbe.T.Examples.Bitblast.Src
open LeanQbe.T.Examples.Bitblast.Ref
open Kraken.Bedrock2.Test

/-! ## 1. `BVHdr` State and Separation Predicate (`128 B`) -/

@[expose] public section

/-- Logical mirror of the `128`-byte C0 `BVHdr` struct (`10` `u64` fields + `12` `u32` fields). -/
structure BVHdrState where
  work_base : BitVec 64
  work_end : BitVec 64
  prog_ptr : BitVec 64
  aig_ptr : BitVec 64
  ht_ptr : BitVec 64
  atom_base_ptr : BitVec 64
  slice_off_ptr : BitVec 64
  lits_ptr : BitVec 64
  marks_ptr : BitVec 64
  dimacs_start : BitVec 64
  n_vars : BitVec 32
  n_nodes : BitVec 32
  n_cwords : BitVec 32
  root_node : BitVec 32
  num_atoms : BitVec 32
  aig_len : BitVec 32
  aig_cap : BitVec 32
  ht_mask : BitVec 32
  lits_len : BitVec 32
  lits_cap : BitVec 32
  oom : BitVec 32
  dimacs_len : BitVec 32

/-- The `10` leading `u64` words of `BVHdrState` (`+0 .. +72`). -/
def BVHdrState.u64s (s : BVHdrState) : List (BitVec 64) :=
  [ s.work_base, s.work_end, s.prog_ptr, s.aig_ptr, s.ht_ptr
  , s.atom_base_ptr, s.slice_off_ptr, s.lits_ptr, s.marks_ptr, s.dimacs_start ]

/-- The `12` trailing `u32` words of `BVHdrState` (`+80 .. +124`). -/
def BVHdrState.u32s (s : BVHdrState) : List (BitVec 32) :=
  [ s.n_vars, s.n_nodes, s.n_cwords, s.root_node
  , s.num_atoms, s.aig_len, s.aig_cap, s.ht_mask
  , s.lits_len, s.lits_cap, s.oom, s.dimacs_len ]

/-- Exact `128`-byte separation predicate for `BVHdr` at `h`. -/
def bvHdrMem (h : BitVec 64) (s : BVHdrState) : Mem 64 → Prop :=
  array64 h s.u64s ⋆ array (t := i32) (h + 80) s.u32s

/-- Packed `u64` encoding `(lhs | (rhs << 32))` of an AIG gate in `aig[idx]`. -/
def packAigGate (lhs rhs : UInt32) : BitVec 64 :=
  lhs.toBitVec.setWidth 64 ||| (rhs.toBitVec.setWidth 64 <<< 32)

/-- Predicate stating that `aigWords` matches `g : Ref.Aig` at gate indices `g.A + 1 ..< len`. -/
structure AigWordsMatch (g : Aig) (aigWords : List (BitVec 64)) : Prop where
  bound : g.A + 1 + g.nodes.size ≤ aigWords.length
  gate_eq : ∀ i (hi : i < g.nodes.size),
    aigWords[g.A + 1 + i]'(by have := bound; omega) = packAigGate g.nodes[i].1 g.nodes[i].2

/-- Combined bitblasting workspace layout (`BVHdr`, `atom_base`, `slice_off`, `aig`, `ht`, `lits`
plus padding slices) partitioning `[work_base, work_end)`. -/
structure BVWorkspaceCfg where
  work_base : BitVec 64
  avail : Nat
  n_vars : Nat
  n_nodes : Nat
  aig_cap : Nat
  ht_slots : Nat
  lits_cap : Nat
  atom_bytes : Nat
  slice_bytes : Nat
  aig_ptr : BitVec 64
  ht_ptr : BitVec 64
  lits_ptr : BitVec 64
  lits_bytes : Nat

/-- Separation invariant for the bitblasting workspace `[work_base, work_base + avail)`. -/
def bvBlastMem (cfg : BVWorkspaceCfg) (hdr : BVHdrState) (atomBases sliceOffs : List (BitVec 32))
    (aigWords : List (BitVec 64)) (htSlots litsPool : List (BitVec 32)) : Mem 64 → Prop :=
  bvHdrMem cfg.work_base hdr ⋆
  array (t := i32) (cfg.work_base + 128) atomBases ⋆
  region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
    (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
  array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) sliceOffs ⋆
  region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
    (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
  array64 cfg.aig_ptr aigWords ⋆
  array (t := i32) cfg.ht_ptr htSlots ⋆
  array (t := i32) cfg.lits_ptr litsPool ⋆
  region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
    (cfg.lits_bytes - 4 * cfg.lits_cap)

/-- Consistency invariants on `BVWorkspaceCfg` ensuring exact partition of `[work_base, avail)`. -/
structure BVWorkspaceOk (cfg : BVWorkspaceCfg) (hdr : BVHdrState)
    (atomBases sliceOffs : List (BitVec 32)) (aigWords : List (BitVec 64))
    (htSlots litsPool : List (BitVec 32)) : Prop where
  fit : cfg.work_base.toNat + cfg.avail < 2 ^ 64
  hdr_wb : hdr.work_base = cfg.work_base
  hdr_we : hdr.work_end = cfg.work_base + BitVec.ofNat 64 cfg.avail
  hdr_ab : hdr.atom_base_ptr = cfg.work_base + 128
  hdr_so : hdr.slice_off_ptr = cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)
  hdr_aig : hdr.aig_ptr = cfg.aig_ptr
  hdr_ht : hdr.ht_ptr = cfg.ht_ptr
  hdr_lits : hdr.lits_ptr = cfg.lits_ptr
  hdr_nv : hdr.n_vars = BitVec.ofNat 32 cfg.n_vars
  hdr_nn : hdr.n_nodes = BitVec.ofNat 32 cfg.n_nodes
  hdr_acap : hdr.aig_cap = BitVec.ofNat 32 cfg.aig_cap
  hdr_htmask : hdr.ht_mask = BitVec.ofNat 32 (cfg.ht_slots - 1)
  hdr_lcap : hdr.lits_cap = BitVec.ofNat 32 cfg.lits_cap
  atom_align : 4 * cfg.n_vars ≤ cfg.atom_bytes
  slice_align : 4 * cfg.n_nodes ≤ cfg.slice_bytes
  aig_ptr_eq :
    cfg.aig_ptr = cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + cfg.slice_bytes)
  ht_ptr_eq : cfg.ht_ptr = cfg.aig_ptr + BitVec.ofNat 64 (8 * cfg.aig_cap)
  lits_ptr_eq : cfg.lits_ptr = cfg.ht_ptr + BitVec.ofNat 64 (4 * cfg.ht_slots)
  lits_fit : 4 * cfg.lits_cap ≤ cfg.lits_bytes
  total_eq : 128 + cfg.atom_bytes + cfg.slice_bytes + 8 * cfg.aig_cap +
    4 * cfg.ht_slots + cfg.lits_bytes = cfg.avail
  nv_lt : cfg.n_vars < 2 ^ 32
  nn_lt : cfg.n_nodes < 2 ^ 32
  acap_lt : cfg.aig_cap < 2 ^ 28
  ht_pos : 0 < cfg.ht_slots
  ht_lt : cfg.ht_slots ≤ 2 ^ 30
  ht_mask_lt : ∀ x : BitVec 32, (x &&& BitVec.ofNat 32 (cfg.ht_slots - 1)).toNat < cfg.ht_slots
  lcap_lt : cfg.lits_cap < 2 ^ 32
  ab_len : atomBases.length = cfg.n_vars
  so_len : sliceOffs.length = cfg.n_nodes
  aig_len_eq : aigWords.length = cfg.aig_cap
  ht_len : htSlots.length = cfg.ht_slots
  lits_len : litsPool.length = cfg.lits_cap

/-- Post-bitblast / COI + DIMACS workspace partitioning `[work_base, work_base + avail)` into:
`BVHdr`, prefix scratch `[work_base + 128, aig_ptr)`, active AIG `aigWords[0 .. aig_len)`,
COI marks `[marks_ptr, marks_ptr + aig_len)`, and free space `[marks_ptr + aig_len, work_end)`. -/
def bvCoiMem (work_base aig_ptr marks_ptr : BitVec 64) (avail : Nat) (hdr : BVHdrState)
    (aigUsed : List (BitVec 64)) (marks : List UInt8) : Mem 64 → Prop :=
  bvHdrMem work_base hdr ⋆
  region (work_base + 128) (aig_ptr.toNat - (work_base.toNat + 128)) ⋆
  array64 aig_ptr aigUsed ⋆
  bytes marks_ptr marks ⋆
  region (marks_ptr + BitVec.ofNat 64 marks.length)
    (work_base.toNat + avail - (marks_ptr.toNat + marks.length))

/-- Final workspace state after `bv_dimacs_write` succeeds:
`[work_base, dimacs_start)` is free/scratch `BVHdr + prefix + aig + marks + gap`,
and `[dimacs_start, work_end)` holds exact `dimacsBytes`. -/
def bvDimacsMem (work_base dimacs_start : BitVec 64) (_avail : Nat)
    (dimacsBytes : List UInt8) : Mem 64 → Prop :=
  region work_base (dimacs_start.toNat - work_base.toNat) ⋆
  bytes dimacs_start dimacsBytes

end

/-! ## 2. `BVHdr` Field Load / Store Lemmas and Region Conversions -/

public section

theorem bvHdrState_u64s_len (s : BVHdrState) : s.u64s.length = 10 := rfl

theorem bvHdrState_u32s_len (s : BVHdrState) : s.u32s.length = 12 := rfl

theorem array_to_region {t : Ty} {a : BitVec 64} {xs : List (Val t)} {m : Mem 64}
    (h : t.bytes * xs.length ≤ 2 ^ 64) (hm : array a xs m) :
    region a (t.bytes * xs.length) m :=
  ⟨bytesOf xs, bytesOf_length xs, array_eq_bytesOf a xs h hm⟩

theorem array64_to_region {a : BitVec 64} {xs : List (BitVec 64)} {m : Mem 64}
    (h : 8 * xs.length ≤ 2 ^ 64) (hm : array64 a xs m) :
    region a (8 * xs.length) m := by
  rw [array64_eq_array] at hm
  exact array_to_region (t := i64) h hm

private theorem toBytes_ofInt_eq_nat (v : BitVec 64) :
    Int.toBytes 8 (v.toNat : Int) = Int.toBytes 8 v.toInt := by
  rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := v.toInt)]
  congr 1
  simp only [Int.take]
  rw [BitVec.toInt_eq_msb_cond]
  have h0 : 0 ≤ (v.toNat : Int) := Int.natCast_nonneg _
  have hlt : (v.toNat : Int) < ((2 ^ 64 : Nat) : Int) := by exact_mod_cast v.isLt
  cases v.msb
  · simp
  · simp only [↓reduceIte]
    rw [show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) from rfl, Int.sub_emod_right,
      Int.emod_eq_of_lt h0 hlt]

private theorem word8Array_to_array64 (a : BitVec 64) (xs : List (BitVec 64)) :
    word8Array a xs = array64 a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [word8Array_cons, array64_cons, ih]
    congr 1
    unfold word8 cell64
    rw [toBytes_ofInt_eq_nat x]

private theorem toBytes4_ofInt_eq_setWidth (x : BitVec 64) :
    Int.toBytes 4 (x.toNat : Int) = Int.toBytes 4 (x.setWidth 32).toInt := by
  rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := (x.setWidth 32).toInt)]
  congr 1
  simp only [Int.take]
  have h0 : 0 ≤ ((x.setWidth 32).toNat : Int) := Int.natCast_nonneg _
  have hlt : ((x.setWidth 32).toNat : Int) < ((2 ^ 32 : Nat) : Int) := by
    exact_mod_cast (x.setWidth 32).isLt
  have htoNat : (x.toNat : Int) % ((2 ^ 32 : Nat) : Int) = ((x.setWidth 32).toNat : Int) := by
    rw [BitVec.toNat_setWidth]
    exact_mod_cast rfl
  rw [show (2 : Int) ^ (8 * 4) = ((2 ^ 32 : Nat) : Int) from rfl, htoNat,
    BitVec.toInt_eq_msb_cond]
  cases (x.setWidth 32).msb
  · simp
  · simp only [↓reduceIte]
    rw [Int.sub_emod_right, Int.emod_eq_of_lt h0 hlt]

private theorem int4Array_to_array32 (a : BitVec 64) (xs : List (BitVec 64)) :
    int4Array a xs = array (t := i32) a (xs.map (BitVec.setWidth 32)) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [int4Array_cons, List.map_cons, array_cons, ih]
    congr 1
    unfold int4 cell toBits Ty.bytes Ty.size
    have hsw : ((x.setWidth 32).setWidth 32).toInt = (x.setWidth 32).toInt := by
      rw [show (x.setWidth 32).setWidth 32 = x.setWidth 32 from
        BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_setWidth])]
    exact (hsw ▸ toBytes4_ofInt_eq_setWidth x) ▸ rfl

theorem region_to_array64 {a : BitVec 64} (k : Nat) (hk : 8 * k ≤ 2 ^ 64) {m : Mem 64}
    (hm : region a (8 * k) m) :
    ∃ xs : List (BitVec 64), xs.length = k ∧ array64 a xs m := by
  obtain ⟨xs, hlen, hmem⟩ := region_to_word8Array k hk hm
  rw [word8Array_to_array64] at hmem
  exact ⟨xs, hlen, hmem⟩

theorem region_to_array32 {a : BitVec 64} (k : Nat) (hk : 4 * k ≤ 2 ^ 64) {m : Mem 64}
    (hm : region a (4 * k) m) :
    ∃ xs : List (BitVec 32), xs.length = k ∧ array (t := i32) a xs m := by
  obtain ⟨xs, hlen, hmem⟩ := region_to_int4Array k hk hm
  rw [int4Array_to_array32] at hmem
  exact ⟨xs.map (BitVec.setWidth 32), by simp [hlen], hmem⟩

theorem region_to_bytes {a : BitVec 64} {n : Nat} {m : Mem 64}
    (hm : region a n m) : ∃ bs : List UInt8, bs.length = n ∧ bytes a bs m := by
  obtain ⟨bs, hl, rfl⟩ := hm
  exact ⟨bs, hl, rfl⟩

theorem bvHdrMem_to_region {h : BitVec 64} {s : BVHdrState} {m : Mem 64}
    (hm : bvHdrMem h s m) : region h 128 m := by
  unfold bvHdrMem at hm
  have hr : (region h 80 ⋆ region (h + 80) 48) m := by
    refine sep_mono2
      (fun _ h64 => by
        have h1 := array64_to_region (a := h) (xs := s.u64s)
          (by rw [bvHdrState_u64s_len]; decide) h64
        simpa [bvHdrState_u64s_len] using h1)
      (fun _ h32 => by
        have h1 := array_to_region (t := i32) (a := h + 80) (xs := s.u32s)
          (by simp [Ty.bytes, Ty.size, bvHdrState_u32s_len]) h32
        simpa [Ty.bytes, Ty.size, bvHdrState_u32s_len] using h1) m hm
  exact (congrFun (region_merge_eq (a := h) (n1 := 80) (n2 := 48) (n := 128) rfl (by decide)) m).mp
    hr

private theorem list_eq_10 {α : Type _} (l : List α) (h : l.length = 10) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9, l = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9] := by
  rcases l with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7, _ |
      ⟨x8, _ | ⟨x9, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, rfl⟩

private theorem list_eq_12 {α : Type _} (l : List α) (h : l.length = 12) :
    ∃ y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11,
      l = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11] := by
  rcases l with _ | ⟨y0, _ | ⟨y1, _ | ⟨y2, _ | ⟨y3, _ | ⟨y4, _ | ⟨y5, _ | ⟨y6, _ | ⟨y7, _ |
      ⟨y8, _ | ⟨y9, _ | ⟨y10, _ | ⟨y11, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, rfl⟩

theorem region_to_bvHdrMem {h : BitVec 64} {m : Mem 64} (hm : region h 128 m) :
    ∃ s : BVHdrState, bvHdrMem h s m := by
  have hsp : (region h 80 ⋆ region (h + 80) 48) m :=
    (congrFun (region_merge_eq (a := h) (n1 := 80) (n2 := 48) (n := 128) rfl (by decide)) m).mpr hm
  have harr := sep_mono2
    (fun _ h1 => region_to_array64 10 (by decide) h1)
    (fun _ h2 => region_to_array32 12 (by decide) h2) m hsp
  obtain ⟨u64s, ha⟩ := sep_ex_l.mp harr
  obtain ⟨u32s, hb⟩ := sep_ex_r.mp ha
  rw [sep_pure_l, sep_pure_r] at hb
  obtain ⟨hl64, hl32, hmem⟩ := hb
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, hu64⟩ := list_eq_10 u64s hl64
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, hu32⟩ := list_eq_12 u32s hl32
  rw [hu64, hu32] at hmem
  exact ⟨⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9,
          y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11⟩, hmem⟩

/-! ### `BVHdr` Field Load / Store Helpers -/

section HdrLoadStore
variable {h : BitVec 64} {s : BVHdrState} {R : Mem 64 → Prop} {m : Mem 64}

private theorem load_hdr_u64 (i : Nat) (hi : i < 10) (off : BitVec 64)
    (hoff : off = BitVec.ofNat 64 (8 * i)) (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + off) = some (s.u64s[i]'(by rw [bvHdrState_u64s_len]; exact hi)) := by
  unfold bvHdrMem at hm
  rw [sep_assoc] at hm
  rw [hoff]
  exact loadVal_array64 (by rw [bvHdrState_u64s_len]; exact hi) hm

private theorem load_hdr_u32 (i : Nat) (hi : i < 12) (off : BitVec 64)
    (hoff : off = 80#64 + BitVec.ofNat 64 (4 * i)) (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + off) = some (s.u32s[i]'(by rw [bvHdrState_u32s_len]; exact hi)) := by
  unfold bvHdrMem at hm
  rw [sep_comm (array64 h s.u64s), sep_assoc] at hm
  rw [hoff, ← BitVec.add_assoc]
  exact loadVal_array (t := i32) (by decide) (by rw [bvHdrState_u32s_len]; exact hi) hm

private theorem store_hdr_u64 (i : Nat) (hi : i < 10) (off : BitVec 64)
    (hoff : off = BitVec.ofNat 64 (8 * i)) (v : BitVec 64)
    (hm : (bvHdrMem h s ⋆ R) m)
    (s' : BVHdrState) (hs' : s'.u64s = s.u64s.set i v) (hs32 : s'.u32s = s.u32s) :
    storeOk m i64 (h + off) ∧ (bvHdrMem h s' ⋆ R) (storeMem m i64 (h + off) v) := by
  unfold bvHdrMem at hm ⊢
  rw [sep_assoc] at hm
  rw [hoff]
  obtain ⟨hok, hm'⟩ := store_array64 v (by rw [bvHdrState_u64s_len]; exact hi) hm
  refine ⟨hok, ?_⟩
  rw [hs', hs32, sep_assoc]
  exact hm'

private theorem store_hdr_u32 (i : Nat) (hi : i < 12) (off : BitVec 64)
    (hoff : off = 80#64 + BitVec.ofNat 64 (4 * i)) (v : BitVec 32)
    (hm : (bvHdrMem h s ⋆ R) m)
    (s' : BVHdrState) (hs64 : s'.u64s = s.u64s) (hs' : s'.u32s = s.u32s.set i v) :
    storeOk m i32 (h + off) ∧ (bvHdrMem h s' ⋆ R) (storeMem m i32 (h + off) v) := by
  unfold bvHdrMem at hm ⊢
  rw [sep_comm (array64 h s.u64s), sep_assoc] at hm
  rw [hoff, ← BitVec.add_assoc]
  obtain ⟨hok, hm'⟩ :=
    store_array (t := i32) v (by decide) (by rw [bvHdrState_u32s_len]; exact hi) hm
  refine ⟨hok, ?_⟩
  rw [hs64, hs', sep_comm (array64 h s.u64s), sep_assoc]
  exact hm'

theorem load_hdr_work_base (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 h = some s.work_base := by
  have h0 := load_hdr_u64 0 (by decide) 0#64 rfl hm
  rwa [BitVec.add_zero] at h0

theorem load_hdr_work_end (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 8#64) = some s.work_end :=
  load_hdr_u64 1 (by decide) 8#64 rfl hm

theorem load_hdr_prog_ptr (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 16#64) = some s.prog_ptr :=
  load_hdr_u64 2 (by decide) 16#64 rfl hm

theorem load_hdr_aig_ptr (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 24#64) = some s.aig_ptr :=
  load_hdr_u64 3 (by decide) 24#64 rfl hm

theorem load_hdr_ht_ptr (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 32#64) = some s.ht_ptr :=
  load_hdr_u64 4 (by decide) 32#64 rfl hm

theorem load_hdr_atom_base_ptr (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 40#64) = some s.atom_base_ptr :=
  load_hdr_u64 5 (by decide) 40#64 rfl hm

theorem load_hdr_slice_off_ptr (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 48#64) = some s.slice_off_ptr :=
  load_hdr_u64 6 (by decide) 48#64 rfl hm

theorem load_hdr_lits_ptr (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 56#64) = some s.lits_ptr :=
  load_hdr_u64 7 (by decide) 56#64 rfl hm

theorem load_hdr_marks_ptr (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 64#64) = some s.marks_ptr :=
  load_hdr_u64 8 (by decide) 64#64 rfl hm

theorem load_hdr_dimacs_start (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 72#64) = some s.dimacs_start :=
  load_hdr_u64 9 (by decide) 72#64 rfl hm

theorem load_hdr_n_vars (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 80#64) = some s.n_vars :=
  load_hdr_u32 0 (by decide) 80#64 rfl hm

theorem load_hdr_n_nodes (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 84#64) = some s.n_nodes :=
  load_hdr_u32 1 (by decide) 84#64 rfl hm

theorem load_hdr_n_cwords (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 88#64) = some s.n_cwords :=
  load_hdr_u32 2 (by decide) 88#64 rfl hm

theorem load_hdr_root_node (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 92#64) = some s.root_node :=
  load_hdr_u32 3 (by decide) 92#64 rfl hm

theorem load_hdr_num_atoms (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 96#64) = some s.num_atoms :=
  load_hdr_u32 4 (by decide) 96#64 rfl hm

theorem load_hdr_aig_len (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 100#64) = some s.aig_len :=
  load_hdr_u32 5 (by decide) 100#64 rfl hm

theorem load_hdr_aig_cap (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 104#64) = some s.aig_cap :=
  load_hdr_u32 6 (by decide) 104#64 rfl hm

theorem load_hdr_ht_mask (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 108#64) = some s.ht_mask :=
  load_hdr_u32 7 (by decide) 108#64 rfl hm

theorem load_hdr_lits_len (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 112#64) = some s.lits_len :=
  load_hdr_u32 8 (by decide) 112#64 rfl hm

theorem load_hdr_lits_cap (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 116#64) = some s.lits_cap :=
  load_hdr_u32 9 (by decide) 116#64 rfl hm

theorem load_hdr_oom (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 120#64) = some s.oom :=
  load_hdr_u32 10 (by decide) 120#64 rfl hm

theorem load_hdr_dimacs_len (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 124#64) = some s.dimacs_len :=
  load_hdr_u32 11 (by decide) 124#64 rfl hm

theorem store_hdr_work_base (v : BitVec 64) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i64 h ∧
      (bvHdrMem h { s with work_base := v } ⋆ R) (storeMem m i64 h v) := by
  simpa [BitVec.add_zero] using
    store_hdr_u64 0 (by decide) 0#64 rfl v hm { s with work_base := v } rfl rfl

theorem store_hdr_work_end (v : BitVec 64) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i64 (h + 8#64) ∧
      (bvHdrMem h { s with work_end := v } ⋆ R) (storeMem m i64 (h + 8#64) v) :=
  store_hdr_u64 1 (by decide) 8#64 rfl v hm { s with work_end := v } rfl rfl

theorem store_hdr_prog_ptr (v : BitVec 64) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i64 (h + 16#64) ∧
      (bvHdrMem h { s with prog_ptr := v } ⋆ R) (storeMem m i64 (h + 16#64) v) :=
  store_hdr_u64 2 (by decide) 16#64 rfl v hm { s with prog_ptr := v } rfl rfl

theorem store_hdr_aig_ptr (v : BitVec 64) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i64 (h + 24#64) ∧
      (bvHdrMem h { s with aig_ptr := v } ⋆ R) (storeMem m i64 (h + 24#64) v) :=
  store_hdr_u64 3 (by decide) 24#64 rfl v hm { s with aig_ptr := v } rfl rfl

theorem store_hdr_ht_ptr (v : BitVec 64) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i64 (h + 32#64) ∧
      (bvHdrMem h { s with ht_ptr := v } ⋆ R) (storeMem m i64 (h + 32#64) v) :=
  store_hdr_u64 4 (by decide) 32#64 rfl v hm { s with ht_ptr := v } rfl rfl

theorem store_hdr_atom_base_ptr (v : BitVec 64) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i64 (h + 40#64) ∧
      (bvHdrMem h { s with atom_base_ptr := v } ⋆ R) (storeMem m i64 (h + 40#64) v) :=
  store_hdr_u64 5 (by decide) 40#64 rfl v hm { s with atom_base_ptr := v } rfl rfl

theorem store_hdr_slice_off_ptr (v : BitVec 64) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i64 (h + 48#64) ∧
      (bvHdrMem h { s with slice_off_ptr := v } ⋆ R) (storeMem m i64 (h + 48#64) v) :=
  store_hdr_u64 6 (by decide) 48#64 rfl v hm { s with slice_off_ptr := v } rfl rfl

theorem store_hdr_lits_ptr (v : BitVec 64) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i64 (h + 56#64) ∧
      (bvHdrMem h { s with lits_ptr := v } ⋆ R) (storeMem m i64 (h + 56#64) v) :=
  store_hdr_u64 7 (by decide) 56#64 rfl v hm { s with lits_ptr := v } rfl rfl

theorem store_hdr_marks_ptr (v : BitVec 64) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i64 (h + 64#64) ∧
      (bvHdrMem h { s with marks_ptr := v } ⋆ R) (storeMem m i64 (h + 64#64) v) :=
  store_hdr_u64 8 (by decide) 64#64 rfl v hm { s with marks_ptr := v } rfl rfl

theorem store_hdr_dimacs_start (v : BitVec 64) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i64 (h + 72#64) ∧
      (bvHdrMem h { s with dimacs_start := v } ⋆ R) (storeMem m i64 (h + 72#64) v) :=
  store_hdr_u64 9 (by decide) 72#64 rfl v hm { s with dimacs_start := v } rfl rfl

theorem store_hdr_n_vars (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 80#64) ∧
      (bvHdrMem h { s with n_vars := v } ⋆ R) (storeMem m i32 (h + 80#64) v) :=
  store_hdr_u32 0 (by decide) 80#64 rfl v hm { s with n_vars := v } rfl rfl

theorem store_hdr_n_nodes (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 84#64) ∧
      (bvHdrMem h { s with n_nodes := v } ⋆ R) (storeMem m i32 (h + 84#64) v) :=
  store_hdr_u32 1 (by decide) 84#64 rfl v hm { s with n_nodes := v } rfl rfl

theorem store_hdr_n_cwords (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 88#64) ∧
      (bvHdrMem h { s with n_cwords := v } ⋆ R) (storeMem m i32 (h + 88#64) v) :=
  store_hdr_u32 2 (by decide) 88#64 rfl v hm { s with n_cwords := v } rfl rfl

theorem store_hdr_root_node (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 92#64) ∧
      (bvHdrMem h { s with root_node := v } ⋆ R) (storeMem m i32 (h + 92#64) v) :=
  store_hdr_u32 3 (by decide) 92#64 rfl v hm { s with root_node := v } rfl rfl

theorem store_hdr_num_atoms (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 96#64) ∧
      (bvHdrMem h { s with num_atoms := v } ⋆ R) (storeMem m i32 (h + 96#64) v) :=
  store_hdr_u32 4 (by decide) 96#64 rfl v hm { s with num_atoms := v } rfl rfl

theorem store_hdr_aig_len (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 100#64) ∧
      (bvHdrMem h { s with aig_len := v } ⋆ R) (storeMem m i32 (h + 100#64) v) :=
  store_hdr_u32 5 (by decide) 100#64 rfl v hm { s with aig_len := v } rfl rfl

theorem store_hdr_aig_cap (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 104#64) ∧
      (bvHdrMem h { s with aig_cap := v } ⋆ R) (storeMem m i32 (h + 104#64) v) :=
  store_hdr_u32 6 (by decide) 104#64 rfl v hm { s with aig_cap := v } rfl rfl

theorem store_hdr_ht_mask (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 108#64) ∧
      (bvHdrMem h { s with ht_mask := v } ⋆ R) (storeMem m i32 (h + 108#64) v) :=
  store_hdr_u32 7 (by decide) 108#64 rfl v hm { s with ht_mask := v } rfl rfl

theorem store_hdr_lits_len (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 112#64) ∧
      (bvHdrMem h { s with lits_len := v } ⋆ R) (storeMem m i32 (h + 112#64) v) :=
  store_hdr_u32 8 (by decide) 112#64 rfl v hm { s with lits_len := v } rfl rfl

theorem store_hdr_lits_cap (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 116#64) ∧
      (bvHdrMem h { s with lits_cap := v } ⋆ R) (storeMem m i32 (h + 116#64) v) :=
  store_hdr_u32 9 (by decide) 116#64 rfl v hm { s with lits_cap := v } rfl rfl

theorem store_hdr_oom (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 120#64) ∧
      (bvHdrMem h { s with oom := v } ⋆ R) (storeMem m i32 (h + 120#64) v) :=
  store_hdr_u32 10 (by decide) 120#64 rfl v hm { s with oom := v } rfl rfl

theorem store_hdr_dimacs_len (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 124#64) ∧
      (bvHdrMem h { s with dimacs_len := v } ⋆ R) (storeMem m i32 (h + 124#64) v) :=
  store_hdr_u32 11 (by decide) 124#64 rfl v hm { s with dimacs_len := v } rfl rfl

end HdrLoadStore

/-! ## 3. Workspace Phase Transitions and Kissat Handoff -/

private theorem region_merge_add {a : BitVec 64} {n1 n2 : Nat} (hfit : n1 + n2 ≤ 2 ^ 64) :
    (region a n1 ⋆ region (a + BitVec.ofNat 64 n1) n2) = region a (n1 + n2) :=
  region_merge_eq rfl hfit

private theorem bv_ofNat_add_eq (a : BitVec 64) (x y : Nat) :
    a + BitVec.ofNat 64 x + BitVec.ofNat 64 y = a + BitVec.ofNat 64 (x + y) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem bv_ofNat_128_add_eq (a : BitVec 64) (y : Nat) :
    a + 128 + BitVec.ofNat 64 y = a + BitVec.ofNat 64 (128 + y) :=
  bv_ofNat_add_eq a 128 y

private theorem bv_add_sub_toNat {a b : BitVec 64} {n : Nat}
    (hb : b = a + BitVec.ofNat 64 n) (hn : a.toNat + n < 2 ^ 64) :
    a + BitVec.ofNat 64 (b.toNat - a.toNat) = b := by
  apply BitVec.eq_of_toNat_eq
  have hbt : b.toNat = a.toNat + n := by
    rw [hb, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [hbt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- Collapse the entire `bvBlastMem` workspace back into `region cfg.work_base cfg.avail`
(used on early exit / trivial UNSAT / trivial SAT / OOM). -/
private theorem sep_lift_l {P P' Q : Mem 64 → Prop} (h : ∀ f, P f → P' f) :
    ∀ f, (P ⋆ Q) f → (P' ⋆ Q) f :=
  fun _ => sep_mono h

private theorem sep_lift_r {P Q Q' : Mem 64 → Prop} (h : ∀ f, Q f → Q' f) :
    ∀ f, (P ⋆ Q) f → (P ⋆ Q') f :=
  fun _ => sep_mono_r h

theorem bvBlastMem_to_region {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {m : Mem 64}
    (hok : BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool)
    (hm : bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool m) :
    region cfg.work_base cfg.avail m := by
  have hfit := hok.fit
  have htot := hok.total_eq
  have hab := hok.ab_len
  have hso := hok.so_len
  have haig := hok.aig_len_eq
  have hht := hok.ht_len
  have hlits := hok.lits_len
  have hnv := hok.nv_lt
  have hnn := hok.nn_lt
  have hacap := hok.acap_lt
  have hht_lt := hok.ht_lt
  have hlcap := hok.lcap_lt
  have hlfit := hok.lits_fit
  have haal := hok.atom_align
  have hsal := hok.slice_align
  have hwb_lt : cfg.work_base.toNat < 2 ^ 64 := cfg.work_base.isLt
  have f0 : ∀ f, bvHdrMem cfg.work_base hdr f → region cfg.work_base 128 f :=
    fun _ => bvHdrMem_to_region
  have f1 : ∀ f, array (t := i32) (cfg.work_base + 128) atomBases f →
      region (cfg.work_base + 128) (4 * cfg.n_vars) f := fun _ h => by
    have hr := array_to_region (t := i32) (a := cfg.work_base + 128) (xs := atomBases)
      (by simp [Ty.bytes, Ty.size, hab]; omega) h
    simpa [Ty.bytes, Ty.size, hab] using hr
  have f2 : ∀ f,
      array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) sliceOffs f →
      region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) (4 * cfg.n_nodes) f :=
    fun _ h => by
      have hr := array_to_region (t := i32)
        (a := cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) (xs := sliceOffs)
        (by simp [Ty.bytes, Ty.size, hso]; omega) h
      simpa [Ty.bytes, Ty.size, hso] using hr
  have f3 : ∀ f, array64 cfg.aig_ptr aigWords f → region cfg.aig_ptr (8 * cfg.aig_cap) f :=
    fun _ h => by
      have hr := array64_to_region (a := cfg.aig_ptr) (xs := aigWords) (by rw [haig]; omega) h
      simpa [haig] using hr
  have f4 : ∀ f, array (t := i32) cfg.ht_ptr htSlots f → region cfg.ht_ptr (4 * cfg.ht_slots) f :=
    fun _ h => by
      have hr := array_to_region (t := i32) (a := cfg.ht_ptr) (xs := htSlots)
        (by simp [Ty.bytes, Ty.size, hht]; omega) h
      simpa [Ty.bytes, Ty.size, hht] using hr
  have f5 : ∀ f, array (t := i32) cfg.lits_ptr litsPool f →
      region cfg.lits_ptr (4 * cfg.lits_cap) f :=
    fun _ h => by
      have hr := array_to_region (t := i32) (a := cfg.lits_ptr) (xs := litsPool)
        (by simp [Ty.bytes, Ty.size, hlits]; omega) h
      simpa [Ty.bytes, Ty.size, hlits] using hr
  have h1 : (region cfg.work_base 128 ⋆
      region (cfg.work_base + 128) (4 * cfg.n_vars) ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
        (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) (4 * cfg.n_nodes) ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
        (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
      region cfg.aig_ptr (8 * cfg.aig_cap) ⋆
      region cfg.ht_ptr (4 * cfg.ht_slots) ⋆
      region cfg.lits_ptr (4 * cfg.lits_cap) ⋆
      region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
        (cfg.lits_bytes - 4 * cfg.lits_cap)) m := by
    unfold bvBlastMem at hm
    exact sep_lift_l (sep_mono2 (sep_mono2 (sep_mono2 (sep_lift_l (sep_mono2
      (sep_lift_l (sep_mono2 f0 f1)) f2)) f3) f4) f5) m hm
  have hm_lits : (region cfg.lits_ptr (4 * cfg.lits_cap) ⋆
      region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
        (cfg.lits_bytes - 4 * cfg.lits_cap)) =
      region cfg.lits_ptr cfg.lits_bytes :=
    region_merge_eq (n := cfg.lits_bytes) (by omega) (by omega)
  have hm_hl : (region cfg.ht_ptr (4 * cfg.ht_slots) ⋆ region cfg.lits_ptr cfg.lits_bytes) =
      region cfg.ht_ptr (4 * cfg.ht_slots + cfg.lits_bytes) := by
    rw [hok.lits_ptr_eq, region_merge_add (by omega)]
  have hm_ahl : (region cfg.aig_ptr (8 * cfg.aig_cap) ⋆
      region cfg.ht_ptr (4 * cfg.ht_slots + cfg.lits_bytes)) =
      region cfg.aig_ptr (8 * cfg.aig_cap + (4 * cfg.ht_slots + cfg.lits_bytes)) := by
    rw [hok.ht_ptr_eq, region_merge_add (by omega)]
  have hm_atom : (region (cfg.work_base + 128) (4 * cfg.n_vars) ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
        (cfg.atom_bytes - 4 * cfg.n_vars)) =
      region (cfg.work_base + 128) cfg.atom_bytes := by
    rw [← bv_ofNat_128_add_eq cfg.work_base (4 * cfg.n_vars),
      region_merge_eq (n := cfg.atom_bytes) (by omega) (by omega)]
  have hm_slice : (region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes))
        (4 * cfg.n_nodes) ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
        (cfg.slice_bytes - 4 * cfg.n_nodes)) =
      region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) cfg.slice_bytes := by
    rw [← bv_ofNat_add_eq cfg.work_base (128 + cfg.atom_bytes) (4 * cfg.n_nodes),
      region_merge_eq (n := cfg.slice_bytes) (by omega) (by omega)]
  have hm_sa : (region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) cfg.slice_bytes ⋆
      region cfg.aig_ptr (8 * cfg.aig_cap + (4 * cfg.ht_slots + cfg.lits_bytes))) =
      region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes))
        (cfg.slice_bytes + (8 * cfg.aig_cap + (4 * cfg.ht_slots + cfg.lits_bytes))) := by
    rw [hok.aig_ptr_eq, ← bv_ofNat_add_eq cfg.work_base (128 + cfg.atom_bytes) cfg.slice_bytes,
      region_merge_add (by omega)]
  let tail := cfg.slice_bytes + (8 * cfg.aig_cap + (4 * cfg.ht_slots + cfg.lits_bytes))
  have hm_asa : (region (cfg.work_base + 128) cfg.atom_bytes ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) tail) =
      region (cfg.work_base + 128) (cfg.atom_bytes + tail) := by
    rw [← bv_ofNat_128_add_eq cfg.work_base cfg.atom_bytes, region_merge_add (by omega)]
  have hm_all : (region cfg.work_base 128 ⋆
      region (cfg.work_base + 128) (cfg.atom_bytes + tail)) =
      region cfg.work_base cfg.avail :=
    region_merge_eq (n := cfg.avail) (by omega) (by omega)
  have h1' : (region cfg.work_base 128 ⋆
      ((region (cfg.work_base + 128) (4 * cfg.n_vars) ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
          (cfg.atom_bytes - 4 * cfg.n_vars)) ⋆
       ((region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) (4 * cfg.n_nodes) ⋆
         region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
           (cfg.slice_bytes - 4 * cfg.n_nodes)) ⋆
        (region cfg.aig_ptr (8 * cfg.aig_cap) ⋆
         (region cfg.ht_ptr (4 * cfg.ht_slots) ⋆
          (region cfg.lits_ptr (4 * cfg.lits_cap) ⋆
           region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
             (cfg.lits_bytes - 4 * cfg.lits_cap))))))) m := sep_ac h1
  rw [hm_lits, hm_hl, hm_ahl, hm_slice, hm_sa, hm_atom, hm_asa, hm_all] at h1'
  exact h1'

/-- Transition from bitblasting workspace `bvBlastMem` to COI/DIMACS workspace `bvCoiMem`,
preserving `aigUsed := aigWords.take aigLen`, splitting off `[marks_ptr, marks_ptr + aigLen)` for
COI marking (when `marks_ptr + aigLen ≤ work_end`), and keeping the remaining space as a region. -/
theorem bvBlastMem_to_coiMem {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {aigLen : Nat} {m : Mem 64}
    (hok : BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool)
    (hlen : aigLen ≤ cfg.aig_cap)
    (hm_fit : 128 + cfg.atom_bytes + cfg.slice_bytes + 8 * aigLen + aigLen ≤ cfg.avail)
    (hm : bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool m) :
    ∃ marks0 : List UInt8, marks0.length = aigLen ∧
      bvCoiMem cfg.work_base cfg.aig_ptr (cfg.aig_ptr + BitVec.ofNat 64 (8 * aigLen))
        cfg.avail hdr (aigWords.take aigLen) marks0 m := by
  have hfit := hok.fit
  have htot := hok.total_eq
  have haig_len := hok.aig_len_eq
  have hnv := hok.nv_lt
  have hnn := hok.nn_lt
  have hacap := hok.acap_lt
  have hht_lt := hok.ht_lt
  have hlcap := hok.lcap_lt
  have hlfit := hok.lits_fit
  have haal := hok.atom_align
  have hsal := hok.slice_align
  have hwb_lt : cfg.work_base.toNat < 2 ^ 64 := cfg.work_base.isLt
  have haig_toNat :
      cfg.aig_ptr.toNat = cfg.work_base.toNat + 128 + cfg.atom_bytes + cfg.slice_bytes := by
    rw [hok.aig_ptr_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  let marksPtr := cfg.aig_ptr + BitVec.ofNat 64 (8 * aigLen)
  have hmptr_toNat : marksPtr.toNat = cfg.aig_ptr.toNat + 8 * aigLen := by
    dsimp only [marksPtr]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have haig_sp : array64 cfg.aig_ptr aigWords =
      (array64 cfg.aig_ptr (aigWords.take aigLen) ⋆
        array64 marksPtr (aigWords.drop aigLen)) := by
    conv => lhs; rw [← List.take_append_drop aigLen aigWords]
    rw [array64_append, List.length_take_of_le (by omega)]
  unfold bvBlastMem at hm
  rw [haig_sp] at hm
  have f1 : ∀ f, array (t := i32) (cfg.work_base + 128) atomBases f →
      region (cfg.work_base + 128) (4 * cfg.n_vars) f := fun _ h => by
    have hr := array_to_region (t := i32) (a := cfg.work_base + 128) (xs := atomBases)
      (by simp [Ty.bytes, Ty.size, hok.ab_len]; omega) h
    simpa [Ty.bytes, Ty.size, hok.ab_len] using hr
  have f2 : ∀ f,
      array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) sliceOffs f →
      region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) (4 * cfg.n_nodes) f :=
    fun _ h => by
      have hr := array_to_region (t := i32)
        (a := cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) (xs := sliceOffs)
        (by simp [Ty.bytes, Ty.size, hok.so_len]; omega) h
      simpa [Ty.bytes, Ty.size, hok.so_len] using hr
  have f3 : ∀ f, array64 marksPtr (aigWords.drop aigLen) f →
      region marksPtr (8 * (cfg.aig_cap - aigLen)) f := fun _ h => by
    have hdl : (aigWords.drop aigLen).length = cfg.aig_cap - aigLen := by simp [haig_len]
    have hr := array64_to_region (a := marksPtr) (xs := aigWords.drop aigLen) (by rw [hdl]; omega) h
    simpa [hdl] using hr
  have f4 : ∀ f, array (t := i32) cfg.ht_ptr htSlots f → region cfg.ht_ptr (4 * cfg.ht_slots) f :=
    fun _ h => by
      have hr := array_to_region (t := i32) (a := cfg.ht_ptr) (xs := htSlots)
        (by simp [Ty.bytes, Ty.size, hok.ht_len]; omega) h
      simpa [Ty.bytes, Ty.size, hok.ht_len] using hr
  have f5 : ∀ f, array (t := i32) cfg.lits_ptr litsPool f →
      region cfg.lits_ptr (4 * cfg.lits_cap) f :=
    fun _ h => by
      have hr := array_to_region (t := i32) (a := cfg.lits_ptr) (xs := litsPool)
        (by simp [Ty.bytes, Ty.size, hok.lits_len]; omega) h
      simpa [Ty.bytes, Ty.size, hok.lits_len] using hr
  have h2 : (bvHdrMem cfg.work_base hdr ⋆
      region (cfg.work_base + 128) (4 * cfg.n_vars) ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
        (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) (4 * cfg.n_nodes) ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
        (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
      (array64 cfg.aig_ptr (aigWords.take aigLen) ⋆
        region marksPtr (8 * (cfg.aig_cap - aigLen))) ⋆
      region cfg.ht_ptr (4 * cfg.ht_slots) ⋆
      region cfg.lits_ptr (4 * cfg.lits_cap) ⋆
      region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
        (cfg.lits_bytes - 4 * cfg.lits_cap)) m :=
    sep_lift_l (sep_mono2 (sep_mono2 (sep_mono2
      (sep_lift_l (sep_mono2 (sep_lift_l (sep_lift_r f1)) f2)) (sep_lift_r f3)) f4) f5) m hm
  have hm_atom : (region (cfg.work_base + 128) (4 * cfg.n_vars) ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
        (cfg.atom_bytes - 4 * cfg.n_vars)) =
      region (cfg.work_base + 128) cfg.atom_bytes := by
    rw [← bv_ofNat_128_add_eq cfg.work_base (4 * cfg.n_vars),
      region_merge_eq (n := cfg.atom_bytes) (by omega) (by omega)]
  have hm_slice : (region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes))
        (4 * cfg.n_nodes) ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
        (cfg.slice_bytes - 4 * cfg.n_nodes)) =
      region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) cfg.slice_bytes := by
    rw [← bv_ofNat_add_eq cfg.work_base (128 + cfg.atom_bytes) (4 * cfg.n_nodes),
      region_merge_eq (n := cfg.slice_bytes) (by omega) (by omega)]
  have hm_pre : (region (cfg.work_base + 128) cfg.atom_bytes ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) cfg.slice_bytes) =
      region (cfg.work_base + 128) (cfg.atom_bytes + cfg.slice_bytes) := by
    rw [← bv_ofNat_128_add_eq cfg.work_base cfg.atom_bytes, region_merge_add (by omega)]
  have hm_lits : (region cfg.lits_ptr (4 * cfg.lits_cap) ⋆
      region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
        (cfg.lits_bytes - 4 * cfg.lits_cap)) =
      region cfg.lits_ptr cfg.lits_bytes :=
    region_merge_eq (n := cfg.lits_bytes) (by omega) (by omega)
  have hm_hl : (region cfg.ht_ptr (4 * cfg.ht_slots) ⋆ region cfg.lits_ptr cfg.lits_bytes) =
      region cfg.ht_ptr (4 * cfg.ht_slots + cfg.lits_bytes) := by
    rw [hok.lits_ptr_eq, region_merge_add (by omega)]
  have hm_tail : (region marksPtr (8 * (cfg.aig_cap - aigLen)) ⋆
      region cfg.ht_ptr (4 * cfg.ht_slots + cfg.lits_bytes)) =
      region marksPtr (cfg.avail - (128 + cfg.atom_bytes + cfg.slice_bytes + 8 * aigLen)) := by
    rw [hok.ht_ptr_eq,
      show cfg.aig_ptr + BitVec.ofNat 64 (8 * cfg.aig_cap) =
        marksPtr + BitVec.ofNat 64 (8 * (cfg.aig_cap - aigLen)) from by
        dsimp only [marksPtr]
        rw [bv_ofNat_add_eq]; congr 1; apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ofNat]; omega]
    exact region_merge_eq (n := cfg.avail - (128 + cfg.atom_bytes + cfg.slice_bytes + 8 * aigLen))
      (by omega) (by omega)
  have hrem_split :
      region marksPtr (cfg.avail - (128 + cfg.atom_bytes + cfg.slice_bytes + 8 * aigLen)) =
      (region marksPtr aigLen ⋆
        region (marksPtr + BitVec.ofNat 64 aigLen)
          (cfg.work_base.toNat + cfg.avail - (marksPtr.toNat + aigLen))) :=
    (region_merge_eq (n1 := aigLen)
      (n2 := cfg.work_base.toNat + cfg.avail - (marksPtr.toNat + aigLen))
      (n := cfg.avail - (128 + cfg.atom_bytes + cfg.slice_bytes + 8 * aigLen))
      (by omega) (by omega)).symm
  have h2' : (bvHdrMem cfg.work_base hdr ⋆
      ((region (cfg.work_base + 128) (4 * cfg.n_vars) ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
          (cfg.atom_bytes - 4 * cfg.n_vars)) ⋆
       (region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) (4 * cfg.n_nodes) ⋆
        region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
          (cfg.slice_bytes - 4 * cfg.n_nodes))) ⋆
      array64 cfg.aig_ptr (aigWords.take aigLen) ⋆
      (region marksPtr (8 * (cfg.aig_cap - aigLen)) ⋆
        (region cfg.ht_ptr (4 * cfg.ht_slots) ⋆
          (region cfg.lits_ptr (4 * cfg.lits_cap) ⋆
            region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
              (cfg.lits_bytes - 4 * cfg.lits_cap))))) m := sep_ac h2
  rw [hm_atom, hm_slice, hm_pre, hm_lits, hm_hl, hm_tail, hrem_split] at h2'
  have h2'' : ((bvHdrMem cfg.work_base hdr ⋆
      region (cfg.work_base + 128) (cfg.aig_ptr.toNat - (cfg.work_base.toNat + 128)) ⋆
      array64 cfg.aig_ptr (aigWords.take aigLen) ⋆
      region (marksPtr + BitVec.ofNat 64 aigLen)
        (cfg.work_base.toNat + cfg.avail - (marksPtr.toNat + aigLen))) ⋆
      region marksPtr aigLen) m := by
    rw [show cfg.aig_ptr.toNat - (cfg.work_base.toNat + 128) = cfg.atom_bytes + cfg.slice_bytes by
      omega]
    exact sep_ac h2'
  have h3 := sep_mono_r (fun _ hr => region_to_bytes hr) h2''
  obtain ⟨marks0, h4⟩ := sep_ex_r.mp h3
  obtain ⟨hm_eq, hm_mem⟩ := sep_pure_r.mp h4
  refine ⟨marks0, hm_eq, ?_⟩
  unfold bvCoiMem
  dsimp only [marksPtr] at hm_mem
  rw [hm_eq]
  exact sep_ac hm_mem

/-- Collapse all non-DIMACS workspace slices (`BVHdr`, prefix, `aig`, `marks`, and free gap)
into `region work_base (dimacs_start - work_base)` for the `kissat_solve_bytes` handoff. -/
theorem bvCoiMem_to_kissatHandoff {work_base aig_ptr marks_ptr dimacs_start : BitVec 64}
    {avail : Nat} {hdr : BVHdrState} {aigUsed : List (BitVec 64)} {marks dimacsBytes : List UInt8}
    {m : Mem 64}
    (hfit : work_base.toNat + avail < 2 ^ 64)
    (haig : work_base.toNat + 128 ≤ aig_ptr.toNat)
    (haig_eq : marks_ptr = aig_ptr + BitVec.ofNat 64 (8 * aigUsed.length))
    (haig_ub : aig_ptr.toNat + 8 * aigUsed.length ≤ work_base.toNat + avail)
    (hmarks_ub : marks_ptr.toNat + marks.length ≤ dimacs_start.toNat)
    (hdend : dimacs_start.toNat + dimacsBytes.length = work_base.toNat + avail)
    (hm : (bvHdrMem work_base hdr ⋆
      region (work_base + 128) (aig_ptr.toNat - (work_base.toNat + 128)) ⋆
      array64 aig_ptr aigUsed ⋆
      bytes marks_ptr marks ⋆
      region (marks_ptr + BitVec.ofNat 64 marks.length)
        (dimacs_start.toNat - (marks_ptr.toNat + marks.length)) ⋆
      bytes dimacs_start dimacsBytes) m) :
    bvDimacsMem work_base dimacs_start avail dimacsBytes m := by
  have hwb_lt : work_base.toNat < 2 ^ 64 := work_base.isLt
  have haig_lt : aig_ptr.toNat < 2 ^ 64 := aig_ptr.isLt
  have hds_lt : dimacs_start.toNat < 2 ^ 64 := dimacs_start.isLt
  have hmptr : marks_ptr.toNat = aig_ptr.toNat + 8 * aigUsed.length := by
    rw [haig_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have g0 : ∀ f, bvHdrMem work_base hdr f → region work_base 128 f := fun _ => bvHdrMem_to_region
  have g1 : ∀ f, array64 aig_ptr aigUsed f → region aig_ptr (8 * aigUsed.length) f :=
    fun _ h => array64_to_region (by omega) h
  have g2 : ∀ f, bytes marks_ptr marks f → region marks_ptr marks.length f :=
    fun _ h => bytes_to_region h
  have h1 : (region work_base 128 ⋆
      region (work_base + 128) (aig_ptr.toNat - (work_base.toNat + 128)) ⋆
      region aig_ptr (8 * aigUsed.length) ⋆
      region marks_ptr marks.length ⋆
      region (marks_ptr + BitVec.ofNat 64 marks.length)
        (dimacs_start.toNat - (marks_ptr.toNat + marks.length)) ⋆
      bytes dimacs_start dimacsBytes) m :=
    sep_lift_l (sep_lift_l (sep_mono2 (sep_mono2 (sep_lift_l g0) g1) g2)) m hm
  have hm_gap : (region marks_ptr marks.length ⋆
      region (marks_ptr + BitVec.ofNat 64 marks.length)
        (dimacs_start.toNat - (marks_ptr.toNat + marks.length))) =
      region marks_ptr (dimacs_start.toNat - marks_ptr.toNat) :=
    region_merge_eq (n := dimacs_start.toNat - marks_ptr.toNat) (by omega) (by omega)
  have hm_aig : (region aig_ptr (8 * aigUsed.length) ⋆
      region marks_ptr (dimacs_start.toNat - marks_ptr.toNat)) =
      region aig_ptr (dimacs_start.toNat - aig_ptr.toNat) := by
    have hmerge := region_merge_eq (a := aig_ptr) (n1 := 8 * aigUsed.length)
      (n2 := dimacs_start.toNat - marks_ptr.toNat) (n := dimacs_start.toNat - aig_ptr.toNat)
      (by omega) (by omega)
    rw [← haig_eq] at hmerge
    exact hmerge
  have hm_pre : (region (work_base + 128) (aig_ptr.toNat - (work_base.toNat + 128)) ⋆
      region aig_ptr (dimacs_start.toNat - aig_ptr.toNat)) =
      region (work_base + 128) (dimacs_start.toNat - (work_base.toNat + 128)) := by
    have h128 : (128 : BitVec 64).toNat = 128 := rfl
    have hadd_toNat : (work_base + 128).toNat = work_base.toNat + 128 := by
      rw [BitVec.toNat_add, h128, Nat.mod_eq_of_lt (by omega)]
    have haig_bv : (work_base + 128) + BitVec.ofNat 64 (aig_ptr.toNat - (work_base.toNat + 128)) =
        aig_ptr := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, hadd_toNat, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    have hmerge := region_merge_eq (a := work_base + 128)
      (n1 := aig_ptr.toNat - (work_base.toNat + 128))
      (n2 := dimacs_start.toNat - aig_ptr.toNat)
      (n := dimacs_start.toNat - (work_base.toNat + 128))
      (by omega) (by omega)
    rw [haig_bv] at hmerge
    exact hmerge
  have hm_hdr : (region work_base 128 ⋆
      region (work_base + 128) (dimacs_start.toNat - (work_base.toNat + 128))) =
      region work_base (dimacs_start.toNat - work_base.toNat) :=
    region_merge_eq (n := dimacs_start.toNat - work_base.toNat) (by omega) (by omega)
  have h1' : (region work_base 128 ⋆
      (region (work_base + 128) (aig_ptr.toNat - (work_base.toNat + 128)) ⋆
        (region aig_ptr (8 * aigUsed.length) ⋆
          (region marks_ptr marks.length ⋆
            region (marks_ptr + BitVec.ofNat 64 marks.length)
              (dimacs_start.toNat - (marks_ptr.toNat + marks.length))))) ⋆
      bytes dimacs_start dimacsBytes) m := sep_ac h1
  rw [hm_gap, hm_aig, hm_pre] at h1'
  have h1'' : ((region work_base 128 ⋆
      region (work_base + 128) (dimacs_start.toNat - (work_base.toNat + 128))) ⋆
      bytes dimacs_start dimacsBytes) m := sep_ac h1'
  rw [hm_hdr] at h1''
  exact h1''

/-- Collapse `bvDimacsMem` (`region work_base kcap ⋆ bytes dimacs_start dimacsBytes`) back into
`region work_base avail` after `kissat_solve_bytes` returns. -/
theorem bvDimacsMem_to_region {work_base dimacs_start : BitVec 64} {avail : Nat}
    {dimacsBytes : List UInt8} {m : Mem 64}
    (hfit : work_base.toNat + avail < 2 ^ 64)
    (hle : work_base.toNat ≤ dimacs_start.toNat)
    (hdend : dimacs_start.toNat + dimacsBytes.length = work_base.toNat + avail)
    (hm : bvDimacsMem work_base dimacs_start avail dimacsBytes m) :
    region work_base avail m := by
  unfold bvDimacsMem at hm
  have hwb_lt : work_base.toNat < 2 ^ 64 := work_base.isLt
  have hds_lt : dimacs_start.toNat < 2 ^ 64 := dimacs_start.isLt
  have h1 : (region work_base (dimacs_start.toNat - work_base.toNat) ⋆
      region dimacs_start dimacsBytes.length) m :=
    sep_mono_r (fun _ => bytes_to_region) hm
  have hds : work_base + BitVec.ofNat 64 (dimacs_start.toNat - work_base.toNat) = dimacs_start := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have hm_eq := region_merge_eq (a := work_base)
    (n1 := dimacs_start.toNat - work_base.toNat) (n2 := dimacsBytes.length) (n := avail)
    (by omega) (by omega)
  rw [hds] at hm_eq
  exact (congrFun hm_eq m).mp h1

/-- Split `region work_ptr wlen` into leading 8-byte alignment pad + `region work_base avail`. -/
theorem region_work_split_pad {work_ptr : BitVec 64} {wlen : Nat} {m : Mem 64}
    (pad : Nat) (hpad : pad ≤ wlen) (hfit : wlen ≤ 2 ^ 64)
    (hm : region work_ptr wlen m) :
    (region work_ptr pad ⋆ region (work_ptr + BitVec.ofNat 64 pad) (wlen - pad)) m :=
  (congrFun (region_merge_eq (a := work_ptr) (n1 := pad) (n2 := wlen - pad) (n := wlen)
    (by omega) hfit) m).mpr hm

/-- Merge leading 8-byte alignment pad + `region work_base avail` into `region work_ptr wlen`. -/
theorem region_work_merge_pad {work_ptr : BitVec 64} {wlen : Nat} {m : Mem 64}
    (pad : Nat) (hpad : pad ≤ wlen) (hfit : wlen ≤ 2 ^ 64)
    (hm : (region work_ptr pad ⋆ region (work_ptr + BitVec.ofNat 64 pad) (wlen - pad)) m) :
    region work_ptr wlen m :=
  (congrFun (region_merge_eq (a := work_ptr) (n1 := pad) (n2 := wlen - pad) (n := wlen)
    (by omega) hfit) m).mp hm

/-! ## 4. Packed AIG Gate Lemmas and Extra Handoff Helpers -/

theorem packAigGate_lo (lhs rhs : UInt32) :
    ((packAigGate lhs rhs) &&& 0xFFFFFFFF#64).setWidth 32 = lhs.toBitVec := by
  unfold packAigGate
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and, (by omega : i < 64)]
  have hmask : (0xFFFFFFFF#64).getLsbD i = true := by
    rw [BitVec.getLsbD_eq_getElem (by omega), BitVec.getElem_eq_testBit_toNat]
    rw [show (0xFFFFFFFF#64).toNat = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hi
  simp [hmask]

theorem packAigGate_hi (lhs rhs : UInt32) :
    (packAigGate lhs rhs >>> 32).setWidth 32 = rhs.toBitVec := by
  unfold packAigGate
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hnot : ¬ (32 + i < 32) := by omega
  have hlt64 : 32 + i < 64 := by omega
  simp [BitVec.getLsbD_ushiftRight, hi, hnot, hlt64]

theorem packAigGate_inj {l1 r1 l2 r2 : UInt32}
    (h : packAigGate l1 r1 = packAigGate l2 r2) : l1 = l2 ∧ r1 = r2 := by
  have hl : l1.toBitVec = l2.toBitVec := by
    rw [← packAigGate_lo l1 r1, ← packAigGate_lo l2 r2, h]
  have hr : r1.toBitVec = r2.toBitVec := by
    rw [← packAigGate_hi l1 r1, ← packAigGate_hi l2 r2, h]
  exact ⟨congrArg UInt32.ofBitVec hl, congrArg UInt32.ofBitVec hr⟩

/-- Store a `u64` at the start of `region a n ⋆ R` when `8 ≤ n`, preserving `region a n ⋆ R`. -/
theorem store_region_u64_head {a v : BitVec 64} {n : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hn : 8 ≤ n) (hfit : n ≤ 2 ^ 64) (hm : (region a n ⋆ R) m) :
    storeOk m i64 a ∧ (region a n ⋆ R) (storeMem m i64 a v) := by
  have hsp : (region a 8 ⋆ region (a + 8#64) (n - 8) ⋆ R) m := by
    have heq := (region_merge_eq (a := a) (n1 := 8) (n2 := n - 8) (n := n)
      (by omega) hfit).symm
    rw [heq] at hm
    exact hm
  have h64 := sep_mono (sep_lift_l (fun _ h => region_to_array64 1 (by decide) h)) hsp
  have h64' : ((fun f => ∃ xs : List (BitVec 64), xs.length = 1 ∧ array64 a xs f) ⋆
      (region (a + 8#64) (n - 8) ⋆ R)) m := sep_ac h64
  obtain ⟨xs, hxs⟩ := sep_ex_l.mp h64'
  obtain ⟨hlen, harr⟩ := sep_pure_l.mp hxs
  obtain ⟨hok, hst⟩ := store_array64 (i := 0) v (by omega) harr
  rw [show a + BitVec.ofNat 64 (8 * 0) = a from by simp] at hok hst
  refine ⟨hok, ?_⟩
  have hr8 : (region a 8 ⋆ (region (a + 8#64) (n - 8) ⋆ R)) (storeMem m i64 a v) :=
    sep_mono (fun _ h => by
      have hr := array64_to_region (by simp [hlen]) h
      simpa [hlen] using hr) hst
  have hr8' : ((region a 8 ⋆ region (a + 8#64) (n - 8)) ⋆ R) (storeMem m i64 a v) := sep_ac hr8
  rw [region_merge_eq (a := a) (n1 := 8) (n2 := n - 8) (n := n) (by omega) hfit] at hr8'
  exact hr8'

/-- Collapse `bvHdrMem work_base hdr ⋆ region (work_base + 128) (avail - 128)` into
`region work_base avail`. -/
theorem bvHdrRegion_to_region {work_base : BitVec 64} {avail : Nat} {hdr : BVHdrState}
    {m : Mem 64} (hle : 128 ≤ avail) (hfit : avail ≤ 2 ^ 64)
    (hm : (bvHdrMem work_base hdr ⋆ region (work_base + 128) (avail - 128)) m) :
    region work_base avail m := by
  have h1 : (region work_base 128 ⋆ region (work_base + 128) (avail - 128)) m :=
    sep_mono (fun _ => bvHdrMem_to_region) hm
  exact (congrFun (region_merge_eq (a := work_base) (n1 := 128) (n2 := avail - 128) (n := avail)
    (by omega) hfit) m).mp h1

/-- Collapse `bvHdrMem work_base hdr ⋆ region (work_base + 128) (dstart - (work_base + 128)) ⋆
bytes dstart dimacsBytes` into `bvDimacsMem work_base dstart avail dimacsBytes`. -/
theorem bvHdrDimacs_to_dimacsMem {work_base dstart : BitVec 64} {avail : Nat} {hdr : BVHdrState}
    {dimacsBytes : List UInt8} {m : Mem 64}
    (h128 : work_base.toNat + 128 ≤ dstart.toNat)
    (hm : (bvHdrMem work_base hdr ⋆
      region (work_base + 128) (dstart.toNat - (work_base.toNat + 128)) ⋆
      bytes dstart dimacsBytes) m) :
    bvDimacsMem work_base dstart avail dimacsBytes m := by
  have hds_lt : dstart.toNat < 2 ^ 64 := dstart.isLt
  have h1 : ((region work_base 128 ⋆
      region (work_base + 128#64) (dstart.toNat - (work_base.toNat + 128))) ⋆
      bytes dstart dimacsBytes) m :=
    sep_mono (sep_lift_l (fun _ => bvHdrMem_to_region)) hm
  rw [region_merge_eq (a := work_base) (n1 := 128)
    (n2 := dstart.toNat - (work_base.toNat + 128))
    (n := dstart.toNat - work_base.toNat) (by omega) (by omega)] at h1
  exact h1

/-- Collapse `bvCoiMem` into `bvHdrMem work_base hdr ⋆ region (work_base + 128) (avail - 128)`
(used when `bv_dimacs_write` returns `false` or takes the `root == 0` path). -/
theorem bvCoiMem_to_hdrRegion {work_base aig_ptr marks_ptr : BitVec 64} {avail : Nat}
    {hdr : BVHdrState} {aigUsed : List (BitVec 64)} {marks : List UInt8} {m : Mem 64}
    (hfit : work_base.toNat + avail < 2 ^ 64)
    (haig : work_base.toNat + 128 ≤ aig_ptr.toNat)
    (haig_eq : marks_ptr = aig_ptr + BitVec.ofNat 64 (8 * aigUsed.length))
    (hmarks_ub : marks_ptr.toNat + marks.length ≤ work_base.toNat + avail)
    (haig_ub : aig_ptr.toNat + 8 * aigUsed.length ≤ work_base.toNat + avail)
    (hm : bvCoiMem work_base aig_ptr marks_ptr avail hdr aigUsed marks m) :
    (bvHdrMem work_base hdr ⋆ region (work_base + 128) (avail - 128)) m := by
  have hwb_lt : work_base.toNat < 2 ^ 64 := work_base.isLt
  have haig_lt : aig_ptr.toNat < 2 ^ 64 := aig_ptr.isLt
  have hmptr : marks_ptr.toNat = aig_ptr.toNat + 8 * aigUsed.length := by
    rw [haig_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have g1 : ∀ f, array64 aig_ptr aigUsed f → region aig_ptr (8 * aigUsed.length) f :=
    fun _ h => array64_to_region (by omega) h
  have g2 : ∀ f, bytes marks_ptr marks f → region marks_ptr marks.length f :=
    fun _ h => bytes_to_region h
  unfold bvCoiMem at hm
  have h1 : (bvHdrMem work_base hdr ⋆
      region (work_base + 128) (aig_ptr.toNat - (work_base.toNat + 128)) ⋆
      region aig_ptr (8 * aigUsed.length) ⋆
      region marks_ptr marks.length ⋆
      region (marks_ptr + BitVec.ofNat 64 marks.length)
        (work_base.toNat + avail - (marks_ptr.toNat + marks.length))) m :=
    sep_lift_l (sep_mono2 (sep_mono2 (fun _ h => h) g1) g2) m hm
  have hm_m : (region marks_ptr marks.length ⋆
      region (marks_ptr + BitVec.ofNat 64 marks.length)
        (work_base.toNat + avail - (marks_ptr.toNat + marks.length))) =
      region marks_ptr (work_base.toNat + avail - marks_ptr.toNat) :=
    region_merge_eq (n := work_base.toNat + avail - marks_ptr.toNat) (by omega) (by omega)
  have hm_a : (region aig_ptr (8 * aigUsed.length) ⋆
      region marks_ptr (work_base.toNat + avail - marks_ptr.toNat)) =
      region aig_ptr (work_base.toNat + avail - aig_ptr.toNat) := by
    have hmerge := region_merge_eq (a := aig_ptr) (n1 := 8 * aigUsed.length)
      (n2 := work_base.toNat + avail - marks_ptr.toNat)
      (n := work_base.toNat + avail - aig_ptr.toNat) (by omega) (by omega)
    rw [← haig_eq] at hmerge
    exact hmerge
  have hm_p : (region (work_base + 128) (aig_ptr.toNat - (work_base.toNat + 128)) ⋆
      region aig_ptr (work_base.toNat + avail - aig_ptr.toNat)) =
      region (work_base + 128) (avail - 128) := by
    have h128 : (128 : BitVec 64).toNat = 128 := rfl
    have hadd_toNat : (work_base + 128).toNat = work_base.toNat + 128 := by
      rw [BitVec.toNat_add, h128, Nat.mod_eq_of_lt (by omega)]
    have haig_bv :
        (work_base + 128) + BitVec.ofNat 64 (aig_ptr.toNat - (work_base.toNat + 128)) =
        aig_ptr := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, hadd_toNat, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    have hmerge := region_merge_eq (a := work_base + 128)
      (n1 := aig_ptr.toNat - (work_base.toNat + 128))
      (n2 := work_base.toNat + avail - aig_ptr.toNat)
      (n := avail - 128) (by omega) (by omega)
    rw [haig_bv] at hmerge
    exact hmerge
  have h2 : (bvHdrMem work_base hdr ⋆
      (region (work_base + 128) (aig_ptr.toNat - (work_base.toNat + 128)) ⋆
        (region aig_ptr (8 * aigUsed.length) ⋆
          (region marks_ptr marks.length ⋆
            region (marks_ptr + BitVec.ofNat 64 marks.length)
              (work_base.toNat + avail - (marks_ptr.toNat + marks.length)))))) m := sep_ac h1
  rw [hm_m, hm_a, hm_p] at h2
  exact h2

end

end LeanQbe.T.Examples.Bitblast.Proof
