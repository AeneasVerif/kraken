/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.Arena
public import LeanQbe.T.Examples.Bitblast.Proof.Bvp1
public import LeanQbe.T.Examples.Bitblast.Ref.Tseitin
public import LeanQbe.T.Examples.Bitblast.Src.Full
public import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.MemLemmas

/-!
# Canonical Specifications, Semantic Invariants & `bitblastEnv` (`Bitblast.Proof.Specs`)

Single source of truth for all `31` canonical `LeanQbe.T.Spec` contracts (`30` defined functions
of `bitblastModule` + extern `kissat_solve_bytes` UNSAT spec), all `XPost`-polymorphic (`noExit =
true`, compatible with `XPost := False`), plus key pure & framing lemmas (`NodeDenotes`
monotonicity, `validDimacs_tseitin_of_counts`, and end-to-end UNSAT bridge).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open Std Std.Sat Std.ExtHashMap
open Std.Tactic.BVDecide
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Ref.BVProg
open LeanQbe.T.Examples.Bitblast.Ref.Tseitin
open LeanQbe.T.Examples.Bitblast.Src

@[expose] public section

/-! ## 1. AIG, Bitblast Evaluation & COI/DIMACS Invariants -/

/-- Exact C0 gate-count cap matching `BV_MAX_GATES` (`89478485`). -/
def bvMaxGates : Nat := 89478485

/-- Field tags of `BVHdrState` (`22` fields: `10 × u64` + `12 × u32`). -/
inductive HdrField
  | work_base | work_end | prog_ptr | aig_ptr | ht_ptr
  | atom_base_ptr | slice_off_ptr | lits_ptr | marks_ptr | dimacs_start
  | n_vars | n_nodes | n_cwords | root_node | num_atoms
  | aig_len | aig_cap | ht_mask | lits_len | lits_cap | oom | dimacs_len
  deriving DecidableEq

/-- Bitvector type (`BitVec 64` or `BitVec 32`) of a `BVHdrState` field. -/
def HdrField.ty : HdrField → Type
  | .work_base | .work_end | .prog_ptr | .aig_ptr | .ht_ptr
  | .atom_base_ptr | .slice_off_ptr | .lits_ptr | .marks_ptr | .dimacs_start => BitVec 64
  | _ => BitVec 32

/-- Field projection `h.get f : f.ty` for `BVHdrState`. -/
def BVHdrState.get (h : BVHdrState) (f : HdrField) : f.ty :=
  match f with
  | .work_base => h.work_base
  | .work_end => h.work_end
  | .prog_ptr => h.prog_ptr
  | .aig_ptr => h.aig_ptr
  | .ht_ptr => h.ht_ptr
  | .atom_base_ptr => h.atom_base_ptr
  | .slice_off_ptr => h.slice_off_ptr
  | .lits_ptr => h.lits_ptr
  | .marks_ptr => h.marks_ptr
  | .dimacs_start => h.dimacs_start
  | .n_vars => h.n_vars
  | .n_nodes => h.n_nodes
  | .n_cwords => h.n_cwords
  | .root_node => h.root_node
  | .num_atoms => h.num_atoms
  | .aig_len => h.aig_len
  | .aig_cap => h.aig_cap
  | .ht_mask => h.ht_mask
  | .lits_len => h.lits_len
  | .lits_cap => h.lits_cap
  | .oom => h.oom
  | .dimacs_len => h.dimacs_len

/-- Framing predicate: `h2` agrees with `h1` on every `BVHdrState` field not in `S`. -/
def Modifies (S : List HdrField) (h1 h2 : BVHdrState) : Prop :=
  ∀ f : HdrField, f ∉ S → h2.get f = h1.get f

/-- Framing predicate: `h2` agrees with `h1` on every `BVHdr` field except `aig_len` and `oom`. -/
abbrev BVHdrState.AigFrame (h1 h2 : BVHdrState) : Prop :=
  Modifies [.aig_len, .oom] h1 h2

/-- Runtime AIG + untrusted HT invariant (zero `Cache.WF` invariant on `htSlots`!). -/
structure AigInv (hdr : BVHdrState) (g : Aig)
    (aigWords : List (BitVec 64)) (htSlots : List (BitVec 32)) : Prop where
  wf : g.Wf
  num_atoms_eq : hdr.num_atoms.toNat = g.A
  aig_len_eq : hdr.aig_len.toNat = g.A + 1 + g.nodes.size
  aig_len_le_cap : g.A + 1 + g.nodes.size ≤ aigWords.length
  aig_cap_eq : hdr.aig_cap.toNat = aigWords.length
  aig_cap_lt : aigWords.length < bvDimacsBound
  gates_bound : g.nodes.size ≤ bvMaxGates
  words_match : AigWordsMatch g aigWords
  ht_len : htSlots.length = hdr.ht_mask.toNat + 1
  ht_mask_lt : ∀ x : BitVec 32, (x &&& hdr.ht_mask).toNat < htSlots.length
  ht_pos : 0 < htSlots.length
  ht_bound : htSlots.length ≤ 2 ^ 30

/-- Extract `w` `UInt32` literals from `litsPool` starting at offset `off`. -/
def litsSlice (litsPool : List (BitVec 32)) (off w : Nat) : List UInt32 :=
  ((litsPool.drop off).take w).map UInt32.ofBitVec

/-- Semantic denotation of evaluated `BVP1` node `i` under parsed `nodes : BinTree ProgNode`. -/
def NodeDenotes (bs : List UInt8) (nodes : BinTree ProgNode) (g : Aig)
    (sliceOffs litsPool : List (BitVec 32)) (litsLen : Nat) (i : Nat) : Prop :=
  match nodes.get? i with
  | some (.bv w e) =>
    let off := (sliceOffs.getD i 0#32).toNat
    off + w ≤ litsLen ∧
    (∀ j < w, ((litsPool.getD (off + j) 0#32) >>> 1).toNat < g.A + 1 + g.nodes.size) ∧
    (∀ assign : BVExpr.Assignment,
      SliceDenotes g (atomAssign bs assign) (litsSlice litsPool off w) (e.eval assign))
  | some (.bool e) =>
    let lit := sliceOffs.getD i 0#32
    (lit >>> 1).toNat < g.A + 1 + g.nodes.size ∧
    (∀ assign : BVExpr.Assignment,
      g.evalLit (atomAssign bs assign) (UInt32.ofBitVec lit) = e.eval assign)
  | none => False

/-- Combined invariant for bitblasting nodes `0 ..< k` inside `bvBlastMem`. -/
structure BlastEvalInv (cfg : BVWorkspaceCfg) (progPtr : BitVec 64) (progBytes : List UInt8)
    (vars : BinTree VarEntry) (cwords : BinTree Nat) (nodes : BinTree ProgNode)
    (prog : BVLogicalExpr) (hdr : BVHdrState) (g : Aig)
    (atomBases sliceOffs : List (BitVec 32)) (aigWords : List (BitVec 64))
    (htSlots litsPool : List (BitVec 32)) (k : Nat) : Prop where
  ws_ok : BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool
  parsed : ParsedBVP1 progBytes vars cwords nodes prog
  prog_ptr_eq : hdr.prog_ptr = progPtr
  prog_fit : progPtr.toNat + progBytes.length < 2 ^ 64
  nv_eq : cfg.n_vars = u32At progBytes 2
  nn_eq : cfg.n_nodes = u32At progBytes 3
  nc_eq : hdr.n_cwords.toNat = u32At progBytes 4
  root_eq : hdr.root_node.toNat = u32At progBytes 5
  lits_le_cap : hdr.lits_len.toNat ≤ cfg.lits_cap
  aig_inv : AigInv hdr g aigWords htSlots
  atoms_eq : g.A = countAtoms progBytes cfg.n_vars - 1
  atom_bases_eq : ∀ v < cfg.n_vars, (atomBases.getD v 0#32).toNat = countAtoms progBytes v
  k_le : k ≤ cfg.n_nodes
  prefix_ok : hdr.oom = 0#32 →
    ∀ i < k, NodeDenotes progBytes nodes g sliceOffs litsPool hdr.lits_len.toNat i

/-- Convert raw C0 byte marks (`0` vs non-zero) to `Array Bool` for `Ref.Tseitin`. -/
def marksToBool (marks : List UInt8) : Array Bool :=
  (marks.map (· != 0)).toArray

/-- Exact workspace sufficiency condition guaranteeing `bv_init_workspace` returns `true`. -/
def bvInitFitsCond (progBytes : List UInt8) (avail : Nat) : Prop :=
  let nv := u32At progBytes 2
  let nn := u32At progBytes 3
  let fixed := 128 + align8 (4 * nv) + align8 (4 * nn)
  fixed + 64 ≤ avail ∧
  countAtoms progBytes nv - 1 < min ((avail - fixed) / 32) (bvDimacsBound - 1)

/-- Concrete trivial-UNSAT condition guaranteeing `bv_solve_bytes` returns `20#64` (used for NV). -/
def bvSolveTrivialUnsatCond (progPtr : BitVec 64) (progBytes : List UInt8)
    (workPtr workCap fuel : BitVec 64) : Prop :=
  let pad := (8 - (workPtr.toNat % 8)) % 8
  fuel ≠ 0#64 ∧
  progPtr ≠ 0#64 ∧
  workPtr ≠ 0#64 ∧
  progPtr.toNat + progBytes.length < 2 ^ 64 ∧
  workPtr.toNat + workCap.toNat < 2 ^ 64 ∧
  pad + 128 ≤ workCap.toNat ∧
  ValidBVP1 progBytes ∧
  bvInitFitsCond progBytes (workCap.toNat - pad) ∧
  (∀ i < u32At progBytes 3,
    u32At progBytes (nodesOff (u32At progBytes 2) (u32At progBytes 4) + 5 * i) = opBConst) ∧
  u32At progBytes (nodesOff (u32At progBytes 2) (u32At progBytes 4) +
    5 * u32At progBytes 5 + 2) % 2 = 0

/-! ## 2. Canonical Specifications — Group A: `Validate` (`4` fns) -/

/-- Canonical spec for `bv_read_u32(prog_ptr, idx)`. -/
def bvReadU32Spec : Spec [i64, i64] [i32] :=
  fun ⟨progPtr, idx, ⟨⟩⟩ m Q _X =>
    ∃ (progBytes : List UInt8) (R : Mem 64 → Prop),
      progPtr.toNat + progBytes.length < 2 ^ 64 ∧
      4 * (idx.toNat + 1) ≤ progBytes.length ∧
      (bytes progPtr progBytes ⋆ R) m ∧
      Q (BitVec.ofNat 32 (u32At progBytes idx.toNat), ⟨⟩) m

/-- Canonical spec for `bv_count_atoms(prog_ptr, n_vars)`. -/
def bvCountAtomsSpec : Spec [i64, i32] [i64] :=
  fun ⟨progPtr, nVars, ⟨⟩⟩ m Q _X =>
    ∃ (progBytes : List UInt8) (R : Mem 64 → Prop),
      progPtr.toNat + progBytes.length < 2 ^ 64 ∧
      4 * (8 + 2 * nVars.toNat) ≤ progBytes.length ∧
      (bytes progPtr progBytes ⋆ R) m ∧
      Q (BitVec.ofNat 64 (countAtoms progBytes nVars.toNat), ⟨⟩) m

/-- Canonical spec for `bv_validate_node(prog_ptr, nodes_w, n_vars, n_cwords, i)`. -/
def bvValidateNodeSpec : Spec [i64, i64, i32, i32, i32] [.bool] :=
  fun ⟨progPtr, nodesW, nVars, nCwords, idx, ⟨⟩⟩ m Q _X =>
    ∃ (progBytes : List UInt8) (R : Mem 64 → Prop),
      progPtr.toNat + progBytes.length < 2 ^ 64 ∧
      nodesW.toNat = nodesOff nVars.toNat nCwords.toNat ∧
      4 * (nodesW.toNat + 5 * (idx.toNat + 1)) ≤ progBytes.length ∧
      (bytes progPtr progBytes ⋆ R) m ∧
      Q (validNodeAt progBytes nVars.toNat nCwords.toNat idx.toNat, ⟨⟩) m

/-- Canonical spec for `bv_validate(prog_ptr, prog_len)`. -/
def bvValidateSpec : Spec [i64, i64] [.bool] :=
  fun ⟨progPtr, progLen, ⟨⟩⟩ m Q _X =>
    ∃ (progBytes : List UInt8) (R : Mem 64 → Prop),
      progLen.toNat = progBytes.length ∧
      (bytes progPtr progBytes ⋆ R) m ∧
      ∀ r : Bool,
        (r = true ↔ progPtr ≠ 0#64 ∧ progPtr.toNat + progBytes.length < 2 ^ 64 ∧
          ValidBVP1 progBytes) →
        Q (r, ⟨⟩) m

/-! ## 3. Canonical Specifications — Group B: `Aig` (`11` fns) -/

/-- Canonical spec for `bv_hash_pair(lhs, rhs)` (untrusted HT needs zero hash semantics). -/
def bvHashPairSpec : Spec [i32, i32] [i32] :=
  fun _xs m Q _X =>
    ∀ r : BitVec 32, Q (r, ⟨⟩) m

/-- Canonical spec for `bv_aig_init(h, aig_ptr, aig_cap, ht_ptr, ht_mask, num_atoms)`. -/
def bvAigInitSpec : Spec [i64, i64, i32, i64, i32, i32] [] :=
  fun ⟨h, aigPtr, aigCap, htPtr, htMask, numAtoms, ⟨⟩⟩ m Q _X =>
    ∃ (hdr : BVHdrState) (htSlots : List (BitVec 32)) (R : Mem 64 → Prop),
      htSlots.length = htMask.toNat + 1 ∧
      htSlots.length ≤ 2 ^ 30 ∧
      numAtoms.toNat + 1 < 2 ^ 32 ∧
      (bvHdrMem h hdr ⋆ array (t := i32) htPtr htSlots ⋆ R) m ∧
      ∀ m' : Mem 64,
        (bvHdrMem h { hdr with
            aig_ptr := aigPtr, aig_cap := aigCap, ht_ptr := htPtr,
            ht_mask := htMask, num_atoms := numAtoms,
            aig_len := numAtoms + 1#32, oom := 0#32 } ⋆
          array (t := i32) htPtr (List.replicate (htMask.toNat + 1) 0#32) ⋆ R) m' →
        Q ⟨⟩ m'

/-- Shared canonical spec shape for binary AIG gate constructors (`and`, `or`, `xor`, `beq`). -/
def bvAigBinSpec (op : Bool → Bool → Bool) (maxNewGates : Nat) : Spec [i64, i32, i32] [i32] :=
  fun ⟨h, lhs, rhs, ⟨⟩⟩ m Q _X =>
    ∃ (hdr : BVHdrState) (g : Aig) (aigWords : List (BitVec 64))
      (htSlots : List (BitVec 32)) (R : Mem 64 → Prop),
      AigInv hdr g aigWords htSlots ∧
      (hdr.oom = 0#32 →
        (lhs >>> 1).toNat < hdr.aig_len.toNat ∧ (rhs >>> 1).toNat < hdr.aig_len.toNat) ∧
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆ R) m ∧
      ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig)
        (aigWords' : List (BitVec 64)) (htSlots' : List (BitVec 32)) (m' : Mem 64),
        hdr.AigFrame hdr' →
        g ≤ g' →
        g'.nodes.size ≤ g.nodes.size + maxNewGates →
        AigInv hdr' g' aigWords' htSlots' →
        (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
        (hdr.oom = 0#32 → g.A + 1 + g.nodes.size + maxNewGates ≤ hdr.aig_cap.toNat →
          g.nodes.size + maxNewGates ≤ bvMaxGates → hdr'.oom = 0#32) →
        (hdr'.oom = 0#32 →
          (ret >>> 1).toNat < hdr'.aig_len.toNat ∧
          ∀ ρ : Nat → Bool,
            g'.evalLit ρ (UInt32.ofBitVec ret) =
              op (g.evalLit ρ (UInt32.ofBitVec lhs)) (g.evalLit ρ (UInt32.ofBitVec rhs))) →
        (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
          array (t := i32) hdr'.ht_ptr htSlots' ⋆ R) m' →
        Q (ret, ⟨⟩) m'

/-- Canonical spec for `bv_mk_and(h, lhs, rhs)`. -/
abbrev bvMkAndSpec : Spec [i64, i32, i32] [i32] :=
  bvAigBinSpec (· && ·) 1

/-- Canonical spec for `bv_aig_not(l)`. -/
def bvAigNotSpec : Spec [i32] [i32] :=
  fun ⟨l, ⟨⟩⟩ m Q _X => Q (l ^^^ 1#32, ⟨⟩) m

/-- Canonical spec for `bv_aig_or(h, a, b)`. -/
abbrev bvAigOrSpec : Spec [i64, i32, i32] [i32] :=
  bvAigBinSpec (· || ·) 1

/-- Canonical spec for `bv_aig_xor(h, a, b)`. -/
abbrev bvAigXorSpec : Spec [i64, i32, i32] [i32] :=
  bvAigBinSpec (· ^^ ·) 3

/-- Canonical spec for `bv_aig_beq(h, a, b)`. -/
abbrev bvAigBeqSpec : Spec [i64, i32, i32] [i32] :=
  bvAigBinSpec (· == ·) 3

/-- Canonical spec for `bv_aig_ite(h, c, t, f)`. -/
def bvAigIteSpec : Spec [i64, i32, i32, i32] [i32] :=
  fun ⟨h, c, t, f, ⟨⟩⟩ m Q _X =>
    ∃ (hdr : BVHdrState) (g : Aig) (aigWords : List (BitVec 64))
      (htSlots : List (BitVec 32)) (R : Mem 64 → Prop),
      AigInv hdr g aigWords htSlots ∧
      (hdr.oom = 0#32 →
        (c >>> 1).toNat < hdr.aig_len.toNat ∧
        (t >>> 1).toNat < hdr.aig_len.toNat ∧
        (f >>> 1).toNat < hdr.aig_len.toNat) ∧
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆ R) m ∧
      ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig)
        (aigWords' : List (BitVec 64)) (htSlots' : List (BitVec 32)) (m' : Mem 64),
        hdr.AigFrame hdr' →
        g ≤ g' →
        g'.nodes.size ≤ g.nodes.size + 3 →
        AigInv hdr' g' aigWords' htSlots' →
        (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
        (hdr.oom = 0#32 → g.A + 1 + g.nodes.size + 3 ≤ hdr.aig_cap.toNat →
          g.nodes.size + 3 ≤ bvMaxGates → hdr'.oom = 0#32) →
        (hdr'.oom = 0#32 →
          (ret >>> 1).toNat < hdr'.aig_len.toNat ∧
          ∀ ρ : Nat → Bool,
            g'.evalLit ρ (UInt32.ofBitVec ret) =
              cond (g.evalLit ρ (UInt32.ofBitVec c))
                (g.evalLit ρ (UInt32.ofBitVec t))
                (g.evalLit ρ (UInt32.ofBitVec f))) →
        (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
          array (t := i32) hdr'.ht_ptr htSlots' ⋆ R) m' →
        Q (ret, ⟨⟩) m'

/-- Canonical spec for `bv_lits_mark(h)`. -/
def bvLitsMarkSpec : Spec [i64] [i32] :=
  fun ⟨h, ⟨⟩⟩ m Q _X =>
    ∃ (hdr : BVHdrState) (R : Mem 64 → Prop),
      (bvHdrMem h hdr ⋆ R) m ∧
      Q (hdr.lits_len, ⟨⟩) m

/-- Canonical spec for `bv_lits_release(h, mark)`. -/
def bvLitsReleaseSpec : Spec [i64, i32] [] :=
  fun ⟨h, mark, ⟨⟩⟩ m Q _X =>
    ∃ (hdr : BVHdrState) (R : Mem 64 → Prop),
      (bvHdrMem h hdr ⋆ R) m ∧
      let len' := if mark.toNat ≤ hdr.lits_len.toNat then mark else hdr.lits_len
      ∀ m' : Mem 64, (bvHdrMem h { hdr with lits_len := len' } ⋆ R) m' → Q ⟨⟩ m'

/-- Canonical spec for `bv_lits_alloc(h, count)`. -/
def bvLitsAllocSpec : Spec [i64, i32] [i32] :=
  fun ⟨h, count, ⟨⟩⟩ m Q _X =>
    ∃ (hdr : BVHdrState) (R : Mem 64 → Prop),
      (bvHdrMem h hdr ⋆ R) m ∧
      if hdr.oom = 0#32 ∧ hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
          count.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat then
        ∀ m' : Mem 64,
          (bvHdrMem h { hdr with lits_len := hdr.lits_len + count } ⋆ R) m' →
          Q (hdr.lits_len, ⟨⟩) m'
      else
        let oom' := if hdr.oom ≠ 0#32 then hdr.oom else 1#32
        ∀ m' : Mem 64,
          (bvHdrMem h { hdr with oom := oom' } ⋆ R) m' →
          Q (0xFFFFFFFF#32, ⟨⟩) m'

/-! ## 4. Canonical Specifications — Group C: `Tseitin` (`8` fns) -/

/-- Canonical spec for `bv_coi_mark(h, root)`. -/
def bvCoiMarkSpec : Spec [i64, i32] [] :=
  fun ⟨h, root, ⟨⟩⟩ m Q _X =>
    ∃ (hdr : BVHdrState) (g : Aig) (aigUsed : List (BitVec 64))
      (marks0 : List UInt8) (R : Mem 64 → Prop),
      g.Wf ∧
      hdr.num_atoms.toNat = g.A ∧
      hdr.aig_len.toNat = g.A + 1 + g.nodes.size ∧
      hdr.aig_len.toNat < bvDimacsBound ∧
      AigWordsMatch g aigUsed ∧
      aigUsed.length = hdr.aig_len.toNat ∧
      marks0.length = hdr.aig_len.toNat ∧
      hdr.marks_ptr ≠ 0#64 ∧
      hdr.marks_ptr.toNat + marks0.length < 2 ^ 64 ∧
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigUsed ⋆
        bytes hdr.marks_ptr marks0 ⋆ R) m ∧
      ∀ (marks1 : List UInt8) (m' : Mem 64),
        marks1.length = hdr.aig_len.toNat →
        marksToBool marks1 = Ref.Tseitin.coiMark g (UInt32.ofBitVec root) →
        (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigUsed ⋆
          bytes hdr.marks_ptr marks1 ⋆ R) m' →
        Q ⟨⟩ m'

/-- Canonical spec for `bv_dec_len(v)`. -/
def bvDecLenSpec : Spec [i32] [i64] :=
  fun ⟨v, ⟨⟩⟩ m Q _X =>
    Q (BitVec.ofNat 64 (natToBytes v.toNat).length, ⟨⟩) m

/-- Canonical spec for `bv_lit_bytes(lit)`. -/
def bvLitBytesSpec : Spec [i32] [i64] :=
  fun ⟨lit, ⟨⟩⟩ m Q _X =>
    Q (BitVec.ofNat 64 (encodeDimacsLit (litToDimacs (UInt32.ofBitVec lit))).length, ⟨⟩) m

/-- Canonical spec for `bv_write_dec(p, v)`. -/
def bvWriteDecSpec : Spec [i64, i32] [i64] :=
  fun ⟨p, v, ⟨⟩⟩ m Q _X =>
    let bs := natToBytes v.toNat
    ∃ R : Mem 64 → Prop,
      p.toNat + bs.length < 2 ^ 64 ∧
      (region p bs.length ⋆ R) m ∧
      ∀ m' : Mem 64,
        (bytes p bs ⋆ R) m' →
        Q (p + BitVec.ofNat 64 bs.length, ⟨⟩) m'

/-- Canonical spec for `bv_write_lit(p, lit)`. -/
def bvWriteLitSpec : Spec [i64, i32] [i64] :=
  fun ⟨p, lit, ⟨⟩⟩ m Q _X =>
    let bs := encodeDimacsLit (litToDimacs (UInt32.ofBitVec lit))
    ∃ R : Mem 64 → Prop,
      p.toNat + bs.length < 2 ^ 64 ∧
      (region p bs.length ⋆ R) m ∧
      ∀ m' : Mem 64,
        (bytes p bs ⋆ R) m' →
        Q (p + BitVec.ofNat 64 bs.length, ⟨⟩) m'

/-- Canonical spec for `bv_write_dimacs_hdr(p, mv, nc)`. -/
def bvWriteDimacsHdrSpec : Spec [i64, i32, i32] [i64] :=
  fun ⟨p, mv, nc, ⟨⟩⟩ m Q _X =>
    let bs := dimacsHeaderPrefix ++ natToBytes mv.toNat ++ [asciiSpace] ++
      natToBytes nc.toNat ++ [asciiNewline]
    ∃ R : Mem 64 → Prop,
      p.toNat + bs.length < 2 ^ 64 ∧
      (region p bs.length ⋆ R) m ∧
      ∀ m' : Mem 64,
        (bytes p bs ⋆ R) m' →
        Q (p + BitVec.ofNat 64 bs.length, ⟨⟩) m'

/-- Canonical spec for `bv_write_clause_end(p)`. -/
def bvWriteClauseEndSpec : Spec [i64] [i64] :=
  fun ⟨p, ⟨⟩⟩ m Q _X =>
    ∃ R : Mem 64 → Prop,
      p.toNat + 2 < 2 ^ 64 ∧
      (region p 2 ⋆ R) m ∧
      ∀ m' : Mem 64,
        (bytes p [asciiZero, asciiNewline] ⋆ R) m' →
        Q (p + 2#64, ⟨⟩) m'

/-- Canonical spec for `bv_dimacs_write(h, root)`. -/
def bvDimacsWriteSpec : Spec [i64, i32] [.bool] :=
  fun ⟨h, root, ⟨⟩⟩ m Q _X =>
    ∃ (workBase aigPtr marksPtr : BitVec 64) (avail : Nat) (hdr : BVHdrState)
      (g : Aig) (aigUsed : List (BitVec 64)) (marks : List UInt8) (R : Mem 64 → Prop),
      h = workBase ∧
      workBase.toNat + avail < 2 ^ 64 ∧
      hdr.work_base = workBase ∧
      hdr.work_end = workBase + BitVec.ofNat 64 avail ∧
      hdr.aig_ptr = aigPtr ∧
      hdr.marks_ptr = marksPtr ∧
      workBase.toNat + 128 ≤ aigPtr.toNat ∧
      marksPtr = aigPtr + BitVec.ofNat 64 (8 * aigUsed.length) ∧
      aigPtr.toNat + 8 * aigUsed.length + marks.length ≤ workBase.toNat + avail ∧
      g.Wf ∧
      hdr.num_atoms.toNat = g.A ∧
      hdr.aig_len.toNat = g.A + 1 + g.nodes.size ∧
      hdr.aig_len.toNat < bvDimacsBound ∧
      AigWordsMatch g aigUsed ∧
      aigUsed.length = hdr.aig_len.toNat ∧
      marks.length = hdr.aig_len.toNat ∧
      (root >>> 1).toNat < hdr.aig_len.toNat ∧
      marksPtr ≠ 0#64 ∧
      (bvCoiMem workBase aigPtr marksPtr avail hdr aigUsed marks ⋆ R) m ∧
      let cnf := Ref.Tseitin.tseitin g (marksToBool marks) (UInt32.ofBitVec root)
      let dbs := encodeDimacs cnf
      ∀ (ret : Bool) (hdr' : BVHdrState) (m' : Mem 64),
        (ret = true →
          ValidDimacsCnf cnf ∧
          hdr'.dimacs_start.toNat + dbs.length = workBase.toNat + avail ∧
          hdr'.dimacs_len.toNat = dbs.length ∧
          workBase.toNat + 128 ≤ hdr'.dimacs_start.toNat ∧
          (bvHdrMem workBase hdr' ⋆
            region (workBase + 128) (hdr'.dimacs_start.toNat - (workBase.toNat + 128)) ⋆
            bytes hdr'.dimacs_start dbs ⋆ R) m' →
          Q (true, ⟨⟩) m') ∧
        (ret = false →
          (bvHdrMem workBase hdr' ⋆ region (workBase + 128) (avail - 128) ⋆ R) m' →
          Q (false, ⟨⟩) m')

/-! ## 5. Canonical Specifications — Group D: `Driver` (`7` fns) & Extern `kissat_solve_bytes` -/

/-- Shared canonical spec for `bv_eval_ops_core`/`shift_mul`/`div_cpop`. -/
def bvEvalSubSpec : Spec [i64, i32] [.bool] :=
  fun ⟨h, nodeIdx, ⟨⟩⟩ m Q _X =>
    ∃ (cfg : BVWorkspaceCfg) (progPtr : BitVec 64) (progBytes : List UInt8)
      (vars : BinTree VarEntry) (cwords : BinTree Nat) (nodes : BinTree ProgNode)
      (prog : BVLogicalExpr) (hdr : BVHdrState) (g : Aig)
      (atomBases sliceOffs : List (BitVec 32)) (aigWords : List (BitVec 64))
      (htSlots litsPool : List (BitVec 32)) (R : Mem 64 → Prop),
      h = cfg.work_base ∧
      nodeIdx.toNat < cfg.n_nodes ∧
      hdr.oom = 0#32 ∧
      BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
        atomBases sliceOffs aigWords htSlots litsPool nodeIdx.toNat ∧
      (bytes progPtr progBytes ⋆
        bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m ∧
      ∀ (ret : Bool) (hdr' : BVHdrState) (g' : Aig) (sliceOffs' : List (BitVec 32))
        (aigWords' : List (BitVec 64)) (htSlots' litsPool' : List (BitVec 32)) (m' : Mem 64),
        BVWorkspaceOk cfg hdr' atomBases sliceOffs' aigWords' htSlots' litsPool' →
        AigInv hdr' g' aigWords' htSlots' →
        g ≤ g' →
        hdr'.prog_ptr = progPtr →
        hdr'.n_cwords = hdr.n_cwords →
        hdr'.root_node = hdr.root_node →
        (ret = true →
          hdr'.oom = 0#32 ∧
          BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr' g'
            atomBases sliceOffs' aigWords' htSlots' litsPool' (nodeIdx.toNat + 1)) →
        (bytes progPtr progBytes ⋆
          bvBlastMem cfg hdr' atomBases sliceOffs' aigWords' htSlots' litsPool' ⋆ R) m' →
        Q (ret, ⟨⟩) m'

/-- Canonical spec for `bv_eval_node(h, node_idx)` (extends `bvEvalSubSpec` with `BCONST` NV). -/
def bvEvalNodeSpec : Spec [i64, i32] [.bool] :=
  fun ⟨h, nodeIdx, ⟨⟩⟩ m Q _X =>
    ∃ (cfg : BVWorkspaceCfg) (progPtr : BitVec 64) (progBytes : List UInt8)
      (vars : BinTree VarEntry) (cwords : BinTree Nat) (nodes : BinTree ProgNode)
      (prog : BVLogicalExpr) (hdr : BVHdrState) (g : Aig)
      (atomBases sliceOffs : List (BitVec 32)) (aigWords : List (BitVec 64))
      (htSlots litsPool : List (BitVec 32)) (R : Mem 64 → Prop),
      h = cfg.work_base ∧
      nodeIdx.toNat < cfg.n_nodes ∧
      hdr.oom = 0#32 ∧
      BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
        atomBases sliceOffs aigWords htSlots litsPool nodeIdx.toNat ∧
      (bytes progPtr progBytes ⋆
        bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m ∧
      ∀ (ret : Bool) (hdr' : BVHdrState) (g' : Aig) (sliceOffs' : List (BitVec 32))
        (aigWords' : List (BitVec 64)) (htSlots' litsPool' : List (BitVec 32)) (m' : Mem 64),
        BVWorkspaceOk cfg hdr' atomBases sliceOffs' aigWords' htSlots' litsPool' →
        AigInv hdr' g' aigWords' htSlots' →
        g ≤ g' →
        hdr'.prog_ptr = progPtr →
        hdr'.n_cwords = hdr.n_cwords →
        hdr'.root_node = hdr.root_node →
        (ret = true →
          hdr'.oom = 0#32 ∧
          BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr' g'
            atomBases sliceOffs' aigWords' htSlots' litsPool' (nodeIdx.toNat + 1)) →
        (u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * nodeIdx.toNat) = opBConst →
          ret = true ∧ g' = g ∧
          sliceOffs' = sliceOffs.set nodeIdx.toNat
            (BitVec.ofNat 32 (u32At progBytes
              (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * nodeIdx.toNat + 2) % 2))) →
        (bytes progPtr progBytes ⋆
          bvBlastMem cfg hdr' atomBases sliceOffs' aigWords' htSlots' litsPool' ⋆ R) m' →
        Q (ret, ⟨⟩) m'

/-- Canonical spec for `bv_eval_program(h)`. -/
def bvEvalProgramSpec : Spec [i64] [.bool] :=
  fun ⟨h, ⟨⟩⟩ m Q _X =>
    ∃ (cfg : BVWorkspaceCfg) (progPtr : BitVec 64) (progBytes : List UInt8)
      (vars : BinTree VarEntry) (cwords : BinTree Nat) (nodes : BinTree ProgNode)
      (prog : BVLogicalExpr) (hdr : BVHdrState) (g : Aig)
      (atomBases sliceOffs : List (BitVec 32)) (aigWords : List (BitVec 64))
      (htSlots litsPool : List (BitVec 32)) (R : Mem 64 → Prop),
      h = cfg.work_base ∧
      hdr.oom = 0#32 ∧
      BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
        atomBases sliceOffs aigWords htSlots litsPool 0 ∧
      (bytes progPtr progBytes ⋆
        bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m ∧
      ∀ (ret : Bool) (hdr' : BVHdrState) (g' : Aig) (sliceOffs' : List (BitVec 32))
        (aigWords' : List (BitVec 64)) (htSlots' litsPool' : List (BitVec 32)) (m' : Mem 64),
        BVWorkspaceOk cfg hdr' atomBases sliceOffs' aigWords' htSlots' litsPool' →
        AigInv hdr' g' aigWords' htSlots' →
        g ≤ g' →
        hdr'.root_node = hdr.root_node →
        (ret = true →
          hdr'.oom = 0#32 ∧
          BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr' g'
            atomBases sliceOffs' aigWords' htSlots' litsPool' cfg.n_nodes) →
        ((∀ i < cfg.n_nodes,
            u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * i) = opBConst) →
          ret = true ∧ g' = g ∧
          ∀ i < cfg.n_nodes,
            (sliceOffs'.getD i 0#32).toNat =
              u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * i + 2) % 2) →
        (bytes progPtr progBytes ⋆
          bvBlastMem cfg hdr' atomBases sliceOffs' aigWords' htSlots' litsPool' ⋆ R) m' →
        Q (ret, ⟨⟩) m'

/-- Canonical spec for `bv_init_workspace(h, work_base, avail, prog_ptr)`. -/
def bvInitWorkspaceSpec : Spec [i64, i64, i64, i64] [.bool] :=
  fun ⟨h, workBase, avail, progPtr, ⟨⟩⟩ m Q _X =>
    ∃ (progBytes : List UInt8) (vars : BinTree VarEntry) (cwords : BinTree Nat)
      (nodes : BinTree ProgNode) (prog : BVLogicalExpr) (R : Mem 64 → Prop),
      h = workBase ∧
      ParsedBVP1 progBytes vars cwords nodes prog ∧
      progPtr.toNat + progBytes.length < 2 ^ 64 ∧
      workBase.toNat + avail.toNat < 2 ^ 64 ∧
      (bytes progPtr progBytes ⋆ region workBase avail.toNat ⋆ R) m ∧
      (bvInitFitsCond progBytes avail.toNat →
        ∀ (cfg : BVWorkspaceCfg) (hdr : BVHdrState)
          (atomBases sliceOffs : List (BitVec 32)) (aigWords : List (BitVec 64))
          (htSlots litsPool : List (BitVec 32)) (m' : Mem 64),
          cfg.work_base = workBase →
          cfg.avail = avail.toNat →
          hdr.oom = 0#32 →
          BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr
            ⟨countAtoms progBytes cfg.n_vars - 1, #[]⟩
            atomBases sliceOffs aigWords htSlots litsPool 0 →
          (bytes progPtr progBytes ⋆
            bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m' →
          Q (true, ⟨⟩) m') ∧
      (¬ bvInitFitsCond progBytes avail.toNat →
        (∀ (cfg : BVWorkspaceCfg) (hdr : BVHdrState)
          (atomBases sliceOffs : List (BitVec 32)) (aigWords : List (BitVec 64))
          (htSlots litsPool : List (BitVec 32)) (m' : Mem 64),
          cfg.work_base = workBase →
          cfg.avail = avail.toNat →
          hdr.oom = 0#32 →
          BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr
            ⟨countAtoms progBytes cfg.n_vars - 1, #[]⟩
            atomBases sliceOffs aigWords htSlots litsPool 0 →
          (bytes progPtr progBytes ⋆
            bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m' →
          Q (true, ⟨⟩) m') ∧
        Q (false, ⟨⟩) m)

/-- Canonical extern UNSAT spec for `kissat_solve_bytes(cnf_ptr, cnf_len, work_ptr, work_cap,
fuel)`. -/
def kissatSolveBytesUnsatSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun ⟨cnfPtr, cnfLen, workPtr, workCap, _fuel, ⟨⟩⟩ m Q _X =>
    ∃ (cnfBytes : List UInt8) (R : Mem 64 → Prop),
      cnfLen.toNat = cnfBytes.length ∧
      cnfPtr.toNat + cnfBytes.length < 2 ^ 64 ∧
      workPtr.toNat + workCap.toNat < 2 ^ 64 ∧
      (bytes cnfPtr cnfBytes ⋆ region workPtr workCap.toNat ⋆ R) m ∧
      ∀ (r : BitVec 64) (m' : Mem 64),
        (bytes cnfPtr cnfBytes ⋆ region workPtr workCap.toNat ⋆ R) m' →
        (r = 20#64 → ∃ cnf : CNF Nat, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        Q (r, ⟨⟩) m'

/-- Canonical top-level spec for `bv_solve_bytes(prog_ptr, prog_len, work_ptr, work_cap, fuel)`. -/
def bvSolveBytesSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun ⟨progPtr, progLen, workPtr, workCap, fuel, ⟨⟩⟩ m Q _X =>
    ∃ (progBytes : List UInt8) (R : Mem 64 → Prop),
      progLen.toNat = progBytes.length ∧
      (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ R) m ∧
      ∀ (r : BitVec 64) (m' : Mem 64),
        (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ R) m' →
        (r = 20#64 → ∀ prog : BVLogicalExpr, BVProg.parse progBytes = some prog → prog.Unsat) →
        (bvSolveTrivialUnsatCond progPtr progBytes workPtr workCap fuel → r = 20#64) →
        Q (r, ⟨⟩) m'

end

/-! ## 6. Key Pure, Framing & End-to-End Composition Lemmas -/

public section

theorem Modifies.refl (S : List HdrField) (h : BVHdrState) : Modifies S h h :=
  fun _ _ => rfl

theorem Modifies.trans {S : List HdrField} {h1 h2 h3 : BVHdrState}
    (h12 : Modifies S h1 h2) (h23 : Modifies S h2 h3) : Modifies S h1 h3 :=
  fun f hf => (h23 f hf).trans (h12 f hf)

theorem Modifies.trans_append {S T : List HdrField} {h1 h2 h3 : BVHdrState}
    (h12 : Modifies S h1 h2) (h23 : Modifies T h2 h3) : Modifies (S ++ T) h1 h3 :=
  fun f hf =>
    (h23 f fun h => hf (List.mem_append_right S h)).trans
      (h12 f fun h => hf (List.mem_append_left T h))

theorem Modifies.mono {S T : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hsub : S ⊆ T := by decide) : Modifies T h1 h2 :=
  fun f hf => h f (fun hmem => hf (hsub hmem))

theorem Modifies.get_eq {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (f : HdrField) (hf : f ∉ S := by decide) :
    h2.get f = h1.get f :=
  h f hf

theorem Modifies.erase_of_eq {S : List HdrField} {x : HdrField} {h1 h2 : BVHdrState}
    (h : Modifies (x :: S) h1 h2) (heq : h2.get x = h1.get x) :
    Modifies S h1 h2 :=
  fun f hf => if hfx : f = x then hfx ▸ heq else h f fun hm =>
    match hm with
    | .head _ => hfx rfl
    | .tail _ hm' => hf hm'

theorem Modifies.drop_lits_len {h1 h2 : BVHdrState}
    (h : Modifies [.aig_len, .lits_len, .oom] h1 h2) (hlen : h2.lits_len = h1.lits_len) :
    Modifies [.aig_len, .oom] h1 h2 :=
  (h.mono (T := [.lits_len, .aig_len, .oom]) (by decide)).erase_of_eq hlen

theorem Modifies.work_base {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .work_base ∉ S := by decide) :
    h2.work_base = h1.work_base := h .work_base hf
theorem Modifies.work_end {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .work_end ∉ S := by decide) :
    h2.work_end = h1.work_end := h .work_end hf
theorem Modifies.prog_ptr {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .prog_ptr ∉ S := by decide) :
    h2.prog_ptr = h1.prog_ptr := h .prog_ptr hf
theorem Modifies.aig_ptr {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .aig_ptr ∉ S := by decide) :
    h2.aig_ptr = h1.aig_ptr := h .aig_ptr hf
theorem Modifies.ht_ptr {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .ht_ptr ∉ S := by decide) :
    h2.ht_ptr = h1.ht_ptr := h .ht_ptr hf
theorem Modifies.atom_base_ptr {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .atom_base_ptr ∉ S := by decide) :
    h2.atom_base_ptr = h1.atom_base_ptr := h .atom_base_ptr hf
theorem Modifies.slice_off_ptr {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .slice_off_ptr ∉ S := by decide) :
    h2.slice_off_ptr = h1.slice_off_ptr := h .slice_off_ptr hf
theorem Modifies.lits_ptr {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .lits_ptr ∉ S := by decide) :
    h2.lits_ptr = h1.lits_ptr := h .lits_ptr hf
theorem Modifies.marks_ptr {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .marks_ptr ∉ S := by decide) :
    h2.marks_ptr = h1.marks_ptr := h .marks_ptr hf
theorem Modifies.dimacs_start {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .dimacs_start ∉ S := by decide) :
    h2.dimacs_start = h1.dimacs_start := h .dimacs_start hf
theorem Modifies.n_vars {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .n_vars ∉ S := by decide) :
    h2.n_vars = h1.n_vars := h .n_vars hf
theorem Modifies.n_nodes {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .n_nodes ∉ S := by decide) :
    h2.n_nodes = h1.n_nodes := h .n_nodes hf
theorem Modifies.n_cwords {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .n_cwords ∉ S := by decide) :
    h2.n_cwords = h1.n_cwords := h .n_cwords hf
theorem Modifies.root_node {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .root_node ∉ S := by decide) :
    h2.root_node = h1.root_node := h .root_node hf
theorem Modifies.num_atoms {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .num_atoms ∉ S := by decide) :
    h2.num_atoms = h1.num_atoms := h .num_atoms hf
theorem Modifies.aig_len {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .aig_len ∉ S := by decide) :
    h2.aig_len = h1.aig_len := h .aig_len hf
theorem Modifies.aig_cap {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .aig_cap ∉ S := by decide) :
    h2.aig_cap = h1.aig_cap := h .aig_cap hf
theorem Modifies.ht_mask {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .ht_mask ∉ S := by decide) :
    h2.ht_mask = h1.ht_mask := h .ht_mask hf
theorem Modifies.lits_len {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .lits_len ∉ S := by decide) :
    h2.lits_len = h1.lits_len := h .lits_len hf
theorem Modifies.lits_cap {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .lits_cap ∉ S := by decide) :
    h2.lits_cap = h1.lits_cap := h .lits_cap hf
theorem Modifies.oom {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .oom ∉ S := by decide) :
    h2.oom = h1.oom := h .oom hf
theorem Modifies.dimacs_len {S : List HdrField} {h1 h2 : BVHdrState}
    (h : Modifies S h1 h2) (hf : .dimacs_len ∉ S := by decide) :
    h2.dimacs_len = h1.dimacs_len := h .dimacs_len hf

theorem BVHdrState.get_with_aig_len (h : BVHdrState) (v : BitVec 32) {f : HdrField}
    (hf : f ≠ .aig_len) : ({ h with aig_len := v } : BVHdrState).get f = h.get f := by
  cases f <;> first | exact absurd rfl hf | rfl

theorem BVHdrState.get_with_lits_len (h : BVHdrState) (v : BitVec 32) {f : HdrField}
    (hf : f ≠ .lits_len) : ({ h with lits_len := v } : BVHdrState).get f = h.get f := by
  cases f <;> first | exact absurd rfl hf | rfl

theorem BVHdrState.get_with_oom (h : BVHdrState) (v : BitVec 32) {f : HdrField}
    (hf : f ≠ .oom) : ({ h with oom := v } : BVHdrState).get f = h.get f := by
  cases f <;> first | exact absurd rfl hf | rfl

theorem Modifies.with_aig_len {S : List HdrField} {h0 h1 : BVHdrState}
    (h : Modifies S h0 h1) (v : BitVec 32) (hf : .aig_len ∈ S := by decide) :
    Modifies S h0 { h1 with aig_len := v } :=
  fun f hfn => (h1.get_with_aig_len v (fun he : f = .aig_len => hfn (he ▸ hf))).trans (h f hfn)

theorem Modifies.with_lits_len {S : List HdrField} {h0 h1 : BVHdrState}
    (h : Modifies S h0 h1) (v : BitVec 32) (hf : .lits_len ∈ S := by decide) :
    Modifies S h0 { h1 with lits_len := v } :=
  fun f hfn => (h1.get_with_lits_len v (fun he : f = .lits_len => hfn (he ▸ hf))).trans (h f hfn)

theorem Modifies.with_oom {S : List HdrField} {h0 h1 : BVHdrState}
    (h : Modifies S h0 h1) (v : BitVec 32) (hf : .oom ∈ S := by decide) :
    Modifies S h0 { h1 with oom := v } :=
  fun f hfn => (h1.get_with_oom v (fun he : f = .oom => hfn (he ▸ hf))).trans (h f hfn)

theorem Modifies.set_aig_len (S : List HdrField) (h : BVHdrState) (v : BitVec 32)
    (hf : .aig_len ∈ S := by decide) : Modifies S h { h with aig_len := v } :=
  (Modifies.refl S h).with_aig_len v hf

theorem Modifies.set_lits_len (S : List HdrField) (h : BVHdrState) (v : BitVec 32)
    (hf : .lits_len ∈ S := by decide) : Modifies S h { h with lits_len := v } :=
  (Modifies.refl S h).with_lits_len v hf

theorem Modifies.set_oom (S : List HdrField) (h : BVHdrState) (v : BitVec 32)
    (hf : .oom ∈ S := by decide) : Modifies S h { h with oom := v } :=
  (Modifies.refl S h).with_oom v hf

theorem Modifies.with_lits_len_oom {S : List HdrField} {h0 h1 : BVHdrState}
    (h : Modifies S h0 h1) (l o : BitVec 32)
    (hl : .lits_len ∈ S := by decide) (ho : .oom ∈ S := by decide) :
    Modifies S h0 { h1 with lits_len := l, oom := o } :=
  (h.with_lits_len l hl).with_oom o ho

theorem Modifies.set_lits_len_oom (S : List HdrField) (h : BVHdrState) (l o : BitVec 32)
    (hl : .lits_len ∈ S := by decide) (ho : .oom ∈ S := by decide) :
    Modifies S h { h with lits_len := l, oom := o } :=
  (Modifies.refl S h).with_lits_len_oom l o hl ho

theorem AigInv.of_modifies {hdr hdr' : BVHdrState} {g : Aig}
    {aigWords : List (BitVec 64)} {htSlots : List (BitVec 32)} {S : List HdrField}
    (hinv : AigInv hdr g aigWords htSlots) (hfr : Modifies S hdr hdr')
    (hal : hdr'.aig_len = hdr.aig_len)
    (hsub : S ⊆ [.aig_len, .lits_len, .oom] := by decide) :
    AigInv hdr' g aigWords htSlots :=
  have h := hfr.mono hsub
  { hinv with
    num_atoms_eq := by rw [h.num_atoms]; exact hinv.num_atoms_eq
    aig_len_eq := by rw [hal]; exact hinv.aig_len_eq
    aig_cap_eq := by rw [h.aig_cap]; exact hinv.aig_cap_eq
    ht_len := by rw [h.ht_mask]; exact hinv.ht_len
    ht_mask_lt := fun x => by rw [h.ht_mask]; exact hinv.ht_mask_lt x }

theorem BVWorkspaceOk.of_modifies {cfg : BVWorkspaceCfg} {hdr hdr' : BVHdrState}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords aigWords' : List (BitVec 64)}
    {htSlots htSlots' litsPool litsPool' : List (BitVec 32)} {S : List HdrField}
    (hok : BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool)
    (hfr : Modifies S hdr hdr')
    (haig' : aigWords'.length = cfg.aig_cap) (hht' : htSlots'.length = cfg.ht_slots)
    (hlits' : litsPool'.length = cfg.lits_cap)
    (hsub : S ⊆ [.aig_len, .lits_len, .oom] := by decide) :
    BVWorkspaceOk cfg hdr' atomBases sliceOffs aigWords' htSlots' litsPool' :=
  have h := hfr.mono hsub
  { hok with
    hdr_wb := h.work_base.trans hok.hdr_wb
    hdr_we := h.work_end.trans hok.hdr_we
    hdr_ab := h.atom_base_ptr.trans hok.hdr_ab
    hdr_so := h.slice_off_ptr.trans hok.hdr_so
    hdr_aig := h.aig_ptr.trans hok.hdr_aig
    hdr_ht := h.ht_ptr.trans hok.hdr_ht
    hdr_lits := h.lits_ptr.trans hok.hdr_lits
    hdr_nv := h.n_vars.trans hok.hdr_nv
    hdr_nn := h.n_nodes.trans hok.hdr_nn
    hdr_acap := h.aig_cap.trans hok.hdr_acap
    hdr_htmask := h.ht_mask.trans hok.hdr_htmask
    hdr_lcap := h.lits_cap.trans hok.hdr_lcap
    aig_len_eq := haig'
    ht_len := hht'
    lits_len := hlits' }

theorem BVWorkspaceOk.of_modifies_aigInv {cfg : BVWorkspaceCfg} {hdr hdr' : BVHdrState} {g' : Aig}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords aigWords' : List (BitVec 64)}
    {htSlots htSlots' litsPool litsPool' : List (BitVec 32)} {S : List HdrField}
    (hok : BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool)
    (hfr : Modifies S hdr hdr') (haig' : AigInv hdr' g' aigWords' htSlots')
    (hlp : litsPool'.length = litsPool.length)
    (hsub : S ⊆ [.aig_len, .lits_len, .oom] := by decide) :
    BVWorkspaceOk cfg hdr' atomBases sliceOffs aigWords' htSlots' litsPool' :=
  have h := hfr.mono hsub
  hok.of_modifies hfr
    (by rw [← haig'.aig_cap_eq, h.aig_cap, hok.hdr_acap, BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by have := hok.acap_lt; omega))
    (by rw [haig'.ht_len, h.ht_mask, hok.hdr_htmask, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by have := hok.ht_lt; omega)]
        have := hok.ht_pos; omega)
    (hlp.trans hok.lits_len)
    hsub

theorem BVWorkspaceOk.of_aigFrame {cfg : BVWorkspaceCfg} {hdr hdr' : BVHdrState}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords aigWords' : List (BitVec 64)}
    {htSlots htSlots' litsPool : List (BitVec 32)}
    (hok : BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool)
    (hfr : hdr.AigFrame hdr')
    (haig' : aigWords'.length = cfg.aig_cap) (hht' : htSlots'.length = cfg.ht_slots) :
    BVWorkspaceOk cfg hdr' atomBases sliceOffs aigWords' htSlots' litsPool :=
  hok.of_modifies hfr haig' hht' hok.lits_len

theorem litsSlice_length {litsPool : List (BitVec 32)} {off w : Nat}
    (hle : off + w ≤ litsPool.length) :
    (litsSlice litsPool off w).length = w := by
  unfold litsSlice
  simp only [List.length_map, List.length_take, List.length_drop]
  omega

theorem litsSlice_getD {litsPool : List (BitVec 32)} {off w j : Nat}
    (hle : off + w ≤ litsPool.length) (hj : j < w) :
    (litsSlice litsPool off w).getD j 0 = UInt32.ofBitVec (litsPool.getD (off + j) 0#32) := by
  unfold litsSlice
  have h1 : j < ((litsPool.drop off).take w).length := by
    simp only [List.length_take, List.length_drop]; omega
  have h2 : off + j < litsPool.length := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take,
    List.getElem?_drop, hj, ↓reduceIte, List.getElem?_eq_getElem h2, Option.map_some,
    Option.getD_some]

theorem NodeDenotes.extend_aig {bs : List UInt8} {nodes : BinTree ProgNode} {g g' : Aig}
    {sliceOffs litsPool : List (BitVec 32)} {litsLen i : Nat}
    (hext : g ≤ g') (hlits : litsLen ≤ litsPool.length)
    (h : NodeDenotes bs nodes g sliceOffs litsPool litsLen i) :
    NodeDenotes bs nodes g' sliceOffs litsPool litsLen i := by
  have hsz : g.A + 1 + g.nodes.size ≤ g'.A + 1 + g'.nodes.size := by
    have := hext.1; have := hext.2.1; omega
  unfold NodeDenotes at h ⊢
  cases hnd : nodes.get? i with
  | none => rw [hnd] at h; exact h
  | some nd =>
    rw [hnd] at h
    cases nd with
    | bv w e =>
      obtain ⟨hle, hbd, hsd⟩ := h
      refine ⟨hle, fun j hj => Nat.lt_of_lt_of_le (hbd j hj) hsz, fun assign => ?_⟩
      refine SliceDenotes.extend hext (fun l hl => ?_) (hsd assign)
      unfold litsSlice at hl
      rw [List.mem_map] at hl
      obtain ⟨bv, hbv, rfl⟩ := hl
      rw [List.mem_iff_getElem] at hbv
      obtain ⟨j, hj_len, rfl⟩ := hbv
      have hj_w : j < w := by simp at hj_len; omega
      let off := (sliceOffs.getD i 0#32).toNat
      have hj_p : off + j < litsPool.length := by omega
      have hget : ((litsPool.drop off).take w)[j]'hj_len = litsPool.getD (off + j) 0#32 := by
        simp only [List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hj_p, Option.getD_some]
      change (((litsPool.drop off).take w)[j]'hj_len >>> 1).toNat < _
      rw [hget]
      exact hbd j hj_w
    | bool e =>
      obtain ⟨hbd, hev⟩ := h
      refine ⟨Nat.lt_of_lt_of_le hbd hsz, fun assign => ?_⟩
      rw [Aig.evalLit_extend_node (l := UInt32.ofBitVec (sliceOffs.getD i 0#32)) hext hbd]
      exact hev assign

theorem NodeDenotes.extend_lits {bs : List UInt8} {nodes : BinTree ProgNode} {g : Aig}
    {sliceOffs litsPool litsPool' : List (BitVec 32)} {litsLen litsLen' i : Nat}
    (hlen : litsLen ≤ litsLen') (hpl : litsLen ≤ litsPool.length)
    (hpl' : litsLen' ≤ litsPool'.length)
    (hagree : ∀ p < litsLen, litsPool'.getD p 0#32 = litsPool.getD p 0#32)
    (h : NodeDenotes bs nodes g sliceOffs litsPool litsLen i) :
    NodeDenotes bs nodes g sliceOffs litsPool' litsLen' i := by
  unfold NodeDenotes at h ⊢
  cases hnd : nodes.get? i with
  | none => rw [hnd] at h; exact h
  | some nd =>
    rw [hnd] at h
    cases nd with
    | bv w e =>
      obtain ⟨hle, hbd, hsd⟩ := h
      let off := (sliceOffs.getD i 0#32).toNat
      have hslice : litsSlice litsPool' off w = litsSlice litsPool off w := by
        apply List.ext_getElem
        · rw [litsSlice_length (by omega), litsSlice_length (by omega)]
        · intro j hj1 hj2
          have hjw : j < w := by rw [litsSlice_length (by omega)] at hj1; exact hj1
          have h1 := litsSlice_getD (litsPool := litsPool') (off := off) (by omega) hjw
          have h2 := litsSlice_getD (litsPool := litsPool) (off := off) (by omega) hjw
          have hg1 : (litsSlice litsPool' off w)[j]'hj1 =
              (litsSlice litsPool' off w).getD j 0 := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1, Option.getD_some]
          have hg2 : (litsSlice litsPool off w)[j]'hj2 =
              (litsSlice litsPool off w).getD j 0 := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2, Option.getD_some]
          rw [hg1, hg2, h1, h2, hagree _ (by omega)]
      refine ⟨by omega, fun j hj => ?_, fun assign => ?_⟩
      · rw [hagree _ (by omega)]; exact hbd j hj
      · rw [hslice]; exact hsd assign
    | bool e => exact h

theorem NodeDenotes.extend_slice {bs : List UInt8} {nodes : BinTree ProgNode} {g : Aig}
    {sliceOffs sliceOffs' litsPool : List (BitVec 32)} {litsLen i : Nat}
    (hagree : sliceOffs'.getD i 0#32 = sliceOffs.getD i 0#32)
    (h : NodeDenotes bs nodes g sliceOffs litsPool litsLen i) :
    NodeDenotes bs nodes g sliceOffs' litsPool litsLen i := by
  unfold NodeDenotes at h ⊢
  cases hnd : nodes.get? i with
  | none => rw [hnd] at h; exact h
  | some nd =>
    rw [hnd] at h
    cases nd with
    | bv w e => simpa only [hagree] using h
    | bool e => simpa only [hagree] using h

private theorem foldl_cnf_clauses_list (cls : List (CNF.Clause Nat)) (init : CNF Nat) :
    (cls.foldl CNF.add init).clauses.toList = init.clauses.toList ++ cls := by
  induction cls generalizing init with
  | nil => simp
  | cons cl cls ih => simp [CNF.add, ih]

/-- `ValidDimacsCnf` directly from the dynamic `max_var < dimacsBound` and `clauses.size <
dimacsBound` checks performed in `bv_dimacs_write` (even when `g.nodes.size = bvMaxGates`). -/
theorem validDimacs_tseitin_of_counts {g : Aig} (marks : Array Bool) {root : UInt32}
    (hvar : cnfMaxVar (tseitin g marks root) < dimacsBound)
    (hcls : (tseitin g marks root).clauses.size < dimacsBound) :
    ValidDimacsCnf (tseitin g marks root) := by
  refine ⟨hvar, hcls, ?_⟩
  unfold tseitin
  by_cases h0 : root == 0
  · simp only [h0, ↓reduceIte]
    intro cl hcl l hl
    simp only [CNF.add, CNF.empty, Array.toList_push, List.nil_append,
      List.mem_singleton] at hcl
    subst hcl
    simp at hl
  · simp only [h0, Bool.false_eq_true, ↓reduceIte]
    intro cl hcl l hl
    have hlist : (((tseitinClauses g marks).foldl CNF.add CNF.empty).add
        (CNF.Clause.ofLiterals [litToDimacs root])).clauses.toList =
        tseitinClauses g marks ++ [CNF.Clause.ofLiterals [litToDimacs root]] := by
      simp [CNF.add, CNF.empty, foldl_cnf_clauses_list]
    rw [hlist, List.mem_append] at hcl
    rcases hcl with hcl | hcl
    · unfold tseitinClauses at hcl
      rw [List.mem_flatMap] at hcl
      rcases hcl with ⟨i, hi_mem, hcl_i⟩
      rw [List.mem_range] at hi_mem
      simp only [hi_mem, ↓reduceDIte] at hcl_i
      split at hcl_i
      · unfold gateClauses at hcl_i
        cases hd : detectIte g i hi_mem with
        | none =>
          rw [hd] at hcl_i
          unfold andClauses at hcl_i
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl_i
          rcases hcl_i with rfl | rfl | rfl <;>
            simp only [CNF.Clause.literals_ofLiterals, List.mem_cons, List.not_mem_nil,
              or_false] at hl <;>
            rcases hl with rfl | rfl | rfl <;>
            simp [litToDimacs]
        | some ctf =>
          rcases ctf with ⟨c, t, f⟩
          rw [hd] at hcl_i
          unfold iteClauses at hcl_i
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl_i
          rcases hcl_i with rfl | rfl | rfl | rfl <;>
            simp only [CNF.Clause.literals_ofLiterals, List.mem_cons, List.not_mem_nil,
              or_false] at hl <;>
            rcases hl with rfl | rfl | rfl <;>
            simp [litToDimacs]
      · cases hcl_i
    · rw [List.mem_singleton] at hcl
      subst hcl
      simp only [CNF.Clause.literals_ofLiterals, List.mem_singleton] at hl
      subst hl
      simp [litToDimacs]

/-- End-to-end semantic UNSAT bridge: if `root` denotes `prog` in `g` and `g.evalLit ρ root = false`
for every `ρ`, then every `prog'` parsed from `progBytes` satisfies `prog'.Unsat`. -/
theorem prog_unsat_of_root_false {progBytes : List UInt8} {vars : BinTree VarEntry}
    {cwords : BinTree Nat} {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {g : Aig}
    {sliceOffs litsPool : List (BitVec 32)} {litsLen : Nat}
    (hp : ParsedBVP1 progBytes vars cwords nodes prog)
    (hroot : NodeDenotes progBytes nodes g sliceOffs litsPool litsLen (u32At progBytes 5))
    (hfalse : ∀ ρ : Nat → Bool,
      g.evalLit ρ (UInt32.ofBitVec (sliceOffs.getD (u32At progBytes 5) 0#32)) = false) :
    ∀ prog' : BVLogicalExpr, BVProg.parse progBytes = some prog' → prog'.Unsat := by
  intro prog' hp'
  rw [hp.parse_eq] at hp'
  injection hp' with heq
  subst heq
  unfold NodeDenotes at hroot
  rw [hp.root_get] at hroot
  intro assign
  rw [← hroot.2 assign]
  exact hfalse (atomAssign progBytes assign)

/-- End-to-end Tseitin-to-`BVLogicalExpr.Unsat` bridge composing `parseDimacs_encodeDimacs`,
`tseitin_sound`, and `prog_unsat_of_root_false`. -/
theorem prog_unsat_of_dimacs_unsat {progBytes : List UInt8} {vars : BinTree VarEntry}
    {cwords : BinTree Nat} {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {g : Aig}
    {sliceOffs litsPool : List (BitVec 32)} {litsLen : Nat} {marks : Array Bool}
    (hwf : g.Wf)
    (hp : ParsedBVP1 progBytes vars cwords nodes prog)
    (hroot : NodeDenotes progBytes nodes g sliceOffs litsPool litsLen (u32At progBytes 5))
    (hvalid : ValidDimacsCnf (tseitin g marks
      (UInt32.ofBitVec (sliceOffs.getD (u32At progBytes 5) 0#32))))
    (hkissat : ∃ cnf : CNF Nat,
      parseDimacs (encodeDimacs (tseitin g marks
        (UInt32.ofBitVec (sliceOffs.getD (u32At progBytes 5) 0#32)))) = some cnf ∧ cnf.Unsat) :
    ∀ prog' : BVLogicalExpr, BVProg.parse progBytes = some prog' → prog'.Unsat := by
  obtain ⟨cnf, hparse, hunsat⟩ := hkissat
  rw [parseDimacs_encodeDimacs hvalid] at hparse
  injection hparse with heq
  subst heq
  exact prog_unsat_of_root_false hp hroot (tseitin_sound g hwf marks _ hunsat)

end

end LeanQbe.T.Examples.Bitblast.Proof
