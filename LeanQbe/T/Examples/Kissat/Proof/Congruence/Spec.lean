/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Src.Congruence
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Congruence` (`32` Functions)

Single source of truth for all `32` functions in `Src.Congruence.fns` on flat `CanonicalEnv`:
- `deps` (`Arena.Spec ++ Clause.Spec ++ Limits.Spec ++ Watch.Spec`)
- Unified pure gate (`CongGateAt`, `CongGateSeqOk`), hash-table (`CongHtInv`), dynamic
  occurrence worklist (`CongCtrlLayout`, `CongQueueCtx`), pair-sort (`CongPairsOk`), and
  conditional-ITE (`SortedRange64`, `CondBinElemOk`, `CondEqElemOk`, `CongMemNoWks3`) defs
- `specs : List SpecEntry` aligned 1:1 with `Src.Congruence.fns`, plus `specs_sigs`,
  `specs_nodup`, `specs_noExit`, `specs_xfree`, and `has_*` projections.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec

public section

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Congruence
open Kraken.Bedrock2.Test

/-! ## 1. Dependencies & Shared Congruence Predicates -/

/-- Exact external dependencies required by `Src.Congruence`. -/
@[expose] def deps : List SpecEntry :=
  Arena.Spec.specs ++ Clause.Spec.specs ++ Limits.Spec.specs ++ Watch.Spec.specs

/-- Boolean XOR sum of literals in `xs` under assignment `α`. -/
@[expose] def xorEvalList (α : Nat → Bool) (xs : List Nat) : Bool :=
  xs.foldr (fun x acc => evalLitVal α x != acc) false

/-- Semantic multi-input XOR gate definition: `g ↔ (xs[0] ⊕ xs[1] ⊕ ...)` in every model. -/
@[expose] def XorListGateDef (f : CNF Nat) (g : Nat) (xs : List Nat) : Prop :=
  ∀ α : Nat → Bool, f.Sat α → evalLitVal α g = xorEvalList α xs

/-- Maximum AND gate arity (`congruenceandarity = 1,000,000`). -/
@[expose] def congAndArityMax : Nat := 1000000

/-- Maximum dynamic power-of-2 `occ_bkt` (`2^20 = 1,048,576`). -/
@[expose] def congOccBktMax : Nat := 1048576

/-- Maximum dynamic congruence hash-table bucket count (`1,048,576`). -/
@[expose] def congHashMaxSz : Nat := 1048576

/-- Decoded arity of a gate meta word: 28-bit for `tag = 3` (wide AND), 8-bit otherwise. -/
@[expose] def congGateArity (mword : BitVec 32) : Nat :=
  if (mword >>> 28) = 3#32 then (mword &&& 0x0FFFFFFF#32).toNat
  else (mword &&& 0xFF#32).toNat

/-- Valid extracted gate parameterized by maximum AND arity `maxA ≤ 1,000,000`. -/
@[expose] def CongGateAt (maxA : Nat) (F_cur : List (List Nat)) (cur_vars : Nat)
    (scr : List (BitVec 32)) (g_len g : Nat) : Prop :=
  ∃ (lhs mword : BitVec 32),
    scr[g]? = some lhs ∧ scr[g + 1]? = some mword ∧
    lhs.toNat < 2 * cur_vars ∧
    let tag := (mword >>> 28).toNat
    let arity := congGateArity mword
    g + 2 + arity ≤ g_len ∧ arity ≤ cur_vars ∧ arity ≤ maxA ∧
    (∀ k < arity, ∃ r : BitVec 32, scr[g + 2 + k]? = some r ∧ r.toNat < 2 * cur_vars) ∧
    (((tag = 0 ∧ 2 ≤ arity ∧ arity ≤ 64 ∨ tag = 3 ∧ 65 ≤ arity) ∧
        AndGateDef (cnfOfClauses F_cur) lhs.toNat
          (((scr.drop (g + 2)).take arity).map BitVec.toNat)) ∨
     (tag = 1 ∧ 2 ≤ arity ∧ arity ≤ 4 ∧
        XorListGateDef (cnfOfClauses F_cur) lhs.toNat
          (((scr.drop (g + 2)).take arity).map BitVec.toNat)) ∨
     (tag = 2 ∧ arity = 3 ∧
        IteGateDef (cnfOfClauses F_cur) lhs.toNat
          (scr[g + 2]?.getD 0#32).toNat (scr[g + 3]?.getD 0#32).toNat
          (scr[g + 4]?.getD 0#32).toNat))

/-- Contiguous sequence of valid `CongGateAt maxA` gates in `scr[g ..< g_len)`. -/
inductive CongGateSeqOk (maxA : Nat) (F_cur : List (List Nat)) (cur_vars : Nat)
    (scr : List (BitVec 32)) (g_len : Nat) : Nat → Prop where
  | done : CongGateSeqOk maxA F_cur cur_vars scr g_len g_len
  | step {g : Nat} (hg : CongGateAt maxA F_cur cur_vars scr g_len g) :
      CongGateSeqOk maxA F_cur cur_vars scr g_len
        (g + 2 + congGateArity (scr[g + 1]?.getD 0#32)) →
      CongGateSeqOk maxA F_cur cur_vars scr g_len g

/-- Every non-empty hash slot in `scr[ht_off ..< ht_off + ht_sz)` points to a valid gate. -/
@[expose] def CongHtInv (maxA : Nat) (F_cur : List (List Nat)) (cur_vars : Nat)
    (scr0 scr : List (BitVec 32)) (g_len ht_off ht_sz : Nat) : Prop :=
  ∀ k < ht_sz,
    let ent := scr[ht_off + k]?.getD 0xFFFFFFFF#32
    ent = 0xFFFFFFFF#32 ∨ CongGateAt maxA F_cur cur_vars scr0 g_len ent.toNat

/-- Dynamic power-of-2 congruence control layout (`occ_bkt = 2^p ≤ 1,048,576`). -/
@[expose] def CongCtrlLayout (c : FullCfg) (scr : List (BitVec 32)) (g_len ctrl_off occ_bkt
    bkt_off inq_off q_off ht_off ht_sz : Nat) : Prop :=
  ctrl_off < c.scratch_cap ∧ ctrl_off + 8 ≤ c.scratch_cap ∧
  g_len ≤ ctrl_off ∧ g_len ≤ 0x01000000 ∧
  scr[ctrl_off]?.getD 0#32 = BitVec.ofNat 32 occ_bkt ∧
  scr[ctrl_off + 1]?.getD 0#32 = BitVec.ofNat 32 bkt_off ∧
  scr[ctrl_off + 2]?.getD 0#32 = BitVec.ofNat 32 inq_off ∧
  scr[ctrl_off + 3]?.getD 0#32 = BitVec.ofNat 32 q_off ∧
  scr[ctrl_off + 6]?.getD 0#32 = BitVec.ofNat 32 ht_off ∧
  scr[ctrl_off + 7]?.getD 0#32 = BitVec.ofNat 32 ht_sz ∧
  0 < occ_bkt ∧ occ_bkt ≤ congOccBktMax ∧ (∃ p : Nat, 1 ≤ p ∧ p ≤ 20 ∧ occ_bkt = 2 ^ p) ∧
  0 < ht_sz ∧
  ctrl_off + 8 ≤ q_off ∧ q_off + occ_bkt ≤ inq_off ∧
  inq_off + occ_bkt ≤ bkt_off ∧ bkt_off + occ_bkt ≤ ht_off ∧
  ht_off + ht_sz ≤ c.scratch_cap ∧
  (scr[ctrl_off + 4]?.getD 0#32).toNat < occ_bkt ∧
  (scr[ctrl_off + 5]?.getD 0#32).toNat ≤ occ_bkt ∧
  (∀ k < (scr[ctrl_off + 5]?.getD 0#32).toNat,
    (scr[q_off + ((scr[ctrl_off + 4]?.getD 0#32).toNat + k) % occ_bkt]?.getD 0#32).toNat <
      occ_bkt)

/-- Queue context passed to `full_cong_enq_var` and `full_cong_eval_gate`. -/
@[expose] def CongQueueCtx (c : FullCfg) (scr : List (BitVec 32))
    (g_len ctrl_off ht_off ht_sz : Nat) : Prop :=
  ctrl_off = c.scratch_cap ∨
  ∃ occ_bkt bkt_off inq_off q_off,
    CongCtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz

/-- Pointwise invariant across `n` adjacent `(u32, u32)` pairs stored in `a[0 ..< 2*n)`. -/
@[expose] def CongPairsOk (P : BitVec 32 → BitVec 32 → Prop) (a : List (BitVec 32))
    (n : Nat) : Prop :=
  ∀ k < n, P (a[2 * k]?.getD 0#32) (a[2 * k + 1]?.getD 0#32)

/-- Max-heap property at node `j` within prefix `hi`. -/
@[expose] def MaxHeapAt (xs : List (BitVec 64)) (hi j : Nat) : Prop :=
  (2 * j + 1 < hi → xs[2 * j + 1]?.getD 0#64 ≤ xs[j]?.getD 0#64) ∧
  (2 * j + 2 < hi → xs[2 * j + 2]?.getD 0#64 ≤ xs[j]?.getD 0#64)

/-- Max-heap range invariant on `[lo, hi)`. -/
@[expose] def MaxHeapRange (xs : List (BitVec 64)) (lo hi : Nat) : Prop :=
  ∀ j, lo ≤ j → j < hi → MaxHeapAt xs hi j

/-- Non-decreasing sortedness of `xs` on `[lo, hi)`. -/
@[expose] def SortedRange64 (xs : List (BitVec 64)) (lo hi : Nat) : Prop :=
  ∀ i j, lo ≤ i → i ≤ j → j < hi → xs[i]?.getD 0#64 ≤ xs[j]?.getD 0#64

/-- Packed `(a, b)` conditional binary pair `(lit ∨ a ∨ b)` with distinct variables. -/
@[expose] def CondBinElemOk (F_cur : List (List Nat)) (cur_vars lit : Nat)
    (w : BitVec 64) : Prop :=
  let a := (w >>> 32).toNat
  let b := (w &&& 0xFFFFFFFF#64).toNat
  a < 2 * cur_vars ∧ b < 2 * cur_vars ∧
  a / 2 ≠ b / 2 ∧ a / 2 ≠ lit / 2 ∧ b / 2 ≠ lit / 2 ∧
  (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, a, b])

/-- Packed `(lhs, rhs)` conditional equivalence `¬lit → (lhs ↔ rhs)` with distinct vars. -/
@[expose] def CondEqElemOk (F_cur : List (List Nat)) (cur_vars lit : Nat)
    (w : BitVec 64) : Prop :=
  let lhs := (w >>> 32).toNat
  let rhs := (w &&& 0xFFFFFFFF#64).toNat
  lhs < 2 * cur_vars ∧ rhs < 2 * cur_vars ∧
  lhs / 2 ≠ rhs / 2 ∧ lhs / 2 ≠ lit / 2 ∧ rhs / 2 ≠ lit / 2 ∧
  (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, lhs, litNeg rhs]) ∧
  (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, litNeg lhs, rhs])

/-- `tarjan_mark` and `tarjan_reach` portion of scratch workspace arrays. -/
@[expose] def FullScrWksArrsNo3 (c : FullCfg) (sc : FullScratch) : Mem 64 → Prop :=
  array (t := i32) c.pTarjanMark sc.tarjan_mark ⋆
  array (t := i32) c.pTarjanReach sc.tarjan_reach

/-- Scratch arrays excluding the 3 `u64`-aliased work arrays (`wsort`, `work_stk1/2`). -/
@[expose] def FullScratchArraysNo3 (c : FullCfg) (sc : FullScratch) : Mem 64 → Prop :=
  FullScrByteArrs c sc ⋆ FullScrU32A c sc ⋆ FullScrWksArrsNo3 c sc ⋆
    FullScrMetaArrs c sc ⋆ FullScrDynArrs c sc

/-- `FullMem` footprint excluding `wsort`, `work_stk1`, and `work_stk2`. -/
@[expose] def FullMemNoWks3 (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  FullCoreArrays c s.core ⋆ FullScratchArraysNo3 c s.scratch ⋆ c.pad

/-! ## 2. Canonical Per-Function `Spec` Contracts (`32` Functions) -/

/-- **1 (`full_cong_find`)**: union-find root compression preserving `FullCongReprInv`. -/
abbrev fullCongFindSpec : Spec [i64, i32] [i32] :=
  Proof.Spec.fullCongFindSpec

/-- **2 (`full_cong_merge`)**: merges equivalence classes of `a` and `b` via binary clauses. -/
abbrev fullCongMergeSpec : Spec [i64, i32, i32] [.bool] :=
  Proof.Spec.fullCongMergeSpec

/-- **3 (`full_cong_mark_trail`)**: marks newly pushed trail literals/reprs in `tarjan_mark`. -/
@[expose] def fullCongMarkTrailSpec : Spec [i64, i64, i32] [] :=
  fun (h, _prev_te, _ep, ()) m Q _ =>
    ∃ (c : FullCfg) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      (FullMem c s ⋆ R) m ∧
      ∀ repr' tmk' m',
        let s' : FullState :=
          { s with
            core := { s.core with repr := repr' }
            scratch := { s.scratch with tarjan_mark := tmk' } }
        s'.LengthsOk c →
        FullCongReprInv F_cur (2 * s.core.cur_vars) repr' →
        (FullMem c s' ⋆ R) m' → Q () m'

/-- **4 (`full_cong_unit_fold`)**: propagates an entailed literal under congruence. -/
@[expose] def fullCongUnitFoldSpec : Spec [i64, i32, i32] [i64] :=
  fun (h, lit, _next_ep, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
      s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      lit.toNat < 2 * s.core.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
        s'.core.cur_level = 0 → s'.core.dense_mode ≠ 0#64 →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
        s'.core.tmp = s.core.tmp → s'.scratch.scratch_buf = s.scratch.scratch_buf →
        FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
        (r = 2#64 → s'.core.inconsistent ≠ 0#64 ∧ F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- **5 (`full_cong_equiv_fold`)**: folds an entailed equivalence `a ↔ b`. -/
@[expose] def fullCongEquivFoldSpec : Spec [i64, i32, i32, i32] [i64] :=
  fun (h, a, b, _next_ep, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
      s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      a.toNat < 2 * s.core.cur_vars ∧ b.toNat < 2 * s.core.cur_vars ∧
      LitEquiv (cnfOfClauses F_cur) a.toNat b.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
        s'.core.cur_level = 0 → s'.core.dense_mode ≠ 0#64 →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
        s'.core.tmp = s.core.tmp → s'.scratch.scratch_buf = s.scratch.scratch_buf →
        FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
        (r = 2#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- **6 (`full_cong_emit_xor`)**: emits normalized 2-input XOR gate record. -/
@[expose] def fullCongEmitXorSpec : Spec [i64, i64, i32, i32, i32] [i64] :=
  fun (scr_ptr, g_len, x0, x1, x2, ()) m Q _ =>
    ∃ (maxA : Nat) (F_cur : List (List Nat)) (cur_vars : Nat) (scr : List (BitVec 32))
      (R : Mem 64 → Prop),
      2 ≤ maxA ∧ maxA ≤ 64 ∧
      x0.toNat < 2 * cur_vars ∧ x1.toNat < 2 * cur_vars ∧ x2.toNat < 2 * cur_vars ∧
      2 ≤ cur_vars ∧ g_len.toNat + 4 ≤ scr.length ∧ scr.length < 2 ^ 32 ∧
      XorGateDef (cnfOfClauses F_cur) (litNeg x0.toNat) x1.toNat x2.toNat ∧
      CongGateSeqOk maxA F_cur cur_vars scr g_len.toNat 0 ∧
      (array (t := i32) scr_ptr scr ⋆ R) m ∧
      ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
        scr'.length = scr.length →
        (∀ idx < g_len.toNat, scr'[idx]? = scr[idx]?) →
        CongGateSeqOk maxA F_cur cur_vars scr' (g_len.toNat + 4) 0 →
        (array (t := i32) scr_ptr scr' ⋆ R) m' → Q (g_len + 4#64, ()) m'

/-- **7 (`full_cong_has_clause_k`)**: checks existence of clause covering `tmp[0 ..< k)`. -/
@[expose] def fullCongHasClauseKSpec : Spec [i64, i32] [.bool] := fun (h, k, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧
    3 ≤ k.toNat ∧ k.toNat ≤ 5 ∧ k.toNat ≤ s.core.cur_vars ∧
    (∀ i < k.toNat, (s.core.tmp[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (∀ i j, i < j → j < k.toNat →
      (s.core.tmp[i]?.getD 0#32).toNat / 2 ≠ (s.core.tmp[j]?.getD 0#32).toNat / 2) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c →
      { s'.core with lit_mark := s.core.lit_mark } = s.core →
      s'.scratch = s.scratch →
      FullLitMarksClear c s' →
      (ok = true → (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((List.range k.toNat).map fun i => (s.core.tmp[i]?.getD 0#32).toNat))) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- **8 (`full_cong_emit_xor4`)**: emits sorted 4-literal / 3-input XOR gate record. -/
@[expose] def fullCongEmitXor4Spec : Spec [i64, i64, i32, i32, i32, i32] [i64] :=
  fun (scr_ptr, g_len, x0, x1, x2, x3, ()) m Q _ =>
    ∃ (maxA : Nat) (F_cur : List (List Nat)) (cur_vars : Nat) (scr : List (BitVec 32))
      (R : Mem 64 → Prop),
      3 ≤ maxA ∧ maxA ≤ 64 ∧
      x0.toNat < 2 * cur_vars ∧ x1.toNat < 2 * cur_vars ∧
      x2.toNat < 2 * cur_vars ∧ x3.toNat < 2 * cur_vars ∧
      3 ≤ cur_vars ∧ g_len.toNat + 5 ≤ scr.length ∧ scr.length < 2 ^ 32 ∧
      XorListGateDef (cnfOfClauses F_cur) (litNeg x0.toNat) [x1.toNat, x2.toNat, x3.toNat] ∧
      CongGateSeqOk maxA F_cur cur_vars scr g_len.toNat 0 ∧
      (array (t := i32) scr_ptr scr ⋆ R) m ∧
      ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
        scr'.length = scr.length →
        (∀ idx < g_len.toNat, scr'[idx]? = scr[idx]?) →
        CongGateSeqOk maxA F_cur cur_vars scr' (g_len.toNat + 5) 0 →
        (array (t := i32) scr_ptr scr' ⋆ R) m' → Q (g_len + 5#64, ()) m'

/-- **9 (`full_cong_extract_xor_k`)**: extracts all `k` XOR orientations (`3 ≤ k ≤ 5`). -/
@[expose] def fullCongExtractXorKSpec : Spec [i64, i32, i32, i64, i64] [i64] :=
  fun (h, k, neg_p, g_len, g_cap, ()) m Q _ =>
    ∃ (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      4 ≤ maxA ∧ maxA ≤ 64 ∧
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧
      3 ≤ k.toNat ∧ k.toNat ≤ 5 ∧ k.toNat ≤ s.core.cur_vars ∧
      g_len.toNat ≤ g_cap.toNat ∧ g_cap.toNat ≤ c.scratch_cap ∧
      CongGateSeqOk maxA F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (∀ i < k.toNat, (s.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (neg_p &&& 1#32).toNat = (List.range k.toNat).foldl
        (fun acc i => acc ^^^ ((s.scratch.work_stk2[i]?.getD 0#32).toNat % 2)) 0 ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause
        ((List.range k.toNat).map fun i => (s.scratch.work_stk2[i]?.getD 0#32).toNat)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (s' : FullState) (m' : Mem 64),
        s'.LengthsOk c →
        { s'.core with tmp := s.core.tmp, lit_mark := s.core.lit_mark } = s.core →
        { s'.scratch with scratch_buf := s.scratch.scratch_buf } = s.scratch →
        FullLitMarksClear c s' →
        g_len.toNat ≤ ret.toNat → ret.toNat ≤ g_cap.toNat →
        (∀ idx < g_len.toNat, s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) →
        CongGateSeqOk maxA F_cur s.core.cur_vars s'.scratch.scratch_buf ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

/-- **10 (`full_cong_try_xor_ite`)**: extracts 3-var XOR gate from ternary clause `(a, b, cl)`. -/
@[expose] def fullCongTryXorIteSpec : Spec [i64, i32, i32, i32, i64, i64] [i64] :=
  fun (h, a, b, cl, g_len, g_cap, ()) m Q _ =>
    ∃ (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      2 ≤ maxA ∧ maxA ≤ 64 ∧
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧
      a.toNat < 2 * s.core.cur_vars ∧ b.toNat < 2 * s.core.cur_vars ∧
      cl.toNat < 2 * s.core.cur_vars ∧
      a.toNat / 2 ≠ b.toNat / 2 ∧ a.toNat / 2 ≠ cl.toNat / 2 ∧ b.toNat / 2 ≠ cl.toNat / 2 ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat, cl.toNat]) ∧
      g_len.toNat + 5 ≤ g_cap.toNat ∧ g_cap.toNat ≤ c.scratch_cap ∧
      CongGateSeqOk maxA F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        g_len.toNat ≤ ret.toNat → ret.toNat ≤ g_cap.toNat →
        (∀ idx < g_len.toNat, scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        CongGateSeqOk maxA F_cur s.core.cur_vars scr' ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

/-- **11 (`full_cong_count_bins`)**: counts binary watches per literal into `work_stk1`. -/
@[expose] def fullCongCountBinsSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧
    (∀ l < 2 * s.core.cur_vars,
      fullWatchOffCore s.core l + fullWatchSizeCore s.core l ≤ c.wcap) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ ws1' m',
      ws1'.length = 2 * c.max_vars →
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m' →
      Q () m'

/-- **12 (`full_cong_eb_match`)**: matches implied binary `(¬x ∨ l)` or `(¬x ∨ k)`. -/
@[expose] def fullCongEbMatchSpec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, x, l, k, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      x.toNat < 2 * s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
      ∀ ok : Bool,
        (ok = true →
          (cnfOfClauses F_cur).EntailsClause (cnfClause [x.toNat ^^^ 1, l.toNat]) ∨
          (cnfOfClauses F_cur).EntailsClause (cnfClause [x.toNat ^^^ 1, k.toNat])) →
        Q (ok, ()) m

/-- **13 (`full_cong_extract_binaries`)**: expands ternary/binary patterns into binary cls. -/
@[expose] def fullCongExtractBinariesSpec : Spec [i64, i64] [i64] :=
  fun (h, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullDenseInvW c F0 F_cur s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- **14 (`full_cong_find_units_equivs`)**: extracts units and equivalences from binary cls. -/
@[expose] def fullCongFindUnitsEquivsSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
    FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInvW c F0 F_cur s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- **15 (`full_cong_extract_and_clause_fid`)**: `O(D)` marked watch scan emitting wide ANDs. -/
@[expose] def fullCongExtractAndClauseFidSpec : Spec [i64, i32, i64, i64, i64] [i64] :=
  fun (h, usz, g_len, g_cap, _tick_lim, ()) m Q _ =>
    ∃ (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      maxA ≤ congAndArityMax ∧
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
      3 ≤ usz.toNat ∧ usz.toNat - 1 ≤ maxA ∧ usz.toNat ≤ s.core.cur_vars ∧
      g_len.toNat ≤ g_cap.toNat ∧ g_cap.toNat ≤ c.scratch_cap ∧
      CongGateSeqOk maxA F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (∀ j < usz.toNat, (s.scratch.work_stk2[j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (∀ j < usz.toNat, ∀ j2 < usz.toNat, j ≠ j2 →
        (s.scratch.work_stk2[j]?.getD 0#32).toNat ≠
          (s.scratch.work_stk2[j2]?.getD 0#32).toNat) ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause
        ((List.range usz.toNat).map fun j => (s.scratch.work_stk2[j]?.getD 0#32).toNat)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (lm' : List (BitVec 8)) (scr' : List (BitVec 32))
        (rsz' : BitVec 64) (m' : Mem 64),
        let s' : FullState :=
          { s with
            core := { s.core with lit_mark := lm' }
            scratch := { s.scratch with scratch_buf := scr', res_sz := rsz' } }
        FullDenseInvW c F0 F_cur s' →
        g_len.toNat ≤ ret.toNat → ret.toNat ≤ g_cap.toNat →
        (∀ idx < g_len.toNat, scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        CongGateSeqOk maxA F_cur s.core.cur_vars scr' ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

/-- **16 (`full_cong_extract_from_fid`)**: two-pass gate extraction from `g_start`. -/
@[expose] def fullCongExtractFromFidSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (h, g_start, g_cap, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
      g_start.toNat ≤ g_cap.toNat ∧ g_cap.toNat ≤ c.scratch_cap ∧
      CongGateSeqOk 64 F_cur s.core.cur_vars s.scratch.scratch_buf g_start.toNat 0 ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (s' : FullState) (m' : Mem 64),
        FullDenseInvW c F0 F_cur s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.core.repr = s.core.repr → s'.core.inconsistent = s.core.inconsistent →
        g_start.toNat ≤ ret.toNat → ret.toNat ≤ g_cap.toNat →
        CongGateSeqOk congAndArityMax F_cur s.core.cur_vars
          s'.scratch.scratch_buf ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

/-- **17 (`full_cong_and_match`)**: `O(ea + ua)` `lit_mark` + `u32` AND matcher. -/
@[expose] def fullCongAndMatchSpec : Spec [i64, i32, i32] [.bool] := fun (h, ent, ua, ()) m Q _ =>
  ∃ (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (scr0 : List (BitVec 32)) (g_len : Nat) (R : Mem 64 → Prop),
    maxA ≤ congAndArityMax ∧ h = c.hdr ∧ s.LengthsOk c ∧
    FullWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
    s.core.cur_level = 0 ∧ FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
    g_len ≤ c.scratch_cap ∧
    (∀ idx < g_len, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
    CongGateAt maxA F_cur s.core.cur_vars scr0 g_len ent.toNat ∧
    ((scr0[ent.toNat + 1]?.getD 0#32 >>> 28) = 0#32 ∨
     (scr0[ent.toNat + 1]?.getD 0#32 >>> 28) = 3#32) ∧
    ua.toNat ≤ s.core.cur_vars ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) repr' lm' m',
      let s' : FullState := { s with core := { s.core with repr := repr', lit_mark := lm' } }
      repr'.length = 2 * c.max_vars →
      lm'.length = 2 * c.max_vars →
      FullLitMarksClear c s' →
      FullCongReprInv F_cur (2 * s.core.cur_vars) repr' →
      (ok = true → 2 ≤ ua.toNat ∧ ua.toNat ≤ congAndArityMax ∧
        ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
          evalLitVal α (scr0[ent.toNat]?.getD 0#32).toNat =
            (List.range ua.toNat).all fun k =>
              evalLitVal α (s.core.tmp[k]?.getD 0#32).toNat) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- **18 (`full_cong_xor_match`)**: matches candidate XOR gate in `scr[ent]` against `tmp`. -/
@[expose] def fullCongXorMatchSpec : Spec [i64, i32, i32] [i32] := fun (h, ent, ua, ()) m Q _ =>
  ∃ (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (scr0 : List (BitVec 32)) (g_len : Nat) (R : Mem 64 → Prop),
    maxA ≤ congAndArityMax ∧
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ s.core.cur_level = 0 ∧
    FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
    2 ≤ s.core.cur_vars ∧ g_len ≤ c.scratch_cap ∧
    (∀ idx < g_len, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
    CongGateAt maxA F_cur s.core.cur_vars scr0 g_len ent.toNat ∧
    (scr0[ent.toNat + 1]?.getD 0#32 >>> 28) = 1#32 ∧
    ua.toNat ≤ s.core.cur_vars ∧
    (∀ k < ua.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ml : BitVec 32) repr' mclr' m',
      let s' : FullState := { s with core := { s.core with repr := repr', min_clr := mclr' } }
      repr'.length = 2 * c.max_vars → mclr'.length = c.max_vars →
      FullCongReprInv F_cur (2 * s.core.cur_vars) repr' →
      (ml ≠ 0xFFFFFFFF#32 → 2 ≤ ua.toNat ∧ ua.toNat ≤ 4 ∧
        ml.toNat < 2 * s.core.cur_vars ∧
        ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
          evalLitVal α ml.toNat =
            xorEvalList α ((s.core.tmp.take ua.toNat).map BitVec.toNat)) →
      (FullMem c s' ⋆ R) m' → Q (ml, ()) m'

/-- **19 (`full_cong_enq_var`)**: enqueues occurrence bucket for variable `v`. -/
@[expose] def fullCongEnqVarSpec : Spec [i64, i64, i32] [] := fun (h, ctrl_off, _v, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (g_len ht_off ht_sz : Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧
    CongQueueCtx c s.scratch.scratch_buf g_len ctrl_off.toNat ht_off ht_sz ∧
    (FullMem c s ⋆ R) m ∧
    ∀ scr' m',
      scr'.length = c.scratch_cap →
      CongQueueCtx c scr' g_len ctrl_off.toNat ht_off ht_sz →
      (ctrl_off.toNat = c.scratch_cap → scr' = s.scratch.scratch_buf) →
      (∀ occ_bkt bkt_off inq_off q_off,
        CongCtrlLayout c s.scratch.scratch_buf g_len ctrl_off.toNat occ_bkt bkt_off inq_off
          q_off ht_off ht_sz →
        scr'[ctrl_off.toNat]? = some (BitVec.ofNat 32 occ_bkt) ∧
        scr'[ctrl_off.toNat + 1]? = some (BitVec.ofNat 32 bkt_off) ∧
        scr'[ctrl_off.toNat + 2]? = some (BitVec.ofNat 32 inq_off) ∧
        scr'[ctrl_off.toNat + 3]? = some (BitVec.ofNat 32 q_off) ∧
        scr'[ctrl_off.toNat + 4]? = s.scratch.scratch_buf[ctrl_off.toNat + 4]? ∧
        scr'[ctrl_off.toNat + 6]? = some (BitVec.ofNat 32 ht_off) ∧
        scr'[ctrl_off.toNat + 7]? = some (BitVec.ofNat 32 ht_sz) ∧
        (∀ idx, idx ≠ ctrl_off.toNat + 5 →
          ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
          ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) →
          scr'[idx]? = s.scratch.scratch_buf[idx]?)) →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
      Q () m'

/-- **20 (`full_cong_eval_gate`)**: re-evaluates and hashes gate at `g` under `repr`. -/
@[expose] def fullCongEvalGateSpec : Spec [i64, i64, i64, i64, i32, i64] [i64] :=
  fun (h, g, ht_off, ht_sz, _next_ep, ctrl_off, ()) m Q _ =>
    ∃ (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (scr0 : List (BitVec 32)) (g_len : Nat) (R : Mem 64 → Prop),
      maxA ≤ congAndArityMax ∧ h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      0 < ht_sz.toNat ∧ ht_sz.toNat < 2 ^ 30 ∧
      g.toNat < g_len ∧ g_len ≤ ht_off.toNat ∧ ht_off.toNat + ht_sz.toNat ≤ c.scratch_cap ∧
      (∀ idx < g_len, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
      CongGateAt maxA F_cur s.core.cur_vars scr0 g_len g.toNat ∧
      CongHtInv maxA F_cur s.core.cur_vars scr0 s.scratch.scratch_buf
        g_len ht_off.toNat ht_sz.toNat ∧
      CongQueueCtx c s.scratch.scratch_buf g_len ctrl_off.toNat ht_off.toNat ht_sz.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) s' m',
        FullDenseInvW c F0 F_cur s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
        FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
        (∀ idx < g_len, s'.scratch.scratch_buf[idx]? = scr0[idx]?) →
        CongHtInv maxA F_cur s'.core.cur_vars scr0 s'.scratch.scratch_buf
          g_len ht_off.toNat ht_sz.toNat →
        CongQueueCtx c s'.scratch.scratch_buf g_len ctrl_off.toNat ht_off.toNat ht_sz.toNat →
        ((r &&& 2#64) = 0#64 →
          (∀ idx < c.scratch_cap, idx < ht_off.toNat →
            (ctrl_off.toNat = c.scratch_cap →
              s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) ∧
            (∀ occ_bkt bkt_off inq_off q_off,
              CongCtrlLayout c s.scratch.scratch_buf g_len ctrl_off.toNat occ_bkt bkt_off
                inq_off q_off ht_off.toNat ht_sz.toNat →
              idx ≠ ctrl_off.toNat + 5 →
              ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
              ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) →
              s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?))) →
        ((r &&& 2#64) ≠ 0#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- **21 (`full_cong_worklist`)**: congruence worklist over 3-word occurrence lists & HT. -/
@[expose] def fullCongWorklistSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (h, g_len, ctrl_off, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (scr0 : List (BitVec 32)) (occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      0 < g_len.toNat ∧ ht_sz ≤ congHashMaxSz ∧
      CongCtrlLayout c s.scratch.scratch_buf g_len.toNat ctrl_off.toNat occ_bkt bkt_off
        inq_off q_off ht_off ht_sz ∧
      CongGateSeqOk congAndArityMax F_cur s.core.cur_vars scr0 g_len.toNat 0 ∧
      (∀ idx < g_len.toNat, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
      CongHtInv congAndArityMax F_cur s.core.cur_vars scr0 s.scratch.scratch_buf
        g_len.toNat ht_off ht_sz ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullDenseInvW c F0 F_cur s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- **22 (`full_cong_sift_pairs_fid`)**: max-heap sift for `(u32, u32)` pairs. -/
@[expose] def fullCongSiftPairsFidSpec : Spec [i64, i64, i64] [] :=
  fun (ap, start, n, ()) m Q _ =>
    ∃ (P : BitVec 32 → BitVec 32 → Prop) (a : List (BitVec 32)) (R : Mem 64 → Prop),
      start.toNat < n.toNat ∧ 2 * n.toNat ≤ a.length ∧ a.length < 2 ^ 61 ∧
      CongPairsOk P a n.toNat ∧ (array (t := i32) ap a ⋆ R) m ∧
      ∀ a' m',
        a'.length = a.length → CongPairsOk P a' n.toNat →
        (∀ idx, 2 * n.toNat ≤ idx → a'[idx]? = a[idx]?) →
        (array (t := i32) ap a' ⋆ R) m' → Q () m'

/-- **23 (`full_cong_sort_pairs_fid`)**: in-place heapsort of `(u32, u32)` pairs. -/
@[expose] def fullCongSortPairsFidSpec : Spec [i64, i64] [] := fun (ap, n, ()) m Q _ =>
  ∃ (P : BitVec 32 → BitVec 32 → Prop) (a : List (BitVec 32)) (R : Mem 64 → Prop),
    2 * n.toNat ≤ a.length ∧ a.length < 2 ^ 61 ∧
    CongPairsOk P a n.toNat ∧ (array (t := i32) ap a ⋆ R) m ∧
    ∀ a' m',
      a'.length = a.length → CongPairsOk P a' n.toNat →
      (∀ idx, 2 * n.toNat ≤ idx → a'[idx]? = a[idx]?) →
      (array (t := i32) ap a' ⋆ R) m' → Q () m'

/-- **24 (`full_cong_fwd_subsume`)**: forward subsumption / self-subsuming strengthening. -/
@[expose] def fullCongFwdSubsumeSpec : Spec [i64, i64] [i64] :=
  fun (h, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullDenseInvW c F0 F_cur s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- **25 (`full_cong_u64_sift_m7`)**: in-place `u64` max-heap sift. -/
@[expose] def fullCongU64SiftM7Spec : Spec [i64, i64, i64] [] :=
  fun (a, start, n, ()) m Q _ =>
    ∃ (xs : List (BitVec 64)) (R : Mem 64 → Prop),
      start.toNat ≤ n.toNat ∧ n.toNat ≤ xs.length ∧ xs.length < 2 ^ 61 ∧
      MaxHeapRange xs (start.toNat + 1) n.toNat ∧
      (array64 a xs ⋆ R) m ∧
      ∀ (xs' : List (BitVec 64)) m',
        xs'.length = xs.length →
        (∀ k, n.toNat ≤ k → k < xs.length → xs'[k]? = xs[k]?) →
        (∀ k < n.toNat, ∃ j < n.toNat, xs'[k]? = xs[j]?) →
        MaxHeapRange xs' start.toNat n.toNat →
        (array64 a xs' ⋆ R) m' → Q () m'

/-- **26 (`full_cong_u64_sort_m7`)**: in-place `u64` heapsort on `a[0 ..< n)`. -/
@[expose] def fullCongU64SortM7Spec : Spec [i64, i64] [] := fun (a, n, ()) m Q _ =>
  ∃ (xs : List (BitVec 64)) (R : Mem 64 → Prop),
    n.toNat ≤ xs.length ∧ xs.length < 2 ^ 61 ∧
    (array64 a xs ⋆ R) m ∧
    ∀ (xs' : List (BitVec 64)) m',
      xs'.length = xs.length →
      (∀ k, n.toNat ≤ k → k < xs.length → xs'[k]? = xs[k]?) →
      (∀ k < n.toNat, ∃ j < n.toNat, xs'[k]? = xs[j]?) →
      SortedRange64 xs' 0 n.toNat →
      (array64 a xs' ⋆ R) m' → Q () m'

/-- **27 (`full_cong_bsearch_u64_m7`)**: sorted `u64` binary search on `[lo, hi)`. -/
@[expose] def fullCongBsearchU64M7Spec : Spec [i64, i64, i64, i64] [.bool] :=
  fun (a, lo, hi, key, ()) m Q _ =>
    ∃ (xs : List (BitVec 64)) (R : Mem 64 → Prop),
      lo.toNat ≤ hi.toNat ∧ hi.toNat ≤ xs.length ∧ xs.length < 2 ^ 61 ∧
      SortedRange64 xs lo.toNat hi.toNat ∧
      (array64 a xs ⋆ R) m ∧
      ∀ r : Bool,
        (r = true ↔ ∃ idx, lo.toNat ≤ idx ∧ idx < hi.toNat ∧ xs[idx]? = some key) →
        Q (r, ()) m

/-- **28 (`full_cong_copy_condbin_m7`)**: level-0 conditional binary extraction from `sz ≥ 3`. -/
@[expose] def fullCongCopyCondbinM7Spec : Spec [i64, i32, i64, i64] [i64] :=
  fun (h, lit, out, cap, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (out0 : List (BitVec 64)) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧
      lit.toNat < 2 * s.core.cur_vars ∧
      out0.length = cap.toNat ∧ cap.toNat < 2 ^ 61 ∧
      (FullMemNoWks3 c s ⋆ array64 out out0 ⋆ R) m ∧
      ∀ (cnt : BitVec 64) (out' : List (BitVec 64)) m',
        out'.length = cap.toNat →
        cnt.toNat ≤ cap.toNat →
        SortedRange64 out' 0 cnt.toNat →
        (∀ k < cnt.toNat, CondBinElemOk F_cur s.core.cur_vars lit.toNat (out'[k]?.getD 0#64)) →
        (FullMemNoWks3 c s ⋆ array64 out out' ⋆ R) m' → Q (cnt, ()) m'

/-- **29 (`full_cong_extract_condeq_m7`)**: conditional equivalence pair scan. -/
@[expose] def fullCongExtractCondeqM7Spec : Spec [i64, i64, i64, i64] [i64] :=
  fun (cb, m, ceq, cap, ()) mem0 Q _ =>
    ∃ (F_cur : List (List Nat)) (cur_vars lit : Nat)
      (cb_xs ceq0 : List (BitVec 64)) (R : Mem 64 → Prop),
      m.toNat ≤ cb_xs.length ∧ cb_xs.length < 2 ^ 61 ∧
      SortedRange64 cb_xs 0 m.toNat ∧
      (∀ k < m.toNat, CondBinElemOk F_cur cur_vars lit (cb_xs[k]?.getD 0#64)) ∧
      ceq0.length = cap.toNat ∧ cap.toNat < 2 ^ 61 ∧
      (array64 cb cb_xs ⋆ array64 ceq ceq0 ⋆ R) mem0 ∧
      ∀ (u : BitVec 64) (ceq' : List (BitVec 64)) mem',
        ceq'.length = cap.toNat → u.toNat ≤ cap.toNat →
        (∀ k < u.toNat, CondEqElemOk F_cur cur_vars lit (ceq'[k]?.getD 0#64)) →
        (array64 cb cb_xs ⋆ array64 ceq ceq' ⋆ R) mem' → Q (u, ()) mem'

/-- **30 (`full_cong_merge_condeq_m7`)**: merges opposite-polarity conditional equivs. -/
@[expose] def fullCongMergeCondeqM7Spec : Spec [i64, i32, i64, i64, i32, i32] [i32] :=
  fun (h, cond, pos_n, neg_n, g_len, g_cap, ()) m Q _ =>
    ∃ (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (wk1 wk2 : List (BitVec 64)) (R : Mem 64 → Prop),
      3 ≤ maxA ∧ maxA ≤ 64 ∧
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      3 ≤ s.core.cur_vars ∧ cond.toNat < 2 * s.core.cur_vars ∧
      g_cap.toNat ≤ c.scratch_cap ∧
      pos_n.toNat ≤ wk1.length ∧ neg_n.toNat ≤ wk2.length ∧
      wk1.length < 2 ^ 61 ∧ wk2.length < 2 ^ 61 ∧
      (∀ k < pos_n.toNat,
        CondEqElemOk F_cur s.core.cur_vars (litNeg cond.toNat) (wk1[k]?.getD 0#64)) ∧
      (∀ k < neg_n.toNat,
        CondEqElemOk F_cur s.core.cur_vars cond.toNat (wk2[k]?.getD 0#64)) ∧
      CongGateSeqOk maxA F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (FullMemNoWks3 c s ⋆ array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R) m ∧
      ∀ (ret : BitVec 32) (scr' : List (BitVec 32)) m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (g_len.toNat ≤ g_cap.toNat → g_len.toNat ≤ ret.toNat ∧ ret.toNat ≤ g_cap.toNat) →
        (∀ idx < g_len.toNat, scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        CongGateSeqOk maxA F_cur s.core.cur_vars scr' ret.toNat 0 →
        (FullMemNoWks3 c s' ⋆ array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R) m' →
        Q (ret, ()) m'

/-- **31 (`full_cong_extract_ite_all_m7`)**: global `O(deg log deg)` ITE extraction. -/
@[expose] def fullCongExtractIteAllM7Spec : Spec [i64, i32, i32, i64] [i32] :=
  fun (h, g_len, g_cap, _tick_lim, ()) m Q _ =>
    ∃ (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      3 ≤ maxA ∧ maxA ≤ 64 ∧
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
      g_len.toNat ≤ g_cap.toNat ∧ g_cap.toNat ≤ c.scratch_cap ∧
      CongGateSeqOk maxA F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 32) (s' : FullState) m',
        FullDenseInvW c F0 F_cur s' →
        s'.core = s.core →
        s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
        s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
        s'.scratch.extend_stk = s.scratch.extend_stk →
        s'.scratch.extend_len = s.scratch.extend_len →
        s'.scratch.last_learned = s.scratch.last_learned →
        s'.scratch.ant_sz = s.scratch.ant_sz →
        s'.scratch.res_sz = s.scratch.res_sz →
        g_len.toNat ≤ ret.toNat → ret.toNat ≤ g_cap.toNat →
        (∀ idx < g_len.toNat, s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) →
        CongGateSeqOk maxA F_cur s.core.cur_vars s'.scratch.scratch_buf ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

/-- **32 (`full_congruence_dense`)**: dense-mode ticks-bounded congruence closure. -/
@[expose] def fullCongruenceDenseSpec : Spec [i64, i64] [i64] :=
  fun (h, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullDenseInv c F0 s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.fuel = s.core.fuel → (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ## 3. Canonical `specs` Table, Structural Obligations & `Env.Has` Projections -/

theorem fullCongFindSpec_xfree : fullCongFindSpec.XFree := by xfree
theorem fullCongMergeSpec_xfree : fullCongMergeSpec.XFree := by xfree
theorem fullCongMarkTrailSpec_xfree : fullCongMarkTrailSpec.XFree := by xfree
theorem fullCongUnitFoldSpec_xfree : fullCongUnitFoldSpec.XFree := by xfree
theorem fullCongEquivFoldSpec_xfree : fullCongEquivFoldSpec.XFree := by xfree
theorem fullCongEmitXorSpec_xfree : fullCongEmitXorSpec.XFree := by xfree
theorem fullCongHasClauseKSpec_xfree : fullCongHasClauseKSpec.XFree := by xfree
theorem fullCongEmitXor4Spec_xfree : fullCongEmitXor4Spec.XFree := by xfree
theorem fullCongExtractXorKSpec_xfree : fullCongExtractXorKSpec.XFree := by xfree
theorem fullCongTryXorIteSpec_xfree : fullCongTryXorIteSpec.XFree := by xfree
theorem fullCongCountBinsSpec_xfree : fullCongCountBinsSpec.XFree := by xfree
theorem fullCongEbMatchSpec_xfree : fullCongEbMatchSpec.XFree := by xfree
theorem fullCongExtractBinariesSpec_xfree : fullCongExtractBinariesSpec.XFree := by xfree
theorem fullCongFindUnitsEquivsSpec_xfree : fullCongFindUnitsEquivsSpec.XFree := by xfree
theorem fullCongExtractAndClauseFidSpec_xfree : fullCongExtractAndClauseFidSpec.XFree := by
  xfree
theorem fullCongExtractFromFidSpec_xfree : fullCongExtractFromFidSpec.XFree := by xfree
theorem fullCongAndMatchSpec_xfree : fullCongAndMatchSpec.XFree := by xfree
theorem fullCongXorMatchSpec_xfree : fullCongXorMatchSpec.XFree := by xfree
theorem fullCongEnqVarSpec_xfree : fullCongEnqVarSpec.XFree := by xfree
theorem fullCongEvalGateSpec_xfree : fullCongEvalGateSpec.XFree := by xfree
theorem fullCongWorklistSpec_xfree : fullCongWorklistSpec.XFree := by xfree
theorem fullCongSiftPairsFidSpec_xfree : fullCongSiftPairsFidSpec.XFree := by xfree
theorem fullCongSortPairsFidSpec_xfree : fullCongSortPairsFidSpec.XFree := by xfree
theorem fullCongFwdSubsumeSpec_xfree : fullCongFwdSubsumeSpec.XFree := by xfree
theorem fullCongU64SiftM7Spec_xfree : fullCongU64SiftM7Spec.XFree := by xfree
theorem fullCongU64SortM7Spec_xfree : fullCongU64SortM7Spec.XFree := by xfree
theorem fullCongBsearchU64M7Spec_xfree : fullCongBsearchU64M7Spec.XFree := by xfree
theorem fullCongCopyCondbinM7Spec_xfree : fullCongCopyCondbinM7Spec.XFree := by xfree
theorem fullCongExtractCondeqM7Spec_xfree : fullCongExtractCondeqM7Spec.XFree := by xfree
theorem fullCongMergeCondeqM7Spec_xfree : fullCongMergeCondeqM7Spec.XFree := by xfree
theorem fullCongExtractIteAllM7Spec_xfree : fullCongExtractIteAllM7Spec.XFree := by xfree
theorem fullCongruenceDenseSpec_xfree : fullCongruenceDenseSpec.XFree := by xfree

/-- Canonical `SpecEntry` list matching `Src.Congruence.fns` order 1:1 (`32` functions). -/
@[expose] def specs : List SpecEntry :=
  [ { name := "full_cong_find", as := [i64, i32], rs := [i32],
      spec := fullCongFindSpec, noExit := true }
  , { name := "full_cong_merge", as := [i64, i32, i32], rs := [.bool],
      spec := fullCongMergeSpec, noExit := true }
  , { name := "full_cong_mark_trail", as := [i64, i64, i32], rs := [],
      spec := fullCongMarkTrailSpec, noExit := true }
  , { name := "full_cong_unit_fold", as := [i64, i32, i32], rs := [i64],
      spec := fullCongUnitFoldSpec, noExit := true }
  , { name := "full_cong_equiv_fold", as := [i64, i32, i32, i32], rs := [i64],
      spec := fullCongEquivFoldSpec, noExit := true }
  , { name := "full_cong_emit_xor", as := [i64, i64, i32, i32, i32], rs := [i64],
      spec := fullCongEmitXorSpec, noExit := true }
  , { name := "full_cong_has_clause_k", as := [i64, i32], rs := [.bool],
      spec := fullCongHasClauseKSpec, noExit := true }
  , { name := "full_cong_emit_xor4", as := [i64, i64, i32, i32, i32, i32], rs := [i64],
      spec := fullCongEmitXor4Spec, noExit := true }
  , { name := "full_cong_extract_xor_k", as := [i64, i32, i32, i64, i64], rs := [i64],
      spec := fullCongExtractXorKSpec, noExit := true }
  , { name := "full_cong_try_xor_ite", as := [i64, i32, i32, i32, i64, i64], rs := [i64],
      spec := fullCongTryXorIteSpec, noExit := true }
  , { name := "full_cong_count_bins", as := [i64], rs := [],
      spec := fullCongCountBinsSpec, noExit := true }
  , { name := "full_cong_eb_match", as := [i64, i32, i32, i32], rs := [.bool],
      spec := fullCongEbMatchSpec, noExit := true }
  , { name := "full_cong_extract_binaries", as := [i64, i64], rs := [i64],
      spec := fullCongExtractBinariesSpec, noExit := true }
  , { name := "full_cong_find_units_equivs", as := [i64], rs := [i64],
      spec := fullCongFindUnitsEquivsSpec, noExit := true }
  , { name := "full_cong_extract_and_clause_fid", as := [i64, i32, i64, i64, i64], rs := [i64],
      spec := fullCongExtractAndClauseFidSpec, noExit := true }
  , { name := "full_cong_extract_from_fid", as := [i64, i64, i64, i64], rs := [i64],
      spec := fullCongExtractFromFidSpec, noExit := true }
  , { name := "full_cong_and_match", as := [i64, i32, i32], rs := [.bool],
      spec := fullCongAndMatchSpec, noExit := true }
  , { name := "full_cong_xor_match", as := [i64, i32, i32], rs := [i32],
      spec := fullCongXorMatchSpec, noExit := true }
  , { name := "full_cong_enq_var", as := [i64, i64, i32], rs := [],
      spec := fullCongEnqVarSpec, noExit := true }
  , { name := "full_cong_eval_gate", as := [i64, i64, i64, i64, i32, i64], rs := [i64],
      spec := fullCongEvalGateSpec, noExit := true }
  , { name := "full_cong_worklist", as := [i64, i64, i64, i64], rs := [i64],
      spec := fullCongWorklistSpec, noExit := true }
  , { name := "full_cong_sift_pairs_fid", as := [i64, i64, i64], rs := [],
      spec := fullCongSiftPairsFidSpec, noExit := true }
  , { name := "full_cong_sort_pairs_fid", as := [i64, i64], rs := [],
      spec := fullCongSortPairsFidSpec, noExit := true }
  , { name := "full_cong_fwd_subsume", as := [i64, i64], rs := [i64],
      spec := fullCongFwdSubsumeSpec, noExit := true }
  , { name := "full_cong_u64_sift_m7", as := [i64, i64, i64], rs := [],
      spec := fullCongU64SiftM7Spec, noExit := true }
  , { name := "full_cong_u64_sort_m7", as := [i64, i64], rs := [],
      spec := fullCongU64SortM7Spec, noExit := true }
  , { name := "full_cong_bsearch_u64_m7", as := [i64, i64, i64, i64], rs := [.bool],
      spec := fullCongBsearchU64M7Spec, noExit := true }
  , { name := "full_cong_copy_condbin_m7", as := [i64, i32, i64, i64], rs := [i64],
      spec := fullCongCopyCondbinM7Spec, noExit := true }
  , { name := "full_cong_extract_condeq_m7", as := [i64, i64, i64, i64], rs := [i64],
      spec := fullCongExtractCondeqM7Spec, noExit := true }
  , { name := "full_cong_merge_condeq_m7", as := [i64, i32, i64, i64, i32, i32], rs := [i32],
      spec := fullCongMergeCondeqM7Spec, noExit := true }
  , { name := "full_cong_extract_ite_all_m7", as := [i64, i32, i32, i64], rs := [i32],
      spec := fullCongExtractIteAllM7Spec, noExit := true }
  , { name := "full_congruence_dense", as := [i64, i64], rs := [i64],
      spec := fullCongruenceDenseSpec, noExit := true } ]

theorem specs_sigs : specs.map SpecEntry.sig = Src.Congruence.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : ∀ e ∈ specs, e.noExit = true := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> rfl

theorem specs_xfree : ∀ e ∈ specs, e.spec.XFree := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact fullCongFindSpec_xfree
  · exact fullCongMergeSpec_xfree
  · exact fullCongMarkTrailSpec_xfree
  · exact fullCongUnitFoldSpec_xfree
  · exact fullCongEquivFoldSpec_xfree
  · exact fullCongEmitXorSpec_xfree
  · exact fullCongHasClauseKSpec_xfree
  · exact fullCongEmitXor4Spec_xfree
  · exact fullCongExtractXorKSpec_xfree
  · exact fullCongTryXorIteSpec_xfree
  · exact fullCongCountBinsSpec_xfree
  · exact fullCongEbMatchSpec_xfree
  · exact fullCongExtractBinariesSpec_xfree
  · exact fullCongFindUnitsEquivsSpec_xfree
  · exact fullCongExtractAndClauseFidSpec_xfree
  · exact fullCongExtractFromFidSpec_xfree
  · exact fullCongAndMatchSpec_xfree
  · exact fullCongXorMatchSpec_xfree
  · exact fullCongEnqVarSpec_xfree
  · exact fullCongEvalGateSpec_xfree
  · exact fullCongWorklistSpec_xfree
  · exact fullCongSiftPairsFidSpec_xfree
  · exact fullCongSortPairsFidSpec_xfree
  · exact fullCongFwdSubsumeSpec_xfree
  · exact fullCongU64SiftM7Spec_xfree
  · exact fullCongU64SortM7Spec_xfree
  · exact fullCongBsearchU64M7Spec_xfree
  · exact fullCongCopyCondbinM7Spec_xfree
  · exact fullCongExtractCondeqM7Spec_xfree
  · exact fullCongMergeCondeqM7Spec_xfree
  · exact fullCongExtractIteAllM7Spec_xfree
  · exact fullCongruenceDenseSpec_xfree

theorem has_full_cong_find {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_find" fullCongFindSpec :=
  h.has (List.getElem_mem (l := specs) (n := 0) (by decide)) fullCongFindSpec_xfree

theorem has_full_cong_merge {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_merge" fullCongMergeSpec :=
  h.has (List.getElem_mem (l := specs) (n := 1) (by decide)) fullCongMergeSpec_xfree

theorem has_full_cong_mark_trail {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_mark_trail" fullCongMarkTrailSpec :=
  h.has (List.getElem_mem (l := specs) (n := 2) (by decide)) fullCongMarkTrailSpec_xfree

theorem has_full_cong_unit_fold {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_unit_fold" fullCongUnitFoldSpec :=
  h.has (List.getElem_mem (l := specs) (n := 3) (by decide)) fullCongUnitFoldSpec_xfree

theorem has_full_cong_equiv_fold {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_equiv_fold" fullCongEquivFoldSpec :=
  h.has (List.getElem_mem (l := specs) (n := 4) (by decide)) fullCongEquivFoldSpec_xfree

theorem has_full_cong_emit_xor {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_emit_xor" fullCongEmitXorSpec :=
  h.has (List.getElem_mem (l := specs) (n := 5) (by decide)) fullCongEmitXorSpec_xfree

theorem has_full_cong_has_clause_k {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_has_clause_k" fullCongHasClauseKSpec :=
  h.has (List.getElem_mem (l := specs) (n := 6) (by decide)) fullCongHasClauseKSpec_xfree

theorem has_full_cong_emit_xor4 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_emit_xor4" fullCongEmitXor4Spec :=
  h.has (List.getElem_mem (l := specs) (n := 7) (by decide)) fullCongEmitXor4Spec_xfree

theorem has_full_cong_extract_xor_k {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_extract_xor_k" fullCongExtractXorKSpec :=
  h.has (List.getElem_mem (l := specs) (n := 8) (by decide)) fullCongExtractXorKSpec_xfree

theorem has_full_cong_try_xor_ite {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_try_xor_ite" fullCongTryXorIteSpec :=
  h.has (List.getElem_mem (l := specs) (n := 9) (by decide)) fullCongTryXorIteSpec_xfree

theorem has_full_cong_count_bins {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_count_bins" fullCongCountBinsSpec :=
  h.has (List.getElem_mem (l := specs) (n := 10) (by decide)) fullCongCountBinsSpec_xfree

theorem has_full_cong_eb_match {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_eb_match" fullCongEbMatchSpec :=
  h.has (List.getElem_mem (l := specs) (n := 11) (by decide)) fullCongEbMatchSpec_xfree

theorem has_full_cong_extract_binaries {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_extract_binaries" fullCongExtractBinariesSpec :=
  h.has (List.getElem_mem (l := specs) (n := 12) (by decide)) fullCongExtractBinariesSpec_xfree

theorem has_full_cong_find_units_equivs {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_find_units_equivs" fullCongFindUnitsEquivsSpec :=
  h.has (List.getElem_mem (l := specs) (n := 13) (by decide)) fullCongFindUnitsEquivsSpec_xfree

theorem has_full_cong_extract_and_clause_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_extract_and_clause_fid" fullCongExtractAndClauseFidSpec :=
  h.has (List.getElem_mem (l := specs) (n := 14) (by decide))
    fullCongExtractAndClauseFidSpec_xfree

theorem has_full_cong_extract_from_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_extract_from_fid" fullCongExtractFromFidSpec :=
  h.has (List.getElem_mem (l := specs) (n := 15) (by decide)) fullCongExtractFromFidSpec_xfree

theorem has_full_cong_and_match {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_and_match" fullCongAndMatchSpec :=
  h.has (List.getElem_mem (l := specs) (n := 16) (by decide)) fullCongAndMatchSpec_xfree

theorem has_full_cong_xor_match {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_xor_match" fullCongXorMatchSpec :=
  h.has (List.getElem_mem (l := specs) (n := 17) (by decide)) fullCongXorMatchSpec_xfree

theorem has_full_cong_enq_var {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_enq_var" fullCongEnqVarSpec :=
  h.has (List.getElem_mem (l := specs) (n := 18) (by decide)) fullCongEnqVarSpec_xfree

theorem has_full_cong_eval_gate {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_eval_gate" fullCongEvalGateSpec :=
  h.has (List.getElem_mem (l := specs) (n := 19) (by decide)) fullCongEvalGateSpec_xfree

theorem has_full_cong_worklist {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_worklist" fullCongWorklistSpec :=
  h.has (List.getElem_mem (l := specs) (n := 20) (by decide)) fullCongWorklistSpec_xfree

theorem has_full_cong_sift_pairs_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_sift_pairs_fid" fullCongSiftPairsFidSpec :=
  h.has (List.getElem_mem (l := specs) (n := 21) (by decide)) fullCongSiftPairsFidSpec_xfree

theorem has_full_cong_sort_pairs_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_sort_pairs_fid" fullCongSortPairsFidSpec :=
  h.has (List.getElem_mem (l := specs) (n := 22) (by decide)) fullCongSortPairsFidSpec_xfree

theorem has_full_cong_fwd_subsume {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_fwd_subsume" fullCongFwdSubsumeSpec :=
  h.has (List.getElem_mem (l := specs) (n := 23) (by decide)) fullCongFwdSubsumeSpec_xfree

theorem has_full_cong_u64_sift_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_u64_sift_m7" fullCongU64SiftM7Spec :=
  h.has (List.getElem_mem (l := specs) (n := 24) (by decide)) fullCongU64SiftM7Spec_xfree

theorem has_full_cong_u64_sort_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_u64_sort_m7" fullCongU64SortM7Spec :=
  h.has (List.getElem_mem (l := specs) (n := 25) (by decide)) fullCongU64SortM7Spec_xfree

theorem has_full_cong_bsearch_u64_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_bsearch_u64_m7" fullCongBsearchU64M7Spec :=
  h.has (List.getElem_mem (l := specs) (n := 26) (by decide)) fullCongBsearchU64M7Spec_xfree

theorem has_full_cong_copy_condbin_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_copy_condbin_m7" fullCongCopyCondbinM7Spec :=
  h.has (List.getElem_mem (l := specs) (n := 27) (by decide)) fullCongCopyCondbinM7Spec_xfree

theorem has_full_cong_extract_condeq_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_extract_condeq_m7" fullCongExtractCondeqM7Spec :=
  h.has (List.getElem_mem (l := specs) (n := 28) (by decide)) fullCongExtractCondeqM7Spec_xfree

theorem has_full_cong_merge_condeq_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_merge_condeq_m7" fullCongMergeCondeqM7Spec :=
  h.has (List.getElem_mem (l := specs) (n := 29) (by decide)) fullCongMergeCondeqM7Spec_xfree

theorem has_full_cong_extract_ite_all_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_cong_extract_ite_all_m7" fullCongExtractIteAllM7Spec :=
  h.has (List.getElem_mem (l := specs) (n := 30) (by decide)) fullCongExtractIteAllM7Spec_xfree

theorem has_full_congruence_dense {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_congruence_dense" fullCongruenceDenseSpec :=
  h.has (List.getElem_mem (l := specs) (n := 31) (by decide)) fullCongruenceDenseSpec_xfree

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
