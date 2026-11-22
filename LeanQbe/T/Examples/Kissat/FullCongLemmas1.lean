module

public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.Full

/-!
# Kissat `D-Full` Gate Extraction & Congruence Closure — Part 1 (`Stage 4`)

Defines `FullCongSpecs` (canonical Stage-4 invariants, congruence union-find & gate-buffer
invariants, callee contracts, and contracts for all 10 congruence functions), pure congruence
soundness lemmas, and parametric `(Γ : Env)` `Func.wp` proofs #1, #2, #4:
1. `full_cong_find` (`full_cong_find_wp`)
2. `full_cong_merge` (`full_cong_merge_wp`)
4. `full_sort_u32` (`full_sort_u32_wp`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Canonical Stage-4 & Congruence Specifications (`FullCongSpecs`) -/

namespace FullCongSpecs

/-- Both variable marks (`mrk`) and literal marks (`lit_mark`) are completely zeroed. -/
@[expose] def FullLitMarksClear (c : FullCfg) (s : FullState) : Prop :=
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
  (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)

/-- Every non-garbage arena clause has pairwise distinct variables (`l / 2`). -/
@[expose] def FullArenaVarsNodup (s : FullState) : Prop :=
  ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false →
    ((fullArenaClauseLits s r).map (· / 2)).Nodup

/-- Every non-sentinel slot in `last_learned[0..8)` points to a valid arena clause. -/
@[expose] def FullLastLearnedWf (s : FullState) : Prop :=
  ∀ i < 8,
    let cr := s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32
    cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ fullArenaClauseRefs s

/-- Extension-stack and `last_learned` scratch well-formedness. -/
@[expose] def FullExtScratchOk (c : FullCfg) (s : FullState) : Prop :=
  FullLastLearnedWf s ∧ s.scratch.extend_len ≤ c.extend_cap

/-- Sparse 2WL invariant (`dense_mode = 0`). -/
@[expose] def FullSparseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

/-- Dense occurrence invariant (`cur_level = 0`, `dense_mode ≠ 0`). -/
@[expose] def FullDenseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64

/-- Union-find parent monotonicity (`repr[l] ≤ l`) on `0 ..< nlits`. -/
@[expose] def CongReprWf (nlits : Nat) (repr : List (BitVec 32)) : Prop :=
  nlits ≤ repr.length ∧ ∀ l < nlits, (repr[l]?.getD 0#32).toNat ≤ l

/-- Semantic union-find invariant: parent monotonicity plus `F_cur ⊨ (l ↔ repr[l])`. -/
@[expose]
def CongReprInv (F_cur : List (List Nat)) (nlits : Nat) (repr : List (BitVec 32)) : Prop :=
  CongReprWf nlits repr ∧
  ∀ l < nlits, LitEquiv (cnfOfClauses F_cur) l (repr[l]?.getD 0#32).toNat

/-- Iterated union-find root following `repr[x]` up to `fuel` steps. -/
@[expose] def congRoot (repr : List (BitVec 32)) : Nat → Nat → Nat
  | 0, x => x
  | fuel + 1, x =>
    let p := (repr[x]?.getD 0#32).toNat
    if p = x then x else congRoot repr fuel p

/-- Valid extracted gate (AND `tag=0`, XOR `tag=1`, or ITE `tag=2`) encoded in `scr` at `g`. -/
@[expose] def GateAt (F_cur : List (List Nat)) (cur_vars : Nat) (scr : List (BitVec 32))
    (g_len g : Nat) : Prop :=
  ∃ (lhs mword : BitVec 32),
    scr[g]? = some lhs ∧ scr[g + 1]? = some mword ∧
    lhs.toNat < 2 * cur_vars ∧
    let tag := (mword >>> 28).toNat
    let arity := (mword &&& 0xFF#32).toNat
    g + 2 + arity ≤ g_len ∧ arity ≤ cur_vars ∧ arity ≤ 8 ∧
    (∀ k < arity, ∃ r : BitVec 32, scr[g + 2 + k]? = some r ∧ r.toNat < 2 * cur_vars) ∧
    ((tag = 0 ∧ 2 ≤ arity ∧
        AndGateDef (cnfOfClauses F_cur) lhs.toNat
          (((scr.drop (g + 2)).take arity).map BitVec.toNat)) ∨
     (tag = 1 ∧ arity = 2 ∧
        XorGateDef (cnfOfClauses F_cur) lhs.toNat
          (scr[g + 2]?.getD 0#32).toNat (scr[g + 3]?.getD 0#32).toNat) ∨
     (tag = 2 ∧ arity = 3 ∧
        IteGateDef (cnfOfClauses F_cur) lhs.toNat
          (scr[g + 2]?.getD 0#32).toNat (scr[g + 3]?.getD 0#32).toNat
          (scr[g + 4]?.getD 0#32).toNat))

/-- Contiguous sequence of valid gates in `scr[g ..< g_len)`. -/
inductive GateSeqOk (F_cur : List (List Nat)) (cur_vars : Nat) (scr : List (BitVec 32))
    (g_len : Nat) : Nat → Prop where
  | done : GateSeqOk F_cur cur_vars scr g_len g_len
  | step {g : Nat} (hg : GateAt F_cur cur_vars scr g_len g) :
      GateSeqOk F_cur cur_vars scr g_len
        (g + 2 + ((scr[g + 1]?.getD 0#32) &&& 0xFF#32).toNat) →
      GateSeqOk F_cur cur_vars scr g_len g

/-- Every non-empty slot in the congruence hash table `scr[ht_off ..< ht_off + ht_sz)` points
to a valid gate offset in `scr0[0 ..< g_len)`. -/
@[expose] def CongHtInv (F_cur : List (List Nat)) (cur_vars : Nat) (scr0 scr : List (BitVec 32))
    (g_len ht_off ht_sz : Nat) : Prop :=
  ∀ k < ht_sz,
    let ent := scr[ht_off + k]?.getD 0xFFFFFFFF#32
    ent = 0xFFFFFFFF#32 ∨ GateAt F_cur cur_vars scr0 g_len ent.toNat

/-! ### Callee contracts -/

@[expose] def fullArenaNextSpec : Spec [i64, i32] [i32] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    Q (BitVec.ofNat 32 (fullArenaNextOff s.core.arena s.core.arena_len cref.toNat), ()) m

@[expose] def fullHasBinSpec : Spec [i64, i32, i32] [.bool] := fun (h, a, b, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ ok : Bool,
      (ok = true →
        a.toNat < 2 * s.core.cur_vars ∧ b.toNat < 2 * s.core.cur_vars ∧
        a ≠ b ∧ a ≠ (b ^^^ 1#32) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat])) →
      Q (ok, ()) m

@[expose] def fullAddBinSpec : Spec [i64, i32, i32] [i64] := fun (h, a, b, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    s.core.cur_level = 0 ∧
    a.toNat < 2 * s.core.cur_vars ∧ b.toNat < 2 * s.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat]) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      s'.core.cur_level = 0 → s'.core.dense_mode = s.core.dense_mode →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.core.mrk = s.core.mrk → s'.core.lit_mark = s.core.lit_mark →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.repr = s.core.repr → s'.core.tmp = s.core.tmp →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.last_learned = s.scratch.last_learned →
      s'.scratch.extend_len = s.scratch.extend_len →
      (r = 20#64 → s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullAddUnitSpec : Spec [i64, i32] [.bool] := fun (h, lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    s.core.cur_level = 0 ∧
    lit.toNat < 2 * s.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      s'.core.cur_level = 0 → s'.core.dense_mode = s.core.dense_mode →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.core.mrk = s.core.mrk → s'.core.lit_mark = s.core.lit_mark →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.repr = s.core.repr → s'.core.tmp = s.core.tmp →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.last_learned = s.scratch.last_learned →
      s'.scratch.extend_len = s.scratch.extend_len →
      (ok = false → s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullBacktrackSpec : Spec [i64, i64] [] := fun (h, target_lvl, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ target_lvl.toNat ≤ s.core.cur_level ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (s' : FullState) (m' : Mem 64),
      FullSparseInv c F0 s' → s'.core.cur_level = target_lvl.toNat →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullEnterDenseSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (ok = true → FullDenseInv c F0 s') →
      (ok = false → FullSparseInv c F0 s') →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullRebuildWatchesSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r ≠ 20#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullPropagateSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ### Owned congruence function contracts (`10` total) -/

@[expose] def fullCongFindSpec : Spec [i64, i32] [i32] := fun (repr_ptr, l, ()) m Q _ =>
  ∃ (F_cur : List (List Nat)) (nlits : Nat) (repr : List (BitVec 32)) (R : Mem 64 → Prop),
    CongReprInv F_cur nlits repr ∧ l.toNat < nlits ∧
    (array (t := i32) repr_ptr repr ⋆ R) m ∧
    ∀ (r : BitVec 32) (repr' : List (BitVec 32)) (m' : Mem 64),
      repr'.length = repr.length →
      CongReprInv F_cur nlits repr' →
      r.toNat ≤ l.toNat → r.toNat < nlits →
      LitEquiv (cnfOfClauses F_cur) l.toNat r.toNat →
      (array (t := i32) repr_ptr repr' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullCongMergeSpec : Spec [i64, i32, i32] [.bool] := fun (h, a, b, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
    s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧
    CongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
    a.toNat < 2 * s.core.cur_vars ∧ b.toNat < 2 * s.core.cur_vars ∧
    LitEquiv (cnfOfClauses F_cur) a.toNat b.toNat ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ch : Bool) (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_level = 0 → s'.core.dense_mode ≠ 0#64 →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.tmp = s.core.tmp →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      CongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      (FullMem c s' ⋆ R) m' → Q (ch, ()) m'

@[expose]
def fullHasTernarySpec : Spec [i64, i32, i32, i32] [.bool] := fun (h, a, b, cl, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧
    a.toNat < 2 * s.core.cur_vars ∧
    (FullMem c s ⋆ R) m ∧
    ∀ ok : Bool,
      (ok = true → a ≠ b → a ≠ cl → b ≠ cl →
        (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat, cl.toNat])) →
      Q (ok, ()) m

@[expose] def fullSortU32Spec : Spec [i64, i32] [] := fun (arr_ptr, n, ()) m Q _ =>
  ∃ (arr : List (BitVec 32)) (R : Mem 64 → Prop),
    n.toNat ≤ arr.length ∧ (array (t := i32) arr_ptr arr ⋆ R) m ∧
    ∀ (arr' : List (BitVec 32)) (m' : Mem 64),
      arr'.length = arr.length →
      List.Perm (arr'.take n.toNat) (arr.take n.toNat) →
      (∀ k, n.toNat ≤ k → arr'[k]? = arr[k]?) →
      (array (t := i32) arr_ptr arr' ⋆ R) m' → Q () m'

@[expose] def fullCongExtractIteSpec : Spec [i64, i32, i32, i32, i64] [i64] :=
  fun (h, c_lit, y, t, g_len, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧
      c_lit.toNat < 2 * s.core.cur_vars ∧ y.toNat < 2 * s.core.cur_vars ∧
      t.toNat < 2 * s.core.cur_vars ∧
      c_lit.toNat / 2 ≠ y.toNat / 2 ∧ c_lit.toNat / 2 ≠ t.toNat / 2 ∧
      y.toNat / 2 ≠ t.toNat / 2 ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [y.toNat, litNeg c_lit.toNat, litNeg t.toNat]) ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg y.toNat, litNeg c_lit.toNat, t.toNat]) ∧
      g_len.toNat + 5 ≤ c.scratch_cap ∧
      GateSeqOk F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (ret = g_len ∨ ret = g_len + 5#64) →
        (∀ idx < g_len.toNat, scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        GateSeqOk F_cur s.core.cur_vars scr' ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

@[expose] def fullCongEmitXorSpec : Spec [i64, i64, i32, i32, i32] [i64] :=
  fun (scr_ptr, g_len, x0, x1, x2, ()) m Q _ =>
    ∃ (F_cur : List (List Nat)) (cur_vars : Nat) (scr : List (BitVec 32)) (R : Mem 64 → Prop),
      x0.toNat < 2 * cur_vars ∧ x1.toNat < 2 * cur_vars ∧ x2.toNat < 2 * cur_vars ∧
      2 ≤ cur_vars ∧ g_len.toNat + 4 ≤ scr.length ∧ scr.length < 2 ^ 32 ∧
      XorGateDef (cnfOfClauses F_cur) (litNeg x0.toNat) x1.toNat x2.toNat ∧
      GateSeqOk F_cur cur_vars scr g_len.toNat 0 ∧
      (array (t := i32) scr_ptr scr ⋆ R) m ∧
      ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
        scr'.length = scr.length →
        (∀ idx < g_len.toNat, scr'[idx]? = scr[idx]?) →
        GateSeqOk F_cur cur_vars scr' (g_len.toNat + 4) 0 →
        (array (t := i32) scr_ptr scr' ⋆ R) m' → Q (g_len + 4#64, ()) m'

@[expose] def fullCongTryXorIteSpec : Spec [i64, i32, i32, i32, i64, i64] [i64] :=
  fun (h, a, b, cl, g_len, g_cap, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧
      a.toNat < 2 * s.core.cur_vars ∧ b.toNat < 2 * s.core.cur_vars ∧
      cl.toNat < 2 * s.core.cur_vars ∧
      a.toNat / 2 ≠ b.toNat / 2 ∧ a.toNat / 2 ≠ cl.toNat / 2 ∧ b.toNat / 2 ≠ cl.toNat / 2 ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat, cl.toNat]) ∧
      g_len.toNat + 5 ≤ g_cap.toNat ∧ g_cap.toNat ≤ c.scratch_cap ∧
      GateSeqOk F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        g_len.toNat ≤ ret.toNat → ret.toNat ≤ g_cap.toNat →
        (∀ idx < g_len.toNat, scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        GateSeqOk F_cur s.core.cur_vars scr' ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

@[expose] def fullCongExtractSpec : Spec [i64, i64] [i64] := fun (h, g_cap, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧
    g_cap.toNat ≤ c.scratch_cap ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      ret.toNat ≤ g_cap.toNat →
      GateSeqOk F_cur s.core.cur_vars scr' ret.toNat 0 →
      (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

@[expose] def fullCongHashStepSpec : Spec [i64, i64, i64, i64] [.bool] :=
  fun (h, g_len, ht_off, ht_sz, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
      s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧
      CongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      0 < ht_sz.toNat ∧ g_len.toNat ≤ ht_off.toNat ∧ ht_off.toNat + ht_sz.toNat ≤ c.scratch_cap ∧
      GateSeqOk F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ch : Bool) (s' : FullState) (m' : Mem 64),
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
        s'.core.cur_level = 0 → s'.core.dense_mode ≠ 0#64 →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
        CongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
        (∀ idx < g_len.toNat, s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) →
        (FullMem c s' ⋆ R) m' → Q (ch, ()) m'

@[expose] def fullCongruenceSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) →
      (r = 1#64 → FullSparseInv c F0 s') →
      (r = 20#64 → F0.Unsat ∧ s'.LengthsOk c) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

end FullCongSpecs

open FullCongSpecs

/-! ## 2. Scoped Tactics & Array Framing Helpers (`FullCongTactics`) -/

namespace FullCongTactics

attribute [scoped bv_c0] List.length_set

theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

scoped macro "fc_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)
scoped macro "fc_unmdata" : tactic =>
  `(tactic| first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)
scoped macro "fc_step" : tactic => `(tactic| ((try fc_unmdata); (repeat fc_strip); c0_step))
scoped macro "fc_steps" : tactic =>
  `(tactic| (
      (try fc_unmdata)
      (repeat fc_strip)
      c0_steps
      repeat (any_goals (fc_strip; repeat fc_strip); c0_steps)))

open Lean Elab Tactic in
/-- Step straight-line code like `c0_steps`, stopping at `Expr.group` instead of inlining joins. -/
scoped elab "fc_to_group" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      evalTactic (← `(tactic| try dsimp only))
      evalTactic (← `(tactic| try fc_unmdata))
      let g ← getMainGoal
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData.headBeta
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push g
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out.push g
    setGoals out.toList
  go 500

open Lean Elab Tactic in
/-- Step straight-line ops on the main goal until the next `Expr.jnz`, then split it once. -/
scoped elab "fc_split" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    evalTactic (← `(tactic| try dsimp only))
    evalTactic (← `(tactic| try fc_unmdata))
    let ty := (← Lean.instantiateMVars (← (← getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← LeanQbe.T.C0Step.stepOnce; return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  go 100

theorem wp_jnz_var {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : Bool} {t e : Expr Val Cont rs} {m : Mem 64}
    (ht : c = true → wp Γ Q X t m) (he : c = false → wp Γ Q X e m) :
    wp Γ Q X (Expr.jnz (Arg.var c) t e) m := ⟨ht, he⟩

scoped macro "fc_let" : tactic =>
  `(tactic| ((try dsimp only); (try fc_unmdata); (try c0_let_simp)))

open Lean Elab Tactic in
/-- Fast `jnz` splitter: steps loads/lets with `c0_let_simp`/`stepOnce` and splits `jnz`
directly without calling `c0_bound` on live branches. -/
scoped elab "fc_split_fast" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    evalTactic (← `(tactic| try dsimp only))
    evalTactic (← `(tactic| try fc_unmdata))
    evalTactic (← `(tactic| try c0_let_simp))
    let ty := (← Lean.instantiateMVars (← (← getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let hcId := Lean.mkIdent `hc
      evalTactic (← `(tactic| refine wp_jnz_var (fun $hcId => ?_) (fun $hcId => ?_)))
      return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  go 100

end FullCongTactics

open scoped FullArenaTactics FullCongTactics

namespace FullCongHelpers

/-- Focus `array (t := i32) c.pRepr s.core.repr` out of `FullMem c s ⋆ R`. -/
@[expose] def FullReprRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
   array (t := i32) c.pFrameDec s.core.frame_dec ⋆
   array (t := i32) c.pWvec s.core.wvec ⋆
   array (t := i32) c.pMinStk s.core.min_stk) ⋆
  (FullCoreByteArrs c s.core ⋆ FullCoreU32A c s.core ⋆ FullCoreDynArrs c s.core ⋆
   fullCoreOuter c s)

theorem focus_full_repr {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pRepr s.core.repr ⋆ (FullReprRest c s ⋆ R)) m := by
  rw [fullMem_eq_coreU32B] at hm; unfold FullCoreU32B at hm; unfold FullReprRest; ecancel

theorem unfocus_full_repr {c : FullCfg} {s : FullState} {repr' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pRepr repr' ⋆ (FullReprRest c s ⋆ R)) m) :
    (FullMem c { s with core := { s.core with repr := repr' } } ⋆ R) m := by
  rw [fullMem_eq_coreU32B]; unfold FullCoreU32B; unfold FullReprRest at hm
  change ((array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
    array (t := i32) c.pFrameDec s.core.frame_dec ⋆
    array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr repr' ⋆
    array (t := i32) c.pMinStk s.core.min_stk) ⋆
    (FullCoreByteArrs c s.core ⋆ FullCoreU32A c s.core ⋆ FullCoreDynArrs c s.core ⋆
     fullCoreOuter c s) ⋆ R) m
  ecancel

/-- Focus `array (t := i32) c.pTmp s.core.tmp` out of `FullMem c s ⋆ R`. -/
@[expose] def FullTmpRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
   array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
   array (t := i32) c.pTrailPos s.core.trail_pos ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
  (FullCoreByteArrs c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
   fullCoreOuter c s)

theorem focus_full_tmp {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pTmp s.core.tmp ⋆ (FullTmpRest c s ⋆ R)) m := by
  rw [fullMem_eq_coreU32A] at hm; unfold FullCoreU32A at hm; unfold FullTmpRest; ecancel

theorem unfocus_full_tmp {c : FullCfg} {s : FullState} {tmp' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pTmp tmp' ⋆ (FullTmpRest c s ⋆ R)) m) :
    (FullMem c { s with core := { s.core with tmp := tmp' } } ⋆ R) m := by
  rw [fullMem_eq_coreU32A]; unfold FullCoreU32A; unfold FullTmpRest at hm
  change ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
    array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
    array (t := i32) c.pTrailPos s.core.trail_pos ⋆ array (t := i32) c.pTmp tmp' ⋆
    array (t := i32) c.pMinClr s.core.min_clr) ⋆
    (FullCoreByteArrs c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
     fullCoreOuter c s) ⋆ R) m
  ecancel

/-- Focus `array (t := i32) c.pScratchBuf s.scratch.scratch_buf` out of `FullMem c s ⋆ R`. -/
@[expose] def FullScrBufRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i32) c.pDelayed s.scratch.delayed ⋆ array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
   array (t := i32) c.pExtendStk s.scratch.extend_stk) ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
   FullScrMetaArrs c s.scratch ⋆ fullScrOuter c s)

theorem focus_full_scratch_buf {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆ (FullScrBufRest c s ⋆ R)) m := by
  rw [fullMem_eq_scrDyn] at hm; unfold FullScrDynArrs at hm; unfold FullScrBufRest; ecancel

theorem unfocus_full_scratch_buf {c : FullCfg} {s : FullState} {scr' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pScratchBuf scr' ⋆ (FullScrBufRest c s ⋆ R)) m) :
    (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m := by
  rw [fullMem_eq_scrDyn]; unfold FullScrDynArrs; unfold FullScrBufRest at hm
  change ((array (t := i32) c.pDelayed s.scratch.delayed ⋆
    array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
    array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
    array (t := i32) c.pScratchBuf scr') ⋆
    (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
     FullScrMetaArrs c s.scratch ⋆ fullScrOuter c s) ⋆ R) m
  ecancel

/-! ## 3. Pure Congruence, BitVec, Invariant, and List Lemmas -/

theorem list_getElem_congr {α : Type} {xs : List α} {i j : Nat}
    (h : i = j) (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

theorem bv64_shl1_toNat (x : BitVec 64) : (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

theorem bv_zext32_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat :=
  zext_toNat x (by decide)

theorem fullLitMarksClear_of_eq {c : FullCfg} {s s' : FullState}
    (h : FullLitMarksClear c s) (h1 : s'.core.mrk = s.core.mrk)
    (h2 : s'.core.lit_mark = s.core.lit_mark) : FullLitMarksClear c s' :=
  ⟨fun v hv => by rw [h1]; exact h.1 v hv, fun l hl => by rw [h2]; exact h.2 l hl⟩

theorem fullArenaVarsNodup_of_eq {s s' : FullState} (h : FullArenaVarsNodup s)
    (h1 : s'.core.arena = s.core.arena) (h2 : s'.core.arena_len = s.core.arena_len) :
    FullArenaVarsNodup s' := by
  unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseRefsCore fullArenaClauseGarb
    fullArenaClauseGarbCore fullArenaHdrCore fullArenaClauseLits fullArenaClauseLitsCore
    fullArenaClauseSizeCore at h ⊢
  rw [h1, h2]; exact h

theorem fullExtScratchOk_of_eq {c : FullCfg} {s s' : FullState} (h : FullExtScratchOk c s)
    (h1 : s'.core.arena = s.core.arena) (h2 : s'.core.arena_len = s.core.arena_len)
    (h3 : s'.scratch.last_learned = s.scratch.last_learned)
    (h4 : s'.scratch.extend_len = s.scratch.extend_len) : FullExtScratchOk c s' := by
  refine ⟨fun i hi => ?_, by rw [h4]; exact h.2⟩
  have hll := h.1 i hi; dsimp only [fullArenaClauseRefs, fullArenaClauseRefsCore] at hll ⊢
  rw [h1, h2, h3]; exact hll

theorem fullWitnessInv_with_repr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (repr' : List (BitVec 32)) :
    FullWitnessInv c F0 F_cur { k with repr := repr' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem fullWitnessInv_with_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (tmp' : List (BitVec 32)) :
    FullWitnessInv c F0 F_cur { k with tmp := tmp' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem fullWitnessInv_with_inconsistent {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (inc' : BitVec 64)
    (hu : inc' ≠ 0#64 → (cnfOfClauses F_cur).Unsat) :
    FullWitnessInv c F0 F_cur { k with inconsistent := inc' } :=
  { hw with
    inconsistent_sound := hu
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem unsat_of_litEquiv_neg {f : CNF Nat} {a : Nat} (h : LitEquiv f a (litNeg a)) : f.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have he := litEquiv_eval hα h; rw [evalLitVal_litNeg] at he
  cases hb : evalLitVal α a <;> simp [hb] at he

theorem bv32_xor1_lt_even {x n : Nat} (hx : x < 2 * n) : x ^^^ 1 < 2 * n :=
  litNeg_lt_two_mul hx

theorem bv32_lt_and_ne_xor1_div_lt {ra rb : BitVec 32} (hlt : ra.toNat < rb.toNat)
    (hne : ra ≠ rb ^^^ 1#32) :
    ra.toNat / 2 < rb.toNat / 2 ∧ (ra ^^^ 1#32).toNat < (rb ^^^ 1#32).toNat := by
  have hdiv_ne : ra.toNat / 2 ≠ rb.toNat / 2 := by
    intro hd
    rcases (litVar_eq_iff ra.toNat rb.toNat).mp hd with h1 | h2
    · omega
    · apply hne; apply BitVec.eq_of_toNat_eq; simpa [litNeg, BitVec.toNat_xor] using h2
  have hdiv_lt : ra.toNat / 2 < rb.toNat / 2 := by omega
  refine ⟨hdiv_lt, ?_⟩
  have h1 : (ra ^^^ 1#32).toNat = litNeg ra.toNat := by simp [litNeg, BitVec.toNat_xor]
  have h2 : (rb ^^^ 1#32).toNat = litNeg rb.toNat := by simp [litNeg, BitVec.toNat_xor]
  rw [h1, h2, litNeg_eq, litNeg_eq]
  split <;> split <;> omega

theorem bv32_xor1_eq_litNeg (x : BitVec 32) : (x ^^^ 1#32).toNat = litNeg x.toNat := by
  simp [litNeg, BitVec.toNat_xor]

theorem bv32_xor1_litNeg (x : BitVec 32) : (x ^^^ 1).toNat = litNeg x.toNat := by
  simp [litNeg, BitVec.toNat_xor]

theorem bv32_xor1_symm {a b : BitVec 32} (h : a ≠ b ^^^ 1#32) : b ≠ a ^^^ 1#32 := by
  intro heq; apply h; rw [heq, BitVec.xor_assoc]; simp

theorem bv8_sgt0_iff_eq1 {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) :
    (0#8 : BitVec 8).slt v = true ↔ v = 1#8 := by
  rcases hdom with rfl | rfl | rfl <;> decide

private theorem not_mem_erase_of_nodup {α : Type} [BEq α] [LawfulBEq α] {a : α} :
    ∀ {xs : List α}, xs.Nodup → a ∉ xs.erase a
  | [], _ => by simp
  | x :: xs, hnd => by
    rw [List.nodup_cons] at hnd
    by_cases hxa : x = a
    · subst hxa; simpa using hnd.1
    · have hne : (x == a) = false := beq_false_of_ne hxa
      simp only [List.erase_cons, hne, Bool.false_eq_true, ↓reduceIte, List.mem_cons, not_or]
      exact ⟨Ne.symm hxa, not_mem_erase_of_nodup hnd.2⟩

theorem nodup_lt_length_le : ∀ {n : Nat} {xs : List Nat},
    xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n := by
  intro n; induction n with
  | zero =>
    intro xs _ hlt; cases xs with
    | nil => exact Nat.le_refl 0
    | cons x _ => exfalso; have := hlt x List.mem_cons_self; omega
  | succ n ih =>
    intro xs hnd hlt
    by_cases hmem : n ∈ xs
    · have hnd' : (xs.erase n).Nodup := hnd.erase n
      have hlt' : ∀ x ∈ xs.erase n, x < n := fun x hx => by
        have hxm : x ∈ xs := List.mem_of_mem_erase hx
        have hne : x ≠ n := fun h => not_mem_erase_of_nodup hnd (h ▸ hx)
        have := hlt x hxm; omega
      have hle := ih hnd' hlt'
      have hlen : (xs.erase n).length = xs.length - 1 := List.length_erase_of_mem hmem
      have hpos : 0 < xs.length := List.length_pos_of_mem hmem; omega
    · have hlt' : ∀ x ∈ xs, x < n := fun x hx => by
        have hne : x ≠ n := fun h => hmem (h ▸ hx)
        have := hlt x hx; omega
      exact Nat.le_trans (ih hnd hlt') (Nat.le_succ n)

theorem fullArenaClauseSize_le_cur_vars {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hnodup : FullArenaVarsNodup s) {r : Nat}
    (hr : r ∈ fullArenaClauseRefs s) (hg : fullArenaClauseGarb s r = false) :
    fullArenaClauseSize s r ≤ s.core.cur_vars := by
  have hwf := hw.arena.refs_wf r hr
  have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
    have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
  have hlen_lits : (fullArenaClauseLits s r).length = fullArenaClauseSizeCore s.core r := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    simp only [List.length_map, List.length_take, List.length_drop]; omega
  have hnd := hnodup r hr hg
  have hle := nodup_lt_length_le (n := s.core.cur_vars) hnd fun v hv => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
    have hl_lt : l < 2 * s.core.cur_vars := hw.arena.lits_lt r hr hg l hl; omega
  rw [List.length_map, hlen_lits] at hle; exact hle

theorem nodup_of_map_nodup {α β : Type} {f : α → β} {xs : List α}
    (h : (xs.map f).Nodup) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    rw [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.mpr ⟨fun ha => h.1 (List.mem_map_of_mem ha), ih h.2⟩

theorem fullArenaScanRefs_next_mem {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos r : Nat}, alen - pos ≤ fuel →
      r ∈ fullArenaScanRefs ar alen pos fuel →
      fullArenaNextOff ar alen r + 3 ≤ alen →
      fullArenaNextOff ar alen r ∈ fullArenaScanRefs ar alen pos fuel
  | 0, _, _, _, h, _ => by simp [fullArenaScanRefs] at h
  | fuel + 1, pos, r, hfl, hmem, hn3 => by
    unfold fullArenaScanRefs at hmem ⊢; split at hmem
    · rename_i hle; simp only [hle, ↓reduceIte, List.mem_cons] at hmem ⊢
      have hb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      rcases hmem with rfl | hrest
      · right; cases fuel with
        | zero => omega
        | succ f' => unfold fullArenaScanRefs; simp [hn3]
      · right; exact fullArenaScanRefs_next_mem (by omega) hrest hn3
    · simp at hmem

theorem fullArenaClauseRefs_zero_mem {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hpos : 0 < k.arena_len) :
    0 ∈ fullArenaClauseRefsCore k := by
  have h3 : 3 ≤ k.arena_len := hw.arena.len_ok.elim (fun h => by omega) id
  unfold fullArenaClauseRefsCore
  cases hal : k.arena_len with
  | zero => omega
  | succ f => unfold fullArenaScanRefs; simp [show 3 ≤ f + 1 by omega]

theorem fullArenaClauseRefs_next_or_end {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {r : Nat}
    (hr : r ∈ fullArenaClauseRefsCore k) :
    fullArenaNextOff k.arena k.arena_len r = k.arena_len ∨
      fullArenaNextOff k.arena k.arena_len r ∈ fullArenaClauseRefsCore k := by
  rcases (hw.arena.refs_wf r hr).2.2.2.2 with heq | h3
  · exact Or.inl heq
  · exact Or.inr (fullArenaScanRefs_next_mem (by omega) hr h3)

/-! ### `congRoot` and union-find path compression lemmas -/

theorem congRoot_fuel_ge {repr : List (BitVec 32)} {nlits : Nat}
    (hwf : CongReprWf nlits repr) :
    ∀ {x f1 f2 : Nat}, x < nlits → x < f1 → x < f2 →
      congRoot repr f1 x = congRoot repr f2 x := by
  intro x; induction x using Nat.strongRecOn with
  | ind x ih =>
    intro f1 f2 hx hf1 hf2
    cases f1 with
    | zero => omega
    | succ f1' =>
      cases f2 with
      | zero => omega
      | succ f2' =>
        simp only [congRoot]; split
        · rfl
        · rename_i hne
          have hle := hwf.2 x hx; have hlt : (repr[x]?.getD 0#32).toNat < x := by omega
          exact ih _ hlt (by omega) (by omega) (by omega)

theorem congRoot_le {repr : List (BitVec 32)} {nlits : Nat} (hwf : CongReprWf nlits repr) :
    ∀ {fuel x : Nat}, x < nlits → congRoot repr fuel x ≤ x := by
  intro fuel; induction fuel with
  | zero => intro x _; exact Nat.le_refl _
  | succ f ih =>
    intro x hx; simp only [congRoot]; split
    · exact Nat.le_refl _
    · have hle := hwf.2 x hx; exact Nat.le_trans (ih (by omega)) hle

theorem congRoot_litEquiv {F_cur : List (List Nat)} {nlits : Nat} {repr : List (BitVec 32)}
    (hinv : CongReprInv F_cur nlits repr) :
    ∀ {fuel x : Nat}, x < nlits →
      LitEquiv (cnfOfClauses F_cur) x (congRoot repr fuel x) := by
  intro fuel; induction fuel with
  | zero => intro x _; exact LitEquiv.refl _ _
  | succ f ih =>
    intro x hx; simp only [congRoot]; split
    · exact LitEquiv.refl _ _
    · have hle := hinv.1.2 x hx; exact (hinv.2 x hx).trans (ih (by omega))

theorem congRoot_eq_of_fixed {repr : List (BitVec 32)} {fuel x : Nat}
    (hfix : (repr[x]?.getD 0#32).toNat = x) : congRoot repr fuel x = x := by
  cases fuel with
  | zero => rfl
  | succ f => simp [congRoot, hfix]

/-! ### `GateAt` & `GateSeqOk` transport lemmas -/

theorem gateAt_congr {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr1 scr2 : List (BitVec 32)} {g_len1 g_len2 g : Nat}
    (hge : g_len1 ≤ g_len2)
    (heq : ∀ idx < g_len1, scr2[idx]? = scr1[idx]?)
    (hg : GateAt F_cur cur_vars scr1 g_len1 g) :
    GateAt F_cur cur_vars scr2 g_len2 g := by
  obtain ⟨lhs, mword, h0, h1, hlhs, hbd, hac, ha8, hrhs, hsem⟩ := hg
  have hslice : (scr2.drop (g + 2)).take (mword &&& 0xFF#32).toNat =
      (scr1.drop (g + 2)).take (mword &&& 0xFF#32).toNat := by
    have hl1 : g + 2 + (mword &&& 0xFF#32).toNat ≤ scr1.length := by
      rcases Nat.eq_zero_or_pos (mword &&& 0xFF#32).toNat with hz | hpos
      · have := (List.getElem?_eq_some_iff.mp h1).1; omega
      · obtain ⟨_, hr, _⟩ := hrhs ((mword &&& 0xFF#32).toNat - 1) (by omega)
        have := (List.getElem?_eq_some_iff.mp hr).1; omega
    have hl2 : g + 2 + (mword &&& 0xFF#32).toNat ≤ scr2.length := by
      rcases Nat.eq_zero_or_pos (mword &&& 0xFF#32).toNat with hz | hpos
      · have h1' : scr2[g + 1]? = some mword := (heq (g + 1) (by omega)).trans h1
        have := (List.getElem?_eq_some_iff.mp h1').1; omega
      · obtain ⟨r, hr, _⟩ := hrhs ((mword &&& 0xFF#32).toNat - 1) (by omega)
        have hr' : scr2[g + 2 + ((mword &&& 0xFF#32).toNat - 1)]? = some r :=
          (heq _ (by omega)).trans hr
        have := (List.getElem?_eq_some_iff.mp hr').1; omega
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop]; omega
    · intro k hk1 _
      simp only [List.length_take, List.length_drop] at hk1
      simp only [List.getElem_take, List.getElem_drop]; have hkeq := heq (g + 2 + k) (by omega)
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hkeq
      exact Option.some.inj hkeq
  refine ⟨lhs, mword, (heq g (by omega)).trans h0, (heq (g + 1) (by omega)).trans h1,
    hlhs, by omega, hac, ha8, ?_, ?_⟩
  · intro k hk; obtain ⟨r, hr, hlt⟩ := hrhs k hk
    exact ⟨r, (heq (g + 2 + k) (by omega)).trans hr, hlt⟩
  · rcases hsem with ⟨ht, ha2, hand⟩ | ⟨ht, ha2, hxor⟩ | ⟨ht, ha3, hite⟩
    · left; exact ⟨ht, ha2, hslice ▸ hand⟩
    · right; left
      rw [heq (g + 2) (by omega), heq (g + 3) (by omega)]; exact ⟨ht, ha2, hxor⟩
    · right; right
      rw [heq (g + 2) (by omega), heq (g + 3) (by omega), heq (g + 4) (by omega)]
      exact ⟨ht, ha3, hite⟩

theorem gateSeqOk_append {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr1 scr2 : List (BitVec 32)} {g_len1 g_len2 : Nat}
    (hge : g_len1 ≤ g_len2)
    (heq : ∀ idx < g_len1, scr2[idx]? = scr1[idx]?)
    (hnew : GateSeqOk F_cur cur_vars scr2 g_len2 g_len1) :
    ∀ {g : Nat}, GateSeqOk F_cur cur_vars scr1 g_len1 g →
      GateSeqOk F_cur cur_vars scr2 g_len2 g := by
  intro g hs; induction hs with
  | done => exact hnew
  | @step g hg _ ih =>
    have hg' := gateAt_congr hge heq hg; obtain ⟨_, mword, _, h1, _, hbd, _⟩ := hg
    have h1' : scr2[g + 1]? = scr1[g + 1]? := heq (g + 1) (by omega)
    exact .step hg' (by simpa [h1'] using ih)

theorem gateSeqOk_congr {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr1 scr2 : List (BitVec 32)} {g_len g : Nat}
    (heq : ∀ idx < g_len, scr2[idx]? = scr1[idx]?)
    (hs : GateSeqOk F_cur cur_vars scr1 g_len g) :
    GateSeqOk F_cur cur_vars scr2 g_len g :=
  gateSeqOk_append (Nat.le_refl _) heq .done hs

theorem gateSeqOk_inv_lt {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr : List (BitVec 32)} {g_len g : Nat}
    (hs : GateSeqOk F_cur cur_vars scr g_len g) (hlt : g < g_len) :
    GateAt F_cur cur_vars scr g_len g ∧
      GateSeqOk F_cur cur_vars scr g_len
        (g + 2 + ((scr[g + 1]?.getD 0#32) &&& 0xFF#32).toNat) := by
  cases hs with
  | done => omega
  | step hg hrest => exact ⟨hg, hrest⟩

/-! ### Semantic gate & ternary-clause helpers -/

theorem entails_of_eval_mem {f : CNF Nat} {xs : List Nat}
    (h : ∀ α : Nat → Bool, f.Sat α → ∃ l ∈ xs, evalLitVal α l = true) :
    f.EntailsClause (cnfClause xs) := by
  rw [CNF.entails_clause_def]
  intro α hα
  rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]; exact h α hα

theorem entails_perm_clause {f : CNF Nat} {xs ys : List Nat}
    (hsub : ∀ x ∈ xs, x ∈ ys) (h : f.EntailsClause (cnfClause xs)) :
    f.EntailsClause (cnfClause ys) :=
  CNF.entails_clause_def.mpr fun α hα =>
    sat_clause_of_subset hsub (CNF.entails_clause_def.mp h α hα)

theorem xorGateDef_of_eval_eq {f : CNF Nat} {g a b : Nat}
    (h : ∀ α : Nat → Bool, f.Sat α → evalLitVal α g = (evalLitVal α a != evalLitVal α b)) :
    XorGateDef f g a b := by
  refine ⟨entails_of_eval_mem fun α hα => ?_, entails_of_eval_mem fun α hα => ?_,
    entails_of_eval_mem fun α hα => ?_, entails_of_eval_mem fun α hα => ?_⟩
  · have hv := h α hα
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b
    · exact ⟨litNeg a, by simp, by simp [evalLitVal_litNeg, ha]⟩
    · exact ⟨g, by simp, by simp [hv, ha, hb]⟩
    · exact ⟨g, by simp, by simp [hv, ha, hb]⟩
    · exact ⟨b, by simp, hb⟩
  · have hv := h α hα
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b
    · exact ⟨litNeg b, by simp, by simp [evalLitVal_litNeg, hb]⟩
    · exact ⟨g, by simp, by simp [hv, ha, hb]⟩
    · exact ⟨g, by simp, by simp [hv, ha, hb]⟩
    · exact ⟨a, by simp, ha⟩
  · have hv := h α hα
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b
    · exact ⟨litNeg g, by simp, by simp [evalLitVal_litNeg, hv, ha, hb]⟩
    · exact ⟨b, by simp, hb⟩
    · exact ⟨a, by simp, ha⟩
    · exact ⟨a, by simp, ha⟩
  · have hv := h α hα
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b
    · exact ⟨litNeg a, by simp, by simp [evalLitVal_litNeg, ha]⟩
    · exact ⟨litNeg a, by simp, by simp [evalLitVal_litNeg, ha]⟩
    · exact ⟨litNeg b, by simp, by simp [evalLitVal_litNeg, hb]⟩
    · exact ⟨litNeg g, by simp, by simp [evalLitVal_litNeg, hv, ha, hb]⟩

theorem iteGateDef_of_eval_eq {f : CNF Nat} {g c t e : Nat}
    (h : ∀ α : Nat → Bool, f.Sat α →
      evalLitVal α g = if evalLitVal α c then evalLitVal α t else evalLitVal α e) :
    IteGateDef f g c t e := by
  refine ⟨entails_of_eval_mem fun α hα => ?_, entails_of_eval_mem fun α hα => ?_,
    entails_of_eval_mem fun α hα => ?_, entails_of_eval_mem fun α hα => ?_⟩
  · have hv := h α hα
    cases hc : evalLitVal α c <;> cases ht : evalLitVal α t
    · exact ⟨litNeg c, by simp, by simp [evalLitVal_litNeg, hc]⟩
    · exact ⟨litNeg c, by simp, by simp [evalLitVal_litNeg, hc]⟩
    · exact ⟨litNeg t, by simp, by simp [evalLitVal_litNeg, ht]⟩
    · exact ⟨g, by simp, by simp [hv, hc, ht]⟩
  · have hv := h α hα
    cases hc : evalLitVal α c <;> cases he : evalLitVal α e
    · exact ⟨litNeg e, by simp, by simp [evalLitVal_litNeg, he]⟩
    · exact ⟨g, by simp, by simp [hv, hc, he]⟩
    · exact ⟨c, by simp, hc⟩
    · exact ⟨c, by simp, hc⟩
  · have hv := h α hα
    cases hc : evalLitVal α c <;> cases ht : evalLitVal α t
    · exact ⟨litNeg c, by simp, by simp [evalLitVal_litNeg, hc]⟩
    · exact ⟨litNeg c, by simp, by simp [evalLitVal_litNeg, hc]⟩
    · exact ⟨litNeg g, by simp, by simp [evalLitVal_litNeg, hv, hc, ht]⟩
    · exact ⟨t, by simp, ht⟩
  · have hv := h α hα
    cases hc : evalLitVal α c <;> cases he : evalLitVal α e
    · exact ⟨litNeg g, by simp, by simp [evalLitVal_litNeg, hv, hc, he]⟩
    · exact ⟨e, by simp, he⟩
    · exact ⟨c, by simp, hc⟩
    · exact ⟨c, by simp, hc⟩

theorem iteGateDef_flip_cond {f : CNF Nat} {g c t e : Nat} (h : IteGateDef f g c t e) :
    IteGateDef f g (litNeg c) e t :=
  iteGateDef_of_eval_eq fun α hα => by
    rw [iteGateDef_eval hα h, evalLitVal_litNeg]; cases evalLitVal α c <;> rfl

theorem iteGateDef_flip_out {f : CNF Nat} {g c t e : Nat} (h : IteGateDef f g c t e) :
    IteGateDef f (litNeg g) c (litNeg t) (litNeg e) :=
  iteGateDef_of_eval_eq fun α hα => by
    rw [evalLitVal_litNeg, iteGateDef_eval hα h, evalLitVal_litNeg, evalLitVal_litNeg]
    cases evalLitVal α c <;> rfl

theorem nodup_len3_subset {xs : List Nat} {a b c : Nat}
    (_hnd : xs.Nodup) (hlen : xs.length = 3)
    (ha : a ∈ xs) (hb : b ∈ xs) (hc : c ∈ xs)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ x ∈ xs, x = a ∨ x = b ∨ x = c := by
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | _⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb hc hx
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl <;>
      simp_all
  · simp at hlen
/-- Adjacent swap of indices `j` and `j + 1` preserves `List.Perm`. -/
theorem perm_swap_adj {α : Type} {xs : List α} {j : Nat} (hj : j + 1 < xs.length) :
    List.Perm ((xs.set (j + 1) xs[j]).set j xs[j + 1]) xs := by
  have hj0 : j < xs.length := by omega
  have hsplit : xs = xs.take j ++ xs[j] :: xs[j + 1] :: xs.drop (j + 2) := by
    calc xs = xs.take j ++ xs.drop j := (List.take_append_drop j xs).symm
      _ = xs.take j ++ xs[j] :: xs.drop (j + 1) := by rw [List.drop_eq_getElem_cons hj0]
      _ = xs.take j ++ xs[j] :: xs[j + 1] :: xs.drop (j + 2) := by
            rw [List.drop_eq_getElem_cons hj]
  have hupd : (xs.set (j + 1) xs[j]).set j xs[j + 1] =
      xs.take j ++ xs[j + 1] :: xs[j] :: xs.drop (j + 2) := by
    apply List.ext_getElem
    · simp only [List.length_set, List.length_append, List.length_take, List.length_cons,
        List.length_drop]
      omega
    · intro k hk1 _
      have hk : k < xs.length := by simpa using hk1
      have htk : (xs.take j).length = j := List.length_take_of_le (by omega)
      by_cases hkj : k < j
      · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (by omega),
          List.getElem_append_left (by omega), List.getElem_take]
      · by_cases hke : k = j
        · subst hke; rw [List.getElem_set_self, List.getElem_append_right (by omega)]
          simp [htk]
        · by_cases hk1e : k = j + 1
          · subst hk1e
            rw [List.getElem_set_ne (by omega), List.getElem_set_self,
              List.getElem_append_right (by omega)]
            simp [htk]
          · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (by omega),
              List.getElem_append_right (by omega)]
            have hidx : k - (xs.take j).length = (k - j - 2) + 2 := by omega
            rw [list_getElem_congr hidx _ (by simp; omega)]
            simp [List.getElem_drop, show j + 2 + (k - j - 2) = k by omega]
  rw [hupd]; (conv => rhs; rw [hsplit])
  exact List.Perm.append_left _ (List.Perm.swap _ _ _)

/-- Insertion-sort inner-loop step: shifting `arr[j - 1]` right and moving virtual `x` left
is an adjacent swap on `arr.set j x`. -/
theorem perm_ins_step {xs : List (BitVec 32)} {j n : Nat} (x : BitVec 32)
    (hj0 : 0 < j) (hjn : j < n) (hn : n ≤ xs.length) :
    List.Perm (((xs.set j (xs[j - 1]'(by omega))).set (j - 1) x).take n)
      ((xs.set j x).take n) := by
  have hj1 : (j - 1) + 1 = j := by omega
  let ys := (xs.set j x).take n
  have hylen : ys.length = n := by simp [ys, List.length_take, Nat.min_eq_left hn]
  have hlt : (j - 1) + 1 < ys.length := by omega
  have heq : ((xs.set j (xs[j - 1]'(by omega))).set (j - 1) x).take n =
      (ys.set ((j - 1) + 1) ys[j - 1]).set (j - 1) ys[(j - 1) + 1] := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_set, ys]
    · intro k hk1 _
      have hkn : k < n := by simp only [List.length_take, List.length_set] at hk1; omega
      simp only [List.getElem_take, ys, hj1]
      by_cases hk1e : k = j - 1
      · subst hk1e; rw [List.getElem_set_self, List.getElem_set_self, List.getElem_set_self]
      · by_cases hk2e : k = j
        · subst hk2e
          rw [List.getElem_set_ne (by omega), List.getElem_set_self,
            List.getElem_set_ne (by omega), List.getElem_set_self,
            List.getElem_set_ne (by omega)]
        · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (by omega),
            List.getElem_set_ne (by omega), List.getElem_set_ne (by omega),
            List.getElem_take, List.getElem_set_ne (by omega)]
  rw [heq]; exact perm_swap_adj hlt

theorem ite_equal_branches_equiv {f : CNF Nat} {lhs0 lhs c t e r : Nat}
    (hite : IteGateDef f lhs0 c t e) (hl : LitEquiv f lhs0 lhs)
    (ht : LitEquiv f t r) (he : LitEquiv f e r) : LitEquiv f lhs r :=
  litEquiv_of_eval_eq fun α hα => by
    rw [← litEquiv_eval hα hl, iteGateDef_eval hα hite, litEquiv_eval hα ht, litEquiv_eval hα he]
    cases evalLitVal α c <;> rfl

theorem perm2_cases {α : Type} {a b c d : α} (h : List.Perm [a, b] [c, d]) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have ha : a ∈ [c, d] := h.subset (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · left; exact ⟨rfl, (List.cons.inj (List.Perm.singleton_eq h.cons_inv)).1⟩
  · right; have h2 : List.Perm [a, b] [a, c] := h.trans (List.Perm.swap a c [])
    exact ⟨rfl, (List.cons.inj (List.Perm.singleton_eq h2.cons_inv)).1⟩

theorem xor_same_var_unit {f : CNF Nat} {lhs0 x0 x1 r0 r1 : Nat} {lhs t0 t1 : BitVec 32}
    (hxor : XorGateDef f lhs0 x0 x1) (hl : LitEquiv f lhs0 lhs.toNat)
    (hperm : List.Perm [t0.toNat, t1.toNat] [r0, r1])
    (h0 : LitEquiv f x0 r0) (h1 : LitEquiv f x1 r1) (hvar : t0.toNat / 2 = t1.toNat / 2) :
    f.EntailsClause (cnfClause [(if t0 = t1 then lhs ^^^ 1#32 else lhs).toNat]) := by
  refine entails_of_eval_mem fun α hα => ?_
  have hev := xorGateDef_eval hα hxor
  rw [litEquiv_eval hα hl, litEquiv_eval hα h0, litEquiv_eval hα h1] at hev
  have hteq : (evalLitVal α r0 != evalLitVal α r1) =
      (evalLitVal α t0.toNat != evalLitVal α t1.toNat) := by
    rcases perm2_cases hperm with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · rw [e0, e1]
    · rw [e0, e1]; cases evalLitVal α r0 <;> cases evalLitVal α r1 <;> rfl
  rw [hteq] at hev
  rcases (litVar_eq_iff t0.toNat t1.toNat).mp hvar with heq | hneg
  · have hbv : t0 = t1 := BitVec.eq_of_toNat_eq heq
    simp only [hbv, ↓reduceIte, bv32_xor1_eq_litNeg]; refine ⟨litNeg lhs.toNat, by simp, ?_⟩
    rw [evalLitVal_litNeg, hev, heq]; cases evalLitVal α t1.toNat <;> rfl
  · have hbv : t0 ≠ t1 := fun h => by
      have : t0.toNat = t1.toNat := congrArg BitVec.toNat h
      rw [this] at hneg; exact litNeg_ne_self t1.toNat hneg.symm
    simp only [hbv, ↓reduceIte]; refine ⟨lhs.toNat, by simp, ?_⟩
    rw [hev, hneg, evalLitVal_litNeg]; cases evalLitVal α t1.toNat <;> rfl

theorem list_take2_eq {α : Type} {xs : List α} (h : 2 ≤ xs.length) :
    xs.take 2 = [xs[0]'(by omega), xs[1]'(by omega)] := by
  cases xs with
  | nil => simp at h
  | cons a xs' => cases xs' with | nil => simp at h | cons b _ => rfl

theorem bv64_and_sub1_lt {x ht_sz : BitVec 64} (hpos : 0 < ht_sz.toNat) :
    (x &&& (ht_sz - 1#64)).toNat < ht_sz.toNat := by
  have hsub : (ht_sz - 1#64).toNat = ht_sz.toNat - 1 := by bv_omega
  rw [BitVec.toNat_and, hsub]
  have hle : x.toNat &&& (ht_sz.toNat - 1) ≤ ht_sz.toNat - 1 := Nat.and_le_right; omega

theorem bv64_add_zext32 {p : BitVec 64} {k : Nat} {i : BitVec 32}
    (h : p.toNat + k + i.toNat < 2 ^ 64) :
    (p + BitVec.ofNat 64 k + i.setWidth 64).toNat = p.toNat + k + i.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_add, bv_zext32_toNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

end FullCongHelpers

open FullCongHelpers

/-! ## 4. `Func.wp` Proofs #1, #2, #4 (`find`, `merge`, `sort_u32`) -/

/-- **#1 (`full_cong_find`)**: union-find root search + path compression preserves `CongReprInv`. -/
theorem full_cong_find_wp (Γ : Env) :
    ∀ args m Q X, fullCongFindSpec args m Q X → Func.wp Γ full_cong_find_body args m Q X := by
  rintro ⟨repr_ptr, l, ⟨⟩⟩ m0 Q X ⟨F_cur, nlits, repr, R, hinv, hl_lt, hm0, hQ⟩
  have hwf := hinv.1; have hlen := hwf.1
  have hl_len : l.toNat < repr.length := by omega
  have hi32 : i32.bytes = 4 := rfl; fc_steps
  refine wp_loop_inv
    (fun (r, ()) ml =>
      r.toNat < nlits ∧ r.toNat ≤ l.toNat ∧ ml = m0 ∧
      congRoot repr (nlits + 1) r.toNat = congRoot repr (nlits + 1) l.toNat)
    (fun (r, ()) _ => r.toNat)
    (fun J hJ => by
      fc_steps; exact hJ (l, ()) m0 ⟨hl_lt, Nat.le_refl _, rfl, rfl⟩)
    (fun J (r, ()) ml ⟨hr_lt, hr_le, hml, hroot_eq⟩ ih => ?_)
  subst hml; have hr_arr : r.toNat < repr.length := by omega
  have hstep_le : (repr[r.toNat]'hr_arr).toNat ≤ r.toNat := by
    have := hwf.2 r.toNat hr_lt
    rwa [List.getElem?_eq_getElem hr_arr, Option.getD_some] at this
  fc_steps
  · have hne_nat : (repr[r.toNat]'hr_arr).toNat ≠ r.toNat := fun heq =>
      hc (BitVec.eq_of_toNat_eq heq)
    have hlt_r : (repr[r.toNat]'hr_arr).toNat < r.toNat := by omega
    have hnext_root : congRoot repr (nlits + 1) (repr[r.toNat]'hr_arr).toNat =
        congRoot repr (nlits + 1) l.toNat := by
      rw [← hroot_eq, congRoot_fuel_ge hwf hr_lt (by omega : r.toNat < nlits + 1)
        (by omega : r.toNat < nlits + 2)]
      simp only [congRoot, List.getElem?_eq_getElem hr_arr, Option.getD_some, hne_nat, ↓reduceIte]
    exact ih (repr[r.toNat]'hr_arr, ()) ml hlt_r ⟨by omega, by omega, rfl, hnext_root⟩
  · have hfix_bv : repr[r.toNat]'hr_arr = r := by grind
    have hfix : (repr[r.toNat]?.getD 0#32).toNat = r.toNat := by
      rw [List.getElem?_eq_getElem hr_arr, Option.getD_some, hfix_bv]
    have hreq : r.toNat = congRoot repr (nlits + 1) l.toNat := by
      rw [← hroot_eq, congRoot_eq_of_fixed hfix]
    have hle_eq : LitEquiv (cnfOfClauses F_cur) l.toNat r.toNat := by
      rw [hreq]; exact congRoot_litEquiv hinv hl_lt
    refine wp_loop_inv
      (fun (cur, ()) mc => ∃ reprc : List (BitVec 32),
        reprc.length = repr.length ∧ cur.toNat < nlits ∧ r.toNat ≤ cur.toNat ∧
        CongReprInv F_cur nlits reprc ∧
        congRoot repr (nlits + 1) cur.toNat = r.toNat ∧
        (∀ x ≤ cur.toNat, reprc[x]? = repr[x]?) ∧
        (array (t := i32) repr_ptr reprc ⋆ R) mc)
      (fun (cur, ()) _ => cur.toNat)
      (fun J2 hJ2 => by
        fc_steps
        exact hJ2 (l, ()) ml ⟨repr, rfl, hl_lt, hr_le, hinv, hreq.symm, fun _ _ => rfl, hm0⟩)
      (fun J2 (cur, ()) mc ⟨reprc, hlen_c, hcur_lt, hr_cur, hinvc, hcur_root, hpref, hmc⟩ ih2 => ?_)
    have hcur_arr : cur.toNat < reprc.length := by omega
    have hcur_arr0 : cur.toNat < repr.length := by omega
    have hget_eq : reprc[cur.toNat]'hcur_arr = repr[cur.toNat]'hcur_arr0 := by
      have h := hpref cur.toNat (Nat.le_refl _)
      rw [List.getElem?_eq_getElem hcur_arr, List.getElem?_eq_getElem hcur_arr0] at h
      exact Option.some.inj h
    fc_steps
    · have hne_r : (repr[cur.toNat]'hcur_arr0).toNat ≠ r.toNat := fun heq =>
        hc (BitVec.eq_of_toNat_eq (by rw [hget_eq]; exact heq))
      have hne_cur : (repr[cur.toNat]'hcur_arr0).toNat ≠ cur.toNat := by
        intro hself
        have hfix_c : (repr[cur.toNat]?.getD 0#32).toNat = cur.toNat := by
          rw [List.getElem?_eq_getElem hcur_arr0, Option.getD_some, hself]
        rw [congRoot_eq_of_fixed hfix_c] at hcur_root; exact hne_r (hself.trans hcur_root)
      have hle_cur : (repr[cur.toNat]'hcur_arr0).toNat ≤ cur.toNat := by
        have := hwf.2 cur.toNat hcur_lt
        rwa [List.getElem?_eq_getElem hcur_arr0, Option.getD_some] at this
      have hn_lt : (repr[cur.toNat]'hcur_arr0).toNat < cur.toNat := by omega
      have hn_root : congRoot repr (nlits + 1) (repr[cur.toNat]'hcur_arr0).toNat = r.toNat := by
        rw [← hcur_root, congRoot_fuel_ge hwf hcur_lt (by omega : cur.toNat < nlits + 1)
          (by omega : cur.toNat < nlits + 2)]
        simp only [congRoot, List.getElem?_eq_getElem hcur_arr0, Option.getD_some,
          hne_cur, ↓reduceIte]
      have hr_le_n : r.toNat ≤ (repr[cur.toNat]'hcur_arr0).toNat := by
        rw [← hn_root]; exact congRoot_le hwf (by omega)
      have hcur_eqv : LitEquiv (cnfOfClauses F_cur) cur.toNat r.toNat := by
        rw [← hcur_root]; exact congRoot_litEquiv hinv hcur_lt
      have hinvc' : CongReprInv F_cur nlits (reprc.set cur.toNat r) := by
        refine ⟨⟨by simp [hlen_c, hlen], fun x hx => ?_⟩, fun x hx => ?_⟩
        · by_cases hxc : x = cur.toNat
          · subst hxc; rw [List.getElem?_set_self hcur_arr, Option.getD_some]; exact hr_cur
          · rw [List.getElem?_set_ne (Ne.symm hxc)]; exact hinvc.1.2 x hx
        · by_cases hxc : x = cur.toNat
          · subst hxc; rw [List.getElem?_set_self hcur_arr, Option.getD_some]; exact hcur_eqv
          · rw [List.getElem?_set_ne (Ne.symm hxc)]; exact hinvc.2 x hx
      have hpref' : ∀ x ≤ (reprc[cur.toNat]'hcur_arr).toNat,
          (reprc.set cur.toNat r)[x]? = repr[x]? := fun x hx => by
        rw [hget_eq] at hx; rw [List.getElem?_set_ne (by omega)]
        exact hpref x (by omega)
      have hm_set : (array (t := i32) repr_ptr (reprc.set cur.toNat r) ⋆ R) m := by
        rw [bv_zext32_toNat] at hm; exact hm
      exact ih2 (reprc[cur.toNat]'hcur_arr, ()) m (by rw [hget_eq]; exact hn_lt)
        ⟨reprc.set cur.toNat r, by simp [hlen_c], by rw [hget_eq]; omega,
         by rw [hget_eq]; exact hr_le_n, hinvc', by rw [hget_eq]; exact hn_root, hpref', hm_set⟩
    · exact hQ r reprc mc hlen_c hinvc hr_le hr_lt hle_eq hmc

/-- **#2 (`full_cong_merge`)**: merges two semantically equivalent literals in `repr` and emits
entailed binary clauses (or flags `inconsistent = 1` on `ra = rb ^ 1` clash). -/
theorem full_cong_merge_wp (Γ : Env)
    (hFind : ∀ args m Q X, fullCongFindSpec args m Q X →
      Γ "full_cong_find" [i64, i32] [i32] args m Q X)
    (hAddBin : ∀ args m Q X, fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullCongMergeSpec args m Q X → Func.wp Γ full_cong_merge_body args m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hmk, hnd, hext, hcl0, hdm, hrepr, ha, hb, heqv, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx; have hcv_le := hlen.core_ok.cur_vars_le
  have hrl := hlen.core_ok.repr_len; fc_steps; c0_call hFind
  refine ⟨F_cur, 2 * s.core.cur_vars, s.core.repr, FullReprRest c s ⋆ R, hrepr, ha,
    focus_full_repr hm0, fun ra repr1 m1 hrl1 hrepr1 _ hra_lt ha_ra hm1 => ?_⟩
  let s1 : FullState := { s with core := { s.core with repr := repr1 } }
  have hlen1 : s1.LengthsOk c := ⟨{ hlen.core_ok with repr_len := by simp [s1, hrl1, hrl] },
    hlen.scratch_ok⟩
  have hw1 : FullWitnessInv c F0 F_cur s1.core := fullWitnessInv_with_repr hw repr1
  have hm1' : (FullMem c s1 ⋆ R) m1 := unfocus_full_repr hm1; c0_call hFind
  refine ⟨F_cur, 2 * s.core.cur_vars, repr1, FullReprRest c s1 ⋆ R, hrepr1, hb,
    focus_full_repr hm1', fun rb repr2 m2 hrl2 hrepr2 _ hrb_lt hb_rb hm2 => ?_⟩
  let s2 : FullState := { s1 with core := { s1.core with repr := repr2 } }
  have hlen2 : s2.LengthsOk c := ⟨{ hlen1.core_ok with repr_len := by simp [s2, hrl2, hrl1, hrl] },
    hlen.scratch_ok⟩
  have hw2 : FullWitnessInv c F0 F_cur s2.core := fullWitnessInv_with_repr hw1 repr2
  have hm2' : (FullMem c s2 ⋆ R) m2 := unfocus_full_repr hm2; clear hm0 hm1 hm1' hm2
  have hrab_eqv : LitEquiv (cnfOfClauses F_cur) ra.toNat rb.toNat :=
    ha_ra.symm.trans (heqv.trans hb_rb)
  fc_split
  · -- ra == rb -> return false
    fc_steps
    exact hQ false s2 m2 hlen2 hw2 hmk hnd hext hcl0 hdm rfl rfl rfl rfl rfl rfl hrepr2 hm2'
  · have hne_eq := hc; clear hc; fc_split
    · -- ra == rb ^ 1 -> inconsistent = 1, return true
      have heq_neg : ra = rb ^^^ 1#32 := by grind
      have hunsat : (cnfOfClauses F_cur).Unsat := by
        have hneg : LitEquiv (cnfOfClauses F_cur) rb.toNat (litNeg rb.toNat) := by
          rw [← bv32_xor1_eq_litNeg rb, ← heq_neg]; exact hrab_eqv.symm
        exact unsat_of_litEquiv_neg hneg
      fc_steps; let s3 : FullState := { s2 with core := { s2.core with inconsistent := 1#64 } }
      have hlen3 : s3.LengthsOk c := ⟨{ hlen2.core_ok with vals_len := hlen2.core_ok.vals_len },
        hlen2.scratch_ok⟩
      have hw3 : FullWitnessInv c F0 F_cur s3.core :=
        fullWitnessInv_with_inconsistent hw2 1#64 (fun _ => hunsat)
      exact hQ true s3 m hlen3 hw3 hmk hnd hext hcl0 hdm rfl rfl rfl rfl rfl rfl hrepr2 hm
    · -- ra != rb ∧ ra != rb ^ 1 -> swap join point
      have hne_neg := hc; clear hc; fc_to_group
      refine wp_join_group (ts := [i32, i32])
        (fun (ra', rb', ()) mj =>
          mj = m2 ∧ ra'.toNat < rb'.toNat ∧ rb'.toNat < 2 * s.core.cur_vars ∧
          ra' ≠ rb' ^^^ 1#32 ∧ LitEquiv (cnfOfClauses F_cur) ra'.toNat rb'.toNat)
        ?_ ?_
      · rintro _ ⟨ra', rb', ⟨⟩⟩ mj ⟨rfl, hlt_ab, hrb'_lt, hne_n', heqv'⟩
        have hra'_lt : ra'.toNat < 2 * s.core.cur_vars := by omega
        have hdiv := bv32_lt_and_ne_xor1_div_lt hlt_ab hne_n'
        have hnrb_lt : (rb' ^^^ 1#32).toNat < 2 * s.core.cur_vars := by
          rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hrb'_lt
        have hnra_lt : (ra' ^^^ 1#32).toNat < 2 * s.core.cur_vars := by
          rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hra'_lt
        have hrb_arr : rb'.toNat < s2.core.repr.length := by
          have := hlen2.core_ok.repr_len; omega
        have hnrb_arr : (rb' ^^^ 1#32).toNat < s2.core.repr.length := by
          have := hlen2.core_ok.repr_len; omega
        have hrb_z : (rb'.setWidth 64).toNat < s2.core.repr.length := by
          rw [bv_zext32_toNat]; exact hrb_arr
        have hnrb_z : ((rb' ^^^ 1).setWidth 64).toNat <
            (s2.core.repr.set (rb'.setWidth 64).toNat ra').length := by
          rw [List.length_set, bv_zext32_toNat]; exact hnrb_arr
        fc_steps; let repr3 := (repr2.set rb'.toNat ra').set (rb' ^^^ 1#32).toNat (ra' ^^^ 1#32)
        let s3 : FullState := { s2 with core := { s2.core with repr := repr3 } }
        have hlen3 : s3.LengthsOk c :=
          ⟨{ hlen2.core_ok with repr_len := by simpa [s3, repr3] using hlen2.core_ok.repr_len },
           hlen2.scratch_ok⟩
        have hw3 : FullWitnessInv c F0 F_cur s3.core := fullWitnessInv_with_repr hw2 repr3
        have hrepr3 : CongReprInv F_cur (2 * s.core.cur_vars) repr3 := by
          have hlen3_r : repr3.length = repr2.length := by simp [repr3]
          refine ⟨⟨by omega, fun x hx => ?_⟩, fun x hx => ?_⟩
          · by_cases hx1 : x = (rb' ^^^ 1#32).toNat
            · subst hx1; dsimp only [repr3]
              rw [List.getElem?_set_self (by simpa using hnrb_arr), Option.getD_some]; omega
            · dsimp only [repr3]; rw [List.getElem?_set_ne (Ne.symm hx1)]
              by_cases hx2 : x = rb'.toNat
              · subst hx2; rw [List.getElem?_set_self hrb_arr, Option.getD_some]; omega
              · rw [List.getElem?_set_ne (Ne.symm hx2)]; exact hrepr2.1.2 x hx
          · by_cases hx1 : x = (rb' ^^^ 1#32).toNat
            · subst hx1; dsimp only [repr3]
              rw [List.getElem?_set_self (by simpa using hnrb_arr), Option.getD_some,
                bv32_xor1_eq_litNeg, bv32_xor1_eq_litNeg]
              exact heqv'.symm.neg
            · dsimp only [repr3]; rw [List.getElem?_set_ne (Ne.symm hx1)]
              by_cases hx2 : x = rb'.toNat
              · subst hx2; rw [List.getElem?_set_self hrb_arr, Option.getD_some]; exact heqv'.symm
              · rw [List.getElem?_set_ne (Ne.symm hx2)]; exact hrepr2.2 x hx
        have hm3 : (FullMem c s3 ⋆ R) m := by
          rw [bv_zext32_toNat, bv_zext32_toNat] at hm; exact hm
        c0_call hAddBin
        refine ⟨c, F0, F_cur, s3, R, rfl, hlen3, hw3, hcl0, hnra_lt, hrb'_lt,
          by rw [bv32_xor1_litNeg]; exact heqv'.1, hm3,
          fun r1 s4 m4 hlen4 hw4 hcl4 hdm4 hcv4 hfl4 hmrk4 hlm4 har4 hal4 hrep4 htmp4 hscr4
            hll4 hel4 hr1_20 hm4 => ?_⟩
        have hmk4 : FullLitMarksClear c s4 := fullLitMarksClear_of_eq hmk hmrk4 hlm4
        have hnd4 : FullArenaVarsNodup s4 := fullArenaVarsNodup_of_eq hnd har4 hal4
        have hext4 : FullExtScratchOk c s4 := fullExtScratchOk_of_eq hext har4 hal4 hll4 hel4
        fc_steps
        · -- first full_add_bin returned 20
          have hunsat4 : (cnfOfClauses F_cur).Unsat := hw4.inconsistent_sound (hr1_20 (by grind))
          let s5 : FullState := { s4 with core := { s4.core with inconsistent := 1#64 } }
          have hlen5 : s5.LengthsOk c := ⟨{ hlen4.core_ok with vals_len := hlen4.core_ok.vals_len },
            hlen4.scratch_ok⟩
          have hw5 : FullWitnessInv c F0 F_cur s5.core :=
            fullWitnessInv_with_inconsistent hw4 1#64 (fun _ => hunsat4)
          exact hQ true s5 m hlen5 hw5 hmk4 hnd4 hext4 hcl4 (hdm4 ▸ hdm) hcv4 hfl4 har4 hal4 htmp4
            hscr4 (by rw [show s5.core.cur_vars = s.core.cur_vars from hcv4,
              show s5.core.repr = repr3 from hrep4]; exact hrepr3) hm
        · -- second full_add_bin
          c0_call hAddBin
          refine ⟨c, F0, F_cur, s4, R, rfl, hlen4, hw4, hcl4,
            hcv4 ▸ hra'_lt, hcv4 ▸ hnrb_lt,
            by rw [bv32_xor1_litNeg]; exact heqv'.2, hm4,
            fun r2 s5 m5 hlen5 hw5 hcl5 hdm5 hcv5 hfl5 hmrk5 hlm5 har5 hal5 hrep5 htmp5 hscr5
              hll5 hel5 hr2_20 hm5 => ?_⟩
          have hmk5 : FullLitMarksClear c s5 := fullLitMarksClear_of_eq hmk4 hmrk5 hlm5
          have hnd5 : FullArenaVarsNodup s5 := fullArenaVarsNodup_of_eq hnd4 har5 hal5
          have hext5 : FullExtScratchOk c s5 := fullExtScratchOk_of_eq hext4 har5 hal5 hll5 hel5
          fc_steps
          · have hunsat5 : (cnfOfClauses F_cur).Unsat := hw5.inconsistent_sound (hr2_20 (by grind))
            let s6 : FullState := { s5 with core := { s5.core with inconsistent := 1#64 } }
            have hlen6 : s6.LengthsOk c :=
              ⟨{ hlen5.core_ok with vals_len := hlen5.core_ok.vals_len }, hlen5.scratch_ok⟩
            have hw6 : FullWitnessInv c F0 F_cur s6.core :=
              fullWitnessInv_with_inconsistent hw5 1#64 (fun _ => hunsat5)
            exact hQ true s6 m hlen6 hw6 hmk5 hnd5 hext5 hcl5 (hdm5.trans hdm4 ▸ hdm)
              (hcv5.trans hcv4) (hfl5.trans hfl4) (har5.trans har4) (hal5.trans hal4)
              (htmp5.trans htmp4) (hscr5.trans hscr4)
              (by rw [show s6.core.cur_vars = s.core.cur_vars from hcv5.trans hcv4,
                      show s6.core.repr = repr3 from hrep5.trans hrep4]; exact hrepr3)
              hm
          · let s6 : FullState := { s5 with scratch :=
              { s5.scratch with cong_cnt := s5.scratch.cong_cnt + 1#64 } }
            have hlen6 : s6.LengthsOk c := ⟨hlen5.core_ok,
              { hlen5.scratch_ok with walk_vals_len := hlen5.scratch_ok.walk_vals_len }⟩
            exact hQ true s6 m hlen6 hw5 hmk5 hnd5 hext5 hcl5 (hdm5.trans hdm4 ▸ hdm)
              (hcv5.trans hcv4) (hfl5.trans hfl4) (har5.trans har4) (hal5.trans hal4)
              (htmp5.trans htmp4) (hscr5.trans hscr4)
              (by rw [show s6.core.cur_vars = s.core.cur_vars from hcv5.trans hcv4,
                      show s6.core.repr = repr3 from hrep5.trans hrep4]; exact hrepr3)
              hm
      · intro J hJ; fc_steps
        · exact hJ (rb, ra, ()) m2 ⟨rfl, by c0_bound, hra_lt, bv32_xor1_symm hne_neg, hrab_eqv.symm⟩
        · have hne_n : ra.toNat ≠ rb.toNat := fun h => hne_eq (BitVec.eq_of_toNat_eq h)
          exact hJ (ra, rb, ()) m2 ⟨rfl, by c0_bound, hrb_lt, hne_neg, hrab_eqv⟩

/-- **#4 (`full_sort_u32`)**: insertion sort on `arr[0 ..< n)` preserves length, suffix, and
permutation (`List.Perm`). -/
theorem full_sort_u32_wp (Γ : Env) :
    ∀ args m Q X, fullSortU32Spec args m Q X → Func.wp Γ full_sort_u32_body args m Q X := by
  rintro ⟨arr_ptr, n, ⟨⟩⟩ m0 Q X ⟨arr, R, hn_le, hm0, hQ⟩
  have hi32 : i32.bytes = 4 := rfl; fc_steps
  refine wp_loop_inv
    (fun (i, ()) mi => ∃ arri : List (BitVec 32),
      arri.length = arr.length ∧
      (1 ≤ i.toNat ∧ (n.toNat = 0 → i.toNat = 1) ∧ (1 ≤ n.toNat → i.toNat ≤ n.toNat)) ∧
      List.Perm (arri.take n.toNat) (arr.take n.toNat) ∧
      (∀ k, n.toNat ≤ k → arri[k]? = arr[k]?) ∧
      (array (t := i32) arr_ptr arri ⋆ R) mi)
    (fun (i, ()) _ => n.toNat - i.toNat)
    (fun J hJ => by
      fc_steps
      exact hJ (1#32, ()) m0 ⟨arr, rfl, ⟨by decide, fun _ => rfl, fun h => h⟩,
        List.Perm.refl _, fun _ _ => rfl, hm0⟩)
    (fun J (i, ()) mi ⟨arri, hlen_i, ⟨hi1, hnz, hi_le⟩, hperm_i, hsuf_i, hmi⟩ ih => ?_)
  fc_split
  · -- i < n
    have hi_lt : i.toNat < n.toNat := by bv_omega
    have hi_arr : i.toNat < arri.length := by omega
    let x := arri[i.toNat]'hi_arr; fc_steps
    refine wp_loop_inv
      (fun (j, ()) mj => ∃ arrj : List (BitVec 32),
        arrj.length = arr.length ∧ j.toNat ≤ i.toNat ∧
        List.Perm ((arrj.set j.toNat x).take n.toNat) (arri.take n.toNat) ∧
        (∀ k, n.toNat ≤ k → arrj[k]? = arri[k]?) ∧
        (array (t := i32) arr_ptr arrj ⋆ R) mj)
      (fun (j, ()) _ => j.toNat)
      (fun J2 hJ2 => by
        fc_steps; have hself : arri.set i.toNat x = arri := List.set_getElem_self hi_arr
        exact hJ2 (i, ()) mi ⟨arri, hlen_i, Nat.le_refl _, by rw [hself], fun _ _ => rfl, hmi⟩)
      (fun J2 (j, ()) mj ⟨arrj, hlen_j, hj_le, hperm_j, hsuf_j, hmj⟩ ih2 => ?_)
    have hj_arr : j.toNat < arrj.length := by omega
    fc_to_group; refine wp_join_group (ts := []) (fun () m' => m' = mj) ?_ ?_
    · rintro _ ⟨⟩ _ rfl
      fc_steps; have hi1_n : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
      have hx_eq : arri[(i.setWidth 64).toNat]'(by rw [bv_zext32_toNat]; omega) = x :=
        list_getElem_congr (bv_zext32_toNat i) _ _
      have hm_set : (array (t := i32) arr_ptr (arrj.set j.toNat x) ⋆ R) m := by
        rw [bv_zext32_toNat, hx_eq] at hm; exact hm
      exact ih (i + 1#32, ()) m (by dsimp only; omega)
        ⟨arrj.set j.toNat x, by simp [hlen_j],
         ⟨by omega, fun h => by omega, fun _ => by omega⟩,
         hperm_j.trans hperm_i,
         fun k hk => by
           rw [List.getElem?_set_ne (by omega)]
           exact (hsuf_j k hk).trans (hsuf_i k hk),
         hm_set⟩
    · intro Jout hJout
      fc_split
      · -- j > 0
        have hj_pos : 0 < j.toNat := by bv_omega
        have hj1_n : (j - 1#32).toNat = j.toNat - 1 := by bv_omega
        have hj1_arr : (j - 1#32).toNat < arrj.length := by omega
        fc_steps
        · -- arrj[j - 1] > x -> shift right and continue
          have hstep := perm_ins_step (xs := arrj) (j := j.toNat) (n := n.toNat) x
            hj_pos (by omega) (by omega)
          have hv_eq : arrj[((j - 1).setWidth 64).toNat]'(by rw [bv_zext32_toNat]; omega) =
              arrj[j.toNat - 1]'(by omega) :=
            list_getElem_congr (by rw [bv_zext32_toNat]; exact hj1_n) _ _
          have hm_set : (array (t := i32) arr_ptr
              (arrj.set j.toNat (arrj[j.toNat - 1]'(by omega))) ⋆ R) m := by
            rw [bv_zext32_toNat, hv_eq] at hm; exact hm
          exact ih2 (j - 1#32, ()) m (by dsimp only; omega)
            ⟨arrj.set j.toNat (arrj[j.toNat - 1]'(by omega)), by simp [hlen_j], by omega,
             by rw [hj1_n]; exact hstep.trans hperm_j,
             fun k hk => by rw [List.getElem?_set_ne (by omega)]; exact hsuf_j k hk, hm_set⟩
        · exact hJout () mj rfl
      · fc_steps; exact hJout () mj rfl
  · -- i >= n -> return
    fc_steps; exact hQ arri mi hlen_i hperm_i hsuf_i hmi

end LeanQbe.T.Examples.Kissat.Full
