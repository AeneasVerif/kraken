module

public import LeanQbe.T.Examples.Kissat.FullM6CongSubst
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas2
public import LeanQbe.T.Examples.Kissat.FullM5DenseSafeProof0
import LeanQbe.T.Examples.Kissat.FullSccLemmas2
import LeanQbe.T.Examples.Kissat.FullCongLemmas1
import LeanQbe.T.Examples.Kissat.FullCongLemmas2
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Agrees

/-!
# Kissat M6 Congruence Closure & 2-Round Substitute Proofs — Part 0

Defines shared M6 `@[expose]` invariants/specs (`XorListGateDef`, `M6GateAt`, `M6GateSeqOk`,
`M6CongHtInv`, `M6CtrlLayout`, `M6OccNodesOk`, `m6Cong*Spec`), pure XOR/parity/gate/worklist
lemmas, and parametric `(Γ : Env)` `Func.wp` proofs for the 4 substitute / Tarjan SCC functions
(UNSAT soundness + `ModuleOk` scope ONLY):
1. `full_subst_rewrite_bins` (`full_subst_rewrite_bins_wp`)
2. `full_subst_rewrite_ar` (`full_subst_rewrite_ar_wp`)
3. `full_tarjan_scc` (`full_tarjan_scc_fast_wp`, `full_tarjan_scc_wp`)
4. `full_substitute` (`full_substitute_wp`, `2`-round loop)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6CongSubst

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.Full.FullSccHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open Kraken.Bedrock2.Test

/-! ## 1. M6 Gate, XOR-List, Occurrence-Worklist & Per-Function `Spec` Contracts -/

section Specs

/-- Boolean XOR sum of literals in `xs` under assignment `α`. -/
def xorEvalList (α : Nat → Bool) (xs : List Nat) : Bool :=
  xs.foldr (fun x acc => evalLitVal α x != acc) false

theorem xorEvalList_nil (α : Nat → Bool) : xorEvalList α [] = false := rfl

theorem xorEvalList_cons (α : Nat → Bool) (x : Nat) (xs : List Nat) :
    xorEvalList α (x :: xs) = (evalLitVal α x != xorEvalList α xs) := rfl

/-- Semantic multi-input XOR gate definition: `g ↔ (xs[0] ⊕ xs[1] ⊕ ...)` in every model of `f`. -/
def XorListGateDef (f : CNF Nat) (g : Nat) (xs : List Nat) : Prop :=
  ∀ α : Nat → Bool, f.Sat α → evalLitVal α g = xorEvalList α xs

/-- Valid M6 extracted gate (`arity ≤ 31` for AND, `2 ≤ arity ≤ 4` for XOR, `3` for ITE). -/
def M6GateAt (F_cur : List (List Nat)) (cur_vars : Nat) (scr : List (BitVec 32))
    (g_len g : Nat) : Prop :=
  ∃ (lhs mword : BitVec 32),
    scr[g]? = some lhs ∧ scr[g + 1]? = some mword ∧
    lhs.toNat < 2 * cur_vars ∧
    let tag := (mword >>> 28).toNat
    let arity := (mword &&& 0xFF#32).toNat
    g + 2 + arity ≤ g_len ∧ arity ≤ cur_vars ∧ arity ≤ 31 ∧
    (∀ k < arity, ∃ r : BitVec 32, scr[g + 2 + k]? = some r ∧ r.toNat < 2 * cur_vars) ∧
    ((tag = 0 ∧ 2 ≤ arity ∧
        AndGateDef (cnfOfClauses F_cur) lhs.toNat
          (((scr.drop (g + 2)).take arity).map BitVec.toNat)) ∨
     (tag = 1 ∧ 2 ≤ arity ∧ arity ≤ 4 ∧
        XorListGateDef (cnfOfClauses F_cur) lhs.toNat
          (((scr.drop (g + 2)).take arity).map BitVec.toNat)) ∨
     (tag = 2 ∧ arity = 3 ∧
        IteGateDef (cnfOfClauses F_cur) lhs.toNat
          (scr[g + 2]?.getD 0#32).toNat (scr[g + 3]?.getD 0#32).toNat
          (scr[g + 4]?.getD 0#32).toNat))

/-- Contiguous sequence of valid M6 gates in `scr[g ..< g_len)`. -/
inductive M6GateSeqOk (F_cur : List (List Nat)) (cur_vars : Nat) (scr : List (BitVec 32))
    (g_len : Nat) : Nat → Prop where
  | done : M6GateSeqOk F_cur cur_vars scr g_len g_len
  | step {g : Nat} (hg : M6GateAt F_cur cur_vars scr g_len g) :
      M6GateSeqOk F_cur cur_vars scr g_len
        (g + 2 + ((scr[g + 1]?.getD 0#32) &&& 0xFF#32).toNat) →
      M6GateSeqOk F_cur cur_vars scr g_len g

/-- Every non-empty hash slot in `scr[ht_off ..< ht_off + ht_sz)` points to an M6 gate in
`scr0[0 ..< g_len)`. -/
def M6CongHtInv (F_cur : List (List Nat)) (cur_vars : Nat) (scr0 scr : List (BitVec 32))
    (g_len ht_off ht_sz : Nat) : Prop :=
  ∀ k < ht_sz,
    let ent := scr[ht_off + k]?.getD 0xFFFFFFFF#32
    ent = 0xFFFFFFFF#32 ∨ M6GateAt F_cur cur_vars scr0 g_len ent.toNat

/-- Valid disjoint layout of worklist control words, FIFO queue, `inq`, `bkt`, and HT inside
`scr[ctrl_off ..< ht_off + ht_sz)`. -/
def M6CtrlLayout (c : FullCfg) (scr : List (BitVec 32)) (g_len ctrl_off occ_bkt bkt_off
    inq_off q_off ht_off ht_sz : Nat) : Prop :=
  ctrl_off < c.scratch_cap ∧ ctrl_off + 8 ≤ c.scratch_cap ∧
  g_len ≤ ctrl_off ∧ g_len ≤ 0x01000000 ∧
  scr[ctrl_off]?.getD 0#32 = BitVec.ofNat 32 occ_bkt ∧
  scr[ctrl_off + 1]?.getD 0#32 = BitVec.ofNat 32 bkt_off ∧
  scr[ctrl_off + 2]?.getD 0#32 = BitVec.ofNat 32 inq_off ∧
  scr[ctrl_off + 3]?.getD 0#32 = BitVec.ofNat 32 q_off ∧
  scr[ctrl_off + 6]?.getD 0#32 = BitVec.ofNat 32 ht_off ∧
  scr[ctrl_off + 7]?.getD 0#32 = BitVec.ofNat 32 ht_sz ∧
  0 < occ_bkt ∧ occ_bkt ≤ 512 ∧ (∃ p : Nat, 1 ≤ p ∧ p ≤ 9 ∧ occ_bkt = 2 ^ p) ∧
  0 < ht_sz ∧
  ctrl_off + 8 ≤ q_off ∧ q_off + occ_bkt ≤ inq_off ∧
  inq_off + occ_bkt ≤ bkt_off ∧ bkt_off + occ_bkt ≤ ht_off ∧
  ht_off + ht_sz ≤ c.scratch_cap ∧
  (scr[ctrl_off + 4]?.getD 0#32).toNat < occ_bkt ∧
  (scr[ctrl_off + 5]?.getD 0#32).toNat ≤ occ_bkt ∧
  (∀ k < (scr[ctrl_off + 5]?.getD 0#32).toNat,
    (scr[q_off + ((scr[ctrl_off + 4]?.getD 0#32).toNat + k) % occ_bkt]?.getD 0#32).toNat <
      occ_bkt)

/-- Queue context passed to `full_cong_enq_var` and `full_cong_eval_gate`: either inactive
(`ctrl_off = c.scratch_cap`, from `full_cong_work_step`) or a live disjoint `M6CtrlLayout`. -/
def M6QueueCtx (c : FullCfg) (scr : List (BitVec 32)) (g_len ctrl_off ht_off ht_sz : Nat) :
    Prop :=
  ctrl_off = c.scratch_cap ∨
  ∃ occ_bkt bkt_off inq_off q_off,
    M6CtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz

/-- Valid occurrence node pointer (sentinel or 2-word aligned offset in `[g_len, occ_end)`). -/
def M6OccNodePtrOk (g_len occ_end : Nat) (ptr : BitVec 32) : Prop :=
  ptr = 0xFFFFFFFF#32 ∨
  (g_len ≤ ptr.toNat ∧ ptr.toNat + 1 < occ_end ∧ (ptr.toNat - g_len) % 2 = 0)

/-- Occurrence bucket heads and 2-word occurrence nodes in `scr[g_len ..< occ_end)` point
only to valid M6 gates and valid node pointers. -/
def M6OccNodesOk (F_cur : List (List Nat)) (cv g_len occ_end ctrl_off bkt_off occ_bkt : Nat)
    (scr0 scr : List (BitVec 32)) : Prop :=
  g_len ≤ occ_end ∧ occ_end ≤ ctrl_off ∧
  (∀ b < occ_bkt, M6OccNodePtrOk g_len occ_end (scr[bkt_off + b]?.getD 0xFFFFFFFF#32)) ∧
  (∀ nd, g_len ≤ nd → nd + 1 < occ_end → (nd - g_len) % 2 = 0 →
    let entry := scr[nd]?.getD 0#32
    let gn := (entry &&& 0x00FFFFFF#32).toNat
    let slot := (entry >>> 24).toNat
    gn < g_len ∧ M6GateAt F_cur cv scr0 g_len gn ∧
    slot ≤ ((scr0[gn + 1]?.getD 0#32) &&& 0xFF#32).toNat ∧
    M6OccNodePtrOk g_len occ_end (scr[nd + 1]?.getD 0xFFFFFFFF#32))

/-- Frame preservation outside the queue buffers of `M6QueueCtx`. -/
def M6QueueFramePres (c : FullCfg) (ctrl_off : Nat) (scr scr' : List (BitVec 32)) : Prop :=
  scr'.length = scr.length ∧
  if _ : ctrl_off = c.scratch_cap then scr' = scr
  else ∃ occ_bkt bkt_off inq_off q_off ht_off ht_sz,
    scr[ctrl_off]? = some (BitVec.ofNat 32 occ_bkt) ∧
    scr[ctrl_off + 2]? = some (BitVec.ofNat 32 inq_off) ∧
    scr[ctrl_off + 3]? = some (BitVec.ofNat 32 q_off) ∧
    (∀ idx, idx ≠ ctrl_off + 5 →
      ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
      ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) →
      scr'[idx]? = scr[idx]?) ∧
    (∀ idx, bkt_off ≤ idx → idx < bkt_off + occ_bkt → scr'[idx]? = scr[idx]?) ∧
    ht_off + ht_sz ≤ scr.length

/-! ### Owned Congruence Function Contracts -/

def m6CongExtractIteSpec : Spec [i64, i32, i32, i32, i64] [i64] :=
  fun (h, c_lit, y, t, g_len, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧
      c_lit.toNat < 2 * s.core.cur_vars ∧ y.toNat < 2 * s.core.cur_vars ∧
      t.toNat < 2 * s.core.cur_vars ∧
      c_lit.toNat / 2 ≠ y.toNat / 2 ∧ c_lit.toNat / 2 ≠ t.toNat / 2 ∧
      y.toNat / 2 ≠ t.toNat / 2 ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [y.toNat, litNeg c_lit.toNat, litNeg t.toNat]) ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [litNeg y.toNat, litNeg c_lit.toNat, t.toNat]) ∧
      g_len.toNat + 5 ≤ c.scratch_cap ∧
      M6GateSeqOk F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (ret = g_len ∨ ret = g_len + 5#64) →
        (∀ idx < g_len.toNat, scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        M6GateSeqOk F_cur s.core.cur_vars scr' ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

def m6CongEmitXorSpec : Spec [i64, i64, i32, i32, i32] [i64] :=
  fun (scr_ptr, g_len, x0, x1, x2, ()) m Q _ =>
    ∃ (F_cur : List (List Nat)) (cur_vars : Nat) (scr : List (BitVec 32)) (R : Mem 64 → Prop),
      x0.toNat < 2 * cur_vars ∧ x1.toNat < 2 * cur_vars ∧ x2.toNat < 2 * cur_vars ∧
      2 ≤ cur_vars ∧ g_len.toNat + 4 ≤ scr.length ∧ scr.length < 2 ^ 32 ∧
      XorGateDef (cnfOfClauses F_cur) (litNeg x0.toNat) x1.toNat x2.toNat ∧
      M6GateSeqOk F_cur cur_vars scr g_len.toNat 0 ∧
      (array (t := i32) scr_ptr scr ⋆ R) m ∧
      ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
        scr'.length = scr.length →
        (∀ idx < g_len.toNat, scr'[idx]? = scr[idx]?) →
        M6GateSeqOk F_cur cur_vars scr' (g_len.toNat + 4) 0 →
        (array (t := i32) scr_ptr scr' ⋆ R) m' → Q (g_len + 4#64, ()) m'

def m6CongHasClauseKSpec : Spec [i64, i32] [.bool] := fun (h, k, ()) m Q _ =>
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

def m6CongExtractXorKSpec : Spec [i64, i32, i32, i64, i64] [i64] :=
  fun (h, k, neg_p, g_len, g_cap, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧
      3 ≤ k.toNat ∧ k.toNat ≤ 5 ∧ k.toNat ≤ s.core.cur_vars ∧
      g_len.toNat ≤ g_cap.toNat ∧ g_cap.toNat ≤ c.scratch_cap ∧
      M6GateSeqOk F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
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
        M6GateSeqOk F_cur s.core.cur_vars s'.scratch.scratch_buf ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

def m6CongTryXorIteSpec : Spec [i64, i32, i32, i32, i64, i64] [i64] :=
  fun (h, a, b, cl, g_len, g_cap, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧
      a.toNat < 2 * s.core.cur_vars ∧ b.toNat < 2 * s.core.cur_vars ∧
      cl.toNat < 2 * s.core.cur_vars ∧
      a.toNat / 2 ≠ b.toNat / 2 ∧ a.toNat / 2 ≠ cl.toNat / 2 ∧ b.toNat / 2 ≠ cl.toNat / 2 ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat, cl.toNat]) ∧
      g_len.toNat + 5 ≤ g_cap.toNat ∧ g_cap.toNat ≤ c.scratch_cap ∧
      M6GateSeqOk F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        g_len.toNat ≤ ret.toNat → ret.toNat ≤ g_cap.toNat →
        (∀ idx < g_len.toNat, scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        M6GateSeqOk F_cur s.core.cur_vars scr' ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

def m6CongCountBinsSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧
    (∀ l < 2 * s.core.cur_vars,
      fullWatchOffCore s.core l + fullWatchSizeCore s.core l ≤ c.wcap) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ ws1' m',
      ws1'.length = 2 * c.max_vars →
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m' →
      Q () m'

def m6CongEbMatchSpec : Spec [i64, i32, i32, i32] [.bool] := fun (h, x, l, k, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    x.toNat < 2 * s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ ok : Bool,
      (ok = true →
        (cnfOfClauses F_cur).EntailsClause (cnfClause [x.toNat ^^^ 1, l.toNat]) ∨
        (cnfOfClauses F_cur).EntailsClause (cnfClause [x.toNat ^^^ 1, k.toNat])) →
      Q (ok, ()) m

def m6CongExtractBinariesSpec : Spec [i64, i64] [i64] := fun (h, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInvW c F0 F_cur s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def m6CongFindUnitsEquivsSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
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

def m6CongExtractSpec : Spec [i64, i64, i64] [i64] := fun (h, g_cap, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ g_cap.toNat ≤ c.scratch_cap ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ret : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.core.repr = s.core.repr → s'.core.inconsistent = s.core.inconsistent →
      ret.toNat ≤ g_cap.toNat →
      M6GateSeqOk F_cur s.core.cur_vars s'.scratch.scratch_buf ret.toNat 0 →
      (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

def m6CongAndMatchSpec : Spec [i64, i32, i32] [.bool] := fun (h, ent, ua, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (scr0 : List (BitVec 32)) (g_len : Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ s.core.cur_level = 0 ∧
    FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
    g_len ≤ c.scratch_cap ∧
    (∀ idx < g_len, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
    M6GateAt F_cur s.core.cur_vars scr0 g_len ent.toNat ∧
    (scr0[ent.toNat + 1]?.getD 0#32 >>> 28) = 0#32 ∧
    ua.toNat ≤ s.core.cur_vars ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) repr' m',
      let s' : FullState := { s with core := { s.core with repr := repr' } }
      repr'.length = 2 * c.max_vars →
      FullCongReprInv F_cur (2 * s.core.cur_vars) repr' →
      (ok = true → 2 ≤ ua.toNat ∧ ua.toNat ≤ 31 ∧
        ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
          evalLitVal α (scr0[ent.toNat]?.getD 0#32).toNat =
            (List.range ua.toNat).all fun k =>
              evalLitVal α (s.core.tmp[k]?.getD 0#32).toNat) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def m6CongXorMatchSpec : Spec [i64, i32, i32] [i32] := fun (h, ent, ua, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (scr0 : List (BitVec 32)) (g_len : Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ s.core.cur_level = 0 ∧
    FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
    2 ≤ s.core.cur_vars ∧ g_len ≤ c.scratch_cap ∧
    (∀ idx < g_len, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
    M6GateAt F_cur s.core.cur_vars scr0 g_len ent.toNat ∧
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

def m6CongEnqVarSpec : Spec [i64, i64, i32] [] := fun (h, ctrl_off, _v, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (g_len ht_off ht_sz : Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧
    M6QueueCtx c s.scratch.scratch_buf g_len ctrl_off.toNat ht_off ht_sz ∧
    (FullMem c s ⋆ R) m ∧
    ∀ scr' m',
      scr'.length = c.scratch_cap →
      M6QueueCtx c scr' g_len ctrl_off.toNat ht_off ht_sz →
      (ctrl_off.toNat = c.scratch_cap → scr' = s.scratch.scratch_buf) →
      (∀ occ_bkt bkt_off inq_off q_off,
        M6CtrlLayout c s.scratch.scratch_buf g_len ctrl_off.toNat occ_bkt bkt_off inq_off
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

def m6CongEvalGateSpec : Spec [i64, i64, i64, i64, i32, i64] [i64] :=
  fun (h, g, ht_off, ht_sz, _next_ep, ctrl_off, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (scr0 : List (BitVec 32)) (g_len : Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      0 < ht_sz.toNat ∧ ht_sz.toNat < 2 ^ 30 ∧
      g.toNat < g_len ∧ g_len ≤ ht_off.toNat ∧ ht_off.toNat + ht_sz.toNat ≤ c.scratch_cap ∧
      (∀ idx < g_len, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
      M6GateAt F_cur s.core.cur_vars scr0 g_len g.toNat ∧
      M6CongHtInv F_cur s.core.cur_vars scr0 s.scratch.scratch_buf g_len ht_off.toNat ht_sz.toNat ∧
      M6QueueCtx c s.scratch.scratch_buf g_len ctrl_off.toNat ht_off.toNat ht_sz.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) s' m',
        FullDenseInvW c F0 F_cur s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
        FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
        (∀ idx < g_len, s'.scratch.scratch_buf[idx]? = scr0[idx]?) →
        M6CongHtInv F_cur s'.core.cur_vars scr0 s'.scratch.scratch_buf
          g_len ht_off.toNat ht_sz.toNat →
        M6QueueCtx c s'.scratch.scratch_buf g_len ctrl_off.toNat ht_off.toNat ht_sz.toNat →
        ((r &&& 2#64) = 0#64 →
          (∀ idx < c.scratch_cap, idx < ht_off.toNat →
            (ctrl_off.toNat = c.scratch_cap →
              s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) ∧
            (∀ occ_bkt bkt_off inq_off q_off,
              M6CtrlLayout c s.scratch.scratch_buf g_len ctrl_off.toNat occ_bkt bkt_off inq_off
                q_off ht_off.toNat ht_sz.toNat →
              idx ≠ ctrl_off.toNat + 5 →
              ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
              ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) →
              s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?))) →
        ((r &&& 2#64) ≠ 0#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def m6CongWorkStepSpec : Spec [i64, i64, i64, i64, i32] [i64] :=
  fun (h, g_len, ht_off, ht_sz, _cur_ep, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (scr0 : List (BitVec 32)) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      0 < ht_sz.toNat ∧ ht_sz.toNat < 2 ^ 30 ∧
      g_len.toNat ≤ ht_off.toNat ∧ ht_off.toNat + ht_sz.toNat ≤ c.scratch_cap ∧
      M6GateSeqOk F_cur s.core.cur_vars scr0 g_len.toNat 0 ∧
      (∀ idx < g_len.toNat, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
      M6CongHtInv F_cur s.core.cur_vars scr0 s.scratch.scratch_buf
        g_len.toNat ht_off.toNat ht_sz.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) s' m',
        FullDenseInvW c F0 F_cur s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
        FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
        (∀ idx < g_len.toNat, s'.scratch.scratch_buf[idx]? = scr0[idx]?) →
        M6CongHtInv F_cur s'.core.cur_vars scr0 s'.scratch.scratch_buf
          g_len.toNat ht_off.toNat ht_sz.toNat →
        ((r &&& 3#64) = 0#64 ∨ (r &&& 3#64) = 1#64 ∨ (r &&& 3#64) = 2#64) →
        ((r &&& 3#64) = 2#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def m6CongWorklistSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (h, g_len, ctrl_off, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (scr0 : List (BitVec 32)) (occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      0 < g_len.toNat ∧ ht_sz < 2 ^ 30 ∧
      M6CtrlLayout c s.scratch.scratch_buf g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off
        q_off ht_off ht_sz ∧
      M6GateSeqOk F_cur s.core.cur_vars scr0 g_len.toNat 0 ∧
      (∀ idx < g_len.toNat, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
      M6CongHtInv F_cur s.core.cur_vars scr0 s.scratch.scratch_buf g_len.toNat ht_off ht_sz ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullDenseInvW c F0 F_cur s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def m6CongFwdSubsumeSpec : Spec [i64, i64] [i64] := fun (h, _tick_lim, ()) m Q _ =>
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

end Specs

/-! ## 2. Pure XOR-List, Parity-Mask, Gate, Arena-Clause & Worklist Helpers -/

section Helpers

theorem xorEvalList_append (α : Nat → Bool) (xs ys : List Nat) :
    xorEvalList α (xs ++ ys) = (xorEvalList α xs != xorEvalList α ys) := by
  induction xs with
  | nil => rw [List.nil_append, xorEvalList_nil, Bool.false_bne]
  | cons a as ih =>
    rw [List.cons_append, xorEvalList_cons, xorEvalList_cons, ih]
    cases evalLitVal α a <;> cases xorEvalList α as <;> cases xorEvalList α ys <;> rfl

theorem xorEvalList_pair (α : Nat → Bool) (a b : Nat) :
    xorEvalList α [a, b] = (evalLitVal α a != evalLitVal α b) := by
  rw [xorEvalList_cons, xorEvalList_cons, xorEvalList_nil]
  cases evalLitVal α a <;> cases evalLitVal α b <;> rfl

theorem xorEvalList_perm (α : Nat → Bool) {xs ys : List Nat} (hp : List.Perm xs ys) :
    xorEvalList α xs = xorEvalList α ys := by
  induction hp with
  | nil => rfl
  | cons x _ ih => rw [xorEvalList_cons, xorEvalList_cons, ih]
  | swap a b l =>
    rw [xorEvalList_cons, xorEvalList_cons, xorEvalList_cons, xorEvalList_cons]
    cases evalLitVal α a <;> cases evalLitVal α b <;> cases xorEvalList α l <;> rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem m6_testBit_false_of_lt {a b : Nat} (h : a < 2 ^ b) : a.testBit b = false := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]; rfl

theorem m6_bv32_and_not1_toNat (x : BitVec 32) :
    (x &&& ~~~1#32).toNat = 2 * (x.toNat / 2) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [BitVec.toNat_and, Nat.testBit_and]
  cases i with
  | zero => simp
  | succ k =>
    by_cases hk : k + 1 < 32
    · have hall : ∀ j < 32, 0 < j → (~~~1#32 : BitVec 32).toNat.testBit j = true := by decide
      rw [hall (k + 1) hk (by omega), Bool.and_true, Nat.testBit_succ, Nat.testBit_succ]
      congr 1; omega
    · have hx : x.toNat < 2 ^ (k + 1) :=
        Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) (by omega))
      have h2 : 2 * (x.toNat / 2) < 2 ^ (k + 1) := by omega
      rw [m6_testBit_false_of_lt hx, m6_testBit_false_of_lt h2, Bool.false_and]

theorem xorEvalList_of_litEquiv {f : CNF Nat} {α : Nat → Bool} (hα : f.Sat α) :
    ∀ {xs ys : List Nat}, xs.length = ys.length →
      (∀ i < xs.length, LitEquiv f (xs[i]?.getD 0) (ys[i]?.getD 0)) →
      xorEvalList α xs = xorEvalList α ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hlen, heq => by
    have h0 := heq 0 (by simp)
    simp only [List.getElem?_cons_zero, Option.getD_some] at h0
    have ih := xorEvalList_of_litEquiv (xs := xs) (ys := ys) hα (by simpa using hlen)
      (fun i hi => by simpa using heq (i + 1) (by simpa using Nat.succ_lt_succ hi))
    rw [xorEvalList_cons, xorEvalList_cons, litEquiv_eval hα h0, ih]

theorem xorEvalList_litNeg_head (α : Nat → Bool) (x : Nat) (xs : List Nat) :
    xorEvalList α (litNeg x :: xs) = !(xorEvalList α (x :: xs)) := by
  rw [xorEvalList_cons, xorEvalList_cons, evalLitVal_litNeg]
  cases evalLitVal α x <;> cases xorEvalList α xs <;> rfl

theorem xorEvalList_dedup_adj (α : Nat → Bool) (x : Nat) (xs : List Nat) :
    xorEvalList α (x :: x :: xs) = xorEvalList α xs := by
  rw [xorEvalList_cons, xorEvalList_cons]
  cases evalLitVal α x <;> cases xorEvalList α xs <;> rfl

/-- Evaluates XOR parity of lower `k` bits of `mask`. -/
def m6MaskParity (mask : BitVec 32) : Nat → BitVec 32 :=
  Nat.rec 0#32 fun b ih => ih ^^^ ((mask >>> b) &&& 1#32)

theorem m6MaskParity_zero (mask : BitVec 32) : m6MaskParity mask 0 = 0#32 := rfl

theorem m6MaskParity_succ (mask : BitVec 32) (b : Nat) :
    m6MaskParity mask (b + 1) = m6MaskParity mask b ^^^ ((mask >>> b) &&& 1#32) := rfl

/-- Encodes truth values of `base[0..k)` under `α` into a `k`-bit mask. -/
def m6MaskOfEval (α : Nat → Bool) (base : List (BitVec 32)) : Nat → BitVec 32 :=
  Nat.rec 0#32 fun b rest =>
    if evalLitVal α (base[b]?.getD 0#32).toNat then rest ||| (1#32 <<< b) else rest

theorem m6MaskOfEval_zero (α : Nat → Bool) (base : List (BitVec 32)) :
    m6MaskOfEval α base 0 = 0#32 := rfl

theorem m6MaskOfEval_succ (α : Nat → Bool) (base : List (BitVec 32)) (b : Nat) :
    m6MaskOfEval α base (b + 1) =
      let rest := m6MaskOfEval α base b
      if evalLitVal α (base[b]?.getD 0#32).toNat then rest ||| (1#32 <<< b) else rest := rfl

theorem m6MaskOfEval_lt {α : Nat → Bool} {base : List (BitVec 32)} :
    ∀ k ≤ 5, (m6MaskOfEval α base k).toNat < 2 ^ k
  | 0, _ => by rw [m6MaskOfEval_zero]; decide
  | b + 1, hb => by
    have ih := m6MaskOfEval_lt (α := α) (base := base) b (by omega)
    rw [m6MaskOfEval_succ]; dsimp only
    have hpow : 2 ^ b < 2 ^ (b + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
    have h2 : (1#32 <<< b : BitVec 32).toNat = 2 ^ b := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      change 1 * 2 ^ b % 2 ^ 32 = 2 ^ b
      rw [Nat.one_mul, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))]
    split
    · have hor : ((m6MaskOfEval α base b ||| (1#32 <<< b))).toNat < 2 ^ (b + 1) := by
        rw [BitVec.toNat_or, h2]; exact Nat.or_lt_two_pow (Nat.lt_trans ih hpow) hpow
      exact hor
    · exact Nat.lt_trans ih hpow

theorem m6MaskOfEval_getLsbD {α : Nat → Bool} {base : List (BitVec 32)} :
    ∀ k j, j < 32 →
      (m6MaskOfEval α base k).getLsbD j =
        (decide (j < k) && evalLitVal α (base[j]?.getD 0#32).toNat)
  | 0, j, _ => by rw [m6MaskOfEval_zero]; simp
  | b + 1, j, hj => by
    have ih := m6MaskOfEval_getLsbD (α := α) (base := base) b j hj
    rw [m6MaskOfEval_succ]; dsimp only
    split
    · rename_i hev
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one, ih]
      by_cases hjb : j < b
      · have hj1 : j < b + 1 := by omega
        simp [hj1, hjb]
      · by_cases hje : j = b
        · subst hje; simp [hj, hev]
        · have hj1 : ¬ j < b + 1 := by omega
          have hsub : j - b ≠ 0 := by omega
          simp [hj1, hjb, hsub]
    · rename_i hev
      by_cases hje : j = b
      · subst hje; simp [ih, hev]
      · have heqv : decide (j < b + 1) = decide (j < b) := by
          by_cases h : j < b <;> simp [h, show j < b + 1 ↔ j < b by omega]
        rw [ih, heqv]

theorem m6MaskOfEval_bit_eq {α : Nat → Bool} {base : List (BitVec 32)} {k b : Nat}
    (hk : k ≤ 5) (hb : b < k) :
    (((m6MaskOfEval α base k) >>> b) &&& 1#32) =
      if evalLitVal α (base[b]?.getD 0#32).toNat then 1#32 else 0#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  cases i with
  | zero =>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, Nat.add_zero, BitVec.getLsbD_one]
    have hlsb := m6MaskOfEval_getLsbD (α := α) (base := base) k b (by omega)
    rw [hlsb]; simp only [hb, decide_true, Bool.true_and]
    cases evalLitVal α (base[b]?.getD 0#32).toNat <;> decide
  | succ i' =>
    have h1 : (1#32 : BitVec 32).getLsbD (i' + 1) = false := by
      simp [BitVec.getLsbD_one]
    simp only [BitVec.getLsbD_and, h1, Bool.and_false]
    split <;> simp [BitVec.getLsbD_one, BitVec.getLsbD_zero]

theorem m6MaskParity_of_eval {α : Nat → Bool} {base : List (BitVec 32)} {k : Nat} (hk : k ≤ 5)
    (hlen : k ≤ base.length) :
    m6MaskParity (m6MaskOfEval α base k) k =
      if xorEvalList α ((base.take k).map BitVec.toNat) then 1#32 else 0#32 := by
  suffices ∀ m ≤ k, m6MaskParity (m6MaskOfEval α base k) m =
      if xorEvalList α ((base.take m).map BitVec.toNat) then 1#32 else 0#32 from
    this k (Nat.le_refl k)
  intro m hm; induction m with
  | zero => rw [m6MaskParity_zero, List.take_zero, List.map_nil, xorEvalList_nil]; rfl
  | succ m' ih =>
    have hm' := ih (by omega)
    have hbit := m6MaskOfEval_bit_eq (α := α) (base := base) hk (by omega : m' < k)
    rw [m6MaskParity_succ, hm', hbit]
    have hlt : m' < base.length := by omega
    have htk : (base.take (m' + 1)).map BitVec.toNat =
        (base.take m').map BitVec.toNat ++ [(base[m']'hlt).toNat] := by
      rw [List.take_succ_eq_append_getElem hlt, List.map_append]; rfl
    have hget : (base[m']?.getD 0#32).toNat = (base[m']'hlt).toNat := by
      rw [List.getElem?_eq_getElem hlt, Option.getD_some]
    rw [htk, xorEvalList_append, hget,
      show xorEvalList α [(base[m']'hlt).toNat] = evalLitVal α (base[m']'hlt).toNat from
        Bool.bne_false _]
    cases xorEvalList α ((base.take m').map BitVec.toNat) <;>
      cases evalLitVal α (base[m']'hlt).toNat <;> rfl

private theorem list_perm_range_filter (k j : Nat) (hj : j < k) :
    List.Perm (List.range k) (j :: (List.range k).filter (· != j)) := by
  have hmem : j ∈ List.range k := List.mem_range.mpr hj
  have hnd : (List.range k).Nodup := List.nodup_range
  rw [List.perm_iff_count]; intro x
  by_cases hxj : x = j
  · subst hxj
    have hnf : x ∉ (List.range k).filter (· != x) := by
      intro hf; have := (List.mem_filter.mp hf).2; simp at this
    rw [List.count_cons_self, List.count_eq_zero.mpr hnf, List.Nodup.count hnd]; simp [hmem]
  · rw [List.count_cons_of_ne (Ne.symm hxj), List.count_filter]; simp [hxj]

private theorem m6_foldl_xor_init {α : Type _} (f : α → Bool) :
    ∀ (l : List α) (init : Bool),
      List.foldl (fun b i => xor b (f i)) init l =
      xor init (List.foldl (fun b i => xor b (f i)) false l)
  | [], init => by simp
  | y :: ys, init => by
    simp only [List.foldl_cons, Bool.false_xor]
    rw [m6_foldl_xor_init f ys (xor init (f y)), m6_foldl_xor_init f ys (f y)]
    cases init <;> cases f y <;> cases List.foldl (fun b i => xor b (f i)) false ys <;> rfl

theorem xorListGateDef_of_all_even_clauses {f : CNF Nat} {base : List (BitVec 32)} {k : Nat}
    (hk : k ≤ 5) (hlen : base.length = k)
    (h0 : f.EntailsClause (cnfClause (base.map BitVec.toNat)))
    (heven : ∀ mask : BitVec 32, 1 ≤ mask.toNat → mask.toNat < 2 ^ k →
      m6MaskParity mask k = 0#32 →
      f.EntailsClause (cnfClause ((List.range k).map fun b =>
        ((base[b]?.getD 0#32) ^^^ ((mask >>> b) &&& 1#32)).toNat)))
    {neg_p : Nat}
    (hnp : neg_p = (List.range k).foldl (fun acc b => acc ^^^ ((base[b]?.getD 0#32).toNat % 2)) 0)
    {j : Nat} (hj : j < k) :
    let sign := BitVec.ofNat 32 (1 ^^^ (neg_p % 2))
    let lhs := ((base[j]?.getD 0#32) &&& ~~~1#32) ||| sign
    let rhs := ((List.range k).filter (· != j)).map fun i =>
      ((base[i]?.getD 0#32) &&& ~~~1#32).toNat
    XorListGateDef f lhs.toNat rhs := by
  intro sign lhs rhs α hα
  have hodd : xorEvalList α (base.map BitVec.toNat) = true := by
    refine Classical.byContradiction fun hne => ?_
    have hfalse : xorEvalList α (base.map BitVec.toNat) = false := by
      cases h : xorEvalList α (base.map BitVec.toNat) <;> simp_all
    let mask := m6MaskOfEval α base k
    have hpar := m6MaskParity_of_eval (α := α) (base := base) hk (by omega)
    rw [List.take_of_length_le (by omega), hfalse] at hpar
    have hsat : ∃ l ∈ (List.range k).map (fun b =>
        ((base[b]?.getD 0#32) ^^^ ((mask >>> b) &&& 1#32)).toNat),
        evalLitVal α l = true := by
      rcases Nat.eq_zero_or_pos mask.toNat with hm0 | hmpos
      · have hm_bv : mask = 0#32 := BitVec.eq_of_toNat_eq hm0
        have hs0 := (clauseEvalVal_iff α _).mpr ((CNF.entails_clause_def.mp h0) α hα)
        rw [clauseEvalVal, List.any_eq_true] at hs0
        obtain ⟨l, hl_mem, hl_t⟩ := hs0
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl_mem
        obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hx
        refine ⟨_, List.mem_map.mpr ⟨idx, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
        rw [List.getElem?_eq_getElem hidx, Option.getD_some, hm_bv]
        simpa using hl_t
      · have hcl := (CNF.entails_clause_def.mp (heven mask hmpos (m6MaskOfEval_lt k hk) hpar)) α hα
        rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true] at hcl; exact hcl
    obtain ⟨l, hl_mem, hl_t⟩ := hsat
    rw [List.mem_map] at hl_mem; obtain ⟨b, hb_rng, rfl⟩ := hl_mem
    have hb_lt : b < k := List.mem_range.mp hb_rng
    have hbit := m6MaskOfEval_bit_eq (α := α) (base := base) hk hb_lt
    change ((mask >>> b) &&& 1#32) = _ at hbit
    rw [hbit] at hl_t
    split at hl_t
    · rename_i hevt; rw [bv32_xor1_eq_litNeg, evalLitVal_litNeg, hevt] at hl_t; cases hl_t
    · rename_i hevf; simp only [BitVec.xor_zero] at hl_t; exact absurd hl_t hevf
  have hev_base : xorEvalList α (base.map BitVec.toNat) =
      xorEvalList α ((List.range k).map fun i => (base[i]?.getD 0#32).toNat) := by
    congr 1; apply List.ext_getElem
    · simp [hlen]
    · intro i hi1 _
      have hi_k : i < k := by simp [hlen] at hi1; exact hi1
      simp [List.getElem_map, List.getElem_range,
        List.getElem?_eq_getElem (by omega : i < base.length)]
  rw [hev_base] at hodd
  let fv : Nat → Bool := fun i => α ((base[i]?.getD 0#32).toNat / 2)
  have hev_split : ∀ (xs : List Nat),
      xorEvalList α (xs.map fun i => (base[i]?.getD 0#32).toNat) =
      ((List.foldl (fun b i => xor b (fv i)) false xs) !=
        (List.foldl (fun p i => p ^^^ ((base[i]?.getD 0#32).toNat % 2)) 0 xs % 2 == 1)) := by
    intro xs; induction xs with
    | nil =>
      rw [List.map_nil, xorEvalList_nil, List.foldl_nil, List.foldl_nil]; rfl
    | cons x xs ih =>
      rw [List.map_cons, xorEvalList_cons, ih]
      have hfold_n : ∀ (l : List Nat) (init : Nat),
          List.foldl (fun p i => p ^^^ ((base[i]?.getD 0#32).toNat % 2)) init l % 2 =
          (init % 2) ^^^
            (List.foldl (fun p i => p ^^^ ((base[i]?.getD 0#32).toNat % 2)) 0 l % 2) := by
        intro l; induction l with
        | nil => intro init; simp
        | cons y ys ihl =>
          intro init; simp only [List.foldl_cons, Nat.zero_xor]
          rw [ihl, ihl ((base[y]?.getD 0#32).toNat % 2)]
          have h1 := Nat.xor_mod_two_pow (a := init) (b := (base[y]?.getD 0#32).toNat % 2) (n := 1)
          simp only [Nat.pow_one] at h1
          rw [h1, Nat.xor_assoc]
      rw [List.foldl_cons, List.foldl_cons, m6_foldl_xor_init fv xs (xor false _),
        hfold_n xs (0 ^^^ _)]
      simp only [Bool.false_xor, Nat.zero_xor, evalLitVal, litVar, litSign, fv]
      rcases Nat.mod_two_eq_zero_or_one (base[x]?.getD 0#32).toNat with hm | hm <;>
        rcases Nat.mod_two_eq_zero_or_one
          (List.foldl (fun p i => p ^^^ (base[i]?.getD 0#32).toNat % 2) 0 xs) with hn | hn <;>
        cases α ((base[x]?.getD 0#32).toNat / 2) <;>
        cases List.foldl (fun b i => xor b (α ((base[i]?.getD 0#32).toNat / 2))) false xs <;>
        simp [hm, hn]
  have hev_all := hev_split (List.range k)
  rw [hodd] at hev_all
  have hvars_true :
      (List.foldl (fun b i => xor b (fv i)) false (List.range k)) = !((neg_p % 2) == 1) := by
    rw [hnp]
    rcases Nat.mod_two_eq_zero_or_one (List.foldl
        (fun p i => p ^^^ (base[i]?.getD 0#32).toNat % 2) 0 (List.range k)) with hn | hn <;>
      cases hvb : List.foldl (fun b i => xor b (fv i)) false (List.range k) <;>
      simp [hn, hvb] at hev_all ⊢
  have hrng_perm := list_perm_range_filter k j hj
  have hfold_perm : ∀ {l1 l2 : List Nat}, List.Perm l1 l2 →
      List.foldl (fun b i => xor b (fv i)) false l1 =
      List.foldl (fun b i => xor b (fv i)) false l2 := by
    intro l1 l2 hp
    have hgen : ∀ l1 l2, List.Perm l1 l2 → ∀ init,
        List.foldl (fun b i => xor b (fv i)) init l1 =
        List.foldl (fun b i => xor b (fv i)) init l2 := by
      intro a b h; induction h with
      | nil => intro; rfl
      | cons _ _ ih => intro init; simp only [List.foldl_cons]; exact ih _
      | swap x y l =>
        intro init; simp only [List.foldl_cons]
        have heq : xor (xor init (fv y)) (fv x) = xor (xor init (fv x)) (fv y) := by
          cases init <;> cases fv x <;> cases fv y <;> rfl
        rw [heq]
      | trans _ _ ih1 ih2 => intro init; exact (ih1 init).trans (ih2 init)
    exact hgen l1 l2 hp false
  have hxors_eq :
      xorEvalList α rhs =
      List.foldl (fun b i => xor b (fv i)) false ((List.range k).filter (· != j)) := by
    dsimp only [rhs]
    suffices ∀ (xs : List Nat),
        xorEvalList α (xs.map fun i => ((base[i]?.getD 0#32) &&& ~~~1#32).toNat) =
        List.foldl (fun b i => xor b (fv i)) false xs from
      this ((List.range k).filter (· != j))
    intro xs; induction xs with
    | nil => rw [List.map_nil, xorEvalList_nil, List.foldl_nil]
    | cons x xs ih =>
      rw [List.map_cons, xorEvalList_cons, ih]
      rw [List.foldl_cons, m6_foldl_xor_init fv xs (xor false _), Bool.false_xor]
      have hev_even : evalLitVal α ((base[x]?.getD 0#32) &&& ~~~1#32).toNat = fv x := by
        rw [m6_bv32_and_not1_toNat]; simp [evalLitVal, litVar, litSign, fv]
      rw [hev_even]
  rw [hxors_eq]
  have hpar_lt : 1 ^^^ (neg_p % 2) < 2 := by
    rcases Nat.mod_two_eq_zero_or_one neg_p with hn | hn <;> simp [hn]
  have hlhs_ev : evalLitVal α lhs.toNat =
      (fv j != ((1 ^^^ (neg_p % 2)) == 1)) := by
    have hsn : sign.toNat = 1 ^^^ (neg_p % 2) := by
      dsimp only [sign]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlhs_n : lhs.toNat = 2 * ((base[j]?.getD 0#32).toNat / 2) + (1 ^^^ (neg_p % 2)) := by
      dsimp only [lhs]
      have h1 : (base[j]?.getD 0#32 &&& ~~~1#32).toNat = 2 * ((base[j]?.getD 0#32).toNat / 2) :=
        m6_bv32_and_not1_toNat _
      rw [BitVec.toNat_or, h1, hsn]
      rcases Nat.mod_two_eq_zero_or_one neg_p with hn | hn
      · rw [hn]; simp only [Nat.xor_zero]
        apply Nat.eq_of_testBit_eq; intro t; cases t with
        | zero => simp [Nat.add_mod]
        | succ t' =>
          rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
            show 1 / 2 = 0 from rfl, Nat.zero_testBit, Bool.or_false,
            show (2 * ((base[j]?.getD 0#32).toNat / 2)) / 2 =
              (base[j]?.getD 0#32).toNat / 2 by omega,
            show (2 * ((base[j]?.getD 0#32).toNat / 2) + 1) / 2 =
              (base[j]?.getD 0#32).toNat / 2 by omega]
      · rw [hn]; simp
    simp only [evalLitVal, litVar, litSign, hlhs_n, fv]
    rw [show (2 * ((base[j]?.getD 0#32).toNat / 2) + (1 ^^^ (neg_p % 2))) / 2 =
        (base[j]?.getD 0#32).toNat / 2 by omega]
    rcases Nat.mod_two_eq_zero_or_one neg_p with hn | hn <;> simp [hn]
  rw [hfold_perm hrng_perm] at hvars_true
  rw [List.foldl_cons, m6_foldl_xor_init fv _ (xor false _), Bool.false_xor] at hvars_true
  rw [hlhs_ev]
  rcases Nat.mod_two_eq_zero_or_one neg_p with hn | hn <;>
    cases ha : fv j <;>
    cases hb : List.foldl (fun b i => xor b (fv i)) false ((List.range k).filter (· != j)) <;>
    simp_all

theorem m6GateAt_of_canon {F_cur : List (List Nat)} {cur_vars : Nat} {scr : List (BitVec 32)}
    {g_len g : Nat} (hg : FullCongSpecs.GateAt F_cur cur_vars scr g_len g) :
    M6GateAt F_cur cur_vars scr g_len g := by
  obtain ⟨lhs, mword, h0, h1, hlhs, hbd, hcv, h8, hrhs, hsem⟩ := hg
  refine ⟨lhs, mword, h0, h1, hlhs, hbd, hcv, by omega, hrhs, ?_⟩
  rcases hsem with h | ⟨ht, ha, hx⟩ | h
  · exact Or.inl h
  · right; left; refine ⟨ht, by omega, by omega, fun α hα => ?_⟩
    have hslice : ((scr.drop (g + 2)).take (mword &&& 0xFF#32).toNat).map BitVec.toNat =
        [(scr[g + 2]?.getD 0#32).toNat, (scr[g + 3]?.getD 0#32).toNat] := by
      have hlen2 : (scr.drop (g + 2)).length ≥ 2 := by
        obtain ⟨_, hr, _⟩ := hrhs 1 (by omega)
        have := (List.getElem?_eq_some_iff.mp hr).1
        simp only [List.length_drop]; omega
      rw [ha]; apply List.ext_getElem
      · simp [List.length_take, List.length_drop]
        obtain ⟨_, hr, _⟩ := hrhs 1 (by omega)
        have := (List.getElem?_eq_some_iff.mp hr).1; omega
      · intro k hk1 _
        simp only [List.length_map, List.length_take, List.length_drop] at hk1
        obtain ⟨r0, hr0, _⟩ := hrhs 0 (by omega)
        obtain ⟨r1, hr1, _⟩ := hrhs 1 (by omega)
        rcases k with _ | _ | k'
        · simp [List.getElem_take, List.getElem_drop, hr0]; rw [List.getElem?_eq_getElem (by
            have := (List.getElem?_eq_some_iff.mp hr0).1; omega)] at hr0
          exact congrArg BitVec.toNat (Option.some.inj hr0)
        · simp [List.getElem_take, List.getElem_drop, hr1]; rw [List.getElem?_eq_getElem (by
            have := (List.getElem?_eq_some_iff.mp hr1).1; omega)] at hr1
          exact congrArg BitVec.toNat (Option.some.inj hr1)
        · omega
    rw [hslice, xorEvalList_pair]; exact xorGateDef_eval hα hx
  · exact Or.inr (Or.inr h)

theorem m6GateSeqOk_of_canon {F_cur : List (List Nat)} {cur_vars : Nat} {scr : List (BitVec 32)}
    {g_len g : Nat} (h : FullCongSpecs.GateSeqOk F_cur cur_vars scr g_len g) :
    M6GateSeqOk F_cur cur_vars scr g_len g := by
  induction h with
  | done => exact .done
  | step hg _ ih => exact .step (m6GateAt_of_canon hg) ih

theorem m6CongHtInv_of_canon {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr0 scr : List (BitVec 32)} {g_len ht_off ht_sz : Nat}
    (h : FullCongSpecs.CongHtInv F_cur cur_vars scr0 scr g_len ht_off ht_sz) :
    M6CongHtInv F_cur cur_vars scr0 scr g_len ht_off ht_sz := fun k hk =>
  (h k hk).elim Or.inl fun hg => Or.inr (m6GateAt_of_canon hg)

theorem m6GateAt_congr {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr1 scr2 : List (BitVec 32)} {g_len1 g_len2 g : Nat} (hge : g_len1 ≤ g_len2)
    (heq : ∀ idx < g_len1, scr2[idx]? = scr1[idx]?)
    (hg : M6GateAt F_cur cur_vars scr1 g_len1 g) :
    M6GateAt F_cur cur_vars scr2 g_len2 g := by
  obtain ⟨lhs, mword, h0, h1, hlhs, hbd, hac, ha31, hrhs, hsem⟩ := hg
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
    hlhs, by omega, hac, ha31, ?_, ?_⟩
  · intro k hk; obtain ⟨r, hr, hlt⟩ := hrhs k hk
    exact ⟨r, (heq (g + 2 + k) (by omega)).trans hr, hlt⟩
  · rcases hsem with ⟨ht, ha2, hand⟩ | ⟨ht, ha2, ha4, hxor⟩ | ⟨ht, ha3, hite⟩
    · left; exact ⟨ht, ha2, hslice ▸ hand⟩
    · right; left; exact ⟨ht, ha2, ha4, hslice ▸ hxor⟩
    · right; right
      rw [heq (g + 2) (by omega), heq (g + 3) (by omega), heq (g + 4) (by omega)]
      exact ⟨ht, ha3, hite⟩

theorem m6GateSeqOk_append {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr1 scr2 : List (BitVec 32)} {g_len1 g_len2 : Nat} (hge : g_len1 ≤ g_len2)
    (heq : ∀ idx < g_len1, scr2[idx]? = scr1[idx]?)
    (hnew : M6GateSeqOk F_cur cur_vars scr2 g_len2 g_len1) :
    ∀ {g : Nat}, M6GateSeqOk F_cur cur_vars scr1 g_len1 g →
      M6GateSeqOk F_cur cur_vars scr2 g_len2 g := by
  intro g hs; induction hs with
  | done => exact hnew
  | @step g hg _ ih =>
    have hg' := m6GateAt_congr hge heq hg
    obtain ⟨_, mword, _, h1, _, hbd, _⟩ := hg
    have h1' : scr2[g + 1]? = scr1[g + 1]? := heq (g + 1) (by omega)
    exact .step hg' (by simpa [h1'] using ih)

theorem m6GateSeqOk_congr {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr1 scr2 : List (BitVec 32)} {g_len g : Nat}
    (heq : ∀ idx < g_len, scr2[idx]? = scr1[idx]?)
    (hs : M6GateSeqOk F_cur cur_vars scr1 g_len g) :
    M6GateSeqOk F_cur cur_vars scr2 g_len g :=
  m6GateSeqOk_append (Nat.le_refl _) heq .done hs

theorem m6GateSeqOk_inv_lt {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr : List (BitVec 32)} {g_len g : Nat}
    (hs : M6GateSeqOk F_cur cur_vars scr g_len g) (hlt : g < g_len) :
    M6GateAt F_cur cur_vars scr g_len g ∧
      M6GateSeqOk F_cur cur_vars scr g_len
        (g + 2 + ((scr[g + 1]?.getD 0#32) &&& 0xFF#32).toNat) := by
  cases hs with
  | done => omega
  | step hg hrest => exact ⟨hg, hrest⟩

theorem m6_andGate_of_emitted {F_cur : List (List Nat)} {cur_vars usz i g_len : Nat}
    {base scr : List (BitVec 32)} (hu3 : 3 ≤ usz) (hu32 : usz ≤ 32) (hucv : usz ≤ cur_vars)
    (hi : i < usz)
    (hlt : ∀ k < usz, (base[k]?.getD 0#32).toNat < 2 * cur_vars)
    (hcl : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((List.range usz).map fun k => (base[k]?.getD 0#32).toNat)))
    (hbins : ∀ k < usz, k ≠ i →
      (cnfOfClauses F_cur).EntailsClause (cnfClause
        [litNeg (base[i]?.getD 0#32).toNat, litNeg (base[k]?.getD 0#32).toNat]))
    (hbd_g : g_len + 2 + (usz - 1) ≤ scr.length)
    (h0 : scr[g_len]? = some (base[i]?.getD 0#32))
    (h1 : scr[g_len + 1]? = some (BitVec.ofNat 32 (usz - 1)))
    (hrhs : ∀ k < usz, k ≠ i →
      scr[g_len + 2 + (if k < i then k else k - 1)]? = some ((base[k]?.getD 0#32) ^^^ 1#32)) :
    M6GateAt F_cur cur_vars scr (g_len + 2 + (usz - 1)) g_len := by
  have hmword_tag : ((BitVec.ofNat 32 (usz - 1) >>> 28)).toNat = 0 := by
    rw [BitVec.toNat_ushiftRight, bv32_ofNat_toNat (by omega), Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (by omega)
  have hmword_ar : ((BitVec.ofNat 32 (usz - 1) &&& 0xFF#32)).toNat = usz - 1 := by
    rw [BitVec.toNat_and, bv32_ofNat_toNat (by omega),
      show (0xFF#32 : BitVec 32).toNat = 255 from rfl]
    simpa [Nat.mod_eq_of_lt (show usz - 1 < 256 by omega)] using
      Nat.and_two_pow_sub_one_eq_mod (usz - 1) 8
  have hrhs_at : ∀ r < usz - 1,
      ∃ v : BitVec 32, scr[g_len + 2 + r]? = some v ∧ v.toNat < 2 * cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause [litNeg (base[i]?.getD 0#32).toNat, v.toNat]) := by
    intro r hr
    let k := if r < i then r else r + 1
    have hk_lt : k < usz := by dsimp only [k]; split <;> omega
    have hk_ne : k ≠ i := by dsimp only [k]; split <;> omega
    have hk_eq : (if k < i then k else k - 1) = r := by
      dsimp only [k]; split <;> (try split) <;> omega
    have hget := hrhs k hk_lt hk_ne; rw [hk_eq] at hget
    exact ⟨_, hget, by rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even (hlt k hk_lt),
      by rw [bv32_xor1_eq_litNeg]; exact hbins k hk_lt hk_ne⟩
  refine ⟨base[i]?.getD 0#32, BitVec.ofNat 32 (usz - 1), h0, h1, hlt i hi, by omega, by omega,
    by omega, fun r hr => let ⟨v, hv, hltv, _⟩ := hrhs_at r (by omega); ⟨v, hv, hltv⟩,
    Or.inl ⟨hmword_tag, by omega, ?_, ?_⟩⟩
  · refine entails_perm_clause (fun x hx => ?_) hcl
    rw [List.mem_map] at hx; obtain ⟨k, hk, rfl⟩ := hx; rw [List.mem_range] at hk
    rw [List.mem_cons]; by_cases hki : k = i
    · subst hki; exact Or.inl rfl
    · right; rw [List.mem_map]
      let r := if k < i then k else k - 1
      have hr_lt : r < usz - 1 := by dsimp only [r]; split <;> omega
      have hscr_r := hrhs k hk hki
      have hr_scr : g_len + 2 + r < scr.length := by omega
      have hval_r : scr[g_len + 2 + r]'hr_scr = (base[k]?.getD 0#32) ^^^ 1#32 := by
        rw [List.getElem?_eq_getElem hr_scr] at hscr_r; exact Option.some.inj hscr_r
      refine ⟨(scr[g_len + 2 + r]'hr_scr).toNat, List.mem_map.mpr ⟨_, ?_, rfl⟩, ?_⟩
      · have hlt_t : r < ((scr.drop (g_len + 2)).take
            ((BitVec.ofNat 32 (usz - 1) &&& 0xFF#32).toNat)).length := by
          rw [List.length_take, List.length_drop, hmword_ar]; omega
        simpa [List.getElem_take, List.getElem_drop] using List.getElem_mem hlt_t
      · rw [hval_r, bv32_xor1_eq_litNeg, litNeg_litNeg]
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx; obtain ⟨r, hr, hget⟩ := List.mem_iff_getElem.mp hv
    rw [List.length_take, List.length_drop, hmword_ar] at hr
    rw [List.getElem_take, List.getElem_drop] at hget
    obtain ⟨v', hv', _, hent⟩ := hrhs_at r (by omega)
    rw [List.getElem?_eq_getElem (by omega)] at hv'
    rwa [(Option.some.inj hv').symm.trans hget] at hent

theorem resolve_ternary_with_either_bin {f : CNF Nat} {x l k : Nat}
    (ht : f.EntailsClause (cnfClause [x, l, k]))
    (hb : f.EntailsClause (cnfClause [x ^^^ 1, l]) ∨ f.EntailsClause (cnfClause [x ^^^ 1, k])) :
    f.EntailsClause (cnfClause [l, k]) := by
  refine entails_of_eval_mem fun α hα => ?_
  have hs := (clauseEvalVal_iff α _).mpr ((CNF.entails_clause_def.mp ht) α hα)
  rw [clauseEvalVal] at hs; simp only [List.any_cons, List.any_nil, Bool.or_false] at hs
  rcases hb with hbl | hbk
  · have hbs := (clauseEvalVal_iff α _).mpr ((CNF.entails_clause_def.mp hbl) α hα)
    rw [clauseEvalVal] at hbs; simp only [List.any_cons, List.any_nil, Bool.or_false] at hbs
    rw [show x ^^^ 1 = litNeg x from rfl, evalLitVal_litNeg] at hbs
    cases hx : evalLitVal α x <;> cases hl : evalLitVal α l <;> cases hk : evalLitVal α k <;>
      simp_all [List.mem_cons]
  · have hbs := (clauseEvalVal_iff α _).mpr ((CNF.entails_clause_def.mp hbk) α hα)
    rw [clauseEvalVal] at hbs; simp only [List.any_cons, List.any_nil, Bool.or_false] at hbs
    rw [show x ^^^ 1 = litNeg x from rfl, evalLitVal_litNeg] at hbs
    cases hx : evalLitVal α x <;> cases hl : evalLitVal α l <;> cases hk : evalLitVal α k <;>
      simp_all [List.mem_cons]

theorem unassigned_clause_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hcl0 : s.core.cur_level = 0)
    {cr : Nat} (hcr : cr ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cr = false)
    {unass : List Nat}
    (hcov : ∀ l ∈ fullArenaClauseLits s cr,
      s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨ l ∈ unass) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause unass) := by
  refine entails_of_eval_mem fun α hα => ?_
  have hsat := (clauseEvalVal_iff α _).mpr
    ((CNF.entails_clause_def.mp (hw.arena.entails cr hcr hng)) α hα)
  rw [clauseEvalVal, List.any_eq_true] at hsat
  obtain ⟨l, hl_mem, hl_t⟩ := hsat
  rcases hcov l hl_mem with hff | hin
  · exfalso
    have hl_lt := hw.arena.lits_lt cr hcr hng l hl_mem
    obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl_lt).mp hff
    have hlvl0 : (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
      have := hw.lvl_le i hi; omega
    have hunit := hw.level0_sound i hi hlvl0; rw [heq] at hunit
    have hs := (CNF.entails_clause_def.mp hunit) α hα
    rw [← clauseEvalVal_iff, clauseEvalVal] at hs
    simp only [List.any_cons, List.any_nil, Bool.or_false,
      show l ^^^ 1 = litNeg l from rfl, evalLitVal_litNeg, hl_t] at hs
    cases hs
  · exact ⟨l, hin, hl_t⟩

theorem m6_bv32_and_sub1_lt {x n : BitVec 32} (hpos : 0 < n.toNat) :
    (x &&& (n - 1#32)).toNat < n.toNat := by
  have hsub : (n - 1#32).toNat = n.toNat - 1 := by bv_omega
  rw [BitVec.toNat_and, hsub]
  have hle : x.toNat &&& (n.toNat - 1) ≤ n.toNat - 1 := Nat.and_le_right; omega

theorem m6_pow2_sub1_and_eq_mod {n p : Nat} (_hp : 1 ≤ p) (hp9 : p ≤ 9) (x : BitVec 32)
    (hn : n = 2 ^ p) : (x &&& (BitVec.ofNat 32 n - 1#32)).toNat = x.toNat % n := by
  have hlt : 2 ^ p ≤ 512 := Nat.pow_le_pow_right (by omega) hp9
  have hsub : (BitVec.ofNat 32 n - 1#32).toNat = 2 ^ p - 1 := by
    have hof : (BitVec.ofNat 32 n).toNat = 2 ^ p := by
      rw [hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hof]; exact Nat.one_le_two_pow)), hof]
    rfl
  rw [BitVec.toNat_and, hsub, hn, Nat.and_two_pow_sub_one_eq_mod]

theorem m6_and_sub1_u32_eq_mod {occ_bkt : Nat}
    (hp : ∃ p : Nat, 1 ≤ p ∧ p ≤ 9 ∧ occ_bkt = 2 ^ p) (x : BitVec 32) :
    (x &&& (BitVec.ofNat 32 occ_bkt - 1#32)).toNat = x.toNat % occ_bkt := by
  obtain ⟨p, h1, h2, rfl⟩ := hp; exact m6_pow2_sub1_and_eq_mod h1 h2 x rfl

theorem m6CtrlLayout_set_q {c : FullCfg} {scr : List (BitVec 32)}
    {g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (h : M6CtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    {scr' : List (BitVec 32)} (_hlen' : scr'.length = scr.length)
    (hk05 : ∀ i < 8, i ≠ 4 → i ≠ 5 → scr'[ctrl_off + i]? = scr[ctrl_off + i]?)
    (hqh' : (scr'[ctrl_off + 4]?.getD 0#32).toNat < occ_bkt)
    (hql' : (scr'[ctrl_off + 5]?.getD 0#32).toNat ≤ occ_bkt)
    (hqok' : ∀ k < (scr'[ctrl_off + 5]?.getD 0#32).toNat,
      (scr'[q_off + ((scr'[ctrl_off + 4]?.getD 0#32).toNat + k) % occ_bkt]?.getD 0#32).toNat <
        occ_bkt) :
    M6CtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz := by
  rcases h with
    ⟨h1, h2, h3, h4, s0, s1, s2, s3, s6, s7, h5, h6, hpow, h7, h8, h9, h10, h11, h12, _, _, _⟩
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_, ?_, ?_, ?_,
    h5, h6, hpow, h7, h8, h9, h10, h11, h12, hqh', hql', hqok'⟩
  · have h0 := hk05 0 (by decide) (by decide) (by decide)
    rw [Nat.add_zero] at h0; exact (congrArg (Option.getD · 0#32) h0).trans s0
  · exact (congrArg (Option.getD · 0#32) (hk05 1 (by decide) (by decide) (by decide))).trans s1
  · exact (congrArg (Option.getD · 0#32) (hk05 2 (by decide) (by decide) (by decide))).trans s2
  · exact (congrArg (Option.getD · 0#32) (hk05 3 (by decide) (by decide) (by decide))).trans s3
  · exact (congrArg (Option.getD · 0#32) (hk05 6 (by decide) (by decide) (by decide))).trans s6
  · exact (congrArg (Option.getD · 0#32) (hk05 7 (by decide) (by decide) (by decide))).trans s7

theorem m6CtrlLayout_same_tail {c : FullCfg} {scr scr' : List (BitVec 32)}
    {g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (h : M6CtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hlen' : scr'.length = scr.length)
    (hql' : (scr'[ctrl_off + 5]?.getD 0#32).toNat ≤ occ_bkt)
    (hk : ∀ i < 8, i ≠ 5 → scr'[ctrl_off + i]? = scr[ctrl_off + i]?)
    (hqok' : ∀ k < (scr'[ctrl_off + 5]?.getD 0#32).toNat,
      (scr'[q_off + ((scr'[ctrl_off + 4]?.getD 0#32).toNat + k) % occ_bkt]?.getD 0#32).toNat <
        occ_bkt) :
    M6CtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz := by
  refine m6CtrlLayout_set_q h hlen' (fun i hi _ h5 => hk i hi h5) ?_ hql' hqok'
  rw [hk 4 (by decide) (by decide)]; exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem m6CtrlLayout_pop_q {c : FullCfg} {scr : List (BitVec 32)}
    {g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (h : M6CtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hlen : scr.length = c.scratch_cap)
    (hpos : 0 < (scr[ctrl_off + 5]?.getD 0#32).toNat) :
    let qh := scr[ctrl_off + 4]?.getD 0#32
    let ql := scr[ctrl_off + 5]?.getD 0#32
    let b := scr[q_off + qh.toNat]?.getD 0#32
    let nqh := (qh + 1#32) &&& (BitVec.ofNat 32 occ_bkt - 1#32)
    let scr' := ((scr.set (ctrl_off + 4) nqh).set (ctrl_off + 5) (ql - 1#32)).set
      (inq_off + b.toNat) 0#32
    b.toNat < occ_bkt ∧ nqh.toNat < occ_bkt ∧
    M6CtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz := by
  intro qh ql b nqh scr'
  rcases h with
    ⟨h1, h2, h3, h4, s0, s1, s2, s3, s6, s7, h5, h6, hpow, h7, h8, h9, h10, h11, h12,
     hqh_lt, hql_le, hqok⟩
  have hb_lt : b.toNat < occ_bkt := by
    have := hqok 0 hpos
    rwa [Nat.add_zero, Nat.mod_eq_of_lt hqh_lt] at this
  have hnqh_lt : nqh.toNat < occ_bkt := by
    dsimp only [nqh]; rw [m6_and_sub1_u32_eq_mod hpow]; exact Nat.mod_lt _ h5
  have hql_sub : (ql - 1#32).toNat = ql.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (show (1#32 : BitVec 32).toNat ≤ ql.toNat from
      Nat.succ_le_of_lt hpos))]; rfl
  have hnqh_mod : nqh.toNat = (qh.toNat + 1) % occ_bkt := by
    dsimp only [nqh]; rw [m6_and_sub1_u32_eq_mod hpow]
    have hqh1 : (qh + 1#32).toNat = qh.toNat + 1 := by
      rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt]
      exact Nat.lt_of_lt_of_le (Nat.succ_lt_succ hqh_lt) (by omega)
    rw [hqh1]
  have hscr'_ctrl : ∀ i, i < 8 → i ≠ 4 → i ≠ 5 → scr'[ctrl_off + i]? = scr[ctrl_off + i]? := by
    intro i _ h4' h5'
    dsimp only [scr']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have hscr'_4 : scr'[ctrl_off + 4]?.getD 0#32 = nqh := by
    dsimp only [scr']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by simp [hlen]; omega), Option.getD_some]
  have hscr'_5 : scr'[ctrl_off + 5]?.getD 0#32 = ql - 1#32 := by
    dsimp only [scr']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hlen]; omega),
      Option.getD_some]
  refine ⟨hb_lt, hnqh_lt, ?_⟩
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_, ?_, ?_, ?_,
    h5, h6, hpow, h7, h8, h9, h10, h11, h12,
    by rw [hscr'_4]; exact hnqh_lt,
    by rw [hscr'_5, hql_sub]; exact Nat.le_trans (Nat.sub_le _ _) hql_le, ?_⟩
  · have h0 := hscr'_ctrl 0 (by decide) (by decide) (by decide)
    rw [Nat.add_zero] at h0; exact (congrArg (Option.getD · 0#32) h0).trans s0
  · exact (congrArg (Option.getD · 0#32)
      (hscr'_ctrl 1 (by decide) (by decide) (by decide))).trans s1
  · exact (congrArg (Option.getD · 0#32)
      (hscr'_ctrl 2 (by decide) (by decide) (by decide))).trans s2
  · exact (congrArg (Option.getD · 0#32)
      (hscr'_ctrl 3 (by decide) (by decide) (by decide))).trans s3
  · exact (congrArg (Option.getD · 0#32)
      (hscr'_ctrl 6 (by decide) (by decide) (by decide))).trans s6
  · exact (congrArg (Option.getD · 0#32)
      (hscr'_ctrl 7 (by decide) (by decide) (by decide))).trans s7
  · intro k hk; rw [hscr'_5, hql_sub] at hk; rw [hscr'_4, hnqh_mod]
    have hidx : ((qh.toNat + 1) % occ_bkt + k) % occ_bkt = (qh.toNat + (k + 1)) % occ_bkt := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc, Nat.add_comm 1 k]
    rw [hidx]
    have hslot_lt : q_off + (qh.toNat + (k + 1)) % occ_bkt < inq_off + b.toNat := by
      have := Nat.mod_lt (qh.toNat + (k + 1)) h5; omega
    have hq_ne4 : ctrl_off + 4 ≠ q_off + (qh.toNat + (k + 1)) % occ_bkt := by omega
    have hq_ne5 : ctrl_off + 5 ≠ q_off + (qh.toNat + (k + 1)) % occ_bkt := by omega
    have hq_nei : inq_off + b.toNat ≠ q_off + (qh.toNat + (k + 1)) % occ_bkt := by omega
    dsimp only [scr']
    rw [List.getElem?_set_ne hq_nei, List.getElem?_set_ne hq_ne5, List.getElem?_set_ne hq_ne4]
    have hk1 : k + 1 < (scr[ctrl_off + 5]?.getD 0#32).toNat := by
      change k < (scr[ctrl_off + 5]?.getD 0#32).toNat - 1 at hk; omega
    exact hqok (k + 1) hk1

theorem m6CtrlLayout_unique {c : FullCfg} {scr : List (BitVec 32)}
    {g_len ctrl_off o1 b1 i1 q1 h1 s1 o2 b2 i2 q2 h2 s2 : Nat}
    (hl1 : M6CtrlLayout c scr g_len ctrl_off o1 b1 i1 q1 h1 s1)
    (hl2 : M6CtrlLayout c scr g_len ctrl_off o2 b2 i2 q2 h2 s2) :
    o1 = o2 ∧ b1 = b2 ∧ i1 = i2 ∧ q1 = q2 ∧ h1 = h2 ∧ s1 = s2 := by
  have heqc : ∀ {a b : Nat}, a < 2 ^ 32 → b < 2 ^ 32 →
      BitVec.ofNat 32 a = BitVec.ofNat 32 b → a = b := fun ha hb hv => by
    have h := congrArg BitVec.toNat hv
    rwa [bv32_ofNat_toNat ha, bv32_ofNat_toNat hb] at h
  rcases hl1 with ⟨_, _, _, _, e1_0, e1_1, e1_2, e1_3, e1_6, e1_7,
    ho1_pos, ho1_le, _, hs1_pos, hq1_lo, hq1_hi, hi1_hi, hb1_hi, hh1_hi, _, _, _⟩
  rcases hl2 with ⟨_, _, _, _, e2_0, e2_1, e2_2, e2_3, e2_6, e2_7,
    ho2_pos, ho2_le, _, hs2_pos, hq2_lo, hq2_hi, hi2_hi, hb2_hi, hh2_hi, _, _, _⟩
  have hsc := c.hscr; unfold dimacsBound at hsc
  have ho : o1 = o2 := heqc (by omega) (by omega) (e1_0.symm.trans e2_0)
  have hb : b1 = b2 := heqc (by omega) (by omega) (e1_1.symm.trans e2_1)
  have hi : i1 = i2 := heqc (by omega) (by omega) (e1_2.symm.trans e2_2)
  have hq : q1 = q2 := heqc (by omega) (by omega) (e1_3.symm.trans e2_3)
  have hh : h1 = h2 := heqc (by omega) (by omega) (e1_6.symm.trans e2_6)
  have hs : s1 = s2 := heqc (by omega) (by omega) (e1_7.symm.trans e2_7)
  exact ⟨ho, hb, hi, hq, hh, hs⟩

private theorem m6_ff24_getLsbD {i : Nat} (hi : i < 32) :
    (0x00FFFFFF#32 : BitVec 32).getLsbD i = decide (i < 24) := by
  have hall : ∀ j : BitVec 5, (0x00FFFFFF#32 : BitVec 32).getLsbD j.toNat =
      decide (j.toNat < 24) := by decide
  have h := hall (BitVec.ofNat 5 i)
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi] using h

private theorem m6_pack_entry_gn {slot gn : Nat} (_hslot : slot < 32) (hgn : gn < 2 ^ 24) :
    (((BitVec.ofNat 32 slot <<< 24) ||| BitVec.ofNat 32 gn) &&& 0x00FFFFFF#32).toNat = gn := by
  have heq : (((BitVec.ofNat 32 slot <<< 24) ||| BitVec.ofNat 32 gn) &&& 0x00FFFFFF#32) =
      BitVec.ofNat 32 gn := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      m6_ff24_getLsbD hi]
    by_cases hi24 : i < 24
    · simp [hi24]
    · have hge24 : 24 ≤ i := by omega
      have hgn0 : (BitVec.ofNat 32 gn).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat]; simp only [hi, decide_true, Bool.true_and]
        exact m6_testBit_false_of_lt
          (Nat.lt_of_lt_of_le hgn (Nat.pow_le_pow_right (by omega) hge24))
      simp [hi24, hgn0]
  rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem m6_pack_entry_slot {slot gn : Nat} (hslot : slot < 32) (hgn : gn < 2 ^ 24) :
    (((BitVec.ofNat 32 slot <<< 24) ||| BitVec.ofNat 32 gn) >>> 24).toNat = slot := by
  have heq : (((BitVec.ofNat 32 slot <<< 24) ||| BitVec.ofNat 32 gn) >>> 24) =
      BitVec.ofNat 32 slot := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
    by_cases hi8 : 24 + i < 32
    · have hle : 24 ≤ 24 + i := by omega
      have hgn0 : (BitVec.ofNat 32 gn).getLsbD (24 + i) = false := by
        rw [BitVec.getLsbD_ofNat]; simp only [hi8, decide_true, Bool.true_and]
        exact m6_testBit_false_of_lt (Nat.lt_of_lt_of_le hgn (Nat.pow_le_pow_right (by omega) hle))
      have hsub : 24 + i - 24 = i := by omega
      rw [hgn0, hsub]; simp [hi8, hle]
    · have hge8 : 8 ≤ i := by omega
      have hff : (24 + i < 32) = False := eq_false hi8
      have hlt5 : slot < 2 ^ i :=
        Nat.lt_of_lt_of_le (show slot < 2 ^ 5 from hslot)
          (Nat.pow_le_pow_right (by decide) (by omega))
      simp only [BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and, hff, decide_false,
        Bool.false_and, Bool.false_or]
      rw [m6_testBit_false_of_lt hlt5]
  rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem m6OccNodesOk_push {F_cur : List (List Nat)} {cv g_len occ_end ctrl_off bkt_off occ_bkt
    gn slot b : Nat} {scr0 scr : List (BitVec 32)}
    (hok : M6OccNodesOk F_cur cv g_len occ_end ctrl_off bkt_off occ_bkt scr0 scr)
    (heven : (occ_end - g_len) % 2 = 0)
    (hctrl : bkt_off + occ_bkt ≤ scr.length) (hocc2 : occ_end + 2 ≤ ctrl_off)
    (hcv2 : occ_end + 1 < 2 ^ 32) (hgn_lt : gn < g_len) (hg_lt24 : g_len ≤ 0x01000000)
    (hgat : M6GateAt F_cur cv scr0 g_len gn)
    (hslot_le : slot ≤ ((scr0[gn + 1]?.getD 0#32) &&& 0xFF#32).toNat)
    (hb : b < occ_bkt) (_hg_ctrl : g_len ≤ ctrl_off) (hdisj : ctrl_off ≤ bkt_off) :
    let head := scr[bkt_off + b]?.getD 0xFFFFFFFF#32
    let entry : BitVec 32 :=
      if slot = 0 then BitVec.ofNat 32 gn
      else (BitVec.ofNat 32 slot <<< 24) ||| BitVec.ofNat 32 gn
    let scr' := ((scr.set occ_end entry).set (occ_end + 1) head).set (bkt_off + b)
      (BitVec.ofNat 32 occ_end)
    M6OccNodesOk F_cur cv g_len (occ_end + 2) ctrl_off bkt_off occ_bkt scr0 scr' := by
  intro head entry scr'
  have h_le : g_len ≤ occ_end := hok.1
  have hslot_lt32 : slot < 32 := by
    obtain ⟨_, mword, _, h1, _, _, _, ha31, _⟩ := hgat
    rw [h1, Option.getD_some] at hslot_le; omega
  have hgn_24 : gn < 2 ^ 24 := by omega
  have hptr_up : ∀ p, M6OccNodePtrOk g_len occ_end p →
      M6OccNodePtrOk g_len (occ_end + 2) p := by
    rintro p (rfl | ⟨h1, h2, h3⟩); · exact Or.inl rfl
    · exact Or.inr ⟨h1, by omega, h3⟩
  have hnew_ptr : M6OccNodePtrOk g_len (occ_end + 2) (BitVec.ofNat 32 occ_end) := by
    right; have hof : (BitVec.ofNat 32 occ_end).toNat = occ_end := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hof]; exact ⟨h_le, by omega, heven⟩
  have hentry_eq : entry = (BitVec.ofNat 32 slot <<< 24) ||| BitVec.ofNat 32 gn := by
    dsimp only [entry]; split
    · rename_i h0; subst h0
      have hz : (BitVec.ofNat 32 0 <<< 24 : BitVec 32) = 0#32 := by decide
      rw [hz, BitVec.zero_or]
    · rfl
  have hgn_rec : (entry &&& 0x00FFFFFF#32).toNat = gn := by
    rw [hentry_eq]; exact m6_pack_entry_gn hslot_lt32 hgn_24
  have hslot_rec : (entry >>> 24).toNat = slot := by
    rw [hentry_eq]; exact m6_pack_entry_slot hslot_lt32 hgn_24
  refine ⟨by omega, hocc2, fun b' hb' => ?_, fun nd hnd1 hnd2 hnd_ev => ?_⟩
  · by_cases hbe : b' = b
    · subst hbe; dsimp only [scr']
      rw [List.getElem?_set_self (by simp; omega), Option.getD_some]; exact hnew_ptr
    · dsimp only [scr']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega)]
      exact hptr_up _ (hok.2.2.1 b' hb')
  · by_cases hnd_new : nd = occ_end
    · subst hnd_new; dsimp only [scr']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by omega), Option.getD_some,
        List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega),
        Option.getD_some, hgn_rec, hslot_rec]
      exact ⟨hgn_lt, hgat, hslot_le, hptr_up _ (hok.2.2.1 b hb)⟩
    · have hnd_old : nd + 1 < occ_end := by omega
      dsimp only [scr']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      obtain ⟨h1, h2, h3, h4⟩ := hok.2.2.2 nd hnd1 hnd_old hnd_ev
      exact ⟨h1, h2, h3, hptr_up _ h4⟩

theorem m6OccNodesOk_relink {F_cur : List (List Nat)} {cv g_len occ_end ctrl_off bkt_off occ_bkt
    nd b_dst : Nat} {scr0 scr : List (BitVec 32)}
    (hok : M6OccNodesOk F_cur cv g_len occ_end ctrl_off bkt_off occ_bkt scr0 scr)
    (hctrl : bkt_off + occ_bkt ≤ scr.length) (hdisj : ctrl_off ≤ bkt_off)
    (hnd1 : g_len ≤ nd) (hnd2 : nd + 1 < occ_end) (hnd_ev : (nd - g_len) % 2 = 0)
    (hcv2 : occ_end + 1 < 2 ^ 32) (hb : b_dst < occ_bkt) :
    let scr' := (scr.set (nd + 1) (scr[bkt_off + b_dst]?.getD 0xFFFFFFFF#32)).set
      (bkt_off + b_dst) (BitVec.ofNat 32 nd)
    M6OccNodesOk F_cur cv g_len occ_end ctrl_off bkt_off occ_bkt scr0 scr' := by
  intro scr'
  have hptr_nd : M6OccNodePtrOk g_len occ_end (BitVec.ofNat 32 nd) := by
    right; have hof : (BitVec.ofNat 32 nd).toNat = nd := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hof]; exact ⟨hnd1, hnd2, hnd_ev⟩
  have hocc_le := hok.2.1
  refine ⟨hok.1, hok.2.1, fun b' hb' => ?_, fun nd' hn1 hn2 hn_ev => ?_⟩
  · by_cases hbe : b' = b_dst
    · subst hbe; dsimp only [scr']
      rw [List.getElem?_set_self (by simp; omega), Option.getD_some]; exact hptr_nd
    · dsimp only [scr']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hok.2.2.1 b' hb'
  · have hnd_ne : bkt_off + b_dst ≠ nd' := by omega
    have hnd_ne1 : nd + 1 ≠ nd' := by omega
    have hent_eq : scr'[nd']? = scr[nd']? := by
      dsimp only [scr']; rw [List.getElem?_set_ne hnd_ne, List.getElem?_set_ne hnd_ne1]
    obtain ⟨h1, h2, h3, h4⟩ := hok.2.2.2 nd' hn1 hn2 hn_ev
    refine ⟨by rw [hent_eq]; exact h1, by rw [hent_eq]; exact h2, by rw [hent_eq]; exact h3, ?_⟩
    by_cases hne : nd' = nd
    · subst hne; dsimp only [scr']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
      exact hok.2.2.1 b_dst hb
    · dsimp only [scr']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact h4

end Helpers

/-! ## 3. `full_subst_rewrite_bins_wp` & `full_subst_rewrite_ar_wp` -/

section RewriteBinsArProof

theorem full_subst_rewrite_bins_wp (Γ : Env)
    (hAddUnit : ∀ args m Q X, fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X)
    (hAddBin : ∀ args m Q X, fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullSubstRewriteBinsSpec args m Q X →
      Func.wp Γ full_subst_rewrite_bins_body args m Q X :=
  FullM5DenseSafe.full_subst_rewrite_bins_m5_wp Γ hAddUnit hAddBin

theorem full_subst_rewrite_ar_wp (Γ : Env)
    (hArenaNext : ∀ args m Q X, fullArenaNextSpec args m Q X →
      Γ "full_arena_next" [i64, i32] [i32] args m Q X)
    (hAddUnit : ∀ args m Q X, fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X)
    (hAddBin : ∀ args m Q X, fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullSubstRewriteArSpec args m Q X →
      Func.wp Γ full_subst_rewrite_ar_body args m Q X :=
  FullM5DenseSafe.full_subst_rewrite_ar_m5_wp Γ hArenaNext hAddUnit hAddBin

end RewriteBinsArProof

end LeanQbe.T.Examples.Kissat.FullM6CongSubst
