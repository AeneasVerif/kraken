/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BCong
public import LeanQbe.T.Examples.Kissat.FullFidelityCongProof0
public import LeanQbe.T.Examples.Kissat.FullM8CongEnqEvalProof
import LeanQbe.T.Examples.Kissat.FullCongLemmas1
import LeanQbe.T.Examples.Kissat.FullCongLemmas2

/-!
# Kissat Fidelity Step 12B — Congruence Invariants, Specs & Pure Lemmas
(`FullFidelityStep12BProofSpec`)

Defines wide-AND congruence invariants (`Step12BGateAt`, `Step12BGateSeqOk`, `Step12BCongHtInv`,
`Step12BOccNodePtrOk`, `Step12BOccNodesOk`, `Step12BCtrlLayout`, `Step12BQueueCtx`,
`Step12BScrFrame`) supporting:
- AND arity up to `congruenceandarity = 1,000,000` (`tag = 0` for `2 ≤ arity ≤ 64`,
  `tag = 3` for `65 ≤ arity ≤ 1,000,000`, keeping `tag ∈ {0, 1, 2}` bit-identical to `FidGateAt`),
- 3-word occurrence nodes `(gn, raw_lit, nxt)` eliminating 8-bit `slot_i` overflow,
- dynamic power-of-2 `occ_bkt ≤ 1,048,576` (`p ≤ 20`).

Also provides all `Spec` contracts for `FullFidelityStep12BCong`, bridges from `M6`/`M8`/`Fid`
invariants, and `List.filter` counting lemmas for `lit_mark` `u32` deduplication.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12B

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open LeanQbe.T.Examples.Kissat.FullM8FidV12
open LeanQbe.T.Examples.Kissat.FullFidelityCong
open Kraken.Bedrock2.Test

/-! ## 1. Wide-AND Gate, 3-Word Occurrence Node & Dynamic `occ_bkt` Invariants -/

@[expose] public section

/-- Maximum AND gate arity (`congruenceandarity`, Kissat 4.0.4 `src/options.h:26`). -/
def step12BCongAndArityMax : Nat := 1000000

/-- Maximum dynamic power-of-2 `occ_bkt` (`2^20 = 1,048,576`). -/
def step12BOccBktMax : Nat := 1048576

/-- Decoded arity of a Step-12B gate meta word: 28-bit for `tag = 3` (wide AND), 8-bit otherwise. -/
def step12BGateArity (mword : BitVec 32) : Nat :=
  if (mword >>> 28) = 3#32 then (mword &&& 0x0FFFFFFF#32).toNat
  else (mword &&& 0xFF#32).toNat

/-- Valid extracted gate parameterized by maximum AND arity `maxA ≤ 1,000,000`.
`tag = 0` carries narrow AND (`2 ≤ arity ≤ 64`), `tag = 3` carries wide AND (`65 ≤ arity`),
`tag = 1` carries XOR (`2 ≤ arity ≤ 4`), and `tag = 2` carries ITE (`arity = 3`). -/
def Step12BGateAt (maxA : Nat) (F_cur : List (List Nat)) (cur_vars : Nat)
    (scr : List (BitVec 32)) (g_len g : Nat) : Prop :=
  ∃ (lhs mword : BitVec 32),
    scr[g]? = some lhs ∧ scr[g + 1]? = some mword ∧
    lhs.toNat < 2 * cur_vars ∧
    let tag := (mword >>> 28).toNat
    let arity := step12BGateArity mword
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

/-- Contiguous sequence of valid `Step12BGateAt maxA` gates in `scr[g ..< g_len)`. -/
inductive Step12BGateSeqOk (maxA : Nat) (F_cur : List (List Nat)) (cur_vars : Nat)
    (scr : List (BitVec 32)) (g_len : Nat) : Nat → Prop where
  | done : Step12BGateSeqOk maxA F_cur cur_vars scr g_len g_len
  | step {g : Nat} (hg : Step12BGateAt maxA F_cur cur_vars scr g_len g) :
      Step12BGateSeqOk maxA F_cur cur_vars scr g_len
        (g + 2 + step12BGateArity (scr[g + 1]?.getD 0#32)) →
      Step12BGateSeqOk maxA F_cur cur_vars scr g_len g

/-- Every non-empty hash slot in `scr[ht_off ..< ht_off + ht_sz)` points to a valid
`Step12BGateAt maxA` gate in `scr0[0 ..< g_len)`. -/
def Step12BCongHtInv (maxA : Nat) (F_cur : List (List Nat)) (cur_vars : Nat)
    (scr0 scr : List (BitVec 32)) (g_len ht_off ht_sz : Nat) : Prop :=
  ∀ k < ht_sz,
    let ent := scr[ht_off + k]?.getD 0xFFFFFFFF#32
    ent = 0xFFFFFFFF#32 ∨ Step12BGateAt maxA F_cur cur_vars scr0 g_len ent.toNat

/-- Valid 3-word occ-node pointer: `0xFFFFFFFF` (nil) or aligned index in `[g_len, occ_end)`. -/
def Step12BOccNodePtrOk (g_len occ_end : Nat) (p : BitVec 32) : Prop :=
  p = 0xFFFFFFFF#32 ∨ (g_len ≤ p.toNat ∧ p.toNat + 2 < occ_end ∧ (p.toNat - g_len) % 3 = 0)

/-- Occurrence bucket heads and 3-word occurrence nodes `(gn, raw_lit, nxt)` in
`scr[g_len ..< occ_end)` point only to valid `Step12BGateAt maxA` gates, valid literals `< 2*cv`,
and valid 3-word node pointers. -/
def Step12BOccNodesOk (maxA : Nat) (F_cur : List (List Nat))
    (cv g_len occ_end ctrl_off bkt_off occ_bkt : Nat) (scr0 scr : List (BitVec 32)) : Prop :=
  g_len ≤ occ_end ∧ occ_end ≤ ctrl_off ∧
  (∀ b < occ_bkt, Step12BOccNodePtrOk g_len occ_end (scr[bkt_off + b]?.getD 0xFFFFFFFF#32)) ∧
  (∀ nd, g_len ≤ nd → nd + 2 < occ_end → (nd - g_len) % 3 = 0 →
    let gn := (scr[nd]?.getD 0#32).toNat
    let raw_lit := (scr[nd + 1]?.getD 0#32).toNat
    gn < g_len ∧ Step12BGateAt maxA F_cur cv scr0 g_len gn ∧
    raw_lit < 2 * cv ∧
    Step12BOccNodePtrOk g_len occ_end (scr[nd + 2]?.getD 0xFFFFFFFF#32))

/-- Dynamic power-of-2 congruence ctrl layout (`occ_bkt = 2^p ≤ 1,048,576`, `1 ≤ p ≤ 20`). -/
def Step12BCtrlLayout (c : FullCfg) (scr : List (BitVec 32)) (g_len ctrl_off occ_bkt bkt_off
    inq_off q_off ht_off ht_sz : Nat) : Prop :=
  ctrl_off < c.scratch_cap ∧ ctrl_off + 8 ≤ c.scratch_cap ∧
  g_len ≤ ctrl_off ∧ g_len ≤ 0x01000000 ∧
  scr[ctrl_off]?.getD 0#32 = BitVec.ofNat 32 occ_bkt ∧
  scr[ctrl_off + 1]?.getD 0#32 = BitVec.ofNat 32 bkt_off ∧
  scr[ctrl_off + 2]?.getD 0#32 = BitVec.ofNat 32 inq_off ∧
  scr[ctrl_off + 3]?.getD 0#32 = BitVec.ofNat 32 q_off ∧
  scr[ctrl_off + 6]?.getD 0#32 = BitVec.ofNat 32 ht_off ∧
  scr[ctrl_off + 7]?.getD 0#32 = BitVec.ofNat 32 ht_sz ∧
  0 < occ_bkt ∧ occ_bkt ≤ step12BOccBktMax ∧ (∃ p : Nat, 1 ≤ p ∧ p ≤ 20 ∧ occ_bkt = 2 ^ p) ∧
  0 < ht_sz ∧
  ctrl_off + 8 ≤ q_off ∧ q_off + occ_bkt ≤ inq_off ∧
  inq_off + occ_bkt ≤ bkt_off ∧ bkt_off + occ_bkt ≤ ht_off ∧
  ht_off + ht_sz ≤ c.scratch_cap ∧
  (scr[ctrl_off + 4]?.getD 0#32).toNat < occ_bkt ∧
  (scr[ctrl_off + 5]?.getD 0#32).toNat ≤ occ_bkt ∧
  (∀ k < (scr[ctrl_off + 5]?.getD 0#32).toNat,
    (scr[q_off + ((scr[ctrl_off + 4]?.getD 0#32).toNat + k) % occ_bkt]?.getD 0#32).toNat <
      occ_bkt)

/-- Queue context passed to `full_cong_enq_var` and `full_cong_eval_gate`: inactive
(`ctrl_off = c.scratch_cap`) or a live disjoint `Step12BCtrlLayout`. -/
def Step12BQueueCtx (c : FullCfg) (scr : List (BitVec 32))
    (g_len ctrl_off ht_off ht_sz : Nat) : Prop :=
  ctrl_off = c.scratch_cap ∨
  ∃ occ_bkt bkt_off inq_off q_off,
    Step12BCtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz

/-- Scratch-buffer frame invariant for `full_cong_eval_gate`. -/
def Step12BScrFrame (c : FullCfg) (g_len ctrl_off ht_off ht_sz : Nat)
    (scr0 scr : List (BitVec 32)) : Prop :=
  scr.length = c.scratch_cap ∧
  ∀ idx < c.scratch_cap, idx < ht_off →
    (ctrl_off = c.scratch_cap → scr[idx]? = scr0[idx]?) ∧
    (∀ occ_bkt bkt_off inq_off q_off,
      Step12BCtrlLayout c scr0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz →
      idx ≠ ctrl_off + 5 →
      ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
      ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) →
      scr[idx]? = scr0[idx]?)

/-! ## 2. Owned Function `Spec` Contracts (`FullFidelityStep12BCong`) -/

/-- `full_cong_extract_and_clause_fid`: single-pass `O(D)` marked watch scan emitting AND gates
up to `maxA ≤ 1,000,000` (`tag = 0` for `arity ≤ 64`, `tag = 3` for `arity ≥ 65`). -/
def step12BCongExtractAndClauseSpec : Spec [i64, i32, i64, i64, i64] [i64] :=
  fun (h, usz, g_len, g_cap, _tick_lim, ()) m Q _ =>
    ∃ (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      maxA ≤ step12BCongAndArityMax ∧
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
      3 ≤ usz.toNat ∧ usz.toNat - 1 ≤ maxA ∧ usz.toNat ≤ s.core.cur_vars ∧
      g_len.toNat ≤ g_cap.toNat ∧ g_cap.toNat ≤ c.scratch_cap ∧
      Step12BGateSeqOk maxA F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (∀ j < usz.toNat, (s.scratch.work_stk2[j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (∀ j < usz.toNat, ∀ j2 < usz.toNat, j ≠ j2 →
        (s.scratch.work_stk2[j]?.getD 0#32).toNat ≠ (s.scratch.work_stk2[j2]?.getD 0#32).toNat) ∧
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
        Step12BGateSeqOk maxA F_cur s.core.cur_vars scr' ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

/-- `full_cong_extract_from_fid`: appends AND (`≤ 1,000,000`) & XOR (`k = 3..5`) gates onto an
existing `FidGateSeqOk 64` prefix starting at `g_start`. -/
def step12BCongExtractFromSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (h, g_start, g_cap, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
      g_start.toNat ≤ g_cap.toNat ∧ g_cap.toNat ≤ c.scratch_cap ∧
      FidGateSeqOk 64 F_cur s.core.cur_vars s.scratch.scratch_buf g_start.toNat 0 ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (s' : FullState) (m' : Mem 64),
        FullDenseInvW c F0 F_cur s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.core.repr = s.core.repr → s'.core.inconsistent = s.core.inconsistent →
        g_start.toNat ≤ ret.toNat → ret.toNat ≤ g_cap.toNat →
        Step12BGateSeqOk step12BCongAndArityMax F_cur s.core.cur_vars
          s'.scratch.scratch_buf ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

/-- `full_cong_extract`: emits `Step12BGateSeqOk 1000000` from scratch offset `0`. -/
def step12BCongExtractSpec : Spec [i64, i64, i64] [i64] :=
  fun (h, g_cap, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ g_cap.toNat ≤ c.scratch_cap ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (s' : FullState) (m' : Mem 64),
        FullDenseInvW c F0 F_cur s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.core.repr = s.core.repr → s'.core.inconsistent = s.core.inconsistent →
        ret.toNat ≤ g_cap.toNat →
        Step12BGateSeqOk step12BCongAndArityMax F_cur s.core.cur_vars
          s'.scratch.scratch_buf ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

/-- `full_cong_and_match`: `O(ea + ua)` `lit_mark` + `u32` counter matcher up to `1,000,000`. -/
def step12BCongAndMatchSpec : Spec [i64, i32, i32] [.bool] := fun (h, ent, ua, ()) m Q _ =>
  ∃ (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (scr0 : List (BitVec 32)) (g_len : Nat) (R : Mem 64 → Prop),
    maxA ≤ step12BCongAndArityMax ∧ h = c.hdr ∧ s.LengthsOk c ∧
    FullWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
    s.core.cur_level = 0 ∧ FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
    g_len ≤ c.scratch_cap ∧
    (∀ idx < g_len, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
    Step12BGateAt maxA F_cur s.core.cur_vars scr0 g_len ent.toNat ∧
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
      (ok = true → 2 ≤ ua.toNat ∧ ua.toNat ≤ step12BCongAndArityMax ∧
        ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
          evalLitVal α (scr0[ent.toNat]?.getD 0#32).toNat =
            (List.range ua.toNat).all fun k =>
              evalLitVal α (s.core.tmp[k]?.getD 0#32).toNat) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- `full_cong_enq_var` with dynamic power-of-2 `occ_bkt ≤ 1,048,576`. -/
def step12BCongEnqVarSpec : Spec [i64, i64, i32] [] := fun (h, ctrl_off, _v, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (g_len ht_off ht_sz : Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧
    Step12BQueueCtx c s.scratch.scratch_buf g_len ctrl_off.toNat ht_off ht_sz ∧
    (FullMem c s ⋆ R) m ∧
    ∀ scr' m',
      scr'.length = c.scratch_cap →
      Step12BQueueCtx c scr' g_len ctrl_off.toNat ht_off ht_sz →
      (ctrl_off.toNat = c.scratch_cap → scr' = s.scratch.scratch_buf) →
      (∀ occ_bkt bkt_off inq_off q_off,
        Step12BCtrlLayout c s.scratch.scratch_buf g_len ctrl_off.toNat occ_bkt bkt_off inq_off
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

/-- `full_cong_eval_gate` supporting wide AND (`≤ 1,000,000`) & dynamic `occ_bkt ≤ 1,048,576`. -/
def step12BCongEvalGateSpec : Spec [i64, i64, i64, i64, i32, i64] [i64] :=
  fun (h, g, ht_off, ht_sz, _next_ep, ctrl_off, ()) m Q _ =>
    ∃ (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (scr0 : List (BitVec 32)) (g_len : Nat) (R : Mem 64 → Prop),
      maxA ≤ step12BCongAndArityMax ∧ h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      0 < ht_sz.toNat ∧ ht_sz.toNat < 2 ^ 30 ∧
      g.toNat < g_len ∧ g_len ≤ ht_off.toNat ∧ ht_off.toNat + ht_sz.toNat ≤ c.scratch_cap ∧
      (∀ idx < g_len, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
      Step12BGateAt maxA F_cur s.core.cur_vars scr0 g_len g.toNat ∧
      Step12BCongHtInv maxA F_cur s.core.cur_vars scr0 s.scratch.scratch_buf
        g_len ht_off.toNat ht_sz.toNat ∧
      Step12BQueueCtx c s.scratch.scratch_buf g_len ctrl_off.toNat ht_off.toNat ht_sz.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) s' m',
        FullDenseInvW c F0 F_cur s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
        FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
        (∀ idx < g_len, s'.scratch.scratch_buf[idx]? = scr0[idx]?) →
        Step12BCongHtInv maxA F_cur s'.core.cur_vars scr0 s'.scratch.scratch_buf
          g_len ht_off.toNat ht_sz.toNat →
        Step12BQueueCtx c s'.scratch.scratch_buf g_len ctrl_off.toNat ht_off.toNat ht_sz.toNat →
        ((r &&& 2#64) = 0#64 →
          (∀ idx < c.scratch_cap, idx < ht_off.toNat →
            (ctrl_off.toNat = c.scratch_cap →
              s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) ∧
            (∀ occ_bkt bkt_off inq_off q_off,
              Step12BCtrlLayout c s.scratch.scratch_buf g_len ctrl_off.toNat occ_bkt bkt_off
                inq_off q_off ht_off.toNat ht_sz.toNat →
              idx ≠ ctrl_off.toNat + 5 →
              ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
              ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) →
              s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?))) →
        ((r &&& 2#64) ≠ 0#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `full_cong_worklist` supporting wide AND (`≤ 1,000,000`), 3-word occurrence nodes, dynamic
`occ_bkt ≤ 1,048,576`, and dynamic in-place HT doubling up to `1,048,576`. -/
def step12BCongWorklistSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (h, g_len, ctrl_off, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (scr0 : List (BitVec 32)) (occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      0 < g_len.toNat ∧ ht_sz ≤ fidCongHashMaxSz ∧
      Step12BCtrlLayout c s.scratch.scratch_buf g_len.toNat ctrl_off.toNat occ_bkt bkt_off
        inq_off q_off ht_off ht_sz ∧
      Step12BGateSeqOk step12BCongAndArityMax F_cur s.core.cur_vars scr0 g_len.toNat 0 ∧
      (∀ idx < g_len.toNat, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
      Step12BCongHtInv step12BCongAndArityMax F_cur s.core.cur_vars scr0 s.scratch.scratch_buf
        g_len.toNat ht_off ht_sz ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullDenseInvW c F0 F_cur s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

end

/-! ## 3. Bridges, Monotonicity & Pure Counting Lemmas -/

public section

theorem step12BGateArity_of_ne3 {mword : BitVec 32} (h : (mword >>> 28) ≠ 3#32) :
    step12BGateArity mword = (mword &&& 0xFF#32).toNat := by
  simp [step12BGateArity, h]

theorem step12BGateArity_of_eq3 {mword : BitVec 32} (h : (mword >>> 28) = 3#32) :
    step12BGateArity mword = (mword &&& 0x0FFFFFFF#32).toNat := by
  simp [step12BGateArity, h]

theorem step12BGateAt_mono {maxA maxB : Nat} (hle : maxA ≤ maxB)
    {F_cur : List (List Nat)} {cv : Nat} {scr : List (BitVec 32)} {g_len g : Nat}
    (h : Step12BGateAt maxA F_cur cv scr g_len g) : Step12BGateAt maxB F_cur cv scr g_len g := by
  obtain ⟨lhs, mword, h0, h1, hlhs, hbd, hcv, ha, hrhs, hsem⟩ := h
  exact ⟨lhs, mword, h0, h1, hlhs, hbd, hcv, Nat.le_trans ha hle, hrhs, hsem⟩

theorem step12BGateAt_of_fid {maxA : Nat} (h64 : maxA ≤ 64)
    {F_cur : List (List Nat)} {cv : Nat} {scr : List (BitVec 32)} {g_len g : Nat}
    (h : FidGateAt maxA F_cur cv scr g_len g) : Step12BGateAt maxA F_cur cv scr g_len g := by
  obtain ⟨lhs, mword, h0, h1, hlhs, hbd, hcv, ha, hrhs, hsem⟩ := h
  have hne3 : (mword >>> 28) ≠ 3#32 := by
    intro h3
    have h3n : (mword >>> 28).toNat = 3 := by rw [h3]; rfl
    rcases hsem with ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨ht, _⟩ <;> omega
  have har : step12BGateArity mword = (mword &&& 0xFF#32).toNat := step12BGateArity_of_ne3 hne3
  refine ⟨lhs, mword, h0, h1, hlhs, har ▸ hbd, har ▸ hcv, har ▸ ha, har ▸ hrhs, ?_⟩
  rw [har]
  rcases hsem with ⟨ht, h2, hand⟩ | ⟨ht, h2, h4, hxor⟩ | ⟨ht, h3, hite⟩
  · exact Or.inl ⟨Or.inl ⟨ht, h2, by omega⟩, hand⟩
  · exact Or.inr (Or.inl ⟨ht, h2, h4, hxor⟩)
  · exact Or.inr (Or.inr ⟨ht, h3, hite⟩)

theorem step12BGateAt_to_fid {maxA : Nat} (h64 : maxA ≤ 64)
    {F_cur : List (List Nat)} {cv : Nat} {scr : List (BitVec 32)} {g_len g : Nat}
    (h : Step12BGateAt maxA F_cur cv scr g_len g) : FidGateAt maxA F_cur cv scr g_len g := by
  obtain ⟨lhs, mword, h0, h1, hlhs, hbd, hcv, ha, hrhs, hsem⟩ := h
  have hne3 : (mword >>> 28) ≠ 3#32 := by
    intro h3
    have h3n : (mword >>> 28).toNat = 3 := by rw [h3]; rfl
    rcases hsem with ⟨⟨ht, _⟩ | ⟨_, h65⟩, _⟩ | ⟨ht, _⟩ | ⟨ht, _⟩ <;> omega
  have har : step12BGateArity mword = (mword &&& 0xFF#32).toNat := step12BGateArity_of_ne3 hne3
  rw [har] at hbd hcv ha hrhs hsem
  refine ⟨lhs, mword, h0, h1, hlhs, hbd, hcv, ha, hrhs, ?_⟩
  rcases hsem with ⟨⟨ht, h2, _⟩ | ⟨_, h65⟩, hand⟩ | ⟨ht, h2, h4, hxor⟩ | ⟨ht, h3, hite⟩
  · exact Or.inl ⟨ht, h2, hand⟩
  · omega
  · exact Or.inr (Or.inl ⟨ht, h2, h4, hxor⟩)
  · exact Or.inr (Or.inr ⟨ht, h3, hite⟩)

theorem step12BGateAt_to_m6_of_xor {maxA : Nat} {F_cur : List (List Nat)} {cv : Nat}
    {scr : List (BitVec 32)} {g_len g : Nat}
    (h : Step12BGateAt maxA F_cur cv scr g_len g)
    (htag : (scr[g + 1]?.getD 0#32 >>> 28) = 1#32) :
    M6GateAt F_cur cv scr g_len g := by
  obtain ⟨lhs, mword, h0, h1, hlhs, hbd, hcv, _, hrhs, hsem⟩ := h
  have hm1 : (mword >>> 28) = 1#32 := by rwa [h1, Option.getD_some] at htag
  have ht1 : (mword >>> 28).toNat = 1 := by rw [hm1]; rfl
  have har : step12BGateArity mword = (mword &&& 0xFF#32).toNat :=
    step12BGateArity_of_ne3 (by rw [hm1]; decide)
  rw [har] at hbd hcv hrhs hsem
  rcases hsem with ⟨⟨h0t, _⟩ | ⟨h3t, _⟩, _⟩ | ⟨_, h2, h4, hxor⟩ | ⟨h2t, _⟩
  · omega
  · omega
  · exact ⟨lhs, mword, h0, h1, hlhs, hbd, hcv, by omega, hrhs, Or.inr (Or.inl ⟨ht1, h2, h4, hxor⟩)⟩
  · omega

theorem step12BGateAt_frame {maxA : Nat} {F_cur : List (List Nat)} {cv g_len g : Nat}
    {scr scr' : List (BitVec 32)}
    (hpref : ∀ idx < g_len, scr'[idx]? = scr[idx]?)
    (h : Step12BGateAt maxA F_cur cv scr g_len g) : Step12BGateAt maxA F_cur cv scr' g_len g := by
  obtain ⟨lhs, mword, h0, h1, hlhs, hbd, hcv, ha, hrhs, hsem⟩ := h
  have hdt : (scr'.drop (g + 2)).take (step12BGateArity mword) =
      (scr.drop (g + 2)).take (step12BGateArity mword) := by
    have hle1 : g + 2 + step12BGateArity mword ≤ scr.length := by
      have h1l : g + 1 < scr.length := (List.getElem?_eq_some_iff.mp h1).1
      rcases Nat.eq_zero_or_pos (step12BGateArity mword) with hz | hp
      · omega
      · obtain ⟨_, hr, _⟩ := hrhs (step12BGateArity mword - 1) (by omega)
        have hrl := (List.getElem?_eq_some_iff.mp hr).1; omega
    have hle2 : g + 2 + step12BGateArity mword ≤ scr'.length := by
      have h1' := (hpref (g + 1) (by omega)).trans h1
      have h1l : g + 1 < scr'.length := (List.getElem?_eq_some_iff.mp h1').1
      rcases Nat.eq_zero_or_pos (step12BGateArity mword) with hz | hp
      · omega
      · obtain ⟨_, hr, _⟩ := hrhs (step12BGateArity mword - 1) (by omega)
        have hr' := (hpref (g + 2 + (step12BGateArity mword - 1)) (by omega)).trans hr
        have hrl := (List.getElem?_eq_some_iff.mp hr').1; omega
    refine List.ext_getElem
      (by simp only [List.length_take, List.length_drop]; omega) fun k hk1 _ => ?_
    simp only [List.getElem_take, List.getElem_drop]
    have hk_lt : k < step12BGateArity mword := by
      simp only [List.length_take, List.length_drop] at hk1; omega
    have heq := hpref (g + 2 + k) (by omega)
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at heq
    exact Option.some.inj heq
  refine ⟨lhs, mword, (hpref g (by omega)).trans h0, (hpref (g + 1) (by omega)).trans h1,
    hlhs, hbd, hcv, ha, fun k hk => ?_, ?_⟩
  · obtain ⟨r, hr, hlt⟩ := hrhs k hk
    exact ⟨r, (hpref (g + 2 + k) (by omega)).trans hr, hlt⟩
  · rcases hsem with ⟨ht, hand⟩ | ⟨ht, h2, h4, hxor⟩ | ⟨ht, h3, hite⟩
    · exact Or.inl ⟨ht, by rwa [hdt]⟩
    · exact Or.inr (Or.inl ⟨ht, h2, h4, by rwa [hdt]⟩)
    · refine Or.inr (Or.inr ⟨ht, h3, ?_⟩)
      rw [hpref (g + 2) (by omega), hpref (g + 3) (by omega), hpref (g + 4) (by omega)]
      exact hite

theorem step12BGateAt_ext_len {maxA : Nat} {F_cur : List (List Nat)} {cv g_len g_len' g : Nat}
    {scr : List (BitVec 32)} (hle : g_len ≤ g_len')
    (h : Step12BGateAt maxA F_cur cv scr g_len g) : Step12BGateAt maxA F_cur cv scr g_len' g := by
  obtain ⟨lhs, mword, h0, h1, hlhs, hbd, hcv, ha, hrhs, hsem⟩ := h
  exact ⟨lhs, mword, h0, h1, hlhs, Nat.le_trans hbd hle, hcv, ha, hrhs, hsem⟩

theorem step12BGateSeqOk_mono {maxA maxB : Nat} (hle : maxA ≤ maxB)
    {F_cur : List (List Nat)} {cv : Nat} {scr : List (BitVec 32)} {g_len g : Nat}
    (h : Step12BGateSeqOk maxA F_cur cv scr g_len g) :
    Step12BGateSeqOk maxB F_cur cv scr g_len g := by
  induction h with
  | done => exact .done
  | step hg _ ih => exact .step (step12BGateAt_mono hle hg) ih

theorem step12BGateSeqOk_of_fid {maxA : Nat} (h64 : maxA ≤ 64)
    {F_cur : List (List Nat)} {cv : Nat} {scr : List (BitVec 32)} {g_len g : Nat}
    (h : FidGateSeqOk maxA F_cur cv scr g_len g) :
    Step12BGateSeqOk maxA F_cur cv scr g_len g := by
  induction h with
  | done => exact .done
  | @step g0 hg _ ih =>
    have hg' := step12BGateAt_of_fid h64 hg
    obtain ⟨_, mword, _, h1, _, _, _, _, _, hsem⟩ := hg
    have hne3 : (mword >>> 28) ≠ 3#32 := by
      intro h3; have h3n : (mword >>> 28).toNat = 3 := by rw [h3]; rfl
      rcases hsem with ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨ht, _⟩ <;> omega
    have har : step12BGateArity (scr[g0 + 1]?.getD 0#32) =
        ((scr[g0 + 1]?.getD 0#32) &&& 0xFF#32).toNat := by
      rw [h1, Option.getD_some]; exact step12BGateArity_of_ne3 hne3
    exact .step hg' (by rw [har]; exact ih)

theorem step12BGateSeqOk_to_fid {maxA : Nat} (h64 : maxA ≤ 64)
    {F_cur : List (List Nat)} {cv : Nat} {scr : List (BitVec 32)} {g_len g : Nat}
    (h : Step12BGateSeqOk maxA F_cur cv scr g_len g) :
    FidGateSeqOk maxA F_cur cv scr g_len g := by
  induction h with
  | done => exact .done
  | @step g0 hg _ ih =>
    have hg' := step12BGateAt_to_fid h64 hg
    have ⟨_, mword, _, h1, _, _, _, _, _, hsem⟩ := hg'
    have hne3 : (mword >>> 28) ≠ 3#32 := by
      intro h3; have h3n : (mword >>> 28).toNat = 3 := by rw [h3]; rfl
      rcases hsem with ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨ht, _⟩ <;> omega
    have har : step12BGateArity (scr[g0 + 1]?.getD 0#32) =
        ((scr[g0 + 1]?.getD 0#32) &&& 0xFF#32).toNat := by
      rw [h1, Option.getD_some]; exact step12BGateArity_of_ne3 hne3
    rw [har] at ih
    exact .step hg' ih

theorem step12BGateSeqOk_append_gate {maxA : Nat} {F_cur : List (List Nat)}
    {cv g_len g_len' g : Nat}
    {scr scr' : List (BitVec 32)}
    (hpref : ∀ idx < g_len, scr'[idx]? = scr[idx]?)
    (hseq : Step12BGateSeqOk maxA F_cur cv scr g_len g)
    (htail : Step12BGateSeqOk maxA F_cur cv scr' g_len' g_len)
    (hle : g_len ≤ g_len') :
    Step12BGateSeqOk maxA F_cur cv scr' g_len' g := by
  induction hseq with
  | done => exact htail
  | @step g0 hg _ ih =>
    have hg' := step12BGateAt_ext_len hle (step12BGateAt_frame hpref hg)
    obtain ⟨_, mword, _, h1, _, hbd, _, _, _, _⟩ := hg
    have hm_eq : scr'[g0 + 1]?.getD 0#32 = scr[g0 + 1]?.getD 0#32 := by
      rw [hpref (g0 + 1) (by omega)]
    exact .step hg' (by rw [hm_eq]; exact ih)

theorem step12BGateSeqOk_inv_lt {maxA : Nat} {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr : List (BitVec 32)} {g_len g : Nat}
    (hs : Step12BGateSeqOk maxA F_cur cur_vars scr g_len g) (hlt : g < g_len) :
    Step12BGateAt maxA F_cur cur_vars scr g_len g ∧
      Step12BGateSeqOk maxA F_cur cur_vars scr g_len
        (g + 2 + step12BGateArity (scr[g + 1]?.getD 0#32)) := by
  cases hs with
  | done => omega
  | step hg hrest => exact ⟨hg, hrest⟩

theorem step12BCongHtInv_mono {maxA maxB : Nat} (hle : maxA ≤ maxB)
    {F_cur : List (List Nat)} {cv : Nat} {scr0 scr : List (BitVec 32)} {g_len ht_off ht_sz : Nat}
    (h : Step12BCongHtInv maxA F_cur cv scr0 scr g_len ht_off ht_sz) :
    Step12BCongHtInv maxB F_cur cv scr0 scr g_len ht_off ht_sz := fun k hk =>
  (h k hk).elim Or.inl fun hg => Or.inr (step12BGateAt_mono hle hg)

theorem step12BCongHtInv_of_fid {maxA : Nat} (h64 : maxA ≤ 64)
    {F_cur : List (List Nat)} {cv : Nat} {scr0 scr : List (BitVec 32)} {g_len ht_off ht_sz : Nat}
    (h : FidCongHtInv maxA F_cur cv scr0 scr g_len ht_off ht_sz) :
    Step12BCongHtInv maxA F_cur cv scr0 scr g_len ht_off ht_sz := fun k hk =>
  (h k hk).elim Or.inl fun hg => Or.inr (step12BGateAt_of_fid h64 hg)

theorem step12BCongHtInv_to_fid {maxA : Nat} (h64 : maxA ≤ 64)
    {F_cur : List (List Nat)} {cv : Nat} {scr0 scr : List (BitVec 32)} {g_len ht_off ht_sz : Nat}
    (h : Step12BCongHtInv maxA F_cur cv scr0 scr g_len ht_off ht_sz) :
    FidCongHtInv maxA F_cur cv scr0 scr g_len ht_off ht_sz := fun k hk =>
  (h k hk).elim Or.inl fun hg => Or.inr (step12BGateAt_to_fid h64 hg)

theorem step12BCongHtInv_set_gate {maxA : Nat} {F_cur : List (List Nat)}
    {cv g_len ht_off ht_sz : Nat}
    {scr0 scr : List (BitVec 32)} {slot : Nat} {g : BitVec 32}
    (hinv : Step12BCongHtInv maxA F_cur cv scr0 scr g_len ht_off ht_sz)
    (hslot : slot < ht_sz) (harr : ht_off + slot < scr.length)
    (hg : Step12BGateAt maxA F_cur cv scr0 g_len g.toNat) :
    Step12BCongHtInv maxA F_cur cv scr0 (scr.set (ht_off + slot) g) g_len ht_off ht_sz := by
  intro k hk
  by_cases hks : k = slot
  · subst hks; right; rw [List.getElem?_set_self harr, Option.getD_some]; exact hg
  · rw [List.getElem?_set_ne (by omega)]; exact hinv k hk

/-! ## 4. Dynamic `Step12BCtrlLayout` & `Step12BScrFrame` (`p ≤ 20`, `occ_bkt ≤ 1,048,576`) -/

theorem step12B_pow2_sub1_and_eq_mod {n p : Nat} (_hp : 1 ≤ p) (hp20 : p ≤ 20) (x : BitVec 32)
    (hn : n = 2 ^ p) : (x &&& (BitVec.ofNat 32 n - 1#32)).toNat = x.toNat % n := by
  have hlt : 2 ^ p ≤ 1048576 := Nat.pow_le_pow_right (by omega) hp20
  have hsub : (BitVec.ofNat 32 n - 1#32).toNat = 2 ^ p - 1 := by
    have hof : (BitVec.ofNat 32 n).toNat = 2 ^ p := by
      rw [hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hof]; exact Nat.one_le_two_pow)), hof]
    rfl
  rw [BitVec.toNat_and, hsub, hn, Nat.and_two_pow_sub_one_eq_mod]

theorem step12B_and_sub1_u32_eq_mod {occ_bkt : Nat}
    (hp : ∃ p : Nat, 1 ≤ p ∧ p ≤ 20 ∧ occ_bkt = 2 ^ p) (x : BitVec 32) :
    (x &&& (BitVec.ofNat 32 occ_bkt - 1#32)).toNat = x.toNat % occ_bkt := by
  obtain ⟨p, h1, h2, rfl⟩ := hp; exact step12B_pow2_sub1_and_eq_mod h1 h2 x rfl

theorem m8CtrlLayout_to_step12B {c : FullCfg} {scr : List (BitVec 32)}
    {g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (h : M8CtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz) :
    Step12BCtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz := by
  rcases h with ⟨h1, h2, h3, h4, s0, s1, s2, s3, s6, s7, h5, h6, ⟨p, hp1, hp13, rfl⟩,
    h7, h8, h9, h10, h11, h12, hqh, hql, hqok⟩
  exact ⟨h1, h2, h3, h4, s0, s1, s2, s3, s6, s7, h5, by unfold step12BOccBktMax; omega,
    ⟨p, hp1, by omega, rfl⟩, h7, h8, h9, h10, h11, h12, hqh, hql, hqok⟩

theorem m8QueueCtx_to_step12B {c : FullCfg} {scr : List (BitVec 32)}
    {g_len ctrl_off ht_off ht_sz : Nat}
    (h : M8QueueCtx c scr g_len ctrl_off ht_off ht_sz) :
    Step12BQueueCtx c scr g_len ctrl_off ht_off ht_sz := by
  rcases h with rfl | ⟨o, b, i, q, hl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨o, b, i, q, m8CtrlLayout_to_step12B hl⟩

theorem step12BCtrlLayout_set_q {c : FullCfg} {scr : List (BitVec 32)}
    {g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (h : Step12BCtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    {scr' : List (BitVec 32)} (_hlen' : scr'.length = scr.length)
    (hk05 : ∀ i < 8, i ≠ 4 → i ≠ 5 → scr'[ctrl_off + i]? = scr[ctrl_off + i]?)
    (hqh' : (scr'[ctrl_off + 4]?.getD 0#32).toNat < occ_bkt)
    (hql' : (scr'[ctrl_off + 5]?.getD 0#32).toNat ≤ occ_bkt)
    (hqok' : ∀ k < (scr'[ctrl_off + 5]?.getD 0#32).toNat,
      (scr'[q_off + ((scr'[ctrl_off + 4]?.getD 0#32).toNat + k) % occ_bkt]?.getD 0#32).toNat <
        occ_bkt) :
    Step12BCtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz := by
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

theorem step12BCtrlLayout_same_tail {c : FullCfg} {scr scr' : List (BitVec 32)}
    {g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (h : Step12BCtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hlen' : scr'.length = scr.length)
    (hql' : (scr'[ctrl_off + 5]?.getD 0#32).toNat ≤ occ_bkt)
    (hk : ∀ i < 8, i ≠ 5 → scr'[ctrl_off + i]? = scr[ctrl_off + i]?)
    (hqok' : ∀ k < (scr'[ctrl_off + 5]?.getD 0#32).toNat,
      (scr'[q_off + ((scr'[ctrl_off + 4]?.getD 0#32).toNat + k) % occ_bkt]?.getD 0#32).toNat <
        occ_bkt) :
    Step12BCtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz := by
  refine step12BCtrlLayout_set_q h hlen' (fun i hi _ h5 => hk i hi h5) ?_ hql' hqok'
  rw [hk 4 (by decide) (by decide)]; exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem step12BCtrlLayout_pop_q {c : FullCfg} {scr : List (BitVec 32)}
    {g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (h : Step12BCtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hlen : scr.length = c.scratch_cap)
    (hpos : 0 < (scr[ctrl_off + 5]?.getD 0#32).toNat) :
    let qh := scr[ctrl_off + 4]?.getD 0#32
    let ql := scr[ctrl_off + 5]?.getD 0#32
    let b := scr[q_off + qh.toNat]?.getD 0#32
    let nqh := (qh + 1#32) &&& (BitVec.ofNat 32 occ_bkt - 1#32)
    let scr' := ((scr.set (ctrl_off + 4) nqh).set (ctrl_off + 5) (ql - 1#32)).set
      (inq_off + b.toNat) 0#32
    b.toNat < occ_bkt ∧ nqh.toNat < occ_bkt ∧
    Step12BCtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz := by
  intro qh ql b nqh scr'
  rcases h with
    ⟨h1, h2, h3, h4, s0, s1, s2, s3, s6, s7, h5, h6, hpow, h7, h8, h9, h10, h11, h12,
     hqh_lt, hql_le, hqok⟩
  have hb_lt : b.toNat < occ_bkt := by
    have := hqok 0 hpos; rwa [Nat.add_zero, Nat.mod_eq_of_lt hqh_lt] at this
  have hnqh_lt : nqh.toNat < occ_bkt := by
    dsimp only [nqh]; rw [step12B_and_sub1_u32_eq_mod hpow]; exact Nat.mod_lt _ h5
  have hql_sub : (ql - 1#32).toNat = ql.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (show (1#32 : BitVec 32).toNat ≤ ql.toNat from
      Nat.succ_le_of_lt hpos))]; rfl
  have hnqh_mod : nqh.toNat = (qh.toNat + 1) % occ_bkt := by
    dsimp only [nqh]; rw [step12B_and_sub1_u32_eq_mod hpow]
    have hqh1 : (qh + 1#32).toNat = qh.toNat + 1 := by
      have hqh_lt' : qh.toNat < occ_bkt := hqh_lt
      rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt]
      unfold step12BOccBktMax at h6; omega
    rw [hqh1]
  have hscr'_ctrl : ∀ i, i < 8 → i ≠ 4 → i ≠ 5 → scr'[ctrl_off + i]? = scr[ctrl_off + i]? := by
    intro i _ h4' h5'; dsimp only [scr']
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
    dsimp only [scr']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
    exact hqok (k + 1) (by change k < (scr[ctrl_off + 5]?.getD 0#32).toNat - 1 at hk; omega)

theorem step12BCtrlLayout_unique {c : FullCfg} {scr : List (BitVec 32)}
    {g_len ctrl_off o1 b1 i1 q1 h1 s1 o2 b2 i2 q2 h2 s2 : Nat}
    (hl1 : Step12BCtrlLayout c scr g_len ctrl_off o1 b1 i1 q1 h1 s1)
    (hl2 : Step12BCtrlLayout c scr g_len ctrl_off o2 b2 i2 q2 h2 s2) :
    o1 = o2 ∧ b1 = b2 ∧ i1 = i2 ∧ q1 = q2 ∧ h1 = h2 ∧ s1 = s2 := by
  have heqc : ∀ {a b : Nat}, a < 2 ^ 32 → b < 2 ^ 32 →
      BitVec.ofNat 32 a = BitVec.ofNat 32 b → a = b := fun ha hb hv => by
    have h := congrArg BitVec.toNat hv
    rwa [bv32_ofNat_toNat ha, bv32_ofNat_toNat hb] at h
  rcases hl1 with ⟨_, _, _, _, e1_0, e1_1, e1_2, e1_3, e1_6, e1_7,
    _, ho1_le, _, _, _, _, _, _, hh1_hi, _, _, _⟩
  rcases hl2 with ⟨_, _, _, _, e2_0, e2_1, e2_2, e2_3, e2_6, e2_7,
    _, ho2_le, _, _, _, _, _, _, hh2_hi, _, _, _⟩
  have hsc := c.hscr; unfold dimacsBound at hsc; unfold step12BOccBktMax at ho1_le ho2_le
  exact ⟨heqc (by omega) (by omega) (e1_0.symm.trans e2_0),
    heqc (by omega) (by omega) (e1_1.symm.trans e2_1),
    heqc (by omega) (by omega) (e1_2.symm.trans e2_2),
    heqc (by omega) (by omega) (e1_3.symm.trans e2_3),
    heqc (by omega) (by omega) (e1_6.symm.trans e2_6),
    heqc (by omega) (by omega) (e1_7.symm.trans e2_7)⟩

theorem step12BScrFrame_refl {c : FullCfg} {g_len ctrl_off ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} (hlen : scr0.length = c.scratch_cap) :
    Step12BScrFrame c g_len ctrl_off ht_off ht_sz scr0 scr0 :=
  ⟨hlen, fun _ _ _ => ⟨fun _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩⟩

theorem step12BScrFrame_pref {c : FullCfg} {g_len ctrl_off ht_off ht_sz : Nat}
    {scr0 scr scr_init : List (BitVec 32)} (hle : g_len ≤ ht_off)
    (hht : ht_off + ht_sz ≤ c.scratch_cap)
    (hpref0 : ∀ idx < g_len, scr0[idx]? = scr_init[idx]?)
    (hq0 : Step12BQueueCtx c scr0 g_len ctrl_off ht_off ht_sz)
    (hfr : Step12BScrFrame c g_len ctrl_off ht_off ht_sz scr0 scr) :
    ∀ idx < g_len, scr[idx]? = scr_init[idx]? := by
  intro idx hidx
  have hlt_cap : idx < c.scratch_cap := by omega
  have hlt_ht : idx < ht_off := by omega
  rcases hq0 with rfl | ⟨occ_bkt, bkt_off, inq_off, q_off, hlay⟩
  · rw [(hfr.2 idx hlt_cap hlt_ht).1 rfl, hpref0 idx hidx]
  · have hlay_dup := hlay
    rcases hlay with ⟨_, _, hg_co, _, _, _, _, _, _, _, _, _, _, _, hcq, hqi, hib, hbh, _⟩
    rw [(hfr.2 idx hlt_cap hlt_ht).2 occ_bkt bkt_off inq_off q_off hlay_dup (by omega)
        (by omega) (by omega),
      hpref0 idx hidx]

theorem m6CongEvalGateSpec_inactive_to_step12B
    {hh g ht_off ht_sz ctrl_off : BitVec 64} {next_ep32 : BitVec 32} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (scr0 : List (BitVec 32)) (g_len : Nat) (R : Mem 64 → Prop),
      hh = c.hdr ∧ ctrl_off.toNat = c.scratch_cap ∧ FullDenseInvW c F0 F_cur s ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      0 < ht_sz.toNat ∧ ht_sz.toNat < 2 ^ 30 ∧
      g.toNat < g_len ∧ g_len ≤ ht_off.toNat ∧ ht_off.toNat + ht_sz.toNat ≤ c.scratch_cap ∧
      (∀ idx < g_len, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
      M6GateAt F_cur s.core.cur_vars scr0 g_len g.toNat ∧
      M6CongHtInv F_cur s.core.cur_vars scr0 s.scratch.scratch_buf g_len ht_off.toNat ht_sz.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) s' m',
        FullDenseInvW c F0 F_cur s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
        FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
        (∀ idx < g_len, s'.scratch.scratch_buf[idx]? = scr0[idx]?) →
        M6CongHtInv F_cur s'.core.cur_vars scr0 s'.scratch.scratch_buf
          g_len ht_off.toNat ht_sz.toNat →
        ((r &&& 2#64) = 0#64 →
          ∀ idx < c.scratch_cap, idx < ht_off.toNat →
            s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) →
        ((r &&& 2#64) ≠ 0#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    step12BCongEvalGateSpec (hh, g, ht_off, ht_sz, next_ep32, ctrl_off, ()) m Q X := by
  rcases h with ⟨c, F0, F_cur, s, scr0, g_len, R, rfl, hcap, hdw, hrepr, hht_pos, hht_bnd, hg_lt,
    hg_le_ht, hht_le, hpref, hgat, hht, hm, hQ⟩
  refine ⟨31, c, F0, F_cur, s, scr0, g_len, R, by unfold step12BCongAndArityMax; decide, rfl,
    hdw, hrepr, hht_pos, hht_bnd, hg_lt, hg_le_ht, hht_le, hpref,
    step12BGateAt_of_fid (by decide) (fidGateAt_of_m6 hgat),
    step12BCongHtInv_of_fid (by decide) (fidCongHtInv_of_m6 hht),
    Or.inl hcap, hm, ?_⟩
  intro r s' m' hdw' hcv' hfl' har' hal' hrepr' hpref' hht' _hq' hfr' huns' hm'
  exact hQ r s' m' hdw' hcv' hfl' har' hal' hrepr' hpref'
    (fidCongHtInv_to_m6 (step12BCongHtInv_to_fid (by decide) hht'))
    (fun hr2 idx h1 h2 => (hfr' hr2 idx h1 h2).1 hcap) huns' hm'

/-! ## 5. Pure `List.filter` Deduplication & Wide-AND Gate Emission Lemmas -/

/-- Filtered-length monotonicity: if `q` implies `p` on `L`, then `|filter q L| ≤ |filter p L|`. -/
theorem filter_length_le_of_imp {α : Type _} {p q : α → Bool} :
    ∀ (L : List α), (∀ x ∈ L, q x = true → p x = true) →
      (L.filter q).length ≤ (L.filter p).length
  | [], _ => Nat.le_refl _
  | a :: xs, himp => by
    have hrest := filter_length_le_of_imp xs (fun x hx => himp x (List.mem_cons_of_mem _ hx))
    simp only [List.filter_cons]
    cases hqa : q a
    · cases p a <;> simp <;> omega
    · have hpa : p a = true := himp a List.mem_cons_self hqa
      simp [hpa]; omega

/-- Pigeonhole on `List.filter`: if `q → p` on `L` and `|filter q L| = |filter p L|`, then
`p → q` on `L`. -/
theorem filter_sub_length_eq_imp_forall {α : Type _} {p q : α → Bool} :
    ∀ (L : List α), (∀ x ∈ L, q x = true → p x = true) →
      (L.filter q).length = (L.filter p).length →
      ∀ x ∈ L, p x = true → q x = true
  | [], _, _, _, hx, _ => nomatch hx
  | a :: xs, himp, hlen, x, hx, hpx => by
    have hrest_le := filter_length_le_of_imp xs (fun y hy => himp y (List.mem_cons_of_mem _ hy))
    simp only [List.filter_cons] at hlen
    rcases List.mem_cons.mp hx with rfl | hxs
    · cases hqa : q x
      · simp [hqa, hpx] at hlen; omega
      · rfl
    · cases hqa : q a
      · cases hpa : p a
        · simp [hqa, hpa] at hlen
          exact filter_sub_length_eq_imp_forall xs
            (fun y hy => himp y (List.mem_cons_of_mem _ hy)) hlen x hxs hpx
        · simp [hqa, hpa] at hlen; omega
      · have hpa : p a = true := himp a List.mem_cons_self hqa
        simp [hqa, hpa] at hlen
        exact filter_sub_length_eq_imp_forall xs
          (fun y hy => himp y (List.mem_cons_of_mem _ hy)) hlen x hxs hpx

/-- Pointwise flip of one element in a `Nodup` list increments `(L.filter p).length` by `1`. -/
theorem filter_length_flip_one {α : Type _} {p p' : α → Bool} {x0 : α} :
    ∀ (L : List α), L.Nodup → x0 ∈ L → p x0 = false → p' x0 = true →
      (∀ y ∈ L, y ≠ x0 → p' y = p y) →
      (L.filter p').length = (L.filter p).length + 1
  | [], _, hmem, _, _, _ => nomatch hmem
  | a :: xs, hnd, hmem, hp0, hp'0, hoth => by
    have ⟨hna, hnd_xs⟩ := List.nodup_cons.mp hnd
    simp only [List.filter_cons]
    rcases List.mem_cons.mp hmem with rfl | hxs
    · have hxs_eq : xs.filter p' = xs.filter p :=
        List.filter_congr fun y hy => hoth y (List.mem_cons_of_mem _ hy) (fun he => hna (he ▸ hy))
      simp [hp0, hp'0, hxs_eq]
    · have hne : a ≠ x0 := fun he => hna (he ▸ hxs)
      have ha_eq : p' a = p a := hoth a List.mem_cons_self hne
      have ih := filter_length_flip_one xs hnd_xs hxs hp0 hp'0
        (fun y hy => hoth y (List.mem_cons_of_mem _ hy))
      rw [ha_eq]; cases p a <;> simp [ih]

/-- Count of elements `< n` with `m ≠ i` in `List.range n` is `n - 1` when `i < n`. -/
theorem filter_range_ne_length {n i : Nat} (hi : i < n) :
    ((List.range n).filter (fun m => decide (m ≠ i))).length = n - 1 := by
  have h1 : ((List.range n).filter (fun _ => true)).length =
      ((List.range n).filter (fun m => decide (m ≠ i))).length + 1 :=
    filter_length_flip_one (x0 := i) (List.range n) List.nodup_range (List.mem_range.mpr hi)
      (by simp) rfl (fun y _ hne => by simp [hne])
  have htr : ∀ k, ((List.range k).filter (fun _ => true)).length = k := fun k => by
    induction k with
    | zero => rfl
    | succ m ih => rw [List.range_succ, List.filter_append]; simp [ih]
  have := htr n; omega

/-- Wide-AND gate emission soundness (`Step12BGateAt maxA`, supporting both `arity ≤ 64` with
`tag = 0` and `65 ≤ arity ≤ maxA ≤ 1,000,000` with `tag = 3`). -/
theorem step12B_andGate_of_emitted {maxA : Nat} (hmax : maxA ≤ step12BCongAndArityMax)
    {F_cur : List (List Nat)} {cur_vars usz i g_len : Nat}
    {base scr : List (BitVec 32)} (hu3 : 3 ≤ usz) (humax : usz - 1 ≤ maxA) (hucv : usz ≤ cur_vars)
    (hi : i < usz)
    (hlt : ∀ k < usz, (base[k]?.getD 0#32).toNat < 2 * cur_vars)
    (hcl : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((List.range usz).map fun k => (base[k]?.getD 0#32).toNat)))
    (hbins : ∀ k < usz, k ≠ i →
      (cnfOfClauses F_cur).EntailsClause (cnfClause
        [litNeg (base[i]?.getD 0#32).toNat, litNeg (base[k]?.getD 0#32).toNat]))
    (hbd_g : g_len + 2 + (usz - 1) ≤ scr.length)
    (h0 : scr[g_len]? = some (base[i]?.getD 0#32))
    (h1 : scr[g_len + 1]? = some (if usz - 1 ≤ 64 then BitVec.ofNat 32 (usz - 1)
      else (3#32 <<< 28) ||| BitVec.ofNat 32 (usz - 1)))
    (hrhs : ∀ k < usz, k ≠ i →
      scr[g_len + 2 + (if k < i then k else k - 1)]? = some ((base[k]?.getD 0#32) ^^^ 1#32)) :
    Step12BGateAt maxA F_cur cur_vars scr (g_len + 2 + (usz - 1)) g_len := by
  unfold step12BCongAndArityMax at hmax
  let mword : BitVec 32 :=
    if usz - 1 ≤ 64 then BitVec.ofNat 32 (usz - 1)
    else (3#32 <<< 28) ||| BitVec.ofNat 32 (usz - 1)
  have hm_props :
      step12BGateArity mword = usz - 1 ∧
      (((mword >>> 28).toNat = 0 ∧ 2 ≤ usz - 1 ∧ usz - 1 ≤ 64) ∨
       ((mword >>> 28).toNat = 3 ∧ 65 ≤ usz - 1)) := by
    by_cases hle64 : usz - 1 ≤ 64
    · have hm : mword = BitVec.ofNat 32 (usz - 1) := by dsimp only [mword]; simp [hle64]
      have htag0 : (mword >>> 28).toNat = 0 := by
        rw [hm, BitVec.toNat_ushiftRight, bv32_ofNat_toNat (by omega), Nat.shiftRight_eq_div_pow]
        exact Nat.div_eq_of_lt (by omega)
      have hne3 : (mword >>> 28) ≠ 3#32 := fun h => by
        have := congrArg BitVec.toNat h; rw [htag0] at this; simp at this
      have har : step12BGateArity mword = usz - 1 := by
        rw [step12BGateArity_of_ne3 hne3, hm, BitVec.toNat_and, bv32_ofNat_toNat (by omega),
          show (0xFF#32 : BitVec 32).toNat = 255 from rfl]
        simpa [Nat.mod_eq_of_lt (show usz - 1 < 256 by omega)] using
          Nat.and_two_pow_sub_one_eq_mod (usz - 1) 8
      exact ⟨har, Or.inl ⟨htag0, by omega, hle64⟩⟩
    · have hm : mword = (3#32 <<< 28) ||| BitVec.ofNat 32 (usz - 1) := by
        dsimp only [mword]; simp [hle64]
      have hlt28 : usz - 1 < 2 ^ 28 := by omega
      have htag3_bv : (mword >>> 28) = 3#32 := by
        rw [hm]; apply BitVec.eq_of_getLsbD_eq; intro k hk
        simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
        by_cases hk4 : k < 4
        · have h28k : 28 + k < 32 := by omega
          have hu0 : (BitVec.ofNat 32 (usz - 1)).getLsbD (28 + k) = false := by
            rw [BitVec.getLsbD_ofNat]; simp only [h28k, decide_true, Bool.true_and]
            exact m6_testBit_false_of_lt (Nat.lt_of_lt_of_le hlt28
              (Nat.pow_le_pow_right (by decide) (by omega)))
          have hsub : 28 + k - 28 = k := by omega
          have hge28 : ¬(28 + k < 28) := by omega
          rw [hu0]; simp [h28k, hge28, hsub]
        · have h32 : ¬(28 + k < 32) := by omega
          have h30 : (3#32 : BitVec 32).getLsbD k = false := by
            rw [BitVec.getLsbD]
            exact m6_testBit_false_of_lt (Nat.lt_of_lt_of_le (by decide : 3 < 2 ^ 4)
              (Nat.pow_le_pow_right (by decide) (by omega)))
          have hu0 : (BitVec.ofNat 32 (usz - 1)).getLsbD (28 + k) = false := by
            rw [BitVec.getLsbD_ofNat]; simp [h32]
          rw [hu0]; simp [h32, h30]
      have har : step12BGateArity mword = usz - 1 := by
        rw [step12BGateArity_of_eq3 htag3_bv, hm]
        have hmask_bit : ∀ j : Fin 32,
            (0x0FFFFFFF#32 : BitVec 32).getLsbD j.val = decide (j.val < 28) := by decide
        have hmask : (((3#32 <<< 28) ||| BitVec.ofNat 32 (usz - 1)) &&& 0x0FFFFFFF#32) =
            BitVec.ofNat 32 (usz - 1) := by
          apply BitVec.eq_of_getLsbD_eq; intro k hk
          simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
          rw [hmask_bit ⟨k, hk⟩]
          by_cases hk28 : k < 28
          · simp [hk28]
          · have hu0 : (BitVec.ofNat 32 (usz - 1)).getLsbD k = false := by
              rw [BitVec.getLsbD_ofNat]; simp only [hk, decide_true, Bool.true_and]
              exact m6_testBit_false_of_lt (Nat.lt_of_lt_of_le hlt28
                (Nat.pow_le_pow_right (by decide) (by omega)))
            simp [hk28, hu0]
        rw [hmask, bv32_ofNat_toNat (by omega)]
      exact ⟨har, Or.inr ⟨by rw [htag3_bv]; rfl, by omega⟩⟩
  obtain ⟨hmword_ar, htag_disj⟩ := hm_props
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
    exact ⟨_, hget,
      by rw [FullCongHelpers.bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even (hlt k hk_lt),
      by rw [FullCongHelpers.bv32_xor1_eq_litNeg]; exact hbins k hk_lt hk_ne⟩
  refine ⟨base[i]?.getD 0#32, mword, h0, h1, hlt i hi, by omega, by omega, by omega,
    fun r hr => let ⟨v, hv, hltv, _⟩ := hrhs_at r (by omega); ⟨v, hv, hltv⟩,
    Or.inl ⟨by rw [hmword_ar]; exact htag_disj, ?_, ?_⟩⟩
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
      · have hlt_t : r < ((scr.drop (g_len + 2)).take (step12BGateArity mword)).length := by
          rw [List.length_take, List.length_drop, hmword_ar]; omega
        simpa [List.getElem_take, List.getElem_drop] using List.getElem_mem hlt_t
      · rw [hval_r, FullCongHelpers.bv32_xor1_eq_litNeg, litNeg_litNeg]
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx; obtain ⟨r, hr, hget⟩ := List.mem_iff_getElem.mp hv
    rw [List.length_take, List.length_drop, hmword_ar] at hr
    rw [List.getElem_take, List.getElem_drop] at hget
    obtain ⟨v', hv', _, hent⟩ := hrhs_at r (by omega)
    rw [List.getElem?_eq_getElem (by omega)] at hv'
    rwa [(Option.some.inj hv').symm.trans hget] at hent

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep12B
