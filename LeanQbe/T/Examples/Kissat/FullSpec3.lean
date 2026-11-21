module

public import LeanQbe.T.Examples.Kissat.FullSpec2
public import LeanQbe.T.Logic.C0Agrees
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Per-Function UNSAT-Only `Spec` Contracts (`Full2` tail, `Full3` & `Full`, 82 fns)

Defines exact UNSAT-only `Spec` contracts for the `14` decision/walk/rephase/restart/extend
functions of `full2_fns`, all `31` functions in `full3_fns`, and all `37` functions in `full4_fns`
prior to `kissat_solve_bytes` (`82` functions total; zero SAT/model-reconstruction proofs):
1. Decision, warmup, WalkSAT, rephase, restart, and extend helpers (`14` fns).
2. Binary/unit/watch helpers & lucky phases (`9` fns: `full_has_bin` .. `full_lucky`).
3. Failed-literal probing, HBR, transitive reduction, vivification (`14` fns).
4. Tarjan SCC equivalent-literal substitution & dense/sparse mode switching (`8` fns).
5. Congruence closure, kitten SAT sweeping, forward subsumption/strengthening, BVE/BCE, BVA
   factoring, and top-level inprocessing/CDCL orchestrators (`37` fns).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Auxiliary predicates & `Full2` decision / walk / rephase / restart / extend (`14` fns) -/

/-- Valid WalkSAT clause entry at `scratch_buf[2*idx .. 2*idx+1]` (`full_walk_collect`,
`full_walk_cl_sat`, `full_walk_pick_lit`). -/
def FullWalkEntryOk (s : FullState) (idx : Nat) : Prop :=
  let w0 := s.scratch.scratch_buf[2 * idx]?.getD 0#32
  if (w0 &&& 0x80000000#32) ≠ 0#32 then
    (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars ∧
    (s.scratch.scratch_buf[2 * idx + 1]?.getD 0#32).toNat < 2 * s.core.cur_vars
  else
    w0.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s w0.toNat = false

def FullWalkEntriesOk (s : FullState) (n : Nat) : Prop :=
  ∀ idx < n, FullWalkEntryOk s idx

/-- Semantic literal-equivalence representative invariant for Tarjan SCC / substitution /
congruence (`full_tarjan_scc`, `full_subst_*`, `full_cong_*`). -/
def FullReprEquiv (F_cur : List (List Nat)) (s : FullState) : Prop :=
  ∀ l < 2 * s.core.cur_vars,
    let r := (s.core.repr[l]?.getD 0#32).toNat
    r < 2 * s.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l, r ^^^ 1]) ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1, r])

/-- Union-find parent monotonicity (`repr[l] ≤ l`) on `0 ..< nlits` (`FullCongSpecs`). -/
def FullCongReprWf (nlits : Nat) (repr : List (BitVec 32)) : Prop :=
  nlits ≤ repr.length ∧ ∀ l < nlits, (repr[l]?.getD 0#32).toNat ≤ l

/-- Semantic union-find invariant: parent monotonicity plus `F_cur ⊨ (l ↔ repr[l])`. -/
def FullCongReprInv (F_cur : List (List Nat)) (nlits : Nat) (repr : List (BitVec 32)) : Prop :=
  FullCongReprWf nlits repr ∧
  ∀ l < nlits, LitEquiv (cnfOfClauses F_cur) l (repr[l]?.getD 0#32).toNat

/-- Opt-A alias for `fullAnalyzeSpec` (carries `FullOtfsInvW` + `cur_level ≤` on `20#64`). -/
abbrev fullAnalyze20Spec := fullAnalyzeSpec

def fullNextDecVarSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ (r, ()) s s' =>
      FullExtScratchPres s s' ∧
      (r = 0xFFFFFFFFFFFFFFFF#64 ∨
        (r.toNat < s.core.cur_vars ∧ s.core.vals[2 * r.toNat]?.getD 0#8 = 0#8)))

def fullDecideSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' m',
      let s' : FullState :=
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', cur_level := cl',
                                unassigned := unass', unflushed := unfl' }
          scratch := sc' }
      FullCoreInv c F0 s' → FullExtScratchPres s s' → (r = 0#64 ∨ r = 1#64) →
      (r = 0#64 → cl' = s.core.cur_level ∧ te' = s.core.trail_end) →
      (r = 1#64 → cl' = s.core.cur_level + 1 ∧ te' = s.core.trail_end + 1) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullWarmupSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCoreInv c F0 s ∧ s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' prob' unass' unfl' wvec' arena'
      wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m',
      let s' : FullState :=
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', propagated := prop',
                                probing := prob', unassigned := unass', unflushed := unfl',
                                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                wusable := wu', fuel := fuel', confl_type := ctype',
                                confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                oom := oom' }
          scratch := sc' }
      FullCoreInv c F0 s' → FullArenaPermEq s.core s'.core → fuel'.toNat ≤ s.core.fuel.toNat →
      FullExtScratchPres s s' → (s.core.probing = 0#64 → prob' = 0#64) →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullWalkCollectSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) s => h = c.hdr ∧ ∃ F0, FullCoreInv c F0 s)
    (fun c _ (r, ()) s s' =>
      FullExtScratchPres s s' ∧ r.toNat ≤ c.scratch_cap / 2 ∧ FullWalkEntriesOk s' r.toNat)

def fullWalkClSatSpec : Spec [i64, i64, i64] [.bool] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, scr, idx, ()) s =>
      h = c.hdr ∧ scr = c.pScratchBuf ∧ (∃ F0, FullCoreInv c F0 s) ∧
      idx.toNat < c.scratch_cap / 2 ∧ FullWalkEntryOk s idx.toNat)
    (fun _ _ _ s s' => s' = s)

def fullWalkPickLitSpec : Spec [i64, i64, i64] [i32] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, scr, idx, ()) s =>
      h = c.hdr ∧ scr = c.pScratchBuf ∧ (∃ F0, FullCoreInv c F0 s) ∧
      idx.toNat < c.scratch_cap / 2 ∧ FullWalkEntryOk s idx.toNat)
    (fun _ _ (r, ()) s s' =>
      FullExtScratchPres s s' ∧ s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
      (r = 0xFFFFFFFF#32 ∨ r.toNat < 2 * s.core.cur_vars))

def fullWalkSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ fuel' sc' m',
      let s' : FullState :=
        { s with core := { s.core with fuel := fuel' }, scratch := sc' }
      s'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat → FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullRephaseSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ vals' lvl' rsns' trl' tp' te' prop' unass' fuel' sc' m',
      let s' : FullState :=
        { core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                                trail_pos := tp', trail_end := te', propagated := prop',
                                cur_level := 0, unassigned := unass', fuel := fuel' }
          scratch := sc' }
      FullCoreInv c F0 s' → fuel'.toNat ≤ s.core.fuel.toNat → FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → Q () m'

abbrev fullSwitchModeSpec := fullSafetyVoidSpec

def fullRestartDueSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ (r, ()) s s' => (r = 0#64 ∨ r = 1#64) ∧ FullExtScratchPres s s')

def fullRestartSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m',
      let s' : FullState :=
        { core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                                trail_pos := tp', trail_end := te', propagated := prop',
                                cur_level := cl', unassigned := unass' }
          scratch := sc' }
      FullCoreInv c F0 s' → cl' ≤ s.core.cur_level → FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullExtendPush2Spec : Spec [i64, i32, i32] [.bool] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _blk, _ot, ()) s => h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap)
    (fun c _ _ s s' =>
      s'.scratch.last_learned = s.scratch.last_learned ∧ s'.scratch.extend_len ≤ c.extend_cap ∧
      s'.scratch.scratch_buf = s.scratch.scratch_buf)

def fullExtendPushClSpec : Spec [i64, i32, i32] [.bool] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _blk, _cref, ()) s => h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap)
    (fun c _ _ s s' =>
      s'.scratch.last_learned = s.scratch.last_learned ∧ s'.scratch.extend_len ≤ c.extend_cap ∧
      s'.scratch.scratch_buf = s.scratch.scratch_buf)

def fullExtendSpec : Spec [i64] [] :=
  SafetySlice.spec fullExtendSlice
    (fun c (h, ()) s => h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap)
    (fun _ _ _ _ _ => True)

/-- HBR binary pairs buffered in `work_stk2[0 ..< 2 * n)` during level-1 probing. -/
def FullHbrBufOkW (F_cur : List (List Nat)) (s : FullState) (n : Nat) : Prop :=
  n ≤ s.core.cur_vars ∧
  ∀ i < n,
    let a := (s.scratch.work_stk2[2 * i]?.getD 0#32).toNat
    let b := (s.scratch.work_stk2[2 * i + 1]?.getD 0#32).toNat
    a < 2 * s.core.cur_vars ∧ b < 2 * s.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [a, b])

/-- Partial representative soundness (`FullSccSpecs.PartialReprInv`). -/
def FullPartialReprInv (F_cur : List (List Nat)) (k : FullCoreState) : Prop :=
  ∀ l < 2 * k.cur_vars, let rv := k.repr[l]?.getD 0xFFFFFFFF#32
    rv ≠ 0xFFFFFFFF#32 → rv.toNat < 2 * k.cur_vars ∧ LitEquiv (cnfOfClauses F_cur) l rv.toNat

/-- Soundness of collected SCC units in `shrink_stk[0 ..< n)` (`FullSccSpecs.UnitsSoundInv`). -/
def FullUnitsSoundInv (F_cur : List (List Nat)) (s : FullState) (n : Nat) : Prop :=
  ∀ i < n, let u := (s.scratch.shrink_stk[i]?.getD 0#32).toNat
    u < 2 * s.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [u])

/-- Frame mask of `full_tarjan_pop_scc` (`FullSccSpecs.popSccMask`). -/
def fullPopSccMask (s : FullState) : FullState :=
  { s with
    core := { s.core with repr := [], tmp_cnt := 0, inconsistent := 0#64 }
    scratch := { s.scratch with tarjan_reach := [], shrink_stk := [], res_sz := 0#64 } }

/-- Valid extracted gate (AND `tag=0`, XOR `tag=1`, or ITE `tag=2`) in `scr` (`FullCongSpecs`). -/
def FullCongGateAt (F_cur : List (List Nat)) (cur_vars : Nat) (scr : List (BitVec 32))
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

/-- Contiguous sequence of valid gates in `scr[g ..< g_len)` (`FullCongSpecs.GateSeqOk`). -/
inductive FullCongGateSeqOk (F_cur : List (List Nat)) (cur_vars : Nat) (scr : List (BitVec 32))
    (g_len : Nat) : Nat → Prop where
  | done : FullCongGateSeqOk F_cur cur_vars scr g_len g_len
  | step {g : Nat} (hg : FullCongGateAt F_cur cur_vars scr g_len g) :
      FullCongGateSeqOk F_cur cur_vars scr g_len
        (g + 2 + ((scr[g + 1]?.getD 0#32) &&& 0xFF#32).toNat) →
      FullCongGateSeqOk F_cur cur_vars scr g_len g

/-- Global literal corresponding to local cone literal `ll < 2 * nv` via `work_stk1`. -/
def fullSweepGlobalLit (s : FullState) (ll : Nat) : Nat :=
  2 * (s.scratch.work_stk1[ll / 2]?.getD 0#32).toNat + (ll % 2)

/-- Bounded local kitten-sweep cone invariant (`nv ≤ 24`, `nv ≤ cur_vars`, `nc ≤ 64`,
`128 ≤ res_sz ≤ 1024`). -/
def FullSweepConeOk (F_cur : List (List Nat)) (s : FullState) (nv nc : Nat) : Prop :=
  nv ≤ 24 ∧ nv ≤ s.core.cur_vars ∧ nc ≤ 64 ∧
  128 ≤ s.scratch.res_sz.toNat ∧ s.scratch.res_sz.toNat ≤ 1024 ∧
  (∀ i < nv, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
  (∀ ci < nc,
    let off := (s.scratch.scratch_buf[ci]?.getD 0#32).toNat
    let sz := (s.scratch.scratch_buf[64 + ci]?.getD 0#32).toNat
    128 ≤ off ∧ off + sz ≤ s.scratch.res_sz.toNat ∧
    (∀ k < sz, (s.scratch.scratch_buf[off + k]?.getD 0#32).toNat < 2 * nv) ∧
    let glits := (List.range sz).map fun k =>
      fullSweepGlobalLit s (s.scratch.scratch_buf[off + k]?.getD 0#32).toNat
    (cnfOfClauses F_cur).EntailsClause (cnfClause glits))

/-- Semantic UNSAT postcondition of `full_sweep_dpll(h, nv, nc, a0, a1) = 20#64`. -/
def FullSweepDpllUnsat (F_cur : List (List Nat)) (s : FullState) (nv a0 a1 : Nat) : Prop :=
  let ass := (if a0 < 2 * nv then [fullSweepGlobalLit s a0 ^^^ 1] else []) ++
             (if a1 < 2 * nv then [fullSweepGlobalLit s a1 ^^^ 1] else [])
  (cnfOfClauses F_cur).EntailsClause (cnfClause ass)

/-- Valid collected occurrence entry in `full_bve_collect` for `lit`. -/
def FullBveEntryOkW (F_cur : List (List Nat)) (s : FullState) (lit : Nat) (w : BitVec 32) : Prop :=
  if (w &&& 0x80000000#32) ≠ 0#32 then
    let ot := (w &&& 0x7FFFFFFF#32).toNat
    ot < 2 * s.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, ot])
  else
    w.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s w.toNat = false

/-- Weak structural BVE occurrence entry preserved across `PH_GARB` marking & binary deletion. -/
def FullBveWeakItemOk (k : FullCoreState) (w : BitVec 32) : Prop :=
  if (w &&& 0x80000000#32) ≠ 0#32 then
    (w &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars
  else
    w.toNat ∈ fullArenaClauseRefsCore k

/-- Structural BCE clause/occurrence entry (`FullBveBvaSpecs.FullBveBceWeakOk`). -/
def FullBveBceWeakOk (c : FullCfg) (s : FullState) (w : BitVec 32) : Prop :=
  if (w &&& 0x80000000#32) ≠ 0#32 then
    (w &&& 0x7FFFFFFF#32).toNat < 2 * c.max_vars
  else
    w.toNat ∈ fullArenaClauseRefs s ∧
    w.toNat + 3 + fullArenaClauseSize s w.toNat ≤ s.core.arena_len ∧
    ∀ l ∈ fullArenaClauseLits s w.toNat, l < 2 * c.max_vars

/-- Serialized entailed resolvent buffer `[sz, l_0, ..., l_{sz-1}, ...]` in `scratch_buf`. -/
inductive FullResBufOkW (F_cur : List (List Nat)) (s : FullState) (r_end : Nat) : Nat → Prop where
  | nil : FullResBufOkW F_cur s r_end r_end
  | cons {p sz : Nat} :
      p + 1 + sz ≤ r_end →
      (s.scratch.scratch_buf[p]?.getD 0#32).toNat = sz →
      (∀ k < sz, (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      ((List.range sz).map fun k =>
        (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2).Nodup →
      (cnfOfClauses F_cur).EntailsClause (cnfClause ((List.range sz).map fun k =>
        (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat)) →
      FullResBufOkW F_cur s r_end (p + 1 + sz) →
      FullResBufOkW F_cur s r_end p

/-! ## 2. `Full3` binary/unit/watch helpers & lucky phases (`9` fns) -/

def fullHasBinSpec : Spec [i64, i32, i32] [.bool] := fun (h, a, b, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ ok : Bool,
      (ok = true → a.toNat < 2 * s.core.cur_vars ∧ b.toNat < 2 * s.core.cur_vars ∧
        a ≠ b ∧ a ≠ (b ^^^ 1#32) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat])) →
      Q (ok, ()) m

def fullAddBinSpec : Spec [i64, i32, i32] [i64] := fun (h, a, b, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ s.core.cur_level = 0 ∧
    (a.toNat < 2 * s.core.cur_vars → b.toNat < 2 * s.core.cur_vars →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat])) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb' oom' inc'
      phases' wsort' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                unassigned := unass', unflushed := unfl', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                                oom := oom', inconsistent := inc' }
          scratch := { s.scratch with phases := phases', wsort := wsort' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat ∧ inc' ≠ 0#64) →
      (r = 2#64 → oom' ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullDeleteBinSideSpec : Spec [i64, i32, i32] [] := fun (h, lit, _other, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧
    (lit.toNat < 2 * s.core.cur_vars →
      fullWatchOff s lit.toNat + fullWatchSize s lit.toNat ≤ s.core.wlen) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wu' m',
      let s' : FullState :=
        { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } }
      s'.LengthsOk c →
      (lit.toNat < 2 * s.core.cur_vars →
        fullWatchOff s' lit.toNat = fullWatchOff s lit.toNat ∧
        fullWatchSize s' lit.toNat ≤ fullWatchSize s lit.toNat) →
      (∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
        fullWatchOff s' l = fullWatchOff s l ∧ fullWatchSize s' l = fullWatchSize s l) →
      (∀ idx < c.wcap,
        (lit.toNat < 2 * s.core.cur_vars →
          idx < fullWatchOff s lit.toNat ∨
          fullWatchOff s lit.toNat + fullWatchSize s lit.toNat ≤ idx) →
        wstk'[idx]? = s.core.wstk[idx]?) →
      (∀ F_cur, WatchSliceOk F_cur s.core lit.toNat (fullWatchOff s lit.toNat)
          (fullWatchSize s lit.toNat) →
        WatchSliceOk F_cur s'.core lit.toNat (fullWatchOff s' lit.toNat)
          (fullWatchSize s' lit.toNat)) →
      (∀ F_cur, DenseWatchSliceOk F_cur s.core lit.toNat (fullWatchOff s lit.toNat)
          (fullWatchSize s lit.toNat) →
        DenseWatchSliceOk F_cur s'.core lit.toNat (fullWatchOff s' lit.toNat)
          (fullWatchSize s' lit.toNat)) →
      (WatchStackLayout s.core → WatchStackLayout s'.core) →
      (∀ F_cur, ModeWatchesInv F_cur s.core → ModeWatchesInv F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullDeleteBinarySpec : Spec [i64, i32, i32] [] := fun (h, _a, _b, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wu' nb' m',
      let s' : FullState :=
        { s with core := { s.core with wvec := wvec', wstk := wstk',
                                       wusable := wu', num_binary := nb' } }
      s'.LengthsOk c → WatchStackLayout s'.core →
      (∀ F_cur, ModeWatchesInv F_cur s.core → ModeWatchesInv F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullSetInactiveSpec : Spec [i64, i32, i32] [] := fun (h, v, _flag, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    if s.core.cur_vars ≤ v.toNat then
      Q () m
    else
      ∀ flags' unass' m',
        flags'.length = c.max_vars →
        let s' : FullState :=
          { s with core := { s.core with flags := flags', unassigned := unass' } }
        (FullMem c s' ⋆ R) m' → Q () m'

def fullAddUnitSpec : Spec [i64, i32] [.bool] := fun (h, lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    (lit.toNat < 2 * s.core.cur_vars → (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat])) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
      phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                propagated := prop', cur_level := cl', unassigned := unass',
                                unflushed := unfl', inconsistent := inc' }
          scratch := { s.scratch with phases := phases', target_assigned := ta',
                                      best_assigned := ba', phases_target := pt',
                                      phases_best := pb', heap := hp', pos := ps',
                                      heap_len := hl', q_search_idx := qsi',
                                      q_search_stamp := qss' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → cl' = 0 →
      (lit.toNat < 2 * s.core.cur_vars → ok = false → F0.Unsat ∧ inc' ≠ 0#64) →
      (ok = false → 2 * s.core.cur_vars ≤ lit.toNat ∨ (F0.Unsat ∧ inc' ≠ 0#64)) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullLuckyScanSpec : Spec [i64, .bool, .bool] [i64] := fun (h, _pos, _fwd, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullLuckyPolarSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r : BitVec 64, (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) → Q (r, ()) m

def fullLuckySpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.probing = 0#64 →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ## 3. `Full3` failed-literal probing, HBR, transitive reduction, vivification (`14` fns) -/

def fullHbrDomSpec : Spec [i64, i32, i32] [i32] := fun (h, cref, implied, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧
    (∃ wv ws wl, FullWitnessInv c F0 F_cur { s.core with wvec := wv, wstk := ws, wlen := wl }) ∧
    FullMrkZero c s ∧ s.core.cur_level = 1 ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s cref.toNat = false ∧ implied.toNat ∈ fullArenaClauseLits s cref.toNat ∧
    (∀ l ∈ fullArenaClauseLits s cref.toNat,
      l ≠ implied.toNat → s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ dom mrk' mclr' m',
      let s' : FullState := { s with core := { s.core with mrk := mrk', min_clr := mclr' } }
      s'.LengthsOk c → FullMrkZero c s' →
      (dom = 0xFFFFFFFF#32 ∨ (dom.toNat < 2 * s.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [dom.toNat ^^^ 1, implied.toNat]))) →
      (FullMem c s' ⋆ R) m' → Q (dom, ()) m'

def fullProbePropLitSpec : Spec [i64, i32] [.bool] := fun (h, _lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullMrkZero c s ∧
    FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64 ∧
    s.core.cur_level = 1 ∧ s.core.oom = 0#64 ∧ FullHbrBufOkW F_cur s s.core.tmp_cnt ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullMrkZero c s' →
      FullArenaVarsNodup s' → FullExtScratchOk c s' → s'.core.dense_mode = 0#64 →
      s'.core.cur_level = 1 → s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.core.lit_mark = s.core.lit_mark → s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s.core.trail_end ≤ s'.core.trail_end → FullHbrBufOkW F_cur s' s'.core.tmp_cnt →
      (ok = false → s'.core.oom ≠ 0#64 ∨ FullConflictOkW F_cur s') →
      (ok = true → s'.core.oom = 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullProbePropSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullMrkZero c s ∧
    FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64 ∧
    s.core.cur_level = 1 ∧ FullHbrBufOkW F_cur s s.core.tmp_cnt ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullMrkZero c s' →
      FullArenaVarsNodup s' → FullExtScratchOk c s' → s'.core.dense_mode = 0#64 →
      s'.core.cur_level = 1 → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.lit_mark = s.core.lit_mark → s'.scratch.work_stk1 = s.scratch.work_stk1 →
      FullHbrBufOkW F_cur s' s'.core.tmp_cnt →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 1#64 → FullConflictOkW F_cur s') →
      (r = 0#64 → s'.core.propagated = s'.core.trail_end) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullProbeFlushHbrSpec : Spec [i64, i64] [i64] := fun (h, hbr_n, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullMrkZero c s ∧
    FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64 ∧
    s.core.cur_level = 0 ∧ FullHbrBufOkW F_cur s hbr_n.toNat ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullMrkZero c s' →
      FullArenaVarsNodup s' → FullExtScratchOk c s' → s'.core.dense_mode = 0#64 →
      s'.core.cur_level = 0 → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.lit_mark = s.core.lit_mark → s'.scratch.work_stk1 = s.scratch.work_stk1 →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullProbeAssumePairSpec : Spec [i64, i32] [i64] := fun (h, lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ lit.toNat < 2 * s.core.cur_vars ∧
    s.core.vals[lit.toNat]?.getD 0#8 = 0#8 ∧ (FullMem c s ⋆ R) m ∧ ∀ r s' m',
      (r = 1#64 ∨ r = 2#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (r = 20#64 → F0.Unsat ∧ ∃ F_cur, FullOtfsInvW c F0 F_cur s') →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullProbeRunSpec : Spec [i64, i64] [i64] := fun (h, _budget, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 → s'.core.probing = 0#64 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullTransLitSpec : Spec [i64, i32] [.bool] := fun (h, src, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧
    src.toNat < 2 * s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullTransitiveSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 → s'.core.probing = 0#64 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullVivSimplifySpec : Spec [i64, i32] [i64] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧
    cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.probing = s.core.probing →
      s'.core.fuel = s.core.fuel → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 0#64 → cref.toNat ∈ fullArenaClauseRefs s' ∧ fullArenaClauseGarb s' cref.toNat = false) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullVivSortLitsSpec : Spec [i64, i64, i32] [] := fun (h, lits_ptr, sz, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ lits_ptr = c.pTmp ∧ s.LengthsOk c ∧ sz.toNat ≤ c.max_vars ∧
    (∀ i < sz.toNat, (s.core.tmp[i]?.getD 0#32).toNat < 2 * c.max_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tmp' m', tmp'.length = c.max_vars →
      (tmp'.take sz.toNat).Perm (s.core.tmp.take sz.toNat) →
      (∀ i, sz.toNat ≤ i → i < c.max_vars → tmp'[i]? = s.core.tmp[i]?) →
      (FullMem c { s with core := { s.core with tmp := tmp' } } ⋆ R) m' → Q () m'

def fullVivDeduceSpec : Spec [i64, i32, i32, i64] [i32] :=
  fun (h, cref, implied, out_ptr, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ out_ptr = c.pWorkStk2 ∧ FullSparseInvW c F0 F_cur s ∧
      cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
      (implied = 0xFFFFFFFF#32 →
        FullConflictOkW F_cur s ∨
        (s.core.confl_type = 0#64 ∧
          ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8)) ∧
      (implied ≠ 0xFFFFFFFF#32 →
        implied.toNat < 2 * s.core.cur_vars ∧ s.core.vals[implied.toNat]?.getD 0#8 = 1#8) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ olen mrk' ws1' ws2' rsz' m',
        let s' : FullState :=
          { s with
            core := { s.core with mrk := mrk' }
            scratch := { s.scratch with work_stk1 := ws1', work_stk2 := ws2', res_sz := rsz' } }
        FullSparseInvW c F0 F_cur s' → olen.toNat ≤ c.max_vars →
        (olen.toNat < fullArenaClauseSize s cref.toNat →
          (∀ i < olen.toNat, (ws2'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
          ((ws2'.take olen.toNat).map fun x => x.toNat / 2).Nodup ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause ((ws2'.take olen.toNat).map BitVec.toNat))) →
        (FullMem c s' ⋆ R) m' → Q (olen, ()) m'

def fullVivCommitSpec : Spec [i64, i32, i64, i32, .bool] [i64] :=
  fun (h, cref, out_ptr, olen, _used_red, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ out_ptr = c.pWorkStk2 ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧
      cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
      olen.toNat ≤ c.max_vars ∧
      (olen.toNat < fullArenaClauseSize s cref.toNat →
        (∀ i < olen.toNat, (s.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
        ((s.scratch.work_stk2.take olen.toNat).map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.work_stk2.take olen.toNat).map BitVec.toNat))) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 → s'.core.cur_vars = s.core.cur_vars →
        s'.core.arena_len = s.core.arena_len → s'.core.probing = s.core.probing →
        s'.core.fuel = s.core.fuel → fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullVivClauseSpec : Spec [i64, i32] [i64] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧
    cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.arena_len = s.core.arena_len →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullVivifySpec : Spec [i64, i64] [i64] := fun (h, _tier_mode, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 → s'.core.probing = 0#64 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ## 4. `Full3` Tarjan SCC substitution & dense/sparse mode transitions (`8` fns) -/

def fullTarjanPopSccSpec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, root_lit, lit, mark_root, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (k0 : Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ s.core.inconsistent = 0#64 ∧
      root_lit.toNat < 2 * s.core.cur_vars ∧ lit.toNat < 2 * s.core.cur_vars ∧
      s.core.tmp_cnt ≤ 2 * s.core.cur_vars ∧ s.scratch.res_sz.toNat ≤ c.max_vars ∧
      k0 < s.core.tmp_cnt ∧ s.scratch.work_stk1[k0]?.getD 0#32 = lit ∧
      (∀ j, k0 < j → j < s.core.tmp_cnt → s.scratch.work_stk1[j]?.getD 0#32 ≠ lit) ∧
      (∀ j < s.core.tmp_cnt, (s.scratch.work_stk1[j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (∀ j, k0 ≤ j → j < s.core.tmp_cnt →
        LitEquiv (cnfOfClauses F_cur) (s.scratch.work_stk1[j]?.getD 0#32).toNat lit.toNat) ∧
      FullPartialReprInv F_cur s.core ∧ FullUnitsSoundInv F_cur s s.scratch.res_sz.toNat ∧
      (mark_root ≠ 0xFFFFFFFF#32 →
        (∀ j, k0 ≤ j → j < s.core.tmp_cnt →
          BinReach (cnfOfClauses F_cur) root_lit.toNat (s.scratch.work_stk1[j]?.getD 0#32).toNat) ∧
        (∀ l < 2 * s.core.cur_vars,
          mark_root.toNat ≤ (s.scratch.tarjan_mark[l]?.getD 0#32).toNat →
          BinReach (cnfOfClauses F_cur) root_lit.toNat l)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (failed' : Bool) (s' : FullState) m',
        AgreesExcept fullPopSccMask s s' → s'.core.tmp_cnt = k0 →
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → s'.scratch.res_sz.toNat ≤ c.max_vars →
        FullPartialReprInv F_cur s'.core → FullUnitsSoundInv F_cur s' s'.scratch.res_sz.toNat →
        (s'.core.inconsistent = 0#64 ∨ s'.core.inconsistent = 1#64) →
        (s'.core.inconsistent ≠ 0#64 → (cnfOfClauses F_cur).Unsat) →
        (s'.core.inconsistent = 0#64 →
          (∀ j, k0 ≤ j → j < s.core.tmp_cnt →
            let x := (s.scratch.work_stk1[j]?.getD 0#32).toNat
            s'.core.repr[x]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
            s'.scratch.tarjan_reach[x]?.getD 0#32 = 0xFFFFFFFF#32) ∧
          (∀ l < 2 * s.core.cur_vars,
            (∀ j, k0 ≤ j → j < s.core.tmp_cnt → (s.scratch.work_stk1[j]?.getD 0#32).toNat ≠ l) →
            s'.core.repr[l]? = s.core.repr[l]? ∧
            s'.scratch.tarjan_reach[l]? = s.scratch.tarjan_reach[l]?)) →
        (FullMem c s' ⋆ R) m' → Q (failed', ()) m'

def fullTarjanSccSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r repr' tc' inc' tmk' trc' ws1' ws2' wsort' sstk' rsz' m',
      let s' : FullState :=
        { s with
          core := { s.core with repr := repr', tmp_cnt := tc', inconsistent := inc' }
          scratch := { s.scratch with tarjan_mark := tmk', tarjan_reach := trc',
                                      work_stk1 := ws1', work_stk2 := ws2', wsort := wsort',
                                      shrink_stk := sstk', res_sz := rsz' } }
      FullSparseInvW c F0 F_cur s' → r.toNat ≤ c.max_vars →
      (∀ k < r.toNat,
        (sstk'[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [(sstk'[k]?.getD 0#32).toNat])) →
      (inc' = 0#64 → FullReprEquiv F_cur s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullSubstElimVarsSpec : Spec [i64, i64] [.bool] := fun (h, ucnt, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧ FullReprEquiv F_cur s ∧
    ucnt.toNat ≤ c.max_vars ∧
    (∀ k < ucnt.toNat,
      (s.scratch.shrink_stk[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [(s.scratch.shrink_stk[k]?.getD 0#32).toNat])) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → FullReprEquiv F_cur s' →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullSubstRewriteBinsSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧ FullReprEquiv F_cur s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → FullReprEquiv F_cur s' → (ok = false → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullSubstRewriteArSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧ FullReprEquiv F_cur s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullSubstituteSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullEnterDenseSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      s'.core.cur_level = 0 → s'.core.fuel = s.core.fuel →
      (ok = true → FullDenseInv c F0 s') →
      (ok = false → FullSparseInv c F0 s') →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullRebuildWatchesSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ## 5. `Full` congruence closure (`10` fns) -/

def fullCongFindSpec : Spec [i64, i32] [i32] := fun (repr_ptr, l, ()) m Q _ =>
  ∃ (F_cur : List (List Nat)) (nlits : Nat) (repr : List (BitVec 32)) (R : Mem 64 → Prop),
    FullCongReprInv F_cur nlits repr ∧ l.toNat < nlits ∧
    (array (t := i32) repr_ptr repr ⋆ R) m ∧
    ∀ (r : BitVec 32) (repr' : List (BitVec 32)) (m' : Mem 64),
      repr'.length = repr.length → FullCongReprInv F_cur nlits repr' →
      r.toNat ≤ l.toNat → r.toNat < nlits → LitEquiv (cnfOfClauses F_cur) l.toNat r.toNat →
      (array (t := i32) repr_ptr repr' ⋆ R) m' → Q (r, ()) m'

def fullCongMergeSpec : Spec [i64, i32, i32] [.bool] := fun (h, a, b, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
    s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧
    FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
    a.toNat < 2 * s.core.cur_vars ∧ b.toNat < 2 * s.core.cur_vars ∧
    LitEquiv (cnfOfClauses F_cur) a.toNat b.toNat ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ch : Bool) (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_level = 0 → s'.core.dense_mode ≠ 0#64 →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.tmp = s.core.tmp → s'.scratch.scratch_buf = s.scratch.scratch_buf →
      FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      (FullMem c s' ⋆ R) m' → Q (ch, ()) m'

def fullHasTernarySpec : Spec [i64, i32, i32, i32] [.bool] := fun (h, a, b, cl, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧
    a.toNat < 2 * s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ ok : Bool,
      (ok = true → a ≠ b → a ≠ cl → b ≠ cl →
        (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat, cl.toNat])) →
      Q (ok, ()) m

def fullSortU32Spec : Spec [i64, i32] [] := fun (arr_ptr, n, ()) m Q _ =>
  ∃ (arr : List (BitVec 32)) (R : Mem 64 → Prop),
    n.toNat ≤ arr.length ∧ (array (t := i32) arr_ptr arr ⋆ R) m ∧
    ∀ (arr' : List (BitVec 32)) (m' : Mem 64),
      arr'.length = arr.length → List.Perm (arr'.take n.toNat) (arr.take n.toNat) →
      (∀ k, n.toNat ≤ k → arr'[k]? = arr[k]?) →
      (array (t := i32) arr_ptr arr' ⋆ R) m' → Q () m'

def fullCongExtractIteSpec : Spec [i64, i32, i32, i32, i64] [i64] :=
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
      FullCongGateSeqOk F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap → (ret = g_len ∨ ret = g_len + 5#64) →
        (∀ idx < g_len.toNat, scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        FullCongGateSeqOk F_cur s.core.cur_vars scr' ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

def fullCongEmitXorSpec : Spec [i64, i64, i32, i32, i32] [i64] :=
  fun (scr_ptr, g_len, x0, x1, x2, ()) m Q _ =>
    ∃ (F_cur : List (List Nat)) (cur_vars : Nat) (scr : List (BitVec 32)) (R : Mem 64 → Prop),
      x0.toNat < 2 * cur_vars ∧ x1.toNat < 2 * cur_vars ∧ x2.toNat < 2 * cur_vars ∧
      2 ≤ cur_vars ∧ g_len.toNat + 4 ≤ scr.length ∧ scr.length < 2 ^ 32 ∧
      XorGateDef (cnfOfClauses F_cur) (litNeg x0.toNat) x1.toNat x2.toNat ∧
      FullCongGateSeqOk F_cur cur_vars scr g_len.toNat 0 ∧
      (array (t := i32) scr_ptr scr ⋆ R) m ∧
      ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
        scr'.length = scr.length → (∀ idx < g_len.toNat, scr'[idx]? = scr[idx]?) →
        FullCongGateSeqOk F_cur cur_vars scr' (g_len.toNat + 4) 0 →
        (array (t := i32) scr_ptr scr' ⋆ R) m' → Q (g_len + 4#64, ()) m'

def fullCongTryXorIteSpec : Spec [i64, i32, i32, i32, i64, i64] [i64] :=
  fun (h, a, b, cl, g_len, g_cap, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧
      a.toNat < 2 * s.core.cur_vars ∧ b.toNat < 2 * s.core.cur_vars ∧
      cl.toNat < 2 * s.core.cur_vars ∧
      a.toNat / 2 ≠ b.toNat / 2 ∧ a.toNat / 2 ≠ cl.toNat / 2 ∧ b.toNat / 2 ≠ cl.toNat / 2 ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat, cl.toNat]) ∧
      g_len.toNat + 5 ≤ g_cap.toNat ∧ g_cap.toNat ≤ c.scratch_cap ∧
      FullCongGateSeqOk F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap → g_len.toNat ≤ ret.toNat → ret.toNat ≤ g_cap.toNat →
        (∀ idx < g_len.toNat, scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        FullCongGateSeqOk F_cur s.core.cur_vars scr' ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

def fullCongExtractSpec : Spec [i64, i64] [i64] := fun (h, g_cap, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧ g_cap.toNat ≤ c.scratch_cap ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap → ret.toNat ≤ g_cap.toNat →
      FullCongGateSeqOk F_cur s.core.cur_vars scr' ret.toNat 0 →
      (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

def fullCongHashStepSpec : Spec [i64, i64, i64, i64] [.bool] :=
  fun (h, g_len, ht_off, ht_sz, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
      s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      0 < ht_sz.toNat ∧ g_len.toNat ≤ ht_off.toNat ∧ ht_off.toNat + ht_sz.toNat ≤ c.scratch_cap ∧
      FullCongGateSeqOk F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ch : Bool) (s' : FullState) (m' : Mem 64),
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
        s'.core.cur_level = 0 → s'.core.dense_mode ≠ 0#64 →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
        FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
        (∀ idx < g_len.toNat, s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) →
        (FullMem c s' ⋆ R) m' → Q (ch, ()) m'

def fullCongruenceSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) →
      (r = 1#64 → FullSparseInv c F0 s') →
      (r = 20#64 → F0.Unsat ∧ s'.LengthsOk c) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ## 6. `Full` kitten SAT sweeping (`7` fns) -/

def fullSweepAddClSpec : Spec [i64, i64, i32, i32] [i64] :=
  fun (h, lits_ptr, sz, nc, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (xs : List (BitVec 32)) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ 1152 ≤ c.scratch_cap ∧
      128 ≤ s.scratch.res_sz.toNat ∧ s.scratch.res_sz.toNat ≤ 1024 ∧ sz.toNat ≤ xs.length ∧
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
        array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
        array (t := i32) lits_ptr xs ⋆ R) m ∧
      if 64 ≤ nc.toNat ∨ 1024 < s.scratch.res_sz.toNat + sz.toNat then
        Q (nc.setWidth 64, ()) m
      else
        ∀ scr' m',
          let lp := s.scratch.res_sz.toNat
          let s' : FullState :=
            { s with scratch :=
              { s.scratch with scratch_buf := scr', res_sz := BitVec.ofNat 64 (lp + sz.toNat) } }
          scr'.length = c.scratch_cap →
          (∀ i < c.scratch_cap, i ≠ nc.toNat → i ≠ 64 + nc.toNat →
            ¬ (lp ≤ i ∧ i < lp + sz.toNat) → scr'[i]? = s.scratch.scratch_buf[i]?) →
          scr'[nc.toNat]? = some (BitVec.ofNat 32 lp) → scr'[64 + nc.toNat]? = some sz →
          (∀ k < sz.toNat, scr'[lp + k]? = xs[k]?) →
          (array64 (c.hdr + 32) (hdrTailWords c s') ⋆
            array (t := i32) c.pScratchBuf scr' ⋆
            array (t := i32) lits_ptr xs ⋆ R) m' →
          Q (BitVec.ofNat 64 (nc.toNat + 1), ()) m'

def fullSweepConeSpec : Spec [i64, i32] [i64] := fun (h, root_v, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1152 ≤ c.scratch_cap ∧
    root_v.toNat < s.core.cur_vars ∧
    (∀ v < s.core.cur_vars, s.scratch.tarjan_mark[v]?.getD 0#32 = 0xFFFFFFFF#32) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r tmp' ws1' tmk' scr' rsz' m',
      let s' : FullState :=
        { s with
          core := { s.core with tmp := tmp' }
          scratch := { s.scratch with work_stk1 := ws1', tarjan_mark := tmk',
                                      scratch_buf := scr', res_sz := rsz' } }
      let nv := (r &&& 0xFFFF#64).toNat
      let nc := (r >>> 16).toNat
      FullDenseInvW c F0 F_cur s' → 1 ≤ nv → FullSweepConeOk F_cur s' nv nc →
      (ws1'[0]?.getD 0#32).toNat = root_v.toNat →
      (∀ v < s.core.cur_vars, tmk'[v]?.getD 0#32 ≠ 0xFFFFFFFF#32 →
        ∃ i < nv, (ws1'[i]?.getD 0#32).toNat = v) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullSweepDpllSpec : Spec [i64, i32, i32, i32, i32] [i64] :=
  fun (h, nv, nc, a0, a1, ()) m Q _ =>
    ∃ (c : FullCfg) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ 1152 ≤ c.scratch_cap ∧
      FullSweepConeOk F_cur s nv.toNat nc.toNat ∧ (FullMem c s ⋆ R) m ∧
      ∀ r fuel' scr' rng' m',
        let s' : FullState :=
          { s with
            core := { s.core with fuel := fuel' }
            scratch := { s.scratch with scratch_buf := scr', rng_state := rng' } }
        s'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat →
        (∀ i < 1024, scr'[i]? = s.scratch.scratch_buf[i]?) →
        FullSweepConeOk F_cur s' nv.toNat nc.toNat →
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → FullSweepDpllUnsat F_cur s nv.toNat a0.toNat a1.toNat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullSweepRefineSpec : Spec [i64, i32, i32] [] := fun (h, nv, _bit_idx, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ 1152 ≤ c.scratch_cap ∧ nv.toNat ≤ 24 ∧
    nv.toNat ≤ 2 * c.max_vars ∧
    (∀ i < nv.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ sig' m', sig'.length = c.max_vars →
      (FullMem c { s with scratch := { s.scratch with sim_sig := sig' } } ⋆ R) m' → Q () m'

def fullSweepSeedSimSpec : Spec [i64, i32, i32] [i32] := fun (h, nv, nc, ()) m Q _ =>
  ∃ (c : FullCfg) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ 1152 ≤ c.scratch_cap ∧ 1 ≤ nv.toNat ∧
    FullSweepConeOk F_cur s nv.toNat nc.toNat ∧ (FullMem c s ⋆ R) m ∧
    ∀ r fuel' scr' rng' sig' m',
      let s' : FullState :=
        { s with
          core := { s.core with fuel := fuel' }
          scratch := { s.scratch with scratch_buf := scr', rng_state := rng', sim_sig := sig' } }
      s'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat →
      (∀ i < 1024, scr'[i]? = s.scratch.scratch_buf[i]?) →
      FullSweepConeOk F_cur s' nv.toNat nc.toNat →
      (r = 0xFFFFFFFF#32 → (cnfOfClauses F_cur).Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullSweepVarSpec : Spec [i64, i32] [i64] := fun (h, root_v, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1152 ≤ c.scratch_cap ∧
    root_v.toNat < s.core.cur_vars ∧
    (∀ v < s.core.cur_vars, s.scratch.tarjan_mark[v]?.getD 0#32 = 0xFFFFFFFF#32) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ v < s'.core.cur_vars, s'.scratch.tarjan_mark[v]?.getD 0#32 = 0xFFFFFFFF#32) →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullSweepSatSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ## 7. `Full` forward subsumption/strengthening, BVE/BCE, BVA & top-level (`20` fns) -/

def fullFwdDedupBinsSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → (ok = false → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullFwdCheckClSpec : Spec [i64, i32] [.bool] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullForwardSubSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullBveCollectSpec : Spec [i64, i32, i64, i32] [i32] :=
  fun (h, lit, out_ptr, cap, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (out_off : Nat)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ lit.toNat < 2 * s.core.cur_vars ∧
      out_ptr = c.pScratchBuf + BitVec.ofNat 64 (4 * out_off) ∧
      out_off + cap.toNat ≤ c.scratch_cap ∧ (FullMem c s ⋆ R) m ∧
      ∀ r scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < out_off ∨ out_off + cap.toNat ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (r = 0xFFFFFFFF#32 ∨ (r.toNat ≤ cap.toNat ∧
          ∀ i < r.toNat, FullBveEntryOkW F_cur s' lit.toNat (scr'[out_off + i]?.getD 0#32))) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullBveMarkAndSpec : Spec [i64, i32, i32, i32, i32] [.bool] :=
  fun (h, v_lit, cr, n_off, nn, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 132 ≤ c.scratch_cap ∧
      cr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cr.toNat = false ∧
      n_off.toNat + nn.toNat ≤ c.scratch_cap ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (v_lit.toNat ^^^ 1)
        (s.scratch.scratch_buf[n_off.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' scr' m',
        let s' : FullState :=
          { s with
            core := { s.core with lit_mark := lm' }
            scratch := { s.scratch with scratch_buf := scr' } }
        FullDenseInvW c F0 F_cur s' →
        (∀ i < c.scratch_cap, i ≠ 130 → i ≠ 131 → scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullBveGatesSpec : Spec [i64, i32, i32, i32] [] := fun (h, v, np, nn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 132 ≤ c.scratch_cap ∧
    v.toNat < s.core.cur_vars ∧ np.toNat ≤ 64 ∧ nn.toNat ≤ 64 ∧
    (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
    (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[64 + j]?.getD 0#32)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ lm' scr' m',
      let s' : FullState :=
        { s with
          core := { s.core with lit_mark := lm' }
          scratch := { s.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' →
      (∀ i < c.scratch_cap, (i < 128 ∨ 132 ≤ i) → scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullBveResolvePairSpec : Spec [i64, i32, i32, i32] [.bool] := fun (h, v, pc, nc, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ v.toNat < s.core.cur_vars ∧
    FullBveEntryOkW F_cur s (2 * v.toNat) pc ∧ FullBveEntryOkW F_cur s (2 * v.toNat + 1) nc ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) lm' tmp' tl' m',
      let s' : FullState :=
        { s with core := { s.core with lit_mark := lm', tmp := tmp', tmp_len := tl' } }
      FullDenseInvW c F0 F_cur s' → tl' ≤ s.core.cur_vars →
      (ok = true →
        (∀ k < tl', (tmp'[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
        ((tmp'.take tl').map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat))) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullBveWeakenSpec : Spec [i64, i32, i32, i32] [.bool] := fun (h, blk_lit, off, cnt, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ blk_lit.toNat < 2 * s.core.cur_vars ∧
    off.toNat + cnt.toNat ≤ c.scratch_cap ∧
    (∀ i < cnt.toNat,
      FullBveWeakItemOk s.core (s.scratch.scratch_buf[off.toNat + i]?.getD 0#32)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.scratch.scratch_buf = s.scratch.scratch_buf →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullBveTryBceSpec : Spec [i64, i32, i32, i32, i32] [.bool] :=
  fun (h, blk_lit, cr, opp_off, opp_n, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ blk_lit.toNat < 2 * s.core.cur_vars ∧
      FullBveBceWeakOk c s cr ∧
      ((cr &&& 0x80000000#32) = 0#32 → ((fullArenaClauseLits s cr.toNat).map (· / 2)).Nodup) ∧
      opp_off.toNat + opp_n.toNat ≤ c.scratch_cap ∧
      (∀ j < opp_n.toNat,
        FullBveBceWeakOk c s (s.scratch.scratch_buf[opp_off.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (blk : Bool) lm' tmp' m',
        let s' : FullState := { s with core := { s.core with lit_mark := lm', tmp := tmp' } }
        FullDenseInvW c F0 F_cur s' → (FullMem c s' ⋆ R) m' → Q (blk, ()) m'

def fullBveCommitResSpec : Spec [i64, i64, i64] [i64] := fun (h, r_off, r_end, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ r_off.toNat ≤ r_end.toNat ∧
    r_end.toNat ≤ c.scratch_cap ∧ FullResBufOkW F_cur s r_end.toNat r_off.toNat ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullBveExtNeedSpec : Spec [i64, i32, i32] [i64] := fun (h, off, cnt, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ off.toNat + cnt.toNat ≤ c.scratch_cap ∧
    (∀ i < cnt.toNat,
      let w := s.scratch.scratch_buf[off.toNat + i]?.getD 0#32
      (w &&& 0x80000000#32) ≠ 0#32 ∨ w.toNat + 2 < c.arena_cap) ∧
    (FullMem c s ⋆ R) m ∧ ∀ r : BitVec 64, Q (r, ()) m

def fullBveVarSpec : Spec [i64, i32] [i64] := fun (h, v, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ v.toNat < s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullInitFreshVarSpec : Spec [i64, i32] [] := fun (h, fv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ fv.toNat < s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ vals' mrk' flags' lvl' rsns' wvec' unass' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', mrk := mrk', flags := flags', lvl := lvl',
                                rsns := rsns', wvec := wvec', unassigned := unass' }
          scratch := sc' }
      s'.LengthsOk c → FullExtScratchPres s s' → sc'.scratch_buf = s.scratch.scratch_buf →
      vals'[2 * fv.toNat]?.getD 1#8 = 0#8 → vals'[2 * fv.toNat + 1]?.getD 1#8 = 0#8 →
      (∀ l < 2 * c.max_vars, l / 2 ≠ fv.toNat → vals'[l]? = s.core.vals[l]?) →
      mrk'[fv.toNat]?.getD 1#8 = 0#8 →
      (∀ v < c.max_vars, v ≠ fv.toNat → mrk'[v]? = s.core.mrk[v]?) →
      lvl'[fv.toNat]?.getD 1#32 = 0#32 →
      (∀ v < c.max_vars, v ≠ fv.toNat → lvl'[v]? = s.core.lvl[v]?) →
      rsns'[fv.toNat]?.getD 0#32 = 0xFFFFFFFF#32 →
      (∀ v < c.max_vars, v ≠ fv.toNat → rsns'[v]? = s.core.rsns[v]?) →
      (∀ k < 4, wvec'[4 * fv.toNat + k]?.getD 1#32 = 0#32) →
      (∀ i < 4 * c.max_vars, i / 4 ≠ fv.toNat → wvec'[i]? = s.core.wvec[i]?) →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullBvaTryLitSpec : Spec [i64, i32] [.bool] := fun (h, f0, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ f0.toNat < 2 * s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars → s'.core.fuel = s.core.fuel →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullFactorSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars → s'.core.fuel = s.core.fuel →
      r = 1#64 → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullProbeSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullEliminateSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullPreprocessSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullSimplifySpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullSearchSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

end LeanQbe.T.Examples.Kissat.Full
