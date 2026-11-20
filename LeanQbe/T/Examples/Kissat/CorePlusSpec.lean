module

public import LeanQbe.T.Examples.Kissat.CorePlusSpec1
public import LeanQbe.T.Logic.C0Step
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Core+` Per-Function `Spec` Contracts & Specification Table (`Stage 2`)

Builds on `CorePlusSpec1` to define concise `{ s with ... }` record-update `Spec` definitions
for all 28 C0 functions in `coreplus_fns`, unit-witness `corePlusSolveBytesCoreSpec`, and the
`Env.ofTable`-backed specification table `corePlusSpecTable` (`mkCorePlusEnv`, `corePlusEnv`),
ready for Wave 1b proofs (`Env.ofTable_moduleOk`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.CorePlus

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Per-function `Spec` definitions for all 28 functions in `coreplus_fns` -/

/-! ### Group A: EVSIDS Heap, Bump/Decay, and Reluctant Restart Heuristics (8 functions) -/

/-- Shared heuristic-only contract for `(h, v) -> ()` helpers modifying only `s.heur`. -/
def corePlusHeurVarVoidSpec : Spec [i64, i32] [] := fun (h, _v, ()) m Q _ =>
  ∃ (c : CorePlusCfg) (s : CorePlusState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (CorePlusMem c s ⋆ R) m ∧
    ∀ heur' m', heur'.LengthsOk c → (CorePlusMem c { s with heur := heur' } ⋆ R) m' → Q () m'

/-- Shared heuristic-only contract for `(h) -> ()` helpers modifying only `s.heur`. -/
def corePlusHeurVoidSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : CorePlusCfg) (s : CorePlusState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (CorePlusMem c s ⋆ R) m ∧
    ∀ heur' m', heur'.LengthsOk c → (CorePlusMem c { s with heur := heur' } ⋆ R) m' → Q () m'

abbrev corePlusHeapSiftUpSpec := corePlusHeurVarVoidSpec
abbrev corePlusHeapPushSpec := corePlusHeurVarVoidSpec
abbrev corePlusRescaleScoresSpec := corePlusHeurVoidSpec
abbrev corePlusBumpVarSpec := corePlusHeurVarVoidSpec
abbrev corePlusBumpDecaySpec := corePlusHeurVoidSpec
abbrev corePlusTickReluctantSpec := corePlusHeurVoidSpec

def corePlusHeapSiftDownSpec : Spec [i64, i32] [] := fun (h, _v, ()) m Q _ =>
  ∃ (c : CorePlusCfg) (s : CorePlusState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (CorePlusMem c s ⋆ R) m ∧
    ∀ heur' m', heur'.LengthsOk c → heur'.heap_len = s.heur.heap_len →
      heur'.rel_trigger = s.heur.rel_trigger →
      (CorePlusMem c { s with heur := heur' } ⋆ R) m' → Q () m'

def corePlusHeapPopMaxSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : CorePlusCfg) (s : CorePlusState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (CorePlusMem c s ⋆ R) m ∧
    ∀ r heur' m',
      (r = 0xFFFFFFFF#64 ∨ r.toNat < c.mv) →
      heur'.LengthsOk c →
      (0 < s.heur.heap_len ∧ s.heur.heap_len ≤ c.mv → heur'.heap_len = s.heur.heap_len - 1) →
      heur'.rel_trigger = s.heur.rel_trigger →
      (CorePlusMem c { s with heur := heur' } ⋆ R) m' →
      Q (r, ()) m'

/-! ### Group B: Arena Helpers (`assign`, `add_watch`, `add_clause`, `backtrack`, `zero_tables`) -/

def corePlusAssignSpec : Spec [i64, i32, i32] [] := fun (h, lit, rsn, ()) m Q _ =>
  ∃ (c : CorePlusCfg) (s : CorePlusState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (CorePlusMem c s ⋆ R) m ∧
    if c.mv ≤ lit.toNat / 2 ∨ c.mv ≤ s.trail_end then
      Q () m
    else
      let v := lit.toNat / 2
      ∀ phases' m', phases'.length = c.mv →
        let s' : CorePlusState :=
          { s with
            vals := (s.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            lvl := s.lvl.set v (BitVec.ofNat 32 s.cur_level)
            rsns := s.rsns.set v rsn
            trl := s.trl.set s.trail_end lit
            trail_end := s.trail_end + 1
            heur := { s.heur with phases := phases' } }
        s'.LengthsOk c → (CorePlusMem c s' ⋆ R) m' → Q () m'

def corePlusAddWatchSpec : Spec [i64, i32, i32] [] := fun (h, _w, _lit, ()) m Q _ =>
  ∃ (c : CorePlusCfg) (s : CorePlusState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (CorePlusMem c s ⋆ R) m ∧
    ∀ wh' wn' m', wh'.length = 2 * c.mv → wn'.length = 2 * c.max_c →
      (CorePlusMem c { s with wh := wh', wn := wn' } ⋆ R) m' → Q () m'

def corePlusAddClauseSpec : Spec [i64, i32] [i64] := fun (h, len, ()) m Q _ =>
  ∃ (c : CorePlusCfg) (s : CorePlusState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ len.toNat ≤ c.mv ∧ (CorePlusMem c s ⋆ R) m ∧
    if c.max_c ≤ s.num_clauses ∨ c.lcap - s.lit_len < len.toNat then
      Q (0xFFFFFFFF#64, ()) m
    else
      ∀ lpool' cls' wh' wn' m',
        let s' := addClauseState s len.toNat lpool' cls' wh' wn'
        s'.LengthsOk c →
        (∀ cid < s.num_clauses, clauseOff s' cid = clauseOff s cid ∧
          clauseSize s' cid = clauseSize s cid) →
        (∀ k < s.lit_len, lpool'[k]? = s.lpool[k]?) →
        clauseOff s' s.num_clauses = s.lit_len →
        clauseSize s' s.num_clauses = len.toNat →
        clauseLits s' s.num_clauses = (s.tmp.take len.toNat).map BitVec.toNat →
        (CorePlusMem c s' ⋆ R) m' →
        Q (BitVec.ofNat 64 s.num_clauses, ()) m'

def corePlusBacktrackSpec : Spec [i64, i64] [] := fun (h, target_lvl, ()) m Q _ =>
  ∃ (c : CorePlusCfg) (F0 : CNF Nat) (s : CorePlusState) (R : Mem 64 → Prop),
    h = c.hdr ∧ CorePlusInv c F0 s ∧ target_lvl.toNat ≤ s.cur_level ∧ (CorePlusMem c s ⋆ R) m ∧
    ∀ vals' lvl' rsns' te' prop' heur' m',
      let s' : CorePlusState :=
        { s with
          vals := vals', lvl := lvl', rsns := rsns', trail_end := te',
          propagated := prop', cur_level := target_lvl.toNat, heur := heur' }
      CorePlusInv c F0 s' → te' ≤ s.trail_end →
      (∀ i < s.trail_end,
        (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat →
        i < te') →
      (CorePlusMem c s' ⋆ R) m' → Q () m'

def corePlusZeroTablesSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : CorePlusCfg) (s : CorePlusState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (CorePlusMem c s ⋆ R) m ∧
    ∀ mstk' heur' m', mstk'.length = 2 * c.minDepth → heur'.LengthsOk c →
      heur'.rel_trigger = s.heur.rel_trigger →
      let s' : CorePlusState :=
        { s with
          vals := List.replicate (2 * c.mv) 0#8
          wh := List.replicate (2 * c.mv) 0xFFFFFFFF#32
          mrk := List.replicate c.mv 0#8
          lvl := List.replicate c.mv 0#32
          rsns := List.replicate c.mv 0xFFFFFFFF#32
          tmp := List.replicate c.mv 0#32
          min_stk := mstk'
          min_clr := List.replicate c.mv 0#32
          heur := heur' }
      (CorePlusMem c s' ⋆ R) m' → Q () m'

/-! ### Group C: Initialization, Syntax Skipping, Clause Ingestion, and Body Parsing -/

def corePlusInitStateSpec : Spec [i64, i64, i64, i64, i64] [.bool] :=
  fun (cnf_ptr, cend, hdr_addr, avail, fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (R : Mem 64 → Prop),
      cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      hdr_addr.toNat + avail.toNat < 2 ^ 64 ∧
      360 ≤ avail.toNat ∧
      (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail.toNat ⋆ R) m ∧
      (∀ m', (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail.toNat ⋆ R) m' →
        (∀ mv nc rest, parseHeader cnfBytes = some (mv, nc, rest) →
          avail.toNat < cpFixedBytes mv + nc * 24) →
        Q (false, ()) m') ∧
      (∀ (c : CorePlusCfg) (s : CorePlusState) (j : Nat) (rest : List UInt8) (m' : Mem 64),
        c.hdr = hdr_addr → c.avail = avail.toNat →
        parseHeader cnfBytes = some (c.mv, c.nc, rest) →
        j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        CorePlusInv c (shiftDownCnf CNF.empty) s →
        s.d_cur = cnf_ptr + BitVec.ofNat 64 j →
        s.lit_len = 0 → s.num_clauses = 0 → s.trail_end = 0 → s.propagated = 0 →
        s.cur_level = 0 → s.fuel = fuel → s.min_clr_len = 0 → s.min_clr_full = 0#64 →
        s.vals = List.replicate (2 * c.mv) 0#8 →
        s.wh = List.replicate (2 * c.mv) 0xFFFFFFFF#32 →
        s.heur.rel_trigger = 0#64 →
        (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s ⋆ R) m' →
        Q (true, ()) m')

def corePlusSkipClauseSyntaxSpec : Spec [i64, i64] [.bool] := fun (cend, d, ()) m Q _ =>
  ∃ (cnf_ptr nc val0 : BitVec 64) (mv : Nat) (cnfBytes : List UInt8) (i0 : Nat)
    (R : Mem 64 → Prop),
    cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    mv < 2 ^ 64 ∧ i0 ≤ cnfBytes.length ∧
    (bytes cnf_ptr cnfBytes ⋆
      dimacsState d (BitVec.ofNat 64 mv) nc (cnf_ptr + BitVec.ofNat 64 i0) val0 ⋆ R) m ∧
    match parseClause mv (cnfBytes.drop i0) with
    | none =>
      ∀ cur' val' m',
        (bytes cnf_ptr cnfBytes ⋆ dimacsState d (BitVec.ofNat 64 mv) nc cur' val' ⋆ R) m' →
        Q (false, ()) m'
    | some (cl, rest) =>
      ∀ j m', (∀ lit ∈ cl.literals, 1 ≤ lit.1) → i0 < j → j ≤ cnfBytes.length →
        cnfBytes.drop j = rest →
        (bytes cnf_ptr cnfBytes ⋆
          dimacsState d (BitVec.ofNat 64 mv) nc (cnf_ptr + BitVec.ofNat 64 j) 0#64 ⋆ R) m' →
        Q (true, ()) m'

def corePlusIngestClauseSpec : Spec [i64, i64] [i64] := fun (h, cend, ()) m Q _ =>
  ∃ (c : CorePlusCfg) (accCnf : CNF Nat) (s : CorePlusState) (cnf_ptr : BitVec 64)
    (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ i0 ≤ cnfBytes.length ∧
    s.d_cur = cnf_ptr + BitVec.ofNat 64 i0 ∧ s.cur_level = 0 ∧
    CorePlusInv c (shiftDownCnf accCnf) s ∧
    (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s ⋆ R) m ∧
    match parseClause c.mv (cnfBytes.drop i0) with
    | none =>
      ∀ s' m', s'.LengthsOk c → s'.fuel = s.fuel →
        s'.heur.rel_trigger = s.heur.rel_trigger →
        (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s' ⋆ R) m' → Q (0#64, ()) m'
    | some (cl, rest) =>
      ∀ r s' j m',
        (∀ lit ∈ cl.literals, 1 ≤ lit.1) →
        i0 < j → j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        s'.LengthsOk c → s'.d_cur = cnf_ptr + BitVec.ofNat 64 j →
        s'.cur_level = 0 → s'.fuel = s.fuel → s'.heur.rel_trigger = s.heur.rel_trigger →
        (r = 1#64 ∨ r = 2#64 ∨ r = 3#64) →
        (r = 1#64 → CorePlusInv c (shiftDownCnf (accCnf.add cl)) s') →
        (r = 2#64 → (shiftDownCnf (accCnf.add cl)).Unsat) →
        (∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
          s.vals[l]?.getD 0#8 = 0#8 →
          r = 1#64 ∧ s'.vals = (s.vals.set l 1#8).set (l ^^^ 1) 0xFF#8 ∧
          s'.trail_end = s.trail_end + 1 ∧ s'.propagated = s.propagated ∧
          s'.num_clauses = s.num_clauses ∧ s'.wh = s.wh) →
        (∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
          s.vals[l]?.getD 0#8 = 0xFF#8 → r = 2#64) →
        (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s' ⋆ R) m' → Q (r, ()) m'

def corePlusParseBodySpec : Spec [i64, i64] [i64] := fun (h, cend, ()) m Q _ =>
  ∃ (c : CorePlusCfg) (s : CorePlusState) (cnf_ptr : BitVec 64) (cnfBytes : List UInt8)
    (i0 : Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ i0 ≤ cnfBytes.length ∧
    parseHeader cnfBytes = some (c.mv, c.nc, cnfBytes.drop i0) ∧
    s.d_cur = cnf_ptr + BitVec.ofNat 64 i0 ∧
    s.cur_level = 0 ∧ s.trail_end = 0 ∧ s.propagated = 0 ∧ s.num_clauses = 0 ∧
    CorePlusInv c (shiftDownCnf CNF.empty) s ∧
    (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → s'.fuel = s.fuel →
      s'.heur.rel_trigger = s.heur.rel_trigger →
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
      (r = 1#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        CorePlusInv c (shiftDownCnf cnf) s' ∧ s'.cur_level = 0) →
      (∀ vals' te', UnitSatTrace c.mv s.vals 0 (cnfBytes.drop i0) c.nc vals' te' →
        r = 1#64 ∧ s'.vals = vals' ∧ s'.trail_end = te' ∧ s'.propagated = 0 ∧
        s'.num_clauses = 0 ∧ s'.wh = s.wh) →
      (UnitUnsatTrace c.mv s.vals (cnfBytes.drop i0) c.nc → r = 20#64) →
      (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ### Group D: Two-Watched-Literal BCP (`find_repl`, `propagate_lit`, `propagate`) -/

def corePlusFindReplSpec : Spec [i64, i64, i32, i32, i64] [i32] :=
  fun (vals_ptr, lits_ptr, sz, srch, n_lits, ()) m Q _ =>
    ∃ (vals : List (BitVec 8)) (lits : List (BitVec 32)) (R : Mem 64 → Prop),
      vals.length = n_lits.toNat ∧ lits.length = sz.toNat ∧
      2 ≤ srch.toNat ∧ srch.toNat ≤ sz.toNat ∧
      (array (t := i8) vals_ptr vals ⋆ array (t := i32) lits_ptr lits ⋆ R) m ∧
      ∀ r : BitVec 32,
        ((r = 0xFFFFFFFF#32 ∧
          ∀ k, 2 ≤ k → k < sz.toNat →
            let cand := (lits[k]?.getD 0#32).toNat
            n_lits.toNat ≤ cand ∨ ((vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = true) ∨
         (2 ≤ r.toNat ∧ r.toNat < sz.toNat ∧
          let cand := (lits[r.toNat]?.getD 0#32).toNat
          cand < n_lits.toNat ∧ ((vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = false)) →
        Q (r, ()) m

def corePlusPropagateLitSpec : Spec [i64, i32] [i64] := fun (h, lit, ()) m Q _ =>
  ∃ (c : CorePlusCfg) (F0 : CNF Nat) (s : CorePlusState) (R : Mem 64 → Prop),
    h = c.hdr ∧ CorePlusInv c F0 s ∧ (CorePlusMem c s ⋆ R) m ∧
    ∀ r vals' lvl' rsns' trl' te' wh' wn' cls' lpool' heur' m',
      let s' : CorePlusState :=
        { s with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_end := te',
          wh := wh', wn := wn', cls := cls', lpool := lpool', heur := heur' }
      CorePlusInv c F0 s' → s.trail_end ≤ te' → heur'.rel_trigger = s.heur.rel_trigger →
      (r = 0xFFFFFFFF#64 ∨
        (r.toNat < s'.num_clauses ∧ ∀ l ∈ clauseLits s' r.toNat, s'.vals[l]?.getD 0#8 = 0xFF#8)) →
      (s.wh[(lit ^^^ 1#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 →
        r = 0xFFFFFFFF#64 ∧ s' = s) →
      (CorePlusMem c s' ⋆ R) m' → Q (r, ()) m'

def corePlusPropagateSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : CorePlusCfg) (F0 : CNF Nat) (s : CorePlusState) (R : Mem 64 → Prop),
    h = c.hdr ∧ CorePlusInv c F0 s ∧ (CorePlusMem c s ⋆ R) m ∧
    ∀ r vals' lvl' rsns' trl' te' prop' wh' wn' cls' lpool' fuel' confl' heur' m',
      let s' : CorePlusState :=
        { s with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_end := te',
          propagated := prop', wh := wh', wn := wn', cls := cls', lpool := lpool',
          fuel := fuel', confl_cid := confl', heur := heur' }
      CorePlusInv c F0 s' → fuel'.toNat ≤ s.fuel.toNat →
      heur'.rel_trigger = s.heur.rel_trigger →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te') →
      (r = 1#64 →
        fuel'.toNat < s.fuel.toNat ∧
        confl'.toNat < s'.num_clauses ∧
        ∀ l ∈ clauseLits s' confl'.toNat, s'.vals[l]?.getD 0#8 = 0xFF#8) →
      ((∀ l < 2 * c.mv, s.wh[l]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) →
        s.trail_end - s.propagated ≤ s.fuel.toNat →
        r = 0#64 ∧ vals' = s.vals ∧ te' = s.trail_end ∧
        fuel'.toNat = s.fuel.toNat - (s.trail_end - s.propagated)) →
      (CorePlusMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ### Group E: Conflict Analysis, Iterative Minimization, Decide, and Solve Loop -/

def corePlusAnalyzeClauseSpec : Spec [i64, i32, i32] [.bool] :=
  fun (h, cid, skip_var, ()) m Q _ =>
    ∃ (c : CorePlusCfg) (s : CorePlusState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ s.tmp_len ≤ c.mv ∧ s.tmp_cnt + c.mv < 2 ^ 64 ∧
      (CorePlusMem c s ⋆ R) m ∧
      ∀ (ok : Bool) mrk' tmp' tc' tl' m',
        let s' : CorePlusState :=
          { s with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl' }
        s'.LengthsOk c → s.tmp_len ≤ tl' → tl' ≤ c.mv → s.tmp_cnt ≤ tc' →
        (∀ v < c.mv, s.mrk[v]?.getD 0#8 ≠ 0#8 → mrk'[v]?.getD 0#8 = s.mrk[v]?.getD 0#8) →
        (∀ k < s.tmp_len, tmp'[k]? = s.tmp[k]?) →
        (∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
          ∃ l ∈ clauseLits s cid.toNat,
            l / 2 = v ∧ v ≠ skip_var.toNat ∧
            0 < (s.lvl[v]?.getD 0#32).toNat ∧ (s.lvl[v]?.getD 0#32).toNat ≤ s.cur_level) →
        (∀ j, s.tmp_len ≤ j → j < tl' →
          let l := (tmp'[j]?.getD 0#32).toNat
          l ∈ clauseLits s cid.toNat ∧ l < 2 * c.mv ∧ l / 2 ≠ skip_var.toNat ∧
          0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧ (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level ∧
          mrk'[l / 2]?.getD 0#8 ≠ 0#8) →
        tc' - s.tmp_cnt =
          ((List.range c.mv).filter fun v =>
            decide (s.mrk[v]?.getD 0#8 = 0#8) &&
            decide (mrk'[v]?.getD 0#8 ≠ 0#8) &&
            decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)).length →
        (ok = true →
          cid.toNat < s.num_clauses ∧
          clauseOff s cid.toNat + clauseSize s cid.toNat ≤ s.lit_len ∧
          ∀ l ∈ clauseLits s cid.toNat,
            l / 2 < c.mv ∧
            (l / 2 ≠ skip_var.toNat →
              (0 < (s.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
              (s.mrk[l / 2]?.getD 0#8 = 0#8 →
                (s.lvl[l / 2]?.getD 0#32).toNat ≤ s.cur_level ∧
                (0 < (s.lvl[l / 2]?.getD 0#32).toNat →
                  (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level →
                  ∃ j, s.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) →
        (CorePlusMem c s' ⋆ R) m' → Q (ok, ()) m'

def corePlusClearMarksSpec : Spec [i64, i64] [] := fun (h, trail_from, ()) m Q _ =>
  ∃ (c : CorePlusCfg) (s : CorePlusState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.tmp_len ≤ c.mv ∧ (CorePlusMem c s ⋆ R) m ∧
    ∀ mrk' m', mrk'.length = c.mv →
      (∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 = 0#8) →
      (∀ i, 1 ≤ i → i < s.tmp_len → (s.tmp[i]?.getD 0#32).toNat / 2 < c.mv →
        mrk'[(s.tmp[i]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) →
      (∀ j, trail_from.toNat ≤ j → j < s.trail_end → (s.trl[j]?.getD 0#32).toNat / 2 < c.mv →
        mrk'[(s.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) →
      (CorePlusMem c { s with mrk := mrk' } ⋆ R) m' → Q () m'

def corePlusMinMarkSpec : Spec [i64, i32, i8] [] := fun (h, v, tag, ()) m Q _ =>
  ∃ (c : CorePlusCfg) (s : CorePlusState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (CorePlusMem c s ⋆ R) m ∧
    if c.mv ≤ v.toNat ∨ s.mrk[v.toNat]?.getD 0#8 ≠ 0#8 then
      Q () m
    else
      let mrk' := s.mrk.set v.toNat tag
      if s.min_clr_len < c.mv then
        ∀ m', (CorePlusMem c { s with
          mrk := mrk', min_clr := s.min_clr.set s.min_clr_len v,
          min_clr_len := s.min_clr_len + 1 } ⋆ R) m' → Q () m'
      else
        ∀ m', (CorePlusMem c { s with mrk := mrk', min_clr_full := 1#64 } ⋆ R) m' → Q () m'

def corePlusMinimizeLitSpec : Spec [i64, i32] [.bool] := fun (h, root_lit, ()) m Q _ =>
  ∃ (c : CorePlusCfg) (F0 : CNF Nat) (s : CorePlusState) (keepSet : List Nat)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ CorePlusCoreInv c F0 s ∧ MinMarkInv c s keepSet ∧
    root_lit.toNat < 2 * c.mv ∧ s.vals[root_lit.toNat]?.getD 0#8 = 0xFF#8 ∧
    s.mrk[root_lit.toNat / 2]?.getD 0#8 = 2#8 ∧
    (CorePlusMem c s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' mstk' mclr' mcl' mcf' m',
      let s' : CorePlusState :=
        { s with mrk := mrk', min_stk := mstk', min_clr := mclr',
                 min_clr_len := mcl', min_clr_full := mcf' }
      s'.LengthsOk c →
      (∀ v < c.mv, s.mrk[v]?.getD 0#8 = 2#8 → mrk'[v]?.getD 0#8 = 2#8) →
      MinMarkInv c s' keepSet →
      (ok = true → ∀ keep' : List Nat,
        (∀ l ∈ keepSet, l = root_lit.toNat ∨ l ∈ keep') → MinMarkInv c s' keep') →
      (CorePlusMem c s' ⋆ R) m' → Q (ok, ()) m'

def corePlusMinimizeClauseSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : CorePlusCfg) (F0 : CNF Nat) (s : CorePlusState) (R : Mem 64 → Prop),
    h = c.hdr ∧ CorePlusInv c F0 s ∧ 1 ≤ s.tmp_len ∧ s.tmp_len ≤ c.mv ∧
    F0.EntailsClause (cnfClause ((s.tmp.take s.tmp_len).map BitVec.toNat)) ∧
    (∀ k < s.tmp_len, let l := (s.tmp[k]?.getD 0#32).toNat
      l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8) ∧
    (CorePlusMem c s ⋆ R) m ∧
    ∀ tmp' tl' mrk' mstk' mclr' mcl' mcf' heur' m',
      let s' : CorePlusState := { s with
        tmp := tmp', tmp_len := tl', mrk := mrk', min_stk := mstk', min_clr := mclr',
        min_clr_len := mcl', min_clr_full := mcf', heur := heur' }
      CorePlusInv c F0 s' → 1 ≤ tl' → tl' ≤ s.tmp_len → tmp'[0]? = s.tmp[0]? →
      (∀ j, 1 ≤ j → j < tl' → ∃ i, 1 ≤ i ∧ i < s.tmp_len ∧ tmp'[j]? = s.tmp[i]?) →
      F0.EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat)) →
      (CorePlusMem c s' ⋆ R) m' → Q () m'

def corePlusAnalyzeSpec : Spec [i64, i64] [i64] := fun (h, confl_cid, ()) m Q _ =>
  ∃ (c : CorePlusCfg) (F0 : CNF Nat) (s : CorePlusState) (R : Mem 64 → Prop),
    h = c.hdr ∧ CorePlusInv c F0 s ∧ confl_cid.toNat < s.num_clauses ∧
    (∀ l ∈ clauseLits s confl_cid.toNat, s.vals[l]?.getD 0#8 = 0xFF#8) ∧
    (CorePlusMem c s ⋆ R) m ∧
    ∀ r vals' lvl' rsns' trl' te' prop' cl' tc' tl' mrk' tmp' wh' cls' wn' lpool'
      ll' nc' mstk' mclr' mcl' mcf' heur' m',
      let s' : CorePlusState := { s with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_end := te',
        propagated := prop', cur_level := cl', tmp_cnt := tc', tmp_len := tl',
        mrk := mrk', tmp := tmp', wh := wh', cls := cls', wn := wn', lpool := lpool',
        lit_len := ll', num_clauses := nc', min_stk := mstk', min_clr := mclr',
        min_clr_len := mcl', min_clr_full := mcf', heur := heur' }
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → CorePlusInv c F0 s') →
      (CorePlusMem c s' ⋆ R) m' → Q (r, ()) m'

def corePlusDecideSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : CorePlusCfg) (F0 : CNF Nat) (s : CorePlusState) (R : Mem 64 → Prop),
    h = c.hdr ∧ CorePlusInv c F0 s ∧ (CorePlusMem c s ⋆ R) m ∧
    ∀ r vals' lvl' rsns' trl' te' cl' heur' m',
      let s' : CorePlusState := { s with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl',
        trail_end := te', cur_level := cl', heur := heur' }
      CorePlusInv c F0 s' → (r = 0#64 ∨ r = 1#64) →
      heur'.rel_trigger = s.heur.rel_trigger →
      (r = 0#64 → vals' = s.vals ∧ lvl' = s.lvl ∧ rsns' = s.rsns ∧ trl' = s.trl ∧
        te' = s.trail_end ∧ cl' = s.cur_level ∧
        ∀ v < c.mv, s.vals[2 * v]?.getD 0#8 ≠ 0#8) →
      ((∀ v < c.mv, s.vals[2 * v]?.getD 0#8 ≠ 0#8) →
        r = 0#64 ∧ vals' = s.vals ∧ lvl' = s.lvl ∧ rsns' = s.rsns ∧ trl' = s.trl ∧
        te' = s.trail_end ∧ cl' = s.cur_level) →
      (CorePlusMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Core `kissat_solve_bytes` contract carrying both general soundness (`0 | 10 | 20`)
and deterministic unit-clause witness traces for non-vacuity. -/
def corePlusSolveBytesCoreSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) →
        (∀ mv nc i0,
          0 < fuel.toNat →
          cpFixedBytes mv + nc * 24 + 8 ≤ wlen →
          i0 ≤ cnfBytes.length →
          parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
          r = 20#64) →
        (∀ mv nc i0 vals' te',
          te' < fuel.toNat →
          cpFixedBytes mv + nc * 24 + 8 ≤ wlen →
          i0 ≤ cnfBytes.length →
          parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitSatTrace mv (List.replicate (2 * mv) 0#8) 0 (cnfBytes.drop i0) nc vals' te' →
          (∀ v < mv, vals'[2 * v]?.getD 0#8 ≠ 0#8) →
          runKissatCheckModel cnfBytes (vals'.map UInt8.ofBitVec) mv = true →
          r = 10#64) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
        Q (r, ()) m'

/-- Headline soundness specification of `kissat_solve_bytes`. -/
def corePlusSolveBytesSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, _fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m', (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' → Q (r, ()) m'

theorem corePlusSolveBytesCoreSpec_of_spec
    {args : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : corePlusSolveBytesSpec args m Q X) : corePlusSolveBytesCoreSpec args m Q X := by
  obtain ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm, hQ⟩ := h
  exact ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm,
    fun r m' hdom hu hs _ _ hm' => hQ r m' hdom hu hs hm'⟩

/-! ## 2. Unified `Env.ofTable` specification table for all 36 functions in `coreplusFns` -/

/-- Specification table matching `coreplusFns` (`dimacs_fns ++ coreplus_fns`) row-by-row. -/
def corePlusSpecTable (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : List SpecEntry :=
  [ ⟨"kissat_is_ws", [i64], [.bool], kissatIsWsSpec, true⟩
  , ⟨"kissat_is_digit", [i64], [.bool], kissatIsDigitSpec, true⟩
  , ⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, true⟩
  , ⟨"kissat_skip_ws1", [i64, i64], [.bool], kissatSkipWs1Spec, true⟩
  , ⟨"kissat_read_nat", [i64, i64], [.bool], kissatReadNatSpec, true⟩
  , ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩
  , ⟨"kissat_next_lit", [i64, i64], [i64], kissatNextLitSpec, true⟩
  , ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩
  , ⟨"kissat_heap_sift_up", [i64, i32], [], corePlusHeapSiftUpSpec, true⟩
  , ⟨"kissat_heap_sift_down", [i64, i32], [], corePlusHeapSiftDownSpec, true⟩
  , ⟨"kissat_heap_push", [i64, i32], [], corePlusHeapPushSpec, true⟩
  , ⟨"kissat_heap_pop_max", [i64], [i64], corePlusHeapPopMaxSpec, true⟩
  , ⟨"kissat_rescale_scores", [i64], [], corePlusRescaleScoresSpec, true⟩
  , ⟨"kissat_bump_var", [i64, i32], [], corePlusBumpVarSpec, true⟩
  , ⟨"kissat_bump_decay", [i64], [], corePlusBumpDecaySpec, true⟩
  , ⟨"kissat_tick_reluctant", [i64], [], corePlusTickReluctantSpec, true⟩
  , ⟨"kissat_assign", [i64, i32, i32], [], corePlusAssignSpec, true⟩
  , ⟨"kissat_add_watch", [i64, i32, i32], [], corePlusAddWatchSpec, true⟩
  , ⟨"kissat_add_clause", [i64, i32], [i64], corePlusAddClauseSpec, true⟩
  , ⟨"kissat_backtrack", [i64, i64], [], corePlusBacktrackSpec, true⟩
  , ⟨"kissat_zero_tables", [i64], [], corePlusZeroTablesSpec, true⟩
  , ⟨"kissat_init_state", [i64, i64, i64, i64, i64], [.bool], corePlusInitStateSpec, true⟩
  , ⟨"kissat_skip_clause_syntax", [i64, i64], [.bool], corePlusSkipClauseSyntaxSpec, true⟩
  , ⟨"kissat_ingest_clause", [i64, i64], [i64], corePlusIngestClauseSpec, true⟩
  , ⟨"kissat_parse_body", [i64, i64], [i64], corePlusParseBodySpec, true⟩
  , ⟨"kissat_find_repl", [i64, i64, i32, i32, i64], [i32], corePlusFindReplSpec, true⟩
  , ⟨"kissat_propagate_lit", [i64, i32], [i64], corePlusPropagateLitSpec, true⟩
  , ⟨"kissat_propagate", [i64], [i64], corePlusPropagateSpec, true⟩
  , ⟨"kissat_analyze_clause", [i64, i32, i32], [.bool], corePlusAnalyzeClauseSpec, true⟩
  , ⟨"kissat_clear_marks", [i64, i64], [], corePlusClearMarksSpec, true⟩
  , ⟨"kissat_min_mark", [i64, i32, i8], [], corePlusMinMarkSpec, true⟩
  , ⟨"kissat_minimize_lit", [i64, i32], [.bool], corePlusMinimizeLitSpec, true⟩
  , ⟨"kissat_minimize_clause", [i64], [], corePlusMinimizeClauseSpec, true⟩
  , ⟨"kissat_analyze", [i64, i64], [i64], corePlusAnalyzeSpec, true⟩
  , ⟨"kissat_decide", [i64], [i64], corePlusDecideSpec, true⟩
  , ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], mainSpec, true⟩
  ]

/-- Parameterized specification environment covering all 36 functions in `coreplusFns`. -/
def mkCorePlusEnv (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : Env :=
  Env.ofTable (corePlusSpecTable mainSpec)

/-- Headline 36-function specification environment for `coreplusModule`. -/
def corePlusEnv : Env := mkCorePlusEnv corePlusSolveBytesSpec

theorem corePlusSpecTable_noExit (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ e ∈ corePlusSpecTable mainSpec, e.noExit = true := by
  intro e he
  simp only [corePlusSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    exact congrArg SpecEntry.noExit h

theorem corePlusSpecTable_sigs (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (corePlusSpecTable mainSpec).map (fun e => (e.name, e.as, e.rs)) =
      coreplusFns.map (fun f => (f.name, f.as, f.rs)) := rfl

end LeanQbe.T.Examples.Kissat.CorePlus
