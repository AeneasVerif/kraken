module

public import LeanQbe.T.Examples.Kissat.PlainSpec2
public import LeanQbe.T.Examples.Kissat.SolverIngestLemmas1
public import LeanQbe.T.Logic.C0Step
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Plain` Per-Function `Spec` Contracts & Specification Table (`Stage 3`)

Builds on `PlainSpec1`/`PlainSpec2` to define `{ s with ... }` record-update `Spec` definitions
for all 51 C0 functions in `plain1_fns ++ plain2_fns`, unit-witness `UnitSatTrace`/`UnitUnsatTrace`,
`plainInitStateSpec` (including the `false`-branch capacity guard), `plainSolveBytesCoreSpec`,
and the 59-row `Env.ofTable` table `plainSpecTable` (`mkPlainEnv`, `plainEnv`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Arithmetic, arena, watch-stack, and heuristic helpers (`Plain1`) -/

def plainIsqrtSpec : Spec [i64] [i64] := fun (x, ()) m Q _ =>
  ∀ r : BitVec 64,
    r.toNat * r.toNat ≤ x.toNat →
    (x.toNat ≤ 1 → r = x) →
    (2 ≤ x.toNat → 1 ≤ r.toNat ∧ x.toNat < (r.toNat + 1) * (r.toNat + 1)) →
    Q (r, ()) m

def plainIlog10Spec : Spec [i64] [i64] := fun (_x, ()) m Q _ =>
  ∀ r : BitVec 64, 1 ≤ r.toNat → r.toNat ≤ 19 → Q (r, ()) m

def plainArenaNextSpec : Spec [i64, i32] [i32] := fun (h, cref, ()) m Q _ =>
  ∃ (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (PlainMem c s ⋆ R) m ∧
    Q (BitVec.ofNat 32 (arenaNextOff s.arena s.arena_len cref.toNat), ()) m

def plainAllocClSpec : Spec [i64, i32, i32, .bool] [i64] := fun (h, sz, _glue, red, ()) m Q _ =>
  ∃ (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (PlainMem c s ⋆ R) m ∧
    if c.arena_cap - s.arena_len < 3 + sz.toNat then
      Q (0xFFFFFFFF#64, ()) m
    else
      ∀ arena' m',
        let alen' := s.arena_len + 3 + sz.toNat
        let s' : PlainState := { s with arena_len := alen', arena := arena' }
        s'.LengthsOk c →
        (∀ k < s.arena_len, arena'[k]? = s.arena[k]?) →
        (arena'[s.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32 →
        (arena'[s.arena_len]?.getD 0#32 &&& 0x00080000#32) = 0#32 →
        ((arena'[s.arena_len]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ↔ red = true) →
        (arena'[s.arena_len + 2]?.getD 0#32).toNat = sz.toNat →
        (PlainMem c s' ⋆ R) m' →
        Q (BitVec.ofNat 64 s.arena_len, ()) m'

def plainWstackDefragSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout c s ∧ (PlainMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wlen' wsort' m',
      let s' : PlainState :=
        { s with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64,
                 heur := { s.heur with wsort := wsort' } }
      s'.LengthsOk c → WatchStackLayout c s' → (1 ≤ s.wlen → 1 ≤ wlen') →
      (∀ l < 2 * c.mv, watchSize s' l = watchSize s l ∧
        ∀ k < watchSize s l, s'.wstk[watchOff s' l + k]? = s.wstk[watchOff s l + k]?) →
      (PlainMem c s' ⋆ R) m' → Q () m'

def plainWatchPushSpec : Spec [i64, i32, i32, i32, i32] [.bool] :=
  fun (h, lit, w0, w1, cnt, ()) m Q _ =>
    ∃ (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout c s ∧
      (cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32) ∧
      (cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32) ∧
      (PlainMem c s ⋆ R) m ∧
      ∀ (ok : Bool) wvec' wstk' wlen' wusable' wsort' m',
        let s' : PlainState :=
          { s with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                   heur := { s.heur with wsort := wsort' } }
        s'.LengthsOk c → WatchStackLayout c s' →
        (∀ l < 2 * c.mv, l ≠ lit.toNat →
          watchSize s' l = watchSize s l ∧
          ∀ k < watchSize s l, s'.wstk[watchOff s' l + k]? = s.wstk[watchOff s l + k]?) →
        (ok = true →
          lit.toNat < 2 * c.mv ∧ (cnt.toNat = 1 ∨ cnt.toNat = 2) ∧
          watchSize s' lit.toNat = watchSize s lit.toNat + cnt.toNat ∧
          (∀ k < watchSize s lit.toNat,
            s'.wstk[watchOff s' lit.toNat + k]? = s.wstk[watchOff s lit.toNat + k]?) ∧
          s'.wstk[watchOff s' lit.toNat + watchSize s lit.toNat]? = some w0 ∧
          (cnt.toNat = 2 →
            s'.wstk[watchOff s' lit.toNat + watchSize s lit.toNat + 1]? = some w1)) →
        (ok = false →
          (lit.toNat < 2 * c.mv →
            watchSize s' lit.toNat = watchSize s lit.toNat ∧
            ∀ k < watchSize s lit.toNat,
              s'.wstk[watchOff s' lit.toNat + k]? = s.wstk[watchOff s lit.toNat + k]?) ∧
          (c.mv * 2 ≤ lit.toNat ∨ (cnt.toNat ≠ 1 ∧ cnt.toNat ≠ 2) ∨
            s' = s ∨ wusable' = 0#64)) →
        (PlainMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Shared heuristic-only contract for `(h, v) -> ()` helpers modifying only `s.heur`. -/
def plainHeurVarVoidSpec : Spec [i64, i32] [] := fun (h, _v, ()) m Q _ =>
  ∃ (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (PlainMem c s ⋆ R) m ∧
    ∀ heur' m', heur'.LengthsOk c → (PlainMem c { s with heur := heur' } ⋆ R) m' → Q () m'

/-- Shared heuristic-only `(h, v) -> ()` contract also preserving `rel_trigger`. -/
def plainHeurVarRelVoidSpec : Spec [i64, i32] [] := fun (h, _v, ()) m Q _ =>
  ∃ (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (PlainMem c s ⋆ R) m ∧
    ∀ heur' m', heur'.LengthsOk c → heur'.rel_trigger = s.heur.rel_trigger →
      (PlainMem c { s with heur := heur' } ⋆ R) m' → Q () m'

/-- Shared heuristic-only contract for `(h) -> ()` helpers modifying only `s.heur`. -/
def plainHeurVoidSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (PlainMem c s ⋆ R) m ∧
    ∀ heur' m', heur'.LengthsOk c → (PlainMem c { s with heur := heur' } ⋆ R) m' → Q () m'

abbrev plainHeapUpSpec := plainHeurVarRelVoidSpec
abbrev plainHeapPushSpec := plainHeurVarRelVoidSpec
abbrev plainRescaleSpec := plainHeurVoidSpec
abbrev plainBumpVarSpec := plainHeurVarVoidSpec
abbrev plainBumpDecaySpec := plainHeurVoidSpec
abbrev plainQueueMtfSpec := plainHeurVarVoidSpec
abbrev plainTickRelSpec := plainHeurVoidSpec
abbrev plainRecomputeTiersSpec := plainHeurVoidSpec
abbrev plainSwitchModeSpec := plainHeurVoidSpec

def plainHeapDownSpec : Spec [i64, i32] [] := fun (h, _v, ()) m Q _ =>
  ∃ (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (PlainMem c s ⋆ R) m ∧
    ∀ heur' m', heur'.LengthsOk c → heur'.heap_len = s.heur.heap_len →
      heur'.rel_trigger = s.heur.rel_trigger →
      (PlainMem c { s with heur := heur' } ⋆ R) m' → Q () m'

def plainHeapPopSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (PlainMem c s ⋆ R) m ∧
    ∀ r heur' m',
      (r = 0xFFFFFFFF#64 ∨ r.toNat < c.mv) →
      heur'.LengthsOk c →
      (0 < s.heur.heap_len ∧ s.heur.heap_len ≤ c.mv → heur'.heap_len = s.heur.heap_len - 1) →
      heur'.rel_trigger = s.heur.rel_trigger →
      (PlainMem c { s with heur := heur' } ⋆ R) m' →
      Q (r, ()) m'

def plainEmaUpdateSpec : Spec [i64, i64] [] := fun (h, _glue, ()) m Q _ =>
  ∃ (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (PlainMem c s ⋆ R) m ∧
    ∀ heur' m', heur'.LengthsOk c → heur'.rel_trigger = s.heur.rel_trigger →
      (PlainMem c { s with heur := heur' } ⋆ R) m' → Q () m'

/-! ## 2. Trail, clause allocation, initialization, and DIMACS ingestion (`Plain1`) -/

def plainAssignSpec : Spec [i64, i32, i32] [] := fun (h, lit, rsn, ()) m Q _ =>
  ∃ (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.cur_level < 2 ^ 32 ∧ (PlainMem c s ⋆ R) m ∧
    if c.mv ≤ lit.toNat / 2 ∨ c.mv ≤ s.trail_end then
      Q () m
    else
      let v := lit.toNat / 2
      let rsn' := if s.cur_level = 0 then 0xFFFFFFFF#32 else rsn
      let unfl' := if s.cur_level = 0 then s.unflushed + 1#64 else s.unflushed
      ∀ phases' m', phases'.length = c.mv →
        let s' : PlainState :=
          { s with
            vals := (s.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            lvl := s.lvl.set v (BitVec.ofNat 32 s.cur_level)
            rsns := s.rsns.set v rsn'
            trl := s.trl.set s.trail_end lit
            trail_pos := s.trail_pos.set v (BitVec.ofNat 32 s.trail_end)
            trail_end := s.trail_end + 1
            unflushed := unfl'
            heur := { s.heur with phases := phases' } }
        s'.LengthsOk c → (PlainMem c s' ⋆ R) m' → Q () m'

def plainBacktrackSpec : Spec [i64, i64] [] := fun (h, target_lvl, ()) m Q _ =>
  ∃ (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧
    (∀ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat < 2 * c.mv) ∧
    (PlainMem c s ⋆ R) m ∧
    ∀ vals' lvl' rsns' te' prop' heur' m',
      let s' : PlainState :=
        { s with
          vals := vals', lvl := lvl', rsns := rsns', trail_end := te',
          propagated := prop', cur_level := target_lvl.toNat, heur := heur' }
      s'.LengthsOk c → te' ≤ s.trail_end → prop' ≤ te' →
      heur'.rel_trigger = s.heur.rel_trigger →
      (∀ i < te', (s.trl[i]?.getD 0#32).toNat < 2 * c.mv) →
      (∀ F0, PlainCoreInv c F0 s → target_lvl.toNat ≤ s.cur_level →
        PlainCoreInv c F0 s' ∧
        ∀ i < s.trail_end,
          ((s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat ↔
            i < te')) →
      (PlainMem c s' ⋆ R) m' → Q () m'

def plainAddClauseSpec : Spec [i64, i32, i32, .bool] [i64] :=
  fun (h, len, _glue, _red, ()) m Q _ =>
    ∃ (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) (R : Mem 64 → Prop),
      h = c.hdr ∧ PlainCoreInv c F0 s ∧ len.toNat ≤ c.mv ∧
      (2 ≤ len.toNat →
        (∀ l ∈ (s.tmp.take len.toNat).map BitVec.toNat, l < 2 * c.mv) ∧
        F0.EntailsClause (cnfClause ((s.tmp.take len.toNat).map BitVec.toNat))) ∧
      (PlainMem c s ⋆ R) m ∧
      if len.toNat < 2 then
        Q (0xFFFFFFFF#64, ()) m
      else if len.toNat = 2 then
        ∀ r wvec' wstk' wlen' wusable' nb' wsort' m',
          let s' : PlainState :=
            { s with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                     num_binary := nb', heur := { s.heur with wsort := wsort' } }
          (r = 0xFFFFFFFF#64 ∨ r = 0xFFFFFFFE#64) →
          PlainCoreInv c F0 s' → (PlainMem c s' ⋆ R) m' → Q (r, ()) m'
      else
        ∀ r arena' alen' wvec' wstk' wlen' wusable' fred' ni' nr' wsort' m',
          (r = 0xFFFFFFFF#64 ∨ r = BitVec.ofNat 64 s.arena_len) →
          (r = 0xFFFFFFFF#64 →
            let s' : PlainState :=
              { s with arena := arena', arena_len := alen', wvec := wvec', wstk := wstk',
                       wlen := wlen', wusable := wusable', heur := { s.heur with wsort := wsort' } }
            PlainCoreInv c F0 s' ∧ (PlainMem c s' ⋆ R) m') →
          (r = BitVec.ofNat 64 s.arena_len →
            alen' = s.arena_len + 3 + len.toNat ∧
            let s' := addClauseState s len.toNat arena' wvec' wstk' wlen' wusable'
              fred' ni' nr' wsort'
            PlainCoreInv c F0 s' ∧ s.arena_len ∈ arenaClauseRefs s' ∧
            arenaClauseGarb s' s.arena_len = false ∧
            arenaClauseLits s' s.arena_len = (s.tmp.take len.toNat).map BitVec.toNat ∧
            (PlainMem c s' ⋆ R) m') →
          Q (r, ()) m'

def plainZeroTablesSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (PlainMem c s ⋆ R) m ∧
    ∀ wstk' mstk' heur' m',
      wstk'.length = c.wcap → mstk'.length = 2 * c.minDepth → heur'.LengthsOk c →
      heur'.rel_trigger = s.heur.rel_trigger →
      let s' : PlainState :=
        { s with
          vals := List.replicate (2 * c.mv) 0#8
          wvec := List.replicate (4 * c.mv) 0#32
          wstk := wstk'
          mrk := List.replicate c.mv 0#8
          lvl := List.replicate c.mv 0#32
          rsns := List.replicate c.mv 0xFFFFFFFF#32
          trl := s.trl
          trail_pos := List.replicate c.mv 0#32
          tmp := List.replicate c.mv 0#32
          min_stk := mstk'
          min_clr := List.replicate c.mv 0#32
          heur := heur' }
      (PlainMem c s' ⋆ R) m' → Q () m'

def plainInitStateSpec : Spec [i64, i64, i64, i64, i64] [.bool] :=
  fun (cnf_ptr, cend, hdr_addr, avail, fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (R : Mem 64 → Prop),
      cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      hdr_addr.toNat + avail.toNat < 2 ^ 64 ∧
      768 ≤ avail.toNat ∧
      (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail.toNat ⋆ R) m ∧
      (∀ m', (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail.toNat ⋆ R) m' →
        (∀ mv nc rest, parseHeader cnfBytes = some (mv, nc, rest) →
          avail.toNat < plainFixedBytes mv + nc * 40 + 136) →
        Q (false, ()) m') ∧
      (∀ (c : PlainCfg) (s : PlainState) (j : Nat) (rest : List UInt8) (m' : Mem 64),
        c.hdr = hdr_addr → c.avail = avail.toNat →
        parseHeader cnfBytes = some (c.mv, c.nc, rest) →
        j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        PlainInv c (shiftDownCnf CNF.empty) s →
        s.d_cur = cnf_ptr + BitVec.ofNat 64 j →
        s.arena_len = 0 → s.wlen = 1 → s.trail_end = 0 → s.propagated = 0 →
        s.cur_level = 0 → s.fuel = fuel → s.unflushed = 0#64 → s.probing = 0#64 →
        s.min_clr_len = 0 → s.min_clr_full = 0#64 → s.oom = 0#64 →
        s.vals = List.replicate (2 * c.mv) 0#8 →
        s.wvec = List.replicate (4 * c.mv) 0#32 →
        s.mrk = List.replicate c.mv 0#8 →
        s.heur.rel_trigger = 0#64 →
        (bytes cnf_ptr cnfBytes ⋆ PlainMem c s ⋆ R) m' →
        Q (true, ()) m')

def plainSkipClSpec : Spec [i64, i64] [.bool] := fun (cend, d, ()) m Q _ =>
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

def plainIngestClSpec : Spec [i64, i64] [i64] := fun (h, cend, ()) m Q _ =>
  ∃ (c : PlainCfg) (accCnf : CNF Nat) (s : PlainState) (cnf_ptr : BitVec 64)
    (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ i0 ≤ cnfBytes.length ∧
    s.d_cur = cnf_ptr + BitVec.ofNat 64 i0 ∧ s.cur_level = 0 ∧
    PlainInv c (shiftDownCnf accCnf) s ∧
    (bytes cnf_ptr cnfBytes ⋆ PlainMem c s ⋆ R) m ∧
    match parseClause c.mv (cnfBytes.drop i0) with
    | none =>
      ∀ s' m', s'.LengthsOk c → s'.fuel = s.fuel → s'.oom = s.oom →
        s'.probing = s.probing → s'.heur.rel_trigger = s.heur.rel_trigger →
        (bytes cnf_ptr cnfBytes ⋆ PlainMem c s' ⋆ R) m' → Q (0#64, ()) m'
    | some (cl, rest) =>
      ∀ r s' j m',
        (∀ lit ∈ cl.literals, 1 ≤ lit.1) →
        i0 < j → j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        s'.LengthsOk c → s'.d_cur = cnf_ptr + BitVec.ofNat 64 j →
        s'.cur_level = 0 → s'.fuel = s.fuel → s'.oom = s.oom →
        s'.probing = s.probing → s'.heur.rel_trigger = s.heur.rel_trigger →
        (r = 1#64 ∨ r = 2#64 ∨ r = 3#64) →
        (r = 1#64 → PlainInv c (shiftDownCnf (accCnf.add cl)) s') →
        (r = 2#64 → (shiftDownCnf (accCnf.add cl)).Unsat) →
        (∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
          s.vals[l]?.getD 0#8 = 0#8 →
          r = 1#64 ∧ s'.vals = (s.vals.set l 1#8).set (l ^^^ 1) 0xFF#8 ∧
          s'.trail_end = s.trail_end + 1 ∧ s'.propagated = s.propagated ∧
          s'.arena_len = s.arena_len ∧ s'.wlen = s.wlen ∧ s'.wvec = s.wvec) →
        (∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
          s.vals[l]?.getD 0#8 = 0xFF#8 → r = 2#64) →
        (bytes cnf_ptr cnfBytes ⋆ PlainMem c s' ⋆ R) m' → Q (r, ()) m'

def plainParseBodySpec : Spec [i64, i64] [i64] := fun (h, cend, ()) m Q _ =>
  ∃ (c : PlainCfg) (s : PlainState) (cnf_ptr : BitVec 64) (cnfBytes : List UInt8)
    (i0 : Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ i0 ≤ cnfBytes.length ∧
    parseHeader cnfBytes = some (c.mv, c.nc, cnfBytes.drop i0) ∧
    s.d_cur = cnf_ptr + BitVec.ofNat 64 i0 ∧ s.cur_level = 0 ∧ s.trail_end = 0 ∧
    s.propagated = 0 ∧ s.arena_len = 0 ∧ s.oom = 0#64 ∧ s.probing = 0#64 ∧
    PlainInv c (shiftDownCnf CNF.empty) s ∧
    (bytes cnf_ptr cnfBytes ⋆ PlainMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → s'.fuel = s.fuel →
      s'.oom = 0#64 → s'.probing = 0#64 → s'.heur.rel_trigger = s.heur.rel_trigger →
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
      (r = 1#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        PlainInv c (shiftDownCnf cnf) s' ∧ s'.cur_level = 0) →
      (∀ vals' te', UnitSatTrace c.mv s.vals 0 (cnfBytes.drop i0) c.nc vals' te' →
        r = 1#64 ∧ s'.vals = vals' ∧ s'.trail_end = te' ∧ s'.propagated = 0 ∧
        s'.arena_len = 0 ∧ s'.wvec = s.wvec) →
      (UnitUnsatTrace c.mv s.vals (cnfBytes.drop i0) c.nc → r = 20#64) →
      (bytes cnf_ptr cnfBytes ⋆ PlainMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ## 3. BCP, reason marking, `reduce` / `sweep` GC (`Plain1` + `Plain2`) -/

def plainFindReplSpec : Spec [i64, i64] [i64] := fun (h, cref, ()) m Q _ =>
  ∃ (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ cref.toNat + 3 ≤ s.arena_len ∧
    3 ≤ arenaClauseSize s cref.toNat ∧
    cref.toNat + 3 + arenaClauseSize s cref.toNat ≤ s.arena_len ∧
    (PlainMem c s ⋆ R) m ∧
    ((∀ k, 2 ≤ k → k < arenaClauseSize s cref.toNat →
        let cand := (s.arena[cref.toNat + 3 + k]?.getD 0#32).toNat
        2 * c.mv ≤ cand ∨ ((s.vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = true) →
      Q (0xFFFFFFFF#64, ()) m) ∧
    (∀ (r : Nat) (m' : Mem 64),
      2 ≤ r → r < arenaClauseSize s cref.toNat →
      (let cand := (s.arena[cref.toNat + 3 + r]?.getD 0#32).toNat
       cand < 2 * c.mv ∧ ((s.vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = false) →
      (PlainMem c { s with arena := s.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r) } ⋆ R) m' →
      Q (BitVec.ofNat 64 r, ()) m')

def plainPropLitSpec : Spec [i64, i32] [.bool] := fun (h, lit, ()) m Q _ =>
  ∃ (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ PlainCoreInv c F0 s ∧ s.oom = 0#64 ∧ (PlainMem c s ⋆ R) m ∧
    ∀ (ok : Bool) vals' lvl' rsns' trl' tp' te' unfl' wvec' arena' wstk' wlen' wu'
      ctype' cref' c0' c1' oom' heur' m',
      let s' : PlainState :=
        { s with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', unflushed := unfl', wvec := wvec', arena := arena',
          wstk := wstk', wlen := wlen', wusable := wu', confl_type := ctype',
          confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom', heur := heur' }
      PlainCoreInv c F0 s' → s.trail_end ≤ te' → heur'.rel_trigger = s.heur.rel_trigger →
      (∀ i < s.trail_end, trl'[i]? = s.trl[i]?) →
      (∀ i < s.trail_end,
        lvl'[(s.trl[i]?.getD 0#32).toNat / 2]? = s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?) →
      (∀ i, s.trail_end ≤ i → i < te' →
        (lvl'[(trl'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.cur_level) →
      (ok = false → oom' ≠ 0#64 ∨
        (ctype' = 1#64 ∧ c0'.toNat < 2 * c.mv ∧ c1'.toNat < 2 * c.mv ∧
          F0.EntailsClause (cnfClause [c0'.toNat, c1'.toNat]) ∧
          s'.vals[c0'.toNat]?.getD 0#8 = 0xFF#8 ∧ s'.vals[c1'.toNat]?.getD 0#8 = 0xFF#8) ∨
        (ctype' = 2#64 ∧ cref'.toNat ∈ arenaClauseRefs s' ∧
          arenaClauseGarb s' cref'.toNat = false ∧
          ∀ l ∈ arenaClauseLits s' cref'.toNat, s'.vals[l]?.getD 0#8 = 0xFF#8)) →
      (watchSize s (lit ^^^ 1#32).toNat = 0 → ok = true ∧ s' = s) →
      (ok = true → oom' = 0#64) →
      (PlainMem c s' ⋆ R) m' → Q (ok, ()) m'

def plainPropagateSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ PlainCoreInv c F0 s ∧ (PlainMem c s ⋆ R) m ∧
    ∀ r vals' lvl' rsns' trl' tp' te' prop' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' heur' m',
      let s' : PlainState :=
        { s with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', propagated := prop', unflushed := unfl', wvec := wvec',
          arena := arena', wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
          confl_type := ctype', confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
          oom := oom', heur := heur' }
      PlainCoreInv c F0 s' → s.trail_end ≤ te' → fuel'.toNat ≤ s.fuel.toNat →
      heur'.rel_trigger = s.heur.rel_trigger →
      (∀ i < s.trail_end, trl'[i]? = s.trl[i]?) →
      (∀ i < s.trail_end,
        lvl'[(s.trl[i]?.getD 0#32).toNat / 2]? = s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?) →
      (∀ i, s.trail_end ≤ i → i < te' →
        (lvl'[(trl'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.cur_level) →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ (s.oom = 0#64 → oom' = 0#64)) →
      (r = 1#64 →
        fuel'.toNat < s.fuel.toNat ∧ oom' = 0#64 ∧
        ((ctype' = 1#64 ∧ c0'.toNat < 2 * c.mv ∧ c1'.toNat < 2 * c.mv ∧
          F0.EntailsClause (cnfClause [c0'.toNat, c1'.toNat]) ∧
          s'.vals[c0'.toNat]?.getD 0#8 = 0xFF#8 ∧ s'.vals[c1'.toNat]?.getD 0#8 = 0xFF#8) ∨
         (ctype' = 2#64 ∧ cref'.toNat ∈ arenaClauseRefs s' ∧
          arenaClauseGarb s' cref'.toNat = false ∧
          ∀ l ∈ arenaClauseLits s' cref'.toNat, s'.vals[l]?.getD 0#8 = 0xFF#8))) →
      (s.oom = 0#64 → (∀ l < 2 * c.mv, watchSize s l = 0) →
        s.trail_end - s.propagated ≤ s.fuel.toNat →
        r = 0#64 ∧ vals' = s.vals ∧ te' = s.trail_end ∧ prop' = s.trail_end ∧
        wvec' = s.wvec ∧ oom' = 0#64 ∧
        fuel'.toNat = s.fuel.toNat - (s.trail_end - s.propagated)) →
      (s.propagated = s.trail_end → r = 0#64 ∧ s' = s) →
      (PlainMem c s' ⋆ R) m' → Q (r, ()) m'

def plainMarkReasonsSpec : Spec [i64, .bool] [] := fun (h, set_flag, ()) m Q _ =>
  ∃ (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ PlainCoreInv c F0 s ∧ (PlainMem c s ⋆ R) m ∧
    ∀ arena' m',
      let s' : PlainState := { s with arena := arena' }
      arenaClauseRefs s' = arenaClauseRefs s →
      (∀ r ∈ arenaClauseRefs s, arenaClauseSize s' r = arenaClauseSize s r ∧
        arenaClauseGarb s' r = arenaClauseGarb s r ∧
        arenaClauseLits s' r = arenaClauseLits s r) →
      (set_flag = true → ReasonsMarked s') →
      PlainCoreInv c F0 s' → (PlainMem c s' ⋆ R) m' → Q () m'

def plainRedLessSpec : Spec [i64, i32, i32] [.bool] := fun (ar_ptr, a, b, ()) m Q _ =>
  ∃ (ar : List (BitVec 32)) (R : Mem 64 → Prop),
    a.toNat + 2 < ar.length ∧ b.toNat + 2 < ar.length ∧
    (array (t := i32) ar_ptr ar ⋆ R) m ∧
    ∀ res : Bool, Q (res, ()) m

def plainSortRedsSpec : Spec [i64, i64] [] := fun (h, n, ()) m Q _ =>
  ∃ (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ n.toNat ≤ c.red_cap ∧
    (∀ k < n.toNat, (s.heur.red_refs[k]?.getD 0#32).toNat + 2 < c.arena_cap) ∧
    (PlainMem c s ⋆ R) m ∧
    ∀ heur' m', heur'.LengthsOk c → heur'.rel_trigger = s.heur.rel_trigger →
      (∀ k < n.toNat, ∃ j < n.toNat, heur'.red_refs[k]? = s.heur.red_refs[j]?) →
      (PlainMem c { s with heur := heur' } ⋆ R) m' → Q () m'

def plainLitRankSpec : Spec [i64, i64, i32] [i64] := fun (vals_ptr, lvl_ptr, l, ()) m Q _ =>
  ∃ (vals : List (BitVec 8)) (lvl : List (BitVec 32)) (R : Mem 64 → Prop),
    l.toNat < vals.length ∧ l.toNat / 2 < lvl.length ∧
    (array (t := i8) vals_ptr vals ⋆ array (t := i32) lvl_ptr lvl ⋆ R) m ∧
    ∀ r : BitVec 64, Q (r, ()) m

def plainSweepSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ PlainCoreInv c F0 s ∧ (0 < s.cur_level → ReasonsMarked s) ∧
    (PlainMem c s ⋆ R) m ∧
    ∀ r vals' lvl' rsns' trl' tp' te' unfl' wvec' wstk' arena' alen' wlen' wu' fred' ni' nr'
      nb' oom' heur' m',
      let s' : PlainState :=
        { s with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', unflushed := unfl', wvec := wvec', wstk := wstk',
          arena := arena', arena_len := alen', wlen := wlen', wusable := wu',
          arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
          num_redundant := nr', num_binary := nb', oom := oom', heur := heur' }
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 3#64) →
      heur'.rel_trigger = s.heur.rel_trigger →
      (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * c.mv) →
      (r = 0#64 ∨ r = 1#64 → PlainCoreInv c F0 s' ∧ oom' = 0#64) →
      (0 < s.cur_level → r = 0#64 →
        vals' = s.vals ∧ lvl' = s.lvl ∧ trl' = s.trl ∧ tp' = s.trail_pos ∧ te' = s.trail_end) →
      (r = 1#64 → s.cur_level = 0 ∧ s.trail_end < te') →
      (r = 2#64 → s.cur_level = 0 ∧ F0.Unsat) →
      (PlainMem c s' ⋆ R) m' → Q (r, ()) m'

def plainReduceSpec : Spec [i64, .bool] [i64] := fun (h, _force, ()) m Q _ =>
  ∃ (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ PlainCoreInv c F0 s ∧ (PlainMem c s ⋆ R) m ∧
    ∀ r vals' lvl' rsns' trl' tp' te' prop' cl' fuel' unfl' wvec' wstk' arena' alen' wlen'
      wu' ag' fred' ni' nr' nb' ctype' cref' c0' c1' oom' heur' m',
      let s' : PlainState :=
        { s with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', propagated := prop', cur_level := cl', fuel := fuel',
          unflushed := unfl', wvec := wvec', wstk := wstk', arena := arena',
          arena_len := alen', wlen := wlen', wusable := wu', arena_garbage := ag',
          first_reducible := fred', num_irred := ni', num_redundant := nr', num_binary := nb',
          confl_type := ctype', confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
          oom := oom', heur := heur' }
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → fuel'.toNat ≤ s.fuel.toNat →
      (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * c.mv) →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → PlainCoreInv c F0 s' ∧ cl' ≤ s.cur_level ∧ (s.oom = 0#64 → oom' = 0#64)) →
      (r = 1#64 → 0 < cl' →
        cl' = s.cur_level ∧ vals' = s.vals ∧ lvl' = s.lvl ∧ trl' = s.trl ∧
        tp' = s.trail_pos ∧ te' = s.trail_end) →
      (PlainMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ## 4. Conflict analysis, shrink/minimize, decision, mode/restart, `lucky` (`Plain2`) -/

def plainAnalyzeLitSpec : Spec [i64, i32, i32] [.bool] := fun (h, lit, skip_var, ()) m Q _ =>
  ∃ (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.cur_level < 2 ^ 32 ∧ s.tmp_len ≤ c.mv ∧
    s.tmp_cnt + 1 < 2 ^ 64 ∧ (PlainMem c s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' tmp' tc' tl' m',
      let s' : PlainState :=
        { s with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl' }
      s'.LengthsOk c → s.tmp_len ≤ tl' → tl' ≤ s.tmp_len + 1 → tl' ≤ c.mv → s.tmp_cnt ≤ tc' →
      tc' = s.tmp_cnt +
        (if lit.toNat / 2 < c.mv ∧ s.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
            mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
            (s.lvl[lit.toNat / 2]?.getD 0#32).toNat = s.cur_level
         then 1 else 0) →
      (∀ v < c.mv, s.mrk[v]?.getD 0#8 ≠ 0#8 → mrk'[v]?.getD 0#8 = s.mrk[v]?.getD 0#8) →
      (∀ k < s.tmp_len, tmp'[k]? = s.tmp[k]?) →
      (∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
        lit.toNat / 2 = v ∧ v ≠ skip_var.toNat ∧
        0 < (s.lvl[v]?.getD 0#32).toNat ∧ (s.lvl[v]?.getD 0#32).toNat ≤ s.cur_level) →
      (∀ j, s.tmp_len ≤ j → j < tl' →
        (tmp'[j]?.getD 0#32).toNat = lit.toNat ∧ lit.toNat / 2 < c.mv ∧
        lit.toNat / 2 ≠ skip_var.toNat ∧ s.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
        0 < (s.lvl[lit.toNat / 2]?.getD 0#32).toNat ∧
        (s.lvl[lit.toNat / 2]?.getD 0#32).toNat < s.cur_level ∧
        mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8) →
      (ok = true →
        lit.toNat / 2 < c.mv ∧
        (lit.toNat / 2 ≠ skip_var.toNat →
          (0 < (s.lvl[lit.toNat / 2]?.getD 0#32).toNat →
            mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8) ∧
          (s.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 →
            (s.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ s.cur_level ∧
            (0 < (s.lvl[lit.toNat / 2]?.getD 0#32).toNat →
              (s.lvl[lit.toNat / 2]?.getD 0#32).toNat = s.cur_level →
              tc' = s.tmp_cnt + 1) ∧
            (0 < (s.lvl[lit.toNat / 2]?.getD 0#32).toNat →
              (s.lvl[lit.toNat / 2]?.getD 0#32).toNat < s.cur_level →
              tl' = s.tmp_len + 1 ∧ tmp'[s.tmp_len]? = some lit)))) →
      (PlainMem c s' ⋆ R) m' → Q (ok, ()) m'

def plainAnalyzeRsnSpec : Spec [i64, i32, i32] [.bool] := fun (h, rsn, skip_var, ()) m Q _ =>
  ∃ (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ PlainCoreInv c F0 s ∧ s.tmp_len ≤ c.mv ∧ s.tmp_cnt + c.mv + 1 < 2 ^ 64 ∧
    (rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ∈ arenaClauseRefs s) ∧
    (PlainMem c s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' tmp' tc' tl' arena' heur' m',
      let s' : PlainState :=
        { s with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                 arena := arena', heur := heur' }
      PlainCoreInv c F0 s' → s.tmp_len ≤ tl' → tl' ≤ c.mv → s.tmp_cnt ≤ tc' →
      arenaClauseRefs s' = arenaClauseRefs s →
      (∀ r ∈ arenaClauseRefs s, arenaClauseSize s' r = arenaClauseSize s r ∧
        arenaClauseGarb s' r = arenaClauseGarb s r ∧
        arenaClauseLits s' r = arenaClauseLits s r) →
      (∀ v < c.mv, s.mrk[v]?.getD 0#8 ≠ 0#8 → mrk'[v]?.getD 0#8 = s.mrk[v]?.getD 0#8) →
      (∀ k < s.tmp_len, tmp'[k]? = s.tmp[k]?) →
      (∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
        ∃ l ∈ rsnLits s rsn,
          l / 2 = v ∧ v ≠ skip_var.toNat ∧
          0 < (s.lvl[v]?.getD 0#32).toNat ∧ (s.lvl[v]?.getD 0#32).toNat ≤ s.cur_level) →
      (∀ j, s.tmp_len ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        l ∈ rsnLits s rsn ∧ l < 2 * c.mv ∧ l / 2 ≠ skip_var.toNat ∧
        s.mrk[l / 2]?.getD 0#8 = 0#8 ∧
        0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧ (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level ∧
        mrk'[l / 2]?.getD 0#8 ≠ 0#8) →
      (tc' - s.tmp_cnt =
        ((List.range c.mv).filter fun v =>
          decide (s.mrk[v]?.getD 0#8 = 0#8) &&
          decide (mrk'[v]?.getD 0#8 ≠ 0#8) &&
          decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)).length) →
      (ok = true → rsn ≠ 0xFFFFFFFF#32 ∧
        ((rsn &&& 0x80000000#32) ≠ 0#32 →
          (rsn &&& 0x7FFFFFFF#32).toNat / 2 < c.mv) ∧
        ((rsn &&& 0x80000000#32) = 0#32 →
          rsn.toNat + 3 ≤ s.arena_len ∧ 3 ≤ arenaClauseSize s rsn.toNat ∧
          rsn.toNat + 3 + arenaClauseSize s rsn.toNat ≤ s.arena_len) ∧
        ∀ l ∈ rsnLits s rsn,
          l / 2 < c.mv ∧
          (l / 2 ≠ skip_var.toNat →
            (0 < (s.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
            (s.mrk[l / 2]?.getD 0#8 = 0#8 →
              (s.lvl[l / 2]?.getD 0#32).toNat ≤ s.cur_level ∧
              (0 < (s.lvl[l / 2]?.getD 0#32).toNat →
                (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level →
                ∃ j, s.tmp_len ≤ j ∧ j < tl' ∧
                  (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) →
      (PlainMem c s' ⋆ R) m' → Q (ok, ()) m'

def plainClearMarksSpec : Spec [i64, i64] [] := fun (h, trail_from, ()) m Q _ =>
  ∃ (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.tmp_len ≤ c.mv ∧ (PlainMem c s ⋆ R) m ∧
    ∀ mrk' m', mrk'.length = c.mv →
      (∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 = 0#8) →
      (∀ i, 1 ≤ i → i < s.tmp_len → (s.tmp[i]?.getD 0#32).toNat / 2 < c.mv →
        mrk'[(s.tmp[i]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) →
      (∀ j, trail_from.toNat ≤ j → j < s.trail_end → (s.trl[j]?.getD 0#32).toNat / 2 < c.mv →
        mrk'[(s.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) →
      (PlainMem c { s with mrk := mrk' } ⋆ R) m' → Q () m'

def plainMinMarkSpec : Spec [i64, i32, i8] [] := fun (h, v, tag, ()) m Q _ =>
  ∃ (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (PlainMem c s ⋆ R) m ∧
    let cur := s.mrk[v.toNat]?.getD 0#8
    if c.mv ≤ v.toNat ∨ (cur &&& tag) ≠ 0#8 then
      Q () m
    else
      let mrk' := s.mrk.set v.toNat (cur ||| tag)
      if cur ≠ 0#8 then
        ∀ m', (PlainMem c { s with mrk := mrk' } ⋆ R) m' → Q () m'
      else if s.min_clr_len < c.mv then
        ∀ m', (PlainMem c { s with
          mrk := mrk', min_clr := s.min_clr.set s.min_clr_len v,
          min_clr_len := s.min_clr_len + 1 } ⋆ R) m' → Q () m'
      else
        ∀ m', (PlainMem c { s with mrk := mrk', min_clr_full := 1#64 } ⋆ R) m' → Q () m'

def plainMinLitSpec : Spec [i64, i32] [.bool] := fun (h, root_lit, ()) m Q _ =>
  ∃ (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) (keepSet : List Nat)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ PlainCoreInv c F0 s ∧ PlainMinMarkInv c F0 s keepSet ∧
    root_lit.toNat < 2 * c.mv ∧ s.vals[root_lit.toNat]?.getD 0#8 = 0xFF#8 ∧
    (∀ v < c.mv,
      (s.lvl[v]?.getD 0#32).toNat ≤ (s.lvl[root_lit.toNat / 2]?.getD 0#32).toNat →
      (s.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
    (PlainMem c s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' mstk' mclr' mcl' mcf' m',
      let s' : PlainState :=
        { s with mrk := mrk', min_stk := mstk', min_clr := mclr',
                 min_clr_len := mcl', min_clr_full := mcf' }
      s'.LengthsOk c →
      (∀ v < c.mv,
        (s.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (∀ v < c.mv, (mrk'[v]?.getD 0#8 &&& 8#8) = (s.mrk[v]?.getD 0#8 &&& 8#8)) →
      PlainMinMarkInv c F0 s' keepSet →
      (ok = true →
        (∀ keep' : List Nat,
          (∀ l ∈ keepSet, l = root_lit.toNat ∨ l ∈ keep') → PlainMinMarkInv c F0 s' keep') ∧
        PlainMinMarkInv c F0 (plainMinMarkState c s' (root_lit.toNat / 2) 2#8) keepSet) →
      (PlainMem c s' ⋆ R) m' → Q (ok, ()) m'

def plainTmpLessSpec : Spec [i64, i64, i32, i32] [.bool] :=
  fun (lvl_ptr, tpos_ptr, a, b, ()) m Q _ =>
    ∃ (lvl tpos : List (BitVec 32)) (R : Mem 64 → Prop),
      let va := a.toNat / 2
      let vb := b.toNat / 2
      let la := (lvl[va]?.getD 0#32).toNat
      let lb := (lvl[vb]?.getD 0#32).toNat
      va < lvl.length ∧ vb < lvl.length ∧ va < tpos.length ∧ vb < tpos.length ∧
      (array (t := i32) lvl_ptr lvl ⋆ array (t := i32) tpos_ptr tpos ⋆ R) m ∧
      Q (decide (la < lb ∨ (la = lb ∧
        (tpos[va]?.getD 0#32).toNat < (tpos[vb]?.getD 0#32).toNat)), ()) m

def plainSortTmpSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.tmp_len ≤ c.mv ∧
    (∀ k, 1 ≤ k → k < s.tmp_len → (s.tmp[k]?.getD 0#32).toNat < 2 * c.mv) ∧
    (PlainMem c s ⋆ R) m ∧
    ∀ tmp' m',
      tmp'.length = c.mv →
      (0 < s.tmp_len → tmp'[0]? = s.tmp[0]?) →
      (∀ j, 1 ≤ j → j < s.tmp_len → ∃ i, 1 ≤ i ∧ i < s.tmp_len ∧ tmp'[j]? = s.tmp[i]?) →
      (∀ i, 1 ≤ i → i < s.tmp_len → ∃ j, 1 ≤ j ∧ j < s.tmp_len ∧ s.tmp[i]? = tmp'[j]?) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.tmp_len →
        (s.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (PlainMem c { s with tmp := tmp' } ⋆ R) m' → Q () m'

def plainShrinkBlkSpec : Spec [i64, i64, i64, i32, i64] [] :=
  fun (h, beg, end_b, blvl, max_tr, ()) m Q _ =>
    ∃ (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) (R : Mem 64 → Prop),
      h = c.hdr ∧ PlainCoreInv c F0 s ∧
      PlainMinMarkInv c F0 s
        (((s.tmp.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) ∧
      (∀ v < c.mv, (s.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
      1 ≤ beg.toNat ∧ beg.toNat < end_b.toNat ∧
      end_b.toNat ≤ s.tmp_len ∧ s.tmp_len ≤ c.mv ∧
      0 < blvl.toNat ∧ blvl.toNat < s.cur_level ∧
      F0.EntailsClause (cnfClause
        (((s.tmp.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) ∧
      (∀ k, beg.toNat ≤ k → k < end_b.toNat →
        let l := (s.tmp[k]?.getD 0#32).toNat
        l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧
        (s.lvl[l / 2]?.getD 0#32).toNat = blvl.toNat ∧
        (s.trail_pos[l / 2]?.getD 0#32).toNat ≤ max_tr.toNat) ∧
      (∀ k < s.tmp_len, s.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        let l := (s.tmp[k]?.getD 0#32).toNat
        l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧
        (s.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
      (PlainMem c s ⋆ R) m ∧
      ∀ tmp' mrk' mstk' mclr' mcl' mcf' heur' m',
        let s' : PlainState :=
          { s with tmp := tmp', mrk := mrk', min_stk := mstk', min_clr := mclr',
                   min_clr_len := mcl', min_clr_full := mcf', heur := heur' }
        PlainCoreInv c F0 s' →
        PlainMinMarkInv c F0 s'
          (((tmp'.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) →
        (∀ v < c.mv, (mrk'[v]?.getD 0#8 &&& 8#8) = 0#8) →
        tmp'.length = c.mv → heur'.rel_trigger = s.heur.rel_trigger →
        (∀ v < c.mv,
          (s.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
        (∀ k < s.tmp_len, (k < beg.toNat ∨ end_b.toNat ≤ k) → tmp'[k]? = s.tmp[k]?) →
        (∀ k, beg.toNat ≤ k → k < end_b.toNat → tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
          (s.lvl[(tmp'[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat) →
        F0.EntailsClause (cnfClause
          (((tmp'.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) →
        (∀ k < s.tmp_len, tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
          let l := (tmp'[k]?.getD 0#32).toNat
          l < 2 * c.mv ∧ s'.vals[l]?.getD 0#8 = 0xFF#8 ∧
          (mrk'[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) →
        (PlainMem c s' ⋆ R) m' → Q () m'

def plainMinShrinkSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ PlainInv c F0 s ∧ 1 ≤ s.tmp_len ∧ s.tmp_len ≤ c.mv ∧
    F0.EntailsClause (cnfClause ((s.tmp.take s.tmp_len).map BitVec.toNat)) ∧
    (∀ k < s.tmp_len, let l := (s.tmp[k]?.getD 0#32).toNat
      l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8) ∧
    (∀ k, 1 ≤ k → k < s.tmp_len →
      let lv := (s.lvl[(s.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.cur_level) ∧
    (PlainMem c s ⋆ R) m ∧
    ∀ tmp' tl' mrk' mstk' mclr' mcl' mcf' heur' m',
      let s' : PlainState := { s with
        tmp := tmp', tmp_len := tl', mrk := mrk', min_stk := mstk', min_clr := mclr',
        min_clr_len := mcl', min_clr_full := mcf', heur := heur' }
      PlainInv c F0 s' → 1 ≤ tl' → tl' ≤ s.tmp_len → tmp'[0]? = s.tmp[0]? →
      heur'.rel_trigger = s.heur.rel_trigger →
      (∀ j, 1 ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        let lv := (s.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧
        0 < lv ∧ lv < s.cur_level ∧
        lv ≤ (s.lvl[(tmp'[tl' - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      F0.EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat)) →
      (PlainMem c s' ⋆ R) m' → Q () m'

def plainAnalyzeSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ PlainInv c F0 s ∧
    ((s.confl_type = 1#64 ∧ s.confl_lit0.toNat < 2 * c.mv ∧ s.confl_lit1.toNat < 2 * c.mv ∧
      F0.EntailsClause (cnfClause [s.confl_lit0.toNat, s.confl_lit1.toNat]) ∧
      s.vals[s.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
      s.vals[s.confl_lit1.toNat]?.getD 0#8 = 0xFF#8) ∨
     (s.confl_type ≠ 1#64 ∧ s.confl_ref.toNat ∈ arenaClauseRefs s ∧
      arenaClauseGarb s s.confl_ref.toNat = false ∧
      ∀ l ∈ arenaClauseLits s s.confl_ref.toNat, s.vals[l]?.getD 0#8 = 0xFF#8)) ∧
    (PlainMem c s ⋆ R) m ∧
    ∀ r vals' lvl' rsns' trl' tp' te' prop' cl' fuel' tc' tl' mrk' tmp' wvec' arena' alen' wstk'
      wlen' wu' ag' fred' ni' nr' nb' unfl' ctype' cref' c0' c1' oom' mstk' mclr' mcl' mcf'
      heur' m',
      let s' : PlainState := { s with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', cur_level := cl', fuel := fuel',
        tmp_cnt := tc', tmp_len := tl', mrk := mrk', tmp := tmp', wvec := wvec',
        arena := arena', arena_len := alen', wstk := wstk', wlen := wlen', wusable := wu',
        arena_garbage := ag', first_reducible := fred', num_irred := ni', num_redundant := nr',
        num_binary := nb', unflushed := unfl', confl_type := ctype', confl_ref := cref',
        confl_lit0 := c0', confl_lit1 := c1', oom := oom', min_stk := mstk', min_clr := mclr',
        min_clr_len := mcl', min_clr_full := mcf', heur := heur' }
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → fuel'.toNat ≤ s.fuel.toNat →
      (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * c.mv) →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → PlainInv c F0 s' ∧ cl' < s.cur_level) →
      (PlainMem c s' ⋆ R) m' → Q (r, ()) m'

def plainDecideSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ PlainInv c F0 s ∧ (PlainMem c s ⋆ R) m ∧
    ∀ r vals' lvl' rsns' trl' tp' te' cl' unfl' heur' m',
      let s' : PlainState := { s with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', cur_level := cl', unflushed := unfl', heur := heur' }
      PlainInv c F0 s' → (r = 0#64 ∨ r = 1#64) →
      heur'.rel_trigger = s.heur.rel_trigger →
      (r = 0#64 → vals' = s.vals ∧ lvl' = s.lvl ∧ rsns' = s.rsns ∧ trl' = s.trl ∧
        te' = s.trail_end ∧ cl' = s.cur_level ∧
        ∀ v < c.mv, s.vals[2 * v]?.getD 0#8 ≠ 0#8) →
      ((∀ v < c.mv, s.vals[2 * v]?.getD 0#8 ≠ 0#8) →
        r = 0#64 ∧ vals' = s.vals ∧ lvl' = s.lvl ∧ rsns' = s.rsns ∧ trl' = s.trl ∧
        te' = s.trail_end ∧ cl' = s.cur_level) →
      (PlainMem c s' ⋆ R) m' → Q (r, ()) m'

def plainRephaseSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ PlainInv c F0 s ∧ (PlainMem c s ⋆ R) m ∧
    ∀ vals' lvl' rsns' te' prop' heur' m',
      let s' : PlainState := { s with
        vals := vals', lvl := lvl', rsns := rsns', trail_end := te',
        propagated := prop', cur_level := 0, heur := heur' }
      PlainInv c F0 s' → (PlainMem c s' ⋆ R) m' → Q () m'

def plainRestartDueSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (PlainMem c s ⋆ R) m ∧
    ∀ r heur' m', heur'.LengthsOk c → (r = 0#64 ∨ r = 1#64) →
      (PlainMem c { s with heur := heur' } ⋆ R) m' → Q (r, ()) m'

def plainLuckyScanSpec : Spec [i64, .bool, .bool] [i64] := fun (h, _pm, _fwd, ()) m Q _ =>
  ∃ (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ PlainInv c F0 s ∧ (PlainMem c s ⋆ R) m ∧
    ∀ r vals' lvl' rsns' trl' tp' te' prop' cl' tc' tl' mrk' tmp' wvec' arena' alen' wstk'
      wlen' wu' ag' fred' ni' nr' nb' unfl' fuel' ctype' cref' c0' c1' oom' mstk' mclr' mcl'
      mcf' heur' m',
      let s' : PlainState := { s with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', cur_level := cl', tmp_cnt := tc', tmp_len := tl',
        mrk := mrk', tmp := tmp', wvec := wvec', arena := arena', arena_len := alen',
        wstk := wstk', wlen := wlen', wusable := wu', arena_garbage := ag',
        first_reducible := fred', num_irred := ni', num_redundant := nr', num_binary := nb',
        unflushed := unfl', fuel := fuel', confl_type := ctype', confl_ref := cref',
        confl_lit0 := c0', confl_lit1 := c1', oom := oom', min_stk := mstk', min_clr := mclr',
        min_clr_len := mcl', min_clr_full := mcf', heur := heur' }
      s'.LengthsOk c → (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) →
      (r = 10#64 → PlainInv c F0 s') →
      (r = 0#64 → PlainInv c F0 s') →
      (PlainMem c s' ⋆ R) m' → Q (r, ()) m'

def plainLuckySpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) (R : Mem 64 → Prop),
    h = c.hdr ∧ PlainInv c F0 s ∧ (PlainMem c s ⋆ R) m ∧
    ∀ r vals' lvl' rsns' trl' tp' te' prop' cl' tc' tl' mrk' tmp' wvec' arena' alen' wstk'
      wlen' wu' ag' fred' ni' nr' nb' unfl' fuel' ctype' cref' c0' c1' oom' mstk' mclr' mcl'
      mcf' heur' m',
      let s' : PlainState := { s with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', cur_level := cl', tmp_cnt := tc', tmp_len := tl',
        mrk := mrk', tmp := tmp', wvec := wvec', arena := arena', arena_len := alen',
        wstk := wstk', wlen := wlen', wusable := wu', arena_garbage := ag',
        first_reducible := fred', num_irred := ni', num_redundant := nr', num_binary := nb',
        unflushed := unfl', probing := 0#64, fuel := fuel', confl_type := ctype',
        confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom',
        min_stk := mstk', min_clr := mclr', min_clr_len := mcl', min_clr_full := mcf',
        heur := heur' }
      s'.LengthsOk c → (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) →
      (r = 10#64 → PlainInv c F0 s') →
      (r = 0#64 → PlainInv c F0 s') →
      (PlainMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ## 5. Top-level `kissat_solve_bytes` contracts & `Env.ofTable` (`59` functions) -/

/-- Converse of `trail_end_lt_of_unassigned`: all variables assigned forces `c.mv ≤ s.trail_end`. -/
theorem PlainCoreInv.mv_le_te {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (h : PlainCoreInv c F0 s) (hall : ∀ v < c.mv, s.vals[2 * v]?.getD 0#8 ≠ 0#8) :
    c.mv ≤ s.trail_end := by
  let idxOf : Nat → Nat :=
    fun v => (List.range s.trail_end).findIdx (fun i => (s.trl[i]?.getD 0#32).toNat / 2 == v)
  have hmem : ∀ v < c.mv,
      idxOf v < s.trail_end ∧ (s.trl[idxOf v]?.getD 0#32).toNat / 2 = v := by
    intro v hv
    have hnex : ¬ ∀ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat / 2 ≠ v := by
      intro hnone
      exact hall v hv ((h.vals_zero_iff (by omega : 2 * v < 2 * c.mv)).mpr fun i hi => by
        have := hnone i hi; omega)
    have hex : ∃ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat / 2 = v :=
      Classical.byContradiction fun hc => hnex fun i hi hEq => hc ⟨i, hi, hEq⟩
    obtain ⟨i, hi, heq⟩ := hex
    have hlt : idxOf v < (List.range s.trail_end).length :=
      List.findIdx_lt_length.mpr ⟨i, List.mem_range.mpr hi, by simp [heq]⟩
    have hp := List.findIdx_getElem (xs := List.range s.trail_end)
      (p := fun k => (s.trl[k]?.getD 0#32).toNat / 2 == v) (w := hlt)
    simp only [List.getElem_range, beq_iff_eq] at hp
    simp only [List.length_range] at hlt
    exact ⟨hlt, hp⟩
  have hlt_mv : c.mv < s.trail_end + 1 :=
    inj_lt_of_missing (k := c.mv) (n := s.trail_end + 1) (v := s.trail_end) idxOf
      (fun a b ha hb heq => by rw [← (hmem a ha).2, ← (hmem b hb).2, heq])
      (fun v hv => by have := (hmem v hv).1; omega)
      (by omega)
      (fun v hv => by have := (hmem v hv).1; omega)
  omega

/-- Core `kissat_solve_bytes` contract carrying both general soundness (`0 | 10 | 20`)
and deterministic unit-clause witness traces (`UnitSatTrace`, `UnitUnsatTrace`) for
non-vacuity. -/
def plainSolveBytesCoreSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
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
          plainFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen →
          i0 ≤ cnfBytes.length →
          parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
          r = 20#64) →
        (∀ mv nc i0 vals' te',
          te' < fuel.toNat →
          plainFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen →
          i0 ≤ cnfBytes.length →
          parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitSatTrace mv (List.replicate (2 * mv) 0#8) 0 (cnfBytes.drop i0) nc vals' te' →
          (∀ v < mv, vals'[2 * v]?.getD 0#8 ≠ 0#8) →
          runKissatCheckModel cnfBytes (vals'.map UInt8.ofBitVec) mv = true →
          r = 10#64) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
        Q (r, ()) m'

/-- Headline soundness specification of `kissat_solve_bytes`. -/
def plainSolveBytesSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, _fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m', (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' → Q (r, ()) m'

theorem plainSolveBytesCoreSpec_of_spec
    {args : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : plainSolveBytesSpec args m Q X) : plainSolveBytesCoreSpec args m Q X := by
  obtain ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm, hQ⟩ := h
  exact ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm,
    fun r m' hdom hu hs _ _ hm' => hQ r m' hdom hu hs hm'⟩

/-- Specification table matching `plainFns` (`dimacs_fns ++ plain1_fns ++ plain2_fns`)
row-by-row (`59` functions). -/
def plainSpecTable (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : List SpecEntry :=
  [ ⟨"kissat_is_ws", [i64], [.bool], kissatIsWsSpec, true⟩
  , ⟨"kissat_is_digit", [i64], [.bool], kissatIsDigitSpec, true⟩
  , ⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, true⟩
  , ⟨"kissat_skip_ws1", [i64, i64], [.bool], kissatSkipWs1Spec, true⟩
  , ⟨"kissat_read_nat", [i64, i64], [.bool], kissatReadNatSpec, true⟩
  , ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩
  , ⟨"kissat_next_lit", [i64, i64], [i64], kissatNextLitSpec, true⟩
  , ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩
  , ⟨"plain_isqrt", [i64], [i64], plainIsqrtSpec, true⟩
  , ⟨"plain_ilog10", [i64], [i64], plainIlog10Spec, true⟩
  , ⟨"plain_arena_next", [i64, i32], [i32], plainArenaNextSpec, true⟩
  , ⟨"plain_alloc_cl", [i64, i32, i32, .bool], [i64], plainAllocClSpec, true⟩
  , ⟨"plain_wstack_defrag", [i64], [], plainWstackDefragSpec, true⟩
  , ⟨"plain_watch_push", [i64, i32, i32, i32, i32], [.bool], plainWatchPushSpec, true⟩
  , ⟨"plain_heap_up", [i64, i32], [], plainHeapUpSpec, true⟩
  , ⟨"plain_heap_down", [i64, i32], [], plainHeapDownSpec, true⟩
  , ⟨"plain_heap_push", [i64, i32], [], plainHeapPushSpec, true⟩
  , ⟨"plain_heap_pop", [i64], [i64], plainHeapPopSpec, true⟩
  , ⟨"plain_rescale", [i64], [], plainRescaleSpec, true⟩
  , ⟨"plain_bump_var", [i64, i32], [], plainBumpVarSpec, true⟩
  , ⟨"plain_bump_decay", [i64], [], plainBumpDecaySpec, true⟩
  , ⟨"plain_queue_mtf", [i64, i32], [], plainQueueMtfSpec, true⟩
  , ⟨"plain_tick_rel", [i64], [], plainTickRelSpec, true⟩
  , ⟨"plain_ema_update", [i64, i64], [], plainEmaUpdateSpec, true⟩
  , ⟨"plain_assign", [i64, i32, i32], [], plainAssignSpec, true⟩
  , ⟨"plain_backtrack", [i64, i64], [], plainBacktrackSpec, true⟩
  , ⟨"plain_add_clause", [i64, i32, i32, .bool], [i64], plainAddClauseSpec, true⟩
  , ⟨"plain_zero_tables", [i64], [], plainZeroTablesSpec, true⟩
  , ⟨"plain_init_state", [i64, i64, i64, i64, i64], [.bool], plainInitStateSpec, true⟩
  , ⟨"plain_skip_cl", [i64, i64], [.bool], plainSkipClSpec, true⟩
  , ⟨"plain_ingest_cl", [i64, i64], [i64], plainIngestClSpec, true⟩
  , ⟨"plain_parse_body", [i64, i64], [i64], plainParseBodySpec, true⟩
  , ⟨"plain_find_repl", [i64, i64], [i64], plainFindReplSpec, true⟩
  , ⟨"plain_prop_lit", [i64, i32], [.bool], plainPropLitSpec, true⟩
  , ⟨"plain_propagate", [i64], [i64], plainPropagateSpec, true⟩
  , ⟨"plain_recompute_tiers", [i64], [], plainRecomputeTiersSpec, true⟩
  , ⟨"plain_mark_reasons", [i64, .bool], [], plainMarkReasonsSpec, true⟩
  , ⟨"plain_red_less", [i64, i32, i32], [.bool], plainRedLessSpec, true⟩
  , ⟨"plain_sort_reds", [i64, i64], [], plainSortRedsSpec, true⟩
  , ⟨"plain_lit_rank", [i64, i64, i32], [i64], plainLitRankSpec, true⟩
  , ⟨"plain_sweep", [i64], [i64], plainSweepSpec, true⟩
  , ⟨"plain_reduce", [i64, .bool], [i64], plainReduceSpec, true⟩
  , ⟨"plain_analyze_lit", [i64, i32, i32], [.bool], plainAnalyzeLitSpec, true⟩
  , ⟨"plain_analyze_rsn", [i64, i32, i32], [.bool], plainAnalyzeRsnSpec, true⟩
  , ⟨"plain_clear_marks", [i64, i64], [], plainClearMarksSpec, true⟩
  , ⟨"plain_min_mark", [i64, i32, i8], [], plainMinMarkSpec, true⟩
  , ⟨"plain_min_lit", [i64, i32], [.bool], plainMinLitSpec, true⟩
  , ⟨"plain_tmp_less", [i64, i64, i32, i32], [.bool], plainTmpLessSpec, true⟩
  , ⟨"plain_sort_tmp", [i64], [], plainSortTmpSpec, true⟩
  , ⟨"plain_shrink_blk", [i64, i64, i64, i32, i64], [], plainShrinkBlkSpec, true⟩
  , ⟨"plain_min_shrink", [i64], [], plainMinShrinkSpec, true⟩
  , ⟨"plain_analyze", [i64], [i64], plainAnalyzeSpec, true⟩
  , ⟨"plain_decide", [i64], [i64], plainDecideSpec, true⟩
  , ⟨"plain_rephase", [i64], [], plainRephaseSpec, true⟩
  , ⟨"plain_switch_mode", [i64], [], plainSwitchModeSpec, true⟩
  , ⟨"plain_restart_due", [i64], [i64], plainRestartDueSpec, true⟩
  , ⟨"plain_lucky_scan", [i64, .bool, .bool], [i64], plainLuckyScanSpec, true⟩
  , ⟨"plain_lucky", [i64], [i64], plainLuckySpec, true⟩
  , ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], mainSpec, true⟩
  ]

/-- Parameterized specification environment covering all 59 functions in `plainFns`. -/
def mkPlainEnv (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : Env :=
  Env.ofTable (plainSpecTable mainSpec)

/-- Headline 59-function specification environment for `plainModule`. -/
def plainEnv : Env := mkPlainEnv plainSolveBytesSpec

theorem plainSpecTable_noExit (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ e ∈ plainSpecTable mainSpec, e.noExit = true := by
  intro e he
  simp only [plainSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    exact congrArg SpecEntry.noExit h

theorem plainSpecTable_sigs (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (plainSpecTable mainSpec).map (fun e => (e.name, e.as, e.rs)) =
      plainFns.map (fun f => (f.name, f.as, f.rs)) := rfl

end LeanQbe.T.Examples.Kissat.Plain
