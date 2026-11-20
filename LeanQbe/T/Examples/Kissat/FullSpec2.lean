module

public import LeanQbe.T.Examples.Kissat.FullSpec1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Per-Function UNSAT-Only `Spec` Contracts (`Full1` & `Full2`, 89 fns)

Defines exact UNSAT-only `Spec` contracts for all `51` functions in `full1_fns` and all `38`
functions in `full2_fns` (`89` functions total; zero SAT/model-reconstruction proofs):
1. Pure / arithmetic / `fullSafetySlice` / `fullExtendSlice` helpers (`28` fns).
2. Arena, watch-stack, chronological trail, initialization, and DIMACS ingestion (`21` fns,
   carrying `UnitUnsatTrace` for non-vacuous UNSAT, strictly UNSAT-only).
3. Chronological BCP, reason marking, `full_arena_sweep`, `full_reduce`, 1UIP/OTFS conflict
   analysis, clause minimization & block shrinking, decision, warmup, rephase, restart (`40` fns).
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

/-! ## 1. Shared `fullSafetySlice` templates & `Full1` arithmetic / arena / watch specs -/

/-- Max-heap property outside `[0 ..< start)` on `ws[0 ..< n)` keyed by `wvec[2 * l]`. -/
def FullWsortMaxHeap (wvec ws : List (BitVec 32)) (lo n : Nat) : Prop :=
  ∀ i, lo ≤ i → i < n →
    let p := (wvec[2 * (ws[i]?.getD 0#32).toNat]?.getD 0#32).toNat
    (2 * i + 1 < n → (wvec[2 * (ws[2 * i + 1]?.getD 0#32).toNat]?.getD 0#32).toNat ≤ p) ∧
    (2 * i + 2 < n → (wvec[2 * (ws[2 * i + 2]?.getD 0#32).toNat]?.getD 0#32).toNat ≤ p)

/-- Comparator matching `full_tmp_less(lvl, tpos, a, b)`. -/
def fullTmpKeyLt (lvl tpos : List (BitVec 32)) (a b : BitVec 32) : Bool :=
  let la := (lvl[a.toNat / 2]?.getD 0#32).toNat
  let lb := (lvl[b.toNat / 2]?.getD 0#32).toNat
  decide (la < lb ∨ (la = lb ∧ (tpos[a.toNat / 2]?.getD 0#32).toNat <
    (tpos[b.toNat / 2]?.getD 0#32).toNat))

/-- Max-heap property on `tmp[1 + lo ..< 1 + n)` ordered by `fullTmpKeyLt`. -/
def FullTmpMaxHeap (tmp lvl tpos : List (BitVec 32)) (lo n : Nat) : Prop :=
  ∀ i, lo ≤ i → i < n →
    let p := tmp[1 + i]?.getD 0#32
    (2 * i + 1 < n → fullTmpKeyLt lvl tpos p (tmp[1 + (2 * i + 1)]?.getD 0#32) = false) ∧
    (2 * i + 2 < n → fullTmpKeyLt lvl tpos p (tmp[1 + (2 * i + 2)]?.getD 0#32) = false)

/-- Shared `fullSafetySlice` contract `(h) -> ()` preserving `FullState.core`, `LengthsOk`, and
`FullProbeScratchPres`. -/
def fullSafetyVoidSpec : Spec [i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullProbeScratchPres s s')

/-- Shared `fullSafetySlice` contract `(h, v) -> ()` preserving `FullState.core`, `LengthsOk`,
and `FullProbeScratchPres`. -/
def fullSafetyVarVoidSpec : Spec [i64, i32] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _v, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullProbeScratchPres s s')

def fullIsqrtSpec : Spec [i64] [i64] := fun (x, ()) m Q _ =>
  ∀ r : BitVec 64,
    r.toNat * r.toNat ≤ x.toNat →
    (x.toNat ≤ 1 → r = x) →
    (2 ≤ x.toNat → 1 ≤ r.toNat ∧ x.toNat < (r.toNat + 1) * (r.toNat + 1)) →
    Q (r, ()) m

def fullIlog10Spec : Spec [i64] [i64] := fun (_x, ()) m Q _ =>
  ∀ r : BitVec 64, 1 ≤ r.toNat → r.toNat ≤ 19 → Q (r, ()) m

def fullRngNextSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => s'.scratch = { s.scratch with rng_state := s'.scratch.rng_state })

def fullArenaNextSpec : Spec [i64, i32] [i32] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    Q (BitVec.ofNat 32 (fullArenaNextOff s.core.arena s.core.arena_len cref.toNat), ()) m

def fullAllocClSpec : Spec [i64, i32, i32, .bool] [i64] := fun (h, sz, _glue, red, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    if c.arena_cap - s.core.arena_len < 3 + sz.toNat then
      Q (0xFFFFFFFF#64, ()) m
    else
      ∀ arena' m',
        let alen' := s.core.arena_len + 3 + sz.toNat
        let s' : FullState :=
          { s with core := { s.core with arena_len := alen', arena := arena' } }
        s'.LengthsOk c →
        (∀ i < s.core.arena_len, arena'[i]? = s.core.arena[i]?) →
        (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32 →
        (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00080000#32) = 0#32 →
        ((arena'[s.core.arena_len]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ↔ red = true) →
        (arena'[s.core.arena_len + 2]?.getD 0#32).toNat = sz.toNat →
        (FullMem c s' ⋆ R) m' →
        Q (BitVec.ofNat 64 s.core.arena_len, ()) m'

def fullWsortSiftSpec : Spec [i64, i64, i64, i64] [] :=
  fun (wvec_ptr, ws_ptr, start, n, ()) m Q _ =>
    ∃ (nlits : Nat) (wvec ws : List (BitVec 32)) (R : Mem 64 → Prop),
      2 * nlits ≤ wvec.length ∧ start.toNat < n.toNat ∧ n.toNat < 2 ^ 62 ∧ n.toNat ≤ ws.length ∧
      (∀ i < n.toNat, (ws[i]?.getD 0#32).toNat < nlits) ∧
      FullWsortMaxHeap wvec ws (start.toNat + 1) n.toNat ∧
      (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr ws ⋆ R) m ∧
      ∀ ws' m',
        ws'.length = ws.length → ws'.Perm ws →
        (∀ i, (i < start.toNat ∨ n.toNat ≤ i) → ws'[i]? = ws[i]?) →
        FullWsortMaxHeap wvec ws' start.toNat n.toNat →
        (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr ws' ⋆ R) m' → Q () m'

def fullWstackDefragSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wlen' wsort' m',
      let s' : FullState :=
        { s with
          core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
          scratch := { s.scratch with wsort := wsort' } }
      s'.LengthsOk c → WatchStackLayout s'.core → (1 ≤ s.core.wlen → 1 ≤ wlen') →
      (∀ l < 2 * s.core.cur_vars, fullWatchSize s' l = fullWatchSize s l ∧
        ∀ k < fullWatchSize s l,
          s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullWatchPushSpec : Spec [i64, i32, i32, i32, i32] [.bool] :=
  fun (h, lit, w0, w1, cnt, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧
      (cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32) ∧
      (cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) wvec' wstk' wlen' wusable' wsort' m',
        let s' : FullState :=
          { s with
            core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                  wusable := wusable' }
            scratch := { s.scratch with wsort := wsort' } }
        s'.LengthsOk c → WatchStackLayout s'.core →
        (∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
          fullWatchSize s' l = fullWatchSize s l ∧
          ∀ k < fullWatchSize s l,
            s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
        (ok = true →
          lit.toNat < 2 * s.core.cur_vars ∧ (cnt.toNat = 1 ∨ cnt.toNat = 2) ∧
          fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat + cnt.toNat ∧
          (∀ k < fullWatchSize s lit.toNat,
            s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
              s.core.wstk[fullWatchOff s lit.toNat + k]?) ∧
          s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat]? = some w0 ∧
          (cnt.toNat = 2 →
            s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat + 1]? = some w1)) →
        (ok = false →
          (lit.toNat < 2 * s.core.cur_vars →
            fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat ∧
            ∀ k < fullWatchSize s lit.toNat,
              s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
                s.core.wstk[fullWatchOff s lit.toNat + k]?) ∧
          (2 * s.core.cur_vars ≤ lit.toNat ∨ (cnt.toNat ≠ 1 ∧ cnt.toNat ≠ 2) ∨
            s' = s ∨ wusable' = 0#64)) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-! ## 2. `Full1` VSIDS / VMTF / Luby / EMA heuristics (`fullSafetySlice`) -/

abbrev fullHeapUpSpec := fullSafetyVarVoidSpec
abbrev fullHeapPushSpec := fullSafetyVarVoidSpec
abbrev fullRescaleSpec := fullSafetyVoidSpec
abbrev fullBumpVarSpec := fullSafetyVarVoidSpec
abbrev fullBumpDecaySpec := fullSafetyVoidSpec
abbrev fullQueueRenumberSpec := fullSafetyVoidSpec
abbrev fullQueueMtfSpec := fullSafetyVarVoidSpec
abbrev fullTickRelSpec := fullSafetyVoidSpec
abbrev fullSaveTargetBestSpec := fullSafetyVoidSpec
abbrev fullRecomputeTiersSpec := fullSafetyVoidSpec

def fullHeapDownSpec : Spec [i64, i32] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _v, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => s'.scratch.heap_len = s.scratch.heap_len ∧ FullProbeScratchPres s s')

def fullHeapPopSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ (r, ()) s s' =>
      (r = 0xFFFFFFFF#64 ∨ r.toNat < s.core.cur_vars) ∧
      (0 < s.scratch.heap_len ∧ s.scratch.heap_len ≤ s.core.cur_vars →
        s'.scratch.heap_len = s.scratch.heap_len - 1) ∧
      FullProbeScratchPres s s')

def fullEmaUpdateSpec : Spec [i64, i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _glue, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullProbeScratchPres s s')

/-! ## 3. `Full1` trail, clause addition, initialization & DIMACS ingestion -/

def fullAssignLvlSpec : Spec [i64, i32, i32, i32] [] :=
  fun (h, lit, rsn, alvl, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      if s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
          s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8 then
        Q () m
      else
        let v := lit.toNat / 2
        let rsn' := if alvl = 0#32 then 0xFFFFFFFF#32 else rsn
        let unfl' := if alvl = 0#32 then s.core.unflushed + 1#64 else s.core.unflushed
        ∀ flags' unass' phases' m',
          flags'.length = c.max_vars → phases'.length = c.max_vars →
          let s' : FullState :=
            { s with
              core :=
                { s.core with
                  vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                  flags := flags', lvl := s.core.lvl.set v alvl, rsns := s.core.rsns.set v rsn'
                  trl := s.core.trl.set s.core.trail_end lit
                  trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
                  trail_end := s.core.trail_end + 1
                  unassigned := unass', unflushed := unfl' }
              scratch := { s.scratch with phases := phases' } }
          (FullMem c s' ⋆ R) m' → Q () m'

def fullAssignSpec : Spec [i64, i32, i32] [] := fun (h, lit, rsn, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level < 2 ^ 32 ∧ (FullMem c s ⋆ R) m ∧
    if s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
        s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8 then
      Q () m
    else
      let v := lit.toNat / 2
      let rsn' := if s.core.cur_level = 0 then 0xFFFFFFFF#32 else rsn
      let unfl' := if s.core.cur_level = 0 then s.core.unflushed + 1#64 else s.core.unflushed
      ∀ flags' unass' phases' m',
        flags'.length = c.max_vars → phases'.length = c.max_vars →
        let s' : FullState :=
          { s with
            core :=
              { s.core with
                vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                flags := flags', lvl := s.core.lvl.set v (BitVec.ofNat 32 s.core.cur_level)
                rsns := s.core.rsns.set v rsn', trl := s.core.trl.set s.core.trail_end lit
                trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
                trail_end := s.core.trail_end + 1
                unassigned := unass', unflushed := unfl' }
            scratch := { s.scratch with phases := phases' } }
        (FullMem c s' ⋆ R) m' → Q () m'

def fullBacktrackSpec : Spec [i64, i64] [] := fun (h, target_lvl, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level < 2 ^ 64 ∧
    (target_lvl.toNat < s.core.cur_level → target_lvl.toNat < c.max_vars) ∧
    (∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                                trail_pos := tp', trail_end := te', propagated := prop',
                                cur_level := cl', unassigned := unass' }
          scratch := sc' }
      s'.LengthsOk c → te' ≤ s.core.trail_end → prop' ≤ te' →
      cl' = min s.core.cur_level target_lvl.toNat → FullProbeScratchPres s s' →
      sc'.shrink_stk = s.scratch.shrink_stk →
      (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      ((∃ F0 F_cur, FullWitnessInv c F0 F_cur s.core ∨ FullOtfsWitnessInv c F0 F_cur s.core) →
        (∀ l < 2 * s.core.cur_vars,
          vals'[l]?.getD 0#8 =
            if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat then
              s.core.vals[l]?.getD 0#8 else 0#8) ∧
        (∀ v < s.core.cur_vars,
          lvl'[v]?.getD 0#32 =
            if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat then
              s.core.lvl[v]?.getD 0#32 else 0#32)) →
      (∀ F0 F_cur, FullWitnessInv c F0 F_cur s.core → target_lvl.toNat ≤ s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (∀ F0 F_cur, FullOtfsWitnessInv c F0 F_cur s.core → target_lvl.toNat < s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullAddClauseSpec : Spec [i64, i32, i32, .bool] [i64] :=
  fun (h, len, _glue, _red, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ s.core.dense_mode = 0#64 ∧
      len.toNat ≤ c.max_vars ∧
      (2 ≤ len.toNat →
        (∀ l ∈ (s.core.tmp.take len.toNat).map BitVec.toNat, l < 2 * s.core.cur_vars) ∧
        ((s.core.tmp.take len.toNat).map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.core.tmp.take len.toNat).map BitVec.toNat))) ∧
      (FullMem c s ⋆ R) m ∧
      if len.toNat < 2 then
        Q (0xFFFFFFFF#64, ()) m
      else if len.toNat = 2 then
        ∀ r wvec' wstk' wlen' wusable' nb' wsort' m',
          let s' : FullState :=
            { s with
              core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                    wusable := wusable', num_binary := nb' }
              scratch := { s.scratch with wsort := wsort' } }
          (r = 0xFFFFFFFF#64 ∨ r = 0xFFFFFFFE#64) →
          s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → (FullMem c s' ⋆ R) m' → Q (r, ()) m'
      else
        ∀ r arena' alen' wvec' wstk' wlen' wusable' fred' ni' nr' wsort' m',
          let s' : FullState :=
            { s with
              core := { s.core with arena := arena', arena_len := alen', wvec := wvec',
                                    wstk := wstk', wlen := wlen', wusable := wusable',
                                    first_reducible := fred', num_irred := ni',
                                    num_redundant := nr' }
              scratch := { s.scratch with wsort := wsort' } }
          (r = 0xFFFFFFFF#64 ∨ r = BitVec.ofNat 64 s.core.arena_len) →
          s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
          (∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s') →
          (FullArenaVarsNodup s → FullArenaVarsNodup s') →
          (r = BitVec.ofNat 64 s.core.arena_len →
            alen' = s.core.arena_len + 3 + len.toNat ∧
            s.core.arena_len ∈ fullArenaClauseRefs s' ∧
            fullArenaClauseGarb s' s.core.arena_len = false ∧
            fullArenaClauseLits s' s.core.arena_len =
              (s.core.tmp.take len.toNat).map BitVec.toNat) →
          (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullZeroTables1Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ wstk' mstk' repr' sc' m',
      wstk'.length = c.wcap → mstk'.length = 2 * c.minDepth → repr'.length = 2 * c.max_vars →
      sc'.LengthsOk c → sc'.extend_len = s.scratch.extend_len →
      (∀ i < 16, sc'.last_learned[i]?.getD 0#32 = 0xFFFFFFFF#32) →
      let s' : FullState :=
        { s with
          core := { s.core with vals := List.replicate (2 * c.max_vars) 0#8
                                lit_mark := List.replicate (2 * c.max_vars) 0#8
                                wvec := List.replicate (4 * c.max_vars) 0#32
                                wstk := wstk', min_stk := mstk', repr := repr' }
          scratch := sc' }
      (FullMem c s' ⋆ R) m' → Q () m'

def fullZeroTables2Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ flags' fdec' sc' m',
      flags'.length = c.max_vars → fdec'.length = c.max_vars + 1 →
      sc'.LengthsOk c → FullExtScratchPres s { s with scratch := sc' } →
      let s' : FullState :=
        { s with
          core := { s.core with mrk := List.replicate c.max_vars 0#8
                                flags := flags'
                                lvl := List.replicate c.max_vars 0#32
                                rsns := List.replicate c.max_vars 0xFFFFFFFF#32
                                frame_trail := List.replicate (c.max_vars + 1) 0#32
                                frame_dec := fdec' }
          scratch := sc' }
      (FullMem c s' ⋆ R) m' → Q () m'

def fullFixedBytesSpec : Spec [i64] [i64] := fun (max_v, ()) m Q _ =>
  max_v.toNat < 2 * dimacsBound ∧ Q (BitVec.ofNat 64 (fullFixedBytes max_v.toNat), ()) m

def fullInitPtrsSpec : Spec [i64, i64, i64] [] := fun (h, hdr_addr, max_v, ()) m Q _ =>
  ∃ (ws : List (BitVec 64)) (R : Mem 64 → Prop),
    h = hdr_addr ∧ ws.length = 140 ∧ max_v.toNat < 2 * dimacsBound ∧
    hdr_addr.toNat + fullFixedBytes max_v.toNat < 2 ^ 64 ∧
    (array64 (hdr_addr + 32) ws ⋆ R) m ∧
    ∀ ws' m', ws'.length = 140 →
      (∀ (c : FullCfg), c.hdr = hdr_addr → c.max_vars = max_v.toNat →
        ws'[4]? = some c.pVals ∧ ws'[5]? = some c.pMark ∧ ws'[6]? = some c.pLevel ∧
        ws'[7]? = some c.pReason ∧ ws'[8]? = some c.pTrail ∧ ws'[9]? = some c.pWvec ∧
        ws'[10]? = some c.pArena ∧ ws'[13]? = some c.pTmp ∧ ws'[21]? = some c.pHeap ∧
        ws'[22]? = some c.pPos ∧ ws'[23]? = some c.pScore ∧ ws'[24]? = some c.pPhases ∧
        ws'[25]? = some c.pMinStk ∧ ws'[26]? = some c.pMinClr ∧
        ws'[29]? = some (BitVec.ofNat 64 c.minDepth) ∧ ws'[41]? = some c.pTrailPos ∧
        ws'[42]? = some c.pQPrev ∧ ws'[43]? = some c.pQNext ∧ ws'[44]? = some c.pQStamp ∧
        ws'[45]? = some c.pPhasesTarget ∧ ws'[46]? = some c.pPhasesBest ∧
        ws'[47]? = some c.pWsort ∧ ws'[48]? = some c.pShrinkStk ∧ ws'[50]? = some c.pGlueUsed ∧
        ws'[96]? = some c.pFlags ∧ ws'[97]? = some c.pLitMark ∧ ws'[98]? = some c.pRepr ∧
        ws'[99]? = some c.pSimSig ∧ ws'[100]? = some c.pFrameTrail ∧
        ws'[101]? = some c.pFrameDec ∧ ws'[102]? = some c.pWorkStk1 ∧
        ws'[103]? = some c.pWorkStk2 ∧ ws'[104]? = some c.pTarjanMark ∧
        ws'[105]? = some c.pTarjanReach ∧ ws'[106]? = some c.pWalkVals ∧
        ws'[107]? = some c.pWalkBest ∧ ws'[113]? = some c.pLastLearned) →
      (∀ i ∈ [0, 1, 11, 12, 49, 51, 52, 108, 109, 111, 112], ws'[i]? = ws[i]?) →
      (array64 (hdr_addr + 32) ws' ⋆ R) m' → Q () m'

def fullInitHdrSpec : Spec [i64, i64, i64, i64] [] := fun (h, mv, max_v, fuel, ()) m Q _ =>
  ∃ (c : FullCfg) (ws : List (BitVec 64)) (R : Mem 64 → Prop),
    h = c.hdr ∧ mv = BitVec.ofNat 64 c.mv ∧ max_v = BitVec.ofNat 64 c.max_vars ∧
    ws.length = 140 ∧
    (∀ (s0 : FullState),
      ∀ i ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
              41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
              102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113],
        ws[i]? = (hdrTailWords c s0)[i]?) ∧
    (array64 (c.hdr + 32) ws ⋆ R) m ∧
    ∀ (s : FullState) m',
      s.core.cur_vars = c.mv → s.core.arena_len = 0 → s.core.wlen = 1 →
      s.core.trail_end = 0 → s.core.propagated = 0 → s.core.cur_level = 0 →
      s.core.tmp_len = 0 → s.core.fuel = fuel → s.core.unflushed = 0#64 →
      s.core.probing = 0#64 → s.core.min_clr_len = 0 → s.core.min_clr_full = 0#64 →
      s.core.oom = 0#64 → s.core.dense_mode = 0#64 → s.core.inconsistent = 0#64 →
      s.scratch.extend_len = 0 →
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ R) m' → Q () m'

def fullCalcMaxVSpec : Spec [i64, i64, i64, i64] [i64] := fun (avail, mv, nc, f0, ()) m Q _ =>
  mv.toNat < dimacsBound ∧ nc.toNat < dimacsBound ∧
  f0.toNat = fullFixedBytes mv.toNat ∧ f0.toNat + nc.toNat * 40 + 136 ≤ avail.toNat ∧
  ∀ r : BitVec 64,
    mv.toNat ≤ r.toNat → r.toNat < 2 * dimacsBound →
    fullFixedBytes r.toNat + nc.toNat * 40 + 136 ≤ avail.toNat →
    Q (r, ()) m

def fullCalcExtCapSpec : Spec [i64] [i64] := fun (rem, ()) m Q _ =>
  ∀ r : BitVec 64,
    r.toNat ≤ 131072 → (rem.toNat < 8192 → r = 0#64) → 4 * r.toNat ≤ rem.toNat / 8 →
    Q (r, ()) m

def fullCalcScrCapSpec : Spec [i64] [i64] := fun (rem, ()) m Q _ =>
  ∀ r : BitVec 64,
    r.toNat ≤ 32768 → (rem.toNat < 8192 → r = 0#64) → 4 * r.toNat ≤ rem.toNat / 4 →
    Q (r, ()) m

def fullInitArenasSpec : Spec [i64, i64, i64, i64] [] :=
  fun (h, hdr_addr, max_v, avail_dyn, ()) m Q _ =>
    ∃ (ws : List (BitVec 64)) (dcap ecap scap : Nat) (R : Mem 64 → Prop),
      h = hdr_addr ∧ ws.length = 140 ∧ max_v.toNat < 2 * dimacsBound ∧
      dcap < dimacsBound ∧ ecap < dimacsBound ∧ scap < dimacsBound ∧
      ws[52]? = some (BitVec.ofNat 64 dcap) ∧ ws[109]? = some (BitVec.ofNat 64 ecap) ∧
      ws[112]? = some (BitVec.ofNat 64 scap) ∧
      hdr_addr.toNat + fullFixedBytes max_v.toNat + avail_dyn.toNat +
        12 * dcap + 4 * ecap + 4 * scap < 2 ^ 64 ∧
      (array64 (hdr_addr + 32) ws ⋆ R) m ∧
      ∀ (acap wcap rcap : Nat) (ws' : List (BitVec 64)) m',
        ws'.length = 140 →
        acap < 2 * dimacsBound → wcap < 2 * dimacsBound → rcap < 2 * dimacsBound →
        4 * acap + 4 * wcap + 4 * rcap ≤ avail_dyn.toNat →
        (40 ≤ avail_dyn.toNat → 1 ≤ wcap) →
        (∀ (c : FullCfg), c.hdr = hdr_addr → c.max_vars = max_v.toNat →
          c.arena_cap = acap → c.wcap = wcap → c.delayed_cap = dcap → c.red_cap = rcap →
          c.extend_cap = ecap → c.scratch_cap = scap →
          ws'[0]? = some (BitVec.ofNat 64 c.arena_cap) ∧
          ws'[1]? = some (BitVec.ofNat 64 c.wcap) ∧
          ws'[4]? = some c.pVals ∧ ws'[5]? = some c.pMark ∧ ws'[6]? = some c.pLevel ∧
          ws'[7]? = some c.pReason ∧ ws'[8]? = some c.pTrail ∧ ws'[9]? = some c.pWvec ∧
          ws'[10]? = some c.pArena ∧ ws'[11]? = some c.pWstk ∧ ws'[12]? = some c.pDelayed ∧
          ws'[13]? = some c.pTmp ∧ ws'[21]? = some c.pHeap ∧ ws'[22]? = some c.pPos ∧
          ws'[23]? = some c.pScore ∧ ws'[24]? = some c.pPhases ∧ ws'[25]? = some c.pMinStk ∧
          ws'[26]? = some c.pMinClr ∧ ws'[29]? = some (BitVec.ofNat 64 c.minDepth) ∧
          ws'[41]? = some c.pTrailPos ∧ ws'[42]? = some c.pQPrev ∧ ws'[43]? = some c.pQNext ∧
          ws'[44]? = some c.pQStamp ∧ ws'[45]? = some c.pPhasesTarget ∧
          ws'[46]? = some c.pPhasesBest ∧ ws'[47]? = some c.pWsort ∧
          ws'[48]? = some c.pShrinkStk ∧ ws'[49]? = some c.pRedRefs ∧
          ws'[50]? = some c.pGlueUsed ∧ ws'[51]? = some (BitVec.ofNat 64 c.red_cap) ∧
          ws'[52]? = some (BitVec.ofNat 64 c.delayed_cap) ∧ ws'[96]? = some c.pFlags ∧
          ws'[97]? = some c.pLitMark ∧ ws'[98]? = some c.pRepr ∧ ws'[99]? = some c.pSimSig ∧
          ws'[100]? = some c.pFrameTrail ∧ ws'[101]? = some c.pFrameDec ∧
          ws'[102]? = some c.pWorkStk1 ∧ ws'[103]? = some c.pWorkStk2 ∧
          ws'[104]? = some c.pTarjanMark ∧ ws'[105]? = some c.pTarjanReach ∧
          ws'[106]? = some c.pWalkVals ∧ ws'[107]? = some c.pWalkBest ∧
          ws'[108]? = some c.pExtendStk ∧ ws'[109]? = some (BitVec.ofNat 64 c.extend_cap) ∧
          ws'[111]? = some c.pScratchBuf ∧ ws'[112]? = some (BitVec.ofNat 64 c.scratch_cap) ∧
          ws'[113]? = some c.pLastLearned) →
        (array64 (hdr_addr + 32) ws' ⋆ R) m' → Q () m'

def fullInitStateSpec : Spec [i64, i64, i64, i64, i64] [.bool] :=
  fun (cnf_ptr, cend, hdr_addr, avail, fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (R : Mem 64 → Prop),
      cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      hdr_addr.toNat + avail.toNat < 2 ^ 64 ∧
      1152 ≤ avail.toNat ∧
      (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail.toNat ⋆ R) m ∧
      (∀ m', (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail.toNat ⋆ R) m' →
        (∀ mv nc rest, parseHeader cnfBytes = some (mv, nc, rest) →
          avail.toNat < fullFixedBytes mv + nc * 40 + 136) →
        Q (false, ()) m') ∧
      (∀ (c : FullCfg) (s : FullState) (j : Nat) (rest : List UInt8) (m' : Mem 64),
        c.hdr = hdr_addr → c.avail = avail.toNat →
        parseHeader cnfBytes = some (c.mv, c.nc, rest) →
        j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        FullSparseInv c (shiftDownCnf CNF.empty) s →
        s.core.cur_vars = c.mv →
        s.core.d_cur = cnf_ptr + BitVec.ofNat 64 j →
        s.core.arena_len = 0 → s.core.wlen = 1 → s.core.trail_end = 0 →
        s.core.propagated = 0 → s.core.cur_level = 0 → s.core.fuel = fuel →
        s.core.unflushed = 0#64 → s.core.probing = 0#64 →
        s.core.min_clr_len = 0 → s.core.min_clr_full = 0#64 →
        s.core.oom = 0#64 → s.core.inconsistent = 0#64 →
        s.core.vals = List.replicate (2 * c.max_vars) 0#8 →
        s.core.wvec = List.replicate (4 * c.max_vars) 0#32 →
        s.core.mrk = List.replicate c.max_vars 0#8 →
        s.core.lit_mark = List.replicate (2 * c.max_vars) 0#8 →
        s.scratch.extend_len = 0 →
        (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R) m' →
        Q (true, ()) m')

def fullSkipClSpec : Spec [i64, i64] [.bool] := fun (cend, d, ()) m Q _ =>
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

def fullIngestClSpec : Spec [i64, i64] [i64] := fun (h, cend, ()) m Q _ =>
  ∃ (c : FullCfg) (accCnf : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (cnf_ptr : BitVec 64) (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ i0 ≤ cnfBytes.length ∧
    s.core.cur_vars = c.mv ∧ s.core.d_cur = cnf_ptr + BitVec.ofNat 64 i0 ∧
    s.core.cur_level = 0 ∧ FullSparseInvW c (shiftDownCnf accCnf) F_cur s ∧
    (shiftDownCnf accCnf).Entails (cnfOfClauses F_cur) ∧
    (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R) m ∧
    match parseClause c.mv (cnfBytes.drop i0) with
    | none =>
      ∀ s' m', s'.LengthsOk c → s'.core.fuel = s.core.fuel → s'.core.oom = s.core.oom →
        s'.core.probing = s.core.probing →
        (bytes cnf_ptr cnfBytes ⋆ FullMem c s' ⋆ R) m' → Q (0#64, ()) m'
    | some (cl, rest) =>
      ∀ r s' j m',
        (∀ lit ∈ cl.literals, 1 ≤ lit.1) →
        i0 < j → j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        s'.LengthsOk c → s'.core.cur_vars = c.mv →
        s'.core.d_cur = cnf_ptr + BitVec.ofNat 64 j →
        s'.core.cur_level = 0 → s'.core.fuel = s.core.fuel → s'.core.oom = s.core.oom →
        s'.core.probing = s.core.probing →
        (r = 1#64 ∨ r = 2#64 ∨ r = 3#64) →
        (r = 1#64 → ∃ F_cur', FullSparseInvW c (shiftDownCnf (accCnf.add cl)) F_cur' s' ∧
          (shiftDownCnf (accCnf.add cl)).Entails (cnfOfClauses F_cur')) →
        (r = 2#64 → (shiftDownCnf (accCnf.add cl)).Unsat) →
        (∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
          s.core.vals[l]?.getD 0#8 = 0#8 →
          r = 1#64 ∧
          (∀ k < 2 * c.mv, s'.core.vals[k]?.getD 0#8 =
            ((s.core.vals.set l 1#8).set (l ^^^ 1) 0xFF#8)[k]?.getD 0#8) ∧
          s'.core.trail_end = s.core.trail_end + 1 ∧ s'.core.propagated = s.core.propagated) →
        (∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
          s.core.vals[l]?.getD 0#8 = 0xFF#8 → r = 2#64) →
        (bytes cnf_ptr cnfBytes ⋆ FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullParseBodySpec : Spec [i64, i64] [i64] := fun (h, cend, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (cnf_ptr : BitVec 64) (cnfBytes : List UInt8)
    (i0 : Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ i0 ≤ cnfBytes.length ∧
    parseHeader cnfBytes = some (c.mv, c.nc, cnfBytes.drop i0) ∧
    s.core.cur_vars = c.mv ∧ s.core.d_cur = cnf_ptr + BitVec.ofNat 64 i0 ∧
    s.core.cur_level = 0 ∧ s.core.trail_end = 0 ∧ s.core.propagated = 0 ∧
    s.core.arena_len = 0 ∧ s.core.oom = 0#64 ∧ s.core.probing = 0#64 ∧
    s.core.inconsistent = 0#64 ∧
    s.core.vals = List.replicate (2 * c.max_vars) 0#8 ∧
    s.core.wvec = List.replicate (4 * c.max_vars) 0#32 ∧
    FullSparseInv c (shiftDownCnf CNF.empty) s ∧
    (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → s'.core.fuel = s.core.fuel →
      s'.core.oom = 0#64 → s'.core.probing = 0#64 →
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
      (r = 1#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        FullSparseInv c (shiftDownCnf cnf) s' ∧ s'.core.cur_level = 0) →
      (UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc → r = 20#64) →
      (bytes cnf_ptr cnfBytes ⋆ FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ## 4. `Full1` & `Full2` BCP, reason marking, `arena_sweep`, `reduce` -/

def fullFindReplSpec : Spec [i64, i64] [i64] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ cref.toNat + 3 ≤ s.core.arena_len ∧
    3 ≤ fullArenaClauseSize s cref.toNat ∧
    cref.toNat + 3 + fullArenaClauseSize s cref.toNat ≤ s.core.arena_len ∧
    (FullMem c s ⋆ R) m ∧
    ((∀ k, 2 ≤ k → k < fullArenaClauseSize s cref.toNat →
        let cand := (s.core.arena[cref.toNat + 3 + k]?.getD 0#32).toNat
        2 * s.core.cur_vars ≤ cand ∨
        ((s.core.vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = true) →
      Q (0xFFFFFFFF#64, ()) m) ∧
    (∀ (r : Nat) (m' : Mem 64),
      2 ≤ r → r < fullArenaClauseSize s cref.toNat →
      (let cand := (s.core.arena[cref.toNat + 3 + r]?.getD 0#32).toNat
       cand < 2 * s.core.cur_vars ∧
       ((s.core.vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = false) →
      (FullMem c { s with core :=
        { s.core with arena := s.core.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r) } } ⋆ R) m' →
      Q (BitVec.ofNat 64 r, ()) m')

def fullAssignLevelSpec : Spec [i64, i32, i32] [i32] := fun (h, cref, forced_lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCoreInv c F0 s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s cref.toNat = false ∧ (FullMem c s ⋆ R) m ∧
    ∀ r : BitVec 32,
      r.toNat ≤ s.core.cur_level →
      (∀ l ∈ fullArenaClauseLits s cref.toNat, l ≠ forced_lit.toNat →
        (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ r.toNat) →
      (0 < r.toNat → ∃ l ∈ fullArenaClauseLits s cref.toNat, l ≠ forced_lit.toNat ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat = r.toNat) →
      Q (r, ()) m

def fullPropLitSpec : Spec [i64, i32, i64] [.bool] := fun (h, _lit, ignore_ref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    s.core.dense_mode = 0#64 ∧ s.core.oom = 0#64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' arena' wstk' wlen' wu'
      ctype' cref' c0' c1' oom' ticks' wsort' phases' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                unassigned := unass', unflushed := unfl', wvec := wvec',
                                arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                                confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' }
          scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      (ok = false → oom' ≠ 0#64 ∨
        (FullConflictOkW F_cur s' ∧ (ctype' = 2#64 → cref' ≠ ignore_ref))) →
      (ok = true → oom' = 0#64 ∧ ctype' = s.core.confl_type) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullPropagateIgnoreSpec : Spec [i64, i64] [i64] := fun (h, ignore_ref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                propagated := prop', unassigned := unass', unflushed := unfl',
                                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                wusable := wu', fuel := fuel', confl_type := ctype',
                                confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                oom := oom' }
          scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ ctype' = s.core.confl_type ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s' ∧
        (ctype' = 2#64 → cref' ≠ ignore_ref)) →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullPropagateSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                propagated := prop', unassigned := unass', unflushed := unfl',
                                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                wusable := wu', fuel := fuel', confl_type := ctype',
                                confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                oom := oom' }
          scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s') →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullMarkReasonsSpec : Spec [i64, .bool] [] := fun (h, set_flag, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ arena' m',
      let s' : FullState := { s with core := { s.core with arena := arena' } }
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
        fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
        fullArenaClauseLits s' r = fullArenaClauseLits s r) →
      (set_flag = true → FullReasonsMarked s') →
      FullCoreInv c F0 s' → (FullMem c s' ⋆ R) m' → Q () m'

def fullRedLessSpec : Spec [i64, i32, i32] [.bool] := fun (ar_ptr, a, b, ()) m Q _ =>
  ∃ (ar : List (BitVec 32)) (R : Mem 64 → Prop),
    a.toNat + 2 < ar.length ∧ b.toNat + 2 < ar.length ∧
    (array (t := i32) ar_ptr ar ⋆ R) m ∧ ∀ res : Bool, Q (res, ()) m

def fullRedSiftSpec : Spec [i64, i64, i64, i64] [] := fun (ar_ptr, rr_ptr, start, n, ()) m Q _ =>
  ∃ (ar rr : List (BitVec 32)) (R : Mem 64 → Prop),
    start.toNat < n.toNat ∧ n.toNat < 2 ^ 62 ∧ n.toNat ≤ rr.length ∧
    (∀ k < n.toNat, (rr[k]?.getD 0#32).toNat + 2 < ar.length) ∧
    (array (t := i32) ar_ptr ar ⋆ array (t := i32) rr_ptr rr ⋆ R) m ∧
    ∀ rr' m', rr'.length = rr.length → rr'.Perm rr →
      (∀ k, (k < start.toNat ∨ n.toNat ≤ k) → rr'[k]? = rr[k]?) →
      (array (t := i32) ar_ptr ar ⋆ array (t := i32) rr_ptr rr' ⋆ R) m' → Q () m'

def fullSortRedsSpec : Spec [i64, i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, n, ()) s => h = c.hdr ∧ n.toNat ≤ c.red_cap ∧
      ∀ k < n.toNat, (s.scratch.red_refs[k]?.getD 0#32).toNat + 2 < c.arena_cap)
    (fun _ (_, n, ()) _ s s' => FullExtScratchPres s s' ∧
      ∀ k < n.toNat, ∃ j < n.toNat, s'.scratch.red_refs[k]? = s.scratch.red_refs[j]?)

def fullLitRankSpec : Spec [i64, i64, i32] [i64] := fun (vals_ptr, lvl_ptr, l, ()) m Q _ =>
  ∃ (vals : List (BitVec 8)) (lvl : List (BitVec 32)) (R : Mem 64 → Prop),
    l.toNat < vals.length ∧ l.toNat / 2 < lvl.length ∧
    (array (t := i8) vals_ptr vals ⋆ array (t := i32) lvl_ptr lvl ⋆ R) m ∧
    ∀ r : BitVec 64, Q (r, ()) m

def fullUnwatchLargeSpec : Spec [i64, i32, i32] [] := fun (h, _lit, _cref, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wu' m',
      let s' : FullState :=
        { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } }
      s'.LengthsOk c → WatchStackLayout s'.core →
      (∀ F_cur, ModeWatchesInv F_cur s.core → ModeWatchesInv F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullSweepBinsSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wlen' wu' nb' wsort' m',
      let s' : FullState :=
        { s with
          core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
                                num_binary := nb' }
          scratch := { s.scratch with wsort := wsort' } }
      s'.LengthsOk c → FullBinOnlyWatchesInv F_cur s'.core → FullWitnessInv c F0 F_cur s'.core →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullSweepCopySpec : Spec [i64, i64, i64, i32, .bool] [i64] :=
  fun (h, src, dst, old_sz, at_root, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧
      dst.toNat ≤ src.toNat ∧ 3 ≤ old_sz.toNat ∧
      src.toNat + 3 + old_sz.toNat ≤ s.core.arena_len ∧
      at_root = decide (s.core.cur_level = 0) ∧
      (∀ j < old_sz.toNat,
        (s.core.arena[src.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (at_root = true →
        FullWitnessInv c F0 F_cur { s.core with arena_len := dst.toNat } ∧
        FullBinOnlyWatchesInv F_cur s.core ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause (((s.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat))) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r arena' vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb'
        oom' ph' wsort' m',
        let s' : FullState :=
          { s with
            core := { s.core with arena := arena', vals := vals', flags := flags', lvl := lvl',
                                  rsns := rsns', trl := trl', trail_pos := tp', trail_end := te',
                                  unassigned := unass', unflushed := unfl', wvec := wvec',
                                  wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                                  oom := oom' }
            scratch := { s.scratch with phases := ph', wsort := wsort' } }
        s'.LengthsOk c →
        (∀ i, (i < dst.toNat + 3 ∨ dst.toNat + 3 + old_sz.toNat ≤ i) →
          arena'[i]? = s.core.arena[i]?) →
        (at_root = false →
          r = old_sz.setWidth 64 ∧ vals' = s.core.vals ∧ flags' = s.core.flags ∧
          lvl' = s.core.lvl ∧ rsns' = s.core.rsns ∧ trl' = s.core.trl ∧
          tp' = s.core.trail_pos ∧ te' = s.core.trail_end ∧ unass' = s.core.unassigned ∧
          unfl' = s.core.unflushed ∧ wvec' = s.core.wvec ∧ wstk' = s.core.wstk ∧
          wlen' = s.core.wlen ∧ wu' = s.core.wusable ∧ nb' = s.core.num_binary ∧
          oom' = s.core.oom ∧ ph' = s.scratch.phases ∧ wsort' = s.scratch.wsort ∧
          ∀ j < old_sz.toNat, arena'[dst.toNat + 3 + j]? = s.core.arena[src.toNat + 3 + j]?) →
        (at_root = true →
          FullWitnessInv c F0 F_cur { s'.core with arena_len := dst.toNat } ∧
          FullBinOnlyWatchesInv F_cur s'.core ∧ s.core.trail_end ≤ te' ∧
          (r = 0xFFFFFFFE#64 ∨ r = 0xFFFFFFFD#64 ∨ r = 1#64 ∨ r = 0xFFFFFFFF#64 ∨
            (3 ≤ r.toNat ∧ r.toNat ≤ old_sz.toNat)) ∧
          (r = 0xFFFFFFFE#64 → F0.Unsat) ∧ (r = 0xFFFFFFFD#64 → oom' ≠ 0#64) ∧
          (r ≠ 0xFFFFFFFD#64 → oom' = s.core.oom) ∧ (r = 1#64 → s.core.trail_end < te') ∧
          (3 ≤ r.toNat ∧ r.toNat ≤ old_sz.toNat →
            (∀ j < r.toNat, (arena'[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
            List.Sublist (((arena'.drop (dst.toNat + 3)).take r.toNat).map BitVec.toNat)
              (((s.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat) ∧
            (cnfOfClauses F_cur).EntailsClause
              (cnfClause (((arena'.drop (dst.toNat + 3)).take r.toNat).map BitVec.toNat)))) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullRewatchArenaSpec : Spec [i64, i64] [.bool] := fun (h, dst, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    s.core.dense_mode = 0#64 ∧ dst.toNat = s.core.arena_len ∧
    (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false ∧
      (fullArenaHdr s r &&& 0x00800000#32) = 0#32) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) arena' wvec' wstk' wlen' wu' oom' wsort' m',
      let s' : FullState :=
        { s with
          core := { s.core with arena := arena', wvec := wvec', wstk := wstk', wlen := wlen',
                                wusable := wu', oom := oom' }
          scratch := { s.scratch with wsort := wsort' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      (FullArenaVarsNodup s → FullArenaVarsNodup s') →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = false → oom' ≠ 0#64) → (ok = true → oom' = s.core.oom) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullArenaSweepSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullArenaVarsNodup s ∧
    s.core.dense_mode = 0#64 ∧ (0 < s.core.cur_level → FullReasonsMarked s) ∧ (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen' wu'
      fred' ni' nr' nb' oom' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                unassigned := unass', unflushed := unfl', wvec := wvec',
                                wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
                                wusable := wu', arena_garbage := 0#64, first_reducible := fred',
                                num_irred := ni', num_redundant := nr', num_binary := nb',
                                oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 3#64) →
      sc'.extend_len = s.scratch.extend_len → sc'.work_stk2 = s.scratch.work_stk2 →
      FullLastLearnedWf s' → FullWitnessInv c F0 F_cur s'.core → FullArenaVarsNodup s' →
      (r = 0#64 ∨ r = 1#64 → oom' = 0#64) →
      (0 < s.core.cur_level → r = 0#64 →
        vals' = s.core.vals ∧ lvl' = s.core.lvl ∧ trl' = s.core.trl ∧
        tp' = s.core.trail_pos ∧ te' = s.core.trail_end) →
      (r = 1#64 → s.core.cur_level = 0 ∧ s.core.trail_end < te') →
      (r = 2#64 → s.core.cur_level = 0 ∧ F0.Unsat) →
      (r = 3#64 → oom' ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullReduceSpec : Spec [i64, .bool] [i64] := fun (h, _force, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInvW c F0 F_cur s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_level ≤ s.core.cur_level → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.cur_vars = s.core.cur_vars → s'.core.tmp = s.core.tmp →
      s'.core.tmp_len = s.core.tmp_len → s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64) →
      (r = 1#64 → 0 < s'.core.cur_level →
        s'.core.cur_level = s.core.cur_level ∧ s'.core.vals = s.core.vals ∧
        s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
        s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ## 5. `Full2` 1UIP/OTFS analysis, minimization, block shrinking, decision, walk, extend -/

def fullAnalyzeLitSpec : Spec [i64, i32, i32] [.bool] := fun (h, lit, skip_var, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level < 2 ^ 32 ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
    s.core.tmp_cnt + 1 < 2 ^ 64 ∧ FullAnaMarksCov c s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' tmp' tc' tl' mcl' ws1' ant' res' m',
      let s' : FullState :=
        { s with
          core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                min_clr_len := mcl' }
          scratch := { s.scratch with work_stk1 := ws1', ant_sz := ant', res_sz := res' } }
      s'.LengthsOk c → FullAnaMarksCov c s' → s.core.tmp_len ≤ tl' → tl' ≤ s.core.tmp_len + 1 →
      tl' ≤ s.core.cur_vars → s.core.tmp_cnt ≤ tc' →
      tc' = s.core.tmp_cnt +
        (if lit.toNat / 2 < s.core.cur_vars ∧ s.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
            mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
            (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = s.core.cur_level
         then 1 else 0) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
        mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) →
      (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
        lit.toNat / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
        0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
        (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) →
      (∀ j, s.core.tmp_len ≤ j → j < tl' →
        (tmp'[j]?.getD 0#32).toNat = lit.toNat ∧ lit.toNat / 2 < s.core.cur_vars ∧
        lit.toNat / 2 ≠ skip_var.toNat ∧ s.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
        0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat < s.core.cur_level ∧
        mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8) →
      (ok = true → lit.toNat / 2 < s.core.cur_vars ∧
        (lit.toNat / 2 ≠ skip_var.toNat →
          (0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat →
            mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8) ∧
          (s.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 →
            (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
            (0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat →
              (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = s.core.cur_level →
              tc' = s.core.tmp_cnt + 1) ∧
            (0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat →
              (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat < s.core.cur_level →
              tl' = s.core.tmp_len + 1 ∧ tmp'[s.core.tmp_len]? = some lit)))) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullAnalyzeRsnSpec : Spec [i64, i32, i32] [.bool] := fun (h, rsn, skip_var, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut s.core ∧ FullAnaMarksCov c s ∧
    s.core.tmp_len ≤ s.core.cur_vars ∧ s.core.tmp_cnt + s.core.cur_vars + 1 < 2 ^ 64 ∧
    (rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ∈ fullArenaClauseRefs s) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' tmp' tc' tl' mcl' arena' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                min_clr_len := mcl', arena := arena' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s'.core → FullAnaMarksCov c s' →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      s.core.tmp_len ≤ tl' → tl' ≤ s.core.cur_vars → s.core.tmp_cnt ≤ tc' →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
        fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
        fullArenaClauseLits s' r = fullArenaClauseLits s r) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
        mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) →
      (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
        ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
          0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
          (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) →
      (∀ j, s.core.tmp_len ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        l ∈ fullRsnLits s rsn ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
        s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧
        0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧
        mrk'[l / 2]?.getD 0#8 ≠ 0#8) →
      (ok = true → rsn ≠ 0xFFFFFFFF#32 ∧
        ∀ l ∈ fullRsnLits s rsn, l / 2 < s.core.cur_vars ∧
          (l / 2 ≠ skip_var.toNat →
            (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
            (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
              (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
              (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
                (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
                ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧
                  (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullClearAnaSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ mrk' m', mrk'.length = c.max_vars →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 = 0#8) →
      (∀ i < s.core.min_clr_len, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars →
        mrk'[(s.scratch.work_stk1[i]?.getD 0#32).toNat]?.getD 0#8 = 0#8) →
      (FullAnaMarksCov c s → ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
      (FullMem c { s with core := { s.core with mrk := mrk', min_clr_len := 0 } } ⋆ R) m' → Q () m'

def fullBumpAnalyzedSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullAnaMarksCov c s ∧ (FullMem c s ⋆ R) m ∧
    ∀ mrk' mcl' sc' m',
      let s' : FullState :=
        { s with core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
      s'.LengthsOk c → FullAnaMarksCov c s' → FullExtScratchPres s s' →
      sc'.work_stk2 = s.scratch.work_stk2 →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullOtfsLargeSpec : Spec [i64, i32, i32] [.bool] := fun (h, cref, uip, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut idx_u : Nat) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut s.core ∧ FullArenaVarsNodup s ∧
    s.core.dense_mode = 0#64 ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s cref.toNat = false ∧ uip.toNat < 2 * s.core.cur_vars ∧
    idx_u < cut ∧ (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat ∧
    s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref ∧
    (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s.core.cur_level ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((fullArenaClauseLits s cref.toNat).filter fun l =>
        decide (l ≠ uip.toNat ∧ (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∨
          l = (s.core.arena[cref.toNat + 3]?.getD 0#32).toNat ∨
          l = (s.core.arena[cref.toNat + 4]?.getD 0#32).toNat)))) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) arena' wvec' wstk' wlen' wu' oom' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with arena := arena', wvec := wvec', wstk := wstk', wlen := wlen',
                                wusable := wu', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur idx_u s'.core → FullArenaVarsNodup s' →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = true → cref.toNat ∈ fullArenaClauseRefs s' ∧
        fullArenaClauseGarb s' cref.toNat = false ∧
        ∀ l ∈ fullArenaClauseLits s' cref.toNat, s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
          ((s'.core.lvl[l / 2]?.getD 0#32).toNat = s'.core.cur_level →
            ∃ m < idx_u, (s'.core.trl[m]?.getD 0#32).toNat = l ^^^ 1)) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullOtfsBinSpec : Spec [i64, i32, i32] [.bool] := fun (h, cref, uip, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut idx_u : Nat) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut s.core ∧ FullArenaVarsNodup s ∧
    s.core.dense_mode = 0#64 ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s cref.toNat = false ∧ uip.toNat < 2 * s.core.cur_vars ∧
    idx_u < cut ∧ (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat ∧
    s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref ∧
    (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s.core.cur_level ∧
    (∀ f0 f1 : BitVec 32,
      f0.toNat ∈ fullArenaClauseLits s cref.toNat → f1.toNat ∈ fullArenaClauseLits s cref.toNat →
      f0 ≠ uip → f1 ≠ uip → f0 ≠ f1 →
      0 < (s.core.lvl[f0.toNat / 2]?.getD 0#32).toNat →
      0 < (s.core.lvl[f1.toNat / 2]?.getD 0#32).toNat →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [f0.toNat, f1.toNat])) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) arena' ag' wvec' wstk' wlen' wu' nb' ctype' cr' c0' c1' oom' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with arena := arena', arena_garbage := ag', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                                confl_type := ctype', confl_ref := cr', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur idx_u s'.core → FullArenaVarsNodup s' →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = true → ctype' = 1#64 ∧ FullConflictOkCut F_cur idx_u s') →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullOtfsSubsumeSpec : Spec [i64, i32, i64, i64, .bool] [] :=
  fun (h, new_confl, old_ctype, old_cref, to_bin, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut s.core ∧ FullArenaVarsNodup s ∧
      (old_ctype = 2#64 → old_cref ≠ 0xFFFFFFFF#64 →
        old_cref.toNat ∈ fullArenaClauseRefs s ∧
        (to_bin = false → new_confl.toNat ∈ fullArenaClauseRefs s) ∧
        ∀ idx < s.core.trail_end,
          let v := (s.core.trl[idx]?.getD 0#32).toNat / 2
          let rsn := s.core.rsns[v]?.getD 0xFFFFFFFF#32
          (idx < cut ∨ (s.core.lvl[v]?.getD 0#32).toNat < s.core.cur_level) →
          rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ old_cref.toNat) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ arena' ag' ni' nr' m',
        let s' : FullState :=
          { s with core := { s.core with arena := arena', arena_garbage := ag',
                                         num_irred := ni', num_redundant := nr' } }
        s'.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s'.core → FullArenaVarsNodup s' →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseLits s' r = fullArenaClauseLits s r ∧
          (old_ctype = 2#64 → r ≠ old_cref.toNat →
            fullArenaClauseGarb s' r = fullArenaClauseGarb s r)) →
        (FullMem c s' ⋆ R) m' → Q () m'

/-- Minimization / block-shrinking mark invariant (`full_min_mark`, `full_min_lit`,
`full_shrink_lower`, `full_shrink_blk`, `full_min_shrink`), parameterized over `F_cur`. -/
structure FullMinMarkInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (keep : List Nat) : Prop where
  mrk_dom : ∀ v < c.max_vars, (s.core.mrk[v]?.getD 0#8 &&& 0xF1#8) = 0#8
  clr_cov : s.core.min_clr_full = 0#64 → ∀ v < c.max_vars,
    (s.core.mrk[v]?.getD 0#8 &&& 6#8) ≠ 0#8 →
    ∃ i < s.core.min_clr_len, (s.core.min_clr[i]?.getD 0#32).toNat = v
  rem_sound : ∀ idx < s.core.trail_end,
    let p := (s.core.trl[idx]?.getD 0#32).toNat
    (s.core.mrk[p / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 →
    (p ^^^ 1) ∈ keep ∨
      let rsn := s.core.rsns[p / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 ∧
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * s.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [p, ot]) ∧
        ∃ k < idx, (s.core.trl[k]?.getD 0#32).toNat = ot ^^^ 1 ∧
          ((s.core.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨
           (s.core.mrk[ot / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
      else
        rsn.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s rsn.toNat = false ∧
        ∀ q ∈ fullArenaClauseLits s rsn.toNat,
          q = p ∨ ∃ k < idx, (s.core.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
            ((s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨
             (s.core.mrk[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)

/-- State update of `full_min_mark(h, v, tag)`. -/
def fullMinMarkState (s : FullState) (v : Nat) (tag : BitVec 8) : FullState :=
  let cur := s.core.mrk[v]?.getD 0#8
  let mclr' := if cur = 0#8 ∧ s.core.min_clr_len < s.core.cur_vars then
                 s.core.min_clr.set s.core.min_clr_len (BitVec.ofNat 32 v)
               else s.core.min_clr
  let mcl' := if cur = 0#8 ∧ s.core.min_clr_len < s.core.cur_vars then
                s.core.min_clr_len + 1
              else s.core.min_clr_len
  let mcf' := if cur = 0#8 ∧ ¬ s.core.min_clr_len < s.core.cur_vars then 1#64
              else s.core.min_clr_full
  { s with core :=
    { s.core with mrk := s.core.mrk.set v (cur ||| tag),
                  min_clr := mclr', min_clr_len := mcl', min_clr_full := mcf' } }

def fullMinMarkSpec : Spec [i64, i32, i8] [] := fun (h, v, tag, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    let cur := s.core.mrk[v.toNat]?.getD 0#8
    if s.core.cur_vars ≤ v.toNat ∨ (cur &&& tag) ≠ 0#8 then
      Q () m
    else
      ∀ m', (FullMem c (fullMinMarkState s v.toNat tag) ⋆ R) m' → Q () m'

def fullMinLitSpec : Spec [i64, i32] [.bool] := fun (h, root_lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (keepSet : List Nat)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullMinMarkInv c F_cur s keepSet ∧
    root_lit.toNat < 2 * s.core.cur_vars ∧ s.core.vals[root_lit.toNat]?.getD 0#8 = 0xFF#8 ∧
    (∀ v < c.max_vars,
      (s.core.lvl[v]?.getD 0#32).toNat ≤ (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat →
      (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' mstk' mclr' mcl' mcf' m',
      let s' : FullState :=
        { s with core := { s.core with mrk := mrk', min_stk := mstk', min_clr := mclr',
                                       min_clr_len := mcl', min_clr_full := mcf' } }
      s'.LengthsOk c →
      (∀ v < c.max_vars,
        (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (∀ v < c.max_vars, (mrk'[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)) →
      FullMinMarkInv c F_cur s' keepSet →
      (ok = true →
        (∀ keep' : List Nat,
          (∀ l ∈ keepSet, l = root_lit.toNat ∨ l ∈ keep') → FullMinMarkInv c F_cur s' keep') ∧
        FullMinMarkInv c F_cur (fullMinMarkState s' (root_lit.toNat / 2) 2#8) keepSet) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullTmpLessSpec : Spec [i64, i64, i32, i32] [.bool] :=
  fun (lvl_ptr, tpos_ptr, a, b, ()) m Q _ =>
    ∃ (lvl tpos : List (BitVec 32)) (R : Mem 64 → Prop),
      a.toNat / 2 < lvl.length ∧ b.toNat / 2 < lvl.length ∧
      a.toNat / 2 < tpos.length ∧ b.toNat / 2 < tpos.length ∧
      (array (t := i32) lvl_ptr lvl ⋆ array (t := i32) tpos_ptr tpos ⋆ R) m ∧
      Q (fullTmpKeyLt lvl tpos a b, ()) m

def fullSortTmpSiftSpec : Spec [i64, i64, i64, i64, i64] [] :=
  fun (tmp_ptr, lvl_ptr, tpos_ptr, start, n, ()) m Q _ =>
    ∃ (tmp lvl tpos : List (BitVec 32)) (R : Mem 64 → Prop),
      start.toNat < n.toNat ∧ n.toNat < 2 ^ 60 ∧ 1 + n.toNat ≤ tmp.length ∧
      (∀ i < n.toNat, (tmp[1 + i]?.getD 0#32).toNat / 2 < lvl.length ∧
        (tmp[1 + i]?.getD 0#32).toNat / 2 < tpos.length) ∧
      FullTmpMaxHeap tmp lvl tpos (start.toNat + 1) n.toNat ∧
      (array (t := i32) tmp_ptr tmp ⋆ array (t := i32) lvl_ptr lvl ⋆
        array (t := i32) tpos_ptr tpos ⋆ R) m ∧
      ∀ tmp' m', tmp'.length = tmp.length → tmp'.Perm tmp →
        (∀ i, (i < 1 + start.toNat ∨ 1 + n.toNat ≤ i) → tmp'[i]? = tmp[i]?) →
        FullTmpMaxHeap tmp' lvl tpos start.toNat n.toNat →
        (array (t := i32) tmp_ptr tmp' ⋆ array (t := i32) lvl_ptr lvl ⋆
          array (t := i32) tpos_ptr tpos ⋆ R) m' → Q () m'

def fullSortTmpSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
    (∀ k, 1 ≤ k → k < s.core.tmp_len → (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tmp' m', tmp'.length = c.max_vars →
      (0 < s.core.tmp_len → tmp'[0]? = s.core.tmp[0]?) →
      (tmp'.take s.core.tmp_len).Perm (s.core.tmp.take s.core.tmp_len) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (FullMem c { s with core := { s.core with tmp := tmp' } } ⋆ R) m' → Q () m'

def fullShrinkLowerSpec : Spec [i64, i32, i32] [.bool] := fun (h, ot, ov, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (keepSet : List Nat)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullMinMarkInv c F_cur s keepSet ∧
    ov.toNat = ot.toNat / 2 ∧ ot.toNat < 2 * s.core.cur_vars ∧
    s.core.vals[ot.toNat]?.getD 0#8 = 0xFF#8 ∧
    (∀ v < c.max_vars,
      (s.core.lvl[v]?.getD 0#32).toNat ≤ (s.core.lvl[ov.toNat]?.getD 0#32).toNat →
      (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' mstk' mclr' mcl' mcf' m',
      let s' : FullState :=
        { s with core := { s.core with mrk := mrk', min_stk := mstk', min_clr := mclr',
                                       min_clr_len := mcl', min_clr_full := mcf' } }
      s'.LengthsOk c →
      (∀ v < c.max_vars,
        (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (∀ v < c.max_vars, (mrk'[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)) →
      FullMinMarkInv c F_cur s' keepSet →
      (ok = true → (mrk'[ov.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullShrinkBlkSpec : Spec [i64, i64, i64, i32, i64] [] :=
  fun (h, beg, end_b, blvl, max_tr, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullMinMarkInv c F_cur s
        (((s.core.tmp.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) ∧
      (∀ v < c.max_vars, (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
      1 ≤ beg.toNat ∧ beg.toNat < end_b.toNat ∧ end_b.toNat ≤ s.core.tmp_len ∧
      s.core.tmp_len ≤ s.core.cur_vars ∧ 0 < blvl.toNat ∧ blvl.toNat < s.core.cur_level ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause
        (((s.core.tmp.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) ∧
      (∀ k, beg.toNat ≤ k → k < end_b.toNat →
        let l := (s.core.tmp[k]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat = blvl.toNat ∧
        (s.core.trail_pos[l / 2]?.getD 0#32).toNat ≤ max_tr.toNat) ∧
      (∀ k < s.core.tmp_len, s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        let l := (s.core.tmp[k]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        (s.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ tmp' mrk' mstk' mclr' mcl' mcf' sstk' m',
        let s' : FullState :=
          { s with
            core := { s.core with tmp := tmp', mrk := mrk', min_stk := mstk', min_clr := mclr',
                                  min_clr_len := mcl', min_clr_full := mcf' }
            scratch := { s.scratch with shrink_stk := sstk' } }
        s'.LengthsOk c →
        FullMinMarkInv c F_cur s'
          (((tmp'.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) →
        (∀ v < c.max_vars, (mrk'[v]?.getD 0#8 &&& 8#8) = 0#8) →
        (∀ k < s.core.tmp_len, (k < beg.toNat ∨ end_b.toNat ≤ k) → tmp'[k]? = s.core.tmp[k]?) →
        (∀ k, beg.toNat ≤ k → k < end_b.toNat → tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
          (s.core.lvl[(tmp'[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat) →
        ((((tmp'.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map fun x => x.toNat / 2).Nodup ∨
          ¬ (((s.core.tmp.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map
            fun x => x.toNat / 2).Nodup) →
        (cnfOfClauses F_cur).EntailsClause (cnfClause
          (((tmp'.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) →
        (∀ k < s.core.tmp_len, tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
          let l := (tmp'[k]?.getD 0#32).toNat
          l < 2 * s.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
          (mrk'[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) →
        (FullMem c s' ⋆ R) m' → Q () m'

def fullMinShrinkSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullOtfsWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
    1 ≤ s.core.tmp_len ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
    ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) ∧
    (∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
    (∀ k, 1 ≤ k → k < s.core.tmp_len →
      let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tmp' tl' mrk' mstk' mclr' mcl' mcf' conf' llits' mrem' sstk' m',
      let s' : FullState :=
        { s with
          core := { s.core with tmp := tmp', tmp_len := tl', mrk := mrk', min_stk := mstk',
                                min_clr := mclr', min_clr_len := mcl', min_clr_full := mcf' }
          scratch := { s.scratch with conflicts := conf', learned_lits := llits',
                                      min_removed := mrem', shrink_stk := sstk' } }
      s'.LengthsOk c → FullOtfsWitnessInv c F0 F_cur s'.core → FullLitMarksClear c s' →
      1 ≤ tl' → tl' ≤ s.core.tmp_len → tmp'[0]? = s.core.tmp[0]? →
      ((tmp'.take tl').map fun x => x.toNat / 2).Nodup →
      (∀ j, 1 ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        0 < lv ∧ lv < s.core.cur_level ∧
        lv ≤ (s.core.lvl[(tmp'[tl' - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat)) →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullDetNewLevelSpec : Spec [i64, i64] [i64] := fun (h, jump, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ r : BitVec 64,
      (s.core.cur_level = 0 → r = 0#64) →
      (0 < s.core.cur_level → jump.toNat < s.core.cur_level →
        jump.toNat ≤ r.toNat ∧ r.toNat < s.core.cur_level) →
      Q (r, ()) m

def fullOneLitConflSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCutInvW c F0 F_cur cut s ∧ FullConflictOkCut F_cur cut s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (r = 2#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 0#64 → ∃ cut' ≤ s'.core.trail_end,
        FullCutInvW c F0 F_cur cut' s' ∧ 0 < s'.core.cur_level ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ FullConflictOkCut F_cur cut' s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullDeduce1uipSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCutInvW c F0 F_cur cut s ∧ 0 < s.core.cur_level ∧
    FullConflictOkCut F_cur cut s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
        ((s'.core.tmp.take s'.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
        (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
          l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
        (∀ k, 1 ≤ k → k < s'.core.tmp_len →
          let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
          0 < lv ∧ lv < s'.core.cur_level) ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s'.core.tmp.take s'.core.tmp_len).map BitVec.toNat))) →
      (r = 2#64 → ∃ cut' ≤ s'.core.trail_end,
        FullCutInvW c F0 F_cur cut' s' ∧ s'.core.cur_level = s.core.cur_level ∧
        FullConflictOkCut F_cur cut' s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullEagerSubsumeSpec : Spec [i64, i64] [] := fun (h, new_ref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧
    (∀ k < s.core.tmp_len, (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
    (new_ref.toNat < 0x80000000 → new_ref.toNat ∈ fullArenaClauseRefs s) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ arena' ag' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with arena := arena', arena_garbage := ag' }
          scratch := sc' }
      FullSparseInvW c F0 F_cur s' → sc'.work_stk2 = s.scratch.work_stk2 →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullLearnClauseSpec : Spec [i64, i64] [i64] := fun (h, _glue, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullOtfsInvW c F0 F_cur s ∧ 0 < s.core.cur_level ∧
    1 ≤ s.core.tmp_len ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
    ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
    (∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
    (∀ k, 1 ≤ k → k < s.core.tmp_len →
      let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level ∧
      lv ≤ (s.core.lvl[(s.core.tmp[s.core.tmp_len - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 → FullSparseInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullAnalyzeSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ FullConflictOkW F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

end LeanQbe.T.Examples.Kissat.Full
