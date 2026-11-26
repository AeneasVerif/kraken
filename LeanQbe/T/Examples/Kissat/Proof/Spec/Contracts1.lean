/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Src.Limits
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb
public import Kraken.Mem
public import Kraken.Separation

/-!
# Kissat `D-Full` Per-Function UNSAT-Only `Spec` Contracts (`Proof.Spec.Contracts1`)

Part 1 of the Stage-4 function contracts (`full_is_zero` .. `full_reduce`, plus shared
`FullKissatMath` arithmetic / `full_log10_q16_core_wp` helpers over `Src.Limits`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Spec

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test

/-! ## 1. Shared `fullSafetySlice` templates & `Full1` arithmetic / arena / watch specs -/

/-- Max-heap property outside `[0 ..< start)` on `ws[0 ..< n)` keyed by `wvec[2 * l]`. -/
@[expose] def FullWsortMaxHeap (wvec ws : List (BitVec 32)) (lo n : Nat) : Prop :=
  ∀ i, lo ≤ i → i < n →
    let p := (wvec[2 * (ws[i]?.getD 0#32).toNat]?.getD 0#32).toNat
    (2 * i + 1 < n → (wvec[2 * (ws[2 * i + 1]?.getD 0#32).toNat]?.getD 0#32).toNat ≤ p) ∧
    (2 * i + 2 < n → (wvec[2 * (ws[2 * i + 2]?.getD 0#32).toNat]?.getD 0#32).toNat ≤ p)

/-- Comparator matching `full_tmp_less(lvl, tpos, a, b)`. -/
@[expose] def fullTmpKeyLt (lvl tpos : List (BitVec 32)) (a b : BitVec 32) : Bool :=
  let la := (lvl[a.toNat / 2]?.getD 0#32).toNat
  let lb := (lvl[b.toNat / 2]?.getD 0#32).toNat
  decide (la < lb ∨ (la = lb ∧ (tpos[a.toNat / 2]?.getD 0#32).toNat <
    (tpos[b.toNat / 2]?.getD 0#32).toNat))

/-- Key and ordering predicates matching `FullMinSpecs` (`full_sort_tmp_sift`, `full_sort_tmp`). -/
@[expose] def fullTmpKey (lvl tpos : List (BitVec 32)) (x : BitVec 32) : Nat × Nat :=
  let v := x.toNat / 2
  ((lvl[v]?.getD 0#32).toNat, (tpos[v]?.getD 0#32).toNat)

@[expose] def fullTmpLt (lvl tpos : List (BitVec 32)) (a b : BitVec 32) : Prop :=
  (fullTmpKey lvl tpos a).1 < (fullTmpKey lvl tpos b).1 ∨
  ((fullTmpKey lvl tpos a).1 = (fullTmpKey lvl tpos b).1 ∧
   (fullTmpKey lvl tpos a).2 < (fullTmpKey lvl tpos b).2)

@[expose] def fullTmpLe (lvl tpos : List (BitVec 32)) (a b : BitVec 32) : Prop :=
  ¬ fullTmpLt lvl tpos b a

@[expose] def FullSortSliceEq (a b : List (BitVec 32)) (hi : Nat) : Prop :=
  (∀ j, 1 ≤ j → j < hi → ∃ i, 1 ≤ i ∧ i < hi ∧ a[j]? = b[i]?) ∧
  (∀ i, 1 ≤ i → i < hi → ∃ j, 1 ≤ j ∧ j < hi ∧ b[i]? = a[j]?)

@[expose] def FullTmpHeapAt (lvl tpos tmp : List (BitVec 32)) (i lim : Nat) : Prop :=
  (2 * i + 1 < lim →
    fullTmpLe lvl tpos (tmp[1 + (2 * i + 1)]?.getD 0#32) (tmp[1 + i]?.getD 0#32)) ∧
  (2 * i + 2 < lim →
    fullTmpLe lvl tpos (tmp[1 + (2 * i + 2)]?.getD 0#32) (tmp[1 + i]?.getD 0#32))

@[expose] def FullTmpMaxHeap (lvl tpos tmp : List (BitVec 32)) (lo lim : Nat) : Prop :=
  ∀ i, lo ≤ i → i < lim → FullTmpHeapAt lvl tpos tmp i lim

/-- Shared `fullSafetySlice` contract `(h) -> ()` preserving `FullState.core`, `LengthsOk`, and
`FullProbeScratchPres`. -/
@[expose] def fullSafetyVoidSpec : Spec [i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullProbeScratchPres s s')

/-- Shared `fullSafetySlice` contract `(h, v) -> ()` preserving `FullState.core`, `LengthsOk`,
and `FullProbeScratchPres`. -/
@[expose] def fullSafetyVarVoidSpec : Spec [i64, i32] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _v, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullProbeScratchPres s s')

@[expose] def fullIsqrtSpec : Spec [i64] [i64] := fun (x, ()) m Q _ =>
  ∀ r : BitVec 64,
    r.toNat * r.toNat ≤ x.toNat →
    (x.toNat ≤ 1 → r = x) →
    (2 ≤ x.toNat → 1 ≤ r.toNat ∧ x.toNat < (r.toNat + 1) * (r.toNat + 1)) →
    Q (r, ()) m

@[expose] def fullIlog10Spec : Spec [i64] [i64] := fun (_x, ()) m Q _ =>
  ∀ r : BitVec 64, 1 ≤ r.toNat → r.toNat ≤ 19 → Q (r, ()) m

@[expose] def fullRngNextSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => s'.scratch = { s.scratch with rng_state := s'.scratch.rng_state })

@[expose] def fullArenaNextSpec : Spec [i64, i32] [i32] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    Q (BitVec.ofNat 32 (fullArenaNextOff s.core.arena s.core.arena_len cref.toNat), ()) m

@[expose]
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

@[expose] def fullWsortSiftSpec : Spec [i64, i64, i64, i64] [] :=
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

@[expose] def fullWstackDefragSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
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

@[expose] def fullWatchPushSpec : Spec [i64, i32, i32, i32, i32] [.bool] :=
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

@[expose] def fullHeapUpSpec : Spec [i64, i32] [] :=
  SafetySlice.spec fullSafetySlice (fun c (h, _v, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullProbeScratchPres s s' ∧
      ∃ hp' ps', s'.scratch = { s.scratch with heap := hp', pos := ps' })
@[expose] def fullHeapPushSpec : Spec [i64, i32] [] :=
  SafetySlice.spec fullSafetySlice (fun c (h, _v, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullProbeScratchPresWith s s'
      (∃ hp' ps' hl', s'.scratch = { s.scratch with heap := hp', pos := ps', heap_len := hl' }))
abbrev fullRescaleSpec := fullSafetyVoidSpec
abbrev fullBumpVarSpec := fullSafetyVarVoidSpec
abbrev fullBumpDecaySpec := fullSafetyVoidSpec
abbrev fullQueueRenumberSpec := fullSafetyVoidSpec
abbrev fullQueueMtfSpec := fullSafetyVarVoidSpec
abbrev fullTickRelSpec := fullSafetyVoidSpec
@[expose] def fullSaveTargetBestSpec : Spec [i64] [] :=
  SafetySlice.spec fullSafetySlice (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullProbeScratchPres s s' ∧
      ∃ ta' ba' pt' pb', s'.scratch = { s.scratch with
        target_assigned := ta', best_assigned := ba',
        phases_target := pt', phases_best := pb' })
abbrev fullRecomputeTiersSpec := fullSafetyVoidSpec

@[expose] def fullHeapDownSpec : Spec [i64, i32] [] :=
  SafetySlice.spec fullSafetySlice (fun c (h, _v, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => s'.scratch.heap_len = s.scratch.heap_len ∧ FullProbeScratchPres s s')

@[expose] def fullHeapPopSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ (r, ()) s s' => (r = 0xFFFFFFFF#64 ∨ r.toNat < s.core.cur_vars) ∧
      (0 < s.scratch.heap_len ∧ s.scratch.heap_len ≤ s.core.cur_vars →
        s'.scratch.heap_len = s.scratch.heap_len - 1) ∧ FullProbeScratchPres s s')

@[expose] def fullEmaUpdateSpec : Spec [i64, i64] [] :=
  SafetySlice.spec fullSafetySlice (fun c (h, _glue, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullProbeScratchPres s s')

/-! ## 3. `Full1` trail, clause addition, initialization & DIMACS ingestion -/

@[expose] def fullAssignLvlSpec : Spec [i64, i32, i32, i32] [] :=
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

@[expose] def fullAssignSpec : Spec [i64, i32, i32] [] := fun (h, lit, rsn, ()) m Q _ =>
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

@[expose] def fullBacktrackSpec : Spec [i64, i64] [] := fun (h, target_lvl, ()) m Q _ =>
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
      (∃ ta' ba' pt' pb' hp' ps' hl' qsi' qss', sc' = { s.scratch with
        target_assigned := ta', best_assigned := ba', phases_target := pt', phases_best := pb',
        heap := hp', pos := ps', heap_len := hl',
        q_search_idx := qsi', q_search_stamp := qss' }) →
      (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      ((∃ F0 F_cur, FullWitnessInv c F0 F_cur s.core ∨ FullOtfsWitnessInv c F0 F_cur s.core) →
        (∀ l < 2 * s.core.cur_vars, vals'[l]?.getD 0#8 =
          if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat then
            s.core.vals[l]?.getD 0#8 else 0#8) ∧
        (∀ i < s.core.trail_end, let v := (s.core.trl[i]?.getD 0#32).toNat / 2
          lvl'[v]?.getD 0#32 = if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat then
            s.core.lvl[v]?.getD 0#32 else 0#32)) →
      (∀ F0 F_cur, FullWitnessInv c F0 F_cur s.core → target_lvl.toNat ≤ s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (∀ F0 F_cur, FullOtfsWitnessInv c F0 F_cur s.core → target_lvl.toNat < s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullAddClauseSpec : Spec [i64, i32, i32, .bool] [i64] :=
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
      if len.toNat < 2 then Q (0xFFFFFFFF#64, ()) m
      else if len.toNat = 2 then
        ∀ r wvec' wstk' wlen' wusable' nb' wsort' m',
          let s' : FullState :=
            { s with core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                           wusable := wusable', num_binary := nb' }
                     scratch := { s.scratch with wsort := wsort' } }
          (r = 0xFFFFFFFF#64 ∨ r = 0xFFFFFFFE#64) →
          s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → (FullMem c s' ⋆ R) m' → Q (r, ()) m'
      else
        ∀ r arena' alen' wvec' wstk' wlen' wusable' fred' ni' nr' wsort' m',
          let s' : FullState :=
            { s with core := { s.core with arena := arena', arena_len := alen', wvec := wvec',
                                           wstk := wstk', wlen := wlen', wusable := wusable',
                                           first_reducible := fred', num_irred := ni',
                                           num_redundant := nr' }
                     scratch := { s.scratch with wsort := wsort' } }
          (r = 0xFFFFFFFF#64 ∨ r = BitVec.ofNat 64 s.core.arena_len) →
          s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
          (∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s') →
          (FullArenaVarsNodup s → FullArenaVarsNodup s') →
          (r = BitVec.ofNat 64 s.core.arena_len → alen' = s.core.arena_len + 3 + len.toNat ∧
            s.core.arena_len ∈ fullArenaClauseRefs s' ∧
            fullArenaClauseGarb s' s.core.arena_len = false ∧
            fullArenaClauseLits s' s.core.arena_len =
              (s.core.tmp.take len.toNat).map BitVec.toNat) →
          (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullZeroTables1Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ wstk' mstk' repr' sc' m',
      wstk'.length = c.wcap → mstk'.length = 2 * c.minDepth → repr'.length = 2 * c.max_vars →
      sc'.LengthsOk c → sc'.extend_len = s.scratch.extend_len →
      (∀ i < 16, sc'.last_learned[i]?.getD 0#32 = 0xFFFFFFFF#32) →
      let s' : FullState :=
        { s with core := { s.core with vals := List.replicate (2 * c.max_vars) 0#8
                                       lit_mark := List.replicate (2 * c.max_vars) 0#8
                                       wvec := List.replicate (4 * c.max_vars) 0#32
                                       wstk := wstk', min_stk := mstk', repr := repr' }
                 scratch := sc' }
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullZeroTables2Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ flags' fdec' sc' m',
      flags'.length = c.max_vars → fdec'.length = c.max_vars + 1 →
      sc'.LengthsOk c → FullExtScratchPres s { s with scratch := sc' } →
      let s' : FullState :=
        { s with core := { s.core with mrk := List.replicate c.max_vars 0#8, flags := flags'
                                       lvl := List.replicate c.max_vars 0#32
                                       rsns := List.replicate c.max_vars 0xFFFFFFFF#32
                                       frame_trail := List.replicate (c.max_vars + 1) 0#32
                                       frame_dec := fdec' }
                 scratch := sc' }
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullFixedBytesSpec : Spec [i64] [i64] := fun (max_v, ()) m Q _ =>
  max_v.toNat < 2 * dimacsBound ∧ Q (BitVec.ofNat 64 (fullFixedBytes max_v.toNat), ()) m

@[expose] def fullInitPtrsSpec : Spec [i64, i64, i64] [] := fun (h, hdr_addr, max_v, ()) m Q _ =>
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

@[expose]
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

@[expose]
def fullCalcMaxVSpec : Spec [i64, i64, i64, i64] [i64] := fun (avail, mv, nc, f0, ()) m Q _ =>
  mv.toNat < dimacsBound ∧ nc.toNat < dimacsBound ∧
  f0.toNat = fullFixedBytes mv.toNat ∧ f0.toNat + nc.toNat * 40 + 136 ≤ avail.toNat ∧
  ∀ r : BitVec 64, mv.toNat ≤ r.toNat → r.toNat < 2 * dimacsBound →
    fullFixedBytes r.toNat + nc.toNat * 40 + 136 ≤ avail.toNat → Q (r, ()) m

@[expose] def fullCalcExtCapSpec : Spec [i64] [i64] := fun (rem, ()) m Q _ =>
  ∀ r : BitVec 64, r.toNat ≤ 131072 → (rem.toNat < 8192 → r = 0#64) →
    4 * r.toNat ≤ rem.toNat / 8 → Q (r, ()) m

@[expose] def fullCalcScrCapSpec : Spec [i64] [i64] := fun (rem, ()) m Q _ =>
  ∀ r : BitVec 64, r.toNat ≤ 32768 → (rem.toNat < 8192 → r = 0#64) →
    4 * r.toNat ≤ rem.toNat / 4 → Q (r, ()) m

@[expose] def fullInitArenasSpec : Spec [i64, i64, i64, i64] [] :=
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

@[expose] def fullInitStateSpec : Spec [i64, i64, i64, i64, i64] [.bool] :=
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

@[expose] def fullSkipClSpec : Spec [i64, i64] [.bool] := fun (cend, d, ()) m Q _ =>
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

@[expose] def fullIngestClSpec : Spec [i64, i64] [i64] := fun (h, cend, ()) m Q _ =>
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

@[expose] def fullParseBodySpec : Spec [i64, i64] [i64] := fun (h, cend, ()) m Q _ =>
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

@[expose] def fullFindReplSpec : Spec [i64, i64] [i64] := fun (h, cref, ()) m Q _ =>
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

@[expose]
def fullAssignLevelSpec : Spec [i64, i32, i32] [i32] := fun (h, cref, forced_lit, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ cref.toNat + 3 ≤ s.core.arena_len ∧
    cref.toNat + 3 + fullArenaClauseSize s cref.toNat ≤ s.core.arena_len ∧
    (∀ l ∈ fullArenaClauseLits s cref.toNat, l ≠ forced_lit.toNat → l / 2 < c.max_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ res : BitVec 32,
      (∀ l ∈ fullArenaClauseLits s cref.toNat, l ≠ forced_lit.toNat →
        (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ res.toNat) →
      (res = 0#32 ∨ ∃ l ∈ fullArenaClauseLits s cref.toNat,
        l ≠ forced_lit.toNat ∧ res = s.core.lvl[l / 2]?.getD 0#32) →
      Q (res, ()) m

@[expose]
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

@[expose] def fullPropagateIgnoreSpec : Spec [i64, i64] [i64] := fun (h, ignore_ref, ()) m Q _ =>
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

@[expose] def fullPropagateSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
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

@[expose] def fullPropagateIgnoreDelSpec : Spec [i64, i64] [i64] := fun (h, ignore_ref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                propagated := prop', unassigned := unass', unflushed := unfl',
                                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                wusable := wu', fuel := fuel', confl_type := ctype',
                                confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                oom := oom' }
          scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                      phases := phases', delayed := delayed' } }
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

theorem fullPropagateIgnoreDelSpec_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {ignore_ref : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hdm : s.core.dense_mode = 0#64)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                propagated := prop', unassigned := unass', unflushed := unfl',
                                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                wusable := wu', fuel := fuel', confl_type := ctype',
                                confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                oom := oom' }
          scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                      phases := phases', delayed := delayed' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ ctype' = s.core.confl_type ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s' ∧
        (ctype' = 2#64 → cref' ≠ ignore_ref)) →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    fullPropagateIgnoreDelSpec (c.hdr, ignore_ref, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, hQ⟩

theorem fullPropagateIgnoreDelSpec_elim {h ignore_ref : BitVec 64} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hs : fullPropagateIgnoreDelSpec (h, ignore_ref, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
      ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
        fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m',
        let s' : FullState :=
          { s with
            core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                  trl := trl', trail_pos := tp', trail_end := te',
                                  propagated := prop', unassigned := unass', unflushed := unfl',
                                  wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                  wusable := wu', fuel := fuel', confl_type := ctype',
                                  confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                  oom := oom' }
            scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                        phases := phases', delayed := delayed' } }
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
        fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
        (r = 0#64 → prop' = te' ∧ ctype' = s.core.confl_type ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
          (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
        (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s' ∧
          (ctype' = 2#64 → cref' ≠ ignore_ref)) →
        (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
        (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m' :=
  hs

theorem fullPropagateIgnoreDelSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : fullPropagateIgnoreDelSpec xs m Q X) :
    fullPropagateIgnoreDelSpec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem fullPropagateIgnoreSpec_of_del {a : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : fullPropagateIgnoreDelSpec a m Q X) :
    fullPropagateIgnoreSpec a m Q X := by
  rcases a with ⟨hptr, ig, ⟨⟩⟩
  obtain ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, hQ⟩ := h
  exact ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm,
    fun r v f lv rs tr tp te pr un uf wv ar ws wl wu fu ct cr c0 c1 oo tk wso ph m'
        hlen' hw' htr hap hfl hd h0 h1 h2 heq hm' =>
      hQ r v f lv rs tr tp te pr un uf wv ar ws wl wu fu ct cr c0 c1 oo tk wso ph
        s.scratch.delayed m' hlen' hw' htr hap hfl hd h0 h1 h2 heq hm'⟩

@[expose] def fullPropagateDelSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                propagated := prop', unassigned := unass', unflushed := unfl',
                                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                wusable := wu', fuel := fuel', confl_type := ctype',
                                confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                oom := oom' }
          scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                      phases := phases', delayed := delayed' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s') →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem fullPropagateDelSpec_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core) (hdm : s.core.dense_mode = 0#64)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                propagated := prop', unassigned := unass', unflushed := unfl',
                                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                wusable := wu', fuel := fuel', confl_type := ctype',
                                confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                oom := oom' }
          scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                      phases := phases', delayed := delayed' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s') →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    fullPropagateDelSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, hQ⟩

theorem fullPropagateDelSpec_elim {h : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : fullPropagateDelSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
      ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
        fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m',
        let s' : FullState :=
          { s with
            core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                  trl := trl', trail_pos := tp', trail_end := te',
                                  propagated := prop', unassigned := unass', unflushed := unfl',
                                  wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                  wusable := wu', fuel := fuel', confl_type := ctype',
                                  confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                  oom := oom' }
            scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                        phases := phases', delayed := delayed' } }
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
        fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
        (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
          (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
        (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s') →
        (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
        (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m' :=
  hs

theorem fullPropagateDelSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : fullPropagateDelSpec xs m Q X) : fullPropagateDelSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem fullPropagateSpec_of_del {a : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : fullPropagateDelSpec a m Q X) : fullPropagateSpec a m Q X := by
  rcases a with ⟨hptr, ⟨⟩⟩
  obtain ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, hQ⟩ := h
  exact ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm,
    fun r v f lv rs tr tp te pr un uf wv ar ws wl wu fu ct cr c0 c1 oo tk wso ph m'
        hlen' hw' htr hap hfl hd h0 h1 h2 heq hm' =>
      hQ r v f lv rs tr tp te pr un uf wv ar ws wl wu fu ct cr c0 c1 oo tk wso ph
        s.scratch.delayed m' hlen' hw' htr hap hfl hd h0 h1 h2 heq hm'⟩

@[expose] def fullMarkReasonsSpec : Spec [i64, .bool] [] := fun (h, set_flag, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ arena' m',
      let s' : FullState := { s with core := { s.core with arena := arena' } }
      s'.LengthsOk c → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
        fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
        fullArenaClauseLits s' r = fullArenaClauseLits s r) →
      (set_flag = true → FullReasonsMarked s') →
      FullWitnessInv c F0 F_cur s'.core → (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullRedLessSpec : Spec [i64, i32, i32] [.bool] := fun (ar_ptr, a, b, ()) m Q _ =>
  ∃ (ar : List (BitVec 32)) (R : Mem 64 → Prop),
    a.toNat + 2 < ar.length ∧ b.toNat + 2 < ar.length ∧
    (array (t := i32) ar_ptr ar ⋆ R) m ∧ ∀ res : Bool, Q (res, ()) m

@[expose]
def fullRedSiftSpec : Spec [i64, i64, i64, i64] [] := fun (ar_ptr, rr_ptr, start, n, ()) m Q _ =>
  ∃ (ar rr : List (BitVec 32)) (R : Mem 64 → Prop),
    start.toNat ≤ n.toNat ∧ n.toNat ≤ rr.length ∧ n.toNat < 2 ^ 62 ∧
    (∀ k < n.toNat, (rr[k]?.getD 0#32).toNat + 2 < ar.length) ∧
    (array (t := i32) ar_ptr ar ⋆ array (t := i32) rr_ptr rr ⋆ R) m ∧
    ∀ rr' m', rr'.length = rr.length →
      (∀ k, n.toNat ≤ k → rr'[k]? = rr[k]?) →
      (∀ k < n.toNat, ∃ j < n.toNat, rr'[k]? = rr[j]?) →
      (array (t := i32) ar_ptr ar ⋆ array (t := i32) rr_ptr rr' ⋆ R) m' → Q () m'

@[expose] def fullSortRedsSpec : Spec [i64, i64] [] := fun (h, n, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ n.toNat ≤ c.red_cap ∧
    (∀ k < n.toNat, (s.scratch.red_refs[k]?.getD 0#32).toNat + 2 < c.arena_cap) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ rr' m', rr'.length = c.red_cap →
      (∀ k < n.toNat, ∃ j < n.toNat, rr'[k]? = s.scratch.red_refs[j]?) →
      (FullMem c { s with scratch := { s.scratch with red_refs := rr' } } ⋆ R) m' → Q () m'

@[expose]
def fullLitRankSpec : Spec [i64, i64, i32] [i64] := fun (vals_ptr, lvl_ptr, l, ()) m Q _ =>
  ∃ (vals : List (BitVec 8)) (lvl : List (BitVec 32)) (R : Mem 64 → Prop),
    l.toNat < vals.length ∧ l.toNat / 2 < lvl.length ∧
    (array (t := i8) vals_ptr vals ⋆ array (t := i32) lvl_ptr lvl ⋆ R) m ∧
    ∀ r : BitVec 64, Q (r, ()) m

@[expose] def fullUnwatchLargeSpec : Spec [i64, i32, i32] [] := fun (h, _lit, _cref, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wu' m',
      let s' := { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } }
      s'.LengthsOk c → WatchStackLayout s'.core →
      (∀ F_cur, ModeWatchesInv F_cur s.core → ModeWatchesInv F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullSweepBinsSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wlen' nb' wsort' m',
      let s' : FullState :=
        { s with
          core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64,
                                num_binary := nb' }
          scratch := { s.scratch with wsort := wsort' } }
      s'.LengthsOk c → FullBinOnlyWatchesInv F_cur s'.core → DenseWatchesInv F_cur s'.core →
      FullWitnessInv c F0 F_cur s'.core → (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullSweepCopySpec : Spec [i64, i64, i64, i32, .bool] [i64] :=
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
          (r = 0xFFFFFFFE#64 → F0.Unsat) ∧ (r = 0xFFFFFFFD#64 → oom' = 1#64) ∧
          (r ≠ 0xFFFFFFFD#64 → oom' = s.core.oom) ∧ (r = 1#64 → s.core.trail_end < te') ∧
          (3 ≤ r.toNat ∧ r.toNat ≤ old_sz.toNat →
            (∀ j < r.toNat, (arena'[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
            List.Sublist (((arena'.drop (dst.toNat + 3)).take r.toNat).map BitVec.toNat)
              (((s.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat) ∧
            (cnfOfClauses F_cur).EntailsClause
              (cnfClause (((arena'.drop (dst.toNat + 3)).take r.toNat).map BitVec.toNat)))) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullRewatchArenaSpec : Spec [i64, i64] [.bool] := fun (h, dst, ()) m Q _ =>
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
      (ok = false → oom' = 1#64) → (ok = true → oom' = s.core.oom) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullArenaSweepSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
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
      (0 < s.core.cur_level → r ≠ 1#64 ∧ r ≠ 2#64 ∧
        vals' = s.core.vals ∧ lvl' = s.core.lvl ∧ trl' = s.core.trl ∧
        tp' = s.core.trail_pos ∧ te' = s.core.trail_end) →
      (r = 1#64 → s.core.cur_level = 0 ∧ s.core.trail_end < te') →
      (r = 2#64 → s.core.cur_level = 0 ∧ F0.Unsat) →
      (r = 3#64 → oom' ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullReduceSpec : Spec [i64, .bool] [i64] := fun (h, _force, ()) m Q _ =>
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

/-! ## 5. Shared Arithmetic, BitVector & `full_log10_q16` Helpers (`FullKissatMath`) -/

namespace FullKissatMath

open Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep

/-! ## 1. Powers of 10, Q16 Packing & `BitVec` Helpers -/

theorem pow10_lt_64 {d : Nat} (hd : d ≤ 19) : 10 ^ d < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hd) (by decide)

theorem pow10_succ_mul10 {d : Nat} {p : BitVec 64} (hd : d < 19) (hp : p.toNat ≤ 10 ^ d) :
    p.toNat * 10 ≤ 10 ^ (d + 1) ∧ p.toNat * 10 < 2 ^ 64 ∧ (p * 10#64).toNat = p.toNat * 10 := by
  have hpow : p.toNat * 10 ≤ 10 ^ (d + 1) := by
    rw [Nat.pow_succ]; exact Nat.mul_le_mul_right 10 hp
  have hlt64 : p.toNat * 10 < 2 ^ 64 := Nat.lt_of_le_of_lt hpow (pow10_lt_64 (by omega))
  have hmul : (p * 10#64).toNat = p.toNat * 10 := by
    rw [BitVec.toNat_mul, show (10#64).toNat = 10 from rfl, Nat.mod_eq_of_lt hlt64]
  exact ⟨hpow, hlt64, hmul⟩

theorem shift_split_65536 {k : Nat} (hk : k < 16) :
    (65536 >>> k) = (32768 >>> k) + (65536 >>> (k + 1)) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
      k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem bv64_add_toNat {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem bv64_add1_toNat {g : BitVec 64} (h : g.toNat + 1 < 2 ^ 64) :
    (g + 1#64).toNat = g.toNat + 1 := bv64_add_toNat h

theorem bv64_sub_toNat {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by bv_omega

theorem bv64_sub1_toNat {f : BitVec 64} (hf : f ≠ 0#64) : (f - 1#64).toNat = f.toNat - 1 := by
  have hpos : 0 < f.toNat := Nat.pos_of_ne_zero fun h0 =>
    hf (BitVec.eq_of_toNat_eq (by simpa using h0))
  bv_omega

theorem bv64_shl1_toNat {v : BitVec 64} (h : 2 * v.toNat < 2 ^ 64) :
    (v <<< 1#64).toNat = 2 * v.toNat := by
  have hsh : v <<< 1#64 = v <<< (1#64).toNat := rfl
  rw [hsh, BitVec.toNat_shiftLeft, show (1#64).toNat = 1 by decide, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem bv64_ofNat_toNat {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem bv32_ofNat_toNat {n : Nat} (hn : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem zext_toNat {w1 w2 : Nat} (x : BitVec w1) (hle : w1 ≤ w2) :
    (x.setWidth w2).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right
    (by omega) hle))]

theorem bv64_trunc32_ofNat {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, bv64_ofNat_toNat (by omega), bv32_ofNat_toNat hn,
    Nat.mod_eq_of_lt hn]

theorem bv64_zext32_ushr1 (x : BitVec 32) :
    ((x.setWidth 64) >>> (BitVec.signExtend 64 (1 : BitVec 32)).toNat).toNat = x.toNat / 2 := by
  have h1 : (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 := rfl
  rw [h1]; bv_omega

theorem bv32_xor1_div2 (x : BitVec 32) : (x ^^^ 1#32).toNat / 2 = x.toNat / 2 := by
  have hsr : (x ^^^ 1#32) >>> 1 = x >>> 1 := by
    ext i hi
    simp [BitVec.getLsbD_xor, show (1#32).getLsbD (1 + i) = false by
      simp [BitVec.getLsbD_one]]
  have h1 : ((x ^^^ 1#32) >>> 1).toNat = (x ^^^ 1#32).toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : (x >>> 1).toNat = x.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [← h1, ← h2, hsr]

private theorem nat_two_mul_or_one (k : Nat) : (2 * k) ||| 1 = 2 * k + 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ j =>
    rw [Nat.testBit_or]; simp only [Nat.testBit_succ]
    have h10 : Nat.testBit (1 / 2) j = false := by simp
    have hd1 : (2 * k) / 2 = k := by omega
    have hd2 : (2 * k + 1) / 2 = k := by omega
    rw [h10, hd1, hd2, Bool.or_false]

theorem bv32_lit_even {x : BitVec 64} (hx : x.toNat < 2 ^ 30) :
    ((x <<< 1#64).setWidth 32).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_setWidth, bv64_shl1_toNat (by omega), Nat.mod_eq_of_lt (by omega)]

theorem bv32_lit_odd {x : BitVec 64} (hx : x.toNat < 2 ^ 30) :
    (((x <<< 1#64).setWidth 32 ||| 1#32)).toNat = 2 * x.toNat + 1 := by
  rw [BitVec.toNat_or, bv32_lit_even hx, show (1#32 : BitVec 32).toNat = 1 by decide]
  exact nat_two_mul_or_one x.toNat

theorem q16_shl_bounds {x d frac : BitVec 64} (hd : d.toNat ≤ 19) (hf : frac.toNat < 65536)
    (h10 : 10 ≤ x.toNat → 1 ≤ d.toNat) :
    ((d <<< (16 : Nat)) + frac).toNat < 20 * 65536 ∧
    (10 ≤ x.toNat → 65536 ≤ ((d <<< (16 : Nat)) + frac).toNat) := by
  have hd_sh : (d <<< (16 : Nat)).toNat = d.toNat * 65536 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      show d.toNat * 2 ^ 16 = d.toNat * 65536 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hsum : ((d <<< (16 : Nat)) + frac).toNat = d.toNat * 65536 + frac.toNat := by
    rw [BitVec.toNat_add, hd_sh, Nat.mod_eq_of_lt (by omega)]
  exact ⟨by rw [hsum]; omega, fun hx => by have := h10 hx; rw [hsum]; omega⟩

theorem q16_mul_bounds {x d frac : BitVec 64} (hd : d.toNat ≤ 19) (hf : frac.toNat < 65536)
    (h10 : 10 ≤ x.toNat → 1 ≤ d.toNat) :
    (d * 65536#64 + frac).toNat < 20 * 65536 ∧
    (10 ≤ x.toNat → 65536 ≤ (d * 65536#64 + frac).toNat) := by
  have hmul : (d * 65536#64).toNat = d.toNat * 65536 := by bv_omega
  have hsum : (d * 65536#64 + frac).toNat = d.toNat * 65536 + frac.toNat := by
    rw [BitVec.toNat_add, hmul, Nat.mod_eq_of_lt (by omega)]
  exact ⟨by rw [hsum]; omega, fun hx => by have := h10 hx; rw [hsum]; omega⟩

/-! ## 2. Shared `wp_let` Math Combinators & `full_log10_q16` WP Core -/

theorem wp_let_ult64_m {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {hm : Ty.bool = Ty.mask i64} {a b : Arg Val i64}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult i64 .bool hm) (a, b, ())) k) m =
      wp Γ Q X (k (BitVec.ult a.val b.val, ())) m := by
  have hc := @wp_let_cmp_eq Γ rs Q X m .ult i64 .bool hm (a, b, ()) k
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, liftCmp,
    evalBits_ult_eq, cast_eq] using hc

theorem wp_let_udiv64_m {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a b : Arg Val i64} {k : Tup Val [i64] → Expr Val Cont rs}
    (hb : b.val ≠ 0#64) :
    wp Γ Q X (.let_ (Op.mk (.udiv 64) (a, b, ())) k) m ↔
      wp Γ Q X (k (a.val / b.val, ())) m := by
  rw [wp_let_udiv_eq]; exact ⟨fun h => h.2, fun h => ⟨hb, h⟩⟩

theorem wp_let_udiv64_var_m {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a : Arg Val i64} {vb : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs}
    (hb : vb ≠ 0#64) :
    wp Γ Q X (.let_ (Op.mk (.udiv 64) (a, .var vb, ())) k) m ↔
      wp Γ Q X (k (a.val / vb, ())) m := wp_let_udiv64_m hb

theorem wp_let_udiv64_imm_m {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a : Arg Val i64} {ib : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs}
    (hb : ib ≠ 0#64) :
    wp Γ Q X (.let_ (Op.mk (.udiv 64) (a, .imm ib, ())) k) m ↔
      wp Γ Q X (k (a.val / ib, ())) m := wp_let_udiv64_m hb

/-- Shared WP theorem for the Q32 repeated-squaring `full_log10_q16` algorithm
(certifying `LeanQbe.T.Examples.Kissat.Src.Limits.full_log10_q16_m7_body`). -/
theorem full_log10_q16_core_wp (Γ : Env) (x : BitVec 64) (m : Mem 64)
    (Q : Post [i64]) (X : XPost)
    (hQ : ∀ r : BitVec 64, r.toNat < 20 * 65536 →
      (10 ≤ x.toNat → 65536 ≤ r.toNat) → Q (r, ()) m) :
    Func.wp Γ LeanQbe.T.Examples.Kissat.Src.Limits.full_log10_q16_m7_body (x, ()) m Q X := by
  c0_hsteps_nogrp
  · have hx1 : x.toNat ≤ 1 := by c0_bound
    exact hQ 0#64 (by decide) (fun hx10 => by omega)
  · refine wp_loop_inv (ts := [i64, i64])
      (fun (d, pow10, ()) m1 =>
        m = m1 ∧ d.toNat ≤ 19 ∧ 1 ≤ pow10.toNat ∧ pow10.toNat ≤ 10 ^ d.toNat ∧
        (d.toNat = 0 → pow10.toNat = 1))
      (fun (d, _, ()) _ => 19 - d.toNat) ?_ ?_
    · intro J hJ
      c0_hsteps; exact hJ (0#64, 1#64, ()) m ⟨rfl, by decide, by decide, by decide, fun _ => rfl⟩
    · rintro J ⟨d, pow10, ⟨⟩⟩ _ ⟨rfl, hd19, hp1, hple, hd0p⟩ hJ
      refine wp_join_group (ts := []) (fun _ m1 => m = m1 ∧ (10 ≤ x.toNat → 1 ≤ d.toNat))
        ?_ ?_
      · rintro _ ⟨⟩ _ ⟨rfl, hd10⟩
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64, i64]) (fun (_, pm', ()) m2 => m = m2 ∧ 1 ≤ pm'.toNat)
          ?_ ?_
        · rintro _ ⟨xm', pm', ⟨⟩⟩ m2 ⟨hm2, hpm⟩
          subst m2
          have hpm_ne : pm' ≠ 0#64 := fun h0 => by subst h0; simp at hpm
          c0_hsteps_nogrp
          all_goals try exact hpm_ne
          refine wp_loop_inv (ts := [i64, i64, i64])
            (fun (_mv, frac, i, ()) m3 => m = m3 ∧ i.toNat ≤ 16 ∧ frac.toNat < 2 ^ i.toNat)
            (fun (_, _, i, ()) _ => 16 - i.toNat) ?_ ?_
          · intro J2 hJ2; c0_hsteps; exact hJ2 (_, 0#64, 0#64, ()) m ⟨rfl, by decide, by decide⟩
          · rintro J2 ⟨mv, frac, i, ⟨⟩⟩ m3 ⟨hm3, hi16, hfl⟩ hJ2
            subst m3; c0_hsteps
            · have hi_lt : i.toNat < 16 := by c0_bound
              have hf_lt : frac.toNat < 2 ^ 15 :=
                Nat.lt_of_lt_of_le hfl (Nat.pow_le_pow_right (by omega) (by omega))
              have hi1 : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_toNat (by omega)
              have hf2p1 : (frac <<< (1 : Nat) + 1#64).toNat = 2 * frac.toNat + 1 := by bv_omega
              have hf2p1_lt : 2 * frac.toNat + 1 < 2 ^ (i.toNat + 1) := by rw [Nat.pow_succ]; omega
              exact hJ2 (_, (frac <<< (1 : Nat)) + 1#64, i + 1#64, ()) m (by dsimp only; omega)
                ⟨rfl, by omega, by rw [hi1, hf2p1]; exact hf2p1_lt⟩
            · have hi_lt : i.toNat < 16 := by c0_bound
              have hf_lt : frac.toNat < 2 ^ 15 :=
                Nat.lt_of_lt_of_le hfl (Nat.pow_le_pow_right (by omega) (by omega))
              have hf_sh : (frac <<< (1 : Nat)).toNat = 2 * frac.toNat := by
                rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
              have hf2_lt : 2 * frac.toNat < 2 ^ (i.toNat + 1) := by rw [Nat.pow_succ]; omega
              have hi1 : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_toNat (by omega)
              exact hJ2 (_, frac <<< (1 : Nat), i + 1#64, ()) m (by dsimp only; omega)
                ⟨rfl, by omega, by rw [hi1, hf_sh]; exact hf2_lt⟩
            · have hflt : frac.toNat < 65536 :=
                Nat.lt_of_lt_of_le hfl (Nat.pow_le_pow_right (by omega) hi16)
              obtain ⟨hlt, hge⟩ := q16_shl_bounds hd19 hflt hd10
              exact hQ ((d <<< (16 : Nat)) + frac) hlt hge
        · intro _ hJm; c0_hsteps_nogrp
          · have hpm_gt : 100000000 < pow10.toNat := by c0_bound
            intro h0; have ht := congrArg BitVec.toNat h0
            change pow10.toNat / 100000000 = 0 at ht
            have hpos : 0 < pow10.toNat / 100000000 :=
              Nat.div_pos (Nat.le_of_lt hpm_gt) (by decide)
            omega
          · exact hJm (x / (pow10 / 100000000#64), 100000000#64, ()) m ⟨rfl, by decide⟩
          · exact hJm (x, pow10, ()) m ⟨rfl, hp1⟩
      · intro _ hJexit; c0_hsteps_nogrp
        · have hd_lt : d.toNat < 19 := by c0_bound
          obtain ⟨hp10, _, hp_mul⟩ := pow10_succ_mul10 hd_lt hple
          have hd1 : (d + 1#64).toNat = d.toNat + 1 := bv64_add1_toNat (by omega)
          exact hJ (d + 1#64, pow10 * 10#64, ()) m (by dsimp only; omega)
            ⟨rfl, by omega, by omega, by rw [hd1, hp_mul]; exact hp10,
             fun h0 => by rw [hd1] at h0; omega⟩
        · have hge : 19 ≤ d.toNat := by c0_bound
          exact hJexit () m ⟨rfl, fun _ => by omega⟩
        · have hlt : x.toNat / 10 < pow10.toNat := by
            have hdiv : (x / 10#64).toNat < pow10.toNat := by c0_bound
            have hmod : (x / 10#64).toNat = x.toNat / 10 := by bv_omega
            omega
          refine hJexit () m ⟨rfl, fun hx10 => ?_⟩
          rcases Nat.eq_zero_or_pos d.toNat with hd0 | hdpos
          · have hp1' := hd0p hd0; omega
          · exact hdpos

end FullKissatMath

end LeanQbe.T.Examples.Kissat.Proof.Spec
