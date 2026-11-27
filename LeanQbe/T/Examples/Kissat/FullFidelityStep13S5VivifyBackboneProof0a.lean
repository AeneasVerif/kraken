/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5VivifyBackbone
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof0
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof1
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof2b
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof4a
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof0
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullM3BackboneLemmas1
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullArena1
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S5-B — Specs, Promote ADD & MarkGarb (`Proof0a`)

Exports Step-13 `@[expose]` callee/function specifications for Shard S5-B (`14` fns) and
proves UNSAT-sound `Func.wp` (`XPost := False`, `0` SAT model proofs) for:
1. `full_viv_recompute_promote_fid_s5_wp` (ADD, `step13VivRecomputePromoteSpec`)
2. `full_viv_mark_garb_m6_s5_wp` (`FullM6VivBackbone.fullVivMarkGarbM6Spec`)
-/

set_option autoImplicit false

local elab "c0_hfast" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local elab "c0_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullArenaTactics FullVivTopTactics
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets

/-! ## 1. Step-13 S5-B Specifications -/

/-- `FullSparseInvW` without `FullMarkClearW`: holds while `mrk`/`lit_mark` are temporarily dirty
during `full_viv_deduce_m6` and still suffices for `full_viv_recompute_promote_fid`. -/
@[expose] def S13SparseInvNoMark (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

/-- `full_viv_recompute_promote_fid(h, cref)`: recomputes glue for non-garbage arena clause
`cref` and lowers it in place if `0 < ng < glue`, restoring `frame_trail` and preserving
`S13SparseInvNoMark`, `fullArenaClauseRefs`, and all clause garb/size/literal lists. -/
@[expose] def step13VivRecomputePromoteSpec : Spec [i64, i32] [] :=
  fun (h, cref, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ S13SparseInvNoMark c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
      fullArenaClauseGarb s cref.toNat = false ∧ (FullMem c s ⋆ R) m ∧
      ∀ ar' mclr' m',
        let s' : FullState := { s with core := { s.core with arena := ar', min_clr := mclr' } }
        S13SparseInvNoMark c F0 F_cur s' →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (∀ r ∈ fullArenaClauseRefs s,
          fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
          fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
          fullArenaClauseLits s' r = fullArenaClauseLits s r) →
        (FullMem c s' ⋆ R) m' → Q () m'

/-- Step-13 `full_viv_deduce_m6(h, cref, sz, implied)`: allows `arena` glue promotion via
`full_viv_recompute_promote_fid` while preserving `FullSparseInvW`, `fullArenaClauseRefs`,
and all clause garb/size/literal lists (`step13VivDeduceM6Spec`). -/
@[expose] def step13VivDeduceM6Spec : Spec [i64, i32, i32, i32] [i32] :=
  fun (h, cref, sz, implied, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
      fullArenaClauseGarb s cref.toNat = false ∧ sz.toNat ≤ c.max_vars ∧
      (∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (implied = 0xFFFFFFFF#32 →
        FullVivifySpecs.FullVivConflictOk F_cur s ∨
        s.core.confl_type = 0#64 ∧
          ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
      (implied ≠ 0xFFFFFFFF#32 →
        implied.toNat < 2 * s.core.cur_vars ∧ s.core.vals[implied.toNat]?.getD 0#8 = 1#8) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ olen ar' mclr' mrk' lm' ws1' ws2' asz' rsz' m',
        let s' : FullState :=
          { s with
            core := { s.core with arena := ar', min_clr := mclr', mrk := mrk', lit_mark := lm' }
            scratch := { s.scratch with
              work_stk1 := ws1', work_stk2 := ws2', ant_sz := asz', res_sz := rsz' } }
        FullSparseInvW c F0 F_cur s' → M6SubRefOk s' asz' →
        (asz' ≠ 0xFFFFFFFFFFFFFFFF#64 → asz' ≠ 0xFFFFFFFFFFFFFFFE#64 →
          asz'.toNat ∈ fullArenaClauseRefs s' ∧ fullArenaClauseGarb s' asz'.toNat = false) →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (∀ r ∈ fullArenaClauseRefs s,
          fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
          fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
          fullArenaClauseLits s' r = fullArenaClauseLits s r) →
        (asz' = 0xFFFFFFFFFFFFFFFF#64 → olen ≠ 0xFFFFFFFF#32 →
          olen.toNat ≤ s.core.cur_vars ∧
          (∀ k < olen.toNat, (ws2'[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
          ((ws2'.take olen.toNat).map fun x => x.toNat / 2).Nodup ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause ((ws2'.take olen.toNat).map BitVec.toNat))) →
        (FullMem c s' ⋆ R) m' → Q (olen, ()) m'

/-- Step-13 `full_vivify_tier_m6_hdr(h, tier_mode, budget, tick_lim)`: threads `FullM6HdrMem`
for watermark ticks and saves/restores `h->probing` (`s'.core.probing = s.core.probing`). -/
@[expose] def step13VivifyTierSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (h, _tier_mode, budget, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullSparseInv c F0 s ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        FullSparseInv c F0 s' →
        (s.core.cur_level = 0 → s'.core.cur_level = 0) →
        s'.core.probing = s.core.probing →
        (budget ≠ 0#64 → s'.core.cur_level = 0) →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Step-13 `full_vivify_m6_hdr(h)`: multi-tier vivification preserving `h->probing`. -/
@[expose] def step13VivifySpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullSparseInv c F0 s ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      FullSparseInv c F0 s' → s'.core.cur_level = 0 ∧ s'.core.probing = s.core.probing →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Step-13 `full_backbone_analyze_m6(h, c0, c1, saved)`: reads `saved0 = h->res_sz` as loop lower
bound while tracking probe decision index `saved` (`saved0 ≤ saved < trail_end`). -/
@[expose] def step13BackboneAnalyzeM6Spec : Spec [i64, i32, i32, i64] [i32] :=
  fun (h, c0, c1, saved, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s0 st : FullState)
      (saved0 max_lvl : Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s0 ∧ BbTrailInv c F0 F_cur s0 st saved0 max_lvl ∧
      0 < st.core.cur_level ∧ st.scratch.res_sz = BitVec.ofNat 64 saved0 ∧
      saved0 ≤ saved.toNat ∧
      st.core.rsns[(st.core.trl[saved.toNat]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
        0xFFFFFFFF#32 ∧
      BackboneProbeSeg F_cur st saved.toNat st.core.cur_level ∧
      c0.toNat < 2 * s0.core.cur_vars ∧ c1.toNat < 2 * s0.core.cur_vars ∧
      st.core.vals[c0.toNat]?.getD 0#8 = 0xFF#8 ∧
      st.core.vals[c1.toNat]?.getD 0#8 = 0xFF#8 ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [c0.toNat, c1.toNat]) ∧
      (∃ idx0, saved.toNat ≤ idx0 ∧ idx0 < st.core.trail_end ∧
        (st.core.trl[idx0]?.getD 0#32).toNat = c0.toNat ^^^ 1) ∧
      (FullMem c st ⋆ R) m ∧
      ∀ (uip : BitVec 32) (mrk' : List (BitVec 8)) m',
        mrk'.length = c.max_vars → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
        (uip ≠ 0xFFFFFFFF#32 → uip.toNat < 2 * s0.core.cur_vars ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause [uip.toNat ^^^ 1])) →
        (FullMem c { st with core := { st.core with mrk := mrk' } } ⋆ R) m' → Q (uip, ()) m'

/-- Step-13 `full_backbone_round_m6(h, cand_n, stop_early)`: packs `(ucnt | (incons ? 2^63 : 0))`
into `h->res_sz` so `(h->res_sz &&& 0x7FFFFFFFFFFFFFFF) = ucnt`. -/
@[expose] def step13BackboneRoundM6Spec : Spec [i64, i64, .bool] [i64] :=
  fun (h, cand_n, _stop_early, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s0 : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s0 ∧ s0.core.cur_level = 0 ∧
      cand_n.toNat ≤ 2 * s0.core.cur_vars ∧
      (∀ i < cand_n.toNat, (s0.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
      (FullMem c s0 ⋆ R) m ∧
      ∀ keep' s' m',
        FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
        s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
        keep'.toNat ≤ 2 * s0.core.cur_vars →
        (∀ i < keep'.toNat, (s'.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) →
        (s'.scratch.res_sz &&& 0x7FFFFFFFFFFFFFFF#64).toNat ≤ 2 * s0.core.cur_vars →
        (∀ i < (s'.scratch.res_sz &&& 0x7FFFFFFFFFFFFFFF#64).toNat,
          (s'.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause [(s'.scratch.work_stk2[i]?.getD 0#32).toNat])) →
        (FullMem c s' ⋆ R) m' → Q (keep', ()) m'

/-- Step-13 `full_backbone_m6(h, tick_lim)`: threads `FullM6HdrMem` (`m6_wm4_{get,set}`) and
saves/restores `h->probing` (`s'.core.probing = s.core.probing`). -/
@[expose] def step13BackboneSpec : Spec [i64, i64] [i64] := fun (h, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullSparseInv c F0 s ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      FullSparseInv c F0 s' →
      (s.core.cur_level = 0 → s'.core.cur_level = 0) →
      s'.core.probing = s.core.probing →
      (s'.core.cur_level = 0 ∧ s'.core.probing = s.core.probing) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Step-13 `FullM6HdrMem`-threaded contract for `full_transitive_m6(h, tick_lim)`: calls
`full_propagate` (`step13BcpM6Spec`) and saves/restores `h->probing`. -/
@[expose] def step13TransitiveSpec : Spec [i64, i64] [i64] := fun (h, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullSparseInv c F0 s ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      FullSparseInv c F0 s' →
      (s.core.cur_level = 0 → s'.core.cur_level = 0) →
      s'.core.probing = s.core.probing →
      (s'.core.cur_level = 0 ∧ s'.core.probing = s.core.probing) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Step-13 `FullM6HdrMem`-threaded contract for `full_propagate` (identical to `S2`'s
`step13BcpM6Spec` without importing `S2`). -/
@[expose] def s5bBcpM6Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
    (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    FullWitnessInv c F0 F_cur s.core ∧ s.core.dense_mode = 0#64 ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen'
      wu' fuel' ctype' cref' c0' c1' oom' (sc' : FullScratch) m',
      let s' : FullState :=
        { s with
          core :=
            { s.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
              unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
              wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
              confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
          scratch := sc' }
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      Full.FullProbeScratchPres { s with scratch := { s.scratch with
        search_ticks := sc'.search_ticks, wsort := sc'.wsort,
        phases := sc'.phases, delayed := sc'.delayed } } s' →
      sc'.red_refs = s.scratch.red_refs →
      sc'.delayed_len = s.scratch.delayed_len →
      (s.core.probing = 0#64 → sc' = { s.scratch with
        search_ticks := sc'.search_ticks, wsort := sc'.wsort,
        phases := sc'.phases, delayed := sc'.delayed }) →
      (c.delayed_cap = 0 → sc'.delayed = s.scratch.delayed) →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s') →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ ext' = ext ∧ s' = s) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Step-13 `full_backbone_prop_m6(h, prop_start, stop_early)`: binary-only propagation under
level-0 unit mode (`cur_level = 0`), probe-level 1UIP mode, or active-level unit cascade
(`0 < st.core.cur_level`). -/
@[expose] def step13BackbonePropM6Spec : Spec [i64, i64, .bool] [.bool] :=
  fun (h, prop_start, _stop_early, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s0 st : FullState)
      (saved0 max_lvl : Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s0 ∧ BbTrailInv c F0 F_cur s0 st saved0 max_lvl ∧
      saved0 ≤ prop_start.toNat ∧ prop_start.toNat ≤ st.core.trail_end ∧
      ((st.core.cur_level = 0 ∧
        ∀ i, prop_start.toNat ≤ i → i < st.core.trail_end →
          (st.core.lvl[(st.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0) ∨
       (0 < st.core.cur_level ∧ st.core.cur_level ≤ c.max_vars)) ∧
      (FullMem c st ⋆ R) m ∧
      ∀ (ok : Bool) vals' lvl' rsns' trl' te' c0' c1' asz' m',
        let st' : FullState :=
          { st with
            core := { st.core with
              vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_end := te',
              confl_lit0 := c0', confl_lit1 := c1' }
            scratch := { st.scratch with ant_sz := asz' } }
        BbTrailInv c F0 F_cur s0 st' saved0 max_lvl →
        st.core.trail_end ≤ te' →
        (∀ i < st.core.trail_end, trl'[i]? = st.core.trl[i]?) →
        (∀ i < st.core.trail_end,
          let v := (st.core.trl[i]?.getD 0#32).toNat / 2
          lvl'[v]? = st.core.lvl[v]? ∧ rsns'[v]? = st.core.rsns[v]?) →
        (∀ saved, saved0 ≤ saved → saved ≤ prop_start.toNat → 0 < st.core.cur_level →
          BackboneProbeSeg F_cur st saved st.core.cur_level →
          BackboneProbeSeg F_cur st' saved st.core.cur_level) →
        (ok = false →
          c0'.toNat < 2 * s0.core.cur_vars ∧ c1'.toNat < 2 * s0.core.cur_vars ∧
          vals'[c0'.toNat]?.getD 0#8 = 0xFF#8 ∧ vals'[c1'.toNat]?.getD 0#8 = 0xFF#8 ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause [c0'.toNat, c1'.toNat]) ∧
          ∃ idx0, prop_start.toNat ≤ idx0 ∧ idx0 < te' ∧
            (trl'[idx0]?.getD 0#32).toNat = c0'.toNat ^^^ 1) →
        (FullMem c st' ⋆ R) m' → Q (ok, ()) m'

/-! ## 2. Shared Pure Helpers -/

section Helpers

private theorem s13_bv32_lshr1 (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  change (x >>> (1 : Nat)).toNat = x.toNat / 2
  rw [BitVec.toNat_ushiftRight]; simp [Nat.shiftRight_eq_div_pow]

private theorem s13_nodup_mem_erase_ne :
    ∀ {xs : List Nat} {n y : Nat}, xs.Nodup → y ∈ xs.erase n → y ≠ n
  | [], _, _, _, h => nomatch h
  | a :: t, n, y, hnd, hy => by
    have hcons := List.nodup_cons.mp hnd
    by_cases ha : a = n
    · subst ha
      rw [List.erase_cons_head] at hy
      intro hyn; subst hyn; exact hcons.1 hy
    · have hne : (a == n) = false := beq_false_of_ne ha
      simp only [List.erase_cons, hne] at hy
      rcases List.mem_cons.mp hy with rfl | ht
      · exact ha
      · exact s13_nodup_mem_erase_ne hcons.2 ht

private theorem s13_nodup_lt_len_le :
    ∀ (n : Nat) (xs : List Nat), xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n
  | 0, [], _, _ => Nat.zero_le _
  | 0, x :: _, _, hx => absurd (hx x List.mem_cons_self) (Nat.not_lt_zero _)
  | n + 1, xs, hnd, hx => by
    by_cases hmem : n ∈ xs
    · have hlt : (xs.erase n).length ≤ n := by
        refine s13_nodup_lt_len_le n (xs.erase n) (hnd.erase n) fun y hy => ?_
        have hy_xs := List.mem_of_mem_erase hy
        have hy_ne := s13_nodup_mem_erase_ne hnd hy
        have := hx y hy_xs; omega
      rw [List.length_erase_of_mem hmem] at hlt
      have hpos : 0 < xs.length := List.length_pos_of_mem hmem
      omega
    · exact Nat.le_trans
        (s13_nodup_lt_len_le n xs hnd fun y hy => by
          have hy_lt := hx y hy
          have hy_ne : y ≠ n := fun he => hmem (he ▸ hy)
          omega)
        (Nat.le_succ n)

private theorem s13_noMark_with_min_clr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : S13SparseInvNoMark c F0 F_cur s) {mc' : List (BitVec 32)}
    (hmc : mc'.length = c.max_vars) :
    S13SparseInvNoMark c F0 F_cur { s with core := { s.core with min_clr := mc' } } :=
  ⟨⟨{ hsp.1.core_ok with min_clr_len_arr := hmc }, hsp.1.scratch_ok⟩,
    { hsp.2.1 with
      arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
      watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
    hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2⟩

private theorem s13_noMark_set_hdr_non_gs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : S13SparseInvNoMark c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (v : BitVec 32)
    (ni' nr' : BitVec 64)
    (h19 : (v &&& 0x00080000#32) = (fullArenaHdr s cref &&& 0x00080000#32))
    (h23 : (v &&& 0x00800000#32) = (fullArenaHdr s cref &&& 0x00800000#32)) :
    let s' : FullState :=
      { s with core :=
        { s.core with arena := s.core.arena.set cref v,
                      num_irred := ni', num_redundant := nr' } }
    S13SparseInvNoMark c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) := by
  intro s'
  obtain ⟨hlen_c, hrefs, hw', hall⟩ :=
    fullWitnessInv_set_hdr_non_gs hsp.1.core_ok hsp.2.1 href v h19 h23
  have hlen' : s'.LengthsOk c := ⟨{ hlen_c with }, hsp.1.scratch_ok⟩
  have hw_s' : FullWitnessInv c F0 F_cur s'.core :=
    { hw' with
      arena := { hw'.arena with len_ok := hw'.arena.len_ok }
      watches := hw'.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  have hrefs' : fullArenaClauseRefs s' = fullArenaClauseRefs s := hrefs
  have hnd' : FullArenaVarsNodup s' := fun r hr hng => by
    have hr0 : r ∈ fullArenaClauseRefs s := hrefs' ▸ hr
    obtain ⟨hg, _, hl⟩ := hall r hr0
    have hl' : fullArenaClauseLits s' r = fullArenaClauseLits s r := hl
    have hg' : fullArenaClauseGarb s' r = fullArenaClauseGarb s r := hg
    rw [hl']; exact hsp.2.2.1 r hr0 (hg'.symm.trans hng)
  have hext' : FullExtScratchOk c s' :=
    ⟨fun i hi => (hsp.2.2.2.1.1 i hi).imp id (fun h => hrefs' ▸ h), hsp.2.2.2.1.2⟩
  exact ⟨⟨hlen', hw_s', hnd', hext', hsp.2.2.2.2⟩, hrefs', hall⟩

private theorem s13_mask31_bit :
    ∀ j : Fin 32, (0x80000000#32)[j.val] = decide (j.val = 31) := by decide
private theorem s13_maskN31_bit :
    ∀ j : Fin 32, (0x7FFFFFFF#32)[j.val] = decide (j.val ≠ 31) := by decide
private theorem s13_mask19_bit :
    ∀ j : Fin 32, (0x00080000#32)[j.val] = decide (j.val = 19) := by decide
private theorem s13_mask23_bit :
    ∀ j : Fin 32, (0x00800000#32)[j.val] = decide (j.val = 23) := by decide
private theorem s13_maskN19_bit :
    ∀ j : Fin 32, (~~~0x7FFFF#32)[j.val] = decide (19 ≤ j.val) := by decide

private theorem s13_bv32_bit31_clr_of_lt {x : BitVec 32} (hx : x.toNat < 2 ^ 31) :
    (x &&& 0x80000000#32) = 0#32 := by
  have hmsb : x[31] = false := by
    have hdiv : x.toNat / 2 ^ 31 = 0 := Nat.div_eq_of_lt hx
    simp [BitVec.getElem_eq_testBit_toNat, Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
  ext i hi
  simp only [BitVec.getElem_and, s13_mask31_bit ⟨i, hi⟩]
  by_cases h31 : i = 31
  · subst h31; simp [hmsb]
  · simp [h31]

private theorem s13_bv32_or_and_cancel {x : BitVec 32} (h31 : (x &&& 0x80000000#32) = 0#32) :
    ((x ||| 0x80000000#32) &&& 0x7FFFFFFF#32) = x := by
  have hmsb : x[31] = false := by
    have h := congrArg (·[31]) h31
    simpa using h
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, s13_mask31_bit ⟨i, hi⟩,
    s13_maskN31_bit ⟨i, hi⟩]
  by_cases h31' : i = 31
  · subst h31'; simp [hmsb]
  · simp [h31']

private theorem s13_bv32_lt19_bit {ng : BitVec 32} (hng : ng.toNat < 2 ^ 19)
    {k : Nat} (hk19 : 19 ≤ k) : ng[k]? = if k < 32 then some false else none := by
  by_cases hk : k < 32
  · simp only [hk, ↓reduceIte, BitVec.getElem?_eq_getElem]
    congr 1
    have hdiv : ng.toNat / 2 ^ k = 0 :=
      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hng (Nat.pow_le_pow_right (by omega) hk19))
    simp [BitVec.getElem_eq_testBit_toNat, Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
  · simp [hk]

private theorem s13_bv32_set_glue_h19 {hdr ng : BitVec 32} (hng : ng.toNat < 2 ^ 19) :
    (((hdr &&& ~~~0x7FFFF#32) ||| ng) &&& 0x00080000#32) = (hdr &&& 0x00080000#32) := by
  have hng19 : ng[19] = false := by
    have h := s13_bv32_lt19_bit hng (k := 19) (by omega)
    simpa [BitVec.getElem?_eq_getElem] using h
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, s13_mask19_bit ⟨i, hi⟩,
    s13_maskN19_bit ⟨i, hi⟩]
  by_cases h19 : i = 19
  · subst h19; simp [hng19]
  · simp [h19]

private theorem s13_bv32_set_glue_h23 {hdr ng : BitVec 32} (hng : ng.toNat < 2 ^ 19) :
    (((hdr &&& ~~~0x7FFFF#32) ||| ng) &&& 0x00800000#32) = (hdr &&& 0x00800000#32) := by
  have hng23 : ng[23] = false := by
    have h := s13_bv32_lt19_bit hng (k := 23) (by omega)
    simpa [BitVec.getElem?_eq_getElem] using h
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, s13_mask23_bit ⟨i, hi⟩,
    s13_maskN19_bit ⟨i, hi⟩]
  by_cases h23 : i = 23
  · subst h23; simp [hng23]
  · simp [h23]

end Helpers

/-! ## 3. `full_viv_recompute_promote_fid_s5_wp` (`ADD`) -/

section PromoteAndMarkGarb

private theorem s13_viv_promote_restore_wp {Γ : Env} {Q : Post []} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {cref hdr glue : BitVec 32} {ng : BitVec 64}
    {ftrl' mclr' : List (BitVec 32)} {m0 : Mem 64}
    (hsp : S13SparseInvNoMark c F0 F_cur s) (href : cref.toNat ∈ fullArenaClauseRefs s)
    (hmx : c.max_vars < 2 * dimacsBound) (_harc : c.arena_cap < 2 * dimacsBound)
    (hcr0_lt : cref.toNat < s.core.arena.length)
    (hhdr : hdr = s.core.arena[cref.toNat]'hcr0_lt)
    (hglue_eq : glue = hdr &&& 0x7FFFF#32)
    (hng_le : ng.toNat ≤ c.max_vars)
    (hftrl_len : ftrl'.length = c.max_vars + 1) (hmclr_len : mclr'.length = c.max_vars)
    (hmark : ∀ j < ng.toNat,
      (mclr'[j]?.getD 0#32).toNat ≤ s.core.cur_level ∧
      (ftrl'[(mclr'[j]?.getD 0#32).toNat]?.getD 0#32) =
        ((s.core.frame_trail[(mclr'[j]?.getD 0#32).toNat]?.getD 0#32) ||| 0x80000000#32))
    (hunmarked : ∀ i < c.max_vars + 1,
      (∀ j < ng.toNat, (mclr'[j]?.getD 0#32).toNat ≠ i) →
      ftrl'[i]? = s.core.frame_trail[i]?)
    (hdistinct : ∀ j1 j2, j1 < j2 → j2 < ng.toNat →
      (mclr'[j1]?.getD 0#32).toNat ≠ (mclr'[j2]?.getD 0#32).toNat)
    (hm0 : (FullMem c { s with core := { s.core with frame_trail := ftrl', min_clr := mclr' } }
      ⋆ R) m0)
    (hQ : ∀ ar' mclr' m',
      let s' : FullState := { s with core := { s.core with arena := ar', min_clr := mclr' } }
      S13SparseInvNoMark c F0 F_cur s' → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s,
        fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
        fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
        fullArenaClauseLits s' r = fullArenaClauseLits s r) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X
      (Expr.group (sig := [[i64]])
        (fun Ju => Blocks.cons (fun pu =>
          Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var pu.fst, Arg.var ng, ())) fun c_u =>
          Expr.jnz (Arg.var c_u.fst)
            (Expr.let_ (Op.mk (.mul i64) (Arg.var pu.fst, Arg.imm 4, ())) fun o1 =>
             Expr.let_ (Op.mk (.add i64) (Arg.var c.pMinClr, Arg.var o1.fst, ())) fun pm =>
             Expr.load i32 (Arg.var pm.fst) fun ml =>
             Expr.let_ (Op.mk (.zext 32 64) (Arg.var ml, ())) fun ml64 =>
             Expr.let_ (Op.mk (.mul i64) (Arg.var ml64.fst, Arg.imm 4, ())) fun o2 =>
             Expr.let_ (Op.mk (.add i64) (Arg.var c.pFrameTrail, Arg.var o2.fst, ())) fun pf1 =>
             Expr.let_ (Op.mk (.zext 32 64) (Arg.var ml, ())) fun ml64b =>
             Expr.let_ (Op.mk (.mul i64) (Arg.var ml64b.fst, Arg.imm 4, ())) fun o2b =>
             Expr.let_ (Op.mk (.add i64) (Arg.var c.pFrameTrail, Arg.var o2b.fst, ())) fun pf2 =>
             Expr.load i32 (Arg.var pf2.fst) fun fv =>
             Expr.let_ (Op.mk (.and i32) (Arg.var fv, Arg.imm 2147483647, ())) fun nfv =>
             Expr.store (Arg.var nfv.fst) (Arg.var pf1.fst)
               (Expr.let_ (Op.mk (.add i64) (Arg.var pu.fst, Arg.imm 1, ())) fun u1 =>
                Expr.jump Ju.fst (Arg.var u1.fst, ())))
            (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) => Expr.ret ())
               Blocks.nil) fun Jg0 =>
             Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var ng, Arg.imm 0, ())) fun cg0 =>
             Expr.jnz (Arg.var cg0.fst)
               (Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                    (Arg.var ng, Arg.var (glue.setWidth 64), ()))
                  fun cng =>
                Expr.jnz (Arg.var cng.fst)
                  (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun cr64 =>
                   Expr.let_ (Op.mk (.mul i64) (Arg.var cr64.fst, Arg.imm 4, ())) fun o3 =>
                   Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var o3.fst, ())) fun pa =>
                   Expr.let_ (Op.mk (.not i32) (Arg.imm 524287, ())) fun hclr =>
                   Expr.let_ (Op.mk (.and i32) (Arg.var hdr, Arg.var hclr.fst, ())) fun hclrd =>
                   Expr.let_ (Op.mk (.trunc 64 32) (Arg.var ng, ())) fun ng32 =>
                   Expr.let_ (Op.mk (.or i32) (Arg.var hclrd.fst, Arg.var ng32.fst, ())) fun nhdr =>
                   Expr.store (Arg.var nhdr.fst) (Arg.var pa.fst) (Expr.jump Jg0.fst ()))
                  (Expr.jump Jg0.fst ()))
               (Expr.jump Jg0.fst ()))) Blocks.nil)
        fun Ju => Expr.jump Ju.fst (Arg.imm 0, ())) m0 := by
  have hcl := hsp.1.core_ok; have hw := hsp.2.1; have _hcv := hcl.cur_vars_le
  have hcl_le : s.core.cur_level ≤ c.max_vars := by
    have := hw.cur_level_le; have := hcl.trail_end_le; omega
  refine wp_loop_inv (ts := [i64])
    (fun (ui, ()) mu => ui.toNat ≤ ng.toNat ∧ ∃ fu : List (BitVec 32),
      fu.length = c.max_vars + 1 ∧
      (∀ j, ui.toNat ≤ j → j < ng.toNat →
        fu[(mclr'[j]?.getD 0#32).toNat]?.getD 0#32 =
          ((s.core.frame_trail[(mclr'[j]?.getD 0#32).toNat]?.getD 0#32) ||| 0x80000000#32)) ∧
      (∀ i < c.max_vars + 1,
        (∀ j, ui.toNat ≤ j → j < ng.toNat → (mclr'[j]?.getD 0#32).toNat ≠ i) →
        fu[i]? = s.core.frame_trail[i]?) ∧
      (FullMem c { s with core := { s.core with frame_trail := fu, min_clr := mclr' } } ⋆ R) mu)
    (fun (ui, ()) _ => ng.toNat - ui.toNat)
    (fun Ju hJu => by
      c0_hfast_nogrp
      exact hJu (0#64, ()) m0 ⟨Nat.zero_le _, ftrl', hftrl_len,
        fun j _ hj => (hmark j hj).2,
        fun i hi hall => hunmarked i hi (fun j hj => hall j (Nat.zero_le _) hj),
        hm0⟩)
    (fun Ju (ui, ()) mu ⟨hui_le, fu, hfu_len, hmk_u, hunm_u, hmu⟩ ihu => ?_)
  · c0_hfast_nogrp
    · have hui_lt : ui.toNat < ng.toNat := BitVec.lt_def.mp (by assumption)
      have hui1 : (ui + 1#64).toNat = ui.toNat + 1 := by bv_omega
      have hui_mc : ui.toNat < mclr'.length := by rw [hmclr_len]; omega
      let ml := mclr'[ui.toNat]'hui_mc
      have hml_lvl : ml.toNat ≤ s.core.cur_level := by
        have h1 := (hmark ui.toNat hui_lt).1
        rwa [List.getElem?_eq_getElem hui_mc, Option.getD_some] at h1
      have hml_ft : ml.toNat < fu.length := by rw [hfu_len]; omega
      have hml_ft0 : ml.toNat < s.core.frame_trail.length := by rw [hcl.frame_trail_len]; omega
      have hft0_lt : (s.core.frame_trail[ml.toNat]?.getD 0#32).toNat < 2 ^ 31 := by
        have h1 := hw.frame_trail_lt ml.toNat hml_lvl
        have := hcl.trail_end_le; unfold dimacsBound at hmx; omega
      have hfu_ml : fu[ml.toNat]'hml_ft =
          ((s.core.frame_trail[ml.toNat]'hml_ft0) ||| 0x80000000#32) := by
        have h1 := hmk_u ui.toNat (Nat.le_refl _) hui_lt
        rw [List.getElem?_eq_getElem hui_mc, Option.getD_some,
          List.getElem?_eq_getElem hml_ft, Option.getD_some,
          List.getElem?_eq_getElem hml_ft0, Option.getD_some] at h1
        exact h1
      have hclr_eq : ((fu[ml.toNat]'hml_ft) &&& 0x7FFFFFFF#32) =
          s.core.frame_trail[ml.toNat]'hml_ft0 := by
        rw [hfu_ml]
        refine s13_bv32_or_and_cancel (s13_bv32_bit31_clr_of_lt ?_)
        rwa [List.getElem?_eq_getElem hml_ft0, Option.getD_some] at hft0_lt
      c0_hfast_nogrp
      refine ihu (ui + 1#64, ()) _ (by dsimp only; rw [hui1]; omega)
        ⟨by rw [hui1]; omega,
          fu.set (BitVec.setWidth 64 ml).toNat (fu[ml.toNat]'hml_ft &&& 2147483647),
          by rw [List.length_set, hfu_len], ?_, ?_, by assumption⟩
      · intro j hj1 hj2
        have hne : ml.toNat ≠ (mclr'[j]?.getD 0#32).toNat := by
          have h1 := hdistinct ui.toNat j (by omega) hj2
          rwa [List.getElem?_eq_getElem hui_mc, Option.getD_some] at h1
        have hne64 : (BitVec.setWidth 64 ml).toNat ≠ (mclr'[j]?.getD 0#32).toNat := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans ml.isLt (by decide))]
          exact hne
        rw [List.getElem?_set_ne hne64]
        exact hmk_u j (by omega) hj2
      · intro i hi hall
        by_cases him : i = ml.toNat
        · subst him
          have hidx : (BitVec.setWidth 64 ml).toNat = ml.toNat := by bv_omega
          have hset_self :
              (fu.set (BitVec.setWidth 64 ml).toNat
                (fu[ml.toNat]'hml_ft &&& 2147483647))[ml.toNat]? =
              some (fu[ml.toNat]'hml_ft &&& 2147483647) := by
            simp only [hidx, List.getElem?_set_self hml_ft]
          rw [hset_self, List.getElem?_eq_getElem hml_ft0]
          exact congrArg some (by
            simpa only [show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl] using hclr_eq)
        · have hidx : (BitVec.setWidth 64 ml).toNat ≠ i := by bv_omega
          rw [List.getElem?_set_ne hidx]
          refine hunm_u i hi fun j hj1 hj2 => ?_
          by_cases hju : j = ui.toNat
          · subst hju
            simpa [ml, List.getElem?_eq_getElem hui_mc, Option.getD_some] using Ne.symm him
          · exact hall j (by omega) hj2
    · clear ihu
      have hui_ge : ng.toNat ≤ ui.toNat :=
        Nat.le_of_not_lt fun h => (by assumption : ¬ ui < ng) (BitVec.lt_def.mpr h)
      have hfu_eq : fu = s.core.frame_trail := by
        apply List.ext_getElem (by rw [hfu_len, hcl.frame_trail_len])
        intro i hi1 hi2
        have h1 := hunm_u i (by rw [← hfu_len]; exact hi1) (fun j hj1 hj2 => by omega)
        rw [List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2] at h1
        exact Option.some.inj h1
      rw [hfu_eq] at hmu
      let smc : FullState := { s with core := { s.core with min_clr := mclr' } }
      have hsp_mc : S13SparseInvNoMark c F0 F_cur smc := s13_noMark_with_min_clr hsp hmclr_len
      have href_mc : cref.toNat ∈ fullArenaClauseRefs smc := href
      have hhdr_mc : fullArenaHdr smc cref.toNat = hdr := by
        unfold fullArenaHdr fullArenaHdrCore; dsimp only [smc]
        rw [hhdr, List.getElem?_eq_getElem hcr0_lt, Option.getD_some]
      refine wp_join_group (ts := []) (fun _ mf =>
          ∃ ar' mclr',
            let s' : FullState := { s with core := { s.core with arena := ar', min_clr := mclr' } }
            S13SparseInvNoMark c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
            (∀ r ∈ fullArenaClauseRefs s,
              fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
              fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
              fullArenaClauseLits s' r = fullArenaClauseLits s r) ∧
            (FullMem c s' ⋆ R) mf)
        (fun _ _ mf ⟨ar', mclr', h1, h2, h3, h4⟩ => by
          c0_hfast; exact hQ ar' mclr' mf h1 h2 h3 h4)
        (fun Jg0 hJg0 => by
          c0_hfast_nogrp
          · have hglue_lt : glue.toNat < 2 ^ 19 := by
              rw [hglue_eq, BitVec.toNat_and]
              exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
            have hng_lt_g : ng.toNat < glue.toNat := by
              have h1 : ng < glue.setWidth 64 := by assumption
              have h2 := BitVec.lt_def.mp h1
              rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)] at h2
            have hng_19 : (BitVec.setWidth 32 ng).toNat < 2 ^ 19 := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; omega
            have hcr_ar : (BitVec.setWidth 64 cref).toNat < s.core.arena.length := by bv_omega
            let nhdr := (hdr &&& ~~~0x7FFFF#32) ||| BitVec.setWidth 32 ng
            have hset := s13_noMark_set_hdr_non_gs hsp_mc href_mc nhdr s.core.num_irred
              s.core.num_redundant (by rw [hhdr_mc]; exact s13_bv32_set_glue_h19 hng_19)
              (by rw [hhdr_mc]; exact s13_bv32_set_glue_h23 hng_19)
            have h429 : ~~~(524287#32 : BitVec 32) = ~~~0x7FFFF#32 := rfl
            have hcr_idx : (BitVec.setWidth 64 cref).toNat = cref.toNat := by bv_omega
            refine hJg0 () _ ⟨_, mclr', hset.1, hset.2.1, hset.2.2, ?_⟩
            simpa only [nhdr, h429, hcr_idx, smc] using by assumption
          · exact hJg0 () _ ⟨s.core.arena, mclr', hsp_mc, rfl, (fun _ _ => ⟨rfl, rfl, rfl⟩), hmu⟩
          · exact hJg0 () _ ⟨s.core.arena, mclr', hsp_mc, rfl, (fun _ _ => ⟨rfl, rfl, rfl⟩), hmu⟩)

theorem full_viv_recompute_promote_fid_s5_wp (Γ : Env) :
    ∀ args m Q X, step13VivRecomputePromoteSpec args m Q X →
      Func.wp Γ FullFidelityStep13S5VivifyBackbone.full_viv_recompute_promote_fid_body
        args m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp, href, hng, hm0, hQ⟩
  have hmx := c.hmaxv; have harc := c.harena; unfold dimacsBound at hmx harc
  have hcl := hsp.1.core_ok; have hsc := hsp.1.scratch_ok; have hw := hsp.2.1
  have hwf := hw.arena.refs_wf cref.toNat href
  have hbd : cref.toNat + 3 + fullArenaClauseSizeCore s.core cref.toNat ≤ s.core.arena.length := by
    have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
  have hcr0_lt : cref.toNat < s.core.arena.length := by
    have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
  have hcr2_eq : (BitVec.setWidth 64 cref + 2#64).toNat = cref.toNat + 2 := by bv_omega
  have hcr2_lt : (BitVec.setWidth 64 cref + 2#64).toNat < s.core.arena.length := by
    have := hwf.2.1; omega
  let hdr := s.core.arena[cref.toNat]'hcr0_lt
  let sz := s.core.arena[(BitVec.setWidth 64 cref + 2#64).toNat]'hcr2_lt
  have hsz_eq : sz.toNat = fullArenaClauseSize s cref.toNat := by
    unfold fullArenaClauseSize fullArenaClauseSizeCore; dsimp only [sz]
    rw [← hcr2_eq, List.getElem?_eq_getElem hcr2_lt, Option.getD_some]
  have hsz_le_cv : sz.toNat ≤ s.core.cur_vars := by
    have hlits_len : (fullArenaClauseLits s cref.toNat).length = sz.toNat := by
      rw [hsz_eq]; unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
      simp only [List.length_map, List.length_take, List.length_drop]
      have h1 :
          fullArenaClauseSizeCore s.core cref.toNat ≤ s.core.arena.length - (cref.toNat + 3) := by
        have := hwf.2.2.1; have := hcl.arena_len_le; have := hcl.arena_len_arr
        unfold fullArenaClauseSizeCore at *; omega
      unfold fullArenaClauseSizeCore at h1
      exact Nat.min_eq_left h1
    have hnd : ((fullArenaClauseLits s cref.toNat).map (· / 2)).Nodup :=
      hsp.2.2.1 cref.toNat href hng
    have hlt : ∀ v ∈ (fullArenaClauseLits s cref.toNat).map (· / 2), v < s.core.cur_vars := by
      intro v hv
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
      have := hw.arena.lits_lt cref.toNat href hng l hl; omega
    have hle := s13_nodup_lt_len_le s.core.cur_vars _ hnd hlt
    simpa [hlits_len] using hle
  have hsz_le_mv : sz.toNat ≤ c.max_vars := Nat.le_trans hsz_le_cv hcl.cur_vars_le
  have hcl_le : s.core.cur_level ≤ c.max_vars := by
    have := hw.cur_level_le; have := hcl.trail_end_le; have := hcl.cur_vars_le; omega
  unfold Func.wp FullFidelityStep13S5VivifyBackbone.full_viv_recompute_promote_fid_body
  c0_hfast_nogrp
  all_goals try
    exact hQ s.core.arena s.core.min_clr m0 hsp rfl (fun _ _ => ⟨rfl, rfl, rfl⟩) hm0
  · have hcr0_64 : (BitVec.setWidth 64 cref).toNat < s.core.arena.length := by bv_omega
    generalize hhdr_gv : s.core.arena[(BitVec.setWidth 64 cref).toNat]'hcr0_64 = hdr_v
    have hhdr_eq : hdr_v = s.core.arena[cref.toNat]'hcr0_lt := by
      rw [← hhdr_gv]
      simp only [BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (Nat.lt_trans cref.isLt (by decide : 2 ^ 32 < 2 ^ 64))]
    dsimp only
    refine wp_join_group (ts := [i64, i32])
      (fun (ng, _k, ()) mp => ng.toNat ≤ sz.toNat ∧ ∃ ftrl' mclr',
        ftrl'.length = c.max_vars + 1 ∧ mclr'.length = c.max_vars ∧
        (∀ j < ng.toNat, (mclr'[j]?.getD 0#32).toNat ≤ s.core.cur_level ∧
          (ftrl'[(mclr'[j]?.getD 0#32).toNat]?.getD 0#32) =
            ((s.core.frame_trail[(mclr'[j]?.getD 0#32).toNat]?.getD 0#32) ||| 0x80000000#32)) ∧
        (∀ i < c.max_vars + 1, (∀ j < ng.toNat, (mclr'[j]?.getD 0#32).toNat ≠ i) →
          ftrl'[i]? = s.core.frame_trail[i]?) ∧
        (∀ j1 j2, j1 < j2 → j2 < ng.toNat →
          (mclr'[j1]?.getD 0#32).toNat ≠ (mclr'[j2]?.getD 0#32).toNat) ∧
        (FullMem c { s with core := { s.core with frame_trail := ftrl', min_clr := mclr' } }
          ⋆ R) mp)
      (fun _ (ng, _k, ()) mp ⟨hng_le, ftrl', mclr', hftrl, hmclr, hmk, hunm, hdist, hmp⟩ => by
        refine s13_viv_promote_restore_wp hsp href hmx harc hcr0_lt hhdr_eq rfl
          (Nat.le_trans hng_le hsz_le_mv) hftrl hmclr hmk hunm hdist hmp hQ)
      (fun Jbrk hJbrk => ?_)
    refine wp_loop_inv (ts := [i64, i32])
      (fun (ng, k, ()) mk => k.toNat ≤ sz.toNat ∧ ng.toNat ≤ k.toNat ∧ ∃ ftrl' mclr',
        ftrl'.length = c.max_vars + 1 ∧ mclr'.length = c.max_vars ∧
        (∀ j < ng.toNat, (mclr'[j]?.getD 0#32).toNat ≤ s.core.cur_level ∧
          (ftrl'[(mclr'[j]?.getD 0#32).toNat]?.getD 0#32) =
            ((s.core.frame_trail[(mclr'[j]?.getD 0#32).toNat]?.getD 0#32) ||| 0x80000000#32)) ∧
        (∀ i < c.max_vars + 1, (∀ j < ng.toNat, (mclr'[j]?.getD 0#32).toNat ≠ i) →
          ftrl'[i]? = s.core.frame_trail[i]?) ∧
        (∀ j1 j2, j1 < j2 → j2 < ng.toNat →
          (mclr'[j1]?.getD 0#32).toNat ≠ (mclr'[j2]?.getD 0#32).toNat) ∧
        (FullMem c { s with core := { s.core with frame_trail := ftrl', min_clr := mclr' } }
          ⋆ R) mk)
      (fun (_, k, ()) _ => sz.toNat - k.toNat)
      (fun Jk hJk => by
        c0_hfast_nogrp
        exact hJk (0#64, 0#32, ()) m0 ⟨Nat.zero_le _, Nat.zero_le _, s.core.frame_trail,
          s.core.min_clr, hcl.frame_trail_len, hcl.min_clr_len_arr,
          (fun _ h => absurd h (Nat.not_lt_zero _)), (fun _ _ _ => rfl),
          (fun _ _ _ h => absurd h (Nat.not_lt_zero _)), hm0⟩)
      (fun Jk (ng, k, ()) mk ⟨hk_le, hng_le, ftrl', mclr', hftrl, hmclr, hmk, hunm, hdist, hmk_m⟩
          ihk => ?_)
    c0_hfast_nogrp
    · have hk_lt : k.toNat < sz.toNat := BitVec.lt_def.mp (by assumption)
      have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
      have hk_sz : k.toNat < fullArenaClauseSizeCore s.core cref.toNat := by
        show k.toNat < fullArenaClauseSize s cref.toNat; exact hsz_eq ▸ hk_lt
      have hidx_eq : (cref.toNat + 3 + k.toNat) % 2 ^ 64 = cref.toNat + 3 + k.toNat := by
        have := hwf.2.2.1; have := hcl.arena_len_le; omega
      have hidx_lt : (cref.toNat + 3 + k.toNat) % 2 ^ 64 < s.core.arena.length := by
        rw [hidx_eq]; have := hwf.2.2.1; have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
      let kl_lit := s.core.arena[(cref.toNat + 3 + k.toNat) % 2 ^ 64]'hidx_lt
      have hkv_lt_bv : ((kl_lit >>> 1).setWidth 64).toNat < s.core.cur_vars := by
        have hmem_l : kl_lit.toNat ∈ fullArenaClauseLitsCore s.core cref.toNat := by
          dsimp only [kl_lit]; simp only [hidx_eq]
          exact (mem_fullArenaClauseLitsCore_iff hbd).mpr ⟨k.toNat, hk_sz, rfl⟩
        have hlt := hw.arena.lits_lt cref.toNat href hng _ hmem_l
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by bv_omega), BitVec.toNat_ushiftRight,
          Nat.shiftRight_eq_div_pow]
        omega
      have hkv_lvl : ((kl_lit >>> 1).setWidth 64).toNat < s.core.lvl.length := by
        rw [hcl.lvl_len]; exact Nat.lt_of_lt_of_le hkv_lt_bv hcl.cur_vars_le
      c0_hfast_nogrp
      refine wp_join_group (ts := [i64])
        (fun (ng', ()) mk' => ng'.toNat ≤ k.toNat + 1 ∧ ∃ ftrl'' mclr'',
          ftrl''.length = c.max_vars + 1 ∧ mclr''.length = c.max_vars ∧
          (∀ j < ng'.toNat, (mclr''[j]?.getD 0#32).toNat ≤ s.core.cur_level ∧
            (ftrl''[(mclr''[j]?.getD 0#32).toNat]?.getD 0#32) =
              ((s.core.frame_trail[(mclr''[j]?.getD 0#32).toNat]?.getD 0#32) ||| 0x80000000#32)) ∧
          (∀ i < c.max_vars + 1, (∀ j < ng'.toNat, (mclr''[j]?.getD 0#32).toNat ≠ i) →
            ftrl''[i]? = s.core.frame_trail[i]?) ∧
          (∀ j1 j2, j1 < j2 → j2 < ng'.toNat →
            (mclr''[j1]?.getD 0#32).toNat ≠ (mclr''[j2]?.getD 0#32).toNat) ∧
          (FullMem c { s with core := { s.core with frame_trail := ftrl'', min_clr := mclr'' } }
            ⋆ R) mk')
        (fun _ (ng', ()) mk' ⟨hng'_le, ftrl'', mclr'', hftrl'', hmclr'', hmk'', hunm'', hdist'',
            hmk'_m⟩ => by
          c0_hfast
          exact ihk (ng', k + 1#32, ()) mk' (by dsimp only; omega)
            ⟨by omega, by omega, ftrl'', mclr'', hftrl'', hmclr'', hmk'', hunm'', hdist'', hmk'_m⟩)
        (fun Js hJs => ?_)
      c0_hsplit
      · c0_hfast_nogrp
        refine wp_join_group (ts := [i64])
          (fun (ng', ()) mk' => ng'.toNat ≤ k.toNat + 1 ∧ ∃ ftrl'' mclr'',
            ftrl''.length = c.max_vars + 1 ∧ mclr''.length = c.max_vars ∧
            (∀ j < ng'.toNat, (mclr''[j]?.getD 0#32).toNat ≤ s.core.cur_level ∧
              (ftrl''[(mclr''[j]?.getD 0#32).toNat]?.getD 0#32) =
                ((s.core.frame_trail[(mclr''[j]?.getD 0#32).toNat]?.getD 0#32) ||| 0x80000000#32)) ∧
            (∀ i < c.max_vars + 1, (∀ j < ng'.toNat, (mclr''[j]?.getD 0#32).toNat ≠ i) →
              ftrl''[i]? = s.core.frame_trail[i]?) ∧
            (∀ j1 j2, j1 < j2 → j2 < ng'.toNat →
              (mclr''[j1]?.getD 0#32).toNat ≠ (mclr''[j2]?.getD 0#32).toNat) ∧
            (FullMem c { s with core := { s.core with frame_trail := ftrl'', min_clr := mclr'' } }
              ⋆ R) mk')
          (fun _ (ng', ()) mk' ⟨hng'_le, ftrl'', mclr'', hftrl'', hmclr'', hmk'', hunm'', hdist'',
              hmk'_m⟩ => by
            c0_hfast; exact hJs (ng', ()) mk' ⟨hng'_le, ftrl'', mclr'', hftrl'', hmclr'', hmk'',
              hunm'', hdist'', hmk'_m⟩)
          (fun Js1 hJs1 => ?_)
        c0_hsplit
        · let kl_bv := (s.core.lvl[((kl_lit >>> 1).setWidth 64).toNat]'hkv_lvl).setWidth 64
          have hkl_le : kl_bv.toNat ≤ s.core.cur_level := by
            have hidx_l : ((kl_lit >>> 1).setWidth 64).toNat = kl_lit.toNat / 2 := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by bv_omega),
                BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
            have hcl_u64 : s.core.cur_level < 2 ^ 64 := by omega
            dsimp only [kl_bv]
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by bv_omega)]
            simpa only [kl_lit, hidx_l, Nat.mod_eq_of_lt hcl_u64] using (by assumption :
              s.core.lvl[s.core.arena[(cref.toNat + 3 + k.toNat) % 2 ^ 64].toNat / 2].toNat ≤
                s.core.cur_level % 2 ^ 64)
          have hkl_ft : kl_bv.toNat < ftrl'.length := by rw [hftrl]; omega
          have hidx_sw : (BitVec.setWidth 64 cref + 3 + BitVec.setWidth 64 k).toNat =
              (cref.toNat + 3 + k.toNat) % 2 ^ 64 := by bv_omega
          let s_mk : FullState :=
            { s with core := { s.core with frame_trail := ftrl', min_clr := mclr' } }
          have hkl_ft_sw : (BitVec.setWidth 64 (s_mk.core.lvl[(BitVec.setWidth 64
              (s_mk.core.arena[(BitVec.setWidth 64 cref + 3 + BitVec.setWidth 64 k).toNat]'
                (by dsimp only [s_mk]; simp only [hidx_sw]; exact hidx_lt) >>> 1)).toNat]'
              (by dsimp only [s_mk]; simp only [hidx_sw]; exact hkv_lvl))).toNat <
              s_mk.core.frame_trail.length := by
            dsimp only [s_mk]; simp only [hidx_sw]; exact hkl_ft
          let ar1 := s.core.arena[(BitVec.setWidth 64 cref + 3 +
              BitVec.setWidth 64 k).toNat]'(by simp only [hidx_sw]; exact hidx_lt)
          have har_sw : ar1 = kl_lit := by
            dsimp only [ar1, kl_lit]
            rw [← Option.some_inj, ← List.getElem?_eq_getElem _, ← List.getElem?_eq_getElem _]
            exact congrArg (s.core.arena[·]?) hidx_sw
          let b1 := BitVec.setWidth 64 (s.core.lvl[(BitVec.setWidth 64
            (ar1 >>> OfNat.ofNat 1)).toNat]'(by rw [har_sw]; exact hkv_lvl))
          have hkl_sw : b1 = kl_bv := by
            dsimp only [b1, kl_bv]
            apply congrArg (BitVec.setWidth 64)
            rw [← Option.some_inj, ← List.getElem?_eq_getElem _, ← List.getElem?_eq_getElem _]
            exact congrArg (fun idx => s.core.lvl[idx]?) (by rw [har_sw])
          have hft_pf : b1.toNat < ftrl'.length := by rw [hkl_sw]; exact hkl_ft
          have hft_sw : ftrl'[b1.toNat]'hft_pf = ftrl'[kl_bv.toNat]'hkl_ft := by
            rw [← Option.some_inj, ← List.getElem?_eq_getElem _, ← List.getElem?_eq_getElem _]
            exact congrArg (fun idx => ftrl'[idx]?) (congrArg BitVec.toNat hkl_sw)
          have h1 : mclr'.set ng.toNat (BitVec.setWidth 32 b1) =
              mclr'.set ng.toNat (BitVec.setWidth 32 kl_bv) := by rw [hkl_sw]
          have h2 : ftrl'.set b1.toNat (ftrl'[b1.toNat]'hft_pf ||| 2147483648) =
              ftrl'.set kl_bv.toNat (ftrl'[kl_bv.toNat]'hkl_ft ||| 0x80000000#32) := by
            rw [hft_sw, congrArg BitVec.toNat hkl_sw]; rfl
          let ftrl_n := ftrl'.set kl_bv.toNat (ftrl'[kl_bv.toNat]'hkl_ft ||| 0x80000000#32)
          let mclr_n := mclr'.set ng.toNat (BitVec.setWidth 32 kl_bv)
          have h_upd :
              (ftrl'[s.core.lvl[s.core.arena[(cref.toNat + 3 + k.toNat) % 2 ^ 64].toNat / 2].toNat]
                &&& 0x80000000#32 = 0#32) →
              (ng + 1#64).toNat = ng.toNat + 1 ∧
              ftrl_n.length = c.max_vars + 1 ∧ mclr_n.length = c.max_vars ∧
              (∀ j < (ng + 1#64).toNat, (mclr_n[j]?.getD 0#32).toNat ≤ s.core.cur_level ∧
                (ftrl_n[(mclr_n[j]?.getD 0#32).toNat]?.getD 0#32) =
                  ((s.core.frame_trail[(mclr_n[j]?.getD 0#32).toNat]?.getD 0#32) |||
                    0x80000000#32)) ∧
              (∀ i < c.max_vars + 1,
                (∀ j < (ng + 1#64).toNat, (mclr_n[j]?.getD 0#32).toNat ≠ i) →
                ftrl_n[i]? = s.core.frame_trail[i]?) ∧
              (∀ j1 j2, j1 < j2 → j2 < (ng + 1#64).toNat →
                (mclr_n[j1]?.getD 0#32).toNat ≠ (mclr_n[j2]?.getD 0#32).toNat) ∧
              (∀ m : Mem 64,
                (FullMem c { s with core := { s.core with
                  min_clr := mclr'.set ng.toNat (BitVec.setWidth 32 b1),
                  frame_trail := ftrl'.set b1.toNat
                    (ftrl'[b1.toNat]'hft_pf ||| 2147483648) } } ⋆ R) m →
                (FullMem c { s with core := { s.core with
                  frame_trail := ftrl_n, min_clr := mclr_n } } ⋆ R) m) := by
            intro hclr_raw
            have hkl_clr : (ftrl'[kl_bv.toNat]'hkl_ft &&& 0x80000000#32) = 0#32 := by
              have hidx_l : ((kl_lit >>> 1).setWidth 64).toNat = kl_lit.toNat / 2 := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by bv_omega),
                  BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
              have hkv_lvl_d : s.core.arena[(cref.toNat + 3 + k.toNat) % 2 ^ 64].toNat / 2 <
                  s.core.lvl.length := by
                have := hkv_lvl; simpa only [kl_lit, hidx_l] using this
              have hkl_bv_n : kl_bv.toNat = (s.core.lvl[s.core.arena[(cref.toNat + 3 +
                  k.toNat) % 2 ^ 64].toNat / 2]'hkv_lvl_d).toNat := by
                dsimp only [kl_bv]
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by bv_omega)]
                simp only [kl_lit, hidx_l]
              simp only [hkl_bv_n]; exact hclr_raw
            have hkl_fresh : ∀ j < ng.toNat, (mclr'[j]?.getD 0#32).toNat ≠ kl_bv.toNat := by
              intro j hj heq
              have h1' := (hmk j hj).2
              rw [heq, List.getElem?_eq_getElem hkl_ft, Option.getD_some] at h1'
              have hbit : ((ftrl'[kl_bv.toNat]'hkl_ft) &&& 0x80000000#32) ≠ 0#32 := by
                intro hzero
                have h31 := congrArg (fun x : BitVec 32 => x.getLsbD 31) hzero
                rw [h1'] at h31; simp at h31
              exact hbit hkl_clr
            have hng_mc : ng.toNat < mclr'.length := by rw [hmclr]; omega
            have hng1 : (ng + 1#64).toNat = ng.toNat + 1 := by
              have := hsz_le_mv; have := hmx; bv_omega
            have hkl_ft0 : kl_bv.toNat < s.core.frame_trail.length := by
              have := hw.cur_level_le; have := hcl.trail_end_le; have := hcl.cur_vars_le
              exact Nat.lt_of_le_of_lt hkl_le (by rw [hcl.frame_trail_len]; omega)
            have hft_eq : ftrl'[kl_bv.toNat]'hkl_ft = s.core.frame_trail[kl_bv.toNat]'hkl_ft0 := by
              have h1' := hunm kl_bv.toNat (by omega) hkl_fresh
              rw [List.getElem?_eq_getElem hkl_ft, List.getElem?_eq_getElem hkl_ft0] at h1'
              exact Option.some.inj h1'
            have hmk' : ∀ j < (ng + 1#64).toNat,
                (mclr_n[j]?.getD 0#32).toNat ≤ s.core.cur_level ∧
                (ftrl_n[(mclr_n[j]?.getD 0#32).toNat]?.getD 0#32 =
                  ((s.core.frame_trail[(mclr_n[j]?.getD 0#32).toNat]?.getD 0#32) |||
                    0x80000000#32)) := by
              intro j hj
              have hkl32 : (BitVec.setWidth 32 kl_bv).toNat = kl_bv.toNat := by bv_omega
              dsimp only [ftrl_n, mclr_n]
              by_cases hjn : j = ng.toNat
              · subst hjn
                rw [List.getElem?_set_self hng_mc, Option.getD_some, hkl32,
                  List.getElem?_set_self hkl_ft, Option.getD_some,
                  List.getElem?_eq_getElem hkl_ft0, Option.getD_some, hft_eq]
                exact ⟨hkl_le, rfl⟩
              · rw [List.getElem?_set_ne (Ne.symm hjn)]
                have hj_lt : j < ng.toNat := by omega
                have hprev := hmk j hj_lt
                have hne := hkl_fresh j hj_lt
                rw [List.getElem?_set_ne (Ne.symm hne)]
                exact hprev
            have hunm' : ∀ i < c.max_vars + 1,
                (∀ j < (ng + 1#64).toNat, (mclr_n[j]?.getD 0#32).toNat ≠ i) →
                ftrl_n[i]? = s.core.frame_trail[i]? := by
              intro i hi hall
              have hkl32 : (BitVec.setWidth 32 kl_bv).toNat = kl_bv.toNat := by bv_omega
              dsimp only [ftrl_n, mclr_n] at hall ⊢
              have hne_i : kl_bv.toNat ≠ i := by
                have h := hall ng.toNat (by omega)
                rwa [List.getElem?_set_self hng_mc, Option.getD_some, hkl32] at h
              rw [List.getElem?_set_ne hne_i]
              refine hunm i hi fun j hj => ?_
              have h := hall j (by omega)
              rwa [List.getElem?_set_ne (by omega : ng.toNat ≠ j)] at h
            have hdist' : ∀ j1 j2, j1 < j2 → j2 < (ng + 1#64).toNat →
                (mclr_n[j1]?.getD 0#32).toNat ≠ (mclr_n[j2]?.getD 0#32).toNat := by
              intro j1 j2 h12 h2
              have hkl32 : (BitVec.setWidth 32 kl_bv).toNat = kl_bv.toNat := by bv_omega
              dsimp only [mclr_n]
              by_cases hj2 : j2 = ng.toNat
              · subst hj2
                rw [List.getElem?_set_self hng_mc, Option.getD_some, hkl32,
                  List.getElem?_set_ne (by omega)]
                exact hkl_fresh j1 (by omega)
              · rw [List.getElem?_set_ne (by omega : ng.toNat ≠ j1),
                  List.getElem?_set_ne (by omega : ng.toNat ≠ j2)]
                exact hdist j1 j2 h12 (by omega)
            refine ⟨hng1, by simp [ftrl_n, hftrl], by simp [mclr_n, hmclr], hmk', hunm', hdist',
              fun m hm => (congrArg (fun x => (FullMem c { s with core := x } ⋆ R) m)
                (by rw [h1, h2] : ({ s.core with
                  min_clr := mclr'.set ng.toNat (BitVec.setWidth 32 b1),
                  frame_trail := ftrl'.set b1.toNat (ftrl'[b1.toNat]'hft_pf ||| 2147483648) } :
                    FullCoreState) =
                  { s.core with
                    frame_trail := ftrl_n, min_clr := mclr_n })).mp hm⟩
          c0_hfast_nogrp
          · obtain ⟨hng1, hftrl', hmclr', hmk', hunm', hdist', hm_rw⟩ := h_upd (by assumption)
            exact hJbrk (ng + 1#64, k, ()) _ ⟨by omega, ftrl_n, mclr_n, hftrl', hmclr', hmk',
              hunm', hdist', hm_rw _ (by assumption)⟩
          · obtain ⟨hng1, hftrl', hmclr', hmk', hunm', hdist', hm_rw⟩ := h_upd (by assumption)
            exact hJs1 (ng + 1#64, ()) _ ⟨by omega, ftrl_n, mclr_n, hftrl', hmclr', hmk', hunm',
              hdist', hm_rw _ (by assumption)⟩
          · exact hJs1 (ng, ()) mk ⟨by omega, ftrl', mclr', hftrl, hmclr, hmk, hunm, hdist, hmk_m⟩
        · exact hJs1 (ng, ()) mk ⟨by omega, ftrl', mclr', hftrl, hmclr, hmk, hunm, hdist, hmk_m⟩
      · exact hJs (ng, ()) mk ⟨by omega, ftrl', mclr', hftrl, hmclr, hmk, hunm, hdist, hmk_m⟩
    · exact hJbrk (ng, k, ()) mk ⟨Nat.le_trans hng_le hk_le, ftrl', mclr', hftrl, hmclr, hmk, hunm,
        hdist, hmk_m⟩

theorem full_viv_mark_garb_m6_s5_wp (Γ : Env)
    (hUnreason : ∀ a m Q X, fullVivUnreasonM6Spec a m Q X →
      Γ "full_viv_unreason_m6" [i64, i32] [] a m Q X)
    (hUnwatch : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X) :
    ∀ args m Q X, fullVivMarkGarbM6Spec args m Q X →
      Func.wp Γ FullFidelityStep13S5VivifyBackbone.full_viv_mark_garb_m6_body args m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s0, R, rfl, hsp0, href0, hm0, hQ⟩
  have hmx := c.hmaxv; have harc := c.harena; unfold dimacsBound at hmx harc
  unfold Func.wp FullFidelityStep13S5VivifyBackbone.full_viv_mark_garb_m6_body
  c0_call hUnreason
  refine ⟨c, F0, F_cur, s0, R, rfl, hsp0, hm0,
    fun s1 m1 hsp1 hna1 hcv1 har1 hal1 hpr1 hfu1 _ _ hrr1 htr1 hm1 => ?_⟩
  have href1 : cref.toNat ∈ fullArenaClauseRefs s1 := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har1, hal1]; exact href0
  have hrefs1 : fullArenaClauseRefs s1 = fullArenaClauseRefs s0 := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har1, hal1]
  have hwf1 := hsp1.2.1.arena.refs_wf cref.toNat href1
  have hcl1 := hsp1.1.core_ok
  have hcr0_lt : cref.toNat < s1.core.arena.length := by
    have := hcl1.arena_len_arr; have := hcl1.arena_len_le; omega
  have hcr2_lt : (cref.setWidth 64 + 2#64).toNat < s1.core.arena.length := by
    have := hcl1.arena_len_arr; have := hcl1.arena_len_le; bv_omega
  have hcr3_lt : (cref.setWidth 64 + 3#64).toNat < s1.core.arena.length := by
    have := hcl1.arena_len_arr; have := hcl1.arena_len_le; bv_omega
  have hcr4_lt : (cref.setWidth 64 + 4#64).toNat < s1.core.arena.length := by
    have := hcl1.arena_len_arr; have := hcl1.arena_len_le; bv_omega
  c0_hfast
  · exact hQ s1 m1 hsp1 hcv1 hal1 hpr1 hfu1 hrefs1 hrr1 htr1 hm1
  · have hlay1 : WatchStackLayout s1.core := by
      have hmw := hsp1.2.1.watches; unfold ModeWatchesInv at hmw
      rw [ite_eq_left hsp1.2.2.2.2.2] at hmw; exact hmw.layout
    c0_call hUnwatch
    refine ⟨c, s1, R, rfl, hsp1.1, hlay1, hm1,
      fun wvec2 wstk2 wu2 m2 hlen2 hlay2 hmw2 hm2 => ?_⟩
    let s2 : FullState :=
      { s1 with core := { s1.core with wvec := wvec2, wstk := wstk2, wusable := wu2 } }
    have hsp2 : FullSparseInvW c F0 F_cur s2 :=
      ⟨hlen2,
        { hsp1.2.1 with
          arena := { hsp1.2.1.arena with len_ok := hsp1.2.1.arena.len_ok }
          watches := hmw2 F_cur hsp1.2.1.watches },
        hsp1.2.2.1, hsp1.2.2.2.1, hsp1.2.2.2.2.1, hsp1.2.2.2.2.2⟩
    c0_hfast
    c0_call hUnwatch
    refine ⟨c, s2, R, rfl, hsp2.1, hlay2, hm2,
      fun wvec3 wstk3 wu3 m3 hlen3 _ hmw3 hm3 => ?_⟩
    let s3 : FullState :=
      { s2 with core := { s2.core with wvec := wvec3, wstk := wstk3, wusable := wu3 } }
    have hsp3 : FullSparseInvW c F0 F_cur s3 :=
      ⟨hlen3,
        { hsp2.2.1 with
          arena := { hsp2.2.1.arena with len_ok := hsp2.2.1.arena.len_ok }
          watches := hmw3 F_cur hsp2.2.1.watches },
        hsp2.2.2.1, hsp2.2.2.2.1, hsp2.2.2.2.2.1, hsp2.2.2.2.2.2⟩
    have hhdr3 : s1.core.arena[cref.toNat]'hcr0_lt = fullArenaHdr s3 cref.toNat := by
      unfold fullArenaHdr fullArenaHdrCore; dsimp only [s3, s2]
      rw [List.getElem?_eq_getElem hcr0_lt, Option.getD_some]
    c0_hfast_nogrp
    refine wp_join_group (ts := [])
      (fun () mf => ∃ (ni' nr' : BitVec 64) (fl' : List (BitVec 32)),
        fl'.length = c.max_vars ∧
        let sf : FullState :=
          { s3 with core :=
            { s3.core with
              arena := s3.core.arena.set cref.toNat (fullArenaHdr s3 cref.toNat ||| 0x00080000#32)
              arena_garbage := s3.core.arena_garbage + 3#64 +
                (s1.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_lt).setWidth 64
              num_irred := ni', num_redundant := nr', flags := fl' } }
        (FullMem c sf ⋆ R) mf) ?_ ?_
    · rintro _ ⟨⟩ mf ⟨ni', nr', fl', hfl', hmf⟩
      c0_hfast
      obtain ⟨hsp_f, hrefs_f⟩ := markGarb_hnonact_preserves_fullSparseW hsp3 href1 hna1
        (s3.core.arena_garbage + 3#64 +
          (s1.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_lt).setWidth 64)
        ni' nr' (s3.scratch.viv_cnt + 1#64)
      have hsp_f2 := fullSparseInvW_with_flags hsp_f hfl'
      exact hQ _ _ hsp_f2 hcv1 hal1 hpr1 hfu1 (hrefs_f.trans hrefs1) hrr1 htr1 (by assumption)
    · intro Jf hJf
      have har_eq : s3.core.arena.set cref.toNat (s1.core.arena[cref.toNat]'hcr0_lt ||| 524288) =
          s3.core.arena.set cref.toNat (fullArenaHdr s3 cref.toNat ||| 0x00080000#32) := by
        rw [hhdr3]; rfl
      have hng3 : fullArenaClauseGarb s3 cref.toNat = false := by
        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
        have h1 : (s1.core.arena[cref.toNat]'hcr0_lt &&& 0x00080000#32) = 0#32 := by assumption
        dsimp only [s3, s2]
        rw [List.getElem?_eq_getElem hcr0_lt, Option.getD_some]
        simpa [show (524288#32 : BitVec 32) = 0x00080000#32 from rfl] using h1
      let sz := s1.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_lt
      have hsz_eq : sz.toNat = fullArenaClauseSizeCore s3.core cref.toNat := by
        unfold fullArenaClauseSizeCore; dsimp only [sz, s3, s2]
        have hcr2_eq : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by bv_omega
        rw [← hcr2_eq, List.getElem?_eq_getElem hcr2_lt, Option.getD_some]
      have hbd3 : cref.toNat + 3 + fullArenaClauseSizeCore s3.core cref.toNat ≤
          s3.core.arena.length := by
        have h1 : cref.toNat + 3 + fullArenaClauseSizeCore s1.core cref.toNat ≤
            s1.core.arena_len := by
          have := hwf1.2.2.1; omega
        have h2 : s1.core.arena_len ≤ s1.core.arena.length := by
          have := hcl1.arena_len_le; have := hcl1.arena_len_arr; omega
        exact Nat.le_trans h1 h2
      have hrun_flags : ∀ (ni' : BitVec 64) (mk : Mem 64),
          (FullMem c { s3 with core :=
            { s3.core with
              arena := s3.core.arena.set cref.toNat (s1.core.arena[cref.toNat]'hcr0_lt ||| 524288)
              arena_garbage := s3.core.arena_garbage + 3#64 + sz.setWidth 64
              num_irred := ni', num_redundant := s3.core.num_redundant } } ⋆ R) mk →
          wp Γ Q X
            (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 800, ())) fun p_34 =>
             Expr.load i64 (Arg.var p_34.fst) fun ld_6 =>
             Expr.group (sig := [[i32]])
              (fun Jk => Blocks.cons (fun pk =>
                Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var pk.fst, Arg.var sz, ()))
                  fun ck =>
                Expr.jnz (Arg.var ck.fst)
                  (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun cr64 =>
                   Expr.let_ (Op.mk (.add i64) (Arg.var cr64.fst, Arg.imm 3, ())) fun c3 =>
                   Expr.let_ (Op.mk (.zext 32 64) (Arg.var pk.fst, ())) fun k64 =>
                   Expr.let_ (Op.mk (.add i64) (Arg.var c3.fst, Arg.var k64.fst, ())) fun idx =>
                   Expr.let_ (Op.mk (.mul i64) (Arg.var idx.fst, Arg.imm 4, ())) fun off =>
                   Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var off.fst, ())) fun pa =>
                   Expr.load i32 (Arg.var pa.fst) fun lg =>
                   Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun pf =>
                     Expr.let_ (Op.mk (.lshr i32) (Arg.var lg, Arg.imm 1, ())) fun lv =>
                     Expr.let_ (Op.mk (.zext 32 64) (Arg.var lv.fst, ())) fun lv64 =>
                     Expr.let_ (Op.mk (.mul i64) (Arg.var lv64.fst, Arg.imm 4, ())) fun off2 =>
                     Expr.let_ (Op.mk (.add i64) (Arg.var ld_6, Arg.var off2.fst, ())) fun pfg =>
                     Expr.let_ (Op.mk (.lshr i32) (Arg.var lg, Arg.imm 1, ())) fun lv2 =>
                     Expr.let_ (Op.mk (.zext 32 64) (Arg.var lv2.fst, ())) fun lv64b =>
                     Expr.let_ (Op.mk (.mul i64) (Arg.var lv64b.fst, Arg.imm 4, ())) fun off2b =>
                     Expr.let_ (Op.mk (.add i64) (Arg.var ld_6, Arg.var off2b.fst, ())) fun pfg2 =>
                     Expr.load i32 (Arg.var pfg2.fst) fun fg =>
                     Expr.let_ (Op.mk (.or i32) (Arg.var fg, Arg.imm 16, ())) fun fg1 =>
                     Expr.let_ (Op.mk (.or i32) (Arg.var fg1.fst, Arg.var pf.fst, ())) fun nfg =>
                     Expr.store (Arg.var nfg.fst) (Arg.var pfg.fst)
                       (Expr.let_ (Op.mk (.add i32) (Arg.var pk.fst, Arg.imm 1, ())) fun k1 =>
                        Expr.jump Jk.fst (Arg.var k1.fst, ()))) Blocks.nil) fun Jt =>
                   Expr.let_ (Op.mk (.and i32) (Arg.var lg, Arg.imm 1, ())) fun b1 =>
                   Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var b1.fst, Arg.imm 0, ()))
                     fun cb =>
                   Expr.jnz (Arg.var cb.fst) (Expr.jump Jt.fst (Arg.imm 64, ()))
                     (Expr.jump Jt.fst (Arg.imm 32, ())))
                  (Expr.jump Jf ())) Blocks.nil)
              fun Jk => Expr.jump Jk.fst (Arg.imm 0, ())) mk := by
        intro ni' mk hmk
        c0_hfast_nogrp
        refine wp_loop_inv (ts := [i32])
          (fun (k, ()) m_k => k.toNat ≤ sz.toNat ∧ ∃ fl_k : List (BitVec 32),
            fl_k.length = c.max_vars ∧
            (FullMem c { s3 with core :=
              { s3.core with
                arena := s3.core.arena.set cref.toNat (s1.core.arena[cref.toNat]'hcr0_lt ||| 524288)
                arena_garbage := s3.core.arena_garbage + 3#64 + sz.setWidth 64
                num_irred := ni', num_redundant := s3.core.num_redundant, flags := fl_k } }
              ⋆ R) m_k)
          (fun (k, ()) _ => sz.toNat - k.toNat)
          (fun Jk hJk => by
            c0_hfast_nogrp
            exact hJk (0#32, ()) mk ⟨Nat.zero_le _, s3.core.flags, hlen3.core_ok.flags_len, hmk⟩)
          (fun Jk (k, ()) m_k ⟨hk_le, fl_k, hfl_k, hm_k⟩ ihk => ?_)
        c0_hfast_nogrp
        · have hk_lt : k.toNat < sz.toNat := BitVec.lt_def.mp (by assumption)
          have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
          have hidx_eq : (BitVec.setWidth 64 cref + 3#64 + BitVec.setWidth 64 k).toNat =
              cref.toNat + 3 + k.toNat := by bv_omega
          have hidx_lt : (BitVec.setWidth 64 cref + 3#64 + BitVec.setWidth 64 k).toNat <
              (s3.core.arena.set cref.toNat
                (s1.core.arena[cref.toNat]'hcr0_lt ||| 524288)).length := by
            rw [List.length_set, hidx_eq]; have := hwf1.2.1; omega
          have hlg_eq : (s3.core.arena.set cref.toNat
              (s1.core.arena[cref.toNat]'hcr0_lt ||| 524288))[
              (BitVec.setWidth 64 cref + 3#64 + BitVec.setWidth 64 k).toNat]'hidx_lt =
              s3.core.arena[cref.toNat + 3 + k.toNat]'(by
                have := hwf1.2.1; have := hlen3.core_ok.arena_len_arr
                have := hlen3.core_ok.arena_len_le; omega) := by
            simp only [hidx_eq]; exact List.getElem_set_ne (by omega) _
          have hlg_lt : (s3.core.arena[cref.toNat + 3 + k.toNat]'(by
              have := hwf1.2.1; have := hlen3.core_ok.arena_len_arr
              have := hlen3.core_ok.arena_len_le; omega)).toNat < 2 * s3.core.cur_vars := by
            have hmem : (s3.core.arena[cref.toNat + 3 + k.toNat]'(by
                have := hwf1.2.1; have := hlen3.core_ok.arena_len_arr
                have := hlen3.core_ok.arena_len_le; omega)).toNat ∈
                fullArenaClauseLitsCore s3.core cref.toNat :=
              (mem_fullArenaClauseLitsCore_iff hbd3).mpr ⟨k.toNat, by omega, rfl⟩
            exact hsp3.2.1.arena.lits_lt cref.toNat href1 hng3 _ hmem
          have hlv_lt : (((s3.core.arena.set cref.toNat
              (s1.core.arena[cref.toNat]'hcr0_lt ||| 524288))[
              (BitVec.setWidth 64 cref + 3#64 +
                BitVec.setWidth 64 k).toNat]'hidx_lt >>> 1#32).setWidth 64).toNat <
              fl_k.length := by
            rw [hlg_eq, BitVec.toNat_setWidth, s13_bv32_lshr1, hfl_k]
            have hcv3 : s3.core.cur_vars ≤ c.max_vars := hlen3.core_ok.cur_vars_le
            dsimp only [s3, s2] at hlg_lt hcv3 ⊢; omega
          c0_hfast
          all_goals
            refine ihk (k + 1#32, ()) _ (by dsimp only; omega) ⟨by omega, _, ?_, by assumption⟩
            rw [List.length_set, hfl_k]
        · clear ihk
          exact hJf () m_k ⟨ni', s3.core.num_redundant, fl_k, hfl_k, by rw [← har_eq]; exact hm_k⟩
      c0_hfast_nogrp
      · refine wp_join_group (ts := []) (fun _ mf => ∃ nr' : BitVec 64,
            (FullMem c { s3 with core :=
              { s3.core with
                arena := s3.core.arena.set (cref.setWidth 64).toNat
                  (s1.core.arena[cref.toNat]'hcr0_lt ||| 524288)
                arena_garbage := s3.core.arena_garbage + 3#64 + sz.setWidth 64
                num_redundant := nr' } } ⋆ R) mf)
          (fun _ _ mf ⟨nr', hmf⟩ => hJf () _ ⟨s3.core.num_irred, nr', s3.core.flags,
            hlen3.core_ok.flags_len, by rw [← har_eq]; exact hmf⟩)
          (fun _ hJs => by c0_hfast <;> exact hJs () _ ⟨_, by assumption⟩)
      · refine wp_join_group (ts := []) (fun _ mf => ∃ ni' : BitVec 64,
            (FullMem c { s3 with core :=
              { s3.core with
                arena := s3.core.arena.set (cref.setWidth 64).toNat
                  (s1.core.arena[cref.toNat]'hcr0_lt ||| 524288)
                arena_garbage := s3.core.arena_garbage + 3#64 + sz.setWidth 64
                num_irred := ni' } } ⋆ R) mf)
          (fun _ _ mf ⟨ni', hmf⟩ => by
            have hcr64_eq : (BitVec.setWidth 64 cref).toNat = cref.toNat := by bv_omega
            refine hrun_flags ni' _ ?_
            simpa [har_eq, hcr64_eq] using hmf)
          (fun _ hJs => by c0_hfast <;> exact hJs () _ ⟨_, by assumption⟩)

end PromoteAndMarkGarb

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

end
