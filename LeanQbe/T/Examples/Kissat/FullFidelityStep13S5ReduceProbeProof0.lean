/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5ReduceProbe
public import LeanQbe.T.Examples.Kissat.FullFidelityTumbleSpec
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof1
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof2
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullSpec1
public import LeanQbe.T.Examples.Kissat.FullSpec2
public import LeanQbe.T.Examples.Kissat.FullSpec3
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullArena1
import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S5-A — Shared Specs, `activate`, `probe_tail` (`Proof0`)

Defines cross-shard Step-13 callee/target `Spec`s for Shard S5-A (`0` cross-shard imports) and
proves UNSAT-sound `Func.wp` (`XPost := False`, `0` `@[expose]` on theorems/lemmas, `<= 100`
cols) for:
1. `full_activate_lit_fid_s5_wp` (`FullFidelityTumble.fullActivateLitFidSpec`)
2. `full_probe_tail_m6_s5_wp` (`FullM6Orch.m6ProbeTailSpec`)
-/

set_option autoImplicit false

local elab "c0_hfast" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local elab "c0_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

local macro "c0_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullFidelityTumble
open LeanQbe.T.Examples.Kissat.FullFidelityStep13S5ReduceProbe
open FullArenaTactics
open scoped FullArenaTactics FullM6Hdr.M6HdrTactics FullM6ProofUtil.M6ProofUtilTactics

@[expose] public section

/-! ## 1. Shared Step-13 Callee & Target Specifications (`S5-A`) -/

/-- Pure memory-preserving spec for all 1-arg `f64u_*` soft-float helpers (`S0`). -/
def f64uPure1Spec : Spec [i64] [i64] :=
  fun _ m Q _ => ∀ r : BitVec 64, Q (r, ()) m

/-- Pure memory-preserving spec for all 2-arg `f64u_*` soft-float helpers (`S0`). -/
def f64uPure2Spec : Spec [i64, i64] [i64] :=
  fun _ m Q _ => ∀ r : BitVec 64, Q (r, ()) m

/-- Step-13 `full_update_classify_fid` contract (`FullM6HdrMem`-preserving). -/
abbrev step13UpdateClassifyM6Spec : Spec [i64] [] := m6HdrW2aSpec [] []

/-- Pure read-only predicate spec for `full_has_factor_cands_fid` (`S1`). -/
def step13HasFactorCandsSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧ ∀ r : Bool, Q (r, ()) m

/-- `full_enter_dense_ex_fid`: parameterized `enter_dense(h, connect_large)` over
`FullM6HdrMem` (`S1`). -/
def step13EnterDenseExM6Spec : Spec [i64, .bool] [.bool] := fun (h, connect_large, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
    (s.core.dense_mode ≠ 0#64 → s.core.oom = 0#64) ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ (ok : Bool) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrCfgOk c → M6HdrExtOk ext' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      s'.LengthsOk c → FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (ok = true → FullDenseInv c F0 s' ∧
        (connect_large = false → s'.core.cur_level = 0 ∧ s'.core.dense_mode ≠ 0#64)) →
      (ok = false → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (ok, ()) m'

/-- `full_enter_dense`: `FullM6HdrMem`-threaded Step-13 `full_enter_dense_ex_fid(h, true)`
(`S1`). -/
def step13EnterDenseM6Spec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
    (s.core.dense_mode ≠ 0#64 → s.core.oom = 0#64) ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ (ok : Bool) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrCfgOk c → M6HdrExtOk ext' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      s'.LengthsOk c → FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (ok = true → FullDenseInv c F0 s') →
      (ok = false → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (ok, ()) m'

/-- `full_dense_bin_roundtrip_fid` binary-watch rebuild contract (`S1`). -/
def step13DenseBinRoundtripSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.dense_mode = s.core.dense_mode →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.vals = s.core.vals → s'.core.lvl = s.core.lvl → s'.core.flags = s.core.flags →
      s'.core.fuel = s.core.fuel → s'.core.inconsistent = s.core.inconsistent →
      s'.core.d_cur = s.core.d_cur → s'.core.d_val = s.core.d_val →
      s'.core.frame_trail = s.core.frame_trail → s'.core.frame_dec = s.core.frame_dec →
      s'.core.trail_end = s.core.trail_end → s'.core.propagated = s.core.propagated →
      s'.scratch.extend_len = s.scratch.extend_len →
      s'.scratch.walk_vals = s.scratch.walk_vals →
      s'.scratch.walk_best = s.scratch.walk_best →
      s'.scratch.last_learned = s.scratch.last_learned →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- Step-13 `FullM6HdrMem`-threaded contract for `full_propagate` (`S2`). -/
def step13BcpM6Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
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
      FullProbeScratchPres { s with scratch := { s.scratch with
        search_ticks := sc'.search_ticks, wsort := sc'.wsort,
        phases := sc'.phases, delayed := sc'.delayed } } s' →
      sc'.red_refs = s.scratch.red_refs → sc'.delayed_len = s.scratch.delayed_len →
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

/-- Step-13 `FullM6HdrMem`-threaded contract for `full_lucky_late_m7` (`S3`). -/
def step13LuckyLateM6Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.probing = 0#64 →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 ∨ r = 2#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Step-13 `FullM6HdrMem`-threaded contract for `full_parse_body_m6` (`S3`). -/
def step13ParseBodyM6Spec : Spec [i64, i64] [i64] := fun (h, cend, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (cnf_ptr : BitVec 64)
    (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ cend = cptrEq cnf_ptr cnfBytes ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ i0 ≤ cnfBytes.length ∧
    parseHeader cnfBytes = some (c.mv, c.nc, cnfBytes.drop i0) ∧
    s.core.cur_vars = c.mv ∧ s.core.d_cur = cnf_ptr + BitVec.ofNat 64 i0 ∧
    s.core.cur_level = 0 ∧ s.core.trail_end = 0 ∧ s.core.propagated = 0 ∧
    s.core.arena_len = 0 ∧ s.core.oom = 0#64 ∧ s.core.probing = 0#64 ∧
    s.core.inconsistent = 0#64 ∧
    s.core.vals = List.replicate (2 * c.max_vars) 0#8 ∧
    s.core.wvec = List.replicate (4 * c.max_vars) 0#32 ∧
    FullM6HdrInv c (shiftDownCnf CNF.empty) ext s ∧
    (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.fuel = s.core.fuel → s'.core.oom = 0#64 → s'.core.probing = 0#64 →
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
      (r = 1#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        FullM6HdrInv c (shiftDownCnf cnf) ext' s' ∧ s'.core.cur_level = 0) →
      (UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc → r = 20#64) →
      (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'
where
  cptrEq (p : BitVec 64) (bs : List UInt8) : BitVec 64 := p + BitVec.ofNat 64 bs.length

/-- Step-13 `FullM6HdrMem`-threaded lift of `fullCompactSpec` (`S6a`). -/
def step13CompactM6Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r c' ext' s' m',
      FullM4Compact.FullCfgCompat c c' → FullM6HdrInv c' F0 ext' s' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars ≤ s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → s'.core.cur_level = 0) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Step-13 `FullM6HdrMem`-threaded lift of `fullRebuildWatchesSpec` (`S6a`). -/
def step13RebuildWatchesM6Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
    FullDenseInv c F0 s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      FullM6HdrInv c F0 ext' s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Step-13 `FullM6HdrMem`-threaded lift of `fullSubstituteSpec` (`S6a`). -/
def step13SubstituteM6Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      FullM6HdrInv c F0 ext' s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Step-13 `full_vivify_m6_hdr` contract (`VivifyBackboneProof0a.step13VivifySpec`). -/
def s5aVivifySpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullSparseInv c F0 s ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      FullSparseInv c F0 s' → s'.core.cur_level = 0 ∧ s'.core.probing = s.core.probing →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Step-13 `full_backbone_m6` contract (`VivifyBackboneProof0a.step13BackboneSpec`). -/
def s5aBackboneSpec : Spec [i64, i64] [i64] := fun (h, _tick_lim, ()) m Q _ =>
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

/-- Step-13 `full_transitive_m6` contract (`VivifyBackboneProof0a.step13TransitiveSpec`). -/
def s5aTransitiveSpec : Spec [i64, i64] [i64] := fun (h, _tick_lim, ()) m Q _ =>
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

/-- Exact `heap`/`pos`-only `full_heap_down` spec matching `Full.fullHeapUpSpec`. -/
def step13HeapDownSpec : Spec [i64, i32] [] :=
  SafetySlice.spec fullSafetySlice (fun c (h, _v, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => ∃ hp' ps', s'.scratch = { s.scratch with heap := hp', pos := ps' })

/-- Step-13 `full_set_inactive` contract (`S6a`). -/
def step13SetInactiveSpec : Spec [i64, i32, i32] [] := fun (h, v, _flag, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    if s.core.cur_vars ≤ v.toNat then
      Q () m
    else
      ∀ flags' unass' qp' qn' qs' qsi' qss' qf' ql' hp' ps' hl' m',
        let s' : FullState :=
          { s with
            core := { s.core with flags := flags', unassigned := unass' }
            scratch :=
              { s.scratch with
                q_prev := qp', q_next := qn', q_stamp := qs',
                q_search_idx := qsi', q_search_stamp := qss',
                q_first := qf', q_last := ql',
                heap := hp', pos := ps', heap_len := hl' } }
        s'.LengthsOk c →
        (FullMem c s' ⋆ R) m' → Q () m'

/-- Step-13 `full_arena_sweep` contract (`FullSpec2.fullArenaSweepSpec` + `sc'.work_stk1`
preservation, needed so `force = true` `full_reduce_m6` preserves `work_stk1` for `S2`). -/
def step13ArenaSweepSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
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
      sc'.extend_len = s.scratch.extend_len → sc'.work_stk1 = s.scratch.work_stk1 →
      sc'.work_stk2 = s.scratch.work_stk2 → FullLastLearnedWf s' →
      FullWitnessInv c F0 F_cur s'.core → FullArenaVarsNodup s' →
      (r = 0#64 ∨ r = 1#64 → oom' = 0#64) →
      (0 < s.core.cur_level → r ≠ 1#64 ∧ r ≠ 2#64 ∧
        vals' = s.core.vals ∧ lvl' = s.core.lvl ∧ trl' = s.core.trl ∧
        tp' = s.core.trail_pos ∧ te' = s.core.trail_end) →
      (r = 1#64 → s.core.cur_level = 0 ∧ s.core.trail_end < te') →
      (r = 2#64 → s.core.cur_level = 0 ∧ F0.Unsat) →
      (r = 3#64 → oom' ≠ 0#64) → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Step-13 compaction-aware `full_reduce_m6` contract (`#3057` §7). When `force = true`,
compaction is disabled (`do_compact = false`), so exact `FullM6Orch.m6ReduceSpec` +
`probing`/`min_clr_len`/`work_stk1` preservation holds for `S2` and `S3`. -/
def step13ReduceM6Spec : Spec [i64, .bool] [i64] := fun (h, force, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
    (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInvW c F0 F_cur ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r c' ext' s' m',
      FullM4Compact.FullCfgCompat c c' → FullM6HdrInv c' F0 ext' s' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars ≤ s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → s'.core.cur_level ≤ s.core.cur_level) →
      (force = true → c' = c ∧ FullM6HdrInvW c F0 F_cur ext' s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧
        s'.core.probing = s.core.probing ∧ s'.core.min_clr_len = s.core.min_clr_len ∧
        s'.core.cur_vars = s.core.cur_vars ∧ s'.core.tmp = s.core.tmp ∧
        s'.core.tmp_len = s.core.tmp_len ∧ s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
        s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
        (r = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64) ∧
        (r = 1#64 → 0 < s'.core.cur_level →
          s'.core.cur_level = s.core.cur_level ∧ s'.core.vals = s.core.vals ∧
          s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
          s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end)) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m'

end

public section

/-! ## 2. `full_activate_lit_fid_s5_wp` (`fullActivateLitFidSpec`) -/

section ActivateLitS5

theorem full_activate_lit_fid_s5_wp (Γ : Env)
    (hInvU64 : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_inv_u64" [i64] [i64] a m Q X)
    (hSub : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_sub" [i64, i64] [i64] a m Q X)
    (hHeapPush : ∀ a m Q X, Full.fullHeapPushSpec a m Q X →
      Γ "full_heap_push" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullActivateLitFidSpec a m Q X →
      Func.wp Γ FullFidelityStep13S5ReduceProbe.full_activate_lit_fid_body a m Q X := by
  rintro ⟨h, v32, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have hcv_mod : s.core.cur_vars % 2 ^ 64 = s.core.cur_vars := Nat.mod_eq_of_lt (by omega)
  unfold Func.wp FullFidelityStep13S5ReduceProbe.full_activate_lit_fid_body
  c0_hfast_nogrp
  · exact hQ s.core.flags s.core.unassigned s.scratch m hlen ⟨rfl, rfl⟩ hm
  · have hv_lt : v32.toNat < s.core.cur_vars := by
      have h1 : ¬ s.core.cur_vars % 2 ^ 64 ≤ (v32.setWidth 64).toNat := by assumption
      have h2 : (v32.setWidth 64).toNat = v32.toNat := by simp [BitVec.toNat_setWidth]; omega
      omega
    have hv_fl : (v32.setWidth 64).toNat < s.core.flags.length := by
      rw [hlen.core_ok.flags_len]; simp [BitVec.toNat_setWidth]; omega
    c0_hfast_nogrp
    · exact hQ s.core.flags s.core.unassigned s.scratch m hlen ⟨rfl, rfl⟩ hm
    · have hgu31 : 31 < s.scratch.glue_used.length := by
        rw [hlen.scratch_ok.glue_used_len]; decide
      c0_hfast_nogrp
      refine wp_join_group (ts := [i32])
        (fun (k32, ()) m1 =>
          k32 ≠ 0#32 ∧ ∃ fl1 un1,
            (FullMem c { core := { s.core with flags := fl1, unassigned := un1 },
                         scratch := s.scratch } ⋆ R) m1 ∧
            ({ core := { s.core with flags := fl1, unassigned := un1 },
               scratch := s.scratch } : FullState).LengthsOk c)
        (fun Jk ⟨k32, ⟨⟩⟩ m1 ⟨_hk_ne0, fl1, un1, hm1, hlen1⟩ => ?_)
        (fun Jk hJk => ?_)
      · have hgu31_1 : 31 < s.scratch.glue_used.length := hgu31
        have hv_qp : (v32.setWidth 64).toNat < s.scratch.q_prev.length := by
          rw [hlen1.scratch_ok.q_prev_len]; simp [BitVec.toNat_setWidth]; omega
        have hv_qn : (v32.setWidth 64).toNat < s.scratch.q_next.length := by
          rw [hlen1.scratch_ok.q_next_len]; simp [BitVec.toNat_setWidth]; omega
        c0_hfast_nogrp
        refine wp_join_state0 (α := FullState)
          (fun s2 m2 =>
            (FullMem c s2 ⋆ R) m2 ∧ ∃ sc2,
              s2 = { core := { s.core with flags := fl1, unassigned := un1 }, scratch := sc2 } ∧
              s2.LengthsOk c ∧ Full.FullExtScratchPres s s2)
          (fun Jq s2 m2 ⟨hm2, sc2, hs2eq, hlen2, hpres2⟩ => ?_)
          (fun Jq hJq => ?_)
        · subst hs2eq
          have hv_qs : (v32.setWidth 64).toNat < sc2.q_stamp.length := by
            rw [hlen2.scratch_ok.q_stamp_len]; simp [BitVec.toNat_setWidth]; omega
          have hv_sc : (v32.setWidth 64).toNat < sc2.score.length := by
            rw [hlen2.scratch_ok.score_len]; simp [BitVec.toNat_setWidth]; omega
          c0_hfast_nogrp
          c0_call hInvU64
          intro r_inv
          c0_hfast_nogrp
          c0_call hSub
          intro r_sub
          c0_hfast_nogrp
          have hv_qs' : (v32.setWidth 64).toNat <
              (sc2.q_stamp.set (v32.setWidth 64).toNat
                (BitVec.setWidth 32 (sc2.q_cur_stamp + 1#64))).length := by
            rw [List.length_set]; exact hv_qs
          let sc2a : FullScratch :=
            { sc2 with
              q_cur_stamp := sc2.q_cur_stamp + 1#64
              q_stamp := sc2.q_stamp.set (v32.setWidth 64).toNat
                (BitVec.setWidth 32 (sc2.q_cur_stamp + 1#64))
              q_search_idx := BitVec.setWidth 64 v32
              q_search_stamp := ((sc2.q_stamp.set (v32.setWidth 64).toNat
                (BitVec.setWidth 32
                  (sc2.q_cur_stamp + 1#64)))[(v32.setWidth 64).toNat]'hv_qs').setWidth 64
              score := sc2.score.set (v32.setWidth 64).toNat r_sub }
          have hlen2a : ({ core := { s.core with flags := fl1, unassigned := un1 }
                           scratch := sc2a } : FullState).LengthsOk c :=
            ⟨hlen2.core_ok, { hlen2.scratch_ok with
              q_stamp_len := by simp [sc2a, hlen2.scratch_ok.q_stamp_len]
              score_len := by simp [sc2a, hlen2.scratch_ok.score_len] }⟩
          refine wp_join_group
            (fun _ m3 => ∃ sc3,
              let s3 : FullState :=
                { core := { s.core with flags := fl1, unassigned := un1 }, scratch := sc3 }
              s3.LengthsOk c ∧ Full.FullExtScratchPres s s3 ∧ (FullMem c s3 ⋆ R) m3)
            (fun _ _ m3 ⟨sc3, hlen3, hpres3, hm3⟩ => by
              c0_hfast_nogrp
              exact hQ fl1 un1 sc3 m3 hlen3 hpres3 hm3)
            (fun Jst hJst => ?_)
          c0_hfast_nogrp
          · c0_call hHeapPush
            refine ⟨c, _, R, rfl, hlen2a, by assumption, fun _ s3 m3 hcore3 hlen3 hpres3 hm3 => ?_⟩
            have hs3_eq : s3 = { core := { s.core with flags := fl1, unassigned := un1 }
                                 scratch := s3.scratch } := by
              cases s3; simp only [FullState.mk.injEq, and_true]; exact hcore3
            have hpres_fin : Full.FullExtScratchPres s s3 :=
              ⟨hpres3.1.1.trans hpres2.1, hpres3.1.2.trans hpres2.2⟩
            c0_hfast_nogrp
            rw [hs3_eq] at hlen3 hpres_fin hm3
            exact hJst () m3 ⟨s3.scratch, hlen3, hpres_fin, hm3⟩
          · exact hJst () _ ⟨sc2a, hlen2a, hpres2, by assumption⟩
        · c0_hfast_nogrp
          · let sc2a : FullScratch :=
              { s.scratch with
                glue_used := s.scratch.glue_used.set 31 k32
                q_prev := s.scratch.q_prev.set (v32.setWidth 64).toNat
                  (s.scratch.q_last.setWidth 32)
                q_next := s.scratch.q_next.set (v32.setWidth 64).toNat 4294967295#32
                q_first := BitVec.setWidth 64 v32
                q_last := BitVec.setWidth 64 v32 }
            refine hJq { core := { s.core with flags := fl1, unassigned := un1 }, scratch := sc2a }
              _ ⟨?_, sc2a, rfl, ?_, ⟨rfl, rfl⟩⟩
            · assumption
            · exact ⟨hlen1.core_ok, { hlen1.scratch_ok with
                glue_used_len := by simp [sc2a, hlen1.scratch_ok.glue_used_len]
                q_prev_len := by simp [sc2a, hlen1.scratch_ok.q_prev_len]
                q_next_len := by simp [sc2a, hlen1.scratch_ok.q_next_len] }⟩
          · have hol_qn : ((s.scratch.q_last.setWidth 32).setWidth 64).toNat <
                (s.scratch.q_next.set (v32.setWidth 64).toNat 4294967295#32).length := by
              rw [List.length_set, hlen1.scratch_ok.q_next_len]
              have h1 : ¬ s.core.cur_vars % 2 ^ 64 ≤
                  (s.scratch.q_last.setWidth 32).toNat := by assumption
              simp only [BitVec.toNat_setWidth]
              have := (s.scratch.q_last.setWidth 32).isLt
              omega
            c0_hfast_nogrp
            let sc2b : FullScratch :=
              { s.scratch with
                glue_used := s.scratch.glue_used.set 31 k32
                q_prev := s.scratch.q_prev.set (v32.setWidth 64).toNat
                  (s.scratch.q_last.setWidth 32)
                q_next := (s.scratch.q_next.set (v32.setWidth 64).toNat 4294967295#32).set
                  ((s.scratch.q_last.setWidth 32).setWidth 64).toNat v32
                q_last := BitVec.setWidth 64 v32 }
            refine hJq { core := { s.core with flags := fl1, unassigned := un1 }, scratch := sc2b }
              _ ⟨?_, sc2b, rfl, ?_, ⟨rfl, rfl⟩⟩
            · assumption
            · exact ⟨hlen1.core_ok, { hlen1.scratch_ok with
                glue_used_len := by simp [sc2b, hlen1.scratch_ok.glue_used_len]
                q_prev_len := by simp [sc2b, hlen1.scratch_ok.q_prev_len]
                q_next_len := by simp [sc2b, hlen1.scratch_ok.q_next_len] }⟩
      · c0_hfast_nogrp
        · have hk_lt : (s.scratch.glue_used[31]'hgu31).toNat < 4294967295 := by assumption
          have hk1_ne0 : s.scratch.glue_used[31]'hgu31 + 1#32 ≠ 0#32 := by
            intro h0
            have h1 := congrArg BitVec.toNat h0
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
            omega
          refine hJk (s.scratch.glue_used[31]'hgu31 + 1#32, ()) _
            ⟨hk1_ne0, ?fl1, ?un1, ?hm1, ?hl1⟩
          case hm1 => assumption
          case hl1 =>
            exact ⟨{ hlen.core_ok with flags_len := by simp [hlen.core_ok.flags_len] },
              hlen.scratch_ok⟩
        · have hk_ge : 4294967295 ≤ (s.scratch.glue_used[31]'hgu31).toNat := by
            have h1 : ¬ (s.scratch.glue_used[31]'hgu31).toNat < 4294967295 := by assumption
            omega
          have hk_ne0 : s.scratch.glue_used[31]'hgu31 ≠ 0#32 := by
            intro h0; rw [h0] at hk_ge; simp at hk_ge
          refine hJk (s.scratch.glue_used[31]'hgu31, ()) _
            ⟨hk_ne0, ?fl2, ?un2, ?hm2, ?hl2⟩
          case hm2 => assumption
          case hl2 =>
            exact ⟨{ hlen.core_ok with flags_len := by simp [hlen.core_ok.flags_len] },
              hlen.scratch_ok⟩

end ActivateLitS5

/-! ## 3. `full_probe_tail_m6_s5_wp` (`FullM6Orch.m6ProbeTailSpec`) -/

section ProbeTailS5

theorem full_probe_tail_m6_s5_wp (Γ : Env)
    (hBackbone : ∀ a m Q X, s5aBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, s5aTransitiveSpec a m Q X →
      Γ "full_transitive_m6" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6ProbeTailSpec a m Q X →
      Func.wp Γ FullFidelityStep13S5ReduceProbe.full_probe_tail_m6_body a m Q X := by
  rintro ⟨h, dticks, ⟨⟩⟩ m Q X hs
  rcases m6ProbeTailSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp FullFidelityStep13S5ReduceProbe.full_probe_tail_m6_body
  refine wp_join_group (ts := [])
    (fun _ m1 => ∃ ext1 s1, FullM6HdrInv c F0 ext1 s1 ∧
      s1.core.cur_level = 0 ∧ s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (FullM6HdrMem c ext1 s1 ⋆ R) m1) ?_ ?_
  · rintro _ _ m1 ⟨ext1, s1, hinv1, hcl1, hfu1, hm1⟩
    rw [Blocks.get_here]
    refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
    c0_hfast_nogrp
    · c0_call hTrans
      refine ⟨c, F0, ext1, s1, R, rfl, hinv1.cfgOk, hinv1.extOk, hinv1.sparse,
        fullM6HdrMem_unfocus hm1f,
        fun r2 ext2 s2 m2 hext2 hsp2 _ _ hclpr2 hfu2 hdom2 hu2 hm2 => ?_⟩
      have hinv2 := FullM6HdrInv.mk_inv hinv1.cfgOk hext2.1 hsp2
      c0_hfast_nogrp
      · exact hQ 20#64 ext2 s2 m2 hsp2.lengths hext2.1 (Nat.le_trans hfu2 hfu1)
          (Or.inr rfl) (fun _ => hu2 ‹_›) (fun h => by cases h) hm2
      · have hr1 : r2 = 1#64 := by
          rcases hdom2 with rfl | rfl
          · rfl
          · contradiction
        exact hQ 1#64 ext2 s2 m2 hsp2.lengths hext2.1 (Nat.le_trans hfu2 hfu1)
          (Or.inl rfl) (fun h => by cases h) (fun _ => ⟨hinv2, hclpr2.1⟩) hm2
    · exact hQ 1#64 ext1 s1 m1 hinv1.sparse.lengths hinv1.extOk hfu1
        (Or.inl rfl) (fun h => by cases h) (fun _ => ⟨hinv1, hcl1⟩) (fullM6HdrMem_unfocus_full hm1f)
  · intro J1 hJ1
    refine wp_m6Hdr_focus_frame hm fun hmf => ?_
    c0_hfast_nogrp
    · c0_call hBackbone
      refine ⟨c, F0, ext, s, R, rfl, hinv.cfgOk, hinv.extOk, hinv.sparse,
        fullM6HdrMem_unfocus hmf,
        fun r1 ext1 s1 m1 hext1 hsp1 _ _ hclpr1 hfu1 hdom1 hu1 hm1 => ?_⟩
      have hinv1 := FullM6HdrInv.mk_inv hinv.cfgOk hext1.1 hsp1
      c0_hfast_nogrp
      · exact hQ 20#64 ext1 s1 m1 hsp1.lengths hext1.1 hfu1 (Or.inr rfl) (fun _ => hu1 ‹_›)
          (fun h => by cases h) hm1
      · exact hJ1 () m1 ⟨ext1, s1, hinv1, hclpr1.1, hfu1, hm1⟩
    · exact hJ1 () m ⟨ext, s, hinv, hcl0, Nat.le_refl _, fullM6HdrMem_unfocus hmf⟩

end ProbeTailS5

/-! ## 4. `full_set_inactive_s5_wp` (`step13SetInactiveSpec`) -/

section SetInactiveS5

private abbrev s5InactVmtfSt (s1 : FullState) (qp qn : List (BitVec 32))
    (qsi qss qf ql : BitVec 64) : FullState :=
  { s1 with
    scratch :=
      { s1.scratch with
        q_prev := qp, q_next := qn, q_search_idx := qsi,
        q_search_stamp := qss, q_first := qf, q_last := ql } }

theorem full_set_inactive_s5_wp (Γ : Env)
    (hHeapUp : ∀ a m Q X, Full.fullHeapUpSpec a m Q X →
      Γ "full_heap_up" [i64, i32] [] a m Q X)
    (hHeapDown : ∀ a m Q X, step13HeapDownSpec a m Q X →
      Γ "full_heap_down" [i64, i32] [] a m Q X) :
    ∀ a m Q X, step13SetInactiveSpec a m Q X →
      Func.wp Γ FullFidelityStep13S5ReduceProbe.full_set_inactive_body a m Q X := by
  rintro ⟨h, v, flag, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hcl := hlen.core_ok
  have hsc := hlen.scratch_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl.cur_vars_le; have hfll := hcl.flags_len; have hvl := hcl.vals_len
  unfold Func.wp FullFidelityStep13S5ReduceProbe.full_set_inactive_body
  c0_hfast_nogrp
  · rw [ite_eq_left (by c0_bound)] at hQ; exact hQ
  · have hv_lt : v.toNat < s.core.cur_vars := by c0_bound
    have hv_mv : v.toNat < c.max_vars := by omega
    have hv_sw : (v.setWidth 64).toNat = v.toNat := by simp [BitVec.toNat_setWidth]; omega
    rw [ite_eq_right (by omega)] at hQ
    have h2v : ((v.setWidth 64) <<< (1 : Nat)).toNat = 2 * v.toNat := by
      rw [BitVec.toNat_shiftLeft, hv_sw]; simp [Nat.shiftLeft_eq]; omega
    refine wp_join_group
      (fun _ mJ => ∃ unass',
        (FullMem c { s with core := { s.core with unassigned := unass' } } ⋆ R) mJ)
      ?_ (fun J hJ => by c0_hfast_nogrp <;> exact hJ () _ ⟨_, by assumption⟩)
    rintro _ _ mJ ⟨unass', hmJ⟩
    have hv_fl : (v.setWidth 64).toNat < s.core.flags.length := by omega
    have hv_qp : (v.setWidth 64).toNat < s.scratch.q_prev.length := by
      rw [hsc.q_prev_len]; omega
    have hv_qn : (v.setWidth 64).toNat < s.scratch.q_next.length := by
      rw [hsc.q_next_len]; omega
    c0_hfast_nogrp
    let s1 : FullState :=
      { s with core := { s.core with
          flags := s.core.flags.set (v.setWidth 64).toNat
            ((s.core.flags[(v.setWidth 64).toNat]'hv_fl &&& ~~~1#32) ||| flag),
          unassigned := unass' } }
    have hlen1 : s1.LengthsOk c :=
      ⟨{ hcl with flags_len := by simp [s1, hfll] }, hsc⟩
    refine wp_join_group
      (fun _ m2 => ∃ qp' qn' qsi' qss' qf' ql',
        let s2 := s5InactVmtfSt s1 qp' qn' qsi' qss' qf' ql'
        s2.LengthsOk c ∧ (FullMem c s2 ⋆ R) m2)
      ?_ ?_
    · rintro _ _ m2 ⟨qp2, qn2, qsi2, qss2, qf2, ql2, hlen2, hm2⟩
      let s2 := s5InactVmtfSt s1 qp2 qn2 qsi2 qss2 qf2 ql2
      have hv_ps : (v.setWidth 64).toNat < s2.scratch.pos.length := by
        rw [hlen2.scratch_ok.pos_len]; omega
      c0_hfast_nogrp
      refine wp_join_group
        (fun _ m3 => ∃ hp' ps' hl',
          let s3 : FullState :=
            { s2 with scratch := { s2.scratch with heap := hp', pos := ps', heap_len := hl' } }
          s3.LengthsOk c ∧ (FullMem c s3 ⋆ R) m3)
        (fun _ _ m3 ⟨hp3, ps3, hl3, hlen3, hm3⟩ => by
          c0_hfast_nogrp
          exact hQ s1.core.flags unass' qp2 qn2 s.scratch.q_stamp qsi2 qss2 qf2 ql2
            hp3 ps3 hl3 m3 hlen3 hm3)
        (fun J3 hJ3 => ?_)
      c0_hfast_nogrp
      · have hn_pos : 0 < (BitVec.ofNat 64 s2.scratch.heap_len).toNat := by c0_bound
        have hcv2 : s2.core.cur_vars ≤ c.max_vars := hlen2.core_ok.cur_vars_le
        have hn_le : (BitVec.ofNat 64 s2.scratch.heap_len).toNat ≤ s2.core.cur_vars := by
          have h1 : (BitVec.ofNat 64 s2.scratch.heap_len).toNat ≤
              (BitVec.ofNat 64 s2.core.cur_vars).toNat := by c0_bound
          simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : s2.core.cur_vars < 2 ^ 64)]
            using h1
        have hhl_len2 : s2.scratch.heap.length = c.max_vars := hlen2.scratch_ok.heap_len_arr
        have hp32_isLt : (s2.scratch.pos[(v.setWidth 64).toNat]'hv_ps).toNat < 2 ^ 32 :=
          (s2.scratch.pos[(v.setWidth 64).toNat]'hv_ps).isLt
        have hp_lt : (s2.scratch.pos[(v.setWidth 64).toNat]'hv_ps).toNat <
            (BitVec.ofNat 64 s2.scratch.heap_len).toNat := by
          have h1 : ((s2.scratch.pos[(v.setWidth 64).toNat]'hv_ps).setWidth 64).toNat <
              s2.scratch.heap_len % 2 ^ 64 := by c0_bound
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)] at h1
          simpa [BitVec.toNat_ofNat] using h1
        have hp_hp : ((s2.scratch.pos[(v.setWidth 64).toNat]'hv_ps).setWidth 64).toNat <
            s2.scratch.heap.length := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hhl_len2]; omega
        c0_hfast_nogrp
        · have hn1_lt : (BitVec.ofNat 64 s2.scratch.heap_len - 1#64).toNat =
              (BitVec.ofNat 64 s2.scratch.heap_len).toNat - 1 := by
            have h1 : 0 < s2.scratch.heap_len % 2 ^ 64 := by
              simpa [BitVec.toNat_ofNat] using hn_pos
            rw [BitVec.toNat_sub]; simp [BitVec.toNat_ofNat]; omega
          have hn1_hp : (BitVec.ofNat 64 s2.scratch.heap_len - 1#64).toNat <
              s2.scratch.heap.length := by rw [hn1_lt, hhl_len2]; omega
          let hl' := (BitVec.ofNat 64 s2.scratch.heap_len - 1#64).toNat
          have hhl'_bv : BitVec.ofNat 64 hl' = BitVec.ofNat 64 s2.scratch.heap_len - 1#64 := by
            apply BitVec.eq_of_toNat_eq; simp [hl']
          let last32 := s2.scratch.heap[(BitVec.ofNat 64 s2.scratch.heap_len - 1#64).toNat]'hn1_hp
          let p32 := s2.scratch.pos[(v.setWidth 64).toNat]'hv_ps
          c0_hfast_nogrp
          refine wp_join_group
            (fun _ m4 => ∃ hp4 ps4,
              let s4 : FullState :=
                { s2 with scratch :=
                  { s2.scratch with heap := hp4, pos := ps4, heap_len := hl' } }
              s4.LengthsOk c ∧ (FullMem c s4 ⋆ R) m4)
            (fun _ _ m4 ⟨hp4, ps4, hlen4, hm4⟩ => by
              c0_hfast_nogrp
              exact hJ3 () m4 ⟨hp4, ps4, hl', hlen4, hm4⟩)
            (fun J4 hJ4 => ?_)
          c0_hfast_nogrp
          · have hl_isLt : last32.toNat < 2 ^ 32 := last32.isLt
            have hl_lt : last32.toNat < s2.core.cur_vars := by
              have h1 : (last32.setWidth 64).toNat < s2.core.cur_vars % 2 ^ 64 := by
                dsimp only [last32]; c0_bound
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : last32.toNat < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : s2.core.cur_vars < 2 ^ 64)] at h1
              exact h1
            have hl_ps : (last32.setWidth 64).toNat <
                (s2.scratch.pos.set (v.setWidth 64).toNat 4294967295#32).length := by
              rw [List.length_set, hlen2.scratch_ok.pos_len]
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : last32.toNat < 2 ^ 64)]
              omega
            c0_hfast_nogrp
            let s2a : FullState :=
              { s2 with scratch :=
                { s2.scratch with
                  heap_len := hl'
                  heap := s2.scratch.heap.set (p32.setWidth 64).toNat last32
                  pos := (s2.scratch.pos.set (v.setWidth 64).toNat 4294967295#32).set
                    (last32.setWidth 64).toNat p32 } }
            have hlen2a : s2a.LengthsOk c :=
              ⟨hlen2.core_ok, { hlen2.scratch_ok with
                heap_len_arr := by
                  dsimp only [s2a, s2, s5InactVmtfSt]
                  rw [List.length_set]
                  exact hsc.heap_len_arr
                pos_len := by
                  dsimp only [s2a, s2, s5InactVmtfSt]
                  rw [List.length_set, List.length_set]
                  exact hsc.pos_len }⟩
            c0_call hHeapUp
            refine ⟨c, s2a, R, rfl, hlen2a, ?_, fun _ s3 m3 hcore3 hlen3 hup3 hm3 => ?_⟩
            · dsimp only [s2a]
              try rw [hhl'_bv]
              assumption
            · obtain ⟨hp3, ps3, hsc3⟩ := hup3.2
              have hs3_eq : s3 =
                  { s2a with scratch := { s2a.scratch with heap := hp3, pos := ps3 } } := by
                cases s3; simp only [FullState.mk.injEq]; exact ⟨hcore3, hsc3⟩
              c0_hfast_nogrp
              c0_call hHeapDown
              refine ⟨c, s3, R, rfl, hlen3, hm3, fun _ s4 m4 hcore4 hlen4 hdn4 hm4 => ?_⟩
              obtain ⟨hp4, ps4, hsc4⟩ := hdn4
              have hcore4' : s4.core = s2.core := hcore3.trans hcore4
              have hsc4' : s4.scratch =
                  { s2.scratch with heap := hp4, pos := ps4, heap_len := hl' } := by
                rw [hsc4, hsc3]
              have hs4_eq : s4 =
                  { s2 with scratch :=
                    { s2.scratch with heap := hp4, pos := ps4, heap_len := hl' } } := by
                cases s4
                dsimp only [FullState.mk.injEq] at *
                congr 1
              rw [hs4_eq] at hlen4 hm4
              exact hJ4 () m4 ⟨hp4, ps4, hlen4, hm4⟩
          · let s2b : FullState :=
              { s2 with scratch :=
                { s2.scratch with
                  pos := s2.scratch.pos.set (v.setWidth 64).toNat 4294967295#32
                  heap_len := hl' } }
            have hlen2b : s2b.LengthsOk c :=
              ⟨hlen2.core_ok, { hlen2.scratch_ok with
                pos_len := by
                  dsimp only [s2b, s2, s5InactVmtfSt]
                  rw [List.length_set]
                  exact hsc.pos_len }⟩
            refine hJ4 () _ ⟨s2.scratch.heap,
              s2.scratch.pos.set (v.setWidth 64).toNat 4294967295#32, hlen2b, ?_⟩
            dsimp only [s2b]
            try rw [hhl'_bv]
            assumption
          · let s2b : FullState :=
              { s2 with scratch :=
                { s2.scratch with
                  pos := s2.scratch.pos.set (v.setWidth 64).toNat 4294967295#32
                  heap_len := hl' } }
            have hlen2b : s2b.LengthsOk c :=
              ⟨hlen2.core_ok, { hlen2.scratch_ok with
                pos_len := by
                  dsimp only [s2b, s2, s5InactVmtfSt]
                  rw [List.length_set]
                  exact hsc.pos_len }⟩
            refine hJ4 () _ ⟨s2.scratch.heap,
              s2.scratch.pos.set (v.setWidth 64).toNat 4294967295#32, hlen2b, ?_⟩
            dsimp only [s2b]
            try rw [hhl'_bv]
            assumption
        · exact hJ3 () m2 ⟨s2.scratch.heap, s2.scratch.pos, s2.scratch.heap_len, hlen2, hm2⟩
      · exact hJ3 () m2 ⟨s2.scratch.heap, s2.scratch.pos, s2.scratch.heap_len, hlen2, hm2⟩
      · exact hJ3 () m2 ⟨s2.scratch.heap, s2.scratch.pos, s2.scratch.heap_len, hlen2, hm2⟩
      · exact hJ3 () m2 ⟨s2.scratch.heap, s2.scratch.pos, s2.scratch.heap_len, hlen2, hm2⟩
    · intro J2 hJ2
      c0_hfast_nogrp
      refine wp_join_group
        (fun _ m_in => (FullMem c s1 ⋆ R) m_in)
        ?_
        (fun J_then hJ_then => by
          c0_hfast_nogrp
          · exact hJ_then () _ (by assumption)
          · exact hJ_then () _ (by assumption)
          · exact hJ_then () _ (by assumption)
          · exact hJ_then () _ (by assumption)
          · refine hJ2 () _ ⟨s1.scratch.q_prev, s1.scratch.q_next, s1.scratch.q_search_idx,
              s1.scratch.q_search_stamp, s1.scratch.q_first, s1.scratch.q_last, hlen1, ?_⟩
            assumption)
      rintro _ _ m_in hm_in
      c0_hfast_nogrp
      refine wp_join_group
        (fun _ ms => ∃ qsi' qss',
          let ss : FullState :=
            { s1 with scratch :=
              { s1.scratch with
                q_search_idx := qsi'
                q_search_stamp := qss' } }
          ss.LengthsOk c ∧ (FullMem c ss ⋆ R) ms)
        ?_
        (fun Js hJs => by
          c0_hfast_nogrp
          · refine wp_join_group (ts := [i32])
              (fun _ m_srch => (FullMem c s1 ⋆ R) m_srch)
              ?_
              (fun Jsrch hJsrch => by
                c0_hfast_nogrp
                · exact hJsrch (s1.scratch.q_prev[(v.setWidth 64).toNat]'hv_qp, ()) m_in hm_in
                · exact hJsrch (s1.scratch.q_next[(v.setWidth 64).toNat]'hv_qn, ()) m_in hm_in)
            rintro _ ⟨srch, ⟨⟩⟩ m_srch hm_srch
            have hlen_srch : ∀ qsi' qss',
                ({ s1 with scratch :=
                  { s1.scratch with q_search_idx := qsi', q_search_stamp := qss' } } :
                  FullState).LengthsOk c := fun _ _ =>
              ⟨hlen1.core_ok, { hlen1.scratch_ok with }⟩
            c0_hfast_nogrp
            refine wp_join_group
              (fun _ m_res => ∃ qsi' qss',
                ({ s1 with scratch :=
                  { s1.scratch with q_search_idx := qsi', q_search_stamp := qss' } } :
                  FullState).LengthsOk c ∧
                (FullMem c { s1 with scratch :=
                  { s1.scratch with q_search_idx := qsi', q_search_stamp := qss' } } ⋆ R) m_res)
              (fun _ _ m_res ⟨qsi', qss', hl_res, hm_res⟩ => by
                c0_hfast_nogrp
                exact hJs () m_res ⟨qsi', qss', hl_res, hm_res⟩)
              (fun Js1 hJs1 => by
                c0_hfast_nogrp
                · refine hJs1 () _ ⟨4294967295#64, 0#64, hlen_srch _ _, ?_⟩
                  assumption
                · have hsrch_lt : (srch.setWidth 64).toNat < s1.scratch.q_stamp.length := by
                    rw [hlen1.scratch_ok.q_stamp_len]
                    have h1 : (srch.setWidth 64).toNat < s.core.cur_vars % 2 ^ 64 := by c0_bound
                    rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at h1
                    omega
                  c0_hfast_nogrp
                  refine hJs1 () _ ⟨srch.setWidth 64,
                    (s1.scratch.q_stamp[(srch.setWidth 64).toNat]'hsrch_lt).setWidth 64,
                    hlen_srch _ _, ?_⟩
                  assumption)
          · refine hJs () m_in ⟨s1.scratch.q_search_idx, s1.scratch.q_search_stamp,
              ⟨hlen1.core_ok, { hlen1.scratch_ok with }⟩, hm_in⟩)
      rintro _ _ ms ⟨qsi', qss', hlens, hms⟩
      let pv32 := s1.scratch.q_prev[(v.setWidth 64).toNat]'hv_qp
      let nv32 := s1.scratch.q_next[(v.setWidth 64).toNat]'hv_qn
      have hv_qp' : (v.setWidth 64).toNat < s1.scratch.q_prev.length := hv_qp
      have hv_qn' : (v.setWidth 64).toNat < s1.scratch.q_next.length := hv_qn
      c0_hfast_nogrp
      refine wp_join_group
        (fun _ mf => ∃ qn' qf',
          let sf : FullState :=
            { s1 with scratch :=
              { s1.scratch with
                q_prev := s1.scratch.q_prev.set (v.setWidth 64).toNat 4294967295#32
                q_next := qn'
                q_search_idx := qsi'
                q_search_stamp := qss'
                q_first := qf' } }
          sf.LengthsOk c ∧ (FullMem c sf ⋆ R) mf)
        ?_
        (fun Jf hJf => by
          c0_hfast_nogrp
          · refine hJf () _ ⟨s1.scratch.q_next.set (v.setWidth 64).toNat 4294967295#32,
              nv32.setWidth 64, ?_, ?_⟩
            · exact ⟨hlens.core_ok, { hlens.scratch_ok with
                q_prev_len := by simp [hlens.scratch_ok.q_prev_len]
                q_next_len := by simp [hlens.scratch_ok.q_next_len] }⟩
            · assumption
          · have hpv_qn : (pv32.setWidth 64).toNat <
                (s1.scratch.q_next.set (v.setWidth 64).toNat 4294967295#32).length := by
              rw [List.length_set, hlens.scratch_ok.q_next_len]
              have hv_qp0 : v.toNat < s1.scratch.q_prev.length := by rw [← hv_sw]; exact hv_qp
              have hpv_eq : pv32 = s1.scratch.q_prev[v.toNat]'hv_qp0 := by
                dsimp only [pv32]; simp only [hv_sw]
              have h1 : ((s1.scratch.q_prev[v.toNat]'hv_qp0).setWidth 64).toNat <
                  s.core.cur_vars % 2 ^ 64 := by dsimp only [s1]; c0_bound
              rw [← hpv_eq, BitVec.toNat_setWidth,
                Nat.mod_eq_of_lt (by have := pv32.isLt; omega : pv32.toNat < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at h1
              rw [BitVec.toNat_setWidth,
                Nat.mod_eq_of_lt (by have := pv32.isLt; omega : pv32.toNat < 2 ^ 64)]
              omega
            c0_hfast_nogrp
            let qn_upd := (s1.scratch.q_next.set (v.setWidth 64).toNat 4294967295#32).set
              (pv32.setWidth 64).toNat nv32
            refine hJf () _ ⟨qn_upd, s1.scratch.q_first, ?_, ?_⟩
            · exact ⟨hlens.core_ok, { hlens.scratch_ok with
                q_prev_len := by simp [hlens.scratch_ok.q_prev_len]
                q_next_len := by simp [qn_upd, hlens.scratch_ok.q_next_len] }⟩
            · assumption)
      rintro _ _ mf ⟨qn', qf', hlenf, hmf⟩
      c0_hfast_nogrp
      refine wp_join_group
        (fun _ ml => ∃ qp' ql',
          let sl : FullState :=
            { s1 with scratch :=
              { s1.scratch with
                q_prev := qp'
                q_next := qn'
                q_search_idx := qsi'
                q_search_stamp := qss'
                q_first := qf'
                q_last := ql' } }
          sl.LengthsOk c ∧ (FullMem c sl ⋆ R) ml)
        (fun _ _ ml ⟨qp', ql', hll, hml⟩ => by
          c0_hfast_nogrp
          exact hJ2 () ml ⟨qp', qn', qsi', qss', qf', ql', hll, hml⟩)
        (fun Jl hJl => ?_)
      c0_hfast_nogrp
      · refine hJl () _ ⟨s1.scratch.q_prev.set (v.setWidth 64).toNat 4294967295#32,
          pv32.setWidth 64, ⟨hlenf.core_ok, { hlenf.scratch_ok with }⟩, ?_⟩
        assumption
      · have hnv_qp : (nv32.setWidth 64).toNat <
            (s1.scratch.q_prev.set (v.setWidth 64).toNat 4294967295#32).length := by
          rw [hlenf.scratch_ok.q_prev_len]
          have hv_qn0 : v.toNat < s1.scratch.q_next.length := by rw [← hv_sw]; exact hv_qn
          have hnv_eq : nv32 = s1.scratch.q_next[v.toNat]'hv_qn0 := by
            dsimp only [nv32]; simp only [hv_sw]
          have h1 : ((s1.scratch.q_next[v.toNat]'hv_qn0).setWidth 64).toNat <
              s.core.cur_vars % 2 ^ 64 := by dsimp only [s1]; c0_bound
          rw [← hnv_eq, BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt (by have := nv32.isLt; omega : nv32.toNat < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at h1
          rw [BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt (by have := nv32.isLt; omega : nv32.toNat < 2 ^ 64)]
          omega
        c0_hfast_nogrp
        let qp_upd := (s1.scratch.q_prev.set (v.setWidth 64).toNat 4294967295#32).set
          (nv32.setWidth 64).toNat pv32
        refine hJl () _ ⟨qp_upd, s1.scratch.q_last, ?_, ?_⟩
        · exact ⟨hlenf.core_ok, { hlenf.scratch_ok with
            q_prev_len := by
              dsimp only [qp_upd]
              rw [List.length_set, hlenf.scratch_ok.q_prev_len] }⟩
        · assumption

end SetInactiveS5

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5
