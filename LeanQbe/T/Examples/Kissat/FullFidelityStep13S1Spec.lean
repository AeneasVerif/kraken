/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec
public import LeanQbe.T.Examples.Kissat.FullM4SweepSpec
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof4a
public import LeanQbe.T.Examples.Kissat.FullFidelityBveProof0
public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof0
public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof2
public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof6

/-!
# Kissat Fidelity Step 13 Shard S1 — Specifications (`FullFidelityStep13S1Spec`)

Parametric Step-13 `Spec` contracts (`0` cross-shard `S0/S2/S3/S4/S5` code imports, `0` `@[expose]`
on theorems/lemmas, `<= 100` cols, `< 1,400` LOC) for all `S1` ADD/lifted MOD functions and shared
Step-13 callee boundaries (`#3057` & `#3059`):
- `f64uPure1Spec`, `f64uPure2Spec` (`S0` soft-float helpers),
- `step13UpdateClassifyM6Spec`, `step13PropagateM6Spec` (`S2` `FullM6HdrMem` helpers),
- `step13FwdFlushLargeCoreSpec` (sparse/dense large-watch flush for `full_dense_bin_*roundtrip`),
- `K6HwmClean`, `step13K6InitSpec`, `step13K6AddClauseSpec`,
  `step13Sweep{Cone,Sim,Units,Classes}Spec`,
- `step13DenseOccCntSpec`, `step13EnterDenseExM6Spec`, `step13EnterDenseM6Spec`,
- `step13DenseBin{,Sort}RoundtripSpec`, `step13WatchLargeClausesSpec`,
- `step13ElsArSpec`, `step13ElsLitSpec`, `step13DenseElsSpec`, `step13SweepVarSpec`,
- `step13CollectCandsSpec`, `step13Has{Factor,Elim}CandsSpec`, `step13BveVarKeySpec`,
- `step13EliminateM6Spec`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullFidelityBve

@[expose] public section

/-! ## 1. Shared `S0`/`S2`/Step-12 Callee `Spec` Contracts -/

/-- Pure 1-arg `f64u_*` soft-float contract (`S0`). -/
def f64uPure1Spec : Spec [i64] [i64] := fun _ m Q _ =>
  ∀ r : BitVec 64, Q (r, ()) m

/-- Pure 2-arg `f64u_*` soft-float contract (`S0`). -/
def f64uPure2Spec : Spec [i64, i64] [i64] := fun _ m Q _ =>
  ∀ r : BitVec 64, Q (r, ()) m

/-- Step-13 `full_update_classify_fid` contract over `FullM6HdrMem` (`m6HdrW2aSpec [] []`). -/
abbrev step13UpdateClassifyM6Spec : Spec [i64] [] :=
  m6HdrW2aSpec [] []

/-- Step-13 `full_propagate` contract over `FullM6HdrMem` (`fullBcpS15Spec` + `M6HdrExt`). -/
def step13PropagateM6Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
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
              unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
              wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
              confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
          scratch := sc' }
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      FullProbeScratchPres { s with scratch := { s.scratch with
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

/-- General `full_fwd_flush_large_m7` contract working in both sparse and dense modes
(`FullWitnessInv`, arbitrary `dense_mode` and `cur_level`). -/
def step13FwdFlushLargeCoreSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.dense_mode = s.core.dense_mode →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.vals = s.core.vals → s'.core.lvl = s.core.lvl → s'.core.flags = s.core.flags →
      s'.core.fuel = s.core.fuel → s'.core.oom = s.core.oom →
      s'.core.inconsistent = s.core.inconsistent →
      s'.core.d_cur = s.core.d_cur → s'.core.d_val = s.core.d_val →
      s'.core.num_binary = s.core.num_binary →
      s'.core.frame_trail = s.core.frame_trail → s'.core.frame_dec = s.core.frame_dec →
      s'.core.trail_end = s.core.trail_end → s'.core.propagated = s.core.propagated →
      s'.core.probing = s.core.probing →
      s'.scratch.last_learned = s.scratch.last_learned →
      s'.scratch.extend_len = s.scratch.extend_len →
      s'.scratch.walk_vals = s.scratch.walk_vals →
      s'.scratch.walk_best = s.scratch.walk_best →
      s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.sim_sig = s.scratch.sim_sig →
      (FullMem c s' ⋆ R) m' → Q () m'

/-! ## 2. S1-C `K6HwmClean`, `step13K6InitSpec`, `step13K6AddClauseSpec` -/

/-- `L6a` / `R1` high-water-mark cleanliness invariant on `K6` variable/literal arrays:
either `hw = 0xFFFFFFFF#32` (cold start, full zeroing required) or all entries in `[hw ..< mv)`
already satisfy the initial `K6` defaults (`lvl=0, rsn=0xFFFFFFFF, flags=0, vals=0, whead=-1`). -/
def K6HwmClean (L : K6Layout) (hw : BitVec 32) (ks : K6State) : Prop :=
  hw = 0xFFFFFFFF#32 ∨
  (hw.toNat ≤ L.maxV ∧
    ∀ v, hw.toNat ≤ v → v < L.maxV →
      ks.lvlArr[v]?.getD 0#32 = 0#32 ∧
      ks.rsn[v]?.getD 0#32 = 0xFFFFFFFF#32 ∧
      ks.flags[v]?.getD 0#32 = 0#32 ∧
      ks.vals[2 * v]?.getD 0#32 = 0#32 ∧
      ks.vals[2 * v + 1]?.getD 0#32 = 0#32 ∧
      ks.whead[2 * v]?.getD 0#32 = 0xFFFFFFFF#32 ∧
      ks.whead[2 * v + 1]?.getD 0#32 = 0xFFFFFFFF#32)

/-- Step-13 `full_k6_init` contract (`glue_used[33]` HWM tracking + `K6HwmClean`). -/
def step13K6InitSpec : Spec [i64, i32] [] := fun (h, nv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    (c.scratch_cap < k6MinScr ∨ k6MaxV c.scratch_cap < nv.toNat → Q () m) ∧
    (k6MinScr ≤ c.scratch_cap → nv.toNat ≤ k6MaxV c.scratch_cap →
      ∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
        K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32)
          (k6StateOfScratch L s.scratch.scratch_buf) ∧
        ∀ (scr' gu' : List (BitVec 32)) (m' : Mem 64),
          let ks' := k6StateOfScratch L scr'
          let s' : FullState :=
            { s with scratch := { s.scratch with scratch_buf := scr', glue_used := gu' } }
          s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
          (∀ i < 64, i ≠ 33 → gu'[i]? = s.scratch.glue_used[i]?) →
          (nv.toNat = L.maxV → gu'[33]? = some 0#32) →
          (nv.toNat < L.maxV →
            gu'[33]? = some 0xFFFFFFFF#32 ∨ nv.toNat ≤ (gu'[33]?.getD 0#32).toNat) →
          K6HwmClean L (gu'[33]?.getD 0#32) ks' →
          (∀ P, K6Inv L P ks') → K6TrailSynced ks' →
          ks'.nv = nv → ks'.nc = 0#32 → ks'.lvl = 0#32 → ks'.prop = 0#32 →
          ks'.trl_end = 0#32 → ks'.unass = nv → ks'.incons = 0#32 → ks'.nassump = 0#32 →
          ks'.status = 0#32 → ks'.openCnt = 0#32 → ks'.neq = 0#32 →
          (FullMem c s' ⋆ R) m' → Q () m')

/-- Step-13 `full_k6_add_clause` contract (`glue_used[33]` HWM update + `K6HwmClean`). -/
def step13K6AddClauseSpec : Spec [i64, i64, i32] [.bool] := fun (h, lits_ptr, sz, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (P : (Nat → Bool) → Prop) (L : K6Layout)
    (scr gu xs : List (BitVec 32)) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.scratch.scratch_buf = scr ∧ s.scratch.glue_used = gu ∧
    L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
    K6Inv L P (k6StateOfScratch L scr) ∧ K6TrailSynced (k6StateOfScratch L scr) ∧
    (k6StateOfScratch L scr).lvl = 0#32 ∧ sz.toNat ≤ xs.length ∧ sz.toNat < 2 ^ 28 ∧
    (∀ i < sz.toNat, (xs[i]?.getD 0#32).toNat < 2 * (k6StateOfScratch L scr).nv.toNat) ∧
    SemEntails P ((xs.take sz.toNat).map BitVec.toNat) ∧
    K6HwmClean L (gu[33]?.getD 0#32) (k6StateOfScratch L scr) ∧
    (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ array (t := i32) c.pScratchBuf scr ⋆
      array (t := i32) c.pGlueUsed gu ⋆ array (t := i32) lits_ptr xs ⋆ R) m ∧
    ∀ (ok : Bool) (scr' gu' : List (BitVec 32)) (m' : Mem 64),
      let ks := k6StateOfScratch L scr; let ks' := k6StateOfScratch L scr'
      let s' : FullState :=
        { s with scratch := { s.scratch with scratch_buf := scr', glue_used := gu' } }
      s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = scr[i]?) →
      (∀ i < 64, i ≠ 33 → gu'[i]? = gu[i]?) →
      K6HwmClean L (gu'[33]?.getD 0#32) ks' →
      K6Inv L P ks' → K6TrailSynced ks' → ks'.lvl = 0#32 → ks'.nv = ks.nv →
      ks'.nassump = ks.nassump → k6AssumpLitsS L scr' = k6AssumpLitsS L scr →
      (ok = false → ks' = ks) →
      (2 ≤ sz.toNat → ks'.trl_end = ks.trl_end ∧ ks'.prop = ks.prop ∧
        ks'.unass = ks.unass ∧ ks'.incons = ks.incons) →
      (∀ M, (∀ i < sz.toNat, (xs[i]?.getD 0#32).toNat < 2 * M) →
        K6LitsBounded M ks → (∀ l ∈ k6TrailLits ks, l < 2 * M) →
        K6LitsBounded M ks' ∧ (∀ l ∈ k6TrailLits ks', l < 2 * M)) →
      (array64 (c.hdr + 32) (Full.hdrTailWords c s') ⋆ array (t := i32) c.pScratchBuf scr' ⋆
        array (t := i32) c.pGlueUsed gu' ⋆ array (t := i32) lits_ptr xs ⋆ R) m' →
      Q (ok, ()) m'

/-- Step-13 `K6HwmClean`-preserving `full_m6_sweep_cone` contract. -/
def step13SweepConeSpec : Spec [i64, i32] [i64] := fun (h, root_v, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ k6MinScr ≤ c.scratch_cap ∧
    root_v.toNat < s.core.cur_vars ∧ M6TmkZero s ∧
    (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
      K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32)
        (k6StateOfScratch L s.scratch.scratch_buf)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r tmp' ws1' tmk' scr' gu' m',
      let s' : FullState :=
        { s with
          core := { s.core with tmp := tmp' }
          scratch := { s.scratch with work_stk1 := ws1', tarjan_mark := tmk',
                                      scratch_buf := scr', glue_used := gu' } }
      let nv := (r &&& 0xFFFF#64).toNat
      let nc := (r >>> 16).toNat
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.vals = s.core.vals →
      s'.core.inconsistent = s.core.inconsistent → M6SweepConeOk F_cur s' nv →
      nc ≤ 3 * k6MaxV c.scratch_cap → r.toNat = nv + nc * 2 ^ 16 →
      (∀ i < 64, i ≠ 33 → gu'[i]? = s.scratch.glue_used[i]?) →
      (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
        K6HwmClean L (gu'[33]?.getD 0#32) (k6StateOfScratch L scr')) →
      (∀ v < s.core.cur_vars, tmk'[v]?.getD 0#32 ≠ 0#32 →
        ∃ i < nv, (ws1'[i]?.getD 0#32).toNat = v) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Step-13 `K6HwmClean`-preserving `full_m6_sweep_sim` contract. -/
def step13SweepSimSpec : Spec [i64, i32, i64] [i32] := fun (h, nv, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ M6SweepConeOk F_cur s nv.toNat ∧
    (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
      K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32)
        (k6StateOfScratch L s.scratch.scratch_buf)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r fuel' rng' sig' scr' m',
      let s' : FullState := { s with core := { s.core with fuel := fuel' }
                                     scratch := { s.scratch with rng_state := rng',
                                                                 sim_sig := sig',
                                                                 scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → fuel'.toNat ≤ s.core.fuel.toNat →
      M6SweepConeOk F_cur s' nv.toNat →
      (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
        K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32) (k6StateOfScratch L scr')) →
      (r = 0xFFFFFFFF#32 → (cnfOfClauses F_cur).Unsat) →
      (r ≠ 0xFFFFFFFF#32 → r.toNat ≤ 64) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Step-13 `K6HwmClean`-preserving `full_m6_sweep_units` contract. -/
def step13SweepUnitsSpec : Spec [i64, i32, i32, i64] [i64] :=
  fun (h, nv, rbit_in, _tlim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ M6SweepConeOk F_cur s nv.toNat ∧
      rbit_in.toNat ≤ 64 ∧
      (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
        K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32)
          (k6StateOfScratch L s.scratch.scratch_buf)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.repr = s.core.repr →
        s'.scratch.work_stk1 = s.scratch.work_stk1 →
        s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
        s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
        s'.scratch.glue_used = s.scratch.glue_used →
        M6SweepConeOk F_cur s' nv.toNat →
        (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
          K6HwmClean L (s'.scratch.glue_used[33]?.getD 0#32)
            (k6StateOfScratch L s'.scratch.scratch_buf)) →
        (r = 0xFFFFFFFFFFFFFFFF#64 → F0.Unsat) →
        (r ≠ 0xFFFFFFFFFFFFFFFF#64 → r.toNat ≤ 64) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Step-13 `K6HwmClean`-preserving `full_m6_sweep_classes` contract. -/
def step13SweepClassesSpec : Spec [i64, i32, i32, i64] [i64] :=
  fun (h, nv, rbit_in, _tlim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ M6SweepConeOk F_cur s nv.toNat ∧
      rbit_in.toNat ≤ 64 ∧
      (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
        K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32)
          (k6StateOfScratch L s.scratch.scratch_buf)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.repr = s.core.repr →
        s'.scratch.work_stk1 = s.scratch.work_stk1 →
        s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
        s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
        s'.scratch.glue_used = s.scratch.glue_used →
        (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
          K6HwmClean L (s'.scratch.glue_used[33]?.getD 0#32)
            (k6StateOfScratch L s'.scratch.scratch_buf)) →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (r = 1#64 → ∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
          M6EqBufOk F_cur s' (k6StateOfScratch L s'.scratch.scratch_buf).neq.toNat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Step-13 `glue_used`-preserving `full_m6_dense_prop` contract (`S6` callee lift). -/
def step13DensePropSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.repr = s.core.repr →
      s'.core.arena_len = s.core.arena_len →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = true ↔ s'.core.inconsistent = 0#64) →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-! ## 3. S1-A `Spec` Contracts (`5` ADD + lifted MOD) -/

/-- `full_sort_bin_watches_fid`: in-place Knuth Shellsort of every literal's binary watch prefix,
preserving `FullSparseInvW`, `WatchesInv`, `core` (all fields except `wstk`), and `wstk.length`. -/
def step13SortBinWatchesSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (wstk' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with core := { s.core with wstk := wstk' } }
      wstk'.length = c.wcap →
      FullSparseInvW c F0 F_cur s' →
      WatchesInv F_cur s'.core →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- `full_dense_occ_cnt_fid`: pure read-only watch occurrence counter capped at `cap + 1`. -/
def step13DenseOccCntSpec : Spec [i64, i32, i64] [i64] := fun (h, lit, _cap, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ lit.toNat < 2 * s.core.cur_vars ∧
    (FullMem c s ⋆ R) m ∧ ∀ r : BitVec 64, Q (r, ()) m

/-- `full_enter_dense_ex_fid`: parameterized `enter_dense(h, connect_large)` over
`FullM6HdrMem` (`full_propagate`). -/
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

/-- `full_enter_dense`: `FullM6HdrMem`-threaded Step-13 `full_enter_dense_ex_fid(h, true)`. -/
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

/-- Shared binary-watch rebuild contract for `full_dense_bin_roundtrip_fid` and
`full_dense_bin_sort_roundtrip_fid`, valid in both sparse (`full_walk_m7`) and dense
(`full_probe_m6`) modes. -/
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
      s'.core.probing = s.core.probing → FullArenaPermEq s.core s'.core →
      s'.scratch.extend_len = s.scratch.extend_len →
      s'.scratch.walk_vals = s.scratch.walk_vals →
      s'.scratch.walk_best = s.scratch.walk_best →
      s'.scratch.last_learned = s.scratch.last_learned →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- Alias for `full_dense_bin_sort_roundtrip_fid`. -/
abbrev step13DenseBinSortRoundtripSpec : Spec [i64] [] := step13DenseBinRoundtripSpec

/-- `full_watch_large_clauses_fid`: ranks large arena clauses & pushes 2WL watches, preserving
`FullCoreInv` (and `FullSparseInv` when `dense_mode = 0`). -/
def step13WatchLargeClausesSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
    s.core.dense_mode = 0#64 ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.dense_mode = s.core.dense_mode →
      s'.core.arena_len = s.core.arena_len →
      s'.core.vals = s.core.vals → s'.core.lvl = s.core.lvl → s'.core.flags = s.core.flags →
      s'.core.fuel = s.core.fuel → s'.core.inconsistent = s.core.inconsistent →
      s'.core.d_cur = s.core.d_cur → s'.core.d_val = s.core.d_val →
      s'.core.probing = s.core.probing → FullArenaPermEq s.core s'.core →
      s'.scratch.extend_len = s.scratch.extend_len →
      s'.scratch.walk_vals = s.scratch.walk_vals →
      s'.scratch.walk_best = s.scratch.walk_best →
      s'.scratch.last_learned = s.scratch.last_learned →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- Step-13 `full_m6_els_ar` using `FullCongReprInv` (supports union-find path compression). -/
def step13ElsArSpec : Spec [i64, i32, i32] [.bool] := fun (h, cr, rl, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ cr.toNat ∈ fullArenaClauseRefs s ∧
    rl.toNat < 2 * s.core.cur_vars ∧ FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel →
      FullCongReprInv F_cur (2 * s.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Step-13 `full_m6_els_lit` using `FullCongReprInv`. -/
def step13ElsLitSpec : Spec [i64, i32, i32] [.bool] := fun (h, l, rl, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ l.toNat < 2 * s.core.cur_vars ∧
    rl.toNat < 2 * s.core.cur_vars ∧ LitEquiv (cnfOfClauses F_cur) l.toNat rl.toNat ∧
    FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel →
      FullCongReprInv F_cur (2 * s.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Step-13 `full_m6_dense_els` using `FullCongReprInv` (incremental union-find fold + ELS). -/
def step13DenseElsSpec : Spec [i64, i32] [.bool] := fun (h, neq, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ M6EqBufOk F_cur s neq.toNat ∧
    FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel →
      FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Step-13 `full_m6_sweep_var` using `FullCongReprInv` + `K6HwmClean`. -/
def step13SweepVarSpec : Spec [i64, i32, i64] [i64] := fun (h, root_v, _tlim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ k6MinScr ≤ c.scratch_cap ∧
    root_v.toNat < s.core.cur_vars ∧ M6TmkZero s ∧
    FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
    (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
      K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32)
        (k6StateOfScratch L s.scratch.scratch_buf)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → M6TmkZero s' →
      FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (∀ i < 64, i ≠ 33 → s'.scratch.glue_used[i]? = s.scratch.glue_used[i]?) →
      (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
        K6HwmClean L (s'.scratch.glue_used[33]?.getD 0#32)
          (k6StateOfScratch L s'.scratch.scratch_buf)) →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Step-13 `full_m6_collect_cands` requiring `WatchStackLayout s.core` for
`full_dense_occ_cnt_fid`. -/
def step13CollectCandsSpec : Spec [i64] [i32] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ nc trc' ws2' m',
      let s' : FullState :=
        { s with scratch := { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } }
      s'.LengthsOk c → nc.toNat ≤ s.core.cur_vars →
      (∀ i < nc.toNat, (trc'[i]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c s' ⋆ R) m' → Q (nc, ()) m'

/-! ## 4. S1-B `Spec` Contracts (`2` ADD + lifted MOD) -/

/-- Pure read-only predicate spec shared by `full_has_factor_cands_fid` and
`full_has_elim_cands_fid`. -/
def step13HasCandsSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧ ∀ r : Bool, Q (r, ()) m

/-- `full_has_factor_cands_fid`. -/
abbrev step13HasFactorCandsSpec : Spec [i64] [.bool] := step13HasCandsSpec

/-- `full_has_elim_cands_fid`. -/
abbrev step13HasElimCandsSpec : Spec [i64] [.bool] := step13HasCandsSpec

/-- Step-13 `full_bve_var_key_m7` requiring `WatchStackLayout s.core` for
`full_dense_occ_cnt_fid`. -/
def step13BveVarKeySpec : Spec [i64, i32] [i64] := fun (h, _v, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ r : BitVec 64, Q (r, ()) m

/-- Step-13 `@[expose]` contract for `full_fwd_scan_lit_m7` (`fullFwdScanLitM7Spec`). -/
def step13FwdScanLitSpec : Spec [i64, i32, i32, i32, .bool] [i32] :=
  fun (h, cref, sz, scan_lit, check_bins, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧ FullArenaVarsNodup s ∧
      cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
      sz.toNat = fullArenaClauseSize s cref.toNat ∧ scan_lit.toNat < 2 * s.core.cur_vars ∧
      (check_bins = true → scan_lit.toNat ∈ fullArenaClauseLits s cref.toNat) ∧
      (∀ x < 2 * s.core.cur_vars,
        s.core.lit_mark[x]?.getD 0#8 ≠ 0#8 ↔ x ∈ fullArenaClauseLits s cref.toNat) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r : BitVec 32,
        (r = 0xFFFFFFFF#32 ∨ r = 0xFFFFFFFE#32 ∨
          (r.toNat ∈ fullArenaClauseLits s cref.toNat ∧
            (cnfOfClauses F_cur).EntailsClause
              (cnfClause ((fullArenaClauseLits s cref.toNat).filter (· != r.toNat))))) →
        Q (r, ()) m

/-- Step-13 `@[expose]` contract for `full_fwd_connect_subsumer_m7`
(`fullFwdConnectSubsumerM6Spec`). -/
def step13FwdConnectSubsumerSpec : Spec [i64, i32] [] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.fuel = s.core.fuel → s'.core.inconsistent = s.core.inconsistent →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.red_refs = s.scratch.red_refs →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- Step-13 `full_eliminate_m6` threaded with `FullM6HdrMem` (`full_enter_dense_ex_fid`,
`full_update_classify_fid`). -/
def step13EliminateM6Spec : Spec [i64, .bool] [i64] := fun (h, _initial, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0 ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      FullM6HdrInv c F0 ext' s' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      s'.core.cur_level = 0 → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

end

/-! ## 5. Shared `_noExit` Bridges (`0` `@[expose]` on theorems) -/

public section

theorem f64uPure1Spec_noExit :
    ∀ xs m Q X, f64uPure1Spec xs m Q X → f64uPure1Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem f64uPure2Spec_noExit :
    ∀ xs m Q X, f64uPure2Spec xs m Q X → f64uPure2Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13PropagateM6Spec_noExit :
    ∀ xs m Q X, step13PropagateM6Spec xs m Q X →
      step13PropagateM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13FwdFlushLargeCoreSpec_noExit :
    ∀ xs m Q X, step13FwdFlushLargeCoreSpec xs m Q X →
      step13FwdFlushLargeCoreSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13K6InitSpec_noExit :
    ∀ xs m Q X, step13K6InitSpec xs m Q X → step13K6InitSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13K6AddClauseSpec_noExit :
    ∀ xs m Q X, step13K6AddClauseSpec xs m Q X →
      step13K6AddClauseSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13SweepConeSpec_noExit :
    ∀ xs m Q X, step13SweepConeSpec xs m Q X →
      step13SweepConeSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13SweepSimSpec_noExit :
    ∀ xs m Q X, step13SweepSimSpec xs m Q X →
      step13SweepSimSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13SweepUnitsSpec_noExit :
    ∀ xs m Q X, step13SweepUnitsSpec xs m Q X →
      step13SweepUnitsSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13SweepClassesSpec_noExit :
    ∀ xs m Q X, step13SweepClassesSpec xs m Q X →
      step13SweepClassesSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13SortBinWatchesSpec_noExit :
    ∀ xs m Q X, step13SortBinWatchesSpec xs m Q X →
      step13SortBinWatchesSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13DenseOccCntSpec_noExit :
    ∀ xs m Q X, step13DenseOccCntSpec xs m Q X →
      step13DenseOccCntSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13EnterDenseExM6Spec_noExit :
    ∀ xs m Q X, step13EnterDenseExM6Spec xs m Q X →
      step13EnterDenseExM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13EnterDenseM6Spec_noExit :
    ∀ xs m Q X, step13EnterDenseM6Spec xs m Q X →
      step13EnterDenseM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13DenseBinRoundtripSpec_noExit :
    ∀ xs m Q X, step13DenseBinRoundtripSpec xs m Q X →
      step13DenseBinRoundtripSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13WatchLargeClausesSpec_noExit :
    ∀ xs m Q X, step13WatchLargeClausesSpec xs m Q X →
      step13WatchLargeClausesSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13ElsArSpec_noExit :
    ∀ xs m Q X, step13ElsArSpec xs m Q X → step13ElsArSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13ElsLitSpec_noExit :
    ∀ xs m Q X, step13ElsLitSpec xs m Q X → step13ElsLitSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13DenseElsSpec_noExit :
    ∀ xs m Q X, step13DenseElsSpec xs m Q X →
      step13DenseElsSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13SweepVarSpec_noExit :
    ∀ xs m Q X, step13SweepVarSpec xs m Q X →
      step13SweepVarSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13CollectCandsSpec_noExit :
    ∀ xs m Q X, step13CollectCandsSpec xs m Q X →
      step13CollectCandsSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13HasCandsSpec_noExit :
    ∀ xs m Q X, step13HasCandsSpec xs m Q X →
      step13HasCandsSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13BveVarKeySpec_noExit :
    ∀ xs m Q X, step13BveVarKeySpec xs m Q X →
      step13BveVarKeySpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13FwdScanLitSpec_noExit :
    ∀ xs m Q X, step13FwdScanLitSpec xs m Q X →
      step13FwdScanLitSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13FwdConnectSubsumerSpec_noExit :
    ∀ xs m Q X, step13FwdConnectSubsumerSpec xs m Q X →
      step13FwdConnectSubsumerSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem step13EliminateM6Spec_noExit :
    ∀ xs m Q X, step13EliminateM6Spec xs m Q X →
      step13EliminateM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1
