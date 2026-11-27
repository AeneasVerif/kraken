/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullM7SearchProof0
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.Cells
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S3 Shared Specs & `u64`-in-`array32` Memory Bridges
(`FullFidelityStep13S3Spec`)

Shared contracts (`0` `import all`, `0` `@[expose]` on theorems, `XPost`-polymorphic, UNSAT-only)
for Step-13 Shard S3 (`32` functions = `10` Walk/Warmup + `22` Search/Restart/EMAs/Compact/Seed):
1. Frozen `S0` pure soft-float callee contracts (`f64uPure1Spec`, `f64uPure2Spec`).
2. `array (t := i32)` <-> `i64` load/store bridges (`S3WalkMemTactics`) for `u64 *tbl` over
   `scratch_buf` and `u64 *wk2` over `work_stk2`.
3. `WalkTblExpsOk` (`tbl[1080] ≤ 1080`) and Step-13 Walk/Warmup/Search/Restart/`--seed`
   `FullM6HdrMem`-threaded specs aligned with the unified Step-13 Option-A architecture.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S3

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM7Search
open Kraken.Bedrock2.Test

@[expose] public section

/-! ## 1. Shared Frozen `S0` Pure Soft-Float Callee Specs -/

/-- Pure memory-preserving spec for all 1-arg `f64u_*` soft-float helpers (`S0`). -/
def f64uPure1Spec : Spec [i64] [i64] :=
  fun _ m Q _ => ∀ r : BitVec 64, Q (r, ()) m

/-- Pure memory-preserving spec for all 2-arg `f64u_*` soft-float helpers (`S0`). -/
def f64uPure2Spec : Spec [i64, i64] [i64] :=
  fun _ m Q _ => ∀ r : BitVec 64, Q (r, ()) m

/-! ## 2. `u64`-in-`array32` Packing Helpers & Walk Table Invariant -/

/-- Little-endian `u64` assembled from two consecutive `u32` words `(lo, hi)`. -/
def u64Of32Pair (lo hi : BitVec 32) : BitVec 64 :=
  lo.setWidth 64 ||| (hi.setWidth 64 <<< 32)

/-- Writes a little-endian `u64` into indices `2 * i` and `2 * i + 1` of a `u32` list. -/
def setU64In32 (xs : List (BitVec 32)) (i : Nat) (v : BitVec 64) : List (BitVec 32) :=
  (xs.set (2 * i) (v.setWidth 32)).set (2 * i + 1) ((v >>> 32).setWidth 32)

/-- Table-length invariant established by `full_walk_cb_inv_m7` (`tbl[1080] ≤ 1080`) and
required by `full_walk_pick_m7` so `tbl[b]` stays strictly inside `scratch_buf[0..2160)`. -/
def WalkTblExpsOk (s : FullState) : Prop :=
  (u64Of32Pair (s.scratch.scratch_buf[2160]?.getD 0#32)
    (s.scratch.scratch_buf[2161]?.getD 0#32)).toNat ≤ 1080

/-- Preservation of the `u64` exponential-table prefix `scratch_buf[0 ..< 2200)`. -/
def WalkScrPrefixPres (s s' : FullState) : Prop :=
  ∀ j < 2200, s'.scratch.scratch_buf[j]? = s.scratch.scratch_buf[j]?

/-! ## 3. Step-13 Shard S3 Function & Cross-Shard Callee Specs -/

/-- Step-13 `full_walk_cb_inv_m7` contract: populates `tbl[0..1082]` in `scratch_buf` and
establishes `WalkTblExpsOk` whenever `r ≠ 0`. -/
def step13WalkCbInvSpec : Spec [i64, i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _ncl, _tot, ()) _ => h = c.hdr)
    (fun _ _ (r, ()) s s' => FullExtScratchPres s s' ∧ (r ≠ 0#64 → WalkTblExpsOk s'))

/-- Step-13 `full_walk_init_table_m7` contract (no-op; table filled in `cb_inv`). -/
def step13WalkInitTableSpec : Spec [i64, i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _iq, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullExtScratchPres s s')

/-- Step-13 `full_walk_break_m7` contract (read-only break count). -/
def step13WalkBreakSpec : Spec [i64, i32, i64] [i32] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _nl, _ncl, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => s' = s)

/-- Step-13 `full_walk_effort_m7` contract: read-only tick-effort calculation. -/
def step13WalkEffortSpec : Spec [i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _mf, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => s' = s)

/-- Step-13 `full_walk_build_occ_m7` contract: preserves `scratch_buf[0..2200)` (`WalkTblExpsOk`)
and returns `ulen ≤ ncl`. -/
def step13WalkBuildOccSpec : Spec [i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _ncl, ()) _ => h = c.hdr)
    (fun _ (_, ncl, ()) (r, ()) s s' =>
      FullExtScratchPres s s' ∧ WalkScrPrefixPres s s' ∧ r.toNat ≤ ncl.toNat)

/-- Step-13 `full_walk_pick_m7` contract: requires & preserves `WalkTblExpsOk`. -/
def step13WalkPickSpec : Spec [i64, i32, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _cl, _ncl, ()) s => h = c.hdr ∧ WalkTblExpsOk s)
    (fun _ _ _ s s' => FullExtScratchPres s s' ∧ WalkTblExpsOk s')

/-- Step-13 `full_walk_flip_m7` contract: preserves `scratch_buf[0..2200)` and bounds
`(r &&& 0xFFFFFFFF) ≤ ncl`. -/
def step13WalkFlipSpec : Spec [i64, i32, i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _fl, _ncl, _ul, ()) _ => h = c.hdr)
    (fun _ (_, _, ncl, _, ()) (r, ()) s s' =>
      FullExtScratchPres s s' ∧ WalkScrPrefixPres s s' ∧ (r &&& 0xFFFFFFFF#64).toNat ≤ ncl.toNat)

/-- Cross-shard `S1` contract for `full_dense_bin_roundtrip_fid` &
`full_watch_large_clauses_fid` called at the start of `full_walk_m7`. -/
def step13WatchRoundtripSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullSparseInv c F0 s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.fuel = s.core.fuel → s'.core.probing = s.core.probing →
      FullExtScratchPres s s' → (FullMem c s' ⋆ R) m' → Q () m'

/-- Step-13 `full_walk_m7` contract (`FullSparseInv`-preserving, allowing binary watch roundtrip
and large-clause watch reconnection). -/
def step13WalkM7Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullSparseInv c F0 s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.probing = s.core.probing →
      FullExtScratchPres s s' → (FullMem c s' ⋆ R) m' → Q () m'

/-- Cross-shard `S2` `FullM6HdrMem`-threaded contract for `full_propagate_beyond_m7` called by
`full_warmup_m7`. -/
def step13PropBeyondM6Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      FullM6HdrInv c F0 ext' s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.probing = s.core.probing → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r ≠ 2#64 → s.core.propagated < s.core.trail_end → s'.core.fuel.toNat < s.core.fuel.toNat) →
      FullExtScratchPres s s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Step-13 `FullM6HdrMem`-threaded contract for `full_warmup_m7` (and `full_walk` /
`full_walk_warmup_m7`). -/
def step13WarmupM6Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ ext' s' m',
      FullM6HdrInv c F0 ext' s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (s.core.probing = 0#64 → s'.core.probing = 0#64) →
      FullExtScratchPres s s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

/-- Step-13 `FullM6HdrMem`-threaded contract for `full_rephase`. -/
def step13RephaseM6Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ ext' s' m',
      FullM6HdrInv c F0 ext' s' → FullArenaPermEq s.core s'.core →
      (s.scratch.stable ≠ 0#64 → s'.core.cur_level = 0) →
      s'.core.cur_level ≤ s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      FullExtScratchPres s s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

/-- Step-13 `full_m7_state_init` contract (`init_exp = 0x3FF0000000000000ULL`): establishes
`M7StateInitOk`, `M7GuPrefixPres`, and `LengthsOk` mutating only `glue_used`. -/
def step13M7StateInitSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ gu' m',
      let s' : FullState := { s with scratch := { s.scratch with glue_used := gu' } }
      s'.LengthsOk c → M7StateInitOk gu' → M7GuPrefixPres s s' →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- Step-13 `full_randec_var_lvl_fid(h, max_lvl)` contract: matches `m7RandecVarSpec` for any
`max_lvl`. -/
def step13RandecVarLvlSpec : Spec [i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _ml, ()) _ => h = c.hdr)
    (fun _ _ (r, ()) s s' =>
      FullProbeScratchPres s s' ∧ M7GuPrefixPres s s' ∧
      (r = 0xFFFFFFFFFFFFFFFF#64 ∨
        (r.toNat < s.core.cur_vars ∧
          (s.core.flags[r.toNat]?.getD 0#32 &&& 1#32) ≠ 0#32 ∧
          s.core.vals[2 * r.toNat]?.getD 0#8 = 0#8)))

/-- Step-13 `full_ema_swap_m7` contract (`init_exp = 0x3FF0000000000000ULL`). -/
def step13EmaSwapSpec : Spec [i64, i64, i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _om, _nm, ()) _ => h = c.hdr)
    (fun _ _ _ s s' =>
      FullProbeScratchPres s s' ∧ M7GuPrefixPres s s' ∧ M7StateInitOk s'.scratch.glue_used)

/-- Step-13 `FullM6HdrMem`-threaded contract for `full_switch_mode_m7` (reads/writes `m6_wm4`
and `M6HdrExt` `dr_state`/`dr_prev`). -/
def step13SwitchModeM6Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ ext' s' m',
      s'.core = s.core → s'.LengthsOk c → FullProbeScratchPres s s' → M6HdrExtOk ext' →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

/-- Cross-shard `S2` `FullM6HdrMem`-threaded BCP contract for `full_propagate` called by
`full_search_m6` (Option A). -/
def step13BcpM6Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
    (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInvW c F0 F_cur ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      FullM6HdrInvW c F0 F_cur ext' s' → FullTrailExt s.core s'.core →
      FullArenaPermEq s.core s'.core → s'.core.cur_level = s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 1#64 → s'.core.fuel.toNat < s.core.fuel.toNat ∧ s'.core.oom = 0#64 ∧
        FullConflictOkW F_cur s') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Cross-shard `FullM6HdrMem`-threaded contract for `full_lucky_late_m7` called by
`full_search_m6` (Option A). -/
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

/-- Cross-shard `S5` `FullM6HdrMem`-threaded contract for `full_parse_body` called by
`kissat_solve_bytes_seeded` (Option A lifting of `Full.fullParseBodySpec`). -/
def step13ParseBodyM6Spec : Spec [i64, i64] [i64] := fun (h, cend, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (cnf_ptr : BitVec 64)
    (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
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

/-- Step-13 `full_init_fresh_var` contract (inlined to avoid `Step7..12` back-import per `K-02`;
definitionally matches `FullFidelityStep7.step7InitFreshVarSpec`). -/
def step13InitFreshVarSpec : Spec [i64, i32] [] := fun (h, fv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ fv.toNat < s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ vals' mrk' flags' lvl' rsns' wvec' unass' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', mrk := mrk', flags := flags', lvl := lvl',
                                rsns := rsns', wvec := wvec', unassigned := unass' }
          scratch := sc' }
      s'.LengthsOk c → FullExtScratchPres s s' →
      sc'.scratch_buf = s.scratch.scratch_buf →
      sc'.wsort = s.scratch.wsort →
      sc'.tarjan_mark = s.scratch.tarjan_mark →
      sc'.tarjan_reach = s.scratch.tarjan_reach →
      sc'.sim_sig = s.scratch.sim_sig →
      sc'.res_sz = s.scratch.res_sz →
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

/-- Top-level 6-arg UNSAT-soundness contract for `kissat_solve_bytes_seeded` (arbitrary `seed`,
exact 6-arg mirror of `FullM7Fidelity.m7FidSolveBytesSpec`). -/
def step13SolveBytesSeededSpec : Spec [i64, i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, _seed, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (∀ mv nc i0,
          cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
          fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen →
          i0 ≤ cnfBytes.length →
          parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
          r = 20#64) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
        Q (r, ()) m'

/-- Top-level 5-arg UNSAT-soundness contract for `kissat_solve_bytes{_m6}` (definitionally
identical to `FullM7Fidelity.m7FidSolveBytesSpec`, inlined to avoid importing M7 assembly). -/
def step13SolveBytesSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (∀ mv nc i0,
          cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
          fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen →
          i0 ≤ cnfBytes.length →
          parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
          r = 20#64) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
        Q (r, ()) m'

end

/-! ## 4. `noExit` Bridges & `array (t := i32)` <-> `i64` Load/Store Lemmas -/

public section

theorem f64uPure1Spec_noExit {a m Q X X'} (h : f64uPure1Spec a m Q X) :
    f64uPure1Spec a m Q X' := h

theorem f64uPure2Spec_noExit {a m Q X X'} (h : f64uPure2Spec a m Q X) :
    f64uPure2Spec a m Q X' := h

theorem step13WalkCbInvSpec_noExit {a m Q X X'} (h : step13WalkCbInvSpec a m Q X) :
    step13WalkCbInvSpec a m Q X' := SafetySlice.spec_noExit h

theorem step13WalkInitTableSpec_noExit {a m Q X X'} (h : step13WalkInitTableSpec a m Q X) :
    step13WalkInitTableSpec a m Q X' := SafetySlice.spec_noExit h

theorem step13WalkBreakSpec_noExit {a m Q X X'} (h : step13WalkBreakSpec a m Q X) :
    step13WalkBreakSpec a m Q X' := SafetySlice.spec_noExit h

theorem step13WalkEffortSpec_noExit {a m Q X X'} (h : step13WalkEffortSpec a m Q X) :
    step13WalkEffortSpec a m Q X' := SafetySlice.spec_noExit h

theorem step13WalkBuildOccSpec_noExit {a m Q X X'} (h : step13WalkBuildOccSpec a m Q X) :
    step13WalkBuildOccSpec a m Q X' := SafetySlice.spec_noExit h

theorem step13WalkPickSpec_noExit {a m Q X X'} (h : step13WalkPickSpec a m Q X) :
    step13WalkPickSpec a m Q X' := SafetySlice.spec_noExit h

theorem step13WalkFlipSpec_noExit {a m Q X X'} (h : step13WalkFlipSpec a m Q X) :
    step13WalkFlipSpec a m Q X' := SafetySlice.spec_noExit h

theorem step13WatchRoundtripSpec_noExit {a m Q X X'} (h : step13WatchRoundtripSpec a m Q X) :
    step13WatchRoundtripSpec a m Q X' := by rcases a with ⟨_, ⟨⟩⟩; exact h

theorem step13WalkM7Spec_noExit {a m Q X X'} (h : step13WalkM7Spec a m Q X) :
    step13WalkM7Spec a m Q X' := by rcases a with ⟨_, ⟨⟩⟩; exact h

theorem step13PropBeyondM6Spec_noExit {a m Q X X'} (h : step13PropBeyondM6Spec a m Q X) :
    step13PropBeyondM6Spec a m Q X' := by rcases a with ⟨_, ⟨⟩⟩; exact h

theorem step13WarmupM6Spec_noExit {a m Q X X'} (h : step13WarmupM6Spec a m Q X) :
    step13WarmupM6Spec a m Q X' := by rcases a with ⟨_, ⟨⟩⟩; exact h

theorem step13RephaseM6Spec_noExit {a m Q X X'} (h : step13RephaseM6Spec a m Q X) :
    step13RephaseM6Spec a m Q X' := by rcases a with ⟨_, ⟨⟩⟩; exact h

theorem step13M7StateInitSpec_noExit {a m Q X X'} (h : step13M7StateInitSpec a m Q X) :
    step13M7StateInitSpec a m Q X' := by rcases a with ⟨_, ⟨⟩⟩; exact h

theorem step13RandecVarLvlSpec_noExit {a m Q X X'} (h : step13RandecVarLvlSpec a m Q X) :
    step13RandecVarLvlSpec a m Q X' := SafetySlice.spec_noExit h

theorem step13EmaSwapSpec_noExit {a m Q X X'} (h : step13EmaSwapSpec a m Q X) :
    step13EmaSwapSpec a m Q X' := SafetySlice.spec_noExit h

theorem step13SwitchModeM6Spec_noExit {a m Q X X'} (h : step13SwitchModeM6Spec a m Q X) :
    step13SwitchModeM6Spec a m Q X' := by rcases a with ⟨_, ⟨⟩⟩; exact h

theorem step13BcpM6Spec_noExit {a m Q X X'} (h : step13BcpM6Spec a m Q X) :
    step13BcpM6Spec a m Q X' := by rcases a with ⟨_, ⟨⟩⟩; exact h

theorem step13LuckyLateM6Spec_noExit {a m Q X X'} (h : step13LuckyLateM6Spec a m Q X) :
    step13LuckyLateM6Spec a m Q X' := by rcases a with ⟨_, ⟨⟩⟩; exact h

theorem step13ParseBodyM6Spec_noExit {a m Q X X'} (h : step13ParseBodyM6Spec a m Q X) :
    step13ParseBodyM6Spec a m Q X' := by rcases a with ⟨_, _, ⟨⟩⟩; exact h

theorem step13InitFreshVarSpec_noExit {a m Q X X'}
    (h : step13InitFreshVarSpec a m Q X) :
    step13InitFreshVarSpec a m Q X' := by
  rcases a with ⟨_, _, ⟨⟩⟩; exact h

theorem step13SolveBytesSeededSpec_noExit {a m Q X X'}
    (h : step13SolveBytesSeededSpec a m Q X) :
    step13SolveBytesSeededSpec a m Q X' := by
  rcases a with ⟨_, _, _, _, _, _, ⟨⟩⟩; exact h

theorem step13SolveBytesSpec_noExit {a m Q X X'}
    (h : step13SolveBytesSpec a m Q X) :
    step13SolveBytesSpec a m Q X' := by
  rcases a with ⟨_, _, _, _, _, ⟨⟩⟩; exact h

/-! ### `setU64In32` & `WalkTblExpsOk` Lemmas -/

theorem setU64In32_length (xs : List (BitVec 32)) (i : Nat) (v : BitVec 64) :
    (setU64In32 xs i v).length = xs.length := by
  simp [setU64In32]

theorem u64Of32Pair_split (v : BitVec 64) :
    u64Of32Pair (v.setWidth 32) ((v >>> 32).setWidth 32) = v := by
  unfold u64Of32Pair
  apply BitVec.eq_of_getElem_eq; intro k hk
  simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth]
  by_cases h32 : k < 32
  · simp [h32, BitVec.getLsbD_eq_getElem hk]
  · have hk1 : k - 32 < 32 := by omega
    have hk2 : 32 + (k - 32) = k := by omega
    simp [h32, hk1, hk2, BitVec.getLsbD_eq_getElem hk]

theorem setU64In32_get_ne {xs : List (BitVec 32)} {i j : Nat} {v : BitVec 64}
    (h1 : j ≠ 2 * i) (h2 : j ≠ 2 * i + 1) :
    (setU64In32 xs i v)[j]? = xs[j]? := by
  unfold setU64In32
  rw [List.getElem?_set_ne (Ne.symm h2), List.getElem?_set_ne (Ne.symm h1)]

theorem walkTblExpsOk_of_setU64_1080 {s : FullState} {v : BitVec 64}
    (hlen : 2162 ≤ s.scratch.scratch_buf.length) (hv : v.toNat ≤ 1080) :
    WalkTblExpsOk { s with scratch := { s.scratch with
      scratch_buf := setU64In32 s.scratch.scratch_buf 1080 v } } := by
  unfold WalkTblExpsOk setU64In32
  dsimp only
  have h1 : (s.scratch.scratch_buf.set 2160 (v.setWidth 32)).length =
      s.scratch.scratch_buf.length := List.length_set
  rw [List.getElem?_set_ne (by omega : 2161 ≠ 2160),
    List.getElem?_set_self (by omega),
    List.getElem?_set_self (by rw [h1]; omega)]
  simp only [Option.getD_some, u64Of32Pair_split]
  exact hv

theorem walkTblExpsOk_of_setU64_ne {s : FullState} {i : Nat} {v : BitVec 64}
    (hne : i ≠ 1080) (hok : WalkTblExpsOk s) :
    WalkTblExpsOk { s with scratch := { s.scratch with
      scratch_buf := setU64In32 s.scratch.scratch_buf i v } } := by
  unfold WalkTblExpsOk at hok ⊢
  dsimp only
  rw [setU64In32_get_ne (by omega) (by omega), setU64In32_get_ne (by omega) (by omega)]
  exact hok

theorem walkTblExpsOk_of_prefixPres {s s' : FullState}
    (h : WalkScrPrefixPres s s') (hok : WalkTblExpsOk s) : WalkTblExpsOk s' := by
  unfold WalkTblExpsOk at hok ⊢
  rw [h 2160 (by decide), h 2161 (by decide)]
  exact hok

theorem walkScrPrefixPres_refl (s : FullState) : WalkScrPrefixPres s s :=
  fun _ _ => rfl

theorem walkScrPrefixPres_trans {s1 s2 s3 : FullState}
    (h1 : WalkScrPrefixPres s1 s2) (h2 : WalkScrPrefixPres s2 s3) :
    WalkScrPrefixPres s1 s3 :=
  fun j hj => (h2 j hj).trans (h1 j hj)

theorem walkScrPrefixPres_set_ge {s : FullState} {idx : Nat} {v : BitVec 32} (hge : 2200 ≤ idx) :
    WalkScrPrefixPres s { s with scratch := { s.scratch with
      scratch_buf := s.scratch.scratch_buf.set idx v } } := by
  intro j hj
  dsimp only
  rw [List.getElem?_set_ne (by omega)]

/-! ### `cell (t := i32)` Pair <-> `cell64` Bridge (`0` `import all`) -/

private theorem toBytes_split_4_4 (v : BitVec 64) :
    Int.toBytes 8 (v.toNat : Int) =
      Int.toBytes 4 ((v.setWidth 32).toNat : Int) ++
      Int.toBytes 4 (((v >>> 32).setWidth 32).toNat : Int) := by
  have hlo : (v.setWidth 32).toNat = v.toNat % 2 ^ 32 := by simp [BitVec.toNat_setWidth]
  have hhi : ((v >>> 32).setWidth 32).toNat = v.toNat / 2 ^ 32 := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have hv := v.isLt
    exact Nat.mod_eq_of_lt (by omega)
  rw [hlo, hhi]
  have hstep : ∀ (x : Nat),
      Int.toBytes 8 (x : Int) = Int.toBytes 4 ((x % 2 ^ 32 : Nat) : Int) ++
        Int.toBytes 4 ((x / 2 ^ 32 : Nat) : Int) := by
    intro x
    simp only [Int.toBytes, Int.take, List.cons_append, List.nil_append, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · congr 1; omega
  exact hstep v.toNat

private theorem toBytes_bv_toInt_eq_toNat {n b : Nat} (hn : n = 8 * b) (v : BitVec n) :
    Int.toBytes b v.toInt = Int.toBytes b (v.toNat : Int) := by
  rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := (v.toNat : Int))]
  congr 1
  simp only [Int.take, ← hn]
  have hmod : v.toInt % (2 ^ n : Int) = (v.toNat : Int) := by
    rw [BitVec.toInt_eq_msb_cond]
    have ha : 0 ≤ (v.toNat : Int) ∧ (v.toNat : Int) < (2 ^ n : Int) :=
      ⟨Int.natCast_nonneg _, by exact_mod_cast v.isLt⟩
    cases v.msb
    · simp [Int.emod_eq_of_lt ha.1 ha.2]
    · simp only [↓reduceIte, Int.natCast_pow, Int.cast_ofNat_Int]
      rw [Int.sub_emod_right, Int.emod_eq_of_lt ha.1 ha.2]
  rw [hmod, Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast v.isLt)]

private theorem cell_i32_eq_bytes (a : BitVec 64) (v : BitVec 32) :
    cell (t := i32) a v = Eq ((Int.toBytes 4 (v.toNat : Int)).At a) := by
  change Eq ((Int.toBytes 4 ((v.setWidth 32).toInt)).At a) = _
  rw [BitVec.setWidth_eq v, toBytes_bv_toInt_eq_toNat (n := 32) (b := 4) rfl v]

private theorem cell64_eq_bytes (a v : BitVec 64) :
    cell64 a v = Eq ((Int.toBytes 8 (v.toNat : Int)).At a) := by
  change Eq ((Int.toBytes 8 ((v.setWidth 64).toInt)).At a) = _
  rw [BitVec.setWidth_eq v, toBytes_bv_toInt_eq_toNat (n := 64) (b := 8) rfl v]

theorem cell_i32_pair_eq_cell64 (a : BitVec 64) (lo hi : BitVec 32) :
    (cell (t := i32) a lo ⋆ cell (t := i32) (a + 4) hi) =
      cell64 a (u64Of32Pair lo hi) := by
  let v := u64Of32Pair lo hi
  have hlo : v.setWidth 32 = lo := by
    apply BitVec.eq_of_getElem_eq; intro k hk
    simp [v, u64Of32Pair]
  have hhi : (v >>> 32).setWidth 32 = hi := by
    apply BitVec.eq_of_getElem_eq; intro k hk
    simp [v, u64Of32Pair, hk, show 32 + k < 64 by omega]
  rw [cell_i32_eq_bytes, cell_i32_eq_bytes, cell64_eq_bytes, toBytes_split_4_4 v, hlo, hhi]
  have ha := Mem.At_append_sep (Int.toBytes 4 (lo.toNat : Int))
    (Int.toBytes 4 (hi.toNat : Int)) a (by simp [Int.toBytes_length])
  simpa [Int.toBytes_length] using ha.symm

theorem array32_focus_pair (a : BitVec 64) (xs : List (BitVec 32)) {i : Nat}
    (hi : 2 * i + 1 < xs.length) :
    array (t := i32) a xs =
      (cell64 (a + BitVec.ofNat 64 (8 * i))
          (u64Of32Pair (xs[2 * i]'(by omega)) (xs[2 * i + 1]'hi)) ⋆
        (array (t := i32) a (xs.take (2 * i)) ⋆
          array (t := i32) (a + BitVec.ofNat 64 (8 * i) + 8) (xs.drop (2 * i + 2)))) := by
  have htake : xs = xs.take (2 * i) ++
      (xs[2 * i]'(by omega) :: xs[2 * i + 1]'hi :: xs.drop (2 * i + 2)) := by
    have h1 := List.take_append_drop (2 * i) xs
    have h2 : xs.drop (2 * i) = xs[2 * i]'(by omega) :: xs.drop (2 * i + 1) :=
      List.drop_eq_getElem_cons (by omega)
    have h3 : xs.drop (2 * i + 1) = xs[2 * i + 1]'hi :: xs.drop (2 * i + 2) :=
      List.drop_eq_getElem_cons hi
    calc xs = xs.take (2 * i) ++ xs.drop (2 * i) := h1.symm
      _ = xs.take (2 * i) ++ (xs[2 * i]'(by omega) :: xs[2 * i + 1]'hi :: xs.drop (2 * i + 2)) := by
        rw [h2, h3]
  conv => lhs; rw [htake]
  rw [array_append, List.length_take_of_le (by omega),
    array_cons, array_cons, show (i32 : Ty).bytes = 4 from rfl]
  have h8 : BitVec.ofNat 64 (4 * (2 * i)) = BitVec.ofNat 64 (8 * i) := by
    congr 1; omega
  have h8p : a + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 4 + BitVec.ofNat 64 4 =
      a + BitVec.ofNat 64 (8 * i) + 8 := by bv_omega
  rw [h8, h8p, ← sep_assoc (cell (t := i32) _ _),
    show (4#64 : BitVec 64) = 4 from rfl,
    cell_i32_pair_eq_cell64 (a + BitVec.ofNat 64 (8 * i))]
  ac_rfl

theorem loadVal_array32_u64 {a : BitVec 64} {xs : List (BitVec 32)} {i : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 2 * i + 1 < xs.length)
    (h : (array (t := i32) a xs ⋆ R) m) :
    loadVal m i64 (a + BitVec.ofNat 64 (8 * i)) =
      some (u64Of32Pair (xs[2 * i]'(by omega)) (xs[2 * i + 1]'hi)) := by
  rw [array32_focus_pair a xs hi, sep_assoc] at h
  exact loadVal_cell64 h

theorem store_array32_u64 {a : BitVec 64} {xs : List (BitVec 32)} {i : Nat} (v : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 2 * i + 1 < xs.length)
    (h : (array (t := i32) a xs ⋆ R) m) :
    storeOk m i64 (a + BitVec.ofNat 64 (8 * i)) ∧
      (array (t := i32) a (setU64In32 xs i v) ⋆ R)
        (storeMem m i64 (a + BitVec.ofNat 64 (8 * i)) v) := by
  rw [array32_focus_pair a xs hi, sep_assoc] at h
  obtain ⟨hok, hst⟩ := store_cell64 v h
  refine ⟨hok, ?_⟩
  have hlen : (setU64In32 xs i v).length = xs.length := setU64In32_length xs i v
  have hi' : 2 * i + 1 < (setU64In32 xs i v).length := by omega
  rw [array32_focus_pair a (setU64In32 xs i v) hi', sep_assoc]
  have htake : (setU64In32 xs i v).take (2 * i) = xs.take (2 * i) := by
    unfold setU64In32
    rw [List.take_set_of_le (by omega), List.take_set_of_le (by omega)]
  have hdrop : (setU64In32 xs i v).drop (2 * i + 2) = xs.drop (2 * i + 2) := by
    unfold setU64In32
    rw [List.drop_set_of_lt (by omega), List.drop_set_of_lt (by omega)]
  have hg0 : (setU64In32 xs i v)[2 * i]'(by omega) = v.setWidth 32 := by
    simp [setU64In32, List.getElem_set_ne (by omega : 2 * i + 1 ≠ 2 * i)]
  have hg1 : (setU64In32 xs i v)[2 * i + 1]'hi' = (v >>> 32).setWidth 32 := by
    simp [setU64In32]
  rw [htake, hdrop, hg0, hg1, u64Of32Pair_split]
  exact hst

/-! ### Strictly Scoped `FullMem` `u64`-View Accessors (`S3WalkMemTactics`) -/

namespace S3WalkMemTactics

private theorem m8_eq (a i : BitVec 64) : a + i * 8 = a + BitVec.ofNat 64 (8 * i.toNat) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_mul_ofNat]

private theorem ufM {c : FullCfg} {s s' : FullState} {G G' B B' R : Mem 64 → Prop}
    {m' : Mem 64} (_hs : FullMem c s = (G ⋆ B)) (hs' : FullMem c s' = (G' ⋆ B'))
    (hb : B' = B) (h : ((G' ⋆ B) ⋆ R) m') : (FullMem c s' ⋆ R) m' := by rw [hs', hb]; exact h

@[scoped c0_load] theorem load_full_scratch_buf_u64 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hi : 2 * i + 1 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pScratchBuf + BitVec.ofNat 64 (8 * i)) =
      some (u64Of32Pair (s.scratch.scratch_buf[2 * i]'(by omega))
        (s.scratch.scratch_buf[2 * i + 1]'hi)) := by
  have h1 := hm; rw [fullMem_eq_scrDyn] at h1; unfold FullScrDynArrs at h1
  exact loadVal_array32_u64 hi (by ecancel)

@[scoped c0_load] theorem c0_load_full_scratch_buf_u64 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : 2 * i.toNat + 1 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pScratchBuf + i * 8) =
      some (u64Of32Pair (s.scratch.scratch_buf[2 * i.toNat]'(by omega))
        (s.scratch.scratch_buf[2 * i.toNat + 1]'hi)) := by
  rw [m8_eq]; exact load_full_scratch_buf_u64 hi hm

@[scoped c0_load] theorem c0_load_full_scratch_buf_u64_imm {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {k : BitVec 64}
    (hmod : k.toNat % 8 = 0) (hi : 2 * (k.toNat / 8) + 1 < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pScratchBuf + k) =
      some (u64Of32Pair (s.scratch.scratch_buf[2 * (k.toNat / 8)]'(by omega))
        (s.scratch.scratch_buf[2 * (k.toNat / 8) + 1]'hi)) := by
  have hk : k = BitVec.ofNat 64 (8 * (k.toNat / 8)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := k.isLt; omega)]; omega
  conv => lhs; rw [hk]
  exact load_full_scratch_buf_u64 hi hm

@[scoped c0_store] theorem store_full_scratch_buf_u64 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : Nat} (v : BitVec 64)
    (hi : 2 * i + 1 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pScratchBuf + BitVec.ofNat 64 (8 * i)) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := setU64In32 s.scratch.scratch_buf i v } } ⋆ R)
        (storeMem m i64 (c.pScratchBuf + BitVec.ofNat 64 (8 * i)) v) := by
  have h1 := hm; rw [fullMem_eq_scrDyn] at h1; unfold FullScrDynArrs at h1
  obtain ⟨hok, hst⟩ := store_array32_u64 v hi (by ecancel)
  exact ⟨hok, ufM (fullMem_eq_scrDyn c s) (fullMem_eq_scrDyn c _) rfl
    (by unfold FullScrDynArrs; dsimp only; ecancel)⟩

@[scoped c0_store] theorem c0_store_full_scratch_buf_u64 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 64)
    (hi : 2 * i.toNat + 1 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pScratchBuf + i * 8) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := setU64In32 s.scratch.scratch_buf i.toNat v } } ⋆ R)
        (storeMem m i64 (c.pScratchBuf + i * 8) v) := by
  rw [m8_eq]; exact store_full_scratch_buf_u64 v hi hm

@[scoped c0_store] theorem c0_store_full_scratch_buf_u64_imm {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {k : BitVec 64} (v : BitVec 64)
    (hmod : k.toNat % 8 = 0) (hi : 2 * (k.toNat / 8) + 1 < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pScratchBuf + k) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := setU64In32 s.scratch.scratch_buf (k.toNat / 8) v } } ⋆ R)
        (storeMem m i64 (c.pScratchBuf + k) v) := by
  have hk : k = BitVec.ofNat 64 (8 * (k.toNat / 8)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := k.isLt; omega)]; omega
  have hres := store_full_scratch_buf_u64 (c := c) (s := s) (R := R) (m := m)
    (i := k.toNat / 8) v hi hm
  rwa [← hk] at hres

@[scoped c0_load] theorem load_full_work_stk2_u64 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hi : 2 * i + 1 < s.scratch.work_stk2.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pWorkStk2 + BitVec.ofNat 64 (8 * i)) =
      some (u64Of32Pair (s.scratch.work_stk2[2 * i]'(by omega))
        (s.scratch.work_stk2[2 * i + 1]'hi)) := by
  have h1 := hm; rw [fullMem_eq_scrWks] at h1; unfold FullScrWksArrs at h1
  exact loadVal_array32_u64 hi (by ecancel)

@[scoped c0_load] theorem c0_load_full_work_stk2_u64 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : 2 * i.toNat + 1 < s.scratch.work_stk2.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pWorkStk2 + i * 8) =
      some (u64Of32Pair (s.scratch.work_stk2[2 * i.toNat]'(by omega))
        (s.scratch.work_stk2[2 * i.toNat + 1]'hi)) := by
  rw [m8_eq]; exact load_full_work_stk2_u64 hi hm

@[scoped c0_store] theorem store_full_work_stk2_u64 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : Nat} (v : BitVec 64)
    (hi : 2 * i + 1 < s.scratch.work_stk2.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pWorkStk2 + BitVec.ofNat 64 (8 * i)) ∧
      (FullMem c { s with scratch := { s.scratch with
        work_stk2 := setU64In32 s.scratch.work_stk2 i v } } ⋆ R)
        (storeMem m i64 (c.pWorkStk2 + BitVec.ofNat 64 (8 * i)) v) := by
  have h1 := hm; rw [fullMem_eq_scrWks] at h1; unfold FullScrWksArrs at h1
  obtain ⟨hok, hst⟩ := store_array32_u64 v hi (by ecancel)
  exact ⟨hok, ufM (fullMem_eq_scrWks c s) (fullMem_eq_scrWks c _) rfl
    (by unfold FullScrWksArrs; dsimp only; ecancel)⟩

@[scoped c0_store] theorem c0_store_full_work_stk2_u64 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 64)
    (hi : 2 * i.toNat + 1 < s.scratch.work_stk2.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pWorkStk2 + i * 8) ∧
      (FullMem c { s with scratch := { s.scratch with
        work_stk2 := setU64In32 s.scratch.work_stk2 i.toNat v } } ⋆ R)
        (storeMem m i64 (c.pWorkStk2 + i * 8) v) := by
  rw [m8_eq]; exact store_full_work_stk2_u64 v hi hm

end S3WalkMemTactics

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S3
