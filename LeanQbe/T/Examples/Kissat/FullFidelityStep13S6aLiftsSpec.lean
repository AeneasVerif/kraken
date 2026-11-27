/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullSpec1
public import LeanQbe.T.Examples.Kissat.FullSpec2
public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1
public import LeanQbe.T.Examples.Kissat.FullM6CompactFlushProof1
public import LeanQbe.T.Examples.Kissat.FullM4CompactLemmas
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof2a
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof2b
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof3a
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof0
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof1
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof2
public import LeanQbe.T.Examples.Kissat.FullM7V2RobustProof0
public import LeanQbe.T.Examples.Kissat.FullM7SearchProof0
public import LeanQbe.T.Examples.Kissat.FullSubstLemmas1
public import LeanQbe.T.Examples.Kissat.FullFidelityTumbleSpec
public import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas1
public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof6
public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof0
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec
public import LeanQbe.T.Examples.Kissat.FullM4SweepSpec
public import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas1
public import LeanQbe.T.Examples.Kissat.FullM6ProofUtil

/-!
# Kissat Fidelity Step 13 Shard `S6a` — Lifted Spec Contracts & `deadSpec` (`S6a`)

Parametric Step-13 `Spec` contracts (`0` cross-shard `S0..S5` imports, `0` `import all`,
`0` `@[expose]` on theorems/lemmas, `<= 100` cols, `< 1,500` LOC) for Wave-1.5 unchanged
Step-12 caller lifts (`FullM6HdrMem` Option A + `S1` `K6HwmClean`/`WatchStackLayout` + `S4`/`S5`
relaxed `flags`/`min_clr`/`arena`/`ws1` contracts), plus reusable `deadSpec` / `deadSpec_wp` for
the unreachable legacy Step-12 functions.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil Kraken.Bedrock2.Test
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6CompactFlush
open LeanQbe.T.Examples.Kissat.FullM4Compact
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM7V2Robust
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullFidelityTumble
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep

@[expose] public section

/-! ## 1. Reusable `deadSpec` for Unreachable Legacy Functions -/

/-- Unsatisfiable precondition contract for unreachable dead functions (`0` runtime calls). -/
def deadSpec {as bs : List Ty} : Spec as bs :=
  fun _ _ _ _ => False

/-! ## 2. Step-13 Callee `Spec` Mirrors (`S1` / `S2` / `S3` / `S4` / `S5` Aligned) -/

/-- Mirror of `S2` `step13PropagateIgnoreM6Spec` (`full_propagate_ignore` /
`full_propagate_ignore_hot`). -/
def step13PropagateIgnoreM6Spec : Spec [i64, i64] [i64] :=
  fun (h, ignore_ref, ()) m Q _ =>
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
        sc'.red_refs = s.scratch.red_refs →
        sc'.delayed_len = s.scratch.delayed_len →
        (s.core.probing = 0#64 → sc' = { s.scratch with
          search_ticks := sc'.search_ticks, wsort := sc'.wsort,
          phases := sc'.phases, delayed := sc'.delayed }) →
        (c.delayed_cap = 0 → sc'.delayed = s.scratch.delayed) →
        fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
        (r = 0#64 → prop' = te' ∧ ctype' = s.core.confl_type ∧
          (s.core.oom = 0#64 → oom' = 0#64) ∧
          (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
        (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s' ∧
          (ctype' = 2#64 → cref' ≠ ignore_ref)) →
        (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
        (s.core.propagated = s.core.trail_end → r = 0#64 ∧ ext' = ext ∧ s' = s) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Mirror of `S2` `step13BcpM6Spec` (`full_bcp_hot` / `full_propagate`). -/
def step13BcpM6Spec : Spec [i64] [i64] :=
  fun (h, ()) m Q _ =>
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

/-- Mirror of `S3` `step13BcpM6Spec` (`FullM6HdrInvW` view consumed by `S3` search). -/
def step13BcpM6S3Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
    (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInvW c F0 F_cur ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      FullM6HdrInvW c F0 F_cur ext' s' → FullTrailExt s.core s'.core →
      FullArenaPermEq s.core s'.core → s'.core.cur_level = s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.scratch.red_refs = s.scratch.red_refs →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 1#64 → s'.core.fuel.toNat < s.core.fuel.toNat ∧ s'.core.oom = 0#64 ∧
        FullConflictOkW F_cur s') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Mirror of `S1` `step13PropagateM6Spec` (explicit `ticks, wsort, phases, delayed` slice). -/
def step13BcpM6S1Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    FullWitnessInv c F0 F_cur s.core ∧ s.core.dense_mode = 0#64 ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' ext' m',
      let s' : FullState :=
        { s with
          core :=
            { s.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
              unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
              wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
              confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
          scratch :=
            { s.scratch with
              search_ticks := ticks', wsort := wsort', phases := phases', delayed := delayed' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      (c.delayed_cap = 0 → delayed' = s.scratch.delayed) →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s') →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Mirror of `S3` `step13WalkM7Spec` (`full_walk_m7`). -/
def step13WalkM7Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullSparseInv c F0 s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.probing = s.core.probing →
      FullExtScratchPres s s' → (FullMem c s' ⋆ R) m' → Q () m'

/-- Mirror of `S3` `step13WarmupM6Spec` (`full_warmup_m7` / `full_walk`). -/
def step13WarmupM6Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ ext' s' m',
      FullM6HdrInv c F0 ext' s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (s.core.probing = 0#64 → s'.core.probing = 0#64) →
      FullExtScratchPres s s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

/-- Mirror of `S4` `step13LuckyScanM6Spec` (`full_lucky_scan`, Option A `FullM6HdrMem`). -/
def step13LuckyScanM6Spec : Spec [i64, .bool, .bool] [i64] := fun (h, _pos, _fwd, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
    FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      M6HdrExtOk ext' → s'.LengthsOk c →
      (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Mirror of `S3` `step13LuckyLateM6Spec` (`full_lucky_late_m7`). -/
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

/-- Mirror of `S3` `step13ParseBodyM6Spec` (`full_parse_body_m6` / `full_parse_body`). -/
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
      (UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc →
        r = 20#64) →
      (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Mirror of `S5` `step13AddClauseSpec` (`full_add_clause`, `flags'` on `len = 2`). -/
def step13AddClauseSpec : Spec [i64, i32, i32, .bool] [i64] :=
  fun (h, len, _glue, _red, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      s.core.dense_mode = 0#64 ∧ len.toNat ≤ c.max_vars ∧
      (2 ≤ len.toNat →
        (∀ l ∈ (s.core.tmp.take len.toNat).map BitVec.toNat, l < 2 * s.core.cur_vars) ∧
        ((s.core.tmp.take len.toNat).map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.core.tmp.take len.toNat).map BitVec.toNat))) ∧
      (FullMem c s ⋆ R) m ∧
      if len.toNat < 2 then Q (0xFFFFFFFF#64, ()) m
      else if len.toNat = 2 then
        ∀ r flags' wvec' wstk' wlen' wusable' nb' wsort' m',
          let s' : FullState :=
            { s with
              core := { s.core with flags := flags', wvec := wvec', wstk := wstk',
                                    wlen := wlen', wusable := wusable', num_binary := nb' }
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
          (r = BitVec.ofNat 64 s.core.arena_len → alen' = s.core.arena_len + 3 + len.toNat ∧
            s.core.arena_len ∈ fullArenaClauseRefs s' ∧
            fullArenaClauseGarb s' s.core.arena_len = false ∧
            fullArenaClauseLits s' s.core.arena_len =
              (s.core.tmp.take len.toNat).map BitVec.toNat) →
          (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Mirror of `S5` `step13DeleteBinarySpec` (`full_delete_binary`). -/
def step13DeleteBinarySpec : Spec [i64, i32, i32] [] := fun (h, a, b, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧
    a.toNat < 2 * c.max_vars ∧ b.toNat < 2 * c.max_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ flags' wvec' wstk' wu' nb' m',
      let s' : FullState :=
        { s with core := { s.core with flags := flags', wvec := wvec', wstk := wstk',
                                       wusable := wu', num_binary := nb' } }
      s'.LengthsOk c → WatchStackLayout s'.core →
      (∀ F_cur, ModeWatchesInv F_cur s.core → ModeWatchesInv F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- Mirror of `S5` `step13BvaScanCandsSpec` (`full_bva_scan_cands`). -/
def step13BvaScanCandsSpec : Spec [i64, i32, i32, i64] [i32] :=
  fun (h, row_off, cur_qn, init_lits, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧
      s.core.dense_mode ≠ 0#64 ∧
      init_lits.toNat ≤ 2 * s.core.cur_vars ∧
      (∀ l < 2 * c.max_vars, (s.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
      row_off.toNat + cur_qn.toNat ≤ c.scratch_cap ∧
      (∀ qi < cur_qn.toNat,
        let w := s.scratch.scratch_buf[row_off.toNat + qi]?.getD 0#32
        if (w &&& 0x80000000#32) ≠ 0#32 then (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars
        else w.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s w.toNat = false) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ncntd : BitVec 32) wsort' ws1' ws2' ant' m',
        let s' : FullState :=
          { s with scratch :=
            { s.scratch with wsort := wsort', work_stk1 := ws1', work_stk2 := ws2',
                             ant_sz := ant' } }
        s'.LengthsOk c → ncntd.toNat ≤ 2 * c.max_vars →
        (∀ i < ncntd.toNat,
          (ws1'[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧
          (ws1'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
        (FullMem c s' ⋆ R) m' → Q (ncntd, ()) m'

/-- Step-13 `full_set_inactive`: extends `FullSubstLemmas.fullSetInactiveSpec` to allow VMTF
(`q_*`) and EVSIDS (`heap`, `pos`, `heap_len`) scratch updates while preserving `LengthsOk c`. -/
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

/-- Step-13 `full_viv_deduce_m6`: extends `fullVivDeduceM6Spec` with `min_clr'` and `arena'`
glue-promotion writes preserving arena refs, garbage flags, sizes, and literals. -/
def step13VivDeduceM6Spec : Spec [i64, i32, i32, i32] [i32] :=
  fun (h, cref, sz, implied, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧
      cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
      sz.toNat ≤ c.max_vars ∧
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

/-- Step-13 `full_viv_finish_m6` (Option A `FullM6HdrMem`-threaded lift of
`fullVivFinishM6Spec`). -/
def step13VivFinishM6Spec : Spec [i64, i32, i32, .bool, i32, .bool] [i64] :=
  fun (h, cref, sz, confl, implied, all_done, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
      (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrInvW c F0 F_cur ext s ∧ sz.toNat ≤ c.max_vars ∧
      cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
      fullArenaClauseSize s cref.toNat = sz.toNat ∧
      ((s.core.tmp.take sz.toNat).map BitVec.toNat).Perm (fullArenaClauseLits s cref.toNat) ∧
      (confl = true → FullConflictOkW F_cur s) ∧
      (confl = false → implied ≠ 0xFFFFFFFF#32 →
        implied.toNat < 2 * s.core.cur_vars ∧ s.core.vals[implied.toNat]?.getD 0#8 = 1#8) ∧
      (confl = false → implied = 0xFFFFFFFF#32 → all_done = true →
        s.core.confl_type = 0#64 ∧
        ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        FullM6HdrInvW c F0 F_cur ext' s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        s'.core.arena_len = s.core.arena_len → fullArenaClauseRefs s' = fullArenaClauseRefs s →
        s'.scratch.red_refs = s.scratch.red_refs →
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Mirror of `S1` `K6HwmClean`. -/
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

/-- Mirror of `S1` `step13K6InitSpec` (`glue_used[33]` HWM + `K6HwmClean`). -/
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

/-- Mirror of `S1` `step13K6AddClauseSpec` (`glue_used[33]` HWM + `K6HwmClean`, `pTmp`-free). -/
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

/-- Mirror of `S1` `step13SweepConeSpec` (`K6HwmClean`-preserving `full_m6_sweep_cone`). -/
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

/-- Mirror of `S1` `step13BveVarKeySpec` (`full_bve_var_key_m7`). -/
def step13BveVarKeySpec : Spec [i64, i32] [i64] := fun (h, _v, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ r : BitVec 64, Q (r, ()) m

/-- Mirror of `S1` `step13EliminateM6Spec` (`full_eliminate_m6`). -/
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

/-- Step-13 `full_analyze_rsn_m6_hdr`: extends `m6AnalyzeRsnHdrSpec` allowing `min_clr'` writes. -/
def step13AnalyzeRsnHdrSpec : Spec [i64, i32, i32] [.bool] := fun (h, rsn, skip_var, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat)
    (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    FullWitnessCutInv c F0 F_cur cut s.core ∧ FullAnaMarksCov c s ∧
    s.core.tmp_len ≤ s.core.cur_vars ∧ s.core.tmp_cnt + s.core.cur_vars + 1 < 2 ^ 64 ∧
    (rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ∈ fullArenaClauseRefs s) ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' tmp' mclr' tc' tl' mcl' arena' sc' ext' m',
      let s' : FullState := { s with
        core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                              min_clr := mclr', min_clr_len := mcl', arena := arena' }
        scratch := sc' }
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6ExtW2bPres ext ext') →
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
      (∀ j, s.core.tmp_len ≤ j → j < tl' → let l := (tmp'[j]?.getD 0#32).toNat
        l ∈ fullRsnLits s rsn ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
        s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8) →
      (∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
        (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2) →
      (tc' - s.core.tmp_cnt = ((List.range s.core.cur_vars).filter fun w =>
        decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
        decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length) →
      (sc'.res_sz = s.scratch.res_sz + BitVec.ofNat 64 ((List.range s.core.cur_vars).filter fun w =>
        decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length) →
      (ok = true → rsn ≠ 0xFFFFFFFF#32 ∧
        sc'.ant_sz = s.scratch.ant_sz + BitVec.ofNat 64 ((fullRsnLits s rsn).countP fun l =>
          decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)) ∧
        ∀ l ∈ fullRsnLits s rsn, l / 2 < s.core.cur_vars ∧ (l / 2 ≠ skip_var.toNat →
          (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
          (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
            (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
              (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
              ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (ok, ()) m'

/-- Step-13 `full_otfs_large`: extends `Full.fullOtfsLargeSpec` allowing `flags'` writes. -/
def step13OtfsLargeSpec : Spec [i64, i32, i32] [.bool] := fun (h, cref, uip, ()) m Q _ =>
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
    ∀ (ok : Bool) flags' arena' wvec' wstk' wlen' wu' oom' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with flags := flags', arena := arena', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wu', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur idx_u s'.core → FullArenaVarsNodup s' →
      FullExtScratchPres s s' → sc'.work_stk1 = s.scratch.work_stk1 →
      sc'.work_stk2 = s.scratch.work_stk2 → sc'.res_sz = s.scratch.res_sz →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = true → cref.toNat ∈ fullArenaClauseRefs s' ∧
        fullArenaClauseGarb s' cref.toNat = false ∧
        ∀ l ∈ fullArenaClauseLits s' cref.toNat, s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
          ((s'.core.lvl[l / 2]?.getD 0#32).toNat = s'.core.cur_level →
            ∃ m < idx_u, (s'.core.trl[m]?.getD 0#32).toNat = l ^^^ 1)) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Step-13 `full_bve_heap_push_m7`: extends `fullBveHeapPushM6Spec` requiring
`WatchStackLayout s.core` for `full_bve_var_key_m7` (`full_dense_occ_cnt_fid`). -/
def step13BveHeapPushSpec : Spec [i64, i64, i32] [i64] := fun (h, hlen, _v, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ hlen' ws1' ss' m',
      ws1'.length = 2 * c.max_vars → ss'.length = c.max_vars →
      (hlen.toNat ≤ s.core.cur_vars → hlen'.toNat ≤ s.core.cur_vars) →
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1', sim_sig := ss' } } ⋆
        R) m' →
      Q (hlen', ()) m'

/-- Step-13 `full_fwd_scan_lit_m7`: extends `fullFwdScanLitM7Spec` requiring
`WatchStackLayout s.core` for `full_dense_occ_cnt_fid`. -/
def step13FwdScanLitSpec : Spec [i64, i32, i32, i32, .bool] [i32] :=
  fun (h, cref, sz, scan_lit, check_bins, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧
      FullWitnessInv c F0 F_cur s.core ∧
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

/-- Step-13 `full_arena_sweep` contract (`FullSpec2.fullArenaSweepSpec` + `sc'.work_stk1`
preservation, matching `FullFidelityStep13S5.step13ArenaSweepSpec`). -/
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

/-! ## 3. Lifted Unchanged-Caller `Spec` Contracts (`S6a`) -/

/-- Mirror of `FullFidelityStep7.step7SortBinWatchesSpec` (`full_sort_bin_watches_fid`). -/
def step13SortBinWatchesSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (wstk' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with core := { s.core with wstk := wstk' } }
      wstk'.length = c.wcap →
      FullSparseInvW c F0 F_cur s' →
      WatchesInv F_cur s'.core →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- Option-A `FullM6HdrMem`-threaded lift of `fullFlushTrailSpec` (`full_flush_trail`). -/
def step13FlushTrailM6Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      FullM6HdrInv c F0 ext' s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (s.core.cur_level = 0 → s'.core.cur_level = 0) →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → s'.core.cur_level = 0 ∧ s'.core.propagated = s'.core.trail_end ∧
        s'.core.oom = 0#64 ∧ s'.core.unflushed = 0#64 ∧ s'.core.inconsistent = 0#64 ∧
        (s.core.cur_level = 0 → s.core.propagated < s.core.trail_end →
          s'.core.fuel.toNat < s.core.fuel.toNat)) →
      (r ≠ 1#64 → s'.core.cur_level = 0 ∨ s'.core.inconsistent ≠ 0#64) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Option-A `FullM6HdrMem`-threaded lift of `fullCompactFlushSpec` (`full_compact_flush`). -/
def step13CompactFlushM6Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      FullM6HdrInv c F0 ext' s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → s'.core.cur_level = 0 ∧ s'.core.propagated = s'.core.trail_end ∧
        s'.core.oom = 0#64 ∧ s'.core.unflushed = 0#64 ∧ s'.core.inconsistent = 0#64) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Option-A `FullM6HdrMem`-threaded lift of `fullCompactSpec` (`full_compact`). -/
def step13CompactM6Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r c' ext' s' m',
      FullCfgCompat c c' → FullM6HdrInv c' F0 ext' s' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars ≤ s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → s'.core.cur_level = 0) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Option-A `FullM6HdrMem`-threaded lift of `Full.fullRebuildWatchesSpec`
(`full_rebuild_watches_nosort_fid` / `full_rebuild_watches`). -/
def step13RebuildWatchesM6Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
    FullDenseInv c F0 s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      FullM6HdrInv c F0 ext' s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Option-A `FullM6HdrMem`-threaded Step-13 contract for `full_reduce_purge_c0` (avoids colliding
with `FullFidelityStep13S2.step13ReducePurgeC0M6Spec`), exporting `probing`, `min_clr_len`,
`work_stk1`, `tmp`, `tmp_len`, `cur_vars`, `work_stk2`, `cur_level ≤`, `fuel.toNat ≤`, `oom`
preservation, `r = 20#64 → F0.Unsat`, and `r = 1#64 → 0 < s'.core.cur_level` trail preservation. -/
def step13ReducePurgeC0HdrM6Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
    (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInvW c F0 F_cur ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      FullM6HdrInvW c F0 F_cur ext' s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_level ≤ s.core.cur_level → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.cur_vars = s.core.cur_vars → s'.core.tmp = s.core.tmp →
      s'.core.tmp_len = s.core.tmp_len → s'.core.probing = s.core.probing →
      s'.core.min_clr_len = s.core.min_clr_len →
      s'.scratch.work_stk1 = s.scratch.work_stk1 → s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64) →
      (r = 1#64 → 0 < s'.core.cur_level →
        s'.core.cur_level = s.core.cur_level ∧ s'.core.vals = s.core.vals ∧
        s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
        s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Option-A `FullM6HdrMem`-threaded lift of `fullVivInstM6Spec` (`full_viv_inst_m6`). -/
def step13VivInstM6Spec : Spec [i64, i32, i32] [i64] := fun (h, cref, sz, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
    (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInvW c F0 F_cur ext s ∧
    cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
    fullArenaClauseSize s cref.toNat = sz.toNat ∧ sz.toNat ≤ c.max_vars ∧
    ((s.core.tmp.take sz.toNat).map BitVec.toNat).Perm (fullArenaClauseLits s cref.toNat) ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      FullM6HdrInvW c F0 F_cur ext' s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.arena_len = s.core.arena_len → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Option-A `FullM6HdrMem`-threaded lift of `fullVivClauseM6Spec` (`full_viv_clause_m6`),
exporting `M6HdrExtInitOk` / `M6ExtW2bPres` preservation for `S5` vivify callers. -/
def step13VivClauseM6Spec : Spec [i64, i32] [i64] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
    (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInvW c F0 F_cur ext s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      FullM6HdrInvW c F0 F_cur ext' s' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.arena_len = s.core.arena_len → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Option-A `FullM6HdrMem`-threaded lift of `fullSubstElimVarsSpec` (`full_subst_elim_vars`). -/
def step13SubstElimVarsM6Spec : Spec [i64, i64] [.bool] := fun (h, ucnt, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
    (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInvW c F0 F_cur ext s ∧ s.core.cur_level = 0 ∧ FullReprEquiv F_cur s ∧
    ucnt.toNat ≤ c.max_vars ∧
    (∀ k < ucnt.toNat,
      (s.scratch.shrink_stk[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [(s.scratch.shrink_stk[k]?.getD 0#32).toNat])) ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ (ok : Bool) ext' s' m',
      FullM6HdrInvW c F0 F_cur ext' s' → s'.core.cur_level = 0 →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      FullReprEquiv F_cur s' → (ok = false → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (ok, ()) m'

/-- Option-A `FullM6HdrMem`-threaded lift of `fullSubstituteSpec` (`full_substitute`). -/
def step13SubstituteM6Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      FullM6HdrInv c F0 ext' s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Step-13 `full_bva_pick_cand`: accepts `ncntd ≤ 2 * c.max_vars` matching
`step13BvaScanCandsSpec` so `full_bva_try_lit` needs no `ncntd ≤ 2 * cur_vars` re-clamp. -/
def step13BvaPickCandSpec : Spec [i64, i32, i32] [i32] :=
  fun (h, ncntd, f0, ()) m Q _ =>
    ∃ c F0 F_cur s R,
      h = c.hdr ∧ FullBvaHeap.FullBvaHeapHelpers.FullDenseInvNoLm c F0 F_cur s ∧
      f0.toNat < 2 * s.core.cur_vars ∧ ncntd.toNat ≤ 2 * c.max_vars ∧
      (∀ i < ncntd.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 32) (repr' mclr' : List (BitVec 32)) (tc' tl' : Nat)
        (wsort' : List (BitVec 32)) (ant' : BitVec 64) (sig' : List (BitVec 64))
        (shrk' : List (BitVec 32)) (m' : Mem 64),
        let s' : FullState :=
          { core := { s.core with tmp_cnt := tc', tmp_len := tl', min_clr := mclr', repr := repr' }
            scratch := { s.scratch with ant_sz := ant', shrink_stk := shrk',
                                          wsort := wsort', sim_sig := sig' } }
        FullBvaHeap.FullBvaHeapHelpers.FullDenseInvNoLm c F0 F_cur s' →
        (r = 4294967295#32 ∨ r.toNat < 2 * s.core.cur_vars) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

end

/-! ## 4. `_monoX` / `_noExit` / `deadSpec_wp` / Structural Bridges (`0` `@[expose]` on thms) -/

public section

theorem deadSpec_monoX {as bs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post bs}
    {X X' : XPost} (h : deadSpec xs m Q X) : deadSpec xs m Q X' := h

theorem deadSpec_noExit {as bs : List Ty} :
    ∀ xs m Q X, deadSpec (as := as) (bs := bs) xs m Q X →
      deadSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem deadSpec_wp {as bs : List Ty} (Γ : Env) (f : Func as bs) :
    ∀ xs m Q X, deadSpec xs m Q X → Func.wp Γ f xs m Q X :=
  fun _ _ _ _ h => False.elim h

theorem step13PropagateIgnoreM6Spec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : step13PropagateIgnoreM6Spec xs m Q X) :
    step13PropagateIgnoreM6Spec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem step13PropagateIgnoreM6Spec_noExit :
    ∀ xs m Q X, step13PropagateIgnoreM6Spec xs m Q X →
      step13PropagateIgnoreM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step13PropagateIgnoreM6Spec_monoX h

theorem step13BcpM6Spec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : step13BcpM6Spec xs m Q X) : step13BcpM6Spec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem step13BcpM6Spec_noExit :
    ∀ xs m Q X, step13BcpM6Spec xs m Q X → step13BcpM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step13BcpM6Spec_monoX h

theorem step13BcpM6S3Spec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : step13BcpM6S3Spec xs m Q X) : step13BcpM6S3Spec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem step13BcpM6S1Spec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : step13BcpM6S1Spec xs m Q X) : step13BcpM6S1Spec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem step13WalkM7Spec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : step13WalkM7Spec xs m Q X) : step13WalkM7Spec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem step13WarmupM6Spec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : step13WarmupM6Spec xs m Q X) : step13WarmupM6Spec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem step13WarmupM6Spec_noExit :
    ∀ xs m Q X, step13WarmupM6Spec xs m Q X → step13WarmupM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step13WarmupM6Spec_monoX h

theorem step13LuckyScanM6Spec_monoX {xs : Tup Val [i64, .bool, .bool]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : step13LuckyScanM6Spec xs m Q X) :
    step13LuckyScanM6Spec xs m Q X' := by
  rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

theorem step13LuckyLateM6Spec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : step13LuckyLateM6Spec xs m Q X) : step13LuckyLateM6Spec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem step13LuckyLateM6Spec_noExit :
    ∀ xs m Q X, step13LuckyLateM6Spec xs m Q X →
      step13LuckyLateM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step13LuckyLateM6Spec_monoX h

theorem step13ParseBodyM6Spec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : step13ParseBodyM6Spec xs m Q X) : step13ParseBodyM6Spec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem step13ParseBodyM6Spec_noExit :
    ∀ xs m Q X, step13ParseBodyM6Spec xs m Q X →
      step13ParseBodyM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step13ParseBodyM6Spec_monoX h

theorem step13AddClauseSpec_monoX {xs : Tup Val [i64, i32, i32, .bool]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : step13AddClauseSpec xs m Q X) :
    step13AddClauseSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, ⟨⟩⟩; exact h

theorem step13DeleteBinarySpec_monoX {xs : Tup Val [i64, i32, i32]} {m : Mem 64}
    {Q : Post []} {X X' : XPost} (h : step13DeleteBinarySpec xs m Q X) :
    step13DeleteBinarySpec xs m Q X' := by
  rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

theorem step13BvaScanCandsSpec_monoX {xs : Tup Val [i64, i32, i32, i64]} {m : Mem 64}
    {Q : Post [i32]} {X X' : XPost} (h : step13BvaScanCandsSpec xs m Q X) :
    step13BvaScanCandsSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, ⟨⟩⟩; exact h

theorem step13BvaPickCandSpec_monoX {xs : Tup Val [i64, i32, i32]} {m : Mem 64} {Q : Post [i32]}
    {X X' : XPost} (h : step13BvaPickCandSpec xs m Q X) : step13BvaPickCandSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

theorem step13BvaPickCandSpec_noExit :
    ∀ xs m Q X, step13BvaPickCandSpec xs m Q X →
      step13BvaPickCandSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step13BvaPickCandSpec_monoX h

theorem fullBvaPickCandSpec_to_step13 :
    ∀ xs m Q X, FullBvaHeap.fullBvaPickCandSpec xs m Q X → step13BvaPickCandSpec xs m Q X := by
  rintro ⟨h, ncntd, f0, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinv, hf0, hnc, hcntd, hm, hQ⟩
  exact ⟨c, F0, F_cur, s, R, rfl, hinv, hf0,
    Nat.le_trans hnc (Nat.mul_le_mul_left 2 hinv.1.core_ok.cur_vars_le), hcntd, hm, hQ⟩

theorem step13SetInactiveSpec_monoX {xs : Tup Val [i64, i32, i32]} {m : Mem 64}
    {Q : Post []} {X X' : XPost} (h : step13SetInactiveSpec xs m Q X) :
    step13SetInactiveSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

theorem step13VivDeduceM6Spec_monoX {xs : Tup Val [i64, i32, i32, i32]} {m : Mem 64}
    {Q : Post [i32]} {X X' : XPost} (h : step13VivDeduceM6Spec xs m Q X) :
    step13VivDeduceM6Spec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, ⟨⟩⟩; exact h

theorem step13VivFinishM6Spec_monoX {xs : Tup Val [i64, i32, i32, .bool, i32, .bool]}
    {m : Mem 64} {Q : Post [i64]} {X X' : XPost} (h : step13VivFinishM6Spec xs m Q X) :
    step13VivFinishM6Spec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, _, _, ⟨⟩⟩; exact h

theorem step13K6InitSpec_monoX {xs : Tup Val [i64, i32]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : step13K6InitSpec xs m Q X) : step13K6InitSpec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem step13K6AddClauseSpec_monoX {xs : Tup Val [i64, i64, i32]} {m : Mem 64} {Q : Post [.bool]}
    {X X' : XPost} (h : step13K6AddClauseSpec xs m Q X) : step13K6AddClauseSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

theorem step13SweepConeSpec_monoX {xs : Tup Val [i64, i32]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : step13SweepConeSpec xs m Q X) : step13SweepConeSpec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem step13SweepConeSpec_noExit :
    ∀ xs m Q X, step13SweepConeSpec xs m Q X → step13SweepConeSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step13SweepConeSpec_monoX h

theorem step13BveVarKeySpec_monoX {xs : Tup Val [i64, i32]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : step13BveVarKeySpec xs m Q X) : step13BveVarKeySpec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem step13EliminateM6Spec_monoX {xs : Tup Val [i64, .bool]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : step13EliminateM6Spec xs m Q X) : step13EliminateM6Spec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem step13AnalyzeRsnHdrSpec_monoX {xs : Tup Val [i64, i32, i32]} {m : Mem 64} {Q : Post [.bool]}
    {X X' : XPost} (h : step13AnalyzeRsnHdrSpec xs m Q X) : step13AnalyzeRsnHdrSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

theorem step13OtfsLargeSpec_monoX {xs : Tup Val [i64, i32, i32]} {m : Mem 64} {Q : Post [.bool]}
    {X X' : XPost} (h : step13OtfsLargeSpec xs m Q X) : step13OtfsLargeSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

theorem step13BveHeapPushSpec_monoX {xs : Tup Val [i64, i64, i32]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : step13BveHeapPushSpec xs m Q X) : step13BveHeapPushSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

theorem step13BveHeapPushSpec_noExit :
    ∀ xs m Q X, step13BveHeapPushSpec xs m Q X →
      step13BveHeapPushSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step13BveHeapPushSpec_monoX h

theorem step13FwdScanLitSpec_monoX {xs : Tup Val [i64, i32, i32, i32, .bool]} {m : Mem 64}
    {Q : Post [i32]} {X X' : XPost} (h : step13FwdScanLitSpec xs m Q X) :
    step13FwdScanLitSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, _, ⟨⟩⟩; exact h

theorem step13FlushTrailM6Spec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : step13FlushTrailM6Spec xs m Q X) : step13FlushTrailM6Spec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem step13FlushTrailM6Spec_noExit :
    ∀ xs m Q X, step13FlushTrailM6Spec xs m Q X →
      step13FlushTrailM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step13FlushTrailM6Spec_monoX h

theorem step13CompactFlushM6Spec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : step13CompactFlushM6Spec xs m Q X) :
    step13CompactFlushM6Spec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem step13CompactFlushM6Spec_noExit :
    ∀ xs m Q X, step13CompactFlushM6Spec xs m Q X →
      step13CompactFlushM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step13CompactFlushM6Spec_monoX h

theorem step13CompactM6Spec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : step13CompactM6Spec xs m Q X) : step13CompactM6Spec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem step13CompactM6Spec_noExit :
    ∀ xs m Q X, step13CompactM6Spec xs m Q X → step13CompactM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step13CompactM6Spec_monoX h

theorem step13RebuildWatchesM6Spec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : step13RebuildWatchesM6Spec xs m Q X) :
    step13RebuildWatchesM6Spec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem step13RebuildWatchesM6Spec_noExit :
    ∀ xs m Q X, step13RebuildWatchesM6Spec xs m Q X →
      step13RebuildWatchesM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step13RebuildWatchesM6Spec_monoX h

theorem step13ArenaSweepSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : step13ArenaSweepSpec xs m Q X) : step13ArenaSweepSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem step13ArenaSweepSpec_noExit :
    ∀ xs m Q X, step13ArenaSweepSpec xs m Q X →
      step13ArenaSweepSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step13ArenaSweepSpec_monoX h

theorem step13ReducePurgeC0HdrM6Spec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : step13ReducePurgeC0HdrM6Spec xs m Q X) :
    step13ReducePurgeC0HdrM6Spec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem step13ReducePurgeC0HdrM6Spec_noExit :
    ∀ xs m Q X, step13ReducePurgeC0HdrM6Spec xs m Q X →
      step13ReducePurgeC0HdrM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step13ReducePurgeC0HdrM6Spec_monoX h

theorem step13VivInstM6Spec_monoX {xs : Tup Val [i64, i32, i32]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : step13VivInstM6Spec xs m Q X) : step13VivInstM6Spec xs m Q X' := by
  rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

theorem step13VivInstM6Spec_noExit :
    ∀ xs m Q X, step13VivInstM6Spec xs m Q X →
      step13VivInstM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step13VivInstM6Spec_monoX h

theorem step13VivClauseM6Spec_monoX {xs : Tup Val [i64, i32]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : step13VivClauseM6Spec xs m Q X) : step13VivClauseM6Spec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem step13VivClauseM6Spec_noExit :
    ∀ xs m Q X, step13VivClauseM6Spec xs m Q X →
      step13VivClauseM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step13VivClauseM6Spec_monoX h

theorem step13SubstElimVarsM6Spec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [.bool]}
    {X X' : XPost} (h : step13SubstElimVarsM6Spec xs m Q X) :
    step13SubstElimVarsM6Spec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem step13SubstElimVarsM6Spec_noExit :
    ∀ xs m Q X, step13SubstElimVarsM6Spec xs m Q X →
      step13SubstElimVarsM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step13SubstElimVarsM6Spec_monoX h

theorem step13SubstituteM6Spec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : step13SubstituteM6Spec xs m Q X) : step13SubstituteM6Spec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem step13SubstituteM6Spec_noExit :
    ∀ xs m Q X, step13SubstituteM6Spec xs m Q X →
      step13SubstituteM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step13SubstituteM6Spec_monoX h

/-- Bridge from `S2`'s `step13BcpM6Spec` (`sc'` general) to `S3`'s `step13BcpM6S3Spec`. -/
theorem step13BcpM6Spec_to_s3 {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : step13BcpM6S3Spec xs m Q X) : step13BcpM6Spec xs m Q X := by
  rcases xs with ⟨hdr, ⟨⟩⟩
  rcases h with ⟨c, F0, F_cur, ext, s, R, rfl, hinv, hm, hQ⟩
  refine ⟨c, F0, F_cur, ext, s, R, rfl, hinv.cfgOk, hinv.extOk, hinv.sparseW.1,
    hinv.sparseW.2.1, hinv.sparseW.2.2.2.2.2, hm, ?_⟩
  intro r ext' vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen'
    wu' fuel' ctype' cref' c0' c1' oom' sc' m' s' hext' _ hlen' hw' htr' hperm' hscp' hrr' _ _ _
    hfl' hr _ hr1 _ _ hm'
  have hspw0 := hinv.sparseW
  have hnd' : FullArenaVarsNodup s' := by
    intro cr hcr hng
    have hcr0 : cr ∈ fullArenaClauseRefs s := by
      change cr ∈ fullArenaClauseRefsCore s'.core at hcr
      change cr ∈ fullArenaClauseRefsCore s.core
      rw [← hperm'.2.1]; exact hcr
    obtain ⟨_, hgb, hp⟩ := hperm'.2.2 cr hcr0
    exact (hspw0.2.2.2.1 cr hcr0 (hgb.symm.trans hng)).perm (hp.symm.map (· / 2))
  have hextScr' : FullExtScratchOk c s' := by
    exact FullExtScratchOk.of_pres hspw0.2.2.2.2.1 hscp'.1 fun cr hcr => by
      change cr ∈ fullArenaClauseRefsCore s'.core; rw [hperm'.2.1]; exact hcr
  have hspw' : FullSparseInvW c F0 F_cur s' :=
    ⟨hlen', hw', hspw0.2.2.1, hnd', hextScr', hspw0.2.2.2.2.2⟩
  have hinv' : FullM6HdrInvW c F0 F_cur ext' s' := FullM6HdrInvW.mk_inv hinv.cfgOk hext' hspw'
  exact hQ r ext' s' m' hinv' htr' hperm' rfl hfl' hrr' hr
    (fun h1 => let ⟨hf, ho, hc⟩ := hr1 h1; ⟨hf, ho, hc⟩) hm'

/-- Bridge from `step13FwdScanLitSpec` to `FullM7BveGates.fullFwdScanLitM7Spec`. -/
theorem step13FwdScanLitSpec_to_canon {xs : Tup Val [i64, i32, i32, i32, .bool]} {m : Mem 64}
    {Q : Post [i32]} {X : XPost} (h : step13FwdScanLitSpec xs m Q X) :
    fullFwdScanLitM7Spec xs m Q X := by
  rcases xs with ⟨hdr, cr, sz, sl, cb, ⟨⟩⟩
  rcases h with ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hl0, hdm, hnd, href, hng, hsz, hscan, hcb,
    hlm, hm, hQ⟩
  exact fullFwdScanLitM7Spec_intro rfl hlen hw hl0 hdm hnd href hng hsz hscan hcb hlm hm hQ

/-- Shared `FullSparseInv` preservation from `step13BcpM6Spec` (`FullProbeScratchPres` +
`FullWitnessInv` + `FullArenaPermEq`). -/
theorem fullSparseInv_of_step13Bcp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInv c F0 s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64} {wvec' arena' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' fuel' ctype' cref' c0' c1' oom' : BitVec 64} {sc' : FullScratch}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te',
                            propagated := prop', unassigned := unass', unflushed := unfl',
                            wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                            wusable := wu', fuel := fuel', confl_type := ctype',
                            confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := sc' } : FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                    trl := trl', trail_pos := tp', trail_end := te',
                    propagated := prop', unassigned := unass', unflushed := unfl',
                    wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                    wusable := wu', fuel := fuel', confl_type := ctype',
                    confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' })
    (hperm' : FullArenaPermEq s.core
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                    trl := trl', trail_pos := tp', trail_end := te',
                    propagated := prop', unassigned := unass', unflushed := unfl',
                    wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                    wusable := wu', fuel := fuel', confl_type := ctype',
                    confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' })
    (hscp' : FullProbeScratchPres { s with scratch := { s.scratch with
      search_ticks := sc'.search_ticks, wsort := sc'.wsort,
      phases := sc'.phases, delayed := sc'.delayed } }
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              propagated := prop', unassigned := unass', unflushed := unfl',
                              wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                              wusable := wu', fuel := fuel', confl_type := ctype',
                              confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                              oom := oom' }
        scratch := sc' }) :
    FullSparseInv c F0
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              propagated := prop', unassigned := unass', unflushed := unfl',
                              wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                              wusable := wu', fuel := fuel', confl_type := ctype',
                              confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                              oom := oom' }
        scratch := sc' } := by
  let s' : FullState :=
    { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te',
                            propagated := prop', unassigned := unass', unflushed := unfl',
                            wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                            wusable := wu', fuel := fuel', confl_type := ctype',
                            confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := sc' }
  have hnd' : FullArenaVarsNodup s' := by
    intro cr hcr hng
    have hcr0 : cr ∈ fullArenaClauseRefs s := by
      change cr ∈ fullArenaClauseRefsCore s'.core at hcr
      change cr ∈ fullArenaClauseRefsCore s.core
      rw [← hperm'.2.1]; exact hcr
    obtain ⟨_, hgb, hp⟩ := hperm'.2.2 cr hcr0
    exact (hsp.2.2.1 cr hcr0 (hgb.symm.trans hng)).perm (hp.symm.map (· / 2))
  have hextScr' : FullExtScratchOk c s' := by
    exact FullExtScratchOk.of_pres hsp.2.2.2.1 hscp'.1 fun cr hcr => by
      change cr ∈ fullArenaClauseRefsCore s'.core; rw [hperm'.2.1]; exact hcr
  exact ⟨⟨hlen', F_cur, hw'⟩, hsp.2.1, hnd', hextScr', hsp.2.2.2.2⟩

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
