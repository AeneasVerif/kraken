module

public import LeanQbe.T.Examples.Kissat.FullFastSched
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.DimacsLemmas
public import LeanQbe.T.Examples.Kissat.FullReduceLemmas2
public import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` M2 Fast-Scheduler `Func.wp` Proofs (`FullFastSchedLemmas`, UNSAT-Only)

Canonical `FullSpec*`-compatible `Func.wp` UNSAT soundness proofs for all `15` upgraded / added
C0 functions in `FullFastSched.lean` plus `kissat_solve_bytes` (`16` proved entries), zero
`FullHdr` layout churn (`last_probe_ticks`/`last_elim_ticks` stored in `fwd_sub_cnt`/`fwd_str_cnt`),
and concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, zero SAT/model proofs):
1. Level-0 binary-sweep `325/325` completeness fix (`full_sweep_bins`, `full_substitute`,
   `full_enter_dense`).
2. Ticks-gated helpers (`full_min_u64`, `full_max_u64`, `full_scale_delta`, `full_probe_dticks`,
   `full_elim_dticks`, `full_probe_tail`, `full_elim_bve`).
3. Upgraded top orchestrators (`full_probe`, `full_eliminate`, `full_preprocess`, `full_simplify`
   with lazy `full_reduce(h, false)`, `full_search`) and `kissat_solve_bytes`.
4. `173`-row `schedSpecTable`, `mkSchedEnv`, `schedEnv`, `schedUnsatEnv`, `SpecEntry.Impl` for all
   `15` `sched_fns` + `kissat_solve_bytes`, and concrete `4096`-byte UNSAT non-vacuity.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFastSched

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Canonical `FullSpec*`-Compatible Contracts & `173`-Row `schedSpecTable` -/

/-- Upgraded `full_enter_dense` contract: identical to `Full.fullEnterDenseSpec` except
`s'.core.fuel.toNat ≤ s.core.fuel.toNat` (reflecting the level-0 `full_propagate` flush). -/
def schedEnterDenseSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      s'.core.cur_level = 0 → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (ok = true → FullDenseInv c F0 s') →
      (ok = false → FullSparseInv c F0 s') →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def schedScaleDeltaSpec : Spec [i64, i64] [i64] := fun (h, _delta, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧ ∀ r : BitVec 64, Q (r, ()) m

def schedMinU64Spec : Spec [i64, i64] [i64] := fun (a, b, ()) m Q _ =>
  ∀ r : BitVec 64, (r = a ∨ r = b) → Q (r, ()) m

def schedMaxU64Spec : Spec [i64, i64] [i64] := fun (a, b, ()) m Q _ =>
  ∀ r : BitVec 64, (r = a ∨ r = b) → Q (r, ()) m

def schedProbeDticksSpec : Spec [i64, .bool] [i64] := fun (h, _initial, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧ ∀ r : BitVec 64, Q (r, ()) m

def schedProbeTailSpec : Spec [i64, i64] [i64] := fun (h, _dticks, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def schedProbeSpec : Spec [i64, .bool] [i64] := fun (h, _initial, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def schedElimDticksSpec : Spec [i64, .bool] [i64] := fun (h, _initial, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧ ∀ r : BitVec 64, Q (r, ()) m

def schedElimBveSpec : Spec [i64, i64] [i64] := fun (h, _bve_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def schedEliminateSpec : Spec [i64, .bool] [i64] := fun (h, _initial, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def schedSimplifySpec : Spec [i64, .bool, .bool] [i64] := fun (h, _dp, _de, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `173`-row specification table matching `schedSplicedFns` row-by-row (`full_sweep_bins` and
`full_substitute` reuse canonical `FullSpec*` rows; `full_enter_dense` uses `schedEnterDenseSpec`;
the `12` ticks-gated schedulers replace indices `160..164`; `kissat_solve_bytes` sits at `172`). -/
def schedSpecTable (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : List SpecEntry :=
  let base := fullSpecTable mainSpec
  base.take 126 ++
  [ ⟨"full_enter_dense", [i64], [.bool], schedEnterDenseSpec, true⟩ ] ++
  (base.drop 127).take 33 ++
  [ ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  , ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
  , ⟨"full_max_u64", [i64, i64], [i64], schedMaxU64Spec, true⟩
  , ⟨"full_probe_dticks", [i64, .bool], [i64], schedProbeDticksSpec, true⟩
  , ⟨"full_probe_tail", [i64, i64], [i64], schedProbeTailSpec, true⟩
  , ⟨"full_probe", [i64, .bool], [i64], schedProbeSpec, true⟩
  , ⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩
  , ⟨"full_elim_bve", [i64, i64], [i64], schedElimBveSpec, true⟩
  , ⟨"full_eliminate", [i64, .bool], [i64], schedEliminateSpec, true⟩
  , ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩
  , ⟨"full_simplify", [i64, .bool, .bool], [i64], schedSimplifySpec, true⟩
  , ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩ ] ++
  base.drop 165

def mkSchedEnv (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : Env :=
  Env.ofTable (schedSpecTable mainSpec)

def schedEnv : Env := mkSchedEnv fullSolveBytesSpec

theorem schedSpecTable_noExit (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ e ∈ schedSpecTable mainSpec, e.noExit = true := by
  intro e he
  have hall : (schedSpecTable mainSpec).all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem schedSpecTable_sigs (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (schedSpecTable mainSpec).map (fun e => (e.name, e.as, e.rs)) =
      schedSplicedFns.map (fun f => (f.name, f.as, f.rs)) := by
  t_kernel_rfl

/-! ## 2. Pure Invariant & Framing Helpers -/

section Helpers

private theorem fullSparseInv_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 { s with scratch := sc' } :=
  h.of_safetySlice (h.lengths.with_scratch hok) rfl ⟨hll, hext⟩

private theorem fullDenseInv_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullDenseInv c F0 { s with scratch := sc' } := by
  obtain ⟨F_cur, hw⟩ := h.1.witness
  have hll' : FullLastLearnedWf { s with scratch := sc' } := fun i hi => by
    change sc'.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (sc'.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s
    rw [hll]; exact h.2.2.2.1.1 i hi
  exact ⟨⟨h.lengths.with_scratch hok, F_cur, hw⟩,
    h.2.1, h.2.2.1, ⟨hll', hext ▸ h.2.2.2.1.2⟩, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem fullDenseInv_with_flags {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {fl' : List (BitVec 32)} (hflen : fl'.length = c.max_vars) :
    FullDenseInv c F0 { s with core := { s.core with flags := fl' } } := by
  obtain ⟨F_cur, hw⟩ := h.1.witness
  have hlen' : ({ s with core := { s.core with flags := fl' } } : FullState).LengthsOk c :=
    ⟨{ h.lengths.core_ok with flags_len := hflen }, h.lengths.scratch_ok⟩
  exact ⟨⟨hlen', F_cur, { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem fullSparseInvW_of_perm {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hperm : FullArenaPermEq s.core s'.core)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hpres : FullExtScratchPres s s') : FullSparseInvW c F0 F_cur s' := by
  refine ⟨hlen', hw', ?_, ?_, ?_, hdm.trans hsp.2.2.2.2.2⟩
  · exact ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
      fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩
  · intro ref href hng
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 ref href0 (hgb.symm.trans hng))
  · exact hsp.2.2.2.2.1.of_pres hpres fun ref href => by
      change ref ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact href

private theorem fullSparseInv_of_perm_core {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (hsp : FullSparseInv c F0 s) (hcore' : FullCoreInv c F0 s')
    (hperm : FullArenaPermEq s.core s'.core)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hpres : FullExtScratchPres s s') : FullSparseInv c F0 s' := by
  refine ⟨hcore', ?_, ?_, ?_, hdm.trans hsp.2.2.2.2⟩
  · exact ⟨fun v hv => by rw [hmrk]; exact hsp.2.1.1 v hv,
      fun l hl => by rw [hlm]; exact hsp.2.1.2 l hl⟩
  · intro ref href hng
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hsp.2.2.1 ref href0 (hgb.symm.trans hng))
  · exact hsp.2.2.2.1.of_pres hpres fun ref href => by
      change ref ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact href

private theorem fullSparseInv_of_same_arena {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (hsp : FullSparseInv c F0 s) (hcore' : FullCoreInv c F0 s')
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hpres : FullExtScratchPres s s') : FullSparseInv c F0 s' := by
  refine ⟨hcore', ?_, ?_, ?_, hdm.trans hsp.2.2.2.2⟩
  · exact ⟨fun v hv => by rw [hmrk]; exact hsp.2.1.1 v hv,
      fun l hl => by rw [hlm]; exact hsp.2.1.2 l hl⟩
  · intro ref href hng
    have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har, hal]
    have hgb : fullArenaClauseGarb s' ref = fullArenaClauseGarb s ref := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [har]
    have hlits : fullArenaClauseLits s' ref = fullArenaClauseLits s ref := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har]
    rw [hrefs] at href; rw [hgb] at hng; rw [hlits]; exact hsp.2.2.1 ref href hng
  · exact hsp.2.2.2.1.of_pres hpres fun ref href => by
      change ref ∈ fullArenaClauseRefsCore s'.core
      unfold fullArenaClauseRefsCore; rw [har, hal]; exact href

private theorem fullSparseInvW_after_sweep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s) (hlen' : s'.LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur s'.core) (hnd' : FullArenaVarsNodup s')
    (hll' : FullLastLearnedWf s') (hext' : s'.scratch.extend_len = s.scratch.extend_len)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = s.core.dense_mode) : FullSparseInvW c F0 F_cur s' :=
  ⟨hlen', hw',
    ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
     fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩,
    hnd', ⟨hll', hext' ▸ hsp.2.2.2.2.1.2⟩, hdm.trans hsp.2.2.2.2.2⟩

private theorem fullSparseInvW_with_unflushed {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (u' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with unflushed := u' } } :=
  ⟨⟨{ hsp.1.core_ok with vals_len := hsp.1.core_ok.vals_len }, hsp.1.scratch_ok⟩,
    FullDenseWatchHelpers.fullWitnessInv_with_unflushed hsp.2.1 u',
    hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem level0_fcur_unsat_of_conflict_okW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hc : FullConflictOkW F_cur s) :
    (cnfOfClauses F_cur).Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    right; rcases hl with rfl | rfl
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
      rwa [heq] at hs
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
      rwa [heq] at hs
  · refine unsat_of_entails_nil
      (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => ?_)
    right
    have hlt := hw.arena.lits_lt _ href hng l hl
    obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hlt).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
    rwa [heq] at hs

private theorem fullWitnessInv_with_inconsistent {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (hu : (cnfOfClauses F_cur).Unsat) (inc' : BitVec 64) :
    FullWitnessInv c F0 F_cur { k with inconsistent := inc' } :=
  { hw with
    inconsistent_sound := fun _ => hu
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

private theorem fullSparseInvW_with_inconsistent {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hu : (cnfOfClauses F_cur).Unsat) (inc' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with inconsistent := inc' } } :=
  ⟨⟨{ hsp.1.core_ok with vals_len := hsp.1.core_ok.vals_len }, hsp.1.scratch_ok⟩,
    fullWitnessInv_with_inconsistent hsp.2.1 hu inc',
    hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem fullSparseInv_after_backtrack0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)}
    {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s) (hlen' : s'.LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur s'.core) (hpres : FullExtScratchPres s s')
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (hdm : s'.core.dense_mode = s.core.dense_mode) : FullSparseInvW c F0 F_cur s' := by
  refine ⟨hlen', hw',
    ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
     fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩, ?_, ?_, hdm.trans hsp.2.2.2.2.2⟩
  · intro ref href hng
    have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har, hal]
    have hgb : fullArenaClauseGarb s' ref = fullArenaClauseGarb s ref := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [har]
    have hlits : fullArenaClauseLits s' ref = fullArenaClauseLits s ref := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har]
    rw [hrefs] at href; rw [hgb] at hng; rw [hlits]; exact hsp.2.2.2.1 ref href hng
  · exact hsp.2.2.2.2.1.of_pres hpres fun ref href => by
      change ref ∈ fullArenaClauseRefsCore s'.core
      unfold fullArenaClauseRefsCore; rw [har, hal]; exact href

private theorem parseClauses_vars_pos {mv : Nat} :
    ∀ {n : Nat} {acc : CNF Nat} {bs : List UInt8} {cnf : CNF Nat},
      CnfVarsPos acc → parseClauses mv n acc bs = some cnf → CnfVarsPos cnf
  | 0, acc, bs, cnf, hacc, h => by
    unfold parseClauses at h
    cases hsw : skipWsComments bs with
    | nil => rw [hsw] at h; cases Option.some.inj h; exact hacc
    | cons _ _ => rw [hsw] at h; cases h
  | n + 1, acc, bs, cnf, hacc, h => by
    unfold parseClauses at h
    cases hpc : parseClause mv bs with
    | none => rw [hpc] at h; cases h
    | some p =>
      rcases p with ⟨cl, rest⟩
      rw [hpc] at h
      exact parseClauses_vars_pos
        (cnfVarsPos_add hacc (parseClauseAux_vars_pos (by simp) hpc)) h

private theorem parseDimacs_vars_pos {bs : List UInt8} {cnf : CNF Nat}
    (h : parseDimacs bs = some cnf) : CnfVarsPos cnf := by
  unfold parseDimacs at h
  cases hh : parseHeader bs with
  | none => rw [hh] at h; cases h
  | some p =>
    rcases p with ⟨mv, nc, rest⟩
    rw [hh] at h
    exact parseClauses_vars_pos (by intro _ hc; simp at hc) h

private theorem fullInv_max_vars_lt32 (c : FullCfg) : c.max_vars < 2 ^ 32 := by
  have h := c.hmaxv; unfold dimacsBound at h; omega

private theorem bv64_ugt_max_sub_false {p : BitVec 64} {n : Nat}
    (hfit : p.toNat + n < 2 ^ 64) :
    ((0xFFFFFFFFFFFFFFFF#64 - p).ult (BitVec.ofNat 64 n)) = false := by
  have hp := p.isLt
  have hmax : (0xFFFFFFFFFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 64 - 1 := rfl
  have hsub : 0xFFFFFFFFFFFFFFFF#64 - p = BitVec.ofNat 64 (2 ^ 64 - 1 - p.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, hmax, bv64_ofNat_toNat (by omega)]; omega
  rw [hsub, bv_ult_eq (by omega) (by omega)]
  simp only [decide_eq_false_iff_not]; omega

private theorem fullAlignPad_bv_eq (p : BitVec 64) :
    (8 - (p &&& 7)) &&& 7 = BitVec.ofNat 64 (fullAlignPad p) := by
  apply BitVec.eq_of_toNat_eq
  rw [show ((8 : BitVec 64) - (p &&& 7)) &&& 7 = (8#64 - (p &&& 7#64)) &&& 7#64 from rfl,
    fullAlignPad_eq, bv64_ofNat_toNat (by have := fullAlignPad_lt8 p; omega)]

private theorem full_merge_reg {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hw_ge : fullAlignPad work_ptr ≤ wlen) {m' : Mem 64}
    (hm' : (bytes cnf_ptr cnfBytes ⋆
      region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
        (wlen - fullAlignPad work_ptr) ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m') :
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' := by
  have h1 : ((region work_ptr (fullAlignPad work_ptr) ⋆
      region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
        (wlen - fullAlignPad work_ptr)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m' := sep_ac hm'
  have h2 : (region work_ptr (fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m' :=
    sep_mono (fun _ f => pad_region_merge (by omega) f) h1
  rw [show fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr) = wlen by omega] at h2
  exact sep_ac h2

private theorem full_merge_arena {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {c : FullCfg} {st : FullState}
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64) (hw_ge : fullAlignPad work_ptr ≤ wlen)
    (hch : c.hdr = work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
    (hca : c.avail = wlen - fullAlignPad work_ptr) (hlen : st.LengthsOk c) {m' : Mem 64}
    (hm' : (bytes cnf_ptr cnfBytes ⋆ FullMem c st ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m') :
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' := by
  apply full_merge_reg hwfit hw_ge
  have h1 : (FullMem c st ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m' := sep_ac hm'
  have h2 : (region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
      (wlen - fullAlignPad work_ptr) ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m' :=
    sep_mono (fun _ f => by rw [← hch, ← hca]; exact FullArenaInv.to_region ⟨hlen, f⟩) h1
  exact sep_ac h2

private def schedSearchVariant (st : FullState) : Nat :=
  2 * st.core.fuel.toNat + if st.core.propagated = st.core.trail_end then 1 else 0

end Helpers

/-! ## 3. Level-0 Binary-Sweep `325/325` Completeness Fix (`3` fns) -/

section CompletenessFix

open scoped FullArenaTactics
open FullReduceHelpers FullDenseWatchHelpers

/-- `Func.wp` proof for upgraded `full_sweep_bins` against exact canonical
`Full.fullSweepBinsSpec` (`prop_done`-guarded falsified-literal deletion + sentinel fill). -/
theorem sched_sweep_bins_wp (Γ : Env)
    (hdefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X) :
    ∀ a m Q X, fullSweepBinsSpec a m Q X → Func.wp Γ full_sweep_bins_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, hQ⟩
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwl_le := hlen.core_ok.wlen_le
  have hv_len := hlen.core_ok.vals_len
  have hl_len := hlen.core_ok.lvl_len
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hwcap_lt : c.wcap < 2 * 2 ^ 28 := c.hwcap
  let dense : Bool := decide (s.core.dense_mode ≠ 0#64)
  have hnlits_eq :
      ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    have h1 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [bv64_shl1_toNat (by omega), h1]
  unfold Func.wp full_sweep_bins_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (l, ()) mL =>
      l.toNat ≤ 2 * s.core.cur_vars ∧
      ∃ wvecL wstkL wuL nbL,
        let sL : FullState :=
          { s with core := { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL,
                                         num_binary := nbL } }
        sL.LengthsOk c ∧ ModeWatchesInv F_cur sL.core ∧
        (∀ j < l.toNat,
          FullReduceSpecs.BinOnlyWatchSliceOk F_cur sL.core j
            (fullWatchOff sL j) (fullWatchSize sL j)) ∧
        (FullMem c sL ⋆ R) mL)
    (fun (l, ()) _ => 2 * s.core.cur_vars - l.toNat)
    (fun JL hLoopL => by
      c0_hsteps
      exact hLoopL (0#64, ()) m ⟨Nat.zero_le _, s.core.wvec, s.core.wstk, s.core.wusable,
        s.core.num_binary, hlen, hw.watches, fun _ hj => absurd hj (Nat.not_lt_zero _), hm⟩)
    (fun JL ⟨l, ⟨⟩⟩ mL ⟨hl_le, wvecL, wstkL, wuL, nbL, hlenL, hwatL, hbinL, hmL⟩ hLoopL => ?_)
  let sL : FullState :=
    { s with core := { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL,
                                   num_binary := nbL } }
  have hwvL_len : wvecL.length = 4 * c.max_vars := hlenL.core_ok.wvec_len
  c0_hsplit
  · have hl_lt : l.toNat < 2 * s.core.cur_vars := by
      have : l.toNat < ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat := by c0_bound
      omega
    have hl1_eq : (l + (1 : BitVec 64)).toNat = l.toNat + 1 := by bv_omega
    have h2l_eq : (l <<< (1 : Nat)).toNat = 2 * l.toNat := bv64_shl1_toNat (by omega)
    have h2l1_eq : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * l.toNat + 1 := by
      rw [bv64_add1 (by omega), h2l_eq]
    have h2l_lt : 2 * l.toNat < wvecL.length := by omega
    have h2l1_lt : 2 * l.toNat + 1 < wvecL.length := by omega
    have h1bv : (1 : BitVec 64).toNat = 1 := rfl
    have hmod0 : 2 * l.toNat % 2 ^ 64 = 2 * l.toNat := Nat.mod_eq_of_lt (by omega)
    have hmod1 : (2 * l.toNat + 1) % 2 ^ 64 = 2 * l.toNat + 1 := Nat.mod_eq_of_lt (by omega)
    let off0 : Nat := fullWatchOff sL l.toNat
    let sz0 : Nat := fullWatchSize sL l.toNat
    let offW : BitVec 32 := wvecL[(l <<< (1 : Nat)).toNat]'(by omega)
    let szW : BitVec 32 := wvecL[((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'(by omega)
    have hoff_idx : (wvecL[2 * l.toNat]'h2l_lt).toNat = off0 := by
      unfold off0 fullWatchOff fullWatchOffCore sL
      rw [List.getElem?_eq_getElem h2l_lt, Option.getD_some]
    have hsz_idx : (wvecL[2 * l.toNat + 1]'h2l1_lt).toNat = sz0 := by
      unfold sz0 fullWatchSize fullWatchSizeCore sL
      rw [List.getElem?_eq_getElem h2l1_lt, Option.getD_some]
    have hoff_eq : offW.toNat = off0 := by unfold offW; simp only [h2l_eq]; exact hoff_idx
    have hsz_eq : szW.toNat = sz0 := by unfold szW; simp only [h2l1_eq]; exact hsz_idx
    have hbd_end : off0 + sz0 ≤ s.core.wlen := hwatL.bounds l.toNat hl_lt
    have hslice0 : FullReduceSpecs.ModeWatchSliceOk dense F_cur sL.core l.toNat off0 sz0 :=
      modeWatchesInv_slice_of_lt hwatL hl_lt
    clear hw hlen hdefrag hQ
    c0_hsplit
    · have hsz0 : sz0 = 0 := by
        have h1 := congrArg BitVec.toNat hc
        simp only [h1bv, hmod1] at h1
        rw [zext_toNat (wvecL[2 * l.toNat + 1]'h2l1_lt) (by decide), hsz_idx] at h1
        exact h1
      c0_hsteps
      refine hLoopL (l + (1 : BitVec 64), ()) mL (by dsimp only; rw [hl1_eq]; omega)
        ⟨by rw [hl1_eq]; omega, wvecL, wstkL, wuL, nbL, hlenL, hwatL, fun j hj => ?_, hmL⟩
      rw [hl1_eq] at hj
      by_cases hjl : j = l.toNat
      · subst hjl; change FullReduceSpecs.BinOnlyWatchSliceOk F_cur sL.core l.toNat off0 sz0
        rw [hsz0]; exact .empty
      · exact hbinL j (by omega)
    · have hlv_eq : (l >>> (1 : Nat)).toNat = l.toNat / 2 := bv64_shr1_toNat l
      have hlv_lt : (l >>> (1 : Nat)).toNat < s.core.lvl.length := by rw [hlv_eq]; omega
      have hl_v : l.toNat < s.core.vals.length := by omega
      let end0 : Nat := off0 + sz0
      c0_hsteps_nogrp
      -- Join after `lsat`
      refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ())) (fun _ => True) ?_ ?_
      · intro _ _ _
        c0_hsteps_nogrp
        -- Join after `lfix`
        refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ()))
          (fun _ => True) ?_ ?_
        · intro _ _ _
          c0_hsteps_nogrp
          -- Inner compaction loop `(p, q)`
          refine wp_loop_inv
            (fun (p, q, ()) m1 =>
              off0 ≤ q.toNat ∧ q.toNat ≤ p.toNat ∧ p.toNat ≤ end0 ∧
              ∃ wstk1 nb1, wstk1.length = c.wcap ∧
                (∀ i, i < off0 ∨ p.toNat ≤ i → wstk1[i]? = wstkL[i]?) ∧
                FullReduceSpecs.ModeWatchSliceOk dense F_cur sL.core l.toNat p.toNat
                  (end0 - p.toNat) ∧
                FullReduceSpecs.BinOnlyWatchSliceOk F_cur
                  { s.core with wvec := wvecL, wstk := wstk1, wusable := wuL, num_binary := nbL }
                  l.toNat off0 (q.toNat - off0) ∧
                (FullMem c { s with core := { s.core with wvec := wvecL, wstk := wstk1,
                                                          wusable := wuL, num_binary := nb1 } } ⋆
                  R) m1)
            (fun (p, _, ()) _ => end0 - p.toNat)
            (fun J1 hLoop1 => by
              c0_hsteps
              have hoff64 : (offW.setWidth 64).toNat = off0 := by
                rw [zext_toNat offW (by decide), hoff_eq]
              refine hLoop1 _ mL ⟨by rw [hoff64]; exact Nat.le_refl _,
                by rw [hoff64]; exact Nat.le_refl _, by rw [hoff64]; omega,
                wstkL, nbL, hlenL.core_ok.wstk_len_arr, fun _ _ => rfl, ?_, ?_, hmL⟩
              · rw [hoff64, show end0 - off0 = sz0 by omega]; exact hslice0
              · rw [hoff64, Nat.sub_self]; exact .empty)
            (fun J1 ⟨p, q, ⟨⟩⟩ m1 ⟨hoq, hqp, hpe, wstk1, nb1, hlen1, hout1, hrem1, hpre1, hm1⟩
                hLoop1 => ?_)
          have hend_bv : (offW.setWidth 64 + szW.setWidth 64).toNat = end0 := by
            rw [BitVec.toNat_add, zext_toNat offW (by decide), zext_toNat szW (by decide),
              hoff_eq, hsz_eq, Nat.mod_eq_of_lt (by omega)]
          c0_hsplit
          · have hp_lt : p.toNat < end0 := by
              simp only [h1bv, hmod0, hmod1, hoff_idx, hsz_idx] at hc; omega
            have hp_w : p.toNat < wstk1.length := by omega
            have hq_w : q.toNat < wstk1.length := by omega
            let w0 := wstk1[p.toNat]'hp_w
            have hw0_orig : sL.core.wstk[p.toNat]? = some w0 := by
              dsimp only [sL]
              rw [← hout1 p.toNat (Or.inr (Nat.le_refl _)), List.getElem?_eq_getElem hp_w]
            have hstep := hrem1.step (by omega) hw0_orig
            c0_hsteps_nogrp; c0_hstep; c0_hsplit
            · -- Binary watch
              have hbin : (w0 &&& 0x80000000#32) ≠ 0#32 := by
                change ((wstk1[p.toNat]'hp_w) &&& 0x80000000#32) ≠ 0#32; assumption
              obtain ⟨hne, hlt_o, hent_o, hrem'⟩ := hstep.1 hbin
              have hp1_eq : (p + (1 : BitVec 64)).toNat = p.toNat + 1 := bv64_add1 (by omega)
              have hq1_eq : (q + (1 : BitVec 64)).toNat = q.toNat + 1 := bv64_add1 (by omega)
              have hot_lt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars := hlt_o
              have hot_sh : ((w0 &&& 0x7FFFFFFF#32) >>> 1#32).toNat =
                  (w0 &&& 0x7FFFFFFF#32).toNat / 2 := bv32_shr1_toNat _
              have hot_lvl : ((w0 &&& 0x7FFFFFFF#32) >>> 1#32).toNat < s.core.lvl.length := by
                rw [hot_sh]; omega
              have hot_v : (w0 &&& 0x7FFFFFFF#32).toNat < s.core.vals.length := by omega
              c0_hsteps_nogrp
              -- Join after `osat`
              refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ()))
                (fun _ => True) ?_ ?_
              · intro _ _ _
                c0_hsteps_nogrp
                -- Join after `ofix`
                refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ()))
                  (fun _ => True) ?_ ?_
                · intro _ _ _
                  c0_hsteps_nogrp
                  -- Join after `if (lfix || ofix) ... else ...`
                  refine wp_join_group (fun (q', ()) mQ =>
                    off0 ≤ q'.toNat ∧ q'.toNat ≤ p.toNat + 1 ∧
                    ∃ wstk' nb', wstk'.length = c.wcap ∧
                      (∀ i, i < off0 ∨ p.toNat + 1 ≤ i → wstk'[i]? = wstkL[i]?) ∧
                      FullReduceSpecs.BinOnlyWatchSliceOk F_cur
                        { s.core with wvec := wvecL, wstk := wstk', wusable := wuL,
                                      num_binary := nbL }
                        l.toNat off0 (q'.toNat - off0) ∧
                      (FullMem c { s with core := { s.core with wvec := wvecL, wstk := wstk',
                                                                wusable := wuL,
                                                                num_binary := nb' } } ⋆ R) mQ)
                    ?_ ?_
                  · rintro _ ⟨q', ⟨⟩⟩ mQ ⟨hoq', hqp', wstk', nb', hlen', hout', hpre', hmQ⟩
                    c0_hsteps
                    exact hLoop1 (p + (1 : BitVec 64), q', ()) mQ
                      (by dsimp only; rw [hp1_eq]; omega)
                      ⟨hoq', by rw [hp1_eq]; omega, by rw [hp1_eq]; omega, wstk', nb', hlen',
                       by rw [hp1_eq]; exact hout',
                       by rw [hp1_eq, show end0 - (p.toNat + 1) = end0 - p.toNat - 1 by omega]
                          exact hrem',
                       hpre', hmQ⟩
                  · intro Jq hJq
                    c0_hsteps_nogrp
                    refine wp_join_group (fun () mD => m1 = mD) ?_ ?_
                    · rintro _ ⟨⟩ mD hmD; subst mD
                      c0_hsteps
                      · exact hJq (q, ()) _ ⟨hoq, by omega, wstk1, nb1 - 1#64, hlen1,
                          fun i hi => hout1 i (by omega), hpre1, hm⟩
                      · exact hJq (q, ()) m1 ⟨hoq, by omega, wstk1, nb1, hlen1,
                          fun i hi => hout1 i (by omega), hpre1, hm1⟩
                      · exact hJq (q, ()) m1 ⟨hoq, by omega, wstk1, nb1, hlen1,
                          fun i hi => hout1 i (by omega), hpre1, hm1⟩
                    · intro Jd hJd
                      c0_hsteps
                      · exact hJd () m1 rfl
                      · exact hJd () m1 rfl
                      · refine hJq (q + (1 : BitVec 64), ()) _
                          ⟨by rw [hq1_eq]; omega, by rw [hq1_eq]; omega,
                           wstk1.set q.toNat w0, nb1, List.length_set.trans hlen1,
                           fun i hi => by
                             rw [List.getElem?_set_ne (by omega)]; exact hout1 i (by omega),
                           ?_, hm⟩
                        rw [hq1_eq, show q.toNat + 1 - off0 = (q.toNat - off0) + 1 by omega]
                        exact FullReduceSpecs.BinOnlyWatchSliceOk.append_bin
                          (k := { s.core with wvec := wvecL, wstk := wstk1, wusable := wuL,
                                              num_binary := nbL })
                          (k' := { s.core with wvec := wvecL, wstk := wstk1.set q.toNat w0,
                                               wusable := wuL, num_binary := nbL })
                          (p := off0) (p' := off0) (Nat.le_refl _)
                          (fun j hj => List.getElem?_set_ne (by omega)) hpre1
                          (by rw [show off0 + (q.toNat - off0) = q.toNat by omega]
                              exact List.getElem?_set_self hq_w)
                          hbin hne hlt_o hent_o
                · intro Jo hJo
                  clear hLoopL JL hLoop1 hbinL hwatL hlenL hslice0 hrem1 hpre1 hout1 hstep
                  c0_hsteps <;> exact hJo _ trivial
              · intro Jos hJos
                clear hLoopL JL hLoop1 hbinL hwatL hlenL hslice0 hrem1 hpre1 hout1 hstep
                c0_hsteps <;> exact hJos _ trivial
            · -- Non-binary watch: advance `p + 2`
              have hlg : (w0 &&& 0x80000000#32) = 0#32 := by
                change ((wstk1[p.toNat]'hp_w) &&& 0x80000000#32) = 0#32; assumption
              obtain ⟨h2rem, _, _, _, _, _, hrem'⟩ := hstep.2 hlg
              have hp2_eq : (p + (2 : BitVec 64)).toNat = p.toNat + 2 := bv64_add2 (by omega)
              c0_hsteps
              exact hLoop1 (p + (2 : BitVec 64), q, ()) m1 (by dsimp only; rw [hp2_eq]; omega)
                ⟨hoq, by rw [hp2_eq]; omega, by rw [hp2_eq]; omega, wstk1, nb1, hlen1,
                 fun i hi => by rw [hp2_eq] at hi; exact hout1 i (by omega),
                 by rw [hp2_eq, show end0 - (p.toNat + 2) = end0 - p.toNat - 2 by omega]
                    exact hrem',
                 hpre1, hm1⟩
          · -- Exit inner loop (`p = end0`): sentinel-fill `[q, end0)` with `0xFFFFFFFFu`
            have hp_end : p.toNat = end0 := by
              simp only [h1bv, hmod0, hmod1, hoff_idx, hsz_idx] at hc; omega
            clear hrem1 hslice0 hLoop1 J1
            c0_hsteps_nogrp
            refine wp_loop_inv
              (fun (k, ()) m2 =>
                q.toNat ≤ k.toNat ∧ k.toNat ≤ end0 ∧
                ∃ wstk2 : List (BitVec 32), wstk2.length = c.wcap ∧
                  (∀ i, i < q.toNat ∨ end0 ≤ i → wstk2[i]? = wstk1[i]?) ∧
                  (FullMem c { s with core := { s.core with wvec := wvecL, wstk := wstk2,
                                                            wusable := wuL,
                                                            num_binary := nb1 } } ⋆ R) m2)
              (fun (k, ()) _ => end0 - k.toNat)
              (fun J2 hLoop2 => by
                c0_hsteps; exact hLoop2 (q, ()) m1 ⟨Nat.le_refl _, by omega, wstk1, hlen1,
                  fun _ _ => rfl, hm1⟩)
              (fun J2 ⟨k, ⟨⟩⟩ m2 ⟨hqk, hke, wstk2, hlen2, hout2, hm2⟩ hLoop2 => ?_)
            c0_hsplit
            · have hk_lt : k.toNat < end0 := by
                simp only [h1bv, hmod0, hmod1, hoff_idx, hsz_idx] at hc; omega
              have hk1_eq : (k + (1 : BitVec 64)).toNat = k.toNat + 1 := bv64_add1 (by omega)
              c0_hsteps
              exact hLoop2 (k + (1 : BitVec 64), ()) _ (by dsimp only; rw [hk1_eq]; omega)
                ⟨by rw [hk1_eq]; omega, by rw [hk1_eq]; omega,
                 wstk2.set k.toNat 0xFFFFFFFF#32, List.length_set.trans hlen2,
                 fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hout2 i hi, hm⟩
            · have hqoff_bv : (q - offW.setWidth 64).setWidth 32
                  = BitVec.ofNat 32 (q.toNat - off0) := by
                apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_setWidth, BitVec.toNat_sub, zext_toNat offW (by decide), hoff_eq]
                have hlt32 : q.toNat - off0 < 2 ^ 32 := by omega
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32]
                have : (2 ^ 64 - off0 + q.toNat) % 2 ^ 64 = q.toNat - off0 := by omega
                rw [this, Nat.mod_eq_of_lt hlt32]
              c0_hsteps
              let wvec' := wvecL.set (2 * l.toNat + 1) (BitVec.ofNat 32 (q.toNat - off0))
              let wu' := wuL + ((offW.setWidth 64 + szW.setWidth 64) - q)
              obtain ⟨hlen', hwat', hbin'⟩ := full_sweep_bins_finish_lit
                hlenL.core_ok hlenL.scratch_ok hwatL hbinL
                hl_lt hlen2 hoq (show q.toNat ≤ end0 by omega)
                (fun i hi => hout1 i (by change i < off0 ∨ end0 ≤ i at hi; omega))
                hout2 hpre1
                { s.core with wvec := wvec', wstk := wstk2, wusable := wu', num_binary := nb1 }
                rfl
              have hwv_eq :
                  wvecL.set ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat
                    ((q - offW.setWidth 64).setWidth 32) = wvec' := by
                dsimp only [wvec']; rw [h2l1_eq, hqoff_bv]
              have hst_eq :
                  ({ s with core := { s.core with
                      wvec := wvecL.set ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat
                        ((q - offW.setWidth 64).setWidth 32),
                      wstk := wstk2, wusable := wu', num_binary := nb1 } } : FullState) =
                  { s with core := { s.core with wvec := wvec', wstk := wstk2,
                                                 wusable := wu', num_binary := nb1 } } :=
                congrArg (fun wv =>
                  { s with core := { s.core with wvec := wv, wstk := wstk2,
                                                 wusable := wu', num_binary := nb1 } })
                  hwv_eq
              exact hLoopL (l + (1 : BitVec 64), ()) _ (by dsimp only; rw [hl1_eq]; omega)
                ⟨by rw [hl1_eq]; omega, wvec', wstk2, wu', nb1, hlen', hwat',
                 by rw [hl1_eq]; exact hbin', fullMem_cast hm hst_eq⟩
        · intro Jf hJf
          clear hLoopL JL hbinL hwatL hlenL hslice0 hbd_end
          c0_hsteps <;> exact hJf _ trivial
      · intro Js hJs
        clear hLoopL JL hbinL hwatL hlenL hslice0 hbd_end
        c0_hsteps <;> exact hJs _ trivial
  · -- Exit outer loop (`l = 2 * cur_vars`): call `full_wstack_defrag`
    have hl_end : l.toNat = 2 * s.core.cur_vars := by
      have : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat ≤ l.toNat := by c0_bound
      omega
    have hbin_all : FullReduceSpecs.BinOnlyWatchesInv F_cur sL.core :=
      ⟨hwatL.layout, fun j hj => hbinL j (hl_end ▸ hj)⟩
    c0_hsteps; c0_call hdefrag
    refine ⟨c, sL, R, rfl, hlenL, hwatL.layout, hmL,
      fun wvec' wstk' wlen' wsort' m' hlen' hlay' _ hpres hm' => ?_⟩
    let sF : FullState :=
      { core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64,
                              num_binary := nbL }
        scratch := { s.scratch with wsort := wsort' } }
    have hbinF : FullReduceSpecs.BinOnlyWatchesInv F_cur sF.core :=
      fullWstackDefrag_preserves_binOnly hbin_all hlay' rfl hpres
    c0_hsteps
    exact hQ wvec' wstk' wlen' nbL wsort' m' hlen' hbinF.toFull hbinF.toDenseWatchesInv
      { hw with arena := { hw.arena with len_ok := hw.arena.len_ok },
                watches := hbinF.toModeWatchesInv } hm'

/-- `Func.wp` proof for upgraded `full_substitute` against exact canonical
`Full.fullSubstituteSpec` (`num_binary == 0` skip + pre-sweep `full_propagate` flush). -/
theorem sched_substitute_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hTarjan : ∀ a m Q X, fullTarjanSccSpec a m Q X → Γ "full_tarjan_scc" [i64] [i64] a m Q X)
    (hElimVars : ∀ a m Q X, fullSubstElimVarsSpec a m Q X →
      Γ "full_subst_elim_vars" [i64, i64] [.bool] a m Q X)
    (hRewriteBins : ∀ a m Q X, fullSubstRewriteBinsSpec a m Q X →
      Γ "full_subst_rewrite_bins" [i64] [.bool] a m Q X)
    (hRewriteAr : ∀ a m Q X, fullSubstRewriteArSpec a m Q X →
      Γ "full_subst_rewrite_ar" [i64] [.bool] a m Q X)
    (hArenaSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullSubstituteSpec a m Q X → Func.wp Γ full_substitute_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s0, R, rfl, hsp0, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  obtain ⟨F_cur0, hw0⟩ := hsp0.exists_witness
  have hcl0 := hsp0.1.lengths.core_ok
  have hclv_lt : s0.core.cur_level < 2 ^ 64 := by
    have := hw0.2.1.cur_level_le; have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega
  unfold Func.wp full_substitute_body
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun st m1 => FullSparseInv c F0 st ∧ st.core.cur_level = 0 ∧
      st.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c st ⋆ R) m1) ?_ ?_
  · rintro _ st1 m1 ⟨hsp1, hl01, hfl1, hm1⟩
    c0_hsplit
    · c0_hsteps
      exact hQ 1#64 st1 m1 hsp1 hl01 hfl1 (Or.inl rfl) (fun h => by cases h) hm1
    · c0_hsteps_nogrp
      refine wp_while_break_state (α := BitVec 64 × FullState) (β := BitVec 64 × FullState)
        (fun p => (p.1, ()))
        (fun p mb => FullSparseInv c F0 p.2 ∧ p.2.core.cur_level = 0 ∧
          p.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c p.2 ⋆ R) mb)
        (fun p => (p.1, ()))
        (fun p => 4 - p.1.toNat)
        (fun p ml => FullSparseInv c F0 p.2 ∧ p.2.core.cur_level = 0 ∧
          p.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ p.1.toNat ≤ 4 ∧ (FullMem c p.2 ⋆ R) ml)
        ?_ ?_ ?_
      · rintro _ ⟨_r, stb⟩ mb ⟨hspb, hl0b, hflb, hmb⟩
        c0_hsteps
        exact hQ 1#64 stb mb hspb hl0b hflb (Or.inl rfl) (fun h => by cases h) hmb
      · rintro B L ⟨round, st⟩ ml hB hL ⟨hsp, hl0_st, hfl_st, hr_le, hml⟩
        c0_hsplit
        · have hr_lt : round.toNat < 4 := hc
          have hr1 : (round + 1#64).toNat = round.toNat + 1 := by bv_omega
          c0_hsplit
          · c0_hsplit
            · obtain ⟨F_cur, hspw⟩ := hsp.exists_witness
              c0_hsteps; c0_call hTarjan
              refine ⟨c, F0, F_cur, st, R, rfl, hspw, hl0_st, hml, ?_⟩
              intro ucnt _ _ inc1 _ _ _ _ _ sstk1 _ m1 st1 hspw1 huc_le hus1 hrepr1 hm1
              have hl01' : st1.core.cur_level = 0 := hl0_st
              have hfl1' : st1.core.fuel.toNat ≤ s0.core.fuel.toNat := hfl_st
              c0_hsplit
              · c0_hsteps; exact hQ 20#64 st1 m1 hspw1.toSparse hl01' hfl1' (Or.inr rfl)
                  (fun _ => hspw1.2.1.ext_sound.2 (hspw1.2.1.inconsistent_sound hc)) hm1
              · c0_hsteps; c0_call hElimVars
                refine ⟨c, F0, F_cur, st1, R, rfl, hspw1, hl01', hrepr1 hc, huc_le, hus1, hm1, ?_⟩
                intro ok2 st2 m2 hspw2 hl02 _ hfl2 hrepr2 hfail2 hm2
                have hfl2' : st2.core.fuel.toNat ≤ s0.core.fuel.toNat := by omega
                c0_hsplit
                · c0_hsplit
                  · c0_hsteps; exact hB (round, st2) m2 ⟨hspw2.toSparse, hl02, hfl2', hm2⟩
                  · c0_hsteps; c0_call hRewriteBins
                    refine ⟨c, F0, F_cur, st2, R, rfl, hspw2, hl02, hrepr2, hm2, ?_⟩
                    intro ok3 st3 m3 hspw3 hl03 _ hfl3 hrepr3 hfail3 hm3
                    have hfl3' : st3.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                      rw [hfl3]; exact hfl2'
                    c0_hsplit
                    · c0_hsteps; c0_call hRewriteAr
                      refine ⟨c, F0, F_cur, st3, R, rfl, hspw3, hl03, hrepr3, hm3, ?_⟩
                      intro ok4 st4 m4 hspw4 hl04 _ hfl4 hfail4 hm4
                      have hfl4' : st4.core.fuel.toNat ≤ s0.core.fuel.toNat := hfl4 ▸ hfl3'
                      c0_hsplit
                      · -- Pre-sweep `full_propagate(h)` flush
                        c0_hsteps; c0_call hProp
                        refine ⟨c, F0, F_cur, st4, R, rfl, hspw4.1, hspw4.2.1,
                          hspw4.2.2.2.2.2, hm4, ?_⟩
                        intro pr4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel4p _ _ _ _ _ _ _ _ m4p st4p
                          hlen4p hw4p _ hperm4p hfl4p _ _ hpr4_1 _ _ hm4p
                        have hspw4p : FullSparseInvW c F0 F_cur st4p :=
                          fullSparseInvW_of_perm hspw4 hlen4p hw4p hperm4p rfl rfl rfl ⟨rfl, rfl⟩
                        have hl04p : st4p.core.cur_level = 0 := hl04
                        have hfl4p' : st4p.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                          have h1 : st4.core.fuel.toNat ≤ s0.core.fuel.toNat := hfl4'
                          dsimp only [st4p]; omega
                        c0_hsplit
                        · c0_hsteps
                          exact hQ 20#64 st4p m4p hspw4p.toSparse hl04p hfl4p' (Or.inr rfl)
                            (fun _ => level0_unsat_of_conflict_okW hw4p hl04p (hpr4_1 hc).2.2) hm4p
                        · c0_hsteps; c0_call hArenaSweep
                          refine ⟨c, F0, F_cur, st4p, R, rfl, hspw4p.1, hspw4p.2.1,
                            hspw4p.2.2.2.1, hspw4p.2.2.2.2.2, fun hpos => by omega, hm4p, ?_⟩
                          intro sr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sc5 m5 st5
                            hlen5 _ hext5 _ hll5 hw5 hnd5 _ _ _ hsr2 _ hm5
                          have hspw5 := fullSparseInvW_after_sweep hspw4p hlen5 hw5 hnd5 hll5 hext5
                            rfl rfl rfl
                          have hl05 : st5.core.cur_level = 0 := hl04p
                          c0_hsplit
                          · c0_hsteps
                            exact hQ 20#64 st5 m5 hspw5.toSparse hl05 hfl4p' (Or.inr rfl)
                              (fun _ => (hsr2 hc).2) hm5
                          · c0_hsteps; c0_call hProp
                            refine ⟨c, F0, F_cur, st5, R, rfl, hspw5.1, hspw5.2.1,
                              hspw5.2.2.2.2.2, hm5, ?_⟩
                            intro pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel6 _ _ _ _ _ _ _ _ m6 st6
                              hlen6 hw6 _ hperm6 hfl6 _ _ hpr1 _ _ hm6
                            have hspw6 := fullSparseInvW_of_perm hspw5 hlen6 hw6 hperm6 rfl rfl rfl
                              ⟨rfl, rfl⟩
                            have hfl6' : st6.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                              have h5 : st5.core.fuel.toNat ≤ s0.core.fuel.toNat := hfl4p'
                              dsimp only [st6]; omega
                            c0_hsplit
                            · c0_hsteps
                              exact hQ 20#64 st6 m6 hspw6.toSparse hl05 hfl6' (Or.inr rfl)
                                (fun _ => level0_unsat_of_conflict_okW hw6 hl05 (hpr1 hc).2.2) hm6
                            · c0_hsteps
                              exact hL (round + 1#64, st6) m6 (by dsimp only; omega)
                                ⟨hspw6.toSparse, hl05, hfl6', by dsimp only; omega, hm6⟩
                      · c0_hsteps; exact hQ 20#64 st4 m4 hspw4.toSparse hl04 hfl4' (Or.inr rfl)
                          (fun _ => hfail4 (by
                            cases ok4 <;> first | rfl | contradiction | exact absurd rfl hc)) hm4
                    · c0_hsteps; exact hQ 20#64 st3 m3 hspw3.toSparse hl03 hfl3' (Or.inr rfl)
                        (fun _ => hfail3 (by
                          cases ok3 <;> first | rfl | contradiction | exact absurd rfl hc)) hm3
                · c0_hsteps; exact hQ 20#64 st2 m2 hspw2.toSparse hl02 hfl2' (Or.inr rfl)
                    (fun _ => hfail2 (by
                      cases ok2 <;> first | rfl | contradiction | exact absurd rfl hc)) hm2
            · c0_hsteps; exact hB (round, st) ml ⟨hsp, hl0_st, hfl_st, hml⟩
          · c0_hsteps; exact hB (round, st) ml ⟨hsp, hl0_st, hfl_st, hml⟩
        · c0_hsteps; exact hB (round, st) ml ⟨hsp, hl0_st, hfl_st, hml⟩
      · intro B L _ hL; c0_hsteps
        exact hL (0#64, st1) m1 ⟨hsp1, hl01, hfl1, Nat.zero_le _, hm1⟩
  · intro Jbt hJbt; c0_hsplit
    · c0_hsteps; c0_call hBacktrack
      refine ⟨c, s0, R, rfl, hsp0.1.lengths, hclv_lt, fun _ => by
        have := hw0.2.1.cur_level_le; have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega,
        hw0.2.1.trail_lits_lt, hm, ?_⟩
      intro _ _ _ _ _ _ _ cl1 _ sc1 m1 st1 hlen1 _ _ hcl1 hprsc1 _ _ _ hw_le _ hm1
      have hw1 := hw_le F0 F_cur0 hw0.2.1 (Nat.zero_le _)
      have hl01 : st1.core.cur_level = 0 := by dsimp only [st1]; rw [hcl1]; simp
      c0_hsteps; exact hJbt st1 m1
        ⟨(fullSparseInv_after_backtrack0 hw0 hlen1 hw1 hprsc1.1 rfl rfl rfl rfl rfl).toSparse,
         hl01, Nat.le_refl _, hm1⟩
    · have hl00 : s0.core.cur_level = 0 := by
        have hnat := congrArg BitVec.toNat hc
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt] at hnat; exact hnat
      c0_hsteps; exact hJbt s0 m ⟨hsp0, hl00, Nat.le_refl _, hm⟩

private def SchedEnterOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s st : FullState) : Prop :=
  st.LengthsOk c ∧ FullWitnessInv c F0 F_cur st.core ∧ FullLitMarksClear c st ∧
  FullArenaVarsNodup st ∧ FullExtScratchOk c st ∧
  st.core.cur_level = 0 ∧ st.core.fuel.toNat ≤ s.core.fuel.toNat

/-- `Func.wp` proof for upgraded `full_enter_dense` against `schedEnterDenseSpec`
(adds level-0 `full_propagate` flush before `full_sweep_bins`). -/
theorem sched_enter_dense_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweepBins : ∀ a m Q X, fullSweepBinsSpec a m Q X → Γ "full_sweep_bins" [i64] [] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, schedEnterDenseSpec a m Q X → Func.wp Γ full_enter_dense_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp0, hm, hQ⟩
  obtain ⟨F_cur, hspw0⟩ := hsp0.exists_witness
  have har_cap : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hclv_lt : s.core.cur_level < 2 ^ 64 := by
    have := hspw0.2.1.cur_level_le; have := hspw0.1.core_ok.trail_end_le
    have := hspw0.1.core_ok.cur_vars_le; omega
  unfold Func.wp full_enter_dense_body
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => SchedEnterOk c F0 F_cur s s1 ∧ s1.core.dense_mode = 0#64 ∧
      (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro _ s1 m1 ⟨hok1, hdm1, hm1⟩
    clear hm hsp0 hspw0
    c0_hsplit
    · exact absurd hdm1 hc
    · -- `dense_mode == 0`: flush level-0 units before `full_sweep_bins`
      c0_hsteps; c0_call hProp
      refine ⟨c, F0, F_cur, s1, R, rfl, hok1.1, hok1.2.1, hdm1, hm1, ?_⟩
      intro pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel1p _ _ _ _ _ _ _ _ m1p s1p
        hlen1p hw1p _ hperm1p hfl1p _ _ hpr1 _ _ hm1p
      have hspw1 : FullSparseInvW c F0 F_cur s1 :=
        ⟨hok1.1, hok1.2.1, hok1.2.2.1, hok1.2.2.2.1, hok1.2.2.2.2.1, hdm1⟩
      have hspw1p := fullSparseInvW_of_perm hspw1 hlen1p hw1p hperm1p rfl rfl rfl ⟨rfl, rfl⟩
      have hcl1p : s1p.core.cur_level = 0 := hok1.2.2.2.2.2.1
      have hfl1p' : s1p.core.fuel.toNat ≤ s.core.fuel.toNat := by
        have h1 : s1.core.fuel.toNat ≤ s.core.fuel.toNat := hok1.2.2.2.2.2.2
        dsimp only [s1p]; omega
      c0_hsplit
      · -- Conflict at level 0: set `inconsistent = 1#64`, return `false`.
        c0_hsteps
        let s_inc : FullState := { s1p with core := { s1p.core with inconsistent := 1#64 } }
        have hu_fc := level0_fcur_unsat_of_conflict_okW hw1p hcl1p (hpr1 hc).2.2
        have hspw_inc : FullSparseInvW c F0 F_cur s_inc :=
          fullSparseInvW_with_inconsistent hspw1p hu_fc 1#64
        exact hQ false s_inc _ hcl1p hfl1p' (by simp) (fun _ => hspw_inc.toSparse) hm
      · -- No conflict: call `full_sweep_bins(h)` then push dense occurrences.
        c0_hsteps; c0_call hSweepBins
        refine ⟨c, F0, F_cur, s1p, R, rfl, hspw1p.1, hspw1p.2.1, hm1p,
          fun wvec2 wstk2 wlen2 nb2 wsort2 m2 hlen2 _ hd2 hw2 hm2 => ?_⟩
        let s2 : FullState :=
          { s1p with
            core := { s1p.core with
              wvec := wvec2, wstk := wstk2, wlen := wlen2, wusable := 0#64, num_binary := nb2 }
            scratch := { s1p.scratch with wsort := wsort2 } }
        have hok2 : SchedEnterOk c F0 F_cur s s2 :=
          ⟨hlen2, hw2, hspw1p.2.2.1, hspw1p.2.2.2.1, hspw1p.2.2.2.2.1, hcl1p, hfl1p'⟩
        c0_hsteps_nogrp
        refine wp_loop_inv
          (fun (p, ()) mP =>
            p.toNat ≤ s2.core.arena_len ∧
            (p.toNat = s2.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s2) ∧
            ∃ sP : FullState,
              SchedEnterOk c F0 F_cur s sP ∧ DenseWatchesInv F_cur sP.core ∧
              sP.core.arena = s2.core.arena ∧ sP.core.arena_len = s2.core.arena_len ∧
              sP.core.dense_mode = 0#64 ∧ (FullMem c sP ⋆ R) mP)
          (fun (p, ()) _ => s2.core.arena_len - p.toNat)
          (fun JP hLoopP => by
            c0_hsteps
            refine hLoopP (0#64, ()) m2 ⟨Nat.zero_le _, ?_, s2, hok2, hd2, rfl, rfl, hdm1, hm2⟩
            by_cases hz : s2.core.arena_len = 0
            · exact Or.inl hz.symm
            · exact Or.inr (FullDenseWatchHelpers.fullArenaClauseRefs_zero_mem hw2.arena
                (Nat.pos_of_ne_zero hz)))
          (fun JP ⟨p, ⟨⟩⟩ mP ⟨hp_le, hp_mem, sP, hokP, hdP, harP, halenP, hdmP, hmP⟩ hLoopP => ?_)
        have halP := hokP.1.core_ok.arena_len_le
        have haarP := hokP.1.core_ok.arena_len_arr
        have hrefsP : fullArenaClauseRefs sP = fullArenaClauseRefs s2 := by
          unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [harP, halenP]
        c0_hsplit
        · have hp_lt : p.toNat < sP.core.arena_len := by c0_bound
          have hp_in : p.toNat ∈ fullArenaClauseRefs sP := by
            rw [hrefsP]; exact hp_mem.resolve_left (by omega)
          have hp_wf := hokP.2.1.arena.refs_wf p.toNat hp_in
          have hp_lt32 : p.toNat < 2 ^ 32 := by omega
          have hp_trunc : (p.setWidth 32).toNat = p.toNat := by bv_omega
          have hnb := fullArenaNextOff_bounds (ar := sP.core.arena) (alen := sP.core.arena_len)
            (cref := p.toNat) hp_wf.1
          have hnxt_mem := fullArenaClauseRefs_next_mem hokP.2.1.arena hp_in
          c0_hsteps_nogrp
          refine wp_join_state0 (α := FullState)
            (fun sN mN => SchedEnterOk c F0 F_cur s sN ∧ DenseWatchesInv F_cur sN.core ∧
              sN.core.arena = s2.core.arena ∧ sN.core.arena_len = s2.core.arena_len ∧
              sN.core.dense_mode = 0#64 ∧ (FullMem c sN ⋆ R) mN)
            (fun _ sN mN ⟨hokN, hdN, harN, halenN, hdmN, hmN⟩ => by
              c0_hsteps; c0_call hArenaNext
              refine ⟨c, sN, R, rfl, hokN.1, hmN, ?_⟩
              have hn_eq : ((BitVec.ofNat 32 (fullArenaNextOff sN.core.arena sN.core.arena_len
                  (p.setWidth 32).toNat)).setWidth 64).toNat =
                  fullArenaNextOff sP.core.arena sP.core.arena_len p.toNat := by
                rw [harN, halenN, ← harP, ← halenP, hp_trunc, BitVec.toNat_setWidth,
                  bv32_ofNat_toNat (by omega)]
                exact Nat.mod_eq_of_lt (by omega)
              c0_hsteps
              exact hLoopP (_, ()) mN (by dsimp only; rw [hn_eq]; omega)
                ⟨by rw [hn_eq]; omega,
                  by rw [hn_eq]
                     rcases hnxt_mem with hend | hmem
                     · exact Or.inl (hend.trans halenP)
                     · exact Or.inr (hrefsP ▸ hmem),
                  sN, hokN, hdN, harN, halenN, hdmN, hmN⟩)
            (fun JN hJN => ?_)
          c0_hsteps_nogrp
          · have hsz_eq : (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat =
                fullArenaClauseSizeCore sP.core p.toNat := by
              have hp2 : (p + 2#64).toNat = p.toNat + 2 := by c0_bound
              unfold fullArenaClauseSizeCore
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hp2]
            have hsz_ge3 : 3 ≤ (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat := by
              rw [hsz_eq]; exact hp_wf.2.1
            have hsz_lt31 : (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat < 2 ^ 31 := by
              rw [hsz_eq]; have := hp_wf.2.2.1; have := hp_wf.2.2.2.1; omega
            have hmask := bv32_mask_7fffffff_props hsz_ge3 hsz_lt31
            have hp_lt31 : (p.setWidth 32).toNat < 0x80000000 := by rw [hp_trunc]; omega
            have hp_neff : p.setWidth 32 ≠ 0xFFFFFFFF#32 := fun heq => by
              rw [heq] at hp_lt31; revert hp_lt31; decide
            refine wp_loop_inv
              (fun (k, ()) mK =>
                k.toNat ≤ (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat ∧
                ∃ sK : FullState,
                  SchedEnterOk c F0 F_cur s sK ∧ DenseWatchesInv F_cur sK.core ∧
                  sK.core.arena = s2.core.arena ∧ sK.core.arena_len = s2.core.arena_len ∧
                  sK.core.dense_mode = 0#64 ∧ (FullMem c sK ⋆ R) mK)
              (fun (k, ()) _ => (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat - k.toNat)
              (fun JK hLoopK => by
                c0_hsteps
                exact hLoopK (0#32, ()) mP ⟨Nat.zero_le _, sP, hokP, hdP, harP, halenP, hdmP, hmP⟩)
              (fun JK ⟨k, ⟨⟩⟩ mK ⟨hk_le, sK, hokK, hdK, harK, halenK, hdmK, hmK⟩ hLoopK => ?_)
            have haarK := hokK.1.core_ok.arena_len_arr
            c0_hsplit
            · have hk_lt : k.toNat < (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat := by
                c0_bound
              have hidx_eq : (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat := by
                have := hp_wf.2.2.1; have := hp_wf.2.2.2.1; bv_omega
              have hidx_lt : (p + 3#64 + k.setWidth 64).toNat < sK.core.arena.length := by
                rw [hidx_eq]; rw [hsz_eq] at hk_lt
                have := hp_wf.2.2.1; have := hp_wf.2.2.2.1
                have := hokK.1.core_ok.arena_len_le; omega
              c0_hsteps; c0_call hWatchPush
              refine ⟨c, sK, R, rfl, hokK.1, hdK.layout, by simp,
                fun _ => ⟨hmask.2.1, hp_neff⟩, hmK,
                fun ok wvecK' wstkK' wlenK' wuK' wsortK' mK' hlenK' hlayK' hothK' hokT
                  hokF hmK' => ?_⟩
              let sK' : FullState :=
                { sK with
                  core := { sK.core with wvec := wvecK', wstk := wstkK', wlen := wlenK',
                                         wusable := wuK' }
                  scratch := { sK.scratch with wsort := wsortK' } }
              have hp_inK : (p.setWidth 32).toNat ∈ fullArenaClauseRefsCore sK.core := by
                rw [hp_trunc]; unfold fullArenaClauseRefsCore; rw [harK, halenK, ← harP, ← halenP]
                exact hp_in
              have hdK' : DenseWatchesInv F_cur sK'.core :=
                fullWatchPush_preserves_denseWatchesInv hdK hlayK' rfl (fun _ r => r)
                  hmask.1 hmask.2.2 hp_lt31 hp_inK hothK'
                  (fun ht => by
                    obtain ⟨hl, _, hsz', hpre', hw0', hw1'⟩ := hokT ht
                    exact ⟨hl, hsz', hpre', hw0', hw1' rfl⟩) (fun hf => (hokF hf).1)
              have hwK' : FullWitnessInv c F0 F_cur sK'.core :=
                { hokK.2.1 with
                  arena := { hokK.2.1.arena with len_ok := hokK.2.1.arena.len_ok }
                  watches := by
                    rw [ModeWatchesInv, ite_eq_left hdmK]; exact denseWatchesInv_toWatchesInv hdK' }
              have hokK' : SchedEnterOk c F0 F_cur s sK' :=
                ⟨hlenK', hwK', hokK.2.2.1, hokK.2.2.2.1, hokK.2.2.2.2.1, hokK.2.2.2.2.2.1,
                  hokK.2.2.2.2.2.2⟩
              c0_hsplit
              · have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                c0_hsteps
                exact hLoopK (k + 1#32, ()) mK' (by dsimp only; omega)
                  ⟨by omega, sK', hokK', hdK', harK, halenK, hdmK, hmK'⟩
              · c0_hsteps
                let sOom : FullState := { sK' with core := { sK'.core with oom := 0#64 } }
                have hlenOom : sOom.LengthsOk c :=
                  ⟨{ hlenK'.core_ok with vals_len := hlenK'.core_ok.vals_len }, hlenK'.scratch_ok⟩
                have hwOom := fullWitnessInv_with_oom hwK' 0#64
                c0_call hSweep
                refine ⟨c, F0, F_cur, sOom, R, rfl, hlenOom, hwOom, hokK'.2.2.2.1, hdmK,
                  fun hpos => by
                    change 0 < sK.core.cur_level at hpos; have := hokK.2.2.2.2.2.1; omega,
                  hm, ?_⟩
                intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ scS mS sS hlenS _ hextS _ hllS
                  hwS hndS _ _ _ _ _ hmS
                have hspS : FullSparseInv c F0 sS :=
                  ⟨⟨hlenS, F_cur, hwS⟩, hokK'.2.2.1, hndS, ⟨hllS, hextS ▸ hokK'.2.2.2.2.1.2⟩, hdmK⟩
                c0_hsteps
                exact hQ false sS mS hokK'.2.2.2.2.2.1 hokK'.2.2.2.2.2.2
                  (by simp) (fun _ => hspS) hmS
            · c0_hsteps; exact hJN sK mK ⟨hokK, hdK, harK, halenK, hdmK, hmK⟩
          all_goals exact hJN sP mP ⟨hokP, hdP, harP, halenP, hdmP, hmP⟩
        · -- Outer loop exit: set `dense_mode = 1#64`, return `true`.
          c0_hsteps
          let sFin : FullState := { sP with core := { sP.core with dense_mode := 1#64 } }
          have hlenFin : sFin.LengthsOk c :=
            ⟨{ hokP.1.core_ok with vals_len := hokP.1.core_ok.vals_len }, hokP.1.scratch_ok⟩
          have hwFin : FullWitnessInv c F0 F_cur sFin.core :=
            fullWitnessInv_with_dense_mode_nz hokP.2.1 hdP (by decide)
          have hdenFin : FullDenseInv c F0 sFin :=
            ⟨⟨hlenFin, F_cur, hwFin⟩, hokP.2.2.1, hokP.2.2.2.1, hokP.2.2.2.2.1,
              hokP.2.2.2.2.2.1, show (1#64 : BitVec 64) ≠ 0#64 by decide⟩
          exact hQ true sFin _ hokP.2.2.2.2.2.1 hokP.2.2.2.2.2.2
            (fun _ => hdenFin) (by simp) hm
  · intro J1 hJ1; c0_hsplit
    · c0_hsteps; c0_call hBacktrack
      refine ⟨c, s, R, rfl, hspw0.1, hclv_lt, fun _ => by
        have := hspw0.2.1.cur_level_le; have := hspw0.1.core_ok.trail_end_le
        have := hspw0.1.core_ok.cur_vars_le; omega,
        hspw0.2.1.trail_lits_lt, hm, ?_⟩
      intro _ _ _ _ _ _ _ cl1 _ sc1 m1 s1 hlen1 _ _ hcl1 hprsc1 _ _ _ hw_le _ hm1
      have hw1 := hw_le F0 F_cur hspw0.2.1 (Nat.zero_le _)
      have hl01 : s1.core.cur_level = 0 := by dsimp only [s1]; rw [hcl1]; simp
      have hsp1 := fullSparseInv_after_backtrack0 hspw0 hlen1 hw1 hprsc1.1 rfl rfl rfl rfl rfl
      c0_hsteps
      exact hJ1 s1 m1 ⟨⟨hsp1.1, hsp1.2.1, hsp1.2.2.1, hsp1.2.2.2.1, hsp1.2.2.2.2.1, hl01,
        Nat.le_refl _⟩, hsp1.2.2.2.2.2, hm1⟩
    · have hl00 : s.core.cur_level = 0 := by
        have hnat := congrArg BitVec.toNat hc
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt] at hnat; exact hnat
      c0_hsteps
      exact hJ1 s m ⟨⟨hspw0.1, hspw0.2.1, hspw0.2.2.1, hspw0.2.2.2.1, hspw0.2.2.2.2.1, hl00,
        Nat.le_refl _⟩, hspw0.2.2.2.2.2, hm⟩

end CompletenessFix

/-! ## 4. Pure Arithmetic & Read-Only Ticks-Budget Helpers (`5` fns) -/

section TicksHelpers

open scoped FullArenaTactics

theorem sched_min_u64_wp (Γ : Env) :
    ∀ a m Q X, schedMinU64Spec a m Q X → Func.wp Γ full_min_u64_body a m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X hQ
  unfold Func.wp full_min_u64_body; c0_hsteps
  · exact hQ a (Or.inl rfl)
  · exact hQ b (Or.inr rfl)

theorem sched_max_u64_wp (Γ : Env) :
    ∀ a m Q X, schedMaxU64Spec a m Q X → Func.wp Γ full_max_u64_body a m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X hQ
  unfold Func.wp full_max_u64_body; c0_hsteps
  · exact hQ a (Or.inl rfl)
  · exact hQ b (Or.inr rfl)

theorem sched_scale_delta_wp (Γ : Env)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X) :
    ∀ a m Q X, schedScaleDeltaSpec a m Q X → Func.wp Γ full_scale_delta_body a m Q X := by
  rintro ⟨h, delta, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, _, hm, hQ⟩
  unfold Func.wp full_scale_delta_body; c0_hsteps
  c0_call hIlog; intro lg _ _
  c0_hsteps_nogrp
  refine wp_join_state_pure (α := BitVec 64) (fun d => (d, ())) (fun _ => True)
    (fun _ d _ => by c0_hsteps; exact hQ _)
    (fun J hJ => by c0_hsteps <;> exact hJ _ trivial)

theorem sched_probe_dticks_wp (Γ : Env)
    (hMax : ∀ a m Q X, schedMaxU64Spec a m Q X → Γ "full_max_u64" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, schedProbeDticksSpec a m Q X → Func.wp Γ full_probe_dticks_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, _, hm, hQ⟩
  unfold Func.wp full_probe_dticks_body; c0_hsteps_nogrp
  refine wp_join_state_pure (α := BitVec 64) (fun r => (r, ())) (fun _ => True)
    (fun _ raw _ => by
      c0_hsteps_nogrp
      refine wp_join_state_pure (α := BitVec 64) (fun dt => (dt, ())) (fun _ => True)
        (fun _ dt _ => by c0_hsteps; c0_call hMax; intro r _; c0_hsteps; exact hQ r)
        (fun J2 hJ2 => by c0_hsteps <;> exact hJ2 _ trivial))
    (fun J1 hJ1 => by c0_hsteps <;> exact hJ1 _ trivial)

theorem sched_elim_dticks_wp (Γ : Env) :
    ∀ a m Q X, schedElimDticksSpec a m Q X → Func.wp Γ full_elim_dticks_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, _, hm, hQ⟩
  unfold Func.wp full_elim_dticks_body; c0_hsteps <;> exact hQ _

end TicksHelpers

/-! ## 5. Ticks-Gated Inprocessing & CDCL Orchestrators (`7` fns) -/

section Orchestrators

open scoped FullArenaTactics

theorem sched_probe_tail_wp (Γ : Env)
    (hTrans : ∀ a m Q X, fullTransitiveSpec a m Q X → Γ "full_transitive" [i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X → Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hPRun : ∀ a m Q X, fullProbeRunSpec a m Q X →
      Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, fullVivifySpec a m Q X → Γ "full_vivify" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, schedProbeTailSpec a m Q X → Func.wp Γ full_probe_tail_body a m Q X := by
  rintro ⟨h, dticks, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_probe_tail_body
  c0_hsteps_nogrp
  -- Join after optional `full_transitive`
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩ => by
      c0_hsteps; c0_call hMin; intro pbud _
      c0_hsteps_nogrp
      -- Join after optional `full_probe_run`
      refine wp_join_state0 (α := FullState)
        (fun s2 m2 => FullSparseInv c F0 s2 ∧ s2.core.cur_level = 0 ∧
          s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s2 ⋆ R) m2)
        (fun _ s2 m2 ⟨hinv2, hcl2, hfu2, hm2⟩ => by
          c0_hsteps; c0_call hViv; refine ⟨c, F0, s2, R, rfl, hinv2, hm2, ?_⟩
          intro r3 s3 m3 hinv3 hcl3 _ hfu3 _ hu3 hm3; c0_hsteps
          · exact hQ 20#64 s3 m3 hinv3 hcl3 (by omega) (Or.inr rfl) (fun _ => hu3 hc) hm3
          c0_call hViv; refine ⟨c, F0, s3, R, rfl, hinv3, hm3, ?_⟩
          intro r4 s4 m4 hinv4 hcl4 _ hfu4 _ hu4 hm4; c0_hsteps
          · exact hQ 20#64 s4 m4 hinv4 hcl4 (by omega) (Or.inr rfl) (fun _ => hu4 hc) hm4
          c0_call hViv; refine ⟨c, F0, s4, R, rfl, hinv4, hm4, ?_⟩
          intro r5 s5 m5 hinv5 hcl5 _ hfu5 _ hu5 hm5; c0_hsteps
          · exact hQ 20#64 s5 m5 hinv5 hcl5 (by omega) (Or.inr rfl) (fun _ => hu5 hc) hm5
          exact hQ 1#64 s5 m5 hinv5 hcl5 (by omega) (Or.inl rfl) (fun h => by cases h) hm5)
        (fun J2 hJ2 => by
          c0_hsplit
          · c0_hsteps; c0_call hPRun; refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
            intro rp s2 m2 hinv2 hcl2 _ hfu2 _ hup2 hm2; c0_hsteps
            · exact hQ 20#64 s2 m2 hinv2 hcl2 (by omega) (Or.inr rfl) (fun _ => hup2 hc) hm2
            exact hJ2 s2 m2 ⟨hinv2, hcl2, by omega, hm2⟩
          · c0_hsteps; exact hJ2 s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩))
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps; c0_call hTrans; refine ⟨c, F0, s, R, rfl, hinv, hm, ?_⟩
        intro rt s1 m1 hinv1 hcl1 _ hfu1 _ hut1 hm1; c0_hsteps
        · exact hQ 20#64 s1 m1 hinv1 hcl1 hfu1 (Or.inr rfl) (fun _ => hut1 hc) hm1
        exact hJ1 s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩
      · c0_hsteps; exact hJ1 s m ⟨hinv, hcl0, Nat.le_refl _, hm⟩)

theorem sched_probe_wp (Γ : Env)
    (hDticks : ∀ a m Q X, schedProbeDticksSpec a m Q X →
      Γ "full_probe_dticks" [i64, .bool] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, fullSubstituteSpec a m Q X → Γ "full_substitute" [i64] [i64] a m Q X)
    (hCong : ∀ a m Q X, fullCongruenceSpec a m Q X → Γ "full_congruence" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullSweepSatSpec a m Q X → Γ "full_sweep_sat" [i64] [i64] a m Q X)
    (hTail : ∀ a m Q X, schedProbeTailSpec a m Q X →
      Γ "full_probe_tail" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, schedProbeSpec a m Q X → Func.wp Γ full_probe_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_probe_body
  c0_hsteps; c0_call hDticks; refine ⟨c, s, R, rfl, hinv.lengths, hm, ?_⟩
  intro dticks
  c0_hsteps_nogrp
  -- Join 1: after `if (!initial)` header-limit update
  refine wp_join_state0 (α := FullState)
    (fun s0 m0 => FullSparseInv c F0 s0 ∧ s0.core.cur_level = 0 ∧
      s0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s0 ⋆ R) m0)
    (fun _ s0 m0 ⟨hinv0, hcl0', hfu0, hm0⟩ => by
      c0_hsteps_nogrp
      -- Join 2: after first optional `full_substitute`
      refine wp_join_state0 (α := FullState)
        (fun s1 m1 => FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
          s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1)
        (fun _ s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩ => by
          c0_hsteps_nogrp
          -- Join 3: `do_dense` boolean computation
          refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ())) (fun _ => True)
            (fun _ _ _ => by
              c0_hsteps_nogrp
              -- Join 4: after `if (do_dense)` block
              refine wp_join_state0 (α := FullState)
                (fun s4 m4 => FullSparseInv c F0 s4 ∧ s4.core.cur_level = 0 ∧
                  s4.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s4 ⋆ R) m4)
                (fun _ s4 m4 ⟨hinv4, hcl4, hfu4, hm4⟩ => by
                  c0_hsteps_nogrp
                  -- Join 5: after second optional `full_substitute`
                  refine wp_join_state0 (α := FullState)
                    (fun s5 m5 => FullSparseInv c F0 s5 ∧ s5.core.cur_level = 0 ∧
                      s5.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s5 ⋆ R) m5)
                    (fun _ s5 m5 ⟨hinv5, hcl5, hfu5, hm5⟩ => by
                      c0_hsteps_nogrp
                      -- Join 6: after `if (!initial && full_probe_tail(h, dticks) == 20ULL)`
                      refine wp_join_state0 (α := FullState)
                        (fun s6 m6 => FullSparseInv c F0 s6 ∧ s6.core.cur_level = 0 ∧
                          s6.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s6 ⋆ R) m6)
                        (fun _ s6 m6 ⟨hinv6, hcl6, hfu6, hm6⟩ => by
                          c0_hsteps
                          let s7 : FullState :=
                            { s6 with scratch := { s6.scratch with
                              fwd_sub_cnt := s6.scratch.search_ticks } }
                          have hinv7 : FullSparseInv c F0 s7 :=
                            fullSparseInv_with_scratch_keep hinv6 { hinv6.lengths.scratch_ok with }
                              rfl rfl
                          exact hQ 1#64 s7 _ hinv7.lengths hfu6 (Or.inl rfl) (fun h => by cases h)
                            (fun _ => ⟨hinv7, hcl6⟩) hm)
                        (fun J6 hJ6 => by
                          c0_hsplit
                          · c0_hsteps; exact hJ6 s5 m5 ⟨hinv5, hcl5, hfu5, hm5⟩
                          · c0_hsteps; c0_call hTail
                            refine ⟨c, F0, s5, R, rfl, hinv5, hcl5, hm5, ?_⟩
                            intro rt s6 m6 hinv6 hcl6 hfu6 _ hut6 hm6; c0_hsteps
                            · exact hQ 20#64 s6 m6 hinv6.lengths (by omega) (Or.inr rfl)
                                (fun _ => hut6 hc) (fun h => by cases h) hm6
                            exact hJ6 s6 m6 ⟨hinv6, hcl6, by omega, hm6⟩))
                    (fun J5 hJ5 => by
                      c0_hsplit
                      · c0_hsteps; c0_call hSubst; refine ⟨c, F0, s4, R, rfl, hinv4, hm4, ?_⟩
                        intro rs s5 m5 hinv5 hcl5 hfu5 _ hus5 hm5; c0_hsteps
                        · exact hQ 20#64 s5 m5 hinv5.lengths (by omega) (Or.inr rfl)
                            (fun _ => hus5 hc) (fun h => by cases h) hm5
                        exact hJ5 s5 m5 ⟨hinv5, hcl5, by omega, hm5⟩
                      · c0_hsteps; exact hJ5 s4 m4 ⟨hinv4, hcl4, hfu4, hm4⟩))
                (fun J4 hJ4 => by
                  c0_hsplit
                  · c0_hsteps; c0_call hCong; refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
                    intro rc s2 m2 hfu2 hrc hsp2 h20_2 hm2; c0_hsplit
                    · c0_hsteps; obtain ⟨hu2, hlen2⟩ := h20_2 hc
                      exact hQ 20#64 s2 m2 hlen2 (by omega) (Or.inr rfl) (fun _ => hu2)
                        (fun h => by cases h) hm2
                    · have hinv2 : FullSparseInv c F0 s2 := hsp2 (hrc.resolve_right hc)
                      c0_hsteps_nogrp
                      refine wp_join_state0 (α := FullState)
                        (fun s3 m3 => FullSparseInv c F0 s3 ∧
                          s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s3 ⋆ R) m3)
                        (fun _ s3 m3 ⟨hinv3, hfu3, hm3⟩ => by
                          c0_hsteps; c0_call hSweep; refine ⟨c, F0, s3, R, rfl, hinv3, hm3, ?_⟩
                          intro rw4 s4 m4 hinv4 hcl4 hfu4 _ huw4 hm4; c0_hsteps
                          · exact hQ 20#64 s4 m4 hinv4.lengths (by omega) (Or.inr rfl)
                              (fun _ => huw4 hc) (fun h => by cases h) hm4
                          exact hJ4 s4 m4 ⟨hinv4, hcl4, by omega, hm4⟩)
                        (fun J3 hJ3 => by
                          c0_hsplit
                          · c0_hsteps; c0_call hSubst; refine ⟨c, F0, s2, R, rfl, hinv2, hm2, ?_⟩
                            intro rs3 s3 m3 hinv3 _ hfu3 _ hus3 hm3; c0_hsteps
                            · exact hQ 20#64 s3 m3 hinv3.lengths (by omega) (Or.inr rfl)
                                (fun _ => hus3 hc) (fun h => by cases h) hm3
                            exact hJ3 s3 m3 ⟨hinv3, by omega, hm3⟩
                          · c0_hsteps; exact hJ3 s2 m2 ⟨hinv2, by omega, hm2⟩)
                  · c0_hsteps; exact hJ4 s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩))
            (fun Jd hJd => by c0_hsteps <;> exact hJd _ trivial))
        (fun J2 hJ2 => by
          c0_hsplit
          · c0_hsteps; c0_call hSubst; refine ⟨c, F0, s0, R, rfl, hinv0, hm0, ?_⟩
            intro rs1 s1 m1 hinv1 hcl1 hfu1 _ hus1 hm1; c0_hsteps
            · exact hQ 20#64 s1 m1 hinv1.lengths (by omega) (Or.inr rfl)
                (fun _ => hus1 hc) (fun h => by cases h) hm1
            exact hJ2 s1 m1 ⟨hinv1, hcl1, by omega, hm1⟩
          · c0_hsteps; exact hJ2 s0 m0 ⟨hinv0, hcl0', hfu0, hm0⟩))
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps; exact hJ1 s m ⟨hinv, hcl0, Nat.le_refl _, hm⟩
      · c0_hsteps
        let s0a : FullState :=
          { s with scratch := { s.scratch with probings := s.scratch.probings + 1#64 } }
        have hlen0a : s0a.LengthsOk c :=
          ⟨hinv.lengths.core_ok, { hinv.lengths.scratch_ok with }⟩
        c0_call hIlog; intro logp _ _
        c0_hsteps; c0_call hScale; refine ⟨c, s0a, R, rfl, hlen0a, hm, ?_⟩
        intro delta
        c0_hsteps
        let s0b : FullState :=
          { s0a with scratch := { s0a.scratch with probe_limit := s0a.scratch.conflicts + delta } }
        have hinv0b : FullSparseInv c F0 s0b :=
          fullSparseInv_with_scratch_keep hinv { hinv.lengths.scratch_ok with } rfl rfl
        exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩)

theorem sched_elim_bve_wp (Γ : Env)
    (hBve : ∀ a m Q X, fullBveVarSpec a m Q X → Γ "full_bve_var" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, schedElimBveSpec a m Q X → Func.wp Γ full_elim_bve_body a m Q X := by
  rintro ⟨h, bve_lim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hden0, hm, hQ⟩
  let cv : Nat := s.core.cur_vars
  have hcv_le_max : cv ≤ c.max_vars := hden0.lengths.core_ok.cur_vars_le
  have hmax_lt32 : c.max_vars < 2 ^ 32 := fullInv_max_vars_lt32 c
  have hcv_lt64 : cv < 2 ^ 64 := by omega
  unfold Func.wp full_elim_bve_body
  c0_hsteps_nogrp
  refine wp_while_break_state
    (α := BitVec 64 × BitVec 64 × FullState)
    (β := BitVec 64 × BitVec 64 × BitVec 64 × FullState)
    (fun p => (p.1, p.2.1, p.2.2.1, ()))
    (fun p mb => FullDenseInv c F0 p.2.2.2 ∧ p.2.2.2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (p.2.2.1 = 1#64 ∨ p.2.2.1 = 20#64) ∧ (p.2.2.1 = 20#64 → F0.Unsat) ∧
      (FullMem c p.2.2.2 ⋆ R) mb)
    (fun p => (p.1, p.2.1, ()))
    (fun p => cv - p.1.toNat)
    (fun p ml => p.1.toNat ≤ cv ∧ cv ≤ p.2.2.core.cur_vars ∧ FullDenseInv c F0 p.2.2 ∧
      p.2.2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c p.2.2 ⋆ R) ml)
    ?_ ?_ ?_
  · rintro _ ⟨_, _, res, sb⟩ mb ⟨hdenb, hfub, hrdom, hru, hmb⟩
    c0_hsteps; exact hQ res sb mb hdenb hfub hrdom hru hmb
  · rintro B L ⟨v_bv, tried, st⟩ ml hB hL ⟨hv_le, hcv_le, hden_t, hfu_t, hml⟩
    dsimp only at hv_le hcv_le hden_t hfu_t hml
    c0_hsplit
    · have hv_lt_cv : v_bv.toNat < cv := by
        have : v_bv.toNat < s.core.cur_vars % 2 ^ 64 := by assumption
        rw [Nat.mod_eq_of_lt hcv_lt64] at this; exact this
      have hv_lt_fl : v_bv.toNat < st.core.flags.length := by
        rw [hden_t.lengths.core_ok.flags_len]; omega
      have h2v_lt_vals : (v_bv <<< (1 : Nat)).toNat < st.core.vals.length := by
        rw [hden_t.lengths.core_ok.vals_len, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      have hv_next_toNat : (v_bv + 1#64).toNat = v_bv.toNat + 1 := by bv_omega
      c0_hsplit
      · c0_hsplit
        · c0_hsplit
          · c0_hsteps
            · let st' : FullState :=
                { st with core :=
                  { st.core with
                    flags := st.core.flags.set v_bv.toNat
                      (st.core.flags[v_bv.toNat] &&& ~~~16#32) } }
              have hden_t' : FullDenseInv c F0 st' :=
                fullDenseInv_with_flags hden_t (by simp [hden_t.lengths.core_ok.flags_len])
              have hfu_t' : st'.core.fuel = st.core.fuel := rfl
              have hcv_t' : st'.core.cur_vars = st.core.cur_vars := rfl
              have hv32 : (v_bv.setWidth 32).toNat < st'.core.cur_vars := by
                have : (v_bv.setWidth 32).toNat = v_bv.toNat := by bv_omega
                rw [hcv_t']; omega
              c0_call hBve; refine ⟨c, F0, st', R, rfl, hden_t', hv32, hm, ?_⟩
              intro br sb mb hden_b hcv_b hfu_b _ hub hmb
              rw [hfu_t'] at hfu_b; rw [hcv_t'] at hcv_b
              c0_hsteps
              · exact hB (v_bv, tried + 1#64, 20#64, sb) mb
                  ⟨hden_b, by dsimp only; omega, Or.inr rfl, (fun _ => hub hc), hmb⟩
              · exact hB (v_bv, tried + 1#64, 1#64, sb) mb
                  ⟨hden_b, by dsimp only; omega, Or.inl rfl, (fun h => by cases h), hmb⟩
              · exact hL (v_bv + 1#64, tried + 1#64, sb) mb
                  (by dsimp only; rw [hv_next_toNat]; omega)
                  ⟨by dsimp only; rw [hv_next_toNat]; omega, Nat.le_trans hcv_le hcv_b,
                    hden_b, by dsimp only; omega, hmb⟩
            · exact hL (v_bv + 1#64, tried, st) ml (by dsimp only; rw [hv_next_toNat]; omega)
                ⟨by dsimp only; rw [hv_next_toNat]; omega, hcv_le, hden_t, hfu_t, hml⟩
            · exact hL (v_bv + 1#64, tried, st) ml (by dsimp only; rw [hv_next_toNat]; omega)
                ⟨by dsimp only; rw [hv_next_toNat]; omega, hcv_le, hden_t, hfu_t, hml⟩
          · c0_hsteps
            exact hB (v_bv, tried, 1#64, st) ml
              ⟨hden_t, hfu_t, Or.inl rfl, (fun h => by cases h), hml⟩
        · c0_hsteps
          exact hB (v_bv, tried, 1#64, st) ml
            ⟨hden_t, hfu_t, Or.inl rfl, (fun h => by cases h), hml⟩
      · c0_hsteps
        exact hB (v_bv, tried, 1#64, st) ml
          ⟨hden_t, hfu_t, Or.inl rfl, (fun h => by cases h), hml⟩
    · c0_hsteps
      exact hB (v_bv, tried, 1#64, st) ml
        ⟨hden_t, hfu_t, Or.inl rfl, (fun h => by cases h), hml⟩
  · intro _ L _ hL; c0_hsteps
    exact hL (0#64, 0#64, s) m ⟨Nat.zero_le _, Nat.le_refl _, hden0, Nat.le_refl _, hm⟩

theorem sched_eliminate_wp (Γ : Env)
    (hDticks : ∀ a m Q X, schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hFwd : ∀ a m Q X, fullForwardSubSpec a m Q X → Γ "full_forward_sub" [i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X → Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, schedElimBveSpec a m Q X → Γ "full_elim_bve" [i64, i64] [i64] a m Q X)
    (hFact : ∀ a m Q X, fullFactorSpec a m Q X → Γ "full_factor" [i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, schedEliminateSpec a m Q X → Func.wp Γ full_eliminate_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_eliminate_body
  c0_hsteps; c0_call hDticks; refine ⟨c, s, R, rfl, hinv.lengths, hm, ?_⟩
  intro dticks
  c0_hsteps_nogrp
  -- Join 1: after `if (!initial)` limit/bound update
  refine wp_join_state0 (α := FullState)
    (fun s0 m0 => FullSparseInv c F0 s0 ∧ s0.core.cur_level = 0 ∧
      s0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s0 ⋆ R) m0)
    (fun _ s0 m0 ⟨hinv0, _, hfu0, hm0⟩ => by
      c0_hsteps; c0_call hEnter; refine ⟨c, F0, s0, R, rfl, hinv0, hm0, ?_⟩
      intro ok s1 m1 hcl1 hfu1 hok_d hfail_s hm1
      c0_hsplit
      · -- `enter_dense` succeeded (`ok = true`)
        have hden1 : FullDenseInv c F0 s1 := hok_d hc
        c0_hsteps; c0_call hFwd; refine ⟨c, F0, s1, R, rfl, hden1, hm1, ?_⟩
        intro fs s2 m2 hden2 _ hfu2 _ huf2 hm2
        let s2r : FullState :=
          { s2 with scratch := { s2.scratch with fwd_sub_cnt := s1.scratch.fwd_sub_cnt } }
        have hden2r : FullDenseInv c F0 s2r :=
          fullDenseInv_with_scratch_keep hden2 { hden2.lengths.scratch_ok with } rfl rfl
        have hfu2r : s2r.core.fuel.toNat ≤ s.core.fuel.toNat := by
          change s2.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hfu2]; omega
        c0_hsplit
        · c0_hsteps; c0_call hReb; refine ⟨c, F0, s2r, R, rfl, hden2r, hm, ?_⟩
          intro _ s3 m3 hsp3 hcl3 hfu3 _ _ hm3; c0_hsteps
          exact hQ 20#64 s3 m3 hsp3 hcl3 (by omega) (Or.inr rfl) (fun _ => huf2 hc) hm3
        · c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
            (fun b => (b, ())) (fun _ => True)
            (fun _ _ _ => by
              c0_hsteps; c0_call hMin; intro bve_lim _
              c0_hsteps; c0_call hBve; refine ⟨c, F0, s2r, R, rfl, hden2r, hm, ?_⟩
              intro res s3 m3 hden3 hfu3 hres_dom hres_u hm3
              c0_hsteps_nogrp
              -- Join after optional `full_factor`
              refine wp_join_state0 (α := FullState)
                (fun sf mf => FullDenseInv c F0 sf ∧ sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  (FullMem c sf ⋆ R) mf)
                (fun _ sf mf ⟨hdenf, hfuf, hmf⟩ => by
                  c0_hsteps; c0_call hReb; refine ⟨c, F0, sf, R, rfl, hdenf, hmf, ?_⟩
                  intro rr se me hspe hcle hfue _ hue hme
                  let se' : FullState :=
                    { se with scratch :=
                      { se.scratch with fwd_str_cnt := se.scratch.search_ticks } }
                  have hspe' : FullSparseInv c F0 se' :=
                    fullSparseInv_with_scratch_keep hspe { hspe.lengths.scratch_ok with } rfl rfl
                  have hfue' : se'.core.fuel.toNat ≤ s.core.fuel.toNat := by
                    change se.core.fuel.toNat ≤ s.core.fuel.toNat; omega
                  c0_hsteps
                  · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl) (fun _ => hres_u hc) hm
                  · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl) (fun _ => hue hc) hm
                  · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                      (fun _ => hspe'.inconsistent_unsat hc) hm
                  · exact hQ 1#64 se' _ hspe' hcle hfue' (Or.inl rfl) (fun h => by cases h) hm)
                (fun Jf hJf => by
                  c0_hsplit
                  · c0_hsteps_nogrp
                    refine wp_join_state0 (α := FullState)
                      (fun sg mg => FullDenseInv c F0 sg ∧ sg.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullMem c sg ⋆ R) mg)
                      (fun _ sg mg ⟨hdeng, hfug, hmg⟩ => by
                        c0_hsteps; c0_call hFact; refine ⟨c, F0, sg, R, rfl, hdeng, hmg, ?_⟩
                        intro _ sf mf hdenf _ hfuf _ hmf; c0_hsteps
                        exact hJf sf mf ⟨hdenf, by rw [hfuf]; omega, hmf⟩)
                      (fun Jdo hJdo => by
                        c0_hsteps
                        · exact hJdo s3 m3 ⟨hden3, by omega, hm3⟩
                        · exact hJdo s3 m3 ⟨hden3, by omega, hm3⟩
                        · exact hJf s3 m3 ⟨hden3, by omega, hm3⟩)
                  · c0_hsteps; exact hJf s3 m3 ⟨hden3, by omega, hm3⟩))
            (fun Jb hJb => by c0_hsteps <;> exact hJb _ trivial)
      · -- `enter_dense` failed (`ok = false`)
        have hsp1 : FullSparseInv c F0 s1 := hfail_s hc
        let s1' : FullState :=
          { s1 with scratch := { s1.scratch with fwd_str_cnt := s1.scratch.search_ticks } }
        have hsp1' : FullSparseInv c F0 s1' :=
          fullSparseInv_with_scratch_keep hsp1 { hsp1.lengths.scratch_ok with } rfl rfl
        have hfu1' : s1'.core.fuel.toNat ≤ s.core.fuel.toNat := by
          change s1.core.fuel.toNat ≤ s.core.fuel.toNat; omega
        c0_hsteps
        · exact hQ 20#64 s1' _ hsp1' hcl1 hfu1' (Or.inr rfl)
            (fun _ => hsp1'.inconsistent_unsat hc) hm
        · exact hQ 1#64 s1' _ hsp1' hcl1 hfu1' (Or.inl rfl) (fun h => by cases h) hm)
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps; exact hJ1 s m ⟨hinv, hcl0, Nat.le_refl _, hm⟩
      · c0_hsteps
        let s0a : FullState :=
          { s with scratch := { s.scratch with eliminations := s.scratch.eliminations + 1#64 } }
        have hlen0a : s0a.LengthsOk c :=
          ⟨hinv.lengths.core_ok, { hinv.lengths.scratch_ok with }⟩
        c0_call hIlog; intro loge _ _
        c0_hsteps; c0_call hScale; refine ⟨c, s0a, R, rfl, hlen0a, hm, ?_⟩
        intro delta
        let s0b : FullState :=
          { s0a with scratch := { s0a.scratch with elim_limit := s0a.scratch.conflicts + delta } }
        have hinv0b : FullSparseInv c F0 s0b :=
          fullSparseInv_with_scratch_keep hinv { hinv.lengths.scratch_ok with } rfl rfl
        let s0c : FullState :=
          { s0b with scratch :=
            { s0b.scratch with elim_bound := s0b.scratch.elim_bound + 2#64 } }
        have hinv0c : FullSparseInv c F0 s0c :=
          fullSparseInv_with_scratch_keep hinv0b { hinv0b.lengths.scratch_ok with } rfl rfl
        c0_hsteps
        · exact hJ1 s0c _ ⟨hinv0c, hcl0, Nat.le_refl _, hm⟩
        · exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩
        · exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩)

/-- `Func.wp` proof for upgraded `full_preprocess` against exact canonical
`Full.fullPreprocessSpec` (adds unflushed sweep + scale_delta limits + 3-SAT fast-path skip). -/
theorem sched_preprocess_wp (Γ : Env)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, schedProbeSpec a m Q X → Γ "full_probe" [i64, .bool] [i64] a m Q X)
    (hElim : ∀ a m Q X, schedEliminateSpec a m Q X →
      Γ "full_eliminate" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullPreprocessSpec a m Q X → Func.wp Γ full_preprocess_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  obtain ⟨F_cur, hspW⟩ := hinv.exists_witness
  unfold Func.wp full_preprocess_body
  c0_hsteps; c0_call hProp
  refine ⟨c, F0, F_cur, s, R, rfl, hspW.1, hspW.2.1, hspW.2.2.2.2.2, hm, ?_⟩
  intro pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 s1
    hlen1 hw1 _ hperm1 hfu1 _ _ hpr1 _ _ hm1
  have hspW1 : FullSparseInvW c F0 F_cur s1 :=
    fullSparseInvW_of_perm hspW hlen1 hw1 hperm1 rfl rfl rfl ⟨rfl, rfl⟩
  have hcl1 : s1.core.cur_level = 0 := hcl0
  c0_hsplit
  · c0_hsteps
    exact hQ 20#64 s1 m1 hlen1 (Or.inr (Or.inr (Or.inr rfl))) hfu1
      (fun _ => level0_unsat_of_conflict_okW (s := s1) hw1 hcl1 (hpr1 hc).2.2)
      (fun h => by cases h) (fun h => by cases h) hm1
  c0_hsplit
  · c0_hsteps
    exact hQ 0#64 s1 m1 hlen1 (Or.inl rfl) hfu1 (fun h => by cases h) (fun h => by cases h)
      (fun h => by cases h) hm1
  c0_hsplit
  · c0_hsteps
    exact hQ 0#64 s1 m1 hlen1 (Or.inl rfl) hfu1 (fun h => by cases h) (fun h => by cases h)
      (fun h => by cases h) hm1
  -- Join after `if (h->unflushed > 0ULL)`
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s2 m2 => FullSparseInv c F0 s2 ∧ s2.core.cur_level = 0 ∧
      s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s2 ⋆ R) m2)
    (fun _ s2 m2 ⟨hinv2, hcl2, hfu2, hm2⟩ => by
      c0_hsplit
      · c0_hsteps
        exact hQ 10#64 s2 m2 hinv2.lengths (Or.inr (Or.inr (Or.inl rfl))) hfu2
          (fun h => by cases h) (fun h => by cases h) (fun _ => hinv2.2.2.2.1.2) hm2
      c0_hsteps; c0_call hScale; refine ⟨c, s2, R, rfl, hinv2.lengths, hm2, ?_⟩
      intro plim
      c0_hsteps
      let s2a : FullState := { s2 with scratch := { s2.scratch with probe_limit := plim } }
      have hinv2a : FullSparseInv c F0 s2a :=
        fullSparseInv_with_scratch_keep hinv2 { hinv2.lengths.scratch_ok with } rfl rfl
      c0_call hScale; refine ⟨c, s2a, R, rfl, hinv2a.lengths, hm, ?_⟩
      intro elim
      c0_hsteps_nogrp
      let s2b : FullState := { s2a with scratch := { s2a.scratch with elim_limit := elim } }
      have hinv2b : FullSparseInv c F0 s2b :=
        fullSparseInv_with_scratch_keep hinv2a { hinv2a.lengths.scratch_ok with } rfl rfl
      -- Join after 3-SAT fast-path skip
      refine wp_join_state0 (α := FullState)
        (fun s2c m2c => FullSparseInv c F0 s2c ∧ s2c.core.cur_level = 0 ∧
          s2c.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s2c ⋆ R) m2c)
        (fun _ s2c m2c ⟨hinv2c, hcl2c, hfu2c, hm2c⟩ => by
          c0_hsteps; c0_call hProbe; refine ⟨c, F0, s2c, R, rfl, hinv2c, hcl2c, hm2c, ?_⟩
          intro rp s3 m3 hlen3 hfu3 hrp_dom hup3 hsp3 hm3; c0_hsteps
          · exact hQ 20#64 s3 m3 hlen3 (Or.inr (Or.inr (Or.inr rfl))) (by omega)
              (fun _ => hup3 hc) (fun h => by cases h) (fun h => by cases h) hm3
          · exact hQ 0#64 s3 m3 hlen3 (Or.inl rfl) (by omega) (fun h => by cases h)
              (fun h => by cases h) (fun h => by cases h) hm3
          · exact hQ 0#64 s3 m3 hlen3 (Or.inl rfl) (by omega) (fun h => by cases h)
              (fun h => by cases h) (fun h => by cases h) hm3
          obtain ⟨hinv3, hcl3⟩ := hsp3 (hrp_dom.resolve_right (by assumption))
          c0_call hElim; refine ⟨c, F0, s3, R, rfl, hinv3, hcl3, hm3, ?_⟩
          intro re s4 m4 hinv4 hcl4 hfu4 _ hue4 hm4; c0_hsteps
          · exact hQ 20#64 s4 m4 hinv4.lengths (Or.inr (Or.inr (Or.inr rfl))) (by omega)
              (fun _ => hue4 hc) (fun h => by cases h) (fun h => by cases h) hm4
          · exact hQ 20#64 s4 m4 hinv4.lengths (Or.inr (Or.inr (Or.inr rfl))) (by omega)
              (fun _ => hinv4.inconsistent_unsat hc) (fun h => by cases h) (fun h => by cases h) hm4
          · exact hQ 0#64 s4 m4 hinv4.lengths (Or.inl rfl) (by omega) (fun h => by cases h)
              (fun h => by cases h) (fun h => by cases h) hm4
          · exact hQ 10#64 s4 m4 hinv4.lengths (Or.inr (Or.inr (Or.inl rfl))) (by omega)
              (fun h => by cases h) (fun h => by cases h) (fun _ => hinv4.2.2.2.1.2) hm4
          c0_call hScale; refine ⟨c, s4, R, rfl, hinv4.lengths, hm4, ?_⟩
          intro plim2
          c0_hsteps
          let s4a : FullState := { s4 with scratch := { s4.scratch with probe_limit := plim2 } }
          have hinv4a : FullSparseInv c F0 s4a :=
            fullSparseInv_with_scratch_keep hinv4 { hinv4.lengths.scratch_ok with } rfl rfl
          c0_call hScale; refine ⟨c, s4a, R, rfl, hinv4a.lengths, hm, ?_⟩
          intro elim2
          c0_hsteps
          let s4b : FullState := { s4a with scratch := { s4a.scratch with elim_limit := elim2 } }
          have hinv4b : FullSparseInv c F0 s4b :=
            fullSparseInv_with_scratch_keep hinv4a { hinv4a.lengths.scratch_ok with } rfl rfl
          exact hQ 1#64 s4b _ hinv4b.lengths (Or.inr (Or.inl rfl))
            (by change s4.core.fuel.toNat ≤ s.core.fuel.toNat; omega)
            (fun h => by cases h) (fun _ => ⟨hinv4b, hcl4⟩) (fun h => by cases h) hm)
        (fun Jsk hJsk => by
          c0_hsteps
          · exact hQ 1#64 s2b _ hinv2b.lengths (Or.inr (Or.inl rfl)) hfu2
              (fun h => by cases h) (fun _ => ⟨hinv2b, hcl2⟩) (fun h => by cases h) hm
          · exact hJsk s2b _ ⟨hinv2b, hcl2, hfu2, hm⟩
          · exact hJsk s2b _ ⟨hinv2b, hcl2, hfu2, hm⟩
          · exact hJsk s2b _ ⟨hinv2b, hcl2, hfu2, hm⟩))
    (fun Ju hJu => by
      c0_hsplit
      · c0_hsteps; c0_call hSweep
        refine ⟨c, F0, F_cur, s1, R, rfl, hspW1.1, hspW1.2.1, hspW1.2.2.2.1, hspW1.2.2.2.2.2,
          fun hpos => by omega, hm1, ?_⟩
        intro sr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sc1a m1a s1a
          hlen1a _ hext1a _ hll1a hw1a hnd1a _ _ _ hsr2 _ hm1a
        have hspW1a := fullSparseInvW_after_sweep hspW1 hlen1a hw1a hnd1a hll1a hext1a rfl rfl rfl
        have hcl1a : s1a.core.cur_level = 0 := hcl1
        c0_hsteps
        · exact hQ 20#64 s1a m1a hlen1a (Or.inr (Or.inr (Or.inr rfl))) hfu1
            (fun _ => (hsr2 hc).2) (fun h => by cases h) (fun h => by cases h) hm1a
        c0_call hProp
        refine ⟨c, F0, F_cur, s1a, R, rfl, hspW1a.1, hspW1a.2.1, hspW1a.2.2.2.2.2, hm1a, ?_⟩
        intro pr1b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel1b _ _ _ _ _ _ _ _ m1b s1b
          hlen1b hw1b _ hperm1b hfl1b _ _ hpr1b_1 _ _ hm1b
        have hspW1b := fullSparseInvW_of_perm hspW1a hlen1b hw1b hperm1b rfl rfl rfl ⟨rfl, rfl⟩
        have hfu1b : s1b.core.fuel.toNat ≤ s.core.fuel.toNat := by
          have h1 : s1a.core.fuel.toNat ≤ s.core.fuel.toNat := hfu1
          dsimp only [s1b]; omega
        c0_hsteps
        · exact hQ 20#64 s1b m1b hlen1b (Or.inr (Or.inr (Or.inr rfl))) hfu1b
            (fun _ => level0_unsat_of_conflict_okW (s := s1b) hw1b hcl1a (hpr1b_1 hc).2.2)
            (fun h => by cases h) (fun h => by cases h) hm1b
        have hspW1c := fullSparseInvW_with_unflushed hspW1b 0#64
        exact hJu _ _ ⟨hspW1c.toSparse, hcl1a, hfu1b, hm⟩
      · c0_hsteps; exact hJu s1 m1 ⟨hspW1.toSparse, hcl1, hfu1, hm1⟩)

theorem sched_simplify_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hRed : ∀ a m Q X, fullReduceSpec a m Q X → Γ "full_reduce" [i64, .bool] [i64] a m Q X)
    (hProbe : ∀ a m Q X, schedProbeSpec a m Q X → Γ "full_probe" [i64, .bool] [i64] a m Q X)
    (hElim : ∀ a m Q X, schedEliminateSpec a m Q X →
      Γ "full_eliminate" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, schedSimplifySpec a m Q X → Func.wp Γ full_simplify_body a m Q X := by
  rintro ⟨h, do_probe, do_elim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  obtain ⟨F_cur0, hw0⟩ := hinv.exists_witness
  have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
    have := hw0.2.1.cur_level_le; have := hinv.lengths.core_ok.trail_end_le
    have := hinv.lengths.core_ok.cur_vars_le; have := fullInv_max_vars_lt32 c; omega
  unfold Func.wp full_simplify_body
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s0 m0 => FullSparseInv c F0 s0 ∧ s0.core.cur_level = 0 ∧
      s0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s0 ⋆ R) m0)
    (fun _ s0 m0 ⟨hinv0, hcl0, hfu0, hm0⟩ => by
      obtain ⟨F_cur1, hspW0⟩ := hinv0.exists_witness
      c0_hsteps; c0_call hRed; refine ⟨c, F0, F_cur1, s0, R, rfl, hspW0, hm0, ?_⟩
      intro r1 s1 m1 hspW1 _ hcl1_le hfu1 _ _ _ _ hur1 _ _ hm1
      have hcl1 : s1.core.cur_level = 0 := by omega
      have hfu1' : s1.core.fuel.toNat ≤ s.core.fuel.toNat := by omega
      c0_hsplit
      · c0_hsteps
        exact hQ 20#64 s1 m1 hspW1.1 hfu1' (Or.inr (Or.inr rfl))
          (fun _ => hur1 hc) (fun h => by cases h) hm1
      c0_hsteps_nogrp
      -- Join after optional `full_probe(h, false)`
      refine wp_join_state0 (α := FullState)
        (fun s2 m2 => FullSparseInv c F0 s2 ∧ s2.core.cur_level = 0 ∧
          s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s2 ⋆ R) m2)
        (fun _ s2 m2 ⟨hinv2, hcl2, hfu2, hm2⟩ => by
          c0_hsplit
          · c0_hsteps
            exact hQ 0#64 s2 m2 hinv2.lengths hfu2 (Or.inl rfl)
              (fun h => by cases h) (fun h => by cases h) hm2
          c0_hsplit
          · c0_hsteps
            exact hQ 0#64 s2 m2 hinv2.lengths hfu2 (Or.inl rfl)
              (fun h => by cases h) (fun h => by cases h) hm2
          c0_hsteps_nogrp
          -- Join after optional `full_eliminate(h, false)`
          refine wp_join_state0 (α := FullState)
            (fun s3 m3 => FullSparseInv c F0 s3 ∧ s3.core.cur_level = 0 ∧
              s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s3 ⋆ R) m3)
            (fun _ s3 m3 ⟨hinv3, hcl3, hfu3, hm3⟩ => by
              c0_hsteps
              · exact hQ 20#64 s3 m3 hinv3.lengths hfu3 (Or.inr (Or.inr rfl))
                  (fun _ => hinv3.inconsistent_unsat hc) (fun h => by cases h) hm3
              · exact hQ 0#64 s3 m3 hinv3.lengths hfu3 (Or.inl rfl)
                  (fun h => by cases h) (fun h => by cases h) hm3
              · exact hQ 1#64 s3 m3 hinv3.lengths hfu3 (Or.inr (Or.inl rfl))
                  (fun h => by cases h) (fun _ => ⟨hinv3, hcl3⟩) hm3)
            (fun Je hJe => by
              c0_hsplit
              · c0_hsteps; c0_call hElim; refine ⟨c, F0, s2, R, rfl, hinv2, hcl2, hm2, ?_⟩
                intro re s3 m3 hinv3 hcl3 hfu3 _ hue3 hm3; c0_hsteps
                · exact hQ 20#64 s3 m3 hinv3.lengths (by omega) (Or.inr (Or.inr rfl))
                    (fun _ => hue3 hc) (fun h => by cases h) hm3
                exact hJe s3 m3 ⟨hinv3, hcl3, by omega, hm3⟩
              · c0_hsteps; exact hJe s2 m2 ⟨hinv2, hcl2, hfu2, hm2⟩))
        (fun Jp hJp => by
          c0_hsplit
          · c0_hsteps; c0_call hProbe; refine ⟨c, F0, s1, R, rfl, hspW1.toSparse, hcl1, hm1, ?_⟩
            intro rp s2 m2 hlen2 hfu2 hrp_dom hup2 hsp2 hm2; c0_hsteps
            · exact hQ 20#64 s2 m2 hlen2 (by omega) (Or.inr (Or.inr rfl))
                (fun _ => hup2 hc) (fun h => by cases h) hm2
            obtain ⟨hinv2, hcl2⟩ := hsp2 (hrp_dom.resolve_right hc)
            exact hJp s2 m2 ⟨hinv2, hcl2, by omega, hm2⟩
          · c0_hsteps; exact hJp s1 m1 ⟨hspW1.toSparse, hcl1, hfu1', hm1⟩))
    (fun Jbt hJbt => by
      c0_hsplit
      · c0_hsteps; c0_call hBt
        refine ⟨c, s, R, rfl, hinv.lengths, hcl_lt64, fun _ => by
          have := hw0.2.1.cur_level_le; have := hinv.lengths.core_ok.trail_end_le
          have := hinv.lengths.core_ok.cur_vars_le; omega,
          hw0.2.1.trail_lits_lt, hm, ?_⟩
        intro _ _ _ _ _ _ _ cl1 _ sc1 m1 s1 hlen1 _ _ hcl1 hprsc1 _ _ _ hw_le _ hm1
        have hw1 := hw_le F0 F_cur0 hw0.2.1 (Nat.zero_le _)
        have hl01 : s1.core.cur_level = 0 := by dsimp only [s1]; rw [hcl1]; simp
        have hsp1 := fullSparseInv_after_backtrack0 hw0 hlen1 hw1 hprsc1.1 rfl rfl rfl rfl rfl
        c0_hsteps; exact hJbt s1 m1 ⟨hsp1.toSparse, hl01, Nat.le_refl _, hm1⟩
      · have hcl0 : s.core.cur_level = 0 := by
          have : ¬ 0 < s.core.cur_level % 2 ^ 64 := by assumption
          rw [Nat.mod_eq_of_lt hcl_lt64] at this; omega
        c0_hsteps; exact hJbt s m ⟨hinv, hcl0, Nat.le_refl _, hm⟩)

/-- `Func.wp` proof for upgraded `full_search` against exact canonical `Full.fullSearchSpec`
(passes separate `due_p`/`due_e` flags to `full_simplify(h, due_p, due_e)`). -/
theorem sched_search_wp (Γ : Env)
    (hLucky : ∀ a m Q X, fullLuckySpec a m Q X → Γ "full_lucky" [i64] [i64] a m Q X)
    (hWarm : ∀ a m Q X, fullWarmupSpec a m Q X → Γ "full_warmup" [i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hAna : ∀ a m Q X, fullAnalyzeSpec a m Q X → Γ "full_analyze" [i64] [i64] a m Q X)
    (hSw : ∀ a m Q X, fullSwitchModeSpec a m Q X → Γ "full_switch_mode" [i64] [] a m Q X)
    (hReph : ∀ a m Q X, fullRephaseSpec a m Q X → Γ "full_rephase" [i64] [] a m Q X)
    (hRed : ∀ a m Q X, fullReduceSpec a m Q X → Γ "full_reduce" [i64, .bool] [i64] a m Q X)
    (hSimp : ∀ a m Q X, schedSimplifySpec a m Q X →
      Γ "full_simplify" [i64, .bool, .bool] [i64] a m Q X)
    (hRdue : ∀ a m Q X, fullRestartDueSpec a m Q X → Γ "full_restart_due" [i64] [i64] a m Q X)
    (hRst : ∀ a m Q X, fullRestartSpec a m Q X → Γ "full_restart" [i64] [] a m Q X)
    (hDec : ∀ a m Q X, fullDecideSpec a m Q X → Γ "full_decide" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullSearchSpec a m Q X → Func.wp Γ full_search_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_search_body
  c0_hsteps; c0_call hLucky; refine ⟨c, F0, s, R, rfl, hinv, hcl0, hm, ?_⟩
  intro lk s1 m1 hlen1 hlk_dom _ _ hulk hsp1 hext1 hm1; c0_hsteps
  · rw [hc]; exact hQ 20#64 s1 m1 hlen1 (Or.inr (Or.inr rfl)) (fun _ => hulk hc)
      (fun h => by cases h) hm1
  · rw [hc]; exact hQ 10#64 s1 m1 hlen1 (Or.inr (Or.inl rfl)) (fun h => by cases h)
      (fun _ => hext1 hc) hm1
  have hlk02 : lk = 0#64 ∨ lk = 2#64 := by
    rcases hlk_dom with h0 | h2 | h10 | h20
    · exact Or.inl h0
    · exact Or.inr h2
    · exact absurd h10 hc
    · exact absurd h20 (by assumption)
  have hinv1 : FullSparseInv c F0 s1 := (hsp1 hlk02).1
  c0_call hWarm; refine ⟨c, F0, s1, R, rfl, hinv1.1, hinv1.2.2.2.2, hm1, ?_⟩
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 s2
    hcore2 hperm2 _ hpres2 _ hm2
  have hinv2 : FullSparseInv c F0 s2 :=
    fullSparseInv_of_perm_core hinv1 hcore2 hperm2 rfl rfl rfl hpres2
  c0_hsteps_nogrp
  refine wp_while_state0 (α := FullState) schedSearchVariant
    (fun st ml => FullSparseInv c F0 st ∧ (FullMem c st ⋆ R) ml)
    (fun _ hL => by c0_hsteps; exact hL s2 m2 ⟨hinv2, hm2⟩)
    (fun _ st ml ⟨hst, hml⟩ ih => ?_)
  c0_hsplit
  rotate_left; · cases hc
  c0_hsteps
  · exact hQ 0#64 st ml hst.lengths (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hml
  · exact hQ 0#64 st ml hst.lengths (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hml
  obtain ⟨F_cur, hspW⟩ := hst.exists_witness
  c0_call hProp; refine ⟨c, F0, F_cur, st, R, rfl, hspW.1, hspW.2.1, hspW.2.2.2.2.2, hml, ?_⟩
  intro pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s3
    hlen3 hw3 _ hperm3 hfu3 hpr_dom hpr0 hpr1 _ _ hm3
  have hspW3 : FullSparseInvW c F0 F_cur s3 :=
    fullSparseInvW_of_perm hspW hlen3 hw3 hperm3 rfl rfl rfl ⟨rfl, rfl⟩
  c0_hsteps
  · exact hQ 0#64 s3 m3 hlen3 (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm3
  · -- Conflict branch (`pr == 1ULL`)
    obtain ⟨hfu3_lt, _, hconf3⟩ := hpr1 hc
    c0_call hAna; refine ⟨c, F0, F_cur, s3, R, rfl, hspW3, hconf3, hm3, ?_⟩
    intro ast s4 m4 hlen4 _ _ hfu4 _ hua4 _ hsp4 hm4; c0_hsteps
    · exact hQ 20#64 s4 m4 hlen4 (Or.inr (Or.inr rfl)) (fun _ => hua4 hc)
        (fun h => by cases h) hm4
    · exact hQ 0#64 s4 m4 hlen4 (Or.inl rfl) (fun h => by cases h)
        (fun h => by cases h) hm4
    have hinv4 : FullSparseInv c F0 s4 := (hsp4 hc).1.toSparse
    c0_call hSw; refine ⟨c, s4, R, rfl, hinv4.lengths, hm4, ?_⟩
    intro ⟨⟩ s5 m5 hcore5 hlen5 hpres5 hm5
    dsimp only [fullSafetySlice, SafetySlice.ofMask] at hm5
    have hinv5 : FullSparseInv c F0 s5 := hinv4.of_safetySlice hlen5 hcore5 hpres5.1
    have hfu5 : s5.core.fuel.toNat < st.core.fuel.toNat := by
      have heq : s5.core = s4.core := fullCoreState_agrees_with_scratch hcore5
      rw [heq]; change s4.core.fuel.toNat < st.core.fuel.toNat; dsimp only [s3] at hfu4; omega
    c0_hsteps_nogrp
    -- Join 1: optional `full_rephase`
    refine wp_join_state0 (α := FullState)
      (fun s6 m6 => FullSparseInv c F0 s6 ∧ s6.core.fuel.toNat < st.core.fuel.toNat ∧
        (FullMem c s6 ⋆ R) m6)
      (fun _ s6 m6 ⟨hinv6, hfu6, hm6⟩ => by
        c0_hsteps_nogrp
        -- Join 2: optional `full_reduce(h, false)`
        refine wp_join_state0 (α := FullState)
          (fun s7 m7 => FullSparseInv c F0 s7 ∧ s7.core.fuel.toNat < st.core.fuel.toNat ∧
            (FullMem c s7 ⋆ R) m7)
          (fun _ s7 m7 ⟨hinv7, hfu7, hm7⟩ => by
            c0_hsteps_nogrp
            -- Join 3: optional `full_simplify(h, due_p, due_e)` else optional `full_restart`
            refine wp_join_state0 (α := FullState)
              (fun s8 m8 => FullSparseInv c F0 s8 ∧ s8.core.fuel.toNat < st.core.fuel.toNat ∧
                (FullMem c s8 ⋆ R) m8)
              (fun _ s8 m8 ⟨hinv8, hfu8, hm8⟩ => by
                c0_hsteps
                have hv_lt : schedSearchVariant s8 < schedSearchVariant st := by
                  unfold schedSearchVariant; split <;> split <;> omega
                exact ih s8 m8 hv_lt ⟨hinv8, hm8⟩)
              (fun Jsr hJsr => by
                c0_hsteps_nogrp
                refine wp_join_group (fun () ms => ms = m7)
                  (fun _ ⟨⟩ ms hms => by
                    subst hms; c0_hsteps
                    c0_call hSimp; refine ⟨c, F0, s7, R, rfl, hinv7, hm7, ?_⟩
                    intro sr s8 m8 hlen8 hfu8 _ hus8 hsp8 hm8; c0_hsteps
                    · exact hQ 20#64 s8 m8 hlen8 (Or.inr (Or.inr rfl)) (fun _ => hus8 hc)
                        (fun h => by cases h) hm8
                    · exact hQ 0#64 s8 m8 hlen8 (Or.inl rfl) (fun h => by cases h)
                        (fun h => by cases h) hm8
                    exact hJsr s8 m8 ⟨(hsp8 hc).1, by omega, hm8⟩)
                  (fun Jsimp hJsimp => by
                    c0_hsteps
                    · exact hJsimp () m7 rfl
                    · exact hJsimp () m7 rfl
                    · c0_call hRdue; refine ⟨c, s7, R, rfl, hinv7.lengths, hm7, ?_⟩
                      intro ⟨rd, ⟨⟩⟩ s7' m7' hcore7' hlen7' ⟨_, hpres7'⟩ hm7'
                      dsimp only [fullSafetySlice, SafetySlice.ofMask] at hm7'
                      have hinv7' : FullSparseInv c F0 s7' :=
                        hinv7.of_safetySlice hlen7' hcore7' hpres7'
                      have hfu7' : s7'.core.fuel.toNat < st.core.fuel.toNat := by
                        have heq : s7'.core = s7.core :=
                          fullCoreState_agrees_with_scratch hcore7'
                        rw [heq]; exact hfu7
                      c0_hsteps
                      · c0_call hRst; refine ⟨c, F0, s7', R, rfl, hinv7'.1, hm7', ?_⟩
                        intro _ _ _ _ _ _ _ _ _ _ m8 s8 hcore8 _ hpres8 hm8
                        have hinv8 : FullSparseInv c F0 s8 :=
                          fullSparseInv_of_same_arena hinv7' hcore8 rfl rfl rfl rfl rfl hpres8
                        c0_hsteps; exact hJsr s8 m8 ⟨hinv8, hfu7', hm8⟩
                      · exact hJsr s7' m7' ⟨hinv7', hfu7', hm7'⟩)))
          (fun Jrd hJrd => by
            c0_hsteps
            · obtain ⟨Fc6, hspW6⟩ := hinv6.exists_witness
              c0_call hRed; refine ⟨c, F0, Fc6, s6, R, rfl, hspW6, hm6, ?_⟩
              intro rr s7 m7 hspW7 _ _ hfu7 _ _ _ _ hur7 _ _ hm7; c0_hsteps
              · exact hQ 20#64 s7 m7 hspW7.1 (Or.inr (Or.inr rfl)) (fun _ => hur7 hc)
                  (fun h => by cases h) hm7
              · exact hQ 0#64 s7 m7 hspW7.1 (Or.inl rfl) (fun h => by cases h)
                  (fun h => by cases h) hm7
              exact hJrd s7 m7 ⟨hspW7.toSparse, by omega, hm7⟩
            · exact hJrd s6 m6 ⟨hinv6, hfu6, hm6⟩))
      (fun Jrp hJrp => by
        c0_hsteps
        · c0_call hReph; refine ⟨c, F0, s5, R, rfl, hinv5.1, hm5, ?_⟩
          intro _ _ _ _ _ _ _ _ _ _ m6 s6 hcore6 hfu6 hpres6 hm6
          have hinv6 : FullSparseInv c F0 s6 :=
            fullSparseInv_of_same_arena hinv5 hcore6 rfl rfl rfl rfl rfl hpres6
          c0_hsteps; exact hJrp s6 m6 ⟨hinv6, by dsimp only [s6]; omega, hm6⟩
        · exact hJrp s5 m5 ⟨hinv5, hfu5, hm5⟩)
  · -- Non-conflict branch, `unassigned == 0ULL`
    exact hQ 10#64 s3 m3 hlen3 (Or.inr (Or.inl rfl)) (fun h => by cases h)
      (fun _ => hspW3.2.2.2.2.1.2) hm3
  · -- Non-conflict branch, `unassigned ≠ 0ULL`: decide
    have hpr_eq0 : pr = 0#64 := by
      rcases hpr_dom with h0 | h1 | h2
      · exact h0
      · exact absurd h1 (by assumption)
      · exact absurd h2 (by assumption)
    obtain ⟨hprop3, _, hfu3_lt_if⟩ := hpr0 hpr_eq0
    have hinv3 : FullSparseInv c F0 s3 := hspW3.toSparse
    c0_call hDec; refine ⟨c, F0, s3, R, rfl, hinv3.1, hm3, ?_⟩
    intro dr _ _ _ _ _ _ _ _ _ _ _ _ _ m4 s4 hcore4 hpres4 hdr_dom _ hd1 hm4
    have hinv4 : FullSparseInv c F0 s4 :=
      fullSparseInv_of_same_arena hinv3 hcore4 rfl rfl rfl rfl rfl hpres4
    c0_hsteps
    · exact hQ 10#64 s4 m4 hinv4.lengths (Or.inr (Or.inl rfl)) (fun h => by cases h)
        (fun _ => hinv4.2.2.2.1.2) hm4
    · exact hQ 0#64 s4 m4 hinv4.lengths (Or.inl rfl) (fun h => by cases h)
        (fun h => by cases h) hm4
    · have hdr1 : dr = 1#64 := hdr_dom.resolve_left hc
      have hte4 : s4.core.trail_end = s3.core.trail_end + 1 := (hd1 hdr1).2
      have hv_lt : schedSearchVariant s4 < schedSearchVariant st := by
        have hfu3' : s3.core.fuel.toNat ≤ st.core.fuel.toNat := hfu3
        have hprop3' : s3.core.propagated = s3.core.trail_end := hprop3
        have hne4 : s4.core.propagated ≠ s4.core.trail_end := by
          change s3.core.propagated ≠ s4.core.trail_end; omega
        have hle_st := hst.lengths.core_ok.propagated_le
        have hfu4 : s4.core.fuel = s3.core.fuel := rfl
        unfold schedSearchVariant
        simp only [hne4, ↓reduceIte, Nat.add_zero, hfu4]
        by_cases heq_st : st.core.propagated = st.core.trail_end
        · simp only [heq_st, ↓reduceIte]; omega
        · simp only [heq_st, ↓reduceIte, Nat.add_zero]
          have hlt_f : s3.core.fuel.toNat < st.core.fuel.toNat := hfu3_lt_if (by omega)
          omega
      exact ih s4 m4 hv_lt ⟨hinv4, hm4⟩

end Orchestrators

/-! ## 6. `kissat_solve_bytes`, `SpecEntry.Impl` (`16` fns) & Concrete UNSAT Non-Vacuity -/

section TopAndNonVacuity

open scoped FullArenaTactics

private theorem sched_solve_bytes_extend_check {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {s3 : FullState} {cnf_ptr work_ptr hdr_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m3 : Mem 64}
    (hExt : ∀ a m Q X, fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64) (hw_ge : fullAlignPad work_ptr ≤ wlen)
    (hch_ptr : c.hdr = hdr_ptr)
    (hch : c.hdr = work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
    (hca : c.avail = wlen - fullAlignPad work_ptr)
    (hlen3 : s3.LengthsOk c) (hext3 : s3.scratch.extend_len ≤ c.extend_cap)
    (hm3 : (bytes cnf_ptr cnfBytes ⋆ FullMem c s3 ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m3)
    (hRet : ∀ r m', (r = 0#64 ∨ r = 10#64) →
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' → Q (r, ()) m') :
    let cnf_end := cnf_ptr + BitVec.ofNat 64 cnfBytes.length
    wp Γ Q X (Expr.call (as := [i64]) (bs := []) "full_extend" (Arg.var hdr_ptr, ()) fun _ =>
      Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var hdr_ptr, Arg.imm 64, ()) }
      fun p1 => Expr.load i64 (Arg.var p1.fst) fun ld_v =>
      Expr.load i64 (Arg.var hdr_ptr) fun ld_mv =>
      Expr.call (as := [i64, i64, i64, i64, i64]) (bs := [i64]) "kissat_check_model"
        (Arg.var cnf_ptr, Arg.var cnf_end, Arg.var hdr_ptr, Arg.var ld_v, Arg.var ld_mv, ())
      fun p2 => Expr.group (sig := [[i64]])
        (fun _ => Blocks.cons (fun p3 => Expr.ret (Arg.var p3.fst, ())) Blocks.nil)
        fun Jr => Expr.let_
          { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
            args := (Arg.var p2.fst, Arg.imm 1, ()) }
          fun p3 => Expr.jnz (Arg.var p3.fst)
            (Expr.jump Jr.fst (Arg.imm 10, ())) (Expr.jump Jr.fst (Arg.imm 0, ()))) m3 := by
  dsimp only; rw [← hch_ptr]
  c0_call hExt
  refine ⟨c, s3, bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R,
    ⟨rfl, hext3⟩, hlen3,
    by dsimp only [fullExtendSlice, SafetySlice.ofMask]; exact sep_ac hm3, ?_⟩
  intro ⟨⟩ s4 m4 _ hlen4 _ hm4
  dsimp only [fullExtendSlice, SafetySlice.ofMask] at hm4
  c0_hsteps
  have hm4_b : (bytes cnf_ptr cnfBytes ⋆ FullMem c s4 ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m4 := sep_ac hm4
  have hmv_bd := c.hmv; have hmx_bd := c.hmaxv; have hbva := c.hbva
  unfold dimacsBound at hmv_bd hmx_bd
  have hcm_mem := fullMem_to_checkModel hlen4 hm4_b
  c0_call hCheck
  refine ⟨BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc, s4.core.d_cur, s4.core.d_val,
    cnfBytes, s4.core.vals.map UInt8.ofBitVec, c.mv,
    FullCheckRest c s4 ⋆ (region work_ptr (fullAlignPad work_ptr) ⋆ R),
    rfl, rfl, hcfit, by omega,
    by simp [hlen4.core_ok.vals_len]; omega,
    by simp [hlen4.core_ok.vals_len]; omega,
    by simpa [sep_assoc] using hcm_mem, ?_⟩
  intro ok mv' nc' cur' val' m5 _ hm5
  have hm5_reg : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m5 :=
    full_merge_reg hwfit hw_ge (by
      rw [← hch, ← hca]
      exact checkModel_post_to_region hlen4 (by simpa [sep_assoc] using hm5))
  refine wp_join_state_pure (α := BitVec 64) (fun r => (r, ())) (fun r => r = 0#64 ∨ r = 10#64)
    (fun _ rv hrv => by c0_hsteps; exact hRet rv m5 hrv hm5_reg)
    (fun Jr hJr => by
      c0_hsteps
      · exact hJr 10#64 (Or.inr rfl)
      · exact hJr 0#64 (Or.inl rfl))

/-- `Func.wp` proof for `Full.kissat_solve_bytes_body` against `fullSolveBytesCoreSpec`
(UNSAT-only soundness + `UnitUnsatTrace` non-vacuity). -/
theorem sched_kissat_solve_bytes_core_wp (Γ : Env)
    (hInit : ∀ a m Q X, fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hParse : ∀ a m Q X, fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hPre : ∀ a m Q X, fullPreprocessSpec a m Q X → Γ "full_preprocess" [i64] [i64] a m Q X)
    (hSearch : ∀ a m Q X, fullSearchSpec a m Q X → Γ "full_search" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullSolveBytesCoreSpec a m Q X →
      Func.wp Γ Full.kissat_solve_bytes_body a m Q X := by
  rintro ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, ⟨⟩⟩ m Q X
    ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, hQ⟩
  unfold Func.wp Full.kissat_solve_bytes_body; wp_unfold
  refine ⟨fun hf0 => ?_, fun _ => ?_⟩
  · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h)
      (fun _ _ _ _ _ hf => by rw [hf0] at hf; simp at hf) hm
  refine ⟨fun hcp0 => ?_, fun _ => ?_⟩
  · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h)
      (fun _ _ _ hcp => absurd hcp0 hcp) hm
  refine ⟨fun hwp0 => ?_, fun _ => ?_⟩
  · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h)
      (fun _ _ _ _ hwp => absurd hwp0 hwp) hm
  have hnot0 : ~~~(0 : BitVec 64) = 0xFFFFFFFFFFFFFFFF#64 := rfl
  rw [hnot0, bv64_ugt_max_sub_false hcfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  rw [bv64_ugt_max_sub_false hwfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  let pNat : Nat := fullAlignPad work_ptr
  have hp_lt8 : pNat < 8 := fullAlignPad_lt8 work_ptr
  have hpad_ult : (BitVec.ofNat 64 wlen).ult (((8 - (work_ptr &&& 7)) &&& 7) + 1152) =
      decide (wlen < pNat + 1152) := by
    rw [fullAlignPad_bv_eq work_ptr, show (1152 : BitVec 64) = BitVec.ofNat 64 1152 from rfl,
      bv_add_ofNat, bv_ult_eq (by omega) (by omega)]
  rw [hpad_ult]; simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun hw_small => ?_, fun hw_ge_not => ?_⟩
  · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h)
      (fun mv nc _ _ _ _ hsz _ _ _ => by unfold fullFixedBytes at hsz; omega) hm
  have hw_ok : pNat + 1152 ≤ wlen := by omega
  let hdr_addr : BitVec 64 := work_ptr + BitVec.ofNat 64 pNat
  let availNat : Nat := wlen - pNat
  have hpad_bv : (8 - (work_ptr &&& 7)) &&& 7 = BitVec.ofNat 64 pNat := fullAlignPad_bv_eq work_ptr
  have hhdr_bv : work_ptr + ((8 - (work_ptr &&& 7)) &&& 7) = hdr_addr := by rw [hpad_bv]
  have hav_bv :
      BitVec.ofNat 64 wlen - ((8 - (work_ptr &&& 7)) &&& 7) = BitVec.ofNat 64 availNat := by
    rw [hpad_bv]; exact bv_sub_ofNat (by omega) (by omega)
  have hav_toNat : (BitVec.ofNat 64 wlen - ((8 - (work_ptr &&& 7)) &&& 7)).toNat = availNat := by
    rw [hav_bv, bv64_ofNat_toNat (by omega)]
  have hhdr_fit : hdr_addr.toNat + availNat < 2 ^ 64 := by
    rw [bv_add_ofNat_toNat (by omega)]; omega
  have hsplit : (bytes cnf_ptr cnfBytes ⋆
      region hdr_addr availNat ⋆ (region work_ptr pNat ⋆ R)) m := by
    have h1 : (region work_ptr wlen ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
    have h2 : ((region work_ptr pNat ⋆ region hdr_addr availNat) ⋆
        (bytes cnf_ptr cnfBytes ⋆ R)) m :=
      sep_mono (fun _ f => region_work_to_hdr (by omega) (by omega) f) h1
    exact sep_ac h2
  c0_call hInit
  refine ⟨cnfBytes, region work_ptr pNat ⋆ R, rfl, hcfit,
    by rw [hhdr_bv, hav_toNat]; exact hhdr_fit,
    by rw [hav_toNat]; omega,
    by rw [hhdr_bv, hav_toNat]; exact hsplit, ?_, ?_⟩
  · intro m' hm' hfail; wp_unfold
    have hm'_r : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' :=
      full_merge_reg hwfit (by omega) (by rw [hhdr_bv, hav_toNat] at hm'; exact hm')
    exact hQ 0#64 m' (Or.inl rfl) (fun h => by cases h)
      (fun mv nc i0 _ _ _ hsz _ hhdr _ => by
        have hlt := hfail mv nc (cnfBytes.drop i0) hhdr; rw [hav_toNat] at hlt; omega) hm'_r
  · intro c s0 j0 rest0 m0 hch_ptr hca0 hhdr0 hj0 hdrop0 hinv0 hcv0 hdcur0
      hal0 _ hte0 hpr0 hcl0 _ _ hprob0 _ _ hoom0 hinc0 hvals0 hwvec0 _ _ _ hm0
    have hch : c.hdr = hdr_addr := hch_ptr.trans hhdr_bv
    have hca : c.avail = availNat := hca0.trans hav_toNat
    have hvals_take : s0.core.vals.take (2 * c.mv) = List.replicate (2 * c.mv) 0#8 := by
      have hbva := c.hbva; rw [hvals0, List.take_replicate, Nat.min_eq_left (by omega)]
    c0_hsplit
    rotate_left; · cases hc
    c0_hsteps
    c0_call hParse
    refine ⟨c, s0, cnf_ptr, cnfBytes, j0, region work_ptr pNat ⋆ R,
      hch_ptr.symm, rfl, hcfit, hj0, by rwa [hdrop0], hcv0, hdcur0, hcl0, hte0, hpr0, hal0,
      hoom0, hprob0, hinc0, hvals0, hwvec0, hinv0, hm0, ?_⟩
    intro pb s1 m1 hlen1 hpb_dom _ _ _ hpb20 hpb1 huns_tr hm1; c0_hsteps
    · rcases hpb_dom with rfl | h1 | rfl
      · refine hQ 0#64 m1 (Or.inl rfl) (fun h => by cases h) ?_
          (full_merge_arena hwfit (by omega) hch hca hlen1 hm1)
        intro mv nc i0 _ _ _ _ _ hhdr hut
        rw [hhdr0, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hhdr
        rcases hhdr with ⟨rfl, rfl, hre⟩
        have h20 := huns_tr (by rw [hvals_take, hdrop0, hre]; exact hut); cases h20
      · exact absurd h1 hc
      · exact hQ 20#64 m1 (Or.inr (Or.inr rfl)) (fun _ => hpb20 rfl)
          (fun _ _ _ _ _ _ _ _ _ _ => rfl)
          (full_merge_arena hwfit (by omega) hch hca hlen1 hm1)
    · obtain ⟨cnf, hparse, hinv1, hcl1⟩ := hpb1 hc
      have hcnf_pos : CnfVarsPos cnf := parseDimacs_vars_pos hparse
      have hnot_ut : ∀ mv nc i0, cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
          fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen → i0 ≤ cnfBytes.length →
          parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc → False := by
        intro mv nc i0 _ _ _ _ _ hhdr hut
        rw [hhdr0, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hhdr
        rcases hhdr with ⟨rfl, rfl, hre⟩
        have h20 := huns_tr (by rw [hvals_take, hdrop0, hre]; exact hut)
        rw [hc] at h20; cases h20
      c0_call hPre; refine ⟨c, shiftDownCnf cnf, s1,
        bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
        hch_ptr.symm, hinv1, hcl1, sep_ac hm1, ?_⟩
      intro pp s2 m2 hlen2 hpp_dom _ hpp20 hpp1 hpp10 hm2
      c0_hsplit
      · c0_hsteps
        exact hQ 20#64 m2 (Or.inr (Or.inr rfl))
          (fun _ => ⟨cnf, hparse, shiftDownCnf_unsat hcnf_pos (hpp20 hc)⟩)
          (fun _ _ _ _ _ _ _ _ _ _ => rfl)
          (full_merge_arena hwfit (by omega) hch hca hlen2 (sep_ac hm2))
      c0_hsteps_nogrp
      refine wp_join_state1 (α := BitVec 64 × FullState) Prod.fst
        (fun p mr => p.2.LengthsOk c ∧ (p.1 = 0#64 ∨ p.1 = 10#64 ∨ p.1 = 20#64) ∧
          (p.1 = 20#64 → cnf.Unsat) ∧ (p.1 = 10#64 → p.2.scratch.extend_len ≤ c.extend_cap) ∧
          (bytes cnf_ptr cnfBytes ⋆ FullMem c p.2 ⋆ (region work_ptr pNat ⋆ R)) mr)
        (fun _ ⟨rv, sr⟩ mr ⟨hlen_r, hrv_dom, hrv_u, hrv_ext, hmr⟩ => by
          c0_hsteps
          · exact sched_solve_bytes_extend_check hExt hCheck hcfit hwfit (by omega) hch_ptr hch hca
              hlen_r (hrv_ext hc) hmr fun res m_end hres hm_end =>
                hQ res m_end (hres.elim Or.inl fun h => Or.inr (Or.inl h))
                  (fun h20 => by rcases hres with rfl | rfl <;> cases h20)
                  (fun mv nc i0 h1 h2 h3 h4 h5 h6 h7 =>
                    (hnot_ut mv nc i0 h1 h2 h3 h4 h5 h6 h7).elim)
                  hm_end
          · exact hQ rv mr hrv_dom (fun h20 => ⟨cnf, hparse, hrv_u h20⟩)
              (fun mv nc i0 h1 h2 h3 h4 h5 h6 h7 => (hnot_ut mv nc i0 h1 h2 h3 h4 h5 h6 h7).elim)
              (full_merge_arena hwfit (by omega) hch hca hlen_r hmr))
        (fun Jr hJr => by
          c0_hsplit
          · c0_hsteps
            exact hJr (10#64, s2) m2 ⟨hlen2, Or.inr (Or.inl rfl), (fun h => by cases h),
              (fun _ => hpp10 hc), sep_ac hm2⟩
          · c0_hsteps_nogrp
            refine wp_join_state1 (α := BitVec 64 × FullState) Prod.fst
              (fun p mr => p.2.LengthsOk c ∧ (p.1 = 0#64 ∨ p.1 = 10#64 ∨ p.1 = 20#64) ∧
                (p.1 = 20#64 → cnf.Unsat) ∧ (p.1 = 10#64 → p.2.scratch.extend_len ≤ c.extend_cap) ∧
                (bytes cnf_ptr cnfBytes ⋆ FullMem c p.2 ⋆ (region work_ptr pNat ⋆ R)) mr)
              (fun _ p mr hp => by c0_hsteps; exact hJr p mr hp)
              (fun Jr2 hJr2 => by
                c0_hsplit
                · c0_hsteps
                  exact hJr2 (0#64, s2) m2 ⟨hlen2, Or.inl rfl, (fun h => by cases h),
                    (fun h => by cases h), sep_ac hm2⟩
                · have hpp_eq1 : pp = 1#64 := by
                    rcases hpp_dom with h0 | h1 | h10 | h20
                    · exact absurd h0 hc
                    · exact h1
                    · exact absurd h10 (by assumption)
                    · exact absurd h20 (by assumption)
                  obtain ⟨hinv2, hcl2⟩ := hpp1 hpp_eq1
                  c0_hsteps; c0_call hSearch
                  refine ⟨c, shiftDownCnf cnf, s2,
                    bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
                    hch_ptr.symm, hinv2, hcl2, hm2, ?_⟩
                  intro r3 s3 m3 hlen3 hr3_dom hur3 hext3 hm3; c0_hsteps
                  exact hJr2 (r3, s3) m3 ⟨hlen3, hr3_dom,
                    fun h20 => shiftDownCnf_unsat hcnf_pos (hur3 h20), hext3, sep_ac hm3⟩))

theorem sched_kissat_solve_bytes_wp (Γ : Env)
    (hInit : ∀ a m Q X, fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hParse : ∀ a m Q X, fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hPre : ∀ a m Q X, fullPreprocessSpec a m Q X → Γ "full_preprocess" [i64] [i64] a m Q X)
    (hSearch : ∀ a m Q X, fullSearchSpec a m Q X → Γ "full_search" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullSolveBytesSpec a m Q X → Func.wp Γ Full.kissat_solve_bytes_body a m Q X :=
  fun _ _ _ _ h => sched_kissat_solve_bytes_core_wp Γ hInit hParse hPre hSearch hExt hCheck
    _ _ _ _ (fullSolveBytesCoreSpec_of_spec h)

private theorem schedSplicedFns_nodup : (schedSplicedFns.map Fn.name).Nodup := by
  have hchk := sched_acyclic
  simp only [schedModule, Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

private theorem schedSpecTable_names_eq (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (schedSpecTable mainSpec).map SpecEntry.name = schedSplicedFns.map Fn.name := by
  have h := congrArg (List.map Prod.fst) (schedSpecTable_sigs mainSpec)
  simpa only [List.map_map, Function.comp_def] using h

private theorem schedSpecTable_nodup (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((schedSpecTable mainSpec).map SpecEntry.name).Nodup := by
  rw [schedSpecTable_names_eq]; exact schedSplicedFns_nodup

private theorem fullFns_length_eq : Full.fullFns.length = 166 := by
  have h := congrArg List.length (Full.fullSpecTable_sigs fullSolveBytesSpec)
  simp only [List.length_map] at h
  exact h.symm

private theorem fullSpecTable_length_eq (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (fullSpecTable mainSpec).length = 166 := by
  rfl

private theorem sched_fns_length_eq : sched_fns.length = 15 := rfl

private theorem schedSplicedFns_getElem?_57 :
    schedSplicedFns[57]? = sched_fns[0]? := by
  unfold schedSplicedFns
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    fullFns_length_eq, sched_fns_length_eq,
    show min 57 166 = 57 from rfl, show min 1 15 = 1 from rfl]
  simp only [show ¬(57 < 57) by omega, show 57 - 57 < 1 by omega, ↓reduceIte, List.getElem?_take]

private theorem schedSplicedFns_getElem?_125 :
    schedSplicedFns[125]? = sched_fns[1]? := by
  unfold schedSplicedFns
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    fullFns_length_eq, sched_fns_length_eq,
    show min 57 166 = 57 from rfl, show min 1 15 = 1 from rfl,
    show min 67 (166 - 58) = 67 from rfl, show min 2 (15 - 1) = 2 from rfl]
  simp only [show ¬(125 < 57) by omega, show ¬(125 - 57 < 1) by omega,
    show ¬(125 - 57 - 1 < 67) by omega, show 125 - 57 - 1 - 67 < 2 by omega, ↓reduceIte,
    List.getElem?_take, List.getElem?_drop]

private theorem schedSplicedFns_getElem?_126 :
    schedSplicedFns[126]? = sched_fns[2]? := by
  unfold schedSplicedFns
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    fullFns_length_eq, sched_fns_length_eq,
    show min 57 166 = 57 from rfl, show min 1 15 = 1 from rfl,
    show min 67 (166 - 58) = 67 from rfl, show min 2 (15 - 1) = 2 from rfl]
  simp only [show ¬(126 < 57) by omega, show ¬(126 - 57 < 1) by omega,
    show ¬(126 - 57 - 1 < 67) by omega, show 126 - 57 - 1 - 67 < 2 by omega, ↓reduceIte,
    List.getElem?_take, List.getElem?_drop]

private theorem schedSplicedFns_getElem?_tail (k : Nat) (hk : k < 12) :
    schedSplicedFns[160 + k]? = sched_fns[3 + k]? := by
  unfold schedSplicedFns
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    fullFns_length_eq, sched_fns_length_eq,
    show min 57 166 = 57 from rfl, show min 1 15 = 1 from rfl,
    show min 67 (166 - 58) = 67 from rfl, show min 2 (15 - 1) = 2 from rfl,
    show min 33 (166 - 127) = 33 from rfl, show 15 - 3 = 12 from rfl]
  simp only [show ¬(160 + k < 57) by omega, show ¬(160 + k - 57 < 1) by omega,
    show ¬(160 + k - 57 - 1 < 67) by omega, show ¬(160 + k - 57 - 1 - 67 < 2) by omega,
    show ¬(160 + k - 57 - 1 - 67 - 2 < 33) by omega,
    show 160 + k - 57 - 1 - 67 - 2 - 33 < 12 by omega, ↓reduceIte, List.getElem?_drop]
  rw [show 3 + (160 + k - 57 - 1 - 67 - 2 - 33) = 3 + k by omega]

private theorem schedSplicedFns_getElem?_172 :
    schedSplicedFns[172]? = Full.fullFns[165]? := by
  unfold schedSplicedFns
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    fullFns_length_eq, sched_fns_length_eq,
    show min 57 166 = 57 from rfl, show min 1 15 = 1 from rfl,
    show min 67 (166 - 58) = 67 from rfl, show min 2 (15 - 1) = 2 from rfl,
    show min 33 (166 - 127) = 33 from rfl, show 15 - 3 = 12 from rfl]
  simp only [show ¬(172 < 57) by omega, show ¬(172 - 57 < 1) by omega,
    show ¬(172 - 57 - 1 < 67) by omega, show ¬(172 - 57 - 1 - 67 < 2) by omega,
    show ¬(172 - 57 - 1 - 67 - 2 < 33) by omega,
    show ¬(172 - 57 - 1 - 67 - 2 - 33 < 12) by omega, ↓reduceIte, List.getElem?_drop]

private theorem schedSpecTable_getElem?_lt126
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {n : Nat} (hn : n < 126) :
    (schedSpecTable mainSpec)[n]? = (fullSpecTable mainSpec)[n]? := by
  unfold schedSpecTable
  simp only [List.append_assoc, List.getElem?_append, List.length_take,
    fullSpecTable_length_eq, show min 126 166 = 126 from rfl, hn, ↓reduceIte, List.getElem?_take]

private theorem schedSpecTable_getElem?_126
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (schedSpecTable mainSpec)[126]? =
      some ⟨"full_enter_dense", [i64], [.bool], schedEnterDenseSpec, true⟩ := by
  unfold schedSpecTable
  simp only [List.append_assoc, List.getElem?_append, List.length_take,
    List.length_cons, List.length_nil, fullSpecTable_length_eq,
    show min 126 166 = 126 from rfl, show (0 : Nat) + 1 = 1 from rfl]
  simp only [show ¬(126 < 126) by omega, show 126 - 126 < 1 by omega, ↓reduceIte]
  rfl

private theorem schedSpecTable_getElem?_mid
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {n : Nat} (h1 : 127 ≤ n) (h2 : n < 160) :
    (schedSpecTable mainSpec)[n]? = (fullSpecTable mainSpec)[n]? := by
  unfold schedSpecTable
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_cons, List.length_nil, fullSpecTable_length_eq,
    show min 126 166 = 126 from rfl, show (0 : Nat) + 1 = 1 from rfl,
    show min 33 (166 - 127) = 33 from rfl]
  simp only [show ¬(n < 126) by omega, show ¬(n - 126 < 1) by omega,
    show n - 126 - 1 < 33 by omega, ↓reduceIte, List.getElem?_take, List.getElem?_drop]
  rw [show 127 + (n - 126 - 1) = n by omega]

private theorem schedSpecTable_getElem?_tail
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {k : Nat} (hk : k < 12) :
    (schedSpecTable mainSpec)[160 + k]? =
      ([ ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
       , ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
       , ⟨"full_max_u64", [i64, i64], [i64], schedMaxU64Spec, true⟩
       , ⟨"full_probe_dticks", [i64, .bool], [i64], schedProbeDticksSpec, true⟩
       , ⟨"full_probe_tail", [i64, i64], [i64], schedProbeTailSpec, true⟩
       , ⟨"full_probe", [i64, .bool], [i64], schedProbeSpec, true⟩
       , ⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩
       , ⟨"full_elim_bve", [i64, i64], [i64], schedElimBveSpec, true⟩
       , ⟨"full_eliminate", [i64, .bool], [i64], schedEliminateSpec, true⟩
       , ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩
       , ⟨"full_simplify", [i64, .bool, .bool], [i64], schedSimplifySpec, true⟩
       , ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩ ])[k]? := by
  unfold schedSpecTable
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_cons, List.length_nil, fullSpecTable_length_eq,
    show min 126 166 = 126 from rfl, show (0 : Nat) + 1 = 1 from rfl,
    show min 33 (166 - 127) = 33 from rfl,
    show (0 : Nat) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 12 from rfl]
  simp only [show ¬(160 + k < 126) by omega, show ¬(160 + k - 126 < 1) by omega,
    show ¬(160 + k - 126 - 1 < 33) by omega, show 160 + k - 126 - 1 - 33 < 12 by omega, ↓reduceIte]
  rw [show 160 + k - 126 - 1 - 33 = k by omega]

private theorem schedSpecTable_getElem?_172
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (schedSpecTable mainSpec)[172]? =
      some ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], mainSpec, true⟩ := by
  unfold schedSpecTable
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_cons, List.length_nil, fullSpecTable_length_eq,
    show min 126 166 = 126 from rfl, show (0 : Nat) + 1 = 1 from rfl,
    show min 33 (166 - 127) = 33 from rfl,
    show (0 : Nat) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 12 from rfl]
  simp only [show ¬(172 < 126) by omega, show ¬(172 - 126 < 1) by omega,
    show ¬(172 - 126 - 1 < 33) by omega, show ¬(172 - 126 - 1 - 33 < 12) by omega,
    ↓reduceIte, List.getElem?_drop]
  rfl

private theorem mkSchedEnv_row_at {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (n : Nat) (e : SpecEntry)
    (hget : (schedSpecTable mainSpec)[n]? = some e)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ a m Q X, e.spec a m Q X → mkSchedEnv mainSpec e.name e.as e.rs a m Q X :=
  fun a m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hget) (schedSpecTable_nodup mainSpec)
      (hno a m Q X h)

private theorem mkSchedEnv_row_lt126 {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (n : Nat) (e : SpecEntry) (hn : n < 126 := by omega)
    (hf : (fullSpecTable mainSpec)[n]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ a m Q X, e.spec a m Q X → mkSchedEnv mainSpec e.name e.as e.rs a m Q X :=
  mkSchedEnv_row_at n e ((schedSpecTable_getElem?_lt126 mainSpec hn).trans hf) hno

private theorem mkSchedEnv_row_mid {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (n : Nat) (e : SpecEntry) (h1 : 127 ≤ n := by omega) (h2 : n < 160 := by omega)
    (hf : (fullSpecTable mainSpec)[n]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ a m Q X, e.spec a m Q X → mkSchedEnv mainSpec e.name e.as e.rs a m Q X :=
  mkSchedEnv_row_at n e ((schedSpecTable_getElem?_mid mainSpec h1 h2).trans hf) hno

private theorem mkSchedEnv_row_tail {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (k : Nat) (e : SpecEntry) (hk : k < 12 := by omega)
    (ht : ([ ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
           , ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
           , ⟨"full_max_u64", [i64, i64], [i64], schedMaxU64Spec, true⟩
           , ⟨"full_probe_dticks", [i64, .bool], [i64], schedProbeDticksSpec, true⟩
           , ⟨"full_probe_tail", [i64, i64], [i64], schedProbeTailSpec, true⟩
           , ⟨"full_probe", [i64, .bool], [i64], schedProbeSpec, true⟩
           , ⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩
           , ⟨"full_elim_bve", [i64, i64], [i64], schedElimBveSpec, true⟩
           , ⟨"full_eliminate", [i64, .bool], [i64], schedEliminateSpec, true⟩
           , ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩
           , ⟨"full_simplify", [i64, .bool, .bool], [i64], schedSimplifySpec, true⟩
           , ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩ ])[k]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ a m Q X, e.spec a m Q X → mkSchedEnv mainSpec e.name e.as e.rs a m Q X :=
  mkSchedEnv_row_at (160 + k) e ((schedSpecTable_getElem?_tail mainSpec hk).trans ht) hno

/-- Indices in `schedSplicedFns` (`173` fns) of all `15` M2 fast-scheduler functions plus
`kissat_solve_bytes` (`16` proved entries). -/
def schedProvedIndices : List Nat :=
  [57, 125, 126, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]

/-- `SpecEntry.Impl (mkSchedEnv mainSpec)` for all `15` M2 fast-scheduler functions and
`kissat_solve_bytes` (`16 / 16` rows). -/
theorem sched_proved_rows_ok (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    ∀ n ∈ schedProvedIndices,
      ∃ fn row, schedSplicedFns[n]? = some fn ∧ (schedSpecTable mainSpec)[n]? = some row ∧
        SpecEntry.Impl (mkSchedEnv mainSpec) fn row := by
  let Γ := mkSchedEnv mainSpec
  have h7 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 7
    ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩
  have h9 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 9
    ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
  have h11 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 11
    ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  have h14 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  have h15 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  have h30 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 30
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  have h41 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 41
    ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩
  have h44 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 44
    ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩
  have h49 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 49
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  have h57 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 57
    ⟨"full_sweep_bins", [i64], [], fullSweepBinsSpec, true⟩
  have h60 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 60
    ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  have h61 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 61
    ⟨"full_reduce", [i64, .bool], [i64], fullReduceSpec, true⟩
  have h82 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 82
    ⟨"full_analyze", [i64], [i64], fullAnalyzeSpec, true⟩
  have h84 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 84
    ⟨"full_decide", [i64], [i64], fullDecideSpec, true⟩
  have h85 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 85
    ⟨"full_warmup", [i64], [], fullWarmupSpec, true⟩
  have h90 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 90
    ⟨"full_rephase", [i64], [], fullRephaseSpec, true⟩
  have h91 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 91
    ⟨"full_switch_mode", [i64], [], fullSwitchModeSpec, true⟩
  have h92 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 92
    ⟨"full_restart_due", [i64], [i64], fullRestartDueSpec, true⟩
  have h93 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 93
    ⟨"full_restart", [i64], [], fullRestartSpec, true⟩
  have h96 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 96
    ⟨"full_extend", [i64], [], fullExtendSpec, true⟩
  have h105 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 105
    ⟨"full_lucky", [i64], [i64], fullLuckySpec, true⟩
  have h111 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 111
    ⟨"full_probe_run", [i64, i64], [i64], fullProbeRunSpec, true⟩
  have h113 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 113
    ⟨"full_transitive", [i64], [i64], fullTransitiveSpec, true⟩
  have h119 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 119
    ⟨"full_vivify", [i64, i64], [i64], fullVivifySpec, true⟩
  have h121 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 121
    ⟨"full_tarjan_scc", [i64], [i64], fullTarjanSccSpec, true⟩
  have h122 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 122
    ⟨"full_subst_elim_vars", [i64, i64], [.bool], fullSubstElimVarsSpec, true⟩
  have h123 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 123
    ⟨"full_subst_rewrite_bins", [i64], [.bool], fullSubstRewriteBinsSpec, true⟩
  have h124 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 124
    ⟨"full_subst_rewrite_ar", [i64], [.bool], fullSubstRewriteArSpec, true⟩
  have h125 := mkSchedEnv_row_lt126 (mainSpec := mainSpec) 125
    ⟨"full_substitute", [i64], [i64], fullSubstituteSpec, true⟩
  have h126 := mkSchedEnv_row_at (mainSpec := mainSpec) 126
    ⟨"full_enter_dense", [i64], [.bool], schedEnterDenseSpec, true⟩
    (schedSpecTable_getElem?_126 mainSpec)
  have h127 := mkSchedEnv_row_mid (mainSpec := mainSpec) 127
    ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  have h137 := mkSchedEnv_row_mid (mainSpec := mainSpec) 137
    ⟨"full_congruence", [i64], [i64], fullCongruenceSpec, true⟩
  have h144 := mkSchedEnv_row_mid (mainSpec := mainSpec) 144
    ⟨"full_sweep_sat", [i64], [i64], fullSweepSatSpec, true⟩
  have h147 := mkSchedEnv_row_mid (mainSpec := mainSpec) 147
    ⟨"full_forward_sub", [i64], [i64], fullForwardSubSpec, true⟩
  have h156 := mkSchedEnv_row_mid (mainSpec := mainSpec) 156
    ⟨"full_bve_var", [i64, i32], [i64], fullBveVarSpec, true⟩
  have h159 := mkSchedEnv_row_mid (mainSpec := mainSpec) 159
    ⟨"full_factor", [i64], [i64], fullFactorSpec, true⟩
  have h160 := mkSchedEnv_row_tail (mainSpec := mainSpec) 0
    ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  have h161 := mkSchedEnv_row_tail (mainSpec := mainSpec) 1
    ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
  have h162 := mkSchedEnv_row_tail (mainSpec := mainSpec) 2
    ⟨"full_max_u64", [i64, i64], [i64], schedMaxU64Spec, true⟩
  have h163 := mkSchedEnv_row_tail (mainSpec := mainSpec) 3
    ⟨"full_probe_dticks", [i64, .bool], [i64], schedProbeDticksSpec, true⟩
  have h164 := mkSchedEnv_row_tail (mainSpec := mainSpec) 4
    ⟨"full_probe_tail", [i64, i64], [i64], schedProbeTailSpec, true⟩
  have h165 := mkSchedEnv_row_tail (mainSpec := mainSpec) 5
    ⟨"full_probe", [i64, .bool], [i64], schedProbeSpec, true⟩
  have h166 := mkSchedEnv_row_tail (mainSpec := mainSpec) 6
    ⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩
  have h167 := mkSchedEnv_row_tail (mainSpec := mainSpec) 7
    ⟨"full_elim_bve", [i64, i64], [i64], schedElimBveSpec, true⟩
  have h168 := mkSchedEnv_row_tail (mainSpec := mainSpec) 8
    ⟨"full_eliminate", [i64, .bool], [i64], schedEliminateSpec, true⟩
  have h169 := mkSchedEnv_row_tail (mainSpec := mainSpec) 9
    ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩
  have h170 := mkSchedEnv_row_tail (mainSpec := mainSpec) 10
    ⟨"full_simplify", [i64, .bool, .bool], [i64], schedSimplifySpec, true⟩
  have h171 := mkSchedEnv_row_tail (mainSpec := mainSpec) 11
    ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩
  intro n hn
  simp only [schedProvedIndices, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact ⟨_, _, schedSplicedFns_getElem?_57,
      schedSpecTable_getElem?_lt126 mainSpec (by omega),
      .of (sched_sweep_bins_wp Γ h14)⟩
  · exact ⟨_, _, schedSplicedFns_getElem?_125,
      schedSpecTable_getElem?_lt126 mainSpec (by omega),
      .of (sched_substitute_wp Γ h30 h121 h122 h123 h124 h60 h49)⟩
  · exact ⟨_, _, schedSplicedFns_getElem?_126, schedSpecTable_getElem?_126 mainSpec,
      .of (sched_enter_dense_wp Γ h30 h49 h57 h15 h60 h11)⟩
  · exact ⟨_, _, schedSplicedFns_getElem?_tail 0 (by omega),
      schedSpecTable_getElem?_tail mainSpec (k := 0) (by omega),
      .of (sched_scale_delta_wp Γ h9)⟩
  · exact ⟨_, _, schedSplicedFns_getElem?_tail 1 (by omega),
      schedSpecTable_getElem?_tail mainSpec (k := 1) (by omega),
      .of (sched_min_u64_wp Γ)⟩
  · exact ⟨_, _, schedSplicedFns_getElem?_tail 2 (by omega),
      schedSpecTable_getElem?_tail mainSpec (k := 2) (by omega),
      .of (sched_max_u64_wp Γ)⟩
  · exact ⟨_, _, schedSplicedFns_getElem?_tail 3 (by omega),
      schedSpecTable_getElem?_tail mainSpec (k := 3) (by omega),
      .of (sched_probe_dticks_wp Γ h162)⟩
  · exact ⟨_, _, schedSplicedFns_getElem?_tail 4 (by omega),
      schedSpecTable_getElem?_tail mainSpec (k := 4) (by omega),
      .of (sched_probe_tail_wp Γ h113 h161 h111 h119)⟩
  · exact ⟨_, _, schedSplicedFns_getElem?_tail 5 (by omega),
      schedSpecTable_getElem?_tail mainSpec (k := 5) (by omega),
      .of (sched_probe_wp Γ h163 h9 h160 h125 h137 h144 h164)⟩
  · exact ⟨_, _, schedSplicedFns_getElem?_tail 6 (by omega),
      schedSpecTable_getElem?_tail mainSpec (k := 6) (by omega),
      .of (sched_elim_dticks_wp Γ)⟩
  · exact ⟨_, _, schedSplicedFns_getElem?_tail 7 (by omega),
      schedSpecTable_getElem?_tail mainSpec (k := 7) (by omega),
      .of (sched_elim_bve_wp Γ h156)⟩
  · exact ⟨_, _, schedSplicedFns_getElem?_tail 8 (by omega),
      schedSpecTable_getElem?_tail mainSpec (k := 8) (by omega),
      .of (sched_eliminate_wp Γ h166 h9 h160 h126 h147 h161 h167 h159 h127)⟩
  · exact ⟨_, _, schedSplicedFns_getElem?_tail 9 (by omega),
      schedSpecTable_getElem?_tail mainSpec (k := 9) (by omega),
      .of (sched_preprocess_wp Γ h49 h60 h160 h165 h168)⟩
  · exact ⟨_, _, schedSplicedFns_getElem?_tail 10 (by omega),
      schedSpecTable_getElem?_tail mainSpec (k := 10) (by omega),
      .of (sched_simplify_wp Γ h30 h61 h165 h168)⟩
  · exact ⟨_, _, schedSplicedFns_getElem?_tail 11 (by omega),
      schedSpecTable_getElem?_tail mainSpec (k := 11) (by omega),
      .of (sched_search_wp Γ h105 h85 h49 h82 h91 h90 h61 h170 h92 h93 h84)⟩
  · exact ⟨_, _, schedSplicedFns_getElem?_172, schedSpecTable_getElem?_172 mainSpec,
      .of (fun a m Q X h =>
        sched_kissat_solve_bytes_core_wp Γ h41 h44 h169 h171 h96 h7 a m Q X
          (hweaken a m Q X h))⟩

/-! ### Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, ZERO SAT model proofs) -/

/-- Concrete UNSAT DIMACS payload (`p cnf 1 2\n1 0\n-1 0\n`, `19` bytes). -/
def schedNvUnsatBytes : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 49, 32, 50, 10, 49, 32, 48, 10, 45, 49, 32, 48, 10]

/-- Parsed `Std.Sat.CNF Nat` for `schedNvUnsatBytes`. -/
def schedNvUnsatCnf : CNF Nat :=
  (CNF.empty.add (CNF.Clause.ofLiterals [(1, true)])).add (CNF.Clause.ofLiterals [(1, false)])

theorem parseDimacs_schedNvUnsatBytes : parseDimacs schedNvUnsatBytes = some schedNvUnsatCnf := rfl

private theorem schedNvUnsat_header :
    parseHeader schedNvUnsatBytes = some (1, 2, schedNvUnsatBytes.drop 9) := by decide

private theorem schedNvUnsat_trace :
    UnitUnsatTrace 1 (List.replicate 2 0#8) (schedNvUnsatBytes.drop 9) 2 := by
  have hcl1 : parseClause 1 (schedNvUnsatBytes.drop 9) =
      some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral 0], schedNvUnsatBytes.drop 13) := rfl
  have hcl2 : parseClause 1 (schedNvUnsatBytes.drop 13) =
      some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral 1], [10]) := rfl
  exact UnitUnsatTrace.step (l := 0) (by decide) hcl1 (by decide)
    (UnitUnsatTrace.conflict (l := 1) (by decide) hcl2 (by decide) ⟨CNF.empty, rfl⟩)

/-- Concrete UNSAT witness contract (`schedNvUnsatBytes`, `work_len = 4096`, `fuel = 16`). -/
def schedUnsatWitnessSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q _ =>
    ∃ R : Mem 64 → Prop,
      cnf_ptr ≠ 0#64 ∧ work_ptr ≠ 0#64 ∧
      cnf_len = BitVec.ofNat 64 schedNvUnsatBytes.length ∧ work_len = 4096#64 ∧ fuel = 16#64 ∧
      cnf_ptr.toNat + schedNvUnsatBytes.length < 2 ^ 64 ∧ work_ptr.toNat + 4096 < 2 ^ 64 ∧
      (bytes cnf_ptr schedNvUnsatBytes ⋆ region work_ptr 4096 ⋆ R) m ∧
      ∀ m', schedNvUnsatCnf.Unsat →
        (bytes cnf_ptr schedNvUnsatBytes ⋆ region work_ptr 4096 ⋆ R) m' → Q (20#64, ()) m'

theorem fullSolveBytesCoreSpec_of_schedUnsatWitness
    {a : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : schedUnsatWitnessSpec a m Q X) : fullSolveBytesCoreSpec a m Q X := by
  obtain ⟨R, hcp, hwp, hcl, hwl, hfu, hcfit, hwfit, hm, hQ⟩ := h
  refine ⟨schedNvUnsatBytes, 4096, R, hcl, hwl, hcfit, hwfit, hm, fun r m' _ hu huns_w hm' => ?_⟩
  have hr20 : r = 20#64 :=
    huns_w 1 2 9 hcp hwp (by rw [hfu]; decide)
      (by unfold fullFixedBytes valsBytes markBytes u32FullBytes fullMinDepthOf; decide)
      (by decide) schedNvUnsat_header schedNvUnsat_trace
  subst hr20
  obtain ⟨cnf, hparse, huns⟩ := hu rfl
  rw [parseDimacs_schedNvUnsatBytes] at hparse; cases Option.some.inj hparse
  exact hQ m' huns hm'

/-- Closed `173`-function environment for concrete UNSAT non-vacuity (`20#64`). -/
def schedUnsatEnv : Env := mkSchedEnv schedUnsatWitnessSpec

abbrev schedNvCnfPtr : BitVec 64 := 0x1000#64
abbrev schedNvWorkPtr (cnfBytes : List UInt8) : BitVec 64 :=
  schedNvCnfPtr + BitVec.ofNat 64 cnfBytes.length

def schedPayload (cnfBytes : List UInt8) : List UInt8 :=
  cnfBytes ++ List.replicate 4096 0

theorem schedPayload_sep (cnfBytes : List UInt8) (hcb : cnfBytes.length ≤ 4096) :
    (bytes schedNvCnfPtr cnfBytes ⋆ region (schedNvWorkPtr cnfBytes) 4096)
      ((schedPayload cnfBytes).At schedNvCnfPtr) := by
  have h4096 : (List.replicate 4096 (0 : UInt8)).length = 4096 := List.length_replicate
  have h1 := Mem.At_append_sep cnfBytes (List.replicate 4096 0) schedNvCnfPtr
    (by simp only [h4096]; omega)
  have h0 : (Eq ((cnfBytes ++ List.replicate 4096 0).At schedNvCnfPtr))
      ((schedPayload cnfBytes).At schedNvCnfPtr) := rfl
  rw [h1] at h0
  exact sep_mono_r (fun _ hfW => ⟨List.replicate 4096 0, h4096, hfW.symm⟩) h0

/-- Headline source-level UNSAT soundness of `kissat_solve_bytes` under `schedEnv`
(`XPost := False`). -/
theorem sched_solve_bytes_correct
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp schedEnv Full.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  sched_kissat_solve_bytes_wp schedEnv
    (mkSchedEnv_row_lt126 (mainSpec := fullSolveBytesSpec) 41
      ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩)
    (mkSchedEnv_row_lt126 (mainSpec := fullSolveBytesSpec) 44
      ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩)
    (mkSchedEnv_row_tail (mainSpec := fullSolveBytesSpec) 9
      ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩)
    (mkSchedEnv_row_tail (mainSpec := fullSolveBytesSpec) 11
      ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩)
    (mkSchedEnv_row_lt126 (mainSpec := fullSolveBytesSpec) 96
      ⟨"full_extend", [i64], [], fullExtendSpec, true⟩)
    (mkSchedEnv_row_lt126 (mainSpec := fullSolveBytesSpec) 7
      ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩)
    _ m _ _
    ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, fun _ _ hdom hu hm' => ⟨hdom, hu, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`): executing `kissat_solve_bytes` on
`p cnf 1 2\n1 0\n-1 0\n` with `4096`-byte workspace and `fuel = 16` provably returns `20#64`
and establishes `schedNvUnsatCnf.Unsat`. -/
theorem sched_unsat_nonvacuous :
    let m0 : Mem 64 := (schedPayload schedNvUnsatBytes).At schedNvCnfPtr
    Func.wp schedUnsatEnv Full.kissat_solve_bytes_body
      (schedNvCnfPtr, BitVec.ofNat 64 schedNvUnsatBytes.length,
        schedNvWorkPtr schedNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 20#64 ∧ schedNvUnsatCnf.Unsat ∧
        (bytes schedNvCnfPtr schedNvUnsatBytes ⋆
          region (schedNvWorkPtr schedNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  sched_kissat_solve_bytes_core_wp schedUnsatEnv
    (mkSchedEnv_row_lt126 (mainSpec := schedUnsatWitnessSpec) 41
      ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩)
    (mkSchedEnv_row_lt126 (mainSpec := schedUnsatWitnessSpec) 44
      ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩)
    (mkSchedEnv_row_tail (mainSpec := schedUnsatWitnessSpec) 9
      ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩)
    (mkSchedEnv_row_tail (mainSpec := schedUnsatWitnessSpec) 11
      ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩)
    (mkSchedEnv_row_lt126 (mainSpec := schedUnsatWitnessSpec) 96
      ⟨"full_extend", [i64], [], fullExtendSpec, true⟩)
    (mkSchedEnv_row_lt126 (mainSpec := schedUnsatWitnessSpec) 7
      ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩)
    _ _ _ _
    (fullSolveBytesCoreSpec_of_schedUnsatWitness
      ⟨emp, by decide, by decide, rfl, rfl, rfl, by decide, by decide,
        by rw [sep_emp]; exact schedPayload_sep schedNvUnsatBytes (by decide),
        fun _ huns hm' => ⟨rfl, huns, hm'⟩⟩)

end TopAndNonVacuity

end LeanQbe.T.Examples.Kissat.FullFastSched
