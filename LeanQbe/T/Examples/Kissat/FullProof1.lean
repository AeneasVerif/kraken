module

public import LeanQbe.T.Examples.Kissat.Full
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.DimacsLemmas
public import LeanQbe.T.Examples.Kissat.SolverIngestLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Top-Level Orchestrator Proofs — Part 1 (`Stage 4`, UNSAT-Only)

Defines Phase-1 local specifications (`FullTopSpecs`) matching the canonical Stage-4 UNSAT-only
invariants (`FullLitMarksClear`, `FullArenaVarsNodup`, `FullLastLearnedWf`, `FullExtScratchOk`,
`FullSparseInv`, `FullDenseInv`) and proves `Func.wp` for the first 4 top orchestrators in
`Full.lean`:
1. `full_probe` (`full_probe_wp`)
2. `full_eliminate` (`full_eliminate_wp`)
3. `full_preprocess` (`full_preprocess_wp`)
4. `full_simplify` (`full_simplify_wp`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Canonical Stage-4 invariants and local Phase-1 callee specifications -/

namespace FullTopSpecs

/-- Both variable marks (`mrk[0..max_vars)`) and literal marks (`lit_mark[0..2*max_vars)`) are
cleared to `0#8`. -/
def FullLitMarksClear (c : FullCfg) (s : FullState) : Prop :=
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
  (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)

/-- Every live non-garbage arena clause has pairwise distinct variable indices. -/
def FullArenaVarsNodup (s : FullState) : Prop :=
  ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false →
    ((fullArenaClauseLits s r).map (· / 2)).Nodup

/-- Every `last_learned[0..8)` ring slot is either empty (`0xFFFFFFFF#32`) or a live arena ref. -/
def FullLastLearnedWf (s : FullState) : Prop :=
  ∀ i < 8,
    let cr := s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32
    cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ fullArenaClauseRefs s

/-- Scratch-side soundness/safety invariant (`last_learned` refs + `extend_len` bound). -/
def FullExtScratchOk (c : FullCfg) (s : FullState) : Prop :=
  FullLastLearnedWf s ∧ s.scratch.extend_len ≤ c.extend_cap

/-- Canonical sparse-mode (`dense_mode = 0#64`) Stage-4 UNSAT-only invariant. -/
def FullSparseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

/-- Canonical dense-mode (`cur_level = 0`, `dense_mode ≠ 0#64`) Stage-4 UNSAT-only invariant. -/
def FullDenseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64

/-- Conflict descriptor recorded by `full_propagate` returning `1#64` (binary or large clause). -/
def FullConflictInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  (s.core.confl_type = 1#64 ∧
    s.core.confl_lit0.toNat < 2 * s.core.cur_vars ∧
    s.core.confl_lit1.toNat < 2 * s.core.cur_vars ∧
    (∀ F_cur, FullWitnessInv c F0 F_cur s.core →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [s.core.confl_lit0.toNat, s.core.confl_lit1.toNat])) ∧
    s.core.vals[s.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
    s.core.vals[s.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8) ∨
  (s.core.confl_type = 2#64 ∧
    s.core.confl_ref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s s.core.confl_ref.toNat = false ∧
    ∀ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat,
      s.core.vals[l]?.getD 0#8 = 0xFF#8)

theorem FullSparseInv.lengths {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) : s.LengthsOk c :=
  h.1.lengths

theorem FullDenseInv.lengths {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) : s.LengthsOk c :=
  h.1.lengths

theorem FullSparseInv.extend_len_le {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) : s.scratch.extend_len ≤ c.extend_cap :=
  h.2.2.2.1.2

theorem FullSparseInv.with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 { s with scratch := sc' } := by
  refine ⟨h.1.with_scratch (h.lengths.with_scratch hok) rfl, h.2.1, h.2.2.1, ?_, h.2.2.2.2⟩
  refine ⟨?_, by simpa [hext] using h.2.2.2.1.2⟩
  intro i hi; simpa [FullLastLearnedWf, hll] using h.2.2.2.1.1 i hi

theorem FullSparseInv.of_safety_slice {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullSparseInv c F0 s)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hlen' : s'.LengthsOk c)
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hext : s'.scratch.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  refine ⟨h.1.with_scratch hlen' hcore, ?_, ?_, ?_, ?_⟩
  · unfold FullLitMarksClear; rw [heq]; exact h.2.1
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [heq]; exact h.2.2.1
  · refine ⟨?_, by rw [hext]; exact h.2.2.2.1.2⟩
    intro i hi; unfold fullArenaClauseRefs; rw [heq, hll]
    exact h.2.2.2.1.1 i hi
  · rw [heq]; exact h.2.2.2.2

theorem FullDenseInv.with_flags {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {fl' : List (BitVec 32)} (hflen : fl'.length = c.max_vars) :
    FullDenseInv c F0 { s with core := { s.core with flags := fl' } } := by
  obtain ⟨F_cur, hw⟩ := h.1.witness
  have hlen' : ({ s with core := { s.core with flags := fl' } } : FullState).LengthsOk c :=
    ⟨{ h.lengths.core_ok with flags_len := hflen }, h.lengths.scratch_ok⟩
  have hcore' : FullCoreInv c F0 { s with core := { s.core with flags := fl' } } :=
    ⟨hlen', F_cur, { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }⟩
  exact ⟨hcore', h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem FullConflictInv.level0_unsat {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) (hl0 : s.core.cur_level = 0) (hc : FullConflictInv c F0 s) :
    F0.Unsat := by
  rcases hc with ⟨_, h0, h1, hent, hf0, hf1⟩ | ⟨_, href, hng, hfals⟩
  · exact hcore.level0_unsat_of_bin_conflict hl0 h0 h1 hent hf0 hf1
  · exact hcore.level0_unsat_of_conflict hl0 href hng hfals

/-! ### Internal callee contracts -/

def fullIsqrtSpec : Spec [i64] [i64] := fun (x, ()) m Q _ =>
  ∀ r : BitVec 64, r.toNat ≤ x.toNat → Q (r, ()) m

/-- Shared contract for sparse inprocessing passes returning `1#64` (level 0) or `20#64` (UNSAT). -/
def fullSparsePassSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 1#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Shared contract for 1-parameter sparse inprocessing passes (`full_probe_run`, `full_vivify`). -/
def fullSparsePassArgSpec : Spec [i64, i64] [i64] := fun (h, _arg, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 1#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

abbrev fullSubstituteSpec := fullSparsePassSpec
abbrev fullCongruenceSpec := fullSparsePassSpec
abbrev fullSweepSatSpec := fullSparsePassSpec
abbrev fullTransitiveSpec := fullSparsePassSpec
abbrev fullProbeRunSpec := fullSparsePassArgSpec
abbrev fullVivifySpec := fullSparsePassArgSpec
abbrev fullProbeSpec := fullSparsePassSpec
abbrev fullEliminateSpec := fullSparsePassSpec

def fullEnterDenseSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (ok = false → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (ok = true → FullDenseInv c F0 s') →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullForwardSubSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → (r = 1#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullBveVarSpec : Spec [i64, i32] [i64] := fun (h, v, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ v.toNat < s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullFactorSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullRebuildWatchesSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 ∨ r = 1#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullPropagateSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      s'.core.cur_level = s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 → FullSparseInv c F0 s' ∧ s'.core.propagated = s'.core.trail_end ∧
        (s.core.propagated < s.core.trail_end → s'.core.fuel.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → FullSparseInv c F0 s' ∧ s'.core.fuel.toNat < s.core.fuel.toNat ∧
        FullConflictInv c F0 s') →
      (r = 2#64 → s'.core.oom ≠ 0#64 ∨ s'.core.fuel = 0#64) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullBacktrackSpec : Spec [i64, i64] [] := fun (h, target_lvl, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ target_lvl.toNat ≤ s.core.cur_level ∧
    (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = target_lvl.toNat →
      s'.core.fuel = s.core.fuel →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullReduceSpec : Spec [i64, .bool] [i64] := fun (h, _force, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullSparseInv c F0 s') →
      (s.core.cur_level = 0 → r = 0#64 → FullSparseInv c F0 s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullPreprocessSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullSimplifySpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullSparseInv c F0 s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullLuckySpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 s') →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullWarmupSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullSparseInv c F0 s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullAnalyzeSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ FullConflictInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullSparseInv c F0 s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullSwitchModeSpec : Spec [i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' =>
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len = s.scratch.extend_len)

def fullRephaseSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullSparseInv c F0 s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullRestartDueSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' =>
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len = s.scratch.extend_len)

def fullRestartSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullSparseInv c F0 s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullDecideSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64) →
      s'.core.fuel = s.core.fuel →
      s'.core.propagated = s.core.propagated →
      (r = 1#64 → FullSparseInv c F0 s' ∧ s'.core.trail_end = s.core.trail_end + 1) →
      (r = 0#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullSearchSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

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
        FullSparseInv c CNF.empty s →
        s.core.d_cur = cnf_ptr + BitVec.ofNat 64 j →
        s.core.cur_vars = c.mv → s.core.arena_len = 0 → s.core.wlen = 1 →
        s.core.trail_end = 0 → s.core.propagated = 0 → s.core.cur_level = 0 →
        s.core.fuel = fuel → s.core.oom = 0#64 → s.core.inconsistent = 0#64 →
        s.core.vals = List.replicate (2 * c.max_vars) 0#8 →
        (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R) m' →
        Q (true, ()) m')

def fullParseBodySpec : Spec [i64, i64] [i64] := fun (h, cend, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (cnf_ptr : BitVec 64) (cnfBytes : List UInt8)
    (i0 : Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ i0 ≤ cnfBytes.length ∧
    parseHeader cnfBytes = some (c.mv, c.nc, cnfBytes.drop i0) ∧
    s.core.d_cur = cnf_ptr + BitVec.ofNat 64 i0 ∧
    s.core.cur_vars = c.mv ∧ s.core.cur_level = 0 ∧ s.core.trail_end = 0 ∧
    s.core.propagated = 0 ∧ s.core.arena_len = 0 ∧ s.core.oom = 0#64 ∧
    s.core.inconsistent = 0#64 ∧
    FullSparseInv c CNF.empty s ∧
    (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
      (r = 1#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        FullSparseInv c cnf s' ∧ s'.core.cur_level = 0) →
      (UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc →
        r = 20#64) →
      (bytes cnf_ptr cnfBytes ⋆ FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullExtendSpec : Spec [i64] [] :=
  SafetySlice.spec fullExtendSlice
    (fun c (h, ()) s => h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap)
    (fun _ _ _ _ _ => True)

/-- Core `kissat_solve_bytes` spec (UNSAT-only soundness + `UnitUnsatTrace` non-vacuity). -/
def fullSolveBytesCoreSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧
      work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (∀ mv nc i0,
          cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
          fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen →
          i0 ≤ cnfBytes.length →
          parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
          r = 20#64) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
        Q (r, ()) m'

/-- Headline UNSAT-only soundness specification of `D-Full` `kissat_solve_bytes`. -/
def fullSolveBytesSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, _fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧
      work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
        Q (r, ()) m'

theorem fullSolveBytesCoreSpec_of_spec
    {args : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : fullSolveBytesSpec args m Q X) : fullSolveBytesCoreSpec args m Q X := by
  obtain ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm, hQ⟩ := h
  exact ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm,
    fun r m' hdom hu _ hm' => hQ r m' hdom hu hm'⟩

end FullTopSpecs

/-! ## 2. `Func.wp` proofs for `full_probe`, `full_eliminate`, `full_preprocess`, `full_simplify` -/

section TopOrchestrators1

open FullTopSpecs
open scoped FullArenaTactics

local macro "fp_steps" : tactic => `(tactic| (try (change wp _ _ _ _ _); c0_steps))

/-- `Func.wp` proof for `full_probe` (`Full.lean:1047-1060`). -/
theorem full_probe_wp (Γ : Env)
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, fullSubstituteSpec a m Q X → Γ "full_substitute" [i64] [i64] a m Q X)
    (hCong : ∀ a m Q X, fullCongruenceSpec a m Q X → Γ "full_congruence" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullSweepSatSpec a m Q X → Γ "full_sweep_sat" [i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, fullTransitiveSpec a m Q X → Γ "full_transitive" [i64] [i64] a m Q X)
    (hPRun : ∀ a m Q X, fullProbeRunSpec a m Q X →
      Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, fullVivifySpec a m Q X → Γ "full_vivify" [i64, i64] [i64] a m Q X) :
    ∀ args m Q X, fullProbeSpec args m Q X → Func.wp Γ full_probe_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  unfold Func.wp full_probe_body; fp_steps
  c0_call hIsqrt
  intro r_sq _
  fp_steps
  let s0 : FullState :=
    { s with
      scratch := { s.scratch with
        probings := s.scratch.probings + 1#64
        probe_limit := s.scratch.conflicts + 500#64 * r_sq } }
  have hinv0 : FullSparseInv c F0 s0 :=
    hinv.with_scratch_keep { hinv.lengths.scratch_ok with } rfl rfl
  have hfu0 : s0.core.fuel = s.core.fuel := rfl
  -- 1. full_substitute(h)
  c0_call hSubst; refine ⟨c, F0, s0, R, rfl, hinv0, hm, ?_⟩
  intro r1 s1 m1 hlen1 hr1 hfu1 hu1 hsp1 hm1
  rw [hfu0] at hfu1; fp_steps
  · exact hQ 20#64 s1 m1 hlen1 (Or.inr rfl) hfu1 (fun _ => hu1 hc) (fun h => by cases h) hm1
  have hr1_1 : r1 = 1#64 := hr1.resolve_right hc
  obtain ⟨hinv1, _⟩ := hsp1 hr1_1
  -- 2. full_congruence(h)
  c0_call hCong; refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
  intro r2 s2 m2 hlen2 hr2 hfu2 hu2 hsp2 hm2; fp_steps
  · exact hQ 20#64 s2 m2 hlen2 (Or.inr rfl) (Nat.le_trans hfu2 hfu1) (fun _ => hu2 hc)
      (fun h => by cases h) hm2
  have hr2_1 : r2 = 1#64 := hr2.resolve_right hc
  obtain ⟨hinv2, _⟩ := hsp2 hr2_1
  -- 3. full_substitute(h)
  c0_call hSubst; refine ⟨c, F0, s2, R, rfl, hinv2, hm2, ?_⟩
  intro r3 s3 m3 hlen3 hr3 hfu3 hu3 hsp3 hm3; fp_steps
  · exact hQ 20#64 s3 m3 hlen3 (Or.inr rfl) (by omega) (fun _ => hu3 hc)
      (fun h => by cases h) hm3
  have hr3_1 : r3 = 1#64 := hr3.resolve_right hc
  obtain ⟨hinv3, _⟩ := hsp3 hr3_1
  -- 4. full_sweep_sat(h)
  c0_call hSweep; refine ⟨c, F0, s3, R, rfl, hinv3, hm3, ?_⟩
  intro r4 s4 m4 hlen4 hr4 hfu4 hu4 hsp4 hm4; fp_steps
  · exact hQ 20#64 s4 m4 hlen4 (Or.inr rfl) (by omega) (fun _ => hu4 hc)
      (fun h => by cases h) hm4
  have hr4_1 : r4 = 1#64 := hr4.resolve_right hc
  obtain ⟨hinv4, _⟩ := hsp4 hr4_1
  -- 5. full_transitive(h)
  c0_call hTrans; refine ⟨c, F0, s4, R, rfl, hinv4, hm4, ?_⟩
  intro r5 s5 m5 hlen5 hr5 hfu5 hu5 hsp5 hm5; fp_steps
  · exact hQ 20#64 s5 m5 hlen5 (Or.inr rfl) (by omega) (fun _ => hu5 hc)
      (fun h => by cases h) hm5
  have hr5_1 : r5 = 1#64 := hr5.resolve_right hc
  obtain ⟨hinv5, _⟩ := hsp5 hr5_1
  -- 6. full_probe_run(h, 64ULL)
  c0_call hPRun; refine ⟨c, F0, s5, R, rfl, hinv5, hm5, ?_⟩
  intro r6 s6 m6 hlen6 hr6 hfu6 hu6 hsp6 hm6; fp_steps
  · exact hQ 20#64 s6 m6 hlen6 (Or.inr rfl) (by omega) (fun _ => hu6 hc)
      (fun h => by cases h) hm6
  have hr6_1 : r6 = 1#64 := hr6.resolve_right hc
  obtain ⟨hinv6, _⟩ := hsp6 hr6_1
  -- 7. full_vivify(h, 1ULL)
  c0_call hViv; refine ⟨c, F0, s6, R, rfl, hinv6, hm6, ?_⟩
  intro r7 s7 m7 hlen7 hr7 hfu7 hu7 hsp7 hm7; fp_steps
  · exact hQ 20#64 s7 m7 hlen7 (Or.inr rfl) (by omega) (fun _ => hu7 hc)
      (fun h => by cases h) hm7
  have hr7_1 : r7 = 1#64 := hr7.resolve_right hc
  obtain ⟨hinv7, _⟩ := hsp7 hr7_1
  -- 8. full_vivify(h, 2ULL)
  c0_call hViv; refine ⟨c, F0, s7, R, rfl, hinv7, hm7, ?_⟩
  intro r8 s8 m8 hlen8 hr8 hfu8 hu8 hsp8 hm8; fp_steps
  · exact hQ 20#64 s8 m8 hlen8 (Or.inr rfl) (by omega) (fun _ => hu8 hc)
      (fun h => by cases h) hm8
  have hr8_1 : r8 = 1#64 := hr8.resolve_right hc
  obtain ⟨hinv8, _⟩ := hsp8 hr8_1
  -- 9. full_vivify(h, 0ULL)
  c0_call hViv; refine ⟨c, F0, s8, R, rfl, hinv8, hm8, ?_⟩
  intro r9 s9 m9 hlen9 hr9 hfu9 hu9 hsp9 hm9; fp_steps
  · exact hQ 20#64 s9 m9 hlen9 (Or.inr rfl) (by omega) (fun _ => hu9 hc)
      (fun h => by cases h) hm9
  have hr9_1 : r9 = 1#64 := hr9.resolve_right hc
  exact hQ 1#64 s9 m9 hlen9 (Or.inl rfl) (by omega) (fun h => by cases h) (fun _ => hsp9 hr9_1) hm9

/-- `Func.wp` proof for `full_eliminate` (`Full.lean:1062-1082`). -/
theorem full_eliminate_wp (Γ : Env)
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, fullEnterDenseSpec a m Q X → Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hFwd : ∀ a m Q X, fullForwardSubSpec a m Q X → Γ "full_forward_sub" [i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, fullBveVarSpec a m Q X → Γ "full_bve_var" [i64, i32] [i64] a m Q X)
    (hFact : ∀ a m Q X, fullFactorSpec a m Q X → Γ "full_factor" [i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ args m Q X, fullEliminateSpec args m Q X → Func.wp Γ full_eliminate_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  unfold Func.wp full_eliminate_body; fp_steps
  c0_call hIsqrt
  intro r_sq _
  fp_steps
  let s0 : FullState :=
    { s with
      scratch := { s.scratch with
        eliminations := s.scratch.eliminations + 1#64
        elim_limit := s.scratch.conflicts + 1500#64 * r_sq } }
  have hinv0 : FullSparseInv c F0 s0 :=
    hinv.with_scratch_keep { hinv.lengths.scratch_ok with } rfl rfl
  have hfu0 : s0.core.fuel = s.core.fuel := rfl
  c0_call hEnter; refine ⟨c, F0, s0, R, rfl, hinv0, hm, ?_⟩
  intro ok s1 m1 hfu1 hfail hok hm1
  rw [hfu0] at hfu1; fp_steps
  · c0_call hFwd; refine ⟨c, F0, s1, R, rfl, hok hc, hm1, ?_⟩
    intro r_fwd s2 m2 hden2 hrfwd hfu2 hufwd hm2; fp_steps
    · c0_call hReb; refine ⟨c, F0, s2, R, rfl, hden2, hm2, ?_⟩
      intro _ s3 m3 hlen3 _ hfu3 _ _ hm3; fp_steps
      exact hQ 20#64 s3 m3 hlen3 (Or.inr rfl) (by omega) (fun _ => hufwd hc)
        (fun h => by cases h) hm3
    -- Post-loop join continuation `J` (unrolled by `fp_steps`)
    have hB : ∀ (v_bv res_v : BitVec 64) (sb : FullState) (mb : Mem 64),
        FullDenseInv c F0 sb → sb.core.fuel.toNat ≤ s.core.fuel.toNat →
        (res_v = 1#64 ∨ res_v = 20#64) → (res_v = 20#64 → F0.Unsat) →
        (FullMem c sb ⋆ R) mb → J (v_bv, res_v, ()) mb := by
      intro v_bv res_v sb mb hden_b hfu_b hres_dom hres_u hmb
      apply hJ; c0_let_simp
      refine wp_join_group (ts := [])
        (fun () mf => ∃ sf : FullState,
          FullDenseInv c F0 sf ∧ sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sf ⋆ R) mf)
        (fun _ ⟨⟩ mf ⟨sf, hden_f, hfu_f, hmf⟩ => by
          fp_steps
          c0_call hReb; refine ⟨c, F0, sf, R, rfl, hden_f, hmf, ?_⟩
          intro rr s_end m_end hlen_e hrr_dom hfu_e hu_e hsp_e hm_e
          fp_steps
          · exact hQ 20#64 s_end m_end hlen_e (Or.inr rfl) (by omega) (fun _ => hres_u hc)
              (fun h => by cases h) hm_e
          · exact hQ 20#64 s_end m_end hlen_e (Or.inr rfl) (by omega) (fun _ => hu_e hc)
              (fun h => by cases h) hm_e
          · have hrr01 : rr = 0#64 ∨ rr = 1#64 := by
              rcases hrr_dom with h0 | h1 | h20
              · exact Or.inl h0
              · exact Or.inr h1
              · exact absurd h20 (by assumption)
            obtain ⟨hsp_end, hcl_end⟩ := hsp_e hrr01
            exact hQ 20#64 s_end m_end hlen_e (Or.inr rfl) (by omega)
              (fun _ => hsp_end.1.inconsistent_unsat hc) (fun h => by cases h) hm_e
          · have hrr01 : rr = 0#64 ∨ rr = 1#64 := by
              rcases hrr_dom with h0 | h1 | h20
              · exact Or.inl h0
              · exact Or.inr h1
              · exact absurd h20 (by assumption)
            exact hQ 1#64 s_end m_end hlen_e (Or.inl rfl) (by omega)
              (fun h => by cases h) (fun _ => hsp_e hrr01) hm_e)
        (fun Jf hJf => by
          fp_steps
          · c0_call hFact; refine ⟨c, F0, sb, R, rfl, hden_b, hmb, ?_⟩
            intro _ sf mf hden_f hfu_f hmf; fp_steps
            exact hJf () mf ⟨sf, hden_f, by omega, hmf⟩
          · exact hJf () mb ⟨sb, hden_b, hfu_b, hmb⟩)
    clear hJ
    -- BVE variable loop (`v < cv && h->oom == 0 && h->fuel > 0`)
    let cv : Nat := s2.core.cur_vars
    have hcv_le_max : cv ≤ c.max_vars := hden2.lengths.core_ok.cur_vars_le
    have hmax_lt32 : c.max_vars < 2 ^ 32 := fullInv_max_vars_lt32 c
    have hcv_lt64 : cv < 2 ^ 64 := by omega
    refine wp_loop_group (ts := [i64])
      (fun rem (v_bv, ()) ml => ∃ st : FullState,
        rem = cv - v_bv.toNat ∧ v_bv.toNat ≤ cv ∧ cv ≤ st.core.cur_vars ∧
        FullDenseInv c F0 st ∧ st.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullMem c st ⋆ R) ml) ?_ ?_
    · -- Loop body (`v < cv && oom == 0 && fuel > 0`)
      rintro L rem ⟨v_bv, ⟨⟩⟩ ml ih ⟨st, rfl, hv_le, hcv_le, hden_t, hfu_t, hml⟩
      fp_steps
      · -- `v < cv && oom == 0 && fuel > 0`
        have hv_lt_cv : v_bv.toNat < cv := by
          have : v_bv.toNat < s2.core.cur_vars % 2 ^ 64 := by assumption
          rw [Nat.mod_eq_of_lt hcv_lt64] at this; exact this
        have hv_lt_fl : v_bv.toNat < st.core.flags.length := by
          rw [hden_t.lengths.core_ok.flags_len]; omega
        have h2v_lt_vals : (v_bv <<< (1 : Nat)).toNat < st.core.vals.length := by
          rw [hden_t.lengths.core_ok.vals_len, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        have hv1_lt64 : v_bv.toNat + 1 < 2 ^ 64 := by omega
        have hv_next_toNat : (v_bv + 1#64).toNat = v_bv.toNat + 1 := by bv_omega
        fp_steps
        · -- Active elim candidate & unassigned: clear `FL_ELIM_C`, call `full_bve_var`
          let st' : FullState :=
            { st with core :=
              { st.core with
                flags := st.core.flags.set v_bv.toNat
                  (st.core.flags[v_bv.toNat] &&& ~~~16#32) } }
          have hden_t' : FullDenseInv c F0 st' :=
            hden_t.with_flags (by simp [hden_t.lengths.core_ok.flags_len])
          have hfu_t' : st'.core.fuel = st.core.fuel := rfl
          have hcv_t' : st'.core.cur_vars = st.core.cur_vars := rfl
          have hv32 : (v_bv.setWidth 32).toNat < st'.core.cur_vars := by
            have hlt32 : v_bv.toNat < 2 ^ 32 := by omega
            have : (v_bv.setWidth 32).toNat = v_bv.toNat := by bv_omega
            rw [hcv_t']; omega
          c0_call hBve; refine ⟨c, F0, st', R, rfl, hden_t', hv32, hm, ?_⟩
          intro br sb mb hden_b hbr_dom hcv_b hfu_b hub hmb
          rw [hfu_t'] at hfu_b; rw [hcv_t'] at hcv_b; fp_steps
          · exact hB v_bv 20#64 sb mb hden_b (by omega) (Or.inr rfl) (fun _ => hub hc) hmb
          · exact hB v_bv 1#64 sb mb hden_b (by omega) (Or.inl rfl) (fun h => by cases h) hmb
          · exact ih (cv - (v_bv + 1#64).toNat) (v_bv + 1#64, ()) mb
              (by rw [hv_next_toNat]; omega)
              ⟨sb, rfl, by rw [hv_next_toNat]; omega, Nat.le_trans hcv_le hcv_b,
                hden_b, by omega, hmb⟩
        · exact ih (cv - (v_bv + 1#64).toNat) (v_bv + 1#64, ()) ml
            (by rw [hv_next_toNat]; omega)
            ⟨st, rfl, by rw [hv_next_toNat]; omega, hcv_le, hden_t, hfu_t, hml⟩
        · exact ih (cv - (v_bv + 1#64).toNat) (v_bv + 1#64, ()) ml
            (by rw [hv_next_toNat]; omega)
            ⟨st, rfl, by rw [hv_next_toNat]; omega, hcv_le, hden_t, hfu_t, hml⟩
      · exact hB v_bv 1#64 st ml hden_t hfu_t (Or.inl rfl) (fun h => by cases h) hml
      · exact hB v_bv 1#64 st ml hden_t hfu_t (Or.inl rfl) (fun h => by cases h) hml
      · exact hB v_bv 1#64 st ml hden_t hfu_t (Or.inl rfl) (fun h => by cases h) hml
    · -- Loop entry
      intro _ hL; fp_steps
      exact hL cv (0#64, ()) m2 ⟨s2, by simp, Nat.zero_le _, Nat.le_refl _,
        hden2, by omega, hm2⟩
  · exact hQ 1#64 s1 m1 (hfail hc).1.lengths (Or.inl rfl) hfu1 (fun h => by cases h)
      (fun _ => hfail hc) hm1

/-- `Func.wp` proof for `full_preprocess` (`Full.lean:1084-1095`). -/
theorem full_preprocess_wp (Γ : Env)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, fullProbeSpec a m Q X → Γ "full_probe" [i64] [i64] a m Q X)
    (hElim : ∀ a m Q X, fullEliminateSpec a m Q X → Γ "full_eliminate" [i64] [i64] a m Q X) :
    ∀ args m Q X, fullPreprocessSpec args m Q X → Func.wp Γ full_preprocess_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_preprocess_body; fp_steps
  c0_call hProp; refine ⟨c, F0, s, R, rfl, hinv, hm, ?_⟩
  intro pr s1 m1 hlen1 hpr_dom hcl1 hfu1 hpr0 hpr1 hpr2 hm1
  have hcl1_0 : s1.core.cur_level = 0 := hcl1.trans hcl0
  fp_steps
  · obtain ⟨hsp1, _, hconf1⟩ := hpr1 hc
    exact hQ 20#64 s1 m1 hlen1 (Or.inr (Or.inr (Or.inr rfl))) hfu1
      (fun _ => hconf1.level0_unsat hsp1.1 hcl1_0) (fun h => by cases h) (fun h => by cases h) hm1
  · exact hQ 0#64 s1 m1 hlen1 (Or.inl rfl) hfu1 (fun h => by cases h) (fun h => by cases h)
      (fun h => by cases h) hm1
  · exact hQ 0#64 s1 m1 hlen1 (Or.inl rfl) hfu1 (fun h => by cases h) (fun h => by cases h)
      (fun h => by cases h) hm1
  · have hpr_eq0 : pr = 0#64 := by
      rcases hpr_dom with h0 | h1 | h2
      · exact h0
      · exact absurd h1 (by assumption)
      · exfalso
        rcases hpr2 h2 with hoom | hfuel
        · exact hoom (by assumption)
        · exact (by assumption : s1.core.fuel ≠ 0#64) hfuel
    exact hQ 10#64 s1 m1 hlen1 (Or.inr (Or.inr (Or.inl rfl))) hfu1 (fun h => by cases h)
      (fun h => by cases h) (fun _ => (hpr0 hpr_eq0).1.extend_len_le) hm1
  have hpr_eq0 : pr = 0#64 := by
    rcases hpr_dom with h0 | h1 | h2
    · exact h0
    · exact absurd h1 (by assumption)
    · exfalso
      rcases hpr2 h2 with hoom | hfuel
      · exact hoom (by assumption)
      · exact (by assumption : s1.core.fuel ≠ 0#64) hfuel
  have hsp1 : FullSparseInv c F0 s1 := (hpr0 hpr_eq0).1
  c0_call hProbe; refine ⟨c, F0, s1, R, rfl, hsp1, hm1, ?_⟩
  intro rp s2 m2 hlen2 hrp_dom hfu2 hup2 hsp2 hm2; fp_steps
  · exact hQ 20#64 s2 m2 hlen2 (Or.inr (Or.inr (Or.inr rfl))) (by omega)
      (fun _ => hup2 hc) (fun h => by cases h) (fun h => by cases h) hm2
  · exact hQ 0#64 s2 m2 hlen2 (Or.inl rfl) (by omega) (fun h => by cases h)
      (fun h => by cases h) (fun h => by cases h) hm2
  · exact hQ 0#64 s2 m2 hlen2 (Or.inl rfl) (by omega) (fun h => by cases h)
      (fun h => by cases h) (fun h => by cases h) hm2
  have hrp1 : rp = 1#64 := hrp_dom.resolve_right (by assumption)
  obtain ⟨hinv2, _⟩ := hsp2 hrp1
  c0_call hElim; refine ⟨c, F0, s2, R, rfl, hinv2, hm2, ?_⟩
  intro re s3 m3 hlen3 hre_dom hfu3 hue3 hsp3 hm3; fp_steps
  · exact hQ 20#64 s3 m3 hlen3 (Or.inr (Or.inr (Or.inr rfl))) (by omega)
      (fun _ => hue3 hc) (fun h => by cases h) (fun h => by cases h) hm3
  · obtain ⟨hinv3, _⟩ := hsp3 (hre_dom.resolve_right (by assumption))
    exact hQ 20#64 s3 m3 hlen3 (Or.inr (Or.inr (Or.inr rfl))) (by omega)
      (fun _ => hinv3.1.inconsistent_unsat hc) (fun h => by cases h) (fun h => by cases h) hm3
  · exact hQ 0#64 s3 m3 hlen3 (Or.inl rfl) (by omega) (fun h => by cases h)
      (fun h => by cases h) (fun h => by cases h) hm3
  · obtain ⟨hinv3, _⟩ := hsp3 (hre_dom.resolve_right (by assumption))
    exact hQ 10#64 s3 m3 hlen3 (Or.inr (Or.inr (Or.inl rfl))) (by omega) (fun h => by cases h)
      (fun h => by cases h) (fun _ => hinv3.extend_len_le) hm3
  · obtain ⟨hinv3, hcl3⟩ := hsp3 (hre_dom.resolve_right (by assumption))
    exact hQ 1#64 s3 m3 hlen3 (Or.inr (Or.inl rfl)) (by omega) (fun h => by cases h)
      (fun _ => ⟨hinv3, hcl3⟩) (fun h => by cases h) hm3

/-- `Func.wp` proof for `full_simplify` (`Full.lean:1097-1106`). -/
theorem full_simplify_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hRed : ∀ a m Q X, fullReduceSpec a m Q X → Γ "full_reduce" [i64, .bool] [i64] a m Q X)
    (hProbe : ∀ a m Q X, fullProbeSpec a m Q X → Γ "full_probe" [i64] [i64] a m Q X)
    (hElim : ∀ a m Q X, fullEliminateSpec a m Q X → Γ "full_eliminate" [i64] [i64] a m Q X) :
    ∀ args m Q X, fullSimplifySpec args m Q X → Func.wp Γ full_simplify_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  unfold Func.wp full_simplify_body
  have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
    obtain ⟨_, hw⟩ := hinv.1.witness
    have h1 := hw.cur_level_le; have h2 := hinv.lengths.core_ok.trail_end_le
    have h3 := hinv.lengths.core_ok.cur_vars_le; have h4 := fullInv_max_vars_lt32 c; omega
  refine wp_join_group
    (fun () m0 => ∃ s0 : FullState,
      FullSparseInv c F0 s0 ∧ s0.core.cur_level = 0 ∧
      s0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s0 ⋆ R) m0)
    (fun _ ⟨⟩ m0 ⟨s0, hinv0, hcl0, hfu0, hm0⟩ => by
      fp_steps
      c0_call hRed; refine ⟨c, F0, s0, R, rfl, hinv0, hm0, ?_⟩
      intro rr s1 m1 hlen1 hrr_dom hfu1 hur1 hsp1 hsp0 hm1; fp_steps
      · exact hQ 20#64 s1 m1 hlen1 (Or.inr (Or.inr rfl)) (by omega)
          (fun _ => hur1 hc) (fun h => by cases h) hm1
      have hinv1 : FullSparseInv c F0 s1 := by
        rcases hrr_dom with h0 | h1 | h20
        · exact hsp0 hcl0 h0
        · exact hsp1 h1
        · exact absurd h20 hc
      c0_call hProbe; refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
      intro rp s2 m2 hlen2 hrp_dom hfu2 hup2 hsp2 hm2; fp_steps
      · exact hQ 20#64 s2 m2 hlen2 (Or.inr (Or.inr rfl)) (by omega)
          (fun _ => hup2 hc) (fun h => by cases h) hm2
      · exact hQ 0#64 s2 m2 hlen2 (Or.inl rfl) (by omega)
          (fun h => by cases h) (fun h => by cases h) hm2
      · exact hQ 0#64 s2 m2 hlen2 (Or.inl rfl) (by omega)
          (fun h => by cases h) (fun h => by cases h) hm2
      have hrp1 : rp = 1#64 := hrp_dom.resolve_right (by assumption)
      obtain ⟨hinv2, _⟩ := hsp2 hrp1
      c0_call hElim; refine ⟨c, F0, s2, R, rfl, hinv2, hm2, ?_⟩
      intro re s3 m3 hlen3 hre_dom hfu3 hue3 hsp3 hm3; fp_steps
      · exact hQ 20#64 s3 m3 hlen3 (Or.inr (Or.inr rfl)) (by omega)
          (fun _ => hue3 hc) (fun h => by cases h) hm3
      · obtain ⟨hinv3, _⟩ := hsp3 (hre_dom.resolve_right (by assumption))
        exact hQ 20#64 s3 m3 hlen3 (Or.inr (Or.inr rfl)) (by omega)
          (fun _ => hinv3.1.inconsistent_unsat hc) (fun h => by cases h) hm3
      · exact hQ 0#64 s3 m3 hlen3 (Or.inl rfl) (by omega)
          (fun h => by cases h) (fun h => by cases h) hm3
      · obtain ⟨hinv3, _⟩ := hsp3 (hre_dom.resolve_right (by assumption))
        exact hQ 1#64 s3 m3 hlen3 (Or.inr (Or.inl rfl)) (by omega)
          (fun h => by cases h) (fun _ => hinv3) hm3)
    (fun J0 hJ0 => by
      fp_steps
      · c0_call hBt; refine ⟨c, F0, s, R, rfl, hinv, Nat.zero_le _, hm, ?_⟩
        intro s0 m0 hinv0 hcl0 hfu0 hm0; fp_steps
        exact hJ0 () m0 ⟨s0, hinv0, hcl0, by rw [hfu0]; exact Nat.le_refl _, hm0⟩
      · have hcl0 : s.core.cur_level = 0 := by c0_bound
        exact hJ0 () m ⟨s, hinv, hcl0, Nat.le_refl _, hm⟩)

end TopOrchestrators1

end LeanQbe.T.Examples.Kissat.Full
