module

public import LeanQbe.T.Examples.Kissat.FullM6TiersProof0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.ControlComb
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat Wave 2 `PR-W2A` (`RC-19`) `Func.wp` Proofs — Part 1b (`FullM6TiersProof1b`)

Proves `Func.wp` (strictly UNSAT-only, ZERO SAT/model proofs) for the remaining `5` Wave-2
inprocessing orchestrators in `FullM6Tiers`:
1. `full_probe_m6` against `m6ProbeInitSpec` (tick budgeting, `M6_WM_REDUCE_CONFL` cooldown skip,
   `delay[4]` adaptive backoff on congruence/sweep/vivifyirr, level-0 backtrack when `initial`).
2. `full_probe` against `Full.fullProbeSpec`.
3. `full_elim_bve_m6` against `m6ElimBveSpec`.
4. `full_eliminate_m6` against `m6ElimInitSpec` (`M6_WM_REDUCE_CONFL` skip + tick budget).
5. `full_eliminate` against `Full.fullEliminateSpec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6Tiers

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped FullArenaTactics
open Kraken.Bedrock2.Test

/-! ## 1. Specs & Pure Helpers -/

/-- Probing specification allowing `initial = true` at positive decision level (calling
`full_backtrack(h, 0)` before returning `1`), matching `Full.fullProbeSpec` when `false`. -/
def m6ProbeInitSpec : Spec [i64, .bool] [i64] := fun (h, initial, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (initial = false → s.core.cur_level = 0) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Dense-mode BVE loop specification for `full_elim_bve_m6(h, bve_lim)`. -/
def m6ElimBveSpec : Spec [i64, i64] [i64] := fun (h, _bve_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Elimination specification allowing `initial = true` on non-level-0 entry (`fullEnterDense`
and `fullRebuildWatches` normalize `cur_level = 0`), matching `Full.fullEliminateSpec` if
`initial = false`. -/
def m6ElimInitSpec : Spec [i64, .bool] [i64] := fun (h, initial, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (initial = false → s.core.cur_level = 0) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

private theorem fullCoreState_with_probing {k : FullCoreState} (v : BitVec 64) :
    ({ k with probing := v } : FullCoreState).probing = v := rfl

private theorem fullSparseInv_with_probing {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (v : BitVec 64) :
    FullSparseInv c F0 { s with core := { s.core with probing := v } } := by
  obtain ⟨F_cur, hw⟩ := h.1.witness
  let hlen' : ({ s with core := { s.core with probing := v } } : FullState).LengthsOk c :=
    ⟨{ h.lengths.core_ok with vals_len := h.lengths.core_ok.vals_len }, h.lengths.scratch_ok⟩
  refine ⟨⟨hlen', F_cur, { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem fullSparseInv_of_same_arena_m6 {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (hsp : FullSparseInv c F0 s) (hcore' : FullCoreInv c F0 s')
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hpres : FullExtScratchPres s s') : FullSparseInv c F0 s' := by
  refine ⟨hcore', ?_, ?_, ?_, hdm.trans hsp.2.2.2.2⟩
  · exact ⟨fun v hv => by rw [hmrk]; exact hsp.2.1.1 v hv,
      fun l hl => by rw [hlm]; exact hsp.2.1.2 l hl⟩
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseRefsCore
      fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
      fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
    rw [har, hal]; exact hsp.2.2.1
  · exact hsp.2.2.2.1.of_pres hpres fun ref href => by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore at href ⊢; rwa [har, hal]

private theorem fullDenseInv_with_flags_m6 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {fl' : List (BitVec 32)} (hflen : fl'.length = c.max_vars) :
    FullDenseInv c F0 { s with core := { s.core with flags := fl' } } := by
  obtain ⟨F_cur, hw⟩ := h.1.witness
  have hlen' : ({ s with core := { s.core with flags := fl' } } : FullState).LengthsOk c :=
    ⟨{ h.lengths.core_ok with flags_len := hflen }, h.lengths.scratch_ok⟩
  exact ⟨⟨hlen', F_cur, { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem fullSparseInv_of_safetySlice_m6 {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullSparseInv c F0 s) (hlen' : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hpres : FullExtScratchPres s s') : FullSparseInv c F0 s' :=
  h.of_safetySlice hlen' hcore hpres

private theorem fullDenseInv_of_safetySlice_m6 {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullDenseInv c F0 s) (hlen' : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hpres : FullExtScratchPres s s') : FullDenseInv c F0 s' :=
  h.of_safetySlice hlen' hcore hpres

/-! ## 2. Local Tactics (`FullM6Proof1b`) -/

section M6Proof1bTactics

open Lean Elab Tactic in
local elab "m6_to_group" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let rawTy ← Lean.instantiateMVars (← g.getType)
      let ty := rawTy.consumeMData
      if rawTy.isMData then
        let g' ← g.change ty (checkDefEq := false)
        setGoals [g']
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out ++ (← getUnsolvedGoals)
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out ++ (← getUnsolvedGoals)
    setGoals out.toList
  go 500

open Lean Elab Tactic in
local elab "m6_split" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let g ← getMainGoal
    let rawTy ← Lean.instantiateMVars (← g.getType)
    let ty := rawTy.consumeMData
    if rawTy.isMData then
      let g' ← g.change ty (checkDefEq := false)
      replaceMainGoal [g']
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← LeanQbe.T.C0Step.stepOnce; return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  go 100

/-! ## 3. `full_probe_m6` & `full_probe` `Func.wp` Proofs -/

theorem full_probe_m6_wp (Γ : Env)
    (hReady : ∀ a m Q X, m6ExtReadySpec a m Q X →
      Γ "full_m6_ext_ready" [i64] [.bool] a m Q X)
    (hGetWm : ∀ a m Q X, m6GetWmSpec a m Q X →
      Γ "full_m6_get_watermark" [i64, i64] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6SetWmSpec a m Q X →
      Γ "full_m6_set_watermark" [i64, i64, i64] [] a m Q X)
    (hDelay : ∀ a m Q X, m6DelayingSpec a m Q X →
      Γ "full_m6_delaying" [i64, i64] [.bool] a m Q X)
    (hBumpD : ∀ a m Q X, m6SafetyArgVoidSpec i64 a m Q X →
      Γ "full_m6_bump_delay" [i64, i64] [] a m Q X)
    (hRedD : ∀ a m Q X, m6SafetyArgVoidSpec i64 a m Q X →
      Γ "full_m6_reduce_delay" [i64, i64] [] a m Q X)
    (hDticks : ∀ a m Q X, m6DticksSpec a m Q X →
      Γ "full_probe_dticks_m6" [i64, .bool] [i64] a m Q X)
    (hScale : ∀ a m Q X, m6ScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m6" [i64, i64] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, fullSubstituteSpec a m Q X → Γ "full_substitute" [i64] [i64] a m Q X)
    (hCong : ∀ a m Q X, fullCongruenceSpec a m Q X → Γ "full_congruence" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullSweepSatSpec a m Q X → Γ "full_sweep_sat" [i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, fullTransitiveSpec a m Q X → Γ "full_transitive" [i64] [i64] a m Q X)
    (hPRun : ∀ a m Q X, fullProbeRunSpec a m Q X →
      Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, fullVivifySpec a m Q X → Γ "full_vivify" [i64, i64] [i64] a m Q X)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ a m Q X, m6ProbeInitSpec a m Q X → Func.wp Γ full_probe_m6_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hinit, hm, hQ⟩
  -- Step 1: optional `REDUCE_CONFL` cooldown skip when `!initial`, joining into `dticks`
  refine wp_join_group (ts := [])
    (fun () m0 => ∃ s0 : FullState,
      FullSparseInv c F0 s0 ∧ s0.core.fuel = s.core.fuel ∧
      (initial = false → s0.core.cur_level = 0) ∧ (FullMem c s0 ⋆ R) m0)
    (fun _ () m0 ⟨s0, hinv0, hfu0, hcl0, hm0⟩ => ?_)
    (fun _ hJ0 => ?_)
  · clear hm
    c0_hsteps_nogrp
    c0_call hDticks
    refine ⟨c, s0, R, rfl, hinv0.lengths, hm0,
      fun ⟨dticks, ⟨⟩⟩ s1 m1 hcore1 hlen1 hpres1 hm1 => ?_⟩
    dsimp only [fullSafetySlice] at hlen1 hm1
    have hinv1 : FullSparseInv c F0 s1 :=
      fullSparseInv_of_safetySlice_m6 hinv0 hlen1 hcore1 hpres1.1.1
    have hfu1 : s1.core.fuel = s.core.fuel :=
      (congrArg FullCoreState.fuel (fullCoreState_agrees_with_scratch hcore1)).trans hfu0
    have hcl1 : initial = false → s1.core.cur_level = 0 := fun hf =>
      (congrArg FullCoreState.cur_level (fullCoreState_agrees_with_scratch hcore1)).trans (hcl0 hf)
    -- Step 2: optional `!initial` `probings` / `probe_limit` update
    refine wp_join_group (ts := [])
      (fun () m2 => ∃ s2 : FullState,
        FullSparseInv c F0 s2 ∧ s2.core.fuel = s.core.fuel ∧
        (initial = false → s2.core.cur_level = 0) ∧ (FullMem c s2 ⋆ R) m2)
      (fun _ () m2 ⟨s2, hinv2, hfu2, hcl2, hm2⟩ => ?_)
      (fun _ hJ2 => ?_)
    · -- `h->probing = 1ULL` + main probing sequence
      c0_hsteps_nogrp
      let s2p : FullState := { s2 with core := { s2.core with probing := 1#64 } }
      have hinv2p : FullSparseInv c F0 s2p := fullSparseInv_with_probing hinv2 1#64
      -- Step 2a: initial `substitute`
      refine wp_join_group (ts := [])
        (fun () m3 => ∃ s3 : FullState,
          FullSparseInv c F0 s3 ∧ s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          (initial = false → s3.core.cur_level = 0) ∧ (FullMem c s3 ⋆ R) m3)
        (fun _ () m3 ⟨s3, hinv3, hfu3, hcl3, hm3⟩ => ?_)
        (fun _ hJ3 => ?_)
      · -- Step 2b: `do_dense` (`congruence`, `substitute`, `sweep_sat`)
        refine wp_join_group (ts := [.bool]) (fun _ md => md = m3)
          (fun _ (dd, ()) md hmd => ?_)
          (fun _ hJdd => by c0_steps <;> exact hJdd (_, ()) m3 rfl)
        subst md
        refine wp_join_group (ts := [])
          (fun () m6 => ∃ s6 : FullState,
            FullSparseInv c F0 s6 ∧ s6.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (FullMem c s6 ⋆ R) m6)
          (fun _ () m6 ⟨s6, hinv6, hfu6, hm6⟩ => ?_)
          (fun _ hJ6 => ?_)
        · -- Step 2c: post-dense `substitute`
          refine wp_join_group (ts := [])
            (fun () m7 => ∃ s7 : FullState,
              FullSparseInv c F0 s7 ∧ s7.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullMem c s7 ⋆ R) m7)
            (fun _ () m7 ⟨s7, hinv7, hfu7, hm7⟩ => ?_)
            (fun _ hJ7 => ?_)
          · -- Step 2d: `!initial` vs `else if (cur_level > 0)`
            refine wp_join_group (ts := [])
              (fun () m8 => ∃ s8 : FullState,
                FullSparseInv c F0 s8 ∧ s8.core.cur_level = 0 ∧
                s8.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s8 ⋆ R) m8)
              (fun _ () m8 ⟨s8, hinv8, hcl8, hfu8, hm8⟩ => ?_)
              (fun _ hJ8 => ?_)
            · c0_hsteps_nogrp
              let s8p : FullState := { s8 with core := { s8.core with probing := 0#64 } }
              have hinv8p : FullSparseInv c F0 s8p := fullSparseInv_with_probing hinv8 0#64
              c0_call hSetWm
              refine ⟨c, s8p, R, rfl, hinv8p.lengths, by assumption,
                fun () s9 m9 hcore9 hlen9 hpres9 hm9 => ?_⟩
              dsimp only [fullSafetySlice] at hlen9 hm9
              have hinv9 : FullSparseInv c F0 s9 :=
                fullSparseInv_of_safetySlice_m6 hinv8p hlen9 hcore9 hpres9.1.1
              have heq9 : s9.core = s8p.core := fullCoreState_agrees_with_scratch hcore9
              c0_steps
              exact hQ 1#64 s9 m9 hinv9.lengths (by rw [heq9]; exact hfu8) (Or.inl rfl)
                (fun h => by cases h) (fun _ => ⟨hinv9, by rw [heq9]; exact hcl8⟩) hm9
            · m6_split
              · -- `initial = true`: `if (cur_level > 0) full_backtrack(h, 0)`
                m6_split
                · obtain ⟨F_cur7, hw7⟩ := hinv7.1.witness
                  have hmax7 := c.hmaxv; unfold dimacsBound at hmax7
                  have hcl_lt64 : s7.core.cur_level < 2 ^ 64 := by
                    have := hw7.cur_level_le; have := hinv7.lengths.core_ok.trail_end_le
                    have := hinv7.lengths.core_ok.cur_vars_le; omega
                  have htgt0 : (0#64 : BitVec 64).toNat < s7.core.cur_level →
                      (0#64 : BitVec 64).toNat < c.max_vars := by
                    intro _; have := hw7.cur_level_le; have := hinv7.lengths.core_ok.trail_end_le
                    have := hinv7.lengths.core_ok.cur_vars_le; omega
                  c0_call hBt
                  refine ⟨c, s7, R, rfl, hinv7.lengths, hcl_lt64, htgt0, hw7.trail_lits_lt, hm7,
                    fun vals' lvl' rsns' trl' tp' te' prop' cl' unas' sc8 m8
                      hlen8 _ _ hcl8' hpres8 _ _ _ hw8' _ hm8 => ?_⟩
                  have hcl8_0 : cl' = 0 := by rw [hcl8']; exact Nat.min_zero _
                  subst hcl8_0
                  let s8 : FullState :=
                    { core := { s7.core with
                        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
                        trail_end := te', propagated := prop', cur_level := 0,
                        unassigned := unas' }
                      scratch := sc8 }
                  have hinv8 : FullSparseInv c F0 s8 :=
                    fullSparseInv_of_same_arena_m6 hinv7
                      ⟨hlen8, F_cur7, hw8' F0 F_cur7 hw7 (Nat.zero_le _)⟩
                      rfl rfl rfl rfl rfl hpres8.1
                  exact hJ () m8 (by
                    rw [Blocks.get_here]; c0_steps
                    exact hJ8 () m8 ⟨s8, hinv8, rfl, by exact hfu7, hm8⟩)
                · obtain ⟨_, hw7⟩ := hinv7.1.witness
                  have := hw7.cur_level_le; have := hinv7.lengths.core_ok.trail_end_le
                  have := hinv7.lengths.core_ok.cur_vars_le
                  have hmax7 := c.hmaxv; unfold dimacsBound at hmax7
                  have hcl7 : s7.core.cur_level = 0 := by
                    change ¬0 < s7.core.cur_level % 2 ^ 64 at hc
                    rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
                  exact hJ () m7 (by
                    rw [Blocks.get_here]; c0_steps
                    exact hJ8 () m7 ⟨s7, hinv7, hcl7, hfu7, hm7⟩)
              · -- `!initial`: `transitive`, `probe_run`, `vivify 1, 2, 0`
                refine wp_join_group (ts := [])
                  (fun () m9 => ∃ s9 : FullState,
                    FullSparseInv c F0 s9 ∧ s9.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    (FullMem c s9 ⋆ R) m9)
                  (fun _ () m9 ⟨s9, hinv9, hfu9, hm9⟩ => ?_)
                  (fun _ hJ9 => ?_)
                · -- `pbud` ternary join -> `probe_run`
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64]) (fun _ mp => mp = m9)
                    (fun _ (pbud, ()) mp hmp => ?_) ?_
                  · subst mp
                    refine wp_join_group (ts := [])
                      (fun () m10 => ∃ s10 : FullState,
                        FullSparseInv c F0 s10 ∧ s10.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullMem c s10 ⋆ R) m10)
                      (fun _ () m10 ⟨s10, hinv10, hfu10, hm10⟩ => ?_)
                      (fun _ hJ10 => ?_)
                    · -- `vivify 1`
                      c0_hsteps_nogrp
                      c0_call hViv
                      refine ⟨c, F0, s10, R, rfl, hinv10, hm10,
                        fun r11 s11 m11 hinv11 _ _ hfu11 hdom11 hu11 hm11 => ?_⟩
                      c0_hsteps_nogrp
                      · exact hQ 20#64 _ _
                          (fullSparseInv_with_probing hinv11 0#64).lengths
                          (by exact Nat.le_trans hfu11 hfu10) (Or.inr rfl) (fun _ => hu11 hc)
                          (fun h => by cases h) (by assumption)
                      · -- `vivify 2`
                        c0_call hViv
                        refine ⟨c, F0, s11, R, rfl, hinv11, hm11,
                          fun r12 s12 m12 hinv12 hcl12 _ hfu12 hdom12 hu12 hm12 => ?_⟩
                        c0_hsteps_nogrp
                        · exact hQ 20#64 _ _
                            (fullSparseInv_with_probing hinv12 0#64).lengths
                            (by exact Nat.le_trans hfu12 (Nat.le_trans hfu11 hfu10))
                            (Or.inr rfl) (fun _ => hu12 hc) (fun h => by cases h) (by assumption)
                        · -- `if (!full_m6_delaying(h, 3)) { vivify 0; bump/reduce_delay }`
                          refine wp_join_group (ts := [])
                            (fun () m13 => ∃ s13 : FullState,
                              FullSparseInv c F0 s13 ∧ s13.core.cur_level = 0 ∧
                              s13.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s13 ⋆ R) m13)
                            (fun _ () m13 ⟨s13, hinv13, hcl13, hfu13, hm13⟩ =>
                              hJ8 () m13 ⟨s13, hinv13, hcl13, hfu13, hm13⟩)
                            (fun _ hJv3 => ?_)
                          c0_call hDelay
                          refine ⟨c, s12, R, rfl, hinv12.lengths, hm12,
                            fun ⟨d3, ⟨⟩⟩ s13 m13 hcore13 hlen13 hpres13 hm13 => ?_⟩
                          dsimp only [fullSafetySlice] at hlen13 hm13
                          have hinv13 : FullSparseInv c F0 s13 :=
                            fullSparseInv_of_safetySlice_m6 hinv12 hlen13 hcore13 hpres13.1.1
                          have heq13 := fullCoreState_agrees_with_scratch hcore13
                          have hcl13 : s13.core.cur_level = 0 := heq13 ▸ hcl12
                          have hfu13 : s13.core.fuel.toNat ≤ s.core.fuel.toNat := by
                            rw [heq13]; exact Nat.le_trans hfu12 (Nat.le_trans hfu11 hfu10)
                          c0_hsteps_nogrp
                          · exact hJv3 () m13 ⟨s13, hinv13, hcl13, hfu13, hm13⟩
                          · c0_call hViv
                            refine ⟨c, F0, s13, R, rfl, hinv13, hm13,
                              fun r14 s14 m14 hinv14 hcl14 _ hfu14 hdom14 hu14 hm14 => ?_⟩
                            c0_hsteps_nogrp
                            · exact hQ 20#64 _ _
                                (fullSparseInv_with_probing hinv14 0#64).lengths
                                (Nat.le_trans hfu14 hfu13) (Or.inr rfl) (fun _ => hu14 hc)
                                (fun h => by cases h) (by assumption)
                            · m6_to_group
                              refine wp_join_group (ts := [])
                                (fun () m15 => ∃ s15 : FullState,
                                  FullSparseInv c F0 s15 ∧ s15.core.cur_level = 0 ∧
                                  s15.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                  (FullMem c s15 ⋆ R) m15)
                                (fun _ () m15 ⟨s15, hinv15, hcl15, hfu15, hm15⟩ =>
                                  hJv3 () m15 ⟨s15, hinv15, hcl15, hfu15, hm15⟩)
                                (fun _ hJvd => ?_)
                              m6_split
                              · c0_call hRedD
                                refine ⟨c, s14, R, rfl, hinv14.lengths, hm14,
                                  fun () s15 m15 hcore15 hlen15 hpres15 hm15 => ?_⟩
                                dsimp only [fullSafetySlice] at hlen15 hm15
                                have hinv15 :=
                                  fullSparseInv_of_safetySlice_m6 hinv14 hlen15 hcore15 hpres15.1.1
                                have heq15 := fullCoreState_agrees_with_scratch hcore15
                                exact hJvd () m15 ⟨s15, hinv15, heq15 ▸ hcl14,
                                  by rw [heq15]; exact Nat.le_trans hfu14 hfu13, hm15⟩
                              · c0_call hBumpD
                                refine ⟨c, s14, R, rfl, hinv14.lengths, hm14,
                                  fun () s15 m15 hcore15 hlen15 hpres15 hm15 => ?_⟩
                                dsimp only [fullSafetySlice] at hlen15 hm15
                                have hinv15 :=
                                  fullSparseInv_of_safetySlice_m6 hinv14 hlen15 hcore15 hpres15.1.1
                                have heq15 := fullCoreState_agrees_with_scratch hcore15
                                exact hJvd () m15 ⟨s15, hinv15, heq15 ▸ hcl14,
                                  by rw [heq15]; exact Nat.le_trans hfu14 hfu13, hm15⟩
                    · m6_split
                      · c0_call hPRun
                        refine ⟨c, F0, s9, R, rfl, hinv9, hm9,
                          fun r10 s10 m10 hinv10 _ _ hfu10 hdom10 hu10 hm10 => ?_⟩
                        c0_hsteps_nogrp
                        · exact hQ 20#64 _ _
                            (fullSparseInv_with_probing hinv10 0#64).lengths
                            (Nat.le_trans hfu10 hfu9) (Or.inr rfl) (fun _ => hu10 hc)
                            (fun h => by cases h) (by assumption)
                        · exact hJ10 () m10 ⟨s10, hinv10, Nat.le_trans hfu10 hfu9, hm10⟩
                      · exact hJ10 () m9 ⟨s9, hinv9, hfu9, hm9⟩
                  · intro _ hJp; c0_steps <;> exact hJp (_, ()) m9 rfl
                · m6_split
                  · c0_call hTrans
                    refine ⟨c, F0, s7, R, rfl, hinv7, hm7,
                      fun r8 s8 m8 hinv8 _ _ hfu8 hdom8 hu8 hm8 => ?_⟩
                    c0_hsteps_nogrp
                    · exact hQ 20#64 _ _
                        (fullSparseInv_with_probing hinv8 0#64).lengths
                        (Nat.le_trans hfu8 hfu7) (Or.inr rfl) (fun _ => hu8 hc)
                        (fun h => by cases h) (by assumption)
                    · exact hJ9 () m8 ⟨s8, hinv8, Nat.le_trans hfu8 hfu7, hm8⟩
                  · exact hJ9 () m7 ⟨s7, hinv7, hfu7, hm7⟩
          · m6_split
            · c0_call hSubst
              refine ⟨c, F0, s6, R, rfl, hinv6, hm6,
                fun r7 s7 m7 hinv7 hcl7 hfu7 hdom7 hu7 hm7 => ?_⟩
              c0_hsteps_nogrp
              · exact hQ 20#64 _ _ (fullSparseInv_with_probing hinv7 0#64).lengths
                  (Nat.le_trans hfu7 hfu6) (Or.inr rfl) (fun _ => hu7 hc)
                  (fun h => by cases h) (by assumption)
              · exact hJ7 () m7 ⟨s7, hinv7, Nat.le_trans hfu7 hfu6, hm7⟩
            · exact hJ7 () m6 ⟨s6, hinv6, hfu6, hm6⟩
        · m6_split
          · -- `do_dense` (`!initial` or small `irred`, and `num_binary >= 4`)
            refine wp_join_group (ts := [])
              (fun () m4 => ∃ s4 : FullState,
                FullSparseInv c F0 s4 ∧ s4.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                (FullMem c s4 ⋆ R) m4)
              (fun _ () m4 ⟨s4, hinv4, hfu4, hm4⟩ => ?_)
              (fun _ hJ4 => ?_)
            · refine wp_join_group (ts := [])
                (fun () m5 => ∃ s5 : FullState,
                  FullSparseInv c F0 s5 ∧ s5.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  (FullMem c s5 ⋆ R) m5)
                (fun _ () m5 ⟨s5, hinv5, hfu5, hm5⟩ => ?_)
                (fun _ hJ5 => ?_)
              · rw [Blocks.get_here]
                refine wp_join_group (ts := [])
                  (fun () m6 => ∃ s6 : FullState,
                    FullSparseInv c F0 s6 ∧ s6.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    (FullMem c s6 ⋆ R) m6)
                  (fun _ () m6 ⟨s6, hinv6, hfu6, hm6⟩ =>
                    hJ6 () m6 ⟨s6, hinv6, hfu6, hm6⟩)
                  (fun _ hJsw => ?_)
                c0_call hDelay
                refine ⟨c, s5, R, rfl, hinv5.lengths, hm5,
                  fun ⟨d2, ⟨⟩⟩ s5d m5d hcore5d hlen5d hpres5d hm5d => ?_⟩
                dsimp only [fullSafetySlice] at hlen5d hm5d
                have hinv5d := fullSparseInv_of_safetySlice_m6 hinv5 hlen5d hcore5d hpres5d.1.1
                have heq5d := fullCoreState_agrees_with_scratch hcore5d
                have hfu5d : s5d.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [heq5d]; exact hfu5
                c0_hsteps_nogrp
                · exact hJsw () m5d ⟨s5d, hinv5d, hfu5d, hm5d⟩
                · c0_call hSweep
                  refine ⟨c, F0, s5d, R, rfl, hinv5d, hm5d,
                    fun rs sr mr hinv_sr _ hfu_sr _ hu_sr hm_sr => ?_⟩
                  c0_hsteps_nogrp
                  · exact hQ 20#64 _ _ (fullSparseInv_with_probing hinv_sr 0#64).lengths
                      (Nat.le_trans hfu_sr hfu5d) (Or.inr rfl) (fun _ => hu_sr hc)
                      (fun h => by cases h) (by assumption)
                  · m6_to_group
                    refine wp_join_group (ts := [])
                      (fun () m6 => ∃ s6 : FullState,
                        FullSparseInv c F0 s6 ∧ s6.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullMem c s6 ⋆ R) m6)
                      (fun _ () m6 ⟨s6, hinv6, hfu6, hm6⟩ =>
                        hJsw () m6 ⟨s6, hinv6, hfu6, hm6⟩)
                      (fun _ hJsd => ?_)
                    refine wp_join_group (ts := []) (fun () mb => mb = mr)
                      (fun _ () _ hmb => by
                        subst hmb
                        c0_call hBumpD
                        refine ⟨c, sr, R, rfl, hinv_sr.lengths, hm_sr,
                          fun () s6 m6 hcore6 hlen6 hpres6 hm6 => ?_⟩
                        dsimp only [fullSafetySlice] at hlen6 hm6
                        have hinv6 :=
                          fullSparseInv_of_safetySlice_m6 hinv_sr hlen6 hcore6 hpres6.1.1
                        have heq6 := fullCoreState_agrees_with_scratch hcore6
                        exact hJsd () m6
                          ⟨s6, hinv6, by rw [heq6]; exact Nat.le_trans hfu_sr hfu5d, hm6⟩)
                      (fun _ hJbd => by
                        c0_steps
                        · c0_call hRedD
                          refine ⟨c, sr, R, rfl, hinv_sr.lengths, hm_sr,
                            fun () s6 m6 hcore6 hlen6 hpres6 hm6 => ?_⟩
                          dsimp only [fullSafetySlice] at hlen6 hm6
                          have hinv6 :=
                            fullSparseInv_of_safetySlice_m6 hinv_sr hlen6 hcore6 hpres6.1.1
                          have heq6 := fullCoreState_agrees_with_scratch hcore6
                          exact hJsd () m6
                            ⟨s6, hinv6, by rw [heq6]; exact Nat.le_trans hfu_sr hfu5d, hm6⟩
                        · exact hJbd () mr rfl
                        · exact hJbd () mr rfl)
              · m6_split
                · c0_call hSubst
                  refine ⟨c, F0, s4, R, rfl, hinv4, hm4,
                    fun r5 s5 m5 hinv5 _ hfu5 _ hu5 hm5 => ?_⟩
                  c0_hsteps_nogrp
                  · exact hQ 20#64 _ _ (fullSparseInv_with_probing hinv5 0#64).lengths
                      (Nat.le_trans hfu5 hfu4) (Or.inr rfl) (fun _ => hu5 hc)
                      (fun h => by cases h) (by assumption)
                  · exact hJ5 () m5 ⟨s5, hinv5, Nat.le_trans hfu5 hfu4, hm5⟩
                · exact hJ5 () m4 ⟨s4, hinv4, hfu4, hm4⟩
            · c0_call hDelay
              refine ⟨c, s3, R, rfl, hinv3.lengths, hm3,
                fun ⟨d1, ⟨⟩⟩ s3d m3d hcore3d hlen3d hpres3d hm3d => ?_⟩
              dsimp only [fullSafetySlice] at hlen3d hm3d
              have hinv3d := fullSparseInv_of_safetySlice_m6 hinv3 hlen3d hcore3d hpres3d.1.1
              have heq3d := fullCoreState_agrees_with_scratch hcore3d
              have hfu3d : s3d.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [heq3d]; exact hfu3
              c0_hsteps_nogrp
              · exact hJ4 () m3d ⟨s3d, hinv3d, hfu3d, hm3d⟩
              · c0_call hCong
                refine ⟨c, F0, s3d, R, rfl, hinv3d, hm3d,
                  fun rc sc mc hfu_c hrc_dom hinv_c h20_c hm_c => ?_⟩
                c0_hsteps_nogrp
                · obtain ⟨hu_c, hlen_c⟩ := h20_c hc
                  let s_c0 : FullState := { sc with core := { sc.core with probing := 0#64 } }
                  have hlen_c0 : s_c0.LengthsOk c :=
                    ⟨{ hlen_c.core_ok with vals_len := hlen_c.core_ok.vals_len },
                      hlen_c.scratch_ok⟩
                  exact hQ 20#64 s_c0 _ hlen_c0
                    (Nat.le_trans hfu_c hfu3d) (Or.inr rfl) (fun _ => hu_c)
                    (fun h => by cases h) (by assumption)
                · have hinv_sc := hinv_c (hrc_dom.resolve_right hc)
                  m6_to_group
                  refine wp_join_group (ts := [])
                    (fun () m4 => ∃ s4 : FullState,
                      FullSparseInv c F0 s4 ∧ s4.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                      (FullMem c s4 ⋆ R) m4)
                    (fun _ () m4 ⟨s4, hinv4, hfu4, hm4⟩ =>
                      hJ4 () m4 ⟨s4, hinv4, hfu4, hm4⟩)
                    (fun _ hJcd => ?_)
                  refine wp_join_group (ts := []) (fun () mb => mb = mc)
                    (fun _ () _ hmb => by
                      subst hmb
                      c0_call hBumpD
                      refine ⟨c, sc, R, rfl, hinv_sc.lengths, hm_c,
                        fun () s4 m4 hcore4 hlen4 hpres4 hm4 => ?_⟩
                      dsimp only [fullSafetySlice] at hlen4 hm4
                      have hinv4 :=
                        fullSparseInv_of_safetySlice_m6 hinv_sc hlen4 hcore4 hpres4.1.1
                      have heq4 := fullCoreState_agrees_with_scratch hcore4
                      exact hJcd () m4
                        ⟨s4, hinv4, by rw [heq4]; exact Nat.le_trans hfu_c hfu3d, hm4⟩)
                    (fun _ hJbd => by
                      c0_steps
                      · c0_call hRedD
                        refine ⟨c, sc, R, rfl, hinv_sc.lengths, hm_c,
                          fun () s4 m4 hcore4 hlen4 hpres4 hm4 => ?_⟩
                        dsimp only [fullSafetySlice] at hlen4 hm4
                        have hinv4 :=
                          fullSparseInv_of_safetySlice_m6 hinv_sc hlen4 hcore4 hpres4.1.1
                        have heq4 := fullCoreState_agrees_with_scratch hcore4
                        exact hJcd () m4
                          ⟨s4, hinv4, by rw [heq4]; exact Nat.le_trans hfu_c hfu3d, hm4⟩
                      · exact hJbd () mc rfl
                      · exact hJbd () mc rfl)
          · exact hJ6 () m3 ⟨s3, hinv3, hfu3, hm3⟩
      · m6_split
        · c0_call hSubst
          refine ⟨c, F0, s2p, R, rfl, hinv2p, by assumption,
            fun r3 s3 m3 hinv3 hcl3 hfu3 _ hu3 hm3 => ?_⟩
          c0_hsteps_nogrp
          · exact hQ 20#64 _ _ (fullSparseInv_with_probing hinv3 0#64).lengths
              (by rw [hfu2] at hfu3; exact hfu3) (Or.inr rfl) (fun _ => hu3 hc)
              (fun h => by cases h) (by assumption)
          · exact hJ3 () m3 ⟨s3, hinv3, by rw [hfu2] at hfu3; exact hfu3, fun _ => hcl3, hm3⟩
        · exact hJ3 () _ ⟨s2p, hinv2p, by exact hfu2.symm ▸ Nat.le_refl _, hcl2, by assumption⟩
    · m6_split
      · exact hJ2 () m1 ⟨s1, hinv1, hfu1, hcl1, hm1⟩
      · c0_hsteps_nogrp
        c0_call hIlog
        intro logp _ _
        c0_hsteps_nogrp
        let s1p : FullState :=
          { s1 with scratch := { s1.scratch with probings := s1.scratch.probings + 1#64 } }
        have hlen1p : s1p.LengthsOk c :=
          hlen1.with_scratch
            { hlen1.scratch_ok with walk_vals_len := hlen1.scratch_ok.walk_vals_len }
        c0_call hScale
        refine ⟨c, s1p, R, rfl, hlen1p, by assumption,
          fun ⟨sd, ⟨⟩⟩ s2 m2 hcore2 hlen2 hpres2 hm2 => ?_⟩
        dsimp only [fullSafetySlice] at hlen2 hm2
        c0_steps
        subst hpres2
        let s2' : FullState :=
          { s1p with scratch := { s1p.scratch with probe_limit := s1p.scratch.conflicts + sd } }
        have hinv2' : FullSparseInv c F0 s2' :=
          fullSparseInv_of_safetySlice_m6 hinv1
            (hlen2.with_scratch
              { hlen2.scratch_ok with walk_vals_len := hlen2.scratch_ok.walk_vals_len })
            rfl ⟨rfl, rfl⟩
        exact hJ2 () _ ⟨s2', hinv2', hfu1, hcl1, by assumption⟩
  · m6_split
    · exact hJ0 () m ⟨s, hinv, rfl, hinit, hm⟩
    · c0_call hReady
      refine ⟨c, s, R, rfl, hinv.lengths, hm, fun ⟨ok, ⟨⟩⟩ s0 m0 hcore0 hlen0 hpres0 hm0 => ?_⟩
      dsimp only [fullSafetySlice] at hlen0 hm0
      have hinv0 := fullSparseInv_of_safetySlice_m6 hinv hlen0 hcore0 hpres0.1.1.1
      have heq0 := fullCoreState_agrees_with_scratch hcore0
      have hinit_f : initial = false := by
        cases initial with | false => rfl | true => cases hc
      m6_split
      · c0_call hGetWm
        refine ⟨c, s0, R, rfl, hlen0, hm0, fun ⟨wm, ⟨⟩⟩ s0w m0w hcore0w hlen0w hpres0w hm0w => ?_⟩
        dsimp only [fullSafetySlice] at hlen0w hm0w
        have hinv0w := fullSparseInv_of_safetySlice_m6 hinv0 hlen0w hcore0w hpres0w.1.1
        have heq0w := fullCoreState_agrees_with_scratch hcore0w
        c0_hsteps_nogrp
        · c0_steps
          exact hQ 1#64 s0w m0w hlen0w (by rw [heq0w, heq0]; exact Nat.le_refl _) (Or.inl rfl)
            (fun h => by cases h) (fun _ => ⟨hinv0w, by rw [heq0w, heq0]; exact hinit hinit_f⟩)
            hm0w
        · exact hJ0 () m0w ⟨s0w, hinv0w, heq0w.trans heq0 ▸ rfl,
            fun _ => by rw [heq0w, heq0]; exact hinit hinit_f, hm0w⟩
      · exact hJ0 () m0 ⟨s0, hinv0, congrArg FullCoreState.fuel heq0,
          fun _ => by rw [heq0]; exact hinit hinit_f, hm0⟩

theorem full_probe_wp (Γ : Env)
    (hPm6 : ∀ a m Q X, m6ProbeInitSpec a m Q X →
      Γ "full_probe_m6" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullProbeSpec a m Q X → Func.wp Γ full_probe_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  c0_hsteps_nogrp
  c0_call hPm6
  refine ⟨c, F0, s, R, rfl, hinv, fun _ => hcl0, hm, fun r s' m' hlen' hfu' hdom hu h1 hm' => ?_⟩
  c0_steps
  exact hQ r s' m' hlen' hfu' hdom hu h1 hm'

/-! ## 4. `full_elim_bve_m6`, `full_eliminate_m6`, `full_eliminate` `Func.wp` Proofs -/

theorem full_elim_bve_m6_wp (Γ : Env)
    (hBve : ∀ a m Q X, fullBveVarSpec a m Q X → Γ "full_bve_var" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, m6ElimBveSpec a m Q X → Func.wp Γ full_elim_bve_m6_body a m Q X := by
  rintro ⟨h, bve_lim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hden, hm, hQ⟩
  let cv : Nat := s.core.cur_vars
  have hcv_le_max : cv ≤ c.max_vars := hden.lengths.core_ok.cur_vars_le
  have hmax_lt32 : c.max_vars < 2 ^ 32 := fullInv_max_vars_lt32 c
  have hcv_lt64 : cv < 2 ^ 64 := by omega
  m6_to_group
  refine wp_join_group (ts := [i64, i64, i64])
    (fun (_, _, res_v, ()) ml => ∃ sb : FullState,
      FullDenseInv c F0 sb ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (res_v = 1#64 ∨ res_v = 20#64) ∧ (res_v = 20#64 → F0.Unsat) ∧ (FullMem c sb ⋆ R) ml)
    (fun _ (_, _, res_v, ()) ml ⟨sb, hden_b, hfu_b, hdom_b, hres_u, hml⟩ => ?_)
    (fun _ hJb => ?_)
  · c0_steps; exact hQ res_v sb ml hden_b hfu_b hdom_b hres_u hml
  · refine wp_loop_inv (ts := [i64, i64])
      (fun (v_bv, tried, ()) ml => ∃ st : FullState,
        v_bv.toNat ≤ cv ∧ cv ≤ st.core.cur_vars ∧ FullDenseInv c F0 st ∧
        st.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c st ⋆ R) ml)
      (fun (v_bv, _, ()) _ => cv - v_bv.toNat)
      (fun L hL => by
        c0_steps
        exact hL (0#64, 0#64, ()) m
          ⟨s, Nat.zero_le _, Nat.le_refl _, hden, Nat.le_refl _, hm⟩)
      (fun L (v_bv, tried, ()) ml ⟨st, hv_le, hcv_le, hden_t, hfu_t, hml⟩ ih => ?_)
    c0_hsteps_nogrp
    · have hv_lt_cv : v_bv.toNat < cv := by
        have h_lt : v_bv.toNat < s.core.cur_vars % 2 ^ 64 := by c0_bound
        rw [Nat.mod_eq_of_lt hcv_lt64] at h_lt; exact h_lt
      have hv_lt_fl : v_bv.toNat < st.core.flags.length := by
        rw [hden_t.lengths.core_ok.flags_len]; omega
      have h2v_lt_vals : (v_bv <<< (1 : Nat)).toNat < st.core.vals.length := by
        rw [hden_t.lengths.core_ok.vals_len, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      have hv1_lt64 : v_bv.toNat + 1 < 2 ^ 64 := by omega
      have hv_next_toNat : (v_bv + 1#64).toNat = v_bv.toNat + 1 := by bv_omega
      refine wp_join_group (ts := [i64, i64])
        (fun (_, _, ()) ml' => ∃ st' : FullState,
          cv ≤ st'.core.cur_vars ∧ FullDenseInv c F0 st' ∧
          st'.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c st' ⋆ R) ml')
        (fun _ (tried', _, ()) ml' ⟨st', hcv', hden', hfu', hml'⟩ => by
          c0_steps
          exact ih (v_bv + 1#64, tried', ()) ml' (by dsimp only; rw [hv_next_toNat]; omega)
            ⟨st', by rw [hv_next_toNat]; omega, hcv', hden', hfu', hml'⟩)
        (fun _ hJit => ?_)
      c0_hsteps_nogrp
      · let st' : FullState :=
          { st with core :=
            { st.core with
              flags := st.core.flags.set v_bv.toNat
                (st.core.flags[v_bv.toNat] &&& ~~~16#32) } }
        have hden_t' : FullDenseInv c F0 st' :=
          fullDenseInv_with_flags_m6 hden_t (by simp [hden_t.lengths.core_ok.flags_len])
        have hfu_t' : st'.core.fuel = st.core.fuel := rfl
        have hcv_t' : st'.core.cur_vars = st.core.cur_vars := rfl
        have hv32 : (v_bv.setWidth 32).toNat < st'.core.cur_vars := by
          have hlt32 : v_bv.toNat < 2 ^ 32 := by omega
          have : (v_bv.setWidth 32).toNat = v_bv.toNat := by bv_omega
          rw [hcv_t']; omega
        c0_call hBve; refine ⟨c, F0, st', R, rfl, hden_t', hv32, by assumption, ?_⟩
        intro br sb mb hden_b hcv_b hfu_b _ hub hmb
        rw [hfu_t'] at hfu_b; rw [hcv_t'] at hcv_b
        c0_hsteps
        · exact hJb (_, _, 20#64, ()) mb
            ⟨sb, hden_b, by omega, Or.inr rfl, (fun _ => hub hc), hmb⟩
        · exact hJb (_, _, 1#64, ()) mb
            ⟨sb, hden_b, by omega, Or.inl rfl, (fun h => by cases h), hmb⟩
        · exact hJit (tried + 1#64, 1#64, ()) mb
            ⟨sb, Nat.le_trans hcv_le hcv_b, hden_b, by omega, hmb⟩
      · exact hJit (tried, 1#64, ()) ml ⟨st, hcv_le, hden_t, hfu_t, hml⟩
      · exact hJit (tried, 1#64, ()) ml ⟨st, hcv_le, hden_t, hfu_t, hml⟩
    · exact hJb (_, _, 1#64, ()) ml ⟨st, hden_t, hfu_t, Or.inl rfl, (fun h => by cases h), hml⟩
    · exact hJb (_, _, 1#64, ()) ml ⟨st, hden_t, hfu_t, Or.inl rfl, (fun h => by cases h), hml⟩
    · exact hJb (_, _, 1#64, ()) ml ⟨st, hden_t, hfu_t, Or.inl rfl, (fun h => by cases h), hml⟩
    · exact hJb (_, _, 1#64, ()) ml ⟨st, hden_t, hfu_t, Or.inl rfl, (fun h => by cases h), hml⟩

theorem full_eliminate_m6_wp (Γ : Env)
    (hReady : ∀ a m Q X, m6ExtReadySpec a m Q X →
      Γ "full_m6_ext_ready" [i64] [.bool] a m Q X)
    (hGetWm : ∀ a m Q X, m6GetWmSpec a m Q X →
      Γ "full_m6_get_watermark" [i64, i64] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6SetWmSpec a m Q X →
      Γ "full_m6_set_watermark" [i64, i64, i64] [] a m Q X)
    (hDticks : ∀ a m Q X, m6DticksSpec a m Q X →
      Γ "full_elim_dticks_m6" [i64, .bool] [i64] a m Q X)
    (hScale : ∀ a m Q X, m6ScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m6" [i64, i64] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, fullEnterDenseSpec a m Q X → Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hFwd : ∀ a m Q X, fullForwardSubSpec a m Q X → Γ "full_forward_sub" [i64] [i64] a m Q X)
    (hElimBve : ∀ a m Q X, m6ElimBveSpec a m Q X →
      Γ "full_elim_bve_m6" [i64, i64] [i64] a m Q X)
    (hFact : ∀ a m Q X, fullFactorSpec a m Q X → Γ "full_factor" [i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, m6ElimInitSpec a m Q X → Func.wp Γ full_eliminate_m6_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hinit, hm, hQ⟩
  refine wp_join_group (ts := [])
    (fun () m0 => ∃ s0 : FullState,
      FullSparseInv c F0 s0 ∧ s0.core.fuel = s.core.fuel ∧
      (initial = false → s0.core.cur_level = 0) ∧ (FullMem c s0 ⋆ R) m0)
    (fun _ () m0 ⟨s0, hinv0, hfu0, hcl0, hm0⟩ => ?_)
    (fun _ hJ0 => ?_)
  · clear hm
    c0_hsteps_nogrp
    c0_call hDticks
    refine ⟨c, s0, R, rfl, hinv0.lengths, hm0,
      fun ⟨dticks, ⟨⟩⟩ s1 m1 hcore1 hlen1 hpres1 hm1 => ?_⟩
    dsimp only [fullSafetySlice] at hlen1 hm1
    have hinv1 := fullSparseInv_of_safetySlice_m6 hinv0 hlen1 hcore1 hpres1.1.1
    have heq1 := fullCoreState_agrees_with_scratch hcore1
    have hfu1 : s1.core.fuel = s.core.fuel := (congrArg FullCoreState.fuel heq1).trans hfu0
    have hcl1 : initial = false → s1.core.cur_level = 0 := fun hf =>
      (congrArg FullCoreState.cur_level heq1).trans (hcl0 hf)
    refine wp_join_group (ts := [])
      (fun () m2 => ∃ s2 : FullState,
        FullSparseInv c F0 s2 ∧ s2.core.fuel = s.core.fuel ∧ (FullMem c s2 ⋆ R) m2)
      (fun _ () m2 ⟨s2, hinv2, hfu2, hm2⟩ => ?_)
      (fun _ hJ2 => ?_)
    · c0_call hEnter
      refine ⟨c, F0, s2, R, rfl, hinv2, hm2, fun ok s3 m3 hcl3 hfu3 hok hfail hm3 => ?_⟩
      have hfu3_eq : s3.core.fuel = s.core.fuel := hfu3.trans hfu2
      c0_hsplit
      · let saved_pt := s3.scratch.fwd_sub_cnt
        c0_hsteps_nogrp
        c0_call hFwd
        refine ⟨c, F0, s3, R, rfl, hok hc, hm3, fun r_fwd s4 m4 hden4 _ hfu4 _ hufwd hm4 => ?_⟩
        have hfu4_le : s4.core.fuel.toNat ≤ s.core.fuel.toNat := by
          rw [hfu4, hfu3_eq]; exact Nat.le_refl _
        c0_hsteps_nogrp
        m6_split
        · let s4' : FullState := { s4 with scratch := { s4.scratch with fwd_sub_cnt := saved_pt } }
          have hden4' : FullDenseInv c F0 s4' :=
            fullDenseInv_of_safetySlice_m6 hden4
              (hden4.lengths.with_scratch
                { hden4.lengths.scratch_ok with
                  walk_vals_len := hden4.lengths.scratch_ok.walk_vals_len })
              rfl ⟨rfl, rfl⟩
          c0_call hReb
          refine ⟨c, F0, s4', R, rfl, hden4', by assumption,
            fun _ s5 m5 hsp5 hcl5 hfu5 _ _ hm5 => ?_⟩
          c0_steps
          exact hQ 20#64 s5 m5 hsp5 hcl5 (Nat.le_trans hfu5 hfu4_le) (Or.inr rfl)
            (fun _ => hufwd hc) hm5
        · refine wp_join_group (ts := [i64]) (fun _ mb => mb = m)
            (fun _ (bve_lim, ()) mb hmb => ?_) ?_
          · subst mb
            refine wp_join_group (ts := [i64]) (fun _ mc => mc = m)
              (fun _ (bve_lim', ()) mc hmc => ?_) ?_
            · subst mc
              let s4' : FullState :=
                { s4 with scratch := { s4.scratch with fwd_sub_cnt := saved_pt } }
              have hden4' : FullDenseInv c F0 s4' :=
                fullDenseInv_of_safetySlice_m6 hden4
                  (hden4.lengths.with_scratch
                    { hden4.lengths.scratch_ok with
                      walk_vals_len := hden4.lengths.scratch_ok.walk_vals_len })
                  rfl ⟨rfl, rfl⟩
              c0_call hElimBve
              refine ⟨c, F0, s4', R, rfl, hden4', by assumption,
                fun res s5 m5 hden5 hfu5 hdom5 hu5 hm5 => ?_⟩
              refine wp_join_group (ts := [])
                (fun () mf => ∃ sf : FullState,
                  FullDenseInv c F0 sf ∧ sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  (FullMem c sf ⋆ R) mf)
                (fun _ () mf ⟨sf, hden_f, hfu_f, hmf⟩ => ?_)
                (fun _ hJf => ?_)
              · c0_call hReb
                refine ⟨c, F0, sf, R, rfl, hden_f, hmf,
                  fun rr s6 m6 hsp6 hcl6 hfu6 _ hu6 hm6 => ?_⟩
                c0_hsteps_nogrp
                c0_call hSetWm
                refine ⟨c, s6, R, rfl, hsp6.lengths, hm6,
                  fun () s7 m7 hcore7 hlen7 hpres7 hm7 => ?_⟩
                dsimp only [fullSafetySlice] at hlen7 hm7
                have hsp7 := fullSparseInv_of_safetySlice_m6 hsp6 hlen7 hcore7 hpres7.1.1
                have heq7 := fullCoreState_agrees_with_scratch hcore7
                have hcl7 : s7.core.cur_level = 0 := heq7 ▸ hcl6
                have hfu7 : s7.core.fuel.toNat ≤ s.core.fuel.toNat := by
                  rw [heq7]; exact Nat.le_trans hfu6 hfu_f
                c0_hsteps
                · exact hQ 20#64 s7 m7 hsp7 hcl7 hfu7 (Or.inr rfl) (fun _ => hu5 hc) hm7
                · exact hQ 20#64 s7 m7 hsp7 hcl7 hfu7 (Or.inr rfl) (fun _ => hu6 hc) hm7
                · exact hQ 20#64 s7 m7 hsp7 hcl7 hfu7 (Or.inr rfl)
                    (fun _ => hsp7.inconsistent_unsat hc) hm7
                · exact hQ 1#64 s7 m7 hsp7 hcl7 hfu7 (Or.inl rfl) (fun h => by cases h) hm7
              · m6_split
                · m6_to_group
                  refine wp_join_group (ts := []) (fun () mf => mf = m5)
                    (fun _ () _ hmf => by
                      subst hmf
                      c0_call hFact
                      refine ⟨c, F0, s5, R, rfl, hden5, hm5,
                        fun _ sf mf hden_f _ hfu_f _ hmf => ?_⟩
                      exact hJf () mf
                        ⟨sf, hden_f, by rw [hfu_f]; exact Nat.le_trans hfu5 hfu4_le, hmf⟩)
                    (fun _ hJcall => by
                      c0_steps
                      · exact hJcall () m5 rfl
                      · exact hJcall () m5 rfl
                      · exact hJf () m5 ⟨s5, hden5, Nat.le_trans hfu5 hfu4_le, hm5⟩)
                · exact hJf () m5 ⟨s5, hden5, Nat.le_trans hfu5 hfu4_le, hm5⟩
            · intro _ hJbl'; c0_steps
              · exact hJbl' (_, ()) m rfl
              · exact hJbl' (_, ()) m rfl
          · intro _ hJbl; c0_steps
            · exact hJbl (_, ()) m rfl
            · exact hJbl (_, ()) m rfl
      · c0_hsteps_nogrp
        c0_call hSetWm
        refine ⟨c, s3, R, rfl, (hfail hc).lengths, hm3,
          fun () s4 m4 hcore4 hlen4 hpres4 hm4 => ?_⟩
        dsimp only [fullSafetySlice] at hlen4 hm4
        have hsp4 := fullSparseInv_of_safetySlice_m6 (hfail hc) hlen4 hcore4 hpres4.1.1
        have heq4 := fullCoreState_agrees_with_scratch hcore4
        c0_hsteps
        · exact hQ 20#64 s4 m4 hsp4 (heq4 ▸ hcl3) (by rw [heq4, hfu3_eq]; exact Nat.le_refl _)
            (Or.inr rfl) (fun _ => hsp4.inconsistent_unsat hc) hm4
        · exact hQ 1#64 s4 m4 hsp4 (heq4 ▸ hcl3) (by rw [heq4, hfu3_eq]; exact Nat.le_refl _)
            (Or.inl rfl) (fun h => by cases h) hm4
    · m6_split
      · exact hJ2 () m1 ⟨s1, hinv1, hfu1, hm1⟩
      · c0_hsteps_nogrp
        c0_call hIlog
        intro loge _ _
        c0_hsteps_nogrp
        let s1e : FullState :=
          { s1 with scratch := { s1.scratch with eliminations := s1.scratch.eliminations + 1#64 } }
        have hlen1e : s1e.LengthsOk c :=
          hlen1.with_scratch
            { hlen1.scratch_ok with walk_vals_len := hlen1.scratch_ok.walk_vals_len }
        c0_call hScale
        refine ⟨c, s1e, R, rfl, hlen1e, by assumption,
          fun ⟨sd, ⟨⟩⟩ s2 m2 hcore2 hlen2 hpres2 hm2 => ?_⟩
        dsimp only [fullSafetySlice] at hlen2 hm2
        subst hpres2
        c0_steps
        · let s3 : FullState :=
            { s1e with scratch := { s1e.scratch with
              elim_limit := s1e.scratch.conflicts + sd,
              elim_bound := s1e.scratch.elim_bound + 2#64 } }
          have hinv3 : FullSparseInv c F0 s3 :=
            fullSparseInv_of_safetySlice_m6 hinv1
              (hlen2.with_scratch
                { hlen2.scratch_ok with walk_vals_len := hlen2.scratch_ok.walk_vals_len })
              rfl ⟨rfl, rfl⟩
          exact hJ2 () _ ⟨s3, hinv3, hfu1, by assumption⟩
        · let s3 : FullState :=
            { s1e with scratch := { s1e.scratch with elim_limit := s1e.scratch.conflicts + sd } }
          have hinv3 : FullSparseInv c F0 s3 :=
            fullSparseInv_of_safetySlice_m6 hinv1
              (hlen2.with_scratch
                { hlen2.scratch_ok with walk_vals_len := hlen2.scratch_ok.walk_vals_len })
              rfl ⟨rfl, rfl⟩
          exact hJ2 () _ ⟨s3, hinv3, hfu1, by assumption⟩
        · let s3 : FullState :=
            { s1e with scratch := { s1e.scratch with elim_limit := s1e.scratch.conflicts + sd } }
          have hinv3 : FullSparseInv c F0 s3 :=
            fullSparseInv_of_safetySlice_m6 hinv1
              (hlen2.with_scratch
                { hlen2.scratch_ok with walk_vals_len := hlen2.scratch_ok.walk_vals_len })
              rfl ⟨rfl, rfl⟩
          exact hJ2 () _ ⟨s3, hinv3, hfu1, by assumption⟩
  · m6_split
    · exact hJ0 () m ⟨s, hinv, rfl, hinit, hm⟩
    · c0_call hReady
      refine ⟨c, s, R, rfl, hinv.lengths, hm, fun ⟨ok, ⟨⟩⟩ s0 m0 hcore0 hlen0 hpres0 hm0 => ?_⟩
      dsimp only [fullSafetySlice] at hlen0 hm0
      have hinv0 := fullSparseInv_of_safetySlice_m6 hinv hlen0 hcore0 hpres0.1.1.1
      have heq0 := fullCoreState_agrees_with_scratch hcore0
      have hinit_f : initial = false := by
        cases initial with | false => rfl | true => cases hc
      m6_split
      · c0_call hGetWm
        refine ⟨c, s0, R, rfl, hlen0, hm0, fun ⟨wm, ⟨⟩⟩ s0w m0w hcore0w hlen0w hpres0w hm0w => ?_⟩
        dsimp only [fullSafetySlice] at hlen0w hm0w
        have hinv0w := fullSparseInv_of_safetySlice_m6 hinv0 hlen0w hcore0w hpres0w.1.1
        have heq0w := fullCoreState_agrees_with_scratch hcore0w
        c0_hsteps_nogrp
        · c0_steps
          exact hQ 1#64 s0w m0w hinv0w (by rw [heq0w, heq0]; exact hinit hinit_f)
            (by rw [heq0w, heq0]; exact Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0w
        · exact hJ0 () m0w ⟨s0w, hinv0w, heq0w.trans heq0 ▸ rfl,
            fun _ => by rw [heq0w, heq0]; exact hinit hinit_f, hm0w⟩
      · exact hJ0 () m0 ⟨s0, hinv0, congrArg FullCoreState.fuel heq0,
          fun _ => by rw [heq0]; exact hinit hinit_f, hm0⟩

theorem full_eliminate_wp (Γ : Env)
    (hEm6 : ∀ a m Q X, m6ElimInitSpec a m Q X →
      Γ "full_eliminate_m6" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullEliminateSpec a m Q X → Func.wp Γ full_eliminate_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  c0_hsteps_nogrp
  c0_call hEm6
  refine ⟨c, F0, s, R, rfl, hinv, fun _ => hcl0, hm, fun r s' m' hinv' hcl' hfu' hdom hu hm' => ?_⟩
  c0_steps
  exact hQ r s' m' hinv' hcl' hfu' hdom hu hm'

end M6Proof1bTactics

end LeanQbe.T.Examples.Kissat.FullM6Tiers
