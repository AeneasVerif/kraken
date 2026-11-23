module

public import LeanQbe.T.Examples.Kissat.FullM7SearchProof2
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import LeanQbe.T.Logic.C0Step
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M7 Search Parity Closed `ModuleOk` & Concrete UNSAT NV (`FullM7SearchProof`)

Combines all `15` parametric `(Γ : Env)` `Func.wp` proofs from `FullM7SearchProof{0,1,2}` and the
`8` extern `FullSpec*` specs into a closed `23`-row `SpecTable`:
- `m7SearchSpecTable` (`23` rows, all `noExit = true`), `m7SearchEnv`, `m7SearchEnv_noExit`.
- `m7Search_tableImpl` and `m7Search_moduleOk : ModuleOk m7SearchEnv m7SearchModule`.
- Parametric drop-in `Fn` handles (`m7LuckyLateFn_dropin_wp`, `m7RandecVarFn_dropin_wp`,
  `m7DecideFn_dropin_wp`, `m7SwitchModeFn_dropin_wp`).
- Concrete `Mem 64` UNSAT non-vacuity (`nv_m7_tumble`, `nv_m7_lucky_late`, `nv_m7_randec_step`,
  `nv_m7_decide`, `nv_m7_switch_mode`) with `XPost := fun _ _ _ _ => False`.

> **Caller Precondition (Single-Invocation Guard)**: `full_lucky_late_m7` MUST run **ONCE**
> before the main search loop starts (e.g., at pre-search root initialization), **NEVER** inside
> the inner decision/conflict loop. Calling it inside the search loop repeatedly invokes level-0
> lucky probing and full restarts/backtracks on every decision iteration.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7Search

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open scoped LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Closed `23`-Row `SpecTable`, `Env`, `TableImpl` & `ModuleOk` -/

/-- Closed `23`-row specification table covering `m7Search_fns` (`15` fns) and
`m7SearchExterns` (`8` externs), all with `noExit = true`. -/
def m7SearchSpecTable : List SpecEntry :=
  [ .ofFn full_lcg_next_m7 m7LcgNextSpec true
  , .ofFn full_m7_get64 m7Get64Spec true
  , .ofFn full_m7_set64 m7Set64Spec true
  , .ofFn full_m7_state_init m7StateInitSpec true
  , .ofFn full_log10_q16_m7 m7Log10Q16Spec true
  , .ofFn full_tumble_clause_m7 m7TumbleClauseSpec true
  , .ofFn full_tumble_clauses_m7 m7TumbleClausesSpec true
  , .ofFn full_tumble_m7 m7TumbleSpec true
  , .ofFn full_lucky_polar_m7 fullLuckyPolarSpec true
  , .ofFn full_lucky_late_m7 m7LuckyLateSpec true
  , .ofFn full_randec_step_m7 m7RandecStepSpec true
  , .ofFn full_randec_var_m7 m7RandecVarSpec true
  , .ofFn full_decide_m7 m7DecideSpec true
  , .ofFn full_ema_swap_m7 m7EmaSwapSpec true
  , .ofFn full_switch_mode_m7 m7SwitchModeSpec true
  , ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  , ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
  , ⟨"full_heap_down", [i64, i32], [], fullHeapDownSpec, true⟩
  , ⟨"full_next_dec_var", [i64], [i64], fullNextDecVarSpec, true⟩
  , ⟨"full_assign", [i64, i32, i32], [], fullAssignSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  , ⟨"full_lucky_scan", [i64, .bool, .bool], [i64], fullLuckyScanSpec, true⟩
  ]

theorem m7SearchSpecTable_length : m7SearchSpecTable.length = 23 := by t_kernel_rfl

private theorem m7SearchSpecTable_nodup : (m7SearchSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem m7SearchSpecTable_allNoExit : m7SearchSpecTable.all (·.noExit) = true := by
  t_kernel_rfl

theorem m7SearchSpecTable_noExit : ∀ e ∈ m7SearchSpecTable, e.noExit = true :=
  fun e he => List.all_eq_true.mp m7SearchSpecTable_allNoExit e he

/-- Specification environment induced by `m7SearchSpecTable`. -/
def m7SearchEnv : Env := Env.ofTable m7SearchSpecTable

theorem m7SearchEnv_noExit :
    ∀ f as bs xs m Q X X',
      m7SearchEnv f as bs xs m Q X → m7SearchEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m7SearchSpecTable_noExit

private theorem m7_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (i : Nat) (hi : m7SearchSpecTable[i]? = some ⟨nm, as, bs, sp, true⟩)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, sp xs m Q X → m7SearchEnv nm as bs xs m Q X :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) (List.mem_of_getElem? hi)
      m7SearchSpecTable_nodup (by simpa only [SpecEntry.eff, ite_true] using hno xs m Q X hs)

private theorem m7Search_allFns_wf : AllFns Fn.Wf m7Search_fns :=
  ⟨full_lcg_next_m7_wf, full_m7_get64_wf, full_m7_set64_wf, full_m7_state_init_wf,
   full_log10_q16_m7_wf, full_tumble_clause_m7_wf, full_tumble_clauses_m7_wf, full_tumble_m7_wf,
   full_lucky_polar_m7_wf, full_lucky_late_m7_wf, full_randec_step_m7_wf, full_randec_var_m7_wf,
   full_decide_m7_wf, full_ema_swap_m7_wf, full_switch_mode_m7_wf, trivial⟩

/-- Row-by-row `TableImpl` for `m7Search_fns` (`15` fns) against `m7SearchSpecTable`. -/
theorem m7Search_tableImpl :
    TableImpl m7SearchEnv m7Search_fns m7SearchSpecTable := by
  have hLcg := m7_row 0 rfl (fun _ _ _ _ h => m7LcgNextSpec_monoX h)
  have hGet := m7_row 1 rfl (fun _ _ _ _ h => m7Get64Spec_monoX h)
  have hSet := m7_row 2 rfl (fun _ _ _ _ h => m7Set64Spec_monoX h)
  have hInit := m7_row 3 rfl (fun _ _ _ _ h => m7StateInitSpec_monoX h)
  have hLog10 := m7_row 4 rfl (fun _ _ _ _ h => m7Log10Q16Spec_monoX h)
  have hTc := m7_row 5 rfl (fun _ _ _ _ h => m7TumbleClauseSpec_monoX h)
  have hTcs := m7_row 6 rfl (fun _ _ _ _ h => m7TumbleClausesSpec_monoX h)
  have hPol := m7_row 8 rfl
  have hRv := m7_row 11 rfl (fun _ _ _ _ h => m7RandecVarSpec_monoX h)
  have hEma := m7_row 13 rfl (fun _ _ _ _ h => m7EmaSwapSpec_monoX h)
  have hNext := m7_row 15 rfl
  have hIlog := m7_row 16 rfl
  have hHeap := m7_row 17 rfl
  have hNd := m7_row 18 rfl
  have hAss := m7_row 19 rfl
  have hBt := m7_row 20 rfl
  have hProp := m7_row 21 rfl
  have hScan := m7_row 22 rfl
  exact ⟨.of (full_lcg_next_m7_wp m7SearchEnv),
    ⟨.of (full_m7_get64_wp m7SearchEnv),
    ⟨.of (full_m7_set64_wp m7SearchEnv),
    ⟨.of (full_m7_state_init_wp m7SearchEnv hGet hSet),
    ⟨.of (full_log10_q16_m7_wp m7SearchEnv),
    ⟨.of (full_tumble_clause_m7_wp m7SearchEnv hLcg),
    ⟨.of (full_tumble_clauses_m7_wp m7SearchEnv hNext hTc),
    ⟨.of (full_tumble_m7_wp m7SearchEnv hTcs),
    ⟨.of (full_lucky_polar_m7_wp m7SearchEnv hNext),
    ⟨.of (full_lucky_late_m7_wp m7SearchEnv hPol hScan hAss hBt hProp),
    ⟨.of (full_randec_step_m7_wp m7SearchEnv hInit hGet hSet),
    ⟨.of (full_randec_var_m7_wp m7SearchEnv hLcg hInit hGet hSet hLog10),
    ⟨.of (full_decide_m7_wp m7SearchEnv hRv hNd hAss),
    ⟨.of (full_ema_swap_m7_wp m7SearchEnv hInit hGet hSet),
    ⟨.of (full_switch_mode_m7_wp m7SearchEnv hIlog hHeap hEma hLog10), trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- Closed `ModuleOk` certification of `m7SearchModule` (`15` fns + `8` externs) under
`m7SearchEnv`. -/
theorem m7Search_moduleOk : ModuleOk m7SearchEnv m7SearchModule :=
  Env.ofTable_moduleOk m7Search_acyclic m7Search_allFns_wf m7Search_tableImpl

/-! ## 2. Canonical `FullSpec` Drop-In `Fn` Handles -/

/-- Drop-in `Full.fullLuckySpec` WP proof for `full_lucky_late_m7`.
Caller precondition: invoke ONLY ONCE before the solver search loop, never per iteration. -/
theorem m7LuckyLateFn_dropin_wp (Γ : Env)
    (hPolar : EnvSpec Γ "full_lucky_polar_m7" fullLuckyPolarSpec)
    (hScan : EnvSpec Γ "full_lucky_scan" fullLuckyScanSpec)
    (hAssign : EnvSpec Γ "full_assign" fullAssignSpec)
    (hBt : EnvSpec Γ "full_backtrack" fullBacktrackSpec)
    (hProp : EnvSpec Γ "full_propagate" fullPropagateSpec) :
    ∀ a m Q X, Full.fullLuckySpec a m Q X → Func.wp Γ full_lucky_late_m7_body a m Q X :=
  full_lucky_late_m7_dropin_wp Γ hPolar hScan hAssign hBt hProp

/-- Drop-in `Full.fullNextDecVarSpec` WP proof for `full_randec_var_m7`. -/
theorem m7RandecVarFn_dropin_wp (Γ : Env)
    (hLcg : EnvSpec Γ "full_lcg_next_m7" m7LcgNextSpec)
    (hInit : EnvSpec Γ "full_m7_state_init" m7StateInitSpec)
    (hGet : EnvSpec Γ "full_m7_get64" m7Get64Spec)
    (hSet : EnvSpec Γ "full_m7_set64" m7Set64Spec)
    (hLog10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec) :
    ∀ a m Q X, Full.fullNextDecVarSpec a m Q X → Func.wp Γ full_randec_var_m7_body a m Q X :=
  full_randec_var_m7_dropin_wp Γ hLcg hInit hGet hSet hLog10

/-- Drop-in `Full.fullDecideSpec` WP proof for `full_decide_m7`. -/
theorem m7DecideFn_dropin_wp (Γ : Env)
    (hRandec : EnvSpec Γ "full_randec_var_m7" m7RandecVarSpec)
    (hNextDec : EnvSpec Γ "full_next_dec_var" fullNextDecVarSpec)
    (hAssign : EnvSpec Γ "full_assign" fullAssignSpec) :
    ∀ a m Q X, Full.fullDecideSpec a m Q X → Func.wp Γ full_decide_m7_body a m Q X :=
  full_decide_m7_dropin_wp Γ hRandec hNextDec hAssign

/-- Drop-in `Full.fullSwitchModeSpec` WP proof for `full_switch_mode_m7`. -/
theorem m7SwitchModeFn_dropin_wp (Γ : Env)
    (hIlog : EnvSpec Γ "full_ilog10" fullIlog10Spec)
    (hHeapDown : EnvSpec Γ "full_heap_down" fullHeapDownSpec)
    (hEmaSwap : EnvSpec Γ "full_ema_swap_m7" m7EmaSwapSpec)
    (hLog10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec) :
    ∀ a m Q X, Full.fullSwitchModeSpec a m Q X → Func.wp Γ full_switch_mode_m7_body a m Q X :=
  full_switch_mode_m7_dropin_wp Γ hIlog hHeapDown hEmaSwap hLog10

/-! ## 3. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `m7SearchEnv`) -/

private theorem nvSearchF0_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

private theorem nvSearch_entails_0 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) := by
  rw [CNF.entails_clause_def]; intro α hα
  exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))

private theorem nvSearch_witness :
    FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState.core := by
  have hrefs : fullArenaClauseRefsCore nvOneLitState.core = [] := rfl
  have hcv : nvOneLitState.core.cur_vars = 1 := rfl
  have hte : nvOneLitState.core.trail_end = 1 := rfl
  have hcl : nvOneLitState.core.cur_level = 0 := rfl
  have hdm : nvOneLitState.core.dense_mode = 0#64 := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvOneLitState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvOneLitState] at hp
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvOneLitState] at hp
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        exact WatchSliceOk.empty
  exact
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩
      watches := hwat
      cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hte] at hi hj; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · constructor
          · intro h; cases h
          · rintro ⟨i, hi, h⟩; rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · constructor
          · intro h; cases h
          · rintro ⟨i, hi, h⟩; rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact Nat.le_refl 0
      dec_earliest := fun _ j _ hj _ hpos => by
        rw [hte] at hj; obtain rfl : j = 0 := (by omega); exact absurd hpos.1 (by decide)
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact nvSearch_entails_0
      trail_pos_inv := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      level0_rsn_none := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      frame_trail_lt := fun L hL => by rw [hcl] at hL; obtain rfl : L = 0 := (by omega); decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega)
        obtain rfl : L2 = 0 := (by omega); exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne }

private theorem nvSearch_sparseW :
    FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState := by
  have hmv : nvOneLitCfg.max_vars = 1 := rfl
  refine ⟨nvOneLit_lengths, nvSearch_witness, ⟨fun v hv => ?_, fun l hl => ?_⟩,
    fun r hr => by have h : fullArenaClauseRefs nvOneLitState = [] := rfl; simp [h] at hr,
    ⟨FullLastLearnedWf.of_cleared fun i hi => by
      simp only [nvOneLitState, nvOneLitScratch, List.getElem?_replicate, show i < 16 by omega,
        ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩, rfl⟩
  · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
  · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl

private theorem nvSearch_coreInv : FullCoreInv nvOneLitCfg nvOneLitF0 nvOneLitState :=
  ⟨nvOneLit_lengths, [[0], [1]], nvSearch_witness⟩

private theorem nvSearchMem_sep : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
  rw [sep_emp]; exact nvOneLitMem_ok

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_tumble_m7`. -/
theorem nv_m7_tumble :
    Func.wp m7SearchEnv full_tumble_m7_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (_, ()) m' => ∃ ar' rng',
        let s' : FullState :=
          { core := { nvOneLitState.core with arena := ar' }
            scratch := { nvOneLitState.scratch with rng_state := rng' } }
        FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        FullArenaPermEq nvOneLitState.core s'.core ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  exact full_tumble_m7_wp m7SearchEnv
    (m7_row 6 rfl (fun _ _ _ _ h => m7TumbleClausesSpec_monoX h)) _ _ _ _
    (m7TumbleSpec_of nvSearch_sparseW nvSearchMem_sep
      fun _ ar' rng' m' hsp hperm _ hm' => by
        rw [sep_emp] at hm'; exact ⟨ar', rng', hsp, hperm, nvSearchF0_unsat, hm'⟩)

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_lucky_late_m7`. -/
theorem nv_m7_lucky_late :
    Func.wp m7SearchEnv full_lucky_late_m7_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s' : FullState,
        s'.LengthsOk nvOneLitCfg ∧ (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        s'.core.fuel.toNat ≤ nvOneLitState.core.fuel.toNat ∧ s'.core.probing = 0#64 ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  exact full_lucky_late_m7_wp m7SearchEnv (m7_row 8 rfl) (m7_row 22 rfl) (m7_row 19 rfl)
    (m7_row 20 rfl) (m7_row 21 rfl) _ _ _ _
    (m7LuckyLateSpec_of nvSearch_sparseW.toSparse nvSearchMem_sep
      fun r s' m' hlen hr hfl hpr _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hlen, hr, hfl, hpr, nvSearchF0_unsat, hm'⟩)

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_randec_step_m7`. -/
theorem nv_m7_randec_step :
    Func.wp m7SearchEnv full_randec_step_m7_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s' : FullState,
        s'.core = nvOneLitState.core ∧ s'.LengthsOk nvOneLitCfg ∧
        M7StateInitOk s'.scratch.glue_used ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  exact full_randec_step_m7_wp m7SearchEnv
    (m7_row 3 rfl (fun _ _ _ _ h => m7StateInitSpec_monoX h))
    (m7_row 1 rfl (fun _ _ _ _ h => m7Get64Spec_monoX h))
    (m7_row 2 rfl (fun _ _ _ _ h => m7Set64Spec_monoX h))
    _ _ _ _ (m7RandecStepSpec_of nvOneLit_lengths nvSearchMem_sep
      fun s' m' hc hlen _ _ hinit _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hc, hlen, hinit, nvSearchF0_unsat, hm'⟩)

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_decide_m7`. -/
theorem nv_m7_decide :
    Func.wp m7SearchEnv full_decide_m7_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s' : FullState,
        FullCoreInv nvOneLitCfg nvOneLitF0 s' ∧ (r = 0#64 ∨ r = 1#64) ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  exact full_decide_m7_wp m7SearchEnv
    (m7_row 11 rfl (fun _ _ _ _ h => m7RandecVarSpec_monoX h))
    (m7_row 18 rfl) (m7_row 19 rfl)
    _ _ _ _ (m7DecideSpec_of nvSearch_coreInv nvSearchMem_sep
      fun r _ _ _ _ _ _ _ _ _ _ _ _ _ m' hinv _ hr _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hinv, hr, nvSearchF0_unsat, hm'⟩)

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_switch_mode_m7`. -/
theorem nv_m7_switch_mode :
    Func.wp m7SearchEnv full_switch_mode_m7_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s' : FullState,
        s'.core = nvOneLitState.core ∧ s'.LengthsOk nvOneLitCfg ∧
        FullProbeScratchPres nvOneLitState s' ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  exact full_switch_mode_m7_wp m7SearchEnv (m7_row 16 rfl) (m7_row 17 rfl)
    (m7_row 13 rfl (fun _ _ _ _ h => m7EmaSwapSpec_monoX h))
    (m7_row 4 rfl (fun _ _ _ _ h => m7Log10Q16Spec_monoX h))
    _ _ _ _ (m7SwitchModeSpec_of nvOneLit_lengths nvSearchMem_sep
      fun s' m' hc hlen hps _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hc, hlen, hps, nvSearchF0_unsat, hm'⟩)

end LeanQbe.T.Examples.Kissat.FullM7Search
