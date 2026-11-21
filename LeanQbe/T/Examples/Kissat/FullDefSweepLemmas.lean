module

public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas3
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas5
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Gate Mining + `kitten` Sweeping Packaging & Non-Vacuity

1. Concrete `defSweepKInv` and `defSweepKInv_laws : KittenInvLaws defSweepKInv`.
2. `21`-row `defSweepSpecTable` (`9` owned `FullDefSweep` fns + `12` canonical externs),
   `defSweepEnv := Env.ofTable defSweepSpecTable`, signature/no-exit lemmas, and
   `SpecEntry.Impl` witnesses for all `9/9` functions of `fullDefSweepModule`.
3. Parameterized `mkDefSweepEnv_moduleOk_of_parts` and unconditional
   `defSweepEnv_moduleOk : ModuleOk defSweepEnv fullDefSweepModule`.
4. Concrete `42716`-byte `Mem 64` UNSAT instance (`nvDefSweepCfg`, `nvDefSweepState`,
   `nvDefSweepMem`) with unconditional `XPost := fun _ _ _ _ => False` non-vacuity witnesses
   (`0` SAT proofs).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullDefSweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Concrete `Kitten` Invariant (`defSweepKInv`) -/

/-- Minimal structural scratch invariant satisfying all `KittenInvLaws` for `FullDefSweep`. -/
def defSweepKInv (nv : Nat) (cls : List (Nat × List Nat)) (_ta : Bool) (_ph : KittenPhase)
    (scr : List (BitVec 32)) : Prop :=
  10240 ≤ scr.length ∧ 1 ≤ nv ∧ nv ≤ 128 ∧ cls.length ≤ 512 ∧
  (scr[256 + 2]?.getD 0#32).toNat = cls.length ∧
  (∀ (i : Nat) (hi : i < cls.length),
    (scr[256 + 7712 + i]?.getD 0#32).toNat = (cls[i]'hi).1) ∧
  (∀ c ∈ cls, ∀ l ∈ c.2, l < 2 * nv) ∧
  (scr[256 + 18]?.getD 0#32).toNat ≤ 2 ∧
  ∀ i < (scr[256 + 18]?.getD 0#32).toNat, (scr[256 + 1184 + i]?.getD 0#32).toNat < 2 * nv

/-- `defSweepKInv` satisfies every law required by `KittenInvLaws`. -/
theorem defSweepKInv_laws : KittenInvLaws defSweepKInv where
  cap_ok h := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  orig_nc_eq h := h.2.2.2.2.1
  cl_aux_eq h := h.2.2.2.2.2.1
  lits_lt h := h.2.2.2.2.2.2.1
  nassump_ok h := h.2.2.2.2.2.2.2
  set_nv h h1 hnv hna hlt := by
    refine ⟨?_, h1, by have := h.2.2.1; omega, h.2.2.2.1, ?_, ?_, hlt, ?_, ?_⟩
    · simp only [List.length_set]; exact h.1
    · rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide)]
      exact h.2.2.2.2.1
    · intro i hi
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact h.2.2.2.2.2.1 i hi
    · rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide), hna]
      decide
    · intro i hi
      rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide), hna] at hi
      omega
  set_assumps h hlen hpres hna hlts := by
    refine ⟨hlen ▸ h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_, ?_, h.2.2.2.2.2.2.1, hna, hlts⟩
    · rw [hpres _ (by decide) (by decide) (by decide)]; exact h.2.2.2.2.1
    · intro i hi
      rw [hpres _ (by omega) (by omega) (by omega)]
      exact h.2.2.2.2.2.1 i hi

/-! ## 2. Specification Table (`21` rows), `defSweepEnv`, & Parameterized `ModuleOk` -/

/-- `21`-row specification table: `9` owned `FullDefSweep` functions + `12` canonical externs. -/
def defSweepSpecTable : List SpecEntry :=
  [ ⟨"full_bve_mark_and", [i64, i32, i32, i32, i32], [.bool], fullBveMarkAndDefSpec, true⟩
  , ⟨"full_find_definition", [i64, i32, i32, i32], [], fullFindDefinitionSpec, true⟩
  , ⟨"full_bve_gates", [i64, i32, i32, i32], [], fullBveGatesDefSpec, true⟩
  , ⟨"full_cong_extract", [i64, i64, i64], [i64], fullCongExtractTickSpec, true⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64], fullCongruenceDenseSpec, true⟩
  , ⟨"full_sweep_cone", [i64, i32], [i64], fullSweepConeKittenSpec defSweepKInv, true⟩
  , ⟨"full_sweep_refine_kitten", [i64, i32, i32], [], fullSweepRefineKittenSpec, true⟩
  , ⟨"full_sweep_var", [i64, i32, i64], [i64], fullSweepVarKittenSpec, true⟩
  , ⟨"full_sweep_dense", [i64, i64, i64], [i64], fullSweepDenseSpec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], FullCongSpecs.fullArenaNextSpec, true⟩
  , ⟨"full_has_bin", [i64, i32, i32], [.bool], FullCongSpecs.fullHasBinSpec, true⟩
  , ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64],
      FullCongSpecs.fullCongTryXorIteSpec, true⟩
  , ⟨"full_cong_hash_step", [i64, i64, i64, i64], [.bool],
      FullCongSpecs.fullCongHashStepSpec, true⟩
  , ⟨"full_add_unit", [i64, i32], [.bool], FullSweepVarSpecs.fullAddUnitSpec, true⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64], FullSweepVarSpecs.fullAddBinSpec, true⟩
  , ⟨"full_kitten_init", [i64, i32, i32], [], fullKittenInitSpec defSweepKInv, true⟩
  , ⟨"full_kitten_add_clause", [i64, i32, i64, i32], [.bool],
      fullKittenAddClauseSpec defSweepKInv, true⟩
  , ⟨"full_kitten_solve", [i64, i64], [i64], fullKittenSolveSpec defSweepKInv, true⟩
  , ⟨"full_kitten_core", [i64], [i32], fullKittenCoreSpec defSweepKInv, true⟩
  , ⟨"full_kitten_shrink", [i64], [], fullKittenShrinkSpec defSweepKInv, true⟩
  , ⟨"full_kitten_flip", [i64, i32], [.bool], fullKittenFlipSpec defSweepKInv, true⟩
  ]

/-- Closed specification environment for `fullDefSweepModule`. -/
def defSweepEnv : Env := Env.ofTable defSweepSpecTable

theorem defSweepSpecTable_nodup : (defSweepSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem defSweepSpecTable_noExit : ∀ e ∈ defSweepSpecTable, e.noExit = true := by
  intro e he
  have hall : defSweepSpecTable.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem defSweepSpecTable_sigs :
    (defSweepSpecTable.take 9).map (fun e => (e.name, e.as, e.rs)) =
      full_def_sweep_fns.map (fun f => (f.name, f.as, f.rs)) :=
  rfl

theorem defSweepSpecTable_ext_sigs :
    (defSweepSpecTable.drop 9).map (fun e => ⟨e.name, e.as, e.rs⟩) = fullDefSweepExterns :=
  rfl

theorem defSweepEnv_noExit :
    ∀ f as bs xs m Q X X',
      defSweepEnv f as bs xs m Q X → defSweepEnv f as bs xs m Q X' :=
  Env.ofTable_noExit defSweepSpecTable_noExit

theorem defSweepEnv_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ defSweepSpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → defSweepEnv nm as bs xs m Q X :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) hmem defSweepSpecTable_nodup
      (hno xs m Q X hs)

private theorem defSweep_allFns_wf : AllFns Fn.Wf fullDefSweepModule.fns :=
  ⟨full_bve_mark_and_wf, full_find_definition_wf, full_bve_gates_wf,
   full_cong_extract_wf, full_congruence_dense_wf, full_sweep_cone_wf,
   full_sweep_refine_kitten_wf, full_sweep_var_wf, full_sweep_dense_wf, trivial⟩

theorem defSweep_mark_and_impl :
    SpecEntry.Impl defSweepEnv
      ⟨"full_bve_mark_and", [i64, i32, i32, i32, i32], [.bool], full_bve_mark_and_body⟩
      ⟨"full_bve_mark_and", [i64, i32, i32, i32, i32], [.bool], fullBveMarkAndDefSpec, true⟩ :=
  SpecEntry.Impl.of (full_bve_mark_and_wp defSweepEnv)

theorem defSweep_find_definition_impl :
    SpecEntry.Impl defSweepEnv
      ⟨"full_find_definition", [i64, i32, i32, i32], [], full_find_definition_body⟩
      ⟨"full_find_definition", [i64, i32, i32, i32], [], fullFindDefinitionSpec, true⟩ :=
  SpecEntry.Impl.of (full_find_definition_wp defSweepEnv defSweepKInv_laws
    (defSweepEnv_row (by simp [defSweepSpecTable]) (fun _ _ _ _ h => h))
    (defSweepEnv_row (by simp [defSweepSpecTable]) (fun _ _ _ _ h => h))
    (defSweepEnv_row (by simp [defSweepSpecTable]) (fun _ _ _ _ h => h))
    (defSweepEnv_row (by simp [defSweepSpecTable]) (fun _ _ _ _ h => h))
    (defSweepEnv_row (by simp [defSweepSpecTable]) (fun _ _ _ _ h => h)))

theorem defSweep_bve_gates_impl :
    SpecEntry.Impl defSweepEnv
      ⟨"full_bve_gates", [i64, i32, i32, i32], [], full_bve_gates_body⟩
      ⟨"full_bve_gates", [i64, i32, i32, i32], [], fullBveGatesDefSpec, true⟩ :=
  SpecEntry.Impl.of (full_bve_gates_wp defSweepEnv
    (defSweepEnv_row (by simp [defSweepSpecTable]) (fun _ _ _ _ h => h))
    (defSweepEnv_row (by simp [defSweepSpecTable]) (fun _ _ _ _ h => h)))

theorem defSweep_cong_extract_impl :
    SpecEntry.Impl defSweepEnv
      ⟨"full_cong_extract", [i64, i64, i64], [i64], full_cong_extract_body⟩
      ⟨"full_cong_extract", [i64, i64, i64], [i64], fullCongExtractTickSpec, true⟩ :=
  SpecEntry.Impl.of (full_cong_extract_wp defSweepEnv
    (defSweepEnv_row (by simp [defSweepSpecTable]) (fun _ _ _ _ h => h))
    (defSweepEnv_row (by simp [defSweepSpecTable]) (fun _ _ _ _ h => h))
    (defSweepEnv_row (by simp [defSweepSpecTable]) (fun _ _ _ _ h => h)))

theorem defSweep_congruence_dense_impl :
    SpecEntry.Impl defSweepEnv
      ⟨"full_congruence_dense", [i64, i64], [i64], full_congruence_dense_body⟩
      ⟨"full_congruence_dense", [i64, i64], [i64], fullCongruenceDenseSpec, true⟩ :=
  SpecEntry.Impl.of (full_congruence_dense_wp defSweepEnv
    (defSweepEnv_row (by simp [defSweepSpecTable]) (fun _ _ _ _ h => h))
    (defSweepEnv_row (by simp [defSweepSpecTable]) (fun _ _ _ _ h => h)))

theorem defSweep_sweep_cone_impl :
    SpecEntry.Impl defSweepEnv
      ⟨"full_sweep_cone", [i64, i32], [i64], full_sweep_cone_body⟩
      ⟨"full_sweep_cone", [i64, i32], [i64], fullSweepConeKittenSpec defSweepKInv, true⟩ :=
  SpecEntry.Impl.of (full_sweep_cone_wp defSweepEnv defSweepKInv_laws
    (defSweepEnv_row (by simp [defSweepSpecTable]) (fun _ _ _ _ h => h))
    (defSweepEnv_row (by simp [defSweepSpecTable]) (fun _ _ _ _ h => h)))

theorem defSweep_sweep_refine_impl :
    SpecEntry.Impl defSweepEnv
      ⟨"full_sweep_refine_kitten", [i64, i32, i32], [], full_sweep_refine_kitten_body⟩
      ⟨"full_sweep_refine_kitten", [i64, i32, i32], [], fullSweepRefineKittenSpec, true⟩ :=
  SpecEntry.Impl.of (full_sweep_refine_kitten_wp defSweepEnv)

/-- Parameterized `TableImpl` assembling `[1..7]` from `FullDefSweepLemmas{2..4}` plus
`hVar`/`hDense` (`full_sweep_var`, `full_sweep_dense`). -/
theorem defSweep_tableImpl_of_parts
    (hVar : ∀ args m Q X, fullSweepVarKittenSpec args m Q X →
      Func.wp defSweepEnv full_sweep_var_body args m Q X)
    (hDense : ∀ args m Q X, fullSweepDenseSpec args m Q X →
      Func.wp defSweepEnv full_sweep_dense_body args m Q X) :
    TableImpl defSweepEnv fullDefSweepModule.fns defSweepSpecTable :=
  ⟨defSweep_mark_and_impl, defSweep_find_definition_impl, defSweep_bve_gates_impl,
   defSweep_cong_extract_impl, defSweep_congruence_dense_impl, defSweep_sweep_cone_impl,
   defSweep_sweep_refine_impl, SpecEntry.Impl.of hVar, SpecEntry.Impl.of hDense, trivial⟩

/-- Parameterized `ModuleOk defSweepEnv fullDefSweepModule` given `full_sweep_var` and
`full_sweep_dense`. -/
theorem mkDefSweepEnv_moduleOk_of_parts
    (hVar : ∀ args m Q X, fullSweepVarKittenSpec args m Q X →
      Func.wp defSweepEnv full_sweep_var_body args m Q X)
    (hDense : ∀ args m Q X, fullSweepDenseSpec args m Q X →
      Func.wp defSweepEnv full_sweep_dense_body args m Q X) :
    ModuleOk defSweepEnv fullDefSweepModule :=
  Env.ofTable_moduleOk fullDefSweep_acyclic defSweep_allFns_wf
    (defSweep_tableImpl_of_parts hVar hDense)

private theorem defSweep_sweep_var_wp_env :
    ∀ args m Q X, fullSweepVarKittenSpec args m Q X →
      Func.wp defSweepEnv full_sweep_var_body args m Q X :=
  full_sweep_var_wp defSweepEnv defSweepKInv_laws
    (defSweepEnv_row (by simp [defSweepSpecTable]) (fun _ _ _ _ h => h))
    (defSweepEnv_row (by simp [defSweepSpecTable]) (fun _ _ _ _ h => h))
    (defSweepEnv_row (by simp [defSweepSpecTable]) (fun _ _ _ _ h => h))
    (defSweepEnv_row (by simp [defSweepSpecTable]) (fun _ _ _ _ h => h))
    (defSweepEnv_row (by simp [defSweepSpecTable]) (fun _ _ _ _ h => h))
    (defSweepEnv_row (by simp [defSweepSpecTable]) (fun _ _ _ _ h => h))

private theorem defSweep_sweep_dense_wp_env :
    ∀ args m Q X, fullSweepDenseSpec args m Q X →
      Func.wp defSweepEnv full_sweep_dense_body args m Q X :=
  full_sweep_dense_wp defSweepEnv
    (defSweepEnv_row (by simp [defSweepSpecTable]) (fun _ _ _ _ h => h))

theorem defSweep_sweep_var_impl :
    SpecEntry.Impl defSweepEnv
      ⟨"full_sweep_var", [i64, i32, i64], [i64], full_sweep_var_body⟩
      ⟨"full_sweep_var", [i64, i32, i64], [i64], fullSweepVarKittenSpec, true⟩ :=
  SpecEntry.Impl.of defSweep_sweep_var_wp_env

theorem defSweep_sweep_dense_impl :
    SpecEntry.Impl defSweepEnv
      ⟨"full_sweep_dense", [i64, i64, i64], [i64], full_sweep_dense_body⟩
      ⟨"full_sweep_dense", [i64, i64, i64], [i64], fullSweepDenseSpec, true⟩ :=
  SpecEntry.Impl.of defSweep_sweep_dense_wp_env

/-- Unconditional `ModuleOk` certifying all `9/9` functions of `fullDefSweepModule` against
`defSweepEnv`. -/
theorem defSweepEnv_moduleOk : ModuleOk defSweepEnv fullDefSweepModule :=
  mkDefSweepEnv_moduleOk_of_parts defSweep_sweep_var_wp_env defSweep_sweep_dense_wp_env

/-! ## 3. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT proofs) -/

/-- Concrete `FullCfg` (`max_vars = 1`, `wcap = 1`, `scratch_cap = 10240`, `avail = 42716`). -/
def nvDefSweepCfg : FullCfg where
  hdr := 0x1000#64
  avail := 42716
  mv := 1
  max_vars := 1
  bva_cap := 0
  nc := 2
  arena_cap := 0
  wcap := 1
  delayed_cap := 0
  red_cap := 0
  extend_cap := 0
  scratch_cap := 10240
  hbva := rfl
  hmv := by decide
  hmaxv := by decide
  hnc := by decide
  harena := by decide
  hwcap := by decide
  hdel := by decide
  hred := by decide
  hext := by decide
  hscr := by decide
  havail_fit := by decide
  hsize := by decide

/-- Concrete `10240`-word `scratch_buf` holding complementary binary entries `x0` / `¬x0`. -/
def nvDefSweepScratchBuf : List (BitVec 32) :=
  ((List.replicate 10240 0#32).set 0 0x80000000#32).set 64 0x80000001#32

theorem nvDefSweepScratchBuf_length : nvDefSweepScratchBuf.length = 10240 := by
  unfold nvDefSweepScratchBuf
  rw [List.length_set, List.length_set, List.length_replicate]

/-- Zero-initialized `FullScratch` for `nvDefSweepCfg` carrying `nvDefSweepScratchBuf`. -/
def nvDefSweepScratch : FullScratch where
  heap_len := 0
  scinc := 0#64; rel_period := 0#64; rel_limit := 0#64; rel_wait := 0#64
  rel_u := 0#64; rel_v := 0#64; rel_trigger := 0#64; conflicts := 0#64
  learned_lits := 0#64; min_removed := 0#64; delayed_len := 0; stable := 0#64
  switched := 0#64; mode_count := 0#64; mode_confl_lim := 0#64; mode_tick_lim := 0#64
  mode_saved_ticks := 0#64; search_ticks := 0#64; q_first := 0#64; q_last := 0#64
  q_search_idx := 0#64; q_search_stamp := 0#64; q_cur_stamp := 0#64
  target_assigned := 0#64; best_assigned := 0#64; rephase_limit := 0#64; rephased := 0#64
  reduce_limit := 0#64; reductions := 0#64; tier1 := 0#64; tier2 := 0#64
  restarts := 0#64; restart_limit := 0#64; ema_fast_biased := 0#64; ema_fast_exp := 0#64
  ema_slow_biased := 0#64; ema_slow_exp := 0#64; extend_len := 0; rng_state := 0#64
  chrono_levels := 0#64; otfs_cnt := 0#64; eager_sub_cnt := 0#64; probe_limit := 0#64
  probings := 0#64; elim_limit := 0#64; eliminations := 0#64; elim_bound := 0#64
  iterating := 0#64; hbr_cnt := 0#64; trans_cnt := 0#64; viv_cnt := 0#64
  subst_cnt := 0#64; cong_cnt := 0#64; sweep_cnt := 0#64; bve_cnt := 0#64
  bce_cnt := 0#64; bva_cnt := 0#64; walk_cnt_stat := 0#64; fwd_sub_cnt := 0#64
  fwd_str_cnt := 0#64; ant_sz := 0#64; res_sz := 0#64
  walk_vals := List.replicate 2 0#8
  phases := List.replicate 1 0#8
  phases_target := List.replicate 1 0#8
  phases_best := List.replicate 1 0#8
  walk_best := List.replicate 1 0#8
  heap := List.replicate 1 0#32
  pos := List.replicate 1 0#32
  shrink_stk := List.replicate 1 0#32
  q_prev := List.replicate 1 0#32
  q_next := List.replicate 1 0#32
  q_stamp := List.replicate 1 0#32
  wsort := List.replicate 2 0#32
  work_stk1 := List.replicate 2 0#32
  work_stk2 := List.replicate 2 0#32
  tarjan_mark := List.replicate 2 0#32
  tarjan_reach := List.replicate 2 0#32
  score := List.replicate 1 0#64
  sim_sig := List.replicate 1 0#64
  glue_used := List.replicate 64 0#32
  last_learned := List.replicate 16 0xFFFFFFFF#32
  delayed := []
  red_refs := []
  extend_stk := []
  scratch_buf := nvDefSweepScratchBuf

/-- Concrete dense-mode UNSAT `FullState` (`FL_ACTIVE | FL_SWEEP`, `dense_mode = 1`,
`inconsistent = 1`, `fuel = 1`, zero trail & `TmkZero`) for `nvOneLitF0 = {(x0), (¬x0)}`. -/
def nvDefSweepState : FullState where
  core :=
    { d_cur := 0#64, d_val := 0#64, cur_vars := 1, unassigned := 1#64
      arena_len := 0, wlen := 1, wusable := 0#64, arena_garbage := 0#64
      first_reducible := 0#64, num_irred := 0#64, num_redundant := 0#64, num_binary := 0#64
      unflushed := 0#64, probing := 0#64, trail_end := 0, propagated := 0
      cur_level := 0, fuel := 1#64, confl_ref := 0#64, confl_type := 1#64
      confl_lit0 := 1#64, confl_lit1 := 1#64, tmp_cnt := 0, tmp_len := 0
      min_clr_len := 0, min_clr_full := 0#64, oom := 0#64, dense_mode := 1#64
      inconsistent := 1#64
      vals := [0#8, 0#8]
      lit_mark := [0#8, 0#8]
      mrk := [0#8]
      flags := [1025#32]
      lvl := [0#32]
      rsns := [0xFFFFFFFF#32]
      trl := [0#32]
      trail_pos := [0#32]
      tmp := [0#32]
      min_clr := [0#32]
      frame_trail := [0#32, 0#32]
      frame_dec := [0#32, 0#32]
      wvec := [0#32, 0#32, 0#32, 0#32]
      repr := [0#32, 0#32]
      min_stk := [0#32, 0#32, 0#32, 0#32]
      arena := []
      wstk := [0#32] }
  scratch := nvDefSweepScratch

theorem nvDefSweepState_lengths : nvDefSweepState.LengthsOk nvDefSweepCfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, nvDefSweepScratchBuf_length⟩⟩

def nvDsBlockHdr : List UInt8 :=
  bytes64 [1#64, 2#64, 0#64, 0#64] ++
  bytes64 (Full.hdrTailWords nvDefSweepCfg nvDefSweepState)

def nvDsBlockBytes : List UInt8 :=
  (bytesOf (t := i8) nvDefSweepState.core.vals ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvDefSweepState.scratch.walk_vals ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvDefSweepState.core.lit_mark ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvDefSweepState.core.mrk ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvDefSweepState.scratch.phases ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvDefSweepState.scratch.phases_target ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvDefSweepState.scratch.phases_best ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvDefSweepState.scratch.walk_best ++ List.replicate 7 0)

def nvDsBlockU32A : List UInt8 :=
  (bytesOf (t := i32) nvDefSweepState.core.flags ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvDefSweepState.core.lvl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvDefSweepState.core.rsns ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvDefSweepState.core.trl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvDefSweepState.core.trail_pos ++ List.replicate 4 0)

def nvDsBlockU32B : List UInt8 :=
  (bytesOf (t := i32) nvDefSweepState.core.tmp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvDefSweepState.scratch.heap ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvDefSweepState.scratch.pos ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvDefSweepState.core.min_clr ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvDefSweepState.scratch.shrink_stk ++ List.replicate 4 0)

def nvDsBlockU32C : List UInt8 :=
  (bytesOf (t := i32) nvDefSweepState.scratch.q_prev ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvDefSweepState.scratch.q_next ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvDefSweepState.scratch.q_stamp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvDefSweepState.core.frame_trail ++ List.replicate 0 0) ++
  (bytesOf (t := i32) nvDefSweepState.core.frame_dec ++ List.replicate 0 0)

def nvDsBlockWvec : List UInt8 :=
  bytesOf (t := i32) nvDefSweepState.core.wvec ++
  bytesOf (t := i32) nvDefSweepState.core.repr ++
  bytesOf (t := i32) nvDefSweepState.scratch.wsort ++
  bytesOf (t := i32) nvDefSweepState.scratch.work_stk1 ++
  bytesOf (t := i32) nvDefSweepState.scratch.work_stk2 ++
  bytesOf (t := i32) nvDefSweepState.scratch.tarjan_mark ++
  bytesOf (t := i32) nvDefSweepState.scratch.tarjan_reach ++
  bytes64 nvDefSweepState.scratch.score ++
  bytes64 nvDefSweepState.scratch.sim_sig

def nvDsBlockTail : List UInt8 :=
  bytesOf (t := i32) nvDefSweepState.core.min_stk ++
  bytesOf (t := i32) nvDefSweepState.scratch.glue_used ++
  bytesOf (t := i32) nvDefSweepState.scratch.last_learned ++
  bytesOf (t := i32) nvDefSweepState.core.arena ++
  bytesOf (t := i32) nvDefSweepState.core.wstk ++
  bytesOf (t := i32) nvDefSweepState.scratch.delayed ++
  bytesOf (t := i32) nvDefSweepState.scratch.red_refs ++
  bytesOf (t := i32) nvDefSweepState.scratch.extend_stk ++
  bytesOf (t := i32) nvDefSweepState.scratch.scratch_buf ++
  List.replicate 0 0

/-- Concrete `42716`-byte image encoding `nvDefSweepCfg` and `nvDefSweepState`. -/
def nvDefSweepBytes : List UInt8 :=
  nvDsBlockHdr ++ nvDsBlockBytes ++ nvDsBlockU32A ++ nvDsBlockU32B ++
  nvDsBlockU32C ++ nvDsBlockWvec ++ nvDsBlockTail

/-- Concrete `Mem 64` heap mapped at `nvDefSweepCfg.hdr` (`0x1000#64`). -/
def nvDefSweepMem : Mem 64 := nvDefSweepBytes.At nvDefSweepCfg.hdr

theorem nvDefSweepBytes_length : nvDefSweepBytes.length = 42716 := by
  simp only [nvDefSweepBytes, nvDsBlockHdr, nvDsBlockBytes, nvDsBlockU32A, nvDsBlockU32B,
    nvDsBlockU32C, nvDsBlockWvec, nvDsBlockTail, nvDefSweepState, nvDefSweepScratch,
    List.length_append, List.length_replicate, bytesOf_length, bytes64_length,
    Full.hdrTailWords_length, nvDefSweepScratchBuf_length, List.length_cons, List.length_nil]
  rfl

theorem nvDefSweepF0_unsat : Full.nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [Full.nvOneLitF0, cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [Full.nvOneLitF0, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

theorem nvDefSweepMem_ok : FullMem nvDefSweepCfg nvDefSweepState nvDefSweepMem := by
  let c := nvDefSweepCfg; let s := nvDefSweepState
  have hvb : valsBytes c.max_vars - 2 * c.max_vars = 6 := by decide
  have hmb : markBytes c.max_vars - c.max_vars = 7 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 0 := by decide
  have hmv1 : BitVec.ofNat 64 c.max_vars = 1#64 := rfl
  have hmv2 : BitVec.ofNat 64 (2 * c.max_vars) = 2#64 := rfl
  have hmv4 : BitVec.ofNat 64 (4 * c.max_vars) = 4#64 := rfl
  have hmv8 : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 8#64 := rfl
  have hHdr : nvDsBlockHdr.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s))
        (nvDsBlockHdr.At c.hdr) :=
    Full.nv_join_pair
      (Full.nv_arr64_p (a := c.hdr) (xs := [1#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
      (Full.nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide))
      (by decide) (by decide)
  have hBytes : nvDsBlockBytes.length = 64 ∧
      (FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ c.padBytes)
        (nvDsBlockBytes.At c.pVals) := by
    have h1 := Full.nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 2 6 rfl
      (by decide)
    have h2 := Full.nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 2 6 rfl
      (by decide)
    have h3 := Full.nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 2 6 rfl
      (by decide)
    have h4 := Full.nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 1 7 rfl
      (by decide)
    have h5 := Full.nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 1 7 rfl
      (by decide)
    have h6 := Full.nv_arr_pad_p (t := i8) (a := c.pPhasesTarget)
      (xs := s.scratch.phases_target) 1 7 rfl (by decide)
    have h7 := Full.nv_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best)
      1 7 rfl (by decide)
    have h8 := Full.nv_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best)
      1 7 rfl (by decide)
    let pB1 : Mem 64 → Prop :=
      region (c.pVals + 2#64) 6 ⋆ region (c.pWalkVals + 2#64) 6 ⋆
      region (c.pLitMark + 2#64) 6 ⋆ region (c.pMark + 1#64) 7
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_sep_reorg (Full.nv_join_pair h123 h4 (by decide) (by decide))
      (Q := (FullCoreByteArrs c s.core ⋆ array (t := i8) c.pWalkVals s.scratch.walk_vals) ⋆ pB1)
      fun _ hm => Full.nv_zip4 hm
    have h12345 := Full.nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := Full.nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := Full.nv_join_pair h123456 h7 (by decide) (by decide)
    have hall := Full.nv_join_pair h1234567 h8 (by decide) (by decide)
    exact Full.nv_sep_reorg hall fun _ hm => by
      have hfin := Full.nv_zip4_tail hm
      unfold FullScrByteArrs FullCfg.padBytes
      rw [hvb, hmb, hmv2, hmv1]
      simpa only [pB1, sep_assoc] using hfin
  have hU32A : nvDsBlockU32A.length = 40 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        (nvDsBlockU32A.At c.pFlags) := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 4 4 rfl
      (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 4 4 rfl
      (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 4 4 rfl
      (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 4 4 rfl
      (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 4 4 rfl
      (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu4, hmv4]; exact sep_ac hm
  have hU32B : nvDsBlockU32B.length = 40 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
        (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
         array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        (nvDsBlockU32B.At c.pTmp) := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 4 4 rfl
      (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 4 4 rfl
      (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 4 4 rfl
      (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 4 4 rfl
      (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk)
      4 4 rfl (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu4, hmv4]; exact sep_ac hm
  have hU32C : nvDsBlockU32C.length = 40 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        (nvDsBlockU32C.At c.pQPrev) := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 4 4 rfl
      (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 4 4 rfl
      (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 4 4 rfl
      (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail)
      8 0 rfl (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 8 0 rfl
      (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu4, hu8, hmv4, hmv8]; exact sep_ac hm
  have hWvec : nvDsBlockWvec.length = 80 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        (nvDsBlockWvec.At c.pWvec) := by
    have h1 := Full.nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 16 rfl (by decide)
    have h2 := Full.nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 8 rfl (by decide)
    have h3 := Full.nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 8 rfl (by decide)
    have h4 := Full.nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 8 rfl
      (by decide)
    have h5 := Full.nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 8 rfl
      (by decide)
    have h6 := Full.nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 8 rfl
      (by decide)
    have h7 := Full.nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach)
      8 rfl (by decide)
    have h8 := Full.nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 8 rfl (by decide)
    have h9 := Full.nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 8 rfl (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := Full.nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := Full.nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := Full.nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := Full.nv_join_pair h1234567 h8 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail : nvDsBlockTail.length = 41300 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        (nvDsBlockTail.At c.pMinStk) := by
    have h1 := Full.nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 16 rfl (by decide)
    have h2 := Full.nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256 rfl
      (by decide)
    have h3 := Full.nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned)
      64 rfl (by decide)
    have h4 := Full.nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 0 rfl (by decide)
    have h5 := Full.nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 4 rfl (by decide)
    have h6 := Full.nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl
      (by decide)
    have h7 := Full.nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl
      (by decide)
    have h8 := Full.nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl
      (by decide)
    have h9 := Full.nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 40960
      (by show 4 * nvDefSweepScratchBuf.length = 40960; rw [nvDefSweepScratchBuf_length])
      (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 0).At c.pSlack) :=
      ⟨rfl, ⟨List.replicate 0 0, by decide, rfl⟩⟩
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := Full.nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := Full.nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := Full.nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := Full.nv_join_pair h1234567 h8 (by decide) (by decide)
    have h123456789 := Full.nv_join_pair h12345678 h9 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h123456789 h10 (by decide) (by decide)) fun _ hm =>
      by unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := Full.nv_join_pair hHdr hBytes (by decide) (by decide)
  have h02 := Full.nv_join_pair h01 hU32A (by decide) (by decide)
  have h03 := Full.nv_join_pair h02 hU32B (by decide) (by decide)
  have h04 := Full.nv_join_pair h03 hU32C (by decide) (by decide)
  have h05 := Full.nv_join_pair h04 hWvec (by decide) (by decide)
  exact (Full.nv_sep_reorg (Q := FullMem c s) (Full.nv_join_pair h05 hTail (by decide) (by decide))
    fun _ hm => by
      unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
        FullScrMetaArrs FullCfg.pad
      exact sep_ac hm).2

theorem nvDefSweep_invW :
    FullDenseInvW nvDefSweepCfg Full.nvOneLitF0 [[0], [1]] nvDefSweepState := by
  have hmv : nvDefSweepCfg.max_vars = 1 := rfl
  have hcv : nvDefSweepState.core.cur_vars = 1 := rfl
  have hte : nvDefSweepState.core.trail_end = 0 := rfl
  have hcl : nvDefSweepState.core.cur_level = 0 := rfl
  have hdm : nvDefSweepState.core.dense_mode ≠ 0#64 := by decide
  have hrefs : fullArenaClauseRefsCore nvDefSweepState.core = [] := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvDefSweepState.core := by
    unfold ModeWatchesInv; rw [ite_eq_right hdm]
    refine DenseWatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
      (fun l1 _ h1 _ _ hp => ?_) (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvDefSweepState] at hp
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvDefSweepState] at hp
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        exact DenseWatchSliceOk.empty
  have hw : FullWitnessInv nvDefSweepCfg Full.nvOneLitF0 [[0], [1]] nvDefSweepState.core :=
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun _ => nvDefSweepF0_unsat
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩
      watches := hwat, cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hte] at hi; omega
      trail_vars_nodup := fun i _ hi => by rw [hte] at hi; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
          simp [nvDefSweepState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
          exact ⟨(fun h => by cases h), (fun ⟨_, hi, _⟩ => by rw [hte] at hi; omega)⟩
      vals_false_iff := fun l hl => by
        rw [hcv] at hl
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
          exact ⟨(fun h => by cases h), (fun ⟨_, hi, _⟩ => by rw [hte] at hi; omega)⟩
      lvl_le := fun i hi => by rw [hte] at hi; omega
      dec_earliest := fun i _ hi => by rw [hte] at hi; omega
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi => by rw [hte] at hi; omega
      trail_pos_inv := fun i hi => by rw [hte] at hi; omega
      level0_rsn_none := fun i hi => by rw [hte] at hi; omega
      frame_trail_lt := fun L hL => by
        rw [hcl] at hL; obtain rfl : L = 0 := (by omega); exact Nat.zero_le _
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega); obtain rfl : L2 = 0 := (by omega)
        exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi => by rw [hte] at hi; omega
      reason_lit_mem := fun i hi => by rw [hte] at hi; omega }
  refine ⟨nvDefSweepState_lengths, hw, ⟨fun v hv => ?_, fun l hl => ?_⟩, fun r hr => ?_,
    ⟨FullLastLearnedWf.of_cleared fun i hi => by
      simp only [nvDefSweepState, nvDefSweepScratch, List.getElem?_replicate,
        show i < 16 by omega, ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩, rfl, hdm⟩
  · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
  · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  · have : fullArenaClauseRefs nvDefSweepState = [] := rfl; simp [this] at hr

theorem nvDefSweep_tmkZero : TmkZero nvDefSweepState := fun v hv => by
  change v < 1 at hv; obtain rfl : v = 0 := (by omega); rfl

private theorem nvDefSweep_entails_00 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0, 0]) := by
  rw [CNF.entails_clause_def]; intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 ⊢
  obtain ⟨lit, hm, heq⟩ := h0
  refine ⟨lit, ?_, heq⟩
  rw [mem_cnfClause_iff] at hm ⊢; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
  exact Or.inl hm

private theorem nvDefSweep_entails_11 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [1, 1]) := by
  rw [CNF.entails_clause_def]; intro α hα
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h1 ⊢
  obtain ⟨lit, hm, heq⟩ := h1
  refine ⟨lit, ?_, heq⟩
  rw [mem_cnfClause_iff] at hm ⊢; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
  exact Or.inl hm

private theorem nvDefSweep_bve_pos :
    ∀ i < 1, FullBveEntryOkW [[0], [1]] nvDefSweepState 0
      (nvDefSweepState.scratch.scratch_buf[i]?.getD 0#32) := by
  intro i hi; obtain rfl : i = 0 := (by omega)
  have hget : nvDefSweepState.scratch.scratch_buf[0]?.getD 0#32 = 0x80000000#32 := by
    change nvDefSweepScratchBuf[0]?.getD 0#32 = 0x80000000#32
    unfold nvDefSweepScratchBuf
    rw [List.getElem?_set_ne (by decide),
      List.getElem?_set_self (by rw [List.length_replicate]; decide)]
    rfl
  rw [hget]
  show if (0x80000000#32 &&& 0x80000000#32) ≠ 0#32 then _ else _
  rw [ite_eq_left (by decide)]
  exact ⟨by decide, nvDefSweep_entails_00⟩

private theorem nvDefSweep_bve_neg :
    ∀ j < 1, FullBveEntryOkW [[0], [1]] nvDefSweepState 1
      (nvDefSweepState.scratch.scratch_buf[64 + j]?.getD 0#32) := by
  intro j hj; obtain rfl : j = 0 := (by omega)
  have hget : nvDefSweepState.scratch.scratch_buf[64]?.getD 0#32 = 0x80000001#32 := by
    change nvDefSweepScratchBuf[64]?.getD 0#32 = 0x80000001#32
    unfold nvDefSweepScratchBuf
    rw [List.getElem?_set_self (by rw [List.length_set, List.length_replicate]; decide)]
    rfl
  rw [hget]
  show if (0x80000001#32 &&& 0x80000000#32) ≠ 0#32 then _ else _
  rw [ite_eq_left (by decide)]
  exact ⟨by decide, nvDefSweep_entails_11⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) for `full_bve_gates`
exercising complementary binary-clause gate extraction `(x0) ∧ (¬x0)`. -/
theorem nv_full_bve_gates :
    Func.wp defSweepEnv full_bve_gates_body (nvDefSweepCfg.hdr, 0#32, 1#32, 1#32, ()) nvDefSweepMem
      (fun () m' => ∃ s',
        FullDenseInvW nvDefSweepCfg Full.nvOneLitF0 [[0], [1]] s' ∧
        FullDefGateUnsat nvDefSweepState 0
          ((s'.scratch.scratch_buf[128]?.getD 0#32).setWidth 64 |||
            ((s'.scratch.scratch_buf[129]?.getD 0#32).setWidth 64 <<< 32))
          ((s'.scratch.scratch_buf[130]?.getD 0#32).setWidth 64 |||
            ((s'.scratch.scratch_buf[131]?.getD 0#32).setWidth 64 <<< 32)) 1 1 ∧
        Full.nvOneLitF0.Unsat ∧ FullMem nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvDefSweepCfg nvDefSweepState ⋆ emp) nvDefSweepMem := by
    rw [sep_emp]; exact nvDefSweepMem_ok
  exact defSweep_bve_gates_impl.2 _ _ _ _
    ⟨nvDefSweepCfg, Full.nvOneLitF0, [[0], [1]], nvDefSweepState, emp, rfl,
     nvDefSweep_invW, by decide, nvDefSweep_tmkZero, by decide, by decide, by decide,
     nvDefSweep_bve_pos, nvDefSweep_bve_neg, hm,
     fun s' m' hd _ _ _ _ _ _ _ hgate hm' => by
       rw [sep_emp] at hm'; exact ⟨s', hd, hgate, nvDefSweepF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) for
`full_find_definition`. -/
theorem nv_full_find_definition :
    Func.wp defSweepEnv full_find_definition_body
      (nvDefSweepCfg.hdr, 0#32, 1#32, 1#32, ()) nvDefSweepMem
      (fun () m' => ∃ s',
        FullDenseInvW nvDefSweepCfg Full.nvOneLitF0 [[0], [1]] s' ∧
        TmkZero s' ∧ Full.nvOneLitF0.Unsat ∧ FullMem nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvDefSweepCfg nvDefSweepState ⋆ emp) nvDefSweepMem := by
    rw [sep_emp]; exact nvDefSweepMem_ok
  exact defSweep_find_definition_impl.2 _ _ _ _
    ⟨nvDefSweepCfg, Full.nvOneLitF0, [[0], [1]], nvDefSweepState, emp, rfl,
     nvDefSweep_invW, by decide, nvDefSweep_tmkZero, by decide, by decide, by decide,
     nvDefSweep_bve_pos, nvDefSweep_bve_neg, hm,
     fun s' m' hd ht _ _ _ _ _ _ _ hm' => by
       rw [sep_emp] at hm'; exact ⟨s', hd, ht, nvDefSweepF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) for
`full_cong_extract`. -/
theorem nv_full_cong_extract :
    Func.wp defSweepEnv full_cong_extract_body
      (nvDefSweepCfg.hdr, 6144#64, 100#64, ()) nvDefSweepMem
      (fun (ret, ()) m' => ∃ scr',
        ret.toNat ≤ 6144 ∧ FullCongSpecs.GateSeqOk [[0], [1]] 1 scr' ret.toNat 0 ∧
        Full.nvOneLitF0.Unsat ∧
        FullMem nvDefSweepCfg
          { nvDefSweepState with scratch := { nvDefSweepState.scratch with scratch_buf := scr' } }
          m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvDefSweepCfg nvDefSweepState ⋆ emp) nvDefSweepMem := by
    rw [sep_emp]; exact nvDefSweepMem_ok
  exact defSweep_cong_extract_impl.2 _ _ _ _
    ⟨nvDefSweepCfg, Full.nvOneLitF0, [[0], [1]], nvDefSweepState, emp, rfl,
     nvDefSweep_invW.1, nvDefSweep_invW.2.1, nvDefSweep_invW.2.2.2.1, rfl, by decide, hm,
     fun ret scr' m' _ hret hseq hm' => by
       rw [sep_emp] at hm'; exact ⟨scr', hret, hseq, nvDefSweepF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) for
`full_congruence_dense` (`tick_lim = 100#64`). -/
theorem nv_full_congruence_dense :
    Func.wp defSweepEnv full_congruence_dense_body
      (nvDefSweepCfg.hdr, 100#64, ()) nvDefSweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvDefSweepCfg Full.nvOneLitF0 s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ Full.nvOneLitF0.Unsat ∧ FullMem nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvDefSweepCfg nvDefSweepState ⋆ emp) nvDefSweepMem := by
    rw [sep_emp]; exact nvDefSweepMem_ok
  exact defSweep_congruence_dense_impl.2 _ _ _ _
    ⟨nvDefSweepCfg, Full.nvOneLitF0, nvDefSweepState, emp, rfl,
     nvDefSweep_invW.toDense, hm, fun r s' m' hd _ hdom _ hm' => by
       rw [sep_emp] at hm'; exact ⟨s', hd, hdom, nvDefSweepF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) for
`full_sweep_cone`. -/
theorem nv_full_sweep_cone :
    Func.wp defSweepEnv full_sweep_cone_body
      (nvDefSweepCfg.hdr, 0#32, ()) nvDefSweepMem
      (fun (r, ()) m' => ∃ s' cls',
        FullDenseInvW nvDefSweepCfg Full.nvOneLitF0 [[0], [1]] s' ∧
        fullSweepKittenConeOk [[0], [1]] s' cls' (r &&& 0xFFFF#64).toNat (r >>> 16).toNat ∧
        Full.nvOneLitF0.Unsat ∧ FullMem nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvDefSweepCfg nvDefSweepState ⋆ emp) nvDefSweepMem := by
    rw [sep_emp]; exact nvDefSweepMem_ok
  exact defSweep_sweep_cone_impl.2 _ _ _ _
    ⟨nvDefSweepCfg, Full.nvOneLitF0, [[0], [1]], nvDefSweepState, emp, rfl,
     nvDefSweep_invW, by decide, by decide, nvDefSweep_tmkZero, hm,
     fun _ _ _ _ _ m' cls' hd _ _ _ _ hcone _ _ _ hm' => by
       rw [sep_emp] at hm'; exact ⟨_, cls', hd, hcone, nvDefSweepF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) for
`full_sweep_refine_kitten`. -/
theorem nv_full_sweep_refine_kitten :
    Func.wp defSweepEnv full_sweep_refine_kitten_body
      (nvDefSweepCfg.hdr, 1#32, 0#32, ()) nvDefSweepMem
      (fun () m' => ∃ sig' : List (BitVec 64),
        sig'.length = nvDefSweepCfg.max_vars ∧ Full.nvOneLitF0.Unsat ∧
        FullMem nvDefSweepCfg
          { nvDefSweepState with scratch := { nvDefSweepState.scratch with sim_sig := sig' } }
          m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvDefSweepCfg nvDefSweepState ⋆ emp) nvDefSweepMem := by
    rw [sep_emp]; exact nvDefSweepMem_ok
  exact defSweep_sweep_refine_impl.2 _ _ _ _
    ⟨nvDefSweepCfg, nvDefSweepState, emp, rfl, nvDefSweep_invW.1, by decide, by decide,
     by decide,
     (fun i hi => by
       change i < 1 at hi; obtain rfl : i = 0 := (by omega)
       exact Nat.zero_lt_one),
     hm, fun sig' m' hlen hm' => by
       rw [sep_emp] at hm'; exact ⟨sig', hlen, nvDefSweepF0_unsat, hm'⟩⟩

/-- Parameterized concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_sweep_var`. -/
theorem nv_full_sweep_var_of_wp
    (hVar : ∀ args m Q X, fullSweepVarKittenSpec args m Q X →
      Func.wp defSweepEnv full_sweep_var_body args m Q X) :
    Func.wp defSweepEnv full_sweep_var_body
      (nvDefSweepCfg.hdr, 0#32, 8192#64, ()) nvDefSweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvW nvDefSweepCfg Full.nvOneLitF0 [[0], [1]] s' ∧
        TmkZero s' ∧ (r = 1#64 ∨ r = 20#64) ∧
        Full.nvOneLitF0.Unsat ∧ FullMem nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvDefSweepCfg nvDefSweepState ⋆ emp) nvDefSweepMem := by
    rw [sep_emp]; exact nvDefSweepMem_ok
  exact hVar _ _ _ _
    ⟨nvDefSweepCfg, Full.nvOneLitF0, [[0], [1]], nvDefSweepState, emp, rfl,
     nvDefSweep_invW, by decide, by decide, nvDefSweep_tmkZero, hm,
     fun r s' m' hd _ _ ht hdom _ hm' => by
       rw [sep_emp] at hm'; exact ⟨s', hd, ht, hdom, nvDefSweepF0_unsat, hm'⟩⟩

/-- Parameterized concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_sweep_dense`. -/
theorem nv_full_sweep_dense_of_wp
    (hDense : ∀ args m Q X, fullSweepDenseSpec args m Q X →
      Func.wp defSweepEnv full_sweep_dense_body args m Q X) :
    Func.wp defSweepEnv full_sweep_dense_body
      (nvDefSweepCfg.hdr, 10#64, 8192#64, ()) nvDefSweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvDefSweepCfg Full.nvOneLitF0 s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ Full.nvOneLitF0.Unsat ∧ FullMem nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvDefSweepCfg nvDefSweepState ⋆ emp) nvDefSweepMem := by
    rw [sep_emp]; exact nvDefSweepMem_ok
  exact hDense _ _ _ _
    ⟨nvDefSweepCfg, Full.nvOneLitF0, nvDefSweepState, emp, rfl,
     nvDefSweep_invW.toDense, hm, fun r s' m' hd _ _ hdom _ hm' => by
       rw [sep_emp] at hm'; exact ⟨s', hd, hdom, nvDefSweepF0_unsat, hm'⟩⟩

/-- Unconditional concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) for
`full_sweep_var` under `defSweepEnv`. -/
theorem nv_full_sweep_var :
    Func.wp defSweepEnv full_sweep_var_body
      (nvDefSweepCfg.hdr, 0#32, 8192#64, ()) nvDefSweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvW nvDefSweepCfg Full.nvOneLitF0 [[0], [1]] s' ∧
        TmkZero s' ∧ (r = 1#64 ∨ r = 20#64) ∧
        Full.nvOneLitF0.Unsat ∧ FullMem nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_sweep_var_of_wp defSweep_sweep_var_wp_env

/-- Unconditional concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) for
`full_sweep_dense` under `defSweepEnv`. -/
theorem nv_full_sweep_dense :
    Func.wp defSweepEnv full_sweep_dense_body
      (nvDefSweepCfg.hdr, 10#64, 8192#64, ()) nvDefSweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvDefSweepCfg Full.nvOneLitF0 s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ Full.nvOneLitF0.Unsat ∧ FullMem nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_sweep_dense_of_wp defSweep_sweep_dense_wp_env

/-- Headline concrete `42716`-byte `Mem 64` UNSAT non-vacuity witness (`XPost := False`,
`0` SAT proofs) for `FullDefSweep` (`full_sweep_dense` under `defSweepEnv`). -/
theorem nv_full_def_sweep :
    Func.wp defSweepEnv full_sweep_dense_body
      (nvDefSweepCfg.hdr, 10#64, 8192#64, ()) nvDefSweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvDefSweepCfg Full.nvOneLitF0 s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ Full.nvOneLitF0.Unsat ∧ FullMem nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_sweep_dense

end LeanQbe.T.Examples.Kissat.FullDefSweep
