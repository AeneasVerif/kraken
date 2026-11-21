module

public import LeanQbe.T.Examples.Kissat.FullKittenLemmas3
public import LeanQbe.T.Examples.Kissat.FullKittenLemmas3a
public import LeanQbe.T.Examples.Kissat.FullKittenLemmas4
public import LeanQbe.T.Examples.Kissat.FullKittenLemmas5
public import LeanQbe.T.Examples.Kissat.FullKittenLemmas6
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Scratch `kitten` Module Assembly & Concrete `Mem 64` Non-Vacuity

1. Environment helpers (`fullKittenEnv_noExit`, `fullKittenEnv_row`), `SpecEntry.Impl` witnesses,
   parameterized `mkFullKittenEnv_moduleOk_of_parts`, and unconditional `fullKittenEnv_moduleOk`
   for all `15/15` functions of `fullKittenModule`.
2. Concrete `Mem 64` UNSAT instance (`nvKittenCfg`, `nvKittenKs`, `nvKittenState`, `nvKittenMem`)
   with `nvKittenMem_ok`, `nv_full_kitten_solve`, and `nv_full_kitten_solve_unsat20`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Specification Table Helpers & `SpecEntry.Impl` Witnesses -/

theorem fullKittenSpecTable_nodup :
    (fullKittenSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem fullKittenEnv_noExit :
    ∀ f as bs xs m Q X X',
      fullKittenEnv f as bs xs m Q X → fullKittenEnv f as bs xs m Q X' :=
  Env.ofTable_noExit fullKittenSpecTable_noExit

theorem fullKittenEnv_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ fullKittenSpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → fullKittenEnv nm as bs xs m Q X :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) hmem fullKittenSpecTable_nodup
      (hno xs m Q X hs)

theorem fullKitten_init_impl :
    SpecEntry.Impl fullKittenEnv
      ⟨"full_kitten_init", [i64, i32, i32], [], full_kitten_init_body⟩
      ⟨"full_kitten_init", [i64, i32, i32], [], fullKittenInitSpec, true⟩ :=
  SpecEntry.Impl.of (full_kitten_init_wp fullKittenEnv)

theorem fullKitten_watch_impl :
    SpecEntry.Impl fullKittenEnv
      ⟨"full_kitten_watch", [i64, i32, i32, i32], [], full_kitten_watch_body⟩
      ⟨"full_kitten_watch", [i64, i32, i32, i32], [], fullKittenWatchSpec, true⟩ :=
  SpecEntry.Impl.of (full_kitten_watch_wp fullKittenEnv)

theorem fullKitten_add_clause_impl :
    SpecEntry.Impl fullKittenEnv
      ⟨"full_kitten_add_clause", [i64, i32, i64, i32], [.bool], full_kitten_add_clause_body⟩
      ⟨"full_kitten_add_clause", [i64, i32, i64, i32], [.bool], fullKittenAddClauseSpec, true⟩ :=
  SpecEntry.Impl.of (full_kitten_add_clause_wp fullKittenEnv
    (fullKittenEnv_row (by simp [fullKittenSpecTable])
      fun _ _ _ _ ⟨ac, ks, R, hs, ha, hn, hc, h0, h1, hm, hQ⟩ =>
        ⟨ac, ks, R, hs, ha, hn, hc, h0, h1, hm, hQ⟩))

theorem fullKitten_assign_impl :
    SpecEntry.Impl fullKittenEnv
      ⟨"full_kitten_assign", [i64, i32, i32], [], full_kitten_assign_body⟩
      ⟨"full_kitten_assign", [i64, i32, i32], [], fullKittenAssignSpec, true⟩ :=
  SpecEntry.Impl.of (full_kitten_assign_wp fullKittenEnv)

theorem fullKitten_mtf_impl :
    SpecEntry.Impl fullKittenEnv
      ⟨"full_kitten_mtf", [i64, i32], [], full_kitten_mtf_body⟩
      ⟨"full_kitten_mtf", [i64, i32], [], fullKittenMtfSpec, true⟩ :=
  SpecEntry.Impl.of (full_kitten_mtf_wp fullKittenEnv)

theorem fullKitten_backtrack_impl :
    SpecEntry.Impl fullKittenEnv
      ⟨"full_kitten_backtrack", [i64, i32], [], full_kitten_backtrack_body⟩
      ⟨"full_kitten_backtrack", [i64, i32], [], fullKittenBacktrackSpec, true⟩ :=
  SpecEntry.Impl.of (full_kitten_backtrack_wp fullKittenEnv)

theorem fullKitten_learn_unit0_impl :
    SpecEntry.Impl fullKittenEnv
      ⟨"full_kitten_learn_unit0", [i64, i32, i32, .bool], [i32], full_kitten_learn_unit0_body⟩
      ⟨"full_kitten_learn_unit0", [i64, i32, i32, .bool], [i32], fullKittenLearnUnit0Spec, true⟩ :=
  SpecEntry.Impl.of (full_kitten_learn_unit0_wp fullKittenEnv)

theorem fullKitten_allFns_wf : AllFns Fn.Wf fullKittenModule.fns :=
  ⟨full_kitten_init_wf, full_kitten_watch_wf, full_kitten_add_clause_wf,
   full_kitten_assign_wf, full_kitten_mtf_wf, full_kitten_backtrack_wf,
   full_kitten_learn_unit0_wf, full_kitten_propagate_wf, full_kitten_ana_clause_wf,
   full_kitten_analyze_wf, full_kitten_build_failing_wf, full_kitten_solve_wf,
   full_kitten_core_wf, full_kitten_shrink_wf, full_kitten_flip_wf, trivial⟩

/-! ## 2. Concrete `Mem 64` UNSAT State (`nvKittenCfg`, `nvKittenState`, `nvKittenMem`) -/

/-- Concrete `FullCfg` (`max_vars = 1`, `wcap = 1`, `scratch_cap = 10240`, `avail = 42716`). -/
def nvKittenCfg : FullCfg where
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

/-- Concrete `KittenState` with `nv = 0`, `nc = orig_nc = 1`, empty clause `0`, `incons = 0`. -/
def nvKittenKs : KittenState where
  nv := 0#32
  nc := 1#32
  orig_nc := 1#32
  lvl := 0#32
  prop := 0#32
  trl_end := 0#32
  unass := 0#32
  incons := 0#32
  failing := 0xFFFFFFFF#32
  ante := 0#32
  qfirst := 0xFFFFFFFF#32
  qlast := 0xFFFFFFFF#32
  qsearch := 0xFFFFFFFF#32
  qstamp := 0#32
  ticks := 0#32
  tick_lim := 8192#32
  alen := 0#32
  acap := 1376#32
  nassump := 0#32
  nunits := 0#32
  nres := 0#32
  nkl := 0#32
  nana := 0#32
  status := 0#32
  phase := 0#32
  hdrTail := List.replicate 7 0#32
  lvlArr := List.replicate 128 0#32
  rsn := List.replicate 128 0#32
  qprev := List.replicate 128 0#32
  qnext := List.replicate 128 0#32
  qstampArr := List.replicate 128 0#32
  trl := List.replicate 128 0#32
  flags := List.replicate 128 0#32
  vals := List.replicate 256 0#32
  assump := List.replicate 128 0#32
  ana := List.replicate 128 0#32
  kl := List.replicate 128 0#32
  units := List.replicate 256 0#32
  res := List.replicate 256 0#32
  whead := List.replicate 256 0#32
  wnext := List.replicate 1792 0#32
  wblit := List.replicate 1792 0#32
  clOff := List.replicate 896 0#32
  clMeta := List.replicate 896 0#32
  clAux := List.replicate 896 0#32
  arena := List.replicate 1376 0#32

theorem nvKittenKs_shapes : nvKittenKs.ShapesOk 1376 :=
  ⟨List.length_replicate, List.length_replicate, List.length_replicate,
   List.length_replicate, List.length_replicate, List.length_replicate,
   List.length_replicate, List.length_replicate, List.length_replicate,
   List.length_replicate, List.length_replicate, List.length_replicate,
   List.length_replicate, List.length_replicate, List.length_replicate,
   List.length_replicate, List.length_replicate, List.length_replicate,
   List.length_replicate, List.length_replicate, List.length_replicate⟩

/-- Concrete `10240`-word `scratch_buf` encoding `nvKittenKs`. -/
def nvKittenScratchBuf : List (BitVec 32) :=
  List.replicate 256 0#32 ++ nvKittenKs.toSlab

theorem nvKittenScratchBuf_length : nvKittenScratchBuf.length = 10240 := by
  have hts : nvKittenKs.toSlab.length = 8608 + 1376 :=
    KittenState.toSlab_length nvKittenKs_shapes
  unfold nvKittenScratchBuf
  rw [List.length_append, List.length_replicate, hts]

theorem nvKittenKs_ofSlab : kittenStateOfScratch nvKittenScratchBuf = nvKittenKs := by
  unfold kittenStateOfScratch nvKittenScratchBuf
  rw [slab_drop_exact _ nvKittenKs.toSlab (by rw [List.length_replicate])]
  exact KittenState.ofSlab_toSlab nvKittenKs_shapes

private theorem nvKitten_cl0_lits : kittenClauseLits nvKittenKs 0 = [] := by
  unfold kittenClauseLits kittenClauseSize kittenClauseMeta
  have h0 : nvKittenKs.clMeta[0]?.getD 0#32 = 0#32 := by
    change (List.replicate 896 0#32)[0]?.getD 0#32 = 0#32
    simp only [List.getElem?_replicate]; rfl
  rw [h0]
  have h1 : ((0#32 &&& 0xFFFF#32) : BitVec 32).toNat = 0 := by decide
  rw [h1, List.take_zero, List.map_nil]

private theorem nvKitten_origClauses : kittenOrigClauses nvKittenKs = [[]] := by
  unfold kittenOrigClauses
  have h1 : nvKittenKs.orig_nc.toNat = 1 := rfl
  rw [h1, List.range_one, List.map_singleton, nvKitten_cl0_lits]

theorem nvKitten_unsat : (cnfOfClauses (kittenOrigClausesS nvKittenScratchBuf)).Unsat := by
  have h1 : kittenOrigClausesS nvKittenScratchBuf = [[]] := by
    unfold kittenOrigClausesS
    rw [nvKittenKs_ofSlab, nvKitten_origClauses]
  rw [h1, CNF.unsat_iff_not_sat]
  intro α hα
  have hc := (cnf_sat_cnfOfClauses_iff α [[]]).mp hα [] (by simp)
  rw [clause_sat_cnfClause_iff] at hc
  obtain ⟨_, hl, _⟩ := hc
  nomatch hl

theorem nvKitten_scratchInv : KittenScratchInv nvKittenScratchBuf := by
  refine ⟨by rw [nvKittenScratchBuf_length]; decide,
    by rw [nvKittenScratchBuf_length]; decide, ?_⟩
  rw [nvKittenKs_ofSlab, show nvKittenScratchBuf.length - 8864 = 1376 by
    rw [nvKittenScratchBuf_length]]
  have hcl : KittenClausesOk 1376 nvKittenKs :=
    { acap_ge := by decide
      acap_lt := by decide
      acap_eq := rfl
      nv_le := by decide
      nc_le := by decide
      orig_nc_le := by decide
      orig_nc_max := by decide
      alen_le := by decide
      nassump_le := by decide
      nunits_le := by decide
      nres_le := by decide
      nkl_le := by decide
      nana_le := by decide
      cl_wf := fun cid hcid => by
        change cid < 1 at hcid
        obtain rfl : cid = 0 := by omega
        have hmeta : kittenClauseMeta nvKittenKs 0 = 0#32 := by
          unfold kittenClauseMeta
          change (List.replicate 896 0#32)[0]?.getD 0#32 = 0#32
          simp only [List.getElem?_replicate]; rfl
        have hoff : kittenClauseOff nvKittenKs 0 = 0 := by
          unfold kittenClauseOff
          change ((List.replicate 896 0#32)[0]?.getD 0#32).toNat = 0
          simp only [List.getElem?_replicate]; rfl
        have his : kittenClauseIsLrn nvKittenKs 0 = false := by
          unfold kittenClauseIsLrn; rw [hmeta]; decide
        have hsz : kittenClauseSize nvKittenKs 0 = 0 := by
          unfold kittenClauseSize; rw [hmeta]; decide
        have hsp : kittenClauseSpan nvKittenKs 0 = 0 := by
          unfold kittenClauseSpan; rw [hsz, his]; simp
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [his]; rfl
        · intro hge; change 1 ≤ 0 at hge; omega
        · rw [hoff, hsp]; decide
        · intro l hmem; rw [nvKitten_cl0_lits] at hmem; nomatch hmem
        · rw [nvKitten_cl0_lits, nvKitten_origClauses]
          exact cnfOfClauses_entailsClause_of_mem (by simp)
        · intro _ hge; change 1 ≤ 0 at hge; omega
      cl_mono := fun c1 c2 h12 hc2 => by change c2 < 1 at hc2; omega
      units_ok := fun ui hui => by change ui < 0 at hui; omega
      incons_ok := fun _ => by
        have huns : (cnfOfClauses (kittenOrigClauses nvKittenKs)).Unsat := by
          rw [nvKitten_origClauses, CNF.unsat_iff_not_sat]
          intro α hα
          have hc := (cnf_sat_cnfOfClauses_iff α [[]]).mp hα [] (by simp)
          rw [clause_sat_cnfClause_iff] at hc
          obtain ⟨_, hl, _⟩ := hc; nomatch hl
        refine ⟨by decide, huns, fun l hl => ?_⟩
        change l ∈ kittenClauseLits nvKittenKs 0 at hl
        rw [nvKitten_cl0_lits] at hl
        nomatch hl
      failing_ok := fun hf => absurd rfl hf
      assump_ok := fun i hi => by change i < 0 at hi; omega
      flags_clean := fun v hv => by change v < 0 at hv; omega }
  have hw : KittenWatchesOk nvKittenKs :=
    ⟨[], rfl, List.nodup_nil, fun l hl => by change l < 0 at hl; omega,
     fun l hl => by change l < 0 at hl; omega⟩
  have hba : KittenBaseAssignOk nvKittenKs :=
    ⟨by decide, by decide, by decide,
     fun l hl => by change l < 0 at hl; omega,
     fun l hl => by change l < 0 at hl; omega,
     fun l hl => by change l < 0 at hl; omega,
     by unfold kittenTrailLits; rw [show nvKittenKs.trl_end.toNat = 0 from rfl]; simp,
     fun l hl => by
       unfold kittenTrailLits at hl
       rw [show nvKittenKs.trl_end.toNat = 0 from rfl] at hl; simp at hl,
     fun v hv => by change v < 0 at hv; omega,
     fun v hv => by change v < 0 at hv; omega,
     fun i j _ hj => by change j < 0 at hj; omega,
     fun i _ _ hi => by change i < 0 at hi; omega,
     fun i hi => by change i < 0 at hi; omega⟩
  have hrsn : ReasonOk nvKittenKs := fun i hi => by change i < 0 at hi; omega
  exact ⟨nvKittenKs_shapes, hcl, hw, hba, hrsn⟩

/-- Zero-initialized concrete `FullScratch` for `nvKittenCfg` with `nvKittenScratchBuf`. -/
def nvKittenScratch : FullScratch where
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
  scratch_buf := nvKittenScratchBuf

/-- Concrete `FullState` with `fuel = 1#64` and `nvKittenScratch`. -/
def nvKittenState : FullState where
  core :=
    { d_cur := 0#64, d_val := 0#64, cur_vars := 1, unassigned := 0#64
      arena_len := 0, wlen := 1, wusable := 0#64, arena_garbage := 0#64
      first_reducible := 0#64, num_irred := 0#64, num_redundant := 0#64, num_binary := 0#64
      unflushed := 0#64, probing := 0#64, trail_end := 1, propagated := 0
      cur_level := 0, fuel := 1#64, confl_ref := 0#64, confl_type := 1#64
      confl_lit0 := 1#64, confl_lit1 := 1#64, tmp_cnt := 0, tmp_len := 0
      min_clr_len := 0, min_clr_full := 0#64, oom := 0#64, dense_mode := 0#64
      inconsistent := 0#64
      vals := [1#8, 0xFF#8]
      lit_mark := [0#8, 0#8]
      mrk := [0#8]
      flags := [0#32]
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
  scratch := nvKittenScratch

theorem nvKittenState_lengths : nvKittenState.LengthsOk nvKittenCfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, nvKittenScratchBuf_length⟩⟩

def nvKBlockHdr : List UInt8 :=
  bytes64 [1#64, 2#64, 0#64, 0#64] ++ bytes64 (hdrTailWords nvKittenCfg nvKittenState)

def nvKBlockBytes : List UInt8 :=
  (bytesOf (t := i8) nvKittenState.core.vals ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvKittenState.scratch.walk_vals ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvKittenState.core.lit_mark ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvKittenState.core.mrk ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvKittenState.scratch.phases ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvKittenState.scratch.phases_target ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvKittenState.scratch.phases_best ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvKittenState.scratch.walk_best ++ List.replicate 7 0)

def nvKBlockU32A : List UInt8 :=
  (bytesOf (t := i32) nvKittenState.core.flags ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvKittenState.core.lvl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvKittenState.core.rsns ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvKittenState.core.trl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvKittenState.core.trail_pos ++ List.replicate 4 0)

def nvKBlockU32B : List UInt8 :=
  (bytesOf (t := i32) nvKittenState.core.tmp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvKittenState.scratch.heap ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvKittenState.scratch.pos ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvKittenState.core.min_clr ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvKittenState.scratch.shrink_stk ++ List.replicate 4 0)

def nvKBlockU32C : List UInt8 :=
  (bytesOf (t := i32) nvKittenState.scratch.q_prev ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvKittenState.scratch.q_next ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvKittenState.scratch.q_stamp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvKittenState.core.frame_trail ++ List.replicate 0 0) ++
  (bytesOf (t := i32) nvKittenState.core.frame_dec ++ List.replicate 0 0)

def nvKBlockWvec : List UInt8 :=
  bytesOf (t := i32) nvKittenState.core.wvec ++
  bytesOf (t := i32) nvKittenState.core.repr ++
  bytesOf (t := i32) nvKittenState.scratch.wsort ++
  bytesOf (t := i32) nvKittenState.scratch.work_stk1 ++
  bytesOf (t := i32) nvKittenState.scratch.work_stk2 ++
  bytesOf (t := i32) nvKittenState.scratch.tarjan_mark ++
  bytesOf (t := i32) nvKittenState.scratch.tarjan_reach ++
  bytes64 nvKittenState.scratch.score ++
  bytes64 nvKittenState.scratch.sim_sig

def nvKBlockTail : List UInt8 :=
  bytesOf (t := i32) nvKittenState.core.min_stk ++
  bytesOf (t := i32) nvKittenState.scratch.glue_used ++
  bytesOf (t := i32) nvKittenState.scratch.last_learned ++
  bytesOf (t := i32) nvKittenState.core.arena ++
  bytesOf (t := i32) nvKittenState.core.wstk ++
  bytesOf (t := i32) nvKittenState.scratch.delayed ++
  bytesOf (t := i32) nvKittenState.scratch.red_refs ++
  bytesOf (t := i32) nvKittenState.scratch.extend_stk ++
  bytesOf (t := i32) nvKittenState.scratch.scratch_buf ++
  List.replicate 0 0

def nvKittenBytes : List UInt8 :=
  nvKBlockHdr ++ nvKBlockBytes ++ nvKBlockU32A ++ nvKBlockU32B ++
  nvKBlockU32C ++ nvKBlockWvec ++ nvKBlockTail

/-- Concrete `42716`-byte `Mem 64` image for `nvKittenState` at `nvKittenCfg.hdr`. -/
def nvKittenMem : Mem 64 := nvKittenBytes.At nvKittenCfg.hdr

private theorem nvK_sep_append {P Q : Mem 64 → Prop} {a b : BitVec 64} {bs1 bs2 : List UInt8}
    (hb : b = a + BitVec.ofNat 64 bs1.length) (hlen : bs1.length + bs2.length ≤ 2 ^ 64)
    (h1 : P (bs1.At a)) (h2 : Q (bs2.At b)) : (P ⋆ Q) ((bs1 ++ bs2).At a) := by
  have heq := congrFun (Mem.At_append_sep bs1 bs2 a hlen) ((bs1 ++ bs2).At a)
  rw [← hb] at heq
  exact sep_mono2 (fun _ h => h ▸ h1) (fun _ h => h ▸ h2) _ (heq.mp rfl)

private theorem nvK_arr_pad_p {t : Ty} {a : BitVec 64} {xs : List (Val t)} (n pad : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n + pad ≤ 2 ^ 64) :
    (bytesOf xs ++ List.replicate pad 0).length = n + pad ∧
    (array (t := t) a xs ⋆ region (a + BitVec.ofNat 64 n) pad)
      ((bytesOf xs ++ List.replicate pad 0).At a) :=
  ⟨by rw [List.length_append, bytesOf_length, List.length_replicate, hn],
   nvK_sep_append (by rw [bytesOf_length, hn])
     (by rw [bytesOf_length, List.length_replicate]; omega)
     (array_bytes a xs (by omega)) ⟨List.replicate pad 0, List.length_replicate, rfl⟩⟩

private theorem nvK_arr_p {t : Ty} {a : BitVec 64} {xs : List (Val t)} (n : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytesOf xs).length = n ∧ array (t := t) a xs ((bytesOf xs).At a) :=
  ⟨by rw [bytesOf_length, hn], array_bytes a xs (by omega)⟩

private theorem nvK_arr64_p {a : BitVec 64} {xs : List (BitVec 64)} (n : Nat)
    (hn : 8 * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytes64 xs).length = n ∧ array64 a xs ((bytes64 xs).At a) :=
  ⟨by rw [bytes64_length, hn], array64_bytes a xs (by omega)⟩

private theorem nvK_join_pair {P Q : Mem 64 → Prop} {a b : BitVec 64} {bs1 bs2 : List UInt8}
    {n1 n2 : Nat} (h1 : bs1.length = n1 ∧ P (bs1.At a))
    (h2 : bs2.length = n2 ∧ Q (bs2.At b))
    (hb : b = a + BitVec.ofNat 64 n1) (hbd : n1 + n2 ≤ 2 ^ 64) :
    (bs1 ++ bs2).length = n1 + n2 ∧ (P ⋆ Q) ((bs1 ++ bs2).At a) :=
  ⟨by rw [List.length_append, h1.1, h2.1], nvK_sep_append (h1.1 ▸ hb) (by omega) h1.2 h2.2⟩

private theorem nvK_sep_reorg {P Q : Mem 64 → Prop} {bs : List UInt8} {a : BitVec 64} {n : Nat}
    (h : bs.length = n ∧ P (bs.At a)) (himp : ∀ m, P m → Q m) : bs.length = n ∧ Q (bs.At a) :=
  ⟨h.1, himp _ h.2⟩

private theorem nvK_zip4 {A1 B1 A2 B2 A3 B3 A4 B4 : Mem 64 → Prop} {m : Mem 64}
    (h : ((((A1 ⋆ B1) ⋆ (A2 ⋆ B2)) ⋆ (A3 ⋆ B3)) ⋆ (A4 ⋆ B4)) m) :
    (((A1 ⋆ A3 ⋆ A4) ⋆ A2) ⋆ (B1 ⋆ B2 ⋆ B3 ⋆ B4)) m := sep_ac h

private theorem nvK_zip4_tail {C A2 P1 A5 B5 A6 B6 A7 B7 A8 B8 : Mem 64 → Prop} {m : Mem 64}
    (h : ((((((C ⋆ A2) ⋆ P1) ⋆ (A5 ⋆ B5)) ⋆ (A6 ⋆ B6)) ⋆ (A7 ⋆ B7)) ⋆ (A8 ⋆ B8)) m) :
    (C ⋆ (A2 ⋆ A5 ⋆ A6 ⋆ A7 ⋆ A8) ⋆ (P1 ⋆ B5 ⋆ B6 ⋆ B7 ⋆ B8)) m := sep_ac h

theorem nvKittenMem_ok : FullMem nvKittenCfg nvKittenState nvKittenMem := by
  let c := nvKittenCfg; let s := nvKittenState
  have hvb : valsBytes c.max_vars - 2 * c.max_vars = 6 := by decide
  have hmb : markBytes c.max_vars - c.max_vars = 7 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 0 := by decide
  have hmv1 : BitVec.ofNat 64 c.max_vars = 1#64 := rfl
  have hmv2 : BitVec.ofNat 64 (2 * c.max_vars) = 2#64 := rfl
  have hmv4 : BitVec.ofNat 64 (4 * c.max_vars) = 4#64 := rfl
  have hmv8 : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 8#64 := rfl
  have hHdr : nvKBlockHdr.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (hdrTailWords c s))
        (nvKBlockHdr.At c.hdr) :=
    nvK_join_pair
      (nvK_arr64_p (a := c.hdr) (xs := [1#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
      (nvK_arr64_p (a := c.hdr + 32) (xs := hdrTailWords c s) 1120
        (by rw [hdrTailWords_length]) (by decide))
      (by decide) (by decide)
  have hBytes : nvKBlockBytes.length = 64 ∧
      (FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ c.padBytes)
        (nvKBlockBytes.At c.pVals) := by
    have h1 := nvK_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 2 6 rfl (by decide)
    have h2 := nvK_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 2 6 rfl
      (by decide)
    have h3 := nvK_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 2 6 rfl
      (by decide)
    have h4 := nvK_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 1 7 rfl (by decide)
    have h5 := nvK_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 1 7 rfl
      (by decide)
    have h6 := nvK_arr_pad_p (t := i8) (a := c.pPhasesTarget) (xs := s.scratch.phases_target) 1 7
      rfl (by decide)
    have h7 := nvK_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best) 1 7 rfl
      (by decide)
    have h8 := nvK_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best) 1 7 rfl
      (by decide)
    let pB1 : Mem 64 → Prop :=
      region (c.pVals + 2#64) 6 ⋆ region (c.pWalkVals + 2#64) 6 ⋆
      region (c.pLitMark + 2#64) 6 ⋆ region (c.pMark + 1#64) 7
    have h12 := nvK_join_pair h1 h2 (by decide) (by decide)
    have h123 := nvK_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nvK_sep_reorg (nvK_join_pair h123 h4 (by decide) (by decide))
      (Q := (FullCoreByteArrs c s.core ⋆ array (t := i8) c.pWalkVals s.scratch.walk_vals) ⋆ pB1)
      fun _ hm => nvK_zip4 hm
    have h12345 := nvK_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nvK_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nvK_join_pair h123456 h7 (by decide) (by decide)
    have hall := nvK_join_pair h1234567 h8 (by decide) (by decide)
    exact nvK_sep_reorg hall fun _ hm => by
      have hfin := nvK_zip4_tail hm
      unfold FullScrByteArrs FullCfg.padBytes
      rw [hvb, hmb, hmv2, hmv1]
      simpa only [pB1, sep_assoc] using hfin
  have hU32A : nvKBlockU32A.length = 40 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        (nvKBlockU32A.At c.pFlags) := by
    have h1 := nvK_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 4 4 rfl (by decide)
    have h2 := nvK_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 4 4 rfl (by decide)
    have h3 := nvK_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 4 4 rfl (by decide)
    have h4 := nvK_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 4 4 rfl (by decide)
    have h5 := nvK_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 4 4 rfl
      (by decide)
    have h12 := nvK_join_pair h1 h2 (by decide) (by decide)
    have h123 := nvK_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nvK_join_pair h123 h4 (by decide) (by decide)
    exact nvK_sep_reorg (nvK_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu4, hmv4]; exact sep_ac hm
  have hU32B : nvKBlockU32B.length = 40 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
        (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
         array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        (nvKBlockU32B.At c.pTmp) := by
    have h1 := nvK_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 4 4 rfl (by decide)
    have h2 := nvK_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 4 4 rfl (by decide)
    have h3 := nvK_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 4 4 rfl (by decide)
    have h4 := nvK_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 4 4 rfl (by decide)
    have h5 := nvK_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk) 4 4 rfl
      (by decide)
    have h12 := nvK_join_pair h1 h2 (by decide) (by decide)
    have h123 := nvK_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nvK_join_pair h123 h4 (by decide) (by decide)
    exact nvK_sep_reorg (nvK_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu4, hmv4]; exact sep_ac hm
  have hU32C : nvKBlockU32C.length = 40 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        (nvKBlockU32C.At c.pQPrev) := by
    have h1 := nvK_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 4 4 rfl
      (by decide)
    have h2 := nvK_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 4 4 rfl
      (by decide)
    have h3 := nvK_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 4 4 rfl
      (by decide)
    have h4 := nvK_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 8 0 rfl
      (by decide)
    have h5 := nvK_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 8 0 rfl
      (by decide)
    have h12 := nvK_join_pair h1 h2 (by decide) (by decide)
    have h123 := nvK_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nvK_join_pair h123 h4 (by decide) (by decide)
    exact nvK_sep_reorg (nvK_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu4, hu8, hmv4, hmv8]; exact sep_ac hm
  have hWvec : nvKBlockWvec.length = 80 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        (nvKBlockWvec.At c.pWvec) := by
    have h1 := nvK_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 16 rfl (by decide)
    have h2 := nvK_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 8 rfl (by decide)
    have h3 := nvK_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 8 rfl (by decide)
    have h4 := nvK_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 8 rfl
      (by decide)
    have h5 := nvK_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 8 rfl
      (by decide)
    have h6 := nvK_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 8 rfl
      (by decide)
    have h7 := nvK_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 8 rfl
      (by decide)
    have h8 := nvK_arr64_p (a := c.pScore) (xs := s.scratch.score) 8 rfl (by decide)
    have h9 := nvK_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 8 rfl (by decide)
    have h12 := nvK_join_pair h1 h2 (by decide) (by decide)
    have h123 := nvK_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nvK_join_pair h123 h4 (by decide) (by decide)
    have h12345 := nvK_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nvK_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nvK_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := nvK_join_pair h1234567 h8 (by decide) (by decide)
    exact nvK_sep_reorg (nvK_join_pair h12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail : nvKBlockTail.length = 41300 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        (nvKBlockTail.At c.pMinStk) := by
    have h1 := nvK_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 16 rfl (by decide)
    have h2 := nvK_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256 rfl
      (by decide)
    have h3 := nvK_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned) 64 rfl
      (by decide)
    have h4 := nvK_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 0 rfl (by decide)
    have h5 := nvK_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 4 rfl (by decide)
    have h6 := nvK_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl (by decide)
    have h7 := nvK_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl (by decide)
    have h8 := nvK_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl
      (by decide)
    have h9 := nvK_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 40960
      (by show 4 * nvKittenScratchBuf.length = 40960; rw [nvKittenScratchBuf_length]) (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 0).At c.pSlack) :=
      ⟨rfl, ⟨List.replicate 0 0, by decide, rfl⟩⟩
    have h12 := nvK_join_pair h1 h2 (by decide) (by decide)
    have h123 := nvK_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nvK_join_pair h123 h4 (by decide) (by decide)
    have h12345 := nvK_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nvK_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nvK_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := nvK_join_pair h1234567 h8 (by decide) (by decide)
    have h123456789 := nvK_join_pair h12345678 h9 (by decide) (by decide)
    exact nvK_sep_reorg (nvK_join_pair h123456789 h10 (by decide) (by decide)) fun _ hm => by
      unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := nvK_join_pair hHdr hBytes (by decide) (by decide)
  have h02 := nvK_join_pair h01 hU32A (by decide) (by decide)
  have h03 := nvK_join_pair h02 hU32B (by decide) (by decide)
  have h04 := nvK_join_pair h03 hU32C (by decide) (by decide)
  have h05 := nvK_join_pair h04 hWvec (by decide) (by decide)
  exact (nvK_sep_reorg (Q := FullMem c s) (nvK_join_pair h05 hTail (by decide) (by decide))
    fun _ hm => by
      unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
        FullScrMetaArrs FullCfg.pad
      exact sep_ac hm).2

/-! ## 3. Solve Implementation, Parameterized `ModuleOk`, & UNSAT Non-Vacuity -/

theorem fullKitten_solve_impl :
    SpecEntry.Impl fullKittenEnv
      ⟨"full_kitten_solve", [i64, i64], [i64], full_kitten_solve_body⟩
      ⟨"full_kitten_solve", [i64, i64], [i64], fullKittenSolveSpec, true⟩ :=
  SpecEntry.Impl.of (full_kitten_solve_wp fullKittenEnv
    (fullKittenEnv_row (by simp [fullKittenSpecTable]) (fun _ _ _ _ h => h))
    (fullKittenEnv_row (by simp [fullKittenSpecTable]) (fun _ _ _ _ h => h))
    (fullKittenEnv_row (by simp [fullKittenSpecTable]) (fun _ _ _ _ h => h))
    (fullKittenEnv_row (by simp [fullKittenSpecTable]) (fun _ _ _ _ h => h))
    (fullKittenEnv_row (by simp [fullKittenSpecTable]) (fun _ _ _ _ h => h)))

/-- Parameterized `TableImpl` assembling `[1..7]` + `[15]` from `h8..h14` (`build_failing`,
`flip`, `propagate`, `ana_clause`, `analyze`, `core`, `shrink`). -/
theorem fullKitten_tableImpl_of_parts
    (h8 : ∀ args m Q X, fullKittenBuildFailingSpec args m Q X →
      Func.wp fullKittenEnv full_kitten_build_failing_body args m Q X)
    (h9 : ∀ args m Q X, fullKittenFlipSpec args m Q X →
      Func.wp fullKittenEnv full_kitten_flip_body args m Q X)
    (h10 : ∀ args m Q X, fullKittenPropagateSpec args m Q X →
      Func.wp fullKittenEnv full_kitten_propagate_body args m Q X)
    (h11 : ∀ args m Q X, fullKittenAnaClauseSpec args m Q X →
      Func.wp fullKittenEnv full_kitten_ana_clause_body args m Q X)
    (h12 : ∀ args m Q X, fullKittenAnalyzeSpec args m Q X →
      Func.wp fullKittenEnv full_kitten_analyze_body args m Q X)
    (h13 : ∀ args m Q X, fullKittenCoreSpec args m Q X →
      Func.wp fullKittenEnv full_kitten_core_body args m Q X)
    (h14 : ∀ args m Q X, fullKittenShrinkSpec args m Q X →
      Func.wp fullKittenEnv full_kitten_shrink_body args m Q X) :
    TableImpl fullKittenEnv fullKittenModule.fns fullKittenSpecTable :=
  ⟨fullKitten_init_impl, fullKitten_watch_impl, fullKitten_add_clause_impl,
   fullKitten_assign_impl, fullKitten_mtf_impl, fullKitten_backtrack_impl,
   fullKitten_learn_unit0_impl, SpecEntry.Impl.of h10, SpecEntry.Impl.of h11,
   SpecEntry.Impl.of h12, SpecEntry.Impl.of h8, fullKitten_solve_impl,
   SpecEntry.Impl.of h13, SpecEntry.Impl.of h14, SpecEntry.Impl.of h9, trivial⟩

/-- Parameterized `ModuleOk` for `fullKittenEnv` / `fullKittenModule` given `[8..14]`. -/
theorem mkFullKittenEnv_moduleOk_of_parts
    (h8 : ∀ args m Q X, fullKittenBuildFailingSpec args m Q X →
      Func.wp fullKittenEnv full_kitten_build_failing_body args m Q X)
    (h9 : ∀ args m Q X, fullKittenFlipSpec args m Q X →
      Func.wp fullKittenEnv full_kitten_flip_body args m Q X)
    (h10 : ∀ args m Q X, fullKittenPropagateSpec args m Q X →
      Func.wp fullKittenEnv full_kitten_propagate_body args m Q X)
    (h11 : ∀ args m Q X, fullKittenAnaClauseSpec args m Q X →
      Func.wp fullKittenEnv full_kitten_ana_clause_body args m Q X)
    (h12 : ∀ args m Q X, fullKittenAnalyzeSpec args m Q X →
      Func.wp fullKittenEnv full_kitten_analyze_body args m Q X)
    (h13 : ∀ args m Q X, fullKittenCoreSpec args m Q X →
      Func.wp fullKittenEnv full_kitten_core_body args m Q X)
    (h14 : ∀ args m Q X, fullKittenShrinkSpec args m Q X →
      Func.wp fullKittenEnv full_kitten_shrink_body args m Q X) :
    ModuleOk fullKittenEnv fullKittenModule :=
  Env.ofTable_moduleOk fullKitten_acyclic fullKitten_allFns_wf
    (fullKitten_tableImpl_of_parts h8 h9 h10 h11 h12 h13 h14)

/-- Unconditional `ModuleOk` certifying all `15/15` functions of `fullKittenModule` against
`fullKittenEnv`. -/
theorem fullKittenEnv_moduleOk : ModuleOk fullKittenEnv fullKittenModule :=
  mkFullKittenEnv_moduleOk_of_parts
    (full_kitten_build_failing_wp fullKittenEnv)
    (full_kitten_flip_wp fullKittenEnv)
    (full_kitten_propagate_wp fullKittenEnv
      (fullKittenEnv_row (by simp [fullKittenSpecTable]) (fun _ _ _ _ h => h))
      (fullKittenEnv_row (by simp [fullKittenSpecTable]) (fun _ _ _ _ h => h)))
    (full_kitten_ana_clause_wp fullKittenEnv)
    (full_kitten_analyze_wp fullKittenEnv
      (fullKittenEnv_row (by simp [fullKittenSpecTable]) (fun _ _ _ _ h => h))
      (fullKittenEnv_row (by simp [fullKittenSpecTable]) (fun _ _ _ _ h => h))
      (fullKittenEnv_row (by simp [fullKittenSpecTable]) (fun _ _ _ _ h => h))
      (fullKittenEnv_row (by simp [fullKittenSpecTable]) (fun _ _ _ _ h => h))
      (fullKittenEnv_row (by simp [fullKittenSpecTable]) (fun _ _ _ _ h => h))
      (fullKittenEnv_row (by simp [fullKittenSpecTable]) (fun _ _ _ _ h => h)))
    (full_kitten_core_wp fullKittenEnv)
    (full_kitten_shrink_wp fullKittenEnv
      (fullKittenEnv_row (by simp [fullKittenSpecTable]) (fun _ _ _ _ h => h)))

section SolveNonVacuity

open LeanQbe.T.C0HeadStep
open scoped KittenMemTactics KittenMemATactics KittenProjTactics

/-- Concrete `42716`-byte `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) for
`full_kitten_solve` via `fullKitten_solve_impl`. -/
theorem nv_full_kitten_solve :
    Func.wp fullKittenEnv full_kitten_solve_body
      (nvKittenCfg.hdr, 8192#64, ()) nvKittenMem
      (fun (r, ()) m' => ∃ fuel' scr',
        let s' : FullState :=
          { nvKittenState with
            core := { nvKittenState.core with fuel := fuel' }
            scratch := { nvKittenState.scratch with scratch_buf := scr' } }
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (cnfOfClauses (kittenOrigClausesS scr') ++ unitsCnf (kittenAssumpLitsS scr')).Unsat ∧
        FullMem nvKittenCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvKittenCfg nvKittenState ⋆ emp) nvKittenMem := by
    rw [sep_emp]; exact nvKittenMem_ok
  exact fullKitten_solve_impl.2 _ _ _ _
    ⟨nvKittenCfg, nvKittenState, emp, rfl, nvKittenState_lengths, nvKitten_scratchInv, hm,
     fun r fuel' scr' m' _ _ _ _ _ _ _ _ _ hperm _ _ hr _ hm' => by
       rw [sep_emp] at hm'
       have huns0 : (cnfOfClauses (kittenOrigClausesS nvKittenScratchBuf) ++
           unitsCnf (kittenAssumpLitsS scr')).Unsat :=
         cnfOfClauses_unsat_append_left _ nvKitten_unsat
       have huns' : (cnfOfClauses (kittenOrigClausesS scr') ++
           unitsCnf (kittenAssumpLitsS scr')).Unsat :=
         (hperm.unsat_iff (unitsCnf (kittenAssumpLitsS scr'))).mpr huns0
       exact ⟨fuel', scr', hr, huns', hm'⟩⟩

/-- Concrete `Mem 64` `r = 20#64` UNSAT non-vacuity (`XPost := False`) for `full_kitten_solve`
under `fullKittenEnv`. -/
theorem nv_full_kitten_solve_unsat20 :
    Func.wp fullKittenEnv full_kitten_solve_body
      (nvKittenCfg.hdr, 8192#64, ()) nvKittenMem
      (fun (r, ()) m' => ∃ scr',
        r = 20#64 ∧
        (kittenStateOfScratch scr').incons ≠ 0xFFFFFFFF#32 ∧
        (cnfOfClauses (kittenOrigClausesS scr') ++ unitsCnf (kittenAssumpLitsS scr')).Unsat ∧
        FullMem nvKittenCfg
          { nvKittenState with
            scratch := { nvKittenState.scratch with scratch_buf := scr' } } m')
      (fun _ _ _ _ => False) := by
  have h8864 : 8864 ≤ nvKittenState.scratch.scratch_buf.length := by
    change 8864 ≤ nvKittenScratchBuf.length
    rw [nvKittenScratchBuf_length]; decide
  have h256 : 256 ≤ nvKittenState.scratch.scratch_buf.length := by omega
  have hinv0 : nvKittenKs.Inv 1376 := by
    have h := nvKitten_scratchInv.2.2
    rw [nvKittenKs_ofSlab, show nvKittenScratchBuf.length - 8864 = 1376 by
      rw [nvKittenScratchBuf_length]] at h
    exact h
  have hm0 : (FullKittenFrame nvKittenCfg nvKittenState ⋆
      KittenMem (nvKittenCfg.pScratchBuf + 1024#64) nvKittenKs ⋆ emp) nvKittenMem := by
    have hm1 := nvKittenMem_ok
    rw [fullMem_eq_kittenFrame h8864] at hm1
    change (FullKittenFrame nvKittenCfg nvKittenState ⋆
      KittenMem (nvKittenCfg.pScratchBuf + 1024#64)
        (kittenStateOfScratch nvKittenScratchBuf)) nvKittenMem at hm1
    rw [nvKittenKs_ofSlab] at hm1
    rw [sep_emp]; exact hm1
  have hkPtr : nvKittenCfg.pScratchBuf + BitVec.ofNat 64 256 * 4 =
      nvKittenCfg.pScratchBuf + 1024#64 := kPtr_base_eq _
  unfold Func.wp full_kitten_solve_body
  c0_hsteps_nogrp
  refine wp_call_of_spec _ _
    (fullKittenEnv_row (sp := fullKittenBacktrackSpec)
      (by simp [fullKittenSpecTable]) (fun _ _ _ _ h => h) _ _ _ _
      ⟨1376, nvKittenKs, FullKittenFrame nvKittenCfg nvKittenState ⋆ emp, hinv0,
       fun i hi _ => by change i < 0 at hi; omega, by rw [hkPtr]; exact sep_ac hm0,
       fun ks1 m1 hinv1 _ _ _ _ hbt1 _ _ hm1 => ?_⟩)
  have hmA1 : (KittenMemA (nvKittenCfg.pScratchBuf + BitVec.ofNat 64 256 * 4) 1376 ks1 ⋆
      (FullKittenFrame nvKittenCfg nvKittenState ⋆ emp)) m1 :=
    kittenMem_to_amem hinv1.shapes (sep_ac hm1)
  c0_hsplit
  · have hinc1 : ks1.incons ≠ 0xFFFFFFFF#32 := ‹_›
    c0_hsteps!
    obtain ⟨_, hmFin1⟩ := kittenMemA_to_mem hmA1
    have huns1 := cnfOfClauses_unsat_append_left (unitsCnf (kittenAssumpLits ks1))
      (hinv1.clauses.incons_ok hinc1).2.1
    have hm_join := fullMem_join_kitten (c := nvKittenCfg) (s := nvKittenState) (acap := 1376)
      (ks' := ks1) (R := emp) h256 hinv1.shapes (by rw [← hkPtr]; exact sep_ac hmFin1)
    dsimp only at hm_join
    rw [sep_emp] at hm_join
    let scr' := nvKittenState.scratch.scratch_buf.take 256 ++ ks1.toSlab
    have htk : (nvKittenState.scratch.scratch_buf.take 256).length = 256 :=
      List.length_take_of_le h256
    have hof1 : kittenStateOfScratch scr' = ks1 := by
      unfold kittenStateOfScratch
      rw [show scr' = nvKittenState.scratch.scratch_buf.take 256 ++ ks1.toSlab from rfl,
        slab_drop_exact _ ks1.toSlab htk]
      exact KittenState.ofSlab_toSlab hinv1.shapes
    refine ⟨scr', rfl, by rw [hof1]; exact hinc1, ?_, hm_join⟩
    unfold kittenOrigClausesS kittenAssumpLitsS
    rw [hof1]
    exact huns1
  · exact absurd (hbt1.incons.symm.trans ‹ks1.incons = 0xFFFFFFFF#32›) (by decide)

end SolveNonVacuity

end LeanQbe.T.Examples.Kissat.Full
