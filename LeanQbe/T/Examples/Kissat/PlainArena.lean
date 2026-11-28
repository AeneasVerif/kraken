module

public import LeanQbe.T.Examples.Kissat.PlainArena1
public import LeanQbe.T.Logic.C0Step
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `D-Plain` Arena Accessors — Part 2 (`Stage 3`)

Completes `@[c0_load]` / `@[c0_store]` separation-logic load and store lemmas for
`PlainMem`:
1. Header words `41..91` (byte offsets `360..760`, including VMTF queue, mode switching,
   rephase/reduce limits, restart EMAs, and `oom`).
2. All 12 `PlainCoreArrays` (`vals`, `mrk`, `lvl`, `rsns`, `trl`, `trail_pos`, `tmp`,
   `wvec`, `arena`, `wstk`, `min_stk`, `min_clr`) and all 14 `PlainHeurArrays` (`heap`,
   `pos`, `score`, `phases`, `phases_target`, `phases_best`, `wsort`, `shrink_stk`,
   `red_refs`, `glue_used`, `q_prev`, `q_next`, `q_stamp`, `delayed`), both `Nat`-indexed
   and `BitVec 64`-indexed (`c0_load_arena_*` / `c0_store_arena_*`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Plain

open LeanQbe.T
open LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test

private theorem arrGetI8 {a : BitVec 64} {xs : List (BitVec 8)} {F : Mem 64 → Prop} {i : Nat}
    {m : Mem 64} (hi : i < xs.length) (h : (array (t := i8) a xs ⋆ F) m) :
    loadVal m i8 (a + BitVec.ofNat 64 i) = some xs[i] := by
  simpa [Ty.bytes, Ty.size, i8] using loadVal_array (t := i8) (by decide) hi h
private theorem arrPutI8 {a : BitVec 64} {xs : List (BitVec 8)} {F : Mem 64 → Prop} {i : Nat}
    {m : Mem 64} (v : BitVec 8) (hi : i < xs.length) (h : (array (t := i8) a xs ⋆ F) m) :
    storeOk m i8 (a + BitVec.ofNat 64 i) ∧
      (array (t := i8) a (xs.set i v) ⋆ F) (storeMem m i8 (a + BitVec.ofNat 64 i) v) := by
  simpa [Ty.bytes, Ty.size, i8] using store_array (t := i8) v (by decide) hi h
private theorem arrGetI32 {a : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop} {i : Nat}
    {m : Mem 64} (hi : i < xs.length) (h : (array (t := i32) a xs ⋆ F) m) :
    loadVal m i32 (a + BitVec.ofNat 64 (4 * i)) = some xs[i] :=
  loadVal_array (t := i32) (by decide) hi h
private theorem arrPutI32 {a : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop}
    {i : Nat} {m : Mem 64} (v : BitVec 32) (hi : i < xs.length)
    (h : (array (t := i32) a xs ⋆ F) m) : storeOk m i32 (a + BitVec.ofNat 64 (4 * i)) ∧
      (array (t := i32) a (xs.set i v) ⋆ F) (storeMem m i32 (a + BitVec.ofNat 64 (4 * i)) v) :=
  store_array (t := i32) v (by decide) hi h
private theorem arrGetI64 {a : BitVec 64} {xs : List (BitVec 64)} {F : Mem 64 → Prop} {i : Nat}
    {m : Mem 64} (hi : i < xs.length) (h : (array64 a xs ⋆ F) m) :
    loadVal m i64 (a + BitVec.ofNat 64 (8 * i)) = some xs[i] :=
  loadVal_array64 hi h
private theorem arrPutI64 {a : BitVec 64} {xs : List (BitVec 64)} {F : Mem 64 → Prop}
    {i : Nat} {m : Mem 64} (v : BitVec 64) (hi : i < xs.length) (h : (array64 a xs ⋆ F) m) :
    storeOk m i64 (a + BitVec.ofNat 64 (8 * i)) ∧
      (array64 a (xs.set i v) ⋆ F) (storeMem m i64 (a + BitVec.ofNat 64 (8 * i)) v) :=
  store_array64 v hi h

private def plainCoreOuter (c : PlainCfg) (s : PlainState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ PlainHeurArrays c s.heur ⋆ c.pad

private def plainHeurOuter (c : PlainCfg) (s : PlainState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ PlainCoreArrays c s ⋆ c.pad

private theorem plainMem_eq_core (c : PlainCfg) (s : PlainState) :
    PlainMem c s = (plainCoreOuter c s ⋆ PlainCoreArrays c s) := by
  unfold PlainMem plainCoreOuter; ac_rfl

private theorem plainMem_eq_heur (c : PlainCfg) (s : PlainState) :
    PlainMem c s = (plainHeurOuter c s ⋆ PlainHeurArrays c s.heur) := by
  unfold PlainMem plainHeurOuter; ac_rfl

private theorem unfocus_pcore {c : PlainCfg} {R : Mem 64 → Prop} (s s' : PlainState)
    {m' : Mem 64} (ho : plainCoreOuter c s' = plainCoreOuter c s)
    (h : ((plainCoreOuter c s ⋆ PlainCoreArrays c s') ⋆ R) m') : (PlainMem c s' ⋆ R) m' := by
  rw [plainMem_eq_core, ho]; exact h

private theorem unfocus_pheur {c : PlainCfg} {R : Mem 64 → Prop} (s s' : PlainState)
    {m' : Mem 64} (ho : plainHeurOuter c s' = plainHeurOuter c s)
    (h : ((plainHeurOuter c s ⋆ PlainHeurArrays c s'.heur) ⋆ R) m') : (PlainMem c s' ⋆ R) m' := by
  rw [plainMem_eq_heur, ho]; exact h

section PlainAccess2
variable {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop} {m : Mem 64}

/-! ## 1. Header words `41..91` (`360..760`) -/

@[c0_load] theorem load_arena_trail_pos (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 360) = some c.pTrailPos := plainHdrTailGet 41 (by decide) hm
@[c0_load] theorem load_arena_q_prev (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 368) = some c.pQPrev := plainHdrTailGet 42 (by decide) hm
@[c0_load] theorem load_arena_q_next (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 376) = some c.pQNext := plainHdrTailGet 43 (by decide) hm
@[c0_load] theorem load_arena_q_stamp (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 384) = some c.pQStamp := plainHdrTailGet 44 (by decide) hm
@[c0_load] theorem load_arena_phases_target_ptr (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 392) = some c.pPhasesTarget := plainHdrTailGet 45 (by decide) hm
@[c0_load] theorem load_arena_phases_best_ptr (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 400) = some c.pPhasesBest := plainHdrTailGet 46 (by decide) hm
@[c0_load] theorem load_arena_wsort_ptr (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 408) = some c.pWsort := plainHdrTailGet 47 (by decide) hm
@[c0_load] theorem load_arena_shrink_stk_ptr (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 416) = some c.pShrinkStk := plainHdrTailGet 48 (by decide) hm
@[c0_load] theorem load_arena_red_refs_ptr (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 424) = some c.pRedRefs := plainHdrTailGet 49 (by decide) hm
@[c0_load] theorem load_arena_glue_used_ptr (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 432) = some c.pGlueUsed := plainHdrTailGet 50 (by decide) hm
@[c0_load] theorem load_arena_red_cap (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 440) = some (BitVec.ofNat 64 c.red_cap) :=
  plainHdrTailGet 51 (by decide) hm
@[c0_load] theorem load_arena_delayed_cap (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 448) = some (BitVec.ofNat 64 c.delayed_cap) :=
  plainHdrTailGet 52 (by decide) hm
@[c0_load] theorem load_arena_delayed_len (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 456) = some (BitVec.ofNat 64 s.heur.delayed_len) :=
  plainHdrTailGet 53 (by decide) hm
@[c0_load] theorem load_arena_wusable (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 464) = some s.wusable := plainHdrTailGet 54 (by decide) hm
@[c0_load] theorem load_arena_garbage (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 472) = some s.arena_garbage := plainHdrTailGet 55 (by decide) hm
@[c0_load] theorem load_arena_first_reducible (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 480) = some s.first_reducible := plainHdrTailGet 56 (by decide) hm
@[c0_load] theorem load_arena_num_irred (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 488) = some s.num_irred := plainHdrTailGet 57 (by decide) hm
@[c0_load] theorem load_arena_num_redundant (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 496) = some s.num_redundant := plainHdrTailGet 58 (by decide) hm
@[c0_load] theorem load_arena_num_binary (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 504) = some s.num_binary := plainHdrTailGet 59 (by decide) hm
@[c0_load] theorem load_arena_unflushed (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 512) = some s.unflushed := plainHdrTailGet 60 (by decide) hm
@[c0_load] theorem load_arena_probing (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 520) = some s.probing := plainHdrTailGet 61 (by decide) hm
@[c0_load] theorem load_arena_confl_type (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 528) = some s.confl_type := plainHdrTailGet 62 (by decide) hm
@[c0_load] theorem load_arena_confl_lit0 (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 536) = some s.confl_lit0 := plainHdrTailGet 63 (by decide) hm
@[c0_load] theorem load_arena_confl_lit1 (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 544) = some s.confl_lit1 := plainHdrTailGet 64 (by decide) hm
@[c0_load] theorem load_arena_stable (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 552) = some s.heur.stable := plainHdrTailGet 65 (by decide) hm
@[c0_load] theorem load_arena_switched (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 560) = some s.heur.switched := plainHdrTailGet 66 (by decide) hm
@[c0_load] theorem load_arena_mode_count (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 568) = some s.heur.mode_count := plainHdrTailGet 67 (by decide) hm
@[c0_load] theorem load_arena_mode_confl_lim (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 576) = some s.heur.mode_confl_lim :=
  plainHdrTailGet 68 (by decide) hm
@[c0_load] theorem load_arena_mode_tick_lim (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 584) = some s.heur.mode_tick_lim :=
  plainHdrTailGet 69 (by decide) hm
@[c0_load] theorem load_arena_mode_saved_ticks (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 592) = some s.heur.mode_saved_ticks :=
  plainHdrTailGet 70 (by decide) hm
@[c0_load] theorem load_arena_search_ticks (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 600) = some s.heur.search_ticks := plainHdrTailGet 71 (by decide) hm
@[c0_load] theorem load_arena_q_first (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 608) = some s.heur.q_first := plainHdrTailGet 72 (by decide) hm
@[c0_load] theorem load_arena_q_last (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 616) = some s.heur.q_last := plainHdrTailGet 73 (by decide) hm
@[c0_load] theorem load_arena_q_search_idx (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 624) = some s.heur.q_search_idx := plainHdrTailGet 74 (by decide) hm
@[c0_load] theorem load_arena_q_search_stamp (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 632) = some s.heur.q_search_stamp :=
  plainHdrTailGet 75 (by decide) hm
@[c0_load] theorem load_arena_q_cur_stamp (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 640) = some s.heur.q_cur_stamp := plainHdrTailGet 76 (by decide) hm
@[c0_load] theorem load_arena_target_assigned (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 648) = some s.heur.target_assigned :=
  plainHdrTailGet 77 (by decide) hm
@[c0_load] theorem load_arena_best_assigned (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 656) = some s.heur.best_assigned :=
  plainHdrTailGet 78 (by decide) hm
@[c0_load] theorem load_arena_rephase_limit (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 664) = some s.heur.rephase_limit :=
  plainHdrTailGet 79 (by decide) hm
@[c0_load] theorem load_arena_rephased (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 672) = some s.heur.rephased := plainHdrTailGet 80 (by decide) hm
@[c0_load] theorem load_arena_reduce_limit (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 680) = some s.heur.reduce_limit := plainHdrTailGet 81 (by decide) hm
@[c0_load] theorem load_arena_reductions (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 688) = some s.heur.reductions := plainHdrTailGet 82 (by decide) hm
@[c0_load] theorem load_arena_tier1 (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 696) = some s.heur.tier1 := plainHdrTailGet 83 (by decide) hm
@[c0_load] theorem load_arena_tier2 (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 704) = some s.heur.tier2 := plainHdrTailGet 84 (by decide) hm
@[c0_load] theorem load_arena_restarts (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 712) = some s.heur.restarts := plainHdrTailGet 85 (by decide) hm
@[c0_load] theorem load_arena_restart_limit (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 720) = some s.heur.restart_limit :=
  plainHdrTailGet 86 (by decide) hm
@[c0_load] theorem load_arena_ema_fast_biased (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 728) = some s.heur.ema_fast_biased :=
  plainHdrTailGet 87 (by decide) hm
@[c0_load] theorem load_arena_ema_fast_exp (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 736) = some s.heur.ema_fast_exp := plainHdrTailGet 88 (by decide) hm
@[c0_load] theorem load_arena_ema_slow_biased (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 744) = some s.heur.ema_slow_biased :=
  plainHdrTailGet 89 (by decide) hm
@[c0_load] theorem load_arena_ema_slow_exp (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 752) = some s.heur.ema_slow_exp := plainHdrTailGet 90 (by decide) hm
@[c0_load] theorem load_arena_oom (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 760) = some s.oom := plainHdrTailGet 91 (by decide) hm

@[c0_store] theorem store_arena_delayed_len (v : Nat) (_hv : v < 2 ^ 64)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i64 (c.hdr + 456) ∧
      (PlainMem c { s with heur := { s.heur with delayed_len := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 456) (BitVec.ofNat 64 v)) :=
  plainHdrTailPut 53 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem c0_store_arena_delayed_len (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 456) ∧
      (PlainMem c { s with heur := { s.heur with delayed_len := v.toNat } } ⋆ R)
        (storeMem m i64 (c.hdr + 456) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_delayed_len v.toNat v.isLt hm
@[c0_store] theorem store_arena_wusable (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 464) ∧
      (PlainMem c { s with wusable := v } ⋆ R) (storeMem m i64 (c.hdr + 464) v) :=
  plainHdrTailPut 54 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_garbage (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 472) ∧
      (PlainMem c { s with arena_garbage := v } ⋆ R) (storeMem m i64 (c.hdr + 472) v) :=
  plainHdrTailPut 55 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_first_reducible (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 480) ∧
      (PlainMem c { s with first_reducible := v } ⋆ R) (storeMem m i64 (c.hdr + 480) v) :=
  plainHdrTailPut 56 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_num_irred (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 488) ∧
      (PlainMem c { s with num_irred := v } ⋆ R) (storeMem m i64 (c.hdr + 488) v) :=
  plainHdrTailPut 57 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_num_redundant (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 496) ∧
      (PlainMem c { s with num_redundant := v } ⋆ R) (storeMem m i64 (c.hdr + 496) v) :=
  plainHdrTailPut 58 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_num_binary (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 504) ∧
      (PlainMem c { s with num_binary := v } ⋆ R) (storeMem m i64 (c.hdr + 504) v) :=
  plainHdrTailPut 59 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_unflushed (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 512) ∧
      (PlainMem c { s with unflushed := v } ⋆ R) (storeMem m i64 (c.hdr + 512) v) :=
  plainHdrTailPut 60 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_probing (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 520) ∧
      (PlainMem c { s with probing := v } ⋆ R) (storeMem m i64 (c.hdr + 520) v) :=
  plainHdrTailPut 61 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_confl_type (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 528) ∧
      (PlainMem c { s with confl_type := v } ⋆ R) (storeMem m i64 (c.hdr + 528) v) :=
  plainHdrTailPut 62 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_confl_lit0 (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 536) ∧
      (PlainMem c { s with confl_lit0 := v } ⋆ R) (storeMem m i64 (c.hdr + 536) v) :=
  plainHdrTailPut 63 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_confl_lit1 (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 544) ∧
      (PlainMem c { s with confl_lit1 := v } ⋆ R) (storeMem m i64 (c.hdr + 544) v) :=
  plainHdrTailPut 64 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_stable (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 552) ∧
      (PlainMem c { s with heur := { s.heur with stable := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 552) v) :=
  plainHdrTailPut 65 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_switched (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 560) ∧
      (PlainMem c { s with heur := { s.heur with switched := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 560) v) :=
  plainHdrTailPut 66 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_mode_count (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 568) ∧
      (PlainMem c { s with heur := { s.heur with mode_count := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 568) v) :=
  plainHdrTailPut 67 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_mode_confl_lim (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 576) ∧
      (PlainMem c { s with heur := { s.heur with mode_confl_lim := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 576) v) :=
  plainHdrTailPut 68 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_mode_tick_lim (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 584) ∧
      (PlainMem c { s with heur := { s.heur with mode_tick_lim := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 584) v) :=
  plainHdrTailPut 69 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_mode_saved_ticks (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 592) ∧
      (PlainMem c { s with heur := { s.heur with mode_saved_ticks := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 592) v) :=
  plainHdrTailPut 70 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_search_ticks (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 600) ∧
      (PlainMem c { s with heur := { s.heur with search_ticks := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 600) v) :=
  plainHdrTailPut 71 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_q_first (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 608) ∧
      (PlainMem c { s with heur := { s.heur with q_first := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 608) v) :=
  plainHdrTailPut 72 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_q_last (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 616) ∧
      (PlainMem c { s with heur := { s.heur with q_last := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 616) v) :=
  plainHdrTailPut 73 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_q_search_idx (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 624) ∧
      (PlainMem c { s with heur := { s.heur with q_search_idx := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 624) v) :=
  plainHdrTailPut 74 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_q_search_stamp (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 632) ∧
      (PlainMem c { s with heur := { s.heur with q_search_stamp := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 632) v) :=
  plainHdrTailPut 75 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_q_cur_stamp (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 640) ∧
      (PlainMem c { s with heur := { s.heur with q_cur_stamp := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 640) v) :=
  plainHdrTailPut 76 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_target_assigned (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 648) ∧
      (PlainMem c { s with heur := { s.heur with target_assigned := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 648) v) :=
  plainHdrTailPut 77 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_best_assigned (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 656) ∧
      (PlainMem c { s with heur := { s.heur with best_assigned := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 656) v) :=
  plainHdrTailPut 78 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_rephase_limit (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 664) ∧
      (PlainMem c { s with heur := { s.heur with rephase_limit := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 664) v) :=
  plainHdrTailPut 79 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_rephased (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 672) ∧
      (PlainMem c { s with heur := { s.heur with rephased := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 672) v) :=
  plainHdrTailPut 80 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_reduce_limit (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 680) ∧
      (PlainMem c { s with heur := { s.heur with reduce_limit := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 680) v) :=
  plainHdrTailPut 81 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_reductions (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 688) ∧
      (PlainMem c { s with heur := { s.heur with reductions := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 688) v) :=
  plainHdrTailPut 82 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_tier1 (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 696) ∧
      (PlainMem c { s with heur := { s.heur with tier1 := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 696) v) :=
  plainHdrTailPut 83 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_tier2 (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 704) ∧
      (PlainMem c { s with heur := { s.heur with tier2 := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 704) v) :=
  plainHdrTailPut 84 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_restarts (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 712) ∧
      (PlainMem c { s with heur := { s.heur with restarts := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 712) v) :=
  plainHdrTailPut 85 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_restart_limit (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 720) ∧
      (PlainMem c { s with heur := { s.heur with restart_limit := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 720) v) :=
  plainHdrTailPut 86 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_ema_fast_biased (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 728) ∧
      (PlainMem c { s with heur := { s.heur with ema_fast_biased := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 728) v) :=
  plainHdrTailPut 87 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_ema_fast_exp (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 736) ∧
      (PlainMem c { s with heur := { s.heur with ema_fast_exp := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 736) v) :=
  plainHdrTailPut 88 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_ema_slow_biased (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 744) ∧
      (PlainMem c { s with heur := { s.heur with ema_slow_biased := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 744) v) :=
  plainHdrTailPut 89 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_ema_slow_exp (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 752) ∧
      (PlainMem c { s with heur := { s.heur with ema_slow_exp := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 752) v) :=
  plainHdrTailPut 90 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_oom (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 760) ∧
      (PlainMem c { s with oom := v } ⋆ R) (storeMem m i64 (c.hdr + 760) v) :=
  plainHdrTailPut 91 (by decide) _ _ hm rfl rfl rfl rfl rfl

/-! ## 2. `PlainCoreArrays` accessors (12 arrays) -/

@[c0_load] theorem load_arena_vals {i : Nat} (hi : i < s.vals.length)
    (hm : (PlainMem c s ⋆ R) m) : loadVal m i8 (c.pVals + BitVec.ofNat 64 i) = some s.vals[i] := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm; exact arrGetI8 hi (by ecancel)
@[c0_load] theorem c0_load_arena_vals {i : BitVec 64} (hi : i.toNat < s.vals.length)
    (hm : (PlainMem c s ⋆ R) m) : loadVal m i8 (c.pVals + i) = some s.vals[i.toNat] := by
  simpa [bv_ofNat_toNat_eq] using load_arena_vals hi hm
@[c0_store] theorem store_arena_vals {i : Nat} (v : BitVec 8) (hi : i < s.vals.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i8 (c.pVals + BitVec.ofNat 64 i) ∧
      (PlainMem c { s with vals := s.vals.set i v } ⋆ R)
        (storeMem m i8 (c.pVals + BitVec.ofNat 64 i) v) := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI8 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pcore s _ rfl ?_⟩; unfold PlainCoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_vals {i : BitVec 64} (v : BitVec 8)
    (hi : i.toNat < s.vals.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i8 (c.pVals + i) ∧ (PlainMem c { s with vals := s.vals.set i.toNat v } ⋆ R)
      (storeMem m i8 (c.pVals + i) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_vals v hi hm

@[c0_load] theorem load_arena_mrk {i : Nat} (hi : i < s.mrk.length)
    (hm : (PlainMem c s ⋆ R) m) : loadVal m i8 (c.pMark + BitVec.ofNat 64 i) = some s.mrk[i] := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm; exact arrGetI8 hi (by ecancel)
@[c0_load] theorem c0_load_arena_mrk {i : BitVec 64} (hi : i.toNat < s.mrk.length)
    (hm : (PlainMem c s ⋆ R) m) : loadVal m i8 (c.pMark + i) = some s.mrk[i.toNat] := by
  simpa [bv_ofNat_toNat_eq] using load_arena_mrk hi hm
@[c0_store] theorem store_arena_mrk {i : Nat} (v : BitVec 8) (hi : i < s.mrk.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i8 (c.pMark + BitVec.ofNat 64 i) ∧
      (PlainMem c { s with mrk := s.mrk.set i v } ⋆ R)
        (storeMem m i8 (c.pMark + BitVec.ofNat 64 i) v) := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI8 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pcore s _ rfl ?_⟩; unfold PlainCoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_mrk {i : BitVec 64} (v : BitVec 8)
    (hi : i.toNat < s.mrk.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i8 (c.pMark + i) ∧ (PlainMem c { s with mrk := s.mrk.set i.toNat v } ⋆ R)
      (storeMem m i8 (c.pMark + i) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_mrk v hi hm

@[c0_load] theorem load_arena_lvl {i : Nat} (hi : i < s.lvl.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pLevel + BitVec.ofNat 64 (4 * i)) = some s.lvl[i] := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm; exact arrGetI32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_lvl {i : BitVec 64} (hi : i.toNat < s.lvl.length)
    (hm : (PlainMem c s ⋆ R) m) : loadVal m i32 (c.pLevel + i * 4) = some s.lvl[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]; exact load_arena_lvl hi hm
@[c0_store] theorem store_arena_lvl {i : Nat} (v : BitVec 32) (hi : i < s.lvl.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i32 (c.pLevel + BitVec.ofNat 64 (4 * i)) ∧
      (PlainMem c { s with lvl := s.lvl.set i v } ⋆ R)
        (storeMem m i32 (c.pLevel + BitVec.ofNat 64 (4 * i)) v) := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pcore s _ rfl ?_⟩; unfold PlainCoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_lvl {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.lvl.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pLevel + i * 4) ∧ (PlainMem c { s with lvl := s.lvl.set i.toNat v } ⋆ R)
      (storeMem m i32 (c.pLevel + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact store_arena_lvl v hi hm

@[c0_load] theorem load_arena_rsns {i : Nat} (hi : i < s.rsns.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pReason + BitVec.ofNat 64 (4 * i)) = some s.rsns[i] := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm; exact arrGetI32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_rsns {i : BitVec 64} (hi : i.toNat < s.rsns.length)
    (hm : (PlainMem c s ⋆ R) m) : loadVal m i32 (c.pReason + i * 4) = some s.rsns[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]; exact load_arena_rsns hi hm
@[c0_store] theorem store_arena_rsns {i : Nat} (v : BitVec 32) (hi : i < s.rsns.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i32 (c.pReason + BitVec.ofNat 64 (4 * i)) ∧
      (PlainMem c { s with rsns := s.rsns.set i v } ⋆ R)
        (storeMem m i32 (c.pReason + BitVec.ofNat 64 (4 * i)) v) := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pcore s _ rfl ?_⟩; unfold PlainCoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_rsns {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.rsns.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pReason + i * 4) ∧ (PlainMem c { s with rsns := s.rsns.set i.toNat v } ⋆ R)
      (storeMem m i32 (c.pReason + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact store_arena_rsns v hi hm

@[c0_load] theorem load_arena_trl {i : Nat} (hi : i < s.trl.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pTrail + BitVec.ofNat 64 (4 * i)) = some s.trl[i] := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm; exact arrGetI32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_trl {i : BitVec 64} (hi : i.toNat < s.trl.length)
    (hm : (PlainMem c s ⋆ R) m) : loadVal m i32 (c.pTrail + i * 4) = some s.trl[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]; exact load_arena_trl hi hm
@[c0_store] theorem store_arena_trl {i : Nat} (v : BitVec 32) (hi : i < s.trl.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i32 (c.pTrail + BitVec.ofNat 64 (4 * i)) ∧
      (PlainMem c { s with trl := s.trl.set i v } ⋆ R)
        (storeMem m i32 (c.pTrail + BitVec.ofNat 64 (4 * i)) v) := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pcore s _ rfl ?_⟩; unfold PlainCoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_trl {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.trl.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pTrail + i * 4) ∧ (PlainMem c { s with trl := s.trl.set i.toNat v } ⋆ R)
      (storeMem m i32 (c.pTrail + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact store_arena_trl v hi hm

@[c0_load] theorem load_arena_tpos {i : Nat} (hi : i < s.trail_pos.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pTrailPos + BitVec.ofNat 64 (4 * i)) = some s.trail_pos[i] := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm; exact arrGetI32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_tpos {i : BitVec 64} (hi : i.toNat < s.trail_pos.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pTrailPos + i * 4) = some s.trail_pos[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]; exact load_arena_tpos hi hm
@[c0_store] theorem store_arena_tpos {i : Nat} (v : BitVec 32) (hi : i < s.trail_pos.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i32 (c.pTrailPos + BitVec.ofNat 64 (4 * i)) ∧
      (PlainMem c { s with trail_pos := s.trail_pos.set i v } ⋆ R)
        (storeMem m i32 (c.pTrailPos + BitVec.ofNat 64 (4 * i)) v) := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pcore s _ rfl ?_⟩; unfold PlainCoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_tpos {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.trail_pos.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pTrailPos + i * 4) ∧
      (PlainMem c { s with trail_pos := s.trail_pos.set i.toNat v } ⋆ R)
        (storeMem m i32 (c.pTrailPos + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact store_arena_tpos v hi hm

@[c0_load] theorem load_arena_tmp {i : Nat} (hi : i < s.tmp.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pTmp + BitVec.ofNat 64 (4 * i)) = some s.tmp[i] := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm; exact arrGetI32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_tmp {i : BitVec 64} (hi : i.toNat < s.tmp.length)
    (hm : (PlainMem c s ⋆ R) m) : loadVal m i32 (c.pTmp + i * 4) = some s.tmp[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]; exact load_arena_tmp hi hm
@[c0_store] theorem store_arena_tmp {i : Nat} (v : BitVec 32) (hi : i < s.tmp.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i32 (c.pTmp + BitVec.ofNat 64 (4 * i)) ∧
      (PlainMem c { s with tmp := s.tmp.set i v } ⋆ R)
        (storeMem m i32 (c.pTmp + BitVec.ofNat 64 (4 * i)) v) := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pcore s _ rfl ?_⟩; unfold PlainCoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_tmp {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.tmp.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + i * 4) ∧ (PlainMem c { s with tmp := s.tmp.set i.toNat v } ⋆ R)
      (storeMem m i32 (c.pTmp + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact store_arena_tmp v hi hm

@[c0_load] theorem load_arena_wvec {i : Nat} (hi : i < s.wvec.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pWvec + BitVec.ofNat 64 (4 * i)) = some s.wvec[i] := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm; exact arrGetI32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_wvec {i : BitVec 64} (hi : i.toNat < s.wvec.length)
    (hm : (PlainMem c s ⋆ R) m) : loadVal m i32 (c.pWvec + i * 4) = some s.wvec[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]; exact load_arena_wvec hi hm
@[c0_store] theorem store_arena_wvec {i : Nat} (v : BitVec 32) (hi : i < s.wvec.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i32 (c.pWvec + BitVec.ofNat 64 (4 * i)) ∧
      (PlainMem c { s with wvec := s.wvec.set i v } ⋆ R)
        (storeMem m i32 (c.pWvec + BitVec.ofNat 64 (4 * i)) v) := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pcore s _ rfl ?_⟩; unfold PlainCoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_wvec {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.wvec.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pWvec + i * 4) ∧
      (PlainMem c { s with wvec := s.wvec.set i.toNat v } ⋆ R)
        (storeMem m i32 (c.pWvec + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact store_arena_wvec v hi hm

@[c0_load] theorem load_arena_arena {i : Nat} (hi : i < s.arena.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pArena + BitVec.ofNat 64 (4 * i)) = some s.arena[i] := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm; exact arrGetI32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_arena {i : BitVec 64} (hi : i.toNat < s.arena.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pArena + i * 4) = some s.arena[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]; exact load_arena_arena hi hm
@[c0_store] theorem store_arena_arena {i : Nat} (v : BitVec 32) (hi : i < s.arena.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i32 (c.pArena + BitVec.ofNat 64 (4 * i)) ∧
      (PlainMem c { s with arena := s.arena.set i v } ⋆ R)
        (storeMem m i32 (c.pArena + BitVec.ofNat 64 (4 * i)) v) := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pcore s _ rfl ?_⟩; unfold PlainCoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_arena {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.arena.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pArena + i * 4) ∧
      (PlainMem c { s with arena := s.arena.set i.toNat v } ⋆ R)
        (storeMem m i32 (c.pArena + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact store_arena_arena v hi hm

@[c0_load] theorem load_arena_wstk {i : Nat} (hi : i < s.wstk.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pWstk + BitVec.ofNat 64 (4 * i)) = some s.wstk[i] := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm; exact arrGetI32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_wstk {i : BitVec 64} (hi : i.toNat < s.wstk.length)
    (hm : (PlainMem c s ⋆ R) m) : loadVal m i32 (c.pWstk + i * 4) = some s.wstk[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]; exact load_arena_wstk hi hm
@[c0_store] theorem store_arena_wstk {i : Nat} (v : BitVec 32) (hi : i < s.wstk.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i32 (c.pWstk + BitVec.ofNat 64 (4 * i)) ∧
      (PlainMem c { s with wstk := s.wstk.set i v } ⋆ R)
        (storeMem m i32 (c.pWstk + BitVec.ofNat 64 (4 * i)) v) := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pcore s _ rfl ?_⟩; unfold PlainCoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_wstk {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.wstk.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pWstk + i * 4) ∧ (PlainMem c { s with wstk := s.wstk.set i.toNat v } ⋆ R)
      (storeMem m i32 (c.pWstk + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact store_arena_wstk v hi hm

@[c0_load] theorem load_arena_min_stk {i : Nat} (hi : i < s.min_stk.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pMinStk + BitVec.ofNat 64 (4 * i)) = some s.min_stk[i] := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm; exact arrGetI32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_min_stk {i : BitVec 64} (hi : i.toNat < s.min_stk.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pMinStk + i * 4) = some s.min_stk[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact load_arena_min_stk hi hm
@[c0_store] theorem store_arena_min_stk {i : Nat} (v : BitVec 32) (hi : i < s.min_stk.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i32 (c.pMinStk + BitVec.ofNat 64 (4 * i)) ∧
      (PlainMem c { s with min_stk := s.min_stk.set i v } ⋆ R)
        (storeMem m i32 (c.pMinStk + BitVec.ofNat 64 (4 * i)) v) := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pcore s _ rfl ?_⟩; unfold PlainCoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_min_stk {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.min_stk.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pMinStk + i * 4) ∧
      (PlainMem c { s with min_stk := s.min_stk.set i.toNat v } ⋆ R)
        (storeMem m i32 (c.pMinStk + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact store_arena_min_stk v hi hm

@[c0_load] theorem load_arena_min_clr {i : Nat} (hi : i < s.min_clr.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pMinClr + BitVec.ofNat 64 (4 * i)) = some s.min_clr[i] := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm; exact arrGetI32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_min_clr {i : BitVec 64} (hi : i.toNat < s.min_clr.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pMinClr + i * 4) = some s.min_clr[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact load_arena_min_clr hi hm
@[c0_store] theorem store_arena_min_clr {i : Nat} (v : BitVec 32) (hi : i < s.min_clr.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i32 (c.pMinClr + BitVec.ofNat 64 (4 * i)) ∧
      (PlainMem c { s with min_clr := s.min_clr.set i v } ⋆ R)
        (storeMem m i32 (c.pMinClr + BitVec.ofNat 64 (4 * i)) v) := by
  rw [plainMem_eq_core] at hm; unfold PlainCoreArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pcore s _ rfl ?_⟩; unfold PlainCoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_min_clr {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.min_clr.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pMinClr + i * 4) ∧
      (PlainMem c { s with min_clr := s.min_clr.set i.toNat v } ⋆ R)
        (storeMem m i32 (c.pMinClr + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact store_arena_min_clr v hi hm

/-! ## 3. `PlainHeurArrays` accessors (14 arrays) -/

@[c0_load] theorem load_arena_heap {i : Nat} (hi : i < s.heur.heap.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pHeap + BitVec.ofNat 64 (4 * i)) = some s.heur.heap[i] := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm; exact arrGetI32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_heap {i : BitVec 64} (hi : i.toNat < s.heur.heap.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pHeap + i * 4) = some s.heur.heap[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]; exact load_arena_heap hi hm
@[c0_store] theorem store_arena_heap {i : Nat} (v : BitVec 32) (hi : i < s.heur.heap.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i32 (c.pHeap + BitVec.ofNat 64 (4 * i)) ∧
      (PlainMem c { s with heur := { s.heur with heap := s.heur.heap.set i v } } ⋆ R)
        (storeMem m i32 (c.pHeap + BitVec.ofNat 64 (4 * i)) v) := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pheur s _ rfl ?_⟩; unfold PlainHeurArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_heap {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.heur.heap.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pHeap + i * 4) ∧
      (PlainMem c { s with heur := { s.heur with heap := s.heur.heap.set i.toNat v } } ⋆ R)
        (storeMem m i32 (c.pHeap + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact store_arena_heap v hi hm

@[c0_load] theorem load_arena_pos {i : Nat} (hi : i < s.heur.pos.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pPos + BitVec.ofNat 64 (4 * i)) = some s.heur.pos[i] := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm; exact arrGetI32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_pos {i : BitVec 64} (hi : i.toNat < s.heur.pos.length)
    (hm : (PlainMem c s ⋆ R) m) : loadVal m i32 (c.pPos + i * 4) = some s.heur.pos[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]; exact load_arena_pos hi hm
@[c0_store] theorem store_arena_pos {i : Nat} (v : BitVec 32) (hi : i < s.heur.pos.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i32 (c.pPos + BitVec.ofNat 64 (4 * i)) ∧
      (PlainMem c { s with heur := { s.heur with pos := s.heur.pos.set i v } } ⋆ R)
        (storeMem m i32 (c.pPos + BitVec.ofNat 64 (4 * i)) v) := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pheur s _ rfl ?_⟩; unfold PlainHeurArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_pos {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.heur.pos.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pPos + i * 4) ∧
      (PlainMem c { s with heur := { s.heur with pos := s.heur.pos.set i.toNat v } } ⋆ R)
        (storeMem m i32 (c.pPos + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact store_arena_pos v hi hm

@[c0_load] theorem load_arena_score {i : Nat} (hi : i < s.heur.score.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.pScore + BitVec.ofNat 64 (8 * i)) = some s.heur.score[i] := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm; exact arrGetI64 hi (by ecancel)
@[c0_load] theorem c0_load_arena_score {i : BitVec 64} (hi : i.toNat < s.heur.score.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.pScore + i * 8) = some s.heur.score[i.toNat] := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_mul_ofNat]; exact load_arena_score hi hm
@[c0_store] theorem store_arena_score {i : Nat} (v : BitVec 64) (hi : i < s.heur.score.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i64 (c.pScore + BitVec.ofNat 64 (8 * i)) ∧
      (PlainMem c { s with heur := { s.heur with score := s.heur.score.set i v } } ⋆ R)
        (storeMem m i64 (c.pScore + BitVec.ofNat 64 (8 * i)) v) := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI64 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pheur s _ rfl ?_⟩; unfold PlainHeurArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_score {i : BitVec 64} (v : BitVec 64)
    (hi : i.toNat < s.heur.score.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.pScore + i * 8) ∧
      (PlainMem c { s with heur := { s.heur with score := s.heur.score.set i.toNat v } } ⋆ R)
        (storeMem m i64 (c.pScore + i * 8) v) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_mul_ofNat]
  exact store_arena_score v hi hm

@[c0_load] theorem load_arena_phases {i : Nat} (hi : i < s.heur.phases.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i8 (c.pPhases + BitVec.ofNat 64 i) = some s.heur.phases[i] := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm; exact arrGetI8 hi (by ecancel)
@[c0_load] theorem c0_load_arena_phases {i : BitVec 64} (hi : i.toNat < s.heur.phases.length)
    (hm : (PlainMem c s ⋆ R) m) : loadVal m i8 (c.pPhases + i) = some s.heur.phases[i.toNat] := by
  simpa [bv_ofNat_toNat_eq] using load_arena_phases hi hm
@[c0_store] theorem store_arena_phases {i : Nat} (v : BitVec 8) (hi : i < s.heur.phases.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i8 (c.pPhases + BitVec.ofNat 64 i) ∧
      (PlainMem c { s with heur := { s.heur with phases := s.heur.phases.set i v } } ⋆ R)
        (storeMem m i8 (c.pPhases + BitVec.ofNat 64 i) v) := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI8 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pheur s _ rfl ?_⟩; unfold PlainHeurArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_phases {i : BitVec 64} (v : BitVec 8)
    (hi : i.toNat < s.heur.phases.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i8 (c.pPhases + i) ∧
      (PlainMem c { s with heur := { s.heur with phases := s.heur.phases.set i.toNat v } } ⋆ R)
        (storeMem m i8 (c.pPhases + i) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_phases v hi hm

@[c0_load] theorem load_arena_phases_target {i : Nat} (hi : i < s.heur.phases_target.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i8 (c.pPhasesTarget + BitVec.ofNat 64 i) = some s.heur.phases_target[i] := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm; exact arrGetI8 hi (by ecancel)
@[c0_load] theorem c0_load_arena_phases_target {i : BitVec 64}
    (hi : i.toNat < s.heur.phases_target.length) (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i8 (c.pPhasesTarget + i) = some s.heur.phases_target[i.toNat] := by
  simpa [bv_ofNat_toNat_eq] using load_arena_phases_target hi hm
@[c0_store] theorem store_arena_phases_target {i : Nat} (v : BitVec 8)
    (hi : i < s.heur.phases_target.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i8 (c.pPhasesTarget + BitVec.ofNat 64 i) ∧
      (PlainMem c { s with
          heur := { s.heur with phases_target := s.heur.phases_target.set i v } } ⋆ R)
        (storeMem m i8 (c.pPhasesTarget + BitVec.ofNat 64 i) v) := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI8 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pheur s _ rfl ?_⟩; unfold PlainHeurArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_phases_target {i : BitVec 64} (v : BitVec 8)
    (hi : i.toNat < s.heur.phases_target.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i8 (c.pPhasesTarget + i) ∧
      (PlainMem c { s with
          heur := { s.heur with phases_target := s.heur.phases_target.set i.toNat v } } ⋆ R)
        (storeMem m i8 (c.pPhasesTarget + i) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_phases_target v hi hm

@[c0_load] theorem load_arena_phases_best {i : Nat} (hi : i < s.heur.phases_best.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i8 (c.pPhasesBest + BitVec.ofNat 64 i) = some s.heur.phases_best[i] := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm; exact arrGetI8 hi (by ecancel)
@[c0_load] theorem c0_load_arena_phases_best {i : BitVec 64}
    (hi : i.toNat < s.heur.phases_best.length) (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i8 (c.pPhasesBest + i) = some s.heur.phases_best[i.toNat] := by
  simpa [bv_ofNat_toNat_eq] using load_arena_phases_best hi hm
@[c0_store] theorem store_arena_phases_best {i : Nat} (v : BitVec 8)
    (hi : i < s.heur.phases_best.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i8 (c.pPhasesBest + BitVec.ofNat 64 i) ∧
      (PlainMem c { s with
          heur := { s.heur with phases_best := s.heur.phases_best.set i v } } ⋆ R)
        (storeMem m i8 (c.pPhasesBest + BitVec.ofNat 64 i) v) := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI8 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pheur s _ rfl ?_⟩; unfold PlainHeurArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_phases_best {i : BitVec 64} (v : BitVec 8)
    (hi : i.toNat < s.heur.phases_best.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i8 (c.pPhasesBest + i) ∧
      (PlainMem c { s with
          heur := { s.heur with phases_best := s.heur.phases_best.set i.toNat v } } ⋆ R)
        (storeMem m i8 (c.pPhasesBest + i) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_phases_best v hi hm

@[c0_load] theorem load_arena_wsort {i : Nat} (hi : i < s.heur.wsort.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pWsort + BitVec.ofNat 64 (4 * i)) = some s.heur.wsort[i] := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm; exact arrGetI32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_wsort {i : BitVec 64} (hi : i.toNat < s.heur.wsort.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pWsort + i * 4) = some s.heur.wsort[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]; exact load_arena_wsort hi hm
@[c0_store] theorem store_arena_wsort {i : Nat} (v : BitVec 32) (hi : i < s.heur.wsort.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i32 (c.pWsort + BitVec.ofNat 64 (4 * i)) ∧
      (PlainMem c { s with heur := { s.heur with wsort := s.heur.wsort.set i v } } ⋆ R)
        (storeMem m i32 (c.pWsort + BitVec.ofNat 64 (4 * i)) v) := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pheur s _ rfl ?_⟩; unfold PlainHeurArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_wsort {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.heur.wsort.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pWsort + i * 4) ∧
      (PlainMem c { s with heur := { s.heur with wsort := s.heur.wsort.set i.toNat v } } ⋆ R)
        (storeMem m i32 (c.pWsort + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact store_arena_wsort v hi hm

@[c0_load] theorem load_arena_shrink_stk {i : Nat} (hi : i < s.heur.shrink_stk.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pShrinkStk + BitVec.ofNat 64 (4 * i)) = some s.heur.shrink_stk[i] := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm; exact arrGetI32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_shrink_stk {i : BitVec 64}
    (hi : i.toNat < s.heur.shrink_stk.length) (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pShrinkStk + i * 4) = some s.heur.shrink_stk[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact load_arena_shrink_stk hi hm
@[c0_store] theorem store_arena_shrink_stk {i : Nat} (v : BitVec 32)
    (hi : i < s.heur.shrink_stk.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pShrinkStk + BitVec.ofNat 64 (4 * i)) ∧
      (PlainMem c { s with
          heur := { s.heur with shrink_stk := s.heur.shrink_stk.set i v } } ⋆ R)
        (storeMem m i32 (c.pShrinkStk + BitVec.ofNat 64 (4 * i)) v) := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pheur s _ rfl ?_⟩; unfold PlainHeurArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_shrink_stk {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.heur.shrink_stk.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pShrinkStk + i * 4) ∧
      (PlainMem c { s with
          heur := { s.heur with shrink_stk := s.heur.shrink_stk.set i.toNat v } } ⋆ R)
        (storeMem m i32 (c.pShrinkStk + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact store_arena_shrink_stk v hi hm

@[c0_load] theorem load_arena_red_refs {i : Nat} (hi : i < s.heur.red_refs.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pRedRefs + BitVec.ofNat 64 (4 * i)) = some s.heur.red_refs[i] := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm; exact arrGetI32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_red_refs {i : BitVec 64} (hi : i.toNat < s.heur.red_refs.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pRedRefs + i * 4) = some s.heur.red_refs[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact load_arena_red_refs hi hm
@[c0_store] theorem store_arena_red_refs {i : Nat} (v : BitVec 32)
    (hi : i < s.heur.red_refs.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pRedRefs + BitVec.ofNat 64 (4 * i)) ∧
      (PlainMem c { s with heur := { s.heur with red_refs := s.heur.red_refs.set i v } } ⋆ R)
        (storeMem m i32 (c.pRedRefs + BitVec.ofNat 64 (4 * i)) v) := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pheur s _ rfl ?_⟩; unfold PlainHeurArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_red_refs {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.heur.red_refs.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pRedRefs + i * 4) ∧
      (PlainMem c { s with
          heur := { s.heur with red_refs := s.heur.red_refs.set i.toNat v } } ⋆ R)
        (storeMem m i32 (c.pRedRefs + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact store_arena_red_refs v hi hm

@[c0_load] theorem load_arena_glue_used {i : Nat} (hi : i < s.heur.glue_used.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pGlueUsed + BitVec.ofNat 64 (4 * i)) = some s.heur.glue_used[i] := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm; exact arrGetI32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_glue_used {i : BitVec 64}
    (hi : i.toNat < s.heur.glue_used.length) (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pGlueUsed + i * 4) = some s.heur.glue_used[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact load_arena_glue_used hi hm
@[c0_store] theorem store_arena_glue_used {i : Nat} (v : BitVec 32)
    (hi : i < s.heur.glue_used.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pGlueUsed + BitVec.ofNat 64 (4 * i)) ∧
      (PlainMem c { s with heur := { s.heur with glue_used := s.heur.glue_used.set i v } } ⋆ R)
        (storeMem m i32 (c.pGlueUsed + BitVec.ofNat 64 (4 * i)) v) := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pheur s _ rfl ?_⟩; unfold PlainHeurArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_glue_used {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.heur.glue_used.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pGlueUsed + i * 4) ∧
      (PlainMem c { s with
          heur := { s.heur with glue_used := s.heur.glue_used.set i.toNat v } } ⋆ R)
        (storeMem m i32 (c.pGlueUsed + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact store_arena_glue_used v hi hm

@[c0_load] theorem load_arena_q_prev_arr {i : Nat} (hi : i < s.heur.q_prev.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pQPrev + BitVec.ofNat 64 (4 * i)) = some s.heur.q_prev[i] := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm; exact arrGetI32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_q_prev_arr {i : BitVec 64} (hi : i.toNat < s.heur.q_prev.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pQPrev + i * 4) = some s.heur.q_prev[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact load_arena_q_prev_arr hi hm
@[c0_store] theorem store_arena_q_prev_arr {i : Nat} (v : BitVec 32) (hi : i < s.heur.q_prev.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i32 (c.pQPrev + BitVec.ofNat 64 (4 * i)) ∧
      (PlainMem c { s with heur := { s.heur with q_prev := s.heur.q_prev.set i v } } ⋆ R)
        (storeMem m i32 (c.pQPrev + BitVec.ofNat 64 (4 * i)) v) := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pheur s _ rfl ?_⟩; unfold PlainHeurArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_q_prev_arr {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.heur.q_prev.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pQPrev + i * 4) ∧
      (PlainMem c { s with heur := { s.heur with q_prev := s.heur.q_prev.set i.toNat v } } ⋆ R)
        (storeMem m i32 (c.pQPrev + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact store_arena_q_prev_arr v hi hm

@[c0_load] theorem load_arena_q_next_arr {i : Nat} (hi : i < s.heur.q_next.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pQNext + BitVec.ofNat 64 (4 * i)) = some s.heur.q_next[i] := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm; exact arrGetI32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_q_next_arr {i : BitVec 64} (hi : i.toNat < s.heur.q_next.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pQNext + i * 4) = some s.heur.q_next[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact load_arena_q_next_arr hi hm
@[c0_store] theorem store_arena_q_next_arr {i : Nat} (v : BitVec 32) (hi : i < s.heur.q_next.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i32 (c.pQNext + BitVec.ofNat 64 (4 * i)) ∧
      (PlainMem c { s with heur := { s.heur with q_next := s.heur.q_next.set i v } } ⋆ R)
        (storeMem m i32 (c.pQNext + BitVec.ofNat 64 (4 * i)) v) := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pheur s _ rfl ?_⟩; unfold PlainHeurArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_q_next_arr {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.heur.q_next.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pQNext + i * 4) ∧
      (PlainMem c { s with heur := { s.heur with q_next := s.heur.q_next.set i.toNat v } } ⋆ R)
        (storeMem m i32 (c.pQNext + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact store_arena_q_next_arr v hi hm

@[c0_load] theorem load_arena_q_stamp_arr {i : Nat} (hi : i < s.heur.q_stamp.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pQStamp + BitVec.ofNat 64 (4 * i)) = some s.heur.q_stamp[i] := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm; exact arrGetI32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_q_stamp_arr {i : BitVec 64} (hi : i.toNat < s.heur.q_stamp.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pQStamp + i * 4) = some s.heur.q_stamp[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact load_arena_q_stamp_arr hi hm
@[c0_store] theorem store_arena_q_stamp_arr {i : Nat} (v : BitVec 32)
    (hi : i < s.heur.q_stamp.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pQStamp + BitVec.ofNat 64 (4 * i)) ∧
      (PlainMem c { s with heur := { s.heur with q_stamp := s.heur.q_stamp.set i v } } ⋆ R)
        (storeMem m i32 (c.pQStamp + BitVec.ofNat 64 (4 * i)) v) := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pheur s _ rfl ?_⟩; unfold PlainHeurArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_q_stamp_arr {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.heur.q_stamp.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pQStamp + i * 4) ∧
      (PlainMem c { s with heur := { s.heur with q_stamp := s.heur.q_stamp.set i.toNat v } } ⋆ R)
        (storeMem m i32 (c.pQStamp + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact store_arena_q_stamp_arr v hi hm

@[c0_load] theorem load_arena_delayed_arr {i : Nat} (hi : i < s.heur.delayed.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pDelayed + BitVec.ofNat 64 (4 * i)) = some s.heur.delayed[i] := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm; exact arrGetI32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_delayed_arr {i : BitVec 64}
    (hi : i.toNat < s.heur.delayed.length) (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pDelayed + i * 4) = some s.heur.delayed[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact load_arena_delayed_arr hi hm
@[c0_store] theorem store_arena_delayed_arr {i : Nat} (v : BitVec 32)
    (hi : i < s.heur.delayed.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pDelayed + BitVec.ofNat 64 (4 * i)) ∧
      (PlainMem c { s with heur := { s.heur with delayed := s.heur.delayed.set i v } } ⋆ R)
        (storeMem m i32 (c.pDelayed + BitVec.ofNat 64 (4 * i)) v) := by
  rw [plainMem_eq_heur] at hm; unfold PlainHeurArrays at hm
  obtain ⟨hok, hst⟩ := arrPutI32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_pheur s _ rfl ?_⟩; unfold PlainHeurArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_delayed_arr {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.heur.delayed.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pDelayed + i * 4) ∧
      (PlainMem c { s with heur := { s.heur with delayed := s.heur.delayed.set i.toNat v } } ⋆ R)
        (storeMem m i32 (c.pDelayed + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact store_arena_delayed_arr v hi hm

end PlainAccess2

end LeanQbe.T.Examples.Kissat.Plain
