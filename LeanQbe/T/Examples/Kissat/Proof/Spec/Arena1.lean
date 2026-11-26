/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Logic.C0Step
public import Kraken.Mem
public import Kraken.Separation

/-! # Kissat `D-Full` Strictly Scoped Arena Accessors (`FullArenaTactics`, `Stage 4`) -/

set_option autoImplicit false

public section
namespace LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T LeanQbe.T.ProofUtil Kraken.Bedrock2.Test
private theorem arrGetI8 {a : BitVec 64} {xs : List (BitVec 8)} {F : Mem 64 → Prop} {i : Nat}
    {m : Mem 64} (hi : i < xs.length) (h : (array (t := i8) a xs ⋆ F) m) :
    loadVal m i8 (a + BitVec.ofNat 64 i) = some xs[i] := by
  simpa [Ty.bytes, Ty.size, i8] using loadVal_array (t := i8) (by decide) hi h
private theorem arrPutI8 {a : BitVec 64} {xs : List (BitVec 8)} {F : Mem 64 → Prop} {i : Nat}
    {m : Mem 64} (v : BitVec 8) (hi : i < xs.length) (h : (array (t := i8) a xs ⋆ F) m) :
    storeOk m i8 (a + BitVec.ofNat 64 i) ∧ (array (t := i8) a (xs.set i v) ⋆ F)
      (storeMem m i8 (a + BitVec.ofNat 64 i) v) := by
  simpa [Ty.bytes, Ty.size, i8] using store_array (t := i8) v (by decide) hi h
private theorem arrGetI32 {a : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop} {i : Nat}
    {m : Mem 64} (hi : i < xs.length) (h : (array (t := i32) a xs ⋆ F) m) : loadVal m i32
    (a + BitVec.ofNat 64 (4 * i)) = some xs[i] := loadVal_array (t := i32) (by decide) hi h
private theorem arrPutI32 {a : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop} {i : Nat}
    {m : Mem 64} (v : BitVec 32) (hi : i < xs.length) (h : (array (t := i32) a xs ⋆ F) m) :
    storeOk m i32 (a + BitVec.ofNat 64 (4 * i)) ∧ (array (t := i32) a (xs.set i v) ⋆ F)
      (storeMem m i32 (a + BitVec.ofNat 64 (4 * i)) v) := store_array (t := i32) v (by decide) hi h
private theorem arrGetI64 {a : BitVec 64} {xs : List (BitVec 64)} {F : Mem 64 → Prop} {i : Nat}
    {m : Mem 64} (hi : i < xs.length) (h : (array64 a xs ⋆ F) m) :
    loadVal m i64 (a + BitVec.ofNat 64 (8 * i)) = some xs[i] := loadVal_array64 hi h
private theorem arrPutI64 {a : BitVec 64} {xs : List (BitVec 64)} {F : Mem 64 → Prop}
    {i : Nat} {m : Mem 64} (v : BitVec 64) (hi : i < xs.length) (h : (array64 a xs ⋆ F) m) :
    storeOk m i64 (a + BitVec.ofNat 64 (8 * i)) ∧ (array64 a (xs.set i v) ⋆ F)
      (storeMem m i64 (a + BitVec.ofNat 64 (8 * i)) v) := store_array64 v hi h
theorem ufM {c : FullCfg} {s s' : FullState} {G G' B B' R : Mem 64 → Prop}
    {m' : Mem 64} (_hs : FullMem c s = (G ⋆ B)) (hs' : FullMem c s' = (G' ⋆ B'))
    (hb : B' = B) (h : ((G' ⋆ B) ⋆ R) m') : (FullMem c s' ⋆ R) m' := by rw [hs', hb]; exact h

theorem m8 (a i : BitVec 64) : a + i * 8 = a + BitVec.ofNat 64 (8 * i.toNat) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_mul_ofNat]

/-! Strictly scoped `FullMem` load/store/bitvector automation (`zero global attributes`). -/
namespace FullArenaTactics
private theorem gH {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} (i : Nat)
    (hm : (FullMem c s ⋆ R) m) (hi : i < 140 := by decide) : loadVal m i64 (c.hdr +
    BitVec.ofNat 64 (32 + 8 * i)) = some ((hdrTailWords c s)[i]'(by simpa using hi)) :=
  fullHdrTailGet i hi hm
private theorem m4 (a i : BitVec 64) : a + i * 4 = a + BitVec.ofNat 64 (4 * i.toNat) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
private theorem bvId (i : BitVec 64) : BitVec.ofNat 64 i.toNat = i := @bv_ofNat_toNat_eq 64 i
local macro "hP" n:num hm:ident : tactic =>
  `(tactic| exact fullHdrTailPut $n (by decide) _ _ $hm rfl rfl rfl rfl rfl)
local macro "ldA" eq:ident grp:ident fn:ident hi:ident hm:ident : tactic =>
  `(tactic|
    { have h1 := $hm; have h_ := $eq; rw [h_] at h1
      unfold $grp at h1; exact $fn $hi (by ecancel) })
local macro "stA" eq:ident grp:ident fn:ident v:ident hi:ident hm:ident s:ident : tactic =>
  `(tactic|
    { have h1 := $hm; have h_ := $eq; rw [h_] at h1; unfold $grp at h1
      obtain ⟨hok, hst⟩ := $fn $v $hi (F := _) (by ecancel)
      exact ⟨hok, ufM ($eq _ $s) ($eq _ _) rfl (by unfold $grp; dsimp only; ecancel)⟩ })
local macro "l4" f:ident hi:ident hm:ident : tactic => `(tactic| { rw [m4]; exact $f $hi $hm })
local macro "l8" f:ident hi:ident hm:ident : tactic => `(tactic| { rw [m8]; exact $f $hi $hm })
local macro "lB" f:ident hi:ident hm:ident : tactic => `(tactic| simpa [bvId] using $f $hi $hm)
local macro "s4" f:ident v:ident hi:ident hm:ident : tactic =>
  `(tactic| { rw [m4]; exact $f $v $hi $hm })
local macro "s8" f:ident v:ident hi:ident hm:ident : tactic =>
  `(tactic| { rw [m8]; exact $f $v $hi $hm })
local macro "sB" f:ident v:ident hi:ident hm:ident : tactic =>
  `(tactic| simpa [bvId] using $f $v $hi $hm)
local macro "ldCB" fn:ident hi:ident hm:ident : tactic =>
  `(tactic| ldA fullMem_eq_coreByte FullCoreByteArrs $fn $hi $hm)
local macro "stCB" fn:ident v:ident hi:ident hm:ident s:ident : tactic =>
  `(tactic| stA fullMem_eq_coreByte FullCoreByteArrs $fn $v $hi $hm $s)
local macro "ldCA" fn:ident hi:ident hm:ident : tactic =>
  `(tactic| ldA fullMem_eq_coreU32A FullCoreU32A $fn $hi $hm)
local macro "stCA" fn:ident v:ident hi:ident hm:ident s:ident : tactic =>
  `(tactic| stA fullMem_eq_coreU32A FullCoreU32A $fn $v $hi $hm $s)
local macro "ldCU" fn:ident hi:ident hm:ident : tactic =>
  `(tactic| ldA fullMem_eq_coreU32B FullCoreU32B $fn $hi $hm)
local macro "stCU" fn:ident v:ident hi:ident hm:ident s:ident : tactic =>
  `(tactic| stA fullMem_eq_coreU32B FullCoreU32B $fn $v $hi $hm $s)
local macro "ldCD" fn:ident hi:ident hm:ident : tactic =>
  `(tactic| ldA fullMem_eq_coreDyn FullCoreDynArrs $fn $hi $hm)
local macro "stCD" fn:ident v:ident hi:ident hm:ident s:ident : tactic =>
  `(tactic| stA fullMem_eq_coreDyn FullCoreDynArrs $fn $v $hi $hm $s)
local macro "ldSB" fn:ident hi:ident hm:ident : tactic =>
  `(tactic| ldA fullMem_eq_scrByte FullScrByteArrs $fn $hi $hm)
local macro "stSB" fn:ident v:ident hi:ident hm:ident s:ident : tactic =>
  `(tactic| stA fullMem_eq_scrByte FullScrByteArrs $fn $v $hi $hm $s)
local macro "ldSA" fn:ident hi:ident hm:ident : tactic =>
  `(tactic| ldA fullMem_eq_scrU32A FullScrU32A $fn $hi $hm)
local macro "stSA" fn:ident v:ident hi:ident hm:ident s:ident : tactic =>
  `(tactic| stA fullMem_eq_scrU32A FullScrU32A $fn $v $hi $hm $s)
local macro "ldSW" fn:ident hi:ident hm:ident : tactic =>
  `(tactic| ldA fullMem_eq_scrWks FullScrWksArrs $fn $hi $hm)
local macro "stSW" fn:ident v:ident hi:ident hm:ident s:ident : tactic =>
  `(tactic| stA fullMem_eq_scrWks FullScrWksArrs $fn $v $hi $hm $s)
local macro "ldSM" fn:ident hi:ident hm:ident : tactic =>
  `(tactic| ldA fullMem_eq_scrMeta FullScrMetaArrs $fn $hi $hm)
local macro "stSM" fn:ident v:ident hi:ident hm:ident s:ident : tactic =>
  `(tactic| stA fullMem_eq_scrMeta FullScrMetaArrs $fn $v $hi $hm $s)
local macro "ldSD" fn:ident hi:ident hm:ident : tactic =>
  `(tactic| ldA fullMem_eq_scrDyn FullScrDynArrs $fn $hi $hm)
local macro "stSD" fn:ident v:ident hi:ident hm:ident s:ident : tactic =>
  `(tactic| stA fullMem_eq_scrDyn FullScrDynArrs $fn $v $hi $hm $s)

attribute [scoped bv_c0 high] bv_c0_zext32_64
attribute [scoped bv_c0] bv32_lshr_1 bv32_and_1 bv32_xor_1 List.length_set Bool.false_eq_true

@[scoped bv_c0] theorem bv64_shl1_nat (x : BitVec 64) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

section HeaderAccess
variable {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}

/-! ### `KissatDimacs` header prefix (`0..24`) and tail words `0..139` (`32..1144`) -/

@[scoped c0_load] theorem load_full_mv (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 c.hdr = some (BitVec.ofNat 64 c.mv) := load_dimacs_mv (focus_dimacs hm)
@[scoped c0_load] theorem load_full_nc (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 8) = some (BitVec.ofNat 64 c.nc) := load_dimacs_nc (focus_dimacs hm)
@[scoped c0_load] theorem load_full_cur (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 16) = some s.core.d_cur := load_dimacs_cur (focus_dimacs hm)
@[scoped c0_load] theorem load_full_val (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 24) = some s.core.d_val := load_dimacs_val (focus_dimacs hm)
@[scoped c0_store] theorem store_full_cur (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 16) ∧ (FullMem c { s with core := { s.core with d_cur := v } } ⋆ R)
      (storeMem m i64 (c.hdr + 16) v) := by
  obtain ⟨hok, hst⟩ := store_dimacs_cur v (focus_dimacs hm); exact ⟨hok, unfocus_dimacs hst⟩

@[scoped c0_load] theorem load_full_arena_cap (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  32) = some (BitVec.ofNat 64 c.arena_cap) := gH 0 hm
@[scoped c0_load] theorem load_full_wcap (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 40) =
  some (BitVec.ofNat 64 c.wcap) := gH 1 hm
@[scoped c0_load] theorem load_full_arena_len (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  48) = some (BitVec.ofNat 64 s.core.arena_len) := gH 2 hm
@[scoped c0_load] theorem load_full_wlen (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 56) =
  some (BitVec.ofNat 64 s.core.wlen) := gH 3 hm
@[scoped c0_load] theorem load_full_values_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  64) = some c.pVals := gH 4 hm
@[scoped c0_load] theorem load_full_mark_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 72)
  = some c.pMark := gH 5 hm
@[scoped c0_load] theorem load_full_level_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  80) = some c.pLevel := gH 6 hm
@[scoped c0_load] theorem load_full_reason_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  88) = some c.pReason := gH 7 hm
@[scoped c0_load] theorem load_full_trail_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  96) = some c.pTrail := gH 8 hm
@[scoped c0_load] theorem load_full_watch_vec_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 104) = some c.pWvec := gH 9 hm
@[scoped c0_load] theorem load_full_arena_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  112) = some c.pArena := gH 10 hm
@[scoped c0_load] theorem load_full_watch_stk_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 120) = some c.pWstk := gH 11 hm
@[scoped c0_load] theorem load_full_delayed_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  128) = some c.pDelayed := gH 12 hm
@[scoped c0_load] theorem load_full_tmp_lits_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  136) = some c.pTmp := gH 13 hm
@[scoped c0_load] theorem load_full_trail_end (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  144) = some (BitVec.ofNat 64 s.core.trail_end) := gH 14 hm
@[scoped c0_load] theorem load_full_propagated (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  152) = some (BitVec.ofNat 64 s.core.propagated) := gH 15 hm
@[scoped c0_load] theorem load_full_cur_level (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  160) = some (BitVec.ofNat 64 s.core.cur_level) := gH 16 hm
@[scoped c0_load] theorem load_full_fuel (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 168) =
  some s.core.fuel := gH 17 hm
@[scoped c0_load] theorem load_full_confl_ref (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  176) = some s.core.confl_ref := gH 18 hm
@[scoped c0_load] theorem load_full_tmp_cnt (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 184)
  = some (BitVec.ofNat 64 s.core.tmp_cnt) := gH 19 hm
@[scoped c0_load] theorem load_full_tmp_len (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 192)
  = some (BitVec.ofNat 64 s.core.tmp_len) := gH 20 hm
@[scoped c0_load] theorem load_full_heap_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  200) = some c.pHeap := gH 21 hm
@[scoped c0_load] theorem load_full_pos_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 208)
  = some c.pPos := gH 22 hm
@[scoped c0_load] theorem load_full_score_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  216) = some c.pScore := gH 23 hm
@[scoped c0_load] theorem load_full_phases_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  224) = some c.pPhases := gH 24 hm
@[scoped c0_load] theorem load_full_min_stk_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  232) = some c.pMinStk := gH 25 hm
@[scoped c0_load] theorem load_full_min_clr_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  240) = some c.pMinClr := gH 26 hm
@[scoped c0_load] theorem load_full_heap_len (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  248) = some (BitVec.ofNat 64 s.scratch.heap_len) := gH 27 hm
@[scoped c0_load] theorem load_full_scinc (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 256) =
  some s.scratch.scinc := gH 28 hm
@[scoped c0_load] theorem load_full_min_depth (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  264) = some (BitVec.ofNat 64 c.minDepth) := gH 29 hm
@[scoped c0_load] theorem load_full_min_clr_len (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  272) = some (BitVec.ofNat 64 s.core.min_clr_len) := gH 30 hm
@[scoped c0_load] theorem load_full_min_clr_full (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  280) = some s.core.min_clr_full := gH 31 hm
@[scoped c0_load] theorem load_full_rel_period (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  288) = some s.scratch.rel_period := gH 32 hm
@[scoped c0_load] theorem load_full_rel_limit (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  296) = some s.scratch.rel_limit := gH 33 hm
@[scoped c0_load] theorem load_full_rel_wait (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  304) = some s.scratch.rel_wait := gH 34 hm
@[scoped c0_load] theorem load_full_rel_u (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 312) =
  some s.scratch.rel_u := gH 35 hm
@[scoped c0_load] theorem load_full_rel_v (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 320) =
  some s.scratch.rel_v := gH 36 hm
@[scoped c0_load] theorem load_full_rel_trigger (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  328) = some s.scratch.rel_trigger := gH 37 hm
@[scoped c0_load] theorem load_full_conflicts (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  336) = some s.scratch.conflicts := gH 38 hm
@[scoped c0_load] theorem load_full_learned_lits (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  344) = some s.scratch.learned_lits := gH 39 hm
@[scoped c0_load] theorem load_full_min_removed (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  352) = some s.scratch.min_removed := gH 40 hm
@[scoped c0_load] theorem load_full_trail_pos_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 360) = some c.pTrailPos := gH 41 hm
@[scoped c0_load] theorem load_full_q_prev_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  368) = some c.pQPrev := gH 42 hm
@[scoped c0_load] theorem load_full_q_next_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  376) = some c.pQNext := gH 43 hm
@[scoped c0_load] theorem load_full_q_stamp_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  384) = some c.pQStamp := gH 44 hm
@[scoped c0_load] theorem load_full_phases_target_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64
  (c.hdr + 392) = some c.pPhasesTarget := gH 45 hm
@[scoped c0_load] theorem load_full_phases_best_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64
  (c.hdr + 400) = some c.pPhasesBest := gH 46 hm
@[scoped c0_load] theorem load_full_wsort_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  408) = some c.pWsort := gH 47 hm
@[scoped c0_load] theorem load_full_shrink_stk_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 416) = some c.pShrinkStk := gH 48 hm
@[scoped c0_load] theorem load_full_red_refs_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  424) = some c.pRedRefs := gH 49 hm
@[scoped c0_load] theorem load_full_glue_used_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 432) = some c.pGlueUsed := gH 50 hm
@[scoped c0_load] theorem load_full_red_cap (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 440)
  = some (BitVec.ofNat 64 c.red_cap) := gH 51 hm
@[scoped c0_load] theorem load_full_delayed_cap (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  448) = some (BitVec.ofNat 64 c.delayed_cap) := gH 52 hm
@[scoped c0_load] theorem load_full_delayed_len (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  456) = some (BitVec.ofNat 64 s.scratch.delayed_len) := gH 53 hm
@[scoped c0_load] theorem load_full_wusable (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 464)
  = some s.core.wusable := gH 54 hm
@[scoped c0_load] theorem load_full_arena_garbage (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 472) = some s.core.arena_garbage := gH 55 hm
@[scoped c0_load] theorem load_full_first_reducible (hm : (FullMem c s ⋆ R) m) : loadVal m i64
  (c.hdr + 480) = some s.core.first_reducible := gH 56 hm
@[scoped c0_load] theorem load_full_num_irred (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  488) = some s.core.num_irred := gH 57 hm
@[scoped c0_load] theorem load_full_num_redundant (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 496) = some s.core.num_redundant := gH 58 hm
@[scoped c0_load] theorem load_full_num_binary (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  504) = some s.core.num_binary := gH 59 hm
@[scoped c0_load] theorem load_full_unflushed (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  512) = some s.core.unflushed := gH 60 hm
@[scoped c0_load] theorem load_full_probing (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 520)
  = some s.core.probing := gH 61 hm
@[scoped c0_load] theorem load_full_confl_type (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  528) = some s.core.confl_type := gH 62 hm
@[scoped c0_load] theorem load_full_confl_lit0 (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  536) = some s.core.confl_lit0 := gH 63 hm
@[scoped c0_load] theorem load_full_confl_lit1 (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  544) = some s.core.confl_lit1 := gH 64 hm
@[scoped c0_load] theorem load_full_stable (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 552)
  = some s.scratch.stable := gH 65 hm
@[scoped c0_load] theorem load_full_switched (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  560) = some s.scratch.switched := gH 66 hm
@[scoped c0_load] theorem load_full_mode_count (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  568) = some s.scratch.mode_count := gH 67 hm
@[scoped c0_load] theorem load_full_mode_confl_lim (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 576) = some s.scratch.mode_confl_lim := gH 68 hm
@[scoped c0_load] theorem load_full_mode_tick_lim (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 584) = some s.scratch.mode_tick_lim := gH 69 hm
@[scoped c0_load] theorem load_full_mode_saved_ticks (hm : (FullMem c s ⋆ R) m) : loadVal m i64
  (c.hdr + 592) = some s.scratch.mode_saved_ticks := gH 70 hm
@[scoped c0_load] theorem load_full_search_ticks (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  600) = some s.scratch.search_ticks := gH 71 hm
@[scoped c0_load] theorem load_full_q_first (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 608)
  = some s.scratch.q_first := gH 72 hm
@[scoped c0_load] theorem load_full_q_last (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 616)
  = some s.scratch.q_last := gH 73 hm
@[scoped c0_load] theorem load_full_q_search_idx (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  624) = some s.scratch.q_search_idx := gH 74 hm
@[scoped c0_load] theorem load_full_q_search_stamp (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 632) = some s.scratch.q_search_stamp := gH 75 hm
@[scoped c0_load] theorem load_full_q_cur_stamp (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  640) = some s.scratch.q_cur_stamp := gH 76 hm
@[scoped c0_load] theorem load_full_target_assigned (hm : (FullMem c s ⋆ R) m) : loadVal m i64
  (c.hdr + 648) = some s.scratch.target_assigned := gH 77 hm
@[scoped c0_load] theorem load_full_best_assigned (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 656) = some s.scratch.best_assigned := gH 78 hm
@[scoped c0_load] theorem load_full_rephase_limit (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 664) = some s.scratch.rephase_limit := gH 79 hm
@[scoped c0_load] theorem load_full_rephased (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  672) = some s.scratch.rephased := gH 80 hm
@[scoped c0_load] theorem load_full_reduce_limit (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  680) = some s.scratch.reduce_limit := gH 81 hm
@[scoped c0_load] theorem load_full_reductions (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  688) = some s.scratch.reductions := gH 82 hm
@[scoped c0_load] theorem load_full_tier1 (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 696) =
  some s.scratch.tier1 := gH 83 hm
@[scoped c0_load] theorem load_full_tier2 (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 704) =
  some s.scratch.tier2 := gH 84 hm
@[scoped c0_load] theorem load_full_restarts (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  712) = some s.scratch.restarts := gH 85 hm
@[scoped c0_load] theorem load_full_restart_limit (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 720) = some s.scratch.restart_limit := gH 86 hm
@[scoped c0_load] theorem load_full_ema_fast_biased (hm : (FullMem c s ⋆ R) m) : loadVal m i64
  (c.hdr + 728) = some s.scratch.ema_fast_biased := gH 87 hm
@[scoped c0_load] theorem load_full_ema_fast_exp (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  736) = some s.scratch.ema_fast_exp := gH 88 hm
@[scoped c0_load] theorem load_full_ema_slow_biased (hm : (FullMem c s ⋆ R) m) : loadVal m i64
  (c.hdr + 744) = some s.scratch.ema_slow_biased := gH 89 hm
@[scoped c0_load] theorem load_full_ema_slow_exp (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  752) = some s.scratch.ema_slow_exp := gH 90 hm
@[scoped c0_load] theorem load_full_oom (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 760) =
  some s.core.oom := gH 91 hm
@[scoped c0_load] theorem load_full_max_vars (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  768) = some (BitVec.ofNat 64 c.max_vars) := gH 92 hm
@[scoped c0_load] theorem load_full_cur_vars (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  776) = some (BitVec.ofNat 64 s.core.cur_vars) := gH 93 hm
@[scoped c0_load] theorem load_full_bva_cap (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 784)
  = some (BitVec.ofNat 64 c.bva_cap) := gH 94 hm
@[scoped c0_load] theorem load_full_unassigned (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  792) = some s.core.unassigned := gH 95 hm
@[scoped c0_load] theorem load_full_flags_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  800) = some c.pFlags := gH 96 hm
@[scoped c0_load] theorem load_full_lit_mark_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  808) = some c.pLitMark := gH 97 hm
@[scoped c0_load] theorem load_full_repr_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  816) = some c.pRepr := gH 98 hm
@[scoped c0_load] theorem load_full_sim_sig_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  824) = some c.pSimSig := gH 99 hm
@[scoped c0_load] theorem load_full_frame_trail_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64
  (c.hdr + 832) = some c.pFrameTrail := gH 100 hm
@[scoped c0_load] theorem load_full_frame_dec_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 840) = some c.pFrameDec := gH 101 hm
@[scoped c0_load] theorem load_full_work_stk1_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 848) = some c.pWorkStk1 := gH 102 hm
@[scoped c0_load] theorem load_full_work_stk2_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 856) = some c.pWorkStk2 := gH 103 hm
@[scoped c0_load] theorem load_full_tarjan_mark_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64
  (c.hdr + 864) = some c.pTarjanMark := gH 104 hm
@[scoped c0_load] theorem load_full_tarjan_reach_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64
  (c.hdr + 872) = some c.pTarjanReach := gH 105 hm
@[scoped c0_load] theorem load_full_walk_vals_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 880) = some c.pWalkVals := gH 106 hm
@[scoped c0_load] theorem load_full_walk_best_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 888) = some c.pWalkBest := gH 107 hm
@[scoped c0_load] theorem load_full_extend_stk_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 896) = some c.pExtendStk := gH 108 hm
@[scoped c0_load] theorem load_full_extend_cap (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  904) = some (BitVec.ofNat 64 c.extend_cap) := gH 109 hm
@[scoped c0_load] theorem load_full_extend_len (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  912) = some (BitVec.ofNat 64 s.scratch.extend_len) := gH 110 hm
@[scoped c0_load] theorem load_full_scratch_buf_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64
  (c.hdr + 920) = some c.pScratchBuf := gH 111 hm
@[scoped c0_load] theorem load_full_scratch_cap (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  928) = some (BitVec.ofNat 64 c.scratch_cap) := gH 112 hm
@[scoped c0_load] theorem load_full_last_learned_ptr (hm : (FullMem c s ⋆ R) m) : loadVal m i64
  (c.hdr + 936) = some c.pLastLearned := gH 113 hm
@[scoped c0_load] theorem load_full_rng_state (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  944) = some s.scratch.rng_state := gH 114 hm
@[scoped c0_load] theorem load_full_chrono_levels (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 952) = some s.scratch.chrono_levels := gH 115 hm
@[scoped c0_load] theorem load_full_otfs_cnt (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  960) = some s.scratch.otfs_cnt := gH 116 hm
@[scoped c0_load] theorem load_full_eager_sub_cnt (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 968) = some s.scratch.eager_sub_cnt := gH 117 hm
@[scoped c0_load] theorem load_full_probe_limit (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  976) = some s.scratch.probe_limit := gH 118 hm
@[scoped c0_load] theorem load_full_probings (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  984) = some s.scratch.probings := gH 119 hm
@[scoped c0_load] theorem load_full_elim_limit (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  992) = some s.scratch.elim_limit := gH 120 hm
@[scoped c0_load] theorem load_full_eliminations (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  1000) = some s.scratch.eliminations := gH 121 hm
@[scoped c0_load] theorem load_full_elim_bound (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  1008) = some s.scratch.elim_bound := gH 122 hm
@[scoped c0_load] theorem load_full_dense_mode (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  1016) = some s.core.dense_mode := gH 123 hm
@[scoped c0_load] theorem load_full_inconsistent (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  1024) = some s.core.inconsistent := gH 124 hm
@[scoped c0_load] theorem load_full_iterating (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  1032) = some s.scratch.iterating := gH 125 hm
@[scoped c0_load] theorem load_full_hbr_cnt (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  1040) = some s.scratch.hbr_cnt := gH 126 hm
@[scoped c0_load] theorem load_full_trans_cnt (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  1048) = some s.scratch.trans_cnt := gH 127 hm
@[scoped c0_load] theorem load_full_viv_cnt (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  1056) = some s.scratch.viv_cnt := gH 128 hm
@[scoped c0_load] theorem load_full_subst_cnt (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  1064) = some s.scratch.subst_cnt := gH 129 hm
@[scoped c0_load] theorem load_full_cong_cnt (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  1072) = some s.scratch.cong_cnt := gH 130 hm
@[scoped c0_load] theorem load_full_sweep_cnt (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  1080) = some s.scratch.sweep_cnt := gH 131 hm
@[scoped c0_load] theorem load_full_bve_cnt (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  1088) = some s.scratch.bve_cnt := gH 132 hm
@[scoped c0_load] theorem load_full_bce_cnt (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  1096) = some s.scratch.bce_cnt := gH 133 hm
@[scoped c0_load] theorem load_full_bva_cnt (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  1104) = some s.scratch.bva_cnt := gH 134 hm
@[scoped c0_load] theorem load_full_walk_cnt_stat (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr
  + 1112) = some s.scratch.walk_cnt_stat := gH 135 hm
@[scoped c0_load] theorem load_full_fwd_sub_cnt (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  1120) = some s.scratch.fwd_sub_cnt := gH 136 hm
@[scoped c0_load] theorem load_full_fwd_str_cnt (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr +
  1128) = some s.scratch.fwd_str_cnt := gH 137 hm
@[scoped c0_load] theorem load_full_ant_sz (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 1136)
  = some s.scratch.ant_sz := gH 138 hm
@[scoped c0_load] theorem load_full_res_sz (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.hdr + 1144)
  = some s.scratch.res_sz := gH 139 hm
/-! ### Mutable header word stores -/
@[scoped c0_store] theorem store_full_arena_len (v : Nat) (_hv : v < 2 ^ 64) (hm : (FullMem c s ⋆ R)
  m) : storeOk m i64 (c.hdr + 48) ∧ (FullMem c { s with core := { s.core with arena_len := v } } ⋆
  R) (storeMem m i64 (c.hdr + 48) (BitVec.ofNat 64 v)) := by hP 2 hm
@[scoped c0_store] theorem c0_store_full_arena_len (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 48) ∧ (FullMem c { s with core := { s.core with arena_len := v.toNat } } ⋆
  R) (storeMem m i64 (c.hdr + 48) v) := by simpa [bvId] using store_full_arena_len v.toNat v.isLt hm
@[scoped c0_store] theorem store_full_wlen (v : Nat) (_hv : v < 2 ^ 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 56) ∧ (FullMem c { s with core := { s.core with wlen := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 56) (BitVec.ofNat 64 v)) := by hP 3 hm
@[scoped c0_store] theorem c0_store_full_wlen (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk m
  i64 (c.hdr + 56) ∧ (FullMem c { s with core := { s.core with wlen := v.toNat } } ⋆ R) (storeMem m
  i64 (c.hdr + 56) v) := by simpa [bvId] using store_full_wlen v.toNat v.isLt hm
@[scoped c0_store] theorem store_full_trail_end (v : Nat) (_hv : v < 2 ^ 64) (hm : (FullMem c s ⋆ R)
  m) : storeOk m i64 (c.hdr + 144) ∧ (FullMem c { s with core := { s.core with trail_end := v } } ⋆
  R) (storeMem m i64 (c.hdr + 144) (BitVec.ofNat 64 v)) := by hP 14 hm
@[scoped c0_store] theorem c0_store_full_trail_end (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 144) ∧ (FullMem c { s with core := { s.core with trail_end := v.toNat } } ⋆
  R) (storeMem m i64 (c.hdr + 144) v)
  := by simpa [bvId] using store_full_trail_end v.toNat v.isLt hm
@[scoped c0_store] theorem store_full_propagated (v : Nat) (_hv : v < 2 ^ 64) (hm : (FullMem c s ⋆
  R) m) : storeOk m i64 (c.hdr + 152) ∧ (FullMem c
  { s with core := { s.core with propagated := v } } ⋆ R) (storeMem m i64 (c.hdr + 152)
  (BitVec.ofNat 64 v)) := by hP 15 hm
@[scoped c0_store] theorem c0_store_full_propagated (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 152) ∧ (FullMem c { s with core := { s.core with propagated := v.toNat } }
  ⋆ R) (storeMem m i64 (c.hdr + 152) v)
  := by simpa [bvId] using store_full_propagated v.toNat v.isLt hm
@[scoped c0_store] theorem store_full_cur_level (v : Nat) (_hv : v < 2 ^ 64) (hm : (FullMem c s ⋆ R)
  m) : storeOk m i64 (c.hdr + 160) ∧ (FullMem c { s with core := { s.core with cur_level := v } } ⋆
  R) (storeMem m i64 (c.hdr + 160) (BitVec.ofNat 64 v)) := by hP 16 hm
@[scoped c0_store] theorem c0_store_full_cur_level (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 160) ∧ (FullMem c { s with core := { s.core with cur_level := v.toNat } } ⋆
  R) (storeMem m i64 (c.hdr + 160) v)
  := by simpa [bvId] using store_full_cur_level v.toNat v.isLt hm
@[scoped c0_store] theorem store_full_fuel (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk m
  i64 (c.hdr + 168) ∧ (FullMem c { s with core := { s.core with fuel := v } } ⋆ R) (storeMem m i64
  (c.hdr + 168) v) := by hP 17 hm
@[scoped c0_store] theorem store_full_confl_ref (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk
  m i64 (c.hdr + 176) ∧ (FullMem c { s with core := { s.core with confl_ref := v } } ⋆ R) (storeMem
  m i64 (c.hdr + 176) v) := by hP 18 hm
@[scoped c0_store] theorem store_full_tmp_cnt (v : Nat) (_hv : v < 2 ^ 64) (hm : (FullMem c s ⋆ R)
  m) : storeOk m i64 (c.hdr + 184) ∧ (FullMem c { s with core := { s.core with tmp_cnt := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 184) (BitVec.ofNat 64 v)) := by hP 19 hm
@[scoped c0_store] theorem c0_store_full_tmp_cnt (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 184) ∧ (FullMem c { s with core := { s.core with tmp_cnt := v.toNat } } ⋆
  R) (storeMem m i64 (c.hdr + 184) v) := by simpa [bvId] using store_full_tmp_cnt v.toNat v.isLt hm
@[scoped c0_store] theorem store_full_tmp_len (v : Nat) (_hv : v < 2 ^ 64) (hm : (FullMem c s ⋆ R)
  m) : storeOk m i64 (c.hdr + 192) ∧ (FullMem c { s with core := { s.core with tmp_len := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 192) (BitVec.ofNat 64 v)) := by hP 20 hm
@[scoped c0_store] theorem c0_store_full_tmp_len (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 192) ∧ (FullMem c { s with core := { s.core with tmp_len := v.toNat } } ⋆
  R) (storeMem m i64 (c.hdr + 192) v) := by simpa [bvId] using store_full_tmp_len v.toNat v.isLt hm
@[scoped c0_store] theorem store_full_heap_len (v : Nat) (_hv : v < 2 ^ 64) (hm : (FullMem c s ⋆ R)
  m) : storeOk m i64 (c.hdr + 248) ∧ (FullMem c
  { s with scratch := { s.scratch with heap_len := v } } ⋆ R) (storeMem m i64 (c.hdr + 248)
  (BitVec.ofNat 64 v)) := by hP 27 hm
@[scoped c0_store] theorem c0_store_full_heap_len (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 248) ∧ (FullMem c
  { s with scratch := { s.scratch with heap_len := v.toNat } } ⋆ R) (storeMem m i64 (c.hdr + 248) v)
  := by simpa [bvId] using store_full_heap_len v.toNat v.isLt hm
@[scoped c0_store] theorem store_full_scinc (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk m
  i64 (c.hdr + 256) ∧ (FullMem c { s with scratch := { s.scratch with scinc := v } } ⋆ R) (storeMem
  m i64 (c.hdr + 256) v) := by hP 28 hm
@[scoped c0_store] theorem store_full_min_clr_len (v : Nat) (_hv : v < 2 ^ 64) (hm : (FullMem c s ⋆
  R) m) : storeOk m i64 (c.hdr + 272) ∧ (FullMem c
  { s with core := { s.core with min_clr_len := v } } ⋆ R) (storeMem m i64 (c.hdr + 272)
  (BitVec.ofNat 64 v)) := by hP 30 hm
@[scoped c0_store] theorem c0_store_full_min_clr_len (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 272) ∧ (FullMem c { s with core := { s.core with min_clr_len := v.toNat } }
  ⋆ R) (storeMem m i64 (c.hdr + 272) v)
  := by simpa [bvId] using store_full_min_clr_len v.toNat v.isLt hm
@[scoped c0_store] theorem store_full_min_clr_full (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 280) ∧ (FullMem c { s with core := { s.core with min_clr_full := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 280) v) := by hP 31 hm
@[scoped c0_store] theorem store_full_rel_period (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 288) ∧ (FullMem c { s with scratch := { s.scratch with rel_period := v } }
  ⋆ R) (storeMem m i64 (c.hdr + 288) v) := by hP 32 hm
@[scoped c0_store] theorem store_full_rel_limit (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk
  m i64 (c.hdr + 296) ∧ (FullMem c { s with scratch := { s.scratch with rel_limit := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 296) v) := by hP 33 hm
@[scoped c0_store] theorem store_full_rel_wait (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk
  m i64 (c.hdr + 304) ∧ (FullMem c { s with scratch := { s.scratch with rel_wait := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 304) v) := by hP 34 hm
@[scoped c0_store] theorem store_full_rel_u (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk m
  i64 (c.hdr + 312) ∧ (FullMem c { s with scratch := { s.scratch with rel_u := v } } ⋆ R) (storeMem
  m i64 (c.hdr + 312) v) := by hP 35 hm
@[scoped c0_store] theorem store_full_rel_v (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk m
  i64 (c.hdr + 320) ∧ (FullMem c { s with scratch := { s.scratch with rel_v := v } } ⋆ R) (storeMem
  m i64 (c.hdr + 320) v) := by hP 36 hm
@[scoped c0_store] theorem store_full_rel_trigger (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 328) ∧ (FullMem c { s with scratch := { s.scratch with rel_trigger := v } }
  ⋆ R) (storeMem m i64 (c.hdr + 328) v) := by hP 37 hm
@[scoped c0_store] theorem store_full_conflicts (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk
  m i64 (c.hdr + 336) ∧ (FullMem c { s with scratch := { s.scratch with conflicts := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 336) v) := by hP 38 hm
@[scoped c0_store] theorem store_full_learned_lits (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 344) ∧ (FullMem c
  { s with scratch := { s.scratch with learned_lits := v } } ⋆ R) (storeMem m i64 (c.hdr + 344) v)
  := by hP 39 hm
@[scoped c0_store] theorem store_full_min_removed (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 352) ∧ (FullMem c { s with scratch := { s.scratch with min_removed := v } }
  ⋆ R) (storeMem m i64 (c.hdr + 352) v) := by hP 40 hm
@[scoped c0_store] theorem store_full_delayed_len (v : Nat) (_hv : v < 2 ^ 64) (hm : (FullMem c s ⋆
  R) m) : storeOk m i64 (c.hdr + 456) ∧ (FullMem c
  { s with scratch := { s.scratch with delayed_len := v } } ⋆ R) (storeMem m i64 (c.hdr + 456)
  (BitVec.ofNat 64 v)) := by hP 53 hm
@[scoped c0_store] theorem c0_store_full_delayed_len (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 456) ∧ (FullMem c
  { s with scratch := { s.scratch with delayed_len := v.toNat } } ⋆ R) (storeMem m i64 (c.hdr + 456)
  v) := by simpa [bvId] using store_full_delayed_len v.toNat v.isLt hm
@[scoped c0_store] theorem store_full_wusable (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk m
  i64 (c.hdr + 464) ∧ (FullMem c { s with core := { s.core with wusable := v } } ⋆ R) (storeMem m
  i64 (c.hdr + 464) v) := by hP 54 hm
@[scoped c0_store] theorem store_full_arena_garbage (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 472) ∧ (FullMem c { s with core := { s.core with arena_garbage := v } } ⋆
  R) (storeMem m i64 (c.hdr + 472) v) := by hP 55 hm
@[scoped c0_store] theorem store_full_first_reducible (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 480) ∧ (FullMem c { s with core := { s.core with first_reducible := v } } ⋆
  R) (storeMem m i64 (c.hdr + 480) v) := by hP 56 hm
@[scoped c0_store] theorem store_full_num_irred (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk
  m i64 (c.hdr + 488) ∧ (FullMem c { s with core := { s.core with num_irred := v } } ⋆ R) (storeMem
  m i64 (c.hdr + 488) v) := by hP 57 hm
@[scoped c0_store] theorem store_full_num_redundant (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 496) ∧ (FullMem c { s with core := { s.core with num_redundant := v } } ⋆
  R) (storeMem m i64 (c.hdr + 496) v) := by hP 58 hm
@[scoped c0_store] theorem store_full_num_binary (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 504) ∧ (FullMem c { s with core := { s.core with num_binary := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 504) v) := by hP 59 hm
@[scoped c0_store] theorem store_full_unflushed (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk
  m i64 (c.hdr + 512) ∧ (FullMem c { s with core := { s.core with unflushed := v } } ⋆ R) (storeMem
  m i64 (c.hdr + 512) v) := by hP 60 hm
@[scoped c0_store] theorem store_full_probing (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk m
  i64 (c.hdr + 520) ∧ (FullMem c { s with core := { s.core with probing := v } } ⋆ R) (storeMem m
  i64 (c.hdr + 520) v) := by hP 61 hm
@[scoped c0_store] theorem store_full_confl_type (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 528) ∧ (FullMem c { s with core := { s.core with confl_type := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 528) v) := by hP 62 hm
@[scoped c0_store] theorem store_full_confl_lit0 (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 536) ∧ (FullMem c { s with core := { s.core with confl_lit0 := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 536) v) := by hP 63 hm
@[scoped c0_store] theorem store_full_confl_lit1 (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 544) ∧ (FullMem c { s with core := { s.core with confl_lit1 := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 544) v) := by hP 64 hm
@[scoped c0_store] theorem store_full_stable (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk m
  i64 (c.hdr + 552) ∧ (FullMem c { s with scratch := { s.scratch with stable := v } } ⋆ R) (storeMem
  m i64 (c.hdr + 552) v) := by hP 65 hm
@[scoped c0_store] theorem store_full_switched (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk
  m i64 (c.hdr + 560) ∧ (FullMem c { s with scratch := { s.scratch with switched := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 560) v) := by hP 66 hm
@[scoped c0_store] theorem store_full_mode_count (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 568) ∧ (FullMem c { s with scratch := { s.scratch with mode_count := v } }
  ⋆ R) (storeMem m i64 (c.hdr + 568) v) := by hP 67 hm
@[scoped c0_store] theorem store_full_mode_confl_lim (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 576) ∧ (FullMem c
  { s with scratch := { s.scratch with mode_confl_lim := v } } ⋆ R) (storeMem m i64 (c.hdr + 576) v)
  := by hP 68 hm
@[scoped c0_store] theorem store_full_mode_tick_lim (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 584) ∧ (FullMem c
  { s with scratch := { s.scratch with mode_tick_lim := v } } ⋆ R) (storeMem m i64 (c.hdr + 584) v)
  := by hP 69 hm
@[scoped c0_store] theorem store_full_mode_saved_ticks (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 592) ∧ (FullMem c
  { s with scratch := { s.scratch with mode_saved_ticks := v } } ⋆ R) (storeMem m i64 (c.hdr + 592)
  v) := by hP 70 hm
@[scoped c0_store] theorem store_full_search_ticks (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 600) ∧ (FullMem c
  { s with scratch := { s.scratch with search_ticks := v } } ⋆ R) (storeMem m i64 (c.hdr + 600) v)
  := by hP 71 hm
@[scoped c0_store] theorem store_full_q_first (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk m
  i64 (c.hdr + 608) ∧ (FullMem c { s with scratch := { s.scratch with q_first := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 608) v) := by hP 72 hm
@[scoped c0_store] theorem store_full_q_last (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk m
  i64 (c.hdr + 616) ∧ (FullMem c { s with scratch := { s.scratch with q_last := v } } ⋆ R) (storeMem
  m i64 (c.hdr + 616) v) := by hP 73 hm
@[scoped c0_store] theorem store_full_q_search_idx (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 624) ∧ (FullMem c
  { s with scratch := { s.scratch with q_search_idx := v } } ⋆ R) (storeMem m i64 (c.hdr + 624) v)
  := by hP 74 hm
@[scoped c0_store] theorem store_full_q_search_stamp (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 632) ∧ (FullMem c
  { s with scratch := { s.scratch with q_search_stamp := v } } ⋆ R) (storeMem m i64 (c.hdr + 632) v)
  := by hP 75 hm
@[scoped c0_store] theorem store_full_q_cur_stamp (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 640) ∧ (FullMem c { s with scratch := { s.scratch with q_cur_stamp := v } }
  ⋆ R) (storeMem m i64 (c.hdr + 640) v) := by hP 76 hm
@[scoped c0_store] theorem store_full_target_assigned (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 648) ∧ (FullMem c
  { s with scratch := { s.scratch with target_assigned := v } } ⋆ R) (storeMem m i64 (c.hdr + 648)
  v) := by hP 77 hm
@[scoped c0_store] theorem store_full_best_assigned (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 656) ∧ (FullMem c
  { s with scratch := { s.scratch with best_assigned := v } } ⋆ R) (storeMem m i64 (c.hdr + 656) v)
  := by hP 78 hm
@[scoped c0_store] theorem store_full_rephase_limit (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 664) ∧ (FullMem c
  { s with scratch := { s.scratch with rephase_limit := v } } ⋆ R) (storeMem m i64 (c.hdr + 664) v)
  := by hP 79 hm
@[scoped c0_store] theorem store_full_rephased (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk
  m i64 (c.hdr + 672) ∧ (FullMem c { s with scratch := { s.scratch with rephased := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 672) v) := by hP 80 hm
@[scoped c0_store] theorem store_full_reduce_limit (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 680) ∧ (FullMem c
  { s with scratch := { s.scratch with reduce_limit := v } } ⋆ R) (storeMem m i64 (c.hdr + 680) v)
  := by hP 81 hm
@[scoped c0_store] theorem store_full_reductions (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 688) ∧ (FullMem c { s with scratch := { s.scratch with reductions := v } }
  ⋆ R) (storeMem m i64 (c.hdr + 688) v) := by hP 82 hm
@[scoped c0_store] theorem store_full_tier1 (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk m
  i64 (c.hdr + 696) ∧ (FullMem c { s with scratch := { s.scratch with tier1 := v } } ⋆ R) (storeMem
  m i64 (c.hdr + 696) v) := by hP 83 hm
@[scoped c0_store] theorem store_full_tier2 (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk m
  i64 (c.hdr + 704) ∧ (FullMem c { s with scratch := { s.scratch with tier2 := v } } ⋆ R) (storeMem
  m i64 (c.hdr + 704) v) := by hP 84 hm
@[scoped c0_store] theorem store_full_restarts (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk
  m i64 (c.hdr + 712) ∧ (FullMem c { s with scratch := { s.scratch with restarts := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 712) v) := by hP 85 hm
@[scoped c0_store] theorem store_full_restart_limit (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 720) ∧ (FullMem c
  { s with scratch := { s.scratch with restart_limit := v } } ⋆ R) (storeMem m i64 (c.hdr + 720) v)
  := by hP 86 hm
@[scoped c0_store] theorem store_full_ema_fast_biased (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 728) ∧ (FullMem c
  { s with scratch := { s.scratch with ema_fast_biased := v } } ⋆ R) (storeMem m i64 (c.hdr + 728)
  v) := by hP 87 hm
@[scoped c0_store] theorem store_full_ema_fast_exp (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 736) ∧ (FullMem c
  { s with scratch := { s.scratch with ema_fast_exp := v } } ⋆ R) (storeMem m i64 (c.hdr + 736) v)
  := by hP 88 hm
@[scoped c0_store] theorem store_full_ema_slow_biased (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 744) ∧ (FullMem c
  { s with scratch := { s.scratch with ema_slow_biased := v } } ⋆ R) (storeMem m i64 (c.hdr + 744)
  v) := by hP 89 hm
@[scoped c0_store] theorem store_full_ema_slow_exp (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 752) ∧ (FullMem c
  { s with scratch := { s.scratch with ema_slow_exp := v } } ⋆ R) (storeMem m i64 (c.hdr + 752) v)
  := by hP 90 hm
@[scoped c0_store] theorem store_full_oom (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk m i64
  (c.hdr + 760) ∧ (FullMem c { s with core := { s.core with oom := v } } ⋆ R) (storeMem m i64 (c.hdr
  + 760) v) := by hP 91 hm
@[scoped c0_store] theorem store_full_cur_vars (v : Nat) (_hv : v < 2 ^ 64) (hm : (FullMem c s ⋆ R)
  m) : storeOk m i64 (c.hdr + 776) ∧ (FullMem c { s with core := { s.core with cur_vars := v } } ⋆
  R) (storeMem m i64 (c.hdr + 776) (BitVec.ofNat 64 v)) := by hP 93 hm
@[scoped c0_store] theorem c0_store_full_cur_vars (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 776) ∧ (FullMem c { s with core := { s.core with cur_vars := v.toNat } } ⋆
  R) (storeMem m i64 (c.hdr + 776) v) := by simpa [bvId] using store_full_cur_vars v.toNat v.isLt hm
@[scoped c0_store] theorem store_full_unassigned (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 792) ∧ (FullMem c { s with core := { s.core with unassigned := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 792) v) := by hP 95 hm
@[scoped c0_store] theorem store_full_extend_len (v : Nat) (_hv : v < 2 ^ 64) (hm : (FullMem c s ⋆
  R) m) : storeOk m i64 (c.hdr + 912) ∧ (FullMem c
  { s with scratch := { s.scratch with extend_len := v } } ⋆ R) (storeMem m i64 (c.hdr + 912)
  (BitVec.ofNat 64 v)) := by hP 110 hm
@[scoped c0_store] theorem c0_store_full_extend_len (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 912) ∧ (FullMem c
  { s with scratch := { s.scratch with extend_len := v.toNat } } ⋆ R) (storeMem m i64 (c.hdr + 912)
  v) := by simpa [bvId] using store_full_extend_len v.toNat v.isLt hm
@[scoped c0_store] theorem store_full_rng_state (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk
  m i64 (c.hdr + 944) ∧ (FullMem c { s with scratch := { s.scratch with rng_state := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 944) v) := by hP 114 hm
@[scoped c0_store] theorem store_full_chrono_levels (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 952) ∧ (FullMem c
  { s with scratch := { s.scratch with chrono_levels := v } } ⋆ R) (storeMem m i64 (c.hdr + 952) v)
  := by hP 115 hm
@[scoped c0_store] theorem store_full_otfs_cnt (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk
  m i64 (c.hdr + 960) ∧ (FullMem c { s with scratch := { s.scratch with otfs_cnt := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 960) v) := by hP 116 hm
@[scoped c0_store] theorem store_full_eager_sub_cnt (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 968) ∧ (FullMem c
  { s with scratch := { s.scratch with eager_sub_cnt := v } } ⋆ R) (storeMem m i64 (c.hdr + 968) v)
  := by hP 117 hm
@[scoped c0_store] theorem store_full_probe_limit (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 976) ∧ (FullMem c { s with scratch := { s.scratch with probe_limit := v } }
  ⋆ R) (storeMem m i64 (c.hdr + 976) v) := by hP 118 hm
@[scoped c0_store] theorem store_full_probings (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk
  m i64 (c.hdr + 984) ∧ (FullMem c { s with scratch := { s.scratch with probings := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 984) v) := by hP 119 hm
@[scoped c0_store] theorem store_full_elim_limit (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 992) ∧ (FullMem c { s with scratch := { s.scratch with elim_limit := v } }
  ⋆ R) (storeMem m i64 (c.hdr + 992) v) := by hP 120 hm
@[scoped c0_store] theorem store_full_eliminations (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 1000) ∧ (FullMem c
  { s with scratch := { s.scratch with eliminations := v } } ⋆ R) (storeMem m i64 (c.hdr + 1000) v)
  := by hP 121 hm
@[scoped c0_store] theorem store_full_elim_bound (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 1008) ∧ (FullMem c { s with scratch := { s.scratch with elim_bound := v } }
  ⋆ R) (storeMem m i64 (c.hdr + 1008) v) := by hP 122 hm
@[scoped c0_store] theorem store_full_dense_mode (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 1016) ∧ (FullMem c { s with core := { s.core with dense_mode := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 1016) v) := by hP 123 hm
@[scoped c0_store] theorem store_full_inconsistent (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 1024) ∧ (FullMem c { s with core := { s.core with inconsistent := v } } ⋆
  R) (storeMem m i64 (c.hdr + 1024) v) := by hP 124 hm
@[scoped c0_store] theorem store_full_iterating (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk
  m i64 (c.hdr + 1032) ∧ (FullMem c { s with scratch := { s.scratch with iterating := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 1032) v) := by hP 125 hm
@[scoped c0_store] theorem store_full_hbr_cnt (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk m
  i64 (c.hdr + 1040) ∧ (FullMem c { s with scratch := { s.scratch with hbr_cnt := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 1040) v) := by hP 126 hm
@[scoped c0_store] theorem store_full_trans_cnt (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk
  m i64 (c.hdr + 1048) ∧ (FullMem c { s with scratch := { s.scratch with trans_cnt := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 1048) v) := by hP 127 hm
@[scoped c0_store] theorem store_full_viv_cnt (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk m
  i64 (c.hdr + 1056) ∧ (FullMem c { s with scratch := { s.scratch with viv_cnt := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 1056) v) := by hP 128 hm
@[scoped c0_store] theorem store_full_subst_cnt (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk
  m i64 (c.hdr + 1064) ∧ (FullMem c { s with scratch := { s.scratch with subst_cnt := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 1064) v) := by hP 129 hm
@[scoped c0_store] theorem store_full_cong_cnt (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk
  m i64 (c.hdr + 1072) ∧ (FullMem c { s with scratch := { s.scratch with cong_cnt := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 1072) v) := by hP 130 hm
@[scoped c0_store] theorem store_full_sweep_cnt (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk
  m i64 (c.hdr + 1080) ∧ (FullMem c { s with scratch := { s.scratch with sweep_cnt := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 1080) v) := by hP 131 hm
@[scoped c0_store] theorem store_full_bve_cnt (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk m
  i64 (c.hdr + 1088) ∧ (FullMem c { s with scratch := { s.scratch with bve_cnt := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 1088) v) := by hP 132 hm
@[scoped c0_store] theorem store_full_bce_cnt (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk m
  i64 (c.hdr + 1096) ∧ (FullMem c { s with scratch := { s.scratch with bce_cnt := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 1096) v) := by hP 133 hm
@[scoped c0_store] theorem store_full_bva_cnt (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk m
  i64 (c.hdr + 1104) ∧ (FullMem c { s with scratch := { s.scratch with bva_cnt := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 1104) v) := by hP 134 hm
@[scoped c0_store] theorem store_full_walk_cnt_stat (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 1112) ∧ (FullMem c
  { s with scratch := { s.scratch with walk_cnt_stat := v } } ⋆ R) (storeMem m i64 (c.hdr + 1112) v)
  := by hP 135 hm
@[scoped c0_store] theorem store_full_fwd_sub_cnt (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 1120) ∧ (FullMem c
  { s with scratch := { s.scratch with fwd_sub_cnt := v } } ⋆ R) (storeMem m i64 (c.hdr + 1120) v)
  := by hP 136 hm
@[scoped c0_store] theorem store_full_fwd_str_cnt (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
  storeOk m i64 (c.hdr + 1128) ∧ (FullMem c
  { s with scratch := { s.scratch with fwd_str_cnt := v } } ⋆ R) (storeMem m i64 (c.hdr + 1128) v)
  := by hP 137 hm
@[scoped c0_store] theorem store_full_ant_sz (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk m
  i64 (c.hdr + 1136) ∧ (FullMem c { s with scratch := { s.scratch with ant_sz := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 1136) v) := by hP 138 hm
@[scoped c0_store] theorem store_full_res_sz (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) : storeOk m
  i64 (c.hdr + 1144) ∧ (FullMem c { s with scratch := { s.scratch with res_sz := v } } ⋆ R)
  (storeMem m i64 (c.hdr + 1144) v) := by hP 139 hm
/-! ### `FullCoreArrays` (`17` arrays) -/
@[scoped c0_load] theorem load_full_vals {i : Nat} (hi : i < s.core.vals.length) (hm : (FullMem c s
  ⋆ R) m) : loadVal m i8 (c.pVals + BitVec.ofNat 64 i) = some s.core.vals[i]
  := by ldCB arrGetI8 hi hm
@[scoped c0_load] theorem c0_load_full_vals {i : BitVec 64} (hi : i.toNat < s.core.vals.length) (hm
  : (FullMem c s ⋆ R) m) : loadVal m i8 (c.pVals + i) = some s.core.vals[i.toNat]
  := by lB load_full_vals hi hm
@[scoped c0_store] theorem store_full_vals {i : Nat} (v : BitVec 8) (hi : i < s.core.vals.length)
  (hm : (FullMem c s ⋆ R) m) : storeOk m i8 (c.pVals + BitVec.ofNat 64 i) ∧ (FullMem c
  { s with core := { s.core with vals := s.core.vals.set i v } } ⋆ R) (storeMem m i8 (c.pVals +
  BitVec.ofNat 64 i) v) := by stCB arrPutI8 v hi hm s
@[scoped c0_store] theorem c0_store_full_vals {i : BitVec 64} (v : BitVec 8) (hi : i.toNat <
  s.core.vals.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i8 (c.pVals + i) ∧ (FullMem c
  { s with core := { s.core with vals := s.core.vals.set i.toNat v } } ⋆ R) (storeMem m i8 (c.pVals
  + i) v) := by sB store_full_vals v hi hm
@[scoped c0_load] theorem load_full_lit_mark {i : Nat} (hi : i < s.core.lit_mark.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i8 (c.pLitMark + BitVec.ofNat 64 i) = some s.core.lit_mark[i]
  := by ldCB arrGetI8 hi hm
@[scoped c0_load] theorem c0_load_full_lit_mark {i : BitVec 64} (hi : i.toNat <
  s.core.lit_mark.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i8 (c.pLitMark + i) = some
  s.core.lit_mark[i.toNat] := by lB load_full_lit_mark hi hm
@[scoped c0_store] theorem store_full_lit_mark {i : Nat} (v : BitVec 8) (hi : i <
  s.core.lit_mark.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i8 (c.pLitMark + BitVec.ofNat 64 i)
  ∧ (FullMem c { s with core := { s.core with lit_mark := s.core.lit_mark.set i v } } ⋆ R) (storeMem
  m i8 (c.pLitMark + BitVec.ofNat 64 i) v) := by stCB arrPutI8 v hi hm s
@[scoped c0_store] theorem c0_store_full_lit_mark {i : BitVec 64} (v : BitVec 8) (hi : i.toNat <
  s.core.lit_mark.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i8 (c.pLitMark + i) ∧ (FullMem c
  { s with core := { s.core with lit_mark := s.core.lit_mark.set i.toNat v } } ⋆ R) (storeMem m i8
  (c.pLitMark + i) v) := by sB store_full_lit_mark v hi hm
@[scoped c0_load] theorem load_full_mrk {i : Nat} (hi : i < s.core.mrk.length) (hm : (FullMem c s ⋆
  R) m) : loadVal m i8 (c.pMark + BitVec.ofNat 64 i) = some s.core.mrk[i] := by ldCB arrGetI8 hi hm
@[scoped c0_load] theorem c0_load_full_mrk {i : BitVec 64} (hi : i.toNat < s.core.mrk.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i8 (c.pMark + i) = some s.core.mrk[i.toNat]
  := by lB load_full_mrk hi hm
@[scoped c0_store] theorem store_full_mrk {i : Nat} (v : BitVec 8) (hi : i < s.core.mrk.length) (hm
  : (FullMem c s ⋆ R) m) : storeOk m i8 (c.pMark + BitVec.ofNat 64 i) ∧ (FullMem c
  { s with core := { s.core with mrk := s.core.mrk.set i v } } ⋆ R) (storeMem m i8 (c.pMark +
  BitVec.ofNat 64 i) v) := by stCB arrPutI8 v hi hm s
@[scoped c0_store] theorem c0_store_full_mrk {i : BitVec 64} (v : BitVec 8) (hi : i.toNat <
  s.core.mrk.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i8 (c.pMark + i) ∧ (FullMem c
  { s with core := { s.core with mrk := s.core.mrk.set i.toNat v } } ⋆ R) (storeMem m i8 (c.pMark +
  i) v) := by sB store_full_mrk v hi hm
@[scoped c0_load] theorem load_full_flags {i : Nat} (hi : i < s.core.flags.length) (hm : (FullMem c
  s ⋆ R) m) : loadVal m i32 (c.pFlags + BitVec.ofNat 64 (4 * i)) = some s.core.flags[i]
  := by ldCA arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_flags {i : BitVec 64} (hi : i.toNat < s.core.flags.length)
  (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pFlags + i * 4) = some s.core.flags[i.toNat]
  := by l4 load_full_flags hi hm
@[scoped c0_store] theorem store_full_flags {i : Nat} (v : BitVec 32) (hi : i < s.core.flags.length)
  (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pFlags + BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with core := { s.core with flags := s.core.flags.set i v } } ⋆ R) (storeMem m i32 (c.pFlags +
  BitVec.ofNat 64 (4 * i)) v) := by stCA arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_flags {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.core.flags.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pFlags + i * 4) ∧ (FullMem c
  { s with core := { s.core with flags := s.core.flags.set i.toNat v } } ⋆ R) (storeMem m i32
  (c.pFlags + i * 4) v) := by s4 store_full_flags v hi hm
@[scoped c0_load] theorem load_full_lvl {i : Nat} (hi : i < s.core.lvl.length) (hm : (FullMem c s ⋆
  R) m) : loadVal m i32 (c.pLevel + BitVec.ofNat 64 (4 * i)) = some s.core.lvl[i]
  := by ldCA arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_lvl {i : BitVec 64} (hi : i.toNat < s.core.lvl.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i32 (c.pLevel + i * 4) = some s.core.lvl[i.toNat]
  := by l4 load_full_lvl hi hm
@[scoped c0_store] theorem store_full_lvl {i : Nat} (v : BitVec 32) (hi : i < s.core.lvl.length) (hm
  : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pLevel + BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with core := { s.core with lvl := s.core.lvl.set i v } } ⋆ R) (storeMem m i32 (c.pLevel +
  BitVec.ofNat 64 (4 * i)) v) := by stCA arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_lvl {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.core.lvl.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pLevel + i * 4) ∧ (FullMem c
  { s with core := { s.core with lvl := s.core.lvl.set i.toNat v } } ⋆ R) (storeMem m i32 (c.pLevel
  + i * 4) v) := by s4 store_full_lvl v hi hm
@[scoped c0_load] theorem load_full_rsns {i : Nat} (hi : i < s.core.rsns.length) (hm : (FullMem c s
  ⋆ R) m) : loadVal m i32 (c.pReason + BitVec.ofNat 64 (4 * i)) = some s.core.rsns[i]
  := by ldCA arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_rsns {i : BitVec 64} (hi : i.toNat < s.core.rsns.length) (hm
  : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pReason + i * 4) = some s.core.rsns[i.toNat]
  := by l4 load_full_rsns hi hm
@[scoped c0_store] theorem store_full_rsns {i : Nat} (v : BitVec 32) (hi : i < s.core.rsns.length)
  (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pReason + BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with core := { s.core with rsns := s.core.rsns.set i v } } ⋆ R) (storeMem m i32 (c.pReason +
  BitVec.ofNat 64 (4 * i)) v) := by stCA arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_rsns {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.core.rsns.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pReason + i * 4) ∧ (FullMem c
  { s with core := { s.core with rsns := s.core.rsns.set i.toNat v } } ⋆ R) (storeMem m i32
  (c.pReason + i * 4) v) := by s4 store_full_rsns v hi hm
@[scoped c0_load] theorem load_full_trl {i : Nat} (hi : i < s.core.trl.length) (hm : (FullMem c s ⋆
  R) m) : loadVal m i32 (c.pTrail + BitVec.ofNat 64 (4 * i)) = some s.core.trl[i]
  := by ldCA arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_trl {i : BitVec 64} (hi : i.toNat < s.core.trl.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i32 (c.pTrail + i * 4) = some s.core.trl[i.toNat]
  := by l4 load_full_trl hi hm
@[scoped c0_store] theorem store_full_trl {i : Nat} (v : BitVec 32) (hi : i < s.core.trl.length) (hm
  : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pTrail + BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with core := { s.core with trl := s.core.trl.set i v } } ⋆ R) (storeMem m i32 (c.pTrail +
  BitVec.ofNat 64 (4 * i)) v) := by stCA arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_trl {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.core.trl.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pTrail + i * 4) ∧ (FullMem c
  { s with core := { s.core with trl := s.core.trl.set i.toNat v } } ⋆ R) (storeMem m i32 (c.pTrail
  + i * 4) v) := by s4 store_full_trl v hi hm
@[scoped c0_load] theorem load_full_trail_pos {i : Nat} (hi : i < s.core.trail_pos.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i32 (c.pTrailPos + BitVec.ofNat 64 (4 * i)) = some
  s.core.trail_pos[i] := by ldCA arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_trail_pos {i : BitVec 64} (hi : i.toNat <
  s.core.trail_pos.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pTrailPos + i * 4) = some
  s.core.trail_pos[i.toNat] := by l4 load_full_trail_pos hi hm
@[scoped c0_store] theorem store_full_trail_pos {i : Nat} (v : BitVec 32) (hi : i <
  s.core.trail_pos.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pTrailPos +
  BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with core := { s.core with trail_pos := s.core.trail_pos.set i v } } ⋆ R) (storeMem m i32
  (c.pTrailPos + BitVec.ofNat 64 (4 * i)) v) := by stCA arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_trail_pos {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.core.trail_pos.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pTrailPos + i * 4) ∧
  (FullMem c { s with core := { s.core with trail_pos := s.core.trail_pos.set i.toNat v } } ⋆ R)
  (storeMem m i32 (c.pTrailPos + i * 4) v) := by s4 store_full_trail_pos v hi hm
@[scoped c0_load] theorem load_full_tmp {i : Nat} (hi : i < s.core.tmp.length) (hm : (FullMem c s ⋆
  R) m) : loadVal m i32 (c.pTmp + BitVec.ofNat 64 (4 * i)) = some s.core.tmp[i]
  := by ldCA arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_tmp {i : BitVec 64} (hi : i.toNat < s.core.tmp.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i32 (c.pTmp + i * 4) = some s.core.tmp[i.toNat]
  := by l4 load_full_tmp hi hm
@[scoped c0_store] theorem store_full_tmp {i : Nat} (v : BitVec 32) (hi : i < s.core.tmp.length) (hm
  : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pTmp + BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with core := { s.core with tmp := s.core.tmp.set i v } } ⋆ R) (storeMem m i32 (c.pTmp +
  BitVec.ofNat 64 (4 * i)) v) := by stCA arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_tmp {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pTmp + i * 4) ∧ (FullMem c
  { s with core := { s.core with tmp := s.core.tmp.set i.toNat v } } ⋆ R) (storeMem m i32 (c.pTmp +
  i * 4) v) := by s4 store_full_tmp v hi hm
@[scoped c0_load] theorem load_full_min_clr {i : Nat} (hi : i < s.core.min_clr.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i32 (c.pMinClr + BitVec.ofNat 64 (4 * i)) = some
  s.core.min_clr[i] := by ldCA arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_min_clr {i : BitVec 64} (hi : i.toNat <
  s.core.min_clr.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pMinClr + i * 4) = some
  s.core.min_clr[i.toNat] := by l4 load_full_min_clr hi hm
@[scoped c0_store] theorem store_full_min_clr {i : Nat} (v : BitVec 32) (hi : i <
  s.core.min_clr.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pMinClr +
  BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with core := { s.core with min_clr := s.core.min_clr.set i v } } ⋆ R) (storeMem m i32
  (c.pMinClr + BitVec.ofNat 64 (4 * i)) v) := by stCA arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_min_clr {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.core.min_clr.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pMinClr + i * 4) ∧ (FullMem c
  { s with core := { s.core with min_clr := s.core.min_clr.set i.toNat v } } ⋆ R) (storeMem m i32
  (c.pMinClr + i * 4) v) := by s4 store_full_min_clr v hi hm
@[scoped c0_load] theorem load_full_frame_trail {i : Nat} (hi : i < s.core.frame_trail.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i32 (c.pFrameTrail + BitVec.ofNat 64 (4 * i)) = some
  s.core.frame_trail[i] := by ldCU arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_frame_trail {i : BitVec 64} (hi : i.toNat <
  s.core.frame_trail.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pFrameTrail + i * 4) =
  some s.core.frame_trail[i.toNat] := by l4 load_full_frame_trail hi hm
@[scoped c0_store] theorem store_full_frame_trail {i : Nat} (v : BitVec 32) (hi : i <
  s.core.frame_trail.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pFrameTrail +
  BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with core := { s.core with frame_trail := s.core.frame_trail.set i v } } ⋆ R) (storeMem m i32
  (c.pFrameTrail + BitVec.ofNat 64 (4 * i)) v) := by stCU arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_frame_trail {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.core.frame_trail.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pFrameTrail + i * 4) ∧
  (FullMem c { s with core := { s.core with frame_trail := s.core.frame_trail.set i.toNat v } } ⋆ R)
  (storeMem m i32 (c.pFrameTrail + i * 4) v) := by s4 store_full_frame_trail v hi hm
@[scoped c0_load] theorem load_full_frame_dec {i : Nat} (hi : i < s.core.frame_dec.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i32 (c.pFrameDec + BitVec.ofNat 64 (4 * i)) = some
  s.core.frame_dec[i] := by ldCU arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_frame_dec {i : BitVec 64} (hi : i.toNat <
  s.core.frame_dec.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pFrameDec + i * 4) = some
  s.core.frame_dec[i.toNat] := by l4 load_full_frame_dec hi hm
@[scoped c0_store] theorem store_full_frame_dec {i : Nat} (v : BitVec 32) (hi : i <
  s.core.frame_dec.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pFrameDec +
  BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with core := { s.core with frame_dec := s.core.frame_dec.set i v } } ⋆ R) (storeMem m i32
  (c.pFrameDec + BitVec.ofNat 64 (4 * i)) v) := by stCU arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_frame_dec {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.core.frame_dec.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pFrameDec + i * 4) ∧
  (FullMem c { s with core := { s.core with frame_dec := s.core.frame_dec.set i.toNat v } } ⋆ R)
  (storeMem m i32 (c.pFrameDec + i * 4) v) := by s4 store_full_frame_dec v hi hm
@[scoped c0_load] theorem load_full_wvec {i : Nat} (hi : i < s.core.wvec.length) (hm : (FullMem c s
  ⋆ R) m) : loadVal m i32 (c.pWvec + BitVec.ofNat 64 (4 * i)) = some s.core.wvec[i]
  := by ldCU arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_wvec {i : BitVec 64} (hi : i.toNat < s.core.wvec.length) (hm
  : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pWvec + i * 4) = some s.core.wvec[i.toNat]
  := by l4 load_full_wvec hi hm
@[scoped c0_store] theorem store_full_wvec {i : Nat} (v : BitVec 32) (hi : i < s.core.wvec.length)
  (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pWvec + BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with core := { s.core with wvec := s.core.wvec.set i v } } ⋆ R) (storeMem m i32 (c.pWvec +
  BitVec.ofNat 64 (4 * i)) v) := by stCU arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_wvec {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.core.wvec.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pWvec + i * 4) ∧ (FullMem c
  { s with core := { s.core with wvec := s.core.wvec.set i.toNat v } } ⋆ R) (storeMem m i32 (c.pWvec
  + i * 4) v) := by s4 store_full_wvec v hi hm
@[scoped c0_load] theorem load_full_repr {i : Nat} (hi : i < s.core.repr.length) (hm : (FullMem c s
  ⋆ R) m) : loadVal m i32 (c.pRepr + BitVec.ofNat 64 (4 * i)) = some s.core.repr[i]
  := by ldCU arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_repr {i : BitVec 64} (hi : i.toNat < s.core.repr.length) (hm
  : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pRepr + i * 4) = some s.core.repr[i.toNat]
  := by l4 load_full_repr hi hm
@[scoped c0_store] theorem store_full_repr {i : Nat} (v : BitVec 32) (hi : i < s.core.repr.length)
  (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pRepr + BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with core := { s.core with repr := s.core.repr.set i v } } ⋆ R) (storeMem m i32 (c.pRepr +
  BitVec.ofNat 64 (4 * i)) v) := by stCU arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_repr {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.core.repr.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pRepr + i * 4) ∧ (FullMem c
  { s with core := { s.core with repr := s.core.repr.set i.toNat v } } ⋆ R) (storeMem m i32 (c.pRepr
  + i * 4) v) := by s4 store_full_repr v hi hm
@[scoped c0_load] theorem load_full_min_stk {i : Nat} (hi : i < s.core.min_stk.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i32 (c.pMinStk + BitVec.ofNat 64 (4 * i)) = some
  s.core.min_stk[i] := by ldCU arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_min_stk {i : BitVec 64} (hi : i.toNat <
  s.core.min_stk.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pMinStk + i * 4) = some
  s.core.min_stk[i.toNat] := by l4 load_full_min_stk hi hm
@[scoped c0_store] theorem store_full_min_stk {i : Nat} (v : BitVec 32) (hi : i <
  s.core.min_stk.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pMinStk +
  BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with core := { s.core with min_stk := s.core.min_stk.set i v } } ⋆ R) (storeMem m i32
  (c.pMinStk + BitVec.ofNat 64 (4 * i)) v) := by stCU arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_min_stk {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.core.min_stk.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pMinStk + i * 4) ∧ (FullMem c
  { s with core := { s.core with min_stk := s.core.min_stk.set i.toNat v } } ⋆ R) (storeMem m i32
  (c.pMinStk + i * 4) v) := by s4 store_full_min_stk v hi hm
@[scoped c0_load] theorem load_full_arena {i : Nat} (hi : i < s.core.arena.length) (hm : (FullMem c
  s ⋆ R) m) : loadVal m i32 (c.pArena + BitVec.ofNat 64 (4 * i)) = some s.core.arena[i]
  := by ldCD arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_arena {i : BitVec 64} (hi : i.toNat < s.core.arena.length)
  (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pArena + i * 4) = some s.core.arena[i.toNat]
  := by l4 load_full_arena hi hm
@[scoped c0_store] theorem store_full_arena {i : Nat} (v : BitVec 32) (hi : i < s.core.arena.length)
  (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pArena + BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with core := { s.core with arena := s.core.arena.set i v } } ⋆ R) (storeMem m i32 (c.pArena +
  BitVec.ofNat 64 (4 * i)) v) := by stCD arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_arena {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.core.arena.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pArena + i * 4) ∧ (FullMem c
  { s with core := { s.core with arena := s.core.arena.set i.toNat v } } ⋆ R) (storeMem m i32
  (c.pArena + i * 4) v) := by s4 store_full_arena v hi hm
@[scoped c0_load] theorem load_full_wstk {i : Nat} (hi : i < s.core.wstk.length) (hm : (FullMem c s
  ⋆ R) m) : loadVal m i32 (c.pWstk + BitVec.ofNat 64 (4 * i)) = some s.core.wstk[i]
  := by ldCD arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_wstk {i : BitVec 64} (hi : i.toNat < s.core.wstk.length) (hm
  : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pWstk + i * 4) = some s.core.wstk[i.toNat]
  := by l4 load_full_wstk hi hm
@[scoped c0_store] theorem store_full_wstk {i : Nat} (v : BitVec 32) (hi : i < s.core.wstk.length)
  (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pWstk + BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with core := { s.core with wstk := s.core.wstk.set i v } } ⋆ R) (storeMem m i32 (c.pWstk +
  BitVec.ofNat 64 (4 * i)) v) := by stCD arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_wstk {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.core.wstk.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pWstk + i * 4) ∧ (FullMem c
  { s with core := { s.core with wstk := s.core.wstk.set i.toNat v } } ⋆ R) (storeMem m i32 (c.pWstk
  + i * 4) v) := by s4 store_full_wstk v hi hm
/-! ### `FullScratchArrays` (`24` arrays) -/
@[scoped c0_load] theorem load_full_walk_vals {i : Nat} (hi : i < s.scratch.walk_vals.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i8 (c.pWalkVals + BitVec.ofNat 64 i) = some
  s.scratch.walk_vals[i] := by ldSB arrGetI8 hi hm
@[scoped c0_load] theorem c0_load_full_walk_vals {i : BitVec 64} (hi : i.toNat <
  s.scratch.walk_vals.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i8 (c.pWalkVals + i) = some
  s.scratch.walk_vals[i.toNat] := by lB load_full_walk_vals hi hm
@[scoped c0_store] theorem store_full_walk_vals {i : Nat} (v : BitVec 8) (hi : i <
  s.scratch.walk_vals.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i8 (c.pWalkVals +
  BitVec.ofNat 64 i) ∧ (FullMem c
  { s with scratch := { s.scratch with walk_vals := s.scratch.walk_vals.set i v } } ⋆ R) (storeMem m
  i8 (c.pWalkVals + BitVec.ofNat 64 i) v) := by stSB arrPutI8 v hi hm s
@[scoped c0_store] theorem c0_store_full_walk_vals {i : BitVec 64} (v : BitVec 8) (hi : i.toNat <
  s.scratch.walk_vals.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i8 (c.pWalkVals + i) ∧ (FullMem
  c { s with scratch := { s.scratch with walk_vals := s.scratch.walk_vals.set i.toNat v } } ⋆ R)
  (storeMem m i8 (c.pWalkVals + i) v) := by sB store_full_walk_vals v hi hm
@[scoped c0_load] theorem load_full_phases {i : Nat} (hi : i < s.scratch.phases.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i8 (c.pPhases + BitVec.ofNat 64 i) = some s.scratch.phases[i]
  := by ldSB arrGetI8 hi hm
@[scoped c0_load] theorem c0_load_full_phases {i : BitVec 64} (hi : i.toNat <
  s.scratch.phases.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i8 (c.pPhases + i) = some
  s.scratch.phases[i.toNat] := by lB load_full_phases hi hm
@[scoped c0_store] theorem store_full_phases {i : Nat} (v : BitVec 8) (hi : i <
  s.scratch.phases.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i8 (c.pPhases + BitVec.ofNat 64 i)
  ∧ (FullMem c { s with scratch := { s.scratch with phases := s.scratch.phases.set i v } } ⋆ R)
  (storeMem m i8 (c.pPhases + BitVec.ofNat 64 i) v) := by stSB arrPutI8 v hi hm s
@[scoped c0_store] theorem c0_store_full_phases {i : BitVec 64} (v : BitVec 8) (hi : i.toNat <
  s.scratch.phases.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i8 (c.pPhases + i) ∧ (FullMem c
  { s with scratch := { s.scratch with phases := s.scratch.phases.set i.toNat v } } ⋆ R) (storeMem m
  i8 (c.pPhases + i) v) := by sB store_full_phases v hi hm
@[scoped c0_load] theorem load_full_phases_target {i : Nat} (hi : i <
  s.scratch.phases_target.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i8 (c.pPhasesTarget +
  BitVec.ofNat 64 i) = some s.scratch.phases_target[i] := by ldSB arrGetI8 hi hm
@[scoped c0_load] theorem c0_load_full_phases_target {i : BitVec 64} (hi : i.toNat <
  s.scratch.phases_target.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i8 (c.pPhasesTarget + i) =
  some s.scratch.phases_target[i.toNat] := by lB load_full_phases_target hi hm
@[scoped c0_store] theorem store_full_phases_target {i : Nat} (v : BitVec 8) (hi : i <
  s.scratch.phases_target.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i8 (c.pPhasesTarget +
  BitVec.ofNat 64 i) ∧ (FullMem c
  { s with scratch := { s.scratch with phases_target := s.scratch.phases_target.set i v } } ⋆ R)
  (storeMem m i8 (c.pPhasesTarget + BitVec.ofNat 64 i) v) := by stSB arrPutI8 v hi hm s
@[scoped c0_store] theorem c0_store_full_phases_target {i : BitVec 64} (v : BitVec 8) (hi : i.toNat
  < s.scratch.phases_target.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i8 (c.pPhasesTarget + i)
  ∧ (FullMem c
  { s with scratch := { s.scratch with phases_target := s.scratch.phases_target.set i.toNat v } } ⋆
  R) (storeMem m i8 (c.pPhasesTarget + i) v) := by sB store_full_phases_target v hi hm
@[scoped c0_load] theorem load_full_phases_best {i : Nat} (hi : i < s.scratch.phases_best.length)
  (hm : (FullMem c s ⋆ R) m) : loadVal m i8 (c.pPhasesBest + BitVec.ofNat 64 i) = some
  s.scratch.phases_best[i] := by ldSB arrGetI8 hi hm
@[scoped c0_load] theorem c0_load_full_phases_best {i : BitVec 64} (hi : i.toNat <
  s.scratch.phases_best.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i8 (c.pPhasesBest + i) = some
  s.scratch.phases_best[i.toNat] := by lB load_full_phases_best hi hm
@[scoped c0_store] theorem store_full_phases_best {i : Nat} (v : BitVec 8) (hi : i <
  s.scratch.phases_best.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i8 (c.pPhasesBest +
  BitVec.ofNat 64 i) ∧ (FullMem c
  { s with scratch := { s.scratch with phases_best := s.scratch.phases_best.set i v } } ⋆ R)
  (storeMem m i8 (c.pPhasesBest + BitVec.ofNat 64 i) v) := by stSB arrPutI8 v hi hm s
@[scoped c0_store] theorem c0_store_full_phases_best {i : BitVec 64} (v : BitVec 8) (hi : i.toNat <
  s.scratch.phases_best.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i8 (c.pPhasesBest + i) ∧
  (FullMem c
  { s with scratch := { s.scratch with phases_best := s.scratch.phases_best.set i.toNat v } } ⋆ R)
  (storeMem m i8 (c.pPhasesBest + i) v) := by sB store_full_phases_best v hi hm
@[scoped c0_load] theorem load_full_walk_best {i : Nat} (hi : i < s.scratch.walk_best.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i8 (c.pWalkBest + BitVec.ofNat 64 i) = some
  s.scratch.walk_best[i] := by ldSB arrGetI8 hi hm
@[scoped c0_load] theorem c0_load_full_walk_best {i : BitVec 64} (hi : i.toNat <
  s.scratch.walk_best.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i8 (c.pWalkBest + i) = some
  s.scratch.walk_best[i.toNat] := by lB load_full_walk_best hi hm
@[scoped c0_store] theorem store_full_walk_best {i : Nat} (v : BitVec 8) (hi : i <
  s.scratch.walk_best.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i8 (c.pWalkBest +
  BitVec.ofNat 64 i) ∧ (FullMem c
  { s with scratch := { s.scratch with walk_best := s.scratch.walk_best.set i v } } ⋆ R) (storeMem m
  i8 (c.pWalkBest + BitVec.ofNat 64 i) v) := by stSB arrPutI8 v hi hm s
@[scoped c0_store] theorem c0_store_full_walk_best {i : BitVec 64} (v : BitVec 8) (hi : i.toNat <
  s.scratch.walk_best.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i8 (c.pWalkBest + i) ∧ (FullMem
  c { s with scratch := { s.scratch with walk_best := s.scratch.walk_best.set i.toNat v } } ⋆ R)
  (storeMem m i8 (c.pWalkBest + i) v) := by sB store_full_walk_best v hi hm
@[scoped c0_load] theorem load_full_heap {i : Nat} (hi : i < s.scratch.heap.length) (hm : (FullMem c
  s ⋆ R) m) : loadVal m i32 (c.pHeap + BitVec.ofNat 64 (4 * i)) = some s.scratch.heap[i]
  := by ldSA arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_heap {i : BitVec 64} (hi : i.toNat < s.scratch.heap.length)
  (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pHeap + i * 4) = some s.scratch.heap[i.toNat]
  := by l4 load_full_heap hi hm
@[scoped c0_store] theorem store_full_heap {i : Nat} (v : BitVec 32) (hi : i <
  s.scratch.heap.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pHeap +
  BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with scratch := { s.scratch with heap := s.scratch.heap.set i v } } ⋆ R) (storeMem m i32
  (c.pHeap + BitVec.ofNat 64 (4 * i)) v) := by stSA arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_heap {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.scratch.heap.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pHeap + i * 4) ∧ (FullMem c
  { s with scratch := { s.scratch with heap := s.scratch.heap.set i.toNat v } } ⋆ R) (storeMem m i32
  (c.pHeap + i * 4) v) := by s4 store_full_heap v hi hm
@[scoped c0_load] theorem load_full_pos {i : Nat} (hi : i < s.scratch.pos.length) (hm : (FullMem c s
  ⋆ R) m) : loadVal m i32 (c.pPos + BitVec.ofNat 64 (4 * i)) = some s.scratch.pos[i]
  := by ldSA arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_pos {i : BitVec 64} (hi : i.toNat < s.scratch.pos.length) (hm
  : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pPos + i * 4) = some s.scratch.pos[i.toNat]
  := by l4 load_full_pos hi hm
@[scoped c0_store] theorem store_full_pos {i : Nat} (v : BitVec 32) (hi : i < s.scratch.pos.length)
  (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pPos + BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with scratch := { s.scratch with pos := s.scratch.pos.set i v } } ⋆ R) (storeMem m i32 (c.pPos
  + BitVec.ofNat 64 (4 * i)) v) := by stSA arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_pos {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.scratch.pos.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pPos + i * 4) ∧ (FullMem c
  { s with scratch := { s.scratch with pos := s.scratch.pos.set i.toNat v } } ⋆ R) (storeMem m i32
  (c.pPos + i * 4) v) := by s4 store_full_pos v hi hm
@[scoped c0_load] theorem load_full_shrink_stk {i : Nat} (hi : i < s.scratch.shrink_stk.length) (hm
  : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pShrinkStk + BitVec.ofNat 64 (4 * i)) = some
  s.scratch.shrink_stk[i] := by ldSA arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_shrink_stk {i : BitVec 64} (hi : i.toNat <
  s.scratch.shrink_stk.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pShrinkStk + i * 4) =
  some s.scratch.shrink_stk[i.toNat] := by l4 load_full_shrink_stk hi hm
@[scoped c0_store] theorem store_full_shrink_stk {i : Nat} (v : BitVec 32) (hi : i <
  s.scratch.shrink_stk.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pShrinkStk +
  BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with scratch := { s.scratch with shrink_stk := s.scratch.shrink_stk.set i v } } ⋆ R) (storeMem
  m i32 (c.pShrinkStk + BitVec.ofNat 64 (4 * i)) v) := by stSA arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_shrink_stk {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.scratch.shrink_stk.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pShrinkStk + i * 4) ∧
  (FullMem c
  { s with scratch := { s.scratch with shrink_stk := s.scratch.shrink_stk.set i.toNat v } } ⋆ R)
  (storeMem m i32 (c.pShrinkStk + i * 4) v) := by s4 store_full_shrink_stk v hi hm
@[scoped c0_load] theorem load_full_q_prev {i : Nat} (hi : i < s.scratch.q_prev.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i32 (c.pQPrev + BitVec.ofNat 64 (4 * i)) = some
  s.scratch.q_prev[i] := by ldSA arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_q_prev {i : BitVec 64} (hi : i.toNat <
  s.scratch.q_prev.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pQPrev + i * 4) = some
  s.scratch.q_prev[i.toNat] := by l4 load_full_q_prev hi hm
@[scoped c0_store] theorem store_full_q_prev {i : Nat} (v : BitVec 32) (hi : i <
  s.scratch.q_prev.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pQPrev +
  BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with scratch := { s.scratch with q_prev := s.scratch.q_prev.set i v } } ⋆ R) (storeMem m i32
  (c.pQPrev + BitVec.ofNat 64 (4 * i)) v) := by stSA arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_q_prev {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.scratch.q_prev.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pQPrev + i * 4) ∧ (FullMem
  c { s with scratch := { s.scratch with q_prev := s.scratch.q_prev.set i.toNat v } } ⋆ R) (storeMem
  m i32 (c.pQPrev + i * 4) v) := by s4 store_full_q_prev v hi hm
@[scoped c0_load] theorem load_full_q_next {i : Nat} (hi : i < s.scratch.q_next.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i32 (c.pQNext + BitVec.ofNat 64 (4 * i)) = some
  s.scratch.q_next[i] := by ldSA arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_q_next {i : BitVec 64} (hi : i.toNat <
  s.scratch.q_next.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pQNext + i * 4) = some
  s.scratch.q_next[i.toNat] := by l4 load_full_q_next hi hm
@[scoped c0_store] theorem store_full_q_next {i : Nat} (v : BitVec 32) (hi : i <
  s.scratch.q_next.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pQNext +
  BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with scratch := { s.scratch with q_next := s.scratch.q_next.set i v } } ⋆ R) (storeMem m i32
  (c.pQNext + BitVec.ofNat 64 (4 * i)) v) := by stSA arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_q_next {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.scratch.q_next.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pQNext + i * 4) ∧ (FullMem
  c { s with scratch := { s.scratch with q_next := s.scratch.q_next.set i.toNat v } } ⋆ R) (storeMem
  m i32 (c.pQNext + i * 4) v) := by s4 store_full_q_next v hi hm
@[scoped c0_load] theorem load_full_q_stamp {i : Nat} (hi : i < s.scratch.q_stamp.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i32 (c.pQStamp + BitVec.ofNat 64 (4 * i)) = some
  s.scratch.q_stamp[i] := by ldSA arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_q_stamp {i : BitVec 64} (hi : i.toNat <
  s.scratch.q_stamp.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pQStamp + i * 4) = some
  s.scratch.q_stamp[i.toNat] := by l4 load_full_q_stamp hi hm
@[scoped c0_store] theorem store_full_q_stamp {i : Nat} (v : BitVec 32) (hi : i <
  s.scratch.q_stamp.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pQStamp +
  BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with scratch := { s.scratch with q_stamp := s.scratch.q_stamp.set i v } } ⋆ R) (storeMem m i32
  (c.pQStamp + BitVec.ofNat 64 (4 * i)) v) := by stSA arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_q_stamp {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.scratch.q_stamp.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pQStamp + i * 4) ∧
  (FullMem c { s with scratch := { s.scratch with q_stamp := s.scratch.q_stamp.set i.toNat v } } ⋆
  R) (storeMem m i32 (c.pQStamp + i * 4) v) := by s4 store_full_q_stamp v hi hm
@[scoped c0_load] theorem load_full_wsort {i : Nat} (hi : i < s.scratch.wsort.length) (hm : (FullMem
  c s ⋆ R) m) : loadVal m i32 (c.pWsort + BitVec.ofNat 64 (4 * i)) = some s.scratch.wsort[i]
  := by ldSW arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_wsort {i : BitVec 64} (hi : i.toNat < s.scratch.wsort.length)
  (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pWsort + i * 4) = some s.scratch.wsort[i.toNat]
  := by l4 load_full_wsort hi hm
@[scoped c0_store] theorem store_full_wsort {i : Nat} (v : BitVec 32) (hi : i <
  s.scratch.wsort.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pWsort +
  BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with scratch := { s.scratch with wsort := s.scratch.wsort.set i v } } ⋆ R) (storeMem m i32
  (c.pWsort + BitVec.ofNat 64 (4 * i)) v) := by stSW arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_wsort {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.scratch.wsort.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pWsort + i * 4) ∧ (FullMem c
  { s with scratch := { s.scratch with wsort := s.scratch.wsort.set i.toNat v } } ⋆ R) (storeMem m
  i32 (c.pWsort + i * 4) v) := by s4 store_full_wsort v hi hm
@[scoped c0_load] theorem load_full_work_stk1 {i : Nat} (hi : i < s.scratch.work_stk1.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i32 (c.pWorkStk1 + BitVec.ofNat 64 (4 * i)) = some
  s.scratch.work_stk1[i] := by ldSW arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_work_stk1 {i : BitVec 64} (hi : i.toNat <
  s.scratch.work_stk1.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pWorkStk1 + i * 4) =
  some s.scratch.work_stk1[i.toNat] := by l4 load_full_work_stk1 hi hm
@[scoped c0_store] theorem store_full_work_stk1 {i : Nat} (v : BitVec 32) (hi : i <
  s.scratch.work_stk1.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pWorkStk1 +
  BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with scratch := { s.scratch with work_stk1 := s.scratch.work_stk1.set i v } } ⋆ R) (storeMem m
  i32 (c.pWorkStk1 + BitVec.ofNat 64 (4 * i)) v) := by stSW arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_work_stk1 {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.scratch.work_stk1.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pWorkStk1 + i * 4) ∧
  (FullMem c { s with scratch := { s.scratch with work_stk1 := s.scratch.work_stk1.set i.toNat v } }
  ⋆ R) (storeMem m i32 (c.pWorkStk1 + i * 4) v) := by s4 store_full_work_stk1 v hi hm
@[scoped c0_load] theorem load_full_work_stk2 {i : Nat} (hi : i < s.scratch.work_stk2.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i32 (c.pWorkStk2 + BitVec.ofNat 64 (4 * i)) = some
  s.scratch.work_stk2[i] := by ldSW arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_work_stk2 {i : BitVec 64} (hi : i.toNat <
  s.scratch.work_stk2.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pWorkStk2 + i * 4) =
  some s.scratch.work_stk2[i.toNat] := by l4 load_full_work_stk2 hi hm
@[scoped c0_store] theorem store_full_work_stk2 {i : Nat} (v : BitVec 32) (hi : i <
  s.scratch.work_stk2.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pWorkStk2 +
  BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set i v } } ⋆ R) (storeMem m
  i32 (c.pWorkStk2 + BitVec.ofNat 64 (4 * i)) v) := by stSW arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_work_stk2 {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.scratch.work_stk2.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pWorkStk2 + i * 4) ∧
  (FullMem c { s with scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set i.toNat v } }
  ⋆ R) (storeMem m i32 (c.pWorkStk2 + i * 4) v) := by s4 store_full_work_stk2 v hi hm
@[scoped c0_load] theorem load_full_tarjan_mark {i : Nat} (hi : i < s.scratch.tarjan_mark.length)
  (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pTarjanMark + BitVec.ofNat 64 (4 * i)) = some
  s.scratch.tarjan_mark[i] := by ldSW arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_tarjan_mark {i : BitVec 64} (hi : i.toNat <
  s.scratch.tarjan_mark.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pTarjanMark + i * 4) =
  some s.scratch.tarjan_mark[i.toNat] := by l4 load_full_tarjan_mark hi hm
@[scoped c0_store] theorem store_full_tarjan_mark {i : Nat} (v : BitVec 32) (hi : i <
  s.scratch.tarjan_mark.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pTarjanMark +
  BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with scratch := { s.scratch with tarjan_mark := s.scratch.tarjan_mark.set i v } } ⋆ R)
  (storeMem m i32 (c.pTarjanMark + BitVec.ofNat 64 (4 * i)) v) := by stSW arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_tarjan_mark {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.scratch.tarjan_mark.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pTarjanMark + i * 4) ∧
  (FullMem c
  { s with scratch := { s.scratch with tarjan_mark := s.scratch.tarjan_mark.set i.toNat v } } ⋆ R)
  (storeMem m i32 (c.pTarjanMark + i * 4) v) := by s4 store_full_tarjan_mark v hi hm
@[scoped c0_load] theorem load_full_tarjan_reach {i : Nat} (hi : i < s.scratch.tarjan_reach.length)
  (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pTarjanReach + BitVec.ofNat 64 (4 * i)) = some
  s.scratch.tarjan_reach[i] := by ldSW arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_tarjan_reach {i : BitVec 64} (hi : i.toNat <
  s.scratch.tarjan_reach.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pTarjanReach + i * 4)
  = some s.scratch.tarjan_reach[i.toNat] := by l4 load_full_tarjan_reach hi hm
@[scoped c0_store] theorem store_full_tarjan_reach {i : Nat} (v : BitVec 32) (hi : i <
  s.scratch.tarjan_reach.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pTarjanReach +
  BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with scratch := { s.scratch with tarjan_reach := s.scratch.tarjan_reach.set i v } } ⋆ R)
  (storeMem m i32 (c.pTarjanReach + BitVec.ofNat 64 (4 * i)) v) := by stSW arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_tarjan_reach {i : BitVec 64} (v : BitVec 32) (hi : i.toNat
  < s.scratch.tarjan_reach.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pTarjanReach + i *
  4) ∧ (FullMem c
  { s with scratch := { s.scratch with tarjan_reach := s.scratch.tarjan_reach.set i.toNat v } } ⋆ R)
  (storeMem m i32 (c.pTarjanReach + i * 4) v) := by s4 store_full_tarjan_reach v hi hm
@[scoped c0_load] theorem load_full_score {i : Nat} (hi : i < s.scratch.score.length) (hm : (FullMem
  c s ⋆ R) m) : loadVal m i64 (c.pScore + BitVec.ofNat 64 (8 * i)) = some s.scratch.score[i]
  := by ldSM arrGetI64 hi hm
@[scoped c0_load] theorem c0_load_full_score {i : BitVec 64} (hi : i.toNat < s.scratch.score.length)
  (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.pScore + i * 8) = some s.scratch.score[i.toNat]
  := by l8 load_full_score hi hm
@[scoped c0_store] theorem store_full_score {i : Nat} (v : BitVec 64) (hi : i <
  s.scratch.score.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i64 (c.pScore +
  BitVec.ofNat 64 (8 * i)) ∧ (FullMem c
  { s with scratch := { s.scratch with score := s.scratch.score.set i v } } ⋆ R) (storeMem m i64
  (c.pScore + BitVec.ofNat 64 (8 * i)) v) := by stSM arrPutI64 v hi hm s
@[scoped c0_store] theorem c0_store_full_score {i : BitVec 64} (v : BitVec 64) (hi : i.toNat <
  s.scratch.score.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i64 (c.pScore + i * 8) ∧ (FullMem c
  { s with scratch := { s.scratch with score := s.scratch.score.set i.toNat v } } ⋆ R) (storeMem m
  i64 (c.pScore + i * 8) v) := by s8 store_full_score v hi hm
@[scoped c0_load] theorem load_full_sim_sig {i : Nat} (hi : i < s.scratch.sim_sig.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i64 (c.pSimSig + BitVec.ofNat 64 (8 * i)) = some
  s.scratch.sim_sig[i] := by ldSM arrGetI64 hi hm
@[scoped c0_load] theorem c0_load_full_sim_sig {i : BitVec 64} (hi : i.toNat <
  s.scratch.sim_sig.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i64 (c.pSimSig + i * 8) = some
  s.scratch.sim_sig[i.toNat] := by l8 load_full_sim_sig hi hm
@[scoped c0_store] theorem store_full_sim_sig {i : Nat} (v : BitVec 64) (hi : i <
  s.scratch.sim_sig.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i64 (c.pSimSig +
  BitVec.ofNat 64 (8 * i)) ∧ (FullMem c
  { s with scratch := { s.scratch with sim_sig := s.scratch.sim_sig.set i v } } ⋆ R) (storeMem m i64
  (c.pSimSig + BitVec.ofNat 64 (8 * i)) v) := by stSM arrPutI64 v hi hm s
@[scoped c0_store] theorem c0_store_full_sim_sig {i : BitVec 64} (v : BitVec 64) (hi : i.toNat <
  s.scratch.sim_sig.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i64 (c.pSimSig + i * 8) ∧
  (FullMem c { s with scratch := { s.scratch with sim_sig := s.scratch.sim_sig.set i.toNat v } } ⋆
  R) (storeMem m i64 (c.pSimSig + i * 8) v) := by s8 store_full_sim_sig v hi hm
@[scoped c0_load] theorem load_full_glue_used {i : Nat} (hi : i < s.scratch.glue_used.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i32 (c.pGlueUsed + BitVec.ofNat 64 (4 * i)) = some
  s.scratch.glue_used[i] := by ldSM arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_glue_used {i : BitVec 64} (hi : i.toNat <
  s.scratch.glue_used.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pGlueUsed + i * 4) =
  some s.scratch.glue_used[i.toNat] := by l4 load_full_glue_used hi hm
@[scoped c0_store] theorem store_full_glue_used {i : Nat} (v : BitVec 32) (hi : i <
  s.scratch.glue_used.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pGlueUsed +
  BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with scratch := { s.scratch with glue_used := s.scratch.glue_used.set i v } } ⋆ R) (storeMem m
  i32 (c.pGlueUsed + BitVec.ofNat 64 (4 * i)) v) := by stSM arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_glue_used {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.scratch.glue_used.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pGlueUsed + i * 4) ∧
  (FullMem c { s with scratch := { s.scratch with glue_used := s.scratch.glue_used.set i.toNat v } }
  ⋆ R) (storeMem m i32 (c.pGlueUsed + i * 4) v) := by s4 store_full_glue_used v hi hm
@[scoped c0_load] theorem load_full_last_learned {i : Nat} (hi : i < s.scratch.last_learned.length)
  (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pLastLearned + BitVec.ofNat 64 (4 * i)) = some
  s.scratch.last_learned[i] := by ldSM arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_last_learned {i : BitVec 64} (hi : i.toNat <
  s.scratch.last_learned.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pLastLearned + i * 4)
  = some s.scratch.last_learned[i.toNat] := by l4 load_full_last_learned hi hm
@[scoped c0_store] theorem store_full_last_learned {i : Nat} (v : BitVec 32) (hi : i <
  s.scratch.last_learned.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pLastLearned +
  BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with scratch := { s.scratch with last_learned := s.scratch.last_learned.set i v } } ⋆ R)
  (storeMem m i32 (c.pLastLearned + BitVec.ofNat 64 (4 * i)) v) := by stSM arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_last_learned {i : BitVec 64} (v : BitVec 32) (hi : i.toNat
  < s.scratch.last_learned.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pLastLearned + i *
  4) ∧ (FullMem c
  { s with scratch := { s.scratch with last_learned := s.scratch.last_learned.set i.toNat v } } ⋆ R)
  (storeMem m i32 (c.pLastLearned + i * 4) v) := by s4 store_full_last_learned v hi hm
@[scoped c0_load] theorem load_full_delayed {i : Nat} (hi : i < s.scratch.delayed.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i32 (c.pDelayed + BitVec.ofNat 64 (4 * i)) = some
  s.scratch.delayed[i] := by ldSD arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_delayed {i : BitVec 64} (hi : i.toNat <
  s.scratch.delayed.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pDelayed + i * 4) = some
  s.scratch.delayed[i.toNat] := by l4 load_full_delayed hi hm
@[scoped c0_store] theorem store_full_delayed {i : Nat} (v : BitVec 32) (hi : i <
  s.scratch.delayed.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pDelayed +
  BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with scratch := { s.scratch with delayed := s.scratch.delayed.set i v } } ⋆ R) (storeMem m i32
  (c.pDelayed + BitVec.ofNat 64 (4 * i)) v) := by stSD arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_delayed {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.scratch.delayed.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pDelayed + i * 4) ∧
  (FullMem c { s with scratch := { s.scratch with delayed := s.scratch.delayed.set i.toNat v } } ⋆
  R) (storeMem m i32 (c.pDelayed + i * 4) v) := by s4 store_full_delayed v hi hm
@[scoped c0_load] theorem load_full_red_refs {i : Nat} (hi : i < s.scratch.red_refs.length) (hm :
  (FullMem c s ⋆ R) m) : loadVal m i32 (c.pRedRefs + BitVec.ofNat 64 (4 * i)) = some
  s.scratch.red_refs[i] := by ldSD arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_red_refs {i : BitVec 64} (hi : i.toNat <
  s.scratch.red_refs.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pRedRefs + i * 4) = some
  s.scratch.red_refs[i.toNat] := by l4 load_full_red_refs hi hm
@[scoped c0_store] theorem store_full_red_refs {i : Nat} (v : BitVec 32) (hi : i <
  s.scratch.red_refs.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pRedRefs +
  BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with scratch := { s.scratch with red_refs := s.scratch.red_refs.set i v } } ⋆ R) (storeMem m
  i32 (c.pRedRefs + BitVec.ofNat 64 (4 * i)) v) := by stSD arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_red_refs {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.scratch.red_refs.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pRedRefs + i * 4) ∧
  (FullMem c { s with scratch := { s.scratch with red_refs := s.scratch.red_refs.set i.toNat v } } ⋆
  R) (storeMem m i32 (c.pRedRefs + i * 4) v) := by s4 store_full_red_refs v hi hm
@[scoped c0_load] theorem load_full_extend_stk {i : Nat} (hi : i < s.scratch.extend_stk.length) (hm
  : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pExtendStk + BitVec.ofNat 64 (4 * i)) = some
  s.scratch.extend_stk[i] := by ldSD arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_extend_stk {i : BitVec 64} (hi : i.toNat <
  s.scratch.extend_stk.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pExtendStk + i * 4) =
  some s.scratch.extend_stk[i.toNat] := by l4 load_full_extend_stk hi hm
@[scoped c0_store] theorem store_full_extend_stk {i : Nat} (v : BitVec 32) (hi : i <
  s.scratch.extend_stk.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pExtendStk +
  BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with scratch := { s.scratch with extend_stk := s.scratch.extend_stk.set i v } } ⋆ R) (storeMem
  m i32 (c.pExtendStk + BitVec.ofNat 64 (4 * i)) v) := by stSD arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_extend_stk {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.scratch.extend_stk.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pExtendStk + i * 4) ∧
  (FullMem c
  { s with scratch := { s.scratch with extend_stk := s.scratch.extend_stk.set i.toNat v } } ⋆ R)
  (storeMem m i32 (c.pExtendStk + i * 4) v) := by s4 store_full_extend_stk v hi hm
@[scoped c0_load] theorem load_full_scratch_buf {i : Nat} (hi : i < s.scratch.scratch_buf.length)
  (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pScratchBuf + BitVec.ofNat 64 (4 * i)) = some
  s.scratch.scratch_buf[i] := by ldSD arrGetI32 hi hm
@[scoped c0_load] theorem c0_load_full_scratch_buf {i : BitVec 64} (hi : i.toNat <
  s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pScratchBuf + i * 4) =
  some s.scratch.scratch_buf[i.toNat] := by l4 load_full_scratch_buf hi hm
@[scoped c0_store] theorem store_full_scratch_buf {i : Nat} (v : BitVec 32) (hi : i <
  s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pScratchBuf +
  BitVec.ofNat 64 (4 * i)) ∧ (FullMem c
  { s with scratch := { s.scratch with scratch_buf := s.scratch.scratch_buf.set i v } } ⋆ R)
  (storeMem m i32 (c.pScratchBuf + BitVec.ofNat 64 (4 * i)) v) := by stSD arrPutI32 v hi hm s
@[scoped c0_store] theorem c0_store_full_scratch_buf {i : BitVec 64} (v : BitVec 32) (hi : i.toNat <
  s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pScratchBuf + i * 4) ∧
  (FullMem c
  { s with scratch := { s.scratch with scratch_buf := s.scratch.scratch_buf.set i.toNat v } } ⋆ R)
  (storeMem m i32 (c.pScratchBuf + i * 4) v) := by s4 store_full_scratch_buf v hi hm
/-! ### Key index-0 base-address shortcuts (`heap[0]`, `wstk[0]`, `wsort[0]`, `min_stk[0]`) -/
@[scoped c0_load] theorem load_full_heap0 (hi : 0 < s.scratch.heap.length)
  (hm : (FullMem c s ⋆ R) m) : loadVal m i32 c.pHeap = some s.scratch.heap[0] :=
  by simpa using load_full_heap (i := 0) hi hm
@[scoped c0_store] theorem store_full_heap0 (v : BitVec 32) (hi : 0 < s.scratch.heap.length)
  (hm : (FullMem c s ⋆ R) m) : storeOk m i32 c.pHeap ∧ (FullMem c
  { s with scratch := { s.scratch with heap := s.scratch.heap.set 0 v } } ⋆ R)
  (storeMem m i32 c.pHeap v) := by simpa using store_full_heap (i := 0) v hi hm
@[scoped c0_load] theorem load_full_wstk0 (hi : 0 < s.core.wstk.length)
  (hm : (FullMem c s ⋆ R) m) : loadVal m i32 c.pWstk = some s.core.wstk[0] :=
  by simpa using load_full_wstk (i := 0) hi hm
@[scoped c0_store] theorem store_full_wstk0 (v : BitVec 32) (hi : 0 < s.core.wstk.length)
  (hm : (FullMem c s ⋆ R) m) : storeOk m i32 c.pWstk ∧ (FullMem c
  { s with core := { s.core with wstk := s.core.wstk.set 0 v } } ⋆ R)
  (storeMem m i32 c.pWstk v) := by simpa using store_full_wstk (i := 0) v hi hm
@[scoped c0_load] theorem load_full_wsort0 (hi : 0 < s.scratch.wsort.length)
  (hm : (FullMem c s ⋆ R) m) : loadVal m i32 c.pWsort = some s.scratch.wsort[0] :=
  by simpa using load_full_wsort (i := 0) hi hm
@[scoped c0_store] theorem store_full_wsort0 (v : BitVec 32) (hi : 0 < s.scratch.wsort.length)
  (hm : (FullMem c s ⋆ R) m) : storeOk m i32 c.pWsort ∧ (FullMem c
  { s with scratch := { s.scratch with wsort := s.scratch.wsort.set 0 v } } ⋆ R)
  (storeMem m i32 c.pWsort v) := by simpa using store_full_wsort (i := 0) v hi hm
@[scoped c0_load] theorem load_full_min_stk0 (hi : 0 < s.core.min_stk.length)
  (hm : (FullMem c s ⋆ R) m) : loadVal m i32 c.pMinStk = some s.core.min_stk[0] :=
  by simpa using load_full_min_stk (i := 0) hi hm
@[scoped c0_store] theorem store_full_min_stk0 (v : BitVec 32) (hi : 0 < s.core.min_stk.length)
  (hm : (FullMem c s ⋆ R) m) : storeOk m i32 c.pMinStk ∧ (FullMem c
  { s with core := { s.core with min_stk := s.core.min_stk.set 0 v } } ⋆ R)
  (storeMem m i32 c.pMinStk v) := by simpa using store_full_min_stk (i := 0) v hi hm
end HeaderAccess
end FullArenaTactics
end LeanQbe.T.Examples.Kissat.Proof.Spec
