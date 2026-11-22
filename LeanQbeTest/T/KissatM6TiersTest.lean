module

public import LeanQbe.T.Examples.Kissat.FullM6TiersProof
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM6TiersProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal
import Kraken.Mem
import Kraken.Separation

/-!
# Verification, Extended-`delayed` Concrete `Mem 64` Non-Vacuity & Axiom Audit (`KissatM6TiersTest`)

1. Executable `#guard` checks on `FullM6Hdr` / `M6HdrExt` layout constants, `m6Tiers_fns`
   (`35` fns), `m6TiersExterns` (`18` externs), `m6TiersSpecTable` (`53` rows, `noExit = true`),
   `m6TiersModule.checkAcyclic`, `m6TiersModule.exits`, `PrintCpp.ppTModule`, `PrintQbe.module`,
   and `Fn.legal` legality across `.aarch64`, `.scalar64`, `.x64AVX512`, and `.x64AVX2`.
2. Concrete `Mem 64` UNSAT-only non-vacuity (`XPost := fun _ _ _ _ => False`, zero SAT/model
   proofs) under closed `m6TiersEnv`:
   - Legacy `delayed_cap = 0` fallback on `nvOneLitMem` (`full_m6_ext_ready` returns `false` and
     preserves `s' = nvOneLitState`).
   - Extended `delayed_cap = 200` (`nvM6ExtCfg` / `nvM6ExtState` / `nvM6ExtMem`, `4156` bytes)
     with nonzero `w2b` sentinel words `del[0..15] = [101..116]` proving BOTH `nvOneLitF0.Unsat` AND
     `∀ k < 16, sc'.delayed[k]? = nvM6ExtDel[k]?` across `full_m6_ext_ready`, mode-split tiers,
     `used[2].glue[128]`, `delay[4]` backoff, separate watermarks, `full_switch_mode_m6`,
     `full_rephase_m6`, `full_reduce_m6`, `full_analyze_rsn_m6`, `full_analyze_m6`, `full_probe`,
     and `full_eliminate`.
3. Single-line `#print axioms` audit (`< 115c`, `std3`-clean) across all exported `_wf`, `_wp`,
   `ModuleOk`, `noExit`, and concrete NV theorems.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatM6TiersTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open scoped LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full hiding
  full_probe_body full_eliminate_body full_probe_wf full_eliminate_wf
open LeanQbe.T.Examples.Kissat.FullM6Tiers
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Sanity Checks -/

#guard fullM6HdrBaseWords == 144
#guard fullM6HdrBaseBytes == 1152
#guard fullM6ExtWords == 288
#guard fullM6ExtBytes == 2304
#guard fullM6HdrTotalWords == 432
#guard fullM6HdrTotalBytes == 3456
#guard fullM6W2bReservedBytes == 48
#guard fullM6DelExtStartU32 == 16
#guard fullM6DelTotalU32s == 566
#guard fullM6DelTotalU32s ≤ 3 * fullM6DelMinCap
#guard m6ExtOffW2bReserved + fullM6W2bReservedBytes == m6ExtOffTier1
#guard m6ExtOffUsed1 + 1024 == fullM6ExtBytes
#guard m6Tiers_fns.length == 35
#guard m6TiersExterns.length == 18
#guard m6TiersModule.checkAcyclic == true
#guard m6TiersModule.exits.isEmpty == true
#guard m6TiersSpecTable.length == 53
#guard m6TiersSpecTable.all (·.noExit) == true
#guard m6Tiers_fns.map Fn.name == (m6TiersSpecTable.take 35).map SpecEntry.name
#guard (PrintCpp.ppTModule m6TiersModule).isOk == true
#guard (PrintQbe.module m6TiersModule).isOk == true
#guard m6Tiers_fns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard m6Tiers_fns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard m6Tiers_fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard m6Tiers_fns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

/-! ## 2. Concrete `Mem 64` Fixtures (`nvOneLit` Legacy + `nvM6Ext` Extended `delayed_cap=200`) -/

private theorem nvOneLitF0_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [nvOneLitF0, cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [nvOneLitF0, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

private theorem nvOneLitMem_sep : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
  rw [sep_emp]; exact nvOneLitMem_ok

/-- Nonzero `w2b` sentinel words `del[0..15] = [101..116]` plus `584` zero `u32` words for
`M6HdrExt` (`600 = 3 * 200`). -/
def nvM6ExtDel : List (BitVec 32) :=
  (List.range 16).map (fun k => BitVec.ofNat 32 (k + 101)) ++ List.replicate 584 0#32

private theorem nvM6ExtDel_len : nvM6ExtDel.length = 600 := by
  unfold nvM6ExtDel
  rw [List.length_append, List.length_map, List.length_range, List.length_replicate]

/-- Concrete `FullCfg` with `delayed_cap = 200` (`avail = 4156`, enabling `M6HdrExt`). -/
def nvM6ExtCfg : FullCfg where
  hdr := 0x1000#64
  avail := 4156
  mv := 1
  max_vars := 1
  bva_cap := 0
  nc := 2
  arena_cap := 0
  wcap := 1
  delayed_cap := 200
  red_cap := 0
  extend_cap := 0
  scratch_cap := 0
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

/-- Concrete `FullScratch` extending `nvOneLitScratch` with `nvM6ExtDel`. -/
def nvM6ExtScratch : FullScratch :=
  { nvOneLitScratch with delayed := nvM6ExtDel }

/-- Concrete level-0 `FullState` on `nvM6ExtCfg` carrying `nvOneLitState.core` and `nvM6ExtDel`. -/
def nvM6ExtState : FullState where
  core := nvOneLitState.core
  scratch := nvM6ExtScratch

def nvExtBlockHdr : List UInt8 :=
  bytes64 [1#64, 2#64, 0#64, 0#64] ++ bytes64 (hdrTailWords nvM6ExtCfg nvM6ExtState)

def nvExtBlockTail : List UInt8 :=
  bytesOf (t := i32) nvM6ExtState.core.min_stk ++
  bytesOf (t := i32) nvM6ExtScratch.glue_used ++
  bytesOf (t := i32) nvM6ExtScratch.last_learned ++
  bytesOf (t := i32) nvM6ExtState.core.arena ++
  bytesOf (t := i32) nvM6ExtState.core.wstk ++
  bytesOf (t := i32) nvM6ExtDel ++
  bytesOf (t := i32) nvM6ExtScratch.red_refs ++
  bytesOf (t := i32) nvM6ExtScratch.extend_stk ++
  bytesOf (t := i32) nvM6ExtScratch.scratch_buf ++
  List.replicate 0 0

/-- Concrete `4156`-byte arena image encoding `nvM6ExtCfg` and `nvM6ExtState`. -/
def nvM6ExtBytes : List UInt8 :=
  nvExtBlockHdr ++ nvBlockBytes ++ nvBlockU32A ++ nvBlockU32B ++
  nvBlockU32C ++ nvBlockWvec ++ nvExtBlockTail

/-- Concrete `Mem 64` heap for `nvM6ExtCfg` at `0x1000`. -/
def nvM6ExtMem : Mem 64 := nvM6ExtBytes.At nvM6ExtCfg.hdr

private theorem nvM6Ext_lengths : nvM6ExtState.LengthsOk nvM6ExtCfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl,
    by rw [show nvM6ExtState.scratch.delayed = nvM6ExtDel from rfl, nvM6ExtDel_len]; rfl,
    rfl, rfl, rfl⟩⟩

private theorem nvM6Ext_entails_0 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) := by
  rw [CNF.entails_clause_def]; intro α hα
  exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))

private theorem nvM6Ext_entails_11 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [1, 1]) := by
  rw [CNF.entails_clause_def]; intro α hα
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h1 ⊢
  obtain ⟨lit, hm, heq⟩ := h1
  refine ⟨lit, ?_, heq⟩
  rw [mem_cnfClause_iff] at hm ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
  exact Or.inl hm

private theorem nvM6Ext_witness :
    FullWitnessInv nvM6ExtCfg nvOneLitF0 [[0], [1]] nvM6ExtState.core := by
  have hrefs : fullArenaClauseRefsCore nvM6ExtState.core = [] := rfl
  have hcv : nvM6ExtState.core.cur_vars = 1 := rfl
  have hte : nvM6ExtState.core.trail_end = 1 := rfl
  have hcl : nvM6ExtState.core.cur_level = 0 := rfl
  have hdm : nvM6ExtState.core.dense_mode = 0#64 := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvM6ExtState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvM6ExtState, nvOneLitState] at hp)
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvM6ExtState, nvOneLitState] at hp)
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
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
          simp [nvM6ExtState, nvOneLitState]
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
      levels_inhabited := fun L _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact nvM6Ext_entails_0
      trail_pos_inv := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      level0_rsn_none := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      frame_trail_lt := fun L hL => by rw [hcl] at hL; obtain rfl : L = 0 := (by omega); decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega)
        obtain rfl : L2 = 0 := (by omega); exact Nat.le_refl _
      frame_trail_before_lt := fun L _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun L _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne }

private theorem nvM6Ext_coreInv : FullCoreInv nvM6ExtCfg nvOneLitF0 nvM6ExtState :=
  ⟨nvM6Ext_lengths, [[0], [1]], nvM6Ext_witness⟩

private theorem nvM6Ext_marks : FullLitMarksClear nvM6ExtCfg nvM6ExtState := by
  refine ⟨fun v hv => ?_, fun l hl => ?_⟩
  · have hmv : nvM6ExtCfg.max_vars = 1 := rfl
    rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
  · have hmv : nvM6ExtCfg.max_vars = 1 := rfl
    rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl

private theorem nvM6Ext_nodup : FullArenaVarsNodup nvM6ExtState := fun r hr => by
  have href : fullArenaClauseRefs nvM6ExtState = [] := rfl
  simp [href] at hr

private theorem nvM6Ext_extScr : FullExtScratchOk nvM6ExtCfg nvM6ExtState :=
  ⟨FullLastLearnedWf.of_cleared fun i hi => by
    simp only [nvM6ExtState, nvM6ExtScratch, nvOneLitScratch, List.getElem?_replicate,
      show i < 16 by omega, ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩

private theorem nvM6Ext_sparseW :
    FullSparseInvW nvM6ExtCfg nvOneLitF0 [[0], [1]] nvM6ExtState :=
  ⟨nvM6Ext_lengths, nvM6Ext_witness, nvM6Ext_marks, nvM6Ext_nodup, nvM6Ext_extScr, rfl⟩

private theorem nvM6Ext_sparse : FullSparseInv nvM6ExtCfg nvOneLitF0 nvM6ExtState :=
  nvM6Ext_sparseW.toSparse

private theorem nvM6Ext_conflW : FullConflictOkW [[0], [1]] nvM6ExtState :=
  Or.inl ⟨rfl, by decide, by decide, rfl, rfl, nvM6Ext_entails_11⟩

private theorem nvM6Ext_marksCov : FullAnaMarksCov nvM6ExtCfg nvM6ExtState :=
  ⟨Nat.zero_le _, by decide,
    fun _ hk => absurd hk (Nat.not_lt_zero _),
    fun v hv hnz => by
      have hmv : nvM6ExtCfg.max_vars = 1 := rfl
      rw [hmv] at hv; obtain rfl : v = 0 := (by omega); exact absurd rfl hnz⟩

private theorem nvM6ExtMem_ok : FullMem nvM6ExtCfg nvM6ExtState nvM6ExtMem := by
  let c := nvM6ExtCfg; let s := nvM6ExtState
  have hvb : valsBytes c.max_vars - 2 * c.max_vars = 6 := by decide
  have hmb : markBytes c.max_vars - c.max_vars = 7 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 0 := by decide
  have hmv1 : BitVec.ofNat 64 c.max_vars = 1#64 := rfl
  have hmv2 : BitVec.ofNat 64 (2 * c.max_vars) = 2#64 := rfl
  have hmv4 : BitVec.ofNat 64 (4 * c.max_vars) = 4#64 := rfl
  have hmv8 : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 8#64 := rfl
  have hHdr : nvExtBlockHdr.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (hdrTailWords c s))
        (nvExtBlockHdr.At c.hdr) :=
    nv_join_pair
      (nv_arr64_p (a := c.hdr) (xs := [1#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
      (nv_arr64_p (a := c.hdr + 32) (xs := hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide))
      (by decide) (by decide)
  have hBytes : nvBlockBytes.length = 64 ∧
      (FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ c.padBytes)
        (nvBlockBytes.At c.pVals) := by
    have h1 := nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 2 6 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 2 6 rfl
      (by decide)
    have h3 := nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 2 6 rfl
      (by decide)
    have h4 := nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 1 7 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 1 7 rfl
      (by decide)
    have h6 := nv_arr_pad_p (t := i8) (a := c.pPhasesTarget) (xs := s.scratch.phases_target) 1 7
      rfl (by decide)
    have h7 := nv_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best) 1 7 rfl
      (by decide)
    have h8 := nv_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best) 1 7 rfl
      (by decide)
    let pB1 : Mem 64 → Prop :=
      region (c.pVals + 2#64) 6 ⋆ region (c.pWalkVals + 2#64) 6 ⋆
      region (c.pLitMark + 2#64) 6 ⋆ region (c.pMark + 1#64) 7
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_sep_reorg (nv_join_pair h123 h4 (by decide) (by decide))
      (Q := (FullCoreByteArrs c s.core ⋆ array (t := i8) c.pWalkVals s.scratch.walk_vals) ⋆ pB1)
      fun _ hm => nv_zip4 hm
    have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
    have hall := nv_join_pair h1234567 h8 (by decide) (by decide)
    exact nv_sep_reorg hall fun _ hm => by
      have hfin := nv_zip4_tail hm
      unfold FullScrByteArrs FullCfg.padBytes
      rw [hvb, hmb, hmv2, hmv1]
      simpa only [pB1, sep_assoc] using hfin
  have hU32A : nvBlockU32A.length = 40 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        (nvBlockU32A.At c.pFlags) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 4 4 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 4 4 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 4 4 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 4 4 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 4 4 rfl
      (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu4, hmv4]; exact sep_ac hm
  have hU32B : nvBlockU32B.length = 40 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
        (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
         array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        (nvBlockU32B.At c.pTmp) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 4 4 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 4 4 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 4 4 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 4 4 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk) 4 4 rfl
      (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu4, hmv4]; exact sep_ac hm
  have hU32C : nvBlockU32C.length = 40 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        (nvBlockU32C.At c.pQPrev) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 4 4 rfl
      (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 4 4 rfl
      (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 4 4 rfl
      (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 8 0 rfl
      (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 8 0 rfl
      (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu4, hu8, hmv4, hmv8]; exact sep_ac hm
  have hWvec : nvBlockWvec.length = 80 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        (nvBlockWvec.At c.pWvec) := by
    have h1 := nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 16 rfl (by decide)
    have h2 := nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 8 rfl (by decide)
    have h3 := nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 8 rfl (by decide)
    have h4 := nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 8 rfl
      (by decide)
    have h5 := nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 8 rfl
      (by decide)
    have h6 := nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 8 rfl
      (by decide)
    have h7 := nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 8 rfl
      (by decide)
    have h8 := nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 8 rfl (by decide)
    have h9 := nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 8 rfl (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := nv_join_pair h1234567 h8 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail : nvExtBlockTail.length = 2740 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        (nvExtBlockTail.At c.pMinStk) := by
    have h1 := nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 16 rfl (by decide)
    have h2 := nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256 rfl
      (by decide)
    have h3 := nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned) 64 rfl
      (by decide)
    have h4 := nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 0 rfl (by decide)
    have h5 := nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 4 rfl (by decide)
    have h6 := nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 2400
      (by rw [show s.scratch.delayed = nvM6ExtDel from rfl, nvM6ExtDel_len]; rfl) (by decide)
    have h7 := nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl (by decide)
    have h8 := nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl
      (by decide)
    have h9 := nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 0 rfl
      (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 0).At c.pSlack) :=
      ⟨rfl, ⟨List.replicate 0 0, by decide, rfl⟩⟩
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := nv_join_pair h1234567 h8 (by decide) (by decide)
    have h123456789 := nv_join_pair h12345678 h9 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h123456789 h10 (by decide) (by decide)) fun _ hm => by
      unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := nv_join_pair hHdr hBytes (by decide) (by decide)
  have h02 := nv_join_pair h01 hU32A (by decide) (by decide)
  have h03 := nv_join_pair h02 hU32B (by decide) (by decide)
  have h04 := nv_join_pair h03 hU32C (by decide) (by decide)
  have h05 := nv_join_pair h04 hWvec (by decide) (by decide)
  exact (nv_sep_reorg (nv_join_pair h05 hTail (by decide) (by decide)) fun _ hm => by
    unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
      FullScrMetaArrs FullCfg.pad
    exact sep_ac hm).2

private theorem nvM6ExtMem_sep : (FullMem nvM6ExtCfg nvM6ExtState ⋆ emp) nvM6ExtMem := by
  rw [sep_emp]; exact nvM6ExtMem_ok

/-! ## 3. Concrete `Mem 64` Non-Vacuity Witnesses (`XPost := False`, `m6TiersEnv`) -/

/-- Exact concrete return value (`3456#64`) for `full_m6_hdr_sizeof` under `m6TiersEnv`. -/
theorem full_m6_hdr_sizeof_nv (m : Mem 64) :
    Func.wp m6TiersEnv full_m6_hdr_sizeof_body () m (fun (r, ()) m' => r = 3456#64 ∧ m' = m)
      (fun _ _ _ _ => False) :=
  m6Tiers_tableImpl.1.2 () m _ _ ⟨rfl, rfl⟩

/-- Exact concrete return value (`2304#64`) for `full_m6_ext_sizeof` under `m6TiersEnv`. -/
theorem full_m6_ext_sizeof_nv (m : Mem 64) :
    Func.wp m6TiersEnv full_m6_ext_sizeof_body () m (fun (r, ()) m' => r = 2304#64 ∧ m' = m)
      (fun _ _ _ _ => False) :=
  m6Tiers_tableImpl.2.1.2 () m _ _ ⟨rfl, rfl⟩

/-- Legacy `delayed_cap = 0` fallback NV on `nvOneLitMem`: `full_m6_ext_ready` returns `false`,
leaves `nvOneLitState` unchanged, and certifies `nvOneLitF0.Unsat`. -/
theorem full_m6_ext_ready_legacy_nv :
    Func.wp m6TiersEnv full_m6_ext_ready_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' => r = false ∧ FullMem nvOneLitCfg nvOneLitState m' ∧ nvOneLitF0.Unsat)
      (fun _ _ _ _ => False) :=
  m6Tiers_tableImpl.2.2.2.2.1.2 (nvOneLitCfg.hdr, ()) nvOneLitMem _ _
    ⟨nvOneLitCfg, nvOneLitState, emp, rfl, nvOneLit_lengths, nvOneLitMem_sep,
      fun (r, ()) s' m' _ _ ⟨_, hiff, _, hfl⟩ hm' => by
        have hrf : r = false := by
          cases r with | false => rfl | true => exact absurd (hiff.mp rfl) (by decide)
        obtain rfl := hfl hrf
        rw [sep_emp] at hm'
        exact ⟨hrf, hm', nvOneLitF0_unsat⟩⟩

/-- Extended `delayed_cap = 200` NV on `nvM6ExtMem`: `full_m6_ext_ready` returns `true`, writes
`fullM6Magic`, and preserves `w2b` sentinel words `del[0..15] = [101..116]`. -/
theorem full_m6_ext_ready_ext_nv :
    Func.wp m6TiersEnv full_m6_ext_ready_body (nvM6ExtCfg.hdr, ()) nvM6ExtMem
      (fun (r, ()) m' => ∃ s',
        r = true ∧ m6Get64Val s'.scratch.delayed m6DelMagicIdx = fullM6Magic ∧
        FullM6DelayedW2bPres nvM6ExtState s' ∧ s'.LengthsOk nvM6ExtCfg ∧
        FullMem nvM6ExtCfg s' m' ∧ nvOneLitF0.Unsat)
      (fun _ _ _ _ => False) :=
  m6Tiers_tableImpl.2.2.2.2.1.2 (nvM6ExtCfg.hdr, ()) nvM6ExtMem _ _
    ⟨nvM6ExtCfg, nvM6ExtState, emp, rfl, nvM6Ext_lengths, nvM6ExtMem_sep,
      fun (r, ()) s' m' _ hln ⟨hpr, hiff, hmg, _⟩ hm' => by
        have hrt : r = true := hiff.mpr (by decide)
        rw [sep_emp] at hm'
        exact ⟨s', hrt, hmg hrt, hpr.2, hln, hm', nvOneLitF0_unsat⟩⟩

/-- Legacy `delayed_cap = 0` NV for `full_recompute_tiers_m6` on `nvOneLitMem`. -/
theorem full_recompute_tiers_legacy_nv :
    Func.wp m6TiersEnv full_recompute_tiers_m6_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s',
        PreservesCoreSlice FullState.core nvOneLitState s' ∧
        s'.LengthsOk nvOneLitCfg ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  let t5 := m6Tiers_tableImpl.2.2.2.2.2
  exact t5.2.2.2.2.1.2 (nvOneLitCfg.hdr, ()) nvOneLitMem _ _
    ⟨nvOneLitCfg, nvOneLitState, emp, rfl, nvOneLit_lengths, nvOneLitMem_sep,
      fun () s' m' hco hln _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hco, hln, nvOneLitF0_unsat, hm'⟩⟩

/-- Extended `delayed_cap = 200` NV for `full_recompute_tiers_m6` preserving `w2b` `del[0..15]`. -/
theorem full_recompute_tiers_ext_nv :
    Func.wp m6TiersEnv full_recompute_tiers_m6_body (nvM6ExtCfg.hdr, ()) nvM6ExtMem
      (fun () m' => ∃ s',
        PreservesCoreSlice FullState.core nvM6ExtState s' ∧
        FullM6DelayedW2bPres nvM6ExtState s' ∧ s'.LengthsOk nvM6ExtCfg ∧
        nvOneLitF0.Unsat ∧ FullMem nvM6ExtCfg s' m')
      (fun _ _ _ _ => False) := by
  let t5 := m6Tiers_tableImpl.2.2.2.2.2
  exact t5.2.2.2.2.1.2 (nvM6ExtCfg.hdr, ()) nvM6ExtMem _ _
    ⟨nvM6ExtCfg, nvM6ExtState, emp, rfl, nvM6Ext_lengths, nvM6ExtMem_sep,
      fun () s' m' hco hln hpr hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hco, hpr.2, hln, nvOneLitF0_unsat, hm'⟩⟩

/-- Extended NV for `full_m6_update_tier_limits` (`w2b` prefix & `Mem 64` preservation). -/
theorem full_m6_update_tier_limits_ext_nv :
    Func.wp m6TiersEnv full_m6_update_tier_limits_body (nvM6ExtCfg.hdr, ()) nvM6ExtMem
      (fun () m' => ∃ s',
        FullM6DelayedW2bPres nvM6ExtState s' ∧ s'.LengthsOk nvM6ExtCfg ∧
        nvOneLitF0.Unsat ∧ FullMem nvM6ExtCfg s' m')
      (fun _ _ _ _ => False) := by
  let t10 := m6Tiers_tableImpl.2.2.2.2.2.2.2.2.2.2
  exact t10.1.2 (nvM6ExtCfg.hdr, ()) nvM6ExtMem _ _
    ⟨nvM6ExtCfg, nvM6ExtState, emp, rfl, nvM6Ext_lengths, nvM6ExtMem_sep,
      fun () s' m' _ hln hpr hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hpr.2, hln, nvOneLitF0_unsat, hm'⟩⟩

/-- Extended NV for `full_m6_record_used` (`used[2].glue[128]` histogram update). -/
theorem full_m6_record_used_ext_nv :
    Func.wp m6TiersEnv full_m6_record_used_body (nvM6ExtCfg.hdr, 5#64, ()) nvM6ExtMem
      (fun () m' => ∃ s',
        FullM6DelayedW2bPres nvM6ExtState s' ∧ s'.LengthsOk nvM6ExtCfg ∧
        nvOneLitF0.Unsat ∧ FullMem nvM6ExtCfg s' m')
      (fun _ _ _ _ => False) := by
  let t10 := m6Tiers_tableImpl.2.2.2.2.2.2.2.2.2.2
  exact t10.2.1.2 (nvM6ExtCfg.hdr, 5#64, ()) nvM6ExtMem _ _
    ⟨nvM6ExtCfg, nvM6ExtState, emp, rfl, nvM6Ext_lengths, nvM6ExtMem_sep,
      fun () s' m' _ hln hpr hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hpr.2, hln, nvOneLitF0_unsat, hm'⟩⟩

/-- Extended NV for `full_m6_delaying` (`delay[4]` backoff slot `fullM6DelayCongruence`). -/
theorem full_m6_delaying_ext_nv :
    Func.wp m6TiersEnv full_m6_delaying_body
      (nvM6ExtCfg.hdr, BitVec.ofNat 64 fullM6DelayCongruence, ()) nvM6ExtMem
      (fun (_, ()) m' => ∃ s',
        FullM6DelayedW2bPres nvM6ExtState s' ∧ s'.LengthsOk nvM6ExtCfg ∧
        nvOneLitF0.Unsat ∧ FullMem nvM6ExtCfg s' m')
      (fun _ _ _ _ => False) := by
  let t10 := m6Tiers_tableImpl.2.2.2.2.2.2.2.2.2.2
  exact t10.2.2.2.2.1.2 (nvM6ExtCfg.hdr, BitVec.ofNat 64 fullM6DelayCongruence, ())
    nvM6ExtMem _ _
    ⟨nvM6ExtCfg, nvM6ExtState, emp, rfl, nvM6Ext_lengths, nvM6ExtMem_sep,
      fun _ s' m' _ hln hpr hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hpr.2, hln, nvOneLitF0_unsat, hm'⟩⟩

/-- Extended NV for `full_m6_bump_delay` (`delay[4]` backoff bump). -/
theorem full_m6_bump_delay_ext_nv :
    Func.wp m6TiersEnv full_m6_bump_delay_body
      (nvM6ExtCfg.hdr, BitVec.ofNat 64 fullM6DelaySweep, ()) nvM6ExtMem
      (fun () m' => ∃ s',
        FullM6DelayedW2bPres nvM6ExtState s' ∧ s'.LengthsOk nvM6ExtCfg ∧
        nvOneLitF0.Unsat ∧ FullMem nvM6ExtCfg s' m')
      (fun _ _ _ _ => False) := by
  let t15 := m6Tiers_tableImpl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact t15.1.2 (nvM6ExtCfg.hdr, BitVec.ofNat 64 fullM6DelaySweep, ()) nvM6ExtMem _ _
    ⟨nvM6ExtCfg, nvM6ExtState, emp, rfl, nvM6Ext_lengths, nvM6ExtMem_sep,
      fun () s' m' _ hln hpr hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hpr.2, hln, nvOneLitF0_unsat, hm'⟩⟩

/-- Extended NV for `full_m6_reduce_delay` & `full_m6_reset_delay`. -/
theorem full_m6_reduce_delay_ext_nv :
    Func.wp m6TiersEnv full_m6_reduce_delay_body
      (nvM6ExtCfg.hdr, BitVec.ofNat 64 fullM6DelayVivifyIrr, ()) nvM6ExtMem
      (fun () m' => ∃ s',
        FullM6DelayedW2bPres nvM6ExtState s' ∧ s'.LengthsOk nvM6ExtCfg ∧
        nvOneLitF0.Unsat ∧ FullMem nvM6ExtCfg s' m')
      (fun _ _ _ _ => False) := by
  let t15 := m6Tiers_tableImpl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact t15.2.1.2 (nvM6ExtCfg.hdr, BitVec.ofNat 64 fullM6DelayVivifyIrr, ()) nvM6ExtMem _ _
    ⟨nvM6ExtCfg, nvM6ExtState, emp, rfl, nvM6Ext_lengths, nvM6ExtMem_sep,
      fun () s' m' _ hln hpr hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hpr.2, hln, nvOneLitF0_unsat, hm'⟩⟩

/-- Extended NV for `full_m6_set_watermark` & `full_m6_add_ticks`. -/
theorem full_m6_add_ticks_ext_nv :
    Func.wp m6TiersEnv full_m6_add_ticks_body (nvM6ExtCfg.hdr, 42#64, ()) nvM6ExtMem
      (fun () m' => ∃ s',
        FullM6DelayedW2bPres nvM6ExtState s' ∧ s'.LengthsOk nvM6ExtCfg ∧
        nvOneLitF0.Unsat ∧ FullMem nvM6ExtCfg s' m')
      (fun _ _ _ _ => False) := by
  let t20 := m6Tiers_tableImpl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact t20.1.2 (nvM6ExtCfg.hdr, 42#64, ()) nvM6ExtMem _ _
    ⟨nvM6ExtCfg, nvM6ExtState, emp, rfl, nvM6Ext_lengths, nvM6ExtMem_sep,
      fun () s' m' _ hln hpr hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hpr.2, hln, nvOneLitF0_unsat, hm'⟩⟩

/-- Extended NV for `full_switch_mode_m6` on `nvM6ExtMem` (`X := False`). -/
theorem full_switch_mode_ext_nv :
    Func.wp m6TiersEnv full_switch_mode_m6_body (nvM6ExtCfg.hdr, ()) nvM6ExtMem
      (fun () m' => ∃ s',
        PreservesCoreSlice FullState.core nvM6ExtState s' ∧
        s'.LengthsOk nvM6ExtCfg ∧ FullProbeScratchPres nvM6ExtState s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvM6ExtCfg s' m')
      (fun _ _ _ _ => False) := by
  let t25 := m6Tiers_tableImpl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact t25.1.2 (nvM6ExtCfg.hdr, ()) nvM6ExtMem _ _
    ⟨nvM6ExtCfg, nvM6ExtState, emp, rfl, nvM6Ext_lengths, nvM6ExtMem_sep,
      fun () s' m' hco hln hpr hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hco, hln, hpr, nvOneLitF0_unsat, hm'⟩⟩

/-- Extended NV for `full_rephase_m6` on `nvM6ExtMem` (`X := False`). -/
theorem full_rephase_ext_nv :
    Func.wp m6TiersEnv full_rephase_m6_body (nvM6ExtCfg.hdr, ()) nvM6ExtMem
      (fun () m' => ∃ s',
        FullCoreInv nvM6ExtCfg nvOneLitF0 s' ∧ FullExtScratchPres nvM6ExtState s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvM6ExtCfg s' m')
      (fun _ _ _ _ => False) := by
  let t25 := m6Tiers_tableImpl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact t25.2.1.2 (nvM6ExtCfg.hdr, ()) nvM6ExtMem _ _
    ⟨nvM6ExtCfg, nvOneLitF0, nvM6ExtState, emp, rfl, nvM6Ext_coreInv, nvM6ExtMem_sep,
      fun _ _ _ _ _ _ _ _ _ _ _ _ hinv _ _ _ hpr hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hinv, hpr, nvOneLitF0_unsat, hm'⟩⟩

/-- Extended NV for `full_reduce_m6` on `nvM6ExtMem` (`X := False`). -/
theorem full_reduce_ext_nv :
    Func.wp m6TiersEnv full_reduce_m6_body (nvM6ExtCfg.hdr, false, ()) nvM6ExtMem
      (fun (r, ()) m' => ∃ s',
        (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧
        FullSparseInvW nvM6ExtCfg nvOneLitF0 [[0], [1]] s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvM6ExtCfg s' m')
      (fun _ _ _ _ => False) := by
  let t25 := m6Tiers_tableImpl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact t25.2.2.1.2 (nvM6ExtCfg.hdr, false, ()) nvM6ExtMem _ _
    ⟨nvM6ExtCfg, nvOneLitF0, [[0], [1]], nvM6ExtState, emp, rfl, nvM6Ext_sparseW,
      nvM6ExtMem_sep, fun r s' m' hsp hdom _ _ _ _ _ _ _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hdom, hsp, nvOneLitF0_unsat, hm'⟩⟩

/-- Extended NV for `full_analyze_rsn_m6` on `nvM6ExtMem` (`X := False`). -/
theorem full_analyze_rsn_ext_nv :
    Func.wp m6TiersEnv full_analyze_rsn_m6_body
      (nvM6ExtCfg.hdr, 0xFFFFFFFF#32, 0#32, ()) nvM6ExtMem
      (fun (_, ()) m' => ∃ s',
        s'.LengthsOk nvM6ExtCfg ∧ FullWitnessCutInv nvM6ExtCfg nvOneLitF0 [[0], [1]] 1 s'.core ∧
        nvOneLitF0.Unsat ∧ FullMem nvM6ExtCfg s' m')
      (fun _ _ _ _ => False) := by
  let t25 := m6Tiers_tableImpl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact t25.2.2.2.1.2 (nvM6ExtCfg.hdr, 0xFFFFFFFF#32, 0#32, ()) nvM6ExtMem _ _
    ⟨nvM6ExtCfg, nvOneLitF0, [[0], [1]], 1, nvM6ExtState, emp, rfl, nvM6Ext_lengths,
      nvM6Ext_witness.toCut, nvM6Ext_marksCov, by decide, by decide,
      fun h => absurd rfl h, nvM6ExtMem_sep,
      fun _ _ _ _ _ _ _ _ m' hln hcut _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hln, hcut, nvOneLitF0_unsat, hm'⟩⟩

/-- Extended NV for `full_analyze_m6` on `nvM6ExtMem` (`X := False`). -/
theorem full_analyze_ext_nv :
    Func.wp m6TiersEnv full_analyze_m6_body (nvM6ExtCfg.hdr, ()) nvM6ExtMem
      (fun (r, ()) m' => ∃ s',
        (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧ s'.LengthsOk nvM6ExtCfg ∧
        nvOneLitF0.Unsat ∧ FullMem nvM6ExtCfg s' m')
      (fun _ _ _ _ => False) := by
  let t25 := m6Tiers_tableImpl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact t25.2.2.2.2.1.2 (nvM6ExtCfg.hdr, ()) nvM6ExtMem _ _
    ⟨nvM6ExtCfg, nvOneLitF0, [[0], [1]], nvM6ExtState, emp, rfl, nvM6Ext_sparseW,
      nvM6Ext_conflW, nvM6ExtMem_sep, fun r s' m' hln hdom _ _ _ _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hdom, hln, nvOneLitF0_unsat, hm'⟩⟩

/-- Extended NV for `full_probe` on `nvM6ExtMem` (`X := False`). -/
theorem full_probe_ext_nv :
    Func.wp m6TiersEnv full_probe_body (nvM6ExtCfg.hdr, ()) nvM6ExtMem
      (fun (r, ()) m' => ∃ s',
        (r = 1#64 ∨ r = 20#64) ∧ s'.LengthsOk nvM6ExtCfg ∧
        nvOneLitF0.Unsat ∧ FullMem nvM6ExtCfg s' m')
      (fun _ _ _ _ => False) := by
  let t30 := m6Tiers_tableImpl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact t30.2.1.2 (nvM6ExtCfg.hdr, ()) nvM6ExtMem _ _
    ⟨nvM6ExtCfg, nvOneLitF0, nvM6ExtState, emp, rfl, nvM6Ext_sparse, rfl, nvM6ExtMem_sep,
      fun r s' m' hln _ hdom _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hdom, hln, nvOneLitF0_unsat, hm'⟩⟩

/-- Extended NV for `full_eliminate` on `nvM6ExtMem` (`X := False`). -/
theorem full_eliminate_ext_nv :
    Func.wp m6TiersEnv full_eliminate_body (nvM6ExtCfg.hdr, ()) nvM6ExtMem
      (fun (r, ()) m' => ∃ s',
        (r = 1#64 ∨ r = 20#64) ∧ FullSparseInv nvM6ExtCfg nvOneLitF0 s' ∧
        s'.core.cur_level = 0 ∧ nvOneLitF0.Unsat ∧ FullMem nvM6ExtCfg s' m')
      (fun _ _ _ _ => False) := by
  let t30 := m6Tiers_tableImpl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact t30.2.2.2.2.1.2 (nvM6ExtCfg.hdr, ()) nvM6ExtMem _ _
    ⟨nvM6ExtCfg, nvOneLitF0, nvM6ExtState, emp, rfl, nvM6Ext_sparse, rfl, nvM6ExtMem_sep,
      fun r s' m' hsp hcl _ hdom _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hdom, hsp, hcl, nvOneLitF0_unsat, hm'⟩⟩

end LeanQbeTest.T.KissatM6TiersTest

/-! ## 4. Single-Line `#print axioms` Audit (`< 115c`, `std3`-Clean) -/

abbrev m6t_00_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_hdr_sizeof_wf
abbrev m6t_01_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_ext_sizeof_wf
abbrev m6t_02_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_get64_wf
abbrev m6t_03_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_set64_wf
abbrev m6t_04_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_ext_ready_wf
abbrev m6t_05_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_sync_legacy_tiers_wf
abbrev m6t_06_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_recompute_tiers_legacy_wf
abbrev m6t_07_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_recompute_tiers_ext_wf
abbrev m6t_08_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_recompute_tiers_mode_wf
abbrev m6t_09_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_recompute_tiers_m6_wf
abbrev m6t_10_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_update_tier_limits_wf
abbrev m6t_11_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_record_used_wf
abbrev m6t_12_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_get_tier1_wf
abbrev m6t_13_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_get_tier2_wf
abbrev m6t_14_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_delaying_wf
abbrev m6t_15_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_bump_delay_wf
abbrev m6t_16_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_reduce_delay_wf
abbrev m6t_17_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_reset_delay_wf
abbrev m6t_18_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_get_watermark_wf
abbrev m6t_19_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_set_watermark_wf
abbrev m6t_20_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_add_ticks_wf
abbrev m6t_21_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_log10_q16_m6_wf
abbrev m6t_22_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_scale_delta_m6_wf
abbrev m6t_23_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_probe_dticks_m6_wf
abbrev m6t_24_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_elim_dticks_m6_wf
abbrev m6t_25_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_switch_mode_m6_wf
abbrev m6t_26_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_rephase_m6_wf
abbrev m6t_27_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_reduce_m6_wf
abbrev m6t_28_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_analyze_rsn_m6_wf
abbrev m6t_29_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_analyze_m6_wf
abbrev m6t_30_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_probe_m6_wf
abbrev m6t_31_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_probe_wf
abbrev m6t_32_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_elim_bve_m6_wf
abbrev m6t_33_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_eliminate_m6_wf
abbrev m6t_34_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_eliminate_wf
abbrev m6t_fns_wf := @LeanQbe.T.Examples.Kissat.FullM6Tiers.m6Tiers_fns_wf
abbrev m6t_acyc := @LeanQbe.T.Examples.Kissat.FullM6Tiers.m6Tiers_acyclic

abbrev m6t_00_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_hdr_sizeof_wp
abbrev m6t_01_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_ext_sizeof_wp
abbrev m6t_02_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_get64_wp
abbrev m6t_03_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_set64_wp
abbrev m6t_04_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_ext_ready_wp
abbrev m6t_05_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_sync_legacy_tiers_wp
abbrev m6t_06_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_recompute_tiers_legacy_wp
abbrev m6t_07_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_recompute_tiers_ext_wp
abbrev m6t_08_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_recompute_tiers_mode_wp
abbrev m6t_09_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_recompute_tiers_m6_wp
abbrev m6t_10_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_update_tier_limits_wp
abbrev m6t_11_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_record_used_wp
abbrev m6t_12_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_get_tier1_wp
abbrev m6t_13_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_get_tier2_wp
abbrev m6t_14_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_delaying_wp
abbrev m6t_15_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_bump_delay_wp
abbrev m6t_16_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_reduce_delay_wp
abbrev m6t_17_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_reset_delay_wp
abbrev m6t_18_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_get_watermark_wp
abbrev m6t_19_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_set_watermark_wp
abbrev m6t_20_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_m6_add_ticks_wp
abbrev m6t_21_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_log10_q16_m6_wp
abbrev m6t_22_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_scale_delta_m6_wp
abbrev m6t_23_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_probe_dticks_m6_wp
abbrev m6t_24_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_elim_dticks_m6_wp
abbrev m6t_25_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_switch_mode_m6_wp
abbrev m6t_26_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_rephase_m6_wp
abbrev m6t_27_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_reduce_m6_wp
abbrev m6t_28_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_analyze_rsn_m6_wp
abbrev m6t_29_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_analyze_m6_wp
abbrev m6t_30_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_probe_m6_wp
abbrev m6t_31_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_probe_wp
abbrev m6t_32_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_elim_bve_m6_wp
abbrev m6t_33_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_eliminate_m6_wp
abbrev m6t_34_wp := @LeanQbe.T.Examples.Kissat.FullM6Tiers.full_eliminate_wp

abbrev m6t_reph_st := @LeanQbe.T.Examples.Kissat.FullM6Tiers.m6RephaseSpec_of_stable
abbrev m6t_void_full := @LeanQbe.T.Examples.Kissat.FullM6Tiers.m6SafetyVoidSpec_to_full
abbrev m6t_noExit_tbl := @LeanQbe.T.Examples.Kissat.FullM6Tiers.m6TiersSpecTable_noExit
abbrev m6t_noExit := @LeanQbe.T.Examples.Kissat.FullM6Tiers.m6Tiers_noExit
abbrev m6t_tableImpl := @LeanQbe.T.Examples.Kissat.FullM6Tiers.m6Tiers_tableImpl
abbrev m6t_moduleOk := @LeanQbe.T.Examples.Kissat.FullM6Tiers.m6Tiers_moduleOk

abbrev m6t_nv_hdr := @LeanQbeTest.T.KissatM6TiersTest.full_m6_hdr_sizeof_nv
abbrev m6t_nv_ext := @LeanQbeTest.T.KissatM6TiersTest.full_m6_ext_sizeof_nv
abbrev m6t_nv_rdy_leg := @LeanQbeTest.T.KissatM6TiersTest.full_m6_ext_ready_legacy_nv
abbrev m6t_nv_rdy_ext := @LeanQbeTest.T.KissatM6TiersTest.full_m6_ext_ready_ext_nv
abbrev m6t_nv_rec_leg := @LeanQbeTest.T.KissatM6TiersTest.full_recompute_tiers_legacy_nv
abbrev m6t_nv_rec_ext := @LeanQbeTest.T.KissatM6TiersTest.full_recompute_tiers_ext_nv
abbrev m6t_nv_upd := @LeanQbeTest.T.KissatM6TiersTest.full_m6_update_tier_limits_ext_nv
abbrev m6t_nv_used := @LeanQbeTest.T.KissatM6TiersTest.full_m6_record_used_ext_nv
abbrev m6t_nv_dly := @LeanQbeTest.T.KissatM6TiersTest.full_m6_delaying_ext_nv
abbrev m6t_nv_bmp := @LeanQbeTest.T.KissatM6TiersTest.full_m6_bump_delay_ext_nv
abbrev m6t_nv_red_d := @LeanQbeTest.T.KissatM6TiersTest.full_m6_reduce_delay_ext_nv
abbrev m6t_nv_tck := @LeanQbeTest.T.KissatM6TiersTest.full_m6_add_ticks_ext_nv
abbrev m6t_nv_sw := @LeanQbeTest.T.KissatM6TiersTest.full_switch_mode_ext_nv
abbrev m6t_nv_reph := @LeanQbeTest.T.KissatM6TiersTest.full_rephase_ext_nv
abbrev m6t_nv_red := @LeanQbeTest.T.KissatM6TiersTest.full_reduce_ext_nv
abbrev m6t_nv_arsn := @LeanQbeTest.T.KissatM6TiersTest.full_analyze_rsn_ext_nv
abbrev m6t_nv_ana := @LeanQbeTest.T.KissatM6TiersTest.full_analyze_ext_nv
abbrev m6t_nv_prb := @LeanQbeTest.T.KissatM6TiersTest.full_probe_ext_nv
abbrev m6t_nv_elm := @LeanQbeTest.T.KissatM6TiersTest.full_eliminate_ext_nv

#print axioms m6t_00_wf
#print axioms m6t_01_wf
#print axioms m6t_02_wf
#print axioms m6t_03_wf
#print axioms m6t_04_wf
#print axioms m6t_05_wf
#print axioms m6t_06_wf
#print axioms m6t_07_wf
#print axioms m6t_08_wf
#print axioms m6t_09_wf
#print axioms m6t_10_wf
#print axioms m6t_11_wf
#print axioms m6t_12_wf
#print axioms m6t_13_wf
#print axioms m6t_14_wf
#print axioms m6t_15_wf
#print axioms m6t_16_wf
#print axioms m6t_17_wf
#print axioms m6t_18_wf
#print axioms m6t_19_wf
#print axioms m6t_20_wf
#print axioms m6t_21_wf
#print axioms m6t_22_wf
#print axioms m6t_23_wf
#print axioms m6t_24_wf
#print axioms m6t_25_wf
#print axioms m6t_26_wf
#print axioms m6t_27_wf
#print axioms m6t_28_wf
#print axioms m6t_29_wf
#print axioms m6t_30_wf
#print axioms m6t_31_wf
#print axioms m6t_32_wf
#print axioms m6t_33_wf
#print axioms m6t_34_wf
#print axioms m6t_fns_wf
#print axioms m6t_acyc
#print axioms m6t_00_wp
#print axioms m6t_01_wp
#print axioms m6t_02_wp
#print axioms m6t_03_wp
#print axioms m6t_04_wp
#print axioms m6t_05_wp
#print axioms m6t_06_wp
#print axioms m6t_07_wp
#print axioms m6t_08_wp
#print axioms m6t_09_wp
#print axioms m6t_10_wp
#print axioms m6t_11_wp
#print axioms m6t_12_wp
#print axioms m6t_13_wp
#print axioms m6t_14_wp
#print axioms m6t_15_wp
#print axioms m6t_16_wp
#print axioms m6t_17_wp
#print axioms m6t_18_wp
#print axioms m6t_19_wp
#print axioms m6t_20_wp
#print axioms m6t_21_wp
#print axioms m6t_22_wp
#print axioms m6t_23_wp
#print axioms m6t_24_wp
#print axioms m6t_25_wp
#print axioms m6t_26_wp
#print axioms m6t_27_wp
#print axioms m6t_28_wp
#print axioms m6t_29_wp
#print axioms m6t_30_wp
#print axioms m6t_31_wp
#print axioms m6t_32_wp
#print axioms m6t_33_wp
#print axioms m6t_34_wp
#print axioms m6t_reph_st
#print axioms m6t_void_full
#print axioms m6t_noExit_tbl
#print axioms m6t_noExit
#print axioms m6t_tableImpl
#print axioms m6t_moduleOk
#print axioms m6t_nv_hdr
#print axioms m6t_nv_ext
#print axioms m6t_nv_rdy_leg
#print axioms m6t_nv_rdy_ext
#print axioms m6t_nv_rec_leg
#print axioms m6t_nv_rec_ext
#print axioms m6t_nv_upd
#print axioms m6t_nv_used
#print axioms m6t_nv_dly
#print axioms m6t_nv_bmp
#print axioms m6t_nv_red_d
#print axioms m6t_nv_tck
#print axioms m6t_nv_sw
#print axioms m6t_nv_reph
#print axioms m6t_nv_red
#print axioms m6t_nv_arsn
#print axioms m6t_nv_ana
#print axioms m6t_nv_prb
#print axioms m6t_nv_elm
