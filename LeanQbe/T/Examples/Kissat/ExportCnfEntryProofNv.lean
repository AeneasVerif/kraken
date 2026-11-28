/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.ExportCnfEntryProof
public import LeanQbe.T.Examples.Kissat.Proof.Spec.SatNv1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import Kraken.Mem
import Kraken.Separation

/-!
# Verified Simplified-CNF Exporter — Shard E3 Concrete `Mem 64` Non-Vacuity (`<= std3`)

Concrete `Mem 64` non-vacuity witnesses (`XPost := False`, `<= std3`) for `ExportCnfEntry`
(`exportCnfEntryEnv`, zero dependency on `FullM6Proof`, `FullM6SatSound`, or `FullM6OrchProof2`):
1. `export_entry_unit_unknown_nv`: deterministic `r = 1#64` simplified CNF export through real
   `kissat_export_cnf_bytes` (`exportCnfEntryEnv`) on a unit-clause `FullState`.
2. `export_entry_inconsistent_nv`: deterministic `r = 20#64` emission of `"p cnf 0 1\n0\n"` when
   `h->inconsistent != 0` on `pp = 1` (`BUG-CROSS-01` fix).
3. `export_entry_sat_nv`: deterministic `r = 10#64` emission of `"p cnf 0 0\n"` (`10 B`)
   on `pp = 10`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.ExportCnfEntryProof

open Std Std.Sat Std.ExtHashMap
open Kraken
open Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src
open LeanQbe.T.Examples.Kissat.Ref hiding isDimacsWs isDimacsDigit dimacsBound
  skipWsCommentsAux skipWsComments skipWs skipWs1 parseDigitsAux parseNat
  parseHeader parseClauseAux parseClause parseClauses parseDimacs
open LeanQbe.T.Examples.Kissat.Proof.Spec hiding
  fullM6WorkBase fullM6WorkHdr m6ExtAddr_fullM6WorkHdr
  region_work_to_m6_workBase region_work_from_m6_hdrMem
  fullM6PreprocessSpec fullM6PreprocessSpec_of fullM6PreprocessSpec_monoX
  nvM6CnfPtr nvM6WorkLen nvM6SatBytes nvM6SatCnf nvM6SatWorkPtr
  nvM6ExtInitWords nvM6SatCfg nvM6SatState nvM6SatBlockHdr nvM6SatBlockBytes
  nvM6SatBlockU32A nvM6SatBlockU32B nvM6SatBlockU32C nvM6SatBlockWvec
  nvM6SatBlockTail nvM6SatArenaBytes nvM6MemBytes nvM6Mem_ok
  nvM6SatCfg_avail_fit nvM6SatCfg_hsize nvM6SatCnf_sat nvM6SatCnf_not_unsat
  nvM6ExtInitWords_len nvM6Sat_lengths
open LeanQbe.T.Examples.Kissat.ExportCnfFmt
open LeanQbe.T.Examples.Kissat.ExportCnfState
open LeanQbe.T.Examples.Kissat.ExportCnfEntry

public section

/-! ## 1. Concrete `M6Hdr` Heap Fixture & `KissatExportOut` Layout (`<= std3`) -/

/-- Shared 8-byte aligned `KissatExportOut` descriptor address (`0x4000#64`). -/
@[expose] def nvOutDescPtr : BitVec 64 := 0x4000#64

/-- Shared output buffer base address immediately following `nvOutDescPtr` (`0x4018#64`). -/
@[expose] def nvOutBufPtr : BitVec 64 := 0x4018#64

/-- Concrete CNF pointer (`0x1000#64`) and `8,192 B` workspace length for NV fixtures. -/
@[expose] def nvM6CnfPtr : BitVec 64 := 0x1000#64

/-- Concrete `8,192 B` workspace size. -/
@[expose] def nvM6WorkLen : Nat := 8192

/-- Concrete SAT DIMACS `"p cnf 2 1\n1 2 0\n"` (`(x1 ∨ x2)`, `16` bytes). -/
@[expose] def nvM6SatBytes : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 50, 32, 49, 10, 49, 32, 50, 32, 48, 10]

/-- Parsed `CNF Nat` for `nvM6SatBytes`. -/
@[expose] def nvM6SatCnf : CNF Nat :=
  CNF.empty.add (CNF.Clause.ofLiterals [(1, true), (2, true)])

/-- Concrete workspace base address immediately following `nvM6SatBytes`. -/
@[expose] def nvM6SatWorkPtr : BitVec 64 :=
  nvM6CnfPtr + BitVec.ofNat 64 nvM6SatBytes.length

/-- Canonical initialized `288`-word `M6HdrExt` header (`fullM6HdrMagic` at word `0`). -/
@[expose] def nvM6ExtInitWords : List (BitVec 64) :=
  fullM6HdrMagic :: List.replicate 287 0#64

private theorem nvM6SatCnf_sat : ∃ α, nvM6SatCnf.Sat α := by
  refine ⟨fun v => v == 1, ?_⟩
  rw [nvM6SatCnf, CNF.sat_add]
  refine ⟨?_, CNF.sat_empty⟩
  rw [CNF.Clause.sat_iff_exists_mem_eq]
  exact ⟨(1, true), by rw [← CNF.Clause.mem_literals_iff]; simp, rfl⟩

private theorem nvM6SatCnf_not_unsat : ¬ nvM6SatCnf.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  exact fun h => let ⟨α, hα⟩ := nvM6SatCnf_sat; h α hα

private theorem nvM6ExtInitWords_len : nvM6ExtInitWords.length = fullM6ExtWords := by
  rw [nvM6ExtInitWords, List.length_cons, List.length_replicate, fullM6ExtWords]

theorem nvM6SatCfg_avail_fit :
    (6416#64 : BitVec 64).toNat + (nvM6WorkLen - fullM6ExtBytes) < 2 ^ 64 := by
  unfold nvM6WorkLen fullM6ExtBytes
  decide

theorem nvM6SatCfg_hsize :
    fullFixedBytes 2 + 4 * 0 + 4 * 1 + 12 * 0 + 4 * 0 + 4 * 0 + 4 * 0 ≤
      nvM6WorkLen - fullM6ExtBytes := by
  have hfb : fullFixedBytes 2 = 1960 := by
    unfold fullFixedBytes valsBytes markBytes u32FullBytes fullMinDepthOf; decide
  rw [hfb]
  unfold nvM6WorkLen fullM6ExtBytes
  omega

/-- Concrete `FullCfg` for `nvM6SatBytes` (`mv = 2, nc = 1`) at `fullM6WorkHdr nvM6SatWorkPtr`. -/
@[expose] def nvM6SatCfg : FullCfg where
  hdr := 6416#64
  avail := nvM6WorkLen - fullM6ExtBytes
  mv := 2
  max_vars := 2
  bva_cap := 0
  nc := 1
  arena_cap := 0
  wcap := 1
  delayed_cap := 0
  red_cap := 0
  extend_cap := 0
  scratch_cap := 0
  hbva := rfl
  hmv := by unfold Ref.dimacsBound; omega
  hmaxv := by unfold Ref.dimacsBound; omega
  hnc := by unfold Ref.dimacsBound; omega
  harena := by unfold Ref.dimacsBound; omega
  hwcap := by unfold Ref.dimacsBound; omega
  hdel := by unfold Ref.dimacsBound; omega
  hred := by unfold Ref.dimacsBound; omega
  hext := by unfold Ref.dimacsBound; omega
  hscr := by unfold Ref.dimacsBound; omega
  havail_fit := nvM6SatCfg_avail_fit
  hsize := nvM6SatCfg_hsize

/-- Concrete solved `FullState` for `(x1 ∨ x2)` with `vals = [1#8, 0xFF#8, 1#8, 0xFF#8]`. -/
@[expose] def nvM6SatState : FullState where
  core :=
    { nvOneLitState.core with
      cur_vars := 2, unassigned := 0#64
      vals := [1#8, 0xFF#8, 1#8, 0xFF#8]
      lit_mark := List.replicate 4 0#8
      mrk := List.replicate 2 0#8
      flags := List.replicate 2 0#32
      lvl := List.replicate 2 0#32
      rsns := List.replicate 2 0xFFFFFFFF#32
      trl := List.replicate 2 0#32
      trail_pos := List.replicate 2 0#32
      tmp := List.replicate 2 0#32
      min_clr := List.replicate 2 0#32
      frame_trail := List.replicate 3 0#32
      frame_dec := List.replicate 3 0#32
      wvec := List.replicate 8 0#32
      repr := List.replicate 4 0#32
      min_stk := List.replicate 6 0#32 }
  scratch :=
    { nvOneLitState.scratch with
      walk_vals := List.replicate 4 0#8
      phases := List.replicate 2 0#8
      phases_target := List.replicate 2 0#8
      phases_best := List.replicate 2 0#8
      walk_best := List.replicate 2 0#8
      heap := List.replicate 2 0#32
      pos := List.replicate 2 0#32
      shrink_stk := List.replicate 2 0#32
      q_prev := List.replicate 2 0#32
      q_next := List.replicate 2 0#32
      q_stamp := List.replicate 2 0#32
      wsort := List.replicate 4 0#32
      work_stk1 := List.replicate 4 0#32
      work_stk2 := List.replicate 4 0#32
      tarjan_mark := List.replicate 4 0#32
      tarjan_reach := List.replicate 4 0#32
      score := List.replicate 2 0#64
      sim_sig := List.replicate 2 0#64 }

private theorem nvM6Sat_lengths : nvM6SatState.LengthsOk nvM6SatCfg :=
  ⟨by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [nvM6SatState, nvM6SatCfg, nvOneLitState, FullCfg.minDepth, fullMinDepthOf],
   by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [nvM6SatState, nvM6SatCfg, nvOneLitState, nvOneLitScratch]⟩

@[expose] def nvM6SatBlockHdr : List UInt8 :=
  bytes64 [2#64, 1#64, 0#64, 0#64] ++ bytes64 (hdrTailWords nvM6SatCfg nvM6SatState)

@[expose] def nvM6SatBlockBytes : List UInt8 :=
  (bytesOf (t := i8) nvM6SatState.core.vals ++ List.replicate 4 0) ++
  (bytesOf (t := i8) nvM6SatState.scratch.walk_vals ++ List.replicate 4 0) ++
  (bytesOf (t := i8) nvM6SatState.core.lit_mark ++ List.replicate 4 0) ++
  (bytesOf (t := i8) nvM6SatState.core.mrk ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvM6SatState.scratch.phases ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvM6SatState.scratch.phases_target ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvM6SatState.scratch.phases_best ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvM6SatState.scratch.walk_best ++ List.replicate 6 0)

@[expose] def nvM6SatBlockU32A : List UInt8 :=
  (bytesOf (t := i32) nvM6SatState.core.flags ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.core.lvl ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.core.rsns ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.core.trl ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.core.trail_pos ++ List.replicate 8 0)

@[expose] def nvM6SatBlockU32B : List UInt8 :=
  (bytesOf (t := i32) nvM6SatState.core.tmp ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.scratch.heap ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.scratch.pos ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.core.min_clr ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.scratch.shrink_stk ++ List.replicate 8 0)

@[expose] def nvM6SatBlockU32C : List UInt8 :=
  (bytesOf (t := i32) nvM6SatState.scratch.q_prev ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.scratch.q_next ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.scratch.q_stamp ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.core.frame_trail ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM6SatState.core.frame_dec ++ List.replicate 4 0)

@[expose] def nvM6SatBlockWvec : List UInt8 :=
  bytesOf (t := i32) nvM6SatState.core.wvec ++
  bytesOf (t := i32) nvM6SatState.core.repr ++
  bytesOf (t := i32) nvM6SatState.scratch.wsort ++
  bytesOf (t := i32) nvM6SatState.scratch.work_stk1 ++
  bytesOf (t := i32) nvM6SatState.scratch.work_stk2 ++
  bytesOf (t := i32) nvM6SatState.scratch.tarjan_mark ++
  bytesOf (t := i32) nvM6SatState.scratch.tarjan_reach ++
  bytes64 nvM6SatState.scratch.score ++
  bytes64 nvM6SatState.scratch.sim_sig

@[expose] def nvM6SatBlockTail : List UInt8 :=
  bytesOf (t := i32) nvM6SatState.core.min_stk ++
  bytesOf (t := i32) nvM6SatState.scratch.glue_used ++
  bytesOf (t := i32) nvM6SatState.scratch.last_learned ++
  bytesOf (t := i32) nvM6SatState.core.arena ++
  bytesOf (t := i32) nvM6SatState.core.wstk ++
  bytesOf (t := i32) nvM6SatState.scratch.delayed ++
  bytesOf (t := i32) nvM6SatState.scratch.red_refs ++
  bytesOf (t := i32) nvM6SatState.scratch.extend_stk ++
  bytesOf (t := i32) nvM6SatState.scratch.scratch_buf ++
  List.replicate nvM6SatCfg.slack 0

@[expose] def nvM6SatArenaBytes : List UInt8 :=
  nvM6SatBlockHdr ++ nvM6SatBlockBytes ++ nvM6SatBlockU32A ++ nvM6SatBlockU32B ++
  nvM6SatBlockU32C ++ nvM6SatBlockWvec ++ nvM6SatBlockTail

@[expose] def nvM6MemBytes : List UInt8 :=
  nvM6SatBytes ++ bytes64 nvM6ExtInitWords ++ nvM6SatArenaBytes

private theorem nvM6SatCfg_slack : nvM6SatCfg.slack = 3924 := by
  unfold FullCfg.slack nvM6SatCfg nvM6WorkLen fullM6ExtBytes fullFixedBytes valsBytes
    markBytes u32FullBytes fullMinDepthOf
  decide

private theorem nvJ {bs1 bs2 : List UInt8} {a1 a2 : BitVec 64} {n1 n2 : Nat}
    {P1 P2 : Mem 64 → Prop} (h1 : bs1.length = n1 ∧ P1 (bs1.At a1))
    (h2 : bs2.length = n2 ∧ P2 (bs2.At a2))
    (ha : a2 = a1 + BitVec.ofNat 64 n1 := by decide)
    (hf : n1 + n2 ≤ 2 ^ 64 := by decide) :
    (bs1 ++ bs2).length = n1 + n2 ∧ (P1 ⋆ P2) ((bs1 ++ bs2).At a1) :=
  nv_join_pair h1 h2 ha hf

private theorem nvAP (t : Ty) (a : BitVec 64) (xs : List (Val t)) (n pad : Nat)
    (hl : t.bytes * xs.length = n := by
      simp [nvM6SatState, nvOneLitState, nvOneLitScratch, Ty.bytes, Ty.size])
    (hf : n + pad ≤ 2 ^ 64 := by decide) :
    (bytesOf (t := t) xs ++ List.replicate pad 0).length = n + pad ∧
      (array (t := t) a xs ⋆ region (a + BitVec.ofNat 64 n) pad)
        ((bytesOf (t := t) xs ++ List.replicate pad 0).At a) :=
  nv_arr_pad_p n pad hl hf

private theorem nvA (t : Ty) (a : BitVec 64) (xs : List (Val t)) (n : Nat)
    (hl : t.bytes * xs.length = n := by
      simp [nvM6SatState, nvOneLitState, nvOneLitScratch, Ty.bytes, Ty.size])
    (hf : n ≤ 2 ^ 64 := by decide) :
    (bytesOf (t := t) xs).length = n ∧ array (t := t) a xs ((bytesOf (t := t) xs).At a) :=
  nv_arr_p n hl hf

private theorem nvM6SatArena_ok :
    nvM6SatArenaBytes.length = nvM6SatCfg.avail ∧
      FullMem nvM6SatCfg nvM6SatState (nvM6SatArenaBytes.At nvM6SatCfg.hdr) := by
  have hvb : valsBytes nvM6SatCfg.max_vars - 2 * nvM6SatCfg.max_vars = 4 := by
    unfold valsBytes nvM6SatCfg; decide
  have hmb : markBytes nvM6SatCfg.max_vars - nvM6SatCfg.max_vars = 6 := by
    unfold markBytes nvM6SatCfg; decide
  have hu4 : u32FullBytes nvM6SatCfg.max_vars - 4 * nvM6SatCfg.max_vars = 8 := by
    unfold u32FullBytes nvM6SatCfg; decide
  have hu8 : u32FullBytes nvM6SatCfg.max_vars - 4 * (nvM6SatCfg.max_vars + 1) = 4 := by
    unfold u32FullBytes nvM6SatCfg; decide
  have hHdr := nvJ
    (nv_arr64_p (a := nvM6SatCfg.hdr) (xs := [2#64, 1#64, 0#64, 0#64]) 32 rfl (by decide))
    (nv_arr64_p (a := nvM6SatCfg.hdr + 32) (xs := hdrTailWords nvM6SatCfg nvM6SatState)
      1120 (by rw [hdrTailWords_length]) (by decide)) rfl
  let pB1 : Mem 64 → Prop :=
    region (nvM6SatCfg.pVals + 4#64) 4 ⋆ region (nvM6SatCfg.pWalkVals + 4#64) 4 ⋆
    region (nvM6SatCfg.pLitMark + 4#64) 4 ⋆ region (nvM6SatCfg.pMark + 2#64) 6
  have h1234 := nv_sep_reorg
    (nvJ (nvJ (nvJ (nvAP i8 nvM6SatCfg.pVals nvM6SatState.core.vals 4 4 rfl)
        (nvAP i8 nvM6SatCfg.pWalkVals nvM6SatState.scratch.walk_vals 4 4))
      (nvAP i8 nvM6SatCfg.pLitMark nvM6SatState.core.lit_mark 4 4))
      (nvAP i8 nvM6SatCfg.pMark nvM6SatState.core.mrk 2 6))
    (Q := (FullCoreByteArrs nvM6SatCfg nvM6SatState.core ⋆
      array (t := i8) nvM6SatCfg.pWalkVals nvM6SatState.scratch.walk_vals) ⋆ pB1)
    fun _ hm => nv_zip4 hm
  have hBytes := nv_sep_reorg
    (nvJ (nvJ (nvJ (nvJ h1234 (nvAP i8 nvM6SatCfg.pPhases nvM6SatState.scratch.phases 2 6))
        (nvAP i8 nvM6SatCfg.pPhasesTarget nvM6SatState.scratch.phases_target 2 6))
      (nvAP i8 nvM6SatCfg.pPhasesBest nvM6SatState.scratch.phases_best 2 6))
      (nvAP i8 nvM6SatCfg.pWalkBest nvM6SatState.scratch.walk_best 2 6))
    (Q := FullCoreByteArrs nvM6SatCfg nvM6SatState.core ⋆
      FullScrByteArrs nvM6SatCfg nvM6SatState.scratch ⋆ nvM6SatCfg.padBytes)
    fun _ hm => by
      have hfin := nv_zip4_tail hm
      unfold FullScrByteArrs FullCfg.padBytes
      rw [hvb, hmb, show BitVec.ofNat 64 (2 * nvM6SatCfg.max_vars) = 4#64 from rfl,
        show BitVec.ofNat 64 nvM6SatCfg.max_vars = 2#64 from rfl]
      simpa only [pB1, sep_assoc] using hfin
  have hU32A := nvJ (nvJ (nvJ (nvJ (nvAP i32 nvM6SatCfg.pFlags nvM6SatState.core.flags 8 8)
      (nvAP i32 nvM6SatCfg.pLevel nvM6SatState.core.lvl 8 8))
    (nvAP i32 nvM6SatCfg.pReason nvM6SatState.core.rsns 8 8))
    (nvAP i32 nvM6SatCfg.pTrail nvM6SatState.core.trl 8 8))
    (nvAP i32 nvM6SatCfg.pTrailPos nvM6SatState.core.trail_pos 8 8)
  have hU32B := nvJ (nvJ (nvJ (nvJ (nvAP i32 nvM6SatCfg.pTmp nvM6SatState.core.tmp 8 8)
      (nvAP i32 nvM6SatCfg.pHeap nvM6SatState.scratch.heap 8 8))
    (nvAP i32 nvM6SatCfg.pPos nvM6SatState.scratch.pos 8 8))
    (nvAP i32 nvM6SatCfg.pMinClr nvM6SatState.core.min_clr 8 8))
    (nvAP i32 nvM6SatCfg.pShrinkStk nvM6SatState.scratch.shrink_stk 8 8)
  have hU32C := nvJ (nvJ (nvJ (nvJ (nvAP i32 nvM6SatCfg.pQPrev nvM6SatState.scratch.q_prev 8 8)
      (nvAP i32 nvM6SatCfg.pQNext nvM6SatState.scratch.q_next 8 8))
    (nvAP i32 nvM6SatCfg.pQStamp nvM6SatState.scratch.q_stamp 8 8))
    (nvAP i32 nvM6SatCfg.pFrameTrail nvM6SatState.core.frame_trail 12 4))
    (nvAP i32 nvM6SatCfg.pFrameDec nvM6SatState.core.frame_dec 12 4)
  have hWvec := nvJ (nvJ (nvJ (nvJ (nvJ (nvJ (nvJ (nvJ
      (nvA i32 nvM6SatCfg.pWvec nvM6SatState.core.wvec 32)
      (nvA i32 nvM6SatCfg.pRepr nvM6SatState.core.repr 16))
    (nvA i32 nvM6SatCfg.pWsort nvM6SatState.scratch.wsort 16))
    (nvA i32 nvM6SatCfg.pWorkStk1 nvM6SatState.scratch.work_stk1 16))
    (nvA i32 nvM6SatCfg.pWorkStk2 nvM6SatState.scratch.work_stk2 16))
    (nvA i32 nvM6SatCfg.pTarjanMark nvM6SatState.scratch.tarjan_mark 16))
    (nvA i32 nvM6SatCfg.pTarjanReach nvM6SatState.scratch.tarjan_reach 16))
    (nv_arr64_p (a := nvM6SatCfg.pScore) (xs := nvM6SatState.scratch.score) 16 rfl (by decide)))
    (nv_arr64_p (a := nvM6SatCfg.pSimSig) (xs := nvM6SatState.scratch.sim_sig) 16 rfl (by decide))
  have hSlack : (List.replicate nvM6SatCfg.slack (0 : UInt8)).length = 3924 ∧
      region nvM6SatCfg.pSlack nvM6SatCfg.slack
        ((List.replicate nvM6SatCfg.slack 0).At nvM6SatCfg.pSlack) :=
    ⟨by rw [List.length_replicate, nvM6SatCfg_slack],
      ⟨List.replicate nvM6SatCfg.slack 0, List.length_replicate, rfl⟩⟩
  have hTail := nvJ (nvJ (nvJ (nvJ (nvJ (nvJ (nvJ (nvJ (nvJ
      (nvA i32 nvM6SatCfg.pMinStk nvM6SatState.core.min_stk 24)
      (nvA i32 nvM6SatCfg.pGlueUsed nvM6SatState.scratch.glue_used 256))
    (nvA i32 nvM6SatCfg.pLastLearned nvM6SatState.scratch.last_learned 64))
    (nvA i32 nvM6SatCfg.pArena nvM6SatState.core.arena 0))
    (nvA i32 nvM6SatCfg.pWstk nvM6SatState.core.wstk 4))
    (nvA i32 nvM6SatCfg.pDelayed nvM6SatState.scratch.delayed 0))
    (nvA i32 nvM6SatCfg.pRedRefs nvM6SatState.scratch.red_refs 0))
    (nvA i32 nvM6SatCfg.pExtendStk nvM6SatState.scratch.extend_stk 0))
    (nvA i32 nvM6SatCfg.pScratchBuf nvM6SatState.scratch.scratch_buf 0)) hSlack
  have h06 := nv_sep_reorg
    (nvJ (nvJ (nvJ (nvJ (nvJ (nvJ hHdr hBytes) hU32A) hU32B) hU32C) hWvec) hTail
      (by decide) (by omega))
    (Q := FullMem nvM6SatCfg nvM6SatState) fun _ hm => by
      unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
        FullScrWksArrs FullCoreDynArrs FullScrDynArrs FullScrMetaArrs FullCfg.pad
        FullCfg.padU32A FullCfg.padU32B FullCfg.padU32C dimacsState
      rw [hu4, hu8, show BitVec.ofNat 64 (4 * nvM6SatCfg.max_vars) = 8#64 from rfl,
        show BitVec.ofNat 64 (4 * (nvM6SatCfg.max_vars + 1)) = 12#64 from rfl]
      exact sep_ac hm
  exact ⟨show nvM6SatArenaBytes.length = nvM6SatCfg.avail from h06.1, h06.2⟩

private theorem nvM6Mem_ok :
    (bytes nvM6CnfPtr nvM6SatBytes ⋆
      FullM6HdrMem nvM6SatCfg nvM6ExtInitWords nvM6SatState) (nvM6MemBytes.At nvM6CnfPtr) := by
  have hExt := nv_arr64_p (a := nvM6SatWorkPtr) (xs := nvM6ExtInitWords) 2304
    (by rw [nvM6ExtInitWords_len]; rfl) (by decide)
  have hav : nvM6SatCfg.avail = 5888 := rfl
  have hM6 := nv_sep_reorg
    (nvJ hExt nvM6SatArena_ok rfl (by rw [hav]; decide))
    (Q := FullM6HdrMem nvM6SatCfg nvM6ExtInitWords nvM6SatState) fun _ hm =>
      fullM6HdrMem_mk (by rw [show nvM6SatCfg.hdr - 2304 = nvM6SatWorkPtr from rfl]; exact hm)
  exact (nvJ ⟨rfl, rfl⟩ hM6 rfl (by rw [hav]; decide)).2

private theorem nv_exportOutMem_bytes64 (outPtr outCap oldLen : BitVec 64) :
    (bytes64 [outPtr, outCap, oldLen]).length = 24 ∧
    exportOutMem nvOutDescPtr outPtr outCap oldLen
      ((bytes64 [outPtr, outCap, oldLen]).At nvOutDescPtr) := by
  have ha := nv_arr64_p (a := nvOutDescPtr) (xs := [outPtr, outCap, oldLen]) 24 rfl (by decide)
  refine ⟨ha.1, ?_⟩
  unfold exportOutMem
  have ha2 := ha.2
  simp only [array64_eq_array, array, show nvOutDescPtr + 8#64 + 8#64 =
    nvOutDescPtr + 16#64 by decide, show BitVec.ofNat 64 i64.bytes = 8#64 by decide] at ha2
  rw [_root_.Std.ExtHashMap.sep_emp] at ha2
  exact sep_ac ha2

/-! ## 2. Deterministic Concrete `Mem 64` Non-Vacuity (`r = 1#64`, `r = 20#64`, `r = 10#64`) -/

/-- Functional sequential byte overwrite into `Mem 64` for concrete witness assembly. -/
@[expose] def storeBytes (m : Mem 64) (p : BitVec 64) : List UInt8 → Mem 64
  | [] => m
  | b :: bs => storeBytes (storeMem m i8 p (BitVec.ofNat 8 b.toNat)) (p + 1#64) bs

private theorem eq_bytes_cons (p : BitVec 64) (b : UInt8) (bs : List UInt8)
    (h : bs.length + 1 ≤ 2 ^ 64) :
    bytes p (b :: bs) =
      (Kraken.Bedrock2.Test.byte1 p (BitVec.ofNat 64 b.toNat) ⋆ bytes (p + 1#64) bs) := by
  change Eq (([b] ++ bs).At p) = _
  rw [eq_append_At p [b] bs (by simp; omega)]
  simp only [List.length_singleton, Kraken.Bedrock2.Test.byte1]
  have hb : Int.toBytes 1 (BitVec.ofNat 64 b.toNat).toNat = [b] := by
    have hlt : b.toNat < 2 ^ 64 := Nat.lt_trans b.toNat_lt (by decide : 2 ^ 8 < 2 ^ 64)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    exact toBytes_u8 b
  rw [hb]; rfl

private theorem storeBytes_bytes_frame :
    ∀ {bs0 bs1 : List UInt8} {p : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64},
      bs0.length = bs1.length → bs0.length < 2 ^ 64 →
      (bytes p bs0 ⋆ R) m → (bytes p bs1 ⋆ R) (storeBytes m p bs1)
  | [], [], _, _, m, _, _, hm => by simpa [storeBytes] using hm
  | b0 :: bs0, b1 :: bs1, p, R, m, hlen, hlt, hm => by
    have hlen' : bs0.length = bs1.length := by simpa using hlen
    rw [eq_bytes_cons p b0 bs0 (by simp at hlt; omega)] at hm
    have hs := (store_byte1 (BitVec.ofNat 8 b1.toNat)
      (sep_ac hm : (Kraken.Bedrock2.Test.byte1 p (BitVec.ofNat 64 b0.toNat) ⋆
        (bytes (p + 1#64) bs0 ⋆ R)) m)).2
    have hblt : b1.toNat < 2 ^ 64 := Nat.lt_trans b1.toNat_lt (by decide : 2 ^ 8 < 2 ^ 64)
    have hsw : (BitVec.ofNat 8 b1.toNat).setWidth 64 = BitVec.ofNat 64 b1.toNat := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt b1.toNat_lt, Nat.mod_eq_of_lt hblt]
    rw [hsw] at hs
    have hhs : (bytes (p + 1#64) bs0 ⋆
        (Kraken.Bedrock2.Test.byte1 p (BitVec.ofNat 64 b1.toNat) ⋆ R))
        (storeMem m i8 p (BitVec.ofNat 8 b1.toNat)) := sep_ac hs
    have hrec := storeBytes_bytes_frame hlen' (by simp at hlt; omega) hhs
    have hgoal : (Kraken.Bedrock2.Test.byte1 p (BitVec.ofNat 64 b1.toNat) ⋆
        bytes (p + 1#64) bs1 ⋆ R)
        (storeBytes (storeMem m i8 p (BitVec.ofNat 8 b1.toNat)) (p + 1#64) bs1) := sep_ac hrec
    rw [eq_bytes_cons p b1 bs1 (by simp at hlt; omega)]
    exact sep_ac hgoal

private theorem nv_base_sat_mem_sep :
    (bytes nvM6CnfPtr nvM6SatBytes ⋆ FullM6HdrMem nvM6SatCfg nvM6ExtInitWords nvM6SatState ⋆
      region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080 ⋆
      exportOutMem nvOutDescPtr nvOutBufPtr 64#64 99#64 ⋆
      bytes nvOutBufPtr (List.replicate 64 0))
      ((nvM6MemBytes ++ (List.replicate 4080 0 ++ bytes64 [nvOutBufPtr, 64#64, 99#64] ++
        List.replicate 64 0)).At nvM6CnfPtr) := by
  have hhdr := hdrTailWords_length nvM6SatCfg nvM6SatState
  have hsl : nvM6SatCfg.slack = 3924 := by
    unfold FullCfg.slack nvM6SatCfg nvM6WorkLen fullM6ExtBytes fullFixedBytes valsBytes
      markBytes u32FullBytes fullMinDepthOf
    decide
  have hm_len : nvM6MemBytes.length = 8208 := by
    have h1 : nvM6SatBlockHdr.length = 1152 := by
      simp only [nvM6SatBlockHdr, List.length_append, bytes64_length, hhdr]; decide
    have h2 : nvM6SatBlockBytes.length = 64 := by
      simp only [nvM6SatBlockBytes, List.length_append, List.length_replicate, bytesOf_length,
        nvM6SatState, nvOneLitState, nvOneLitScratch, Ty.bytes, Ty.size,
        List.length_cons, List.length_nil]
    have h3 : nvM6SatBlockU32A.length = 80 := by
      simp only [nvM6SatBlockU32A, List.length_append, List.length_replicate, bytesOf_length,
        nvM6SatState, nvOneLitState, nvOneLitScratch, Ty.bytes, Ty.size]
    have h4 : nvM6SatBlockU32B.length = 80 := by
      simp only [nvM6SatBlockU32B, List.length_append, List.length_replicate, bytesOf_length,
        nvM6SatState, nvOneLitState, nvOneLitScratch, Ty.bytes, Ty.size]
    have h5 : nvM6SatBlockU32C.length = 80 := by
      simp only [nvM6SatBlockU32C, List.length_append, List.length_replicate, bytesOf_length,
        nvM6SatState, nvOneLitState, nvOneLitScratch, Ty.bytes, Ty.size]
    have h6 : nvM6SatBlockWvec.length = 160 := by
      simp only [nvM6SatBlockWvec, List.length_append, List.length_replicate, bytes64_length,
        bytesOf_length, nvM6SatState, nvOneLitState, nvOneLitScratch, Ty.bytes, Ty.size]
    have h7 : nvM6SatBlockTail.length = 348 + 3924 := by
      simp only [nvM6SatBlockTail, List.length_append, List.length_replicate, bytesOf_length, hsl,
        nvM6SatState, nvOneLitState, nvOneLitScratch, Ty.bytes, Ty.size,
        List.length_cons, List.length_nil]
    have ha : nvM6SatArenaBytes.length = 5888 := by
      simp only [nvM6SatArenaBytes, List.length_append, h1, h2, h3, h4, h5, h6, h7]
    have hx : (bytes64 nvM6ExtInitWords).length = 2304 := by
      rw [bytes64_length, nvM6ExtInitWords_len]; decide
    have hs : nvM6SatBytes.length = 16 := by decide
    simp only [nvM6MemBytes, List.length_append, ha, hx, hs]
  have hm1 : (bytes nvM6CnfPtr nvM6SatBytes ⋆
      FullM6HdrMem nvM6SatCfg nvM6ExtInitWords nvM6SatState) (nvM6MemBytes.At nvM6CnfPtr) :=
    nvM6Mem_ok
  have ha : (List.replicate 4080 (0 : UInt8)).length = 4080 ∧
      region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080
        ((List.replicate 4080 (0 : UInt8)).At (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen)) :=
    ⟨List.length_replicate, ⟨List.replicate 4080 0, List.length_replicate, rfl⟩⟩
  have hb := nv_exportOutMem_bytes64 nvOutBufPtr 64#64 99#64
  have hab := nv_join_pair ha hb (by decide) (by decide)
  have hc : (List.replicate 64 (0 : UInt8)).length = 64 ∧
      bytes nvOutBufPtr (List.replicate 64 0)
        ((List.replicate 64 (0 : UInt8)).At nvOutBufPtr) := ⟨List.length_replicate, rfl⟩
  have habc := nv_join_pair hab hc (by decide) (by decide)
  have haddr : nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen =
      nvM6CnfPtr + BitVec.ofNat 64 nvM6MemBytes.length := by rw [hm_len]; decide
  have hsep := nv_sep_append haddr (by rw [hm_len, habc.1]; decide) hm1 habc.2
  rw [List.append_assoc] at hsep ⊢
  exact sep_ac hsep

/-- `16`-byte UNSAT empty-clause DIMACS CNF `"p cnf 2 1\n  0  \n"` for `BUG-CROSS-01` NV. -/
@[expose] def nvM6EmptyClBytes : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 50, 32, 49, 10, 32, 32, 48, 32, 32, 10]

/-- Parsed `CNF Nat` for `nvM6EmptyClBytes`. -/
@[expose] def nvM6EmptyClCnf : CNF Nat := CNF.empty.add CNF.Clause.empty

theorem parseDimacs_nvM6EmptyClBytes :
    parseDimacs nvM6EmptyClBytes = some nvM6EmptyClCnf := by
  have h : (CNF.Clause.ofLiterals ([] : List (Std.Sat.Literal Nat))) = CNF.Clause.empty :=
    CNF.Clause.ext (by simp [CNF.Clause.literals_ofLiterals])
  rw [nvM6EmptyClCnf, ← h]
  rfl

theorem nvM6EmptyClCnf_unsat : nvM6EmptyClCnf.Unsat := by
  intro α
  rw [nvM6EmptyClCnf, CNF.eval_add, CNF.eval_empty, CNF.Clause.eval_empty]
  rfl

/-- Deterministic `1`-unit-clause `FullState` on `nvM6SatCfg` (`"p cnf 2 1\n1 0\n"`). -/
@[expose] def nvM6UnitState : FullState :=
  { core :=
      { nvM6SatState.core with
        vals := [1#8, 0xFF#8, 0#8, 0#8]
        trail_end := 1
        unassigned := 1#64 }
    scratch := nvM6SatState.scratch }

/-- `inconsistent = 1#64` state on `nvM6SatCfg` witnessing `BUG-CROSS-01` fix. -/
@[expose] def nvM6InconsState : FullState :=
  { core :=
      { nvM6SatState.core with
        vals := [0#8, 0#8, 0#8, 0#8]
        trail_end := 0
        unassigned := 2#64
        inconsistent := 1#64 }
    scratch := nvM6SatState.scratch }

private theorem nv_zero_watches_ok {F_cur : List (List Nat)} {k : FullCoreState}
    (hcur : k.cur_vars = 2) (hwv : k.wvec = List.replicate 8 0#32)
    (hwl : k.wlen = 1) : WatchesInv F_cur k := by
  refine ⟨⟨fun l hl => by
      rw [hcur] at hl
      rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;>
        simp [fullWatchOffCore, fullWatchSizeCore, hwv, hwl],
      fun l hl hs => by
        rw [hcur] at hl
        rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;>
          simp [fullWatchSizeCore, hwv] at hs,
      fun l1 _ h1 _ _ hp _ => by
        rw [hcur] at h1
        rcases (by omega : l1 = 0 ∨ l1 = 1 ∨ l1 = 2 ∨ l1 = 3) with rfl | rfl | rfl | rfl <;>
          simp [fullWatchSizeCore, hwv] at hp,
      fun l hl _ hi => by
        rw [hcur] at hl
        rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;>
          simp [fullWatchSizeCore, hwv] at hi⟩,
    fun l hl => by
      rw [hcur] at hl
      rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;>
        · simp [fullWatchOffCore, fullWatchSizeCore, hwv]; exact WatchSliceOk.empty⟩

private theorem nvM6_extScratchOk {s : FullState}
    (hs : s.scratch = nvM6SatState.scratch) : FullExtScratchOk nvM6SatCfg s := by
  refine ⟨fun i hi => Or.inl ?_, by rw [hs]; decide⟩
  rw [hs]
  rcases (by omega :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem nv_arenaRefs_nil {s : FullState} {r : Nat}
    (h0 : s.core.arena_len = 0) (hr : r ∈ fullArenaClauseRefs s) : False := by
  rw [fullArenaClauseRefs, fullArenaClauseRefsCore, h0, fullArenaScanRefs] at hr
  cases hr

private theorem nvUnitCur_not_unsat : ¬ (cnfOfClauses [[0]]).Unsat := by
  intro hu
  have hcl : (cnfClause [0]).Sat (fun _ => true) := by
    rw [CNF.Clause.sat_iff_exists_mem_eq]
    refine ⟨(0, true), ?_, rfl⟩
    rw [← CNF.Clause.mem_literals_iff, cnfClause, List.map_singleton, litToLiteral,
      CNF.Clause.literals_ofLiterals]
    exact List.mem_singleton_self _
  have hsat : (cnfOfClauses [[0]]).Sat (fun _ => true) :=
    CNF.sat_of_all_mem_sat fun cl h => by
      rw [CNF.Internal.mem_iff] at h
      have hl : cl ∈ ([cnfClause [0]] : List (CNF.Clause Nat)) := by
        simpa [cnfOfClauses] using h
      rcases List.mem_singleton.mp hl with rfl
      exact hcl
  exact Bool.false_ne_true ((hu (fun _ => true)).symm.trans ((CNF.sat_def _ _).mp hsat))

private theorem nvM6Unit_lengths : nvM6UnitState.LengthsOk nvM6SatCfg :=
  ⟨{ nvM6Sat_lengths.core_ok with vals_len := rfl, trail_end_le := by decide },
   nvM6Sat_lengths.scratch_ok⟩

private theorem nvM6UnitState_witnessInv :
    FullWitnessInv nvM6SatCfg (shiftDownCnf nvM6SatCnf) [[0]] nvM6UnitState.core := by
  have hcur : nvM6UnitState.core.cur_vars = 2 := rfl
  have hte : nvM6UnitState.core.trail_end = 1 := rfl
  have hcl : nvM6UnitState.core.cur_level = 0 := rfl
  refine
      { ext_sound := ⟨fun cl hcl' l hl => by
            simp only [List.mem_singleton] at hcl'; subst hcl'
            simp only [List.mem_singleton] at hl; subst hl; decide,
          fun hunsat => False.elim (nvUnitCur_not_unsat hunsat)⟩
        inconsistent_sound := fun h => absurd rfl h
        arena := ⟨Or.inl rfl,
          (fun _ hr => nomatch (show _ ∈ ([] : List Nat) from hr)),
          (fun _ hr _ => nomatch (show _ ∈ ([] : List Nat) from hr)),
          (fun _ hr _ _ _ => nomatch (show _ ∈ ([] : List Nat) from hr)),
          (fun _ hr _ => nomatch (show _ ∈ ([] : List Nat) from hr))⟩
        watches := nv_zero_watches_ok hcur rfl rfl
        cur_level_le := by decide
        trail_lits_lt := fun i hi => by
          rw [hte] at hi; obtain rfl : i = 0 := (by omega)
          simp [nvM6UnitState, nvM6SatState, nvOneLitState]
        trail_vars_nodup := fun _ _ hi hj _ => by rw [hte] at hi hj; omega
        vals_domain := fun l hl => by
          rw [hcur] at hl
          rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> decide
        vals_true_iff := fun l hl => by
          rw [hcur] at hl
          rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
          · exact ⟨fun _ => ⟨0, by decide, rfl⟩, fun _ => rfl⟩
          · exact ⟨(fun h => by cases h),
              fun ⟨i, hi, h⟩ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h⟩
          · exact ⟨(fun h => by cases h),
              fun ⟨i, hi, h⟩ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h⟩
          · exact ⟨(fun h => by cases h),
              fun ⟨i, hi, h⟩ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h⟩
        vals_false_iff := fun l hl => by
          rw [hcur] at hl
          rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
          · exact ⟨(fun h => by cases h),
              fun ⟨i, hi, h⟩ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h⟩
          · exact ⟨fun _ => ⟨0, by decide, rfl⟩, fun _ => rfl⟩
          · exact ⟨(fun h => by cases h),
              fun ⟨i, hi, h⟩ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h⟩
          · exact ⟨(fun h => by cases h),
              fun ⟨i, hi, h⟩ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h⟩
        lvl_le := fun i hi => by
          rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
        dec_earliest := fun _ j _ hj _ hp => by
          rw [hte] at hj; obtain rfl : j = 0 := (by omega); exact absurd hp.1 (by decide)
        levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
        level0_sound := fun i hi _ => by
          rw [hte] at hi; obtain rfl : i = 0 := (by omega)
          exact entails_mem_cnfOfClauses (by
            simp [nvM6UnitState, nvM6SatState, nvOneLitState])
        trail_pos_inv := fun i hi => by
          rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
        level0_rsn_none := fun i hi _ => by
          rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
        frame_trail_lt := fun L hL => by
          rw [hcl] at hL; obtain rfl : L = 0 := (by omega); decide
        frame_trail_mono := fun L1 L2 _ hL2 => by
          rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega)
          obtain rfl : L2 = 0 := (by omega); exact Nat.le_refl _
        frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
        frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
        reason_inv := fun i hi hn => by
          rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hn
        reason_lit_mem := fun i hi hn => by
          rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hn }

private theorem nvM6UnitState_sparseInv :
    FullSparseInv nvM6SatCfg (shiftDownCnf nvM6SatCnf) nvM6UnitState := by
  refine ⟨⟨nvM6Unit_lengths, [[0]], nvM6UnitState_witnessInv⟩, ?_,
    fun _ hr => False.elim (nv_arenaRefs_nil rfl hr), nvM6_extScratchOk rfl, rfl⟩
  · refine ⟨fun v hv => by
      change v < 2 at hv; rcases (by omega : v = 0 ∨ v = 1) with rfl | rfl <;> rfl,
      fun l hl => by
        rw [show nvM6SatCfg.max_vars = 2 from rfl] at hl
        rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

private theorem nvM6Incons_lengths : nvM6InconsState.LengthsOk nvM6SatCfg :=
  ⟨{ nvM6Sat_lengths.core_ok with
      vals_len := rfl, trail_end_le := by decide, propagated_le := by decide },
   nvM6Sat_lengths.scratch_ok⟩

private theorem nvM6InconsState_witnessInv :
    FullWitnessInv nvM6SatCfg (shiftDownCnf nvM6EmptyClCnf) [[]] nvM6InconsState.core := by
  have hcur : nvM6InconsState.core.cur_vars = 2 := rfl
  have hte : nvM6InconsState.core.trail_end = 0 := rfl
  have hcl : nvM6InconsState.core.cur_level = 0 := rfl
  refine
      { ext_sound := ⟨(fun cl hcl' _ hl => by
            simp only [List.mem_singleton] at hcl'; subst hcl'; cases hl),
          fun _ => by
            refine CNF.unsat_of_mem_unsat (c := CNF.Clause.empty) ?_ CNF.Clause.unsat_empty
            rw [CNF.Internal.mem_iff]
            have he : shiftDownClause CNF.Clause.empty = CNF.Clause.empty :=
              CNF.Clause.ext (by simp [shiftDownClause, CNF.Clause.literals_ofLiterals])
            simp only [nvM6EmptyClCnf, shiftDownCnf, Array.mem_map]
            exact ⟨CNF.Clause.empty, by simp [CNF.empty, CNF.add], he⟩⟩
        inconsistent_sound := fun _ =>
          unsat_of_entails_nil (entails_mem_cnfOfClauses (by simp))
        arena := ⟨Or.inl rfl,
          (fun _ hr => nomatch (show _ ∈ ([] : List Nat) from hr)),
          (fun _ hr _ => nomatch (show _ ∈ ([] : List Nat) from hr)),
          (fun _ hr _ _ _ => nomatch (show _ ∈ ([] : List Nat) from hr)),
          (fun _ hr _ => nomatch (show _ ∈ ([] : List Nat) from hr))⟩
        watches := nv_zero_watches_ok hcur rfl rfl
        cur_level_le := by decide
        trail_lits_lt := fun _ hi => by rw [hte] at hi; omega
        trail_vars_nodup := fun _ _ hi _ _ => by rw [hte] at hi; omega
        vals_domain := fun l hl => by
          rw [hcur] at hl
          rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> decide
        vals_true_iff := fun l hl => by
          rw [hcur] at hl
          rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;>
            exact ⟨(fun h => by cases h), fun ⟨_, hi, _⟩ => by rw [hte] at hi; omega⟩
        vals_false_iff := fun l hl => by
          rw [hcur] at hl
          rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;>
            exact ⟨(fun h => by cases h), fun ⟨_, hi, _⟩ => by rw [hte] at hi; omega⟩
        lvl_le := fun _ hi => by rw [hte] at hi; omega
        dec_earliest := fun _ _ _ hj _ _ => by rw [hte] at hj; omega
        levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
        level0_sound := fun _ hi _ => by rw [hte] at hi; omega
        trail_pos_inv := fun _ hi => by rw [hte] at hi; omega
        level0_rsn_none := fun _ hi _ => by rw [hte] at hi; omega
        frame_trail_lt := fun L hL => by
          rw [hcl] at hL; obtain rfl : L = 0 := (by omega); decide
        frame_trail_mono := fun L1 L2 _ hL2 => by
          rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega)
          obtain rfl : L2 = 0 := (by omega); exact Nat.le_refl _
        frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
        frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
        reason_inv := fun _ hi _ => by rw [hte] at hi; omega
        reason_lit_mem := fun _ hi _ => by rw [hte] at hi; omega }

private theorem nvM6InconsState_sparseInv :
    FullSparseInv nvM6SatCfg (shiftDownCnf nvM6EmptyClCnf) nvM6InconsState := by
  refine ⟨⟨nvM6Incons_lengths, [[]], nvM6InconsState_witnessInv⟩, ?_,
    fun _ hr => False.elim (nv_arenaRefs_nil rfl hr), nvM6_extScratchOk rfl, rfl⟩
  · refine ⟨fun v hv => by
      change v < 2 at hv; rcases (by omega : v = 0 ∨ v = 1) with rfl | rfl <;> rfl,
      fun l hl => by
        rw [show nvM6SatCfg.max_vars = 2 from rfl] at hl
        rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

/-- Concrete `Mem 64` for `nvM6UnitState` (`FullM6HdrMem` + `nvOutDescPtr` + `64 B` buffer). -/
@[expose] def nvExportUnitMem : Mem 64 :=
  let base := (nvM6MemBytes ++ (List.replicate 4080 0 ++ bytes64 [nvOutBufPtr, 64#64, 99#64] ++
    List.replicate 64 0)).At nvM6CnfPtr
  let m1 := storeMem base i64 (nvM6SatCfg.hdr + 144) 1#64
  let m2 := storeMem m1 i64 (nvM6SatCfg.hdr + 792) 1#64
  storeBytes m2 (nvM6SatCfg.pVals + 2#64) [0, 0]

theorem nvExportUnitMem_sep :
    (bytes nvM6CnfPtr nvM6SatBytes ⋆ FullM6HdrMem nvM6SatCfg nvM6ExtInitWords nvM6UnitState ⋆
      exportOutMem nvOutDescPtr nvOutBufPtr 64#64 99#64 ⋆
      bytes nvOutBufPtr (List.replicate 64 0) ⋆
      region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080) nvExportUnitMem := by
  let base := (nvM6MemBytes ++ (List.replicate 4080 0 ++ bytes64 [nvOutBufPtr, 64#64, 99#64] ++
    List.replicate 64 0)).At nvM6CnfPtr
  have hb0 : (FullM6HdrMem nvM6SatCfg nvM6ExtInitWords nvM6SatState ⋆
      (bytes nvM6CnfPtr nvM6SatBytes ⋆
        region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080 ⋆
        exportOutMem nvOutDescPtr nvOutBufPtr 64#64 99#64 ⋆
        bytes nvOutBufPtr (List.replicate 64 0))) base := sep_ac nv_base_sat_mem_sep
  rw [fullM6HdrMem_iff] at hb0
  have hb : (FullMem nvM6SatCfg nvM6SatState ⋆
      (array64 (nvM6SatCfg.hdr - 2304) nvM6ExtInitWords ⋆
        bytes nvM6CnfPtr nvM6SatBytes ⋆
        region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080 ⋆
        exportOutMem nvOutDescPtr nvOutBufPtr 64#64 99#64 ⋆
        bytes nvOutBufPtr (List.replicate 64 0))) base := sep_ac hb0
  have h1 := (FullArenaTactics.store_full_trail_end 1 (by decide) hb).2
  have h2 := (FullArenaTactics.store_full_unassigned 1#64 h1).2
  have h3 := (FullArenaTactics.store_full_vals (i := 2) 0#8 (by decide) h2).2
  have h4 := (FullArenaTactics.store_full_vals (i := 3) 0#8 (by decide) h3).2
  have heq : nvExportUnitMem =
      storeMem (storeMem (storeMem (storeMem base
        i64 (nvM6SatCfg.hdr + 144) (BitVec.ofNat 64 1)) i64 (nvM6SatCfg.hdr + 792) 1#64)
        i8 (nvM6SatCfg.pVals + 2#64) 0#8) i8 (nvM6SatCfg.pVals + 3#64) 0#8 := by
    simp only [nvExportUnitMem, base, storeBytes, BitVec.add_assoc]; rfl
  have h5 : (FullMem nvM6SatCfg nvM6UnitState ⋆
      (array64 (nvM6SatCfg.hdr - 2304) nvM6ExtInitWords ⋆
        (bytes nvM6CnfPtr nvM6SatBytes ⋆
          region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080 ⋆
          exportOutMem nvOutDescPtr nvOutBufPtr 64#64 99#64 ⋆
          bytes nvOutBufPtr (List.replicate 64 0)))) nvExportUnitMem := by
    rw [heq]
    simpa [nvM6UnitState, nvM6SatState, nvOneLitState, List.set] using sep_ac h4
  rw [← fullM6HdrMem_iff] at h5
  exact sep_ac h5

/-- Concrete `Mem 64` for `nvM6InconsState` (`BUG-CROSS-01` regression witness). -/
@[expose] def nvExportInconsMem : Mem 64 :=
  let base := (nvM6MemBytes ++ (List.replicate 4080 0 ++ bytes64 [nvOutBufPtr, 64#64, 99#64] ++
    List.replicate 64 0)).At nvM6CnfPtr
  let m0 := storeBytes base nvM6CnfPtr nvM6EmptyClBytes
  let m1 := storeMem m0 i64 (nvM6SatCfg.hdr + 144) 0#64
  let m2 := storeMem m1 i64 (nvM6SatCfg.hdr + 792) 2#64
  let m3 := storeMem m2 i64 (nvM6SatCfg.hdr + 1024) 1#64
  storeBytes m3 nvM6SatCfg.pVals [0, 0, 0, 0]

/-- Concrete `Mem 64` for `nvM6SatState` (`export_entry_sat_nv` with `pp = 10`). -/
@[expose] def nvExportSatLoadedMem : Mem 64 :=
  (nvM6MemBytes ++ (List.replicate 4080 0 ++ bytes64 [nvOutBufPtr, 64#64, 99#64] ++
    List.replicate 64 0)).At nvM6CnfPtr

theorem nvExportInconsMem_sep :
    (bytes nvM6CnfPtr nvM6EmptyClBytes ⋆ FullM6HdrMem nvM6SatCfg nvM6ExtInitWords nvM6InconsState ⋆
      exportOutMem nvOutDescPtr nvOutBufPtr 64#64 99#64 ⋆
      bytes nvOutBufPtr (List.replicate 64 0) ⋆
      region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080) nvExportInconsMem := by
  let base := (nvM6MemBytes ++ (List.replicate 4080 0 ++ bytes64 [nvOutBufPtr, 64#64, 99#64] ++
    List.replicate 64 0)).At nvM6CnfPtr
  have hb0 : (bytes nvM6CnfPtr nvM6SatBytes ⋆
      (FullM6HdrMem nvM6SatCfg nvM6ExtInitWords nvM6SatState ⋆
        region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080 ⋆
        exportOutMem nvOutDescPtr nvOutBufPtr 64#64 99#64 ⋆
        bytes nvOutBufPtr (List.replicate 64 0))) base := sep_ac nv_base_sat_mem_sep
  have hb := storeBytes_bytes_frame (bs0 := nvM6SatBytes) (bs1 := nvM6EmptyClBytes)
    (by decide) (by decide) hb0
  have h0 : (FullM6HdrMem nvM6SatCfg nvM6ExtInitWords nvM6SatState ⋆
      (bytes nvM6CnfPtr nvM6EmptyClBytes ⋆
        region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080 ⋆
        exportOutMem nvOutDescPtr nvOutBufPtr 64#64 99#64 ⋆
        bytes nvOutBufPtr (List.replicate 64 0)))
      (storeBytes base nvM6CnfPtr nvM6EmptyClBytes) := sep_ac hb
  rw [fullM6HdrMem_iff] at h0
  have hf : (FullMem nvM6SatCfg nvM6SatState ⋆
      (array64 (nvM6SatCfg.hdr - 2304) nvM6ExtInitWords ⋆
        bytes nvM6CnfPtr nvM6EmptyClBytes ⋆
        region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080 ⋆
        exportOutMem nvOutDescPtr nvOutBufPtr 64#64 99#64 ⋆
        bytes nvOutBufPtr (List.replicate 64 0)))
      (storeBytes base nvM6CnfPtr nvM6EmptyClBytes) := sep_ac h0
  have h1 := (FullArenaTactics.store_full_trail_end 0 (by decide) hf).2
  have h2 := (FullArenaTactics.store_full_unassigned 2#64 h1).2
  have h3 := (FullArenaTactics.store_full_inconsistent 1#64 h2).2
  have h4 := (FullArenaTactics.store_full_vals (i := 0) 0#8 (by decide) h3).2
  have h5 := (FullArenaTactics.store_full_vals (i := 1) 0#8 (by decide) h4).2
  have h6 := (FullArenaTactics.store_full_vals (i := 2) 0#8 (by decide) h5).2
  have h7 := (FullArenaTactics.store_full_vals (i := 3) 0#8 (by decide) h6).2
  let m3 := storeMem (storeMem (storeMem (storeBytes base nvM6CnfPtr nvM6EmptyClBytes)
    i64 (nvM6SatCfg.hdr + 144) (BitVec.ofNat 64 0)) i64 (nvM6SatCfg.hdr + 792) 2#64)
    i64 (nvM6SatCfg.hdr + 1024) 1#64
  have heq : nvExportInconsMem =
      storeMem (storeMem (storeMem (storeMem m3 i8 nvM6SatCfg.pVals 0#8)
        i8 (nvM6SatCfg.pVals + 1#64) 0#8) i8 (nvM6SatCfg.pVals + 2#64) 0#8)
        i8 (nvM6SatCfg.pVals + 3#64) 0#8 := by
    simp only [nvExportInconsMem, m3, base, storeBytes, BitVec.add_assoc]; rfl
  have h8 : (FullMem nvM6SatCfg nvM6InconsState ⋆
      (array64 (nvM6SatCfg.hdr - 2304) nvM6ExtInitWords ⋆
        (bytes nvM6CnfPtr nvM6EmptyClBytes ⋆
          region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080 ⋆
          exportOutMem nvOutDescPtr nvOutBufPtr 64#64 99#64 ⋆
          bytes nvOutBufPtr (List.replicate 64 0)))) nvExportInconsMem := by
    rw [heq]
    simpa [m3, nvM6InconsState, nvM6SatState, nvOneLitState, List.set] using sep_ac h7
  rw [← fullM6HdrMem_iff] at h8; exact sep_ac h8

private theorem exportBinSliceClauses_len2 (wstk : List (BitVec 32)) (l0 p : Nat) :
    ∀ fuel cl, cl ∈ exportBinSliceClauses wstk l0 p fuel → cl.length = 2
  | 0, _, h => by rw [exportBinSliceClauses.eq_1] at h; cases h
  | f + 1, _, h => by
    rw [exportBinSliceClauses.eq_def] at h; dsimp only at h
    split at h
    · split at h
      · rcases List.mem_cons.mp h with rfl | hrest
        · rfl
        · exact exportBinSliceClauses_len2 wstk l0 (p + 1) f _ hrest
      · exact exportBinSliceClauses_len2 wstk l0 (p + 1) f _ h
    · cases f with
      | zero => cases h
      | succ f' => exact exportBinSliceClauses_len2 wstk l0 (p + 2) f' _ h

private theorem nv2_exportStateBytes_bounds {k : FullCoreState} {F0 : CNF Nat}
    {F_cur : List (List Nat)}
    (hlen : k.LengthsOk nvM6SatCfg) (hw : FullWitnessInv nvM6SatCfg F0 F_cur k)
    (hl0 : k.cur_level = 0) (hcv : k.cur_vars = 2) (hinc : k.inconsistent = 0#64)
    (harl : k.arena_len = 0) (_hwln : k.wlen = 1) :
    exportStateMv k < dimacsBound ∧ (exportStateClauses k).length < dimacsBound ∧
      (exportStateBytes k).length ≤ 64 := by
  have hmv_eq : exportStateMv k = 2 := by simp [exportStateMv, hinc, hcv]
  have htr_len : (exportTrailUnitClauses k).length ≤ 2 := by
    rw [exportTrailUnitClauses_length hlen]; have := hlen.trail_end_le
    rw [hcv] at this
    omega
  have hbin_len : (exportBinClauses k).length ≤ 1 := by
    have := (exportBinClauses_props hlen hw.watches).1; omega
  have har_nil : exportArenaClauses k = [] := by
    have h0 := (exportArenaClauses_props hlen hw.arena).1; rw [harl] at h0
    exact List.length_eq_zero_iff.mp (by omega)
  have hcl_eq : exportStateClauses k = exportTrailUnitClauses k ++ exportBinClauses k := by
    simp [exportStateClauses, hinc, har_nil]
  have hcl_lt : (exportStateClauses k).length < dimacsBound := by
    rw [hcl_eq, List.length_append]; unfold dimacsBound; omega
  have hmv_lt : exportStateMv k < dimacsBound := by rw [hmv_eq]; unfold dimacsBound; omega
  have hlit_le : ∀ l, l < 4 → (emitDimacsLitBytes l).length ≤ 3 := fun l hl => by
    rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> decide
  have hcl_le : ∀ cl : List Nat, (∀ l ∈ cl, l < 4) →
      (emitDimacsClauseBytes cl).length ≤ 3 * cl.length + 2 := by
    intro cl hls
    unfold emitDimacsClauseBytes
    induction cl with
    | nil => simp
    | cons l rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
      have hl3 := hlit_le l (hls l List.mem_cons_self)
      have ihr := ih (fun x hx => hls x (List.mem_cons_of_mem _ hx))
      simp only [List.length_nil] at ihr ⊢
      omega
  have hsum_le : ∀ (bound : Nat) (cs : List (List Nat)),
      (∀ cl ∈ cs, (emitDimacsClauseBytes cl).length ≤ bound) →
      (cs.flatMap emitDimacsClauseBytes).length ≤ bound * cs.length := by
    intro bound cs hcs
    induction cs with
    | nil => simp
    | cons c rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have h1 := hcs c List.mem_cons_self
      have h2 := ih (fun x hx => hcs x (List.mem_cons_of_mem _ hx))
      rw [Nat.mul_succ]; omega
  have htr_bytes : ((exportTrailUnitClauses k).flatMap emitDimacsClauseBytes).length ≤ 10 := by
    have hb := hsum_le 5 (exportTrailUnitClauses k) fun cl hcl => by
      have h1 : cl.length = 1 := by
        unfold exportTrailUnitClauses at hcl; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hcl; rfl
      have h2 := hcl_le cl (fun l hl => by
        have := (exportTrailUnitClauses_sound hlen hw hl0 cl hcl).1 l hl; omega)
      omega
    omega
  have hbin_bytes : ((exportBinClauses k).flatMap emitDimacsClauseBytes).length ≤ 8 := by
    have hb := hsum_le 8 (exportBinClauses k) fun cl hcl => by
      have h1 : cl.length = 2 := by
        unfold exportBinClauses at hcl; obtain ⟨_, _, hm⟩ := List.mem_flatMap.mp hcl
        exact exportBinSliceClauses_len2 _ _ _ _ _ hm
      have h2 := hcl_le cl (fun l hl => by
        have := ((exportBinClauses_props hlen hw.watches).2.2 cl hcl).1 l hl; omega)
      omega
    omega
  have hhdr_len :
      (emitDimacsHdrBytes (exportStateMv k) (exportStateClauses k).length).length ≤ 10 := by
    unfold emitDimacsHdrBytes dimacsHeaderPrefix
    rw [natToBytes_of_lt_10 (by omega),
      natToBytes_of_lt_10 (by rw [hcl_eq, List.length_append]; omega)]
    simp
  refine ⟨hmv_lt, hcl_lt, ?_⟩
  unfold exportStateBytes emitDimacsBytes
  rw [hcl_eq, List.length_append, List.flatMap_append, List.length_append, List.length_append]
  rw [hcl_eq, List.length_append] at hhdr_len
  omega

/-- Deterministic preprocess-hook environment on `nvM6SatCfg` linking REAL `exportCnfEntryEnv`. -/
@[expose] def mkWitnessPreEnv (code : BitVec 64) (st : FullState) : Env :=
  fun f as rs xs m Q X =>
    if h : f = "full_preprocess_m6" ∧ as = [i64] ∧ rs = [i64] then
      specCast h.2.1 h.2.2 (fun (h_arg, ()) m0 Q0 _ =>
        ∃ R0 : Mem 64 → Prop, h_arg = nvM6SatCfg.hdr ∧
          (FullM6HdrMem nvM6SatCfg nvM6ExtInitWords st ⋆ R0) m0 ∧
          Q0 (code, ()) m0) xs m Q X
    else exportCnfEntryEnv f as rs xs m Q X

/-- Deterministic `full_parse_body_m6`-hook environment on `nvM6SatCfg`. -/
@[expose] def mkWitnessEnv (code : BitVec 64) (cnfBs : List UInt8) (st : FullState) : Env :=
  fun f as rs xs m Q X =>
    if h : f = "full_parse_body_m6" ∧ as = [i64, i64] ∧ rs = [i64] then
      specCast h.2.1 h.2.2 (fun (h_arg, cend, ()) m0 Q0 _ =>
        ∃ R0 : Mem 64 → Prop, h_arg = nvM6SatCfg.hdr ∧
          cend = nvM6CnfPtr + BitVec.ofNat 64 cnfBs.length ∧
          (bytes nvM6CnfPtr cnfBs ⋆ FullMem nvM6SatCfg st ⋆ R0) m0 ∧
          Q0 (1#64, ()) m0) xs m Q X
    else mkWitnessPreEnv code st f as rs xs m Q X

private theorem mkWitnessEnv_parse (code : BitVec 64) (cnfBs : List UInt8) (st : FullState) :
    mkWitnessEnv code cnfBs st "full_parse_body_m6" [i64, i64] [i64] =
      (fun (h_arg, cend, ()) m0 Q0 _ =>
        ∃ R0 : Mem 64 → Prop, h_arg = nvM6SatCfg.hdr ∧
          cend = nvM6CnfPtr + BitVec.ofNat 64 cnfBs.length ∧
          (bytes nvM6CnfPtr cnfBs ⋆ FullMem nvM6SatCfg st ⋆ R0) m0 ∧
          Q0 (1#64, ()) m0) := by
  funext ⟨a1, a2, _⟩ m Q X; simp [mkWitnessEnv, specCast]

private theorem mkWitnessEnv_pre (code : BitVec 64) (cnfBs : List UInt8) (st : FullState) :
    mkWitnessEnv code cnfBs st "full_preprocess_m6" [i64] [i64] =
      (fun (h_arg, ()) m0 Q0 _ =>
        ∃ R0 : Mem 64 → Prop, h_arg = nvM6SatCfg.hdr ∧
          (FullM6HdrMem nvM6SatCfg nvM6ExtInitWords st ⋆ R0) m0 ∧
          Q0 (code, ()) m0) := by
  funext ⟨a1, _⟩ m Q X; simp [mkWitnessEnv, mkWitnessPreEnv, specCast]

private theorem mkWitnessEnv_triv (code : BitVec 64) (cnfBs : List UInt8) (st : FullState) :
    mkWitnessEnv code cnfBs st "kissat_emit_trivial_cnf_bytes" [i64, i64, i64, i64] [i64] =
      exportCnfEntryEnv "kissat_emit_trivial_cnf_bytes" [i64, i64, i64, i64] [i64] := by
  funext a m Q X; simp [mkWitnessEnv, mkWitnessPreEnv]

private theorem mkWitnessEnv_cnf_bytes (code : BitVec 64) (cnfBs : List UInt8) (st : FullState) :
    mkWitnessEnv code cnfBs st "kissat_export_cnf_bytes" [i64, i64, i64, i64] [i64] =
      exportCnfEntryEnv "kissat_export_cnf_bytes" [i64, i64, i64, i64] [i64] := by
  funext a m Q X; simp [mkWitnessEnv, mkWitnessPreEnv]

private theorem nv_loaded_step_to_branch {code : BitVec 64} {cnfBs : List UInt8}
    {st : FullState} {m0 : Mem 64} {Q : Post [i64]}
    (hm0 : (bytes nvM6CnfPtr cnfBs ⋆ FullM6HdrMem nvM6SatCfg nvM6ExtInitWords st ⋆
      exportOutMem nvOutDescPtr nvOutBufPtr 64#64 99#64 ⋆ bytes nvOutBufPtr (List.replicate 64 0) ⋆
      region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080) m0)
    (hcont : ∀ m2,
      (FullMem nvM6SatCfg st ⋆ bytes nvOutBufPtr (List.replicate 64 0) ⋆
        cell64 (nvOutDescPtr + 16#64) 99#64 ⋆
        (bytes nvM6CnfPtr cnfBs ⋆ array64 (nvM6SatCfg.hdr - 2304) nvM6ExtInitWords ⋆
          cell64 nvOutDescPtr nvOutBufPtr ⋆ cell64 (nvOutDescPtr + 8#64) 64#64 ⋆
          region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080)) m2 →
      wp (mkWitnessEnv code cnfBs st) Q (fun _ _ _ _ => False)
        (Expr.let_
          { sig := [i64, i64]
            code := OpCode.cmp CmpOp.eq i64 Ty.bool (by simp)
            args := (Arg.var code, Arg.imm 20#64, ()) } fun pb20 =>
          Expr.jnz (Arg.var pb20.fst)
            (Expr.call (as := [i64, i64, i64, i64]) (bs := [i64])
              "kissat_emit_trivial_cnf_bytes"
              (Arg.var nvOutBufPtr, Arg.var 64#64, Arg.var (nvOutDescPtr + 16#64),
                Arg.imm 1#64, ())
              (fun r => Expr.ret (Arg.var r.fst, ())))
            (Expr.let_
              { sig := [i64, i64]
                code := OpCode.cmp CmpOp.eq i64 Ty.bool (by simp)
                args := (Arg.var code, Arg.imm 10#64, ()) } fun pb10 =>
              Expr.jnz (Arg.var pb10.fst)
                (Expr.call (as := [i64, i64, i64, i64]) (bs := [i64])
                  "kissat_emit_trivial_cnf_bytes"
                  (Arg.var nvOutBufPtr, Arg.var 64#64, Arg.var (nvOutDescPtr + 16#64),
                    Arg.imm 0#64, ())
                  (fun r => Expr.ret (Arg.var r.fst, ())))
                (Expr.let_
                  { sig := [i64, i64]
                    code := OpCode.cmp CmpOp.ne i64 Ty.bool (by simp)
                    args := (Arg.var code, Arg.imm 1#64, ()) } fun pne1 =>
                  Expr.jnz (Arg.var pne1.fst) (Expr.ret (Arg.imm 0#64, ()))
                    (Expr.call (as := [i64, i64, i64, i64]) (bs := [i64])
                      "kissat_export_cnf_bytes"
                      (Arg.var nvM6SatCfg.hdr, Arg.var nvOutBufPtr, Arg.var 64#64,
                        Arg.var (nvOutDescPtr + 16#64), ())
                      (fun p =>
                        Expr.let_
                          { sig := [i64, i64]
                            code := OpCode.cmp CmpOp.eq i64 Ty.bool (by simp)
                            args := (Arg.var p.fst, Arg.imm 0#64, ()) } fun pb =>
                          Expr.jnz (Arg.var pb.fst)
                            (Expr.group (fun _Js => Blocks.cons
                              (fun (_ : Tup Val []) => Expr.ret (Arg.imm 0#64, ())) Blocks.nil)
                              fun Js =>
                              Expr.let_
                                { sig := [i64, i64]
                                  code := OpCode.add i64
                                  args := (Arg.var nvOutDescPtr, Arg.imm 16#64, ()) } fun p1 =>
                                Expr.load i64 (Arg.var p1.fst) fun ld2 =>
                                  Expr.let_
                                    { sig := [i64, i64]
                                      code := OpCode.cmp CmpOp.ule i64 Ty.bool (by simp)
                                      args := (Arg.var ld2, Arg.var 64#64, ()) } fun pc =>
                                    Expr.jnz (Arg.var pc.fst)
                                      (Expr.let_
                                        { sig := [i64, i64]
                                          code := OpCode.add i64
                                          args := (Arg.var nvOutDescPtr, Arg.imm 16#64, ()) }
                                        fun p2 =>
                                          Expr.store (t := i64) (Arg.imm 0#64) (Arg.var p2.fst)
                                            (Expr.jump Js.fst ()))
                                      (Expr.jump Js.fst ()))
                            (Expr.let_
                              { sig := [i64, i64]
                                code := OpCode.add i64
                                args := (Arg.var nvM6SatCfg.hdr, Arg.imm 1024#64, ()) } fun pi =>
                              Expr.load i64 (Arg.var pi.fst) fun linc =>
                                Expr.let_
                                  { sig := [i64, i64]
                                    code := OpCode.cmp CmpOp.ne i64 Ty.bool (by simp)
                                    args := (Arg.var linc, Arg.imm 0#64, ()) } fun pne =>
                                  Expr.jnz (Arg.var pne.fst) (Expr.ret (Arg.imm 20#64, ()))
                                    (Expr.ret (Arg.imm 1#64, ())))))))) m2) :
    Func.wp (mkWitnessEnv code cnfBs st) kissat_simplify_export_loaded_body
      (nvM6SatCfg.hdr, nvM6CnfPtr + BitVec.ofNat 64 cnfBs.length, nvOutDescPtr, ()) m0
      Q (fun _ _ _ _ => False) := by
  unfold Func.wp kissat_simplify_export_loaded_body; dsimp only
  have hm0' : (bytes nvM6CnfPtr cnfBs ⋆ FullMem nvM6SatCfg st ⋆
      (array64 (nvM6SatCfg.hdr - 2304) nvM6ExtInitWords ⋆
        exportOutMem nvOutDescPtr nvOutBufPtr 64#64 99#64 ⋆
        bytes nvOutBufPtr (List.replicate 64 0) ⋆
        region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080)) m0 := by
    have h : (FullM6HdrMem nvM6SatCfg nvM6ExtInitWords st ⋆
        (bytes nvM6CnfPtr cnfBs ⋆
          exportOutMem nvOutDescPtr nvOutBufPtr 64#64 99#64 ⋆
          bytes nvOutBufPtr (List.replicate 64 0) ⋆
          region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080)) m0 := sep_ac hm0
    rw [fullM6HdrMem_iff] at h; exact sep_ac h
  refine wp_call_of_spec _ _ ?_
  rw [mkWitnessEnv_parse]
  refine ⟨_, rfl, rfl, hm0', ?_⟩
  c0_hsteps_nogrp
  have hld_ptr : loadVal m0 i64 nvOutDescPtr = some nvOutBufPtr :=
    loadVal_cell64 (R := bytes nvM6CnfPtr cnfBs ⋆
      FullM6HdrMem nvM6SatCfg nvM6ExtInitWords st ⋆
      cell64 (nvOutDescPtr + 8#64) 64#64 ⋆ cell64 (nvOutDescPtr + 16#64) 99#64 ⋆
      bytes nvOutBufPtr (List.replicate 64 0) ⋆
      region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080)
      (by unfold exportOutMem at hm0; exact sep_ac hm0)
  have hld_cap : loadVal m0 i64 (nvOutDescPtr + 8#64) = some 64#64 :=
    loadVal_cell64 (R := bytes nvM6CnfPtr cnfBs ⋆
      FullM6HdrMem nvM6SatCfg nvM6ExtInitWords st ⋆
      cell64 nvOutDescPtr nvOutBufPtr ⋆ cell64 (nvOutDescPtr + 16#64) 99#64 ⋆
      bytes nvOutBufPtr (List.replicate 64 0) ⋆
      region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080)
      (by unfold exportOutMem at hm0; exact sep_ac hm0)
  refine wp_load_of hld_ptr ?_
  c0_hsteps_nogrp
  refine wp_load_of hld_cap ?_
  c0_hsteps_nogrp
  refine wp_call_of_spec _ _ ?_
  rw [mkWitnessEnv_pre]
  refine ⟨bytes nvM6CnfPtr cnfBs ⋆ exportOutMem nvOutDescPtr nvOutBufPtr 64#64 99#64 ⋆
      bytes nvOutBufPtr (List.replicate 64 0) ⋆
      region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080,
    rfl, sep_ac hm0, ?_⟩
  have hm2_exp : (FullMem nvM6SatCfg st ⋆ bytes nvOutBufPtr (List.replicate 64 0) ⋆
      cell64 (nvOutDescPtr + 16#64) 99#64 ⋆
      (bytes nvM6CnfPtr cnfBs ⋆ array64 (nvM6SatCfg.hdr - 2304) nvM6ExtInitWords ⋆
        cell64 nvOutDescPtr nvOutBufPtr ⋆ cell64 (nvOutDescPtr + 8#64) 64#64 ⋆
        region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080)) m0 := by
    unfold exportOutMem at hm0'; exact sep_ac hm0'
  exact hcont m0 hm2_exp

private theorem nvM6SatCnf_varsPos : CnfVarsPos nvM6SatCnf := by
  intro cl hcl lit hlit
  rw [CNF.Internal.mem_iff] at hcl
  have h1 : cl ∈ ([CNF.Clause.ofLiterals [(1, true), (2, true)]] : List (CNF.Clause Nat)) := by
    simpa [nvM6SatCnf, CNF.empty, CNF.add] using hcl
  rcases List.mem_singleton.mp h1 with rfl
  rw [CNF.Clause.literals_ofLiterals] at hlit
  rcases List.mem_cons.mp hlit with rfl | h2
  · decide
  · rcases List.mem_singleton.mp h2 with rfl; decide

/-- Concrete Witness 3 (`XPost := False`, `<= std3`): `kissat_simplify_export_loaded` on
`nvExportUnitMem` (`nvM6UnitState` on `"p cnf 2 1\n1 2 0\n"`) deterministically runs REAL
`kissat_export_cnf_bytes` (`exportCnfEntryEnv`), returning **`r = 1#64`**, writing
`0 < written ≤ 64` valid simplified DIMACS bytes parsing back to `some cnfOut`
(`cnfOut.Unsat → nvM6SatCnf.Unsat`). -/
theorem export_entry_unit_unknown_nv :
    Func.wp (mkWitnessEnv 1#64 nvM6SatBytes nvM6UnitState) kissat_simplify_export_loaded_body
      (nvM6SatCfg.hdr, nvM6CnfPtr + BitVec.ofNat 64 nvM6SatBytes.length, nvOutDescPtr, ())
      nvExportUnitMem
      (fun (r, ()) m' =>
        ∃ (s' : FullState) (outBytes : List UInt8) (written : Nat) (cnfOut : CNF Nat),
          r = 1#64 ∧ 0 < written ∧ written ≤ 64 ∧ outBytes.length = written ∧
          parseDimacs outBytes = some cnfOut ∧ (cnfOut.Unsat → nvM6SatCnf.Unsat) ∧
          (bytes nvM6CnfPtr nvM6SatBytes ⋆ FullM6HdrMem nvM6SatCfg nvM6ExtInitWords s' ⋆
            exportOutMem nvOutDescPtr nvOutBufPtr 64#64 (BitVec.ofNat 64 written) ⋆
            bytes nvOutBufPtr (outBytes ++ List.replicate (64 - written) 0) ⋆
            region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080) m')
      (fun _ _ _ _ => False) := by
  refine nv_loaded_step_to_branch nvExportUnitMem_sep fun m2 hm2_exp => ?_
  c0_hsteps_nogrp
  refine wp_call_of_spec _ _ ?_
  rw [mkWitnessEnv_cnf_bytes]
  refine exportCnfEntryEnv_cnf_bytes _ _ _ _ ?_
  refine ⟨nvM6SatCfg, shiftDownCnf nvM6SatCnf, [[0]], nvM6UnitState, nvOutBufPtr,
    nvOutDescPtr + 16#64, 99#64, List.replicate 64 0, _, rfl, by decide, nvM6Unit_lengths,
    nvM6UnitState_witnessInv, hm2_exp, fun ok s3 outBytes written m3 hlen3 hw3 hl03 hcv3
      hinc3 _ harl3 _ _ hwln3 _ _ hok hwr_lt hok0 hok1 => ?_⟩
  have hcv2 : s3.core.cur_vars = 2 := by rw [hcv3]; rfl
  have hinc0 : s3.core.inconsistent = 0#64 := by rw [hinc3]; rfl
  have harl0 : s3.core.arena_len = 0 := by rw [harl3]; rfl
  have hwln1 : s3.core.wlen = 1 := by rw [hwln3]; rfl
  have ⟨hmv_lt, hcl_lt, hbs_le⟩ :=
    nv2_exportStateBytes_bounds hlen3.core_ok hw3 hl03 hcv2 hinc0 harl0 hwln1
  c0_hsteps_nogrp
  · exfalso
    have ⟨_, hbd, _⟩ := hok0 ‹_›
    have ⟨hweq, hlt64⟩ := hbd hmv_lt hcl_lt
    simp only [List.length_replicate] at hlt64
    omega
  · have hok1' : ok = 1#64 := hok.elim (fun h0 => absurd h0 ‹_›) id
    obtain ⟨hout_eq, hwr_eq, hwr_le, ⟨cnfOut, hpOut, _, huOut⟩, hm3⟩ := hok1 hok1'
    have hm3_f : (FullMem nvM6SatCfg s3 ⋆
        (bytes nvOutBufPtr (outBytes ++ (List.replicate 64 (0 : UInt8)).drop written) ⋆
          cell64 (nvOutDescPtr + 16#64) (BitVec.ofNat 64 written) ⋆
          bytes nvM6CnfPtr nvM6SatBytes ⋆
          array64 (nvM6SatCfg.hdr - 2304) nvM6ExtInitWords ⋆ cell64 nvOutDescPtr nvOutBufPtr ⋆
          cell64 (nvOutDescPtr + 8#64) 64#64 ⋆
          region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080)) m3 := sep_ac hm3
    refine wp_load_of (FullArenaTactics.load_full_inconsistent hm3_f) ?_
    c0_hsteps_nogrp
    have hwr_pos : 0 < written := by rw [hwr_eq, hout_eq]; exact exportStateBytes_len_pos s3.core
    have hwr_le64 : written ≤ 64 := by simpa using hwr_le
    have hu_dim : cnfOut.Unsat → nvM6SatCnf.Unsat :=
      fun hu => shiftDownCnf_unsat nvM6SatCnf_varsPos (huOut hu)
    have hm3_m6 : (bytes nvM6CnfPtr nvM6SatBytes ⋆
        FullM6HdrMem nvM6SatCfg nvM6ExtInitWords s3 ⋆
        exportOutMem nvOutDescPtr nvOutBufPtr 64#64 (BitVec.ofNat 64 written) ⋆
        bytes nvOutBufPtr (outBytes ++ List.replicate (64 - written) 0) ⋆
        region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080) m3 := by
      unfold exportOutMem
      have h : (FullMem nvM6SatCfg s3 ⋆
          (array64 (nvM6SatCfg.hdr - 2304) nvM6ExtInitWords ⋆
            (bytes nvM6CnfPtr nvM6SatBytes ⋆
              cell64 nvOutDescPtr nvOutBufPtr ⋆ cell64 (nvOutDescPtr + 8#64) 64#64 ⋆
              cell64 (nvOutDescPtr + 16#64) (BitVec.ofNat 64 written) ⋆
              bytes nvOutBufPtr (outBytes ++ (List.replicate 64 (0 : UInt8)).drop written) ⋆
              region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080))) m3 := sep_ac hm3
      rw [← fullM6HdrMem_iff, List.drop_replicate] at h
      exact sep_ac h
    exact ⟨s3, outBytes, written, cnfOut, rfl, hwr_pos, hwr_le64, hwr_eq.symm, hpOut, hu_dim,
      hm3_m6⟩

/-- Concrete Witness 4 (`XPost := False`, `<= std3`): `kissat_simplify_export_loaded` on
`nvExportInconsMem` (`nvM6InconsState` with `inconsistent = 1#64` on `pp = 1#64`, `BUG-CROSS-01`)
deterministically returns **`r = 20#64`**, emits `unsatDimacsBytes` (`"p cnf 0 1\n0\n"`, `12 B`),
and certifies `nvM6EmptyClCnf.Unsat`. -/
theorem export_entry_inconsistent_nv :
    Func.wp (mkWitnessEnv 1#64 nvM6EmptyClBytes nvM6InconsState) kissat_simplify_export_loaded_body
      (nvM6SatCfg.hdr, nvM6CnfPtr + BitVec.ofNat 64 nvM6EmptyClBytes.length, nvOutDescPtr, ())
      nvExportInconsMem
      (fun (r, ()) m' =>
        ∃ s' : FullState,
          r = 20#64 ∧ nvM6EmptyClCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6EmptyClBytes ⋆
            FullM6HdrMem nvM6SatCfg nvM6ExtInitWords s' ⋆
            exportOutMem nvOutDescPtr nvOutBufPtr 64#64 12#64 ⋆
            bytes nvOutBufPtr (unsatDimacsBytes ++ List.replicate 52 0) ⋆
            region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080) m')
      (fun _ _ _ _ => False) := by
  refine nv_loaded_step_to_branch nvExportInconsMem_sep fun m2 hm2_exp => ?_
  c0_hsteps_nogrp
  refine wp_call_of_spec _ _ ?_
  rw [mkWitnessEnv_cnf_bytes]
  refine exportCnfEntryEnv_cnf_bytes _ _ _ _ ?_
  refine ⟨nvM6SatCfg, shiftDownCnf nvM6EmptyClCnf, [[]], nvM6InconsState, nvOutBufPtr,
    nvOutDescPtr + 16#64, 99#64, List.replicate 64 0, _, rfl, by decide, nvM6Incons_lengths,
    nvM6InconsState_witnessInv, hm2_exp, fun ok s3 outBytes written m3 _ _ _ _
      hinc3 _ _ _ _ _ _ _ hok _ hok0 hok1 => ?_⟩
  have hinc1 : s3.core.inconsistent = 1#64 := by rw [hinc3]; rfl
  have hinc_ne : s3.core.inconsistent ≠ 0#64 := by rw [hinc1]; decide
  have hbs : exportStateBytes s3.core = unsatDimacsBytes :=
    exportStateBytes_inconsistent_eq hinc_ne
  c0_hsteps_nogrp
  · exfalso
    have ⟨_, hbd, _⟩ := hok0 ‹_›
    have hmv0 : exportStateMv s3.core < dimacsBound := by
      simp [exportStateMv, hinc_ne, dimacsBound]
    have hnc1 : (exportStateClauses s3.core).length < dimacsBound := by
      simp [exportStateClauses, hinc_ne, dimacsBound]
    have ⟨hweq, hlt64⟩ := hbd hmv0 hnc1
    rw [hbs, unsatDimacsBytes_len] at hweq
    simp only [List.length_replicate] at hlt64
    omega
  · have hok1' : ok = 1#64 := hok.elim (fun h0 => absurd h0 ‹_›) id
    obtain ⟨hout_eq, hwr_eq, _, _, hm3⟩ := hok1 hok1'
    have hm3_f : (FullMem nvM6SatCfg s3 ⋆
        (bytes nvOutBufPtr (outBytes ++ (List.replicate 64 (0 : UInt8)).drop written) ⋆
          cell64 (nvOutDescPtr + 16#64) (BitVec.ofNat 64 written) ⋆
          bytes nvM6CnfPtr nvM6EmptyClBytes ⋆
          array64 (nvM6SatCfg.hdr - 2304) nvM6ExtInitWords ⋆ cell64 nvOutDescPtr nvOutBufPtr ⋆
          cell64 (nvOutDescPtr + 8#64) 64#64 ⋆
          region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080)) m3 := sep_ac hm3
    refine wp_load_of (FullArenaTactics.load_full_inconsistent hm3_f) ?_
    c0_hsteps_nogrp
    have h12 : written = 12 := by rw [hwr_eq, hout_eq, hbs, unsatDimacsBytes_len]
    have hm3_m6 : (bytes nvM6CnfPtr nvM6EmptyClBytes ⋆
        FullM6HdrMem nvM6SatCfg nvM6ExtInitWords s3 ⋆
        exportOutMem nvOutDescPtr nvOutBufPtr 64#64 12#64 ⋆
        bytes nvOutBufPtr (unsatDimacsBytes ++ List.replicate 52 0) ⋆
        region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080) m3 := by
      unfold exportOutMem
      have h : (FullMem nvM6SatCfg s3 ⋆
          (array64 (nvM6SatCfg.hdr - 2304) nvM6ExtInitWords ⋆
            (bytes nvM6CnfPtr nvM6EmptyClBytes ⋆
              cell64 nvOutDescPtr nvOutBufPtr ⋆ cell64 (nvOutDescPtr + 8#64) 64#64 ⋆
              cell64 (nvOutDescPtr + 16#64) (BitVec.ofNat 64 written) ⋆
              bytes nvOutBufPtr (outBytes ++ (List.replicate 64 (0 : UInt8)).drop written) ⋆
              region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080))) m3 := sep_ac hm3
      rw [← fullM6HdrMem_iff, h12, hout_eq, hbs, List.drop_replicate] at h
      exact sep_ac h
    exact ⟨s3, rfl, nvM6EmptyClCnf_unsat, hm3_m6⟩

/-- Concrete Witness 5 (`XPost := False`, `<= std3`): `kissat_simplify_export_loaded` on
`nvExportSatLoadedMem` (`nvM6SatState` with `pp = 10#64`) deterministically returns
**`r = 10#64`**, emits `satEmptyDimacsBytes` (`"p cnf 0 0\n"`, `10 B`), parses back to
`some CNF.empty`, and certifies `¬ nvM6SatCnf.Unsat`. -/
theorem export_entry_sat_nv :
    Func.wp (mkWitnessEnv 10#64 nvM6SatBytes nvM6SatState) kissat_simplify_export_loaded_body
      (nvM6SatCfg.hdr, nvM6CnfPtr + BitVec.ofNat 64 nvM6SatBytes.length, nvOutDescPtr, ())
      nvExportSatLoadedMem
      (fun (r, ()) m' =>
        r = 10#64 ∧ ¬ nvM6SatCnf.Unsat ∧
        (∃ cnfOut : CNF Nat, parseDimacs satEmptyDimacsBytes = some cnfOut ∧
          (cnfOut.Unsat → nvM6SatCnf.Unsat)) ∧
        (bytes nvM6CnfPtr nvM6SatBytes ⋆
          FullM6HdrMem nvM6SatCfg nvM6ExtInitWords nvM6SatState ⋆
          exportOutMem nvOutDescPtr nvOutBufPtr 64#64 10#64 ⋆
          bytes nvOutBufPtr (satEmptyDimacsBytes ++ List.replicate 54 0) ⋆
          region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080) m')
      (fun _ _ _ _ => False) := by
  refine nv_loaded_step_to_branch (sep_ac nv_base_sat_mem_sep) fun m2 hm2_exp => ?_
  c0_hsteps_nogrp
  refine wp_call_of_spec _ _ ?_
  rw [mkWitnessEnv_triv]
  refine exportCnfEntryEnv_triv _ _ _ _ ?_
  have hm2_tr : (bytes nvOutBufPtr (List.replicate 64 0) ⋆ cell64 (nvOutDescPtr + 16#64) 99#64 ⋆
      (FullMem nvM6SatCfg nvM6SatState ⋆ bytes nvM6CnfPtr nvM6SatBytes ⋆
        array64 (nvM6SatCfg.hdr - 2304) nvM6ExtInitWords ⋆
        cell64 nvOutDescPtr nvOutBufPtr ⋆ cell64 (nvOutDescPtr + 8#64) 64#64 ⋆
        region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080)) m2 := sep_ac hm2_exp
  refine ⟨nvOutBufPtr, nvOutDescPtr + 16#64, 99#64, 0#64, List.replicate 64 0, _,
    rfl, by decide, hm2_tr, fun r m3 h0 hpos => ?_⟩
  have h10_lt : 10 ≤ (List.replicate 64 (0 : UInt8)).length := by decide
  have hr10 : r = 10#64 := (hpos h10_lt).1
  have hm3 := (hpos h10_lt).2
  have hm3_m6 : (bytes nvM6CnfPtr nvM6SatBytes ⋆
      FullM6HdrMem nvM6SatCfg nvM6ExtInitWords nvM6SatState ⋆
      exportOutMem nvOutDescPtr nvOutBufPtr 64#64 10#64 ⋆
      bytes nvOutBufPtr (satEmptyDimacsBytes ++ List.replicate 54 0) ⋆
      region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080) m3 := by
    unfold exportOutMem
    have h : (FullMem nvM6SatCfg nvM6SatState ⋆
        (array64 (nvM6SatCfg.hdr - 2304) nvM6ExtInitWords ⋆
          (bytes nvM6CnfPtr nvM6SatBytes ⋆
            cell64 nvOutDescPtr nvOutBufPtr ⋆ cell64 (nvOutDescPtr + 8#64) 64#64 ⋆
            cell64 (nvOutDescPtr + 16#64) 10#64 ⋆
            bytes nvOutBufPtr
              (satEmptyDimacsBytes ++ (List.replicate 64 (0 : UInt8)).drop 10) ⋆
            region (nvM6SatWorkPtr + BitVec.ofNat 64 nvM6WorkLen) 4080))) m3 := sep_ac hm3
    rw [← fullM6HdrMem_iff, List.drop_replicate] at h
    exact sep_ac h
  c0_hsteps_nogrp
  refine ⟨hr10, nvM6SatCnf_not_unsat, ⟨kissatCnfToDimacs [], parseDimacs_satEmptyDimacsBytes,
    fun hunsat => False.elim <| Bool.false_ne_true
      ((hunsat (fun _ => true)).symm.trans (CNF.eval_empty _))⟩, hm3_m6⟩

end

end LeanQbe.T.Examples.Kissat.ExportCnfEntryProof
