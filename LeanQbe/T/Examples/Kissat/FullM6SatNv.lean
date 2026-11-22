module

public import LeanQbe.T.Examples.Kissat.FullM6SatSound
public import LeanQbe.T.Examples.Kissat.FullProof
public import LeanQbe.T.Examples.Kissat.FullM5SatNv
import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.Bytes
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `D-Full` M6 Concrete `Mem 64` Non-Vacuity Scaffolding (`FullM6SatNv`)

Constructs explicit concrete `Mem 64` witnesses inhabiting `M6Hdr`'s `3,456 B` header prefix
(`2,304 B` `M6HdrExt` with `fullM6HdrMagic` + `1,152 B` `FullHdr`) and `FullM6Hdr` preconditions
on BOTH a concrete UNSAT DIMACS formula (`(x1) ∧ (~x1)`) AND a concrete SAT DIMACS formula
(`(x1 ∨ x2)`):

1. **`nvM6UnsatInitMem` & `nvM6SatInitMem`**: concrete `8 KiB` workspace memories (`nvM6CnfPtr =
   0x1000#64`, `nvM6WorkLen = 8192`) for `"p cnf 1 2\n1 0\n-1 0\n"` (`pad = 5`) and
   `"p cnf 2 1\n1 2 0\n"` (`pad = 0`).
2. **`nvM6Mem`**: explicit concrete `Mem 64` witness inhabiting `M6Hdr`'s `3,456 B` initialized
   prefix (`nvM6ExtInitWords_ok : M6HdrExtInitOk nvM6ExtInitWords`, `nvM6SatCfg_ok : FullM6HdrCfgOk
   nvM6SatCfg`, `nvM6Mem_ok : (bytes ⋆ FullM6HdrMem) nvM6Mem`) together with a verified model
   `vals = [1#8, 0xFF#8, 1#8, 0xFF#8]` satisfying `(x1 ∨ x2)` under `readModelFromWorkM6`.
3. **Real C0 `Func.wp` Executions (`XPost := False`, `0` vacuous hypotheses)**:
   - `nvM6_unsat_full_m6_mem_init` & `nvM6_sat_full_m6_mem_init`: execute `full_m6_mem_init` on
     both formulas' `8 KiB` host buffers, returning `c.hdr = fullM6WorkHdr work_ptr ≠ 0#64` with
     `M6HdrExtInitOk` and `FullM6HdrInv`.
   - `nvM6_unsat_init_parse_wp`: executes `full_init_state` + `full_parse_body` on `(x1) ∧ (~x1)`
     in `M6Hdr`'s `3,456 B` workspace layout, returning `r = 20#64` and `nvM6UnsatCnf.Unsat`.
   - `nvM6_sat_checkModel_wp` & `nvM6_sat_extend_check_wp`: execute `kissat_check_model` and
     `full_extend` + `kissat_check_model` on `nvM6Mem`, returning `1#64` (`r = 10#64`), proving
     `nvM6SatCnf.Sat (readModelFromWorkM6 m' nvM6SatWorkPtr)`, and restoring the `8 KiB` region.
4. **Tier-3b Concrete Non-Vacuity Theorems (`fullM6_unsat_nv`, `fullM6_sat_nv`)**: show that
   every precondition of `fullM6SolveBytesCoreModelSpec` / `fullM6SolveBytesSpec` is concretely
   inhabited on `(x1) ∧ (~x1)` and `(x1 ∨ x2)` (`0` vacuous hypotheses, `XPost := False`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open Kraken.Bedrock2.Test

/-! ## 1. Concrete Formulas & `8,192 B` Host Payloads (`UNSAT` & `SAT`) -/

@[expose] def nvM6CnfPtr : BitVec 64 := 0x1000#64

@[expose] def nvM6WorkLen : Nat := 8192

/-- Concrete UNSAT DIMACS `"p cnf 1 2\n1 0\n-1 0\n"` (`(x1) ∧ (~x1)`, `19` bytes). -/
@[expose] def nvM6UnsatBytes : List UInt8 := fullNvUnsatBytes

@[expose] def nvM6UnsatCnf : CNF Nat := fullNvUnsatCnf

@[expose] def nvM6UnsatWorkPtr : BitVec 64 :=
  nvM6CnfPtr + BitVec.ofNat 64 nvM6UnsatBytes.length

/-- Concrete SAT DIMACS `"p cnf 2 1\n1 2 0\n"` (`(x1 ∨ x2)`, `16` bytes). -/
@[expose] def nvM6SatBytes : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 50, 32, 49, 10, 49, 32, 50, 32, 48, 10]

@[expose] def nvM6SatCnf : CNF Nat :=
  CNF.empty.add (CNF.Clause.ofLiterals [(1, true), (2, true)])

@[expose] def nvM6SatWorkPtr : BitVec 64 :=
  nvM6CnfPtr + BitVec.ofNat 64 nvM6SatBytes.length

@[expose] def nvM6UnsatInitMem : Mem 64 :=
  (nvM6UnsatBytes ++ List.replicate nvM6WorkLen 0).At nvM6CnfPtr

@[expose] def nvM6SatInitMem : Mem 64 :=
  (nvM6SatBytes ++ List.replicate nvM6WorkLen 0).At nvM6CnfPtr

theorem nvM6UnsatWorkPtr_eq_fullNvWorkPtr :
    nvM6UnsatWorkPtr = fullNvWorkPtr nvM6UnsatBytes := rfl

theorem nvM6SatWorkPtr_eq_fullNvWorkPtr :
    nvM6SatWorkPtr = fullNvWorkPtr nvM6SatBytes := rfl

theorem nvM6Unsat_pad_eq : fullAlignPad nvM6UnsatWorkPtr = 5 := by decide

theorem nvM6Sat_pad_eq : fullAlignPad nvM6SatWorkPtr = 0 := by decide

theorem nvM6_payload_sep (cnfBytes : List UInt8) (hlen : cnfBytes.length ≤ 4096) :
    (bytes nvM6CnfPtr cnfBytes ⋆ region (fullNvWorkPtr cnfBytes) nvM6WorkLen)
      ((cnfBytes ++ List.replicate nvM6WorkLen 0).At nvM6CnfPtr) :=
  nv_sep_append rfl
    (by unfold nvM6WorkLen; rw [List.length_replicate]; omega)
    rfl ⟨List.replicate nvM6WorkLen 0, List.length_replicate, rfl⟩

theorem nvM6UnsatInitMem_sep :
    (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) nvM6UnsatInitMem := by
  rw [nvM6UnsatWorkPtr_eq_fullNvWorkPtr]
  exact nvM6_payload_sep nvM6UnsatBytes (by decide)

theorem nvM6SatInitMem_sep :
    (bytes nvM6CnfPtr nvM6SatBytes ⋆ region nvM6SatWorkPtr nvM6WorkLen) nvM6SatInitMem := by
  rw [nvM6SatWorkPtr_eq_fullNvWorkPtr]
  exact nvM6_payload_sep nvM6SatBytes (by unfold nvM6SatBytes; decide)

theorem parseDimacs_nvM6UnsatBytes : parseDimacs nvM6UnsatBytes = some nvM6UnsatCnf :=
  parseDimacs_fullNvUnsatBytes

theorem nvM6UnsatCnf_unsat : nvM6UnsatCnf.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hsat
  rw [nvM6UnsatCnf, fullNvUnsatCnf, CNF.sat_add, CNF.sat_add] at hsat
  rcases hsat with ⟨hc2, hc1, _⟩
  rw [CNF.Clause.sat_iff_exists_mem_eq] at hc1 hc2
  obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := hc1
  obtain ⟨⟨v2, p2⟩, hm2, he2⟩ := hc2
  rw [← CNF.Clause.mem_literals_iff] at hm1 hm2
  simp at hm1 hm2
  rcases hm1 with ⟨rfl, rfl⟩
  rcases hm2 with ⟨rfl, rfl⟩
  rw [he1] at he2
  exact nomatch he2

theorem nvM6Unsat_header :
    parseHeader nvM6UnsatBytes = some (1, 2, nvM6UnsatBytes.drop 9) := rfl

theorem nvM6Unsat_unitTrace :
    UnitUnsatTrace 1 (List.replicate 2 0#8) (nvM6UnsatBytes.drop 9) 2 := by
  have hcl1 : parseClause 1 (nvM6UnsatBytes.drop 9) =
      some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral 0], nvM6UnsatBytes.drop 13) := rfl
  have hcl2 : parseClause 1 (nvM6UnsatBytes.drop 13) =
      some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral 1], nvM6UnsatBytes.drop 18) := rfl
  exact UnitUnsatTrace.step (l := 0) (by decide) hcl1 (by decide)
    (UnitUnsatTrace.conflict (l := 1) (by decide) hcl2 (by decide) ⟨CNF.empty, rfl⟩)

theorem nvM6_unsat_bound :
    fullM6ExtBytes + fullFixedBytes 1 + 2 * 40 + 136 + 8 ≤ nvM6WorkLen := by
  unfold nvM6WorkLen fullM6ExtBytes fullFixedBytes valsBytes markBytes u32FullBytes
    fullMinDepthOf
  decide

theorem parseDimacs_nvM6SatBytes : parseDimacs nvM6SatBytes = some nvM6SatCnf := rfl

theorem nvM6Sat_header :
    parseHeader nvM6SatBytes = some (2, 1, nvM6SatBytes.drop 9) := rfl

theorem nvM6SatCnf_sat : ∃ α, nvM6SatCnf.Sat α := by
  refine ⟨fun v => v == 1, ?_⟩
  rw [nvM6SatCnf, CNF.sat_add]
  refine ⟨?_, CNF.sat_empty⟩
  rw [CNF.Clause.sat_iff_exists_mem_eq]
  exact ⟨(1, true), by rw [← CNF.Clause.mem_literals_iff]; simp, rfl⟩

theorem nvM6SatCnf_not_unsat : ¬ nvM6SatCnf.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  exact fun h => let ⟨α, hα⟩ := nvM6SatCnf_sat; h α hα

/-! ## 2. Concrete `Mem 64` Witness `nvM6Mem` Inhabiting `M6Hdr`'s `3,456 B` Prefix -/

/-- Canonical initialized `288`-word `M6HdrExt` header (`fullM6HdrMagic` at word `0`). -/
@[expose] def nvM6ExtInitWords : List (BitVec 64) :=
  fullM6HdrMagic :: List.replicate 287 0#64

theorem nvM6ExtInitWords_len : nvM6ExtInitWords.length = fullM6ExtWords := by
  rw [nvM6ExtInitWords, List.length_cons, List.length_replicate, fullM6ExtWords]

theorem nvM6ExtInitWords_ok : M6HdrExtOk nvM6ExtInitWords :=
  M6HdrExtOk.of_len (by rw [nvM6ExtInitWords_len]; rfl)

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
  hmv := by unfold dimacsBound; omega
  hmaxv := by unfold dimacsBound; omega
  hnc := by unfold dimacsBound; omega
  harena := by unfold dimacsBound; omega
  hwcap := by unfold dimacsBound; omega
  hdel := by unfold dimacsBound; omega
  hred := by unfold dimacsBound; omega
  hext := by unfold dimacsBound; omega
  hscr := by unfold dimacsBound; omega
  havail_fit := nvM6SatCfg_avail_fit
  hsize := nvM6SatCfg_hsize

theorem nvM6SatCfg_hdr_eq : nvM6SatCfg.hdr = fullM6WorkHdr nvM6SatWorkPtr := rfl

theorem nvM6SatCfg_ok : FullM6HdrCfgOk nvM6SatCfg := by
  apply M6HdrCfgOk_of_le
  have h1 : nvM6SatCfg.hdr.toNat = 6416 := rfl
  omega

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

theorem nvM6Sat_lengths : nvM6SatState.LengthsOk nvM6SatCfg :=
  ⟨by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [nvM6SatState, nvM6SatCfg, nvOneLitState, FullCfg.minDepth, fullMinDepthOf],
   by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [nvM6SatState, nvM6SatCfg, nvOneLitState, nvOneLitScratch]⟩

@[expose] def nvM6SatBlockHdr : List UInt8 :=
  bytes64 [2#64, 1#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords nvM6SatCfg nvM6SatState)

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

/-- Concrete `Mem 64` witness mapped at `nvM6CnfPtr = 0x1000#64` holding `nvM6SatBytes` followed
by `M6Hdr`'s `3,456 B` initialized prefix (`M6HdrExtInitOk` with `fullM6HdrMagic` + `FullHdr`)
and verified SAT model `vals = [1#8, 0xFF#8, 1#8, 0xFF#8]` across an `8,192 B` workspace. -/
@[expose] def nvM6Mem : Mem 64 := nvM6MemBytes.At nvM6CnfPtr

private theorem nvM6SatCfg_slack : nvM6SatCfg.slack = 3924 := by
  unfold FullCfg.slack nvM6SatCfg nvM6WorkLen fullM6ExtBytes fullFixedBytes valsBytes
    markBytes u32FullBytes fullMinDepthOf
  decide

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
  have hmv1 : BitVec.ofNat 64 nvM6SatCfg.max_vars = 2#64 := rfl
  have hmv2 : BitVec.ofNat 64 (2 * nvM6SatCfg.max_vars) = 4#64 := rfl
  have hmv4 : BitVec.ofNat 64 (4 * nvM6SatCfg.max_vars) = 8#64 := rfl
  have hmv8 : BitVec.ofNat 64 (4 * (nvM6SatCfg.max_vars + 1)) = 12#64 := rfl
  have hsl : nvM6SatCfg.slack = 3924 := nvM6SatCfg_slack
  have hHdr : nvM6SatBlockHdr.length = 1152 ∧
      (dimacsState nvM6SatCfg.hdr (BitVec.ofNat 64 nvM6SatCfg.mv)
        (BitVec.ofNat 64 nvM6SatCfg.nc)
        nvM6SatState.core.d_cur nvM6SatState.core.d_val ⋆
        array64 (nvM6SatCfg.hdr + 32) (Full.hdrTailWords nvM6SatCfg nvM6SatState))
        (nvM6SatBlockHdr.At nvM6SatCfg.hdr) :=
    nv_join_pair
      (nv_arr64_p (a := nvM6SatCfg.hdr) (xs := [2#64, 1#64, 0#64, 0#64]) 32 rfl (by decide))
      (nv_arr64_p (a := nvM6SatCfg.hdr + 32) (xs := Full.hdrTailWords nvM6SatCfg nvM6SatState)
        1120 (by rw [Full.hdrTailWords_length]) (by decide))
      rfl (by decide)
  have hBytes : nvM6SatBlockBytes.length = 64 ∧
      (FullCoreByteArrs nvM6SatCfg nvM6SatState.core ⋆
        FullScrByteArrs nvM6SatCfg nvM6SatState.scratch ⋆ nvM6SatCfg.padBytes)
        (nvM6SatBlockBytes.At nvM6SatCfg.pVals) := by
    have h1 := nv_arr_pad_p (t := i8) (a := nvM6SatCfg.pVals) (xs := nvM6SatState.core.vals)
      4 4 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i8) (a := nvM6SatCfg.pWalkVals)
      (xs := nvM6SatState.scratch.walk_vals) 4 4
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h3 := nv_arr_pad_p (t := i8) (a := nvM6SatCfg.pLitMark)
      (xs := nvM6SatState.core.lit_mark) 4 4
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h4 := nv_arr_pad_p (t := i8) (a := nvM6SatCfg.pMark)
      (xs := nvM6SatState.core.mrk) 2 6
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h5 := nv_arr_pad_p (t := i8) (a := nvM6SatCfg.pPhases)
      (xs := nvM6SatState.scratch.phases) 2 6
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h6 := nv_arr_pad_p (t := i8) (a := nvM6SatCfg.pPhasesTarget)
      (xs := nvM6SatState.scratch.phases_target) 2 6
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h7 := nv_arr_pad_p (t := i8) (a := nvM6SatCfg.pPhasesBest)
      (xs := nvM6SatState.scratch.phases_best) 2 6
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h8 := nv_arr_pad_p (t := i8) (a := nvM6SatCfg.pWalkBest)
      (xs := nvM6SatState.scratch.walk_best) 2 6
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    let pB1 : Mem 64 → Prop :=
      region (nvM6SatCfg.pVals + 4#64) 4 ⋆ region (nvM6SatCfg.pWalkVals + 4#64) 4 ⋆
      region (nvM6SatCfg.pLitMark + 4#64) 4 ⋆ region (nvM6SatCfg.pMark + 2#64) 6
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_sep_reorg (nv_join_pair h123 h4 (by decide) (by decide))
      (Q := (FullCoreByteArrs nvM6SatCfg nvM6SatState.core ⋆
        array (t := i8) nvM6SatCfg.pWalkVals nvM6SatState.scratch.walk_vals) ⋆ pB1)
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
  have hU32A : nvM6SatBlockU32A.length = 80 ∧
      ((array (t := i32) nvM6SatCfg.pFlags nvM6SatState.core.flags ⋆
        array (t := i32) nvM6SatCfg.pLevel nvM6SatState.core.lvl ⋆
        array (t := i32) nvM6SatCfg.pReason nvM6SatState.core.rsns ⋆
        array (t := i32) nvM6SatCfg.pTrail nvM6SatState.core.trl ⋆
        array (t := i32) nvM6SatCfg.pTrailPos nvM6SatState.core.trail_pos) ⋆
        nvM6SatCfg.padU32A) (nvM6SatBlockU32A.At nvM6SatCfg.pFlags) := by
    have h1 := nv_arr_pad_p (t := i32) (a := nvM6SatCfg.pFlags) (xs := nvM6SatState.core.flags)
      8 8 (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := nvM6SatCfg.pLevel) (xs := nvM6SatState.core.lvl)
      8 8 (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := nvM6SatCfg.pReason) (xs := nvM6SatState.core.rsns)
      8 8 (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := nvM6SatCfg.pTrail) (xs := nvM6SatState.core.trl)
      8 8 (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := nvM6SatCfg.pTrailPos)
      (xs := nvM6SatState.core.trail_pos) 8 8
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu4, hmv4]; exact sep_ac hm
  have hU32B : nvM6SatBlockU32B.length = 80 ∧
      ((array (t := i32) nvM6SatCfg.pTmp nvM6SatState.core.tmp ⋆
        array (t := i32) nvM6SatCfg.pMinClr nvM6SatState.core.min_clr) ⋆
        (array (t := i32) nvM6SatCfg.pHeap nvM6SatState.scratch.heap ⋆
         array (t := i32) nvM6SatCfg.pPos nvM6SatState.scratch.pos ⋆
         array (t := i32) nvM6SatCfg.pShrinkStk nvM6SatState.scratch.shrink_stk) ⋆
        nvM6SatCfg.padU32B) (nvM6SatBlockU32B.At nvM6SatCfg.pTmp) := by
    have h1 := nv_arr_pad_p (t := i32) (a := nvM6SatCfg.pTmp) (xs := nvM6SatState.core.tmp)
      8 8 (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := nvM6SatCfg.pHeap) (xs := nvM6SatState.scratch.heap)
      8 8 (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := nvM6SatCfg.pPos) (xs := nvM6SatState.scratch.pos)
      8 8 (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := nvM6SatCfg.pMinClr)
      (xs := nvM6SatState.core.min_clr) 8 8
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := nvM6SatCfg.pShrinkStk)
      (xs := nvM6SatState.scratch.shrink_stk) 8 8
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu4, hmv4]; exact sep_ac hm
  have hU32C : nvM6SatBlockU32C.length = 80 ∧
      ((array (t := i32) nvM6SatCfg.pQPrev nvM6SatState.scratch.q_prev ⋆
        array (t := i32) nvM6SatCfg.pQNext nvM6SatState.scratch.q_next ⋆
        array (t := i32) nvM6SatCfg.pQStamp nvM6SatState.scratch.q_stamp) ⋆
        (array (t := i32) nvM6SatCfg.pFrameTrail nvM6SatState.core.frame_trail ⋆
         array (t := i32) nvM6SatCfg.pFrameDec nvM6SatState.core.frame_dec) ⋆
        nvM6SatCfg.padU32C) (nvM6SatBlockU32C.At nvM6SatCfg.pQPrev) := by
    have h1 := nv_arr_pad_p (t := i32) (a := nvM6SatCfg.pQPrev)
      (xs := nvM6SatState.scratch.q_prev) 8 8
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := nvM6SatCfg.pQNext)
      (xs := nvM6SatState.scratch.q_next) 8 8
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := nvM6SatCfg.pQStamp)
      (xs := nvM6SatState.scratch.q_stamp) 8 8
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := nvM6SatCfg.pFrameTrail)
      (xs := nvM6SatState.core.frame_trail) 12 4
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := nvM6SatCfg.pFrameDec)
      (xs := nvM6SatState.core.frame_dec) 12 4
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu4, hu8, hmv4, hmv8]; exact sep_ac hm
  have hWvec : nvM6SatBlockWvec.length = 160 ∧
      ((array (t := i32) nvM6SatCfg.pWvec nvM6SatState.core.wvec ⋆
        array (t := i32) nvM6SatCfg.pRepr nvM6SatState.core.repr) ⋆
        FullScrWksArrs nvM6SatCfg nvM6SatState.scratch ⋆
        (array64 nvM6SatCfg.pScore nvM6SatState.scratch.score ⋆
         array64 nvM6SatCfg.pSimSig nvM6SatState.scratch.sim_sig))
        (nvM6SatBlockWvec.At nvM6SatCfg.pWvec) := by
    have h1 := nv_arr_p (t := i32) (a := nvM6SatCfg.pWvec) (xs := nvM6SatState.core.wvec) 32
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h2 := nv_arr_p (t := i32) (a := nvM6SatCfg.pRepr) (xs := nvM6SatState.core.repr) 16
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h3 := nv_arr_p (t := i32) (a := nvM6SatCfg.pWsort) (xs := nvM6SatState.scratch.wsort) 16
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h4 := nv_arr_p (t := i32) (a := nvM6SatCfg.pWorkStk1)
      (xs := nvM6SatState.scratch.work_stk1) 16
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h5 := nv_arr_p (t := i32) (a := nvM6SatCfg.pWorkStk2)
      (xs := nvM6SatState.scratch.work_stk2) 16
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h6 := nv_arr_p (t := i32) (a := nvM6SatCfg.pTarjanMark)
      (xs := nvM6SatState.scratch.tarjan_mark) 16
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h7 := nv_arr_p (t := i32) (a := nvM6SatCfg.pTarjanReach)
      (xs := nvM6SatState.scratch.tarjan_reach) 16
      (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h8 := nv_arr64_p (a := nvM6SatCfg.pScore) (xs := nvM6SatState.scratch.score) 16
      (by simp [nvM6SatState]) (by decide)
    have h9 := nv_arr64_p (a := nvM6SatCfg.pSimSig) (xs := nvM6SatState.scratch.sim_sig) 16
      (by simp [nvM6SatState]) (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := nv_join_pair h1234567 h8 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail : nvM6SatBlockTail.length = 4272 ∧
      (array (t := i32) nvM6SatCfg.pMinStk nvM6SatState.core.min_stk ⋆
        (array (t := i32) nvM6SatCfg.pGlueUsed nvM6SatState.scratch.glue_used ⋆
         array (t := i32) nvM6SatCfg.pLastLearned nvM6SatState.scratch.last_learned) ⋆
        FullCoreDynArrs nvM6SatCfg nvM6SatState.core ⋆
        FullScrDynArrs nvM6SatCfg nvM6SatState.scratch ⋆
        region nvM6SatCfg.pSlack nvM6SatCfg.slack)
        (nvM6SatBlockTail.At nvM6SatCfg.pMinStk) := by
    have h1 := nv_arr_p (t := i32) (a := nvM6SatCfg.pMinStk) (xs := nvM6SatState.core.min_stk)
      24 (by simp [nvM6SatState, Ty.bytes, Ty.size]) (by decide)
    have h2 := nv_arr_p (t := i32) (a := nvM6SatCfg.pGlueUsed)
      (xs := nvM6SatState.scratch.glue_used) 256
      (by simp [nvM6SatState, nvOneLitState, nvOneLitScratch, Ty.bytes, Ty.size]) (by decide)
    have h3 := nv_arr_p (t := i32) (a := nvM6SatCfg.pLastLearned)
      (xs := nvM6SatState.scratch.last_learned) 64
      (by simp [nvM6SatState, nvOneLitState, nvOneLitScratch, Ty.bytes, Ty.size]) (by decide)
    have h4 := nv_arr_p (t := i32) (a := nvM6SatCfg.pArena) (xs := nvM6SatState.core.arena) 0
      (by simp [nvM6SatState, nvOneLitState, Ty.bytes, Ty.size]) (by decide)
    have h5 := nv_arr_p (t := i32) (a := nvM6SatCfg.pWstk) (xs := nvM6SatState.core.wstk) 4
      (by simp [nvM6SatState, nvOneLitState, Ty.bytes, Ty.size]) (by decide)
    have h6 := nv_arr_p (t := i32) (a := nvM6SatCfg.pDelayed)
      (xs := nvM6SatState.scratch.delayed) 0
      (by simp [nvM6SatState, nvOneLitState, nvOneLitScratch, Ty.bytes, Ty.size]) (by decide)
    have h7 := nv_arr_p (t := i32) (a := nvM6SatCfg.pRedRefs)
      (xs := nvM6SatState.scratch.red_refs) 0
      (by simp [nvM6SatState, nvOneLitState, nvOneLitScratch, Ty.bytes, Ty.size]) (by decide)
    have h8 := nv_arr_p (t := i32) (a := nvM6SatCfg.pExtendStk)
      (xs := nvM6SatState.scratch.extend_stk) 0
      (by simp [nvM6SatState, nvOneLitState, nvOneLitScratch, Ty.bytes, Ty.size]) (by decide)
    have h9 := nv_arr_p (t := i32) (a := nvM6SatCfg.pScratchBuf)
      (xs := nvM6SatState.scratch.scratch_buf) 0
      (by simp [nvM6SatState, nvOneLitState, nvOneLitScratch, Ty.bytes, Ty.size]) (by decide)
    have h10 : (List.replicate nvM6SatCfg.slack (0 : UInt8)).length = 3924 ∧
        region nvM6SatCfg.pSlack nvM6SatCfg.slack
          ((List.replicate nvM6SatCfg.slack 0).At nvM6SatCfg.pSlack) :=
      ⟨by rw [List.length_replicate, hsl],
        ⟨List.replicate nvM6SatCfg.slack 0, List.length_replicate, rfl⟩⟩
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
  have hav : nvM6SatCfg.avail = 5888 := rfl
  have h06 := nv_sep_reorg (nv_join_pair h05 hTail (by decide) (by omega))
    (Q := FullMem nvM6SatCfg nvM6SatState) fun _ hm => by
      unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
        FullScrMetaArrs FullCfg.pad
      exact sep_ac hm
  have hlen_avail : nvM6SatArenaBytes.length = nvM6SatCfg.avail := by
    unfold nvM6SatArenaBytes
    rw [h06.1, hav]
  exact ⟨hlen_avail, h06.2⟩

theorem nvM6Mem_ok :
    (bytes nvM6CnfPtr nvM6SatBytes ⋆
      FullM6HdrMem nvM6SatCfg nvM6ExtInitWords nvM6SatState) nvM6Mem := by
  have hExt : (bytes64 nvM6ExtInitWords).length = 2304 ∧
      array64 nvM6SatWorkPtr nvM6ExtInitWords
        ((bytes64 nvM6ExtInitWords).At nvM6SatWorkPtr) :=
    nv_arr64_p (a := nvM6SatWorkPtr) (xs := nvM6ExtInitWords) 2304
      (by rw [nvM6ExtInitWords_len]; rfl) (by decide)
  have hArena := nvM6SatArena_ok
  have hav : nvM6SatCfg.avail = 5888 := rfl
  have hwlen : nvM6WorkLen = 8192 := rfl
  have hM6 : (bytes64 nvM6ExtInitWords ++ nvM6SatArenaBytes).length = nvM6WorkLen ∧
      FullM6HdrMem nvM6SatCfg nvM6ExtInitWords nvM6SatState
        ((bytes64 nvM6ExtInitWords ++ nvM6SatArenaBytes).At nvM6SatWorkPtr) := by
    have hj := nv_join_pair hExt hArena rfl (by rw [hav]; omega)
    have hj' : (bytes64 nvM6ExtInitWords ++ nvM6SatArenaBytes).length = nvM6WorkLen ∧ _ :=
      ⟨by rw [hj.1, hav, hwlen], hj.2⟩
    exact nv_sep_reorg hj'
      (Q := FullM6HdrMem nvM6SatCfg nvM6ExtInitWords nvM6SatState) fun _ hm => by
        apply fullM6HdrMem_mk
        have hsub : nvM6SatCfg.hdr - 2304 = nvM6SatWorkPtr := rfl
        rwa [hsub]
  have hCnf : nvM6SatBytes.length = 16 ∧
      bytes nvM6CnfPtr nvM6SatBytes (nvM6SatBytes.At nvM6CnfPtr) :=
    ⟨rfl, rfl⟩
  have hj := nv_join_pair hCnf hM6 rfl (by rw [hwlen]; omega)
  exact hj.2

theorem nvM6Mem_region :
    (bytes nvM6CnfPtr nvM6SatBytes ⋆ region nvM6SatWorkPtr nvM6WorkLen) nvM6Mem := by
  have hm := nvM6Mem_ok
  refine sep_mono_r (fun _ hr => ?_) hm
  have hr_m6 := fullM6HdrMem_to_region nvM6SatCfg_ok nvM6ExtInitWords_ok
    nvM6Sat_lengths hr
  have haddr : m6ExtAddr nvM6SatCfg.hdr = nvM6SatWorkPtr := by
    rw [m6ExtAddr_eq]; rfl
  have hsz : fullM6ExtBytes + nvM6SatCfg.avail = nvM6WorkLen := rfl
  rwa [haddr, hsz] at hr_m6

theorem nvM6Mem_readModel_1 : readModelFromWorkM6 nvM6Mem nvM6SatWorkPtr 1 = true := by
  have hr := readModelFromWorkM6_of_vals (c := nvM6SatCfg) (ext := nvM6ExtInitWords)
    (s := nvM6SatState) (R := bytes nvM6CnfPtr nvM6SatBytes) (F := emp)
    (work_ptr := nvM6SatWorkPtr) rfl nvM6Sat_lengths (sep_ac nvM6Mem_ok)
    (by rw [Std.ExtHashMap.sep_emp]) (v := 1) (by omega) (by decide)
  rw [hr]; decide

theorem nvM6Mem_readModel_2 : readModelFromWorkM6 nvM6Mem nvM6SatWorkPtr 2 = true := by
  have hr := readModelFromWorkM6_of_vals (c := nvM6SatCfg) (ext := nvM6ExtInitWords)
    (s := nvM6SatState) (R := bytes nvM6CnfPtr nvM6SatBytes) (F := emp)
    (work_ptr := nvM6SatWorkPtr) rfl nvM6Sat_lengths (sep_ac nvM6Mem_ok)
    (by rw [Std.ExtHashMap.sep_emp]) (v := 2) (by omega) (by decide)
  rw [hr]; decide

theorem nvM6Mem_sat : nvM6SatCnf.Sat (readModelFromWorkM6 nvM6Mem nvM6SatWorkPtr) := by
  rw [nvM6SatCnf, CNF.sat_add]
  refine ⟨?_, CNF.sat_empty⟩
  rw [CNF.Clause.sat_iff_exists_mem_eq]
  exact ⟨(1, true), by rw [← CNF.Clause.mem_literals_iff]; simp, nvM6Mem_readModel_1⟩

/-! ## 3. Real C0 `Func.wp` Executions (`XPost := False`, `0` Vacuous Hypotheses) -/

private def nvM6NvSpecTable : List SpecEntry :=
  [ ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, false⟩
  , ⟨"full_fixed_bytes", [i64], [i64], FullParseInitSpecs.fullFixedBytesSpec, false⟩
  , ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], FullParseInitSpecs.fullCalcMaxVSpec, false⟩
  , ⟨"full_calc_ext_cap", [i64], [i64], FullParseInitSpecs.fullCalcExtCapSpec, false⟩
  , ⟨"full_calc_scr_cap", [i64], [i64], FullParseInitSpecs.fullCalcScrCapSpec, false⟩
  , ⟨"full_init_arenas", [i64, i64, i64, i64], [], FullParseInitSpecs.fullInitArenasSpec, false⟩
  , ⟨"full_init_hdr", [i64, i64, i64, i64], [], FullParseInitSpecs.fullInitHdrSpec, false⟩
  , ⟨"full_zero_tables1", [i64], [], FullParseInitSpecs.fullZeroTables1Spec, false⟩
  , ⟨"full_zero_tables2", [i64], [], FullParseInitSpecs.fullZeroTables2Spec, false⟩
  , ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool],
      FullParseInitSpecs.fullInitStateSpec, false⟩
  , ⟨"m6_hdr_init", [i64], [], m6HdrInitSpec, false⟩
  , ⟨"full_skip_cl", [i64, i64], [.bool], fullSkipClSpec, false⟩
  , ⟨"full_ingest_cl", [i64, i64], [i64], fullIngestClSpec, false⟩
  , ⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, false⟩
  , ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, false⟩ ]

private theorem nvM6NvSpecTable_nodup :
    (nvM6NvSpecTable.map SpecEntry.name).Nodup := by
  decide

/-- Concrete `Env` backing real C0 `Func.wp` execution of `m6_hdr_init`, `full_init_state`,
`full_m6_mem_init`, and `full_parse_body` over the verified `Full` / `FullM6Hdr` specs. -/
def nvM6NvEnv : Env := Env.ofTable nvM6NvSpecTable

private theorem nvM6NvEnv_mem {e : SpecEntry} (he : e ∈ nvM6NvSpecTable)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost} (h : e.eff xs m Q X) :
    nvM6NvEnv e.name e.as e.rs xs m Q X :=
  Env.ofTable_of_mem he nvM6NvSpecTable_nodup h

private theorem nvM6NvEnv_init_state {a : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost} (hs : fullInitStateSpec a m Q X) :
    nvM6NvEnv "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X :=
  nvM6NvEnv_mem (e := ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool],
    fullInitStateSpec, false⟩) (List.mem_of_getElem? (i := 9) rfl) hs

private theorem nvM6NvEnv_m6_hdr_init {a : Tup Val [i64]} {m : Mem 64}
    {Q : Post []} {X : XPost} (hs : m6HdrInitSpec a m Q X) :
    nvM6NvEnv "m6_hdr_init" [i64] [] a m Q X :=
  nvM6NvEnv_mem (e := ⟨"m6_hdr_init", [i64], [], m6HdrInitSpec, false⟩)
    (List.mem_of_getElem? (i := 10) rfl) hs

theorem nvM6_m6_hdr_init_nv_wp {a : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X : XPost}
    (h : m6HdrInitSpec a m Q X) :
    Func.wp nvM6NvEnv m6_hdr_init_body a m Q X :=
  m6_hdr_init_wp nvM6NvEnv a m Q X h

theorem nvM6_full_init_state_nv_wp {a : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (h : FullParseInitSpecs.fullInitStateSpec a m Q X) :
    Func.wp nvM6NvEnv full_init_state_body a m Q X :=
  full_init_state_bridge_wp nvM6NvEnv
    (fun _ _ _ _ hs => nvM6NvEnv_mem
      (e := ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, false⟩)
      (List.mem_of_getElem? (i := 0) rfl) hs)
    (fun _ _ _ _ hs => nvM6NvEnv_mem
      (e := ⟨"full_fixed_bytes", [i64], [i64],
        FullParseInitSpecs.fullFixedBytesSpec, false⟩)
      (List.mem_of_getElem? (i := 1) rfl) hs)
    (fun _ _ _ _ hs => nvM6NvEnv_mem
      (e := ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64],
        FullParseInitSpecs.fullCalcMaxVSpec, false⟩)
      (List.mem_of_getElem? (i := 2) rfl) hs)
    (fun _ _ _ _ hs => nvM6NvEnv_mem
      (e := ⟨"full_calc_ext_cap", [i64], [i64],
        FullParseInitSpecs.fullCalcExtCapSpec, false⟩)
      (List.mem_of_getElem? (i := 3) rfl) hs)
    (fun _ _ _ _ hs => nvM6NvEnv_mem
      (e := ⟨"full_calc_scr_cap", [i64], [i64],
        FullParseInitSpecs.fullCalcScrCapSpec, false⟩)
      (List.mem_of_getElem? (i := 4) rfl) hs)
    (fun _ _ _ _ hs => nvM6NvEnv_mem
      (e := ⟨"full_init_arenas", [i64, i64, i64, i64], [],
        FullParseInitSpecs.fullInitArenasSpec, false⟩)
      (List.mem_of_getElem? (i := 5) rfl) hs)
    (fun _ _ _ _ hs => nvM6NvEnv_mem
      (e := ⟨"full_init_hdr", [i64, i64, i64, i64], [],
        FullParseInitSpecs.fullInitHdrSpec, false⟩)
      (List.mem_of_getElem? (i := 6) rfl) hs)
    (fun _ _ _ _ hs => nvM6NvEnv_mem
      (e := ⟨"full_zero_tables1", [i64], [],
        FullParseInitSpecs.fullZeroTables1Spec, false⟩)
      (List.mem_of_getElem? (i := 7) rfl) hs)
    (fun _ _ _ _ hs => nvM6NvEnv_mem
      (e := ⟨"full_zero_tables2", [i64], [],
        FullParseInitSpecs.fullZeroTables2Spec, false⟩)
      (List.mem_of_getElem? (i := 8) rfl) hs)
    a m Q X h

theorem nvM6_full_m6_mem_init_nv_wp {a : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} (h : fullM6MemInitSpec a m Q X) :
    Func.wp nvM6NvEnv full_m6_mem_init_body a m Q X :=
  full_m6_mem_init_wp nvM6NvEnv
    (fun _ _ _ _ hs => nvM6NvEnv_init_state hs)
    (fun _ _ _ _ hs => nvM6NvEnv_m6_hdr_init hs)
    a m Q X h

theorem nvM6_full_parse_body_nv_wp {a : Tup Val [i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} (h : fullParseBodySpec a m Q X) :
    Func.wp nvM6NvEnv full_parse_body_body a m Q X :=
  full_parse_body_bridge_wp nvM6NvEnv
    (fun _ _ _ _ hs => nvM6NvEnv_mem
      (e := ⟨"full_skip_cl", [i64, i64], [.bool], fullSkipClSpec, false⟩)
      (List.mem_of_getElem? (i := 11) rfl) hs)
    (fun _ _ _ _ hs => nvM6NvEnv_mem
      (e := ⟨"full_ingest_cl", [i64, i64], [i64], fullIngestClSpec, false⟩)
      (List.mem_of_getElem? (i := 12) rfl) hs)
    (fun _ _ _ _ hs => nvM6NvEnv_mem
      (e := ⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, false⟩)
      (List.mem_of_getElem? (i := 13) rfl) hs)
    a m Q X h

private theorem m5_parse_body_spec_wp {a : Tup Val [i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} (h : fullParseBodySpec a m Q X) :
    Func.wp (FullM5.mkM5Env fullSolveBytesSpec) full_parse_body_body a m Q X := by
  have hm := FullM5.mkM5Env_moduleOk fullSolveBytesSpec
    (fun _ _ _ _ hs => fullSolveBytesCoreSpec_of_spec hs)
  have hfn := (hm.fnsOk (FullM5.m5Module.fns.take 48)
    ⟨"full_parse_body", [i64, i64], [i64], full_parse_body_body⟩
    (FullM5.m5Module.fns.drop 49) rfl).2.2
  exact hfn a m Q X (FullM5.mkM5Env_parse_body fullSolveBytesSpec a m Q X h)

private theorem m5_extend_spec_wp {a : Tup Val [i64]}
    {m : Mem 64} {Q : Post []} {X : XPost} (h : fullExtendSpec a m Q X) :
    Func.wp (FullM5.mkM5Env fullSolveBytesSpec) full_extend_body a m Q X :=
  full_extend_wp (FullM5.mkM5Env fullSolveBytesSpec) a m Q X h

private theorem dimacs_check_model_spec_wp {a : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} (h : kissatCheckModelExactSpec a m Q X) :
    Func.wp dimacsExactEnv kissat_check_model_body a m Q X := by
  have hfn := (dimacsExactEnv_moduleOk.fnsOk (dimacsModule.fns.take 7)
    ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissat_check_model_body⟩
    (dimacsModule.fns.drop 8) rfl).2.2
  exact hfn a m Q X h

/-- Parametric C0 `full_m6_mem_init` execution (`XPost := False`, `0` vacuous hypotheses) on
concrete `8 KiB` `nvM6UnsatInitMem` (`(x1) ∧ (~x1)`, `pad = 5`, `avail = 8187`). -/
theorem nvM6_unsat_full_m6_mem_init_of (Γ : Env)
    (hinit : ∀ a m Q X, fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hm6 : ∀ a m Q X, m6HdrInitSpec a m Q X →
      Γ "m6_hdr_init" [i64] [] a m Q X) :
    Func.wp Γ full_m6_mem_init_body
      (nvM6CnfPtr, nvM6CnfPtr + BitVec.ofNat 64 nvM6UnsatBytes.length,
        fullM6WorkBase nvM6UnsatWorkPtr,
        BitVec.ofNat 64 (nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr), 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (hdr, ()) =>
          ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState),
            hdr = c.hdr ∧ c.hdr = fullM6WorkHdr nvM6UnsatWorkPtr ∧
            c.avail = nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr - fullM6ExtBytes ∧
            c.mv = 1 ∧ c.nc = 2 ∧
            FullM6HdrCfgOk c ∧ M6HdrExtInitOk ext ∧
            FullM6HdrInv c (shiftDownCnf CNF.empty) ext s ∧
            s.core.cur_vars = c.mv ∧
            s.core.d_cur = nvM6CnfPtr + 9#64 ∧
            s.core.arena_len = 0 ∧ s.core.wlen = 1 ∧ s.core.trail_end = 0 ∧
            s.core.propagated = 0 ∧ s.core.cur_level = 0 ∧ s.core.fuel = 16#64 ∧
            s.core.oom = 0#64 ∧ s.core.inconsistent = 0#64 ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ FullM6HdrMem c ext s ⋆
              region nvM6UnsatWorkPtr (fullAlignPad nvM6UnsatWorkPtr)) m')
      (fun _ _ _ _ => False) := by
  have hle : fullAlignPad nvM6UnsatWorkPtr + fullM6HdrTotalBytes ≤ nvM6WorkLen := by decide
  have hfit : nvM6WorkLen ≤ 2 ^ 64 := by unfold nvM6WorkLen; omega
  have hm : (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
      region (fullM6WorkBase nvM6UnsatWorkPtr)
        (nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr) ⋆
      region nvM6UnsatWorkPtr (fullAlignPad nvM6UnsatWorkPtr)) nvM6UnsatInitMem :=
    sep_ac (sep_mono_r (fun _ hr => region_work_to_m6_workBase hle hfit hr)
      nvM6UnsatInitMem_sep)
  refine full_m6_mem_init_wp Γ hinit hm6 _ _ _ _
    (fullM6MemInitSpec_of rfl (by decide) (by decide) hm
      (fun m' _ hfail => ?_)
      (fun c ext s j rest m' hhdr hav hcfg hext hph hj hd hinv hcv hdcur hal hw hte hpr hcl
        hfu hoom hinc hm' => ?_))
  · exfalso
    rcases hfail with hlt | hsmall
    · revert hlt; decide
    · have hsmall' := hsmall 1 2 (nvM6UnsatBytes.drop 9) nvM6Unsat_header
      revert hsmall'; unfold fullFixedBytes valsBytes markBytes u32FullBytes fullMinDepthOf
      decide
  · simp only [nvM6Unsat_header, Option.some.injEq, Prod.mk.injEq] at hph
    rcases hph with ⟨hmv, hnc, hrest⟩
    have hrest_len : (nvM6UnsatBytes.drop j).length = (nvM6UnsatBytes.drop 9).length := by
      rw [hd, hrest]
    have hj9 : j = 9 := by
      have h19 : nvM6UnsatBytes.length = 19 := rfl
      simp only [List.length_drop, h19] at hj hrest_len ⊢; omega
    subst hj9
    have hc_hdr : c.hdr = fullM6WorkHdr nvM6UnsatWorkPtr := by
      rw [hhdr]; unfold fullM6WorkHdr; rfl
    have hc_avail : c.avail = nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr - fullM6ExtBytes := by
      rw [hav]; decide
    exact ⟨c, ext, s, rfl, hc_hdr, hc_avail, hmv.symm, hnc.symm, hcfg, hext, hinv,
      hcv, hdcur, hal, hw, hte, hpr, hcl, hfu, hoom, hinc, hm'⟩

/-- Concrete C0 `full_m6_mem_init` execution (`XPost := False`, `nvM6NvEnv`) on `8 KiB`
`nvM6UnsatInitMem` (`(x1) ∧ (~x1)`, `pad = 5`, `avail = 8187`). -/
theorem nvM6_unsat_full_m6_mem_init :
    Func.wp nvM6NvEnv full_m6_mem_init_body
      (nvM6CnfPtr, nvM6CnfPtr + BitVec.ofNat 64 nvM6UnsatBytes.length,
        fullM6WorkBase nvM6UnsatWorkPtr,
        BitVec.ofNat 64 (nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr), 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (hdr, ()) =>
          ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState),
            hdr = c.hdr ∧ c.hdr = fullM6WorkHdr nvM6UnsatWorkPtr ∧
            c.avail = nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr - fullM6ExtBytes ∧
            c.mv = 1 ∧ c.nc = 2 ∧
            FullM6HdrCfgOk c ∧ M6HdrExtInitOk ext ∧
            FullM6HdrInv c (shiftDownCnf CNF.empty) ext s ∧
            s.core.cur_vars = c.mv ∧
            s.core.d_cur = nvM6CnfPtr + 9#64 ∧
            s.core.arena_len = 0 ∧ s.core.wlen = 1 ∧ s.core.trail_end = 0 ∧
            s.core.propagated = 0 ∧ s.core.cur_level = 0 ∧ s.core.fuel = 16#64 ∧
            s.core.oom = 0#64 ∧ s.core.inconsistent = 0#64 ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ FullM6HdrMem c ext s ⋆
              region nvM6UnsatWorkPtr (fullAlignPad nvM6UnsatWorkPtr)) m')
      (fun _ _ _ _ => False) :=
  nvM6_unsat_full_m6_mem_init_of nvM6NvEnv
    (fun _ _ _ _ hs => nvM6NvEnv_init_state hs)
    (fun _ _ _ _ hs => nvM6NvEnv_m6_hdr_init hs)

/-- Parametric C0 `full_m6_mem_init` execution (`XPost := False`, `0` vacuous hypotheses) on
concrete `8 KiB` `nvM6SatInitMem` (`(x1 ∨ x2)`, `pad = 0`, `avail = 8192`). -/
theorem nvM6_sat_full_m6_mem_init_of (Γ : Env)
    (hinit : ∀ a m Q X, fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hm6 : ∀ a m Q X, m6HdrInitSpec a m Q X →
      Γ "m6_hdr_init" [i64] [] a m Q X) :
    Func.wp Γ full_m6_mem_init_body
      (nvM6CnfPtr, nvM6CnfPtr + BitVec.ofNat 64 nvM6SatBytes.length,
        fullM6WorkBase nvM6SatWorkPtr,
        BitVec.ofNat 64 (nvM6WorkLen - fullAlignPad nvM6SatWorkPtr), 16#64, ())
      nvM6SatInitMem
      (fun rs m' =>
        match rs with
        | (hdr, ()) =>
          ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState),
            hdr = c.hdr ∧ c.hdr = fullM6WorkHdr nvM6SatWorkPtr ∧
            c.avail = nvM6WorkLen - fullAlignPad nvM6SatWorkPtr - fullM6ExtBytes ∧
            c.mv = 2 ∧ c.nc = 1 ∧
            FullM6HdrCfgOk c ∧ M6HdrExtInitOk ext ∧
            FullM6HdrInv c (shiftDownCnf CNF.empty) ext s ∧
            s.core.cur_vars = c.mv ∧
            s.core.d_cur = nvM6CnfPtr + 9#64 ∧
            s.core.arena_len = 0 ∧ s.core.wlen = 1 ∧ s.core.trail_end = 0 ∧
            s.core.propagated = 0 ∧ s.core.cur_level = 0 ∧ s.core.fuel = 16#64 ∧
            s.core.oom = 0#64 ∧ s.core.inconsistent = 0#64 ∧
            (bytes nvM6CnfPtr nvM6SatBytes ⋆ FullM6HdrMem c ext s ⋆
              region nvM6SatWorkPtr (fullAlignPad nvM6SatWorkPtr)) m')
      (fun _ _ _ _ => False) := by
  have hpad0 : fullAlignPad nvM6SatWorkPtr = 0 := nvM6Sat_pad_eq
  have hle : fullAlignPad nvM6SatWorkPtr + fullM6HdrTotalBytes ≤ nvM6WorkLen := by
    rw [hpad0]; unfold fullM6HdrTotalBytes nvM6WorkLen; omega
  have hfit : nvM6WorkLen ≤ 2 ^ 64 := by unfold nvM6WorkLen; omega
  have hm : (bytes nvM6CnfPtr nvM6SatBytes ⋆
      region (fullM6WorkBase nvM6SatWorkPtr)
        (nvM6WorkLen - fullAlignPad nvM6SatWorkPtr) ⋆
      region nvM6SatWorkPtr (fullAlignPad nvM6SatWorkPtr)) nvM6SatInitMem :=
    sep_ac (sep_mono_r (fun _ hr => region_work_to_m6_workBase hle hfit hr)
      nvM6SatInitMem_sep)
  refine full_m6_mem_init_wp Γ hinit hm6 _ _ _ _
    (fullM6MemInitSpec_of rfl (by decide) (by decide) hm
      (fun m' _ hfail => ?_)
      (fun c ext s j rest m' hhdr hav hcfg hext hph hj hd hinv hcv hdcur hal hw hte hpr hcl
        hfu hoom hinc hm' => ?_))
  · exfalso
    rcases hfail with hlt | hsmall
    · revert hlt; rw [hpad0]; unfold nvM6WorkLen fullM6HdrTotalBytes; decide
    · have hsmall' := hsmall 2 1 (nvM6SatBytes.drop 9) nvM6Sat_header
      revert hsmall'; rw [hpad0]
      unfold nvM6WorkLen fullM6ExtBytes fullFixedBytes valsBytes markBytes u32FullBytes
        fullMinDepthOf
      decide
  · simp only [nvM6Sat_header, Option.some.injEq, Prod.mk.injEq] at hph
    rcases hph with ⟨hmv, hnc, hrest⟩
    have hrest_len : (nvM6SatBytes.drop j).length = (nvM6SatBytes.drop 9).length := by
      rw [hd, hrest]
    have hj9 : j = 9 := by
      have h16 : nvM6SatBytes.length = 16 := rfl
      simp only [List.length_drop, h16] at hj hrest_len ⊢; omega
    subst hj9
    have hc_hdr : c.hdr = fullM6WorkHdr nvM6SatWorkPtr := by
      rw [hhdr]; unfold fullM6WorkHdr; rfl
    have hc_avail : c.avail = nvM6WorkLen - fullAlignPad nvM6SatWorkPtr - fullM6ExtBytes := by
      rw [hav, hpad0]; unfold nvM6WorkLen fullM6ExtBytes; decide
    exact ⟨c, ext, s, rfl, hc_hdr, hc_avail, hmv.symm, hnc.symm, hcfg, hext, hinv,
      hcv, hdcur, hal, hw, hte, hpr, hcl, hfu, hoom, hinc, hm'⟩

/-- Concrete C0 `full_m6_mem_init` execution (`XPost := False`, `nvM6NvEnv`) on `8 KiB`
`nvM6SatInitMem` (`(x1 ∨ x2)`, `pad = 0`, `avail = 8192`). -/
theorem nvM6_sat_full_m6_mem_init :
    Func.wp nvM6NvEnv full_m6_mem_init_body
      (nvM6CnfPtr, nvM6CnfPtr + BitVec.ofNat 64 nvM6SatBytes.length,
        fullM6WorkBase nvM6SatWorkPtr,
        BitVec.ofNat 64 (nvM6WorkLen - fullAlignPad nvM6SatWorkPtr), 16#64, ())
      nvM6SatInitMem
      (fun rs m' =>
        match rs with
        | (hdr, ()) =>
          ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState),
            hdr = c.hdr ∧ c.hdr = fullM6WorkHdr nvM6SatWorkPtr ∧
            c.avail = nvM6WorkLen - fullAlignPad nvM6SatWorkPtr - fullM6ExtBytes ∧
            c.mv = 2 ∧ c.nc = 1 ∧
            FullM6HdrCfgOk c ∧ M6HdrExtInitOk ext ∧
            FullM6HdrInv c (shiftDownCnf CNF.empty) ext s ∧
            s.core.cur_vars = c.mv ∧
            s.core.d_cur = nvM6CnfPtr + 9#64 ∧
            s.core.arena_len = 0 ∧ s.core.wlen = 1 ∧ s.core.trail_end = 0 ∧
            s.core.propagated = 0 ∧ s.core.cur_level = 0 ∧ s.core.fuel = 16#64 ∧
            s.core.oom = 0#64 ∧ s.core.inconsistent = 0#64 ∧
            (bytes nvM6CnfPtr nvM6SatBytes ⋆ FullM6HdrMem c ext s ⋆
              region nvM6SatWorkPtr (fullAlignPad nvM6SatWorkPtr)) m')
      (fun _ _ _ _ => False) :=
  nvM6_sat_full_m6_mem_init_of nvM6NvEnv
    (fun _ _ _ _ hs => nvM6NvEnv_init_state hs)
    (fun _ _ _ _ hs => nvM6NvEnv_m6_hdr_init hs)

/-- Real C0 `full_init_state` + `full_parse_body` execution (`XPost := False`, `M6Hdr` `3,456 B`
layout, `nvM6NvEnv`) on `(x1) ∧ (~x1)`: executes to `r = 20#64`, certifies `nvM6UnsatCnf.Unsat`,
and restores `(bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen)`. -/
theorem nvM6_unsat_init_parse_wp :
    Func.wp nvM6NvEnv full_init_state_body
      (nvM6CnfPtr, nvM6CnfPtr + BitVec.ofNat 64 nvM6UnsatBytes.length,
        fullM6WorkHdr nvM6UnsatWorkPtr,
        BitVec.ofNat 64 (nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr - fullM6ExtBytes),
        16#64, ())
      nvM6UnsatInitMem
      (fun rs m1 =>
        match rs with
        | (ok, ()) =>
          ok = true ∧
          Func.wp (FullM5.mkM5Env fullSolveBytesSpec) full_parse_body_body
            (fullM6WorkHdr nvM6UnsatWorkPtr,
              nvM6CnfPtr + BitVec.ofNat 64 nvM6UnsatBytes.length, ()) m1
            (fun rs2 m2 =>
              match rs2 with
              | (r, ()) =>
                r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
                (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
                  region nvM6UnsatWorkPtr nvM6WorkLen) m2)
            (fun _ _ _ _ => False))
      (fun _ _ _ _ => False) := by
  have hpad : fullAlignPad nvM6UnsatWorkPtr = 5 := nvM6Unsat_pad_eq
  have hle : fullAlignPad nvM6UnsatWorkPtr + fullM6HdrTotalBytes ≤ nvM6WorkLen := by decide
  have hfit : nvM6WorkLen ≤ 2 ^ 64 := by unfold nvM6WorkLen; omega
  have hm_pad : (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
      region (fullM6WorkBase nvM6UnsatWorkPtr)
        (nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr) ⋆
      region nvM6UnsatWorkPtr (fullAlignPad nvM6UnsatWorkPtr)) nvM6UnsatInitMem :=
    sep_ac (sep_mono_r (fun _ hr => region_work_to_m6_workBase hle hfit hr)
      nvM6UnsatInitMem_sep)
  have hsum : fullM6ExtBytes +
      (nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr - fullM6ExtBytes) =
      nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr := by
    rw [hpad]; unfold fullM6ExtBytes nvM6WorkLen; decide
  have hsplit_ext : ∀ m, region (fullM6WorkBase nvM6UnsatWorkPtr)
      (nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr) m →
      (region (fullM6WorkBase nvM6UnsatWorkPtr) fullM6ExtBytes ⋆
        region (fullM6WorkHdr nvM6UnsatWorkPtr)
          (nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr - fullM6ExtBytes)) m := by
    intro m hr
    simpa [fullM6WorkHdr] using (congrFun (region_merge_eq (a := fullM6WorkBase nvM6UnsatWorkPtr)
      hsum (by unfold nvM6WorkLen; omega)) m).mpr hr
  have hmid : ∀ x,
      (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
        region (fullM6WorkBase nvM6UnsatWorkPtr)
          (nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr)) x →
      (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
        (region (fullM6WorkBase nvM6UnsatWorkPtr) fullM6ExtBytes ⋆
          region (fullM6WorkHdr nvM6UnsatWorkPtr)
            (nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr - fullM6ExtBytes))) x :=
    fun _ hm => sep_mono_r hsplit_ext hm
  have hm_split0 : ((bytes nvM6CnfPtr nvM6UnsatBytes ⋆
      (region (fullM6WorkBase nvM6UnsatWorkPtr) fullM6ExtBytes ⋆
        region (fullM6WorkHdr nvM6UnsatWorkPtr)
          (nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr - fullM6ExtBytes))) ⋆
      region nvM6UnsatWorkPtr (fullAlignPad nvM6UnsatWorkPtr)) nvM6UnsatInitMem :=
    sep_mono hmid hm_pad
  have hm_split : (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
      region (fullM6WorkHdr nvM6UnsatWorkPtr)
        (nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr - fullM6ExtBytes) ⋆
      (region (fullM6WorkBase nvM6UnsatWorkPtr) fullM6ExtBytes ⋆
        region nvM6UnsatWorkPtr (fullAlignPad nvM6UnsatWorkPtr))) nvM6UnsatInitMem :=
    sep_ac hm_split0
  refine nvM6_full_init_state_nv_wp ⟨nvM6UnsatBytes,
    region (fullM6WorkBase nvM6UnsatWorkPtr) fullM6ExtBytes ⋆
      region nvM6UnsatWorkPtr (fullAlignPad nvM6UnsatWorkPtr),
    rfl, by decide, by decide, by decide, hm_split, fun _ _ hfail => ?_,
    fun c s j rest m1 hhdr hav hph hj hd hinv hcv hdcur hal hw hte hpr hcl hfu
      hun hprob hmc hmf hoom hinc hvals hwvec _ _ _ hm1 => ?_⟩
  · exfalso
    have hf := hfail 1 2 (nvM6UnsatBytes.drop 9) nvM6Unsat_header
    revert hf; rw [hpad]
    unfold fullFixedBytes valsBytes markBytes u32FullBytes fullMinDepthOf nvM6WorkLen fullM6ExtBytes
    decide
  · simp only [nvM6Unsat_header, Option.some.injEq, Prod.mk.injEq] at hph
    rcases hph with ⟨hmv, hnc, hrest⟩
    have hrest_len : (nvM6UnsatBytes.drop j).length = (nvM6UnsatBytes.drop 9).length := by
      rw [hd, hrest]
    have hj9 : j = 9 := by
      have h19 : nvM6UnsatBytes.length = 19 := rfl
      simp only [List.length_drop, h19] at hj hrest_len ⊢; omega
    subst hj9
    refine ⟨rfl, ?_⟩
    rw [← hhdr]
    have hlen_c := hinv.1.lengths
    have h2mv : 2 ≤ 2 * c.max_vars := by
      have hge := hlen_c.core_ok.cur_vars_ge
      have hle := hlen_c.core_ok.cur_vars_le
      omega
    have hut : UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv))
        (nvM6UnsatBytes.drop 9) c.nc := by
      rw [← hmv, ← hnc]
      have htake : (s.core.vals.take 2) = List.replicate 2 0#8 := by
        rw [hvals, List.take_replicate, Nat.min_eq_left h2mv]
      rw [htake]
      exact nvM6Unsat_unitTrace
    refine m5_parse_body_spec_wp ⟨c, s, nvM6CnfPtr, nvM6UnsatBytes, 9,
      region (fullM6WorkBase nvM6UnsatWorkPtr) fullM6ExtBytes ⋆
        region nvM6UnsatWorkPtr (fullAlignPad nvM6UnsatWorkPtr),
      rfl, rfl, by decide, by decide, ?_, hcv, hdcur, hcl, hte, hpr, hal, hoom, hprob, hinc,
      hvals, hwvec, hinv, hm1, fun r s' m2 hlen' _ _ _ _ h20 _ htr hm2 => ?_⟩
    · rw [← hmv, ← hnc]; exact nvM6Unsat_header
    · have hr20 : r = 20#64 := htr hut
      subst hr20
      obtain ⟨cnf, hp, hu⟩ := h20 rfl
      rw [parseDimacs_nvM6UnsatBytes, Option.some.injEq] at hp
      subst hp
      refine ⟨rfl, hu, ?_⟩
      have hstep : ∀ x,
          (FullMem c s' ⋆
            (region (fullM6WorkBase nvM6UnsatWorkPtr) fullM6ExtBytes ⋆
              region nvM6UnsatWorkPtr (fullAlignPad nvM6UnsatWorkPtr))) x →
          (region c.hdr c.avail ⋆
            (region (fullM6WorkBase nvM6UnsatWorkPtr) fullM6ExtBytes ⋆
              region nvM6UnsatWorkPtr (fullAlignPad nvM6UnsatWorkPtr))) x :=
        fun _ hx => sep_mono (fun _ ha => FullArenaInv.to_region ⟨hlen', ha⟩) hx
      have hm2_reg : (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
          region c.hdr c.avail ⋆
          (region (fullM6WorkBase nvM6UnsatWorkPtr) fullM6ExtBytes ⋆
            region nvM6UnsatWorkPtr (fullAlignPad nvM6UnsatWorkPtr))) m2 := by
        have hm2_p : (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
            (FullMem c s' ⋆
              (region (fullM6WorkBase nvM6UnsatWorkPtr) fullM6ExtBytes ⋆
                region nvM6UnsatWorkPtr (fullAlignPad nvM6UnsatWorkPtr)))) m2 :=
          sep_ac hm2
        exact sep_ac (sep_mono_r hstep hm2_p)
      have hm2_base : (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
          (region (fullM6WorkBase nvM6UnsatWorkPtr) fullM6ExtBytes ⋆
            region (fullM6WorkHdr nvM6UnsatWorkPtr)
              (nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr - fullM6ExtBytes)) ⋆
          region nvM6UnsatWorkPtr (fullAlignPad nvM6UnsatWorkPtr)) m2 := by
        have hch : c.hdr = fullM6WorkHdr nvM6UnsatWorkPtr := hhdr
        have hca : c.avail = nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr - fullM6ExtBytes := by
          rw [hav, hpad]; unfold nvM6WorkLen fullM6ExtBytes; decide
        rw [hch, hca] at hm2_reg
        exact sep_ac hm2_reg
      have hwb : (region (fullM6WorkBase nvM6UnsatWorkPtr) fullM6ExtBytes ⋆
          region (fullM6WorkHdr nvM6UnsatWorkPtr)
            (nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr - fullM6ExtBytes)) =
          region (fullM6WorkBase nvM6UnsatWorkPtr)
            (nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr) := by
        simpa [fullM6WorkHdr] using
          region_merge_eq (a := fullM6WorkBase nvM6UnsatWorkPtr) hsum
            (by unfold nvM6WorkLen; omega)
      rw [hwb] at hm2_base
      have hm2_pad : (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
          (region nvM6UnsatWorkPtr (fullAlignPad nvM6UnsatWorkPtr) ⋆
            region (fullM6WorkBase nvM6UnsatWorkPtr)
              (nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr))) m2 := sep_ac hm2_base
      have hfull_sum : fullAlignPad nvM6UnsatWorkPtr +
          (nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr) = nvM6WorkLen := by
        rw [hpad]; unfold nvM6WorkLen; decide
      have hwm := region_merge_eq (a := nvM6UnsatWorkPtr) hfull_sum hfit
      exact sep_mono_r (fun _ hr => (congrFun hwm _).mp hr) hm2_pad

/-- Real C0 `kissat_check_model` execution (`XPost := False`, `0` vacuous hypotheses) on the
concrete `nvM6Mem` witness (`(x1 ∨ x2)` with `3,456 B` `M6Hdr` prefix and `vals = [1, -1, 1, -1]`):
returns `ok = 1#64`, certifies `nvM6SatCnf.Sat (readModelFromWorkM6 m' nvM6SatWorkPtr)`, and
collapses the `8,192 B` workspace back to `region nvM6SatWorkPtr nvM6WorkLen`. -/
theorem nvM6_sat_checkModel_wp :
    Func.wp dimacsExactEnv kissat_check_model_body
      (nvM6CnfPtr, nvM6CnfPtr + BitVec.ofNat 64 nvM6SatBytes.length,
        nvM6SatCfg.hdr, nvM6SatCfg.pVals, BitVec.ofNat 64 nvM6SatCfg.mv, ())
      nvM6Mem
      (fun rs m' =>
        match rs with
        | (ok, ()) =>
          ok = 1#64 ∧
          nvM6SatCnf.Sat (readModelFromWorkM6 m' nvM6SatWorkPtr) ∧
          (bytes nvM6CnfPtr nvM6SatBytes ⋆ region nvM6SatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  have hm_m6 : (bytes nvM6CnfPtr nvM6SatBytes ⋆
      FullM6HdrMem nvM6SatCfg nvM6ExtInitWords nvM6SatState ⋆ emp) nvM6Mem := by
    rw [Std.ExtHashMap.sep_emp]
    exact nvM6Mem_ok
  have hm_chk := m6HdrMem_to_checkModel nvM6Sat_lengths hm_m6
  refine dimacs_check_model_spec_wp ⟨BitVec.ofNat 64 nvM6SatCfg.mv,
    BitVec.ofNat 64 nvM6SatCfg.nc, nvM6SatState.core.d_cur, nvM6SatState.core.d_val,
    nvM6SatBytes, nvM6SatState.core.vals.map UInt8.ofBitVec, nvM6SatCfg.mv,
    FullCheckRest nvM6SatCfg nvM6SatState ⋆ array64 (nvM6SatCfg.hdr - 2304) nvM6ExtInitWords ⋆
      emp,
    rfl, rfl, by decide, by decide, by decide, by decide, hm_chk,
    fun ok mv' nc' cur' val' m' hok hm' => ?_⟩
  have hrun : runKissatCheckModel nvM6SatBytes (nvM6SatState.core.vals.map UInt8.ofBitVec)
      nvM6SatCfg.mv = true := rfl
  have hok1 : ok = 1#64 := by rw [hok, hrun]; rfl
  have hm_post : (dimacsState nvM6SatCfg.hdr mv' nc' cur' val' ⋆
      bytes nvM6SatCfg.pVals (nvM6SatState.core.vals.map UInt8.ofBitVec) ⋆
      FullCheckRest nvM6SatCfg nvM6SatState ⋆
      (bytes nvM6CnfPtr nvM6SatBytes ⋆ array64 (nvM6SatCfg.hdr - 2304) nvM6ExtInitWords ⋆
        emp)) m' := sep_ac hm'
  obtain ⟨cnf, hp, _, _, hsat⟩ :=
    sat_of_checkModel_post_m6 nvM6SatCfg_hdr_eq nvM6Sat_lengths hm_post hrun
  rw [parseDimacs_nvM6SatBytes, Option.some.injEq] at hp
  subst hp
  have hsat' := hsat emp m' (by rw [Std.ExtHashMap.sep_emp])
  have hpad0 : fullAlignPad nvM6SatWorkPtr = 0 := nvM6Sat_pad_eq
  have hm_reg_pad : (bytes nvM6CnfPtr nvM6SatBytes ⋆
      dimacsState nvM6SatCfg.hdr mv' nc' cur' val' ⋆
      bytes nvM6SatCfg.pVals (nvM6SatState.core.vals.map UInt8.ofBitVec) ⋆
      (FullCheckRest nvM6SatCfg nvM6SatState ⋆
        array64 (nvM6SatCfg.hdr - 2304) nvM6ExtInitWords ⋆
        region nvM6SatWorkPtr (fullAlignPad nvM6SatWorkPtr) ⋆ emp)) m' := by
    rw [hpad0, region_zero, Std.ExtHashMap.sep_emp]
    exact sep_ac hm'
  have hreg := checkModel_post_to_m6_region (R := emp)
    (by rw [hpad0]; decide) (by decide)
    nvM6SatCfg_hdr_eq rfl nvM6ExtInitWords_ok nvM6Sat_lengths hm_reg_pad
  rw [Std.ExtHashMap.sep_emp] at hreg
  exact ⟨hok1, hsat', hreg⟩

private theorem fullExtendSpec_weaken {Q1 Q2 : Post []} {X : XPost}
    (himp : ∀ r m1, Q1 r m1 → Q2 r m1) {a : Tup Val [i64]} {m0 : Mem 64}
    (h : fullExtendSpec a m0 Q1 X) : fullExtendSpec a m0 Q2 X := by
  rcases a with ⟨hptr, ⟨⟩⟩
  obtain ⟨c, s, R, hp, hs, hm, hQ⟩ := h
  exact ⟨c, s, R, hp, hs, hm, fun r s' m1 hpr hs' hpo hm1 =>
    himp r m1 (hQ r s' m1 hpr hs' hpo hm1)⟩

/-- Real C0 `full_extend` + `kissat_check_model` zero-drag post-hoc execution (`XPost := False`)
in `FullM5.mkM5Env fullSolveBytesSpec` on concrete `nvM6Mem`: exercises
`fullM6_extend_check_cont` end-to-end. -/
theorem nvM6_sat_extend_check_wp :
    Func.wp (FullM5.mkM5Env fullSolveBytesSpec) full_extend_body
      (nvM6SatCfg.hdr, ()) nvM6Mem
      (fun _ m1 =>
        Func.wp (FullM5.mkM5Env fullSolveBytesSpec) kissat_check_model_body
          (nvM6CnfPtr, nvM6CnfPtr + BitVec.ofNat 64 nvM6SatBytes.length,
            nvM6SatCfg.hdr, nvM6SatCfg.pVals, BitVec.ofNat 64 nvM6SatCfg.mv, ()) m1
          (fun rs2 m2 =>
            match rs2 with
            | (ok, ()) =>
              ((if ok == 1#64 then 10#64 else 0#64) = 10#64 ∧
                nvM6SatCnf.Sat (readModelFromWorkM6 m2 nvM6SatWorkPtr) ∧
                (bytes nvM6CnfPtr nvM6SatBytes ⋆ region nvM6SatWorkPtr nvM6WorkLen) m2) ∨
              (if ok == 1#64 then 10#64 else 0#64) ≠ 10#64)
          (fun _ _ _ _ => False))
      (fun _ _ _ _ => False) := by
  have hpad0 : fullAlignPad nvM6SatWorkPtr = 0 := nvM6Sat_pad_eq
  have hm_pad : (bytes nvM6CnfPtr nvM6SatBytes ⋆
      FullM6HdrMem nvM6SatCfg nvM6ExtInitWords nvM6SatState ⋆
      region nvM6SatWorkPtr (fullAlignPad nvM6SatWorkPtr) ⋆ emp) nvM6Mem := by
    rw [hpad0, region_zero, Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_emp]
    exact nvM6Mem_ok
  have hcont := fullM6_extend_check_cont
    (cnf_ptr := nvM6CnfPtr) (cnf_end := nvM6CnfPtr + BitVec.ofNat 64 nvM6SatBytes.length)
    (work_ptr := nvM6SatWorkPtr) (cnfBytes := nvM6SatBytes) (wlen := nvM6WorkLen)
    (c := nvM6SatCfg) (ext := nvM6ExtInitWords) (s := nvM6SatState) (R := emp)
    (m := nvM6Mem) (X := fun _ _ _ _ => False)
    (K := fun r m2 =>
      (r = 10#64 ∧ nvM6SatCnf.Sat (readModelFromWorkM6 m2 nvM6SatWorkPtr) ∧
        (bytes nvM6CnfPtr nvM6SatBytes ⋆ region nvM6SatWorkPtr nvM6WorkLen) m2) ∨
      r ≠ 10#64)
    rfl (by decide) (by decide)
    (by rw [hpad0]; unfold nvM6WorkLen fullM6HdrTotalBytes; omega)
    nvM6SatCfg_hdr_eq (by rw [hpad0]; rfl)
    nvM6ExtInitWords_ok nvM6Sat_lengths (by decide) hm_pad
    (fun r m2 _ _ h10 hm2 => by
      by_cases hr : r = 10#64
      · subst hr
        obtain ⟨cnf, hp, hsat⟩ := h10 rfl
        rw [parseDimacs_nvM6SatBytes, Option.some.injEq] at hp
        subst hp
        rw [Std.ExtHashMap.sep_emp] at hm2
        exact Or.inl ⟨rfl, hsat emp m2 (by rw [Std.ExtHashMap.sep_emp]), hm2⟩
      · exact Or.inr hr)
  refine m5_extend_spec_wp (fullExtendSpec_weaken (fun _ m1 h1 => ?_) hcont)
  obtain ⟨s1, _, _, hchk⟩ := h1
  have hm := FullM5.mkM5Env_moduleOk fullSolveBytesSpec
    (fun _ _ _ _ hs => fullSolveBytesCoreSpec_of_spec hs)
  have hfn := (hm.fnsOk (FullM5.m5Module.fns.take 7)
    ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissat_check_model_body⟩
    (FullM5.m5Module.fns.drop 8) rfl).2.2
  exact hfn _ m1 _ _ (FullM5.mkM5Env_check_model fullSolveBytesSpec _ m1 _ _ hchk)

/-! ## 4. Concrete Tier-3b Non-Vacuity Theorems (`fullM6_unsat_nv`, `fullM6_sat_nv`) -/

/-- **Concrete Tier-3b UNSAT Non-Vacuity (`fullM6_unsat_nv`)**:
For ANY `solveBody` satisfying `fullM6SolveBytesCoreModelSpec` on concrete `8,192 B`
`nvM6UnsatInitMem` (`(x1) ∧ (~x1)`, `M6Hdr` `3,456 B` layout, `pad = 5`), all preconditions
are concretely satisfiable (`0` vacuous hypotheses, `XPost := False`), deterministically yielding
`r = 20#64`, `nvM6UnsatCnf.Unsat`, and restored workspace region. -/
theorem fullM6_unsat_nv (Γ : Env) (solveBody : Func [i64, i64, i64, i64, i64] [i64])
    (hwp : ∀ (a : Tup Val [i64, i64, i64, i64, i64]) (m : Mem 64)
      (Q : Post [i64]) (X : XPost),
      fullM6SolveBytesCoreModelSpec a m Q X → Func.wp Γ solveBody a m Q X) :
    Func.wp Γ solveBody
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  have hm0 : (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen ⋆ emp)
      nvM6UnsatInitMem := by
    rw [Std.ExtHashMap.sep_emp]
    exact nvM6UnsatInitMem_sep
  refine hwp _ _ _ _ (fullM6SolveBytesCoreModelSpec_intro (by decide) (by decide) hm0
    fun r m' _ _ _ htr hm' => ?_)
  have hr20 : r = 20#64 := htr 1 2 9 (by decide) (by decide) (by decide) nvM6_unsat_bound
    (by decide) nvM6Unsat_header nvM6Unsat_unitTrace
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨hr20, nvM6UnsatCnf_unsat, hm'⟩

/-- **Concrete Tier-3b SAT Non-Vacuity (`fullM6_sat_nv`)**:
For ANY `solveBody` satisfying `fullM6SolveBytesSpec` on concrete `8,192 B` `nvM6SatInitMem`
(`(x1 ∨ x2)`, `M6Hdr` `3,456 B` layout), all preconditions are concretely satisfiable (`0` vacuous
hypotheses, `XPost := False`): `r = 20#64` is impossible (`¬ nvM6SatCnf.Unsat`), `r ∈ {0, 10}`,
and `r = 10#64` guarantees constructive `nvM6SatCnf.Sat (readModelFromWorkM6 M nvM6SatWorkPtr)`
for every host memory extension `(Eq m' ⋆ F) M`. -/
theorem fullM6_sat_nv (Γ : Env) (solveBody : Func [i64, i64, i64, i64, i64] [i64])
    (hwp : ∀ (a : Tup Val [i64, i64, i64, i64, i64]) (m : Mem 64)
      (Q : Post [i64]) (X : XPost),
      fullM6SolveBytesSpec a m Q X → Func.wp Γ solveBody a m Q X) :
    Func.wp Γ solveBody
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6SatBytes.length,
        nvM6SatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6SatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64) ∧ r ≠ 20#64 ∧
          (r = 10#64 →
            ¬ nvM6SatCnf.Unsat ∧
            (∀ (F : Mem 64 → Prop) (M : Mem 64),
              (Eq m' ⋆ F) M → nvM6SatCnf.Sat (readModelFromWorkM6 M nvM6SatWorkPtr))) ∧
          (bytes nvM6CnfPtr nvM6SatBytes ⋆ region nvM6SatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  have hm0 : (bytes nvM6CnfPtr nvM6SatBytes ⋆ region nvM6SatWorkPtr nvM6WorkLen ⋆ emp)
      nvM6SatInitMem := by
    rw [Std.ExtHashMap.sep_emp]
    exact nvM6SatInitMem_sep
  refine hwp _ _ _ _ (fullM6SolveBytesSpec_intro (by decide) (by decide) hm0 ?_)
  intro r m' hdom h20 h10 hm'
  have hrne20 : r ≠ 20#64 := by
    intro h20eq
    obtain ⟨cnf, hp, hu⟩ := h20 h20eq
    rw [parseDimacs_nvM6SatBytes, Option.some.injEq] at hp
    subst hp
    exact nvM6SatCnf_not_unsat hu
  have hdom' : r = 0#64 ∨ r = 10#64 := by
    rcases hdom with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact False.elim (hrne20 rfl)
  refine ⟨hdom', hrne20, fun hr10 => ?_, ?_⟩
  · obtain ⟨cnf, hp, hsat⟩ := h10 hr10
    rw [parseDimacs_nvM6SatBytes, Option.some.injEq] at hp
    subst hp
    exact ⟨nvM6SatCnf_not_unsat, hsat⟩
  · rwa [Std.ExtHashMap.sep_emp] at hm'

end LeanQbe.T.Examples.Kissat.FullM6
