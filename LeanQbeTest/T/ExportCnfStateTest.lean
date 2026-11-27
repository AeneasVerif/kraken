/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.ExportCnfState
public import LeanQbe.T.Examples.Kissat.ExportCnfStateProof
public import LeanQbe.T.Examples.Kissat.ExportCnfFmtProof
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.InterpKissat
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation
meta import LeanQbe.T.Examples.Kissat.ExportCnfState
meta import LeanQbe.T.Examples.Kissat.ExportCnfStateProof
meta import LeanQbe.T.Examples.Kissat.ExportCnfFmtProof
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.InterpKissat
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal
meta import LeanQbe.T.Frontend.C0

/-!
# Verification, Functional, and Codegen Tests for `ExportCnfState`

* Structural `#guard` checks: 9 functions (`4` formatter + `5` state exporter), acyclicity,
  sole Kissat extern `full_backtrack`, `0` exits, `<= 6` args, C0/C99 parser acceptance,
  `PrintCpp`, `PrintQbe`, and `Legal` across `aarch64`, `scalar64`, `x64AVX2`, `x64AVX512`.
* Pure state-extractor & `parseDimacs` round-trip `#guard` checks:
  - inconsistent state -> `"p cnf 0 1\n0\n"` (`12` bytes);
  - consistent simplified state with level-0 trail units, deduplicated binary watches (`l0 < l1`)
    mixed with 2-word non-binary watches, live irredundant, redundant (`PH_RED`), garbage
    (`PH_GARB`), and shrunk (`PH_SHRK` + padding + `0xFFFFFFFF` sentinel) arena clauses.
* End-to-end executable `interpModule` `#guard` checks running `kissat_export_cnf_bytes` on
  concrete `Mem 64` `FullHdr` states (inconsistent full-write, inconsistent insufficient-capacity,
  consistent 2-pass simplified state full-write & dry-run) and verifying exact DIMACS output and
  `parseDimacs` round-trip.
* WP soundness & non-vacuity witnesses (`XPost := False`, `<= std3`) for:
  - inconsistent state -> `"p cnf 0 1\n0\n"` and `F0.Unsat`,
  - dry-run (`buf = []`) -> returns `0`, buffer untouched, exact byte length stored,
  - 1-based input DIMACS end-to-end `cnfOut.Unsat → cnfIn.Unsat`.
* `#print axioms` audit (`<= std3`).
-/

set_option autoImplicit false

namespace LeanQbeTest.T.ExportCnfStateTest

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.ExportCnfFmt
open LeanQbe.T.Examples.Kissat.ExportCnfState

/-! ## 1. Structural, C0/C99 Parse, and Backend Legalization `#guard` Checks -/

#guard exportCnfStateMod.fns.length == 9
#guard exportCnfStateMod.checkAcyclic == true
#guard exportCnfStateMod.exits.isEmpty
#guard exportCnfStateMod.externs == [⟨"full_backtrack", [i64, i64], []⟩]
#guard (exportCnfStateMod.fns.map (·.name)).Nodup
#guard exportCnfStateMod.fns.all fun f => f.as.length ≤ 6
#guard (parseC0 exportCnfStateC0Src).isOk
#guard (ppTModule exportCnfStateMod).isOk
#guard (PrintQbe.module exportCnfStateMod).isOk
#guard [LegalTarget.aarch64, .scalar64, .x64AVX2, .x64AVX512].all fun t =>
  (ppModule (exportCnfStateAllFns.map (Fn.legal t))).isOk

/-! ## 2. Pure Clause-Extractor & Executable `interpModule` Functional Checks -/

public section

/-- False exit postcondition witnessing zero `.exit` transitions. -/
abbrev nvXFalse : XPost := fun _ _ _ _ => False

end

private def cnfLits (cnf : CNF Nat) : List (List (Nat × Bool)) :=
  cnf.clauses.toList.map (·.literals)

private def parseDimacsMatches (bs : List UInt8) (expected : CNF Nat) : Bool :=
  match parseDimacs bs with
  | some got => cnfLits got == cnfLits expected
  | none => false

private def readSlice (m : Mem 64) (base : BitVec 64) (n : Nat) : Option (List UInt8) :=
  (List.range n).mapM fun i => do
    let b ← loadVal m i8 (base + BitVec.ofNat 64 i)
    pure (UInt8.ofNat b.toNat)

private def writeU64s (m : Mem 64) (base : BitVec 64) (ws : List (BitVec 64)) : Mem 64 :=
  (ws.zipIdx).foldl (fun acc (v, i) => storeMem acc i64 (base + BitVec.ofNat 64 (8 * i)) v) m

private def writeU32s (m : Mem 64) (base : BitVec 64) (ws : List (BitVec 32)) : Mem 64 :=
  (ws.zipIdx).foldl (fun acc (v, i) => storeMem acc i32 (base + BitVec.ofNat 64 (4 * i)) v) m

private def emptyCoreState : FullCoreState :=
  { d_cur := 0, d_val := 0, cur_vars := 0, unassigned := 0, arena_len := 0, wlen := 0,
    wusable := 0, arena_garbage := 0, first_reducible := 0, num_irred := 0, num_redundant := 0,
    num_binary := 0, unflushed := 0, probing := 0, trail_end := 0, propagated := 0,
    cur_level := 0, fuel := 0, confl_ref := 0, confl_type := 0, confl_lit0 := 0,
    confl_lit1 := 0, tmp_cnt := 0, tmp_len := 0, min_clr_len := 0, min_clr_full := 0,
    oom := 0, dense_mode := 0, inconsistent := 0, vals := [], lit_mark := [], mrk := [],
    flags := [], lvl := [], rsns := [], trl := [], trail_pos := [], tmp := [], min_clr := [],
    frame_trail := [], frame_dec := [], wvec := [], repr := [], min_stk := [], arena := [],
    wstk := [] }

-- Sample simplified state over 3 variables (literals 0..5 = +1, -1, +2, -2, +3, -3):
-- * Trail units (`trail_end = 1`): `[0#32]` -> `[0]` (`1 0\n`); `trl[1] = 5#32` ignored.
-- * Watches:
--   - `l0 = 2` (+2): binary `(PW_BIN_FLAG ||| 5)` (+2 v -3, emitted since `2 < 5`),
--     followed by 2-word non-binary entry `[0x00000001, 0x80000004]` (skipped cleanly!).
--   - `l0 = 5` (-3): mirror binary `(PW_BIN_FLAG ||| 2)` (skipped since `¬(5 < 2)`!).
-- * Arena (`arena_len = 25`):
--   - cref 0: live irredundant 3-lit `[0, 3, 4]` (`hdr = 0`) -> emitted!
--   - cref 6: redundant (`PH_RED = 0x00400000`) -> skipped!
--   - cref 12: garbage (`PH_GARB = 0x00080000`) -> skipped!
--   - cref 18: shrunk live irredundant (`PH_SHRK = 0x00800000`, `sz = 3`, lits `[1, 2, 5]`,
--     pad `0x00000007`, sentinel `0xFFFFFFFF`) -> emitted, next = 26 -> stops!
private def sampleTrl : List (BitVec 32) := [0#32, 5#32]

private def sampleWvec : List (BitVec 32) :=
  [0#32, 0#32, 0#32, 0#32, 0#32, 3#32, 0#32, 0#32, 0#32, 0#32, 3#32, 1#32]

private def sampleWstk : List (BitVec 32) :=
  [0x80000005#32, 0x00000001#32, 0x80000004#32, 0x80000002#32]

private def sampleArena : List (BitVec 32) :=
  [ 0x00000000#32, 0#32, 3#32, 0#32, 3#32, 4#32,
    0x00400000#32, 0#32, 3#32, 1#32, 2#32, 4#32,
    0x00080000#32, 0#32, 3#32, 0#32, 2#32, 5#32,
    0x00800000#32, 0#32, 3#32, 1#32, 2#32, 5#32, 0x00000007#32, 0xFFFFFFFF#32 ]

private def sampleCore : FullCoreState :=
  { emptyCoreState with
    cur_vars := 3, trl := sampleTrl, trail_end := 1,
    wvec := sampleWvec, wstk := sampleWstk, wlen := 4,
    arena := sampleArena, arena_len := sampleArena.length }

private def sampleInconsCore : FullCoreState :=
  { sampleCore with inconsistent := 1#64 }

private def sampleExpectedDimacs : String :=
  "p cnf 3 4\n1 0\n2 -3 0\n1 -2 3 0\n-1 2 -3 0\n"

#guard exportTrailUnitClauses sampleCore == [[0]]
#guard exportBinClauses sampleCore == [[2, 5]]
#guard exportArenaClauses sampleCore == [[0, 3, 4], [1, 2, 5]]
#guard exportStateClauses sampleCore == [[0], [2, 5], [0, 3, 4], [1, 2, 5]]
#guard exportStateBytes sampleCore == sampleExpectedDimacs.toUTF8.toList
#guard parseDimacsMatches (exportStateBytes sampleCore)
  (kissatCnfToDimacs [[0], [2, 5], [0, 3, 4], [1, 2, 5]])
#guard exportStateBytes sampleInconsCore == "p cnf 0 1\n0\n".toUTF8.toList
#guard parseDimacsMatches (exportStateBytes sampleInconsCore) (kissatCnfToDimacs [[]])

private def buildSampleMem (incons : BitVec 64) (cap : Nat) :
    Mem 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let hdr : BitVec 64 := 0x10000#64
  let pTrl : BitVec 64 := 0x20000#64
  let pWvec : BitVec 64 := 0x21000#64
  let pWstk : BitVec 64 := 0x22000#64
  let pAr : BitVec 64 := 0x23000#64
  let pOut : BitVec 64 := 0x30000#64
  let pLen : BitVec 64 := 0x40000#64
  let m0 := writeU64s (∅ : Mem 64) hdr (List.replicate 144 0#64)
  let m1 := storeMem m0 i64 (hdr + 8 * 6) (BitVec.ofNat 64 sampleArena.length)
  let m2 := storeMem m1 i64 (hdr + 8 * 7) 4#64
  let m3 := storeMem m2 i64 (hdr + 8 * 12) pTrl
  let m4 := storeMem m3 i64 (hdr + 8 * 13) pWvec
  let m5 := storeMem m4 i64 (hdr + 8 * 14) pAr
  let m6 := storeMem m5 i64 (hdr + 8 * 15) pWstk
  let m7 := storeMem m6 i64 (hdr + 8 * 18) 1#64
  let m8 := storeMem m7 i64 (hdr + 8 * 20) 0#64
  let m9 := storeMem m8 i64 (hdr + 8 * 97) 3#64
  let m10 := storeMem m9 i64 (hdr + 8 * 128) incons
  let m11 := writeU32s m10 pTrl sampleTrl
  let m12 := writeU32s m11 pWvec sampleWvec
  let m13 := writeU32s m12 pWstk sampleWstk
  let m14 := writeU32s m13 pAr sampleArena
  let m15 := (List.range cap).foldl
    (fun acc i => storeMem acc i8 (pOut + BitVec.ofNat 64 i) (0xAA : BitVec 8)) m14
  let m16 := storeMem m15 i64 pLen 999#64
  (m16, hdr, pOut, pLen)

private def checkInterpConsistentFull : Bool :=
  let (m0, hdr, pOut, pLen) := buildSampleMem 0#64 64
  let want := sampleExpectedDimacs.toUTF8.toList
  match interpModule exportCnfStateMod 50000 "kissat_export_cnf_bytes"
      [i64, i64, i64, i64] [i64] (hdr, pOut, 64#64, pLen, ()) m0 with
  | .ok (r, ()) m1 =>
    r == 1#64 &&
    loadVal m1 i64 pLen == some (BitVec.ofNat 64 want.length) &&
    readSlice m1 pOut want.length == some want &&
    parseDimacsMatches want (kissatCnfToDimacs [[0], [2, 5], [0, 3, 4], [1, 2, 5]])
  | _ => false

private def checkInterpConsistentDryRun : Bool :=
  let (m0, hdr, pOut, pLen) := buildSampleMem 0#64 8
  let wantLen := sampleExpectedDimacs.toUTF8.toList.length
  match interpModule exportCnfStateMod 50000 "kissat_export_cnf_bytes"
      [i64, i64, i64, i64] [i64] (hdr, pOut, 8#64, pLen, ()) m0 with
  | .ok (r, ()) m1 =>
    r == 0#64 &&
    loadVal m1 i64 pLen == some (BitVec.ofNat 64 wantLen) &&
    readSlice m1 pOut 8 == some (List.replicate 8 (0xAA : UInt8))
  | _ => false

private def checkInterpInconsistent : Bool :=
  let want := "p cnf 0 1\n0\n".toUTF8.toList
  let (m0, hdr, pOut, pLen) := buildSampleMem 1#64 16
  let okFull :=
    match interpModule exportCnfStateMod 50000 "kissat_export_cnf_bytes"
        [i64, i64, i64, i64] [i64] (hdr, pOut, 16#64, pLen, ()) m0 with
    | .ok (r, ()) m1 =>
      r == 1#64 &&
      loadVal m1 i64 pLen == some 12#64 &&
      readSlice m1 pOut 12 == some want
    | _ => false
  let (m0s, hdrs, pOuts, pLens) := buildSampleMem 1#64 4
  let okShort :=
    match interpModule exportCnfStateMod 50000 "kissat_export_cnf_bytes"
        [i64, i64, i64, i64] [i64] (hdrs, pOuts, 4#64, pLens, ()) m0s with
    | .ok (r, ()) m1 =>
      r == 0#64 &&
      loadVal m1 i64 pLens == some 12#64 &&
      readSlice m1 pOuts 4 == some (List.replicate 4 (0xAA : UInt8))
    | _ => false
  okFull && okShort

#guard checkInterpConsistentFull
#guard checkInterpConsistentDryRun
#guard checkInterpInconsistent

/-! ## 3. WP Soundness & Non-Vacuity Witnesses (`XPost := False`, `<= std3`) -/

public section

/-- Closed-module certification witness for `exportCnfStateMod`. -/
theorem nv_export_cnf_state_moduleOk : ModuleOk exportCnfStateEnv exportCnfStateMod :=
  exportCnfStateEnv_moduleOk

/-- WP soundness witness for the inconsistent branch (`s.core.inconsistent ≠ 0`, `buf.length ≥ 12`),
including optional level-0 backtrack: returns `1`, emits `"p cnf 0 1\n0\n"` (`12` bytes), parses
to the empty-clause CNF, and implies `F0.Unsat`. -/
theorem nv_export_cnf_bytes_inconsistent_wp
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {out out_len_ptr old_len : BitVec 64} {buf : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hcap : buf.length < 2 ^ 64)
    (hge12 : 12 ≤ buf.length)
    (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core)
    (hinc : s.core.inconsistent ≠ 0#64)
    (hm : (FullMem c s ⋆ bytes out buf ⋆ cell64 out_len_ptr old_len ⋆ R) m) :
    Func.wp exportCnfStateEnv kissat_export_cnf_bytes_body
      (c.hdr, out, BitVec.ofNat 64 buf.length, out_len_ptr, ()) m
      (fun (r, ()) m' =>
        r = 1#64 ∧
        F0.Unsat ∧
        ∃ s' : FullState,
          s'.LengthsOk c ∧
          FullWitnessInv c F0 F_cur s'.core ∧
          s'.core.cur_level = 0 ∧
          (FullMem c s' ⋆ bytes out (emitDimacsBytes 0 [[]] ++ buf.drop 12) ⋆
            cell64 out_len_ptr 12#64 ⋆ R) m')
      nvXFalse := by
  refine kissat_export_cnf_bytes_sound _ m _ nvXFalse
    ⟨c, F0, F_cur, s, out, out_len_ptr, old_len, buf, R, rfl, hcap, hlen, hw, hm, ?_⟩
  intro r s' outBytes written m' hlen' hw' hl0 _ hinc' _ _ _ _ _ _ _ hr _ h0 h1
  have hinc_s' : s'.core.inconsistent ≠ 0#64 := hinc' ▸ hinc
  have hbs : exportStateBytes s'.core = emitDimacsBytes 0 [[]] := by
    simp [exportStateBytes, exportStateMv, exportStateClauses, hinc_s']
  have hblen : (exportStateBytes s'.core).length = 12 := by rw [hbs]; decide
  rcases hr with rfl | rfl
  · obtain ⟨_, hbound, _⟩ := h0 rfl
    have hmv0 : exportStateMv s'.core < dimacsBound := by
      simp [exportStateMv, hinc_s', dimacsBound]
    have hnc1 : (exportStateClauses s'.core).length < dimacsBound := by
      simp [exportStateClauses, hinc_s', dimacsBound]
    obtain ⟨hw_eq, hlt⟩ := hbound hmv0 hnc1
    omega
  · obtain ⟨hout_eq, hw_eq, _, ⟨cnfOut, _, hcnf_eq, hu⟩, hm'⟩ := h1 rfl
    have hcl_eq : exportStateClauses s'.core = [[]] := by
      simp [exportStateClauses, hinc_s']
    have hunsat_out : cnfOut.Unsat := by
      rw [hcnf_eq, hcl_eq]
      intro α
      rw [Bool.eq_false_iff]
      intro hsat
      have hsat_cl : (CNF.Clause.ofLiterals ([] : List (Literal Nat))).Sat α := by
        refine (CNF.sat_iff_all_mem_sat.mp hsat) _ ?_
        rw [CNF.Internal.mem_iff, kissatCnfToDimacs]
        simp [kissatClauseToDimacs]
      obtain ⟨l, hmem, _⟩ := CNF.Clause.sat_iff_exists_mem_eq.mp hsat_cl
      rw [← CNF.Clause.mem_literals_iff, CNF.Clause.literals_ofLiterals] at hmem
      cases hmem
    have hw12 : written = 12 := by rw [hw_eq, hout_eq, hblen]
    refine ⟨rfl, hu hunsat_out, s', hlen', hw', hl0, ?_⟩
    simpa [hout_eq, hbs, hw12] using hm'

/-- WP dry-run witness (`buf = []`, `cap = 0`): returns `0`, never touches `out`, and when
`(mv, nc)` fit in `dimacsBound`, stores the exact required byte length in `*out_len_ptr`. -/
theorem nv_export_cnf_bytes_dryrun_wp
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {out out_len_ptr old_len : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core)
    (hm : (FullMem c s ⋆ bytes out [] ⋆ cell64 out_len_ptr old_len ⋆ R) m) :
    Func.wp exportCnfStateEnv kissat_export_cnf_bytes_body
      (c.hdr, out, 0#64, out_len_ptr, ()) m
      (fun (r, ()) m' =>
        r = 0#64 ∧
        ∃ (s' : FullState) (written : Nat),
          s'.LengthsOk c ∧
          FullWitnessInv c F0 F_cur s'.core ∧
          s'.core.cur_level = 0 ∧
          (exportStateMv s'.core < dimacsBound →
            (exportStateClauses s'.core).length < dimacsBound →
            written = (exportStateBytes s'.core).length) ∧
          (FullMem c s' ⋆ bytes out [] ⋆
            cell64 out_len_ptr (BitVec.ofNat 64 written) ⋆ R) m')
      nvXFalse := by
  refine kissat_export_cnf_bytes_sound _ m _ nvXFalse
    ⟨c, F0, F_cur, s, out, out_len_ptr, old_len, [], R, rfl, by decide, hlen, hw, hm, ?_⟩
  intro r s' outBytes written m' hlen' hw' hl0 _ _ _ _ _ _ _ _ _ hr _ h0 h1
  rcases hr with rfl | rfl
  · obtain ⟨_, hbound, hm'⟩ := h0 rfl
    exact ⟨rfl, s', written, hlen', hw', hl0, fun h1 h2 => (hbound h1 h2).1, hm'⟩
  · obtain ⟨hout_eq, hw_eq, hle0, _, _⟩ := h1 rfl
    have hpos : 0 < (exportStateBytes s'.core).length := by
      unfold exportStateBytes emitDimacsBytes emitDimacsHdrBytes dimacsHeaderPrefix
      simp
    simp only [List.length_nil] at hle0
    rw [hw_eq, hout_eq] at hle0
    omega

/-- End-to-end 1-based DIMACS WP soundness witness (`XPost := False`): when `r = 1#64`,
`outBytes` parses via `LratBytes.parseDimacs` to a valid `cnfOut` with `cnfOut.Unsat → cnfIn.Unsat`.
-/
theorem nv_export_cnf_bytes_dimacs_unsat_wp
    {c : FullCfg} {cnfIn : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {out out_len_ptr old_len : BitVec 64} {buf : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hcap : buf.length < 2 ^ 64)
    (hlen : s.LengthsOk c)
    (hpos : CnfVarsPos cnfIn)
    (hw : FullWitnessInv c (shiftDownCnf cnfIn) F_cur s.core)
    (hm : (FullMem c s ⋆ bytes out buf ⋆ cell64 out_len_ptr old_len ⋆ R) m) :
    Func.wp exportCnfStateEnv kissat_export_cnf_bytes_body
      (c.hdr, out, BitVec.ofNat 64 buf.length, out_len_ptr, ()) m
      (fun (r, ()) m' =>
        ∃ (s' : FullState) (outBytes : List UInt8) (written : Nat),
          s'.LengthsOk c ∧
          FullWitnessInv c (shiftDownCnf cnfIn) F_cur s'.core ∧
          s'.core.cur_level = 0 ∧
          (r = 0#64 ∨ r = 1#64) ∧
          (r = 0#64 →
            (FullMem c s' ⋆ bytes out buf ⋆
              cell64 out_len_ptr (BitVec.ofNat 64 written) ⋆ R) m') ∧
          (r = 1#64 →
            outBytes = exportStateBytes s'.core ∧
            written = outBytes.length ∧
            written ≤ buf.length ∧
            (∃ cnfOut : CNF Nat,
              parseDimacs outBytes = some cnfOut ∧
              (cnfOut.Unsat → cnfIn.Unsat)) ∧
            (FullMem c s' ⋆ bytes out (outBytes ++ buf.drop written) ⋆
              cell64 out_len_ptr (BitVec.ofNat 64 written) ⋆ R) m'))
      nvXFalse :=
  kissat_export_cnf_bytes_sound_dimacs hcap hlen hpos hw hm

end

/-! ## 4. Axiom Audit (`<= std3`) -/

#print axioms LeanQbe.T.Examples.Kissat.ExportCnfState.kissat_export_arena_next_wf
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfState.kissat_export_trail_units_wf
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfState.kissat_export_bin_clauses_wf
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfState.kissat_export_arena_clauses_wf
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfState.kissat_export_cnf_bytes_wf
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfState.exportCnfStateAllFns_wf
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfState.exportCnfStateMod_checkAcyclic
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfState.exportCnfStateMod_namesNodup
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfState.exportCnfStateAllFns_max6args
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfState.exportStateBytes_sound
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfState.exportStateBytes_sound_dimacs
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfState.kissat_export_arena_next_wp
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfState.kissat_export_trail_units_wp
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfState.kissat_export_bin_clauses_wp
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfState.kissat_export_arena_clauses_wp
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfState.kissat_export_cnf_bytes_wp
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfState.exportCnfStateFns_sound_in
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfState.exportCnfStateEnv_sound
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfState.exportCnfStateEnv_moduleOk
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfState.kissat_export_cnf_bytes_sound
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfState.kissat_export_cnf_bytes_sound_dimacs
#print axioms LeanQbeTest.T.ExportCnfStateTest.nv_export_cnf_state_moduleOk
#print axioms LeanQbeTest.T.ExportCnfStateTest.nv_export_cnf_bytes_inconsistent_wp
#print axioms LeanQbeTest.T.ExportCnfStateTest.nv_export_cnf_bytes_dryrun_wp
#print axioms LeanQbeTest.T.ExportCnfStateTest.nv_export_cnf_bytes_dimacs_unsat_wp

end LeanQbeTest.T.ExportCnfStateTest
