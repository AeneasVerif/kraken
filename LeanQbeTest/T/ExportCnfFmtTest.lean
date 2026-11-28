/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanQbe.T.Examples.Kissat.ExportCnfFmt
import LeanQbe.T.Examples.Kissat.ExportCnfFmtProof
import LeanQbe.T.Examples.LratBytes
import LeanQbe.T.InterpKissat
import LeanQbe.T.PrintCpp
import LeanQbe.T.PrintQbe
import LeanQbe.T.Legal
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation
meta import LeanQbe.T.Examples.Kissat.ExportCnfFmt
meta import LeanQbe.T.Examples.Kissat.ExportCnfFmtProof
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.InterpKissat
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal
meta import LeanQbe.T.Frontend.C0

/-!
# Verification, Non-Vacuity, and Codegen Tests for `ExportCnfFmt`

* Structural `#guard` checks: 4 functions, acyclicity, zero exits/externs, `<= 6` args,
  C0/C99 parser acceptance, `PrintCpp`, `PrintQbe`, and `Legal` across `aarch64`, `scalar64`,
  `x64AVX2`, `x64AVX512`.
* Executable `interpModule` tests across `kissat_emit_byte`, `kissat_emit_u64` (including `0`,
  `42`, `2^64 - 1`, dry-run `cap = 0`, truncated capacity), `kissat_emit_dimacs_lit`, and
  `kissat_emit_dimacs_hdr`, plus `parseDimacs` round-trip checks.
* Concrete `Mem 64` WP non-vacuity witnesses (`XPost := False`):
  1. Emitting `"p cnf 0 1\n0\n"` and proving `parseDimacs outBytes = some (kissatCnfToDimacs [[]])`.
  2. Emitting `"p cnf 2 1\n1 -2 0\n"` and proving `parseDimacs outBytes = some ...`.
  3. Dry-run `cap = 0` emitting `2^64 - 1` (`20` bytes) with `m' = ∅`.
  4. Insufficient-capacity `cap = 5` header emission returning `10` with exact 5-byte prefix.
* `#print axioms` audit (`<= std3`).
-/

set_option autoImplicit false

namespace LeanQbeTest.T.ExportCnfFmtTest

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.ExportCnfFmt

/-! ## 1. Structural, C0/C99 Parse, and Backend Legalization `#guard` Checks -/

#guard exportCnfFmtMod.fns.length == 4
#guard exportCnfFmtMod.checkAcyclic == true
#guard exportCnfFmtMod.exits.isEmpty && exportCnfFmtMod.externs.isEmpty
#guard (exportCnfFmtMod.fns.map (·.name)).Nodup
#guard exportCnfFmtMod.fns.all fun f => f.as.length ≤ 6
#guard (parseC0 exportCnfFmtC0Src).isOk
#guard (ppTModule exportCnfFmtMod).isOk
#guard (PrintQbe.module exportCnfFmtMod).isOk
#guard [LegalTarget.aarch64, .scalar64, .x64AVX2, .x64AVX512].all fun t =>
  (ppModule (exportCnfFmt_fns.map (Fn.legal t))).isOk

/-! ## 2. Pure Round-Trip and `interpModule` Functional Checks -/

section

/-- Concrete byte vector for `"p cnf 0 1\n0\n"` (`12` bytes). -/
def nvEmptyClauseBytes : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 48, 32, 49, 10, 48, 10]

/-- Concrete byte vector for `"p cnf 2 1\n1 -2 0\n"` (`17` bytes). -/
def nvSmallClauseBytes : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 50, 32, 49, 10, 49, 32, 45, 50, 32, 48, 10]

/-- Concrete byte vector for `"p cnf"` (`5` bytes). -/
def nvTruncHdrBytes : List UInt8 :=
  [112, 32, 99, 110, 102]

/-- False exit postcondition witnessing zero `.exit` transitions. -/
abbrev nvXFalse : XPost := fun _ _ _ _ => False

end

#guard nvEmptyClauseBytes == "p cnf 0 1\n0\n".toUTF8.toList
#guard nvSmallClauseBytes == "p cnf 2 1\n1 -2 0\n".toUTF8.toList
#guard nvTruncHdrBytes == "p cnf".toUTF8.toList

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

private def checkEmitU64Case (x : BitVec 64) (expected : String) : Bool :=
  let base : BitVec 64 := 0x1000#64
  let cap : Nat := 32
  let m0 : Mem 64 := (List.replicate cap (0xAA : UInt8)).At base
  let want := expected.toUTF8.toList
  let okWrite :=
    match interpModule exportCnfFmtMod 5000 "kissat_emit_u64" [i64, i64, i64, i64] [i64]
        (base, BitVec.ofNat 64 cap, 0#64, x, ()) m0 with
    | .ok (p, ()) m1 =>
      p == BitVec.ofNat 64 want.length && readSlice m1 base want.length == some want
    | _ => false
  let okDry :=
    match interpModule exportCnfFmtMod 5000 "kissat_emit_u64" [i64, i64, i64, i64] [i64]
        (0#64, 0#64, 7#64, x, ()) ∅ with
    | .ok (p, ()) _ => p == BitVec.ofNat 64 (7 + want.length)
    | _ => false
  okWrite && okDry

#guard checkEmitU64Case 0#64 "0"
#guard checkEmitU64Case 1#64 "1"
#guard checkEmitU64Case 9#64 "9"
#guard checkEmitU64Case 10#64 "10"
#guard checkEmitU64Case 42#64 "42"
#guard checkEmitU64Case 268435455#64 "268435455"
#guard checkEmitU64Case 18446744073709551615#64 "18446744073709551615"

private def checkEmitFullEmptyClause : Bool :=
  let base : BitVec 64 := 0x2000#64
  let cap : BitVec 64 := 16#64
  let m0 : Mem 64 := (List.replicate 16 (0 : UInt8)).At base
  match interpModule exportCnfFmtMod 5000 "kissat_emit_dimacs_hdr"
      [i64, i64, i64, i64, i64] [i64] (base, cap, 0#64, 0#64, 1#64, ()) m0 with
  | .ok (p1, ()) m1 =>
    match interpModule exportCnfFmtMod 5000 "kissat_emit_byte"
        [i64, i64, i64, i64] [i64] (base, cap, p1, 48#64, ()) m1 with
    | .ok (p2, ()) m2 =>
      match interpModule exportCnfFmtMod 5000 "kissat_emit_byte"
          [i64, i64, i64, i64] [i64] (base, cap, p2, 10#64, ()) m2 with
      | .ok (p3, ()) m3 =>
        p3 == BitVec.ofNat 64 nvEmptyClauseBytes.length &&
        readSlice m3 base nvEmptyClauseBytes.length == some nvEmptyClauseBytes &&
        parseDimacsMatches nvEmptyClauseBytes (kissatCnfToDimacs [[]])
      | _ => false
    | _ => false
  | _ => false

private def checkEmitSmallClause : Bool :=
  let base : BitVec 64 := 0x3000#64
  let cap : BitVec 64 := 32#64
  let m0 : Mem 64 := (List.replicate 32 (0 : UInt8)).At base
  match interpModule exportCnfFmtMod 5000 "kissat_emit_dimacs_hdr"
      [i64, i64, i64, i64, i64] [i64] (base, cap, 0#64, 2#64, 1#64, ()) m0 with
  | .ok (p1, ()) m1 =>
    match interpModule exportCnfFmtMod 5000 "kissat_emit_dimacs_lit"
        [i64, i64, i64, i64] [i64] (base, cap, p1, 0#64, ()) m1 with
    | .ok (p2, ()) m2 =>
      match interpModule exportCnfFmtMod 5000 "kissat_emit_dimacs_lit"
          [i64, i64, i64, i64] [i64] (base, cap, p2, 3#64, ()) m2 with
      | .ok (p3, ()) m3 =>
        match interpModule exportCnfFmtMod 5000 "kissat_emit_byte"
            [i64, i64, i64, i64] [i64] (base, cap, p3, 48#64, ()) m3 with
        | .ok (p4, ()) m4 =>
          match interpModule exportCnfFmtMod 5000 "kissat_emit_byte"
              [i64, i64, i64, i64] [i64] (base, cap, p4, 10#64, ()) m4 with
          | .ok (p5, ()) m5 =>
            p5 == BitVec.ofNat 64 nvSmallClauseBytes.length &&
            readSlice m5 base nvSmallClauseBytes.length == some nvSmallClauseBytes &&
            parseDimacsMatches nvSmallClauseBytes (kissatCnfToDimacs [[0, 3]])
          | _ => false
        | _ => false
      | _ => false
    | _ => false
  | _ => false

private def checkTruncatedAndSaturating : Bool :=
  let base : BitVec 64 := 0x4000#64
  let m0 : Mem 64 := (List.replicate 5 (0x55 : UInt8)).At base
  let okTrunc :=
    match interpModule exportCnfFmtMod 5000 "kissat_emit_dimacs_hdr"
        [i64, i64, i64, i64, i64] [i64] (base, 5#64, 0#64, 0#64, 1#64, ()) m0 with
    | .ok (p, ()) m1 =>
      p == 10#64 && readSlice m1 base 5 == some nvTruncHdrBytes
    | _ => false
  let okSat :=
    match interpModule exportCnfFmtMod 5000 "kissat_emit_byte"
        [i64, i64, i64, i64] [i64] (base, 5#64, 0xFFFFFFFFFFFFFFFF#64, 65#64, ()) m0 with
    | .ok (p, ()) m1 =>
      p == 0xFFFFFFFFFFFFFFFF#64 && readSlice m1 base 5 == some (List.replicate 5 0x55)
    | _ => false
  okTrunc && okSat

#guard checkEmitFullEmptyClause
#guard checkEmitSmallClause
#guard checkTruncatedAndSaturating
#guard emitDimacsBytes 0 [[]] == nvEmptyClauseBytes
#guard emitDimacsBytes 2 [[0, 3]] == nvSmallClauseBytes
#guard parseDimacsMatches (emitDimacsBytes 5 [[0, 3], [1]]) (kissatCnfToDimacs [[0, 3], [1]])

/-! ## 3. Concrete `Mem 64` WP Non-Vacuity Witnesses (`XPost := False`) -/

section

/-- Concrete `Mem 64` WP non-vacuity witness emitting `"p cnf 0 1\n0\n"` (`12` bytes) into a
16-byte buffer at `0x10000`, with `XPost := False`, and verifying `parseDimacs` round-trip. -/
theorem nv_emit_empty_clause_dimacs :
    let out : BitVec 64 := 0x10000#64
    let m0 : Mem 64 := (List.replicate 16 (0 : UInt8)).At out
    Func.wp exportCnfFmtEnv kissat_emit_dimacs_hdr_body
      (out, 16#64, 0#64, 0#64, 1#64, ()) m0
      (fun (p1, ()) m1 =>
        Func.wp exportCnfFmtEnv kissat_emit_byte_body
          (out, 16#64, p1, 48#64, ()) m1
          (fun (p2, ()) m2 =>
            Func.wp exportCnfFmtEnv kissat_emit_byte_body
              (out, 16#64, p2, 10#64, ()) m2
              (fun (p3, ()) m3 =>
                p3 = 12#64 ∧
                m3.loadBytes out 12 = some nvEmptyClauseBytes ∧
                parseDimacs nvEmptyClauseBytes = some (kissatCnfToDimacs [[]]))
              nvXFalse)
          nvXFalse)
      nvXFalse := by
  intro out m0
  have hm0 : (bytes out (List.replicate 16 0) ⋆ emp) m0 := by
    rw [sep_emp]; rfl
  refine kissat_emit_dimacs_hdr_sound _ m0 _ nvXFalse
    ⟨out, List.replicate 16 0, 0, 0#64, 1#64, emp, rfl, by decide, by decide, hm0,
      fun m1 _ hm1 => ?_⟩
  refine kissat_emit_byte_sound _ m1 _ nvXFalse
    ⟨out, writeSlice (List.replicate 16 0) 0 (emitDimacsHdrBytes 0 1), 10, 48#64, emp,
      by decide, by decide, by decide, hm1, fun m2 _ hm2 => ?_⟩
  refine kissat_emit_byte_sound _ m2 _ nvXFalse
    ⟨out, writeSlice (writeSlice (List.replicate 16 0) 0 (emitDimacsHdrBytes 0 1)) 10 [48],
      11, 10#64, emp, by decide, by decide, by decide, hm2, fun m3 _ hm3 => ?_⟩
  have hbytes :
      writeSlice
        (writeSlice (writeSlice (List.replicate 16 (0 : UInt8)) 0 (emitDimacsHdrBytes 0 1)) 10 [48])
        11 [10] =
      nvEmptyClauseBytes ++ List.replicate 4 0 := by
    decide
  rw [show UInt8.ofNat (10#64 : BitVec 64).toNat = (10 : UInt8) from rfl, hbytes] at hm3
  rw [show bytes out (nvEmptyClauseBytes ++ List.replicate 4 0) =
      (Eq (nvEmptyClauseBytes.At out) ⋆
        Eq ((List.replicate 4 (0 : UInt8)).At (out + BitVec.ofNat 64 12))) from
    eq_append_At out nvEmptyClauseBytes (List.replicate 4 0) (by decide)] at hm3
  have hm3' : (Eq (nvEmptyClauseBytes.At out) ⋆
      (Eq ((List.replicate 4 (0 : UInt8)).At (out + BitVec.ofNat 64 12)) ⋆ emp)) m3 :=
    sep_cast hm3 (by ac_rfl)
  have hload : m3.loadBytes out 12 = some nvEmptyClauseBytes :=
    loadBytes_sep_At (a := out) (bs := nvEmptyClauseBytes) (by decide) hm3'
  have hwant_eq : nvEmptyClauseBytes = emitDimacsBytes 0 [[]] := by decide
  refine ⟨rfl, hload, ?_⟩
  rw [hwant_eq]
  exact parseDimacs_emitDimacsBytes (mv := 0) (clauses := [[]]) (by decide) (by decide)
    (fun _ hcl _ hl => by simp at hcl; subst hcl; cases hl)

/-- Concrete `Mem 64` WP non-vacuity witness emitting `"p cnf 2 1\n1 -2 0\n"` (`17` bytes) into a
32-byte buffer at `0x20000`, with `XPost := False`, and verifying `parseDimacs` round-trip. -/
theorem nv_emit_small_clause_dimacs :
    let out : BitVec 64 := 0x20000#64
    let m0 : Mem 64 := (List.replicate 32 (0 : UInt8)).At out
    Func.wp exportCnfFmtEnv kissat_emit_dimacs_hdr_body
      (out, 32#64, 0#64, 2#64, 1#64, ()) m0
      (fun (p1, ()) m1 =>
        Func.wp exportCnfFmtEnv kissat_emit_dimacs_lit_body
          (out, 32#64, p1, 0#64, ()) m1
          (fun (p2, ()) m2 =>
            Func.wp exportCnfFmtEnv kissat_emit_dimacs_lit_body
              (out, 32#64, p2, 3#64, ()) m2
              (fun (p3, ()) m3 =>
                Func.wp exportCnfFmtEnv kissat_emit_byte_body
                  (out, 32#64, p3, 48#64, ()) m3
                  (fun (p4, ()) m4 =>
                    Func.wp exportCnfFmtEnv kissat_emit_byte_body
                      (out, 32#64, p4, 10#64, ()) m4
                      (fun (p5, ()) m5 =>
                        p5 = 17#64 ∧
                        m5.loadBytes out 17 = some nvSmallClauseBytes ∧
                        parseDimacs nvSmallClauseBytes = some (kissatCnfToDimacs [[0, 3]]))
                      nvXFalse)
                  nvXFalse)
              nvXFalse)
          nvXFalse)
      nvXFalse := by
  intro out m0
  have hm0 : (bytes out (List.replicate 32 0) ⋆ emp) m0 := by
    rw [sep_emp]; rfl
  let b0 := List.replicate 32 (0 : UInt8)
  let b1 := writeSlice b0 0 (emitDimacsHdrBytes 2 1)
  let b2 := writeSlice b1 10 (emitDimacsLitBytes 0)
  let b3 := writeSlice b2 12 (emitDimacsLitBytes 3)
  let b4 := writeSlice b3 15 [48]
  let b5 := writeSlice b4 16 [10]
  refine kissat_emit_dimacs_hdr_sound _ m0 _ nvXFalse
    ⟨out, b0, 0, 2#64, 1#64, emp, rfl, by decide, by decide, hm0, fun m1 _ hm1 => ?_⟩
  refine kissat_emit_dimacs_lit_sound _ m1 _ nvXFalse
    ⟨out, b1, 10, 0#64, emp, by decide, by decide, by decide, hm1, fun m2 _ hm2 => ?_⟩
  refine kissat_emit_dimacs_lit_sound _ m2 _ nvXFalse
    ⟨out, b2, 12, 3#64, emp, by decide, by decide, by decide, hm2, fun m3 _ hm3 => ?_⟩
  refine kissat_emit_byte_sound _ m3 _ nvXFalse
    ⟨out, b3, 15, 48#64, emp, by decide, by decide, by decide, hm3, fun m4 _ hm4 => ?_⟩
  refine kissat_emit_byte_sound _ m4 _ nvXFalse
    ⟨out, b4, 16, 10#64, emp, by decide, by decide, by decide, hm4, fun m5 _ hm5 => ?_⟩
  have hbytes : b5 = nvSmallClauseBytes ++ List.replicate 15 0 := by decide
  change (bytes out b5 ⋆ emp) m5 at hm5
  rw [hbytes] at hm5
  rw [show bytes out (nvSmallClauseBytes ++ List.replicate 15 0) =
      (Eq (nvSmallClauseBytes.At out) ⋆
        Eq ((List.replicate 15 (0 : UInt8)).At (out + BitVec.ofNat 64 17))) from
    eq_append_At out nvSmallClauseBytes (List.replicate 15 0) (by decide)] at hm5
  have hm5' : (Eq (nvSmallClauseBytes.At out) ⋆
      (Eq ((List.replicate 15 (0 : UInt8)).At (out + BitVec.ofNat 64 17)) ⋆ emp)) m5 :=
    sep_cast hm5 (by ac_rfl)
  have hload : m5.loadBytes out 17 = some nvSmallClauseBytes :=
    loadBytes_sep_At (a := out) (bs := nvSmallClauseBytes) (by decide) hm5'
  have hwant_eq : nvSmallClauseBytes = emitDimacsBytes 2 [[0, 3]] := by decide
  refine ⟨rfl, hload, ?_⟩
  rw [hwant_eq]
  exact parseDimacs_emitDimacsBytes (mv := 2) (clauses := [[0, 3]]) (by decide) (by decide)
    (fun cl hcl l hl => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      subst hcl
      rcases List.mem_cons.mp hl with rfl | hl
      · decide
      · rcases List.mem_cons.mp hl with rfl | hl
        · decide
        · cases hl)

/-- Concrete `Mem 64` WP non-vacuity witness for dry-run (`cap = 0`, `out = 0`, `m = ∅`)
counting `2^64 - 1` (`20` ASCII digits) without touching memory. -/
theorem nv_emit_u64_max_dryrun :
    Func.wp exportCnfFmtEnv kissat_emit_u64_body
      (0#64, 0#64, 0#64, 0xFFFFFFFFFFFFFFFF#64, ()) (∅ : Mem 64)
      (fun (p, ()) m' => p = 20#64 ∧ m' = ∅) nvXFalse := by
  refine kissat_emit_u64_dryrun (out := 0#64) (pos := 0) (x := 0xFFFFFFFFFFFFFFFF#64)
    (m := (∅ : Mem 64)) (by decide) ?_
  have hlen : (natToBytes (0xFFFFFFFFFFFFFFFF#64 : BitVec 64).toNat).length = 20 := by decide
  rw [hlen]
  exact ⟨rfl, rfl⟩

/-- Concrete `Mem 64` WP non-vacuity witness for insufficient-capacity header emission
(`cap = 5` < `10`): writes exact 5-byte prefix `"p cnf"` in bounds and returns `10`. -/
theorem nv_emit_hdr_truncated :
    let out : BitVec 64 := 0x30000#64
    let m0 : Mem 64 := (List.replicate 5 (0xAA : UInt8)).At out
    Func.wp exportCnfFmtEnv kissat_emit_dimacs_hdr_body
      (out, 5#64, 0#64, 0#64, 1#64, ()) m0
      (fun (p, ()) m' => p = 10#64 ∧ m'.loadBytes out 5 = some nvTruncHdrBytes)
      nvXFalse := by
  intro out m0
  have hm0 : (bytes out (List.replicate 5 0xAA) ⋆ emp) m0 := by rw [sep_emp]; rfl
  refine kissat_emit_dimacs_hdr_sound _ m0 _ nvXFalse
    ⟨out, List.replicate 5 0xAA, 0, 0#64, 1#64, emp, rfl, by decide, by decide, hm0,
      fun m' _ hm' => ?_⟩
  have hws :
      writeSlice (List.replicate 5 0xAA) 0 (emitDimacsHdrBytes (0#64).toNat (1#64).toNat) =
        nvTruncHdrBytes := by decide
  rw [hws] at hm'
  exact ⟨by decide, loadBytes_sep_At (a := out) (bs := nvTruncHdrBytes) (by decide) hm'⟩

end

/-! ## 4. Axiom Audit (`<= std3`) -/

#print axioms LeanQbe.T.Examples.Kissat.ExportCnfFmt.kissat_emit_byte_wf
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfFmt.kissat_emit_u64_wf
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfFmt.kissat_emit_dimacs_lit_wf
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfFmt.kissat_emit_dimacs_hdr_wf
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfFmt.exportCnfFmt_fns_wf
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfFmt.exportCnfFmtMod_checkAcyclic
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfFmt.exportCnfFmtMod_namesNodup
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfFmt.natToBytes_eq_natRepr_toUTF8
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfFmt.parseDimacs_emitDimacsBytes_canonical
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfFmt.parseDimacs_emitDimacsBytes
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfFmt.kissat_emit_byte_wp
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfFmt.kissat_emit_u64_wp
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfFmt.kissat_emit_dimacs_lit_wp
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfFmt.kissat_emit_dimacs_hdr_wp
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfFmt.exportCnfFmtEnv_sound
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfFmt.exportCnfFmtEnv_moduleOk
#print axioms LeanQbe.T.Examples.Kissat.ExportCnfFmt.exportCnfFmtFns_sound_in
#print axioms LeanQbeTest.T.ExportCnfFmtTest.nv_emit_empty_clause_dimacs
#print axioms LeanQbeTest.T.ExportCnfFmtTest.nv_emit_small_clause_dimacs
#print axioms LeanQbeTest.T.ExportCnfFmtTest.nv_emit_u64_max_dryrun
#print axioms LeanQbeTest.T.ExportCnfFmtTest.nv_emit_hdr_truncated

end LeanQbeTest.T.ExportCnfFmtTest
