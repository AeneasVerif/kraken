module

public import LeanQbe.T.Examples.Kissat.FullM6
public import LeanQbe.T.Examples.Kissat.ExportCnfEntry
public import LeanQbe.T.Examples.Kissat.ExportCnfEntryProof
public import LeanQbe.T.Examples.Kissat.ExportCnfEntryProofNv
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.InterpKissat
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM6
meta import LeanQbe.T.Examples.Kissat.ExportCnfEntry
meta import LeanQbe.T.Examples.Kissat.ExportCnfEntryProof
meta import LeanQbe.T.Examples.Kissat.ExportCnfEntryProofNv
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.InterpKissat
meta import LeanQbe.T.Legal

set_option autoImplicit false

namespace LeanQbeTest.T.ExportCnfEntryTest

open Std.Sat
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.ExportCnfEntry
open LeanQbe.T.Examples.Kissat.ExportCnfEntryProof

/-! ## 1. C0 / IL Structural, ABI, Acyclicity, Legal & QBE/C++ Print Checks -/

#guard exportCnfEntry_fns.length == 3
#guard exportCnfEntryAllFns.length == 12
#guard exportCnfEntryMod.externs.length == 4
#guard exportCnfEntryMod.exits.isEmpty
#guard (exportCnfEntryMod.names).Nodup
#guard exportCnfEntryAllFns.all fun f => f.as.length ≤ 6
#guard exportCnfEntryMod.checkAcyclic == true

#guard m6ExportMod.fns.length == 394
#guard m6ExportMod.externs.isEmpty
#guard m6ExportMod.exits.isEmpty
#guard m6ExportMod.names.Nodup

#guard exportCnfEntry.C0Src.contains "kissat_simplify_export_bytes"
#guard exportCnfEntry.C0Src.contains "kissat_simplify_export_loaded"
#guard exportCnfEntry.C0Src.contains "kissat_emit_trivial_cnf_bytes"

#guard (ppTModule exportCnfEntryMod).isOk
#guard (PrintQbe.module exportCnfEntryMod).isOk
#guard
  match PrintQbe.module exportCnfEntryMod with
  | .ok qbe =>
    qbe.contains "export function l $kissat_simplify_export_bytes(" &&
    qbe.contains "export function l $kissat_simplify_export_loaded(" &&
    qbe.contains "export function l $kissat_emit_trivial_cnf_bytes("
  | .error _ => false

#guard [LegalTarget.aarch64, .scalar64, .x64, .x64SSE, .x64AVX2, .x64AVX512].all fun t =>
  exportCnfEntryMod.fns.all fun f => f.body.isLegal t

#eval show IO Unit from do
  let check (ok : Bool) (msg : String) : IO Unit :=
    if !ok then throw <| IO.userError s!"ExportCnfEntryTest check failed: {msg}" else pure ()
  check m6ExportMod.checkAcyclic "m6ExportMod.checkAcyclic"
  check (PrintQbe.module m6ExportMod).isOk "PrintQbe.module m6ExportMod"
  for (lbl, t) in [("x64", LegalTarget.x64), ("x64SSE", .x64SSE),
      ("x64AVX2", .x64AVX2), ("x64AVX512", .x64AVX512), ("aarch64", .aarch64)] do
    check (m6ExportMod.fns.all fun f => f.body.isLegal t) s!"m6 {lbl} legal"

/-! ## 2. Executable Interpreter Tests on Closed 394-Fn `m6ExportMod` -/

private meta def mkTestMem (cnfBytes : List UInt8) (cap : BitVec 64) : Mem 64 :=
  let m0 : Mem 64 := (cnfBytes ++ List.replicate 16 0).At 0x1000#64
  let m1 := storeBytes m0 0x2000#64 (List.replicate 65536 0)
  let m2 := storeBytes m1 0x100000#64 (bytes64 [0x110000#64, cap, 99#64])
  storeBytes m2 0x110000#64 (List.replicate 1024 0)

private meta def readOutSlice (m : Mem 64) (dptr bptr : BitVec 64) : Nat × List UInt8 :=
  let len := match loadVal m i64 (dptr + 16#64) with
    | some v => v.toNat
    | none => 0
  let bs := (List.range len).filterMap fun i =>
    match loadVal m i8 (bptr + BitVec.ofNat 64 i) with
    | some v => some v.toNat.toUInt8
    | none => none
  (len, bs)

private meta def evalSimplifyExport (s : String) (cap : BitVec 64) (ppFuel : Nat)
    (dptrOverride : Option (BitVec 64) := none) : IO (BitVec 64 × Nat × List UInt8) := do
  let bs := s.toUTF8.toList
  let m := mkTestMem bs cap
  let dptr := dptrOverride.getD 0x100000#64
  match interpModule m6ExportMod 2000000 "kissat_simplify_export_bytes"
      [i64, i64, i64, i64, i64, i64] [i64]
      (0x1000#64, BitVec.ofNat 64 bs.length, 0x2000#64, 65536#64,
        BitVec.ofNat 64 ppFuel, dptr, ()) m with
  | .ok (r, ()) m' =>
    let (n, obs) := readOutSlice m' 0x100000#64 0x110000#64
    pure (r, n, obs)
  | .outOfFuel => throw <| IO.userError "kissat_simplify_export_bytes: outOfFuel"
  | .ub => throw <| IO.userError "kissat_simplify_export_bytes: ub"
  | .exit f _ _ => throw <| IO.userError s!"kissat_simplify_export_bytes: exit {f}"

#eval show IO Unit from do
  let assertEq {α : Type} [BEq α] [Repr α] (got exp : α) (msg : String) : IO Unit :=
    if got != exp then
      throw <| IO.userError s!"{msg}: got {repr got}, expected {repr exp}"
    else pure ()

  -- Direct contradiction (`BUG-CROSS-01` fix): returns 20 and valid explicit contradiction.
  let (rUnsat, nUnsat, obsUnsat) ← evalSimplifyExport "p cnf 1 2\n1 0\n-1 0\n" 128#64 100
  assertEq rUnsat 20#64 "unsat ret"
  assertEq nUnsat 12 "unsat out_len"
  assertEq obsUnsat unsatDimacsBytes "unsat outBytes"
  if !(parseDimacs obsUnsat).isSome then
    throw <| IO.userError "unsat outBytes failed parseDimacs"

  -- Nontrivial UNSAT (PHP 3->2): preprocess derives inconsistency and exports `p cnf 0 1\n0\n`.
  let php32 :=
    "p cnf 6 9\n1 2 0\n3 4 0\n5 6 0\n-1 -3 0\n-1 -5 0\n-3 -5 0\n-2 -4 0\n-2 -6 0\n-4 -6 0\n"
  let (rPhp, nPhp, obsPhp) ← evalSimplifyExport php32 128#64 100
  assertEq rPhp 20#64 "php32 ret"
  assertEq nPhp 12 "php32 out_len"
  assertEq obsPhp unsatDimacsBytes "php32 outBytes"

  -- Satisfiable formula: returns 10 and valid empty-clause-free `p cnf 0 0\n`.
  let (rSat, nSat, obsSat) ← evalSimplifyExport "p cnf 2 1\n1 2 0\n" 128#64 100
  assertEq rSat 10#64 "sat ret"
  assertEq nSat 10 "sat out_len"
  assertEq obsSat satEmptyDimacsBytes "sat outBytes"
  if !(parseDimacs obsSat).isSome then
    throw <| IO.userError "sat outBytes failed parseDimacs"

  -- Small capacity rejection (`cap = 4 < 10`): returns 0 without overflowing buffer.
  let (rSmall, nSmall, _) ← evalSimplifyExport "p cnf 2 1\n1 2 0\n" 4#64 100
  assertEq rSmall 0#64 "small_cap ret"
  assertEq nSmall 10 "small_cap needed_len"

  -- Null output descriptor pointer: cleanly returns 0.
  let (rNull, _, _) ← evalSimplifyExport "p cnf 1 2\n1 0\n-1 0\n" 128#64 100 (some 0#64)
  assertEq rNull 0#64 "null_desc ret"

  -- Concrete non-trivial `kissat_export_cnf_bytes` execution on `nvExportUnitMem`:
  match interpModule m6ExportMod 100000 "kissat_export_cnf_bytes"
      [i64, i64, i64, i64] [i64]
      (nvM6SatCfg.hdr, nvOutBufPtr, 64#64, nvOutDescPtr + 16#64, ()) nvExportUnitMem with
  | .ok (ok, ()) m' =>
    let (nUnit, obsUnit) := readOutSlice m' nvOutDescPtr nvOutBufPtr
    assertEq ok 1#64 "nvExportUnitMem ok"
    assertEq nUnit 14 "nvExportUnitMem out_len"
    assertEq obsUnit "p cnf 2 1\n1 0\n".toUTF8.toList "nvExportUnitMem outBytes"
    if !(parseDimacs obsUnit).isSome then
      throw <| IO.userError "nvExportUnitMem outBytes failed parseDimacs"
  | _ => throw <| IO.userError "nvExportUnitMem kissat_export_cnf_bytes failed"

/-! ## 3. Formal Theorem Instantiation & Axiom Checks (`<= std3`, single line < 115c) -/

example : ModuleOk exportCnfEntryEnv exportCnfEntryMod := exportCnfEntryEnv_moduleOk
example : ModuleOk m6ExportEnv m6ExportMod := m6ExportEnv_moduleOk
example : m6ExportMod.names.Nodup := m6ExportMod_namesNodup

example := @kissat_simplify_export_bytes_wp
example := @kissat_simplify_export_bytes_sound
example := @kissat_simplify_export_bytes_sound_parsed
example := @m6_export_simplify_sound
example := @m6_export_unsat_nv
example := @m6_export_sat_sound_nv
example := @export_entry_unit_unknown_nv
example := @export_entry_inconsistent_nv
example := @export_entry_sat_nv

#print axioms exportCnfEntryEnv_moduleOk
#print axioms m6ExportEnv_moduleOk
#print axioms kissat_simplify_export_bytes_wp
#print axioms kissat_simplify_export_bytes_sound
#print axioms kissat_simplify_export_bytes_sound_parsed
#print axioms m6_export_simplify_sound
#print axioms m6_export_unsat_nv
#print axioms m6_export_sat_sound_nv
#print axioms export_entry_unit_unknown_nv
#print axioms export_entry_inconsistent_nv
#print axioms export_entry_sat_nv

end LeanQbeTest.T.ExportCnfEntryTest
