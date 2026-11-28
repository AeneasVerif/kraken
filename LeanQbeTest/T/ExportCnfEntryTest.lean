module

import LeanQbe.T.Examples.Kissat.ExportCnfEntry
import LeanQbe.T.Examples.Kissat.ExportCnfEntryProof
import LeanQbe.T.Examples.Kissat.ExportCnfEntryProofNv
import LeanQbe.T.PrintCpp
import LeanQbe.T.PrintQbe
import LeanQbe.T.InterpKissat
import LeanQbe.T.Legal
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

/-! ## 2. Executable Interpreter Tests on Standalone `12`-Fn `exportCnfEntryMod` -/

private meta def mkGuardMem (cnfBytes : List UInt8) (cap : BitVec 64) : Mem 64 :=
  let m0 : Mem 64 := (cnfBytes ++ List.replicate 16 0).At 0x1000#64
  let m1 := storeBytes m0 0x2000#64 (List.replicate 4096 0)
  let m2 := storeBytes m1 0x100000#64 (bytes64 [0x110000#64, cap, 99#64])
  storeBytes m2 0x110000#64 (List.replicate 256 0)

private meta def readOutSlice (m : Mem 64) (dptr bptr : BitVec 64) : Nat × List UInt8 :=
  let len := match loadVal m i64 (dptr + 16#64) with
    | some v => v.toNat
    | none => 0
  let bs := (List.range len).filterMap fun i =>
    match loadVal m i8 (bptr + BitVec.ofNat 64 i) with
    | some v => some v.toNat.toUInt8
    | none => none
  (len, bs)

private meta def evalTrivialCnf (cap isUnsat : BitVec 64) : IO (BitVec 64 × Nat × List UInt8) := do
  let m0 := storeBytes (∅ : Mem 64) 0x100000#64 (bytes64 [99#64])
  let m1 := storeBytes m0 0x110000#64 (List.replicate 64 0)
  match interpModule exportCnfEntryMod 10000 "kissat_emit_trivial_cnf_bytes"
      [i64, i64, i64, i64] [i64] (0x110000#64, cap, 0x100000#64, isUnsat, ()) m1 with
  | .ok (r, ()) m' =>
    let len := (loadVal m' i64 0x100000#64).getD 0#64
    let bs := (List.range len.toNat).filterMap fun i =>
      (loadVal m' i8 (0x110000#64 + BitVec.ofNat 64 i)).map (·.toNat.toUInt8)
    pure (r, len.toNat, bs)
  | .outOfFuel => throw <| IO.userError "kissat_emit_trivial_cnf_bytes: outOfFuel"
  | .ub => throw <| IO.userError "kissat_emit_trivial_cnf_bytes: ub"
  | .exit f _ _ => throw <| IO.userError s!"kissat_emit_trivial_cnf_bytes: exit {f}"

private meta def evalSimplifyGuard (s : String) (cap wcap fuel : BitVec 64)
    (dptrOverride : Option (BitVec 64) := none) : IO (BitVec 64 × Nat) := do
  let bs := s.toUTF8.toList
  let m := mkGuardMem bs cap
  let dptr := dptrOverride.getD 0x100000#64
  match interpModule exportCnfEntryMod 100000 "kissat_simplify_export_bytes"
      [i64, i64, i64, i64, i64, i64] [i64]
      (0x1000#64, BitVec.ofNat 64 bs.length, 0x2000#64, wcap, fuel, dptr, ()) m with
  | .ok (r, ()) m' =>
    let len := (loadVal m' i64 (0x100000#64 + 16#64)).getD 0#64
    pure (r, len.toNat)
  | .outOfFuel => throw <| IO.userError "kissat_simplify_export_bytes: outOfFuel"
  | .ub => throw <| IO.userError "kissat_simplify_export_bytes: ub"
  | .exit f _ _ => throw <| IO.userError s!"kissat_simplify_export_bytes: exit {f}"

#eval show IO Unit from do
  let assertEq {α : Type} [BEq α] [Repr α] (got exp : α) (msg : String) : IO Unit :=
    if got != exp then
      throw <| IO.userError s!"{msg}: got {repr got}, expected {repr exp}"
    else pure ()

  -- Trivial emitter: UNSAT (`20`), SAT (`10`), and insufficient capacity (`0`).
  let (rUnsat, nUnsat, obsUnsat) ← evalTrivialCnf 128#64 1#64
  assertEq rUnsat 20#64 "triv unsat ret"
  assertEq nUnsat 12 "triv unsat out_len"
  assertEq obsUnsat unsatDimacsBytes "triv unsat outBytes"
  if !(parseDimacs obsUnsat).isSome then
    throw <| IO.userError "triv unsat outBytes failed parseDimacs"

  let (rSat, nSat, obsSat) ← evalTrivialCnf 128#64 0#64
  assertEq rSat 10#64 "triv sat ret"
  assertEq nSat 10 "triv sat out_len"
  assertEq obsSat satEmptyDimacsBytes "triv sat outBytes"
  if !(parseDimacs obsSat).isSome then
    throw <| IO.userError "triv sat outBytes failed parseDimacs"

  let (rSmall, nSmall, _) ← evalTrivialCnf 4#64 0#64
  assertEq rSmall 0#64 "triv small_cap ret"
  assertEq nSmall 10 "triv small_cap needed_len"

  -- Entrypoint boundary guards (null desc, zero fuel, tiny workspace): reset out_len and ret 0.
  let (rNull, _) ← evalSimplifyGuard "p cnf 1 2\n1 0\n-1 0\n" 128#64 4096#64 100#64 (some 0#64)
  assertEq rNull 0#64 "null_desc ret"
  let (rFuel, nFuel) ← evalSimplifyGuard "p cnf 1 2\n1 0\n-1 0\n" 128#64 4096#64 0#64
  assertEq rFuel 0#64 "zero_fuel ret"
  assertEq nFuel 0 "zero_fuel out_len"
  let (rTiny, nTiny) ← evalSimplifyGuard "p cnf 1 2\n1 0\n-1 0\n" 128#64 1024#64 100#64
  assertEq rTiny 0#64 "tiny_work ret"
  assertEq nTiny 0 "tiny_work out_len"

  -- Concrete non-trivial `kissat_export_cnf_bytes` execution on `nvExportUnitMem`:
  match interpModule exportCnfEntryMod 100000 "kissat_export_cnf_bytes"
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
example : exportCnfEntryMod.names.Nodup := exportCnfEntryMod_namesNodup

example := @kissat_emit_trivial_cnf_bytes_wp
example := @kissat_simplify_export_loaded_wp
example := @kissat_simplify_export_bytes_wp
example := @kissat_simplify_export_bytes_sound
example := @kissat_simplify_export_bytes_sound_parsed
example := @export_entry_unit_unknown_nv
example := @export_entry_inconsistent_nv
example := @export_entry_sat_nv

#print axioms exportCnfEntryEnv_moduleOk
#print axioms kissat_emit_trivial_cnf_bytes_wp
#print axioms kissat_simplify_export_loaded_wp
#print axioms kissat_simplify_export_bytes_wp
#print axioms kissat_simplify_export_bytes_sound
#print axioms kissat_simplify_export_bytes_sound_parsed
#print axioms export_entry_unit_unknown_nv
#print axioms export_entry_inconsistent_nv
#print axioms export_entry_sat_nv

end LeanQbeTest.T.ExportCnfEntryTest
