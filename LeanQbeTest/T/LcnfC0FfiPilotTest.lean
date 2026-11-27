/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import LeanQbe.T.LeanLCNF.LcnfC0FfiPilotProof
public meta import LeanQbeTest.T.LcnfC0FfiPilotCertX64
public meta import LeanQbe.T.InterpKissat
public meta import LeanQbe.T.PrintQbe
public meta import LeanQbe.T.PrintCpp

/-!
# Shard `F3` SysV x86-64 + Generic Verification & Axiom Audit (`LcnfC0FfiPilotTest`)

Validates:
1. `@&` borrow descriptors in `pilotC0Externs`, `26`-fn `pilotTailMod`, and `165`-fn closed
   `pilotLinkedMod` (`0` C files, `0` externs).
2. Stock-QBE `.ssa` and C++20 emitted-code sanity for `pilotTailMod` (`0` `$abort`/`$exit` calls).
3. Executable `interpModule` end-to-end runtime sanity across all `12` pilot scenarios over
   `pilotLinkedMod` (UNSAT/SAT/OOM `ByteArray`, tagged scalar & zero-copy `MPZ` `Nat`,
   `xorBA`/`xorNat` ok & non-aborting OOM, and round-trip `solveXorBA`).
4. Kernel `#print axioms` audit (`<= std3`) on every target-generic and SysV x86-64 headline
   theorem.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.LcnfC0FfiPilotTest

open LeanQbe.T
open LeanQbe.T.Amd64
open LeanQbe.T.LeanLCNF
open LeanQbe.T.LeanLCNF.LcnfC0FfiPilot

private meta def hasSub (s pat : String) : Bool :=
  (s.splitOn pat).length > 1

private meta def countSub (s pat : String) : Nat :=
  (s.splitOn pat).length - 1

private meta def rdU8 (m : Mem 64) (a : BitVec 64) : UInt8 :=
  (loadVal m i8 a).map (fun x => UInt8.ofNat x.toNat) |>.getD 0

private meta def rdU32 (m : Mem 64) (a : BitVec 64) : BitVec 32 :=
  (loadVal m i32 a).getD 0#32

private meta def rdU64 (m : Mem 64) (a : BitVec 64) : BitVec 64 :=
  (loadVal m i64 a).getD 0#64

private meta def rdBytes (m : Mem 64) (a : BitVec 64) (n : Nat) : List UInt8 :=
  (List.range n).map fun i => rdU8 m (a + BitVec.ofNat 64 i)

private meta def getEnd (m : Mem 64) : Option (BitVec 64) :=
  match interpModule pilotLinkedMod 1000 "lcnf_ffi_get_end" [i64] [i64] (nvPilotBase, ()) m with
  | .ok (sEnd, ()) _ => some sEnd
  | _ => none

/-! ## 1. Structural, Borrow-Annotation & Emitted Code Checks -/

#guard checkC0Externs pilotC0Externs (some pilotC0_module) == true
#guard
  pilotC0Externs.map (fun e => (e.c0Sym, e.borrows, e.passRt)) ==
    [ ("lcnf_c0_kissat_solve_ba", [true, false, false], true)
    , ("lcnf_c0_kissat_solve_nat", [true, false, false], true)
    , ("lcnf_c0_xor_ba", [true, false], true)
    , ("lcnf_c0_xor_nat", [true, false], true) ]
#guard pilotProgMod.fns.length == 5
#guard pilotC0_fns.length == 6
#guard pilotTailFns.length == 26
#guard pilotTailMod.fns.length == 26 && !pilotTailMod.externs.isEmpty
#guard pilotLinkedMod.fns.length == 165 && pilotLinkedMod.externs.isEmpty

#guard
  match PrintQbe.module pilotTailMod with
  | .ok s =>
    hasSub s "$l_LeanQbe_T_LeanLCNF_LcnfC0FfiPilot_checkSatBA" &&
    hasSub s "$l_LeanQbe_T_LeanLCNF_LcnfC0FfiPilot_checkSatNat" &&
    hasSub s "$l_LeanQbe_T_LeanLCNF_LcnfC0FfiPilot_xorBA" &&
    hasSub s "$l_LeanQbe_T_LeanLCNF_LcnfC0FfiPilot_xorNat" &&
    hasSub s "$l_LeanQbe_T_LeanLCNF_LcnfC0FfiPilot_solveXorBA" &&
    hasSub s "$lcnf_c0_kissat_solve_ba" &&
    hasSub s "$lcnf_c0_kissat_solve_nat" &&
    hasSub s "$c0_xor_bytes" &&
    countSub s "call $abort" == 0 &&
    countSub s "call $exit" == 0
  | .error _ => false

#guard
  match PrintCpp.ppTModule pilotTailMod with
  | .ok s =>
    s.length > 1000 &&
    hasSub s "c0_xor_bytes" &&
    hasSub s "lcnf_c0_kissat_solve_ba" &&
    hasSub s "lcnf_c0_kissat_solve_nat" &&
    hasSub s "l_LeanQbe_T_LeanLCNF_LcnfC0FfiPilot_solveXorBA"
  | .error _ => false

/-! ## 2. Executable Interpreter End-to-End Sanity (`pilotLinkedMod`, `165` fns) -/

#guard
  match interpModule pilotLinkedMod 200000 "l_LeanQbe_T_LeanLCNF_LcnfC0FfiPilot_checkSatBA"
      [i64, i64, i64, i64] [i64]
      (nvPilotBase, nvUnsatBaAddr nvPilotRem, 2048#64, 100#64, ())
      ((nvPilotSlab nvPilotRem).At 4096#64) with
  | .ok (r, ()) m' => r == 20#64 && getEnd m' == some (nvPilotScr nvPilotRem)
  | _ => false

#guard
  match interpModule pilotLinkedMod 200000 "l_LeanQbe_T_LeanLCNF_LcnfC0FfiPilot_checkSatBA"
      [i64, i64, i64, i64] [i64]
      (nvPilotBase, nvSatBaAddr nvPilotRem, 2048#64, 100#64, ())
      ((nvPilotSlab nvPilotRem).At 4096#64) with
  | .ok (r, ()) _ => r == 10#64
  | _ => false

#guard
  match interpModule pilotLinkedMod 50000 "l_LeanQbe_T_LeanLCNF_LcnfC0FfiPilot_checkSatBA"
      [i64, i64, i64, i64] [i64]
      (nvPilotBase, nvUnsatBaAddr nvPilotOomRem, 2048#64, 100#64, ())
      ((nvPilotSlab nvPilotOomRem).At 4096#64) with
  | .ok (r, ()) _ => r == 3#64
  | _ => false

#guard
  match interpModule pilotLinkedMod 200000 "l_LeanQbe_T_LeanLCNF_LcnfC0FfiPilot_checkSatNat"
      [i64, i64, i64, i64] [i64]
      (nvPilotBase, nvUnsatMpzAddr nvPilotRem, 2048#64, 100#64, ())
      ((nvPilotSlab nvPilotRem).At 4096#64) with
  | .ok (r, ()) m' => r == 20#64 && getEnd m' == some (nvPilotScr nvPilotRem)
  | _ => false

#guard
  match interpModule pilotLinkedMod 50000 "l_LeanQbe_T_LeanLCNF_LcnfC0FfiPilot_checkSatNat"
      [i64, i64, i64, i64] [i64]
      (nvPilotBase, nvTaggedArg, 2048#64, 100#64, ())
      ((nvPilotSlab nvPilotRem).At 4096#64) with
  | .ok (r, ()) _ => r == 0#64
  | _ => false

#guard
  match interpModule pilotLinkedMod 50000 "l_LeanQbe_T_LeanLCNF_LcnfC0FfiPilot_checkSatNat"
      [i64, i64, i64, i64] [i64]
      (nvPilotBase, nvUnsatMpzAddr nvPilotOomRem, 2048#64, 100#64, ())
      ((nvPilotSlab nvPilotOomRem).At 4096#64) with
  | .ok (r, ()) _ => r == 3#64
  | _ => false

#guard
  match interpModule pilotLinkedMod 50000 "l_LeanQbe_T_LeanLCNF_LcnfC0FfiPilot_xorBA"
      [i64, i64, i8] [i64]
      (nvPilotBase, nvMaskedBaAddr nvPilotRem, nvXorKeyBv, ())
      ((nvPilotSlab nvPilotRem).At 4096#64) with
  | .ok (resP, ()) m' =>
    let baP := rdU64 m' (resP + 8#64)
    resP != 0#64 && (resP &&& 1#64) == 0#64 &&
    rdU32 m' resP == 1#32 && rdU8 m' (resP + 7#64) == 0 &&
    baP != 0#64 && (baP &&& 1#64) == 0#64 &&
    rdU8 m' (baP + 7#64) == 248 &&
    rdU64 m' (baP + 8#64) == BitVec.ofNat 64 nvUnsatDimacs.length &&
    rdBytes m' (baP + 24#64) nvUnsatDimacs.length == nvUnsatDimacs
  | _ => false

#guard
  match interpModule pilotLinkedMod 50000 "l_LeanQbe_T_LeanLCNF_LcnfC0FfiPilot_xorBA"
      [i64, i64, i8] [i64]
      (nvPilotBase, nvUnsatBaAddr nvPilotOomRem, nvXorKeyBv, ())
      ((nvPilotSlab nvPilotOomRem).At 4096#64) with
  | .ok (r, ()) _ => r == ffiResOomWord
  | _ => false

#guard
  match interpModule pilotLinkedMod 50000 "l_LeanQbe_T_LeanLCNF_LcnfC0FfiPilot_xorNat"
      [i64, i64, i8] [i64]
      (nvPilotBase, nvTaggedArg, nvXorKeyBv, ())
      ((nvPilotSlab nvPilotRem).At 4096#64) with
  | .ok (resP, ()) m' =>
    resP != 0#64 && (resP &&& 1#64) == 0#64 &&
    rdU32 m' resP == 1#32 && rdU8 m' (resP + 7#64) == 0 &&
    (rdU64 m' (resP + 8#64) &&& 1#64) == 1#64
  | _ => false

#guard
  match interpModule pilotLinkedMod 50000 "l_LeanQbe_T_LeanLCNF_LcnfC0FfiPilot_xorNat"
      [i64, i64, i8] [i64]
      (nvPilotBase, nvUnsatMpzAddr nvPilotRem, nvXorKeyBv, ())
      ((nvPilotSlab nvPilotRem).At 4096#64) with
  | .ok (resP, ()) m' =>
    let natP := rdU64 m' (resP + 8#64)
    resP != 0#64 && (resP &&& 1#64) == 0#64 &&
    rdU32 m' resP == 1#32 && rdU8 m' (resP + 7#64) == 0 &&
    natP != 0#64 && (natP &&& 1#64) == 0#64 && rdU8 m' (natP + 7#64) == 250
  | _ => false

#guard
  match interpModule pilotLinkedMod 50000 "l_LeanQbe_T_LeanLCNF_LcnfC0FfiPilot_xorNat"
      [i64, i64, i8] [i64]
      (nvPilotBase, nvUnsatMpzAddr nvPilotOomRem, nvXorKeyBv, ())
      ((nvPilotSlab nvPilotOomRem).At 4096#64) with
  | .ok (r, ()) _ => r == ffiResOomWord
  | _ => false

#guard
  match interpModule pilotLinkedMod 200000 "l_LeanQbe_T_LeanLCNF_LcnfC0FfiPilot_solveXorBA"
      [i64, i64, i8, i64, i64] [i64]
      (nvPilotBase, nvMaskedBaAddr nvPilotRem, nvXorKeyBv, 2048#64, 100#64, ())
      ((nvPilotSlab nvPilotRem).At 4096#64) with
  | .ok (r, ()) m' => r == 20#64 && getEnd m' == some (nvPilotScr nvPilotRem)
  | _ => false

#guard
  match interpModule pilotLinkedMod 50000 "l_LeanQbe_T_LeanLCNF_LcnfC0FfiPilot_solveXorBA"
      [i64, i64, i8, i64, i64] [i64]
      (nvPilotBase, nvMaskedBaAddr nvPilotOomRem, nvXorKeyBv, 2048#64, 100#64, ())
      ((nvPilotSlab nvPilotOomRem).At 4096#64) with
  | .ok (r, ()) _ => r == 3#64
  | _ => false

/-! ## 3. Strict `std3` Axiom Audits (Target-Generic + SysV x86-64) -/

#print axioms pilotLcMod_externs_valid
#print axioms pilotC0Externs_valid
#print axioms pilotTfs_lower
#print axioms pilotLinkedMod_checkAcyclic
#print axioms pilotLinkedMod_fns_wf
#print axioms pilotLinkedMod_fn_sound
#print axioms pilotLinkedMod_moduleOk
#print axioms pilotLinkedEnv_noExit_prog
#print axioms pilot_checkSatBA_wp
#print axioms pilot_checkSatNat_wp
#print axioms pilot_xorBA_wp
#print axioms pilot_xorNat_wp
#print axioms pilot_solveXorBA_wp
#print axioms nv_pilot_checkSatBA_unsat
#print axioms nv_pilot_checkSatBA_sat
#print axioms nv_pilot_checkSatBA_oom
#print axioms nv_pilot_checkSatNat_mpz_unsat
#print axioms nv_pilot_checkSatNat_tagged
#print axioms nv_pilot_checkSatNat_oom
#print axioms nv_pilot_xorBA_ok
#print axioms nv_pilot_xorBA_oom
#print axioms nv_pilot_xorNat_tagged_ok
#print axioms nv_pilot_xorNat_mpz_ok
#print axioms nv_pilot_xorNat_oom
#print axioms nv_pilot_solveXorBA_unsat
#print axioms nv_pilot_solveXorBA_oom
#print axioms pilotX64Cert_bounds_len
#print axioms pilotX64_legalSigAll
#print axioms pilotX64InitMem_entry
#print axioms pilotX64_checkSatBA_fnSpec
#print axioms pilotX64_checkSatNat_fnSpec
#print axioms pilotX64_xorBA_fnSpec
#print axioms pilotX64_xorNat_fnSpec
#print axioms pilotX64_solveXorBA_fnSpec
#print axioms pilotX64_checkSatBA_unsat_run
#print axioms pilotX64_checkSatBA_sat_run
#print axioms pilotX64_checkSatBA_oom_run
#print axioms pilotX64_checkSatNat_mpz_unsat_run
#print axioms pilotX64_checkSatNat_tagged_run
#print axioms pilotX64_xorBA_ok_run
#print axioms pilotX64_xorBA_oom_run
#print axioms pilotX64_xorNat_tagged_ok_run
#print axioms pilotX64_xorNat_mpz_ok_run
#print axioms pilotX64_xorNat_oom_run
#print axioms pilotX64_solveXorBA_unsat_run
#print axioms pilotX64_solveXorBA_oom_run

end LeanQbeTest.T.LcnfC0FfiPilotTest
