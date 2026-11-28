module

import LeanQbe.T.IfOptLemmas
import LeanQbe.T.OptFlatCfgLemmas
import LeanQbe.T.SimplifyGroupPlanLemmas
import LeanQbe.T.FlatLemmas
import LeanQbe.T.WPLemmas
import LeanQbe.T.MainFlat
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.PrintAsm0
meta import LeanQbe.T.IfOpt
meta import LeanQbe.T.OptFlatCfg
meta import LeanQbe.T.SimplifyGroupPlan
meta import LeanQbe.T.Main
meta import LeanQbe.T.MainFlat
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.PrintAsm0

/-!
# Store-Sinking Common-Address RMW Diamond If-Conversion Tests (`IfOptStoreSinkTest`)

Tests Rank 7 P1 common-address store-sinking diamond conversion across both PHOAS
(`Func.ifOpt` / `Func.ifOptBits`), native `TFlat` (`OptFlatCfg.ifOptFlat`), and SysV x64
codegen (`Amd64.x64Target`; Arm64 `csel` companion in `IfOptStoreSinkArm64Test`):

1. `full_m6_sweep_sim`-shaped RMW diamond (`zext + shl + add + load + or/(not+and) + store`)
   with duplicated address computation (`SymTbl.internOp` GVN) and `.ret` join, verifying:
   - branchless `.select` + 1 `.load` + 1 `.store` in both PHOAS and `TFlat`,
   - SysV x64 codegen (`cmov`, zero conditional jumps),
   - closed-function `Wf`, `Func.ifOptBits_spec`, `Func.ifOptBits_callsOk`.
2. Loop `.group` RMW diamond (`full_m6_sweep_sim.L33` shape) with post-store `.let_` tail.
3. Non-RMW identical-address store diamonds (`i64` & `i32`) inside 1-block `.group`
   (`Func.ifOpt` + `SimplifyGroupPlan`), plus 2-load reuse with operand deduplication.
4. Negative guards: mismatched addresses, mismatched `storeTy`, trapping `.udiv`, single-arm
   `.store`, and unmatched `.load` all remain unconverted (`.jnz` preserved).
5. `OptFlatCfg.ifOptFlat` parity theorems and strict `[propext, Classical.choice, Quot.sound]`
   axiom audit.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.IfOptStoreSinkTest

open LeanQbe.T

/-- Check whether `op` is a `.select` operation. -/
def isSelectOp : {sig ts : List Ty} → OpCode sig ts → Bool
  | _, _, .select _ => true
  | _, _, _ => false

/-- Combine 4-tuple counters `(jnz, load, store, select)` componentwise. -/
def add4 (a b : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2 + b.2.2.2)

mutual
/-- Recursive `(jnz, load, store, select)` counter across `TFlat`. -/
def countTFlat : {rs : List Ty} → TFlat rs → Nat × Nat × Nat × Nat
  | _, .let_ op k =>
    let sel := if isSelectOp op.code then 1 else 0
    add4 (0, 0, 0, sel) (countTFlat k)
  | _, .load _ _ k => add4 (0, 1, 0, 0) (countTFlat k)
  | _, .store _ _ k => add4 (0, 0, 1, 0) (countTFlat k)
  | _, .call _ _ _ k => countTFlat k
  | _, .jnz _ t e => add4 (1, 0, 0, 0) (add4 (countTFlat t) (countTFlat e))
  | _, .group bs k => add4 (countTBlocks bs) (countTFlat k)
  | _, .jump _ _ | _, .ret _ | _, .exit _ _ | _, .hlt => (0, 0, 0, 0)

/-- Recursive `(jnz, load, store, select)` counter across `TBlocks`. -/
def countTBlocks : {rs : List Ty} → {sig : List (List Ty)} → TBlocks rs sig →
    Nat × Nat × Nat × Nat
  | _, _, .nil => (0, 0, 0, 0)
  | _, _, .cons b bs => add4 (countTFlat b) (countTBlocks bs)
end

/-- `full_m6_sweep_sim`-shaped RMW diamond with GVN-matched address ops and `.ret` tail:
`if (flag == 1) { sig[gv] |= mask; return 1; } else { sig[gv] &= ~mask; return 0; }`. -/
def fullM6SweepRmwDia : Func [i32, i64, i32, i64] [i64] :=
  fun _ _ (flag, sig, gv, mask, ()) =>
  .let_ (op2 (.cmp .eq i32) (.var flag) (.imm 1#32)) fun (cond, ()) =>
  .jnz (.var cond)
    (.let_ (op1 (.zext 32 64) (.var gv)) fun (gv64, ()) =>
     .let_ (op2 (.shl i64) (.var gv64) (.imm 3#64)) fun (off, ()) =>
     .let_ (op2 (.add i64) (.var sig) (.var off)) fun (addr, ()) =>
     .load i64 (.var addr) fun old =>
     .let_ (op2 (.or i64) (.var old) (.var mask)) fun (nv, ()) =>
     .store (.var nv) (.var addr) <|
     .ret (.imm 1#64, ()))
    (.let_ (op1 (.zext 32 64) (.var gv)) fun (gv64, ()) =>
     .let_ (op2 (.shl i64) (.var gv64) (.imm 3#64)) fun (off, ()) =>
     .let_ (op2 (.add i64) (.var sig) (.var off)) fun (addr, ()) =>
     .load i64 (.var addr) fun old =>
     .let_ (op1 (.not i64) (.var mask)) fun (nmask, ()) =>
     .let_ (op2 (.and i64) (.var old) (.var nmask)) fun (nv, ()) =>
     .store (.var nv) (.var addr) <|
     .ret (.imm 0#64, ()))

theorem fullM6SweepRmwDia_branchless :
    countTFlat (reifyFunc (Func.ifOptBits fullM6SweepRmwDia)) = (0, 1, 1, 2) := by
  t_kernel_rfl

theorem fullM6SweepRmwDia_flat_parity :
    OptFlatCfg.ifOptFlat true [i32, i64, i32, i64] (reifyFunc fullM6SweepRmwDia) =
      reifyFunc (Func.ifOptBits fullM6SweepRmwDia) :=
  OptFlatCfg.ifOptFlat_true_eq (reifyFunc fullM6SweepRmwDia)
    (PassFlatKit.reifyFunc_wfCheck (by t_wf_reify))

theorem fullM6SweepRmwDia_flat_kernel :
    OptFlatCfg.ifOptFlat true [i32, i64, i32, i64] (reifyFunc fullM6SweepRmwDia) =
      reifyFunc (Func.ifOptBits fullM6SweepRmwDia) := by
  t_kernel_rfl

theorem fullM6SweepRmwDia_wf : fullM6SweepRmwDia.Wf := by t_wf_reify

theorem fullM6SweepRmwDia_spec {Γ : Env} {xs m Q X}
    (h : Func.wp Γ fullM6SweepRmwDia xs m Q X) :
    Func.wp Γ (Func.ifOptBits fullM6SweepRmwDia) xs m Q X :=
  Func.ifOptBits_spec fullM6SweepRmwDia_wf h

theorem fullM6SweepRmwDia_callsOk {allowed : List SigEntry} {exits : List Sym}
    (hc : (fullM6SweepRmwDia (fun _ => Unit) (fun _ => Unit)
      (Tup.units [i32, i64, i32, i64])).callsOk allowed exits) :
    ((Func.ifOptBits fullM6SweepRmwDia) (fun _ => Unit) (fun _ => Unit)
      (Tup.units [i32, i64, i32, i64])).callsOk allowed exits :=
  Func.ifOptBits_callsOk fullM6SweepRmwDia_wf hc

/-- `full_m6_sweep_sim.L33`-shaped loop with inner RMW diamond + post-store `i + 1` tail. -/
def fullM6SweepRmwLoop : Func [i32, i64, i64, i64] [i64] :=
  fun _ _ (nv, valsPtr, sigPtr, mask, ()) =>
  .group (sig := [[i32]])
    (fun (loop, ()) =>
      .cons (fun (i, ()) =>
        .let_ (op2 (.cmp .ult i32) (.var i) (.var nv)) fun (inBound, ()) =>
        .jnz (.var inBound)
          (.let_ (op1 (.zext 32 64) (.var i)) fun (i64v, ()) =>
           .let_ (op2 (.shl i64) (.var i64v) (.imm 3#64)) fun (vOff, ()) =>
           .let_ (op2 (.add i64) (.var valsPtr) (.var vOff)) fun (vAddr, ()) =>
           .load i32 (.var vAddr) fun flag =>
           .let_ (op2 (.cmp .eq i32) (.var flag) (.imm 1#32)) fun (isOne, ()) =>
           .let_ (op2 (.add i64) (.var sigPtr) (.var vOff)) fun (sAddr, ()) =>
           .jnz (.var isOne)
             (.load i64 (.var sAddr) fun old =>
              .let_ (op2 (.or i64) (.var old) (.var mask)) fun (nv, ()) =>
              .store (.var nv) (.var sAddr) <|
              .let_ (op2 (.add i32) (.var i) (.imm 1#32)) fun (iNext, ()) =>
              .jump loop (.var iNext, ()))
             (.load i64 (.var sAddr) fun old =>
              .let_ (op1 (.not i64) (.var mask)) fun (nmask, ()) =>
              .let_ (op2 (.and i64) (.var old) (.var nmask)) fun (nv, ()) =>
              .store (.var nv) (.var sAddr) <|
              .let_ (op2 (.add i32) (.var i) (.imm 1#32)) fun (iNext, ()) =>
              .jump loop (.var iNext, ())))
          (.ret (.var sigPtr, ())))
        .nil)
    (fun (loop, ()) => .jump loop (.imm 0#32, ()))

theorem fullM6SweepRmwLoop_counts :
    countTFlat (reifyFunc (Func.ifOptBits fullM6SweepRmwLoop)) = (1, 2, 1, 2) := by
  t_kernel_rfl

theorem fullM6SweepRmwLoop_flat_parity :
    OptFlatCfg.ifOptFlat true [i32, i64, i64, i64] (reifyFunc fullM6SweepRmwLoop) =
      reifyFunc (Func.ifOptBits fullM6SweepRmwLoop) := by
  t_kernel_rfl

theorem fullM6SweepRmwLoop_wf : fullM6SweepRmwLoop.Wf := by t_wf_reify

theorem fullM6SweepRmwLoop_spec {Γ : Env} {xs m Q X}
    (h : Func.wp Γ fullM6SweepRmwLoop xs m Q X) :
    Func.wp Γ (Func.ifOptBits fullM6SweepRmwLoop) xs m Q X :=
  Func.ifOptBits_spec fullM6SweepRmwLoop_wf h

/-- Non-RMW identical-address store diamond in a 1-block `.group` (`Func.ifOpt`). -/
def pureStoreGroupDia : Func [i32, i64, i64, i64] [i64] :=
  fun _ _ (flag, addr, x, y, ()) =>
  .let_ (op2 (.cmp .eq i32) (.var flag) (.imm 1#32)) fun (c, ()) =>
  .group (sig := [[i64]])
    (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.add i64) (.var x) (.imm 5#64)) fun (a, ()) =>
         .store (.var a) (.var addr) <|
         .jump J (.var a, ()))
        (.let_ (op2 (.sub i64) (.var y) (.imm 3#64)) fun (b, ()) =>
         .store (.var b) (.var addr) <|
         .jump J (.var b, ())))

theorem pureStoreGroupDia_branchless :
    countTFlat (reifyFunc (Func.simplifyGroupPlan (Func.ifOpt pureStoreGroupDia))) =
      (0, 0, 1, 2) := by
  t_kernel_rfl

theorem pureStoreGroupDia_flat_parity :
    OptFlatCfg.ifOptFlat false [i32, i64, i64, i64] (reifyFunc pureStoreGroupDia) =
      reifyFunc (Func.ifOpt pureStoreGroupDia) := by
  t_kernel_rfl

theorem pureStoreGroupDia_wf : pureStoreGroupDia.Wf := by t_wf_reify

theorem pureStoreGroupDia_spec {Γ : Env} {xs m Q X}
    (h : Func.wp Γ pureStoreGroupDia xs m Q X) :
    Func.wp Γ (Func.simplifyGroupPlan (Func.ifOpt pureStoreGroupDia)) xs m Q X :=
  Func.simplifyGroupPlan_spec (Func.ifOpt_wf pureStoreGroupDia_wf)
    (Func.ifOpt_spec pureStoreGroupDia_wf h)

/-- Two-load matched diamond with identical exit argument deduplication (`select` count = 1). -/
def twoLoadReuseDia : Func [i32, i64, i64, i64] [i64] :=
  fun _ _ (flag, a1, a2, retv, ()) =>
  .let_ (op2 (.cmp .eq i32) (.var flag) (.imm 0#32)) fun (c, ()) =>
  .jnz (.var c)
    (.load i64 (.var a1) fun v1 =>
     .load i64 (.var a2) fun v2 =>
     .let_ (op2 (.add i64) (.var v1) (.var v2)) fun (s, ()) =>
     .store (.var s) (.var a1) <|
     .ret (.var retv, ()))
    (.load i64 (.var a2) fun v2 =>
     .load i64 (.var a1) fun v1 =>
     .let_ (op2 (.sub i64) (.var v1) (.var v2)) fun (d, ()) =>
     .store (.var d) (.var a1) <|
     .ret (.var retv, ()))

theorem twoLoadReuseDia_counts :
    countTFlat (reifyFunc (Func.ifOptBits twoLoadReuseDia)) = (0, 2, 1, 1) := by
  t_kernel_rfl

theorem twoLoadReuseDia_spec {Γ : Env} {xs m Q X}
    (h : Func.wp Γ twoLoadReuseDia xs m Q X) :
    Func.wp Γ (Func.ifOptBits twoLoadReuseDia) xs m Q X :=
  Func.ifOptBits_spec (by t_wf_reify) h

/-! ## Negative Guard Fixtures (must keep `.jnz`) -/

def negMismatchAddr : Func [i32, i64, i64, i64] [i64] :=
  fun _ _ (flag, a1, a2, v, ()) =>
  .let_ (op2 (.cmp .eq i32) (.var flag) (.imm 1#32)) fun (c, ()) =>
  .jnz (.var c)
    (.store (.var v) (.var a1) <| .ret (.imm 1#64, ()))
    (.store (.var v) (.var a2) <| .ret (.imm 0#64, ()))

def negMismatchTy : Func [i32, i64, i32, i64] [i64] :=
  fun _ _ (flag, a, v32, v64, ()) =>
  .let_ (op2 (.cmp .eq i32) (.var flag) (.imm 1#32)) fun (c, ()) =>
  .jnz (.var c)
    (.store (t := i32) (.var v32) (.var a) <| .ret (.imm 1#64, ()))
    (.store (t := i64) (.var v64) (.var a) <| .ret (.imm 0#64, ()))

def negTrapDiv : Func [i32, i64, i64, i64] [i64] :=
  fun _ _ (flag, a, x, y, ()) =>
  .let_ (op2 (.cmp .eq i32) (.var flag) (.imm 1#32)) fun (c, ()) =>
  .jnz (.var c)
    (.let_ (op2 (.udiv 64) (.var x) (.var y)) fun (q, ()) =>
     .store (.var q) (.var a) <| .ret (.imm 1#64, ()))
    (.store (.var x) (.var a) <| .ret (.imm 0#64, ()))

def negOneArmStore : Func [i32, i64, i64] [i64] :=
  fun _ _ (flag, a, x, ()) =>
  .let_ (op2 (.cmp .eq i32) (.var flag) (.imm 1#32)) fun (c, ()) =>
  .jnz (.var c)
    (.store (.var x) (.var a) <| .ret (.imm 1#64, ()))
    (.ret (.imm 0#64, ()))

def negUnmatchedLoad : Func [i32, i64, i64, i64] [i64] :=
  fun _ _ (flag, a1, a2, v, ()) =>
  .let_ (op2 (.cmp .eq i32) (.var flag) (.imm 1#32)) fun (c, ()) =>
  .jnz (.var c)
    (.load i64 (.var a1) fun old =>
     .let_ (op2 (.or i64) (.var old) (.var v)) fun (nv, ()) =>
     .store (.var nv) (.var a2) <| .ret (.imm 1#64, ()))
    (.store (.var v) (.var a2) <| .ret (.imm 0#64, ()))

theorem negMismatchAddr_unchanged :
    Func.ifOptBits negMismatchAddr = negMismatchAddr := by t_kernel_rfl
theorem negMismatchTy_unchanged :
    Func.ifOptBits negMismatchTy = negMismatchTy := by t_kernel_rfl
theorem negTrapDiv_unchanged :
    Func.ifOptBits negTrapDiv = negTrapDiv := by t_kernel_rfl
theorem negOneArmStore_unchanged :
    Func.ifOptBits negOneArmStore = negOneArmStore := by t_kernel_rfl
theorem negUnmatchedLoad_unchanged :
    Func.ifOptBits negUnmatchedLoad = negUnmatchedLoad := by t_kernel_rfl

theorem neg_all_flat_parity :
    OptFlatCfg.ifOptFlat true [i32, i64, i64, i64] (reifyFunc negMismatchAddr) =
        reifyFunc negMismatchAddr ∧
    OptFlatCfg.ifOptFlat true [i32, i64, i32, i64] (reifyFunc negMismatchTy) =
        reifyFunc negMismatchTy ∧
    OptFlatCfg.ifOptFlat true [i32, i64, i64, i64] (reifyFunc negTrapDiv) =
        reifyFunc negTrapDiv ∧
    OptFlatCfg.ifOptFlat true [i32, i64, i64] (reifyFunc negOneArmStore) =
        reifyFunc negOneArmStore ∧
    OptFlatCfg.ifOptFlat true [i32, i64, i64, i64] (reifyFunc negUnmatchedLoad) =
        reifyFunc negUnmatchedLoad := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> t_kernel_rfl

/-! ## SysV x64 Codegen Verification (`cmov`, zero branches on diamonds) -/

/-- Substring check helper. -/
meta def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

#eval show IO Unit from do
  let rmwFn : Fn := ⟨"rmw_dia", [i32, i64, i32, i64], [i64], fullM6SweepRmwDia⟩
  let pureFn : Fn := ⟨"pure_store", [i32, i64, i64, i64], [i64], pureStoreGroupDia⟩
  let negFn : Fn := ⟨"neg_addr", [i32, i64, i64, i64], [i64], negMismatchAddr⟩
  for (label, fn, expectBranchless) in
      [("full_m6_rmw", rmwFn, true), ("pure_store", pureFn, true), ("neg_addr", negFn, false)] do
    let ff : TFlatFn := ⟨fn.name, fn.as, fn.rs, reifyFunc fn.body⟩
    let hx := Fn.computeHints Amd64.x64Target.toIsa Amd64.x64LegalTarget fn
    let xDirsP ← IO.ofExcept (compileFn Amd64.x64Target.toIsa Amd64.x64LegalTarget hx fn)
    let xDirsF ← IO.ofExcept (compileFlatFn Amd64.x64Target.toIsa Amd64.x64LegalTarget hx ff)
    let xAsmP := Amd64.printAsm0 xDirsP
    let xAsmF := Amd64.printAsm0 xDirsF
    if xAsmP != xAsmF then
      throw <| IO.userError s!"x64 flat/phoas mismatch for {label}"
    if expectBranchless then
      if !hasSub xAsmP "cmov" then
        throw <| IO.userError s!"x64 {label}: expected cmov in:\n{xAsmP}"
      for jcc in ["\nje ", "\njne ", "\tjz ", "\tjnz ", "\tjmp "] do
        if hasSub xAsmP jcc then
          throw <| IO.userError s!"x64 {label}: unexpected branch {jcc} in:\n{xAsmP}"
    else
      if !["\nje ", "\njne ", "\tjz ", "\tjnz "].any (hasSub xAsmP) then
        throw <| IO.userError s!"x64 {label}: negative case unexpectedly eliminated branch"
  IO.println "OK (IfOptStoreSinkTest/x64): cmov + zero branches + flat parity verified"

#print axioms fullM6SweepRmwDia_spec
#print axioms fullM6SweepRmwDia_callsOk
#print axioms fullM6SweepRmwLoop_spec
#print axioms pureStoreGroupDia_spec
#print axioms twoLoadReuseDia_spec
#print axioms fullM6SweepRmwDia_flat_parity

end LeanQbeTest.T.IfOptStoreSinkTest
