module

public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.IselLemmas1
public import LeanQbe.T.Amd64.IselLemmas5
public import LeanQbe.T.RegaLemmas2
public import LeanQbe.T.RegaLemmas4
public import LeanQbe.T.Spill
meta import LeanQbe.T.Amd64.TargLemmas
meta import LeanQbe.T.Spill

/-!
# Redundant 32-to-64 Zero-Extension Elision Tests (SysV x86-64)

Regression tests on `x64Target` for verified elision of redundant 32->64 zero-extension
moves (`movl %r, %r`) on x86-64:

1. Redundant `movl %r, %r` is elided when a GPR already holds a proven zero-extended
   32-bit value (32-bit ALU `add 32`, 32-bit load `load i32`, incoming ABI argument).
2. Non-canonical 64-bit values (e.g. 64-bit ALU `add 64` truncated to 32-bit) STILL
   emit `movl %r, %r` safely before returning or when zero-extended.
3. Axiom audit (`#print axioms`) confirming only standard Lean axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.X64Zext32ElideTest

open LeanQbe.T LeanQbe.T.Amd64

/-! ## Helpers -/

meta def hintsOf (fs : List Fn) : List x64Target.toIsa.Hints :=
  fs.map (Fn.computeHints x64Target.toIsa x64LegalTarget)

meta def chk (fs : List Fn) : Bool :=
  checkCompile x64Target x64Layout x64LegalTarget [] [] 0 fs (hintsOf fs) 2048

meta def codeOf (fs : List Fn) : List x64Target.toIsa.Directive :=
  extractCode (compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes [] [] 0 fs
    (hintsOf fs))

meta def isSelfMov32 : Directive → Bool
  | .instr (.regular _ .W32 (.mov (.reg (.low a .W32)) (.regOrMem (.reg (.low b .W32))))) => a == b
  | _ => false

meta def countDirs (p : Directive → Bool) (ds : List Directive) : Nat := (ds.filter p).length

/-! ## 1. Verified Elision of Redundant 32->64 Zero-Extension -/

/-- 32-bit ALU (`add 32`) returned: GPR is hardware zero-extended, so `canonAbi` emits no `movl`. -/
meta def add32RetFn : Fn :=
  ⟨"add32Ret", [i32, i32], [i32], fun _ _ (a, b, ()) =>
    .let_ (op2 (.add i32) (.var a) (.var b)) fun (c, ()) => .ret (.var c, ())⟩

/-- 32-bit ALU (`xor 32`) returned: emits no `movl`. -/
meta def xor32RetFn : Fn :=
  ⟨"xor32Ret", [i32, i32], [i32], fun _ _ (a, b, ()) =>
    .let_ (op2 (.xor i32) (.var a) (.var b)) fun (c, ()) => .ret (.var c, ())⟩

/-- 32-bit load returned: `load i32` hardware zero-extends upper 32 bits, emits no `movl`. -/
meta def load32RetFn : Fn :=
  ⟨"load32Ret", [i64], [i32], fun _ _ (p, ()) =>
    .load i32 (.var p) fun x => .ret (.var x, ())⟩

/-- `zext 32 64` of 32-bit ALU op: elided completely, emitting no instructions. -/
meta def zextAdd32Fn : Fn :=
  ⟨"zextAdd32", [i32, i32], [i64], fun _ _ (a, b, ()) =>
    .let_ (op2 (.add i32) (.var a) (.var b)) fun (c, ()) =>
    .let_ (op1 (.zext 32 64) (.var c)) fun (d, ()) => .ret (.var d, ())⟩

#guard chk [add32RetFn] && chk [xor32RetFn] && chk [load32RetFn] && chk [zextAdd32Fn]
#guard countDirs isSelfMov32 (codeOf [add32RetFn]) == 0
#guard countDirs isSelfMov32 (codeOf [xor32RetFn]) == 0
#guard countDirs isSelfMov32 (codeOf [load32RetFn]) == 0
#guard countDirs isSelfMov32 (codeOf [zextAdd32Fn]) == 0

/-! ## 2. Non-Canonical 64-bit Values Safely Preserve `movl` -/

/-- Truncated 64-bit `add 64` returned as `i32`: upper bits non-zero, must emit `movl`. -/
meta def truncAdd64RetFn : Fn :=
  ⟨"truncAdd64Ret", [i64, i64], [i32], fun _ _ (a, b, ()) =>
    .let_ (op2 (.add i64) (.var a) (.var b)) fun (c, ()) =>
    .let_ (op1 (.trunc 64 32) (.var c)) fun (d, ()) => .ret (.var d, ())⟩

/-- `zext 32 64` of truncated 64-bit value: must emit `movl` to clear upper bits safely. -/
meta def truncAdd64ZextFn : Fn :=
  ⟨"truncAdd64Zext", [i64, i64], [i64], fun _ _ (a, b, ()) =>
    .let_ (op2 (.add i64) (.var a) (.var b)) fun (c, ()) =>
    .let_ (op1 (.trunc 64 32) (.var c)) fun (d, ()) =>
    .let_ (op1 (.zext 32 64) (.var d)) fun (e, ()) => .ret (.var e, ())⟩

#guard chk [truncAdd64RetFn] && chk [truncAdd64ZextFn]
#guard countDirs isSelfMov32 (codeOf [truncAdd64RetFn]) >= 1
#guard countDirs isSelfMov32 (codeOf [truncAdd64ZextFn]) >= 1

/-! ## 3. Axiom Audit -/

#print axioms LeanQbe.T.Rega.lowerFn_correct
#print axioms LeanQbe.T.Rega.abiHeld_ok
#print axioms LeanQbe.T.Rega.skipOk_of_abiSkips
#print axioms LeanQbe.T.Rega.lowerOp_ok
#print axioms LeanQbe.T.Rega.lowerLoad_ok

end LeanQbeTest.T.X64Zext32ElideTest
