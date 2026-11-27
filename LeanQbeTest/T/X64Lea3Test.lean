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
# Batch Z Compiler Pass: `H24 S28 lea-three-op-arith` Test

Regression tests on `x64Target` for verified 3-operand `leaq`/`leal` arithmetic lowering:

1. Scaled-index + displacement without base (`lea disp(, %rx, 2^s), %rd`) for 32-bit & 64-bit
   and `scale ∈ {2, 4, 8}` (`+ imm`, `- imm`, `(x + d) <<< s`, chained shifts).
2. Base + scaled-index + displacement (`lea disp(%ry, %rx, 2^s), %rd`) for 32-bit & 64-bit.
3. Non-destructive immediate shift lowering (`shl 1..3`) into `lea (,%rx,2^s), %rd`.
4. Hardware upper-32 zeroing of `leal` (`zext 32 64` elided without `movl %r, %r`).
5. Target guards (`%rsp` cannot be SIB index, `s1` swaps when base ≠ `%rsp`, `fitsImm32` check).
6. Standard-axiom audit (`#print axioms`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.X64Lea3Test

open LeanQbe.T LeanQbe.T.Amd64

/-! ## Helpers -/

meta def hintsOf (fs : List Fn) : List x64Target.toIsa.Hints :=
  fs.map (Fn.computeHints x64Target.toIsa x64LegalTarget)

meta def chk (fs : List Fn) : Bool :=
  checkCompile x64Target x64Layout x64LegalTarget [] [] 0 fs (hintsOf fs) 2048

meta def codeOf (fs : List Fn) : List x64Target.toIsa.Directive :=
  extractCode (compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes [] [] 0 fs
    (hintsOf fs))

meta def isLea32 : Directive → Bool
  | .instr (.regular _ .W32 (.lea _ _)) => true
  | _ => false

meta def isLea64 : Directive → Bool
  | .instr (.regular _ .W64 (.lea _ _)) => true
  | _ => false

meta def isLeaAny (d : Directive) : Bool := isLea32 d || isLea64 d

meta def isShl : Directive → Bool
  | .instr (.regular _ _ (.shl _ _)) => true
  | _ => false

meta def isSelfMov32 : Directive → Bool
  | .instr (.regular _ .W32 (.mov (.reg (.low a .W32)) (.regOrMem (.reg (.low b .W32))))) => a == b
  | _ => false

meta def countDirs (p : Directive → Bool) (ds : List Directive) : Nat := (ds.filter p).length

/-! ## 1. 64-bit & 32-bit `lea disp(, %rx, 2^s)` and `lea disp(%ry, %rx, 2^s)` -/

/-- `(i <<< 1) + 1` (scale 2 + imm, 64-bit): 1 `leaq`, 0 `shl`. -/
meta def idx2AddImm64Fn : Fn :=
  ⟨"idx2AddImm64", [i64], [i64], fun _ _ (i, ()) =>
    .let_ (op2 (.shl i64) (.var i) (.imm 1#64)) fun (s, ()) =>
    .let_ (op2 (.add i64) (.var s) (.imm 1#64)) fun (r, ()) => .ret (.var r, ())⟩

/-- `(i <<< 2) - 4` (scale 4 - imm, 32-bit): 1 `leal`, 0 `shl`. -/
meta def idx4SubImm32Fn : Fn :=
  ⟨"idx4SubImm32", [i32], [i32], fun _ _ (i, ()) =>
    .let_ (op2 (.shl i32) (.var i) (.imm 2#32)) fun (s, ()) =>
    .let_ (op2 (.sub i32) (.var s) (.imm 4#32)) fun (r, ()) => .ret (.var r, ())⟩

/-- `(i <<< 3) + 12` (scale 8 + imm, 32-bit) zero-extended to `i64`: `leal` + 0 `movl` + 0 `shl`. -/
meta def idx8AddImm32ZextFn : Fn :=
  ⟨"idx8AddImm32Zext", [i32], [i64], fun _ _ (i, ()) =>
    .let_ (op2 (.shl i32) (.var i) (.imm 3#32)) fun (s, ()) =>
    .let_ (op2 (.add i32) (.var s) (.imm 12#32)) fun (r, ()) =>
    .let_ (op1 (.zext 32 64) (.var r)) fun (z, ()) => .ret (.var z, ())⟩

/-- `((i + 3) <<< 2)` (64-bit): 1 `leaq`, 0 `shl`. -/
meta def addThenShl64Fn : Fn :=
  ⟨"addThenShl64", [i64], [i64], fun _ _ (i, ()) =>
    .let_ (op2 (.add i64) (.var i) (.imm 3#64)) fun (a, ()) =>
    .let_ (op2 (.shl i64) (.var a) (.imm 2#64)) fun (r, ()) => .ret (.var r, ())⟩

/-- `((i - 2) <<< 3)` (32-bit): 1 `leal`, 0 `shl`. -/
meta def subThenShl32Fn : Fn :=
  ⟨"subThenShl32", [i32], [i32], fun _ _ (i, ()) =>
    .let_ (op2 (.sub i32) (.var i) (.imm 2#32)) fun (a, ()) =>
    .let_ (op2 (.shl i32) (.var a) (.imm 3#32)) fun (r, ()) => .ret (.var r, ())⟩

/-- `(i <<< 1) <<< 2` (scale 8, 32-bit): 1 `leal`, 0 `shl`. -/
meta def chainShl32Fn : Fn :=
  ⟨"chainShl32", [i32], [i32], fun _ _ (i, ()) =>
    .let_ (op2 (.shl i32) (.var i) (.imm 1#32)) fun (a, ()) =>
    .let_ (op2 (.shl i32) (.var a) (.imm 2#32)) fun (r, ()) => .ret (.var r, ())⟩

/-- `base + (idx <<< 2)` and `(base + (idx <<< 3)) + 16` (64-bit). -/
meta def baseIdxDisp64Fn : Fn :=
  ⟨"baseIdxDisp64", [i64, i64], [i64], fun _ _ (b, i, ()) =>
    .let_ (op2 (.shl i64) (.var i) (.imm 3#64)) fun (s, ()) =>
    .let_ (op2 (.add i64) (.var b) (.var s)) fun (a, ()) =>
    .let_ (op2 (.add i64) (.var a) (.imm 16#64)) fun (r, ()) => .ret (.var r, ())⟩

/-- `(base + 4) + ((idx <<< 2) + 8)` (32-bit): 1 `leal`, 0 `shl`. -/
meta def baseIdxDisp32Fn : Fn :=
  ⟨"baseIdxDisp32", [i32, i32], [i32], fun _ _ (b, i, ()) =>
    .let_ (op2 (.add i32) (.var b) (.imm 4#32)) fun (b1, ()) =>
    .let_ (op2 (.shl i32) (.var i) (.imm 2#32)) fun (s, ()) =>
    .let_ (op2 (.add i32) (.var s) (.imm 8#32)) fun (s1, ()) =>
    .let_ (op2 (.add i32) (.var b1) (.var s1)) fun (r, ()) => .ret (.var r, ())⟩

/-- Non-destructive shifts `i <<< 1`, `i <<< 2` reusing `i`: uses `lea` instead of `mov + shl`. -/
meta def reuseShift32Fn : Fn :=
  ⟨"reuseShift32", [i32], [i32, i32, i32], fun _ _ (i, ()) =>
    .let_ (op2 (.shl i32) (.var i) (.imm 1#32)) fun (a, ()) =>
    .let_ (op2 (.shl i32) (.var i) (.imm 2#32)) fun (b, ()) =>
    .ret (.var a, .var b, .var i, ())⟩

#guard chk [idx2AddImm64Fn, idx4SubImm32Fn, idx8AddImm32ZextFn, addThenShl64Fn, subThenShl32Fn,
  chainShl32Fn, baseIdxDisp64Fn, baseIdxDisp32Fn, reuseShift32Fn]
#guard countDirs isLea64 (codeOf [idx2AddImm64Fn]) == 1 &&
  countDirs isShl (codeOf [idx2AddImm64Fn]) == 0
#guard countDirs isLea32 (codeOf [idx4SubImm32Fn]) == 1 &&
  countDirs isShl (codeOf [idx4SubImm32Fn]) == 0
#guard countDirs isLea32 (codeOf [idx8AddImm32ZextFn]) == 1 &&
  countDirs isSelfMov32 (codeOf [idx8AddImm32ZextFn]) == 0 &&
  countDirs isShl (codeOf [idx8AddImm32ZextFn]) == 0
#guard countDirs isLea64 (codeOf [addThenShl64Fn]) == 1 &&
  countDirs isShl (codeOf [addThenShl64Fn]) == 0
#guard countDirs isLea32 (codeOf [subThenShl32Fn]) == 1 &&
  countDirs isShl (codeOf [subThenShl32Fn]) == 0
#guard countDirs isLea32 (codeOf [chainShl32Fn]) == 1 &&
  countDirs isShl (codeOf [chainShl32Fn]) == 0
#guard countDirs isLea64 (codeOf [baseIdxDisp64Fn]) == 1 &&
  countDirs isShl (codeOf [baseIdxDisp64Fn]) == 0
#guard countDirs isLea32 (codeOf [baseIdxDisp32Fn]) == 1 &&
  countDirs isShl (codeOf [baseIdxDisp32Fn]) == 0
#guard countDirs isLea32 (codeOf [reuseShift32Fn]) >= 2 &&
  countDirs isShl (codeOf [reuseShift32Fn]) == 0

/-! ## 2. Target Guards: `%rsp` Index Guard & `fitsImm32` Displacement Bounds -/

#guard (x64Gpr.leaArith 64 (some .rax) .rsp .s2 4 .rcx).isNone
#guard (x64Gpr.leaArith 64 none .rsp .s4 8 .rcx).isNone
#guard (x64Gpr.leaArith 32 none .rsp .s8 0 .rcx).isNone
-- When `sc == .s1` and `base ≠ .rsp`, swapping base and index is valid:
#guard (x64Gpr.leaArith 64 (some .rax) .rsp .s1 4 .rcx) ==
  some ([.instr (.regular .W64 .W64 (.lea (q .rcx) (atSIB .rsp .rax .s1 4)))], maskNone)
-- Out-of-imm32 displacements are rejected safely:
#guard (x64Gpr.leaArith 64 (some .rax) .rbx .s2 ⟨0x100000000⟩ .rcx).isNone
#guard (x64Gpr.leaArith 64 none .rbx .s4 ⟨-0x80000001⟩ .rcx).isNone
-- `opShiftIns` never emits `lea (, %rsp, 2)`:
#guard (opShiftIns .W64 .shl (.gpr .rsp) (.imm 1#64) .rcx).map
  (fun p => p.1.any fun i => match i with | .regular _ _ (.lea _ _) => true | _ => false) ==
  some false

/-! ## 3. Axiom Audit -/

#print axioms LeanQbe.T.Rega.lowerFn_correct
#print axioms LeanQbe.T.Rega.lowerOp_ok
#print axioms LeanQbe.T.Amd64.x64Gpr_leaArith_spec
#print axioms LeanQbe.T.Amd64.x64Gpr_leaArith_zero32
#print axioms LeanQbe.T.Amd64.x64GprSpec

end LeanQbeTest.T.X64Lea3Test
