module

public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.PrintAsm0
public import LeanQbe.T.Amd64.IselLemmas5
public import LeanQbe.T.RegaLemmas4
public import LeanQbe.T.Spill
public import LeanQbe.T.MainFlatLemmas
meta import Lean
meta import LeanQbe.T.Amd64.TargLemmas
meta import LeanQbe.T.Amd64.PrintAsm0
meta import LeanQbe.T.Spill
meta import LeanQbe.T.MainFlat

/-!
# x64 Sign-Bit `test %r, %r; js/jns` & Constant-Multiply `lea` Regression Tests (`X64TestJsLeaTest`)

Verifies Rank 8 P1 x86-64 ISel optimizations end to end on `x64Target`:
1. Macro-fusable `testl %r, %r; js`/`jns` for `(x &&& 0x80000000#32) != 0` / `== 0`,
   `(x &&& 0x8000000000000000#64) != 0` / `== 0` (`testq`), and `(x &&& 0x80000000#64) != 0`
   (`testl`), with `0` `testl $-2147483648` instructions emitted.
2. 1-cycle `lea` lowering for `mul` by `3, 5, 6, 9, 10, 12` (`i32` & `i64`, commutative `imm * x`,
   `src == dst` aliasing, `zext 32 64` elision, and `%rsp` SIB-index guard) with `0` `imul`.
3. `MainFlat` (`compileFlatFn = compileFn`) parity, native x86-64 execution check via `cc`,
   AArch64/Vll isolation check, and `<= std3` axiom audit.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.X64TestJsLeaTest

open LeanQbe.T LeanQbe.T.Amd64

/-! ## Helpers -/

meta def hintsOf (fs : List Fn) : List x64Target.toIsa.Hints :=
  fs.map (Fn.computeHints x64Target.toIsa x64LegalTarget)

meta def chk (fs : List Fn) : Bool :=
  checkCompile x64Target x64Layout x64LegalTarget [] [] 0 fs (hintsOf fs) 4096

meta def compileRes (fs : List Fn) : List Directive :=
  match compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes [] [] 0 fs
      (hintsOf fs) with
  | .ok (p, _) => p
  | .error _ => []

meta def codeOf (fs : List Fn) : List Directive :=
  extractCode (compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes [] [] 0 fs
    (hintsOf fs))

meta def asmOf (fs : List Fn) : String :=
  printModule0 (fs.map (·.name)) (compileRes fs)

meta def hasSubstr (hay needle : String) : Bool :=
  (hay.splitOn needle).length > 1

meta def isTestSelf32 : Directive → Bool
  | .instr (.regular _ .W32 (.test (.reg (.low a .W32)) (.regOrMem (.reg (.low b .W32))))) =>
    a == b
  | _ => false

meta def isTestSelf64 : Directive → Bool
  | .instr (.regular _ .W64 (.test (.reg (.low a .W64)) (.regOrMem (.reg (.low b .W64))))) =>
    a == b
  | _ => false

meta def isTestImmSign32 : Directive → Bool
  | .instr (.regular _ .W32 (.test (.reg _) (.imm (.int64 c)))) =>
    c.toBitVec.setWidth 32 == 0x80000000#32
  | _ => false

meta def isJccSign : CondCode → Directive → Bool
  | want, .instr (.regular _ .W64 (.jcc cc _)) => cc == want
  | _, _ => false

meta def isLeaSIB : Directive → Bool
  | .instr (.regular _ _ (.lea _ a)) => a.base.isSome && a.idx.isSome
  | _ => false

meta def isImulDir : Directive → Bool
  | .instr (.regular _ _ (.imul1 _)) => true
  | .instr (.regular _ _ (.imul _ _ _)) => true
  | _ => false

meta def isSelfMov32 : Directive → Bool
  | .instr (.regular _ .W32 (.mov (.reg (.low a .W32)) (.regOrMem (.reg (.low b .W32))))) => a == b
  | _ => false

meta def countDirs (p : Directive → Bool) (ds : List Directive) : Nat := (ds.filter p).length

/-! ## 1. Macro-Fusable `testl`/`testq %r, %r; js/jns` Sign-Bit Branches -/

meta def signBit32NeFn : Fn :=
  ⟨"signBit32Ne", [i32, i64, i32, i32], [i32], fun _ _ (x, p, a, b, ()) =>
    .let_ (op2 (.and i32) (.var x) (.imm 0x80000000#32)) fun (m, ()) =>
    .let_ (op2 (.cmp .ne i32) (.var m) (.imm 0#32)) fun (c, ()) =>
    .jnz (.var c)
      (.store (t := i32) (.var a) (.var p) (.ret (.var a, ())))
      (.store (t := i32) (.var b) (.var p) (.ret (.var b, ())))⟩

meta def signBit32EqFn : Fn :=
  ⟨"signBit32Eq", [i32, i64, i32, i32], [i32], fun _ _ (x, p, a, b, ()) =>
    .let_ (op2 (.and i32) (.var x) (.imm 0x80000000#32)) fun (m, ()) =>
    .let_ (op2 (.cmp .eq i32) (.var m) (.imm 0#32)) fun (c, ()) =>
    .jnz (.var c)
      (.store (t := i32) (.var a) (.var p) (.ret (.var a, ())))
      (.store (t := i32) (.var b) (.var p) (.ret (.var b, ())))⟩

meta def signBit32InvertFn : Fn :=
  ⟨"signBit32Invert", [i32, i64, i32, i32], [i32], fun _ _ (x, p, a, b, ()) =>
    .group (sig := [[], []])
      (fun _ => Blocks.cons (fun () => .store (t := i32) (.var a) (.var p) (.ret (.var a, ())))
        (Blocks.cons (fun () =>
          .let_ (op2 (.add i32) (.var b) (.imm 1#32)) fun (b1, ()) =>
          .store (t := i32) (.var b1) (.var p) (.ret (.var b1, ())))
          Blocks.nil))
      fun (j0, j1, ()) =>
        .let_ (op2 (.and i32) (.var x) (.imm 0x80000000#32)) fun (m, ()) =>
        .let_ (op2 (.cmp .ne i32) (.var m) (.imm 0#32)) fun (c, ()) =>
        .jnz (.var c) (.jump j0 ()) (.jump j1 ())⟩

meta def signBit64NeFn : Fn :=
  ⟨"signBit64Ne", [i64, i64, i64, i64], [i64], fun _ _ (x, p, a, b, ()) =>
    .let_ (op2 (.and i64) (.var x) (.imm 0x8000000000000000#64)) fun (m, ()) =>
    .let_ (op2 (.cmp .ne i64) (.var m) (.imm 0#64)) fun (c, ()) =>
    .jnz (.var c)
      (.store (t := i64) (.var a) (.var p) (.ret (.var a, ())))
      (.store (t := i64) (.var b) (.var p) (.ret (.var b, ())))⟩

meta def signBit64EqFn : Fn :=
  ⟨"signBit64Eq", [i64, i64, i64, i64], [i64], fun _ _ (x, p, a, b, ()) =>
    .let_ (op2 (.and i64) (.var x) (.imm 0x8000000000000000#64)) fun (m, ()) =>
    .let_ (op2 (.cmp .eq i64) (.var m) (.imm 0#64)) fun (c, ()) =>
    .jnz (.var c)
      (.store (t := i64) (.var a) (.var p) (.ret (.var a, ())))
      (.store (t := i64) (.var b) (.var p) (.ret (.var b, ())))⟩

meta def bit31In64NeFn : Fn :=
  ⟨"bit31In64Ne", [i64, i64, i64, i64], [i64], fun _ _ (x, p, a, b, ()) =>
    .let_ (op2 (.and i64) (.var x) (.imm 0x80000000#64)) fun (m, ()) =>
    .let_ (op2 (.cmp .ne i64) (.var m) (.imm 0#64)) fun (c, ()) =>
    .jnz (.var c)
      (.store (t := i64) (.var a) (.var p) (.ret (.var a, ())))
      (.store (t := i64) (.var b) (.var p) (.ret (.var b, ())))⟩

#guard chk [signBit32NeFn] && chk [signBit32EqFn] && chk [signBit32InvertFn]
#guard chk [signBit64NeFn] && chk [signBit64EqFn] && chk [bit31In64NeFn]

#guard countDirs isTestSelf32 (codeOf [signBit32NeFn]) == 1 &&
  countDirs isTestImmSign32 (codeOf [signBit32NeFn]) == 0 &&
  countDirs (isJccSign .s) (codeOf [signBit32NeFn]) >= 1
#guard countDirs isTestSelf32 (codeOf [signBit32EqFn]) == 1 &&
  countDirs isTestImmSign32 (codeOf [signBit32EqFn]) == 0 &&
  countDirs (isJccSign .ns) (codeOf [signBit32EqFn]) >= 1
#guard countDirs isTestSelf32 (codeOf [signBit32InvertFn]) == 1 &&
  countDirs isTestImmSign32 (codeOf [signBit32InvertFn]) == 0 &&
  (countDirs (isJccSign .s) (codeOf [signBit32InvertFn]) +
   countDirs (isJccSign .ns) (codeOf [signBit32InvertFn])) >= 1 &&
  hasSubstr (asmOf [signBit32InvertFn]) "testl %" &&
  (hasSubstr (asmOf [signBit32InvertFn]) "js " || hasSubstr (asmOf [signBit32InvertFn]) "jns ")
#guard countDirs isTestSelf64 (codeOf [signBit64NeFn]) == 1 &&
  countDirs (isJccSign .s) (codeOf [signBit64NeFn]) >= 1
#guard countDirs isTestSelf64 (codeOf [signBit64EqFn]) == 1 &&
  countDirs (isJccSign .ns) (codeOf [signBit64EqFn]) >= 1
#guard countDirs isTestSelf32 (codeOf [bit31In64NeFn]) == 1 &&
  !hasSubstr (asmOf [bit31In64NeFn]) "2147483648"
#guard !hasSubstr (asmOf [signBit32NeFn]) "-2147483648" &&
  hasSubstr (asmOf [signBit32NeFn]) "testl %" && hasSubstr (asmOf [signBit32NeFn]) "js "
#guard !hasSubstr (asmOf [signBit32EqFn]) "-2147483648" &&
  hasSubstr (asmOf [signBit32EqFn]) "testl %" && hasSubstr (asmOf [signBit32EqFn]) "jns "

/-! ## 2. 1-Cycle `lea` Multiplication (`3, 5, 6, 9, 10, 12`) & Guards -/

meta def mkMul32Fn (nm : String) (c : BitVec 32) : Fn :=
  ⟨nm, [i32], [i32], fun _ _ (x, ()) =>
    .let_ (op2 (.mul i32) (.var x) (.imm c)) fun (r, ()) => .ret (.var r, ())⟩

meta def mkMul64Fn (nm : String) (c : BitVec 64) : Fn :=
  ⟨nm, [i64], [i64], fun _ _ (x, ()) =>
    .let_ (op2 (.mul i64) (.var x) (.imm c)) fun (r, ()) => .ret (.var r, ())⟩

meta def mulComm32Fn : Fn :=
  ⟨"mulComm32", [i32], [i32], fun _ _ (x, ()) =>
    .let_ (op2 (.mul i32) (.imm 5#32) (.var x)) fun (r, ()) => .ret (.var r, ())⟩

meta def mulComm64Fn : Fn :=
  ⟨"mulComm64", [i64], [i64], fun _ _ (x, ()) =>
    .let_ (op2 (.mul i64) (.imm 10#64) (.var x)) fun (r, ()) => .ret (.var r, ())⟩

/-- `mul32` by `6` zero-extended to `i64`: `leal` + `addl` zeroes upper 32 bits (`0` `movl`). -/
meta def mul32ZextFn : Fn :=
  ⟨"mul32Zext", [i32], [i64], fun _ _ (x, ()) =>
    .let_ (op2 (.mul i32) (.var x) (.imm 6#32)) fun (r, ()) =>
    .let_ (op1 (.zext 32 64) (.var r)) fun (z, ()) => .ret (.var z, ())⟩

/-- Chain `(x * 3) + (x * 12)` reusing `x` across `src == dst` / live values. -/
meta def mulChainFn : Fn :=
  ⟨"mulChain", [i64, i32], [i64], fun _ _ (a, b, ()) =>
    .let_ (op2 (.mul i64) (.var a) (.imm 9#64)) fun (a9, ()) =>
    .let_ (op2 (.mul i32) (.var b) (.imm 12#32)) fun (b12, ()) =>
    .let_ (op1 (.zext 32 64) (.var b12)) fun (bz, ()) =>
    .let_ (op2 (.add i64) (.var a9) (.var bz)) fun (s, ()) => .ret (.var s, ())⟩

meta def mulFns32 : List Fn :=
  [ mkMul32Fn "mul32_3" 3#32, mkMul32Fn "mul32_5" 5#32, mkMul32Fn "mul32_6" 6#32,
    mkMul32Fn "mul32_9" 9#32, mkMul32Fn "mul32_10" 10#32, mkMul32Fn "mul32_12" 12#32,
    mulComm32Fn, mul32ZextFn ]

meta def mulFns64 : List Fn :=
  [ mkMul64Fn "mul64_3" 3#64, mkMul64Fn "mul64_5" 5#64, mkMul64Fn "mul64_6" 6#64,
    mkMul64Fn "mul64_9" 9#64, mkMul64Fn "mul64_10" 10#64, mkMul64Fn "mul64_12" 12#64,
    mulComm64Fn, mulChainFn ]

#guard (mulFns32 ++ mulFns64).all fun f => chk [f]
#guard (mulFns32 ++ mulFns64).all fun f =>
  countDirs isLeaSIB (codeOf [f]) >= 1 && countDirs isImulDir (codeOf [f]) == 0
#guard countDirs isSelfMov32 (codeOf [mul32ZextFn]) == 0

-- Direct ISel checks for `src == dst` aliasing and `%rsp` SIB-index guard
#guard
  let alias32 := x64Op (.mul i32) (.gpr .rax, .imm 3#32, ()) (.gpr .rax, ()) .default
  let alias64 := x64Op (.mul i64) (.gpr .rdi, .imm 12#64, ()) (.gpr .rdi, ()) .default
  let rspGuard := opBinLeaMul? .W64 .mul .rsp 3#64 .rax
  let rspFallback := x64Op (.mul i64) (.gpr .rsp, .imm 6#64, ()) (.gpr .rax, ()) .default
  match alias32, alias64, rspGuard, rspFallback with
  | some (d32, cl32), some (d64, cl64), none, some (dRsp, _) =>
    countDirs isLeaSIB d32 == 1 && countDirs isImulDir d32 == 0 && cl32 == maskNone &&
    countDirs isLeaSIB d64 == 1 && countDirs isImulDir d64 == 0 && cl64 == maskAll &&
    countDirs isLeaSIB dRsp == 0 && countDirs isImulDir dRsp == 1
  | _, _, _, _ => false

/-! ## 3. `MainFlat` Parity & Native `x86_64` Execution Check -/

meta def allFns : List Fn :=
  [signBit32NeFn, signBit32EqFn, signBit32InvertFn, signBit64NeFn, signBit64EqFn,
   bit31In64NeFn] ++ mulFns32 ++ mulFns64

meta def toTFlatFn (f : Fn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, reifyFunc f.body⟩

meta def flatParityCheck (f : Fn) : Bool :=
  let tf := toTFlatFn f
  let h := Fn.computeHints x64Target.toIsa x64LegalTarget tf.toFn
  let hOrig := Fn.computeHints x64Target.toIsa x64LegalTarget f
  if !tf.wfCheck then false
  else
    match compileFlatFn x64Target.toIsa x64LegalTarget h tf,
        compileFn x64Target.toIsa x64LegalTarget h tf.toFn,
        compileFlatFn x64Target.toIsa x64LegalTarget hOrig tf,
        compileFn x64Target.toIsa x64LegalTarget hOrig f with
    | .ok fc, .ok xc, .ok fc0, .ok xc0 => fc == xc && fc0 == xc0
    | _, _, _, _ => false

#guard allFns.all flatParityCheck

meta def execHarnessC : String :=
  "#include <stdint.h>\n" ++
  "#include <stdio.h>\n" ++
  "int32_t signBit32Ne(int32_t, int32_t*, int32_t, int32_t);\n" ++
  "int32_t signBit32Eq(int32_t, int32_t*, int32_t, int32_t);\n" ++
  "int32_t signBit32Invert(int32_t, int32_t*, int32_t, int32_t);\n" ++
  "int64_t signBit64Ne(int64_t, int64_t*, int64_t, int64_t);\n" ++
  "int64_t signBit64Eq(int64_t, int64_t*, int64_t, int64_t);\n" ++
  "int64_t bit31In64Ne(int64_t, int64_t*, int64_t, int64_t);\n" ++
  "uint32_t mul32_3(uint32_t); uint32_t mul32_5(uint32_t); uint32_t mul32_6(uint32_t);\n" ++
  "uint32_t mul32_9(uint32_t); uint32_t mul32_10(uint32_t); uint32_t mul32_12(uint32_t);\n" ++
  "uint32_t mulComm32(uint32_t); uint64_t mul32Zext(uint32_t);\n" ++
  "uint64_t mul64_3(uint64_t); uint64_t mul64_5(uint64_t); uint64_t mul64_6(uint64_t);\n" ++
  "uint64_t mul64_9(uint64_t); uint64_t mul64_10(uint64_t); uint64_t mul64_12(uint64_t);\n" ++
  "uint64_t mulComm64(uint64_t); uint64_t mulChain(uint64_t, uint32_t);\n" ++
  "int main(void) {\n" ++
  "  int32_t xs32[] = {0, 1, -1, 0x7fffffff, (int32_t)0x80000000u, (int32_t)0x80000001u};\n" ++
  "  for (int i = 0; i < 6; i++) {\n" ++
  "    int32_t x = xs32[i], slot = 0; uint32_t u = (uint32_t)x;\n" ++
  "    int neg = (u & 0x80000000u) != 0;\n" ++
  "    if (signBit32Ne(x, &slot, 11, 22) != (neg ? 11 : 22) ||\n" ++
  "        slot != (neg ? 11 : 22)) return 1;\n" ++
  "    if (signBit32Eq(x, &slot, 11, 22) != (neg ? 22 : 11) ||\n" ++
  "        slot != (neg ? 22 : 11)) return 2;\n" ++
  "    if (signBit32Invert(x, &slot, 10, 99) != (neg ? 10 : 100) ||\n" ++
  "        slot != (neg ? 10 : 100)) return 3;\n" ++
  "    if (mul32_3(u) != u * 3u || mul32_5(u) != u * 5u || mul32_6(u) != u * 6u) return 4;\n" ++
  "    if (mul32_9(u) != u * 9u || mul32_10(u) != u * 10u || mul32_12(u) != u * 12u) return 5;\n" ++
  "    if (mulComm32(u) != u * 5u || mul32Zext(u) != (uint64_t)(u * 6u)) return 6;\n" ++
  "  }\n" ++
  "  uint64_t xs64[] = {0ULL, 1ULL, 0x7fffffffULL, 0x80000000ULL,\n" ++
  "    0x8000000000000000ULL, 0xffffffffffffffffULL, 0x123456789abcdef0ULL};\n" ++
  "  for (int i = 0; i < 7; i++) {\n" ++
  "    uint64_t x = xs64[i]; int64_t s64 = 0;\n" ++
  "    int neg64 = (x >> 63) != 0; int b31 = ((x >> 31) & 1) != 0;\n" ++
  "    if (signBit64Ne((int64_t)x, &s64, 100, 200) != (neg64 ? 100 : 200) ||\n" ++
  "        s64 != (neg64 ? 100 : 200)) return 7;\n" ++
  "    if (signBit64Eq((int64_t)x, &s64, 100, 200) != (neg64 ? 200 : 100) ||\n" ++
  "        s64 != (neg64 ? 200 : 100)) return 8;\n" ++
  "    if (bit31In64Ne((int64_t)x, &s64, 100, 200) != (b31 ? 100 : 200) ||\n" ++
  "        s64 != (b31 ? 100 : 200)) return 9;\n" ++
  "    if (mul64_3(x) != x * 3ULL || mul64_5(x) != x * 5ULL ||\n" ++
  "        mul64_6(x) != x * 6ULL) return 10;\n" ++
  "    if (mul64_9(x) != x * 9ULL || mul64_10(x) != x * 10ULL ||\n" ++
  "        mul64_12(x) != x * 12ULL) return 11;\n" ++
  "    if (mulComm64(x) != x * 10ULL) return 12;\n" ++
  "    if (mulChain(x, (uint32_t)x) != x * 9ULL + (uint64_t)((uint32_t)x * 12u)) return 13;\n" ++
  "  }\n" ++
  "  return 0;\n" ++
  "}\n"

#eval show IO Unit from do
  IO.FS.withTempDir fun dir => do
    let asmPath := dir / "test.s"
    let cPath := dir / "main.c"
    let binPath := dir / "test_bin"
    IO.FS.writeFile asmPath (asmOf allFns)
    IO.FS.writeFile cPath execHarnessC
    let compOut ← IO.Process.output {
      cmd := "timeout"
      args := #["30", "cc", "-O1", "-o", binPath.toString, cPath.toString, asmPath.toString]
    }
    if compOut.exitCode != 0 then
      throw <| IO.userError s!"cc failed ({compOut.exitCode}): {compOut.stderr}"
    let runOut ← IO.Process.output { cmd := "timeout", args := #["15", binPath.toString] }
    if runOut.exitCode != 0 then
      throw <| IO.userError s!"native x86_64 execution failed ({runOut.exitCode}): {runOut.stderr}"

/-! ## 4. Axiom Audit (`std3`) & Isolation Checks -/

theorem x64TestJsLea_gprSpec_check : GprTarget x64Mach x64Gpr x64Scratch :=
  x64_gprSpec

theorem x64TestJsLea_labelClean_check : Rega.LabelClean x64Target.toIsa :=
  x64LabelClean

theorem x64TestJsLea_flat_eq_check (h : x64Target.toIsa.Hints) (f : TFlatFn)
    (hwf : f.wfCheck = true) :
    compileFlatFn x64Target.toIsa x64LegalTarget h f =
      compileFn x64Target.toIsa x64LegalTarget h f.toFn :=
  compileFlatFn_eq_compileFn x64Target.toIsa x64LegalTarget h f hwf

#print axioms LeanQbe.T.Amd64.x64Gpr_testJcc_spec
#print axioms LeanQbe.T.Amd64.x64Gpr_testJcc_noLab
#print axioms LeanQbe.T.Amd64.opBin_leaMul_z
#print axioms LeanQbe.T.Amd64.x64_gprSpec
#print axioms LeanQbe.T.Amd64.x64LabelClean
#print axioms LeanQbe.T.Rega.lowerFn_correct
#print axioms LeanQbe.T.compileFlatFn_eq_compileFn

open Lean

private def allowedStdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]
private def isForbiddenArmMod (m : Name) : Bool :=
  (m.toString.splitOn "Arm64").length > 1 || m.toString.startsWith "Kraken.AArch64"
private def isForbiddenVllMod (m : Name) : Bool :=
  (m.toString.splitOn "Vll").length > 1

#eval show MetaM Unit from do
  let testBad := (← getEnv).header.moduleNames.filter fun m =>
    isForbiddenArmMod m || isForbiddenVllMod m
  if !testBad.isEmpty then
    throwError "X64TestJsLeaTest imports Arm64/AArch64/Vll: {testBad.toList}"
  let env ← getEnv
  for nm in [``LeanQbe.T.Amd64.x64Gpr_testJcc_spec,
      ``LeanQbe.T.Amd64.x64Gpr_testJcc_noLab,
      ``LeanQbe.T.Amd64.opBin_leaMul_z,
      ``LeanQbe.T.Amd64.x64_gprSpec, ``LeanQbe.T.Amd64.x64LabelClean,
      ``LeanQbe.T.Rega.lowerFn_correct, ``LeanQbe.T.compileFlatFn_eq_compileFn,
      ``x64TestJsLea_gprSpec_check, ``x64TestJsLea_labelClean_check,
      ``x64TestJsLea_flat_eq_check] do
    let axs ← Lean.collectAxioms nm
    let badAx := axs.filter fun a => !allowedStdAxioms.contains a
    if !badAx.isEmpty then throwError "Disallowed axioms for {nm}: {badAx.toList}"
    let some ci := env.find? nm | throwError "Missing {nm}"
    if ci.isUnsafe then throwError "{nm} is unsafe"

end LeanQbeTest.T.X64TestJsLeaTest
