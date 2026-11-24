module

public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Bignum
public import LeanQbe.T.Spill
public import LeanQbeTest.T.RegaTestKit
public import LeanQbeTest.T.Arm64DirPreds
meta import LeanQbe.T.Arm64.TargLemmas
meta import LeanQbe.T.Examples.Bignum
meta import LeanQbe.T.Spill
meta import LeanQbeTest.T.RegaTestKit
meta import LeanQbeTest.T.Arm64DirPreds
public meta import Kraken.AArch64.Print

/-!
# Flag Fusion, Flag-Coloring Fixpoint & Per-Call Live-Range Splitting on AArch64

AArch64 twin of `LeanQbeTest.T.FlagRaOptTest` (x64), kept in its own module so the two targets'
Kraken ISAs are never co-imported. Every check compiles through the verified `Rega.lowerFn` via
`checkCompile` on `armTarget`:

1. Flag fusion over `GprIsa.cmpFlags`: all `240` `cmp` cases (`10` `CmpOp`s, `4` widths, `3`
   operand forms, `select`/`jnz` consumers) compile with zero `cset` (`CSINC`).
2. `Bignum` keeps compiling with no more `cset`s than before (`mul4x4`: `21`).
3. The `SpillFlags` fixpoint keeps `addcAfterUlt`/`addcAfterCmp`/`addcAfterSlt` compiling.
4. Per-call splitting: the `sel`-style cold-branch call leaves the fast path spill-free.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.FlagRaOptArm64Test

open LeanQbe.T LeanQbe.T.Arm64
open LeanQbeTest.T.RegaTestKit
open LeanQbeTest.T.Arm64DirPreds

/-! ## Helpers -/

/-- Hints from the default heuristics (`Fn.computeHints` = `Spill.hints ∘ Fn.mid`). -/
meta def hintsOf (fs : List Fn) : List armTarget.toIsa.Hints :=
  RegaTestKit.hintsOf armTarget armLegalTarget fs

/-- End-to-end verified compilation check (lowering, labels, stack bounds). -/
meta def chk (fs : List Fn) : Bool :=
  RegaTestKit.chk armTarget armLayout armLegalTarget fs

/-- Emitted code of a module (empty on a compile error). -/
meta def codeOf (fs : List Fn) : List armTarget.toIsa.Directive :=
  RegaTestKit.codeOf armTarget armLegalTarget fs

/-! ## 1. Flag fusion: `240` `cmp` cases, zero `cset` -/

#guard cmpCases.length == 240
#guard cmpCases.all fun f => chk [f]
#guard (cmpCases.map fun f => countDirs isCsetDir (codeOf [f])).sum == 0

/-! ## 2. `Bignum` keeps compiling without extra `cset`s -/

#guard chk Examples.Bignum.mul4x4Module.fns
#guard countDirs isCsetDir (codeOf Examples.Bignum.mul4x4Module.fns) ≤ 21
#guard chk Examples.Bignum.addMod25519Module.fns && chk Examples.Bignum.subMod25519Module.fns

/-! ## 3. `SpillFlags` fixpoint: no failed `adcx`/`adox` speculation -/

#guard chk [addcAfter "addcAfterUlt" .ult]
#guard chk [addcAfter "addcAfterCmp" .eq]
#guard chk [addcAfter "addcAfterSlt" .slt]

/-! ## 4. Per-call splitting: cold-branch call, spill-free fast path -/

meta def selMid : Fn := selFn.mid armLegalTarget
meta def selHints : armTarget.toIsa.Hints := Spill.hints armTarget.toIsa selMid
meta def selTree : Live.Tree × List (Nat × Ty) × Nat × Nat × Nat × Trie Ty := Live.Tree.ofFn selMid

#guard chk [slowFn, selFn]
#guard selHints.saved.isEmpty
#guard
  let cs := callIps selTree.1
  let ips := slotMoveIps selHints selTree.2.2.2.2.1
  cs.length == 1 && ips.length == 2 && ips.all fun ip => cs.any fun c => ip == c || ip == c + 1

/-! ## 5. `[base + disp]` addressing on AArch64 (`armSupportsAddrDisp`) -/

/-- Scaled positive offset (`+16` for `i32`/`i64`) is elided cleanly across `cmp` (`0 cset`). -/
meta def addrDispFn : Fn :=
  ⟨"addrDispArm64", [i64, i64], [i64], fun _ _ (p, y, ()) =>
    .let_ (op2 (.cmp .ult i64) (.var p) (.var y)) fun (c, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 16)) fun (p1, ()) =>
    .load i32 (.var p1) fun a =>
    .let_ (op1 (.zext 32 64) (.var a)) fun (az, ()) =>
    .store (t := i64) (.var az) (.var p1) (
    .let_ (op3 (.select i64) (.var c) (.var p) (.var y)) fun (r, ()) =>
    .ret (.var r, ()))⟩

/-- Elided `add64 +24` across `call slow`: keeps `p` across the call and folds `[x, #24]`. -/
meta def addrCallFn : Fn :=
  ⟨"addrCallArm64", [i64, i64], [i64], fun _ _ (p, k, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 24)) fun (p1, ()) =>
    .call "slow" (as := [i64]) (bs := [i64]) (.var k, ()) fun (_r, ()) =>
    .load i64 (.var p1) fun x =>
    .ret (.var x, ())⟩

/-- Unaligned (`+4` for `i64`), negative (`sub 8`), and out-of-range (`4096 * 8`) offsets must NOT
be elided on Arm64 (would force `.X16` literal-pool `ldr =...` fallback inside `armSetupAddr`). -/
meta def addrSkipArm64Fn : Fn :=
  ⟨"addrSkipArm64", [i64], [i64], fun _ _ (p, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 4)) fun (pUnalign, ()) =>
    .load i64 (.var pUnalign) fun a =>
    .let_ (op2 (.sub i64) (.var p) (.imm 8)) fun (pNeg, ()) =>
    .load i32 (.var pNeg) fun b =>
    .let_ (op2 (.add i64) (.var p) (.imm (BitVec.ofNat 64 (4096 * 8)))) fun (pOor, ()) =>
    .load i64 (.var pOor) fun c =>
    .let_ (op1 (.zext 32 64) (.var b)) fun (bz, ()) =>
    .let_ (op2 (.add i64) (.var a) (.var bz)) fun (s1, ()) =>
    .let_ (op2 (.add i64) (.var s1) (.var c)) fun (s2, ()) =>
    .ret (.var s2, ())⟩

#guard chk [addrDispFn]
#guard countDirs isArmAddSubOrPoolDir (codeOf [addrDispFn]) == 0
#guard countDirs isCsetDir (codeOf [addrDispFn]) == 0
#guard chk [slowFn, addrCallFn]
#guard (Fn.computeHints armTarget.toIsa armLegalTarget addrCallFn).elide.getD 0 false == true
#guard chk [addrSkipArm64Fn]
#guard (Fn.computeHints armTarget.toIsa armLegalTarget addrSkipArm64Fn).elide.getD 0 false == false
#guard (Fn.computeHints armTarget.toIsa armLegalTarget addrSkipArm64Fn).elide.getD 2 false == false
#guard (Fn.computeHints armTarget.toIsa armLegalTarget addrSkipArm64Fn).elide.getD 4 false == false

/-! ## 6. `[base, idx, lsl #k]` scaled-index addressing (`armSupportsAddrIdx`) -/

/-- `(idx <<< 2) + base` and `base + (idx <<< 3)` are folded into `[xb, xm, lsl #2/#3]`. -/
meta def sibIdx64Fn : Fn :=
  ⟨"sibIdx64Arm64", [i64, i64, i64], [i64], fun _ _ (base, idx, y, ()) =>
    .let_ (op2 (.cmp .ult i64) (.var idx) (.var y)) fun (c, ()) =>
    .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun (off4, ()) =>
    .let_ (op2 (.add i64) (.var base) (.var off4)) fun (p4, ()) =>
    .load i32 (.var p4) fun w =>
    .let_ (op1 (.zext 32 64) (.var w)) fun (wz, ()) =>
    .let_ (op2 (.shl i64) (.var idx) (.imm 3)) fun (off8, ()) =>
    .let_ (op2 (.add i64) (.var off8) (.var base)) fun (p8, ()) =>
    .store (t := i64) (.var wz) (.var p8) (
    .let_ (op3 (.select i64) (.var c) (.var idx) (.var y)) fun (r, ()) =>
    .ret (.var r, ()))⟩

/-- Elides `shl 3` + `add` across `call slow`, keeping `(base, idx)`
    and folding `[xb, xm, lsl #3]`. -/
meta def sibCallFn : Fn :=
  ⟨"sibCallArm64", [i64, i64, i64], [i64], fun _ _ (base, idx, k, ()) =>
    .let_ (op2 (.shl i64) (.var idx) (.imm 3)) fun (off, ()) =>
    .let_ (op2 (.add i64) (.var base) (.var off)) fun (p, ()) =>
    .call "slow" (as := [i64]) (bs := [i64]) (.var k, ()) fun (_r, ()) =>
    .load i64 (.var p) fun x =>
    .ret (.var x, ())⟩

/-- Mismatched scale (`shl 3` for `i32` load, `shl 4` for `i64` load) must NOT be elided. -/
meta def sibSkipArm64Fn : Fn :=
  ⟨"sibSkipArm64", [i64, i64], [i64], fun _ _ (base, idx, ()) =>
    .let_ (op2 (.shl i64) (.var idx) (.imm 3)) fun (offBad1, ()) =>
    .let_ (op2 (.add i64) (.var base) (.var offBad1)) fun (pBad1, ()) =>
    .load i32 (.var pBad1) fun a =>
    .let_ (op2 (.shl i64) (.var idx) (.imm 4)) fun (offBad2, ()) =>
    .let_ (op2 (.add i64) (.var base) (.var offBad2)) fun (pBad2, ()) =>
    .load i64 (.var pBad2) fun b =>
    .let_ (op1 (.zext 32 64) (.var a)) fun (az, ()) =>
    .let_ (op2 (.add i64) (.var az) (.var b)) fun (sum, ()) =>
    .ret (.var sum, ())⟩

#guard chk [sibIdx64Fn]
#guard (Fn.computeHints armTarget.toIsa armLegalTarget sibIdx64Fn).elide.getD 1 false == true
#guard (Fn.computeHints armTarget.toIsa armLegalTarget sibIdx64Fn).elide.getD 2 false == true
#guard (Fn.computeHints armTarget.toIsa armLegalTarget sibIdx64Fn).elide.getD 5 false == true
#guard (Fn.computeHints armTarget.toIsa armLegalTarget sibIdx64Fn).elide.getD 6 false == true
#guard countDirs isArmAddSubShlOrPoolDir (codeOf [sibIdx64Fn]) == 0
#guard countDirs isCsetDir (codeOf [sibIdx64Fn]) == 0
#guard countDirs isArmSibDir (codeOf [sibIdx64Fn]) == 2
#guard chk [slowFn, sibCallFn]
#guard (Fn.computeHints armTarget.toIsa armLegalTarget sibCallFn).elide.getD 0 false == true
#guard (Fn.computeHints armTarget.toIsa armLegalTarget sibCallFn).elide.getD 1 false == true
#guard countDirs isArmSibDir (codeOf [slowFn, sibCallFn]) == 1
#guard chk [sibSkipArm64Fn]
#guard (Fn.computeHints armTarget.toIsa armLegalTarget sibSkipArm64Fn).elide.getD 0 false == false
#guard (Fn.computeHints armTarget.toIsa armLegalTarget sibSkipArm64Fn).elide.getD 3 false == false
#guard countDirs isArmSibDir (codeOf [sibSkipArm64Fn]) == 0

/-! ## 7. Upper-32 zeroing parity (`zext 32->64` elision vs `sext 32->64`) -/

/-- `zext 32 64` after `load i32`, `add i32`, and `sext 8->32` is elided (`0` `orr w`/`ubfm`). -/
meta def zextElideArm64Fn : Fn :=
  ⟨"zextElideArm64", [i64, i32, i32, i8], [i64], fun _ _ (p, x, y, b, ()) =>
    .load i32 (.var p) fun ld =>
    .let_ (op1 (.zext 32 64) (.var ld)) fun (z0, ()) =>
    .let_ (op2 (.add i32) (.var x) (.var y)) fun (s, ()) =>
    .let_ (op1 (.zext 32 64) (.var s)) fun (z1, ()) =>
    .let_ (op1 (.sext 8 32) (.var b)) fun (s8, ()) =>
    .let_ (op1 (.zext 32 64) (.var s8)) fun (z2, ()) =>
    .let_ (op2 (.add i64) (.var z0) (.var z1)) fun (t, ()) =>
    .let_ (op2 (.add i64) (.var t) (.var z2)) fun (res, ()) =>
    .ret (.var res, ())⟩

/-- `sext 32 64` must NOT be elided after `load i32` (`sbfm x, x, #0, #31` must remain). -/
meta def sextKeepArm64Fn : Fn :=
  ⟨"sextKeepArm64", [i64], [i64], fun _ _ (p, ()) =>
    .load i32 (.var p) fun x =>
    .let_ (op1 (.sext 32 64) (.var x)) fun (sx, ()) =>
    .ret (.var sx, ())⟩

#guard chk [zextElideArm64Fn]
#guard countDirs isArmOrrWOrUbfmDir (codeOf [zextElideArm64Fn]) == 0
#guard chk [sextKeepArm64Fn]
#guard countDirs isArmSext32Dir (codeOf [sextKeepArm64Fn]) == 1

end LeanQbeTest.T.FlagRaOptArm64Test
