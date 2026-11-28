module

import LeanQbe.T.Amd64.TargLemmas
import LeanQbe.T.Examples.Bignum
import LeanQbe.T.Spill
import LeanQbeTest.T.RegaTestKit
meta import LeanQbe.T.Amd64.TargLemmas
meta import LeanQbe.T.Examples.Bignum
meta import LeanQbe.T.Spill
meta import LeanQbeTest.T.RegaTestKit

/-!
# Flag Fusion, Flag-Coloring Fixpoint & Per-Call Live-Range Splitting on x64

Regression tests for the untrusted `Spill` / `SpillFlags` hint heuristics on `x64Target` (every
check compiles through the verified `Rega.lowerFn` via `checkCompile`); the AArch64 twin is
`LeanQbeTest.T.FlagRaOptArm64Test` (the two targets' Kraken ISAs are never co-imported):

1. Flag fusion over `GprIsa.cmpFlags`: all `240` combinations of `10` `CmpOp`s, `4` widths, `3`
   operand forms (reg-reg, reg-imm, imm-reg) and `2` consumers (`select`, `jnz`) compile with
   zero `setcc`.
2. Carry-first condition priority: `Bignum.mul4x4` keeps `11 mulx`, `12 adcx`, `12 adox`, and
   `0 setcc`.
3. The `SpillFlags` fixpoint: a `cmp` web live across an `.addc` whose carry-out cannot stay in
   flags no longer relies on a speculated `adcx`/`adox` variant (`addcAfterUlt` and
   `addcAfterCmp` used to fail `Rega` with `let: op`).
4. Per-call splitting: in a `sel`-style function whose cold branch calls `slow`, the call-crossing
   argument lives in a caller-saved register, no callee-saved register is saved, and every stack
   access sits at the call (backup store) or right after it (reload): the fast path has no
   spills.
-/

set_option autoImplicit false


namespace LeanQbeTest.T.FlagRaOptTest

open LeanQbe.T LeanQbe.T.Amd64
open LeanQbeTest.T.RegaTestKit

/-! ## Helpers -/

/-- Hints from the default heuristics (`Fn.computeHints` = `Spill.hints ∘ Fn.mid`). -/
meta def hintsOf (fs : List Fn) : List x64Target.toIsa.Hints :=
  RegaTestKit.hintsOf x64Target x64LegalTarget fs

/-- End-to-end verified compilation check (lowering, labels, stack bounds). -/
meta def chk (fs : List Fn) : Bool :=
  RegaTestKit.chk x64Target x64Layout x64LegalTarget fs

/-- Emitted code of a module (empty on a compile error). -/
meta def codeOf (fs : List Fn) : List x64Target.toIsa.Directive :=
  RegaTestKit.codeOf x64Target x64LegalTarget fs

meta def isSetccDir : Directive → Bool
  | .instr (.regular _ _ (.setcc _ _)) => true
  | _ => false

meta def isMulxDir : Directive → Bool
  | .instr (.regular _ _ (.mulx _ _ _)) => true
  | _ => false

meta def isAdcxDir : Directive → Bool
  | .instr (.regular _ _ (.adcx _ _)) => true
  | _ => false

meta def isAdoxDir : Directive → Bool
  | .instr (.regular _ _ (.adox _ _)) => true
  | _ => false

/-! ## 1. Flag fusion: `240` `cmp` cases, zero `setcc` -/

#guard cmpCases.length == 240
#guard cmpCases.all fun f => chk [f]
#guard (cmpCases.map fun f => countDirs isSetccDir (codeOf [f])).sum == 0

/-! ## 2. Carry-first priority keeps `mul4x4`'s dual carry chains -/

meta def mul4x4Code : List Directive := codeOf Examples.Bignum.mul4x4Module.fns

#guard chk Examples.Bignum.mul4x4Module.fns
#guard countDirs isMulxDir mul4x4Code == 11
#guard countDirs isAdcxDir mul4x4Code == 12
#guard countDirs isAdoxDir mul4x4Code == 12
#guard countDirs isSetccDir mul4x4Code == 0
#guard chk Examples.Bignum.addMod25519Module.fns && chk Examples.Bignum.subMod25519Module.fns

/-! ## 3. `SpillFlags` fixpoint: no failed `adcx`/`adox` speculation -/

#guard chk [addcAfter "addcAfterUlt" .ult]
#guard chk [addcAfter "addcAfterCmp" .eq]
#guard chk [addcAfter "addcAfterSlt" .slt]

/-! ## 4. Per-call splitting: cold-branch call, spill-free fast path -/

meta def selMid : Fn := selFn.mid x64LegalTarget
meta def selHints : x64Target.toIsa.Hints := Spill.hints x64Target.toIsa selMid
meta def selTree : Live.Tree × List (Nat × Ty) × Nat × Nat × Nat × Trie Ty := Live.Tree.ofFn selMid

#guard chk [slowFn, selFn]
#guard selHints.saved.isEmpty
#guard
  let cs := callIps selTree.1
  let ips := slotMoveIps selHints selTree.2.2.2.2.1
  cs.length == 1 && ips.length == 2 && ips.all fun ip => cs.any fun c => ip == c || ip == c + 1

/-! ## 5. `[base + disp]` addressing via `Hints.elide` + `DefFact.addImm64` -/

meta def isAddSubLeaDir : Directive → Bool
  | .instr (.regular _ .W64 (.add (.reg (.low .rsp .W64)) _))
  | .instr (.regular _ .W64 (.sub (.reg (.low .rsp .W64)) _)) => false
  | .instr (.regular _ _ (.add _ _))
  | .instr (.regular _ _ (.sub _ _))
  | .instr (.regular _ _ (.lea _ _)) => true
  | _ => false

/-- Elides both `add64 +16` and `sub64 8` (`[-8]`) into memory displacements; preserves `cmp`
flags live across the elided `add64` (`0 setcc`). -/
meta def addrDispFn : Fn :=
  ⟨"addrDispX64", [i64, i64], [i64], fun _ _ (p, y, ()) =>
    .let_ (op2 (.cmp .ult i64) (.var p) (.var y)) fun (c, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 16)) fun (p1, ()) =>
    .let_ (op2 (.sub i64) (.var p) (.imm 8)) fun (p2, ()) =>
    .load i32 (.var p1) fun a =>
    .let_ (op1 (.zext 32 64) (.var a)) fun (az, ()) =>
    .store (t := i64) (.var az) (.var p2) (
    .let_ (op3 (.select i64) (.var c) (.var p) (.var y)) fun (r, ()) =>
    .ret (.var r, ()))⟩

/-- Elided address def whose base `p` crosses `call slow`, reloading `p` at the load site. -/
meta def addrCallFn : Fn :=
  ⟨"addrCallX64", [i64, i64], [i64], fun _ _ (p, k, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 24)) fun (p1, ()) =>
    .call "slow" (as := [i64]) (bs := [i64]) (.var k, ()) fun (_r, ()) =>
    .load i64 (.var p1) fun x =>
    .ret (.var x, ())⟩

/-- Vector `[base + disp]` (`v4i32` unaligned load at `base + 32`) elides `add64`. -/
meta def addrVecFn : Fn :=
  ⟨"addrVecX64", [i64], [v4i32], fun _ _ (p, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 32)) fun (p1, ()) =>
    .load v4i32 (.var p1) fun v =>
    .ret (.var v, ())⟩

/-- Non-address use (value of `store`) prevents elision, and out-of-int32 disp (`2^33`) prevents
elision so no fallback `movabs+add` inside `addrToExpr` is triggered. -/
meta def addrNoElideFn : Fn :=
  ⟨"addrNoElideX64", [i64, i64], [i64], fun _ _ (p, q, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 8)) fun (v1, ()) =>
    .store (t := i64) (.var v1) (.var q) (
    .let_ (op2 (.add i64) (.var p) (.imm (BitVec.ofNat 64 (2 ^ 33)))) fun (pBig, ()) =>
    .load i64 (.var pBig) fun r =>
    .ret (.var r, ()))⟩

#guard chk [addrDispFn]
#guard countDirs isAddSubLeaDir (codeOf [addrDispFn]) == 0
#guard countDirs isSetccDir (codeOf [addrDispFn]) == 0
#guard chk [slowFn, addrCallFn]
#guard (Fn.computeHints x64Target.toIsa x64LegalTarget addrCallFn).elide.getD 0 false == true
#guard chk [addrVecFn]
#guard countDirs isAddSubLeaDir (codeOf [addrVecFn]) == 0
#guard chk [addrNoElideFn]
#guard (Fn.computeHints x64Target.toIsa x64LegalTarget addrNoElideFn).elide.getD 0 false == false
#guard (Fn.computeHints x64Target.toIsa x64LegalTarget addrNoElideFn).elide.getD 2 false == false

/-! ## 6. `[base + idx * scale + disp]` SIB addressing (`Hints.elide` + `DefFact`) -/

meta def isSibMemDir : Directive → Bool
  | .instr (.regular _ _ (.mov dst src)) =>
    (match dst with | .mem e => e.idx.isSome | _ => false) ||
    (match src with | .regOrMem (.mem e) => e.idx.isSome | _ => false)
  | .instr (.regular _ _ (.movzx dst src)) =>
    (match dst with | .mem e => e.idx.isSome | _ => false) ||
    (match src with | .mem e => e.idx.isSome | _ => false)
  | _ => false

meta def isShlDir : Directive → Bool
  | .instr (.regular _ _ (.shl _ _)) => true
  | _ => false

/-- Covers Kissat SIB patterns: `vals[lit]` (`scale=1`, `zext`), `ar[(idx+2)<<2]` &
`ar[(idx+3)<<2]` (`scale=4, disp=8,12` across `cmp`/`select`), and `wvec[(lit<<1)+1]`
(`scale=8, disp=4` store). Emits 4 SIB memory ops, 0 `shl`, 0 `add`/`sub`/`lea`, 0 `setcc`. -/
meta def addrSibChainFn : Fn :=
  ⟨"addrSibChainX64", [i64, i64, i64, i32, i64], [i32],
    fun _ _ (vals, ar, wvec, lit, idx, ()) =>
      .let_ (op1 (.zext 32 64) (.var lit)) fun (lit64, ()) =>
      .let_ (op2 (.add i64) (.var vals) (.var lit64)) fun (pv, ()) =>
      .load i8 (.var pv) fun vb =>
      .let_ (op1 (.zext 8 32) (.var vb)) fun (vb32, ()) =>
      .let_ (op2 (.cmp .ult i64) (.var idx) (.var vals)) fun (c, ()) =>
      .let_ (op2 (.add i64) (.var idx) (.imm 2)) fun (c2, ()) =>
      .let_ (op2 (.shl i64) (.var c2) (.imm 2)) fun (o2, ()) =>
      .let_ (op2 (.add i64) (.var ar) (.var o2)) fun (pa2, ()) =>
      .let_ (op2 (.add i64) (.var idx) (.imm 3)) fun (c3, ()) =>
      .let_ (op2 (.shl i64) (.var c3) (.imm 2)) fun (o3, ()) =>
      .let_ (op2 (.add i64) (.var ar) (.var o3)) fun (pa3, ()) =>
      .load i32 (.var pa2) fun a2 =>
      .load i32 (.var pa3) fun a3 =>
      .let_ (op2 (.shl i64) (.var lit64) (.imm 3)) fun (wl, ()) =>
      .let_ (op2 (.add i64) (.var wvec) (.var wl)) fun (pw0, ()) =>
      .let_ (op2 (.add i64) (.var pw0) (.imm 4)) fun (pw1, ()) =>
      .store (t := i32) (.var vb32) (.var pw1) (
      .let_ (op3 (.select i32) (.var c) (.var a2) (.var a3)) fun (res, ()) =>
      .ret (.var res, ()))⟩

/-- Elides `(idx + 1) << 2` + `base` across `call slow`, preserving `p` and `idx` live. -/
meta def addrSibCallFn : Fn :=
  ⟨"addrSibCallX64", [i64, i64, i64], [i64], fun _ _ (p, idx, k, ()) =>
    .let_ (op2 (.add i64) (.var idx) (.imm 1)) fun (i1, ()) =>
    .let_ (op2 (.shl i64) (.var i1) (.imm 2)) fun (off, ()) =>
    .let_ (op2 (.add i64) (.var p) (.var off)) fun (pa, ()) =>
    .call "slow" (as := [i64]) (bs := [i64]) (.var k, ()) fun (_r, ()) =>
    .load i64 (.var pa) fun x =>
    .ret (.var x, ())⟩

/-- Vector `vload` with `[base + idx * 8 + 16]` SIB elides `add`/`shl`. -/
meta def addrSibVecFn : Fn :=
  ⟨"addrSibVecX64", [i64, i64], [v4i32], fun _ _ (p, idx, ()) =>
    .let_ (op2 (.add i64) (.var idx) (.imm 2)) fun (i2, ()) =>
    .let_ (op2 (.shl i64) (.var i2) (.imm 3)) fun (off, ()) =>
    .let_ (op2 (.add i64) (.var p) (.var off)) fun (pa, ()) =>
    .load v4i32 (.var pa) fun v =>
    .ret (.var v, ())⟩

/-- Scale-shift overflow (`<< 4`), non-address value use, and int32 disp overflow prevent SIB
elision cleanly. -/
meta def addrSibNoElideFn : Fn :=
  ⟨"addrSibNoElideX64", [i64, i64, i64], [i64], fun _ _ (p, idx, q, ()) =>
    .let_ (op2 (.shl i64) (.var idx) (.imm 4)) fun (s16, ()) =>
    .let_ (op2 (.add i64) (.var p) (.var s16)) fun (p16, ()) =>
    .load i64 (.var p16) fun v0 =>
    .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun (s4, ()) =>
    .let_ (op2 (.add i64) (.var p) (.var s4)) fun (pEsc, ()) =>
    .store (t := i64) (.var pEsc) (.var q) (
    .let_ (op2 (.add i64) (.var idx) (.imm (BitVec.ofNat 64 (2 ^ 30)))) fun (ib, ()) =>
    .let_ (op2 (.shl i64) (.var ib) (.imm 3)) fun (ob, ()) =>
    .let_ (op2 (.add i64) (.var p) (.var ob)) fun (pBig, ()) =>
    .load i64 (.var pBig) fun v1 =>
    .let_ (op2 (.add i64) (.var v0) (.var v1)) fun (r, ()) =>
    .ret (.var r, ()))⟩

#guard chk [addrSibChainFn]
#guard countDirs isSibMemDir (codeOf [addrSibChainFn]) == 4
#guard countDirs isShlDir (codeOf [addrSibChainFn]) == 0
#guard countDirs isAddSubLeaDir (codeOf [addrSibChainFn]) == 0
#guard countDirs isSetccDir (codeOf [addrSibChainFn]) == 0
#guard chk [slowFn, addrSibCallFn]
#guard countDirs isSibMemDir (codeOf [slowFn, addrSibCallFn]) == 1
#guard countDirs isShlDir (codeOf [slowFn, addrSibCallFn]) == 0
#guard countDirs isAddSubLeaDir (codeOf [slowFn, addrSibCallFn]) == 0
#guard (Fn.computeHints x64Target.toIsa x64LegalTarget addrSibCallFn).elide.getD 0 false == true
#guard (Fn.computeHints x64Target.toIsa x64LegalTarget addrSibCallFn).elide.getD 1 false == true
#guard (Fn.computeHints x64Target.toIsa x64LegalTarget addrSibCallFn).elide.getD 2 false == true
#guard chk [addrSibVecFn]
#guard countDirs isShlDir (codeOf [addrSibVecFn]) == 0
#guard countDirs isAddSubLeaDir (codeOf [addrSibVecFn]) == 0
#guard chk [addrSibNoElideFn]
#guard (Fn.computeHints x64Target.toIsa x64LegalTarget addrSibNoElideFn).elide.getD 0 false == false
#guard (Fn.computeHints x64Target.toIsa x64LegalTarget addrSibNoElideFn).elide.getD 3 false == false
#guard (Fn.computeHints x64Target.toIsa x64LegalTarget addrSibNoElideFn).elide.getD 6 false == false

/-- `wstk[end + 1ULL]` scaled address folding (SIB scaled addressing): `end = off + sz`
(represented as `addrSum off sz 0 0`) followed by `p = end + 1`, `sh = p << 2`, `ptr = wstk + sh`
records `ptr` as `addrSum wstk end 2 4`, emitting `4(%wstk,%end,4)` and eliding `p`, `sh`, `ptr`. -/
meta def addrSibScaledDispFn : Fn :=
  ⟨"addrSibScaledDispX64", [i64, i64, i64, i32], [i32],
    fun _ _ (wstk, off, sz, val, ()) =>
      .let_ (op2 (.add i64) (.var off) (.var sz)) fun (endv, ()) =>
      .let_ (op2 (.add i64) (.var endv) (.imm 1)) fun (p1, ()) =>
      .let_ (op2 (.shl i64) (.var p1) (.imm 2)) fun (sh1, ()) =>
      .let_ (op2 (.add i64) (.var wstk) (.var sh1)) fun (ptr1, ()) =>
      .let_ (op2 (.add i64) (.var endv) (.imm 2)) fun (p2, ()) =>
      .let_ (op2 (.shl i64) (.var p2) (.imm 2)) fun (sh2, ()) =>
      .let_ (op2 (.add i64) (.var wstk) (.var sh2)) fun (ptr2, ()) =>
      .store (t := i32) (.var val) (.var ptr1) (
      .load i32 (.var ptr2) fun r =>
      .ret (.var r, ()))⟩

meta def addrSibScaledDispHints : x64Target.toIsa.Hints :=
  Fn.computeHints x64Target.toIsa x64LegalTarget addrSibScaledDispFn

#guard chk [addrSibScaledDispFn]
#guard countDirs isSibMemDir (codeOf [addrSibScaledDispFn]) == 2
#guard countDirs isShlDir (codeOf [addrSibScaledDispFn]) == 0
#guard [1, 2, 3, 4, 5, 6].all fun ip => addrSibScaledDispHints.elide.getD ip false == true

/-- Non-destructive 3-address `lea` for live inputs (`x + y`, `x + 3`, `y - 2`) with both
`x` and `y` live to the return tuple, emitting `lea` instead of `mov + add/sub`, plus `cmp`/`select`
with `0 setcc` across `x + 3`/`y - 2`. -/
meta def leaNonDestructFn : Fn :=
  ⟨"leaNonDestructX64", [i64, i64], [i64, i64], fun _ _ (x, y, ()) =>
    .let_ (op2 (.add i64) (.var x) (.var y)) fun (s1, ()) =>
    .let_ (op2 (.cmp .ult i64) (.var x) (.var y)) fun (c, ()) =>
    .let_ (op2 (.add i64) (.var x) (.imm 3)) fun (s2, ()) =>
    .let_ (op2 (.sub i64) (.var y) (.imm 2)) fun (s3, ()) =>
    .let_ (op3 (.select i64) (.var c) (.var s2) (.var s3)) fun (r0, ()) =>
    .let_ (op2 (.xor i64) (.var x) (.var y)) fun (k0, ()) =>
    .let_ (op2 (.xor i64) (.var r0) (.var k0)) fun (r1, ()) =>
    .ret (.var s1, .var r1, ())⟩

meta def isAddOrSubDir : Directive → Bool
  | .instr (.regular _ .W64 (.add (.reg (.low .rsp .W64)) _))
  | .instr (.regular _ .W64 (.sub (.reg (.low .rsp .W64)) _)) => false
  | .instr (.regular _ _ (.add _ _))
  | .instr (.regular _ _ (.sub _ _)) => true
  | _ => false

meta def isLeaDir : Directive → Bool
  | .instr (.regular _ _ (.lea _ _)) => true
  | _ => false

#guard chk [leaNonDestructFn]
#guard countDirs isAddOrSubDir (codeOf [leaNonDestructFn]) == 0
#guard countDirs isLeaDir (codeOf [leaNonDestructFn]) == 3
#guard countDirs isSetccDir (codeOf [leaNonDestructFn]) == 0

/-! ## 7. Upper-32 zero tracking: `zext 32 64` elision -/

meta def isMovlRegDir : Directive → Bool
  | .instr (.regular _ .W32 (.mov (.reg (.low _ .W32)) (.regOrMem (.reg (.low _ .W32))))) => true
  | _ => false

meta def isSelfMovlDir : Directive → Bool
  | .instr (.regular _ .W32 (.mov (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))) =>
    rd == rs
  | _ => false

/-- `load i32` directly followed by `zext 32 64` emits zero reg-to-reg `movl`. -/
meta def zext32LoadRetFn : Fn :=
  ⟨"zext32LoadRetX64", [i64], [i64], fun _ _ (p, ()) =>
    .load i32 (.var p) fun a =>
    .let_ (op1 (.zext 32 64) (.var a)) fun (z, ()) =>
    .ret (.var z, ())⟩

/-- `load i32`, `and i32`, and `lshr i32` preserve zero upper 32 bits even across `call slow`,
eliminating any self-`movl` at `zext 32 64`. -/
meta def zext32UpperZeroFn : Fn :=
  ⟨"zext32UpperZeroX64", [i64, i64], [i64], fun _ _ (p, k, ()) =>
    .load i32 (.var p) fun a =>
    .let_ (op2 (.and i32) (.var a) (.imm 0xfff)) fun (b, ()) =>
    .let_ (op2 (.lshr i32) (.var b) (.imm 1)) fun (c, ()) =>
    .call "slow" (as := [i64]) (bs := [i64]) (.var k, ()) fun (r0, ()) =>
    .let_ (op1 (.zext 32 64) (.var c)) fun (z, ()) =>
    .let_ (op2 (.add i64) (.var z) (.var r0)) fun (ans, ()) =>
    .ret (.var ans, ())⟩

/-- `trunc 64 32` can leave non-zero upper bits; `zext 32 64` must retain a `movl`. -/
meta def zext32AfterTruncFn : Fn :=
  ⟨"zext32AfterTruncX64", [i64], [i64], fun _ _ (x, ()) =>
    .let_ (op1 (.trunc 64 32) (.var x)) fun (y, ()) =>
    .let_ (op1 (.zext 32 64) (.var y)) fun (z, ()) =>
    .ret (.var z, ())⟩

#guard chk [zext32LoadRetFn]
#guard countDirs isMovlRegDir (codeOf [zext32LoadRetFn]) == 0
#guard chk [slowFn, zext32UpperZeroFn]
#guard countDirs isSelfMovlDir (codeOf [slowFn, zext32UpperZeroFn]) == 0
#guard chk [zext32AfterTruncFn]
#guard countDirs isMovlRegDir (codeOf [zext32AfterTruncFn]) >= 1

/-! ## 8. Flag/Mem-Compare Fusion & Zero-Frame Leaf Elision -/

meta def isTestDir : Directive → Bool
  | .instr (.regular _ _ (.test _ _)) => true
  | _ => false

meta def isTestMemDir : Directive → Bool
  | .instr (.regular _ _ (.test (.mem _) _)) => true
  | _ => false

meta def isCmpDir : Directive → Bool
  | .instr (.regular _ _ (.cmp _ _)) => true
  | _ => false

meta def isCmpbMemDir : Directive → Bool
  | .instr (.regular _ .W8 (.cmp (.mem _) _)) => true
  | _ => false

meta def isCmpMemDir : Directive → Bool
  | .instr (.regular _ _ (.cmp (.mem _) _)) => true
  | _ => false

meta def isAndDir : Directive → Bool
  | .instr (.regular _ _ (.and _ _)) => true
  | _ => false

meta def isMovzxOrSxDir : Directive → Bool
  | .instr (.regular _ _ (.movzx _ _)) => true
  | .instr (.regular _ _ (.movsx _ _)) => true
  | _ => false

meta def isRspAdjDir : Directive → Bool
  | .instr (.regular _ .W64 (.add (.reg (.low .rsp .W64)) _))
  | .instr (.regular _ .W64 (.sub (.reg (.low .rsp .W64)) _)) => true
  | _ => false

meta def isMovi64Dir : Directive → Bool
  | .instr (.regular _ .W64 (.mov (.reg (.low _ .W64)) (.imm _))) => true
  | _ => false

meta def isMovi32Dir : Directive → Bool
  | .instr (.regular _ .W32 (.mov (.reg (.low _ .W32)) (.imm _))) => true
  | _ => false

/-- Kissat BCP binary-watch bit test `(w & 0x80000000) != 0` fuses into `testl` (`0 and`/`cmp`). -/
meta def testImmFuseFn : Fn :=
  ⟨"testImmFuseX64", [i32, i64, i64], [i64], fun _ _ (w, a, b, ()) =>
    .let_ (op2 (.and i32) (.var w) (.imm 0x80000000#32)) fun (t, ()) =>
    .let_ (op2 (.cmp .ne i32) (.var t) (.imm 0#32)) fun (c, ()) =>
    .jnz (.var c) (.ret (.var a, ())) (.ret (.var b, ()))⟩

/-- Kissat `(marks[var] & 1) == 0` fuses `load i32` + `and` + `cmp` into `testl [mem]`. -/
meta def testMemFuseFn : Fn :=
  ⟨"testMemFuseX64", [i64, i64, i64, i64], [i64], fun _ _ (base, idx, a, b, ()) =>
    .let_ (op2 (.shl i64) (.var idx) (.imm 2#64)) fun (off, ()) =>
    .let_ (op2 (.add i64) (.var base) (.var off)) fun (p, ()) =>
    .load i32 (.var p) fun v =>
    .let_ (op2 (.and i32) (.var v) (.imm 1#32)) fun (t, ()) =>
    .let_ (op2 (.cmp .eq i32) (.var t) (.imm 0#32)) fun (c, ()) =>
    .jnz (.var c) (.ret (.var a, ())) (.ret (.var b, ()))⟩

/-- Kissat `vals[lit] < 0` (`sext 8 32 (load i8 [base+idx]) <s 0`) fuses into `cmpb $0, [mem]`. -/
meta def cmpbMemSextFn : Fn :=
  ⟨"cmpbMemSextX64", [i64, i64, i64, i64], [i64], fun _ _ (base, idx, a, b, ()) =>
    .let_ (op2 (.add i64) (.var base) (.var idx)) fun (p, ()) =>
    .load i8 (.var p) fun v =>
    .let_ (op1 (.sext 8 32) (.var v)) fun (s, ()) =>
    .let_ (op2 (.cmp .slt i32) (.var s) (.imm 0#32)) fun (c, ()) =>
    .jnz (.var c) (.ret (.var a, ())) (.ret (.var b, ()))⟩

/-- Unsigned byte compare `zext 8 32 (load i8 [base+idx]) == 5` fuses into `cmpb $5, [mem]`. -/
meta def cmpbMemZextFn : Fn :=
  ⟨"cmpbMemZextX64", [i64, i64, i64, i64], [i64], fun _ _ (base, idx, a, b, ()) =>
    .let_ (op2 (.add i64) (.var base) (.var idx)) fun (p, ()) =>
    .load i8 (.var p) fun v =>
    .let_ (op1 (.zext 8 32) (.var v)) fun (z, ()) =>
    .let_ (op2 (.cmp .eq i32) (.var z) (.imm 5#32)) fun (c, ()) =>
    .jnz (.var c) (.ret (.var a, ())) (.ret (.var b, ()))⟩

/-- Negative test: intervening `store` must block load-into-`cmp` elision (aliasing soundness). -/
meta def cmpMemStoreBlockFn : Fn :=
  ⟨"cmpMemStoreBlockX64", [i64, i64, i64, i64], [i64], fun _ _ (p, q, a, b, ()) =>
    .load i32 (.var p) fun v =>
    .store (t := i32) (.imm 0#32) (.var q) (
    .let_ (op2 (.cmp .eq i32) (.var v) (.imm 0#32)) fun (c, ()) =>
    .jnz (.var c) (.ret (.var a, ())) (.ret (.var b, ())))⟩

/-- Negative test: signed `<s` on `zext 8 32` must not narrow-fuse to signed `cmpb`. -/
meta def cmpZextSignedNoFuseFn : Fn :=
  ⟨"cmpZextSignedNoFuseX64", [i64, i64, i64], [i64], fun _ _ (p, a, b, ()) =>
    .load i8 (.var p) fun v =>
    .let_ (op1 (.zext 8 32) (.var v)) fun (z, ()) =>
    .let_ (op2 (.cmp .slt i32) (.var z) (.imm 0#32)) fun (c, ()) =>
    .jnz (.var c) (.ret (.var a, ())) (.ret (.var b, ()))⟩

/-- Compact 5-byte `movl $uimm32` for unsigned 32-bit constants in 64-bit returns, and 0-slot leaf
frame elision (`0` `%rsp` adjustments, stack bound `0`). -/
meta def movi32LeafFn : Fn :=
  ⟨"movi32LeafX64", [i64], [i64], fun _ _ (x, ()) =>
    .let_ (op2 (.xor i64) (.var x) (.imm 0xdeadbeef#64)) fun (y, ()) =>
    .ret (.var y, ())⟩

#guard chk [testImmFuseFn]
#guard countDirs isTestDir (codeOf [testImmFuseFn]) == 1
#guard countDirs isAndDir (codeOf [testImmFuseFn]) == 0
#guard countDirs isCmpDir (codeOf [testImmFuseFn]) == 0
#guard countDirs isSetccDir (codeOf [testImmFuseFn]) == 0
#guard countDirs isRspAdjDir (codeOf [testImmFuseFn]) == 0

#guard chk [testMemFuseFn]
#guard countDirs isTestMemDir (codeOf [testMemFuseFn]) == 1
#guard countDirs isAndDir (codeOf [testMemFuseFn]) == 0
#guard countDirs isCmpDir (codeOf [testMemFuseFn]) == 0
#guard countDirs isRspAdjDir (codeOf [testMemFuseFn]) == 0

#guard chk [cmpbMemSextFn]
#guard countDirs isCmpbMemDir (codeOf [cmpbMemSextFn]) == 1
#guard countDirs isMovzxOrSxDir (codeOf [cmpbMemSextFn]) == 0
#guard countDirs isRspAdjDir (codeOf [cmpbMemSextFn]) == 0

#guard chk [cmpbMemZextFn]
#guard countDirs isCmpbMemDir (codeOf [cmpbMemZextFn]) == 1
#guard countDirs isMovzxOrSxDir (codeOf [cmpbMemZextFn]) == 0

#guard chk [cmpMemStoreBlockFn]
#guard countDirs isCmpMemDir (codeOf [cmpMemStoreBlockFn]) == 0

#guard chk [cmpZextSignedNoFuseFn]
#guard countDirs isCmpbMemDir (codeOf [cmpZextSignedNoFuseFn]) == 0

#guard chk [movi32LeafFn]
#guard countDirs isMovi64Dir (codeOf [movi32LeafFn]) == 0
#guard countDirs isMovi32Dir (codeOf [movi32LeafFn]) >= 1
#guard countDirs isRspAdjDir (codeOf [movi32LeafFn]) == 0
#guard
  match compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes [] [] 0
      [movi32LeafFn] [Fn.computeHints x64Target.toIsa x64LegalTarget movi32LeafFn] with
  | .ok (_, [(_, b)]) => b == 0
  | _ => false

/-! ## 8. `jnz` jump-threading checks `Hints.pre` at the taken branch `ip` -/

/-- `then`-arm is `.jump` at `ip = 4` (after a multi-step `else`-arm at `ip = 2, 3`). -/
meta def jnzPreThenFn : Fn :=
  ⟨"jnzPreThenX64", [i64, i64, i64], [i64], fun _ _ (x, y, p, ()) =>
    .group (sig := [[i64]])
      (fun (j, ()) => .cons (fun (q, ()) => .ret (.var q, ())) .nil)
      (fun (j, ()) =>
        .let_ (op2 (.cmp .eq i64) (.var x) (.imm 0#64)) fun (c, ()) =>
        .jnz (.var c)
          (.jump j (.var x, ()))
          (.store (t := i64) (.var x) (.var p) (.jump j (.var y, ()))))⟩

/-- `else`-arm is `.jump` at `ip = 2` (before a multi-step `then`-arm). -/
meta def jnzPreElseFn : Fn :=
  ⟨"jnzPreElseX64", [i64, i64, i64], [i64], fun _ _ (x, y, p, ()) =>
    .group (sig := [[i64]])
      (fun (j, ()) => .cons (fun (q, ()) => .ret (.var q, ())) .nil)
      (fun (j, ()) =>
        .let_ (op2 (.cmp .eq i64) (.var x) (.imm 0#64)) fun (c, ()) =>
        .jnz (.var c)
          (.store (t := i64) (.var x) (.var p) (.jump j (.var y, ())))
          (.jump j (.var x, ())))⟩

meta def jnzThreadHints (f : Fn) : x64Target.toIsa.Hints :=
  let h0 := Fn.computeHints x64Target.toIsa x64LegalTarget f
  { h0 with entry := h0.entry.insert 0 { live := [], ploc := [.gpr .rdi] } }

meta def withPreAt (h : x64Target.toIsa.Hints) (ip : Nat)
    (ps : PreStep Reg64 RegMm CondCode) : x64Target.toIsa.Hints :=
  { h with pre := h.pre.insert ip ps }

meta def chkHints (f : Fn) (h : x64Target.toIsa.Hints) : Bool :=
  checkCompile x64Target x64Layout x64LegalTarget [] [] 0 [f] [h] 2048

meta def rdiSymSt : Rega.SymState x64Target.toIsa :=
  { regs := [(.var 0, .gpr .rdi), (.var 1, .gpr .rsi), (.var 2, .gpr .rdx)],
    slots := .empty, defs := .empty, vecWidths := .empty }

meta def jnzJump0 : Expr Rega.VNat Rega.LNat [i64] :=
  .jump (ts := [i64]) 0 (Arg.var 0, ())

#guard chk [jnzPreThenFn]
#guard chk [jnzPreElseFn]
#guard
  let h := jnzThreadHints jnzPreThenFn
  Rega.zeroMoveJump? x64Target.toIsa h 4 rdiSymSt jnzJump0 == some 0 &&
    chkHints jnzPreThenFn h
#guard
  let h := withPreAt (jnzThreadHints jnzPreThenFn) 4 { moves := [.mov .rax .rsi] }
  Rega.zeroMoveJump? x64Target.toIsa h 4 rdiSymSt jnzJump0 == none &&
    chkHints jnzPreThenFn h
#guard
  let h := withPreAt (jnzThreadHints jnzPreThenFn) 4 { clearFlags := true }
  Rega.zeroMoveJump? x64Target.toIsa h 4 rdiSymSt jnzJump0 == none &&
    chkHints jnzPreThenFn h
#guard
  let h := jnzThreadHints jnzPreElseFn
  Rega.zeroMoveJump? x64Target.toIsa h 2 rdiSymSt jnzJump0 == some 0 &&
    chkHints jnzPreElseFn h
#guard
  let h := withPreAt (jnzThreadHints jnzPreElseFn) 2 { moves := [.mov .rax .rsi] }
  Rega.zeroMoveJump? x64Target.toIsa h 2 rdiSymSt jnzJump0 == none &&
    chkHints jnzPreElseFn h
#guard
  let h := withPreAt (jnzThreadHints jnzPreElseFn) 2 { clearFlags := true }
  Rega.zeroMoveJump? x64Target.toIsa h 2 rdiSymSt jnzJump0 == none &&
    chkHints jnzPreElseFn h

/-! ## 9. Zero-instruction `.not .bool` flag-home coloring (`S06`) -/

meta def isXorDir : Directive → Bool
  | .instr (.regular _ _ (.xor _ _)) => true
  | _ => false

/-- `.not .bool` of a flag-homed `cmp` keeps a negated `.flag` home and feeds `jnz` directly
with `0` `setcc`, `0` `movzx`, and `0` `xor`. -/
meta def boolNotJnzFn : Fn :=
  ⟨"boolNotJnzX64", [i64, i64, i64, i64], [i64], fun _ _ (x, y, a, b, ()) =>
    .let_ (op2 (.cmp .ult i64) (.var x) (.var y)) fun (c, ()) =>
    .let_ (op1 (.not .bool) (.var c)) fun (nc, ()) =>
    .jnz (.var nc) (.ret (.var a, ())) (.ret (.var b, ()))⟩

/-- `.not .bool` feeding `select` keeps `0` `setcc`, `0` `movzx`, and `0` `xor`. -/
meta def boolNotSelectFn : Fn :=
  ⟨"boolNotSelectX64", [i32, i64, i64], [i64], fun _ _ (x, a, b, ()) =>
    .let_ (op2 (.cmp .eq i32) (.var x) (.imm 0#32)) fun (c, ()) =>
    .let_ (op1 (.not .bool) (.var c)) fun (nc, ()) =>
    .let_ (op3 (.select i64) (.var nc) (.var a) (.var b)) fun (r, ()) =>
    .ret (.var r, ())⟩

/-- Chained double negation `!!c` preserves zero-instruction flag-home lowering. -/
meta def boolDoubleNotFn : Fn :=
  ⟨"boolDoubleNotX64", [i64, i64, i64, i64], [i64], fun _ _ (x, y, a, b, ()) =>
    .let_ (op2 (.cmp .slt i64) (.var x) (.var y)) fun (c, ()) =>
    .let_ (op1 (.not .bool) (.var c)) fun (n1, ()) =>
    .let_ (op1 (.not .bool) (.var n1)) fun (n2, ()) =>
    .jnz (.var n2) (.ret (.var a, ())) (.ret (.var b, ()))⟩

/-- Negated flag-homed `.bool` stays in `.flag` across non-clobbering `lea` (`maskNone`) and
feeds both `select` (`cmovcc`) and `jnz` with `0` `setcc`, `0` `movzx`, and `0` `xor`. -/
meta def boolNotAcrossLeaFn : Fn :=
  ⟨"boolNotAcrossLeaX64", [i64, i64, i64, i64], [i64], fun _ _ (x, y, a, b, ()) =>
    .let_ (op2 (.cmp .ult i64) (.var x) (.imm 5#64)) fun (c1, ()) =>
    .let_ (op2 (.add i64) (.var y) (.imm 8#64)) fun (y8, ()) =>
    .let_ (op1 (.not .bool) (.var c1)) fun (nc1, ()) =>
    .let_ (op2 (.sub i64) (.var a) (.imm 4#64)) fun (a4, ()) =>
    .let_ (op3 (.select i64) (.var nc1) (.var y8) (.var a4)) fun (r, ()) =>
    .jnz (.var nc1) (.ret (.var r, ())) (.ret (.var b, ()))⟩

/-- Interfering `c || (!c && b)` across flag-clobbering `.and .bool` falls back safely. -/
meta def boolNotInterfFallbackFn : Fn :=
  ⟨"boolNotInterfFallbackX64", [i64, i64, .bool], [.bool], fun _ _ (x, y, b, ()) =>
    .let_ (op2 (.cmp .eq i64) (.var x) (.var y)) fun (c, ()) =>
    .let_ (op1 (.not .bool) (.var c)) fun (nc, ()) =>
    .let_ (op2 (.and .bool) (.var b) (.var nc)) fun (z, ()) =>
    .let_ (op2 (.or .bool) (.var c) (.var z)) fun (w, ()) =>
    .ret (.var w, ())⟩

#guard chk [boolNotJnzFn]
#guard countDirs isSetccDir (codeOf [boolNotJnzFn]) == 0
#guard countDirs isMovzxOrSxDir (codeOf [boolNotJnzFn]) == 0
#guard countDirs isXorDir (codeOf [boolNotJnzFn]) == 0
#guard match (hintsOf [boolNotJnzFn]).head?.bind (·.dest.find? 5) with
  | some (.flag .ae) => true
  | _ => false

#guard chk [boolNotSelectFn]
#guard countDirs isSetccDir (codeOf [boolNotSelectFn]) == 0
#guard countDirs isMovzxOrSxDir (codeOf [boolNotSelectFn]) == 0
#guard countDirs isXorDir (codeOf [boolNotSelectFn]) == 0

#guard chk [boolDoubleNotFn]
#guard countDirs isSetccDir (codeOf [boolDoubleNotFn]) == 0
#guard countDirs isMovzxOrSxDir (codeOf [boolDoubleNotFn]) == 0
#guard countDirs isXorDir (codeOf [boolDoubleNotFn]) == 0

#guard chk [boolNotAcrossLeaFn]
#guard countDirs isSetccDir (codeOf [boolNotAcrossLeaFn]) == 0
#guard countDirs isMovzxOrSxDir (codeOf [boolNotAcrossLeaFn]) == 0
#guard countDirs isXorDir (codeOf [boolNotAcrossLeaFn]) == 0

#guard chk [boolNotInterfFallbackFn]

end LeanQbeTest.T.FlagRaOptTest
