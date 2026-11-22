module

public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Bignum
public import LeanQbe.T.Spill
meta import LeanQbe.T.Arm64.TargLemmas
meta import LeanQbe.T.Examples.Bignum
meta import LeanQbe.T.Spill
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

/-! ## Helpers -/

/-- Hints from the production heuristics (`Fn.computeHints` = `Spill.hints ∘ Fn.mid`). -/
meta def hintsOf (fs : List Fn) : List armTarget.toIsa.Hints :=
  fs.map (Fn.computeHints armTarget.toIsa armLegalTarget)

/-- End-to-end verified compilation check (lowering, labels, stack bounds). -/
meta def chk (fs : List Fn) : Bool :=
  checkCompile armTarget armLayout armLegalTarget [] [] 0 fs (hintsOf fs) 2048

/-- Emitted code of a module (empty on a compile error). -/
meta def codeOf (fs : List Fn) : List armTarget.toIsa.Directive :=
  extractCode (compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes [] [] 0 fs
    (hintsOf fs))

/-- `cset` is `CSINC xd, xzr, xzr, ¬c`. -/
meta def isCsetDir (d : armTarget.toIsa.Directive) : Bool :=
  (Kraken.AArch64.Print.directive d).startsWith "csinc"

meta def countDirs (p : armTarget.toIsa.Directive → Bool) (ds : List armTarget.toIsa.Directive) :
    Nat :=
  (ds.filter p).length

/-! ## 1. Flag fusion: `240` `cmp` cases, zero `cset` -/

meta def cmpOps : List CmpOp := [.eq, .ne, .ult, .ule, .ugt, .uge, .slt, .sle, .sgt, .sge]

/-- `cmp co` at width `w`, operand form `form` (`0` reg-reg, `1` reg-imm, `2` imm-reg), feeding
a `jnz` (`jnz? = true`) or a `select`. -/
meta def cmpFn (co : CmpOp) (w form : Nat) (jnz? : Bool) : Fn :=
  ⟨"cmpCase", [.bits w, .bits w, i64, i64], [i64], fun V _ (x, y, a, b, ()) =>
    let l : Arg V (.bits w) := if form == 2 then .imm 5 else .var x
    let r : Arg V (.bits w) := if form == 1 then .imm 5 else .var y
    .let_ (op2 (.cmp co (.bits w)) l r) fun (c, ()) =>
    if jnz? then .jnz (.var c) (.ret (.var a, ())) (.ret (.var b, ()))
    else .let_ (op3 (.select i64) (.var c) (.var a) (.var b)) fun (s, ()) => .ret (.var s, ())⟩

meta def cmpCases : List Fn :=
  cmpOps.flatMap fun co => [8, 16, 32, 64].flatMap fun w =>
    [0, 1, 2].flatMap fun form => [false, true].map (cmpFn co w form)

#guard cmpCases.length == 240
#guard cmpCases.all fun f => chk [f]
#guard (cmpCases.map fun f => countDirs isCsetDir (codeOf [f])).sum == 0

/-! ## 2. `Bignum` keeps compiling without extra `cset`s -/

#guard chk Examples.Bignum.mul4x4Module.fns
#guard countDirs isCsetDir (codeOf Examples.Bignum.mul4x4Module.fns) ≤ 21
#guard chk Examples.Bignum.addMod25519Module.fns && chk Examples.Bignum.subMod25519Module.fns

/-! ## 3. `SpillFlags` fixpoint: no failed `adcx`/`adox` speculation -/

/-- `c = cmp co x y` stays live across an `addc` with a dead carry-out, then feeds a `select`. -/
meta def addcAfter (nm : Sym) (co : CmpOp) : Fn :=
  ⟨nm, [i64, i64, i64, i64], [i64, i64], fun _ _ (x, y, a, b, ()) =>
    .let_ (op2 (.cmp co i64) (.var x) (.var y)) fun (c, ()) =>
    .let_ (op3 (.addc 64) (.var a) (.var b) (.imm false)) fun (s0, _c0, ()) =>
    .let_ (op3 (.select i64) (.var c) (.var s0) (.imm 0)) fun (r, ()) =>
    .ret (.var r, .var s0, ())⟩

#guard chk [addcAfter "addcAfterUlt" .ult]
#guard chk [addcAfter "addcAfterCmp" .eq]
#guard chk [addcAfter "addcAfterSlt" .slt]

/-! ## 4. Per-call splitting: cold-branch call, spill-free fast path -/

meta def slowFn : Fn :=
  ⟨"slow", [i64], [i64], fun _ _ (x, ()) =>
    .let_ (op2 (.mul i64) (.var x) (.var x)) fun (r, ()) => .ret (.var r, ())⟩

/-- `sel x y`: the fast path returns `x + y`; the cold path calls `slow x` with `y` live across. -/
meta def selFn : Fn :=
  ⟨"sel", [i64, i64], [i64], fun _ _ (x, y, ()) =>
    .let_ (op2 (.and i64) (.var x) (.imm 1)) fun (t, ()) =>
    .let_ (op2 (.cmp .eq i64) (.var t) (.imm 0)) fun (c, ()) =>
    .jnz (.var c)
      (.let_ (op2 (.add i64) (.var x) (.var y)) fun (r, ()) => .ret (.var r, ()))
      (.call "slow" (as := [i64]) (bs := [i64]) (.var x, ()) fun (s, ()) =>
        .let_ (op2 (.add i64) (.var s) (.var y)) fun (r, ()) => .ret (.var r, ()))⟩

mutual
meta def callIps : Live.Tree → List Nat
  | .call _ ip _ _ _ _ _ k => ip :: callIps k
  | .let_ _ _ _ _ _ k | .load _ _ _ _ _ k | .store _ _ _ _ _ k | .skip _ _ k => callIps k
  | .jnz _ _ _ _ t e => callIps t ++ callIps e
  | .group _ bs k => callIpsB bs ++ callIps k
  | _ => []

meta def callIpsB : Live.TreeBlocks → List Nat
  | .nil => []
  | .cons _ _ b bs => callIps b ++ callIpsB bs
end

meta def isSlotMove : armTarget.toIsa.Move → Bool
  | .st .. | .ld .. | .vst .. | .vld .. => true
  | _ => false

/-- `PreStep` ips (below `nip`) that move a value between a register and a stack slot. -/
meta def slotMoveIps (h : armTarget.toIsa.Hints) (nip : Nat) : List Nat :=
  (List.range nip).filter fun ip => match h.pre.find? ip with
    | some ps => ps.moves.any isSlotMove
    | none => false

meta def selMid : Fn := selFn.mid armLegalTarget
meta def selHints : armTarget.toIsa.Hints := Spill.hints armTarget.toIsa selMid
meta def selTree : Live.Tree × List (Nat × Ty) × Nat × Nat × Nat × Trie Ty := Live.Tree.ofFn selMid

#guard chk [slowFn, selFn]
#guard selHints.saved.isEmpty
#guard
  let cs := callIps selTree.1
  let ips := slotMoveIps selHints selTree.2.2.2.2.1
  cs.length == 1 && ips.length == 2 && ips.all fun ip => cs.any fun c => ip == c || ip == c + 1

/-! ## 5. Stage 1a `[base + disp]` addressing on AArch64 (`armSupportsAddrDisp`) -/

meta def isArmAddSubOrPoolDir (d : armTarget.toIsa.Directive) : Bool :=
  let s := Kraken.AArch64.Print.directive d
  !(s.startsWith "add sp," || s.startsWith "sub sp,") &&
    (s.startsWith "add " || s.startsWith "sub " || s.contains '=')

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

/-! ## 6. Track C6 `[base, idx, lsl #k]` scaled-index addressing (`armSupportsAddrIdx`) -/

meta def isArmAddSubShlOrPoolDir (d : armTarget.toIsa.Directive) : Bool :=
  let s := Kraken.AArch64.Print.directive d
  !(s.startsWith "add sp," || s.startsWith "sub sp,") &&
    (s.startsWith "add " || s.startsWith "sub " || s.startsWith "lsl " || s.contains '=')

meta def isArmSibDir (d : armTarget.toIsa.Directive) : Bool :=
  let s := Kraken.AArch64.Print.directive d
  (s.startsWith "ldr" || s.startsWith "str") &&
    (s.contains ", lsl #1" || s.contains ", lsl #2" || s.contains ", lsl #3")

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

/-! ## 7. Track C1c upper-32 zeroing parity (`zext 32->64` elision vs `sext 32->64`) -/

meta def isArmOrrWOrUbfmDir (d : armTarget.toIsa.Directive) : Bool :=
  let s := Kraken.AArch64.Print.directive d
  s.startsWith "orr w" || s.startsWith "ubfm"

meta def isArmSext32Dir (d : armTarget.toIsa.Directive) : Bool :=
  let s := Kraken.AArch64.Print.directive d
  s.startsWith "sbfm x" && s.contains ", #0, #31"

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
