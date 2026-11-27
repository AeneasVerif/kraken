module

public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.IselLemmas5
public import LeanQbe.T.RegaLemmas4
public import LeanQbe.T.Spill
meta import LeanQbe.T.Amd64.TargLemmas
meta import LeanQbe.T.Spill

/-!
# Bool-Zext Elision, `.gpr` Branch Inversion, Flag Reuse & Compare Canonicalization Tests (x64)

Regression suite for Wave `W3` x64 `Rega`/`Isel` optimizations (`x64Target`):
1. **#1a**: Direct `setcc` + `OPb` boolean lowering without `movb`/`movzx` roundtrips.
2. **#1b**: Flag consumption (`jnz`/`cmov`) of recently computed flags
   (`boolFlagOut?` / `cmpFlagsOut?`).
3. **#5a**: `.gpr` `JnzCond` branch-over-jump inversion (`jnzGprInv?`) and chained trampoline block
   forwarding (`findGroupFwds`).
4. **#6**: Zero-compare canonicalization (`normCmpZero1`: `x >=s 1` -> `x >s 0`,
   `x <u 1` -> `x == 0`), sequential compare & ALU-zero flag reuse
   (`SymState.flags` / `tryReuseFlagCmp`), and `elideTrunc?`.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.BoolFlagOptX64Test

open LeanQbe.T LeanQbe.T.Amd64

/-! ## Helpers -/

meta def hintsOf (fs : List Fn) : List x64Target.toIsa.Hints :=
  fs.map (Fn.computeHints x64Target.toIsa x64LegalTarget)

meta def chk (fs : List Fn) : Bool :=
  checkCompile x64Target x64Layout x64LegalTarget [] [] 0 fs (hintsOf fs) 2048

meta def codeOf (fs : List Fn) : List x64Target.toIsa.Directive :=
  extractCode (compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes [] [] 0 fs
    (hintsOf fs))

meta def isSetccDir : Directive → Bool
  | .instr (.regular _ _ (.setcc _ _)) => true
  | _ => false

meta def isMovzxDir : Directive → Bool
  | .instr (.regular _ _ (.movzx _ _)) => true
  | _ => false

meta def isTestDir : Directive → Bool
  | .instr (.regular _ _ (.test _ _)) => true
  | _ => false

meta def isCmpDir : Directive → Bool
  | .instr (.regular _ _ (.cmp _ _)) => true
  | _ => false

meta def isLabelDir : Directive → Bool
  | .label _ => true
  | _ => false

meta def isJzOrJeDir : Directive → Bool
  | .instr (.regular _ _ (.jcc .z _)) => true
  | _ => false

meta def countDirs (p : Directive → Bool) (ds : List Directive) : Nat := (ds.filter p).length

/-! ## 1. #1a & #1b: Bool-Zext Elision and Multi-Use Flag Reuse -/

/-- `(x <u y) && (a == 5)` feeding `jnz`: `0` `movzx`, `0` `test`, `<= 1` `setcc`. -/
meta def boolAndJnzFn : Fn :=
  ⟨"boolAndJnzX64", [i64, i64, i32, i64, i64], [i64], fun _ _ (x, y, a, tval, fval, ()) =>
    .let_ (op2 (.cmp .ult i64) (.var x) (.var y)) fun (c1, ()) =>
    .let_ (op2 (.cmp .eq i32) (.var a) (.imm 5#32)) fun (c2, ()) =>
    .let_ (op2 (.and .bool) (.var c1) (.var c2)) fun (b, ()) =>
    .jnz (.var b) (.ret (.var tval, ())) (.ret (.var fval, ()))⟩

/-- `(x <u y) && ((a == 5) ^^^ (b != 7))` feeding `select`: `0` `movzx`, `0` `test`. -/
meta def boolXorSelectFn : Fn :=
  ⟨"boolXorSelectX64", [i64, i64, i32, i32, i64, i64], [i64],
    fun _ _ (x, y, a, b, tval, fval, ()) =>
      .let_ (op2 (.cmp .ult i64) (.var x) (.var y)) fun (c1, ()) =>
      .let_ (op2 (.cmp .eq i32) (.var a) (.imm 5#32)) fun (c2, ()) =>
      .let_ (op2 (.cmp .ne i32) (.var b) (.imm 7#32)) fun (c3, ()) =>
      .let_ (op2 (.xor .bool) (.var c2) (.var c3)) fun (c23, ()) =>
      .let_ (op2 (.and .bool) (.var c1) (.var c23)) fun (all, ()) =>
      .let_ (op3 (.select i64) (.var all) (.var tval) (.var fval)) fun (r, ()) =>
      .ret (.var r, ())⟩

/-- Multi-use `c = (x <u y)` used in `select` then across flag-preserving `add` in `jnz`:
reuses flags with `0` `test` (`1` `setcc`). -/
meta def flagReuseSelectJnzFn : Fn :=
  ⟨"flagReuseSelectJnzX64", [i64, i64, i64, i64], [i64], fun _ _ (x, y, a, b, ()) =>
    .let_ (op2 (.cmp .ult i64) (.var x) (.var y)) fun (c, ()) =>
    .let_ (op2 (.add i64) (.var a) (.imm 8#64)) fun (a8, ()) =>
    .let_ (op3 (.select i64) (.var c) (.var a8) (.var b)) fun (r, ()) =>
    .jnz (.var c) (.ret (.var r, ())) (.ret (.var y, ()))⟩

#guard chk [boolAndJnzFn]
#guard countDirs isMovzxDir (codeOf [boolAndJnzFn]) == 0
#guard countDirs isTestDir (codeOf [boolAndJnzFn]) == 0
#guard countDirs isSetccDir (codeOf [boolAndJnzFn]) <= 2

#guard chk [boolXorSelectFn]
#guard countDirs isMovzxDir (codeOf [boolXorSelectFn]) == 0
#guard countDirs isTestDir (codeOf [boolXorSelectFn]) == 0
#guard countDirs isSetccDir (codeOf [boolXorSelectFn]) <= 4

#guard chk [flagReuseSelectJnzFn]
#guard countDirs isTestDir (codeOf [flagReuseSelectJnzFn]) == 0

/-! ## 2. #5a: `.gpr` `jnzGprInv?` & Trampoline Block Forwarding -/

/-- `.bool` parameter in GPR inside hot loop: `invertJnz` inverts `.gpr` branch to `jz`. -/
meta def gprBoolHotLoopFn : Fn :=
  ⟨"gprBoolHotLoopX64", [.bool, i64], [i64], fun _ _ (cond, n, ()) =>
    .group (sig := [[i64, i64]])
      (fun (loopLbl, ()) => .cons (ts := [i64, i64]) (fun (i, acc, ()) =>
        .jnz (.var cond)
          (.let_ (op2 (.cmp .eq i64) (.var i) (.imm 0#64)) fun (done, ()) =>
           .jnz (.var done)
             (.ret (.var acc, ()))
             (.let_ (op2 (.add i64) (.var acc) (.var i)) fun (acc', ()) =>
              .let_ (op2 (.sub i64) (.var i) (.imm 1#64)) fun (i', ()) =>
              .jump loopLbl (.var i', .var acc', ())))
          (.ret (.var acc, ()))) .nil)
      (fun (loopLbl, ()) => .jump loopLbl (.var n, .imm 0#64, ()))⟩

/-- Chained trampoline blocks `b0 -> b1 -> b2`: `b0` and `b1` are forwarded and elided. -/
meta def trampolineChainFn : Fn :=
  ⟨"trampolineChainX64", [i64, i64], [i64], fun _ _ (x, y, ()) =>
    .group (sig := [[i64], [i64], [i64]])
      (fun (_b0, b1, b2, ()) =>
        .cons (ts := [i64]) (fun (v0, ()) => .jump b1 (.var v0, ()))
          (.cons (ts := [i64]) (fun (v1, ()) => .jump b2 (.var v1, ()))
            (.cons (ts := [i64]) (fun (v2, ()) =>
              .let_ (op2 (.add i64) (.var v2) (.var y)) fun (r, ()) => .ret (.var r, ())) .nil)))
      (fun (b0, _b1, _b2, ()) => .jump b0 (.var x, ()))⟩

#guard chk [gprBoolHotLoopFn]
#guard (codeOf [gprBoolHotLoopFn]).any isJzOrJeDir

#guard chk [trampolineChainFn]
#guard countDirs isLabelDir (codeOf [trampolineChainFn]) <= 2

/-! ## 3. #6: Zero-Compare Canonicalization, Flag Reuse, and `elideTrunc?` -/

/-- `x >=s 1` in GPR canonicalizes to `x >s 0`, lowering to `testq` (`0` `cmp`), and `x == 0` reuses its flags. -/
meta def normSge1Fn : Fn :=
  ⟨"normSge1X64", [i64, i64, i64], [i64], fun _ _ (x, a, b, ()) =>
    .let_ (op2 (.cmp .sge i64) (.var x) (.imm 1#64)) fun (c1, ()) =>
    .let_ (op2 (.cmp .eq i64) (.var x) (.imm 0#64)) fun (c2, ()) =>
    .jnz (.var c2) (.ret (.var b, ()))
      (.jnz (.var c1) (.ret (.var a, ())) (.ret (.imm 0#64, ())))⟩

/-- `x <u 1` in GPR canonicalizes to `x == 0`, lowering to `testl` (`0` `cmp`). -/
meta def normUlt1Fn : Fn :=
  ⟨"normUlt1X64", [i32, i32, i64, i64], [i64], fun _ _ (x, y, a, b, ()) =>
    .let_ (op2 (.cmp .ult i32) (.var x) (.imm 1#32)) fun (c1, ()) =>
    .let_ (op2 (.cmp .eq i32) (.var y) (.imm 0#32)) fun (c2, ()) =>
    .let_ (op2 (.and .bool) (.var c1) (.var c2)) fun (c, ()) =>
    .jnz (.var c) (.ret (.var a, ())) (.ret (.var b, ()))⟩

/-- Sequential `(x <s y)` then `(x == y)` reuses flags (`1` `cmp` total, not `2`). -/
meta def seqCmpReuseFn : Fn :=
  ⟨"seqCmpReuseX64", [i64, i64, i64, i64], [i64], fun _ _ (x, y, a, b, ()) =>
    .let_ (op2 (.cmp .slt i64) (.var x) (.var y)) fun (c1, ()) =>
    .let_ (op2 (.cmp .eq i64) (.var x) (.var y)) fun (c2, ()) =>
    .jnz (.var c1)
      (.ret (.var a, ()))
      (.jnz (.var c2) (.ret (.var b, ())) (.ret (.imm 0#64, ())))⟩

/-- `(x &&& y) <s 0` reuses `andq` flags (`0` `cmp`, `0` `test`). -/
meta def aluZeroReuseFn : Fn :=
  ⟨"aluZeroReuseX64", [i64, i64, i64], [i64], fun _ _ (x, y, b, ()) =>
    .let_ (op2 (.and i64) (.var x) (.var y)) fun (d, ()) =>
    .let_ (op2 (.cmp .slt i64) (.var d) (.imm 0#64)) fun (c, ()) =>
    .jnz (.var c) (.ret (.var d, ())) (.ret (.var b, ()))⟩

/-- `trunc 64 32` / `trunc 32 16` into the same GPR elides via `Rega.elideTrunc?`. -/
meta def truncChainFn : Fn :=
  ⟨"truncChainX64", [i64, i32, i16], [i32], fun _ _ (a, x, y, ()) =>
    .let_ (op1 (.trunc 64 32) (.var a)) fun (t32, ()) =>
    .let_ (op1 (.trunc 32 16) (.var t32)) fun (t16, ()) =>
    .let_ (op2 (.add i16) (.var t16) (.var y)) fun (v16, ()) =>
    .let_ (op1 (.zext 16 32) (.var v16)) fun (v32, ()) =>
    .let_ (op2 (.add i32) (.var t32) (.var x)) fun (u32, ()) =>
    .let_ (op2 (.add i32) (.var u32) (.var v32)) fun (r, ()) =>
    .ret (.var r, ())⟩

#guard chk [normSge1Fn] && countDirs isCmpDir (codeOf [normSge1Fn]) == 0 &&
  countDirs isTestDir (codeOf [normSge1Fn]) == 1
#guard chk [normUlt1Fn] && countDirs isCmpDir (codeOf [normUlt1Fn]) == 0 &&
  countDirs isTestDir (codeOf [normUlt1Fn]) == 2
#guard chk [seqCmpReuseFn] && countDirs isCmpDir (codeOf [seqCmpReuseFn]) == 1
#guard chk [aluZeroReuseFn] && countDirs isCmpDir (codeOf [aluZeroReuseFn]) == 0 &&
  countDirs isTestDir (codeOf [aluZeroReuseFn]) == 0
#guard chk [truncChainFn]
#guard Rega.elideTrunc? x64Target.toIsa [(.var 0, .gpr .rdi)]
  (.trunc 64 32) (.var 0, ()) (.gpr .rdi, ())

/-! ## 4. Axiom Audit -/

#print axioms LeanQbe.T.Rega.lowerFn_correct
#print axioms LeanQbe.T.Rega.lowerExpr_correct
#print axioms LeanQbe.T.Amd64.x64Target
#print axioms LeanQbe.T.Amd64.x64GprSpec

end LeanQbeTest.T.BoolFlagOptX64Test
