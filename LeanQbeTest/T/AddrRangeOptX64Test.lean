module

import LeanQbe.T.Amd64.TargLemmas
import LeanQbe.T.Amd64.IselLemmas5
import LeanQbe.T.MainLemmas
import LeanQbe.T.Spill
meta import LeanQbe.T.Amd64.TargLemmas
meta import LeanQbe.T.Spill

/-!
# Wave C3 IR Speedups (`AddrRangeOpt`) End-to-End x86-64 Codegen Tests

Verifies end-to-end compilation through `x64Target` (`Rega.lowerFn` + `checkCompile`) for:
1. Loop-aware address reassociation (`base + ((zext(iv) + inv) << 2)` and
   `base + ((iv + inv) << 2)`):
   hoists invariant `base + (inv << 2)` computation before the loop, leaving a single scaled SIB
   memory load inside the loop with zero extra `shl` or address `add` instructions.
2. Signed/unsigned range-check collapse (`0x30 <=s x && x <s 0x3a` → `(x - 0x30) <u 10`, and
   `(0 <=s x && x <s 64)` → `x <u 64`): emits single compare with zero `andb`/`setcc`.
3. Standard-axiom audit (`#print axioms`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.AddrRangeOptX64Test

open LeanQbe.T LeanQbe.T.Amd64

/-! ## Helpers -/

meta def hintsOf (fs : List Fn) : List x64Target.toIsa.Hints :=
  fs.map (Fn.computeHints x64Target.toIsa x64LegalTarget)

meta def chk (fs : List Fn) : Bool :=
  checkCompile x64Target x64Layout x64LegalTarget [] [] 0 fs (hintsOf fs) 2048

meta def codeOf (fs : List Fn) : List x64Target.toIsa.Directive :=
  extractCode (compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes [] [] 0 fs
    (hintsOf fs))

meta def isShlDir : Directive → Bool
  | .instr (.regular _ _ (.shl _ _)) => true
  | _ => false

meta def isSetccDir : Directive → Bool
  | .instr (.regular _ _ (.setcc _ _)) => true
  | _ => false

meta def isAndDir : Directive → Bool
  | .instr (.regular _ _ (.and _ _)) => true
  | _ => false

meta def isSibMem : AddrExpr → Bool
  | { base := some (.reg _), idx := some _, .. } => true
  | _ => false

meta def isSibLoadDir : Directive → Bool
  | .instr (.regular _ _ (.mov _ (.regOrMem (.mem a)))) => isSibMem a
  | .instr (.regular _ _ (.movzx _ (.mem a))) => isSibMem a
  | .instr (.regular _ _ (.movsx _ (.mem a))) => isSibMem a
  | _ => false

meta def countDirs (p : Directive → Bool) (ds : List Directive) : Nat := (ds.filter p).length

/-! ## 1. Loop-Hoisted SIB Addressing -/

/-- `base + ((inv + iv) << 2)` inside a loop lowers to hoisted base calculation + single SIB
`movl (%base, %iv, 4), %reg` with 0 `shl`. -/
meta def x64LoopSibFn : Fn :=
  ⟨"x64LoopSib", [i64, i64, i64], [i64], fun _ _ (base, inv, n, ()) =>
    loop1 (ts := [i64, i64])
      (fun lp (iv, acc, ()) =>
        .let_ (op2 (.cmp .eq i64) (.var iv) (.var n)) fun (done, ()) =>
        .jnz (.var done) (.ret (.var acc, ()))
          (.let_ (op2 (.add i64) (.var inv) (.var iv)) fun (idx, ()) =>
           .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun (off, ()) =>
           .let_ (op2 (.add i64) (.var base) (.var off)) fun (ptr, ()) =>
           .load i32 (.var ptr) fun w =>
           .let_ (op1 (.zext 32 64) (.var w)) fun (w64, ()) =>
           .let_ (op2 (.add i64) (.var acc) (.var w64)) fun (acc', ()) =>
           .let_ (op2 (.add i64) (.var iv) (.imm 1)) fun (iv', ()) =>
           .jump lp (.var iv', .var acc', ())))
      (fun lp => .jump lp (.imm 0, .imm 0, ()))⟩

/-- `base + ((zext(iv) + zext(inv)) << 2)` matching `full_has_ternary` / `full_sweep_copy`. -/
meta def x64LoopZextSibFn : Fn :=
  ⟨"x64LoopZextSib", [i64, i32, i32], [i64], fun _ _ (base, inv, n, ()) =>
    loop1 (ts := [i32, i64])
      (fun lp (iv, acc, ()) =>
        .let_ (op2 (.cmp .eq i32) (.var iv) (.var n)) fun (done, ()) =>
        .jnz (.var done) (.ret (.var acc, ()))
          (.let_ (op1 (.zext 32 64) (.var iv)) fun (iv64, ()) =>
           .let_ (op1 (.zext 32 64) (.var inv)) fun (inv64, ()) =>
           .let_ (op2 (.add i64) (.var iv64) (.var inv64)) fun (idx, ()) =>
           .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun (off, ()) =>
           .let_ (op2 (.add i64) (.var base) (.var off)) fun (ptr, ()) =>
           .load i32 (.var ptr) fun w =>
           .let_ (op1 (.zext 32 64) (.var w)) fun (w64, ()) =>
           .let_ (op2 (.add i64) (.var acc) (.var w64)) fun (acc', ()) =>
           .let_ (op2 (.add i32) (.var iv) (.imm 1)) fun (iv', ()) =>
           .jump lp (.var iv', .var acc', ())))
      (fun lp => .jump lp (.imm 0, .imm 0, ()))⟩

/-- `base + (((zext(iv) + 3) + zext(inv)) << 2)` distributes `+ 12` into SIB displacement while
hoisting `base + (zext(inv) << 2)`, leaving 1 SIB load and 0 `shl`. -/
meta def x64LoopZextDispSibFn : Fn :=
  ⟨"x64LoopZextDispSib", [i64, i32, i32], [i64], fun _ _ (base, inv, n, ()) =>
    loop1 (ts := [i32, i64])
      (fun lp (iv, acc, ()) =>
        .let_ (op2 (.cmp .eq i32) (.var iv) (.var n)) fun (done, ()) =>
        .jnz (.var done) (.ret (.var acc, ()))
          (.let_ (op1 (.zext 32 64) (.var iv)) fun (iv64, ()) =>
           .let_ (op2 (.add i64) (.var iv64) (.imm 3)) fun (ivDisp, ()) =>
           .let_ (op1 (.zext 32 64) (.var inv)) fun (inv64, ()) =>
           .let_ (op2 (.add i64) (.var ivDisp) (.var inv64)) fun (idx, ()) =>
           .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun (off, ()) =>
           .let_ (op2 (.add i64) (.var base) (.var off)) fun (ptr, ()) =>
           .load i32 (.var ptr) fun w =>
           .let_ (op1 (.zext 32 64) (.var w)) fun (w64, ()) =>
           .let_ (op2 (.add i64) (.var acc) (.var w64)) fun (acc', ()) =>
           .let_ (op2 (.add i32) (.var iv) (.imm 1)) fun (iv', ()) =>
           .jump lp (.var iv', .var acc', ())))
      (fun lp => .jump lp (.imm 0, .imm 0, ()))⟩

#guard chk [x64LoopSibFn]
#guard chk [x64LoopZextSibFn]
#guard chk [x64LoopZextDispSibFn]
#guard countDirs isSibLoadDir (codeOf [x64LoopSibFn]) == 1
#guard countDirs isShlDir (codeOf [x64LoopSibFn]) == 0
#guard countDirs isSibLoadDir (codeOf [x64LoopZextSibFn]) == 1
#guard countDirs isShlDir (codeOf [x64LoopZextSibFn]) == 0
-- `Func.peel` peels iteration 0 before the loop, producing 2 SIB loads and 0 `shl`.
#guard countDirs isSibLoadDir (codeOf [x64LoopZextDispSibFn]) == 2
#guard countDirs isShlDir (codeOf [x64LoopZextDispSibFn]) == 0

/-! ## 2. Collapsed Range Checks (`jnz` Flag-Kept, Zero `setcc`/`andb`) -/

meta def x64DigitBranchFn : Fn :=
  ⟨"x64DigitBranch", [i8, i64, i64], [i64], fun _ _ (ch, a, b, ()) =>
    .let_ (op2 (.cmp .sge i8) (.var ch) (.imm 0x30#8)) fun (c1, ()) =>
    .let_ (op2 (.cmp .slt i8) (.var ch) (.imm 0x3a#8)) fun (c2, ()) =>
    .let_ (op2 (.and .bool) (.var c1) (.var c2)) fun (ok, ()) =>
    .jnz (.var ok) (.ret (.var a, ())) (.ret (.var b, ()))⟩

meta def x64ZeroLoBranchFn : Fn :=
  ⟨"x64ZeroLoBranch", [i32, i64, i64], [i64], fun _ _ (x, a, b, ()) =>
    .let_ (op2 (.cmp .sge i32) (.var x) (.imm 0#32)) fun (c1, ()) =>
    .let_ (op2 (.cmp .slt i32) (.var x) (.imm 64#32)) fun (c2, ()) =>
    .let_ (op2 (.and .bool) (.var c1) (.var c2)) fun (ok, ()) =>
    .jnz (.var ok) (.ret (.var a, ())) (.ret (.var b, ()))⟩

meta def x64ZextSignedRangeBranchFn : Fn :=
  ⟨"x64ZextSignedRangeBranch", [i32, i64, i64], [i64], fun _ _ (x, a, b, ()) =>
    .let_ (op1 (.zext 32 64) (.var x)) fun (z1, ()) =>
    .let_ (op2 (.cmp .sge i64) (.var z1) (.imm 0#64)) fun (c1, ()) =>
    .let_ (op1 (.zext 32 64) (.var x)) fun (z2, ()) =>
    .let_ (op2 (.cmp .slt i64) (.var z2) (.imm 64#64)) fun (c2, ()) =>
    .let_ (op2 (.and .bool) (.var c1) (.var c2)) fun (ok, ()) =>
    .jnz (.var ok) (.ret (.var a, ())) (.ret (.var b, ()))⟩

#guard chk [x64DigitBranchFn]
#guard chk [x64ZeroLoBranchFn]
#guard chk [x64ZextSignedRangeBranchFn]
#guard countDirs isSetccDir (codeOf [x64DigitBranchFn]) == 0
#guard countDirs isAndDir (codeOf [x64DigitBranchFn]) == 0
#guard countDirs isSetccDir (codeOf [x64ZeroLoBranchFn]) == 0
#guard countDirs isAndDir (codeOf [x64ZeroLoBranchFn]) == 0
#guard countDirs isSetccDir (codeOf [x64ZextSignedRangeBranchFn]) == 0
#guard countDirs isAndDir (codeOf [x64ZextSignedRangeBranchFn]) == 0

/-! ## 3. Axiom Audit -/

#print axioms LeanQbe.T.Amd64.x64GprSpec
#print axioms LeanQbe.T.Amd64.x64LabelClean
#print axioms LeanQbe.T.compile_sound

end LeanQbeTest.T.AddrRangeOptX64Test
