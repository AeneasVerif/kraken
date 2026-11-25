module

public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Arm64.IselLemmas4
public import LeanQbe.T.MainLemmas
public import LeanQbe.T.Spill
meta import LeanQbe.T.Arm64.Isel
meta import LeanQbe.T.Arm64.TargLemmas
meta import LeanQbe.T.Spill

/-!
# Wave C3 IR Speedups (`AddrRangeOpt`) End-to-End AArch64 Codegen Tests

Verifies end-to-end compilation through `armTarget` (`Rega.lowerFn` + `checkCompile`) for:
1. Loop-aware address reassociation (`base + ((inv + iv) << 2)` and
   `base + ((zext(iv) + zext(inv)) << 2)`):
   hoists invariant `base + (inv << 2)` out of the loop (pre-loop `ADD_s ... LSL #2`) and emits a
   single scaled-index `LDR w, [xB, xI, lsl #2]` (`UXTX #2`) inside the loop.
2. Signed/unsigned range-check collapse (`0x30 <=s x && x <s 0x3a`, `(0 <=s x && x <s 64)`):
   emits single comparison + conditional branch with zero `AND`/`CSET`.
3. Standard-axiom audit (`#print axioms`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.AddrRangeOptArm64Test

open LeanQbe.T LeanQbe.T.Arm64

/-! ## Helpers -/

meta def hintsOf (fs : List Fn) : List armTarget.toIsa.Hints :=
  fs.map (Fn.computeHints armTarget.toIsa armLegalTarget)

meta def chk (fs : List Fn) : Bool :=
  checkCompile armTarget armLayout armLegalTarget [] [] 0 fs (hintsOf fs) 2048

meta def codeOf (fs : List Fn) : List Directive :=
  extractCode (compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes [] [] 0 fs
    (hintsOf fs))

meta def isIdxScale2Ldr : Directive → Bool
  | .instr { operation := .LDR _ (.addr { off := .reg { ext := e, .. }, .. }), .. } =>
    e.amount == .E2
  | _ => false

meta def isUbfmDir : Directive → Bool
  | .instr { operation := .UBFM .., .. } => true
  | _ => false

meta def isAddShift2Dir : Directive → Bool
  | .instr { operation := .ADD_s _ _ sr, .. } => sr.shift == .LSL && sr.amount == 2
  | _ => false

meta def isSubsDir : Directive → Bool
  | .instr { operation := .SUBS_e .., .. }
  | .instr { operation := .SUBS_s .., .. } => true
  | _ => false

meta def isCselDir : Directive → Bool
  | .instr { operation := .CSEL .., .. } => true
  | _ => false

meta def isAndDir : Directive → Bool
  | .instr { operation := .AND_i .., .. }
  | .instr { operation := .AND_s .., .. }
  | .instr { operation := .ANDS_i .., .. }
  | .instr { operation := .ANDS_s .., .. } => true
  | _ => false

meta def isCsincCsetDir : Directive → Bool
  | .instr { operation := .CSINC .., .. } => true
  | _ => false

meta def isBcondDir : Directive → Bool
  | .instr { operation := .B_cond .., .. } => true
  | _ => false

meta def countDirs (p : Directive → Bool) (ds : List Directive) : Nat := (ds.filter p).length

/-! ## 1. Hoisted Shifted Base + Single `[xB, xI, lsl #2]` Loop Load -/

meta def arm64LoopIdxFn : Fn :=
  ⟨"arm64LoopIdx", [i64, i64, i64], [i64], fun _ _ (base, inv, n, ()) =>
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

meta def arm64LoopZextIdxFn : Fn :=
  ⟨"arm64LoopZextIdx", [i64, i32, i32], [i64], fun _ _ (base, inv, n, ()) =>
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

meta def arm64LoopZextDispIdxFn : Fn :=
  ⟨"arm64LoopZextDispIdx", [i64, i32, i32], [i64], fun _ _ (base, inv, n, ()) =>
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

#guard chk [arm64LoopIdxFn]
#guard chk [arm64LoopZextIdxFn]
#guard chk [arm64LoopZextDispIdxFn]
#guard countDirs isIdxScale2Ldr (codeOf [arm64LoopIdxFn]) == 1
#guard countDirs isUbfmDir (codeOf [arm64LoopIdxFn]) == 0
#guard countDirs isAddShift2Dir (codeOf [arm64LoopIdxFn]) == 1
#guard countDirs isIdxScale2Ldr (codeOf [arm64LoopZextIdxFn]) == 1
#guard countDirs isUbfmDir (codeOf [arm64LoopZextIdxFn]) == 0
#guard countDirs isAddShift2Dir (codeOf [arm64LoopZextIdxFn]) == 1
#guard countDirs isUbfmDir (codeOf [arm64LoopZextDispIdxFn]) == 0
#guard countDirs isAddShift2Dir (codeOf [arm64LoopZextDispIdxFn]) >= 1

/-! ## 2. Collapsed Range Checks (Zero `AND`/`CSET`, Single Compare) -/

meta def arm64DigitBranchFn : Fn :=
  ⟨"arm64DigitBranch", [i8, i64, i64], [i64], fun _ _ (ch, a, b, ()) =>
    .let_ (op2 (.cmp .sge i8) (.var ch) (.imm 0x30#8)) fun (c1, ()) =>
    .let_ (op2 (.cmp .slt i8) (.var ch) (.imm 0x3a#8)) fun (c2, ()) =>
    .let_ (op2 (.and .bool) (.var c1) (.var c2)) fun (ok, ()) =>
    .jnz (.var ok) (.ret (.var a, ())) (.ret (.var b, ()))⟩

meta def arm64DigitStoreBranchFn : Fn :=
  ⟨"arm64DigitStoreBranch", [i8, i64, i64], [i64], fun _ _ (ch, p, a, ()) =>
    .let_ (op2 (.cmp .sge i8) (.var ch) (.imm 0x30#8)) fun (c1, ()) =>
    .let_ (op2 (.cmp .slt i8) (.var ch) (.imm 0x3a#8)) fun (c2, ()) =>
    .let_ (op2 (.and .bool) (.var c1) (.var c2)) fun (ok, ()) =>
    .jnz (.var ok) (.store (.var a) (.var p) (.ret (.imm 1, ()))) (.ret (.imm 0, ()))⟩

meta def arm64ZeroLoBranchFn : Fn :=
  ⟨"arm64ZeroLoBranch", [i32, i64, i64], [i64], fun _ _ (x, a, b, ()) =>
    .let_ (op2 (.cmp .sge i32) (.var x) (.imm 0#32)) fun (c1, ()) =>
    .let_ (op2 (.cmp .slt i32) (.var x) (.imm 64#32)) fun (c2, ()) =>
    .let_ (op2 (.and .bool) (.var c1) (.var c2)) fun (ok, ()) =>
    .jnz (.var ok) (.ret (.var a, ())) (.ret (.var b, ()))⟩

meta def arm64ZextSignedRangeBranchFn : Fn :=
  ⟨"arm64ZextSignedRangeBranch", [i32, i64, i64], [i64], fun _ _ (x, a, b, ()) =>
    .let_ (op1 (.zext 32 64) (.var x)) fun (z1, ()) =>
    .let_ (op2 (.cmp .sge i64) (.var z1) (.imm 0#64)) fun (c1, ()) =>
    .let_ (op1 (.zext 32 64) (.var x)) fun (z2, ()) =>
    .let_ (op2 (.cmp .slt i64) (.var z2) (.imm 64#64)) fun (c2, ()) =>
    .let_ (op2 (.and .bool) (.var c1) (.var c2)) fun (ok, ()) =>
    .jnz (.var ok) (.ret (.var a, ())) (.ret (.var b, ()))⟩

#guard chk [arm64DigitBranchFn]
#guard chk [arm64DigitStoreBranchFn]
#guard chk [arm64ZeroLoBranchFn]
#guard chk [arm64ZextSignedRangeBranchFn]
#guard countDirs isAndDir (codeOf [arm64DigitBranchFn]) == 0
#guard countDirs isCsincCsetDir (codeOf [arm64DigitBranchFn]) == 0
#guard countDirs isSubsDir (codeOf [arm64DigitBranchFn]) == 1
#guard countDirs isCselDir (codeOf [arm64DigitBranchFn]) == 1
#guard countDirs isAndDir (codeOf [arm64DigitStoreBranchFn]) == 0
#guard countDirs isCsincCsetDir (codeOf [arm64DigitStoreBranchFn]) == 0
#guard countDirs isBcondDir (codeOf [arm64DigitStoreBranchFn]) == 1
#guard countDirs isAndDir (codeOf [arm64ZeroLoBranchFn]) == 0
#guard countDirs isCsincCsetDir (codeOf [arm64ZeroLoBranchFn]) == 0
#guard countDirs isSubsDir (codeOf [arm64ZeroLoBranchFn]) == 1
#guard countDirs isAndDir (codeOf [arm64ZextSignedRangeBranchFn]) == 0
#guard countDirs isCsincCsetDir (codeOf [arm64ZextSignedRangeBranchFn]) == 0
#guard countDirs isSubsDir (codeOf [arm64ZextSignedRangeBranchFn]) == 1

/-! ## 3. Axiom Audit -/

#print axioms LeanQbe.T.Arm64.armGprSpec
#print axioms LeanQbe.T.Arm64.armLabelClean
#print axioms LeanQbe.T.compile_sound

end LeanQbeTest.T.AddrRangeOptArm64Test
