module

import LeanQbe.T.Arm64.TargLemmas
import LeanQbe.T.MainLemmas
import LeanQbe.T.Driver
import LeanQbe.T.MainInline
import LeanQbe.T.Examples.Kissat.Plain
import LeanQbeTest.T.Arm64DirPreds
import LeanQbeTest.T.RegaTestKit
meta import LeanQbe.T.Arm64.TargLemmas
meta import LeanQbe.T.MainLemmas
meta import LeanQbe.T.Driver
meta import LeanQbe.T.MainInline
meta import LeanQbe.T.Examples.Kissat.Plain
meta import LeanQbeTest.T.Arm64DirPreds
meta import LeanQbeTest.T.RegaTestKit
meta import Kraken.AArch64.Print

/-!
# Arm64 Wave 6.2-A (`OPT-7` + `OPT-10`) Activation Tests

End-to-end `Live` -> `Spill` -> `Rega` -> `Arm64.Isel` activation `#guard`s for the verified
Arm64 Wave 6.2-A bundle (`OPT-7` zero/scratch-const/immediate optimizations and `OPT-10`
zero-extension/narrowing/dead-low-multiply cleanups), checked against the same compiler with the
Wave 6.2-A `GprIsa` hooks switched off (`armIsaNoOpt710`):

* **`OPT-7a`**: `#0` store/op lowering uses `WZR`/`XZR` (`0` redundant `MOVZ #0`).
* **`OPT-7b`**: intra-block scratch-constant reuse (`x16`/`x17`) avoids duplicate literal
  reloads, and natural-loop large constant hoisting moves invariant immediates out of loops.
* **`OPT-7c`**: `preferRegImm?` / `preferStoreRegImm` reuse live GPRs instead of scratch reloads.
* **`OPT-10a`**: `zeroExtOp` / `zeroExtBoolCmp` / `zeroExtSetcc` plus cross-block `.gprZ` entry
  propagation elide redundant `UBFM #0, #7`/`#15`/`#31` and `ORR w, wzr, w`.
* **`OPT-10b`**: `load i64` -> `trunc 64 32` narrows to single `LDR w` without narrow copy/mask.
* **`OPT-10c`**: dead-low `umulw`/`smulw` emits single `UMULH`/`SMULH`.
* Real `Kissat.Plain` hot functions emit strictly fewer instructions with Wave 6.2-A on.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.Arm64W62Opt710Test

open LeanQbe.T LeanQbe.T.Arm64
open LeanQbeTest.T.RegaTestKit LeanQbeTest.T.Arm64DirPreds

/-! ## 1. Compilation & Inspection Helpers -/

/-- `armTarget.toIsa` with every Wave 6.2-A `OPT-7` / `OPT-10` hook switched off. -/
meta def armIsaNoOpt710 : Isa :=
  { armTarget.toIsa with
    gpr :=
      { armGpr with
        zeroExtOp := fun _ _ _ => false
        zeroExtBoolCmp := false
        zeroExtSetcc := false
        preferRegImm? := none
        preferStoreRegImm := fun _ _ => false
        mulHi? := none
        storeScr? := none
        storeZextIdxScr? := none
        loadScr? := none
        loadZextIdxScr? := none
        opScr? := none } }

meta def armChk (fs : List Fn) : Bool :=
  chk armTarget armLayout armLegalTarget fs

meta def armCode (fs : List Fn) : List armTarget.toIsa.Directive :=
  codeOf armTarget armLegalTarget fs

meta def armCodeOff (fs : List Fn) : List Directive :=
  extractCode (compileModule armIsaNoOpt710 armLegalTarget 0 [] [] 0 fs
    (fs.map (Fn.computeHints armIsaNoOpt710 armLegalTarget)))

meta def isInstrDir : Directive → Bool
  | .instr _ => true
  | _ => false

meta def insnCount (ds : List Directive) : Nat :=
  countDirs isInstrDir ds

meta def isMovzOrMovkDir (d : Directive) : Bool :=
  isMovzDir d || isMovkDir d

meta def isStrZrDir : Directive → Bool
  | .instr { operation := .STR (.low .XZR _) _, .. } => true
  | _ => false

meta def isLdrWDir : Directive → Bool
  | .instr { operation := .LDR (.low (.reg _) .W32) _, .. } => true
  | _ => false

meta def isMulDir : Directive → Bool
  | .instr { operation := .MADD _ _ _ (.low .XZR _), .. } => true
  | _ => false

meta def isUmulhDir : Directive → Bool
  | .instr { operation := .UMULH .., .. } => true
  | _ => false

meta def isSmulhDir : Directive → Bool
  | .instr { operation := .SMULH .., .. } => true
  | _ => false

/-! ## 2. `OPT-7a`: Zero-Register (`WZR`/`XZR`) Substitution -/

/-- Store `#0` at 64-bit and 32-bit widths and subtract `#0` (expected zero `MOVZ #0`). -/
def zeroStoreAndSubFn : Fn :=
  ⟨"zero_store_sub", [i64, i64, i64], [i64], fun _ _ (p, q, x, ()) =>
    .store (t := i64) (.imm (0 : BitVec 64)) (.var p)
      (.store (t := i32) (.imm (0 : BitVec 32)) (.var q)
        (.let_ (op2 (.sub i64) (.var x) (.imm 0)) fun (r, ()) =>
          .ret (.var r, ())))⟩

#guard armChk [zeroStoreAndSubFn]
#guard countDirs isMovz0Dir (armCode [zeroStoreAndSubFn]) == 0
#guard countDirs isStrZrDir (armCode [zeroStoreAndSubFn]) >= 2

/-! ## 3. `OPT-7b`: Intra-Block Scratch-Const Reuse & Natural-Loop Hoisting -/

/-- Repeated 64-bit constant `0x123456789abcdef0` in stores reuses `.X17`. -/
def scrReuseStoreFn : Fn :=
  let big : BitVec 64 := 0x123456789abcdef0#64
  ⟨"scr_reuse_store", [i64, i64, i64], [i64], fun _ _ (p, q, r, ()) =>
    .store (t := i64) (.imm big) (.var p)
      (.store (t := i64) (.imm big) (.var q)
        (.store (t := i64) (.imm big) (.var r)
          (.ret (.imm (0 : BitVec 64), ()))))⟩

#guard armChk [scrReuseStoreFn]
#guard insnCount (armCode [scrReuseStoreFn]) < insnCount (armCodeOff [scrReuseStoreFn])
#guard countDirs isLdrPoolDir (armCode [scrReuseStoreFn]) == 1 &&
  countDirs isLdrPoolDir (armCodeOff [scrReuseStoreFn]) == 3

/-- Repeated 64-bit constant in straight-line `xor` ops reuses `.X17` across instructions. -/
def scrReuseAluFn : Fn :=
  let big : BitVec 64 := 0x123456789abcdef0#64
  ⟨"scr_reuse_alu", [i64, i64], [i64], fun _ _ (x, y, ()) =>
    .let_ (op2 (.xor i64) (.var x) (.imm big)) fun (a, ()) =>
    .let_ (op2 (.xor i64) (.var y) (.imm big)) fun (b, ()) =>
    .let_ (op2 (.add i64) (.var a) (.var b)) fun (s, ()) =>
    .ret (.var s, ())⟩

#guard armChk [scrReuseAluFn]
#guard insnCount (armCode [scrReuseAluFn]) < insnCount (armCodeOff [scrReuseAluFn])

/-- Natural loop using a 4-chunk 64-bit constant on every iteration triggers loop hoisting. -/
def loopConstHoistFn : Fn :=
  let big : BitVec 64 := 0x123456789abcdef0#64
  ⟨"loop_const_hoist", [i64, i64], [i64], fun _ _ (n0, acc0, ()) =>
    loop1 (ts := [i64, i64])
      (fun lp (n, acc, ()) =>
        .let_ (op2 (.cmp .ugt i64) (.var n) (.imm 0)) fun (c, ()) =>
        .jnz (.var c)
          (.let_ (op2 (.xor i64) (.var acc) (.imm big)) fun (a1, ()) =>
           .let_ (op2 (.add i64) (.var a1) (.imm big)) fun (a2, ()) =>
           .let_ (op2 (.sub i64) (.var n) (.imm 1)) fun (n1, ()) =>
           .jump lp (.var n1, .var a2, ()))
          (.ret (.var acc, ())))
      (fun lp => .jump lp (.var n0, .var acc0, ()))⟩

#guard armChk [loopConstHoistFn]
#guard insnCount (armCode [loopConstHoistFn]) < insnCount (armCodeOff [loopConstHoistFn])

/-! ## 4. `OPT-7c`: Live-GPR Immediate Preference (`preferRegImm?`, `preferStoreRegImm`) -/

/-- When non-encodable constant `big` is already materialized into a GPR, subsequent ops and stores
prefer the live GPR rather than reloading `big` into `x16`/`x17`. -/
def preferRegImmFn : Fn :=
  let big : BitVec 64 := 0x123456789abcdef0#64
  ⟨"prefer_reg_imm", [i64, i64], [i64, i64], fun _ _ (x, p, ()) =>
    .let_ (op1 (.copy i64) (.imm big)) fun (k, ()) =>
    .let_ (op2 (.xor i64) (.var x) (.imm big)) fun (a, ()) =>
    .store (t := i64) (.imm big) (.var p)
      (.let_ (op2 (.add i64) (.var a) (.var k)) fun (s, ()) =>
        .ret (.var s, .var k, ()))⟩

#guard armChk [preferRegImmFn]
#guard countDirs isLdrPoolDir (armCode [preferRegImmFn]) == 2
#guard countDirs isLdrPoolDir (armCode [preferRegImmFn]) <
  countDirs isLdrPoolDir (armCodeOff [preferRegImmFn])
#guard insnCount (armCode [preferRegImmFn]) < insnCount (armCodeOff [preferRegImmFn])

/-! ## 5. `OPT-10a`: Canonical Zero-Extension Elision & Cross-Block `.gprZ` -/

/-- `setcc`/`ofBool` + narrow `ldrb` feeding `zext 8 -> 64` elide extra `UBFM #0, #7` and
`ORR w, wzr, w` zero-extensions. -/
def zextElideInBlockFn : Fn :=
  ⟨"zext_elide_in_blk", [i64, (.bits 8), (.bits 8)], [i64], fun _ _ (p, a, b, ()) =>
    .load (.bits 8) (.var p) fun v =>
    .let_ (op2 (.cmp .ult (.bits 8)) (.var a) (.var b)) fun (c, ()) =>
    .let_ (op1 (.ofBool 8) (.var c)) fun (c8, ()) =>
    .let_ (op1 (.zext 8 64) (.var v)) fun (v64, ()) =>
    .let_ (op1 (.zext 8 64) (.var c8)) fun (c64, ()) =>
    .let_ (op2 (.add i64) (.var v64) (.var c64)) fun (s, ()) =>
    .ret (.var s, ())⟩

#guard armChk [zextElideInBlockFn]
#guard countDirs isArmOrrWOrUbfmDir (armCode [zextElideInBlockFn]) == 0
#guard insnCount (armCode [zextElideInBlockFn]) < insnCount (armCodeOff [zextElideInBlockFn])

/-- Cross-block `.gprZ` entry propagation: loop carries canonical `.bits 8` across entry and
backedge via `.ofBool 8`, eliminating cross-block re-zero-extension in `ON` vs `OFF`. -/
def zextCrossBlockJoinFn : Fn :=
  ⟨"zext_cross_block_join", [i64, i64, i64], [i64], fun _ _ (n0, x0, dst, ()) =>
    .let_ (op2 (.cmp .ult i64) (.var x0) (.var n0)) fun (c0, ()) =>
    .let_ (op1 (.ofBool 8) (.var c0)) fun (bInit, ()) =>
    loop1 (ts := [i64, (.bits 8)])
      (fun lp (n, b, ()) =>
        .let_ (op1 (.zext 8 64) (.var b)) fun (b64, ()) =>
        .let_ (op2 (.cmp .ugt i64) (.var n) (.imm 0)) fun (cond, ()) =>
        .jnz (.var cond)
          (.store (t := i64) (.var b64) (.var dst)
            (.let_ (op2 (.cmp .eq i64) (.var b64) (.imm 1)) fun (c1, ()) =>
             .let_ (op1 (.ofBool 8) (.var c1)) fun (bNext, ()) =>
             .let_ (op2 (.sub i64) (.var n) (.imm 1)) fun (n1, ()) =>
             .jump lp (.var n1, .var bNext, ())))
          (.ret (.var b64, ())))
      (fun lp => .jump lp (.var n0, .var bInit, ()))⟩

#guard armChk [zextCrossBlockJoinFn]
#guard countDirs isUbfmZext8Dir (armCode [zextCrossBlockJoinFn]) <
  countDirs isUbfmZext8Dir (armCodeOff [zextCrossBlockJoinFn])
#guard insnCount (armCode [zextCrossBlockJoinFn]) <
  insnCount (armCodeOff [zextCrossBlockJoinFn])

/-! ## 6. `OPT-10b`: `64 -> 32` Load Narrowing (`elideLoadTruncDeps`) -/

/-- Loading `i64` followed by a single-use `trunc 64 32` lowers to a single `LDR w` (`32`-bit
load) without emitting a `64`-bit load or explicit `ORR w`/`UBFM` narrow copy. -/
def loadTrunc64To32Fn : Fn :=
  ⟨"load_trunc_64_32", [i64], [(.bits 32)], fun _ _ (p, ()) =>
    .load (.bits 64) (.var p) fun v =>
    .let_ (op1 (.trunc 64 32) (.var v)) fun (w, ()) =>
    .ret (.var w, ())⟩

#guard armChk [loadTrunc64To32Fn]
#guard countDirs isLdrWDir (armCode [loadTrunc64To32Fn]) == 1
#guard countDirs isArmOrrWOrUbfmDir (armCode [loadTrunc64To32Fn]) == 0

/-! ## 7. `OPT-10c`: Dead-Low `umulw` / `smulw` (`armMulHi`) -/

/-- Dead-low 64-bit unsigned and signed widening multiplies emit only `UMULH`/`SMULH`. -/
def mulHiUnsignedFn : Fn :=
  ⟨"mulhi_u64", [i64, i64], [i64], fun _ _ (a, b, ()) =>
    .let_ (op2 (.umulw 64) (.var a) (.var b)) fun (_lo, hi, ()) =>
    .ret (.var hi, ())⟩

def mulHiSignedFn : Fn :=
  ⟨"mulhi_s64", [i64, i64], [i64], fun _ _ (a, b, ()) =>
    .let_ (op2 (.smulw 64) (.var a) (.var b)) fun (_lo, hi, ()) =>
    .ret (.var hi, ())⟩

#guard armChk [mulHiUnsignedFn, mulHiSignedFn]
#guard countDirs isUmulhDir (armCode [mulHiUnsignedFn]) == 1 &&
  countDirs isMulDir (armCode [mulHiUnsignedFn]) == 0
#guard countDirs isSmulhDir (armCode [mulHiSignedFn]) == 1 &&
  countDirs isMulDir (armCode [mulHiSignedFn]) == 0
#guard insnCount (armCode [mulHiUnsignedFn]) < insnCount (armCodeOff [mulHiUnsignedFn])
#guard insnCount (armCode [mulHiSignedFn]) < insnCount (armCodeOff [mulHiSignedFn])

/-! ## 8. Real `Kissat.Plain` Hot-Function Activation -/

meta def plainPolFns : List Fn :=
  (LeanQbe.T.Examples.Kissat.Plain.plainModule.optInlinePolicy {}).fns

meta def okInsns : Except String (List Directive) → Nat
  | .ok ds => insnCount ds
  | .error _ => 0

meta def hotPair (nm : Sym) : Nat × Nat :=
  match plainPolFns.find? (·.name == nm) with
  | some f =>
    (okInsns (Driver.compileFnFlat armTarget.toIsa armLegalTarget f),
      okInsns (Driver.compileFnFlat armIsaNoOpt710 armLegalTarget f))
  | none => (0, 0)

meta def hotWins (nm : Sym) : Bool :=
  let (on, off) := hotPair nm
  0 < on && on < off

#guard hotWins "plain_watch_push"
#guard hotWins "plain_prop_lit"
#guard hotWins "plain_sweep"
#guard hotWins "plain_shrink_blk"
#guard hotWins "plain_rephase"
#guard hotWins "plain_ema_update"
#guard hotWins "plain_init_state"
#guard hotWins "plain_reduce"
#guard (hotPair "plain_sweep").1 <= 585

/-! ## 9. Axiom Audit (`std3` only) -/

#print axioms LeanQbe.T.Arm64.armTarget
#print axioms LeanQbe.T.Arm64.armLabelClean
#print axioms LeanQbe.T.compile_sound

end LeanQbeTest.T.Arm64W62Opt710Test
