/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.AddrRangeOptLemmas
public import LeanQbe.T.OptFlatAddrRangeLemmas
public import LeanQbe.T.OptLemmas
public import LeanQbe.T.MainLemmas
public import LeanQbe.T.Arm64.TargLemmas
import LeanQbe.T.Driver
import LeanQbe.T.Arm64.Targ
import LeanQbe.T.MainInline
import LeanQbe.T.Examples.Kissat.Plain
import Kraken.AArch64.Syntax
meta import LeanQbe.T.Driver
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.MainInline
meta import LeanQbe.T.Examples.Kissat.Plain
meta import Kraken.AArch64.Syntax

/-!
# `OPT-5` Displacement-into-Hoisted-Base Folding Tests (`AddrDispHoistTest`)

Verifies `LegalTarget.foldAddrDisp` (`true` on `armLegalTarget`, `false` on `x64LegalTarget`),
`Func.addrRangeOptWith`, and `OptFlatAddrRange.addrRangeOptFlatWith`:
1. Unit litmus loops (`addrShl` and `addrPlain` with unique non-zero `+12` displacement) hoist
   `((base + (inv <<< 2)) + 12)` out of the loop when `foldDisp = true` and emit single-instruction
   `ldr w, [xH, wI, uxtw #2]` on AArch64 (`0` `add x16` + `[x16, #12]` pairs).
2. Negative unique-disp guard: functions accessing the same hoisted `(base, inv, sh)` with
   multiple distinct displacements (`+8` and `+12`) keep displacements unhoisted.
3. Kissat `Plain` AArch64 activation `#guard`s:
   * AArch64 `plain_shrink_blk`, `plain_watch_push`, `plain_prop_lit`, and `plain_analyze_rsn`
     emit `<= 1` (and `0` on `plain_shrink_blk`, `plain_watch_push`, `plain_prop_lit`)
     `add x16, ..., uxtw #2; ldr/str [x16, #12]` pairs and bounded scaled-`x16` disp pairs.
   * x86-64 `LegalTarget.x64` keeps `foldAddrDisp = false` (`0`-diff SIB addressing).
4. Standard-axiom audit (`<= std3`, `0` sorry).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.AddrDispHoistTest

open LeanQbe.T

/-! ## 1. LegalTarget Flag Checks -/

#guard Arm64.armLegalTarget.foldAddrDisp == true
#guard LegalTarget.aarch64.foldAddrDisp == true
#guard (LegalTarget.x64 [128, 256, 512]).foldAddrDisp == false

/-! ## 2. Unit Litmus IR & Negative Multi-Disp Guard -/

/-- Unique `+12` displacement via `zext(iv) + 3 + zext(inv)` shifted by `2`. -/
def dispShlAddLoop : Func [i64, i32, i32] [i64] := fun _ _ (base, inv, n, ()) =>
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
    (fun lp => .jump lp (.imm 0, .imm 0, ()))

/-- Unique `+12` displacement via unshifted `base + ((inv + iv) + 12)`. -/
def dispPlainLoop : Func [i64, i64, i64] [i64] := fun _ _ (base, inv, n, ()) =>
  loop1 (ts := [i64, i64])
    (fun lp (iv, acc, ()) =>
      .let_ (op2 (.cmp .eq i64) (.var iv) (.var n)) fun (done, ()) =>
      .jnz (.var done) (.ret (.var acc, ()))
        (.let_ (op2 (.add i64) (.var inv) (.var iv)) fun (idx, ()) =>
         .let_ (op2 (.add i64) (.var idx) (.imm 12)) fun (off, ()) =>
         .let_ (op2 (.add i64) (.var base) (.var off)) fun (ptr, ()) =>
         .load i8 (.var ptr) fun b =>
         .let_ (op1 (.zext 8 64) (.var b)) fun (b64, ()) =>
         .let_ (op2 (.add i64) (.var acc) (.var b64)) fun (acc', ()) =>
         .let_ (op2 (.add i64) (.var iv) (.imm 1)) fun (iv', ()) =>
         .jump lp (.var iv', .var acc', ())))
    (fun lp => .jump lp (.imm 0, .imm 0, ()))

/-- Multi-disp negative guard: same `(base, inv, sh=2)` used with both `+8` and `+12`. -/
def multiDispGuardLoop : Func [i64, i32, i32] [i64] := fun _ _ (base, inv, n, ()) =>
  loop1 (ts := [i32, i64])
    (fun lp (iv, acc, ()) =>
      .let_ (op2 (.cmp .eq i32) (.var iv) (.var n)) fun (done, ()) =>
      .jnz (.var done) (.ret (.var acc, ()))
        (.let_ (op1 (.zext 32 64) (.var iv)) fun (iv64, ()) =>
         .let_ (op1 (.zext 32 64) (.var inv)) fun (inv64, ()) =>
         .let_ (op2 (.add i64) (.var iv64) (.var inv64)) fun (idx, ()) =>
         .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun (off, ()) =>
         .let_ (op2 (.add i64) (.var off) (.imm 8)) fun (off8, ()) =>
         .let_ (op2 (.add i64) (.var base) (.var off8)) fun (p8, ()) =>
         .load i32 (.var p8) fun w1 =>
         .let_ (op2 (.add i64) (.var off) (.imm 12)) fun (off12, ()) =>
         .let_ (op2 (.add i64) (.var base) (.var off12)) fun (p12, ()) =>
         .load i32 (.var p12) fun w2 =>
         .let_ (op2 (.add i32) (.var w1) (.var w2)) fun (sum, ()) =>
         .let_ (op1 (.zext 32 64) (.var sum)) fun (s64, ()) =>
         .let_ (op2 (.add i64) (.var acc) (.var s64)) fun (acc', ()) =>
         .let_ (op2 (.add i32) (.var iv) (.imm 1)) fun (iv', ()) =>
         .jump lp (.var iv', .var acc', ())))
    (fun lp => .jump lp (.imm 0, .imm 0, ()))

mutual
def countOuterLets {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k => 1 + countOuterLets k
  | .load _ _ k | .store _ _ k | .call _ _ _ k => countOuterLets k
  | .jnz _ t e => countOuterLets t + countOuterLets e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => 0
  | .group _ k => countOuterLets k
end

def funcOuterLets {as rs : List Ty} (f : Func as rs) : Nat :=
  countOuterLets (reifyFunc f)

-- With `foldDisp = true`, `dispShlAddLoop` hoists 4 outer lets (`zext`, `shl`, `add base`, `+12`)
-- vs 3 when `foldDisp = false`; `dispPlainLoop` hoists 2 (`base+inv`, `+12`) vs 1.
#guard funcOuterLets (Func.dceP (Func.licm (Func.lateCfgPreWith true dispShlAddLoop))) == 4
#guard funcOuterLets (Func.dceP (Func.licm (Func.lateCfgPreWith false dispShlAddLoop))) == 3
#guard funcOuterLets (Func.dceP (Func.licm (Func.lateCfgPreWith true dispPlainLoop))) == 2
#guard funcOuterLets (Func.dceP (Func.licm (Func.lateCfgPreWith false dispPlainLoop))) == 1

-- Multi-displacement `(base, inv, sh=2)` with `{8, 12}` MUST NOT fold either `+disp`.
theorem multiDispGuardLoop_no_disp_fold :
    Func.addrRangeOptWith true multiDispGuardLoop =
      Func.addrRangeOptWith false multiDispGuardLoop := by
  rfl

theorem multiDispGuardLoop_flat_no_disp_fold :
    OptFlatAddrRange.addrRangeOptFlatWith true [i64, i32, i32] (reifyFunc multiDispGuardLoop) =
      OptFlatAddrRange.addrRangeOptFlatWith false [i64, i32, i32]
        (reifyFunc multiDispGuardLoop) := by
  rfl

/-! ## 3. End-to-End AArch64 Unit Codegen Checks -/

private abbrev ArmDir := Arm64.armTarget.toIsa.Directive

private def isRegX16 {w : RegWidth} : RegOrSp w → Bool
  | .low (.reg .X16) _ => true
  | _ => false

private def isZrX16 {w : RegWidth} : RegOrZr w → Bool
  | .low (.reg .X16) _ => true
  | _ => false

private def isAddX16ExtUxtw2 : ArmDir → Bool
  | .instr {
      operation := .ADD_e dst _ (.ext { ext := { type := .UXTW, amount := .E2 }, .. }), .. } =>
    isRegX16 dst
  | _ => false

private def isAddX16Scaled : ArmDir → Bool
  | .instr { operation := .ADD_e dst _ (.ext _), .. } => isRegX16 dst
  | .instr { operation := .ADD_s dst _ _, .. } => isZrX16 dst
  | _ => false

private def isX16ImmMemAccess : ArmDir → Int64 → Bool
  | .instr {
      operation := .LDR _ (.addr { base := b, off := .imm { imm := .int64 k, .. } }), .. },
      d => isRegX16 b && k == d
  | .instr {
      operation := .STR _ { base := b, off := .imm { imm := .int64 k, .. } }, .. }, d =>
    isRegX16 b && k == d
  | _, _ => false

private def isX16AnyImmMemAccess : ArmDir → Bool
  | .instr { operation := .LDR _ (.addr { base := b, off := .imm _ }), .. } => isRegX16 b
  | .instr { operation := .STR _ { base := b, off := .imm _ }, .. } => isRegX16 b
  | _ => false

private def countX16Uxtw2Disp12 : List ArmDir → Nat
  | [] | [_] => 0
  | d1 :: d2 :: rest =>
    (if isAddX16ExtUxtw2 d1 && isX16ImmMemAccess d2 12 then 1 else 0) +
      countX16Uxtw2Disp12 (d2 :: rest)

private def countX16AnyDispPairs : List ArmDir → Nat
  | [] | [_] => 0
  | d1 :: d2 :: rest =>
    (if isAddX16Scaled d1 && isX16AnyImmMemAccess d2 then 1 else 0) +
      countX16AnyDispPairs (d2 :: rest)

private def isArmIdxScale2Ldr : ArmDir → Bool
  | .instr { operation := .LDR _ (.addr { off := .reg { ext := e, .. }, .. }), .. } =>
    e.amount == .E2
  | _ => false

private def dispShlArmFn : Fn :=
  ⟨"dispShlArm", [i64, i32, i32], [i64], dispShlAddLoop⟩

private def dispPlainArmFn : Fn :=
  ⟨"dispPlainArm", [i64, i64, i64], [i64], dispPlainLoop⟩

private def multiDispArmFn : Fn :=
  ⟨"multiDispArm", [i64, i32, i32], [i64], multiDispGuardLoop⟩

private def compileArmOk (f : Fn) : Except String (List ArmDir) :=
  Driver.compileFnFlat Arm64.armTarget.toIsa Arm64.armLegalTarget f

private def armHasSingleIdxLdrNoX16 (f : Fn) : Bool :=
  match compileArmOk f with
  | .ok ds =>
    countX16Uxtw2Disp12 ds == 0 && (ds.filter isArmIdxScale2Ldr).length >= 1
  | .error _ => false

private def armNoDispFoldOnMulti (f : Fn) : Bool :=
  match compileArmOk f with
  | .ok ds => countX16Uxtw2Disp12 ds >= 1
  | .error _ => false

#guard armHasSingleIdxLdrNoX16 dispShlArmFn
#guard match compileArmOk dispPlainArmFn with
  | .ok ds => countX16AnyDispPairs ds == 0
  | .error _ => false
#guard armNoDispFoldOnMulti multiDispArmFn

/-! ## 4. Kissat `Plain` Arm64 Activation `#guard`s -/

private meta abbrev ArmDirM := Arm64.armTarget.toIsa.Directive

private meta def isRegX16M {w : RegWidth} : RegOrSp w → Bool
  | .low (.reg .X16) _ => true
  | _ => false

private meta def isZrX16M {w : RegWidth} : RegOrZr w → Bool
  | .low (.reg .X16) _ => true
  | _ => false

private meta def isAddX16ExtUxtw2M : ArmDirM → Bool
  | .instr {
      operation := .ADD_e dst _ (.ext { ext := { type := .UXTW, amount := .E2 }, .. }), .. } =>
    isRegX16M dst
  | _ => false

private meta def isAddX16ScaledM : ArmDirM → Bool
  | .instr { operation := .ADD_e dst _ (.ext _), .. } => isRegX16M dst
  | .instr { operation := .ADD_s dst _ _, .. } => isZrX16M dst
  | _ => false

private meta def isX16ImmMemAccessM : ArmDirM → Int64 → Bool
  | .instr {
      operation := .LDR _ (.addr { base := b, off := .imm { imm := .int64 k, .. } }), .. },
      d => isRegX16M b && k == d
  | .instr {
      operation := .STR _ { base := b, off := .imm { imm := .int64 k, .. } }, .. }, d =>
    isRegX16M b && k == d
  | _, _ => false

private meta def isX16AnyImmMemAccessM : ArmDirM → Bool
  | .instr { operation := .LDR _ (.addr { base := b, off := .imm _ }), .. } => isRegX16M b
  | .instr { operation := .STR _ { base := b, off := .imm _ }, .. } => isRegX16M b
  | _ => false

private meta def countX16Uxtw2Disp12M : List ArmDirM → Nat
  | [] | [_] => 0
  | d1 :: d2 :: rest =>
    (if isAddX16ExtUxtw2M d1 && isX16ImmMemAccessM d2 12 then 1 else 0) +
      countX16Uxtw2Disp12M (d2 :: rest)

private meta def countX16AnyDispPairsM : List ArmDirM → Nat
  | [] | [_] => 0
  | d1 :: d2 :: rest =>
    (if isAddX16ScaledM d1 && isX16AnyImmMemAccessM d2 then 1 else 0) +
      countX16AnyDispPairsM (d2 :: rest)

private meta def findPlainInlFn (nm : Sym) : Option Fn :=
  let m := LeanQbe.T.Examples.Kissat.Plain.plainModule
  let fns := (m.optInlinePolicy {}).fns
  fns.find? (·.name == nm)

private meta def checkKissatArm64 (nm : Sym) (maxUxtw2Disp12 maxTotalPairs : Nat) : Bool :=
  match findPlainInlFn nm with
  | none => false
  | some f =>
    match Driver.compileFnFlat Arm64.armTarget.toIsa Arm64.armLegalTarget f with
    | .error _ => false
    | .ok ds =>
      countX16Uxtw2Disp12M ds <= maxUxtw2Disp12 && countX16AnyDispPairsM ds <= maxTotalPairs

#guard checkKissatArm64 "plain_shrink_blk" 0 4
#guard checkKissatArm64 "plain_watch_push" 0 11
#guard checkKissatArm64 "plain_analyze_rsn" 1 2
#guard checkKissatArm64 "plain_prop_lit" 0 14

/-! ## 5. Axiom Audit -/

#print axioms LeanQbe.T.Func.addrRangeOptWith_wf
#print axioms LeanQbe.T.Func.addrRangeOptWith_spec
#print axioms LeanQbe.T.OptFlatAddrRange.addrRangeOptFlatWith_eq
#print axioms LeanQbe.T.Func.lateCfgPreWith_wf
#print axioms LeanQbe.T.Func.lateCfgPreWith_spec

end LeanQbeTest.T.AddrDispHoistTest
