module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.MainCertInline
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Arm64.PrintAlign
public import LeanQbe.T.Arm64.DebugAsm
public import LeanQbe.T.Examples.LitmusProgs
public import LeanQbe.T.Examples.Bignum
public import LeanQbe.T.Examples.ChaCha
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Notation
public meta import Lean
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.MainCertFlatElab
public meta import LeanQbe.T.MainCertInline
public meta import LeanQbe.T.Arm64.Targ
public meta import LeanQbe.T.Arm64.PrintAlign
public meta import LeanQbe.T.Arm64.DebugAsm
public meta import LeanQbe.T.Examples.LitmusProgs
public meta import LeanQbe.T.Examples.Bignum
public meta import LeanQbe.T.Examples.ChaCha
public meta import LeanQbe.T.Examples.LratBytes
public meta import LeanQbe.T.MainFlat

/-!
# P0 Backend Performance Pack — AAPCS64 Arm64 Regression & Parity Tests

Verifies Ranks 4 & 5 on AAPCS64 Arm64:
1. Rank 4 (`RegaDefs.lname` + `Arm64.DebugAsm`): `.L<fn>.<n>` local labels (`0` `{fn}.L{n}` leaks)
   and `emitArm64DebugAsmChecked` `some hs == none` parity with `loopAlign := true/false`.
2. Rank 5a (`Arm64.Isel` `armMovIns`): zero-cycle-renamed `ORR_s` (`orr xD, xzr, xS`) for GPR
   moves, `ADD_e #0` preserved for `.SP`, and `0` non-SP `add xD, xS, #0` across compiled programs.
3. Rank 5b (`Arm64.PrintAlign`): unit and compiled-IR `.p2align 4` backward-branch loop alignment
   (`B`, `B_cond`, `CBZ`, `CBNZ`, `TBZ`, `TBNZ`, skipping forward branches and tail calls).
4. Exact `(flat := false)` vs `(flat := true)` kernel `code = rfl` and `bounds = rfl` parity.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.P0BackendPackArm64Test

open Kraken.AArch64
open LeanQbe.T
open LeanQbe.T.Arm64
open LeanQbe.T.Notation

/-! ## Rank 5a: Kernel-Checked `armMovIns` (`ORR_s` for GPR, `ADD_e` for `.SP`) -/

def isOrrMov : List Directive → Bool
  | [.instr ⟨.W64, .ORR_s (.low (.reg _) .W64) (.low .XZR .W64) _⟩] => true
  | _ => false

def isAdd0Mov : List Directive → Bool
  | [.instr ⟨.W64, .ADD_e _ _ (.imm ⟨0, .S0⟩)⟩] => true
  | _ => false

theorem armMov_gpr_is_orr :
    isOrrMov (armGpr.mov (.reg .X0) (.reg .X1)) = true := by rfl

#guard toAsm (armGpr.mov (.reg .X0) (.reg .X1)) == "orr x0, xzr, x1"

theorem armMov_sp_dst_is_add :
    isAdd0Mov (armGpr.mov .SP (.reg .X0)) = true := by rfl

theorem armMov_sp_src_is_add :
    isAdd0Mov (armGpr.mov (.reg .X0) .SP) = true := by rfl

/-! ## Rank 5b: `Arm64.PrintAlign` Unit Tests -/

private def mkB (l : String) : Directive := .instr ⟨.W64, .B (.label l)⟩
private def mkBne (l : String) : Directive := .instr ⟨.W64, .B_cond .NE (.label l)⟩
private def mkCbz (l : String) : Directive :=
  .instr ⟨.W64, .CBZ (.low (.reg .X0) .W64) (.label l)⟩
private def mkCbnz (l : String) : Directive :=
  .instr ⟨.W64, .CBNZ (.low (.reg .X0) .W64) (.label l)⟩
private def mkTbz (l : String) : Directive :=
  .instr ⟨.W64, .TBZ (.low (.reg .X0) .W64) 0 (.label l)⟩
private def mkTbnz (l : String) : Directive :=
  .instr ⟨.W64, .TBNZ (.low (.reg .X0) .W64) 0 (.label l)⟩
private def mkRet : Directive := .instr ⟨.W64, .RET (.low (.reg .X30) .W64)⟩
private def mkMov01 : Directive :=
  match armGpr.mov (.reg .X0) (.reg .X1) with
  | d :: _ => d
  | [] => mkRet

private def countAlign (asm : String) : Nat :=
  (asm.splitOn "\n").foldl (fun a ln =>
    if ln.trimAscii.toString == loopAlignDirective then a + 1 else a) 0

private def alignPrecedesOnly (asm : String) (hdrs : List String) : Bool :=
  let lines := (asm.splitOn "\n").map (·.trimAscii.toString)
  let rec go : List String → List String → Bool
    | [], acc => acc.reverse == hdrs
    | ln :: rest, acc =>
      if ln == loopAlignDirective then
        match rest with
        | lbl :: rest' =>
          if lbl.endsWith ":" then
            go rest' ((lbl.dropEnd 1).toString :: acc)
          else false
        | [] => false
      else go rest acc
  go lines []

#guard
  let straight : List Directive := [.label "fn", mkMov01, mkRet]
  let fwd : List Directive :=
    [.label "fn", mkBne ".Lfn.1", mkMov01, mkB ".Lfn.0",
     .label ".Lfn.0", mkMov01, .label ".Lfn.1", mkRet]
  let selfTail : List Directive := [.label "fn", mkMov01, mkB "fn"]
  detectLoopHeaders straight == [] && toAsmAligned straight == toAsm straight &&
  detectLoopHeaders fwd == [] && toAsmAligned fwd == toAsm fwd &&
  detectLoopHeaders selfTail == [] && toAsmAligned selfTail == toAsm selfTail

#guard
  let backProgs : List (List Directive) :=
    [ [.label "f0", .label ".Lf0.0", mkMov01, mkB ".Lf0.0", mkRet]
    , [.label "f1", .label ".Lf1.0", mkMov01, mkBne ".Lf1.0", mkRet]
    , [.label "f2", .label ".Lf2.0", mkMov01, mkCbz ".Lf2.0", mkRet]
    , [.label "f3", .label ".Lf3.0", mkMov01, mkCbnz ".Lf3.0", mkRet]
    , [.label "f4", .label ".Lf4.0", mkMov01, mkTbz ".Lf4.0", mkRet]
    , [.label "f5", .label ".Lf5.0", mkMov01, mkTbnz ".Lf5.0", mkRet] ]
  backProgs.all fun p =>
    let asm := toAsmAligned p
    let hdrs := detectLoopHeaders p
    hdrs.length == 1 && countAlign asm == 1 && alignPrecedesOnly asm hdrs &&
      toAsmWithAlign none p == toAsm p

#guard
  let multi : List Directive :=
    [.label "fn", mkB ".Lfn.0", .label ".Lfn.0", .label ".Lfn.1",
     mkCbnz ".Lfn.1", mkBne ".Lfn.0", mkB ".Lfn.0", .label ".Lfn.2", mkRet]
  let asm := toAsmAligned multi
  detectLoopHeaders multi == [".Lfn.0", ".Lfn.1"] &&
    countAlign asm == 2 && alignPrecedesOnly asm [".Lfn.0", ".Lfn.1"]

/-! ## Compiled-IR Checks (Ranks 4, 5a, 5b) -/

private meta def compileArmFns (fns : List Fn) : List Directive :=
  let hs := fns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  match compile armTarget.toIsa armLegalTarget fns hs with
  | .ok ds => ds
  | .error _ => []

private meta def isNonSpAdd0 (ln : String) : Bool :=
  let s := ln.trimAscii.toString
  s.startsWith "add x" && s.endsWith ", #0" && (s.splitOn "sp").length == 1

private meta def isOrrMovXX (ln : String) : Bool :=
  let s := ln.trimAscii.toString
  s.startsWith "orr x" && (s.splitOn ", xzr, x").length > 1

-- Compiled `sumto`, `chacha20Module`, `lratBytesFns`, `mul4x4Module`:
-- 0 non-SP `add x, y, #0`, `orr x, xzr, y` emitted, `.p2align 4` on loops (`0` on `mul4x4`)
#guard
  let sumDs := compileArmFns [Examples.Litmus.sumto]
  let ccDs := compileArmFns Examples.ChaCha.chacha20Module.fns
  let lratDs := compileArmFns Examples.LratBytes.lratBytesFns
  let mulDs := compileArmFns Examples.Bignum.mul4x4Module.fns
  let allAsm := toAsmAligned (sumDs ++ ccDs ++ lratDs ++ mulDs)
  let allLines := allAsm.splitOn "\n"
  let nAdd0 := allLines.foldl (fun a l => if isNonSpAdd0 l then a + 1 else a) 0
  let nMov := allLines.foldl (fun a l => if isOrrMovXX l then a + 1 else a) 0
  nAdd0 == 0 && nMov ≥ 10 &&
    countAlign (toAsmAligned sumDs) ≥ 1 &&
    countAlign (toAsmAligned ccDs) ≥ 1 &&
    countAlign (toAsmAligned lratDs) ≥ 1 &&
    countAlign (toAsmAligned mulDs) == 0

-- Rank 4 + DebugAsm parity on Arm64 (`loopAlign := true` and `false`)
#guard
  let fns := [Examples.Litmus.sumto, Examples.Litmus.evenodd, Examples.Litmus.nested]
  let hs := fns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  match compile armTarget.toIsa armLegalTarget fns hs with
  | .error _ => false
  | .ok ds =>
    let fnNames := fns.map (·.name)
    let localLbls := ds.filterMap fun
      | .label l => if fnNames.contains l then none else some l
      | _ => none
    let allDotL := !localLbls.isEmpty && localLbls.all (·.startsWith ".L")
    let dbgAligned :=
      match emitArm64DebugAsmChecked fns ds (some hs) [] false true,
            emitArm64DebugAsmChecked fns ds none [] false true with
      | .ok s1, .ok s2 => s1 == s2 && countAlign s1 ≥ 2
      | _, _ => false
    let dbgNoAlign :=
      match emitArm64DebugAsmChecked fns ds (some hs) [] false false,
            emitArm64DebugAsmChecked fns ds none [] false false with
      | .ok s1, .ok s2 => s1 == s2 && countAlign s1 == 0
      | _, _ => false
    allDotL && dbgAligned && dbgNoAlign

/-! ## Dual-Mode `(flat := false)` vs `(flat := true)` Parity -/

def p0ArmSrcMod : Module :=
  ⟨[Examples.Litmus.sumto, Examples.Litmus.evenodd, Examples.Litmus.nested], [], []⟩

inline_mod! p0ArmMod p0ArmSrcMod {} (compile := false)

compile_linked_chunks! p0ArmLeg armTarget armLayout armLegalTarget armLabelClean
  p0ArmMod 32 (flat := false)

compile_linked_chunks! p0ArmFlat armTarget armLayout armLegalTarget armLabelClean
  p0ArmMod 32 (flat := true)

theorem p0_arm_code_eq : p0ArmLeg.code = p0ArmFlat.code := rfl

theorem p0_arm_bounds_eq : p0ArmLeg.bounds = p0ArmFlat.bounds := rfl

#print axioms armMov_gpr_is_orr
#print axioms armMov_sp_dst_is_add
#print axioms armMov_sp_src_is_add
#print axioms p0_arm_code_eq
#print axioms p0_arm_bounds_eq
#print axioms p0ArmLeg
#print axioms p0ArmFlat

end LeanQbeTest.T.P0BackendPackArm64Test
