module

public import BvDecideQbe.Tactic
public meta import BvDecideQbe.Tactic
public import Lean.Compiler.IR.CompilerM
public meta import Lean.Compiler.IR.CompilerM

/-!
# Trust-Pure `bv_decide_qbe` End-to-End Unit Tests (`S3d`)

Verifies:
1. Concrete UNSAT BitVec theorems proved directly via `by bv_decide_qbe` and `by bv_decide_qbe +uf`.
2. `#print axioms` and programmatic `collectAxioms` audit: ONLY
   `[propext, Classical.choice, Quot.sound, <thm>._leanqbe.bv_solve.ax_1]` (0 source axioms).
3. `_expr_def` is added via `Lean.addDecl` ONLY (zero `compileDecl` IR entries).
4. Pure kernel `Eq.refl` reduction (`BVProg.parseWords ws = some _expr_def`) `< 5 ms`.
5. SAT counterexample decoding (`evalEfficient`-validated) and formatting via `bvDecideQbe'`.
6. Injectable `SolveFn` tests: `2x` `.workTooSmall` retry escalation, real `solveDimacsBackend`
   retry, corrupt SAT model rejection by `evalEfficient`, and `.unknown` / OOM error handling.
-/

set_option autoImplicit false
set_option Elab.async false

public section

namespace BvDecideQbeTest.UnitTest

open Lean
open Lean.Meta
open Lean.Meta.Tactic.BVDecide
open Std.Tactic.BVDecide
open LeanQbe.T.Examples.Bitblast.Ref
open BvDecideQbe

/-! ## 1. Concrete UNSAT Theorems (`by bv_decide_qbe` & `+uf`) -/

theorem thm_a1 (x y z : BitVec 32) :
    (((x &&& y) ||| (x &&& ~~~y)) ^^^ z) = (x ^^^ z) := by
  bv_decide_qbe

theorem thm_a2 (x y : BitVec 32) :
    ((x ^^^ y) + ((x &&& y) <<< 1#32)) = (x + y) := by
  bv_decide_qbe

theorem thm_a3 (x y : BitVec 32) :
    ((x ||| y) - (x &&& y)) = (x ^^^ y) := by
  bv_decide_qbe

theorem thm_a5 (x : BitVec 16) :
    (let m := BitVec.sshiftRight x 15
     ((x ^^^ m) - m) = (if x.getLsbD 15 then ~~~x + 1#16 else x)) := by
  bv_decide_qbe

theorem thm_b1 (x y : BitVec 64) :
    ((x ^^^ y) + ((x &&& y) <<< 1#64)) = (x + y) := by
  bv_decide_qbe

theorem thm_b2 (x y : BitVec 128) :
    let zx := BitVec.zeroExtend 129 x
    let zy := BitVec.zeroExtend 129 y
    ((zx + zy) >>> 1#129) =
      BitVec.zeroExtend 129 ((x &&& y) + ((x ^^^ y) >>> 1#128)) := by
  bv_decide_qbe

theorem thm_b4 (a b c : BitVec 256) :
    (((a ^^^ b) ^^^ c) + (((a &&& b) ||| (b &&& c) ||| (a &&& c)) <<< 1#256)) =
      ((a + b) + c) := by
  bv_decide_qbe

theorem thm_b5 (a b c : BitVec 256) (h1 : a < b) (h2 : b < c) : a < c := by
  bv_decide_qbe

theorem thm_d6 (x0 x1 : BitVec 4) (h0 : x0 < 2#4) (h1 : x1 < 2#4) (hne : x0 ≠ x1) :
    x0 ^^^ x1 = 1#4 := by
  bv_decide_qbe

theorem thm_uint32 (a b : UInt32) :
    ((a ^^^ b) + ((a &&& b) <<< 1)) = (a + b) := by
  bv_decide_qbe

theorem thm_preproc_only (x : BitVec 32) : x ^^^ x = 0#32 := by
  bv_decide_qbe

theorem thm_cegar_e1 (f : BitVec 32 → BitVec 32) (x y : BitVec 32)
    (h : x ^^^ y = 0#32) : f x = f y := by
  bv_decide_qbe +uf

theorem thm_cegar_multi (f : BitVec 16 → BitVec 16 → BitVec 16) (a b c : BitVec 16)
    (h1 : a = b) (h2 : b = c) : f a (c + 0#16) = f c a := by
  bv_decide_qbe +uf

theorem thm_cegar_bool (p : BitVec 8 → Bool) (x y : BitVec 8)
    (h : x + 1#8 = y + 1#8) : p x = p y := by
  bv_decide_qbe +uf

#print axioms thm_a1
#print axioms thm_a2
#print axioms thm_b4
#print axioms thm_b5
#print axioms thm_cegar_e1

/-! ## 2. Programmatic MetaM / Kernel Verification Suite -/

private def assertTrue (msg : String) (b : Bool) : IO Unit := do
  if !b then throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def stdAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

private def resolveAuxName (env : Environment) (base : Name) : Name :=
  if env.contains base then base else mkPrivateName env base

private def checkTheoremAxioms (thmName : Name) (expectPerGoalAx : Bool) : CoreM Unit := do
  let axs ← collectAxioms thmName
  let env ← getEnv
  let expectedAx := resolveAuxName env (thmName ++ `_leanqbe.bv_solve.ax_1)
  if expectPerGoalAx then
    assertTrue s!"{thmName}: expected axiom {expectedAx} in {axs.toList}"
      (axs.contains expectedAx)
    let some axInfo := env.find? expectedAx
      | throwError "missing axiom {expectedAx}"
    assertTrue s!"{expectedAx}: must be axiomInfo" (axInfo matches .axiomInfo _)
  for ax in axs do
    if !stdAxioms.contains ax && (!expectPerGoalAx || ax != expectedAx) then
      throwError "unexpected axiom {ax} in {thmName}"
  let exprDefName := resolveAuxName env (thmName ++ `_expr_def_1)
  if expectPerGoalAx then
    let some defInfo := env.find? exprDefName
      | throwError "missing _expr_def {exprDefName} for {thmName}"
    assertTrue s!"{exprDefName}: must be defnInfo" (defInfo matches .defnInfo _)
    assertTrue s!"{exprDefName}: must NOT be compiled (IR.findEnvDecl == none)"
      (IR.findEnvDecl env exprDefName |>.isNone)

private def checkKernelEqReflTiming (ws : List Nat) (bv : BVLogicalExpr) :
    MetaM Nat := do
  let expr := ShareCommon.shareCommon (toExpr bv)
  let exprDefName ← Lean.mkAuxDeclName `_test_expr_def
  Lean.addDecl <| .defnDecl {
    name := exprDefName
    levelParams := []
    type := mkConst ``BVLogicalExpr
    value := expr
    hints := .abbrev
    safety := .safe
  }
  let wsExpr := mkNatListExpr ws
  let bvLogTy := mkConst ``BVLogicalExpr
  let optBvLogTy := mkApp (mkConst ``Option [0]) bvLogTy
  let reflectedExpr := mkConst exprDefName
  let someExpr := mkApp2 (mkConst ``Option.some [0]) bvLogTy reflectedExpr
  let lhs := mkApp (mkConst ``BVProg.parseWords) wsExpr
  let eqType := mkApp3 (mkConst ``Eq [1]) optBvLogTy lhs someExpr
  let prf := mkApp2 (mkConst ``Eq.refl [1]) optBvLogTy someExpr
  let thmName ← Lean.mkAuxDeclName `_test_rfl_thm
  let env ← getEnv
  let decl : Declaration := .thmDecl {
    name := thmName
    levelParams := []
    type := eqType
    value := prf
  }
  let kenv := env.toKernelEnv
  let t0 ← IO.monoNanosNow
  let _ ← Lean.ofExceptKernelException (kenv.addDeclCore 0 0 decl none)
  let t1 ← IO.monoNanosNow
  return t1 - t0

private def dagExpr (n : Nat) : BVLogicalExpr := Id.run do
  let x : BVExpr 32 := .var 0
  let y : BVExpr 32 := .var 1
  let mut cur : BVExpr 32 := .bin x .add y
  for i in [0:n] do
    if i % 2 == 0 then
      cur := .bin cur .xor y
    else
      cur := .bin cur .add x
  return .not (.literal (.bin cur .eq cur))

private def runMetaGoal (prop : Expr) (cfg : Lean.Elab.Tactic.BVDecide.BVDecideConfig := {})
    (qbeCtx : QbeContext := {}) : MetaM (Except String (Except CounterExample CegarResult)) := do
  let mvar ← mkFreshExprMVar prop
  let tacticCtx := mkQbeTacticContext cfg
  let params ← Grind.mkDefaultParams {}
  try
    let res ← Grind.GrindM.run (params := params) <|
      bvDecideQbe' (.mvarIdTarget mvar.mvarId!) tacticCtx qbeCtx
    return .ok res
  catch ex =>
    return .error (← ex.toMessageData.toString)

private def mkTestBvForall (w : Nat) (bodyFn : Expr → MetaM Expr) : MetaM Expr :=
  withLocalDeclD `x (mkApp (mkConst ``BitVec) (mkNatLit w)) fun x => do
    mkForallFVars #[x] (← bodyFn x)

private def runAllCore : CoreM Unit := do
  -- 1. Audit axioms and non-compilation of _expr_def on reflected theorems
  for thm in [``thm_a1, ``thm_a2, ``thm_a3, ``thm_a5, ``thm_b1, ``thm_b2,
              ``thm_b4, ``thm_b5, ``thm_d6, ``thm_uint32, ``thm_cegar_e1,
              ``thm_cegar_multi, ``thm_cegar_bool] do
    checkTheoremAxioms thm true
  checkTheoremAxioms ``thm_preproc_only false

  -- 2. Verify zero non-per-goal axioms across all BvDecideQbe / BvDecideQbeTest decls
  let env ← getEnv
  let reflectedNames : List Name :=
    [``thm_a1, ``thm_a2, ``thm_a3, ``thm_a5, ``thm_b1, ``thm_b2,
     ``thm_b4, ``thm_b5, ``thm_d6, ``thm_uint32, ``thm_cegar_e1,
     ``thm_cegar_multi, ``thm_cegar_bool]
  for (name, _) in env.constants do
    let s := name.toString
    if (s.startsWith "BvDecideQbe." || s.startsWith "BvDecideQbeTest.") &&
       !reflectedNames.contains name && !s.endsWith "._leanqbe.bv_solve.ax_1" &&
       !s.contains "._test_" && !s.contains ".runAll" then
      let axs ← collectAxioms name
      for ax in axs do
        if !stdAxioms.contains ax then
          throwError "unexpected axiom {ax} used by {name}"

  -- 3. Kernel Eq.refl timing gate (< 5 ms small) + wide/DAG checks
  MetaM.run' do
    let smallExpr : BVLogicalExpr :=
      .not (.literal (.bin (.bin (.var 0 : BVExpr 4) .xor (.var 0)) .eq (.const 0#4)))
    let smallWs := (BvDecideQbe.encodeWords smallExpr).get!
    let nsSmall ← checkKernelEqReflTiming smallWs smallExpr
    assertTrue s!"kernel rfl small took {nsSmall / 1000} us (< 5000 us)" (nsSmall < 5000000)

    let b4Expr : BVLogicalExpr :=
      let a : BVExpr 256 := .var 0
      let b : BVExpr 256 := .var 1
      let c : BVExpr 256 := .var 2
      .not (.literal (.bin (.bin (.bin (.bin a .xor b) .xor c) .add
        (.shiftLeft (.bin (.bin a .and b) .or (.bin (.bin b .and c) .or (.bin a .and c)))
          (.const 1#256))) .eq (.bin (.bin a .add b) .add c)))
    let b4Ws := (BvDecideQbe.encodeWords b4Expr).get!
    let nsB4 ← checkKernelEqReflTiming b4Ws b4Expr
    assertTrue s!"kernel rfl b4 took {nsB4 / 1000000} ms (< 50 ms)" (nsB4 < 50000000)

    let dag120 := dagExpr 120
    let dagWs := (BvDecideQbe.encodeWords dag120).get!
    let nsDag ← checkKernelEqReflTiming dagWs dag120
    assertTrue s!"kernel rfl dag120 took {nsDag / 1000000} ms (< 500 ms)" (nsDag < 500000000)

    -- 4. UNSAT via bvDecideQbe' upfront work sizing (attempts == 1)
    let bv32Ty := mkApp (mkConst ``BitVec) (mkNatLit 32)
    let propUnsat ← withLocalDeclD `x bv32Ty fun x =>
      withLocalDeclD `y bv32Ty fun y => do
        let one := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 32) (mkNatLit 1)
        let xXorY ← mkAppM ``HXor.hXor #[x, y]
        let xAndY ← mkAppM ``HAnd.hAnd #[x, y]
        let shl ← mkAppM ``HShiftLeft.hShiftLeft #[xAndY, one]
        let lhs ← mkAppM ``HAdd.hAdd #[xXorY, shl]
        let rhs ← mkAppM ``HAdd.hAdd #[x, y]
        mkForallFVars #[x, y] (← mkEq lhs rhs)
    let cfgNoPre : Lean.Elab.Tactic.BVDecide.BVDecideConfig :=
      { embeddedConstraintSubst := false, andFlattening := false }
    let resUnsat ← runMetaGoal propUnsat cfgNoPre
    match resUnsat with
    | .ok (.ok cres) =>
      match cres.proveResult? with
      | some pr =>
        assertTrue s!"attempts == 1 (got {pr.attempts})" (pr.attempts == 1)
        assertTrue "workBytesUsed >= minWorkBytes" (pr.workBytesUsed >= minWorkBytes)
      | none => throwError "expected proveResult? = some _"
    | .ok (.error _) => throwError "unexpected counterexample on UNSAT goal"
    | .error err => throwError "unexpected error on UNSAT goal: {err}"

    -- 5. SAT counterexample decoding & formatting (`x + 1#8 = 0#8` -> x = 255#8)
    let propSat ← mkTestBvForall 8 fun x => do
      let one := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 8) (mkNatLit 1)
      let zero := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 8) (mkNatLit 0)
      let sum ← mkAppM ``HAdd.hAdd #[x, one]
      pure (mkNot (← mkEq sum zero))
    match ← runMetaGoal propSat with
    | .ok (.error cex) =>
      assertTrue "SAT counterexample has 1 equation" (cex.equations.size == 1)
      assertTrue "SAT counterexample value == 255#8" (cex.equations[0]!.2.bv.toNat == 255)
      let msg ← cex.goal.withContext do (← explainCounterExampleQuality cex).toString
      assertTrue s!"formatted CEX contains 'counterexample': {msg}"
        (msg.contains "counterexample")
    | .ok (.ok _) => throwError "expected SAT counterexample, got UNSAT"
    | .error err => throwError "unexpected error on SAT goal: {err}"

    -- 6. UF SAT counterexample (`+uf` on `f x = f y`)
    let bv8Ty := mkApp (mkConst ``BitVec) (mkNatLit 8)
    let fnTy ← mkArrow bv8Ty bv8Ty
    let propUfSat ← withLocalDeclD `f fnTy fun f =>
      withLocalDeclD `x bv8Ty fun x =>
      withLocalDeclD `y bv8Ty fun y => do
        mkForallFVars #[f, x, y] (← mkEq (mkApp f x) (mkApp f y))
    match ← runMetaGoal propUfSat { uf := true } with
    | .ok (.error cex) =>
      assertTrue "UF SAT counterexample has functionAtoms" (!cex.functionAtoms.isEmpty)
    | .ok (.ok _) => throwError "expected UF SAT counterexample, got UNSAT"
    | .error err => throwError "unexpected error on UF SAT goal: {err}"

    -- 7. Injectable backend: 2x `.workTooSmall` retry escalation (1024 -> 16384 in 5 attempts)
    let mockRetryCtx : QbeContext := {
      initWorkOverride? := some 1024
      maxWorkBytes := 65536
      solveFn := fun _ work _ => if work < 16384 then .workTooSmall else .unsat
    }
    match ← runMetaGoal propUnsat cfgNoPre mockRetryCtx with
    | .ok (.ok cres) =>
      match cres.proveResult? with
      | some pr =>
        assertTrue s!"mock retry attempts == 5 (got {pr.attempts})" (pr.attempts == 5)
        assertTrue s!"mock retry work == 16384 (got {pr.workBytesUsed})"
          (pr.workBytesUsed == 16384)
      | none => throwError "expected proveResult?"
    | other => throwError "mock retry failed: {repr (other.map (fun _ => ()))}"

    -- 8. Real `solveDimacsBackend` retry fallback from 1024 B
    let realRetryCtx : QbeContext := {
      initWorkOverride? := some 1024
      solveFn := solveDimacsBackend
    }
    match ← runMetaGoal propUnsat cfgNoPre realRetryCtx with
    | .ok (.ok cres) =>
      match cres.proveResult? with
      | some pr =>
        assertTrue s!"real retry attempts > 1 (got {pr.attempts})" (pr.attempts > 1)
      | none => throwError "expected proveResult?"
    | _ => throwError "real solveDimacsBackend retry failed"

    -- 9. Corrupt SAT model rejected by `evalEfficient`
    let badSatCtx : QbeContext := {
      solveFn := fun _ _ _ => .sat (ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    }
    match ← runMetaGoal propSat {} badSatCtx with
    | .error msg =>
      assertTrue s!"evalEfficient rejection message: {msg}" (msg.contains "evalEfficient")
    | .ok _ => throwError "corrupt SAT model was not rejected"

    -- 10. `.unknown` and `.workTooSmall` error paths
    match ← runMetaGoal propUnsat cfgNoPre { solveFn := fun _ _ _ => .unknown } with
    | .error msg =>
      assertTrue s!"unknown message: {msg}" (msg.contains "unknown")
    | .ok _ => throwError ".unknown should fail"

    let oomCtx : QbeContext := {
      initWorkOverride? := some 1024
      maxWorkBytes := 4096
      solveFn := fun _ _ _ => .workTooSmall
    }
    match ← runMetaGoal propUnsat cfgNoPre oomCtx with
    | .error msg =>
      assertTrue s!"oom message: {msg}" (msg.contains "workspace limit")
    | .ok _ => throwError "exhausted workspace should fail"

  IO.println
    "UnitTest: ALL PASSED (theorems, +uf CEGAR, axioms, rfl <5ms, CEX, retry, evalEfficient)"

def runAll : IO Unit := do
  let opts : Options := {}
  let env ← importModules #[{ module := `BvDecideQbeTest.UnitTest }] opts
  let ctx : Core.Context := { fileName := "UnitTest.lean", fileMap := default }
  let ((), _) ← (runAllCore.toIO ctx { env := env })
  pure ()

#eval runAllCore

end BvDecideQbeTest.UnitTest

def main : IO Unit := BvDecideQbeTest.UnitTest.runAll
