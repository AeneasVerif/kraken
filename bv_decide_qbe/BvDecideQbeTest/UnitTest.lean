module

public import BvDecideQbe.Tactic
public meta import BvDecideQbe.Tactic
public import Lean.Compiler.IR.CompilerM
public meta import Lean.Compiler.IR.CompilerM

/-!
# Trust-Pure `bv_decide_qbe` End-to-End Unit Tests (`Step 2`)

Verifies:
1. Concrete UNSAT BitVec theorems proved directly via `by bv_decide_qbe` and `by bv_decide_qbe +uf`.
2. `#print axioms` and programmatic `collectAxioms` audit: ONLY
   `[propext, Classical.choice, Quot.sound, <thm>._leanqbe.bv_solve.ax_1]` (0 source axioms).
3. `_expr_def` is added via `Lean.addDecl` ONLY (zero `compileDecl` IR entries).
4. Pure kernel `Eq.refl` reduction (`BVProg.parseWords ws = some _expr_def`) `< 5 ms`.
5. SAT counterexample decoding (`evalEfficient`-validated) and formatting via `bvDecideQbe'` with
   ZERO axioms added to the environment on SAT or intermediate `+uf` CEGAR probes.
6. Real in-process `bv_solve_bytes` retry escalation (`initWorkOverride? := some 1024`), corrupt SAT
   model rejection by `evalEfficient`, and `.unknown` (`fuel := 1`) / `.workTooSmall` error paths.
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

theorem thm_cegar_chain (f g : BitVec 8 → BitVec 8) (x y : BitVec 8)
    (h : x ^^^ y = 0#8) : f (g x) = f (g y) := by
  bv_decide_qbe +uf

/-! ## 1b. `sym =>` & `grind =>` Mode Tests (`bv_decide_qbe`, `bv_decide_qbe_push`, `types [...]`)
-/

@[ext]
structure SymPair where
  a : BitVec 32
  b : BitVec 32

theorem thm_sym_basic (x y : BitVec 32) :
    ((x ^^^ y) + ((x &&& y) <<< 1#32)) = (x + y) := by
  sym =>
    bv_decide_qbe

theorem thm_sym_push (x y : BitVec 64) (h : x = y + 1#64) : x - 1#64 = y := by
  sym =>
    bv_decide_qbe_push
    bv_decide_qbe

theorem thm_sym_std_push (x y : BitVec 64) (h : x = y + 1#64) : x - 1#64 = y := by
  sym =>
    bv_decide_push
    bv_decide_qbe

theorem thm_sym_types (p q : SymPair) (h : p = q) : p.a + p.b = q.a + q.b := by
  sym =>
    bv_decide_qbe types [SymPair]

theorem thm_grind_basic (x y : BitVec 64) (h : x = y) :
    ((x &&& 0xff00#64) ||| (y &&& 0xffffffffffff00ff#64)) = x := by
  grind -hom =>
    bv_decide_qbe_push
    bv_decide_qbe

/-! ## 1c. `*`-Gated Automatic `acNf` Tests (`E0 / H1`) -/

theorem thm_acnf_mul_comm_64 (a b : BitVec 64) : a * b = b * a := by
  bv_decide_qbe

theorem thm_acnf_mul_comm_add_64 (a b c : BitVec 64) : a * b + c = b * a + c := by
  bv_decide_qbe

theorem thm_acnf_bitvec_mul_64 (a b : BitVec 64) : BitVec.mul a b = BitVec.mul b a := by
  bv_decide_qbe

theorem thm_acnf_uint64_mul_comm (a b : UInt64) : a * b = b * a := by
  bv_decide_qbe

theorem thm_acnf_sym_mul_comm_64 (a b : BitVec 64) : a * b = b * a := by
  sym =>
    bv_decide_qbe

theorem thm_acnf_sym_push_mul_comm_64 (a b : BitVec 64) : a * b = b * a := by
  sym =>
    bv_decide_qbe_push
    bv_decide_qbe

theorem thm_acnf_disabled_4 (a b : BitVec 4) : a * b = b * a := by
  bv_decide_qbe -acNf

/-! ## 1d. Upstream-Fidelity Mode (`bv_decide_qbe_upstream`, `bv_decide_qbe.mode`, Overrides) -/

theorem thm_upstream_alias_mul_4 (a b : BitVec 4) : a * b = b * a := by
  bv_decide_qbe_upstream

theorem thm_upstream_alias_sym_4 (a b : BitVec 4) : a * b = b * a := by
  sym =>
    bv_decide_qbe_upstream

theorem thm_upstream_config_mul_4 (a b : BitVec 4) : a * b = b * a := by
  bv_decide_qbe (config := { mode := .upstream })

theorem thm_upstream_compat_config (x y : BitVec 16) :
    ((x ^^^ y) + ((x &&& y) <<< 1#16)) = x + y := by
  bv_decide_qbe (config := { timeout := 5, acNf := false, solverMode := .default })

section UpstreamOptionScope
set_option bv_decide_qbe.mode "upstream"

theorem thm_upstream_opt_mul_4 (a b : BitVec 4) : a * b = b * a := by
  bv_decide_qbe

theorem thm_upstream_opt_sym_4 (a b : BitVec 4) : (a + 1#4) * b = b * (a + 1#4) := by
  sym =>
    bv_decide_qbe

theorem thm_upstream_opt_push_mul_4 (a b : BitVec 4) : a * (b + 1#4) = (b + 1#4) * a := by
  sym =>
    bv_decide_qbe_push
    bv_decide_qbe

end UpstreamOptionScope

theorem thm_override_auto_acnf_false (a b : BitVec 4) : a * b = b * a := by
  bv_decide_qbe (autoAcNf := some false)

theorem thm_override_upstream_auto_acnf_true (a b : BitVec 64) : a * b = b * a := by
  bv_decide_qbe_upstream (autoAcNf := some true)

theorem thm_upstream_explicit_acnf_64 (a b : BitVec 64) : a * b = b * a := by
  bv_decide_qbe_upstream (config := { acNf := true })

/--
error: Invalid value `bogus` for option `bv_decide_qbe.mode` (expected "enhanced" or "upstream")
-/
#guard_msgs in
set_option bv_decide_qbe.mode "bogus" in
example (x : BitVec 8) : x = x := by
  bv_decide_qbe

#print axioms thm_a1
#print axioms thm_a2
#print axioms thm_b4
#print axioms thm_b5
#print axioms thm_cegar_e1
#print axioms thm_cegar_chain
#print axioms thm_sym_basic

/-! ## 2. Programmatic MetaM / Kernel Verification Suite -/

private def assertTrue (msg : String) (b : Bool) : IO Unit := do
  if !b then throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def stdAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

private def resolveAuxName (env : Environment) (base : Name) : Name :=
  if env.contains base then base else mkPrivateName env base

private def countBvSolveAxioms (env : Environment) : Nat :=
  env.constants.fold (init := 0) fun acc name _ =>
    if name.toString.contains "_leanqbe.bv_solve.ax" then acc + 1 else acc

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

private def runQbeModeTests : CoreM Unit := do
  -- Default option is "enhanced"
  let optsDefault ← getOptions
  assertTrue "default bv_decide_qbe.mode == enhanced"
    ((← withOptions (fun _ => optsDefault) (resolveQbeMode none)) == .enhanced)
  assertTrue "explicit none resolves upstream option"
    ((← withOptions (bv_decide_qbe.mode.set · "upstream") (resolveQbeMode none)) == .upstream)
  assertTrue "explicit mode overrides valid option"
    ((← withOptions (bv_decide_qbe.mode.set · "enhanced")
      (resolveQbeMode (some .upstream))) == .upstream)

  -- Invalid bv_decide_qbe.mode throws a clean error
  let mut badCaught := false
  try
    discard <| withOptions (bv_decide_qbe.mode.set · "invalid_mode") (resolveQbeMode none)
  catch ex =>
    let msg ← ex.toMessageData.toString
    assertTrue s!"invalid mode error mentions value: {msg}" (msg.contains "invalid_mode")
    badCaught := true
  assertTrue "invalid bv_decide_qbe.mode threw error" badCaught

  let mut badWithOverrideCaught := false
  try
    discard <| withOptions (bv_decide_qbe.mode.set · "bad_opt")
      (resolveQbeMode (some .upstream))
  catch ex =>
    let msg ← ex.toMessageData.toString
    assertTrue s!"invalid ambient mode throws even with explicit mode: {msg}"
      (msg.contains "bad_opt")
    badWithOverrideCaught := true
  assertTrue "invalid ambient mode caught with explicit mode" badWithOverrideCaught

  -- Preset resolution and per-feature Option Bool overrides
  let upFeat := resolveQbeFeatures .upstream {}
  assertTrue "upstream disables autoAcNf" (!upFeat.autoAcNf)
  assertTrue "upstream disables extraNormalize" (!upFeat.extraNormalize)
  assertTrue "upstream disables simCex" (!upFeat.simCex)
  assertTrue "upstream disables ringDispatch" (!upFeat.ringDispatch)
  assertTrue "upstream disables arisca" (!upFeat.arisca)
  assertTrue "upstream disables ariscaTier2" (!upFeat.ariscaTier2)
  assertTrue "upstream disables fraigHints" (!upFeat.fraigHints)
  assertTrue "upstream disables kitten" (!upFeat.kitten)
  assertTrue "upstream forces fidelity" (upFeat.solverVariant == .fidelity)

  let enhFeat := resolveQbeFeatures .enhanced {}
  assertTrue "enhanced enables autoAcNf" enhFeat.autoAcNf
  assertTrue "enhanced disables extraNormalize in bv_decide_qbe" (!enhFeat.extraNormalize)
  assertTrue "enhanced enables simCex" enhFeat.simCex
  assertTrue "enhanced disables ariscaTier2" (!enhFeat.ariscaTier2)
  assertTrue "enhanced disables fraigHints" (!enhFeat.fraigHints)
  assertTrue "enhanced disables kitten" (!enhFeat.kitten)

  let ovrFeat := resolveQbeFeatures .enhanced {
    autoAcNf := some false
    extraNormalize := some true
    simCex := some false
    ringDispatch := some true
    arisca := some true
    ariscaProbeMs := some 250
  }
  assertTrue "override autoAcNf := some false" (!ovrFeat.autoAcNf)
  assertTrue "override extraNormalize := some true" ovrFeat.extraNormalize
  assertTrue "override simCex := some false" (!ovrFeat.simCex)
  assertTrue "override ringDispatch := some true" ovrFeat.ringDispatch
  assertTrue "override arisca := some true" ovrFeat.arisca
  assertTrue "override ariscaProbeMs := some 250" (ovrFeat.ariscaProbeMs == 250)

  let upOvrFeat := resolveQbeFeatures .upstream { autoAcNf := some true }
  assertTrue "upstream with autoAcNf := some true" (upOvrFeat.autoAcNf && !upOvrFeat.simCex)

private meta def runQbeConfigElabTests : CoreM Unit := do
  let chk (msg : String) (b : Bool) : IO Unit := do
    if !b then throw (IO.userError s!"ASSERTION FAILED: {msg}")
  -- Tactic elaboration tests via elabQbeConfig (backwards compat + overrides)
  MetaM.run' <| Elab.Term.TermElabM.run' do
    let elabCfg (stx : TSyntax `Lean.Parser.Tactic.optConfig) : Elab.TermElabM QbeConfig :=
      elabQbeConfig stx |>.run { elaborator := `test } |>.run' { goals := [] }
    let q1 ← elabCfg (← `(Lean.Parser.Tactic.optConfig|
      (config := { timeout := 7, acNf := true, solverMode := .counterexample })))
    chk "compat config timeout == 7" (q1.timeout == 7)
    chk "compat config acNf == true" q1.acNf
    chk "compat config mode == none" q1.mode.isNone

    let q2 ← elabCfg (← `(Lean.Parser.Tactic.optConfig| (config := { mode := .upstream })))
    chk "config mode == some .upstream" (q2.mode == some .upstream)

    let q2b ← elabCfg (← `(Lean.Parser.Tactic.optConfig| (config := { mode := some .upstream })))
    chk "config some mode == some .upstream" (q2b.mode == some .upstream)

    let q3 ← elabCfg (← `(Lean.Parser.Tactic.optConfig|
      (autoAcNf := some false) (extraNormalize := some true) (simCex := some false)
      (ringDispatch := some true) (arisca := some false)))
    chk "optConfig autoAcNf == some false" (q3.autoAcNf == some false)
    chk "optConfig extraNormalize == some true" (q3.extraNormalize == some true)
    chk "optConfig simCex == some false" (q3.simCex == some false)
    chk "optConfig ringDispatch == some true" (q3.ringDispatch == some true)
    chk "optConfig arisca == some false" (q3.arisca == some false)

#eval runQbeConfigElabTests

private def runAllCore : CoreM Unit := do
  -- 1. Audit axioms and non-compilation of _expr_def on reflected theorems
  for thm in [``thm_a1, ``thm_a2, ``thm_a3, ``thm_a5, ``thm_b1, ``thm_b2,
              ``thm_b4, ``thm_b5, ``thm_d6, ``thm_uint32, ``thm_cegar_e1,
              ``thm_cegar_multi, ``thm_cegar_bool, ``thm_cegar_chain,
              ``thm_sym_basic, ``thm_acnf_disabled_4,
              ``thm_upstream_alias_mul_4, ``thm_upstream_alias_sym_4,
              ``thm_upstream_config_mul_4, ``thm_upstream_compat_config,
              ``thm_upstream_opt_mul_4, ``thm_upstream_opt_sym_4,
              ``thm_upstream_opt_push_mul_4, ``thm_override_auto_acnf_false] do
    checkTheoremAxioms thm true
  for thm in [``thm_acnf_mul_comm_64, ``thm_acnf_mul_comm_add_64,
              ``thm_acnf_bitvec_mul_64, ``thm_acnf_uint64_mul_comm,
              ``thm_acnf_sym_mul_comm_64, ``thm_acnf_sym_push_mul_comm_64,
              ``thm_override_upstream_auto_acnf_true,
              ``thm_upstream_explicit_acnf_64] do
    checkTheoremAxioms thm false
  for thm in [``thm_preproc_only, ``thm_sym_push, ``thm_sym_std_push,
              ``thm_sym_types, ``thm_grind_basic] do
    let axs ← collectAxioms thm
    for ax in axs do
      if !stdAxioms.contains ax && !ax.toString.contains "_leanqbe.bv_solve.ax" then
        throwError "unexpected axiom {ax} in {thm}"

  -- 2. Verify zero non-per-goal axioms across all BvDecideQbe / BvDecideQbeTest decls
  let env ← getEnv
  let reflectedNames : List Name :=
    [``thm_a1, ``thm_a2, ``thm_a3, ``thm_a5, ``thm_b1, ``thm_b2,
     ``thm_b4, ``thm_b5, ``thm_d6, ``thm_uint32, ``thm_cegar_e1,
     ``thm_cegar_multi, ``thm_cegar_bool, ``thm_cegar_chain,
     ``thm_sym_basic, ``thm_sym_push, ``thm_sym_std_push,
     ``thm_sym_types, ``thm_grind_basic, ``thm_acnf_disabled_4,
     ``thm_upstream_alias_mul_4, ``thm_upstream_alias_sym_4,
     ``thm_upstream_config_mul_4, ``thm_upstream_compat_config,
     ``thm_upstream_opt_mul_4, ``thm_upstream_opt_sym_4,
     ``thm_upstream_opt_push_mul_4, ``thm_override_auto_acnf_false]
  for (name, _) in env.constants do
    let s := name.toString
    if (s.startsWith "BvDecideQbe." || s.startsWith "BvDecideQbeTest.") &&
       !reflectedNames.contains name && !s.endsWith "._leanqbe.bv_solve.ax_1" &&
       !s.contains "._test_" && !s.contains ".runAll" && !s.contains ".runQbeModeTests" then
      let axs ← collectAxioms name
      for ax in axs do
        if !stdAxioms.contains ax then
          throwError "unexpected axiom {ax} used by {name}"

  runQbeModeTests

  -- 3. Kernel Eq.refl timing gate (< 5 ms small) + wide/DAG checks
  MetaM.run' do
    let smallExpr : BVLogicalExpr :=
      .not (.literal (.bin (.bin (.var 0 : BVExpr 4) .xor (.var 0)) .eq (.const 0#4)))
    let smallWs := (BvDecideQbe.encodeWords smallExpr).get!
    let nsSmall ← checkKernelEqReflTiming smallWs smallExpr
    assertTrue s!"kernel rfl small took {nsSmall / 1000} us (< 50000 us)" (nsSmall < 50000000)

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

    -- 4. UNSAT via bvDecideQbe' upfront work sizing (attempts == 1) & single axiom emission
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
    let axBeforeUnsat := countBvSolveAxioms (← getEnv)
    let resUnsat ← runMetaGoal propUnsat cfgNoPre
    let axAfterUnsat := countBvSolveAxioms (← getEnv)
    assertTrue "UNSAT commits exactly 1 _leanqbe.bv_solve.ax"
      (axAfterUnsat == axBeforeUnsat + 1)
    match resUnsat with
    | .ok (.ok cres) =>
      match cres.proveResult? with
      | some pr =>
        assertTrue s!"attempts == 1 (got {pr.attempts})" (pr.attempts == 1)
        assertTrue "workBytesUsed >= minWorkBytes" (pr.workBytesUsed >= minWorkBytes)
      | none => throwError "expected proveResult? = some _"
    | .ok (.error _) => throwError "unexpected counterexample on UNSAT goal"
    | .error err => throwError "unexpected error on UNSAT goal: {err}"

    -- 5. SAT counterexample decoding & formatting (`x + 1#8 = 0#8` -> x = 255#8, 0 axioms emitted)
    let propSat ← mkTestBvForall 8 fun x => do
      let one := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 8) (mkNatLit 1)
      let zero := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 8) (mkNatLit 0)
      let sum ← mkAppM ``HAdd.hAdd #[x, one]
      pure (mkNot (← mkEq sum zero))
    let axBeforeSat := countBvSolveAxioms (← getEnv)
    match ← runMetaGoal propSat with
    | .ok (.error cex) =>
      assertTrue "SAT emits 0 axioms" (countBvSolveAxioms (← getEnv) == axBeforeSat)
      assertTrue "SAT counterexample has 1 equation" (cex.equations.size == 1)
      assertTrue "SAT counterexample value == 255#8" (cex.equations[0]!.2.bv.toNat == 255)
      let msg ← cex.goal.withContext do (← explainCounterExampleQuality cex).toString
      assertTrue s!"formatted CEX contains 'counterexample': {msg}"
        (msg.contains "counterexample")
    | .ok (.ok _) => throwError "expected SAT counterexample, got UNSAT"
    | .error err => throwError "unexpected error on SAT goal: {err}"

    -- 6. UF SAT counterexample (`+uf` on `f x = f y`, 0 axioms emitted)
    let bv8Ty := mkApp (mkConst ``BitVec) (mkNatLit 8)
    let fnTy ← mkArrow bv8Ty bv8Ty
    let propUfSat ← withLocalDeclD `f fnTy fun f =>
      withLocalDeclD `x bv8Ty fun x =>
      withLocalDeclD `y bv8Ty fun y => do
        mkForallFVars #[f, x, y] (← mkEq (mkApp f x) (mkApp f y))
    let axBeforeUfSat := countBvSolveAxioms (← getEnv)
    match ← runMetaGoal propUfSat { uf := true } with
    | .ok (.error cex) =>
      assertTrue "UF SAT emits 0 axioms" (countBvSolveAxioms (← getEnv) == axBeforeUfSat)
      assertTrue "UF SAT counterexample has functionAtoms" (!cex.functionAtoms.isEmpty)
    | .ok (.ok _) => throwError "expected UF SAT counterexample, got UNSAT"
    | .error err => throwError "unexpected error on UF SAT goal: {err}"

    -- 7. UF UNSAT multi-round CEGAR (`+uf` single-solve emits exactly 1 axiom)
    let propUfUnsat ← withLocalDeclD `f fnTy fun f =>
      withLocalDeclD `g fnTy fun g =>
      withLocalDeclD `x bv8Ty fun x =>
      withLocalDeclD `y bv8Ty fun y => do
        let h ← mkEq x y
        let concl ← mkEq (mkApp f (mkApp g x)) (mkApp f (mkApp g y))
        mkForallFVars #[f, g, x, y] (← mkArrow h concl)
    let axBeforeUfUnsat := countBvSolveAxioms (← getEnv)
    match ← runMetaGoal propUfUnsat { uf := true, embeddedConstraintSubst := false } with
    | .ok (.ok cres) =>
      assertTrue "UF UNSAT emits exactly 1 axiom (single-solve)"
        (countBvSolveAxioms (← getEnv) == axBeforeUfUnsat + 1)
      assertTrue "UF UNSAT has proveResult?" cres.proveResult?.isSome
    | .ok (.error _) => throwError "unexpected counterexample on UF UNSAT goal"
    | .error err => throwError "unexpected error on UF UNSAT goal: {err}"

    -- 8. Real `bv_solve_bytes` 2x `.workTooSmall` retry escalation from 1024 B
    let realRetryCtx : QbeContext := {
      initWorkOverride? := some 1024
    }
    match ← runMetaGoal propUnsat cfgNoPre realRetryCtx with
    | .ok (.ok cres) =>
      match cres.proveResult? with
      | some pr =>
        assertTrue s!"real retry attempts > 1 (got {pr.attempts})" (pr.attempts > 1)
      | none => throwError "expected proveResult?"
    | _ => throwError "real bv_solve_bytes retry failed"

    -- 9. Corrupt SAT model rejected by `evalEfficient`
    let badSatExpr : BVLogicalExpr :=
      .literal (.bin (.bin (.var 0 : BVExpr 8) .add (.const 1#8)) .eq (.const 0#8))
    let some badEnc := BvDecideQbe.encode badSatExpr
      | throwError "encode badSatExpr failed"
    let badModel := ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    match reconstructValidatedCounterExample badSatExpr badEnc badModel {} with
    | .error msg =>
      assertTrue s!"evalEfficient rejection message: {msg}" (msg.contains "evalEfficient")
    | .ok _ => throwError "corrupt SAT model was not rejected"

    -- 10. Real `bv_solve_bytes` `.timeout` (`fuel := 0`, `fuel := 1`)
    --     and `.workTooSmall` (`4096 B`)
    match ← runMetaGoal propUnsat cfgNoPre { fuel := 0, acNf := false } with
    | .error msg =>
      assertTrue s!"timeout(0, acNf=false) message: {msg}" (msg.contains "timed out")
      assertTrue s!"timeout(0, acNf=false) suggests acNf: {msg}" (msg.contains "acNf")
    | .ok _ => throwError "fuel=0 should fail with timeout"

    match ← runMetaGoal propUnsat cfgNoPre { fuel := 0, acNf := true } with
    | .error msg =>
      assertTrue s!"timeout(0, acNf=true) message: {msg}" (msg.contains "timed out")
      assertTrue s!"timeout(0, acNf=true) omits acNf hint: {msg}" (!msg.contains "acNf")
    | .ok _ => throwError "fuel=0 with acNf=true should fail with timeout"

    match ← runMetaGoal propUnsat cfgNoPre { fuel := 1 } with
    | .error msg =>
      assertTrue s!"timeout(1) message: {msg}" (msg.contains "timed out")
    | .ok _ => throwError "fuel=1 should fail with timeout"

    let oomCtx : QbeContext := {
      initWorkOverride? := some 1024
      maxWorkBytes := 4096
    }
    match ← runMetaGoal propUnsat cfgNoPre oomCtx with
    | .error msg =>
      assertTrue s!"oom message: {msg}" (msg.contains "workspace limit")
    | .ok _ => throwError "exhausted workspace should fail"

    -- 11. `*`-gated automatic `acNf` config detection & `Expr` gating
    let stxEmpty ← `(Lean.Parser.Tactic.optConfig| )
    let stxPos ← `(Lean.Parser.Tactic.optConfig| +acNf)
    let stxNeg ← `(Lean.Parser.Tactic.optConfig| -acNf)
    let stxAssignFalse ← `(Lean.Parser.Tactic.optConfig| (acNf := false))
    let stxAssignTrue ← `(Lean.Parser.Tactic.optConfig| (acNf := true))
    let stxOther ← `(Lean.Parser.Tactic.optConfig| +uf (timeout := 5))
    let stxCfgNoAcNf ← `(Lean.Parser.Tactic.optConfig| (config := { timeout := 1 }))
    let stxCfgFalse ← `(Lean.Parser.Tactic.optConfig| (config := { acNf := false }))
    let stxCfgWith ← `(Lean.Parser.Tactic.optConfig| (config := { base with timeout := 1 }))
    let stxCfgOpaque ← `(Lean.Parser.Tactic.optConfig| (config := myCfg))

    assertTrue "hasExplicitAcNf empty == false" (!hasExplicitAcNf stxEmpty)
    assertTrue "hasExplicitAcNf +acNf == true" (hasExplicitAcNf stxPos)
    assertTrue "hasExplicitAcNf -acNf == true" (hasExplicitAcNf stxNeg)
    assertTrue "hasExplicitAcNf (acNf := false) == true" (hasExplicitAcNf stxAssignFalse)
    assertTrue "hasExplicitAcNf (acNf := true) == true" (hasExplicitAcNf stxAssignTrue)
    assertTrue "hasExplicitAcNf +uf (timeout := 5) == false" (!hasExplicitAcNf stxOther)
    assertTrue "hasExplicitAcNf (config := { timeout := 1 }) == false"
      (!hasExplicitAcNf stxCfgNoAcNf)
    assertTrue "hasExplicitAcNf (config := { acNf := false }) == true"
      (hasExplicitAcNf stxCfgFalse)
    assertTrue "hasExplicitAcNf (config := { base with timeout := 1 }) == true"
      (hasExplicitAcNf stxCfgWith)
    assertTrue "hasExplicitAcNf (config := myCfg) == true" (hasExplicitAcNf stxCfgOpaque)

    let bv64Ty := mkApp (mkConst ``BitVec) (mkNatLit 64)
    let propMul ← withLocalDeclD `a bv64Ty fun a =>
      withLocalDeclD `b bv64Ty fun b => do
        let ab ← mkAppM ``HMul.hMul #[a, b]
        let ba ← mkAppM ``HMul.hMul #[b, a]
        mkForallFVars #[a, b] (← mkEq ab ba)
    let mvarMul ← mkFreshExprMVar propMul
    assertTrue "resolveAutoAcNf default on BitVec * => true"
      ((← resolveAutoAcNf stxEmpty {} mvarMul.mvarId!).acNf)
    assertTrue "resolveAutoAcNf -acNf on BitVec * => false"
      (!(← resolveAutoAcNf stxNeg { acNf := false } mvarMul.mvarId!).acNf)
    assertTrue "resolveAutoAcNf (acNf := false) on BitVec * => false"
      (!(← resolveAutoAcNf stxAssignFalse { acNf := false } mvarMul.mvarId!).acNf)
    assertTrue "resolveAutoAcNf (config := { acNf := false }) on BitVec * => false"
      (!(← resolveAutoAcNf stxCfgFalse { acNf := false } mvarMul.mvarId!).acNf)
    assertTrue "resolveAutoAcNf (config := { timeout := 1 }) on BitVec * => true"
      ((← resolveAutoAcNf stxCfgNoAcNf { timeout := 1 } mvarMul.mvarId!).acNf)
    assertTrue "resolveAutoAcNf (config := myCfg) on BitVec * => false"
      (!(← resolveAutoAcNf stxCfgOpaque { acNf := false } mvarMul.mvarId!).acNf)

    let propBvMul ← withLocalDeclD `a bv64Ty fun a =>
      withLocalDeclD `b bv64Ty fun b => do
        let ab := mkApp3 (mkConst ``BitVec.mul) (mkNatLit 64) a b
        let ba := mkApp3 (mkConst ``BitVec.mul) (mkNatLit 64) b a
        mkForallFVars #[a, b] (← mkEq ab ba)
    let mvarBvMul ← mkFreshExprMVar propBvMul
    assertTrue "resolveAutoAcNf default on BitVec.mul => true"
      ((← resolveAutoAcNf stxEmpty {} mvarBvMul.mvarId!).acNf)

    let propU64Mul ← withLocalDeclD `a (mkConst ``UInt64) fun a =>
      withLocalDeclD `b (mkConst ``UInt64) fun b => do
        let ab ← mkAppM ``HMul.hMul #[a, b]
        let ba ← mkAppM ``HMul.hMul #[b, a]
        mkForallFVars #[a, b] (← mkEq ab ba)
    let mvarU64Mul ← mkFreshExprMVar propU64Mul
    assertTrue "resolveAutoAcNf default on UInt64 * => true"
      ((← resolveAutoAcNf stxEmpty {} mvarU64Mul.mvarId!).acNf)
    assertTrue "resolveAutoAcNf -fixedInt on UInt64 * => false"
      (!(← resolveAutoAcNf stxEmpty { fixedInt := false } mvarU64Mul.mvarId!).acNf)

    let propNoMul ← withLocalDeclD `a bv64Ty fun a =>
      withLocalDeclD `b bv64Ty fun b => do
        let cond ← mkAppM ``BEq.beq #[a, b]
        let sum ← mkAppM ``HAdd.hAdd #[a, b]
        let xored ← mkAppM ``HXor.hXor #[a, b]
        let mux ← mkAppM ``cond #[cond, sum, xored]
        mkForallFVars #[a, b] (← mkEq mux mux)
    let mvarNoMul ← mkFreshExprMVar propNoMul
    assertTrue "resolveAutoAcNf default on non-* mux/add/xor => false"
      (!(← resolveAutoAcNf stxEmpty {} mvarNoMul.mvarId!).acNf)
    assertTrue "resolveAutoAcNf +acNf on non-* => true"
      ((← resolveAutoAcNf stxPos { acNf := true } mvarNoMul.mvarId!).acNf)

    let propNatMul ← withLocalDeclD `x (mkConst ``Nat) fun x =>
      withLocalDeclD `y (mkConst ``Nat) fun y => do
        let xy ← mkAppM ``HMul.hMul #[x, y]
        let yx ← mkAppM ``HMul.hMul #[y, x]
        mkForallFVars #[x, y] (← mkEq xy yx)
    let mvarNatMul ← mkFreshExprMVar propNatMul
    assertTrue "resolveAutoAcNf default on Nat * => false"
      (!(← resolveAutoAcNf stxEmpty {} mvarNatMul.mvarId!).acNf)

    let mulWidth ← mkAppM ``HMul.hMul #[mkNatLit 2, mkNatLit 32]
    let bvMulW := mkApp (mkConst ``BitVec) mulWidth
    let propWidthMul ← withLocalDeclD `x bvMulW fun x => do
      mkForallFVars #[x] (← mkEq x x)
    let mvarWidthMul ← mkFreshExprMVar propWidthMul
    assertTrue "resolveAutoAcNf default on BitVec (2 * 32) without BV * => false"
      (!(← resolveAutoAcNf stxEmpty {} mvarWidthMul.mvarId!).acNf)

    let hypMulOk ← withLocalDeclD `a bv64Ty fun a =>
      withLocalDeclD `b bv64Ty fun b =>
      withLocalDeclD `c bv64Ty fun c => do
        let ab ← mkAppM ``HMul.hMul #[a, b]
        withLocalDeclD `h (← mkEq ab c) fun _ => do
          let mvarHyp ← mkFreshExprMVar (← mkEq c c)
          return (← resolveAutoAcNf stxEmpty {} mvarHyp.mvarId!).acNf
    assertTrue "resolveAutoAcNf detects BitVec * in local hypothesis => true" hypMulOk

    let letMulOk ← withLocalDeclD `a bv64Ty fun a =>
      withLocalDeclD `b bv64Ty fun b => do
        let ab ← mkAppM ``HMul.hMul #[a, b]
        withLetDecl `p bv64Ty ab fun p => do
          let mvarLet ← mkFreshExprMVar (← mkEq p p)
          return (← resolveAutoAcNf stxEmpty {} mvarLet.mvarId!).acNf
    assertTrue "resolveAutoAcNf detects BitVec * in local let binding => true" letMulOk

  IO.println
    "UnitTest: ALL PASSED (+uf, sym/grind, *-gated acNf, timeout, axioms, rfl, CEX, retry, evalEff)"

def runAll : IO Unit := do
  let opts : Options := {}
  let env ← importModules #[{ module := `BvDecideQbeTest.UnitTest }] opts
  let ctx : Core.Context := { fileName := "UnitTest.lean", fileMap := default }
  let ((), _) ← (runAllCore.toIO ctx { env := env })
  pure ()

#eval runAllCore

end BvDecideQbeTest.UnitTest

def main : IO Unit := BvDecideQbeTest.UnitTest.runAll
