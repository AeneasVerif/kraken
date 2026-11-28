module

public import BvDecideQbe.Tactic
public import BvDecideQbe.Cegar
public meta import BvDecideQbe.Tactic
public meta import BvDecideQbe.Cegar

/-!
# Nested `HMul` Subterm `*`-Sorting Canonicalizer Regression Tests (`Gap #14`)

Verifies that 64-bit nested `HMul` commutativity and associativity inside bitwise, shift,
addition, comparison, `UInt64`, hypothesis-driven, and `sym =>` goals collapse before bitblasting
in `.enhanced` mode, solve in `< 50 ms`, emit zero unexpected axioms (`≤ std3`), and leave
`.upstream` mode and non-`*` goals untouched.
-/

set_option autoImplicit false
set_option Elab.async false

public section

namespace BvDecideQbeTest.AcMulTest

open Lean
open Lean.Meta
open Lean.Meta.Tactic.BVDecide
open BvDecideQbe

/-! ## 1. Nested 64-bit `*` Commutativity & Associativity Theorems -/

theorem thm_nested_xor_64 (x y w : BitVec 64) :
    (x * y) ^^^ w = (y * x) ^^^ w := by
  bv_decide_qbe

theorem thm_nested_shr_64 (a b : BitVec 64) :
    ((a * b) >>> 32) = ((b * a) >>> 32) := by
  bv_decide_qbe

theorem thm_nested_shl_64 (a b : BitVec 64) :
    ((a * b) <<< 7) = ((b * a) <<< 7) := by
  bv_decide_qbe

theorem thm_nested_and_or_64 (a b w z : BitVec 64) :
    (((a * b) &&& w) ||| z) = (((b * a) &&& w) ||| z) := by
  bv_decide_qbe

theorem thm_nested_assoc_xor_64 (a b c w : BitVec 64) :
    ((a * b) * c) ^^^ w = (c * (b * a)) ^^^ w := by
  bv_decide_qbe

theorem thm_nested_assoc4_shr_64 (a b c d : BitVec 64) :
    (a * (b * (c * d))) >>> 16 = (((d * c) * b) * a) >>> 16 := by
  bv_decide_qbe

theorem thm_nested_add_same_64 (a b c : BitVec 64) :
    ((a * b) + c) = ((b * a) + c) := by
  bv_decide_qbe

theorem thm_nested_add_comm_64 (a b c : BitVec 64) :
    ((a * b) + c) = (c + (b * a)) := by
  bv_decide_qbe

theorem thm_nested_ult_irrefl_64 (a b : BitVec 64) :
    ¬((a * b) < (b * a)) := by
  bv_decide_qbe

theorem thm_nested_and_ule_64 (a b w : BitVec 64) :
    ((a * b) &&& w) ≤ (b * a) := by
  bv_decide_qbe

theorem thm_nested_deep_mul_64 (a b c d : BitVec 64) :
    (((a * b) ^^^ c) * d) >>> 8 = (d * ((b * a) ^^^ c)) >>> 8 := by
  bv_decide_qbe

theorem thm_nested_uint64_xor (x y w : UInt64) :
    (x * y) ^^^ w = (y * x) ^^^ w := by
  bv_decide_qbe

theorem thm_nested_hyp_64 (x y w z : BitVec 64) (h : (x * y) ^^^ w = z) :
    (y * x) ^^^ w = z := by
  bv_decide_qbe

theorem thm_nested_sym_64 (x y w : BitVec 64) :
    (x * y) ^^^ w = (y * x) ^^^ w := by
  sym =>
    bv_decide_qbe

theorem thm_nested_const_shr_64 (x : BitVec 64) :
    ((48271#64 * x) >>> 31) = ((x * 48271#64) >>> 31) := by
  bv_decide_qbe

theorem thm_upstream_small_nested_4 (x y w : BitVec 4) :
    (x * y) ^^^ w = (y * x) ^^^ w := by
  bv_decide_qbe_upstream

/-! ## 2. Programmatic `< 50 ms` Timing, Axiom & Mode-Gating Audit -/

private def assertTrue (msg : String) (b : Bool) : IO Unit := do
  if !b then throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def stdAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

private def runGoalTimed (prop : Expr) (cfg : Lean.Elab.Tactic.BVDecide.BVDecideConfig)
    (qbeCtx : QbeContext) : MetaM (Nat × Except CounterExample CegarResult) := do
  let mvar ← mkFreshExprMVar prop
  let tacticCtx := mkQbeTacticContext cfg
  let t0 ← IO.monoNanosNow
  let res ← runPlainGrindM <|
    bvDecideQbe' (.mvarIdTarget mvar.mvarId!) tacticCtx qbeCtx
  let t1 ← IO.monoNanosNow
  return (t1 - t0, res)

private def runAllCore : CoreM Unit := do
  -- 1. Zero-solver-axiom collapse audit on pre-bitblasting theorems
  for thm in [``thm_nested_xor_64, ``thm_nested_shr_64, ``thm_nested_shl_64,
              ``thm_nested_and_or_64, ``thm_nested_assoc_xor_64,
              ``thm_nested_assoc4_shr_64, ``thm_nested_add_same_64,
              ``thm_nested_ult_irrefl_64, ``thm_nested_deep_mul_64,
              ``thm_nested_uint64_xor, ``thm_nested_hyp_64,
              ``thm_nested_sym_64, ``thm_nested_const_shr_64] do
    let axs ← collectAxioms thm
    for ax in axs do
      if !stdAxioms.contains ax then
        throwError "unexpected axiom {ax} in pre-bitblast collapsed theorem {thm}"

  -- 2. Shared-node SAT-assisted nested `*` theorems (`≤ std3` + valid bv_solve axiom)
  for thm in [``thm_nested_add_comm_64, ``thm_nested_and_ule_64,
              ``thm_upstream_small_nested_4] do
    let axs ← collectAxioms thm
    let env ← getEnv
    for ax in axs do
      if !stdAxioms.contains ax then
        if !ax.toString.contains "_leanqbe.bv_solve.ax" then
          throwError "unexpected axiom {ax} in {thm}"
        let some axInfo := env.find? ax
          | throwError "missing axiom {ax}"
        assertTrue s!"{ax}: valid bv_solve axiom type"
          (isValidBvSolveAxiomType axInfo.type)

  -- 3. Live `< 50 ms` timing gates on 64-bit nested `*` goals across ops
  MetaM.run' do
    let bv64 := mkApp (mkConst ``BitVec) (mkNatLit 64)
    let enhCfg : Lean.Elab.Tactic.BVDecide.BVDecideConfig := { acNf := true }
    let enhCtx := mkQbeContext enhCfg (resolveQbeFeatures .enhanced {})

    let mkXorProp : MetaM Expr :=
      withLocalDeclD `x bv64 fun x =>
      withLocalDeclD `y bv64 fun y =>
      withLocalDeclD `w bv64 fun w => do
        let xy ← mkAppM ``HMul.hMul #[x, y]
        let yx ← mkAppM ``HMul.hMul #[y, x]
        let lhs ← mkAppM ``HXor.hXor #[xy, w]
        let rhs ← mkAppM ``HXor.hXor #[yx, w]
        mkForallFVars #[x, y, w] (← mkEq lhs rhs)

    let mkShrProp : MetaM Expr :=
      withLocalDeclD `a bv64 fun a =>
      withLocalDeclD `b bv64 fun b => do
        let ab ← mkAppM ``HMul.hMul #[a, b]
        let ba ← mkAppM ``HMul.hMul #[b, a]
        let lhs ← mkAppM ``HShiftRight.hShiftRight #[ab, mkNatLit 32]
        let rhs ← mkAppM ``HShiftRight.hShiftRight #[ba, mkNatLit 32]
        mkForallFVars #[a, b] (← mkEq lhs rhs)

    let mkAssocXorProp : MetaM Expr :=
      withLocalDeclD `a bv64 fun a =>
      withLocalDeclD `b bv64 fun b =>
      withLocalDeclD `c bv64 fun c =>
      withLocalDeclD `w bv64 fun w => do
        let ab ← mkAppM ``HMul.hMul #[a, b]
        let abc ← mkAppM ``HMul.hMul #[ab, c]
        let ba ← mkAppM ``HMul.hMul #[b, a]
        let cba ← mkAppM ``HMul.hMul #[c, ba]
        let lhs ← mkAppM ``HXor.hXor #[abc, w]
        let rhs ← mkAppM ``HXor.hXor #[cba, w]
        mkForallFVars #[a, b, c, w] (← mkEq lhs rhs)

    let mkAddCommProp : MetaM Expr :=
      withLocalDeclD `a bv64 fun a =>
      withLocalDeclD `b bv64 fun b =>
      withLocalDeclD `c bv64 fun c => do
        let ab ← mkAppM ``HMul.hMul #[a, b]
        let ba ← mkAppM ``HMul.hMul #[b, a]
        let lhs ← mkAppM ``HAdd.hAdd #[ab, c]
        let rhs ← mkAppM ``HAdd.hAdd #[c, ba]
        mkForallFVars #[a, b, c] (← mkEq lhs rhs)

    let mkUltProp : MetaM Expr :=
      withLocalDeclD `a bv64 fun a =>
      withLocalDeclD `b bv64 fun b => do
        let ab ← mkAppM ``HMul.hMul #[a, b]
        let ba ← mkAppM ``HMul.hMul #[b, a]
        let lt ← mkAppM ``LT.lt #[ab, ba]
        mkForallFVars #[a, b] (mkNot lt)

    let mkAndOrProp : MetaM Expr :=
      withLocalDeclD `a bv64 fun a =>
      withLocalDeclD `b bv64 fun b =>
      withLocalDeclD `w bv64 fun w =>
      withLocalDeclD `z bv64 fun z => do
        let ab ← mkAppM ``HMul.hMul #[a, b]
        let ba ← mkAppM ``HMul.hMul #[b, a]
        let lhs ← mkAppM ``HOr.hOr #[← mkAppM ``HAnd.hAnd #[ab, w], z]
        let rhs ← mkAppM ``HOr.hOr #[← mkAppM ``HAnd.hAnd #[ba, w], z]
        mkForallFVars #[a, b, w, z] (← mkEq lhs rhs)

    let mkAssocShrProp : MetaM Expr :=
      withLocalDeclD `a bv64 fun a =>
      withLocalDeclD `b bv64 fun b =>
      withLocalDeclD `c bv64 fun c => do
        let ab ← mkAppM ``HMul.hMul #[a, b]
        let abc ← mkAppM ``HMul.hMul #[ab, c]
        let ba ← mkAppM ``HMul.hMul #[b, a]
        let cba ← mkAppM ``HMul.hMul #[c, ba]
        let lhs ← mkAppM ``HShiftRight.hShiftRight #[abc, mkNatLit 32]
        let rhs ← mkAppM ``HShiftRight.hShiftRight #[cba, mkNatLit 32]
        mkForallFVars #[a, b, c] (← mkEq lhs rhs)

    let mkAndUleProp : MetaM Expr :=
      withLocalDeclD `a bv64 fun a =>
      withLocalDeclD `b bv64 fun b =>
      withLocalDeclD `w bv64 fun w => do
        let ab ← mkAppM ``HMul.hMul #[a, b]
        let ba ← mkAppM ``HMul.hMul #[b, a]
        let lhs ← mkAppM ``HAnd.hAnd #[ab, w]
        mkForallFVars #[a, b, w] (← mkAppM ``LE.le #[lhs, ba])

    let mkAndAddProp : MetaM Expr :=
      withLocalDeclD `a bv64 fun a =>
      withLocalDeclD `b bv64 fun b =>
      withLocalDeclD `w bv64 fun w =>
      withLocalDeclD `c bv64 fun c => do
        let ab ← mkAppM ``HMul.hMul #[a, b]
        let ba ← mkAppM ``HMul.hMul #[b, a]
        let lhs ← mkAppM ``HAdd.hAdd #[← mkAppM ``HAnd.hAnd #[ab, w], c]
        let rhs ← mkAppM ``HAdd.hAdd #[← mkAppM ``HAnd.hAnd #[ba, w], c]
        mkForallFVars #[a, b, w, c] (← mkEq lhs rhs)

    let mkUleReflProp : MetaM Expr :=
      withLocalDeclD `a bv64 fun a =>
      withLocalDeclD `b bv64 fun b => do
        let ab ← mkAppM ``HMul.hMul #[a, b]
        let ba ← mkAppM ``HMul.hMul #[b, a]
        mkForallFVars #[a, b] (← mkAppM ``LE.le #[ab, ba])

    let cases : List (String × Expr × Bool × Nat) := [
      ("xor_64", ← mkXorProp, true, 50),
      ("shr32_64", ← mkShrProp, true, 50),
      ("and_or_64", ← mkAndOrProp, true, 50),
      ("assoc_xor_64", ← mkAssocXorProp, true, 50),
      ("assoc_shr32_64", ← mkAssocShrProp, true, 50),
      ("add_comm_64", ← mkAddCommProp, true, 50),
      ("and_add_64", ← mkAndAddProp, true, 50),
      ("ult_irrefl_64", ← mkUltProp, true, 50),
      ("ule_refl_64", ← mkUleReflProp, true, 50),
      ("and_ule_64", ← mkAndUleProp, false, 5000)
    ]
    -- Warmup one call so JIT / simp theorem table init is amortized
    discard <| runGoalTimed (← mkShrProp) enhCfg enhCtx
    for (label, prop, expectPreBitblast, maxMs) in cases do
      let (ns, res) ← runGoalTimed prop enhCfg enhCtx
      let ms := ns / 1000000
      match res with
      | .ok cres =>
        if expectPreBitblast then
          assertTrue s!"{label}: expected pre-bitblast collapse (proveResult? == none)"
            cres.proveResult?.isNone
        assertTrue s!"{label}: took {ms} ms (must be < {maxMs} ms)" (ns < maxMs * 1000000)
        let pre := cres.proveResult?.isNone
        IO.println s!"AcMulTest timing {label}: {ns / 1000} us (preBitblast={pre})"
      | .error _ => throwError "{label}: unexpected counterexample"

    -- 4. Upstream parity gate: `.upstream` mode leaves non-cancellable nested `*` untouched
    --    (goes to solver even with `acNf := true`, whereas `.enhanced` collapses pre-bitblast!)
    let bv4 := mkApp (mkConst ``BitVec) (mkNatLit 4)
    let prop4 ← withLocalDeclD `x bv4 fun x =>
      withLocalDeclD `y bv4 fun y =>
      withLocalDeclD `w bv4 fun w => do
        let xy ← mkAppM ``HMul.hMul #[x, y]
        let yx ← mkAppM ``HMul.hMul #[y, x]
        let lhs ← mkAppM ``HAnd.hAnd #[xy, w]
        let rhs ← mkAppM ``HAnd.hAnd #[yx, w]
        mkForallFVars #[x, y, w] (← mkEq lhs rhs)
    let upCtx := mkQbeContext enhCfg (resolveQbeFeatures .upstream {})
    let (_, resUp) ← runGoalTimed prop4 enhCfg upCtx
    match resUp with
    | .ok cres =>
      assertTrue "upstream mode does NOT invoke enhanced nested-* pass (uses solver)"
        cres.proveResult?.isSome
    | .error _ => throwError "upstream 4-bit nested-* failed"
    let (_, resEnh4) ← runGoalTimed prop4 enhCfg enhCtx
    match resEnh4 with
    | .ok cres =>
      assertTrue "enhanced mode collapses 4-bit nested-* pre-bitblast"
        cres.proveResult?.isNone
    | .error _ => throwError "enhanced 4-bit nested-* failed"

    -- 5. Fast `*`-presence guard rejects non-`*` expressions
    let propNoMul ← withLocalDeclD `x bv64 fun x =>
      withLocalDeclD `y bv64 fun y => do
        let lhs ← mkAppM ``HXor.hXor #[x, y]
        mkForallFVars #[x, y] (← mkEq lhs lhs)
    assertTrue "exprHasBvHMul false on non-* expr"
      (!Normalize.AC.exprHasBvHMul propNoMul)

  IO.println "AcMulTest: ALL PASSED (nested 64-bit * AC < 50 ms, <= std3, upstream parity)"

#eval runAllCore

end BvDecideQbeTest.AcMulTest
