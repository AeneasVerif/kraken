module

public import BvDecideQbe.Tactic
public import BvDecideQbe.Cegar
public meta import BvDecideQbe.Tactic
public meta import BvDecideQbe.Cegar

/-!
# Lightweight Batched UF Congruence & McCarthy Array ROW Regression Tests (`Gap #15`)

Verifies:
1. Batched & top-down cascading UF congruence cuts multi-round CEGAR chains and iterated UF
   (`f^6 x = f^6 y`, 6-deep chains, diamonds, wide parallel UF) down to minimal rounds.
2. Kernel-proved McCarthy array read-over-write (`Array.{set,setIfInBounds,set!}`,
   `Vector.{set,setIfInBounds,set!}`, `List.set`, `Std.HashMap.{insert,getD}`) and
   `BitVec.toNat` read congruence solve single-write, chained-write, `BitVec`, and `Bool` array
   goals under `bv_decide_qbe +uf`.
3. SAT goals (both UF chains and array read-over-write) cleanly return counterexamples with `0`
   emitted axioms, `.upstream` mode preserves upstream CEGAR parity, and all theorems depend only
   on `≤ std3` + valid `_leanqbe.bv_solve.ax`.
-/

set_option autoImplicit false
set_option Elab.async false

public section

namespace BvDecideQbeTest.CegarEnhanceTest

open Lean
open Lean.Meta
open Lean.Meta.Tactic.BVDecide
open BvDecideQbe

/-! ## 1. Batched & Cascading UF Congruence Theorems -/

theorem thm_uf_chain6_64 (f1 f2 f3 f4 f5 f6 : BitVec 64 → BitVec 64) (x y : BitVec 64)
    (h : x + 1#64 = y + 1#64) :
    f1 (f2 (f3 (f4 (f5 (f6 x))))) = f1 (f2 (f3 (f4 (f5 (f6 y))))) := by
  bv_decide_qbe +uf

theorem thm_uf_iter6_64 (f : BitVec 64 → BitVec 64) (x y : BitVec 64)
    (h : x ^^^ y = 0#64) :
    f (f (f (f (f (f x))))) = f (f (f (f (f (f y))))) := by
  bv_decide_qbe +uf

theorem thm_uf_diamond_32 (f : BitVec 32 → BitVec 32 → BitVec 32)
    (g1 g2 : BitVec 32 → BitVec 32) (x y : BitVec 32)
    (h : x ^^^ y = 0#32) :
    f (g1 x) (g2 x) = f (g1 y) (g2 y) := by
  bv_decide_qbe +uf

theorem thm_uf_wide_parallel_32 (f : BitVec 32 → BitVec 32)
    (x1 y1 x2 y2 x3 y3 x4 y4 : BitVec 32)
    (h1 : x1 ^^^ y1 = 0#32) (h2 : x2 ^^^ y2 = 0#32)
    (h3 : x3 ^^^ y3 = 0#32) (h4 : x4 ^^^ y4 = 0#32) :
    f x1 + f x2 + f x3 + f x4 = f y1 + f y2 + f y3 + f y4 := by
  bv_decide_qbe +uf

theorem thm_uf_bridge_m0_e2 (f g : BitVec 32 → BitVec 32) (x y z : BitVec 32)
    (h1 : x ≤ y) (h2 : y ≤ x) (h3 : f x = z) :
    g (f y) = g z := by
  bv_decide_qbe +uf

/-! ## 2. McCarthy Array Read-Over-Write & Read Congruence Theorems -/

theorem thm_vec_row_same_64 (reg : Vector (BitVec 64) 32) (i j : BitVec 5) (v : BitVec 64)
    (h : i + 1#5 = j + 1#5) :
    (reg.set i.toNat v i.isLt)[j.toNat]'j.isLt = v := by
  bv_decide_qbe +uf

theorem thm_vec_row_diff_64 (reg : Vector (BitVec 64) 32) (i j : BitVec 5) (v : BitVec 64)
    (h : (i ^^^ j) ≠ 0#5) :
    (reg.set i.toNat v i.isLt)[j.toNat]'j.isLt = reg[j.toNat]'j.isLt := by
  bv_decide_qbe +uf

theorem thm_vec_row_ite_64 (reg : Vector (BitVec 64) 32) (i j : BitVec 5) (v : BitVec 64) :
    (reg.set i.toNat v i.isLt)[j.toNat]'j.isLt =
      (bif i == j then v else reg[j.toNat]'j.isLt) := by
  bv_decide_qbe +uf

theorem thm_vec_row_setIfInBounds_32 (reg : Vector (BitVec 32) 16)
    (i j : BitVec 4) (v : BitVec 32) :
    (reg.setIfInBounds i.toNat v)[j.toNat]'j.isLt =
      (bif i == j then v else reg[j.toNat]'j.isLt) := by
  bv_decide_qbe +uf

theorem thm_vec_row_setBang_32 (reg : Vector (BitVec 32) 16)
    (i j : BitVec 4) (v : BitVec 32) :
    (reg.set! i.toNat v)[j.toNat]'j.isLt =
      (bif i == j then v else reg[j.toNat]'j.isLt) := by
  bv_decide_qbe +uf

theorem thm_vec_row_chain3_32 (reg : Vector (BitVec 32) 16)
    (i1 i2 i3 j : BitVec 4) (v1 v2 v3 : BitVec 32)
    (h3 : j ≠ i3) (h2 : j ≠ i2) (h1 : (j ^^^ i1) = 0#4) :
    let r1 := reg.set i1.toNat v1 i1.isLt
    let r2 := r1.set i2.toNat v2 i2.isLt
    let r3 := r2.set i3.toNat v3 i3.isLt
    r3[j.toNat]'j.isLt = v1 := by
  bv_decide_qbe +uf

theorem thm_vec_bool_row_16 (flags : Vector Bool 16) (i j : BitVec 4) (b : Bool)
    (h : (i ^^^ j) = 0#4) :
    (flags.set i.toNat b i.isLt)[j.toNat]'j.isLt = b := by
  bv_decide_qbe +uf

theorem thm_vec_read_congr_64 (reg : Vector (BitVec 64) 32) (i j : BitVec 5)
    (h : (i ^^^ j) = 0#5) :
    reg[i.toNat]'i.isLt = reg[j.toNat]'j.isLt := by
  bv_decide_qbe +uf

theorem thm_arr_row_same_32 (arr : Array (BitVec 32)) (i j : BitVec 8) (v : BitVec 32)
    (hi : i.toNat < arr.size) (hj : j.toNat < (arr.set i.toNat v hi).size)
    (h : (i ^^^ j) = 0#8) :
    (arr.set i.toNat v hi)[j.toNat]'hj = v := by
  bv_decide_qbe +uf

theorem thm_arr_row_diff_32 (arr : Array (BitVec 32)) (i j : BitVec 8) (v : BitVec 32)
    (hi : i.toNat < arr.size) (hj0 : j.toNat < arr.size)
    (hj : j.toNat < (arr.set i.toNat v hi).size) (h : i ≠ j) :
    (arr.set i.toNat v hi)[j.toNat]'hj = arr[j.toNat]'hj0 := by
  bv_decide_qbe +uf

theorem thm_arr_row_setIfInBounds_32 (arr : Array (BitVec 32)) (i j : BitVec 8) (v : BitVec 32)
    (hj0 : j.toNat < arr.size) (hj : j.toNat < (arr.setIfInBounds i.toNat v).size) :
    (arr.setIfInBounds i.toNat v)[j.toNat]'hj =
      (bif i == j then v else arr[j.toNat]'hj0) := by
  bv_decide_qbe +uf

theorem thm_arr_row_setBang_32 (arr : Array (BitVec 32)) (i j : BitVec 8) (v : BitVec 32)
    (hj0 : j.toNat < arr.size) (hj : j.toNat < (arr.set! i.toNat v).size) :
    (arr.set! i.toNat v)[j.toNat]'hj =
      (bif i == j then v else arr[j.toNat]'hj0) := by
  bv_decide_qbe +uf

theorem thm_list_row_ite_32 (xs : List (BitVec 32)) (i j : BitVec 8) (v : BitVec 32)
    (hj0 : j.toNat < xs.length) (hj : j.toNat < (xs.set i.toNat v).length) :
    (xs.set i.toNat v)[j.toNat]'hj =
      (bif i == j then v else xs[j.toNat]'hj0) := by
  bv_decide_qbe +uf

theorem thm_hm_row_ite_64 (m : Std.HashMap (BitVec 64) (BitVec 64)) (i j v d : BitVec 64) :
    (m.insert i v).getD j d = (bif i == j then v else m.getD j d) := by
  bv_decide_qbe +uf

theorem thm_hm_row_chain2_64 (m : Std.HashMap (BitVec 64) (BitVec 64))
    (i1 i2 j v1 v2 d : BitVec 64) (h2 : j ≠ i2) (h1 : (j ^^^ i1) = 0#64) :
    ((m.insert i1 v1).insert i2 v2).getD j d = v1 := by
  bv_decide_qbe +uf

/-! ## 3. Programmatic Round-Count, SAT Soundness, Upstream Parity & Axiom Audit -/

private def assertTrue (msg : String) (b : Bool) : IO Unit := do
  if !b then throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def stdAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

private def countBvSolveAxioms (env : Environment) : Nat :=
  env.constants.fold (init := 0) fun acc name _ =>
    if name.toString.contains "_leanqbe.bv_solve.ax" then acc + 1 else acc

private def runAndCountRounds (prop : Expr) (mode : QbeMode) :
    MetaM (Except CounterExample CegarResult × Nat) := do
  let cfg : Lean.Elab.Tactic.BVDecide.BVDecideConfig := { uf := true }
  let tacticCtx := mkQbeTacticContext cfg
  let qbeCtx := mkQbeContext cfg (resolveQbeFeatures mode {})
  withOptions (fun o => o.setBool `trace.Meta.Tactic.bv true) do
    let savedTraces := (← getTraceState).traces
    let tracesBefore := savedTraces.size
    let mvar ← mkFreshExprMVar prop
    let res ← runPlainGrindM <|
      bvDecideQbe' (.mvarIdTarget mvar.mvarId!) tacticCtx qbeCtx
    let traces := (← getTraceState).traces
    let mut rounds := 0
    for i in [tracesBefore:traces.size] do
      let s ← traces[i]!.msg.toString
      rounds := rounds + ((s.splitOn "Checking BitVec abstraction").length - 1)
    modifyTraceState fun st => { st with traces := savedTraces }
    return (res, rounds)

private def satArrayProp : Prop :=
  ∀ (reg : Vector (BitVec 32) 16) (i j : BitVec 4) (v : BitVec 32),
    (reg.set i.toNat v i.isLt)[j.toNat]'j.isLt = v

private def satUfChainProp : Prop :=
  ∀ (f g h k : BitVec 32 → BitVec 32) (x y : BitVec 32),
    f (g (h (k x))) = f (g (h (k y)))

private def runAllCore : CoreM Unit := do
  -- 1. Axiom audit across all Gap #15 theorems (`<= std3` + valid per-goal bv_solve axiom)
  let thms : List Name := [
    ``thm_uf_chain6_64, ``thm_uf_iter6_64, ``thm_uf_diamond_32,
    ``thm_uf_wide_parallel_32, ``thm_uf_bridge_m0_e2,
    ``thm_vec_row_same_64, ``thm_vec_row_diff_64, ``thm_vec_row_ite_64,
    ``thm_vec_row_setIfInBounds_32, ``thm_vec_row_setBang_32,
    ``thm_vec_row_chain3_32, ``thm_vec_bool_row_16, ``thm_vec_read_congr_64,
    ``thm_arr_row_same_32, ``thm_arr_row_diff_32,
    ``thm_arr_row_setIfInBounds_32, ``thm_arr_row_setBang_32,
    ``thm_list_row_ite_32, ``thm_hm_row_ite_64, ``thm_hm_row_chain2_64
  ]
  let env ← getEnv
  for thm in thms do
    let axs ← collectAxioms thm
    for ax in axs do
      if !stdAxioms.contains ax then
        if !ax.toString.contains "_leanqbe.bv_solve.ax" then
          throwError "unexpected axiom {ax} in {thm}"
        let some axInfo := env.find? ax
          | throwError "missing axiom {ax}"
        assertTrue s!"{ax}: valid bv_solve axiom type"
          (isValidBvSolveAxiomType axInfo.type)

  -- 2. Programmatic round-count checks + SAT soundness (0 axioms) + `.upstream` parity
  MetaM.run' do
    let getType (n : Name) : MetaM Expr := do
      let some info := (← getEnv).find? n | throwError "missing {n}"
      return info.type
    let getVal (n : Name) : MetaM Expr := do
      let some info := (← getEnv).find? n | throwError "missing {n}"
      let some val := info.value? | throwError "missing value for {n}"
      return val

    -- 6-deep UF chain: `.enhanced` solves in 2 rounds (vs 7 rounds in `.upstream`)
    let pChain ← getType ``thm_uf_chain6_64
    let (resChainEnh, rChainEnh) ← runAndCountRounds pChain .enhanced
    let (resChainUp, rChainUp) ← runAndCountRounds pChain .upstream
    assertTrue "uf_chain6_64 enhanced UNSAT" resChainEnh.isOk
    assertTrue "uf_chain6_64 upstream UNSAT" resChainUp.isOk
    assertTrue s!"uf_chain6_64 enhanced rounds == 2 (got {rChainEnh})" (rChainEnh == 2)
    assertTrue s!"uf_chain6_64 upstream rounds == 7 (got {rChainUp})" (rChainUp == 7)

    -- Iterated 6x UF: `.enhanced` solves in 2 rounds (vs 16 rounds in `.upstream`)
    let pIter ← getType ``thm_uf_iter6_64
    let (resIterEnh, rIterEnh) ← runAndCountRounds pIter .enhanced
    assertTrue "uf_iter6_64 enhanced UNSAT" resIterEnh.isOk
    assertTrue s!"uf_iter6_64 enhanced rounds == 2 (got {rIterEnh})" (rIterEnh == 2)

    -- 3-write chained Vector McCarthy ROW: `.enhanced` solves in 2 rounds, `.upstream` leaves SAT
    let pVec3 ← getType ``thm_vec_row_chain3_32
    let (resVec3Enh, rVec3Enh) ← runAndCountRounds pVec3 .enhanced
    let (resVec3Up, _) ← runAndCountRounds pVec3 .upstream
    assertTrue "vec_row_chain3_32 enhanced UNSAT" resVec3Enh.isOk
    assertTrue s!"vec_row_chain3_32 enhanced rounds == 2 (got {rVec3Enh})" (rVec3Enh == 2)
    assertTrue "vec_row_chain3_32 upstream returns spurious CEX (parity)" (!resVec3Up.isOk)

    -- SAT soundness: array ROW & UF chain SAT must return `.error` with 0 new axioms
    let axBefore := countBvSolveAxioms (← getEnv)
    let (resSatArr, rSatArr) ← runAndCountRounds (← getVal ``satArrayProp) .enhanced
    assertTrue "SAT array ROW returns counterexample" (!resSatArr.isOk)
    assertTrue s!"SAT array ROW rounds == 2 (got {rSatArr})" (rSatArr == 2)
    let (resSatUf, rSatUf) ← runAndCountRounds (← getVal ``satUfChainProp) .enhanced
    assertTrue "SAT UF chain returns counterexample" (!resSatUf.isOk)
    assertTrue s!"SAT UF chain rounds == 2 (got {rSatUf})" (rSatUf == 2)
    assertTrue "SAT goals emit 0 bv_solve axioms" (countBvSolveAxioms (← getEnv) == axBefore)

  IO.println
    "CegarEnhanceTest: ALL PASSED (batched/cascading UF + McCarthy array ROW + SAT + parity)"

#eval runAllCore

end BvDecideQbeTest.CegarEnhanceTest
