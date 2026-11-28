module

import LeanQbe.T.LeanLCNF.Sem.P
meta import LeanQbe.T.LeanLCNF.Sem.P
import LeanQbe.T.LeanLCNF.Sem.PLemmas
meta import LeanQbe.T.LeanLCNF.Sem.PLemmas
import LeanQbe.T.LeanLCNF.Sem.PAdequacy
meta import LeanQbe.T.LeanLCNF.Sem.PAdequacy
import LeanQbe.T.LeanLCNF.Sem.RcCheck
meta import LeanQbe.T.LeanLCNF.Sem.RcCheck
import LeanQbe.T.LeanLCNF.Coverage
meta import LeanQbe.T.LeanLCNF.Coverage
import LeanQbe.T.LeanLCNF.LcnfC0Demo
meta import LeanQbe.T.LeanLCNF.LcnfC0Demo
import LeanQbe.T.LeanLCNF.LcnfC0LoopDemo
meta import LeanQbe.T.LeanLCNF.LcnfC0LoopDemo
import LeanQbe.T.LeanLCNF.LcnfC0RecDemo
meta import LeanQbe.T.LeanLCNF.LcnfC0RecDemo
import LeanQbe.T.LeanLCNF.LcnfC0TreeDemo
meta import LeanQbe.T.LeanLCNF.LcnfC0TreeDemo
import LeanQbe.T.LeanLCNF.LcnfC0ArrayDemo
meta import LeanQbe.T.LeanLCNF.LcnfC0ArrayDemo
import LeanQbe.T.LeanLCNF.LcnfC0MutRecDemo
meta import LeanQbe.T.LeanLCNF.LcnfC0MutRecDemo

/-!
# Tier-P Pure Semantics, Adequacy, and `RcCheck` Test Suite (`LcnfSemPTest`)

Differential `#guard` suite comparing executable `PEval` against Lean 4 reference functions
across all 6 `LcnfC0*Demo` modules and all 15 `Coverage.covMod` benchmarks (`shared = false` and
`shared = true`), positive/negative `RcCheck` unit tests, concrete `PWp` / adequacy non-vacuity
theorems, and `#print axioms` checks (`<= std3`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.LcnfSemPTest

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.LeanLCNF.Sem

/-! ## 1. Pure Helpers & Negative `RcCheck` Test Fixtures -/

def mkTestMod (name : String) (decls : List LcDecl) : LcModule :=
  { name := name, roots := decls.map (·.name), decls := decls, externs := [], snaps := [] }

def pObj (id : Nat) (borrow : Bool := false) : LcParam :=
  { id := id, ty := .object, borrow := borrow }

def pTagged (id : Nat) : LcParam :=
  { id := id, ty := .tobject, borrow := false }

def ctorBoolFalse : LcCtor := LcCtor.mk "Bool.false" 0 0 0 0
def ctorBoolTrue : LcCtor := LcCtor.mk "Bool.true" 1 0 0 0
def ctorPair : LcCtor := LcCtor.mk "Pair" 0 2 0 0
def ctorSingle : LcCtor := LcCtor.mk "Box" 0 1 0 0

def encTree : TreeDemo.Tree → PVal
  | .leaf => .ctor 0 [] []
  | .node v l r => .ctor 1 [.nat v, encTree l, encTree r] []

def sampleTree : TreeDemo.Tree :=
  .node 10 (.node 3 .leaf .leaf) (.node 7 (.node 1 .leaf .leaf) .leaf)

mutual
def encRose : MutRecDemo.Rose → PVal
  | .node v cs => .ctor 0 [.nat v, encForest cs] []
def encForest : MutRecDemo.Forest → PVal
  | .nil => .ctor 0 [] []
  | .cons hd tl => .ctor 1 [encRose hd, encForest tl] []
end

def sampleRose : MutRecDemo.Rose :=
  .node 5 (.cons (.node 2 .nil) (.cons (.node 8 (.cons (.node 1 .nil) .nil)) .nil))

def sampleForest : MutRecDemo.Forest :=
  .cons (.node 4 .nil) (.cons sampleRose .nil)

/-- Negative (a): leaked owned variable (`x.1` never consumed or `dec`'d). -/
def badLeakMod : LcModule :=
  mkTestMod "BadLeak"
    [{ name := "badLeak", params := [pObj 1], retTy := .erased, body := .ret .erased }]

/-- Negative (b1): double `dec` on an owned variable (`x.1` already dead at second `dec`). -/
def badDoubleDecMod : LcModule :=
  mkTestMod "BadDoubleDec"
    [{ name := "badDoubleDec"
       params := [pObj 1]
       retTy := .erased
       body := .dec 1 1 false (.dec 1 1 false (.ret .erased)) }]

/-- Negative (b2): use-after-free (`oproj` on `x.1` after `dec 1 1`). -/
def badUseAfterFreeMod : LcModule :=
  mkTestMod "BadUseAfterFree"
    [{ name := "badUaf"
       params := [pObj 1]
       retTy := .object
       body := .dec 1 1 false (.let_ 2 .object (.oproj 0 1)
         (.inc 2 1 false (.ret (.var 2)))) }]

/-- Negative (c): consuming a borrowed `@&` variable without `inc`. -/
def badConsumeBorrowMod : LcModule :=
  mkTestMod "BadConsumeBorrow"
    [{ name := "badConsumeBorrow"
       params := [pObj 1 (borrow := true)]
       retTy := .object
       body := .ret (.var 1) }]

/-- Negative (d1): unguarded `.oset` without `isShared == false` or fresh allocation. -/
def badUnguardedOsetMod : LcModule :=
  mkTestMod "BadUnguardedOset"
    [{ name := "badOset"
       params := [pObj 1, pObj 2]
       retTy := .object
       body := .oset 1 0 (.var 2) (.ret (.var 1)) }]

/-- Negative (d2): unguarded `.setTag` without exclusivity proof. -/
def badUnguardedSetTagMod : LcModule :=
  mkTestMod "BadUnguardedSetTag"
    [{ name := "badSetTag"
       params := [pObj 1]
       retTy := .object
       body := .setTag 1 1 (.ret (.var 1)) }]

/-- Negative (d3): unguarded `.del` without exclusivity proof. -/
def badUnguardedDelMod : LcModule :=
  mkTestMod "BadUnguardedDel"
    [{ name := "badDel"
       params := [pObj 1]
       retTy := .erased
       body := .del 1 (.ret .erased) }]

/-- Negative (e): child `oproj` borrow invalidated after parent `dec`. -/
def badParentDecBorrowMod : LcModule :=
  mkTestMod "BadParentDecBorrow"
    [{ name := "badParentDecBorrow"
       params := [pObj 1]
       retTy := .object
       body := .let_ 2 .object (.oproj 0 1)
         (.dec 1 1 false (.inc 2 1 false (.ret (.var 2)))) }]

/-- Negative (f): mismatched owned counts across two `jmp` sites targeting the same `jp`. -/
def badJmpMismatchMod : LcModule :=
  mkTestMod "BadJmpMismatch"
    [{ name := "badJmpMismatch"
       params := [pObj 1, pTagged 2]
       retTy := .erased
       body :=
         .jp 1 [] (.ret .erased)
           (.cases 2
             [ (.ctor 0 "Bool.false", .jmp 1 [])
             , (.ctor 1 "Bool.true", .dec 1 1 false (.jmp 1 [])) ]) }]

/-- Negative (g1): mutating a `reset` token via `.oset`. -/
def badResetOsetMod : LcModule :=
  mkTestMod "BadResetOset"
    [{ name := "badResetOset"
       params := [pObj 1]
       retTy := .object
       body := .let_ 2 .object (.reset 1 1)
         (.oset 2 0 .erased
           (.let_ 3 .object (.reuse 2 ctorSingle false [.erased]) (.ret (.var 3)))) }]

/-- Negative (g2): freeing a `reset` token via `.del`. -/
def badResetDelMod : LcModule :=
  mkTestMod "BadResetDel"
    [{ name := "badResetDel"
       params := [pObj 1]
       retTy := .erased
       body := .let_ 2 .object (.reset 1 1) (.del 2 (.ret .erased)) }]

/-- Positive control: `isShared == false` branch grants exclusivity for `oset`, while `true`
branch allocates fresh and `dec`s old parent. -/
def goodGuardedOsetMod : LcModule :=
  mkTestMod "GoodGuardedOset"
    [{ name := "goodOset"
       params := [pObj 1, pObj 2]
       retTy := .object
       body := .let_ 3 .tobject (.isShared 1)
         (.cases 3
           [ (.ctor 0 "Bool.false", .oset 1 0 (.var 2) (.ret (.var 1)))
           , (.ctor 1 "Bool.true",
               .let_ 4 .object (.oproj 1 1)
                 (.inc 4 1 false
                   (.dec 1 1 false
                     (.let_ 5 .object (.ctor ctorPair [.var 2, .var 4])
                       (.ret (.var 5)))))) ]) }]

/-! ## 2. Concrete Non-Vacuity & Metatheory Theorems -/

def jpLoopDecl : LcDecl :=
  { name := "jpCountdown"
    params := [pTagged 1, pTagged 2]
    retTy := .tobject
    body :=
      .jp 10 [pTagged 3, pTagged 4]
        (.let_ 8 .tobject (.lit (.nat 0))
          (.let_ 5 .tobject (.fap "Nat.decEq" [.var 3, .var 8])
            (.cases 5
              [ (.ctor 0 "Bool.false",
                  .let_ 6 .tobject (.lit (.nat 1))
                    (.let_ 7 .tobject (.fap "Nat.sub" [.var 3, .var 6])
                      (.jmp 10 [.var 7, .var 4])))
              , (.ctor 1 "Bool.true", .ret (.var 4)) ])))
        (.jmp 10 [.var 1, .var 2]) }

def jpLoopMod : LcModule :=
  mkTestMod "JpLoopMod" [jpLoopDecl]

/-- Pure symbolic loop verification via `PWp_jp_loop` + `PWp_frame_pure` on a `.jp` loop. -/
theorem nonvac_jp_loop_countdown (n k : Nat) :
    PWp (modArityOf jpLoopMod) PEnv.bot PJEnv.empty
      (PValEnv.empty.bindAll jpLoopDecl.params [.nat n, .nat k])
      (fun r => n ≥ 0 ∧ r = .nat k) (fun _ => n ≥ 0 ∧ False) jpLoopDecl.body := by
  refine PWp_frame_pure (Nat.zero_le n) ?_
  dsimp only [jpLoopDecl]
  let Inv : Nat → List PVal → Prop := fun m as => as = [.nat m, .nat k]
  refine PWp_jp_loop Inv (fun m as hm => by simp [Inv] at hm; simp [hm]) ?_ ?_
  · intro Jj m as ih hm
    dsimp only [Inv] at hm; subst hm
    have he1 : (((PValEnv.empty.bindAll [pTagged 1, pTagged 2] [.nat n, .nat k]).bindAll
        [pTagged 3, pTagged 4] [.nat m, .nat k]).set 8 (.nat 0)).evalArgs [.var 3, .var 8] =
        some [.nat m, .nat 0] := rfl
    have hoob0 : ("Nat.decEq" == "outOfBounds._redArg") = false := rfl
    have hp0 : pIsPrimName "Nat.decEq" = true := rfl
    have hpr0 : primP "Nat.decEq" [.nat m, .nat 0] = some (PVal.bool (m == 0)) := rfl
    dsimp only [PWp, PVal.wp]
    rw [he1]; dsimp only
    rw [ite_eq_right (by rw [hoob0]; exact Bool.false_ne_true)]
    rw [ite_eq_left hp0, hpr0]; dsimp only
    by_cases hzero : m = 0
    · subst hzero
      have h5 : ((((PValEnv.empty.bindAll [pTagged 1, pTagged 2] [.nat n, .nat k]).bindAll
          [pTagged 3, pTagged 4] [.nat 0, .nat k]).set 8 (.nat 0)).set 5
          (PVal.bool (0 == 0))) 5 = some (PVal.bool (0 == 0)) := rfl
      have ht : (PVal.bool (0 == 0)).tag? = some 1 := rfl
      have he4 : ((((PValEnv.empty.bindAll [pTagged 1, pTagged 2] [.nat n, .nat k]).bindAll
          [pTagged 3, pTagged 4] [.nat 0, .nat k]).set 8 (.nat 0)).set 5
          (PVal.bool (0 == 0))).evalArg (.var 4) = some (.nat k) := rfl
      rw [h5, Option.bind_some, ht]; dsimp only [PWpCtorAlts]
      rw [ite_eq_right (by decide), ite_eq_left rfl]
      dsimp only [PWp]; rw [he4]
    · have h5 : ((((PValEnv.empty.bindAll [pTagged 1, pTagged 2] [.nat n, .nat k]).bindAll
          [pTagged 3, pTagged 4] [.nat m, .nat k]).set 8 (.nat 0)).set 5
          (PVal.bool (m == 0))) 5 = some (PVal.bool (m == 0)) := rfl
      have hf : (PVal.bool (m == 0)).tag? = some 0 := by
        simp [PVal.bool, PVal.tag?, beq_false_of_ne hzero]
      have he2 : (((((PValEnv.empty.bindAll [pTagged 1, pTagged 2] [.nat n, .nat k]).bindAll
          [pTagged 3, pTagged 4] [.nat m, .nat k]).set 8 (.nat 0)).set 5
          (PVal.bool (m == 0))).set 6 (.nat 1)).evalArgs [.var 3, .var 6] =
          some [.nat m, .nat 1] := rfl
      have hoob1 : ("Nat.sub" == "outOfBounds._redArg") = false := rfl
      have hp1 : pIsPrimName "Nat.sub" = true := rfl
      have hpr1 : primP "Nat.sub" [.nat m, .nat 1] = some (.nat (m - 1)) := rfl
      have hejmp : ((((((PValEnv.empty.bindAll [pTagged 1, pTagged 2] [.nat n, .nat k]).bindAll
          [pTagged 3, pTagged 4] [.nat m, .nat k]).set 8 (.nat 0)).set 5
          (PVal.bool (m == 0))).set 6 (.nat 1)).set 7 (.nat (m - 1))).evalArgs
          [.var 7, .var 4] = some [.nat (m - 1), .nat k] := rfl
      rw [h5, Option.bind_some, hf]; dsimp only [PWpCtorAlts]
      rw [ite_eq_left rfl]
      dsimp only [PWp, PVal.wp]
      rw [he2]; dsimp only
      rw [ite_eq_right (by rw [hoob1]; exact Bool.false_ne_true)]
      rw [ite_eq_left hp1, hpr1]; dsimp only [PWp]
      rw [hejmp]; dsimp only [PJEnv.set]
      rw [ite_eq_left rfl]
      have hlt : m - 1 < m := Nat.sub_lt (Nat.pos_of_ne_zero hzero) Nat.one_pos
      exact ih (m - 1) [.nat (m - 1), .nat k] hlt rfl
  · intro Jj hJ
    have hej : (PValEnv.empty.bindAll [pTagged 1, pTagged 2] [.nat n, .nat k]).evalArgs
        [.var 1, .var 2] = some [.nat n, .nat k] := rfl
    dsimp only [PWp]; rw [hej]; dsimp only [PJEnv.set]
    rw [ite_eq_left rfl]
    exact hJ n [.nat n, .nat k] rfl

private theorem forall_mem_nil {α : Type} {P : α → Prop} : ∀ x ∈ ([] : List α), P x := by
  intro _ hx; cases hx

private theorem forall_mem_cons {α : Type} {P : α → Prop} {a : α} {as : List α}
    (ha : P a) (has : ∀ x ∈ as, P x) : ∀ x ∈ a :: as, P x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact ha
  · exact has x hx'

/-- Adequacy non-vacuity: `demoNatStrLcMod`'s `addNat 3 4` satisfies BOTH `PWp (PEvalInf ...)`
and `OutcomeOk` via `PWp_iff_PEval` and `PWp_sound_PEval`. -/
theorem nonvac_demo_addNat_iff :
    let d := demoNatStrLcMod.decls.head!
    PWp (modArityOf demoNatStrLcMod) (PEvalInf demoNatStrLcMod false) PJEnv.empty
      (PValEnv.empty.bindAll d.params [.nat 3, .nat 4])
      (fun r => r = .nat 7) (fun _ => False) d.body := by
  intro d
  have hd : d ∈ demoNatStrLcMod.decls := List.head_mem (by decide)
  have hno : noIsSharedCode d.body = true := rfl
  have hfind : demoNatStrLcMod.decls.find? (·.name == d.name) = some d := rfl
  have hlen : ([PVal.nat 3, PVal.nat 4] : List PVal).length = d.params.length := rfl
  rw [PWp_iff_PEval hd hno hfind hlen]
  exact ⟨10, .ret (.nat 7), rfl, rfl⟩

/-- Adequacy + module soundness non-vacuity on `DemoNatStr.addNat` via `PModuleOk_PEvalInf`
and `PWp_sound_PEval`. -/
theorem nonvac_demo_addNat_sound {fuel : Nat} {out : POutcome}
    (hev : PEval fuel demoNatStrLcMod "LeanQbe.T.LeanLCNF.DemoNatStr.addNat"
      [.nat 3, .nat 4] false = some out) :
    out = .ret (.nat 7) := by
  have hno : noIsSharedMod demoNatStrLcMod = true := rfl
  have hnodup : ∀ d ∈ demoNatStrLcMod.decls,
      demoNatStrLcMod.decls.find? (·.name == d.name) = some d := by
    dsimp [demoNatStrLcMod]
    repeat (first | exact forall_mem_nil | refine forall_mem_cons rfl ?_)
  have hm : PModuleOk (PEvalInf demoNatStrLcMod false) demoNatStrLcMod :=
    PModuleOk_PEvalInf hno hnodup false
  have hspec : PEvalInf demoNatStrLcMod false "LeanQbe.T.LeanLCNF.DemoNatStr.addNat"
      [.nat 3, .nat 4] (fun r => r = .nat 7) (fun _ => False) :=
    ⟨10, .ret (.nat 7), rfl, rfl⟩
  have hok := PWp_sound_PEval hm hspec hev
  cases out with
  | ret r => exact congrArg POutcome.ret hok
  | panic c => exact False.elim hok

/-- Adequacy non-vacuity on recursive `FactLoop.factAcc 5 1 = 120`. -/
theorem nonvac_factLoop_factAcc_iff :
    ∃ d ∈ factLoopLcMod.decls,
      d.name = "LeanQbe.T.LeanLCNF.FactLoop.factAcc" ∧
      PWp (modArityOf factLoopLcMod) (PEvalInf factLoopLcMod false) PJEnv.empty
        (PValEnv.empty.bindAll d.params [.nat 5, .nat 1])
        (fun r => r = .nat 120) (fun _ => False) d.body := by
  let d := factLoopLcMod.decls.head!
  have hd : d ∈ factLoopLcMod.decls := List.head_mem (by decide)
  have hnm : d.name = "LeanQbe.T.LeanLCNF.FactLoop.factAcc" := rfl
  have hno : noIsSharedCode d.body = true := rfl
  have hfind : factLoopLcMod.decls.find? (·.name == d.name) = some d := rfl
  have hlen : ([PVal.nat 5, PVal.nat 1] : List PVal).length = d.params.length := rfl
  exact ⟨d, hd, hnm, (PWp_iff_PEval hd hno hfind hlen).mpr ⟨30, .ret (.nat 120), rfl, rfl⟩⟩

end LeanQbeTest.T.LcnfSemPTest

end

/-! ## 3. Differential `#guard` Tests (`LcnfC0*Demo` + `Coverage.covMod`) -/

section TierPDiffGuards
open LeanQbe.T.LeanLCNF LeanQbe.T.LeanLCNF.Sem LeanQbeTest.T.LcnfSemPTest

-- `noIsSharedMod` and positive `RcCheck` checks
#guard noIsSharedMod demoNatStrLcMod == true
#guard noIsSharedMod factLoopLcMod == true
#guard noIsSharedMod recDemoLcMod == true
#guard noIsSharedMod treeDemoLcMod == true
#guard noIsSharedMod arrayDemoLcMod == true
#guard noIsSharedMod mutRecDemoLcMod == true
#guard noIsSharedMod Coverage.covMod == true

#guard RcCheck demoNatStrLcMod == true
#guard RcCheck factLoopLcMod == true
#guard RcCheck recDemoLcMod == true
#guard RcCheck treeDemoLcMod == true
#guard RcCheck arrayDemoLcMod == true
#guard RcCheck mutRecDemoLcMod == true
#guard RcCheck Coverage.covMod == true
#guard RcCheck goodGuardedOsetMod == true

-- 1. `LcnfC0Demo` (3 entry points, `shared = false` and `shared = true`)
#guard PEval 20 demoNatStrLcMod "LeanQbe.T.LeanLCNF.DemoNatStr.addNat" [.nat 3, .nat 4] false ==
  some (.ret (.nat (DemoNatStr.addNat 3 4)))
#guard PEval 20 demoNatStrLcMod "LeanQbe.T.LeanLCNF.DemoNatStr.addNat" [.nat 0, .nat 17] true ==
  some (.ret (.nat (DemoNatStr.addNat 0 17)))
#guard PEval 20 demoNatStrLcMod "LeanQbe.T.LeanLCNF.DemoNatStr.addToStr" [.nat 19, .nat 23] false ==
  some (.ret (.str (DemoNatStr.addToStr 19 23)))
#guard PEval 20 demoNatStrLcMod "LeanQbe.T.LeanLCNF.DemoNatStr.addToStr" [.nat 19, .nat 23] true ==
  some (.ret (.str (DemoNatStr.addToStr 19 23)))
#guard PEval 20 demoNatStrLcMod "LeanQbe.T.LeanLCNF.DemoNatStr.fmtSumTagged"
    [.str "sum", .nat 4, .nat 5] false ==
  some (.ret (.str (DemoNatStr.fmtSumTagged "sum" 4 5)))
#guard PEval 20 demoNatStrLcMod "LeanQbe.T.LeanLCNF.DemoNatStr.fmtSumTagged"
    [.str "sum", .nat 4, .nat 5] true ==
  some (.ret (.str (DemoNatStr.fmtSumTagged "sum" 4 5)))

-- 2. `LcnfC0LoopDemo` (2 entry points, `shared = false` and `shared = true`)
#guard PEval 40 factLoopLcMod "LeanQbe.T.LeanLCNF.FactLoop.factAcc" [.nat 5, .nat 1] false ==
  some (.ret (.nat (FactLoop.factAcc 5 1)))
#guard PEval 40 factLoopLcMod "LeanQbe.T.LeanLCNF.FactLoop.factAcc" [.nat 0, .nat 7] true ==
  some (.ret (.nat (FactLoop.factAcc 0 7)))
#guard PEval 40 factLoopLcMod "LeanQbe.T.LeanLCNF.FactLoop.factStr" [.nat 5] false ==
  some (.ret (.str (FactLoop.factStr 5)))
#guard PEval 40 factLoopLcMod "LeanQbe.T.LeanLCNF.FactLoop.factStr" [.nat 5] true ==
  some (.ret (.str (FactLoop.factStr 5)))

-- 3. `LcnfC0RecDemo` (`listSum`, `shared = false` and `shared = true`)
#guard PEval 40 recDemoLcMod "LeanQbe.T.LeanLCNF.RecDemo.listSum"
    [PVal.ofList [.nat 10, .nat 20, .nat 30]] false ==
  some (.ret (.nat (RecDemo.listSum [10, 20, 30])))
#guard PEval 40 recDemoLcMod "LeanQbe.T.LeanLCNF.RecDemo.listSum" [PVal.ofList []] true ==
  some (.ret (.nat (RecDemo.listSum [])))

-- 4. `LcnfC0TreeDemo` (`treeSum`, `treeSize`, `shared = false` and `shared = true`)
#guard PEval 40 treeDemoLcMod "LeanQbe.T.LeanLCNF.TreeDemo.treeSum" [encTree sampleTree] false ==
  some (.ret (.nat (TreeDemo.treeSum sampleTree)))
#guard PEval 40 treeDemoLcMod "LeanQbe.T.LeanLCNF.TreeDemo.treeSum" [encTree .leaf] true ==
  some (.ret (.nat (TreeDemo.treeSum .leaf)))
#guard PEval 40 treeDemoLcMod "LeanQbe.T.LeanLCNF.TreeDemo.treeSize" [encTree sampleTree] false ==
  some (.ret (.nat (TreeDemo.treeSize sampleTree)))
#guard PEval 40 treeDemoLcMod "LeanQbe.T.LeanLCNF.TreeDemo.treeSize" [encTree sampleTree] true ==
  some (.ret (.nat (TreeDemo.treeSize sampleTree)))

-- 5. `LcnfC0ArrayDemo` (3 entry points, `shared = false` and `shared = true`)
#guard PEval 60 arrayDemoLcMod "LeanQbe.T.LeanLCNF.ArrayDemo.arrayPushSetGet"
    [.nat 10, .nat 20, .nat 99] false ==
  some (.ret (.nat (ArrayDemo.arrayPushSetGet 10 20 99)))
#guard PEval 60 arrayDemoLcMod "LeanQbe.T.LeanLCNF.ArrayDemo.arrayPushSetGet"
    [.nat 10, .nat 20, .nat 99] true ==
  some (.ret (.nat (ArrayDemo.arrayPushSetGet 10 20 99)))
#guard PEval 60 arrayDemoLcMod "LeanQbe.T.LeanLCNF.ArrayDemo.baPushSetGet"
    [.nat 5, .bits 8 11#8, .bits 8 22#8, .bits 8 77#8] false ==
  some (.ret (.bits 8 (ArrayDemo.baPushSetGet 5 11 22 77).toBitVec))
#guard PEval 60 arrayDemoLcMod "LeanQbe.T.LeanLCNF.ArrayDemo.baPushSetGet"
    [.nat 5, .bits 8 11#8, .bits 8 22#8, .bits 8 77#8] true ==
  some (.ret (.bits 8 (ArrayDemo.baPushSetGet 5 11 22 77).toBitVec))
#guard PEval 60 arrayDemoLcMod "LeanQbe.T.LeanLCNF.ArrayDemo.baCowSetGet"
    [.barr [10, 20, 30], .bits 8 55#8] false ==
  some (.ret (.bits 8 (ArrayDemo.baCowSetGet (ByteArray.mk #[10, 20, 30]) 55).toBitVec))
#guard PEval 60 arrayDemoLcMod "LeanQbe.T.LeanLCNF.ArrayDemo.baCowSetGet"
    [.barr [10, 20, 30], .bits 8 55#8] true ==
  some (.ret (.bits 8 (ArrayDemo.baCowSetGet (ByteArray.mk #[10, 20, 30]) 55).toBitVec))

-- 6. `LcnfC0MutRecDemo` (`roseSum`, `forestSum`, `shared = false` and `shared = true`)
#guard PEval 60 mutRecDemoLcMod "LeanQbe.T.LeanLCNF.MutRecDemo.roseSum"
    [encRose sampleRose] false ==
  some (.ret (.nat (MutRecDemo.roseSum sampleRose)))
#guard PEval 60 mutRecDemoLcMod "LeanQbe.T.LeanLCNF.MutRecDemo.roseSum"
    [encRose sampleRose] true ==
  some (.ret (.nat (MutRecDemo.roseSum sampleRose)))
#guard PEval 60 mutRecDemoLcMod "LeanQbe.T.LeanLCNF.MutRecDemo.forestSum"
    [encForest sampleForest] false ==
  some (.ret (.nat (MutRecDemo.forestSum sampleForest)))
#guard PEval 60 mutRecDemoLcMod "LeanQbe.T.LeanLCNF.MutRecDemo.forestSum"
    [encForest sampleForest] true ==
  some (.ret (.nat (MutRecDemo.forestSum sampleForest)))

-- 7. `Coverage.covMod` (all 15 benchmarks, `shared = false` and `shared = true`)
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.strLitTest" [.nat 3] false ==
  some (.ret (.nat (Coverage.strLitTest 3)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.strLitTest" [.nat 3] true ==
  some (.ret (.nat (Coverage.strLitTest 3)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.strBuildBench" [.nat 6] false ==
  some (.ret (.nat (Coverage.strBuildBench 6)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.strBuildBench" [.nat 6] true ==
  some (.ret (.nat (Coverage.strBuildBench 6)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.bigNatBench" [.nat 4] false ==
  some (.ret (.nat (Coverage.bigNatBench 4)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.bigNatBench" [.nat 4] true ==
  some (.ret (.nat (Coverage.bigNatBench 4)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.arrBench" [.nat 5] false ==
  some (.ret (.nat (Coverage.arrBench 5)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.arrBench" [.nat 5] true ==
  some (.ret (.nat (Coverage.arrBench 5)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.arrLinear" [.nat 4, .nat 9] false ==
  some (.ret (.nat (Coverage.arrLinear 4 9)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.arrLinear" [.nat 4, .nat 9] true ==
  some (.ret (.nat (Coverage.arrLinear 4 9)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.arrShared" [.nat 4, .nat 9] false ==
  some (.ret (.nat (Coverage.arrShared 4 9)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.arrShared" [.nat 4, .nat 9] true ==
  some (.ret (.nat (Coverage.arrShared 4 9)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.byteArrBench" [.nat 5] false ==
  some (.ret (.nat (Coverage.byteArrBench 5)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.byteArrBench" [.nat 5] true ==
  some (.ret (.nat (Coverage.byteArrBench 5)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.floatBench" [.nat 7] false ==
  some (.ret (.bits 64 (Coverage.floatBench 7).toBitVec))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.floatBench" [.nat 7] true ==
  some (.ret (.bits 64 (Coverage.floatBench 7).toBitVec))
#guard PEval 300 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.intBench" [.nat 7] false ==
  some (.ret (.nat (Coverage.intBench 7)))
#guard PEval 300 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.intBench" [.nat 7] true ==
  some (.ret (.nat (Coverage.intBench 7)))
#guard PEval 300 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.bitVecIntBench" [.nat 7] false ==
  some (.ret (.nat (Coverage.bitVecIntBench 7)))
#guard PEval 300 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.bitVecIntBench" [.nat 7] true ==
  some (.ret (.nat (Coverage.bitVecIntBench 7)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.int64Bench" [.nat 7] false ==
  some (.ret (.nat (Coverage.int64Bench 7)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.int64Bench" [.nat 7] true ==
  some (.ret (.nat (Coverage.int64Bench 7)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.uintBvBench" [.nat 7] false ==
  some (.ret (.nat (Coverage.uintBvBench 7)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.uintBvBench" [.nat 7] true ==
  some (.ret (.nat (Coverage.uintBvBench 7)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.shapeBench" [.nat 7] false ==
  some (.ret (.nat (Coverage.shapeBench 7)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.shapeBench" [.nat 7] true ==
  some (.ret (.nat (Coverage.shapeBench 7)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.usizeBench" [.nat 7] false ==
  some (.ret (.nat (Coverage.usizeBench 7)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.usizeBench" [.nat 7] true ==
  some (.ret (.nat (Coverage.usizeBench 7)))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.shaMix" [.nat 7] false ==
  some (.ret (.nat 319659308))
#guard PEval 50 Coverage.covMod "LeanQbe.T.LeanLCNF.Coverage.shaMix" [.nat 7] true ==
  some (.ret (.nat (Coverage.shaMix 7)))

end TierPDiffGuards

/-! ## 4. Negative `RcCheck` Unit Tests & Axiom Audits -/

section RcCheckNegGuards
open LeanQbe.T.LeanLCNF.Sem LeanQbeTest.T.LcnfSemPTest

#guard RcCheck badLeakMod == false
#guard RcCheck badDoubleDecMod == false
#guard RcCheck badUseAfterFreeMod == false
#guard RcCheck badConsumeBorrowMod == false
#guard RcCheck badUnguardedOsetMod == false
#guard RcCheck badUnguardedSetTagMod == false
#guard RcCheck badUnguardedDelMod == false
#guard RcCheck badParentDecBorrowMod == false
#guard RcCheck badJmpMismatchMod == false
#guard RcCheck badResetOsetMod == false
#guard RcCheck badResetDelMod == false

end RcCheckNegGuards

#print axioms LeanQbe.T.LeanLCNF.Sem.PWp_conseq
#print axioms LeanQbe.T.LeanLCNF.Sem.PWp_mono
#print axioms LeanQbe.T.LeanLCNF.Sem.PWp_env_mono
#print axioms LeanQbe.T.LeanLCNF.Sem.PWp_jp_mono
#print axioms LeanQbe.T.LeanLCNF.Sem.PWp_frame_pure
#print axioms LeanQbe.T.LeanLCNF.Sem.PWp_jp_loop
#print axioms LeanQbe.T.LeanLCNF.Sem.PWp_jp_rule
#print axioms LeanQbe.T.LeanLCNF.Sem.PEvalCode_fuel_mono
#print axioms LeanQbe.T.LeanLCNF.Sem.PEval_fuel_mono
#print axioms LeanQbe.T.LeanLCNF.Sem.PEvalCode_det
#print axioms LeanQbe.T.LeanLCNF.Sem.PEval_det
#print axioms LeanQbe.T.LeanLCNF.Sem.PWp_sound_PEval
#print axioms LeanQbe.T.LeanLCNF.Sem.PWp_sound_PEval_idx
#print axioms LeanQbe.T.LeanLCNF.Sem.PWp_terminates_PEval
#print axioms LeanQbe.T.LeanLCNF.Sem.PEval_complete_PWp
#print axioms LeanQbe.T.LeanLCNF.Sem.PModuleOk_PEvalInf
#print axioms LeanQbe.T.LeanLCNF.Sem.PWp_iff_PEval
#print axioms LeanQbeTest.T.LcnfSemPTest.nonvac_jp_loop_countdown
#print axioms LeanQbeTest.T.LcnfSemPTest.nonvac_demo_addNat_iff
#print axioms LeanQbeTest.T.LcnfSemPTest.nonvac_demo_addNat_sound
#print axioms LeanQbeTest.T.LcnfSemPTest.nonvac_factLoop_factAcc_iff
