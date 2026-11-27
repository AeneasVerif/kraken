module

public import LeanQbe.T.LeanLCNF.Sem.Perceus
meta import LeanQbe.T.LeanLCNF.Sem.Perceus
public import LeanQbe.T.LeanLCNF.Sem.PLemmas
meta import LeanQbe.T.LeanLCNF.Sem.PLemmas
public import LeanQbe.T.LeanLCNF.Sem.PAdequacy
meta import LeanQbe.T.LeanLCNF.Sem.PAdequacy
public import LeanQbe.T.LeanLCNF.LcnfC0Demo
meta import LeanQbe.T.LeanLCNF.LcnfC0Demo
public import LeanQbe.T.LeanLCNF.LcnfC0LoopDemo
meta import LeanQbe.T.LeanLCNF.LcnfC0LoopDemo

/-!
# Perceus Soundness (`L4b`) End-to-End Test Suite (`LcnfPerceusTest`)

Verifies `RcCheck`, `perceusModWf`, pure `PModuleOk` / `PModuleOkIdx`, and Tier-P → Tier-H
soundness (`perceus_sound`, `perceus_sound_idx`) across:
- Acyclic first-order arithmetic (`addNatMod`: `13 + 29 = 42` on concrete `testInitState`),
- FBIP `isShared`-guarded in-place update vs shared allocation (`goodOsetMod`),
- Recursive measure-indexed functions (`factAccMod`, `listSumMod`, `treeSumMod`),
  including concrete non-vacuous execution of `factAcc 5 1 = 120`,
- Negative `RcCheck` / `perceusModWf` controls and `#print axioms` (`<= std3`).
-/

set_option autoImplicit false

namespace LeanQbeTest.T.LcnfPerceusTest

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.LeanLCNF.Sem

public section

/-! ## 1. Test Modules, Initial Heap State, and Negative Controls -/

@[expose] def mkTestMod (name : String) (decls : List LcDecl) : LcModule :=
  { name := name, roots := decls.map (·.name), decls := decls, externs := [], snaps := [] }

@[expose] def ctorPair : LcCtor := LcCtor.mk "Pair" 0 2 0 0

@[expose] def addNatDecl : LcDecl :=
  { name := "LeanQbe.T.LeanLCNF.DemoNatStr.addNat"
    params := [{ id := 1, ty := .tobject, borrow := true },
               { id := 2, ty := .tobject, borrow := true }]
    retTy := .tobject
    body := .let_ 3 .tobject (.fap "Nat.add" [.var 1, .var 2]) (.ret (.var 3)) }

@[expose] def addNatMod : LcModule :=
  mkTestMod "AddNatMod" [addNatDecl]

@[expose] def factAccDecl : LcDecl :=
  { name := "LeanQbe.T.LeanLCNF.FactLoop.factAcc"
    params := [{ id := 1, ty := .tobject, borrow := false },
               { id := 2, ty := .tobject, borrow := false }]
    retTy := .tobject
    body :=
      .let_ 3 .tagged (.lit (.nat 0))
        (.let_ 4 .uint8 (.fap "Nat.decEq" [.var 1, .var 3])
          (.cases 4
            [ (.ctor 0 "Bool.false",
                .let_ 5 .tagged (.lit (.nat 1))
                  (.let_ 6 .tobject (.fap "Nat.sub" [.var 1, .var 5])
                    (.let_ 7 .tobject (.fap "Nat.mul" [.var 2, .var 1])
                      (.dec 1 1 true
                        (.dec 2 1 true
                          (.let_ 8 .tobject
                            (.fap "LeanQbe.T.LeanLCNF.FactLoop.factAcc" [.var 6, .var 7])
                            (.ret (.var 8))))))))
            , (.ctor 1 "Bool.true", .dec 1 1 true (.ret (.var 2))) ])) }

@[expose] def factAccMod : LcModule :=
  mkTestMod "FactAccMod" [factAccDecl]

@[expose] def listSumDecl : LcDecl :=
  { name := "listSum"
    params := [{ id := 1, ty := .tobject, borrow := true }]
    retTy := .tobject
    body := .cases 1
      [ (.ctor 0 "List.nil", .let_ 2 .tobject (.lit (.nat 0)) (.ret (.var 2)))
      , (.ctor 1 "List.cons",
          .let_ 3 .tobject (.oproj 0 1)
            (.let_ 4 .tobject (.oproj 1 1)
              (.let_ 5 .tobject (.fap "listSum" [.var 4])
                (.let_ 6 .tobject (.fap "Nat.add" [.var 3, .var 5])
                  (.dec 5 1 true (.ret (.var 6))))))) ] }

@[expose] def listSumMod : LcModule :=
  mkTestMod "ListSumMod" [listSumDecl]

@[expose] def treeSumDecl : LcDecl :=
  { name := "treeSum"
    params := [{ id := 1, ty := .tobject, borrow := true }]
    retTy := .tobject
    body := .cases 1
      [ (.ctor 0 "Tree.leaf", .let_ 2 .tobject (.lit (.nat 0)) (.ret (.var 2)))
      , (.ctor 1 "Tree.node",
          .let_ 3 .tobject (.oproj 0 1)
            (.let_ 4 .tobject (.oproj 1 1)
              (.let_ 5 .tobject (.oproj 2 1)
                (.let_ 6 .tobject (.fap "treeSum" [.var 4])
                  (.let_ 7 .tobject (.fap "treeSum" [.var 5])
                    (.let_ 8 .tobject (.fap "Nat.add" [.var 3, .var 6])
                      (.dec 6 1 true
                        (.let_ 9 .tobject (.fap "Nat.add" [.var 8, .var 7])
                          (.dec 8 1 true (.dec 7 1 true (.ret (.var 9)))))))))))) ] }

@[expose] def treeSumMod : LcModule :=
  mkTestMod "TreeSumMod" [treeSumDecl]

@[expose] def goodOsetDecl : LcDecl :=
  { name := "goodOset"
    params := [{ id := 1, ty := .object, borrow := false },
               { id := 2, ty := .object, borrow := false }]
    retTy := .object
    body := .let_ 3 .uint8 (.isShared 1)
      (.cases 3
        [ (.ctor 0 "Bool.false", .oset 1 0 (.var 2) (.ret (.var 1)))
        , (.ctor 1 "Bool.true",
            .let_ 4 .tobject (.oproj 1 1)
              (.inc 4 1 true
                (.dec 1 1 false
                  (.let_ 5 .object (.ctor ctorPair [.var 2, .var 4])
                    (.ret (.var 5)))))) ]) }

@[expose] def goodOsetMod : LcModule :=
  mkTestMod "GoodOsetMod" [goodOsetDecl]

@[expose] def badLeakMod : LcModule :=
  mkTestMod "BadLeak"
    [{ name := "badLeak"
       params := [{ id := 1, ty := .object, borrow := false }]
       retTy := .erased
       body := .ret .erased }]

@[expose] def badDoubleDecMod : LcModule :=
  mkTestMod "BadDoubleDec"
    [{ name := "badDoubleDec"
       params := [{ id := 1, ty := .object, borrow := false }]
       retTy := .erased
       body := .dec 1 1 false (.dec 1 1 false (.ret .erased)) }]

@[expose] def badUnguardedOsetMod : LcModule :=
  mkTestMod "BadUnguardedOset"
    [{ name := "badOset"
       params := [{ id := 1, ty := .object, borrow := false },
                  { id := 2, ty := .object, borrow := false }]
       retTy := .object
       body := .oset 1 0 (.var 2) (.ret (.var 1)) }]

@[expose] def testRtBase : BitVec 64 := 0x10000#64

@[expose] def testInitState : HState :=
  { st := initRtC0State testRtBase 8 256 (by decide) (by decide)
    objs := []
    scr := 0x10000#64 + 64
    scrLimbs := List.replicate 32 0#64 }

theorem testInitState_inv : HInv testRtBase testInitState := by
  refine ⟨?_, by decide, by decide, by decide, by decide, by decide⟩
  unfold RtC0State.Bounded48
  decide

theorem testInitState_heapClean : HeapClean testRtBase testInitState := by
  refine ⟨⟨testInitState_inv, ?_, ?_, ?_, ?_⟩, List.nodup_nil⟩
  · intro _ ho; cases ho
  · intro _ ho; cases ho
  · decide
  · intro _ ho; cases ho

/-! ## 2. `RcCheck`, `perceusModWf`, and Concrete `addNat` / FBIP `perceus_sound` -/

private theorem forall_mem_nil {α : Type} {P : α → Prop} : ∀ x ∈ ([] : List α), P x := by
  intro _ hx; cases hx

private theorem forall_mem_cons {α : Type} {P : α → Prop} {a : α} {as : List α}
    (ha : P a) (has : ∀ x ∈ as, P x) : ∀ x ∈ a :: as, P x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact ha
  · exact has x hx'

private theorem testInitState_resStateInv : ResStateInv testInitState 0 0 0 := by
  refine ⟨Nat.zero_le _, ?_, ?_⟩ <;> decide

private theorem testInitState_rcInv_twoNat {d : LcDecl} {br : Bool} {a b : Nat}
    (hps : d.params = [{ id := 1, ty := .tobject, borrow := br },
                       { id := 2, ty := .tobject, borrow := br }])
    (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    RcInv testRtBase
      (entryRcFrame d [.nat a, .nat b] [Word.i64 (boxNat a), Word.i64 (boxNat b)] [] [])
      testInitState := by
  rcases d with ⟨nm, ps, rty, body⟩
  dsimp only at hps; subst hps
  let d0 : LcDecl :=
    ⟨nm, [{ id := 1, ty := .tobject, borrow := br },
          { id := 2, ty := .tobject, borrow := br }], rty, body⟩
  change RcInv testRtBase
    (entryRcFrame d0 [.nat a, .nat b] [Word.i64 (boxNat a), Word.i64 (boxNat b)] [] [])
    testInitState
  have hclean : HeapClean testRtBase testInitState := testInitState_heapClean
  have hnd : (List.map RcVar.id
      (entryRcFrame d0 [.nat a, .nat b]
        [Word.i64 (boxNat a), Word.i64 (boxNat b)] [] []).ctx.vars).Nodup := by
    cases br <;>
      simp [d0, entryRcFrame, RcCtx.bindParams, RcCtx.bindOwned, RcCtx.bindBorrowed, RcCtx.put,
        RcCtx.put.go, LcTy.needsRc]
  have hhs : HandlesRcSound
      (frameHandles (entryRcFrame d0 [.nat a, .nat b]
        [Word.i64 (boxNat a), Word.i64 (boxNat b)] [] []))
      testInitState.objs :=
    ⟨fun _ h => by simp [testInitState] at h, fun _ h => by simp [testInitState] at h⟩
  refine ⟨hclean, hnd, hhs, ?_, ?_⟩
  · intro v hv _
    have hvars : (entryRcFrame d0 [.nat a, .nat b]
        [Word.i64 (boxNat a), Word.i64 (boxNat b)] [] []).ctx.vars =
        if br then
          [{ id := 1, ty := .tobject, borrowed := true },
           { id := 2, ty := .tobject, borrowed := true }]
        else
          [{ id := 1, ty := .tobject, owned := 1 },
           { id := 2, ty := .tobject, owned := 1 }] := by cases br <;> rfl
    rw [hvars] at hv
    cases br <;>
    · simp at hv
      rcases hv with rfl | rfl
      · refine ⟨.nat a, Word.i64 (boxNat a), rfl, rfl, ?_, ?_⟩
        · refine ⟨boxNat a, rfl, ?_, (fun h => by cases h), fun _ => boxNat_and1_ne_zero a⟩
          simp [ObjRep, natRepR0, ha, boxNat]
        · intro _; refine ⟨boxNat a, rfl, (fun h => by cases h), (fun h => by cases h),
            (fun h => by cases h), fun _ _ _ hev => absurd hev (boxNat_and1_ne_zero a)⟩
      · refine ⟨.nat b, Word.i64 (boxNat b), rfl, rfl, ?_, ?_⟩
        · refine ⟨boxNat b, rfl, ?_, (fun h => by cases h), fun _ => boxNat_and1_ne_zero b⟩
          simp [ObjRep, natRepR0, hb, boxNat]
        · intro _; refine ⟨boxNat b, rfl, (fun h => by cases h), (fun h => by cases h),
            (fun h => by cases h), fun _ _ _ hev => absurd hev (boxNat_and1_ne_zero b)⟩
  · intro p hp
    cases br <;>
      simp [d0, entryRcFrame, RcCtx.bindParams, RcCtx.bindOwned, RcCtx.bindBorrowed, RcCtx.put,
        RcCtx.put.go, LcTy.needsRc] at hp

@[expose] def addNatResEnv : PResEnv :=
  fun fn pvs rem wr rcr Pr _ =>
    fn = addNatDecl.name ∧
    ∃ a b : Nat, a + b < 2 ^ 63 ∧ pvs = [.nat a, .nat b] ∧ Pr (.nat (a + b)) rem wr rcr

private theorem addNatResEnv_ok : PResOk addNatResEnv addNatMod := by
  intro d hd as rem wr rcr Q _ _ ⟨_, a, b, hsum, has, hq⟩
  subst has
  rcases List.mem_singleton.mp hd with rfl
  obtain ⟨_, hcv⟩ : ∃ c, checkVal (mkRcModEnv addNatMod)
      (RcCtx.mk [] [] |>.bindParams addNatDecl.params) 3 .tobject
      (.fap "Nat.add" [.var 1, .var 2]) = .ok c := ⟨_, rfl⟩
  have hev : (PValEnv.empty.bindAll
      [{ id := 1, ty := .tobject, borrow := true }, { id := 2, ty := .tobject, borrow := true }]
      [.nat a, .nat b]).evalArgs [.var 1, .var 2] = some [.nat a, .nat b] := rfl
  have hdisj : ((mkRcModEnv addNatMod).decls.find? (·.1 == "Nat.add")).isSome = false := rfl
  have hpadd : primP "Nat.add" [.nat a, .nat b] = some (.nat (a + b)) := rfl
  dsimp only [addNatDecl] at hcv
  dsimp only [addNatDecl, PRWp, PRValWp]
  rw [hcv]; dsimp only
  rw [hev]; dsimp only
  rw [ite_eq_right (fun h => by cases h), ite_eq_right (fun h => by rw [h] at hdisj; cases hdisj)]
  rw [hpadd]; dsimp only
  refine ⟨rfl, hsum, ?_⟩
  have he3 : ((PValEnv.empty.bindAll
      [{ id := 1, ty := .tobject, borrow := true }, { id := 2, ty := .tobject, borrow := true }]
      [.nat a, .nat b]).set 3 (.nat (a + b))).evalArg (.var 3) = some (.nat (a + b)) := rfl
  rw [he3]
  exact hq

/-- End-to-end `perceus_sound` on acyclic `addNatMod`. -/
public theorem addNatMod_perceus_sound :
    HModuleOk (hOfP addNatMod (PEvalInf addNatMod false)) addNatMod := by
  have hm : PModuleOk (PEvalInf addNatMod false) addNatMod :=
    PModuleOk_PEvalInf (by decide) (by
      intro d hd; rcases List.mem_singleton.mp hd with rfl; rfl) false
  exact perceus_sound (by decide) (by decide) hm

/-- Non-vacuous Tier-H execution of `addNat 13 29 = 42` on `testInitState` via `perceus_sound`. -/
public theorem addNatMod_nonvac_hwp :
    HWp (hOfP addNatMod (PEvalInf addNatMod false)) testRtBase .tobject HJEnv.empty
      (HValEnv.empty.bindAll addNatDecl.params [Word.i64 (boxNat 13), Word.i64 (boxNat 29)])
      (fun rw σ' => ValRep .tobject (.nat 42) rw σ'.objs)
      (fun _ _ => False) addNatDecl.body testInitState := by
  have hd : addNatDecl ∈ addNatMod.decls := List.mem_singleton.mpr rfl
  have hrc := testInitState_rcInv_twoNat (d := addNatDecl) (br := true) (a := 13) (b := 29) rfl
    (by decide) (by decide)
  have hmatch : paramsMatch addNatDecl.params [Word.i64 (boxNat 13), Word.i64 (boxNat 29)] := by
    simp [paramsMatch, addNatDecl, LcTy.toTTy, LcTy.width, Word.i64]
  have hspec : hOfP addNatMod (PEvalInf addNatMod false) addNatDecl.name
      [Word.i64 (boxNat 13), Word.i64 (boxNat 29)] testInitState
      (fun rw σ' => ValRep .tobject (.nat 42) rw σ'.objs) (fun _ _ => False) := by
    unfold hOfP
    refine ⟨testRtBase, addNatDecl, addNatResEnv, [.nat 13, .nat 29], [], [], 0, 0, 0,
      fun r => r = .nat 42, fun _ => False, fun r _ _ _ => r = .nat 42,
      fun _ _ _ _ => False, hd, rfl, addNatResEnv_ok, hrc, ?_⟩
    refine ⟨(fun _ h => nomatch h), testInitState_resStateInv, rfl,
      ⟨10, .ret (.nat 42), rfl, rfl⟩, ⟨rfl, 13, 29, by decide, rfl, rfl⟩, ?_, ?_⟩
    · rintro r rw σ' _ _ _ rfl _ _ _ hvr _ _ _; exact hvr
    · intro c _ _ _ _ hf _; exact False.elim hf
  exact addNatMod_perceus_sound addNatDecl hd testRtBase
    [Word.i64 (boxNat 13), Word.i64 (boxNat 29)] testInitState
    (fun rw σ' => ValRep .tobject (.nat 42) rw σ'.objs) (fun _ _ => False)
    testInitState_inv hmatch hspec

/-- Pure Tier-P specification for FBIP `isShared`-guarded `goodOsetMod` (both branches agree on
tag-0 `Pair` values with empty scalar payload). -/
@[expose] def goodOsetPEnv : PEnv :=
  fun fn as Q _ =>
    fn = "goodOset" ∧
    ∃ x1 x2 y, as = [.ctor 0 [x1, x2] [], y] ∧ Q (.ctor 0 [y, x2] [])

private theorem goodOsetMod_pModuleOk : PModuleOk goodOsetPEnv goodOsetMod := by
  intro d hd as Q X _ ⟨_, x1, x2, y, has, hq⟩
  subst has
  rcases List.mem_singleton.mp hd with rfl
  let ρO : PValEnv := PValEnv.empty.bindAll
    [{ id := 1, ty := .object, borrow := false }, { id := 2, ty := .object, borrow := false }]
    [.ctor 0 [x1, x2] [], y]
  dsimp only [goodOsetDecl, PWp, PVal.wp]
  refine ⟨rfl, fun b => ?_⟩
  cases b with
  | false =>
    have hb : ((ρO.set 3 (.bool false)) 3).bind PVal.tag? = some 0 := rfl
    change match ((ρO.set 3 (.bool false)) 3).bind PVal.tag? with | _ => _
    rw [hb]; dsimp only [PWpCtorAlts]
    rw [ite_eq_left (by decide)]
    have hx : (ρO.set 3 (.bool false)) 1 = some (.ctor 0 [x1, x2] []) := rfl
    have hy : (ρO.set 3 (.bool false)).evalArg (.var 2) = some y := rfl
    have hset : (PVal.ctor 0 [x1, x2] []).setObj 0 y = some (.ctor 0 [y, x2] []) := rfl
    dsimp only [PWp]; rw [hx, hy]; dsimp only; rw [hset]; dsimp only [PWp]
    have hret : ((ρO.set 3 (.bool false)).set 1 (.ctor 0 [y, x2] [])).evalArg (.var 1) =
        some (.ctor 0 [y, x2] []) := rfl
    rw [hret]; exact hq
  | true =>
    have hb : ((ρO.set 3 (.bool true)) 3).bind PVal.tag? = some 1 := rfl
    change match ((ρO.set 3 (.bool true)) 3).bind PVal.tag? with | _ => _
    rw [hb]; dsimp only [PWpCtorAlts]
    rw [ite_eq_right (by decide), ite_eq_left (by decide)]
    have hop : ((ρO.set 3 (.bool true)) 1).bind (·.getObj? 1) = some x2 := rfl
    dsimp only [PWp, PVal.wp]; rw [hop]; dsimp only [PWp, PVal.wp]
    have hev : ((ρO.set 3 (.bool true)).set 4 x2).evalArgs [.var 2, .var 4] = some [y, x2] := rfl
    have hmk : PVal.mkCtor .object ctorPair [y, x2] = some (.ctor 0 [y, x2] []) := rfl
    rw [hev]; dsimp only; rw [hmk]; dsimp only [PWp]
    have hret : (((ρO.set 3 (.bool true)).set 4 x2).set 5 (.ctor 0 [y, x2] [])).evalArg
        (.var 5) = some (.ctor 0 [y, x2] []) := rfl
    rw [hret]; exact hq

/-- End-to-end `perceus_sound` for FBIP `isShared`-guarded `oset` (`goodOsetMod`). -/
public theorem goodOsetMod_perceus_sound :
    HModuleOk (hOfP goodOsetMod goodOsetPEnv) goodOsetMod :=
  perceus_sound (by decide) (by decide) goodOsetMod_pModuleOk

/-! ## 3. Generic Measure-Indexed Contracts & Recursive `perceus_sound_idx` -/

@[expose] def fuelPEnv (m : LcModule) : Nat → PEnv
  | 0 => PEnv.bot
  | k + 1 => fun fn as Q X =>
    fuelPEnv m k fn as Q X ∨
    ∃ d ∈ m.decls, d.name = fn ∧ as.length = d.params.length ∧
      PWp (modArityOf m) (fuelPEnv m k) PJEnv.empty
        (PValEnv.empty.bindAll d.params as) Q X d.body

private theorem fuelPEnv_le (m : LcModule) (k : Nat) :
    (fuelPEnv m k).le (fuelPEnv m (k + 1)) :=
  fun _ _ _ _ h => Or.inl h

private theorem fuelPEnv_pModuleOkIdx (m : LcModule) (hmwf : perceusModWf m = true) :
    PModuleOkIdx (fuelPEnv m) m := by
  refine ⟨fuelPEnv_le m, fun k d hd as Q X hlen hΔ => ?_⟩
  obtain ⟨hnd, _⟩ := perceusModWf_facts hmwf
  induction k generalizing d as Q X with
  | zero => exact False.elim hΔ
  | succ k ih =>
    rcases hΔ with hprev | ⟨d', hd', hnm, _, hwp⟩
    · have hp := ih d hd as Q X hlen hprev
      refine PWp_env_mono (fun _ _ _ _ h => ?_) hp
      cases k with
      | zero => exact False.elim h
      | succ k' => exact Or.inl h
    · obtain rfl := mod_decl_unique hnd hd hd' hnm
      exact hwp

/-- Measure-indexed `perceus_sound_idx` for tail-recursive `factAccMod`. -/
public theorem factAccMod_perceus_sound_idx :
    HModuleOkIdx (hOfPIdx factAccMod (fuelPEnv factAccMod)) factAccMod :=
  perceus_sound_idx (by decide) (by decide) (fuelPEnv_pModuleOkIdx factAccMod (by decide))

/-- Measure-indexed `perceus_sound_idx` for recursive `listSumMod`. -/
public theorem listSumMod_perceus_sound_idx :
    HModuleOkIdx (hOfPIdx listSumMod (fuelPEnv listSumMod)) listSumMod :=
  perceus_sound_idx (by decide) (by decide) (fuelPEnv_pModuleOkIdx listSumMod (by decide))

/-- Measure-indexed `perceus_sound_idx` for non-tail-recursive `treeSumMod`. -/
public theorem treeSumMod_perceus_sound_idx :
    HModuleOkIdx (hOfPIdx treeSumMod (fuelPEnv treeSumMod)) treeSumMod :=
  perceus_sound_idx (by decide) (by decide) (fuelPEnv_pModuleOkIdx treeSumMod (by decide))

/-- Acyclic `PEvalInf`-backed `perceus_sound` for recursive `listSumMod`. -/
public theorem listSumMod_perceus_sound :
    HModuleOk (hOfP listSumMod (PEvalInf listSumMod false)) listSumMod :=
  perceus_sound (by decide) (by decide) (PModuleOk_PEvalInf (by decide) (by
    intro d hd; rcases List.mem_singleton.mp hd with rfl; rfl) false)

/-- Acyclic `PEvalInf`-backed `perceus_sound` for recursive `treeSumMod`. -/
public theorem treeSumMod_perceus_sound :
    HModuleOk (hOfP treeSumMod (PEvalInf treeSumMod false)) treeSumMod :=
  perceus_sound (by decide) (by decide) (PModuleOk_PEvalInf (by decide) (by
    intro d hd; rcases List.mem_singleton.mp hd with rfl; rfl) false)

@[expose] def myFact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * myFact n

private theorem myFact_pos (n : Nat) : 0 < myFact n := by
  induction n with
  | zero => decide
  | succ m ih => exact Nat.mul_pos (Nat.succ_pos m) ih

@[expose] def factAccResIdx : Nat → PResEnv
  | 0 => PResEnv.bot
  | k + 1 => fun fn pvs rem wr rcr Pr _ =>
    fn = factAccDecl.name ∧
    ∃ n acc : Nat,
      n < k + 1 ∧ n < 2 ^ 63 ∧ acc < 2 ^ 63 ∧ myFact n * acc < 2 ^ 63 ∧
      pvs = [.nat n, .nat acc] ∧ Pr (.nat (myFact n * acc)) rem wr rcr

@[expose] def faCtx0 : RcCtx := (RcCtx.mk [] [] |>.bindParams factAccDecl.params)
@[expose] def faCtx3 : RcCtx := faCtx0.bindOwned 3 .tagged
@[expose] def faCtx4 : RcCtx := faCtx3.bindOwned 4 .uint8
@[expose] def faCtx5 : RcCtx := faCtx4.bindOwned 5 .tagged
@[expose] def faCtx6 : RcCtx := faCtx5.bindOwned 6 .tobject
@[expose] def faCtx7 : RcCtx := faCtx6.bindOwned 7 .tobject

private theorem factAccResIdx_ok : PResOkIdx factAccResIdx factAccMod := by
  refine ⟨?_, fun k d hd pvs rem wr rcr Pr _ _ hΔ => ?_⟩
  · intro k fn pvs rem wr rcr Pr _ h
    cases k with
    | zero => exact False.elim h
    | succ k =>
      rcases h with ⟨hnm, n, acc, hn, hn63, hacc63, hfac, hpvs, hpr⟩
      exact ⟨hnm, n, acc, Nat.lt_succ_of_lt hn, hn63, hacc63, hfac, hpvs, hpr⟩
  · rcases List.mem_singleton.mp hd with rfl
    cases k with
    | zero => exact False.elim hΔ
    | succ k =>
      rcases hΔ with ⟨_, n, acc, hn, hn63, hacc63, hfac, has, hpr⟩
      subst has
      dsimp only [factAccDecl, PRWp, PRValWp]
      let ρ0 := (PValEnv.empty.bindAll
        [{ id := 1, ty := .tobject, borrow := false },
         { id := 2, ty := .tobject, borrow := false }] [.nat n, .nat acc]).set 3 (.nat 0)
      have hcv4 : checkVal (mkRcModEnv factAccMod) faCtx3 4 .uint8
          (.fap "Nat.decEq" [.var 1, .var 3]) = .ok faCtx4 := rfl
      have hdisj0 : ((mkRcModEnv factAccMod).decls.find? (·.1 == "Nat.decEq")).isSome =
          false := rfl
      have hdeq : primP "Nat.decEq" [.nat n, .nat 0] = some (.bool (n == 0)) := rfl
      refine ⟨by decide, ?_⟩
      change match checkVal (mkRcModEnv factAccMod) faCtx3 4 .uint8
          (.fap "Nat.decEq" [.var 1, .var 3]) with
        | Except.ok ctx' => match ρ0.evalArgs [.var 1, .var 3] with | _ => _
        | Except.error _ => False
      rw [hcv4]; dsimp only
      rw [ite_eq_right (fun h => by cases h),
        ite_eq_right (fun h => by rw [h] at hdisj0; cases hdisj0)]
      rw [hdeq]; dsimp only
      refine ⟨rfl, ⟨hn63, by decide⟩, ?_⟩
      let ρ4 := ρ0.set 4 (.bool (n == 0))
      have hg4 : RcCtx.get? (RcCtx.bindOwned (RcCtx.bindOwned (({ } : RcCtx).bindParams
          [{ id := 1, ty := .tobject }, { id := 2, ty := .tobject }]) 3 .tagged) 4 .uint8) 4 =
          some ({ id := 4, ty := .uint8, noRc := true } : RcVar) := rfl
      have hr4 : (((PValEnv.empty.bindAll
          [{ id := 1, ty := .tobject }, { id := 2, ty := .tobject }] [.nat n, .nat acc]).set
          3 (.nat 0)).set 4 (.bool (n == 0))) 4 = some (.bool (n == 0)) := rfl
      rw [hg4, hr4]; dsimp only [Option.bind, casesResSafe]
      have hfa4 : RcCtx.bindOwned (RcCtx.bindOwned (({ } : RcCtx).bindParams
          [{ id := 1, ty := .tobject }, { id := 2, ty := .tobject }]) 3 .tagged) 4 .uint8 =
          faCtx4 := rfl
      have hsp4 : faCtx4.sharedPreds = [] := rfl
      have hmsb4 : faCtx4.markScalarBranch 4 = faCtx4 := rfl
      rw [hfa4]
      cases n with
      | zero =>
        have htg : (PVal.bool (0 == 0)).tag? = some 1 := rfl
        have hscT : (mkRcModEnv factAccMod).scalarCtors.contains "Bool.true" = true := rfl
        rw [htg]; dsimp only [PRWpCtorAlts]
        rw [ite_eq_right (by decide), ite_eq_left (by decide)]
        refine ⟨(by dsimp only [PVal.bool]; exact Or.inl rfl), fun _ => rfl, ?_⟩
        rw [hscT, hsp4, hmsb4, ite_eq_left rfl]; dsimp only [Option.map, List.find?, PRWp]
        obtain ⟨_, hcons⟩ : ∃ c, faCtx4.consumeVar 1 1 = .ok c := ⟨_, rfl⟩
        rw [hcons]; dsimp only
        refine ⟨?_, ?_⟩
        · dsimp only [safeNonColdDec]
          have hg1 : faCtx4.get? 1 = some ({ id := 1, ty := .tobject, owned := 1 } : RcVar) := rfl
          have hr1 : (((PValEnv.empty.bindAll
              [{ id := 1, ty := .tobject }, { id := 2, ty := .tobject }] [.nat 0, .nat acc]).set
              3 (.nat 0)).set 4 (.bool (0 == 0))) 1 = some (.nat 0) := rfl
          rw [hg1, hr1]; exact Or.inr (Or.inr (Or.inl rfl))
        · have hret : (((PValEnv.empty.bindAll
              [{ id := 1, ty := .tobject }, { id := 2, ty := .tobject }] [.nat 0, .nat acc]).set
              3 (.nat 0)).set 4 (.bool (0 == 0))).evalArg (.var 2) = some (.nat acc) := rfl
          rw [hret]
          simpa [myFact] using hpr
      | succ m =>
        have htg : (PVal.bool ((m + 1) == 0)).tag? = some 0 := rfl
        have hscF : (mkRcModEnv factAccMod).scalarCtors.contains "Bool.false" = true := rfl
        rw [htg]; dsimp only [PRWpCtorAlts]
        rw [ite_eq_left (by decide)]
        refine ⟨(by dsimp only [PVal.bool]; exact Or.inl rfl), fun _ => rfl, ?_⟩
        rw [hscF, hsp4, hmsb4, ite_eq_left rfl]
        dsimp only [Option.map, List.find?, PRWp, PRValWp]
        have hcv5 : checkVal (mkRcModEnv factAccMod) faCtx4 5 .tagged (.lit (.nat 1)) =
            .ok faCtx5 := rfl
        rw [hcv5]; dsimp only
        refine ⟨by decide, ?_⟩
        have hcv6 : checkVal (mkRcModEnv factAccMod) faCtx5 6 .tobject
            (.fap "Nat.sub" [.var 1, .var 5]) = .ok faCtx6 := rfl
        have hdisj_sub : ((mkRcModEnv factAccMod).decls.find? (·.1 == "Nat.sub")).isSome =
            false := rfl
        have hsub : primP "Nat.sub" [.nat (m + 1), .nat 1] = some (.nat m) := by
          change some (PVal.nat (m + 1 - 1)) = some (PVal.nat m); simp
        have hev6 : (((((PValEnv.empty.bindAll
            [{ id := 1, ty := .tobject }, { id := 2, ty := .tobject }]
            [.nat (m + 1), .nat acc]).set 3 (.nat 0)).set 4 (.bool (m + 1 == 0))).set
            5 (.nat 1)).evalArgs [.var 1, .var 5]) = some [.nat (m + 1), .nat 1] := rfl
        rw [hcv6]; dsimp only; rw [hev6]; dsimp only
        rw [ite_eq_right (fun h => by cases h),
          ite_eq_right (fun h => by rw [h] at hdisj_sub; cases hdisj_sub)]
        rw [hsub]; dsimp only
        refine ⟨rfl, ⟨hn63, by decide⟩, ?_⟩
        have hcv7 : checkVal (mkRcModEnv factAccMod) faCtx6 7 .tobject
            (.fap "Nat.mul" [.var 2, .var 1]) = .ok faCtx7 := rfl
        have hdisj_mul : ((mkRcModEnv factAccMod).decls.find? (·.1 == "Nat.mul")).isSome =
            false := rfl
        have hmul : primP "Nat.mul" [.nat acc, .nat (m + 1)] =
            some (.nat (acc * (m + 1))) := rfl
        have hev7 : ((((((PValEnv.empty.bindAll
            [{ id := 1, ty := .tobject }, { id := 2, ty := .tobject }]
            [.nat (m + 1), .nat acc]).set 3 (.nat 0)).set 4 (.bool (m + 1 == 0))).set
            5 (.nat 1)).set 6 (.nat m)).evalArgs [.var 2, .var 1]) =
            some [.nat acc, .nat (m + 1)] := rfl
        rw [hcv7]; dsimp only; rw [hev7]; dsimp only
        rw [ite_eq_right (fun h => by cases h),
          ite_eq_right (fun h => by rw [h] at hdisj_mul; cases hdisj_mul)]
        rw [hmul]; dsimp only
        have hmul_eq : myFact m * (acc * (m + 1)) = myFact (m + 1) * acc := by
          dsimp only [myFact]
          calc
            myFact m * (acc * (m + 1))
              = (myFact m * (m + 1)) * acc := by rw [Nat.mul_comm acc (m + 1), Nat.mul_assoc]
            _ = ((m + 1) * myFact m) * acc := by rw [Nat.mul_comm (myFact m)]
        have hmul63 : acc * (m + 1) < 2 ^ 63 := by
          have hle : acc * (m + 1) ≤ myFact m * (acc * (m + 1)) :=
            Nat.le_mul_of_pos_left _ (myFact_pos m)
          omega
        refine ⟨rfl, ⟨hacc63, hn63, hmul63⟩, ?_⟩
        let faCtx7a := faCtx7.put ({ id := 1, ty := .tobject } : RcVar)
        have hcons1 : faCtx7.consumeVar 1 1 = .ok faCtx7a := rfl
        have hcons2 : faCtx7a.consumeVar 2 1 =
            .ok (faCtx7a.put ({ id := 2, ty := .tobject } : RcVar)) := rfl
        rw [hcons1]; dsimp only
        refine ⟨?_, ?_⟩
        · dsimp only [safeNonColdDec]
          have hg1 : faCtx7.get? 1 = some ({ id := 1, ty := .tobject, owned := 1 } : RcVar) := rfl
          have hr1 : ((((((PValEnv.empty.bindAll
              [{ id := 1, ty := .tobject }, { id := 2, ty := .tobject }]
              [.nat (m + 1), .nat acc]).set 3 (.nat 0)).set 4 (.bool (m + 1 == 0))).set
              5 (.nat 1)).set 6 (.nat m)).set 7 (.nat (acc * (m + 1)))) 1 =
              some (.nat (m + 1)) := rfl
          rw [hg1, hr1]; exact Or.inr (Or.inr (Or.inl (by simp [isTaggedPVal, hn63])))
        · rw [hcons2]; dsimp only
          refine ⟨?_, ?_⟩
          · dsimp only [safeNonColdDec]
            have hg2 : faCtx7a.get? 2 =
                some ({ id := 2, ty := .tobject, owned := 1 } : RcVar) := rfl
            have hr2 : ((((((PValEnv.empty.bindAll
                [{ id := 1, ty := .tobject }, { id := 2, ty := .tobject }]
                [.nat (m + 1), .nat acc]).set 3 (.nat 0)).set 4 (.bool (m + 1 == 0))).set
                5 (.nat 1)).set 6 (.nat m)).set 7 (.nat (acc * (m + 1)))) 2 =
                some (.nat acc) := rfl
            rw [hg2, hr2]; exact Or.inr (Or.inr (Or.inl (by simp [isTaggedPVal, hacc63])))
          · obtain ⟨_, hcv8⟩ : ∃ c, checkVal (mkRcModEnv factAccMod)
                (faCtx7a.put ({ id := 2, ty := .tobject } : RcVar)) 8 .tobject
                (.fap "LeanQbe.T.LeanLCNF.FactLoop.factAcc" [.var 6, .var 7]) = .ok c := ⟨_, rfl⟩
            have hf_mem : ((mkRcModEnv factAccMod).decls.find?
                (·.1 == "LeanQbe.T.LeanLCNF.FactLoop.factAcc")).isSome = true := rfl
            have hev8 : ((((((PValEnv.empty.bindAll
                [{ id := 1, ty := .tobject }, { id := 2, ty := .tobject }]
                [.nat (m + 1), .nat acc]).set 3 (.nat 0)).set 4 (.bool (m + 1 == 0))).set
                5 (.nat 1)).set 6 (.nat m)).set 7 (.nat (acc * (m + 1)))).evalArgs
                [.var 6, .var 7] = some [.nat m, .nat (acc * (m + 1))] := rfl
            rw [hcv8]; dsimp only; rw [hev8]; dsimp only
            rw [ite_eq_right (fun h => by cases h), ite_eq_left hf_mem]
            refine ⟨fun r rem' wr' rcr' =>
                r = .nat (myFact m * (acc * (m + 1))) ∧ rem' = rem ∧ wr' = wr ∧ rcr' = rcr,
              fun _ _ _ _ => False,
              ?_, fun r _ _ _ ⟨hr, rfl, rfl, rfl⟩ => ?_, fun _ _ _ _ hf => False.elim hf⟩
            · cases k with
              | zero => omega
              | succ k' =>
                exact ⟨rfl, m, acc * (m + 1), by omega, by omega, hmul63, by omega, rfl,
                  rfl, rfl, rfl, rfl⟩
            · have hret : (((((((PValEnv.empty.bindAll
                  [{ id := 1, ty := .tobject }, { id := 2, ty := .tobject }]
                  [.nat (m + 1), .nat acc]).set 3 (.nat 0)).set 4 (.bool (m + 1 == 0))).set
                  5 (.nat 1)).set 6 (.nat m)).set 7 (.nat (acc * (m + 1)))).set 8 r).evalArg
                  (.var 8) = some r := rfl
              rw [hret, hr, hmul_eq]; dsimp only
              exact hpr

private theorem factAcc_fuelPEnv_eval (n acc : Nat) :
    fuelPEnv factAccMod (n + 1) factAccDecl.name [.nat n, .nat acc]
      (fun r => r = .nat (myFact n * acc)) (fun _ => False) := by
  induction n generalizing acc with
  | zero =>
    refine Or.inr ⟨factAccDecl, List.mem_singleton.mpr rfl, rfl, rfl, ?_⟩
    dsimp only [factAccDecl, PWp, PVal.wp]
    let ρ0 := (PValEnv.empty.bindAll
      [{ id := 1, ty := .tobject, borrow := false },
       { id := 2, ty := .tobject, borrow := false }] [.nat 0, .nat acc]).set 3 (.nat 0)
    have hev0 : ρ0.evalArgs [.var 1, .var 3] = some [.nat 0, .nat 0] := rfl
    change match ρ0.evalArgs [.var 1, .var 3] with | _ => _
    rw [hev0]; dsimp only
    rw [ite_eq_right (fun h => by cases h), ite_eq_left (by rfl)]
    have hp : primP "Nat.decEq" [.nat 0, .nat 0] = some (.bool true) := rfl
    rw [hp]; dsimp only [PWp, PWpCtorAlts]
    have h4 : ((ρ0.set 4 (.bool true)) 4).bind PVal.tag? = some 1 := rfl
    rw [h4]; dsimp only [PWpCtorAlts]
    rw [ite_eq_right (by decide), ite_eq_left rfl]
    have hret : (ρ0.set 4 (.bool true)).evalArg (.var 2) = some (.nat acc) := rfl
    rw [hret]; simp [myFact]
  | succ m ih =>
    refine Or.inr ⟨factAccDecl, List.mem_singleton.mpr rfl, rfl, rfl, ?_⟩
    dsimp only [factAccDecl, PWp, PVal.wp]
    let ρ0 := (PValEnv.empty.bindAll
      [{ id := 1, ty := .tobject, borrow := false },
       { id := 2, ty := .tobject, borrow := false }] [.nat (m + 1), .nat acc]).set 3 (.nat 0)
    have hev0 : ρ0.evalArgs [.var 1, .var 3] = some [.nat (m + 1), .nat 0] := rfl
    change match ρ0.evalArgs [.var 1, .var 3] with | _ => _
    rw [hev0]; dsimp only
    rw [ite_eq_right (fun h => by cases h), ite_eq_left (by rfl)]
    have hp : primP "Nat.decEq" [.nat (m + 1), .nat 0] = some (.bool false) := by
      change some (PVal.bool ((m + 1) == 0)) = some (PVal.bool false); simp
    rw [hp]; dsimp only [PWp, PWpCtorAlts]
    have h4 : ((ρ0.set 4 (.bool false)) 4).bind PVal.tag? = some 0 := rfl
    rw [h4]; dsimp only [PWpCtorAlts]
    rw [ite_eq_left rfl]
    dsimp only [PWp, PVal.wp]
    have hsub : ((ρ0.set 4 (.bool false)).set 5 (.nat 1)).evalArgs [.var 1, .var 5] =
        some [.nat (m + 1), .nat 1] := rfl
    rw [hsub]; dsimp only
    rw [ite_eq_right (fun h => by cases h), ite_eq_left (by rfl)]
    have hsubp : primP "Nat.sub" [.nat (m + 1), .nat 1] = some (.nat m) := by
      change some (PVal.nat (m + 1 - 1)) = some (PVal.nat m); simp
    rw [hsubp]; dsimp only [PWp, PVal.wp]
    have hmul : (((ρ0.set 4 (.bool false)).set 5 (.nat 1)).set 6 (.nat m)).evalArgs
        [.var 2, .var 1] = some [.nat acc, .nat (m + 1)] := rfl
    rw [hmul]; dsimp only
    rw [ite_eq_right (fun h => by cases h), ite_eq_left (by rfl)]
    have hmulp : primP "Nat.mul" [.nat acc, .nat (m + 1)] = some (.nat (acc * (m + 1))) := rfl
    rw [hmulp]; dsimp only [PWp, PVal.wp]
    have hev8 : ((((ρ0.set 4 (.bool false)).set 5 (.nat 1)).set 6 (.nat m)).set 7
        (.nat (acc * (m + 1)))).evalArgs [.var 6, .var 7] =
        some [.nat m, .nat (acc * (m + 1))] := rfl
    rw [hev8]; dsimp only
    rw [ite_eq_right (fun h => by cases h), ite_eq_right (fun h => by cases h)]
    refine ⟨fun r => r = .nat (myFact m * (acc * (m + 1))), fun _ => False,
      ih (acc * (m + 1)), fun r hr => ?_, fun _ hf => False.elim hf⟩
    have hmul_eq : myFact m * (acc * (m + 1)) = myFact (m + 1) * acc := by
      dsimp only [myFact]
      calc
        myFact m * (acc * (m + 1))
          = (myFact m * (m + 1)) * acc := by rw [Nat.mul_comm acc (m + 1), Nat.mul_assoc]
        _ = ((m + 1) * myFact m) * acc := by rw [Nat.mul_comm (myFact m)]
    have hret : (((((ρ0.set 4 (.bool false)).set 5 (.nat 1)).set 6 (.nat m)).set 7
        (.nat (acc * (m + 1)))).set 8 r).evalArg (.var 8) = some r := rfl
    rw [hret, hr, hmul_eq]

/-- Non-vacuous recursive Tier-H execution of `factAcc 5 1 = 120` via `perceus_sound_idx`. -/
public theorem factAccMod_nonvac_hwp :
    HWp (hOfPIdx factAccMod (fuelPEnv factAccMod) 6) testRtBase .tobject HJEnv.empty
      (HValEnv.empty.bindAll factAccDecl.params [Word.i64 (boxNat 5), Word.i64 (boxNat 1)])
      (fun rw σ' => ValRep .tobject (.nat 120) rw σ'.objs)
      (fun _ _ => False) factAccDecl.body testInitState := by
  have hd : factAccDecl ∈ factAccMod.decls := List.mem_singleton.mpr rfl
  have hrc := testInitState_rcInv_twoNat (d := factAccDecl) (br := false) (a := 5) (b := 1) rfl
    (by decide) (by decide)
  have hmatch : paramsMatch factAccDecl.params [Word.i64 (boxNat 5), Word.i64 (boxNat 1)] := by
    simp [paramsMatch, factAccDecl, LcTy.toTTy, LcTy.width, Word.i64]
  have hspec : hOfPIdx factAccMod (fuelPEnv factAccMod) 7 factAccDecl.name
      [Word.i64 (boxNat 5), Word.i64 (boxNat 1)] testInitState
      (fun rw σ' => ValRep .tobject (.nat 120) rw σ'.objs) (fun _ _ => False) := by
    unfold hOfPIdx
    refine ⟨testRtBase, factAccDecl, factAccResIdx, [.nat 5, .nat 1], [], [], 0, 0, 0,
      fun r => r = .nat 120, fun _ => False, fun r _ _ _ => r = .nat 120,
      fun _ _ _ _ => False, hd, rfl, factAccResIdx_ok, hrc, ?_⟩
    refine ⟨(fun _ h => nomatch h), testInitState_resStateInv, rfl,
      ?_, ⟨rfl, 5, 1, by decide, by decide, by decide, by decide, rfl, rfl⟩, ?_, ?_⟩
    · refine fuelPEnv_le factAccMod 6 _ _ _ _ ?_
      have h120 : myFact 5 * 1 = 120 := rfl
      simpa [h120] using factAcc_fuelPEnv_eval 5 1
    · rintro r rw σ' _ _ _ rfl _ _ _ hvr _ _ _; exact hvr
    · intro c _ _ _ _ hf _; exact False.elim hf
  exact factAccMod_perceus_sound_idx.2 7 factAccDecl hd testRtBase
    [Word.i64 (boxNat 5), Word.i64 (boxNat 1)] testInitState
    (fun rw σ' => ValRep .tobject (.nat 120) rw σ'.objs) (fun _ _ => False)
    testInitState_inv hmatch hspec

end

end LeanQbeTest.T.LcnfPerceusTest

/-! ## 4. Compile-Time `#guard` Matrix & `#print axioms` Checks -/

section PerceusGuards
open LeanQbe.T.LeanLCNF LeanQbe.T.LeanLCNF.Sem LeanQbeTest.T.LcnfPerceusTest

-- Positive `RcCheck` and `perceusModWf` checks
#guard RcCheck addNatMod == true
#guard RcCheck factAccMod == true
#guard RcCheck listSumMod == true
#guard RcCheck treeSumMod == true
#guard RcCheck goodOsetMod == true

#guard perceusModWf addNatMod == true
#guard perceusModWf factAccMod == true
#guard perceusModWf listSumMod == true
#guard perceusModWf treeSumMod == true
#guard perceusModWf goodOsetMod == true

-- Negative `RcCheck` / `perceusModWf` controls
#guard RcCheck badLeakMod == false
#guard RcCheck badDoubleDecMod == false
#guard RcCheck badUnguardedOsetMod == false
#guard perceusModWf demoNatStrLcMod == false

-- Functional `PEval` sanity checks
#guard PEval 20 addNatMod addNatDecl.name [.nat 13, .nat 29] false == some (.ret (.nat 42))
#guard PEval 40 factAccMod factAccDecl.name [.nat 5, .nat 1] false == some (.ret (.nat 120))
#guard PEval 30 listSumMod "listSum" [PVal.ofList [.nat 10, .nat 20, .nat 30]] false ==
  some (.ret (.nat 60))
#guard PEval 30 treeSumMod "treeSum"
    [.ctor 1 [.nat 10, .ctor 1 [.nat 3, .ctor 0 [] [], .ctor 0 [] []] [],
      .ctor 1 [.nat 8, .ctor 0 [] [], .ctor 0 [] []] []] []] false ==
  some (.ret (.nat 21))
#guard PEval 20 goodOsetMod "goodOset" [.ctor 0 [.nat 1, .nat 2] [], .nat 99] false ==
  some (.ret (.ctor 0 [.nat 99, .nat 2] []))
#guard PEval 20 goodOsetMod "goodOset" [.ctor 0 [.nat 1, .nat 2] [], .nat 99] true ==
  some (.ret (.ctor 0 [.nat 99, .nat 2] []))

end PerceusGuards

#print axioms LeanQbe.T.LeanLCNF.Sem.perceus_sound
#print axioms LeanQbe.T.LeanLCNF.Sem.perceus_sound_idx
#print axioms LeanQbe.T.LeanLCNF.Sem.perceus_sound_res
#print axioms LeanQbe.T.LeanLCNF.Sem.perceus_sound_res_idx
#print axioms LeanQbeTest.T.LcnfPerceusTest.addNatMod_perceus_sound
#print axioms LeanQbeTest.T.LcnfPerceusTest.addNatMod_nonvac_hwp
#print axioms LeanQbeTest.T.LcnfPerceusTest.goodOsetMod_perceus_sound
#print axioms LeanQbeTest.T.LcnfPerceusTest.factAccMod_perceus_sound_idx
#print axioms LeanQbeTest.T.LcnfPerceusTest.factAccMod_nonvac_hwp
#print axioms LeanQbeTest.T.LcnfPerceusTest.listSumMod_perceus_sound_idx
#print axioms LeanQbeTest.T.LcnfPerceusTest.treeSumMod_perceus_sound_idx
