module

public import LeanQbe.T.LeanLCNF.Sem.LowerSound4
public import LeanQbe.T.LeanLCNF.LcnfC0Demo
public import LeanQbe.T.LeanLCNF.LcnfC0LoopDemo

/-!
# End-to-End Lowering Soundness Smoke Tests (`LcnfLowerSoundTest`)

Validates `LcModule.inFirstOrderFragment` on extracted `LeanLCNF` demo programs
(`demoNatStrLcMod`, `factLoopLcMod`) and instantiates `lowerModule_moduleOk`,
`lowerModule_moduleOk_idx`, `lowerModule_moduleSccOk`, and `lowerModule_semScc`
on a concrete first-order module exercising `.fap`, `.jp`, `.jmp`, and `.ret`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.LcnfLowerSoundTest

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.LeanLCNF
open LeanQbe.T.LeanLCNF.Sem

-- Extracted Lean demo modules satisfy the Phase-1 first-order fragment checks.
theorem demoNatStr_inFirstOrder :
    demoNatStrLcMod.inFirstOrderFragment = true := by decide

theorem factLoop_inFirstOrder :
    factLoopLcMod.inFirstOrderFragment = true := by decide

theorem demoNatStr_checkAcyclic :
    demoNatStrLinkedMod.checkAcyclic = true := by decide

theorem factLoop_checkAcyclic :
    factLoopLinkedMod.checkAcyclic = true := by decide

theorem factLoop_checkCyclic :
    LinkRec.checkCyclic factLoopLinkedMod = true := by decide

def smokeIdDecl : LcDecl :=
  { name := "smoke_id"
    params := [{ id := 0, ty := .uint64 }]
    retTy := .uint64
    body := .ret (.var 0) }

def smokeWrapDecl : LcDecl :=
  { name := "smoke_wrap"
    params := [{ id := 0, ty := .uint64 }]
    retTy := .uint64
    body :=
      .jp 10 [{ id := 1, ty := .uint64 }] (.ret (.var 1))
        (.let_ 2 .uint64 (.fap "smoke_id" [.var 0]) (.jmp 10 [.var 2])) }

def smokeMod : LcModule :=
  { name := "smoke_mod"
    decls := [smokeIdDecl, smokeWrapDecl]
    externs := []
    roots := ["smoke_wrap"]
    snaps := [] }

def smokeTfs : List Frontend.C0.TFlatFn :=
  match lowerModule smokeMod with
  | .ok tfs => tfs
  | .error _ => []

private theorem smokeMod_fo : smokeMod.inFirstOrderFragment = true := by
  decide

private theorem smokeMod_lower : lowerModule smokeMod = .ok smokeTfs := by
  have hok : (lowerModule smokeMod).isOk = true := by decide
  dsimp only [smokeTfs]
  cases h : lowerModule smokeMod with
  | error _ => rw [h] at hok; cases hok
  | ok _ => rfl

private theorem smokeMod_acyc : (linkLcnfWithRtC0 smokeTfs).checkAcyclic = true := by
  decide

private theorem smokeMod_cyc : LinkRec.checkCyclic (linkLcnfWithRtC0 smokeTfs) = true := by
  decide

private theorem smokeMod_noLoop :
    ∀ d ∈ smokeMod.decls, hasSelfTail d.name d.params.length d.body = false := by
  intro d hd
  simp only [smokeMod, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl <;> decide

def smokeIdSpec : HSpec := fun ws σ Q _ =>
  ∃ a : BitVec 64, ws = [⟨i64, a⟩] ∧ Q ⟨i64, a⟩ σ

def smokeDelta : HEnv := fun nm ws σ Q X =>
  if nm = "smoke_id" ∨ nm = "smoke_wrap" then smokeIdSpec ws σ Q X else False

def smokeDeltaIdx : Nat → HEnv
  | 0 => fun nm => if nm = "smoke_id" then smokeIdSpec else fun _ _ _ _ => False
  | _ + 1 => smokeDelta

private theorem smokeDelta_retTyped : HEnv.RetTyped smokeMod smokeDelta := by
  intro d hd as σ Q₁ Q₂ X₁ X₂ hQ _ hS
  simp only [smokeMod, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl <;>
    simp only [smokeDelta, smokeIdDecl, smokeWrapDecl, smokeIdSpec] at hS ⊢ <;>
    rcases hS with ⟨a, rfl, hq⟩ <;>
    exact ⟨a, rfl, hQ ⟨i64, a⟩ σ rfl hq⟩

private theorem smokeDeltaIdx_retTyped : ∀ k, HEnv.RetTyped smokeMod (smokeDeltaIdx k) := by
  intro k
  cases k with
  | zero =>
    intro d hd as σ Q₁ Q₂ X₁ X₂ hQ _ hS
    simp only [smokeMod, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · simp only [smokeDeltaIdx, smokeIdDecl, ↓reduceIte, smokeIdSpec] at hS ⊢
      rcases hS with ⟨a, rfl, hq⟩
      exact ⟨a, rfl, hQ ⟨i64, a⟩ σ rfl hq⟩
    · simp only [smokeDeltaIdx, smokeWrapDecl] at hS
      cases hS
  | succ _ => exact smokeDelta_retTyped

private theorem smokeId_body_wp {Δc : HEnv} {rt : BitVec 64} {as : List Word}
    {σ : HState} {Q : HPost} {X : HXPost}
    (hcall : smokeIdSpec as σ Q X) :
    HWp Δc rt .uint64 HJEnv.empty (HValEnv.empty.bindAll smokeIdDecl.params as)
      Q X smokeIdDecl.body σ := by
  rcases hcall with ⟨a, rfl, hQ⟩
  simp only [smokeIdDecl, HValEnv.bindAll, HValEnv.empty, HValEnv.set,
    HWp, HValEnv.evalArgAt]
  exact hQ

private theorem smokeWrap_body_wp {Δc : HEnv} {rt : BitVec 64} {as : List Word}
    {σ : HState} {Q : HPost} {X : HXPost}
    (hcallee : ∀ ws σ' Q' X', smokeIdSpec ws σ' Q' X' → Δc "smoke_id" ws σ' Q' X')
    (hcall : smokeIdSpec as σ Q X) :
    HWp Δc rt .uint64 HJEnv.empty (HValEnv.empty.bindAll smokeWrapDecl.params as)
      Q X smokeWrapDecl.body σ := by
  rcases hcall with ⟨a, rfl, hQ⟩
  simp only [smokeWrapDecl, HValEnv.bindAll]
  rw [HWp.eq_2]
  intro J hJ
  rw [HWp.eq_1, HVal.wp.eq_10]
  have hnPrim : isPrimName "smoke_id" = false := by decide
  simp only [HValEnv.evalArgsOwn.eq_2, HValEnv.evalArgsOwn.eq_1, HValEnv.evalArgOwn,
    HValEnv.set, hnPrim, Bool.false_eq_true, ↓reduceIte]
  refine ⟨(fun r σ' => r = ⟨i64, a⟩ ∧ σ' = σ), (fun _ _ => False),
    hcallee [⟨i64, a⟩] σ _ _ ⟨a, rfl, rfl, rfl⟩, ?_, (fun _ _ hF => hF.elim)⟩
  intro r1 σ1 ⟨hrEq, hσEq⟩
  rw [hrEq, hσEq]
  refine ⟨⟨i64, a⟩, rfl, ?_⟩
  rw [HWp.eq_3]
  simp only [HValEnv.evalArgsOwn.eq_2, HValEnv.evalArgsOwn.eq_1, HValEnv.evalArgOwn,
    HValEnv.set, HJEnv.set]
  refine hJ [⟨i64, a⟩] σ ?_ ?_
  · simp [paramsMatch]; rfl
  · rw [HWp.eq_5]
    simp only [HValEnv.evalArgAt]
    exact hQ

private theorem smokeMod_hOk : HModuleOk smokeDelta smokeMod := by
  intro d hd rt as σ Q X _ _ hcall
  simp only [smokeMod, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · simp only [smokeDelta, smokeIdDecl] at hcall
    exact smokeId_body_wp hcall
  · simp only [smokeDelta, smokeWrapDecl] at hcall
    exact smokeWrap_body_wp
      (fun ws σ' Q' X' h => by simp only [smokeDelta]; exact h) hcall

private theorem smokeMod_hOkIdx : HModuleOkIdx smokeDeltaIdx smokeMod := by
  refine ⟨fun k => ?_, fun k d hd rt as σ Q X _ _ hcall => ?_⟩
  · cases k with
    | zero =>
      intro f ws σ P E hf
      by_cases hId : f = "smoke_id"
      · subst hId
        simp only [smokeDeltaIdx, smokeDelta] at hf ⊢
        exact hf
      · simp only [smokeDeltaIdx, hId, ↓reduceIte] at hf
    | succ _ => exact HEnv.le_refl _
  · simp only [smokeMod, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · cases k with
      | zero =>
        simp only [smokeDeltaIdx, smokeIdDecl] at hcall
        exact smokeId_body_wp hcall
      | succ _ =>
        simp only [smokeDeltaIdx, smokeDelta, smokeIdDecl] at hcall
        exact smokeId_body_wp hcall
    · cases k with
      | zero =>
        simp only [smokeDeltaIdx, smokeWrapDecl] at hcall
        cases hcall
      | succ k' =>
        simp only [smokeDeltaIdx, smokeDelta, smokeWrapDecl] at hcall
        refine smokeWrap_body_wp (fun ws σ' Q' X' h => ?_) hcall
        cases k' with
        | zero => simp only [smokeDeltaIdx]; exact h
        | succ _ => simp only [smokeDeltaIdx, smokeDelta]; exact h

/-- Concrete `ModuleOk` theorem instantiated via `lowerModule_moduleOk`. -/
theorem smokeMod_moduleOk :
    ModuleOk (linkRtC0Env (liftEnv smokeMod smokeDelta)) (linkLcnfWithRtC0 smokeTfs) :=
  lowerModule_moduleOk smokeMod_fo smokeMod_lower smokeMod_acyc
    smokeDelta_retTyped smokeMod_hOk smokeMod_noLoop

/-- Concrete indexed `ModuleOk` theorem instantiated via `lowerModule_moduleOk_idx`. -/
theorem smokeMod_moduleOk_idx :
    ModuleOk (linkRtC0Env (liftEnv smokeMod (smokeDeltaIdx 1))) (linkLcnfWithRtC0 smokeTfs) :=
  lowerModule_moduleOk_idx smokeMod_fo smokeMod_lower smokeMod_acyc
    smokeDeltaIdx_retTyped smokeMod_hOkIdx 1

/-- Concrete `ModuleSccOk` theorem instantiated via `lowerModule_moduleSccOk`. -/
theorem smokeMod_moduleSccOk :
    LinkScc.ModuleSccOk LinkScc.natRecIdx (lowerSccRecEnv smokeMod smokeDeltaIdx)
      (fun _ _ _ _ _ _ _ => False) false (linkLcnfWithRtC0 smokeTfs) :=
  lowerModule_moduleSccOk smokeMod_fo smokeMod_lower smokeMod_cyc
    smokeDeltaIdx_retTyped smokeMod_hOkIdx

/-- Concrete `Env.semScc` theorem instantiated via `lowerModule_semScc`. -/
theorem smokeMod_semScc :
    HCallEnvOk smokeMod (smokeDeltaIdx 1)
      (Env.semScc (linkLcnfWithRtC0 smokeTfs) (fun _ _ _ _ _ _ _ => False)) :=
  (lowerModule_semScc smokeMod_fo smokeMod_lower smokeMod_cyc
    smokeDeltaIdx_retTyped smokeMod_hOkIdx).1 1

#print axioms LeanQbe.T.LeanLCNF.Sem.lowerCode_sound
#print axioms LeanQbe.T.LeanLCNF.Sem.lowerDecl_sound
#print axioms LeanQbe.T.LeanLCNF.Sem.lowerDecl_sound_loop
#print axioms LeanQbe.T.LeanLCNF.Sem.lowerModule_moduleOk
#print axioms LeanQbe.T.LeanLCNF.Sem.lowerModule_moduleOk_idx
#print axioms LeanQbe.T.LeanLCNF.Sem.lowerModule_moduleSccOk
#print axioms LeanQbe.T.LeanLCNF.Sem.lowerModule_semScc
#print axioms smokeMod_moduleOk
#print axioms smokeMod_moduleOk_idx
#print axioms smokeMod_moduleSccOk
#print axioms smokeMod_semScc

end LeanQbeTest.T.LcnfLowerSoundTest
