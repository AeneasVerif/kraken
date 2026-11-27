module

public import LeanQbe.T.LeanLCNF.Sem.LowerSound2c
import LeanQbe.T.OpsLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.LeanLCNF.Sem.SpecNorm

/-!
# Tier-H `Array.*`, Miscellaneous `LMMono`, `objTagNat`, and `externPrim` Soundness (`LowerSound2d`)

Part 2 of the container / external-primitive Stage 2 proofs on top of `LowerSound2c`:
1. `Array.*` monotonicity and simulation (`arrayPrim_mono`, `arrayPrim_sound`).
2. `LMMono` monotonicity lemmas for `floatPrim`, `charPrim`, `intPrim`, `int64Prim`,
   `objTagNat`, and `externPrim`.
3. `objTagNat_wp` and top-level `externPrim_sound` covering every `isPhase1Prim` operation.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Frontend.C0
open Std.ExtHashMap

/-! ## 1. `Array.*` Monotonicity & Simulation (`arrayPrim_sound`) -/

theorem arrayPrim_mono {rt : LArg} {op : String} {args : List LArg} {k : LArg → LM LExpr}
    (hk : ∀ r, LMMono (k r)) : LMMono (arrayPrim rt op args k) := by
  unfold arrayPrim
  dsimp only
  split
  all_goals first
    | exact lfail_mono
    | exact hk _
    | exact loadAt_mono fun _ => boxSmall_mono hk
    | exact loadAt_mono hk
    | exact rtCall1_mono hk

private theorem isPhase1ArrayPrim_mem {op : String} {arity : Nat} {retTy : LcTy}
    (h : isPhase1ArrayPrim op arity retTy = true) :
    (op = "empty" ∧ arity = 1) ∨
    (op = "size" ∧ arity = 2) ∨
    (op = "usize" ∧ arity = 2) ∨
    (op = "mkEmpty" ∧ arity = 2) ∨
    (op = "emptyWithCapacity" ∧ arity = 2) ∨
    (op = "push" ∧ arity = 3) ∨
    (op = "get!Internal" ∧ arity = 4) ∨
    (op = "get!InternalBorrowed" ∧ arity = 4) ∨
    (op = "propagateMark" ∧ arity = 4) ∨
    (op = "set!" ∧ arity = 4) ∨
    (op = "set" ∧ arity = 5) := by
  unfold isPhase1ArrayPrim at h
  split at h <;> simp_all

private theorem arrayMkEmpty_rtCall1_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg capArg : LArg}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt cap : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost} {X : HXPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (rtCall1 rtArg "lcnf_array_mk_empty" [capArg] 64 k).run n = .ok (e, n'))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (hcapId : argIdsBelow capArg n) (hcapEv : EvalRtArg ρ capArg cap)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem) (hX : HXPostRel rt R X XT)
    (hpre :
      let c := if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0
      if c ≤ arrMaxCap then
        canAllocBytes σ.st (arrAllocBytes c) ∧
        ∀ p st', p ≠ 0#64 → p.toNat % 8 = 0 → st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem →
          let arrObj := mkArrObj p 1#32 c []
          ArrCanon arrObj → K (Word.i64 p) { σ with st := st', objs := arrObj :: σ.objs }
      else X panicCapCode σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (nr : Nat)
        (res : BitVec 64) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, n') → argIdsBelow r nr → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' i64 r = some res → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K (Word.i64 res) σ' → LExpr.wp Γ QT XT ek ρ' J m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  let scrFrame : Mem 64 → Prop :=
    cell64 (rt + 33672#64) σ.scr ⋆
    cell64 (rt + 33680#64) (BitVec.ofNat 64 σ.scrLimbs.length) ⋆
    array64 σ.scr σ.scrLimbs ⋆ lcnfHeap σ.objs ⋆ R
  have hm' : (rtC0Inv rt σ.st ⋆ scrFrame) mem := by
    rw [hstate_mem_unfold] at hm; exact sep_cast hm (by dsimp only [scrFrame]; ac_rfl)
  let P : Post [i64] := fun (p, ()) m' =>
    ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m' ∧ K (Word.i64 p) σ'
  have hspec : lcnfArrayMkEmptySpec (rt, cap, ()) mem P XT := by
    dsimp only [lcnfArrayMkEmptySpec] at hpre ⊢
    by_cases hc : (if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0) ≤ arrMaxCap
    · rw [ite_eq_left hc] at hpre ⊢
      refine ⟨σ.st, scrFrame, hpre.1, hm', fun p st' m' hp0 hp8 hpm hrem hcan hmObj => ?_⟩
      let c := if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0
      let arrObj := mkArrObj p 1#32 c []
      let σ' : HState := { σ with st := st', objs := arrObj :: σ.objs }
      have hmPost : (σ'.mem rt ⋆ R) m' := by
        rw [hstate_mem_unfold]; dsimp only [σ']; rw [lcnfHeap.eq_2]
        exact sep_cast hmObj (by dsimp only [scrFrame]; ac_rfl)
      exact ⟨σ', hinv_of_preservesMeta hinv hpm, hmPost, hpre.2 p st' hp0 hp8 hpm hrem hcan⟩
    · rw [ite_eq_right hc] at hpre ⊢
      exact hX panicCapCode σ hpre mem hm
  have hsig : ("lcnf_array_mk_empty", [i64, i64], [i64]) ∈ rtCoreCallSigs := by decide
  refine rtCall1_wp hrun hrt hnrt (by simp [hcapId])
    (evalRtArgs_cons hcapEv (evalRtArgs_nil ρ))
    (hΓ.rt hsig (rtR2Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR2Env_lcnf_array_mk_empty hspec)))
    (fun _ _ _ _ h => h) ?_
  intro ret m' ⟨σ', hinv', hm'', hK⟩ r ek ρ' nr hnr hek hr hagr hrEv
  have hrEv' : LArg.eval ρ' i64 r = some ret := by simpa [BitVec.setWidth_eq] using hrEv
  exact hk r ek ρ' nr ret σ' m' hnr hek hr hagr hrEv' hinv' hm'' hK

private theorem arrayPush_rtCall1_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg arrArg vArg : LArg}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt arr v : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost} {X : HXPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (rtCall1 rtArg "lcnf_array_push" [arrArg, vArg] 64 k).run n = .ok (e, n'))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (harrId : argIdsBelow arrArg n) (harrEv : EvalRtArg ρ arrArg arr)
    (hvId : argIdsBelow vArg n) (hvEv : EvalRtArg ρ vArg v)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem) (hX : HXPostRel rt R X XT)
    (hpre : ∃ (idx : Nat) (hidx : idx < σ.objs.length),
      let arrObj := σ.objs[idx]'hidx
      let childObjs := σ.objs.eraseIdx idx
      arrObj.addr = arr ∧ ArrCanon arrObj ∧ (∀ y ∈ childObjs, y.Wf) ∧
      (arrObj.rc ≠ 1#32 →
        (∀ f ∈ arrObj.fields, (f &&& 1#64) = 0#64 → ∃ y ∈ childObjs, y.addr = f) ∧
        (∀ y ∈ childObjs, 0 < y.rc.toInt →
          y.rc.toInt + (arrObj.fields.count y.addr : Int) < 2147483648)) ∧
      if arrObj.cap ≤ arrObj.fields.length ∧ arrMaxCap ≤ arrObj.cap then X panicCapCode σ
      else
        let newCap := arrEnsureCap arrObj.fields.length arrObj.cap 1#64
        let needAlloc := arrObj.rc ≠ 1#32 ∨ arrObj.fields.length ≥ arrObj.cap
        (needAlloc → canAllocBytes σ.st (arrAllocBytes newCap)) ∧
        ∀ r st' childObjs',
          r ≠ 0#64 → r.toNat % 8 = 0 → st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem →
          (arrObj.rc = 1#32 → arrObj.fields.length < arrObj.cap → r = arr ∧ st' = σ.st) →
          let rObj := mkArrObj r 1#32 newCap (arrObj.fields ++ [v])
          ArrCanon rObj →
          (arrObj.rc = 1#32 → childObjs' = childObjs) →
          (arrObj.rc ≠ 1#32 → childObjs' = incChildrenObjs arrObj.fields childObjs) →
          let objs' :=
            if arrObj.rc = 1#32 then rObj :: childObjs'
            else rObj :: arrObj.withRc (decNonExclRc arrObj.rc) :: childObjs'
          K (Word.i64 r) { σ with st := st', objs := objs' })
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (nr : Nat)
        (res : BitVec 64) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, n') → argIdsBelow r nr → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' i64 r = some res → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K (Word.i64 res) σ' → LExpr.wp Γ QT XT ek ρ' J m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  rcases hpre with ⟨idx, hidx, ha, hc, hch, hrc, hbody⟩
  let arrObj := σ.objs[idx]'hidx
  let childObjs := σ.objs.eraseIdx idx
  let scrFrame : Mem 64 → Prop :=
    cell64 (rt + 33672#64) σ.scr ⋆
    cell64 (rt + 33680#64) (BitVec.ofNat 64 σ.scrLimbs.length) ⋆
    array64 σ.scr σ.scrLimbs ⋆ R
  have hm' : (rtC0Inv rt σ.st ⋆ lcnfObjMem arrObj ⋆ lcnfHeap childObjs ⋆ scrFrame) mem := by
    rw [hstate_mem_unfold, lcnfHeap_eraseIdx σ.objs hidx] at hm
    exact sep_cast hm (by dsimp only [scrFrame, arrObj, childObjs]; ac_rfl)
  let P : Post [i64] := fun (r, ()) m' =>
    ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m' ∧ K (Word.i64 r) σ'
  have hspec : lcnfArrayPushSpec (rt, arr, v, ()) mem P XT := by
    refine ⟨σ.st, arrObj, childObjs, scrFrame, ha, hc, hch, hm', hrc, ?_⟩
    dsimp only at hbody ⊢
    by_cases hp : arrObj.cap ≤ arrObj.fields.length ∧ arrMaxCap ≤ arrObj.cap
    · rw [ite_eq_left hp] at hbody ⊢; exact hX panicCapCode σ hbody mem hm
    · rw [ite_eq_right hp] at hbody ⊢
      rcases hbody with ⟨hneed, hpost⟩
      refine ⟨hneed, fun r st' childObjs' m' hr0 hr8 hpm hrem hIn hcan hC1 hCn hmObj => ?_⟩
      let newCap := arrEnsureCap arrObj.fields.length arrObj.cap 1#64
      let rObj := mkArrObj r 1#32 newCap (arrObj.fields ++ [v])
      let objs' :=
        if arrObj.rc = 1#32 then rObj :: childObjs'
        else rObj :: arrObj.withRc (decNonExclRc arrObj.rc) :: childObjs'
      let σ' : HState := { σ with st := st', objs := objs' }
      have hmPost : (σ'.mem rt ⋆ R) m' := by
        rw [hstate_mem_unfold]
        dsimp only [σ', objs']
        by_cases hrc1 : arrObj.rc = 1#32
        · simp only [hrc1, ↓reduceIte] at hmObj ⊢
          rw [lcnfHeap.eq_2]
          exact sep_cast hmObj (by dsimp only [scrFrame, newCap, rObj]; ac_rfl)
        · simp only [hrc1, ↓reduceIte] at hmObj ⊢
          rw [lcnfHeap.eq_2, lcnfHeap.eq_2]
          exact sep_cast hmObj (by dsimp only [scrFrame, newCap, rObj, arrObj]; ac_rfl)
      exact ⟨σ', hinv_of_preservesMeta hinv hpm, hmPost,
        hpost r st' childObjs' hr0 hr8 hpm hrem hIn hcan hC1 hCn⟩
  have hsig : ("lcnf_array_push", [i64, i64, i64], [i64]) ∈ rtCoreCallSigs := by decide
  refine rtCall1_wp hrun hrt hnrt (by simp [harrId, hvId])
    (evalRtArgs_cons harrEv (evalRtArgs_cons hvEv (evalRtArgs_nil ρ)))
    (hΓ.rt hsig (rtR2Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR2Env_lcnf_array_push hspec)))
    (fun _ _ _ _ h => h) ?_
  intro ret m' ⟨σ', hinv', hm'', hK⟩ r ek ρ' nr hnr hek hr hagr hrEv
  have hrEv' : LArg.eval ρ' i64 r = some ret := by simpa [BitVec.setWidth_eq] using hrEv
  exact hk r ek ρ' nr ret σ' m' hnr hek hr hagr hrEv' hinv' hm'' hK

private theorem arrayGet_rtCall1_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg dvArg arrArg idxArg : LArg} {mode : Nat}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt dv arr idx : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost}
    (hΓ : HCallEnvOk m Δ Γ) (hmode : mode = 0 ∨ mode = 1)
    (hrun : (rtCall1 rtArg "lcnf_array_get" [dvArg, arrArg, idxArg, imm64 mode] 64 k).run n =
      .ok (e, n'))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (hdvId : argIdsBelow dvArg n) (hdvEv : EvalRtArg ρ dvArg dv)
    (harrId : argIdsBelow arrArg n) (harrEv : EvalRtArg ρ arrArg arr)
    (hidxId : argIdsBelow idxArg n) (hidxEv : EvalRtArg ρ idxArg idx)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hpre : ∃ arrObj ∈ σ.objs, arrObj.addr = arr ∧ ArrCanon arrObj ∧ (∀ o ∈ σ.objs, o.Wf) ∧
      let ret :=
        if (idx &&& 1#64) ≠ 0#64 then
          if h : (idx >>> 1).toNat < arrObj.fields.length then arrObj.fields[(idx >>> 1).toNat]
          else dv
        else dv
      (mode = 0 →
        ((ret ≠ 0#64 ∧ (ret &&& 1#64) = 0#64) → ∃ o ∈ σ.objs, o.addr = ret) ∧
        let objs' :=
          if ret = 0#64 ∨ (ret &&& 1#64) ≠ 0#64 then σ.objs
          else σ.objs.map fun o => if o.addr = ret then o.withRc (incRcVal o.rc) else o
        K (Word.i64 ret) { σ with objs := objs' }) ∧
      (mode = 1 → K (Word.i64 ret) σ))
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (nr : Nat)
        (res : BitVec 64) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, n') → argIdsBelow r nr → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' i64 r = some res → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K (Word.i64 res) σ' → LExpr.wp Γ QT XT ek ρ' J m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  rcases hpre with ⟨arrObj, hmArr, haArr, hcArr, hwf, hbody⟩
  let scrFrame : Mem 64 → Prop :=
    rtC0Inv rt σ.st ⋆ cell64 (rt + 33672#64) σ.scr ⋆
    cell64 (rt + 33680#64) (BitVec.ofNat 64 σ.scrLimbs.length) ⋆
    array64 σ.scr σ.scrLimbs ⋆ R
  have hm' : (lcnfHeap σ.objs ⋆ scrFrame) mem := by
    rw [hstate_mem_unfold] at hm; exact sep_cast hm (by dsimp only [scrFrame]; ac_rfl)
  let P : Post [i64] := fun (r, ()) m' =>
    ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m' ∧ K (Word.i64 r) σ'
  have hspec : lcnfArrayGetSpec (rt, dv, arr, idx, BitVec.ofNat 64 mode, ()) mem P
      (fun _ _ _ _ => False) := by
    refine ⟨arrObj, σ.objs, scrFrame, hmArr, haArr, hcArr, hwf, hm', ?_⟩
    dsimp only at hbody ⊢
    have hnunb : ¬ ((BitVec.ofNat 64 mode &&& 2#64) ≠ 0#64) := by
      rcases hmode with rfl | rfl <;> decide
    have hnotPan : ¬ ((BitVec.ofNat 64 mode &&& 2#64) ≠ 0#64 ∧
        arrObj.fields.length ≤ idx.toNat) := fun h => hnunb h.1
    rw [ite_eq_right hnotPan]
    simp only [hnunb, ↓reduceIte]
    rcases hmode with rfl | rfl
    · have hnb : ¬ ((BitVec.ofNat 64 0 &&& 1#64) ≠ 0#64) := by decide
      simp only [hnb, false_or, not_false_eq_true, true_and]
      rcases hbody.1 rfl with ⟨hretMem, hK⟩
      refine ⟨hretMem, fun m' hbmem hmObj => ?_⟩
      let ret :=
        if (idx &&& 1#64) ≠ 0#64 then
          if h : (idx >>> 1).toNat < arrObj.fields.length then arrObj.fields[(idx >>> 1).toNat]
          else dv
        else dv
      let objs' :=
        if ret = 0#64 ∨ (ret &&& 1#64) ≠ 0#64 then σ.objs
        else σ.objs.map fun o => if o.addr = ret then o.withRc (incRcVal o.rc) else o
      let σ' : HState := { σ with objs := objs' }
      have hmPost : (σ'.mem rt ⋆ R) m' := by
        rw [hstate_mem_unfold]
        dsimp only [σ', objs', ret]
        exact sep_cast hmObj (by dsimp only [scrFrame]; ac_rfl)
      exact ⟨σ', hinv, hmPost, hK⟩
    · refine ⟨fun h => absurd (by decide : (1#64 &&& 1#64) ≠ 0#64) h.1, fun m' hbmem _ => ?_⟩
      have hmEq : m' = mem := hbmem (by decide)
      rw [hmEq]
      exact ⟨σ, hinv, hm, hbody.2 rfl⟩
  have hsig : ("lcnf_array_get", [i64, i64, i64, i64, i64], [i64]) ∈ rtCoreCallSigs := by decide
  have hids : ∀ a ∈ [dvArg, arrArg, idxArg, imm64 mode], argIdsBelow a n := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact hdvId
    · exact harrId
    · exact hidxId
    · exact argIdsBelow_imm _ _ _
  refine rtCall1_wp hrun hrt hnrt hids
    (evalRtArgs_cons hdvEv (evalRtArgs_cons harrEv
      (evalRtArgs_cons hidxEv (evalRtArgs_cons (evalRtArg_imm64 ρ mode) (evalRtArgs_nil ρ)))))
    (hΓ.rt hsig (rtR2Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR2Env_lcnf_array_get hspec)))
    (fun _ _ _ _ hf => False.elim hf) ?_
  intro ret m' ⟨σ', hinv', hm'', hK⟩ r ek ρ' nr hnr hek hr hagr hrEv
  have hrEv' : LArg.eval ρ' i64 r = some ret := by simpa [BitVec.setWidth_eq] using hrEv
  exact hk r ek ρ' nr ret σ' m' hnr hek hr hagr hrEv' hinv' hm'' hK

private theorem arraySet_rtCall1_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg arrArg idxArg vArg : LArg}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt arr idx v : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (rtCall1 rtArg "lcnf_array_set" [arrArg, idxArg, vArg, imm64 0] 64 k).run n =
      .ok (e, n'))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (harrId : argIdsBelow arrArg n) (harrEv : EvalRtArg ρ arrArg arr)
    (hidxId : argIdsBelow idxArg n) (hidxEv : EvalRtArg ρ idxArg idx)
    (hvId : argIdsBelow vArg n) (hvEv : EvalRtArg ρ vArg v)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hpre : HArraySetWp arr idx v K σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (nr : Nat)
        (res : BitVec 64) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, n') → argIdsBelow r nr → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' i64 r = some res → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K (Word.i64 res) σ' → LExpr.wp Γ QT XT ek ρ' J m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  rcases hpre with ⟨idxObj, hidx, ha, hc, hnotIn, hwf, hcl, hbody⟩
  let scrFrame : Mem 64 → Prop :=
    cell64 (rt + 33672#64) σ.scr ⋆
    cell64 (rt + 33680#64) (BitVec.ofNat 64 σ.scrLimbs.length) ⋆
    array64 σ.scr σ.scrLimbs ⋆ R
  have hm' : (rtC0Inv rt σ.st ⋆ lcnfHeap σ.objs ⋆ scrFrame) mem := by
    rw [hstate_mem_unfold] at hm; exact sep_cast hm (by dsimp only [scrFrame]; ac_rfl)
  let P : Post [i64] := fun (r, ()) m' =>
    ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m' ∧ K (Word.i64 r) σ'
  have hspec : lcnfArraySetSpec (rt, arr, idx, v, 0#64, ()) mem P (fun _ _ _ _ => False) := by
    refine ⟨σ.st, σ.objs, idxObj, hidx, scrFrame, ha, hc, hnotIn, hwf, hcl, hm', ?_⟩
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    dsimp only at hbody ⊢
    by_cases hlt : (if ¬(idx &&& 1#64 = 0#64) then (idx >>> 1).toNat
        else σ.objs[idxObj].fields.length) < σ.objs[idxObj].fields.length
    · rw [dite_eq_left hlt]
      have hlt' : (if (idx &&& 1#64) ≠ 0#64 then (idx >>> 1).toNat
          else σ.objs[idxObj].fields.length) < σ.objs[idxObj].fields.length := hlt
      rw [dite_eq_left hlt'] at hbody
      rcases hbody with ⟨h1, h2, h3, hpost⟩
      refine ⟨h1, h2, h3, fun r st' objs' m' hr0 hr8 hpm hrem hIn rObj mid1 mid2 hro hm1 hm2
          hm2eq hdec hmObj => ?_⟩
      let σ' : HState := { σ with st := st', objs := objs' }
      have hmPost : (σ'.mem rt ⋆ R) m' := by
        rw [hstate_mem_unfold]; exact sep_cast hmObj (by dsimp only [scrFrame, σ']; ac_rfl)
      exact ⟨σ', hinv_of_preservesMeta hinv hpm, hmPost,
        hpost r st' objs' hr0 hr8 hpm hrem hIn rObj mid1 mid2 hro hm1 hm2 hm2eq hdec⟩
    · rw [dite_eq_right hlt]
      have hlt' : ¬((if (idx &&& 1#64) ≠ 0#64 then (idx >>> 1).toNat
          else σ.objs[idxObj].fields.length) < σ.objs[idxObj].fields.length) := hlt
      rw [dite_eq_right hlt'] at hbody
      rcases hbody with ⟨hvOk, hpost⟩
      refine ⟨hvOk, fun st' objs' m' hpm hrem hdec hmObj => ?_⟩
      let σ' : HState := { σ with st := st', objs := objs' }
      have hmPost : (σ'.mem rt ⋆ R) m' := by
        rw [hstate_mem_unfold]; exact sep_cast hmObj (by dsimp only [scrFrame, σ']; ac_rfl)
      exact ⟨σ', hinv_of_preservesMeta hinv hpm, hmPost, hpost st' objs' hpm hrem hdec⟩
  have hsig : ("lcnf_array_set", [i64, i64, i64, i64, i64], [i64]) ∈ rtCoreCallSigs := by decide
  have hids : ∀ a ∈ [arrArg, idxArg, vArg, imm64 0], argIdsBelow a n := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact harrId
    · exact hidxId
    · exact hvId
    · exact argIdsBelow_imm _ _ _
  refine rtCall1_wp hrun hrt hnrt hids
    (evalRtArgs_cons harrEv (evalRtArgs_cons hidxEv
      (evalRtArgs_cons hvEv (evalRtArgs_cons (evalRtArg_imm64 ρ 0) (evalRtArgs_nil ρ)))))
    (hΓ.rt hsig (rtR2Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR2Env_lcnf_array_set hspec)))
    (fun _ _ _ _ hf => False.elim hf) ?_
  intro ret m' ⟨σ', hinv', hm'', hK⟩ r ek ρ' nr hnr hek hr hagr hrEv
  have hrEv' : LArg.eval ρ' i64 r = some ret := by simpa [BitVec.setWidth_eq] using hrEv
  exact hk r ek ρ' nr ret σ' m' hnr hek hr hagr hrEv' hinv' hm'' hK

theorem arrayPrim_sound {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg : LArg} {op : String} {args : List LArg}
    {retTy : LcTy} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {ws : List Word} {K : HPost} {X : HXPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hprim : isPhase1ArrayPrim op args.length retTy = true)
    (hrun : (arrayPrim rtArg op args k).run n = .ok (e, n'))
    (_hkMono : ∀ r, LMMono (k r))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (hargsIds : ∀ a ∈ args, argIdsBelow a n) (hargsEv : EvalWordArgs ρ args ws)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem) (hX : HXPostRel rt R X XT)
    (hwp : HArrayPrimWp op ws K X σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk rw : Nat)
        (vr : BitVec rw) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits rw) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits rw, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  rcases isPhase1ArrayPrim_mem hprim with
    ⟨rfl, har⟩ | ⟨rfl, har⟩ | ⟨rfl, har⟩ | ⟨rfl, har⟩ | ⟨rfl, har⟩ | ⟨rfl, har⟩ |
    ⟨rfl, har⟩ | ⟨rfl, har⟩ | ⟨rfl, har⟩ | ⟨rfl, har⟩ | ⟨rfl, har⟩
  · -- "empty"
    rcases args with _ | ⟨a0, _ | _⟩ <;> simp at har
    rcases ws with _ | ⟨w0, _ | _⟩
    · simp [EvalWordArgs] at hargsEv
    · simp only [HArrayPrimWp] at hwp
      unfold arrayPrim at hrun
      refine arrayMkEmpty_rtCall1_wp hΓ hrun hrt hnrt (argIdsBelow_imm i64 1#64 n)
        (evalRtArg_imm64 ρ 1) hinv hm hX ?_ fun r ek ρ' nr res σ' m' hnr hek hr hagr hrEv
        hinv' hm' hK =>
        hk r ek ρ' J nr n' 64 res σ' m' hnr hek hr hagr (JEnvAgreeBelow.refl n J) hrEv
          hinv' hm' hK
      have hc0 : (if (1#64 &&& 1#64) ≠ 0#64 then (1#64 >>> 1).toNat else 0) = 0 := by decide
      have hle : 0 ≤ arrMaxCap := by decide
      simpa [hc0, hle] using hwp
    · simp [EvalWordArgs] at hargsEv
  · -- "size"
    rcases args with _ | ⟨a0, _ | ⟨arrArg, _ | _⟩⟩ <;> simp at har
    rcases ws with _ | ⟨w0, _ | ⟨wa, _ | _⟩⟩
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · have haId := hargsIds arrArg (List.mem_cons_of_mem _ List.mem_cons_self)
      have haW := hargsEv.2 (arrArg, wa) (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [HArrayPrimWp] at hwp
      cases hwa : wa.toBV64? with
      | none => simp [hwa] at hwp
      | some arr =>
        simp only [hwa] at hwp
        rcases hwp with ⟨arrObj, hmArr, haArr, hcArr, hK⟩
        obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hmArr
        obtain ⟨_, hmObj⟩ := hmem_focus_obj hidx hm
        have hload : loadVal mem i64 (arr + BitVec.ofNat 64 8) =
            some (BitVec.ofNat 64 σ.objs[idx].fields.length) := by
          rw [← haArr]; exact lcnfObjMem_load_fieldsLen_array hcArr hmObj
        unfold arrayPrim at hrun
        refine lm_loadAt_wp hrun (haW.toBV64? hwa) haId hload ?_
        intro szArg ek1 ρ1 n1 hn1 hek1 _ hagr1 hszEv
        refine boxSmall_wp hek1 hszEv ?_
        intro rArg ek2 ρ2 hek2 hrId hagr2 hrEv
        exact hk rArg ek2 ρ2 J (n1 + 2) n' 64 _ σ mem (by omega) hek2 hrId
          ((hagr2.mono (by omega : n ≤ n1)).trans hagr1) (JEnvAgreeBelow.refl n J) hrEv hinv hm hK
    · simp [EvalWordArgs] at hargsEv
  · -- "usize"
    rcases args with _ | ⟨a0, _ | ⟨arrArg, _ | _⟩⟩ <;> simp at har
    rcases ws with _ | ⟨w0, _ | ⟨wa, _ | _⟩⟩
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · have haId := hargsIds arrArg (List.mem_cons_of_mem _ List.mem_cons_self)
      have haW := hargsEv.2 (arrArg, wa) (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [HArrayPrimWp] at hwp
      cases hwa : wa.toBV64? with
      | none => simp [hwa] at hwp
      | some arr =>
        simp only [hwa] at hwp
        rcases hwp with ⟨arrObj, hmArr, haArr, hcArr, hK⟩
        obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hmArr
        obtain ⟨_, hmObj⟩ := hmem_focus_obj hidx hm
        have hload : loadVal mem i64 (arr + BitVec.ofNat 64 8) =
            some (BitVec.ofNat 64 σ.objs[idx].fields.length) := by
          rw [← haArr]; exact lcnfObjMem_load_fieldsLen_array hcArr hmObj
        unfold arrayPrim at hrun
        refine lm_loadAt_wp hrun (haW.toBV64? hwa) haId hload ?_
        intro szArg ek1 ρ1 n1 hn1 hek1 hszId hagr1 hszEv
        exact hk szArg ek1 ρ1 J n1 n' 64 _ σ mem (by omega) hek1 hszId hagr1
          (JEnvAgreeBelow.refl n J) hszEv hinv hm hK
    · simp [EvalWordArgs] at hargsEv
  · -- "mkEmpty"
    rcases args with _ | ⟨a0, _ | ⟨capArg, _ | _⟩⟩ <;> simp at har
    rcases ws with _ | ⟨w0, _ | ⟨wc, _ | _⟩⟩
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · have hcId := hargsIds capArg (List.mem_cons_of_mem _ List.mem_cons_self)
      have hcW := hargsEv.2 (capArg, wc) (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [HArrayPrimWp] at hwp
      cases hwc : wc.toBV64? with
      | none => simp [hwc] at hwp
      | some cap =>
        simp only [hwc] at hwp
        unfold arrayPrim at hrun
        exact arrayMkEmpty_rtCall1_wp hΓ hrun hrt hnrt hcId (hcW.toRtArgBV64 hwc)
          hinv hm hX hwp fun r ek ρ' nr res σ' m' hnr hek hr hagr hrEv hinv' hm' hK =>
          hk r ek ρ' J nr n' 64 res σ' m' hnr hek hr hagr (JEnvAgreeBelow.refl n J) hrEv
            hinv' hm' hK
    · simp [EvalWordArgs] at hargsEv
  · -- "emptyWithCapacity"
    rcases args with _ | ⟨a0, _ | ⟨capArg, _ | _⟩⟩ <;> simp at har
    rcases ws with _ | ⟨w0, _ | ⟨wc, _ | _⟩⟩
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · have hcId := hargsIds capArg (List.mem_cons_of_mem _ List.mem_cons_self)
      have hcW := hargsEv.2 (capArg, wc) (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [HArrayPrimWp] at hwp
      cases hwc : wc.toBV64? with
      | none => simp [hwc] at hwp
      | some cap =>
        simp only [hwc] at hwp
        unfold arrayPrim at hrun
        exact arrayMkEmpty_rtCall1_wp hΓ hrun hrt hnrt hcId (hcW.toRtArgBV64 hwc)
          hinv hm hX hwp fun r ek ρ' nr res σ' m' hnr hek hr hagr hrEv hinv' hm' hK =>
          hk r ek ρ' J nr n' 64 res σ' m' hnr hek hr hagr (JEnvAgreeBelow.refl n J) hrEv
            hinv' hm' hK
    · simp [EvalWordArgs] at hargsEv
  · -- "push"
    rcases args with _ | ⟨a0, _ | ⟨arrArg, _ | ⟨vArg, _ | _⟩⟩⟩ <;> simp at har
    rcases ws with _ | ⟨w0, _ | ⟨wa, _ | ⟨wv, _ | _⟩⟩⟩
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · have haId := hargsIds arrArg (List.mem_cons_of_mem _ List.mem_cons_self)
      have hvId := hargsIds vArg
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have haW := hargsEv.2 (arrArg, wa) (List.mem_cons_of_mem _ List.mem_cons_self)
      have hvW := hargsEv.2 (vArg, wv)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      simp only [HArrayPrimWp] at hwp
      cases hwa : wa.toBV64? with
      | none => simp [hwa] at hwp
      | some arr => cases hwv : wv.toBV64? with
        | none => simp [hwa, hwv] at hwp
        | some v =>
          simp only [hwa, hwv] at hwp
          unfold arrayPrim at hrun
          exact arrayPush_rtCall1_wp hΓ hrun hrt hnrt haId (haW.toRtArgBV64 hwa)
            hvId (hvW.toRtArgBV64 hwv) hinv hm hX hwp fun r ek ρ' nr res σ' m' hnr hek hr
            hagr hrEv hinv' hm' hK =>
            hk r ek ρ' J nr n' 64 res σ' m' hnr hek hr hagr (JEnvAgreeBelow.refl n J) hrEv
              hinv' hm' hK
    · simp [EvalWordArgs] at hargsEv
  · -- "get!Internal"
    rcases args with _ | ⟨a0, _ | ⟨dvArg, _ | ⟨arrArg, _ | ⟨idxArg, _ | _⟩⟩⟩⟩ <;> simp at har
    rcases ws with _ | ⟨w0, _ | ⟨wdv, _ | ⟨wa, _ | ⟨wi, _ | _⟩⟩⟩⟩
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · have hdvId := hargsIds dvArg (List.mem_cons_of_mem _ List.mem_cons_self)
      have haId := hargsIds arrArg
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have hiId := hargsIds idxArg (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      have hdvW := hargsEv.2 (dvArg, wdv) (List.mem_cons_of_mem _ List.mem_cons_self)
      have haW := hargsEv.2 (arrArg, wa)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have hiW := hargsEv.2 (idxArg, wi) (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      simp only [HArrayPrimWp] at hwp
      cases hwdv : wdv.toBV64? with
      | none => simp [hwdv] at hwp
      | some dv => cases hwa : wa.toBV64? with
        | none => simp [hwdv, hwa] at hwp
        | some arr => cases hwi : wi.toBV64? with
          | none => simp [hwdv, hwa, hwi] at hwp
          | some idx =>
            simp only [hwdv, hwa, hwi] at hwp
            rcases hwp with ⟨arrObj, hmArr, haArr, hcArr, hwf, hrest⟩
            unfold arrayPrim at hrun
            exact arrayGet_rtCall1_wp hΓ (Or.inl rfl) hrun hrt hnrt hdvId
              (hdvW.toRtArgBV64 hwdv) haId (haW.toRtArgBV64 hwa) hiId (hiW.toRtArgBV64 hwi)
              hinv hm ⟨arrObj, hmArr, haArr, hcArr, hwf, ⟨fun _ => hrest, fun h => by cases h⟩⟩
              fun r ek ρ' nr res σ' m' hnr hek hr hagr hrEv hinv' hm' hK =>
              hk r ek ρ' J nr n' 64 res σ' m' hnr hek hr hagr (JEnvAgreeBelow.refl n J) hrEv
                hinv' hm' hK
    · simp [EvalWordArgs] at hargsEv
  · -- "get!InternalBorrowed"
    rcases args with _ | ⟨a0, _ | ⟨dvArg, _ | ⟨arrArg, _ | ⟨idxArg, _ | _⟩⟩⟩⟩ <;> simp at har
    rcases ws with _ | ⟨w0, _ | ⟨wdv, _ | ⟨wa, _ | ⟨wi, _ | _⟩⟩⟩⟩
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · have hdvId := hargsIds dvArg (List.mem_cons_of_mem _ List.mem_cons_self)
      have haId := hargsIds arrArg
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have hiId := hargsIds idxArg (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      have hdvW := hargsEv.2 (dvArg, wdv) (List.mem_cons_of_mem _ List.mem_cons_self)
      have haW := hargsEv.2 (arrArg, wa)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have hiW := hargsEv.2 (idxArg, wi) (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      simp only [HArrayPrimWp] at hwp
      cases hwdv : wdv.toBV64? with
      | none => simp [hwdv] at hwp
      | some dv => cases hwa : wa.toBV64? with
        | none => simp [hwdv, hwa] at hwp
        | some arr => cases hwi : wi.toBV64? with
          | none => simp [hwdv, hwa, hwi] at hwp
          | some idx =>
            simp only [hwdv, hwa, hwi] at hwp
            rcases hwp with ⟨arrObj, hmArr, haArr, hcArr, hwf, hrest⟩
            unfold arrayPrim at hrun
            exact arrayGet_rtCall1_wp hΓ (Or.inr rfl) hrun hrt hnrt hdvId
              (hdvW.toRtArgBV64 hwdv) haId (haW.toRtArgBV64 hwa) hiId (hiW.toRtArgBV64 hwi)
              hinv hm ⟨arrObj, hmArr, haArr, hcArr, hwf, ⟨(fun h => by cases h), fun _ => hrest⟩⟩
              fun r ek ρ' nr res σ' m' hnr hek hr hagr hrEv hinv' hm' hK =>
              hk r ek ρ' J nr n' 64 res σ' m' hnr hek hr hagr (JEnvAgreeBelow.refl n J) hrEv
                hinv' hm' hK
    · simp [EvalWordArgs] at hargsEv
  · -- "propagateMark"
    rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨ysArg, _ | _⟩⟩⟩⟩ <;> simp at har
    rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨wys, _ | _⟩⟩⟩⟩
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · have hysId := hargsIds ysArg (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      have hysW := hargsEv.2 (ysArg, wys) (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      rcases hysW with ⟨bw, bv, _, rfl, hysEv⟩
      simp only [HArrayPrimWp] at hwp
      unfold arrayPrim at hrun
      exact hk ysArg e ρ J n n' bw bv σ mem (Nat.le_refl n) hrun hysId
        (VEnvAgreeBelow.refl n ρ) (JEnvAgreeBelow.refl n J) hysEv hinv hm hwp.2
    · simp [EvalWordArgs] at hargsEv
  · -- "set!"
    rcases args with _ | ⟨a0, _ | ⟨arrArg, _ | ⟨idxArg, _ | ⟨vArg, _ | _⟩⟩⟩⟩ <;> simp at har
    rcases ws with _ | ⟨w0, _ | ⟨wa, _ | ⟨wi, _ | ⟨wv, _ | _⟩⟩⟩⟩
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · have haId := hargsIds arrArg (List.mem_cons_of_mem _ List.mem_cons_self)
      have hiId := hargsIds idxArg
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have hvId := hargsIds vArg (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      have haW := hargsEv.2 (arrArg, wa) (List.mem_cons_of_mem _ List.mem_cons_self)
      have hiW := hargsEv.2 (idxArg, wi)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have hvW := hargsEv.2 (vArg, wv) (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      simp only [HArrayPrimWp] at hwp
      cases hwa : wa.toBV64? with
      | none => simp [hwa] at hwp
      | some arr => cases hwi : wi.toBV64? with
        | none => simp [hwa, hwi] at hwp
        | some idx => cases hwv : wv.toBV64? with
          | none => simp [hwa, hwi, hwv] at hwp
          | some v =>
            simp only [hwa, hwi, hwv] at hwp
            unfold arrayPrim at hrun
            exact arraySet_rtCall1_wp hΓ hrun hrt hnrt haId (haW.toRtArgBV64 hwa)
              hiId (hiW.toRtArgBV64 hwi) hvId (hvW.toRtArgBV64 hwv) hinv hm hwp fun r ek ρ'
              nr res σ' m' hnr hek hr hagr hrEv hinv' hm' hK =>
              hk r ek ρ' J nr n' 64 res σ' m' hnr hek hr hagr (JEnvAgreeBelow.refl n J) hrEv
                hinv' hm' hK
    · simp [EvalWordArgs] at hargsEv
  · -- "set"
    rcases args with _ | ⟨a0, _ | ⟨arrArg, _ | ⟨idxArg, _ | ⟨vArg, _ | ⟨a4, _ | _⟩⟩⟩⟩⟩ <;>
      simp at har
    rcases ws with _ | ⟨w0, _ | ⟨wa, _ | ⟨wi, _ | ⟨wv, _ | ⟨w4, _ | _⟩⟩⟩⟩⟩
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · have haId := hargsIds arrArg (List.mem_cons_of_mem _ List.mem_cons_self)
      have hiId := hargsIds idxArg
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have hvId := hargsIds vArg (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      have haW := hargsEv.2 (arrArg, wa) (List.mem_cons_of_mem _ List.mem_cons_self)
      have hiW := hargsEv.2 (idxArg, wi)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have hvW := hargsEv.2 (vArg, wv) (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      simp only [HArrayPrimWp] at hwp
      cases hwa : wa.toBV64? with
      | none => simp [hwa] at hwp
      | some arr => cases hwi : wi.toBV64? with
        | none => simp [hwa, hwi] at hwp
        | some idx => cases hwv : wv.toBV64? with
          | none => simp [hwa, hwi, hwv] at hwp
          | some v =>
            simp only [hwa, hwi, hwv] at hwp
            unfold arrayPrim at hrun
            exact arraySet_rtCall1_wp hΓ hrun hrt hnrt haId (haW.toRtArgBV64 hwa)
              hiId (hiW.toRtArgBV64 hwi) hvId (hvW.toRtArgBV64 hwv) hinv hm hwp fun r ek ρ'
              nr res σ' m' hnr hek hr hagr hrEv hinv' hm' hK =>
              hk r ek ρ' J nr n' 64 res σ' m' hnr hek hr hagr (JEnvAgreeBelow.refl n J) hrEv
                hinv' hm' hK
    · simp [EvalWordArgs] at hargsEv

/-! ## 2. Miscellaneous `LMMono` Lemmas -/

theorem floatPrim_mono {rt : LArg} {op : String} {args : List LArg} {k : LArg → LM LExpr}
    (hk : ∀ r, LMMono (k r)) : LMMono (floatPrim rt op args k) := by
  unfold floatPrim
  split
  all_goals first
    | exact hk _
    | exact rtCall1_mono hk
    | exact lfail_mono
    | (split <;> first | exact rtCall1_mono hk | exact lfail_mono)

theorem charPrim_mono {rt : LArg} {op : String} {args : List LArg} {k : LArg → LM LExpr}
    (hk : ∀ r, LMMono (k r)) : LMMono (charPrim rt op args k) := by
  unfold charPrim
  split
  · exact rtCall1_mono hk
  · exact uintPrim_mono fun _ => convW_mono hk
  · exact rtCall1_mono hk
  · exact lfail_mono

theorem intPrim_mono {rt : LArg} {op : String} {args : List LArg} {k : LArg → LM LExpr}
    (hk : ∀ r, LMMono (k r)) : LMMono (intPrim rt op args k) := by
  unfold intPrim
  simp only [intCall]
  split
  all_goals first
    | with_reducible exact lfail_mono
    | with_reducible exact rtCall1_mono hk
    | (with_reducible refine tagBin_mono (fun _ _ hslow => ?_) hk
       first
       | with_reducible exact cmpOp_mono fun _ => boolToU8_mono fun _ => pure_mono _
       | exact op1_mono fun _ => op1_mono fun _ => op1_mono fun _ =>
           add64_mono fun _ => cmpOp_mono fun _ =>
             bind_mono (boxSmall_mono fun _ => pure_mono _) fun _ =>
               bind_mono hslow fun _ => pure_mono _)
    | (with_reducible refine isScalarObj_mono fun _ => withJoin1_mono hk fun _ => ?_
       exact bind_mono (lshr64_mono fun _ => cmpOp_mono fun _ =>
         bind_mono (rtCall1_mono fun _ => pure_mono _) fun _ => pure_mono _) fun _ =>
         bind_mono (rtCall1_mono fun _ => pure_mono _) fun _ => pure_mono _)

theorem int64Prim_mono {rt : LArg} {op : String} {args : List LArg} {k : LArg → LM LExpr}
    (hk : ∀ r, LMMono (k r)) : LMMono (int64Prim rt op args k) := by
  unfold int64Prim
  split
  all_goals first
    | exact uintOfNat_mono hk
    | exact uintPrim_mono hk
    | exact cmpOp_mono fun _ => boolToU8_mono hk
    | exact lfail_mono
    | (refine convW_mono fun _ => withJoin1_mono hk fun _ => ?_
       unfold intCall intFitsSmall
       refine bind_mono (rtCall1_mono fun _ => pure_mono _) fun _ =>
         bind_mono (boxSmall_mono fun _ => pure_mono _) fun _ =>
           add64_mono fun _ => cmpOp_mono fun _ => pure_mono _)

theorem objTagNat_mono {x : LArg} {k : LArg → LM LExpr} (hk : ∀ r, LMMono (k r)) :
    LMMono (objTagNat x k) := by
  unfold objTagNat
  refine isScalarObj_mono fun _ => withJoin1_mono hk fun _ => ?_
  exact bind_mono (loadAt_mono fun _ => convW_mono fun _ => boxSmall_mono fun _ => pure_mono _)
    fun _ => pure_mono _

theorem externPrim_mono {rt : LArg} {name : String} {args : List LArg} {k : LArg → LM LExpr}
    (hk : ∀ r, LMMono (k r)) : LMMono (externPrim rt name args k) := by
  unfold externPrim
  split
  · exact natPrim_mono hk
  · exact arrayPrim_mono hk
  · exact stringPrim_mono hk
  · exact byteArrayPrim_mono hk
  · exact floatPrim_mono hk
  · exact charPrim_mono hk
  · exact intPrim_mono hk
  · exact int64Prim_mono hk
  · split <;> first | exact objTagNat_mono hk | exact lfail_mono
  · exact hk _
  · split <;> first | exact rtCall1_mono hk | exact lfail_mono
  · split <;> first | exact uintPrim_mono hk | exact lfail_mono
  · exact lfail_mono

/-! ## 3. `objTagNat_wp` and Top-Level `externPrim_sound` -/

theorem objTagNat_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {xArg : LArg} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt vx : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost}
    (hrun : (objTagNat xArg k).run n = .ok (e, n'))
    (hkMono : ∀ r, LMMono (k r))
    (hxId : argIdsBelow xArg n) (hxEv : LArg.eval ρ i64 xArg = some vx)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hwp : if (vx &&& 1#64) ≠ 0#64 then K (Word.i64 vx) σ
      else ∃ o ∈ σ.objs, o.addr = vx ∧ o.Wf ∧
        K (Word.i64 ((BitVec.ofNat 64 o.tag <<< 1) ||| 1#64)) σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk rw : Nat)
        (vr : BitVec rw) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits rw) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits rw, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold objTagNat at hrun
  refine isScalarObj_wp hrun hxEv ?_
  intro sArg ek1 ρ1 hek1 _ hagr1 hsEv
  let Inv : Val i64 → Mem 64 → Prop := fun v m1 =>
    ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m1 ∧ K (Word.i64 v) σ'
  refine withJoin1_wp (Inv := Inv) hek1 (hkMono _) ?_ ?_
  · intro r blk n2 J' hblk hr hJagr v m1 ⟨σ', hinv', hm', hK⟩ hagr rEv
    exact hk r blk _ J' (n + 4) n2 64 v σ' m1 (by omega) hblk hr
      ((hagr.mono (by omega : n ≤ n + 2)).trans hagr1)
      (hJagr.mono (by omega : n ≤ n + 2)) rEv hinv' hm' hK
  · intro j body n2 J' hn2 hbody _ hjok
    rw [lm_bind_run] at hbody
    rcases hbody with ⟨ePtr, _, hePtr, hpure⟩
    rw [lm_pure_run] at hpure
    injection hpure with hpr
    have hbod : LExpr.jnz sArg (j xArg) ePtr = body := congrArg Prod.fst hpr
    subst hbod
    refine wp_jnz hsEv ?_ ?_
    · intro htrue
      have hsc : (vx &&& 1#64) ≠ 0#64 := of_decide_eq_true htrue
      rw [ite_eq_left hsc] at hwp
      exact hjok J' xArg ρ1 mem vx (JEnvAgreeBelow.refl _ J')
        ((hagr1.eval hxId).trans hxEv) ⟨σ, hinv, hm, hwp⟩
    · intro hfalse
      have hsc : ¬ ((vx &&& 1#64) ≠ 0#64) := of_decide_eq_false hfalse
      rw [ite_eq_right hsc] at hwp
      rcases hwp with ⟨o, hmO, haO, hwf, hK⟩
      obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hmO
      obtain ⟨_, hmObj⟩ := hmem_focus_obj hidx hm
      have hload : loadVal mem i8 (vx + 7#64) = some (BitVec.ofNat 8 σ.objs[idx].tag) := by
        rw [← haO]; exact lcnfObjMem_load_i8_tag hwf hmObj
      have hx1 : LArg.eval ρ1 i64 xArg = some vx := (hagr1.eval hxId).trans hxEv
      refine lm_loadAt_wp hePtr hx1 (argIdsBelow_mono (by omega) hxId) hload ?_
      intro t8Arg ek2 ρ2 n3 hn3 hek2 ht8Id hagr2 ht8Ev
      refine convW_wp hek2 ht8Ev ht8Id ?_
      intro t64Arg ek3 ρ3 n4 hn4 hek3 ht64Id hagr3 ht64Ev
      have htagLt : σ.objs[idx].tag < 256 := hwf.2.2.2.2.2.1
      have hw8Eq : (BitVec.ofNat 8 σ.objs[idx].tag).setWidth 64 =
          BitVec.ofNat 64 σ.objs[idx].tag := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : σ.objs[idx].tag < 2 ^ 8),
          Nat.mod_eq_of_lt (by omega : σ.objs[idx].tag < 2 ^ 64)]
      rw [hw8Eq] at ht64Ev
      refine boxSmall_wp hek3 ht64Ev ?_
      intro rArg ek4 ρ4 hek4 _ _ hrEv
      rw [lm_pure_run] at hek4
      injection hek4 with hp4
      have he4 : j rArg = ek4 := congrArg Prod.fst hp4
      subst he4
      exact hjok J' rArg ρ4 mem _ (JEnvAgreeBelow.refl _ J') hrEv ⟨σ, hinv, hm, hK⟩

private theorem externPrim_uint_reduce {rtArg : LArg} {name p0 p1 : String}
    {args : List LArg} {retTy : LcTy} {k : LArg → LM LExpr} {w : Nat}
    {rt : BitVec 64} {ws : List Word} {K : HPost} {X : HXPost} {σ : HState}
    (hsp : splitDot name = [p0, p1]) (hu : uintWidth? p0 = some w) :
    isPhase1Prim name args.length retTy = isPhase1UintPrim w p1 args.length retTy ∧
    externPrim rtArg name args k = uintPrim rtArg w p1 args k ∧
    HPrim.wp rt name ws K X σ = HUintPrimWp rt w p1 ws K σ := by
  unfold uintWidth? at hu
  unfold isPhase1Prim externPrim HPrim.wp
  rw [hsp]
  split at hu <;> cases hu <;> simp [uintWidth?]

private theorem isPhase1Prim_split2_none {name p0 p1 : String} {arity : Nat} {retTy : LcTy}
    (hsp : splitDot name = [p0, p1])
    (hstr : p0 ≠ "String") (hnat : p0 ≠ "Nat") (harr : p0 ≠ "Array") (hba : p0 ≠ "ByteArray")
    (hu : uintWidth? p0 = none) (h : isPhase1Prim name arity retTy = true) : False := by
  unfold isPhase1Prim at h
  rw [hsp] at h
  clear hsp
  split at h
  all_goals first
    | cases h
    | (rename_i heq; cases heq <;> first
        | exact hnat rfl
        | exact harr rfl
        | exact hstr rfl
        | exact hba rfl
        | (rw [hu] at h; cases h))

private theorem isPhase1Prim_split3_absurd {name p0 p1 p2 : String} {arity : Nat} {retTy : LcTy}
    (hsp : splitDot name = [p0, p1, p2]) (hstr : p0 ≠ "String")
    (hsys : ¬ (p0 = "System" ∧ p1 = "Platform" ∧ p2 = "getNumBits"))
    (h : isPhase1Prim name arity retTy = true) : False := by
  unfold isPhase1Prim at h
  rw [hsp] at h
  clear hsp
  split at h
  all_goals first
    | cases h
    | (rename_i heq; cases heq <;> first
        | exact hstr rfl
        | exact hsys ⟨rfl, rfl, rfl⟩)

private theorem isPhase1Prim_split4_absurd {name p0 p1 p2 p3 : String} {rest : List String}
    {arity : Nat} {retTy : LcTy} (hsp : splitDot name = p0 :: p1 :: p2 :: p3 :: rest)
    (hstr : p0 ≠ "String") (h : isPhase1Prim name arity retTy = true) : False := by
  unfold isPhase1Prim at h
  rw [hsp] at h
  clear hsp
  split at h
  all_goals first
    | cases h
    | (rename_i heq; cases heq <;> exact hstr rfl)

theorem externPrim_sound {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg : LArg} {name : String} {args : List LArg}
    {retTy : LcTy} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {ws : List Word} {K : HPost} {X : HXPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hprim : isPhase1Prim name args.length retTy = true)
    (hrun : (externPrim rtArg name args k).run n = .ok (e, n'))
    (hkMono : ∀ r, LMMono (k r))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (hargsIds : ∀ a ∈ args, argIdsBelow a n) (hargsEv : EvalWordArgs ρ args ws)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem) (hX : HXPostRel rt R X XT)
    (hwp : HPrim.wp rt name ws K X σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk rw : Nat)
        (vr : BitVec rw) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits rw) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits rw, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  by_cases hsplit : ∃ rest, splitDot name = "String" :: rest
  · rcases hsplit with ⟨rest, hsp⟩
    unfold isPhase1Prim at hprim
    unfold externPrim at hrun
    unfold HPrim.wp at hwp
    rw [hsp] at hprim hrun hwp
    dsimp only at hprim hrun hwp
    exact stringPrim_sound hΓ hprim hrun hkMono hrt hnrt hargsIds hargsEv hinv hm hX hwp hk
  · have hnoStr : ∀ rest, splitDot name ≠ "String" :: rest := fun rest h => hsplit ⟨rest, h⟩
    cases hsp : splitDot name with
    | nil =>
      unfold isPhase1Prim at hprim
      rw [hsp] at hprim
      cases hprim
    | cons p0 rest =>
      have hstr : p0 ≠ "String" := fun he => hnoStr rest (by rw [hsp, he])
      rcases rest with _ | ⟨p1, rest2⟩
      · unfold isPhase1Prim at hprim
        unfold externPrim at hrun
        unfold HPrim.wp at hwp
        rw [hsp] at hprim hrun hwp
        by_cases hg : p0 = "getObjTagNat"
        · subst hg; dsimp only at hprim hrun hwp
          rcases args with _ | ⟨x0, _ | ⟨x1, _ | _⟩⟩ <;> simp at hprim
          · rcases ws with _ | ⟨wx, _ | _⟩
            · simp [EvalWordArgs] at hargsEv
            · have hxId := hargsIds x0 List.mem_cons_self
              have hxW := hargsEv.2 (x0, wx) List.mem_cons_self
              simp only [Option.bind_some] at hwp
              cases hwx : wx.toBV64? with
              | none => simp [hwx] at hwp
              | some vx =>
                simp only [hwx] at hwp
                exact objTagNat_wp hrun hkMono hxId (hxW.toBV64? hwx) hinv hm hwp hk
            · simp [EvalWordArgs] at hargsEv
          · rcases ws with _ | ⟨w0, _ | ⟨wx, _ | _⟩⟩
            · simp [EvalWordArgs] at hargsEv
            · simp [EvalWordArgs] at hargsEv
            · have hxId := hargsIds x1 (List.mem_cons_of_mem _ List.mem_cons_self)
              have hxW := hargsEv.2 (x1, wx) (List.mem_cons_of_mem _ List.mem_cons_self)
              simp only [Option.bind_some] at hwp
              cases hwx : wx.toBV64? with
              | none => simp [hwx] at hwp
              | some vx =>
                simp only [hwx] at hwp
                exact objTagNat_wp hrun hkMono hxId (hxW.toBV64? hwx) hinv hm hwp hk
            · simp [EvalWordArgs] at hargsEv
        · simp [hstr, hg] at hprim
      · rcases rest2 with _ | ⟨p2, rest3⟩
        · by_cases hnat : p0 = "Nat"
          · subst hnat
            unfold isPhase1Prim at hprim
            unfold externPrim at hrun
            unfold HPrim.wp at hwp
            rw [hsp] at hprim hrun hwp
            dsimp only at hprim hrun hwp
            exact natPrim_sound hΓ hprim hrun hkMono hrt hnrt hargsIds hargsEv hinv hm hX hwp hk
          · by_cases harr : p0 = "Array"
            · subst harr
              unfold isPhase1Prim at hprim
              unfold externPrim at hrun
              unfold HPrim.wp at hwp
              rw [hsp] at hprim hrun hwp
              dsimp only at hprim hrun hwp
              exact arrayPrim_sound hΓ hprim hrun hkMono hrt hnrt hargsIds hargsEv hinv hm hX
                hwp hk
            · by_cases hba : p0 = "ByteArray"
              · subst hba
                unfold isPhase1Prim at hprim
                unfold externPrim at hrun
                unfold HPrim.wp at hwp
                rw [hsp] at hprim hrun hwp
                dsimp only at hprim hrun hwp
                exact byteArrayPrim_sound hΓ hprim hrun hkMono hrt hnrt hargsIds hargsEv hinv hm
                  hX hwp hk
              · cases hu : uintWidth? p0 with
                | none =>
                  exact False.elim (isPhase1Prim_split2_none hsp hstr hnat harr hba hu hprim)
                | some w =>
                  have ⟨hp', hr', hw'⟩ := externPrim_uint_reduce
                    (rtArg := rtArg) (args := args) (retTy := retTy) (k := k)
                    (rt := rt) (ws := ws) (K := K) (X := X) (σ := σ) hsp hu
                  rw [hp'] at hprim
                  rw [hr'] at hrun
                  rw [hw'] at hwp
                  exact uintPrim_sound hΓ (uintWidth?_cases hu) hprim hrun hkMono hrt hnrt
                    hargsIds hargsEv hinv hm hwp hk
        · rcases rest3 with _ | ⟨p3, rest4⟩
          · by_cases hsys : p0 = "System" ∧ p1 = "Platform" ∧ p2 = "getNumBits"
            · rcases hsys with ⟨rfl, rfl, rfl⟩
              unfold externPrim at hrun
              unfold HPrim.wp at hwp
              rw [hsp] at hrun hwp
              dsimp only at hrun hwp
              exact hk (imm64 (2 * 64 + 1)) e ρ J n n' 64 (BitVec.ofNat 64 (2 * 64 + 1)) σ mem
                (Nat.le_refl n) hrun (argIdsBelow_imm i64 _ n) (VEnvAgreeBelow.refl n ρ)
                (JEnvAgreeBelow.refl n J) (LArg.eval_imm_self ρ i64 _) hinv hm hwp
            · exact False.elim (isPhase1Prim_split3_absurd hsp hstr hsys hprim)
          · exact False.elim (isPhase1Prim_split4_absurd hsp hstr hprim)

end LeanQbe.T.LeanLCNF.Sem
