module

public import LeanQbe.T.LeanLCNF.Sem.LowerSound3a

/-!
# Call and Value Lowering Simulation (`LowerSound3`)

Stage 2 simulation theorems for calls (`lowerFap_sound`) and all Phase-1 `LcVal` expressions
(`lowerVal_sound`) on top of `LowerSound3a`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Frontend.C0
open Std.ExtHashMap

/-! ## 1. User & Primitive Call Simulation (`lowerFap_sound`) -/

private theorem mapM_length_ok {α β : Type} :
    ∀ {f : α → LM β} {xs : List α} {ys : List β} {n n' : Nat},
      (xs.mapM f).run n = .ok (ys, n') → ys.length = xs.length
  | _, [], ys, _, _, h => by
    simp only [List.mapM_nil, lm_pure_run, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; rfl
  | f, x :: xs, ys, n, n', h => by
    simp only [List.mapM_cons, lm_bind_run] at h
    rcases h with ⟨y, n1, _, ys', n2, htl, hp⟩
    rw [lm_pure_run] at hp
    injection hp with hpe
    have hys : y :: ys' = ys := congrArg Prod.fst hpe
    subst hys
    exact congrArg Nat.succ (mapM_length_ok htl)

private theorem m_decls_find?_of_mem {decls : List LcDecl}
    (hnd : symsNodup (decls.map (·.name)) = true) {d : LcDecl} (hm : d ∈ decls) :
    decls.find? (·.name == d.name) = some d := by
  induction decls with
  | nil => cases hm
  | cons d' ds ih =>
    simp only [List.map_cons, symsNodup, Bool.and_eq_true, Bool.not_eq_true'] at hnd
    rcases hnd with ⟨hnot, hnd'⟩
    rcases List.mem_cons.mp hm with rfl | hmem
    · simp [List.find?]
    · have hne : (d'.name == d.name) = false := by
        cases he : (d'.name == d.name) with
        | false => rfl
        | true =>
          have heq : d'.name = d.name := beq_iff_eq.mp he
          have hmemName : d'.name ∈ ds.map (·.name) :=
            List.mem_map.mpr ⟨d, hmem, heq.symm⟩
          have hc : (ds.map (·.name)).contains d'.name = true :=
            List.contains_iff_mem.mpr hmemName
          rw [hc] at hnot
          cases hnot
      simp only [List.find?, hne]
      exact ih hnd' hmem

private theorem env_cast_args {Γ : Env} {sym : Sym} {ts₁ ts₂ : List Ty} {ret : Ty}
    (h : ts₁ = ts₂) {xs : Tup Val ts₁} {rt : BitVec 64} {m : Mem 64} {P : Post [ret]} {X : XPost}
    (hcall : Γ sym (i64 :: ts₂) [ret] (rt, h ▸ xs) m P X) :
    Γ sym (i64 :: ts₁) [ret] (rt, xs) m P X := by
  cases h; exact hcall

private theorem evalArgs_cast_tys {ρ : Frontend.C0.VEnv} {t₁ t₂ : List Ty} (h : t₁ = t₂)
    {as : List LArg} {xs : Tup Val t₁} (hev : evalArgs ρ t₁ as = some xs) :
    evalArgs ρ t₂ as = some (h ▸ xs) := by
  cases h; exact hev

private theorem wordsOfTup_cast_tys {t₁ t₂ : List Ty} (h : t₁ = t₂) (xs : Tup Val t₁) :
    wordsOfTup (h ▸ xs) = wordsOfTup xs := by
  cases h; rfl

private theorem liftCall_of_HCallEnvOk {m : LcModule} {Δ : HEnv} {Γ : Env}
    {rt : BitVec 64} {R : Mem 64 → Prop} {σ : HState} {mem : Mem 64}
    {d : LcDecl} {ts : List Ty} {xs : Tup Val ts} {ws : List Word}
    {P : HPost} {E : HXPost}
    (hΓ : HCallEnvOk m Δ Γ) (hret : HEnv.RetTyped m Δ) (hd : d ∈ m.decls)
    (hlen : d.params.length ≤ regArgs) (htys : ts = d.params.map (·.ty.toTTy))
    (hws : wordsOfTup (htys ▸ xs) = ws)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem) (hcall : Δ d.name ws σ P E) :
    let PT : Post [d.retTy.toTTy] := fun (rv, ()) m' =>
      ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m' ∧ P ⟨d.retTy.toTTy, rv⟩ σ'
    let ET : XPost := fun g cs ys m' =>
      ∃ code σ', E code σ' ∧ g = "lcnf_panic" ∧ ∃ hcs : cs = [i64, i64],
        ys = hcs ▸ (rt, code, ()) ∧ (σ'.mem rt ⋆ R) m'
    Γ (mangleLc d.name) (i64 :: ts) [d.retTy.toTTy] (rt, xs) mem PT ET := by
  subst htys
  dsimp only at hws
  have htake : (d.params.map (·.ty.toTTy)).take regArgs = d.params.map (·.ty.toTTy) :=
    List.take_of_length_le (by simp [hlen])
  let PT : Post [d.retTy.toTTy] := fun (rv, ()) m' =>
    ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m' ∧ P ⟨d.retTy.toTTy, rv⟩ σ'
  let ET : XPost := fun g cs ys m' =>
    ∃ code σ', E code σ' ∧ g = "lcnf_panic" ∧ ∃ hcs : cs = [i64, i64],
      ys = hcs ▸ (rt, code, ()) ∧ (σ'.mem rt ⋆ R) m'
  have hspec_of : ∀ (ts' : List Ty) (heq : d.params.map (·.ty.toTTy) = ts'),
      liftSpec (Δ d.name) ts' d.retTy.toTTy (rt, heq ▸ xs) mem PT ET := by
    intro ts' heq
    cases heq
    refine ⟨σ, R, hinv, hm, ?_⟩
    rw [hws]
    refine hret d hd ws σ _ _ _ _ ?_ ?_ hcall
    · intro r σ' hty hrP
      rcases r with ⟨rt1, rv1⟩
      dsimp only at hty
      subst hty
      refine ⟨rfl, fun m' hinv' hm' => ⟨σ', hinv', hm', hrP⟩⟩
    · intro c σ' hEc m' hm'
      exact ⟨c, σ', hEc, rfl, rfl, rfl, hm'⟩
  have hdecl : liftDeclSpec (Δ d.name) d.params d.retTy
      (rt, htake.symm ▸ xs) mem PT ET :=
    (liftDeclSpec_iff_liftSpec_of_le (Δ d.name) d.params d.retTy hlen
      (rt, htake.symm ▸ xs) mem PT ET).mpr (hspec_of _ htake.symm)
  have hcall' := hΓ.1 (mangleLc d.name) (i64 :: (d.params.map (·.ty.toTTy)).take regArgs)
    [d.retTy.toTTy] (rt, htake.symm ▸ xs) mem PT ET (liftEnv_of_mem hd hdecl)
  exact env_cast_args htake.symm hcall'

theorem lowerFap_sound {m : LcModule} {env : LEnv} {Δ : HEnv} {Γ : Env}
    {rt : BitVec 64} {R : Mem 64 → Prop}
    {c : LCtx} {f : String} {as : List LcArg} {ty : LcTy}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {QH : HPost} {XH : HXPost} {QT : Post [c.retTy.toTTy]} {XT : XPost}
    {JH : HJEnv} {ρH : HValEnv} {ρL : Frontend.C0.VEnv} {JL : JEnv}
    {σ : HState} {mem : Mem 64} {K : HPost} {X : HXPost}
    (hfrag : m.inFirstOrderFragment = true)
    (henv : LEnvOk m env)
    (hΓ : HCallEnvOk m Δ Γ) (hret : HEnv.RetTyped m Δ)
    (hval : LcVal.inFirstOrder m.decls ty (.fap f as) = true)
    (hrun : (lowerFap env c f as ty k).run n = .ok (e, n'))
    (hkMono : ∀ r, LMMono (k r))
    (hsim : HSimInv Δ rt R c n QH XH QT XT JH ρH ρL JL)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hX : HXPostRel rt R X XT)
    (hwp : HVal.wp Δ rt ρH ty (.fap f as) K X σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv)
        (nr nk : Nat) (w : Word) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρL → JEnvAgreeBelow n J' JL →
      (hw : w.1 = ty.toTTy) → LArg.eval ρ' ty.toTTy r = some (hw ▸ w.2) →
      HInv rt σ' → (σ'.mem rt ⋆ R) m' → K w σ' →
      LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρL JL mem := by
  have hfrag' := hfrag
  simp only [LcModule.inFirstOrderFragment, Bool.and_eq_true, List.all_eq_true] at hfrag'
  rcases hfrag' with ⟨⟨hndNames, _⟩, hdeclsFo⟩
  dsimp only [HVal.wp] at hwp
  cases hown : ρH.evalArgsOwn as with
  | none => simp [hown] at hwp
  | some ws =>
    simp only [hown] at hwp
    unfold lowerFap at hrun
    cases hlu : env.decls.lookup f with
    | none =>
      have hfindNone : m.decls.find? (·.name == f) = none := by
        cases hf : m.decls.find? (·.name == f) with
        | none => rfl
        | some d =>
          have hmem : d ∈ m.decls := List.mem_of_find?_eq_some hf
          have hnm : d.name = f :=
            beq_iff_eq.mp (List.find?_some (p := fun (d : LcDecl) => d.name == f) hf)
          have hlu' := (henv f d).mpr ⟨hmem, hnm⟩
          rw [hlu'] at hlu
          cases hlu
      simp only [LcVal.inFirstOrder, hfindNone] at hval
      have hprimName : isPrimName f = true := isPrimName_of_isPhase1Prim hval
      simp only [hprimName, ↓reduceIte] at hwp
      simp only [hlu, lm_bind_run] at hrun
      rcases hrun with ⟨args, n1, has, hrunExt⟩
      obtain ⟨hn1, hargIds, hwordArgs⟩ :=
        mapM_argOwn_spec hsim.idsOk hsim.varRel hown has
      subst n1
      have harLen : args.length = as.length := mapM_length_ok has
      have hvalArgs : isPhase1Prim f args.length ty = true := by rw [harLen]; exact hval
      have hvalWs : isPhase1Prim f ws.length ty = true := by rw [← hwordArgs.1]; exact hvalArgs
      have hwp' := hPrim_wp_retTy hvalWs hwp
      refine externPrim_sound hΓ hvalArgs hrunExt hkMono hsim.rtOk hsim.idsOk.1 hargIds
        hwordArgs hinv hm hX hwp' ?_
      intro r ek ρ' J' nr nk rw vr σ' m' hnr hek hrId hagr hJagr hrEv hinv' hm' ⟨hwty, hK⟩
      dsimp only at hwty
      have hw' : (⟨.bits rw, vr⟩ : Word).1 = ty.toTTy := hwty
      have hrEv' : LArg.eval ρ' ty.toTTy r = some (hw' ▸ vr) := by
        have : Ty.bits rw = ty.toTTy := hwty
        cases this
        exact hrEv
      exact hk r ek ρ' J' nr nk ⟨.bits rw, vr⟩ σ' m' hnr hek hrId hagr hJagr
        hw' hrEv' hinv' hm' hK
    | some d =>
      obtain ⟨hdMem, rfl⟩ := (henv f d).mp hlu
      have hfindSome := m_decls_find?_of_mem hndNames hdMem
      simp only [LcVal.inFirstOrder, hfindSome, Bool.and_eq_true] at hval
      rcases hval with ⟨⟨hnotPrim, hlenDec⟩, hargsOk⟩
      have hprimFalse : isPrimName d.name = false := by
        cases hp : isPrimName d.name <;> simp [hp] at hnotPrim ⊢
      have hlen : d.params.length ≤ regArgs := decide_eq_true_eq.mp hlenDec
      have hdeclFo := hdeclsFo d hdMem
      simp only [LcDecl.inFirstOrder, Bool.and_eq_true] at hdeclFo
      have hnotConst : (d.params.isEmpty && !d.retTy.isScalar) = false := by
        cases hc : (d.params.isEmpty && !d.retTy.isScalar) <;>
          simp [hc] at hdeclFo ⊢
      have harLen : as.length = d.params.length := by
        simpa [List.length_map] using argsOkForTys_length hargsOk
      have harNe : (as.length != d.params.length) = false := by simp [harLen]
      simp only [hlu, hnotConst, harNe, Bool.false_eq_true, ↓reduceIte,
        lm_bind_run] at hrun
      simp only [hprimFalse, Bool.false_eq_true, ↓reduceIte] at hwp
      rcases hwp with ⟨P, E, hcall, hP, hE⟩
      rcases hrun with ⟨args, n1, hmap, hrunCall⟩
      obtain ⟨hn1, htysZip, hmapTys⟩ := mapM_argAt_fap_run as d.params n n1 args hmap
      subst n1
      have htys : args.map Prod.snd = d.params.map (·.ty.toTTy) := by
        rw [htysZip]; exact map_snd_zip_map harLen
      obtain ⟨_, _, xsTys, hxsEv, hxsWs⟩ :=
        mapM_argAt_tys_spec hargsOk hown hsim.idsOk hsim.varRel hmapTys
      have hlenArgs : args.length ≤ regArgs := by
        have : args.length = d.params.length := by
          have := congrArg List.length htys; simpa using this
        omega
      have hxsMap : (d.params.map (·.ty)).map LcTy.toTTy = d.params.map (·.ty.toTTy) :=
        List.map_map
      have hcastEq : (d.params.map (·.ty)).map LcTy.toTTy = args.map Prod.snd :=
        hxsMap.trans htys.symm
      have hxsEv' := evalArgs_cast_tys hcastEq hxsEv
      have hlift := liftCall_of_HCallEnvOk hΓ hret hdMem hlen htys
        (by
          rw [wordsOfTup_cast_tys htys, wordsOfTup_cast_tys hcastEq]
          exact hxsWs)
        hinv hm hcall
      refine callFn_reg_wp hlenArgs hrunCall hsim.rtOk hxsEv' hlift ?_ ?_
      · intro g cs ys m' ⟨code, σ', hEc, hg, hcs, hys, hm'⟩
        cases hg
        cases hcs
        cases hys
        exact hX code σ' (hE code σ' hEc) m' hm'
      · intro r ek hek hrId rv m' ⟨σ', hinv', hm', hPrv⟩ hagr1 hrEv
        obtain ⟨r', hrw, hK⟩ := hP ⟨d.retTy.toTTy, rv⟩ σ' hPrv
        dsimp only [Word.toWidth, LcTy.toTTy] at hrw
        cases hrw
        refine convW_wp hek hrEv hrId ?_
        intro r2 ek2 ρ2 nr2 hnr2 hek2 hr2Id hagr2 hr2Ev
        have hagrAll : VEnvAgreeBelow n ρ2 ρL :=
          (hagr2.mono (Nat.le_succ n)).trans hagr1
        exact hk r2 ek2 ρ2 JL nr2 n' ⟨ty.toTTy, rv.setWidth ty.width⟩ σ' m'
          (Nat.le_trans (Nat.le_succ n) hnr2) hek2 hr2Id hagrAll
          (JEnvAgreeBelow.refl n JL) rfl hr2Ev hinv' hm' hK

/-! ## 2. Value-Level Simulation (`lowerVal_sound`) -/

theorem lowerVal_sound {m : LcModule} {env : LEnv} {Δ : HEnv} {Γ : Env}
    {rt : BitVec 64} {R : Mem 64 → Prop}
    {c : LCtx} {ty : LcTy} {v : LcVal}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {QH : HPost} {XH : HXPost} {QT : Post [c.retTy.toTTy]} {XT : XPost}
    {JH : HJEnv} {ρH : HValEnv} {ρL : Frontend.C0.VEnv} {JL : JEnv}
    {σ : HState} {mem : Mem 64} {K : HPost} {X : HXPost}
    (hfrag : m.inFirstOrderFragment = true)
    (henv : LEnvOk m env)
    (hΓ : HCallEnvOk m Δ Γ) (hret : HEnv.RetTyped m Δ)
    (hval : LcVal.inFirstOrder m.decls ty v = true)
    (hrun : (lowerVal env c ty v k).run n = .ok (e, n'))
    (hkMono : ∀ r, LMMono (k r))
    (hsim : HSimInv Δ rt R c n QH XH QT XT JH ρH ρL JL)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hX : HXPostRel rt R X XT)
    (hwp : HVal.wp Δ rt ρH ty v K X σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv)
        (nr nk : Nat) (w : Word) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρL → JEnvAgreeBelow n J' JL →
      (hw : w.1 = ty.toTTy) → LArg.eval ρ' ty.toTTy r = some (hw ▸ w.2) →
      HInv rt σ' → (σ'.mem rt ⋆ R) m' → K w σ' →
      LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρL JL mem := by
  cases v with
  | lit l =>
    cases l with
    | nat natV =>
      simp only [LcVal.inFirstOrder, Bool.and_eq_true] at hval
      rcases hval with ⟨hltDec, hwDec⟩
      have hlt : natV < 2 ^ 63 := decide_eq_true_eq.mp hltDec
      have hw64 : ty.width = 64 := beq_iff_eq.mp hwDec
      have htt : i64 = ty.toTTy := by simp [LcTy.toTTy, hw64, i64]
      simp only [lowerVal, hlt, ↓reduceIte] at hrun
      simp only [HVal.wp, hlt, ↓reduceIte] at hwp
      have hev := eval_cast_ty htt (LArg.eval_imm_self ρL i64 (BitVec.ofNat 64 (2 * natV + 1)))
      exact hk (imm64 (2 * natV + 1)) e ρL JL n n' (Word.i64 (BitVec.ofNat 64 (2 * natV + 1)))
        σ mem (Nat.le_refl n) hrun (argIdsBelow_imm _ _ _)
        (VEnvAgreeBelow.refl n ρL) (JEnvAgreeBelow.refl n JL) htt hev hinv hm hwp
    | scalar bvV =>
      dsimp only [lowerVal] at hrun
      dsimp only [HVal.wp] at hwp
      exact hk (imm ty.width bvV) e ρL JL n n' ⟨ty.toTTy, BitVec.ofNat ty.width bvV⟩
        σ mem (Nat.le_refl n) hrun (argIdsBelow_imm _ _ _)
        (VEnvAgreeBelow.refl n ρL) (JEnvAgreeBelow.refl n JL) rfl
        (LArg.eval_imm_self ρL ty.toTTy _) hinv hm hwp
    | str _ => cases hval
  | erased =>
    dsimp only [lowerVal] at hrun
    dsimp only [HVal.wp] at hwp
    exact hk (imm ty.width (if ty.isScalar then 0 else 1)) e ρL JL n n'
      ⟨ty.toTTy, BitVec.ofNat ty.width (if ty.isScalar then 0 else 1)⟩
      σ mem (Nat.le_refl n) hrun (argIdsBelow_imm _ _ _)
      (VEnvAgreeBelow.refl n ρL) (JEnvAgreeBelow.refl n JL) rfl
      (LArg.eval_imm_self ρL ty.toTTy _) hinv hm hwp
  | ap _ _ => cases hval
  | pap _ _ => cases hval
  | reset _ _ => cases hval
  | reuse _ _ _ _ => cases hval
  | isShared _ => cases hval
  | ctor ci as =>
    by_cases hsc : ci.isScalar = true
    · simp only [lowerVal, hsc, ↓reduceIte] at hrun
      simp only [HVal.wp, hsc, ↓reduceIte] at hwp
      let bv := BitVec.ofNat ty.width (if ty.isScalar then ci.cidx else 2 * ci.cidx + 1)
      exact hk (imm ty.width (if ty.isScalar then ci.cidx else 2 * ci.cidx + 1))
        e ρL JL n n' ⟨ty.toTTy, bv⟩ σ mem (Nat.le_refl n) hrun (argIdsBelow_imm _ _ _)
        (VEnvAgreeBelow.refl n ρL) (JEnvAgreeBelow.refl n JL) rfl
        (LArg.eval_imm_self ρL ty.toTTy bv) hinv hm hwp
    · simp only [LcVal.inFirstOrder, hsc, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hval
      have hw64 : ty.width = 64 := beq_iff_eq.mp hval.1
      have htt : i64 = ty.toTTy := by simp [LcTy.toTTy, hw64, i64]
      simp only [HVal.wp, hsc, Bool.false_eq_true, ↓reduceIte] at hwp
      cases hobj : ρH.evalObjArgs as with
      | none => simp [hobj] at hwp
      | some vs =>
        simp only [hobj] at hwp
        rcases hwp with ⟨hvslen, hci244, hci256, hmin, hmax, hcan, hK⟩
        simp only [lowerVal, hsc, Bool.false_eq_true, ↓reduceIte, lm_bind_run] at hrun
        rcases hrun with ⟨vsArgs, n1, hvs, hrunCtor⟩
        obtain ⟨hn1, hlenEq, hvsIds, hvsEv⟩ :=
          mapM_argAt_tobject_spec hsim.idsOk hsim.varRel hobj hvs
        subst n1
        refine ctor_alloc_store_wp hΓ hrunCtor hsim.rtOk hlenEq hvslen hci244 hci256
          hmin hmax hcan hvsIds hvsEv hinv hm ?_
        dsimp only
        intro p st' scal rp ek ρ' nr m' hp0 hp8 hfresh hpm hrem hremLo hscal hnr
          hinv' hm' hek hrpId hagr hrpEv
        have hrpEv' := eval_cast_ty htt hrpEv
        exact hk rp ek ρ' JL nr n' (Word.i64 p) _ m' (Nat.le_trans (Nat.le_succ n) hnr)
          hek hrpId hagr (JEnvAgreeBelow.refl n JL) htt hrpEv' hinv' hm'
          (hK p st' scal hp0 hp8 hfresh hpm hrem hremLo hscal)
  | oproj i x =>
    have hw64 : ty.width = 64 := beq_iff_eq.mp hval
    have htt : i64 = ty.toTTy := by simp [LcTy.toTTy, hw64, i64]
    dsimp only [HVal.wp] at hwp
    cases hx : ρH.getBV64? x with
    | none => simp [hx] at hwp
    | some addr =>
      simp only [hx] at hwp
      rcases hwp with ⟨o, hmObj, haddr, htag, hi, hK⟩
      obtain ⟨la, ty', hlu, htyw, hEvLa⟩ := hsim.varRel.getBV64? hx
      have hlaId := ctxIdsBelow_lookup_var hsim.idsOk hlu
      simp only [lowerVal, lm_bind_run] at hrun
      rw [ctxVar_run_of_lookup hlu] at hrun
      rcases hrun with ⟨p, n1, hp, hrunLoad⟩
      injection hp with hpe
      have hp1 : (la, ty') = p := congrArg Prod.fst hpe
      have hn1 : n = n1 := congrArg Prod.snd hpe
      subst hp1; subst hn1
      have hload := mem_load_lcnfObj_field hmObj htag hi haddr hm
      refine lm_loadAt_wp hrunLoad hEvLa hlaId hload ?_
      intro r ek ρ' nr hnr hek hrId hagr hrEv
      have hrEv' := eval_cast_ty htt hrEv
      exact hk r ek ρ' JL nr n' (Word.i64 (o.fields[i]'hi)) σ mem
        (Nat.le_trans (Nat.le_succ n) hnr) hek hrId hagr (JEnvAgreeBelow.refl n JL)
        htt hrEv' hinv hm hK
  | uproj i x =>
    have hw64 : ty.width = 64 := beq_iff_eq.mp hval
    have htt : i64 = ty.toTTy := by simp [LcTy.toTTy, hw64, i64]
    dsimp only [HVal.wp] at hwp
    cases hx : ρH.getBV64? x with
    | none => simp [hx] at hwp
    | some addr =>
      simp only [hx] at hwp
      rcases hwp with ⟨o, hmObj, haddr, hwf, htag, hfl, hboff, hK⟩
      obtain ⟨la, ty', hlu, _, hEvLa⟩ := hsim.varRel.getBV64? hx
      have hlaId := ctxIdsBelow_lookup_var hsim.idsOk hlu
      simp only [lowerVal, lm_bind_run] at hrun
      rw [ctxVar_run_of_lookup hlu] at hrun
      rcases hrun with ⟨p, n1, hp, hrunLoad⟩
      injection hp with hpe
      have hp1 : (la, ty') = p := congrArg Prod.fst hpe
      have hn1 : n = n1 := congrArg Prod.snd hpe
      subst hp1; subst hn1
      have hoff : 8 * (i - o.fields.length) + (64 + 7) / 8 ≤ o.scalarData.length := hboff
      have hload := mem_load_lcnfObj_scalar hmObj hwf htag hoff haddr hm
      have hptr : addr + BitVec.ofNat 64 (8 + 8 * o.fields.length + 8 * (i - o.fields.length)) =
          addr + BitVec.ofNat 64 (8 + 8 * i) := by
        congr 2; omega
      rw [hptr] at hload
      refine lm_loadAt_wp hrunLoad hEvLa hlaId hload ?_
      intro r ek ρ' nr hnr hek hrId hagr hrEv
      have hrEv' := eval_cast_ty htt hrEv
      exact hk r ek ρ' JL nr n' (Word.i64 (readBitsLE 64 o.scalarData (8 * (i - o.fields.length))))
        σ mem (Nat.le_trans (Nat.le_succ n) hnr) hek hrId hagr (JEnvAgreeBelow.refl n JL)
        htt hrEv' hinv hm hK
  | sproj nFld off x =>
    dsimp only [HVal.wp] at hwp
    cases hx : ρH.getBV64? x with
    | none => simp [hx] at hwp
    | some addr =>
      simp only [hx] at hwp
      rcases hwp with ⟨o, hmObj, haddr, hwf, htag, hfl, hboff, hK⟩
      obtain ⟨la, ty', hlu, _, hEvLa⟩ := hsim.varRel.getBV64? hx
      have hlaId := ctxIdsBelow_lookup_var hsim.idsOk hlu
      simp only [lowerVal, lm_bind_run] at hrun
      rw [ctxVar_run_of_lookup hlu] at hrun
      rcases hrun with ⟨p, n1, hp, hrunLoad⟩
      injection hp with hpe
      have hp1 : (la, ty') = p := congrArg Prod.fst hpe
      have hn1 : n = n1 := congrArg Prod.snd hpe
      subst hp1; subst hn1
      have hoff :
          8 * (nFld - o.fields.length) + off + (ty.width + 7) / 8 ≤ o.scalarData.length := by
        rw [toTTy_bytes_eq ty]; exact hboff
      have hload := mem_load_lcnfObj_scalar hmObj hwf htag hoff haddr hm
      have hptr : addr + BitVec.ofNat 64
          (8 + 8 * o.fields.length + (8 * (nFld - o.fields.length) + off)) =
          addr + BitVec.ofNat 64 (8 + 8 * nFld + off) := by
        congr 2; omega
      rw [hptr] at hload
      refine lm_loadAt_wp hrunLoad hEvLa hlaId hload ?_
      intro r ek ρ' nr hnr hek hrId hagr hrEv
      exact hk r ek ρ' JL nr n'
        ⟨ty.toTTy, readBitsLE ty.width o.scalarData (8 * (nFld - o.fields.length) + off)⟩
        σ mem (Nat.le_trans (Nat.le_succ n) hnr) hek hrId hagr (JEnvAgreeBelow.refl n JL)
        (Eq.refl ty.toTTy) hrEv hinv hm hK
  | fap f as =>
    exact lowerFap_sound hfrag henv hΓ hret hval hrun hkMono hsim hinv hm hX hwp hk
  | box t x =>
    dsimp only [HVal.wp] at hwp
    cases hevAt : ρH.evalArgAt (.var x) t with
    | none => simp [hevAt] at hwp
    | some w =>
      simp only [hevAt] at hwp
      simp only [HValEnv.evalArgAt] at hevAt
      cases hx : ρH x with
      | none => simp [hx] at hevAt
      | some px =>
        rcases px with ⟨tx, wx⟩
        simp only [hx] at hevAt
        by_cases hwt : wx.1 = t.toTTy
        · simp only [hwt, ↓reduceIte, Option.some.injEq] at hevAt
          subst hevAt
          obtain ⟨la, hwx, hlu, hEvLa⟩ := hsim.varRel x tx wx hx
          have hlaId := ctxIdsBelow_lookup_var hsim.idsOk hlu
          have htxEq : tx.toTTy = t.toTTy := hwx.symm.trans hwt
          have hEvT : LArg.eval ρL t.toTTy la = some (hwt ▸ wx.2) := by
            rw [← eqRec_trans hwx htxEq wx.2]
            exact eval_cast_ty htxEq hEvLa
          simp only [lowerVal, lm_bind_run] at hrun
          rw [ctxVar_run_of_lookup hlu] at hrun
          rcases hrun with ⟨p, n1, hp, hrunBox⟩
          injection hp with hpe
          have hp1 : (la, tx) = p := congrArg Prod.fst hpe
          have hn1 : n = n1 := congrArg Prod.snd hpe
          subst hp1; subst hn1
          cases t
          all_goals
            dsimp only [LcVal.inFirstOrder] at hval
            dsimp only at hwp hrunBox
          case uint64 | usize | float =>
            have hw64 : ty.width = 64 := beq_iff_eq.mp hval
            have htt : i64 = ty.toTTy := by simp [LcTy.toTTy, hw64, i64]
            rcases wx with ⟨wt, wv⟩
            dsimp only at hwt hEvT hwp
            cases hwt
            cases hbv : Word.toBV64? ⟨_, wv⟩ with
            | none => simp [hbv] at hwp
            | some v64 =>
              simp only [hbv] at hwp
              have hvEq : wv = v64 := by
                dsimp only [Word.toBV64?] at hbv
                cases hbv
                rfl
              subst hvEq
              rcases hwp with ⟨hcan, hK⟩
              refine boxU64_wp hΓ hrunBox hsim.rtOk hEvT hlaId hcan hinv hm ?_
              dsimp only
              intro p st' rp ek ρ' nr m' hp0 hp8 hfresh hpm hrem hremLo hnr
                hinv' hm' hek hrpId hagr hrpEv
              have hrpEv' := eval_cast_ty htt hrpEv
              exact hk rp ek ρ' JL nr n' (Word.i64 p) _ m' (Nat.le_trans (Nat.le_succ n) hnr)
                hek hrpId hagr (JEnvAgreeBelow.refl n JL) htt hrpEv' hinv' hm'
                (hK p st' hp0 hp8 hfresh hpm hrem hremLo)
          case uint8 | uint16 | uint32 =>
            have hw64 : ty.width = 64 := beq_iff_eq.mp hval
            have htt : i64 = ty.toTTy := by simp [LcTy.toTTy, hw64, i64]
            rcases wx with ⟨wt, wv⟩
            dsimp only at hwt hEvT hwp
            cases hwt
            cases hw64b : (Word.toWidth 64 ⟨_, wv⟩).bind Word.toBV64? with
            | none => simp [hw64b] at hwp
            | some x64 =>
              simp only [hw64b] at hwp
              have hx64 : wv.setWidth 64 = x64 := by
                dsimp only [Word.toWidth, Word.toBV64?, Option.bind] at hw64b
                cases hw64b
                rfl
              refine convW_wp hrunBox hEvT hlaId ?_
              intro r1 ek1 ρ1 nr1 hnr1 hek1 hr1Id hagr1 hr1Ev
              rw [hx64] at hr1Ev
              refine boxSmall_wp hek1 hr1Ev ?_
              intro r2 ek2 ρ2 hek2 hr2Id hagr2 hr2Ev
              have hagrAll : VEnvAgreeBelow n ρ2 ρL :=
                (hagr2.mono hnr1).trans hagr1
              have hr2Ev' := eval_cast_ty htt hr2Ev
              exact hk r2 ek2 ρ2 JL (nr1 + 2) n' (Word.i64 (x64 <<< 1 ||| 1#64)) σ mem
                (by omega) hek2 hr2Id hagrAll (JEnvAgreeBelow.refl n JL) htt hr2Ev' hinv hm hwp
          all_goals
            have hweq : ty.width = _ := beq_iff_eq.mp hval
            have htyEq : _ = ty.toTTy := (congrArg Ty.bits hweq).symm
            have hEvTy : LArg.eval ρL ty.toTTy la = some ((hwt.trans htyEq) ▸ wx.2) := by
              rw [← eqRec_trans hwt htyEq wx.2]
              exact eval_cast_ty htyEq hEvT
            exact hk la e ρL JL n n' wx σ mem (Nat.le_refl n) hrunBox hlaId
              (VEnvAgreeBelow.refl n ρL) (JEnvAgreeBelow.refl n JL)
              (hwt.trans htyEq) hEvTy hinv hm hwp
        · simp [hwt] at hevAt
  | unbox x =>
    dsimp only [HVal.wp] at hwp
    cases hx : ρH.getBV64? x with
    | none => simp [hx] at hwp
    | some addr =>
      simp only [hx] at hwp
      obtain ⟨la, ty', hlu, _, hEvLa⟩ := hsim.varRel.getBV64? hx
      have hlaId := ctxIdsBelow_lookup_var hsim.idsOk hlu
      simp only [lowerVal, lm_bind_run] at hrun
      rw [ctxVar_run_of_lookup hlu] at hrun
      rcases hrun with ⟨p, n1, hp, hrunUnbox⟩
      injection hp with hpe
      have hp1 : (la, ty') = p := congrArg Prod.fst hpe
      have hn1 : n = n1 := congrArg Prod.snd hpe
      subst hp1; subst hn1
      cases ty
      case uint64 | usize | float =>
        rcases hwp with ⟨o, hmObj, haddr, hwf, htag0, hf0, hoff, hK⟩
        have htag : o.tag ≤ 244 := by rw [htag0]; decide
        have hoff' : 0 + (64 + 7) / 8 ≤ o.scalarData.length := by simpa using hoff
        have hload := mem_load_lcnfObj_scalar hmObj hwf htag hoff' haddr hm
        have hptr : addr + BitVec.ofNat 64 (8 + 8 * o.fields.length + 0) =
            addr + BitVec.ofNat 64 8 := by
          rw [hf0]; rfl
        rw [hptr] at hload
        refine lm_loadAt_wp hrunUnbox hEvLa hlaId hload ?_
        intro r ek ρ' nr hnr hek hrId hagr hrEv
        exact hk r ek ρ' JL nr n' (Word.i64 (readBitsLE 64 o.scalarData 0)) σ mem
          (Nat.le_trans (Nat.le_succ n) hnr) hek hrId hagr (JEnvAgreeBelow.refl n JL)
          rfl hrEv hinv hm hK
      all_goals
        refine lshr64_wp hrunUnbox hEvLa (LArg.eval_imm_self ρL i64 1#64) ?_
        intro r1 ek1 ρ1 hek1 hr1Id hagr1 hr1Ev
        have h1Mod : (1#64 : BitVec 64).toNat % 64 = 1 := rfl
        rw [h1Mod] at hr1Ev
        refine convW_wp hek1 hr1Ev hr1Id ?_
        intro r2 ek2 ρ2 nr2 hnr2 hek2 hr2Id hagr2 hr2Ev
        have hagrAll : VEnvAgreeBelow n ρ2 ρL :=
          (hagr2.mono (Nat.le_succ n)).trans hagr1
        dsimp only at hwp
        refine hk r2 ek2 ρ2 JL nr2 n' _ σ mem
          (Nat.le_trans (Nat.le_succ n) hnr2) hek2 hr2Id
          hagrAll (JEnvAgreeBelow.refl n JL) ?_ ?_ hinv hm hwp
        · rfl
        · exact hr2Ev

end LeanQbe.T.LeanLCNF.Sem
