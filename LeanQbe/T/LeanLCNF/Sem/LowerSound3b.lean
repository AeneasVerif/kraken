module

public import LeanQbe.T.LeanLCNF.Sem.LowerSound3Cases

/-!
# Soundness of `lowerCode` (`Lower1.lean`)

Proves `lowerCode_sound : m.inFirstOrderFragment = true → HCodeSim m (firstOrderLEnv m)`
for all Phase-1 first-order `LcCode` constructs (`.let_` including self-tail calls, `.jp`, `.jmp`,
`.cases`, `.ret`, `.unreach`, `.inc`, `.dec`), parametric in any `Γ` satisfying `HCallEnvOk m Δ Γ`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.LeanLCNF

private theorem LcVal.inFirstOrder_fap_of_find {decls : List LcDecl} {ty : LcTy}
    {f : String} {as : List LcArg} {d : LcDecl}
    (hf : LcVal.inFirstOrder decls ty (.fap f as) = true)
    (hfind : decls.find? (·.name == f) = some d) :
    !Sem.isPrimName f = true ∧ d.params.length ≤ regArgs ∧
      argsOkForTys as (d.params.map (·.ty)) = true := by
  simp only [LcVal.inFirstOrder, hfind] at hf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
  exact ⟨hf.1.1, hf.1.2, hf.2⟩

private theorem word_bits_eq_of_width_eq {w1 w2 n0 : Nat} (h : w1 = w2) (rv0 : BitVec n0) :
    (⟨Ty.bits w2, BitVec.setWidth w2 rv0⟩ : Word) = ⟨Ty.bits w1, BitVec.setWidth w1 rv0⟩ := by
  subst h; rfl

private theorem evalArgAt_selfTail_ret {ρH : HValEnv} {x : Nat} {ty retTy : LcTy}
    {r r' w : Word}
    (htoW : Word.toWidth ty.width r = some r')
    (hev : (ρH.set x ty r').evalArgAt (.var x) retTy = some w) :
    ∃ rw, Word.toWidth retTy.width r = some rw ∧ rw = w := by
  have hset : (ρH.set x ty r') x = some (ty, r') := by simp [HValEnv.set]
  simp only [HValEnv.evalArgAt, hset] at hev
  split at hev
  · next heq =>
    injection hev with hw
    subst hw
    cases r with
    | mk rt0 rv0 =>
      cases rt0 with
      | bits n0 =>
        dsimp only [Word.toWidth] at htoW
        injection htoW with hr'
        subst hr'
        dsimp only [LcTy.toTTy] at heq
        have hwid : ty.width = retTy.width := Ty.bits.inj heq
        exact ⟨⟨Ty.bits retTy.width, BitVec.setWidth retTy.width rv0⟩, rfl,
          word_bits_eq_of_width_eq hwid rv0⟩
      | bool => simp [Word.toWidth] at htoW
      | float _ => simp [Word.toWidth] at htoW
      | pair _ _ => simp [Word.toWidth] at htoW
  · cases hev

private theorem bindAll_fields (ps : List LcParam) (as : List LArg) (c : LCtx) :
    (c.bindAll ps as).jps = c.jps ∧
      (c.bindAll ps as).loop? = c.loop? ∧
      (c.bindAll ps as).fn = c.fn ∧
      (c.bindAll ps as).params = c.params ∧
      (c.bindAll ps as).retTy = c.retTy ∧
      (c.bindAll ps as).rt = c.rt := by
  dsimp only [LCtx.bindAll]
  induction ps.zip as generalizing c with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons x xs ih => simp only [List.foldl_cons]; exact ih _

private theorem loopRel_of_eq {Δ : HEnv} {rt : BitVec 64} {R : Mem 64 → Prop}
    {c1 c2 : LCtx} {QH : HPost} {XH : HXPost} {JL : Frontend.C0.JEnv}
    (hloop : c1.loop? = c2.loop?) (hfn : c1.fn = c2.fn)
    (hps : c1.params = c2.params) (hret : c1.retTy = c2.retTy)
    (hRel : LoopRel Δ rt R c2 QH XH JL) : LoopRel Δ rt R c1 QH XH JL := by
  rcases c1 with ⟨f1, r1, rt1, ps1, v1, j1, l1⟩
  rcases c2 with ⟨f2, r2, rt2, ps2, v2, j2, l2⟩
  dsimp only at hloop hfn hps hret
  subst hloop; subst hfn; subst hps; subst hret
  exact hRel

private theorem post_cast_wp {Γ : Env} {t1 t2 : LcTy} (h : t1 = t2)
    {Q : Post [t2.toTTy]} {X : XPost} {e : LExpr} {ρ : Frontend.C0.VEnv}
    {J : JEnv} {m : Mem 64} :
    LExpr.wp Γ (h.symm ▸ Q) X e ρ J m → LExpr.wp Γ Q X e ρ J m := by
  subst h; exact id

private theorem postRel_cast {rt : BitVec 64} {t1 t2 : LcTy} (h : t1 = t2)
    {R : Mem 64 → Prop} {QH : HPost} {QT : Post [t2.toTTy]}
    (hP : HPostRel rt t2 R QH QT) : HPostRel rt t1 R QH (h.symm ▸ QT) := by
  subst h; exact hP

private theorem jenv_set_cast_eq (JL : JEnv) (n : Nat) {ts1 ts2 : List Ty}
    (h : ts1 = ts2) (k : Cont ts1) :
    JL.set n ts1 k = JL.set n ts2 (h ▸ k) := by
  cases h; rfl

private theorem tup_apply_cast {ts1 ts2 : List Ty} (h : ts1 = ts2) (k : Cont ts1)
    (xs : Tup Val ts2) (m : Mem 64) : k (h.symm ▸ xs) m → (h ▸ k) xs m := by
  cases h; exact id

private theorem mkFreshVars_id_ge (ts : List Ty) (m1 : Nat) (x1 : Frontend.C0.LVar)
    (hx : x1 ∈ mkFreshVars ts m1) : m1 ≤ x1.id := by
  induction ts generalizing m1 with
  | nil => simp [mkFreshVars] at hx
  | cons _ _ ih =>
    simp only [mkFreshVars, List.mem_cons] at hx
    rcases hx with hEq | hx'
    · subst hEq; exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_succ _) (ih _ hx')

private theorem jprel_push_jp_params {rt : BitVec 64} {R : Mem 64 → Prop} {c : LCtx}
    {JH : HJEnv} {JL : Frontend.C0.JEnv} {n j lbl : Nat} {ps : List LcParam}
    {k : Cont (ps.map (·.ty.toTTy))}
    (hids : ctxIdsBelow c n) (hjp : JpRel rt R c JH JL) (hle : n ≤ lbl) :
    let Jj := fun ws σ => HInv rt σ →
      ∀ (xs : Tup Val (ps.map (·.ty.toTTy))), wordsOfTup xs = ws →
        ∀ m', (HState.mem rt σ ⋆ R) m' → k xs m'
    JpRel rt R { c with jps := (j, lbl, ps.map (·.ty)) :: c.jps }
      (JH.set j Jj) (JL.set lbl (ps.map (·.ty.toTTy)) k) := by
  have hmap : ps.map (·.ty.toTTy) = (ps.map (·.ty)).map LcTy.toTTy := by
    simp only [List.map_map]; rfl
  revert k
  rw [hmap]
  intro k
  exact JpRel.push_jp hids hjp hle

private theorem list_mapM_map {α β γ : Type} (f : α → β) (g : β → LM γ) (xs : List α) :
    xs.mapM (fun x => g (f x)) = (xs.map f).mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.mapM_cons, List.map_cons, ih]

private theorem lookup_map_jps_none (j : Nat) :
    ∀ (jps : List (Nat × Nat × List LcTy)),
      jps.lookup j = none → (jps.map fun p => (p.1, p.2.2)).lookup j = none
  | [], _ => rfl
  | (k, _, _) :: rest, h => by
    simp only [List.lookup, List.map_cons] at h ⊢
    cases hbeq : (j == k)
    · simp only [hbeq] at h; exact lookup_map_jps_none j rest h
    · simp only [hbeq] at h; cases h

private theorem lookup_map_jps_some (j lbl : Nat) (ts : List LcTy) :
    ∀ (jps : List (Nat × Nat × List LcTy)),
      jps.lookup j = some (lbl, ts) → (jps.map fun p => (p.1, p.2.2)).lookup j = some ts
  | [], h => by cases h
  | (k, l, ts') :: rest, h => by
    simp only [List.lookup, List.map_cons] at h ⊢
    cases hbeq : (j == k)
    · simp only [hbeq] at h; exact lookup_map_jps_some j lbl ts rest h
    · simp only [hbeq] at h; injection h with hp; cases hp; rfl

private theorem lowerCode_sound_aux {m : LcModule} {env : LEnv}
    (hfrag : m.inFirstOrderFragment = true) (henv : LEnvOk m env)
    {Δ : HEnv} {Γ : Env} (hΓ : HCallEnvOk m Δ Γ) (hret : HEnv.RetTyped m Δ) :
    ∀ (code : LcCode) (c : LCtx) (n n' : Nat) (e : LExpr)
      {rt : BitVec 64} {R : Mem 64 → Prop} {QH : HPost} {XH : HXPost}
      {QT : Post [c.retTy.toTTy]} {XT : XPost} {JH : HJEnv} {ρH : HValEnv}
      {ρL : Frontend.C0.VEnv} {JL : Frontend.C0.JEnv} {σ : HState} {mem : Mem 64},
      code.inFirstOrder m.decls (c.jps.map fun p => (p.1, p.2.2)) = true →
      (lowerCode env c code).run n = .ok (e, n') →
      HSimInv Δ rt R c n QH XH QT XT JH ρH ρL JL →
      (∀ lbl, c.loop? = some lbl →
        ∃ d, m.decls.find? (·.name == c.fn) = some d ∧ c.params = d.params.map (·.ty)) →
      HInv rt σ → (HState.mem rt σ ⋆ R) mem →
      HWp Δ rt c.retTy JH ρH QH XH code σ →
      LExpr.wp Γ QT XT e ρL JL mem
  | .let_ x ty v k, c, n, n', e, rt, R, QH, XH, QT, XT, JH, ρH, ρL, JL, σ, mem,
      hc, hrun, hsim, hloop, hinv, hm, hwp => by
    rw [lowerCode.eq_1] at hrun
    rw [LcCode.inFirstOrder.eq_1, Bool.and_eq_true] at hc
    cases hst : selfTailJump? c (.let_ x ty v k) with
    | some jump =>
      rw [hst] at hrun
      dsimp only at hrun
      dsimp only [selfTailJump?] at hst
      cases hcl : c.loop? with
      | none => simp [hcl] at hst
      | some lbl =>
        simp only [hcl] at hst
        cases hv : v with
        | fap f as =>
          subst hv
          simp only at hst
          by_cases hself : isSelfTail c.fn c.params.length (.let_ x ty (.fap f as) k) = true
          · simp only [hself, ↓reduceIte] at hst
            injection hst with hj
            subst hj
            cases hk : k with
            | ret arg =>
              cases arg with
              | var y =>
                dsimp only [isSelfTail] at hself
                simp only [hk, Bool.and_eq_true, beq_iff_eq] at hself
                rcases hself with ⟨⟨rfl, rfl⟩, _⟩
                obtain ⟨d, hfind, hcParams⟩ := hloop lbl hcl
                obtain ⟨hnPrim, _, hargsOk⟩ := LcVal.inFirstOrder_fap_of_find hc.1 hfind
                have hargsOkC : argsOkForTys as c.params = true := hcParams ▸ hargsOk
                rw [HWp.eq_1, HVal.wp.eq_10] at hwp
                cases hevH : ρH.evalArgsOwn as with
                | none => simp [hevH] at hwp
                | some ws =>
                  have hnp : isPrimName c.fn = false := by
                    revert hnPrim; cases isPrimName c.fn <;> decide
                  simp only [hevH] at hwp
                  split at hwp
                  · next ht => rw [hnp] at ht; cases ht
                  · rcases hwp with ⟨P, E, hcall, hP, hE⟩
                    rw [lm_bind_run] at hrun
                    rcases hrun with ⟨las, n1, hmap, hpure⟩
                    obtain ⟨hpe1, hn1Eq⟩ := pure_run_eq hpure
                    subst hpe1; subst hn1Eq
                    obtain ⟨rfl, _, xs, hevL, hws⟩ :=
                      mapM_argAt_tys_spec hargsOkC hevH hsim.idsOk hsim.varRel hmap
                    obtain ⟨kLoop, hgetLoop, hkLoop⟩ := hsim.loopRel lbl hcl
                    refine wp_jump hgetLoop hevL (hkLoop ws σ P E hcall hinv ?_ hE xs hws mem hm)
                    intro r σ' hrP
                    obtain ⟨r', htoW, hretWp⟩ := hP r σ' hrP
                    rw [hk, HWp.eq_5] at hretWp
                    cases hevRet : (ρH.set x ty r').evalArgAt (.var x) c.retTy with
                    | none => simp [hevRet] at hretWp
                    | some w =>
                      simp only [hevRet] at hretWp
                      obtain ⟨rw, hrw, rfl⟩ := evalArgAt_selfTail_ret htoW hevRet
                      exact ⟨rw, hrw, hretWp⟩
              | erased => simp [isSelfTail, hk] at hself
            | let_ _ _ _ _ => simp [isSelfTail, hk] at hself
            | jp _ _ _ _ => simp [isSelfTail, hk] at hself
            | jmp _ _ => simp [isSelfTail, hk] at hself
            | cases _ _ => simp [isSelfTail, hk] at hself
            | unreach => simp [isSelfTail, hk] at hself
            | oset _ _ _ _ => simp [isSelfTail, hk] at hself
            | uset _ _ _ _ => simp [isSelfTail, hk] at hself
            | sset _ _ _ _ _ _ => simp [isSelfTail, hk] at hself
            | setTag _ _ _ => simp [isSelfTail, hk] at hself
            | inc _ _ _ _ => simp [isSelfTail, hk] at hself
            | dec _ _ _ _ => simp [isSelfTail, hk] at hself
            | del _ _ => simp [isSelfTail, hk] at hself
          · simp [hself] at hst
        | _ => simp [hv] at hst
    | none =>
      rw [hst] at hrun
      dsimp only at hrun
      rw [HWp.eq_1] at hwp
      have hkMono : ∀ r, LMMono (lowerCode env (c.bind x r ty) k) :=
        fun r => lowerCode_mono_of_fo hfrag henv k (c.bind x r ty) hc.2
      refine lowerVal_sound hfrag henv hΓ hret hc.1 hrun hkMono hsim hinv hm hsim.xpostRel hwp ?_
      intro r ek ρ' J' nr nk w σ' m' hnr hek hrId hagr hJ hw hrEv hinv' hm' hwpK
      have hsim' := (hsim.transfer hnr hagr hJ).bind_lcVar (x := x) hrId hw hrEv
      exact lowerCode_sound_aux hfrag henv hΓ hret k (c.bind x r ty) nr nk ek
        hc.2 hek hsim' hloop hinv' hm' hwpK
  | .jp j ps body k, c, n, n', e, rt, R, QH, XH, QT, XT, JH, ρH, ρL, JL, σ, mem,
      hc, hrun, hsim, hloop, hinv, hm, hwp => by
    rw [lowerCode.eq_2] at hrun
    rw [LcCode.inFirstOrder.eq_2, Bool.and_eq_true] at hc
    simp only [lm_bind_run] at hrun
    rcases hrun with ⟨lbl, n1, hfresh, pvs, n2, hpvs, b, n3, hbRun, kk, n4, hkkRun, hpure⟩
    simp only [fresh, modifyGet, StateT.run, MonadStateOf.modifyGet, StateT.modifyGet,
      Except.pure, Pure.pure, Except.ok.injEq, Prod.mk.injEq] at hfresh
    rcases hfresh with ⟨rfl, rfl⟩
    rw [list_mapM_map (fun p : LcParam => p.ty.toTTy) freshVar ps, mapM_freshVar_run] at hpvs
    injection hpvs with hpvPair
    have hpvEq : pvs = mkFreshVars (ps.map (·.ty.toTTy)) (n + 1) :=
      (congrArg Prod.fst hpvPair).symm
    have hn2Eq : n2 = n + 1 + ps.length := by
      have h2 := congrArg Prod.snd hpvPair
      simp only [List.length_map] at h2
      exact h2.symm
    subst hpvEq; subst hn2Eq
    obtain ⟨hpe1, hn4Eq⟩ := pure_run_eq hpure
    subst hpe1; subst hn4Eq
    let c' : LCtx := { c with jps := (j, n, ps.map (·.ty)) :: c.jps }
    have hpvTy : (mkFreshVars (ps.map (·.ty.toTTy)) (n + 1)).map (·.ty) = ps.map (·.ty.toTTy) :=
      mkFreshVars_map_ty _ (n + 1)
    rw [LExpr.wp.eq_10]
    intro Js hcl
    rcases Js with ⟨kL, ⟨⟩⟩
    have hJLbind : JL.bind (lBlockIds [(n, mkFreshVars (ps.map (·.ty.toTTy)) (n + 1), b)])
        (lBlockSig [(n, mkFreshVars (ps.map (·.ty.toTTy)) (n + 1), b)]) (kL, PUnit.unit) =
        JL.set n ((mkFreshVars (ps.map (·.ty.toTTy)) (n + 1)).map (·.ty)) kL := rfl
    rw [hJLbind] at hcl ⊢
    rw [LExpr.closed.eq_2] at hcl
    let kTyped : Cont (ps.map (·.ty.toTTy)) := hpvTy ▸ kL
    have hkSetEq : JL.set n ((mkFreshVars (ps.map (·.ty.toTTy)) (n + 1)).map (·.ty)) kL =
        JL.set n (ps.map (·.ty.toTTy)) kTyped :=
      jenv_set_cast_eq JL n hpvTy kL
    rw [hkSetEq] at hcl ⊢
    let Jj : List Word → HState → Prop := fun ws σ' =>
      HInv rt σ' → ∀ (xs : Tup Val (ps.map (·.ty.toTTy))), wordsOfTup xs = ws →
        ∀ m', (HState.mem rt σ' ⋆ R) m' → kTyped xs m'
    rw [HWp.eq_2] at hwp
    have hBodyRule : ∀ (as : List Word) (σ' : HState), paramsMatch ps as →
        HWp Δ rt c.retTy (JH.set j Jj) (ρH.bindAll ps as) QH XH body σ' → Jj as σ' := by
      intro as σ' hpm hbodyWp hinv' xs hws m' hm'
      refine tup_apply_cast hpvTy kL xs m' (hcl.1 (hpvTy.symm ▸ xs) m' ?_)
      let pvsL := (mkFreshVars (ps.map (·.ty.toTTy)) (n + 1)).map vArg
      let cBody : LCtx := c'.bindAll ps pvsL
      obtain ⟨hJpsEq, hLoopEq, hFnEq, hParamsEq, hRetEq, hRtEq⟩ := bindAll_fields ps pvsL c'
      have hcIds1 : ctxIdsBelow c (n + 1) := ctxIdsBelow_mono (Nat.le_succ n) hsim.idsOk
      have hc'Ids1 : ctxIdsBelow c' (n + 1) := ctxIdsBelow_pushJp hcIds1 (Nat.lt_succ_self n)
      have hc'Ids2 : ctxIdsBelow c' (n + 1 + ps.length) :=
        ctxIdsBelow_mono (by omega) hc'Ids1
      have hc'BindIds : ctxIdsBelow cBody (n + 1 + ps.length) :=
        ctxIdsBelow_bindAll hc'Ids2 (fun a ha => by
          have ha' := mkFreshVars_vArg_ltBound a ha
          simpa [List.length_map] using ha')
      have hrt' : LArg.eval
          (ρL.bind (mkFreshVars (ps.map (·.ty.toTTy)) (n + 1))
            ((mkFreshVars (ps.map (·.ty.toTTy)) (n + 1)).map (·.ty)) (hpvTy.symm ▸ xs))
          i64 cBody.rt = some rt := by
        rw [hRtEq, LArg.eval_bind_of_ltBound (n := n + 1)]
        · exact hsim.rtOk
        · exact argIdsBelow_mono (Nat.le_succ n) hsim.idsOk.1
        · intro b1 hb1; exact mkFreshVars_id_ge _ (n + 1) b1 hb1
      have hvar' : VarRel cBody (ρH.bindAll ps as)
          (ρL.bind (mkFreshVars (ps.map (·.ty.toTTy)) (n + 1))
            ((mkFreshVars (ps.map (·.ty.toTTy)) (n + 1)).map (·.ty)) (hpvTy.symm ▸ xs)) :=
        VarRel.bindAll_of_pushJp hc'Ids1 hsim.varRel hpm hws
      have hjp' : JpRel rt R c' (JH.set j Jj) (JL.set n (ps.map (·.ty.toTTy)) kTyped) :=
        jprel_push_jp_params hsim.idsOk hsim.jpRel (Nat.le_refl n)
      have hjpBind : JpRel rt R cBody (JH.set j Jj) (JL.set n (ps.map (·.ty.toTTy)) kTyped) := by
        intro jj ll ts hlu
        rw [hJpsEq] at hlu
        exact hjp' jj ll ts hlu
      have hloopRel' : LoopRel Δ rt R c' QH XH (JL.set n (ps.map (·.ty.toTTy)) kTyped) :=
        LoopRel.push_jp hsim.idsOk hsim.loopRel (Nat.le_refl n)
      have hloopBind : LoopRel Δ rt R cBody QH XH (JL.set n (ps.map (·.ty.toTTy)) kTyped) :=
        loopRel_of_eq hLoopEq hFnEq hParamsEq hRetEq hloopRel'
      have hpostBody : HPostRel rt cBody.retTy R QH (hRetEq.symm ▸ QT) :=
        postRel_cast hRetEq hsim.postRel
      have hsimBody : HSimInv Δ rt R cBody (n + 1 + ps.length) QH XH (hRetEq.symm ▸ QT) XT
          (JH.set j Jj) (ρH.bindAll ps as)
          (ρL.bind (mkFreshVars (ps.map (·.ty.toTTy)) (n + 1))
            ((mkFreshVars (ps.map (·.ty.toTTy)) (n + 1)).map (·.ty)) (hpvTy.symm ▸ xs))
          (JL.set n (ps.map (·.ty.toTTy)) kTyped) :=
        HSimInv.mk hc'BindIds hrt' hvar' hjpBind hloopBind hpostBody hsim.xpostRel
      have hcBodyFo : body.inFirstOrder m.decls (cBody.jps.map fun p => (p.1, p.2.2)) = true := by
        rw [hJpsEq]; exact hc.1
      have hloopBody : ∀ lbl_l, cBody.loop? = some lbl_l →
          ∃ d, m.decls.find? (·.name == cBody.fn) = some d ∧
            cBody.params = d.params.map (·.ty) := by
        intro lbl_l heq
        rw [hLoopEq] at heq; rw [hFnEq, hParamsEq]
        exact hloop lbl_l heq
      have hbodyWp' : HWp Δ rt cBody.retTy (JH.set j Jj) (ρH.bindAll ps as) QH XH body σ' := by
        rw [hRetEq]; exact hbodyWp
      refine post_cast_wp hRetEq ?_
      exact lowerCode_sound_aux hfrag henv hΓ hret body cBody (n + 1 + ps.length) n3 b
        hcBodyFo hbRun hsimBody hloopBody hinv' hm' hbodyWp'
    have hkWp := hwp Jj hBodyRule
    have hc1Bind : body.inFirstOrder m.decls
        ((c'.bindAll ps ((mkFreshVars (ps.map (·.ty.toTTy)) (n + 1)).map vArg)).jps.map
          fun p => (p.1, p.2.2)) = true := by
      rw [bindAll_jps]; exact hc.1
    have hn3 : n + 1 + ps.length ≤ n3 :=
      lowerCode_mono_of_fo hfrag henv body _ hc1Bind _ _ _ hbRun
    have hc'IdsN3 : ctxIdsBelow c' n3 :=
      ctxIdsBelow_mono hn3 (ctxIdsBelow_mono (by omega)
        (ctxIdsBelow_pushJp (ctxIdsBelow_mono (Nat.le_succ n) hsim.idsOk) (Nat.lt_succ_self n)))
    have hjpK : JpRel rt R c' (JH.set j Jj) (JL.set n (ps.map (·.ty.toTTy)) kTyped) :=
      jprel_push_jp_params hsim.idsOk hsim.jpRel (Nat.le_refl n)
    have hloopRelK : LoopRel Δ rt R c' QH XH (JL.set n (ps.map (·.ty.toTTy)) kTyped) :=
      LoopRel.push_jp hsim.idsOk hsim.loopRel (Nat.le_refl n)
    have hvarK : VarRel c' ρH ρL := hsim.varRel
    have hsimK : HSimInv Δ rt R c' n3 QH XH QT XT (JH.set j Jj) ρH ρL
        (JL.set n (ps.map (·.ty.toTTy)) kTyped) :=
      HSimInv.mk hc'IdsN3 hsim.rtOk hvarK hjpK hloopRelK hsim.postRel hsim.xpostRel
    exact lowerCode_sound_aux hfrag henv hΓ hret k c' n3 n4 kk
      hc.2 hkkRun hsimK hloop hinv hm hkWp
  | .jmp j as, c, n, n', e, rt, R, QH, XH, QT, XT, JH, ρH, ρL, JL, σ, mem,
      hc, hrun, hsim, _, hinv, hm, hwp => by
    rw [lowerCode.eq_3] at hrun
    rw [LcCode.inFirstOrder.eq_3] at hc
    rw [HWp.eq_3] at hwp
    cases hlu : List.lookup j c.jps with
    | none =>
      have hluMap := lookup_map_jps_none j c.jps hlu
      simp [hluMap] at hc
    | some p =>
      rcases p with ⟨lbl, ts⟩
      have hluMap := lookup_map_jps_some j lbl ts c.jps hlu
      simp only [hluMap] at hc
      have hlenEq : as.length = ts.length := argsOkForTys_length hc
      have hneB : (as.length != ts.length) = false := by simp [hlenEq]
      simp only [hlu, hneB, Bool.false_eq_true, ↓reduceIte] at hrun
      cases hevH : ρH.evalArgsOwn as with
      | none => simp [hevH] at hwp
      | some ws =>
        simp only [hevH] at hwp
        rw [lm_bind_run] at hrun
        rcases hrun with ⟨las, n1, hmap, hpure⟩
        obtain ⟨hpe1, hn1Eq⟩ := pure_run_eq hpure
        subst hpe1; subst hn1Eq
        obtain ⟨rfl, _, xs, hevL, hws⟩ :=
          mapM_argAt_tys_spec hc hevH hsim.idsOk hsim.varRel hmap
        obtain ⟨kL, hgetL, hkL⟩ := hsim.jpRel j lbl ts hlu
        exact wp_jump hgetL hevL (hkL ws σ hwp hinv xs hws mem hm)
  | .cases x alts, c, n, n', e, rt, R, QH, XH, QT, XT, JH, ρH, ρL, JL, σ, mem,
      hc, hrun, hsim, hloop, hinv, hm, hwp => by
    rw [lowerCode.eq_4] at hrun
    rw [LcCode.inFirstOrder.eq_4] at hc
    refine lowerCases_sound hfrag henv hc hrun hsim hm hwp (fun p hp nr nr' ek ρ' J'
        _ _ _ hek hsim' hwpP => ?_)
    have hlt : sizeOf p.2 < sizeOf (LcCode.cases x alts) := sizeOf_snd_lt_of_mem_cases hp
    have hpFo := (inFirstOrder_of_mem_alts hc p hp).2
    exact lowerCode_sound_aux hfrag henv hΓ hret p.2 c nr nr' ek
      hpFo hek hsim' hloop hinv hm hwpP
  | .ret a, c, n, n', e, rt, R, QH, XH, QT, XT, JH, ρH, ρL, JL, σ, mem,
      _, hrun, hsim, _, hinv, hm, hwp => by
    rw [lowerCode.eq_5] at hrun
    rw [HWp.eq_5] at hwp
    cases hevH : ρH.evalArgAt a c.retTy with
    | none => simp [hevH] at hwp
    | some w =>
      simp only [hevH] at hwp
      obtain ⟨la, htyEq, hargRun, hEvLa⟩ := hsim.varRel.evalArgAt hevH
      rw [lm_bind_run] at hrun
      rcases hrun with ⟨la', n1, hlaRun, hpure⟩
      rw [hargRun n] at hlaRun
      injection hlaRun with hlaPair
      have hlaEq : la' = la := (congrArg Prod.fst hlaPair).symm
      rw [hlaEq] at hpure
      obtain ⟨hpe1, hn1Eq⟩ := pure_run_eq hpure
      subst hpe1; subst hn1Eq
      have hevArgs : evalArgs ρL [c.retTy.toTTy] [la] = some (htyEq ▸ w.snd, ()) := by
        rw [evalArgs.eq_2, evalArgs.eq_1, hEvLa]
      exact wp_ret hevArgs (hsim.postRel w σ hwp htyEq mem hinv hm)
  | .unreach, c, n, n', e, rt, R, QH, XH, QT, XT, JH, ρH, ρL, JL, σ, mem,
      _, hrun, hsim, _, _, hm, hwp => by
    rw [lowerCode.eq_6] at hrun
    rw [HWp.eq_6] at hwp
    obtain ⟨hpe1, hnEq⟩ := pure_run_eq hrun
    subst hpe1; subst hnEq
    have himm : LArg.eval ρL i64 (imm64 panicUnreachable) =
        some (BitVec.ofNat 64 panicUnreachable) :=
      LArg.eval_imm_self ρL i64 _
    have hevExit : evalArgs ρL [i64, i64] [c.rt, imm64 panicUnreachable] =
        some (rt, BitVec.ofNat 64 panicUnreachable, ()) := by
      rw [evalArgs.eq_2, evalArgs.eq_2, evalArgs.eq_1, hsim.rtOk, himm]
    exact wp_exit hevExit (hsim.xpostRel _ σ hwp mem hm)
  | .inc x cnt chk k, c, n, n', e, rt, R, QH, XH, QT, XT, JH, ρH, ρL, JL, σ, mem,
      hc, hrun, hsim, hloop, hinv, hm, hwp => by
    rw [lowerCode.eq_11] at hrun
    rw [LcCode.inFirstOrder.eq_7] at hc
    rw [HWp.eq_11] at hwp
    cases hρ : ρH.getTypedBV64? x with
    | none => simp [hρ] at hwp
    | some p =>
      rcases p with ⟨ty, addr⟩
      obtain ⟨la, hlu, _, hEvLa⟩ := hsim.varRel.getTypedBV64? hρ
      have hlaId : argIdsBelow la n := ctxIdsBelow_lookup_var hsim.idsOk hlu
      rw [lm_bind_run] at hrun
      rcases hrun with ⟨⟨xa, xt⟩, n1, hvar, hrunInc⟩
      obtain ⟨hn1, hlu2⟩ := ctxVar_run_eq hvar
      subst n1
      rw [hlu] at hlu2
      injection hlu2 with hlap
      have rfl_xa : xa = la := (congrArg Prod.fst hlap).symm
      have rfl_xt : xt = ty := (congrArg Prod.snd hlap).symm
      subst rfl_xa; subst rfl_xt
      have hkMono : LMMono (lowerCode env c k) := lowerCode_mono_of_fo hfrag henv k c hc
      refine emitInc_wp hrunInc hkMono hEvLa hlaId hinv hm ?_
      simp only [hρ] at hwp
      split
      · next hskip =>
        split at hwp
        · intro ek hek
          exact lowerCode_sound_aux hfrag henv hΓ hret k c n n' ek hc hek hsim hloop hinv hm hwp
        · exact absurd hskip ‹_›
      · next hnoSkip =>
        split at hwp
        · exact absurd ‹_› hnoSkip
        · split
          · next hbit =>
            split at hwp
            · rcases hwp with ⟨rfl, rfl, hwpK⟩
              refine ⟨rfl, rfl, fun ek ρ' J' nr nk hnr hek hagr hJ => ?_⟩
              have hsim' := HSimInv.transfer hsim hnr hagr hJ
              exact lowerCode_sound_aux hfrag henv hΓ hret k c nr nk ek hc hek hsim' hloop
                hinv hm hwpK
            · exact absurd hbit ‹_›
          · next hnbit =>
            split at hwp
            · exact absurd ‹_› hnbit
            · rcases hwp with ⟨idx, hidx, haddr, hwf, _, hwpK⟩
              refine ⟨idx, hidx, haddr, hwf, fun ek ρ' J' nr nk m' hnr hek hagr hJ hinv' hm' => ?_⟩
              have hsim' := HSimInv.transfer hsim hnr hagr hJ
              exact lowerCode_sound_aux hfrag henv hΓ hret k c nr nk ek hc hek hsim' hloop
                hinv' hm' hwpK
  | .dec x cnt chk k, c, n, n', e, rt, R, QH, XH, QT, XT, JH, ρH, ρL, JL, σ, mem,
      hc, hrun, hsim, hloop, hinv, hm, hwp => by
    rw [lowerCode.eq_12] at hrun
    rw [LcCode.inFirstOrder.eq_8] at hc
    rw [HWp.eq_12] at hwp
    cases hρ : ρH.getTypedBV64? x with
    | none => simp [hρ] at hwp
    | some p =>
      rcases p with ⟨ty, addr⟩
      obtain ⟨la, hlu, _, hEvLa⟩ := hsim.varRel.getTypedBV64? hρ
      have hlaId : argIdsBelow la n := ctxIdsBelow_lookup_var hsim.idsOk hlu
      rw [lm_bind_run] at hrun
      rcases hrun with ⟨⟨xa, xt⟩, n1, hvar, hrunDec⟩
      obtain ⟨hn1, hlu2⟩ := ctxVar_run_eq hvar
      subst n1
      rw [hlu] at hlu2
      injection hlu2 with hlap
      have rfl_xa : xa = la := (congrArg Prod.fst hlap).symm
      have rfl_xt : xt = ty := (congrArg Prod.snd hlap).symm
      subst rfl_xa; subst rfl_xt
      have hkMono : LMMono (lowerCode env c k) := lowerCode_mono_of_fo hfrag henv k c hc
      simp only [hρ] at hwp
      refine emitDec_wp hΓ hkMono cnt n n' e ρL JL σ mem hrunDec hsim.rtOk hsim.idsOk.1
        hEvLa hlaId hinv hm hwp ?_
      intro ek ρ' J' nr nk σ' m' hnr hek hagr hJ hinv' hm' hwpK
      have hsim' := HSimInv.transfer hsim hnr hagr hJ
      exact lowerCode_sound_aux hfrag henv hΓ hret k c nr nk ek hc hek hsim' hloop hinv' hm' hwpK
  | .oset _ _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc,
      _, _, _, _, _, _ => by
    simp [LcCode.inFirstOrder.eq_9] at hc
  | .uset _ _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc,
      _, _, _, _, _, _ => by
    simp [LcCode.inFirstOrder.eq_10] at hc
  | .sset _ _ _ _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc,
      _, _, _, _, _, _ => by
    simp [LcCode.inFirstOrder.eq_11] at hc
  | .setTag _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc,
      _, _, _, _, _, _ => by
    simp [LcCode.inFirstOrder] at hc
  | .del _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc,
      _, _, _, _, _, _ => by
    simp [LcCode.inFirstOrder] at hc
termination_by code => sizeOf code
decreasing_by
  all_goals first
    | (simp only [LcCode.let_.sizeOf_spec]; omega)
    | (simp only [LcCode.jp.sizeOf_spec]; omega)
    | (simp only [LcCode.inc.sizeOf_spec]; omega)
    | (simp only [LcCode.dec.sizeOf_spec]; omega)
    | exact hlt

/-- Full body simulation theorem for Phase-1 first-order `LeanLCNF` modules. -/
theorem lowerCode_sound {m : LcModule} (hfrag : m.inFirstOrderFragment = true) :
    HCodeSim m (firstOrderLEnv m) := by
  intro Δ Γ rt R c n n' code e QH XH QT XT JH ρH ρL JL σ mem
    hΓ hret hc hrun hsim hloop hinv hm hwp
  exact lowerCode_sound_aux hfrag (firstOrderLEnv_ok hfrag) hΓ hret code c n n' e
    hc hrun hsim hloop hinv hm hwp

end LeanQbe.T.LeanLCNF.Sem
