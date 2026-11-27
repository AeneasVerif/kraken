module

public import LeanQbe.T.LeanLCNF.Sem.PerceusJp4

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T

section JmpInvs

private theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = Except.ok b) : ∃ a, x = Except.ok a ∧ f a = Except.ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem snd_mem_of_mem_zip {α β : Type} {xs : List α} {ys : List β} {a : α} {b : β}
    (h : (a, b) ∈ xs.zip ys) : b ∈ ys := by
  induction xs generalizing ys with
  | nil => simp at h
  | cons x rest ih =>
    cases ys with
    | nil => simp at h
    | cons y ys' =>
      rcases List.mem_cons.mp h with h0 | htail
      · cases h0; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih htail)

private theorem jmp_ctxS_invs {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState}
    {Jp : PResJEnv} {Jh : HJEnv} {e : JpEntry} {as : List LcArg} {ctx1 : RcCtx}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hsbv : SharedBoolVars rf.ctx) (hsbp : SharedBoolPreds rf.ctx)
    (hok : JpEntryOk rt rf0 σ0 Jp Jh e)
    (ha1 : rf.ctx.applyArgs as (e.info.params.map (·.borrow)) = Except.ok ctx1)
    (hleaks : ctx1.checkNoLeaks e.info.scopeIds = Except.ok ())
    (hw_base : CtxWeakens e.baseCtx (ctx1.restrict e.info.scopeIds)) :
    let ctxS := ctx1.restrict e.info.scopeIds
    let rfB_ctx := e.baseCtx.bindParams e.info.params
    (ctxS.vars.map RcVar.id).Nodup ∧ CleanVars ctxS ∧ ParentsOwned ctxS ∧
    NoRcCorrect ctxS ∧ SharedBoolVars ctxS ∧ SharedBoolPreds ctxS ∧
    CleanVars rfB_ctx ∧ ParentsOwned rfB_ctx ∧ NoRcCorrect rfB_ctx ∧
    SharedBoolVars rfB_ctx ∧ SharedBoolPreds rfB_ctx := by
  intro ctxS rfB_ctx
  have hsB := hok.2.2.2.2.1
  have hndP := hok.2.2.1
  have hfrB := hok.2.2.2.1
  have hnd1 := applyArgs_nodup hinv.2.1 ha1
  have hclean1 := (cleanVars_applyArgs hinv.2.1 hclean as (e.info.params.map (·.borrow)) ha1).1
  have hpo1 := parentsOwned_applyArgs hinv.2.1 hclean hpo as (e.info.params.map (·.borrow)) ha1
  have hnorc1 := noRcCorrect_applyArgs hinv.2.1 hnorc as (e.info.params.map (·.borrow)) ha1
  obtain ⟨hsbv1, hsbp1⟩ := sharedBool_applyArgs hinv.2.1 hsbv hsbp ha1
  obtain ⟨hndS, hcleanS, hpoS, hnorcS, hsbvS, hsbpS, _⟩ :=
    restrict_ctx_invs hnd1 hclean1 hpo1 hnorc1 hsbv1 hsbp1 hleaks
  have hsame : ∀ v ∈ ctxS.vars, ∃ w ∈ e.baseCtx.vars, w.id = v.id := by
    have hperm_sc := hok.2.2.2.2.2.1
    have hnd_sc : e.info.scopeIds.Nodup := nodup_of_perm_nodup hperm_sc hsB.1
    have hiff_ids : ∀ z, z ∈ ctxS.vars.map RcVar.id ↔ z ∈ e.baseCtx.vars.map RcVar.id := by
      intro z
      constructor
      · intro hz
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
        have hmem_sc : v.id ∈ e.info.scopeIds := by
          have h1 := (restrict_mem_iff.mp hv).2
          exact List.contains_iff_mem.mp h1
        exact (perm_symm_mem hperm_sc).mpr hmem_sc
      · intro hz
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
        obtain ⟨v, hv, hwid, _⟩ := hw_base.2.2.1 w hw
        exact List.mem_map.mpr ⟨v, hv, hwid.symm⟩
    have hperm_S_B := perm_of_nodup_mem hndS hsB.1 hiff_ids
    intro v hv
    have hid_in : v.id ∈ e.baseCtx.vars.map RcVar.id :=
      (perm_symm_mem hperm_S_B).mp (List.mem_map.mpr ⟨v, hv, rfl⟩)
    obtain ⟨w, hw, heq⟩ := List.mem_map.mp hid_in
    exact ⟨w, hw, heq⟩
  have hcleanB := cleanVars_of_ctxWeakens hw_base hcleanS
  have hpoB := parentsOwned_of_ctxWeakens hw_base hpoS hsame
  have hsbvB := sharedBoolVars_of_ctxWeakens hw_base hsbvS
  have hcleanB_ps := (cleanVars_bindParams hsB.1 hcleanB e.info.params).1
  have hpoB_ps := parentsOwned_bindParams hsB.1 hpoB hndP hfrB
  have hnorcB_ps := bindParams_noRcCorrect hsB.1 hsB.2.1 e.info.params
  have hsbvB_ps : SharedBoolVars rfB_ctx := by
    intro p hp vb hgb
    have hpB : p ∈ e.baseCtx.sharedPreds := by rwa [bindParams_sharedPreds] at hp
    have hnot1 : ∀ q ∈ e.info.params, q.id ≠ p.1 := fun q hq heq =>
      (binderFreshOwned_sharedPreds (List.all_eq_true.mp hfrB q hq) hpB).1 heq.symm
    rw [bindParams_get?_of_not_mem hsB.1 e.info.params hnot1] at hgb
    exact hsbvB p hpB vb hgb
  have hsbpB_ps : SharedBoolPreds rfB_ctx := by
    intro p hp
    have hpB : p ∈ e.baseCtx.sharedPreds := by rwa [bindParams_sharedPreds] at hp
    have hnot1 : ∀ q ∈ e.info.params, q.id ≠ p.1 := fun q hq heq =>
      (binderFreshOwned_sharedPreds (List.all_eq_true.mp hfrB q hq) hpB).1 heq.symm
    obtain ⟨vb, hgb, hnr⟩ := hsB.2.2.1 p hpB
    refine ⟨vb, ?_, hnr⟩
    rw [bindParams_get?_of_not_mem hsB.1 e.info.params hnot1]
    exact hgb
  exact ⟨hndS, hcleanS, hpoS, hnorcS, hsbvS, hsbpS,
    hcleanB_ps, hpoB_ps, hnorcB_ps, hsbvB_ps, hsbpB_ps⟩

private theorem varInv_bindParams_keep {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState}
    {Jp : PResJEnv} {Jh : HJEnv} {e : JpEntry} {ρP : PValEnv} {as : List LcArg} {ctx1 : RcCtx}
    {pvs : List PVal} {ws : List Word}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx)
    (hok : JpEntryOk rt rf0 σ0 Jp Jh e) (hlive : JpEntryLiveAgree e rf ρP)
    (ha1 : rf.ctx.applyArgs as (e.info.params.map (·.borrow)) = Except.ok ctx1)
    (hw_base : CtxWeakens e.baseCtx (ctx1.restrict e.info.scopeIds))
    (hcleanS : CleanVars (ctx1.restrict e.info.scopeIds))
    (hcleanB_ps : CleanVars (e.baseCtx.bindParams e.info.params))
    (hpoB_ps : ParentsOwned (e.baseCtx.bindParams e.info.params))
    (hnoMut : ∀ id ∈ baseCtxLiveIds e.baseCtx, id ∉ e.mutVars)
    (hext : e.extH = rf.extH)
    {v : RcVar} (hv_mem : v ∈ e.baseCtx.vars) (hnotP : ∀ p ∈ e.info.params, p.id ≠ v.id)
    (hvl : v.isLive = true) :
    let rfB : RcFrame := {
      ctx := e.baseCtx.bindParams e.info.params, envP := e.envPJp.bindAll e.info.params pvs,
      envH := e.envHJp.bindAll e.info.params ws, extH := e.extH, ghostH := rf.ghostH }
    VarInv v rfB σ.objs := by
  intro rfB _
  have hsB := hok.2.2.2.2.1
  have hfrB := hok.2.2.2.1
  obtain ⟨vs, v_rf, _, hvs_get, hrf_get, hrf_mem, hrf_live, hwid, hid_rf,
    hrf_no, hrf_ps, hrf_ty, hvs_no, hvs_ps, hvs_ow, _, hbr_rel, hex_rel,
    heP, heH, _, _⟩ :=
    baseCtx_live_agree_rf hinv hclean hok hlive ha1 hw_base hcleanS hnoMut hv_mem hvl
  obtain ⟨pv, w, hPv, hHv, hvr, hrest⟩ := hinv.2.2.2.1 v_rf hrf_mem hrf_live
  have hPvB : rfB.envP v.id = some pv := by
    dsimp only [rfB]
    rw [bindAllP_of_not_mem e.info.params e.envPJp pvs hnotP, ← heP, ← hid_rf]
    exact hPv
  have hHvB : rfB.envH v.id = some (v.ty, w) := by
    dsimp only [rfB]
    rw [bindAllH_of_not_mem e.info.params e.envHJp ws hnotP, ← heH, ← hid_rf, ← hrf_ty]
    exact hHv
  refine ⟨pv, w, hPvB, hHvB, hrf_ty ▸ hvr, fun hvnsc => ?_⟩
  have hrf_nsc : ¬v_rf.ty.isScalar = true := by rw [hrf_ty]; exact hvnsc
  obtain ⟨bv, hwbv, hno_rf, hps_rf, hex_rf, hbr_rf⟩ := hrest hrf_nsc
  refine ⟨bv, hwbv, fun hno => hno_rf (hrf_no.trans hno),
    fun hps hb0 => hps_rf (hrf_ps.trans hps) hb0, fun hex => ?_, fun hno hps hbr hb0 => ?_⟩
  · obtain ⟨hes, herf⟩ := hex_rel hex
    obtain ⟨h1, h2, h3, h4⟩ := hex_rf herf
    have hnd1 := applyArgs_nodup hinv.2.1 ha1
    have hvs_mem1 : vs ∈ ctx1.vars := (restrict_mem_iff.mp (RcCtx.get?_mem hvs_get).1).1
    have hvs_get1 : ctx1.get? v.id = some vs := by
      rw [← hwid]; exact (RcCtx.mem_get?_iff hnd1).mpr hvs_mem1
    obtain ⟨v_orig, hg_orig, _, how_orig⟩ := applyArgs_excl_owned_eq hinv.2.1 ha1 hvs_get1 hes
    rw [hrf_get, Option.some.injEq] at hg_orig
    cases hg_orig
    have heq_ow := how_orig (by omega)
    have how_eq : v.owned = 1 := by
      rw [← hvs_ow, heq_ow, h3]
    exact ⟨hrf_no.symm.trans h1, hrf_ps.symm.trans h2, how_eq, h4⟩
  · obtain ⟨_, _, hbrf, hprf⟩ := hbr_rel hbr
    have hno' : v_rf.noRc = false := hrf_no.trans hno
    have hps'' : v_rf.persistent = false := hrf_ps.trans hps
    obtain ⟨_, hpar_rf⟩ := hbr_rf hno' hps'' hbrf hb0
    have hframe_ext : ∀ r ∈ rfB.extH ++ rfB.ghostH, r ∈ frameHandles rfB := by
      intro r hr; rw [frameHandles.eq_1, List.append_assoc]; exact List.mem_append.mpr (Or.inr hr)
    cases hvp : v.parent? with
    | none =>
      have hvp_rf : v_rf.parent? = none := hprf.trans hvp
      rw [hvp_rf] at hpar_rf
      have hb_ext : Backed σ.objs (rfB.extH ++ rfB.ghostH) bv := by
        simpa [rfB, hext] using hpar_rf
      exact ⟨backed_mono_roots hframe_ext hb_ext, hb_ext⟩
    | some par =>
      have hvp_rf : v_rf.parent? = some par := hprf.trans hvp
      rw [hvp_rf] at hpar_rf
      obtain ⟨_, _, _, _, _, _, hpar_bv⟩ := hpar_rf
      have hv_mem_ps : v ∈ rfB.ctx.vars := by
        have hgB := baseCtx_vars_of_mem_nodup hsB.1 hv_mem
        rw [← bindParams_get?_of_not_mem hsB.1 e.info.params hnotP] at hgB
        exact (RcCtx.get?_mem hgB).1
      obtain ⟨pw, hpw_mem, hpw_id, hpw_no, hpw_ps, hpw_ow, _⟩ := hpoB_ps v hv_mem_ps par hvp
      have hnot_par : ∀ q ∈ e.info.params, q.id ≠ par := by
        intro q hq heq
        have hfr_q := List.all_eq_true.mp hfrB q hq
        simp only [binderFreshOwned, Bool.and_eq_true, List.all_eq_true] at hfr_q
        have h1 := hfr_q.1.1 v hv_mem
        simp [hvp, heq] at h1
      have hpw_base : pw ∈ e.baseCtx.vars := by
        have hndB_ps := bindParams_nodup hsB.1 e.info.params
        have hg_ps := baseCtx_vars_of_mem_nodup hndB_ps hpw_mem
        rw [hpw_id, bindParams_get?_of_not_mem hsB.1 e.info.params hnot_par] at hg_ps
        exact (RcCtx.get?_mem hg_ps).1
      have hpw_live : pw.isLive = true := by simp [RcVar.isLive, hpw_ow]
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, heH_par, _, _⟩ :=
        baseCtx_live_agree_rf hinv hclean hok hlive ha1 hw_base hcleanS hnoMut hpw_base hpw_live
      have heq_env_par : rfB.envH par = rf.envH par := by
        dsimp only [rfB]
        rw [bindAllH_of_not_mem e.info.params e.envHJp ws hnot_par, ← hpw_id, ← heH_par, hpw_id]
      have hb_parent : Backed σ.objs ((match rfB.envH par with
          | some (_, wp) => match wp.toBV64? with | some bp => [bp] | none => []
          | none => []) ++ (rfB.extH ++ rfB.ghostH)) bv := by
        dsimp only [rfB] at heq_env_par ⊢
        rw [heq_env_par, hext]
        exact hpar_bv
      refine ⟨?_, pw, hpw_mem, hpw_id, hpw_no, hpw_ps, Or.inl hpw_ow, hb_parent⟩
      rcases hb_parent with hor | ⟨r, hr_mem, hreach⟩
      · exact Or.inl hor
      · rcases List.mem_append.mp hr_mem with hr_p | hr_e
        · cases hpar_e : rfB.envH par with
          | none => simp [hpar_e] at hr_p
          | some wp =>
            cases hbv_p : wp.2.toBV64? with
            | none => simp [hpar_e, hbv_p] at hr_p
            | some bp =>
              simp only [hpar_e, hbv_p, List.mem_singleton] at hr_p
              rw [hr_p] at hreach
              obtain ⟨o0, ho0, hoa0, _⟩ := nonPersistReach_root_mem hreach
              have hbw0 : (bp &&& 1#64 == 0#64) = true :=
                beq_iff_eq.mpr (hoa0 ▸ obj_addr_and1_zero (hinv.1.1.2.1 o0 ho0))
              have hpw_rt : pw.resetTok = false := (hcleanB_ps pw hpw_mem).2.2.2.2
              have hpw_ow0 : (pw.owned == 0) = false := beq_false_of_ne (Nat.ne_of_gt hpw_ow)
              have hin_vh : bp ∈ varHandles rfB.envH pw := by
                rw [varHandles]
                simp only [hpw_no, hpw_ps, hpw_rt, hpw_ow0, Bool.or_self,
                  Bool.false_eq_true, ↓reduceIte, hpw_id, hpar_e, hbv_p, hbw0]
                exact List.mem_replicate.mpr ⟨Nat.ne_of_gt hpw_ow, rfl⟩
              have hin_fh : bp ∈ frameHandles rfB := by
                rw [frameHandles.eq_1]
                exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
                  (Or.inl (List.mem_flatten.mpr ⟨varHandles rfB.envH pw,
                    List.mem_map.mpr ⟨pw, hpw_mem, rfl⟩, hin_vh⟩))))
              exact Or.inr ⟨bp, hin_fh, hreach⟩
        · exact Or.inr ⟨r, hframe_ext r hr_e, hreach⟩

private theorem lcTy_beq_eq {a b : LcTy} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

private theorem varInv_bindParams_param {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    {as : List LcArg} {ctx1 : RcCtx} {ps : List LcParam}
    {pvs : List PVal} {ws : List Word}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hnorc : NoRcCorrect rf.ctx)
    (hndP : (ps.map (·.id)).Nodup)
    (hlen1 : pvs.length = ps.length) (hlen2 : ws.length = ps.length) (hlen3 : as.length = ps.length)
    (envPJp : PValEnv) (envHJp : HValEnv) (extH : List (BitVec 64))
    (ha1 : rf.ctx.applyArgs as (ps.map (·.borrow)) = Except.ok ctx1)
    (hmatch : argsMatchTys rf.ctx as (ps.map (·.ty)) = true)
    (hbext : argsBorrowFromExt ctx1 as (ps.map (·.borrow)) = true)
    (hpvs : rf.envP.evalArgs as = some pvs) (hws : rf.envH.evalArgsOwn as = some ws)
    (hext : extH = rf.extH)
    {p : LcParam} (hp : p ∈ ps) :
    let rfB : RcFrame := {
      ctx := RcCtx.mk [] [], envP := envPJp.bindAll ps pvs,
      envH := envHJp.bindAll ps ws, extH := extH, ghostH := rf.ghostH }
    let v : RcVar :=
      if p.borrow = true then
        { id := p.id, ty := p.ty, noRc := !p.ty.needsRc,
          persistent := false, borrowed := !(!p.ty.needsRc) && true, parent? := none }
      else
        { id := p.id, ty := p.ty, noRc := !p.ty.needsRc, persistent := false,
          owned := if ((!p.ty.needsRc) || false) = true then 0 else 1,
          excl := false, resetTok := false }
    VarInv v { rfB with ctx := rf.ctx } σ.objs := by
  intro rfB v _
  obtain ⟨a, pv, w, hpa_mem, hPvB, hHvB, hpa, hwa⟩ :=
    bindAll_eval_at_param ps as pvs ws hndP hlen1 hlen2 hlen3 envPJp envHJp rf hmatch hpvs hws hp
  have hvid : v.id = p.id := by by_cases hbr : p.borrow = true <;> simp [v, hbr]
  have hvty : v.ty = p.ty := by by_cases hbr : p.borrow = true <;> simp [v, hbr]
  have hvp : v.persistent = false := by by_cases hbr : p.borrow = true <;> simp [v, hbr]
  have hvex : v.excl = false := by by_cases hbr : p.borrow = true <;> simp [v, hbr]
  have hvpar : v.parent? = none := by by_cases hbr : p.borrow = true <;> simp [v, hbr]
  have hvnr : v.noRc = !p.ty.needsRc := by by_cases hbr : p.borrow = true <;> simp [v, hbr]
  have hvbr : v.borrowed = (p.borrow && p.ty.needsRc) := by
    by_cases hbr : p.borrow = true <;> by_cases hnr : p.ty.needsRc = true <;> simp [v, hbr, hnr]
  have hframe_ext : ∀ r ∈ extH ++ rf.ghostH,
      r ∈ localHandles rf.ctx (envHJp.bindAll ps ws) ++ (extH ++ rf.ghostH) := fun r hr =>
    List.mem_append.mpr (Or.inr hr)
  refine ⟨pv, w, by simpa [hvid] using hPvB, by simpa [hvid, hvty] using hHvB, ?_, fun hvnsc => ?_⟩
  · have hm := argsMatchTys_mem hmatch hpa_mem
    cases a with
    | erased =>
      simp only [PValEnv.evalArg, Option.some.injEq] at hpa; subst hpa
      simp only [HValEnv.evalArgOwn, Option.some.injEq] at hwa; subst hwa
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hm
      obtain ⟨⟨hns, hne_obj⟩, hne_tag⟩ := hm
      rw [hvty, ValRep]
      simp only [hns, Bool.false_eq_true, ↓reduceIte]
      exact ⟨1#64, rfl, by rw [ObjRep.eq_1],
        fun h => absurd hne_obj (by rw [h]; decide),
        fun h => absurd hne_tag (by rw [h]; decide)⟩
    | var z =>
      have hlive_a := applyArgs_var_live hinv.2.1 hclean ha1 (LcArg.var z)
        (snd_mem_of_mem_zip hpa_mem)
      rcases hlive_a with h0 | ⟨z', vz, heqz, hgz, hlivez⟩
      · cases h0
      · cases heqz
        have hmemz := RcCtx.get?_mem hgz
        obtain ⟨pvv, wv, hPv, hHv, hvr, _⟩ := hinv.2.2.2.1 vz hmemz.1 hlivez
        simp only [PValEnv.evalArg] at hpa
        rw [← hmemz.2, hPv, Option.some.injEq] at hpa; subst hpa
        simp only [HValEnv.evalArgOwn] at hwa
        rw [← hmemz.2, hHv, Option.map_some, Option.some.injEq] at hwa; subst hwa
        simp only [hgz, Bool.and_eq_true] at hm
        obtain ⟨⟨⟨⟨hsc, hw⟩, hobj⟩, htag⟩, _⟩ := hm
        have hsc' : vz.ty.isScalar = p.ty.isScalar := beq_iff_eq.mp hsc
        have hw' : vz.ty.width = p.ty.width := beq_iff_eq.mp hw
        have hobj' : p.ty = LcTy.object → vz.ty = LcTy.object := fun h =>
          lcTy_beq_eq ((of_decide_eq_true hobj) (by rw [h]; decide))
        have htag' : p.ty = LcTy.tagged → vz.ty = LcTy.tagged := fun h =>
          lcTy_beq_eq ((of_decide_eq_true htag) (by rw [h]; decide))
        rw [hvty]
        exact valRep_cast hvr hsc' hw' hobj' htag'
  · cases a with
    | erased =>
      simp only [HValEnv.evalArgOwn, Option.some.injEq] at hwa; subst hwa
      refine ⟨1#64, rfl, fun _ => by decide, fun hp_abs => by simp [hvp] at hp_abs,
        fun he_abs => by simp [hvex] at he_abs, fun _ _ _ hb0 => by
          exfalso; revert hb0; decide⟩
    | var z =>
      have hlive_a := applyArgs_var_live hinv.2.1 hclean ha1 (LcArg.var z)
        (snd_mem_of_mem_zip hpa_mem)
      rcases hlive_a with h0 | ⟨z', vz, heqz, hgz, hlivez⟩
      · cases h0
      · cases heqz
        have hmemz := RcCtx.get?_mem hgz
        obtain ⟨_, wv, _, hHv, _, hrest⟩ := hinv.2.2.2.1 vz hmemz.1 hlivez
        simp only [HValEnv.evalArgOwn] at hwa
        rw [← hmemz.2, hHv, Option.map_some, Option.some.injEq] at hwa; subst hwa
        have hm := argsMatchTys_mem hmatch hpa_mem
        simp only [hgz, Bool.and_eq_true] at hm
        have hsc : vz.ty.isScalar = p.ty.isScalar := beq_iff_eq.mp hm.1.1.1.1
        have hpnsc : ¬p.ty.isScalar = true := by rw [← hvty]; exact hvnsc
        have hzv_nsc : ¬vz.ty.isScalar = true := by rw [hsc]; exact hpnsc
        obtain ⟨bv, hwbv, hno_z, hps_z, _, hbr_z⟩ := hrest hzv_nsc
        refine ⟨bv, hwbv, fun hno => ?_, fun hp_abs => by simp [hvp] at hp_abs,
          fun he_abs => by simp [hvex] at he_abs, fun hnoF hpsF hbrT hb0 => ?_⟩
        · have hnrF : p.ty.needsRc = false := by rw [hvnr] at hno; simpa using hno
          have hpnsc' : p.ty.isScalar = false := Bool.eq_false_iff.mpr hpnsc
          have hm2 := hm.2
          simp only [hpnsc', hnrF, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
            Bool.or_eq_true] at hm2
          have hvz_no : vz.noRc = true := by
            rcases hm2 with htag | hno'
            · by_cases hvno' : vz.noRc = true
              · exact hvno'
              · exfalso
                have htz : vz.ty = LcTy.tagged := lcTy_beq_eq htag
                have hnr_z := hnorc vz hmemz.1 (Bool.eq_false_iff.mpr hvno')
                simp [htz, LcTy.needsRc] at hnr_z
            · exact hno'
          exact hno_z hvz_no
        · have hbr_p : p.borrow = true := by
            rw [hvbr] at hbrT; exact (Bool.and_eq_true _ _ |>.mp hbrT).1
          have hbe := argsBorrowFromExt_mem hbext hpa_mem hbr_p
          cases hg1 : ctx1.get? z with
          | none => simp [hg1] at hbe
          | some v1 =>
            simp only [hg1, Bool.and_eq_true, Bool.or_eq_true] at hbe
            obtain ⟨vz', hgz', _, hno_eq, hps_eq, _, _, hbr_eq, _⟩ :=
              applyArgs_get?_live_back hinv.2.1 hclean ha1 z hg1 hbe.1
            rw [hgz, Option.some.injEq] at hgz'; subst hgz'
            rcases hbe.2 with (hv1_no | hv1_ps) | hv1_br
            · exfalso; exact hno_z (hno_eq.symm ▸ hv1_no) hb0
            · obtain ⟨o, ho, hoa, horc⟩ := hps_z (hps_eq.symm ▸ hv1_ps) hb0
              have hb_eq : Backed σ.objs (extH ++ rf.ghostH) bv := Or.inl ⟨o, ho, hoa, horc⟩
              exact ⟨Or.inl ⟨o, ho, hoa, horc⟩, by simpa [hvpar] using hb_eq⟩
            · have hv1_b := hv1_br.1
              have hv1_p : v1.parent? = none := by simpa [Option.isNone_iff_eq_none] using hv1_br.2
              obtain ⟨hz_b, hz_p⟩ := hbr_eq hv1_b
              have hz_no : vz.noRc = false := (hclean vz hmemz.1).2.2.1 hz_b |>.1
              have hz_ps : vz.persistent = false := (hclean vz hmemz.1).2.2.1 hz_b |>.2.1
              obtain ⟨_, hpar_z⟩ := hbr_z hz_no hz_ps hz_b hb0
              rw [hz_p, hv1_p] at hpar_z
              have hb_eq : Backed σ.objs (extH ++ rf.ghostH) bv := by
                simpa [hext] using hpar_z
              have hmono : Backed σ.objs
                  (localHandles rf.ctx (envHJp.bindAll ps ws) ++ extH ++ rf.ghostH) bv := by
                rw [List.append_assoc]; exact backed_mono_roots hframe_ext hb_eq
              exact ⟨hmono, by simpa [hvpar] using hb_eq⟩

private theorem varInv_bindParams_jmp {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState}
    {Jp : PResJEnv} {Jh : HJEnv} {e : JpEntry} {ρP : PValEnv} {as : List LcArg} {ctx1 : RcCtx}
    {pvs : List PVal} {ws : List Word}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hnorc : NoRcCorrect rf.ctx)
    (hok : JpEntryOk rt rf0 σ0 Jp Jh e) (hlive : JpEntryLiveAgree e rf ρP)
    (ha1 : rf.ctx.applyArgs as (e.info.params.map (·.borrow)) = Except.ok ctx1)
    (hw_base : CtxWeakens e.baseCtx (ctx1.restrict e.info.scopeIds))
    (hcleanS : CleanVars (ctx1.restrict e.info.scopeIds))
    (hcleanB_ps : CleanVars (e.baseCtx.bindParams e.info.params))
    (hpoB_ps : ParentsOwned (e.baseCtx.bindParams e.info.params))
    (hnoMut : ∀ id ∈ baseCtxLiveIds e.baseCtx, id ∉ e.mutVars)
    (hmatch : argsMatchTys rf.ctx as (e.info.params.map (·.ty)) = true)
    (hbext : argsBorrowFromExt ctx1 as (e.info.params.map (·.borrow)) = true)
    (hpvs : rf.envP.evalArgs as = some pvs) (hws : rf.envH.evalArgsOwn as = some ws)
    (hlen1 : pvs.length = e.info.params.length) (hlen2 : ws.length = e.info.params.length)
    (hlen3 : as.length = e.info.params.length) (hext : e.extH = rf.extH) :
    let rfB : RcFrame := {
      ctx := e.baseCtx.bindParams e.info.params, envP := e.envPJp.bindAll e.info.params pvs,
      envH := e.envHJp.bindAll e.info.params ws, extH := e.extH, ghostH := rf.ghostH }
    ∀ v ∈ rfB.ctx.vars, VarInv v rfB σ.objs := by
  intro rfB v hv hvl
  have hsB := hok.2.2.2.2.1
  have hndP := hok.2.2.1
  rcases bindParams_mem_cases hsB.1 hndP hv with ⟨hv_base, hnotP⟩ | ⟨p, hp, _, rfl⟩
  · exact (varInv_bindParams_keep (pvs := pvs) (ws := ws)
      hinv hclean hok hlive ha1 hw_base hcleanS hcleanB_ps hpoB_ps hnoMut hext
      hv_base hnotP hvl) hvl
  · have hvp := varInv_bindParams_param hinv hclean hnorc hndP hlen1 hlen2 hlen3
      e.envPJp e.envHJp e.extH ha1 hmatch hbext hpvs hws hext hp hvl
    obtain ⟨pv, w, hP, hH, hvr, hrest⟩ := hvp
    refine ⟨pv, w, hP, hH, hvr, fun hvnsc => ?_⟩
    obtain ⟨bv, hwbv, hno, hps, hex, hbr⟩ := hrest hvnsc
    refine ⟨bv, hwbv, hno, hps, hex, fun hnoF hpsF hbrT hb0 => ?_⟩
    obtain ⟨_, hpar_res⟩ := hbr hnoF hpsF hbrT hb0
    have hframe_ext : ∀ r ∈ rfB.extH ++ rfB.ghostH, r ∈ frameHandles rfB := by
      intro r hr; rw [frameHandles.eq_1, List.append_assoc]; exact List.mem_append.mpr (Or.inr hr)
    have hvp_none : (if p.borrow = true then
        { id := p.id, ty := p.ty, noRc := !p.ty.needsRc, persistent := false,
          borrowed := !(!p.ty.needsRc) && true, parent? := none : RcVar }
      else
        { id := p.id, ty := p.ty, noRc := !p.ty.needsRc, persistent := false,
          owned := if ((!p.ty.needsRc) || false) = true then 0 else 1,
          excl := false, resetTok := false }).parent? = none := by
      by_cases hbr0 : p.borrow = true <;> simp [hbr0]
    rw [hvp_none] at hpar_res ⊢
    exact ⟨backed_mono_roots hframe_ext hpar_res, hpar_res⟩

private theorem parentChildBacked_bindParams_jmp {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState}
    {Jp : PResJEnv} {Jh : HJEnv} {e : JpEntry} {ρP : PValEnv} {as : List LcArg} {ctx1 : RcCtx}
    {pvs : List PVal} {ws : List Word}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hok : JpEntryOk rt rf0 σ0 Jp Jh e) (hlive : JpEntryLiveAgree e rf ρP)
    (ha1 : rf.ctx.applyArgs as (e.info.params.map (·.borrow)) = Except.ok ctx1)
    (hw_base : CtxWeakens e.baseCtx (ctx1.restrict e.info.scopeIds))
    (hcleanS : CleanVars (ctx1.restrict e.info.scopeIds))
    (hpoB_ps : ParentsOwned (e.baseCtx.bindParams e.info.params))
    (hnoMut : ∀ id ∈ baseCtxLiveIds e.baseCtx, id ∉ e.mutVars)
    (hext : e.extH = rf.extH) :
    let rfB : RcFrame := {
      ctx := e.baseCtx.bindParams e.info.params, envP := e.envPJp.bindAll e.info.params pvs,
      envH := e.envHJp.bindAll e.info.params ws, extH := e.extH, ghostH := rf.ghostH }
    ParentChildBacked rfB σ.objs := by
  intro rfB u hu hul huno hups hubr par hupar bv hHu hb0
  have hsB := hok.2.2.2.2.1
  have hndP := hok.2.2.1
  have hfrB := hok.2.2.2.1
  have hu_base : u ∈ e.baseCtx.vars ∧ ∀ p ∈ e.info.params, p.id ≠ u.id := by
    rcases bindParams_mem_cases hsB.1 hndP hu with h1 | ⟨p, _, _, rfl⟩
    · exact h1
    · exfalso; by_cases hbr : p.borrow = true <;> simp [hbr] at hupar
  have hnot_par : ∀ q ∈ e.info.params, q.id ≠ par := by
    intro q hq heq
    have hfr_q := List.all_eq_true.mp hfrB q hq
    simp only [binderFreshOwned, Bool.and_eq_true, List.all_eq_true] at hfr_q
    have h1 := hfr_q.1.1 u hu_base.1
    simp [hupar, heq] at h1
  obtain ⟨_, v_rf, _, _, hgf_rf, hrf_mem, hrf_live, _, _, hrf_no, hrf_ps, hrf_ty,
    _, _, _, _, hbr_rel, _, _, heH_u, _, _⟩ :=
    baseCtx_live_agree_rf hinv hclean hok hlive ha1 hw_base hcleanS hnoMut hu_base.1 hul
  obtain ⟨_, _, hbrf, hprf⟩ := hbr_rel hubr
  have hrf_Hu : rf.envH v_rf.id = some (v_rf.ty, Word.i64 bv) := by
    dsimp only [rfB] at hHu
    rw [bindAllH_of_not_mem e.info.params e.envHJp ws hu_base.2, ← heH_u] at hHu
    have hid_rf : v_rf.id = u.id := (RcCtx.get?_mem hgf_rf).2
    rw [hid_rf, hrf_ty]; exact hHu
  have hres := hpcb v_rf hrf_mem hrf_live (hrf_no ▸ huno) (hrf_ps ▸ hups) hbrf par
    (hprf.trans hupar) bv hrf_Hu hb0
  rcases hres with h_ext | ⟨wp, o_p, hHp, hbp, ho_p, hcf⟩
  · left; simpa [rfB, hext] using h_ext
  · right
    obtain ⟨pw, hpw_mem, hpw_id, _, _, hpw_ow, _⟩ := hpoB_ps u hu par hupar
    have hpw_base : pw ∈ e.baseCtx.vars := by
      have hndB_ps := bindParams_nodup hsB.1 e.info.params
      have hg_ps := baseCtx_vars_of_mem_nodup hndB_ps hpw_mem
      rw [hpw_id, bindParams_get?_of_not_mem hsB.1 e.info.params hnot_par] at hg_ps
      exact (RcCtx.get?_mem hg_ps).1
    have hpw_live : pw.isLive = true := by simp [RcVar.isLive, hpw_ow]
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, heH_par, _, _⟩ :=
      baseCtx_live_agree_rf hinv hclean hok hlive ha1 hw_base hcleanS hnoMut hpw_base hpw_live
    have heq_env_par : rfB.envH par = rf.envH par := by
      dsimp only [rfB]
      rw [bindAllH_of_not_mem e.info.params e.envHJp ws hnot_par, ← hpw_id, ← heH_par, hpw_id]
    exact ⟨wp, o_p, heq_env_par ▸ hHp, hbp, ho_p, hcf⟩

private theorem applyArgs_preserves_flags {ctx ctx1 : RcCtx} {as : List LcArg} {bs : List Bool}
    (hnd : (ctx.vars.map RcVar.id).Nodup) (ha : ctx.applyArgs as bs = Except.ok ctx1) :
    ∀ z, Option.map (fun v => (v.noRc, v.persistent, v.ty)) (ctx1.get? z) =
      Option.map (fun v => (v.noRc, v.persistent, v.ty)) (ctx.get? z) := by
  let R : RcCtx → RcCtx → Prop := fun c1 c2 =>
    (c1.vars.map RcVar.id).Nodup →
      (c2.vars.map RcVar.id).Nodup ∧
      ∀ z, Option.map (fun v => (v.noRc, v.persistent, v.ty)) (c2.get? z) =
        Option.map (fun v => (v.noRc, v.persistent, v.ty)) (c1.get? z)
  exact (applyArgs_rel R (fun _ h => ⟨h, fun _ => rfl⟩)
    (fun h12 h23 h => let ⟨h2, f12⟩ := h12 h; let ⟨h3, f23⟩ := h23 h2;
      ⟨h3, fun z => (f23 z).trans (f12 z)⟩)
    (fun hc h => ⟨consumeVar_nodup h hc, consumeVar_preserves_flags h hc⟩) ha hnd).2

private theorem sharedPred_jmp_flags {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState}
    {Jp : PResJEnv} {Jh : HJEnv} {e : JpEntry} {ρP : PValEnv} {as : List LcArg} {ctx1 : RcCtx}
    (hinv : RcInv rt rf σ) (hok : JpEntryOk rt rf0 σ0 Jp Jh e) (hlive : JpEntryLiveAgree e rf ρP)
    (ha1 : rf.ctx.applyArgs as (e.info.params.map (·.borrow)) = Except.ok ctx1)
    (hw_base : CtxWeakens e.baseCtx (ctx1.restrict e.info.scopeIds))
    (hnoMut : ∀ id ∈ baseCtxLiveIds e.baseCtx, id ∉ e.mutVars)
    {p : Nat × Nat} (hp : p ∈ (e.baseCtx.bindParams e.info.params).sharedPreds)
    {vb vx : RcVar} (hvb_no : vb.noRc = true)
    (hg_vb : e.baseCtx.get? p.1 = some vb) (hg_vx : e.baseCtx.get? p.2 = some vx) :
    ∃ vx_rf,
      p ∈ rf.ctx.sharedPreds ∧
      rf.ctx.get? p.2 = some vx_rf ∧
      vx_rf.noRc = vx.noRc ∧ vx_rf.persistent = vx.persistent ∧ vx_rf.ty = vx.ty ∧
      rf.envH p.2 = e.envHJp p.2 ∧
      (∀ q ∈ e.info.params, q.id ≠ p.1 ∧ q.id ≠ p.2) := by
  have hsB := hok.2.2.2.2.1
  have hfrB := hok.2.2.2.1
  have hpB : p ∈ e.baseCtx.sharedPreds := by rwa [bindParams_sharedPreds] at hp
  have hnotPQ : ∀ q ∈ e.info.params, q.id ≠ p.1 ∧ q.id ≠ p.2 := fun q hq =>
    have h0 := binderFreshOwned_sharedPreds (List.all_eq_true.mp hfrB q hq) hpB
    ⟨h0.1.symm, h0.2.symm⟩
  have hpS : p ∈ (ctx1.restrict e.info.scopeIds).sharedPreds := hw_base.2.2.2 p hpB
  have hp1 : p ∈ ctx1.sharedPreds := (List.mem_filter.mp hpS).1
  have hp_rf : p ∈ rf.ctx.sharedPreds := applyArgs_sharedPreds_sub ha1 p hp1
  have hvb_mem := (RcCtx.get?_mem hg_vb).1
  have hvx_mem := (RcCtx.get?_mem hg_vx).1
  have hvb_live : vb.isLive = true := by simp [RcVar.isLive, hvb_no]
  have hid1 : p.1 ∈ baseCtxLiveIds e.baseCtx := by
    rw [← (RcCtx.get?_mem hg_vb).2]
    exact List.mem_map.mpr ⟨vb, List.mem_filter.mpr ⟨hvb_mem, hvb_live⟩, rfl⟩
  have hnotM1 : p.1 ∉ e.mutVars := hnoMut p.1 hid1
  obtain ⟨_, heH2, hty_Jp⟩ := hlive.2 p hp_rf hid1 hnotM1
  have hty_st := (hok.2.2.2.2.2.2.1.2 p hpB hid1).2
  obtain ⟨vxS, hvxS_mem, hxid, _, _, hxno, hxps, _, _, _, _⟩ := hw_base.2.2.1 vx hvx_mem
  have hvxS_mem1 : vxS ∈ ctx1.vars := (restrict_mem_iff.mp hvxS_mem).1
  have hnd1 : (ctx1.vars.map RcVar.id).Nodup := applyArgs_nodup hinv.2.1 ha1
  have hgx1 : ctx1.get? p.2 = some vxS := by
    rw [← (RcCtx.get?_mem hg_vx).2, hxid]
    exact (RcCtx.mem_get?_iff hnd1).mpr hvxS_mem1
  have hfl := applyArgs_preserves_flags hinv.2.1 ha1 p.2
  rw [hgx1] at hfl
  have h1_ty : (rf.ctx.get? p.2).map (·.ty) = (e.baseCtx.get? p.2).map (·.ty) :=
    hty_Jp.trans hty_st
  cases hgx_rf : rf.ctx.get? p.2 with
  | none => rw [hgx_rf] at hfl; cases hfl
  | some vx_rf =>
    rw [hgx_rf] at hfl h1_ty
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hfl
    rw [hg_vx] at h1_ty
    simp only [Option.map_some, Option.some.injEq] at h1_ty
    exact ⟨vx_rf, hp_rf, rfl, hfl.1.symm.trans hxno.symm, hfl.2.1.symm.trans hxps.symm,
      h1_ty, heH2, hnotPQ⟩

private theorem count_varHandles_bv {envH : HValEnv} {v : RcVar} {bv : BitVec 64}
    (hno : v.noRc = false) (hps : v.persistent = false) (hrt : v.resetTok = false)
    (how : 0 < v.owned) (hH : envH v.id = some (v.ty, Word.i64 bv))
    (hb0 : bv &&& 1#64 = 0#64) :
    List.count bv (varHandles envH v) = v.owned := by
  have hnz : (v.owned == 0) = false := beq_false_of_ne (Nat.ne_of_gt how)
  have hbv0 : (bv &&& 1#64 == 0#64) = true := beq_iff_eq.mpr hb0
  simp [varHandles, hno, hps, hrt, hnz, hH, Word.toBV64?, Word.i64, hbv0]

private theorem sharedPredInv_bindParams_jmp {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState}
    {Jp : PResJEnv} {Jh : HJEnv} {e : JpEntry} {ρP : PValEnv} {as : List LcArg} {ctx1 : RcCtx}
    {pvs : List PVal} {ws : List Word}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hok : JpEntryOk rt rf0 σ0 Jp Jh e) (hlive : JpEntryLiveAgree e rf ρP)
    (ha1 : rf.ctx.applyArgs as (e.info.params.map (·.borrow)) = Except.ok ctx1)
    (hleaks : ctx1.checkNoLeaks e.info.scopeIds = Except.ok ())
    (hmatch : argsMatchTys rf.ctx as (e.info.params.map (·.ty)) = true)
    (hnsh : argsNoSharedTarget rf.ctx as (e.info.params.map (·.borrow)) = true)
    (hw_base : CtxWeakens e.baseCtx (ctx1.restrict e.info.scopeIds))
    (hcleanS : CleanVars (ctx1.restrict e.info.scopeIds))
    (hcleanB_ps : CleanVars (e.baseCtx.bindParams e.info.params))
    (hsbpB_ps : SharedBoolPreds (e.baseCtx.bindParams e.info.params))
    (hnoMut : ∀ id ∈ baseCtxLiveIds e.baseCtx, id ∉ e.mutVars)
    (hpvs : rf.envP.evalArgs as = some pvs) (hws : rf.envH.evalArgsOwn as = some ws)
    (hlen2 : ws.length = e.info.params.length)
    (hall_live : ∀ a ∈ as, a = LcArg.erased ∨
      ∃ z v, a = LcArg.var z ∧ rf.ctx.get? z = some v ∧ v.isLive = true)
    (hext : e.extH = rf.extH) :
    let rfB : RcFrame := {
      ctx := e.baseCtx.bindParams e.info.params, envP := e.envPJp.bindAll e.info.params pvs,
      envH := e.envHJp.bindAll e.info.params ws, extH := e.extH, ghostH := rf.ghostH }
    SharedPredInv rfB σ.objs := by
  intro rfB p hp vb vx hgb_ps hgx_ps hvb_l hvx_no hvx_ps
  have hsB := hok.2.2.2.2.1
  have hfrB := hok.2.2.2.1
  have hpB : p ∈ e.baseCtx.sharedPreds := by rwa [bindParams_sharedPreds] at hp
  have hnotPQ : ∀ q ∈ e.info.params, q.id ≠ p.1 ∧ q.id ≠ p.2 := fun q hq =>
    have h0 := binderFreshOwned_sharedPreds (List.all_eq_true.mp hfrB q hq) hpB
    ⟨h0.1.symm, h0.2.symm⟩
  have hgb_B : e.baseCtx.get? p.1 = some vb := by
    rwa [← bindParams_get?_of_not_mem hsB.1 e.info.params (fun q hq => (hnotPQ q hq).1)]
  have hgx_B : e.baseCtx.get? p.2 = some vx := by
    rwa [← bindParams_get?_of_not_mem hsB.1 e.info.params (fun q hq => (hnotPQ q hq).2)]
  obtain ⟨vb0, hgb0, hvb_no0⟩ := hsbpB_ps p hp
  rw [hgb_ps, Option.some.injEq] at hgb0; subst hgb0
  obtain ⟨vx_rf, hp_rf, hgx_rf, hvx_no_rf, hvx_ps_rf, hvx_ty_rf, heH2, _⟩ :=
    sharedPred_jmp_flags hinv hok hlive ha1 hw_base hnoMut hp hvb_no0 hgb_B hgx_B
  have hvb_mem := (RcCtx.get?_mem hgb_B).1
  obtain ⟨_, vb_rf, _, _, _, _, hvb_live_rf, _, _, _, _, _, _, _, _, _, _,
    _, heP1, _, _, _⟩ :=
    baseCtx_live_agree_rf hinv hclean hok hlive ha1 hw_base hcleanS hnoMut hvb_mem hvb_l
  have hgb_rf : rf.ctx.get? p.1 = some vb_rf := by
    rwa [← (RcCtx.get?_mem hgb_B).2]
  have heP_eq : rfB.envP p.1 = rf.envP p.1 := by
    dsimp only [rfB]
    rw [bindAllP_of_not_mem e.info.params e.envPJp pvs (fun q hq => (hnotPQ q hq).1)]
    rw [← (RcCtx.get?_mem hgb_B).2, heP1]
  have heH_eq : rfB.envH p.2 = rf.envH p.2 := by
    dsimp only [rfB]
    rw [bindAllH_of_not_mem e.info.params e.envHJp ws (fun q hq => (hnotPQ q hq).2), heH2]
  have hsp_rf := hinv.2.2.2.2 p hp_rf vb_rf vx_rf hgb_rf hgx_rf hvb_live_rf
    (hvx_no_rf.trans hvx_no) (hvx_ps_rf.trans hvx_ps)
  have hvx_own_eq : vx_rf.owned = vx.owned := by
    obtain ⟨vxS, hvxS_mem, hxid, _, _, _, _, hxow, _, _, _⟩ :=
      hw_base.2.2.1 vx (RcCtx.get?_mem hgx_B).1
    have hnd1 : (ctx1.vars.map RcVar.id).Nodup := applyArgs_nodup hinv.2.1 ha1
    have hgx1 : ctx1.get? p.2 = some vxS := by
      rw [← (RcCtx.get?_mem hgx_B).2, hxid]
      exact (RcCtx.mem_get?_iff hnd1).mpr (restrict_mem_iff.mp hvxS_mem).1
    have hpS : p ∈ (ctx1.restrict e.info.scopeIds).sharedPreds := hw_base.2.2.2 p hpB
    have hp1 : p ∈ ctx1.sharedPreds := (List.mem_filter.mp hpS).1
    obtain ⟨vx_rf', hgx_rf', how_eq'⟩ :=
      applyArgs_sharedPred_target_eq hinv.2.1 hclean hpo ha1 hnsh hp1 hgx1
    rw [hgx_rf, Option.some.injEq] at hgx_rf'; cases hgx_rf'
    exact how_eq'.trans hxow.symm
  constructor
  · intro htag
    rw [heP_eq] at htag
    obtain ⟨bv, hH_rf, hbv0, hpos_rf⟩ := hsp_rf.1 htag
    refine ⟨bv, by rw [heH_eq, hH_rf, hvx_ty_rf], hbv0, fun hpos => ?_⟩
    obtain ⟨hzero, o, ho_mem, ho_addr, ho_rc⟩ := hpos_rf (hvx_own_eq ▸ hpos)
    refine ⟨?_, o, ho_mem, ho_addr, hvx_own_eq ▸ ho_rc⟩
    have hlhe_zero :
        List.count bv (localHandlesExcept rf.ctx rf.envH p.2 ++ rf.extH ++ rf.ghostH) = 0 := by
      omega
    have hno_pers : ∀ v ∈ rf.ctx.vars, v.isLive = true → v.persistent = true →
        ∀ w, rf.envH v.id = some (v.ty, w) → w.toBV64? ≠ some bv := by
      intro vp hvp hvp_l hvp_p w hHw hwbv
      have hvp_no : vp.noRc = false := (hclean vp hvp).2.1 hvp_p |>.1
      have hvp_nsc : ¬vp.ty.isScalar = true := not_isScalar_of_check (hclean vp hvp) hvp_no
      obtain ⟨_, wv, _, hHv, _, hrest⟩ := hinv.2.2.2.1 vp hvp hvp_l
      rw [hHw, Option.some.injEq, Prod.mk.injEq] at hHv
      obtain ⟨_, hweqw⟩ := hHv
      subst hweqw
      obtain ⟨bvp, hwbvp, _, hvp_ps_imp, _, _⟩ := hrest hvp_nsc
      rw [hwbvp] at hwbv
      simp only [Word.toBV64?, Word.i64, Option.some.injEq] at hwbv
      subst hwbv
      obtain ⟨o', ho'_mem, ho'_addr, ho'_rc⟩ := hvp_ps_imp hvp_p hbv0
      have ho_eq := obj_eq_of_addr_nodup hinv.1.2 ho'_mem ho_mem (ho'_addr.trans ho_addr.symm)
      subst ho_eq
      rw [ho'_rc] at ho_rc
      have hz : (0#32 : BitVec 32).toNat = 0 := rfl
      omega
    have hle := (handlesRcSound_jmp_frame hinv hclean hpo hok hlive ha1 hleaks hmatch hnsh
      hw_base hcleanS hnoMut hpvs hws hlen2 hall_live hext).1 bv hno_pers
    have hc_rf : List.count bv (localHandles rf.ctx rf.envH) =
        vx.owned + List.count bv (localHandlesExcept rf.ctx rf.envH p.2) := by
      have hp_f := localHandles_perm_filter hinv.2.1 rf.envH vx_rf (RcCtx.get?_mem hgx_rf).1
      rw [(RcCtx.get?_mem hgx_rf).2] at hp_f
      rw [hp_f.count_eq, List.count_append]
      congr 1
      have hH_rf' : rf.envH vx_rf.id = some (vx_rf.ty, Word.i64 bv) := by
        rw [(RcCtx.get?_mem hgx_rf).2]; exact hH_rf
      have h1 := count_varHandles_bv (hvx_no_rf.trans hvx_no) (hvx_ps_rf.trans hvx_ps)
        (hclean vx_rf (RcCtx.get?_mem hgx_rf).1).2.2.2.2 (hvx_own_eq ▸ hpos) hH_rf' hbv0
      rw [h1, hvx_own_eq]
    have hndB_ps : ((e.baseCtx.bindParams e.info.params).vars.map RcVar.id).Nodup :=
      bindParams_nodup hsB.1 e.info.params
    have hc_B : List.count bv (localHandles rfB.ctx rfB.envH) =
        vx.owned + List.count bv (localHandlesExcept rfB.ctx rfB.envH p.2) := by
      have hp_f := localHandles_perm_filter hndB_ps rfB.envH vx (RcCtx.get?_mem hgx_ps).1
      rw [(RcCtx.get?_mem hgx_ps).2] at hp_f
      rw [hp_f.count_eq, List.count_append]
      congr 1
      have hH_B' : rfB.envH vx.id = some (vx.ty, Word.i64 bv) := by
        rw [(RcCtx.get?_mem hgx_ps).2, heH_eq, hH_rf, hvx_ty_rf]
      exact count_varHandles_bv hvx_no hvx_ps (hcleanB_ps vx (RcCtx.get?_mem hgx_ps).1).2.2.2.2
        hpos hH_B' hbv0
    change List.count bv (frameHandles rfB) ≤ List.count bv (frameHandles rf) at hle
    rw [frameHandles.eq_1, frameHandles.eq_1, List.count_append, List.count_append,
      List.count_append, List.count_append, hc_rf, hc_B] at hle
    simp only [rfB, hext] at hle ⊢
    rw [List.count_append, List.count_append] at hlhe_zero ⊢
    omega
  · intro htag hpos
    rw [heP_eq] at htag
    obtain ⟨bv, hH_rf, hbv0, o, ho_mem, ho_addr, hrc⟩ := hsp_rf.2 htag (hvx_own_eq ▸ hpos)
    exact ⟨bv, by rw [heH_eq, hH_rf, hvx_ty_rf], hbv0, o, ho_mem, ho_addr, hvx_own_eq ▸ hrc⟩

private theorem sharedTargetsHeap_bindParams_jmp {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState}
    {Jp : PResJEnv} {Jh : HJEnv} {e : JpEntry} {ρP : PValEnv} {as : List LcArg} {ctx1 : RcCtx}
    {pvs : List PVal} {ws : List Word}
    (hinv : RcInv rt rf σ) (hst : SharedTargetsHeap rf)
    (hok : JpEntryOk rt rf0 σ0 Jp Jh e) (hlive : JpEntryLiveAgree e rf ρP)
    (ha1 : rf.ctx.applyArgs as (e.info.params.map (·.borrow)) = Except.ok ctx1)
    (hw_base : CtxWeakens e.baseCtx (ctx1.restrict e.info.scopeIds))
    (hsbpB_ps : SharedBoolPreds (e.baseCtx.bindParams e.info.params))
    (hnoMut : ∀ id ∈ baseCtxLiveIds e.baseCtx, id ∉ e.mutVars) :
    let rfB : RcFrame := {
      ctx := e.baseCtx.bindParams e.info.params, envP := e.envPJp.bindAll e.info.params pvs,
      envH := e.envHJp.bindAll e.info.params ws, extH := e.extH, ghostH := rf.ghostH }
    SharedTargetsHeap rfB := by
  intro rfB p hp vx hgx_ps hvx_no
  have hsB := hok.2.2.2.2.1
  have hfrB := hok.2.2.2.1
  have hpB : p ∈ e.baseCtx.sharedPreds := by rwa [bindParams_sharedPreds] at hp
  have hnotPQ : ∀ q ∈ e.info.params, q.id ≠ p.1 ∧ q.id ≠ p.2 := fun q hq =>
    have h0 := binderFreshOwned_sharedPreds (List.all_eq_true.mp hfrB q hq) hpB
    ⟨h0.1.symm, h0.2.symm⟩
  obtain ⟨vb, hgb_ps, hvb_no⟩ := hsbpB_ps p hp
  have hgb_B : e.baseCtx.get? p.1 = some vb := by
    rwa [← bindParams_get?_of_not_mem hsB.1 e.info.params (fun q hq => (hnotPQ q hq).1)]
  have hgx_B : e.baseCtx.get? p.2 = some vx := by
    rwa [← bindParams_get?_of_not_mem hsB.1 e.info.params (fun q hq => (hnotPQ q hq).2)]
  obtain ⟨vx_rf, hp_rf, hgx_rf, hvx_no_rf, _, hvx_ty_rf, heH2, _⟩ :=
    sharedPred_jmp_flags hinv hok hlive ha1 hw_base hnoMut hp hvb_no hgb_B hgx_B
  obtain ⟨bv, hH_rf, hbv0⟩ := hst p hp_rf vx_rf hgx_rf (hvx_no_rf.trans hvx_no)
  refine ⟨bv, ?_, hbv0⟩
  dsimp only [rfB]
  rw [bindAllH_of_not_mem e.info.params e.envHJp ws (fun q hq => (hnotPQ q hq).2), ← heH2,
    hH_rf, hvx_ty_rf]

private theorem exclCtorHeap_bindParams_jmp {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState}
    {Jp : PResJEnv} {Jh : HJEnv} {e : JpEntry} {ρP : PValEnv} {as : List LcArg} {ctx1 : RcCtx}
    {pvs : List PVal} {ws : List Word}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hexcl : ExclCtorHeap rf)
    (hok : JpEntryOk rt rf0 σ0 Jp Jh e) (hlive : JpEntryLiveAgree e rf ρP)
    (ha1 : rf.ctx.applyArgs as (e.info.params.map (·.borrow)) = Except.ok ctx1)
    (hw_base : CtxWeakens e.baseCtx (ctx1.restrict e.info.scopeIds))
    (hcleanS : CleanVars (ctx1.restrict e.info.scopeIds))
    (hnoMut : ∀ id ∈ baseCtxLiveIds e.baseCtx, id ∉ e.mutVars) :
    let rfB : RcFrame := {
      ctx := e.baseCtx.bindParams e.info.params, envP := e.envPJp.bindAll e.info.params pvs,
      envH := e.envHJp.bindAll e.info.params ws, extH := e.extH, ghostH := rf.ghostH }
    ExclCtorHeap rfB := by
  intro rfB v hv hvl hvex huno hups cidx fs sc hP_v
  have hsB := hok.2.2.2.2.1
  have hndP := hok.2.2.1
  have hv_base : v ∈ e.baseCtx.vars ∧ ∀ p ∈ e.info.params, p.id ≠ v.id := by
    rcases bindParams_mem_cases hsB.1 hndP hv with h1 | ⟨p, _, _, rfl⟩
    · exact h1
    · exfalso; by_cases hbr : p.borrow = true <;> simp [hbr] at hvex
  obtain ⟨_, v_rf, _, _, _, hrf_mem, hrf_live, _, hid_rf, hrf_no, hrf_ps, hrf_ty,
    _, _, _, _, _, hex_rel, heP, heH, _, _⟩ :=
    baseCtx_live_agree_rf hinv hclean hok hlive ha1 hw_base hcleanS hnoMut hv_base.1 hvl
  have hP_rf : rf.envP v_rf.id = some (PVal.ctor cidx fs sc) := by
    dsimp only [rfB] at hP_v
    rw [bindAllP_of_not_mem e.info.params e.envPJp pvs hv_base.2, ← heP] at hP_v
    rwa [hid_rf]
  obtain ⟨bv, hH_rf, hbv0⟩ := hexcl v_rf hrf_mem hrf_live (hex_rel hvex).2
    (hrf_no.trans huno) (hrf_ps.trans hups) cidx fs sc hP_rf
  refine ⟨bv, ?_, hbv0⟩
  dsimp only [rfB]
  rw [bindAllH_of_not_mem e.info.params e.envHJp ws hv_base.2, ← heH, ← hid_rf, hH_rf, hrf_ty]

private theorem entryPres_bindParams_jmp {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState}
    {Jp : PResJEnv} {Jh : HJEnv} {e : JpEntry} {ρP : PValEnv} {as : List LcArg} {ctx1 : RcCtx}
    {pvs : List PVal} {ws : List Word}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hep : EntryPres rf0 σ0 rf σ)
    (hok : JpEntryOk rt rf0 σ0 Jp Jh e) (hlive : JpEntryLiveAgree e rf ρP)
    (ha1 : rf.ctx.applyArgs as (e.info.params.map (·.borrow)) = Except.ok ctx1)
    (hmatch : argsMatchTys rf.ctx as (e.info.params.map (·.ty)) = true)
    (hw_base : CtxWeakens e.baseCtx (ctx1.restrict e.info.scopeIds))
    (hcleanS : CleanVars (ctx1.restrict e.info.scopeIds))
    (hnoMut : ∀ id ∈ baseCtxLiveIds e.baseCtx, id ∉ e.mutVars)
    (hpvs : rf.envP.evalArgs as = some pvs) (hws : rf.envH.evalArgsOwn as = some ws)
    (hlen1 : pvs.length = e.info.params.length) (hlen2 : ws.length = e.info.params.length)
    (hlen3 : as.length = e.info.params.length) (hext : e.extH = rf.extH) :
    let rfB : RcFrame := {
      ctx := e.baseCtx.bindParams e.info.params, envP := e.envPJp.bindAll e.info.params pvs,
      envH := e.envHJp.bindAll e.info.params ws, extH := e.extH, ghostH := rf.ghostH }
    EntryPres rf0 σ0 rfB σ := by
  intro rfB
  refine ⟨hep.1, fun a ha hiso0 => ?_, hext.trans hep.2.2.1, hep.2.2.2⟩
  obtain ⟨hiso_rf, hobs⟩ := hep.2.1 a ha hiso0
  refine ⟨⟨fun v hv hvl hnsc w hHw => ?_, hiso_rf.2⟩, hobs⟩
  have hsB := hok.2.2.2.2.1
  have hndP := hok.2.2.1
  rcases bindParams_mem_cases hsB.1 hndP hv with ⟨hv_base, hnotP⟩ | ⟨p, hp, _, rfl⟩
  · obtain ⟨_, v_rf, _, _, _, hrf_mem, hrf_live, _, hid_rf, _, _, hrf_ty,
      _, _, _, _, _, _, _, heH, _, _⟩ :=
      baseCtx_live_agree_rf hinv hclean hok hlive ha1 hw_base hcleanS hnoMut hv_base hvl
    have hHw_rf : rf.envH v_rf.id = some (v_rf.ty, w) := by
      dsimp only [rfB] at hHw
      rw [bindAllH_of_not_mem e.info.params e.envHJp ws hnotP, ← heH] at hHw
      rw [hid_rf, hrf_ty]; exact hHw
    exact hiso_rf.1 v_rf hrf_mem hrf_live (by rwa [hrf_ty]) w hHw_rf
  · obtain ⟨arg, _, w_p, hpa_mem, _, hHvB, _, hwa⟩ :=
      bindAll_eval_at_param e.info.params as pvs ws hndP hlen1 hlen2 hlen3
        e.envPJp e.envHJp rf hmatch hpvs hws hp
    let vp : RcVar := if p.borrow = true then
        { id := p.id, ty := p.ty, noRc := !p.ty.needsRc, persistent := false,
          borrowed := !(!p.ty.needsRc) && true, parent? := none }
      else
        { id := p.id, ty := p.ty, noRc := !p.ty.needsRc, persistent := false,
          owned := if ((!p.ty.needsRc) || false) = true then 0 else 1,
          excl := false, resetTok := false }
    change (!decide (vp.ty.isScalar = true)) = true at hnsc
    change rfB.envH vp.id = some (vp.ty, w) at hHw
    have hvty : vp.ty = p.ty := by by_cases hbr : p.borrow = true <;> simp [vp, hbr]
    have hvid : vp.id = p.id := by by_cases hbr : p.borrow = true <;> simp [vp, hbr]
    rw [hvty] at hnsc hHw
    rw [hvid] at hHw
    dsimp only [rfB] at hHw
    rw [hHvB, Option.some.injEq, Prod.mk.injEq] at hHw
    obtain ⟨_, hwp⟩ := hHw
    subst hwp
    cases arg with
    | erased =>
      simp only [HValEnv.evalArgOwn, Option.some.injEq] at hwa
      subst hwa
      intro hbv
      simp only [Word.toBV64?, Word.i64, Option.some.injEq] at hbv
      subst hbv
      obtain ⟨o, _, howf, ho1, _⟩ := hiso_rf.2.2
      have ha0 := ho1 ▸ obj_addr_and1_zero howf
      revert ha0; decide
    | var z =>
      have hlive_a := applyArgs_var_live hinv.2.1 hclean ha1 (LcArg.var z)
        (snd_mem_of_mem_zip hpa_mem)
      rcases hlive_a with h0 | ⟨z', vz, heqz, hgz, hlivez⟩
      · cases h0
      · cases heqz
        have hmemz := RcCtx.get?_mem hgz
        simp only [HValEnv.evalArgOwn] at hwa
        cases hHz : rf.envH z with
        | none => rw [hHz] at hwa; cases hwa
        | some pr =>
          rw [hHz, Option.map_some, Option.some.injEq] at hwa; subst hwa
          have hm := argsMatchTys_mem hmatch hpa_mem
          simp only [hgz, Bool.and_eq_true, beq_iff_eq] at hm
          have hsc : vz.ty.isScalar = p.ty.isScalar := hm.1.1.1.1
          have hznsc : (!decide (vz.ty.isScalar = true)) = true := by
            rw [hsc]; exact hnsc
          have hvz_nsc : ¬vz.ty.isScalar = true := fun h => by simp [h] at hznsc
          obtain ⟨_, wv, _, hHv, hvr, _⟩ := hinv.2.2.2.1 vz hmemz.1 hlivez
          rw [hmemz.2, hHz, Option.some.injEq, Prod.mk.injEq] at hHv
          obtain ⟨hty_pr, hwv_eq⟩ := hHv
          subst hwv_eq
          obtain ⟨bv, hpr2⟩ := valRep_nonRc_odd hvz_nsc hvr
          have hHz' : rf.envH vz.id = some (vz.ty, Word.i64 bv) := by
            rw [hmemz.2, hHz]; exact congrArg some (Prod.ext hty_pr hpr2)
          have hne := hiso_rf.1 vz hmemz.1 hlivez hznsc (Word.i64 bv) hHz'
          rwa [hpr2]

/-- Bundled invariants across `jmp` parameter binding into `baseCtx.bindParams ps`. -/
public theorem jmp_bindParams_invs {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState}
    {Jp : PResJEnv} {Jh : HJEnv} {e : JpEntry} {ρP : PValEnv} {as : List LcArg} {ctx1 : RcCtx}
    {pvs : List PVal} {ws : List Word}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hst : SharedTargetsHeap rf) (hheap : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hep : EntryPres rf0 σ0 rf σ) (hsbv : SharedBoolVars rf.ctx) (hsbp : SharedBoolPreds rf.ctx)
    (hexcl : ExclCtorHeap rf)
    (hok : JpEntryOk rt rf0 σ0 Jp Jh e) (hlive : JpEntryLiveAgree e rf ρP)
    (ha1 : rf.ctx.applyArgs as (e.info.params.map (·.borrow)) = Except.ok ctx1)
    (hleaks : ctx1.checkNoLeaks e.info.scopeIds = Except.ok ())
    (hmatch : argsMatchTys rf.ctx as (e.info.params.map (·.ty)) = true)
    (hnoSh : argsNoSharedTarget rf.ctx as (e.info.params.map (·.borrow)) = true)
    (hbext : argsBorrowFromExt ctx1 as (e.info.params.map (·.borrow)) = true)
    (hw_base : CtxWeakens e.baseCtx (ctx1.restrict e.info.scopeIds))
    (hnoMut : ∀ id ∈ baseCtxLiveIds e.baseCtx, id ∉ e.mutVars)
    (hpvs : rf.envP.evalArgs as = some pvs) (hws : rf.envH.evalArgsOwn as = some ws)
    (hlen1 : pvs.length = e.info.params.length) (hlen2 : ws.length = e.info.params.length)
    (hlen3 : as.length = e.info.params.length)
    (hall_live : ∀ a ∈ as, a = LcArg.erased ∨
      ∃ z v, a = LcArg.var z ∧ rf.ctx.get? z = some v ∧ v.isLive = true) :
    let rfB : RcFrame := {
      ctx := e.baseCtx.bindParams e.info.params, envP := e.envPJp.bindAll e.info.params pvs,
      envH := e.envHJp.bindAll e.info.params ws, extH := e.extH, ghostH := rf.ghostH }
    RcInv rt rfB σ ∧ CleanVars rfB.ctx ∧ ParentsOwned rfB.ctx ∧ NoRcCorrect rfB.ctx ∧
    ParentChildBacked rfB σ.objs ∧ SharedTargetsHeap rfB ∧
    HandlesInHeap (rfB.extH ++ rfB.ghostH) σ.objs ∧ EntryPres rf0 σ0 rfB σ ∧
    SharedBoolVars rfB.ctx ∧ SharedBoolPreds rfB.ctx ∧ ExclCtorHeap rfB := by
  intro rfB
  have hext : e.extH = rf.extH := hok.2.1.trans hep.2.2.1.symm
  obtain ⟨_, hcleanS, _, _, _, _, hcleanB_ps, hpoB_ps, hnorcB_ps, hsbvB_ps, hsbpB_ps⟩ :=
    jmp_ctxS_invs hinv hclean hpo hnorc hsbv hsbp hok ha1 hleaks hw_base
  have hndB_ps := bindParams_nodup hok.2.2.2.2.1.1 e.info.params
  have hrsB := (handlesRcSound_jmp_frame hinv hclean hpo hok hlive ha1 hleaks hmatch hnoSh
    hw_base hcleanS hnoMut hpvs hws hlen2 hall_live hext).2
  have hvvB := @varInv_bindParams_jmp rt rf0 rf σ0 σ Jp Jh e ρP as ctx1 pvs ws
    hinv hclean hnorc hok hlive ha1 hw_base hcleanS hcleanB_ps hpoB_ps hnoMut
    hmatch hbext hpvs hws hlen1 hlen2 hlen3 hext
  have hpcbB := @parentChildBacked_bindParams_jmp rt rf0 rf σ0 σ Jp Jh e ρP as ctx1 pvs ws
    hinv hclean hpcb hok hlive ha1 hw_base hcleanS hpoB_ps hnoMut hext
  have hspB := @sharedPredInv_bindParams_jmp rt rf0 rf σ0 σ Jp Jh e ρP as ctx1 pvs ws
    hinv hclean hpo hok hlive ha1 hleaks hmatch hnoSh hw_base hcleanS hcleanB_ps hsbpB_ps
    hnoMut hpvs hws hlen2 hall_live hext
  have hstB := @sharedTargetsHeap_bindParams_jmp rt rf0 rf σ0 σ Jp Jh e ρP as ctx1 pvs ws
    hinv hst hok hlive ha1 hw_base hsbpB_ps hnoMut
  have hexclB := @exclCtorHeap_bindParams_jmp rt rf0 rf σ0 σ Jp Jh e ρP as ctx1 pvs ws
    hinv hclean hexcl hok hlive ha1 hw_base hcleanS hnoMut
  have hepB := @entryPres_bindParams_jmp rt rf0 rf σ0 σ Jp Jh e ρP as ctx1 pvs ws
    hinv hclean hep hok hlive ha1 hmatch hw_base hcleanS hnoMut hpvs hws hlen1 hlen2 hlen3 hext
  have hheapB : HandlesInHeap (rfB.extH ++ rfB.ghostH) σ.objs := by
    simpa [rfB, hext] using hheap
  exact ⟨⟨hinv.1, hndB_ps, hrsB, hvvB, hspB⟩, hcleanB_ps, hpoB_ps, hnorcB_ps, hpcbB, hstB,
    hheapB, hepB, hsbvB_ps, hsbpB_ps, hexclB⟩

end JmpInvs

section JpConseq

/-- Postcondition monotonicity for `PRValWp`. -/
public theorem PRValWp_mono {env : RcModEnv} {Δr : PResEnv} {ρ : PValEnv}
    {ty : LcTy} {v : LcVal} {rem wr rcr : Nat} {K₁ K₂ : PResPost} {X : PResXPost}
    (hK : ∀ r rem' wr' rcr', K₁ r rem' wr' rcr' → K₂ r rem' wr' rcr') :
    PRValWp env Δr ρ ty v rem wr rcr K₁ X → PRValWp env Δr ρ ty v rem wr rcr K₂ X := by
  intro h
  unfold PRValWp at h ⊢
  cases v with
  | lit l =>
    cases l with
    | nat n => exact ⟨h.1, hK _ _ _ _ h.2⟩
    | str s => cases h
    | scalar n => exact hK _ _ _ _ h
  | erased => exact hK _ _ _ _ h
  | ctor ci as =>
    dsimp only at h ⊢
    cases he : ρ.evalArgs as with
    | none => simp only [he] at h
    | some vs =>
      simp only [he] at h ⊢
      cases hc : PVal.mkCtor ty ci vs with
      | none => simp only [hc] at h
      | some r =>
        simp only [hc] at h ⊢
        by_cases hsc : ci.isScalar = true
        · simp only [hsc, ↓reduceIte] at h ⊢; exact hK _ _ _ _ h
        · simp only [hsc, Bool.false_eq_true, ↓reduceIte] at h ⊢
          exact ⟨h.1, h.2.1, hK _ _ _ _ h.2.2⟩
  | oproj i x =>
    dsimp only at h ⊢
    cases he : (ρ x).bind fun v => v.getObj? i with
    | none => simp only [he] at h
    | some r => simp only [he] at h ⊢; exact hK _ _ _ _ h
  | uproj i x =>
    dsimp only at h ⊢
    cases he : (ρ x).bind fun v => v.getUsize? i with
    | none => simp only [he] at h
    | some r => simp only [he] at h ⊢; exact hK _ _ _ _ h
  | sproj n off x =>
    dsimp only at h ⊢
    cases he : (ρ x).bind fun v => v.getScalar? n off ty with
    | none => simp only [he] at h
    | some r => simp only [he] at h ⊢; exact hK _ _ _ _ h
  | box t x =>
    dsimp only at h ⊢
    cases he : (ρ x).bind (PVal.box t) with
    | none => simp only [he] at h
    | some r =>
      simp only [he] at h ⊢
      by_cases ht : (t == LcTy.uint64 || t == LcTy.usize || t == LcTy.float) = true
      · simp only [ht, ↓reduceIte] at h ⊢; exact ⟨h.1, h.2.1, hK _ _ _ _ h.2.2⟩
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact hK _ _ _ _ h
  | unbox x =>
    dsimp only at h ⊢
    cases hx : ρ x with
    | none => simp only [hx, Option.bind_none] at h
    | some pv =>
      simp only [hx, Option.bind_some] at h ⊢
      cases hu : PVal.unbox ty pv with
      | none => simp only [hu] at h
      | some r => simp only [hu] at h ⊢; exact ⟨h.1, hK _ _ _ _ h.2⟩
  | isShared x =>
    dsimp only at h ⊢
    cases hx : ρ x with
    | none => simp only [hx] at h
    | some pv => simp only [hx] at h ⊢; exact ⟨h.1, fun b => hK _ _ _ _ (h.2 b)⟩
  | reset x n => cases h
  | reuse x n y vs => cases h
  | pap fn as => cases h
  | ap fn as => cases h
  | fap f as =>
    dsimp only at h ⊢
    cases he : ρ.evalArgs as with
    | none => simp only [he] at h
    | some vs =>
      simp only [he] at h ⊢
      by_cases hoob : (f == "outOfBounds._redArg") = true
      · simp only [hoob, ↓reduceIte] at h ⊢; exact h
      · simp only [hoob, Bool.false_eq_true, ↓reduceIte] at h ⊢
        by_cases hd : (env.decls.find? (fun d => d.1 == f)).isSome = true
        · simp only [hd, ↓reduceIte] at h ⊢
          obtain ⟨P, E, hΔ, hP, hX⟩ := h
          exact ⟨P, E, hΔ, fun r rem' wr' rcr' hp => hK _ _ _ _ (hP r rem' wr' rcr' hp), hX⟩
        · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
          refine ⟨h.1, ?_⟩
          cases hp : primP f vs with
          | none => simp only [hp] at h; exact h.2
          | some r => simp only [hp] at h ⊢; exact ⟨h.2.1, hK _ _ _ _ h.2.2⟩

/-- `PRWp` depends only on entries of `J` that are bound in `jps` when `checkCode` succeeds. -/
public theorem PRWp_jp_congr_of_check {m : LcModule} {env : RcModEnv} {retTy : LcTy}
    {Δr : PResEnv} {Q : PResPost} {X : PResXPost} (c : LcCode) :
    ∀ (jps : List RcJpInfo) (ctx : RcCtx) (J₁ J₂ : PResJEnv),
      (∀ id, (∃ info ∈ jps, info.id = id) → J₁ id = J₂ id) →
      ∀ (jumps : List (Nat × RcCtx)),
        checkCode env retTy jps ctx c = Except.ok jumps →
        ∀ (ρ : PValEnv) (rem wr rcr : Nat),
          PRWp m env retTy Δr jps ctx J₁ ρ rem wr rcr Q X c →
          PRWp m env retTy Δr jps ctx J₂ ρ rem wr rcr Q X c := by
  let P1 : LcCode → Prop := fun code =>
    ∀ (jps : List RcJpInfo) (ctx : RcCtx) (J₁ J₂ : PResJEnv),
      (∀ id, (∃ info ∈ jps, info.id = id) → J₁ id = J₂ id) →
      ∀ (jumps : List (Nat × RcCtx)),
        checkCode env retTy jps ctx code = Except.ok jumps →
        ∀ (ρ : PValEnv) (rem wr rcr : Nat),
          PRWp m env retTy Δr jps ctx J₁ ρ rem wr rcr Q X code →
          PRWp m env retTy Δr jps ctx J₂ ρ rem wr rcr Q X code
  let P2 : List (LcPat × LcCode) → Prop := fun alts =>
    ∀ (jps : List RcJpInfo) (ctx : RcCtx) (J₁ J₂ : PResJEnv),
      (∀ id, (∃ info ∈ jps, info.id = id) → J₁ id = J₂ id) →
      ∀ (scru : Nat) (target? : Option Nat) (jumps : List (Nat × RcCtx)),
        checkAlts env retTy jps ctx scru target? alts = Except.ok jumps →
        ∀ (ρ : PValEnv) (rem wr rcr : Nat),
          (PRWpDfltAlts m env retTy Δr jps ctx J₁ ρ rem wr rcr Q X alts →
            PRWpDfltAlts m env retTy Δr jps ctx J₂ ρ rem wr rcr Q X alts) ∧
          ∀ (pv : PVal) (tag : Nat) (F₁ F₂ : Prop),
            (F₁ → F₂) →
            PRWpCtorAlts m env retTy Δr jps ctx scru target? pv J₁ ρ tag rem wr rcr Q X alts F₁ →
            PRWpCtorAlts m env retTy Δr jps ctx scru target? pv J₂ ρ tag rem wr rcr Q X alts F₂
  let P3 : (LcPat × LcCode) → Prop := fun hd => P1 hd.2
  refine (@LcCode.rec P1 P2 P3 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ c)
  · intro x ty v k ih jps ctx J₁ J₂ hJ jumps hchk ρ rem wr rcr hpr
    rw [checkCode.eq_1] at hchk
    obtain ⟨ctx', hcv, hck⟩ := except_bind_ok hchk
    rw [PRWp.eq_1, hcv] at hpr ⊢
    exact PRValWp_mono (fun r rem' wr' rcr' hk => ih jps ctx' J₁ J₂ hJ jumps hck _ _ _ _ hk) hpr
  · intro j ps body k ih_body ih_k jps ctx J₁ J₂ hJ jumps hchk ρ rem wr rcr hpr
    rw [checkCode.eq_2] at hchk
    dsimp only at hchk
    obtain ⟨jumpsK, hckK, hrest⟩ := except_bind_ok hchk
    obtain ⟨optC, hmg, hrest2⟩ := except_bind_ok hrest
    let baseCtx := optC.getD ctx
    have hckB :
        ∃ jumpsB, checkCode env retTy jps (baseCtx.bindParams ps) body = Except.ok jumpsB := by
      cases optC with
      | none =>
        simp only [baseCtx, Option.getD_none]
        simp only [bind, Except.bind, pure, Except.pure] at hrest2
        obtain ⟨jumpsB, hB, _⟩ := except_bind_ok hrest2
        exact ⟨jumpsB, hB⟩
      | some c' =>
        simp only [baseCtx, Option.getD_some]
        simp only [bind, Except.bind, pure, Except.pure] at hrest2
        obtain ⟨jumpsB, hB, _⟩ := except_bind_ok hrest2
        exact ⟨jumpsB, hB⟩
    obtain ⟨jumpsB, hB⟩ := hckB
    rw [PRWp.eq_2] at hpr ⊢
    dsimp only at hpr ⊢
    have hbase_eq : jpBaseCtx env retTy jps ctx j ps k = baseCtx :=
      jpBaseCtx_eq_of_check hckK hmg
    rw [hbase_eq] at hpr ⊢
    intro Jj hJj
    have hJj1 : ∀ (as : List PVal) (rem' wr' rcr' : Nat),
        as.length = ps.length →
        PRWp m env retTy Δr jps (baseCtx.bindParams ps) (J₁.set j Jj) (ρ.bindAll ps as)
          rem' wr' rcr' Q X body →
        Jj as rem' wr' rcr' := by
      intro as rem' wr' rcr' hlen hbody
      refine hJj as rem' wr' rcr' hlen ?_
      refine ih_body jps (baseCtx.bindParams ps) (J₁.set j Jj) (J₂.set j Jj)
        (fun id hid => ?_) jumpsB hB _ _ _ _ hbody
      funext a r' w' rc'
      by_cases hjd : id = j
      · subst hjd; simp [PResJEnv.set]
      · simp only [PResJEnv.set, hjd, ↓reduceIte]
        have h1 := hJ id hid
        exact congrFun (congrFun (congrFun (congrFun h1 a) r') w') rc'
    refine ih_k ({ id := j, params := ps, scopeIds := List.map (fun x => x.id) ctx.vars } :: jps)
      ctx (J₁.set j Jj) (J₂.set j Jj) (fun id hid => ?_) jumpsK hckK ρ rem wr rcr (hpr Jj hJj1)
    rcases hid with ⟨info, hinfo, rfl⟩
    funext a r' w' rc'
    rcases List.mem_cons.mp hinfo with rfl | hmem
    · simp [PResJEnv.set]
    · by_cases hjd : info.id = j
      · rw [hjd]; simp [PResJEnv.set]
      · simp only [PResJEnv.set, hjd, ↓reduceIte]
        have h1 := hJ info.id ⟨info, hmem, rfl⟩
        exact congrFun (congrFun (congrFun (congrFun h1 a) r') w') rc'
  · intro j args jps ctx J₁ J₂ hJ jumps hchk ρ rem wr rcr hpr
    rw [checkCode.eq_3] at hchk
    cases hfd : jps.find? (fun x => x.id == j) with
    | none => rw [hfd] at hchk; cases hchk
    | some info =>
      have hmem := List.mem_of_find?_eq_some hfd
      have hid : info.id = j :=
        beq_iff_eq.mp (@List.find?_some _ (fun x : RcJpInfo => x.id == j) _ _ hfd)
      have hJeq := hJ j ⟨info, hmem, hid⟩
      rw [PRWp.eq_3] at hpr ⊢
      cases hev : ρ.evalArgs args with
      | none => simp only [hev] at hpr
      | some vs => simp only [hev] at hpr ⊢; rwa [← hJeq]
  · intro x alts ih_alts jps ctx J₁ J₂ hJ jumps hchk ρ rem wr rcr hpr
    rw [checkCode.eq_4] at hchk
    obtain ⟨_, _, halts⟩ := except_bind_ok hchk
    dsimp only at halts
    rw [PRWp.eq_4] at hpr ⊢
    cases hgx : ctx.get? x with
    | none => simp only [hgx] at hpr
    | some vx =>
      cases hpx : ρ x with
      | none => simp only [hgx, hpx, Option.bind_none] at hpr
      | some pv =>
        cases htag : pv.tag? with
        | none => simp only [hgx, hpx, htag, Option.bind_some] at hpr
        | some tag =>
          simp only [hgx, hpx, htag, Option.bind_some] at hpr ⊢
          obtain ⟨hdflt, hctor⟩ := ih_alts jps ctx J₁ J₂ hJ x
            (Option.map Prod.snd (List.find? (fun p => p.1 == x) ctx.sharedPreds))
            jumps halts ρ rem wr rcr
          exact ⟨hpr.1, hctor pv tag _ _ hdflt hpr.2⟩
  · intro x jps ctx J₁ J₂ _ _ _ ρ rem wr rcr hpr; exact hpr
  · intro jps ctx J₁ J₂ _ _ _ ρ rem wr rcr hpr; exact hpr
  · intro x i y k ih jps ctx J₁ J₂ hJ jumps hchk ρ rem wr rcr hpr
    rw [checkCode.eq_7] at hchk
    obtain ⟨_, _, hrest⟩ := except_bind_ok hchk
    obtain ⟨ctx1, hc1, hk⟩ := except_bind_ok hrest
    rw [PRWp.eq_7, hc1] at hpr ⊢
    cases hrx : ρ x with
    | none => simp only [hrx] at hpr
    | some xv =>
      cases hry : ρ.evalArg y with
      | none => simp only [hrx, hry] at hpr
      | some yv =>
        simp only [hrx, hry] at hpr ⊢
        cases hso : xv.setObj i yv with
        | none => simp only [hso] at hpr
        | some xv' =>
          simp only [hso] at hpr ⊢
          exact ih jps ctx1 J₁ J₂ hJ jumps hk _ _ _ _ hpr
  · intro x i y k ih jps ctx J₁ J₂ hJ jumps hchk ρ rem wr rcr hpr
    rw [checkCode.eq_8] at hchk
    obtain ⟨_, _, hrest⟩ := except_bind_ok hchk
    obtain ⟨_, _, hk⟩ := except_bind_ok hrest
    rw [PRWp.eq_8] at hpr ⊢
    cases hrx : ρ x with
    | none => simp only [hrx] at hpr
    | some xv =>
      cases hry : ρ y with
      | none => simp only [hrx, hry] at hpr
      | some yv =>
        simp only [hrx, hry] at hpr ⊢
        cases hsu : xv.setUsize i yv with
        | none => simp only [hsu] at hpr
        | some xv' =>
          simp only [hsu] at hpr ⊢
          exact ih jps ctx J₁ J₂ hJ jumps hk _ _ _ _ hpr
  · intro x n off y ty k ih jps ctx J₁ J₂ hJ jumps hchk ρ rem wr rcr hpr
    rw [checkCode.eq_9] at hchk
    obtain ⟨_, _, hrest⟩ := except_bind_ok hchk
    obtain ⟨_, _, hk⟩ := except_bind_ok hrest
    rw [PRWp.eq_9] at hpr ⊢
    cases hrx : ρ x with
    | none => simp only [hrx] at hpr
    | some xv =>
      cases hry : ρ y with
      | none => simp only [hrx, hry] at hpr
      | some yv =>
        simp only [hrx, hry] at hpr ⊢
        cases hss : xv.setScalar n off ty yv with
        | none => simp only [hss] at hpr
        | some xv' =>
          simp only [hss] at hpr ⊢
          exact ih jps ctx J₁ J₂ hJ jumps hk _ _ _ _ hpr
  · intro x cidx k ih jps ctx J₁ J₂ hJ jumps hchk ρ rem wr rcr hpr
    rw [checkCode.eq_10] at hchk
    obtain ⟨_, _, hk⟩ := except_bind_ok hchk
    rw [PRWp.eq_10] at hpr ⊢
    cases hst : (ρ x).bind (fun v => v.setTag cidx) with
    | none => simp only [hst] at hpr
    | some xv' =>
      simp only [hst] at hpr ⊢
      exact ih jps ctx J₁ J₂ hJ jumps hk _ _ _ _ hpr
  · intro x n chk k ih jps ctx J₁ J₂ hJ jumps hchk ρ rem wr rcr hpr
    rw [checkCode.eq_11] at hchk
    rw [PRWp.eq_11] at hpr ⊢
    cases hgx : ctx.get? x with
    | none => simp only [hgx] at hpr
    | some v =>
      simp only [hgx] at hchk hpr ⊢
      have hlive : (!v.isLive) = false := by
        by_cases hnl : (!v.isLive) = true
        · simp only [hnl, ↓reduceIte] at hchk
          change Except.error _ = Except.ok jumps at hchk
          cases hchk
        · exact Bool.eq_false_iff.mpr hnl
      simp only [hlive, Bool.false_eq_true, ↓reduceIte] at hchk
      by_cases hskip : (v.noRc || v.persistent || n == 0) = true
      · simp only [hskip, ↓reduceIte] at hchk hpr ⊢
        exact ih jps ctx J₁ J₂ hJ jumps hchk ρ rem wr rcr hpr
      · simp only [hskip, Bool.false_eq_true, ↓reduceIte] at hchk hpr ⊢
        exact ⟨hpr.1, ih jps (ctx.put _) J₁ J₂ hJ jumps hchk ρ rem wr (rcr - n) hpr.2⟩
  · intro x n chk k ih jps ctx J₁ J₂ hJ jumps hchk ρ rem wr rcr hpr
    rw [checkCode.eq_12] at hchk
    obtain ⟨ctx1, hc1, hk⟩ := except_bind_ok hchk
    rw [PRWp.eq_12, hc1] at hpr ⊢
    exact ⟨hpr.1, ih jps ctx1 J₁ J₂ hJ jumps hk ρ rem wr rcr hpr.2⟩
  · intro x k ih jps ctx J₁ J₂ hJ jumps hchk ρ rem wr rcr hpr
    rw [checkCode.eq_13] at hchk
    obtain ⟨_, _, hrest⟩ := except_bind_ok hchk
    obtain ⟨ctx1, hc1, hk⟩ := except_bind_ok hrest
    rw [PRWp.eq_13, hc1] at hpr ⊢
    exact ih jps ctx1 J₁ J₂ hJ jumps hk ρ rem wr rcr hpr
  · intro jps ctx J₁ J₂ hJ scru target? jumps hchk ρ rem wr rcr
    refine ⟨id, fun pv tag F₁ F₂ hF hpr => ?_⟩
    rw [PRWpCtorAlts.eq_1] at hpr ⊢; exact hF hpr
  · intro hd tail ih_hd ih_tail jps ctx J₁ J₂ hJ scru target? jumps hchk ρ rem wr rcr
    rcases hd with ⟨pat, b⟩
    dsimp only [P3, P1] at ih_hd
    cases pat with
    | dflt =>
      rw [checkAlts.eq_4 env retTy jps ctx scru b tail target? (fun tgt name _ h => by cases h)]
        at hchk
      dsimp only at hchk
      obtain ⟨j1, hck1, hrest⟩ := except_bind_ok hchk
      obtain ⟨j2, hck2, _⟩ := except_bind_ok hrest
      have htl := ih_tail jps ctx J₁ J₂ hJ scru target? j2 hck2 ρ rem wr rcr
      refine ⟨fun hd => ?_, fun pv tag F₁ F₂ hF hpr => ?_⟩
      · rw [PRWpDfltAlts.eq_2] at hd ⊢
        exact ih_hd jps ctx J₁ J₂ hJ j1 hck1 ρ rem wr rcr hd
      · rw [PRWpCtorAlts.eq_4] at hpr ⊢
        exact htl.2 pv tag F₁ F₂ hF hpr
    | ctor ci cname =>
      by_cases hhit : ∃ tgt, target? = some tgt ∧ ci = 0
      · obtain ⟨tgt, rfl, rfl⟩ := hhit
        rw [checkAlts.eq_2 env retTy jps ctx scru b tail 0 cname tgt cname rfl] at hchk
        dsimp only at hchk
        obtain ⟨j1, hck1, hrest⟩ := except_bind_ok hchk
        obtain ⟨j2, hck2, _⟩ := except_bind_ok hrest
        have htl := ih_tail jps ctx J₁ J₂ hJ scru (some tgt) j2 hck2 ρ rem wr rcr
        refine ⟨fun hd => ?_, fun pv tag F₁ F₂ hF hpr => ?_⟩
        · rw [PRWpDfltAlts.eq_3] at hd ⊢; exact htl.1 hd
        · rw [PRWpCtorAlts.eq_2] at hpr ⊢
          by_cases h0t : 0 = tag
          · simp only [h0t, ↓reduceIte] at hpr ⊢
            exact ⟨hpr.1, ih_hd jps _ J₁ J₂ hJ j1 hck1 ρ rem wr rcr hpr.2⟩
          · simp only [h0t, ↓reduceIte] at hpr ⊢
            exact htl.2 pv tag F₁ F₂ hF hpr
      · have hno :
            ∀ tgt name, target? = some tgt → LcPat.ctor ci cname = LcPat.ctor 0 name → False := by
          intro tgt name ht hc; cases hc; exact hhit ⟨tgt, ht, rfl⟩
        have hno2 : ∀ tgt, target? = some tgt → ci = 0 → False := fun tgt ht h0 =>
          hhit ⟨tgt, ht, h0⟩
        rw [checkAlts.eq_3 env retTy jps ctx scru b tail ci cname target? hno] at hchk
        dsimp only at hchk
        obtain ⟨j1, hck1, hrest⟩ := except_bind_ok hchk
        obtain ⟨j2, hck2, _⟩ := except_bind_ok hrest
        have htl := ih_tail jps ctx J₁ J₂ hJ scru target? j2 hck2 ρ rem wr rcr
        refine ⟨fun hd => ?_, fun pv tag F₁ F₂ hF hpr => ?_⟩
        · rw [PRWpDfltAlts.eq_3] at hd ⊢; exact htl.1 hd
        · rw [PRWpCtorAlts.eq_3 m env retTy Δr jps ctx scru target? pv J₁ ρ tag rem wr rcr Q X F₁
              ci cname b tail hno2] at hpr
          rw [PRWpCtorAlts.eq_3 m env retTy Δr jps ctx scru target? pv J₂ ρ tag rem wr rcr Q X F₂
              ci cname b tail hno2]
          by_cases hct : ci = tag
          · simp only [hct, ↓reduceIte] at hpr ⊢
            exact ⟨hpr.1, ih_hd jps _ J₁ J₂ hJ j1 hck1 ρ rem wr rcr hpr.2⟩
          · simp only [hct, ↓reduceIte] at hpr ⊢
            exact htl.2 pv tag F₁ F₂ hF hpr
  · intro _ snd ih; exact ih

end JpConseq

section JpSupport

/-- Updating `Jp` at `j` preserves `JpsOk` when `j` is not in `jpsOk`. -/
public theorem jpsOk_set_jp_of_ne {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 : HState}
    {Jp : PResJEnv} {Jh : HJEnv} {jpsOk : List JpEntry} {ρP : PValEnv}
    {jumps : List (Nat × RcCtx)} {j : Nat} {Jp_j : List PVal → Nat → Nat → Nat → Prop}
    (hne : ∀ e ∈ jpsOk, e.info.id ≠ j)
    (h : JpsOk rt rf0 σ0 Jp Jh jpsOk rf ρP jumps) :
    JpsOk rt rf0 σ0 (Jp.set j Jp_j) Jh jpsOk rf ρP jumps := by
  intro e he
  obtain ⟨hok, hlive, hjmp⟩ := h e he
  refine ⟨⟨hok.1, hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1, hok.2.2.2.2.2.1,
    hok.2.2.2.2.2.2.1, fun pvs rem wr rcr hJp hpb => ?_⟩, hlive, hjmp⟩
  have hne_e : e.info.id ≠ j := hne e he
  simp only [PResJEnv.set, hne_e, ↓reduceIte] at hJp
  exact hok.2.2.2.2.2.2.2 pvs rem wr rcr hJp hpb

/-- Updating `Jh` at `j` preserves `JpsOk` when `j` is not in `jpsOk`. -/
public theorem jpsOk_set_jh_of_ne {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 : HState}
    {Jp : PResJEnv} {Jh : HJEnv} {jpsOk : List JpEntry} {ρP : PValEnv}
    {jumps : List (Nat × RcCtx)} {j : Nat} {Jh_j : List Word → HState → Prop}
    (hne : ∀ e ∈ jpsOk, e.info.id ≠ j)
    (h : JpsOk rt rf0 σ0 Jp Jh jpsOk rf ρP jumps) :
    JpsOk rt rf0 σ0 Jp (Jh.set j Jh_j) jpsOk rf ρP jumps := by
  intro e he
  obtain ⟨hok, hlive, hjmp⟩ := h e he
  refine ⟨⟨hok.1, hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1, hok.2.2.2.2.2.1,
    hok.2.2.2.2.2.2.1, fun pvs rem wr rcr hJp hpb => ?_⟩, hlive, hjmp⟩
  obtain ⟨hlen, hbody⟩ := hok.2.2.2.2.2.2.2 pvs rem wr rcr hJp hpb
  refine ⟨hlen, fun ws σ' ghostH' hpm hinv hcl hpo hnr hpcb hst hhh hep hsbv hsbp hex hrs hav => ?_⟩
  have hne_e : e.info.id ≠ j := hne e he
  simp only [HJEnv.set, hne_e, ↓reduceIte]
  exact hbody ws σ' ghostH' hpm hinv hcl hpo hnr hpcb hst hhh hep hsbv hsbp hex hrs hav

private theorem bindAllP_eq_of_mem {ps : List LcParam} {pvs : List PVal}
    {ρ₁ ρ₂ : PValEnv} {p : LcParam}
    (hnd : (ps.map (·.id)).Nodup) (hlen : pvs.length = ps.length) (hp : p ∈ ps) :
    (ρ₁.bindAll ps pvs) p.id = (ρ₂.bindAll ps pvs) p.id := by
  induction ps generalizing pvs ρ₁ ρ₂ with
  | nil => cases hp
  | cons p0 rest ih =>
    cases pvs with
    | nil => cases hlen
    | cons pv restV =>
      rw [PValEnv.bindAll.eq_1, PValEnv.bindAll.eq_1]
      have hnd' := List.nodup_cons.mp hnd
      have hlen' : restV.length = rest.length := by simpa using hlen
      rcases List.mem_cons.mp hp with hp0 | hp'
      · subst hp0
        have hnotR : ∀ q ∈ rest, q.id ≠ p.id := fun q hq heq =>
          hnd'.1 (List.mem_map.mpr ⟨q, hq, heq⟩)
        rw [bindAllP_of_not_mem rest _ restV hnotR, bindAllP_of_not_mem rest _ restV hnotR]
        simp [PValEnv.set]
      · exact ih hnd'.2 hlen' hp'

/-- `ShadowOk []` holds across `baseCtx.bindParams ps` if live `baseCtx` vars are initialized. -/
public theorem shadowOk_bindParams_empty {baseCtx ctx : RcCtx} {ps : List LcParam}
    {sm : List (Nat × Nat × List Bool)} {ρP envP : PValEnv} {pvs : List PVal}
    (hsB : CtxStaticInv baseCtx) (hndP : (ps.map (·.id)).Nodup) (hlen : pvs.length = ps.length)
    (hall : (baseCtx.vars.all (fun v => !v.isLive || isVarScalarInit sm v.id)) = true)
    (hsh : ShadowOk sm ctx ρP envP)
    (hagree : ∀ v ∈ baseCtx.vars, v.isLive = true →
      ∃ v_rf ∈ ctx.vars, v_rf.id = v.id ∧ v_rf.isLive = true) :
    ShadowOk [] (baseCtx.bindParams ps) (ρP.bindAll ps pvs) (envP.bindAll ps pvs) := by
  intro v hv hvl
  simp only [isVarScalarInit, List.all_nil, ↓reduceIte]
  rcases bindParams_mem_cases hsB.1 hndP hv with ⟨hv_base, hnotP⟩ | ⟨p, hp, hid, _⟩
  · rw [bindAllP_of_not_mem ps ρP pvs hnotP, bindAllP_of_not_mem ps envP pvs hnotP]
    obtain ⟨v_rf, hrf_mem, hvid, hrf_l⟩ := hagree v hv_base hvl
    have hinit : isVarScalarInit sm v.id = true := by
      have h1 := List.all_eq_true.mp hall v hv_base
      simpa [hvl] using h1
    have hsh_v := hsh v_rf hrf_mem hrf_l
    rw [hvid] at hsh_v
    simp only [hinit, ↓reduceIte] at hsh_v
    exact hsh_v
  · rw [hid]
    exact bindAllP_eq_of_mem hndP hlen hp

/-- Evaluating `as` in `PValEnv` succeeds when all live var arguments are bound. -/
public theorem evalArgs_some_live {ctx : RcCtx} {as : List LcArg} {ρ : PValEnv}
    (hall : ∀ a ∈ as, a = LcArg.erased ∨
      ∃ z v, a = LcArg.var z ∧ ctx.get? z = some v ∧ v.isLive = true)
    (hvar : ∀ v ∈ ctx.vars, v.isLive = true → ∃ pv, ρ v.id = some pv) :
    ∃ vs, ρ.evalArgs as = some vs ∧ vs.length = as.length := by
  induction as with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons a rest ih =>
    have ha := hall a List.mem_cons_self
    obtain ⟨vs, hvs, hlen⟩ := ih (fun b hb => hall b (List.mem_cons_of_mem _ hb))
    rcases ha with rfl | ⟨z, v, rfl, hgz, hvl⟩
    · refine ⟨PVal.erased :: vs, ?_, by simp [hlen]⟩
      simp [PValEnv.evalArgs, PValEnv.evalArg, hvs]
    · have hmem := RcCtx.get?_mem hgz
      obtain ⟨pv, hpv⟩ := hvar v hmem.1 hvl
      rw [hmem.2] at hpv
      refine ⟨pv :: vs, ?_, by simp [hlen]⟩
      simp [PValEnv.evalArgs, PValEnv.evalArg, hpv, hvs]

/-- Evaluating `as` in `HValEnv` succeeds under `RcInv` when all args are live. -/
public theorem evalArgsOwn_some {rt : BitVec 64} {rf : RcFrame} {σ : HState} {as : List LcArg}
    (hinv : RcInv rt rf σ)
    (hall : ∀ a ∈ as, a = LcArg.erased ∨
      ∃ z v, a = LcArg.var z ∧ rf.ctx.get? z = some v ∧ v.isLive = true) :
    ∃ ws, rf.envH.evalArgsOwn as = some ws ∧ ws.length = as.length := by
  induction as with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons a rest ih =>
    have ha := hall a List.mem_cons_self
    obtain ⟨ws, hws, hlen⟩ := ih (fun b hb => hall b (List.mem_cons_of_mem _ hb))
    rcases ha with rfl | ⟨z, v, rfl, hgz, hvl⟩
    · refine ⟨Word.i64 1#64 :: ws, ?_, by simp [hlen]⟩
      simp [HValEnv.evalArgsOwn, HValEnv.evalArgOwn, hws]
    · have hmem := RcCtx.get?_mem hgz
      obtain ⟨_, w, _, hHv, _, _⟩ := hinv.2.2.2.1 v hmem.1 hvl
      rw [hmem.2] at hHv
      refine ⟨w :: ws, ?_, by simp [hlen]⟩
      simp [HValEnv.evalArgsOwn, HValEnv.evalArgOwn, hHv, hws]

end JpSupport

end LeanQbe.T.LeanLCNF.Sem
