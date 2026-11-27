module

public import LeanQbe.T.LeanLCNF.Sem.PerceusJp5

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T

section JpSteps

private theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = Except.ok b) : ∃ a, x = Except.ok a ∧ f a = Except.ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem noMut_of_jpLiveNoMut_jmp {e : JpEntry} {j : Nat} {as : List LcArg}
    (hjlnm : jpLiveNoMut e.info.id (baseCtxLiveIds e.baseCtx) e.mutVars (LcCode.jmp j as) = true)
    (heid : e.info.id = j) :
    ∀ id ∈ baseCtxLiveIds e.baseCtx, id ∉ e.mutVars := by
  simp only [jpLiveNoMut.eq_6, heid, beq_self_eq_true, ↓reduceIte] at hjlnm
  intro id hid hin
  have h1 : e.mutVars.any (baseCtxLiveIds e.baseCtx).contains = true :=
    List.any_eq_true.mpr ⟨id, hin, List.contains_iff_mem.mpr hid⟩
  simp [h1] at hjlnm

private theorem staticAgree_ctx_base {baseCtx ctx0 c0 : RcCtx}
    (hagree_c0 : StaticAgree (baseCtxLiveIds baseCtx) ctx0 c0)
    (hw_c0 : CtxWeakens baseCtx c0)
    (hmap : baseCtx.vars.map RcVar.id = c0.vars.map RcVar.id)
    (hhead : ∀ w ∈ baseCtx.vars, ∃ v ∈ c0.vars, w.id = v.id ∧ w.ty = v.ty)
    (hsp : ∀ p, p ∈ baseCtx.sharedPreds → p ∈ c0.sharedPreds) :
    StaticAgree (baseCtxLiveIds baseCtx) ctx0 baseCtx := by
  refine ⟨fun id hid hl => ?_, fun p hp hp1 => ?_⟩
  · cases hgb : baseCtx.get? id with
    | none => rw [hgb] at hl; cases hl
    | some w =>
      rw [hgb] at hl
      simp only [Option.map_some, Option.some.injEq] at hl
      have hw_mem := (RcCtx.get?_mem hgb).1
      have hwid := (RcCtx.get?_mem hgb).2
      obtain ⟨v, hv_mem, hvid, _, _, hno, hps, how, hbr, _, hrt⟩ := hw_c0.2.2.1 w hw_mem
      obtain ⟨v', hv'_mem, hvid', hty'⟩ := hhead w hw_mem
      have hgv : c0.get? id = some v := by
        rw [← hwid, hvid]; exact (RcCtx.mem_get?_iff hw_c0.2.1).mpr hv_mem
      have hgv' : c0.get? id = some v' := by
        rw [← hwid, hvid']; exact (RcCtx.mem_get?_iff hw_c0.2.1).mpr hv'_mem
      rw [hgv] at hgv'; cases hgv'
      have hvl : v.isLive = true := by
        by_cases hvrt : v.resetTok = true
        · simp [RcVar.isLive, hvrt]
        · have hvrtF : v.resetTok = false := Bool.eq_false_iff.mpr hvrt
          have hwrtF : w.resetTok = false := hrt hvrtF
          simp only [RcVar.isLive, hwrtF, Bool.or_false] at hl
          rcases Bool.or_eq_true _ _ |>.mp hl with h123 | hbrw
          · rcases Bool.or_eq_true _ _ |>.mp h123 with h12 | howw
            · rcases Bool.or_eq_true _ _ |>.mp h12 with hnow | hpsw
              · simp [RcVar.isLive, ← hno, hnow]
              · simp [RcVar.isLive, ← hps, hpsw]
            · simp [RcVar.isLive, ← how, howw]
          · simp [RcVar.isLive, (hbr hbrw).1]
      have h1 := hagree_c0.1 id hid (by simp [hgv, hvl])
      refine ⟨h1.1, h1.2.trans ?_⟩
      simp only [hgv, Option.map_some, Option.some.injEq]
      exact hty'.symm
  · have hpc0 : p ∈ c0.sharedPreds := hsp p hp
    have h1 := hagree_c0.2 p hpc0 hp1
    refine ⟨h1.1, h1.2.trans ?_⟩
    cases hgb : baseCtx.get? p.2 with
    | none =>
      cases hgc : c0.get? p.2 with
      | none => rfl
      | some v =>
        exfalso
        have his : (c0.get? p.2).isSome = true := by simp [hgc]
        rw [get?_isSome_iff_mem_map_id c0 p.2, ← hmap,
          ← get?_isSome_iff_mem_map_id baseCtx p.2, hgb] at his
        cases his
    | some w =>
      obtain ⟨v', hv'_mem, hvid', hty'⟩ := hhead w (RcCtx.get?_mem hgb).1
      have hgc : c0.get? p.2 = some v' := by
        rw [← (RcCtx.get?_mem hgb).2, hvid']
        exact (RcCtx.mem_get?_iff hw_c0.2.1).mpr hv'_mem
      simp [hgc, hty']

/-- Join-point jump step simulation (`jmp`). -/
public theorem jmp_step {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {Jp : PResJEnv} {Jh : HJEnv} {Q : PResPost} {Xp : PResXPost}
    {Qh : HPost} {Xh : HXPost} {jpsOk : List JpEntry} {rf0 rf : RcFrame} {σ0 σ : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr : Nat}
    {j : Nat} {as : List LcArg} {jumps : List (Nat × RcCtx)}
    (hchk : checkCode env retTy (jpsOk.map JpEntry.info) rf.ctx (LcCode.jmp j as) = Except.ok jumps)
    (hwf : perceusCodeWf env retTy (jpsOk.map JpEntry.info) rf.ctx sm (LcCode.jmp j as) = true)
    (hpr : PRWp m env retTy Δr (jpsOk.map JpEntry.info) rf.ctx Jp ρP rem wr rcr Q Xp
      (LcCode.jmp j as))
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hst : SharedTargetsHeap rf) (hheap : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hep : EntryPres rf0 σ0 rf σ) (hsbv : SharedBoolVars rf.ctx) (hsbp : SharedBoolPreds rf.ctx)
    (hexcl : ExclCtorHeap rf) (hsh : ShadowOk sm rf.ctx ρP rf.envP)
    (hrs : ResStateInv σ rem wr rcr)
    (hjps : JpsOk rt rf0 σ0 Jp Jh jpsOk rf ρP jumps)
    (hjlnm : ∀ e ∈ jpsOk,
      jpLiveNoMut e.info.id (baseCtxLiveIds e.baseCtx) e.mutVars (LcCode.jmp j as) = true)
    (hpw_j : ∀ e ∈ jpsOk, e.info.id = j → ∀ pvs, ρP.evalArgs as = some pvs → e.PBody pvs) :
    HWp Δh rt retTy Jh rf.envH Qh Xh (LcCode.jmp j as) σ := by
  rw [checkCode.eq_3] at hchk
  cases hfd : (jpsOk.map JpEntry.info).find? (fun x => x.id == j) with
  | none => rw [hfd] at hchk; cases hchk
  | some info =>
    rw [hfd] at hchk
    obtain ⟨ctx1, ha1, hrest⟩ := except_bind_ok hchk
    obtain ⟨⟨⟩, hleaks, hjumps⟩ := except_bind_ok hrest
    simp only [pure, Except.pure, Except.ok.injEq] at hjumps
    obtain ⟨e, he_mem, rfl, heid⟩ := jpsOk_find?_mem hfd
    obtain ⟨hok, hlive, hjmp_w⟩ := hjps e he_mem
    have hw_base : CtxWeakens e.baseCtx (ctx1.restrict e.info.scopeIds) :=
      hjmp_w (j, ctx1.restrict e.info.scopeIds)
        (by rw [← hjumps]; exact List.mem_singleton.mpr rfl) heid.symm
    rw [perceusCodeWf.eq_4] at hwf
    have hwf1 := Bool.and_eq_true _ _ |>.mp hwf
    have harg_sc := hwf1.1
    have hwf2 := hwf1.2
    rw [hfd] at hwf2
    dsimp only at hwf2
    have hwf3 := Bool.and_eq_true _ _ |>.mp hwf2
    have hwf4 := Bool.and_eq_true _ _ |>.mp hwf3.1
    have hmatch := hwf4.1
    have hnoSh := hwf4.2
    have hbext : argsBorrowFromExt ctx1 as (e.info.params.map (·.borrow)) = true := by
      simpa [ha1] using hwf3.2
    have hall_live : ∀ a ∈ as, a = LcArg.erased ∨
        ∃ z v, a = LcArg.var z ∧ rf.ctx.get? z = some v ∧ v.isLive = true := fun a ha =>
      applyArgs_var_live hinv.2.1 hclean ha1 a ha
    obtain ⟨pvs_rf, hpvs_rf, hlen_pvs⟩ := evalArgs_some_live hall_live (fun v hv hvl => by
      obtain ⟨pv, _, hP, _⟩ := hinv.2.2.2.1 v hv hvl; exact ⟨pv, hP⟩)
    obtain ⟨ws, hws, hlen_ws⟩ := evalArgsOwn_some hinv hall_live
    have hpvs_eq : ρP.evalArgs as = rf.envP.evalArgs as :=
      evalArgs_of_shadowOk hsh harg_sc hall_live
    rw [PRWp.eq_3, hpvs_eq, hpvs_rf] at hpr
    have hpb := hpw_j e he_mem heid pvs_rf (hpvs_eq.trans hpvs_rf)
    obtain ⟨hlen_p, hk_e⟩ := hok.2.2.2.2.2.2.2 pvs_rf rem wr rcr (heid ▸ hpr) hpb
    have hlen3 : as.length = e.info.params.length := hlen_pvs.symm.trans hlen_p
    have hlen2 : ws.length = e.info.params.length := hlen_ws.trans hlen3
    have hpm : paramsMatch e.info.params ws :=
      paramsMatch_of_argsMatchTys hinv e.info.params as pvs_rf ws hmatch hpvs_rf hws hall_live
    have hnoMut := noMut_of_jpLiveNoMut_jmp (hjlnm e he_mem) heid
    obtain ⟨hinvB, hcleanB, hpoB, hnorcB, hpcbB, hstB, hheapB, hepB, hsbvB, hsbpB, hexclB⟩ :=
      jmp_bindParams_invs hinv hclean hpo hnorc hpcb hst hheap hep hsbv hsbp hexcl
        hok hlive ha1 hleaks hmatch hnoSh hbext hw_base hnoMut hpvs_rf hws
        hlen_p hlen2 hlen3 hall_live
    have hall_sim : ∀ a ∈ as, match a with
        | LcArg.erased => True
        | LcArg.var id => ∃ v, rf.ctx.get? id = some v ∧ v.isLive = true := by
      intro a ha
      rcases hall_live a ha with rfl | ⟨z, v, rfl, hgz, hvl⟩
      · trivial
      · exact ⟨v, hgz, hvl⟩
    obtain ⟨ws', hws', havr⟩ := evalArgsOwn_sim hinv.2.2.2.1 hall_sim hpvs_rf
    rw [hws, Option.some.injEq] at hws'; subst hws'
    have hJh := hk_e ws σ rf.ghostH hpm hinvB hcleanB hpoB hnorcB hpcbB hstB
      hheapB hepB hsbvB hsbpB hexclB hrs havr
    rw [HWp.eq_3, hws]
    exact heid ▸ hJh

/-- Join-point introduction step simulation (`jp`). -/
public theorem jp_step {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {Jp : PResJEnv} {Jh : HJEnv} {Qp : PResPost} {Xp : PResXPost}
    {Qh : HPost} {Xh : HXPost} {jpsOk : List JpEntry} {rf0 rf : RcFrame} {σ0 σ : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr : Nat}
    {j : Nat} {ps : List LcParam} {body k : LcCode} {jumps : List (Nat × RcCtx)}
    {PBody : List PVal → Prop}
    (hchk : checkCode env retTy (jpsOk.map JpEntry.info) rf.ctx (LcCode.jp j ps body k) =
      Except.ok jumps)
    (hwf : perceusCodeWf env retTy (jpsOk.map JpEntry.info) rf.ctx sm (LcCode.jp j ps body k) =
      true)
    (hpr : PRWp m env retTy Δr (jpsOk.map JpEntry.info) rf.ctx Jp ρP rem wr rcr Qp Xp
      (LcCode.jp j ps body k))
    (hinv : RcInv rt rf σ)
    (hep : EntryPres rf0 σ0 rf σ) (hsh : ShadowOk sm rf.ctx ρP rf.envP)
    (hstatic : CtxStaticInv rf.ctx)
    (hscope : JpsScopeIn (jpsOk.map JpEntry.info) rf.ctx)
    (hjps : JpsOk rt rf0 σ0 Jp Jh jpsOk rf ρP jumps)
    (hjlnm : ∀ e ∈ jpsOk,
      jpLiveNoMut e.info.id (baseCtxLiveIds e.baseCtx) e.mutVars (LcCode.jp j ps body k) = true)
    (hpb : ∀ e ∈ jpsOk, ∀ pvs, e.PBody pvs) (hPBody : ∀ pvs, PBody pvs)
    (hbody : ∀ (Jp' : PResJEnv) (Jh' : HJEnv) (jpsOk' : List JpEntry) (rf' : RcFrame)
        (σ' : HState) (sm' : List (Nat × Nat × List Bool)) (ρP' : PValEnv)
        (rem' wr' rcr' : Nat) (jumps' : List (Nat × RcCtx)),
      checkCode env retTy (jpsOk'.map JpEntry.info) rf'.ctx body = Except.ok jumps' →
      perceusCodeWf env retTy (jpsOk'.map JpEntry.info) rf'.ctx sm' body = true →
      PRWp m env retTy Δr (jpsOk'.map JpEntry.info) rf'.ctx Jp' ρP' rem' wr' rcr' Qp Xp body →
      (∃ pvs, ρP' = ρP.bindAll ps pvs ∧ PBody pvs) →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs → EntryPres rf0 σ0 rf' σ' →
      SharedBoolVars rf'.ctx → SharedBoolPreds rf'.ctx → ExclCtorHeap rf' →
      ShadowOk sm' rf'.ctx ρP' rf'.envP → ShadowSmWf sm' →
      ResStateInv σ' rem' wr' rcr' → CtxStaticInv rf'.ctx →
      JpsScopeIn (jpsOk'.map JpEntry.info) rf'.ctx →
      JpsOk rt rf0 σ0 Jp' Jh' jpsOk' rf' ρP' jumps' →
      (∀ e ∈ jpsOk',
        jpLiveNoMut e.info.id (baseCtxLiveIds e.baseCtx) e.mutVars body = true) →
      (∀ e ∈ jpsOk', ∀ pvs, e.PBody pvs) →
      HWp Δh rt retTy Jh' rf'.envH Qh Xh body σ')
    (hk : ∀ (Jp' : PResJEnv) (Jh' : HJEnv) (jpsOk' : List JpEntry)
        (jumps' : List (Nat × RcCtx)),
      PRWp m env retTy Δr (jpsOk'.map JpEntry.info) rf.ctx Jp' ρP rem wr rcr Qp Xp k →
      checkCode env retTy (jpsOk'.map JpEntry.info) rf.ctx k = Except.ok jumps' →
      perceusCodeWf env retTy (jpsOk'.map JpEntry.info) rf.ctx sm k = true →
      JpsScopeIn (jpsOk'.map JpEntry.info) rf.ctx →
      JpsOk rt rf0 σ0 Jp' Jh' jpsOk' rf ρP jumps' →
      (∀ e ∈ jpsOk',
        jpLiveNoMut e.info.id (baseCtxLiveIds e.baseCtx) e.mutVars k = true) →
      (∀ e ∈ jpsOk', ∀ pvs, e.PBody pvs) →
      HWp Δh rt retTy Jh' rf.envH Qh Xh k σ) :
    HWp Δh rt retTy Jh rf.envH Qh Xh (LcCode.jp j ps body k) σ := by
  have hchk0 := hchk
  rw [checkCode.eq_2] at hchk
  dsimp only at hchk
  obtain ⟨jumpsK, hckK, hrest⟩ := except_bind_ok hchk
  obtain ⟨optC, hmg, hrest2⟩ := except_bind_ok hrest
  let baseCtx := optC.getD rf.ctx
  have hbase_eq : jpBaseCtx env retTy (jpsOk.map JpEntry.info) rf.ctx j ps k = baseCtx :=
    jpBaseCtx_eq_of_check hckK hmg
  have hckB_ex : ∃ jumpsBody,
      checkCode env retTy (jpsOk.map JpEntry.info) (baseCtx.bindParams ps) body =
        Except.ok jumpsBody ∧
      jumps = List.filter (fun x => x.fst != j) jumpsK ++ jumpsBody := by
    cases optC with
    | none =>
      simp only [baseCtx, Option.getD_none]
      simp only [bind, Except.bind, pure, Except.pure] at hrest2
      obtain ⟨jumpsBody, hB, hp⟩ := except_bind_ok hrest2
      simp only [Except.ok.injEq] at hp
      exact ⟨jumpsBody, hB, hp.symm⟩
    | some c' =>
      simp only [baseCtx, Option.getD_some]
      simp only [bind, Except.bind, pure, Except.pure] at hrest2
      obtain ⟨jumpsBody, hB, hp⟩ := except_bind_ok hrest2
      simp only [Except.ok.injEq] at hp
      exact ⟨jumpsBody, hB, hp.symm⟩
  obtain ⟨jumpsBody, hckB, hjumps_eq⟩ := hckB_ex
  have hwf0 := hwf
  rw [perceusCodeWf.eq_3] at hwf
  dsimp only at hwf
  rw [hbase_eq] at hwf
  have hw1 := Bool.and_eq_true _ _ |>.mp hwf
  have hwfB := hw1.2
  have hw2 := Bool.and_eq_true _ _ |>.mp hw1.1
  have hwfK := hw2.2
  have hw3 := Bool.and_eq_true _ _ |>.mp hw2.1
  have hjlnm_k := hw3.2
  have hw4 := Bool.and_eq_true _ _ |>.mp hw3.1
  have hall_sc := hw4.2
  have hw5 := Bool.and_eq_true _ _ |>.mp hw4.1
  have hfrB := hw5.2
  have hw6 := Bool.and_eq_true _ _ |>.mp hw5.1
  have hall_ne := hw6.1
  have hndP := of_decide_eq_true hw6.2
  have hneJ : ∀ e ∈ jpsOk, e.info.id ≠ j := by
    intro e he heq
    have h1 := List.all_eq_true.mp hall_ne e.info (List.mem_map.mpr ⟨e, he, rfl⟩)
    simp [heq] at h1
  obtain ⟨hsB, hpermB, hsomeB, hweakB, hheadB⟩ :=
    jpBaseCtx_static_invs hstatic hscope hckK hmg hwf0
  have hnd_scope : (rf.ctx.vars.map RcVar.id).Nodup := hinv.2.1
  have hscopeK : JpsScopeIn
      ({ id := j, params := ps, scopeIds := rf.ctx.vars.map (·.id) } :: jpsOk.map JpEntry.info)
      rf.ctx := by
    refine ⟨List.nodup_cons.mpr ⟨fun hin => ?_, hscope.1⟩, fun info hinfo => ?_⟩
    · obtain ⟨info, hinfo, hid⟩ := List.mem_map.mp hin
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hinfo
      exact absurd hid (hneJ e he)
    · rcases List.mem_cons.mp hinfo with rfl | hmem
      · refine ⟨hndP, hnd_scope, fun id hid => ?_⟩
        exact (get?_isSome_iff_mem_map_id rf.ctx id).mpr hid
      · exact hscope.2 info hmem
  have hstaticB : CtxStaticInv (baseCtx.bindParams ps) :=
    (bindParams_static_invs hsB hndP hfrB).1
  have hscopeB : JpsScopeIn (jpsOk.map JpEntry.info) (baseCtx.bindParams ps) := by
    refine ⟨hscope.1, fun info hinfo => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hscope.2 info hinfo
    refine ⟨h1, h2, fun id hid => ?_⟩
    exact (bindParams_static_invs hsB hndP hfrB).2 id (hsomeB id (h3 id hid))
  have hagree_base : StaticAgree (baseCtxLiveIds baseCtx) rf.ctx baseCtx := by
    cases hmj : (jumpsK.filter (fun x => x.1 == j)).map Prod.snd with
    | nil =>
      rw [hmj] at hmg
      have hnone : optC = none := by
        unfold mergeJpList at hmg
        simp only [pure, Except.pure, Except.ok.injEq] at hmg
        exact hmg.symm
      subst hnone
      exact staticAgree_refl (baseCtxLiveIds baseCtx) rf.ctx
    | cons c0 rest =>
      have hc0 : c0 ∈ (jumpsK.filter (fun x => x.1 == j)).map Prod.snd := by
        rw [hmj]; exact List.mem_cons_self
      obtain ⟨jc, hjc_f, hjc_snd⟩ := List.mem_map.mp hc0
      have hjc_mem := (List.mem_filter.mp hjc_f).1
      have hjc_id : jc.1 = j := beq_iff_eq.mp (List.mem_filter.mp hjc_f).2
      have hfilt_eq :
          List.filter (fun id => !([] : List Nat).contains id) (baseCtxLiveIds baseCtx) =
            baseCtxLiveIds baseCtx :=
        List.filter_eq_self.mpr (fun _ _ => by simp)
      have hagree_c0 : StaticAgree (baseCtxLiveIds baseCtx) rf.ctx c0 := by
        have hst0 := staticAgree_refl (baseCtxLiveIds baseCtx) rf.ctx
        rw [← hfilt_eq] at hst0
        rw [← hjc_snd]
        exact checkCode_static_agree hstatic hscopeK hckK hwfK hjlnm_k hst0 jc hjc_mem hjc_id
      have hhd := hheadB c0 rest hmj
      exact staticAgree_ctx_base hagree_c0 (hweakB c0 (hmj ▸ List.mem_cons_self))
        hhd.1 hhd.2.1 hhd.2.2
  let Jp_j : List PVal → Nat → Nat → Nat → Prop := fun pvs rem' wr' rcr' =>
    pvs.length = ps.length ∧
    PRWp m env retTy Δr (jpsOk.map JpEntry.info) (baseCtx.bindParams ps) Jp
      (ρP.bindAll ps pvs) rem' wr' rcr' Qp Xp body
  have hpr_k : PRWp m env retTy Δr
      ({ id := j, params := ps, scopeIds := rf.ctx.vars.map (·.id) } :: jpsOk.map JpEntry.info)
      rf.ctx (Jp.set j Jp_j) ρP rem wr rcr Qp Xp k := by
    rw [PRWp.eq_2] at hpr
    dsimp only at hpr
    rw [hbase_eq] at hpr
    refine hpr Jp_j fun as rem' wr' rcr' hlen hbody_pr => ⟨hlen, ?_⟩
    refine PRWp_jp_congr_of_check body (jpsOk.map JpEntry.info) (baseCtx.bindParams ps)
      (Jp.set j Jp_j) Jp (fun id hid => ?_) jumpsBody hckB _ _ _ _ hbody_pr
    obtain ⟨info, hinfo, rfl⟩ := hid
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hinfo
    funext a r' w' rc'
    simp [PResJEnv.set, hneJ e he]
  rw [HWp.eq_2]
  intro Jh_j hJh_j
  let jInfo : RcJpInfo := { id := j, params := ps, scopeIds := rf.ctx.vars.map (·.id) }
  let e_new : JpEntry := {
    info := jInfo, ctxJp := rf.ctx, envPJp := rf.envP, envHJp := rf.envH,
    extH := rf.extH, baseCtx := baseCtx, mutVars := [], PBody := PBody }
  have hok_new : JpEntryOk rt rf0 σ0 (Jp.set j Jp_j) (Jh.set j Jh_j) e_new := by
    refine ⟨rfl, hep.2.2.1, hndP, hfrB, hsB, hpermB, hagree_base,
      fun pvs rem' wr' rcr' hJpj hpb_j => ?_⟩
    simp only [PResJEnv.set, ↓reduceIte, e_new, jInfo] at hJpj hpb
    obtain ⟨hlen_pvs, hpr_body⟩ := hJpj
    refine ⟨hlen_pvs, fun ws σ' ghostH' hpm hinvB hcleanB hpoB hnorcB hpcbB hstB
        hheapB hepB hsbvB hsbpB hexclB hrsB havr => ?_⟩
    simp only [HJEnv.set, e_new, jInfo, ↓reduceIte]
    refine hJh_j ws σ' hpm ?_
    let jpsOk_body : List JpEntry := List.map (fun e => ({
      info := e.info, ctxJp := e.ctxJp, envPJp := e.envPJp, envHJp := e.envHJp,
      extH := e.extH, baseCtx := e.baseCtx, mutVars := ps.map (·.id) ++ e.mutVars,
      PBody := e.PBody } : JpEntry))
      jpsOk
    have hmap_body : jpsOk_body.map JpEntry.info = jpsOk.map JpEntry.info := by
      simp [jpsOk_body, List.map_map, Function.comp_def]
    have hjps_body := jpsOk_enter_body hstatic hscope hckK hmg hwf0 hneJ
      (hjumps_eq ▸ hjps) (Jh_j := Jh_j) (pvs := pvs) (ws := ws) (ghostH' := ghostH')
    dsimp only at hjps_body
    change JpsOk rt rf0 σ0 Jp (Jh.set j Jh_j) jpsOk_body
      { ctx := baseCtx.bindParams ps, envP := rf.envP.bindAll ps pvs,
        envH := rf.envH.bindAll ps ws, extH := rf.extH, ghostH := ghostH' }
      (ρP.bindAll ps pvs) jumpsBody at hjps_body
    have hjlnm_body : ∀ e ∈ jpsOk_body,
        jpLiveNoMut e.info.id (baseCtxLiveIds e.baseCtx) e.mutVars body = true := by
      intro e he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
      have h0 := hjlnm e0 he0
      rw [jpLiveNoMut.eq_5] at h0
      exact (Bool.and_eq_true _ _ |>.mp h0).1
    have hsh_body : ShadowOk [] (baseCtx.bindParams ps) (ρP.bindAll ps pvs)
        (rf.envP.bindAll ps pvs) := by
      refine shadowOk_bindParams_empty hsB hndP hlen_pvs hall_sc hsh (fun v hv_b hvl => ?_)
      have hid_live : v.id ∈ baseCtxLiveIds baseCtx :=
        List.mem_map.mpr ⟨v, List.mem_filter.mpr ⟨hv_b, hvl⟩, rfl⟩
      have hgb_b := (RcCtx.mem_get?_iff hsB.1).mpr hv_b
      have hlive_rf := (hagree_base.1 v.id hid_live (by
        simp only [Option.map_eq_some_iff]; exact ⟨v, hgb_b, hvl⟩)).1
      obtain ⟨v_rf, hgf_rf, hrf_mem, hrf_id, hrf_l⟩ := vars_mem_of_id_live hlive_rf
      exact ⟨v_rf, hrf_mem, hrf_id, hrf_l⟩
    have hpb_body : ∀ e ∈ jpsOk_body, ∀ pvs, e.PBody pvs := by
      intro e he pvs
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
      exact hpb e0 he0 pvs
    have hwb := hbody Jp (Jh.set j Jh_j) jpsOk_body
      { ctx := baseCtx.bindParams ps, envP := rf.envP.bindAll ps pvs,
        envH := rf.envH.bindAll ps ws, extH := rf.extH, ghostH := ghostH' }
      σ' [] (ρP.bindAll ps pvs) rem' wr' rcr' jumpsBody
      (hmap_body ▸ hckB) (hmap_body ▸ hwfB) (hmap_body ▸ hpr_body) ⟨pvs, rfl, hpb_j⟩
      hinvB hcleanB hpoB hnorcB hpcbB hstB hheapB hepB hsbvB hsbpB hexclB
      hsh_body List.nodup_nil hrsB hstaticB (hmap_body ▸ hscopeB) hjps_body hjlnm_body
      hpb_body
    exact hwb
  have hlive_new : JpEntryLiveAgree e_new rf ρP := by
    refine ⟨fun id hid _ hgf => ?_, fun p hp _ _ => ⟨hp, rfl, rfl⟩⟩
    obtain ⟨u, hu, heq⟩ := List.mem_map.mp hid
    have hmem_u := (List.mem_filter.mp hu).1
    have hlive_u := (List.mem_filter.mp hu).2
    have hinit : isVarScalarInit sm id = true := by
      have h1 := List.all_eq_true.mp hall_sc u hmem_u
      rw [← heq]
      simpa [hlive_u] using h1
    obtain ⟨v_rf, _, hrf_mem, _, hrf_l⟩ := vars_mem_of_id_live hgf
    have hsh_v := hsh v_rf hrf_mem hrf_l
    have hid_rf : v_rf.id = id := (RcCtx.get?_mem ‹_›).2
    simp only [hid_rf, hinit, ↓reduceIte] at hsh_v
    exact ⟨rfl, rfl, hsh_v, rfl, hgf⟩
  have hjps_k : JpsOk rt rf0 σ0 (Jp.set j Jp_j) (Jh.set j Jh_j) (e_new :: jpsOk) rf ρP jumpsK := by
    have hjps_out : JpsOk rt rf0 σ0 (Jp.set j Jp_j) (Jh.set j Jh_j) jpsOk rf ρP jumps :=
      jpsOk_set_jh_of_ne hneJ (jpsOk_set_jp_of_ne hneJ hjps)
    intro e he
    rcases List.mem_cons.mp he with rfl | he_tail
    · refine ⟨hok_new, hlive_new, fun jc hjc hjeq => ?_⟩
      have hjc_in : jc.2 ∈ (jumpsK.filter (fun x => x.1 == j)).map Prod.snd :=
        List.mem_map.mpr ⟨jc, List.mem_filter.mpr ⟨hjc, beq_iff_eq.mpr hjeq⟩, rfl⟩
      exact hweakB jc.2 hjc_in
    · obtain ⟨hok_e, hlive_e, hjmp_e⟩ := hjps_out e he_tail
      refine ⟨hok_e, hlive_e, fun jc hjc hjeq => ?_⟩
      have hne_ej : jc.1 ≠ j := by rw [hjeq]; exact hneJ e he_tail
      have hjc_f : jc ∈ jumps := by
        rw [hjumps_eq]
        exact List.mem_append.mpr (Or.inl (List.mem_filter.mpr ⟨hjc, bne_iff_ne.mpr hne_ej⟩))
      exact hjmp_e jc hjc_f hjeq
  have hjlnm_k_all : ∀ e ∈ (e_new :: jpsOk),
      jpLiveNoMut e.info.id (baseCtxLiveIds e.baseCtx) e.mutVars k = true := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he_tail
    · exact hjlnm_k
    · have h0 := hjlnm e he_tail
      rw [jpLiveNoMut.eq_5] at h0
      exact (Bool.and_eq_true _ _ |>.mp h0).2
  have hpb_k_all : ∀ e ∈ (e_new :: jpsOk), ∀ pvs, e.PBody pvs := by
    intro e he pvs
    rcases List.mem_cons.mp he with rfl | he_tail
    · exact hPBody pvs
    · exact hpb e he_tail pvs
  exact hk (Jp.set j Jp_j) (Jh.set j Jh_j) (e_new :: jpsOk) jumpsK
    hpr_k hckK hwfK hscopeK hjps_k hjlnm_k_all hpb_k_all

end JpSteps

end LeanQbe.T.LeanLCNF.Sem
