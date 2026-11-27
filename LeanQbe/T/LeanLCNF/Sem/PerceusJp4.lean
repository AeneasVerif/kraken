module

public import LeanQbe.T.LeanLCNF.Sem.PerceusJp3
public import LeanQbe.T.LeanLCNF.Sem.PerceusCall

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T

section JpsOkDefs

private theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = Except.ok b) : ∃ a, x = Except.ok a ∧ f a = Except.ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- Dynamic tracking entry for an enclosing join point along a checked path. -/
public structure JpEntry where
  info : RcJpInfo
  ctxJp : RcCtx
  envPJp : PValEnv
  envHJp : HValEnv
  extH : List (BitVec 64)
  baseCtx : RcCtx
  mutVars : List Nat
  PBody : List PVal → Prop := fun _ => True

/-- Agreement of unmutated live variables and `sharedPreds` relative to `JpEntry`. -/
@[expose] public def JpEntryLiveAgree (e : JpEntry) (rf : RcFrame) (ρP : PValEnv) : Prop :=
  (∀ id ∈ baseCtxLiveIds e.baseCtx, id ∉ e.mutVars →
    (rf.ctx.get? id).map RcVar.isLive = some true →
      rf.envP id = e.envPJp id ∧ rf.envH id = e.envHJp id ∧ ρP id = e.envPJp id ∧
      (rf.ctx.get? id).map (·.ty) = (e.ctxJp.get? id).map (·.ty) ∧
      (e.ctxJp.get? id).map RcVar.isLive = some true) ∧
  (∀ p ∈ rf.ctx.sharedPreds, p.1 ∈ baseCtxLiveIds e.baseCtx → p.1 ∉ e.mutVars →
    p ∈ e.ctxJp.sharedPreds ∧ rf.envH p.2 = e.envHJp p.2 ∧
    (rf.ctx.get? p.2).map (·.ty) = (e.ctxJp.get? p.2).map (·.ty))

/-- Static + semantic contract for an enclosing join point entry `e`. -/
@[expose] public def JpEntryOk (rt : BitVec 64) (rf0 : RcFrame) (σ0 : HState)
    (Jp : PResJEnv) (Jh : HJEnv) (e : JpEntry) : Prop :=
  e.info.scopeIds = e.ctxJp.vars.map (·.id) ∧
  e.extH = rf0.extH ∧
  (e.info.params.map (·.id)).Nodup ∧
  e.info.params.all (binderFreshOwned e.baseCtx ·.id) = true ∧
  CtxStaticInv e.baseCtx ∧
  (e.baseCtx.vars.map RcVar.id).Perm e.info.scopeIds ∧
  StaticAgree (baseCtxLiveIds e.baseCtx) e.ctxJp e.baseCtx ∧
  ∀ pvs rem wr rcr, Jp e.info.id pvs rem wr rcr →
    e.PBody pvs →
    pvs.length = e.info.params.length ∧
    ∀ ws σ' ghostH',
      let rfB : RcFrame := {
        ctx := e.baseCtx.bindParams e.info.params,
        envP := e.envPJp.bindAll e.info.params pvs,
        envH := e.envHJp.bindAll e.info.params ws,
        extH := e.extH, ghostH := ghostH' }
      paramsMatch e.info.params ws →
      RcInv rt rfB σ' → CleanVars rfB.ctx → ParentsOwned rfB.ctx → NoRcCorrect rfB.ctx →
      ParentChildBacked rfB σ'.objs → SharedTargetsHeap rfB →
      HandlesInHeap (rfB.extH ++ rfB.ghostH) σ'.objs →
      EntryPres rf0 σ0 rfB σ' → SharedBoolVars rfB.ctx → SharedBoolPreds rfB.ctx →
      ExclCtorHeap rfB → ResStateInv σ' rem wr rcr → ArgsValRep pvs ws σ'.objs →
      Jh e.info.id ws σ'

/-- Join-point environment invariant tying `jps` to `jpsOk` and current `jumps`. -/
@[expose] public def JpsOk (rt : BitVec 64) (rf0 : RcFrame) (σ0 : HState)
    (Jp : PResJEnv) (Jh : HJEnv) (jpsOk : List JpEntry) (rf : RcFrame) (ρP : PValEnv)
    (jumps : List (Nat × RcCtx)) : Prop :=
  ∀ e ∈ jpsOk, JpEntryOk rt rf0 σ0 Jp Jh e ∧ JpEntryLiveAgree e rf ρP ∧
    ∀ jc ∈ jumps, jc.1 = e.info.id → CtxWeakens e.baseCtx jc.2

/-- Lookup in `jpsOk` matching `jpsOk.map JpEntry.info`. -/
public theorem jpsOk_find?_mem {jpsOk : List JpEntry} {j : Nat} {info : RcJpInfo}
    (hf : (jpsOk.map JpEntry.info).find? (·.id == j) = some info) :
    ∃ e ∈ jpsOk, e.info = info ∧ info.id = j := by
  induction jpsOk with
  | nil => cases hf
  | cons hd tl ih =>
    simp only [List.map_cons, List.find?_cons] at hf
    by_cases heq : (hd.info.id == j) = true
    · simp only [heq] at hf; cases hf
      exact ⟨hd, List.mem_cons_self, rfl, beq_iff_eq.mp heq⟩
    · simp only [heq] at hf
      obtain ⟨e, he, hinfo, hid⟩ := ih hf
      exact ⟨e, List.mem_cons_of_mem _ he, hinfo, hid⟩

/-- `JpsOk` is invariant across context-only steps (`inc`/`dec`/`del`/`cases`). -/
public theorem jpsOk_ctx_step {rt : BitVec 64} {rf0 : RcFrame} {σ0 : HState}
    {Jp : PResJEnv} {Jh : HJEnv} {jpsOk : List JpEntry} {rf : RcFrame} {ρP : PValEnv}
    {jumps jumps' : List (Nat × RcCtx)} {ctx' : RcCtx} {ghostH' : List (BitVec 64)}
    (hjps : JpsOk rt rf0 σ0 Jp Jh jpsOk rf ρP jumps)
    (hstep : (∀ z, (ctx'.get? z).map (·.ty) = (rf.ctx.get? z).map (·.ty) ∧
      ((ctx'.get? z).map RcVar.isLive = some true →
        (rf.ctx.get? z).map RcVar.isLive = some true)) ∧
      (∀ p, p ∈ ctx'.sharedPreds → p ∈ rf.ctx.sharedPreds))
    (hjumps : ∀ jc ∈ jumps', jc ∈ jumps) :
    JpsOk rt rf0 σ0 Jp Jh jpsOk
      { ctx := ctx', envP := rf.envP, envH := rf.envH, extH := rf.extH, ghostH := ghostH' }
      ρP jumps' := by
  intro e he
  obtain ⟨hok, hlive, hw⟩ := hjps e he
  refine ⟨hok, ⟨fun id hid hnot hl => ?_, fun p hp h1 hnot => ?_⟩, fun jc hjc hjeq =>
      hw jc (hjumps jc hjc) hjeq⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hlive.1 id hid hnot ((hstep.1 id).2 hl)
    exact ⟨h1, h2, h3, (hstep.1 id).1.trans h4, h5⟩
  · obtain ⟨hp0, heh, hty⟩ := hlive.2 p (hstep.2 p hp) h1 hnot
    exact ⟨hp0, heh, (hstep.1 p.2).1.trans hty⟩

/-- `JpsOk` is invariant across steps mutating `x` and updating environments only at `x`. -/
public theorem jpsOk_mut_step {rt : BitVec 64} {rf0 : RcFrame} {σ0 : HState}
    {Jp : PResJEnv} {Jh : HJEnv} {jpsOk : List JpEntry} {rf : RcFrame} {ρP ρP' : PValEnv}
    {jumps jumps' : List (Nat × RcCtx)} {ctx' : RcCtx} {envP' : PValEnv} {envH' : HValEnv}
    {ghostH' : List (BitVec 64)} {x : Nat}
    (hjps : JpsOk rt rf0 σ0 Jp Jh jpsOk rf ρP jumps)
    (hstep : (∀ z, z ≠ x → (ctx'.get? z).map (·.ty) = (rf.ctx.get? z).map (·.ty) ∧
      ((ctx'.get? z).map RcVar.isLive = some true →
        (rf.ctx.get? z).map RcVar.isLive = some true)) ∧
      (∀ p ∈ ctx'.sharedPreds, p.1 ≠ x → p ∈ rf.ctx.sharedPreds ∧ p.2 ≠ x))
    (henv : ∀ z, z ≠ x → envP' z = rf.envP z ∧ envH' z = rf.envH z ∧ ρP' z = ρP z)
    (hjumps : ∀ jc ∈ jumps', jc ∈ jumps) :
    JpsOk rt rf0 σ0 Jp Jh (jpsOk.map (fun e => { e with mutVars := x :: e.mutVars }))
      { ctx := ctx', envP := envP', envH := envH', extH := rf.extH, ghostH := ghostH' }
      ρP' jumps' := by
  intro e' he'
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
  obtain ⟨hok, hlive, hw⟩ := hjps e he
  refine ⟨hok, ⟨fun id hid hnot hl => ?_, fun p hp h1 hnot => ?_⟩, fun jc hjc hjeq =>
      hw jc (hjumps jc hjc) hjeq⟩
  · have hne : id ≠ x := fun hx => hnot (hx ▸ List.mem_cons_self)
    have hnot' : id ∉ e.mutVars := fun hm => hnot (List.mem_cons_of_mem _ hm)
    obtain ⟨heP, heH, hrP, hty, hl0⟩ := hlive.1 id hid hnot' ((hstep.1 id hne).2 hl)
    obtain ⟨hnP, hnH, hnR⟩ := henv id hne
    exact ⟨hnP.trans heP, hnH.trans heH, hnR.trans hrP,
      (hstep.1 id hne).1.trans hty, hl0⟩
  · have hne1 : p.1 ≠ x := fun hx => hnot (hx ▸ List.mem_cons_self)
    have hnot' : p.1 ∉ e.mutVars := fun hm => hnot (List.mem_cons_of_mem _ hm)
    obtain ⟨hpm, hne2⟩ := hstep.2 p hp hne1
    obtain ⟨hp0, heH, hty⟩ := hlive.2 p hpm h1 hnot'
    obtain ⟨_, hnH2, _⟩ := henv p.2 hne2
    exact ⟨hp0, hnH2.trans heH, (hstep.1 p.2 hne2).1.trans hty⟩

public theorem bindAllP_of_not_mem (ps : List LcParam) (ρ : PValEnv) (vs : List PVal)
    {z : Nat} (hnot : ∀ p ∈ ps, p.id ≠ z) : (ρ.bindAll ps vs) z = ρ z := by
  induction ps generalizing ρ vs with
  | nil => cases vs <;> simp [PValEnv.bindAll]
  | cons q rest ih =>
    cases vs with
    | nil => simp [PValEnv.bindAll]
    | cons v restv =>
      rw [PValEnv.bindAll.eq_1]
      have h1 : (ρ.set q.id v) z = ρ z := by
        simp [PValEnv.set, (hnot q List.mem_cons_self).symm]
      rw [ih _ _ (fun p hp => hnot p (List.mem_cons_of_mem _ hp)), h1]

public theorem bindAllH_of_not_mem (ps : List LcParam) (ρ : HValEnv) (ws : List Word)
    {z : Nat} (hnot : ∀ p ∈ ps, p.id ≠ z) : (ρ.bindAll ps ws) z = ρ z := by
  induction ps generalizing ρ ws with
  | nil => cases ws <;> simp [HValEnv.bindAll]
  | cons q rest ih =>
    cases ws with
    | nil => simp [HValEnv.bindAll]
    | cons w restw =>
      rw [HValEnv.bindAll.eq_1]
      have h1 : (ρ.set q.id q.ty w) z = ρ z := by
        simp [HValEnv.set, (hnot q List.mem_cons_self).symm]
      rw [ih _ _ (fun p hp => hnot p (List.mem_cons_of_mem _ hp)), h1]

/-- `JpsOk` is preserved when entering an inner `jp` body (`baseCtx.bindParams ps`). -/
public theorem jpsOk_enter_body {env : RcModEnv} {retTy : LcTy} {rt : BitVec 64}
    {rf0 : RcFrame} {σ0 : HState} {Jp : PResJEnv} {Jh : HJEnv} {jpsOk : List JpEntry}
    {rf : RcFrame} {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv}
    {j : Nat} {ps : List LcParam} {body k : LcCode}
    {jumpsK jumpsBody : List (Nat × RcCtx)} {optC : Option RcCtx}
    {Jh_j : List Word → HState → Prop}
    {pvs : List PVal} {ws : List Word} {ghostH' : List (BitVec 64)}
    (hs : CtxStaticInv rf.ctx) (hjpsScope : JpsScopeIn (jpsOk.map JpEntry.info) rf.ctx)
    (hK : checkCode env retTy
      ({ id := j, params := ps, scopeIds := rf.ctx.vars.map (·.id) } :: jpsOk.map JpEntry.info)
      rf.ctx k = Except.ok jumpsK)
    (hm : mergeJpList ((jumpsK.filter (·.1 == j)).map Prod.snd) = Except.ok optC)
    (hwf : perceusCodeWf env retTy (jpsOk.map JpEntry.info) rf.ctx sm
      (LcCode.jp j ps body k) = true)
    (hnotJ : ∀ e ∈ jpsOk, e.info.id ≠ j)
    (hjps : JpsOk rt rf0 σ0 Jp Jh jpsOk rf ρP (jumpsK.filter (·.1 != j) ++ jumpsBody)) :
    let baseCtx := optC.getD rf.ctx
    JpsOk rt rf0 σ0 Jp (Jh.set j Jh_j)
      (jpsOk.map (fun e => { e with mutVars := ps.map (·.id) ++ e.mutVars }))
      { ctx := baseCtx.bindParams ps, envP := rf.envP.bindAll ps pvs,
        envH := rf.envH.bindAll ps ws, extH := rf.extH, ghostH := ghostH' }
      (ρP.bindAll ps pvs) jumpsBody := by
  have hwf' := hwf
  rw [perceusCodeWf.eq_3] at hwf'; dsimp only at hwf'
  have ha1 := Bool.and_eq_true _ _ |>.mp hwf'
  have ha2 := Bool.and_eq_true _ _ |>.mp ha1.1
  have ha3 := Bool.and_eq_true _ _ |>.mp ha2.1
  have ha4 := Bool.and_eq_true _ _ |>.mp ha3.1
  have ha5 := Bool.and_eq_true _ _ |>.mp ha4.1
  obtain ⟨hsB, _, _, _, _⟩ := jpBaseCtx_static_invs hs hjpsScope hK hm hwf
  have hbase_eq : jpBaseCtx env retTy (jpsOk.map JpEntry.info) rf.ctx j ps k = optC.getD rf.ctx :=
    jpBaseCtx_eq_of_check hK hm
  have hfrB : ps.all (binderFreshOwned (optC.getD rf.ctx) ·.id) = true := by
    simpa [hbase_eq] using ha5.2
  have hba := jpBaseCtx_static_agree hs hjpsScope hK hm hwf
  intro baseCtx e' he'
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
  obtain ⟨hok, hlive, hw⟩ := hjps e he
  have hneJ := hnotJ e he
  have hok' : JpEntryOk rt rf0 σ0 Jp (Jh.set j Jh_j)
      { e with mutVars := ps.map (·.id) ++ e.mutVars } := by
    refine ⟨hok.1, hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1, hok.2.2.2.2.2.1,
      hok.2.2.2.2.2.2.1, fun pvs' rem wr rcr hjp hpb => ?_⟩
    simp only [HJEnv.set, hneJ, ↓reduceIte]
    exact hok.2.2.2.2.2.2.2 pvs' rem wr rcr hjp hpb
  have hagree_in : StaticAgree
      ((baseCtxLiveIds e.baseCtx).filter (fun id => !e.mutVars.contains id)) e.ctxJp rf.ctx := by
    refine ⟨fun id hid hl => ?_, fun p hp hp1 => ?_⟩
    · have h1 := List.mem_filter.mp hid
      have hnot : id ∉ e.mutVars := fun hm =>
        absurd (List.contains_iff_mem.mpr hm) (by simpa using h1.2)
      obtain ⟨_, _, _, hty, hl0⟩ := hlive.1 id h1.1 hnot hl
      exact ⟨hl0, hty.symm⟩
    · have h1 := List.mem_filter.mp hp1
      have hnot : p.1 ∉ e.mutVars := fun hm =>
        absurd (List.contains_iff_mem.mpr hm) (by simpa using h1.2)
      obtain ⟨hp0, _, hty⟩ := hlive.2 p hp h1.1 hnot
      exact ⟨hp0, hty.symm⟩
  have hagree_out := inner_jp_body_agree hs hjpsScope hK hm hwf hagree_in
  have hlive' : JpEntryLiveAgree { e with mutVars := ps.map (·.id) ++ e.mutVars }
      { ctx := baseCtx.bindParams ps, envP := rf.envP.bindAll ps pvs,
        envH := rf.envH.bindAll ps ws, extH := rf.extH, ghostH := ghostH' }
      (ρP.bindAll ps pvs) := by
    refine ⟨fun id hid hnot hl => ?_, fun p hp hp1 hnot => ?_⟩
    · have hnotP : ∀ p ∈ ps, p.id ≠ id := fun p hp heq =>
        hnot (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨p, hp, heq⟩)))
      have hnotM : id ∉ e.mutVars := fun hm => hnot (List.mem_append.mpr (Or.inr hm))
      have hidF : id ∈ (baseCtxLiveIds e.baseCtx).filter
          (fun z => !(ps.map (·.id) ++ e.mutVars).contains z) := by
        refine List.mem_filter.mpr ⟨hid, ?_⟩
        cases hc : (ps.map (·.id) ++ e.mutVars).contains id
        · rfl
        · exfalso; exact hnot (List.contains_iff_mem.mp hc)
      obtain ⟨hl0, hty0⟩ := hagree_out.1 id hidF hl
      have hl_base : (baseCtx.get? id).map RcVar.isLive = some true := by
        rw [← bindParams_get?_of_not_mem hsB.1 ps hnotP]; exact hl
      have hidB : id ∈ baseCtxLiveIds baseCtx := by
        cases hgB : baseCtx.get? id with
        | none => simp [hgB] at hl_base
        | some vb =>
          have hvb_live : vb.isLive = true := by simpa [hgB] using hl_base
          have hmem := RcCtx.get?_mem hgB
          exact List.mem_map.mpr ⟨vb, List.mem_filter.mpr ⟨hmem.1, hvb_live⟩, hmem.2⟩
      have hl_rf : (rf.ctx.get? id).map RcVar.isLive = some true := (hba.1 id hidB hl_base).1
      obtain ⟨heP, heH, hrP, _, _⟩ := hlive.1 id hid hnotM hl_rf
      exact ⟨(bindAllP_of_not_mem ps rf.envP pvs hnotP).trans heP,
        (bindAllH_of_not_mem ps rf.envH ws hnotP).trans heH,
        (bindAllP_of_not_mem ps ρP pvs hnotP).trans hrP, hty0.symm, hl0⟩
    · have hnotM : p.1 ∉ e.mutVars := fun hm => hnot (List.mem_append.mpr (Or.inr hm))
      have hpB : p ∈ baseCtx.sharedPreds := by rwa [bindParams_sharedPreds] at hp
      have hnotP2 : ∀ q ∈ ps, q.id ≠ p.2 := fun q hq heq =>
        (binderFreshOwned_sharedPreds (List.all_eq_true.mp hfrB q hq) hpB).2 heq.symm
      have hp1F : p.1 ∈ (baseCtxLiveIds e.baseCtx).filter
          (fun z => !(ps.map (·.id) ++ e.mutVars).contains z) := by
        refine List.mem_filter.mpr ⟨hp1, ?_⟩
        cases hc : (ps.map (·.id) ++ e.mutVars).contains p.1
        · rfl
        · exfalso; exact hnot (List.contains_iff_mem.mp hc)
      obtain ⟨vb, hgB, hnoRc⟩ := hsB.2.2.1 p hpB
      have hvb_live : vb.isLive = true := by simp [RcVar.isLive, hnoRc]
      have hmem := RcCtx.get?_mem hgB
      have hp1B : p.1 ∈ baseCtxLiveIds baseCtx :=
        List.mem_map.mpr ⟨vb, List.mem_filter.mpr ⟨hmem.1, hvb_live⟩, hmem.2⟩
      have hp_rf : p ∈ rf.ctx.sharedPreds := (hba.2 p hpB hp1B).1
      obtain ⟨hp0, heH, _⟩ := hlive.2 p hp_rf hp1 hnotM
      have hty0 := (hagree_out.2 p hp hp1F).2
      exact ⟨hp0, (bindAllH_of_not_mem ps rf.envH ws hnotP2).trans heH, hty0.symm⟩
  exact ⟨hok', hlive', fun jc hjc hjeq => hw jc (List.mem_append.mpr (Or.inr hjc)) hjeq⟩

end JpsOkDefs

section JmpFrame

private theorem nodup_put_mem_of_get? {ctx : RcCtx}
    {x : Nat} {v : RcVar} (hg : ctx.get? x = some v) : v ∈ ctx.vars ∧ v.id = x :=
  RcCtx.get?_mem hg

private theorem varHandles_bindParam_eq (envH : HValEnv) (p : LcParam) (w : Word) :
    varHandles (envH.set p.id p.ty w)
      (if p.borrow = true then
        { id := p.id, ty := p.ty, noRc := !p.ty.needsRc,
          persistent := false, borrowed := !(!p.ty.needsRc) && true, parent? := none }
      else
        { id := p.id, ty := p.ty, noRc := !p.ty.needsRc, persistent := false,
          owned := if ((!p.ty.needsRc) || false) = true then 0 else 1,
          excl := false, resetTok := false }) =
      entryParamHandles p w := by
  by_cases hbr : p.borrow = true
  · by_cases hnr : p.ty.needsRc = true <;>
      simp [varHandles, entryParamHandles, hbr, hnr]
  · by_cases hnr : p.ty.needsRc = true
    · simp [varHandles, entryParamHandles, HValEnv.set, hbr, hnr]
      cases hw : w.toBV64? with
      | none => simp
      | some bv => by_cases hev : (bv &&& 1#64 == 0#64) = true <;> simp
    · simp [varHandles, entryParamHandles, hbr, hnr]

public theorem localHandles_bindParams_perm_fresh (ps : List LcParam) (ws : List Word)
    (hlen : ws.length = ps.length) (hndP : (ps.map (·.id)).Nodup)
    (ctx : RcCtx) (envH : HValEnv) (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hfr : ps.all (binderFreshOwned ctx ·.id) = true) :
    (localHandles (ctx.bindParams ps) (envH.bindAll ps ws)).Perm
      (localHandles ctx envH ++
        (ps.zip ws |>.map fun (p, w) => entryParamHandles p w).flatten) := by
  induction ps generalizing ws ctx envH with
  | nil =>
    cases ws with
    | nil => simp [RcCtx.bindParams, HValEnv.bindAll]
    | cons => simp at hlen
  | cons p rest ih =>
    cases ws with
    | nil => simp at hlen
    | cons w ws' =>
      have hlen' : ws'.length = rest.length := by simpa using hlen
      have hndP' : (rest.map (·.id)).Nodup := by
        simp only [List.map_cons, List.nodup_cons] at hndP; exact hndP.2
      have hp_not : p.id ∉ rest.map (·.id) := by
        simp only [List.map_cons, List.nodup_cons] at hndP; exact hndP.1
      have hfr_p : binderFreshOwned ctx p.id = true :=
        (List.all_eq_true.mp hfr) p List.mem_cons_self
      let vp : RcVar :=
        if p.borrow = true then
          { id := p.id, ty := p.ty, noRc := !p.ty.needsRc,
            persistent := false, borrowed := !(!p.ty.needsRc) && true, parent? := none }
        else
          { id := p.id, ty := p.ty, noRc := !p.ty.needsRc, persistent := false,
            owned := if ((!p.ty.needsRc) || false) = true then 0 else 1,
            excl := false, resetTok := false }
      have hctx_step : (if p.borrow = true then ctx.bindBorrowed p.id p.ty
          else ctx.bindOwned p.id p.ty) = ctx.put vp := by
        by_cases hbr : p.borrow = true <;>
          simp [vp, RcCtx.bindBorrowed, RcCtx.bindOwned, hbr]
      have hvp_id : vp.id = p.id := by by_cases hbr : p.borrow = true <;> simp [vp, hbr]
      have hvp_par : vp.parent? = none := by by_cases hbr : p.borrow = true <;> simp [vp, hbr]
      have hnd1 : ((ctx.put vp).vars.map RcVar.id).Nodup := RcCtx.put_nodup hnd vp
      have hfr1 : rest.all (binderFreshOwned (ctx.put vp) ·.id) = true := by
        refine List.all_eq_true.mpr fun q hq => ?_
        have hne : q.id ≠ vp.id := by
          rw [hvp_id]; intro heq; exact hp_not (heq ▸ List.mem_map.mpr ⟨q, hq, rfl⟩)
        exact binderFreshOwned_put_none hnd hvp_par hne
          ((List.all_eq_true.mp hfr) q (List.mem_cons_of_mem _ hq))
      have hih := ih ws' hlen' hndP' (ctx.put vp) (envH.set p.id p.ty w) hnd1 hfr1
      have hput : (localHandles (ctx.put vp) (envH.set p.id p.ty w)).Perm
          (varHandles (envH.set p.id p.ty w) vp ++
            localHandlesExcept ctx (envH.set p.id p.ty w) vp.id) :=
        localHandles_put_perm hnd (envH.set p.id p.ty w) vp
      have hcongr : localHandlesExcept ctx (envH.set p.id p.ty w) vp.id =
          localHandlesExcept ctx envH vp.id :=
        localHandlesExcept_congr_env vp.id fun y hne => by
          have hne' : y ≠ p.id := by simpa [hvp_id] using hne
          simp [HValEnv.set, hne']
      have hfr_perm : (localHandlesExcept ctx envH vp.id).Perm (localHandles ctx envH) := by
        rw [hvp_id]; exact localHandlesExcept_fresh_perm hnd hfr_p
      have hvh : varHandles (envH.set p.id p.ty w) vp = entryParamHandles p w :=
        varHandles_bindParam_eq envH p w
      have hstep_perm : (localHandles (ctx.put vp) (envH.set p.id p.ty w)).Perm
          (localHandles ctx envH ++ entryParamHandles p w) := by
        refine hput.trans ?_
        rw [hcongr, hvh]
        exact (List.Perm.append_left _ hfr_perm).trans List.perm_append_comm
      rw [RcCtx.bindParams.eq_1] at hih ⊢
      simp only [List.foldl_cons, hctx_step]
      rw [HValEnv.bindAll.eq_1]
      refine hih.trans ?_
      simp only [List.zip_cons_cons, List.map_cons, List.flatten_cons]
      exact (List.Perm.append_right _ hstep_perm).trans (by
        simp only [List.append_assoc]; exact List.Perm.refl _)

public theorem count_flatten_map_le_of_inj {α β : Type} [DecidableEq α]
    (l1 l2 : List β) (idFn : β → Nat) (f1 f2 : β → List α)
    (hnd1 : (l1.map idFn).Nodup)
    (hsub : ∀ w ∈ l1, f1 w = [] ∨ ∃ v ∈ l2, idFn v = idFn w ∧ f1 w = f2 v) (a : α) :
    List.count a (l1.map f1).flatten ≤ List.count a (l2.map f2).flatten := by
  induction l1 generalizing l2 with
  | nil => simp
  | cons w rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.flatten_cons, List.count_append] at hnd1 ⊢
    rcases hsub w List.mem_cons_self with hnil | ⟨v, hv, hid, hfeq⟩
    · rw [hnil]; simp only [List.count_nil, Nat.zero_add]
      exact ih l2 hnd1.2 (fun u hu => hsub u (List.mem_cons_of_mem _ hu))
    · obtain ⟨l2a, l2b, rfl⟩ := List.append_of_mem hv
      have hsub' : ∀ u ∈ rest,
          f1 u = [] ∨ ∃ v' ∈ l2a ++ l2b, idFn v' = idFn u ∧ f1 u = f2 v' := by
        intro u hu
        rcases hsub u (List.mem_cons_of_mem _ hu) with hu0 | ⟨v', hv', hid', hf'⟩
        · exact Or.inl hu0
        · refine Or.inr ⟨v', ?_, hid', hf'⟩
          rcases List.mem_append.mp hv' with h1 | h2
          · exact List.mem_append.mpr (Or.inl h1)
          · rcases List.mem_cons.mp h2 with rfl | h3
            · exfalso; exact hnd1.1 (by rw [← hid, hid']; exact List.mem_map.mpr ⟨u, hu, rfl⟩)
            · exact List.mem_append.mpr (Or.inr h3)
      have ih_res := ih (l2a ++ l2b) hnd1.2 hsub'
      simp only [List.map_append, List.map_cons, List.flatten_append, List.flatten_cons,
        List.count_append] at ih_res ⊢
      rw [hfeq]
      omega

public theorem valRep_nonRc_odd {ty : LcTy} {pv : PVal} {w : Word} {objs : List LcnfObj}
    (hns : ¬ty.isScalar = true) (hrep : ValRep ty pv w objs) :
    ∃ bv, w = Word.i64 bv := by
  simp [ValRep, hns] at hrep
  obtain ⟨bv, hw, _⟩ := hrep; exact ⟨bv, hw⟩

public theorem valRep_fst_eq {ty : LcTy} {pv : PVal} {w : Word} {objs : List LcnfObj}
    (hrep : ValRep ty pv w objs) : w.fst = ty.toTTy := by
  by_cases hsc : ty.isScalar = true
  · simp only [ValRep, hsc, ↓reduceIte, ScalarRep] at hrep
    rcases hrep with ⟨bv, _, hw⟩ | ⟨cidx, _, _, hw⟩ | ⟨_, hw⟩ <;>
      simp [hw, LcTy.toTTy]
  · obtain ⟨bv, hw⟩ := valRep_nonRc_odd hsc hrep
    subst hw
    cases ty <;> simp [LcTy.isScalar, LcTy.toTTy, LcTy.width, Word.i64] at hsc ⊢

private theorem applyArgsHandles_entryParamHandles_count_le {rt : BitVec 64}
    {rf : RcFrame} {σ : HState} (hinv : RcInv rt rf σ)
    (ps : List LcParam) (as : List LcArg) (pvs : List PVal) (ws : List Word)
    (hmatch : argsMatchTys rf.ctx as (ps.map (·.ty)) = true)
    (hpvs : rf.envP.evalArgs as = some pvs) (hws : rf.envH.evalArgsOwn as = some ws)
    (hlive : ∀ a ∈ as, a = LcArg.erased ∨ ∃ z v, a = LcArg.var z ∧
      rf.ctx.get? z = some v ∧ v.isLive = true)
    {addr : BitVec 64}
    (hnp : ∀ v ∈ rf.ctx.vars, v.isLive = true → v.persistent = true →
      ∀ w, rf.envH v.id = some (v.ty, w) → w.toBV64? ≠ some addr) :
    List.count addr (ps.zip ws |>.map fun (p, w) => entryParamHandles p w).flatten ≤
      List.count addr (applyArgsHandles rf as (ps.map (·.borrow))) := by
  induction ps generalizing as pvs ws with
  | nil =>
    cases as with
    | nil => cases ws <;> simp [HValEnv.evalArgsOwn] at hws ⊢
    | cons => simp [argsMatchTys] at hmatch
  | cons p rest ih =>
    cases as with
    | nil => simp [argsMatchTys] at hmatch
    | cons a as' =>
      have hmatch' := hmatch
      simp only [argsMatchTys, List.map_cons, List.length_cons, List.length_map, beq_iff_eq,
        Nat.succ.injEq, List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hmatch'
      obtain ⟨hlen, hm1, hm_rest⟩ := hmatch'
      have hmt_rest : argsMatchTys rf.ctx as' (rest.map (·.ty)) = true := by
        simpa [argsMatchTys, hlen] using hm_rest
      rw [PValEnv.evalArgs.eq_2] at hpvs
      cases hpa : rf.envP.evalArg a with
      | none => simp [hpa] at hpvs
      | some pv0 =>
        cases hpas : rf.envP.evalArgs as' with
        | none => simp [hpa, hpas] at hpvs
        | some pvs0 =>
          simp only [hpa, hpas, Option.some.injEq] at hpvs
          cases hpvs
          rw [HValEnv.evalArgsOwn.eq_2] at hws
          cases hwa : rf.envH.evalArgOwn a with
          | none => simp [hwa] at hws
          | some w0 =>
            cases hwas : rf.envH.evalArgsOwn as' with
            | none => simp [hwa, hwas] at hws
            | some ws0 =>
              simp only [hwa, hwas, Option.some.injEq] at hws
              cases hws
              have htail := ih as' pvs0 ws0 hmt_rest hpas hwas
                (fun b hb => hlive b (List.mem_cons_of_mem _ hb))
              simp only [List.zip_cons_cons, List.map_cons, List.flatten_cons,
                List.count_append]
              by_cases hbr : p.borrow = true
              · cases a with
                | erased =>
                  rw [applyArgsHandles.eq_2]
                  simp only [hbr, ↓reduceIte, entryParamHandles, Bool.true_or, List.count_nil,
                    Nat.zero_add]
                  exact htail
                | var id =>
                  rw [applyArgsHandles.eq_3]
                  simp only [hbr, ↓reduceIte, entryParamHandles, Bool.true_or, List.count_nil,
                    Nat.zero_add]
                  exact htail
              · have hhead : List.count addr (entryParamHandles p w0) ≤
                    List.count addr (match a with
                      | LcArg.erased => []
                      | LcArg.var id => consumeVarHandles rf id 1) := by
                  by_cases hnr : p.ty.needsRc = true
                  · cases a with
                    | erased =>
                      simp only [HValEnv.evalArgOwn, Option.some.injEq] at hwa
                      cases hwa
                      simp [entryParamHandles, Word.toBV64?, Word.i64]
                    | var z =>
                      rcases hlive (LcArg.var z) List.mem_cons_self with
                        h0 | ⟨z', vz, heqz, hgz, hlivez⟩
                      · cases h0
                      · cases heqz
                        have hmemz := RcCtx.get?_mem hgz
                        obtain ⟨pvv, wv, hPv, hHv, hvr, hrest⟩ := hinv.2.2.2.1 vz hmemz.1 hlivez
                        simp only [HValEnv.evalArgOwn] at hwa
                        rw [← hmemz.2, hHv, Option.map_some, Option.some.injEq] at hwa
                        cases hwa
                        have hm1' := hm1
                        simp only [hgz, Bool.and_eq_true] at hm1'
                        have hty_sc : vz.ty.isScalar = p.ty.isScalar := by
                          simpa [beq_iff_eq] using hm1'.1.1.1.1
                        have hnp_sc : p.ty.isScalar = false := by
                          have h1 : ∀ t : LcTy, t.needsRc = true → t.isScalar = false := fun t => by
                            cases t <;> simp [LcTy.needsRc, LcTy.isScalar]
                          exact h1 p.ty hnr
                        have hzv_nsc : ¬vz.ty.isScalar = true := by simp [hty_sc, hnp_sc]
                        obtain ⟨bv, hwbv, hno, hps, _⟩ := hrest hzv_nsc
                        subst hwbv
                        by_cases hvno : vz.noRc = true
                        · have hodd := hno hvno
                          simp [entryParamHandles, Word.toBV64?, Word.i64, hodd]
                        · have hvnoF : vz.noRc = false := Bool.eq_false_iff.mpr hvno
                          by_cases hvps : vz.persistent = true
                          · have hne : (Word.i64 bv).toBV64? ≠ some addr :=
                              hnp vz hmemz.1 hlivez hvps _ (hmemz.2 ▸ hHv)
                            have hne' : bv ≠ addr :=
                              fun h => hne (by simp [Word.toBV64?, Word.i64, h])
                            simp [entryParamHandles, Word.toBV64?, Word.i64, hbr, hnr]
                            by_cases h0 : bv &&& 1#64 = 0#64 <;>
                              simp [h0, hne']
                          · have hvpsF : vz.persistent = false := Bool.eq_false_iff.mpr hvps
                            have hHz : rf.envH z = some (vz.ty, Word.i64 bv) := hmemz.2 ▸ hHv
                            simp [entryParamHandles, consumeVarHandles, hgz, hvnoF, hvpsF,
                              hbr, hnr, hHz, Word.toBV64?, Word.i64]
                  · simp [entryParamHandles, hnr]
                cases a with
                | erased =>
                  rw [applyArgsHandles.eq_2]
                  simp only [hbr, Bool.false_eq_true, ↓reduceIte, List.count_append]
                  exact Nat.add_le_add hhead htail
                | var id =>
                  rw [applyArgsHandles.eq_3]
                  simp only [hbr, Bool.false_eq_true, ↓reduceIte, List.count_append]
                  exact Nat.add_le_add hhead htail

public theorem perm_symm_mem {α : Type} {l1 l2 : List α} (h : l1.Perm l2) {a : α} :
    a ∈ l1 ↔ a ∈ l2 := h.mem_iff

public theorem nodup_of_perm_nodup {α : Type} {l1 l2 : List α} (hp : l1.Perm l2)
    (hnd : l1.Nodup) : l2.Nodup := hp.nodup_iff.mp hnd

public theorem baseCtx_vars_of_mem_nodup {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    {v : RcVar} (hv : v ∈ ctx.vars) : ctx.get? v.id = some v :=
  (RcCtx.mem_get?_iff hnd).mpr hv

public theorem vars_mem_of_id_live {ctx : RcCtx}
    {id : Nat} (hg : (ctx.get? id).map RcVar.isLive = some true) :
    ∃ v, ctx.get? id = some v ∧ v ∈ ctx.vars ∧ v.id = id ∧ v.isLive = true := by
  cases h : ctx.get? id with
  | none => simp [h] at hg
  | some v =>
    have hl : v.isLive = true := by simpa [h] using hg
    have hm := RcCtx.get?_mem h
    exact ⟨v, rfl, hm.1, hm.2, hl⟩

public theorem restrict_mem_iff {ctx : RcCtx} {scopeIds : List Nat} {v : RcVar} :
    v ∈ (ctx.restrict scopeIds).vars ↔ v ∈ ctx.vars ∧ scopeIds.contains v.id = true := by
  simp [RcCtx.restrict, List.mem_filter]

public theorem bindParams_nodup {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (ps : List LcParam) : ((ctx.bindParams ps).vars.map RcVar.id).Nodup := by
  induction ps generalizing ctx with
  | nil => simpa [RcCtx.bindParams] using hnd
  | cons p rest ih =>
    rw [RcCtx.bindParams.eq_1, List.foldl_cons]
    refine ih ?_
    by_cases hbr : p.borrow = true
    · simp only [hbr, ↓reduceIte, RcCtx.bindBorrowed]
      exact RcCtx.put_nodup hnd _
    · simp only [hbr, Bool.false_eq_true, ↓reduceIte, RcCtx.bindOwned]
      exact RcCtx.put_nodup hnd _

public theorem bindParams_noRcCorrect {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hnorc : NoRcCorrect ctx) (ps : List LcParam) : NoRcCorrect (ctx.bindParams ps) := by
  induction ps generalizing ctx with
  | nil => simpa [RcCtx.bindParams] using hnorc
  | cons p rest ih =>
    rw [RcCtx.bindParams.eq_1, List.foldl_cons]
    by_cases hbr : p.borrow = true
    · simp only [hbr, ↓reduceIte, RcCtx.bindBorrowed]
      refine ih (RcCtx.put_nodup hnd _) (noRcCorrect_put hnd hnorc fun h => by simpa using h)
    · simp only [hbr, Bool.false_eq_true, ↓reduceIte, RcCtx.bindOwned]
      refine ih (RcCtx.put_nodup hnd _) (noRcCorrect_put hnd hnorc fun h => by simpa using h)

public theorem bindParams_mem_cases {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    {ps : List LcParam} (hndP : (ps.map (·.id)).Nodup)
    {v : RcVar} (hv : v ∈ (ctx.bindParams ps).vars) :
    (v ∈ ctx.vars ∧ ∀ p ∈ ps, p.id ≠ v.id) ∨
      ∃ p ∈ ps, v.id = p.id ∧
        v = (if p.borrow = true then
          { id := p.id, ty := p.ty, noRc := !p.ty.needsRc,
            persistent := false, borrowed := !(!p.ty.needsRc) && true, parent? := none }
        else
          { id := p.id, ty := p.ty, noRc := !p.ty.needsRc, persistent := false,
            owned := if ((!p.ty.needsRc) || false) = true then 0 else 1,
            excl := false, resetTok := false }) := by
  induction ps generalizing ctx with
  | nil =>
    simp only [RcCtx.bindParams, List.foldl_nil] at hv
    exact Or.inl ⟨hv, fun p hp => nomatch hp⟩
  | cons p rest ih =>
    rw [RcCtx.bindParams.eq_1, List.foldl_cons] at hv
    have hndP' : (rest.map (·.id)).Nodup := by
      simp only [List.map_cons, List.nodup_cons] at hndP; exact hndP.2
    let vp : RcVar :=
      if p.borrow = true then
        { id := p.id, ty := p.ty, noRc := !p.ty.needsRc,
          persistent := false, borrowed := !(!p.ty.needsRc) && true, parent? := none }
      else
        { id := p.id, ty := p.ty, noRc := !p.ty.needsRc, persistent := false,
          owned := if ((!p.ty.needsRc) || false) = true then 0 else 1,
          excl := false, resetTok := false }
    have hstep : (if p.borrow = true then ctx.bindBorrowed p.id p.ty
        else ctx.bindOwned p.id p.ty) = ctx.put vp := by
      by_cases hbr : p.borrow = true <;>
        simp [vp, RcCtx.bindBorrowed, RcCtx.bindOwned, hbr]
    have hvp_id : vp.id = p.id := by by_cases hbr : p.borrow = true <;> simp [vp, hbr]
    rw [hstep] at hv
    rcases ih (RcCtx.put_nodup hnd vp) hndP' hv with ⟨hmem, hnot⟩ | ⟨q, hq, hid, heq⟩
    · rcases (RcCtx.put_mem_iff hnd).mp hmem with rfl | ⟨hold, hne⟩
      · refine Or.inr ⟨p, List.mem_cons_self, hvp_id, rfl⟩
      · refine Or.inl ⟨hold, fun q hq => ?_⟩
        rcases List.mem_cons.mp hq with rfl | hqr
        · exact fun h => hne (by rw [← h, hvp_id])
        · exact hnot q hqr
    · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hid, heq⟩

public theorem bindAll_eval_at_param (ps : List LcParam) (as : List LcArg)
    (pvs : List PVal) (ws : List Word)
    (hndP : (ps.map (·.id)).Nodup)
    (hlen1 : pvs.length = ps.length) (hlen2 : ws.length = ps.length) (hlen3 : as.length = ps.length)
    (envP0 : PValEnv) (envH0 : HValEnv)
    (rf : RcFrame)
    (hmatch : argsMatchTys rf.ctx as (ps.map (·.ty)) = true)
    (hpvs : rf.envP.evalArgs as = some pvs) (hws : rf.envH.evalArgsOwn as = some ws)
    {p : LcParam} (hp : p ∈ ps) :
    ∃ a pv w,
      (p, a) ∈ ps.zip as ∧
      (envP0.bindAll ps pvs) p.id = some pv ∧
      (envH0.bindAll ps ws) p.id = some (p.ty, w) ∧
      rf.envP.evalArg a = some pv ∧
      rf.envH.evalArgOwn a = some w := by
  induction ps generalizing as pvs ws envP0 envH0 with
  | nil => cases hp
  | cons q rest ih =>
    cases as with
    | nil => simp at hlen3
    | cons a as' =>
      cases pvs with
      | nil => simp at hlen1
      | cons pv pvs' =>
        cases ws with
        | nil => simp at hlen2
        | cons w ws' =>
          have hndP' : (rest.map (·.id)).Nodup := by
            simp only [List.map_cons, List.nodup_cons] at hndP; exact hndP.2
          have hq_not : q.id ∉ rest.map (·.id) := by
            simp only [List.map_cons, List.nodup_cons] at hndP; exact hndP.1
          rw [PValEnv.evalArgs.eq_2] at hpvs
          cases hpa : rf.envP.evalArg a with
          | none => simp [hpa] at hpvs
          | some pv0 =>
            cases hpas : rf.envP.evalArgs as' with
            | none => simp [hpa, hpas] at hpvs
            | some pvs0 =>
              simp only [hpa, hpas, Option.some.injEq, List.cons.injEq] at hpvs
              obtain ⟨rfl, rfl⟩ := hpvs
              rw [HValEnv.evalArgsOwn.eq_2] at hws
              cases hwa : rf.envH.evalArgOwn a with
              | none => simp [hwa] at hws
              | some w0 =>
                cases hwas : rf.envH.evalArgsOwn as' with
                | none => simp [hwa, hwas] at hws
                | some ws0 =>
                  simp only [hwa, hwas, Option.some.injEq, List.cons.injEq] at hws
                  obtain ⟨rfl, rfl⟩ := hws
                  have hmatch' := hmatch
                  simp only [argsMatchTys, List.map_cons, List.length_cons, List.length_map,
                    beq_iff_eq, Nat.succ.injEq, List.zip_cons_cons, List.all_cons,
                    Bool.and_eq_true] at hmatch'
                  obtain ⟨hlen, _, hm_rest⟩ := hmatch'
                  have hmt_rest : argsMatchTys rf.ctx as' (rest.map (·.ty)) = true := by
                    simpa [argsMatchTys, hlen] using hm_rest
                  rw [PValEnv.bindAll.eq_1, HValEnv.bindAll.eq_1]
                  rcases List.mem_cons.mp hp with hp_eq | hmem
                  · subst hp_eq
                    have hnotP : ∀ r ∈ rest, r.id ≠ p.id := fun r hr heq =>
                      hq_not (heq ▸ List.mem_map.mpr ⟨r, hr, rfl⟩)
                    refine ⟨a, pv0, w0, List.mem_cons_self, ?_, ?_, hpa, hwa⟩
                    · rw [bindAllP_of_not_mem rest _ _ hnotP]; simp [PValEnv.set]
                    · rw [bindAllH_of_not_mem rest _ _ hnotP]; simp [HValEnv.set]
                  · obtain ⟨a', pv', w', ha_mem, hP', hH', hpa', hwa'⟩ :=
                      ih as' pvs0 ws0 hndP' (by simpa using hlen1) (by simpa using hlen2)
                        (by simpa using hlen3) (envP0.set q.id pv0) (envH0.set q.id q.ty w0)
                        hmt_rest hpas hwas hmem
                    exact ⟨a', pv', w', List.mem_cons_of_mem _ ha_mem, hP', hH', hpa', hwa'⟩

public theorem argsMatchTys_mem {ctx : RcCtx} {as : List LcArg} {ps : List LcParam}
    (hmatch : argsMatchTys ctx as (ps.map (·.ty)) = true) {p : LcParam} {a : LcArg}
    (hmem : (p, a) ∈ ps.zip as) :
    match a with
    | LcArg.erased =>
      (!p.ty.isScalar && p.ty != LcTy.object && p.ty != LcTy.tagged) = true
    | LcArg.var x =>
      match ctx.get? x with
      | some v =>
        (v.ty.isScalar == p.ty.isScalar && v.ty.width == p.ty.width &&
          decide ((p.ty == LcTy.object) = true → (v.ty == LcTy.object) = true) &&
          decide ((p.ty == LcTy.tagged) = true → (v.ty == LcTy.tagged) = true) &&
          (p.ty.isScalar ||
            if p.ty.needsRc = true then
              v.ty.needsRc || p.ty == LcTy.tobject && v.ty == LcTy.tagged
            else v.ty == LcTy.tagged || v.noRc)) = true
      | none => False := by
  simp only [argsMatchTys, Bool.and_eq_true, List.all_eq_true] at hmatch
  have ha_mem : (a, p.ty) ∈ as.zip (ps.map (·.ty)) := by
    clear hmatch
    induction ps generalizing as with
    | nil => cases hmem
    | cons q rest ih =>
      cases as with
      | nil => cases hmem
      | cons a0 as' =>
        rcases List.mem_cons.mp hmem with h0 | h1
        · cases h0; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih h1)
  have hall := hmatch.2 (a, p.ty) ha_mem
  cases a with
  | erased => exact hall
  | var x =>
    dsimp only at hall ⊢
    cases hg : ctx.get? x with
    | none => simp [hg] at hall
    | some v => simpa [hg] using hall

public theorem argsBorrowFromExt_mem {ctx1 : RcCtx} {as : List LcArg} {ps : List LcParam}
    (hb : argsBorrowFromExt ctx1 as (ps.map (·.borrow)) = true)
    {p : LcParam} {a : LcArg} (hmem : (p, a) ∈ ps.zip as) (hbr : p.borrow = true) :
    match a with
    | LcArg.erased => True
    | LcArg.var x =>
      match ctx1.get? x with
      | some v => (v.isLive && (v.noRc || v.persistent || v.borrowed && v.parent?.isNone)) = true
      | none => False := by
  simp only [argsBorrowFromExt, List.all_eq_true] at hb
  have hmem2 : (a, p.borrow) ∈ as.zip (ps.map (·.borrow)) := by
    clear hb
    induction ps generalizing as with
    | nil => cases hmem
    | cons q rest ih =>
      cases as with
      | nil => cases hmem
      | cons a0 as' =>
        rcases List.mem_cons.mp hmem with h0 | h1
        · cases h0; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih h1)
  have h1 := hb (a, p.borrow) hmem2
  simp only [hbr, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h1
  cases a with
  | erased => trivial
  | var x =>
    dsimp only at h1 ⊢
    cases hg : ctx1.get? x with
    | none => simp [hg] at h1
    | some v => simpa [hg] using h1

public theorem applyArgs_sharedPred_target_eq {ctx ctx1 : RcCtx}
    {as : List LcArg} {bs : List Bool}
    (hnd : (ctx.vars.map RcVar.id).Nodup) (hc : CleanVars ctx) (hpo : ParentsOwned ctx)
    (ha : ctx.applyArgs as bs = Except.ok ctx1)
    (hsh : argsNoSharedTarget ctx as bs = true)
    {p : Nat × Nat} (hp : p ∈ ctx1.sharedPreds) {vx1 : RcVar} (hg1 : ctx1.get? p.2 = some vx1) :
    ∃ vx, ctx.get? p.2 = some vx ∧ vx.owned = vx1.owned := by
  induction as generalizing bs ctx with
  | nil =>
    cases bs with
    | nil =>
      rw [RcCtx.applyArgs.eq_1] at ha
      cases ha; exact ⟨vx1, hg1, rfl⟩
    | cons =>
      rw [RcCtx.applyArgs.eq_3 _ _ _ (by intro _ h; cases h)
        (by intro _ _ _ _ h _; cases h)] at ha
      cases ha
  | cons a as' ih =>
    cases bs with
    | nil =>
      rw [RcCtx.applyArgs.eq_3 _ _ _ (by intro h _; cases h)
        (by intro _ _ _ _ _ h; cases h)] at ha
      cases ha
    | cons b bs' =>
      rw [RcCtx.applyArgs.eq_2] at ha
      have hsh' := hsh
      simp only [argsNoSharedTarget, List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hsh'
      by_cases hb : b = true
      · simp only [hb, ↓reduceIte] at ha
        obtain ⟨_, _, ha_tail⟩ := except_bind_ok ha
        have hsh_tail : argsNoSharedTarget ctx as' bs' = true := by
          simpa [argsNoSharedTarget] using hsh'.2
        exact ih hnd hc hpo ha_tail hsh_tail
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
        obtain ⟨ctx_s, hcons, ha_tail⟩ := except_bind_ok ha
        have hp_s : p ∈ ctx_s.sharedPreds := applyArgs_sharedPreds_sub ha_tail p hp
        have hnd_s : (ctx_s.vars.map RcVar.id).Nodup := by
          cases a with
          | erased => simp [RcCtx.consumeArg] at hcons; cases hcons; exact hnd
          | var z => exact consumeVar_nodup hnd hcons
        have hc_s : CleanVars ctx_s := by
          cases a with
          | erased => simp [RcCtx.consumeArg] at hcons; cases hcons; exact hc
          | var z => exact cleanVars_consumeVar hnd hc hcons
        have hpo_s : ParentsOwned ctx_s := by
          cases a with
          | erased => simp [RcCtx.consumeArg] at hcons; cases hcons; exact hpo
          | var z => exact parentsOwned_consumeVar hnd hc hpo hcons
        have hp_ctx : p ∈ ctx.sharedPreds := by
          cases a with
          | erased => simp [RcCtx.consumeArg] at hcons; cases hcons; exact hp_s
          | var z => exact consumeVar_sharedPreds_sub hcons p hp_s
        have hsh_tail : argsNoSharedTarget ctx_s as' bs' = true := by
          simp only [argsNoSharedTarget, List.all_eq_true] at hsh' ⊢
          intro ⟨a1, b1⟩ hmem1
          have h1 := hsh'.2 ⟨a1, b1⟩ hmem1
          by_cases hb1 : b1 = true
          · simp [hb1]
          · simp only [hb1, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
            cases a1 with
            | erased => trivial
            | var x1 =>
              exact List.all_eq_true.mpr fun ⟨fst, tgt⟩ hsp =>
                List.all_eq_true.mp h1 ⟨fst, tgt⟩ (by
                  cases a with
                  | erased => simp [RcCtx.consumeArg] at hcons; cases hcons; exact hsp
                  | var z => exact consumeVar_sharedPreds_sub hcons _ hsp)
        obtain ⟨vxs, hgs, how_eq⟩ := ih hnd_s hc_s hpo_s ha_tail hsh_tail
        cases a with
        | erased =>
          simp [RcCtx.consumeArg] at hcons; cases hcons
          exact ⟨vxs, hgs, how_eq⟩
        | var z =>
          simp only [RcCtx.consumeArg] at hcons
          have hne_tgt : p.2 ≠ z := by
            have h1 := hsh'.1
            simp only [hb, Bool.false_eq_true, ↓reduceIte, List.all_eq_true] at h1
            have h2 := h1 p hp_ctx
            simpa [bne_iff_ne] using h2
          simp only [RcCtx.consumeVar] at hcons
          cases hgz : ctx.get? z with
          | none => simp [hgz] at hcons
          | some vz =>
            simp only [hgz] at hcons
            by_cases hskip : (vz.noRc || vz.persistent) = true
            · simp [hskip] at hcons; cases hcons; exact ⟨vxs, hgs, how_eq⟩
            · have hnz : ((1 : Nat) == 0) = false := rfl
              simp only [hskip, Bool.false_eq_true, ↓reduceIte, hnz] at hcons
              split at hcons
              · simp at hcons
              · split at hcons
                · simp only [pure, Except.pure, Except.ok.injEq] at hcons
                  rw [← hcons] at hgs
                  have hmem_inv := RcCtx.get?_mem hgs
                  obtain ⟨w, hw_mem, hwid, _, _, _, hw_ow, _, _, _⟩ :=
                    invalidateChildren_live_back z hmem_inv.1
                  have hw_get := (RcCtx.mem_get?_iff (RcCtx.put_nodup hnd _)).mpr hw_mem
                  rw [← hwid, hmem_inv.2, RcCtx.put_get? hnd] at hw_get
                  have hne_vz : (p.2 == vz.id) = false := by
                    have hvid : vz.id = z := (RcCtx.get?_mem hgz).2
                    rw [hvid]; exact beq_false_of_ne hne_tgt
                  simp only [hne_vz, Bool.false_eq_true, ↓reduceIte] at hw_get
                  exact ⟨w, hw_get, hw_ow.symm.trans how_eq⟩
                · simp only [pure, Except.pure, Except.ok.injEq] at hcons
                  rw [← hcons, RcCtx.put_get? hnd] at hgs
                  have hne_vz : (p.2 == vz.id) = false := by
                    have hvid : vz.id = z := (RcCtx.get?_mem hgz).2
                    rw [hvid]; exact beq_false_of_ne hne_tgt
                  simp only [hne_vz, Bool.false_eq_true, ↓reduceIte] at hgs
                  exact ⟨vxs, hgs, how_eq⟩

public theorem applyArgs_excl_owned_eq {ctx ctx1 : RcCtx}
    {as : List LcArg} {bs : List Bool} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (ha : ctx.applyArgs as bs = Except.ok ctx1) {z : Nat} {v1 : RcVar}
    (hg1 : ctx1.get? z = some v1) (hexcl : v1.excl = true) :
    ∃ v, ctx.get? z = some v ∧ v.excl = true ∧ (v.owned ≤ 1 → v1.owned = v.owned) := by
  induction as generalizing bs ctx with
  | nil =>
    cases bs with
    | nil => rw [RcCtx.applyArgs.eq_1] at ha; cases ha; exact ⟨v1, hg1, hexcl, fun _ => rfl⟩
    | cons =>
      rw [RcCtx.applyArgs.eq_3 _ _ _ (by intro _ h; cases h)
        (by intro _ _ _ _ h _; cases h)] at ha
      cases ha
  | cons a as' ih =>
    cases bs with
    | nil =>
      rw [RcCtx.applyArgs.eq_3 _ _ _ (by intro h _; cases h)
        (by intro _ _ _ _ _ h; cases h)] at ha
      cases ha
    | cons b bs' =>
      rw [RcCtx.applyArgs.eq_2] at ha
      by_cases hb : b = true
      · simp only [hb, ↓reduceIte] at ha
        obtain ⟨_, _, ha_tail⟩ := except_bind_ok ha
        exact ih hnd ha_tail
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
        obtain ⟨ctx_s, hcons, ha_tail⟩ := except_bind_ok ha
        have hnd_s : (ctx_s.vars.map RcVar.id).Nodup := by
          cases a with
          | erased => simp [RcCtx.consumeArg] at hcons; cases hcons; exact hnd
          | var y => exact consumeVar_nodup hnd hcons
        obtain ⟨vs, hgs, hexcl_s, how_eq⟩ := ih hnd_s ha_tail
        cases a with
        | erased =>
          simp [RcCtx.consumeArg] at hcons; cases hcons
          exact ⟨vs, hgs, hexcl_s, how_eq⟩
        | var y =>
          simp only [RcCtx.consumeArg, RcCtx.consumeVar] at hcons
          cases hgy : ctx.get? y with
          | none => simp [hgy] at hcons
          | some vy =>
            simp only [hgy] at hcons
            by_cases hskip : (vy.noRc || vy.persistent) = true
            · simp [hskip] at hcons; cases hcons; exact ⟨vs, hgs, hexcl_s, how_eq⟩
            · have hnz : ((1 : Nat) == 0) = false := rfl
              simp only [hskip, Bool.false_eq_true, ↓reduceIte, hnz] at hcons
              split at hcons
              · simp at hcons
              · split at hcons
                · rename_i hinv
                  simp only [pure, Except.pure, Except.ok.injEq] at hcons
                  rw [← hcons] at hgs
                  have hmem_inv := RcCtx.get?_mem hgs
                  obtain ⟨w, hw_mem, hwid, _, _, _, hw_ow, hw_ex, _, _⟩ :=
                    invalidateChildren_live_back y hmem_inv.1
                  have hw_get := (RcCtx.mem_get?_iff (RcCtx.put_nodup hnd _)).mpr hw_mem
                  rw [← hwid, hmem_inv.2] at hw_get
                  by_cases hzy : z = y
                  · subst hzy; rw [RcCtx.put_get? hnd] at hw_get
                    have hvyid : z = vy.id := (RcCtx.get?_mem hgy).2.symm
                    simp only [hvyid, beq_self_eq_true, ↓reduceIte] at hw_get
                    cases hw_get
                    exfalso
                    have hzero : (vy.owned - 1 == 0) = true := (Bool.and_eq_true _ _ |>.mp hinv).1
                    simp [hzero, hexcl_s] at hw_ex
                  · rw [RcCtx.put_get? hnd] at hw_get
                    have hne_vy : (z == vy.id) = false := by
                      have hvid : vy.id = y := (RcCtx.get?_mem hgy).2
                      rw [hvid]; exact beq_false_of_ne hzy
                    simp only [hne_vy, Bool.false_eq_true, ↓reduceIte] at hw_get
                    exact ⟨w, hw_get, hw_ex.symm.trans hexcl_s,
                      fun hle => (how_eq (hw_ow ▸ hle)).trans hw_ow⟩
                · simp only [pure, Except.pure, Except.ok.injEq] at hcons
                  rw [← hcons, RcCtx.put_get? hnd] at hgs
                  by_cases hzy : z = y
                  · subst hzy
                    have hvyid : z = vy.id := (RcCtx.get?_mem hgy).2.symm
                    simp only [hvyid, beq_self_eq_true, ↓reduceIte] at hgs; cases hgs
                    by_cases hzero : (vy.owned - 1 == 0) = true
                    · simp [hzero] at hexcl_s
                    · exact ⟨vy, hgy, by simpa [hzero] using hexcl_s,
                        fun hle => by
                          exfalso
                          have hne0 : vy.owned - 1 ≠ 0 := fun h => hzero (beq_iff_eq.mpr h)
                          omega⟩
                  · have hne_vy : (z == vy.id) = false := by
                      have hvid : vy.id = y := (RcCtx.get?_mem hgy).2
                      rw [hvid]; exact beq_false_of_ne hzy
                    simp only [hne_vy, Bool.false_eq_true, ↓reduceIte] at hgs
                    exact ⟨vs, hgs, hexcl_s, how_eq⟩

public theorem nonPersistReach_root_mem {objs : List LcnfObj} {r a : BitVec 64}
    (h : NonPersistReach objs r a) :
    ∃ o, o ∈ objs ∧ o.addr = r ∧ o.rc ≠ 0#32 := by
  induction h with
  | refl h0 => exact h0
  | step _ _ _ _ ih => exact ih

private theorem nodup_count_eq_one {α : Type} [DecidableEq α] {l : List α}
    (hnd : l.Nodup) {a : α} (hm : a ∈ l) : List.count a l = 1 := by
  induction l with
  | nil => cases hm
  | cons x xs ih =>
    simp only [List.nodup_cons] at hnd
    rcases List.mem_cons.mp hm with rfl | hx
    · simp [List.count_eq_zero_of_not_mem hnd.1]
    · have hne : x ≠ a := fun h => hnd.1 (h ▸ hx)
      simp [hne, ih hnd.2 hx]

public theorem perm_of_nodup_mem {α : Type} [DecidableEq α] {l1 l2 : List α}
    (h1 : l1.Nodup) (h2 : l2.Nodup) (hiff : ∀ a, a ∈ l1 ↔ a ∈ l2) : l1.Perm l2 := by
  refine List.perm_iff_count.mpr fun a => ?_
  by_cases ha : a ∈ l1
  · have ha2 : a ∈ l2 := (hiff a).mp ha
    rw [nodup_count_eq_one h1 ha, nodup_count_eq_one h2 ha2]
  · have ha2 : a ∉ l2 := fun h => ha ((hiff a).mpr h)
    rw [List.count_eq_zero_of_not_mem ha, List.count_eq_zero_of_not_mem ha2]

public theorem sharedBool_applyArgs {ctx ctx1 : RcCtx} {as : List LcArg} {bs : List Bool}
    (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hsbv : SharedBoolVars ctx) (hsbp : SharedBoolPreds ctx)
    (ha : ctx.applyArgs as bs = Except.ok ctx1) :
    SharedBoolVars ctx1 ∧ SharedBoolPreds ctx1 := by
  induction as generalizing bs ctx with
  | nil =>
    cases bs with
    | nil => rw [RcCtx.applyArgs.eq_1] at ha; cases ha; exact ⟨hsbv, hsbp⟩
    | cons =>
      rw [RcCtx.applyArgs.eq_3 _ _ _ (by intro _ h; cases h)
        (by intro _ _ _ _ h _; cases h)] at ha
      cases ha
  | cons a as' ih =>
    cases bs with
    | nil =>
      rw [RcCtx.applyArgs.eq_3 _ _ _ (by intro h _; cases h)
        (by intro _ _ _ _ _ h; cases h)] at ha
      cases ha
    | cons b bs' =>
      rw [RcCtx.applyArgs.eq_2] at ha
      by_cases hb : b = true
      · simp only [hb, ↓reduceIte] at ha
        obtain ⟨_, _, ha_tail⟩ := except_bind_ok ha
        exact ih hnd hsbv hsbp ha_tail
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
        obtain ⟨ctx_s, hcons, ha_tail⟩ := except_bind_ok ha
        have hnd_s : (ctx_s.vars.map RcVar.id).Nodup := by
          cases a with
          | erased => simp [RcCtx.consumeArg] at hcons; cases hcons; exact hnd
          | var z => exact consumeVar_nodup hnd hcons
        have hstep : SharedBoolVars ctx_s ∧ SharedBoolPreds ctx_s := by
          cases a with
          | erased => simp [RcCtx.consumeArg] at hcons; cases hcons; exact ⟨hsbv, hsbp⟩
          | var z =>
            simp only [RcCtx.consumeArg, RcCtx.consumeVar] at hcons
            cases hgz : ctx.get? z with
            | none => simp [hgz] at hcons
            | some vz =>
              simp only [hgz] at hcons
              by_cases hskip : (vz.noRc || vz.persistent) = true
              · simp [hskip] at hcons; cases hcons; exact ⟨hsbv, hsbp⟩
              · have hnz : ((1 : Nat) == 0) = false := rfl
                simp only [hskip, Bool.false_eq_true, ↓reduceIte, hnz] at hcons
                split at hcons
                · simp at hcons
                · have hput_sbv : ∀ {vz' : RcVar}, vz'.id = vz.id → vz'.noRc = vz.noRc →
                      SharedBoolVars (ctx.put vz') ∧ SharedBoolPreds (ctx.put vz') := by
                    intro vz' hid' hnr'
                    refine ⟨fun p hp vb hgb => ?_, fun p hp => ?_⟩
                    · rw [RcCtx.put.eq_1] at hp
                      rw [RcCtx.put_get? hnd] at hgb
                      by_cases h1 : (p.1 == vz'.id) = true
                      · simp only [h1, ↓reduceIte, Option.some.injEq] at hgb
                        have hpeq : p.1 = z :=
                          (beq_iff_eq.mp h1).trans (hid'.trans (RcCtx.get?_mem hgz).2)
                        obtain ⟨vb0, hgb0, hnr0⟩ := hsbp p hp
                        rw [hpeq, hgz] at hgb0; cases hgb0
                        rw [← hgb, hnr']; exact hnr0
                      · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hgb
                        exact hsbv p hp vb hgb
                    · rw [RcCtx.put.eq_1] at hp
                      obtain ⟨vb0, hgb0, hnr0⟩ := hsbp p hp
                      have hne : p.1 ≠ vz'.id := fun h => by
                        have hpeq : p.1 = z := h.trans (hid'.trans (RcCtx.get?_mem hgz).2)
                        rw [hpeq, hgz] at hgb0; cases hgb0; simp [hnr0] at hskip
                      refine ⟨vb0, ?_, hnr0⟩
                      rw [RcCtx.put_get? hnd]; simp [beq_false_of_ne hne, hgb0]
                  split at hcons
                  · simp only [pure, Except.pure, Except.ok.injEq] at hcons
                    let vz' : RcVar := {
                      id := vz.id, ty := vz.ty, noRc := vz.noRc, persistent := vz.persistent,
                      owned := vz.owned - 1, borrowed := vz.borrowed, parent? := vz.parent?,
                      excl := if (vz.owned - 1 == 0) = true then false else vz.excl,
                      resetTok := if (vz.owned - 1 == 0) = true then false else vz.resetTok }
                    obtain ⟨hsbv_p, hsbp_p⟩ := @hput_sbv vz' rfl rfl
                    have hnd_p : ((ctx.put vz').vars.map RcVar.id).Nodup := RcCtx.put_nodup hnd vz'
                    rw [← hcons]
                    refine ⟨fun p hp vb hgb => ?_, fun p hp => ?_⟩
                    · have hp_p := (invalidateChildren_live_ty_back _ hnd_p z p.1).2.2.2 p hp
                      have hmem := RcCtx.get?_mem hgb
                      obtain ⟨w, hw_mem, hwid, _, hwno, _, _, _, _, _⟩ :=
                        invalidateChildren_live_back z hmem.1
                      have hgw := (RcCtx.mem_get?_iff hnd_p).mpr hw_mem
                      rw [← hwid, hmem.2] at hgw
                      rw [hwno]; exact hsbv_p p hp_p w hgw
                    · have hp_p := (invalidateChildren_live_ty_back _ hnd_p z p.1).2.2.2 p hp
                      obtain ⟨vb0, hgb0, hnr0⟩ := hsbp_p p hp_p
                      have hmem0 := RcCtx.get?_mem hgb0
                      have hnd_inv := (invalidateChildren_live_ty_back _ hnd_p z p.1).1
                      by_cases hpar : (vb0.parent? == some z) = true
                      · let vb1 : RcVar := {
                          id := vb0.id, ty := vb0.ty, noRc := vb0.noRc,
                          persistent := vb0.persistent,
                          owned := vb0.owned, excl := vb0.excl, resetTok := vb0.resetTok }
                        have hinv_m : ((ctx.put vz').invalidateChildren z).get? p.1 = some vb1 := by
                          have hm : vb1 ∈ ((ctx.put vz').invalidateChildren z).vars := by
                            simp only [RcCtx.invalidateChildren, List.mem_map]
                            exact ⟨vb0, hmem0.1, by simp [vb1, hpar]⟩
                          have hg := (RcCtx.mem_get?_iff hnd_inv).mpr hm
                          rwa [show vb1.id = p.1 from hmem0.2] at hg
                        exact ⟨vb1, hinv_m, hnr0⟩
                      · have hinv_m : ((ctx.put vz').invalidateChildren z).get? p.1 = some vb0 := by
                          have hm : vb0 ∈ ((ctx.put vz').invalidateChildren z).vars := by
                            simp only [RcCtx.invalidateChildren, List.mem_map]
                            exact ⟨vb0, hmem0.1, by simp [hpar]⟩
                          have hg := (RcCtx.mem_get?_iff hnd_inv).mpr hm
                          rwa [hmem0.2] at hg
                        exact ⟨vb0, hinv_m, hnr0⟩
                  · simp only [pure, Except.pure, Except.ok.injEq] at hcons
                    rw [← hcons]; exact hput_sbv rfl rfl
        exact ih hnd_s hstep.1 hstep.2 ha_tail

public theorem baseCtx_live_agree_rf {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState}
    {Jp : PResJEnv} {Jh : HJEnv} {e : JpEntry} {ρP : PValEnv} {as : List LcArg} {ctx1 : RcCtx}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx)
    (hok : JpEntryOk rt rf0 σ0 Jp Jh e) (hlive : JpEntryLiveAgree e rf ρP)
    (ha1 : rf.ctx.applyArgs as (e.info.params.map (·.borrow)) = Except.ok ctx1)
    (hw_base : CtxWeakens e.baseCtx (ctx1.restrict e.info.scopeIds))
    (hcleanS : CleanVars (ctx1.restrict e.info.scopeIds))
    (hnoMut : ∀ id ∈ baseCtxLiveIds e.baseCtx, id ∉ e.mutVars)
    {w : RcVar} (hw : w ∈ e.baseCtx.vars) (hwl : w.isLive = true) :
    ∃ vs v_rf,
      vs ∈ (ctx1.restrict e.info.scopeIds).vars ∧
      (ctx1.restrict e.info.scopeIds).get? w.id = some vs ∧
      rf.ctx.get? w.id = some v_rf ∧ v_rf ∈ rf.ctx.vars ∧ v_rf.isLive = true ∧
      vs.id = w.id ∧ v_rf.id = w.id ∧
      v_rf.noRc = w.noRc ∧ v_rf.persistent = w.persistent ∧ v_rf.ty = w.ty ∧
      vs.noRc = w.noRc ∧ vs.persistent = w.persistent ∧ vs.owned = w.owned ∧
      vs.owned ≤ v_rf.owned ∧
      (w.borrowed = true → vs.borrowed = true ∧ vs.parent? = w.parent? ∧
        v_rf.borrowed = true ∧ v_rf.parent? = w.parent?) ∧
      (w.excl = true → vs.excl = true ∧ v_rf.excl = true) ∧
      rf.envP w.id = e.envPJp w.id ∧ rf.envH w.id = e.envHJp w.id ∧ ρP w.id = e.envPJp w.id ∧
      varHandles e.envHJp w = varHandles rf.envH vs := by
  have hsB := hok.2.2.2.2.1
  have hidB : w.id ∈ baseCtxLiveIds e.baseCtx :=
    List.mem_map.mpr ⟨w, List.mem_filter.mpr ⟨hw, hwl⟩, rfl⟩
  have hnotM : w.id ∉ e.mutVars := hnoMut w.id hidB
  obtain ⟨vs, hvs_mem, hwid, _, _, hnr, hps, how, hbr_imp, hex_imp, hrt_imp⟩ :=
    hw_base.2.2.1 w hw
  have hvs_get : (ctx1.restrict e.info.scopeIds).get? w.id = some vs := by
    rw [hwid]; exact (RcCtx.mem_get?_iff hw_base.2.1).mpr hvs_mem
  have hvs_live : vs.isLive = true := by
    have hrtW' : w.resetTok = false := hrt_imp (hcleanS vs hvs_mem).2.2.2.2
    simp only [RcVar.isLive, hrtW', Bool.or_false] at hwl ⊢
    by_cases h1 : w.noRc = true
    · simp [← hnr, h1]
    · by_cases h2 : w.persistent = true
      · simp [← hps, h2]
      · by_cases h3 : w.owned > 0
        · simp [← how, h3]
        · have h4 : w.borrowed = true := by
            simp [h1, h2, h3] at hwl; exact hwl
          simp [(hbr_imp h4).1]
  have hvs_mem1 : vs ∈ ctx1.vars := (restrict_mem_iff.mp hvs_mem).1
  have hvs_get1 : ctx1.get? w.id = some vs := by
    have hnd1 := applyArgs_nodup hinv.2.1 ha1
    rw [hwid]; exact (RcCtx.mem_get?_iff hnd1).mpr hvs_mem1
  obtain ⟨v_rf, hrf_get, hrf_live, hrf_no, hrf_ps, hrf_ty, hrf_ow, hrf_br, hrf_ex⟩ :=
    applyArgs_get?_live_back hinv.2.1 hclean ha1 w.id hvs_get1 hvs_live
  have hrf_mem := RcCtx.get?_mem hrf_get
  have hrf_get_live : (rf.ctx.get? w.id).map RcVar.isLive = some true := by
    simp [hrf_get, hrf_live]
  obtain ⟨heP, heH, hrP, hty_rf_jp, hlive_jp⟩ := hlive.1 w.id hidB hnotM hrf_get_live
  have hagree_base := hok.2.2.2.2.2.2.1
  have hgB : e.baseCtx.get? w.id = some w := baseCtx_vars_of_mem_nodup hsB.1 hw
  have hbase_live : (e.baseCtx.get? w.id).map RcVar.isLive = some true := by simp [hgB, hwl]
  have hty_jp_base := (hagree_base.1 w.id hidB hbase_live).2
  have hty_eq : v_rf.ty = w.ty := by
    have h1 : (rf.ctx.get? w.id).map (·.ty) = (e.baseCtx.get? w.id).map (·.ty) :=
      hty_rf_jp.trans hty_jp_base
    simpa [hrf_get, hgB, ← hrf_ty] using h1
  have hcleanB := cleanVars_of_ctxWeakens hw_base hcleanS
  have hrtW : w.resetTok = false := (hcleanB w hw).2.2.2.2
  have hrtS : vs.resetTok = false := (hcleanS vs hvs_mem).2.2.2.2
  have hvh : varHandles e.envHJp w = varHandles rf.envH vs := by
    simp only [varHandles, ← hnr, ← hps, hrtW, hrtS, ← how, ← hwid, heH]
  refine ⟨vs, v_rf, hvs_mem, hvs_get, hrf_get, hrf_mem.1, hrf_live, hwid.symm, hrf_mem.2,
    hrf_no.trans hnr.symm, hrf_ps.trans hps.symm, hty_eq, hnr.symm, hps.symm, how.symm, hrf_ow,
    ?_, ?_, heP, heH, hrP, hvh⟩
  · intro hwbr
    obtain ⟨hbs, hps'⟩ := hbr_imp hwbr
    obtain ⟨hbrf, hprf⟩ := hrf_br hbs
    exact ⟨hbs, hps', hbrf, hprf.trans hps'⟩
  · intro hwex
    have hes := hex_imp hwex
    exact ⟨hes, hrf_ex hes⟩

public theorem handlesRcSound_jmp_frame {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState}
    {Jp : PResJEnv} {Jh : HJEnv} {e : JpEntry} {ρP : PValEnv} {as : List LcArg} {ctx1 : RcCtx}
    {pvs : List PVal} {ws : List Word}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hok : JpEntryOk rt rf0 σ0 Jp Jh e) (hlive : JpEntryLiveAgree e rf ρP)
    (ha1 : rf.ctx.applyArgs as (e.info.params.map (·.borrow)) = Except.ok ctx1)
    (hleaks : ctx1.checkNoLeaks e.info.scopeIds = Except.ok ())
    (hmatch : argsMatchTys rf.ctx as (e.info.params.map (·.ty)) = true)
    (hnst : argsNoSharedTarget rf.ctx as (e.info.params.map (·.borrow)) = true)
    (hw_base : CtxWeakens e.baseCtx (ctx1.restrict e.info.scopeIds))
    (hcleanS : CleanVars (ctx1.restrict e.info.scopeIds))
    (hnoMut : ∀ id ∈ baseCtxLiveIds e.baseCtx, id ∉ e.mutVars)
    (hpvs : rf.envP.evalArgs as = some pvs) (hws : rf.envH.evalArgsOwn as = some ws)
    (hlen_ws : ws.length = e.info.params.length)
    (hlive_as : ∀ a ∈ as, a = LcArg.erased ∨ ∃ z v, a = LcArg.var z ∧
      rf.ctx.get? z = some v ∧ v.isLive = true)
    (hext : e.extH = rf.extH) :
    let rfB : RcFrame := {
      ctx := e.baseCtx.bindParams e.info.params, envP := e.envPJp.bindAll e.info.params pvs,
      envH := e.envHJp.bindAll e.info.params ws, extH := e.extH, ghostH := rf.ghostH }
    (∀ addr, (∀ v ∈ rf.ctx.vars, v.isLive = true → v.persistent = true →
        ∀ w, rf.envH v.id = some (v.ty, w) → w.toBV64? ≠ some addr) →
      List.count addr (frameHandles rfB) ≤ List.count addr (frameHandles rf)) ∧
    HandlesRcSound (frameHandles rfB) σ.objs := by
  intro rfB
  have hsB := hok.2.2.2.2.1
  have hfrB := hok.2.2.2.1
  have hndP := hok.2.2.1
  obtain ⟨hperm1, hinv1, hclean1, _⟩ := rcInv_applyArgs_step hinv hclean hpo ha1 hnst
  obtain ⟨hpermS, _⟩ := restrict_handles_perm rf.envH hclean1 hleaks
  have hbind_perm := localHandles_bindParams_perm_fresh e.info.params ws hlen_ws hndP
    e.baseCtx e.envHJp hsB.1 hfrB
  have hle_keep : ∀ addr, List.count addr (localHandles e.baseCtx e.envHJp) ≤
      List.count addr (localHandles (ctx1.restrict e.info.scopeIds) rf.envH) := by
    intro addr
    refine count_flatten_map_le_of_inj e.baseCtx.vars (ctx1.restrict e.info.scopeIds).vars
      RcVar.id (varHandles e.envHJp) (varHandles rf.envH) hsB.1 (fun w hw => ?_) addr
    by_cases hwl : w.isLive = true
    · obtain ⟨vs, _, _, _, _, _, _, hwid, _, _, _, _, _, _, _, _, _, _, _, _, _, hvh⟩ :=
        baseCtx_live_agree_rf hinv hclean hok hlive ha1 hw_base hcleanS hnoMut hw hwl
      exact Or.inr ⟨vs, ‹vs ∈ (ctx1.restrict e.info.scopeIds).vars›, hwid, hvh⟩
    · refine Or.inl ?_
      have hwlF : (w.noRc || w.persistent || w.resetTok || w.owned == 0) = true := by
        simp only [RcVar.isLive, Bool.or_eq_true, not_or] at hwl
        by_cases hnr : w.noRc = true
        · exfalso; exact hwl.1.1.1.1 hnr
        by_cases hps : w.persistent = true
        · exfalso; exact hwl.1.1.1.2 hps
        have how0 : (w.owned == 0) = true := by
          by_cases h0 : w.owned == 0
          · exact h0
          · exfalso; have hgt : 0 < w.owned := Nat.pos_of_ne_zero (fun heq => h0 (by simp [heq]))
            exact hwl.1.1.2 (decide_eq_true hgt)
        simp [how0]
      simp [varHandles, hwlF]
  have hcount : ∀ addr,
      (∀ v ∈ rf.ctx.vars, v.isLive = true → v.persistent = true →
        ∀ w, rf.envH v.id = some (v.ty, w) → w.toBV64? ≠ some addr) →
      List.count addr (frameHandles rfB) ≤ List.count addr (frameHandles rf) := by
    intro addr hnp
    have hle_new := applyArgsHandles_entryParamHandles_count_le hinv e.info.params as pvs ws
      hmatch hpvs hws hlive_as hnp
    have hk := hle_keep addr
    have hpB := hbind_perm.count_eq addr
    have hpS := hpermS.count_eq addr
    have hp1 := hperm1.count_eq addr
    dsimp only [rfB] at hpB ⊢
    simp only [frameHandles.eq_1, List.count_append] at hpB hpS hp1 ⊢
    rw [hext]
    have hlam : (List.map (fun x => entryParamHandles x.fst x.snd) (e.info.params.zip ws)).flatten =
        (List.map (fun (p, w) => entryParamHandles p w) (e.info.params.zip ws)).flatten := rfl
    rw [← hlam] at hle_new
    omega
  refine ⟨hcount, hinv.2.2.1.1, fun y hy hy_pos => ?_⟩
  have hnp_y : ∀ v ∈ rf.ctx.vars, v.isLive = true → v.persistent = true →
      ∀ w, rf.envH v.id = some (v.ty, w) → w.toBV64? ≠ some y.addr := by
    intro v hv hvl hvps w hHv hweq
    obtain ⟨_, wv, _, hHv0, _, hrest⟩ := hinv.2.2.2.1 v hv hvl
    rw [hHv0, Option.some.injEq] at hHv
    have hvnrc : v.noRc = false := (hclean v hv).2.1 hvps |>.1
    have hvnsc : ¬v.ty.isScalar = true := fun h => by
      have := (hclean v hv).1.2 h; simp [hvnrc] at this
    obtain ⟨bv, hwbv, _, hps, _⟩ := hrest hvnsc
    have hbv : bv = y.addr := by
      have hwe := (Prod.mk.inj hHv).2
      rw [← hwe, hwbv] at hweq
      simp only [Word.toBV64?, Word.i64, Option.some.injEq] at hweq
      exact hweq
    have hywf : y.Wf := hinv.1.1.2.1 y hy
    have hbv0 : bv &&& 1#64 = 0#64 := hbv ▸ obj_addr_and1_zero hywf
    obtain ⟨o, ho, hoa, horc⟩ := hps hvps hbv0
    have heqo : o = y := obj_eq_of_addr_nodup hinv.1.2 ho hy (hoa.trans hbv)
    subst heqo
    have h0 : (0#32 : BitVec 32).toInt = 0 := rfl
    rw [horc, h0] at hy_pos; exact absurd hy_pos (by omega)
  have hc_y := hcount y.addr hnp_y
  have hbase_y := hinv.2.2.1.2 y hy hy_pos
  omega

public theorem paramsMatch_of_argsMatchTys {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (ps : List LcParam) (as : List LcArg) (pvs : List PVal) (ws : List Word)
    (hmatch : argsMatchTys rf.ctx as (ps.map (·.ty)) = true)
    (hpvs : rf.envP.evalArgs as = some pvs) (hws : rf.envH.evalArgsOwn as = some ws)
    (hlive : ∀ a ∈ as, a = LcArg.erased ∨ ∃ z v, a = LcArg.var z ∧
      rf.ctx.get? z = some v ∧ v.isLive = true) :
    paramsMatch ps ws := by
  induction ps generalizing as pvs ws with
  | nil =>
    cases as with
    | nil =>
      cases ws with
      | nil => simp [paramsMatch]
      | cons => simp [HValEnv.evalArgsOwn] at hws
    | cons => simp [argsMatchTys] at hmatch
  | cons p rest ih =>
    cases as with
    | nil => simp [argsMatchTys] at hmatch
    | cons a as' =>
      have hmatch' := hmatch
      simp only [argsMatchTys, List.map_cons, List.length_cons, List.length_map, beq_iff_eq,
        Nat.succ.injEq, List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hmatch'
      obtain ⟨hlen, hm1, hm_rest⟩ := hmatch'
      have hmt_rest : argsMatchTys rf.ctx as' (rest.map (·.ty)) = true := by
        simpa [argsMatchTys, hlen] using hm_rest
      rw [PValEnv.evalArgs.eq_2] at hpvs
      cases hpa : rf.envP.evalArg a with
      | none => simp [hpa] at hpvs
      | some pv0 =>
        cases hpas : rf.envP.evalArgs as' with
        | none => simp [hpa, hpas] at hpvs
        | some pvs0 =>
          simp only [hpa, hpas, Option.some.injEq] at hpvs
          cases hpvs
          rw [HValEnv.evalArgsOwn.eq_2] at hws
          cases hwa : rf.envH.evalArgOwn a with
          | none => simp [hwa] at hws
          | some w0 =>
            cases hwas : rf.envH.evalArgsOwn as' with
            | none => simp [hwa, hwas] at hws
            | some ws0 =>
              simp only [hwa, hwas, Option.some.injEq] at hws
              cases hws
              rw [paramsMatch.eq_2]
              refine ⟨?_, ih as' pvs0 ws0 hmt_rest hpas hwas
                (fun b hb => hlive b (List.mem_cons_of_mem _ hb))⟩
              cases a with
              | erased =>
                simp only [HValEnv.evalArgOwn, Option.some.injEq] at hwa
                cases hwa
                have hnp_sc : p.ty.isScalar = false := by
                  simpa using (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp hm1).1).1
                have h1 : ∀ t : LcTy, t.isScalar = false → t.toTTy = Ty.bits 64 := fun t => by
                  cases t <;> simp [LcTy.isScalar, LcTy.toTTy, LcTy.width]
                rw [h1 p.ty hnp_sc, Word.i64]
              | var z =>
                rcases hlive (LcArg.var z) List.mem_cons_self with
                  h0 | ⟨z', vz, heqz, hgz, hlivez⟩
                · cases h0
                · cases heqz
                  have hmemz := RcCtx.get?_mem hgz
                  obtain ⟨pvv, wv, hPv, hHv, hvr, _⟩ := hinv.2.2.2.1 vz hmemz.1 hlivez
                  simp only [HValEnv.evalArgOwn] at hwa
                  rw [← hmemz.2, hHv, Option.map_some, Option.some.injEq] at hwa
                  cases hwa
                  have hty_w : vz.ty.width = p.ty.width := by
                    simp only [hgz, Bool.and_eq_true, beq_iff_eq] at hm1
                    exact hm1.1.1.1.2
                  rw [valRep_fst_eq hvr, LcTy.toTTy, LcTy.toTTy, hty_w]

public theorem evalArgs_of_shadowOk {sm : List (Nat × Nat × List Bool)} {ctx : RcCtx}
    {ρP envP : PValEnv} (hshd : ShadowOk sm ctx ρP envP)
    {as : List LcArg} (hinit : as.all (argScalarInit sm) = true)
    (hlive : ∀ a ∈ as, a = LcArg.erased ∨ ∃ z v, a = LcArg.var z ∧
      ctx.get? z = some v ∧ v.isLive = true) :
    ρP.evalArgs as = envP.evalArgs as := by
  induction as with
  | nil => simp [PValEnv.evalArgs]
  | cons a rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hinit
    have ih_res := ih hinit.2 (fun b hb => hlive b (List.mem_cons_of_mem _ hb))
    rw [PValEnv.evalArgs.eq_2, PValEnv.evalArgs.eq_2, ih_res]
    have h1 : ρP.evalArg a = envP.evalArg a := by
      refine shadowOk_evalArg hshd hinit.1 ?_
      cases a with
      | erased => trivial
      | var z =>
        rcases hlive (LcArg.var z) List.mem_cons_self with h0 | ⟨z', v, heqz, hgz, hv⟩
        · cases h0
        · cases heqz; have hm := RcCtx.get?_mem hgz; exact ⟨v, hm.1, hm.2, hv⟩
    rw [h1]

end JmpFrame

end LeanQbe.T.LeanLCNF.Sem
