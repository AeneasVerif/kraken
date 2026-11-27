module

public import LeanQbe.T.LeanLCNF.Sem.PerceusCases
public import LeanQbe.T.LeanLCNF.Sem.PerceusInc
public import LeanQbe.T.LeanLCNF.Sem.PerceusDec
public import LeanQbe.T.LeanLCNF.Sem.PerceusDel
public import LeanQbe.T.LeanLCNF.Sem.PerceusMut
public import LeanQbe.T.LeanLCNF.Sem.PerceusJp
public import LeanQbe.T.LeanLCNF.Sem.PerceusLet

/-!
# Perceus Tier-P → Tier-H Soundness (`perceus_sound`)

Combines all construct-level stepwise simulations (`let_step`, `cases_branch_step`, `inc_step_ctx`,
`dec_step_ctx`, `del_step_ctx`, `oset_step_ctx`, `uset_step`, `sset_step`, `setTag_step`,
`jp_step`, `jmp_step`, `ret_step`, `unreach_step`) into:
- `perceus_code_sim`: whole-body simulation over `LcCode`,
- `perceus_decl_ok_res`, `perceus_sound_res`, `perceus_sound_res_idx`,
- `perceus_sound` and `perceus_sound_idx`.
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

section Helpers

public theorem heapClean_swap_rt {rt1 rt2 : BitVec 64} {σ : HState}
    (hc : HeapClean rt1 σ) (hrt2 : rt2.toNat + LcnfC0BigNumRt.sizeof < 2 ^ 64) :
    HeapClean rt2 σ :=
  ⟨⟨⟨hc.1.1.1, hrt2, hc.1.1.2.2⟩, hc.1.2⟩, hc.2⟩

public theorem rcInv_swap_rt {rt1 rt2 : BitVec 64} {rf : RcFrame} {σ : HState}
    (hrc : RcInv rt1 rf σ) (hinv2 : HInv rt2 σ) : RcInv rt2 rf σ :=
  ⟨⟨hinv2, hrc.1.2⟩, hrc.2⟩

private theorem localHandles_eq_nil_of_checkNoLeaks {ctx : RcCtx} {envH : HValEnv}
    (hnl : ctx.checkNoLeaks [] = .ok ()) : localHandles ctx envH = [] := by
  have hspec := checkNoLeaks_spec hnl
  have hvh : ∀ v ∈ ctx.vars, varHandles envH v = [] := fun v hv => by
    have hflg := hspec v hv (by simp)
    unfold varHandles
    rcases Bool.or_eq_true _ _ |>.mp hflg with h12 | hown0
    · rcases Bool.or_eq_true _ _ |>.mp h12 with hno | hpers
      · simp [hno]
      · simp [hpers]
    · simp [hown0]
  suffices h : ∀ l : List RcVar, (∀ v ∈ l, varHandles envH v = []) →
      (l.map (varHandles envH)).flatten = [] from
    h ctx.vars hvh
  intro l hl
  induction l with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, List.flatten_cons]
    rw [hl v List.mem_cons_self, List.nil_append]
    exact ih (fun u hu => hl u (List.mem_cons_of_mem _ hu))

private theorem handlesRcSound_add_persist_ret {hs : List (BitVec 64)} {objs : List LcnfObj}
    (hsnd : HandlesRcSound hs objs) (hnodup : (objs.map LcnfObj.addr).Nodup)
    {bv : BitVec 64} {o : LcnfObj} (ho : o ∈ objs) (hoa : o.addr = bv) (horc0 : o.rc = 0#32) :
    HandlesRcSound (bv :: hs) objs := by
  refine ⟨hsnd.1, fun q hq hpos => ?_⟩
  have hqne : q.addr ≠ bv := fun heq => by
    have hqeq := obj_eq_of_addr_nodup hnodup hq ho (heq.trans hoa.symm)
    subst hqeq; rw [horc0] at hpos; simp at hpos
  rw [List.count_cons_of_ne (Ne.symm hqne)]
  exact hsnd.2 q hq hpos

public theorem mod_decl_unique {m : LcModule} (hnd : (m.decls.map LcDecl.name).Nodup)
    {d d' : LcDecl} (hd : d ∈ m.decls) (hd' : d' ∈ m.decls) (heq : d'.name = d.name) :
    d' = d := by
  generalize m.decls = ds at hnd hd hd'
  induction ds with
  | nil => cases hd
  | cons a rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hd with rfl | hd_r <;> rcases List.mem_cons.mp hd' with rfl | hd'_r
    · rfl
    · exact absurd ⟨d', hd'_r, heq⟩ hnd.1
    · exact absurd ⟨d, hd_r, heq.symm⟩ hnd.1
    · exact ih hnd.2 hd_r hd'_r

private theorem checkModule_for_aux (env : RcModEnv) (ds : List LcDecl) :
    (match (do
      for d in ds do
        match checkDeclRc env d with
        | .ok () => pure ()
        | .error msg => throw (d.name, msg)
      pure () : Except (String × String) Unit) with
    | .ok () => true
    | .error _ => false) = true →
    ∀ d ∈ ds, checkDeclRc env d = .ok () := by
  induction ds with
  | nil => intro _ d hd; cases hd
  | cons d0 tl ih =>
    intro h d hd
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw, MonadExcept.throw, List.forIn_cons] at h
    cases hck : checkDeclRc env d0 with
    | error msg => simp [hck] at h
    | ok _ =>
      simp only [hck] at h
      rcases List.mem_cons.mp hd with rfl | htl
      · exact hck
      · exact ih (by simpa [bind, Except.bind, pure, Except.pure, throw, throwThe,
          MonadExceptOf.throw, MonadExcept.throw] using h) d htl

public theorem rcCheck_decl_checkCode {m : LcModule} (hrc : RcCheck m = true)
    {d : LcDecl} (hd : d ∈ m.decls) :
    ∃ jumps, checkCode (mkRcModEnv m) d.retTy [] ((RcCtx.mk [] []).bindParams d.params)
      d.body = .ok jumps := by
  have hdecl := checkModule_for_aux (mkRcModEnv m) m.decls hrc d hd
  unfold checkDeclRc at hdecl
  cases hcc : checkCode (mkRcModEnv m) d.retTy [] ((RcCtx.mk [] []).bindParams d.params)
      d.body with
  | error e => simp [hcc, Bind.bind, Except.bind] at hdecl
  | ok js => exact ⟨js, rfl⟩

private theorem checkCode_cases_branch {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {x : Nat} {alts : List (LcPat × LcCode)} {jumps : List (Nat × RcCtx)}
    (hcc : checkCode env retTy jps ctx (.cases x alts) = .ok jumps)
    {pat : LcPat} {b : LcCode} (hmem : (pat, b) ∈ alts) :
    let target? := (ctx.sharedPreds.find? (·.1 == x)).map Prod.snd
    ∃ j_b, checkCode env retTy jps (casesBranchCtx env target? pat x ctx) b = .ok j_b ∧
      ∀ jc ∈ j_b, jc ∈ jumps := by
  intro target?
  dsimp only [target?]
  rw [checkCode.eq_4] at hcc
  cases hcl : ctx.checkLive x with
  | error _ => simp [hcl, bind, Except.bind] at hcc
  | ok _ =>
    simp only [hcl, bind, Except.bind] at hcc
    induction alts generalizing jumps with
    | nil => cases hmem
    | cons a rest ih =>
      rcases a with ⟨p1, b1⟩
      have hca_eq : checkAlts env retTy jps ctx x
            ((ctx.sharedPreds.find? (·.1 == x)).map Prod.snd) ((p1, b1) :: rest) =
          (do
            let j1 ← checkCode env retTy jps (casesBranchCtx env
              ((ctx.sharedPreds.find? (·.1 == x)).map Prod.snd) p1 x ctx) b1
            let j2 ← checkAlts env retTy jps ctx x
              ((ctx.sharedPreds.find? (·.1 == x)).map Prod.snd) rest
            pure (j1 ++ j2)) := by
        cases p1 with
        | dflt => cases (ctx.sharedPreds.find? (·.1 == x)).map Prod.snd <;> rfl
        | ctor ci cname =>
          cases ci <;> cases (ctx.sharedPreds.find? (·.1 == x)).map Prod.snd <;> rfl
      rw [hca_eq] at hcc
      cases h1 : checkCode env retTy jps
          (casesBranchCtx env ((ctx.sharedPreds.find? (·.1 == x)).map Prod.snd) p1 x ctx) b1 with
      | error _ => simp [h1, bind, Except.bind] at hcc
      | ok j1 =>
        simp only [h1, bind, Except.bind] at hcc
        cases h2 : checkAlts env retTy jps ctx x
            ((ctx.sharedPreds.find? (·.1 == x)).map Prod.snd) rest with
        | error _ => simp [h2] at hcc
        | ok j2 =>
          simp only [h2, pure, Except.pure, Except.ok.injEq] at hcc
          subst hcc
          rcases List.mem_cons.mp hmem with hhead | hrest
          · cases hhead; exact ⟨j1, h1, fun jc hjc => List.mem_append.mpr (Or.inl hjc)⟩
          · obtain ⟨jb, hjb_ok, hjb_sub⟩ := ih hrest h2
            exact ⟨jb, hjb_ok, fun jc hjc => List.mem_append.mpr (Or.inr (hjb_sub jc hjc))⟩

private theorem jpAltsLiveNoMut_mem {j : Nat} {liveIds mutVars : List Nat}
    {alts : List (LcPat × LcCode)}
    (ha : jpAltsLiveNoMut j liveIds mutVars alts = true)
    {pat : LcPat} {b : LcCode} (hm : (pat, b) ∈ alts) :
    jpLiveNoMut j liveIds mutVars b = true := by
  induction alts with
  | nil => cases hm
  | cons a rest ih =>
    rcases a with ⟨p1, b1⟩
    have ha_eq : jpAltsLiveNoMut j liveIds mutVars ((p1, b1) :: rest) =
        (jpLiveNoMut j liveIds mutVars b1 && jpAltsLiveNoMut j liveIds mutVars rest) := rfl
    rw [ha_eq, Bool.and_eq_true] at ha
    rcases List.mem_cons.mp hm with hhead | hrest
    · cases hhead; exact ha.1
    · exact ih ha.2 hrest

private theorem sharedBoolVars_put_eq_noRc {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hsbv : SharedBoolVars ctx) {v v' : RcVar}
    (hmem : v ∈ ctx.vars) (hid : v'.id = v.id) (hno : v'.noRc = v.noRc) :
    SharedBoolVars (ctx.put v') := by
  intro p hp vb hgb
  by_cases hpid : p.1 = v.id
  · rw [hpid, ← hid, get?_put_self ctx hnd v'] at hgb
    cases hgb
    have hvg := (RcCtx.mem_get?_iff hnd).mpr hmem
    rw [hno]
    exact hsbv p hp v (by simpa [hpid] using hvg)
  · rw [get?_put_ne ctx hnd (by simpa [hid] using hpid)] at hgb
    exact hsbv p hp vb hgb

private theorem sharedBoolPreds_put_eq_noRc {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hsbp : SharedBoolPreds ctx) {v v' : RcVar}
    (hmem : v ∈ ctx.vars) (hid : v'.id = v.id) (hno : v'.noRc = v.noRc) :
    SharedBoolPreds (ctx.put v') := by
  intro p hp
  obtain ⟨vb, hgb, hvb_no⟩ := hsbp p hp
  by_cases hpid : p.1 = v.id
  · refine ⟨v', by rw [hpid, ← hid, get?_put_self ctx hnd v'], ?_⟩
    have hvg := (RcCtx.mem_get?_iff hnd).mpr hmem
    rw [hpid] at hgb
    rw [hvg] at hgb; cases hgb
    exact hno.trans hvb_no
  · refine ⟨vb, ?_, hvb_no⟩
    rw [get?_put_ne ctx hnd (by simpa [hid] using hpid)]
    exact hgb

private theorem exclCtorHeap_put_exclFalse {rf : RcFrame}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup) (hex : ExclCtorHeap rf) {v' : RcVar}
    (hexcl_f : v'.excl = false) :
    ExclCtorHeap { rf with ctx := rf.ctx.put v' } := by
  intro u hu hl huex hnr hpr cidx fs sc hp
  have hgetu := get?_of_mem_nodup (rf.ctx.put_nodup hnd v') hu
  by_cases heq : u.id = v'.id
  · rw [heq, get?_put_self rf.ctx hnd v'] at hgetu
    have hu_eq := Option.some.inj hgetu
    rw [← hu_eq, hexcl_f] at huex
    cases huex
  · rw [get?_put_ne rf.ctx hnd heq] at hgetu
    exact hex u (RcCtx.get?_mem hgetu).1 hl huex hnr hpr cidx fs sc hp

private theorem shadowOk_put_live {sm : List (Nat × Nat × List Bool)} {ctx : RcCtx}
    {ρP envP : PValEnv} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hsh : ShadowOk sm ctx ρP envP) {v v' : RcVar}
    (hmem : v ∈ ctx.vars) (hid : v'.id = v.id) (hlive_imp : v'.isLive = true → v.isLive = true) :
    ShadowOk sm (ctx.put v') ρP envP := by
  intro u hu hl
  have hgetu := get?_of_mem_nodup (ctx.put_nodup hnd v') hu
  by_cases heq : u.id = v'.id
  · rw [heq, get?_put_self ctx hnd v'] at hgetu
    have hu_eq := Option.some.inj hgetu
    have hv'_l : v'.isLive = true := hu_eq ▸ hl
    have hshv := hsh v hmem (hlive_imp hv'_l)
    rw [← hu_eq, hid]; exact hshv
  · rw [get?_put_ne ctx hnd heq] at hgetu
    exact hsh u (RcCtx.get?_mem hgetu).1 hl

private theorem shadowOk_filter_del {sm : List (Nat × Nat × List Bool)} {ctx ctx1 : RcCtx}
    {ρP envP : PValEnv} {x : Nat} (hnd : (ctx.vars.map RcVar.id).Nodup) (hcl : CleanVars ctx)
    (hchk : ctx.checkExcl x "del" = .ok ()) (hcons : ctx.consumeVar x = .ok ctx1)
    (hsh : ShadowOk sm ctx ρP envP) :
    ShadowOk (sm.filter (·.1 != x)) ctx1 ρP envP := by
  have hsh1 := shadowOk_consumeVar hnd hcl hcons hsh
  have hnd1 := consumeVar_nodup hnd hcons
  have hcl1 := cleanVars_consumeVar hnd hcl hcons
  obtain ⟨vx, hgx, hno, hpers, hrt, hown1, hex, _⟩ := checkExcl_facts hchk
  intro u hu hl
  have hne : u.id ≠ x := fun heq => by
    have hgetu := get?_of_mem_nodup hnd1 hu
    rw [heq] at hgetu
    unfold RcCtx.consumeVar at hcons
    rw [hgx] at hcons
    dsimp only at hcons
    rw [hno, hpers] at hcons
    simp only [Bool.false_or] at hcons
    have hlt : ¬vx.owned < 1 := by omega
    simp only [hlt, ↓reduceIte, beq_false_of_ne (by decide : (1 : Nat) ≠ 0)] at hcons
    let v' : RcVar := {
      id := vx.id, ty := vx.ty, noRc := false, persistent := false, owned := 0,
      borrowed := false, parent? := vx.parent?, excl := false, resetTok := false }
    have hbor : vx.borrowed = false := by
      by_cases hb : vx.borrowed = true
      · exact absurd ((hcl vx (RcCtx.get?_mem hgx).1).2.2.1 hb).2.2 (by simp [hex])
      · exact Bool.eq_false_iff.mpr hb
    have hput : ctx1 = (ctx.put v').invalidateChildren x := by
      simp only [hown1, hbor, Nat.sub_self, beq_self_eq_true, Bool.not_false, Bool.and_self,
        Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hcons
      exact hcons.symm
    have hnd_put := ctx.put_nodup hnd v'
    have hgv' : (ctx.put v').get? x = some v' := by
      have hid' : v'.id = x := (RcCtx.get?_mem hgx).2
      rw [← hid', get?_put_self ctx hnd v']
    have hm_u : u ∈ ((ctx.put v').invalidateChildren x).vars := hput ▸ hu
    obtain ⟨w, hw, hw_eq⟩ := List.mem_map.mp hm_u
    have hw_id : w.id = x := by
      have : (if w.parent? == some x then { w with borrowed := false, parent? := none } else w).id =
          u.id := by rw [hw_eq]
      rw [heq] at this
      split at this <;> exact this
    have hwg : (ctx.put v').get? x = some w := by
      have := get?_of_mem_nodup hnd_put hw; rwa [hw_id] at this
    rw [hgv'] at hwg; cases hwg
    rw [← hw_eq] at hl
    split at hl <;> simp [v', RcVar.isLive] at hl
  have h0 := hsh1 u hu hl
  have his : isVarScalarInit (sm.filter (·.1 != x)) u.id = isVarScalarInit sm u.id := by
    simp only [isVarScalarInit, List.all_filter]
    congr 1; ext e
    by_cases hfx : e.1 = x
    · simp [hfx, hne.symm]
    · simp [hfx]
  rw [his]
  by_cases hisu : isVarScalarInit sm u.id = true
  · simp only [hisu, ↓reduceIte] at h0 ⊢; exact h0
  · simp only [hisu, Bool.false_eq_true, ↓reduceIte] at h0 ⊢
    rw [find?_filter_ne sm hne]; exact h0

private theorem markScalarBranch_ctx_props {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    {x : Nat} (hx : ∀ v, ctx.get? x = some v → v.isLive = true) :
    (∀ z, Option.map RcVar.ty ((ctx.markScalarBranch x).get? z) = Option.map RcVar.ty (ctx.get? z) ∧
      (Option.map RcVar.isLive ((ctx.markScalarBranch x).get? z) = some true →
        Option.map RcVar.isLive (ctx.get? z) = some true)) ∧
    (∀ p, p ∈ (ctx.markScalarBranch x).sharedPreds → p ∈ ctx.sharedPreds) ∧
    (∀ id, (ctx.get? id).isSome = true → ((ctx.markScalarBranch x).get? id).isSome = true) := by
  unfold RcCtx.markScalarBranch
  cases hgx : ctx.get? x with
  | none => exact ⟨fun z => ⟨rfl, fun h => h⟩, fun _ h => h, fun _ h => h⟩
  | some v =>
    by_cases hty : (v.ty == LcTy.tobject || v.ty == LcTy.tagged) = true
    · simp only [hty, ↓reduceIte]
      let v' : RcVar := { id := v.id, ty := v.ty, noRc := true }
      have hnd1 := ctx.put_nodup hnd v'
      have hinv_c := fun z => invalidateChildren_live_ty_back (ctx.put v') hnd1 x z
      have hvl : v.isLive = true := hx v hgx
      refine ⟨fun z => ?_, fun p hp => ?_, fun id hid => ?_⟩
      · obtain ⟨_, hty_i, hlive_i, _⟩ := hinv_c z
        by_cases hzx : z = x
        · subst hzx
          have hgx_m := RcCtx.get?_mem hgx
          have hgx_id : ctx.get? v.id = some v := hgx_m.2 ▸ hgx
          have heq_p : (ctx.put v').get? v.id = some v' := get?_put_self ctx hnd v'
          constructor
          · rw [hty_i, ← hgx_m.2, heq_p, hgx_id]; rfl
          · intro _; rw [hgx]; simp [hvl]
        · have hne_v : z ≠ v'.id := by
            have := (RcCtx.get?_mem hgx).2; simp [v', this, hzx]
          refine ⟨hty_i.trans (congrArg (Option.map RcVar.ty) (get?_put_ne ctx hnd hne_v)),
            fun h => ?_⟩
          have h' := hlive_i h
          rw [get?_put_ne ctx hnd hne_v] at h'
          exact h'
      · exact (hinv_c 0).2.2.2 p hp
      · have hty_z := (hinv_c id).2.1
        have h1 : (((ctx.put v').invalidateChildren x).get? id).isSome =
            ((ctx.put v').get? id).isSome := by
          cases h : ((ctx.put v').invalidateChildren x).get? id <;>
            cases h' : (ctx.put v').get? id <;> simp_all
        rw [h1]
        exact get?_isSome_put ctx v' id hid
    · simp only [hty, Bool.false_eq_true, ↓reduceIte]
      simp

private theorem markExcl_ctx_props {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup) (tgt : Nat) :
    (∀ z, Option.map RcVar.ty ((ctx.markExcl tgt).get? z) = Option.map RcVar.ty (ctx.get? z) ∧
      (Option.map RcVar.isLive ((ctx.markExcl tgt).get? z) = some true →
        Option.map RcVar.isLive (ctx.get? z) = some true)) ∧
    (∀ p, p ∈ (ctx.markExcl tgt).sharedPreds → p ∈ ctx.sharedPreds) ∧
    (∀ id, (ctx.get? id).isSome = true → ((ctx.markExcl tgt).get? id).isSome = true) := by
  unfold RcCtx.markExcl
  cases hgt : ctx.get? tgt with
  | none => exact ⟨fun _ => ⟨rfl, fun h => h⟩, fun _ h => h, fun _ h => h⟩
  | some vt =>
    by_cases hcond : (!vt.noRc && !vt.persistent && vt.owned == 1) = true
    · simp only [hcond, ↓reduceIte]
      let vt' := { vt with excl := true }
      refine ⟨fun z => ?_, fun p hp => hp, fun id hid => get?_isSome_put ctx vt' id hid⟩
      by_cases hzt : z = vt.id
      · have hid' : vt'.id = vt.id := rfl
        have hget_vt := (RcCtx.mem_get?_iff hnd).mpr (RcCtx.get?_mem hgt).1
        rw [hzt, ← hid', get?_put_self ctx hnd vt', hid', hget_vt]
        exact ⟨rfl, fun h => h⟩
      · have hne : z ≠ vt'.id := by simpa [vt'] using hzt
        exact ⟨by rw [get?_put_ne ctx hnd hne], fun h => by rwa [get?_put_ne ctx hnd hne] at h⟩
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      simp

end Helpers

section StepLeafs

/-- Terminal simulation for `LcCode.unreach`. -/
public theorem unreach_step {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {Jh : HJEnv} {Jp : PResJEnv} {Qp : PResPost} {Xp : PResXPost}
    {Qh : HPost} {Xh : HXPost} {jps : List RcJpInfo} {rf : RcFrame} {σ : HState}
    {ρP : PValEnv} {rem wr rcr : Nat}
    (hpr : PRWp m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Qp Xp .unreach)
    (_hrc : RcInv rt rf σ)
    (hx : ∀ {c rem' wr' rcr' : Nat} {σ' : HState},
      Xp c rem' wr' rcr' → Xh (BitVec.ofNat 64 c) σ') :
    HWp Δh rt retTy Jh rf.envH Qh Xh .unreach σ := by
  have hpr' : Xp panicUnreachable rem wr rcr := hpr
  exact hx hpr'

private theorem ret_step_erased {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {Jh : HJEnv} {Jp : PResJEnv} {Qp : PResPost} {Xp : PResXPost}
    {Qh : HPost} {Xh : HXPost} {jps : List RcJpInfo} {rf0 rf : RcFrame} {σ0 σ : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr : Nat}
    {jumps : List (Nat × RcCtx)}
    (hcc : checkCode env retTy jps rf.ctx (.ret .erased) = .ok jumps)
    (hpw : perceusCodeWf env retTy jps rf.ctx sm (.ret .erased) = true)
    (hpr : PRWp m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Qp Xp (.ret .erased))
    (hrc : RcInv rt rf σ) (hep : EntryPres rf0 σ0 rf σ) (hres : ResStateInv σ rem wr rcr)
    (hq : ∀ {r : PVal} {rw : Word} {σ' : HState} {rem' wr' rcr' : Nat},
      Qp r rem' wr' rcr' → HeapClean rt σ' → ResStateInv σ' rem' wr' rcr' →
      ValRep retTy r rw σ'.objs →
      (¬retTy.isScalar = true → ¬retTy.needsRc = true →
        ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64) →
      HandlesRcSound (retHandles retTy rw ++ rf.extH ++ rf.ghostH) σ'.objs →
      EntryPres rf0 σ0 rf σ' → Qh rw σ') :
    HWp Δh rt retTy Jh rf.envH Qh Xh (.ret .erased) σ := by
  have hpw' : !retTy.isScalar = true ∧ (retTy != .object) = true ∧ (retTy != .tagged) = true := by
    have heq : perceusCodeWf env retTy jps rf.ctx sm (.ret .erased) =
        (argScalarInit sm .erased && !retTy.isScalar &&
          retTy != .object && retTy != .tagged) := rfl
    rw [heq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hpw
    exact ⟨hpw.1.1.2, hpw.1.2, hpw.2⟩
  have hns : retTy.isScalar = false := by simpa using hpw'.1
  have hne_obj : retTy ≠ .object := by
    intro h; subst h; cases hpw'.2.1
  have hne_tag : retTy ≠ .tagged := by
    intro h; subst h; cases hpw'.2.2
  have hw64 : retTy.width = 64 := ty_width_of_not_scalar hns
  have hnl : rf.ctx.checkNoLeaks [] = .ok () := by
    rw [checkCode.eq_5] at hcc
    cases hnr : retTy.needsRc <;>
      · simp only [hnr, Bool.false_eq_true, ↓reduceIte, RcCtx.checkArgLive, RcCtx.consumeArg,
          bind, Except.bind, pure, Except.pure] at hcc
        cases h0 : rf.ctx.checkNoLeaks with
        | error e => simp [h0] at hcc
        | ok u => cases u; rfl
  have hlh : localHandles rf.ctx rf.envH = [] := localHandles_eq_nil_of_checkNoLeaks hnl
  have hvr : ValRep retTy .erased (Word.i64 1#64) σ.objs := by
    simp only [ValRep, hns, Bool.false_eq_true, ↓reduceIte, ObjRep.eq_1]
    exact ⟨1#64, rfl, rfl, fun h => absurd h hne_obj, fun h => absurd h hne_tag⟩
  have hreth : retHandles retTy (Word.i64 1#64) = [] := by
    unfold retHandles
    cases hnr : retTy.needsRc <;> simp [hns, Word.toBV64?, Word.i64]
  have hsnd : HandlesRcSound (retHandles retTy (Word.i64 1#64) ++ rf.extH ++ rf.ghostH)
      σ.objs := by
    rw [hreth, List.nil_append]
    have hfrm : frameHandles rf = rf.extH ++ rf.ghostH := by
      simp [frameHandles, hlh]
    rw [← hfrm]; exact hrc.2.2.1
  have hev_at : rf.envH.evalArgAt .erased retTy = some (Word.i64 1#64) := by
    simp only [HValEnv.evalArgAt, hns, LcTy.toTTy]
    rw [hw64]; rfl
  have hpr' : Qp .erased rem wr rcr := hpr
  have hwp_eq : HWp Δh rt retTy Jh rf.envH Qh Xh (.ret .erased) σ =
      match rf.envH.evalArgAt .erased retTy with
      | some w => Qh w σ
      | none => False := rfl
  rw [hwp_eq, hev_at]
  exact hq hpr' hrc.1 hres hvr (fun _ _ => ⟨1#64, rfl, by decide⟩) hsnd hep

private theorem ret_step_var {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {Jh : HJEnv} {Jp : PResJEnv} {Qp : PResPost} {Xp : PResXPost}
    {Qh : HPost} {Xh : HXPost} {jps : List RcJpInfo} {rf0 rf : RcFrame} {σ0 σ : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr y : Nat}
    {jumps : List (Nat × RcCtx)}
    (hcc : checkCode env retTy jps rf.ctx (.ret (.var y)) = .ok jumps)
    (hpw : perceusCodeWf env retTy jps rf.ctx sm (.ret (.var y)) = true)
    (hpr : PRWp m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Qp Xp (.ret (.var y)))
    (hrc : RcInv rt rf σ) (hcl : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hno : NoRcCorrect rf.ctx) (hep : EntryPres rf0 σ0 rf σ) (hsh : ShadowOk sm rf.ctx ρP rf.envP)
    (hres : ResStateInv σ rem wr rcr)
    (hq : ∀ {r : PVal} {rw : Word} {σ' : HState} {rem' wr' rcr' : Nat},
      Qp r rem' wr' rcr' → HeapClean rt σ' → ResStateInv σ' rem' wr' rcr' →
      ValRep retTy r rw σ'.objs →
      (¬retTy.isScalar = true → ¬retTy.needsRc = true →
        ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64) →
      HandlesRcSound (retHandles retTy rw ++ rf.extH ++ rf.ghostH) σ'.objs →
      EntryPres rf0 σ0 rf σ' → Qh rw σ') :
    HWp Δh rt retTy Jh rf.envH Qh Xh (.ret (.var y)) σ := by
  have hpw_eq : perceusCodeWf env retTy jps rf.ctx sm (.ret (.var y)) =
      (isVarScalarInit sm y &&
        match rf.ctx.get? y with
        | some vx =>
          (vx.ty.isScalar == retTy.isScalar) && (vx.ty.width == retTy.width) &&
            ((retTy.needsRc == vx.ty.needsRc) || (retTy == .tagged && vx.ty == .tobject) ||
              (!retTy.isScalar && !retTy.needsRc && vx.noRc)) &&
            decide ((retTy == .object) = true → (vx.ty == .object) = true) &&
            decide ((retTy == .tagged) = true → (vx.ty == .tagged) = true)
        | none => false) := rfl
  rw [hpw_eq, Bool.and_eq_true] at hpw
  rcases hpw with ⟨hinit, hvy_chk⟩
  cases hgety : rf.ctx.get? y with
  | none => simp [hgety] at hvy_chk
  | some vy =>
    simp only [hgety, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      beq_iff_eq] at hvy_chk
    rcases hvy_chk with ⟨⟨⟨⟨hsc_eq, hw_eq⟩, hnrc_chk⟩, hobj_imp⟩, htag_imp⟩
    have hpr' : ∃ pv, ρP y = some pv ∧ Qp pv rem wr rcr := by
      have heq : PRWp m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Qp Xp (.ret (.var y)) =
          match ρP y with | some r => Qp r rem wr rcr | none => False := rfl
      rw [heq] at hpr
      cases hρ : ρP y with
      | none => rw [hρ] at hpr; exact False.elim hpr
      | some pv => rw [hρ] at hpr; exact ⟨pv, rfl, hpr⟩
    rcases hpr' with ⟨pv_y, hρy, hQp⟩
    have hcc_eq : checkCode env retTy jps rf.ctx (.ret (.var y)) =
        (if retTy.needsRc = true then
          rf.ctx.consumeVar y >>= fun ctx1 => ctx1.checkNoLeaks [] >>= fun _ => .ok []
         else
          rf.ctx.checkLive y >>= fun _ => rf.ctx.checkNoLeaks [] >>= fun _ => .ok []) := rfl
    rw [hcc_eq] at hcc
    have hlive_y : vy.isLive = true := by
      cases hnr : retTy.needsRc with
      | false =>
        simp only [hnr, Bool.false_eq_true, ↓reduceIte] at hcc
        cases hclv : rf.ctx.checkLive y with
        | error e => simp [hclv, bind, Except.bind] at hcc
        | ok _ =>
          obtain ⟨v0, hg0, hl0⟩ := checkLive_facts hclv
          rw [hg0] at hgety; cases hgety; exact hl0
      | true =>
        simp only [hnr, ↓reduceIte] at hcc
        cases hcons : rf.ctx.consumeVar y with
        | error e => simp [hcons, bind, Except.bind] at hcc
        | ok ctx1 =>
          unfold RcCtx.consumeVar at hcons
          rw [hgety] at hcons
          by_cases h1 : vy.noRc = true
          · simp [RcVar.isLive, h1]
          · by_cases h2 : vy.persistent = true
            · simp [RcVar.isLive, h2]
            · have h1f : vy.noRc = false := Bool.eq_false_iff.mpr h1
              have h2f : vy.persistent = false := Bool.eq_false_iff.mpr h2
              simp only [h1f, h2f, Bool.or_self,
                beq_false_of_ne (by decide : (1 : Nat) ≠ 0)] at hcons
              by_cases hlt : vy.owned < 1
              · simp [hlt] at hcons
              · simp [RcVar.isLive]; omega
    have hsh_y := hsh vy (RcCtx.get?_mem hgety).1 hlive_y
    rw [(RcCtx.get?_mem hgety).2, hinit] at hsh_y
    simp only [↓reduceIte] at hsh_y
    obtain ⟨pv_y', w_y, hev_py, hev_hy, hvr_y, hnorc_y⟩ :=
      hrc.2.2.2.1 vy (RcCtx.get?_mem hgety).1 hlive_y
    rw [(RcCtx.get?_mem hgety).2] at hev_py hev_hy
    rw [← hsh_y, hρy] at hev_py; cases hev_py
    have hwt_y : w_y.fst = retTy.toTTy := by
      unfold ValRep at hvr_y
      by_cases hvy_s : vy.ty.isScalar = true
      · simp only [hvy_s, ↓reduceIte, ScalarRep] at hvr_y
        rcases hvr_y with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩ <;>
          simp [LcTy.toTTy, hw_eq]
      · have hvy_ns : vy.ty.isScalar = false := Bool.eq_false_iff.mpr hvy_s
        simp only [hvy_ns, Bool.false_eq_true, ↓reduceIte] at hvr_y
        rcases hvr_y with ⟨bv, rfl, _⟩
        have hret_ns : retTy.isScalar = false := by rw [← hsc_eq, hvy_ns]
        have hret_w : retTy.width = 64 := ty_width_of_not_scalar hret_ns
        simp [Word.i64, LcTy.toTTy, hret_w]
    have hev_at : rf.envH.evalArgAt (.var y) retTy = some w_y := by
      simp [HValEnv.evalArgAt, hev_hy, hwt_y]
    have hvr_ret : ValRep retTy pv_y w_y σ.objs :=
      valRep_cast hvr_y hsc_eq hw_eq
        (fun h => (lcTy_beq_iff vy.ty .object).mp (hobj_imp ((lcTy_beq_iff retTy .object).mpr h)))
        (fun h => (lcTy_beq_iff vy.ty .tagged).mp (htag_imp ((lcTy_beq_iff retTy .tagged).mpr h)))
    have hno_ret : ¬retTy.isScalar = true → ¬retTy.needsRc = true →
        ∃ bv, w_y = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64 := by
      intro hns hnnr
      have hvy_ns : ¬vy.ty.isScalar = true := by rw [hsc_eq]; exact hns
      by_cases htag : retTy = .tagged
      · subst htag
        simp only [ValRep, LcTy.isScalar, Bool.false_eq_true, ↓reduceIte] at hvr_ret
        rcases hvr_ret with ⟨bv, hw_bv, _, _, htag_odd⟩
        exact ⟨bv, hw_bv, htag_odd trivial⟩
      · have hvy_no : vy.noRc = true := by
          have hnr_f : retTy.needsRc = false := Bool.eq_false_iff.mpr hnnr
          rcases hnrc_chk with (h1 | h2) | h3
          · have hvy_nr : vy.ty.needsRc = false := h1.symm.trans hnr_f
            cases hvyno : vy.noRc with
            | true => rfl
            | false =>
              exact absurd (hno vy (RcCtx.get?_mem hgety).1 hvyno) (by simp [hvy_nr])
          · exact absurd h2.1 (fun h => htag ((lcTy_beq_iff retTy .tagged).mp h))
          · exact h3.2
        obtain ⟨bv, hw_bv, hno_bv, _⟩ := hnorc_y hvy_ns
        exact ⟨bv, hw_bv, hno_bv hvy_no⟩
    have hsnd : HandlesRcSound (retHandles retTy w_y ++ rf.extH ++ rf.ghostH) σ.objs := by
      cases hnr : retTy.needsRc with
      | false =>
        simp only [hnr, Bool.false_eq_true, ↓reduceIte] at hcc
        cases hclv : rf.ctx.checkLive y with
        | error e => simp [hclv, bind, Except.bind] at hcc
        | ok _ =>
          simp only [hclv, bind, Except.bind] at hcc
          cases hnl : rf.ctx.checkNoLeaks [] with
          | error e => simp [hnl] at hcc
          | ok _ =>
            have hlh := localHandles_eq_nil_of_checkNoLeaks (envH := rf.envH) hnl
            have hreth : retHandles retTy w_y = [] := by unfold retHandles; simp [hnr]
            rw [hreth, List.nil_append]
            have hfrm : frameHandles rf = rf.extH ++ rf.ghostH := by
              simp [frameHandles, hlh]
            rw [← hfrm]; exact hrc.2.2.1
      | true =>
        simp only [hnr, ↓reduceIte] at hcc
        cases hcons : rf.ctx.consumeVar y with
        | error e => simp [hcons, bind, Except.bind] at hcc
        | ok ctx1 =>
          simp only [hcons, bind, Except.bind] at hcc
          cases hnl : ctx1.checkNoLeaks [] with
          | error e => simp [hnl] at hcc
          | ok _ =>
            have hret_ns : retTy.isScalar = false := by
              cases retTy <;> simp_all [LcTy.needsRc, LcTy.isScalar]
            have hvy_ns : ¬vy.ty.isScalar = true := by rw [hsc_eq]; simp [hret_ns]
            obtain ⟨bv, hw_bv, hno_bv, hpers_bv, _, _⟩ := hnorc_y hvy_ns
            have hev_y_bv : rf.envH y = some (vy.ty, Word.i64 bv) := by
              rw [← hw_bv]; exact hev_hy
            have hlh1 : localHandles ctx1 rf.envH = [] := localHandles_eq_nil_of_checkNoLeaks hnl
            have hsh_tgt : ∀ p ∈ rf.ctx.sharedPreds, p.2 = y →
                ∀ v, rf.ctx.get? y = some v →
                  v.noRc = true ∨ v.persistent = true ∨ 1 = 0 ∨ v.owned ≤ 1 := by
              intro p _ _ v hgv
              rw [hgety] at hgv; cases hgv
              by_cases h1 : vy.noRc = true
              · exact Or.inl h1
              · by_cases h2 : vy.persistent = true
                · exact Or.inr (Or.inl h2)
                · have h1f : vy.noRc = false := Bool.eq_false_iff.mpr h1
                  have h2f : vy.persistent = false := Bool.eq_false_iff.mpr h2
                  have hcons' := hcons
                  unfold RcCtx.consumeVar at hcons'
                  rw [hgety] at hcons'
                  dsimp only at hcons'
                  rw [h1f, h2f] at hcons'
                  simp only [Bool.or_self, Bool.false_eq_true,
                    beq_false_of_ne (by decide : (1 : Nat) ≠ 0), ↓reduceIte] at hcons'
                  by_cases hlt : vy.owned < 1
                  · simp [hlt] at hcons'
                  · simp only [hlt, ↓reduceIte] at hcons'
                    let v' : RcVar := {
                      vy with
                      noRc := false
                      persistent := false
                      owned := vy.owned - 1
                      excl := if vy.owned - 1 == 0 then false else vy.excl
                      resetTok := if vy.owned - 1 == 0 then false else vy.resetTok }
                    have hw_ex : ∃ w ∈ ctx1.vars, w.id = y ∧ w.noRc = false ∧
                        w.persistent = false ∧ w.owned = vy.owned - 1 := by
                      have hv'm : v' ∈ (rf.ctx.put v').vars :=
                        (RcCtx.put_mem_iff hrc.2.1).mpr (Or.inl rfl)
                      have hv'id : v'.id = y := (RcCtx.get?_mem hgety).2
                      by_cases hinv : (vy.owned - 1 == 0 && !vy.borrowed) = true
                      · simp only [hinv, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hcons'
                        let u' : RcVar :=
                          if v'.parent? == some y then
                            { v' with borrowed := false, parent? := none }
                          else v'
                        refine ⟨u', ?_, ?_⟩
                        · rw [← hcons']
                          exact List.mem_map.mpr ⟨v', hv'm, rfl⟩
                        · dsimp only [u']
                          by_cases hp : (v'.parent? == some y) = true <;>
                            simp [hp, v', hv'id]
                      · simp only [hinv, Bool.false_eq_true, ↓reduceIte,
                          pure, Except.pure, Except.ok.injEq] at hcons'
                        refine ⟨v', ?_, hv'id, rfl, rfl, rfl⟩
                        rw [← hcons']; exact hv'm
                    obtain ⟨w, hw_m, _, hw_no, hw_ps, hw_ow⟩ := hw_ex
                    have hchk_w := checkNoLeaks_spec hnl w hw_m (by simp)
                    simp only [hw_no, hw_ps, Bool.false_or, beq_iff_eq, hw_ow] at hchk_w
                    exact Or.inr (Or.inr (Or.inr (by omega)))
            obtain ⟨hperm, _⟩ := rcInv_consumeVar_step hrc hcl hpo hcons hsh_tgt
            rw [hlh1, List.nil_append] at hperm
            by_cases h1 : vy.noRc = true
            · have hodd := hno_bv h1
              have hreth : retHandles retTy w_y = [] := by
                rw [hw_bv]; simp [retHandles, hnr, hret_ns, Word.toBV64?, Word.i64, hodd]
              have hch : consumeVarHandles rf y 1 = [] := by
                simp [consumeVarHandles, hgety, h1]
              rw [hch] at hperm
              have hfrm : (frameHandles rf).Perm (rf.extH ++ rf.ghostH) := by
                unfold frameHandles
                simpa [List.nil_append] using (hperm.append_right rf.extH).append_right rf.ghostH
              rw [hreth, List.nil_append]
              exact handlesRcSound_of_perm hfrm hrc.2.2.1
            · by_cases h2 : vy.persistent = true
              · have hch : consumeVarHandles rf y 1 = [] := by
                  simp [consumeVarHandles, hgety, h2]
                rw [hch] at hperm
                have hfrm : (frameHandles rf).Perm (rf.extH ++ rf.ghostH) := by
                  unfold frameHandles
                  simpa [List.nil_append] using
                    (hperm.append_right rf.extH).append_right rf.ghostH
                have hsnd_ext := handlesRcSound_of_perm hfrm hrc.2.2.1
                by_cases heven : bv &&& 1#64 = 0#64
                · obtain ⟨o, ho, hoa, horc0⟩ := hpers_bv h2 heven
                  have hreth : retHandles retTy w_y = [bv] := by
                    rw [hw_bv]
                    simp [retHandles, hnr, hret_ns, Word.toBV64?, Word.i64, heven]
                  rw [hreth, List.singleton_append]
                  exact handlesRcSound_add_persist_ret hsnd_ext hrc.1.2 ho hoa horc0
                · have hreth : retHandles retTy w_y = [] := by
                    rw [hw_bv]
                    simp [retHandles, hnr, hret_ns, Word.toBV64?, Word.i64, heven]
                  rw [hreth, List.nil_append]; exact hsnd_ext
              · have h1f : vy.noRc = false := Bool.eq_false_iff.mpr h1
                have h2f : vy.persistent = false := Bool.eq_false_iff.mpr h2
                have hch : consumeVarHandles rf y 1 = retHandles retTy w_y := by
                  rw [hw_bv]
                  simp only [consumeVarHandles, hgety, h1f, h2f, Bool.or_self,
                    Bool.false_eq_true, beq_false_of_ne (by decide : (1 : Nat) ≠ 0),
                    ↓reduceIte, hev_y_bv, Word.toBV64?, Word.i64, List.replicate_one,
                    retHandles, hnr, hret_ns, Bool.true_and, Bool.not_false]
                rw [hch] at hperm
                have hfrm : (frameHandles rf).Perm
                    (retHandles retTy w_y ++ rf.extH ++ rf.ghostH) := by
                  unfold frameHandles
                  simpa [List.append_assoc] using
                    (hperm.append_right rf.extH).append_right rf.ghostH
                exact handlesRcSound_of_perm hfrm hrc.2.2.1
    have hwp_eq : HWp Δh rt retTy Jh rf.envH Qh Xh (.ret (.var y)) σ =
        match rf.envH.evalArgAt (.var y) retTy with
        | some w => Qh w σ
        | none => False := rfl
    rw [hwp_eq, hev_at]
    exact hq hQp hrc.1 hres hvr_ret hno_ret hsnd hep

/-- Terminal simulation for `LcCode.ret`. -/
public theorem ret_step {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {Jh : HJEnv} {Jp : PResJEnv} {Qp : PResPost} {Xp : PResXPost}
    {Qh : HPost} {Xh : HXPost} {jps : List RcJpInfo} {rf0 rf : RcFrame} {σ0 σ : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr : Nat} {a : LcArg}
    {jumps : List (Nat × RcCtx)}
    (hcc : checkCode env retTy jps rf.ctx (.ret a) = .ok jumps)
    (hpw : perceusCodeWf env retTy jps rf.ctx sm (.ret a) = true)
    (hpr : PRWp m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Qp Xp (.ret a))
    (hrc : RcInv rt rf σ) (hcl : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hno : NoRcCorrect rf.ctx) (hep : EntryPres rf0 σ0 rf σ) (hsh : ShadowOk sm rf.ctx ρP rf.envP)
    (hres : ResStateInv σ rem wr rcr)
    (hq : ∀ {r : PVal} {rw : Word} {σ' : HState} {rem' wr' rcr' : Nat},
      Qp r rem' wr' rcr' → HeapClean rt σ' → ResStateInv σ' rem' wr' rcr' →
      ValRep retTy r rw σ'.objs →
      (¬retTy.isScalar = true → ¬retTy.needsRc = true →
        ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64) →
      HandlesRcSound (retHandles retTy rw ++ rf.extH ++ rf.ghostH) σ'.objs →
      EntryPres rf0 σ0 rf σ' → Qh rw σ') :
    HWp Δh rt retTy Jh rf.envH Qh Xh (.ret a) σ := by
  cases a with
  | erased => exact ret_step_erased hcc hpw hpr hrc hep hres hq
  | var y => exact ret_step_var hcc hpw hpr hrc hcl hpo hno hep hsh hres hq

end StepLeafs

section BodyHelpers

public theorem perceusModWf_facts {m : LcModule} (hmwf : perceusModWf m = true) :
    (m.decls.map LcDecl.name).Nodup ∧
    ∀ d ∈ m.decls, !isPrimName d.name = true ∧ (d.params.map LcParam.id).Nodup ∧
      perceusCodeWf (mkRcModEnv m) d.retTy [] ((RcCtx.mk [] []).bindParams d.params) []
        d.body = true := by
  unfold perceusModWf at hmwf
  simp only [Bool.and_eq_true, List.all_eq_true] at hmwf
  refine ⟨of_decide_eq_true hmwf.1, fun d hd => ?_⟩
  have h0 := hmwf.2 d hd
  simp only [decide_eq_true_eq] at h0
  exact ⟨h0.1.1, h0.1.2, h0.2⟩

public theorem exclCtorHeap_init (ps : List LcParam) (envP : PValEnv) (envH : HValEnv)
    (extH ghostH : List (BitVec 64)) :
    ExclCtorHeap
      { ctx := (RcCtx.mk [] []).bindParams ps, envP := envP, envH := envH,
        extH := extH, ghostH := ghostH } := by
  suffices h : ∀ (ctx : RcCtx), (ctx.vars.map RcVar.id).Nodup →
      (∀ u ∈ ctx.vars, u.excl = false) → ∀ u ∈ (ctx.bindParams ps).vars, u.excl = false by
    intro u hu _ hexcl
    have h0 := h { vars := [], sharedPreds := [] } (by simp) (fun _ hm => nomatch hm) u hu
    rw [h0] at hexcl; cases hexcl
  intro ctx hnd hctx
  induction ps generalizing ctx with
  | nil => exact hctx
  | cons p ps ih =>
    simp only [RcCtx.bindParams, List.foldl_cons]
    cases hb : p.borrow with
    | true =>
      simp only [↓reduceIte]
      refine ih _ (ctx.put_nodup hnd _) (fun u hu => ?_)
      rcases (RcCtx.put_mem_iff hnd).mp hu with rfl | ⟨hm, _⟩
      · rfl
      · exact hctx u hm
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ih _ (ctx.put_nodup hnd _) (fun u hu => ?_)
      rcases (RcCtx.put_mem_iff hnd).mp hu with rfl | ⟨hm, _⟩
      · dsimp only [RcCtx.bindOwned]; split <;> rfl
      · exact hctx u hm

private theorem jpsScopeIn_consumeVar {jps : List RcJpInfo} {ctx ctx' : RcCtx}
    (hnd : (ctx.vars.map RcVar.id).Nodup) {x n : Nat}
    (hc : ctx.consumeVar x n = .ok ctx') (hs : JpsScopeIn jps ctx) : JpsScopeIn jps ctx' :=
  jpsScopeIn_mono hs (consumeVar_ctx_props hnd hc).2.2.1

private theorem jpsScopeIn_consumeArg {jps : List RcJpInfo} {ctx ctx' : RcCtx}
    (hnd : (ctx.vars.map RcVar.id).Nodup) {a : LcArg}
    (hc : ctx.consumeArg a = .ok ctx') (hs : JpsScopeIn jps ctx) : JpsScopeIn jps ctx' := by
  cases a with
  | erased => simp [RcCtx.consumeArg, pure, Except.pure] at hc; subst hc; exact hs
  | var x => exact jpsScopeIn_consumeVar hnd hc hs

private theorem consumeArg_ctx_props {ctx ctx' : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (_hcl : CleanVars ctx) {a : LcArg} (hc : ctx.consumeArg a = .ok ctx') :
    (∀ z, Option.map RcVar.ty (ctx'.get? z) = Option.map RcVar.ty (ctx.get? z) ∧
      (Option.map RcVar.isLive (ctx'.get? z) = some true →
        Option.map RcVar.isLive (ctx.get? z) = some true)) ∧
    (∀ p, p ∈ ctx'.sharedPreds → p ∈ ctx.sharedPreds) := by
  cases a with
  | erased =>
    simp [RcCtx.consumeArg, pure, Except.pure] at hc
    subst hc; exact ⟨fun _ => ⟨rfl, fun h => h⟩, fun _ h => h⟩
  | var x =>
    have hp := consumeVar_ctx_props hnd hc
    exact ⟨hp.1, hp.2.1⟩

private theorem consumeArg_sharedBoolPreds {ctx ctx' : RcCtx}
    (hnd : (ctx.vars.map RcVar.id).Nodup) (hsbp : SharedBoolPreds ctx) {a : LcArg}
    (hc : ctx.consumeArg a = .ok ctx') : SharedBoolPreds ctx' := by
  cases a with
  | erased => simp [RcCtx.consumeArg, pure, Except.pure] at hc; subst hc; exact hsbp
  | var x => exact sharedBoolPreds_consumeVar hnd hsbp hc

private theorem ctx_props_refl (ctx : RcCtx) :
    ((∀ z, Option.map RcVar.ty (ctx.get? z) = Option.map RcVar.ty (ctx.get? z) ∧
      (Option.map RcVar.isLive (ctx.get? z) = some true →
        Option.map RcVar.isLive (ctx.get? z) = some true)) ∧
      (∀ p, p ∈ ctx.sharedPreds → p ∈ ctx.sharedPreds)) ∧
    (∀ id, (ctx.get? id).isSome = true → (ctx.get? id).isSome = true) :=
  ⟨⟨fun _ => ⟨rfl, fun h => h⟩, fun _ h => h⟩, fun _ h => h⟩

private theorem ctx_props_trans {ctx0 ctx1 ctx2 : RcCtx}
    (h1 : ((∀ z, Option.map RcVar.ty (ctx1.get? z) = Option.map RcVar.ty (ctx0.get? z) ∧
        (Option.map RcVar.isLive (ctx1.get? z) = some true →
          Option.map RcVar.isLive (ctx0.get? z) = some true)) ∧
        (∀ p, p ∈ ctx1.sharedPreds → p ∈ ctx0.sharedPreds)) ∧
      (∀ id, (ctx0.get? id).isSome = true → (ctx1.get? id).isSome = true))
    (h2 : ((∀ z, Option.map RcVar.ty (ctx2.get? z) = Option.map RcVar.ty (ctx1.get? z) ∧
        (Option.map RcVar.isLive (ctx2.get? z) = some true →
          Option.map RcVar.isLive (ctx1.get? z) = some true)) ∧
        (∀ p, p ∈ ctx2.sharedPreds → p ∈ ctx1.sharedPreds)) ∧
      (∀ id, (ctx1.get? id).isSome = true → (ctx2.get? id).isSome = true)) :
    ((∀ z, Option.map RcVar.ty (ctx2.get? z) = Option.map RcVar.ty (ctx0.get? z) ∧
        (Option.map RcVar.isLive (ctx2.get? z) = some true →
          Option.map RcVar.isLive (ctx0.get? z) = some true)) ∧
        (∀ p, p ∈ ctx2.sharedPreds → p ∈ ctx0.sharedPreds)) ∧
      (∀ id, (ctx0.get? id).isSome = true → (ctx2.get? id).isSome = true) :=
  ⟨⟨fun z => ⟨(h2.1.1 z).1.trans (h1.1.1 z).1, fun h => (h1.1.1 z).2 ((h2.1.1 z).2 h)⟩,
    fun p hp => h1.1.2 p (h2.1.2 p hp)⟩, fun id hid => h2.2 id (h1.2 id hid)⟩

private theorem casesBranchCtx_props {env : RcModEnv} {ctx : RcCtx}
    (hnd : (ctx.vars.map RcVar.id).Nodup) {x : Nat}
    (hx : ∀ v, ctx.get? x = some v → v.isLive = true)
    (target? : Option Nat) (pat : LcPat) :
    ((∀ z, Option.map RcVar.ty ((casesBranchCtx env target? pat x ctx).get? z) =
        Option.map RcVar.ty (ctx.get? z) ∧
      (Option.map RcVar.isLive ((casesBranchCtx env target? pat x ctx).get? z) = some true →
        Option.map RcVar.isLive (ctx.get? z) = some true)) ∧
      (∀ p, p ∈ (casesBranchCtx env target? pat x ctx).sharedPreds → p ∈ ctx.sharedPreds)) ∧
    (∀ id, (ctx.get? id).isSome = true →
      ((casesBranchCtx env target? pat x ctx).get? id).isSome = true) := by
  let ctx1 := match pat with
    | .ctor _ cname => if env.scalarCtors.contains cname then ctx.markScalarBranch x else ctx
    | .dflt => ctx
  have h1 : ((∀ z, Option.map RcVar.ty (ctx1.get? z) = Option.map RcVar.ty (ctx.get? z) ∧
      (Option.map RcVar.isLive (ctx1.get? z) = some true →
        Option.map RcVar.isLive (ctx.get? z) = some true)) ∧
      (∀ p, p ∈ ctx1.sharedPreds → p ∈ ctx.sharedPreds)) ∧
      (∀ id, (ctx.get? id).isSome = true → (ctx1.get? id).isSome = true) := by
    cases pat with
    | dflt => exact ctx_props_refl ctx
    | ctor ci cname =>
      by_cases hsc : env.scalarCtors.contains cname = true
      · dsimp only [ctx1]; rw [ite_eq_left hsc]
        have hms := markScalarBranch_ctx_props hnd hx
        exact ⟨⟨hms.1, hms.2.1⟩, hms.2.2⟩
      · dsimp only [ctx1]; rw [ite_eq_right hsc]; exact ctx_props_refl ctx
  have hnd1 : (ctx1.vars.map RcVar.id).Nodup := by
    cases pat with
    | dflt => exact hnd
    | ctor ci cname =>
      by_cases hsc : env.scalarCtors.contains cname = true
      · dsimp only [ctx1]; rw [ite_eq_left hsc]
        unfold RcCtx.markScalarBranch
        cases hgx : ctx.get? x with
        | none => exact hnd
        | some v =>
          by_cases hty : (v.ty == .tobject || v.ty == .tagged) = true
          · simp only [hty, ↓reduceIte]
            exact (invalidateChildren_live_ty_back _ (ctx.put_nodup hnd _) x 0).1
          · simp only [hty, Bool.false_eq_true, ↓reduceIte]; exact hnd
      · dsimp only [ctx1]; rw [ite_eq_right hsc]; exact hnd
  have h2 : ((∀ z, Option.map RcVar.ty ((casesBranchCtx env target? pat x ctx).get? z) =
        Option.map RcVar.ty (ctx1.get? z) ∧
      (Option.map RcVar.isLive ((casesBranchCtx env target? pat x ctx).get? z) = some true →
        Option.map RcVar.isLive (ctx1.get? z) = some true)) ∧
      (∀ p, p ∈ (casesBranchCtx env target? pat x ctx).sharedPreds → p ∈ ctx1.sharedPreds)) ∧
      (∀ id, (ctx1.get? id).isSome = true →
        ((casesBranchCtx env target? pat x ctx).get? id).isSome = true) := by
    cases target? with
    | none =>
      have heq : casesBranchCtx env none pat x ctx = ctx1 := by
        cases pat with
        | dflt => rfl
        | ctor ci _ => cases ci <;> rfl
      rw [heq]; exact ctx_props_refl ctx1
    | some tgt =>
      cases pat with
      | dflt => exact ctx_props_refl ctx1
      | ctor ci cname =>
        cases ci with
        | zero =>
          have heq : casesBranchCtx env (some tgt) (.ctor 0 cname) x ctx = ctx1.markExcl tgt := rfl
          rw [heq]
          have hme := markExcl_ctx_props hnd1 tgt
          exact ⟨⟨hme.1, hme.2.1⟩, hme.2.2⟩
        | succ m0 =>
          have heq : casesBranchCtx env (some tgt) (.ctor (m0 + 1) cname) x ctx = ctx1 := rfl
          rw [heq]; exact ctx_props_refl ctx1
  exact ctx_props_trans h1 h2

private theorem checkCode_inc_ctx {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {x n : Nat} {chk : Bool} {k : LcCode} {jumps : List (Nat × RcCtx)}
    (hcc : checkCode env retTy jps ctx (.inc x n chk k) = .ok jumps) :
    ∃ v, ctx.get? x = some v ∧ v.isLive = true ∧
      checkCode env retTy jps
        (if v.noRc || v.persistent || n == 0 then ctx
         else ctx.put { v with owned := v.owned + n, excl := false }) k = .ok jumps := by
  rw [checkCode.eq_11] at hcc
  cases hgx : ctx.get? x with
  | none => rw [hgx] at hcc; cases hcc
  | some v =>
    rw [hgx] at hcc
    dsimp only at hcc
    by_cases hnl : (!v.isLive) = true
    · simp [hnl, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hcc
    · have hvl : v.isLive = true := by cases h : v.isLive <;> simp_all
      simp only [hnl, Bool.false_eq_true, ↓reduceIte] at hcc
      refine ⟨v, rfl, hvl, ?_⟩
      by_cases hsk : (v.noRc || v.persistent || n == 0) = true <;>
        simp [hsk] at hcc ⊢ <;> exact hcc

private theorem jpsOk_mut_step_sameEnvH {rt : BitVec 64} {rf0 : RcFrame} {σ0 : HState}
    {Jp : PResJEnv} {Jh : HJEnv} {jpsOk : List JpEntry} {rf : RcFrame} {ρP ρP' : PValEnv}
    {jumps jumps' : List (Nat × RcCtx)} {ctx' : RcCtx} {envP' : PValEnv} {envH' : HValEnv}
    {ghostH' : List (BitVec 64)} {x : Nat}
    (hjps : JpsOk rt rf0 σ0 Jp Jh jpsOk rf ρP jumps)
    (hstep : (∀ z, Option.map RcVar.ty (ctx'.get? z) = Option.map RcVar.ty (rf.ctx.get? z) ∧
        (Option.map RcVar.isLive (ctx'.get? z) = some true →
          Option.map RcVar.isLive (rf.ctx.get? z) = some true)) ∧
      (∀ p, p ∈ ctx'.sharedPreds → p ∈ rf.ctx.sharedPreds))
    (henvH : envH' = rf.envH)
    (henv : ∀ z ≠ x, envP' z = rf.envP z ∧ ρP' z = ρP z)
    (hjumps : ∀ jc ∈ jumps', jc ∈ jumps) :
    JpsOk rt rf0 σ0 Jp Jh
      (jpsOk.map fun e => { e with mutVars := x :: e.mutVars })
      { ctx := ctx', envP := envP', envH := envH', extH := rf.extH, ghostH := ghostH' }
      ρP' jumps' := by
  intro e' he'
  rcases List.mem_map.mp he' with ⟨e, he, rfl⟩
  obtain ⟨hok, hlive, hw⟩ := hjps e he
  refine ⟨hok, ⟨fun id hid hnot hl => ?_, fun p hp h1 hnot => ?_⟩,
    fun jc hjc hjeq => hw jc (hjumps jc hjc) hjeq⟩
  · have hne : id ≠ x := fun hx => hnot (hx ▸ List.mem_cons_self)
    have hnot' : id ∉ e.mutVars := fun hm => hnot (List.mem_cons_of_mem x hm)
    obtain ⟨heP, heH, hrP, hty, hl0⟩ := hlive.1 id hid hnot' ((hstep.1 id).2 hl)
    obtain ⟨hnP, hnR⟩ := henv id hne
    exact ⟨hnP.trans heP, (congrFun henvH id).trans heH, hnR.trans hrP,
      (hstep.1 id).1.trans hty, hl0⟩
  · have hnot' : p.1 ∉ e.mutVars := fun hm => hnot (List.mem_cons_of_mem x hm)
    obtain ⟨hp0, heH, hty⟩ := hlive.2 p (hstep.2 p hp) h1 hnot'
    exact ⟨hp0, (congrFun henvH p.2).trans heH, (hstep.1 p.2).1.trans hty⟩

private theorem checkCode_uset_unwrap {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {x i y : Nat} {k : LcCode} {jumps : List (Nat × RcCtx)}
    (hcc : checkCode env retTy jps ctx (.uset x i y k) = .ok jumps) :
    ctx.checkExcl x "uset" = .ok () ∧ ctx.checkLive y = .ok () ∧
      checkCode env retTy jps ctx k = .ok jumps := by
  rw [checkCode.eq_8] at hcc
  cases hc1 : ctx.checkExcl x "uset" with
  | error e => rw [hc1] at hcc; cases hcc
  | ok _ =>
    simp only [hc1, Bind.bind, Except.bind] at hcc
    cases hc2 : ctx.checkLive y with
    | error e => rw [hc2] at hcc; cases hcc
    | ok _ => simp only [hc2] at hcc; exact ⟨rfl, rfl, hcc⟩

private theorem checkCode_sset_unwrap {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {x n off y : Nat} {ty : LcTy} {k : LcCode} {jumps : List (Nat × RcCtx)}
    (hcc : checkCode env retTy jps ctx (.sset x n off y ty k) = .ok jumps) :
    ctx.checkExcl x "sset" = .ok () ∧ ctx.checkLive y = .ok () ∧
      checkCode env retTy jps ctx k = .ok jumps := by
  rw [checkCode.eq_9] at hcc
  cases hc1 : ctx.checkExcl x "sset" with
  | error e => rw [hc1] at hcc; cases hcc
  | ok _ =>
    simp only [hc1, Bind.bind, Except.bind] at hcc
    cases hc2 : ctx.checkLive y with
    | error e => rw [hc2] at hcc; cases hcc
    | ok _ => simp only [hc2] at hcc; exact ⟨rfl, rfl, hcc⟩

private theorem checkCode_setTag_unwrap {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {x cidx : Nat} {k : LcCode} {jumps : List (Nat × RcCtx)}
    (hcc : checkCode env retTy jps ctx (.setTag x cidx k) = .ok jumps) :
    ctx.checkExcl x "setTag" = .ok () ∧ checkCode env retTy jps ctx k = .ok jumps := by
  rw [checkCode.eq_10] at hcc
  cases hc1 : ctx.checkExcl x "setTag" with
  | error e => rw [hc1] at hcc; cases hcc
  | ok _ => simp only [hc1, Bind.bind, Except.bind] at hcc; exact ⟨rfl, hcc⟩

public theorem mkRcModEnv_decl_not_prim {m : LcModule}
    (hmwf : ∀ d ∈ m.decls, !isPrimName d.name = true ∧ (d.params.map LcParam.id).Nodup)
    {f : String} (hfd : ((mkRcModEnv m).decls.find? (·.1 == f)).isSome = true) :
    pIsPrimName f = false := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hfd
  have hmem := List.mem_of_find?_eq_some he
  have hbeq : (e.1 == f) = true :=
    List.find?_some (p := fun (x : String × List Bool × List LcTy × LcTy × Bool) => x.1 == f) he
  have hid : e.1 = f := beq_iff_eq.mp hbeq
  simp only [mkRcModEnv, List.mem_map] at hmem
  obtain ⟨d, hd, rfl⟩ := hmem
  have hnp := (hmwf d hd).1
  dsimp only at hid
  rw [hid] at hnp
  change !pIsPrimName f = true at hnp
  exact Bool.eq_false_iff.mpr (by simpa using hnp)

end BodyHelpers

section BodySim

public theorem perceus_code_sim {m : LcModule} {retTy : LcTy} {Δr : PResEnv} {Δh : HEnv}
    {rt : BitVec 64}
    (hmwf : ∀ d ∈ m.decls, !isPrimName d.name = true ∧ (d.params.map LcParam.id).Nodup)
    (hcompat : PRCallCompat m Δr Δh) :
    ∀ (c : LcCode) {Jh : HJEnv} {Jp : PResJEnv} {Qp : PResPost} {Xp : PResXPost}
      {Qh : HPost} {Xh : HXPost} {jpsOk : List JpEntry} {rf0 rf : RcFrame} {σ0 σ : HState}
      {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr : Nat}
      {jumps : List (Nat × RcCtx)},
      checkCode (mkRcModEnv m) retTy (jpsOk.map JpEntry.info) rf.ctx c = .ok jumps →
      perceusCodeWf (mkRcModEnv m) retTy (jpsOk.map JpEntry.info) rf.ctx sm c = true →
      PRWp m (mkRcModEnv m) retTy Δr (jpsOk.map JpEntry.info) rf.ctx Jp ρP rem wr rcr Qp Xp c →
      RcInv rt rf σ → CleanVars rf.ctx → ParentsOwned rf.ctx → NoRcCorrect rf.ctx →
      ParentChildBacked rf σ.objs → SharedTargetsHeap rf →
      HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs → EntryPres rf0 σ0 rf σ →
      SharedBoolVars rf.ctx → SharedBoolPreds rf.ctx → ExclCtorHeap rf →
      ShadowSmWf sm → ShadowOk sm rf.ctx ρP rf.envP → ResStateInv σ rem wr rcr →
      JpsScopeIn (jpsOk.map JpEntry.info) rf.ctx → JpsOk rt rf0 σ0 Jp Jh jpsOk rf ρP jumps →
      (∀ e ∈ jpsOk, jpLiveNoMut e.info.id (baseCtxLiveIds e.baseCtx) e.mutVars c = true) →
      (∀ e ∈ jpsOk, ∀ pvs, e.PBody pvs) →
      (∀ {r : PVal} {rw : Word} {σ' : HState} {rf' : RcFrame} {rem' wr' rcr' : Nat},
        Qp r rem' wr' rcr' → HeapClean rt σ' → ResStateInv σ' rem' wr' rcr' →
        ValRep retTy r rw σ'.objs →
        (¬retTy.isScalar = true → ¬retTy.needsRc = true →
          ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64) →
        HandlesRcSound (retHandles retTy rw ++ rf'.extH ++ rf'.ghostH) σ'.objs →
        EntryPres rf0 σ0 rf' σ' → Qh rw σ') →
      (∀ {c rem' wr' rcr' : Nat} {σ' : HState},
        Xp c rem' wr' rcr' → Xh (BitVec.ofNat 64 c) σ') →
      HWp Δh rt retTy Jh rf.envH Qh Xh c σ := by
  intro c
  match c with
  | .unreach =>
    intro Jh Jp Qp Xp Qh Xh jpsOk rf0 rf σ0 σ sm ρP rem wr rcr jumps
      _ _ hpr hrc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hx
    exact unreach_step hpr hrc hx
  | .ret a =>
    intro Jh Jp Qp Xp Qh Xh jpsOk rf0 rf σ0 σ sm ρP rem wr rcr jumps
      hcc hwf hpr hrc hcl hpo hno _ _ _ hep _ _ _ _ hsh hres _ _ _ _ hq _
    exact ret_step hcc hwf hpr hrc hcl hpo hno hep hsh hres
      (fun hQ hc' hres' hvr hodd hsnd hep' => hq hQ hc' hres' hvr hodd hsnd hep')
  | .jmp j as =>
    intro Jh Jp Qp Xp Qh Xh jpsOk rf0 rf σ0 σ sm ρP rem wr rcr jumps
      hcc hwf hpr hrc hcl hpo hno hpcb hsth hhih hep hsbv hsbp hex _ hsh hres _ hjok hjmut hpb _ _
    exact jmp_step hcc hwf hpr hrc hcl hpo hno hpcb hsth hhih hep hsbv hsbp hex hsh hres hjok
      hjmut (fun e he _ pvs _ => hpb e he pvs)
  | .let_ x ty v k =>
    intro Jh Jp Qp Xp Qh Xh jpsOk rf0 rf σ0 σ sm ρP rem wr rcr jumps
      hcc hwf hpr hrc hcl hpo hno hpcb hsth hhih hep hsbv hsbp hex hsmwf hsh hres
      hjsc hjok hjmut hpb hq hx
    exact let_step (fun d hd => ⟨by simpa using (hmwf d hd).1, (hmwf d hd).2⟩) hcompat
      hcc hwf hpr hrc hcl hpo hno hpcb hsth hhih hep hsbv hsbp hex hsmwf hsh hres
      hjsc hjok hjmut hpb hx
      (fun hcc' hwf' hpr' hrc' hcl' hpo' hno' hpcb' hsth' hhih' hep' hsbv' hsbp' hex'
        hsmwf' hsh' hres' hjsc' hjok' hjmut' hpb' =>
        perceus_code_sim hmwf hcompat k hcc' hwf' hpr' hrc' hcl' hpo' hno' hpcb' hsth' hhih' hep'
          hsbv' hsbp' hex' hsmwf' hsh' hres' hjsc' hjok' hjmut' hpb' hq hx)
  | .jp j ps body k =>
    intro Jh Jp Qp Xp Qh Xh jpsOk rf0 rf σ0 σ sm ρP rem wr rcr jumps
      hcc hwf hpr hrc hcl hpo hno hpcb hsth hhih hep hsbv hsbp hex hsmwf hsh hres
      hjsc hjok hjmut hpb hq hx
    exact jp_step (PBody := fun _ => True) hcc hwf hpr hrc hep hsh
      (ctxStaticInv_of hrc.2.1 hcl hno hsbp) hjsc hjok hjmut hpb (fun _ => trivial)
      (fun _ _ _ _ _ _ _ _ _ _ _ hccB hwfB hprB _ hrcB hclB hpoB hnoB hpcbB hsthB hhihB
          hepB hsbvB hsbpB hexB hshB hsmwfB hresB _ hjscB hjokB hjmutB hpbB =>
        perceus_code_sim hmwf hcompat body hccB hwfB hprB hrcB hclB hpoB hnoB hpcbB hsthB hhihB
          hepB hsbvB hsbpB hexB hsmwfB hshB hresB hjscB hjokB hjmutB hpbB hq hx)
      (fun _ _ _ _ hprK hccK hwfK hjscK hjokK hjmutK hpbK =>
        perceus_code_sim hmwf hcompat k hccK hwfK hprK hrc hcl hpo hno hpcb hsth hhih hep
          hsbv hsbp hex hsmwf hsh hres hjscK hjokK hjmutK hpbK hq hx)
  | .cases x alts =>
    intro Jh Jp Qp Xp Qh Xh jpsOk rf0 rf σ0 σ sm ρP rem wr rcr jumps
      hcc hwf hpr hrc hcl hpo hno hpcb hsth hhih hep hsbv hsbp hex hsmwf hsh hres
      hjsc hjok hjmut hpb hq hx
    have hclv_x : rf.ctx.checkLive x = .ok () := by
      rw [checkCode.eq_4] at hcc
      cases hclv : rf.ctx.checkLive x with
      | error e => rw [hclv] at hcc; cases hcc
      | ok _ => rfl
    refine cases_branch_step hwf hclv_x hpr hrc hcl hpo hno hpcb hsth hhih hep
      hsbv hsbp hex hsmwf hsh hres ?_
    intro b _ ctx' rf' ⟨pat, hmem, hctx_eq⟩ hbw hbp h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hres'
    have hmem' : (pat, b) ∈ alts := hmem
    obtain ⟨jb, hjb_ok, hjb_sub⟩ := checkCode_cases_branch hcc hmem'
    have hcb := casesBranchCtx_props (env := mkRcModEnv m) hrc.2.1 (fun v hv => by
      obtain ⟨v0, hg0, hl0⟩ := checkLive_facts hclv_x
      rw [hv] at hg0; cases hg0; exact hl0)
      ((rf.ctx.sharedPreds.find? (·.1 == x)).map Prod.snd) pat
    have hjsc' : JpsScopeIn (jpsOk.map JpEntry.info) ctx' := by
      rw [hctx_eq]; exact jpsScopeIn_mono hjsc hcb.2
    have hjok' : JpsOk rt rf0 σ0 Jp Jh jpsOk rf' ρP jb :=
      jpsOk_ctx_step hjok (hctx_eq ▸ hcb.1) hjb_sub
    have hjmut' : ∀ e ∈ jpsOk,
        jpLiveNoMut e.info.id (baseCtxLiveIds e.baseCtx) e.mutVars b = true :=
      fun e he => by
        have h0 := hjmut e he
        rw [jpLiveNoMut.eq_7] at h0
        exact jpAltsLiveNoMut_mem h0 hmem'
    have hlt_b : sizeOf b < 1 + x + sizeOf alts := by
      have := List.sizeOf_lt_of_mem hmem'; simp_all; omega
    exact perceus_code_sim hmwf hcompat b (rf := rf') (by simpa only [← hctx_eq] using hjb_ok)
      hbw hbp h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hres' hjsc' hjok' hjmut' hpb hq hx
  | .inc x n chk k =>
    intro Jh Jp Qp Xp Qh Xh jpsOk rf0 rf σ0 σ sm ρP rem wr rcr jumps
      hcc hwf hpr hrc hcl hpo hno hpcb hsth hhih hep hsbv hsbp hex hsmwf hsh hres
      hjsc hjok hjmut hpb hq hx
    obtain ⟨v0, hgx0, hvl0, hcc0⟩ := checkCode_inc_ctx hcc
    refine inc_step_ctx hwf hpr hrc hcl hpo hno hpcb hsth hhih hep hres ?_
    intro rf' σ' rcr' hwf' hpr' hrc' hcl' hpo' hno' hpcb' hsth' hhih' hep' hres' _ hrel
    rcases rf' with ⟨ctx', envP', envH', extH', ghostH'⟩
    rcases hrel with ⟨rfl, rfl, rfl, hctx_rel⟩
    dsimp only at hctx_rel
    have hjmut' : ∀ e ∈ jpsOk,
        jpLiveNoMut e.info.id (baseCtxLiveIds e.baseCtx) e.mutVars k = true :=
      fun e he => by simpa [jpLiveNoMut, jpLiveNoMut._f] using hjmut e he
    rcases hctx_rel with ⟨v, hgx, hskip, hctx_eq⟩ | ⟨v, hgx, hnskip, hput⟩
    · rw [hgx0] at hgx; cases hgx
      have hcc' : checkCode (mkRcModEnv m) retTy (jpsOk.map JpEntry.info) rf.ctx k =
          .ok jumps := by
        simpa [hskip] using hcc0
      exact perceus_code_sim hmwf hcompat k (hctx_eq ▸ hcc') hwf' hpr' hrc' hcl' hpo' hno'
        hpcb' hsth' hhih' hep' (hctx_eq ▸ hsbv) (hctx_eq ▸ hsbp) (hctx_eq ▸ hex) hsmwf
        (hctx_eq ▸ hsh) hres' (hctx_eq ▸ hjsc)
        (jpsOk_ctx_step hjok (hctx_eq ▸ ⟨fun _ => ⟨rfl, fun h => h⟩, fun _ h => h⟩)
          (fun _ h => h)) hjmut' hpb hq hx
    · rw [hgx0] at hgx; cases hgx
      have hcc' : checkCode (mkRcModEnv m) retTy (jpsOk.map JpEntry.info) ctx' k = .ok jumps := by
        simpa [hnskip, hput] using hcc0
      have hv_mem := (RcCtx.get?_mem hgx0).1
      have hsbv' : SharedBoolVars ctx' :=
        hput ▸ sharedBoolVars_put_eq_noRc hrc.2.1 hsbv hv_mem rfl rfl
      have hsbp' : SharedBoolPreds ctx' :=
        hput ▸ sharedBoolPreds_put_eq_noRc hrc.2.1 hsbp hv_mem rfl rfl
      have hex' : ExclCtorHeap (RcFrame.mk ctx' rf.envP rf.envH rf.extH ghostH') :=
        hput ▸ exclCtorHeap_put_exclFalse hrc.2.1 hex rfl
      have hsh' : ShadowOk sm ctx' ρP rf.envP :=
        hput ▸ shadowOk_put_live hrc.2.1 hsh hv_mem rfl (fun _ => hvl0)
      have hjsc' : JpsScopeIn (jpsOk.map JpEntry.info) ctx' := hput ▸ jpsScopeIn_put hrc.2.1 hjsc
      have hctx_props :
          (∀ z, Option.map RcVar.ty (ctx'.get? z) = Option.map RcVar.ty (rf.ctx.get? z) ∧
            (Option.map RcVar.isLive (ctx'.get? z) = some true →
              Option.map RcVar.isLive (rf.ctx.get? z) = some true)) ∧
          (∀ p, p ∈ ctx'.sharedPreds → p ∈ rf.ctx.sharedPreds) := by
        refine ⟨fun z => ?_, fun p hp => by rw [hput] at hp; simpa [RcCtx.put] using hp⟩
        rw [hput]
        by_cases hzx : z = v0.id
        · rw [hzx, get?_put_self rf.ctx hrc.2.1 _, rcCtx_get?_of_mem hrc.2.1 hv_mem]
          exact ⟨rfl, fun _ => by simp [hvl0]⟩
        · have hne : z ≠ ({ v0 with owned := v0.owned + n, excl := false } : RcVar).id := hzx
          rw [get?_put_ne rf.ctx hrc.2.1 hne]
          exact ⟨rfl, fun h => h⟩
      exact perceus_code_sim hmwf hcompat k hcc' hwf' hpr' hrc' hcl' hpo' hno' hpcb' hsth' hhih'
        hep' hsbv' hsbp' hex' hsmwf hsh' hres' hjsc'
        (jpsOk_ctx_step hjok hctx_props fun _ h => h) hjmut' hpb hq hx
  | .dec x n chk k =>
    intro Jh Jp Qp Xp Qh Xh jpsOk rf0 rf σ0 σ sm ρP rem wr rcr jumps
      hcc hwf hpr hrc hcl hpo hno hpcb hsth hhih hep hsbv hsbp hex hsmwf hsh hres
      hjsc hjok hjmut hpb hq hx
    obtain ⟨ctx0, hcons0, hcc0, _⟩ := checkCode_dec_unwrap hcc hwf
    refine dec_step_ctx hwf hpr hrc hcl hpo hno hpcb hsth hhih hep hsbv hsbp hex hsmwf hsh hres ?_
    intro rf' σ' hwf' hpr' hrc' hcl' hpo' hno' hpcb' hsth' hhih' hep' hsbv' hsbp' hex'
      hsmwf' hsh' hres' hrel
    rcases rf' with ⟨ctx', envP', envH', extH', ghostH'⟩
    rcases hrel with ⟨rfl, rfl, rfl, hcons⟩
    dsimp only at hcons
    have hcc' : checkCode (mkRcModEnv m) retTy (jpsOk.map JpEntry.info) ctx' k = .ok jumps := by
      rw [hcons0] at hcons; cases hcons; exact hcc0
    have hjsc' := jpsScopeIn_consumeVar hrc.2.1 hcons hjsc
    have hcp := consumeVar_ctx_props hrc.2.1 hcons
    have hjok' := jpsOk_ctx_step (ghostH' := ghostH') hjok ⟨hcp.1, hcp.2.1⟩ (fun _ h => h)
    have hjmut' : ∀ e ∈ jpsOk,
        jpLiveNoMut e.info.id (baseCtxLiveIds e.baseCtx) e.mutVars k = true :=
      fun e he => by simpa [jpLiveNoMut, jpLiveNoMut._f] using hjmut e he
    exact perceus_code_sim hmwf hcompat k hcc' hwf' hpr' hrc' hcl' hpo' hno' hpcb' hsth' hhih'
      hep' hsbv' hsbp' hex' hsmwf' hsh' hres' hjsc' hjok' hjmut' hpb hq hx
  | .del x k =>
    intro Jh Jp Qp Xp Qh Xh jpsOk rf0 rf σ0 σ sm ρP rem wr rcr jumps
      hcc hwf hpr hrc hcl hpo hno hpcb hsth hhih hep hsbv hsbp hex hsmwf hsh hres
      hjsc hjok hjmut hpb hq hx
    obtain ⟨ctx0, hchk, hcons0, hcc0, _⟩ := checkCode_del_unwrap hcc hwf
    refine del_step_ctx hwf hchk hpr hrc hcl hpo hno hpcb hsth hhih hep hres ?_
    intro rf' σ' hwf' hpr' hrc' hcl' hpo' hno' hpcb' hsth' hhih' hep' hres' _ hrel
    rcases rf' with ⟨ctx', envP', envH', extH', ghostH'⟩
    rcases hrel with ⟨rfl, rfl, rfl, hcons⟩
    dsimp only at hcons
    have hcc' : checkCode (mkRcModEnv m) retTy (jpsOk.map JpEntry.info) ctx' k = .ok jumps := by
      rw [hcons0] at hcons; cases hcons; exact hcc0
    have hsbv' := sharedBoolVars_consumeVar hrc.2.1 hsbv hcons
    have hsbp' := sharedBoolPreds_consumeVar hrc.2.1 hsbp hcons
    have hex' := exclCtorHeap_consumeVar hrc.2.1 hcl hcons hex
    have hsmwf' := shadowSmWf_filter hsmwf x
    have hsh' := shadowOk_filter_del hrc.2.1 hcl hchk hcons hsh
    have hjsc' := jpsScopeIn_consumeVar hrc.2.1 hcons hjsc
    have hcp := consumeVar_ctx_props hrc.2.1 hcons
    have hjok' := jpsOk_ctx_step (ghostH' := ghostH') hjok ⟨hcp.1, hcp.2.1⟩ (fun _ h => h)
    have hjmut' : ∀ e ∈ jpsOk,
        jpLiveNoMut e.info.id (baseCtxLiveIds e.baseCtx) e.mutVars k = true :=
      fun e he => by simpa [jpLiveNoMut, jpLiveNoMut._f] using hjmut e he
    exact perceus_code_sim hmwf hcompat k hcc' hwf' hpr' hrc' hcl' hpo' hno' hpcb' hsth' hhih'
      hep' hsbv' hsbp' hex' hsmwf' hsh' hres' hjsc' hjok' hjmut' hpb hq hx
  | .oset x i y k =>
    intro Jh Jp Qp Xp Qh Xh jpsOk rf0 rf σ0 σ sm ρP rem wr rcr jumps
      hcc hwf hpr hrc hcl hpo hno hpcb hsth hhih hep hsbv hsbp hex hsmwf hsh hres
      hjsc hjok hjmut hpb hq hx
    obtain ⟨ctx1, hchk, hcons1, hcc1, _⟩ := checkCode_oset_unwrap hcc hwf
    refine oset_step_ctx hwf hchk hpr hrc hcl hpo hno hpcb hsth hhih hep hsbv hex hsmwf hsh hres ?_
    intro rf' σ' ρP' hwf' hpr' hrc' hcl' hpo' hno' hpcb' hsth' hhih' hep' hsbv' hex'
      hsmwf' hsh' hres' hrel
    rcases rf' with ⟨ctx', envP', envH', extH', ghostH'⟩
    rcases hrel with ⟨henvH, hrho_eq, rfl, hcons⟩
    dsimp only at henvH hcons
    have hcc' : checkCode (mkRcModEnv m) retTy (jpsOk.map JpEntry.info) ctx' k = .ok jumps := by
      rw [hcons1] at hcons; cases hcons; exact hcc1
    have hsbp' := consumeArg_sharedBoolPreds hrc.2.1 hsbp hcons
    have hjsc' := jpsScopeIn_consumeArg hrc.2.1 hcons hjsc
    have hjok' := jpsOk_mut_step_sameEnvH (ghostH' := ghostH') hjok
      (consumeArg_ctx_props hrc.2.1 hcl hcons) henvH
      (fun z hz => ⟨(hrho_eq z hz).2, (hrho_eq z hz).1⟩) (fun _ h => h)
    have hmap_info :
        (jpsOk.map fun e => { e with mutVars := x :: e.mutVars }).map JpEntry.info =
          jpsOk.map JpEntry.info := by
      simp [List.map_map, Function.comp_def]
    have hjmut' : ∀ e ∈ (jpsOk.map fun e => { e with mutVars := x :: e.mutVars }),
        jpLiveNoMut e.info.id (baseCtxLiveIds e.baseCtx) e.mutVars k = true := fun e he => by
      rcases List.mem_map.mp he with ⟨e0, he0, rfl⟩
      simpa [jpLiveNoMut, jpLiveNoMut._f] using hjmut e0 he0
    have hpb' : ∀ e ∈ (jpsOk.map fun e => { e with mutVars := x :: e.mutVars }),
        ∀ pvs, e.PBody pvs := fun e he pvs => by
      rcases List.mem_map.mp he with ⟨e0, he0, rfl⟩
      exact hpb e0 he0 pvs
    exact perceus_code_sim hmwf hcompat k (hmap_info ▸ hcc') (hmap_info ▸ hwf') (hmap_info ▸ hpr')
      hrc' hcl' hpo' hno' hpcb' hsth' hhih' hep' hsbv' hsbp' hex' hsmwf' hsh' hres'
      (hmap_info ▸ hjsc') hjok' hjmut' hpb' hq hx
  | .uset x i y k =>
    intro Jh Jp Qp Xp Qh Xh jpsOk rf0 rf σ0 σ sm ρP rem wr rcr jumps
      hcc hwf hpr hrc hcl hpo hno hpcb hsth hhih hep hsbv hsbp hex hsmwf hsh hres
      hjsc hjok hjmut hpb hq hx
    obtain ⟨hchk, hclv, hcc1⟩ := checkCode_uset_unwrap hcc
    refine uset_step hwf hchk hclv hpr hrc hcl hpo hno hpcb hsth hhih hep hsbv hex hsmwf hsh hres ?_
    intro rf' σ' ρP' hwf' hpr' hrc' hcl' hpo' hno' hpcb' hsth' hhih' hep' hsbv' hex'
      hsmwf' hsh' hres' hrel
    rcases rf' with ⟨ctx', envP', envH', extH', ghostH'⟩
    rcases hrel with ⟨rfl, rfl, henvH, hrho_eq⟩
    dsimp only at henvH
    have hjok' := jpsOk_mut_step_sameEnvH (ghostH' := ghostH') hjok
      ⟨fun _ => ⟨rfl, fun h => h⟩, fun _ h => h⟩ henvH
      (fun z hz => ⟨(hrho_eq z hz).2, (hrho_eq z hz).1⟩) (fun _ h => h)
    have hmap_info :
        (jpsOk.map fun e => { e with mutVars := x :: e.mutVars }).map JpEntry.info =
          jpsOk.map JpEntry.info := by
      simp [List.map_map, Function.comp_def]
    have hjmut' : ∀ e ∈ (jpsOk.map fun e => { e with mutVars := x :: e.mutVars }),
        jpLiveNoMut e.info.id (baseCtxLiveIds e.baseCtx) e.mutVars k = true := fun e he => by
      rcases List.mem_map.mp he with ⟨e0, he0, rfl⟩
      simpa [jpLiveNoMut, jpLiveNoMut._f] using hjmut e0 he0
    have hpb' : ∀ e ∈ (jpsOk.map fun e => { e with mutVars := x :: e.mutVars }),
        ∀ pvs, e.PBody pvs := fun e he pvs => by
      rcases List.mem_map.mp he with ⟨e0, he0, rfl⟩
      exact hpb e0 he0 pvs
    exact perceus_code_sim hmwf hcompat k (hmap_info ▸ hcc1) (hmap_info ▸ hwf') (hmap_info ▸ hpr')
      hrc' hcl' hpo' hno' hpcb' hsth' hhih' hep' hsbv' hsbp hex' hsmwf' hsh' hres'
      (hmap_info ▸ hjsc) hjok' hjmut' hpb' hq hx
  | .sset x n off y ty k =>
    intro Jh Jp Qp Xp Qh Xh jpsOk rf0 rf σ0 σ sm ρP rem wr rcr jumps
      hcc hwf hpr hrc hcl hpo hno hpcb hsth hhih hep hsbv hsbp hex hsmwf hsh hres
      hjsc hjok hjmut hpb hq hx
    obtain ⟨hchk, hclv, hcc1⟩ := checkCode_sset_unwrap hcc
    refine sset_step hwf hchk hclv hpr hrc hcl hpo hno hpcb hsth hhih hep hsbv hex hsmwf hsh hres ?_
    intro rf' σ' ρP' hwf' hpr' hrc' hcl' hpo' hno' hpcb' hsth' hhih' hep' hsbv' hex'
      hsmwf' hsh' hres' hrel
    rcases rf' with ⟨ctx', envP', envH', extH', ghostH'⟩
    rcases hrel with ⟨rfl, rfl, henvH, hrho_eq⟩
    dsimp only at henvH
    have hjok' := jpsOk_mut_step_sameEnvH (ghostH' := ghostH') hjok
      ⟨fun _ => ⟨rfl, fun h => h⟩, fun _ h => h⟩ henvH
      (fun z hz => ⟨(hrho_eq z hz).2, (hrho_eq z hz).1⟩) (fun _ h => h)
    have hmap_info :
        (jpsOk.map fun e => { e with mutVars := x :: e.mutVars }).map JpEntry.info =
          jpsOk.map JpEntry.info := by
      simp [List.map_map, Function.comp_def]
    have hjmut' : ∀ e ∈ (jpsOk.map fun e => { e with mutVars := x :: e.mutVars }),
        jpLiveNoMut e.info.id (baseCtxLiveIds e.baseCtx) e.mutVars k = true := fun e he => by
      rcases List.mem_map.mp he with ⟨e0, he0, rfl⟩
      simpa [jpLiveNoMut, jpLiveNoMut._f] using hjmut e0 he0
    have hpb' : ∀ e ∈ (jpsOk.map fun e => { e with mutVars := x :: e.mutVars }),
        ∀ pvs, e.PBody pvs := fun e he pvs => by
      rcases List.mem_map.mp he with ⟨e0, he0, rfl⟩
      exact hpb e0 he0 pvs
    exact perceus_code_sim hmwf hcompat k (hmap_info ▸ hcc1) (hmap_info ▸ hwf') (hmap_info ▸ hpr')
      hrc' hcl' hpo' hno' hpcb' hsth' hhih' hep' hsbv' hsbp hex' hsmwf' hsh' hres'
      (hmap_info ▸ hjsc) hjok' hjmut' hpb' hq hx
  | .setTag x cidx k =>
    intro Jh Jp Qp Xp Qh Xh jpsOk rf0 rf σ0 σ sm ρP rem wr rcr jumps
      hcc hwf hpr hrc hcl hpo hno hpcb hsth hhih hep hsbv hsbp hex hsmwf hsh hres
      hjsc hjok hjmut hpb hq hx
    obtain ⟨hchk, hcc1⟩ := checkCode_setTag_unwrap hcc
    refine setTag_step hwf hchk hpr hrc hcl hpo hno hpcb hsth hhih hep hsbv hex hsmwf hsh hres ?_
    intro rf' σ' ρP' hwf' hpr' hrc' hcl' hpo' hno' hpcb' hsth' hhih' hep' hsbv' hex'
      hsmwf' hsh' hres' hrel
    rcases rf' with ⟨ctx', envP', envH', extH', ghostH'⟩
    rcases hrel with ⟨rfl, rfl, henvH, hrho_eq⟩
    dsimp only at henvH
    have hjok' := jpsOk_mut_step_sameEnvH (ghostH' := ghostH') hjok
      ⟨fun _ => ⟨rfl, fun h => h⟩, fun _ h => h⟩ henvH
      (fun z hz => ⟨(hrho_eq z hz).2, (hrho_eq z hz).1⟩) (fun _ h => h)
    have hmap_info :
        (jpsOk.map fun e => { e with mutVars := x :: e.mutVars }).map JpEntry.info =
          jpsOk.map JpEntry.info := by
      simp [List.map_map, Function.comp_def]
    have hjmut' : ∀ e ∈ (jpsOk.map fun e => { e with mutVars := x :: e.mutVars }),
        jpLiveNoMut e.info.id (baseCtxLiveIds e.baseCtx) e.mutVars k = true := fun e he => by
      rcases List.mem_map.mp he with ⟨e0, he0, rfl⟩
      simpa [jpLiveNoMut, jpLiveNoMut._f] using hjmut e0 he0
    have hpb' : ∀ e ∈ (jpsOk.map fun e => { e with mutVars := x :: e.mutVars }),
        ∀ pvs, e.PBody pvs := fun e he pvs => by
      rcases List.mem_map.mp he with ⟨e0, he0, rfl⟩
      exact hpb e0 he0 pvs
    exact perceus_code_sim hmwf hcompat k (hmap_info ▸ hcc1) (hmap_info ▸ hwf') (hmap_info ▸ hpr')
      hrc' hcl' hpo' hno' hpcb' hsth' hhih' hep' hsbv' hsbp hex' hsmwf' hsh' hres'
      (hmap_info ▸ hjsc) hjok' hjmut' hpb' hq hx
termination_by c => sizeOf c
decreasing_by all_goals (simp; try (first | exact hlt_b | omega))

end BodySim

end LeanQbe.T.LeanLCNF.Sem
