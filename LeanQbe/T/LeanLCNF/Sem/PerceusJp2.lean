module

public import LeanQbe.T.LeanLCNF.Sem.PerceusJp1

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T

section HelpersAndBaseCtx

private theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = Except.ok b) : ∃ a, x = Except.ok a ∧ f a = Except.ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- `(ctx.get? id).isSome = true` iff `id ∈ ctx.vars.map RcVar.id`. -/
public theorem get?_isSome_iff_mem_map_id (ctx : RcCtx) (id : Nat) :
    (ctx.get? id).isSome = true ↔ id ∈ ctx.vars.map RcVar.id := by
  unfold RcCtx.get?
  constructor
  · intro h
    cases hf : ctx.vars.find? (fun v => v.id == id) with
    | none => rw [hf] at h; cases h
    | some v =>
      have hvs := List.find?_some hf
      exact List.mem_map.mpr
        ⟨v, List.mem_of_find?_eq_some hf, beq_iff_eq.mp hvs⟩
  · intro hm
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hm
    cases hf : ctx.vars.find? (fun w => w.id == v.id) with
    | some _ => rfl
    | none =>
      exfalso
      have hfn := List.find?_eq_none.mp hf v hv
      simp at hfn

/-- Restricting a `Nodup` context to a `Nodup` subset of IDs yields a permutation of `scopeIds`. -/
public theorem perm_scopeIds_of_subset {ctx : RcCtx} {scopeIds : List Nat}
    (hndV : (ctx.vars.map RcVar.id).Nodup) (hndS : scopeIds.Nodup)
    (hsub : ∀ id ∈ scopeIds, (ctx.get? id).isSome = true) :
    ((ctx.restrict scopeIds).vars.map RcVar.id).Perm scopeIds := by
  have hndR : ((ctx.restrict scopeIds).vars.map RcVar.id).Nodup := restrict_nodup hndV scopeIds
  refine (List.perm_ext_iff_of_nodup hndR hndS).mpr fun id => ?_
  constructor
  · intro hm
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hm
    exact List.contains_iff_mem.mp (List.mem_filter.mp hv).2
  · intro hid
    obtain ⟨v, hv, hvid⟩ := List.mem_map.mp ((get?_isSome_iff_mem_map_id ctx id).mp (hsub id hid))
    have hvr : v ∈ (ctx.restrict scopeIds).vars :=
      List.mem_filter.mpr ⟨hv, List.contains_iff_mem.mpr (hvid.symm ▸ hid)⟩
    exact List.mem_map.mpr ⟨v, hvr, hvid⟩

/-- Two contexts with permuted ID lists agree on `(·.get? id).isSome`. -/
public theorem perm_get?_isSome {c1 c2 : RcCtx}
    (hp : (c1.vars.map RcVar.id).Perm (c2.vars.map RcVar.id)) :
    ∀ id, (c1.get? id).isSome = true ↔ (c2.get? id).isSome = true := by
  intro id
  rw [get?_isSome_iff_mem_map_id, get?_isSome_iff_mem_map_id]
  exact hp.mem_iff

/-- Live variable IDs of a join point's merged `baseCtx`. -/
@[expose] public def baseCtxLiveIds (baseCtx : RcCtx) : List Nat :=
  (baseCtx.vars.filter (fun v => v.isLive)).map (fun v => v.id)

/-- `CtxStaticInv` preserved through `RcCtx.restrict`. -/
public theorem restrict_static_invs {ctx : RcCtx} (hs : CtxStaticInv ctx)
    (keepIds : List Nat) : CtxStaticInv (ctx.restrict keepIds) := by
  refine ⟨restrict_nodup hs.1 keepIds, ?_, ?_, ?_⟩
  · intro w hw hno; exact hs.2.1 w (List.mem_filter.mp hw).1 hno
  · intro pr hpr
    have hp1in := List.contains_iff_mem.mp
      (Bool.and_eq_true _ _ |>.mp (List.mem_filter.mp hpr).2).1
    obtain ⟨vb, hgb, hvbno⟩ := hs.2.2.1 pr (List.mem_filter.mp hpr).1
    have hgb' : (ctx.restrict keepIds).get? pr.1 = some vb := by
      rw [restrict_get?_eq]
      simp only [List.contains_iff_mem.mpr hp1in, ↓reduceIte]
      exact hgb
    exact ⟨vb, hgb', hvbno⟩
  · intro w hw hb; exact hs.2.2.2 w (List.mem_filter.mp hw).1 hb

/-- `bindParams` preserves `sharedPreds`. -/
public theorem bindParams_sharedPreds (ctx : RcCtx) (ps : List LcParam) :
    (ctx.bindParams ps).sharedPreds = ctx.sharedPreds := by
  induction ps generalizing ctx with
  | nil => rfl
  | cons q rest ih =>
    simp only [RcCtx.bindParams, List.foldl_cons]
    have h1 : (if q.borrow = true then ctx.bindBorrowed q.id q.ty
        else ctx.bindOwned q.id q.ty).sharedPreds = ctx.sharedPreds := by
      cases q.borrow <;> rfl
    exact (ih _).trans h1

/-- `bindParams` preserves `get? id` when `id` is not bound in `ps`. -/
public theorem bindParams_get?_of_not_mem {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (ps : List LcParam) {id : Nat} (hnot : ∀ p ∈ ps, p.id ≠ id) :
    (ctx.bindParams ps).get? id = ctx.get? id := by
  induction ps generalizing ctx with
  | nil => rfl
  | cons q rest ih =>
    simp only [RcCtx.bindParams, List.foldl_cons]
    let ctx1 := if q.borrow = true then ctx.bindBorrowed q.id q.ty else ctx.bindOwned q.id q.ty
    have hnd1 : (ctx1.vars.map RcVar.id).Nodup := by
      dsimp only [ctx1]; cases q.borrow <;> exact RcCtx.put_nodup hnd _
    have h1 : ctx1.get? id = ctx.get? id := by
      have hne : (id == q.id) = false := beq_false_of_ne (hnot q List.mem_cons_self).symm
      dsimp only [ctx1]; cases q.borrow <;>
        simp [RcCtx.bindBorrowed, RcCtx.bindOwned, RcCtx.put_get? hnd, hne]
    have hrest : ∀ p ∈ rest, p.id ≠ id := fun p hp => hnot p (List.mem_cons_of_mem _ hp)
    exact (ih hnd1 hrest).trans h1

/-- `binderFreshOwned` prevents `x` from occurring in `ctx.sharedPreds`. -/
public theorem binderFreshOwned_sharedPreds {ctx : RcCtx} {x : Nat}
    (hfr : binderFreshOwned ctx x = true) {b tgt : Nat} (hp : (b, tgt) ∈ ctx.sharedPreds) :
    b ≠ x ∧ tgt ≠ x := by
  unfold binderFreshOwned at hfr
  have h1 := (Bool.and_eq_true _ _ |>.mp hfr).1
  have h2 := (Bool.and_eq_true _ _ |>.mp h1).2
  have hm := List.all_eq_true.mp h2 (b, tgt) hp
  have hb := Bool.and_eq_true _ _ |>.mp hm
  exact ⟨fun heq => by simp [heq] at hb, fun heq => by simp [heq] at hb⟩

private theorem perm_vars_same_ids {c1 c2 : RcCtx}
    (heq : c1.vars.map RcVar.id = c2.vars.map RcVar.id) :
    ∀ v ∈ c2.vars, ∃ w ∈ c1.vars, w.id = v.id := by
  intro v hv
  have hm : v.id ∈ c1.vars.map RcVar.id := heq ▸ List.mem_map.mpr ⟨v, hv, rfl⟩
  exact List.mem_map.mp hm

/-- Unwrap `jpBaseCtx` when `checkCode` on `k` succeeded and `mergeJpList` returned `optC`. -/
public theorem jpBaseCtx_eq_of_check {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {j : Nat} {ps : List LcParam} {k : LcCode} {jumpsK : List (Nat × RcCtx)}
    {optC : Option RcCtx}
    (hK : checkCode env retTy ({ id := j, params := ps, scopeIds := ctx.vars.map (·.id) } :: jps)
      ctx k = Except.ok jumpsK)
    (hm : mergeJpList ((jumpsK.filter (·.1 == j)).map Prod.snd) = Except.ok optC) :
    jpBaseCtx env retTy jps ctx j ps k = optC.getD ctx := by
  unfold jpBaseCtx
  dsimp only
  rw [hK]
  simp only [hm]
  cases optC <;> rfl

/-- Core invariants of `jpBaseCtx` derived from static invariants on `jumpsK`. -/
public theorem jpBaseCtx_invs_of_jumps {ctx : RcCtx} {optC : Option RcCtx}
    {myJumps : List RcCtx} (hs : CtxStaticInv ctx)
    (hm : mergeJpList myJumps = Except.ok optC)
    (hmy : ∀ c ∈ myJumps, CtxStaticInv c ∧ (c.vars.map RcVar.id).Perm (ctx.vars.map RcVar.id)) :
    let baseCtx := optC.getD ctx
    CtxStaticInv baseCtx ∧
    (baseCtx.vars.map RcVar.id).Perm (ctx.vars.map RcVar.id) ∧
    (∀ id, (ctx.get? id).isSome = true → (baseCtx.get? id).isSome = true) ∧
    (∀ c ∈ myJumps, CtxWeakens baseCtx c) ∧
    (∀ c0 rest, myJumps = c0 :: rest →
      baseCtx.vars.map RcVar.id = c0.vars.map RcVar.id ∧
      (∀ w ∈ baseCtx.vars, ∃ v ∈ c0.vars, w.id = v.id ∧ w.ty = v.ty) ∧
      (∀ p, p ∈ baseCtx.sharedPreds → p ∈ c0.sharedPreds)) := by
  cases myJumps with
  | nil =>
    simp [mergeJpList, pure, Except.pure] at hm
    cases hm
    dsimp only [Option.getD]
    exact ⟨hs, List.Perm.refl _, fun _ h => h,
      (fun _ hc => by cases hc), (fun _ _ h => by cases h)⟩
  | cons c0 cs =>
    cases optC with
    | none =>
      exfalso
      unfold mergeJpList at hm; dsimp only at hm
      obtain ⟨r, _, hr⟩ := except_bind_ok hm
      simp [pure, Except.pure] at hr
    | some baseCtx =>
      dsimp only [Option.getD]
      have hs0 := (hmy c0 List.mem_cons_self).1
      have hp0 := (hmy c0 List.mem_cons_self).2
      have hndCs : ∀ c ∈ cs, (c.vars.map RcVar.id).Nodup := fun c hc =>
        (hmy c (List.mem_cons_of_mem _ hc)).1.1
      obtain ⟨hndB, hnrB, hmapB, hwB, hheadB, hspB⟩ :=
        mergeJpList_weakens hm hs0.1 hs0.2.2.2 hs0.2.1 hndCs
      have hsbpB : SharedBoolPreds baseCtx :=
        sharedBoolPreds_of_ctxWeakens (hwB c0 List.mem_cons_self) hs0.2.2.1
          (perm_vars_same_ids hmapB)
      have hbpB : ∀ w ∈ baseCtx.vars, w.borrowed = false → w.parent? = none := fun w hw hb => by
        obtain ⟨_, _, _, _, hbp, _⟩ := (hwB c0 List.mem_cons_self).2.2.1 w hw
        exact hbp hb
      have hpermB : (baseCtx.vars.map RcVar.id).Perm (ctx.vars.map RcVar.id) := by
        simpa [hmapB] using hp0
      have hkeep : ∀ id, (ctx.get? id).isSome = true → (baseCtx.get? id).isSome = true :=
        fun id hid => (perm_get?_isSome hpermB id).mpr hid
      refine ⟨⟨hndB, hnrB, hsbpB, hbpB⟩, hpermB, hkeep, hwB, ?_⟩
      intro c0' rest' heq
      cases heq
      exact ⟨hmapB, hheadB, hspB⟩

end HelpersAndBaseCtx

section UnwrapHelpers

/-- Unwrap `let_` across both `checkCode` and `perceusCodeWf`. -/
public theorem checkCode_let_unwrap {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {sm : List (Nat × Nat × List Bool)} {x : Nat} {ty : LcTy} {v : LcVal}
    {k : LcCode} {jumps : List (Nat × RcCtx)}
    (hchk : checkCode env retTy jps ctx (LcCode.let_ x ty v k) = Except.ok jumps)
    (hwf : perceusCodeWf env retTy jps ctx sm (LcCode.let_ x ty v k) = true) :
    ∃ ctx' sm', checkVal env ctx x ty v = Except.ok ctx' ∧
      perceusValWf env ctx x ty v = true ∧ valScalarWf sm ty v = true ∧
      checkCode env retTy jps ctx' k = Except.ok jumps ∧
      perceusCodeWf env retTy jps ctx' sm' k = true := by
  rw [checkCode.eq_1] at hchk
  obtain ⟨ctx', hcv, hrest⟩ := except_bind_ok hchk
  cases v with
  | ctor ci args =>
    rw [perceusCodeWf.eq_1] at hwf
    have ha1 := Bool.and_eq_true _ _ |>.mp hwf
    have ha2 := Bool.and_eq_true _ _ |>.mp ha1.1
    simp only [hcv] at hwf
    exact ⟨ctx', ctorBindMask x ci sm, hcv, ha2.1, ha2.2, hrest, (Bool.and_eq_true _ _ |>.mp hwf).2⟩
  | _ =>
    rw [perceusCodeWf.eq_2 _ _ _ _ _ _ _ _ _ (fun _ _ h => by cases h)] at hwf
    have ha1 := Bool.and_eq_true _ _ |>.mp hwf
    have ha2 := Bool.and_eq_true _ _ |>.mp ha1.1
    simp only [hcv] at hwf
    exact ⟨ctx', sm.filter (·.1 != x), hcv, ha2.1, ha2.2, hrest,
      (Bool.and_eq_true _ _ |>.mp hwf).2⟩

/-- Unwrap `oset` across both `checkCode` and `perceusCodeWf`. -/
public theorem checkCode_oset_unwrap {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {sm : List (Nat × Nat × List Bool)} {x i : Nat} {y : LcArg} {k : LcCode}
    {jumps : List (Nat × RcCtx)}
    (hchk : checkCode env retTy jps ctx (LcCode.oset x i y k) = Except.ok jumps)
    (hwf : perceusCodeWf env retTy jps ctx sm (LcCode.oset x i y k) = true) :
    ∃ ctx1, ctx.checkExcl x "oset" = Except.ok () ∧ ctx.consumeArg y = Except.ok ctx1 ∧
      checkCode env retTy jps ctx1 k = Except.ok jumps ∧
      perceusCodeWf env retTy jps ctx1 sm k = true := by
  rw [checkCode.eq_7] at hchk
  obtain ⟨u, hexcl, hrest1⟩ := except_bind_ok hchk
  cases u
  obtain ⟨ctx1, hca, hrest2⟩ := except_bind_ok hrest1
  have hgx : ∃ vx, ctx.get? x = some vx := by
    unfold RcCtx.checkExcl at hexcl
    cases hg : ctx.get? x with
    | none => rw [hg] at hexcl; cases hexcl
    | some vx => exact ⟨vx, rfl⟩
  obtain ⟨vx, hgx⟩ := hgx
  cases y with
  | erased =>
    rw [perceusCodeWf.eq_10 _ _ _ _ _ _ _ _ vx hgx] at hwf
    simp only [hca] at hwf
    exact ⟨ctx1, hexcl, hca, hrest2, (Bool.and_eq_true _ _ |>.mp hwf).2⟩
  | var yid =>
    rw [perceusCodeWf.eq_9 _ _ _ _ _ _ _ _ vx yid hgx] at hwf
    simp only [hca] at hwf
    exact ⟨ctx1, hexcl, hca, hrest2, (Bool.and_eq_true _ _ |>.mp hwf).2⟩

/-- Unwrap `inc` across both `checkCode` and `perceusCodeWf`. -/
public theorem checkCode_inc_unwrap {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {sm : List (Nat × Nat × List Bool)} {x n : Nat} {chk : Bool} {k : LcCode}
    {jumps : List (Nat × RcCtx)}
    (hchk : checkCode env retTy jps ctx (LcCode.inc x n chk k) = Except.ok jumps)
    (hwf : perceusCodeWf env retTy jps ctx sm (LcCode.inc x n chk k) = true) :
    ∃ v ctx1, ctx.get? x = some v ∧ v.isLive = true ∧
      (ctx1 = ctx ∨
        ((v.noRc || v.persistent || n == 0) = false ∧
          ctx1 = ctx.put {
            id := v.id, ty := v.ty, noRc := v.noRc, persistent := v.persistent,
            owned := v.owned + n, borrowed := v.borrowed, parent? := v.parent?,
            resetTok := v.resetTok })) ∧
      checkCode env retTy jps ctx1 k = Except.ok jumps ∧
      perceusCodeWf env retTy jps ctx1 sm k = true := by
  rw [checkCode.eq_11] at hchk
  rw [perceusCodeWf.eq_15] at hwf
  cases hg : ctx.get? x with
  | none => rw [hg] at hchk; cases hchk
  | some v =>
    rw [hg] at hchk hwf
    dsimp only at hchk hwf
    have hlive : v.isLive = true := by
      cases hl : v.isLive with
      | true => rfl | false => rw [hl] at hwf; simp at hwf
    have hnl : (!v.isLive) = false := by simp [hlive]
    simp only [hnl, Bool.false_eq_true, ↓reduceIte] at hchk
    have hwf1 := (Bool.and_eq_true _ _ |>.mp hwf).2
    have hwf2 := (Bool.and_eq_true _ _ |>.mp hwf1).2
    by_cases hskip : (v.noRc || v.persistent || n == 0) = true
    · simp only [hskip, ↓reduceIte] at hchk hwf2
      exact ⟨v, ctx, rfl, hlive, Or.inl rfl, hchk, hwf2⟩
    · simp only [hskip, Bool.false_eq_true, ↓reduceIte] at hchk hwf2
      exact ⟨v, _, rfl, hlive, Or.inr ⟨Bool.eq_false_iff.mpr hskip, rfl⟩,
        hchk, (Bool.and_eq_true _ _ |>.mp hwf2).2⟩

/-- Unwrap `dec` across both `checkCode` and `perceusCodeWf`. -/
public theorem checkCode_dec_unwrap {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {sm : List (Nat × Nat × List Bool)} {x n : Nat} {chk : Bool} {k : LcCode}
    {jumps : List (Nat × RcCtx)}
    (hchk : checkCode env retTy jps ctx (LcCode.dec x n chk k) = Except.ok jumps)
    (hwf : perceusCodeWf env retTy jps ctx sm (LcCode.dec x n chk k) = true) :
    ∃ ctx1, ctx.consumeVar x n = Except.ok ctx1 ∧
      checkCode env retTy jps ctx1 k = Except.ok jumps ∧
      perceusCodeWf env retTy jps ctx1 sm k = true := by
  rw [checkCode.eq_12] at hchk
  rw [perceusCodeWf.eq_16] at hwf
  obtain ⟨ctx1, hcons, hrest⟩ := except_bind_ok hchk
  cases hg : ctx.get? x with
  | none => rw [hg] at hwf; simp at hwf
  | some v =>
    rw [hg] at hwf; simp only [hcons] at hwf
    exact ⟨ctx1, hcons, hrest, (Bool.and_eq_true _ _ |>.mp hwf).2⟩

/-- Unwrap `del` across both `checkCode` and `perceusCodeWf`. -/
public theorem checkCode_del_unwrap {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {sm : List (Nat × Nat × List Bool)} {x : Nat} {k : LcCode}
    {jumps : List (Nat × RcCtx)}
    (hchk : checkCode env retTy jps ctx (LcCode.del x k) = Except.ok jumps)
    (hwf : perceusCodeWf env retTy jps ctx sm (LcCode.del x k) = true) :
    ∃ ctx1, ctx.checkExcl x "del" = Except.ok () ∧ ctx.consumeVar x 1 = Except.ok ctx1 ∧
      checkCode env retTy jps ctx1 k = Except.ok jumps ∧
      perceusCodeWf env retTy jps ctx1 (sm.filter (·.1 != x)) k = true := by
  rw [checkCode.eq_13] at hchk
  rw [perceusCodeWf.eq_17] at hwf
  obtain ⟨u, hexcl, hrest1⟩ := except_bind_ok hchk
  cases u
  obtain ⟨ctx1, hcons, hrest2⟩ := except_bind_ok hrest1
  simp only [hcons] at hwf
  exact ⟨ctx1, hexcl, hcons, hrest2, hwf⟩

/-- Unwrap `checkAlts`/`perceusAltsWf` on a cons alternative list. -/
public theorem checkAlts_cons_unwrap {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {sm : List (Nat × Nat × List Bool)} {scru : Nat} {scruTy : LcTy}
    {tgt? : Option Nat} {pat : LcPat} {b : LcCode} {rest : List (LcPat × LcCode)}
    {jumps : List (Nat × RcCtx)}
    (hchk : checkAlts env retTy jps ctx scru tgt? ((pat, b) :: rest) = Except.ok jumps)
    (hwf : perceusAltsWf env retTy jps ctx sm scru scruTy tgt? ((pat, b) :: rest) = true) :
    ∃ j1 j2 ctxBranch, jumps = j1 ++ j2 ∧
      checkCode env retTy jps ctxBranch b = Except.ok j1 ∧
      checkAlts env retTy jps ctx scru tgt? rest = Except.ok j2 ∧
      perceusCodeWf env retTy jps ctxBranch sm b = true ∧
      perceusAltsWf env retTy jps ctx sm scru scruTy tgt? rest = true ∧
      (∃ ctx1, (ctxBranch = ctx1 ∨ ∃ tgt, tgt? = some tgt ∧ ctxBranch = ctx1.markExcl tgt) ∧
        (ctx1 = ctx ∨ ctx1 = ctx.markScalarBranch scru)) := by
  cases pat with
  | dflt =>
    rw [checkAlts.eq_4 _ _ _ _ _ _ _ _ (fun _ _ _ h => by cases h)] at hchk
    rw [perceusAltsWf.eq_4 _ _ _ _ _ _ _ _ _ _ (fun _ _ _ h => by cases h)] at hwf
    obtain ⟨j1, h1, hrest⟩ := except_bind_ok hchk
    obtain ⟨j2, h2, hj⟩ := except_bind_ok hrest
    simp only [pure, Except.pure, Except.ok.injEq] at hj
    have ha1 := Bool.and_eq_true _ _ |>.mp hwf
    have ha2 := Bool.and_eq_true _ _ |>.mp ha1.1
    exact ⟨j1, j2, ctx, hj.symm, h1, h2, ha2.2, ha1.2, ⟨ctx, Or.inl rfl, Or.inl rfl⟩⟩
  | ctor cidx cname =>
    have hctx1 : ∀ (c1 : RcCtx),
        c1 = (if env.scalarCtors.contains cname = true then ctx.markScalarBranch scru else ctx) →
        c1 = ctx ∨ c1 = ctx.markScalarBranch scru := fun c1 hc => by
      by_cases hsc : env.scalarCtors.contains cname = true
      · simp only [hsc, ↓reduceIte] at hc; exact Or.inr hc
      · simp only [hsc, Bool.false_eq_true, ↓reduceIte] at hc; exact Or.inl hc
    cases cidx with
    | zero =>
      cases tgt? with
      | none =>
        rw [checkAlts.eq_3 _ _ _ _ _ _ _ _ _ _ (fun _ _ hs _ => by cases hs)] at hchk
        rw [perceusAltsWf.eq_3 _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ hs _ => by cases hs)] at hwf
        obtain ⟨j1, h1, hrest⟩ := except_bind_ok hchk
        obtain ⟨j2, h2, hj⟩ := except_bind_ok hrest
        simp only [pure, Except.pure, Except.ok.injEq] at hj
        have ha1 := Bool.and_eq_true _ _ |>.mp hwf
        have ha2 := Bool.and_eq_true _ _ |>.mp ha1.1
        exact ⟨j1, j2, _, hj.symm, h1, h2, ha2.2, ha1.2, ⟨_, Or.inl rfl, hctx1 _ rfl⟩⟩
      | some tgt =>
        rw [checkAlts.eq_2 _ _ _ _ _ _ _ _ _ _ cname rfl] at hchk
        rw [perceusAltsWf.eq_2 _ _ _ _ _ _ _ _ _ _ _ _ cname rfl] at hwf
        obtain ⟨j1, h1, hrest⟩ := except_bind_ok hchk
        obtain ⟨j2, h2, hj⟩ := except_bind_ok hrest
        simp only [pure, Except.pure, Except.ok.injEq] at hj
        have ha1 := Bool.and_eq_true _ _ |>.mp hwf
        have ha2 := Bool.and_eq_true _ _ |>.mp ha1.1
        exact ⟨j1, j2, _, hj.symm, h1, h2, ha2.2, ha1.2,
          ⟨_, Or.inr ⟨tgt, rfl, rfl⟩, hctx1 _ rfl⟩⟩
    | succ cidx' =>
      rw [checkAlts.eq_3 _ _ _ _ _ _ _ _ _ _ (fun _ _ _ hc => by cases hc)] at hchk
      rw [perceusAltsWf.eq_3 _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ _ hc => by cases hc)] at hwf
      obtain ⟨j1, h1, hrest⟩ := except_bind_ok hchk
      obtain ⟨j2, h2, hj⟩ := except_bind_ok hrest
      simp only [pure, Except.pure, Except.ok.injEq] at hj
      have ha1 := Bool.and_eq_true _ _ |>.mp hwf
      have ha2 := Bool.and_eq_true _ _ |>.mp ha1.1
      exact ⟨j1, j2, _, hj.symm, h1, h2, ha2.2, ha1.2, ⟨_, Or.inl rfl, hctx1 _ rfl⟩⟩

end UnwrapHelpers

section StaticCheckCode

private def StaticCodeProp (code : LcCode) : Prop :=
  ∀ env retTy jps ctx sm jumps,
    CtxStaticInv ctx → JpsScopeIn jps ctx →
    checkCode env retTy jps ctx code = Except.ok jumps →
    perceusCodeWf env retTy jps ctx sm code = true →
    ∀ jc ∈ jumps, CtxStaticInv jc.2 ∧ ∃ info ∈ jps,
      info.id = jc.1 ∧ (jc.2.vars.map RcVar.id).Perm info.scopeIds

private def StaticAltsProp (alts : List (LcPat × LcCode)) : Prop :=
  ∀ env retTy jps ctx sm scru scruTy tgt? jumps,
    CtxStaticInv ctx → JpsScopeIn jps ctx →
    checkAlts env retTy jps ctx scru tgt? alts = Except.ok jumps →
    perceusAltsWf env retTy jps ctx sm scru scruTy tgt? alts = true →
    ∀ jc ∈ jumps, CtxStaticInv jc.2 ∧ ∃ info ∈ jps,
      info.id = jc.1 ∧ (jc.2.vars.map RcVar.id).Perm info.scopeIds

private theorem staticCode_jp {j : Nat} {ps : List LcParam} {body k : LcCode}
    (ihBody : StaticCodeProp body) (ihK : StaticCodeProp k) :
    StaticCodeProp (LcCode.jp j ps body k) := by
  intro env retTy jps ctx sm jumps hs hjps hchk hwf jc hjc
  rw [checkCode.eq_2] at hchk
  rw [perceusCodeWf.eq_3] at hwf
  dsimp only at hchk hwf
  let jInfo : RcJpInfo := { id := j, params := ps, scopeIds := ctx.vars.map (·.id) }
  have ha1 := Bool.and_eq_true _ _ |>.mp hwf
  have ha2 := Bool.and_eq_true _ _ |>.mp ha1.1
  have ha3 := Bool.and_eq_true _ _ |>.mp ha2.1
  have ha4 := Bool.and_eq_true _ _ |>.mp ha3.1
  have ha5 := Bool.and_eq_true _ _ |>.mp ha4.1
  have ha6 := Bool.and_eq_true _ _ |>.mp ha5.1
  have hnotJ : j ∉ jps.map RcJpInfo.id := fun hm => by
    obtain ⟨info, hi, hid⟩ := List.mem_map.mp hm
    have hne := List.all_eq_true.mp ha6.1 info hi
    simp [hid] at hne
  have hjpsK : JpsScopeIn (jInfo :: jps) ctx := by
    refine ⟨List.nodup_cons.mpr ⟨hnotJ, hjps.1⟩, fun info hi => ?_⟩
    rcases List.mem_cons.mp hi with rfl | hi'
    · exact ⟨decide_eq_true_iff.mp ha6.2, hs.1,
        fun id hid => (get?_isSome_iff_mem_map_id ctx id).mpr hid⟩
    · exact hjps.2 info hi'
  obtain ⟨jumpsK, hK, hrest1⟩ := except_bind_ok hchk
  obtain ⟨optC, hmerge, hrest2⟩ := except_bind_ok hrest1
  have hResK := ihK env retTy (jInfo :: jps) ctx sm jumpsK hs hjpsK hK ha2.2
  have hmy : ∀ c ∈ (jumpsK.filter (·.1 == j)).map Prod.snd,
      CtxStaticInv c ∧ (c.vars.map RcVar.id).Perm (ctx.vars.map RcVar.id) := by
    intro c hc
    obtain ⟨jc', hjc', rfl⟩ := List.mem_map.mp hc
    have hmem := (List.mem_filter.mp hjc').1
    have hjeq : jc'.1 = j := beq_iff_eq.mp (List.mem_filter.mp hjc').2
    obtain ⟨hsc, info, hi, hid, hperm⟩ := hResK jc' hmem
    have hinfo : info = jInfo := by
      rcases List.mem_cons.mp hi with rfl | hi'
      · rfl
      · exact absurd (hid.trans hjeq) fun heq =>
          hnotJ (heq ▸ List.mem_map.mpr ⟨info, hi', rfl⟩)
    subst hinfo
    exact ⟨hsc, hperm⟩
  obtain ⟨hsB, _, hkeepB, _, _⟩ := jpBaseCtx_invs_of_jumps hs hmerge hmy
  have hbase_eq : jpBaseCtx env retTy jps ctx j ps k = optC.getD ctx :=
    jpBaseCtx_eq_of_check hK hmerge
  have hfrB : ps.all (binderFreshOwned (optC.getD ctx) ·.id) = true := by
    simpa [hbase_eq] using ha5.2
  have hwfB : perceusCodeWf env retTy jps ((optC.getD ctx).bindParams ps) [] body = true := by
    simpa [hbase_eq] using ha1.2
  obtain ⟨hsBP, hkeepBP⟩ := bindParams_static_invs hsB (decide_eq_true_iff.mp ha6.2) hfrB
  have hjpsB : JpsScopeIn jps ((optC.getD ctx).bindParams ps) :=
    jpsScopeIn_mono hjps fun id hid => hkeepBP id (hkeepB id hid)
  have hbody_eq : ∃ jumpsBody,
      checkCode env retTy jps ((optC.getD ctx).bindParams ps) body = Except.ok jumpsBody ∧
      jumps = jumpsK.filter (·.1 != j) ++ jumpsBody := by
    cases optC with
    | none =>
      simp only [bind, Except.bind, pure, Except.pure] at hrest2
      obtain ⟨jb, hjb, hj⟩ := except_bind_ok hrest2
      simp only [Except.ok.injEq] at hj
      exact ⟨jb, hjb, hj.symm⟩
    | some c =>
      simp only [bind, Except.bind, pure, Except.pure] at hrest2
      obtain ⟨jb, hjb, hj⟩ := except_bind_ok hrest2
      simp only [Except.ok.injEq] at hj
      exact ⟨jb, hjb, hj.symm⟩
  obtain ⟨jumpsBody, hB, hjeq⟩ := hbody_eq
  rw [hjeq] at hjc
  rcases List.mem_append.mp hjc with hOut | hInB
  · have hmem := (List.mem_filter.mp hOut).1
    have hne : jc.1 ≠ j := by
      simpa using (List.mem_filter.mp hOut).2
    obtain ⟨hsc, info, hi, hid, hperm⟩ := hResK jc hmem
    rcases List.mem_cons.mp hi with rfl | hi'
    · exact absurd hid.symm hne
    · exact ⟨hsc, info, hi', hid, hperm⟩
  · exact ihBody env retTy jps ((optC.getD ctx).bindParams ps) [] jumpsBody
      hsBP hjpsB hB hwfB jc hInB

private theorem staticCode_jmp {j : Nat} {as : List LcArg} :
    StaticCodeProp (LcCode.jmp j as) := by
  intro env retTy jps ctx sm jumps hs hjps hchk _ jc hjc
  rw [checkCode.eq_3] at hchk
  cases hf : jps.find? (·.id == j) with
  | none => rw [hf] at hchk; cases hchk
  | some info =>
    rw [hf] at hchk
    obtain ⟨ctx1, ha, hrest1⟩ := except_bind_ok hchk
    obtain ⟨u, _, hres⟩ := except_bind_ok hrest1
    cases u
    simp only [pure, Except.pure, Except.ok.injEq] at hres
    subst hres
    simp only [List.mem_singleton] at hjc
    subst hjc
    obtain ⟨hs1, hkeep1⟩ := ctxStaticInv_applyArgs hs ha
    have hsR := restrict_static_invs hs1 info.scopeIds
    have hinfo_mem : info ∈ jps := List.mem_of_find?_eq_some hf
    have hfs := List.find?_some hf
    have hinfo_id : info.id = j := beq_iff_eq.mp hfs
    have hsub : ∀ id ∈ info.scopeIds, (ctx1.get? id).isSome = true := fun id hid =>
      hkeep1 id ((hjps.2 info hinfo_mem).2.2 id hid)
    exact ⟨hsR, info, hinfo_mem, hinfo_id,
      perm_scopeIds_of_subset hs1.1 (hjps.2 info hinfo_mem).2.1 hsub⟩

private theorem static_rec_all (code : LcCode) : StaticCodeProp code := by
  refine @LcCode.rec StaticCodeProp StaticAltsProp (fun a => StaticCodeProp a.2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ code
  · intro x ty v k ih
    intro env retTy jps ctx sm jumps hs hjps hchk hwf jc hjc
    obtain ⟨ctx', sm', hcv, hwfv, _, hk, hwfk⟩ := checkCode_let_unwrap hchk hwf
    obtain ⟨hs', hkeep'⟩ := checkVal_static_invs hs hwfv hcv
    exact ih env retTy jps ctx' sm' jumps hs' (jpsScopeIn_mono hjps hkeep') hk hwfk jc hjc
  · intro j ps body k ihB ihK; exact staticCode_jp ihB ihK
  · intro j as; exact staticCode_jmp
  · intro x alts ihA
    intro env retTy jps ctx sm jumps hs hjps hchk hwf jc hjc
    rw [checkCode.eq_4] at hchk
    rw [perceusCodeWf.eq_5] at hwf
    obtain ⟨u, _, hA⟩ := except_bind_ok hchk
    cases u
    cases hg : ctx.get? x with
    | none => rw [hg] at hwf; simp at hwf
    | some vx =>
      rw [hg] at hwf
      exact ihA env retTy jps ctx sm x vx.ty _ jumps hs hjps hA hwf jc hjc
  · intro a env retTy jps ctx sm jumps hs hjps hchk _ jc hjc
    rw [checkCode.eq_5] at hchk
    dsimp only at hchk
    by_cases hrc : retTy.needsRc = true
    · simp only [hrc, ↓reduceIte] at hchk
      obtain ⟨_, _, hres⟩ := except_bind_ok hchk
      obtain ⟨_, _, hj⟩ := except_bind_ok hres
      simp only [pure, Except.pure, Except.ok.injEq] at hj
      subst hj; cases hjc
    · simp only [hrc, Bool.false_eq_true, ↓reduceIte] at hchk
      obtain ⟨_, _, hres⟩ := except_bind_ok hchk
      obtain ⟨_, _, hres2⟩ := except_bind_ok hres
      obtain ⟨_, _, hj⟩ := except_bind_ok hres2
      simp only [pure, Except.pure, Except.ok.injEq] at hj
      subst hj; cases hjc
  · intro env retTy jps ctx sm jumps _ _ hchk _ jc hjc
    rw [checkCode.eq_6] at hchk
    simp only [pure, Except.pure, Except.ok.injEq] at hchk
    subst hchk; cases hjc
  · intro x i y k ih env retTy jps ctx sm jumps hs hjps hchk hwf jc hjc
    obtain ⟨ctx1, _, hca, hk, hwfk⟩ := checkCode_oset_unwrap hchk hwf
    have hcons : CtxStaticInv ctx1 ∧
        (∀ id, (ctx.get? id).isSome = true → (ctx1.get? id).isSome = true) := by
      cases y with
      | erased =>
        simp [RcCtx.consumeArg, pure, Except.pure] at hca; cases hca
        exact ⟨hs, fun _ h => h⟩
      | var yid =>
        exact ⟨ctxStaticInv_consumeVar hs hca, fun id hid => get?_isSome_consumeVar hca id hid⟩
    exact ih env retTy jps ctx1 sm jumps hcons.1 (jpsScopeIn_mono hjps hcons.2) hk hwfk jc hjc
  · intro x i y k ih env retTy jps ctx sm jumps hs hjps hchk hwf jc hjc
    rw [checkCode.eq_8] at hchk
    rw [perceusCodeWf.eq_12] at hwf
    obtain ⟨_, _, h1⟩ := except_bind_ok hchk
    obtain ⟨_, _, hk⟩ := except_bind_ok h1
    exact ih env retTy jps ctx _ jumps hs hjps hk (Bool.and_eq_true _ _ |>.mp hwf).2 jc hjc
  · intro x n off y ty k ih env retTy jps ctx sm jumps hs hjps hchk hwf jc hjc
    rw [checkCode.eq_9] at hchk
    rw [perceusCodeWf.eq_13] at hwf
    obtain ⟨_, _, h1⟩ := except_bind_ok hchk
    obtain ⟨_, _, hk⟩ := except_bind_ok h1
    exact ih env retTy jps ctx _ jumps hs hjps hk (Bool.and_eq_true _ _ |>.mp hwf).2 jc hjc
  · intro x cidx k ih env retTy jps ctx sm jumps hs hjps hchk hwf jc hjc
    rw [checkCode.eq_10] at hchk
    rw [perceusCodeWf.eq_14] at hwf
    obtain ⟨_, _, hk⟩ := except_bind_ok hchk
    exact ih env retTy jps ctx sm jumps hs hjps hk (Bool.and_eq_true _ _ |>.mp hwf).2 jc hjc
  · intro x n chk k ih env retTy jps ctx sm jumps hs hjps hchk hwf jc hjc
    obtain ⟨v, ctx1, hg, _, h1, hk, hwfk⟩ := checkCode_inc_unwrap hchk hwf
    rcases h1 with rfl | ⟨_, rfl⟩
    · exact ih env retTy jps ctx1 sm jumps hs hjps hk hwfk jc hjc
    · obtain ⟨hs1, hk1⟩ := ctxStaticInv_inc hs hg
      exact ih env retTy jps _ sm jumps hs1 (jpsScopeIn_mono hjps hk1) hk hwfk jc hjc
  · intro x n chk k ih env retTy jps ctx sm jumps hs hjps hchk hwf jc hjc
    obtain ⟨ctx1, hcons, hk, hwfk⟩ := checkCode_dec_unwrap hchk hwf
    have hs1 := ctxStaticInv_consumeVar hs hcons
    exact ih env retTy jps ctx1 sm jumps hs1
      (jpsScopeIn_mono hjps (fun id hid => get?_isSome_consumeVar hcons id hid)) hk hwfk jc hjc
  · intro x k ih env retTy jps ctx sm jumps hs hjps hchk hwf jc hjc
    obtain ⟨ctx1, _, hcons, hk, hwfk⟩ := checkCode_del_unwrap hchk hwf
    have hs1 := ctxStaticInv_consumeVar hs hcons
    exact ih env retTy jps ctx1 _ jumps hs1
      (jpsScopeIn_mono hjps (fun id hid => get?_isSome_consumeVar hcons id hid)) hk hwfk jc hjc
  · intro env retTy jps ctx sm scru scruTy tgt? jumps _ _ hchk _ jc hjc
    rw [checkAlts.eq_1] at hchk
    simp only [pure, Except.pure, Except.ok.injEq] at hchk
    subst hchk; cases hjc
  · intro hd tl ihB ihR env retTy jps ctx sm scru scruTy tgt? jumps hs hjps hchk hwf jc hjc
    obtain ⟨j1, j2, ctxB, rfl, h1, h2, hwf1, hwf2, ⟨ctx1, hbr, hmsb⟩⟩ :=
      checkAlts_cons_unwrap hchk hwf
    have h1s : CtxStaticInv ctx1 ∧
        (∀ id, (ctx.get? id).isSome = true → (ctx1.get? id).isSome = true) := by
      rcases hmsb with rfl | rfl
      · exact ⟨hs, fun _ h => h⟩
      · exact ctxStaticInv_markScalarBranch hs scru
    have hBs : CtxStaticInv ctxB ∧
        (∀ id, (ctx.get? id).isSome = true → (ctxB.get? id).isSome = true) := by
      rcases hbr with rfl | ⟨tgt, _, rfl⟩
      · exact h1s
      · obtain ⟨hs2, hk2⟩ := ctxStaticInv_markExcl h1s.1 tgt
        exact ⟨hs2, fun id hid => hk2 id (h1s.2 id hid)⟩
    rcases List.mem_append.mp hjc with hmem1 | hmem2
    · exact ihB env retTy jps ctxB sm j1 hBs.1 (jpsScopeIn_mono hjps hBs.2) h1 hwf1 jc hmem1
    · exact ihR env retTy jps ctx sm scru scruTy tgt? j2 hs hjps h2 hwf2 jc hmem2
  · intro _ c ih; exact ih

/-- Every jump context returned by `checkCode` preserves `CtxStaticInv` and `scopeIds`. -/
public theorem checkCode_static_invs {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {sm : List (Nat × Nat × List Bool)} {code : LcCode} {jumps : List (Nat × RcCtx)}
    (hs : CtxStaticInv ctx) (hjps : JpsScopeIn jps ctx)
    (hchk : checkCode env retTy jps ctx code = Except.ok jumps)
    (hwf : perceusCodeWf env retTy jps ctx sm code = true) :
    ∀ jc ∈ jumps, CtxStaticInv jc.2 ∧ ∃ info ∈ jps,
      info.id = jc.1 ∧ (jc.2.vars.map RcVar.id).Perm info.scopeIds :=
  static_rec_all code env retTy jps ctx sm jumps hs hjps hchk hwf

/-- Join-point `baseCtx` static invariants, ID permutation, and weakening facts from `jp` WF. -/
public theorem jpBaseCtx_static_invs {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {sm : List (Nat × Nat × List Bool)} {j : Nat} {ps : List LcParam}
    {body k : LcCode} {jumpsK : List (Nat × RcCtx)} {optC : Option RcCtx}
    (hs : CtxStaticInv ctx) (hjps : JpsScopeIn jps ctx)
    (hK : checkCode env retTy ({ id := j, params := ps, scopeIds := ctx.vars.map (·.id) } :: jps)
      ctx k = Except.ok jumpsK)
    (hm : mergeJpList ((jumpsK.filter (·.1 == j)).map Prod.snd) = Except.ok optC)
    (hwf : perceusCodeWf env retTy jps ctx sm (LcCode.jp j ps body k) = true) :
    let baseCtx := optC.getD ctx
    let myJumps := (jumpsK.filter (·.1 == j)).map Prod.snd
    CtxStaticInv baseCtx ∧
    (baseCtx.vars.map RcVar.id).Perm (ctx.vars.map RcVar.id) ∧
    (∀ id, (ctx.get? id).isSome = true → (baseCtx.get? id).isSome = true) ∧
    (∀ c ∈ myJumps, CtxWeakens baseCtx c) ∧
    (∀ c0 rest, myJumps = c0 :: rest →
      baseCtx.vars.map RcVar.id = c0.vars.map RcVar.id ∧
      (∀ w ∈ baseCtx.vars, ∃ v ∈ c0.vars, w.id = v.id ∧ w.ty = v.ty) ∧
      (∀ p, p ∈ baseCtx.sharedPreds → p ∈ c0.sharedPreds)) := by
  rw [perceusCodeWf.eq_3] at hwf; dsimp only at hwf
  let jInfo : RcJpInfo := { id := j, params := ps, scopeIds := ctx.vars.map (·.id) }
  have ha1 := Bool.and_eq_true _ _ |>.mp hwf
  have ha2 := Bool.and_eq_true _ _ |>.mp ha1.1
  have ha3 := Bool.and_eq_true _ _ |>.mp ha2.1
  have ha4 := Bool.and_eq_true _ _ |>.mp ha3.1
  have ha5 := Bool.and_eq_true _ _ |>.mp ha4.1
  have ha6 := Bool.and_eq_true _ _ |>.mp ha5.1
  have hnotJ : j ∉ jps.map RcJpInfo.id := fun hmem => by
    obtain ⟨info, hi, hid⟩ := List.mem_map.mp hmem
    have hne := List.all_eq_true.mp ha6.1 info hi
    simp [hid] at hne
  have hjpsK : JpsScopeIn (jInfo :: jps) ctx := by
    refine ⟨List.nodup_cons.mpr ⟨hnotJ, hjps.1⟩, fun info hi => ?_⟩
    rcases List.mem_cons.mp hi with rfl | hi'
    · exact ⟨decide_eq_true_iff.mp ha6.2, hs.1,
        fun id hid => (get?_isSome_iff_mem_map_id ctx id).mpr hid⟩
    · exact hjps.2 info hi'
  have hResK := checkCode_static_invs hs hjpsK hK ha2.2
  refine jpBaseCtx_invs_of_jumps hs hm fun c hc => ?_
  obtain ⟨jc, hjc, rfl⟩ := List.mem_map.mp hc
  have hmem := (List.mem_filter.mp hjc).1
  have hjeq : jc.1 = j := beq_iff_eq.mp (List.mem_filter.mp hjc).2
  obtain ⟨hsc, info, hi, hid, hperm⟩ := hResK jc hmem
  have hinfo : info = jInfo := by
    rcases List.mem_cons.mp hi with rfl | hi'
    · rfl
    · exact absurd (hid.trans hjeq) fun heq =>
        hnotJ (heq ▸ List.mem_map.mpr ⟨info, hi', rfl⟩)
  subst hinfo
  exact ⟨hsc, hperm⟩

end StaticCheckCode

end LeanQbe.T.LeanLCNF.Sem
