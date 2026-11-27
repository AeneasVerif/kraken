module

public import LeanQbe.T.LeanLCNF.Sem.PerceusJp2

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T

section StaticAgreeLemmas

private theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = Except.ok b) : ∃ a, x = Except.ok a ∧ f a = Except.ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- Static agreement on live variable types, liveness, and `sharedPreds` across paths. -/
@[expose] public def StaticAgree (avoidIds : List Nat) (ctx0 ctx : RcCtx) : Prop :=
  (∀ id ∈ avoidIds, (ctx.get? id).map RcVar.isLive = some true →
    (ctx0.get? id).map RcVar.isLive = some true ∧
    (ctx0.get? id).map (·.ty) = (ctx.get? id).map (·.ty)) ∧
  (∀ p ∈ ctx.sharedPreds, p.1 ∈ avoidIds →
    p ∈ ctx0.sharedPreds ∧ (ctx0.get? p.2).map (·.ty) = (ctx.get? p.2).map (·.ty))

/-- `StaticAgree` is reflexive. -/
public theorem staticAgree_refl (avoidIds : List Nat) (ctx : RcCtx) :
    StaticAgree avoidIds ctx ctx :=
  ⟨fun _ _ h => ⟨h, rfl⟩, fun _ hp _ => ⟨hp, rfl⟩⟩

@[expose] public def CtxLiveTyBack (c1 c2 : RcCtx) : Prop :=
  (c1.vars.map RcVar.id).Nodup →
    (c2.vars.map RcVar.id).Nodup ∧
    (∀ z, (c2.get? z).map (·.ty) = (c1.get? z).map (·.ty) ∧
      ((c2.get? z).map RcVar.isLive = some true → (c1.get? z).map RcVar.isLive = some true)) ∧
    (∀ p, p ∈ c2.sharedPreds → p ∈ c1.sharedPreds)

/-- Type and backward-liveness preservation through `RcCtx.invalidateChildren`. -/
public theorem invalidateChildren_live_ty_back (ctx : RcCtx)
    (hnd : (ctx.vars.map RcVar.id).Nodup) (x z : Nat) :
    ((ctx.invalidateChildren x).vars.map RcVar.id).Nodup ∧
    ((ctx.invalidateChildren x).get? z).map (·.ty) = (ctx.get? z).map (·.ty) ∧
    (((ctx.invalidateChildren x).get? z).map RcVar.isLive = some true →
      (ctx.get? z).map RcVar.isLive = some true) ∧
    (∀ p, p ∈ (ctx.invalidateChildren x).sharedPreds → p ∈ ctx.sharedPreds) := by
  have hnd1 : ((ctx.invalidateChildren x).vars.map RcVar.id).Nodup := by
    have hm : ((ctx.invalidateChildren x).vars.map RcVar.id) = ctx.vars.map RcVar.id := by
      unfold RcCtx.invalidateChildren; simp only [List.map_map]
      congr 1; funext v; dsimp only [Function.comp_def]; split <;> rfl
    rw [hm]; exact hnd
  refine ⟨hnd1, ?_, ?_, fun p hp => ?_⟩
  · cases hres : (ctx.invalidateChildren x).get? z with
    | none =>
      cases hg : ctx.get? z with
      | none => rfl
      | some v =>
        exfalso
        have his : ((ctx.invalidateChildren x).get? z).isSome = true :=
          get?_isSome_invalidateChildren ctx x z (by simp [hg])
        rw [hres] at his; cases his
    | some v' =>
      obtain ⟨w, hw, hweq⟩ := List.mem_map.mp (RcCtx.get?_mem hres).1
      have hwid : w.id = z := by
        have h1 := (RcCtx.get?_mem hres).2
        rw [← hweq] at h1
        by_cases h : (w.parent? == some x) = true <;> simp [h] at h1 <;> exact h1
      have hgw : ctx.get? z = some w := hwid ▸ (RcCtx.mem_get?_iff hnd).mpr hw
      rw [hgw, ← hweq]
      dsimp only [Option.map]; by_cases h : (w.parent? == some x) = true <;> simp [h]
  · intro hl
    cases hres : (ctx.invalidateChildren x).get? z with
    | none => rw [hres] at hl; cases hl
    | some v' =>
      rw [hres] at hl; dsimp only [Option.map] at hl
      obtain ⟨w, hw, hweq⟩ := List.mem_map.mp (RcCtx.get?_mem hres).1
      have hwid : w.id = z := by
        have h1 := (RcCtx.get?_mem hres).2
        rw [← hweq] at h1
        by_cases h : (w.parent? == some x) = true <;> simp [h] at h1 <;> exact h1
      have hgw : ctx.get? z = some w := hwid ▸ (RcCtx.mem_get?_iff hnd).mpr hw
      rw [hgw]; dsimp only [Option.map]
      rw [← hweq] at hl
      by_cases h : (w.parent? == some x) = true
      · simp only [h, ↓reduceIte] at hl
        by_cases hno : w.noRc = true <;> by_cases hp : w.persistent = true <;>
          by_cases hrt : w.resetTok = true <;> by_cases ho : decide (w.owned > 0) = true <;>
          simp [RcVar.isLive, hno, hp, hrt, ho] at hl ⊢
      · simp only [h, Bool.false_eq_true, ↓reduceIte] at hl; exact hl
  · simp only [RcCtx.invalidateChildren, List.mem_filter] at hp; exact hp.1

/-- Type and backward-liveness preservation through `RcCtx.put`. -/
public theorem put_same_ty_live {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    {x : Nat} {v : RcVar} (v' : RcVar) (hg : ctx.get? x = some v) (hid : v'.id = v.id)
    (hty : v'.ty = v.ty) (hl : v'.isLive = true → v.isLive = true) (z : Nat) :
    ((ctx.put v').get? z).map (·.ty) = (ctx.get? z).map (·.ty) ∧
    (((ctx.put v').get? z).map RcVar.isLive = some true →
      (ctx.get? z).map RcVar.isLive = some true) := by
  rw [RcCtx.put_get? hnd]
  by_cases hz : (z == v'.id) = true
  · have heq : z = x := (beq_iff_eq.mp hz).trans (hid.trans (RcCtx.get?_mem hg).2)
    simp only [hz, ↓reduceIte]
    rw [heq, hg]
    refine ⟨by simp [hty], fun h => ?_⟩
    simp only [Option.map_some, Option.some.injEq] at h ⊢
    exact hl h
  · simp [hz]

/-- Type and backward-liveness preservation through `RcCtx.consumeVar`. -/
public theorem consumeVar_live_ty_back {ctx ctx' : RcCtx} {x n : Nat}
    (hcons : ctx.consumeVar x n = Except.ok ctx') : CtxLiveTyBack ctx ctx' := by
  intro hnd
  unfold RcCtx.consumeVar at hcons
  cases hg : ctx.get? x with
  | none => rw [hg] at hcons; cases hcons
  | some v =>
    rw [hg] at hcons
    by_cases hnp : (v.noRc || v.persistent) = true
    · simp [hnp, pure, Except.pure] at hcons; cases hcons
      exact ⟨hnd, fun _ => ⟨rfl, id⟩, fun _ hp => hp⟩
    · simp only [hnp, Bool.false_eq_true, ↓reduceIte] at hcons
      by_cases hn0 : (n == 0) = true
      · simp [hn0, pure, Except.pure] at hcons; cases hcons
        exact ⟨hnd, fun _ => ⟨rfl, id⟩, fun _ hp => hp⟩
      · simp only [hn0, Bool.false_eq_true, ↓reduceIte] at hcons
        by_cases hlt : v.owned < n
        · simp [hlt] at hcons
        · simp only [hlt, ↓reduceIte, pure, Except.pure] at hcons
          let v' : RcVar := {
            id := v.id, ty := v.ty, noRc := v.noRc, persistent := v.persistent,
            owned := v.owned - n, borrowed := v.borrowed, parent? := v.parent?,
            excl := if (v.owned - n == 0) = true then false else v.excl,
            resetTok := if (v.owned - n == 0) = true then false else v.resetTok }
          have hlback : v'.isLive = true → v.isLive = true := fun hl => by
            dsimp only [v'] at hl
            by_cases hno : v.noRc = true
            · simp [RcVar.isLive, hno]
            · by_cases hp : v.persistent = true
              · simp [RcVar.isLive, hp]
              · by_cases hb : v.borrowed = true
                · simp [RcVar.isLive, hb]
                · by_cases hrt : v.resetTok = true
                  · simp [RcVar.isLive, hrt]
                  · have hgt : 0 < v.owned := by
                      by_cases hze : (v.owned - n == 0) = true
                      · have hez := beq_iff_eq.mp hze
                        simp [RcVar.isLive, hno, hp, hb, hze] at hl
                        omega
                      · have hne : v.owned - n ≠ 0 := fun h => hze (by simp [h])
                        omega
                    simp [RcVar.isLive, hgt]
          have hndP := RcCtx.put_nodup hnd v'
          have hput : CtxLiveTyBack ctx (ctx.put v') := fun _ =>
            ⟨hndP, fun z => put_same_ty_live hnd v' hg rfl rfl hlback z, fun _ hp => hp⟩
          split at hcons <;> cases hcons
          · obtain ⟨_, hty1, _⟩ := hput hnd
            have hinv := invalidateChildren_live_ty_back (ctx.put v') hndP x
            refine ⟨(hinv 0).1, fun z => ?_, fun p hp => (hput hnd).2.2 p ((hinv 0).2.2.2 p hp)⟩
            obtain ⟨_, hti, hli, _⟩ := hinv z
            exact ⟨hti.trans (hty1 z).1, fun h => (hty1 z).2 (hli h)⟩
          · exact hput hnd

private theorem applyArgs_live_ty_back {ctx ctx' : RcCtx} {as : List LcArg} {bs : List Bool}
    (ha : ctx.applyArgs as bs = Except.ok ctx') : CtxLiveTyBack ctx ctx' :=
  applyArgs_rel CtxLiveTyBack
    (fun _ hnd => ⟨hnd, fun _ => ⟨rfl, id⟩, fun _ hp => hp⟩)
    (fun h12 h23 hnd =>
      let ⟨hnd2, h12', hs12⟩ := h12 hnd
      let ⟨hnd3, h23', hs23⟩ := h23 hnd2
      ⟨hnd3, fun z => ⟨(h23' z).1.trans (h12' z).1, fun h => (h12' z).2 ((h23' z).2 h)⟩,
        fun p hp => hs12 p (hs23 p hp)⟩)
    (fun hcons => consumeVar_live_ty_back hcons)
    ha

private theorem put_live_ty_back {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (v : RcVar) {z : Nat} (hne : z ≠ v.id) : (ctx.put v).get? z = ctx.get? z := by
  have hnb : (z == v.id) = false := beq_false_of_ne hne
  simp [RcCtx.put_get? hnd, hnb]

private theorem staticAgree_bind_step {ctx0 ctx ctx' : RcCtx} {avoidIds : List Nat} {x : Nat}
    (hne : ∀ id ∈ avoidIds, id ≠ x) (hagree : StaticAgree avoidIds ctx0 ctx)
    (hstep : (∀ z, z ≠ x → (ctx'.get? z).map (·.ty) = (ctx.get? z).map (·.ty) ∧
      ((ctx'.get? z).map RcVar.isLive = some true → (ctx.get? z).map RcVar.isLive = some true)) ∧
      (∀ p ∈ ctx'.sharedPreds, p.1 ≠ x → p ∈ ctx.sharedPreds ∧ p.2 ≠ x)) :
    StaticAgree avoidIds ctx0 ctx' := by
  refine ⟨fun id hid hl => ?_, fun p hp hp1 => ?_⟩
  · have hne1 := hne id hid
    have hl0 := (hstep.1 id hne1).2 hl
    obtain ⟨hl', hty'⟩ := hagree.1 id hid hl0
    exact ⟨hl', hty'.trans (hstep.1 id hne1).1.symm⟩
  · have hne1 := hne p.1 hp1
    obtain ⟨hpm, hne2⟩ := hstep.2 p hp hne1
    obtain ⟨hp0, hty0⟩ := hagree.2 p hpm hp1
    exact ⟨hp0, hty0.trans (hstep.1 p.2 hne2).1.symm⟩

/-- Type, backward-liveness, and `sharedPreds` preservation for `z ≠ x` across `checkVal`. -/
public theorem checkVal_step_agree {env : RcModEnv} {ctx ctx' : RcCtx} {x : Nat} {ty : LcTy}
    {v : LcVal} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hcv : checkVal env ctx x ty v = Except.ok ctx')
    (hwf : perceusValWf env ctx x ty v = true) :
    (∀ z, z ≠ x → (ctx'.get? z).map (·.ty) = (ctx.get? z).map (·.ty) ∧
      ((ctx'.get? z).map RcVar.isLive = some true → (ctx.get? z).map RcVar.isLive = some true)) ∧
    (∀ p ∈ ctx'.sharedPreds, p.1 ≠ x → p ∈ ctx.sharedPreds ∧ p.2 ≠ x) := by
  have hfr : binderFreshOwned ctx x = true := by
    unfold perceusValWf at hwf; exact (Bool.and_eq_true _ _ |>.mp hwf).1
  have hno_sp : ∀ p ∈ ctx.sharedPreds, p.2 ≠ x := fun p hp =>
    (binderFreshOwned_sharedPreds hfr hp).2
  have of_put_only : ∀ {v' : RcVar}, ctx' = ctx.put v' → v'.id = x →
      (∀ z, z ≠ x → (ctx'.get? z).map (·.ty) = (ctx.get? z).map (·.ty) ∧
        ((ctx'.get? z).map RcVar.isLive = some true →
          (ctx.get? z).map RcVar.isLive = some true)) ∧
      (∀ p ∈ ctx'.sharedPreds, p.1 ≠ x → p ∈ ctx.sharedPreds ∧ p.2 ≠ x) := by
    intro v' hctx hvid; subst hctx
    refine ⟨fun z hne => ?_, fun p hp _ => ⟨hp, hno_sp p hp⟩⟩
    change ((ctx.put v').get? z).map (·.ty) = _ ∧ _
    rw [put_live_ty_back hnd v' (hvid ▸ hne)]; exact ⟨rfl, id⟩
  have of_apply_put : ∀ {ctx1 : RcCtx} {as : List LcArg} {bs : List Bool} {v' : RcVar},
      ctx.applyArgs as bs = Except.ok ctx1 → ctx' = ctx1.put v' → v'.id = x →
      (∀ z, z ≠ x → (ctx'.get? z).map (·.ty) = (ctx.get? z).map (·.ty) ∧
        ((ctx'.get? z).map RcVar.isLive = some true →
          (ctx.get? z).map RcVar.isLive = some true)) ∧
      (∀ p ∈ ctx'.sharedPreds, p.1 ≠ x → p ∈ ctx.sharedPreds ∧ p.2 ≠ x) := by
    intro ctx1 as bs v' ha hctx hvid; subst hctx
    obtain ⟨hnd1, hty1, hsp1⟩ := applyArgs_live_ty_back ha hnd
    refine ⟨fun z hne => ?_, fun p hp _ => ⟨hsp1 p hp, hno_sp p (hsp1 p hp)⟩⟩
    change ((ctx1.put v').get? z).map (·.ty) = _ ∧ _
    rw [put_live_ty_back hnd1 v' (hvid ▸ hne)]; exact hty1 z
  unfold checkVal at hcv; dsimp only at hcv
  cases v with
  | lit l =>
    cases l with
    | nat n =>
      by_cases hrc : (!ty.needsRc) = true
      · simp only [hrc, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hcv
        exact of_put_only hcv.symm rfl
      · simp only [hrc, Bool.false_eq_true, ↓reduceIte] at hcv
        by_cases hlt : n < 2 ^ 63 <;>
          simp only [hlt, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hcv <;>
          exact of_put_only hcv.symm rfl
    | str _ => cases hcv; exact of_put_only rfl rfl
    | scalar _ => cases hcv; exact of_put_only rfl rfl
  | erased => cases hcv; exact of_put_only rfl rfl
  | ctor ci as =>
    by_cases hsc : ci.isScalar = true
    · simp only [hsc, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hcv
      exact of_put_only hcv.symm rfl
    · simp only [hsc, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure] at hcv
      cases ha : ctx.applyArgs as (List.replicate as.length false) with
      | error _ => rw [ha] at hcv; cases hcv
      | ok ctx1 => rw [ha] at hcv; cases hcv; exact of_apply_put ha rfl rfl
  | oproj i obj =>
    obtain ⟨bp, _, hrest⟩ := except_bind_ok hcv
    simp only [pure, Except.pure, Except.ok.injEq] at hrest
    exact of_put_only hrest.symm rfl
  | uproj _ obj =>
    obtain ⟨_, _, hrest⟩ := except_bind_ok hcv
    simp only [pure, Except.pure, Except.ok.injEq] at hrest
    exact of_put_only hrest.symm rfl
  | sproj _ _ obj =>
    obtain ⟨_, _, hrest⟩ := except_bind_ok hcv
    simp only [pure, Except.pure, Except.ok.injEq] at hrest
    exact of_put_only hrest.symm rfl
  | box _ y =>
    obtain ⟨_, _, hrest⟩ := except_bind_ok hcv
    simp only [pure, Except.pure, Except.ok.injEq] at hrest
    exact of_put_only hrest.symm rfl
  | unbox y =>
    obtain ⟨_, _, hrest⟩ := except_bind_ok hcv
    simp only [pure, Except.pure, Except.ok.injEq] at hrest
    exact of_put_only hrest.symm rfl
  | isShared y =>
    obtain ⟨u, _, hrest⟩ := except_bind_ok hcv; cases u
    simp only [pure, Except.pure, Except.ok.injEq] at hrest; subst hrest
    refine ⟨fun z hne => ?_, fun p hp hne => ?_⟩
    · have hget_is :
          ({ vars := (ctx.bindOwned x ty).vars,
             sharedPreds := (x, y) :: (ctx.bindOwned x ty).sharedPreds } : RcCtx).get? z =
          (ctx.bindOwned x ty).get? z := rfl
      have hbind_eq : (ctx.bindOwned x ty).get? z = ctx.get? z := by
        unfold RcCtx.bindOwned; exact put_live_ty_back hnd _ hne
      rw [hget_is, hbind_eq]; exact ⟨rfl, id⟩
    · rcases List.mem_cons.mp hp with rfl | hpm
      · exact absurd rfl hne
      · exact ⟨hpm, hno_sp p hpm⟩
  | reset _ _ => unfold perceusValWf at hwf; simp [hfr] at hwf
  | reuse _ _ _ _ => unfold perceusValWf at hwf; simp [hfr] at hwf
  | pap _ _ => unfold perceusValWf at hwf; simp [hfr] at hwf
  | ap _ _ => unfold perceusValWf at hwf; simp [hfr] at hwf
  | fap f as =>
    cases hdecls : env.decls.find? (fun d => d.1 == f) with
    | some dinfo =>
      simp only [hdecls] at hcv
      rcases dinfo with ⟨_, borrows, _, _, isConst⟩
      by_cases hic : (isConst && as.isEmpty) = true
      · simp only [hic, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hcv
        exact of_put_only hcv.symm rfl
      · simp only [hic, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
          at hcv
        cases ha : ctx.applyArgs as borrows with
        | error _ => rw [ha] at hcv; cases hcv
        | ok ctx1 => rw [ha] at hcv; cases hcv; exact of_apply_put ha rfl rfl
    | none =>
      simp only [hdecls] at hcv
      cases hprim : primRcSig f as.length with
      | none => simp only [hprim] at hcv; cases hcv
      | some pr =>
        simp only [hprim, bind, Except.bind, pure, Except.pure] at hcv
        rcases pr with ⟨borrows, retKind⟩
        cases ha : ctx.applyArgs as borrows with
        | error _ => rw [ha] at hcv; cases hcv
        | ok ctx1 =>
          rw [ha] at hcv
          cases retKind with
          | owned => cases hcv; exact of_apply_put ha rfl rfl
          | persistent => cases hcv; exact of_apply_put ha rfl rfl
          | borrowed idx =>
            dsimp only at hcv
            cases has : as[idx]? with
            | none => rw [has] at hcv; cases hcv; exact of_apply_put ha rfl rfl
            | some a =>
              rw [has] at hcv
              cases a with
              | erased => cases hcv; exact of_apply_put ha rfl rfl
              | var src =>
                dsimp only at hcv
                cases hpb : ctx1.projBacking src with
                | error _ => rw [hpb] at hcv; cases hcv
                | ok bp => rw [hpb] at hcv; cases hcv; exact of_apply_put ha rfl rfl

private theorem markScalarBranch_agree {ctx0 ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (scru : Nat) (hchk : ctx.checkLive scru = Except.ok ()) {avoidIds : List Nat}
    (hagree : StaticAgree avoidIds ctx0 ctx) :
    StaticAgree avoidIds ctx0 (ctx.markScalarBranch scru) := by
  have hscru_live : ∃ vs, ctx.get? scru = some vs ∧ vs.isLive = true := by
    unfold RcCtx.checkLive at hchk
    cases hg : ctx.get? scru with
    | none => rw [hg] at hchk; cases hchk
    | some vs =>
      rw [hg] at hchk
      by_cases hl : vs.isLive = true
      · exact ⟨vs, rfl, hl⟩
      · simp [hl] at hchk
  obtain ⟨vs, hgs, hvsl⟩ := hscru_live
  unfold RcCtx.markScalarBranch; rw [hgs]
  by_cases hty : (vs.ty == .tobject || vs.ty == .tagged) = true
  · simp only [hty, ↓reduceIte]
    let v' : RcVar := { id := vs.id, ty := vs.ty, noRc := true }
    have hndP := RcCtx.put_nodup hnd v'
    obtain ⟨_, _, _, hspi⟩ := invalidateChildren_live_ty_back (ctx.put v') hndP scru 0
    refine ⟨fun id hid hl => ?_, fun p hp hp1 => ?_⟩
    · have hlP : ((ctx.put v').get? id).map RcVar.isLive = some true :=
        (invalidateChildren_live_ty_back (ctx.put v') hndP scru id).2.2.1 hl
      have htyP : ((ctx.put v').get? id).map (·.ty) =
          (((ctx.put v').invalidateChildren scru).get? id).map (·.ty) :=
        (invalidateChildren_live_ty_back (ctx.put v') hndP scru id).2.1.symm
      rw [RcCtx.put_get? hnd] at hlP
      by_cases hidEq : (id == v'.id) = true
      · have heq : id = scru := (beq_iff_eq.mp hidEq).trans (RcCtx.get?_mem hgs).2
        have hgs' : ctx.get? id = some vs := heq.symm ▸ hgs
        have hl0 : (ctx.get? id).map RcVar.isLive = some true := by simp [hgs', hvsl]
        obtain ⟨hlC, htyC⟩ := hagree.1 id hid hl0
        have htyEq : ((ctx.put v').get? id).map (·.ty) = (ctx.get? id).map (·.ty) := by
          rw [RcCtx.put_get? hnd]; simp [hidEq, hgs', v']
        exact ⟨hlC, htyC.trans (htyEq.symm.trans htyP)⟩
      · simp only [hidEq, Bool.false_eq_true, ↓reduceIte] at hlP
        obtain ⟨hlC, htyC⟩ := hagree.1 id hid hlP
        have htyEq : ((ctx.put v').get? id).map (·.ty) = (ctx.get? id).map (·.ty) := by
          rw [RcCtx.put_get? hnd]; simp [hidEq]
        exact ⟨hlC, htyC.trans (htyEq.symm.trans htyP)⟩
    · have hpP : p ∈ (ctx.put v').sharedPreds := hspi p hp
      obtain ⟨hp0, hty0⟩ := hagree.2 p hpP hp1
      have hty_inv := (invalidateChildren_live_ty_back (ctx.put v') hndP scru p.2).2.1
      have htyP : ((ctx.put v').get? p.2).map (·.ty) = (ctx.get? p.2).map (·.ty) := by
        rw [RcCtx.put_get? hnd]
        by_cases hpeq : (p.2 == v'.id) = true
        · have heq : p.2 = scru := (beq_iff_eq.mp hpeq).trans (RcCtx.get?_mem hgs).2
          simp only [hpeq, ↓reduceIte]
          rw [heq, hgs]; rfl
        · simp [hpeq]
      exact ⟨hp0, hty0.trans (htyP.symm.trans hty_inv.symm)⟩
  · simp only [hty, Bool.false_eq_true, ↓reduceIte]; exact hagree

private theorem markExcl_agree {ctx0 ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (tgt : Nat) {avoidIds : List Nat} (hagree : StaticAgree avoidIds ctx0 ctx) :
    StaticAgree avoidIds ctx0 (ctx.markExcl tgt) := by
  unfold RcCtx.markExcl
  cases hg : ctx.get? tgt with
  | none => exact hagree
  | some v =>
    dsimp only
    by_cases hc : (!v.noRc && !v.persistent && v.owned == 1) = true
    · simp only [hc, ↓reduceIte]
      let v' : RcVar := {
        id := v.id, ty := v.ty, noRc := v.noRc, persistent := v.persistent,
        owned := v.owned, borrowed := v.borrowed, parent? := v.parent?, excl := true,
        resetTok := v.resetTok }
      have hmap : ∀ z, ((ctx.put v').get? z).map (·.ty) = (ctx.get? z).map (·.ty) ∧
          (((ctx.put v').get? z).map RcVar.isLive = some true →
            (ctx.get? z).map RcVar.isLive = some true) :=
        fun z => put_same_ty_live hnd v' hg rfl rfl (fun hl => hl) z
      exact ⟨fun id hid hl =>
          let ⟨hl0, hty0⟩ := hagree.1 id hid ((hmap id).2 hl)
          ⟨hl0, hty0.trans (hmap id).1.symm⟩,
        fun p hp hp1 =>
          let ⟨hp0, hty0⟩ := hagree.2 p hp hp1
          ⟨hp0, hty0.trans (hmap p.2).1.symm⟩⟩
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact hagree

private theorem staticAgree_mono_ids {a1 a2 : List Nat} {ctx0 ctx : RcCtx}
    (hsub : ∀ id ∈ a1, id ∈ a2) (h : StaticAgree a2 ctx0 ctx) : StaticAgree a1 ctx0 ctx :=
  ⟨fun id hid hl => h.1 id (hsub id hid) hl, fun p hp hp1 => h.2 p hp (hsub p.1 hp1)⟩

private theorem filter_mut_cons_sub (liveIds mutated : List Nat) (x : Nat) :
    ∀ id ∈ liveIds.filter (fun z => !(x :: mutated).contains z),
      id ∈ liveIds.filter (fun z => !mutated.contains z) := by
  intro id hid
  have h1 := List.mem_filter.mp hid
  refine List.mem_filter.mpr ⟨h1.1, ?_⟩
  have hnot : id ∉ x :: mutated := fun hm => by
    have hc := List.contains_iff_mem.mpr hm
    have h2 := h1.2
    rw [hc] at h2; cases h2
  cases hm : mutated.contains id
  · rfl
  · exact absurd (List.mem_cons_of_mem _ (List.contains_iff_mem.mp hm)) hnot

private theorem ctxWeakens_isLive_back {ctxW ctxS : RcCtx} (hw : CtxWeakens ctxW ctxS) {id : Nat}
    (hlW : (ctxW.get? id).map RcVar.isLive = some true) :
    (ctxS.get? id).map RcVar.isLive = some true := by
  cases hgW : ctxW.get? id with
  | none => rw [hgW] at hlW; cases hlW
  | some w =>
    rw [hgW] at hlW; dsimp only [Option.map] at hlW
    obtain ⟨v, hvm, hid, _, _, hno, hpers, hown, hbr, _, hrt⟩ :=
      hw.2.2.1 w (RcCtx.get?_mem hgW).1
    have hgs : ctxS.get? id = some v :=
      ((RcCtx.get?_mem hgW).2.symm.trans hid) ▸ (RcCtx.mem_get?_iff hw.2.1).mpr hvm
    rw [hgs]; dsimp only [Option.map]
    by_cases h1 : w.noRc = true
    · simp [RcVar.isLive, hno.symm.trans h1]
    · by_cases h2 : w.persistent = true
      · simp [RcVar.isLive, hpers.symm.trans h2]
      · by_cases h3 : w.owned > 0
        · simp [RcVar.isLive, hown ▸ h3]
        · by_cases h4 : w.borrowed = true
          · simp [RcVar.isLive, (hbr h4).1]
          · by_cases h5 : w.resetTok = true
            · by_cases hvrt : v.resetTok = true
              · simp [RcVar.isLive, hvrt]
              · exact absurd (hrt (Bool.eq_false_iff.mpr hvrt)) (by simp [h5])
            · simp [RcVar.isLive, Bool.eq_false_iff.mpr h1, Bool.eq_false_iff.mpr h2,
                Bool.eq_false_iff.mpr h4, Bool.eq_false_iff.mpr h5, h3] at hlW

private def AgreeCodeProp (code : LcCode) : Prop :=
  ∀ env retTy jps ctx sm jumps targetJ liveIds mutated ctx0,
    CtxStaticInv ctx → JpsScopeIn jps ctx →
    checkCode env retTy jps ctx code = Except.ok jumps →
    perceusCodeWf env retTy jps ctx sm code = true →
    jpLiveNoMut targetJ liveIds mutated code = true →
    StaticAgree (liveIds.filter (fun id => !mutated.contains id)) ctx0 ctx →
    ∀ jc ∈ jumps, jc.1 = targetJ → StaticAgree liveIds ctx0 jc.2

private def AgreeAltsProp (alts : List (LcPat × LcCode)) : Prop :=
  ∀ env retTy jps ctx sm scru scruTy tgt? jumps targetJ liveIds mutated ctx0,
    CtxStaticInv ctx → JpsScopeIn jps ctx →
    ctx.checkLive scru = Except.ok () →
    checkAlts env retTy jps ctx scru tgt? alts = Except.ok jumps →
    perceusAltsWf env retTy jps ctx sm scru scruTy tgt? alts = true →
    jpAltsLiveNoMut targetJ liveIds mutated alts = true →
    StaticAgree (liveIds.filter (fun id => !mutated.contains id)) ctx0 ctx →
    ∀ jc ∈ jumps, jc.1 = targetJ → StaticAgree liveIds ctx0 jc.2

private theorem jpBaseCtx_static_agree_aux {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {sm : List (Nat × Nat × List Bool)} {j : Nat} {ps : List LcParam}
    {body k : LcCode} {jumpsK : List (Nat × RcCtx)} {optC : Option RcCtx}
    (ihK : AgreeCodeProp k)
    (hs : CtxStaticInv ctx) (hjps : JpsScopeIn jps ctx)
    (hK : checkCode env retTy ({ id := j, params := ps, scopeIds := ctx.vars.map (·.id) } :: jps)
      ctx k = Except.ok jumpsK)
    (hm : mergeJpList ((jumpsK.filter (·.1 == j)).map Prod.snd) = Except.ok optC)
    (hwf : perceusCodeWf env retTy jps ctx sm (LcCode.jp j ps body k) = true) :
    StaticAgree (baseCtxLiveIds (optC.getD ctx)) ctx (optC.getD ctx) := by
  have hwf_orig := hwf
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
  obtain ⟨_, _, _, hwB, hheadsp⟩ := jpBaseCtx_static_invs hs hjps hK hm hwf_orig
  have hbase_eq : jpBaseCtx env retTy jps ctx j ps k = optC.getD ctx :=
    jpBaseCtx_eq_of_check hK hm
  let baseCtx := optC.getD ctx
  have hnomut_j : jpLiveNoMut j (baseCtxLiveIds baseCtx) [] k = true := by
    simpa [hbase_eq, baseCtxLiveIds] using ha3.2
  cases hmy : (jumpsK.filter (·.1 == j)).map Prod.snd with
  | nil =>
    cases optC with
    | none => exact staticAgree_refl _ ctx
    | some c =>
      exfalso; rw [hmy] at hm; simp [mergeJpList, pure, Except.pure] at hm
  | cons c0 cs =>
    have hc0_in : c0 ∈ (jumpsK.filter (·.1 == j)).map Prod.snd := hmy ▸ List.mem_cons_self
    obtain ⟨jc0, hjc0, rfl⟩ := List.mem_map.mp hc0_in
    have hjc0_mem := (List.mem_filter.mp hjc0).1
    have hjc0_id : jc0.1 = j := beq_iff_eq.mp (List.mem_filter.mp hjc0).2
    have hK_agree : StaticAgree (baseCtxLiveIds baseCtx) ctx jc0.2 :=
      ihK env retTy (jInfo :: jps) ctx sm jumpsK j (baseCtxLiveIds baseCtx) [] ctx hs hjpsK
        hK ha2.2 hnomut_j
        (staticAgree_mono_ids (fun _ h => (List.mem_filter.mp h).1) (staticAgree_refl _ ctx))
        jc0 hjc0_mem hjc0_id
    obtain ⟨hmap0, hhead, hsp⟩ := hheadsp jc0.2 cs hmy
    have hw0 : CtxWeakens baseCtx jc0.2 := hwB jc0.2 hc0_in
    have hty_eq : ∀ id, (baseCtx.get? id).map (·.ty) = (jc0.2.get? id).map (·.ty) := by
      intro id
      cases hgB : baseCtx.get? id with
      | none =>
        cases hg0 : jc0.2.get? id with
        | none => rfl
        | some v0 =>
          exfalso
          have hid0 : id ∈ jc0.2.vars.map RcVar.id :=
            List.mem_map.mpr ⟨v0, (RcCtx.get?_mem hg0).1, (RcCtx.get?_mem hg0).2⟩
          have hidB : id ∈ baseCtx.vars.map RcVar.id := hmap0.symm ▸ hid0
          have his : (baseCtx.get? id).isSome = true :=
            (get?_isSome_iff_mem_map_id baseCtx id).mpr hidB
          rw [hgB] at his; cases his
      | some wb =>
        obtain ⟨v0, hv0m, hid0, hty0⟩ := hhead wb (RcCtx.get?_mem hgB).1
        have hg0 : jc0.2.get? id = some v0 :=
          ((RcCtx.get?_mem hgB).2.symm.trans hid0) ▸ (RcCtx.mem_get?_iff hw0.2.1).mpr hv0m
        simp [hg0, hty0]
    refine ⟨fun id hid hlB => ?_, fun p hp hp1 => ?_⟩
    · obtain ⟨hlC, htyC⟩ := hK_agree.1 id hid (ctxWeakens_isLive_back hw0 hlB)
      exact ⟨hlC, htyC.trans (hty_eq id).symm⟩
    · obtain ⟨hpC, htyC⟩ := hK_agree.2 p (hsp p hp) hp1
      exact ⟨hpC, htyC.trans (hty_eq p.2).symm⟩

private theorem agreeCode_jp_body_init {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {sm : List (Nat × Nat × List Bool)} {j : Nat} {ps : List LcParam}
    {body k : LcCode} {jumpsK : List (Nat × RcCtx)} {optC : Option RcCtx}
    {liveIds mutated : List Nat} {ctx0 : RcCtx}
    (ihK : AgreeCodeProp k)
    (hs : CtxStaticInv ctx) (hjps : JpsScopeIn jps ctx)
    (hK : checkCode env retTy ({ id := j, params := ps, scopeIds := ctx.vars.map (·.id) } :: jps)
      ctx k = Except.ok jumpsK)
    (hm : mergeJpList ((jumpsK.filter (·.1 == j)).map Prod.snd) = Except.ok optC)
    (hwf : perceusCodeWf env retTy jps ctx sm (LcCode.jp j ps body k) = true)
    (hagree : StaticAgree (liveIds.filter (fun id => !mutated.contains id)) ctx0 ctx) :
    let baseCtx := optC.getD ctx
    StaticAgree (liveIds.filter (fun id => !(ps.map (·.id) ++ mutated).contains id)) ctx0
      (baseCtx.bindParams ps) := by
  have hwf_orig := hwf
  rw [perceusCodeWf.eq_3] at hwf; dsimp only at hwf
  have ha1 := Bool.and_eq_true _ _ |>.mp hwf
  have ha2 := Bool.and_eq_true _ _ |>.mp ha1.1
  have ha3 := Bool.and_eq_true _ _ |>.mp ha2.1
  have ha4 := Bool.and_eq_true _ _ |>.mp ha3.1
  have ha5 := Bool.and_eq_true _ _ |>.mp ha4.1
  obtain ⟨hsB, _, _, _, _⟩ := jpBaseCtx_static_invs hs hjps hK hm hwf_orig
  have hbase_eq : jpBaseCtx env retTy jps ctx j ps k = optC.getD ctx :=
    jpBaseCtx_eq_of_check hK hm
  let baseCtx := optC.getD ctx
  have hfrB : ps.all (binderFreshOwned baseCtx ·.id) = true := by
    simpa [hbase_eq] using ha5.2
  have hagree_base := jpBaseCtx_static_agree_aux ihK hs hjps hK hm hwf_orig
  refine ⟨fun id hid hlBP => ?_, fun p hp hp1 => ?_⟩
  · have hf1 := List.mem_filter.mp hid
    have hnotP : ∀ q ∈ ps, q.id ≠ id := fun q hq heq => by
      have hm : id ∈ ps.map (·.id) ++ mutated :=
        List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨q, hq, heq⟩))
      have hc := List.contains_iff_mem.mpr hm
      have h2 := hf1.2
      rw [hc] at h2; cases h2
    have hnotM : id ∈ liveIds.filter (fun z => !mutated.contains z) := by
      refine List.mem_filter.mpr ⟨hf1.1, ?_⟩
      cases hc : mutated.contains id
      · rfl
      · exfalso
        have hm : id ∈ ps.map (·.id) ++ mutated :=
          List.mem_append.mpr (Or.inr (List.contains_iff_mem.mp hc))
        have hc' := List.contains_iff_mem.mpr hm
        have h2 := hf1.2
        rw [hc'] at h2; cases h2
    rw [bindParams_get?_of_not_mem hsB.1 ps hnotP] at hlBP
    have hlive_id : id ∈ baseCtxLiveIds baseCtx := by
      cases hgB : baseCtx.get? id with
      | none => rw [hgB] at hlBP; cases hlBP
      | some vb =>
        rw [hgB] at hlBP; dsimp only [Option.map] at hlBP
        exact List.mem_map.mpr ⟨vb, List.mem_filter.mpr ⟨(RcCtx.get?_mem hgB).1,
          Option.some.inj hlBP⟩, (RcCtx.get?_mem hgB).2⟩
    obtain ⟨hlC, htyC⟩ := hagree_base.1 id hlive_id hlBP
    obtain ⟨hl0, hty0⟩ := hagree.1 id hnotM hlC
    rw [bindParams_get?_of_not_mem hsB.1 ps hnotP]
    exact ⟨hl0, hty0.trans htyC⟩
  · have hpB : p ∈ baseCtx.sharedPreds := by rwa [bindParams_sharedPreds] at hp
    obtain ⟨vb, hgb, hvb_no⟩ := hsB.2.2.1 p hpB
    have hvb_live : vb.isLive = true := by simp [RcVar.isLive, hvb_no]
    have hbp_live : p.1 ∈ baseCtxLiveIds baseCtx :=
      List.mem_map.mpr ⟨vb, List.mem_filter.mpr ⟨(RcCtx.get?_mem hgb).1, hvb_live⟩,
        (RcCtx.get?_mem hgb).2⟩
    have hf1 := List.mem_filter.mp hp1
    have hnotM : p.1 ∈ liveIds.filter (fun z => !mutated.contains z) := by
      refine List.mem_filter.mpr ⟨hf1.1, ?_⟩
      cases hc : mutated.contains p.1
      · rfl
      · exfalso
        have hm : p.1 ∈ ps.map (·.id) ++ mutated :=
          List.mem_append.mpr (Or.inr (List.contains_iff_mem.mp hc))
        have hc' := List.contains_iff_mem.mpr hm
        have h2 := hf1.2
        rw [hc'] at h2; cases h2
    obtain ⟨hpC, htyC⟩ := hagree_base.2 p hpB hbp_live
    obtain ⟨hp0, hty0⟩ := hagree.2 p hpC hnotM
    have hnotP2 : ∀ q ∈ ps, q.id ≠ p.2 := fun q hq heq =>
      (binderFreshOwned_sharedPreds (List.all_eq_true.mp hfrB q hq) hpB).2 heq.symm
    rw [bindParams_get?_of_not_mem hsB.1 ps hnotP2]
    exact ⟨hp0, hty0.trans htyC⟩

private theorem agreeCode_jp {j : Nat} {ps : List LcParam} {body k : LcCode}
    (ihB : AgreeCodeProp body) (ihK : AgreeCodeProp k) :
    AgreeCodeProp (LcCode.jp j ps body k) := by
  intro env retTy jps ctx sm jumps targetJ liveIds mutated ctx0 hs hjps hchk hwf hnm hagree
    jc hjc hj
  have hwf_orig := hwf
  rw [checkCode.eq_2] at hchk
  rw [perceusCodeWf.eq_3] at hwf
  rw [jpLiveNoMut.eq_5] at hnm
  dsimp only at hchk hwf
  let jInfo : RcJpInfo := { id := j, params := ps, scopeIds := ctx.vars.map (·.id) }
  have ha1 := Bool.and_eq_true _ _ |>.mp hwf
  have ha2 := Bool.and_eq_true _ _ |>.mp ha1.1
  have ha3 := Bool.and_eq_true _ _ |>.mp ha2.1
  have ha4 := Bool.and_eq_true _ _ |>.mp ha3.1
  have ha5 := Bool.and_eq_true _ _ |>.mp ha4.1
  have ha6 := Bool.and_eq_true _ _ |>.mp ha5.1
  have hnm_pair := Bool.and_eq_true _ _ |>.mp hnm
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
  obtain ⟨jumpsK, hK, hrest1⟩ := except_bind_ok hchk
  obtain ⟨optC, hmerge, hrest2⟩ := except_bind_ok hrest1
  obtain ⟨hsB, _, hkeepB, _, _⟩ := jpBaseCtx_static_invs hs hjps hK hmerge hwf_orig
  have hbase_eq : jpBaseCtx env retTy jps ctx j ps k = optC.getD ctx :=
    jpBaseCtx_eq_of_check hK hmerge
  have hfrB : ps.all (binderFreshOwned (optC.getD ctx) ·.id) = true := by
    simpa [hbase_eq] using ha5.2
  have hwfB : perceusCodeWf env retTy jps ((optC.getD ctx).bindParams ps) [] body = true := by
    simpa [hbase_eq] using ha1.2
  obtain ⟨hsBP, hkeepBP⟩ := bindParams_static_invs hsB (decide_eq_true_iff.mp ha6.2) hfrB
  have hjpsB : JpsScopeIn jps ((optC.getD ctx).bindParams ps) :=
    jpsScopeIn_mono hjps fun id hid => hkeepBP id (hkeepB id hid)
  have hagreeB := agreeCode_jp_body_init ihK hs hjps hK hmerge hwf_orig hagree
  have hbody_eq : ∃ jumpsBody,
      checkCode env retTy jps ((optC.getD ctx).bindParams ps) body = Except.ok jumpsBody ∧
      jumps = jumpsK.filter (·.1 != j) ++ jumpsBody := by
    cases optC with
    | none =>
      simp only [bind, Except.bind, pure, Except.pure] at hrest2
      obtain ⟨jb, hjb, heq⟩ := except_bind_ok hrest2
      simp only [Except.ok.injEq] at heq
      exact ⟨jb, hjb, heq.symm⟩
    | some c =>
      simp only [bind, Except.bind, pure, Except.pure] at hrest2
      obtain ⟨jb, hjb, heq⟩ := except_bind_ok hrest2
      simp only [Except.ok.injEq] at heq
      exact ⟨jb, hjb, heq.symm⟩
  obtain ⟨jumpsBody, hB, rfl⟩ := hbody_eq
  rcases List.mem_append.mp hjc with hOut | hInB
  · exact ihK env retTy (jInfo :: jps) ctx sm jumpsK targetJ liveIds mutated ctx0
      hs hjpsK hK ha2.2 hnm_pair.2 hagree jc (List.mem_filter.mp hOut).1 hj
  · exact ihB env retTy jps ((optC.getD ctx).bindParams ps) [] jumpsBody targetJ liveIds
      (ps.map (·.id) ++ mutated) ctx0 hsBP hjpsB hB hwfB hnm_pair.1 hagreeB jc hInB hj

private theorem agreeCode_jmp {j : Nat} {as : List LcArg} :
    AgreeCodeProp (LcCode.jmp j as) := by
  intro env retTy jps ctx sm jumps targetJ liveIds mutated ctx0 hs _ hchk _ hnm hagree jc hjc hj
  rw [checkCode.eq_3] at hchk
  rw [jpLiveNoMut.eq_6] at hnm
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
    dsimp only at hj
    subst hj
    simp only [beq_self_eq_true, ↓reduceIte, Bool.not_eq_true'] at hnm
    have hmut_none : ∀ id ∈ liveIds, id ∈ liveIds.filter (fun z => !mutated.contains z) := by
      intro id hid
      refine List.mem_filter.mpr ⟨hid, ?_⟩
      cases hc : mutated.contains id
      · rfl
      · exfalso
        have hany : mutated.any liveIds.contains = true :=
          List.any_eq_true.mpr ⟨id, List.contains_iff_mem.mp hc, List.contains_iff_mem.mpr hid⟩
        rw [hany] at hnm; cases hnm
    have hagree' := staticAgree_mono_ids hmut_none hagree
    obtain ⟨_, hty1, hsp1⟩ := applyArgs_live_ty_back ha hs.1
    refine ⟨fun id hid hlR => ?_, fun p hp hp1 => ?_⟩
    · have hl1 : (ctx1.get? id).map RcVar.isLive = some true := by
        cases hinc : info.scopeIds.contains id with
        | true => rw [restrict_get?_eq] at hlR; simp only [hinc, ↓reduceIte] at hlR; exact hlR
        | false => rw [restrict_get?_eq] at hlR; rw [hinc] at hlR; cases hlR
      have htyR : (ctx1.get? id).map (·.ty) =
          ((ctx1.restrict info.scopeIds).get? id).map (·.ty) := by
        have hinc : info.scopeIds.contains id = true := by
          cases hc : info.scopeIds.contains id
          · rw [restrict_get?_eq] at hlR; rw [hc] at hlR; cases hlR
          · rfl
        rw [restrict_get?_eq]; simp only [hinc, ↓reduceIte]
      obtain ⟨hl0, hty0⟩ := hagree'.1 id hid ((hty1 id).2 hl1)
      exact ⟨hl0, hty0.trans ((hty1 id).1.symm.trans htyR)⟩
    · simp only [RcCtx.restrict, List.mem_filter] at hp
      have hp_mut := Bool.and_eq_true _ _ |>.mp hp.2
      obtain ⟨hp0, hty0⟩ := hagree'.2 p (hsp1 p hp.1) hp1
      have htyR : (ctx1.get? p.2).map (·.ty) =
          ((ctx1.restrict info.scopeIds).get? p.2).map (·.ty) := by
        rw [restrict_get?_eq]; simp only [hp_mut.2, ↓reduceIte]
      exact ⟨hp0, hty0.trans ((hty1 p.2).1.symm.trans htyR)⟩

private theorem agree_rec_all (code : LcCode) : AgreeCodeProp code := by
  refine @LcCode.rec AgreeCodeProp AgreeAltsProp (fun a => AgreeCodeProp a.2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ code
  · intro x ty v k ih
    intro env retTy jps ctx sm jumps targetJ liveIds mutated ctx0 hs hjps hchk hwf hnm hagree
      jc hjc hj
    obtain ⟨ctx', sm', hcv, hwfv, _, hk, hwfk⟩ := checkCode_let_unwrap hchk hwf
    obtain ⟨hs', hkeep'⟩ := checkVal_static_invs hs hwfv hcv
    rw [jpLiveNoMut.eq_1] at hnm
    have hagree1 := staticAgree_mono_ids (filter_mut_cons_sub liveIds mutated x) hagree
    have hne_mut : ∀ id ∈ liveIds.filter (fun z => !(x :: mutated).contains z), id ≠ x := by
      intro id hid heq
      have h2 := (List.mem_filter.mp hid).2
      subst heq
      simp at h2
    have hagree' := staticAgree_bind_step hne_mut hagree1 (checkVal_step_agree hs.1 hcv hwfv)
    exact ih env retTy jps ctx' sm' jumps targetJ liveIds (x :: mutated) ctx0
      hs' (jpsScopeIn_mono hjps hkeep') hk hwfk hnm hagree' jc hjc hj
  · intro j ps body k ihB ihK; exact agreeCode_jp ihB ihK
  · intro j as; exact agreeCode_jmp
  · intro x alts ihA
    intro env retTy jps ctx sm jumps targetJ liveIds mutated ctx0 hs hjps hchk hwf hnm hagree
      jc hjc hj
    rw [checkCode.eq_4] at hchk; rw [perceusCodeWf.eq_5] at hwf; rw [jpLiveNoMut.eq_7] at hnm
    obtain ⟨u, hchkL, hA⟩ := except_bind_ok hchk; cases u
    cases hg : ctx.get? x with
    | none => rw [hg] at hwf; simp at hwf
    | some vx =>
      rw [hg] at hwf
      exact ihA env retTy jps ctx sm x vx.ty _ jumps targetJ liveIds mutated ctx0
        hs hjps hchkL hA hwf hnm hagree jc hjc hj
  · intro a env retTy jps ctx sm jumps _ _ _ _ _ _ hchk _ _ _ jc hjc _
    rw [checkCode.eq_5] at hchk; dsimp only at hchk
    by_cases hrc : retTy.needsRc = true
    · simp only [hrc, ↓reduceIte] at hchk
      obtain ⟨_, _, h1⟩ := except_bind_ok hchk
      obtain ⟨_, _, hj⟩ := except_bind_ok h1
      simp only [pure, Except.pure, Except.ok.injEq] at hj; subst hj; cases hjc
    · simp only [hrc, Bool.false_eq_true, ↓reduceIte] at hchk
      obtain ⟨_, _, h1⟩ := except_bind_ok hchk
      obtain ⟨_, _, h2⟩ := except_bind_ok h1
      obtain ⟨_, _, hj⟩ := except_bind_ok h2
      simp only [pure, Except.pure, Except.ok.injEq] at hj; subst hj; cases hjc
  · intro env retTy jps ctx sm jumps _ _ _ _ _ _ hchk _ _ _ jc hjc _
    rw [checkCode.eq_6] at hchk; simp only [pure, Except.pure, Except.ok.injEq] at hchk
    subst hchk; cases hjc
  · intro x i y k ih
    intro env retTy jps ctx sm jumps targetJ liveIds mutated ctx0 hs hjps hchk hwf hnm hagree
      jc hjc hj
    obtain ⟨ctx1, _, hca, hk, hwfk⟩ := checkCode_oset_unwrap hchk hwf
    rw [jpLiveNoMut.eq_10] at hnm
    have hcons : CtxStaticInv ctx1 ∧
        (∀ id, (ctx.get? id).isSome = true → (ctx1.get? id).isSome = true) ∧
        CtxLiveTyBack ctx ctx1 := by
      cases y with
      | erased =>
        simp [RcCtx.consumeArg, pure, Except.pure] at hca; cases hca
        exact ⟨hs, (fun _ h => h), (fun hnd => ⟨hnd, (fun _ => ⟨rfl, id⟩), (fun _ hp => hp)⟩)⟩
      | var yid =>
        exact ⟨ctxStaticInv_consumeVar hs hca,
          fun id hid => get?_isSome_consumeVar hca id hid, consumeVar_live_ty_back hca⟩
    obtain ⟨_, hty1, hsp1⟩ := hcons.2.2 hs.1
    have hagree1 := staticAgree_mono_ids (filter_mut_cons_sub liveIds mutated x) hagree
    have hagree' :
        StaticAgree (liveIds.filter (fun z => !(x :: mutated).contains z)) ctx0 ctx1 :=
      ⟨fun id hid hl =>
        let ⟨hl0, hty0⟩ := hagree1.1 id hid ((hty1 id).2 hl)
        ⟨hl0, hty0.trans (hty1 id).1.symm⟩,
      fun p hp hp1 =>
        let ⟨hp0, hty0⟩ := hagree1.2 p (hsp1 p hp) hp1
        ⟨hp0, hty0.trans (hty1 p.2).1.symm⟩⟩
    exact ih env retTy jps ctx1 sm jumps targetJ liveIds (x :: mutated) ctx0
      hcons.1 (jpsScopeIn_mono hjps hcons.2.1) hk hwfk hnm hagree' jc hjc hj
  · intro x i y k ih
    intro env retTy jps ctx sm jumps targetJ liveIds mutated ctx0 hs hjps hchk hwf hnm hagree
      jc hjc hj
    rw [checkCode.eq_8] at hchk; rw [perceusCodeWf.eq_12] at hwf; rw [jpLiveNoMut.eq_11] at hnm
    obtain ⟨_, _, h1⟩ := except_bind_ok hchk
    obtain ⟨_, _, hk⟩ := except_bind_ok h1
    have hagree' := staticAgree_mono_ids (filter_mut_cons_sub liveIds mutated x) hagree
    exact ih env retTy jps ctx _ jumps targetJ liveIds (x :: mutated) ctx0
      hs hjps hk (Bool.and_eq_true _ _ |>.mp hwf).2 hnm hagree' jc hjc hj
  · intro x n off y ty k ih
    intro env retTy jps ctx sm jumps targetJ liveIds mutated ctx0 hs hjps hchk hwf hnm hagree
      jc hjc hj
    rw [checkCode.eq_9] at hchk; rw [perceusCodeWf.eq_13] at hwf; rw [jpLiveNoMut.eq_12] at hnm
    obtain ⟨_, _, h1⟩ := except_bind_ok hchk
    obtain ⟨_, _, hk⟩ := except_bind_ok h1
    have hagree' := staticAgree_mono_ids (filter_mut_cons_sub liveIds mutated x) hagree
    exact ih env retTy jps ctx _ jumps targetJ liveIds (x :: mutated) ctx0
      hs hjps hk (Bool.and_eq_true _ _ |>.mp hwf).2 hnm hagree' jc hjc hj
  · intro x cidx k ih
    intro env retTy jps ctx sm jumps targetJ liveIds mutated ctx0 hs hjps hchk hwf hnm hagree
      jc hjc hj
    rw [checkCode.eq_10] at hchk; rw [perceusCodeWf.eq_14] at hwf; rw [jpLiveNoMut.eq_13] at hnm
    obtain ⟨_, _, hk⟩ := except_bind_ok hchk
    have hagree' := staticAgree_mono_ids (filter_mut_cons_sub liveIds mutated x) hagree
    exact ih env retTy jps ctx sm jumps targetJ liveIds (x :: mutated) ctx0
      hs hjps hk (Bool.and_eq_true _ _ |>.mp hwf).2 hnm hagree' jc hjc hj
  · intro x n chk k ih
    intro env retTy jps ctx sm jumps targetJ liveIds mutated ctx0 hs hjps hchk hwf hnm hagree
      jc hjc hj
    obtain ⟨v, ctx1, hg, hvl, h1, hk, hwfk⟩ := checkCode_inc_unwrap hchk hwf
    rw [jpLiveNoMut.eq_2] at hnm
    rcases h1 with rfl | ⟨_, rfl⟩
    · exact ih env retTy jps ctx1 sm jumps targetJ liveIds mutated ctx0 hs hjps hk hwfk hnm
        hagree jc hjc hj
    · obtain ⟨hs1, hk1⟩ := ctxStaticInv_inc hs hg
      let v' : RcVar := {
        id := v.id, ty := v.ty, noRc := v.noRc, persistent := v.persistent,
        owned := v.owned + n, borrowed := v.borrowed, parent? := v.parent?,
        resetTok := v.resetTok }
      have hmap : ∀ z, ((ctx.put v').get? z).map (·.ty) = (ctx.get? z).map (·.ty) ∧
          (((ctx.put v').get? z).map RcVar.isLive = some true →
            (ctx.get? z).map RcVar.isLive = some true) :=
        fun z => put_same_ty_live hs.1 v' hg rfl rfl (fun _ => hvl) z
      have hagree' :
          StaticAgree (liveIds.filter (fun z => !mutated.contains z)) ctx0 (ctx.put v') :=
        ⟨fun id hid hl =>
          let ⟨hl0, hty0⟩ := hagree.1 id hid ((hmap id).2 hl)
          ⟨hl0, hty0.trans (hmap id).1.symm⟩,
        fun p hp hp1 =>
          let ⟨hp0, hty0⟩ := hagree.2 p hp hp1
          ⟨hp0, hty0.trans (hmap p.2).1.symm⟩⟩
      exact ih env retTy jps (ctx.put v') sm jumps targetJ liveIds mutated ctx0
        hs1 (jpsScopeIn_mono hjps hk1) hk hwfk hnm hagree' jc hjc hj
  · intro x n chk k ih
    intro env retTy jps ctx sm jumps targetJ liveIds mutated ctx0 hs hjps hchk hwf hnm hagree
      jc hjc hj
    obtain ⟨ctx1, hcons, hk, hwfk⟩ := checkCode_dec_unwrap hchk hwf
    rw [jpLiveNoMut.eq_3] at hnm
    have hs1 := ctxStaticInv_consumeVar hs hcons
    obtain ⟨_, hty1, hsp1⟩ := consumeVar_live_ty_back hcons hs.1
    have hagree' : StaticAgree (liveIds.filter (fun z => !mutated.contains z)) ctx0 ctx1 :=
      ⟨fun id hid hl =>
        let ⟨hl0, hty0⟩ := hagree.1 id hid ((hty1 id).2 hl)
        ⟨hl0, hty0.trans (hty1 id).1.symm⟩,
      fun p hp hp1 =>
        let ⟨hp0, hty0⟩ := hagree.2 p (hsp1 p hp) hp1
        ⟨hp0, hty0.trans (hty1 p.2).1.symm⟩⟩
    exact ih env retTy jps ctx1 sm jumps targetJ liveIds mutated ctx0
      hs1 (jpsScopeIn_mono hjps (fun id hid => get?_isSome_consumeVar hcons id hid))
      hk hwfk hnm hagree' jc hjc hj
  · intro x k ih
    intro env retTy jps ctx sm jumps targetJ liveIds mutated ctx0 hs hjps hchk hwf hnm hagree
      jc hjc hj
    obtain ⟨ctx1, _, hcons, hk, hwfk⟩ := checkCode_del_unwrap hchk hwf
    rw [jpLiveNoMut.eq_4] at hnm
    have hs1 := ctxStaticInv_consumeVar hs hcons
    obtain ⟨_, hty1, hsp1⟩ := consumeVar_live_ty_back hcons hs.1
    have hagree' : StaticAgree (liveIds.filter (fun z => !mutated.contains z)) ctx0 ctx1 :=
      ⟨fun id hid hl =>
        let ⟨hl0, hty0⟩ := hagree.1 id hid ((hty1 id).2 hl)
        ⟨hl0, hty0.trans (hty1 id).1.symm⟩,
      fun p hp hp1 =>
        let ⟨hp0, hty0⟩ := hagree.2 p (hsp1 p hp) hp1
        ⟨hp0, hty0.trans (hty1 p.2).1.symm⟩⟩
    exact ih env retTy jps ctx1 _ jumps targetJ liveIds mutated ctx0
      hs1 (jpsScopeIn_mono hjps (fun id hid => get?_isSome_consumeVar hcons id hid))
      hk hwfk hnm hagree' jc hjc hj
  · intro env retTy jps ctx sm scru scruTy tgt? jumps _ _ _ _ _ _ _ hchk _ _ _ jc hjc _
    rw [checkAlts.eq_1] at hchk; simp only [pure, Except.pure, Except.ok.injEq] at hchk
    subst hchk; cases hjc
  · intro hd tl ihB ihR
    intro env retTy jps ctx sm scru scruTy tgt? jumps targetJ liveIds mutated ctx0
      hs hjps hchkL hchk hwf hnm hagree jc hjc hj
    obtain ⟨j1, j2, ctxB, rfl, h1, h2, hwf1, hwf2, ⟨ctx1, hbr, hmsb⟩⟩ :=
      checkAlts_cons_unwrap hchk hwf
    rw [jpAltsLiveNoMut.eq_2] at hnm
    have hnm_pair := Bool.and_eq_true _ _ |>.mp hnm
    have h1s : CtxStaticInv ctx1 ∧
        (∀ id, (ctx.get? id).isSome = true → (ctx1.get? id).isSome = true) ∧
        StaticAgree (liveIds.filter (fun z => !mutated.contains z)) ctx0 ctx1 := by
      rcases hmsb with rfl | rfl
      · exact ⟨hs, (fun _ h => h), hagree⟩
      · obtain ⟨hs1, hk1⟩ := ctxStaticInv_markScalarBranch hs scru
        exact ⟨hs1, hk1, markScalarBranch_agree hs.1 scru hchkL hagree⟩
    have hBs : CtxStaticInv ctxB ∧
        (∀ id, (ctx.get? id).isSome = true → (ctxB.get? id).isSome = true) ∧
        StaticAgree (liveIds.filter (fun z => !mutated.contains z)) ctx0 ctxB := by
      rcases hbr with rfl | ⟨tgt, _, rfl⟩
      · exact h1s
      · obtain ⟨hs2, hk2⟩ := ctxStaticInv_markExcl h1s.1 tgt
        exact ⟨hs2, fun id hid => hk2 id (h1s.2.1 id hid), markExcl_agree h1s.1.1 tgt h1s.2.2⟩
    rcases List.mem_append.mp hjc with hmem1 | hmem2
    · exact ihB env retTy jps ctxB sm j1 targetJ liveIds mutated ctx0
        hBs.1 (jpsScopeIn_mono hjps hBs.2.1) h1 hwf1 hnm_pair.1 hBs.2.2 jc hmem1 hj
    · exact ihR env retTy jps ctx sm scru scruTy tgt? j2 targetJ liveIds mutated ctx0
        hs hjps hchkL h2 hwf2 hnm_pair.2 hagree jc hmem2 hj
  · intro _ c ih; exact ih

/-- Static type/liveness/sharedPreds agreement along `checkCode` when `jpLiveNoMut` holds. -/
public theorem checkCode_static_agree {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {sm : List (Nat × Nat × List Bool)} {code : LcCode}
    {jumps : List (Nat × RcCtx)} {targetJ : Nat} {liveIds mutated : List Nat} {ctx0 : RcCtx}
    (hs : CtxStaticInv ctx) (hjps : JpsScopeIn jps ctx)
    (hchk : checkCode env retTy jps ctx code = Except.ok jumps)
    (hwf : perceusCodeWf env retTy jps ctx sm code = true)
    (hnm : jpLiveNoMut targetJ liveIds mutated code = true)
    (hagree : StaticAgree (liveIds.filter (fun id => !mutated.contains id)) ctx0 ctx) :
    ∀ jc ∈ jumps, jc.1 = targetJ → StaticAgree liveIds ctx0 jc.2 :=
  agree_rec_all code env retTy jps ctx sm jumps targetJ liveIds mutated ctx0
    hs hjps hchk hwf hnm hagree

/-- Static agreement between `jp` entry `ctx` and its merged `baseCtx`. -/
public theorem jpBaseCtx_static_agree {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {sm : List (Nat × Nat × List Bool)} {j : Nat} {ps : List LcParam}
    {body k : LcCode} {jumpsK : List (Nat × RcCtx)} {optC : Option RcCtx}
    (hs : CtxStaticInv ctx) (hjps : JpsScopeIn jps ctx)
    (hK : checkCode env retTy ({ id := j, params := ps, scopeIds := ctx.vars.map (·.id) } :: jps)
      ctx k = Except.ok jumpsK)
    (hm : mergeJpList ((jumpsK.filter (·.1 == j)).map Prod.snd) = Except.ok optC)
    (hwf : perceusCodeWf env retTy jps ctx sm (LcCode.jp j ps body k) = true) :
    StaticAgree (baseCtxLiveIds (optC.getD ctx)) ctx (optC.getD ctx) :=
  jpBaseCtx_static_agree_aux (agree_rec_all k) hs hjps hK hm hwf

/-- Outer static agreement preserved when entering an inner `jp` body (`baseCtx.bindParams ps`). -/
public theorem inner_jp_body_agree {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {sm : List (Nat × Nat × List Bool)} {j : Nat} {ps : List LcParam}
    {body k : LcCode} {jumpsK : List (Nat × RcCtx)} {optC : Option RcCtx}
    {liveIds mutated : List Nat} {ctx0 : RcCtx}
    (hs : CtxStaticInv ctx) (hjps : JpsScopeIn jps ctx)
    (hK : checkCode env retTy ({ id := j, params := ps, scopeIds := ctx.vars.map (·.id) } :: jps)
      ctx k = Except.ok jumpsK)
    (hm : mergeJpList ((jumpsK.filter (·.1 == j)).map Prod.snd) = Except.ok optC)
    (hwf : perceusCodeWf env retTy jps ctx sm (LcCode.jp j ps body k) = true)
    (hagree : StaticAgree (liveIds.filter (fun id => !mutated.contains id)) ctx0 ctx) :
    StaticAgree (liveIds.filter (fun id => !(ps.map (·.id) ++ mutated).contains id)) ctx0
      ((optC.getD ctx).bindParams ps) :=
  agreeCode_jp_body_init (agree_rec_all k) hs hjps hK hm hwf hagree

end StaticAgreeLemmas

end LeanQbe.T.LeanLCNF.Sem
