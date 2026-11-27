module

public import LeanQbe.T.LeanLCNF.Sem.PerceusMut
public import LeanQbe.T.LeanLCNF.Sem.PerceusPrims1
import LeanQbe.T.Logic.ProofKit

/-!
# LCNF Perceus-Sound Simulation: `dec` Step

Non-cold reference-counting invariant preservation and stepwise simulation lemma for
`LcCode.dec`, showing `safeNonColdDec` + `perceusCodeWf` keeps execution off `DecColdRel`
and maintains `RcInv`, `SharedBoolVars`, `SharedBoolPreds`, `ExclCtorHeap`, `ShadowOk`,
and `EntryPres`.
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

section DecStep

/-- Every `sharedPreds` entry `(b, tgt)` has `b` present in `ctx` with `noRc = true`. -/
@[expose] public def SharedBoolPreds (ctx : RcCtx) : Prop :=
  ∀ p ∈ ctx.sharedPreds, ∃ vb, ctx.get? p.1 = some vb ∧ vb.noRc = true

public theorem sharedBoolPreds_vars {ctx : RcCtx} (h : SharedBoolPreds ctx) :
    SharedBoolVars ctx := by
  intro p hp vb hgb
  obtain ⟨vb0, hgb0, hno0⟩ := h p hp
  rw [hgb0] at hgb; cases hgb; exact hno0

public theorem sharedBoolPreds_init (ps : List LcParam) :
    SharedBoolPreds (({ vars := [], sharedPreds := [] } : RcCtx).bindParams ps) := by
  have hsp : ∀ ctx : RcCtx, ctx.sharedPreds = [] →
      (ctx.bindParams ps).sharedPreds = [] := by
    intro ctx hc
    induction ps generalizing ctx with
    | nil => exact hc
    | cons p ps ih =>
      simp only [RcCtx.bindParams, List.foldl_cons]
      refine ih _ ?_
      cases p.borrow <;> simp [RcCtx.bindBorrowed, RcCtx.bindOwned, RcCtx.put, hc]
  intro p hp
  rw [hsp _ rfl] at hp; cases hp

public theorem sharedBoolPreds_consumeVar {ctx ctx1 : RcCtx} {x n : Nat}
    (hnd : (ctx.vars.map RcVar.id).Nodup) (hsbp : SharedBoolPreds ctx)
    (hcons : ctx.consumeVar x n = .ok ctx1) : SharedBoolPreds ctx1 := by
  intro p hp
  have hp0 := consumeVar_sharedPreds_sub hcons p hp
  obtain ⟨vb, hgb, hno⟩ := hsbp p hp0
  have hflg := consumeVar_preserves_flags hnd hcons p.1
  cases hg1 : ctx1.get? p.1 with
  | none => rw [hgb, hg1] at hflg; cases hflg
  | some vb1 =>
    rw [hgb, hg1] at hflg
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hflg
    exact ⟨vb1, rfl, hflg.1.trans hno⟩

public theorem sharedBoolPreds_consumeArg {ctx ctx1 : RcCtx} {y : LcArg}
    (hnd : (ctx.vars.map RcVar.id).Nodup) (hsbp : SharedBoolPreds ctx)
    (hcons : ctx.consumeArg y = .ok ctx1) : SharedBoolPreds ctx1 := by
  cases y with
  | erased => simp [RcCtx.consumeArg, pure, Except.pure] at hcons; subst hcons; exact hsbp
  | var yid => exact sharedBoolPreds_consumeVar hnd hsbp hcons

public theorem sharedBoolPreds_put_fresh {ctx : RcCtx}
    (hnd : (ctx.vars.map RcVar.id).Nodup) (hsbp : SharedBoolPreds ctx)
    {v : RcVar} (hsp_ne : ∀ p ∈ ctx.sharedPreds, p.1 ≠ v.id) :
    SharedBoolPreds (ctx.put v) := by
  intro p hp
  have hp0 : p ∈ ctx.sharedPreds := by simpa [RcCtx.put] using hp
  obtain ⟨vb, hgb, hno⟩ := hsbp p hp0
  refine ⟨vb, ?_, hno⟩
  rw [RcCtx.put_get? hnd, beq_false_of_ne (hsp_ne p hp0)]
  exact hgb

/-- Any `isTaggedPVal` non-scalar `ValRep` evaluates to an odd `BitVec 64` word. -/
public theorem isTaggedPVal_odd {ty : LcTy} {pv : PVal} {bv : BitVec 64} {objs : List LcnfObj}
    (hns : ¬ty.isScalar = true) (htag : isTaggedPVal pv = true)
    (hrep : ValRep ty pv (.i64 bv) objs) : bv &&& 1#64 ≠ 0#64 := by
  simp only [ValRep, hns] at hrep
  obtain ⟨bv0, hw, hobj, _⟩ := hrep
  cases hw
  cases pv with
  | erased =>
    dsimp only [ObjRep] at hobj; rw [hobj]; decide
  | bits w v =>
    have hwlt : w < 64 := by simpa [isTaggedPVal] using htag
    dsimp only [ObjRep] at hobj
    rcases hobj with ⟨_, hbv⟩ | ⟨hw64, _⟩
    · rw [hbv]
      intro h0
      have hbit := congrArg (·.getLsbD 0) h0
      simp at hbit
    · omega
  | nat n =>
    have hnlt : n < 2 ^ 63 := by simpa [isTaggedPVal] using htag
    dsimp only [ObjRep] at hobj
    rw [(natRep_small hnlt).mp hobj]
    intro h0
    have := boxNat_and1_eq_one n
    rw [h0] at this; cases this
  | ctor cidx fs sc =>
    have hc : fs = [] ∧ sc = [] ∧ cidx < 2 ^ 63 := by
      cases fs <;> cases sc <;> simp [isTaggedPVal] at htag
      exact ⟨rfl, rfl, htag⟩
    obtain ⟨rfl, rfl, hclt⟩ := hc
    dsimp only [ObjRep] at hobj
    rcases hobj with ⟨_, _, _, hbv⟩ | ⟨hne, _⟩
    · rw [hbv]
      intro h0
      have := boxNat_and1_eq_one cidx
      rw [h0] at this; cases this
    · exact absurd ⟨rfl, rfl⟩ hne
  | str _ | arr _ | barr _ | int _ | clo _ _ _ => simp [isTaggedPVal] at htag

/-- `ShadowOk` agrees on `PVal.tag?` for every live variable in `ctx`. -/
public theorem shadow_tag?_eq {sm : List (Nat × Nat × List Bool)} {ctx : RcCtx}
    {ρP envP : PValEnv} (hshd : ShadowOk sm ctx ρP envP)
    {v : RcVar} (hv : v ∈ ctx.vars) (hlive : v.isLive = true) :
    (ρP v.id).bind PVal.tag? = (envP v.id).bind PVal.tag? := by
  have hs := hshd v hv hlive
  cases hi : isVarScalarInit sm v.id
  · simp only [hi, Bool.false_eq_true, ↓reduceIte] at hs
    obtain ⟨_, _, _, cidx, fs, pscal, hscal, hρ, hE, _⟩ := hs
    rw [hρ, hE]; rfl
  · simp only [hi, ite_true] at hs
    rw [hs]

/-- `ShadowOk` preserves `isTaggedPVal` between `ρP` and `envP`. -/
public theorem shadow_isTaggedPVal {sm : List (Nat × Nat × List Bool)} {ctx : RcCtx}
    {ρP envP : PValEnv} (hshd : ShadowOk sm ctx ρP envP)
    {v : RcVar} (hv : v ∈ ctx.vars) (hlive : v.isLive = true)
    {pv : PVal} (hρ : ρP v.id = some pv) (htag : isTaggedPVal pv = true) :
    ∃ pv', envP v.id = some pv' ∧ isTaggedPVal pv' = true := by
  have hs := hshd v hv hlive
  cases hi : isVarScalarInit sm v.id
  · simp only [hi, Bool.false_eq_true, ↓reduceIte] at hs
    obtain ⟨_, _, _, cidx, fs, pscal, hscal, hρ0, hE0, hpl, hhl, _⟩ := hs
    rw [hρ] at hρ0; cases hρ0
    have hfp : fs = [] ∧ pscal = [] := by
      cases fs <;> cases pscal <;> simp_all [isTaggedPVal]
    obtain ⟨rfl, rfl⟩ := hfp
    have hhs0 : hscal = [] := List.length_eq_zero_iff.mp (by simp at hpl; omega)
    subst hhs0
    exact ⟨.ctor cidx [] [], hE0, htag⟩
  · simp only [hi, ite_true] at hs
    exact ⟨pv, hs.symm.trans hρ, htag⟩

private theorem tobject_of_ne_even_dec {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) {x : Nat} {v : RcVar} (hget : rf.ctx.get? x = some v)
    (hlive : v.isLive = true) (hneeds : v.ty.needsRc = true) {bv : BitVec 64}
    (henvh : rf.envH x = some (v.ty, .i64 bv)) (hodd : bv &&& 1#64 ≠ 0#64) :
    v.ty = .tobject := by
  have ⟨hvm, hxid⟩ := RcCtx.get?_mem hget
  have hnonsc : ¬v.ty.isScalar = true := by
    cases hty : v.ty <;> simp_all [LcTy.needsRc, LcTy.isScalar]
  have ⟨_, wu, _, hwu, hrep, _⟩ := hinv.2.2.2.1 v hvm hlive
  rw [← hxid, hwu] at henvh; cases henvh
  simp only [ValRep, hnonsc] at hrep
  obtain ⟨bvp, hwp, _, hobj_even, _⟩ := hrep
  cases hwp
  cases hty : v.ty with
  | object => exact absurd (hobj_even hty) hodd
  | tobject => rfl
  | tagged | erased | void | uint8 | uint16 | uint32 | uint64 | usize | float =>
    rw [hty] at hneeds; cases hneeds

private theorem consumeVar_vars_eq_of_vars_eq {ctxA ctxB ctxA' : RcCtx} {x n : Nat}
    (hvars : ctxA.vars = ctxB.vars) (hcons : ctxA.consumeVar x n = .ok ctxA') :
    ∃ ctxB', ctxB.consumeVar x n = .ok ctxB' ∧ ctxB'.vars = ctxA'.vars := by
  have hget : ctxB.get? x = ctxA.get? x := by simp [RcCtx.get?, hvars]
  unfold RcCtx.consumeVar at hcons ⊢
  rw [hget]
  cases hga : ctxA.get? x with
  | none => simp [hga] at hcons
  | some v =>
    rw [hga] at hcons; dsimp only at hcons ⊢
    cases h1 : (v.noRc || v.persistent)
    · cases h2 : (n == 0)
      · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at hcons ⊢
        by_cases hlt : v.owned < n
        · simp [hlt] at hcons
        · simp only [hlt, ↓reduceIte] at hcons ⊢
          have hput_vars : ∀ w : RcVar, (ctxB.put w).vars = (ctxA.put w).vars :=
            fun w => by simp [RcCtx.put, hvars]
          cases hiz : ((v.owned - n == 0) && !v.borrowed)
          · simp only [hiz, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
              Except.ok.injEq] at hcons ⊢
            subst hcons
            exact ⟨_, rfl, hput_vars _⟩
          · simp only [hiz, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hcons ⊢
            subst hcons
            refine ⟨_, rfl, ?_⟩
            simp [RcCtx.invalidateChildren, hput_vars _]
      · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
          Except.ok.injEq] at hcons ⊢
        subst hcons; exact ⟨ctxB, rfl, hvars.symm⟩
    · simp only [h1, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hcons ⊢
      subst hcons; exact ⟨ctxB, rfl, hvars.symm⟩

private theorem rcInv_consumeVar_no_sp {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    {x n : Nat} {ctx1 : RcCtx} (hcons : rf.ctx.consumeVar x n = .ok ctx1) :
    let rf1 : RcFrame := { rf with ctx := ctx1 }
    (localHandles rf.ctx rf.envH).Perm (localHandles ctx1 rf.envH ++ consumeVarHandles rf x n) ∧
    (∀ s ≠ x, (localHandlesExcept rf.ctx rf.envH s).Perm
      (localHandlesExcept ctx1 rf.envH s ++ consumeVarHandles rf x n)) ∧
    HeapClean rt σ ∧ (ctx1.vars.map RcVar.id).Nodup ∧
    HandlesRcSound (frameHandles rf1) σ.objs ∧ (∀ v ∈ ctx1.vars, VarInv v rf1 σ.objs) ∧
    CleanVars ctx1 ∧ ParentsOwned ctx1 ∧
    (∀ v, rf.ctx.get? x = some v → ∀ vx', ctx1.get? x = some vx' →
      vx'.owned = (if v.noRc || v.persistent || n == 0 then v.owned else v.owned - n)) := by
  let ctx0 : RcCtx := { vars := rf.ctx.vars, sharedPreds := [] }
  let rf0 : RcFrame := { rf with ctx := ctx0 }
  obtain ⟨ctx0', hcons0, hveq⟩ :=
    consumeVar_vars_eq_of_vars_eq (ctxA := rf.ctx) (ctxB := ctx0) (ctxA' := ctx1) rfl hcons
  have hinv0 : RcInv rt rf0 σ :=
    ⟨hinv.1, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, fun _ hp => by cases hp⟩
  have hstep := rcInv_consumeVar_step hinv0 hclean hpo hcons0 (fun _ hp => by cases hp)
  obtain ⟨hpl, hpex, hinv0', hclean', hpo', hown⟩ := hstep
  have hlh_eq : localHandles ctx1 rf.envH = localHandles ctx0' rf.envH := by
    simp [localHandles, hveq]
  have hlhex_eq : ∀ s, localHandlesExcept ctx1 rf.envH s = localHandlesExcept ctx0' rf.envH s :=
    fun s => by simp [localHandlesExcept, hveq]
  have hcv_eq : consumeVarHandles rf x n = consumeVarHandles rf0 x n := by
    simp [consumeVarHandles, rf0, RcCtx.get?, ctx0]
  have hget0' : ∀ z, ctx1.get? z = ctx0'.get? z := fun z => by simp [RcCtx.get?, hveq]
  have hclean1 : CleanVars ctx1 := fun u hu => hclean' u (hveq ▸ hu)
  have hpo1 : ParentsOwned ctx1 := fun u hu p hpu => by
    obtain ⟨pv, hpvm, hpvid, hp1, hp2, hp3, hp4⟩ := hpo' u (hveq ▸ hu) p hpu
    exact ⟨pv, hveq ▸ hpvm, hpvid, hp1, hp2, hp3, hp4⟩
  have hsound1 : HandlesRcSound (frameHandles { rf with ctx := ctx1 }) σ.objs := by
    simpa [frameHandles, hlh_eq] using hinv0'.2.2.1
  have hvars1 : ∀ v ∈ ctx1.vars, VarInv v { rf with ctx := ctx1 } σ.objs := by
    intro v hv hvl
    simpa [frameHandles, hlh_eq, hveq] using hinv0'.2.2.2.1 v (hveq ▸ hv) hvl
  refine ⟨?_, ?_, hinv0'.1, ?_, hsound1, hvars1, hclean1, hpo1, ?_⟩
  · have h1 : localHandles ctx1 rf.envH = (List.map (varHandles rf.envH) ctx0'.vars).flatten := by
      simp [localHandles, hveq]
    rw [h1, hcv_eq]
    exact hpl
  · intro s hs
    have h1 : localHandlesExcept ctx1 rf.envH s =
        (List.map (varHandles rf.envH) (ctx0'.vars.filter fun v => v.id != s)).flatten := by
      simp [localHandlesExcept, hveq]
    rw [h1, hcv_eq]
    exact hpex s hs
  · simpa [hveq] using hinv0'.2.1
  · intro v hgx vx' hgx'
    exact hown v hgx vx' (hget0' x ▸ hgx')

private theorem HDecN_skip {bv : BitVec 64} {ty : LcTy} {chk : Bool} {K : HState → Prop}
    {σ : HState} (hnodup : (σ.objs.map LcnfObj.addr).Nodup) (hwf : ∀ o ∈ σ.objs, o.Wf)
    (hcond : ¬ty.needsRc = true ∨ (bv &&& 1#64 ≠ 0#64 ∧ chk = true ∧ ty = .tobject) ∨
      (bv &&& 1#64 = 0#64 ∧ ∃ o ∈ σ.objs, o.addr = bv ∧ o.rc = 0#32)) :
    ∀ n : Nat, K σ → HDecN bv ty chk n K σ := by
  intro n hK
  induction n with
  | zero => exact hK
  | succ k ih =>
    rcases hcond with hnr | ⟨hodd, rfl, rfl⟩ | ⟨hev, o, ho, hoa, horc0⟩
    · have hnr' : (!ty.needsRc) = true := by simp [hnr]
      refine ⟨by simp [HDec1Pre, hnr'], fun σ' hrel => ?_⟩
      simp only [HDec1Rel, hnr', ite_true] at hrel; rw [hrel]; exact ih
    · refine ⟨by simp [HDec1Pre, hodd], fun σ' hrel => ?_⟩
      simp only [HDec1Rel, LcTy.needsRc, Bool.not_true, Bool.false_eq_true, ite_false] at hrel
      split at hrel <;> simp_all
    · by_cases hnr : ty.needsRc = true
      · refine ⟨?_, fun σ' hrel => ?_⟩
        · simp only [HDec1Pre, hnr, Bool.not_true, Bool.false_eq_true, ite_false, hev, ne_eq,
            not_true_eq_false]
          exact ⟨o, ho, hoa, hwf o ho, fun h1 => by rw [horc0] at h1; cases h1⟩
        · simp only [HDec1Rel, hnr, Bool.not_true, Bool.false_eq_true, ite_false, hev, ne_eq,
            not_true_eq_false] at hrel
          rcases hrel with ⟨_, _, _, _, rfl⟩ | ⟨idx, hidx, haddr, hgt, _⟩ | hcold
          · exact ih
          · exfalso
            have hoe := obj_eq_of_addr_nodup hnodup (List.getElem_mem hidx) ho
              (haddr.trans hoa.symm)
            rw [hoe, horc0] at hgt; simp at hgt
          · exfalso
            obtain ⟨obj, hobj, hobja, hobj1⟩ := hcold.2.2.2.2.1
            have hoe := obj_eq_of_addr_nodup hnodup hobj ho (hobja.trans hoa.symm)
            rw [hoe, horc0] at hobj1; cases hobj1
      · have hnr' : (!ty.needsRc) = true := by simp [hnr]
        refine ⟨by simp [HDec1Pre, hnr'], fun σ' hrel => ?_⟩
        simp only [HDec1Rel, hnr', ite_true] at hrel; rw [hrel]; exact ih

private theorem bv32_sub_step {rc : BitVec 32} (hbd : rc.toNat < 2 ^ 31 - 1)
    {k : Nat} (hk : k + 1 < rc.toNat) :
    (rc - 1#32) - BitVec.ofNat 32 k = rc - BitVec.ofNat 32 (k + 1) := by
  have h1_le : (1#32 : BitVec 32) ≤ rc := by rw [BitVec.le_def]; simp; omega
  have h1t : (rc - 1#32).toNat = rc.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le h1_le]; simp
  have hk_le : BitVec.ofNat 32 k ≤ rc - 1#32 := by
    rw [BitVec.le_def, h1t]; simp; omega
  have hk1_le : BitVec.ofNat 32 (k + 1) ≤ rc := by
    rw [BitVec.le_def]; simp; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le hk_le, BitVec.toNat_sub_of_le hk1_le, h1t]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 32)]
  omega

private theorem HDecN_nonCold_run {bv : BitVec 64} {ty : LcTy} {chk : Bool}
    (hne : ty.needsRc = true) (hev : bv &&& 1#64 = 0#64) {idx : Nat} {K : HState → Prop} :
    ∀ (k : Nat) (σ : HState),
      (σ.objs.map LcnfObj.addr).Nodup → ∀ (hidx : idx < σ.objs.length), σ.objs[idx].addr = bv →
      (∀ o ∈ σ.objs, o.Wf) →
      σ.objs[idx].rc.toNat < 2 ^ 31 - 1 → k < σ.objs[idx].rc.toNat →
      K { σ with
          objs := σ.objs.set idx
            (σ.objs[idx].withRc (σ.objs[idx].rc - BitVec.ofNat 32 k)) } →
      HDecN bv ty chk k K σ := by
  intro k
  induction k with
  | zero =>
    intro σ _ hidx _ _ _ _ hK
    have hrc0 : σ.objs[idx].withRc (σ.objs[idx].rc - BitVec.ofNat 32 0) = σ.objs[idx] := by
      cases ho : σ.objs[idx]; simp [LcnfObj.withRc]
    rw [hrc0, List.set_getElem_self] at hK
    exact hK
  | succ k ih =>
    intro σ hnodup hidx haddr hwf hbd hlt hK
    have hgt1 : 1 < σ.objs[idx].rc.toInt := by
      have h0 : 0 ≤ σ.objs[idx].rc.toInt := by
        rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
      have : σ.objs[idx].rc.toInt = ↑σ.objs[idx].rc.toNat := by
        rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
      omega
    have hne1 : σ.objs[idx].rc ≠ 1#32 := fun h => by
      rw [h] at hgt1; simp at hgt1
    refine ⟨?_, fun σ' hrel => ?_⟩
    · simp only [HDec1Pre, hne, Bool.not_true, Bool.false_eq_true, ite_false, hev, ne_eq,
        not_true_eq_false]
      exact ⟨σ.objs[idx], List.getElem_mem hidx, haddr, hwf _ (List.getElem_mem hidx),
        fun h => absurd h hne1⟩
    · simp only [HDec1Rel, hne, Bool.not_true, Bool.false_eq_true, ite_false, hev, ne_eq,
        not_true_eq_false] at hrel
      rcases hrel with ⟨o0, ho0, h0a, h0rc, _⟩ | ⟨j, hj, hja, _, rfl⟩ | hcold
      · exfalso
        have hoe := obj_eq_of_addr_nodup hnodup ho0 (List.getElem_mem hidx) (h0a.trans haddr.symm)
        rw [hoe] at h0rc; rw [h0rc] at hlt; simp at hlt
      · have hj_eq : j = idx := nodup_map_getElem_inj hnodup hj hidx (hja.trans haddr.symm)
        subst j
        have hidx' : idx < (σ.objs.set idx
            (σ.objs[idx].withRc (σ.objs[idx].rc - 1#32))).length := by
          simp only [List.length_set]; exact hidx
        have hnodup' : ((σ.objs.set idx
            (σ.objs[idx].withRc (σ.objs[idx].rc - 1#32))).map LcnfObj.addr).Nodup := by
          rw [list_map_addr_set_eq hidx
            (rfl : (σ.objs[idx].withRc (σ.objs[idx].rc - 1#32)).addr = σ.objs[idx].addr)]
          exact hnodup
        have hwf' : ∀ o ∈ σ.objs.set idx (σ.objs[idx].withRc (σ.objs[idx].rc - 1#32)), o.Wf := by
          intro o ho; rw [list_mem_set_iff hidx] at ho
          rcases ho with rfl | ⟨j, hj, _, rfl⟩
          · exact lcnfObj_wf_withRc (hwf _ (List.getElem_mem hidx)) (by
              have hle1 : (1#32 : BitVec 32) ≤ σ.objs[idx].rc := by
                rw [BitVec.le_def]; simp; omega
              rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_sub_of_le hle1]
              simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
              split <;> omega)
          · exact hwf _ (List.getElem_mem hj)
        have hrc_sub := rc_sub_nat_eq hbd hgt1
        have hsub_step := bv32_sub_step hbd hlt
        refine ih _ hnodup' hidx' (by simp [LcnfObj.withRc, haddr]) hwf' ?_ ?_ ?_
        · simp only [List.getElem_set_self, LcnfObj.withRc, hrc_sub]; omega
        · simp only [List.getElem_set_self, LcnfObj.withRc, hrc_sub]; omega
        · simpa [List.set_set, LcnfObj.withRc, hsub_step] using hK
      · exfalso
        obtain ⟨o1, ho1, h1a, h1rc⟩ := hcold.2.2.2.2.1
        have hoe := obj_eq_of_addr_nodup hnodup ho1 (List.getElem_mem hidx) (h1a.trans haddr.symm)
        rw [hoe] at h1rc; exact hne1 h1rc

private theorem dec_heap_sound_vars {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx)
    {x n : Nat} (hn : 0 < n) {v : RcVar} (hget : rf.ctx.get? x = some v)
    (hno : v.noRc = false) (hpers : v.persistent = false)
    {bv : BitVec 64} (henvh : rf.envH x = some (v.ty, .i64 bv)) (hev : bv &&& 1#64 = 0#64)
    {idx : Nat} (hidx : idx < σ.objs.length) (haddr : σ.objs[idx].addr = bv)
    (hnlt : n < σ.objs[idx].rc.toNat)
    {ctx1 : RcCtx} (hcons : rf.ctx.consumeVar x n = .ok ctx1)
    (hperm_lh : (localHandles rf.ctx rf.envH).Perm
      (localHandles ctx1 rf.envH ++ consumeVarHandles rf x n))
    (hclean1 : CleanVars ctx1) (hnd1 : (ctx1.vars.map RcVar.id).Nodup)
    (hpo1 : ParentsOwned ctx1)
    (hvars1 : ∀ u ∈ ctx1.vars, VarInv u { rf with ctx := ctx1 } σ.objs) :
    let rc' := σ.objs[idx].rc - BitVec.ofNat 32 n
    let σ' : HState := { σ with objs := σ.objs.set idx (σ.objs[idx].withRc rc') }
    let rf' : RcFrame := { rf with ctx := ctx1 }
    HeapClean rt σ' ∧ HandlesRcSound (frameHandles rf') σ'.objs ∧
    (∀ u ∈ ctx1.vars, VarInv u rf' σ'.objs) ∧
    (∀ q ∈ σ.objs, q.Wf → ∃ q' ∈ σ'.objs,
      ObjDataEq q q' ∧ (q.rc = 0#32 → q'.rc = 0#32) ∧
      (0 < q.rc.toInt → 0 < q'.rc.toInt) ∧ (q'.rc = 0#32 → q.rc = 0#32)) ∧
    (∀ a, nonPersistRefs σ'.objs a = nonPersistRefs σ.objs a) ∧
    (∀ a, (frameHandles rf').count a + (if a = bv then n else 0) = (frameHandles rf).count a) := by
  intro rc' σ' rf'
  have ⟨hheap, hnodup, hsound, _, _⟩ := hinv
  have hwf_all := hheap.1.2.1
  have hnodup_objs := hheap.2
  have hrc_all := hheap.1.2.2.2.2
  have hbd_idx := hrc_all _ (List.getElem_mem hidx)
  have hrc_pos : 0 < σ.objs[idx].rc.toInt := by
    have h0 := (hwf_all _ (List.getElem_mem hidx)).2.2.1
    have : σ.objs[idx].rc ≠ 0#32 := fun h => by rw [h] at hnlt; simp at hnlt
    exact rc_toInt_pos_of_ne_zero h0 this
  have hrc'_le : BitVec.ofNat 32 n ≤ σ.objs[idx].rc := by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 32)]
    omega
  have hrc'_nat : rc'.toNat = σ.objs[idx].rc.toNat - n := by
    rw [show rc' = σ.objs[idx].rc - BitVec.ofNat 32 n from rfl, BitVec.toNat_sub_of_le hrc'_le,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 32)]
  have hrc'_lt : rc'.toNat < 2 ^ 31 - 1 := by omega
  have hrc'_pos : 0 < rc'.toInt := by
    rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
  have hrc_flag : σ.objs[idx].rc = 0#32 ↔ rc' = 0#32 := by
    constructor
    · intro h; rw [h] at hnlt; simp at hnlt
    · intro h; rw [h] at hrc'_pos; simp at hrc'_pos
  have hnodup_objs' : (σ'.objs.map LcnfObj.addr).Nodup := by
    dsimp only [σ']
    rw [list_map_addr_set_eq hidx (rfl : (σ.objs[idx].withRc rc').addr = σ.objs[idx].addr)]
    exact hnodup_objs
  have hmap : ∀ q ∈ σ.objs, q.Wf → ∃ q' ∈ σ'.objs,
      ObjDataEq q q' ∧ (q.rc = 0#32 → q'.rc = 0#32) ∧
      (0 < q.rc.toInt → 0 < q'.rc.toInt) ∧ (q'.rc = 0#32 → q.rc = 0#32) := by
    intro q hq hqwf
    obtain ⟨j, hj, hget_j⟩ := obj_mem_idx hq
    by_cases hji : j = idx
    · subst hji
      have hdeq : ObjDataEq q (σ.objs[j].withRc rc') := by
        rw [hget_j]; exact objDataEq_withRc hqwf rc' (by omega)
      refine ⟨σ.objs[j].withRc rc', (list_mem_set_iff hidx).mpr (Or.inl rfl), hdeq,
        fun h => by rw [hget_j, h] at hnlt; simp at hnlt, fun _ => hrc'_pos,
        fun h => by simp [LcnfObj.withRc] at h; rw [h] at hrc'_pos; simp at hrc'_pos⟩
    · have hmem : q ∈ σ'.objs := (list_mem_set_iff hidx).mpr (Or.inr ⟨j, hj, hji, hget_j⟩)
      exact ⟨q, hmem, objDataEq_refl q hqwf, id, id, id⟩
  have hwf_all' : ∀ q ∈ σ'.objs, q.Wf := by
    intro q hq; dsimp only [σ'] at hq; rw [list_mem_set_iff hidx] at hq
    rcases hq with rfl | ⟨j, hj, _, rfl⟩
    · exact lcnfObj_wf_withRc (hwf_all _ (List.getElem_mem hidx)) (by omega)
    · exact hwf_all _ (List.getElem_mem hj)
  have hclosed' : lcnfHeapClosed σ'.objs := by
    intro q hq f hf hevf
    have ⟨q0, hq0, hdeq⟩ : ∃ q0 ∈ σ.objs, ObjDataEq q0 q := by
      dsimp only [σ'] at hq; rw [list_mem_set_iff hidx] at hq
      rcases hq with rfl | ⟨j, hj, _, rfl⟩
      · exact ⟨_, List.getElem_mem hidx,
          objDataEq_withRc (hwf_all _ (List.getElem_mem hidx)) rc' (by omega)⟩
      · exact ⟨_, List.getElem_mem hj, objDataEq_refl _ (hwf_all _ (List.getElem_mem hj))⟩
    have hcf : f ∈ q0.childFields := objDataEq_childFields hdeq ▸ hf
    obtain ⟨t, ht, hta⟩ := hheap.1.2.2.1 q0 hq0 f hcf hevf
    obtain ⟨t', ht', hdeq', _⟩ := hmap t ht (hwf_all t ht)
    exact ⟨t', ht', hdeq'.1.trans hta⟩
  have hrc_all' : ∀ q ∈ σ'.objs, q.rc.toNat < 2 ^ 31 - 1 := by
    intro q hq; dsimp only [σ'] at hq; rw [list_mem_set_iff hidx] at hq
    rcases hq with rfl | ⟨j, hj, _, rfl⟩
    · exact hrc'_lt
    · exact hrc_all _ (List.getElem_mem hj)
  have hheap' : HeapClean rt σ' :=
    ⟨⟨hheap.1.1, hwf_all', hclosed', by simpa [σ'] using hheap.1.2.2.2.1, hrc_all'⟩,
      hnodup_objs'⟩
  have hnpre : ∀ a, nonPersistRefs σ'.objs a = nonPersistRefs σ.objs a := fun a =>
    nonPersistRefs_set_withRc hidx hrc_flag a
  have hcons_h : consumeVarHandles rf x n = List.replicate n bv := by
    have hn0 : (n == 0) = false := beq_false_of_ne (by omega)
    have hbev : (bv &&& 1#64 == 0#64) = true := beq_iff_eq.mpr hev
    simp [consumeVarHandles, hget, hno, hpers, hn0, henvh, Word.i64, Word.toBV64?, hbev]
  have hcnt_f : ∀ a, (frameHandles rf').count a + (if a = bv then n else 0) =
      (frameHandles rf).count a := by
    intro a
    have hp := hperm_lh.count_eq a
    rw [List.count_append, hcons_h] at hp
    simp only [frameHandles, rf', List.count_append]
    by_cases hab : bv = a
    · subst hab
      simp only [List.count_replicate, beq_self_eq_true, ite_true] at hp ⊢
      omega
    · have hrc0 : (List.replicate n bv).count a = 0 := by
        rw [List.count_eq_zero]
        intro hm
        exact hab (List.eq_of_mem_replicate hm).symm
      rw [hrc0, Nat.add_zero] at hp
      simp only [Ne.symm hab, ite_false]
      omega
  have hsound' : HandlesRcSound (frameHandles rf') σ'.objs := by
    refine ⟨?_, ?_⟩
    · intro p hp hp0 f hf hevf
      dsimp only [σ'] at hp; rw [list_mem_set_iff hidx] at hp
      rcases hp with rfl | ⟨j, hj, _, rfl⟩
      · simp [LcnfObj.withRc] at hp0; rw [hp0] at hrc'_pos; simp at hrc'_pos
      · obtain ⟨q, hq, hqa, hq0⟩ := hsound.1 _ (List.getElem_mem hj) hp0 f hf hevf
        obtain ⟨q', hq', hdeq, h0, _⟩ := hmap q hq (hwf_all q hq)
        exact ⟨q', hq', hdeq.1.trans hqa, h0 hq0⟩
    · intro q hq hqpos
      dsimp only [σ'] at hq; rw [list_mem_set_iff hidx] at hq
      rcases hq with rfl | ⟨j, hj, _, rfl⟩
      · simp only [LcnfObj.withRc]
        have hb := hsound.2 _ (List.getElem_mem hidx) hrc_pos
        have hn_a := hnpre σ.objs[idx].addr
        have hc_a := hcnt_f bv
        rw [haddr] at hb hn_a ⊢
        simp only [ite_true] at hc_a
        omega
      · have hb := hsound.2 _ (List.getElem_mem hj) hqpos
        have hn_a := hnpre σ.objs[j].addr
        have hc_a := hcnt_f σ.objs[j].addr
        omega
  have hmap_rc : ∀ q ∈ σ.objs, q.Wf → ∃ q' ∈ σ'.objs,
      q'.addr = q.addr ∧ q'.childFields = q.childFields ∧
      (q.rc = 0#32 → q'.rc = 0#32) ∧ (0 < q.rc.toInt → q'.rc ≠ 0#32) := by
    intro q hq hqwf
    obtain ⟨q', hq', hdeq, h0, hpos, _⟩ := hmap q hq hqwf
    exact ⟨q', hq', hdeq.1, objDataEq_childFields hdeq, h0, fun hp h0' => by
      have := hpos hp; simp [h0'] at this⟩
  have howned' : ∀ pv ∈ ctx1.vars, pv.noRc = false → pv.persistent = false →
      pv.resetTok = false → 0 < pv.owned → ∃ ty w, rf'.envH pv.id = some (ty, w) := by
    intro pv hpvm _ _ _ hppos
    obtain ⟨_, wu, _, hwu, _⟩ := hvars1 pv hpvm (by simp [RcVar.isLive, hppos])
    exact ⟨pv.ty, wu, hwu⟩
  have hv_own_le : ¬v.owned < n := by
    intro hlt
    unfold RcCtx.consumeVar at hcons
    simp [hget, hno, hpers, beq_false_of_ne (by omega : n ≠ 0), hlt] at hcons
  have hvars' : ∀ u ∈ ctx1.vars, VarInv u rf' σ'.objs := by
    intro u hu hul
    obtain ⟨pu, wu, hp, hh, hrep, hnon⟩ := hvars1 u hu hul
    have hrep' : ValRep u.ty pu wu σ'.objs := by
      refine valRep_mono_pred (P := fun _ => True)
        (fun q hq hqwf _ => let ⟨q', hq', hdeq, _⟩ := hmap q hq hqwf; ⟨q', hq', hdeq⟩)
        (fun _ _ _ _ _ _ _ => trivial) hrep (fun _ _ _ _ => trivial)
    refine ⟨pu, wu, hp, hh, hrep', fun hns => ?_⟩
    obtain ⟨bvu, hwu, hno_u, hpers_u, hex_u, hbor_u⟩ := hnon hns
    refine ⟨bvu, hwu, hno_u, fun hp' hev' => ?_, fun hex' => ?_, fun hn0' hp0' hb0' hevu => ?_⟩
    · obtain ⟨q, hq, hqa, hq0⟩ := hpers_u hp' hev'
      obtain ⟨q', hq', hdeq, h0, _⟩ := hmap q hq (hwf_all q hq)
      exact ⟨q', hq', hdeq.1.trans hqa, h0 hq0⟩
    · obtain ⟨hx1, hx2, hx3, hxo⟩ := hex_u hex'
      refine ⟨hx1, hx2, hx3, fun hevu => ?_⟩
      obtain ⟨o_u, ho_u, ho_ua, ho_urc⟩ := hxo hevu
      have hu_ne : u.id ≠ x := by
        intro hux
        have hgu := rcCtx_get?_of_mem hnd1 hu
        obtain ⟨w0, hw0, _, _, _, _, _, _, hw0_ex⟩ :=
          consumeVar_get?_live_back hnodup hclean hcons u.id hgu hul
        have hweq : w0 = v := by have h := hw0; rw [hux, hget] at h; cases h; rfl
        have hw0_ex' := (hw0_ex hex').2 hux
        rcases hw0_ex' with h0 | hsum
        · omega
        · obtain ⟨_, _, _, _, _, hnon_w0⟩ := hinv.2.2.2.1 v (RcCtx.get?_mem hget).1
            (by simp [RcVar.isLive]; omega)
          have hns_v : ¬v.ty.isScalar = true := fun hs => by
            have := (hclean v (RcCtx.get?_mem hget).1).1.2 hs; rw [hno] at this; cases this
          obtain ⟨_, _, _, _, hex_v, _⟩ := hnon_w0 hns_v
          have hv_own1 := (hex_v (hweq ▸ (hw0_ex hex').1)).2.2.1
          rw [hweq, hv_own1] at hsum
          omega
      have hbne : bvu ≠ bv := by
        intro heqb
        have hrt_v := (hclean v (RcCtx.get?_mem hget).1).2.2.2.2
        have hbev : (bv &&& 1#64 == 0#64) = true := beq_iff_eq.mpr hev
        have hvh_v : (varHandles rf.envH v).count bv = v.owned := by
          simp [varHandles, hno, hpers, hrt_v, beq_false_of_ne (by omega : v.owned ≠ 0),
            (RcCtx.get?_mem hget).2 ▸ henvh, Word.i64, Word.toBV64?, hbev]
        have hgu := rcCtx_get?_of_mem hnd1 hu
        obtain ⟨w0, hw0, _, hw0_no, hw0_ps, _, hw0_le, _, _⟩ :=
          consumeVar_get?_live_back hnodup hclean hcons u.id hgu hul
        have hw0_id : w0.id = u.id := (RcCtx.get?_mem hw0).2
        have hw0_mem := (RcCtx.get?_mem hw0).1
        have hw0_rt := (hclean w0 hw0_mem).2.2.2.2
        have hw0_own_pos : 0 < w0.owned := by omega
        have henv_w0 : rf.envH w0.id = some (u.ty, .i64 bv) := by
          rw [hw0_id, hh, hwu, heqb]
        have hw0_vh : 1 ≤ (varHandles rf.envH w0).count bv := by
          have hnz : w0.owned ≠ 0 := by omega
          simp [varHandles, hw0_no, hx1, hw0_ps, hx2, hw0_rt, beq_false_of_ne hnz,
            henv_w0, Word.i64, Word.toBV64?, hbev]
          omega
        have hsub_w0 : (varHandles rf.envH w0).Sublist
            (localHandlesExcept rf.ctx rf.envH v.id) := by
          simp only [localHandlesExcept]
          exact List.sublist_flatten_of_mem (List.mem_map.mpr
            ⟨w0, List.mem_filter.mpr ⟨hw0_mem, bne_iff_ne.mpr
              (by rw [hw0_id, (RcCtx.get?_mem hget).2]; exact hu_ne)⟩, rfl⟩)
        have hlh := localHandles_count_eq_add hnodup rf.envH (RcCtx.get?_mem hget).1 bv
        have hs := hsound.2 o_u ho_u (by rw [ho_urc]; decide)
        rw [ho_urc] at hs
        simp only [frameHandles, List.count_append, ho_ua, heqb, BitVec.toNat_ofNat] at hs
        have hcle := hsub_w0.count_le bv
        rw [(RcCtx.get?_mem hget).2] at hlh hcle
        omega
      obtain ⟨j, hj, hget_j⟩ := obj_mem_idx ho_u
      have hjne : j ≠ idx := fun h => by
        subst h; exact hbne (ho_ua.symm.trans (hget_j.symm ▸ haddr))
      exact ⟨o_u, (list_mem_set_iff hidx).mpr (Or.inr ⟨j, hj, hjne, hget_j⟩), ho_ua, ho_urc⟩
    · obtain ⟨_, hbk2⟩ := hbor_u hn0' hp0' hb0' hevu
      have hbk2' : Backed σ'.objs ((match u.parent? with
          | none => []
          | some p => match rf'.envH p with
            | some (_, w) => match w.toBV64? with | some bp => [bp] | none => []
            | none => []) ++ (rf'.extH ++ rf'.ghostH)) bvu := by
        cases hpar : u.parent? with
        | none =>
          rw [hpar] at hbk2; dsimp only at hbk2 ⊢
          exact backed_mono_rc_pos hmap_rc hwf_all (fun _ hr => hr) hbk2
        | some p =>
          rw [hpar] at hbk2; dsimp only at hbk2 ⊢
          obtain ⟨pv, hpvm, hpvid, hp1, hp2, hp3, hp_bk⟩ := hbk2
          exact backed_mono_rc_pos hmap_rc hwf_all (fun _ hr => hr) hp_bk
      refine ⟨varInv_backed_parent hwf_all' howned' hclean1 hpo1 hu hbk2', ?_⟩
      cases hpar : u.parent? with
      | none =>
        rw [hpar] at hbk2; dsimp only at hbk2 ⊢
        exact backed_mono_rc_pos hmap_rc hwf_all (fun _ hr => hr) hbk2
      | some p =>
        rw [hpar] at hbk2; dsimp only at hbk2 ⊢
        obtain ⟨pv, hpvm, hpvid, hp1, hp2, hp3, hp_bk⟩ := hbk2
        exact ⟨pv, hpvm, hpvid, hp1, hp2, hp3,
          backed_mono_rc_pos hmap_rc hwf_all (fun _ hr => hr) hp_bk⟩
  exact ⟨hheap', hsound', hvars', hmap, hnpre, hcnt_f⟩

private theorem dec_sharedPredInv {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx)
    (hsth : SharedTargetsHeap rf) (hsbp : SharedBoolPreds rf.ctx)
    {x n : Nat} (hn : 0 < n) {v : RcVar} (hget : rf.ctx.get? x = some v)
    (hno : v.noRc = false) (hpers : v.persistent = false)
    {bv : BitVec 64} (henvh : rf.envH x = some (v.ty, .i64 bv)) (hev : bv &&& 1#64 = 0#64)
    {idx : Nat} (hidx : idx < σ.objs.length) (haddr : σ.objs[idx].addr = bv)
    (hnlt : n < σ.objs[idx].rc.toNat)
    {ctx1 : RcCtx} (hcons : rf.ctx.consumeVar x n = .ok ctx1)
    (hsh_dec : n < v.owned ∨ ∀ p ∈ rf.ctx.sharedPreds, ∀ vb vt,
      rf.ctx.get? p.1 = some vb → rf.ctx.get? p.2 = some vt →
      (!vb.isLive || vt.noRc || vt.persistent || vt.owned == 0 || p.2 == x || vt.excl) = true)
    (hclean1 : CleanVars ctx1) (hnd1 : (ctx1.vars.map RcVar.id).Nodup)
    (hperm_ex : ∀ s ≠ x, (localHandlesExcept rf.ctx rf.envH s).Perm
      (localHandlesExcept ctx1 rf.envH s ++ consumeVarHandles rf x n))
    (hown_x : ∀ v0, rf.ctx.get? x = some v0 → ∀ vx', ctx1.get? x = some vx' →
      vx'.owned = (if v0.noRc || v0.persistent || n == 0 then v0.owned else v0.owned - n)) :
    let rc' := σ.objs[idx].rc - BitVec.ofNat 32 n
    let σ' : HState := { σ with objs := σ.objs.set idx (σ.objs[idx].withRc rc') }
    (∀ a, nonPersistRefs σ'.objs a = nonPersistRefs σ.objs a) →
    (∀ a, (frameHandles { rf with ctx := ctx1 }).count a + (if a = bv then n else 0) =
      (frameHandles rf).count a) →
    (∀ q ∈ σ.objs, q.Wf → ∃ q' ∈ σ'.objs,
      ObjDataEq q q' ∧ (q.rc = 0#32 → q'.rc = 0#32) ∧
      (0 < q.rc.toInt → 0 < q'.rc.toInt) ∧ (q'.rc = 0#32 → q.rc = 0#32)) →
    SharedPredInv { rf with ctx := ctx1 } σ'.objs := by
  intro rc' σ' hnpre hcnt_f hmap p hp vb1 vs1 hgb1 hgs1 _ hsno hspers
  have ⟨hheap, hnodup, hsound, hvars, hsp⟩ := hinv
  have hwf_all := hheap.1.2.1
  have hnodup_objs := hheap.2
  have hnodup_objs' : (σ'.objs.map LcnfObj.addr).Nodup := by
    dsimp only [σ']
    rw [list_map_addr_set_eq hidx (rfl : (σ.objs[idx].withRc rc').addr = σ.objs[idx].addr)]
    exact hnodup_objs
  have hrc'_le : BitVec.ofNat 32 n ≤ σ.objs[idx].rc := by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 32)]
    omega
  have hrc'_nat : rc'.toNat = σ.objs[idx].rc.toNat - n := by
    rw [show rc' = σ.objs[idx].rc - BitVec.ofNat 32 n from rfl, BitVec.toNat_sub_of_le hrc'_le,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 32)]
  have hidx_len : idx < σ'.objs.length := by simp [σ', hidx]
  have hn0_b : (n == 0) = false := beq_false_of_ne (by omega)
  have hv_own_le : ¬v.owned < n := by
    intro hlt
    unfold RcCtx.consumeVar at hcons
    simp [hget, hno, hpers, hn0_b, hlt] at hcons
  have hp0 := consumeVar_sharedPreds_sub hcons p hp
  obtain ⟨vb0, hgb0, hvb0_no⟩ := hsbp p hp0
  have hvb0_live : vb0.isLive = true := by simp [RcVar.isLive, hvb0_no]
  have hflg_s := consumeVar_preserves_flags hnodup hcons p.2
  have ⟨vs0, hgs0, hvs0_no, hvs0_ps, hvs0_ty⟩ : ∃ vs0, rf.ctx.get? p.2 = some vs0 ∧
      vs0.noRc = false ∧ vs0.persistent = false ∧ vs0.ty = vs1.ty := by
    cases hg0 : rf.ctx.get? p.2 with
    | none => rw [hg0, hgs1] at hflg_s; cases hflg_s
    | some w0 =>
      rw [hg0, hgs1] at hflg_s
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hflg_s
      exact ⟨w0, rfl, hflg_s.1.symm.trans hsno, hflg_s.2.1.symm.trans hspers, hflg_s.2.2.symm⟩
  obtain ⟨bvs, henvs0, hevs⟩ := hsth p hp0 vs0 hgs0 hvs0_no
  have henvs : rf.envH p.2 = some (vs1.ty, .i64 bvs) := hvs0_ty ▸ henvs0
  have hcons_h : consumeVarHandles rf x n = List.replicate n bv := by
    have hbev : (bv &&& 1#64 == 0#64) = true := beq_iff_eq.mpr hev
    simp [consumeVarHandles, hget, hno, hpers, hn0_b, henvh, Word.i64, Word.toBV64?, hbev]
  have hrt_v := (hclean v (RcCtx.get?_mem hget).1).2.2.2.2
  have hbev : (bv &&& 1#64 == 0#64) = true := beq_iff_eq.mpr hev
  have hvh_v : (varHandles rf.envH v).count bv = v.owned := by
    simp [varHandles, hno, hpers, hrt_v, beq_false_of_ne (by omega : v.owned ≠ 0),
      (RcCtx.get?_mem hget).2 ▸ henvh, Word.i64, Word.toBV64?, hbev]
  refine ⟨fun htag => ⟨bvs, henvs, hevs, fun hspos => ?_⟩, fun htag hspos => ?_⟩
  · have hl_s1 : vs1.isLive = true := by simp [RcVar.isLive, hspos]
    obtain ⟨w0, hw0, hw0_l, _, _, _, hw0_le, _⟩ :=
      consumeVar_get?_live_back hnodup hclean hcons p.2 hgs1 hl_s1
    have hweq : w0 = vs0 := by have h := hw0.symm.trans hgs0; cases h; rfl
    subst w0
    obtain ⟨bvs', henvs', _, hrest⟩ :=
      (hsp p hp0 vb0 vs0 hgb0 hgs0 hvb0_live hvs0_no hvs0_ps).1 htag
    have hbeq : bvs' = bvs := by
      have := henvs'.symm.trans henvs0; cases this; rfl
    subst bvs'
    obtain ⟨hc0, o_s, ho_s, ho_sa, ho_src⟩ := hrest (by omega)
    by_cases hpx : p.2 = x
    · have hvs0_eq : vs0 = v := by have h := hgs0.symm.trans (hpx ▸ hget); cases h; rfl
      have hb_eq : bvs = bv := by
        have h1 := congrArg (Option.bind · (fun q => q.2.toBV64?))
          (henvs0.symm.trans (hpx ▸ henvh))
        simpa [Word.i64, Word.toBV64?] using h1
      have ho_seq : o_s = σ.objs[idx] :=
        obj_eq_of_addr_nodup hnodup_objs ho_s (List.getElem_mem hidx)
          (ho_sa.trans (hb_eq ▸ haddr.symm))
      subst o_s
      have hown1 : vs1.owned = v.owned - n := by
        have h1 := hown_x v hget vs1 (hpx ▸ hgs1)
        simp [hno, hpers, hn0_b] at h1; exact h1
      have hlh0 := localHandles_count_eq_add hnodup rf.envH (RcCtx.get?_mem hgs0).1 bvs
      have hlh1 := localHandles_count_eq_add hnd1 rf.envH (RcCtx.get?_mem hgs1).1 bvs
      have hrt_1 : vs1.resetTok = false := (hclean1 vs1 (RcCtx.get?_mem hgs1).1).2.2.2.2
      have hvs1_vh : (varHandles rf.envH vs1).count bvs = vs1.owned := by
        have : vs1.owned ≠ 0 := by omega
        have hevs_b : (bvs &&& 1#64 == 0#64) = true := beq_iff_eq.mpr hevs
        simp [varHandles, hsno, hspers, hrt_1, beq_false_of_ne this,
          (RcCtx.get?_mem hgs1).2 ▸ henvs, Word.i64, Word.toBV64?, hevs_b]
      have hvh_s0 : (varHandles rf.envH vs0).count bvs = vs0.owned := by
        rw [hvs0_eq, hb_eq]; exact hvh_v
      have hvs0_own : vs0.owned = v.owned := by rw [hvs0_eq]
      have hc_bvs := hcnt_f bvs
      have hif_eq : (if bvs = bv then n else 0) = n := ite_eq_left hb_eq
      simp only [frameHandles, List.count_append, hif_eq] at hc_bvs
      rw [(RcCtx.get?_mem hgs0).2, hvh_s0] at hlh0
      rw [(RcCtx.get?_mem hgs1).2, hvs1_vh] at hlh1
      simp only [List.count_append] at hc0 ⊢
      refine ⟨by rw [hnpre bvs]; omega, σ.objs[idx].withRc rc',
        (list_mem_set_iff hidx).mpr (Or.inl rfl), haddr.trans hb_eq.symm, ?_⟩
      simp [LcnfObj.withRc, hrc'_nat, ho_src, hvs0_eq, hown1]
    · have hne_bv : bvs ≠ bv := by
        intro heq
        have hv_filt : v ∈ rf.ctx.vars.filter (fun u => u.id != p.2) :=
          List.mem_filter.mpr ⟨(RcCtx.get?_mem hget).1,
            bne_iff_ne.mpr (by rw [(RcCtx.get?_mem hget).2]; exact Ne.symm hpx)⟩
        have hsub : (varHandles rf.envH v).Sublist (localHandlesExcept rf.ctx rf.envH p.2) := by
          simp only [localHandlesExcept]
          exact List.sublist_flatten_of_mem (List.mem_map.mpr ⟨v, hv_filt, rfl⟩)
        have hle := hsub.count_le bv
        rw [heq] at hc0
        simp only [List.count_append] at hc0
        omega
      have hpex := (hperm_ex p.2 hpx).count_eq bvs
      have hcr : (List.replicate n bv).count bvs = 0 := by
        rw [List.count_eq_zero]; intro hm
        exact hne_bv (List.eq_of_mem_replicate hm)
      rw [List.count_append, hcons_h, hcr, Nat.add_zero] at hpex
      have hlh0 := localHandles_count_eq_add hnodup rf.envH (RcCtx.get?_mem hgs0).1 bvs
      have hlh1 := localHandles_count_eq_add hnd1 rf.envH (RcCtx.get?_mem hgs1).1 bvs
      have hc_bvs := hcnt_f bvs
      simp only [frameHandles, List.count_append, ite_eq_right hne_bv] at hc_bvs
      have hrt0 := (hclean vs0 (RcCtx.get?_mem hgs0).1).2.2.2.2
      have hevs_b : (bvs &&& 1#64 == 0#64) = true := beq_iff_eq.mpr hevs
      have hvh0 : (varHandles rf.envH vs0).count bvs = vs0.owned := by
        have : vs0.owned ≠ 0 := by omega
        simp [varHandles, hvs0_no, hvs0_ps, hrt0, beq_false_of_ne this,
          (RcCtx.get?_mem hgs0).2 ▸ henvs0, Word.i64, Word.toBV64?, hevs_b]
      have hvh1 : (varHandles rf.envH vs1).count bvs = vs1.owned := by
        have hrt1 := (hclean1 vs1 (RcCtx.get?_mem hgs1).1).2.2.2.2
        have : vs1.owned ≠ 0 := by omega
        simp [varHandles, hsno, hspers, hrt1, beq_false_of_ne this,
          (RcCtx.get?_mem hgs1).2 ▸ henvs, Word.i64, Word.toBV64?, hevs_b]
      rw [(RcCtx.get?_mem hgs0).2, hvh0] at hlh0
      rw [(RcCtx.get?_mem hgs1).2, hvh1] at hlh1
      have hown_eq : vs1.owned = vs0.owned := by omega
      obtain ⟨j, hj, hget_j⟩ := obj_mem_idx ho_s
      have hjne : j ≠ idx := fun h => by
        subst h; exact hne_bv (ho_sa.symm.trans (hget_j.symm ▸ haddr))
      simp only [List.count_append] at hc0 ⊢
      refine ⟨by rw [hnpre bvs]; omega, o_s,
        (list_mem_set_iff hidx).mpr (Or.inr ⟨j, hj, hjne, hget_j⟩), ho_sa,
        ho_src.trans hown_eq.symm⟩
  · have hl_s1 : vs1.isLive = true := by simp [RcVar.isLive, hspos]
    obtain ⟨w0, hw0, hw0_l, _, _, _, hw0_le, _⟩ :=
      consumeVar_get?_live_back hnodup hclean hcons p.2 hgs1 hl_s1
    have hweq : w0 = vs0 := by have h := hw0.symm.trans hgs0; cases h; rfl
    subst w0
    obtain ⟨bvs', henvs', _, o_s, ho_s, ho_sa', horc⟩ :=
      (hsp p hp0 vb0 vs0 hgb0 hgs0 hvb0_live hvs0_no hvs0_ps).2 htag (by omega)
    have hbeq : bvs' = bvs := by
      have := henvs'.symm.trans henvs0; cases this; rfl
    have ho_sa : o_s.addr = bvs := ho_sa'.trans hbeq
    refine ⟨bvs, henvs, hevs, ?_⟩
    by_cases hpx : p.2 = x
    · have hvs0_eq : vs0 = v := by have h := hgs0.symm.trans (hpx ▸ hget); cases h; rfl
      have hb_eq : bvs = bv := by
        have h1 := congrArg (Option.bind · (fun q => q.2.toBV64?))
          (henvs0.symm.trans (hpx ▸ henvh))
        simpa [Word.i64, Word.toBV64?] using h1
      have ho_seq : o_s = σ.objs[idx] :=
        obj_eq_of_addr_nodup hnodup_objs ho_s (List.getElem_mem hidx)
          (ho_sa.trans (hb_eq ▸ haddr.symm))
      rw [ho_seq] at horc
      have hown1 : vs1.owned = v.owned - n := by
        have h1 := hown_x v hget vs1 (hpx ▸ hgs1)
        simp [hno, hpers, hn0_b] at h1; exact h1
      refine ⟨σ.objs[idx].withRc rc', (list_mem_set_iff hidx).mpr (Or.inl rfl),
        haddr.trans hb_eq.symm, ?_⟩
      rcases horc with h0 | hlt
      · exfalso; rw [h0] at hnlt; simp at hnlt
      · right; simp [LcnfObj.withRc, hrc'_nat]; rw [hvs0_eq] at hlt; omega
    · by_cases heqb : bvs = bv
      · have ho_seq : o_s = σ.objs[idx] :=
          obj_eq_of_addr_nodup hnodup_objs ho_s (List.getElem_mem hidx)
            (ho_sa.trans (heqb ▸ haddr.symm))
        rw [ho_seq] at horc
        rcases horc with h0 | hlt
        · exfalso; rw [h0] at hnlt; simp at hnlt
        · have hv_filt : v ∈ rf.ctx.vars.filter (fun u => u.id != p.2) :=
            List.mem_filter.mpr ⟨(RcCtx.get?_mem hget).1,
              bne_iff_ne.mpr (by rw [(RcCtx.get?_mem hget).2]; exact Ne.symm hpx)⟩
          have hsub : (varHandles rf.envH v).Sublist (localHandlesExcept rf.ctx rf.envH p.2) := by
            simp only [localHandlesExcept]
            exact List.sublist_flatten_of_mem (List.mem_map.mpr ⟨v, hv_filt, rfl⟩)
          have hrt0 := (hclean vs0 (RcCtx.get?_mem hgs0).1).2.2.2.2
          have hevs_b : (bvs &&& 1#64 == 0#64) = true := beq_iff_eq.mpr hevs
          have hvh0 : (varHandles rf.envH vs0).count bvs = vs0.owned := by
            have : vs0.owned ≠ 0 := by omega
            simp [varHandles, hvs0_no, hvs0_ps, hrt0, beq_false_of_ne this,
              (RcCtx.get?_mem hgs0).2 ▸ henvs0, Word.i64, Word.toBV64?, hevs_b]
          have hlh0 := localHandles_count_eq_add hnodup rf.envH (RcCtx.get?_mem hgs0).1 bvs
          rw [(RcCtx.get?_mem hgs0).2, hvh0] at hlh0
          have hs := hsound.2 _ (List.getElem_mem hidx)
            (rc_toInt_pos_of_ne_zero (hwf_all _ (List.getElem_mem hidx)).2.2.1
              (fun h => by rw [h] at hnlt; simp at hnlt))
          simp only [frameHandles, List.count_append, haddr, ← heqb] at hs
          have hle := hsub.count_le bvs
          have hvh_v_bvs : (varHandles rf.envH v).count bvs = v.owned := by
            rw [heqb]; exact hvh_v
          rcases hsh_dec with hnv | hall
          · refine ⟨σ.objs[idx].withRc rc', (list_mem_set_iff hidx).mpr (Or.inl rfl),
              haddr.trans heqb.symm, Or.inr (by simp [LcnfObj.withRc, hrc'_nat]; omega)⟩
          · exfalso
            have hp_ok := hall p hp0 vb0 vs0 hgb0 hgs0
            simp only [hvb0_live, Bool.not_true, hvs0_no, hvs0_ps,
              beq_false_of_ne (by omega : vs0.owned ≠ 0), Bool.false_or,
              beq_false_of_ne hpx] at hp_ok
            obtain ⟨_, _, _, hhu_s, _, hnon_s⟩ :=
              hvars vs0 (RcCtx.get?_mem hgs0).1 (by simp [RcVar.isLive]; omega)
            have hns_s : ¬vs0.ty.isScalar = true := fun hs => by
              have := (hclean vs0 (RcCtx.get?_mem hgs0).1).1.2 hs
              rw [hvs0_no] at this; cases this
            obtain ⟨bvx, hwx, _, _, hex_s, _⟩ := hnon_s hns_s
            have hbx : bvx = bvs := by
              have h1 := congrArg (Option.bind · (fun q => q.2.toBV64?))
                (((RcCtx.get?_mem hgs0).2 ▸ henvs0).symm.trans (hwx ▸ hhu_s))
              have hbx_s : bvs = bvx := by simpa [Word.i64, Word.toBV64?] using h1
              exact hbx_s.symm
            obtain ⟨_, _, _, hox⟩ := hex_s hp_ok
            obtain ⟨ox, hox_m, hox_a, hox_rc⟩ := hox (hbx ▸ hevs)
            have hoeq := obj_eq_of_addr_nodup hnodup_objs hox_m (List.getElem_mem hidx)
              (hox_a.trans (hbx.trans (heqb.trans haddr.symm)))
            rw [← hoeq, hox_rc] at hs
            simp only [BitVec.toNat_ofNat] at hs
            omega
      · obtain ⟨o_s', ho_s', hdeq, h0, _, _⟩ := hmap o_s ho_s (hwf_all o_s ho_s)
        refine ⟨o_s', ho_s', hdeq.1.trans ho_sa, ?_⟩
        rcases horc with h0eq | hlt
        · exact Or.inl (h0 h0eq)
        · right
          obtain ⟨j, hj, hget_j⟩ := obj_mem_idx ho_s
          have hjne : j ≠ idx := fun h => by
            subst h; exact heqb (ho_sa.symm.trans (hget_j.symm ▸ haddr))
          have ho_s_eq : o_s' = o_s :=
            obj_eq_of_addr_nodup hnodup_objs' ho_s'
              ((list_mem_set_iff hidx).mpr (Or.inr ⟨j, hj, hjne, hget_j⟩)) hdeq.1
          rw [ho_s_eq]; omega

private theorem dec_sharedPredInv_same_heap {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx)
    (hsth : SharedTargetsHeap rf) (hsbp : SharedBoolPreds rf.ctx)
    {x n : Nat} (hn : 0 < n) {v : RcVar} (hget : rf.ctx.get? x = some v)
    (hno : v.noRc = false) (hpers : v.persistent = false)
    {bv : BitVec 64} (henvh : rf.envH x = some (v.ty, .i64 bv))
    (hzero : bv &&& 1#64 = 0#64 → ∃ o ∈ σ.objs, o.addr = bv ∧ o.rc = 0#32)
    {ctx1 : RcCtx} (hcons : rf.ctx.consumeVar x n = .ok ctx1)
    (hclean1 : CleanVars ctx1) (hnd1 : (ctx1.vars.map RcVar.id).Nodup)
    (hperm_lh : (localHandles rf.ctx rf.envH).Perm
      (localHandles ctx1 rf.envH ++ consumeVarHandles rf x n))
    (hperm_ex : ∀ s ≠ x, (localHandlesExcept rf.ctx rf.envH s).Perm
      (localHandlesExcept ctx1 rf.envH s ++ consumeVarHandles rf x n)) :
    SharedPredInv { rf with ctx := ctx1 } σ.objs := by
  intro p hp vb1 vs1 hgb1 hgs1 _ hsno hspers
  have ⟨hheap, hnodup, _, _, hsp⟩ := hinv
  have hnodup_objs := hheap.2
  have hn0_b : (n == 0) = false := beq_false_of_ne (by omega)
  have hp0 := consumeVar_sharedPreds_sub hcons p hp
  obtain ⟨vb0, hgb0, hvb0_no⟩ := hsbp p hp0
  have hvb0_live : vb0.isLive = true := by simp [RcVar.isLive, hvb0_no]
  have hflg_s := consumeVar_preserves_flags hnodup hcons p.2
  have ⟨vs0, hgs0, hvs0_no, hvs0_ps, hvs0_ty⟩ : ∃ vs0, rf.ctx.get? p.2 = some vs0 ∧
      vs0.noRc = false ∧ vs0.persistent = false ∧ vs0.ty = vs1.ty := by
    cases hg0 : rf.ctx.get? p.2 with
    | none => rw [hg0, hgs1] at hflg_s; cases hflg_s
    | some w0 =>
      rw [hg0, hgs1] at hflg_s
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hflg_s
      exact ⟨w0, rfl, hflg_s.1.symm.trans hsno, hflg_s.2.1.symm.trans hspers, hflg_s.2.2.symm⟩
  obtain ⟨bvs, henvs0, hevs⟩ := hsth p hp0 vs0 hgs0 hvs0_no
  have henvs : rf.envH p.2 = some (vs1.ty, .i64 bvs) := hvs0_ty ▸ henvs0
  have hzero_case : ∀ (h0 : ∃ o ∈ σ.objs, o.addr = bvs ∧ o.rc = 0#32),
      (((rf.envP p.1).bind PVal.tag? = some 0 →
        ∃ bv, rf.envH p.2 = some (vs1.ty, .i64 bv) ∧ bv &&& 1#64 = 0#64 ∧
          (0 < vs1.owned → nonPersistRefs σ.objs bv +
            (localHandlesExcept ctx1 rf.envH p.2 ++ rf.extH ++ rf.ghostH).count bv = 0 ∧
            ∃ o ∈ σ.objs, o.addr = bv ∧ o.rc.toNat = vs1.owned)) ∧
       ((rf.envP p.1).bind PVal.tag? = some 1 → 0 < vs1.owned →
        ∃ bv, rf.envH p.2 = some (vs1.ty, .i64 bv) ∧ bv &&& 1#64 = 0#64 ∧
          ∃ o ∈ σ.objs, o.addr = bv ∧ (o.rc = 0#32 ∨ vs1.owned < o.rc.toNat))) := by
    rintro ⟨oz, hoz, hoza, hoz0⟩
    refine ⟨fun htag => ⟨bvs, henvs, hevs, fun hspos => ?_⟩,
      fun _ _ => ⟨bvs, henvs, hevs, oz, hoz, hoza, Or.inl hoz0⟩⟩
    exfalso
    have hl_s1 : vs1.isLive = true := by simp [RcVar.isLive, hspos]
    obtain ⟨w0, hw0, _, _, _, _, hw0_le, _⟩ :=
      consumeVar_get?_live_back hnodup hclean hcons p.2 hgs1 hl_s1
    have hweq : w0 = vs0 := by have h := hw0.symm.trans hgs0; cases h; rfl
    subst w0
    obtain ⟨bvs', henvs', _, hrest⟩ :=
      (hsp p hp0 vb0 vs0 hgb0 hgs0 hvb0_live hvs0_no hvs0_ps).1 htag
    have hbeq : bvs' = bvs := by have h := henvs'.symm.trans henvs0; cases h; rfl
    subst bvs'
    obtain ⟨_, o_s, ho_s, ho_sa, ho_src⟩ := hrest (by omega)
    have hoe := obj_eq_of_addr_nodup hnodup_objs ho_s hoz (ho_sa.trans hoza.symm)
    rw [hoe, hoz0] at ho_src; simp at ho_src; omega
  by_cases hpx : p.2 = x
  · have hb_eq : bvs = bv := by
      have h1 := congrArg (Option.bind · (fun q => q.2.toBV64?))
        (henvs0.symm.trans (hpx ▸ henvh))
      simpa [Word.i64, Word.toBV64?] using h1
    exact hzero_case (by
      obtain ⟨o, ho, hoa, horc⟩ := hzero (hb_eq ▸ hevs)
      exact ⟨o, ho, hb_eq ▸ hoa, horc⟩)
  · by_cases heqb : bvs = bv
    · obtain ⟨o, ho, hoa, horc⟩ := hzero (heqb ▸ hevs)
      exact hzero_case ⟨o, ho, heqb ▸ hoa, horc⟩
    · have hcons_cnt : (consumeVarHandles rf x n).count bvs = 0 := by
        by_cases hev : bv &&& 1#64 = 0#64
        · have hbev : (bv &&& 1#64 == 0#64) = true := beq_iff_eq.mpr hev
          have hch : consumeVarHandles rf x n = List.replicate n bv := by
            simp [consumeVarHandles, hget, hno, hpers, hn0_b, henvh, Word.i64, Word.toBV64?, hbev]
          rw [hch, List.count_eq_zero]
          intro hm
          exact heqb (List.eq_of_mem_replicate hm)
        · have hbev : (bv &&& 1#64 == 0#64) = false := beq_false_of_ne hev
          have hch : consumeVarHandles rf x n = [] := by
            simp [consumeVarHandles, hget, hno, hpers, hn0_b, henvh, Word.i64, Word.toBV64?, hbev]
          simp [hch]
      have hlhc := hperm_lh.count_eq bvs
      have hpex := (hperm_ex p.2 hpx).count_eq bvs
      rw [List.count_append, hcons_cnt, Nat.add_zero] at hlhc hpex
      refine ⟨fun htag => ⟨bvs, henvs, hevs, fun hspos => ?_⟩, fun htag hspos => ?_⟩
      · have hl_s1 : vs1.isLive = true := by simp [RcVar.isLive, hspos]
        obtain ⟨w0, hw0, _, _, _, _, hw0_le, _⟩ :=
          consumeVar_get?_live_back hnodup hclean hcons p.2 hgs1 hl_s1
        have hweq : w0 = vs0 := by have h := hw0.symm.trans hgs0; cases h; rfl
        subst w0
        obtain ⟨bvs', henvs', _, hrest⟩ :=
          (hsp p hp0 vb0 vs0 hgb0 hgs0 hvb0_live hvs0_no hvs0_ps).1 htag
        have hbeq : bvs' = bvs := by have h := henvs'.symm.trans henvs0; cases h; rfl
        subst bvs'
        obtain ⟨hc0, o_s, ho_s, ho_sa, ho_src⟩ := hrest (by omega)
        have hlh0 := localHandles_count_eq_add hnodup rf.envH (RcCtx.get?_mem hgs0).1 bvs
        have hlh1 := localHandles_count_eq_add hnd1 rf.envH (RcCtx.get?_mem hgs1).1 bvs
        have hrt0 := (hclean vs0 (RcCtx.get?_mem hgs0).1).2.2.2.2
        have hrt1 := (hclean1 vs1 (RcCtx.get?_mem hgs1).1).2.2.2.2
        have hevs_b : (bvs &&& 1#64 == 0#64) = true := beq_iff_eq.mpr hevs
        have hvh0 : (varHandles rf.envH vs0).count bvs = vs0.owned := by
          have : vs0.owned ≠ 0 := by omega
          simp [varHandles, hvs0_no, hvs0_ps, hrt0, beq_false_of_ne this,
            (RcCtx.get?_mem hgs0).2 ▸ henvs0, Word.i64, Word.toBV64?, hevs_b]
        have hvh1 : (varHandles rf.envH vs1).count bvs = vs1.owned := by
          have : vs1.owned ≠ 0 := by omega
          simp [varHandles, hsno, hspers, hrt1, beq_false_of_ne this,
            (RcCtx.get?_mem hgs1).2 ▸ henvs, Word.i64, Word.toBV64?, hevs_b]
        rw [(RcCtx.get?_mem hgs0).2, hvh0] at hlh0
        rw [(RcCtx.get?_mem hgs1).2, hvh1] at hlh1
        have hown_eq : vs1.owned = vs0.owned := by omega
        simp only [List.count_append] at hc0 ⊢
        exact ⟨by omega, o_s, ho_s, ho_sa, ho_src.trans hown_eq.symm⟩
      · have hl_s1 : vs1.isLive = true := by simp [RcVar.isLive, hspos]
        obtain ⟨w0, hw0, _, _, _, _, hw0_le, _⟩ :=
          consumeVar_get?_live_back hnodup hclean hcons p.2 hgs1 hl_s1
        have hweq : w0 = vs0 := by have h := hw0.symm.trans hgs0; cases h; rfl
        subst w0
        obtain ⟨bvs', henvs', _, o_s, ho_s, ho_sa', horc⟩ :=
          (hsp p hp0 vb0 vs0 hgb0 hgs0 hvb0_live hvs0_no hvs0_ps).2 htag (by omega)
        have hbeq : bvs' = bvs := by have h := henvs'.symm.trans henvs0; cases h; rfl
        have ho_sa : o_s.addr = bvs := ho_sa'.trans hbeq
        refine ⟨bvs, henvs, hevs, o_s, ho_s, ho_sa, ?_⟩
        rcases horc with h0 | hlt
        · exact Or.inl h0
        · exact Or.inr (Nat.lt_of_le_of_lt hw0_le hlt)

private theorem dec_aux_invs {rt : BitVec 64} {rf rf0 : RcFrame} {σ σ0 : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (_hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hepres : EntryPres rf0 σ0 rf σ) (hsbp : SharedBoolPreds rf.ctx) (hexcl : ExclCtorHeap rf)
    {sm : List (Nat × Nat × List Bool)}
    {ρP : PValEnv} (hshdP : ShadowOk sm rf.ctx ρP rf.envP)
    {rem wr rcr : Nat} (hres : ResStateInv σ rem wr rcr)
    {x n : Nat} (hn : 0 < n) {v : RcVar} (hget : rf.ctx.get? x = some v)
    (hno : v.noRc = false) (hpers : v.persistent = false)
    {bv : BitVec 64} (henvh : rf.envH x = some (v.ty, .i64 bv)) (_hev : bv &&& 1#64 = 0#64)
    {idx : Nat} (hidx : idx < σ.objs.length) (haddr : σ.objs[idx].addr = bv)
    (hnlt : n < σ.objs[idx].rc.toNat)
    {ctx1 : RcCtx} (hcons : rf.ctx.consumeVar x n = .ok ctx1)
    (hmap : ∀ q ∈ σ.objs, q.Wf → ∃ q' ∈ (σ.objs.set idx
        (σ.objs[idx].withRc (σ.objs[idx].rc - BitVec.ofNat 32 n))),
      ObjDataEq q q' ∧ (q.rc = 0#32 → q'.rc = 0#32) ∧
      (0 < q.rc.toInt → 0 < q'.rc.toInt) ∧ (q'.rc = 0#32 → q.rc = 0#32))
    (hnodup_objs' : ((σ.objs.set idx
        (σ.objs[idx].withRc (σ.objs[idx].rc - BitVec.ofNat 32 n))).map LcnfObj.addr).Nodup) :
    let rc' := σ.objs[idx].rc - BitVec.ofNat 32 n
    let σ' : HState := { σ with objs := σ.objs.set idx (σ.objs[idx].withRc rc') }
    let rf' : RcFrame := { rf with ctx := ctx1 }
    NoRcCorrect rf'.ctx ∧ ParentChildBacked rf' σ'.objs ∧ SharedTargetsHeap rf' ∧
    HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs ∧ EntryPres rf0 σ0 rf' σ' ∧
    SharedBoolVars rf'.ctx ∧ SharedBoolPreds rf'.ctx ∧ ExclCtorHeap rf' ∧
    ShadowOk sm rf'.ctx ρP rf'.envP ∧ ResStateInv σ' rem wr rcr := by
  intro rc' σ' rf'
  have hnodup := hinv.2.1
  have hwf_all := hinv.1.1.2.1
  have hnodup_objs := hinv.1.2
  have hmap_rc : ∀ q ∈ σ.objs, q.Wf → ∃ q' ∈ σ'.objs,
      q'.addr = q.addr ∧ q'.childFields = q.childFields ∧
      (q.rc = 0#32 → q'.rc = 0#32) ∧ (0 < q.rc.toInt → q'.rc ≠ 0#32) := by
    intro q hq hqwf
    obtain ⟨q', hq', hdeq, h0, hpos, _⟩ := hmap q hq hqwf
    exact ⟨q', hq', hdeq.1, objDataEq_childFields hdeq, h0, fun hp h0' => by
      have := hpos hp; simp [h0'] at this⟩
  have hnorc1 := noRcCorrect_consumeVar hnodup hnorc hcons
  have hpcb0 := parentChildBacked_consumeVar hnodup hclean hcons hpcb
  have hpcb1 : ParentChildBacked rf' σ'.objs := by
    intro u hu hul huno hupers hubor q hpar bvu henvu hevu
    rcases hpcb0 u hu hul huno hupers hubor q hpar bvu henvu hevu with hext | hch
    · exact Or.inl (backed_mono_rc_pos hmap_rc hwf_all (fun _ hr => hr) hext)
    · obtain ⟨wp, o_q, hwp, hqa, ho_q, o_mid, ho_mid, hreach_mid, hcf⟩ := hch
      obtain ⟨o_q', ho_q', hdeq, _⟩ := hmap o_q ho_q (hwf_all o_q ho_q)
      obtain ⟨o_mid', ho_mid', hdeq_m, _⟩ := hmap o_mid ho_mid (hwf_all o_mid ho_mid)
      have hreach' := nonPersistReach_mono_rc_pos hmap_rc hwf_all hreach_mid
      rw [← hdeq.1, ← hdeq_m.1] at hreach'
      exact Or.inr ⟨wp, o_q', hwp, hqa.trans (congrArg some hdeq.1.symm), ho_q',
        o_mid', ho_mid', hreach', objDataEq_childFields hdeq_m ▸ hcf⟩
  have hsth1 := sharedTargetsHeap_consumeVar hnodup hsth hcons
  have hhih1 : HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs := by
    intro a ha
    obtain ⟨q, hq, hqa⟩ := hhih a ha
    obtain ⟨q', hq', hdeq, _⟩ := hmap q hq (hwf_all q hq)
    exact ⟨q', hq', hdeq.1.trans hqa⟩
  have hepres0 := entryPres_consumeVar hnodup hclean hcons hepres
  have hv_own_le : ¬v.owned < n := by
    intro hlt
    unfold RcCtx.consumeVar at hcons
    simp [hget, hno, hpers, beq_false_of_ne (by omega : n ≠ 0), hlt] at hcons
  have hepres1 : EntryPres rf0 σ0 rf' σ' := by
    obtain ⟨hhs0, hiso0, hext0, hgh0⟩ := hepres0
    have hhs_step : HeapStepRel (rf0.extH ++ rf0.ghostH) σ σ' := by
      refine ⟨by simp [σ', RtC0State.PreservesMeta], rfl, rfl, fun q hq hqwf _ => ?_,
        fun a hb => backed_mono_rc_pos hmap_rc hwf_all (fun _ hr => hr) hb⟩
      obtain ⟨q', hq', hdeq, h0, hpos, _⟩ := hmap q hq hqwf
      exact ⟨q', hq', hdeq, h0, hpos⟩
    refine ⟨heapStepRel_trans hhs0 hhs_step, ?_, hext0, hgh0⟩
    intro a ha hiso_a0
    obtain ⟨⟨hiso_live, hiso_np, o_a, ho_a, ho_awf, ho_aa, ho_arc1⟩, ha_rc1⟩ := hiso0 a ha hiso_a0
    have hiso_pre := (hepres.2.1 a ha hiso_a0).1.1
    have hne_bv : a ≠ bv := fun heq => by
      have hlive_v : v.isLive = true := by simp [RcVar.isLive]; omega
      have hns_v : !v.ty.isScalar = true := by
        have := (hclean v (RcCtx.get?_mem hget).1).1.2
        cases h : v.ty.isScalar <;> simp_all
      exact absurd (congrArg some heq.symm)
        (hiso_pre v (RcCtx.get?_mem hget).1 hlive_v hns_v
          (.i64 bv) ((RcCtx.get?_mem hget).2 ▸ henvh))
    obtain ⟨j, hj, hget_j⟩ := obj_mem_idx ho_a
    have hjne : j ≠ idx := fun h => by
      subst h; exact hne_bv (ho_aa.symm.trans (hget_j.symm ▸ haddr))
    have ho_a' : o_a ∈ σ'.objs := (list_mem_set_iff hidx).mpr (Or.inr ⟨j, hj, hjne, hget_j⟩)
    have hrc_nz : σ.objs[idx].rc ≠ 0#32 := fun h => by rw [h] at hnlt; simp at hnlt
    have hle_n : BitVec.ofNat 32 n ≤ σ.objs[idx].rc := by
      rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 32)]
      omega
    have hrc'_nz : rc' ≠ 0#32 := by
      intro h
      have hsub := BitVec.toNat_sub_of_le hle_n
      change rc'.toNat = σ.objs[idx].rc.toNat - (BitVec.ofNat 32 n).toNat at hsub
      rw [h] at hsub
      have hmod : (BitVec.ofNat 32 n).toNat = n := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      simp [hmod] at hsub; omega
    have hnp_a' : nonPersistRefs σ'.objs a = 0 := by
      rw [nonPersistRefs_set_withRc hidx
        ⟨fun h => absurd h hrc_nz, fun h => absurd h hrc'_nz⟩ a]
      exact hiso_np
    refine ⟨⟨hiso_live, hnp_a', o_a, ho_a', ho_awf, ho_aa, ho_arc1⟩, fun q0 hq0 hqa0 => ?_⟩
    obtain ⟨q, hq, hdeq, hq1⟩ := ha_rc1 q0 hq0 hqa0
    obtain ⟨jq, hjq, hget_jq⟩ := obj_mem_idx hq
    have hjqne : jq ≠ idx := fun h => by
      subst h; exact hne_bv (hqa0.symm.trans (hdeq.1.symm.trans (hget_jq.symm ▸ haddr)))
    exact ⟨q, (list_mem_set_iff hidx).mpr (Or.inr ⟨jq, hjq, hjqne, hget_jq⟩), hdeq, hq1⟩
  have hsbp1 := sharedBoolPreds_consumeVar hnodup hsbp hcons
  have hsbv1 := sharedBoolPreds_vars hsbp1
  have hexcl1 := exclCtorHeap_consumeVar hnodup hclean hcons hexcl
  have hshd1 := shadowOk_consumeVar hnodup hclean hcons hshdP
  have hres1 : ResStateInv σ' rem wr rcr := by
    refine ⟨hres.1, by simpa [σ'] using hres.2.1, ?_⟩
    have hm : maxObjRc σ'.objs ≤ maxObjRc σ.objs := by
      apply maxObjRc_set_le
      intro _
      have hle : BitVec.ofNat 32 n ≤ σ.objs[idx].rc := by
        rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 32)]
        omega
      have hmod : (BitVec.ofNat 32 n).toNat = n := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have hsub := BitVec.toNat_sub_of_le hle
      simp only [LcnfObj.withRc]
      dsimp only [rc']
      rw [hsub, hmod]
      omega
    have hmax_le : Nat.max 1 (maxObjRc σ'.objs) ≤ Nat.max 1 (maxObjRc σ.objs) :=
      Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hm (Nat.le_max_right _ _)⟩
    have := hres.2.2; omega
  exact ⟨hnorc1, hpcb1, hsth1, hhih1, hepres1, hsbv1, hsbp1, hexcl1, hshd1, hres1⟩

/-- Stepwise simulation for `LcCode.dec` exposing `extH` and `consumeVar` post-context. -/
public theorem dec_step_ctx {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {J : HJEnv} {Jp : PResJEnv}
    {Q : PResPost} {Xp : PResXPost} {Qh : HPost} {Xh : HXPost}
    {jps : List RcJpInfo} {rf rf0 : RcFrame} {σ σ0 : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr : Nat}
    {x n : Nat} {chk : Bool} {k : LcCode}
    (hwf : perceusCodeWf env retTy jps rf.ctx sm (LcCode.dec x n chk k) = true)
    (hpr : PRWp m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Q Xp (LcCode.dec x n chk k))
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hepres : EntryPres rf0 σ0 rf σ) (hsbv : SharedBoolVars rf.ctx)
    (hsbp : SharedBoolPreds rf.ctx) (hexcl : ExclCtorHeap rf)
    (hsm : ShadowSmWf sm) (hshd : ShadowOk sm rf.ctx ρP rf.envP)
    (hres : ResStateInv σ rem wr rcr)
    (hk : ∀ {rf' : RcFrame} {σ' : HState},
      perceusCodeWf env retTy jps rf'.ctx sm k = true →
      PRWp m env retTy Δr jps rf'.ctx Jp ρP rem wr rcr Q Xp k →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs → EntryPres rf0 σ0 rf' σ' →
      SharedBoolVars rf'.ctx → SharedBoolPreds rf'.ctx → ExclCtorHeap rf' →
      ShadowSmWf sm → ShadowOk sm rf'.ctx ρP rf'.envP → ResStateInv σ' rem wr rcr →
      rf'.envH = rf.envH ∧ rf'.envP = rf.envP ∧ rf'.extH = rf.extH ∧
        rf.ctx.consumeVar x n = .ok rf'.ctx →
      HWp Δh rt retTy J rf'.envH Qh Xh k σ') :
    HWp Δh rt retTy J rf.envH Qh Xh (LcCode.dec x n chk k) σ := by
  rw [perceusCodeWf.eq_16] at hwf
  rw [PRWp.eq_12] at hpr
  rw [HWp.eq_12]
  cases hget : rf.ctx.get? x with
  | none => simp [hget] at hwf
  | some v =>
    simp only [hget, Bool.and_eq_true, decide_eq_true_eq] at hwf
    rcases hwf with ⟨⟨⟨⟨hlive, hw64⟩, hchk⟩, hsh_guard⟩, hwf_rest⟩
    cases hcons : rf.ctx.consumeVar x n with
    | error _ => simp [hcons] at hpr
    | ok ctx1 =>
      simp only [hcons] at hwf_rest hpr
      rcases hpr with ⟨hsafe, hpr_k⟩
      have hnodup := hinv.2.1
      have hnodup_objs := hinv.1.2
      obtain ⟨bv, henvh, htbv⟩ := getTypedBV64?_of_varInv hinv.2.2.2.1
        (RcCtx.get?_mem hget).1 hlive (by simpa using hw64)
      have htbv_x : rf.envH.getTypedBV64? x = some (v.ty, bv) :=
        (RcCtx.get?_mem hget).2 ▸ htbv
      have henvh_x : rf.envH x = some (v.ty, .i64 bv) :=
        (RcCtx.get?_mem hget).2 ▸ henvh
      rw [htbv_x]
      have hskip_ctx : v.noRc = true ∨ v.persistent = true →
          ctx1 = rf.ctx ∧ (¬v.ty.needsRc = true ∨
            (bv &&& 1#64 ≠ 0#64 ∧ chk = true ∧ v.ty = .tobject) ∨
            (bv &&& 1#64 = 0#64 ∧ ∃ o ∈ σ.objs, o.addr = bv ∧ o.rc = 0#32)) := by
        intro hs
        have hce : ctx1 = rf.ctx := by
          unfold RcCtx.consumeVar at hcons; rw [hget] at hcons
          rcases hs with h1 | h2
          · simp [h1, pure, Except.pure] at hcons; exact hcons.symm
          · simp [h2, pure, Except.pure] at hcons; exact hcons.symm
        refine ⟨hce, ?_⟩
        by_cases hnr : v.ty.needsRc = true
        · have hnonsc : ¬v.ty.isScalar = true := by
            cases hty : v.ty <;> simp_all [LcTy.needsRc, LcTy.isScalar]
          obtain ⟨_, _, _, hhu, _, hnon⟩ := hinv.2.2.2.1 v (RcCtx.get?_mem hget).1 hlive
          obtain ⟨bv0, hw0, hno_r, hpers_r, _⟩ := hnon hnonsc
          have heq_bv : bv = bv0 := by
            have := henvh.symm.trans (hw0 ▸ hhu); cases this; rfl
          rcases hs with h1 | h2
          · right; left
            have hodd : bv &&& 1#64 ≠ 0#64 := heq_bv ▸ hno_r h1
            have htb := tobject_of_ne_even_dec hinv hget hlive hnr henvh_x hodd
            exact ⟨hodd, hchk (by rw [htb]; rfl), htb⟩
          · by_cases hev : bv &&& 1#64 = 0#64
            · right; right
              obtain ⟨oz, hoz, hoza, hozr⟩ := hpers_r h2 (heq_bv ▸ hev)
              exact ⟨hev, oz, hoz, hoza.trans heq_bv.symm, hozr⟩
            · right; left
              have htb := tobject_of_ne_even_dec hinv hget hlive hnr henvh_x hev
              exact ⟨hev, hchk (by rw [htb]; rfl), htb⟩
        · exact Or.inl hnr
      by_cases hn0 : n = 0
      · subst hn0
        have hce : ctx1 = rf.ctx := by
          unfold RcCtx.consumeVar at hcons; rw [hget] at hcons
          cases h : (v.noRc || v.persistent)
          · simp [h, pure, Except.pure] at hcons; exact hcons.symm
          · simp [h, pure, Except.pure] at hcons; exact hcons.symm
        subst hce
        exact hk hwf_rest hpr_k hinv hclean hpo hnorc hpcb hsth hhih hepres hsbv hsbp
          hexcl hsm hshd hres ⟨rfl, rfl, rfl, hcons⟩
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      by_cases hskip_v : v.noRc = true ∨ v.persistent = true
      · obtain ⟨hce, hcond⟩ := hskip_ctx hskip_v
        subst hce
        exact HDecN_skip hnodup_objs hinv.1.1.2.1 hcond n
          (hk hwf_rest hpr_k hinv hclean hpo hnorc hpcb hsth hhih hepres hsbv hsbp
            hexcl hsm hshd hres ⟨rfl, rfl, rfl, hcons⟩)
      have hno : v.noRc = false := by cases h : v.noRc <;> simp_all
      have hpers : v.persistent = false := by cases h : v.persistent <;> simp_all
      by_cases hnr : v.ty.needsRc = true
      · have hsame_heap : (bv &&& 1#64 = 0#64 → ∃ o ∈ σ.objs, o.addr = bv ∧ o.rc = 0#32) →
            HDecN bv v.ty chk n
              (HWp Δh rt retTy J { rf with ctx := ctx1 }.envH Qh Xh k) σ := by
          intro hzero
          obtain ⟨hperm_lh, hperm_ex, hheap1, hnd1, hsound1, hvars1, hclean1, hpo1, _⟩ :=
            rcInv_consumeVar_no_sp hinv hclean hpo hcons
          have hsp1 := dec_sharedPredInv_same_heap hinv hclean hsth hsbp hn_pos hget hno hpers
            henvh_x hzero hcons hclean1 hnd1 hperm_lh hperm_ex
          have hinv1 : RcInv rt { rf with ctx := ctx1 } σ := ⟨hheap1, hnd1, hsound1, hvars1, hsp1⟩
          have hnorc1 := noRcCorrect_consumeVar hnodup hnorc hcons
          have hpcb1 := parentChildBacked_consumeVar hnodup hclean hcons hpcb
          have hsth1 := sharedTargetsHeap_consumeVar hnodup hsth hcons
          have hepres1 := entryPres_consumeVar hnodup hclean hcons hepres
          have hsbp1 := sharedBoolPreds_consumeVar hnodup hsbp hcons
          have hsbv1 := sharedBoolPreds_vars hsbp1
          have hexcl1 := exclCtorHeap_consumeVar hnodup hclean hcons hexcl
          have hshd1 := shadowOk_consumeVar hnodup hclean hcons hshd
          have hcond : (bv &&& 1#64 ≠ 0#64 ∧ chk = true ∧ v.ty = .tobject) ∨
              (bv &&& 1#64 = 0#64 ∧ ∃ o ∈ σ.objs, o.addr = bv ∧ o.rc = 0#32) := by
            by_cases hev : bv &&& 1#64 = 0#64
            · exact Or.inr ⟨hev, hzero hev⟩
            · have htb := tobject_of_ne_even_dec hinv hget hlive hnr henvh_x hev
              exact Or.inl ⟨hev, hchk (by rw [htb]; rfl), htb⟩
          refine HDecN_skip hnodup_objs hinv.1.1.2.1 (Or.inr hcond) n ?_
          exact hk hwf_rest hpr_k hinv1 hclean1 hpo1 hnorc1 hpcb1 hsth1 hhih hepres1
            hsbv1 hsbp1 hexcl1 hsm hshd1 hres ⟨rfl, rfl, rfl, hcons⟩
        by_cases hev : bv &&& 1#64 = 0#64
        · have hnonsc : ¬v.ty.isScalar = true := by
            cases hty : v.ty <;> simp_all [LcTy.needsRc, LcTy.isScalar]
          obtain ⟨_, wu, hE, hhu, hrep, hnon⟩ := hinv.2.2.2.1 v (RcCtx.get?_mem hget).1 hlive
          obtain ⟨bv0, hw0, _, _, _⟩ := hnon hnonsc
          have heq_bv : bv = bv0 := by
            have := henvh.symm.trans (hw0 ▸ hhu); cases this; rfl
          have hv_own_le : ¬v.owned < n := by
            intro hlt
            unfold RcCtx.consumeVar at hcons
            simp [hget, hno, hpers, beq_false_of_ne hn0, hlt] at hcons
          have hlt_n_or_z : (∃ o ∈ σ.objs, o.addr = bv ∧ o.rc = 0#32) ∨
              (∃ idx : Nat, ∃ _ : idx < σ.objs.length,
                σ.objs[idx].addr = bv ∧ n < σ.objs[idx].rc.toNat) := by
            simp only [safeNonColdDec, hget] at hsafe
            cases hρx : ρP x with
            | none => simp [hρx] at hsafe
            | some pv =>
              simp only [hρx] at hsafe
              rcases hsafe with h1 | h2 | htag | hnlt_own | ⟨b, hbx, hbtag⟩
              · rw [h1] at hno; cases hno
              · rw [h2] at hpers; cases hpers
              · exfalso
                obtain ⟨pv', hE', htag'⟩ := shadow_isTaggedPVal hshd (RcCtx.get?_mem hget).1
                  hlive ((RcCtx.get?_mem hget).2 ▸ hρx) htag
                rw [hE] at hE'; cases hE'
                exact absurd (heq_bv ▸ hev) (isTaggedPVal_odd hnonsc htag' (hw0 ▸ hrep))
              · obtain ⟨o, ho, hoa⟩ := valRep_even_mem (hw0 ▸ hrep) hnonsc (heq_bv ▸ hev)
                obtain ⟨idx, hidx, hget_idx⟩ := obj_mem_idx ho
                have haddr : σ.objs[idx].addr = bv := hget_idx ▸ hoa.trans heq_bv.symm
                by_cases hrc0 : σ.objs[idx].rc = 0#32
                · exact Or.inl ⟨σ.objs[idx], List.getElem_mem hidx, haddr, hrc0⟩
                · have hrc_pos : 0 < σ.objs[idx].rc.toInt :=
                    rc_toInt_pos_of_ne_zero (hinv.1.1.2.1 _ (List.getElem_mem hidx)).2.2.1 hrc0
                  have hrt_v := (hclean v (RcCtx.get?_mem hget).1).2.2.2.2
                  have hbev : (bv &&& 1#64 == 0#64) = true := beq_iff_eq.mpr hev
                  have hvh_v : (varHandles rf.envH v).count bv = v.owned := by
                    simp [varHandles, hno, hpers, hrt_v, beq_false_of_ne (by omega : v.owned ≠ 0),
                      henvh, Word.i64, Word.toBV64?, hbev]
                  have hle_lh := localHandles_count_eq_add hnodup rf.envH
                    (RcCtx.get?_mem hget).1 bv
                  rw [(RcCtx.get?_mem hget).2, hvh_v] at hle_lh
                  have hs := hinv.2.2.1.2 _ (List.getElem_mem hidx) hrc_pos
                  simp only [frameHandles, List.count_append, haddr] at hs
                  exact Or.inr ⟨idx, hidx, haddr, by omega⟩
              · obtain ⟨vb, hgb, hvb_no⟩ := hsbp (b, x) hbx
                have hvb_live : vb.isLive = true := by simp [RcVar.isLive, hvb_no]
                have hid_b : vb.id = b := (RcCtx.get?_mem hgb).2
                have htag_b : (rf.envP b).bind PVal.tag? = some 1 := by
                  rw [← hid_b, ← shadow_tag?_eq hshd (RcCtx.get?_mem hgb).1 hvb_live, hid_b]
                  exact hbtag
                obtain ⟨bvs, henvs, _, o_s, ho_s, ho_sa, horc⟩ :=
                  (hinv.2.2.2.2 (b, x) hbx vb v hgb hget hvb_live hno hpers).2 htag_b
                    (by omega)
                have hb_eq : bvs = bv := by
                  have h := henvs.symm.trans henvh_x; cases h; rfl
                rcases horc with hrc0 | hlt
                · exact Or.inl ⟨o_s, ho_s, ho_sa.trans hb_eq, hrc0⟩
                · obtain ⟨idx, hidx, hget_idx⟩ := obj_mem_idx ho_s
                  exact Or.inr ⟨idx, hidx, hget_idx ▸ ho_sa.trans hb_eq, by rw [hget_idx]; omega⟩
          rcases hlt_n_or_z with ⟨o, ho, hoa, hrc0⟩ | ⟨idx, hidx, haddr, hnlt⟩
          · exact hsame_heap (fun _ => ⟨o, ho, hoa, hrc0⟩)
          · obtain ⟨hperm_lh, hperm_ex, _, hnd1, _, hvars1, hclean1, hpo1, hown_x⟩ :=
              rcInv_consumeVar_no_sp hinv hclean hpo hcons
            obtain ⟨hheap', hsound', hvars', hmap, hnpre, hcnt_f⟩ :=
              dec_heap_sound_vars hinv hclean hn_pos hget hno hpers henvh_x hev hidx haddr hnlt
                hcons hperm_lh hclean1 hnd1 hpo1 hvars1
            have hsh_dec : n < v.owned ∨ ∀ p ∈ rf.ctx.sharedPreds, ∀ vb vt,
                rf.ctx.get? p.1 = some vb → rf.ctx.get? p.2 = some vt →
                (!vb.isLive || vt.noRc || vt.persistent || vt.owned == 0 ||
                  p.2 == x || vt.excl) = true := by
              simp only [hno, hpers, beq_false_of_ne hn0, Bool.false_or, Bool.or_eq_true,
                decide_eq_true_eq, List.all_eq_true, Prod.forall] at hsh_guard
              rcases hsh_guard with hlt | hall
              · exact Or.inl hlt
              · exact Or.inr fun p hp vb vt hgp1 hgp2 => by
                  simpa [hgp1, hgp2] using hall p.1 p.2 hp
            have hsp' := dec_sharedPredInv hinv hclean hsth hsbp hn_pos hget hno hpers henvh_x hev
              hidx haddr hnlt hcons hsh_dec hclean1 hnd1 hperm_ex hown_x hnpre hcnt_f hmap
            obtain ⟨hnorc', hpcb', hsth', hhih', hepres', hsbv', hsbp', hexcl', hshd', hres'⟩ :=
              dec_aux_invs hinv hclean hpo hnorc hpcb hsth hhih hepres hsbp hexcl hshd hres
                hn_pos hget hno hpers henvh_x hev hidx haddr hnlt hcons hmap hheap'.2
            refine HDecN_nonCold_run hnr hev n σ hnodup_objs hidx haddr hinv.1.1.2.1
              (hinv.1.1.2.2.2.2 _ (List.getElem_mem hidx)) hnlt ?_
            exact hk (rf' := { rf with ctx := ctx1 }) hwf_rest hpr_k
              ⟨hheap', hnd1, hsound', hvars', hsp'⟩ hclean1 hpo1
              hnorc' hpcb' hsth' hhih' hepres' hsbv' hsbp' hexcl' hsm hshd' hres'
              ⟨rfl, rfl, rfl, hcons⟩
        · exact hsame_heap (fun h => absurd h hev)
      · exact absurd (hnorc v (RcCtx.get?_mem hget).1 hno) hnr

/-- Stepwise simulation for `LcCode.dec`: advances `HWp`, `RcInv`, and all auxiliary
    invariants without hitting `DecColdRel`. -/
public theorem dec_step {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {J : HJEnv} {Jp : PResJEnv}
    {Q : PResPost} {Xp : PResXPost} {Qh : HPost} {Xh : HXPost}
    {jps : List RcJpInfo} {rf rf0 : RcFrame} {σ σ0 : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr : Nat}
    {x n : Nat} {chk : Bool} {k : LcCode}
    (hwf : perceusCodeWf env retTy jps rf.ctx sm (LcCode.dec x n chk k) = true)
    (hpr : PRWp m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Q Xp (LcCode.dec x n chk k))
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hepres : EntryPres rf0 σ0 rf σ) (hsbv : SharedBoolVars rf.ctx)
    (hsbp : SharedBoolPreds rf.ctx) (hexcl : ExclCtorHeap rf)
    (hsm : ShadowSmWf sm) (hshd : ShadowOk sm rf.ctx ρP rf.envP)
    (hres : ResStateInv σ rem wr rcr)
    (hk : ∀ {rf' : RcFrame} {σ' : HState},
      perceusCodeWf env retTy jps rf'.ctx sm k = true →
      PRWp m env retTy Δr jps rf'.ctx Jp ρP rem wr rcr Q Xp k →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs → EntryPres rf0 σ0 rf' σ' →
      SharedBoolVars rf'.ctx → SharedBoolPreds rf'.ctx → ExclCtorHeap rf' →
      ShadowSmWf sm → ShadowOk sm rf'.ctx ρP rf'.envP → ResStateInv σ' rem wr rcr →
      rf'.envH = rf.envH ∧ rf'.envP = rf.envP →
      HWp Δh rt retTy J rf'.envH Qh Xh k σ') :
    HWp Δh rt retTy J rf.envH Qh Xh (LcCode.dec x n chk k) σ :=
  dec_step_ctx hwf hpr hinv hclean hpo hnorc hpcb hsth hhih hepres hsbv hsbp hexcl hsm hshd hres
    fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 he =>
      hk h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 ⟨he.1, he.2.1⟩

end DecStep

end LeanQbe.T.LeanLCNF.Sem