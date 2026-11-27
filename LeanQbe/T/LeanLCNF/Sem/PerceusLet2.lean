module

public import LeanQbe.T.LeanLCNF.Sem.PerceusLet1
import LeanQbe.T.Logic.ProofKit

/-!
# LCNF Perceus-Sound Simulation: `let_` Bind-Wrapper Lemmas (`PerceusLet2`)

Full invariant-preservation wrappers for non-pointer, `isShared`, borrowed, `box`, and `ctor`
bindings, plus field-count and shared-predicate accounting across `applyArgs` and allocation.
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

section BindWrappers

public theorem bind_nonPtr_step_invs {rt : BitVec 64} {rf0 rf : RcFrame}
    {σ0 σ : HState} {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv}
    {x : Nat} {ty : LcTy} {pv : PVal} {w : Word}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hno : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hep : EntryPres rf0 σ0 rf σ) (hsbp : SharedBoolPreds rf.ctx)
    (hexcl : ExclCtorHeap rf) (hshd : ShadowOk sm rf.ctx ρP rf.envP)
    (hfr : binderFreshOwned rf.ctx x = true)
    (hrep : ValRep ty pv w σ.objs)
    (htag : ¬ty.isScalar = true → ∃ bv, w = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64) :
    let ctx' := rf.ctx.bindOwned x ty
    let rf' : RcFrame := {
      ctx := ctx', envP := rf.envP.set x pv, envH := rf.envH.set x ty w,
      extH := rf.extH, ghostH := rf.ghostH }
    RcInv rt rf' σ ∧ CleanVars ctx' ∧ ParentsOwned ctx' ∧ NoRcCorrect ctx' ∧
      ParentChildBacked rf' σ.objs ∧ SharedTargetsHeap rf' ∧
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ.objs ∧ EntryPres rf0 σ0 rf' σ ∧
      SharedBoolVars ctx' ∧ SharedBoolPreds ctx' ∧ ExclCtorHeap rf' ∧
      ShadowOk (sm.filter (fun e => e.1 != x)) ctx' (ρP.set x pv) rf'.envP := by
  intro ctx' rf'
  have hnd : (rf.ctx.vars.map RcVar.id).Nodup := hinv.2.1
  have hwf_all : ∀ o ∈ σ.objs, o.Wf := fun o ho => hinv.1.1.2.1 o ho
  have hrc := rcInv_bind_nonPtr hinv hclean hfr ty false hrep htag
  have hpo' := parentsOwned_bindOwned hnd hpo hfr ty false false false
  have hno' := noRcCorrect_bindOwned hnd hno x ty false false false
  let vx : RcVar := {
    id := x, ty := ty, noRc := !ty.needsRc,
    persistent := if (!ty.needsRc) = true then false else false,
    owned := if (!ty.needsRc || false) = true then 0 else 1,
    excl := if (!ty.needsRc || false) = true then false else false,
    resetTok := if (!ty.needsRc || false) = true then false else false }
  have hpcb' : ParentChildBacked rf' σ.objs := by
    apply parentChildBacked_bindFreshOwned hnd hclean hwf_all hinv.2.2.2.1 hpo hpcb hfr
      (v := vx) rfl rfl (roots := localHandles rf.ctx rf.envH)
    · intro pv0 hpv0 hno0 hps0 hown0 bp hbp hev_bp
      have hc := localHandles_count_eq_add hnd rf.envH hpv0 bp
      have hrt0 : pv0.resetTok = false := (hclean pv0 hpv0).2.2.2.2
      have hown0_ne : (pv0.owned == 0) = false := by simp; omega
      have hvh : varHandles rf.envH pv0 = List.replicate pv0.owned bp := by
        simp [varHandles, hno0, hps0, hrt0, hown0_ne, hbp, Word.toBV64?, Word.i64, hev_bp]
      rw [← List.count_pos_iff, hc, hvh, List.count_replicate]
      simp only [beq_self_eq_true, ↓reduceIte]; omega
    · intro o ho howf _; exact ⟨o, ho, objDataEq_refl o howf, id⟩
    · intro a ha; exact ha
  have hsth' : SharedTargetsHeap rf' :=
    sharedTargetsHeap_put_fresh hnd hsth hfr (v := vx) rfl (fun p hp => hp)
  have hep' : EntryPres rf0 σ0 rf' σ := entryPres_bindNonPtr hnd hwf_all hfr (v := vx) rfl
    (pv := pv) (fun hns => htag hns) hep
  have hsbp' : SharedBoolPreds (rf.ctx.put vx) := sharedBoolPreds_put_fresh hnd hsbp
    (fun p hp => (binderFreshOwned_mem_false hfr p hp).1)
  have hsbv' := sharedBoolPreds_vars hsbp'
  have hexcl' : ExclCtorHeap rf' := exclCtorHeap_put_nonExcl hnd hexcl (vx := vx) rfl (by simp [vx])
  have hshd' := shadowOk_put_same hnd hshd (vx := vx) rfl (pv := pv)
  exact ⟨hrc.1, hrc.2, hpo', hno', hpcb', hsth', hhih, hep', hsbv', hsbp', hexcl', hshd'⟩

public theorem bind_isShared_step_invs {rt : BitVec 64} {rf0 rf : RcFrame}
    {σ0 σ : HState} {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv}
    {x y : Nat} {vy : RcVar} {bv : BitVec 64} {o : LcnfObj}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hno : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hep : EntryPres rf0 σ0 rf σ) (hsbp : SharedBoolPreds rf.ctx)
    (hexcl : ExclCtorHeap rf) (hshd : ShadowOk sm rf.ctx ρP rf.envP)
    (hfr : binderFreshOwned rf.ctx x = true)
    (hgy : rf.ctx.get? y = some vy) (hylive : vy.isLive = true) (hyown : vy.owned ≤ 1)
    (hyh : rf.envH y = some (vy.ty, Word.i64 bv)) (ho : o ∈ σ.objs) (hoa : o.addr = bv) :
    let b := decide (o.rc ≠ 1#32)
    let ctx1 := rf.ctx.bindOwned x LcTy.uint8
    let ctx' : RcCtx := { vars := ctx1.vars, sharedPreds := (x, y) :: ctx1.sharedPreds }
    let rf' : RcFrame := {
      ctx := ctx', envP := rf.envP.set x (PVal.bool b),
      envH := rf.envH.set x LcTy.uint8 (Word.i8 (if o.rc ≠ 1#32 then 1#8 else 0#8)),
      extH := rf.extH, ghostH := rf.ghostH }
    RcInv rt rf' σ ∧ CleanVars ctx' ∧ ParentsOwned ctx' ∧ NoRcCorrect ctx' ∧
      ParentChildBacked rf' σ.objs ∧ SharedTargetsHeap rf' ∧
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ.objs ∧ EntryPres rf0 σ0 rf' σ ∧
      SharedBoolVars ctx' ∧ SharedBoolPreds ctx' ∧ ExclCtorHeap rf' ∧
      ShadowOk (sm.filter (fun e => e.1 != x)) ctx' (ρP.set x (PVal.bool b)) rf'.envP := by
  intro b ctx1 ctx' rf'
  have hnd : (rf.ctx.vars.map RcVar.id).Nodup := hinv.2.1
  have hwf_all : ∀ q ∈ σ.objs, q.Wf := fun q hq => hinv.1.1.2.1 q hq
  have hrc := rcInv_bind_isShared hinv hclean hfr hgy hylive hyown hyh ho hoa
  have hpo' : ParentsOwned ctx' := parentsOwned_bindOwned hnd hpo hfr LcTy.uint8 false false false
  have hno' : NoRcCorrect ctx' := noRcCorrect_bindOwned hnd hno x LcTy.uint8 false false false
  let vx : RcVar := {
    id := x, ty := LcTy.uint8, noRc := !LcTy.uint8.needsRc,
    persistent := if (!LcTy.uint8.needsRc) = true then false else false,
    owned := if (!LcTy.uint8.needsRc || false) = true then 0 else 1,
    excl := if (!LcTy.uint8.needsRc || false) = true then false else false,
    resetTok := if (!LcTy.uint8.needsRc || false) = true then false else false }
  have hpcb' : ParentChildBacked rf' σ.objs := by
    have h1 : ParentChildBacked rf' σ.objs :=
      parentChildBacked_bindFreshOwned hnd hclean hwf_all hinv.2.2.2.1 hpo hpcb hfr
      (v := vx) rfl rfl (pv := PVal.bool b) (roots := localHandles rf.ctx rf.envH)
      (fun pv0 hpv0 hno0 hps0 hown0 bp hbp hev_bp => by
        have hc := localHandles_count_eq_add hnd rf.envH hpv0 bp
        have hrt0 : pv0.resetTok = false := (hclean pv0 hpv0).2.2.2.2
        have hown0_ne : (pv0.owned == 0) = false := by simp; omega
        have hvh : varHandles rf.envH pv0 = List.replicate pv0.owned bp := by
          simp [varHandles, hno0, hps0, hrt0, hown0_ne, hbp, Word.toBV64?, Word.i64, hev_bp]
        rw [← List.count_pos_iff, hc, hvh, List.count_replicate]
        simp only [beq_self_eq_true, ↓reduceIte]; omega)
      (fun q hq hqwf _ => ⟨q, hq, objDataEq_refl q hqwf, id⟩)
      (fun a ha => ha)
    intro u hu hl hno_u hps hbr p hp bv_u hev hevn
    exact h1 u hu hl hno_u hps hbr p hp bv_u hev hevn
  have hxy_ne : y ≠ x := by
    intro heq; subst heq
    simp only [binderFreshOwned, Bool.and_eq_true, hgy, Bool.not_eq_true'] at hfr
    rw [hylive] at hfr; simp at hfr
  have hsth' : SharedTargetsHeap rf' := by
    intro p hp vt hgt htno
    change p ∈ (x, y) :: ctx1.sharedPreds at hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | hp
    · have hgt1 : rf.ctx.get? y = some vt := by
        have hget : ctx1.get? y = some vt := hgt
        change (rf.ctx.put vx).get? y = some vt at hget
        have hxid : vx.id = x := rfl
        rw [RcCtx.put_get? hnd vx y, hxid] at hget
        simp only [beq_false_of_ne hxy_ne, Bool.false_eq_true, ↓reduceIte] at hget
        exact hget
      rw [hgy] at hgt1; injection hgt1 with hvt; subst hvt
      refine ⟨bv, by simp [rf', HValEnv.set, hxy_ne, hyh], ?_⟩
      have howf := hwf_all o ho
      have hmod := hoa ▸ howf.2.1
      apply BitVec.eq_of_toNat_eq
      have hmod1 : (1#64).toNat = 1 := rfl
      have hmod0 : (0#64).toNat = 0 := rfl
      simp only [BitVec.toNat_and, hmod1, hmod0]
      have hband := Nat.and_one_is_mod bv.toNat
      omega
    · have hsth1 : SharedTargetsHeap { rf' with ctx := ctx1 } :=
        sharedTargetsHeap_put_fresh hnd hsth hfr (v := vx) rfl (fun q hq => hq)
      exact hsth1 p hp vt hgt htno
  have hep' : EntryPres rf0 σ0 rf' σ := by
    have hep1 : EntryPres rf0 σ0 { rf' with ctx := ctx1 } σ :=
      entryPres_bindNonPtr hnd hwf_all hfr (v := vx) rfl (pv := PVal.bool b)
        (w := Word.i8 (if o.rc ≠ 1#32 then 1#8 else 0#8)) (fun h => absurd rfl h) hep
    exact ⟨hep1.1, hep1.2.1, hep1.2.2⟩
  have hsbp' : SharedBoolPreds ctx' := sharedBoolPreds_bind_isShared hnd hfr hsbp (y := y)
  have hsbv' := sharedBoolPreds_vars hsbp'
  have hexcl' : ExclCtorHeap rf' := by
    have h1 := exclCtorHeap_put_nonExcl hnd hexcl (vx := vx) rfl
      (pv := PVal.bool b) (w := Word.i8 (if o.rc ≠ 1#32 then 1#8 else 0#8)) (by simp [vx])
    exact fun v hv => h1 v hv
  have hshd' : ShadowOk (sm.filter (fun e => e.1 != x)) ctx' (ρP.set x (PVal.bool b)) rf'.envP := by
    have h1 := shadowOk_put_same hnd hshd (vx := vx) rfl (pv := PVal.bool b)
    exact fun v hv => h1 v hv
  exact ⟨hrc.1, hrc.2, hpo', hno', hpcb', hsth', hhih, hep', hsbv', hsbp', hexcl', hshd'⟩

public theorem bind_borrowed_step_invs {rt : BitVec 64} {rf0 rf : RcFrame}
    {σ0 σ : HState} {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv}
    {x src : Nat} {ty : LcTy} {p? : Option Nat} {pers : Bool}
    {v_src : RcVar} {bv_src : BitVec 64} {o_src : LcnfObj}
    {pv : PVal} {bv : BitVec 64}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hno : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hep : EntryPres rf0 σ0 rf σ) (hsbp : SharedBoolPreds rf.ctx)
    (hexcl : ExclCtorHeap rf) (hshd : ShadowOk sm rf.ctx ρP rf.envP)
    (hfr : binderFreshOwned rf.ctx x = true)
    (hty : ty.needsRc = true)
    (hpb : rf.ctx.projBacking src = Except.ok (p?, pers))
    (hgsrc : rf.ctx.get? src = some v_src) (hns_src : ¬v_src.ty.isScalar = true)
    (hsrch : rf.envH src = some (v_src.ty, Word.i64 bv_src))
    (hosrc : o_src ∈ σ.objs) (hoasrc : o_src.addr = bv_src)
    (hrep : ValRep ty pv (Word.i64 bv) σ.objs)
    (hch : bv &&& 1#64 = 0#64 → bv ∈ o_src.childFields) :
    let ctx' := rf.ctx.bindBorrowed x ty p? pers
    let rf' : RcFrame := {
      ctx := ctx', envP := rf.envP.set x pv, envH := rf.envH.set x ty (Word.i64 bv),
      extH := rf.extH, ghostH := rf.ghostH }
    RcInv rt rf' σ ∧ CleanVars ctx' ∧ ParentsOwned ctx' ∧ NoRcCorrect ctx' ∧
      ParentChildBacked rf' σ.objs ∧ SharedTargetsHeap rf' ∧
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ.objs ∧ EntryPres rf0 σ0 rf' σ ∧
      SharedBoolVars ctx' ∧ SharedBoolPreds ctx' ∧ ExclCtorHeap rf' ∧
      ShadowOk (sm.filter (fun e => e.1 != x)) ctx' (ρP.set x pv) rf'.envP := by
  intro ctx' rf'
  have hnd : (rf.ctx.vars.map RcVar.id).Nodup := hinv.2.1
  have hwf_all : ∀ o ∈ σ.objs, o.Wf := fun o ho => hinv.1.1.2.1 o ho
  have hclosed := hinv.1.1.2.2.1
  have hnodup_objs := hinv.1.2
  have hsound := hinv.2.2.1
  have hrc := rcInv_bind_borrowed hinv hclean hfr ty hty hpb hgsrc hns_src hsrch hosrc hoasrc
    hrep hch
  have hpo' := parentsOwned_bindBorrowed hnd hpo hclean hfr ty hpb
  have hno' := noRcCorrect_bindBorrowed hnd hno x ty p? pers
  let vx : RcVar := {
    id := x, ty := ty, noRc := !ty.needsRc,
    persistent := if (!ty.needsRc) = true then false else pers,
    borrowed := !(!ty.needsRc) && !pers,
    parent? := if (!ty.needsRc || pers) = true then none else p? }
  have hl_src : v_src.isLive = true := by
    simp only [RcCtx.projBacking, hgsrc] at hpb
    cases hl : v_src.isLive <;> simp [hl] at hpb ⊢
  have hpar_ne : vx.parent? ≠ some x := by
    intro hp_eq
    have hsrc_ne : src ≠ x := by
      intro heq; subst heq
      simp only [binderFreshOwned, Bool.and_eq_true, hgsrc, hl_src, Bool.not_true] at hfr
      simp at hfr
    have hpu : (if (!ty.needsRc || pers) = true then none else p?) = some x := hp_eq
    split at hpu
    · cases hpu
    · simp only [RcCtx.projBacking, hgsrc, hl_src, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte] at hpb
      by_cases hvp : v_src.persistent = true
      · simp [hvp, pure, Except.pure, Except.ok.injEq] at hpb
        rw [← hpb.1] at hpu; cases hpu
      · simp only [hvp, Bool.false_eq_true, ↓reduceIte] at hpb
        by_cases hvb : v_src.borrowed = true
        · simp only [hvb, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hpb
          have hpb1 : v_src.parent? = p? := congrArg Prod.fst hpb
          rw [← hpb1] at hpu
          simp only [binderFreshOwned, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hfr
          exact hfr.1.1 v_src (RcCtx.get?_mem hgsrc).1 hpu
        · simp only [hvb, Bool.false_eq_true, ↓reduceIte] at hpb
          split at hpb <;> simp [pure, Except.pure, Except.ok.injEq] at hpb
          · rw [← hpb.1] at hpu; cases hpu; exact hsrc_ne rfl
          · rw [← hpb.1] at hpu; cases hpu
  have hev_src : bv_src &&& 1#64 = 0#64 := by
    have howf := hwf_all o_src hosrc
    have hmod := hoasrc ▸ howf.2.1
    apply BitVec.eq_of_toNat_eq
    have hmod1 : (1#64).toNat = 1 := rfl
    have hmod0 : (0#64).toNat = 0 := rfl
    simp only [BitVec.toNat_and, hmod1, hmod0]
    have hband := Nat.and_one_is_mod bv_src.toNat
    omega
  have hpcb' : ParentChildBacked rf' σ.objs := by
    apply parentChildBacked_bindBorrowed hnd hpcb hfr (v := vx) rfl hpar_ne
    intro p hp hev
    change (if (!ty.needsRc || pers) = true then none else p?) = some p at hp
    have hps_false : pers = false := by cases pers <;> simp [hty] at hp ⊢
    subst hps_false
    simp only [hty, Bool.not_true, Bool.false_or] at hp
    simp only [RcCtx.projBacking, hgsrc, hl_src, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte] at hpb
    by_cases hvp : v_src.persistent = true
    · simp [hvp, pure, Except.pure, Except.ok.injEq] at hpb
    · simp only [hvp, Bool.false_eq_true, ↓reduceIte] at hpb
      have hsrc_m := (RcCtx.get?_mem hgsrc).1
      have hsrc_id := (RcCtx.get?_mem hgsrc).2
      have hno_src : v_src.noRc = false := by
        cases h : v_src.noRc
        · rfl
        · have := (hclean v_src hsrc_m).1.1 h
          by_cases hvb : v_src.borrowed = true
          · simp [hvb] at this
          · simp only [hvb, Bool.false_eq_true, ↓reduceIte, this.2.1] at hpb
            simp [pure, Except.pure, Except.ok.injEq] at hpb
            rw [← hpb] at hp; cases hp
      by_cases hvb : v_src.borrowed = true
      · simp only [hvb, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hpb
        by_cases hrc0 : o_src.rc = 0#32
        · obtain ⟨q, hq, hqa, hqrc0⟩ := hsound.1 o_src hosrc hrc0 bv (hch hev) hev
          exact Or.inl (Or.inl ⟨q, hq, hqa, hqrc0⟩)
        · rcases hpcb v_src hsrc_m hl_src hno_src (by simp [hvp]) hvb p
              ((congrArg Prod.fst hpb).trans hp)
              bv_src (hsrc_id ▸ hsrch) hev_src with hbk | ⟨wp, o_p, hwp, hpa, hopm, o_mid, hom_m,
                hreach_mid, hcf_mid⟩
          · obtain ⟨t, ht, hta⟩ := hclosed o_src hosrc bv (hch hev) hev
            by_cases htrc0 : t.rc = 0#32
            · exact Or.inl (Or.inl ⟨t, ht, hta, htrc0⟩)
            · rcases hbk with ⟨q, hq, hqa, hqrc0⟩ | ⟨r, hr, hrr⟩
              · exfalso
                have heq := obj_eq_of_addr_nodup hnodup_objs hosrc hq (hoasrc.trans hqa.symm)
                rw [heq] at hrc0; exact hrc0 hqrc0
              · exact Or.inl (Or.inr ⟨r, hr, NonPersistReach.step hrr
                  ⟨o_src, hosrc, hoasrc, hch hev⟩ hev ⟨t, ht, hta, htrc0⟩⟩)
          · exact Or.inr ⟨wp, o_p, hwp, hpa, hopm, o_src, hosrc,
              NonPersistReach.step hreach_mid ⟨o_mid, hom_m, rfl, hoasrc.symm ▸ hcf_mid⟩
                (hoasrc ▸ hev_src) ⟨o_src, hosrc, rfl, hrc0⟩, hch hev⟩
      · simp only [hvb, Bool.false_eq_true, ↓reduceIte] at hpb
        split at hpb <;> simp [pure, Except.pure, Except.ok.injEq] at hpb
        · rw [← hpb] at hp; injection hp with hp'; subst hp'
          by_cases hrc0 : o_src.rc = 0#32
          · obtain ⟨q, hq, hqa, hqrc0⟩ := hsound.1 o_src hosrc hrc0 bv (hch hev) hev
            exact Or.inl (Or.inl ⟨q, hq, hqa, hqrc0⟩)
          · exact Or.inr ⟨(v_src.ty, Word.i64 bv_src), o_src, hsrch,
              by simp [Word.toBV64?, Word.i64, hoasrc], hosrc,
              o_src, hosrc, NonPersistReach.refl ⟨o_src, hosrc, rfl, hrc0⟩, hch hev⟩
        · rw [← hpb] at hp; cases hp
  have hsth' : SharedTargetsHeap rf' :=
    sharedTargetsHeap_put_fresh hnd hsth hfr (v := vx) rfl (fun q hq => hq)
  have hep' : EntryPres rf0 σ0 rf' σ :=
    entryPres_bindBorrowed hnd hinv.2.2.1 hwf_all hinv.1.2 hfr (v := vx) rfl
      (pv := pv) hgsrc hns_src hsrch hosrc hoasrc hch hep
  have hsbp' : SharedBoolPreds (rf.ctx.put vx) := sharedBoolPreds_put_fresh hnd hsbp
    (fun q hq => (binderFreshOwned_mem_false hfr q hq).1)
  have hsbv' := sharedBoolPreds_vars hsbp'
  have hexcl' : ExclCtorHeap rf' := exclCtorHeap_put_nonExcl hnd hexcl (vx := vx) rfl (by simp [vx])
  have hshd' := shadowOk_put_same hnd hshd (vx := vx) rfl (pv := pv)
  exact ⟨hrc.1, hrc.2, hpo', hno', hpcb', hsth', hhih, hep', hsbv', hsbp', hexcl', hshd'⟩

public theorem box_fresh_alloc_step_invs {rt : BitVec 64} {rf0 rf : RcFrame}
    {σ0 σ : HState} {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv}
    {x : Nat} {ty : LcTy} {bv : BitVec 64} {p : BitVec 64} {st' : RtC0State}
    {rem wr rcr : Nat}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hno : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hep : EntryPres rf0 σ0 rf σ) (hsbp : SharedBoolPreds rf.ctx)
    (hexcl : ExclCtorHeap rf) (hshd : ShadowOk sm rf.ctx ρP rf.envP)
    (hres : ResStateInv σ rem wr rcr) (hrem : 16 ≤ rem) (hwr : 1 ≤ wr)
    (hfr : binderFreshOwned rf.ctx x = true)
    (hty_nrc : ty.needsRc = true) (hty_nt : ty ≠ LcTy.tagged)
    (hp_nz : p ≠ 0#64) (hp_al : p.toNat % 8 = 0)
    (hp_fr : ∀ o ∈ σ.objs, o.addr ≠ p)
    (hmeta : st'.PreservesMeta σ.st) (hrem_lb : σ.st.rem - 16 ≤ st'.rem) :
    let newObj : LcnfObj := {
      addr := p, rc := 1#32, csSz := 16, other := 0, tag := 0,
      scalarData := writeNatLE bv.toNat 8 }
    let σ' : HState := { st := st', objs := newObj :: σ.objs, scr := σ.scr, scrLimbs := σ.scrLimbs }
    let ctx' := rf.ctx.bindOwned x ty true
    let rf' : RcFrame := {
      ctx := ctx', envP := rf.envP.set x (PVal.bits 64 bv),
      envH := rf.envH.set x ty (Word.i64 p), extH := rf.extH, ghostH := rf.ghostH }
    RcInv rt rf' σ' ∧ CleanVars ctx' ∧ ParentsOwned ctx' ∧ NoRcCorrect ctx' ∧
      ParentChildBacked rf' σ'.objs ∧ SharedTargetsHeap rf' ∧
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs ∧ EntryPres rf0 σ0 rf' σ' ∧
      SharedBoolVars ctx' ∧ SharedBoolPreds ctx' ∧ ExclCtorHeap rf' ∧
      ShadowOk (sm.filter (fun e => e.1 != x)) ctx' (ρP.set x (PVal.bits 64 bv)) rf'.envP ∧
      ResStateInv σ' (rem - 16) (wr - 1) rcr := by
  intro newObj σ' ctx' rf'
  have hwf_all : ∀ o ∈ σ.objs, o.Wf := fun o ho => hinv.1.1.2.1 o ho
  have hnd : (rf.ctx.vars.map RcVar.id).Nodup := hinv.2.1
  have hbn : BigNumRtWf rt st' σ.scr σ.scrLimbs :=
    bigNumRtWf_of_preservesMeta hinv.1.1.1 hmeta
  have hnew_wf : newObj.Wf := by
    dsimp only [newObj]
    refine ⟨hp_nz, hp_al, show 0 ≤ (1#32).toInt from by decide,
      show (16 : Nat) < 65536 from by decide, show (0 : Nat) < 256 from by decide,
      show (0 : Nat) < 256 from by decide, ?_, ?_, ?_, ?_⟩ <;>
      simp [LcnfObj.totalBytes, closureTag, arrayTag, sarrayTag, stringTag, mpzTag,
        rtMinObjBytes, rtMaxObjBytes, writeNatLE_length] <;> try omega
  have hch_mem : ∀ f ∈ newObj.childFields, f &&& 1#64 = 0#64 → ∃ q ∈ σ.objs, q.addr = f := by
    intro f hf; simp [newObj, LcnfObj.childFields] at hf
  have hno_self : ¬newObj.addr ∈ newObj.childFields := by
    simp [newObj, LcnfObj.childFields]
  have hty_ns : ¬ty.isScalar = true := by
    cases ty <;> simp_all [LcTy.isScalar, LcTy.needsRc]
  have hrep : ValRep ty (PVal.bits 64 bv) (Word.i64 p) σ'.objs := by
    simp only [ValRep, hty_ns, Bool.false_eq_true, ↓reduceIte]
    refine ⟨p, rfl, ?_, fun _ => ?_, fun h => absurd h hty_nt⟩
    · rw [ObjRep.eq_2]
      exact Or.inr ⟨rfl, newObj, List.mem_cons_self, rfl, hnew_wf, rfl, rfl, rfl⟩
    · apply BitVec.eq_of_toNat_eq
      have hmod1 : (1#64).toNat = 1 := rfl
      have hmod0 : (0#64).toNat = 0 := rfl
      simp only [BitVec.toNat_and, hmod1, hmod0]
      have hband := Nat.and_one_is_mod p.toNat
      omega
  have hfab := rcInv_fresh_alloc_bind hinv hclean hhih hres hrem hwr hnew_wf rfl hp_fr
    hch_mem hno_self hrem_lb (by simp [RtC0State.workCap, hmeta.2.2.2.2.2.1]) hbn (fun a ha => ha)
    (fun o ho hrc => by simp [newObj, LcnfObj.childFields])
    (fun b hb =>
      match hb with
      | Or.inl ⟨q, hq, hqa, hqrc0⟩ => Or.inl ⟨q, List.mem_cons_of_mem newObj hq, hqa, hqrc0⟩
      | Or.inr ⟨r, hr, hrr⟩ => Or.inr ⟨r, hr, nonPersistReach_mono_rc_pos
          (fun o ho _ => ⟨o, List.mem_cons_of_mem newObj ho, rfl, rfl, id,
            fun h0 h => by rw [h] at h0; simp at h0⟩) hwf_all hrr⟩)
    hfr ty hty_nrc true hrep
  have hpo' : ParentsOwned ctx' := parentsOwned_bindOwned hnd hpo hfr ty true false false
  have hno' : NoRcCorrect ctx' := noRcCorrect_bindOwned hnd hno x ty true false false
  let vx : RcVar := {
    id := x, ty := ty, noRc := !ty.needsRc,
    persistent := if (!ty.needsRc) = true then false else false,
    owned := if (!ty.needsRc || false) = true then 0 else 1,
    excl := if (!ty.needsRc || false) = true then false else true,
    resetTok := if (!ty.needsRc || false) = true then false else false }
  have hpcb' : ParentChildBacked rf' σ'.objs := by
    apply parentChildBacked_bindFreshOwned hnd hclean hwf_all hinv.2.2.2.1 hpo hpcb hfr
      (v := vx) rfl rfl (roots := localHandles rf.ctx rf.envH)
    · intro pv0 hpv0 hno0 hps0 hown0 bp hbp hev_bp
      have hc := localHandles_count_eq_add hnd rf.envH hpv0 bp
      have hrt0 : pv0.resetTok = false := (hclean pv0 hpv0).2.2.2.2
      have hown0_ne : (pv0.owned == 0) = false := by simp; omega
      have hvh : varHandles rf.envH pv0 = List.replicate pv0.owned bp := by
        simp [varHandles, hno0, hps0, hrt0, hown0_ne, hbp, Word.toBV64?, Word.i64, hev_bp]
      rw [← List.count_pos_iff, hc, hvh, List.count_replicate]
      simp only [beq_self_eq_true, ↓reduceIte]; omega
    · intro o ho howf _; exact ⟨o, List.mem_cons_of_mem newObj ho, objDataEq_refl o howf, id⟩
    · intro a ha
      rcases ha with ⟨q, hq, hqa, hqrc0⟩ | ⟨r, hr, hrr⟩
      · exact Or.inl ⟨q, List.mem_cons_of_mem newObj hq, hqa, hqrc0⟩
      · exact Or.inr ⟨r, hr, nonPersistReach_mono_rc_pos
          (fun o ho _ => ⟨o, List.mem_cons_of_mem newObj ho, rfl, rfl, id,
            fun h0 h => by rw [h] at h0; simp at h0⟩) hwf_all hrr⟩
  have hsth' : SharedTargetsHeap rf' :=
    sharedTargetsHeap_put_fresh hnd hsth hfr (v := vx) rfl (fun p hp => hp)
  have hep' : EntryPres rf0 σ0 rf' σ' :=
    entryPres_freshAlloc hnd hwf_all hwf_all hnew_wf rfl hp_fr
      (fun a _ _ => by simp [newObj, LcnfObj.childFields]) hmeta (v := vx) rfl
      (pv := PVal.bits 64 bv) (fun a ha => ha) (fun _ => Nat.le_refl _) hep
  have hsbp' : SharedBoolPreds (rf.ctx.put vx) := sharedBoolPreds_put_fresh hnd hsbp
    (fun p hp => (binderFreshOwned_mem_false hfr p hp).1)
  have hsbv' := sharedBoolPreds_vars hsbp'
  have hexcl' : ExclCtorHeap rf' := exclCtorHeap_put_notCtor hnd hexcl (vx := vx) rfl
    (fun _ _ _ h => by cases h)
  have hshd' := shadowOk_put_same hnd hshd (vx := vx) rfl (pv := PVal.bits 64 bv)
  exact ⟨hfab.1, hfab.2.1, hpo', hno', hpcb', hsth', hfab.2.2.1, hep', hsbv', hsbp',
    hexcl', hshd', hfab.2.2.2.1⟩

private theorem nonPersistRefs_eq_zero_of_all {objs : List LcnfObj} {a : BitVec 64}
    (h : ∀ q ∈ objs, q.rc ≠ 0#32 → ¬a ∈ q.childFields) : nonPersistRefs objs a = 0 := by
  induction objs with
  | nil => simp [nonPersistRefs]
  | cons q rest ih =>
    rw [nonPersistRefs_cons, ih (fun r hr => h r (List.mem_cons_of_mem q hr))]
    by_cases hq : q.rc = 0#32
    · simp [hq]
    · simp [hq, List.count_eq_zero.mpr (h q List.mem_cons_self hq)]

private theorem mem_frameHandles_put_fresh {ctx : RcCtx} {envH : HValEnv}
    {extH ghostH : List (BitVec 64)} {x : Nat} {vx : RcVar} {w : Word}
    (hnd : (ctx.vars.map RcVar.id).Nodup) (hfr : binderFreshOwned ctx x = true)
    (hxid : vx.id = x) {r : BitVec 64}
    (hr : r ∈ localHandles ctx envH ++ extH ++ ghostH) :
    r ∈ localHandles (ctx.put vx) (envH.set x vx.ty w) ++ extH ++ ghostH := by
  simp only [List.mem_append] at hr ⊢
  rcases hr with (h1 | h2) | h3
  · left; left
    have hperm := (localHandles_put_perm hnd (envH.set x vx.ty w) vx).count_eq r
    have hlex : localHandlesExcept ctx (envH.set x vx.ty w) x =
        localHandlesExcept ctx envH x :=
      localHandlesExcept_congr_env x (fun y hy => by simp [HValEnv.set, hy])
    have hfr_p := (localHandlesExcept_fresh_perm (envH := envH) hnd hfr).count_eq r
    rw [← List.count_pos_iff] at h1 ⊢
    rw [List.count_append, hxid, hlex] at hperm
    omega
  · left; right; exact h2
  · right; exact h3

private theorem count_fields_le_applyArgsHandles {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) {as : List LcArg} {bs : List Bool}
    (hns : argsNonScalar rf.ctx as = true)
    (hbs : bs = List.replicate as.length false)
    {ctx1 : RcCtx} (ha : rf.ctx.applyArgs as bs = Except.ok ctx1) :
    ∀ {bvs : List (BitVec 64)},
      rf.envH.evalObjArgs as = some bvs →
      (∀ f ∈ applyArgsHandles rf as bs, f ∈ bvs) ∧
      (∀ o ∈ σ.objs, o.Wf → 0 < o.rc.toInt →
        List.count o.addr bvs = List.count o.addr (applyArgsHandles rf as bs)) ∧
      (∀ f ∈ bvs, f = 1#64 ∨ ∃ vz ∈ rf.ctx.vars,
        vz.isLive = true ∧ ¬vz.ty.isScalar = true ∧
        rf.envH vz.id = some (vz.ty, Word.i64 f)) := by
  intro bvs hev
  have hwf_all := hinv.1.1.2.1
  have hnodup_o := hinv.1.2
  have hvars := hinv.2.2.2.1
  have hnd0 := hinv.2.1
  subst hbs
  have hgen : ∀ (ctxCur : RcCtx) (as' : List LcArg),
      (ctxCur.vars.map RcVar.id).Nodup →
      (∀ z v1, ctxCur.get? z = some v1 → ∃ v0, rf.ctx.get? z = some v0 ∧
        v0.ty = v1.ty ∧ v0.noRc = v1.noRc ∧ v0.persistent = v1.persistent ∧
        (v1.isLive = true → v0.isLive = true)) →
      argsNonScalar ctxCur as' = true →
      ctxCur.applyArgs as' (List.replicate as'.length false) = Except.ok ctx1 →
      ∀ {bvs' : List (BitVec 64)}, rf.envH.evalObjArgs as' = some bvs' →
      (∀ f ∈ applyArgsHandles rf as' (List.replicate as'.length false), f ∈ bvs') ∧
      (∀ o ∈ σ.objs, o.Wf → 0 < o.rc.toInt →
        List.count o.addr bvs' =
          List.count o.addr (applyArgsHandles rf as' (List.replicate as'.length false))) ∧
      (∀ f ∈ bvs', f = 1#64 ∨ ∃ vz ∈ rf.ctx.vars,
        vz.isLive = true ∧ ¬vz.ty.isScalar = true ∧
        rf.envH vz.id = some (vz.ty, Word.i64 f)) := by
    intro ctxCur as' hndCur hrel hns' ha' bvs' hev'
    induction as' generalizing ctxCur bvs' with
    | nil =>
      simp only [HValEnv.evalObjArgs.eq_1, Option.some.injEq] at hev'
      subst hev'
      exact ⟨fun f hf => by simp [applyArgsHandles.eq_1] at hf,
        fun _ _ _ _ => by simp [applyArgsHandles.eq_1], fun _ hf => by cases hf⟩
    | cons a as' ih =>
      simp only [HValEnv.evalObjArgs.eq_2] at hev'
      simp only [List.length_cons, List.replicate_succ] at ha'
      rw [RcCtx.applyArgs.eq_2] at ha'
      simp only [Bool.false_eq_true, ↓reduceIte] at ha'
      cases hca : ctxCur.consumeArg a with
      | error e => simp [bind, Except.bind, hca] at ha'
      | ok ctxMid =>
        simp only [bind, Except.bind, hca] at ha'
        cases ha1 : (rf.envH.evalArgAt a LcTy.tobject).bind Word.toBV64? with
        | none => simp [ha1] at hev'
        | some bv =>
          cases ha2 : rf.envH.evalObjArgs as' with
          | none => simp [ha1, ha2] at hev'
          | some bvs'' =>
            simp only [ha1, ha2, Option.some.injEq] at hev'
            subst hev'
            have hns1 : argsNonScalar ctxCur [a] = true ∧ argsNonScalar ctxCur as' = true := by
              simp only [argsNonScalar, List.all_cons, Bool.and_eq_true] at hns'
              have hns_a : argsNonScalar ctxCur [a] = true := by
                simp only [argsNonScalar, List.all_cons, List.all_nil, Bool.and_true]
                exact hns'.1
              exact ⟨hns_a, hns'.2⟩
            have hndMid : (ctxMid.vars.map RcVar.id).Nodup := by
              cases a with
              | erased =>
                simp only [RcCtx.consumeArg, pure, Except.pure, Except.ok.injEq] at hca
                subst hca; exact hndCur
              | var z => exact consumeVar_nodup hndCur hca
            have hprops : (∀ z, Option.map RcVar.ty (ctxMid.get? z) =
                  Option.map RcVar.ty (ctxCur.get? z) ∧
                  (Option.map RcVar.isLive (ctxMid.get? z) = some true →
                    Option.map RcVar.isLive (ctxCur.get? z) = some true)) ∧
                (∀ p, p ∈ ctxMid.sharedPreds → p ∈ ctxCur.sharedPreds) ∧
                (∀ z, (ctxCur.get? z).isSome = true → (ctxMid.get? z).isSome = true) ∧
                (∀ u ∈ ctxMid.vars, ∃ u0 ∈ ctxCur.vars, u.id = u0.id ∧ u.ty = u0.ty ∧
                  (u.isLive = true → u0.isLive = true) ∧ u.noRc = u0.noRc ∧
                  u.persistent = u0.persistent ∧ (u.excl = true → u0.excl = true) ∧
                  (u.parent? = u0.parent? ∨ u.parent? = none)) := by
              cases a with
              | erased =>
                simp only [RcCtx.consumeArg, pure, Except.pure, Except.ok.injEq] at hca
                subst hca
                exact ⟨fun _ => ⟨rfl, id⟩, fun _ h => h, fun _ h => h,
                  fun u hu => ⟨u, hu, rfl, rfl, id, rfl, rfl, id, Or.inl rfl⟩⟩
              | var z => exact consumeVar_ctx_props hndCur hca
            have hrelMid : ∀ z v1, ctxMid.get? z = some v1 → ∃ v0, rf.ctx.get? z = some v0 ∧
                v0.ty = v1.ty ∧ v0.noRc = v1.noRc ∧ v0.persistent = v1.persistent ∧
                (v1.isLive = true → v0.isLive = true) := by
              intro z v1 hgz1
              obtain ⟨u0, hu0, hid, hty, hl0, hno, hps, _, _⟩ :=
                hprops.2.2.2 v1 (RcCtx.get?_mem hgz1).1
              have hgu0 : ctxCur.get? z = some u0 := by
                have h := (RcCtx.mem_get?_iff hndCur).mpr hu0
                rwa [← hid, (RcCtx.get?_mem hgz1).2] at h
              obtain ⟨v0, hgv0, hty0, hno0, hps0, hl_top⟩ := hrel z u0 hgu0
              exact ⟨v0, hgv0, hty0.trans hty.symm, hno0.trans hno.symm, hps0.trans hps.symm,
                fun h => hl_top (hl0 h)⟩
            have hnsMid : argsNonScalar ctxMid as' = true := by
              simp only [argsNonScalar, List.all_eq_true] at hns1 ⊢
              intro a' ha'
              cases a' with
              | erased => rfl
              | var id' =>
                have h0 := hns1.2 (.var id') ha'
                cases hg0 : ctxCur.get? id' with
                | none => simp [hg0] at h0
                | some u0 =>
                  simp only [hg0] at h0
                  have his := hprops.2.2.1 id' (by simp [hg0])
                  cases hg1 : ctxMid.get? id' with
                  | none => simp [hg1] at his
                  | some v1 =>
                    have hty_eq := (hprops.1 id').1
                    rw [hg1, hg0] at hty_eq
                    simp only [Option.map_some, Option.some.injEq] at hty_eq
                    dsimp only; rw [hg1]
                    simp [hty_eq, h0]
            have hih := ih ctxMid hndMid hrelMid hnsMid ha' ha2
            cases a with
            | erased =>
              simp only [List.length_cons, List.replicate_succ]
              simp only [applyArgsHandles.eq_2, Bool.false_eq_true, ↓reduceIte, List.nil_append]
              simp only [HValEnv.evalArgAt, LcTy.toTTy, LcTy.width, LcTy.isScalar,
                Word.toBV64?, Option.bind_some, Option.some.injEq] at ha1
              refine ⟨fun f hf => List.mem_cons_of_mem bv (hih.1 f hf),
                fun o ho howf hrc => ?_, fun f hf => ?_⟩
              · have hne : bv ≠ o.addr := by
                  subst ha1; intro h; have hmod := howf.2.1; rw [← h] at hmod; simp at hmod
                rw [List.count_cons]
                simp [hne]
                exact hih.2.1 o ho howf hrc
              · rcases List.mem_cons.mp hf with rfl | hf'
                · exact Or.inl ha1.symm
                · exact hih.2.2 f hf'
            | var z =>
              simp only [List.length_cons, List.replicate_succ]
              simp only [applyArgsHandles.eq_3, Bool.false_eq_true, ↓reduceIte]
              cases hgzCur : ctxCur.get? z with
              | none => simp [RcCtx.consumeArg, RcCtx.consumeVar, hgzCur] at hca
              | some vzCur =>
                obtain ⟨vz0, hgz0, hty_z, hno_z, hps_z, hl_top⟩ := hrel z vzCur hgzCur
                have hns_z : ¬vz0.ty.isScalar = true := by
                  simp only [argsNonScalar, List.all_cons, List.all_nil, Bool.and_true,
                    hgzCur, Bool.not_eq_true'] at hns1
                  simp only [hty_z]
                  exact Bool.eq_false_iff.mp hns1.1
                have hvz_cur_live : vzCur.isLive = true := by
                  by_cases hnp : (vzCur.noRc || vzCur.persistent) = true
                  · simp [RcVar.isLive, hnp]
                  · simp only [RcCtx.consumeArg, RcCtx.consumeVar, hgzCur, hnp,
                      Bool.false_eq_true, ↓reduceIte] at hca
                    have h10 : (1 == 0) = false := rfl
                    simp only [h10, Bool.false_eq_true, ↓reduceIte] at hca
                    by_cases hlt : vzCur.owned < 1
                    · simp [hlt] at hca
                    · simp only [RcVar.isLive, hnp, Bool.false_or, Bool.or_eq_true,
                        decide_eq_true_eq]
                      left; omega
                have hvz_live := hl_top hvz_cur_live
                have hvar0 := hvars vz0 (RcCtx.get?_mem hgz0).1 hvz_live
                obtain ⟨_, wu0, _, hwu0, _, hnon0⟩ := hvar0
                obtain ⟨bv0, hweq0, hno_r, hps_r, _⟩ := hnon0 hns_z
                have hbv0_eq : bv0 = bv := by
                  have hgz0_id := (RcCtx.get?_mem hgz0).2
                  rw [hweq0, hgz0_id] at hwu0
                  simp only [HValEnv.evalArgAt, hwu0, Option.bind_eq_some_iff,
                    Word.toBV64?] at ha1
                  obtain ⟨w', hw', hbv'⟩ := ha1
                  split at hw'
                  · injection hw' with hw''; subst hw''; cases hbv'; rfl
                  · cases hw'
                have hweqh : rf.envH z = some (vz0.ty, Word.i64 bv) := by
                  have hgz0_id := (RcCtx.get?_mem hgz0).2
                  rw [hgz0_id, hweq0, hbv0_eq] at hwu0
                  exact hwu0
                constructor
                · intro f hf
                  rw [List.mem_append] at hf
                  rcases hf with hf1 | hf2
                  · rw [List.mem_cons]; left
                    simp only [consumeVarHandles, hgz0] at hf1
                    by_cases hnp : (vz0.noRc || vz0.persistent || (1 == 0)) = true
                    · simp only [hnp, ↓reduceIte, List.not_mem_nil] at hf1
                    · simp only [hnp, Bool.false_eq_true, ↓reduceIte, hweqh,
                        Word.toBV64?, Word.i64] at hf1
                      by_cases hev : (bv &&& 1#64 == 0#64) = true
                      · simp only [hev, ↓reduceIte, List.mem_replicate] at hf1
                        exact hf1.2
                      · simp [hev] at hf1
                  · exact List.mem_cons_of_mem bv (hih.1 f hf2)
                · constructor
                  · intro o ho howf hrc
                    rw [List.count_append, List.count_cons]
                    have hih_o := hih.2.1 o ho howf hrc
                    by_cases hbo : bv = o.addr
                    · have hmod := howf.2.1
                      have hev : bv &&& 1#64 = 0#64 := by
                        apply BitVec.eq_of_toNat_eq
                        have hmod1 : (1#64).toNat = 1 := rfl
                        have hmod0 : (0#64).toNat = 0 := rfl
                        simp only [BitVec.toNat_and, hmod1, hmod0]
                        have := Nat.and_one_is_mod bv.toNat
                        rw [hbo] at *; omega
                      have hno_f : vz0.noRc = false := by
                        cases h : vz0.noRc
                        · rfl
                        · exact absurd (hbv0_eq ▸ hev) (hno_r h)
                      have hps_f : vz0.persistent = false := by
                        cases h : vz0.persistent
                        · rfl
                        · obtain ⟨q, hq, hqa, hqrc⟩ := hps_r h (hbv0_eq ▸ hev)
                          have heq := obj_eq_of_addr_nodup hnodup_o ho hq
                            (hbo.symm.trans (hbv0_eq ▸ hqa.symm))
                          rw [heq, hqrc] at hrc; simp at hrc
                      have hc1 : List.count o.addr (consumeVarHandles rf z 1) = 1 := by
                        have h10 : (1 == 0) = false := rfl
                        have hev_o : o.addr &&& 1#64 = 0#64 := hbo ▸ hev
                        simp [consumeVarHandles, hgz0, hno_f, hps_f, h10, hweqh,
                          Word.toBV64?, Word.i64, hbo, hev_o]
                      simp only [hc1, hbo, beq_self_eq_true, ↓reduceIte]; omega
                    · have hc0 : List.count o.addr (consumeVarHandles rf z 1) = 0 := by
                        rw [List.count_eq_zero]
                        intro hmem
                        simp only [consumeVarHandles, hgz0] at hmem
                        by_cases hnp : (vz0.noRc || vz0.persistent || (1 == 0)) = true
                        · simp only [hnp, ↓reduceIte, List.not_mem_nil] at hmem
                        · simp only [hnp, Bool.false_eq_true, ↓reduceIte, hweqh,
                            Word.toBV64?, Word.i64] at hmem
                          by_cases hev : (bv &&& 1#64 == 0#64) = true
                          · simp only [hev, ↓reduceIte, List.mem_replicate] at hmem
                            exact hbo hmem.2.symm
                          · simp [hev] at hmem
                      have hbeq : (bv == o.addr) = false := beq_false_of_ne hbo
                      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, hc0]; omega
                  · intro f hf
                    rcases List.mem_cons.mp hf with rfl | hf'
                    · exact Or.inr ⟨vz0, (RcCtx.get?_mem hgz0).1, hvz_live, hns_z,
                        (RcCtx.get?_mem hgz0).2 ▸ hweqh⟩
                    · exact hih.2.2 f hf'
  exact hgen rf.ctx as hnd0 (fun z v1 hg => ⟨v1, hg, rfl, rfl, rfl, id⟩) hns ha hev

private theorem count_localHandlesExcept_put_fresh_ne {ctx : RcCtx}
    (hnd : (ctx.vars.map RcVar.id).Nodup)
    {envH : HValEnv} {x : Nat} (hfr : binderFreshOwned ctx x = true)
    {vx : RcVar} (hxid : vx.id = x)
    {w : Word} {p : BitVec 64} (hw_p : varHandles (envH.set x vx.ty w) vx = [p] ∨
      varHandles (envH.set x vx.ty w) vx = [])
    {s : Nat} (hne : s ≠ x) {vt : RcVar} (hgs : ctx.get? s = some vt)
    {a : BitVec 64} (hne_p : a ≠ p) :
    List.count a (localHandlesExcept (ctx.put vx) (envH.set x vx.ty w) s) =
      List.count a (localHandlesExcept ctx envH s) := by
  let envH' := envH.set x vx.ty w
  have hnd' : ((ctx.put vx).vars.map RcVar.id).Nodup := RcCtx.put_nodup hnd vx
  have hvt_mem := (RcCtx.get?_mem hgs).1
  have hvt_id := (RcCtx.get?_mem hgs).2
  have hvt_mem' : vt ∈ (ctx.put vx).vars :=
    (RcCtx.put_mem_iff hnd).mpr (Or.inr ⟨hvt_mem, by simpa [hxid, hvt_id] using hne⟩)
  have hc_all' := localHandles_count_eq_add hnd' envH' hvt_mem' a
  have hc_all := localHandles_count_eq_add hnd envH hvt_mem a
  have hc_put := localHandles_put_perm hnd envH' vx
  have hvh_vt : varHandles envH' vt = varHandles envH vt := by
    simp only [varHandles, envH', HValEnv.set, hvt_id, hne, ↓reduceIte]
  have hlex_x : List.count a (localHandlesExcept ctx envH' x) =
      List.count a (localHandles ctx envH) := by
    rw [localHandlesExcept_congr_env (envH := envH) (envH' := envH') x
      (fun y hy => by simp [envH', HValEnv.set, hy])]
    exact (localHandlesExcept_fresh_perm hnd hfr).count_eq a
  have hvh_vx : List.count a (varHandles envH' vx) = 0 := by
    rcases hw_p with h1 | h0
    · simp [envH', h1, hne_p.symm]
    · simp [envH', h0]
  have hc_p := hc_put.count_eq a
  rw [List.count_append, hxid, hvh_vx, Nat.zero_add, hlex_x] at hc_p
  rw [hvt_id] at hc_all' hc_all
  rw [hvh_vt] at hc_all'
  change List.count a (localHandlesExcept (ctx.put vx) envH' s) =
    List.count a (localHandlesExcept ctx envH s)
  omega

private theorem sharedPredInv_ctor_alloc {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    {as : List LcArg} {bs : List Bool} {ctx1 : RcCtx}
    (ha : rf.ctx.applyArgs as bs = Except.ok ctx1)
    (hsh_as : argsNoSharedTarget rf.ctx as bs = true)
    (hbs : bs = List.replicate as.length false)
    (hns : argsNonScalar rf.ctx as = true)
    {x : Nat} (hfr : binderFreshOwned rf.ctx x = true)
    {vx : RcVar} (hxid : vx.id = x)
    {p : BitVec 64} (hp_fr : ∀ o ∈ σ.objs, o.addr ≠ p)
    {newObj : LcnfObj} (hnrc : newObj.rc = 1#32)
    {bvs : List (BitVec 64)}
    (hncf : newObj.childFields = bvs) (hev : rf.envH.evalObjArgs as = some bvs)
    (hvh_x : varHandles (rf.envH.set x vx.ty (Word.i64 p)) vx = [p] ∨
      varHandles (rf.envH.set x vx.ty (Word.i64 p)) vx = [])
    {pv_h : PVal} :
    let rf' : RcFrame := {
      ctx := ctx1.put vx, envP := rf.envP.set x pv_h,
      envH := rf.envH.set x vx.ty (Word.i64 p), extH := rf.extH, ghostH := rf.ghostH }
    SharedPredInv rf' (newObj :: σ.objs) := by
  intro rf' pr hpr vb vt hgb hgt hbl hsno hsps
  have hstep1 := rcInv_applyArgs_step hinv hclean hpo ha hsh_as
  have hrc1 : RcInv rt {
      ctx := ctx1, envP := rf.envP, envH := rf.envH,
      extH := rf.extH, ghostH := rf.ghostH } σ := hstep1.2.1
  have hperm1 := hstep1.1
  have hfr1 := binderFreshOwned_applyArgs_nodup hfr hinv.2.1 ha
  have hne_pr := binderFreshOwned_mem_false hfr1 pr hpr
  have hnd1 : (ctx1.vars.map RcVar.id).Nodup := hrc1.2.1
  have hgb1 : ctx1.get? pr.1 = some vb := by
    rw [RcCtx.put_get? hnd1] at hgb
    simpa [hxid, beq_false_of_ne hne_pr.1] using hgb
  have hgt1 : ctx1.get? pr.2 = some vt := by
    rw [RcCtx.put_get? hnd1] at hgt
    simpa [hxid, beq_false_of_ne hne_pr.2] using hgt
  have hsp1 := hrc1.2.2.2.2 pr hpr vb vt hgb1 hgt1 hbl hsno hsps
  dsimp only at hsp1
  have hpenv_eq : (rf'.envP pr.1).bind PVal.tag? = (rf.envP pr.1).bind PVal.tag? := by
    simp [rf', PValEnv.set, hne_pr.1]
  have hhenv_eq : rf'.envH pr.2 = rf.envH pr.2 := by
    simp [rf', HValEnv.set, hne_pr.2]
  rw [hpenv_eq, hhenv_eq]
  have ⟨_, hle_bvs, _⟩ := count_fields_le_applyArgsHandles hinv hns hbs ha hev
  refine ⟨fun htag => ?_, fun htag hspos => ?_⟩
  · obtain ⟨bvs_t, henvt, hevt, hrest⟩ := hsp1.1 htag
    refine ⟨bvs_t, henvt, hevt, fun hspos => ?_⟩
    obtain ⟨hc0, o_s, ho_s, ho_sa, ho_src⟩ := hrest hspos
    have hne_p : bvs_t ≠ p := by rw [← ho_sa]; exact hp_fr o_s ho_s
    have hc_lex := count_localHandlesExcept_put_fresh_ne hnd1 hfr1 hxid hvh_x
      hne_pr.2 hgt1 hne_p
    have hwf_all := hinv.1.1.2.1
    have ho_pos : 0 < o_s.rc.toInt := by
      have howf := hwf_all o_s ho_s
      have hne0 : o_s.rc ≠ 0#32 := by
        intro h0; rw [h0] at ho_src; simp at ho_src; omega
      exact rc_toInt_pos_of_ne_zero howf.2.2.1 hne0
    have hprops := applyArgs_ctx_props hinv.2.1 ha
    have hpr_orig : pr ∈ rf.ctx.sharedPreds := hprops.2.1 pr hpr
    have hno_sh_tgt : (as.zip bs).all (fun p => if p.2 = true then true else
        match p.1 with | .erased => true | .var z => (z != pr.2)) = true := by
      simp only [argsNoSharedTarget, List.all_eq_true] at hsh_as ⊢
      intro q hq
      have hq' := hsh_as q hq
      cases hq2 : q.2
      · simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [hq2, Bool.false_eq_true, ↓reduceIte] at hq'
        cases hq1 : q.1 with
        | erased => simp
        | var z =>
          simp only [hq1, List.all_eq_true] at hq'
          have hq_pr := hq' pr hpr_orig
          simp only [bne_iff_ne] at hq_pr ⊢
          exact Ne.symm hq_pr
      · simp
    have hget_orig : ∃ vb0 vt0, rf.ctx.get? pr.1 = some vb0 ∧ vb0.isLive = true ∧
        rf.ctx.get? pr.2 = some vt0 := by
      have hm1 := (RcCtx.get?_mem hgb1).1
      obtain ⟨vb0, hvb0_m, hid1, _, hl1, _, _, _, _⟩ := hprops.2.2.2 vb hm1
      have hgb0 : rf.ctx.get? pr.1 = some vb0 := by
        have h := (RcCtx.mem_get?_iff hinv.2.1).mpr hvb0_m
        rwa [← hid1, (RcCtx.get?_mem hgb1).2] at h
      have hm2 := (RcCtx.get?_mem hgt1).1
      obtain ⟨vt0, hvt0_m, hid2, _, _, _, _, _, _⟩ := hprops.2.2.2 vt hm2
      have hgt0 : rf.ctx.get? pr.2 = some vt0 := by
        have h := (RcCtx.mem_get?_iff hinv.2.1).mpr hvt0_m
        rwa [← hid2, (RcCtx.get?_mem hgt1).2] at h
      exact ⟨vb0, vt0, hgb0, hl1 hbl, hgt0⟩
    obtain ⟨vb0, vt0, hgb0, hbl0, hgt0⟩ := hget_orig
    have hsame_vt := applyArgs_unconsumed_var_same hinv.2.1 hno_sh_tgt ha hgt0 hgt1
    have hvh_vt_eq : varHandles rf.envH vt = varHandles rf.envH vt0 := by
      simp only [varHandles, (RcCtx.get?_mem hgt1).2, (RcCtx.get?_mem hgt0).2,
        hsame_vt.1, hsame_vt.2.1, hsame_vt.2.2.1, hsame_vt.2.2.2.1]
    have hc_orig := (hinv.2.2.2.2 pr hpr_orig vb0 vt0 hgb0 hgt0 hbl0
      (hsame_vt.2.1 ▸ hsno) (hsame_vt.2.2.1 ▸ hsps)).1 htag
    obtain ⟨bvs_t0, henvt0, _, hrest0⟩ := hc_orig
    rw [henvt] at henvt0; injection henvt0 with htv0
    have hbvs_eq : bvs_t0 = bvs_t := by
      have h := congrArg Prod.snd htv0
      cases h; rfl
    rw [hbvs_eq] at hrest0
    obtain ⟨hc0_orig, _⟩ := hrest0 (hsame_vt.1 ▸ hspos)
    have hc_perm := hperm1.count_eq bvs_t
    have hc_add0 := localHandles_count_eq_add hinv.2.1 rf.envH (RcCtx.get?_mem hgt0).1 bvs_t
    have hc_add1 := localHandles_count_eq_add hnd1 rf.envH (RcCtx.get?_mem hgt1).1 bvs_t
    rw [(RcCtx.get?_mem hgt0).2] at hc_add0
    rw [(RcCtx.get?_mem hgt1).2, hvh_vt_eq] at hc_add1
    have hc_app0 : List.count bvs_t (applyArgsHandles rf as bs) = 0 := by
      simp only [List.count_append] at hc0_orig hc_perm ⊢; omega
    have hc_bvs : List.count bvs_t bvs = 0 := by
      have hle := hle_bvs o_s ho_s (hwf_all o_s ho_s) ho_pos
      rw [ho_sa] at hle; omega
    have hnpre_cons : nonPersistRefs (newObj :: σ.objs) bvs_t =
        nonPersistRefs σ.objs bvs_t + List.count bvs_t bvs := by
      have hrc_ne : ¬newObj.rc = 0#32 := by rw [hnrc]; decide
      rw [nonPersistRefs_cons]; simp only [hrc_ne, ↓reduceIte, hncf]; omega
    refine ⟨?_, o_s, List.mem_cons_of_mem newObj ho_s, ho_sa, ho_src⟩
    simp only [rf', List.count_append] at hc0 ⊢
    rw [hc_lex, hnpre_cons, hc_bvs]
    omega
  · obtain ⟨bvs_t, henvt, hevt, o_s, ho_s, ho_sa, horc⟩ := hsp1.2 htag hspos
    exact ⟨bvs_t, henvt, hevt, o_s, List.mem_cons_of_mem newObj ho_s, ho_sa, horc⟩

public theorem ctor_fresh_alloc_step_invs {rt : BitVec 64} {rf0 rf : RcFrame}
    {σ0 σ : HState} {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv}
    {x : Nat} {ty : LcTy} {ci : LcCtor} {as : List LcArg} {ctx1 : RcCtx}
    {pvs : List PVal} {bvs : List (BitVec 64)} {p : BitVec 64} {st' : RtC0State}
    {scal : List UInt8} {rem wr rcr : Nat}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hno : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hep : EntryPres rf0 σ0 rf σ) (hsbp : SharedBoolPreds rf.ctx)
    (hexcl : ExclCtorHeap rf) (hshd : ShadowOk sm rf.ctx ρP rf.envP)
    (hres : ResStateInv σ rem wr rcr) (hrem : ci.byteSize ≤ rem) (hwr : 1 ≤ wr)
    (hfr : binderFreshOwned rf.ctx x = true)
    (hty_nrc : ty.needsRc = true) (hty_nt : ty ≠ LcTy.tagged)
    (hns_ci : ¬ci.isScalar = true)
    (hcidx : ci.cidx ≤ 244) (hsize : ci.size < 256)
    (hmin : rtMinObjBytes ≤ ci.byteSize) (hmax : ci.byteSize < 65536)
    (hns_as : argsNonScalar rf.ctx as = true)
    (hsh_as : argsNoSharedTarget rf.ctx as (List.replicate as.length false) = true)
    (ha : rf.ctx.applyArgs as (List.replicate as.length false) = Except.ok ctx1)
    (hpvs_len : pvs.length = ci.size)
    (hbvs : rf.envH.evalObjArgs as = some bvs)
    (hobj_rep : objFieldsRep pvs bvs σ.objs)
    (hp_nz : p ≠ 0#64) (hp_al : p.toNat % 8 = 0)
    (hp_fr : ∀ o ∈ σ.objs, o.addr ≠ p)
    (hmeta : st'.PreservesMeta σ.st) (hrem_lb : σ.st.rem - ci.byteSize ≤ st'.rem)
    (hscal_len : scal.length = 8 * ci.usize + ci.ssize) :
    let newObj : LcnfObj := {
      addr := p, rc := 1#32, csSz := ci.byteSize, other := ci.size, tag := ci.cidx,
      fields := bvs, scalarData := scal }
    let σ' : HState := { st := st', objs := newObj :: σ.objs, scr := σ.scr, scrLimbs := σ.scrLimbs }
    let ctx' := ctx1.bindOwned x ty true
    let pvP := PVal.ctor ci.cidx pvs (List.replicate (8 * ci.usize + ci.ssize) 0)
    let pvH := PVal.ctor ci.cidx pvs scal
    let rf' : RcFrame := {
      ctx := ctx', envP := rf.envP.set x pvH, envH := rf.envH.set x ty (Word.i64 p),
      extH := rf.extH, ghostH := rf.ghostH }
    RcInv rt rf' σ' ∧ CleanVars ctx' ∧ ParentsOwned ctx' ∧ NoRcCorrect ctx' ∧
      ParentChildBacked rf' σ'.objs ∧ SharedTargetsHeap rf' ∧
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs ∧ EntryPres rf0 σ0 rf' σ' ∧
      SharedBoolVars ctx' ∧ SharedBoolPreds ctx' ∧ ExclCtorHeap rf' ∧
      ShadowOk (ctorBindMask x ci sm) ctx' (ρP.set x pvP) rf'.envP ∧
      ResStateInv σ' (rem - ci.byteSize) (wr - 1) rcr := by
  intro newObj σ' ctx' pvP pvH rf'
  have hwf_all : ∀ o ∈ σ.objs, o.Wf := fun o ho => hinv.1.1.2.1 o ho
  have hnodup_o := hinv.1.2
  have hnd0 := hinv.2.1
  have hstep1 := rcInv_applyArgs_step hinv hclean hpo ha hsh_as
  obtain ⟨hperm1, hinv1, hclean1, hpo1⟩ := hstep1
  have hnd1 := hinv1.2.1
  have hfr1 := binderFreshOwned_applyArgs_nodup hfr hnd0 ha
  have hno1 := noRcCorrect_applyArgs hnd0 hno as (List.replicate as.length false) ha
  have hpcb1 := parentChildBacked_applyArgs hnd0 hclean ha hpcb
  have hsth1 := sharedTargetsHeap_applyArgs hnd0 hsth ha
  have hhih1 : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs := hhih
  have hep1 := entryPres_applyArgs hnd0 hclean ha hep
  have hsbp1 : SharedBoolPreds ctx1 := by
    have h1 := sharedBool_applyArgs hnd0 (sharedBoolPreds_vars hsbp) hsbp ha
    exact h1.2
  have hexcl1 := exclCtorHeap_applyArgs hnd0 hexcl ha
  have hshd1 := shadowOk_applyArgs hnd0 hshd ha
  have hbvs_len : bvs.length = ci.size := (objFieldsRep_length hobj_rep).symm.trans hpvs_len
  have hnew_wf : newObj.Wf := by
    have hne245 : ci.cidx ≠ 245 := by omega
    have hne246 : ci.cidx ≠ 246 := by omega
    have hne248 : ci.cidx ≠ 248 := by omega
    have hne249 : ci.cidx ≠ 249 := by omega
    have hne250 : ci.cidx ≠ 250 := by omega
    have htotal_eq : newObj.totalBytes = ci.byteSize := by
      dsimp only [newObj]
      simp only [LcnfObj.totalBytes, arrayTag, sarrayTag, stringTag, mpzTag,
        hne246, hne248, hne249, hne250, ↓reduceIte, LcCtor.byteSize, Nat.add_assoc]
    refine ⟨hp_nz, hp_al, show 0 ≤ (1#32).toInt from by decide, hmax,
      by dsimp only [newObj]; omega, by dsimp only [newObj]; omega, ?_, ?_, ?_, ?_⟩
    · rw [htotal_eq]; exact hmin
    · rw [htotal_eq]
      have hmax_rt : (65536 : Nat) ≤ rtMaxObjBytes := by decide
      omega
    · rw [htotal_eq, LcCtor.byteSize]; omega
    · dsimp only [newObj]
      simp only [closureTag, arrayTag, sarrayTag, stringTag, mpzTag,
        hne245, hne246, hne248, hne249, hne250, ↓reduceIte,
        hbvs_len, hscal_len, LcCtor.byteSize]
      refine ⟨hcidx, trivial, ?_, ?_⟩ <;> omega
  have hbn := bigNumRtWf_of_preservesMeta hinv.1.1.1 hmeta
  have hne_pair : ¬(pvs = [] ∧ scal = []) := by
    rintro ⟨hp_nil, hs_nil⟩
    have hsz0 : ci.size = 0 := by rw [← hpvs_len, hp_nil]; rfl
    have hsc0 : 8 * ci.usize + ci.ssize = 0 := by rw [← hscal_len, hs_nil]; rfl
    have h0a : 8 * ci.usize = 0 := by omega
    have h0b : ci.ssize = 0 := by omega
    simp only [LcCtor.byteSize, hsz0, h0a, h0b, rtMinObjBytes] at hmin
    omega
  have hnew_cf : newObj.childFields = bvs := by
    simp [newObj, LcnfObj.childFields, hcidx]
  have hch_mem : ∀ f ∈ newObj.childFields, f &&& 1#64 = 0#64 → ∃ q ∈ σ.objs, q.addr = f := by
    intro f hf hev
    rw [hnew_cf] at hf
    obtain ⟨idx_f, hidx_f, hget_f⟩ := List.mem_iff_getElem.mp hf
    have hrep_f := objFieldsRep_getElem hobj_rep (hb := hidx_f)
      (hi := by rw [objFieldsRep_length hobj_rep]; exact hidx_f)
    rw [← hget_f]
    exact objRep_even_mem hrep_f (hget_f ▸ hev)
  have hres' : ResStateInv σ' (rem - ci.byteSize) (wr - 1) rcr :=
    resStateInv_fresh_alloc hres hrem hwr (newObj := newObj) rfl hrem_lb
      (scrLimbs' := σ.scrLimbs) (by simp [RtC0State.workCap, hmeta.2.2.2.2.2.1])
  have hheap' : HeapClean rt σ' := by
    apply heapClean_fresh_alloc hinv.1 hbn hnew_wf
      (show newObj.rc.toNat < 2 ^ 31 - 1 from by dsimp only [newObj]; decide) hp_fr
    · have := hres'.2.1; exact Nat.le_trans (Nat.le_add_right _ _) this
    · exact hch_mem
  have hty_ns : ¬ty.isScalar = true := by
    cases ty <;> simp_all [LcTy.isScalar, LcTy.needsRc]
  have hobj_rep' : objFieldsRep pvs bvs σ'.objs := by
    apply objFieldsRep_mono_pred (P := fun _ => True)
    · intro o ho howf _; exact ⟨o, List.mem_cons_of_mem newObj ho, objDataEq_refl o howf⟩
    · intro _ _ _ _ _ _ _; trivial
    · exact hobj_rep
    · intro _ _ _; trivial
  have hev_p : p &&& 1#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    have hmod1 : (1#64).toNat = 1 := rfl
    have hmod0 : (0#64).toNat = 0 := rfl
    simp only [BitVec.toNat_and, hmod1, hmod0]
    have := Nat.and_one_is_mod p.toNat; omega
  have hrep : ValRep ty pvH (Word.i64 p) σ'.objs := by
    simp only [ValRep, hty_ns, Bool.false_eq_true, ↓reduceIte]
    refine ⟨p, rfl, ?_, fun _ => hev_p, fun h => absurd h hty_nt⟩
    rw [ObjRep.eq_4]
    exact Or.inr ⟨hne_pair, newObj, List.mem_cons_self, rfl, hnew_wf, rfl, hcidx, rfl, hobj_rep'⟩
  let vx : RcVar := {
    id := x, ty := ty, noRc := !ty.needsRc,
    persistent := if (!ty.needsRc) = true then false else false,
    owned := if (!ty.needsRc || false) = true then 0 else 1,
    excl := if (!ty.needsRc || false) = true then false else true,
    resetTok := if (!ty.needsRc || false) = true then false else false }
  have hcv : CleanVar vx := by
    simpa [vx] using cleanVar_bindOwned x ty true false
  have hvh_vx : varHandles (rf.envH.set x vx.ty (Word.i64 p)) vx = [p] := by
    simp [varHandles, vx, hty_nrc, HValEnv.set, hev_p, Word.toBV64?, Word.i64]
  have hvarX : VarInv vx rf' σ'.objs := by
    intro _
    refine ⟨pvH, Word.i64 p, by dsimp only [rf']; simp [vx, PValEnv.set],
      by dsimp only [rf']; simp [vx, HValEnv.set], hrep, fun _ => ?_⟩
    refine ⟨p, rfl, fun h => by simp [vx, hty_nrc] at h, fun h => by simp [vx, hty_nrc] at h,
      fun _ => ⟨by simp [vx, hty_nrc], by simp [vx, hty_nrc], by simp [vx, hty_nrc],
        fun _ => ⟨newObj, List.mem_cons_self, rfl, rfl⟩⟩,
      fun _ _ h => by simp [vx] at h⟩
  have ⟨_, hle_bvs, hbvs_vars⟩ := count_fields_le_applyArgsHandles hinv hns_as rfl ha hbvs
  let rf1 : RcFrame := {
    ctx := ctx1, envP := rf.envP, envH := rf.envH, extH := rf.extH, ghostH := rf.ghostH }
  have hhs' : HandlesRcSound
      (varHandles (rf.envH.set x vx.ty (Word.i64 p)) vx ++
        localHandles ctx1 rf.envH ++ rf.extH ++ rf.ghostH) σ'.objs := by
    refine ⟨?_, ?_⟩
    · intro q hq hq0 f hf hevf
      rcases List.mem_cons.mp hq with rfl | hq_old
      · cases hq0
      · obtain ⟨t, ht, hta, htrc0⟩ := hinv.2.2.1.1 q hq_old hq0 f hf hevf
        exact ⟨t, List.mem_cons_of_mem newObj ht, hta, htrc0⟩
    · intro y hy hypos
      rcases List.mem_cons.mp hy with rfl | hy_old
      · have hno_in_bvs : ¬p ∈ bvs := by
          intro hmem
          by_cases hev_p2 : p &&& 1#64 = 0#64
          · obtain ⟨q, hq, hqa⟩ := hch_mem p (by rw [hnew_cf]; exact hmem) hev_p2
            exact hp_fr q hq hqa
          · exact hev_p2 hev_p
        have hno_in_old :
            List.count p (localHandles ctx1 rf.envH ++ rf.extH ++ rf.ghostH) = 0 := by
          rw [List.count_eq_zero]
          intro hmem
          simp only [List.mem_append] at hmem
          rcases hmem with (h1 | h2) | h3
          · obtain ⟨q, hq, hqa⟩ := handlesInHeap_localHandles hinv1 hclean1 p h1
            exact hp_fr q hq hqa
          · obtain ⟨q, hq, hqa⟩ := hhih p (List.mem_append.mpr (Or.inl h2))
            exact hp_fr q hq hqa
          · obtain ⟨q, hq, hqa⟩ := hhih p (List.mem_append.mpr (Or.inr h3))
            exact hp_fr q hq hqa
        have hno_in_objs : ∀ q ∈ σ.objs, q.rc ≠ 0#32 → ¬p ∈ q.childFields := by
          intro q hq _ hmem
          obtain ⟨t, ht, hta⟩ := hinv.1.1.2.2.1 q hq p hmem hev_p
          exact hp_fr t ht hta
        have hnew_rc_ne : newObj.rc ≠ 0#32 := by dsimp only [newObj]; decide
        have hna : newObj.addr = p := rfl
        have hnpre_new : nonPersistRefs (newObj :: σ.objs) p = 0 := by
          rw [nonPersistRefs_cons]
          split
          · exact absurd ‹_› hnew_rc_ne
          · simp [hnew_cf, List.count_eq_zero.mpr hno_in_bvs,
              nonPersistRefs_eq_zero_of_all hno_in_objs]
        have hc_vh : List.count p (varHandles (rf.envH.set x vx.ty (Word.i64 p)) vx) = 1 := by
          rw [hvh_vx]; simp
        have hrc1 : newObj.rc.toNat = 1 := rfl
        simp only [List.count_append] at hno_in_old ⊢
        rw [hna, hrc1, hc_vh, hnpre_new]
        omega
      · have hne_p : y.addr ≠ p := hp_fr y hy_old
        have hc_vh :
            List.count y.addr (varHandles (rf.envH.set x vx.ty (Word.i64 p)) vx) = 0 := by
          rw [hvh_vx, List.count_eq_zero]
          intro hm
          simp only [List.mem_singleton] at hm
          exact hne_p hm
        have hnew_rc_ne : newObj.rc ≠ 0#32 := by dsimp only [newObj]; decide
        have hnpre_y : nonPersistRefs (newObj :: σ.objs) y.addr =
            List.count y.addr bvs + nonPersistRefs σ.objs y.addr := by
          rw [nonPersistRefs_cons]
          split
          · exact absurd ‹_› hnew_rc_ne
          · rw [hnew_cf]
        have horig := hinv.2.2.1.2 y hy_old hypos
        have hperm_c := hperm1.count_eq y.addr
        have heq_bvs := hle_bvs y hy_old (hwf_all y hy_old) hypos
        simp only [frameHandles, List.count_append] at horig hperm_c ⊢
        rw [hc_vh, hnpre_y, heq_bvs]
        omega
  have hbk_frame :
      ∀ bv, Backed σ.objs (frameHandles rf1) bv → Backed σ'.objs (frameHandles rf') bv := by
    intro bv hbv
    refine backed_mono_rc_pos ?_ hwf_all ?_ hbv
    · intro o ho _
      exact ⟨o, List.mem_cons_of_mem newObj ho, rfl, rfl, id,
        fun h0 h => by rw [h] at h0; simp at h0⟩
    · intro r hr
      exact mem_frameHandles_put_fresh hnd1 hfr1 rfl hr
  have hbk_ext : ∀ bv, Backed σ.objs (rf1.extH ++ rf1.ghostH) bv →
      Backed σ'.objs (rf1.extH ++ rf1.ghostH) bv := by
    intro bv hbv
    refine backed_mono_rc_pos ?_ hwf_all (fun _ hr => hr) hbv
    intro o ho _
    exact ⟨o, List.mem_cons_of_mem newObj ho, rfl, rfl, id,
      fun h0 h => by rw [h] at h0; simp at h0⟩
  have hspi' : SharedPredInv rf' σ'.objs :=
    sharedPredInv_ctor_alloc hinv hclean hpo ha hsh_as rfl hns_as hfr rfl hp_fr
      (newObj := newObj) rfl hnew_cf hbvs (Or.inl hvh_vx)
  have hrc := rcInv_put_fresh hinv1 hclean1 hfr1 rfl hcv hheap'
    (fun o ho howf => ⟨o, List.mem_cons_of_mem newObj ho, objDataEq_refl o howf, rfl⟩)
    hvarX hhs' hbk_frame hbk_ext hspi'
  have hpo' : ParentsOwned ctx' := parentsOwned_bindOwned hnd1 hpo1 hfr1 ty true false false
  have hno' : NoRcCorrect ctx' := noRcCorrect_bindOwned hnd1 hno1 x ty true false false
  have hpcb' : ParentChildBacked rf' σ'.objs := by
    apply parentChildBacked_bindFreshOwned hnd1 hclean1 hwf_all hinv1.2.2.2.1 hpo1 hpcb1 hfr1
      rfl rfl (roots := localHandles ctx1 rf.envH)
    · intro pv0 hpv0 hno0 hps0 hown0 bp hbp hev_bp
      have hc := localHandles_count_eq_add hnd1 rf.envH hpv0 bp
      have hrt0 : pv0.resetTok = false := (hclean1 pv0 hpv0).2.2.2.2
      have hown0_ne : (pv0.owned == 0) = false := by simp; omega
      have hvh : varHandles rf.envH pv0 = List.replicate pv0.owned bp := by
        dsimp only at hbp
        simp [varHandles, hno0, hps0, hrt0, hown0_ne, hbp, Word.toBV64?, Word.i64, hev_bp]
      rw [← List.count_pos_iff, hc, hvh, List.count_replicate]
      simp only [beq_self_eq_true, ↓reduceIte]; omega
    · intro o ho howf _; exact ⟨o, List.mem_cons_of_mem newObj ho, objDataEq_refl o howf, id⟩
    · intro a ha_ext; exact hbk_ext a ha_ext
  have hsth' : SharedTargetsHeap rf' :=
    sharedTargetsHeap_put_fresh hnd1 hsth1 hfr1 rfl (fun q hq => hq)
  have hhih' : HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs :=
    fun a ha => let ⟨o, ho, hoa⟩ := hhih a ha; ⟨o, List.mem_cons_of_mem newObj ho, hoa⟩
  have hisol_cf : ∀ a, a ∈ rf0.extH ++ rf0.ghostH → IsolatedAddr a rf0 σ0.objs →
      ¬a ∈ newObj.childFields := by
    intro a ha_mem hisol0 ha_cf
    have hisol := (hep.2.1 a ha_mem hisol0).1
    obtain ⟨o_s, _, howf_s, haddr_s, _⟩ := hisol.2.2
    rw [hnew_cf] at ha_cf
    rcases hbvs_vars a ha_cf with h1 | ⟨vz, hvz_m, hvz_live, hvz_ns, hvz_h⟩
    · have hmod := howf_s.2.1
      rw [haddr_s, h1] at hmod
      simp at hmod
    · exact hisol.1 vz hvz_m hvz_live (by simp [hvz_ns]) (Word.i64 a) hvz_h
        (by simp [Word.toBV64?, Word.i64])
  have hep' : EntryPres rf0 σ0 rf' σ' :=
    entryPres_freshAlloc hnd1 hwf_all hwf_all hnew_wf rfl hp_fr
      hisol_cf hmeta rfl (pv := pvH) (fun _ h => h) (fun _ => Nat.le_refl _) hep1
  have hsbp' : SharedBoolPreds (ctx1.put vx) := sharedBoolPreds_put_fresh hnd1 hsbp1
    (v := vx) (fun q hq => (binderFreshOwned_mem_false hfr1 q hq).1)
  have hsbv' := sharedBoolPreds_vars hsbp'
  have hexcl' : ExclCtorHeap rf' := exclCtorHeap_put_ctor hnd1 hexcl1 rfl hev_p (pv := pvH)
  have hshd' : ShadowOk (ctorBindMask x ci sm) ctx' (ρP.set x pvP) rf'.envP :=
    shadowOk_bind_ctor hnd1 hshd1 (vx := vx) rfl hns_ci hpvs_len hscal_len
  exact ⟨hrc.1, hrc.2, hpo', hno', hpcb', hsth', hhih', hep', hsbv', hsbp', hexcl', hshd', hres'⟩

end BindWrappers

end LeanQbe.T.LeanLCNF.Sem
