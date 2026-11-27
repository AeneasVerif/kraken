module

public import LeanQbe.T.LeanLCNF.Sem.PerceusCases

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T

section CtxWeakensAndMerge

/-- Weakening relation from a branch context `ctxS` to a merged join-point context `ctxW`. -/
@[expose] public def CtxWeakens (ctxW ctxS : RcCtx) : Prop :=
  (ctxW.vars.map RcVar.id).Nodup ∧
  (ctxS.vars.map RcVar.id).Nodup ∧
  (∀ w ∈ ctxW.vars, ∃ v, v ∈ ctxS.vars ∧
    w.id = v.id ∧
    (w.noRc = false → w.ty.needsRc = true) ∧
    (w.borrowed = false → w.parent? = none) ∧
    w.noRc = v.noRc ∧ w.persistent = v.persistent ∧ w.owned = v.owned ∧
    (w.borrowed = true → v.borrowed = true ∧ v.parent? = w.parent?) ∧
    (w.excl = true → v.excl = true) ∧
    (v.resetTok = false → w.resetTok = false)) ∧
  (∀ p, p ∈ ctxW.sharedPreds → p ∈ ctxS.sharedPreds)

/-- `CtxWeakens` is reflexive when `Nodup`, `CleanVars`, and `NoRcCorrect` hold. -/
public theorem ctxWeakens_refl {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hc : CleanVars ctx) (hnr : NoRcCorrect ctx) : CtxWeakens ctx ctx := by
  refine ⟨hnd, hnd, fun w hw => ?_, fun _ hp => hp⟩
  exact ⟨w, hw, rfl, hnr w hw, (hc w hw).2.2.2.1, rfl, rfl, rfl,
    fun h => ⟨h, rfl⟩, id, id⟩

/-- `CtxWeakens` is transitive. -/
public theorem ctxWeakens_trans {c1 c2 c3 : RcCtx}
    (h12 : CtxWeakens c1 c2) (h23 : CtxWeakens c2 c3) : CtxWeakens c1 c3 := by
  refine ⟨h12.1, h23.2.1, fun w hw => ?_, fun p hp => h23.2.2.2 p (h12.2.2.2 p hp)⟩
  obtain ⟨v2, hv2, hid1, hnrw, hbp, hnr1, hp1, ho1, hbr1, hex1, hrt1⟩ := h12.2.2.1 w hw
  obtain ⟨v3, hv3, hid2, _, _, hnr2, hp2, ho2, hbr2, hex2, hrt2⟩ := h23.2.2.1 v2 hv2
  refine ⟨v3, hv3, hid1.trans hid2, hnrw, hbp, hnr1.trans hnr2, hp1.trans hp2,
    ho1.trans ho2, ?_, fun h => hex2 (hex1 h), fun h => hrt1 (hrt2 h)⟩
  intro hbw
  obtain ⟨hb2, hp2'⟩ := hbr1 hbw
  obtain ⟨hb3, hp3'⟩ := hbr2 hb2
  exact ⟨hb3, hp3'.trans hp2'⟩

private theorem except_str_throw_eq {α : Type} (s : String) :
    (throw s : Except String α) = Except.error s := rfl

private theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = Except.ok b) : ∃ a, x = Except.ok a ∧ f a = Except.ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private def mergePairVar (v1 v2 : RcVar) : RcVar :=
  let b := v1.borrowed && v2.borrowed && (v1.parent? == v2.parent?)
  let p? := if b = true then v1.parent? else none
  { id := v1.id, ty := v1.ty, noRc := v1.noRc, persistent := v1.persistent,
    owned := v1.owned, borrowed := b, parent? := p?,
    excl := v1.excl && v2.excl, resetTok := v1.resetTok && v2.resetTok }

private theorem mergeJp_loop_spec (c2 : RcCtx)
    (step : RcVar → List RcVar → Except String (ForInStep (List RcVar)))
    (hstep : ∀ v1 acc res, step v1 acc = Except.ok res ↔
      ∃ v2, c2.get? v1.id = some v2 ∧ v1.noRc = v2.noRc ∧
        v1.persistent = v2.persistent ∧ v1.owned = v2.owned ∧
        res = ForInStep.yield (acc ++ [mergePairVar v1 v2]))
    (xs acc : List RcVar) :
    ∀ merged, forIn xs acc step = Except.ok merged →
      merged.map RcVar.id = acc.map RcVar.id ++ xs.map RcVar.id ∧
      (∀ u, u ∈ merged ↔ u ∈ acc ∨ ∃ v1 v2, v1 ∈ xs ∧ c2.get? v1.id = some v2 ∧
        v1.noRc = v2.noRc ∧ v1.persistent = v2.persistent ∧ v1.owned = v2.owned ∧
        u = mergePairVar v1 v2) := by
  induction xs generalizing acc with
  | nil => intro merged hm; cases hm; simp
  | cons v1 rest ih =>
    intro merged hm
    simp only [List.forIn_cons, bind, Except.bind] at hm
    cases hs : step v1 acc with
    | error _ => rw [hs] at hm; cases hm
    | ok st =>
      rw [hs] at hm
      obtain ⟨v2, hg, hno, hpers, hown, rfl⟩ := (hstep v1 acc st).mp hs
      have hsub := ih (acc ++ [mergePairVar v1 v2]) merged hm
      refine ⟨?_, fun u => ?_⟩
      · rw [hsub.1, List.map_append]; simp [mergePairVar]
      · rw [hsub.2 u, List.mem_append, List.mem_singleton]
        constructor
        · rintro ((hu | rfl) | ⟨a, b, ha, hgb, hno', hp', ho', rfl⟩)
          · exact Or.inl hu
          · exact Or.inr ⟨v1, v2, List.mem_cons_self, hg, hno, hpers, hown, rfl⟩
          · exact Or.inr ⟨a, b, List.mem_cons_of_mem _ ha, hgb, hno', hp', ho', rfl⟩
        · rintro (hu | ⟨a, b, ha, hgb, hno', hp', ho', rfl⟩)
          · exact Or.inl (Or.inl hu)
          · rcases List.mem_cons.mp ha with rfl | ha'
            · rw [hg] at hgb; cases hgb; exact Or.inl (Or.inr rfl)
            · exact Or.inr ⟨a, b, ha', hgb, hno', hp', ho', rfl⟩

/-- `c1.mergeJp c2 = .ok cm` yields `CtxWeakens cm c1`, `CtxWeakens cm c2`, and head `ty` match. -/
public theorem mergeJp_weakens {c1 c2 cm : RcCtx} (hm : c1.mergeJp c2 = Except.ok cm)
    (hnd1 : (c1.vars.map RcVar.id).Nodup) (hnd2 : (c2.vars.map RcVar.id).Nodup)
    (hnr1 : NoRcCorrect c1) :
    (cm.vars.map RcVar.id).Nodup ∧ NoRcCorrect cm ∧
    cm.vars.map RcVar.id = c1.vars.map RcVar.id ∧
    CtxWeakens cm c1 ∧ CtxWeakens cm c2 ∧
    (∀ w ∈ cm.vars, ∃ v1 ∈ c1.vars, w.id = v1.id ∧ w.ty = v1.ty) ∧
    (∀ p, p ∈ cm.sharedPreds → p ∈ c1.sharedPreds) := by
  unfold RcCtx.mergeJp at hm
  dsimp only at hm
  obtain ⟨merged, hf, hm2⟩ := except_bind_ok hm
  simp only [pure, Except.pure, Except.ok.injEq] at hm2
  subst hm2
  have hstep : ∀ (v1 : RcVar) (acc : List RcVar) (res : ForInStep (List RcVar)),
      (have merged := acc
       match c2.get? v1.id with
       | none => do
         (throw ("jp merge: missing var x." ++ toString v1.id) : Except String PUnit)
         pure (ForInStep.yield merged)
       | some v2 =>
         have __do_jp := fun (_ : Unit) =>
           have b := v1.borrowed && v2.borrowed && (v1.parent? == v2.parent?)
           have p? := if b = true then v1.parent? else none
           have merged := merged ++ [mergePairVar v1 v2]
           pure (ForInStep.yield merged)
         if (v1.noRc != v2.noRc || v1.persistent != v2.persistent ||
             v1.owned != v2.owned) = true then do
           let __r ← (throw ("jp merge: ownership mismatch on x." ++ toString v1.id ++
             " (" ++ toString v1.owned ++ " vs " ++ toString v2.owned ++ ")") :
               Except String Unit)
           __do_jp __r
         else __do_jp ()) = Except.ok res ↔
      ∃ v2, c2.get? v1.id = some v2 ∧ v1.noRc = v2.noRc ∧
        v1.persistent = v2.persistent ∧ v1.owned = v2.owned ∧
        res = ForInStep.yield (acc ++ [mergePairVar v1 v2]) := by
    intro v1 acc res
    dsimp only
    cases hg : c2.get? v1.id with
    | none =>
      simp only [bind, Except.bind, except_str_throw_eq]
      simp
    | some v2 =>
      by_cases hmm :
          (v1.noRc != v2.noRc || v1.persistent != v2.persistent ||
            v1.owned != v2.owned) = true
      · simp only [hmm, ↓reduceIte, bind, Except.bind, except_str_throw_eq]
        constructor
        · intro h; cases h
        · rintro ⟨v2', hg', hno, hp, ho, _⟩; cases hg'; simp [hno, hp, ho] at hmm
      · have hn : v1.noRc = v2.noRc ∧ v1.persistent = v2.persistent ∧
            v1.owned = v2.owned := by
          have hb : (v1.noRc != v2.noRc) = false ∧ (v1.persistent != v2.persistent) = false ∧
              (v1.owned != v2.owned) = false := by
            revert hmm
            cases (v1.noRc != v2.noRc) <;> cases (v1.persistent != v2.persistent) <;>
              cases (v1.owned != v2.owned) <;> decide
          exact ⟨by simpa [bne] using hb.1, by simpa [bne] using hb.2.1,
            by simpa [bne] using hb.2.2⟩
        simp only [hmm, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
        constructor
        · intro h; exact ⟨v2, rfl, hn.1, hn.2.1, hn.2.2, h.symm⟩
        · rintro ⟨v2', hg', _, _, _, rfl⟩; cases hg'; rfl
  obtain ⟨hmap, hmem⟩ := mergeJp_loop_spec c2 _ hstep c1.vars [] merged hf
  have hndm : (merged.map RcVar.id).Nodup := by simpa using hmap ▸ hnd1
  have hmem' : ∀ w ∈ merged, ∃ v1 v2, v1 ∈ c1.vars ∧ c2.get? v1.id = some v2 ∧
      v1.noRc = v2.noRc ∧ v1.persistent = v2.persistent ∧ v1.owned = v2.owned ∧
      w = mergePairVar v1 v2 := fun w hw => by
    rcases (hmem w).mp hw with hnil | h
    · cases hnil
    · exact h
  have hnrm : NoRcCorrect { vars := merged, sharedPreds := [] } := fun w hw hno => by
    obtain ⟨v1, _, hv1m, _, _, _, _, rfl⟩ := hmem' w hw; exact hnr1 v1 hv1m hno
  have hbp_none : ∀ {v1 v2 : RcVar},
      (mergePairVar v1 v2).borrowed = false → (mergePairVar v1 v2).parent? = none := by
    intro v1 v2 hb; dsimp only [mergePairVar] at hb ⊢; simp [hb]
  refine ⟨hndm, hnrm, by simpa using hmap, ?_, ?_, ?_, ?_⟩
  · refine ⟨hndm, hnd1, fun w hw => ?_, fun p hp => (List.mem_filter.mp hp).1⟩
    obtain ⟨v1, v2, hv1m, _, _, _, _, rfl⟩ := hmem' w hw
    have hbr1 : (mergePairVar v1 v2).borrowed = true →
        v1.borrowed = true ∧ v1.parent? = (mergePairVar v1 v2).parent? := by
      intro hb; dsimp only [mergePairVar] at hb ⊢
      cases hb1 : v1.borrowed <;> cases hb2 : v2.borrowed <;>
        cases hp : (v1.parent? == v2.parent?) <;> simp_all [beq_iff_eq]
    have hex1 : (mergePairVar v1 v2).excl = true → v1.excl = true := by
      intro hex; dsimp only [mergePairVar] at hex
      cases hx1 : v1.excl <;> cases hx2 : v2.excl <;> simp_all
    refine ⟨v1, hv1m, rfl, hnr1 v1 hv1m, hbp_none, rfl, rfl, rfl,
      hbr1, hex1, fun hrt => by simp [mergePairVar, hrt]⟩
  · refine ⟨hndm, hnd2, fun w hw => ?_, fun p hp => by
        simpa [List.mem_filter, List.contains_eq_mem] using (List.mem_filter.mp hp).2⟩
    obtain ⟨v1, v2, hv1m, hg2, hno, hpers, hown, rfl⟩ := hmem' w hw
    obtain ⟨hv2m, hv2id⟩ := RcCtx.get?_mem hg2
    have hbr2 : (mergePairVar v1 v2).borrowed = true →
        v2.borrowed = true ∧ v2.parent? = (mergePairVar v1 v2).parent? := by
      intro hb; dsimp only [mergePairVar] at hb ⊢
      cases hb1 : v1.borrowed <;> cases hb2 : v2.borrowed <;>
        cases hp : (v1.parent? == v2.parent?) <;> simp_all [beq_iff_eq]
    have hex2 : (mergePairVar v1 v2).excl = true → v2.excl = true := by
      intro hex; dsimp only [mergePairVar] at hex
      cases hx1 : v1.excl <;> cases hx2 : v2.excl <;> simp_all
    refine ⟨v2, hv2m, hv2id.symm, hnr1 v1 hv1m, hbp_none, hno, hpers, hown,
      hbr2, hex2, fun hrt => by simp [mergePairVar, hrt]⟩
  · intro w hw; obtain ⟨v1, _, hv1m, _, _, _, _, rfl⟩ := hmem' w hw; exact ⟨v1, hv1m, rfl, rfl⟩
  · intro p hp; exact (List.mem_filter.mp hp).1

private theorem mergeJpList_loop_spec (cs : List RcCtx) (acc : RcCtx)
    (step : RcCtx → RcCtx → Except String (ForInStep RcCtx))
    (hstep : ∀ c' acc res, step c' acc = Except.ok res ↔
      ∃ m, acc.mergeJp c' = Except.ok m ∧ res = ForInStep.yield m)
    (hndA : (acc.vars.map RcVar.id).Nodup)
    (hcA : ∀ w ∈ acc.vars, w.borrowed = false → w.parent? = none)
    (hnrA : NoRcCorrect acc) (hndCs : ∀ c ∈ cs, (c.vars.map RcVar.id).Nodup) :
    ∀ res, forIn cs acc step = Except.ok res →
      (res.vars.map RcVar.id).Nodup ∧ NoRcCorrect res ∧
      res.vars.map RcVar.id = acc.vars.map RcVar.id ∧ CtxWeakens res acc ∧
      (∀ c ∈ cs, CtxWeakens res c) ∧
      (∀ w ∈ res.vars, ∃ v ∈ acc.vars, w.id = v.id ∧ w.ty = v.ty) ∧
      (∀ p, p ∈ res.sharedPreds → p ∈ acc.sharedPreds) := by
  induction cs generalizing acc with
  | nil =>
    intro res hr; cases hr
    have hrefl : CtxWeakens acc acc :=
      ⟨hndA, hndA, fun w hw => ⟨w, hw, rfl, hnrA w hw, hcA w hw, rfl, rfl, rfl,
        (fun h => ⟨h, rfl⟩), id, id⟩, fun _ hp => hp⟩
    exact ⟨hndA, hnrA, rfl, hrefl, (fun _ hc => by cases hc),
      (fun w hw => ⟨w, hw, rfl, rfl⟩), fun _ hp => hp⟩
  | cons c1 rest ih =>
    intro res hr
    simp only [List.forIn_cons, bind, Except.bind] at hr
    cases hs : step c1 acc with
    | error _ => rw [hs] at hr; cases hr
    | ok st =>
      rw [hs] at hr
      obtain ⟨cm, hm, rfl⟩ := (hstep c1 acc st).mp hs
      obtain ⟨hndm, hnrm, hmapm, hwa, hw1, hhead, hsp⟩ :=
        mergeJp_weakens hm hndA (hndCs c1 List.mem_cons_self) hnrA
      have hcm_bp : ∀ w ∈ cm.vars, w.borrowed = false → w.parent? = none := fun w hw hb => by
        obtain ⟨_, _, _, _, hbp, _⟩ := hwa.2.2.1 w hw; exact hbp hb
      obtain ⟨hndr, hnrr, hmapr, hwm, hrest, hheadr, hspr⟩ :=
        ih cm hndm hcm_bp hnrm (fun c hc => hndCs c (List.mem_cons_of_mem _ hc)) res hr
      refine ⟨hndr, hnrr, hmapr.trans hmapm, ctxWeakens_trans hwm hwa, fun c hc => ?_,
        fun w hw => ?_, fun p hp => hsp p (hspr p hp)⟩
      · rcases List.mem_cons.mp hc with rfl | hc'
        · exact ctxWeakens_trans hwm hw1
        · exact hrest c hc'
      · obtain ⟨vm, hvm, hid1, hty1⟩ := hheadr w hw
        obtain ⟨va, hva, hid2, hty2⟩ := hhead vm hvm
        exact ⟨va, hva, hid1.trans hid2, hty1.trans hty2⟩

/-- Merging a non-empty jump list yields weakening to every member and preserves head `ty`. -/
public theorem mergeJpList_weakens {c0 : RcCtx} {cs : List RcCtx} {res : RcCtx}
    (hm : mergeJpList (c0 :: cs) = Except.ok (some res))
    (hnd0 : (c0.vars.map RcVar.id).Nodup)
    (hbp0 : ∀ w ∈ c0.vars, w.borrowed = false → w.parent? = none)
    (hnr0 : NoRcCorrect c0) (hndCs : ∀ c ∈ cs, (c.vars.map RcVar.id).Nodup) :
    (res.vars.map RcVar.id).Nodup ∧ NoRcCorrect res ∧
    res.vars.map RcVar.id = c0.vars.map RcVar.id ∧
    (∀ c ∈ c0 :: cs, CtxWeakens res c) ∧
    (∀ w ∈ res.vars, ∃ v ∈ c0.vars, w.id = v.id ∧ w.ty = v.ty) ∧
    (∀ p, p ∈ res.sharedPreds → p ∈ c0.sharedPreds) := by
  unfold mergeJpList at hm
  dsimp only at hm
  obtain ⟨r, hf, hm2⟩ := except_bind_ok hm
  simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hm2
  subst hm2
  have hstep : ∀ (c' acc : RcCtx) (res' : ForInStep RcCtx),
      (have acc := acc
       do let __x ← acc.mergeJp c'; have acc : RcCtx := __x; pure (ForInStep.yield acc)) =
        Except.ok res' ↔
      ∃ m, acc.mergeJp c' = Except.ok m ∧ res' = ForInStep.yield m := by
    intro c' acc res'
    dsimp only
    simp only [bind, Except.bind, pure, Except.pure]
    cases acc.mergeJp c' with
    | error _ => simp
    | ok m => simp [eq_comm]
  obtain ⟨hnd, hnr, hmap, hw0, hwcs, hhead, hsp⟩ :=
    mergeJpList_loop_spec cs c0 _ hstep hnd0 hbp0 hnr0 hndCs r hf
  refine ⟨hnd, hnr, hmap, fun c hc => ?_, hhead, hsp⟩
  rcases List.mem_cons.mp hc with rfl | hc'
  · exact hw0
  · exact hwcs c hc'

end CtxWeakensAndMerge

section WeakeningInvs

/-- `CleanVars` transfers from `ctxS` to `ctxW` under `CtxWeakens ctxW ctxS`. -/
public theorem cleanVars_of_ctxWeakens {ctxW ctxS : RcCtx}
    (hw : CtxWeakens ctxW ctxS) (hc : CleanVars ctxS) : CleanVars ctxW := by
  intro w hwm
  obtain ⟨v, hvm, _, hnrw, hbp, hno, hpers, hown, hbr, hex, hrt⟩ := hw.2.2.1 w hwm
  have hcv := hc v hvm
  have hnb_of : v.borrowed = false → w.borrowed = false := fun hvb => by
    cases hb : w.borrowed with
    | false => rfl | true => exact absurd (hbr hb).1 (by simp [hvb])
  have hnex_of : v.excl = false → w.excl = false := fun hve => by
    cases hx : w.excl with
    | false => rfl | true => exact absurd (hex hx) (by simp [hve])
  refine ⟨⟨fun hno_w => ?_, fun hsc_w => ?_⟩, fun hp_w => ?_, fun hb_w => ?_, hbp, ?_⟩
  · have hv := hcv.1.1 (hno.symm.trans hno_w)
    have hwb := hnb_of hv.2.2.1
    exact ⟨hpers.trans hv.1, hown.trans hv.2.1, hwb, hbp hwb, hnex_of hv.2.2.2.2⟩
  · cases hno_f : w.noRc with
    | true => rfl
    | false =>
      have hnr := hnrw hno_f
      cases hty : w.ty <;> rw [hty] at hsc_w hnr <;>
        simp [LcTy.isScalar, LcTy.needsRc] at hsc_w hnr
  · have hv := hcv.2.1 (hpers.symm.trans hp_w)
    have hwb := hnb_of hv.2.2.1
    exact ⟨hno.trans hv.1, hown.trans hv.2.1, hwb, hbp hwb, hnex_of hv.2.2.2.2⟩
  · have hv := hcv.2.2.1 (hbr hb_w).1
    exact ⟨hno.trans hv.1, hpers.trans hv.2.1, hnex_of hv.2.2⟩
  · exact hrt hcv.2.2.2.2

/-- `ParentsOwned` transfers from `ctxS` to `ctxW` when `ctxS` and `ctxW` share IDs. -/
public theorem parentsOwned_of_ctxWeakens {ctxW ctxS : RcCtx}
    (hw : CtxWeakens ctxW ctxS) (hpo : ParentsOwned ctxS)
    (hsame : ∀ v ∈ ctxS.vars, ∃ w ∈ ctxW.vars, w.id = v.id) :
    ParentsOwned ctxW := by
  intro w hwm p hp
  obtain ⟨v, hvm, _, _, hbp, _, _, _, hbr, _, _⟩ := hw.2.2.1 w hwm
  have hbw : w.borrowed = true := by
    cases hb : w.borrowed with | true => rfl | false => rw [hbp hb] at hp; cases hp
  obtain ⟨hbv, hpv⟩ := hbr hbw
  obtain ⟨pvs, hpvsm, hpvsid, hno, hpers, hown, hpvsbr⟩ := hpo v hvm p (hpv.trans hp)
  obtain ⟨pvw, hpvwm, hpvwid⟩ := hsame pvs hpvsm
  obtain ⟨pvs', hpvs'm, hid', _, _, hno', hpers', hown', hbr', _, _⟩ := hw.2.2.1 pvw hpvwm
  have hpeq := rcVar_eq_of_mem_nodup hw.2.1 hpvs'm hpvsm (hid'.symm.trans hpvwid)
  subst hpeq
  have hpvbr : pvw.borrowed = false := by
    cases hb : pvw.borrowed with
    | false => rfl | true => exact absurd (hbr' hb).1 (by simp [hpvsbr])
  exact ⟨pvw, hpvwm, hpvwid.trans hpvsid, hno'.trans hno, hpers'.trans hpers,
    by rw [hown']; exact hown, hpvbr⟩

/-- `SharedBoolVars` transfers from `ctxS` to `ctxW` under `CtxWeakens`. -/
public theorem sharedBoolVars_of_ctxWeakens {ctxW ctxS : RcCtx}
    (hw : CtxWeakens ctxW ctxS) (hsbv : SharedBoolVars ctxS) : SharedBoolVars ctxW := by
  intro p hp vb hgb
  obtain ⟨vs, hvsm, hid, _, _, hno, _⟩ := hw.2.2.1 vb (RcCtx.get?_mem hgb).1
  have hgs : ctxS.get? p.1 = some vs := by
    rw [← (RcCtx.get?_mem hgb).2, hid]; exact (RcCtx.mem_get?_iff hw.2.1).mpr hvsm
  rw [hno]; exact hsbv p (hw.2.2.2 p hp) vs hgs

/-- `SharedBoolPreds` transfers from `ctxS` to `ctxW` when IDs match `ctxS.vars`. -/
public theorem sharedBoolPreds_of_ctxWeakens {ctxW ctxS : RcCtx}
    (hw : CtxWeakens ctxW ctxS) (hsbp : SharedBoolPreds ctxS)
    (hsame : ∀ v ∈ ctxS.vars, ∃ w ∈ ctxW.vars, w.id = v.id) :
    SharedBoolPreds ctxW := by
  intro p hp
  obtain ⟨vs, hgs, hno_s⟩ := hsbp p (hw.2.2.2 p hp)
  obtain ⟨vsm, vsid⟩ := RcCtx.get?_mem hgs
  obtain ⟨vw, hvwm, hvwid⟩ := hsame vs vsm
  obtain ⟨vs', hvs'm, hid', _, _, hno', _⟩ := hw.2.2.1 vw hvwm
  have hpeq := rcVar_eq_of_mem_nodup hw.2.1 hvs'm vsm (hid'.symm.trans hvwid)
  subst hpeq
  have hgw : ctxW.get? p.1 = some vw := by
    rw [← vsid, ← hvwid]; exact (RcCtx.mem_get?_iff hw.1).mpr hvwm
  exact ⟨vw, hgw, hno'.trans hno_s⟩

end WeakeningInvs

section RestrictLemmas

private theorem checkNoLeaks_loop_spec (keepIds : List Nat)
    (step : RcVar → PUnit → Except String (ForInStep PUnit))
    (hstep : ∀ u st, step u PUnit.unit = Except.ok st →
      (!keepIds.contains u.id && !u.noRc && !u.persistent && u.owned != 0) = false ∧
      st = ForInStep.yield PUnit.unit)
    (xs : List RcVar) :
    forIn xs PUnit.unit step = Except.ok PUnit.unit →
    ∀ v ∈ xs, v.id ∉ keepIds → (v.noRc || v.persistent || v.owned == 0) = true := by
  induction xs with
  | nil => intro _ v hv; cases hv
  | cons u rest ih =>
    intro h v hv hnot
    simp only [List.forIn_cons, bind, Except.bind] at h
    cases hs : step u PUnit.unit with
    | error _ => rw [hs] at h; cases h
    | ok st =>
      rw [hs] at h
      obtain ⟨hcond, rfl⟩ := hstep u st hs
      rcases List.mem_cons.mp hv with rfl | hv'
      · have hkc : keepIds.contains v.id = false := by
          cases hc : keepIds.contains v.id with
          | false => rfl | true => exact absurd (List.contains_iff_mem.mp hc) hnot
        rw [hkc] at hcond
        revert hcond
        cases v.noRc <;> cases v.persistent <;> cases hze : (v.owned == 0) <;> simp [bne, hze]
      · exact ih h v hv' hnot

/-- `ctx.checkNoLeaks keepIds = .ok ()` ensures every dropped variable has zero owned refs. -/
public theorem checkNoLeaks_spec {ctx : RcCtx} {keepIds : List Nat}
    (hl : ctx.checkNoLeaks keepIds = Except.ok ()) :
    ∀ v ∈ ctx.vars, v.id ∉ keepIds → (v.noRc || v.persistent || v.owned == 0) = true := by
  unfold RcCtx.checkNoLeaks at hl
  obtain ⟨u, hf, _⟩ := except_bind_ok hl
  have hstep : ∀ (v : RcVar) st,
      (if (!keepIds.contains v.id && !v.noRc && !v.persistent && v.owned != 0) = true then do
        (throw ("leaked owned var x." ++ toString v.id ++
          " (owned=" ++ toString v.owned ++ ")") : Except String PUnit)
        pure (ForInStep.yield PUnit.unit)
      else pure (ForInStep.yield PUnit.unit)) = Except.ok st →
      (!keepIds.contains v.id && !v.noRc && !v.persistent && v.owned != 0) = false ∧
      st = ForInStep.yield PUnit.unit := by
    intro v st hs
    by_cases hbad : (!keepIds.contains v.id && !v.noRc && !v.persistent && v.owned != 0) = true
    · simp only [hbad, ↓reduceIte, bind, Except.bind] at hs; cases hs
    · simp only [hbad, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hs
      exact ⟨Bool.eq_false_iff.mpr hbad, hs.symm⟩
  cases u
  exact checkNoLeaks_loop_spec keepIds _ hstep ctx.vars hf

private theorem filter_map_nodup {α β : Type} {f : α → β} {p : α → Bool} :
    ∀ {xs : List α}, (xs.map f).Nodup → ((xs.filter p).map f).Nodup
  | [], h => h
  | x :: xs, h => by
    simp only [List.map_cons, List.nodup_cons] at h
    simp only [List.filter_cons]
    split
    · simp only [List.map_cons, List.nodup_cons]
      have hnotin : f x ∉ (xs.filter p).map f := fun hmem => by
        obtain ⟨y, hy, hyf⟩ := List.mem_map.mp hmem
        exact h.1 (List.mem_map.mpr ⟨y, (List.mem_filter.mp hy).1, hyf⟩)
      exact ⟨hnotin, filter_map_nodup h.2⟩
    · exact filter_map_nodup h.2

/-- Restricting a context preserves `Nodup` of variable IDs. -/
public theorem restrict_nodup {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (keepIds : List Nat) : ((ctx.restrict keepIds).vars.map RcVar.id).Nodup :=
  filter_map_nodup hnd

private theorem find?_filter_of_true {α : Type} {p q : α → Bool} :
    ∀ (xs : List α), (∀ x, q x = true → p x = true) → (xs.filter p).find? q = xs.find? q
  | [], _ => rfl
  | x :: xs, hpq => by
    simp only [List.filter_cons]
    by_cases hpx : p x = true
    · simp only [hpx, ↓reduceIte, List.find?_cons]
      by_cases hqx : q x = true
      · simp [hqx]
      · simp [hqx, find?_filter_of_true xs hpq]
    · have hqx : q x = false := by
        cases h : q x with | false => rfl | true => exact absurd (hpq x h) hpx
      simp only [hpx, Bool.false_eq_true, ↓reduceIte, List.find?_cons, hqx]
      exact find?_filter_of_true xs hpq

/-- Lookup in `ctx.restrict keepIds` agrees with `ctx.get?` on `keepIds`. -/
public theorem restrict_get?_eq (ctx : RcCtx) (keepIds : List Nat) (s : Nat) :
    (ctx.restrict keepIds).get? s =
      if keepIds.contains s = true then ctx.get? s else none := by
  unfold RcCtx.restrict RcCtx.get?
  dsimp only
  by_cases hs : keepIds.contains s = true
  · simp only [hs, ↓reduceIte]
    exact find?_filter_of_true ctx.vars fun v hv => by simpa [beq_iff_eq.mp hv] using hs
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    cases hf : (ctx.vars.filter (fun v => keepIds.contains v.id)).find? (fun v => v.id == s) with
    | none => rfl
    | some v =>
      exfalso
      have hfv := (List.mem_filter.mp (List.mem_of_find?_eq_some hf)).2
      have hvs := List.find?_some hf
      have hid : v.id = s := beq_iff_eq.mp hvs
      rw [hid] at hfv
      exact hs hfv

private theorem list_filter_comm {α : Type} (p q : α → Bool) :
    ∀ (xs : List α), (xs.filter p).filter q = (xs.filter q).filter p
  | [] => rfl
  | x :: xs => by
    simp only [List.filter_cons]
    by_cases hp : p x = true <;> by_cases hq : q x = true <;>
      simp [hp, hq, list_filter_comm p q xs]

private theorem localHandles_filter_perm_zero (envH : HValEnv) (p : RcVar → Bool) :
    ∀ (vars : List RcVar),
      (∀ v ∈ vars, p v = false → varHandles envH v = []) →
      ((vars.filter p).map (varHandles envH)).flatten.Perm (vars.map (varHandles envH)).flatten
  | [], _ => List.Perm.refl _
  | v :: vs, hzero => by
    have ih := localHandles_filter_perm_zero envH p vs
      (fun u hu hpu => hzero u (List.mem_cons_of_mem _ hu) hpu)
    simp only [List.filter_cons, List.map_cons, List.flatten_cons]
    by_cases hp : p v = true
    · simp only [hp, ↓reduceIte, List.map_cons, List.flatten_cons]; exact ih.append_left _
    · have hf := Bool.eq_false_iff.mpr hp
      simpa [hf, hzero v List.mem_cons_self hf] using ih

/-- With `checkNoLeaks keepIds`, `restrict keepIds` preserves all live local handles. -/
public theorem restrict_handles_perm {ctx : RcCtx} {keepIds : List Nat} (envH : HValEnv)
    (hc : CleanVars ctx) (hl : ctx.checkNoLeaks keepIds = Except.ok ()) :
    (localHandles (ctx.restrict keepIds) envH).Perm (localHandles ctx envH) ∧
    ∀ s, (localHandlesExcept (ctx.restrict keepIds) envH s).Perm
      (localHandlesExcept ctx envH s) := by
  have hzero := checkNoLeaks_spec hl
  have hvh0 : ∀ v ∈ ctx.vars, v.id ∉ keepIds → varHandles envH v = [] := by
    intro v hv hnot
    have hflags := hzero v hv hnot
    have hrt : v.resetTok = false := (hc v hv).2.2.2.2
    unfold varHandles
    have hcond : (v.noRc || v.persistent || v.resetTok || v.owned == 0) = true := by
      revert hflags; rw [hrt]
      cases v.noRc <;> cases v.persistent <;> cases (v.owned == 0) <;> simp
    simp [hcond]
  have hmain : ∀ (v : RcVar), v ∈ ctx.vars → keepIds.contains v.id = false →
      varHandles envH v = [] := fun v hv hfalse =>
    hvh0 v hv fun hmem => by
      have hc' : keepIds.contains v.id = true := List.contains_iff_mem.mpr hmem
      rw [hc'] at hfalse; cases hfalse
  refine ⟨localHandles_filter_perm_zero envH (fun v => keepIds.contains v.id) ctx.vars hmain,
    fun s => ?_⟩
  unfold localHandlesExcept RcCtx.restrict
  dsimp only
  rw [list_filter_comm]
  exact localHandles_filter_perm_zero envH (fun v => keepIds.contains v.id)
    (ctx.vars.filter (fun v => v.id != s)) fun v hv hfalse =>
      hmain v (List.mem_filter.mp hv).1 hfalse

/-- Static + dynamic context invariants preserved by `ctx.restrict keepIds`. -/
public theorem restrict_ctx_invs {ctx : RcCtx} {keepIds : List Nat}
    (hnd : (ctx.vars.map RcVar.id).Nodup) (hc : CleanVars ctx) (hpo : ParentsOwned ctx)
    (hnr : NoRcCorrect ctx) (hsbv : SharedBoolVars ctx) (hsbp : SharedBoolPreds ctx)
    (hl : ctx.checkNoLeaks keepIds = Except.ok ()) :
    let ctxS := ctx.restrict keepIds
    (ctxS.vars.map RcVar.id).Nodup ∧ CleanVars ctxS ∧ ParentsOwned ctxS ∧ NoRcCorrect ctxS ∧
    SharedBoolVars ctxS ∧ SharedBoolPreds ctxS ∧
    (∀ id ∈ keepIds, (ctx.get? id).isSome = true → (ctxS.get? id).isSome = true) := by
  intro ctxS
  have hzero := checkNoLeaks_spec hl
  have hmemS : ∀ {v : RcVar}, v ∈ ctxS.vars ↔ v ∈ ctx.vars ∧ v.id ∈ keepIds := by
    intro v; simp [ctxS, RcCtx.restrict, List.mem_filter]
  refine ⟨restrict_nodup hnd keepIds, fun v hv => hc v (hmemS.mp hv).1, ?_,
    fun v hv => hnr v (hmemS.mp hv).1, ?_, ?_, ?_⟩
  · intro v hv p hpv
    obtain ⟨pv, hpvm, hpvid, hpvno, hpvp, hpvown, hpvbr⟩ := hpo v (hmemS.mp hv).1 p hpv
    have hpin : p ∈ keepIds := by
      cases hkp : keepIds.contains p with
      | true => exact List.contains_iff_mem.mp hkp
      | false =>
        exfalso
        have hnot : pv.id ∉ keepIds := fun hm => by
          have hmem : keepIds.contains p = true := List.contains_iff_mem.mpr (hpvid ▸ hm)
          rw [hmem] at hkp; cases hkp
        have hbad := hzero pv hpvm hnot
        rw [hpvno, hpvp] at hbad
        have : pv.owned = 0 := beq_iff_eq.mp (by simpa using hbad)
        omega
    exact ⟨pv, hmemS.mpr ⟨hpvm, hpvid ▸ hpin⟩, hpvid, hpvno, hpvp, hpvown, hpvbr⟩
  · intro pr hpr vb hgb
    have hp1in := List.contains_iff_mem.mp
      (Bool.and_eq_true _ _ |>.mp (List.mem_filter.mp hpr).2).1
    dsimp only [ctxS] at hgb
    rw [restrict_get?_eq] at hgb
    simp only [List.contains_iff_mem.mpr hp1in, ↓reduceIte] at hgb
    exact hsbv pr (List.mem_filter.mp hpr).1 vb hgb
  · intro pr hpr
    have hp1in := List.contains_iff_mem.mp
      (Bool.and_eq_true _ _ |>.mp (List.mem_filter.mp hpr).2).1
    obtain ⟨vb, hgb, hvbno⟩ := hsbp pr (List.mem_filter.mp hpr).1
    have hgb' : ctxS.get? pr.1 = some vb := by
      dsimp only [ctxS]
      rw [restrict_get?_eq]
      simp only [List.contains_iff_mem.mpr hp1in, ↓reduceIte]
      exact hgb
    exact ⟨vb, hgb', hvbno⟩
  · intro id hid hsome
    rw [restrict_get?_eq]
    simp only [List.contains_iff_mem.mpr hid, ↓reduceIte]
    exact hsome

end RestrictLemmas

section StaticAndApplyArgsHelpers

/-- Pure context invariants propagated statically through `checkCode`. -/
@[expose] public def CtxStaticInv (ctx : RcCtx) : Prop :=
  (ctx.vars.map RcVar.id).Nodup ∧ NoRcCorrect ctx ∧ SharedBoolPreds ctx ∧
  (∀ v ∈ ctx.vars, v.borrowed = false → v.parent? = none)

/-- Join-point scope well-formedness relative to the current `ctx`. -/
@[expose] public def JpsScopeIn (jps : List RcJpInfo) (ctx : RcCtx) : Prop :=
  (jps.map RcJpInfo.id).Nodup ∧
  ∀ info ∈ jps, (info.params.map (·.id)).Nodup ∧ info.scopeIds.Nodup ∧
    ∀ id ∈ info.scopeIds, (ctx.get? id).isSome = true

/-- Generic invariant propagation across `RcCtx.applyArgs`. -/
public theorem applyArgs_inv (P : RcCtx → Prop)
    (hstep : ∀ {ctx ctx1 : RcCtx} {y n : Nat},
      P ctx → ctx.consumeVar y n = Except.ok ctx1 → P ctx1) :
    ∀ {ctx ctx1 : RcCtx} {as : List LcArg} {bs : List Bool},
      P ctx → ctx.applyArgs as bs = Except.ok ctx1 → P ctx1 := by
  intro ctx ctx1 as
  induction as generalizing ctx with
  | nil =>
    intro bs hp ha
    cases bs <;> simp [RcCtx.applyArgs] at ha
    cases ha; exact hp
  | cons a rest ih =>
    intro bs hp ha
    cases bs with
    | nil => simp [RcCtx.applyArgs] at ha
    | cons b brest =>
      simp only [RcCtx.applyArgs, bind, Except.bind] at ha
      by_cases hb : b = true
      · simp only [hb, ↓reduceIte] at ha
        cases hchk : ctx.checkArgLive a with
        | error _ => rw [hchk] at ha; cases ha
        | ok _ => rw [hchk] at ha; exact ih hp ha
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
        cases hc : ctx.consumeArg a with
        | error _ => rw [hc] at ha; cases ha
        | ok ctx' =>
          rw [hc] at ha
          have hp' : P ctx' := by
            cases a with
            | erased => simp [RcCtx.consumeArg, pure, Except.pure] at hc; cases hc; exact hp
            | var y => exact hstep hp hc
          exact ih hp' ha

/-- Generic preorder relation propagation across `RcCtx.applyArgs`. -/
public theorem applyArgs_rel (R : RcCtx → RcCtx → Prop)
    (hrefl : ∀ ctx, R ctx ctx) (htrans : ∀ {a b c}, R a b → R b c → R a c)
    (hstep : ∀ {ctx ctx1 : RcCtx} {y n : Nat}, ctx.consumeVar y n = Except.ok ctx1 → R ctx ctx1) :
    ∀ {ctx ctx1 : RcCtx} {as : List LcArg} {bs : List Bool},
      ctx.applyArgs as bs = Except.ok ctx1 → R ctx ctx1 := by
  intro ctx ctx1 as
  induction as generalizing ctx with
  | nil =>
    intro bs ha; cases bs <;> simp [RcCtx.applyArgs] at ha
    cases ha; exact hrefl _
  | cons a rest ih =>
    intro bs ha
    cases bs with
    | nil => simp [RcCtx.applyArgs] at ha
    | cons b brest =>
      simp only [RcCtx.applyArgs, bind, Except.bind] at ha
      by_cases hb : b = true
      · simp only [hb, ↓reduceIte] at ha
        cases hchk : ctx.checkArgLive a with
        | error _ => rw [hchk] at ha; cases ha
        | ok _ => rw [hchk] at ha; exact ih ha
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
        cases hc : ctx.consumeArg a with
        | error _ => rw [hc] at ha; cases ha
        | ok ctx' =>
          rw [hc] at ha
          have hr : R ctx ctx' := by
            cases a with
            | erased => simp [RcCtx.consumeArg, pure, Except.pure] at hc; cases hc; exact hrefl _
            | var y => exact hstep hc
          exact htrans hr (ih ha)

/-- `jpsScopeIn_mono` lifts `JpsScopeIn` across ID-preserving context extensions. -/
public theorem jpsScopeIn_mono {jps : List RcJpInfo} {ctx ctx' : RcCtx}
    (hj : JpsScopeIn jps ctx)
    (hkeep : ∀ id, (ctx.get? id).isSome = true → (ctx'.get? id).isSome = true) :
    JpsScopeIn jps ctx' :=
  ⟨hj.1, fun info hi =>
    ⟨(hj.2 info hi).1, (hj.2 info hi).2.1, fun id hid => hkeep id ((hj.2 info hi).2.2 id hid)⟩⟩

private theorem noBorrowParent_put {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hnbp : ∀ v ∈ ctx.vars, v.borrowed = false → v.parent? = none)
    {v : RcVar} (hv : v.borrowed = false → v.parent? = none) :
    ∀ w ∈ (ctx.put v).vars, w.borrowed = false → w.parent? = none := fun w hw hb => by
  rcases (RcCtx.put_mem_iff hnd).mp hw with rfl | ⟨hwm, _⟩
  · exact hv hb
  · exact hnbp w hwm hb

private theorem noBorrowParent_invalidateChildren {ctx : RcCtx}
    (hnbp : ∀ v ∈ ctx.vars, v.borrowed = false → v.parent? = none) (x : Nat) :
    ∀ w ∈ (ctx.invalidateChildren x).vars, w.borrowed = false → w.parent? = none := by
  intro w hw hb
  unfold RcCtx.invalidateChildren at hw
  obtain ⟨u, hum, rfl⟩ := List.mem_map.mp hw
  by_cases h : (u.parent? == some x) = true
  · simp [h]
  · simp only [h, Bool.false_eq_true, ↓reduceIte] at hb ⊢
    exact hnbp u hum hb

private theorem noRcCorrect_put' {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hnr : NoRcCorrect ctx) {v : RcVar} (hv : v.noRc = false → v.ty.needsRc = true) :
    NoRcCorrect (ctx.put v) := fun w hw hno => by
  rcases (RcCtx.put_mem_iff hnd).mp hw with rfl | ⟨hwm, _⟩
  · exact hv hno
  · exact hnr w hwm hno

private theorem noRcCorrect_invalidateChildren' {ctx : RcCtx} (hnr : NoRcCorrect ctx) (x : Nat) :
    NoRcCorrect (ctx.invalidateChildren x) := by
  intro w hw hno
  unfold RcCtx.invalidateChildren at hw
  obtain ⟨u, hum, rfl⟩ := List.mem_map.mp hw
  by_cases h : (u.parent? == some x) = true
  · simp only [h, ↓reduceIte] at hno ⊢; exact hnr u hum hno
  · simp only [h, Bool.false_eq_true, ↓reduceIte] at hno ⊢; exact hnr u hum hno

private theorem find?_put_go_isSome (v : RcVar) (id : Nat) :
    ∀ (vars : List RcVar),
      ((vars.find? (fun w => w.id == id)).isSome = true →
        ((RcCtx.put.go v vars).find? (fun w => w.id == id)).isSome = true) ∧
      ((RcCtx.put.go v vars).find? (fun w => w.id == v.id)).isSome = true
  | [] => ⟨fun h => by simp at h, by simp [RcCtx.put.go]⟩
  | u :: us => by
    have ih := find?_put_go_isSome v id us
    unfold RcCtx.put.go
    by_cases huv : (u.id == v.id) = true
    · simp only [huv, ↓reduceIte, List.find?_cons]
      refine ⟨fun hs => ?_, by simp⟩
      by_cases hiv : (v.id == id) = true
      · simp [hiv]
      · have hiu : (u.id == id) = false := by
          by_cases hc : (u.id == id) = true
          · exfalso
            have h1 : u.id = id := beq_iff_eq.mp hc
            have h2 : u.id = v.id := beq_iff_eq.mp huv
            rw [← h2, h1, beq_self_eq_true] at hiv
            exact hiv rfl
          · exact Bool.eq_false_iff.mpr hc
        simp only [hiu] at hs
        simp [hiv, hs]
    · simp only [huv, Bool.false_eq_true, ↓reduceIte, List.find?_cons]
      constructor
      · intro hs
        by_cases hiu : (u.id == id) = true
        · simp [hiu]
        · simp only [hiu] at hs ⊢
          exact ih.1 hs
      · have hvu : (v.id == u.id) = false := by
          rw [Bool.beq_comm]; exact Bool.eq_false_iff.mpr huv
        simp [ih.2]

/-- Lookup ID preservation through `RcCtx.put`. -/
public theorem get?_isSome_put (ctx : RcCtx) (v : RcVar) (id : Nat)
    (h : (ctx.get? id).isSome = true) : ((ctx.put v).get? id).isSome = true :=
  (find?_put_go_isSome v id ctx.vars).1 h

/-- Lookup ID preservation through `RcCtx.invalidateChildren`. -/
public theorem get?_isSome_invalidateChildren (ctx : RcCtx) (p id : Nat)
    (h : (ctx.get? id).isSome = true) : ((ctx.invalidateChildren p).get? id).isSome = true := by
  unfold RcCtx.get? at h ⊢
  unfold RcCtx.invalidateChildren
  dsimp only
  cases hf : ctx.vars.find? (fun v => v.id == id) with
  | none => rw [hf] at h; cases h
  | some w =>
    let f : RcVar → RcVar := fun v =>
      if (v.parent? == some p) = true then { v with borrowed := false, parent? := none } else v
    let w' : RcVar := f w
    have hw'm : w' ∈ ctx.vars.map f := List.mem_map.mpr ⟨w, List.mem_of_find?_eq_some hf, rfl⟩
    have hw'id : w'.id = id := by
      dsimp only [w', f]
      have hws := List.find?_some hf
      split <;> exact beq_iff_eq.mp hws
    cases hres : (ctx.vars.map f).find? (fun v => v.id == id) with
    | some _ => rfl
    | none =>
      exfalso
      have hfn := List.find?_eq_none.mp hres w' hw'm
      rw [hw'id, beq_self_eq_true] at hfn
      exact hfn rfl

private theorem invalidateChildren_nodup' (ctx : RcCtx) (p : Nat)
    (hnd : (ctx.vars.map RcVar.id).Nodup) :
    ((ctx.invalidateChildren p).vars.map RcVar.id).Nodup := by
  have hmap : ((ctx.invalidateChildren p).vars.map RcVar.id) = ctx.vars.map RcVar.id := by
    unfold RcCtx.invalidateChildren
    simp only [List.map_map]
    congr 1; funext v; dsimp only [Function.comp_def]; split <;> rfl
  rw [hmap]; exact hnd

private theorem sharedBoolPreds_invalidateChildren' {ctx : RcCtx}
    (hnd : (ctx.vars.map RcVar.id).Nodup) (hsbp : SharedBoolPreds ctx) (x : Nat) :
    SharedBoolPreds (ctx.invalidateChildren x) := by
  intro p hp
  simp only [RcCtx.invalidateChildren, List.mem_filter] at hp
  obtain ⟨wb, hgb, hno⟩ := hsbp p hp.1
  let w1 : RcVar := if (wb.parent? == some x) = true then
    { wb with borrowed := false, parent? := none } else wb
  have hw1m : w1 ∈ (ctx.invalidateChildren x).vars :=
    List.mem_map.mpr ⟨wb, (RcCtx.get?_mem hgb).1, rfl⟩
  have hw1id : w1.id = p.1 := by dsimp only [w1]; split <;> exact (RcCtx.get?_mem hgb).2
  have hw1no : w1.noRc = true := by dsimp only [w1]; split <;> exact hno
  exact ⟨w1, hw1id ▸ (RcCtx.mem_get?_iff (invalidateChildren_nodup' ctx x hnd)).mpr hw1m, hw1no⟩

private theorem binderFreshOwned_invalidateChildren' {ctx : RcCtx}
    (hnd : (ctx.vars.map RcVar.id).Nodup) {x y : Nat} (hfr : binderFreshOwned ctx y = true) :
    binderFreshOwned (ctx.invalidateChildren x) y = true := by
  unfold binderFreshOwned at hfr ⊢
  have h1 := Bool.and_eq_true _ _ |>.mp hfr
  have h2 := Bool.and_eq_true _ _ |>.mp h1.1
  have hp1 : (ctx.invalidateChildren x).vars.all (fun u => u.parent? != some y) = true := by
    apply List.all_eq_true.mpr; intro u hu
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
    by_cases h : (w.parent? == some x) = true
    · simp [h]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact List.all_eq_true.mp h2.1 w hw
  have hsp1 : (ctx.invalidateChildren x).sharedPreds.all
      (fun p => p.1 != y && p.2 != y) = true := by
    apply List.all_eq_true.mpr; intro p hp
    simp only [RcCtx.invalidateChildren, List.mem_filter] at hp
    exact List.all_eq_true.mp h2.2 p hp.1
  have hg1 : (match (ctx.invalidateChildren x).get? y with
      | none => true | some v => !v.isLive) = true := by
    cases hres : (ctx.invalidateChildren x).get? y with
    | none => rfl
    | some v =>
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (RcCtx.get?_mem hres).1
      have hwid : w.id = y := by
        have hv := (RcCtx.get?_mem hres).2
        by_cases h : (w.parent? == some x) = true <;> simp [h] at hv <;> exact hv
      have hgw : ctx.get? y = some w := hwid ▸ (RcCtx.mem_get?_iff hnd).mpr hw
      have hnl : (!w.isLive) = true := by simpa [hgw] using h1.2
      cases hw_no : w.noRc <;> cases hw_p : w.persistent <;>
        cases hw_b : w.borrowed <;> cases hw_r : w.resetTok <;>
        by_cases h : (w.parent? == some x) = true <;> simp_all [RcVar.isLive]
  rw [hp1, hsp1]; exact hg1

/-- Static invariants preserved through `RcCtx.consumeVar`. -/
public theorem ctxStaticInv_consumeVar {ctx ctx1 : RcCtx} (hs : CtxStaticInv ctx)
    {x n : Nat} (hc : ctx.consumeVar x n = Except.ok ctx1) : CtxStaticInv ctx1 := by
  unfold RcCtx.consumeVar at hc
  cases hg : ctx.get? x with
  | none => rw [hg] at hc; cases hc
  | some v =>
    rw [hg] at hc
    by_cases hnp : (v.noRc || v.persistent) = true
    · simp [hnp, pure, Except.pure] at hc; cases hc; exact hs
    · simp only [hnp, Bool.false_eq_true, ↓reduceIte] at hc
      by_cases hn0 : (n == 0) = true
      · simp [hn0, pure, Except.pure] at hc; cases hc; exact hs
      · simp only [hn0, Bool.false_eq_true, ↓reduceIte] at hc
        by_cases hlt : v.owned < n
        · simp [hlt] at hc
        · simp only [hlt, ↓reduceIte, pure, Except.pure] at hc
          let v' : RcVar := {
            id := v.id, ty := v.ty, noRc := v.noRc, persistent := v.persistent,
            owned := v.owned - n, borrowed := v.borrowed, parent? := v.parent?,
            excl := if (v.owned - n == 0) = true then false else v.excl,
            resetTok := if (v.owned - n == 0) = true then false else v.resetTok }
          have hvm := (RcCtx.get?_mem hg).1
          have hnr1 := noRcCorrect_put' (v := v') hs.1 hs.2.1 (fun hno => hs.2.1 v hvm hno)
          have hnbp1 := noBorrowParent_put (v := v') hs.1 hs.2.2.2 (fun hb => hs.2.2.2 v hvm hb)
          have hnd1 := RcCtx.put_nodup hs.1 v'
          have hsbp_put : SharedBoolPreds (ctx.put v') := by
            intro p hp
            obtain ⟨vb, hgb, hvbno⟩ := hs.2.2.1 p hp
            by_cases hp1 : (p.1 == v'.id) = true
            · have hvbe := rcVar_eq_of_mem_nodup hs.1 (RcCtx.get?_mem hgb).1 hvm
                ((RcCtx.get?_mem hgb).2.trans (beq_iff_eq.mp hp1))
              have hno' : v'.noRc = true := by dsimp only [v']; rw [← hvbe]; exact hvbno
              exact ⟨v', by simp [RcCtx.put_get? hs.1, hp1], hno'⟩
            · exact ⟨vb, by simp [RcCtx.put_get? hs.1, hp1, hgb], hvbno⟩
          split at hc <;> cases hc
          · exact ⟨invalidateChildren_nodup' (ctx.put v') x hnd1,
              noRcCorrect_invalidateChildren' hnr1 x,
              sharedBoolPreds_invalidateChildren' hnd1 hsbp_put x,
              noBorrowParent_invalidateChildren hnbp1 x⟩
          · exact ⟨hnd1, hnr1, hsbp_put, hnbp1⟩

/-- Lookup ID preservation through `RcCtx.consumeVar`. -/
public theorem get?_isSome_consumeVar {ctx ctx1 : RcCtx} {x n : Nat}
    (h : ctx.consumeVar x n = Except.ok ctx1) (id : Nat)
    (hs : (ctx.get? id).isSome = true) : (ctx1.get? id).isSome = true := by
  unfold RcCtx.consumeVar at h
  cases hg : ctx.get? x with
  | none => rw [hg] at h; cases h
  | some v =>
    rw [hg] at h
    by_cases hnp : (v.noRc || v.persistent) = true
    · simp [hnp, pure, Except.pure] at h; cases h; exact hs
    · simp only [hnp, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hn0 : (n == 0) = true
      · simp [hn0, pure, Except.pure] at h; cases h; exact hs
      · simp only [hn0, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hlt : v.owned < n
        · simp [hlt] at h
        · simp only [hlt, ↓reduceIte, pure, Except.pure] at h
          let v' : RcVar := {
            id := v.id, ty := v.ty, noRc := v.noRc, persistent := v.persistent,
            owned := v.owned - n, borrowed := v.borrowed, parent? := v.parent?,
            excl := if (v.owned - n == 0) = true then false else v.excl,
            resetTok := if (v.owned - n == 0) = true then false else v.resetTok }
          have hp := get?_isSome_put ctx v' id hs
          split at h <;> cases h
          · exact get?_isSome_invalidateChildren (ctx.put v') x id hp
          · exact hp

/-- Static invariants preserved through `RcCtx.consumeArg`. -/
public theorem ctxStaticInv_consumeArg {ctx ctx1 : RcCtx} (hs : CtxStaticInv ctx)
    {y : LcArg} (hc : ctx.consumeArg y = Except.ok ctx1) :
    CtxStaticInv ctx1 ∧ (∀ id, (ctx.get? id).isSome = true → (ctx1.get? id).isSome = true) := by
  cases y with
  | erased => simp [RcCtx.consumeArg, pure, Except.pure] at hc; cases hc; exact ⟨hs, fun _ h => h⟩
  | var id => exact ⟨ctxStaticInv_consumeVar hs hc, fun z hz => get?_isSome_consumeVar hc z hz⟩

/-- Static invariants preserved through `RcCtx.applyArgs`. -/
public theorem ctxStaticInv_applyArgs {ctx ctx1 : RcCtx} (hs : CtxStaticInv ctx)
    {as : List LcArg} {bs : List Bool} (ha : ctx.applyArgs as bs = Except.ok ctx1) :
    CtxStaticInv ctx1 ∧ (∀ id, (ctx.get? id).isSome = true → (ctx1.get? id).isSome = true) :=
  ⟨applyArgs_inv CtxStaticInv (fun h hc => ctxStaticInv_consumeVar h hc) hs ha,
    fun id hsome => applyArgs_inv (fun c => (c.get? id).isSome = true)
      (fun h hc => get?_isSome_consumeVar hc id h) hsome ha⟩

/-- `CtxStaticInv` preserved through `RcCtx.bindOwned`. -/
public theorem ctxStaticInv_bindOwned {ctx : RcCtx} (hs : CtxStaticInv ctx)
    {x : Nat} (hfr : binderFreshOwned ctx x = true) (ty : LcTy)
    (excl pers rtok : Bool) : CtxStaticInv (ctx.bindOwned x ty excl pers rtok) := by
  have hsp : ∀ p ∈ ctx.sharedPreds, p.1 ≠ x := fun p hp heq => by
    have ha := (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp hfr).1).2
    have hm := List.all_eq_true.mp ha p hp
    simp [heq] at hm
  exact ⟨RcCtx.put_nodup hs.1 _,
    noRcCorrect_put' hs.1 hs.2.1 (fun h => by
      dsimp only [RcCtx.bindOwned] at h; simp at h ⊢; exact h),
    sharedBoolPreds_put_fresh hs.1 hs.2.2.1 hsp,
    noBorrowParent_put hs.1 hs.2.2.2 (fun _ => rfl)⟩

/-- `CtxStaticInv` preserved through `RcCtx.bindBorrowed`. -/
public theorem ctxStaticInv_bindBorrowed {ctx : RcCtx} (hs : CtxStaticInv ctx)
    {x : Nat} (hfr : binderFreshOwned ctx x = true) (ty : LcTy)
    (p? : Option Nat) (pers : Bool) : CtxStaticInv (ctx.bindBorrowed x ty p? pers) := by
  have hsp : ∀ p ∈ ctx.sharedPreds, p.1 ≠ x := fun p hp heq => by
    have ha := (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp hfr).1).2
    have hm := List.all_eq_true.mp ha p hp
    simp [heq] at hm
  refine ⟨RcCtx.put_nodup hs.1 _,
    noRcCorrect_put' hs.1 hs.2.1 (fun h => by
      dsimp only [RcCtx.bindBorrowed] at h; simp at h ⊢; exact h),
    sharedBoolPreds_put_fresh hs.1 hs.2.2.1 hsp, noBorrowParent_put hs.1 hs.2.2.2 fun hb => ?_⟩
  simp only at hb ⊢
  have hcond : (!ty.needsRc || pers) = true := by
    revert hb; cases !ty.needsRc <;> cases pers <;> simp
  simp [hcond]

private theorem binderFreshOwned_consumeVar_noClean {ctx : RcCtx}
    (hnd : (ctx.vars.map RcVar.id).Nodup) {x n y : Nat} {ctx' : RcCtx}
    (hcons : ctx.consumeVar x n = Except.ok ctx')
    (hfr : binderFreshOwned ctx y = true) : binderFreshOwned ctx' y = true := by
  unfold RcCtx.consumeVar at hcons
  cases hg : ctx.get? x with
  | none => rw [hg] at hcons; cases hcons
  | some v =>
    rw [hg] at hcons
    by_cases hnp : (v.noRc || v.persistent) = true
    · simp [hnp, pure, Except.pure] at hcons; cases hcons; exact hfr
    · simp only [hnp, Bool.false_eq_true, ↓reduceIte] at hcons
      by_cases hn0 : (n == 0) = true
      · simp [hn0, pure, Except.pure] at hcons; cases hcons; exact hfr
      · simp only [hn0, Bool.false_eq_true, ↓reduceIte] at hcons
        by_cases hlt : v.owned < n
        · simp [hlt] at hcons
        · simp only [hlt, ↓reduceIte, pure, Except.pure] at hcons
          let v' : RcVar := {
            id := v.id, ty := v.ty, noRc := v.noRc, persistent := v.persistent,
            owned := v.owned - n, borrowed := v.borrowed, parent? := v.parent?,
            excl := if (v.owned - n == 0) = true then false else v.excl,
            resetTok := if (v.owned - n == 0) = true then false else v.resetTok }
          have hfr_a := Bool.and_eq_true _ _ |>.mp hfr
          have hfr_b := Bool.and_eq_true _ _ |>.mp hfr_a.1
          have hput : binderFreshOwned (ctx.put v') y = true := by
            unfold binderFreshOwned
            have hp1 : (ctx.put v').vars.all (fun u => u.parent? != some y) = true := by
              apply List.all_eq_true.mpr; intro u hu
              rcases (RcCtx.put_mem_iff hnd).mp hu with rfl | ⟨hum, _⟩
              · exact List.all_eq_true.mp hfr_b.1 v (RcCtx.get?_mem hg).1
              · exact List.all_eq_true.mp hfr_b.1 u hum
            have hget1 : (match (ctx.put v').get? y with
                | none => true | some u => !u.isLive) = true := by
              rw [RcCtx.put_get? hnd]
              by_cases hy : (y == v'.id) = true
              · simp only [hy, ↓reduceIte]
                have hyx : y = x := (beq_iff_eq.mp hy).trans (RcCtx.get?_mem hg).2
                rw [hyx] at hfr_a
                have hlive0 : (!v.isLive) = true := by rw [hg] at hfr_a; exact hfr_a.2
                exfalso
                have hn_pos : 0 < n := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hn0
                have hv0 : v.owned = 0 := by
                  by_cases hgt : v.owned > 0
                  · exfalso; simp [RcVar.isLive, hgt] at hlive0
                  · omega
                omega
              · simp only [hy, Bool.false_eq_true, ↓reduceIte]; exact hfr_a.2
            have hsp1 : (ctx.put v').sharedPreds.all
                (fun p => p.1 != y && p.2 != y) = true := hfr_b.2
            rw [hp1, hsp1]; exact hget1
          split at hcons <;> cases hcons
          · exact binderFreshOwned_invalidateChildren' (RcCtx.put_nodup hnd v') hput
          · exact hput

private theorem binderFreshOwned_applyArgs' {ctx ctx1 : RcCtx}
    (hnd : (ctx.vars.map RcVar.id).Nodup) {as : List LcArg} {bs : List Bool}
    (ha : ctx.applyArgs as bs = Except.ok ctx1) {x : Nat} (hfr : binderFreshOwned ctx x = true) :
    binderFreshOwned ctx1 x = true :=
  (applyArgs_inv (fun c => (c.vars.map RcVar.id).Nodup ∧ binderFreshOwned c x = true)
    (fun h hc => ⟨consumeVar_nodup h.1 hc, binderFreshOwned_consumeVar_noClean h.1 hc h.2⟩)
    ⟨hnd, hfr⟩ ha).2

/-- Static invariants preserved through `checkVal`. -/
public theorem checkVal_static_invs {env : RcModEnv} {ctx ctx' : RcCtx} {x : Nat} {ty : LcTy}
    {v : LcVal} (hs : CtxStaticInv ctx) (hwf : perceusValWf env ctx x ty v = true)
    (hcv : checkVal env ctx x ty v = Except.ok ctx') :
    CtxStaticInv ctx' ∧ (∀ id, (ctx.get? id).isSome = true → (ctx'.get? id).isSome = true) := by
  unfold perceusValWf at hwf
  obtain ⟨hfr, hwfv⟩ := Bool.and_eq_true _ _ |>.mp hwf
  cases v with
  | lit l =>
    cases l with
    | nat n =>
      unfold checkVal at hcv
      by_cases h1 : (!ty.needsRc) = true <;> by_cases h2 : n < 2 ^ 63 <;>
        simp [h1, h2, pure, Except.pure] at hcv <;> cases hcv <;>
        exact ⟨ctxStaticInv_bindOwned hs hfr ty false _ false,
          fun id hid => get?_isSome_put _ _ id hid⟩
    | str _ => simp at hwfv
    | scalar _ =>
      simp only [checkVal, pure, Except.pure, Except.ok.injEq] at hcv; cases hcv
      exact ⟨ctxStaticInv_bindOwned hs hfr ty false false false,
        fun id hid => get?_isSome_put _ _ id hid⟩
  | erased =>
    simp only [checkVal, pure, Except.pure, Except.ok.injEq] at hcv; cases hcv
    exact ⟨ctxStaticInv_bindOwned hs hfr ty false false false,
      fun id hid => get?_isSome_put _ _ id hid⟩
  | ctor ci as =>
    unfold checkVal at hcv
    by_cases hsc : ci.isScalar = true
    · simp only [hsc, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hcv; cases hcv
      exact ⟨ctxStaticInv_bindOwned hs hfr ty false false false,
        fun id hid => get?_isSome_put _ _ id hid⟩
    · simp only [hsc, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure] at hcv
      cases ha : ctx.applyArgs as (List.replicate as.length false) with
      | error _ => rw [ha] at hcv; cases hcv
      | ok ctx1 =>
        rw [ha] at hcv; cases hcv
        obtain ⟨hs1, hk1⟩ := ctxStaticInv_applyArgs hs ha
        have hfr1 := binderFreshOwned_applyArgs' hs.1 ha hfr
        exact ⟨ctxStaticInv_bindOwned hs1 hfr1 ty true false false,
          fun id hid => get?_isSome_put _ _ id (hk1 id hid)⟩
  | oproj i obj =>
    simp only [checkVal, bind, Except.bind, pure, Except.pure] at hcv
    cases hpb : ctx.projBacking obj with
    | error _ => rw [hpb] at hcv; cases hcv
    | ok pr =>
      rw [hpb] at hcv; cases hcv
      exact ⟨ctxStaticInv_bindBorrowed hs hfr ty pr.1 pr.2,
        fun id hid => get?_isSome_put _ _ id hid⟩
  | uproj _ obj | sproj _ _ obj | unbox obj =>
    simp only [checkVal, bind, Except.bind, pure, Except.pure] at hcv
    cases hcl : ctx.checkLive obj with
    | error _ => rw [hcl] at hcv; cases hcv
    | ok _ =>
      rw [hcl] at hcv; cases hcv
      exact ⟨ctxStaticInv_bindOwned hs hfr ty false false false,
        fun id hid => get?_isSome_put _ _ id hid⟩
  | box _ y =>
    simp only [checkVal, bind, Except.bind, pure, Except.pure] at hcv
    cases hcl : ctx.checkLive y with
    | error _ => rw [hcl] at hcv; cases hcv
    | ok _ =>
      rw [hcl] at hcv; cases hcv
      exact ⟨ctxStaticInv_bindOwned hs hfr ty true false false,
        fun id hid => get?_isSome_put _ _ id hid⟩
  | isShared y =>
    simp only [checkVal, bind, Except.bind, pure, Except.pure] at hcv
    cases hcl : ctx.checkLive y with
    | error _ => rw [hcl] at hcv; cases hcv
    | ok _ =>
      rw [hcl] at hcv; cases hcv
      have hty : ty = LcTy.uint8 :=
        (lcTy_beq_iff ty LcTy.uint8).mp (Bool.and_eq_true _ _ |>.mp hwfv).1
      subst hty
      have hs1 := ctxStaticInv_bindOwned hs hfr LcTy.uint8 false false false
      have hgetx : (ctx.bindOwned x LcTy.uint8).get? x =
          some { id := x, ty := LcTy.uint8, noRc := true, persistent := false, owned := 0 } := by
        simp [RcCtx.bindOwned, RcCtx.put_get? hs.1, LcTy.needsRc]
      refine ⟨⟨hs1.1, hs1.2.1, fun p hp => ?_, hs1.2.2.2⟩,
        fun id hid => get?_isSome_put _ _ id hid⟩
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact ⟨_, hgetx, rfl⟩
      · exact hs1.2.2.1 p hp'
  | reset _ _ | reuse _ _ _ _ | pap _ _ | ap _ _ => simp at hwfv
  | fap f as =>
    unfold checkVal at hcv
    dsimp only at hcv
    cases hdecls : env.decls.find? (fun d => d.1 == f) with
    | some dinfo =>
      simp only [hdecls] at hcv
      rcases dinfo with ⟨_, borrows, _, _, isConst⟩
      by_cases hic : (isConst && as.isEmpty) = true
      · simp only [hic, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hcv; cases hcv
        exact ⟨ctxStaticInv_bindOwned hs hfr ty false true false,
          fun id hid => get?_isSome_put _ _ id hid⟩
      · simp only [hic, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
          at hcv
        cases ha : ctx.applyArgs as borrows with
        | error _ => rw [ha] at hcv; cases hcv
        | ok ctx1 =>
          rw [ha] at hcv; cases hcv
          obtain ⟨hs1, hk1⟩ := ctxStaticInv_applyArgs hs ha
          have hfr1 := binderFreshOwned_applyArgs' hs.1 ha hfr
          exact ⟨ctxStaticInv_bindOwned hs1 hfr1 ty false false false,
            fun id hid => get?_isSome_put _ _ id (hk1 id hid)⟩
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
          rw [ha] at hcv; dsimp only at hcv
          obtain ⟨hs1, hkeep1⟩ := ctxStaticInv_applyArgs hs ha
          have hfr1 := binderFreshOwned_applyArgs' hs.1 ha hfr
          cases retKind with
          | owned =>
            cases hcv
            exact ⟨ctxStaticInv_bindOwned hs1 hfr1 ty false false false,
              fun id hid => get?_isSome_put _ _ id (hkeep1 id hid)⟩
          | persistent =>
            cases hcv
            exact ⟨ctxStaticInv_bindOwned hs1 hfr1 ty false true false,
              fun id hid => get?_isSome_put _ _ id (hkeep1 id hid)⟩
          | borrowed idx =>
            dsimp only at hcv
            cases has : as[idx]? with
            | none =>
              rw [has] at hcv; cases hcv
              exact ⟨ctxStaticInv_bindBorrowed hs1 hfr1 ty none false,
                fun id hid => get?_isSome_put _ _ id (hkeep1 id hid)⟩
            | some a =>
              rw [has] at hcv
              cases a with
              | erased =>
                cases hcv
                exact ⟨ctxStaticInv_bindBorrowed hs1 hfr1 ty none false,
                  fun id hid => get?_isSome_put _ _ id (hkeep1 id hid)⟩
              | var src =>
                dsimp only at hcv
                cases hpb : ctx1.projBacking src with
                | error _ => rw [hpb] at hcv; cases hcv
                | ok bp =>
                  rw [hpb] at hcv; cases hcv
                  exact ⟨ctxStaticInv_bindBorrowed hs1 hfr1 ty bp.1 bp.2,
                    fun id hid => get?_isSome_put _ _ id (hkeep1 id hid)⟩

/-- Static context invariants for `baseCtx.bindParams ps`. -/
public theorem bindParams_static_invs {ctx : RcCtx} (hs : CtxStaticInv ctx)
    {ps : List LcParam} (hndP : (ps.map (·.id)).Nodup)
    (hfr : ps.all (binderFreshOwned ctx ·.id) = true) :
    CtxStaticInv (ctx.bindParams ps) ∧
    (∀ id, (ctx.get? id).isSome = true → ((ctx.bindParams ps).get? id).isSome = true) := by
  induction ps generalizing ctx with
  | nil => exact ⟨hs, fun _ h => h⟩
  | cons q rest ih =>
    simp only [RcCtx.bindParams, List.foldl_cons]
    simp only [List.map_cons, List.nodup_cons] at hndP
    have hqfr := List.all_eq_true.mp hfr q List.mem_cons_self
    have hrestfr : rest.all (binderFreshOwned ctx ·.id) = true :=
      List.all_eq_true.mpr fun r hr => List.all_eq_true.mp hfr r (List.mem_cons_of_mem _ hr)
    let ctx1 := if q.borrow = true then ctx.bindBorrowed q.id q.ty else ctx.bindOwned q.id q.ty
    have hs1 : CtxStaticInv ctx1 := by
      dsimp only [ctx1]; split
      · exact ctxStaticInv_bindBorrowed hs hqfr q.ty none false
      · exact ctxStaticInv_bindOwned hs hqfr q.ty false false false
    have hkeep1 : ∀ id, (ctx.get? id).isSome = true → (ctx1.get? id).isSome = true := by
      intro id hid
      dsimp only [ctx1]; split <;> exact get?_isSome_put _ _ id hid
    have hfr1 : rest.all (binderFreshOwned ctx1 ·.id) = true := by
      apply List.all_eq_true.mpr; intro r hr
      have hr0 := List.all_eq_true.mp hrestfr r hr
      have hne : r.id ≠ q.id := fun heq => hndP.1 (heq ▸ List.mem_map.mpr ⟨r, hr, rfl⟩)
      unfold binderFreshOwned at hr0 ⊢
      have hr0a := Bool.and_eq_true _ _ |>.mp hr0
      have hr0b := Bool.and_eq_true _ _ |>.mp hr0a.1
      have hvars1 : ctx1.vars.all (fun u => u.parent? != some r.id) = true := by
        apply List.all_eq_true.mpr; intro u hu
        dsimp only [ctx1] at hu
        split at hu <;> rcases (RcCtx.put_mem_iff hs.1).mp hu with rfl | ⟨hum, _⟩
        · simp
        · exact List.all_eq_true.mp hr0b.1 u hum
        · simp
        · exact List.all_eq_true.mp hr0b.1 u hum
      have hsp1 : ctx1.sharedPreds.all (fun p => p.1 != r.id && p.2 != r.id) = true := by
        dsimp only [ctx1]; split <;> exact hr0b.2
      have hget1 : (match ctx1.get? r.id with | none => true | some v => !v.isLive) = true := by
        have hneq : (r.id == q.id) = false := beq_false_of_ne hne
        dsimp only [ctx1]
        cases hqb : q.borrow <;>
          simp only [Bool.false_eq_true, ↓reduceIte, RcCtx.bindOwned,
            RcCtx.bindBorrowed, RcCtx.put_get? hs.1, hneq] <;>
          exact hr0a.2
      rw [hvars1, hsp1]; exact hget1
    obtain ⟨hsr, hkr⟩ := ih hs1 hndP.2 hfr1
    exact ⟨hsr, fun id hid => hkr id (hkeep1 id hid)⟩

/-- `CtxStaticInv` preserved through `RcCtx.markScalarBranch`. -/
public theorem ctxStaticInv_markScalarBranch {ctx : RcCtx} (hs : CtxStaticInv ctx) (x : Nat) :
    CtxStaticInv (ctx.markScalarBranch x) ∧
    (∀ id, (ctx.get? id).isSome = true → ((ctx.markScalarBranch x).get? id).isSome = true) := by
  unfold RcCtx.markScalarBranch
  cases hg : ctx.get? x with
  | none => exact ⟨hs, fun _ h => h⟩
  | some vx =>
    by_cases hty : (vx.ty == .tobject || vx.ty == .tagged) = true
    · simp only [hty, ↓reduceIte]
      let vx' : RcVar := { id := vx.id, ty := vx.ty, noRc := true }
      have hnd1 := invalidateChildren_nodup' (ctx.put vx') x (RcCtx.put_nodup hs.1 vx')
      have hnr1 := noRcCorrect_invalidateChildren'
        (noRcCorrect_put' (v := vx') hs.1 hs.2.1 (fun h => by simp [vx'] at h)) x
      have hsbp1 : SharedBoolPreds ((ctx.put vx').invalidateChildren x) := by
        intro p hp
        simp only [RcCtx.invalidateChildren, List.mem_filter] at hp
        obtain ⟨wb, hgb0, hno0⟩ := hs.2.2.1 p hp.1
        by_cases hp1x : p.1 = vx.id
        · let v1 := if (vx'.parent? == some x) = true then
            { vx' with borrowed := false, parent? := none } else vx'
          have hv1m : v1 ∈ ((ctx.put vx').invalidateChildren x).vars :=
            List.mem_map.mpr ⟨vx', (RcCtx.put_mem_iff hs.1).mpr (Or.inl rfl), rfl⟩
          have hv1id : v1.id = p.1 := by dsimp only [v1]; split <;> simp [vx', hp1x]
          have hv1no : v1.noRc = true := by dsimp only [v1]; split <;> rfl
          exact ⟨v1, hv1id ▸ (RcCtx.mem_get?_iff hnd1).mpr hv1m, hv1no⟩
        · let v1 := if (wb.parent? == some x) = true then
            { wb with borrowed := false, parent? := none } else wb
          have hwm : wb ∈ (ctx.put vx').vars :=
            (RcCtx.put_mem_iff hs.1).mpr (Or.inr ⟨(RcCtx.get?_mem hgb0).1,
              (RcCtx.get?_mem hgb0).2.symm ▸ hp1x⟩)
          have hv1m : v1 ∈ ((ctx.put vx').invalidateChildren x).vars :=
            List.mem_map.mpr ⟨wb, hwm, rfl⟩
          have hv1id : v1.id = p.1 := by dsimp only [v1]; split <;> exact (RcCtx.get?_mem hgb0).2
          have hv1no : v1.noRc = true := by dsimp only [v1]; split <;> exact hno0
          exact ⟨v1, hv1id ▸ (RcCtx.mem_get?_iff hnd1).mpr hv1m, hv1no⟩
      have hnbp1 := noBorrowParent_invalidateChildren
        (noBorrowParent_put (v := vx') hs.1 hs.2.2.2 (fun _ => rfl)) x
      exact ⟨⟨hnd1, hnr1, hsbp1, hnbp1⟩,
        fun id hid => get?_isSome_invalidateChildren _ x id (get?_isSome_put _ _ id hid)⟩
    · simp only [hty, Bool.false_eq_true, ↓reduceIte]; exact ⟨hs, fun _ h => h⟩

/-- `CtxStaticInv` preserved through `RcCtx.markExcl`. -/
public theorem ctxStaticInv_markExcl {ctx : RcCtx} (hs : CtxStaticInv ctx) (x : Nat) :
    CtxStaticInv (ctx.markExcl x) ∧
    (∀ id, (ctx.get? id).isSome = true → ((ctx.markExcl x).get? id).isSome = true) := by
  unfold RcCtx.markExcl
  cases hg : ctx.get? x with
  | none => exact ⟨hs, fun _ h => h⟩
  | some v =>
    dsimp only
    by_cases hcond : (!v.noRc && !v.persistent && v.owned == 1) = true
    · simp only [hcond, ↓reduceIte]
      let v' : RcVar := {
        id := v.id, ty := v.ty, noRc := v.noRc, persistent := v.persistent,
        owned := v.owned, borrowed := v.borrowed, parent? := v.parent?, excl := true,
        resetTok := v.resetTok }
      have hnd1 := RcCtx.put_nodup hs.1 v'
      have hnr1 := noRcCorrect_put' (v := v') hs.1 hs.2.1
        (fun hno => hs.2.1 v (RcCtx.get?_mem hg).1 hno)
      have hsbp1 : SharedBoolPreds (ctx.put v') := by
        intro p hp
        obtain ⟨vb, hgb, hvbno⟩ := hs.2.2.1 p hp
        by_cases hp1 : (p.1 == v'.id) = true
        · have hvmeq := rcVar_eq_of_mem_nodup hs.1 (RcCtx.get?_mem hgb).1 (RcCtx.get?_mem hg).1
            ((RcCtx.get?_mem hgb).2.trans (beq_iff_eq.mp hp1))
          have hno' : v'.noRc = true := by dsimp only [v']; rw [← hvmeq]; exact hvbno
          exact ⟨v', by simp [RcCtx.put_get? hs.1, hp1], hno'⟩
        · exact ⟨vb, by simp [RcCtx.put_get? hs.1, hp1, hgb], hvbno⟩
      have hnbp1 := noBorrowParent_put (v := v') hs.1 hs.2.2.2
        (fun hb => hs.2.2.2 v (RcCtx.get?_mem hg).1 hb)
      exact ⟨⟨hnd1, hnr1, hsbp1, hnbp1⟩, fun id hid => get?_isSome_put _ _ id hid⟩
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]; exact ⟨hs, fun _ h => h⟩

/-- `CtxStaticInv` preserved through `inc`. -/
public theorem ctxStaticInv_inc {ctx : RcCtx} (hs : CtxStaticInv ctx) {x n : Nat}
    {v : RcVar} (hg : ctx.get? x = some v) :
    let v' : RcVar := {
      id := v.id, ty := v.ty, noRc := v.noRc, persistent := v.persistent,
      owned := v.owned + n, borrowed := v.borrowed, parent? := v.parent?,
      resetTok := v.resetTok }
    CtxStaticInv (ctx.put v') ∧
    (∀ id, (ctx.get? id).isSome = true → ((ctx.put v').get? id).isSome = true) := by
  intro v'
  have hnd1 := RcCtx.put_nodup hs.1 v'
  have hnr1 := noRcCorrect_put' (v := v') hs.1 hs.2.1
    (fun hno => hs.2.1 v (RcCtx.get?_mem hg).1 hno)
  have hsbp1 : SharedBoolPreds (ctx.put v') := by
    intro p hp
    obtain ⟨vb, hgb, hvbno⟩ := hs.2.2.1 p hp
    by_cases hp1 : (p.1 == v'.id) = true
    · have hvmeq := rcVar_eq_of_mem_nodup hs.1 (RcCtx.get?_mem hgb).1 (RcCtx.get?_mem hg).1
        ((RcCtx.get?_mem hgb).2.trans (beq_iff_eq.mp hp1))
      have hno' : v'.noRc = true := by dsimp only [v']; rw [← hvmeq]; exact hvbno
      exact ⟨v', by simp [RcCtx.put_get? hs.1, hp1], hno'⟩
    · exact ⟨vb, by simp [RcCtx.put_get? hs.1, hp1, hgb], hvbno⟩
  have hnbp1 := noBorrowParent_put (v := v') hs.1 hs.2.2.2
    (fun hb => hs.2.2.2 v (RcCtx.get?_mem hg).1 hb)
  exact ⟨⟨hnd1, hnr1, hsbp1, hnbp1⟩, fun id hid => get?_isSome_put _ _ id hid⟩

end StaticAndApplyArgsHelpers

end LeanQbe.T.LeanLCNF.Sem
