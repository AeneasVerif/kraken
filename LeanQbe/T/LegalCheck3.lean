module

public import LeanQbe.T.LegalCheck2

/-!
# Target legality proofs for `LeanQbe.T.Legal` (Part 3: `legalOp_isLegal`, `Func.legal_isLegal`)

Proves `legalOp_isLegal`, `legalExpr_isLegal_wf`, `Func.legal_isLegal`, and `Fn.legal_isLegal`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

section LegalIsLegal

private theorem ArgRel_single {target : LegalTarget} {G : Ctx K (LVar target K)} {t : Ty}
    {x : Tup (Arg K) [t]} {y : Tup (Arg (LVar target K)) [t]}
    (h : TRel (ArgRel G) x y) : ArgRel G t x.1 y.1 := by
  rcases x with ⟨a₁, ⟨⟩⟩; rcases y with ⟨a₂, ⟨⟩⟩; cases h with | cons h1 _ => exact h1

private theorem ArgRel_pair {target : LegalTarget} {G : Ctx K (LVar target K)} {t₁ t₂ : Ty}
    {x : Tup (Arg K) [t₁, t₂]} {y : Tup (Arg (LVar target K)) [t₁, t₂]}
    (h : TRel (ArgRel G) x y) : ArgRel G t₁ x.1 y.1 ∧ ArgRel G t₂ x.2.1 y.2.1 := by
  rcases x with ⟨a₁, b₁, ⟨⟩⟩; rcases y with ⟨a₂, b₂, ⟨⟩⟩
  cases h with | cons h1 h2 => cases h2 with | cons h3 _ => exact ⟨h1, h3⟩

private theorem ArgRel_triple {target : LegalTarget} {G : Ctx K (LVar target K)} {t₁ t₂ t₃ : Ty}
    {x : Tup (Arg K) [t₁, t₂, t₃]} {y : Tup (Arg (LVar target K)) [t₁, t₂, t₃]}
    (h : TRel (ArgRel G) x y) :
    ArgRel G t₁ x.1 y.1 ∧ ArgRel G t₂ x.2.1 y.2.1 ∧ ArgRel G t₃ x.2.2.1 y.2.2.1 := by
  rcases x with ⟨a₁, b₁, c₁, ⟨⟩⟩; rcases y with ⟨a₂, b₂, c₂, ⟨⟩⟩
  cases h with | cons h1 h2 => cases h2 with | cons h3 h4 => cases h4 with | cons h5 _ => exact ⟨h1, h3, h5⟩

private theorem not_hasFloat_pair {a b : Ty} (h : (!(Ty.pair a b).hasFloat) = true) :
    (!a.hasFloat) = true ∧ (!b.hasFloat) = true := by
  cases ha : a.hasFloat <;> cases hb : b.hasFloat <;> simp [Ty.hasFloat, ha, hb] at h ⊢

private theorem dite_pred {α : Type} {p : Prop} [Decidable p] {t : p → α} {e : ¬p → α}
    {P : α → Prop} (ht : ∀ h, P (t h)) (he : ∀ h, P (e h)) : P (dite p t e) := by
  by_cases h : p
  · rw [dite_eq_left h]; exact ht h
  · rw [dite_eq_right h]; exact he h

theorem legalOp_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) {Γ : List (Ty × VarKind)} {LG : Ctx K (LVar target K)}
    (hc : CLegal target Γ LG) {ts : List Ty} {op₁ : Op K ts} {op₂ : Op (LVar target K) ts}
    (hop : OpRel LG op₁ op₂) (hsupp : target.supportsOpCode op₁.code = true) (nv₁ : Nat := 0)
    {k : Tup (LVar target K) ts → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' res => ∀ t v₂, (∃ v₁, ⟨t, v₁, v₂⟩ ∈ Tup.zip (Tup.levels ts nv₁) res) → ArgsNormal target Γ' v₂) k) :
    (toTFlat (legalOp target op₂ k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hcont1 : ∀ {u : Ty} (k' : Tup (LVar target K) [u] → Expr K KL rs),
      IsLegalCont target Γ Δ (fun Γ' res => ∀ t v₂, (∃ v₁, ⟨t, v₁, v₂⟩ ∈ Tup.zip (Tup.levels [u] nv₁) res) → ArgsNormal target Γ' v₂) k' →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) (fun r => k' (r, ())) := by
    intro u k' hk' Γ' r hExt hr
    exact hk' Γ' (r, ()) hExt fun t v₂ ⟨v₁, hm⟩ => by
      simp only [Tup.levels_cons, Tup.levels_nil, Tup.zip] at hm
      rcases List.mem_cons.1 hm with ⟨rfl, rfl, rfl⟩ | hm'
      · exact hr
      · cases hm'
  have hcont2 : ∀ {u₁ u₂ : Ty} (k' : Tup (LVar target K) [u₁, u₂] → Expr K KL rs),
      IsLegalCont target Γ Δ (fun Γ' res => ∀ t v₂, (∃ v₁, ⟨t, v₁, v₂⟩ ∈ Tup.zip (Tup.levels [u₁, u₂] nv₁) res) → ArgsNormal target Γ' v₂) k' →
      ∀ (Γ' : List (Ty × VarKind)) (r₁ : LVar target K u₁) (r₂ : LVar target K u₂),
        CtxExtends Γ Γ' → ArgsNormal target Γ' r₁ → ArgsNormal target Γ' r₂ →
        (toTFlat (k' (r₁, r₂, ())) Γ'.length Δ.length).isLegal target Γ' Δ = true := by
    intro u₁ u₂ k' hk' Γ' r₁ r₂ hExt hr₁ hr₂
    exact hk' Γ' (r₁, r₂, ()) hExt fun t v₂ ⟨v₁, hm⟩ => by
      simp only [Tup.levels_cons, Tup.levels_nil, Tup.zip] at hm
      rcases List.mem_cons.1 hm with ⟨rfl, rfl, rfl⟩ | hm'
      · exact hr₁
      · rcases List.mem_cons.1 hm' with ⟨rfl, rfl, rfl⟩ | hm''
        · exact hr₂
        · cases hm''
  have h64 := valid_mem64 hv
  rcases hop with @⟨_, _, code, args₁, args₂, hargs⟩
  dsimp only [Op.code, LegalTarget.supportsOpCode] at hsupp
  cases code with
  | copy t =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    exact hcont1 k hk Γ (legalArg target a) (CtxExtends.refl Γ) (legalArg_isNormal hc hsupp (ArgRel_single hargs))
  | add t | sub t | mul t =>
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    have ha := legalArg_isNormal hc hsupp (ArgRel_pair hargs).1
    have hb := legalArg_isNormal hc hsupp (ArgRel_pair hargs).2
    simp only [legalOp]
    by_cases hf : t.hasFloat = true
    · simp [hf, toTFlat_hlt]
    · have hff : t.hasFloat = false := Bool.eq_false_iff.mpr hf
      simp only [hff, Bool.false_eq_true, ↓reduceIte]
      refine legalBinTree_isLegal target (fun u => target.supportsTy u = true ∧ !u.hasFloat = true)
        (fun a b h => by
          have hab := h.1
          simp only [LegalTarget.supportsTy, Bool.and_eq_true] at hab
          have hf := not_hasFloat_pair h.2
          exact ⟨⟨hab.1, hf.1⟩, ⟨hab.2, hf.2⟩⟩)
        _ _ (fun _ => rfl)
        (fun a b unif _ hp hvs => by simp [LegalTarget.isLegalOp, hp, hvs])
        _ _ _ _
        (fun _ Γ' x y cont hx hy hc' => by
          refine isLegal_let_op2_normal target _ x y _ rfl (by rfl) hx hy rfl ?_
          exact hc' _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' rfl))
        (fun n hP Γ' x y cont hx hy hc' =>
          legalBitsArith_isLegal target hv hP.1 _ x y hx hy hc')
        (fun _ hP => by simp [Ty.hasFloat] at hP)
        t ⟨hsupp, by simp [hff]⟩ (legalArg target a) (legalArg target b) none ha hb (hcont1 k hk)
  | neg t =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    have ha := legalArg_isNormal hc hsupp (ArgRel_single hargs)
    simp only [legalOp]
    by_cases hf : t.hasFloat = true
    · simp [hf, toTFlat_hlt]
    · have hff : t.hasFloat = false := Bool.eq_false_iff.mpr hf
      simp only [hff, Bool.false_eq_true, ↓reduceIte]
      refine legalUnaryTree_isLegal target (fun u => target.supportsTy u = true ∧ !u.hasFloat = true)
        (fun a b h => by
          have hab := h.1
          simp only [LegalTarget.supportsTy, Bool.and_eq_true] at hab
          have hf := not_hasFloat_pair h.2
          exact ⟨⟨hab.1, hf.1⟩, ⟨hab.2, hf.2⟩⟩)
        .neg (fun u => target.vecIntOpSupported (.neg u) u false) (fun _ => rfl)
        (fun a b h hp hvs => by simp [LegalTarget.isLegalOp, hp, hvs])
        _ _ _
        (fun _ Γ' x cont hx hc' => hc' Γ' x (CtxExtends.refl Γ') hx)
        (fun n hP Γ' x cont hx hc' => by
          have hw := widenWidth_mem_of_supports hP.1
          have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
          by_cases hn0 : (n == 0) = true
          · simp only [hn0, ↓reduceIte]; exact hc' Γ' (.imm _) (CtxExtends.refl Γ') hlegW
          · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
            refine isLegal_let_op1_normal target (.neg (.bits (target.widenWidth n))) x _ rfl
              (by simp [LegalTarget.isLegalOp, hw]) hx hlegW ?_
            exact emitMaskToN_isLegal target hw (.var Γ'.length) (ArgNormal.head target Γ' hlegW)
              fun Γ'' r hExt'' hr => hc' Γ'' r ((CtxExtends.cons _ _).trans hExt'') hr)
        (fun _ hP => by simp [Ty.hasFloat] at hP)
        t ⟨hsupp, by simp [hff]⟩ (legalArg target a) ha (hcont1 k hk)
  | and t | or t | xor t =>
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    have ha := legalArg_isNormal hc hsupp (ArgRel_pair hargs).1
    have hb := legalArg_isNormal hc hsupp (ArgRel_pair hargs).2
    simp only [legalOp]
    refine legalBinTree_isLegal target (fun u => target.supportsTy u = true)
      (fun a b h => by simpa [LegalTarget.supportsTy, Bool.and_eq_true] using h)
      _ _ (fun _ => rfl)
      (fun a b unif _ hp hvs => by simp [LegalTarget.isLegalOp, hp, hvs])
      _ _ _ _
      (fun _ Γ' x y cont hx hy hc' => by
        refine isLegal_let_op2_normal target _ x y _ rfl (by rfl) hx hy rfl ?_
        exact hc' _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' rfl))
      (fun n hP Γ' x y cont hx hy hc' =>
        legalBitsArith_isLegal target hv hP _ x y hx hy hc')
      (fun f hP Γ' x y cont hx hy hc' => by
        have hf : f ∈ target.floatFmts := (by simpa [LegalTarget.supportsTy] using hP : f ∈ target.floatFmts ∧ f.width ≤ 64).1
        exact legalFloatBit2_isLegal target hv _ _
          (fun w _ hw => by simp [LegalTarget.isLegalOp, hw])
          (fun f' _ hsb hf' => by simp [LegalTarget.isLegalOp, hsb, hf'])
          (fun _ => rfl) (fun _ => rfl) f hf x y hx hy hc')
      t hsupp (legalArg target a) (legalArg target b) none ha hb (hcont1 k hk)
  | not t =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    have ha := legalArg_isNormal hc hsupp (ArgRel_single hargs)
    simp only [legalOp]
    refine legalUnaryTree_isLegal target (fun u => target.supportsTy u = true)
      (fun a b h => by simpa [LegalTarget.supportsTy, Bool.and_eq_true] using h)
      .not (fun u => target.vecIntOpSupported (.not u) u false) (fun _ => rfl)
      (fun a b _ hp hvs => by simp [LegalTarget.isLegalOp, hp, hvs])
      _ _ _
      (fun _ Γ' x cont hx hc' => by
        refine isLegal_let_op1_normal target (.not .bool) x _ rfl rfl hx rfl ?_
        exact hc' _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' rfl))
      (fun n hP Γ' x cont hx hc' => by
        have hw := widenWidth_mem_of_supports hP
        have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
        by_cases hn0 : (n == 0) = true
        · simp only [hn0, ↓reduceIte]; exact hc' Γ' (.imm _) (CtxExtends.refl Γ') hlegW
        · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
          by_cases hnw : (n == target.widenWidth n) = true
          · simp only [hnw, ↓reduceIte]
            refine isLegal_let_op1_normal target (.not (.bits (target.widenWidth n))) x _ rfl
              (by simp [LegalTarget.isLegalOp, hw]) hx hlegW ?_
            exact hc' _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' hlegW)
          · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
            refine isLegal_let_op1_normal target (.not (.bits (target.widenWidth n))) x _ rfl
              (by simp [LegalTarget.isLegalOp, hw]) hx hlegW ?_
            exact emitMaskToN_isLegal target hw (.var Γ'.length) (ArgNormal.head target Γ' hlegW)
              fun Γ'' r hExt'' hr => hc' Γ'' r ((CtxExtends.cons _ _).trans hExt'') hr)
      (fun f hP Γ' x cont hx hc' => by
        have hf : f ∈ target.floatFmts := (by simpa [LegalTarget.supportsTy] using hP : f ∈ target.floatFmts ∧ f.width ≤ 64).1
        have ⟨hfw, _⟩ := valid_float_spec hv hf
        have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
        have hlegFw : target.isLegalTy (.bits f.width) = true := by simpa [LegalTarget.isLegalTy] using hfw
        by_cases hsb : target.scalarFloatBitwise = true
        · simp only [hsb, ↓reduceIte]
          refine isLegal_let_op1_normal target (.not (.float f)) x _ rfl
            (by simp [LegalTarget.isLegalOp, hsb, hf]) hx hlegF ?_
          exact hc' _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' hlegF)
        · simp only [hsb, Bool.false_eq_true, ↓reduceIte]
          refine isLegal_let_op1_normal target (.bitcast (.float f) (.bits f.width) rfl) x _ rfl
            (by simp [LegalTarget.isLegalOp, hlegF, hlegFw, bne_iff_ne]) hx hlegFw ?_
          let Γ1 := (.bits f.width, VarKind.normal) :: Γ'
          refine isLegal_let_op1_normal target (.not (.bits f.width)) (.var Γ'.length) _ rfl
            (by simp [LegalTarget.isLegalOp, hfw]) (ArgNormal.head target Γ' hlegFw) hlegFw ?_
          let Γ2 := (.bits f.width, VarKind.normal) :: Γ1
          refine isLegal_let_op1_normal target (.bitcast (.bits f.width) (.float f) rfl) (.var Γ1.length) _ rfl
            (by simp [LegalTarget.isLegalOp, hlegFw, hlegF, bne_iff_ne]) (ArgNormal.head target Γ1 hlegFw) hlegF ?_
          exact hc' _ (.var Γ2.length)
            ((CtxExtends.cons _ _).trans ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _)))
            (ArgNormal.head target Γ2 hlegF))
      t hsupp (legalArg target a) ha (hcont1 k hk)
  | ternlog t imm =>
    rcases args₂ with ⟨a, b, c, ⟨⟩⟩
    have ha := legalArg_isNormal hc hsupp (ArgRel_triple hargs).1
    have hb := legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.1
    have hc' := legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.2
    simp only [legalOp]
    refine legalTernaryTree_isLegal target (fun u => target.supportsTy u = true)
      (fun a b h => by simpa [LegalTarget.supportsTy, Bool.and_eq_true] using h)
      (fun u => .ternlog u imm) (fun u => target.vecIntOpSupported (.ternlog u imm) u false)
      (fun _ => rfl) (fun a b _ hp hvs => by simp [LegalTarget.isLegalOp, hp, hvs])
      _ _ _
      (fun _ Γ' x y z cont hx hy hz hcont => emitTernlogBool_isLegal target x y z imm hx hy hz hcont)
      (fun n hP Γ' x y z cont hx hy hz hcont => by
        have hw := widenWidth_mem_of_supports hP
        have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
        by_cases hn0 : (n == 0) = true
        · simp only [hn0, ↓reduceIte]; exact hcont Γ' (.imm _) (CtxExtends.refl Γ') hlegW
        · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
          by_cases hst : target.scalarTernlog = true
          · simp only [hst, ↓reduceIte]
            refine isLegal_let_op3_normal target (.ternlog (.bits (target.widenWidth n)) imm) x y z _ rfl
              (by simp [LegalTarget.isLegalOp, hst, hw]) hx hy hz hlegW ?_
            exact emitMaskToN_isLegal target hw (.var Γ'.length) (ArgNormal.head target Γ' hlegW)
              fun Γ'' r hExt'' hr => hcont Γ'' r ((CtxExtends.cons _ _).trans hExt'') hr
          · simp only [hst, Bool.false_eq_true, ↓reduceIte]
            refine emitTernlogBits_isLegal target hw x y z imm hx hy hz fun Γ1 r hExt1 hr => ?_
            exact emitMaskToN_isLegal target hw r hr fun Γ2 r' hExt2 hr' => hcont Γ2 r' (hExt1.trans hExt2) hr')
      (fun f hP Γ' x y z cont hx hy hz hcont => by
        have hf : f ∈ target.floatFmts := (by simpa [LegalTarget.supportsTy] using hP : f ∈ target.floatFmts ∧ f.width ≤ 64).1
        have ⟨hfw, _⟩ := valid_float_spec hv hf
        have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
        have hlegFw : target.isLegalTy (.bits f.width) = true := by simpa [LegalTarget.isLegalTy] using hfw
        by_cases hboth : (target.scalarFloatBitwise && target.scalarTernlog) = true
        · simp only [hboth, ↓reduceIte]
          have hboth' := (Bool.and_eq_true _ _).mp hboth
          refine isLegal_let_op3_normal target (.ternlog (.float f) imm) x y z _ rfl
            (by simp [LegalTarget.isLegalOp, hboth'.1, hboth'.2, hf]) hx hy hz hlegF ?_
          exact hcont _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' hlegF)
        · simp only [hboth, Bool.false_eq_true, ↓reduceIte]
          refine isLegal_let_op1_normal target (.bitcast (.float f) (.bits f.width) rfl) x _ rfl
            (by simp [LegalTarget.isLegalOp, hlegF, hlegFw, bne_iff_ne]) hx hlegFw ?_
          let Γ1 := (.bits f.width, VarKind.normal) :: Γ'
          have h1 : CtxExtends Γ' Γ1 := CtxExtends.cons _ _
          refine isLegal_let_op1_normal target (.bitcast (.float f) (.bits f.width) rfl) y _ rfl
            (by simp [LegalTarget.isLegalOp, hlegF, hlegFw, bne_iff_ne]) (hy.mono h1) hlegFw ?_
          let Γ2 := (.bits f.width, VarKind.normal) :: Γ1
          have h2 : CtxExtends Γ1 Γ2 := CtxExtends.cons _ _
          refine isLegal_let_op1_normal target (.bitcast (.float f) (.bits f.width) rfl) z _ rfl
            (by simp [LegalTarget.isLegalOp, hlegF, hlegFw, bne_iff_ne]) (hz.mono (h1.trans h2)) hlegFw ?_
          let Γ3 := (.bits f.width, VarKind.normal) :: Γ2
          have h13 : CtxExtends Γ' Γ3 := h1.trans (h2.trans (CtxExtends.cons _ _))
          have hx3 : ArgNormal target Γ3 (.bits f.width) (.var Γ'.length) :=
            (ArgNormal.head target Γ' hlegFw).mono (h2.trans (CtxExtends.cons (.bits f.width, VarKind.normal) Γ2))
          have hy3 : ArgNormal target Γ3 (.bits f.width) (.var Γ1.length) :=
            (ArgNormal.head target Γ1 hlegFw).mono (CtxExtends.cons (.bits f.width, VarKind.normal) Γ2)
          have hz3 := ArgNormal.head target Γ2 hlegFw
          have hstep : IsLegalCont target Γ3 Δ (fun Γ'' br => ArgNormal target Γ'' (.bits f.width) br) fun br =>
              .let_ (op1 (.bitcast (.bits f.width) (.float f) rfl) br) fun (r, ()) => cont (.var r) := by
            intro Γ4 br hExt4 hbr
            refine isLegal_let_op1_normal target (.bitcast (.bits f.width) (.float f) rfl) br _ rfl
              (by simp [LegalTarget.isLegalOp, hlegFw, hlegF, bne_iff_ne]) hbr hlegF ?_
            exact hcont _ (.var Γ4.length) ((h13.trans hExt4).trans (CtxExtends.cons _ _)) (ArgNormal.head target Γ4 hlegF)
          by_cases hst : target.scalarTernlog = true
          · simp only [hst, ↓reduceIte]
            refine isLegal_let_op3_normal target (.ternlog (.bits f.width) imm) (.var Γ'.length) (.var Γ1.length) (.var Γ2.length) _ rfl
              (by simp [LegalTarget.isLegalOp, hst, hfw]) hx3 hy3 hz3 hlegFw ?_
            exact hstep _ (.var Γ3.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ3 hlegFw)
          · simp only [hst, Bool.false_eq_true, ↓reduceIte]
            exact emitTernlogBits_isLegal target hfw (.var Γ'.length) (.var Γ1.length) (.var Γ2.length) imm hx3 hy3 hz3 hstep)
      t hsupp (legalArg target a) (legalArg target b) (legalArg target c) ha hb hc' (hcont1 k hk)
  | shl t | lshr t | ashr t | rotl t | rotr t =>
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    have ha := legalArg_isNormal hc hsupp (ArgRel_pair hargs).1
    have hb := legalArg_isNormal hc hsupp (ArgRel_pair hargs).2
    simp only [legalOp]
    by_cases hf : t.hasFloat = true
    · simp [hf, toTFlat_hlt]
    · have hff : t.hasFloat = false := Bool.eq_false_iff.mpr hf
      simp only [hff, Bool.false_eq_true, ↓reduceIte]
      refine legalBinTree_isLegal target (fun u => target.supportsTy u = true ∧ !u.hasFloat = true)
        (fun a b h => by
          have hab := h.1
          simp only [LegalTarget.supportsTy, Bool.and_eq_true] at hab
          have hf := not_hasFloat_pair h.2
          exact ⟨⟨hab.1, hf.1⟩, ⟨hab.2, hf.2⟩⟩)
        _ _ (fun _ => rfl)
        (fun a b unif _ hp hvs => by simp [LegalTarget.isLegalOp, hp, hvs])
        _ _ _ _
        (fun _ Γ' x _ cont hx _ hc' => hc' Γ' x (CtxExtends.refl Γ') hx)
        (fun n hP Γ' x y cont hx hy hc' =>
          legalBitsArith_isLegal target hv hP.1 _ x y hx hy hc')
        (fun _ hP => by simp [Ty.hasFloat] at hP)
        t ⟨hsupp, by simp [hff]⟩ (legalArg target a) (legalArg target b) (some b) ha hb (hcont1 k hk)
  | fshl n =>
    rcases args₂ with ⟨a, b, c, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_triple hargs).1).1
    have hb := (legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.1).1
    have hc' := (legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.2).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]; exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op3_normal target (.fshl (target.widenWidth n)) (legalArg target a).1 (legalArg target b).1 (legalArg target c).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hc' hlegW ?_
        exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_isLegal target hv hw (legalArg target c).1 hc' fun Γ1 cm hExt1 hcm => ?_
        refine isLegal_let_op2_normal target (.sub (.bits (target.widenWidth n))) (.imm _) cm _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) hlegW hcm hlegW ?_
        let Γ2 := (.bits (target.widenWidth n), VarKind.normal) :: Γ1
        have h12 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.shl (.bits (target.widenWidth n))) (legalArg target a).1 cm _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ha.mono h12) (hcm.mono (CtxExtends.cons _ _)) hlegW ?_
        let Γ3 := (.bits (target.widenWidth n), VarKind.normal) :: Γ2
        have h13 : CtxExtends Γ Γ3 := h12.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.lshr (.bits (target.widenWidth n))) (legalArg target b).1 (.var Γ1.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (hb.mono h13) ((ArgNormal.head target Γ1 hlegW).mono (CtxExtends.cons _ _)) hlegW ?_
        let Γ4 := (.bits (target.widenWidth n), VarKind.normal) :: Γ3
        refine isLegal_let_op2_normal target (.or (.bits (target.widenWidth n))) (.var Γ2.length) (.var Γ3.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) ((ArgNormal.head target Γ2 hlegW).mono (CtxExtends.cons _ _))
          (ArgNormal.head target Γ3 hlegW) hlegW ?_
        let Γ5 := (.bits (target.widenWidth n), VarKind.normal) :: Γ4
        have h15 : CtxExtends Γ Γ5 := h13.trans ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _))
        exact emitMaskToN_isLegal target hw (.var Γ4.length) (ArgNormal.head target Γ4 hlegW)
          fun Γ6 r hExt6 hr => hcont1 k hk Γ6 (r, ()) (h15.trans hExt6) ⟨hr, trivial⟩
  | fshr n =>
    rcases args₂ with ⟨a, b, c, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_triple hargs).1).1
    have hb := (legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.1).1
    have hc' := (legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.2).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]; exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op3_normal target (.fshr (target.widenWidth n)) (legalArg target a).1 (legalArg target b).1 (legalArg target c).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hc' hlegW ?_
        exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_isLegal target hv hw (legalArg target c).1 hc' fun Γ1 cm hExt1 hcm => ?_
        refine isLegal_let_op2_normal target (.sub (.bits (target.widenWidth n))) (.imm _) cm _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) hlegW hcm hlegW ?_
        let Γ2 := (.bits (target.widenWidth n), VarKind.normal) :: Γ1
        have h12 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.lshr (.bits (target.widenWidth n))) (legalArg target b).1 cm _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (hb.mono h12) (hcm.mono (CtxExtends.cons _ _)) hlegW ?_
        let Γ3 := (.bits (target.widenWidth n), VarKind.normal) :: Γ2
        have h13 : CtxExtends Γ Γ3 := h12.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.shl (.bits (target.widenWidth n))) (legalArg target a).1 (.var Γ1.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ha.mono h13) ((ArgNormal.head target Γ1 hlegW).mono (CtxExtends.cons _ _)) hlegW ?_
        let Γ4 := (.bits (target.widenWidth n), VarKind.normal) :: Γ3
        refine isLegal_let_op2_normal target (.or (.bits (target.widenWidth n))) (.var Γ2.length) (.var Γ3.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) ((ArgNormal.head target Γ2 hlegW).mono (CtxExtends.cons _ _))
          (ArgNormal.head target Γ3 hlegW) hlegW ?_
        let Γ5 := (.bits (target.widenWidth n), VarKind.normal) :: Γ4
        have h15 : CtxExtends Γ Γ5 := h13.trans ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _))
        exact emitMaskToN_isLegal target hw (.var Γ4.length) (ArgNormal.head target Γ4 hlegW)
          fun Γ6 r hExt6 hr => hcont1 k hk Γ6 (r, ()) (h15.trans hExt6) ⟨hr, trivial⟩
  | bswap t =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    exact legalBswapTree_isLegal target hv t hsupp (legalArg target a)
      (legalArg_isNormal hc hsupp (ArgRel_single hargs)) (hcont1 k hk)
  | clz n =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_single hargs)).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]; exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op1_normal target (.clz (target.widenWidth n)) (legalArg target a).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hlegW ?_
        exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op1_normal target (.clz (target.widenWidth n)) (legalArg target a).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hlegW ?_
        let Γ1 := (.bits (target.widenWidth n), VarKind.normal) :: Γ
        refine isLegal_let_op2_normal target (.sub (.bits (target.widenWidth n))) (.var Γ.length) (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.head target Γ hlegW) hlegW hlegW ?_
        exact hcont1 k hk _ (.var Γ1.length, ()) ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _))
          ⟨ArgNormal.head target Γ1 hlegW, trivial⟩
  | cls n =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_single hargs)).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]; exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op1_normal target (.cls (target.widenWidth n)) (legalArg target a).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hlegW ?_
        exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitSextToW_isLegal target hw (legalArg target a).1 ha fun Γ1 sa hExt1 hsa => ?_
        refine isLegal_let_op1_normal target (.cls (target.widenWidth n)) sa _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) hsa hlegW ?_
        let Γ2 := (.bits (target.widenWidth n), VarKind.normal) :: Γ1
        refine isLegal_let_op2_normal target (.sub (.bits (target.widenWidth n))) (.var Γ1.length) (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.head target Γ1 hlegW) hlegW hlegW ?_
        exact hcont1 k hk _ (.var Γ2.length, ()) (hExt1.trans ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _)))
          ⟨ArgNormal.head target Γ2 hlegW, trivial⟩
  | rbit n =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_single hargs)).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]; exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op1_normal target (.rbit (target.widenWidth n)) (legalArg target a).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hlegW ?_
        exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op1_normal target (.rbit (target.widenWidth n)) (legalArg target a).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hlegW ?_
        let Γ1 := (.bits (target.widenWidth n), VarKind.normal) :: Γ
        refine isLegal_let_op2_normal target (.lshr (.bits (target.widenWidth n))) (.var Γ.length) (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.head target Γ hlegW) hlegW hlegW ?_
        exact hcont1 k hk _ (.var Γ1.length, ()) ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _))
          ⟨ArgNormal.head target Γ1 hlegW, trivial⟩
  | ctz n =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_single hargs)).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]; exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op1_normal target (.ctz (target.widenWidth n)) (legalArg target a).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hlegW ?_
        exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op2_normal target (.or (.bits (target.widenWidth n))) (legalArg target a).1 (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) ha hlegW hlegW ?_
        let Γ1 := (.bits (target.widenWidth n), VarKind.normal) :: Γ
        refine isLegal_let_op1_normal target (.ctz (target.widenWidth n)) (.var Γ.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) (ArgNormal.head target Γ hlegW) hlegW ?_
        exact hcont1 k hk _ (.var Γ1.length, ()) ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _))
          ⟨ArgNormal.head target Γ1 hlegW, trivial⟩
  | popcnt n =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_single hargs)).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]; exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      refine isLegal_let_op1_normal target (.popcnt (target.widenWidth n)) (legalArg target a).1 _ rfl
        (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hlegW ?_
      exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
  | cmp o t m h =>
    subst h
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    have ha := legalArg_isNormal hc hsupp (ArgRel_pair hargs).1
    have hb := legalArg_isNormal hc hsupp (ArgRel_pair hargs).2
    simp only [legalOp]
    by_cases hf : t.hasFloat = true
    · simp [hf, toTFlat_hlt]
    · simp only [hf, Bool.false_eq_true, ↓reduceIte]
      exact legalCmpTree_isLegal target hv o t hsupp (legalArg target a) (legalArg target b) ha hb (hcont1 k hk)
  | select t =>
    rcases args₂ with ⟨c, a, b, ⟨⟩⟩
    have hcs := (legalArg_isNormal hc rfl (ArgRel_triple hargs).1).1
    have ha := legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.1
    have hb := legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.2
    simp only [legalOp]
    exact legalSelectTree_isLegal target (legalArg target c).1 hcs t hsupp (legalArg target a) (legalArg target b) ha hb (hcont1 k hk)
  | blend t m h =>
    subst h
    dsimp only [LegalTarget.supportsOpCode] at hsupp
    rcases args₂ with ⟨c, a, b, ⟨⟩⟩
    have hc' := legalArg_isNormal hc (supportsTy_mask target t) (ArgRel_triple hargs).1
    have ha := legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.1
    have hb := legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.2
    simp only [legalOp]
    exact legalBlendTree_isLegal target t hsupp (legalArg target c) (legalArg target a) (legalArg target b) hc' ha hb (hcont1 k hk)
  | zext m n =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    simp only [Bool.and_eq_true] at hsupp
    rcases hpa : legalArg target a with ⟨a', ⟨⟩⟩
    have ha' := legalArg_isNormal hc hsupp.1 (ArgRel_single hargs)
    dsimp only at ha'; rw [hpa] at ha'
    have ha := ha'.1
    have hwm := widenWidth_mem_of_supports hsupp.1
    have hwn := widenWidth_mem_of_supports hsupp.2
    have hlegWn : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hwn
    simp only [legalOp, hpa]
    by_cases hmn : m > n
    · simp [hmn]
    · simp only [hmn, ↓reduceIte]
      by_cases hm0 : (m == 0) = true
      · simp only [hm0, ↓reduceIte]; exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegWn, trivial⟩
      · simp only [hm0, Bool.false_eq_true, ↓reduceIte]
        by_cases heq : target.widenWidth m = target.widenWidth n
        · simp only [heq, ↓reduceDIte]
          exact hcont1 k hk Γ (castArgBits heq a', ()) (CtxExtends.refl Γ) ⟨ArgNormal.cast heq ha, trivial⟩
        · simp only [heq, ↓reduceDIte]
          by_cases hlt : target.widenWidth m < target.widenWidth n
          · simp only [hlt, ↓reduceIte]
            refine isLegal_let_op1_normal target (.zext (target.widenWidth m) (target.widenWidth n)) a' _ rfl
              (by simp [LegalTarget.isLegalOp, hwm, hwn, hlt]) ha hlegWn ?_
            exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegWn, trivial⟩
          · simp [hlt]
  | sext m n =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    simp only [Bool.and_eq_true] at hsupp
    rcases hpa : legalArg target a with ⟨a', ⟨⟩⟩
    have ha' := legalArg_isNormal hc hsupp.1 (ArgRel_single hargs)
    dsimp only at ha'; rw [hpa] at ha'
    have ha := ha'.1
    have hwm := widenWidth_mem_of_supports hsupp.1
    have hwn := widenWidth_mem_of_supports hsupp.2
    have hlegWn : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hwn
    simp only [legalOp, hpa]
    by_cases hmn : m > n
    · simp [hmn]
    · simp only [hmn, ↓reduceIte]
      by_cases hm0 : (m == 0) = true
      · simp only [hm0, ↓reduceIte]; exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegWn, trivial⟩
      · simp only [hm0, Bool.false_eq_true, ↓reduceIte]
        refine emitSextToW_isLegal target hwm a' ha fun Γ1 sx hExt1 hsx => ?_
        have hstep2 : IsLegalCont target Γ1 Δ (fun Γ' r => ArgNormal target Γ' (.bits (target.widenWidth n)) r)
            fun r => emitMaskToN n (target.widenWidth n) r fun rm => k ((rm, ()), ()) := by
          intro Γ2 r hExt2 hr
          exact emitMaskToN_isLegal target hwn r hr fun Γ3 rm hExt3 hrm =>
            hcont1 k hk Γ3 (rm, ()) ((hExt1.trans hExt2).trans hExt3) ⟨hrm, trivial⟩
        by_cases heq : target.widenWidth m = target.widenWidth n
        · simp only [heq, ↓reduceDIte]
          exact hstep2 Γ1 (castArgBits heq sx) (CtxExtends.refl Γ1) (ArgNormal.cast heq hsx)
        · simp only [heq, ↓reduceDIte]
          by_cases hlt : target.widenWidth m < target.widenWidth n
          · simp only [hlt, ↓reduceIte]
            refine isLegal_let_op1_normal target (.sext (target.widenWidth m) (target.widenWidth n)) sx _ rfl
              (by simp [LegalTarget.isLegalOp, hwm, hwn, hlt]) hsx hlegWn ?_
            exact hstep2 _ (.var Γ1.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ1 hlegWn)
          · simp [hlt]
  | trunc m n =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    simp only [Bool.and_eq_true] at hsupp
    rcases hpa : legalArg target a with ⟨a', ⟨⟩⟩
    have ha' := legalArg_isNormal hc hsupp.1 (ArgRel_single hargs)
    dsimp only at ha'; rw [hpa] at ha'
    have ha := ha'.1
    have hwm := widenWidth_mem_of_supports hsupp.1
    have hwn := widenWidth_mem_of_supports hsupp.2
    have hlegWn : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hwn
    simp only [legalOp, hpa]
    by_cases hnm : n > m
    · simp [hnm]
    · simp only [hnm, ↓reduceIte]
      by_cases hn0 : (n == 0) = true
      · simp only [hn0, ↓reduceIte]; exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegWn, trivial⟩
      · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
        have hstep2 : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' (.bits (target.widenWidth n)) r)
            fun r => emitMaskToN n (target.widenWidth n) r fun rm => k ((rm, ()), ()) := by
          intro Γ1 r hExt1 hr
          exact emitMaskToN_isLegal target hwn r hr fun Γ2 rm hExt2 hrm =>
            hcont1 k hk Γ2 (rm, ()) (hExt1.trans hExt2) ⟨hrm, trivial⟩
        by_cases heq : target.widenWidth n = target.widenWidth m
        · simp only [heq, ↓reduceDIte]
          exact hstep2 Γ (castArgBits heq.symm a') (CtxExtends.refl Γ) (ArgNormal.cast heq.symm ha)
        · simp only [heq, ↓reduceDIte]
          by_cases hlt : target.widenWidth n < target.widenWidth m
          · simp only [hlt, ↓reduceIte]
            refine isLegal_let_op1_normal target (.trunc (target.widenWidth m) (target.widenWidth n)) a' _ rfl
              (by simp [LegalTarget.isLegalOp, hwm, hwn, hlt]) ha hlegWn ?_
            exact hstep2 _ (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hlegWn)
          · simp [hlt]
  | ofBool n =>
    rcases args₂ with ⟨c, ⟨⟩⟩
    have hc' := (legalArg_isNormal hc rfl (ArgRel_single hargs)).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]; exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      refine isLegal_let_op1_normal target (.ofBool (target.widenWidth n)) (legalArg target c).1 _ rfl
        (by simp [LegalTarget.isLegalOp, hw, hwpos]) hc' hlegW ?_
      exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
  | addc n =>
    rcases args₂ with ⟨a, b, c, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_triple hargs).1).1
    have hb := (legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.1).1
    have hc' := (legalArg_isNormal hc rfl (ArgRel_triple hargs).2.2).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]
      exact hcont2 k hk Γ (.imm _, ()) ((legalArg target c).1, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩ ⟨hc', trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op3_2res target (.addc (target.widenWidth n)) (legalArg target a).1 (legalArg target b).1 (legalArg target c).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hc' hlegW rfl ?_
        have hvt := ArgsNormal_varsTup_levels target [.bits (target.widenWidth n), .bool] Γ
          (by simp [LegalTarget.isLegalSig, LegalTarget.isLegalTy, hw])
        exact hcont2 k hk _ (.var Γ.length, ()) (.var (Γ.length + 1), ()) (CtxExtends.pushNormal _ _)
          ⟨hvt.1, trivial⟩ ⟨hvt.2.1, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op1_normal target (.ofBool (target.widenWidth n)) (legalArg target c).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) hc' hlegW ?_
        let Γ1 := (.bits (target.widenWidth n), VarKind.normal) :: Γ
        have h1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
        refine isLegal_let_op2_normal target (.add (.bits (target.widenWidth n))) (legalArg target a).1 (legalArg target b).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ha.mono h1) (hb.mono h1) hlegW ?_
        let Γ2 := (.bits (target.widenWidth n), VarKind.normal) :: Γ1
        have h2 : CtxExtends Γ1 Γ2 := CtxExtends.cons _ _
        refine isLegal_let_op2_normal target (.add (.bits (target.widenWidth n))) (.var Γ1.length) (.var Γ.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.head target Γ1 hlegW) ((ArgNormal.head target Γ hlegW).mono h2) hlegW ?_
        let Γ3 := (.bits (target.widenWidth n), VarKind.normal) :: Γ2
        have h13 : CtxExtends Γ Γ3 := h1.trans (h2.trans (CtxExtends.cons _ _))
        refine emitMaskToN_isLegal target hw (.var Γ2.length) (ArgNormal.head target Γ2 hlegW) fun Γ4 s hExt4 hs => ?_
        have hsw : ArgNormal target Γ4 (.bits (target.widenWidth n)) (.var Γ2.length) :=
          (ArgNormal.head target Γ2 hlegW).mono hExt4
        refine isLegal_let_op2_normal target (.ule (.bits (target.widenWidth n))) (.imm _) (.var Γ2.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) hlegW hsw rfl ?_
        let Γ5 := (.bool, VarKind.normal) :: Γ4
        exact hcont2 k hk Γ5 (s, ()) (.var Γ4.length, ()) ((h13.trans hExt4).trans (CtxExtends.cons _ _))
          ⟨hs.mono (CtxExtends.cons _ _), trivial⟩ ⟨ArgNormal.head target Γ4 rfl, trivial⟩
  | subb n =>
    rcases args₂ with ⟨a, b, c, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_triple hargs).1).1
    have hb := (legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.1).1
    have hc' := (legalArg_isNormal hc rfl (ArgRel_triple hargs).2.2).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]
      exact hcont2 k hk Γ (.imm _, ()) ((legalArg target c).1, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩ ⟨hc', trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op3_2res target (.subb (target.widenWidth n)) (legalArg target a).1 (legalArg target b).1 (legalArg target c).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hc' hlegW rfl ?_
        have hvt := ArgsNormal_varsTup_levels target [.bits (target.widenWidth n), .bool] Γ
          (by simp [LegalTarget.isLegalSig, LegalTarget.isLegalTy, hw])
        exact hcont2 k hk _ (.var Γ.length, ()) (.var (Γ.length + 1), ()) (CtxExtends.pushNormal _ _)
          ⟨hvt.1, trivial⟩ ⟨hvt.2.1, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op3_2res target (.subb (target.widenWidth n)) (legalArg target a).1 (legalArg target b).1 (legalArg target c).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hc' hlegW rfl ?_
        let Γ1 := pushNormal [.bits (target.widenWidth n), .bool] Γ
        have hvt := ArgsNormal_varsTup_levels target [.bits (target.widenWidth n), .bool] Γ
          (by simp [LegalTarget.isLegalSig, LegalTarget.isLegalTy, hw])
        refine emitMaskToN_isLegal target hw (.var Γ.length) hvt.1 fun Γ2 d hExt2 hd => ?_
        exact hcont2 k hk Γ2 (d, ()) (.var (Γ.length + 1), ()) ((CtxExtends.pushNormal _ _).trans hExt2)
          ⟨hd, trivial⟩ ⟨hvt.2.1.mono hExt2, trivial⟩
  | umulw n =>
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_pair hargs).1).1
    have hb := (legalArg_isNormal hc hsupp (ArgRel_pair hargs).2).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]
      exact hcont2 k hk Γ (.imm _, ()) (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩ ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op2_2res target (.umulw (target.widenWidth n)) (legalArg target a).1 (legalArg target b).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hlegW hlegW ?_
        have hvt := ArgsNormal_varsTup_levels target [.bits (target.widenWidth n), .bits (target.widenWidth n)] Γ
          (by simp [LegalTarget.isLegalSig, hlegW])
        exact hcont2 k hk _ (.var Γ.length, ()) (.var (Γ.length + 1), ()) (CtxExtends.pushNormal _ _)
          ⟨hvt.1, trivial⟩ ⟨hvt.2.1, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op2_2res target (.umulw (target.widenWidth n)) (legalArg target a).1 (legalArg target b).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hlegW hlegW ?_
        let Γ1 := pushNormal [.bits (target.widenWidth n), .bits (target.widenWidth n)] Γ
        have h1 : CtxExtends Γ Γ1 := CtxExtends.pushNormal _ _
        have hvt := ArgsNormal_varsTup_levels target [.bits (target.widenWidth n), .bits (target.widenWidth n)] Γ
          (by simp [LegalTarget.isLegalSig, hlegW])
        refine emitMaskToN_isLegal target hw (.var Γ.length) hvt.1 fun Γ2 lo hExt2 hlo => ?_
        refine isLegal_let_op2_normal target (.lshr (.bits (target.widenWidth n))) (.var Γ.length) (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (hvt.1.mono hExt2) hlegW hlegW ?_
        let Γ3 := (.bits (target.widenWidth n), VarKind.normal) :: Γ2
        refine isLegal_let_op2_normal target (.shl (.bits (target.widenWidth n))) (.var (Γ.length + 1)) (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (hvt.2.1.mono (hExt2.trans (CtxExtends.cons _ _))) hlegW hlegW ?_
        let Γ4 := (.bits (target.widenWidth n), VarKind.normal) :: Γ3
        refine isLegal_let_op2_normal target (.or (.bits (target.widenWidth n))) (.var Γ2.length) (.var Γ3.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) ((ArgNormal.head target Γ2 hlegW).mono (CtxExtends.cons _ _))
          (ArgNormal.head target Γ3 hlegW) hlegW ?_
        let Γ5 := (.bits (target.widenWidth n), VarKind.normal) :: Γ4
        have h15 : CtxExtends Γ Γ5 := h1.trans (hExt2.trans ((CtxExtends.cons _ _).trans ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _))))
        refine emitMaskToN_isLegal target hw (.var Γ4.length) (ArgNormal.head target Γ4 hlegW) fun Γ6 hi hExt6 hhi => ?_
        have hlo' := hlo.mono ((CtxExtends.cons _ _).trans ((CtxExtends.cons _ _).trans ((CtxExtends.cons _ _).trans hExt6)))
        exact hcont2 k hk Γ6 (lo, ()) (hi, ()) (h15.trans hExt6) ⟨hlo', trivial⟩ ⟨hhi, trivial⟩
  | smulw n =>
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_pair hargs).1).1
    have hb := (legalArg_isNormal hc hsupp (ArgRel_pair hargs).2).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]
      exact hcont2 k hk Γ (.imm _, ()) (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩ ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op2_2res target (.smulw (target.widenWidth n)) (legalArg target a).1 (legalArg target b).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hlegW hlegW ?_
        have hvt := ArgsNormal_varsTup_levels target [.bits (target.widenWidth n), .bits (target.widenWidth n)] Γ
          (by simp [LegalTarget.isLegalSig, hlegW])
        exact hcont2 k hk _ (.var Γ.length, ()) (.var (Γ.length + 1), ()) (CtxExtends.pushNormal _ _)
          ⟨hvt.1, trivial⟩ ⟨hvt.2.1, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitSextToW_isLegal target hw (legalArg target a).1 ha fun Γa sa hExta hsa => ?_
        refine emitSextToW_isLegal target hw ((legalArg target b).1) (hb.mono hExta) fun Γb sb hExtb hsb => ?_
        have hab := hExta.trans hExtb
        refine isLegal_let_op2_2res target (.smulw (target.widenWidth n)) sa sb _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) (hsa.mono hExtb) hsb hlegW hlegW ?_
        let Γ1 := pushNormal [.bits (target.widenWidth n), .bits (target.widenWidth n)] Γb
        have h1 : CtxExtends Γ Γ1 := hab.trans (CtxExtends.pushNormal _ _)
        have hvt := ArgsNormal_varsTup_levels target [.bits (target.widenWidth n), .bits (target.widenWidth n)] Γb
          (by simp [LegalTarget.isLegalSig, hlegW])
        refine emitMaskToN_isLegal target hw (.var Γb.length) hvt.1 fun Γ2 lo hExt2 hlo => ?_
        refine isLegal_let_op2_normal target (.lshr (.bits (target.widenWidth n))) (.var Γb.length) (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (hvt.1.mono hExt2) hlegW hlegW ?_
        let Γ3 := (.bits (target.widenWidth n), VarKind.normal) :: Γ2
        refine isLegal_let_op2_normal target (.shl (.bits (target.widenWidth n))) (.var (Γb.length + 1)) (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (hvt.2.1.mono (hExt2.trans (CtxExtends.cons _ _))) hlegW hlegW ?_
        let Γ4 := (.bits (target.widenWidth n), VarKind.normal) :: Γ3
        refine isLegal_let_op2_normal target (.or (.bits (target.widenWidth n))) (.var Γ2.length) (.var Γ3.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) ((ArgNormal.head target Γ2 hlegW).mono (CtxExtends.cons _ _))
          (ArgNormal.head target Γ3 hlegW) hlegW ?_
        let Γ5 := (.bits (target.widenWidth n), VarKind.normal) :: Γ4
        have h15 : CtxExtends Γ Γ5 := h1.trans (hExt2.trans ((CtxExtends.cons _ _).trans ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _))))
        refine emitMaskToN_isLegal target hw (.var Γ4.length) (ArgNormal.head target Γ4 hlegW) fun Γ6 hi hExt6 hhi => ?_
        have hlo' := hlo.mono ((CtxExtends.cons _ _).trans ((CtxExtends.cons _ _).trans ((CtxExtends.cons _ _).trans hExt6)))
        exact hcont2 k hk Γ6 (lo, ()) (hi, ()) (h15.trans hExt6) ⟨hlo', trivial⟩ ⟨hhi, trivial⟩
  | udiv n =>
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    rcases hpa : legalArg target a with ⟨a', ⟨⟩⟩
    rcases hpb : legalArg target b with ⟨b', ⟨⟩⟩
    have ha' := legalArg_isNormal hc hsupp (ArgRel_pair hargs).1
    have hb' := legalArg_isNormal hc hsupp (ArgRel_pair hargs).2
    dsimp only at ha' hb'; rw [hpa] at ha'; rw [hpb] at hb'
    have ha := ha'.1; have hb := hb'.1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp, hpa, hpb]
    by_cases hn0 : (n == 0) = true
    · simp [hn0]
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      refine isLegal_let_op2_normal target (.udiv (target.widenWidth n)) a' b' _ rfl
        (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hlegW ?_
      exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
  | sdiv n =>
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    rcases hpa : legalArg target a with ⟨a', ⟨⟩⟩
    rcases hpb : legalArg target b with ⟨b', ⟨⟩⟩
    have ha' := legalArg_isNormal hc hsupp (ArgRel_pair hargs).1
    have hb' := legalArg_isNormal hc hsupp (ArgRel_pair hargs).2
    dsimp only at ha' hb'; rw [hpa] at ha'; rw [hpb] at hb'
    have ha := ha'.1; have hb := hb'.1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp, hpa, hpb]
    by_cases hn0 : (n == 0) = true
    · simp [hn0]
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op2_normal target (.sdiv (target.widenWidth n)) a' b' _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hlegW ?_
        exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitSextToW_isLegal target hw a' ha fun Γ1 sa hExt1 hsa => ?_
        refine emitSextToW_isLegal target hw b' (hb.mono hExt1) fun Γ2 sb hExt2 hsb => ?_
        refine isLegal_let_op2_normal target (.sdiv (target.widenWidth n)) sa sb _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) (hsa.mono hExt2) hsb hlegW ?_
        let Γ3 := (.bits (target.widenWidth n), VarKind.normal) :: Γ2
        refine emitMaskToN_isLegal target hw (.var Γ2.length) (ArgNormal.head target Γ2 hlegW) fun Γ4 rm hExt4 hrm => ?_
        exact hcont1 k hk Γ4 (rm, ()) (((hExt1.trans hExt2).trans (CtxExtends.cons _ _)).trans hExt4) ⟨hrm, trivial⟩
  | urem n =>
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    rcases hpa : legalArg target a with ⟨a', ⟨⟩⟩
    rcases hpb : legalArg target b with ⟨b', ⟨⟩⟩
    have ha' := legalArg_isNormal hc hsupp (ArgRel_pair hargs).1
    have hb' := legalArg_isNormal hc hsupp (ArgRel_pair hargs).2
    dsimp only at ha' hb'; rw [hpa] at ha'; rw [hpb] at hb'
    have ha := ha'.1; have hb := hb'.1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp, hpa, hpb]
    by_cases hn0 : (n == 0) = true
    · simp [hn0]
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      refine isLegal_let_op2_normal target (.urem (target.widenWidth n)) a' b' _ rfl
        (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hlegW ?_
      exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
  | srem n =>
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    rcases hpa : legalArg target a with ⟨a', ⟨⟩⟩
    rcases hpb : legalArg target b with ⟨b', ⟨⟩⟩
    have ha' := legalArg_isNormal hc hsupp (ArgRel_pair hargs).1
    have hb' := legalArg_isNormal hc hsupp (ArgRel_pair hargs).2
    dsimp only at ha' hb'; rw [hpa] at ha'; rw [hpb] at hb'
    have ha := ha'.1; have hb := hb'.1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp, hpa, hpb]
    by_cases hn0 : (n == 0) = true
    · simp [hn0]
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op2_normal target (.srem (target.widenWidth n)) a' b' _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hlegW ?_
        exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitSextToW_isLegal target hw a' ha fun Γ1 sa hExt1 hsa => ?_
        refine emitSextToW_isLegal target hw b' (hb.mono hExt1) fun Γ2 sb hExt2 hsb => ?_
        refine isLegal_let_op2_normal target (.srem (target.widenWidth n)) sa sb _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) (hsa.mono hExt2) hsb hlegW ?_
        let Γ3 := (.bits (target.widenWidth n), VarKind.normal) :: Γ2
        refine emitMaskToN_isLegal target hw (.var Γ2.length) (ArgNormal.head target Γ2 hlegW) fun Γ4 rm hExt4 hrm => ?_
        exact hcont1 k hk Γ4 (rm, ()) (((hExt1.trans hExt2).trans (CtxExtends.cons _ _)).trans hExt4) ⟨hrm, trivial⟩
  | udiv0 n =>
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_pair hargs).1).1
    have hb := (legalArg_isNormal hc hsupp (ArgRel_pair hargs).2).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]; exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      refine isLegal_let_op2_normal target (.udiv0 (target.widenWidth n)) (legalArg target a).1 (legalArg target b).1 _ rfl
        (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hlegW ?_
      exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
  | sdiv0 n =>
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_pair hargs).1).1
    have hb := (legalArg_isNormal hc hsupp (ArgRel_pair hargs).2).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]; exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op2_normal target (.sdiv0 (target.widenWidth n)) (legalArg target a).1 (legalArg target b).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hlegW ?_
        exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitSextToW_isLegal target hw (legalArg target a).1 ha fun Γ1 sa hExt1 hsa => ?_
        refine emitSextToW_isLegal target hw (legalArg target b).1 (hb.mono hExt1) fun Γ2 sb hExt2 hsb => ?_
        refine isLegal_let_op2_normal target (.sdiv0 (target.widenWidth n)) sa sb _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) (hsa.mono hExt2) hsb hlegW ?_
        let Γ3 := (.bits (target.widenWidth n), VarKind.normal) :: Γ2
        refine emitMaskToN_isLegal target hw (.var Γ2.length) (ArgNormal.head target Γ2 hlegW) fun Γ4 rm hExt4 hrm => ?_
        exact hcont1 k hk Γ4 (rm, ()) (((hExt1.trans hExt2).trans (CtxExtends.cons _ _)).trans hExt4) ⟨hrm, trivial⟩
  | mkpair a b =>
    rcases args₂ with ⟨va, vb, ⟨⟩⟩
    simp only [Bool.and_eq_true] at hsupp
    have hla := legalArg_isNormal hc hsupp.1 (ArgRel_pair hargs).1
    have hlb := legalArg_isNormal hc hsupp.2 (ArgRel_pair hargs).2
    simp only [legalOp]
    split
    · next hp =>
      have hp' := hp
      simp only [LegalTarget.keepsPacked, LegalTarget.hasLegalLeaves, Bool.and_eq_true] at hp'
      have ha_pb := hp'.1.1
      refine packFromLegal_isLegal target ha_pb a hp'.2.1 _ hla fun Γ1 pa hExt1 hpa => ?_
      refine packFromLegal_isLegal target ha_pb b hp'.2.2 _ (hlb.mono hExt1) fun Γ2 pb hExt2 hpb => ?_
      have hpa' := hpa.mono hExt2
      rw [toTFlat_let]; dsimp only [op2, Tup.levels_cons, Tup.levels_nil]; rw [idxArgs_pair, TFlat.isLegal_let_mkpair]
      have hlpair : target.hasLegalLeaves (.pair a b) = true := by
        simp only [LegalTarget.hasLegalLeaves, Bool.and_eq_true]; exact hp'.2
      have hlegP : target.isLegalTy (.pair a b) = true := hp
      simp only [ha_pb, hlpair, hlegP, ↓reduceIte, Bool.true_and]
      have hchkA : (match idxArg Γ2.length pa with
          | .var idx => checkVarKind Γ2 a (fun vk => (vk == .normal && target.isLegalTy a) || vk == .packedBridge) idx
          | .imm _ => target.isLegalTy a) = true := by
        cases pa with | imm _ => exact hpa' | var _ => exact hpa'.checkVarKind
      have hchkB : (match idxArg Γ2.length pb with
          | .var idx => checkVarKind Γ2 b (fun vk => (vk == .normal && target.isLegalTy b) || vk == .packedBridge) idx
          | .imm _ => target.isLegalTy b) = true := by
        cases pb with | imm _ => exact hpb | var _ => exact hpb.checkVarKind
      cases pa <;> cases pb <;> dsimp only [idxArg] at hchkA hchkB ⊢ <;>
        simp only [hchkA, hchkB, Bool.true_and]
      all_goals
        let Γ3 := (.pair a b, VarKind.normal) :: Γ2
        have hlen3 : Γ3.length = Γ2.length + [a.pair b].length := by simp [Γ3]
        rw [← hlen3]
        exact hcont1 k hk Γ3 (tupToPacked hp (.var Γ2.length, ())) ((hExt1.trans hExt2).trans (CtxExtends.cons _ _))
          (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ2 hlegP, trivial⟩)
    · next hnp =>
      have hf := Bool.eq_false_iff.mpr hnp
      exact hcont1 k hk Γ (tupToSplit hf (tupAppend (legalArg target va) (legalArg target vb))) (CtxExtends.refl Γ)
        (ArgsNormal_tupToSplit hf (ArgsNormal_tupAppend hla hlb))
  | unpair a b =>
    rcases args₂ with ⟨vp, ⟨⟩⟩
    have hsuppP : target.supportsTy (.pair a b) = true := hsupp
    have ⟨hsa, hsb⟩ := (Bool.and_eq_true _ _).mp hsupp
    have hlp := legalArg_isNormal hc hsuppP (ArgRel_single hargs)
    simp only [legalOp]
    split
    · next hp =>
      have hp' := hp
      simp only [LegalTarget.keepsPacked, LegalTarget.hasLegalLeaves, Bool.and_eq_true] at hp'
      have ha_pb := hp'.1.1
      have hlegP : target.isLegalTy (.pair a b) = true := hp
      cases hv0 : (packedToTup hp (legalArg target vp)).1 with
      | imm c =>
        dsimp only
        exact hcont2 k hk Γ (encodeImm target a c.1) (encodeImm target b c.2) (CtxExtends.refl Γ)
          (ArgsNormal_encodeImm a hsa c.1) (ArgsNormal_encodeImm b hsb c.2)
      | var v =>
        dsimp only
        have hvn : ArgNormal target Γ (.pair a b) (.var v) := by
          have := (ArgsNormal_packedToTup hp hlp).1
          dsimp only at this
          change ArgNormal target Γ (a.pair b) (packedToTup hp (legalArg target vp)).1 at this
          rw [hv0] at this; exact this
        rw [toTFlat_let]; dsimp only [op1, Tup.levels_cons, Tup.levels_nil]
        rw [idxArgs_single, TFlat.isLegal_let_unpair]
        have hlpair : target.hasLegalLeaves (.pair a b) = true := by
          simp only [LegalTarget.hasLegalLeaves, Bool.and_eq_true]; exact hp'.2
        have hchkP : checkVarKind Γ (.pair a b)
            (fun vk => (vk == .normal && target.isLegalTy (.pair a b)) || vk == .unpackedBridge)
            (if v < Γ.length then Γ.length - 1 - v else Γ.length) = true :=
          (hvn.1.weaken_pred (fun vk hvk => by simp [hvk, hlegP])).checkVarKind
        dsimp only [idxArg]
        simp only [ha_pb, hlpair, hchkP, Bool.true_and]
        let ka := if target.isLegalTy a then VarKind.normal else .unpackedBridge
        let kb := if target.isLegalTy b then VarKind.normal else .unpackedBridge
        let Γ1 := pushTypes [(a, ka), (b, kb)] Γ
        have hExt1 : CtxExtends Γ Γ1 := CtxExtends.pushTypes _ _
        have hlen1' : Γ1.length = Γ.length + 2 := by simp [Γ1, pushTypes_length, Nat.add_comm]
        have hlen1 : Γ1.length = Γ.length + [a, b].length := by simpa using hlen1'
        rw [← hlen1]
        have hget0 : listGet? Γ1 (Γ1.length - 1 - Γ.length) = some (a, ka) := by
          have hrev : Γ1 = [(b, kb), (a, ka)] ++ Γ := rfl
          have hidx : Γ1.length - 1 - Γ.length = 1 := by omega
          rw [hidx, hrev]; rfl
        have hget1 : listGet? Γ1 (Γ1.length - 1 - (Γ.length + 1)) = some (b, kb) := by
          have hrev : Γ1 = [(b, kb), (a, ka)] ++ Γ := rfl
          have hidx : Γ1.length - 1 - (Γ.length + 1) = 0 := by omega
          rw [hidx, hrev]; rfl
        have hUa : UnpackBridgeArg target Γ1 a (.var Γ.length) := by
          refine ⟨⟨by omega, ka, hget0, ?_⟩, ?_⟩
          · by_cases haL : target.isLegalTy a = true <;> simp [ka, haL]
          · intro haL; refine ⟨by omega, .normal, ?_, rfl⟩; simpa [ka, haL] using hget0
        have hUb : UnpackBridgeArg target Γ1 b (.var (Γ.length + 1)) := by
          refine ⟨⟨by omega, kb, hget1, ?_⟩, ?_⟩
          · by_cases hbL : target.isLegalTy b = true <;> simp [kb, hbL]
          · intro hbL; refine ⟨by omega, .normal, ?_, rfl⟩; simpa [kb, hbL] using hget1
        change (toTFlat (unpackToLegal target a (.var Γ.length) fun la =>
          unpackToLegal target b (.var (Γ.length + 1)) fun lb => k (la, lb, ()))
            Γ1.length Δ.length).isLegal target Γ1 Δ = true
        refine unpackToLegal_isLegal target hv ha_pb a hp'.2.1 (.var Γ.length) hUa fun Γ2 la hExt12 hla => ?_
        refine unpackToLegal_isLegal target hv ha_pb b hp'.2.2 (.var (Γ.length + 1)) (hUb.mono hExt12)
          fun Γ3 lb hExt23 hlb => ?_
        exact hcont2 k hk Γ3 la lb (hExt1.trans (hExt12.trans hExt23)) (hla.mono hExt23) hlb
    · next hnp =>
      have hf := Bool.eq_false_iff.mpr hnp
      obtain ⟨hla, hlb⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hlp)
      exact hcont2 k hk Γ _ _ (CtxExtends.refl Γ) hla hlb
  | bitcast t u h =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    simp only [Bool.and_eq_true] at hsupp
    have ha := legalArg_isNormal hc hsupp.1 (ArgRel_single hargs)
    simp only [legalOp]
    by_cases heq : t = u
    · simp only [heq, ↓reduceDIte]
      subst heq
      exact hcont1 k hk Γ (legalArg target a) (CtxExtends.refl Γ) ha
    · simp only [heq, ↓reduceDIte]
      have hfallback : (toTFlat (splitLegalToLeaves target t (legalArg target a) fun fx =>
          packLeavesToWords64 target t fx fun words =>
          unpackWords64ToLeaves target words 0 u fun fu =>
          packLeavesToLegal target u fu fun res => k (res, ())) Γ.length Δ.length).isLegal target Γ Δ = true := by
        refine splitLegalToLeaves_isLegal target t (legalArg target a) ha fun Γ1 fx hExt1 hfx => ?_
        refine packLeavesToWords64_isLegal target hv t hsupp.1 fx hfx fun Γ2 words hExt2 hwords => ?_
        refine unpackWords64ToLeaves_isLegal target hv words hwords 0 u hsupp.2 fun Γ3 fu hExt3 hfu => ?_
        exact packLeavesToLegal_isLegal target u fu hfu fun Γ4 res hExt4 hres =>
          hcont1 k hk Γ4 res (((hExt1.trans hExt2).trans hExt3).trans hExt4) hres
      refine dite_pred (P := fun e => (toTFlat e Γ.length Δ.length).isLegal target Γ Δ = true) (fun ht => ?_) (fun _ => hfallback)
      refine dite_pred (P := fun e => (toTFlat e Γ.length Δ.length).isLegal target Γ Δ = true) (fun hu => ?_) (fun _ => hfallback)
      have htL : target.isLegalTy t = true := ((Bool.and_eq_true _ _).mp ht).1
      have htM := ((Bool.and_eq_true _ _).mp ht).2
      have huL : target.isLegalTy u = true := ((Bool.and_eq_true _ _).mp hu).1
      have huM := ((Bool.and_eq_true _ _).mp hu).2
      have hlt : target.legalTys t = [t] := by
        cases t with
        | bool => rfl
        | bits m => simp [LegalTarget.legalTys, beq_iff_eq.mp htM]
        | float _ => rfl
        | pair _ _ => simp [LegalTarget.isLegalTy] at htL; simp [LegalTarget.legalTys, htL]
      have hlu : target.legalTys u = [u] := by
        cases u with
        | bool => rfl
        | bits m => simp [LegalTarget.legalTys, beq_iff_eq.mp huM]
        | float _ => rfl
        | pair _ _ => simp [LegalTarget.isLegalTy] at huL; simp [LegalTarget.legalTys, huL]
      have hx' : ArgNormal target Γ t (cast (by rw [hlt]) (legalArg target a) : Tup (Arg K) [t]).1 :=
        (ArgsNormal_cast_eq _ hlt ha).1
      refine isLegal_let_op1_normal target (.bitcast t u h) _ _ rfl
        (by simp [LegalTarget.isLegalOp, htL, huL, bne_iff_ne, heq]) hx' huL ?_
      exact hcont1 k hk _ _ (CtxExtends.cons _ _)
        (ArgsNormal_cast_eq _ hlu.symm ⟨ArgNormal.head target Γ huL, trivial⟩)
  | shufd t imm =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsupp
    have ha := legalArg_isNormal hc hsupp.1 (ArgRel_single hargs)
    simp only [legalOp]
    exact legalShufd_isLegal target hv hsupp.2 imm t hsupp.1 (legalArg target a) ha (hcont1 k hk)
  | shufb t =>
    rcases args₂ with ⟨a, m, ⟨⟩⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsupp
    have ha := legalArg_isNormal hc hsupp.1 (ArgRel_pair hargs).1
    have hm := legalArg_isNormal hc hsupp.1 (ArgRel_pair hargs).2
    simp only [legalOp]
    exact legalShufb_isLegal target hv hsupp.2 t hsupp.1 (legalArg target a) (legalArg target m) ha hm (hcont1 k hk)
  | alignr t imm =>
    rcases args₂ with ⟨hi, lo, ⟨⟩⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsupp
    have hhi := legalArg_isNormal hc hsupp.1 (ArgRel_pair hargs).1
    have hlo := legalArg_isNormal hc hsupp.1 (ArgRel_pair hargs).2
    simp only [legalOp]
    exact legalAlignr_isLegal target hv hsupp.2 imm t hsupp.1 (legalArg target hi) (legalArg target lo) hhi hlo (hcont1 k hk)
  | blendw t imm =>
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsupp
    have ha := legalArg_isNormal hc hsupp.1 (ArgRel_pair hargs).1
    have hb := legalArg_isNormal hc hsupp.1 (ArgRel_pair hargs).2
    simp only [legalOp]
    exact legalBlendw_isLegal target hv hsupp.2 imm t hsupp.1 (legalArg target a) (legalArg target b) ha hb (hcont1 k hk)
  | sha256rnds2 =>
    rcases args₂ with ⟨cdgh, abef, wk, ⟨⟩⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsupp
    have hc' := legalArg_isNormal hc hsupp.1 (ArgRel_triple hargs).1
    have ha := legalArg_isNormal hc hsupp.1 (ArgRel_triple hargs).2.1
    have hw := legalArg_isNormal hc hsupp.1 (ArgRel_triple hargs).2.2
    have hsc : (toTFlat (splitLegalToLeaves target v4i32 (legalArg target cdgh) fun fc =>
        splitLegalToLeaves target v4i32 (legalArg target abef) fun fa =>
        splitLegalToLeaves target v4i32 (legalArg target wk) fun fw =>
        packLeavesToWords64 target v4i32 fc fun wc =>
        packLeavesToWords64 target v4i32 fa fun wa =>
        packLeavesToWords64 target v4i32 fw fun ww =>
        words2ToDwords4 (wc.getD 0 (.imm 0#64)) (wc.getD 1 (.imm 0#64)) fun cd0 cd1 cd2 cd3 =>
        words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun ab0 ab1 ab2 ab3 =>
        words2ToDwords4 (ww.getD 0 (.imm 0#64)) (ww.getD 1 (.imm 0#64)) fun wk0 wk1 wk2 wk3 =>
        scalarSha256rnds2 cd0 cd1 cd2 cd3 ab0 ab1 ab2 ab3 wk0 wk1 wk2 wk3 fun r0 r1 r2 r3 =>
        dwords4ToWords2 r0 r1 r2 r3 fun w0 w1 =>
        unpackWords64ToLeaves target [w0, w1] 0 v4i32 fun fres =>
        packLeavesToLegal target v4i32 fres fun res => k (res, ())) Γ.length Δ.length).isLegal target Γ Δ = true := by
      refine splitLegalToLeaves_isLegal target v4i32 (legalArg target cdgh) hc' fun Γ1 fc h1 hfc => ?_
      refine splitLegalToLeaves_isLegal target v4i32 (legalArg target abef) (ha.mono h1) fun Γ2 fa h2 hfa => ?_
      have h12 := h1.trans h2
      refine splitLegalToLeaves_isLegal target v4i32 (legalArg target wk) (hw.mono h12) fun Γ3 fw h3 hfw => ?_
      have h13 := h12.trans h3
      refine packLeavesToWords64_isLegal target hv v4i32 hsupp.1 fc (hfc.mono (h2.trans h3)) fun Γ4 wc h4 hwc => ?_
      refine packLeavesToWords64_isLegal target hv v4i32 hsupp.1 fa ((hfa.mono h3).mono h4) fun Γ5 wa h5 hwa => ?_
      have h45 := h4.trans h5
      refine packLeavesToWords64_isLegal target hv v4i32 hsupp.1 fw (hfw.mono h45) fun Γ6 ww h6 hww => ?_
      have h16 := h13.trans (h45.trans h6)
      refine words2ToDwords4_isLegal target hsupp.2 h64 _ _
        (ArgNormal_getD_i64 target h64 wc (fun x hx => (hwc x hx).mono (h5.trans h6)) 0)
        (ArgNormal_getD_i64 target h64 wc (fun x hx => (hwc x hx).mono (h5.trans h6)) 1)
        fun Γ7 cd0 cd1 cd2 cd3 h7 hcd0 hcd1 hcd2 hcd3 => ?_
      refine words2ToDwords4_isLegal target hsupp.2 h64 _ _
        (ArgNormal_getD_i64 target h64 wa (fun x hx => (hwa x hx).mono (h6.trans h7)) 0)
        (ArgNormal_getD_i64 target h64 wa (fun x hx => (hwa x hx).mono (h6.trans h7)) 1)
        fun Γ8 ab0 ab1 ab2 ab3 h8 hab0 hab1 hab2 hab3 => ?_
      refine words2ToDwords4_isLegal target hsupp.2 h64 _ _
        (ArgNormal_getD_i64 target h64 ww (fun x hx => (hww x hx).mono (h7.trans h8)) 0)
        (ArgNormal_getD_i64 target h64 ww (fun x hx => (hww x hx).mono (h7.trans h8)) 1)
        fun Γ9 wk0 wk1 wk2 wk3 h9 hwk0 hwk1 _ _ => ?_
      have h79 := h7.trans (h8.trans h9)
      have h89 := h8.trans h9
      refine scalarSha256rnds2_isLegal target hsupp.2 cd0 cd1 cd2 cd3 ab0 ab1 ab2 ab3 wk0 wk1 wk2 wk3
        (hcd0.mono h89) (hcd1.mono h89) (hcd2.mono h89) (hcd3.mono h89)
        (hab0.mono h9) (hab1.mono h9) (hab2.mono h9) (hab3.mono h9) hwk0 hwk1
        fun Γ10 r0 r1 r2 r3 h10 hr0 hr1 hr2 hr3 => ?_
      refine dwords4ToWords2_isLegal target hsupp.2 h64 r0 r1 r2 r3 hr0 hr1 hr2 hr3 fun Γ11 w0 w1 h11 hw0 hw1 => ?_
      refine unpackWords64ToLeaves_isLegal target hv [w0, w1]
        (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> assumption)
        0 v4i32 hsupp.1 fun Γ12 fres h12' hfres => ?_
      exact packLeavesToLegal_isLegal target v4i32 fres hfres fun Γ13 res h13' hres =>
        hcont1 k hk Γ13 res ((((h16.trans h79).trans h10).trans h11).trans (h12'.trans h13')) hres
    simp only [legalOp]
    split
    · next hp =>
      by_cases hsup : target.vecIntOpSupported .sha256rnds2 v4i32 false = true
      · simp only [hsup, ↓reduceIte]
        have hl : target.legalTys v4i32 = [v4i32] := by simp [LegalTarget.legalTys, hp]
        refine isLegal_let_op3_normal target .sha256rnds2 _ _ _ _ rfl
          (by simp [LegalTarget.isLegalOp, hp, hsup])
          (ArgsNormal_cast_eq _ hl hc').1 (ArgsNormal_cast_eq _ hl ha).1 (ArgsNormal_cast_eq _ hl hw).1 hp ?_
        exact hcont1 k hk _ _ (CtxExtends.cons _ _)
          (ArgsNormal_cast_eq _ hl.symm ⟨ArgNormal.head target Γ hp, trivial⟩)
      · have hsupf : target.vecIntOpSupported .sha256rnds2 v4i32 false = false := Bool.eq_false_iff.mpr hsup
        simp only [hsupf, Bool.false_eq_true, ↓reduceIte]; exact hsc
    · exact hsc
  | sha256msg1 =>
    rcases args₂ with ⟨w0123, w4, ⟨⟩⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsupp
    have ha := legalArg_isNormal hc hsupp.1 (ArgRel_pair hargs).1
    have hb := legalArg_isNormal hc hsupp.1 (ArgRel_pair hargs).2
    have hsc : (toTFlat (splitLegalToLeaves target v4i32 (legalArg target w0123) fun fa =>
        splitLegalToLeaves target v4i32 (legalArg target w4) fun fb =>
        packLeavesToWords64 target v4i32 fa fun wa =>
        packLeavesToWords64 target v4i32 fb fun wb =>
        words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun a0 a1 a2 a3 =>
        words2ToDwords4 (wb.getD 0 (.imm 0#64)) (wb.getD 1 (.imm 0#64)) fun b0 b1 b2 b3 =>
        scalarSha256msg1 a0 a1 a2 a3 b0 b1 b2 b3 fun r0 r1 r2 r3 =>
        dwords4ToWords2 r0 r1 r2 r3 fun w0 w1 =>
        unpackWords64ToLeaves target [w0, w1] 0 v4i32 fun fres =>
        packLeavesToLegal target v4i32 fres fun res => k (res, ())) Γ.length Δ.length).isLegal target Γ Δ = true := by
      refine splitLegalToLeaves_isLegal target v4i32 (legalArg target w0123) ha fun Γ1 fa h1 hfa => ?_
      refine splitLegalToLeaves_isLegal target v4i32 (legalArg target w4) (hb.mono h1) fun Γ2 fb h2 hfb => ?_
      have h12 := h1.trans h2
      refine packLeavesToWords64_isLegal target hv v4i32 hsupp.1 fa (hfa.mono h2) fun Γ3 wa h3 hwa => ?_
      refine packLeavesToWords64_isLegal target hv v4i32 hsupp.1 fb (hfb.mono h3) fun Γ4 wb h4 hwb => ?_
      have h14 := h12.trans (h3.trans h4)
      refine words2ToDwords4_isLegal target hsupp.2 h64 _ _
        (ArgNormal_getD_i64 target h64 wa (fun x hx => (hwa x hx).mono h4) 0)
        (ArgNormal_getD_i64 target h64 wa (fun x hx => (hwa x hx).mono h4) 1)
        fun Γ5 a0 a1 a2 a3 h5 ha0 ha1 ha2 ha3 => ?_
      refine words2ToDwords4_isLegal target hsupp.2 h64 _ _
        (ArgNormal_getD_i64 target h64 wb (fun x hx => (hwb x hx).mono h5) 0)
        (ArgNormal_getD_i64 target h64 wb (fun x hx => (hwb x hx).mono h5) 1)
        fun Γ6 b0 b1 b2 b3 h6 hb0 _ _ _ => ?_
      refine scalarSha256msg1_isLegal target hsupp.2 a0 a1 a2 a3 b0 b1 b2 b3
        (ha0.mono h6) (ha1.mono h6) (ha2.mono h6) (ha3.mono h6) hb0
        fun Γ7 r0 r1 r2 r3 h7 hr0 hr1 hr2 hr3 => ?_
      refine dwords4ToWords2_isLegal target hsupp.2 h64 r0 r1 r2 r3 hr0 hr1 hr2 hr3 fun Γ8 w0 w1 h8 hw0 hw1 => ?_
      refine unpackWords64ToLeaves_isLegal target hv [w0, w1]
        (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> assumption)
        0 v4i32 hsupp.1 fun Γ9 fres h9 hfres => ?_
      exact packLeavesToLegal_isLegal target v4i32 fres hfres fun Γ10 res h10 hres =>
        hcont1 k hk Γ10 res ((((h14.trans (h5.trans h6)).trans h7).trans h8).trans (h9.trans h10)) hres
    simp only [legalOp]
    split
    · next hp =>
      have hkp : target.keepsPacked v4i32 = true := (Bool.and_eq_true _ _).mp hp |>.1
      have hsup : target.vecIntOpSupported .sha256msg1 v4i32 false = true := (Bool.and_eq_true _ _).mp hp |>.2
      have hl : target.legalTys v4i32 = [v4i32] := by simp [LegalTarget.legalTys, hkp]
      refine isLegal_let_op2_normal target .sha256msg1 _ _ _ rfl
        (by simp [LegalTarget.isLegalOp, hkp, hsup])
        (ArgsNormal_cast_eq _ hl ha).1 (ArgsNormal_cast_eq _ hl hb).1 hkp ?_
      exact hcont1 k hk _ _ (CtxExtends.cons _ _)
        (ArgsNormal_cast_eq _ hl.symm ⟨ArgNormal.head target Γ hkp, trivial⟩)
    · exact hsc
  | sha256msg2 =>
    rcases args₂ with ⟨sums, w, ⟨⟩⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsupp
    have ha := legalArg_isNormal hc hsupp.1 (ArgRel_pair hargs).1
    have hb := legalArg_isNormal hc hsupp.1 (ArgRel_pair hargs).2
    have hsc : (toTFlat (splitLegalToLeaves target v4i32 (legalArg target sums) fun fa =>
        splitLegalToLeaves target v4i32 (legalArg target w) fun fb =>
        packLeavesToWords64 target v4i32 fa fun wa =>
        packLeavesToWords64 target v4i32 fb fun wb =>
        words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun s0 s1 s2 s3 =>
        words2ToDwords4 (wb.getD 0 (.imm 0#64)) (wb.getD 1 (.imm 0#64)) fun w0 w1 w2 w3 =>
        scalarSha256msg2 s0 s1 s2 s3 w0 w1 w2 w3 fun r0 r1 r2 r3 =>
        dwords4ToWords2 r0 r1 r2 r3 fun wr0 wr1 =>
        unpackWords64ToLeaves target [wr0, wr1] 0 v4i32 fun fres =>
        packLeavesToLegal target v4i32 fres fun res => k (res, ())) Γ.length Δ.length).isLegal target Γ Δ = true := by
      refine splitLegalToLeaves_isLegal target v4i32 (legalArg target sums) ha fun Γ1 fa h1 hfa => ?_
      refine splitLegalToLeaves_isLegal target v4i32 (legalArg target w) (hb.mono h1) fun Γ2 fb h2 hfb => ?_
      have h12 := h1.trans h2
      refine packLeavesToWords64_isLegal target hv v4i32 hsupp.1 fa (hfa.mono h2) fun Γ3 wa h3 hwa => ?_
      refine packLeavesToWords64_isLegal target hv v4i32 hsupp.1 fb (hfb.mono h3) fun Γ4 wb h4 hwb => ?_
      have h14 := h12.trans (h3.trans h4)
      refine words2ToDwords4_isLegal target hsupp.2 h64 _ _
        (ArgNormal_getD_i64 target h64 wa (fun x hx => (hwa x hx).mono h4) 0)
        (ArgNormal_getD_i64 target h64 wa (fun x hx => (hwa x hx).mono h4) 1)
        fun Γ5 s0 s1 s2 s3 h5 hs0 hs1 hs2 hs3 => ?_
      refine words2ToDwords4_isLegal target hsupp.2 h64 _ _
        (ArgNormal_getD_i64 target h64 wb (fun x hx => (hwb x hx).mono h5) 0)
        (ArgNormal_getD_i64 target h64 wb (fun x hx => (hwb x hx).mono h5) 1)
        fun Γ6 w0 w1 w2 w3 h6 _ _ hw2 hw3 => ?_
      refine scalarSha256msg2_isLegal target hsupp.2 s0 s1 s2 s3 w0 w1 w2 w3
        (hs0.mono h6) (hs1.mono h6) (hs2.mono h6) (hs3.mono h6) hw2 hw3
        fun Γ7 r0 r1 r2 r3 h7 hr0 hr1 hr2 hr3 => ?_
      refine dwords4ToWords2_isLegal target hsupp.2 h64 r0 r1 r2 r3 hr0 hr1 hr2 hr3 fun Γ8 wr0 wr1 h8 hwr0 hwr1 => ?_
      refine unpackWords64ToLeaves_isLegal target hv [wr0, wr1]
        (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> assumption)
        0 v4i32 hsupp.1 fun Γ9 fres h9 hfres => ?_
      exact packLeavesToLegal_isLegal target v4i32 fres hfres fun Γ10 res h10 hres =>
        hcont1 k hk Γ10 res ((((h14.trans (h5.trans h6)).trans h7).trans h8).trans (h9.trans h10)) hres
    simp only [legalOp]
    split
    · next hp =>
      by_cases hsup : target.vecIntOpSupported .sha256msg2 v4i32 false = true
      · simp only [hsup, ↓reduceIte]
        have hl : target.legalTys v4i32 = [v4i32] := by simp [LegalTarget.legalTys, hp]
        refine isLegal_let_op2_normal target .sha256msg2 _ _ _ rfl
          (by simp [LegalTarget.isLegalOp, hp, hsup])
          (ArgsNormal_cast_eq _ hl ha).1 (ArgsNormal_cast_eq _ hl hb).1 hp ?_
        exact hcont1 k hk _ _ (CtxExtends.cons _ _)
          (ArgsNormal_cast_eq _ hl.symm ⟨ArgNormal.head target Γ hp, trivial⟩)
      · have hsupf : target.vecIntOpSupported .sha256msg2 v4i32 false = false := Bool.eq_false_iff.mpr hsup
        simp only [hsupf, Bool.false_eq_true, ↓reduceIte]; exact hsc
    · exact hsc
  | fadd t | fsub t | fmul t | fdiv t =>
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    have ha := legalArg_isNormal hc hsupp (ArgRel_pair hargs).1
    have hb := legalArg_isNormal hc hsupp (ArgRel_pair hargs).2
    simp only [legalOp]
    by_cases hft : t.isFloatTree = true
    · simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine legalBinTree_isLegal target (fun u => target.supportsTy u = true ∧ u.isFloatTree = true)
        (fun a b h => by
          simp only [LegalTarget.supportsTy, Ty.isFloatTree, Bool.and_eq_true] at h
          exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩)
        _ _ (fun _ => rfl)
        (fun a b unif _ hp hvs => by simp [LegalTarget.isLegalOp, hp, hvs])
        _ _ _ _
        (fun hP => by simp [Ty.isFloatTree] at hP)
        (fun _ hP => by simp [Ty.isFloatTree] at hP)
        (fun f hP Γ' x y cont hx hy hc' => by
          have hf : f ∈ target.floatFmts := (by simpa [LegalTarget.supportsTy] using hP.1 : f ∈ target.floatFmts ∧ f.width ≤ 64).1
          have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
          refine isLegal_let_op2_normal target _ x y _ rfl (by simp [LegalTarget.isLegalOp, hf]) hx hy hlegF ?_
          exact hc' _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' hlegF))
        t ⟨hsupp, hft⟩ (legalArg target a) (legalArg target b) none ha hb (hcont1 k hk)
    · simp [hft, toTFlat_hlt]
  | ffma t =>
    rcases args₂ with ⟨a, b, c, ⟨⟩⟩
    have ha := legalArg_isNormal hc hsupp (ArgRel_triple hargs).1
    have hb := legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.1
    have hc' := legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.2
    simp only [legalOp]
    by_cases hft : t.isFloatTree = true
    · simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine legalTernaryTree_isLegal target (fun u => target.supportsTy u = true ∧ u.isFloatTree = true)
        (fun a b h => by
          simp only [LegalTarget.supportsTy, Ty.isFloatTree, Bool.and_eq_true] at h
          exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩)
        _ _ (fun _ => rfl)
        (fun a b _ hp hvs => by simp [LegalTarget.isLegalOp, hp, hvs])
        _ _ _
        (fun hP => by simp [Ty.isFloatTree] at hP)
        (fun _ hP => by simp [Ty.isFloatTree] at hP)
        (fun f hP Γ' x y z cont hx hy hz hcont => by
          have hf : f ∈ target.floatFmts := (by simpa [LegalTarget.supportsTy] using hP.1 : f ∈ target.floatFmts ∧ f.width ≤ 64).1
          have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
          refine isLegal_let_op3_normal target (.ffma (.float f)) x y z _ rfl
            (by simp [LegalTarget.isLegalOp, hf]) hx hy hz hlegF ?_
          exact hcont _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' hlegF))
        t ⟨hsupp, hft⟩ (legalArg target a) (legalArg target b) (legalArg target c) ha hb hc' (hcont1 k hk)
    · simp [hft, toTFlat_hlt]
  | fsqrt t | fneg t | fabs t =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    have ha := legalArg_isNormal hc hsupp (ArgRel_single hargs)
    simp only [legalOp]
    by_cases hft : t.isFloatTree = true
    · simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine legalUnaryTree_isLegal target (fun u => target.supportsTy u = true ∧ u.isFloatTree = true)
        (fun a b h => by
          simp only [LegalTarget.supportsTy, Ty.isFloatTree, Bool.and_eq_true] at h
          exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩)
        _ _ (fun _ => rfl)
        (fun a b _ hp hvs => by simp [LegalTarget.isLegalOp, hp, hvs])
        _ _ _
        (fun hP => by simp [Ty.isFloatTree] at hP)
        (fun _ hP => by simp [Ty.isFloatTree] at hP)
        (fun f hP Γ' x cont hx hcont => by
          have hf : f ∈ target.floatFmts := (by simpa [LegalTarget.supportsTy] using hP.1 : f ∈ target.floatFmts ∧ f.width ≤ 64).1
          have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
          refine isLegal_let_op1_normal target _ x _ rfl (by simp [LegalTarget.isLegalOp, hf]) hx hlegF ?_
          exact hcont _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' hlegF))
        t ⟨hsupp, hft⟩ (legalArg target a) ha (hcont1 k hk)
    · simp [hft, toTFlat_hlt]
  | fcmp o t m h =>
    subst h
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    have ha := legalArg_isNormal hc hsupp (ArgRel_pair hargs).1
    have hb := legalArg_isNormal hc hsupp (ArgRel_pair hargs).2
    simp only [legalOp]
    by_cases hft : t.isFloatTree = true
    · simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact legalFCmpTree_isLegal target o t hsupp (legalArg target a) (legalArg target b) ha hb (hcont1 k hk)
    · simp [hft, toTFlat_hlt]
  | fptoui f n =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    simp only [Bool.and_eq_true] at hsupp
    have hf : f ∈ target.floatFmts := (by simpa [LegalTarget.supportsTy] using hsupp.1 : f ∈ target.floatFmts ∧ f.width ≤ 64).1
    have ha := (legalArg_isNormal hc hsupp.1 (ArgRel_single hargs)).1
    have hw := widenWidth_mem_of_supports hsupp.2
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]
      refine isLegal_let_op1_normal target (.fptoui f (target.widenWidth n)) (legalArg target a).1 _ rfl
        (by simp [LegalTarget.isLegalOp, hf, hw]) ha hlegW ?_
      exact hcont1 k hk _ (.imm _, ()) (CtxExtends.cons _ _) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      refine isLegal_let_op1_normal target (.fptoui f (target.widenWidth n)) (legalArg target a).1 _ rfl
        (by simp [LegalTarget.isLegalOp, hf, hw]) ha hlegW ?_
      exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
  | fptosi f n =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    simp only [Bool.and_eq_true] at hsupp
    have hf : f ∈ target.floatFmts := (by simpa [LegalTarget.supportsTy] using hsupp.1 : f ∈ target.floatFmts ∧ f.width ≤ 64).1
    rcases hpa : legalArg target a with ⟨a', ⟨⟩⟩
    have ha' := legalArg_isNormal hc hsupp.1 (ArgRel_single hargs)
    dsimp only at ha'; rw [hpa] at ha'
    have ha := ha'.1
    have hw := widenWidth_mem_of_supports hsupp.2
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp, hpa]
    by_cases hn0 : (n == 0) = true
    · simp [hn0]
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op1_normal target (.fptosi f (target.widenWidth n)) a' _ rfl
          (by simp [LegalTarget.isLegalOp, hf, hw]) ha hlegW ?_
        exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op1_normal target (.fptosi f (target.widenWidth n)) a' _ rfl
          (by simp [LegalTarget.isLegalOp, hf, hw]) ha hlegW ?_
        let Γ1 := (.bits (target.widenWidth n), VarKind.normal) :: Γ
        refine emitMaskToN_isLegal target hw (.var Γ.length) (ArgNormal.head target Γ hlegW) fun Γ2 rm hExt2 hrm => ?_
        exact hcont1 k hk Γ2 (rm, ()) ((CtxExtends.cons _ _).trans hExt2) ⟨hrm, trivial⟩
  | uitofp n f =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    simp only [Bool.and_eq_true] at hsupp
    have hf : f ∈ target.floatFmts := (by simpa [LegalTarget.supportsTy] using hsupp.1 : f ∈ target.floatFmts ∧ f.width ≤ 64).1
    have ha := (legalArg_isNormal hc hsupp.2 (ArgRel_single hargs)).1
    have hw := widenWidth_mem_of_supports hsupp.2
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]
      refine isLegal_let_op1_normal target (.uitofp (target.widenWidth n) f) (.imm _) _ rfl
        (by simp [LegalTarget.isLegalOp, hw, hf]) hlegW hlegF ?_
      exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegF, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      refine isLegal_let_op1_normal target (.uitofp (target.widenWidth n) f) (legalArg target a).1 _ rfl
        (by simp [LegalTarget.isLegalOp, hw, hf]) ha hlegF ?_
      exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegF, trivial⟩
  | sitofp n f =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    simp only [Bool.and_eq_true] at hsupp
    have hf : f ∈ target.floatFmts := (by simpa [LegalTarget.supportsTy] using hsupp.1 : f ∈ target.floatFmts ∧ f.width ≤ 64).1
    have ha := (legalArg_isNormal hc hsupp.2 (ArgRel_single hargs)).1
    have hw := widenWidth_mem_of_supports hsupp.2
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]
      refine isLegal_let_op1_normal target (.sitofp (target.widenWidth n) f) (.imm _) _ rfl
        (by simp [LegalTarget.isLegalOp, hw, hf]) hlegW hlegF ?_
      exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegF, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      refine emitSextToW_isLegal target hw (legalArg target a).1 ha fun Γ1 sa hExt1 hsa => ?_
      refine isLegal_let_op1_normal target (.sitofp (target.widenWidth n) f) sa _ rfl
        (by simp [LegalTarget.isLegalOp, hw, hf]) hsa hlegF ?_
      exact hcont1 k hk _ (.var Γ1.length, ()) (hExt1.trans (CtxExtends.cons _ _))
        ⟨ArgNormal.head target Γ1 hlegF, trivial⟩
  | fcvt f g =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    simp only [Bool.and_eq_true] at hsupp
    have hf : f ∈ target.floatFmts := (by simpa [LegalTarget.supportsTy] using hsupp.1 : f ∈ target.floatFmts ∧ f.width ≤ 64).1
    have hg : g ∈ target.floatFmts := (by simpa [LegalTarget.supportsTy] using hsupp.2 : g ∈ target.floatFmts ∧ g.width ≤ 64).1
    have ha := (legalArg_isNormal hc hsupp.1 (ArgRel_single hargs)).1
    have hlegG : target.isLegalTy (.float g) = true := by simpa [LegalTarget.isLegalTy] using hg
    simp only [legalOp]
    refine isLegal_let_op1_normal target (.fcvt f g) (legalArg target a).1 _ rfl
      (by simp [LegalTarget.isLegalOp, hf, hg]) ha hlegG ?_
    exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegG, trivial⟩

private theorem TBlocks_isLegal_of_forall (target : LegalTarget) {rs : List Ty}
    {Γ : List (Ty × VarKind)} {Δ : List (List Ty)} :
    ∀ {sig : List (List Ty)} (bs : Blocks K KL rs sig),
      (∀ ts (i : Member ts sig),
        target.isLegalSig ts = true ∧
        (toTFlat (bs.get i (Tup.levels ts Γ.length)) (Γ.length + ts.length) Δ.length).isLegal target
          (pushNormal ts Γ) Δ = true) →
      (toTBlocks bs Γ.length Δ.length).isLegal target Γ Δ = true
  | [], .nil, _ => rfl
  | ts :: sig', .cons b bs, h => by
    rw [toTBlocks_cons, TBlocks.isLegal_cons]
    have h0 := h ts .here
    simp only [Bool.and_eq_true] at h0 ⊢
    refine ⟨⟨h0.1, h0.2⟩, TBlocks_isLegal_of_forall target bs fun ts' i => h ts' (.there i)⟩

private theorem TBlocks_supportsSource_get (target : LegalTarget) {rs : List Ty} :
    ∀ {sig : List (List Ty)} (bs : Blocks K KL rs sig) {nv nl : Nat},
      (toTBlocks bs nv nl).supportsSource target = true →
      ∀ {ts} (i : Member ts sig),
        ts.all target.supportsTy = true ∧
        (toTFlat (bs.get i (Tup.levels ts nv)) (nv + ts.length) nl).supportsSource target = true
  | _, .cons b bs, nv, nl, hs, _, .here => by
    rw [toTBlocks_cons] at hs
    simp only [TBlocks.supportsSource, Bool.and_eq_true] at hs
    exact ⟨hs.1.1, hs.1.2⟩
  | _, .cons b bs, nv, nl, hs, ts, .there i => by
    rw [toTBlocks_cons] at hs
    simp only [TBlocks.supportsSource, Bool.and_eq_true] at hs
    exact TBlocks_supportsSource_get target bs hs.2 i

private theorem member_map_inv {α β : Type} (f : α → β) :
    ∀ {xs : List α} {b : β} (i' : Member b (xs.map f)),
      ∃ a, ∃ (i : Member a xs), b = f a ∧ HEq i' (Member.map f i) := by
  intro xs b i'
  induction xs generalizing b with
  | nil => cases i'
  | cons a xs ih =>
    cases i' with
    | here => exact ⟨a, .here, rfl, HEq.rfl⟩
    | there j =>
      obtain ⟨a0, i0, rfl, hij⟩ := ih j
      exact ⟨a0, .there i0, rfl, by cases hij; exact HEq.rfl⟩

theorem legalExpr_isLegal_wf (target : LegalTarget) (hv : target.valid = true) :
    {rs : List Ty} → {G : Ctx K (LVar target K)} → {D : Ctx KL (LLab target KL)} →
    {e₁ : Expr K KL rs} → {e₂ : Expr (LVar target K) (LLab target KL) rs} →
    Wf G D e₁ e₂ →
    ∀ {Γ : List (Ty × VarKind)} {Δ : List (List Ty)} (nv₁ nl₁ : Nat),
      CLegal target Γ G → DLegal target Δ D →
      (toTFlat e₁ nv₁ nl₁).supportsSource target = true →
      rs.all target.supportsTy = true →
      (toTFlat (legalExpr target e₂) Γ.length Δ.length).isLegal target Γ Δ = true := by
  intro rs G D e₁ e₂ hwf
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop hk ih =>
    intro Γ Δ nv₁ nl₁ hc hd hs hrs
    rw [toTFlat_let] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hs
    rw [legalExpr.eq_1]
    refine legalOp_isLegal target hv hc hop hs.1 nv₁ fun Γ' res hExt hres => ?_
    exact ih (Tup.levels ts nv₁) res (nv₁ + ts.length) nl₁ (hc.mono hExt |>.pushTRel hres) hd hs.2 hrs
  | @load G D t a₁ a₂ k₁ k₂ ha hk ih =>
    intro Γ Δ nv₁ nl₁ hc hd hs hrs
    rw [toTFlat_load] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true, decide_eq_true_eq] at hs
    have h64 := valid_mem64 hv
    have h64w : target.widenWidth 64 = 64 := widenWidth_eq_self_of_mem target h64
    rw [legalExpr.eq_2, dite_eq_left h64w]
    have hs64 : target.supportsTy i64 = true := supportsTy_bits_iff.2 ⟨⟨64, h64, Nat.le_refl 64⟩, by omega⟩
    have haN : ArgNormal target Γ i64 (castArgBits h64w (legalArg target a₂).1) :=
      ArgNormal.cast h64w (legalArg_isNormal hc hs64 ha).1
    refine legalLoad_isLegal target hv t _ hs.1.1 haN fun Γ' res hExt hres => ?_
    refine ih nv₁ res (nv₁ + 1) nl₁ ?_ hd hs.2 hrs
    intro t' lv₁ lv₂ hm
    rcases List.mem_cons.1 hm with ⟨rfl, rfl, rfl⟩ | htail
    · exact hres
    · exact (hc t' lv₁ lv₂ htail).mono hExt
  | @store G D t v₁ v₂ a₁ a₂ k₁ k₂ hv_rel ha hk ih =>
    intro Γ Δ nv₁ nl₁ hc hd hs hrs
    rw [toTFlat_store] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true, decide_eq_true_eq] at hs
    have h64 := valid_mem64 hv
    have h64w : target.widenWidth 64 = 64 := widenWidth_eq_self_of_mem target h64
    rw [legalExpr.eq_3, dite_eq_left h64w]
    have hs64 : target.supportsTy i64 = true := supportsTy_bits_iff.2 ⟨⟨64, h64, Nat.le_refl 64⟩, by omega⟩
    have hvN := legalArg_isNormal hc hs.1.1 hv_rel
    have haN : ArgNormal target Γ i64 (castArgBits h64w (legalArg target a₂).1) :=
      ArgNormal.cast h64w (legalArg_isNormal hc hs64 ha).1
    refine legalStore_isLegal target hv t (legalArg target v₂) _ hs.1.1 hvN haN fun Γ' hExt => ?_
    exact ih nv₁ nl₁ (hc.mono hExt) hd hs.2 hrs
  | @call G D f as bs args₁ args₂ k₁ k₂ hargs hk ih =>
    intro Γ Δ nv₁ nl₁ hc hd hs hrs
    rw [toTFlat_call] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hs
    rw [legalExpr.eq_4, toTFlat_call, TFlat.isLegal_call]
    have hArgsN := joinArgs_isNormal hc hs.1.1 hargs
    have hsigA := isLegalSig_legalSig hv hs.1.1
    have hsigB := isLegalSig_legalSig hv hs.1.2
    simp only [hsigA, hsigB, hArgsN.checkLegalArgs, Bool.true_and]
    let Γ' := pushNormal (target.legalSig bs) Γ
    have hlen : Γ'.length = Γ.length + (target.legalSig bs).length := by
      simp [Γ', pushNormal_length, Nat.add_comm]
    rw [← hlen]
    exact ih (Tup.levels bs nv₁) (splitParams target bs (Tup.levels (target.legalSig bs) Γ.length))
      (nv₁ + bs.length) nl₁ (CLegal.pushSplit target hv hc bs hs.1.2 _) hd hs.2 hrs
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hrel ht he iht ihe =>
    intro Γ Δ nv₁ nl₁ hc hd hs hrs
    rw [toTFlat_jnz] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hs
    rcases hpc : legalArg target c₂ with ⟨c', ⟨⟩⟩
    have hcN := legalArg_isNormal hc rfl hrel
    rw [hpc] at hcN
    simp only [legalExpr.eq_5, toTFlat_jnz, TFlat.isLegal_jnz, hpc, hcN.1.checkLegalArg, Bool.true_and, Bool.and_eq_true]
    exact ⟨iht nv₁ nl₁ hc hd hs.1 hrs, ihe nv₁ nl₁ hc hd hs.2 hrs⟩
  | @jump G D ts j₁ j₂ args₁ args₂ hj hargs =>
    intro Γ Δ _ _ hc hd hs _
    rw [toTFlat_jump] at hs
    simp only [TFlat.supportsSource] at hs
    rw [legalExpr.eq_6, toTFlat_jump, TFlat.isLegal_jump]
    obtain ⟨hlt, hget, hts⟩ := hd ts j₁ j₂ hj
    have hsigT := isLegalSig_legalSig hv hts
    have hArgsN := joinArgs_isNormal hc hts hargs
    simp only [hlt, ↓reduceIte, hget, hsigT, hArgsN.checkLegalArgs, Bool.true_and, Bool.and_true]
    cases hd' : listTyDecEq (target.legalSig ts) (target.legalSig ts) with
    | isTrue _ => rfl
    | isFalse hf => exact absurd rfl hf
  | @ret G D vs₁ vs₂ hvs =>
    intro Γ Δ _ _ hc _ _ hrs
    rw [legalExpr.eq_7, toTFlat_ret, TFlat.isLegal_ret]
    have hsigR := isLegalSig_legalSig hv hrs
    have hArgsN := joinArgs_isNormal hc hrs hvs
    simp [hsigR, hArgsN.checkLegalArgs]
  | @exit G D f as args₁ args₂ hargs =>
    intro Γ Δ _ _ hc _ hs _
    rw [toTFlat_exit] at hs
    simp only [TFlat.supportsSource] at hs
    rw [legalExpr.eq_8, toTFlat_exit, TFlat.isLegal_exit]
    have hsigA := isLegalSig_legalSig hv hs
    have hArgsN := joinArgs_isNormal hc hs hargs
    simp [hsigA, hArgsN.checkLegalArgs]
  | @hlt G D =>
    intro _ _ _ _ _ _ _ _
    simp [legalExpr.eq_9]
  | @group G D sig b₁ b₂ k₁ k₂ hb hk ihb ihk =>
    intro Γ Δ nv₁ nl₁ hc hd hs hrs
    rw [toTFlat_group] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hs
    rw [legalExpr.eq_10, toTFlat_group, TFlat.isLegal_group]
    have hsigAll : (sig.map target.legalSig).all target.isLegalSig = true := by
      rw [List.all_map]
      exact List.all_eq_true.mpr fun ts hts =>
        isLegalSig_legalSig hv (List.all_eq_true.mp hs.1.1 ts hts)
    let Js₁ := Tup.levels sig nl₁
    let Js₂ := tupLiftMap target.legalSig KL (Tup.levels (sig.map target.legalSig) Δ.length)
    let Δ' := pushTypes (sig.map target.legalSig) Δ
    have hD' : DLegal target Δ' (Tup.zip Js₁ Js₂ ++ D) :=
      DLegal.pushLiftMap target hd sig hs.1.1 nl₁
    have hlenΔ : Δ'.length = Δ.length + (sig.map target.legalSig).length := by
      simp [Δ', pushTypes_length, Nat.add_comm]
    rw [← hlenΔ]
    have hB : (toTBlocks (legalBlocks target (b₂ Js₂)) Γ.length Δ'.length).isLegal target Γ Δ' = true := by
      refine TBlocks_isLegal_of_forall target (legalBlocks target (b₂ Js₂)) fun ts' i' => ?_
      obtain ⟨ts, i, rfl, heqi⟩ := member_map_inv target.legalSig i'
      have heqi' : i' = Member.map target.legalSig i := eq_of_heq heqi
      subst heqi'
      obtain ⟨hts_supp, hget_supp⟩ := TBlocks_supportsSource_get target (b₁ Js₁) hs.1.2 i
      have hsigT := isLegalSig_legalSig hv hts_supp
      refine ⟨hsigT, ?_⟩
      rw [legalBlocks_get]
      let Γ' := pushNormal (target.legalSig ts) Γ
      have hlenΓ : Γ'.length = Γ.length + (target.legalSig ts).length := by
        simp [Γ', pushNormal_length, Nat.add_comm]
      rw [← hlenΓ]
      exact ihb Js₁ Js₂ i (Tup.levels ts nv₁) (splitParams target ts (Tup.levels (target.legalSig ts) Γ.length))
        (nv₁ + ts.length) (nl₁ + sig.length)
        (CLegal.pushSplit target hv hc ts hts_supp (Tup.levels ts nv₁)) hD' hget_supp hrs
    have hK : (toTFlat (legalExpr target (k₂ Js₂)) Γ.length Δ'.length).isLegal target Γ Δ' = true :=
      ihk Js₁ Js₂ nv₁ (nl₁ + sig.length) hc hD' hs.2 hrs
    simp only [hsigAll, Bool.true_and, Bool.and_eq_true]
    exact ⟨hB, hK⟩

theorem Func.legal_isLegal (target : LegalTarget) {as rs : List Ty} (f : Func as rs)
    (hf : f.Wf) (hsupp : f.supportsSource target = true) :
    (f.legal target).isLegal target = true := by
  simp only [Func.supportsSource, Bool.and_eq_true] at hsupp
  rcases hsupp with ⟨⟨⟨hv, has⟩, hrs⟩, hbody⟩
  simp only [Func.isLegal, Bool.and_eq_true]
  refine ⟨⟨isLegalSig_legalSig hv has, isLegalSig_legalSig hv hrs⟩, ?_⟩
  let Γ₀ := pushNormal (target.legalSig as) []
  have hlen₀ : Γ₀.length = (target.legalSig as).length := by simp [Γ₀, pushNormal_length]
  change (toTFlat (legalExpr target (f (LVar target K) (LLab target KL)
    (splitParams target as (Tup.levels (target.legalSig as) 0)))) (target.legalSig as).length 0).isLegal
      target Γ₀ [] = true
  rw [← hlen₀, show (0 : Nat) = ([] : List (List Ty)).length from rfl]
  have hc₀ : CLegal target Γ₀ (Tup.zip (Tup.levels as 0)
      (splitParams target as (Tup.levels (target.legalSig as) ([] : List (Ty × VarKind)).length)) ++ []) :=
    CLegal.pushSplit target hv (fun _ _ _ h => by cases h) as has (Tup.levels as 0)
  have hd₀ : DLegal target ([] : List (List Ty)) [] := fun _ _ _ h => by cases h
  exact legalExpr_isLegal_wf target hv
    (hf K (LVar target K) KL (LLab target KL) (Tup.levels as 0)
      (splitParams target as (Tup.levels (target.legalSig as) 0)))
    as.length 0 (by simpa using hc₀) hd₀ hbody hrs

theorem Fn.legal_isLegal (target : LegalTarget) (fn : Fn)
    (hf : fn.Wf) (hsupp : fn.body.supportsSource target = true) :
    (fn.legal target).body.isLegal target = true :=
  Func.legal_isLegal target fn.body hf hsupp


end LegalIsLegal

end LeanQbe.T
