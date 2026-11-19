module

public import LeanQbe.T.LegalCheck3a

/-!
# Target legality proofs for `LeanQbe.T.Legal` (Part 3a-ii: `legalOp_isLegal`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

section LegalIsLegal

theorem legalOp_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) {Γ : List (Ty × VarKind)} {LG : Ctx K (LVar target K)}
    (hc : CLegal target Γ LG) {ts : List Ty} {op₁ : Op K ts} {op₂ : Op (LVar target K) ts}
    (hop : OpRel LG op₁ op₂) (hsupp : target.supportsOpCode op₁.code = true) (nv₁ : Nat := 0)
    {k : Tup (LVar target K) ts → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ
      (fun Γ' res =>
      ∀ t v₂, (∃ v₁, ⟨t, v₁, v₂⟩ ∈ Tup.zip (Tup.levels ts nv₁) res) → ArgsNormal target Γ' v₂) k) :
    (toTFlat (legalOp target op₂ k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  if hpart : isLegalOpPart2 op₁.code = true then
    exact legalOp_isLegal_part2 target hv hc hop hsupp hpart nv₁ hk
  else
  have hcont1 := @legalOp_isLegal_cont1 target Γ Δ rs nv₁
  have hcont2 := @legalOp_isLegal_cont2 target Γ Δ rs nv₁
  have h64 := valid_mem64 hv
  rcases hop with @⟨_, _, code, args₁, args₂, hargs⟩
  dsimp only [Op.code] at hpart
  dsimp only [Op.code, LegalTarget.supportsOpCode] at hsupp
  cases code with
  | copy t =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    exact hcont1 k hk Γ (legalArg target a) (CtxExtends.refl Γ)
      (legalArg_isNormal hc hsupp (ArgRel_single hargs))
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
      refine legalUnaryTree_isLegal target
        (fun u => target.supportsTy u = true ∧ !u.hasFloat = true)
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
          have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
            simpa [LegalTarget.isLegalTy] using hw
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
        have hf : f ∈ target.floatFmts :=
          (by simpa [LegalTarget.supportsTy] using hP : f ∈ target.floatFmts ∧ f.width ≤ 64).1
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
        have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
          simpa [LegalTarget.isLegalTy] using hw
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
        have hf : f ∈ target.floatFmts :=
          (by simpa [LegalTarget.supportsTy] using hP : f ∈ target.floatFmts ∧ f.width ≤ 64).1
        have ⟨hfw, _⟩ := valid_float_spec hv hf
        have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
        have hlegFw : target.isLegalTy (.bits f.width) = true := by
          simpa [LegalTarget.isLegalTy] using hfw
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
          refine isLegal_let_op1_normal target (.bitcast (.bits f.width) (.float f) rfl)
            (.var Γ1.length) _ rfl
            (by simp [LegalTarget.isLegalOp, hlegFw, hlegF, bne_iff_ne])
              (ArgNormal.head target Γ1 hlegFw) hlegF ?_
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
      (fun _ Γ' x y z cont hx hy hz hcont =>
        emitTernlogBool_isLegal target x y z imm hx hy hz hcont)
      (fun n hP Γ' x y z cont hx hy hz hcont => by
        have hw := widenWidth_mem_of_supports hP
        have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
          simpa [LegalTarget.isLegalTy] using hw
        by_cases hn0 : (n == 0) = true
        · simp only [hn0, ↓reduceIte]; exact hcont Γ' (.imm _) (CtxExtends.refl Γ') hlegW
        · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
          by_cases hst : target.scalarTernlog = true
          · simp only [hst, ↓reduceIte]
            refine isLegal_let_op3_normal target (.ternlog (.bits (target.widenWidth n)) imm) x y z
              _ rfl
              (by simp [LegalTarget.isLegalOp, hst, hw]) hx hy hz hlegW ?_
            exact emitMaskToN_isLegal target hw (.var Γ'.length) (ArgNormal.head target Γ' hlegW)
              fun Γ'' r hExt'' hr => hcont Γ'' r ((CtxExtends.cons _ _).trans hExt'') hr
          · simp only [hst, Bool.false_eq_true, ↓reduceIte]
            refine emitTernlogBits_isLegal target hw x y z imm hx hy hz fun Γ1 r hExt1 hr => ?_
            exact emitMaskToN_isLegal target hw r hr fun Γ2 r' hExt2 hr' =>
              hcont Γ2 r' (hExt1.trans hExt2) hr')
      (fun f hP Γ' x y z cont hx hy hz hcont => by
        have hf : f ∈ target.floatFmts :=
          (by simpa [LegalTarget.supportsTy] using hP : f ∈ target.floatFmts ∧ f.width ≤ 64).1
        have ⟨hfw, _⟩ := valid_float_spec hv hf
        have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
        have hlegFw : target.isLegalTy (.bits f.width) = true := by
          simpa [LegalTarget.isLegalTy] using hfw
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
            (by simp [LegalTarget.isLegalOp, hlegF, hlegFw, bne_iff_ne]) (hz.mono (h1.trans h2))
              hlegFw ?_
          let Γ3 := (.bits f.width, VarKind.normal) :: Γ2
          have h13 : CtxExtends Γ' Γ3 := h1.trans (h2.trans (CtxExtends.cons _ _))
          have hx3 : ArgNormal target Γ3 (.bits f.width) (.var Γ'.length) :=
            (ArgNormal.head target Γ' hlegFw).mono
              (h2.trans (CtxExtends.cons (.bits f.width, VarKind.normal) Γ2))
          have hy3 : ArgNormal target Γ3 (.bits f.width) (.var Γ1.length) :=
            (ArgNormal.head target Γ1 hlegFw).mono
              (CtxExtends.cons (.bits f.width, VarKind.normal) Γ2)
          have hz3 := ArgNormal.head target Γ2 hlegFw
          have hstep :
            IsLegalCont target Γ3 Δ (fun Γ'' br => ArgNormal target Γ'' (.bits f.width) br)
            fun br =>
              .let_ (op1 (.bitcast (.bits f.width) (.float f) rfl) br) fun (r, ()) =>
                cont (.var r) := by
            intro Γ4 br hExt4 hbr
            refine isLegal_let_op1_normal target (.bitcast (.bits f.width) (.float f) rfl) br _ rfl
              (by simp [LegalTarget.isLegalOp, hlegFw, hlegF, bne_iff_ne]) hbr hlegF ?_
            exact hcont _ (.var Γ4.length) ((h13.trans hExt4).trans (CtxExtends.cons _ _))
              (ArgNormal.head target Γ4 hlegF)
          by_cases hst : target.scalarTernlog = true
          · simp only [hst, ↓reduceIte]
            refine isLegal_let_op3_normal target (.ternlog (.bits f.width) imm) (.var Γ'.length)
              (.var Γ1.length) (.var Γ2.length) _ rfl
              (by simp [LegalTarget.isLegalOp, hst, hfw]) hx3 hy3 hz3 hlegFw ?_
            exact hstep _ (.var Γ3.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ3 hlegFw)
          · simp only [hst, Bool.false_eq_true, ↓reduceIte]
            exact emitTernlogBits_isLegal target hfw (.var Γ'.length) (.var Γ1.length)
              (.var Γ2.length) imm hx3 hy3 hz3 hstep)
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
        t ⟨hsupp, by simp [hff]⟩ (legalArg target a) (legalArg target b) (some b) ha hb
          (hcont1 k hk)
  | fshl n =>
    rcases args₂ with ⟨a, b, c, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_triple hargs).1).1
    have hb := (legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.1).1
    have hc' := (legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.2).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte];
        exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op3_normal target (.fshl (target.widenWidth n)) (legalArg target a).1
          (legalArg target b).1 (legalArg target c).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hc' hlegW ?_
        exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _)
          ⟨ArgNormal.head target Γ hlegW, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_isLegal target hv hw (legalArg target c).1 hc' fun Γ1 cm hExt1 hcm => ?_
        refine isLegal_let_op2_normal target (.sub (.bits (target.widenWidth n))) (.imm _) cm _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) hlegW hcm hlegW ?_
        let Γ2 := (.bits (target.widenWidth n), VarKind.normal) :: Γ1
        have h12 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.shl (.bits (target.widenWidth n)))
          (legalArg target a).1 cm _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ha.mono h12) (hcm.mono (CtxExtends.cons _ _)) hlegW
            ?_
        let Γ3 := (.bits (target.widenWidth n), VarKind.normal) :: Γ2
        have h13 : CtxExtends Γ Γ3 := h12.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.lshr (.bits (target.widenWidth n)))
          (legalArg target b).1 (.var Γ1.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (hb.mono h13)
            ((ArgNormal.head target Γ1 hlegW).mono (CtxExtends.cons _ _)) hlegW ?_
        let Γ4 := (.bits (target.widenWidth n), VarKind.normal) :: Γ3
        refine isLegal_let_op2_normal target (.or (.bits (target.widenWidth n))) (.var Γ2.length)
          (.var Γ3.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw])
            ((ArgNormal.head target Γ2 hlegW).mono (CtxExtends.cons _ _))
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
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte];
        exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op3_normal target (.fshr (target.widenWidth n)) (legalArg target a).1
          (legalArg target b).1 (legalArg target c).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hc' hlegW ?_
        exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _)
          ⟨ArgNormal.head target Γ hlegW, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_isLegal target hv hw (legalArg target c).1 hc' fun Γ1 cm hExt1 hcm => ?_
        refine isLegal_let_op2_normal target (.sub (.bits (target.widenWidth n))) (.imm _) cm _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) hlegW hcm hlegW ?_
        let Γ2 := (.bits (target.widenWidth n), VarKind.normal) :: Γ1
        have h12 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.lshr (.bits (target.widenWidth n)))
          (legalArg target b).1 cm _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (hb.mono h12) (hcm.mono (CtxExtends.cons _ _)) hlegW
            ?_
        let Γ3 := (.bits (target.widenWidth n), VarKind.normal) :: Γ2
        have h13 : CtxExtends Γ Γ3 := h12.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.shl (.bits (target.widenWidth n)))
          (legalArg target a).1 (.var Γ1.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ha.mono h13)
            ((ArgNormal.head target Γ1 hlegW).mono (CtxExtends.cons _ _)) hlegW ?_
        let Γ4 := (.bits (target.widenWidth n), VarKind.normal) :: Γ3
        refine isLegal_let_op2_normal target (.or (.bits (target.widenWidth n))) (.var Γ2.length)
          (.var Γ3.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw])
            ((ArgNormal.head target Γ2 hlegW).mono (CtxExtends.cons _ _))
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
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte];
        exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op1_normal target (.clz (target.widenWidth n)) (legalArg target a).1 _
          rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hlegW ?_
        exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _)
          ⟨ArgNormal.head target Γ hlegW, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op1_normal target (.clz (target.widenWidth n)) (legalArg target a).1 _
          rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hlegW ?_
        let Γ1 := (.bits (target.widenWidth n), VarKind.normal) :: Γ
        refine isLegal_let_op2_normal target (.sub (.bits (target.widenWidth n))) (.var Γ.length)
          (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.head target Γ hlegW) hlegW hlegW ?_
        exact hcont1 k hk _ (.var Γ1.length, ()) ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _))
          ⟨ArgNormal.head target Γ1 hlegW, trivial⟩
  | cls n =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_single hargs)).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte];
        exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op1_normal target (.cls (target.widenWidth n)) (legalArg target a).1 _
          rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hlegW ?_
        exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _)
          ⟨ArgNormal.head target Γ hlegW, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitSextToW_isLegal target hw (legalArg target a).1 ha fun Γ1 sa hExt1 hsa => ?_
        refine isLegal_let_op1_normal target (.cls (target.widenWidth n)) sa _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) hsa hlegW ?_
        let Γ2 := (.bits (target.widenWidth n), VarKind.normal) :: Γ1
        refine isLegal_let_op2_normal target (.sub (.bits (target.widenWidth n))) (.var Γ1.length)
          (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.head target Γ1 hlegW) hlegW hlegW ?_
        exact hcont1 k hk _ (.var Γ2.length, ())
          (hExt1.trans ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _)))
          ⟨ArgNormal.head target Γ2 hlegW, trivial⟩
  | rbit n =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_single hargs)).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte];
        exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op1_normal target (.rbit (target.widenWidth n)) (legalArg target a).1 _
          rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hlegW ?_
        exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _)
          ⟨ArgNormal.head target Γ hlegW, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op1_normal target (.rbit (target.widenWidth n)) (legalArg target a).1 _
          rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hlegW ?_
        let Γ1 := (.bits (target.widenWidth n), VarKind.normal) :: Γ
        refine isLegal_let_op2_normal target (.lshr (.bits (target.widenWidth n))) (.var Γ.length)
          (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.head target Γ hlegW) hlegW hlegW ?_
        exact hcont1 k hk _ (.var Γ1.length, ()) ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _))
          ⟨ArgNormal.head target Γ1 hlegW, trivial⟩
  | ctz n =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_single hargs)).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte];
        exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op1_normal target (.ctz (target.widenWidth n)) (legalArg target a).1 _
          rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hlegW ?_
        exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _)
          ⟨ArgNormal.head target Γ hlegW, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op2_normal target (.or (.bits (target.widenWidth n)))
          (legalArg target a).1 (.imm _) _ rfl
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
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte];
        exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      refine isLegal_let_op1_normal target (.popcnt (target.widenWidth n)) (legalArg target a).1 _
        rfl
        (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hlegW ?_
      exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _)
        ⟨ArgNormal.head target Γ hlegW, trivial⟩
  | cmp o t m h =>
    subst h
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    have ha := legalArg_isNormal hc hsupp (ArgRel_pair hargs).1
    have hb := legalArg_isNormal hc hsupp (ArgRel_pair hargs).2
    simp only [legalOp]
    by_cases hf : t.hasFloat = true
    · simp [hf, toTFlat_hlt]
    · simp only [hf, Bool.false_eq_true, ↓reduceIte]
      exact legalCmpTree_isLegal target hv o t hsupp (legalArg target a) (legalArg target b) ha hb
        (hcont1 k hk)
  | select t =>
    rcases args₂ with ⟨c, a, b, ⟨⟩⟩
    have hcs := (legalArg_isNormal hc rfl (ArgRel_triple hargs).1).1
    have ha := legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.1
    have hb := legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.2
    simp only [legalOp]
    exact legalSelectTree_isLegal target (legalArg target c).1 hcs t hsupp (legalArg target a)
      (legalArg target b) ha hb (hcont1 k hk)
  | blend t m h =>
    subst h
    dsimp only [LegalTarget.supportsOpCode] at hsupp
    rcases args₂ with ⟨c, a, b, ⟨⟩⟩
    have hc' := legalArg_isNormal hc (supportsTy_mask target t) (ArgRel_triple hargs).1
    have ha := legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.1
    have hb := legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.2
    simp only [legalOp]
    exact legalBlendTree_isLegal target t hsupp (legalArg target c) (legalArg target a)
      (legalArg target b) hc' ha hb (hcont1 k hk)
  | zext m n =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    simp only [Bool.and_eq_true] at hsupp
    rcases hpa : legalArg target a with ⟨a', ⟨⟩⟩
    have ha' := legalArg_isNormal hc hsupp.1 (ArgRel_single hargs)
    dsimp only at ha'; rw [hpa] at ha'
    have ha := ha'.1
    have hwm := widenWidth_mem_of_supports hsupp.1
    have hwn := widenWidth_mem_of_supports hsupp.2
    have hlegWn : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hwn
    simp only [legalOp, hpa]
    by_cases hmn : m > n
    · simp [hmn]
    · simp only [hmn, ↓reduceIte]
      by_cases hm0 : (m == 0) = true
      · simp only [hm0, ↓reduceIte];
          exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegWn, trivial⟩
      · simp only [hm0, Bool.false_eq_true, ↓reduceIte]
        by_cases heq : target.widenWidth m = target.widenWidth n
        · simp only [heq, ↓reduceDIte]
          exact hcont1 k hk Γ (castArgBits heq a', ()) (CtxExtends.refl Γ)
            ⟨ArgNormal.cast heq ha, trivial⟩
        · simp only [heq, ↓reduceDIte]
          by_cases hlt : target.widenWidth m < target.widenWidth n
          · simp only [hlt, ↓reduceIte]
            refine isLegal_let_op1_normal target (.zext (target.widenWidth m) (target.widenWidth n))
              a' _ rfl
              (by simp [LegalTarget.isLegalOp, hwm, hwn, hlt]) ha hlegWn ?_
            exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _)
              ⟨ArgNormal.head target Γ hlegWn, trivial⟩
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
    have hlegWn : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hwn
    simp only [legalOp, hpa]
    by_cases hmn : m > n
    · simp [hmn]
    · simp only [hmn, ↓reduceIte]
      by_cases hm0 : (m == 0) = true
      · simp only [hm0, ↓reduceIte];
          exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegWn, trivial⟩
      · simp only [hm0, Bool.false_eq_true, ↓reduceIte]
        refine emitSextToW_isLegal target hwm a' ha fun Γ1 sx hExt1 hsx => ?_
        have hstep2 :
          IsLegalCont target Γ1 Δ (fun Γ' r => ArgNormal target Γ' (.bits (target.widenWidth n)) r)
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
            refine isLegal_let_op1_normal target (.sext (target.widenWidth m) (target.widenWidth n))
              sx _ rfl
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
    have hlegWn : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hwn
    simp only [legalOp, hpa]
    by_cases hnm : n > m
    · simp [hnm]
    · simp only [hnm, ↓reduceIte]
      by_cases hn0 : (n == 0) = true
      · simp only [hn0, ↓reduceIte];
          exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegWn, trivial⟩
      · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
        have hstep2 :
          IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' (.bits (target.widenWidth n)) r)
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
            refine isLegal_let_op1_normal target
              (.trunc (target.widenWidth m) (target.widenWidth n)) a' _ rfl
              (by simp [LegalTarget.isLegalOp, hwm, hwn, hlt]) ha hlegWn ?_
            exact hstep2 _ (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hlegWn)
          · simp [hlt]
  | ofBool n =>
    rcases args₂ with ⟨c, ⟨⟩⟩
    have hc' := (legalArg_isNormal hc rfl (ArgRel_single hargs)).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte];
        exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      refine isLegal_let_op1_normal target (.ofBool (target.widenWidth n)) (legalArg target c).1 _
        rfl
        (by simp [LegalTarget.isLegalOp, hw, hwpos]) hc' hlegW ?_
      exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _)
        ⟨ArgNormal.head target Γ hlegW, trivial⟩
  | addc n =>
    rcases args₂ with ⟨a, b, c, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_triple hargs).1).1
    have hb := (legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.1).1
    have hc' := (legalArg_isNormal hc rfl (ArgRel_triple hargs).2.2).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]
      exact hcont2 k hk Γ (.imm _, ()) ((legalArg target c).1, ()) (CtxExtends.refl Γ)
        ⟨hlegW, trivial⟩ ⟨hc', trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op3_2res target (.addc (target.widenWidth n)) (legalArg target a).1
          (legalArg target b).1 (legalArg target c).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hc' hlegW rfl ?_
        have hvt := ArgsNormal_varsTup_levels target [.bits (target.widenWidth n), .bool] Γ
          (by simp [LegalTarget.isLegalSig, LegalTarget.isLegalTy, hw])
        exact hcont2 k hk _ (.var Γ.length, ()) (.var (Γ.length + 1), ())
          (CtxExtends.pushNormal _ _)
          ⟨hvt.1, trivial⟩ ⟨hvt.2.1, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op1_normal target (.ofBool (target.widenWidth n)) (legalArg target c).1 _
          rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) hc' hlegW ?_
        let Γ1 := (.bits (target.widenWidth n), VarKind.normal) :: Γ
        have h1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
        refine isLegal_let_op2_normal target (.add (.bits (target.widenWidth n)))
          (legalArg target a).1 (legalArg target b).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ha.mono h1) (hb.mono h1) hlegW ?_
        let Γ2 := (.bits (target.widenWidth n), VarKind.normal) :: Γ1
        have h2 : CtxExtends Γ1 Γ2 := CtxExtends.cons _ _
        refine isLegal_let_op2_normal target (.add (.bits (target.widenWidth n))) (.var Γ1.length)
          (.var Γ.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.head target Γ1 hlegW)
            ((ArgNormal.head target Γ hlegW).mono h2) hlegW ?_
        let Γ3 := (.bits (target.widenWidth n), VarKind.normal) :: Γ2
        have h13 : CtxExtends Γ Γ3 := h1.trans (h2.trans (CtxExtends.cons _ _))
        refine emitMaskToN_isLegal target hw (.var Γ2.length) (ArgNormal.head target Γ2 hlegW)
          fun Γ4 s hExt4 hs => ?_
        have hsw : ArgNormal target Γ4 (.bits (target.widenWidth n)) (.var Γ2.length) :=
          (ArgNormal.head target Γ2 hlegW).mono hExt4
        refine isLegal_let_op2_normal target (.ule (.bits (target.widenWidth n))) (.imm _)
          (.var Γ2.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) hlegW hsw rfl ?_
        let Γ5 := (.bool, VarKind.normal) :: Γ4
        exact hcont2 k hk Γ5 (s, ()) (.var Γ4.length, ())
          ((h13.trans hExt4).trans (CtxExtends.cons _ _))
          ⟨hs.mono (CtxExtends.cons _ _), trivial⟩ ⟨ArgNormal.head target Γ4 rfl, trivial⟩
  | subb n =>
    rcases args₂ with ⟨a, b, c, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_triple hargs).1).1
    have hb := (legalArg_isNormal hc hsupp (ArgRel_triple hargs).2.1).1
    have hc' := (legalArg_isNormal hc rfl (ArgRel_triple hargs).2.2).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]
      exact hcont2 k hk Γ (.imm _, ()) ((legalArg target c).1, ()) (CtxExtends.refl Γ)
        ⟨hlegW, trivial⟩ ⟨hc', trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op3_2res target (.subb (target.widenWidth n)) (legalArg target a).1
          (legalArg target b).1 (legalArg target c).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hc' hlegW rfl ?_
        have hvt := ArgsNormal_varsTup_levels target [.bits (target.widenWidth n), .bool] Γ
          (by simp [LegalTarget.isLegalSig, LegalTarget.isLegalTy, hw])
        exact hcont2 k hk _ (.var Γ.length, ()) (.var (Γ.length + 1), ())
          (CtxExtends.pushNormal _ _)
          ⟨hvt.1, trivial⟩ ⟨hvt.2.1, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op3_2res target (.subb (target.widenWidth n)) (legalArg target a).1
          (legalArg target b).1 (legalArg target c).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hc' hlegW rfl ?_
        let Γ1 := pushNormal [.bits (target.widenWidth n), .bool] Γ
        have hvt := ArgsNormal_varsTup_levels target [.bits (target.widenWidth n), .bool] Γ
          (by simp [LegalTarget.isLegalSig, LegalTarget.isLegalTy, hw])
        refine emitMaskToN_isLegal target hw (.var Γ.length) hvt.1 fun Γ2 d hExt2 hd => ?_
        exact hcont2 k hk Γ2 (d, ()) (.var (Γ.length + 1), ())
          ((CtxExtends.pushNormal _ _).trans hExt2)
          ⟨hd, trivial⟩ ⟨hvt.2.1.mono hExt2, trivial⟩
  | umulw n =>
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_pair hargs).1).1
    have hb := (legalArg_isNormal hc hsupp (ArgRel_pair hargs).2).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]
      exact hcont2 k hk Γ (.imm _, ()) (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
        ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op2_2res target (.umulw (target.widenWidth n)) (legalArg target a).1
          (legalArg target b).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hlegW hlegW ?_
        have hvt :=
          ArgsNormal_varsTup_levels target
          [.bits (target.widenWidth n), .bits (target.widenWidth n)] Γ
          (by simp [LegalTarget.isLegalSig, hlegW])
        exact hcont2 k hk _ (.var Γ.length, ()) (.var (Γ.length + 1), ())
          (CtxExtends.pushNormal _ _)
          ⟨hvt.1, trivial⟩ ⟨hvt.2.1, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op2_2res target (.umulw (target.widenWidth n)) (legalArg target a).1
          (legalArg target b).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hlegW hlegW ?_
        let Γ1 := pushNormal [.bits (target.widenWidth n), .bits (target.widenWidth n)] Γ
        have h1 : CtxExtends Γ Γ1 := CtxExtends.pushNormal _ _
        have hvt :=
          ArgsNormal_varsTup_levels target
          [.bits (target.widenWidth n), .bits (target.widenWidth n)] Γ
          (by simp [LegalTarget.isLegalSig, hlegW])
        refine emitMaskToN_isLegal target hw (.var Γ.length) hvt.1 fun Γ2 lo hExt2 hlo => ?_
        refine isLegal_let_op2_normal target (.lshr (.bits (target.widenWidth n))) (.var Γ.length)
          (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (hvt.1.mono hExt2) hlegW hlegW ?_
        let Γ3 := (.bits (target.widenWidth n), VarKind.normal) :: Γ2
        refine isLegal_let_op2_normal target (.shl (.bits (target.widenWidth n)))
          (.var (Γ.length + 1)) (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (hvt.2.1.mono (hExt2.trans (CtxExtends.cons _ _)))
            hlegW hlegW ?_
        let Γ4 := (.bits (target.widenWidth n), VarKind.normal) :: Γ3
        refine isLegal_let_op2_normal target (.or (.bits (target.widenWidth n))) (.var Γ2.length)
          (.var Γ3.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw])
            ((ArgNormal.head target Γ2 hlegW).mono (CtxExtends.cons _ _))
          (ArgNormal.head target Γ3 hlegW) hlegW ?_
        let Γ5 := (.bits (target.widenWidth n), VarKind.normal) :: Γ4
        have h15 : CtxExtends Γ Γ5 :=
          h1.trans
          (hExt2.trans
          ((CtxExtends.cons _ _).trans ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _))))
        refine emitMaskToN_isLegal target hw (.var Γ4.length) (ArgNormal.head target Γ4 hlegW)
          fun Γ6 hi hExt6 hhi => ?_
        have hlo' :=
          hlo.mono
          ((CtxExtends.cons _ _).trans
          ((CtxExtends.cons _ _).trans ((CtxExtends.cons _ _).trans hExt6)))
        exact hcont2 k hk Γ6 (lo, ()) (hi, ()) (h15.trans hExt6) ⟨hlo', trivial⟩ ⟨hhi, trivial⟩
  | smulw n =>
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_pair hargs).1).1
    have hb := (legalArg_isNormal hc hsupp (ArgRel_pair hargs).2).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]
      exact hcont2 k hk Γ (.imm _, ()) (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
        ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op2_2res target (.smulw (target.widenWidth n)) (legalArg target a).1
          (legalArg target b).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hlegW hlegW ?_
        have hvt :=
          ArgsNormal_varsTup_levels target
          [.bits (target.widenWidth n), .bits (target.widenWidth n)] Γ
          (by simp [LegalTarget.isLegalSig, hlegW])
        exact hcont2 k hk _ (.var Γ.length, ()) (.var (Γ.length + 1), ())
          (CtxExtends.pushNormal _ _)
          ⟨hvt.1, trivial⟩ ⟨hvt.2.1, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitSextToW_isLegal target hw (legalArg target a).1 ha fun Γa sa hExta hsa => ?_
        refine emitSextToW_isLegal target hw ((legalArg target b).1) (hb.mono hExta) fun Γb sb hExtb
          hsb => ?_
        have hab := hExta.trans hExtb
        refine isLegal_let_op2_2res target (.smulw (target.widenWidth n)) sa sb _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) (hsa.mono hExtb) hsb hlegW hlegW ?_
        let Γ1 := pushNormal [.bits (target.widenWidth n), .bits (target.widenWidth n)] Γb
        have h1 : CtxExtends Γ Γ1 := hab.trans (CtxExtends.pushNormal _ _)
        have hvt :=
          ArgsNormal_varsTup_levels target
          [.bits (target.widenWidth n), .bits (target.widenWidth n)] Γb
          (by simp [LegalTarget.isLegalSig, hlegW])
        refine emitMaskToN_isLegal target hw (.var Γb.length) hvt.1 fun Γ2 lo hExt2 hlo => ?_
        refine isLegal_let_op2_normal target (.lshr (.bits (target.widenWidth n))) (.var Γb.length)
          (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (hvt.1.mono hExt2) hlegW hlegW ?_
        let Γ3 := (.bits (target.widenWidth n), VarKind.normal) :: Γ2
        refine isLegal_let_op2_normal target (.shl (.bits (target.widenWidth n)))
          (.var (Γb.length + 1)) (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (hvt.2.1.mono (hExt2.trans (CtxExtends.cons _ _)))
            hlegW hlegW ?_
        let Γ4 := (.bits (target.widenWidth n), VarKind.normal) :: Γ3
        refine isLegal_let_op2_normal target (.or (.bits (target.widenWidth n))) (.var Γ2.length)
          (.var Γ3.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw])
            ((ArgNormal.head target Γ2 hlegW).mono (CtxExtends.cons _ _))
          (ArgNormal.head target Γ3 hlegW) hlegW ?_
        let Γ5 := (.bits (target.widenWidth n), VarKind.normal) :: Γ4
        have h15 : CtxExtends Γ Γ5 :=
          h1.trans
          (hExt2.trans
          ((CtxExtends.cons _ _).trans ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _))))
        refine emitMaskToN_isLegal target hw (.var Γ4.length) (ArgNormal.head target Γ4 hlegW)
          fun Γ6 hi hExt6 hhi => ?_
        have hlo' :=
          hlo.mono
          ((CtxExtends.cons _ _).trans
          ((CtxExtends.cons _ _).trans ((CtxExtends.cons _ _).trans hExt6)))
        exact hcont2 k hk Γ6 (lo, ()) (hi, ()) (h15.trans hExt6) ⟨hlo', trivial⟩ ⟨hhi, trivial⟩
  | udiv _ | sdiv _ | urem _ | srem _ | udiv0 _ | sdiv0 _ | mkpair _ _ | unpair _ _
  | bitcast _ _ _ | shufd _ _ | shufb _ | alignr _ _ | blendw _ _ | sha256rnds2
  | sha256msg1 | sha256msg2 | fadd _ | fsub _ | fmul _ | fdiv _ | ffma _ | fsqrt _
  | fneg _ | fabs _ | fcmp _ _ _ _ | fptoui _ _ | fptosi _ _ | uitofp _ _
  | sitofp _ _ | fcvt _ _ => exact absurd (by rfl) hpart

end LegalIsLegal

end LeanQbe.T
