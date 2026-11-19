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

theorem ArgRel_single {target : LegalTarget} {G : Ctx K (LVar target K)} {t : Ty}
    {x : Tup (Arg K) [t]} {y : Tup (Arg (LVar target K)) [t]}
    (h : TRel (ArgRel G) x y) : ArgRel G t x.1 y.1 := by
  rcases x with ⟨a₁, ⟨⟩⟩; rcases y with ⟨a₂, ⟨⟩⟩; cases h with | cons h1 _ => exact h1

theorem ArgRel_pair {target : LegalTarget} {G : Ctx K (LVar target K)} {t₁ t₂ : Ty}
    {x : Tup (Arg K) [t₁, t₂]} {y : Tup (Arg (LVar target K)) [t₁, t₂]}
    (h : TRel (ArgRel G) x y) : ArgRel G t₁ x.1 y.1 ∧ ArgRel G t₂ x.2.1 y.2.1 := by
  rcases x with ⟨a₁, b₁, ⟨⟩⟩; rcases y with ⟨a₂, b₂, ⟨⟩⟩
  cases h with | cons h1 h2 => cases h2 with | cons h3 _ => exact ⟨h1, h3⟩

theorem ArgRel_triple {target : LegalTarget} {G : Ctx K (LVar target K)} {t₁ t₂ t₃ : Ty}
    {x : Tup (Arg K) [t₁, t₂, t₃]} {y : Tup (Arg (LVar target K)) [t₁, t₂, t₃]}
    (h : TRel (ArgRel G) x y) :
    ArgRel G t₁ x.1 y.1 ∧ ArgRel G t₂ x.2.1 y.2.1 ∧ ArgRel G t₃ x.2.2.1 y.2.2.1 := by
  rcases x with ⟨a₁, b₁, c₁, ⟨⟩⟩; rcases y with ⟨a₂, b₂, c₂, ⟨⟩⟩
  cases h with | cons h1 h2 => cases h2 with | cons h3 h4 => cases h4 with | cons h5 _ =>
    exact ⟨h1, h3, h5⟩

theorem not_hasFloat_pair {a b : Ty} (h : (!(Ty.pair a b).hasFloat) = true) :
    (!a.hasFloat) = true ∧ (!b.hasFloat) = true := by
  cases ha : a.hasFloat <;> cases hb : b.hasFloat <;> simp [Ty.hasFloat, ha, hb] at h ⊢

private theorem dite_pred {α : Type} {p : Prop} [Decidable p] {t : p → α} {e : ¬p → α}
    {P : α → Prop} (ht : ∀ h, P (t h)) (he : ∀ h, P (e h)) : P (dite p t e) := by
  by_cases h : p
  · rw [dite_eq_left h]; exact ht h
  · rw [dite_eq_right h]; exact he h

/-- Lift a single-result `legalOp_isLegal` continuation to an `ArgsNormal` obligation. -/
theorem legalOp_isLegal_cont1 (target : LegalTarget) {Γ : List (Ty × VarKind)} {Δ : List (List Ty)}
    {rs : List Ty} (nv₁ : Nat) {u : Ty} (k' : Tup (LVar target K) [u] → Expr K KL rs)
    (hk' : IsLegalCont target Γ Δ
      (fun Γ' res =>
      ∀ t v₂, (∃ v₁, ⟨t, v₁, v₂⟩ ∈ Tup.zip (Tup.levels [u] nv₁) res) →
      ArgsNormal target Γ' v₂) k') :
    IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) (fun r => k' (r, ())) := by
  intro Γ' r hExt hr
  exact hk' Γ' (r, ()) hExt fun t v₂ ⟨v₁, hm⟩ => by
    simp only [Tup.levels_cons, Tup.levels_nil, Tup.zip] at hm
    rcases List.mem_cons.1 hm with ⟨rfl, rfl, rfl⟩ | hm'
    · exact hr
    · cases hm'

/-- Lift a two-result `legalOp_isLegal` continuation to `ArgsNormal` obligations. -/
theorem legalOp_isLegal_cont2 (target : LegalTarget) {Γ : List (Ty × VarKind)} {Δ : List (List Ty)}
    {rs : List Ty} (nv₁ : Nat) {u₁ u₂ : Ty} (k' : Tup (LVar target K) [u₁, u₂] → Expr K KL rs)
    (hk' : IsLegalCont target Γ Δ
      (fun Γ' res =>
      ∀ t v₂, (∃ v₁, ⟨t, v₁, v₂⟩ ∈ Tup.zip (Tup.levels [u₁, u₂] nv₁) res) →
      ArgsNormal target Γ' v₂) k') :
    ∀ (Γ' : List (Ty × VarKind)) (r₁ : LVar target K u₁) (r₂ : LVar target K u₂),
      CtxExtends Γ Γ' → ArgsNormal target Γ' r₁ → ArgsNormal target Γ' r₂ →
      (toTFlat (k' (r₁, r₂, ())) Γ'.length Δ.length).isLegal target Γ' Δ = true := by
  intro Γ' r₁ r₂ hExt hr₁ hr₂
  exact hk' Γ' (r₁, r₂, ()) hExt fun t v₂ ⟨v₁, hm⟩ => by
    simp only [Tup.levels_cons, Tup.levels_nil, Tup.zip] at hm
    rcases List.mem_cons.1 hm with ⟨rfl, rfl, rfl⟩ | hm'
    · exact hr₁
    · rcases List.mem_cons.1 hm' with ⟨rfl, rfl, rfl⟩ | hm''
      · exact hr₂
      · cases hm''

theorem legalOp_isLegal_part2 (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) {Γ : List (Ty × VarKind)} {LG : Ctx K (LVar target K)}
    (hc : CLegal target Γ LG) {ts : List Ty} {op₁ : Op K ts} {op₂ : Op (LVar target K) ts}
    (hop : OpRel LG op₁ op₂) (hsupp : target.supportsOpCode op₁.code = true)
    (hpart : isLegalOpPart2 op₁.code = true) (nv₁ : Nat := 0)
    {k : Tup (LVar target K) ts → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ
      (fun Γ' res =>
      ∀ t v₂, (∃ v₁, ⟨t, v₁, v₂⟩ ∈ Tup.zip (Tup.levels ts nv₁) res) → ArgsNormal target Γ' v₂) k) :
    (toTFlat (legalOp target op₂ k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hcont1 := @legalOp_isLegal_cont1 target Γ Δ rs nv₁
  have hcont2 := @legalOp_isLegal_cont2 target Γ Δ rs nv₁
  have h64 := valid_mem64 hv
  rcases hop with @⟨_, _, code, args₁, args₂, hargs⟩
  dsimp only [Op.code] at hpart
  dsimp only [Op.code, LegalTarget.supportsOpCode] at hsupp
  cases code with
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
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp, hpa, hpb]
    by_cases hn0 : (n == 0) = true
    · simp [hn0]
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      refine isLegal_let_op2_normal target (.udiv (target.widenWidth n)) a' b' _ rfl
        (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hlegW ?_
      exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _)
        ⟨ArgNormal.head target Γ hlegW, trivial⟩
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
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp, hpa, hpb]
    by_cases hn0 : (n == 0) = true
    · simp [hn0]
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op2_normal target (.sdiv (target.widenWidth n)) a' b' _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hlegW ?_
        exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _)
          ⟨ArgNormal.head target Γ hlegW, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitSextToW_isLegal target hw a' ha fun Γ1 sa hExt1 hsa => ?_
        refine emitSextToW_isLegal target hw b' (hb.mono hExt1) fun Γ2 sb hExt2 hsb => ?_
        refine isLegal_let_op2_normal target (.sdiv (target.widenWidth n)) sa sb _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) (hsa.mono hExt2) hsb hlegW ?_
        let Γ3 := (.bits (target.widenWidth n), VarKind.normal) :: Γ2
        refine emitMaskToN_isLegal target hw (.var Γ2.length) (ArgNormal.head target Γ2 hlegW)
          fun Γ4 rm hExt4 hrm => ?_
        exact hcont1 k hk Γ4 (rm, ())
          (((hExt1.trans hExt2).trans (CtxExtends.cons _ _)).trans hExt4) ⟨hrm, trivial⟩
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
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp, hpa, hpb]
    by_cases hn0 : (n == 0) = true
    · simp [hn0]
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      refine isLegal_let_op2_normal target (.urem (target.widenWidth n)) a' b' _ rfl
        (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hlegW ?_
      exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _)
        ⟨ArgNormal.head target Γ hlegW, trivial⟩
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
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp, hpa, hpb]
    by_cases hn0 : (n == 0) = true
    · simp [hn0]
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op2_normal target (.srem (target.widenWidth n)) a' b' _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hlegW ?_
        exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _)
          ⟨ArgNormal.head target Γ hlegW, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitSextToW_isLegal target hw a' ha fun Γ1 sa hExt1 hsa => ?_
        refine emitSextToW_isLegal target hw b' (hb.mono hExt1) fun Γ2 sb hExt2 hsb => ?_
        refine isLegal_let_op2_normal target (.srem (target.widenWidth n)) sa sb _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) (hsa.mono hExt2) hsb hlegW ?_
        let Γ3 := (.bits (target.widenWidth n), VarKind.normal) :: Γ2
        refine emitMaskToN_isLegal target hw (.var Γ2.length) (ArgNormal.head target Γ2 hlegW)
          fun Γ4 rm hExt4 hrm => ?_
        exact hcont1 k hk Γ4 (rm, ())
          (((hExt1.trans hExt2).trans (CtxExtends.cons _ _)).trans hExt4) ⟨hrm, trivial⟩
  | udiv0 n =>
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_pair hargs).1).1
    have hb := (legalArg_isNormal hc hsupp (ArgRel_pair hargs).2).1
    have hw := widenWidth_mem_of_supports hsupp
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte];
        exact hcont1 k hk Γ (.imm _, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      refine isLegal_let_op2_normal target (.udiv0 (target.widenWidth n)) (legalArg target a).1
        (legalArg target b).1 _ rfl
        (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hlegW ?_
      exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _)
        ⟨ArgNormal.head target Γ hlegW, trivial⟩
  | sdiv0 n =>
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    have ha := (legalArg_isNormal hc hsupp (ArgRel_pair hargs).1).1
    have hb := (legalArg_isNormal hc hsupp (ArgRel_pair hargs).2).1
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
        refine isLegal_let_op2_normal target (.sdiv0 (target.widenWidth n)) (legalArg target a).1
          (legalArg target b).1 _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb hlegW ?_
        exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _)
          ⟨ArgNormal.head target Γ hlegW, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitSextToW_isLegal target hw (legalArg target a).1 ha fun Γ1 sa hExt1 hsa => ?_
        refine emitSextToW_isLegal target hw (legalArg target b).1 (hb.mono hExt1) fun Γ2 sb hExt2
          hsb => ?_
        refine isLegal_let_op2_normal target (.sdiv0 (target.widenWidth n)) sa sb _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) (hsa.mono hExt2) hsb hlegW ?_
        let Γ3 := (.bits (target.widenWidth n), VarKind.normal) :: Γ2
        refine emitMaskToN_isLegal target hw (.var Γ2.length) (ArgNormal.head target Γ2 hlegW)
          fun Γ4 rm hExt4 hrm => ?_
        exact hcont1 k hk Γ4 (rm, ())
          (((hExt1.trans hExt2).trans (CtxExtends.cons _ _)).trans hExt4) ⟨hrm, trivial⟩
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
      refine packFromLegal_isLegal target ha_pb b hp'.2.2 _ (hlb.mono hExt1) fun Γ2 pb hExt2 hpb =>
        ?_
      have hpa' := hpa.mono hExt2
      rw [toTFlat_let]; dsimp only [op2, Tup.levels_cons, Tup.levels_nil];
        rw [idxArgs_pair, TFlat.isLegal_let_mkpair]
      have hlpair : target.hasLegalLeaves (.pair a b) = true := by
        simp only [LegalTarget.hasLegalLeaves, Bool.and_eq_true]; exact hp'.2
      have hlegP : target.isLegalTy (.pair a b) = true := hp
      simp only [ha_pb, hlpair, hlegP, ↓reduceIte, Bool.true_and]
      have hchkA : (match idxArg Γ2.length pa with
          | .var idx =>
              checkVarKind Γ2 a
              (fun vk => (vk == .normal && target.isLegalTy a) || vk == .packedBridge) idx
          | .imm _ => target.isLegalTy a) = true := by
        cases pa with | imm _ => exact hpa' | var _ => exact hpa'.checkVarKind
      have hchkB : (match idxArg Γ2.length pb with
          | .var idx =>
              checkVarKind Γ2 b
              (fun vk => (vk == .normal && target.isLegalTy b) || vk == .packedBridge) idx
          | .imm _ => target.isLegalTy b) = true := by
        cases pb with | imm _ => exact hpb | var _ => exact hpb.checkVarKind
      cases pa <;> cases pb <;> dsimp only [idxArg] at hchkA hchkB ⊢ <;>
        simp only [hchkA, hchkB, Bool.true_and]
      all_goals
        let Γ3 := (.pair a b, VarKind.normal) :: Γ2
        have hlen3 : Γ3.length = Γ2.length + [a.pair b].length := by simp [Γ3]
        rw [← hlen3]
        exact hcont1 k hk Γ3 (tupToPacked hp (.var Γ2.length, ()))
          ((hExt1.trans hExt2).trans (CtxExtends.cons _ _))
          (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ2 hlegP, trivial⟩)
    · next hnp =>
      have hf := Bool.eq_false_iff.mpr hnp
      exact hcont1 k hk Γ (tupToSplit hf (tupAppend (legalArg target va) (legalArg target vb)))
        (CtxExtends.refl Γ)
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
        refine unpackToLegal_isLegal target hv ha_pb a hp'.2.1 (.var Γ.length) hUa fun Γ2 la hExt12
          hla => ?_
        refine unpackToLegal_isLegal target hv ha_pb b hp'.2.2 (.var (Γ.length + 1))
          (hUb.mono hExt12)
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
          packLeavesToLegal target u fu fun res =>
            k (res, ())) Γ.length Δ.length).isLegal target Γ Δ = true := by
        refine splitLegalToLeaves_isLegal target t (legalArg target a) ha fun Γ1 fx hExt1 hfx => ?_
        refine packLeavesToWords64_isLegal target hv t hsupp.1 fx hfx fun Γ2 words hExt2 hwords =>
          ?_
        refine unpackWords64ToLeaves_isLegal target hv words hwords 0 u hsupp.2 fun Γ3 fu hExt3
          hfu => ?_
        exact packLeavesToLegal_isLegal target u fu hfu fun Γ4 res hExt4 hres =>
          hcont1 k hk Γ4 res (((hExt1.trans hExt2).trans hExt3).trans hExt4) hres
      refine dite_pred (P := fun e => (toTFlat e Γ.length Δ.length).isLegal target Γ Δ = true)
        (fun ht => ?_) (fun _ => hfallback)
      refine dite_pred (P := fun e => (toTFlat e Γ.length Δ.length).isLegal target Γ Δ = true)
        (fun hu => ?_) (fun _ => hfallback)
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
      have hx' :
        ArgNormal target Γ t (cast (by rw [hlt]) (legalArg target a) : Tup (Arg K) [t]).1 :=
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
    exact legalShufb_isLegal target hv hsupp.2 t hsupp.1 (legalArg target a) (legalArg target m) ha
      hm (hcont1 k hk)
  | alignr t imm =>
    rcases args₂ with ⟨hi, lo, ⟨⟩⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsupp
    have hhi := legalArg_isNormal hc hsupp.1 (ArgRel_pair hargs).1
    have hlo := legalArg_isNormal hc hsupp.1 (ArgRel_pair hargs).2
    simp only [legalOp]
    exact legalAlignr_isLegal target hv hsupp.2 imm t hsupp.1 (legalArg target hi)
      (legalArg target lo) hhi hlo (hcont1 k hk)
  | blendw t imm =>
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsupp
    have ha := legalArg_isNormal hc hsupp.1 (ArgRel_pair hargs).1
    have hb := legalArg_isNormal hc hsupp.1 (ArgRel_pair hargs).2
    simp only [legalOp]
    exact legalBlendw_isLegal target hv hsupp.2 imm t hsupp.1 (legalArg target a)
      (legalArg target b) ha hb (hcont1 k hk)
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
        packLeavesToLegal target v4i32 fres fun res =>
          k (res, ())) Γ.length Δ.length).isLegal target Γ Δ = true := by
      refine splitLegalToLeaves_isLegal target v4i32 (legalArg target cdgh) hc' fun Γ1 fc h1 hfc =>
        ?_
      refine splitLegalToLeaves_isLegal target v4i32 (legalArg target abef) (ha.mono h1) fun Γ2 fa
        h2 hfa => ?_
      have h12 := h1.trans h2
      refine splitLegalToLeaves_isLegal target v4i32 (legalArg target wk) (hw.mono h12) fun Γ3 fw h3
        hfw => ?_
      have h13 := h12.trans h3
      refine packLeavesToWords64_isLegal target hv v4i32 hsupp.1 fc (hfc.mono (h2.trans h3)) fun Γ4
        wc h4 hwc => ?_
      refine packLeavesToWords64_isLegal target hv v4i32 hsupp.1 fa ((hfa.mono h3).mono h4) fun Γ5
        wa h5 hwa => ?_
      have h45 := h4.trans h5
      refine packLeavesToWords64_isLegal target hv v4i32 hsupp.1 fw (hfw.mono h45) fun Γ6 ww h6
        hww => ?_
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
      refine scalarSha256rnds2_isLegal target hsupp.2 cd0 cd1 cd2 cd3 ab0 ab1 ab2 ab3 wk0 wk1 wk2
        wk3
        (hcd0.mono h89) (hcd1.mono h89) (hcd2.mono h89) (hcd3.mono h89)
        (hab0.mono h9) (hab1.mono h9) (hab2.mono h9) (hab3.mono h9) hwk0 hwk1
        fun Γ10 r0 r1 r2 r3 h10 hr0 hr1 hr2 hr3 => ?_
      refine dwords4ToWords2_isLegal target hsupp.2 h64 r0 r1 r2 r3 hr0 hr1 hr2 hr3 fun Γ11 w0 w1
        h11 hw0 hw1 => ?_
      refine unpackWords64ToLeaves_isLegal target hv [w0, w1]
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx;
          rcases hx with rfl | rfl <;> assumption)
        0 v4i32 hsupp.1 fun Γ12 fres h12' hfres => ?_
      exact packLeavesToLegal_isLegal target v4i32 fres hfres fun Γ13 res h13' hres =>
        hcont1 k hk Γ13 res ((((h16.trans h79).trans h10).trans h11).trans (h12'.trans h13')) hres
    simp only [legalOp]
    split
    · next hp =>
      have hkp : target.keepsPacked v4i32 = true := (Bool.and_eq_true _ _).mp hp |>.1
      have hsup : target.vecIntOpSupported .sha256rnds2 v4i32 false = true :=
        (Bool.and_eq_true _ _).mp hp |>.2
      have hl : target.legalTys v4i32 = [v4i32] := by simp [LegalTarget.legalTys, hkp]
      refine isLegal_let_op3_normal target .sha256rnds2 _ _ _ _ rfl
        (by simp [LegalTarget.isLegalOp, hkp, hsup])
        (ArgsNormal_cast_eq _ hl hc').1 (ArgsNormal_cast_eq _ hl ha).1
        (ArgsNormal_cast_eq _ hl hw).1 hkp ?_
      exact hcont1 k hk _ _ (CtxExtends.cons _ _)
        (ArgsNormal_cast_eq _ hl.symm ⟨ArgNormal.head target Γ hkp, trivial⟩)
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
        packLeavesToLegal target v4i32 fres fun res =>
          k (res, ())) Γ.length Δ.length).isLegal target Γ Δ = true := by
      refine splitLegalToLeaves_isLegal target v4i32 (legalArg target w0123) ha fun Γ1 fa h1 hfa =>
        ?_
      refine splitLegalToLeaves_isLegal target v4i32 (legalArg target w4) (hb.mono h1) fun Γ2 fb h2
        hfb => ?_
      have h12 := h1.trans h2
      refine packLeavesToWords64_isLegal target hv v4i32 hsupp.1 fa (hfa.mono h2) fun Γ3 wa h3
        hwa => ?_
      refine packLeavesToWords64_isLegal target hv v4i32 hsupp.1 fb (hfb.mono h3) fun Γ4 wb h4
        hwb => ?_
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
      refine dwords4ToWords2_isLegal target hsupp.2 h64 r0 r1 r2 r3 hr0 hr1 hr2 hr3 fun Γ8 w0 w1 h8
        hw0 hw1 => ?_
      refine unpackWords64ToLeaves_isLegal target hv [w0, w1]
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx;
          rcases hx with rfl | rfl <;> assumption)
        0 v4i32 hsupp.1 fun Γ9 fres h9 hfres => ?_
      exact packLeavesToLegal_isLegal target v4i32 fres hfres fun Γ10 res h10 hres =>
        hcont1 k hk Γ10 res ((((h14.trans (h5.trans h6)).trans h7).trans h8).trans (h9.trans h10))
          hres
    simp only [legalOp]
    split
    · next hp =>
      have hkp : target.keepsPacked v4i32 = true := (Bool.and_eq_true _ _).mp hp |>.1
      have hsup : target.vecIntOpSupported .sha256msg1 v4i32 false = true :=
        (Bool.and_eq_true _ _).mp hp |>.2
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
        packLeavesToLegal target v4i32 fres fun res =>
          k (res, ())) Γ.length Δ.length).isLegal target Γ Δ = true := by
      refine splitLegalToLeaves_isLegal target v4i32 (legalArg target sums) ha fun Γ1 fa h1 hfa =>
        ?_
      refine splitLegalToLeaves_isLegal target v4i32 (legalArg target w) (hb.mono h1) fun Γ2 fb h2
        hfb => ?_
      have h12 := h1.trans h2
      refine packLeavesToWords64_isLegal target hv v4i32 hsupp.1 fa (hfa.mono h2) fun Γ3 wa h3
        hwa => ?_
      refine packLeavesToWords64_isLegal target hv v4i32 hsupp.1 fb (hfb.mono h3) fun Γ4 wb h4
        hwb => ?_
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
      refine dwords4ToWords2_isLegal target hsupp.2 h64 r0 r1 r2 r3 hr0 hr1 hr2 hr3 fun Γ8 wr0 wr1
        h8 hwr0 hwr1 => ?_
      refine unpackWords64ToLeaves_isLegal target hv [wr0, wr1]
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx;
          rcases hx with rfl | rfl <;> assumption)
        0 v4i32 hsupp.1 fun Γ9 fres h9 hfres => ?_
      exact packLeavesToLegal_isLegal target v4i32 fres hfres fun Γ10 res h10 hres =>
        hcont1 k hk Γ10 res ((((h14.trans (h5.trans h6)).trans h7).trans h8).trans (h9.trans h10))
          hres
    simp only [legalOp]
    split
    · next hp =>
      have hkp : target.keepsPacked v4i32 = true := (Bool.and_eq_true _ _).mp hp |>.1
      have hsup : target.vecIntOpSupported .sha256msg2 v4i32 false = true :=
        (Bool.and_eq_true _ _).mp hp |>.2
      have hl : target.legalTys v4i32 = [v4i32] := by simp [LegalTarget.legalTys, hkp]
      refine isLegal_let_op2_normal target .sha256msg2 _ _ _ rfl
        (by simp [LegalTarget.isLegalOp, hkp, hsup])
        (ArgsNormal_cast_eq _ hl ha).1 (ArgsNormal_cast_eq _ hl hb).1 hkp ?_
      exact hcont1 k hk _ _ (CtxExtends.cons _ _)
        (ArgsNormal_cast_eq _ hl.symm ⟨ArgNormal.head target Γ hkp, trivial⟩)
    · exact hsc
  | fadd t | fsub t | fmul t | fdiv t =>
    rcases args₂ with ⟨a, b, ⟨⟩⟩
    have ha := legalArg_isNormal hc hsupp (ArgRel_pair hargs).1
    have hb := legalArg_isNormal hc hsupp (ArgRel_pair hargs).2
    simp only [legalOp]
    by_cases hft : t.isFloatTree = true
    · simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine legalBinTree_isLegal target
        (fun u => target.supportsTy u = true ∧ u.isFloatTree = true)
        (fun a b h => by
          simp only [LegalTarget.supportsTy, Ty.isFloatTree, Bool.and_eq_true] at h
          exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩)
        _ _ (fun _ => rfl)
        (fun a b unif _ hp hvs => by simp [LegalTarget.isLegalOp, hp, hvs])
        _ _ _ _
        (fun hP => by simp [Ty.isFloatTree] at hP)
        (fun _ hP => by simp [Ty.isFloatTree] at hP)
        (fun f hP Γ' x y cont hx hy hc' => by
          have hf : f ∈ target.floatFmts :=
            (by simpa [LegalTarget.supportsTy] using hP.1 : f ∈ target.floatFmts ∧ f.width ≤ 64).1
          have hlegF : target.isLegalTy (.float f) = true := by
            simpa [LegalTarget.isLegalTy] using hf
          refine isLegal_let_op2_normal target _ x y _ rfl (by simp [LegalTarget.isLegalOp, hf]) hx
            hy hlegF ?_
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
      refine legalTernaryTree_isLegal target
        (fun u => target.supportsTy u = true ∧ u.isFloatTree = true)
        (fun a b h => by
          simp only [LegalTarget.supportsTy, Ty.isFloatTree, Bool.and_eq_true] at h
          exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩)
        _ _ (fun _ => rfl)
        (fun a b _ hp hvs => by simp [LegalTarget.isLegalOp, hp, hvs])
        _ _ _
        (fun hP => by simp [Ty.isFloatTree] at hP)
        (fun _ hP => by simp [Ty.isFloatTree] at hP)
        (fun f hP Γ' x y z cont hx hy hz hcont => by
          have hf : f ∈ target.floatFmts :=
            (by simpa [LegalTarget.supportsTy] using hP.1 : f ∈ target.floatFmts ∧ f.width ≤ 64).1
          have hlegF : target.isLegalTy (.float f) = true := by
            simpa [LegalTarget.isLegalTy] using hf
          refine isLegal_let_op3_normal target (.ffma (.float f)) x y z _ rfl
            (by simp [LegalTarget.isLegalOp, hf]) hx hy hz hlegF ?_
          exact hcont _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' hlegF))
        t ⟨hsupp, hft⟩ (legalArg target a) (legalArg target b) (legalArg target c) ha hb hc'
          (hcont1 k hk)
    · simp [hft, toTFlat_hlt]
  | fsqrt t | fneg t | fabs t =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    have ha := legalArg_isNormal hc hsupp (ArgRel_single hargs)
    simp only [legalOp]
    by_cases hft : t.isFloatTree = true
    · simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine legalUnaryTree_isLegal target
        (fun u => target.supportsTy u = true ∧ u.isFloatTree = true)
        (fun a b h => by
          simp only [LegalTarget.supportsTy, Ty.isFloatTree, Bool.and_eq_true] at h
          exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩)
        _ _ (fun _ => rfl)
        (fun a b _ hp hvs => by simp [LegalTarget.isLegalOp, hp, hvs])
        _ _ _
        (fun hP => by simp [Ty.isFloatTree] at hP)
        (fun _ hP => by simp [Ty.isFloatTree] at hP)
        (fun f hP Γ' x cont hx hcont => by
          have hf : f ∈ target.floatFmts :=
            (by simpa [LegalTarget.supportsTy] using hP.1 : f ∈ target.floatFmts ∧ f.width ≤ 64).1
          have hlegF : target.isLegalTy (.float f) = true := by
            simpa [LegalTarget.isLegalTy] using hf
          refine isLegal_let_op1_normal target _ x _ rfl (by simp [LegalTarget.isLegalOp, hf]) hx
            hlegF ?_
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
      exact legalFCmpTree_isLegal target o t hsupp (legalArg target a) (legalArg target b) ha hb
        (hcont1 k hk)
    · simp [hft, toTFlat_hlt]
  | fptoui f n =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    simp only [Bool.and_eq_true] at hsupp
    have hf : f ∈ target.floatFmts :=
      (by simpa [LegalTarget.supportsTy] using hsupp.1 : f ∈ target.floatFmts ∧ f.width ≤ 64).1
    have ha := (legalArg_isNormal hc hsupp.1 (ArgRel_single hargs)).1
    have hw := widenWidth_mem_of_supports hsupp.2
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]
      refine isLegal_let_op1_normal target (.fptoui f (target.widenWidth n)) (legalArg target a).1 _
        rfl
        (by simp [LegalTarget.isLegalOp, hf, hw]) ha hlegW ?_
      exact hcont1 k hk _ (.imm _, ()) (CtxExtends.cons _ _) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      refine isLegal_let_op1_normal target (.fptoui f (target.widenWidth n)) (legalArg target a).1 _
        rfl
        (by simp [LegalTarget.isLegalOp, hf, hw]) ha hlegW ?_
      exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _)
        ⟨ArgNormal.head target Γ hlegW, trivial⟩
  | fptosi f n =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    simp only [Bool.and_eq_true] at hsupp
    have hf : f ∈ target.floatFmts :=
      (by simpa [LegalTarget.supportsTy] using hsupp.1 : f ∈ target.floatFmts ∧ f.width ≤ 64).1
    rcases hpa : legalArg target a with ⟨a', ⟨⟩⟩
    have ha' := legalArg_isNormal hc hsupp.1 (ArgRel_single hargs)
    dsimp only at ha'; rw [hpa] at ha'
    have ha := ha'.1
    have hw := widenWidth_mem_of_supports hsupp.2
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalOp, hpa]
    by_cases hn0 : (n == 0) = true
    · simp [hn0]
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op1_normal target (.fptosi f (target.widenWidth n)) a' _ rfl
          (by simp [LegalTarget.isLegalOp, hf, hw]) ha hlegW ?_
        exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _)
          ⟨ArgNormal.head target Γ hlegW, trivial⟩
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op1_normal target (.fptosi f (target.widenWidth n)) a' _ rfl
          (by simp [LegalTarget.isLegalOp, hf, hw]) ha hlegW ?_
        let Γ1 := (.bits (target.widenWidth n), VarKind.normal) :: Γ
        refine emitMaskToN_isLegal target hw (.var Γ.length) (ArgNormal.head target Γ hlegW) fun Γ2
          rm hExt2 hrm => ?_
        exact hcont1 k hk Γ2 (rm, ()) ((CtxExtends.cons _ _).trans hExt2) ⟨hrm, trivial⟩
  | uitofp n f =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    simp only [Bool.and_eq_true] at hsupp
    have hf : f ∈ target.floatFmts :=
      (by simpa [LegalTarget.supportsTy] using hsupp.1 : f ∈ target.floatFmts ∧ f.width ≤ 64).1
    have ha := (legalArg_isNormal hc hsupp.2 (ArgRel_single hargs)).1
    have hw := widenWidth_mem_of_supports hsupp.2
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]
      refine isLegal_let_op1_normal target (.uitofp (target.widenWidth n) f) (.imm _) _ rfl
        (by simp [LegalTarget.isLegalOp, hw, hf]) hlegW hlegF ?_
      exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _)
        ⟨ArgNormal.head target Γ hlegF, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      refine isLegal_let_op1_normal target (.uitofp (target.widenWidth n) f) (legalArg target a).1 _
        rfl
        (by simp [LegalTarget.isLegalOp, hw, hf]) ha hlegF ?_
      exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _)
        ⟨ArgNormal.head target Γ hlegF, trivial⟩
  | sitofp n f =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    simp only [Bool.and_eq_true] at hsupp
    have hf : f ∈ target.floatFmts :=
      (by simpa [LegalTarget.supportsTy] using hsupp.1 : f ∈ target.floatFmts ∧ f.width ≤ 64).1
    have ha := (legalArg_isNormal hc hsupp.2 (ArgRel_single hargs)).1
    have hw := widenWidth_mem_of_supports hsupp.2
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
    simp only [legalOp]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]
      refine isLegal_let_op1_normal target (.sitofp (target.widenWidth n) f) (.imm _) _ rfl
        (by simp [LegalTarget.isLegalOp, hw, hf]) hlegW hlegF ?_
      exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _)
        ⟨ArgNormal.head target Γ hlegF, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      refine emitSextToW_isLegal target hw (legalArg target a).1 ha fun Γ1 sa hExt1 hsa => ?_
      refine isLegal_let_op1_normal target (.sitofp (target.widenWidth n) f) sa _ rfl
        (by simp [LegalTarget.isLegalOp, hw, hf]) hsa hlegF ?_
      exact hcont1 k hk _ (.var Γ1.length, ()) (hExt1.trans (CtxExtends.cons _ _))
        ⟨ArgNormal.head target Γ1 hlegF, trivial⟩
  | fcvt f g =>
    rcases args₂ with ⟨a, ⟨⟩⟩
    simp only [Bool.and_eq_true] at hsupp
    have hf : f ∈ target.floatFmts :=
      (by simpa [LegalTarget.supportsTy] using hsupp.1 : f ∈ target.floatFmts ∧ f.width ≤ 64).1
    have hg : g ∈ target.floatFmts :=
      (by simpa [LegalTarget.supportsTy] using hsupp.2 : g ∈ target.floatFmts ∧ g.width ≤ 64).1
    have ha := (legalArg_isNormal hc hsupp.1 (ArgRel_single hargs)).1
    have hlegG : target.isLegalTy (.float g) = true := by simpa [LegalTarget.isLegalTy] using hg
    simp only [legalOp]
    refine isLegal_let_op1_normal target (.fcvt f g) (legalArg target a).1 _ rfl
      (by simp [LegalTarget.isLegalOp, hf, hg]) ha hlegG ?_
    exact hcont1 k hk _ (.var Γ.length, ()) (CtxExtends.cons _ _)
      ⟨ArgNormal.head target Γ hlegG, trivial⟩

  | copy _ | add _ | sub _ | mul _ | neg _ | and _ | or _ | xor _ | not _
  | ternlog _ _ | shl _ | lshr _ | ashr _ | rotl _ | rotr _ | fshl _ | fshr _
  | bswap _ | clz _ | cls _ | rbit _ | ctz _ | popcnt _ | cmp _ _ _ _ | select _
  | blend _ _ _ | zext _ _ | sext _ _ | trunc _ _ | ofBool _ | addc _ | subb _
  | umulw _ | smulw _ => cases hpart

end LegalIsLegal

end LeanQbe.T
