module

public import LeanQbe.T.LegalOpWpLemmas1

/-!
# Legalization `legalOp_wp` div/pair/SIMD/float cases (Part 3b-ii)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

section LegalWp

/-- Partition predicate splitting `OpCode` cases across Part 1 (`copy`..`smulw`) and Part 2. -/
@[expose] def isLegalOpPart2 : {as rs : List Ty} → OpCode as rs → Bool
  | _, _, .udiv _ | _, _, .sdiv _ | _, _, .urem _ | _, _, .srem _
  | _, _, .udiv0 _ | _, _, .sdiv0 _ | _, _, .mkpair _ _ | _, _, .unpair _ _
  | _, _, .bitcast _ _ _ | _, _, .shufd _ _ | _, _, .shufb _
  | _, _, .alignr _ _ | _, _, .blendw _ _ | _, _, .sha256rnds2
  | _, _, .sha256msg1 | _, _, .sha256msg2 | _, _, .fadd _ | _, _, .fsub _
  | _, _, .fmul _ | _, _, .fdiv _ | _, _, .ffma _ | _, _, .fsqrt _
  | _, _, .fneg _ | _, _, .fabs _ | _, _, .fcmp _ _ _ _
  | _, _, .fptoui _ _ | _, _, .fptosi _ _ | _, _, .uitofp _ _
  | _, _, .sitofp _ _ | _, _, .fcvt _ _ => true
  | _, _, _ => false

theorem legalOp_wp_part2 (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx Val (LVar target Val)} (hG : CGoodWp target G)
    {ts : List Ty} {op₁ : Op Val ts} {op₂ : Op (LVar target Val) ts}
    (hop : OpRel G op₁ op₂) (hsupp : target.supportsOpCode op₁.code = true)
    (hpart : isLegalOpPart2 op₁.code = true)
    {P : Tup Val ts → Prop}
    {k : Tup (LVar target Val) ts → Expr Val Cont rs} {m : Mem 64}
    (hw : op₁.wp P)
    (hk : ∀ (r : Tup Val ts) (lr : Tup (LVar target Val) ts),
      TRel (fun t x lv => valsTup lv = encodeVal target t x) r lr →
      P r → wp Γ Q X (k lr) m) :
    wp Γ Q X (legalOp target op₂ k) m := by
  rcases hop with ⟨code, hargs⟩
  dsimp only at hsupp hw hpart
  cases code with
  | udiv n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_udiv] at hw
    rcases hw with ⟨hb0, hwP⟩
    have hn0 : n ≠ 0 := by intro h; subst h; exact hb0 (Subsingleton.elim _ _)
    dsimp only [legalOp]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩; rw [hpb] at hb_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    simp only [beq_iff_eq, hn0, ↓reduceIte]
    rw [wp_let, op2_wp_eq, OpCode.wp_udiv]
    have hp : 2 ^ n ≤ 2 ^ target.widenWidth n := Nat.pow_le_pow_right (by omega) hs.2.1
    have hbnz : b'.val ≠ 0 := by
      intro h; apply hb0; apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat h
      rw [hbeq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b₁.val.isLt hp)] at this
      exact this
    refine ⟨hbnz, hk _ _ (TRel.cons ?_ TRel.nil) hwP⟩
    change (a'.val / b'.val, ()) = (BitVec.setWidth (target.widenWidth n) (a₁.val / b₁.val), ())
    congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_udiv, haeq, hbeq, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      BitVec.toNat_setWidth, BitVec.toNat_udiv,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt hp),
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b₁.val.isLt hp),
      Nat.mod_eq_of_lt
        (Nat.lt_of_le_of_lt (Nat.div_le_self a₁.val.toNat b₁.val.toNat)
        (Nat.lt_of_lt_of_le a₁.val.isLt hp))]
  | sdiv n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_sdiv] at hw
    rcases hw with ⟨hsdef, hwP⟩
    have hb0 : b₁.val ≠ 0 := by
      dsimp only [sdivDefined] at hsdef
      simp only [Bool.and_eq_true, bne_iff_ne] at hsdef
      exact hsdef.1
    have hn0 : n ≠ 0 := by intro h; subst h; exact hb0 (Subsingleton.elim _ _)
    dsimp only [legalOp]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩; rw [hpb] at hb_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    simp only [beq_iff_eq, hn0, ↓reduceIte]
    split
    · next hnw =>
      rw [wp_let, op2_wp_eq, OpCode.wp_sdiv]; dsimp only
      refine ⟨op2_pred_self (P := fun {k} x y => sdivDefined x y = true) hnw haeq hbeq hsdef,
        hk _ _ (TRel.cons ?_ TRel.nil) hwP⟩
      change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
      congr 1; simp only [Arg.val_var]; exact op2_setWidth_self hnw haeq hbeq
    · next hnw =>
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      have hn_lt : n < target.widenWidth n := Nat.lt_of_le_of_ne hs.2.1 hnw
      refine emitSextToW_wp hn_pos hs.2.1 haeq fun sa hsa =>
        emitSextToW_wp hn_pos hs.2.1 hbeq fun sb hsb => ?_
      rw [wp_let, op2_wp_eq, OpCode.wp_sdiv]; dsimp only
      refine ⟨by rw [hsa, hsb]; exact opWp_sdivDefined_widened hn_pos hn_lt hb0, ?_⟩
      refine emitMaskToN_wp hs.2.1 rfl fun rm hrm => ?_
      simp only [Arg.val_var] at hrm
      refine hk _ _ (TRel.cons ?_ TRel.nil) hwP
      change (rm.val, ()) = (BitVec.setWidth (target.widenWidth n) (BitVec.sdiv a₁.val b₁.val), ())
      congr 1; rw [hrm, hsa, hsb, opWp_sdiv_widened hs.2.1 a₁.val b₁.val]
  | urem n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_urem] at hw
    rcases hw with ⟨hb0, hwP⟩
    have hn0 : n ≠ 0 := by intro h; subst h; exact hb0 (Subsingleton.elim _ _)
    dsimp only [legalOp]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩; rw [hpb] at hb_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    simp only [beq_iff_eq, hn0, ↓reduceIte]
    rw [wp_let, op2_wp_eq, OpCode.wp_urem]
    have hp : 2 ^ n ≤ 2 ^ target.widenWidth n := Nat.pow_le_pow_right (by omega) hs.2.1
    have hbnz : b'.val ≠ 0 := by
      intro h; apply hb0; apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat h
      rw [hbeq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b₁.val.isLt hp)] at this
      exact this
    refine ⟨hbnz, hk _ _ (TRel.cons ?_ TRel.nil) hwP⟩
    change (a'.val % b'.val, ()) = (BitVec.setWidth (target.widenWidth n) (a₁.val % b₁.val), ())
    congr 1; apply BitVec.eq_of_toNat_eq
    have hbpos : 0 < b₁.val.toNat := Nat.pos_of_ne_zero fun h => hb0 (BitVec.eq_of_toNat_eq h)
    rw [BitVec.toNat_umod, haeq, hbeq, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      BitVec.toNat_setWidth, BitVec.toNat_umod,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt hp),
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b₁.val.isLt hp),
      Nat.mod_eq_of_lt
        (Nat.lt_trans (Nat.mod_lt a₁.val.toNat hbpos) (Nat.lt_of_lt_of_le b₁.val.isLt hp))]
  | srem n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_srem] at hw
    rcases hw with ⟨hsdef, hwP⟩
    have hb0 : b₁.val ≠ 0 := by
      dsimp only [sdivDefined] at hsdef
      simp only [Bool.and_eq_true, bne_iff_ne] at hsdef
      exact hsdef.1
    have hn0 : n ≠ 0 := by intro h; subst h; exact hb0 (Subsingleton.elim _ _)
    dsimp only [legalOp]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩; rw [hpb] at hb_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    simp only [beq_iff_eq, hn0, ↓reduceIte]
    split
    · next hnw =>
      rw [wp_let, op2_wp_eq, OpCode.wp_srem]; dsimp only
      refine ⟨op2_pred_self (P := fun {k} x y => sdivDefined x y = true) hnw haeq hbeq hsdef,
        hk _ _ (TRel.cons ?_ TRel.nil) hwP⟩
      change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
      congr 1; simp only [Arg.val_var]; exact op2_setWidth_self hnw haeq hbeq
    · next hnw =>
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      have hn_lt : n < target.widenWidth n := Nat.lt_of_le_of_ne hs.2.1 hnw
      refine emitSextToW_wp hn_pos hs.2.1 haeq fun sa hsa =>
        emitSextToW_wp hn_pos hs.2.1 hbeq fun sb hsb => ?_
      rw [wp_let, op2_wp_eq, OpCode.wp_srem]; dsimp only
      refine ⟨by rw [hsa, hsb]; exact opWp_sdivDefined_widened hn_pos hn_lt hb0, ?_⟩
      refine emitMaskToN_wp hs.2.1 rfl fun rm hrm => ?_
      simp only [Arg.val_var] at hrm
      refine hk _ _ (TRel.cons ?_ TRel.nil) hwP
      change (rm.val, ()) = (BitVec.setWidth (target.widenWidth n) (BitVec.srem a₁.val b₁.val), ())
      congr 1; rw [hrm, hsa, hsb, opWp_srem_widened hs.2.1 a₁.val b₁.val]
  | udiv0 n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_udiv0] at hw
    dsimp only [legalOp]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩; rw [hpb] at hb_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
      have h0 : (if b₁.val = 0 then 0 else a₁.val / b₁.val) = 0#0 := Subsingleton.elim _ _
      rw [h0]; congr 1
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      rw [wp_let, op2_wp_eq, OpCode.wp_udiv0]; dsimp only
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      change ((if b'.val = 0 then 0 else a'.val / b'.val), ()) =
        (BitVec.setWidth (target.widenWidth n) (if b₁.val = 0 then 0 else a₁.val / b₁.val), ())
      congr 1
      have hp : 2 ^ n ≤ 2 ^ target.widenWidth n := Nat.pow_le_pow_right (by omega) hs.2.1
      have hbz : (b'.val = 0) ↔ (b₁.val = 0) := by
        constructor
        · intro h; apply BitVec.eq_of_toNat_eq
          have := congrArg BitVec.toNat h
          rw [hbeq, BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b₁.val.isLt hp)] at this
          exact this
        · intro h; rw [hbeq, h]; apply BitVec.eq_of_toNat_eq; simp
      by_cases hb0 : b₁.val = 0
      · have hb0' : b'.val = 0 := hbz.mpr hb0
        simp only [hb0, hb0', ↓reduceIte]; apply BitVec.eq_of_toNat_eq; simp
      · have hb0' : b'.val ≠ 0 := fun h => hb0 (hbz.mp h)
        simp only [hb0, hb0', ↓reduceIte]; apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_udiv, haeq, hbeq, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
          BitVec.toNat_setWidth, BitVec.toNat_udiv,
          Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt hp),
          Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b₁.val.isLt hp),
          Nat.mod_eq_of_lt
            (Nat.lt_of_le_of_lt (Nat.div_le_self a₁.val.toNat b₁.val.toNat)
            (Nat.lt_of_lt_of_le a₁.val.isLt hp))]
  | sdiv0 n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_sdiv0] at hw
    dsimp only [legalOp]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩; rw [hpb] at hb_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
      have h0 : (if b₁.val = 0 then 0 else BitVec.sdiv a₁.val b₁.val) = 0#0 := Subsingleton.elim _ _
      rw [h0]; congr 1
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op2_wp_eq, OpCode.wp_sdiv0]; dsimp only
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1
        exact op2_setWidth_self
          (op := fun {k} (x y : BitVec k) => if y = 0 then 0 else BitVec.sdiv x y)
          hnw haeq hbeq
      · next _ =>
        have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
        refine emitSextToW_wp hn_pos hs.2.1 haeq fun sa hsa =>
          emitSextToW_wp hn_pos hs.2.1 hbeq fun sb hsb => ?_
        rw [wp_let, op2_wp_eq, OpCode.wp_sdiv0]; dsimp only
        refine emitMaskToN_wp hs.2.1 rfl fun rm hrm => ?_
        simp only [Arg.val_var] at hrm
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (rm.val, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1; rw [hrm, hsa, hsb]; congr 1
        have hsbz : (BitVec.signExtend (target.widenWidth n) b₁.val = 0) ↔ (b₁.val = 0) := by
          constructor
          · intro h
            have hi := congrArg BitVec.toInt h
            rw [opWp_signExtend_toInt hs.2.1] at hi
            have := congrArg (BitVec.ofInt n) hi
            simpa [BitVec.ofInt_toInt] using this
          · intro h; rw [h]; apply BitVec.eq_of_toNat_eq
            rw [BitVec.signExtend_eq_setWidth_of_msb_false (by
              rw [BitVec.msb_eq_getLsbD_last]; simp)]; simp
        by_cases hb0 : b₁.val = 0
        · have hb0' : BitVec.signExtend (target.widenWidth n) b₁.val = 0 := hsbz.mpr hb0
          simp only [hb0', ↓reduceIte]; simp only [hb0, ↓reduceIte]; apply BitVec.eq_of_toNat_eq;
            simp
        · have hb0' : BitVec.signExtend (target.widenWidth n) b₁.val ≠ 0 := fun h => hb0 (hsbz.mp h)
          rw [ite_eq_right hb0', ite_eq_right hb0]
          exact opWp_sdiv_widened hs.2.1 a₁.val b₁.val
  | mkpair a b =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_mkpair] at hw
    dsimp only [legalOp]
    dsimp only [LegalTarget.supportsOpCode] at hsupp
    simp only [Bool.and_eq_true] at hsupp
    by_cases hkp : target.keepsPacked (a.pair b) = true
    · simp only [hkp, ↓reduceDIte]
      refine packFromLegal_wp target a hsupp.1 (legalArg target a₂) a₁.val
        (valsTup_legalArg target hG ha)
        fun pa hpa => packFromLegal_wp target b hsupp.2 (legalArg target b₂) b₁.val
          (valsTup_legalArg target hG hb) fun pb hpb => ?_
      rw [wp_let, op2_wp_eq, OpCode.wp_mkpair]; dsimp only
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      have hres := opWp_valsTup_tupToPacked hkp (Arg.var (V := Val) (pa.val, pb.val), ())
      simpa [hpa, hpb] using hres
    · have hkf : target.keepsPacked (a.pair b) = false := Bool.eq_false_iff.mpr hkp
      simp only [hkp]
      exact hk _ _ (TRel.cons (opWp_valsTup_tupToSplit hkf (legalArg target a₂) (legalArg target b₂)
        (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb)) TRel.nil) hw
  | unpair a b =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, hp, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_unpair] at hw
    dsimp only [legalOp]
    dsimp only [LegalTarget.supportsOpCode] at hsupp
    simp only [Bool.and_eq_true] at hsupp
    by_cases hkp : target.keepsPacked (a.pair b) = true
    · simp only [hkp, ↓reduceDIte]
      have hlp := valsTup_legalArg target hG hp
      have hfst := opWp_packedToTup_fst hkp (legalArg target a₂) a₁.val hlp
      cases hpfst : (packedToTup hkp (legalArg target a₂)).fst with
      | imm c =>
        simp only [hpfst] at hfst ⊢
        have hc_eq : c = a₁.val := hfst
        rw [hc_eq]
        exact hk _ _ (TRel.cons (opWp_valsTup_encodeImm target a a₁.val.1)
          (TRel.cons (opWp_valsTup_encodeImm target b a₁.val.2) TRel.nil)) hw
      | var v =>
        simp only [hpfst] at hfst ⊢
        have hv_eq : v = a₁.val := hfst
        rw [wp_let, op1_wp_eq, OpCode.wp_unpair]; dsimp only
        rw [hv_eq]
        exact unpackToLegal_wp target a hsupp.1 (Arg.var a₁.val.1) fun la hla =>
          unpackToLegal_wp target b hsupp.2 (Arg.var a₁.val.2) fun lb hlb =>
            hk _ _ (TRel.cons hla (TRel.cons hlb TRel.nil)) hw
    · have hkf : target.keepsPacked (a.pair b) = false := Bool.eq_false_iff.mpr hkp
      simp only [hkp]
      have hsp :=
        opWp_valsTup_splitToTup hkf (legalArg target a₂) a₁.val (valsTup_legalArg target hG hp)
      rcases htup : tupSplit (splitToTup hkf (legalArg target a₂)) with ⟨la, lb⟩
      rw [htup] at hsp
      simp only [htup]
      exact hk _ _ (TRel.cons hsp.1 (TRel.cons hsp.2 TRel.nil)) hw
  | bitcast t u hsz =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_bitcast] at hw
    dsimp only [legalOp]
    dsimp only [LegalTarget.supportsOpCode] at hsupp
    simp only [Bool.and_eq_true] at hsupp
    by_cases heq : t = u
    · subst heq; simp only [↓reduceDIte]
      have hid : ofBits t (BitVec.cast rfl (toBits t a₁.val)) = a₁.val := ofBits_toBits t a₁.val
      rw [hid] at hw
      exact hk _ _ (TRel.cons (valsTup_legalArg target hG ha) TRel.nil) hw
    · simp only [heq, ↓reduceDIte]
      by_cases ht : isNatTy target t = true
      · refine dite_true_wp (P := fun e => wp Γ Q X e m) (by cases t <;> simpa [isNatTy] using ht)
          ?_
        by_cases hu : isNatTy target u = true
        · refine dite_true_wp (P := fun e => wp Γ Q X e m) (by cases u <;> simpa [isNatTy] using hu)
            ?_
          have hlt_leg : target.isLegalTy t = true := by
            cases t with | bits _ => exact (Bool.and_eq_true _ _ |>.mp ht).1 | _ => exact ht
          have hlu_leg : target.isLegalTy u = true := by
            cases u with | bits _ => exact (Bool.and_eq_true _ _ |>.mp hu).1 | _ => exact hu
          have hlt_tys : target.legalTys t = [t] := opWp_isLegalTy_legalTys hlt_leg
          have hlu_tys : target.legalTys u = [u] := opWp_isLegalTy_legalTys hlu_leg
          rw [wp_let, op1_wp_eq, OpCode.wp_bitcast]; dsimp only
          have hin := opWp_cast_isLegal_in hlt_leg hlt_tys (legalArg target a₂) a₁.val
            (valsTup_legalArg target hG ha)
          rw [hin]
          exact hk _ _ (TRel.cons (opWp_cast_isLegal_out hlu_leg hlu_tys (Arg.var _)) TRel.nil) hw
        · refine dite_false_wp (P := fun e => wp Γ Q X e m)
            (by cases u <;> simpa [isNatTy] using hu) ?_
          refine splitLegalToLeaves_wp target t hsupp.1 (legalArg target a₂) a₁.val
            (valsTup_legalArg target hG ha) fun fx hfx =>
            packLeavesToWords64_wp target hv t hsupp.1 hfx fun words hbits _ _ =>
            unpackWords64ToLeaves_wp target hv u hsupp.2
              (fun i hi => by
                rw [Nat.zero_add, hbits i (by rw [hsz]; exact hi), toBits_ofBits,
                  BitVec.getLsbD_cast])
              fun fu hfu => packLeavesToLegal_wp target u hsupp.2 fu _ hfu fun res hres =>
                hk _ _ (TRel.cons hres TRel.nil) hw
      · refine dite_false_wp (P := fun e => wp Γ Q X e m) (by cases t <;> simpa [isNatTy] using ht)
          ?_
        refine splitLegalToLeaves_wp target t hsupp.1 (legalArg target a₂) a₁.val
          (valsTup_legalArg target hG ha) fun fx hfx =>
          packLeavesToWords64_wp target hv t hsupp.1 hfx fun words hbits _ _ =>
          unpackWords64ToLeaves_wp target hv u hsupp.2
            (fun i hi => by
              rw [Nat.zero_add, hbits i (by rw [hsz]; exact hi), toBits_ofBits,
                BitVec.getLsbD_cast])
            fun fu hfu => packLeavesToLegal_wp target u hsupp.2 fu _ hfu fun res hres =>
              hk _ _ (TRel.cons hres TRel.nil) hw
  | shufd t imm =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    have hsupp := (Bool.and_eq_true _ _ |>.mp hsupp).1
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_shufd] at hw
    rcases hw with ⟨hne, hmod, hwP⟩
    dsimp only [legalOp]
    exact legalShufd_wp target hv imm t hsupp hne hmod (legalArg target a₂) a₁.val
      (valsTup_legalArg target hG ha) (fun res => k (res, ())) m fun res hres =>
        hk _ _ (TRel.cons hres TRel.nil) hwP
  | shufb t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    have hsupp := (Bool.and_eq_true _ _ |>.mp hsupp).1
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_shufb] at hw
    rcases hw with ⟨hne, hmod, hwP⟩
    dsimp only [legalOp]
    exact legalShufb_wp target hv t hsupp hne hmod (legalArg target a₂) (legalArg target b₂) a₁.val
      b₁.val
      (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb) (fun res => k (res, ())) m
      fun res hres => hk _ _ (TRel.cons hres TRel.nil) hwP
  | alignr t imm =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    have hsupp := (Bool.and_eq_true _ _ |>.mp hsupp).1
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_alignr] at hw
    rcases hw with ⟨hne, hmod, hwP⟩
    dsimp only [legalOp]
    exact legalAlignr_wp target hv imm t hsupp hne hmod (legalArg target a₂) (legalArg target b₂)
      a₁.val b₁.val
      (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb) (fun res => k (res, ())) m
      fun res hres => hk _ _ (TRel.cons hres TRel.nil) hwP
  | blendw t imm =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    have hsupp := (Bool.and_eq_true _ _ |>.mp hsupp).1
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_blendw] at hw
    rcases hw with ⟨hne, hmod, hwP⟩
    dsimp only [legalOp]
    exact legalBlendw_wp target hv imm t hsupp hne hmod (legalArg target a₂) (legalArg target b₂)
      a₁.val b₁.val
      (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb) (fun res => k (res, ())) m
      fun res hres => hk _ _ (TRel.cons hres TRel.nil) hwP
  | sha256rnds2 =>
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, w₁, w₂, _, _, hw', hargs⟩; cases hargs
    have hsupp := (Bool.and_eq_true _ _ |>.mp hsupp).1
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_sha256rnds2] at hw
    dsimp only [legalOp]
    have hc_val := valsTup_legalArg target hG hc'
    have ha_val := valsTup_legalArg target hG ha
    have hw_val := valsTup_legalArg target hG hw'
    split
    · next hcond =>
      have hkp : target.keepsPacked v4i32 = true := (Bool.and_eq_true _ _ |>.mp hcond).1
      have hl_leg : target.isLegalTy v4i32 = true := hkp
      have hl_tys : target.legalTys v4i32 = [v4i32] := opWp_isLegalTy_legalTys hkp
      rw [wp_let, op3_wp_eq, OpCode.wp_sha256rnds2]; dsimp only
      rw [opWp_cast_isLegal_in hl_leg hl_tys (legalArg target c₂) c₁.val hc_val,
        opWp_cast_isLegal_in hl_leg hl_tys (legalArg target a₂) a₁.val ha_val,
        opWp_cast_isLegal_in hl_leg hl_tys (legalArg target w₂) w₁.val hw_val]
      exact hk _ _ (TRel.cons (opWp_cast_isLegal_out hl_leg hl_tys (Arg.var _)) TRel.nil) hw
    · refine splitLegalToLeaves_wp target v4i32 hsupp (legalArg target c₂) c₁.val hc_val fun fc
        hfc =>
        splitLegalToLeaves_wp target v4i32 hsupp (legalArg target a₂) a₁.val ha_val fun fa hfa =>
        splitLegalToLeaves_wp target v4i32 hsupp (legalArg target w₂) w₁.val hw_val fun fw hfw =>
        packLeavesToWords64_wp target hv v4i32 hsupp hfc fun wc hwc _ hwcl =>
        packLeavesToWords64_wp target hv v4i32 hsupp hfa fun wa hwa _ hwal =>
        packLeavesToWords64_wp target hv v4i32 hsupp hfw fun ww hww _ hwwl => ?_
      have hcw := opWp_words64_two wc (toBits v4i32 c₁.val) hwc (hwcl rfl)
      have haw := opWp_words64_two wa (toBits v4i32 a₁.val) hwa (hwal rfl)
      have hww' := opWp_words64_two ww (toBits v4i32 w₁.val) hww (hwwl rfl)
      refine words2ToDwords4_wp hcw.1 hcw.2 fun cd0 cd1 cd2 cd3 hcd0 hcd1 hcd2 hcd3 =>
        words2ToDwords4_wp haw.1 haw.2 fun ab0 ab1 ab2 ab3 hab0 hab1 hab2 hab3 =>
        words2ToDwords4_wp hww'.1 hww'.2 fun wk0 wk1 wk2 wk3 hwk0 hwk1 _ _ =>
        scalarSha256rnds2_wp hcd0 hcd1 hcd2 hcd3 hab0 hab1 hab2 hab3 hwk0 hwk1 fun r0 r1 r2 r3 hr0
          hr1 hr2 hr3 =>
        dwords4ToWords2_wp hr0 hr1 hr2 hr3 fun w0 w1 hw0 hw1 =>
        unpackWords64ToLeaves_wp target hv v4i32 hsupp (fun i hi => by
          have hi128 : i < 128 := hi
          rw [Nat.zero_add, toBits_ofBits]
          by_cases hi64 : i < 64
          · simp [words64GetLsb, Nat.div_eq_of_lt hi64, Nat.mod_eq_of_lt hi64, hw0, hi64]
          · have hi2 : i - 64 < 64 := by omega
            simp [words64GetLsb, show i / 64 = 1 by omega, show i % 64 = i - 64 by omega, hw1,
              hi2, show 64 + (i - 64) = i by omega])
        fun fres hfres => packLeavesToLegal_wp target v4i32 hsupp fres _ hfres fun res hres =>
          hk _ _ (TRel.cons hres TRel.nil) hw
  | sha256msg1 =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    have hsupp := (Bool.and_eq_true _ _ |>.mp hsupp).1
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_sha256msg1] at hw
    dsimp only [legalOp]
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    split
    · next hcond =>
      have hkp : target.keepsPacked v4i32 = true := (Bool.and_eq_true _ _ |>.mp hcond).1
      have hl_leg : target.isLegalTy v4i32 = true := hkp
      have hl_tys : target.legalTys v4i32 = [v4i32] := opWp_isLegalTy_legalTys hkp
      rw [wp_let, op2_wp_eq, OpCode.wp_sha256msg1]; dsimp only
      rw [opWp_cast_isLegal_in hl_leg hl_tys (legalArg target a₂) a₁.val ha_val,
        opWp_cast_isLegal_in hl_leg hl_tys (legalArg target b₂) b₁.val hb_val]
      exact hk _ _ (TRel.cons (opWp_cast_isLegal_out hl_leg hl_tys (Arg.var _)) TRel.nil) hw
    · refine splitLegalToLeaves_wp target v4i32 hsupp (legalArg target a₂) a₁.val ha_val fun fa
        hfa =>
        splitLegalToLeaves_wp target v4i32 hsupp (legalArg target b₂) b₁.val hb_val fun fb hfb =>
        packLeavesToWords64_wp target hv v4i32 hsupp hfa fun wa hwa _ hwal =>
        packLeavesToWords64_wp target hv v4i32 hsupp hfb fun wb hwb _ hwbl => ?_
      have haw := opWp_words64_two wa (toBits v4i32 a₁.val) hwa (hwal rfl)
      have hbw := opWp_words64_two wb (toBits v4i32 b₁.val) hwb (hwbl rfl)
      refine words2ToDwords4_wp haw.1 haw.2 fun a0 a1 a2 a3 ha0 ha1 ha2 ha3 =>
        words2ToDwords4_wp hbw.1 hbw.2 fun b0 b1 b2 b3 hb0 _ _ _ =>
        scalarSha256msg1_wp ha0 ha1 ha2 ha3 hb0 fun r0 r1 r2 r3 hr0 hr1 hr2 hr3 =>
        dwords4ToWords2_wp hr0 hr1 hr2 hr3 fun w0 w1 hw0 hw1 =>
        unpackWords64ToLeaves_wp target hv v4i32 hsupp (fun i hi => by
          have hi128 : i < 128 := hi
          rw [Nat.zero_add, toBits_ofBits]
          by_cases hi64 : i < 64
          · simp [words64GetLsb, Nat.div_eq_of_lt hi64, Nat.mod_eq_of_lt hi64, hw0, hi64]
          · have hi2 : i - 64 < 64 := by omega
            simp [words64GetLsb, show i / 64 = 1 by omega, show i % 64 = i - 64 by omega, hw1,
              hi2, show 64 + (i - 64) = i by omega])
        fun fres hfres => packLeavesToLegal_wp target v4i32 hsupp fres _ hfres fun res hres =>
          hk _ _ (TRel.cons hres TRel.nil) hw
  | sha256msg2 =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    have hsupp := (Bool.and_eq_true _ _ |>.mp hsupp).1
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_sha256msg2] at hw
    dsimp only [legalOp]
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    split
    · next hcond =>
      have hkp : target.keepsPacked v4i32 = true := (Bool.and_eq_true _ _ |>.mp hcond).1
      have hl_leg : target.isLegalTy v4i32 = true := hkp
      have hl_tys : target.legalTys v4i32 = [v4i32] := opWp_isLegalTy_legalTys hkp
      rw [wp_let, op2_wp_eq, OpCode.wp_sha256msg2]; dsimp only
      rw [opWp_cast_isLegal_in hl_leg hl_tys (legalArg target a₂) a₁.val ha_val,
        opWp_cast_isLegal_in hl_leg hl_tys (legalArg target b₂) b₁.val hb_val]
      exact hk _ _ (TRel.cons (opWp_cast_isLegal_out hl_leg hl_tys (Arg.var _)) TRel.nil) hw
    · refine splitLegalToLeaves_wp target v4i32 hsupp (legalArg target a₂) a₁.val ha_val fun fa
        hfa =>
        splitLegalToLeaves_wp target v4i32 hsupp (legalArg target b₂) b₁.val hb_val fun fb hfb =>
        packLeavesToWords64_wp target hv v4i32 hsupp hfa fun wa hwa _ hwal =>
        packLeavesToWords64_wp target hv v4i32 hsupp hfb fun wb hwb _ hwbl => ?_
      have haw := opWp_words64_two wa (toBits v4i32 a₁.val) hwa (hwal rfl)
      have hbw := opWp_words64_two wb (toBits v4i32 b₁.val) hwb (hwbl rfl)
      refine words2ToDwords4_wp haw.1 haw.2 fun s0 s1 s2 s3 hs0 hs1 hs2 hs3 =>
        words2ToDwords4_wp hbw.1 hbw.2 fun w0 w1 w2 w3 _ _ hw2 hw3 =>
        scalarSha256msg2_wp hs0 hs1 hs2 hs3 hw2 hw3 fun r0 r1 r2 r3 hr0 hr1 hr2 hr3 =>
        dwords4ToWords2_wp hr0 hr1 hr2 hr3 fun wr0 wr1 hwr0 hwr1 =>
        unpackWords64ToLeaves_wp target hv v4i32 hsupp (fun i hi => by
          have hi128 : i < 128 := hi
          rw [Nat.zero_add, toBits_ofBits]
          by_cases hi64 : i < 64
          · simp [words64GetLsb, Nat.div_eq_of_lt hi64, Nat.mod_eq_of_lt hi64, hwr0, hi64]
          · have hi2 : i - 64 < 64 := by omega
            simp [words64GetLsb, show i / 64 = 1 by omega, show i % 64 = i - 64 by omega, hwr1,
              hi2, show 64 + (i - 64) = i by omega])
        fun fres hfres => packLeavesToLegal_wp target v4i32 hsupp fres _ hfres fun res hres =>
          hk _ _ (TRel.cons hres TRel.nil) hw
  | fadd t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [legalOp]
    exact legalOp_floatBin_wp target hG OpCode.fadd Float.Model.UnpackedFloat.add
      (fun u x y p => OpCode.wp_fadd u (x, y, ()) p) (fun _ => rfl) hsupp ha hb hw hk
  | fsub t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [legalOp]
    exact legalOp_floatBin_wp target hG OpCode.fsub Float.Model.UnpackedFloat.sub
      (fun u x y p => OpCode.wp_fsub u (x, y, ()) p) (fun _ => rfl) hsupp ha hb hw hk
  | fmul t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [legalOp]
    exact legalOp_floatBin_wp target hG OpCode.fmul Float.Model.UnpackedFloat.mul
      (fun u x y p => OpCode.wp_fmul u (x, y, ()) p) (fun _ => rfl) hsupp ha hb hw hk
  | fdiv t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [legalOp]
    exact legalOp_floatBin_wp target hG OpCode.fdiv Float.Model.UnpackedFloat.div
      (fun u x y p => OpCode.wp_fdiv u (x, y, ()) p) (fun _ => rfl) hsupp ha hb hw hk
  | ffma t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_ffma] at hw
    dsimp only [legalOp]
    cases hft : t.isFloatTree
    · simp [hft] at hw
    · simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      refine legalTernaryTree_wp target OpCode.ffma
        (fun u => target.vecFloatOpSupported (OpCode.ffma u) u)
        (fun _ _ _ _ => Expr.hlt) (fun _ _ _ _ _ => Expr.hlt)
        (fun fmt x y z cont => Expr.let_ (op3 (OpCode.ffma (Ty.float fmt)) x y z) fun (r, _) =>
          cont (Arg.var r))
        (onB := fun _ _ _ _ => False) (onBi := fun _ _ _ _ _ => False)
        (onF := fun fmt a b c q =>
          floatResultWp fmt (Float.Model.UnpackedFloat.fma fmt.format
            (unpackFloat fmt a) (unpackFloat fmt b) (unpackFloat fmt c)) q)
        (by intros; contradiction)
        (by intros; contradiction)
        ?_ ?_ (by intros; contradiction) (by intros; contradiction)
        (fun fmt _ _ _ _ _ hpq h => opWp_floatResultWp_mono fmt _ hpq h)
        t hsupp (legalArg target a₂) (legalArg target b₂) (legalArg target c₂) a₁.val b₁.val c₁.val
        (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb)
          (valsTup_legalArg target hG hc')
        (fun res => k (res, ())) m ?_
      · intro fmt _ a' b' c' a b c cont m' ha' hb' hc'' hpre
        rw [wp_let, op3_wp_eq, OpCode.wp_ffma];
          simp only [Ty.isFloatTree, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        change floatResultWp fmt (Float.Model.UnpackedFloat.fma fmt.format
          (unpackFloat fmt a'.val) (unpackFloat fmt b'.val) (unpackFloat fmt c'.val)) _
        rw [ha', hb', hc'']
        exact opWp_floatResultWp_mono fmt _ (fun res hres => hres (Arg.var res) rfl) hpre
      · intro u _ _ _ x y z p htr
        have hu := opWp_float3_isFloatTree_of_treeRel3 Float.Model.UnpackedFloat.fma u x y z p htr
        rw [OpCode.wp_ffma]; simp [hu.1, hu.2]
      · exact opWp_treeRel3_float3 Float.Model.UnpackedFloat.fma t hft a₁.val b₁.val c₁.val _
          (opWp_liftFloatRel3_mono Float.Model.UnpackedFloat.fma t a₁.val b₁.val c₁.val
            (fun r hr => fun fres hfres => hk _ _ (TRel.cons hfres TRel.nil) hr) hw)
  | fsqrt t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_fsqrt] at hw
    dsimp only [legalOp]
    cases hft : t.isFloatTree
    · simp [hft] at hw
    · simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      refine legalUnaryTree_wp target OpCode.fsqrt
        (fun u => target.vecFloatOpSupported (OpCode.fsqrt u) u)
        (fun _ _ => Expr.hlt) (fun _ _ _ => Expr.hlt)
        (fun fmt x cont => Expr.let_ (op1 (OpCode.fsqrt (Ty.float fmt)) x) fun (r, _) =>
          cont (Arg.var r))
        (onB := fun _ _ => False) (onBi := fun _ _ _ => False)
        (onF := fun fmt a q =>
          floatResultWp fmt (Float.Model.UnpackedFloat.sqrt fmt.format (unpackFloat fmt a)) q)
        (by intros; contradiction)
        (by intros; contradiction)
        ?_ ?_ (by intros; contradiction) (by intros; contradiction)
        (fun fmt _ _ _ hpq h => opWp_floatResultWp_mono fmt _ hpq h)
        t hsupp (legalArg target a₂) a₁.val (valsTup_legalArg target hG ha) (fun res => k (res, ()))
          m ?_
      · intro fmt _ a' a cont m' ha' hpre
        rw [wp_let, op1_wp_eq, OpCode.wp_fsqrt];
          simp only [Ty.isFloatTree, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        change floatResultWp fmt
          (Float.Model.UnpackedFloat.sqrt fmt.format (unpackFloat fmt a'.val)) _
        rw [ha']
        exact opWp_floatResultWp_mono fmt _ (fun res hres => hres (Arg.var res) rfl) hpre
      · intro u _ _ _ x p htr
        have hu := opWp_float1_isFloatTree_of_treeRel1 Float.Model.UnpackedFloat.sqrt u x p htr
        rw [OpCode.wp_fsqrt]; simp [hu.1, hu.2]
      · exact opWp_treeRel1_float1 Float.Model.UnpackedFloat.sqrt t hft a₁.val _
          (opWp_liftFloatRel1_mono Float.Model.UnpackedFloat.sqrt t a₁.val
            (fun r hr => fun fres hfres => hk _ _ (TRel.cons hfres TRel.nil) hr) hw)
  | fneg t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_fneg] at hw
    dsimp only [legalOp]
    cases hft : t.isFloatTree
    · simp [hft] at hw
    · simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      refine legalUnaryTree_wp target OpCode.fneg
        (fun u => target.vecFloatOpSupported (OpCode.fneg u) u)
        (fun _ _ => Expr.hlt) (fun _ _ _ => Expr.hlt)
        (fun fmt x cont => Expr.let_ (op1 (OpCode.fneg (Ty.float fmt)) x) fun (r, _) =>
          cont (Arg.var r))
        (onB := fun _ _ => False) (onBi := fun _ _ _ => False)
        (onF := fun fmt a q => q (a ^^^ 1#fmt.width <<< (fmt.width - 1)))
        (by intros; contradiction)
        (by intros; contradiction)
        (fun fmt _ x' x cont m' hx' hpre => by
          rw [wp_let, op1_wp_eq, OpCode.wp_fneg, hx']; exact hpre _ rfl)
        (fun u _ _ _ x p htr => by
          have hu := opWp_lift1_float_of_treeRel1 (fun {n} x => x ^^^ 1#n <<< (n - 1)) u x p htr
          rw [OpCode.wp_fneg]; simp [hu.1, hu.2])
        (by intros; contradiction) (by intros; contradiction)
        (fun _ _ _ _ hpq h => hpq _ h)
        t hsupp (legalArg target a₂) a₁.val (valsTup_legalArg target hG ha) (fun res => k (res, ()))
          m
        (opWp_treeRel1_lift1_float (fun {n} x => x ^^^ 1#n <<< (n - 1)) t hft _ _
          fun fres hfres => hk _ _ (TRel.cons hfres TRel.nil) hw)
  | fabs t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_fabs] at hw
    dsimp only [legalOp]
    cases hft : t.isFloatTree
    · simp [hft] at hw
    · simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      refine legalUnaryTree_wp target OpCode.fabs
        (fun u => target.vecFloatOpSupported (OpCode.fabs u) u)
        (fun _ _ => Expr.hlt) (fun _ _ _ => Expr.hlt)
        (fun fmt x cont => Expr.let_ (op1 (OpCode.fabs (Ty.float fmt)) x) fun (r, _) =>
          cont (Arg.var r))
        (onB := fun _ _ => False) (onBi := fun _ _ _ => False)
        (onF := fun fmt a q => q (a &&& ~~~(1#fmt.width <<< (fmt.width - 1))))
        (by intros; contradiction)
        (by intros; contradiction)
        (fun fmt _ x' x cont m' hx' hpre => by
          rw [wp_let, op1_wp_eq, OpCode.wp_fabs, hx']; exact hpre _ rfl)
        (fun u _ _ _ x p htr => by
          have hu := opWp_lift1_float_of_treeRel1 (fun {n} x => x &&& ~~~(1#n <<< (n - 1))) u x p
            htr
          rw [OpCode.wp_fabs]; simp [hu.1, hu.2])
        (by intros; contradiction) (by intros; contradiction)
        (fun _ _ _ _ hpq h => hpq _ h)
        t hsupp (legalArg target a₂) a₁.val (valsTup_legalArg target hG ha) (fun res => k (res, ()))
          m
        (opWp_treeRel1_lift1_float (fun {n} x => x &&& ~~~(1#n <<< (n - 1))) t hft _ _
          fun fres hfres => hk _ _ (TRel.cons hfres TRel.nil) hw)
  | fcmp o t m_ty hm =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    cases hm
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_fcmp] at hw
    dsimp only [legalOp]
    cases hft : t.isFloatTree
    · simp [hft] at hw
    · simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      exact legalFCmpTree_wp target o t hsupp hft (legalArg target a₂) (legalArg target b₂)
        a₁.val b₁.val (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb)
        (fun res => k (res, ())) m
        (fun res hres => hk (liftFCmp o t a₁.val b₁.val, ()) (res, ()) (TRel.cons hres TRel.nil) hw)
  | fptoui fmt n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_fptoui] at hw
    dsimp only [legalOp]
    have ha_val := valsTup_legalArg target hG ha
    split
    · next a' hpa =>
      dsimp only [Tup, LVar, LegalTarget.legalTys] at k ha_val ⊢
      rw [hpa] at ha_val
      have haeq : a'.val = a₁.val := (Prod.mk.inj ha_val).1
      dsimp only [LegalTarget.supportsOpCode] at hsupp
      simp only [Bool.and_eq_true] at hsupp
      have hs := opWp_widen_spec hv hsupp.2
      cases htr : truncToInt (unpackFloat fmt a₁.val) with
      | none => simp [htr] at hw
      | some z =>
        simp only [htr] at hw
        rcases hw with ⟨hz0, hzn, hwP⟩
        have hzn' : z < ((2 ^ n : Nat) : Int) := by
          push_cast; exact hzn
        have hp : 2 ^ n ≤ 2 ^ target.widenWidth n := Nat.pow_le_pow_right (by omega) hs.2.1
        have hzw : z < 2 ^ target.widenWidth n := by
          rw [show (2 ^ target.widenWidth n : Int) = ((2 ^ target.widenWidth n : Nat) : Int) from
            (Int.natCast_pow 2 _).symm]
          omega
        by_cases hn0 : n = 0
        · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
          rw [wp_let, op1_wp_eq, OpCode.wp_fptoui, haeq, htr]
          refine ⟨hz0, hzw, hk _ _ (TRel.cons ?_ TRel.nil) hwP⟩
          change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
          have h0 : BitVec.ofInt 0 z = 0#0 := Subsingleton.elim _ _
          rw [h0]; congr 1
        · simp only [beq_iff_eq, hn0, ↓reduceIte]
          rw [wp_let, op1_wp_eq, OpCode.wp_fptoui, haeq, htr]
          refine ⟨hz0, hzw, hk _ _ (TRel.cons ?_ TRel.nil) hwP⟩
          change (BitVec.ofInt (target.widenWidth n) z, ()) =
            (BitVec.setWidth (target.widenWidth n) (BitVec.ofInt n z), ())
          congr 1; exact opWp_fptoui_widened (Nat.pos_of_ne_zero hn0) hs.2.1 hz0 hzn'
  | fptosi fmt n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_fptosi] at hw
    rcases hw with ⟨hn0, hw⟩
    dsimp only [legalOp]
    have ha_val := valsTup_legalArg target hG ha
    split
    · next a' hpa =>
      dsimp only [Tup, LVar, LegalTarget.legalTys] at k ha_val ⊢
      rw [hpa] at ha_val
      have haeq : a'.val = a₁.val := (Prod.mk.inj ha_val).1
      dsimp only [LegalTarget.supportsOpCode] at hsupp
      simp only [Bool.and_eq_true] at hsupp
      have hs := opWp_widen_spec hv hsupp.2
      simp only [beq_iff_eq, hn0, ↓reduceIte]
      cases htr : truncToInt (unpackFloat fmt a₁.val) with
      | none => simp [htr] at hw
      | some z =>
        simp only [htr] at hw
        rcases hw with ⟨hzlo, hzhi, hwP⟩
        have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
        have hp : 2 ^ (n - 1) ≤ 2 ^ (target.widenWidth n - 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hzlo' : -(2 ^ (target.widenWidth n - 1) : Int) ≤ z := by
          rw [show (2 ^ (target.widenWidth n - 1) : Int) =
            ((2 ^ (target.widenWidth n - 1) : Nat) : Int) from (Int.natCast_pow 2 _).symm]
          rw [show (2 ^ (n - 1) : Int) = ((2 ^ (n - 1) : Nat) : Int) from
            (Int.natCast_pow 2 _).symm] at hzlo
          omega
        have hzhi' : z < 2 ^ (target.widenWidth n - 1) := by
          rw [show (2 ^ (target.widenWidth n - 1) : Int) =
            ((2 ^ (target.widenWidth n - 1) : Nat) : Int) from (Int.natCast_pow 2 _).symm]
          rw [show (2 ^ (n - 1) : Int) = ((2 ^ (n - 1) : Nat) : Int) from
            (Int.natCast_pow 2 _).symm] at hzhi
          omega
        split
        · next hnw =>
          rw [wp_let, op1_wp_eq, OpCode.wp_fptosi, haeq, htr]
          refine ⟨Nat.ne_of_gt hs.2.2.1, hzlo', hzhi', hk _ _ (TRel.cons ?_ TRel.nil) hwP⟩
          change (BitVec.ofInt (target.widenWidth n) z, ()) =
            (BitVec.setWidth (target.widenWidth n) (BitVec.ofInt n z), ())
          congr 1
          apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_setWidth, ← hnw]
          exact (Nat.mod_eq_of_lt (BitVec.ofInt n z).isLt).symm
        · next _ =>
          rw [wp_let, op1_wp_eq, OpCode.wp_fptosi, haeq, htr]
          refine ⟨Nat.ne_of_gt hs.2.2.1, hzlo', hzhi', ?_⟩
          refine emitMaskToN_wp hs.2.1 rfl fun rm hrm => ?_
          simp only [Arg.val_var] at hrm
          refine hk _ _ (TRel.cons ?_ TRel.nil) hwP
          change (rm.val, ()) = (BitVec.setWidth (target.widenWidth n) (BitVec.ofInt n z), ())
          congr 1; rw [hrm, opWp_fptosi_widened hs.2.1 z]
  | uitofp n fmt =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_uitofp] at hw
    dsimp only [legalOp]
    have ha_val := valsTup_legalArg target hG ha
    split
    · next a' hpa =>
      dsimp only [Tup, LVar, LegalTarget.legalTys] at k ha_val ⊢
      rw [hpa] at ha_val
      have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
      dsimp only [LegalTarget.supportsOpCode] at hsupp
      simp only [Bool.and_eq_true] at hsupp
      have hs := opWp_widen_spec hv hsupp.2
      by_cases hn0 : n = 0
      · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
        rw [wp_let, op1_wp_eq, OpCode.wp_uitofp]; dsimp only
        have ha0 : a₁.val = 0#0 := Subsingleton.elim _ _
        have h0 : (0#(target.widenWidth 0)).toNat = (0#0).toNat := by simp
        rw [ha0, ← h0] at hw
        exact hk _ _ (TRel.cons (by rfl) TRel.nil) hw
      · simp only [beq_iff_eq, hn0, ↓reduceIte]
        rw [wp_let, op1_wp_eq, OpCode.wp_uitofp]; dsimp only
        have hp : 2 ^ n ≤ 2 ^ target.widenWidth n := Nat.pow_le_pow_right (by omega) hs.2.1
        have htn : a'.val.toNat = a₁.val.toNat := by
          rw [haeq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt hp)]
        rw [htn]
        exact hk _ _ (TRel.cons (by rfl) TRel.nil) hw
  | sitofp n fmt =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_sitofp] at hw
    dsimp only [legalOp]
    have ha_val := valsTup_legalArg target hG ha
    split
    · next a' hpa =>
      dsimp only [Tup, LVar, LegalTarget.legalTys] at k ha_val ⊢
      rw [hpa] at ha_val
      have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
      dsimp only [LegalTarget.supportsOpCode] at hsupp
      simp only [Bool.and_eq_true] at hsupp
      have hs := opWp_widen_spec hv hsupp.2
      by_cases hn0 : n = 0
      · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
        rw [wp_let, op1_wp_eq, OpCode.wp_sitofp]; dsimp only
        have ha0 : a₁.val = 0#0 := Subsingleton.elim _ _
        have hi0 : (0#(target.widenWidth 0)).toInt = (0#0).toInt := by
          simp [BitVec.toInt_zero]
        rw [ha0, ← hi0] at hw
        exact hk _ _ (TRel.cons (by rfl) TRel.nil) hw
      · simp only [beq_iff_eq, hn0, ↓reduceIte]
        refine emitSextToW_wp (Nat.pos_of_ne_zero hn0) hs.2.1 haeq fun sa hsa => ?_
        rw [wp_let, op1_wp_eq, OpCode.wp_sitofp]; dsimp only
        rw [hsa, opWp_signExtend_toInt hs.2.1]
        exact hk _ _ (TRel.cons (by rfl) TRel.nil) hw
  | fcvt fmt g =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_fcvt] at hw
    dsimp only [legalOp]
    have ha_val := valsTup_legalArg target hG ha
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    have haeq : a'.val = a₁.val := (Prod.mk.inj ha_val).1
    rw [wp_let, op1_wp_eq, OpCode.wp_fcvt, haeq]
    have hmono : ∀ (src dst : Fmt) (b : BitVec src.width) {p q : BitVec dst.width → Prop},
        (∀ r, p r → q r) → convertFloat src dst b p → convertFloat src dst b q := by
      intro src dst b p q hpq hcf
      dsimp only [convertFloat] at hcf ⊢
      cases huf : unpackFloat src b with
      | notANumber => simp only [huf] at hcf; exact fun r hr => hpq r (hcf r hr)
      | _ => simp only [huf] at hcf; exact hpq _ hcf
    exact hmono fmt g a₁.val (fun r hr => hk _ _ (TRel.cons (by rfl) TRel.nil) hr) hw

  | copy _ | add _ | sub _ | mul _ | neg _ | and _ | or _ | xor _ | not _
  | ternlog _ _ | shl _ | lshr _ | ashr _ | rotl _ | rotr _ | fshl _ | fshr _
  | bswap _ | clz _ | cls _ | rbit _ | ctz _ | popcnt _ | cmp _ _ _ _ | select _
  | blend _ _ _ | zext _ _ | sext _ _ | trunc _ _ | ofBool _ | addc _ | subb _
  | umulw _ | smulw _ => cases hpart

end LegalWp

end LeanQbe.T
