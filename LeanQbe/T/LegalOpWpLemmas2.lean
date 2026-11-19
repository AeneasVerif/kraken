module

public import LeanQbe.T.LegalOpWpLemmas1

/-!
# Legalization `legalOp_wp` semantic preservation for all `OpCode`s (`T5`, Part 3b)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

section LegalWp

theorem legalOp_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx Val (LVar target Val)} (hG : CGoodWp target G)
    {ts : List Ty} {op₁ : Op Val ts} {op₂ : Op (LVar target Val) ts}
    (hop : OpRel G op₁ op₂) (hsupp : target.supportsOpCode op₁.code = true)
    {P : Tup Val ts → Prop}
    {k : Tup (LVar target Val) ts → Expr Val Cont rs} {m : Mem 64}
    (hw : op₁.wp P)
    (hk : ∀ (r : Tup Val ts) (lr : Tup (LVar target Val) ts),
      TRel (fun t x lv => valsTup lv = encodeVal target t x) r lr →
      P r → wp Γ Q X (k lr) m) :
    wp Γ Q X (legalOp target op₂ k) m := by
  rcases hop with ⟨code, hargs⟩
  dsimp only at hsupp hw
  cases code with
  | copy t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    rw [legalOp.eq_1]
    exact hk _ _ (TRel.cons (valsTup_legalArg target hG ha) TRel.nil) hw
  | add t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_2]
    exact legalOp_intBin_wp target hG OpCode.add (fun {n} x1 x2 => x1 + x2) (fun x1 x2 => x1 ^^ x2)
      (fun u x y p => OpCode.wp_add u (x, y, ()) p) (fun _ => rfl)
      (fun x y cont => Expr.let_ (op2 (OpCode.xor Ty.bool) x y) fun (r, _) => cont (Arg.var r))
      (fun a' b' a b cont m' ha' hb' hpre => by
        rw [wp_let, op2_wp_eq, OpCode.wp_xor, ha', hb']; exact hpre _ rfl)
      (fun n hsn a' b' a b cont m' ha' hb' hpre =>
        legalBitsArith_wp target hsn (OpCode.add (Ty.bits n)) trivial a' b' a b ha' hb'
          (by dsimp only [Op.wp, vals]; rw [OpCode.wp_add]; simpa [lift2] using hpre))
      hsupp ha hb hw hk
  | sub t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_3]
    exact legalOp_intBin_wp target hG OpCode.sub (fun {n} x1 x2 => x1 - x2) (fun x1 x2 => x1 ^^ x2)
      (fun u x y p => OpCode.wp_sub u (x, y, ()) p) (fun _ => rfl)
      (fun x y cont => Expr.let_ (op2 (OpCode.xor Ty.bool) x y) fun (r, _) => cont (Arg.var r))
      (fun a' b' a b cont m' ha' hb' hpre => by
        rw [wp_let, op2_wp_eq, OpCode.wp_xor, ha', hb']; exact hpre _ rfl)
      (fun n hsn a' b' a b cont m' ha' hb' hpre =>
        legalBitsArith_wp target hsn (OpCode.sub (Ty.bits n)) trivial a' b' a b ha' hb'
          (by dsimp only [Op.wp, vals]; rw [OpCode.wp_sub]; simpa [lift2] using hpre))
      hsupp ha hb hw hk
  | mul t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_4]
    exact legalOp_intBin_wp target hG OpCode.mul (fun {n} x1 x2 => x1 * x2) (fun x1 x2 => x1 && x2)
      (fun u x y p => OpCode.wp_mul u (x, y, ()) p) (fun _ => rfl)
      (fun x y cont => Expr.let_ (op2 (OpCode.and Ty.bool) x y) fun (r, _) => cont (Arg.var r))
      (fun a' b' a b cont m' ha' hb' hpre => by
        rw [wp_let, op2_wp_eq, OpCode.wp_and, ha', hb']; exact hpre _ rfl)
      (fun n hsn a' b' a b cont m' ha' hb' hpre =>
        legalBitsArith_wp target hsn (OpCode.mul (Ty.bits n)) trivial a' b' a b ha' hb'
          (by dsimp only [Op.wp, vals]; rw [OpCode.wp_mul]; simpa [lift2] using hpre))
      hsupp ha hb hw hk
  | neg t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_neg] at hw
    rw [legalOp.eq_5]
    cases hf : t.hasFloat
    · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      refine legalUnaryTree_wp target OpCode.neg (fun u => target.vecIntOpSupported (OpCode.neg u) u false)
        (fun x cont => cont x)
        (fun n x cont => if (n == 0) = true then cont (Arg.imm 0#(target.widenWidth n)) else
          Expr.let_ (op1 (OpCode.neg (Ty.bits (target.widenWidth n))) x) fun (r, _) =>
            emitMaskToN n (target.widenWidth n) (Arg.var r) cont)
        (fun _ _ _ => Expr.hlt)
        (onB := fun a q => q a) (onBi := fun _ a q => q (-a)) (onF := fun _ _ _ => False)
        ?_ ?_ (fun _ _ _ _ _ _ _ h => False.elim h)
        ?_ (fun _ _ _ hpq h => hpq _ h) (fun _ _ _ _ hpq h => hpq _ h) (fun _ _ _ _ _ h => False.elim h)
        t hsupp (legalArg target a₂) a₁.val (valsTup_legalArg target hG ha) (fun res => k (res, ())) m
        (opWp_treeRel1_lift1_noFloat (fun {n} x => -x) id t hf _ _
          fun fres hfres => hk _ _ (TRel.cons hfres TRel.nil) hw)
      · intro x' x cont m' hx' hpre; exact hpre x' hx'
      · intro n hsn x' x cont m' hx' hpre
        have hs := opWp_widen_spec hv hsn
        dsimp only at hs ⊢
        by_cases hn0 : n = 0
        · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
          apply hpre (Arg.imm 0#(target.widenWidth 0))
          have h0 : (-x : BitVec 0) = 0#0 := Subsingleton.elim _ _
          rw [Arg.val_imm, h0]; apply BitVec.eq_of_toNat_eq; simp
        · simp only [beq_iff_eq, hn0, ↓reduceIte]
          rw [wp_let, op1_wp_eq, OpCode.wp_neg]; dsimp only
          have hbf : (Ty.bits (target.widenWidth n)).hasFloat = false := rfl
          simp only [hbf, Bool.false_eq_true, ↓reduceIte]
          refine emitMaskToN_wp hs.2.1 rfl fun r hr => ?_
          simp only [Arg.val_var, lift1] at hr
          apply hpre r
          rw [hr, hx', opWp_setWidth_neg hs.2.1 x]
      · intro u _ _ _ x p htr
        have hu := opWp_lift1_noFloat_of_treeRel1 (fun {n} x => -x) id u x p htr
        rw [OpCode.wp_neg]; simp [hu.1, hu.2]
    · simp [hf] at hw
  | and t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_6]
    exact legalOp_bitwiseBin_wp target hG OpCode.and (fun {n} x1 x2 => x1 &&& x2) (fun x1 x2 => x1 && x2)
      (fun u x y p => OpCode.wp_and u (x, y, ()) p) (fun _ => rfl) (fun _ => trivial) hsupp ha hb hw hk
  | or t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_7]
    exact legalOp_bitwiseBin_wp target hG OpCode.or (fun {n} x1 x2 => x1 ||| x2) (fun x1 x2 => x1 || x2)
      (fun u x y p => OpCode.wp_or u (x, y, ()) p) (fun _ => rfl) (fun _ => trivial) hsupp ha hb hw hk
  | xor t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_8]
    exact legalOp_bitwiseBin_wp target hG OpCode.xor (fun {n} x1 x2 => x1 ^^^ x2) (fun x1 x2 => x1 ^^ x2)
      (fun u x y p => OpCode.wp_xor u (x, y, ()) p) (fun _ => rfl) (fun _ => trivial) hsupp ha hb hw hk
  | not t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_not] at hw
    rw [legalOp.eq_9]
    refine legalUnaryTree_wp target OpCode.not (fun u => target.vecIntOpSupported (OpCode.not u) u false)
      (fun x cont => Expr.let_ (op1 (OpCode.not Ty.bool) x) fun (r, _) => cont (Arg.var r))
      (fun n x cont =>
        let w := target.widenWidth n
        if (n == 0) = true then cont (Arg.imm 0#w)
        else if (n == w) = true then Expr.let_ (op1 (OpCode.not (Ty.bits w)) x) fun (r, _) => cont (Arg.var r)
        else Expr.let_ (op1 (OpCode.not (Ty.bits w)) x) fun (r, _) => emitMaskToN n w (Arg.var r) cont)
      (fun fmt x cont =>
        if target.scalarFloatBitwise = true then Expr.let_ (op1 (OpCode.not (Ty.float fmt)) x) fun (r, _) => cont (Arg.var r)
        else
          let fw := fmt.width
          Expr.let_ (op1 (OpCode.bitcast (Ty.float fmt) (Ty.bits fw) rfl) x) fun (bx, _) =>
            Expr.let_ (op1 (OpCode.not (Ty.bits fw)) (Arg.var bx)) fun (br, _) =>
              Expr.let_ (op1 (OpCode.bitcast (Ty.bits fw) (Ty.float fmt) rfl) (Arg.var br)) fun (r, _) =>
                cont (Arg.var r))
      (onB := fun a q => q (!a)) (onBi := fun _ a q => q (~~~a)) (onF := fun _ a q => q (~~~a))
      ?_ ?_ ?_ ?_ (fun _ _ _ hpq h => hpq _ h) (fun _ _ _ _ hpq h => hpq _ h) (fun _ _ _ _ hpq h => hpq _ h)
      t hsupp (legalArg target a₂) a₁.val (valsTup_legalArg target hG ha) (fun res => k (res, ())) m
      (opWp_treeRel1_lift1 (fun {n} x => ~~~x) (fun x => !x) (fun _ a q => q (~~~a))
        (fun _ _ _ h => h) t _ _ fun fres hfres => hk _ _ (TRel.cons hfres TRel.nil) hw)
    · intro x' x cont m' hx' hpre
      rw [wp_let, op1_wp_eq, OpCode.wp_not, hx']; exact hpre _ rfl
    · intro n hsn x' x cont m' hx' hpre
      have hs := opWp_widen_spec hv hsn
      dsimp only at hs ⊢
      by_cases hn0 : n = 0
      · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
        apply hpre (Arg.imm 0#(target.widenWidth 0))
        have h0 : (~~~x : BitVec 0) = 0#0 := Subsingleton.elim _ _
        rw [Arg.val_imm, h0]; apply BitVec.eq_of_toNat_eq; simp
      · simp only [beq_iff_eq, hn0, ↓reduceIte]
        split
        · next hnw =>
          rw [wp_let, op1_wp_eq, OpCode.wp_not]; dsimp only
          simp only [lift1]
          refine hpre _ ?_
          simp only [Arg.val_var]
          exact op1_setWidth_self (op := fun {k} (x : BitVec k) => ~~~x) hnw hx'
        · next _ =>
          rw [wp_let, op1_wp_eq, OpCode.wp_not]; dsimp only
          refine emitMaskToN_wp hs.2.1 rfl fun r hr => ?_
          simp only [Arg.val_var, lift1] at hr
          apply hpre r; rw [hr, hx', opWp_not_setWidth hs.2.1 x]
    · intro fmt _ x' x cont m' hx' hpre
      dsimp only
      split
      · rw [wp_let, op1_wp_eq, OpCode.wp_not, hx']; exact hpre _ rfl
      · rw [wp_let, op1_wp_eq, OpCode.wp_bitcast, wp_let, op1_wp_eq, OpCode.wp_not,
          wp_let, op1_wp_eq, OpCode.wp_bitcast]
        apply hpre (Arg.var _)
        simp only [Arg.val_var, toBits, ofBits, lift1, BitVec.cast_eq]
        rw [hx']
    · intro u _ _ _ x p htr
      rw [OpCode.wp_not]
      exact opWp_lift1_of_treeRel1 (fun {n} x => ~~~x) (fun x => !x) (fun _ a q => q (~~~a))
        (fun _ _ _ h => h) (fun _ _ _ _ hpq h => hpq _ h) u x p htr
  | ternlog t imm =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_ternlog] at hw
    rw [legalOp.eq_10]
    refine legalTernaryTree_wp target (fun u => OpCode.ternlog u imm)
      (fun u => target.vecIntOpSupported (OpCode.ternlog u imm) u false)
      (fun x y z cont => emitTernlogBool x y z imm cont)
      (fun n x y z cont =>
        let w := target.widenWidth n
        if (n == 0) = true then cont (Arg.imm 0#w)
        else if target.scalarTernlog = true then
          Expr.let_ (op3 (OpCode.ternlog (Ty.bits w) imm) x y z) fun (r, _) => emitMaskToN n w (Arg.var r) cont
        else emitTernlogBits w x y z imm fun r => emitMaskToN n w r cont)
      (fun fmt x y z cont =>
        if (target.scalarFloatBitwise && target.scalarTernlog) = true then
          Expr.let_ (op3 (OpCode.ternlog (Ty.float fmt) imm) x y z) fun (r, _) => cont (Arg.var r)
        else
          let fw := fmt.width
          Expr.let_ (op1 (OpCode.bitcast (Ty.float fmt) (Ty.bits fw) rfl) x) fun (bx, _) =>
            Expr.let_ (op1 (OpCode.bitcast (Ty.float fmt) (Ty.bits fw) rfl) y) fun (by_, _) =>
              Expr.let_ (op1 (OpCode.bitcast (Ty.float fmt) (Ty.bits fw) rfl) z) fun (bz, _) =>
                (if target.scalarTernlog = true then fun cc =>
                  Expr.let_ (op3 (OpCode.ternlog (Ty.bits fw) imm) (Arg.var bx) (Arg.var by_) (Arg.var bz))
                    fun (br, _) => cc (Arg.var br)
                else emitTernlogBits fw (Arg.var bx) (Arg.var by_) (Arg.var bz) imm) fun br =>
                  Expr.let_ (op1 (OpCode.bitcast (Ty.bits fw) (Ty.float fmt) rfl) br) fun (r, _) =>
                    cont (Arg.var r))
      (onB := fun a b c q => q (ternaryLogicBool a b c imm))
      (onBi := fun _ a b c q => q (ternaryLogic a b c imm))
      (onF := fun _ a b c q => q (ternaryLogic a b c imm))
      ?_ ?_ ?_ ?_ (fun _ _ _ _ _ hpq h => hpq _ h) (fun _ _ _ _ _ _ hpq h => hpq _ h) (fun _ _ _ _ _ _ hpq h => hpq _ h)
      t hsupp (legalArg target a₂) (legalArg target b₂) (legalArg target c₂) a₁.val b₁.val c₁.val
      (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb) (valsTup_legalArg target hG hc')
      (fun res => k (res, ())) m
      (opWp_treeRel3_lift3 (fun {n} x y z => ternaryLogic x y z imm)
        (fun x y z => ternaryLogicBool x y z imm) t _ _ _ _
        fun fres hfres => hk _ _ (TRel.cons hfres TRel.nil) hw)
    · intro a' b' c' a b c cont m' ha' hb' hc'' hpre
      exact emitTernlogBool_wp a' b' c' imm fun r hr => hpre r (by simpa [ha', hb', hc''] using hr)
    · intro n hsn a' b' c' a b c cont m' ha' hb' hc'' hpre
      have hs := opWp_widen_spec hv hsn
      dsimp only at hs ⊢
      by_cases hn0 : n = 0
      · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
        apply hpre (Arg.imm 0#(target.widenWidth 0))
        have h0 : ternaryLogic a b c imm = 0#0 := Subsingleton.elim _ _
        rw [Arg.val_imm, h0]; apply BitVec.eq_of_toNat_eq; simp
      · simp only [beq_iff_eq, hn0, ↓reduceIte]
        split
        · rw [wp_let, op3_wp_eq, OpCode.wp_ternlog]; dsimp only
          refine emitMaskToN_wp hs.2.1 rfl fun r hr => ?_
          simp only [Arg.val_var, lift3] at hr
          apply hpre r; rw [hr, ha', hb', hc'']
          exact congrArg (BitVec.setWidth _) (opWp_ternaryLogic_setWidth hs.2.1 a b c imm)
        · refine emitTernlogBits_wp a' b' c' imm fun r1 hr1 =>
            emitMaskToN_wp hs.2.1 rfl fun r hr => ?_
          apply hpre r; rw [hr, hr1, ha', hb', hc'']
          exact congrArg (BitVec.setWidth _) (opWp_ternaryLogic_setWidth hs.2.1 a b c imm)
    · intro fmt _ a' b' c' a b c cont m' ha' hb' hc'' hpre
      dsimp only
      split
      · rw [wp_let, op3_wp_eq, OpCode.wp_ternlog, ha', hb', hc'']
        exact hpre _ rfl
      · rw [wp_let, op1_wp_eq, OpCode.wp_bitcast, wp_let, op1_wp_eq, OpCode.wp_bitcast,
          wp_let, op1_wp_eq, OpCode.wp_bitcast]
        split
        · rw [wp_let, op3_wp_eq, OpCode.wp_ternlog, wp_let, op1_wp_eq, OpCode.wp_bitcast]
          apply hpre (Arg.var _)
          simp only [Arg.val_var, toBits, ofBits, lift3, BitVec.cast_eq]
          rw [ha', hb', hc'']
        · refine emitTernlogBits_wp _ _ _ imm fun br hbr => ?_
          rw [wp_let, op1_wp_eq, OpCode.wp_bitcast]
          apply hpre (Arg.var _)
          simp only [Arg.val_var, toBits, ofBits, BitVec.cast_eq] at hbr ⊢
          rw [hbr, ha', hb', hc'']
    · intro u _ _ _ x y z p htr
      rw [OpCode.wp_ternlog]
      exact opWp_lift3_of_treeRel3 (fun {n} x y z => ternaryLogic x y z imm)
        (fun x y z => ternaryLogicBool x y z imm) u x y z p htr
  | shl t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_11]
    exact legalOp_shiftBin_wp target hG OpCode.shl (fun {n} x y => x <<< (y.toNat % n))
      (fun u x y p => OpCode.wp_shl u (x, y, ()) p)
      (fun n hsn a' b' a b cont m' ha' hb' hpre =>
        legalBitsArith_wp target hsn (OpCode.shl (Ty.bits n)) trivial a' b' a b ha' hb'
          (by dsimp only [Op.wp, vals]; rw [OpCode.wp_shl]; simpa [lift2] using hpre))
      (fun _ _ _ _ hsk => by cases hsk)
      (fun u c w s _ hunif x => opWp_shl_uniformShift u c w s hunif x)
      hsupp ha hb hw hk
  | lshr t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_12]
    exact legalOp_shiftBin_wp target hG OpCode.lshr (fun {n} x y => x >>> (y.toNat % n))
      (fun u x y p => OpCode.wp_lshr u (x, y, ()) p)
      (fun n hsn a' b' a b cont m' ha' hb' hpre =>
        legalBitsArith_wp target hsn (OpCode.lshr (Ty.bits n)) trivial a' b' a b ha' hb'
          (by dsimp only [Op.wp, vals]; rw [OpCode.wp_lshr]; simpa [lift2] using hpre))
      (fun _ _ _ _ hsk => by cases hsk) (fun _ _ _ _ hsk => by cases hsk)
      hsupp ha hb hw hk
  | ashr t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_13]
    exact legalOp_shiftBin_wp target hG OpCode.ashr (fun {n} x y => x.sshiftRight (y.toNat % n))
      (fun u x y p => OpCode.wp_ashr u (x, y, ()) p)
      (fun n hsn a' b' a b cont m' ha' hb' hpre =>
        legalBitsArith_wp target hsn (OpCode.ashr (Ty.bits n)) trivial a' b' a b ha' hb'
          (by dsimp only [Op.wp, vals]; rw [OpCode.wp_ashr]; simpa [lift2] using hpre))
      (fun _ _ _ _ hsk => by cases hsk) (fun _ _ _ _ hsk => by cases hsk)
      hsupp ha hb hw hk
  | rotl t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_14]
    exact legalOp_shiftBin_wp target hG OpCode.rotl (fun {n} x y => x.rotateLeft (y.toNat % n))
      (fun u x y p => OpCode.wp_rotl u (x, y, ()) p)
      (fun n hsn a' b' a b cont m' ha' hb' hpre =>
        legalBitsArith_wp target hsn (OpCode.rotl (Ty.bits n)) trivial a' b' a b ha' hb'
          (by dsimp only [Op.wp, vals]; rw [OpCode.wp_rotl]; simpa [lift2] using hpre))
      (fun u c w s _ hunif x => opWp_rotl_uniformShift u c w s hunif x)
      (fun _ _ _ _ hsk => by cases hsk)
      hsupp ha hb hw hk
  | rotr t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_15]
    exact legalOp_shiftBin_wp target hG OpCode.rotr (fun {n} x y => x.rotateRight (y.toNat % n))
      (fun u x y p => OpCode.wp_rotr u (x, y, ()) p)
      (fun n hsn a' b' a b cont m' ha' hb' hpre =>
        legalBitsArith_wp target hsn (OpCode.rotr (Ty.bits n)) trivial a' b' a b ha' hb'
          (by dsimp only [Op.wp, vals]; rw [OpCode.wp_rotr]; simpa [lift2] using hpre))
      (fun _ _ _ _ hsk => by cases hsk) (fun _ _ _ _ hsk => by cases hsk)
      hsupp ha hb hw hk
  | fshl n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_fshl] at hw
    rw [legalOp.eq_16]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    have hc_val := valsTup_legalArg target hG hc'
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩
    rcases hpc : legalArg target c₂ with ⟨c', ⟨⟩⟩
    rw [hpa] at ha_val; rw [hpb] at hb_val; rw [hpc] at hc_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hceq : c'.val = BitVec.setWidth (target.widenWidth n) c₁.val := (Prod.mk.inj hc_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      change (0#(target.widenWidth 0), ()) = (BitVec.setWidth (target.widenWidth 0) _, ())
      have h0 : BitVec.extractLsb' 0 0 ((a₁.val ++ b₁.val) <<< (c₁.val.toNat % 0)) = 0#0 := Subsingleton.elim _ _
      rw [h0]; congr 1
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op3_wp_eq, OpCode.wp_fshl]; dsimp only
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1
        exact op3_setWidth_self (op := fun {k} (x y z : BitVec k) => BitVec.extractLsb' k k ((x ++ y) <<< (z.toNat % k)))
          hnw haeq hbeq hceq
      · next hnw =>
        have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
        have hn_lt : n < target.widenWidth n := Nat.lt_of_le_of_ne hs.2.1 hnw
        refine emitCountMod_wp hn_pos hn_lt hceq fun cm hcm => ?_
        rw [wp_let, op2_wp_eq, OpCode.wp_sub, wp_let, op2_wp_eq, OpCode.wp_shl,
          wp_let, op2_wp_eq, OpCode.wp_lshr, wp_let, op2_wp_eq, OpCode.wp_or]
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine emitMaskToN_wp hs.2.1 rfl fun r hr => ?_
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (r.val, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1
        rw [hr]
        congr 1
        simp only [Arg.val_var, Arg.val_imm, lift2, haeq, hbeq, hcm]
        have hnw2 : target.widenWidth n < 2 ^ target.widenWidth n := Nat.lt_two_pow_self
        have hn2w : n < 2 ^ target.widenWidth n := Nat.lt_trans hn_lt hnw2
        have hcn2w : c₁.val.toNat % n < 2 ^ target.widenWidth n := Nat.lt_trans (Nat.mod_lt _ hn_pos) hn2w
        have hm1 : (BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat % target.widenWidth n =
            c₁.val.toNat % n := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcn2w, Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hn_pos) hn_lt)]
        have hm2 : (BitVec.ofNat (target.widenWidth n) n -
            BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat % target.widenWidth n =
            (BitVec.ofNat (target.widenWidth n) n -
              BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat := by
          apply Nat.mod_eq_of_lt
          rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt hn2w, Nat.mod_eq_of_lt hcn2w]
          have : c₁.val.toNat % n < n := Nat.mod_lt _ hn_pos
          rw [← Nat.sub_add_comm (Nat.le_of_lt hcn2w), Nat.add_sub_assoc (Nat.le_of_lt this),
            Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
          omega
        change BitVec.setWidth n
          ((BitVec.setWidth (target.widenWidth n) a₁.val <<<
              ((BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat % target.widenWidth n)) |||
           (BitVec.setWidth (target.widenWidth n) b₁.val >>>
              ((BitVec.ofNat (target.widenWidth n) n - BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat %
                target.widenWidth n))) = _
        rw [hm1, hm2]
        have hres := opWp_fshl_widened hn_pos hn_lt a₁.val b₁.val c₁.val
        have hs_bv : (BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat = c₁.val.toNat % n := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcn2w]
        have hsl_eq : ∀ (x y : BitVec (target.widenWidth n)), x <<< y = x <<< y.toNat := fun _ _ => rfl
        have hsr_eq : ∀ (x y : BitVec (target.widenWidth n)), x >>> y = x >>> y.toNat := fun _ _ => rfl
        rw [hsl_eq, hsr_eq, hs_bv] at hres
        exact hres
  | fshr n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_fshr] at hw
    rw [legalOp.eq_17]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    have hc_val := valsTup_legalArg target hG hc'
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩
    rcases hpc : legalArg target c₂ with ⟨c', ⟨⟩⟩
    rw [hpa] at ha_val; rw [hpb] at hb_val; rw [hpc] at hc_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hceq : c'.val = BitVec.setWidth (target.widenWidth n) c₁.val := (Prod.mk.inj hc_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      change (0#(target.widenWidth 0), ()) = (BitVec.setWidth (target.widenWidth 0) _, ())
      have h0 : BitVec.extractLsb' 0 0 ((a₁.val ++ b₁.val) >>> (c₁.val.toNat % 0)) = 0#0 := Subsingleton.elim _ _
      rw [h0]; congr 1
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op3_wp_eq, OpCode.wp_fshr]; dsimp only
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1
        exact op3_setWidth_self (op := fun {k} (x y z : BitVec k) => BitVec.extractLsb' 0 k ((x ++ y) >>> (z.toNat % k)))
          hnw haeq hbeq hceq
      · next hnw =>
        have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
        have hn_lt : n < target.widenWidth n := Nat.lt_of_le_of_ne hs.2.1 hnw
        refine emitCountMod_wp hn_pos hn_lt hceq fun cm hcm => ?_
        rw [wp_let, op2_wp_eq, OpCode.wp_sub, wp_let, op2_wp_eq, OpCode.wp_lshr,
          wp_let, op2_wp_eq, OpCode.wp_shl, wp_let, op2_wp_eq, OpCode.wp_or]
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine emitMaskToN_wp hs.2.1 rfl fun r hr => ?_
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (r.val, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1; rw [hr]; congr 1
        simp only [Arg.val_var, Arg.val_imm, lift2, haeq, hbeq, hcm]
        have hnw2 : target.widenWidth n < 2 ^ target.widenWidth n := Nat.lt_two_pow_self
        have hn2w : n < 2 ^ target.widenWidth n := Nat.lt_trans hn_lt hnw2
        have hcn2w : c₁.val.toNat % n < 2 ^ target.widenWidth n := Nat.lt_trans (Nat.mod_lt _ hn_pos) hn2w
        have hm1 : (BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat % target.widenWidth n =
            c₁.val.toNat % n := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcn2w, Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hn_pos) hn_lt)]
        have hm2 : (BitVec.ofNat (target.widenWidth n) n -
            BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat % target.widenWidth n =
            (BitVec.ofNat (target.widenWidth n) n -
              BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat := by
          apply Nat.mod_eq_of_lt
          rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt hn2w, Nat.mod_eq_of_lt hcn2w]
          have : c₁.val.toNat % n < n := Nat.mod_lt _ hn_pos
          rw [← Nat.sub_add_comm (Nat.le_of_lt hcn2w), Nat.add_sub_assoc (Nat.le_of_lt this),
            Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
          omega
        change BitVec.setWidth n
          ((BitVec.setWidth (target.widenWidth n) b₁.val >>>
              ((BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat % target.widenWidth n)) |||
           (BitVec.setWidth (target.widenWidth n) a₁.val <<<
              ((BitVec.ofNat (target.widenWidth n) n - BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat %
                target.widenWidth n))) = _
        rw [hm1, hm2]
        have hres := opWp_fshr_widened hn_pos hn_lt a₁.val b₁.val c₁.val
        have hs_bv : (BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat = c₁.val.toNat % n := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcn2w]
        have hsl_eq : ∀ (x y : BitVec (target.widenWidth n)), x <<< y = x <<< y.toNat := fun _ _ => rfl
        have hsr_eq : ∀ (x y : BitVec (target.widenWidth n)), x >>> y = x >>> y.toNat := fun _ _ => rfl
        rw [hsr_eq, hsl_eq, hs_bv] at hres
        exact hres
  | bswap t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_bswap] at hw
    cases hbs : t.bswapOk
    · simp [hbs] at hw
    · simp only [hbs, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw
      rw [legalOp.eq_18]
      exact legalBswapTree_wp target hv t hsupp hbs (legalArg target a₂) a₁.val
        (valsTup_legalArg target hG ha) fun res hres => hk _ _ (TRel.cons hres TRel.nil) hw
  | clz n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_clz] at hw
    rw [legalOp.eq_19]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      have h0 : a₁.val.clz = 0#0 := Subsingleton.elim _ _
      change (0#(target.widenWidth 0), ()) = (BitVec.setWidth (target.widenWidth 0) a₁.val.clz, ())
      rw [h0]; congr 1
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op1_wp_eq, OpCode.wp_clz]; dsimp only
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (a'.val.clz, ()) = (BitVec.setWidth (target.widenWidth n) a₁.val.clz, ())
        congr 1; exact op1_setWidth_self hnw haeq
      · next hnw =>
        rw [wp_let, op1_wp_eq, OpCode.wp_clz, wp_let, op2_wp_eq, OpCode.wp_sub]
        dsimp only
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (_, ()) = (BitVec.setWidth (target.widenWidth n) a₁.val.clz, ())
        congr 1
        simp only [Arg.val_var, Arg.val_imm, lift2, haeq]
        exact opWp_clz_widened (Nat.pos_of_ne_zero hn0) (Nat.lt_of_le_of_ne hs.2.1 hnw) a₁.val
  | cls n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_cls] at hw
    rw [legalOp.eq_20]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      have h0 : ((if a₁.val.msb = true then (~~~a₁.val).clz else a₁.val.clz) - 1#0) = 0#0 := Subsingleton.elim _ _
      change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
      rw [h0]; congr 1
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op1_wp_eq, OpCode.wp_cls]; dsimp only
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1
        exact op1_setWidth_self (op := fun {k} (x : BitVec k) => (if x.msb = true then (~~~x).clz else x.clz) - 1#k)
          hnw haeq
      · next hnw =>
        have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
        have hn_lt : n < target.widenWidth n := Nat.lt_of_le_of_ne hs.2.1 hnw
        refine emitSextToW_wp hn_pos hs.2.1 haeq fun sa hsa => ?_
        rw [wp_let, op1_wp_eq, OpCode.wp_cls, wp_let, op2_wp_eq, OpCode.wp_sub]
        dsimp only
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1
        simp only [Arg.val_var, Arg.val_imm, lift2, hsa]
        exact opWp_cls_widened hn_pos hn_lt a₁.val
  | rbit n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_rbit] at hw
    rw [legalOp.eq_21]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      have h0 : a₁.val.reverse = 0#0 := Subsingleton.elim _ _
      change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
      rw [h0]; congr 1
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op1_wp_eq, OpCode.wp_rbit]; dsimp only
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1; exact op1_setWidth_self hnw haeq
      · next hnw =>
        rw [wp_let, op1_wp_eq, OpCode.wp_rbit, wp_let, op2_wp_eq, OpCode.wp_lshr]
        dsimp only
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1
        simp only [Arg.val_var, Arg.val_imm, lift2, haeq]
        have hnw2 : target.widenWidth n < 2 ^ target.widenWidth n := Nat.lt_two_pow_self
        have hmod : (BitVec.ofNat (target.widenWidth n) (target.widenWidth n - n)).toNat % target.widenWidth n =
            target.widenWidth n - n := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hnw2),
            Nat.mod_eq_of_lt (by omega)]
        rw [hmod]
        exact opWp_rbit_widened (Nat.pos_of_ne_zero hn0) (Nat.lt_of_le_of_ne hs.2.1 hnw) a₁.val
  | ctz n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_ctz] at hw
    rw [legalOp.eq_22]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      have h0 : a₁.val.reverse.clz = 0#0 := Subsingleton.elim _ _
      change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
      rw [h0]; congr 1
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op1_wp_eq, OpCode.wp_ctz]; dsimp only
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1
        exact op1_setWidth_self (op := fun {k} (x : BitVec k) => x.reverse.clz) hnw haeq
      · next hnw =>
        rw [wp_let, op2_wp_eq, OpCode.wp_or, wp_let, op1_wp_eq, OpCode.wp_ctz]
        dsimp only
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1
        simp only [Arg.val_var, Arg.val_imm, lift2, haeq]
        exact opWp_ctz_widened (Nat.pos_of_ne_zero hn0) (Nat.lt_of_le_of_ne hs.2.1 hnw) a₁.val
  | popcnt n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_popcnt] at hw
    rw [legalOp.eq_23]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      have h0 : a₁.val.cpop = 0#0 := Subsingleton.elim _ _
      change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
      rw [h0]; congr 1
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      rw [wp_let, op1_wp_eq, OpCode.wp_popcnt]; dsimp only
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      change (_, ()) = (BitVec.setWidth (target.widenWidth n) a₁.val.cpop, ())
      congr 1; rw [haeq]; exact opWp_popcnt_widened hs.2.1 a₁.val
  | cmp o t m_ty hm =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    cases hm
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_cmp] at hw
    rw [legalOp.eq_24]
    cases hf : t.hasFloat
    · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      exact legalCmpTree_wp target o t hsupp hf (legalArg target a₂) (legalArg target b₂)
        a₁.val b₁.val (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb)
        (fun res => k (res, ())) m
        (fun res hres => hk (liftCmp (fun {n} => o.evalBits) o.evalBool t a₁.val b₁.val, ())
          (res, ()) (TRel.cons hres TRel.nil) hw)
    · simp [hf] at hw
  | select t =>
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_select] at hw
    rw [legalOp.eq_25]
    have hc_val := valsTup_legalArg target hG hc'
    rcases hpc : legalArg target c₂ with ⟨c', ⟨⟩⟩; rw [hpc] at hc_val
    have hceq : c'.val = c₁.val := (Prod.mk.inj hc_val).1
    exact legalSelectTree_wp target c' c₁.val hceq t hsupp (legalArg target a₂) (legalArg target b₂)
      a₁.val b₁.val (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb)
      (fun res => k (res, ())) m
      (fun res hres => hk _ _ (TRel.cons hres TRel.nil) hw)
  | blend t m_ty hm =>
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    cases hm
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_blend] at hw
    rw [legalOp.eq_26]
    exact legalBlendTree_wp target t hsupp (legalArg target c₂) (legalArg target a₂) (legalArg target b₂)
      c₁.val a₁.val b₁.val (valsTup_legalArg target hG hc') (valsTup_legalArg target hG ha)
      (valsTup_legalArg target hG hb) (fun res => k (res, ())) m
      (fun res hres => hk _ _ (TRel.cons hres TRel.nil) hw)
  | zext m' n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_zext] at hw
    rcases hw with ⟨hmn, hwP⟩
    rw [legalOp.eq_27]
    simp only [Nat.not_lt.mpr hmn, ↓reduceIte]
    have ha_val := valsTup_legalArg target hG ha
    split
    · next a' hpa =>
      dsimp only [Tup, LVar, LegalTarget.legalTys] at k ha_val ⊢
      rw [hpa] at ha_val
      have haeq : a'.val = BitVec.setWidth (target.widenWidth m') a₁.val := (Prod.mk.inj ha_val).1
      dsimp only [LegalTarget.supportsOpCode] at hsupp
      simp only [Bool.and_eq_true] at hsupp
      have hsm := opWp_widen_spec hv hsupp.1
      have hsn := opWp_widen_spec hv hsupp.2
      have hmono := opWp_widen_mono hv hsupp.1 hsupp.2 hmn
      by_cases hm0 : m' = 0
      · subst hm0; simp only [beq_self_eq_true, ↓reduceIte]
        refine hk _ _ (TRel.cons ?_ TRel.nil) hwP
        have ha0 : a₁.val = 0#0 := Subsingleton.elim _ _
        change (0#(target.widenWidth n), ()) = (BitVec.setWidth (target.widenWidth n) (BitVec.setWidth n a₁.val), ())
        rw [ha0]; congr 1; apply BitVec.eq_of_toNat_eq; simp
      · simp only [beq_iff_eq, hm0, ↓reduceIte]
        by_cases heqw : target.widenWidth m' = target.widenWidth n
        · simp only [heqw, ↓reduceDIte]
          refine hk _ _ (TRel.cons ?_ TRel.nil) hwP
          change ((castArgBits heqw a').val, ()) = (BitVec.setWidth (target.widenWidth n) (BitVec.setWidth n a₁.val), ())
          rw [val_castArgBits]
          congr 1
          apply BitVec.eq_of_toNat_eq
          have hp1 : 2 ^ m' ≤ 2 ^ target.widenWidth m' := Nat.pow_le_pow_right (by omega) hsm.2.1
          have hp2 : 2 ^ m' ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hmn
          have hp3 : 2 ^ n ≤ 2 ^ target.widenWidth n := Nat.pow_le_pow_right (by omega) hsn.2.1
          rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt hp2),
            Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt (Nat.le_trans hp2 hp3))]
          have hcast : ∀ (k : Nat) (hk : target.widenWidth m' = k) (v : BitVec (target.widenWidth m')),
              (hk ▸ v).toNat = v.toNat := by intro k hk v; subst hk; rfl
          rw [hcast _ heqw a'.val, haeq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt hp1)]
        · have hltw : target.widenWidth m' < target.widenWidth n := Nat.lt_of_le_of_ne hmono heqw
          simp only [heqw, ↓reduceDIte, hltw, ↓reduceIte]
          rw [wp_let, op1_wp_eq, OpCode.wp_zext]; refine ⟨Nat.le_of_lt hltw, ?_⟩
          refine hk _ _ (TRel.cons ?_ TRel.nil) hwP
          dsimp only [Arg.val]
          change (BitVec.setWidth (target.widenWidth n) a'.val, ()) =
            (BitVec.setWidth (target.widenWidth n) (BitVec.setWidth n a₁.val), ())
          congr 1; apply BitVec.eq_of_toNat_eq
          have hp1 : 2 ^ m' ≤ 2 ^ target.widenWidth m' := Nat.pow_le_pow_right (by omega) hsm.2.1
          have hp2 : 2 ^ m' ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hmn
          have hp3 : 2 ^ n ≤ 2 ^ target.widenWidth n := Nat.pow_le_pow_right (by omega) hsn.2.1
          have hp4 : 2 ^ target.widenWidth m' ≤ 2 ^ target.widenWidth n := Nat.pow_le_pow_right (by omega) hmono
          rw [haeq, BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt hp1),
            Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt (Nat.le_trans hp1 hp4)),
            Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt hp2),
            Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt (Nat.le_trans hp2 hp3))]
  | sext m' n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_sext] at hw
    rcases hw with ⟨hmn, hwP⟩
    rw [legalOp.eq_28]
    simp only [Nat.not_lt.mpr hmn, ↓reduceIte]
    have ha_val := valsTup_legalArg target hG ha
    split
    · next a' hpa =>
      dsimp only [Tup, LVar, LegalTarget.legalTys] at k ha_val ⊢
      rw [hpa] at ha_val
      have haeq : a'.val = BitVec.setWidth (target.widenWidth m') a₁.val := (Prod.mk.inj ha_val).1
      dsimp only [LegalTarget.supportsOpCode] at hsupp
      simp only [Bool.and_eq_true] at hsupp
      have hsm := opWp_widen_spec hv hsupp.1
      have hsn := opWp_widen_spec hv hsupp.2
      have hmono := opWp_widen_mono hv hsupp.1 hsupp.2 hmn
      by_cases hm0 : m' = 0
      · subst hm0; simp only [beq_self_eq_true, ↓reduceIte]
        refine hk _ _ (TRel.cons ?_ TRel.nil) hwP
        have ha0 : a₁.val = 0#0 := Subsingleton.elim _ _
        change (0#(target.widenWidth n), ()) = (BitVec.setWidth (target.widenWidth n) (BitVec.signExtend n a₁.val), ())
        rw [ha0]
        congr 1; apply BitVec.eq_of_toNat_eq
        rw [BitVec.signExtend_eq_setWidth_of_msb_false (by rfl)]; simp
      · simp only [beq_iff_eq, hm0, ↓reduceIte]
        have hm_pos : 0 < m' := Nat.pos_of_ne_zero hm0
        refine emitSextToW_wp hm_pos hsm.2.1 haeq fun sx hsx => ?_
        have hstep2 : ∀ (cont : Arg Val (Ty.bits (target.widenWidth n)) → _),
            (∀ r : Arg Val (Ty.bits (target.widenWidth n)),
              r.val = BitVec.signExtend (target.widenWidth n) a₁.val → wp Γ Q X (cont r) m) →
            wp Γ Q X (if h : target.widenWidth m' = target.widenWidth n then cont (castArgBits h sx)
              else if target.widenWidth m' < target.widenWidth n then
                Expr.let_ (op1 (OpCode.sext (target.widenWidth m') (target.widenWidth n)) sx) fun (r, _) => cont (Arg.var r)
              else Expr.hlt) m := by
          intro cont hcont
          by_cases heqw : target.widenWidth m' = target.widenWidth n
          · simp only [heqw, ↓reduceDIte]
            apply hcont (castArgBits heqw sx)
            rw [val_castArgBits, hsx]
            apply BitVec.eq_of_getLsbD_eq; intro i hi
            rw [getLsbD_eq_rec heqw, BitVec.getLsbD_signExtend, BitVec.getLsbD_signExtend,
              decide_eq_true hi, decide_eq_true (by rw [heqw]; exact hi)]
          · have hltw : target.widenWidth m' < target.widenWidth n := Nat.lt_of_le_of_ne hmono heqw
            simp only [heqw, ↓reduceDIte, hltw, ↓reduceIte]
            rw [wp_let, op1_wp_eq, OpCode.wp_sext]; refine ⟨Nat.le_of_lt hltw, ?_⟩
            apply hcont (Arg.var _)
            simp only [Arg.val_var]
            rw [hsx]
            apply BitVec.eq_of_getLsbD_eq
            intro i hi
            simp only [BitVec.getLsbD_signExtend, decide_eq_true hi, Bool.true_and]
            by_cases him : i < target.widenWidth m'
            · simp [him]
            · have hlast : target.widenWidth m' - 1 < target.widenWidth m' := by omega
              have hmsb_eq : (BitVec.signExtend (target.widenWidth m') a₁.val).msb = a₁.val.msb := by
                rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_signExtend, decide_eq_true hlast, Bool.true_and]
                by_cases hlastm : target.widenWidth m' - 1 < m'
                · have heqm : target.widenWidth m' - 1 = m' - 1 := by omega
                  simp only [heqm, ← BitVec.msb_eq_getLsbD_last, ite_self]
                · simp only [hlastm, ↓reduceIte]
              have him' : ¬ i < m' := by omega
              simp [him, him', hmsb_eq]
        refine hstep2 (fun r => emitMaskToN n (target.widenWidth n) r fun rm => k ((rm, ()), ())) fun r hr => ?_
        refine emitMaskToN_wp hsn.2.1 rfl fun rm hrm => ?_
        refine hk _ _ (TRel.cons ?_ TRel.nil) hwP
        change (rm.val, ()) = (BitVec.setWidth (target.widenWidth n) (BitVec.signExtend n a₁.val), ())
        congr 1; rw [hrm, hr]; congr 1
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        simp only [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and,
          BitVec.getLsbD_signExtend, decide_eq_true (Nat.lt_of_lt_of_le hi hsn.2.1)]
  | trunc m' n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_trunc] at hw
    rcases hw with ⟨hnm, hwP⟩
    rw [legalOp.eq_29]
    simp only [Nat.not_lt.mpr hnm, ↓reduceIte]
    have ha_val := valsTup_legalArg target hG ha
    split
    · next a' hpa =>
      dsimp only [Tup, LVar, LegalTarget.legalTys] at k ha_val ⊢
      rw [hpa] at ha_val
      have haeq : a'.val = BitVec.setWidth (target.widenWidth m') a₁.val := (Prod.mk.inj ha_val).1
      dsimp only [LegalTarget.supportsOpCode] at hsupp
      simp only [Bool.and_eq_true] at hsupp
      have hsm := opWp_widen_spec hv hsupp.1
      have hsn := opWp_widen_spec hv hsupp.2
      have hmono := opWp_widen_mono hv hsupp.2 hsupp.1 hnm
      by_cases hn0 : n = 0
      · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
        refine hk _ _ (TRel.cons ?_ TRel.nil) hwP
        have h0 : BitVec.setWidth 0 a₁.val = 0#0 := Subsingleton.elim _ _
        change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
        rw [h0]; congr 1
      · simp only [beq_iff_eq, hn0, ↓reduceIte]
        have hstep1 : ∀ (cont : Arg Val (Ty.bits (target.widenWidth n)) → _),
            (∀ r : Arg Val (Ty.bits (target.widenWidth n)),
              BitVec.setWidth n r.val = BitVec.setWidth n a₁.val → wp Γ Q X (cont r) m) →
            wp Γ Q X (if h : target.widenWidth n = target.widenWidth m' then cont (castArgBits h.symm a')
              else if target.widenWidth n < target.widenWidth m' then
                Expr.let_ (op1 (OpCode.trunc (target.widenWidth m') (target.widenWidth n)) a')
                  fun (r, _) => cont (Arg.var r)
              else Expr.hlt) m := by
          intro cont hcont
          by_cases heqw : target.widenWidth n = target.widenWidth m'
          · simp only [heqw, ↓reduceDIte]
            apply hcont (castArgBits heqw.symm a')
            rw [val_castArgBits]
            apply BitVec.eq_of_getLsbD_eq; intro i hi
            have hcast : ∀ (k : Nat) (hk : target.widenWidth m' = k) (v : BitVec (target.widenWidth m')),
                (hk ▸ v).getLsbD i = v.getLsbD i := fun k hk v => getLsbD_eq_rec hk v i
            rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and,
              hcast _ heqw.symm a'.val, haeq, BitVec.getLsbD_setWidth,
              decide_eq_true (Nat.lt_of_lt_of_le hi (by rw [← heqw]; exact hsn.2.1)), Bool.true_and]
          · have hltw : target.widenWidth n < target.widenWidth m' := Nat.lt_of_le_of_ne hmono heqw
            simp only [heqw, ↓reduceDIte, hltw, ↓reduceIte]
            rw [wp_let, op1_wp_eq, OpCode.wp_trunc]; refine ⟨Nat.le_of_lt hltw, ?_⟩
            apply hcont (Arg.var _)
            simp only [Arg.val_var]
            rw [haeq, BitVec.setWidth_setWidth_of_le _ hsn.2.1,
              BitVec.setWidth_setWidth_of_le _ (Nat.le_trans hnm hsm.2.1)]
        refine hstep1 (fun r => emitMaskToN n (target.widenWidth n) r fun rm => k ((rm, ()), ())) fun r hr => ?_
        refine emitMaskToN_wp hsn.2.1 rfl fun rm hrm => ?_
        refine hk _ _ (TRel.cons ?_ TRel.nil) hwP
        change (rm.val, ()) = (BitVec.setWidth (target.widenWidth n) (BitVec.setWidth n a₁.val), ())
        congr 1; rw [hrm, hr]
  | ofBool n =>
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_ofBool] at hw
    rw [legalOp.eq_30]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have hc_val := valsTup_legalArg target hG hc'
    rcases hpc : legalArg target c₂ with ⟨c', ⟨⟩⟩; rw [hpc] at hc_val
    have hceq : c'.val = c₁.val := (Prod.mk.inj hc_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      have h0 : BitVec.ofNat 0 c₁.val.toNat = 0#0 := Subsingleton.elim _ _
      change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
      rw [h0]; congr 1
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      rw [wp_let, op1_wp_eq, OpCode.wp_ofBool]; dsimp only
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
      congr 1; simp only [Arg.val_var, hceq]; apply BitVec.eq_of_toNat_eq
      have hcc : c₁.val.toNat ≤ 1 := by cases c₁.val <;> simp
      have hpn : 1 < 2 ^ n := Nat.one_lt_pow hn0 (by omega)
      have hpw : 2 ^ n ≤ 2 ^ target.widenWidth n := Nat.pow_le_pow_right (by omega) hs.2.1
      rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  | addc n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_addc] at hw
    rw [legalOp.eq_31]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    have hc_val := valsTup_legalArg target hG hc'
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩; rw [hpb] at hb_val
    rcases hpc : legalArg target c₂ with ⟨c', ⟨⟩⟩; rw [hpc] at hc_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hceq : c'.val = c₁.val := (Prod.mk.inj hc_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw
      · change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
        have h0 : a₁.val + b₁.val + BitVec.ofNat 0 c₁.val.toNat = 0#0 := Subsingleton.elim _ _
        rw [h0]; congr 1
      · change (c'.val, ()) = (decide (2 ^ 0 ≤ a₁.val.toNat + b₁.val.toNat + c₁.val.toNat), ())
        have ha0 : a₁.val.toNat = 0 := by have := a₁.val.isLt; omega
        have hb0 : b₁.val.toNat = 0 := by have := b₁.val.isLt; omega
        rw [hceq, ha0, hb0]; cases c₁.val <;> rfl
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op3_wp_eq, OpCode.wp_addc]; dsimp only
        have hp : 2 ^ n = 2 ^ target.widenWidth n := by rw [← hnw]
        have ha_nat : a'.val.toNat = a₁.val.toNat := by
          rw [haeq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by simpa [← hp] using a₁.val.isLt)]
        have hb_nat : b'.val.toNat = b₁.val.toNat := by
          rw [hbeq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by simpa [← hp] using b₁.val.isLt)]
        refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw
        · change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; simp only [Arg.val_var]; apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, ha_nat, hb_nat, hceq,
            BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, ← hp, Nat.mod_mod]
        · change (decide _, ()) = (decide _, ())
          congr 1; simp only [hp, ha_nat, hb_nat, hceq]
      · next hnw =>
        rw [wp_let, op1_wp_eq, OpCode.wp_ofBool, wp_let, op2_wp_eq, OpCode.wp_add, wp_let, op2_wp_eq, OpCode.wp_add]
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine emitMaskToN_wp hs.2.1 rfl fun s hs_eq => ?_
        rw [wp_let, op2_wp_eq, OpCode.wp_cmp]; simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [Arg.val_var, Arg.val_imm, lift2, liftCmp, CmpOp.evalBits] at hs_eq ⊢
        have hwid := opWp_addc_widened (Nat.pos_of_ne_zero hn0) (Nat.lt_of_le_of_ne hs.2.1 hnw)
          a₁.val b₁.val c₁.val
        refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw
        · change (s.val, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; rw [hs_eq, haeq, hbeq, hceq, hwid.1]
        · change (BitVec.ule (1#(target.widenWidth n) <<< n) _, ()) = (_, ())
          congr 1; rw [haeq, hbeq, hceq]; exact hwid.2
  | subb n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_subb] at hw
    rw [legalOp.eq_32]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    have hc_val := valsTup_legalArg target hG hc'
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩; rw [hpb] at hb_val
    rcases hpc : legalArg target c₂ with ⟨c', ⟨⟩⟩; rw [hpc] at hc_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hceq : c'.val = c₁.val := (Prod.mk.inj hc_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw
      · change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
        have h0 : a₁.val - b₁.val - BitVec.ofNat 0 c₁.val.toNat = 0#0 := Subsingleton.elim _ _
        rw [h0]; congr 1
      · change (c'.val, ()) = (decide (a₁.val.toNat < b₁.val.toNat + c₁.val.toNat), ())
        have ha0 : a₁.val.toNat = 0 := by have := a₁.val.isLt; omega
        have hb0 : b₁.val.toNat = 0 := by have := b₁.val.isLt; omega
        rw [hceq, ha0, hb0]; cases c₁.val <;> rfl
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op3_wp_eq, OpCode.wp_subb]; dsimp only
        have hp : 2 ^ n = 2 ^ target.widenWidth n := by rw [← hnw]
        have ha_nat : a'.val.toNat = a₁.val.toNat := by
          rw [haeq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by simpa [← hp] using a₁.val.isLt)]
        have hb_nat : b'.val.toNat = b₁.val.toNat := by
          rw [hbeq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by simpa [← hp] using b₁.val.isLt)]
        refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw
        · change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; rw [hceq]
          exact op2_setWidth_self (op := fun {k} (x y : BitVec k) => x - y - BitVec.ofNat k c₁.val.toNat)
            hnw haeq hbeq
        · change (decide _, ()) = (decide _, ())
          congr 1; simp only [ha_nat, hb_nat, hceq]
      · next hnw =>
        rw [wp_let, op3_wp_eq, OpCode.wp_subb]; dsimp only
        refine emitMaskToN_wp hs.2.1 rfl fun d hd => ?_
        simp only [Arg.val_var] at hd
        have hwid := opWp_subb_widened (Nat.pos_of_ne_zero hn0) (Nat.lt_of_le_of_ne hs.2.1 hnw)
          a₁.val b₁.val c₁.val
        refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw
        · change (d.val, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; rw [hd, haeq, hbeq, hceq, hwid.1]
        · change (decide (a'.val.toNat < b'.val.toNat + c'.val.toNat), ()) = (_, ())
          congr 1; rw [haeq, hbeq, hceq]; exact hwid.2
  | umulw n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_umulw] at hw
    rw [legalOp.eq_33]
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
      have hzv : ∀ v : BitVec 0, 0#(target.widenWidth 0) = BitVec.setWidth (target.widenWidth 0) v := fun v => by
        rw [Subsingleton.elim v (0#0)]; apply BitVec.eq_of_toNat_eq; simp
      refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw <;>
        (change (0#(target.widenWidth 0), ()) = (BitVec.setWidth (target.widenWidth 0) _, ());
         congr 1; exact hzv _)
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op2_wp_eq, OpCode.wp_umulw]; dsimp only
        refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw
        · change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; simp only [Arg.val_var]
          exact op2_setWidth_self (op := fun {k} (x y : BitVec k) => x * y) hnw haeq hbeq
        · change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; simp only [Arg.val_var]
          exact op2_setWidth_self (op := fun {k} (x y : BitVec k) => BitVec.ofNat k (x.toNat * y.toNat / 2 ^ k))
            hnw haeq hbeq
      · next hnw =>
        have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
        have hn_lt : n < target.widenWidth n := Nat.lt_of_le_of_ne hs.2.1 hnw
        rw [wp_let, op2_wp_eq, OpCode.wp_umulw]; dsimp only
        refine emitMaskToN_wp hs.2.1 rfl fun lo hlo => ?_
        rw [wp_let, op2_wp_eq, OpCode.wp_lshr, wp_let, op2_wp_eq, OpCode.wp_shl, wp_let, op2_wp_eq, OpCode.wp_or]
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine emitMaskToN_wp hs.2.1 rfl fun hi hhi => ?_
        simp only [Arg.val_var] at hlo
        simp only [Arg.val_var, Arg.val_imm, lift2] at hhi
        have hwid := opWp_umulw_widened hn_pos hn_lt a₁.val b₁.val
        have hnw2 : target.widenWidth n < 2 ^ target.widenWidth n := Nat.lt_two_pow_self
        have hn2w : n < 2 ^ target.widenWidth n := Nat.lt_trans hn_lt hnw2
        have hwsub2w : target.widenWidth n - n < 2 ^ target.widenWidth n :=
          Nat.lt_of_le_of_lt (Nat.sub_le _ _) hnw2
        have hm1 : (BitVec.ofNat (target.widenWidth n) n).toNat % target.widenWidth n = n := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn2w, Nat.mod_eq_of_lt hn_lt]
        have hm2 : (BitVec.ofNat (target.widenWidth n) (target.widenWidth n - n)).toNat % target.widenWidth n =
            target.widenWidth n - n := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwsub2w, Nat.mod_eq_of_lt (by omega)]
        refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw
        · change (lo.val, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; rw [hlo, haeq, hbeq, hwid.1]
        · change (hi.val, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; rw [hhi, haeq, hbeq, hm1, hm2, hwid.2]
  | smulw n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_smulw] at hw
    rw [legalOp.eq_34]
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
      have hzv : ∀ v : BitVec 0, 0#(target.widenWidth 0) = BitVec.setWidth (target.widenWidth 0) v := fun v => by
        rw [Subsingleton.elim v (0#0)]; apply BitVec.eq_of_toNat_eq; simp
      refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw <;>
        (change (0#(target.widenWidth 0), ()) = (BitVec.setWidth (target.widenWidth 0) _, ());
         congr 1; exact hzv _)
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op2_wp_eq, OpCode.wp_smulw]; dsimp only
        refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw
        · change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; simp only [Arg.val_var]
          exact op2_setWidth_self (op := fun {k} (x y : BitVec k) => x * y) hnw haeq hbeq
        · change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; simp only [Arg.val_var]
          exact op2_setWidth_self (op := fun {k} (x y : BitVec k) =>
            BitVec.extractLsb' k k (BitVec.ofInt (k + k) (x.toInt * y.toInt))) hnw haeq hbeq
      · next hnw =>
        have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
        have hn_lt : n < target.widenWidth n := Nat.lt_of_le_of_ne hs.2.1 hnw
        refine emitSextToW_wp hn_pos hs.2.1 haeq fun sa hsa =>
          emitSextToW_wp hn_pos hs.2.1 hbeq fun sb hsb => ?_
        rw [wp_let, op2_wp_eq, OpCode.wp_smulw]; dsimp only
        refine emitMaskToN_wp hs.2.1 rfl fun lo hlo => ?_
        rw [wp_let, op2_wp_eq, OpCode.wp_lshr, wp_let, op2_wp_eq, OpCode.wp_shl, wp_let, op2_wp_eq, OpCode.wp_or]
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine emitMaskToN_wp hs.2.1 rfl fun hi hhi => ?_
        simp only [Arg.val_var] at hlo
        simp only [Arg.val_var, Arg.val_imm, lift2] at hhi
        have hwid := opWp_smulw_widened hn_pos hn_lt a₁.val b₁.val
        have hnw2 : target.widenWidth n < 2 ^ target.widenWidth n := Nat.lt_two_pow_self
        have hn2w : n < 2 ^ target.widenWidth n := Nat.lt_trans hn_lt hnw2
        have hwsub2w : target.widenWidth n - n < 2 ^ target.widenWidth n :=
          Nat.lt_of_le_of_lt (Nat.sub_le _ _) hnw2
        have hm1 : (BitVec.ofNat (target.widenWidth n) n).toNat % target.widenWidth n = n := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn2w, Nat.mod_eq_of_lt hn_lt]
        have hm2 : (BitVec.ofNat (target.widenWidth n) (target.widenWidth n - n)).toNat % target.widenWidth n =
            target.widenWidth n - n := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwsub2w, Nat.mod_eq_of_lt (by omega)]
        refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw
        · change (lo.val, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; rw [hlo, hsa, hsb, hwid.1]
        · change (hi.val, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; rw [hhi, hsa, hsb, hm1, hm2, hwid.2]
  | udiv n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_udiv] at hw
    rcases hw with ⟨hb0, hwP⟩
    have hn0 : n ≠ 0 := by intro h; subst h; exact hb0 (Subsingleton.elim _ _)
    rw [legalOp.eq_35]
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
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self a₁.val.toNat b₁.val.toNat) (Nat.lt_of_lt_of_le a₁.val.isLt hp))]
  | sdiv n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_sdiv] at hw
    rcases hw with ⟨hsdef, hwP⟩
    have hb0 : b₁.val ≠ 0 := by
      unfold sdivDefined at hsdef; simp only [Bool.and_eq_true, bne_iff_ne] at hsdef; exact hsdef.1
    have hn0 : n ≠ 0 := by intro h; subst h; exact hb0 (Subsingleton.elim _ _)
    rw [legalOp.eq_36]
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
    rw [legalOp.eq_37]
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
      Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt a₁.val.toNat hbpos) (Nat.lt_of_lt_of_le b₁.val.isLt hp))]
  | srem n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_srem] at hw
    rcases hw with ⟨hsdef, hwP⟩
    have hb0 : b₁.val ≠ 0 := by
      unfold sdivDefined at hsdef; simp only [Bool.and_eq_true, bne_iff_ne] at hsdef; exact hsdef.1
    have hn0 : n ≠ 0 := by intro h; subst h; exact hb0 (Subsingleton.elim _ _)
    rw [legalOp.eq_38]
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
    rw [legalOp.eq_39]
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
          rw [hbeq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b₁.val.isLt hp)] at this
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
          Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self a₁.val.toNat b₁.val.toNat) (Nat.lt_of_lt_of_le a₁.val.isLt hp))]
  | sdiv0 n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_sdiv0] at hw
    rw [legalOp.eq_40]
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
        exact op2_setWidth_self (op := fun {k} (x y : BitVec k) => if y = 0 then 0 else BitVec.sdiv x y)
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
          simp only [hb0', ↓reduceIte]; simp only [hb0, ↓reduceIte]; apply BitVec.eq_of_toNat_eq; simp
        · have hb0' : BitVec.signExtend (target.widenWidth n) b₁.val ≠ 0 := fun h => hb0 (hsbz.mp h)
          rw [ite_eq_right hb0', ite_eq_right hb0]
          exact opWp_sdiv_widened hs.2.1 a₁.val b₁.val
  | mkpair a b =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_mkpair] at hw
    rw [legalOp.eq_41]
    dsimp only [LegalTarget.supportsOpCode] at hsupp
    simp only [Bool.and_eq_true] at hsupp
    dsimp only
    by_cases hkp : target.keepsPacked (a.pair b) = true
    · simp only [hkp, ↓reduceDIte]
      refine packFromLegal_wp target a hsupp.1 (legalArg target a₂) a₁.val (valsTup_legalArg target hG ha)
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
    rw [legalOp.eq_42]
    dsimp only [LegalTarget.supportsOpCode] at hsupp
    simp only [Bool.and_eq_true] at hsupp
    dsimp only
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
      have hsp := opWp_valsTup_splitToTup hkf (legalArg target a₂) a₁.val (valsTup_legalArg target hG hp)
      rcases htup : tupSplit (splitToTup hkf (legalArg target a₂)) with ⟨la, lb⟩
      rw [htup] at hsp
      simp only [htup]
      exact hk _ _ (TRel.cons hsp.1 (TRel.cons hsp.2 TRel.nil)) hw
  | bitcast t u hsz =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_bitcast] at hw
    rw [legalOp.eq_43]
    dsimp only [LegalTarget.supportsOpCode] at hsupp
    simp only [Bool.and_eq_true] at hsupp
    dsimp only
    by_cases heq : t = u
    · subst heq; simp only [↓reduceDIte]
      have hid : ofBits t (BitVec.cast rfl (toBits t a₁.val)) = a₁.val := ofBits_toBits t a₁.val
      rw [hid] at hw
      exact hk _ _ (TRel.cons (valsTup_legalArg target hG ha) TRel.nil) hw
    · simp only [heq, ↓reduceDIte]
      by_cases ht : isNatTy target t = true
      · refine dite_true_wp (P := fun e => wp Γ Q X e m) (by cases t <;> simpa [isNatTy] using ht) ?_
        by_cases hu : isNatTy target u = true
        · refine dite_true_wp (P := fun e => wp Γ Q X e m) (by cases u <;> simpa [isNatTy] using hu) ?_
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
        · refine dite_false_wp (P := fun e => wp Γ Q X e m) (by cases u <;> simpa [isNatTy] using hu) ?_
          refine splitLegalToLeaves_wp target t hsupp.1 (legalArg target a₂) a₁.val
            (valsTup_legalArg target hG ha) fun fx hfx =>
            packLeavesToWords64_wp target hv t hsupp.1 hfx fun words hbits _ _ =>
            unpackWords64ToLeaves_wp target hv u hsupp.2
              (fun i hi => by
                rw [Nat.zero_add, hbits i (by rw [hsz]; exact hi), toBits_ofBits, BitVec.getLsbD_cast])
              fun fu hfu => packLeavesToLegal_wp target u hsupp.2 fu _ hfu fun res hres =>
                hk _ _ (TRel.cons hres TRel.nil) hw
      · refine dite_false_wp (P := fun e => wp Γ Q X e m) (by cases t <;> simpa [isNatTy] using ht) ?_
        refine splitLegalToLeaves_wp target t hsupp.1 (legalArg target a₂) a₁.val
          (valsTup_legalArg target hG ha) fun fx hfx =>
          packLeavesToWords64_wp target hv t hsupp.1 hfx fun words hbits _ _ =>
          unpackWords64ToLeaves_wp target hv u hsupp.2
            (fun i hi => by
              rw [Nat.zero_add, hbits i (by rw [hsz]; exact hi), toBits_ofBits, BitVec.getLsbD_cast])
            fun fu hfu => packLeavesToLegal_wp target u hsupp.2 fu _ hfu fun res hres =>
              hk _ _ (TRel.cons hres TRel.nil) hw
  | shufd t imm =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    have hsupp := (Bool.and_eq_true _ _ |>.mp hsupp).1
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_shufd] at hw
    rcases hw with ⟨hne, hmod, hwP⟩
    rw [legalOp.eq_44]
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
    rw [legalOp.eq_45]
    exact legalShufb_wp target hv t hsupp hne hmod (legalArg target a₂) (legalArg target b₂) a₁.val b₁.val
      (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb) (fun res => k (res, ())) m
      fun res hres => hk _ _ (TRel.cons hres TRel.nil) hwP
  | alignr t imm =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    have hsupp := (Bool.and_eq_true _ _ |>.mp hsupp).1
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_alignr] at hw
    rcases hw with ⟨hne, hmod, hwP⟩
    rw [legalOp.eq_46]
    exact legalAlignr_wp target hv imm t hsupp hne hmod (legalArg target a₂) (legalArg target b₂) a₁.val b₁.val
      (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb) (fun res => k (res, ())) m
      fun res hres => hk _ _ (TRel.cons hres TRel.nil) hwP
  | blendw t imm =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    have hsupp := (Bool.and_eq_true _ _ |>.mp hsupp).1
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_blendw] at hw
    rcases hw with ⟨hne, hmod, hwP⟩
    rw [legalOp.eq_47]
    exact legalBlendw_wp target hv imm t hsupp hne hmod (legalArg target a₂) (legalArg target b₂) a₁.val b₁.val
      (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb) (fun res => k (res, ())) m
      fun res hres => hk _ _ (TRel.cons hres TRel.nil) hwP
  | sha256rnds2 =>
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, w₁, w₂, _, _, hw', hargs⟩; cases hargs
    have hsupp := (Bool.and_eq_true _ _ |>.mp hsupp).1
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_sha256rnds2] at hw
    rw [legalOp.eq_48]
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
    · refine splitLegalToLeaves_wp target v4i32 hsupp (legalArg target c₂) c₁.val hc_val fun fc hfc =>
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
        scalarSha256rnds2_wp hcd0 hcd1 hcd2 hcd3 hab0 hab1 hab2 hab3 hwk0 hwk1 fun r0 r1 r2 r3 hr0 hr1 hr2 hr3 =>
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
    rw [legalOp.eq_49]
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
    · refine splitLegalToLeaves_wp target v4i32 hsupp (legalArg target a₂) a₁.val ha_val fun fa hfa =>
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
    rw [legalOp.eq_50]
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
    · refine splitLegalToLeaves_wp target v4i32 hsupp (legalArg target a₂) a₁.val ha_val fun fa hfa =>
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
    rw [legalOp.eq_51]
    exact legalOp_floatBin_wp target hG OpCode.fadd Float.Model.UnpackedFloat.add
      (fun u x y p => OpCode.wp_fadd u (x, y, ()) p) (fun _ => rfl) hsupp ha hb hw hk
  | fsub t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_52]
    exact legalOp_floatBin_wp target hG OpCode.fsub Float.Model.UnpackedFloat.sub
      (fun u x y p => OpCode.wp_fsub u (x, y, ()) p) (fun _ => rfl) hsupp ha hb hw hk
  | fmul t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_53]
    exact legalOp_floatBin_wp target hG OpCode.fmul Float.Model.UnpackedFloat.mul
      (fun u x y p => OpCode.wp_fmul u (x, y, ()) p) (fun _ => rfl) hsupp ha hb hw hk
  | fdiv t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_54]
    exact legalOp_floatBin_wp target hG OpCode.fdiv Float.Model.UnpackedFloat.div
      (fun u x y p => OpCode.wp_fdiv u (x, y, ()) p) (fun _ => rfl) hsupp ha hb hw hk
  | ffma t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_ffma] at hw
    rw [legalOp.eq_55]
    cases hft : t.isFloatTree
    · simp [hft] at hw
    · simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      refine legalTernaryTree_wp target OpCode.ffma (fun u => target.vecFloatOpSupported (OpCode.ffma u) u)
        (fun _ _ _ _ => Expr.hlt) (fun _ _ _ _ _ => Expr.hlt)
        (fun fmt x y z cont => Expr.let_ (op3 (OpCode.ffma (Ty.float fmt)) x y z) fun (r, _) => cont (Arg.var r))
        (onB := fun _ _ _ _ => False) (onBi := fun _ _ _ _ _ => False)
        (onF := fun fmt a b c q =>
          floatResultWp fmt (Float.Model.UnpackedFloat.fma fmt.format
            (unpackFloat fmt a) (unpackFloat fmt b) (unpackFloat fmt c)) q)
        (by intros; contradiction)
        (by intros; contradiction)
        ?_ ?_ (by intros; contradiction) (by intros; contradiction)
        (fun fmt _ _ _ _ _ hpq h => opWp_floatResultWp_mono fmt _ hpq h)
        t hsupp (legalArg target a₂) (legalArg target b₂) (legalArg target c₂) a₁.val b₁.val c₁.val
        (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb) (valsTup_legalArg target hG hc')
        (fun res => k (res, ())) m ?_
      · intro fmt _ a' b' c' a b c cont m' ha' hb' hc'' hpre
        rw [wp_let, op3_wp_eq, OpCode.wp_ffma]; simp only [Ty.isFloatTree, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
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
    rw [legalOp.eq_56]
    cases hft : t.isFloatTree
    · simp [hft] at hw
    · simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      refine legalUnaryTree_wp target OpCode.fsqrt (fun u => target.vecFloatOpSupported (OpCode.fsqrt u) u)
        (fun _ _ => Expr.hlt) (fun _ _ _ => Expr.hlt)
        (fun fmt x cont => Expr.let_ (op1 (OpCode.fsqrt (Ty.float fmt)) x) fun (r, _) => cont (Arg.var r))
        (onB := fun _ _ => False) (onBi := fun _ _ _ => False)
        (onF := fun fmt a q =>
          floatResultWp fmt (Float.Model.UnpackedFloat.sqrt fmt.format (unpackFloat fmt a)) q)
        (by intros; contradiction)
        (by intros; contradiction)
        ?_ ?_ (by intros; contradiction) (by intros; contradiction)
        (fun fmt _ _ _ hpq h => opWp_floatResultWp_mono fmt _ hpq h)
        t hsupp (legalArg target a₂) a₁.val (valsTup_legalArg target hG ha) (fun res => k (res, ())) m ?_
      · intro fmt _ a' a cont m' ha' hpre
        rw [wp_let, op1_wp_eq, OpCode.wp_fsqrt]; simp only [Ty.isFloatTree, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        change floatResultWp fmt (Float.Model.UnpackedFloat.sqrt fmt.format (unpackFloat fmt a'.val)) _
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
    rw [legalOp.eq_57]
    cases hft : t.isFloatTree
    · simp [hft] at hw
    · simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      refine legalUnaryTree_wp target OpCode.fneg (fun u => target.vecFloatOpSupported (OpCode.fneg u) u)
        (fun _ _ => Expr.hlt) (fun _ _ _ => Expr.hlt)
        (fun fmt x cont => Expr.let_ (op1 (OpCode.fneg (Ty.float fmt)) x) fun (r, _) => cont (Arg.var r))
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
        t hsupp (legalArg target a₂) a₁.val (valsTup_legalArg target hG ha) (fun res => k (res, ())) m
        (opWp_treeRel1_lift1_float (fun {n} x => x ^^^ 1#n <<< (n - 1)) t hft _ _
          fun fres hfres => hk _ _ (TRel.cons hfres TRel.nil) hw)
  | fabs t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_fabs] at hw
    rw [legalOp.eq_58]
    cases hft : t.isFloatTree
    · simp [hft] at hw
    · simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      refine legalUnaryTree_wp target OpCode.fabs (fun u => target.vecFloatOpSupported (OpCode.fabs u) u)
        (fun _ _ => Expr.hlt) (fun _ _ _ => Expr.hlt)
        (fun fmt x cont => Expr.let_ (op1 (OpCode.fabs (Ty.float fmt)) x) fun (r, _) => cont (Arg.var r))
        (onB := fun _ _ => False) (onBi := fun _ _ _ => False)
        (onF := fun fmt a q => q (a &&& ~~~(1#fmt.width <<< (fmt.width - 1))))
        (by intros; contradiction)
        (by intros; contradiction)
        (fun fmt _ x' x cont m' hx' hpre => by
          rw [wp_let, op1_wp_eq, OpCode.wp_fabs, hx']; exact hpre _ rfl)
        (fun u _ _ _ x p htr => by
          have hu := opWp_lift1_float_of_treeRel1 (fun {n} x => x &&& ~~~(1#n <<< (n - 1))) u x p htr
          rw [OpCode.wp_fabs]; simp [hu.1, hu.2])
        (by intros; contradiction) (by intros; contradiction)
        (fun _ _ _ _ hpq h => hpq _ h)
        t hsupp (legalArg target a₂) a₁.val (valsTup_legalArg target hG ha) (fun res => k (res, ())) m
        (opWp_treeRel1_lift1_float (fun {n} x => x &&& ~~~(1#n <<< (n - 1))) t hft _ _
          fun fres hfres => hk _ _ (TRel.cons hfres TRel.nil) hw)
  | fcmp o t m_ty hm =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    cases hm
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_fcmp] at hw
    rw [legalOp.eq_59]
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
    rw [legalOp.eq_60]
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
          rw [show (2 ^ target.widenWidth n : Int) = ((2 ^ target.widenWidth n : Nat) : Int) from (Int.natCast_pow 2 _).symm]
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
          change (BitVec.ofInt (target.widenWidth n) z, ()) = (BitVec.setWidth (target.widenWidth n) (BitVec.ofInt n z), ())
          congr 1; exact opWp_fptoui_widened (Nat.pos_of_ne_zero hn0) hs.2.1 hz0 hzn'
  | fptosi fmt n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_fptosi] at hw
    rcases hw with ⟨hn0, hw⟩
    rw [legalOp.eq_61]
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
          rw [show (2 ^ (target.widenWidth n - 1) : Int) = ((2 ^ (target.widenWidth n - 1) : Nat) : Int) from (Int.natCast_pow 2 _).symm]
          rw [show (2 ^ (n - 1) : Int) = ((2 ^ (n - 1) : Nat) : Int) from (Int.natCast_pow 2 _).symm] at hzlo
          omega
        have hzhi' : z < 2 ^ (target.widenWidth n - 1) := by
          rw [show (2 ^ (target.widenWidth n - 1) : Int) = ((2 ^ (target.widenWidth n - 1) : Nat) : Int) from (Int.natCast_pow 2 _).symm]
          rw [show (2 ^ (n - 1) : Int) = ((2 ^ (n - 1) : Nat) : Int) from (Int.natCast_pow 2 _).symm] at hzhi
          omega
        split
        · next hnw =>
          rw [wp_let, op1_wp_eq, OpCode.wp_fptosi, haeq, htr]
          refine ⟨Nat.ne_of_gt hs.2.2.1, hzlo', hzhi', hk _ _ (TRel.cons ?_ TRel.nil) hwP⟩
          change (BitVec.ofInt (target.widenWidth n) z, ()) = (BitVec.setWidth (target.widenWidth n) (BitVec.ofInt n z), ())
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
    rw [legalOp.eq_62]
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
    rw [legalOp.eq_63]
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
    rw [legalOp.eq_64]
    have ha_val := valsTup_legalArg target hG ha
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    have haeq : a'.val = a₁.val := (Prod.mk.inj ha_val).1
    rw [wp_let, op1_wp_eq, OpCode.wp_fcvt, haeq]
    have hmono : ∀ (src dst : Fmt) (b : BitVec src.width) {p q : BitVec dst.width → Prop},
        (∀ r, p r → q r) → convertFloat src dst b p → convertFloat src dst b q := by
      intro src dst b p q hpq hcf
      unfold convertFloat at hcf ⊢
      cases huf : unpackFloat src b with
      | notANumber => simp only [huf] at hcf; exact fun r hr => hpq r (hcf r hr)
      | _ => simp only [huf] at hcf; exact hpq _ hcf
    exact hmono fmt g a₁.val (fun r hr => hk _ _ (TRel.cons (by rfl) TRel.nil) hr) hw


end LegalWp

end LeanQbe.T
