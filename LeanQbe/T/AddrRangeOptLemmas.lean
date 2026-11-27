module

public import LeanQbe.T.AddrRangeOptLemmas0
import LeanQbe.T.OpsLemmas

/-!
# Correctness of `Func.addrRangeOpt`

Proves weakest-precondition preservation (`addrRangeSweep_wp`), relational well-formedness
preservation (`addrRangeSweep_wf`), and closed-function theorems `Func.addrRangeOpt_wf` and
`Func.addrRangeOpt_spec`, building on `AddrRangeOptLemmas0`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-- Positional projection of `LoopBlocks` at block index `i`. -/
def LoopBlocks.get {sig : List (List Ty)} {ts : List Ty} :
    LoopBlocks → Member ts sig → Bool × LoopTree
  | .nil, _ => (false, .leaf)
  | .cons isL ph _, .here => (isL, ph)
  | .cons _ _ pt, .there i => pt.get i

theorem addrRangeSweepB_get_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (curD b : Nat) :
    {sig : List (List Ty)} → (bsPlan : LoopBlocks) → (bs : Blocks (ARVal V) L rs sig) →
    ∀ {ts : List Ty} (i : Member ts sig) (xs : Tup V ts),
      (addrRangeSweepB curD b bsPlan bs).get i xs =
        let p := bsPlan.get i
        let bd := if p.1 then curD + 1 else curD
        addrRangeSweep bd (b + ts.length) p.2 (bs.get i (freshARVals bd ts xs b))
  | _ :: _, .nil, .cons _ _, _, .here, _ => rfl
  | _ :: _, .cons _ _ _, .cons _ _, _, .here, _ => rfl
  | _ :: _, .nil, .cons _ bs, _, .there i, xs => addrRangeSweepB_get_eq curD b .nil bs i xs
  | _ :: _, .cons _ _ pt, .cons _ bs, _, .there i, xs => addrRangeSweepB_get_eq curD b pt bs i xs

private theorem addrRangeSweep_let {V : Ty → Type} {L : List Ty → Type} {ts rs : List Ty}
    (curD next : Nat) (plan : LoopTree) (op : Op (ARVal V) ts)
    (k : Tup (ARVal V) ts → Expr (ARVal V) L rs) :
    addrRangeSweep curD next plan (.let_ op k) =
      let kPlan := plan.step1
      let foldD := plan.foldDisp
      match op.arStep curD next with
      | .elim res => addrRangeSweep curD next kPlan (k res)
      | .emit1 op' wrap =>
        .let_ op' fun xs => addrRangeSweep curD (next + ts.length) kPlan (k (wrap xs))
      | .rangeSubCmp w o x lo width outD =>
        .let_ (op2 (.sub (.bits w)) x (.imm lo)) fun (t, ()) =>
        .let_ (op2 (.cmp o (.bits w)) (.var t) (.imm width)) fun (r, ()) =>
        addrRangeSweep curD (next + 1) kPlan (k (ARVal.fresh r next outD, ()))
      | .addrShl n isSub base inv iv ivD sh _ disp =>
        .let_ (op2 (.shl (.bits n)) inv (.imm (BitVec.ofNat n sh))) fun (t1, ()) =>
        .let_ (op2 (if isSub then .sub (.bits n) else .add (.bits n)) base (.var t1))
          fun (t2, ()) =>
        if disp == 0#n then
          .let_ (op2 (.shl (.bits n)) iv (.imm (BitVec.ofNat n sh))) fun (t3, ()) =>
          .let_ (op2 (.add (.bits n)) (.var t2) (.var t3)) fun (t4, ()) =>
          addrRangeSweep curD (next + 1) kPlan (k (ARVal.fresh t4 next ivD, ()))
        else if foldD then
          .let_ (op2 (.add (.bits n)) (.var t2) (.imm disp)) fun (t2d, ()) =>
          .let_ (op2 (.shl (.bits n)) iv (.imm (BitVec.ofNat n sh))) fun (t3, ()) =>
          .let_ (op2 (.add (.bits n)) (.var t2d) (.var t3)) fun (t4, ()) =>
          addrRangeSweep curD (next + 1) kPlan (k (ARVal.fresh t4 next ivD, ()))
        else
          .let_ (op2 (.shl (.bits n)) iv (.imm (BitVec.ofNat n sh))) fun (t3, ()) =>
          .let_ (op2 (.add (.bits n)) (.var t2) (.var t3)) fun (t4, ()) =>
          .let_ (op2 (.add (.bits n)) (.var t4) (.imm disp)) fun (t5, ()) =>
          addrRangeSweep curD (next + 1) kPlan (k (ARVal.fresh t5 next ivD, ()))
      | .addrPlain n isSub base inv iv invD ivD disp =>
        .let_ (op2 (if isSub then .sub (.bits n) else .add (.bits n)) base inv) fun (t1, ()) =>
        if disp == 0#n then
          .let_ (op2 (.add (.bits n)) (.var t1) iv) fun (t2, ()) =>
          addrRangeSweep curD (next + 1) kPlan
            (k (⟨.var t2, .var next, ivD, { addr? := some (.addVV (.var t1) invD iv ivD 0#n) }⟩,
              ()))
        else if foldD then
          .let_ (op2 (.add (.bits n)) (.var t1) (.imm disp)) fun (t1d, ()) =>
          .let_ (op2 (.add (.bits n)) (.var t1d) iv) fun (t2, ()) =>
          addrRangeSweep curD (next + 1) kPlan
            (k (⟨.var t2, .var next, ivD, { addr? := some (.addVV (.var t1d) invD iv ivD 0#n) }⟩,
              ()))
        else
          .let_ (op2 (.add (.bits n)) (.var t1) iv) fun (t2, ()) =>
          .let_ (op2 (.add (.bits n)) (.var t2) (.imm disp)) fun (t3, ()) =>
          addrRangeSweep curD (next + 1) kPlan
            (k (⟨.var t3, .var next, ivD, { addr? := some (.addVV (.var t1) invD iv ivD disp) }⟩,
              ())) := by
  delta addrRangeSweep; dsimp only [Expr.brecOn, Expr.rec, addrRangeSweep._f]
  cases op.arStep curD next <;> rfl

/-- Helper for `addrRangeSweep_wp` covering one `.let_` step. -/
private theorem arStep_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {G : Ctx (ARVal Val) Val} {ρ : FEnv} {curD b : Nat} (hG : ARGood ρ b G)
    {sig ts : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg (ARVal Val)) sig} {args₂ : Tup (Arg Val) sig}
    (hargs : TRel (ArgRel G) args₁ args₂)
    {k₁ : Tup (ARVal Val) ts → Expr (ARVal Val) Cont rs}
    {k₂ : Tup Val ts → Expr Val Cont rs}
    (plan : LoopTree)
    (ih : ∀ xs₁ xs₂ b' ρ', ARGood ρ' b' (Tup.zip xs₁ xs₂ ++ G) →
      wp Γ Q X (k₂ xs₂) m → wp Γ Q X (addrRangeSweep curD b' plan.step1 (k₁ xs₁)) m)
    (hw : code.wp (vals args₂) fun xs => wp Γ Q X (k₂ xs) m) :
    wp Γ Q X (addrRangeSweep curD b plan (.let_ ⟨code, args₁⟩ k₁)) m := by
  rw [addrRangeSweep_let]
  dsimp only [Op.arStep]
  have hkeep : ∀ (outD : Nat),
      wp Γ Q X (.let_ ⟨code, tupArOut args₁⟩ fun xs =>
        addrRangeSweep curD (b + ts.length) plan.step1 (k₁ (wrapKept outD b code args₁ xs))) m := by
    intro outD
    dsimp only [wp, Op.wp]
    rw [hargs.arOut_vals hG]
    exact OpCode.wp_mono code (vals args₂) (fun xs ⟨hk2, hG'⟩ =>
      ih _ xs (b + ts.length) (fupdTup ρ b xs) hG' hk2)
      (wrapKept_good hG hargs hw)
  have haddrShl : ∀ {n : Nat} (isSub : Bool) (base inv iv : Arg Val (.bits n))
      (ivD sh : Nat) (hsh : sh < n) (disp : BitVec n)
      {k₁' : Tup (ARVal Val) [.bits n] → Expr (ARVal Val) Cont rs}
      {k₂' : Tup Val [.bits n] → Expr Val Cont rs}
      (ih' : ∀ xs₁ xs₂ b' ρ', ARGood ρ' b' (Tup.zip xs₁ xs₂ ++ G) →
        wp Γ Q X (k₂' xs₂) m → wp Γ Q X (addrRangeSweep curD b' plan.step1 (k₁' xs₁)) m)
      (hw' : wp Γ Q X (k₂' ((if isSub then ((base.val - (inv.val <<< sh)) + (iv.val <<< sh)) + disp
          else ((base.val + (inv.val <<< sh)) + (iv.val <<< sh)) + disp), ())) m),
      wp Γ Q X
        (.let_ (op2 (.shl (.bits n)) inv (.imm (BitVec.ofNat n sh))) fun (t1, ()) =>
         .let_ (op2 (if isSub then .sub (.bits n) else .add (.bits n)) base (.var t1))
           fun (t2, ()) =>
         if disp == 0#n then
           .let_ (op2 (.shl (.bits n)) iv (.imm (BitVec.ofNat n sh))) fun (t3, ()) =>
           .let_ (op2 (.add (.bits n)) (.var t2) (.var t3)) fun (t4, ()) =>
           addrRangeSweep curD (b + 1) plan.step1 (k₁' (ARVal.fresh t4 b ivD, ()))
         else if plan.foldDisp then
           .let_ (op2 (.add (.bits n)) (.var t2) (.imm disp)) fun (t2d, ()) =>
           .let_ (op2 (.shl (.bits n)) iv (.imm (BitVec.ofNat n sh))) fun (t3, ()) =>
           .let_ (op2 (.add (.bits n)) (.var t2d) (.var t3)) fun (t4, ()) =>
           addrRangeSweep curD (b + 1) plan.step1 (k₁' (ARVal.fresh t4 b ivD, ()))
         else
           .let_ (op2 (.shl (.bits n)) iv (.imm (BitVec.ofNat n sh))) fun (t3, ()) =>
           .let_ (op2 (.add (.bits n)) (.var t2) (.var t3)) fun (t4, ()) =>
           .let_ (op2 (.add (.bits n)) (.var t4) (.imm disp)) fun (t5, ()) =>
           addrRangeSweep curD (b + 1) plan.step1 (k₁' (ARVal.fresh t5 b ivD, ()))) m := by
    intro n isSub base inv iv ivD sh hsh disp k₁' k₂' ih' hw'
    have hsh_mod : (BitVec.ofNat n sh).toNat % n = sh := by
      have h1 : (BitVec.ofNat n sh).toNat = sh := by
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hsh (Nat.le_of_lt Nat.lt_two_pow_self))
      rw [h1, Nat.mod_eq_of_lt hsh]
    cases isSub <;> simp only [Bool.false_eq_true, ↓reduceIte] at hw' ⊢
    all_goals
      dsimp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, lift2, Ty.hasFloat]
      simp only [Bool.false_eq_true, ↓reduceIte, hsh_mod]
      cases hd0 : (disp == 0#n) with
      | true =>
        simp only [↓reduceIte]; have hd0' : disp = 0#n := eq_of_beq hd0
        subst hd0'; simp only [BitVec.add_zero] at hw'
        dsimp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, lift2, Ty.hasFloat]
        simp only [Bool.false_eq_true, ↓reduceIte, hsh_mod]
        exact ih' _ _ (b + 1) (fupd ρ b _) (hG.freshOne ivD _) hw'
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases hfold : plan.foldDisp with
        | true =>
          simp only [↓reduceIte]
          dsimp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, lift2, Ty.hasFloat]
          simp only [Bool.false_eq_true, ↓reduceIte, hsh_mod]
          rw [BitVec.add_assoc, BitVec.add_comm _ disp, ← BitVec.add_assoc] at hw'
          exact ih' _ _ (b + 1) (fupd ρ b _) (hG.freshOne ivD _) hw'
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          dsimp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, lift2, Ty.hasFloat]
          simp only [Bool.false_eq_true, ↓reduceIte, hsh_mod]
          exact ih' _ _ (b + 1) (fupd ρ b _) (hG.freshOne ivD _) hw'
  have haddrPlain : ∀ {n : Nat} (isSub : Bool) (base inv iv : Arg Val (.bits n))
      (invD ivD : Nat) (disp : BitVec n)
      {k₁' : Tup (ARVal Val) [.bits n] → Expr (ARVal Val) Cont rs}
      {k₂' : Tup Val [.bits n] → Expr Val Cont rs}
      (ih' : ∀ xs₁ xs₂ b' ρ', ARGood ρ' b' (Tup.zip xs₁ xs₂ ++ G) →
        wp Γ Q X (k₂' xs₂) m → wp Γ Q X (addrRangeSweep curD b' plan.step1 (k₁' xs₁)) m)
      (hw' : wp Γ Q X (k₂' ((if isSub then ((base.val - inv.val) + iv.val) + disp
          else ((base.val + inv.val) + iv.val) + disp), ())) m),
      wp Γ Q X
        (.let_ (op2 (if isSub then .sub (.bits n) else .add (.bits n)) base inv) fun (t1, ()) =>
         if disp == 0#n then
           .let_ (op2 (.add (.bits n)) (.var t1) iv) fun (t2, ()) =>
           addrRangeSweep curD (b + 1) plan.step1
             (k₁' (⟨.var t2, .var b, ivD,
               { addr? := some (.addVV (.var t1) invD iv ivD 0#n) }⟩, ()))
         else if plan.foldDisp then
           .let_ (op2 (.add (.bits n)) (.var t1) (.imm disp)) fun (t1d, ()) =>
           .let_ (op2 (.add (.bits n)) (.var t1d) iv) fun (t2, ()) =>
           addrRangeSweep curD (b + 1) plan.step1
             (k₁' (⟨.var t2, .var b, ivD,
               { addr? := some (.addVV (.var t1d) invD iv ivD 0#n) }⟩, ()))
         else
           .let_ (op2 (.add (.bits n)) (.var t1) iv) fun (t2, ()) =>
           .let_ (op2 (.add (.bits n)) (.var t2) (.imm disp)) fun (t3, ()) =>
           addrRangeSweep curD (b + 1) plan.step1
             (k₁' (⟨.var t3, .var b, ivD,
               { addr? := some (.addVV (.var t1) invD iv ivD disp) }⟩, ()))) m := by
    intro n isSub base inv iv invD ivD disp k₁' k₂' ih' hw'
    cases isSub <;> simp only [Bool.false_eq_true, ↓reduceIte] at hw' ⊢
    all_goals
      dsimp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, lift2, Ty.hasFloat]
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hd0 : (disp == 0#n) with
      | true =>
        simp only [↓reduceIte]; have hd0' : disp = 0#n := eq_of_beq hd0
        subst hd0'; simp only [BitVec.add_zero] at hw'
        dsimp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, lift2, Ty.hasFloat]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih' _ _ (b + 1) _ ((hG.upd _).cons ⟨rfl, fupd_eq ρ b _, Nat.lt_succ_self b,
          addrOptGood_of (fun _ h => by injection h with h; subst h; simp [AddrDefGood, Arg.val])⟩)
          hw'
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases hfold : plan.foldDisp with
        | true =>
          simp only [↓reduceIte]
          dsimp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, lift2, Ty.hasFloat]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [BitVec.add_assoc, BitVec.add_comm _ disp, ← BitVec.add_assoc] at hw'
          exact ih' _ _ (b + 1) _ ((hG.upd _).cons ⟨rfl, fupd_eq ρ b _, Nat.lt_succ_self b,
            addrOptGood_of (fun _ h => by
              injection h with h; subst h; simp [AddrDefGood, Arg.val])⟩) hw'
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          dsimp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, lift2, Ty.hasFloat]
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ih' _ _ (b + 1) _ ((hG.upd _).cons ⟨rfl, fupd_eq ρ b _, Nat.lt_succ_self b,
            addrOptGood_of (fun _ h => by injection h with h; subst h; rfl)⟩) hw'
  cases code with
  | add t =>
    cases t with
    | bits n =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      dsimp only
      cases hcond : (n == 64 && decide (0 < curD)) with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact hkeep _
      | true =>
        simp only [↓reduceIte]
        cases h1 : tryAddrReassocOne a₁ b₁ with
        | some st =>
          simp only [OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, lift2] at hw
          have hs := tryAddrReassocOne_sound hG ha hb h1
          cases st with
          | addrShl _ isSub base inv iv ivD sh hsh disp =>
            exact haddrShl isSub base inv iv ivD sh hsh disp ih (hs.2.symm ▸ hw)
          | addrPlain _ isSub base inv iv invD ivD disp =>
            exact haddrPlain isSub base inv iv invD ivD disp ih (hs.2.symm ▸ hw)
          | elim _ | emit1 _ _ => exact False.elim hs
        | none =>
          cases h2 : tryAddrReassocOne b₁ a₁ with
          | some st =>
            simp only [OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, lift2] at hw
            have hs := tryAddrReassocOne_sound hG hb ha h2
            rw [BitVec.add_comm b₂.val a₂.val] at hs
            cases st with
            | addrShl _ isSub base inv iv ivD sh hsh disp =>
              exact haddrShl isSub base inv iv ivD sh hsh disp ih (hs.2.symm ▸ hw)
            | addrPlain _ isSub base inv iv invD ivD disp =>
              exact haddrPlain isSub base inv iv invD ivD disp ih (hs.2.symm ▸ hw)
            | elim _ | emit1 _ _ => exact False.elim hs
          | none =>
            exact hkeep _
    | bool | float _ | pair _ _ => exact hkeep _
  | and t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      simp only [OpCode.wp, vals, lift2] at hw
      dsimp only
      cases hfalse : (a₁.arOut.imm? == some false || b₁.arOut.imm? == some false) with
      | true =>
        simp only [↓reduceIte]
        have hval : (a₂.val && b₂.val) = false := by
          simp only [Bool.or_eq_true, beq_iff_eq] at hfalse
          rcases hfalse with h1 | h2
          · rw [arOut_imm?_eq_val hG ha h1]; rfl
          · rw [arOut_imm?_eq_val hG hb h2]; simp
        exact ih _ (false, ()) b ρ
          (by dsimp only [Tup.zip, List.cons_append, List.nil_append]
              exact hG.cons (ARValGood.ofImm (t := .bool) false))
          (hval ▸ hw)
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases ha1 : (a₁.arOut.imm? == some true) with
        | true =>
          simp only [↓reduceIte]
          have ha1' : a₂.val = true := arOut_imm?_eq_val hG ha (eq_of_beq ha1)
          rw [ha1', Bool.true_and] at hw
          exact ih _ (b₂.val, ()) b ρ
            (by dsimp only [Tup.zip, List.cons_append, List.nil_append]
                exact hG.cons (hb.toARVal_good hG)) hw
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases hb1 : (b₁.arOut.imm? == some true) with
          | true =>
            simp only [↓reduceIte]
            have hb1' : b₂.val = true := arOut_imm?_eq_val hG hb (eq_of_beq hb1)
            rw [hb1', Bool.and_true] at hw
            exact ih _ (a₂.val, ()) b ρ
              (by dsimp only [Tup.zip, List.cons_append, List.nil_append]
                  exact hG.cons (ha.toARVal_good hG)) hw
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            cases hr : tryRangeStep false _ b a₁ b₁ with
            | none =>
              dsimp only [wp, Op.wp, OpCode.wp, op2, vals, lift2]
              rw [ha.arOut_val hG, hb.arOut_val hG]
              exact ih _ (a₂.val && b₂.val, ()) (b + 1) (fupd ρ b _) (hG.freshOne _ _) hw
            | some st =>
              have hs := tryRangeStep_sound hG false ha hb hr (P := fun xs => wp Γ Q X (k₂ xs) m) hw
              cases st with
              | elim res =>
                obtain ⟨xs, hk2, hG'⟩ := hs
                exact ih res xs b ρ hG' hk2
              | emit1 op' wrap =>
                dsimp only [wp]
                exact Op.wp_mono (fun xs ⟨hk2, hG'⟩ =>
                  ih (wrap xs) xs (b + 1) (fupdTup ρ b xs) hG' hk2) hs
              | rangeSubCmp w o x lo width outD =>
                dsimp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, lift2, liftCmp, Ty.hasFloat]
                simp only [Bool.false_eq_true, ↓reduceIte]
                exact ih _ _ (b + 1) (fupd ρ b _) (hG.freshOne outD _) hs
    | bits _ | float _ | pair _ _ => exact hkeep _
  | or t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      simp only [OpCode.wp, vals, lift2] at hw
      dsimp only
      cases htrue : (a₁.arOut.imm? == some true || b₁.arOut.imm? == some true) with
      | true =>
        simp only [↓reduceIte]
        have hval : (a₂.val || b₂.val) = true := by
          simp only [Bool.or_eq_true, beq_iff_eq] at htrue
          rcases htrue with h1 | h2
          · rw [arOut_imm?_eq_val hG ha h1]; rfl
          · rw [arOut_imm?_eq_val hG hb h2]; simp
        exact ih _ (true, ()) b ρ
          (by dsimp only [Tup.zip, List.cons_append, List.nil_append]
              exact hG.cons (ARValGood.ofImm (t := .bool) true))
          (hval ▸ hw)
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases ha1 : (a₁.arOut.imm? == some false) with
        | true =>
          simp only [↓reduceIte]
          have ha1' : a₂.val = false := arOut_imm?_eq_val hG ha (eq_of_beq ha1)
          rw [ha1', Bool.false_or] at hw
          exact ih _ (b₂.val, ()) b ρ
            (by dsimp only [Tup.zip, List.cons_append, List.nil_append]
                exact hG.cons (hb.toARVal_good hG)) hw
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases hb1 : (b₁.arOut.imm? == some false) with
          | true =>
            simp only [↓reduceIte]
            have hb1' : b₂.val = false := arOut_imm?_eq_val hG hb (eq_of_beq hb1)
            rw [hb1', Bool.or_false] at hw
            exact ih _ (a₂.val, ()) b ρ
              (by dsimp only [Tup.zip, List.cons_append, List.nil_append]
                  exact hG.cons (ha.toARVal_good hG)) hw
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            cases hr : tryRangeStep true _ b a₁ b₁ with
            | none =>
              dsimp only [wp, Op.wp, OpCode.wp, op2, vals, lift2]
              rw [ha.arOut_val hG, hb.arOut_val hG]
              exact ih _ (a₂.val || b₂.val, ()) (b + 1) (fupd ρ b _) (hG.freshOne _ _) hw
            | some st =>
              have hs := tryRangeStep_sound hG true ha hb hr (P := fun xs => wp Γ Q X (k₂ xs) m) hw
              cases st with
              | elim res =>
                obtain ⟨xs, hk2, hG'⟩ := hs
                exact ih res xs b ρ hG' hk2
              | emit1 op' wrap =>
                dsimp only [wp]
                exact Op.wp_mono (fun xs ⟨hk2, hG'⟩ =>
                  ih (wrap xs) xs (b + 1) (fupdTup ρ b xs) hG' hk2) hs
              | rangeSubCmp w o x lo width outD =>
                dsimp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, lift2, liftCmp, Ty.hasFloat]
                simp only [Bool.false_eq_true, ↓reduceIte]
                exact ih _ _ (b + 1) (fupd ρ b _) (hG.freshOne outD _) hs
    | bits _ | float _ | pair _ _ => exact hkeep _
  | _ =>
    all_goals exact hkeep _

/-- Weakest-precondition preservation for `addrRangeSweep` under any untrusted `LoopTree`. -/
theorem addrRangeSweep_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (ARVal Val) Val} {D : Ctx Cont Cont}
    {e₁ : Expr (ARVal Val) Cont rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    (∀ p ∈ D, p.2.1 = p.2.2) →
    ∀ curD b ρ plan, ARGood ρ b G → ∀ m, wp Γ Q X e₂ m →
      wp Γ Q X (addrRangeSweep curD b plan e₁) m := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro hD curD b ρ plan hG m hw
    dsimp only [wp] at hw
    cases hop with
    | @mk sig _ code args₁ args₂ hargs =>
      exact arStep_wp hG hargs plan
        (fun xs₁ xs₂ b' ρ' hG' hk2 => ih xs₁ xs₂ hD curD b' ρ' _ hG' m hk2) hw
  | load t ha _ ih =>
    intro hD curD b ρ plan hG m hw
    dsimp only [wp, addrRangeSweep] at hw ⊢
    rcases hw with ⟨v, hv, hk⟩
    exact ⟨v, ha.arOut_val hG ▸ hv,
      ih (ARVal.fresh v b curD) v hD curD (b + 1) (fupd ρ b v) _ (hG.freshOne curD v) m hk⟩
  | store hv ha _ ih =>
    intro hD curD b ρ plan hG m hw
    dsimp only [wp, addrRangeSweep] at hw ⊢
    rw [ha.arOut_val hG, hv.arOut_val hG]
    exact ⟨hw.1, ih hD curD b ρ _ hG _ hw.2⟩
  | call f hargs _ ih =>
    intro hD curD b ρ plan hG m hw
    dsimp only [wp, addrRangeSweep] at hw ⊢
    rcases hw with ⟨P, E, hΓ, hP, hE⟩
    rw [hargs.arOut_vals hG]
    exact ⟨P, E, hΓ, fun r m' hp =>
      ih (freshARVals curD _ r b) r hD curD (b + _) (fupdTup ρ b r) _
        (hG.freshARVals curD r) m' (hP r m' hp), hE⟩
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hc _ _ iht ihe =>
    intro hD curD b ρ plan hG m hw
    dsimp only [wp] at hw
    have hcv := hc.arOut_val hG
    dsimp only [addrRangeSweep]
    cases hcf : c₁.arOut with
    | imm bv =>
      rw [hcf] at hcv
      cases bv
      · exact ihe hD curD b ρ _ hG m (hw.2 hcv.symm)
      · exact iht hD curD b ρ _ hG m (hw.1 hcv.symm)
    | var _ =>
      rw [hcf] at hcv; dsimp only [wp]
      exact ⟨fun h => iht hD curD b ρ _ hG m (hw.1 (hcv ▸ h)),
             fun h => ihe hD curD b ρ _ hG m (hw.2 (hcv ▸ h))⟩
  | jump hj hargs =>
    intro hD _ _ _ _ hG _ hw
    have hj' := hD _ hj; dsimp only at hj'
    dsimp only [wp, addrRangeSweep] at hw ⊢
    rw [hj', hargs.arOut_vals hG]; exact hw
  | ret hvs | exit _ hvs =>
    intro _ _ _ _ _ hG _ hw
    dsimp only [wp, addrRangeSweep] at hw ⊢
    rw [hvs.arOut_vals hG]; exact hw
  | hlt =>
    intro _ _ _ _ _ _ _ hw; exact hw
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro hD curD b ρ plan hG m hw
    dsimp only [wp, addrRangeSweep] at hw ⊢
    intro Js hclosed
    refine ihk Js Js (tup_zip_self_eq hD Js) curD b ρ _ hG m (hw Js ?_)
    rw [closed_iff] at hclosed ⊢
    intro ts i xs m' hb
    let p := plan.stepGroup.1.get i
    let bd := if p.1 then curD + 1 else curD
    have hsw := ihb Js Js i (freshARVals bd ts xs b) xs (tup_zip_self_eq hD Js)
      bd (b + ts.length) (fupdTup ρ b xs) p.2 (hG.freshARVals bd xs) m' hb
    rw [← addrRangeSweepB_get_eq curD b plan.stepGroup.1 (b₁ Js) i xs] at hsw
    exact hclosed i xs m' hsw

/-! ## Relational well-formedness (`ARRelG` and `addrRangeSweep_wf`) -/

section
variable {V₁ V₂ : Ty → Type}

inductive CmpImmRel (G' : Ctx V₁ V₂) : CmpImmDef V₁ → CmpImmDef V₂ → Prop
  | mk {w : Nat} (o : CmpOp) {lhs₁ : Arg V₁ (.bits w)} {lhs₂ : Arg V₂ (.bits w)}
      (hlhs : ArgRel G' (.bits w) lhs₁ lhs₂) (lhsKey : FKey (.bits w)) (imm : BitVec w) :
      CmpImmRel G' ⟨w, o, lhs₁, lhsKey, imm⟩ ⟨w, o, lhs₂, lhsKey, imm⟩

theorem CmpImmRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂)
    {c₁ : CmpImmDef V₁} {c₂ : CmpImmDef V₂} :
    CmpImmRel G₁ c₁ c₂ → CmpImmRel G₂ c₁ c₂
  | .mk o hlhs k imm => .mk o (hlhs.weaken hsub) k imm

inductive ZextDefRel (G' : Ctx V₁ V₂) {n : Nat} : ZextDef V₁ n → ZextDef V₂ n → Prop
  | mk {m : Nat} (hm0 : 0 < m) (hmn : m < n)
      {src₁ : Arg V₁ (.bits m)} {src₂ : Arg V₂ (.bits m)}
      (hsrc : ArgRel G' (.bits m) src₁ src₂) (srcKey : FKey (.bits m)) :
      ZextDefRel G' ⟨m, hm0, hmn, src₁, srcKey⟩ ⟨m, hm0, hmn, src₂, srcKey⟩

theorem ZextDefRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂) {n : Nat}
    {z₁ : ZextDef V₁ n} {z₂ : ZextDef V₂ n} :
    ZextDefRel G₁ z₁ z₂ → ZextDefRel G₂ z₁ z₂
  | .mk hm0 hmn hs k => .mk hm0 hmn (hs.weaken hsub) k

inductive AddrDefRel (G' : Ctx V₁ V₂) {n : Nat} : AddrDef V₁ n → AddrDef V₂ n → Prop
  | addVC {x₁ : Arg V₁ (.bits n)} {x₂ : Arg V₂ (.bits n)}
      (hx : ArgRel G' (.bits n) x₁ x₂) (dx : Nat) (disp : BitVec n) :
      AddrDefRel G' (.addVC x₁ dx disp) (.addVC x₂ dx disp)
  | shlVC {x₁ : Arg V₁ (.bits n)} {x₂ : Arg V₂ (.bits n)}
      (hx : ArgRel G' (.bits n) x₁ x₂) (dx sh : Nat) (hsh : sh < n) (disp : BitVec n) :
      AddrDefRel G' (.shlVC x₁ dx sh hsh disp) (.shlVC x₂ dx sh hsh disp)
  | addVV {x₁ : Arg V₁ (.bits n)} {x₂ : Arg V₂ (.bits n)}
      {y₁ : Arg V₁ (.bits n)} {y₂ : Arg V₂ (.bits n)}
      (hx : ArgRel G' (.bits n) x₁ x₂) (dx : Nat)
      (hy : ArgRel G' (.bits n) y₁ y₂) (dy : Nat) (disp : BitVec n) :
      AddrDefRel G' (.addVV x₁ dx y₁ dy disp) (.addVV x₂ dx y₂ dy disp)
  | subVV {x₁ : Arg V₁ (.bits n)} {x₂ : Arg V₂ (.bits n)}
      {y₁ : Arg V₁ (.bits n)} {y₂ : Arg V₂ (.bits n)}
      (hx : ArgRel G' (.bits n) x₁ x₂) (dx : Nat)
      (hy : ArgRel G' (.bits n) y₁ y₂) (dy : Nat) (disp : BitVec n) :
      AddrDefRel G' (.subVV x₁ dx y₁ dy disp) (.subVV x₂ dx y₂ dy disp)
  | shlAddVV {x₁ : Arg V₁ (.bits n)} {x₂ : Arg V₂ (.bits n)}
      {y₁ : Arg V₁ (.bits n)} {y₂ : Arg V₂ (.bits n)}
      (hx : ArgRel G' (.bits n) x₁ x₂) (dx : Nat)
      (hy : ArgRel G' (.bits n) y₁ y₂) (dy : Nat)
      (sh : Nat) (hsh : sh < n) (disp : BitVec n) :
      AddrDefRel G' (.shlAddVV x₁ dx y₁ dy sh hsh disp) (.shlAddVV x₂ dx y₂ dy sh hsh disp)
  | shlSubVV {x₁ : Arg V₁ (.bits n)} {x₂ : Arg V₂ (.bits n)}
      {y₁ : Arg V₁ (.bits n)} {y₂ : Arg V₂ (.bits n)}
      (hx : ArgRel G' (.bits n) x₁ x₂) (dx : Nat)
      (hy : ArgRel G' (.bits n) y₁ y₂) (dy : Nat)
      (sh : Nat) (hsh : sh < n) (disp : BitVec n) :
      AddrDefRel G' (.shlSubVV x₁ dx y₁ dy sh hsh disp) (.shlSubVV x₂ dx y₂ dy sh hsh disp)

theorem AddrDefRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂) {n : Nat}
    {a₁ : AddrDef V₁ n} {a₂ : AddrDef V₂ n} :
    AddrDefRel G₁ a₁ a₂ → AddrDefRel G₂ a₁ a₂
  | .addVC hx dx d => .addVC (hx.weaken hsub) dx d
  | .shlVC hx dx sh hsh d => .shlVC (hx.weaken hsub) dx sh hsh d
  | .addVV hx dx hy dy d => .addVV (hx.weaken hsub) dx (hy.weaken hsub) dy d
  | .subVV hx dx hy dy d => .subVV (hx.weaken hsub) dx (hy.weaken hsub) dy d
  | .shlAddVV hx dx hy dy sh hsh d => .shlAddVV (hx.weaken hsub) dx (hy.weaken hsub) dy sh hsh d
  | .shlSubVV hx dx hy dy sh hsh d => .shlSubVV (hx.weaken hsub) dx (hy.weaken hsub) dy sh hsh d

theorem AddrDefRel.shiftDisp {G' : Ctx V₁ V₂} {n : Nat} (c : BitVec n)
    {a₁ : AddrDef V₁ n} {a₂ : AddrDef V₂ n} :
    AddrDefRel G' a₁ a₂ → AddrDefRel G' (a₁.shiftDisp c) (a₂.shiftDisp c)
  | .addVC hx dx d => .addVC hx dx (d + c)
  | .shlVC hx dx sh hsh d => .shlVC hx dx sh hsh (d + c)
  | .addVV hx dx hy dy d => .addVV hx dx hy dy (d + c)
  | .subVV hx dx hy dy d => .subVV hx dx hy dy (d + c)
  | .shlAddVV hx dx hy dy sh hsh d => .shlAddVV hx dx hy dy sh hsh (d + c)
  | .shlSubVV hx dx hy dy sh hsh d => .shlSubVV hx dx hy dy sh hsh (d + c)

def OptRel {α : Type} {β : Type} (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

theorem OptRel.weaken {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {x : Option α} {y : Option β}, OptRel R x y → OptRel S x y
  | none, none, _ => trivial
  | some a, some b, hab => h a b hab
  | none, some _, h0 => False.elim h0
  | some _, none, h0 => False.elim h0

def BitsProvRel (G' : Ctx V₁ V₂) {n : Nat} (p₁ : BitsProv V₁ n) (p₂ : BitsProv V₂ n) : Prop :=
  OptRel (AddrDefRel G') p₁.addr? p₂.addr? ∧ OptRel (ZextDefRel G') p₁.zext? p₂.zext?

theorem BitsProvRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂) {n : Nat}
    {p₁ : BitsProv V₁ n} {p₂ : BitsProv V₂ n} (h : BitsProvRel G₁ p₁ p₂) :
    BitsProvRel G₂ p₁ p₂ :=
  ⟨h.1.weaken (fun _ _ hr => hr.weaken hsub), h.2.weaken (fun _ _ hr => hr.weaken hsub)⟩

def ARProvRel (G' : Ctx V₁ V₂) : {t : Ty} → ARProv V₁ t → ARProv V₂ t → Prop
  | .bool, none, none => True
  | .bool, some c₁, some c₂ => CmpImmRel G' c₁ c₂
  | .bool, _, _ => False
  | .bits _, bp₁, bp₂ => BitsProvRel G' bp₁ bp₂
  | .float _, (), () => True
  | .pair _ _, (), () => True

theorem ARProvRel.none {G' : Ctx V₁ V₂} {t : Ty} :
    ARProvRel G' (ARProv.none (V := V₁) (t := t)) (ARProv.none (V := V₂) (t := t)) := by
  cases t with
  | bits _ => exact ⟨trivial, trivial⟩
  | bool | float _ | pair _ _ => trivial

theorem ARProvRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂)
    {t : Ty} {p₁ : ARProv V₁ t} {p₂ : ARProv V₂ t} (h : ARProvRel G₁ p₁ p₂) :
    ARProvRel G₂ p₁ p₂ := by
  cases t with
  | bool =>
    cases p₁ <;> cases p₂ <;> first | trivial | exact False.elim h | exact CmpImmRel.weaken hsub h
  | bits _ => exact BitsProvRel.weaken hsub h
  | float _ | pair _ _ => trivial

def ARValRel (G' : Ctx V₁ V₂) {t : Ty} (a₁ : ARVal V₁ t) (a₂ : ARVal V₂ t) : Prop :=
  ArgRel G' t a₁.out a₂.out ∧ a₁.key = a₂.key ∧ a₁.depth = a₂.depth ∧ ARProvRel G' a₁.prov a₂.prov

theorem ARValRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂)
    {t : Ty} {a₁ : ARVal V₁ t} {a₂ : ARVal V₂ t} (h : ARValRel G₁ a₁ a₂) :
    ARValRel G₂ a₁ a₂ :=
  ⟨h.1.weaken hsub, h.2.1, h.2.2.1, h.2.2.2.weaken hsub⟩

theorem ARValRel.fresh {G' : Ctx V₁ V₂} {t : Ty} {v₁ : V₁ t} {v₂ : V₂ t} (b d : Nat)
    (hm : ⟨t, v₁, v₂⟩ ∈ G') :
    ARValRel G' (ARVal.fresh v₁ b d) (ARVal.fresh v₂ b d) :=
  ⟨.var hm, rfl, rfl, ARProvRel.none⟩

theorem ARValRel.ofImm {G' : Ctx V₁ V₂} {t : Ty} (c : Val t) :
    ARValRel G' (ARVal.ofImm (V := V₁) c) (ARVal.ofImm (V := V₂) c) :=
  ⟨.imm c, rfl, rfl, ARProvRel.none⟩

def ARRelG (G' : Ctx V₁ V₂) (G : Ctx (ARVal V₁) (ARVal V₂)) : Prop :=
  ∀ p ∈ G, ARValRel G' p.2.1 p.2.2

theorem ARRelG.cons {G' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)} (hG : ARRelG G' G)
    {t : Ty} {a₁ : ARVal V₁ t} {a₂ : ARVal V₂ t} (ha : ARValRel G' a₁ a₂) :
    ARRelG G' (⟨t, a₁, a₂⟩ :: G)
  | _, .head _ => ha
  | _, .tail _ hp => hG _ hp

theorem ARRelG.append {G' : Ctx V₁ V₂} {G H : Ctx (ARVal V₁) (ARVal V₂)}
    (h1 : ARRelG G' G) (h2 : ARRelG G' H) : ARRelG G' (H ++ G) := by
  intro p hp; rcases List.mem_append.1 hp with hp | hp
  · exact h2 p hp
  · exact h1 p hp

theorem ARRelG.weaken {G' G'' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)}
    (hG : ARRelG G' G) (hsub : ∀ p ∈ G', p ∈ G'') : ARRelG G'' G :=
  fun p hp => (hG p hp).weaken hsub

theorem ARRelG.append_tup {G' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)} (hG : ARRelG G' G) :
    {ts : List Ty} → {r₁ : Tup (ARVal V₁) ts} → {r₂ : Tup (ARVal V₂) ts} →
    TRel (fun _ => ARValRel G') r₁ r₂ → ARRelG G' (Tup.zip r₁ r₂ ++ G)
  | [], (), (), .nil => hG
  | _ :: _, (_, _), (_, _), .cons hr hs => (ARRelG.append_tup hG hs).cons hr

private theorem ARRelG.freshARVals_only (d : Nat) {ts : List Ty}
    (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) (b : Nat) :
    ARRelG (Tup.zip xs₁ xs₂) (Tup.zip (freshARVals d ts xs₁ b) (freshARVals d ts xs₂ b)) :=
  mem_tup_zip_tupFreshWith (fun x n => ARVal.fresh x n d) (fun x n => ARVal.fresh x n d)
    (P := fun G' _ c₁ c₂ => ARValRel G' c₁ c₂)
    (fun hsub _ _ _ h => h.weaken hsub)
    (fun _ _ idx => ARValRel.fresh idx d List.mem_cons_self)
    xs₁ xs₂ b

theorem ARRelG.freshARVals {G' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)} (hG : ARRelG G' G)
    (d : Nat) {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) (b : Nat) :
    ARRelG (Tup.zip xs₁ xs₂ ++ G')
      (Tup.zip (freshARVals d ts xs₁ b) (freshARVals d ts xs₂ b) ++ G) :=
  (hG.weaken fun _ hq => List.mem_append_right _ hq).append
    ((ARRelG.freshARVals_only d xs₁ xs₂ b).weaken fun _ hq => List.mem_append_left G' hq)

theorem ARRelG.freshOne {G' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)} (hG : ARRelG G' G)
    (d : Nat) {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) (b : Nat) :
    ARRelG (⟨t, v₁, v₂⟩ :: G') (⟨t, ARVal.fresh v₁ b d, ARVal.fresh v₂ b d⟩ :: G) :=
  (hG.weaken fun _ hq => List.mem_cons_of_mem _ hq).cons
    (ARValRel.fresh b d List.mem_cons_self)

theorem TRel.freshARVals_rel {G' : Ctx V₁ V₂} (d : Nat) {ts : List Ty}
    (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) (b : Nat) :
    TRel (fun _ => ARValRel (Tup.zip xs₁ xs₂ ++ G'))
      (freshARVals d ts xs₁ b) (freshARVals d ts xs₂ b) :=
  TRel_tupFreshWith (fun x n => ARVal.fresh x n d) (fun x n => ARVal.fresh x n d)
    (P := fun G' _ c₁ c₂ => ARValRel G' c₁ c₂)
    (fun hsub _ _ _ h => h.weaken hsub)
    (fun _ _ idx => ARValRel.fresh idx d List.mem_cons_self)
    xs₁ xs₂ b

theorem ArgRel.arOut {G' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)} (hG : ARRelG G' G)
    {t : Ty} {a₁ : Arg (ARVal V₁) t} {a₂ : Arg (ARVal V₂) t} :
    ArgRel G t a₁ a₂ → ArgRel G' t a₁.arOut a₂.arOut
  | .var h => (hG _ h).1
  | .imm c => .imm c

theorem ArgRel.arKey_eq {G' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)} (hG : ARRelG G' G)
    {t : Ty} {a₁ : Arg (ARVal V₁) t} {a₂ : Arg (ARVal V₂) t} :
    ArgRel G t a₁ a₂ → a₁.arKey = a₂.arKey
  | .var h => (hG _ h).2.1
  | .imm _ => rfl

theorem ArgRel.arDepth_eq {G' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)} (hG : ARRelG G' G)
    {t : Ty} {a₁ : Arg (ARVal V₁) t} {a₂ : Arg (ARVal V₂) t} :
    ArgRel G t a₁ a₂ → a₁.arDepth = a₂.arDepth
  | .var h => (hG _ h).2.2.1
  | .imm _ => rfl

theorem ArgRel.arProv_rel {G' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)} (hG : ARRelG G' G)
    {t : Ty} {a₁ : Arg (ARVal V₁) t} {a₂ : Arg (ARVal V₂) t} :
    ArgRel G t a₁ a₂ → ARProvRel G' a₁.arProv a₂.arProv
  | .var h => (hG _ h).2.2.2
  | .imm _ => ARProvRel.none

theorem ArgRel.toARVal_rel {G' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)} (hG : ARRelG G' G)
    {t : Ty} {a₁ : Arg (ARVal V₁) t} {a₂ : Arg (ARVal V₂) t} :
    ArgRel G t a₁ a₂ → ARValRel G' a₁.toARVal a₂.toARVal
  | .var h => hG _ h
  | .imm c => ARValRel.ofImm c

theorem TRel.arOut {G' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)} (hG : ARRelG G' G)
    {ts : List Ty} {as₁ : Tup (Arg (ARVal V₁)) ts} {as₂ : Tup (Arg (ARVal V₂)) ts}
    (h : TRel (ArgRel G) as₁ as₂) : TRel (ArgRel G') (tupArOut as₁) (tupArOut as₂) :=
  TRel.tupMapArg_rel (fun _ => Arg.arOut) (fun _ => Arg.arOut) (fun ha => ha.arOut hG) h

theorem TRel.tupMaxDepth_eq {G' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)} (hG : ARRelG G' G) :
    {ts : List Ty} → {as₁ : Tup (Arg (ARVal V₁)) ts} → {as₂ : Tup (Arg (ARVal V₂)) ts} →
    TRel (ArgRel G) as₁ as₂ → tupMaxDepth as₁ = tupMaxDepth as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons ha has => by
    dsimp only [tupMaxDepth]; rw [ha.arDepth_eq hG, TRel.tupMaxDepth_eq hG has]

private theorem argRel_imm?_eq {G' : Ctx V₁ V₂} {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} :
    ArgRel G' t a₁ a₂ → a₁.imm? = a₂.imm?
  | .var _ | .imm _ => rfl

private theorem recordAddProv_rel {G' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)}
    (hG : ARRelG G' G) {n : Nat} {a₁ b₁ : Arg (ARVal V₁) (.bits n)}
    {a₂ b₂ : Arg (ARVal V₂) (.bits n)} (ha : ArgRel G (.bits n) a₁ a₂)
    (hb : ArgRel G (.bits n) b₁ b₂) :
    OptRel (AddrDefRel G') (recordAddProv a₁ b₁) (recordAddProv a₂ b₂) := by
  dsimp only [recordAddProv]
  split
  · trivial
  · rw [argRel_imm?_eq (ha.arOut hG), argRel_imm?_eq (hb.arOut hG)]
    cases a₂.arOut.imm? <;> cases b₂.arOut.imm?
    · have hp1 := (ha.arProv_rel hG).1
      have hp2 := (hb.arProv_rel hG).1
      rw [ha.arDepth_eq hG, hb.arDepth_eq hG]
      cases h1 : a₁.arProv.addr? <;> cases h2 : a₂.arProv.addr? <;> rw [h1, h2] at hp1
      · cases h3 : b₁.arProv.addr? <;> cases h4 : b₂.arProv.addr? <;> rw [h3, h4] at hp2
        · exact .addVV (ha.arOut hG) _ (hb.arOut hG) _ 0#n
        · exact False.elim hp2
        · exact False.elim hp2
        · cases hp2 with
          | addVC hy dy d2 => exact .addVV (ha.arOut hG) _ hy dy d2
          | _ => exact .addVV (ha.arOut hG) _ (hb.arOut hG) _ 0#n
      · exact False.elim hp1
      · exact False.elim hp1
      · cases hp1 with
        | addVC hx dx d1 =>
          cases h3 : b₁.arProv.addr? <;> cases h4 : b₂.arProv.addr? <;> rw [h3, h4] at hp2
          · exact .addVV hx dx (hb.arOut hG) _ d1
          · exact False.elim hp2
          · exact False.elim hp2
          · cases hp2 with
            | addVC hy dy d2 => exact .addVV hx dx hy dy (d1 + d2)
            | _ => exact .addVV hx dx (hb.arOut hG) _ d1
        | shlVC hx dx sh1 hsh1 d1 =>
          cases h3 : b₁.arProv.addr? <;> cases h4 : b₂.arProv.addr? <;> rw [h3, h4] at hp2
          · exact .addVV (ha.arOut hG) _ (hb.arOut hG) _ 0#n
          · exact False.elim hp2
          · exact False.elim hp2
          · cases hp2 with
            | addVC hy dy d2 => exact .addVV (ha.arOut hG) _ hy dy d2
            | shlVC hy dy sh2 hsh2 d2 =>
              dsimp only; split
              · exact .shlAddVV hx dx hy dy sh1 hsh1 (d1 + d2)
              · exact .addVV (ha.arOut hG) _ (hb.arOut hG) _ 0#n
            | _ => exact .addVV (ha.arOut hG) _ (hb.arOut hG) _ 0#n
        | _ =>
          cases h3 : b₁.arProv.addr? <;> cases h4 : b₂.arProv.addr? <;> rw [h3, h4] at hp2
          · exact .addVV (ha.arOut hG) _ (hb.arOut hG) _ 0#n
          · exact False.elim hp2
          · exact False.elim hp2
          · cases hp2 with
            | addVC hy dy d2 => exact .addVV (ha.arOut hG) _ hy dy d2
            | _ => exact .addVV (ha.arOut hG) _ (hb.arOut hG) _ 0#n
    · rename_i c
      have hp := (ha.arProv_rel hG).1
      cases h1 : a₁.arProv.addr? <;> cases h2 : a₂.arProv.addr? <;> rw [h1, h2] at hp
      · rw [ha.arDepth_eq hG]; exact .addVC (ha.arOut hG) _ c
      · exact False.elim hp
      · exact False.elim hp
      · exact hp.shiftDisp c
    · rename_i c
      have hp := (hb.arProv_rel hG).1
      cases h1 : b₁.arProv.addr? <;> cases h2 : b₂.arProv.addr? <;> rw [h1, h2] at hp
      · rw [hb.arDepth_eq hG]; exact .addVC (hb.arOut hG) _ c
      · exact False.elim hp
      · exact False.elim hp
      · exact hp.shiftDisp c
    · trivial

private theorem recordSubProv_rel {G' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)}
    (hG : ARRelG G' G) {n : Nat} {a₁ b₁ : Arg (ARVal V₁) (.bits n)}
    {a₂ b₂ : Arg (ARVal V₂) (.bits n)} (ha : ArgRel G (.bits n) a₁ a₂)
    (hb : ArgRel G (.bits n) b₁ b₂) :
    OptRel (AddrDefRel G') (recordSubProv a₁ b₁) (recordSubProv a₂ b₂) := by
  dsimp only [recordSubProv]
  split
  · trivial
  · rw [argRel_imm?_eq (ha.arOut hG), argRel_imm?_eq (hb.arOut hG)]
    cases a₂.arOut.imm? <;> cases b₂.arOut.imm?
    · have hp1 := (ha.arProv_rel hG).1
      have hp2 := (hb.arProv_rel hG).1
      rw [ha.arDepth_eq hG, hb.arDepth_eq hG]
      cases h1 : a₁.arProv.addr? <;> cases h2 : a₂.arProv.addr? <;> rw [h1, h2] at hp1
      · cases h3 : b₁.arProv.addr? <;> cases h4 : b₂.arProv.addr? <;> rw [h3, h4] at hp2
        · exact .subVV (ha.arOut hG) _ (hb.arOut hG) _ 0#n
        · exact False.elim hp2
        · exact False.elim hp2
        · cases hp2 with
          | addVC hy dy d2 => exact .subVV (ha.arOut hG) _ hy dy (-d2)
          | _ => exact .subVV (ha.arOut hG) _ (hb.arOut hG) _ 0#n
      · exact False.elim hp1
      · exact False.elim hp1
      · cases hp1 with
        | addVC hx dx d1 =>
          cases h3 : b₁.arProv.addr? <;> cases h4 : b₂.arProv.addr? <;> rw [h3, h4] at hp2
          · exact .subVV hx dx (hb.arOut hG) _ d1
          · exact False.elim hp2
          · exact False.elim hp2
          · cases hp2 with
            | addVC hy dy d2 => exact .subVV hx dx hy dy (d1 - d2)
            | _ => exact .subVV hx dx (hb.arOut hG) _ d1
        | shlVC hx dx sh1 hsh1 d1 =>
          cases h3 : b₁.arProv.addr? <;> cases h4 : b₂.arProv.addr? <;> rw [h3, h4] at hp2
          · exact .subVV (ha.arOut hG) _ (hb.arOut hG) _ 0#n
          · exact False.elim hp2
          · exact False.elim hp2
          · cases hp2 with
            | addVC hy dy d2 => exact .subVV (ha.arOut hG) _ hy dy (-d2)
            | shlVC hy dy sh2 hsh2 d2 =>
              dsimp only; split
              · exact .shlSubVV hx dx hy dy sh1 hsh1 (d1 - d2)
              · exact .subVV (ha.arOut hG) _ (hb.arOut hG) _ 0#n
            | _ => exact .subVV (ha.arOut hG) _ (hb.arOut hG) _ 0#n
        | _ =>
          cases h3 : b₁.arProv.addr? <;> cases h4 : b₂.arProv.addr? <;> rw [h3, h4] at hp2
          · exact .subVV (ha.arOut hG) _ (hb.arOut hG) _ 0#n
          · exact False.elim hp2
          · exact False.elim hp2
          · cases hp2 with
            | addVC hy dy d2 => exact .subVV (ha.arOut hG) _ hy dy (-d2)
            | _ => exact .subVV (ha.arOut hG) _ (hb.arOut hG) _ 0#n
    · rename_i c
      have hp := (ha.arProv_rel hG).1
      cases h1 : a₁.arProv.addr? <;> cases h2 : a₂.arProv.addr? <;> rw [h1, h2] at hp
      · rw [ha.arDepth_eq hG]; exact .addVC (ha.arOut hG) _ (-c)
      · exact False.elim hp
      · exact False.elim hp
      · exact hp.shiftDisp (-c)
    · trivial
    · trivial

private theorem recordShlProv_rel {G' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)}
    (hG : ARRelG G' G) {n : Nat} {a₁ b₁ : Arg (ARVal V₁) (.bits n)}
    {a₂ b₂ : Arg (ARVal V₂) (.bits n)} (ha : ArgRel G (.bits n) a₁ a₂)
    (hb : ArgRel G (.bits n) b₁ b₂) :
    OptRel (AddrDefRel G') (recordShlProv a₁ b₁) (recordShlProv a₂ b₂) := by
  dsimp only [recordShlProv]
  split
  · trivial
  · rw [argRel_imm?_eq (hb.arOut hG)]
    cases b₂.arOut.imm? with
    | none => trivial
    | some k =>
      dsimp only; split
      · rename_i hkn
        have hp := (ha.arProv_rel hG).1
        cases h1 : a₁.arProv.addr? <;> cases h2 : a₂.arProv.addr? <;> rw [h1, h2] at hp
        · rw [ha.arDepth_eq hG]; exact .shlVC (ha.arOut hG) _ k.toNat hkn.2 0#n
        · exact False.elim hp
        · exact False.elim hp
        · cases hp with
          | addVC hx dx d => exact .shlVC hx dx k.toNat _ (d <<< k.toNat)
          | shlVC hx dx sh _ d =>
            dsimp only; split
            · exact .shlVC hx dx (sh + k.toNat) _ (d <<< k.toNat)
            · trivial
          | addVV hx dx hy dy d => exact .shlAddVV hx dx hy dy k.toNat _ (d <<< k.toNat)
          | subVV hx dx hy dy d => exact .shlSubVV hx dx hy dy k.toNat _ (d <<< k.toNat)
          | shlAddVV hx dx hy dy sh _ d =>
            dsimp only; split
            · exact .shlAddVV hx dx hy dy (sh + k.toNat) _ (d <<< k.toNat)
            · trivial
          | shlSubVV hx dx hy dy sh _ d =>
            dsimp only; split
            · exact .shlSubVV hx dx hy dy (sh + k.toNat) _ (d <<< k.toNat)
            · trivial
      · trivial

private theorem recordZextProv_rel {G' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)}
    (hG : ARRelG G' G) (m n : Nat) {a₁ : Arg (ARVal V₁) (.bits m)}
    {a₂ : Arg (ARVal V₂) (.bits m)} (ha : ArgRel G (.bits m) a₁ a₂) :
    BitsProvRel G' (recordZextProv m n a₁) (recordZextProv m n a₂) := by
  dsimp only [recordZextProv]
  split
  · rename_i hmn
    have hp := (ha.arProv_rel hG).2
    cases h1 : a₁.arProv.zext? <;> cases h2 : a₂.arProv.zext? <;> rw [h1, h2] at hp
    · refine ⟨trivial, ?_⟩
      rw [ha.arKey_eq hG]; exact .mk hmn.1 hmn.2 (ha.arOut hG) _
    · exact False.elim hp
    · exact False.elim hp
    · cases hp with
      | mk hm0 hmn0 hs k => exact ⟨trivial, .mk hm0 (Nat.lt_trans hmn0 hmn.2) hs k⟩
  · exact ⟨trivial, trivial⟩

private theorem mkCmpImmFromArg_rel {G' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)}
    (hG : ARRelG G' G) {n : Nat} (o : CmpOp) {a₁ : Arg (ARVal V₁) (.bits n)}
    {a₂ : Arg (ARVal V₂) (.bits n)} (ha : ArgRel G (.bits n) a₁ a₂) (c : BitVec n) :
    CmpImmRel G' (mkCmpImmFromArg o a₁ c) (mkCmpImmFromArg o a₂ c) := by
  dsimp only [mkCmpImmFromArg]
  have hp := (ha.arProv_rel hG).2
  cases h1 : a₁.arProv.zext? <;> cases h2 : a₂.arProv.zext? <;> rw [h1, h2] at hp
  · rw [ha.arKey_eq hG]; exact .mk o (ha.arOut hG) _ c
  · exact False.elim hp
  · exact False.elim hp
  · cases hp with
    | mk hm0 hmn hs k =>
      dsimp only; split
      · exact .mk _ hs k _
      · rw [ha.arKey_eq hG]; exact .mk o (ha.arOut hG) _ c

private theorem recordCmpImmProv_rel {G' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)}
    (hG : ARRelG G' G) {w : Nat} (o : CmpOp) {a₁ b₁ : Arg (ARVal V₁) (.bits w)}
    {a₂ b₂ : Arg (ARVal V₂) (.bits w)} (ha : ArgRel G (.bits w) a₁ a₂)
    (hb : ArgRel G (.bits w) b₁ b₂) :
    ARProvRel G' (t := .bool) (recordCmpImmProv o a₁ b₁) (recordCmpImmProv o a₂ b₂) := by
  dsimp only [recordCmpImmProv]
  rw [argRel_imm?_eq (ha.arOut hG), argRel_imm?_eq (hb.arOut hG)]
  cases a₂.arOut.imm? <;> cases b₂.arOut.imm?
  · trivial
  · exact mkCmpImmFromArg_rel hG o ha _
  · exact mkCmpImmFromArg_rel hG o.swap hb _
  · exact mkCmpImmFromArg_rel hG o ha _

private theorem wrapKept_rel {G' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)}
    (hG : ARRelG G' G) (outD b : Nat) {sig ts : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg (ARVal V₁)) sig} {args₂ : Tup (Arg (ARVal V₂)) sig}
    (hargs : TRel (ArgRel G) args₁ args₂) (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) :
    TRel (fun _ => ARValRel (Tup.zip xs₁ xs₂ ++ G'))
      (wrapKept outD b code args₁ xs₁) (wrapKept outD b code args₂ xs₂) := by
  have hsub : ∀ p ∈ G', p ∈ Tup.zip xs₁ xs₂ ++ G' := fun _ hq => List.mem_append_right _ hq
  cases code with
  | add t =>
    cases t with
    | bits n =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      exact .cons ⟨.var List.mem_cons_self, rfl, rfl,
        ⟨(recordAddProv_rel hG ha hb).weaken (fun _ _ h => h.weaken hsub), trivial⟩⟩ .nil
    | bool | float _ | pair _ _ => exact TRel.freshARVals_rel outD xs₁ xs₂ b
  | sub t =>
    cases t with
    | bits n =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      exact .cons ⟨.var List.mem_cons_self, rfl, rfl,
        ⟨(recordSubProv_rel hG ha hb).weaken (fun _ _ h => h.weaken hsub), trivial⟩⟩ .nil
    | bool | float _ | pair _ _ => exact TRel.freshARVals_rel outD xs₁ xs₂ b
  | shl t =>
    cases t with
    | bits n =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      exact .cons ⟨.var List.mem_cons_self, rfl, rfl,
        ⟨(recordShlProv_rel hG ha hb).weaken (fun _ _ h => h.weaken hsub), trivial⟩⟩ .nil
    | bool | float _ | pair _ _ => exact TRel.freshARVals_rel outD xs₁ xs₂ b
  | zext m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    exact .cons ⟨.var List.mem_cons_self, rfl, rfl,
      (recordZextProv_rel hG m n ha).weaken hsub⟩ .nil
  | copy t =>
    cases t with
    | bits n =>
      rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
      rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _⟩
      exact .cons ⟨.var List.mem_cons_self, rfl, rfl,
        (ha.arProv_rel hG).weaken hsub⟩ .nil
    | bool =>
      rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
      rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _⟩
      exact .cons ⟨.var List.mem_cons_self, rfl, rfl,
        (ha.arProv_rel hG).weaken hsub⟩ .nil
    | float _ | pair _ _ => exact TRel.freshARVals_rel outD xs₁ xs₂ b
  | cmp o t m hm =>
    cases t with
    | bits w =>
      subst hm
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      exact .cons ⟨.var List.mem_cons_self, rfl, rfl,
        (recordCmpImmProv_rel hG o ha hb).weaken hsub⟩ .nil
    | bool | float _ | pair _ _ => exact TRel.freshARVals_rel outD xs₁ xs₂ b
  | not t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
      rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _⟩
      have hp := ha.arProv_rel hG
      have hneg : ARProvRel G' (t := .bool)
          (a₁.arProv.map fun cm => ⟨cm.w, cm.op.neg, cm.lhs, cm.lhsKey, cm.imm⟩)
          (a₂.arProv.map fun cm => ⟨cm.w, cm.op.neg, cm.lhs, cm.lhsKey, cm.imm⟩) := by
        cases h1 : a₁.arProv <;> cases h2 : a₂.arProv <;> rw [h1, h2] at hp
        · trivial
        · exact False.elim hp
        · exact False.elim hp
        · cases hp with
          | mk o hlhs k imm => exact .mk o.neg hlhs k imm
      exact .cons ⟨.var List.mem_cons_self, rfl, rfl, hneg.weaken hsub⟩ .nil
    | bits _ | float _ | pair _ _ => exact TRel.freshARVals_rel outD xs₁ xs₂ b
  | _ =>
    all_goals exact TRel.freshARVals_rel outD xs₁ xs₂ b

inductive ARStepRel (G' : Ctx V₁ V₂) : {ts : List Ty} → ARStep V₁ ts → ARStep V₂ ts → Prop
  | elim {ts : List Ty} {r₁ : Tup (ARVal V₁) ts} {r₂ : Tup (ARVal V₂) ts}
      (hr : TRel (fun _ => ARValRel G') r₁ r₂) : ARStepRel G' (.elim r₁) (.elim r₂)
  | emit1 {ts : List Ty} {op₁ : Op V₁ ts} {op₂ : Op V₂ ts}
      {w₁ : Tup V₁ ts → Tup (ARVal V₁) ts} {w₂ : Tup V₂ ts → Tup (ARVal V₂) ts}
      (hop : OpRel G' op₁ op₂)
      (hw : ∀ xs₁ xs₂, TRel (fun _ => ARValRel (Tup.zip xs₁ xs₂ ++ G')) (w₁ xs₁) (w₂ xs₂)) :
      ARStepRel G' (.emit1 op₁ w₁) (.emit1 op₂ w₂)
  | rangeSubCmp {w : Nat} (o : CmpOp) {x₁ : Arg V₁ (.bits w)} {x₂ : Arg V₂ (.bits w)}
      (hx : ArgRel G' (.bits w) x₁ x₂) (lo width : BitVec w) (outD : Nat) :
      ARStepRel G' (.rangeSubCmp w o x₁ lo width outD) (.rangeSubCmp w o x₂ lo width outD)
  | addrShl {n : Nat} (isSub : Bool)
      {base₁ : Arg V₁ (.bits n)} {base₂ : Arg V₂ (.bits n)}
      {inv₁ : Arg V₁ (.bits n)} {inv₂ : Arg V₂ (.bits n)}
      {iv₁ : Arg V₁ (.bits n)} {iv₂ : Arg V₂ (.bits n)}
      (hb : ArgRel G' (.bits n) base₁ base₂)
      (hinv : ArgRel G' (.bits n) inv₁ inv₂)
      (hiv : ArgRel G' (.bits n) iv₁ iv₂)
      (ivD sh : Nat) (hsh : sh < n) (disp : BitVec n) :
      ARStepRel G' (.addrShl n isSub base₁ inv₁ iv₁ ivD sh hsh disp)
        (.addrShl n isSub base₂ inv₂ iv₂ ivD sh hsh disp)
  | addrPlain {n : Nat} (isSub : Bool)
      {base₁ : Arg V₁ (.bits n)} {base₂ : Arg V₂ (.bits n)}
      {inv₁ : Arg V₁ (.bits n)} {inv₂ : Arg V₂ (.bits n)}
      {iv₁ : Arg V₁ (.bits n)} {iv₂ : Arg V₂ (.bits n)}
      (hb : ArgRel G' (.bits n) base₁ base₂)
      (hinv : ArgRel G' (.bits n) inv₁ inv₂)
      (hiv : ArgRel G' (.bits n) iv₁ iv₂)
      (invD ivD : Nat) (disp : BitVec n) :
      ARStepRel G' (.addrPlain n isSub base₁ inv₁ iv₁ invD ivD disp)
        (.addrPlain n isSub base₂ inv₂ iv₂ invD ivD disp)

private def OptARStepRel (G' : Ctx V₁ V₂) {ts : List Ty} :
    Option (ARStep V₁ ts) → Option (ARStep V₂ ts) → Prop
  | none, none => True
  | some s₁, some s₂ => ARStepRel G' s₁ s₂
  | _, _ => False

private theorem tryAddrReassocOne_rel {G' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)}
    (hG : ARRelG G' G) {n : Nat} {base₁ off₁ : Arg (ARVal V₁) (.bits n)}
    {base₂ off₂ : Arg (ARVal V₂) (.bits n)}
    (hb : ArgRel G (.bits n) base₁ base₂) (ho : ArgRel G (.bits n) off₁ off₂) :
    OptARStepRel G' (tryAddrReassocOne base₁ off₁) (tryAddrReassocOne base₂ off₂) := by
  dsimp only [tryAddrReassocOne]
  rw [argRel_imm?_eq (hb.arOut hG), hb.arDepth_eq hG]
  split
  · trivial
  · have hp := (ho.arProv_rel hG).1
    cases h1 : off₁.arProv.addr? <;> cases h2 : off₂.arProv.addr? <;> rw [h1, h2] at hp
    · trivial
    · exact False.elim hp
    · exact False.elim hp
    · cases hp with
      | addVC _ _ _ | shlVC _ _ _ _ _ => trivial
      | shlAddVV hx dx hy dy sh hsh disp =>
        dsimp only
        split
        · exact .addrShl false (hb.arOut hG) hx hy dy sh hsh disp
        · split
          · exact .addrShl false (hb.arOut hG) hy hx dx sh hsh disp
          · trivial
      | shlSubVV hx dx hy dy sh hsh disp =>
        dsimp only
        split
        · exact .addrShl true (hb.arOut hG) hy hx dx sh hsh disp
        · trivial
      | addVV hx dx hy dy disp =>
        dsimp only
        split
        · exact .addrPlain false (hb.arOut hG) hx hy _ dy disp
        · split
          · exact .addrPlain false (hb.arOut hG) hy hx _ dx disp
          · trivial
      | subVV hx dx hy dy disp =>
        dsimp only
        split
        · exact .addrPlain true (hb.arOut hG) hy hx _ dx disp
        · trivial

private theorem tryRangeStep_rel {G' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)}
    (hG : ARRelG G' G) (isOr : Bool) (outD b : Nat)
    {a₁ b₁ : Arg (ARVal V₁) .bool} {a₂ b₂ : Arg (ARVal V₂) .bool}
    (ha : ArgRel G .bool a₁ a₂) (hb : ArgRel G .bool b₁ b₂) :
    OptARStepRel G' (tryRangeStep isOr outD b a₁ b₁) (tryRangeStep isOr outD b a₂ b₂) := by
  dsimp only [tryRangeStep]
  have hp1 := ha.arProv_rel hG
  have hp2 := hb.arProv_rel hG
  cases h1 : a₁.arProv <;> cases h2 : a₂.arProv <;> rw [h1, h2] at hp1
  · trivial
  · exact False.elim hp1
  · exact False.elim hp1
  · cases h3 : b₁.arProv <;> cases h4 : b₂.arProv <;> rw [h3, h4] at hp2
    · trivial
    · exact False.elim hp2
    · exact False.elim hp2
    · cases hp1 with
      | mk o1 hlhs1 key1 imm1 =>
        cases hp2 with
        | mk o2 hlhs2 key2 imm2 =>
          dsimp only
          split
          · rename_i hw; subst hw
            dsimp only
            split
            · cases toRangeBound o1 imm1 with
              | none => trivial
              | some rb1 =>
                cases toRangeBound o2 imm2 with
                | none => trivial
                | some rb2 =>
                  dsimp only
                  cases hm : (if isOr then matchOrBounds rb1 rb2 else matchAndBounds rb1 rb2) with
                  | none => trivial
                  | some triple =>
                    rcases triple with ⟨signed, lo, hi⟩
                    dsimp only
                    cases hlt : (if signed then lo.slt hi else lo.ult hi) with
                    | false =>
                      simp only [Bool.not_false, ↓reduceIte]
                      exact .elim (.cons (ARValRel.ofImm (t := .bool) isOr) .nil)
                    | true =>
                      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                      cases hlo0 : (lo == 0#_) with
                      | true =>
                        simp only [↓reduceIte]
                        exact .emit1 (.mk _ (.cons hlhs1 (.cons (.imm (t := .bits _) hi) .nil)))
                          (fun (r₁, ()) (r₂, ()) =>
                            .cons (ARValRel.fresh b outD List.mem_cons_self) .nil)
                      | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        exact .rangeSubCmp _ hlhs1 lo (hi - lo) outD
            · trivial
          · trivial

private theorem OpRel.arStep_rel {G' : Ctx V₁ V₂} {G : Ctx (ARVal V₁) (ARVal V₂)}
    (hG : ARRelG G' G) (curD b : Nat) {sig ts : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg (ARVal V₁)) sig} {args₂ : Tup (Arg (ARVal V₂)) sig}
    (hargs : TRel (ArgRel G) args₁ args₂) :
    ARStepRel G'
      (({ code := code, args := args₁ } : Op (ARVal V₁) ts).arStep curD b)
      (({ code := code, args := args₂ } : Op (ARVal V₂) ts).arStep curD b) := by
  dsimp only [Op.arStep]
  rw [TRel.tupMaxDepth_eq hG hargs]
  have hkeep : ∀ outD, ARStepRel G'
      (.emit1 ⟨code, tupArOut args₁⟩ (wrapKept outD b code args₁))
      (.emit1 ⟨code, tupArOut args₂⟩ (wrapKept outD b code args₂)) := fun outD =>
    .emit1 (.mk code (TRel.arOut hG hargs)) (wrapKept_rel hG outD b hargs)
  cases code with
  | add t =>
    cases t with
    | bits n =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      dsimp only
      split
      · have hr1 := tryAddrReassocOne_rel hG ha hb
        cases h1 : tryAddrReassocOne a₁ b₁ <;> cases h2 : tryAddrReassocOne a₂ b₂ <;>
          rw [h1, h2] at hr1
        · have hr2 := tryAddrReassocOne_rel hG hb ha
          cases h3 : tryAddrReassocOne b₁ a₁ <;> cases h4 : tryAddrReassocOne b₂ a₂ <;>
            rw [h3, h4] at hr2
          · exact hkeep _
          · exact False.elim hr2
          · exact False.elim hr2
          · exact hr2
        · exact False.elim hr1
        · exact False.elim hr1
        · exact hr1
      · exact hkeep _
    | bool | float _ | pair _ _ => exact hkeep _
  | and t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      dsimp only
      rw [argRel_imm?_eq (ha.arOut hG), argRel_imm?_eq (hb.arOut hG)]
      split
      · exact .elim (.cons (ARValRel.ofImm (t := .bool) false) .nil)
      · split
        · exact .elim (.cons (hb.toARVal_rel hG) .nil)
        · split
          · exact .elim (.cons (ha.toARVal_rel hG) .nil)
          · let outD := if (OpCode.and .bool).isLicmPure then
              tupMaxDepth (ts := [.bool, .bool]) (a₂, b₂, ()) else curD
            have hr := tryRangeStep_rel hG false outD b ha hb
            cases h1 : tryRangeStep false outD b a₁ b₁ <;>
              cases h2 : tryRangeStep false outD b a₂ b₂ <;> rw [h1, h2] at hr
            · exact .emit1 (.mk _ (.cons (ha.arOut hG) (.cons (hb.arOut hG) .nil)))
                (fun xs₁ xs₂ => TRel.freshARVals_rel outD xs₁ xs₂ b)
            · exact False.elim hr
            · exact False.elim hr
            · exact hr
    | bits _ | float _ | pair _ _ => exact hkeep _
  | or t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      dsimp only
      rw [argRel_imm?_eq (ha.arOut hG), argRel_imm?_eq (hb.arOut hG)]
      split
      · exact .elim (.cons (ARValRel.ofImm (t := .bool) true) .nil)
      · split
        · exact .elim (.cons (hb.toARVal_rel hG) .nil)
        · split
          · exact .elim (.cons (ha.toARVal_rel hG) .nil)
          · let outD := if (OpCode.or .bool).isLicmPure then
              tupMaxDepth (ts := [.bool, .bool]) (a₂, b₂, ()) else curD
            have hr := tryRangeStep_rel hG true outD b ha hb
            cases h1 : tryRangeStep true outD b a₁ b₁ <;>
              cases h2 : tryRangeStep true outD b a₂ b₂ <;> rw [h1, h2] at hr
            · exact .emit1 (.mk _ (.cons (ha.arOut hG) (.cons (hb.arOut hG) .nil)))
                (fun xs₁ xs₂ => TRel.freshARVals_rel outD xs₁ xs₂ b)
            · exact False.elim hr
            · exact False.elim hr
            · exact hr
    | bits _ | float _ | pair _ _ => exact hkeep _
  | _ =>
    all_goals exact hkeep _

end

/-- Relational well-formedness preservation for `addrRangeSweep` under any untrusted `LoopTree`. -/
theorem addrRangeSweep_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (ARVal V₁) (ARVal V₂)} {D : Ctx L₁ L₂}
    {e₁ : Expr (ARVal V₁) L₁ rs} {e₂ : Expr (ARVal V₂) L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂}, ARRelG G' G → ∀ curD b plan,
      Wf G' D (addrRangeSweep curD b plan e₁) (addrRangeSweep curD b plan e₂) := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro G' hG curD b plan
    cases hop with
    | @mk sig _ code args₁ args₂ hargs =>
      rw [addrRangeSweep_let, addrRangeSweep_let]
      have hst := OpRel.arStep_rel hG curD b hargs (code := code)
      generalize hs1 :
        ({ code := code, args := args₁ } : Op (ARVal V₁) ts).arStep curD b = st₁ at hst
      generalize hs2 :
        ({ code := code, args := args₂ } : Op (ARVal V₂) ts).arStep curD b = st₂ at hst
      cases hst with
      | elim hr => exact ih _ _ (hG.append_tup hr) curD b _
      | emit1 hop' hw =>
        refine .let_ hop' fun xs₁ xs₂ => ?_
        have hG' : ARRelG (Tup.zip xs₁ xs₂ ++ G') G :=
          hG.weaken fun _ hq => List.mem_append_right _ hq
        exact ih _ _ (hG'.append_tup (hw xs₁ xs₂)) curD (b + ts.length) _
      | rangeSubCmp o hx lo width outD =>
        refine .let_ (.mk _ (.cons hx (.cons (.imm (t := .bits _) lo) .nil)))
          fun (t₁, ()) (t₂, ()) => ?_
        refine .let_ (.mk _ (.cons (.var List.mem_cons_self)
          (.cons (.imm (t := .bits _) width) .nil)))
          fun (r₁, ()) (r₂, ()) => ?_
        have hsub : ∀ p ∈ G', p ∈ (⟨.bool, r₁, r₂⟩ :: ⟨.bits _, t₁, t₂⟩ :: G') :=
          fun _ hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)
        exact ih (ARVal.fresh r₁ b outD, ()) (ARVal.fresh r₂ b outD, ())
          (by dsimp only [Tup.zip, List.cons_append, List.nil_append]
              exact (hG.weaken hsub).cons (ARValRel.fresh b outD List.mem_cons_self))
          curD (b + 1) _
      | addrShl isSub hb hinv hiv ivD sh hsh disp =>
        refine .let_ (.mk _ (.cons hinv (.cons (.imm (t := .bits _) _) .nil)))
          fun (t1₁, ()) (t1₂, ()) => ?_
        have hsub1 : ∀ p ∈ G', p ∈ (⟨.bits _, t1₁, t1₂⟩ :: G') :=
          fun _ hq => List.mem_cons_of_mem _ hq
        refine .let_ (.mk _ (.cons (hb.weaken hsub1) (.cons (.var List.mem_cons_self) .nil)))
          fun (t2₁, ()) (t2₂, ()) => ?_
        have hsub2 : ∀ p ∈ G', p ∈ (⟨.bits _, t2₁, t2₂⟩ :: ⟨.bits _, t1₁, t1₂⟩ :: G') :=
          fun _ hq => List.mem_cons_of_mem _ (hsub1 _ hq)
        cases hdisp : (disp == 0#_) with
        | true =>
          simp only [↓reduceIte]
          refine .let_ (.mk _ (.cons (hiv.weaken hsub2) (.cons (.imm (t := .bits _) _) .nil)))
            fun (t3₁, ()) (t3₂, ()) => ?_
          refine .let_ (.mk _ (.cons (.var (List.mem_cons_of_mem _ List.mem_cons_self))
            (.cons (.var List.mem_cons_self) .nil))) fun (t4₁, ()) (t4₂, ()) => ?_
          have hsub4 : ∀ p ∈ G',
              p ∈ (⟨.bits _, t4₁, t4₂⟩ :: ⟨.bits _, t3₁, t3₂⟩ ::
                   ⟨.bits _, t2₁, t2₂⟩ :: ⟨.bits _, t1₁, t1₂⟩ :: G') :=
            fun _ hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hsub2 _ hq))
          exact ih (ARVal.fresh t4₁ b ivD, ()) (ARVal.fresh t4₂ b ivD, ())
            (by dsimp only [Tup.zip, List.cons_append, List.nil_append]
                exact (hG.weaken hsub4).cons (ARValRel.fresh b ivD List.mem_cons_self))
            curD (b + 1) _
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases hfold : plan.foldDisp with
          | true =>
            simp only [↓reduceIte]
            refine .let_ (.mk _ (.cons (.var List.mem_cons_self)
              (.cons (.imm (t := .bits _) disp) .nil)))
              fun (t2d₁, ()) (t2d₂, ()) => ?_
            have hsub2d : ∀ p ∈ G',
                p ∈ (⟨.bits _, t2d₁, t2d₂⟩ :: ⟨.bits _, t2₁, t2₂⟩ :: ⟨.bits _, t1₁, t1₂⟩ :: G') :=
              fun _ hq => List.mem_cons_of_mem _ (hsub2 _ hq)
            refine .let_ (.mk _ (.cons (hiv.weaken hsub2d) (.cons (.imm (t := .bits _) _) .nil)))
              fun (t3₁, ()) (t3₂, ()) => ?_
            refine .let_ (.mk _ (.cons (.var (List.mem_cons_of_mem _ List.mem_cons_self))
              (.cons (.var List.mem_cons_self) .nil))) fun (t4₁, ()) (t4₂, ()) => ?_
            have hsub5 : ∀ p ∈ G',
                p ∈ (⟨.bits _, t4₁, t4₂⟩ :: ⟨.bits _, t3₁, t3₂⟩ :: ⟨.bits _, t2d₁, t2d₂⟩ ::
                     ⟨.bits _, t2₁, t2₂⟩ :: ⟨.bits _, t1₁, t1₂⟩ :: G') :=
              fun _ hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hsub2d _ hq))
            exact ih (ARVal.fresh t4₁ b ivD, ()) (ARVal.fresh t4₂ b ivD, ())
              (by dsimp only [Tup.zip, List.cons_append, List.nil_append]
                  exact (hG.weaken hsub5).cons (ARValRel.fresh b ivD List.mem_cons_self))
              curD (b + 1) _
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine .let_ (.mk _ (.cons (hiv.weaken hsub2) (.cons (.imm (t := .bits _) _) .nil)))
              fun (t3₁, ()) (t3₂, ()) => ?_
            refine .let_ (.mk _ (.cons (.var (List.mem_cons_of_mem _ List.mem_cons_self))
              (.cons (.var List.mem_cons_self) .nil))) fun (t4₁, ()) (t4₂, ()) => ?_
            refine .let_ (.mk _ (.cons (.var List.mem_cons_self)
              (.cons (.imm (t := .bits _) disp) .nil)))
              fun (t5₁, ()) (t5₂, ()) => ?_
            have hsub5 : ∀ p ∈ G',
                p ∈ (⟨.bits _, t5₁, t5₂⟩ :: ⟨.bits _, t4₁, t4₂⟩ :: ⟨.bits _, t3₁, t3₂⟩ ::
                     ⟨.bits _, t2₁, t2₂⟩ :: ⟨.bits _, t1₁, t1₂⟩ :: G') :=
              fun _ hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (hsub2 _ hq)))
            exact ih (ARVal.fresh t5₁ b ivD, ()) (ARVal.fresh t5₂ b ivD, ())
              (by dsimp only [Tup.zip, List.cons_append, List.nil_append]
                  exact (hG.weaken hsub5).cons (ARValRel.fresh b ivD List.mem_cons_self))
              curD (b + 1) _
      | addrPlain isSub hb hinv hiv invD ivD disp =>
        refine .let_ (.mk _ (.cons hb (.cons hinv .nil))) fun (t1₁, ()) (t1₂, ()) => ?_
        have hsub1 : ∀ p ∈ G', p ∈ (⟨.bits _, t1₁, t1₂⟩ :: G') :=
          fun _ hq => List.mem_cons_of_mem _ hq
        cases hdisp : (disp == 0#_) with
        | true =>
          simp only [↓reduceIte]
          refine .let_ (.mk _ (.cons (.var List.mem_cons_self) (.cons (hiv.weaken hsub1) .nil)))
            fun (t2₁, ()) (t2₂, ()) => ?_
          have hsub2 : ∀ p ∈ G', p ∈ (⟨.bits _, t2₁, t2₂⟩ :: ⟨.bits _, t1₁, t1₂⟩ :: G') :=
            fun _ hq => List.mem_cons_of_mem _ (hsub1 _ hq)
          exact ih
            (⟨.var t2₁, .var b, ivD, { addr? := some (.addVV (.var t1₁) invD _ ivD 0#_) }⟩, ())
            (⟨.var t2₂, .var b, ivD, { addr? := some (.addVV (.var t1₂) invD _ ivD 0#_) }⟩, ())
            (by dsimp only [Tup.zip, List.cons_append, List.nil_append]
                exact (hG.weaken hsub2).cons
                  ⟨.var List.mem_cons_self, rfl, rfl,
                    ⟨AddrDefRel.addVV (.var (List.mem_cons_of_mem _ List.mem_cons_self)) invD
                      (hiv.weaken hsub2) ivD 0#_, trivial⟩⟩)
            curD (b + 1) _
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases hfold : plan.foldDisp with
          | true =>
            simp only [↓reduceIte]
            refine .let_ (.mk _ (.cons (.var List.mem_cons_self)
              (.cons (.imm (t := .bits _) disp) .nil)))
              fun (t1d₁, ()) (t1d₂, ()) => ?_
            have hsub1d : ∀ p ∈ G',
                p ∈ (⟨.bits _, t1d₁, t1d₂⟩ :: ⟨.bits _, t1₁, t1₂⟩ :: G') :=
              fun _ hq => List.mem_cons_of_mem _ (hsub1 _ hq)
            refine .let_ (.mk _ (.cons (.var List.mem_cons_self) (.cons (hiv.weaken hsub1d) .nil)))
              fun (t2₁, ()) (t2₂, ()) => ?_
            have hsub3 : ∀ p ∈ G',
                p ∈ (⟨.bits _, t2₁, t2₂⟩ :: ⟨.bits _, t1d₁, t1d₂⟩ :: ⟨.bits _, t1₁, t1₂⟩ :: G') :=
              fun _ hq => List.mem_cons_of_mem _ (hsub1d _ hq)
            exact ih
              (⟨.var t2₁, .var b, ivD,
                { addr? := some (.addVV (.var t1d₁) invD _ ivD 0#_) }⟩, ())
              (⟨.var t2₂, .var b, ivD,
                { addr? := some (.addVV (.var t1d₂) invD _ ivD 0#_) }⟩, ())
              (by dsimp only [Tup.zip, List.cons_append, List.nil_append]
                  exact (hG.weaken hsub3).cons
                    ⟨.var List.mem_cons_self, rfl, rfl,
                      ⟨AddrDefRel.addVV (.var (List.mem_cons_of_mem _ List.mem_cons_self))
                        invD (hiv.weaken hsub3) ivD 0#_, trivial⟩⟩)
              curD (b + 1) _
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine .let_ (.mk _ (.cons (.var List.mem_cons_self) (.cons (hiv.weaken hsub1) .nil)))
              fun (t2₁, ()) (t2₂, ()) => ?_
            refine .let_ (.mk _ (.cons (.var List.mem_cons_self)
              (.cons (.imm (t := .bits _) disp) .nil)))
              fun (t3₁, ()) (t3₂, ()) => ?_
            have hsub3 : ∀ p ∈ G',
                p ∈ (⟨.bits _, t3₁, t3₂⟩ :: ⟨.bits _, t2₁, t2₂⟩ :: ⟨.bits _, t1₁, t1₂⟩ :: G') :=
              fun _ hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hsub1 _ hq))
            exact ih
              (⟨.var t3₁, .var b, ivD, { addr? := some (.addVV (.var t1₁) invD _ ivD disp) }⟩, ())
              (⟨.var t3₂, .var b, ivD, { addr? := some (.addVV (.var t1₂) invD _ ivD disp) }⟩, ())
              (by dsimp only [Tup.zip, List.cons_append, List.nil_append]
                  exact (hG.weaken hsub3).cons
                    ⟨.var List.mem_cons_self, rfl, rfl,
                      ⟨AddrDefRel.addVV (.var (List.mem_cons_of_mem _
                        (List.mem_cons_of_mem _ List.mem_cons_self)))
                        invD (hiv.weaken hsub3) ivD disp, trivial⟩⟩)
              curD (b + 1) _
  | load t ha _ ih =>
    intro _ hG curD b _
    exact .load t (ha.arOut hG) fun v₁ v₂ => ih _ _ (hG.freshOne curD v₁ v₂ b) curD (b + 1) _
  | store hv ha _ ih =>
    intro _ hG curD b _
    exact .store (hv.arOut hG) (ha.arOut hG) (ih hG curD b _)
  | call f hargs _ ih =>
    intro _ hG curD b _
    exact .call f (TRel.arOut hG hargs) fun xs₁ xs₂ =>
      ih _ _ (hG.freshARVals curD xs₁ xs₂ b) curD (b + _) _
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hc _ _ iht ihe =>
    intro _ hG curD b plan
    dsimp only [addrRangeSweep]
    cases hc with
    | @var v₁ v₂ h =>
      rcases v₁ with ⟨a₁, κ₁, d₁, p₁⟩; rcases v₂ with ⟨a₂, κ₂, d₂, p₂⟩
      obtain ⟨h', _, _, _⟩ := hG _ h; dsimp only at h' ⊢
      cases h' with
      | var hm => exact .jnz (.var hm) (iht hG curD b _) (ihe hG curD b _)
      | imm bv => cases bv <;> first | exact iht hG curD b _ | exact ihe hG curD b _
    | imm bv => cases bv <;> first | exact iht hG curD b _ | exact ihe hG curD b _
  | jump hj hargs =>
    intro _ hG _ _ _; exact .jump hj (TRel.arOut hG hargs)
  | ret hvs =>
    intro _ hG _ _ _; exact .ret (TRel.arOut hG hvs)
  | exit f hargs =>
    intro _ hG _ _ _; exact .exit f (TRel.arOut hG hargs)
  | hlt =>
    intro _ _ _ _ _; exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro _ hG curD b plan
    dsimp only [addrRangeSweep]
    refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_)
      (fun Js₁ Js₂ => ihk Js₁ Js₂ hG curD b _)
    simpa [addrRangeSweepB_get_eq] using
      ihb Js₁ Js₂ i _ _ (hG.freshARVals _ xs₁ xs₂ b)
        (if (plan.stepGroup.1.get i).1 then curD + 1 else curD) (b + _) (plan.stepGroup.1.get i).2

/-! ## Closed-function theorems (`Func.addrRangeOpt_wf`, `Func.addrRangeOpt_spec`) -/

/-- `Func.addrRangeOptWith` preserves relational well-formedness. -/
theorem Func.addrRangeOptWith_wf (foldDisp : Bool) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) : (Func.addrRangeOptWith foldDisp f).Wf := by
  dsimp only [Func.addrRangeOptWith]
  split
  · intro V₁ V₂ L₁ L₂ xs₁ xs₂
    have hwf := hf (ARVal V₁) (ARVal V₂) L₁ L₂ (freshARVals 0 as xs₁ 0) (freshARVals 0 as xs₂ 0)
    have hrel : ARRelG (Tup.zip xs₁ xs₂)
        (Tup.zip (freshARVals 0 as xs₁ 0) (freshARVals 0 as xs₂ 0)) := by
      simpa using ARRelG.freshARVals (G := []) (G' := []) (fun _ hp => nomatch hp) 0 xs₁ xs₂ 0
    exact addrRangeSweep_wf hwf hrel 0 as.length _
  · exact hf

/-- `Func.addrRangeOptWith` refines function contracts. -/
theorem Func.addrRangeOptWith_spec (foldDisp : Bool) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.addrRangeOptWith foldDisp f) xs m Q X := by
  dsimp only [Func.addrRangeOptWith]
  split
  · have hwf := hf (ARVal Val) Val Cont Cont (freshARVals 0 as xs 0) xs
    have hgood : ARGood (fupdTup (fun _ _ => default) 0 xs) as.length
        (Tup.zip (freshARVals 0 as xs 0) xs) := by
      simpa using ARGood.freshARVals (ρ := fun _ _ => default) (b := 0) (G := [])
        (fun _ hp => nomatch hp) 0 xs
    exact addrRangeSweep_wp hwf (fun _ hp => nomatch hp) 0 as.length _ _ hgood m h
  · exact h

/-- `Func.addrRangeOpt` preserves relational well-formedness. -/
theorem Func.addrRangeOpt_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.addrRangeOpt f).Wf :=
  Func.addrRangeOptWith_wf false hf

/-- `Func.addrRangeOpt` refines function contracts. -/
theorem Func.addrRangeOpt_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.addrRangeOpt f) xs m Q X :=
  Func.addrRangeOptWith_spec false hf h

end LeanQbe.T
