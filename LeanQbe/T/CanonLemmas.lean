module

public import LeanQbe.T.Canon
public import LeanQbe.T.Wf
public import LeanQbe.T.WP
import LeanQbe.T.WPLemmas
import LeanQbe.T.WfLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.PassEnvKit

/-!
# Correctness of `canon`

* `CmpOp.swap_evalBits`, `CmpOp.swap_evalBool`, `liftCmp_swap`, `AssocOp.eval_comm`,
  `AssocOp.eval_assoc`: leaf-wise commutativity and associativity across `.bool`, `.bits n`, and
  `.pair`/vector trees.
* `OpRel.canonLet_wp`: `canonLet` preserves `Op.wp` and the semantic invariant `CanonGood`.
* `canon_wp`: source `wp` implies canonicalized `wp`, proved via `Wf.induct`.
* `canon_wf`: `Wf` is preserved, proved via `Wf.induct` and `CanonRelG`.
* `Func.canon_spec`, `Func.canon_wf`: closed-function specifications.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## Algebraic laws for `AssocOp.eval` -/

theorem AssocOp.eval_comm (op : AssocOp) (t : Ty) (a b : Val t) :
    op.eval t a b = op.eval t b a := by
  cases op
  · exact lift2_comm (· + ·) (· ^^ ·) BitVec.add_comm Bool.xor_comm t a b
  · exact lift2_comm (· * ·) (· && ·) BitVec.mul_comm Bool.and_comm t a b
  · exact lift2_comm (· &&& ·) (· && ·) BitVec.and_comm Bool.and_comm t a b
  · exact lift2_comm (· ||| ·) (· || ·) BitVec.or_comm Bool.or_comm t a b
  · exact lift2_comm (· ^^^ ·) (· ^^ ·) BitVec.xor_comm Bool.xor_comm t a b

theorem AssocOp.eval_assoc (op : AssocOp) (t : Ty) (a b c : Val t) :
    op.eval t (op.eval t a b) c = op.eval t a (op.eval t b c) := by
  cases op
  · exact lift2_assoc (· + ·) (· ^^ ·) BitVec.add_assoc Bool.xor_assoc t a b c
  · exact lift2_assoc (· * ·) (· && ·) BitVec.mul_assoc Bool.and_assoc t a b c
  · exact lift2_assoc (· &&& ·) (· && ·) BitVec.and_assoc Bool.and_assoc t a b c
  · exact lift2_assoc (· ||| ·) (· || ·) BitVec.or_assoc Bool.or_assoc t a b c
  · exact lift2_assoc (· ^^^ ·) (· ^^ ·) BitVec.xor_assoc Bool.xor_assoc t a b c

theorem negVal_invol : ∀ (t : Ty) (a : Val t), negVal t (negVal t a) = a
  | .bool, _ => rfl
  | .bits _, _ => BitVec.neg_neg
  | .float _, _ => BitVec.neg_neg
  | .pair s u, (a₁, a₂) => Prod.ext (negVal_invol s a₁) (negVal_invol u a₂)

theorem subVal_eq_add_negVal : ∀ (t : Ty) (a b : Val t),
    lift2 (· - ·) (· ^^ ·) t a b = AssocOp.eval .add t a (negVal t b)
  | .bool, _, _ => rfl
  | .bits _, a, b => BitVec.sub_eq_add_neg a b
  | .float _, a, b => BitVec.sub_eq_add_neg a b
  | .pair s u, (a₁, a₂), (b₁, b₂) =>
    Prod.ext (subVal_eq_add_negVal s a₁ b₁) (subVal_eq_add_negVal u a₂ b₂)

theorem sub_add_imm_eq : ∀ (t : Ty) (a b c : Val t),
    lift2 (· - ·) (· ^^ ·) t a (AssocOp.eval .add t b c) =
      lift2 (· - ·) (· ^^ ·) t (AssocOp.eval .add t a (negVal t c)) b
  | .bool, a, b, c => by
    simp only [AssocOp.eval, lift2, negVal, lift1]
    rw [Bool.xor_comm b c, ← Bool.xor_assoc]; rfl
  | .bits _, a, b, c | .float _, a, b, c => by
    simp only [AssocOp.eval, lift2, negVal, lift1]
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.neg_add,
      BitVec.sub_eq_add_neg, BitVec.add_comm (-b) (-c), ← BitVec.add_assoc]
  | .pair s u, (a₁, a₂), (b₁, b₂), (c₁, c₂) =>
    Prod.ext (sub_add_imm_eq s a₁ b₁ c₁) (sub_add_imm_eq u a₂ b₂ c₂)

theorem AssocOp.toOpCode_wp (op : AssocOp) (t : Ty)
    (ht : op.needsNoFloat = true → t.hasFloat = false)
    (a b : Val t) (P : Tup Val [t] → Prop) :
    (op.toOpCode t).wp (a, b, ()) P ↔ P (op.eval t a b, ()) := by
  cases op <;> simp [AssocOp.toOpCode, AssocOp.eval, OpCode.wp] <;> exact fun _ => ht rfl

/-! ## Semantic invariant `CanonGood` and `Op.canonLet` soundness -/

/-- Provenance invariant: if `constDef = some d`, `v` equals `d.op.eval t d.base.val d.imm` and
non-float constraints hold. -/
def CanonDefGood : {t : Ty} → Option (CanonDef Val t) → Val t → Prop
  | _, none, _ => True
  | t, some d, v =>
      (d.op.needsNoFloat = true → t.hasFloat = false) ∧ v = d.op.eval t d.base.val d.imm

/-- Value invariant for `CanonVal Val t`: `out.val = v` and `constDef` is sound for `v`. -/
def CanonValGood {t : Ty} (cv : CanonVal Val t) (v : Val t) : Prop :=
  cv.out.val = v ∧ CanonDefGood cv.constDef v

/-- Context invariant for `canon_wp`: every entry in `G` satisfies `CanonValGood`. -/
def CanonGood (G : Ctx (CanonVal Val) Val) : Prop :=
  CtxPred (fun _ => CanonValGood) G

theorem CanonGood.cons {G : Ctx (CanonVal Val) Val} (hG : CanonGood G)
    {t : Ty} {cv : CanonVal Val t} {v : Val t} (hcv : CanonValGood cv v) :
    CanonGood (⟨t, cv, v⟩ :: G) :=
  CtxPred.cons hcv hG

theorem CanonGood.append {G₁ G₂ : Ctx (CanonVal Val) Val}
    (h1 : CanonGood G₁) (h2 : CanonGood G₂) : CanonGood (G₁ ++ G₂) :=
  CtxPred.append h1 h2

theorem CanonGood.freshCanonVals {G : Ctx (CanonVal Val) Val} (hG : CanonGood G)
    {ts : List Ty} (xs : Tup Val ts) (b : Nat) :
    CanonGood (Tup.zip (freshCanonVals ts xs b) xs ++ G) :=
  (CtxPred.zip_tupFreshWith_left_const (mk := CanonVal.fresh)
    (P := fun _ => CanonValGood) (fun _ _ => ⟨rfl, trivial⟩) xs b).append hG

theorem CanonGood.freshOne {G : Ctx (CanonVal Val) Val} (hG : CanonGood G)
    {t : Ty} (v : Val t) (b : Nat) :
    CanonGood (⟨t, CanonVal.fresh v b, v⟩ :: G) :=
  hG.cons ⟨rfl, trivial⟩

theorem ArgRel.cnout_val {G : Ctx (CanonVal Val) Val} (hG : CanonGood G)
    {t : Ty} {a₁ : Arg (CanonVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → a₁.cnout.val = a₂.val
  | .var h => (hG _ h).1
  | .imm _ => rfl

theorem TRel.cnout_vals {G : Ctx (CanonVal Val) Val} (hG : CanonGood G)
    {ts : List Ty} {as₁ : Tup (Arg (CanonVal Val)) ts} {as₂ : Tup (Arg Val) ts}
    (h : TRel (ArgRel G) as₁ as₂) : vals (tupCnOut as₁) = vals as₂ :=
  TRel.tupMapArg_vals (fun _ => Arg.cnout) (fun ha => ha.cnout_val hG) h

theorem ArgRel.cndef_good {G : Ctx (CanonVal Val) Val} (hG : CanonGood G)
    {t : Ty} {a₁ : Arg (CanonVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → CanonDefGood a₁.cndef? a₂.val
  | .var h => (hG _ h).2
  | .imm _ => trivial

private theorem canonAssocCore_wp {G : Ctx (CanonVal Val) Val} (hG : CanonGood G) (b : Nat)
    (aop : AssocOp) (t : Ty) (ht : aop.needsNoFloat = true → t.hasFloat = false)
    {a' b' : Arg (CanonVal Val) t} {a₂' b₂' : Arg Val t}
    (ha' : ArgRel G t a' a₂') (hb' : ArgRel G t b' b₂')
    {P : Tup Val [t] → Prop} (hw : P (aop.eval t a₂'.val b₂'.val, ())) :
    let step := canonAssocCore b aop t a' b'
    step.op.wp fun ys => P ys ∧ CanonGood (Tup.zip (step.wrap ys) ys ++ G) := by
  dsimp only [canonAssocCore]
  cases himm : b'.cnout.imm? with
  | none =>
    simp only [Op.wp, op2, vals, AssocOp.toOpCode_wp aop t ht,
      ha'.cnout_val hG, hb'.cnout_val hG]
    exact ⟨hw, hG.cons ⟨rfl, trivial⟩⟩
  | some c₂ =>
    have hb2c : b₂'.val = c₂ := (hb'.cnout_val hG).symm.trans (imm?_eq_some_val himm)
    have hplain : ({ code := aop.toOpCode t, args := (a'.cnout, .imm c₂, ()) } : Op Val [t]).wp
        fun ys => P ys ∧ CanonGood (⟨t, ⟨.var ys.1, .var b,
          some { op := aop, base := a'.cnout, imm := c₂ }⟩, ys.1⟩ :: G) := by
      simp only [Op.wp, vals, AssocOp.toOpCode_wp aop t ht,
        ha'.cnout_val hG, Arg.val_imm, ← hb2c]
      exact ⟨hw, hG.cons ⟨rfl, ht, ha'.cnout_val hG ▸ rfl⟩⟩
    cases hd : a'.cndef? with
    | none => exact hplain
    | some d =>
      dsimp only
      cases heq : (d.op == aop)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hplain
      · have hdeq : d.op = aop := eq_of_beq heq
        have hdg := ha'.cndef_good hG
        rw [hd] at hdg
        dsimp only [CanonDefGood] at hdg; rw [hdeq] at hdg
        have hre : aop.eval t d.base.val (aop.eval t d.imm c₂) = aop.eval t a₂'.val b₂'.val := by
          rw [← AssocOp.eval_assoc, ← hdg.2, ← hb2c]
        simp only [↓reduceIte, Op.wp, op2, vals,
          AssocOp.toOpCode_wp aop t ht, Arg.val_imm, hre]
        exact ⟨hw, hG.cons ⟨rfl, ht, hre.symm⟩⟩

theorem canonAssocStep_wp {G : Ctx (CanonVal Val) Val} (hG : CanonGood G) (b : Nat)
    (aop : AssocOp) (t : Ty) (ht : aop.needsNoFloat = true → t.hasFloat = false)
    {a₁ b₁ : Arg (CanonVal Val) t} {a₂ b₂ : Arg Val t}
    (ha : ArgRel G t a₁ a₂) (hb : ArgRel G t b₁ b₂)
    {P : Tup Val [t] → Prop} (hw : (aop.toOpCode t).wp (a₂.val, b₂.val, ()) P) :
    let step := canonAssocStep b aop t a₁ b₁
    step.op.wp fun ys => P ys ∧ CanonGood (Tup.zip (step.wrap ys) ys ++ G) := by
  rw [AssocOp.toOpCode_wp aop t ht] at hw
  dsimp only [canonAssocStep]
  cases hsw : shouldSwap a₁ b₁
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact canonAssocCore_wp hG b aop t ht ha hb hw
  · simp only [↓reduceIte]
    have hw' : P (aop.eval t b₂.val a₂.val, ()) := by
      rw [AssocOp.eval_comm]; exact hw
    exact canonAssocCore_wp hG b aop t ht hb ha hw'

private theorem canonAssocStepIf_wp {G : Ctx (CanonVal Val) Val} (hG : CanonGood G) (b : Nat)
    (aop : AssocOp) (t : Ty) {a₁ b₁ : Arg (CanonVal Val) t} {a₂ b₂ : Arg Val t}
    (ha : ArgRel G t a₁ a₂) (hb : ArgRel G t b₁ b₂)
    {P : Tup Val [t] → Prop} (hw : (aop.toOpCode t).wp (a₂.val, b₂.val, ()) P) :
    let step := canonAssocStepIf b aop t a₁ b₁
    step.op.wp fun ys => P ys ∧ CanonGood (Tup.zip (step.wrap ys) ys ++ G) := by
  dsimp only [canonAssocStepIf]
  split
  · dsimp only [Op.wp, op2, vals]
    rw [ha.cnout_val hG, hb.cnout_val hG]
    exact OpCode.wp_mono _ _ (fun ys hys => ⟨hys, hG.freshCanonVals ys b⟩) hw
  · rename_i hnf
    exact canonAssocStep_wp hG b aop t (fun h => by simp_all) ha hb hw

private theorem canonSubCore_wp {G : Ctx (CanonVal Val) Val} (hG : CanonGood G) (b : Nat)
    (t : Ty) (hnf : t.hasFloat = false)
    {a' b' : Arg (CanonVal Val) t} {a₂' b₂' : Arg Val t}
    (ha' : ArgRel G t a' a₂') (hb' : ArgRel G t b' b₂')
    {P : Tup Val [t] → Prop} (hw : P (lift2 (· - ·) (· ^^ ·) t a₂'.val b₂'.val, ())) :
    let step := canonSubCore b t a' b'
    step.op.wp fun ys => P ys ∧ CanonGood (Tup.zip (step.wrap ys) ys ++ G) := by
  dsimp only [canonSubCore]
  have hsub_add : ∀ x y, lift2 (· - ·) (· ^^ ·) t x y = AssocOp.eval .add t x (negVal t y) :=
    subVal_eq_add_negVal t
  have hplain : ({ code := .sub t, args := (a'.cnout, b'.cnout, ()) } : Op Val [t]).wp fun ys =>
      P ys ∧ CanonGood (⟨t, CanonVal.fresh ys.1 b, ys.1⟩ :: G) := by
    dsimp only [Op.wp, op2, vals]
    rw [ha'.cnout_val hG, hb'.cnout_val hG]
    simp only [OpCode.wp_sub, hnf, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hw, hG.cons ⟨rfl, trivial⟩⟩
  cases himm : b'.cnout.imm? with
  | some c₂ =>
    have hb2c : b₂'.val = c₂ := (hb'.cnout_val hG).symm.trans (imm?_eq_some_val himm)
    have himm_fb : ({ code := .sub t, args := (a'.cnout, .imm c₂, ()) } : Op Val [t]).wp fun ys =>
        P ys ∧ CanonGood (⟨t, ⟨.var ys.1, .var b,
          some { op := .add, base := a'.cnout, imm := negVal t c₂, isSub := true }⟩,
          ys.1⟩ :: G) := by
      simp only [Op.wp, vals, OpCode.wp_sub, hnf, Bool.false_eq_true, ↓reduceIte,
        ha'.cnout_val hG, Arg.val_imm, ← hb2c]
      refine ⟨hw, hG.cons ⟨rfl, fun _ => hnf, ?_⟩⟩
      change lift2 (· - ·) (· ^^ ·) t a₂'.val b₂'.val =
        AssocOp.eval .add t a'.cnout.val (negVal t b₂'.val)
      rw [ha'.cnout_val hG, hsub_add]
    cases hd : a'.cndef? with
    | none => exact himm_fb
    | some d =>
      dsimp only
      cases heq : (d.op == .add)
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact himm_fb
      · have hdeq : d.op = .add := eq_of_beq heq
        have hdg := ha'.cndef_good hG
        rw [hd] at hdg
        dsimp only [CanonDefGood] at hdg; rw [hdeq] at hdg
        have hval : AssocOp.eval .add t d.base.val (AssocOp.eval .add t d.imm (negVal t c₂)) =
            lift2 (· - ·) (· ^^ ·) t a₂'.val b₂'.val := by
          rw [← AssocOp.eval_assoc, ← hdg.2, ← hb2c, ← hsub_add]
        simp only [↓reduceIte]
        cases d.isSub
        · simp only [Bool.false_eq_true, ↓reduceIte]
          simp only [Op.wp, op2, vals, OpCode.wp_add, hnf, Bool.false_eq_true, ↓reduceIte,
            Arg.val_imm]
          change P (AssocOp.eval .add t d.base.val _, ()) ∧ CanonGood _
          exact ⟨hval ▸ hw, hG.cons ⟨rfl, fun _ => hnf, rfl⟩⟩
        · simp only [↓reduceIte]
          simp only [Op.wp, op2, vals, OpCode.wp_sub, hnf, Bool.false_eq_true, ↓reduceIte,
            Arg.val_imm, subVal_eq_add_negVal, negVal_invol]
          change P (AssocOp.eval .add t d.base.val _, ()) ∧ CanonGood _
          exact ⟨hval ▸ hw, hG.cons ⟨rfl, fun _ => hnf, rfl⟩⟩
  | none =>
    cases ha_imm : a'.cnout.imm? with
    | none => exact hplain
    | some c₁ =>
      have ha1c : a₂'.val = c₁ := (ha'.cnout_val hG).symm.trans (imm?_eq_some_val ha_imm)
      cases hd : b'.cndef? with
      | none => exact hplain
      | some d =>
        dsimp only
        cases heq : (d.op == .add)
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact hplain
        · have hdeq : d.op = .add := eq_of_beq heq
          have hdg := hb'.cndef_good hG
          rw [hd] at hdg
          dsimp only [CanonDefGood] at hdg; rw [hdeq] at hdg
          simp only [↓reduceIte]
          dsimp only [Op.wp, op2, vals]
          simp only [OpCode.wp_sub, hnf, Bool.false_eq_true, ↓reduceIte, Arg.val_imm]
          have hre : lift2 (· - ·) (· ^^ ·) t
              (AssocOp.eval .add t c₁ (negVal t d.imm)) d.base.val =
              lift2 (· - ·) (· ^^ ·) t a₂'.val b₂'.val := by
            rw [← sub_add_imm_eq, ← ha1c, ← hdg.2]
          rw [hre]
          exact ⟨hw, hG.cons ⟨rfl, trivial⟩⟩

private theorem canonSubStepIf_wp {G : Ctx (CanonVal Val) Val} (hG : CanonGood G) (b : Nat)
    (t : Ty) {a₁ b₁ : Arg (CanonVal Val) t} {a₂ b₂ : Arg Val t}
    (ha : ArgRel G t a₁ a₂) (hb : ArgRel G t b₁ b₂)
    {P : Tup Val [t] → Prop} (hw : (OpCode.sub t).wp (a₂.val, b₂.val, ()) P) :
    let step := canonSubStepIf b t a₁ b₁
    step.op.wp fun ys => P ys ∧ CanonGood (Tup.zip (step.wrap ys) ys ++ G) := by
  dsimp only [canonSubStepIf]
  split
  · dsimp only [Op.wp, op2, vals]
    rw [ha.cnout_val hG, hb.cnout_val hG]
    exact OpCode.wp_mono _ _ (fun ys hys => ⟨hys, hG.freshCanonVals ys b⟩) hw
  · rename_i hnf
    have hnf' : t.hasFloat = false := Bool.eq_false_iff.mpr hnf
    simp only [OpCode.wp_sub, hnf', Bool.false_eq_true, ↓reduceIte] at hw
    exact canonSubCore_wp hG b t hnf' ha hb hw

theorem OpRel.canonLet_wp {G : Ctx (CanonVal Val) Val} (hG : CanonGood G) (b : Nat)
    {sig ts : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg (CanonVal Val)) sig} {args₂ : Tup (Arg Val) sig}
    (hargs : TRel (ArgRel G) args₁ args₂)
    {P : Tup Val ts → Prop} (hw : code.wp (vals args₂) P) :
    let step := ({ code := code, args := args₁ } : Op (CanonVal Val) ts).canonLet b
    step.op.wp fun ys => P ys ∧ CanonGood (Tup.zip (step.wrap ys) ys ++ G) := by
  dsimp only [Op.canonLet]
  cases code with
  | add t | mul t | and t | or t | xor t =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
    exact canonAssocStepIf_wp hG b _ t ha hb hw
  | sub t =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
    exact canonSubStepIf_wp hG b t ha hb hw
  | cmp o t m h =>
    subst h
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
    dsimp only [OpCode.canonLet, Op.wp, op2, vals]
    split
    · rename_i hcond
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      simp only [OpCode.wp_cmp, hcond.1, Bool.false_eq_true, ↓reduceIte, cast_eq,
        ha.cnout_val hG, hb.cnout_val hG, liftCmp_swap] at hw ⊢
      exact ⟨hw, hG.freshCanonVals _ b⟩
    · rw [ha.cnout_val hG, hb.cnout_val hG]
      exact OpCode.wp_mono _ _ (fun ys hys => ⟨hys, hG.freshCanonVals ys b⟩) hw
  | _ =>
    all_goals
      (dsimp only [OpCode.canonLet, Op.wp]
       rw [hargs.cnout_vals hG]
       exact OpCode.wp_mono _ _ (fun ys hys => ⟨hys, hG.freshCanonVals ys b⟩) hw)

theorem canonB_get {V₁ : Ty → Type} {L₁ : List Ty → Type} {rs : List Ty} (b : Nat) :
    {sig : List (List Ty)} → {ts : List Ty} → (bs : Blocks (CanonVal V₁) L₁ rs sig) →
    (i : Member ts sig) → (xs : Tup V₁ ts) →
    (canonB b bs).get i xs = canon (b + ts.length) (bs.get i (freshCanonVals ts xs b))
  | _, _, .cons _ _, .here, _ => rfl
  | _, _, .cons _ bs, .there i, xs => canonB_get b bs i xs

/-- Weakest-precondition preservation for `canon`, proved via `Wf.induct`. -/
theorem canon_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (CanonVal Val) Val} {D : Ctx Cont Cont}
    {e₁ : Expr (CanonVal Val) Cont rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    (∀ p ∈ D, p.2.1 = p.2.2) →
    ∀ b, CanonGood G → ∀ m, wp Γ Q X e₂ m → wp Γ Q X (canon b e₁) m := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro hD b hG m hw
    dsimp only [wp] at hw
    cases hop with
    | @mk sig _ code args₁ args₂ hargs =>
      have hstep := OpRel.canonLet_wp hG b hargs hw
      dsimp only [canon, wp]
      exact Op.wp_mono (fun ys ⟨hk2, hG'⟩ => ih _ ys hD (b + ts.length) hG' m hk2) hstep
  | load t ha _ ih =>
    intro hD b hG m hw
    dsimp only [wp, canon] at hw ⊢
    rcases hw with ⟨v, hv, hk⟩
    exact ⟨v, ha.cnout_val hG ▸ hv, ih (CanonVal.fresh v b) v hD (b + 1) (hG.freshOne v b) m hk⟩
  | store hv ha _ ih =>
    intro hD b hG m hw
    dsimp only [wp, canon] at hw ⊢
    rw [ha.cnout_val hG, hv.cnout_val hG]
    exact ⟨hw.1, ih hD b hG _ hw.2⟩
  | call f hargs _ ih =>
    intro hD b hG m hw
    dsimp only [wp, canon] at hw ⊢
    rcases hw with ⟨P, E, hΓ, hP, hE⟩
    rw [hargs.cnout_vals hG]
    exact ⟨P, E, hΓ, fun r m' hp =>
      ih (freshCanonVals _ r b) r hD (b + _) (hG.freshCanonVals r b) m' (hP r m' hp), hE⟩
  | jnz hc _ _ iht ihe =>
    intro hD b hG m hw
    dsimp only [wp, canon] at hw ⊢
    rw [hc.cnout_val hG]
    exact ⟨fun h => iht hD b hG m (hw.1 h), fun h => ihe hD b hG m (hw.2 h)⟩
  | jump hj hargs =>
    intro hD b hG m hw
    have hj' := hD _ hj; dsimp only at hj'
    dsimp only [wp, canon] at hw ⊢
    rw [hj', hargs.cnout_vals hG]
    exact hw
  | ret hvs =>
    intro _ b hG m hw
    dsimp only [wp, canon] at hw ⊢
    rw [hvs.cnout_vals hG]
    exact hw
  | exit f hargs =>
    intro _ b hG m hw
    dsimp only [wp, canon] at hw ⊢
    rw [hargs.cnout_vals hG]
    exact hw
  | hlt =>
    intro _ _ _ _ hw
    exact hw
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro hD b hG m hw
    dsimp only [wp, canon] at hw ⊢
    intro Js hclosed
    refine ihk Js Js (tup_zip_self_eq hD Js) b hG m (hw Js ?_)
    rw [closed_iff] at hclosed ⊢
    intro ts i xs m' hb
    have hcanon := ihb Js Js i (freshCanonVals ts xs b) xs (tup_zip_self_eq hD Js)
      (b + ts.length) (hG.freshCanonVals xs b) m' hb
    rw [← canonB_get b (b₁ Js) i xs] at hcanon
    exact hclosed i xs m' hcanon

/-! ## Relational well-formedness for `canon` (`CanonRelG` and `canon_wf`) -/

section
variable {V₁ V₂ : Ty → Type}

def CanonDefRel (G' : Ctx V₁ V₂) :
    {t : Ty} → Option (CanonDef V₁ t) → Option (CanonDef V₂ t) → Prop
  | _, none, none => True
  | t, some d₁, some d₂ =>
      d₁.op = d₂.op ∧ ArgRel G' t d₁.base d₂.base ∧ d₁.imm = d₂.imm ∧ d₁.isSub = d₂.isSub
  | _, _, _ => False

theorem CanonDefRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂) :
    {t : Ty} → {d₁ : Option (CanonDef V₁ t)} → {d₂ : Option (CanonDef V₂ t)} →
    CanonDefRel G₁ d₁ d₂ → CanonDefRel G₂ d₁ d₂
  | _, none, none, _ => trivial
  | _, some _, some _, ⟨hop, hbase, himm, hsubf⟩ => ⟨hop, hbase.weaken hsub, himm, hsubf⟩

def CanonValRel (G' : Ctx V₁ V₂) {t : Ty} (c₁ : CanonVal V₁ t) (c₂ : CanonVal V₂ t) : Prop :=
  ArgRel G' t c₁.out c₂.out ∧ c₁.key = c₂.key ∧ CanonDefRel G' c₁.constDef c₂.constDef

theorem CanonValRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂)
    {t : Ty} {c₁ : CanonVal V₁ t} {c₂ : CanonVal V₂ t} (h : CanonValRel G₁ c₁ c₂) :
    CanonValRel G₂ c₁ c₂ :=
  ⟨h.1.weaken hsub, h.2.1, h.2.2.weaken hsub⟩

theorem CanonValRel.fresh {G' : Ctx V₁ V₂} {t : Ty} {v₁ : V₁ t} {v₂ : V₂ t} (b : Nat)
    (hm : ⟨t, v₁, v₂⟩ ∈ G') :
    CanonValRel G' (CanonVal.fresh v₁ b) (CanonVal.fresh v₂ b) :=
  ⟨.var hm, rfl, trivial⟩

private def canonRelKit : RelKit CanonVal where
  out c := c.out
  fresh v k := CanonVal.fresh v k
  rel G' _ c₁ c₂ := CanonValRel G' c₁ c₂
  rel_weaken hsub _ _ _ h := h.weaken hsub
  rel_out h := h.1
  rel_fresh b hm := CanonValRel.fresh b hm

def CanonRelG (G' : Ctx V₁ V₂) (G : Ctx (CanonVal V₁) (CanonVal V₂)) : Prop :=
  canonRelKit.RelG G' G

theorem CanonRelG.cons {G' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)}
    (hG : CanonRelG G' G) {t : Ty} {c₁ : CanonVal V₁ t} {c₂ : CanonVal V₂ t}
    (hc : CanonValRel G' c₁ c₂) :
    CanonRelG G' (⟨t, c₁, c₂⟩ :: G) :=
  canonRelKit.relG_cons hc hG

theorem CanonRelG.append {G' : Ctx V₁ V₂} {G H : Ctx (CanonVal V₁) (CanonVal V₂)}
    (h1 : CanonRelG G' G) (h2 : CanonRelG G' H) : CanonRelG G' (H ++ G) :=
  canonRelKit.relG_append h2 h1

theorem CanonRelG.weaken {G' G'' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)}
    (hG : CanonRelG G' G) (hsub : ∀ p ∈ G', p ∈ G'') : CanonRelG G'' G :=
  canonRelKit.relG_weaken hsub hG

theorem CanonRelG.append_tup {G' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)}
    (hG : CanonRelG G' G) :
    {ts : List Ty} → {r₁ : Tup (CanonVal V₁) ts} → {r₂ : Tup (CanonVal V₂) ts} →
    TRel (fun _ => CanonValRel G') r₁ r₂ → CanonRelG G' (Tup.zip r₁ r₂ ++ G) :=
  fun hT => canonRelKit.relG_append_tup hT hG

theorem CanonRelG.freshCanonVals {G' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)}
    (hG : CanonRelG G' G) {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) (b : Nat) :
    CanonRelG (Tup.zip xs₁ xs₂ ++ G')
      (Tup.zip (freshCanonVals ts xs₁ b) (freshCanonVals ts xs₂ b) ++ G) :=
  canonRelKit.relG_freshTup ts xs₁ xs₂ b hG

theorem CanonRelG.freshOne {G' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)}
    (hG : CanonRelG G' G) {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) (b : Nat) :
    CanonRelG (⟨t, v₁, v₂⟩ :: G') (⟨t, CanonVal.fresh v₁ b, CanonVal.fresh v₂ b⟩ :: G) :=
  canonRelKit.relG_freshOne v₁ v₂ b hG

theorem TRel.freshCanonVals_rel {G' : Ctx V₁ V₂} {ts : List Ty}
    (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) (b : Nat) :
    TRel (fun _ => CanonValRel (Tup.zip xs₁ xs₂ ++ G'))
      (freshCanonVals ts xs₁ b) (freshCanonVals ts xs₂ b) :=
  canonRelKit.trel_freshTup ts xs₁ xs₂ b

theorem ArgRel.cnout {G' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)} (hG : CanonRelG G' G)
    {t : Ty} {a₁ : Arg (CanonVal V₁) t} {a₂ : Arg (CanonVal V₂) t} :
    ArgRel G t a₁ a₂ → ArgRel G' t a₁.cnout a₂.cnout
  | .var h => (hG _ h).1
  | .imm c => .imm c

theorem ArgRel.cnkey_eq {G' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)}
    (hG : CanonRelG G' G) {t : Ty} {a₁ : Arg (CanonVal V₁) t} {a₂ : Arg (CanonVal V₂) t} :
    ArgRel G t a₁ a₂ → a₁.cnkey = a₂.cnkey
  | .var h => (hG _ h).2.1
  | .imm _ => rfl

theorem ArgRel.cndef_rel {G' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)}
    (hG : CanonRelG G' G) {t : Ty} {a₁ : Arg (CanonVal V₁) t} {a₂ : Arg (CanonVal V₂) t} :
    ArgRel G t a₁ a₂ → CanonDefRel G' a₁.cndef? a₂.cndef?
  | .var h => (hG _ h).2.2
  | .imm _ => trivial

theorem TRel.cnout {G' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)} (hG : CanonRelG G' G)
    {ts : List Ty} {as₁ : Tup (Arg (CanonVal V₁)) ts} {as₂ : Tup (Arg (CanonVal V₂)) ts}
    (h : TRel (ArgRel G) as₁ as₂) : TRel (ArgRel G') (tupCnOut as₁) (tupCnOut as₂) :=
  TRel.tupMapArg_rel (fun _ => Arg.cnout) (fun _ => Arg.cnout) (fun ha => ha.cnout hG) h

theorem shouldSwap_eq {G' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)}
    (hG : CanonRelG G' G) {t : Ty} {a₁ b₁ : Arg (CanonVal V₁) t} {a₂ b₂ : Arg (CanonVal V₂) t}
    (ha : ArgRel G t a₁ a₂) (hb : ArgRel G t b₁ b₂) :
    shouldSwap a₁ b₁ = shouldSwap a₂ b₂ := by
  dsimp only [shouldSwap]
  rw [argRel_imm?_eq (ha.cnout hG), argRel_imm?_eq (hb.cnout hG),
    ha.cnkey_eq hG, hb.cnkey_eq hG]

structure CanonStepRel (G' : Ctx V₁ V₂) {ts : List Ty}
    (s₁ : CanonLetStep V₁ ts) (s₂ : CanonLetStep V₂ ts) : Prop where
  op : OpRel G' s₁.op s₂.op
  wrap : ∀ xs₁ xs₂, TRel (fun _ => CanonValRel (Tup.zip xs₁ xs₂ ++ G')) (s₁.wrap xs₁) (s₂.wrap xs₂)

private theorem canonStepRel_fresh {G' : Ctx V₁ V₂} {t : Ty} (b : Nat)
    (code : OpCode [t, t] [t]) {x₁ y₁ : Arg V₁ t} {x₂ y₂ : Arg V₂ t}
    (hx : ArgRel G' t x₁ x₂) (hy : ArgRel G' t y₁ y₂) :
    CanonStepRel G'
      ({ op := op2 code x₁ y₁, wrap := fun (r, ()) => (CanonVal.fresh r b, ()) } :
        CanonLetStep V₁ [t])
      ({ op := op2 code x₂ y₂, wrap := fun (r, ()) => (CanonVal.fresh r b, ()) } :
        CanonLetStep V₂ [t]) :=
  ⟨.mk _ (.cons hx (.cons hy .nil)), fun _ _ =>
    .cons (CanonValRel.fresh b List.mem_cons_self) .nil⟩

private theorem canonStepRel_def {G' : Ctx V₁ V₂} {t : Ty} (b : Nat)
    (code : OpCode [t, t] [t]) (aop : AssocOp) (isSub : Bool) (c : Val t)
    {base₁ : Arg V₁ t} {base₂ : Arg V₂ t} {x₁ y₁ : Arg V₁ t} {x₂ y₂ : Arg V₂ t}
    (hbase : ArgRel G' t base₁ base₂) (hx : ArgRel G' t x₁ x₂) (hy : ArgRel G' t y₁ y₂) :
    CanonStepRel G'
      ({ op := op2 code x₁ y₁
         wrap := fun (r, ()) =>
           (⟨.var r, .var b, some { op := aop, base := base₁, imm := c, isSub := isSub }⟩, ()) } :
        CanonLetStep V₁ [t])
      ({ op := op2 code x₂ y₂
         wrap := fun (r, ()) =>
           (⟨.var r, .var b, some { op := aop, base := base₂, imm := c, isSub := isSub }⟩, ()) } :
        CanonLetStep V₂ [t]) := by
  refine ⟨.mk _ (.cons hx (.cons hy .nil)), fun (r₁, ()) (r₂, ()) => ?_⟩
  have hsub : ∀ p ∈ G', p ∈ (Tup.zip (as := [t]) (r₁, ()) (r₂, ()) ++ G') :=
    fun _ hq => List.mem_cons_of_mem _ hq
  exact .cons ⟨.var List.mem_cons_self, rfl,
    ⟨rfl, hbase.weaken hsub, rfl, rfl⟩⟩ .nil

private theorem canonAssocCore_rel {G' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)}
    (hG : CanonRelG G' G) (b : Nat) (aop : AssocOp) (t : Ty)
    {a₁' b₁' : Arg (CanonVal V₁) t} {a₂' b₂' : Arg (CanonVal V₂) t}
    (ha' : ArgRel G t a₁' a₂') (hb' : ArgRel G t b₁' b₂') :
    CanonStepRel G' (canonAssocCore b aop t a₁' b₁') (canonAssocCore b aop t a₂' b₂') := by
  dsimp only [canonAssocCore]
  rw [argRel_imm?_eq (hb'.cnout hG)]
  cases himm : b₂'.cnout.imm? with
  | none => exact canonStepRel_fresh b _ (ha'.cnout hG) (hb'.cnout hG)
  | some c₂ =>
    have hdef := ha'.cndef_rel hG
    cases hd₁ : a₁'.cndef? <;> cases hd₂ : a₂'.cndef? <;> rw [hd₁, hd₂] at hdef <;>
      try exact False.elim hdef
    · exact canonStepRel_def b _ aop false c₂ (ha'.cnout hG) (ha'.cnout hG) (.imm c₂)
    · rcases hdef with ⟨hop, hbase, himm, _⟩
      dsimp only; rw [hop, himm]
      cases heq : (_ == aop)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact canonStepRel_def b _ aop false c₂ (ha'.cnout hG) (ha'.cnout hG) (.imm c₂)
      · simp only [↓reduceIte]
        exact canonStepRel_def b _ aop false _ hbase hbase (.imm _)

private theorem canonAssocStep_rel {G' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)}
    (hG : CanonRelG G' G) (b : Nat) (aop : AssocOp) (t : Ty)
    {a₁ b₁ : Arg (CanonVal V₁) t} {a₂ b₂ : Arg (CanonVal V₂) t}
    (ha : ArgRel G t a₁ a₂) (hb : ArgRel G t b₁ b₂) :
    CanonStepRel G' (canonAssocStep b aop t a₁ b₁) (canonAssocStep b aop t a₂ b₂) := by
  dsimp only [canonAssocStep]; rw [shouldSwap_eq hG ha hb]
  cases hsw : shouldSwap a₂ b₂
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact canonAssocCore_rel hG b aop t ha hb
  · simp only [↓reduceIte]
    exact canonAssocCore_rel hG b aop t hb ha

private theorem canonAssocStepIf_rel {G' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)}
    (hG : CanonRelG G' G) (b : Nat) (aop : AssocOp) (t : Ty)
    {a₁ b₁ : Arg (CanonVal V₁) t} {a₂ b₂ : Arg (CanonVal V₂) t}
    (ha : ArgRel G t a₁ a₂) (hb : ArgRel G t b₁ b₂) :
    CanonStepRel G' (canonAssocStepIf b aop t a₁ b₁) (canonAssocStepIf b aop t a₂ b₂) := by
  dsimp only [canonAssocStepIf]
  split
  · exact ⟨.mk (aop.toOpCode t) (.cons (ha.cnout hG) (.cons (hb.cnout hG) .nil)),
      fun xs₁ xs₂ => TRel.freshCanonVals_rel xs₁ xs₂ b⟩
  · exact canonAssocStep_rel hG b aop t ha hb

private theorem canonSubCore_rel {G' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)}
    (hG : CanonRelG G' G) (b : Nat) (t : Ty)
    {a₁' b₁' : Arg (CanonVal V₁) t} {a₂' b₂' : Arg (CanonVal V₂) t}
    (ha' : ArgRel G t a₁' a₂') (hb' : ArgRel G t b₁' b₂') :
    CanonStepRel G' (canonSubCore b t a₁' b₁') (canonSubCore b t a₂' b₂') := by
  dsimp only [canonSubCore]
  rw [argRel_imm?_eq (hb'.cnout hG)]
  cases himm : b₂'.cnout.imm? with
  | some c₂ =>
    dsimp only
    have hdef := ha'.cndef_rel hG
    cases hd₁ : a₁'.cndef? <;> cases hd₂ : a₂'.cndef? <;> rw [hd₁, hd₂] at hdef <;>
      try exact False.elim hdef
    · exact canonStepRel_def b _ .add true (negVal t c₂)
        (ha'.cnout hG) (ha'.cnout hG) (.imm c₂)
    · rcases hdef with ⟨hop, hbase, himm, hsubf⟩
      dsimp only; rw [hop, himm, hsubf]
      cases heq : (_ == AssocOp.add)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact canonStepRel_def b _ .add true (negVal t c₂)
          (ha'.cnout hG) (ha'.cnout hG) (.imm c₂)
      · simp only [↓reduceIte]
        split <;> exact canonStepRel_def b _ .add _ _ hbase hbase (.imm _)
  | none =>
    dsimp only
    rw [argRel_imm?_eq (ha'.cnout hG)]
    cases himma : a₂'.cnout.imm? with
    | none => exact canonStepRel_fresh b _ (ha'.cnout hG) (hb'.cnout hG)
    | some c₁ =>
      have hdef := hb'.cndef_rel hG
      cases hd₁ : b₁'.cndef? <;> cases hd₂ : b₂'.cndef? <;> rw [hd₁, hd₂] at hdef <;>
        try exact False.elim hdef
      · exact canonStepRel_fresh b _ (ha'.cnout hG) (hb'.cnout hG)
      · rcases hdef with ⟨hop, hbase, himm, _⟩
        dsimp only; rw [hop, himm]
        cases heq : (_ == AssocOp.add)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact canonStepRel_fresh b _ (ha'.cnout hG) (hb'.cnout hG)
        · simp only [↓reduceIte]
          exact canonStepRel_fresh b _ (.imm _) hbase

private theorem canonSubStepIf_rel {G' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)}
    (hG : CanonRelG G' G) (b : Nat) (t : Ty)
    {a₁ b₁ : Arg (CanonVal V₁) t} {a₂ b₂ : Arg (CanonVal V₂) t}
    (ha : ArgRel G t a₁ a₂) (hb : ArgRel G t b₁ b₂) :
    CanonStepRel G' (canonSubStepIf b t a₁ b₁) (canonSubStepIf b t a₂ b₂) := by
  dsimp only [canonSubStepIf]
  split
  · exact ⟨.mk (.sub t) (.cons (ha.cnout hG) (.cons (hb.cnout hG) .nil)),
      fun xs₁ xs₂ => TRel.freshCanonVals_rel xs₁ xs₂ b⟩
  · exact canonSubCore_rel hG b t ha hb

theorem OpRel.canonLet_rel {G' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)}
    (hG : CanonRelG G' G) (b : Nat) {sig ts : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg (CanonVal V₁)) sig} {args₂ : Tup (Arg (CanonVal V₂)) sig}
    (hargs : TRel (ArgRel G) args₁ args₂) :
    CanonStepRel G'
      (({ code := code, args := args₁ } : Op (CanonVal V₁) ts).canonLet b)
      (({ code := code, args := args₂ } : Op (CanonVal V₂) ts).canonLet b) := by
  dsimp only [Op.canonLet]
  cases code with
  | add t | mul t | and t | or t | xor t =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
    exact canonAssocStepIf_rel hG b _ t ha hb
  | sub t =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
    exact canonSubStepIf_rel hG b t ha hb
  | cmp o t m h =>
    subst h
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
    dsimp only [OpCode.canonLet]; rw [shouldSwap_eq hG ha hb]
    split
    · exact ⟨.mk (.cmp o.swap t) (.cons (hb.cnout hG) (.cons (ha.cnout hG) .nil)),
        fun xs₁ xs₂ => TRel.freshCanonVals_rel xs₁ xs₂ b⟩
    · exact ⟨.mk (.cmp o t) (.cons (ha.cnout hG) (.cons (hb.cnout hG) .nil)),
        fun xs₁ xs₂ => TRel.freshCanonVals_rel xs₁ xs₂ b⟩
  | _ =>
    all_goals
      exact ⟨.mk _ (TRel.cnout hG hargs), fun xs₁ xs₂ => TRel.freshCanonVals_rel xs₁ xs₂ b⟩

end

/-- Well-formedness preservation for `canon`, proved via `Wf.induct`. -/
theorem canon_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (CanonVal V₁) (CanonVal V₂)} {D : Ctx L₁ L₂}
    {e₁ : Expr (CanonVal V₁) L₁ rs} {e₂ : Expr (CanonVal V₂) L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂}, CanonRelG G' G → ∀ b, Wf G' D (canon b e₁) (canon b e₂) := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro G' hG b
    cases hop with
    | @mk sig _ code args₁ args₂ hargs =>
      have hrel := OpRel.canonLet_rel hG b hargs (code := code)
      dsimp only [canon]
      refine .let_ hrel.op fun xs₁ xs₂ => ?_
      have hG' : CanonRelG (Tup.zip xs₁ xs₂ ++ G') G :=
        hG.weaken fun _ hq => List.mem_append_right _ hq
      exact ih _ _ (hG'.append_tup (hrel.wrap xs₁ xs₂)) (b + ts.length)
  | load t ha _ ih =>
    intro G' hG b
    exact .load t (ha.cnout hG) fun v₁ v₂ => ih _ _ (hG.freshOne v₁ v₂ b) (b + 1)
  | store hv ha _ ih =>
    intro G' hG b
    exact .store (hv.cnout hG) (ha.cnout hG) (ih hG b)
  | call f hargs _ ih =>
    intro G' hG b
    exact .call f (TRel.cnout hG hargs) fun xs₁ xs₂ =>
      ih _ _ (hG.freshCanonVals xs₁ xs₂ b) (b + _)
  | jnz hc _ _ iht ihe =>
    intro G' hG b
    exact .jnz (hc.cnout hG) (iht hG b) (ihe hG b)
  | jump hj hargs =>
    intro G' hG _
    exact .jump hj (TRel.cnout hG hargs)
  | ret hvs =>
    intro G' hG _
    exact .ret (TRel.cnout hG hvs)
  | exit f hargs =>
    intro G' hG _
    exact .exit f (TRel.cnout hG hargs)
  | hlt =>
    intro _ _ _
    exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro G' hG b
    refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_)
      (fun Js₁ Js₂ => ihk Js₁ Js₂ hG b)
    rw [canonB_get, canonB_get]
    exact ihb Js₁ Js₂ i _ _ (hG.freshCanonVals xs₁ xs₂ b) (b + _)

/-! ## Closed functions -/

theorem Func.canon_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) : (Func.canon f).Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  have hwf := hf (CanonVal V₁) (CanonVal V₂) L₁ L₂
    (freshCanonVals as xs₁ 0) (freshCanonVals as xs₂ 0)
  have hrel : CanonRelG (Tup.zip xs₁ xs₂)
      (Tup.zip (freshCanonVals as xs₁ 0) (freshCanonVals as xs₂ 0)) := by
    simpa using CanonRelG.freshCanonVals (G := []) (G' := []) (fun _ hp => nomatch hp) xs₁ xs₂ 0
  exact LeanQbe.T.canon_wf hwf hrel as.length

/-- Canonicalization refines function contracts: any source contract holds on `Func.canon f`. -/
theorem Func.canon_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.canon f) xs m Q X := by
  have hwf := hf (CanonVal Val) Val Cont Cont (freshCanonVals as xs 0) xs
  have hgood : CanonGood (Tup.zip (freshCanonVals as xs 0) xs) := by
    simpa using CanonGood.freshCanonVals (G := []) (fun _ hp => nomatch hp) xs 0
  exact LeanQbe.T.canon_wp hwf (fun _ hp => nomatch hp) as.length hgood m h

end LeanQbe.T
