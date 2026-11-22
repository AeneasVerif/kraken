module

public import LeanQbe.T.Canon
public import LeanQbe.T.Wf
public import LeanQbe.T.WP
import LeanQbe.T.WPLemmas
import LeanQbe.T.WfLemmas
import LeanQbe.T.OpsLemmas

/-!
# Correctness of `canon` (`O-M1`)

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

theorem AssocOp.toOpCode_wp (op : AssocOp) (t : Ty)
    (ht : op.needsNoFloat = true → t.hasFloat = false)
    (a b : Val t) (P : Tup Val [t] → Prop) :
    (op.toOpCode t).wp (a, b, ()) P ↔ P (op.eval t a b, ()) := by
  cases op
  · dsimp only [AssocOp.toOpCode, AssocOp.eval, OpCode.wp]; simp [ht rfl]
  · dsimp only [AssocOp.toOpCode, AssocOp.eval, OpCode.wp]; simp [ht rfl]
  · dsimp only [AssocOp.toOpCode, AssocOp.eval, OpCode.wp]; exact Iff.rfl
  · dsimp only [AssocOp.toOpCode, AssocOp.eval, OpCode.wp]; exact Iff.rfl
  · dsimp only [AssocOp.toOpCode, AssocOp.eval, OpCode.wp]; exact Iff.rfl

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
  ∀ p ∈ G, CanonValGood p.2.1 p.2.2

theorem CanonGood.cons {G : Ctx (CanonVal Val) Val} (hG : CanonGood G)
    {t : Ty} {cv : CanonVal Val t} {v : Val t} (hcv : CanonValGood cv v) :
    CanonGood (⟨t, cv, v⟩ :: G)
  | _, .head _ => hcv
  | _, .tail _ hp => hG _ hp

theorem CanonGood.append {G₁ G₂ : Ctx (CanonVal Val) Val}
    (h1 : CanonGood G₁) (h2 : CanonGood G₂) : CanonGood (G₁ ++ G₂) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact h1 p hp
  · exact h2 p hp

private theorem CanonGood.freshCanonVals_only :
    {ts : List Ty} → (xs : Tup Val ts) → (b : Nat) →
    CanonGood (Tup.zip (freshCanonVals ts xs b) xs)
  | [], (), _ => fun _ hp => nomatch hp
  | _ :: _, (x, xs), b => by
    intro p hp
    cases hp with
    | head => exact ⟨rfl, trivial⟩
    | tail _ hp => exact CanonGood.freshCanonVals_only xs (b + 1) p hp

theorem CanonGood.freshCanonVals {G : Ctx (CanonVal Val) Val} (hG : CanonGood G)
    {ts : List Ty} (xs : Tup Val ts) (b : Nat) :
    CanonGood (Tup.zip (freshCanonVals ts xs b) xs ++ G) :=
  (CanonGood.freshCanonVals_only xs b).append hG

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

private theorem imm?_eq_some_val {V : Ty → Type} : ∀ {t : Ty} {a : Arg V t} {c : Val t},
    a.imm? = some c → a = .imm c
  | _, .var _, _, h => by cases h
  | _, .imm _, _, h => by injection h with h; subst h; rfl

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
    have hb2c : b₂'.val = c₂ := by
      have h1 := hb'.cnout_val hG
      rw [imm?_eq_some_val himm] at h1
      exact h1.symm
    cases hd : a'.cndef? with
    | none =>
      simp only [Op.wp, op2, vals, AssocOp.toOpCode_wp aop t ht,
        ha'.cnout_val hG, Arg.val_imm, ← hb2c]
      exact ⟨hw, hG.cons ⟨rfl, ht, ha'.cnout_val hG ▸ rfl⟩⟩
    | some d =>
      dsimp only
      cases heq : (d.op == aop)
      · simp only [Bool.false_eq_true, ↓reduceIte, Op.wp, op2, vals,
          AssocOp.toOpCode_wp aop t ht, ha'.cnout_val hG, Arg.val_imm, ← hb2c]
        exact ⟨hw, hG.cons ⟨rfl, ht, ha'.cnout_val hG ▸ rfl⟩⟩
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
  | t, some d₁, some d₂ => d₁.op = d₂.op ∧ ArgRel G' t d₁.base d₂.base ∧ d₁.imm = d₂.imm
  | _, _, _ => False

theorem CanonDefRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂) :
    {t : Ty} → {d₁ : Option (CanonDef V₁ t)} → {d₂ : Option (CanonDef V₂ t)} →
    CanonDefRel G₁ d₁ d₂ → CanonDefRel G₂ d₁ d₂
  | _, none, none, _ => trivial
  | _, some _, some _, ⟨hop, hbase, himm⟩ => ⟨hop, hbase.weaken hsub, himm⟩

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

def CanonRelG (G' : Ctx V₁ V₂) (G : Ctx (CanonVal V₁) (CanonVal V₂)) : Prop :=
  ∀ p ∈ G, CanonValRel G' p.2.1 p.2.2

theorem CanonRelG.cons {G' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)}
    (hG : CanonRelG G' G) {t : Ty} {c₁ : CanonVal V₁ t} {c₂ : CanonVal V₂ t}
    (hc : CanonValRel G' c₁ c₂) :
    CanonRelG G' (⟨t, c₁, c₂⟩ :: G)
  | _, .head _ => hc
  | _, .tail _ hp => hG _ hp

theorem CanonRelG.append {G' : Ctx V₁ V₂} {G H : Ctx (CanonVal V₁) (CanonVal V₂)}
    (h1 : CanonRelG G' G) (h2 : CanonRelG G' H) : CanonRelG G' (H ++ G) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact h2 p hp
  · exact h1 p hp

theorem CanonRelG.weaken {G' G'' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)}
    (hG : CanonRelG G' G) (hsub : ∀ p ∈ G', p ∈ G'') : CanonRelG G'' G :=
  fun p hp => (hG p hp).weaken hsub

theorem CanonRelG.append_tup {G' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)}
    (hG : CanonRelG G' G) :
    {ts : List Ty} → {r₁ : Tup (CanonVal V₁) ts} → {r₂ : Tup (CanonVal V₂) ts} →
    TRel (fun _ => CanonValRel G') r₁ r₂ → CanonRelG G' (Tup.zip r₁ r₂ ++ G)
  | [], (), (), .nil => hG
  | _ :: _, (_, _), (_, _), .cons hr hs => (CanonRelG.append_tup hG hs).cons hr

private theorem CanonRelG.freshCanonVals_only {ts : List Ty}
    (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) (b : Nat) :
    CanonRelG (Tup.zip xs₁ xs₂)
      (Tup.zip (freshCanonVals ts xs₁ b) (freshCanonVals ts xs₂ b)) :=
  mem_tup_zip_tupFreshWith (fun x n => CanonVal.fresh x n) (fun x n => CanonVal.fresh x n)
    (P := fun G' _ c₁ c₂ => CanonValRel G' c₁ c₂)
    (fun hsub _ _ _ h => h.weaken hsub)
    (fun _ _ idx => CanonValRel.fresh idx List.mem_cons_self)
    xs₁ xs₂ b

theorem CanonRelG.freshCanonVals {G' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)}
    (hG : CanonRelG G' G) {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) (b : Nat) :
    CanonRelG (Tup.zip xs₁ xs₂ ++ G')
      (Tup.zip (freshCanonVals ts xs₁ b) (freshCanonVals ts xs₂ b) ++ G) :=
  (hG.weaken fun _ hq => List.mem_append_right _ hq).append
    ((CanonRelG.freshCanonVals_only xs₁ xs₂ b).weaken fun _ hq => List.mem_append_left G' hq)

theorem CanonRelG.freshOne {G' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)}
    (hG : CanonRelG G' G) {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) (b : Nat) :
    CanonRelG (⟨t, v₁, v₂⟩ :: G') (⟨t, CanonVal.fresh v₁ b, CanonVal.fresh v₂ b⟩ :: G) :=
  (hG.weaken fun _ hq => List.mem_cons_of_mem _ hq).cons
    (CanonValRel.fresh b List.mem_cons_self)

theorem TRel.freshCanonVals_rel {G' : Ctx V₁ V₂} {ts : List Ty}
    (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) (b : Nat) :
    TRel (fun _ => CanonValRel (Tup.zip xs₁ xs₂ ++ G'))
      (freshCanonVals ts xs₁ b) (freshCanonVals ts xs₂ b) :=
  TRel_tupFreshWith (fun x n => CanonVal.fresh x n) (fun x n => CanonVal.fresh x n)
    (P := fun G' _ c₁ c₂ => CanonValRel G' c₁ c₂)
    (fun hsub _ _ _ h => h.weaken hsub)
    (fun _ _ idx => CanonValRel.fresh idx List.mem_cons_self)
    xs₁ xs₂ b

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

private theorem argRel_imm?_eq {G' : Ctx V₁ V₂} {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} :
    ArgRel G' t a₁ a₂ → a₁.imm? = a₂.imm?
  | .var _ | .imm _ => rfl

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

private theorem canonAssocCore_rel {G' : Ctx V₁ V₂} {G : Ctx (CanonVal V₁) (CanonVal V₂)}
    (hG : CanonRelG G' G) (b : Nat) (aop : AssocOp) (t : Ty)
    {a₁' b₁' : Arg (CanonVal V₁) t} {a₂' b₂' : Arg (CanonVal V₂) t}
    (ha' : ArgRel G t a₁' a₂') (hb' : ArgRel G t b₁' b₂') :
    CanonStepRel G' (canonAssocCore b aop t a₁' b₁') (canonAssocCore b aop t a₂' b₂') := by
  dsimp only [canonAssocCore]
  have hb_imm : b₁'.cnout.imm? = b₂'.cnout.imm? := argRel_imm?_eq (hb'.cnout hG)
  rw [hb_imm]
  cases himm : b₂'.cnout.imm? with
  | none =>
    refine ⟨.mk _ (.cons (ha'.cnout hG) (.cons (hb'.cnout hG) .nil)), fun xs₁ xs₂ => ?_⟩
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
    exact .cons (CanonValRel.fresh b List.mem_cons_self) .nil
  | some c₂ =>
    have hdef := ha'.cndef_rel hG
    cases hd₁ : a₁'.cndef? <;> cases hd₂ : a₂'.cndef? <;> rw [hd₁, hd₂] at hdef
    · exact ⟨.mk _ (.cons (ha'.cnout hG) (.cons (.imm c₂) .nil)), fun xs₁ xs₂ => by
        rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
        have hsub : ∀ p ∈ G', p ∈ (Tup.zip (as := [t]) (r₁, ()) (r₂, ()) ++ G') :=
          fun _ hq => List.mem_cons_of_mem _ hq
        exact .cons ⟨.var List.mem_cons_self, rfl,
          ⟨rfl, (ha'.cnout hG).weaken hsub, rfl⟩⟩ .nil⟩
    · exact False.elim hdef
    · exact False.elim hdef
    · rcases hdef with ⟨hop, hbase, himm⟩
      dsimp only
      rw [hop, himm]
      cases heq : (_ == aop)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨.mk _ (.cons (ha'.cnout hG) (.cons (.imm c₂) .nil)), fun xs₁ xs₂ => by
          rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
          have hsub : ∀ p ∈ G', p ∈ (Tup.zip (as := [t]) (r₁, ()) (r₂, ()) ++ G') :=
            fun _ hq => List.mem_cons_of_mem _ hq
          exact .cons ⟨.var List.mem_cons_self, rfl,
            ⟨rfl, (ha'.cnout hG).weaken hsub, rfl⟩⟩ .nil⟩
      · simp only [↓reduceIte]
        exact ⟨.mk _ (.cons hbase (.cons (.imm _) .nil)), fun xs₁ xs₂ => by
          rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
          have hsub : ∀ p ∈ G', p ∈ (Tup.zip (as := [t]) (r₁, ()) (r₂, ()) ++ G') :=
            fun _ hq => List.mem_cons_of_mem _ hq
          exact .cons ⟨.var List.mem_cons_self, rfl, ⟨rfl, hbase.weaken hsub, rfl⟩⟩ .nil⟩

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
