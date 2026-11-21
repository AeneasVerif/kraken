module

public import LeanQbe.T.LegalCheck1a
public import LeanQbe.T.LegalWpBaseLemmas1

/-!
# Bundled straight-line legalizer combinators (`Emit`, `LegalEmitSpec`)

Provides a 5-constructor typed DAG/CPS builder `Emit inTys outTy` whose `Emit.run` compiles
*definitionally* (`rfl`) to `LeanQbe.T.Expr V L rs` while verifying `isLegal`, `Wf`, and `wp` in a
single structural induction:

* Master theorems: `Emit.run_isLegal`, `Emit.run_wf`, `Emit.wp_mono`, `Emit.run_wp`, and
  `Emit.bundle` / `Emit.bundlePure` returning `LegalEmitSpec`.
* Definitional bridges (`*_eq_emit*`) and single-pass `LegalEmitSpec` bundles for the 5 `LegalBase`
  builders: `emitBoolCmp`, `emitBoolSelect`, `emitMaskToN`, `emitSextToW`, and `emitTernlogBool`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## 1. Five-constructor `Emit` DAG and single-induction `LegalEmitSpec` bundle -/

/-- Typed straight-line legalizer DAG parameterized by input context `inTys`. -/
inductive Emit : List Ty → Ty → Type where
  | arg  {inTys : List Ty} {t : Ty} (i : Member t inTys) : Emit inTys t
  | imm  {inTys : List Ty} {t : Ty} (v : Val t) : Emit inTys t
  | op1  {inTys : List Ty} {a b : Ty} (code : OpCode [a] [b]) (e : Emit inTys a) :
      Emit inTys b
  | op2  {inTys : List Ty} {a b c : Ty} (code : OpCode [a, b] [c])
      (e₁ : Emit inTys a) (e₂ : Emit inTys b) : Emit inTys c
  | letE {inTys : List Ty} {a b : Ty} (rhs : Emit inTys a) (body : Emit (a :: inTys) b) :
      Emit inTys b

/-- Compile `Emit` into PHOAS `Expr V L rs` with zero runtime/wrapper overhead. -/
def Emit.run {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {inTys : List Ty} → {t : Ty} → Emit inTys t →
    Tup (Arg V) inTys → (Arg V t → Expr V L rs) → Expr V L rs
  | _, _, .arg i, env, k => k (env.get i)
  | _, _, .imm v, _, k => k (.imm v)
  | _, _, .op1 code e, env, k =>
    e.run env fun x => .let_ (LeanQbe.T.op1 code x) fun (r, ()) => k (.var r)
  | _, _, .op2 code e₁ e₂, env, k =>
    e₁.run env fun x => e₂.run env fun y =>
      .let_ (LeanQbe.T.op2 code x y) fun (r, ()) => k (.var r)
  | _, _, .letE rhs body, env, k =>
    rhs.run env fun x => body.run (x, env) k

/-- Weakest-precondition semantics of an `Emit` program (supports both total and guarded ops). -/
def Emit.wp : {inTys : List Ty} → {t : Ty} → Emit inTys t →
    Tup Val inTys → (Val t → Prop) → Prop
  | _, _, .arg i, env, post => post (env.get i)
  | _, _, .imm v, _, post => post v
  | _, _, .op1 code e, env, post =>
    e.wp env fun x => OpCode.wp code (x, ()) fun (r, ()) => post r
  | _, _, .op2 code e₁ e₂, env, post =>
    e₁.wp env fun x => e₂.wp env fun y => OpCode.wp code (x, y, ()) fun (r, ()) => post r
  | _, _, .letE rhs body, env, post =>
    rhs.wp env fun x => body.wp (x, env) post

/-- Single-pass target-legality condition for `Emit` (no `CtxExtends` threading needed). -/
def Emit.IsLegal (target : LegalTarget) : {inTys : List Ty} → {t : Ty} → Emit inTys t → Prop
  | _, _, .arg _ => True
  | _, t, .imm _ => target.isLegalTy t = true
  | _, b, .op1 code e =>
    e.IsLegal target ∧ code.isPackBridge = false ∧
      target.isLegalOp code false = true ∧ target.isLegalTy b = true
  | _, c, .op2 code e₁ e₂ =>
    e₁.IsLegal target ∧ e₂.IsLegal target ∧ code.isPackBridge = false ∧
      (∀ u : Bool, target.isLegalOp code u = true) ∧ target.isLegalTy c = true
  | _, _, .letE rhs body => rhs.IsLegal target ∧ body.IsLegal target

private theorem argsNormal_get {target : LegalTarget} {Γ : List (Ty × VarKind)} :
    ∀ {ts : List Ty} {env : Tup (Arg K) ts} {t : Ty},
      ArgsNormal target Γ env → (i : Member t ts) → ArgNormal target Γ t (env.get i)
  | _ :: _, (_, _), _, ⟨h, _⟩, .here => h
  | _ :: _, (_, _), _, ⟨_, hs⟩, .there i => argsNormal_get hs i

private theorem trel_get {α : Type} {f g : α → Type} {R : ∀ a, f a → g a → Prop} :
    ∀ {ts : List α} {xs : Tup f ts} {ys : Tup g ts} {a : α},
      TRel R xs ys → (i : Member a ts) → R a (xs.get i) (ys.get i)
  | _ :: _, (_, _), (_, _), _, .cons h _, .here => h
  | _ :: _, (_, _), (_, _), _, .cons _ hs, .there i => trel_get hs i

private theorem valsTup_get :
    ∀ {ts : List Ty} (env : Tup (Arg Val) ts) {t : Ty} (i : Member t ts),
      (env.get i).val = (valsTup env).get i
  | _ :: _, (_, _), _, .here => rfl
  | _ :: _, (_, _), _, .there i => valsTup_get _ i

/-- Master theorem 1: every `Emit.IsLegal` program produces `TFlat.isLegal = true`. -/
theorem Emit.run_isLegal (target : LegalTarget) :
    ∀ {inTys : List Ty} {t : Ty} (e : Emit inTys t)
      {Γ : List (Ty × VarKind)} {Δ : List (List Ty)} {rs : List Ty}
      (env : Tup (Arg K) inTys),
      e.IsLegal target → ArgsNormal target Γ env →
      ∀ {k : Arg K t → Expr K KL rs},
        IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' t r) k →
        (toTFlat (e.run env k) Γ.length Δ.length).isLegal target Γ Δ = true
  | _, _, .arg i, Γ, _, _, env, _, henv, _, hk =>
    hk Γ (env.get i) (CtxExtends.refl Γ) (argsNormal_get henv i)
  | _, _, .imm v, Γ, _, _, _, hleg, _, _, hk =>
    hk Γ (.imm v) (CtxExtends.refl Γ) hleg
  | _, b, .op1 code e, _, _, _, env, hleg, henv, _, hk => by
    obtain ⟨he, hne, hop, hb⟩ := hleg
    exact e.run_isLegal target env he henv fun Γ1 x h1 hx => by
      refine isLegal_let_op1_normal target code x _ hne hop hx hb ?_
      exact hk ((b, .normal) :: Γ1) (.var Γ1.length)
        (h1.trans (CtxExtends.cons _ _)) (ArgNormal.head target Γ1 hb)
  | _, c, .op2 code e₁ e₂, _, _, _, env, hleg, henv, _, hk => by
    obtain ⟨he1, he2, hne, hop, hc⟩ := hleg
    exact e₁.run_isLegal target env he1 henv fun Γ1 x h1 hx =>
      e₂.run_isLegal target env he2 (henv.mono h1) fun Γ2 y h2 hy => by
        refine isLegal_let_op2_normal target code x y _ hne (hop _) (hx.mono h2) hy hc ?_
        exact hk ((c, .normal) :: Γ2) (.var Γ2.length)
          ((h1.trans h2).trans (CtxExtends.cons _ _)) (ArgNormal.head target Γ2 hc)
  | _, _, .letE rhs body, _, _, _, env, hleg, henv, _, hk => by
    obtain ⟨hrhs, hbody⟩ := hleg
    exact rhs.run_isLegal target env hrhs henv fun _ x h1 hx =>
      body.run_isLegal target (x, env) hbody ⟨hx, henv.mono h1⟩ fun Γ2 r h2 hr =>
        hk Γ2 r (h1.trans h2) hr

/-- Master theorem 2: every `Emit` program is unconditionally `Wf`. -/
theorem Emit.run_wf :
    ∀ {inTys : List Ty} {t : Ty} (e : Emit inTys t)
      {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
      {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {env₁ : Tup (Arg V₁) inTys} {env₂ : Tup (Arg V₂) inTys},
      TRel (ArgRel G) env₁ env₂ →
      ∀ {k₁ : Arg V₁ t → Expr V₁ L₁ rs} {k₂ : Arg V₂ t → Expr V₂ L₂ rs},
        (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' t y₁ y₂ →
          Wf G' D (k₁ y₁) (k₂ y₂)) →
        Wf G D (e.run env₁ k₁) (e.run env₂ k₂)
  | _, _, .arg i, _, _, _, _, _, _, _, _, _, henv, _, _, hk =>
    hk (fun _ h => h) _ _ (trel_get henv i)
  | _, _, .imm _, _, _, _, _, _, _, _, _, _, _, _, _, hk =>
    hk (fun _ h => h) _ _ (.imm _)
  | _, _, .op1 code e, _, _, _, _, _, _, _, _, _, henv, _, _, hk =>
    e.run_wf henv fun h1 _ _ hx =>
      Wf.let1 code hx fun h2 r₁ r₂ hr => hk (sub_trans h1 h2) r₁ r₂ hr
  | _, _, .op2 code e₁ e₂, _, _, _, _, _, _, _, _, _, henv, _, _, hk =>
    e₁.run_wf henv fun h1 _ _ hx =>
      e₂.run_wf (TRel_argRel_weaken' h1 henv) fun h2 _ _ hy =>
        Wf.let2 code (hx.weaken h2) hy fun h3 r₁ r₂ hr =>
          hk (sub_trans h1 (sub_trans h2 h3)) r₁ r₂ hr
  | _, _, .letE rhs body, _, _, _, _, _, _, _, _, _, henv, _, _, hk =>
    rhs.run_wf henv fun h1 _ _ hx =>
      body.run_wf (.cons hx (TRel_argRel_weaken' h1 henv)) fun h2 r₁ r₂ hr =>
        hk (sub_trans h1 h2) r₁ r₂ hr

/-- Monotonicity of `Emit.wp` in its postcondition. -/
theorem Emit.wp_mono : ∀ {inTys : List Ty} {t : Ty} (e : Emit inTys t)
    {env : Tup Val inTys} {p q : Val t → Prop},
    (∀ v, p v → q v) → e.wp env p → e.wp env q
  | _, _, .arg _, _, _, _, hpq, h => hpq _ h
  | _, _, .imm _, _, _, _, hpq, h => hpq _ h
  | _, _, .op1 code e, _, _, _, hpq, h =>
    e.wp_mono (fun x hx => OpCode.wp_mono code (x, ()) (fun (r, ()) hr => hpq r hr) hx) h
  | _, _, .op2 code e₁ e₂, _, _, _, hpq, h =>
    e₁.wp_mono (fun x hx => e₂.wp_mono (fun y hy =>
      OpCode.wp_mono code (x, y, ()) (fun (r, ()) hr => hpq r hr) hy) hx) h
  | _, _, .letE rhs body, _, _, _, hpq, h =>
    rhs.wp_mono (fun _ hx => body.wp_mono hpq hx) h

/-- Master theorem 3: every `Emit` program satisfies `wp` w.r.t. `Emit.wp`. -/
theorem Emit.run_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64} :
    ∀ {inTys : List Ty} {t : Ty} (e : Emit inTys t)
      (env : Tup (Arg Val) inTys) {k : Arg Val t → Expr Val Cont rs},
      e.wp (valsTup env) (fun v => ∀ r : Arg Val t, r.val = v → LeanQbe.T.wp Γ Q X (k r) m) →
      LeanQbe.T.wp Γ Q X (e.run env k) m
  | _, _, .arg i, env, _, hpost => hpost (env.get i) (valsTup_get env i)
  | _, _, .imm v, _, _, hpost => hpost (.imm v) rfl
  | _, _, .op1 code e, env, _, hpost =>
    e.run_wp env <| e.wp_mono (fun x hx rx hrx => by
      dsimp only [LeanQbe.T.wp, Op.wp, vals, LeanQbe.T.op1]
      rw [hrx]
      exact OpCode.wp_mono code (x, ()) (fun (rv, ()) hrv => hrv (.var rv) rfl) hx) hpost
  | _, _, .op2 code e₁ e₂, env, _, hpost =>
    e₁.run_wp env <| e₁.wp_mono (fun x hx rx hrx =>
      e₂.run_wp env <| e₂.wp_mono (fun y hy ry hry => by
        dsimp only [LeanQbe.T.wp, Op.wp, vals, LeanQbe.T.op2]
        rw [hrx, hry]
        exact OpCode.wp_mono code (x, y, ()) (fun (rv, ()) hrv => hrv (.var rv) rfl) hy) hx) hpost
  | _, _, .letE rhs body, env, _, hpost =>
    rhs.run_wp env <| rhs.wp_mono (fun _ hx rx hrx =>
      body.run_wp (rx, env) (by simpa only [valsTup_cons, hrx] using hx)) hpost

/-- Bundled 3-in-1 specification record (`isLegal`, `Wf`, `wp`) for an `Emit` builder. -/
structure LegalEmitSpec (target : LegalTarget) {inTys : List Ty} {t : Ty}
    (e : Emit inTys t) (sem : Tup Val inTys → (Val t → Prop) → Prop) : Prop where
  isLegal : ∀ {Γ Δ rs} (env : Tup (Arg K) inTys), ArgsNormal target Γ env →
    ∀ {k : Arg K t → Expr K KL rs},
      IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' t r) k →
      (toTFlat (e.run env k) Γ.length Δ.length).isLegal target Γ Δ = true
  wf : ∀ {V₁ V₂ L₁ L₂ rs} {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {env₁ : Tup (Arg V₁) inTys} {env₂ : Tup (Arg V₂) inTys},
    TRel (ArgRel G) env₁ env₂ →
    ∀ {k₁ : Arg V₁ t → Expr V₁ L₁ rs} {k₂ : Arg V₂ t → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' t y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (e.run env₁ k₁) (e.run env₂ k₂)
  wp : ∀ {Γ rs Q X m} (env : Tup (Arg Val) inTys) {k : Arg Val t → Expr Val Cont rs},
    sem (valsTup env) (fun v => ∀ r, r.val = v → LeanQbe.T.wp Γ Q X (k r) m) →
    LeanQbe.T.wp Γ Q X (e.run env k) m

/-- Derive `isLegal` for an existing PHOAS builder `rhs` equal to `e.run env k`. -/
theorem LegalEmitSpec.isLegal_eq {target : LegalTarget} {inTys : List Ty} {t : Ty}
    {e : Emit inTys t} {sem : Tup Val inTys → (Val t → Prop) → Prop}
    (h : LegalEmitSpec target e sem) {Γ Δ rs} (env : Tup (Arg K) inTys)
    (henv : ArgsNormal target Γ env) {k : Arg K t → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' t r) k)
    {rhs : Expr K KL rs} (heq : e.run env k = rhs) :
    (toTFlat rhs Γ.length Δ.length).isLegal target Γ Δ = true :=
  heq ▸ h.isLegal env henv hk

/-- Derive `Wf` for an existing PHOAS builder `rhs₁`/`rhs₂` equal to `e.run envᵢ kᵢ`. -/
theorem LegalEmitSpec.wf_eq {target : LegalTarget} {inTys : List Ty} {t : Ty}
    {e : Emit inTys t} {sem : Tup Val inTys → (Val t → Prop) → Prop}
    (h : LegalEmitSpec target e sem) {V₁ V₂ L₁ L₂ rs} {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {env₁ : Tup (Arg V₁) inTys} {env₂ : Tup (Arg V₂) inTys}
    (henv : TRel (ArgRel G) env₁ env₂)
    {k₁ : Arg V₁ t → Expr V₁ L₁ rs} {k₂ : Arg V₂ t → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' t y₁ y₂ →
      Wf G' D (k₁ y₁) (k₂ y₂))
    {rhs₁ : Expr V₁ L₁ rs} {rhs₂ : Expr V₂ L₂ rs}
    (heq₁ : e.run env₁ k₁ = rhs₁) (heq₂ : e.run env₂ k₂ = rhs₂) :
    Wf G D rhs₁ rhs₂ :=
  heq₁ ▸ heq₂ ▸ h.wf henv hk

/-- Derive `wp` for an existing PHOAS builder `rhs` equal to `e.run env k`. -/
theorem LegalEmitSpec.wp_eq {target : LegalTarget} {inTys : List Ty} {t : Ty}
    {e : Emit inTys t} {sem : Tup Val inTys → (Val t → Prop) → Prop}
    (h : LegalEmitSpec target e sem) {Γ rs Q X m} (env : Tup (Arg Val) inTys)
    {k : Arg Val t → Expr Val Cont rs}
    (hsem : sem (valsTup env) (fun v => ∀ r, r.val = v → LeanQbe.T.wp Γ Q X (k r) m))
    {rhs : Expr Val Cont rs} (heq : e.run env k = rhs) :
    LeanQbe.T.wp Γ Q X rhs m :=
  heq ▸ h.wp env hsem

/-- Construct all three (`isLegal`, `wf`, `wp`) from `(hleg : e.IsLegal target)` and a pure
semantic implication `hsem : sem → e.wp`. -/
theorem Emit.bundle (target : LegalTarget) {inTys : List Ty} {t : Ty} (e : Emit inTys t)
    {sem : Tup Val inTys → (Val t → Prop) → Prop}
    (hleg : e.IsLegal target)
    (hsem : ∀ env p, sem env p → e.wp env p) :
    LegalEmitSpec target e sem :=
  ⟨fun env henv _ hk => e.run_isLegal target env hleg henv hk,
   fun henv _ _ hk => e.run_wf henv hk,
   fun env _ hpost => e.run_wp env (hsem _ _ hpost)⟩

/-- Construct `LegalEmitSpec` for a total deterministic semantics `f : Tup Val inTys → Val t`. -/
theorem Emit.bundlePure (target : LegalTarget) {inTys : List Ty} {t : Ty} (e : Emit inTys t)
    (f : Tup Val inTys → Val t)
    (hleg : e.IsLegal target)
    (hsem : ∀ env, e.wp env (fun r => r = f env)) :
    LegalEmitSpec target e (fun env p => p (f env)) :=
  e.bundle target hleg fun env _ hp =>
    e.wp_mono (fun r (hr : r = f env) => hr.symm ▸ hp) (hsem env)

/-! ## 2. `LegalBase` builders via `Emit` with `rfl` bridges -/

/-! ### `emitBoolCmp` -/

/-- `Emit` compilation of `LeanQbe.T.emitBoolCmp`. -/
def boolCmpEmit : CmpOp → Emit [.bool, .bool] .bool
  | .eq => .op1 (.not .bool) (.op2 (.xor .bool) (.arg .here) (.arg (.there .here)))
  | .ne => .op2 (.xor .bool) (.arg .here) (.arg (.there .here))
  | .ult | .sgt => .op2 (.and .bool) (.op1 (.not .bool) (.arg .here)) (.arg (.there .here))
  | .ule | .sge => .op2 (.or .bool) (.op1 (.not .bool) (.arg .here)) (.arg (.there .here))
  | .ugt | .slt => .op2 (.and .bool) (.arg .here) (.op1 (.not .bool) (.arg (.there .here)))
  | .uge | .sle => .op2 (.or .bool) (.arg .here) (.op1 (.not .bool) (.arg (.there .here)))

/-- Exact definitional (`rfl` per `CmpOp`) correspondence with `emitBoolCmp`. -/
theorem boolCmpEmit_eq_emitBoolCmp {V L rs} (o : CmpOp) (a b : Arg V .bool)
    (k : Arg V .bool → Expr V L rs) :
    (boolCmpEmit o).run (a, b, ()) k = emitBoolCmp o a b k := by
  cases o <;> rfl

/-- Single-pass `isLegal + Wf + wp` bundle for `boolCmpEmit`. -/
theorem boolCmpEmit_bundle (target : LegalTarget) (o : CmpOp) :
    LegalEmitSpec target (boolCmpEmit o) (fun (a, b, ()) p => p (o.evalBool a b)) :=
  (boolCmpEmit o).bundle target
    (by cases o <;> simp [boolCmpEmit, Emit.IsLegal, OpCode.isPackBridge,
      LegalTarget.isLegalOp, LegalTarget.isLegalTy])
    (fun (a, b, ()) p hp => by
      cases o <;> cases a <;> cases b <;>
        simpa [boolCmpEmit, Emit.wp, Tup.get, OpCode.wp, lift1, lift2, CmpOp.evalBool] using hp)

/-! ### `emitBoolSelect` -/

/-- `Emit` compilation of `LeanQbe.T.emitBoolSelect`. -/
def boolSelectEmit : Emit [.bool, .bool, .bool] .bool :=
  .op2 (.or .bool)
    (.op2 (.and .bool) (.arg .here) (.arg (.there .here)))
    (.op2 (.and .bool) (.op1 (.not .bool) (.arg .here)) (.arg (.there (.there .here))))

/-- Exact definitional (`rfl`) correspondence with `emitBoolSelect`. -/
theorem boolSelectEmit_eq_emitBoolSelect {V L rs} (c a b : Arg V .bool)
    (k : Arg V .bool → Expr V L rs) :
    boolSelectEmit.run (c, a, b, ()) k = emitBoolSelect c a b k := rfl

/-- Single-pass `isLegal + Wf + wp` bundle for `boolSelectEmit`. -/
theorem boolSelectEmit_bundle (target : LegalTarget) :
    LegalEmitSpec target boolSelectEmit (fun (c, a, b, ()) p => p (if c then a else b)) :=
  boolSelectEmit.bundle target
    (by simp [boolSelectEmit, Emit.IsLegal, OpCode.isPackBridge,
      LegalTarget.isLegalOp, LegalTarget.isLegalTy])
    (fun (c, a, b, ()) p hp => by
      cases c <;> cases a <;> cases b <;>
        simpa [boolSelectEmit, Emit.wp, Tup.get, OpCode.wp, lift1, lift2] using hp)

/-! ### `emitMaskToN` -/

/-- `Emit` compilation of `LeanQbe.T.emitMaskToN`. -/
def maskToNEmit (n w : Nat) : Emit [.bits w] (.bits w) :=
  if n == 0 then .imm 0#w
  else if w ≤ n then .arg .here
  else .op2 (.and (.bits w)) (.arg .here) (.imm (lowMask n w))

/-- Exact definitional (`rfl` per branch) correspondence with `emitMaskToN`. -/
theorem maskToNEmit_eq_emitMaskToN {V L rs} (n w : Nat) (x : Arg V (.bits w))
    (k : Arg V (.bits w) → Expr V L rs) :
    (maskToNEmit n w).run (x, ()) k = emitMaskToN n w x k := by
  unfold maskToNEmit emitMaskToN
  split
  · rfl
  · split <;> rfl

/-- Single-pass `isLegal + Wf + wp` bundle for `maskToNEmit`. -/
theorem maskToNEmit_bundle (target : LegalTarget) {n w : Nat} (hw : w ∈ target.bitWidths)
    (hnw : n ≤ w) :
    LegalEmitSpec target (maskToNEmit n w) (fun (x, ()) p => p ((x.setWidth n).setWidth w)) :=
  (maskToNEmit n w).bundle target
    (by
      unfold maskToNEmit
      split
      · simp [Emit.IsLegal, LegalTarget.isLegalTy, hw]
      · split
        · trivial
        · simp [Emit.IsLegal, OpCode.isPackBridge, LegalTarget.isLegalOp,
            LegalTarget.isLegalTy, hw])
    (fun (x, ()) p hp => by
      unfold maskToNEmit
      split
      · rename_i hn0; have : n = 0 := beq_iff_eq.mp hn0; subst this
        simpa [Emit.wp, BitVec.eq_nil (x.setWidth 0)] using hp
      · split
        · rename_i hle; have : n = w := Nat.le_antisymm hnw hle; subst this
          simpa [Emit.wp, Tup.get, BitVec.setWidth_eq] using hp
        · simpa [Emit.wp, Tup.get, OpCode.wp, lift2, lowMask_and hnw] using hp)

/-! ### `emitSextToW` -/

/-- `Emit` compilation of `LeanQbe.T.emitSextToW`. -/
def sextToWEmit (n w : Nat) : Emit [.bits w] (.bits w) :=
  if n == 0 || w ≤ n then .arg .here
  else
    let sh := BitVec.ofNat w (w - n)
    .op2 (.ashr (.bits w)) (.op2 (.shl (.bits w)) (.arg .here) (.imm sh)) (.imm sh)

/-- Exact definitional (`rfl` per branch) correspondence with `emitSextToW`. -/
theorem sextToWEmit_eq_emitSextToW {V L rs} (n w : Nat) (x : Arg V (.bits w))
    (k : Arg V (.bits w) → Expr V L rs) :
    (sextToWEmit n w).run (x, ()) k = emitSextToW n w x k := by
  unfold sextToWEmit emitSextToW; split <;> rfl

private theorem signExtend_eq_shl_ashr_aux {n w : Nat} (hn0 : 0 < n) (hnw : n < w)
    (a : BitVec n) :
    (a.setWidth w <<< (w - n)).sshiftRight (w - n) = a.signExtend w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_sshiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi]
  have hmsb : ((a.setWidth w) <<< (w - n)).msb = a.msb := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last]
    simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    have hd1 : decide (w - 1 < w) = true := decide_eq_true (by omega)
    have hd2 : decide (w - 1 < w - n) = false := decide_eq_false (by omega)
    have hd3 : decide (n - 1 < w) = true := decide_eq_true (by omega)
    have hcancel : w - 1 - (w - n) = n - 1 := by omega
    simp only [hd1, hd2, hd3, hcancel, Bool.not_false, Bool.true_and]
  by_cases hin : i < n
  · have hltw : w - n + i < w := by omega
    have hnot2 : ¬ (w ≤ i) := by omega
    have hge : ¬ (w - n + i < w - n) := by omega
    have hcancel : w - n + i - (w - n) = i := by omega
    simp [hltw, hnot2, hge, hcancel, hin, hi]
  · have hge : ¬ (w - n + i < w) := by omega
    have hnot2 : ¬ (w ≤ i) := by omega
    simp [hge, hin, hmsb, hnot2]

/-- Single-pass `isLegal + Wf + wp` bundle for `sextToWEmit`. -/
theorem sextToWEmit_bundle (target : LegalTarget) {n w : Nat} (hw : w ∈ target.bitWidths)
    (hn0 : 0 < n) (hnw : n ≤ w) :
    LegalEmitSpec target (sextToWEmit n w)
      (fun (x, ()) p => ∃ a : BitVec n, x = a.setWidth w ∧ p (a.signExtend w)) :=
  (sextToWEmit n w).bundle target
    (by
      unfold sextToWEmit; split
      · trivial
      · simp [Emit.IsLegal, OpCode.isPackBridge, LegalTarget.isLegalOp,
          LegalTarget.isLegalTy, hw])
    (fun (x, ()) p ⟨a, hx, hp⟩ => by
      subst hx; unfold sextToWEmit; split
      · rename_i hskip
        have hn0f : (n == 0) = false := beq_false_of_ne (by omega)
        simp only [hn0f, Bool.false_or, decide_eq_true_eq] at hskip
        have heq : n = w := Nat.le_antisymm hnw hskip; subst heq
        simpa [Emit.wp, Tup.get, BitVec.setWidth_eq, BitVec.signExtend_eq] using hp
      · rename_i hnskip
        have hnwl : n < w := by
          have : ¬(n == 0 || decide (w ≤ n)) = true := hnskip
          simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at this; omega
        have hpow : w < 2 ^ w := @Nat.lt_pow_self w 2 (by decide)
        have hsh : (BitVec.ofNat w (w - n)).toNat % w = w - n := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (by omega) hpow),
            Nat.mod_eq_of_lt (by omega)]
        simp only [Emit.wp, Tup.get, OpCode.wp, lift2, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
        rw [hsh, signExtend_eq_shl_ashr_aux hn0 hnwl a]
        exact hp)

/-! ### `emitTernlogBool` -/

/-- Structural AST builder for `emitTernlogBool` (context order `[nc, nb, na, a, b, c]`). -/
def ternlogBoolGo (imm : BitVec 8) :
    Nat → Option (Emit [.bool, .bool, .bool, .bool, .bool, .bool] .bool) →
    Emit [.bool, .bool, .bool, .bool, .bool, .bool] .bool
  | 0, some acc => acc
  | 0, none => .imm false
  | k + 1, acc =>
    let idx := 7 - k
    if imm.getLsbD idx then
      let pa : Emit _ .bool := if idx / 4 % 2 == 1 then .arg (.there (.there (.there .here)))
        else .arg (.there (.there .here))
      let pb : Emit _ .bool :=
        if idx / 2 % 2 == 1 then .arg (.there (.there (.there (.there .here))))
        else .arg (.there .here)
      let pc : Emit _ .bool :=
        if idx % 2 == 1 then .arg (.there (.there (.there (.there (.there .here)))))
        else .arg .here
      let term := .op2 (.and .bool) (.op2 (.and .bool) pa pb) pc
      let acc' := match acc with
        | none => term
        | some prev => .op2 (.or .bool) prev term
      ternlogBoolGo imm k (some acc')
    else ternlogBoolGo imm k acc

/-- `Emit` compilation of `LeanQbe.T.emitTernlogBool`. -/
def ternlogBoolEmit (imm : BitVec 8) : Emit [.bool, .bool, .bool] .bool :=
  if imm == 0#8 then .imm false
  else if imm == 0xff#8 then .imm true
  else
    .letE (.op1 (.not .bool) (.arg .here)) <|
    .letE (.op1 (.not .bool) (.arg (.there (.there .here)))) <|
    .letE (.op1 (.not .bool) (.arg (.there (.there (.there (.there .here)))))) <|
      ternlogBoolGo imm 8 none

private theorem ite_arg_run {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    {inTys : List Ty} {t : Ty} (b : Bool) (i j : Member t inTys)
    (env : Tup (Arg V) inTys) (k : Arg V t → Expr V L rs) :
    (if b then Emit.arg i else Emit.arg j).run env k =
      k (if b then env.get i else env.get j) := by
  cases b <;> rfl

private theorem ternlogBoolGo_run_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (imm : BitVec 8) (a b c : Arg V .bool) (na nb nc : V .bool)
    (k : Arg V .bool → Expr V L rs) :
    ∀ (d : Nat) (_hd : d ≤ 8)
      (acc : Option (Emit [.bool, .bool, .bool, .bool, .bool, .bool] .bool)),
      let env : Tup (Arg V) [.bool, .bool, .bool, .bool, .bool, .bool] :=
        (.var nc, .var nb, .var na, a, b, c, ())
      (ternlogBoolGo imm d acc).run env k =
        match acc with
        | none => emitTernlogBool.go imm k (8 - d) none a b c (.var na) (.var nb) (.var nc)
        | some prev => prev.run env fun p =>
            emitTernlogBool.go imm k (8 - d) (some p) a b c (.var na) (.var nb) (.var nc)
  | 0, _, none => by
    rw [emitTernlogBool.go.eq_def]
    rfl
  | 0, _, some prev => by
    dsimp only [ternlogBoolGo]
    congr 1; funext p
    rw [emitTernlogBool.go.eq_def]
    rfl
  | d + 1, hd, acc => by
    have hlt : ¬ (8 - (d + 1) ≥ 8) := by omega
    have hidx : 7 - d = 8 - (d + 1) := by omega
    have hnext : 8 - (d + 1) + 1 = 8 - d := by omega
    dsimp only [ternlogBoolGo]
    rw [hidx]
    by_cases hbit : imm.getLsbD (8 - (d + 1)) = true
    · simp only [hbit, ↓reduceIte]
      cases acc with
      | none =>
        rw [ternlogBoolGo_run_eq imm a b c na nb nc k d (by omega)]
        rw [emitTernlogBool.go.eq_def imm k (8 - (d + 1)) none a b c (.var na) (.var nb) (.var nc)]
        simp only [hlt, ↓reduceIte, hbit, hnext, Emit.run, ite_arg_run, Tup.get]
      | some prev =>
        rw [ternlogBoolGo_run_eq imm a b c na nb nc k d (by omega)]
        dsimp only [Emit.run]
        congr 1; funext p
        rw [emitTernlogBool.go.eq_def imm k (8 - (d + 1)) (some p) a b c
          (.var na) (.var nb) (.var nc)]
        simp only [hlt, ↓reduceIte, hbit, hnext, ite_arg_run, Tup.get]
    · simp only [hbit, Bool.false_eq_true, ↓reduceIte]
      cases acc with
      | none =>
        rw [ternlogBoolGo_run_eq imm a b c na nb nc k d (by omega)]
        rw [emitTernlogBool.go.eq_def imm k (8 - (d + 1)) none a b c (.var na) (.var nb) (.var nc)]
        simp only [hlt, ↓reduceIte, hbit, Bool.false_eq_true, hnext]
      | some prev =>
        rw [ternlogBoolGo_run_eq imm a b c na nb nc k d (by omega)]
        dsimp only
        congr 1; funext p
        rw [emitTernlogBool.go.eq_def imm k (8 - (d + 1)) (some p) a b c
          (.var na) (.var nb) (.var nc)]
        simp only [hlt, ↓reduceIte, hbit, Bool.false_eq_true, hnext]

/-- Exact correspondence between `(ternlogBoolEmit imm).run` and `emitTernlogBool` for all
`imm : BitVec 8` (and `rfl` on `0#8`/`0xff#8` and loop-free cases). -/
theorem ternlogBoolEmit_eq_emitTernlogBool {V L rs} (imm : BitVec 8) (a b c : Arg V .bool)
    (k : Arg V .bool → Expr V L rs) :
    (ternlogBoolEmit imm).run (a, b, c, ()) k = emitTernlogBool a b c imm k := by
  unfold ternlogBoolEmit emitTernlogBool
  split
  · rfl
  · split
    · rfl
    · dsimp only [Emit.run, Tup.get]
      congr 1; funext (na, _)
      congr 1; funext (nb, _)
      congr 1; funext (nc, _)
      exact ternlogBoolGo_run_eq imm a b c na nb nc k 8 (Nat.le_refl _) none

private theorem ternlogBoolGo_isLegal (target : LegalTarget) (imm : BitVec 8) :
    ∀ k acc, (∀ e, acc = some e → e.IsLegal target) → (ternlogBoolGo imm k acc).IsLegal target
  | 0, some e, h => h e rfl
  | 0, none, _ => rfl
  | k + 1, acc, h => by
    dsimp only [ternlogBoolGo]
    by_cases hbit : imm.getLsbD (7 - k) = true
    · simp only [hbit, ↓reduceIte]
      refine ternlogBoolGo_isLegal target imm k _ fun e he => ?_
      cases he
      cases acc with
      | none =>
        refine ⟨⟨?_, ?_, rfl, fun _ => rfl, rfl⟩, ?_, rfl, fun _ => rfl, rfl⟩ <;>
          (split <;> trivial)
      | some prev =>
        refine ⟨h prev rfl, ⟨⟨?_, ?_, rfl, fun _ => rfl, rfl⟩, ?_, rfl, fun _ => rfl, rfl⟩,
          rfl, fun _ => rfl, rfl⟩ <;> (split <;> trivial)
    · simp only [hbit]
      exact ternlogBoolGo_isLegal target imm k acc h

private theorem ternlogBoolGo_wp (imm : BitVec 8) (a b c : Bool) :
    ∀ k (_hk : k ≤ 8) acc (v0 : Bool),
      (∀ e p, acc = some e → p v0 → e.wp (!c, !b, !a, a, b, c, ()) p) →
      (acc = none → v0 = false) →
      ∀ p, p (([0, 1, 2, 3, 4, 5, 6, 7].drop (8 - k)).foldl (fun cur i =>
        if imm.getLsbD i then
          cur || ((if i / 4 % 2 == 1 then a else !a) &&
                  (if i / 2 % 2 == 1 then b else !b) &&
                  (if i % 2 == 1 then c else !c))
        else cur) v0) →
      (ternlogBoolGo imm k acc).wp (!c, !b, !a, a, b, c, ()) p
  | 0, _, some e, _, hacc, _, p, hp => hacc e p rfl hp
  | 0, _, none, _, _, hnone, p, hp => by
    dsimp only [ternlogBoolGo, Emit.wp]
    simpa [hnone rfl] using hp
  | k + 1, hk, acc, v0, hacc, hnone, p, hp => by
    have hdrop : [0, 1, 2, 3, 4, 5, 6, 7].drop (8 - (k + 1)) =
        (7 - k) :: [0, 1, 2, 3, 4, 5, 6, 7].drop (8 - k) := by
      rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · omega
    rw [hdrop, List.foldl_cons] at hp
    dsimp only [ternlogBoolGo]
    by_cases hbit : imm.getLsbD (7 - k) = true
    · simp only [hbit, ↓reduceIte] at hp ⊢
      refine ternlogBoolGo_wp imm a b c k (by omega) _ _
        (fun e' q he' hq => ?_) (fun h => by cases h) p hp
      cases he'
      cases acc with
      | none =>
        have hv0 := hnone rfl; subst hv0
        by_cases h1 : (7 - k) / 4 % 2 = 1 <;> by_cases h2 : (7 - k) / 2 % 2 = 1 <;>
          by_cases h3 : (7 - k) % 2 = 1 <;>
          simpa [h1, h2, h3, Emit.wp, Tup.get, OpCode.wp, lift2] using hq
      | some prev =>
        exact hacc prev _ rfl (by
          by_cases h1 : (7 - k) / 4 % 2 = 1 <;> by_cases h2 : (7 - k) / 2 % 2 = 1 <;>
            by_cases h3 : (7 - k) % 2 = 1 <;>
            simpa [h1, h2, h3, Emit.wp, Tup.get, OpCode.wp, lift2] using hq)
    · simp only [hbit] at hp ⊢
      exact ternlogBoolGo_wp imm a b c k (by omega) acc v0 hacc hnone p hp

/-- Single-pass `isLegal + Wf + wp` bundle for `ternlogBoolEmit`. -/
theorem ternlogBoolEmit_bundle (target : LegalTarget) (imm : BitVec 8) :
    LegalEmitSpec target (ternlogBoolEmit imm)
      (fun (a, b, c, ()) p => p (ternaryLogicBool a b c imm)) :=
  (ternlogBoolEmit imm).bundle target
    (by
      unfold ternlogBoolEmit; split
      · rfl
      · split
        · rfl
        · exact ⟨⟨trivial, rfl, rfl, rfl⟩, ⟨trivial, rfl, rfl, rfl⟩, ⟨trivial, rfl, rfl, rfl⟩,
            ternlogBoolGo_isLegal target imm 8 none (fun _ h => by cases h)⟩)
    (fun (a, b, c, ()) p hp => by
      unfold ternlogBoolEmit; split
      · rename_i h0; have := beq_iff_eq.mp h0; subst this
        simpa [Emit.wp, ternaryLogicBool] using hp
      · split
        · rename_i hff; have := beq_iff_eq.mp hff; subst this
          have hall : ∀ x y z : Bool, ternaryLogicBool x y z 0xff#8 = true := by decide
          simpa [Emit.wp, hall] using hp
        · dsimp only [Emit.wp, Tup.get, OpCode.wp, lift1]
          refine ternlogBoolGo_wp imm a b c 8 (Nat.le_refl _) none false
            (fun _ _ h => by cases h) (fun _ => rfl) p ?_
          have hfold : ∀ (va vb vc : Bool) (im : BitVec 8),
              ([0, 1, 2, 3, 4, 5, 6, 7].foldl (fun cur i =>
                if im.getLsbD i then
                  cur || ((if i / 4 % 2 == 1 then va else !va) &&
                          (if i / 2 % 2 == 1 then vb else !vb) &&
                          (if i % 2 == 1 then vc else !vc))
                else cur) false) = ternaryLogicBool va vb vc im := by
            intro va vb vc im; cases va <;> cases vb <;> cases vc <;> simp [ternaryLogicBool]
          rw [show [0, 1, 2, 3, 4, 5, 6, 7].drop 0 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, hfold]
          exact hp)

end LeanQbe.T
