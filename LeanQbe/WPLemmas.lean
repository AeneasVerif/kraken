module

public import LeanQbe.WP
import LeanQbe.OpsLemmas

/-!
# Lemmas about `wp`

The consequence rule by plain structural induction (no `Wf` needed), and the normal forms used to
unfold block bodies in user proofs.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

/-- Consequence rule, for every term (exotic or not), in both postconditions. -/
theorem wp_mono {Γ : Env} {Q Q' : Post} {X X' : XPost}
    (hQ : ∀ vs m, Q vs m → Q' vs m) (hX : ∀ f vs m, X f vs m → X' f vs m) (e : Expr Val Cont) :
    ∀ args acc m, wp Γ Q X e args acc m → wp Γ Q' X' e args acc m := by
  induction e with
  | let_ op k ih =>
    intro args acc m h; simp only [wp] at h ⊢
    exact ⟨h.1, Op.wp_mono (fun v => ih v [] [] m) h.2⟩
  | load c s sg a k ih =>
    intro args acc m h; simp only [wp] at h ⊢
    grind
  | store s v a k ih =>
    intro args acc m h; simp only [wp] at h ⊢
    exact ⟨h.1, h.2.1, ih _ _ _ h.2.2⟩
  | call f as k ih =>
    intro args acc m h; simp only [wp] at h ⊢
    grind
  | jnz c t e iht ihe =>
    intro args acc m h; simp only [wp] at h ⊢
    exact ⟨h.1, fun hc => iht _ _ _ (h.2.1 hc), fun hc => ihe _ _ _ (h.2.2 hc)⟩
  | jump j as => intro args acc m h; simpa only [wp] using h
  | ret vs => intro args acc m h; simp only [wp] at h ⊢; exact ⟨h.1, hQ _ _ h.2⟩
  | exit f as => intro args acc m h; simp only [wp] at h ⊢; exact ⟨h.1, hX _ _ _ h.2⟩
  | hlt => intro args acc m h; simp only [wp] at h
  | param f ih =>
    intro args acc m h
    cases args with
    | nil => simp only [wp] at h
    | cons a as => simp only [wp] at h ⊢; exact ih a _ _ _ h
  | label f ih =>
    intro args acc m h; simp only [wp] at h ⊢
    exact ⟨h.1, fun J => ih J _ _ _ (h.2 J)⟩
  | block b rest ihb ihr =>
    intro args acc m h
    cases acc with
    | nil => simp only [wp, and_false] at h
    | cons J acc' =>
      simp only [wp] at h ⊢
      exact ⟨h.1, fun hJ => ihr _ _ _ (h.2 (fun as m' hb => hJ as m' (ihb _ _ _ hb)))⟩

/-- A contract is monotone in its postconditions. -/
def Spec.Mono (spec : Spec) : Prop :=
  ∀ args m (Q Q' : Post) (X X' : XPost), (∀ vs m, Q vs m → Q' vs m) →
    (∀ f vs m, X f vs m → X' f vs m) → spec args m Q X → spec args m Q' X'

theorem Func.spec_mono (Γ : Env) (f : Func) : (Func.spec Γ f).Mono :=
  fun args m _ _ _ _ hQ hX h => wp_mono hQ hX (f Val Cont) args [] m h

theorem wp_env_mono {Γ Γ' : Env} {Q : Post} {X : XPost}
    (hΓ : ∀ g vs m P E, Γ g vs m P E → Γ' g vs m P E) (e : Expr Val Cont) :
    ∀ args acc m, wp Γ Q X e args acc m → wp Γ' Q X e args acc m := by
  induction e with
  | let_ op k ih =>
    intro args acc m h; simp only [wp] at h ⊢
    exact ⟨h.1, Op.wp_mono (fun v => ih v [] [] m) h.2⟩
  | load c s sg a k ih =>
    intro args acc m h; simp only [wp] at h ⊢
    grind
  | store s v a k ih =>
    intro args acc m h; simp only [wp] at h ⊢
    exact ⟨h.1, h.2.1, ih _ _ _ h.2.2⟩
  | call f as k ih =>
    intro args acc m h; simp only [wp] at h ⊢
    grind
  | jnz c t e iht ihe =>
    intro args acc m h; simp only [wp] at h ⊢
    exact ⟨h.1, fun hc => iht _ _ _ (h.2.1 hc), fun hc => ihe _ _ _ (h.2.2 hc)⟩
  | jump j as => intro args acc m h; simpa only [wp] using h
  | ret vs => intro args acc m h; simpa only [wp] using h
  | exit f as => intro args acc m h; simpa only [wp] using h
  | hlt => intro args acc m h; simp only [wp] at h
  | param f ih =>
    intro args acc m h
    cases args with
    | nil => simp only [wp] at h
    | cons a as => simp only [wp] at h ⊢; exact ih a _ _ _ h
  | label f ih =>
    intro args acc m h; simp only [wp] at h ⊢
    exact ⟨h.1, fun J => ih J _ _ _ (h.2 J)⟩
  | block b rest ihb ihr =>
    intro args acc m h
    cases acc with
    | nil => simp only [wp, and_false] at h
    | cons J acc' =>
      simp only [wp] at h ⊢
      exact ⟨h.1, fun hJ => ihr _ _ _ (h.2 (fun as m' hb => hJ as m' (ihb _ _ _ hb)))⟩

theorem Func.spec_env_mono {Γ Γ' : Env}
    (hΓ : ∀ g vs m P E, Γ g vs m P E → Γ' g vs m P E) {f : Func} {args : List Val}
    {m : Mem 64} {Q : Post} {X : XPost} (h : Func.spec Γ f args m Q X) :
    Func.spec Γ' f args m Q X :=
  wp_env_mono hΓ (f Val Cont) args [] m h

/-- Closure under a block that starts with a parameter: the parameter becomes a bound variable. -/
theorem closed_param {Γ : Env} {Q : Post} {X : XPost} {f : Val → Expr Val Cont} {J : Cont} :
    (∀ as m, wp Γ Q X (.param f) as [] m → J as m) ↔
      ∀ x, ∀ as m, wp Γ Q X (f x) as [] m → J (x :: as) m := by
  constructor
  · intro h x as m hw; exact h (x :: as) m (by simpa only [wp] using hw)
  · intro h as m hw
    cases as with
    | nil => simp only [wp] at hw
    | cons a as' => simp only [wp] at hw; exact h a as' m hw

/-- Normal form used after `closed_param`: a body that is not a `param` consumes no arguments. -/
theorem forall_args_nil {P : List Val → Mem 64 → Prop} {R : Mem 64 → Prop} :
    (∀ as m, (as = [] ∧ R m) → P as m) ↔ ∀ m, R m → P [] m := by
  grind

theorem wp_param_cons {Γ : Env} {Q : Post} {X : XPost} {f : Val → Expr Val Cont} {a : Val}
    {as : List Val} {acc : List Cont} {m : Mem 64} :
    wp Γ Q X (.param f) (a :: as) acc m ↔ wp Γ Q X (f a) as [] m := Iff.rfl

/-- A call to a callee whose contract is monotone can be discharged with the continuation itself. -/
theorem wp_call_of_spec {Γ : Env} {Q : Post} {X : XPost} {f : Sym} {as : List (Arg Val)}
    {k : Expr Val Cont} {acc : List Cont} {m : Mem 64}
    (h : Γ f (as.map Arg.val) m (fun rs m' => wp Γ Q X k rs [] m') X) :
    wp Γ Q X (.call f as k) [] acc m :=
  ⟨rfl, _, _, h, fun _ _ h => h, fun _ _ _ h => h⟩

end LeanQbe
