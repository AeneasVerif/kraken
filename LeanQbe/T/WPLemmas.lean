module

public import LeanQbe.T.WP
public import LeanQbe.T.OpsLemmas

/-!
# Lemmas about `LeanQbe.T.WP`

* `Expr.induct` / `Blocks.induct_get`: one-motive induction principle for `Expr`, quantifying over
  group blocks by position (`Blocks.get`).
* `closed_iff`: positional characterization of `Closed`.
* `wp_mono` (proved via `induction e using Expr.induct`), `Spec.Mono`, `Func.spec_mono`,
  `wp_env_mono`, `Func.spec_env_mono`.
* Loop and join rules (`wp_loop`, `wp_loop1`, `wp_join`), call discharge (`wp_call_of_spec`,
  `wp_call_ret1`), and user operation-spec helpers (`wp_let_op1`/`2`/`3`, `wp_addc`, `wp_subb`,
  `wp_umulw`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## One-motive induction principle on `Expr` -/

section
set_option linter.unusedSectionVars false
variable {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} {motive : Expr V L rs → Prop}
  (let_ : ∀ {ts} (op : Op V ts) (k : Tup V ts → Expr V L rs), (∀ xs, motive (k xs)) →
    motive (.let_ op k))
  (load : ∀ t (a : Arg V i64) (k : V t → Expr V L rs), (∀ v, motive (k v)) →
    motive (.load t a k))
  (store : ∀ {t} (v : Arg V t) (a : Arg V i64) (k : Expr V L rs), motive k →
    motive (.store v a k))
  (call : ∀ (f : Sym) {as bs} (args : Tup (Arg V) as) (k : Tup V bs → Expr V L rs),
    (∀ xs, motive (k xs)) → motive (.call f args k))
  (jnz : ∀ c t e, motive t → motive e → motive (.jnz c t e))
  (jump : ∀ {ts} (j : L ts) (args : Tup (Arg V) ts), motive (.jump j args))
  (ret : ∀ vs, motive (.ret vs))
  (exit : ∀ (f : Sym) {as} (args : Tup (Arg V) as), motive (.exit f args))
  (hlt : motive .hlt)
  (group : ∀ {sig} (bodies : Tup L sig → Blocks V L rs sig) (k : Tup L sig → Expr V L rs),
    (∀ Js {ts} (i : Member ts sig) xs, motive ((bodies Js).get i xs)) → (∀ Js, motive (k Js)) →
    motive (.group bodies k))

include let_ load store call jnz jump ret exit hlt group

mutual
/-- One-motive structural induction on `Expr`, usable with `induction e using Expr.induct`. -/
theorem Expr.induct : (e : Expr V L rs) → motive e
  | .let_ op k => let_ op k fun xs => Expr.induct (k xs)
  | .load t a k => load t a k fun v => Expr.induct (k v)
  | .store v a k => store v a k (Expr.induct k)
  | .call f args k => call f args k fun xs => Expr.induct (k xs)
  | .jnz c t e => jnz c t e (Expr.induct t) (Expr.induct e)
  | .jump j args => jump j args
  | .ret vs => ret vs
  | .exit f args => exit f args
  | .hlt => hlt
  | .group bodies k => group bodies k (fun Js _ i xs => Blocks.induct_get (bodies Js) i xs)
      (fun Js => Expr.induct (k Js))

/-- Mutual helper for `Expr.induct`: induction on a block accessed by position `i`. -/
theorem Blocks.induct_get : {sig : List (List Ty)} → {ts : List Ty} → (bs : Blocks V L rs sig) →
    (i : Member ts sig) → (xs : Tup V ts) → motive (bs.get i xs)
  | _, _, .cons b _, .here, xs => Expr.induct (b xs)
  | _, _, .cons _ bs, .there i, xs => Blocks.induct_get bs i xs
end
end

/-! ## Positional characterization of `Closed` -/

/-- `Closed` holds iff every block in the group implies its corresponding join point by position. -/
theorem closed_iff (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    {sig : List (List Ty)} → (bs : Blocks Val Cont rs sig) → (Js : Tup Cont sig) →
    (Closed Γ Q X bs Js ↔
      ∀ {ts} (i : Member ts sig) xs m, wp Γ Q X (bs.get i xs) m → Js.get i xs m)
  | [], .nil, () => by simp only [Closed, true_iff]; intro _ i; exact nomatch i
  | _ :: _, .cons b bs, Js => by
    simp only [Closed, closed_iff Γ Q X bs Js.2]
    constructor
    · rintro ⟨hb, hbs⟩ _ i xs m h
      cases i with
      | here => exact hb xs m h
      | there i => exact hbs i xs m h
    · intro h
      exact ⟨fun xs m => h .here xs m, fun i xs m => h (.there i) xs m⟩

/-! ## Monotonicity of `wp` and `Func.spec` -/

/-- Consequence rule for `wp`, proved via `induction e using Expr.induct`. -/
theorem wp_mono {Γ : Env} {rs : List Ty} {Q Q' : Post rs} {X X' : XPost}
    (hQ : ∀ vs m, Q vs m → Q' vs m) (hX : ∀ f cs xs m, X f cs xs m → X' f cs xs m)
    (e : Expr Val Cont rs) : ∀ m, wp Γ Q X e m → wp Γ Q' X' e m := by
  induction e using Expr.induct with
  | let_ op k ih =>
    intro m h
    simp only [wp] at h ⊢
    exact Op.wp_mono (fun r => ih r m) h
  | load t a k ih =>
    intro m ⟨v, hv, h⟩
    exact ⟨v, hv, ih v m h⟩
  | store v a k ih =>
    intro m ⟨hok, h⟩
    exact ⟨hok, ih _ h⟩
  | call f args k ih =>
    intro m ⟨P, E, hΓ, hP, hE⟩
    exact ⟨P, E, hΓ, fun r m' hr => ih r m' (hP r m' hr), fun g cs xs m' he => hX g cs xs m' (hE g cs xs m' he)⟩
  | jnz c t e iht ihe =>
    intro m h
    exact ⟨fun hc => iht m (h.1 hc), fun hc => ihe m (h.2 hc)⟩
  | jump j args =>
    intro m h
    exact h
  | ret vs =>
    intro m h
    exact hQ _ m h
  | exit f args =>
    intro m h
    exact hX f _ _ m h
  | hlt =>
    intro m h
    exact h
  | group bodies k ihb ihk =>
    intro m h Js hc
    refine ihk Js m (h Js ?_)
    rw [closed_iff] at hc ⊢
    exact fun i xs m' hb => hc i xs m' (ihb Js i xs m' hb)

/-- A typed function contract is monotone in both postconditions. -/
def Spec.Mono {as bs : List Ty} (spec : Spec as bs) : Prop :=
  ∀ xs m (Q Q' : Post bs) (X X' : XPost),
    (∀ vs m, Q vs m → Q' vs m) →
    (∀ f cs ys m, X f cs ys m → X' f cs ys m) →
    spec xs m Q X → spec xs m Q' X'

theorem Func.spec_mono {as rs : List Ty} (Γ : Env) (f : Func as rs) : (Func.spec Γ f).Mono :=
  fun xs m _ _ _ _ hQ hX h => wp_mono hQ hX (f Val Cont xs) m h

theorem wp_env_mono {Γ Γ' : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hΓ : ∀ g as bs xs m P E, Γ g as bs xs m P E → Γ' g as bs xs m P E)
    (e : Expr Val Cont rs) : ∀ m, wp Γ Q X e m → wp Γ' Q X e m := by
  induction e using Expr.induct with
  | let_ op k ih =>
    intro m h
    simp only [wp] at h ⊢
    exact Op.wp_mono (fun r => ih r m) h
  | load t a k ih =>
    intro m ⟨v, hv, h⟩
    exact ⟨v, hv, ih v m h⟩
  | store v a k ih =>
    intro m ⟨hok, h⟩
    exact ⟨hok, ih _ h⟩
  | call f args k ih =>
    intro m ⟨P, E, hG, hP, hE⟩
    exact ⟨P, E, hΓ f _ _ _ m P E hG, fun r m' hr => ih r m' (hP r m' hr), hE⟩
  | jnz c t e iht ihe =>
    intro m h
    exact ⟨fun hc => iht m (h.1 hc), fun hc => ihe m (h.2 hc)⟩
  | jump j args => intro m h; exact h
  | ret vs => intro m h; exact h
  | exit f args => intro m h; exact h
  | hlt => intro m h; exact h
  | group bodies k ihb ihk =>
    intro m h Js hc
    refine ihk Js m (h Js ?_)
    rw [closed_iff] at hc ⊢
    exact fun i xs m' hb => hc i xs m' (ihb Js i xs m' hb)

theorem Func.spec_env_mono {Γ Γ' : Env} {as rs : List Ty}
    (hΓ : ∀ g cs ds xs m P E, Γ g cs ds xs m P E → Γ' g cs ds xs m P E)
    {f : Func as rs} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ' f xs m Q X :=
  wp_env_mono hΓ (f Val Cont xs) m h

/-! ## Structured loop and join rules -/

/-- A one-block loop proved by strong induction on a `Nat`-indexed invariant. -/
theorem wp_loop {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (body : Cont ts → Tup Val ts → Expr Val Cont rs)
    (entry : Cont ts → Expr Val Cont rs)
    (Inv : Nat → Tup Val ts → Mem 64 → Prop)
    (hbody : ∀ (J : Cont ts) n xs m,
      (∀ n' ys m', n' < n → Inv n' ys m' → J ys m') →
      Inv n xs m → wp Γ Q X (body J xs) m)
    (hentry : ∀ J : Cont ts, (∀ n xs m, Inv n xs m → J xs m) → wp Γ Q X (entry J) m) :
    wp Γ Q X (.group (sig := [ts]) (fun Js => .cons (body Js.1) .nil) (fun Js => entry Js.1)) m := by
  simp only [wp]
  intro Js hc
  simp only [Closed, and_true] at hc
  apply hentry
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih => exact fun xs m hinv => hc xs m (hbody Js.1 n xs m (fun n' ys m' h => ih n' h ys m') hinv)

/-- `wp_loop` specialized to `loop1`. -/
theorem wp_loop1 {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (body : Cont ts → Tup Val ts → Expr Val Cont rs)
    (entry : Cont ts → Expr Val Cont rs)
    (Inv : Nat → Tup Val ts → Mem 64 → Prop)
    (hbody : ∀ (J : Cont ts) n xs m,
      (∀ n' ys m', n' < n → Inv n' ys m' → J ys m') →
      Inv n xs m → wp Γ Q X (body J xs) m)
    (hentry : ∀ J : Cont ts, (∀ n xs m, Inv n xs m → J xs m) → wp Γ Q X (entry J) m) :
    wp Γ Q X (loop1 body entry) m :=
  wp_loop body entry Inv hbody hentry

/-- A forward (non-recursive) join point in a one-block group. -/
theorem wp_join {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (body : Tup Val ts → Expr Val Cont rs) (entry : Cont ts → Expr Val Cont rs)
    (P : Tup Val ts → Mem 64 → Prop)
    (hbody : ∀ xs m, P xs m → wp Γ Q X (body xs) m)
    (hentry : ∀ J : Cont ts, (∀ xs m, P xs m → J xs m) → wp Γ Q X (entry J) m) :
    wp Γ Q X (.group (sig := [ts]) (fun _ => .cons body .nil) (fun Js => entry Js.1)) m :=
  wp_loop (fun _ => body) entry (fun _ => P) (fun _ _ xs m _ h => hbody xs m h)
    fun J hJ => hentry J (hJ 0)

/-! ## Call and operation simplification rules -/

section
variable {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}

theorem wp_let {ts : List Ty} (op : Op Val ts) (k : Tup Val ts → Expr Val Cont rs) :
    wp Γ Q X (.let_ op k) m = op.wp (fun r => wp Γ Q X (k r) m) := by
  simp [wp]

@[simp] theorem wp_let_op1 {t ts} (c : OpCode [t] ts) (a : Arg Val t)
    (k : Tup Val ts → Expr Val Cont rs) :
    wp Γ Q X (.let_ (op1 c a) k) m = c.wp (a.val, ()) (fun r => wp Γ Q X (k r) m) := by
  simp [wp, Op.wp, op1, vals]

@[simp] theorem wp_let_op2 {t u ts} (c : OpCode [t, u] ts) (a : Arg Val t) (b : Arg Val u)
    (k : Tup Val ts → Expr Val Cont rs) :
    wp Γ Q X (.let_ (op2 c a b) k) m =
      c.wp (a.val, b.val, ()) (fun r => wp Γ Q X (k r) m) := by
  simp [wp, Op.wp, op2, vals]

@[simp] theorem wp_let_op3 {t u w ts} (c : OpCode [t, u, w] ts) (a : Arg Val t) (b : Arg Val u)
    (d : Arg Val w) (k : Tup Val ts → Expr Val Cont rs) :
    wp Γ Q X (.let_ (op3 c a b d) k) m =
      c.wp (a.val, b.val, d.val, ()) (fun r => wp Γ Q X (k r) m) := by
  simp [wp, Op.wp, op3, vals]

@[simp] theorem wp_jnz (c : Arg Val .bool) (t e : Expr Val Cont rs) :
    wp Γ Q X (.jnz c t e) m =
      ((c.val = true → wp Γ Q X t m) ∧ (c.val = false → wp Γ Q X e m)) := by
  simp [wp]

@[simp] theorem wp_jump {ts} (j : Cont ts) (args : Tup (Arg Val) ts) :
    wp Γ Q X (.jump j args) m = j (vals args) m := by
  simp [wp]

@[simp] theorem wp_ret (vs : Tup (Arg Val) rs) :
    wp Γ Q X (.ret vs) m = Q (vals vs) m := by
  simp [wp]

@[simp] theorem wp_exit (f : Sym) {as : List Ty} (args : Tup (Arg Val) as) :
    wp Γ Q X (.exit f args) m = X f as (vals args) m := by
  simp [wp]

theorem wp_load (t : Ty) (a : Arg Val i64) (k : Val t → Expr Val Cont rs) :
    wp Γ Q X (.load t a k) m = (∃ v, loadVal m t a.val = some v ∧ wp Γ Q X (k v) m) := by
  simp [wp]

theorem wp_store {t : Ty} (v : Arg Val t) (a : Arg Val i64) (k : Expr Val Cont rs) :
    wp Γ Q X (.store v a k) m = (storeOk m t a.val ∧ wp Γ Q X k (storeMem m t a.val v.val)) := by
  simp [wp]

theorem wp_call_of_spec {f : Sym} {as bs : List Ty} (args : Tup (Arg Val) as)
    (k : Tup Val bs → Expr Val Cont rs)
    (h : Γ f as bs (vals args) m (fun r m' => wp Γ Q X (k r) m') X) :
    wp Γ Q X (.call f args k) m :=
  ⟨_, _, h, fun _ _ hr => hr, fun _ _ _ _ hx => hx⟩

theorem wp_call_ret1 {f : Sym} {as : List Ty} {b : Ty} (args : Tup (Arg Val) as)
    (k : Tup Val [b] → Expr Val Cont rs) (Pred : Val b → Mem 64 → Prop)
    (hcall : Γ f as [b] (vals args) m (fun (r, ()) m' => Pred r m') (fun _ _ _ _ => False))
    (hk : ∀ r m', Pred r m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call f args k) m :=
  ⟨_, _, hcall, fun (r, ()) m' hr => hk r m' hr, fun _ _ _ _ hx => hx.elim⟩

/-! ## Named-result operation rules for `addc`, `subb`, `umulw` -/

theorem wp_addc {n : Nat} (a b : Arg Val (.bits n)) (c : Arg Val .bool)
    (k : Tup Val [.bits n, .bool] → Expr Val Cont rs)
    (h : ∀ (s : BitVec n) (co : Bool),
      co.toNat * 2 ^ n + s.toNat = a.val.toNat + b.val.toNat + c.val.toNat →
      wp Γ Q X (k (s, co, ())) m) :
    wp Γ Q X (.let_ (op3 (.addc n) a b c) k) m := by
  rw [wp_let_op3]
  exact h _ _ (addc_toNat _ _ _)

theorem wp_subb {n : Nat} (a b : Arg Val (.bits n)) (c : Arg Val .bool)
    (k : Tup Val [.bits n, .bool] → Expr Val Cont rs)
    (h : ∀ (d : BitVec n) (bo : Bool),
      d.toNat + b.val.toNat + c.val.toNat = a.val.toNat + bo.toNat * 2 ^ n →
      wp Γ Q X (k (d, bo, ())) m) :
    wp Γ Q X (.let_ (op3 (.subb n) a b c) k) m := by
  rw [wp_let_op3]
  exact h _ _ (subb_toNat _ _ _)

theorem wp_umulw {n : Nat} (a b : Arg Val (.bits n))
    (k : Tup Val [.bits n, .bits n] → Expr Val Cont rs)
    (h : ∀ lo hi : BitVec n, hi.toNat * 2 ^ n + lo.toNat = a.val.toNat * b.val.toNat →
      wp Γ Q X (k (lo, hi, ())) m) :
    wp Γ Q X (.let_ (op2 (.umulw n) a b) k) m := by
  rw [wp_let_op2]
  refine h _ _ ?_
  have := (umulw_toNat a.val b.val).1
  rw [Nat.mul_comm] at this
  omega

end

end LeanQbe.T
