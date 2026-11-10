module

/-
Candidate encoding E1 ("uniform"): ONE non-mutual, non-indexed inductive type.
  * `V L : Type` (single-sorted values, untyped label arity; arity mismatch means `False`).
  * every bound name is one λ: `let_` binds a value, `param` binds a block/function parameter,
    `label` declares a join point.
  * a group of mutually recursive join points is `label* block*`:
      label fun even => label fun odd => block bEven (block bOdd entry)
    the i-th `block` defines the i-th pending label.
  * a block (and a function) is an `Expr` that starts with `param`s.
Checks: (a) Lean accepts structural `wp` with two accumulators (pending args, pending labels);
        (b) consequence rule by plain `induction`;
        (c) unfolding ergonomics on even/odd;
        (d) Chlipala-style `Wf` as one plain inductive predicate, provable by a dumb tactic;
        (e) first-order mirror, `toFlat`, `denote`, and `rfl` reification.
-/
set_option autoImplicit false

@[expose] public section

namespace E1

abbrev Val := BitVec 64
abbrev Mem := BitVec 64 → Option (BitVec 64)

inductive Op (V : Type) : Type
  | const (c : Val)
  | add (a b : V)
  | sub (a b : V)
  | ult (a b : V)
  | udiv (a b : V)
  | load (a : V)

inductive Expr (V L : Type) : Type
  | let_ (op : Op V) (k : V → Expr V L)
  | store (a v : V) (k : Expr V L)
  | jnz (c : V) (t e : Expr V L)
  | jump (j : L) (args : List V)
  | ret (vs : List V)
  | hlt
  | param (f : V → Expr V L)
  | label (f : L → Expr V L)
  | block (b rest : Expr V L)

def Op.wp : Op Val → Mem → (Val → Mem → Prop) → Prop
  | .const c, m, post => post c m
  | .add a b, m, post => post (a + b) m
  | .sub a b, m, post => post (a - b) m
  | .ult a b, m, post => post (if a < b then 1 else 0) m
  | .udiv a b, m, post => b ≠ 0 ∧ post (a / b) m
  | .load a, m, post => ∃ v, m a = some v ∧ post v m

theorem Op.wp_mono {op : Op Val} {m : Mem} {p q : Val → Mem → Prop}
    (h : ∀ v m, p v m → q v m) : op.wp m p → op.wp m q := by
  cases op with
  | const c => exact h _ _
  | add a b => exact h _ _
  | sub a b => exact h _ _
  | ult a b => exact h _ _
  | udiv a b => exact fun ⟨h1, h2⟩ => ⟨h1, h _ _ h2⟩
  | load a => exact fun ⟨v, h1, h2⟩ => ⟨v, h1, h _ _ h2⟩

abbrev Cont := List Val → Mem → Prop
abbrev Post := List Val → Mem → Prop

/-- `wp Q e args acc m`: `args` are the arguments still to be consumed by `param`s,
`acc` the labels declared by `label` and not yet defined by `block` (oldest first). -/
def wp (Q : Post) : Expr Val Cont → List Val → List Cont → Mem → Prop
  | .let_ op k, args, _, m => args = [] ∧ op.wp m (fun v m' => wp Q (k v) [] [] m')
  | .store a v k, args, _, m =>
      args = [] ∧ (m a).isSome ∧ wp Q k [] [] (fun a' => if a' = a then some v else m a')
  | .jnz c t e, args, _, m => args = [] ∧ (c ≠ 0 → wp Q t [] [] m) ∧ (c = 0 → wp Q e [] [] m)
  | .jump j as, args, _, m => args = [] ∧ j as m
  | .ret vs, args, _, m => args = [] ∧ Q vs m
  | .hlt, _, _, _ => False
  | .param _, [], _, _ => False
  | .param f, a :: as, _, m => wp Q (f a) as [] m
  | .label f, args, acc, m => args = [] ∧ ∀ J : Cont, wp Q (f J) [] (acc ++ [J]) m
  | .block b rest, args, acc, m =>
      args = [] ∧
      match acc with
      | [] => False
      | J :: acc' => (∀ as m', wp Q b as [] m' → J as m') → wp Q rest [] acc' m

/-- Consequence rule for every term, exotic or not; plain structural induction. -/
theorem wp_mono {Q Q' : Post} (hQ : ∀ v m, Q v m → Q' v m) (e : Expr Val Cont) :
    ∀ args acc m, wp Q e args acc m → wp Q' e args acc m := by
  induction e with
  | let_ op k ih =>
    intro args acc m h; simp only [wp] at h ⊢
    exact ⟨h.1, Op.wp_mono (fun v m' => ih v [] [] m') h.2⟩
  | store a v k ih =>
    intro args acc m h; simp only [wp] at h ⊢
    exact ⟨h.1, h.2.1, ih _ _ _ h.2.2⟩
  | jnz c t e iht ihe =>
    intro args acc m h; simp only [wp] at h ⊢
    exact ⟨h.1, fun hc => iht _ _ _ (h.2.1 hc), fun hc => ihe _ _ _ (h.2.2 hc)⟩
  | jump j as => intro args acc m h; simpa only [wp] using h
  | ret vs => intro args acc m h; simp only [wp] at h ⊢; exact ⟨h.1, hQ _ _ h.2⟩
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

/-- Closure under a block that starts with a parameter: the parameter becomes a bound variable. -/
theorem closed_param {Q : Post} {f : Val → Expr Val Cont} {J : Cont} :
    (∀ as m, wp Q (.param f) as [] m → J as m) ↔
      ∀ x, ∀ as m, wp Q (f x) as [] m → J (x :: as) m := by
  constructor
  · intro h x as m hw; exact h (x :: as) m (by simpa only [wp] using hw)
  · intro h as m hw
    cases as with
    | nil => simp only [wp] at hw
    | cons a as' => simp only [wp] at hw; exact h a as' m hw

/-! ## even/odd by mutual recursion between two join points -/

def evenOdd (V L : Type) : Expr V L :=
  .param fun n =>
  .let_ (.const 0) fun zero =>
  .let_ (.const 1) fun one =>
  .label fun even => .label fun odd =>
  .block (.param fun x =>
      .let_ (.ult zero x) fun c =>
      .jnz c (.let_ (.sub x one) fun x' => .jump odd [x']) (.ret [one])) <|
  .block (.param fun x =>
      .let_ (.ult zero x) fun c =>
      .jnz c (.let_ (.sub x one) fun x' => .jump even [x']) (.ret [zero])) <|
  .jump even [n]

def parity (k : Nat) : Val := if k % 2 = 0 then 1 else 0

/-- Normal form used below: a body that is not a `param` consumes no arguments. -/
theorem forall_args_nil {P : List Val → Mem → Prop} {R : Mem → Prop} :
    (∀ as m, (as = [] ∧ R m) → P as m) ↔ ∀ m, R m → P [] m := by
  constructor
  · intro h m hr; exact h [] m ⟨rfl, hr⟩
  · intro h as m ⟨has, hr⟩; subst has; exact h m hr

theorem evenOdd_correct (n : Val) (m : Mem) :
    wp (fun r m' => r = [parity n.toNat] ∧ m' = m) (evenOdd Val Cont) [n] [] m := by
  simp only [evenOdd, wp, Op.wp, closed_param, forall_args_nil, List.nil_append,
    List.cons_append, true_and]
  intro even odd hEven hOdd
  suffices h : ∀ k : Nat, k < 2 ^ 64 →
      (n.toNat % 2 = k % 2 → even [BitVec.ofNat 64 k] m) ∧
      (n.toNat % 2 ≠ k % 2 → odd [BitVec.ofNat 64 k] m) by
    have := (h n.toNat (by omega)).1 rfl
    simpa using this
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun hk => hEven _ _ ?_, fun hk => hOdd _ _ ?_⟩
    · have : n.toNat % 2 = 0 := by omega
      simp [parity, this]
    · have : ¬ n.toNat % 2 = 0 := by omega
      simp [parity, this]
  | succ k ih =>
    intro hk
    have ih := ih (by omega)
    have hsub : BitVec.ofNat 64 (k + 1) - (1 : Val) = BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hpos : (if (0 : Val) < BitVec.ofNat 64 (k + 1) then (1 : Val) else 0) = 1 := by
      have : (0 : Val) < BitVec.ofNat 64 (k + 1) := by
        simp [BitVec.lt_def, BitVec.toNat_ofNat]; omega
      split
      · rfl
      · contradiction
    refine ⟨fun h => hEven _ _ ?_, fun h => hOdd _ _ ?_⟩
    · rw [hpos, hsub]
      exact ⟨fun _ => ih.2 (by omega), fun h0 => absurd h0 (by decide)⟩
    · rw [hpos, hsub]
      exact ⟨fun _ => ih.1 (by omega), fun h0 => absurd h0 (by decide)⟩

/-! ## Chlipala-style well-formedness: one plain inductive predicate -/

inductive OpRel {V₁ V₂ : Type} (R : V₁ → V₂ → Prop) : Op V₁ → Op V₂ → Prop
  | const (c : Val) : OpRel R (.const c) (.const c)
  | add {a₁ b₁ a₂ b₂} : R a₁ a₂ → R b₁ b₂ → OpRel R (.add a₁ b₁) (.add a₂ b₂)
  | sub {a₁ b₁ a₂ b₂} : R a₁ a₂ → R b₁ b₂ → OpRel R (.sub a₁ b₁) (.sub a₂ b₂)
  | ult {a₁ b₁ a₂ b₂} : R a₁ a₂ → R b₁ b₂ → OpRel R (.ult a₁ b₁) (.ult a₂ b₂)
  | udiv {a₁ b₁ a₂ b₂} : R a₁ a₂ → R b₁ b₂ → OpRel R (.udiv a₁ b₁) (.udiv a₂ b₂)
  | load {a₁ a₂} : R a₁ a₂ → OpRel R (.load a₁) (.load a₂)

inductive Forall₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall₂ R [] []
  | cons {a b as bs} : R a b → Forall₂ R as bs → Forall₂ R (a :: as) (b :: bs)

inductive Wf {V₁ V₂ L₁ L₂ : Type} :
    List (V₁ × V₂) → List (L₁ × L₂) → Expr V₁ L₁ → Expr V₂ L₂ → Prop
  | let_ {G D op₁ op₂ k₁ k₂} : OpRel (fun a b => (a, b) ∈ G) op₁ op₂ →
      (∀ v₁ v₂, Wf ((v₁, v₂) :: G) D (k₁ v₁) (k₂ v₂)) → Wf G D (.let_ op₁ k₁) (.let_ op₂ k₂)
  | store {G D a₁ a₂ v₁ v₂ k₁ k₂} : (a₁, a₂) ∈ G → (v₁, v₂) ∈ G → Wf G D k₁ k₂ →
      Wf G D (.store a₁ v₁ k₁) (.store a₂ v₂ k₂)
  | jnz {G D c₁ c₂ t₁ t₂ e₁ e₂} : (c₁, c₂) ∈ G → Wf G D t₁ t₂ → Wf G D e₁ e₂ →
      Wf G D (.jnz c₁ t₁ e₁) (.jnz c₂ t₂ e₂)
  | jump {G D j₁ j₂ as₁ as₂} : (j₁, j₂) ∈ D → Forall₂ (fun a b => (a, b) ∈ G) as₁ as₂ →
      Wf G D (.jump j₁ as₁) (.jump j₂ as₂)
  | ret {G D vs₁ vs₂} : Forall₂ (fun a b => (a, b) ∈ G) vs₁ vs₂ →
      Wf G D (.ret vs₁) (.ret vs₂)
  | hlt {G D} : Wf G D .hlt .hlt
  | param {G D f₁ f₂} : (∀ v₁ v₂, Wf ((v₁, v₂) :: G) D (f₁ v₁) (f₂ v₂)) →
      Wf G D (.param f₁) (.param f₂)
  | label {G D f₁ f₂} : (∀ j₁ j₂, Wf G ((j₁, j₂) :: D) (f₁ j₁) (f₂ j₂)) →
      Wf G D (.label f₁) (.label f₂)
  | block {G D b₁ b₂ r₁ r₂} : Wf G D b₁ b₂ → Wf G D r₁ r₂ →
      Wf G D (.block b₁ r₁) (.block b₂ r₂)

/-- A dumb tactic proves it for a concrete program. -/
theorem evenOdd_wf (V₁ V₂ L₁ L₂ : Type) :
    Wf ([] : List (V₁ × V₂)) ([] : List (L₁ × L₂)) (evenOdd V₁ L₁) (evenOdd V₂ L₂) := by
  unfold evenOdd
  repeat (first | intro _ _ | constructor!)

/-! ## First-order mirror, `toFlat`, `denote`, `rfl` reification -/

inductive Flat : Type
  | let_ (op : Op Nat) (k : Flat)
  | store (a v : Nat) (k : Flat)
  | jnz (c : Nat) (t e : Flat)
  | jump (j : Nat) (args : List Nat)
  | ret (vs : List Nat)
  | hlt
  | param (k : Flat)
  | label (k : Flat)
  | block (b rest : Flat)

/-- Names are de Bruijn levels: `nv` / `nl` = number of variables / labels in scope. -/
def toFlat : Expr Nat Nat → Nat → Nat → Flat
  | .let_ op k, nv, nl => .let_ op (toFlat (k nv) (nv + 1) nl)
  | .store a v k, nv, nl => .store a v (toFlat k nv nl)
  | .jnz c t e, nv, nl => .jnz c (toFlat t nv nl) (toFlat e nv nl)
  | .jump j as, _, _ => .jump j as
  | .ret vs, _, _ => .ret vs
  | .hlt, _, _ => .hlt
  | .param f, nv, nl => .param (toFlat (f nv) (nv + 1) nl)
  | .label f, nv, nl => .label (toFlat (f nl) nv (nl + 1))
  | .block b r, nv, nl => .block (toFlat b nv nl) (toFlat r nv nl)

/-- `ctx` has the newest binder first; `n` is its length (kept as a closed literal). -/
def lookup {α : Type} (ctx : List α) (n i : Nat) : Option α :=
  if i < n then ctx[n - 1 - i]? else none

def lookups {α : Type} (ctx : List α) (n : Nat) : List Nat → Option (List α)
  | [] => some []
  | i :: is =>
    match lookup ctx n i, lookups ctx n is with
    | some v, some vs => some (v :: vs)
    | _, _ => none

def denoteOp {V : Type} (ctx : List V) (n : Nat) : Op Nat → Option (Op V)
  | .const c => some (.const c)
  | .add a b => match lookup ctx n a, lookup ctx n b with
    | some a, some b => some (.add a b) | _, _ => none
  | .sub a b => match lookup ctx n a, lookup ctx n b with
    | some a, some b => some (.sub a b) | _, _ => none
  | .ult a b => match lookup ctx n a, lookup ctx n b with
    | some a, some b => some (.ult a b) | _, _ => none
  | .udiv a b => match lookup ctx n a, lookup ctx n b with
    | some a, some b => some (.udiv a b) | _, _ => none
  | .load a => match lookup ctx n a with
    | some a => some (.load a) | _ => none

def denote (V L : Type) : Flat → Nat → List V → Nat → List L → Expr V L
  | .let_ op k, nv, vs, nl, ls =>
    match denoteOp vs nv op with
    | some op => .let_ op fun v => denote V L k (nv + 1) (v :: vs) nl ls
    | none => .hlt
  | .store a v k, nv, vs, nl, ls =>
    match lookup vs nv a, lookup vs nv v with
    | some a, some v => .store a v (denote V L k nv vs nl ls)
    | _, _ => .hlt
  | .jnz c t e, nv, vs, nl, ls =>
    match lookup vs nv c with
    | some c => .jnz c (denote V L t nv vs nl ls) (denote V L e nv vs nl ls)
    | none => .hlt
  | .jump j as, nv, vs, nl, ls =>
    match lookup ls nl j, lookups vs nv as with
    | some j, some as => .jump j as
    | _, _ => .hlt
  | .ret rs, nv, vs, _, _ =>
    match lookups vs nv rs with
    | some rs => .ret rs
    | none => .hlt
  | .hlt, _, _, _, _ => .hlt
  | .param k, nv, vs, nl, ls => .param fun v => denote V L k (nv + 1) (v :: vs) nl ls
  | .label k, nv, vs, nl, ls => .label fun j => denote V L k nv vs (nl + 1) (j :: ls)
  | .block b r, nv, vs, nl, ls => .block (denote V L b nv vs nl ls) (denote V L r nv vs nl ls)

def evenOddFlat : Flat := toFlat (evenOdd Nat Nat) 0 0

/-- Reification is validated by the kernel: the PHOAS term IS the denotation of its
first-order image, definitionally. -/
theorem evenOdd_reified : evenOdd = fun V L => denote V L evenOddFlat 0 [] 0 [] := by
  rfl

/-- Generic: every denotation is well-formed (statement only; the proof is plan work). -/
def WfDenoteStatement : Prop :=
  ∀ (flat : Flat) (V₁ V₂ L₁ L₂ : Type) (vs₁ : List V₁) (vs₂ : List V₂) (ls₁ : List L₁) (ls₂ : List L₂),
    vs₁.length = vs₂.length → ls₁.length = ls₂.length →
    Wf (vs₁.zip vs₂) (ls₁.zip ls₂) (denote V₁ L₁ flat vs₁.length vs₁ ls₁.length ls₁)
      (denote V₂ L₂ flat vs₂.length vs₂ ls₂.length ls₂)

#print axioms wp_mono
#print axioms evenOdd_correct
#print axioms evenOdd_wf
#print axioms evenOdd_reified

end E1
