module

public import LeanQbe.T.WP
public import LeanQbe.T.Flat
public import LeanQbe.T.Trie

/-!
# Shared mid-end pass utilities

Common `Arg` / `Tup` / `Ctx` / `Trie` combinators (`Arg.imm?`, `tupMapArg`, `tupImms?`,
`tupFreshWith`, `FKey`/`valBeq`/`fKeyBeq`, `flattenArg`/`flattenArgs`/`flattenOp`/`toArgTup`,
`OptV`/`KL0`/`someTup`/`noneTup`/`dummyArgOptTup`/`argSweep`/`argsSweep`,
`trieUnion`/`addArgKey`/`addArgKeys`/`anyLive`), relational transport lemmas, and generic
`liftFloatRel{1,2,3}_pred` preservation lemmas shared across mid-end optimization passes.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

attribute [local instance] Val.inhabited

/-! ## Shared `Arg` and `Tup` combinators -/

/-- Extract the immediate value of an operand, if any. -/
def Arg.imm? {V : Ty → Type} {t : Ty} : Arg V t → Option (Val t)
  | .var _ => none
  | .imm c => some c

/-- Map a polymorphic operand transformation across an operand tuple. -/
def tupMapArg {V W : Ty → Type} (f : ∀ t, Arg V t → Arg W t) :
    {ts : List Ty} → Tup (Arg V) ts → Tup (Arg W) ts
  | [], () => ()
  | _ :: _, (a, as) => (f _ a, tupMapArg f as)

/-- Extract a tuple of immediate values when every operand in the tuple is `.imm`. -/
def tupImms? {V : Ty → Type} : {ts : List Ty} → Tup (Arg V) ts → Option (Tup Val ts)
  | [], () => some ()
  | _ :: _, (a, as) => do
    let c ← a.imm?
    let cs ← tupImms? as
    pure (c, cs)

/-- Wrap bound variables `xs : Tup V ts` using `mk x idx` starting at `next`. -/
def tupFreshWith {V W : Ty → Type} (mk : ∀ {t : Ty}, V t → Nat → W t) :
    (ts : List Ty) → Tup V ts → Nat → Tup W ts
  | [], (), _ => ()
  | _ :: ts, (x, xs), next => (mk x next, tupFreshWith mk ts xs (next + 1))

/-! ## Symbolic value keys and kernel-reducible equality -/

/-- Symbolic variable/immediate key for detecting equal operands independently of `V`. -/
abbrev FKey (t : Ty) := Arg K t

/-- Kernel-reducible boolean equality on `Val t`. -/
def valBeq : (t : Ty) → Val t → Val t → Bool
  | .bool, a, b => a == b
  | .bits _, a, b => a == b
  | .float _, a, b => a == b
  | .pair s u, (a₁, a₂), (b₁, b₂) => valBeq s a₁ b₁ && valBeq u a₂ b₂

/-- Kernel-reducible boolean equality on `FKey t`. -/
def fKeyBeq {t : Ty} : FKey t → FKey t → Bool
  | .var i, .var j => i == j
  | .imm a, .imm b => valBeq t a b
  | _, _ => false

/-! ## Two-level operand flattening and `Option`-tagged binder helpers -/

/-- Flatten a two-level operand `Arg (Arg V) t` into `Arg V t`. -/
def flattenArg {V : Ty → Type} {t : Ty} : Arg (Arg V) t → Arg V t
  | .var a => a
  | .imm c => .imm c

/-- Flatten a tuple of two-level operands into `Tup (Arg V) ts`. -/
abbrev flattenArgs {V : Ty → Type} {ts : List Ty} :
    Tup (Arg (Arg V)) ts → Tup (Arg V) ts :=
  tupMapArg fun _ => flattenArg

/-- Flatten operands of an `Op (Arg V) rs` into `Op V rs`. -/
def flattenOp {V : Ty → Type} {rs : List Ty} (op : Op (Arg V) rs) : Op V rs :=
  ⟨op.code, flattenArgs op.args⟩

/-- Lift a variable tuple `Tup V ts` into `Tup (Arg V) ts`. -/
def toArgTup {V : Ty → Type} : {ts : List Ty} → Tup V ts → Tup (Arg V) ts
  | [], () => ()
  | _ :: _, (x, xs) => (.var x, toArgTup xs)

/-- Optional variable representation (`none` for dropped or static-probe binders). -/
abbrev OptV (V : Ty → Type) (t : Ty) : Type := Option (V t)

/-- Type-erased label representation used during bottom-up analysis passes. -/
abbrev KL0 : List Ty → Type := fun _ => Unit

/-- Wrap every variable in `Tup V ts` as `some`. -/
def someTup {V : Ty → Type} : (ts : List Ty) → Tup V ts → Tup (OptV V) ts
  | [], () => ()
  | _ :: ts, (x, xs) => (some x, someTup ts xs)

/-- Build a tuple of `none` variables matching `ts`. -/
def noneTup {V : Ty → Type} : (ts : List Ty) → Tup (OptV V) ts
  | [] => ()
  | _ :: ts => (none, noneTup ts)

/-- Build dummy `Arg.var none` operands matching `ts` for static probing. -/
def dummyArgOptTup {V : Ty → Type} (ts : List Ty) : Tup (Arg (OptV V)) ts :=
  toArgTup (noneTup ts)

/-- Replace dropped (`none`) variables with `default` immediate values. -/
def argSweep {V : Ty → Type} {t : Ty} : Arg (OptV V) t → Arg V t
  | .var (some v) => .var v
  | .var none => .imm default
  | .imm c => .imm c

/-- Map `argSweep` across an operand tuple. -/
abbrev argsSweep {V : Ty → Type} {ts : List Ty} :
    Tup (Arg (OptV V)) ts → Tup (Arg V) ts :=
  tupMapArg fun _ => argSweep

/-! ## Shared `Trie Unit` liveness helpers -/

/-- Structural union of two `Trie Unit` liveness sets (`rfl`-safe). -/
def trieUnion : Trie Unit → Trie Unit → Trie Unit
  | .empty, t => t
  | t, .empty => t
  | .node (some ()) e₁ o₁, .node _ e₂ o₂ =>
    .node (some ()) (trieUnion e₁ e₂) (trieUnion o₁ o₂)
  | .node none e₁ o₁, .node v₂ e₂ o₂ =>
    .node v₂ (trieUnion e₁ e₂) (trieUnion o₁ o₂)

/-- Record a variable operand key in a `Trie Unit` liveness set. -/
def addArgKey {t : Ty} : Arg K t → Trie Unit → Trie Unit
  | .var i, s => s.insert i ()
  | .imm _, s => s

/-- Record all variable operand keys of a tuple in a `Trie Unit` liveness set. -/
def addArgKeys : {ts : List Ty} → Tup (Arg K) ts → Trie Unit → Trie Unit
  | [], (), s => s
  | _ :: _, (a, as), s => addArgKey a (addArgKeys as s)

/-- Return `true` iff any de Bruijn level in `[b, b + k)` is present in `s`. -/
def anyLive (b : Nat) : Nat → Trie Unit → Bool
  | 0, _ => false
  | k + 1, s => (s.find? b).isSome || anyLive (b + 1) k s

/-! ## Shared CFG reachability fixpoint helpers -/

/-- Insert all elements of `xs` not already in `acc`, returning `(acc', changed)`. -/
def unionNatsChanged (acc : List Nat) : List Nat → List Nat × Bool
  | [] => (acc, false)
  | x :: xs =>
    if acc.contains x then unionNatsChanged acc xs
    else
      let (acc', _) := unionNatsChanged (x :: acc) xs
      (acc', true)

/-- One forward reachability step over adjacency list `adj`, expanding `reach` with successors of
reached nodes. -/
def forwardReachStep (adj : List (Nat × List Nat)) (reach : List Nat) : List Nat × Bool :=
  adj.foldl (fun (acc, ch) (id, succs) =>
    if reach.contains id then
      let (acc', ch') := unionNatsChanged acc succs
      (acc', ch || ch')
    else (acc, ch)) (reach, false)

/-- One backward reachability step over adjacency list `adj`, adding nodes with a successor in
`reach`. -/
def backReachStep (adj : List (Nat × List Nat)) (reach : List Nat) : List Nat × Bool :=
  adj.foldl (fun (acc, ch) (id, succs) =>
    if !acc.contains id && succs.any (fun s => acc.contains s) then
      (id :: acc, true)
    else (acc, ch)) (reach, false)

/-- Bounded fixpoint reachability closure over adjacency list `adj` using step function `step`. -/
def reachFixpoint (step : List (Nat × List Nat) → List Nat → List Nat × Bool)
    (adj : List (Nat × List Nat)) : Nat → List Nat → List Nat
  | 0, reach => reach
  | fuel + 1, reach =>
    let (reach', changed) := step adj reach
    if changed then reachFixpoint step adj fuel reach' else reach

/-! ## Shared `Tup` / `TRel` / `Ctx` transport lemmas -/

theorem tupImms?_vals :
    {ts : List Ty} → {as : Tup (Arg Val) ts} → {cs : Tup Val ts} →
    tupImms? as = some cs → vals as = cs
  | [], (), (), _ => rfl
  | _ :: _, (a, as), (_, _), h => by
    simp only [tupImms?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨c', hc', _, hcs', rfl, rfl⟩
    have ha : a.val = c' := by cases a <;> simp_all [Arg.imm?, Arg.val]
    exact Prod.ext ha (tupImms?_vals hcs')

theorem TRel.get {α : Type _} {f g : α → Type _} {R : ∀ a, f a → g a → Prop} :
    {as : List α} → {xs : Tup f as} → {ys : Tup g as} → {a : α} → (i : Member a as) →
    TRel R xs ys → R a (xs.get i) (ys.get i)
  | _ :: _, (_, _), (_, _), _, .here, .cons h _ => h
  | _ :: _, (_, _), (_, _), _, .there i, .cons _ hs => TRel.get i hs

theorem TRel.tupImms?_eq {V₁ V₂ : Ty → Type} {R : ∀ t, Arg V₁ t → Arg V₂ t → Prop}
    (himm : ∀ {t a₁ a₂}, R t a₁ a₂ → a₁.imm? = a₂.imm?) :
    ∀ {ts : List Ty} {as₁ : Tup (Arg V₁) ts} {as₂ : Tup (Arg V₂) ts},
      TRel R as₁ as₂ → tupImms? as₁ = tupImms? as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons h hs => by
    simp only [tupImms?, himm h, TRel.tupImms?_eq himm hs]

theorem TRel.tupMapArg_vals {V : Ty → Type} {R : ∀ t, Arg V t → Arg Val t → Prop}
    (f : ∀ t, Arg V t → Arg Val t)
    (hf : ∀ {t} {a₁ : Arg V t} {a₂ : Arg Val t}, R t a₁ a₂ → (f t a₁).val = a₂.val) :
    {ts : List Ty} → {as₁ : Tup (Arg V) ts} → {as₂ : Tup (Arg Val) ts} →
    TRel R as₁ as₂ → vals (tupMapArg f as₁) = vals as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons h hs => Prod.ext (hf h) (TRel.tupMapArg_vals f hf hs)

theorem TRel.tupMapArg_rel {V₁ V₂ W₁ W₂ : Ty → Type}
    {R₁ : ∀ t, Arg V₁ t → Arg V₂ t → Prop} {R₂ : ∀ t, Arg W₁ t → Arg W₂ t → Prop}
    (f₁ : ∀ t, Arg V₁ t → Arg W₁ t) (f₂ : ∀ t, Arg V₂ t → Arg W₂ t)
    (hf : ∀ {t} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t},
      R₁ t a₁ a₂ → R₂ t (f₁ t a₁) (f₂ t a₂)) :
    {ts : List Ty} → {as₁ : Tup (Arg V₁) ts} → {as₂ : Tup (Arg V₂) ts} →
    TRel R₁ as₁ as₂ → TRel R₂ (tupMapArg f₁ as₁) (tupMapArg f₂ as₂)
  | [], (), (), .nil => .nil
  | _ :: _, (_, _), (_, _), .cons h hs => .cons (hf h) (TRel.tupMapArg_rel f₁ f₂ hf hs)

theorem mem_tup_zip_tupFreshWith {V₁ V₂ W₁ W₂ : Ty → Type}
    (mk₁ : ∀ {t : Ty}, V₁ t → Nat → W₁ t) (mk₂ : ∀ {t : Ty}, V₂ t → Nat → W₂ t)
    {P : Ctx V₁ V₂ → (t : Ty) → W₁ t → W₂ t → Prop}
    (hweak : ∀ {G₁ G₂ : Ctx V₁ V₂}, (∀ p ∈ G₁, p ∈ G₂) →
      ∀ {t w₁ w₂}, P G₁ t w₁ w₂ → P G₂ t w₁ w₂)
    (hmk : ∀ {t} (v₁ : V₁ t) (v₂ : V₂ t) (b : Nat), P [⟨t, v₁, v₂⟩] t (mk₁ v₁ b) (mk₂ v₂ b)) :
    ∀ {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) (b : Nat)
      (p : (t : Ty) × W₁ t × W₂ t),
      p ∈ Tup.zip (tupFreshWith mk₁ ts xs₁ b) (tupFreshWith mk₂ ts xs₂ b) →
      P (Tup.zip xs₁ xs₂) p.1 p.2.1 p.2.2
  | [], (), (), _, _, hp => nomatch hp
  | _ :: _, (x₁, xs₁), (x₂, xs₂), b, p, hp => by
    simp only [tupFreshWith, Tup.zip] at hp ⊢
    cases hp with
    | head =>
      exact hweak
        (fun _ hq => by cases hq with | head => exact List.mem_cons_self | tail _ h => nomatch h)
        (hmk x₁ x₂ b)
    | tail _ hp =>
      exact hweak (fun _ hq => List.mem_cons_of_mem _ hq)
        (mem_tup_zip_tupFreshWith mk₁ mk₂ hweak hmk xs₁ xs₂ (b + 1) p hp)

private theorem trel_weaken {α : Type} {f g : α → Type} {R S : ∀ a, f a → g a → Prop}
    (h : ∀ {a x y}, R a x y → S a x y) :
    {as : List α} → {xs : Tup f as} → {ys : Tup g as} → TRel R xs ys → TRel S xs ys
  | [], (), (), .nil => .nil
  | _ :: _, (_, _), (_, _), .cons hr hrs => .cons (h hr) (trel_weaken h hrs)

theorem TRel_tupFreshWith {V₁ V₂ W₁ W₂ : Ty → Type}
    (mk₁ : ∀ {t : Ty}, V₁ t → Nat → W₁ t) (mk₂ : ∀ {t : Ty}, V₂ t → Nat → W₂ t)
    {P : Ctx V₁ V₂ → (t : Ty) → W₁ t → W₂ t → Prop}
    (hweak : ∀ {G₁ G₂ : Ctx V₁ V₂}, (∀ p ∈ G₁, p ∈ G₂) →
      ∀ {t w₁ w₂}, P G₁ t w₁ w₂ → P G₂ t w₁ w₂)
    (hmk : ∀ {t} (v₁ : V₁ t) (v₂ : V₂ t) (b : Nat), P [⟨t, v₁, v₂⟩] t (mk₁ v₁ b) (mk₂ v₂ b)) :
    {G' : Ctx V₁ V₂} → {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) → (b : Nat) →
    TRel (fun t w₁ w₂ => P (Tup.zip xs₁ xs₂ ++ G') t w₁ w₂)
      (tupFreshWith mk₁ ts xs₁ b) (tupFreshWith mk₂ ts xs₂ b)
  | _, [], (), (), _ => .nil
  | _, _ :: _, (x₁, xs₁), (x₂, xs₂), b => by
    simp only [tupFreshWith, Tup.zip, List.cons_append]
    exact .cons
      (hweak
        (fun _ hq => by cases hq with | head => exact List.mem_cons_self | tail _ h => nomatch h)
        (hmk x₁ x₂ b))
      (trel_weaken (fun h => hweak (fun _ hq => List.mem_cons_of_mem _ hq) h)
        (TRel_tupFreshWith mk₁ mk₂ hweak hmk xs₁ xs₂ (b + 1)))

theorem tup_zip_self_eq {α : Type} {f : α → Type} {D : Ctx f f}
    (hD : ∀ p ∈ D, p.2.1 = p.2.2) :
    {sig : List α} → (Js : Tup f sig) → ∀ p ∈ Tup.zip Js Js ++ D, p.2.1 = p.2.2
  | [], (), p, hp => hD p hp
  | _ :: _, (_, Js), p, hp => by
    simp only [Tup.zip, List.cons_append] at hp
    cases hp with
    | head => rfl
    | tail _ hp => exact tup_zip_self_eq hD Js p hp

/-! ## Generic `liftFloatRel{1,2,3}` predicate preservation -/

theorem liftFloatRel1_pred
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (M : (t : Ty) → Val t → (Val t → Prop) → Prop)
    (hmono : ∀ t a {P Q : Val t → Prop}, (∀ r, P r → Q r) → M t a P → M t a Q)
    (hleaf : ∀ f a P, floatResultWp f (op f.format (unpackFloat f a)) P → M (.float f) a P)
    (hpair : ∀ s u a₁ a₂ P,
      M s a₁ (fun r₁ => M u a₂ (fun r₂ => P (r₁, r₂))) → M (.pair s u) (a₁, a₂) P) :
    ∀ (t : Ty) (a : Val t) (P : Val t → Prop), liftFloatRel1 op t a P → M t a P
  | .float f, a, P, hw => hleaf f a P hw
  | .bool, _, _, hw => False.elim hw
  | .bits _, _, _, hw => False.elim hw
  | .pair s u, (a₁, a₂), P, hw =>
    hpair s u a₁ a₂ P
      (hmono s a₁ (fun r₁ => liftFloatRel1_pred op M hmono hleaf hpair u a₂ (fun r₂ => P (r₁, r₂)))
        (liftFloatRel1_pred op M hmono hleaf hpair s a₁ _ hw))

theorem liftFloatRel2_pred
    (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (M : (t : Ty) → Val t → Val t → (Val t → Prop) → Prop)
    (hmono : ∀ t a b {P Q : Val t → Prop}, (∀ r, P r → Q r) → M t a b P → M t a b Q)
    (hleaf : ∀ f a b P,
      floatResultWp f (op f.format (unpackFloat f a) (unpackFloat f b)) P → M (.float f) a b P)
    (hpair : ∀ s u a₁ a₂ b₁ b₂ P,
      M s a₁ b₁ (fun r₁ => M u a₂ b₂ (fun r₂ => P (r₁, r₂))) →
      M (.pair s u) (a₁, a₂) (b₁, b₂) P) :
    ∀ (t : Ty) (a b : Val t) (P : Val t → Prop), liftFloatRel2 op t a b P → M t a b P
  | .float f, a, b, P, hw => hleaf f a b P hw
  | .bool, _, _, _, hw => False.elim hw
  | .bits _, _, _, _, hw => False.elim hw
  | .pair s u, (a₁, a₂), (b₁, b₂), P, hw =>
    hpair s u a₁ a₂ b₁ b₂ P
      (hmono s a₁ b₁
        (fun r₁ => liftFloatRel2_pred op M hmono hleaf hpair u a₂ b₂ (fun r₂ => P (r₁, r₂)))
        (liftFloatRel2_pred op M hmono hleaf hpair s a₁ b₁ _ hw))

theorem liftFloatRel3_pred
    (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (M : (t : Ty) → Val t → Val t → Val t → (Val t → Prop) → Prop)
    (hmono : ∀ t a b c {P Q : Val t → Prop}, (∀ r, P r → Q r) → M t a b c P → M t a b c Q)
    (hleaf : ∀ f a b c P,
      floatResultWp f (op f.format (unpackFloat f a) (unpackFloat f b) (unpackFloat f c)) P →
      M (.float f) a b c P)
    (hpair : ∀ s u a₁ a₂ b₁ b₂ c₁ c₂ P,
      M s a₁ b₁ c₁ (fun r₁ => M u a₂ b₂ c₂ (fun r₂ => P (r₁, r₂))) →
      M (.pair s u) (a₁, a₂) (b₁, b₂) (c₁, c₂) P) :
    ∀ (t : Ty) (a b c : Val t) (P : Val t → Prop), liftFloatRel3 op t a b c P → M t a b c P
  | .float f, a, b, c, P, hw => hleaf f a b c P hw
  | .bool, _, _, _, _, hw => False.elim hw
  | .bits _, _, _, _, _, hw => False.elim hw
  | .pair s u, (a₁, a₂), (b₁, b₂), (c₁, c₂), P, hw =>
    hpair s u a₁ a₂ b₁ b₂ c₁ c₂ P
      (hmono s a₁ b₁ c₁
        (fun r₁ =>
          liftFloatRel3_pred op M hmono hleaf hpair u a₂ b₂ c₂ (fun r₂ => P (r₁, r₂)))
        (liftFloatRel3_pred op M hmono hleaf hpair s a₁ b₁ c₁ _ hw))

end LeanQbe.T
