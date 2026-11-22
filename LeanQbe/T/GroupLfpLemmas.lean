module

public import LeanQbe.T.WPLemmas
public import LeanQbe.T.WfLemmas

/-!
# The least join-point solution `Js^*` of a `.group` and `.group` commutation lemmas

`wp Γ Q X (.group bodies k) m` quantifies over every label tuple `Js` that is `Closed` under the
group's bodies, i.e. over every *pre-fixpoint* of `F(Js)ᵢ := wp (bodiesᵢ Js)`. This file gives the
Knaster–Tarski reading of that definition, with **no assumption on `Γ : Env`**:

* `Tup.ofMember` / `Tup.get_ofMember`: build a tuple from a function on positions.
* `DiagV G` (both sides of a value context are equal) and `MonoD D` (the left label of every pair
  implies the right one): the contexts under which two `Wf`-related instantiations of one term
  can be compared semantically.
* `wp_label_mono`: `wp` is monotone in the *labels*. Labels are PHOAS-instantiated, so this is
  parametricity and needs `Wf` (`wp_mono` only covers `Q` and `X`).
* `lfp Γ Q X bodies`: the least closed tuple `Js^*ᵢ xs m := ∀ Js, Closed (bodies Js) Js → Jsᵢ xs m`,
  with `lfp_le` (below every closed tuple) and `lfp_closed` (itself closed).
* `wp_group_iff`: `wp (.group bodies k) m ↔ wp (k Js^*) m`.
* `.group` commutes with `let_`, `load`, `store`, `call`, a `jnz` with a label-free arm, and an
  inner `.group` whose bodies ignore the outer labels (`group_let`, `group_load`, `group_store`,
  `group_call`, `group_jnz_then`, `group_jnz_else`, `group_group_swap`); a group whose entry
  ignores the labels is dead (`group_const`), and a label-free family has an
  instantiation-independent `wp` (`wp_labelfree_iff`).

`Js^*` depends only on `bodies` (not on the memory, nor on enclosing binders), which is what lets
one solution be reused under `∃ P E` (`call`), `∃ v` (`load`) and `op.wp` (`let_`). Only `call`
genuinely needs it: for an arbitrary contract `Γ f`, `∀ Js` cannot be pushed inside `∃ P E`.

The `Wf` hypotheses are the diagonal instance of `Func.Wf` (`Func.Wf.refl` at `Val`/`Cont`,
followed by `Wf.group_inv` and friends); `DiagV`/`MonoD` start from `diag_zip` and `MonoD.nil`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## Tuples from positions -/

/-- The tuple whose component at position `i` is `h i`. -/
@[expose] def Tup.ofMember {α : Type} {f : α → Type} :
    (as : List α) → (∀ {a : α}, Member a as → f a) → Tup f as
  | [], _ => ()
  | _ :: as, h => (h .here, Tup.ofMember as fun i => h (.there i))

/-- `Tup.get` reads back the function a tuple was built from. -/
theorem Tup.get_ofMember {α : Type} {f : α → Type} :
    (as : List α) → (h : ∀ {a : α}, Member a as → f a) → {a : α} → (i : Member a as) →
    (Tup.ofMember as h).get i = h i
  | _ :: _, _, _, .here => rfl
  | _ :: as, h, _, .there i => Tup.get_ofMember as (fun j => h (.there j)) i

/-! ## Diagonal value contexts and monotone label contexts -/

/-- A value context relating every variable to itself. -/
@[expose] def DiagV (G : Ctx Val Val) : Prop := ∀ p ∈ G, p.2.1 = p.2.2

/-- A label context whose left continuations imply the right ones. -/
@[expose] def MonoD (D : Ctx Cont Cont) : Prop := ∀ p ∈ D, ∀ xs m, p.2.1 xs m → p.2.2 xs m

/-- The empty value context is diagonal. -/
theorem DiagV.nil : DiagV [] := fun _ h => nomatch h

/-- The empty label context is monotone. -/
theorem MonoD.nil : MonoD [] := fun _ h => nomatch h

/-- Pairing a value tuple with itself is diagonal (the context of `Func.Wf.refl`). -/
theorem diag_zip : {ts : List Ty} → (xs : Tup Val ts) → DiagV (Tup.zip xs xs)
  | [], _ => fun _ h => nomatch h
  | _ :: _, (_, xs) => fun p hp => by
    cases hp with
    | head => rfl
    | tail _ hp => exact diag_zip xs p hp

/-- Binding a result tuple (`let_`, `call`, block parameters) keeps the context diagonal. -/
theorem DiagV.append {G : Ctx Val Val} (hG : DiagV G) {ts : List Ty} (xs : Tup Val ts) :
    DiagV (Tup.zip xs xs ++ G) := fun p hp => by
  rcases List.mem_append.1 hp with hp | hp
  · exact diag_zip xs p hp
  · exact hG p hp

/-- Binding one value (`load`) keeps the context diagonal. -/
theorem DiagV.cons {G : Ctx Val Val} (hG : DiagV G) {t : Ty} (v : Val t) :
    DiagV (⟨t, v, v⟩ :: G) := fun p hp => by
  cases hp with
  | head => rfl
  | tail _ hp => exact hG p hp

/-- Pairing two label tuples is monotone when the first implies the second pointwise. -/
theorem mono_zip : {sig : List (List Ty)} → (A B : Tup Cont sig) →
    (∀ {ts} (i : Member ts sig) xs m, A.get i xs m → B.get i xs m) → MonoD (Tup.zip A B)
  | [], _, _, _ => fun _ h => nomatch h
  | _ :: _, (_, A), (_, B), h => fun p hp => by
    cases hp with
    | head => exact h .here
    | tail _ hp => exact mono_zip A B (fun i => h (.there i)) p hp

/-- Pairing a label tuple with itself is monotone. -/
theorem mono_zip_self {sig : List (List Ty)} (Js : Tup Cont sig) : MonoD (Tup.zip Js Js) :=
  mono_zip Js Js fun _ _ _ h => h

/-- Monotone label contexts concatenate. -/
theorem MonoD.append {D H : Ctx Cont Cont} (hH : MonoD H) (hD : MonoD D) : MonoD (H ++ D) :=
  fun p hp => by
    rcases List.mem_append.1 hp with hp | hp
    · exact hH p hp
    · exact hD p hp

/-- Related operands of a diagonal context denote the same value. -/
theorem argRel_val {G : Ctx Val Val} (hG : DiagV G) {t : Ty} {a₁ a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → a₁.val = a₂.val
  | .var hm => hG _ hm
  | .imm _ => rfl

/-- Related operand tuples of a diagonal context denote the same values. -/
theorem trel_vals {G : Ctx Val Val} (hG : DiagV G) :
    {ts : List Ty} → {as₁ as₂ : Tup (Arg Val) ts} → TRel (ArgRel G) as₁ as₂ → vals as₁ = vals as₂
  | [], _, _, .nil => rfl
  | _ :: _, _, _, .cons h hs => by dsimp only [vals]; rw [argRel_val hG h, trel_vals hG hs]

/-! ## Label monotonicity of `wp` (parametricity from `Wf`) -/

/-- `wp` is monotone in the labels: two `Wf`-related instantiations of a term at the same values
(`DiagV G`) and at pointwise weaker labels (`MonoD D`) have weaker `wp`s. In the `group` case
both sides are instantiated at the same `Js`, and `Closed` is antitone in the bodies. -/
theorem wp_label_mono {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx Val Val} {D : Ctx Cont Cont} {e₁ e₂ : Expr Val Cont rs} (h : Wf G D e₁ e₂) :
    DiagV G → MonoD D → ∀ m, wp Γ Q X e₁ m → wp Γ Q X e₂ m := by
  induction h using Wf.induct with
  | let_ hop _ ih =>
    intro hG hD m h
    cases hop with | mk code hargs =>
    dsimp only [wp, Op.wp] at h ⊢
    rw [← trel_vals hG hargs]
    exact OpCode.wp_mono code _ (fun r hr => ih r r (hG.append r) hD m hr) h
  | load t ha _ ih =>
    intro hG hD m ⟨v, hv, h⟩
    dsimp only [wp]
    rw [← argRel_val hG ha]
    exact ⟨v, hv, ih v v (hG.cons v) hD m h⟩
  | store hv ha _ ih =>
    intro hG hD m ⟨hok, h⟩
    dsimp only [wp]
    rw [← argRel_val hG hv, ← argRel_val hG ha]
    exact ⟨hok, ih hG hD _ h⟩
  | call f hargs _ ih =>
    intro hG hD m ⟨P, E, hΓ, hP, hE⟩
    dsimp only [wp]
    rw [← trel_vals hG hargs]
    exact ⟨P, E, hΓ, fun r m' hr => ih r r (hG.append r) hD m' (hP r m' hr), hE⟩
  | jnz hc _ _ iht ihe =>
    intro hG hD m ⟨ht, he⟩
    dsimp only [wp]
    rw [← argRel_val hG hc]
    exact ⟨fun h => iht hG hD m (ht h), fun h => ihe hG hD m (he h)⟩
  | jump hj hargs =>
    intro hG hD m h
    dsimp only [wp] at h ⊢
    rw [← trel_vals hG hargs]
    exact hD _ hj _ m h
  | ret hvs =>
    intro hG _ m h
    dsimp only [wp] at h ⊢
    rw [← trel_vals hG hvs]
    exact h
  | exit f hargs =>
    intro hG _ m h
    dsimp only [wp] at h ⊢
    rw [← trel_vals hG hargs]
    exact h
  | hlt => intro _ _ _ h; exact h
  | group _ _ ihb ihk =>
    intro hG hD m h Js hcl
    have hD' : MonoD (Tup.zip Js Js ++ _) := (mono_zip_self Js).append hD
    refine ihk Js Js hG hD' m (h Js ?_)
    rw [closed_iff] at hcl ⊢
    exact fun i xs m' hb => hcl i xs m' (ihb Js Js i xs xs (hG.append xs) hD' m' hb)

/-- A label-free family (`Wf` under the *outer* label context only) has the same `wp` at every
label instantiation. With `Js₁ := lfp ..` this discharges the arm that a sunk group leaves. -/
theorem wp_labelfree_iff {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {sig : List (List Ty)} {G : Ctx Val Val} {D : Ctx Cont Cont} (hG : DiagV G) (hD : MonoD D)
    (e : Tup Cont sig → Expr Val Cont rs) (he : ∀ Js₁ Js₂, Wf G D (e Js₁) (e Js₂))
    (Js₁ Js₂ : Tup Cont sig) (m : Mem 64) :
    wp Γ Q X (e Js₁) m ↔ wp Γ Q X (e Js₂) m :=
  ⟨wp_label_mono (he Js₁ Js₂) hG hD m, wp_label_mono (he Js₂ Js₁) hG hD m⟩

/-! ## The least join-point solution `Js^*` -/

/-- The least closed label tuple of a group:
`Js^*ᵢ xs m := ∀ Js, Closed Γ Q X (bodies Js) Js → Jsᵢ xs m`. The quantifier over `Js` is
impredicative (`Prop`), so `lfp .. : Tup Cont sig` stays in `Type`. -/
@[expose] def lfp (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) {sig : List (List Ty)}
    (bodies : Tup Cont sig → Blocks Val Cont rs sig) : Tup Cont sig :=
  Tup.ofMember sig fun i xs m => ∀ Js, Closed Γ Q X (bodies Js) Js → Js.get i xs m

section
variable {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {sig : List (List Ty)}
  {G : Ctx Val Val} {D : Ctx Cont Cont} {bodies : Tup Cont sig → Blocks Val Cont rs sig}

/-- Component `i` of `Js^*` holds iff component `i` of every closed tuple does. -/
theorem lfp_get {ts : List Ty} (i : Member ts sig) (xs : Tup Val ts) (m : Mem 64) :
    (lfp Γ Q X bodies).get i xs m ↔ ∀ Js, Closed Γ Q X (bodies Js) Js → Js.get i xs m := by
  rw [lfp, Tup.get_ofMember]

/-- `Js^*` is below every closed tuple. -/
theorem lfp_le {Js : Tup Cont sig} (hcl : Closed Γ Q X (bodies Js) Js) :
    ∀ {ts} (i : Member ts sig) xs m, (lfp Γ Q X bodies).get i xs m → Js.get i xs m :=
  fun i xs m h => (lfp_get i xs m).1 h Js hcl

/-- `Js^*` is closed. Only `Wf` of the bodies (parametricity) is needed, nothing about `Γ`. -/
theorem lfp_closed (hG : DiagV G) (hD : MonoD D)
    (hwf : ∀ Js₁ Js₂, WfB G (Tup.zip Js₁ Js₂ ++ D) (bodies Js₁) (bodies Js₂)) :
    Closed Γ Q X (bodies (lfp Γ Q X bodies)) (lfp Γ Q X bodies) := by
  rw [closed_iff]
  intro ts i xs m hb
  rw [lfp_get]
  intro Js hJs
  have hmono : MonoD (Tup.zip (lfp Γ Q X bodies) Js ++ D) :=
    (mono_zip _ _ (lfp_le hJs)).append hD
  exact (closed_iff Γ Q X _ _).1 hJs i xs m
    (wp_label_mono ((hwf (lfp Γ Q X bodies) Js).get i xs xs) (hG.append xs) hmono m hb)

/-- A group is its entry at the least closed tuple. -/
theorem wp_group_iff (hG : DiagV G) (hD : MonoD D) {k : Tup Cont sig → Expr Val Cont rs}
    (hb : ∀ Js₁ Js₂, WfB G (Tup.zip Js₁ Js₂ ++ D) (bodies Js₁) (bodies Js₂))
    (hk : ∀ Js₁ Js₂, Wf G (Tup.zip Js₁ Js₂ ++ D) (k Js₁) (k Js₂)) (m : Mem 64) :
    wp Γ Q X (.group bodies k) m ↔ wp Γ Q X (k (lfp Γ Q X bodies)) m := by
  constructor
  · intro h
    exact h _ (lfp_closed hG hD hb)
  · intro h Js hcl
    exact wp_label_mono (hk _ Js) hG ((mono_zip _ _ (lfp_le hcl)).append hD) m h

/-! ## Commutation lemmas -/

/-- Block lists stay `Wf`-related under additional value binders. -/
theorem WfB.weaken_append {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {s : List (List Ty)} {bs₁ : Blocks V₁ L₁ rs s}
    {bs₂ : Blocks V₂ L₂ rs s} (H : Ctx V₁ V₂) (h : WfB G D bs₁ bs₂) : WfB (H ++ G) D bs₁ bs₂ :=
  h.weaken (fun _ hp => List.mem_append_right H hp) fun _ hp => hp

/-- A group whose entry `e` does not mention its labels is dead. -/
theorem group_const (e : Expr Val Cont rs) (hG : DiagV G) (hD : MonoD D)
    (hb : ∀ Js₁ Js₂, WfB G (Tup.zip Js₁ Js₂ ++ D) (bodies Js₁) (bodies Js₂))
    (he : Wf G D e e) (m : Mem 64) :
    wp Γ Q X (.group bodies fun _ => e) m ↔ wp Γ Q X e m :=
  wp_group_iff hG hD hb
    (fun _ _ => he.weaken_D fun _ hp => List.mem_append_right _ hp) m

/-- A group commutes with a `let_` in its entry. -/
theorem group_let {ts : List Ty} (op : Op Val ts)
    (k : Tup Val ts → Tup Cont sig → Expr Val Cont rs) (hG : DiagV G) (hD : MonoD D)
    (hwf : Wf G D (.group bodies fun Js => .let_ op fun r => k r Js)
      (.group bodies fun Js => .let_ op fun r => k r Js)) (m : Mem 64) :
    wp Γ Q X (.group bodies fun Js => .let_ op fun r => k r Js) m ↔
      wp Γ Q X (.let_ op fun r => .group bodies (k r)) m := by
  obtain ⟨hb, hk⟩ := Wf.group_inv hwf
  have hkr : ∀ (r : Tup Val ts) Js₁ Js₂,
      Wf (Tup.zip r r ++ G) (Tup.zip Js₁ Js₂ ++ D) (k r Js₁) (k r Js₂) :=
    fun r Js₁ Js₂ => (Wf.let_inv (hk Js₁ Js₂)).2 r r
  have hbr : ∀ (r : Tup Val ts) Js₁ Js₂,
      WfB (Tup.zip r r ++ G) (Tup.zip Js₁ Js₂ ++ D) (bodies Js₁) (bodies Js₂) :=
    fun r Js₁ Js₂ => WfB.weaken_append _ (hb Js₁ Js₂)
  rw [wp_group_iff hG hD hb hk]
  dsimp only [wp]
  exact ⟨Op.wp_mono fun r h => (wp_group_iff (hG.append r) hD (hbr r) (hkr r) m).2 h,
    Op.wp_mono fun r h => (wp_group_iff (hG.append r) hD (hbr r) (hkr r) m).1 h⟩

/-- A group commutes with a `load` in its entry (`Js^*` does not depend on the loaded value). -/
theorem group_load (t : Ty) (a : Arg Val i64)
    (k : Val t → Tup Cont sig → Expr Val Cont rs) (hG : DiagV G) (hD : MonoD D)
    (hwf : Wf G D (.group bodies fun Js => .load t a fun v => k v Js)
      (.group bodies fun Js => .load t a fun v => k v Js)) (m : Mem 64) :
    wp Γ Q X (.group bodies fun Js => .load t a fun v => k v Js) m ↔
      wp Γ Q X (.load t a fun v => .group bodies (k v)) m := by
  obtain ⟨hb, hk⟩ := Wf.group_inv hwf
  have hkv : ∀ (v : Val t) Js₁ Js₂,
      Wf (⟨t, v, v⟩ :: G) (Tup.zip Js₁ Js₂ ++ D) (k v Js₁) (k v Js₂) :=
    fun v Js₁ Js₂ => (Wf.load_inv (hk Js₁ Js₂)).2 v v
  have hbv : ∀ (v : Val t) Js₁ Js₂,
      WfB (⟨t, v, v⟩ :: G) (Tup.zip Js₁ Js₂ ++ D) (bodies Js₁) (bodies Js₂) :=
    fun v Js₁ Js₂ => WfB.weaken_append [⟨t, v, v⟩] (hb Js₁ Js₂)
  rw [wp_group_iff hG hD hb hk]
  dsimp only [wp]
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, (wp_group_iff (hG.cons v) hD (hbv v) (hkv v) m).2 h⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, (wp_group_iff (hG.cons v) hD (hbv v) (hkv v) m).1 h⟩

/-- A group commutes with a `store` in its entry (`Js^*` does not depend on the memory). -/
theorem group_store {t : Ty} (v : Arg Val t) (a : Arg Val i64)
    (k : Tup Cont sig → Expr Val Cont rs) (hG : DiagV G) (hD : MonoD D)
    (hwf : Wf G D (.group bodies fun Js => .store v a (k Js))
      (.group bodies fun Js => .store v a (k Js))) (m : Mem 64) :
    wp Γ Q X (.group bodies fun Js => .store v a (k Js)) m ↔
      wp Γ Q X (.store v a (.group bodies k)) m := by
  obtain ⟨hb, hk⟩ := Wf.group_inv hwf
  have hk' : ∀ Js₁ Js₂, Wf G (Tup.zip Js₁ Js₂ ++ D) (k Js₁) (k Js₂) :=
    fun Js₁ Js₂ => (Wf.store_inv (hk Js₁ Js₂)).2.2
  rw [wp_group_iff hG hD hb hk, wp_store, wp_store, wp_group_iff hG hD hb hk']

/-- A group commutes with a `call` in its entry, for an arbitrary contract `Γ f`. This is the
step that needs `Js^*`: the source is instantiated once, at `Js^*`, to obtain `P` and `E`. -/
theorem group_call {f : Sym} {as bs : List Ty} (args : Tup (Arg Val) as)
    (k : Tup Val bs → Tup Cont sig → Expr Val Cont rs) (hG : DiagV G) (hD : MonoD D)
    (hwf : Wf G D (.group bodies fun Js => .call f args fun r => k r Js)
      (.group bodies fun Js => .call f args fun r => k r Js)) (m : Mem 64) :
    wp Γ Q X (.group bodies fun Js => .call f args fun r => k r Js) m ↔
      wp Γ Q X (.call f args fun r => .group bodies (k r)) m := by
  obtain ⟨hb, hk⟩ := Wf.group_inv hwf
  have hkr : ∀ (r : Tup Val bs) Js₁ Js₂,
      Wf (Tup.zip r r ++ G) (Tup.zip Js₁ Js₂ ++ D) (k r Js₁) (k r Js₂) :=
    fun r Js₁ Js₂ => (Wf.call_inv (hk Js₁ Js₂)).2 r r
  have hbr : ∀ (r : Tup Val bs) Js₁ Js₂,
      WfB (Tup.zip r r ++ G) (Tup.zip Js₁ Js₂ ++ D) (bodies Js₁) (bodies Js₂) :=
    fun r Js₁ Js₂ => WfB.weaken_append _ (hb Js₁ Js₂)
  rw [wp_group_iff hG hD hb hk]
  dsimp only [wp]
  constructor
  · rintro ⟨P, E, hΓ, hP, hE⟩
    exact ⟨P, E, hΓ, fun r m' hr =>
      (wp_group_iff (hG.append r) hD (hbr r) (hkr r) m').2 (hP r m' hr), hE⟩
  · rintro ⟨P, E, hΓ, hP, hE⟩
    exact ⟨P, E, hΓ, fun r m' hr =>
      (wp_group_iff (hG.append r) hD (hbr r) (hkr r) m').1 (hP r m' hr), hE⟩

/-- A group sinks into the `then` arm of a `jnz` whose `else` arm `e` does not mention the
group's labels (`e` is a constant here; `wp_labelfree_iff` turns a `Wf G D` side condition on a
label-indexed arm into this form). -/
theorem group_jnz_then (c : Arg Val .bool) (t : Tup Cont sig → Expr Val Cont rs)
    (e : Expr Val Cont rs) (hG : DiagV G) (hD : MonoD D)
    (hwf : Wf G D (.group bodies fun Js => .jnz c (t Js) e)
      (.group bodies fun Js => .jnz c (t Js) e)) (m : Mem 64) :
    wp Γ Q X (.group bodies fun Js => .jnz c (t Js) e) m ↔
      wp Γ Q X (.jnz c (.group bodies t) e) m := by
  obtain ⟨hb, hk⟩ := Wf.group_inv hwf
  have ht : ∀ Js₁ Js₂, Wf G (Tup.zip Js₁ Js₂ ++ D) (t Js₁) (t Js₂) :=
    fun Js₁ Js₂ => (Wf.jnz_inv (hk Js₁ Js₂)).2.1
  rw [wp_group_iff hG hD hb hk, wp_jnz, wp_jnz, wp_group_iff hG hD hb ht]

/-- A group sinks into the `else` arm of a `jnz` whose `then` arm `t` does not mention the
group's labels. -/
theorem group_jnz_else (c : Arg Val .bool) (t : Expr Val Cont rs)
    (e : Tup Cont sig → Expr Val Cont rs) (hG : DiagV G) (hD : MonoD D)
    (hwf : Wf G D (.group bodies fun Js => .jnz c t (e Js))
      (.group bodies fun Js => .jnz c t (e Js))) (m : Mem 64) :
    wp Γ Q X (.group bodies fun Js => .jnz c t (e Js)) m ↔
      wp Γ Q X (.jnz c t (.group bodies e)) m := by
  obtain ⟨hb, hk⟩ := Wf.group_inv hwf
  have he : ∀ Js₁ Js₂, Wf G (Tup.zip Js₁ Js₂ ++ D) (e Js₁) (e Js₂) :=
    fun Js₁ Js₂ => (Wf.jnz_inv (hk Js₁ Js₂)).2.2
  rw [wp_group_iff hG hD hb hk, wp_jnz, wp_jnz, wp_group_iff hG hD hb he]

private theorem mem_swap3 {α : Type} {A B C : List α} {p : α} :
    p ∈ A ++ (B ++ C) → p ∈ B ++ (A ++ C) := by
  simp only [List.mem_append]
  rintro (h | h | h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

private theorem mem_mid {α : Type} {A B C : List α} {p : α} : p ∈ A ++ C → p ∈ A ++ (B ++ C) := by
  simp only [List.mem_append]
  rintro (h | h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

/-- Two nested groups swap when the inner bodies `c` ignore the outer labels (`hc` is stated
under `D` only) and the outer bodies ignore the inner labels (they are not in scope). Both sides
are `wp (k Js^* Hs^*)`. -/
theorem group_group_swap {sig' : List (List Ty)} (c : Tup Cont sig' → Blocks Val Cont rs sig')
    (k : Tup Cont sig → Tup Cont sig' → Expr Val Cont rs) (hG : DiagV G) (hD : MonoD D)
    (hc : ∀ Hs₁ Hs₂, WfB G (Tup.zip Hs₁ Hs₂ ++ D) (c Hs₁) (c Hs₂))
    (hbk : ∀ Js₁ Js₂, WfB G (Tup.zip Js₁ Js₂ ++ D) (bodies Js₁) (bodies Js₂))
    (hk : ∀ Js₁ Js₂ Hs₁ Hs₂,
      Wf G (Tup.zip Hs₁ Hs₂ ++ (Tup.zip Js₁ Js₂ ++ D)) (k Js₁ Hs₁) (k Js₂ Hs₂)) (m : Mem 64) :
    wp Γ Q X (.group bodies fun Js => .group c (k Js)) m ↔
      wp Γ Q X (.group c fun Hs => .group bodies fun Js => k Js Hs) m := by
  have hk_sw : ∀ Hs₁ Hs₂ Js₁ Js₂,
      Wf G (Tup.zip Js₁ Js₂ ++ (Tup.zip Hs₁ Hs₂ ++ D)) (k Js₁ Hs₁) (k Js₂ Hs₂) :=
    fun H₁ H₂ J₁ J₂ => (hk J₁ J₂ H₁ H₂).weaken_D fun _ hp => mem_swap3 hp
  have hc' : ∀ (Js₁ Js₂ : Tup Cont sig) Hs₁ Hs₂,
      WfB G (Tup.zip Hs₁ Hs₂ ++ (Tup.zip Js₁ Js₂ ++ D)) (c Hs₁) (c Hs₂) :=
    fun _ _ H₁ H₂ => (hc H₁ H₂).weaken (fun _ hp => hp) fun _ hp => mem_mid hp
  have hbk' : ∀ (Hs₁ Hs₂ : Tup Cont sig') Js₁ Js₂,
      WfB G (Tup.zip Js₁ Js₂ ++ (Tup.zip Hs₁ Hs₂ ++ D)) (bodies Js₁) (bodies Js₂) :=
    fun _ _ J₁ J₂ => (hbk J₁ J₂).weaken (fun _ hp => hp) fun _ hp => mem_mid hp
  have hmJ : MonoD (Tup.zip (lfp Γ Q X bodies) (lfp Γ Q X bodies) ++ D) :=
    (mono_zip_self _).append hD
  have hmH : MonoD (Tup.zip (lfp Γ Q X c) (lfp Γ Q X c) ++ D) := (mono_zip_self _).append hD
  -- Left: `wp (group c (k Js^*))`, then `wp (k Js^* Hs^*)`.
  rw [wp_group_iff hG hD hbk fun J₁ J₂ => .group (hc' J₁ J₂) (hk J₁ J₂),
    wp_group_iff hG hmJ (hc' _ _) (hk _ _)]
  -- Right: `wp (group bodies (k · Hs^*))`, then `wp (k Js^* Hs^*)`.
  rw [wp_group_iff hG hD hc fun H₁ H₂ => .group (hbk' H₁ H₂) (hk_sw H₁ H₂),
    wp_group_iff hG hmH (hbk' _ _) (hk_sw _ _)]

end

end LeanQbe.T
