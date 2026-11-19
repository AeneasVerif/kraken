module

public import LeanQbe.T.Flat
public import LeanQbe.T.WfLemmas
public import LeanQbe.T.WPLemmas
public meta import Lean.Elab.Tactic

/-!
# Soundness of `TFlat` reification: `denote_wf` and `Func.wf_of_reify`

* `denote_wf` / `denoteB_wf`: for every `tf : TFlat rs` and any two instantiations
  `(V₁, L₁)` and `(V₂, L₂)` with related contexts `CtxRel G vs₁ vs₂` and `CtxRel D ls₁ ls₂`,
  `denote V₁ L₁ tf vs₁ ls₁` and `denote V₂ L₂ tf vs₂ ls₂` are `Wf G D`-related.
* `Func.wf_of_denote` / `Func.wf_of_reify`: a closed function equal to the denotation of its
  own reification (`toTFlat`) is `Func.Wf`.
* `denote_wp` / `renorm_wp` / `Func.renorm_spec`: `reifyFunc`/`denoteFunc` round-trip preserves
  `Func.wp` for any `Func.Wf` function without hitting `.hlt`.
* `t_kernel_rfl` and `t_wf_reify`: kernel-only `Eq.refl` check avoiding elaborator `isDefEq`
  overhead on large PHOAS terms.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Optional values and context relation -/

/-- Both `none`, or both `some` and related by `R`. -/
def ORel {α β : Type} (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

/-- Entry-wise correspondence between two sigma-tagged runtime environments and a relational
context `G`. -/
inductive CtxRel {α : Type} {f g : α → Type} (G : Ctx f g) :
    List ((a : α) × f a) → List ((a : α) × g a) → Prop
  | nil : CtxRel G [] []
  | cons {a : α} {x : f a} {y : g a} {xs : List ((a : α) × f a)} {ys : List ((a : α) × g a)} :
      ⟨a, x, y⟩ ∈ G → CtxRel G xs ys → CtxRel G (⟨a, x⟩ :: xs) (⟨a, y⟩ :: ys)

theorem CtxRel.mono {α : Type} {f g : α → Type} {G G' : Ctx f g}
    (hG : ∀ p ∈ G, p ∈ G') {xs ys} (h : CtxRel G xs ys) : CtxRel G' xs ys := by
  induction h with
  | nil => exact .nil
  | cons hxy _ ih => exact .cons (hG _ hxy) ih

private theorem ctxRel_pushTup_aux {α : Type} {f g : α → Type} {G' : Ctx f g} :
    {as : List α} → {xs₁ : Tup f as} → {xs₂ : Tup g as} →
    {acc₁ : List ((a : α) × f a)} → {acc₂ : List ((a : α) × g a)} →
    (∀ {a x y}, ⟨a, x, y⟩ ∈ Tup.zip xs₁ xs₂ → ⟨a, x, y⟩ ∈ G') →
    CtxRel G' acc₁ acc₂ →
    CtxRel G' (pushTup xs₁ acc₁) (pushTup xs₂ acc₂)
  | [], (), (), _, _, _, hacc => hacc
  | _ :: _, (_, xs₁), (_, xs₂), _, _, hmem, hacc =>
    ctxRel_pushTup_aux (xs₁ := xs₁) (xs₂ := xs₂)
      (fun hp => hmem (List.mem_cons_of_mem _ hp))
      (.cons (hmem List.mem_cons_self) hacc)

theorem ctxRel_pushTup {α : Type} {f g : α → Type} {G : Ctx f g} {as : List α}
    (xs₁ : Tup f as) (xs₂ : Tup g as) {vs₁ : List ((a : α) × f a)} {vs₂ : List ((a : α) × g a)}
    (hvs : CtxRel G vs₁ vs₂) :
    CtxRel (Tup.zip xs₁ xs₂ ++ G) (pushTup xs₁ vs₁) (pushTup xs₂ vs₂) :=
  ctxRel_pushTup_aux (fun hp => List.mem_append_left G hp)
    (hvs.mono fun _ hp => List.mem_append_right _ hp)

/-! ## Lookup and operand denotation lemmas -/

theorem listGet?_rel {α : Type} {f g : α → Type} {G : Ctx f g} :
    {vs₁ : List ((a : α) × f a)} → {vs₂ : List ((a : α) × g a)} →
    CtxRel G vs₁ vs₂ → ∀ idx : Nat,
    ORel (fun p q => ∃ a x y, p = ⟨a, x⟩ ∧ q = ⟨a, y⟩ ∧ ⟨a, x, y⟩ ∈ G)
      (listGet? vs₁ idx) (listGet? vs₂ idx)
  | [], [], .nil, idx => by cases idx <;> trivial
  | _ :: _, _ :: _, .cons hxy _, 0 => ⟨_, _, _, rfl, rfl, hxy⟩
  | _ :: _, _ :: _, .cons _ hrest, idx + 1 => listGet?_rel hrest idx

section
variable {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}

theorem castTy_rel {G : Ctx V₁ V₂} {t' t : Ty} {v₁ : V₁ t'} {v₂ : V₂ t'}
    (h : ⟨t', v₁, v₂⟩ ∈ G) :
    ORel (fun x y => ⟨t, x, y⟩ ∈ G) (castTy t' t v₁) (castTy t' t v₂) := by
  cases t' with
  | bool => cases t <;> first | exact h | trivial
  | bits m =>
    cases t with
    | bits n =>
      simp only [castTy]
      split <;> rename_i heq
      · subst heq; exact h
      · trivial
    | _ => trivial
  | float f =>
    cases t with
    | float g =>
      simp only [castTy]
      split <;> rename_i heq
      · subst heq; exact h
      · trivial
    | _ => trivial
  | pair a1 b1 =>
    cases t with
    | pair a2 b2 =>
      simp only [castTy]
      cases tyDecEq a1 a2 with
      | isFalse _ => trivial
      | isTrue h1 =>
        cases tyDecEq b1 b2 with
        | isFalse _ => trivial
        | isTrue h2 => subst h1; subst h2; exact h
    | _ => trivial

theorem castListTy_rel {D : Ctx L₁ L₂} {ts' ts : List Ty} {l₁ : L₁ ts'} {l₂ : L₂ ts'}
    (h : ⟨ts', l₁, l₂⟩ ∈ D) :
    ORel (fun x y => ⟨ts, x, y⟩ ∈ D) (castListTy ts' ts l₁) (castListTy ts' ts l₂) := by
  simp only [castListTy]
  cases listTyDecEq ts' ts with
  | isTrue heq => subst heq; exact h
  | isFalse _ => trivial

theorem lookupV_rel {G : Ctx V₁ V₂} {vs₁ vs₂} (hvs : CtxRel G vs₁ vs₂) (t : Ty) (idx : Nat) :
    ORel (fun x y => ⟨t, x, y⟩ ∈ G) (lookupV vs₁ t idx) (lookupV vs₂ t idx) := by
  have hg := listGet?_rel hvs idx
  simp only [lookupV]
  cases e₁ : listGet? vs₁ idx <;> cases e₂ : listGet? vs₂ idx <;> rw [e₁, e₂] at hg <;>
    simp only [ORel] at hg ⊢
  rcases hg with ⟨a, x, y, rfl, rfl, hmem⟩
  exact castTy_rel hmem

theorem lookupL_rel {D : Ctx L₁ L₂} {ls₁ ls₂} (hls : CtxRel D ls₁ ls₂) (ts : List Ty) (idx : Nat) :
    ORel (fun x y => ⟨ts, x, y⟩ ∈ D) (lookupL ls₁ ts idx) (lookupL ls₂ ts idx) := by
  have hg := listGet?_rel hls idx
  simp only [lookupL]
  cases e₁ : listGet? ls₁ idx <;> cases e₂ : listGet? ls₂ idx <;> rw [e₁, e₂] at hg <;>
    simp only [ORel] at hg ⊢
  rcases hg with ⟨a, x, y, rfl, rfl, hmem⟩
  exact castListTy_rel hmem

theorem denoteArg_rel {G : Ctx V₁ V₂} {vs₁ vs₂} (hvs : CtxRel G vs₁ vs₂) {t : Ty} (a : Arg K t) :
    ORel (ArgRel G t) (denoteArg vs₁ a) (denoteArg vs₂ a) := by
  cases a with
  | var idx =>
    have hl := lookupV_rel hvs t idx
    simp only [denoteArg]
    cases e₁ : lookupV vs₁ t idx <;> cases e₂ : lookupV vs₂ t idx <;> rw [e₁, e₂] at hl <;>
      simp only [ORel] at hl ⊢
    exact .var hl
  | imm c => exact .imm c

theorem denoteArgs_rel {G : Ctx V₁ V₂} {vs₁ vs₂} (hvs : CtxRel G vs₁ vs₂) :
    {ts : List Ty} → (as : Tup (Arg K) ts) →
    ORel (TRel (ArgRel G)) (denoteArgs vs₁ as) (denoteArgs vs₂ as)
  | [], () => .nil
  | _ :: _, (a, as) => by
    have ha := denoteArg_rel hvs a
    have has := denoteArgs_rel hvs as
    simp only [denoteArgs]
    cases e₁ : denoteArg vs₁ a <;> cases e₂ : denoteArg vs₂ a <;> rw [e₁, e₂] at ha <;>
      simp only [ORel] at ha ⊢ <;>
      cases f₁ : denoteArgs vs₁ as <;> cases f₂ : denoteArgs vs₂ as <;> rw [f₁, f₂] at has <;>
      simp only [ORel] at has ⊢
    exact .cons ha has

end

/-! ## `denote_wf` and `Func.wf_of_reify` -/

mutual
/-- Every denotation of a `TFlat` across related contexts is `Wf`-related. -/
theorem denote_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    (tf : TFlat rs) → {G : Ctx V₁ V₂} → {D : Ctx L₁ L₂} →
    {vs₁ : List ((t : Ty) × V₁ t)} → {vs₂ : List ((t : Ty) × V₂ t)} →
    {ls₁ : List ((ts : List Ty) × L₁ ts)} → {ls₂ : List ((ts : List Ty) × L₂ ts)} →
    CtxRel G vs₁ vs₂ → CtxRel D ls₁ ls₂ →
    Wf G D (denote V₁ L₁ tf vs₁ ls₁) (denote V₂ L₂ tf vs₂ ls₂)
  | .let_ op k, _, _, vs₁, vs₂, ls₁, ls₂, hvs, hls => by
    have hr := denoteArgs_rel hvs op.args
    simp only [denote]
    cases e₁ : denoteArgs vs₁ op.args <;> cases e₂ : denoteArgs vs₂ op.args <;>
      rw [e₁, e₂] at hr <;> simp only [ORel] at hr ⊢
    · exact .hlt
    · exact .let_ (.mk op.code hr) fun xs₁ xs₂ =>
        denote_wf k (ctxRel_pushTup xs₁ xs₂ hvs) hls
  | .load t a k, _, _, vs₁, vs₂, ls₁, ls₂, hvs, hls => by
    have hr := denoteArg_rel hvs a
    simp only [denote]
    cases e₁ : denoteArg vs₁ a <;> cases e₂ : denoteArg vs₂ a <;>
      rw [e₁, e₂] at hr <;> simp only [ORel] at hr ⊢
    · exact .hlt
    · exact .load t hr fun v₁ v₂ =>
        denote_wf k (.cons List.mem_cons_self (hvs.mono fun _ hp => List.mem_cons_of_mem _ hp)) hls
  | .store v a k, _, _, vs₁, vs₂, ls₁, ls₂, hvs, hls => by
    have hv := denoteArg_rel hvs v
    have ha := denoteArg_rel hvs a
    simp only [denote]
    cases e₁ : denoteArg vs₁ v <;> cases e₂ : denoteArg vs₂ v <;> rw [e₁, e₂] at hv <;>
      simp only [ORel] at hv ⊢ <;>
      cases f₁ : denoteArg vs₁ a <;> cases f₂ : denoteArg vs₂ a <;> rw [f₁, f₂] at ha <;>
      simp only [ORel] at ha ⊢ <;>
      first | exact .hlt | exact .store hv ha (denote_wf k hvs hls)
  | .call f _ args k, _, _, vs₁, vs₂, ls₁, ls₂, hvs, hls => by
    have hr := denoteArgs_rel hvs args
    simp only [denote]
    cases e₁ : denoteArgs vs₁ args <;> cases e₂ : denoteArgs vs₂ args <;>
      rw [e₁, e₂] at hr <;> simp only [ORel] at hr ⊢
    · exact .hlt
    · exact .call f hr fun xs₁ xs₂ =>
        denote_wf k (ctxRel_pushTup xs₁ xs₂ hvs) hls
  | .jnz c t e, _, _, vs₁, vs₂, ls₁, ls₂, hvs, hls => by
    have hr := denoteArg_rel hvs c
    simp only [denote]
    cases e₁ : denoteArg vs₁ c <;> cases e₂ : denoteArg vs₂ c <;>
      rw [e₁, e₂] at hr <;> simp only [ORel] at hr ⊢
    · exact .hlt
    · exact .jnz hr (denote_wf t hvs hls) (denote_wf e hvs hls)
  | .jump (ts := ts) j args, _, _, vs₁, vs₂, ls₁, ls₂, hvs, hls => by
    have hj := lookupL_rel hls ts j
    have hr := denoteArgs_rel hvs args
    simp only [denote]
    cases e₁ : lookupL ls₁ ts j <;> cases e₂ : lookupL ls₂ ts j <;> rw [e₁, e₂] at hj <;>
      simp only [ORel] at hj ⊢ <;>
      cases f₁ : denoteArgs vs₁ args <;> cases f₂ : denoteArgs vs₂ args <;> rw [f₁, f₂] at hr <;>
      simp only [ORel] at hr ⊢ <;>
      first | exact .hlt | exact .jump hj hr
  | .ret vs, _, _, vs₁, vs₂, _, _, hvs, _ => by
    have hr := denoteArgs_rel hvs vs
    simp only [denote]
    cases e₁ : denoteArgs vs₁ vs <;> cases e₂ : denoteArgs vs₂ vs <;>
      rw [e₁, e₂] at hr <;> simp only [ORel] at hr ⊢
    · exact .hlt
    · exact .ret hr
  | .exit f args, _, _, vs₁, vs₂, _, _, hvs, _ => by
    have hr := denoteArgs_rel hvs args
    simp only [denote]
    cases e₁ : denoteArgs vs₁ args <;> cases e₂ : denoteArgs vs₂ args <;>
      rw [e₁, e₂] at hr <;> simp only [ORel] at hr ⊢
    · exact .hlt
    · exact .exit f hr
  | .hlt, _, _, _, _, _, _, _, _ => .hlt
  | .group bodies k, _, _, _, _, _, _, hvs, hls =>
    .group
      (fun Js₁ Js₂ => denoteB_wf bodies hvs (ctxRel_pushTup Js₁ Js₂ hls))
      (fun Js₁ Js₂ => denote_wf k hvs (ctxRel_pushTup Js₁ Js₂ hls))

/-- Every denotation of a `TBlocks` across related contexts is `WfB`-related. -/
theorem denoteB_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) → {G : Ctx V₁ V₂} → {D : Ctx L₁ L₂} →
    {vs₁ : List ((t : Ty) × V₁ t)} → {vs₂ : List ((t : Ty) × V₂ t)} →
    {ls₁ : List ((ts : List Ty) × L₁ ts)} → {ls₂ : List ((ts : List Ty) × L₂ ts)} →
    CtxRel G vs₁ vs₂ → CtxRel D ls₁ ls₂ →
    WfB G D (denoteB V₁ L₁ tb vs₁ ls₁) (denoteB V₂ L₂ tb vs₂ ls₂)
  | _, .nil, _, _, _, _, _, _, _, _ => .nil
  | _, .cons b bs, _, _, _, _, _, _, hvs, hls =>
    .cons (fun xs₁ xs₂ => denote_wf b (ctxRel_pushTup xs₁ xs₂ hvs) hls) (denoteB_wf bs hvs hls)
end

/-- A closed function equal to the denotation of some `TFlat rs` is well-formed. -/
theorem Func.wf_of_denote {as rs : List Ty} {f : Func as rs} (tf : TFlat rs)
    (h : f = fun V L xs => denote V L tf (pushTup xs []) []) : Func.Wf f := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  have h₁ : f V₁ L₁ xs₁ = denote V₁ L₁ tf (pushTup xs₁ []) [] :=
    congrFun (congrFun (congrFun h V₁) L₁) xs₁
  have h₂ : f V₂ L₂ xs₂ = denote V₂ L₂ tf (pushTup xs₂ []) [] :=
    congrFun (congrFun (congrFun h V₂) L₂) xs₂
  rw [h₁, h₂]
  exact denote_wf tf
    ((ctxRel_pushTup xs₁ xs₂ (.nil (G := []))).mono fun _ hp => by simpa using hp) .nil

/-- A closed function equal to the denotation of its own `toTFlat` reification is well-formed. -/
theorem Func.wf_of_reify {as rs : List Ty} {f : Func as rs}
    (h : f = fun V L xs => denote V L (toTFlat (f K KL (Tup.levels as 0)) as.length 0)
      (pushTup xs []) []) : Func.Wf f :=
  Func.wf_of_denote (toTFlat (f K KL (Tup.levels as 0)) as.length 0) h

/-! ## Soundness of `wfCheck` (no `.hlt` fallback from bad lookups) -/

/-- Runtime context `vs` agrees in shape and types with `Γ`. -/
inductive CtxTypes {α : Type} {f : α → Type} : List α → List ((a : α) × f a) → Prop
  | nil : CtxTypes [] []
  | cons {a : α} {Γ : List α} {v : f a} {vs : List ((a : α) × f a)} :
      CtxTypes Γ vs → CtxTypes (a :: Γ) (⟨a, v⟩ :: vs)

theorem CtxTypes.push {α : Type} {f : α → Type} :
    {as : List α} → (xs : Tup f as) → {Γ : List α} → {vs : List ((a : α) × f a)} →
    CtxTypes Γ vs → CtxTypes (pushTypes as Γ) (pushTup xs vs)
  | [], (), _, _, h => h
  | _ :: _, (_, xs), _, _, h => CtxTypes.push xs (.cons h)

private theorem castTy_self {V : Ty → Type} : ∀ (t : Ty) (v : V t), (castTy t t v).isSome = true
  | .bool, _ => rfl
  | .bits n, _ => by simp [castTy]
  | .float f, _ => by simp [castTy]
  | .pair a b, v => by
    simp only [castTy]
    cases h1 : tyDecEq a a with
    | isFalse hne => exact absurd rfl hne
    | isTrue _ =>
      cases h2 : tyDecEq b b with
      | isFalse hne => exact absurd rfl hne
      | isTrue _ => rfl

theorem lookupV_isSome_of_check {V : Ty → Type} :
    {Γ : List Ty} → {vs : List ((t : Ty) × V t)} → CtxTypes Γ vs →
    ∀ {t : Ty} {idx : Nat},
    (match listGet? Γ idx with
     | some t' => match tyDecEq t' t with | isTrue _ => true | isFalse _ => false
     | none => false) = true →
    (lookupV vs t idx).isSome = true
  | [], [], .nil, _, idx, h => by cases idx <;> simp [listGet?] at h
  | t' :: _, ⟨_, v⟩ :: _, .cons _, t, 0, h => by
    simp only [listGet?] at h
    cases hdec : tyDecEq t' t with
    | isFalse _ => simp [hdec] at h
    | isTrue heq => subst heq; simpa [lookupV, listGet?] using castTy_self t' v
  | _ :: _, _ :: _, .cons hrest, t, idx + 1, h => by
    simpa [lookupV, listGet?] using lookupV_isSome_of_check hrest h

theorem lookupL_isSome_of_check {L : List Ty → Type} :
    {Δ : List (List Ty)} → {ls : List ((ts : List Ty) × L ts)} → CtxTypes Δ ls →
    ∀ {ts : List Ty} {idx : Nat},
    (match listGet? Δ idx with
     | some ts' => match listTyDecEq ts' ts with | isTrue _ => true | isFalse _ => false
     | none => false) = true →
    (lookupL ls ts idx).isSome = true
  | [], [], .nil, _, idx, h => by cases idx <;> simp [listGet?] at h
  | ts' :: _, ⟨_, l⟩ :: _, .cons _, ts, 0, h => by
    simp only [listGet?] at h
    cases hdec : listTyDecEq ts' ts with
    | isFalse _ => simp [hdec] at h
    | isTrue heq =>
      subst heq
      simp only [lookupL, listGet?, castListTy]
      cases h2 : listTyDecEq ts' ts' with
      | isTrue _ => rfl
      | isFalse hne => exact absurd rfl hne
  | _ :: _, _ :: _, .cons hrest, ts, idx + 1, h => by
    simpa [lookupL, listGet?] using lookupL_isSome_of_check hrest h

theorem denoteArg_isSome_of_checkArg {V : Ty → Type} {Γ : List Ty} {vs : List ((t : Ty) × V t)}
    (hctx : CtxTypes Γ vs) {t : Ty} {a : Arg K t} (h : checkArg Γ t a = true) :
    (denoteArg vs a).isSome = true := by
  cases a with
  | var idx =>
    have hl := lookupV_isSome_of_check hctx h
    rcases Option.isSome_iff_exists.1 hl with ⟨v, hv⟩
    simp [denoteArg, hv]
  | imm c => simp [denoteArg]

theorem denoteArgs_isSome_of_checkArgs {V : Ty → Type} {Γ : List Ty} {vs : List ((t : Ty) × V t)}
    (hctx : CtxTypes Γ vs) :
    {ts : List Ty} → {as : Tup (Arg K) ts} → checkArgs Γ as = true →
    (denoteArgs vs as).isSome = true
  | [], (), _ => rfl
  | _ :: _, (a, as), h => by
    simp only [checkArgs, Bool.and_eq_true] at h
    have ha := denoteArg_isSome_of_checkArg hctx h.1
    have has := denoteArgs_isSome_of_checkArgs hctx h.2
    rcases Option.isSome_iff_exists.1 ha with ⟨a', ha'⟩
    rcases Option.isSome_iff_exists.1 has with ⟨as', has'⟩
    simp [denoteArgs, ha', has']

mutual
/-- Structural predicate stating that an expression contains no `.hlt` node. -/
inductive Expr.NoHlt {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Expr V L rs → Prop
  | let_ {ts op k} : (∀ xs, Expr.NoHlt (k xs)) → Expr.NoHlt (.let_ (ts := ts) op k)
  | load {t a k} : (∀ v, Expr.NoHlt (k v)) → Expr.NoHlt (.load t a k)
  | store {t v a k} : Expr.NoHlt k → Expr.NoHlt (.store (t := t) v a k)
  | call {f as bs args k} : (∀ xs, Expr.NoHlt (k xs)) →
      Expr.NoHlt (.call f (as := as) (bs := bs) args k)
  | jnz {c t e} : Expr.NoHlt t → Expr.NoHlt e → Expr.NoHlt (.jnz c t e)
  | jump {ts j args} : Expr.NoHlt (.jump (ts := ts) j args)
  | ret {vs} : Expr.NoHlt (.ret vs)
  | exit {f as args} : Expr.NoHlt (.exit f (as := as) args)
  | group {sig bodies k} : (∀ Js, Blocks.NoHlt (bodies Js)) → (∀ Js, Expr.NoHlt (k Js)) →
      Expr.NoHlt (.group (sig := sig) bodies k)

/-- Structural predicate stating that a block list contains no `.hlt` node. -/
inductive Blocks.NoHlt {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → Blocks V L rs sig → Prop
  | nil : Blocks.NoHlt .nil
  | cons {ts sig b bs} : (∀ xs, Expr.NoHlt (b xs)) → Blocks.NoHlt bs →
      Blocks.NoHlt (.cons (ts := ts) (sig := sig) b bs)
end

mutual
/-- If `tf.wfCheck Γ Δ = true` and `tf.noHlt = true`, then `denote` never triggers `.hlt` fallback. -/
theorem denote_noHlt_of_wfCheck {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × V t)} → {ls : List ((ts : List Ty) × L ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → tf.wfCheck Γ Δ = true → tf.noHlt = true →
    Expr.NoHlt (denote V L tf vs ls)
  | .let_ op k, _, _, vs, ls, hΓ, hΔ, hwf, hno => by
    simp only [TFlat.wfCheck, Bool.and_eq_true] at hwf
    simp only [TFlat.noHlt] at hno
    rcases Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1) with ⟨args', ha⟩
    simp only [denote, ha]
    exact .let_ fun xs => denote_noHlt_of_wfCheck k (CtxTypes.push xs hΓ) hΔ hwf.2 hno
  | .load t a k, _, _, vs, ls, hΓ, hΔ, hwf, hno => by
    simp only [TFlat.wfCheck, Bool.and_eq_true] at hwf
    simp only [TFlat.noHlt] at hno
    rcases Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1) with ⟨a', ha⟩
    simp only [denote, ha]
    exact .load fun v => denote_noHlt_of_wfCheck k (.cons hΓ) hΔ hwf.2 hno
  | .store v a k, _, _, vs, ls, hΓ, hΔ, hwf, hno => by
    simp only [TFlat.wfCheck, Bool.and_eq_true] at hwf
    simp only [TFlat.noHlt] at hno
    rcases Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1) with ⟨v', hv⟩
    rcases Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.2) with ⟨a', ha⟩
    simp only [denote, hv, ha]
    exact .store (denote_noHlt_of_wfCheck k hΓ hΔ hwf.2 hno)
  | .call f bs args k, _, _, vs, ls, hΓ, hΔ, hwf, hno => by
    simp only [TFlat.wfCheck, Bool.and_eq_true] at hwf
    simp only [TFlat.noHlt] at hno
    rcases Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1) with ⟨args', ha⟩
    simp only [denote, ha]
    exact .call fun xs => denote_noHlt_of_wfCheck k (CtxTypes.push xs hΓ) hΔ hwf.2 hno
  | .jnz c t e, _, _, vs, ls, hΓ, hΔ, hwf, hno => by
    simp only [TFlat.wfCheck, Bool.and_eq_true] at hwf
    simp only [TFlat.noHlt, Bool.and_eq_true] at hno
    rcases Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1) with ⟨c', hc⟩
    simp only [denote, hc]
    exact .jnz (denote_noHlt_of_wfCheck t hΓ hΔ hwf.1.2 hno.1)
      (denote_noHlt_of_wfCheck e hΓ hΔ hwf.2 hno.2)
  | .jump (ts := ts) j args, _, _, vs, ls, hΓ, hΔ, hwf, _ => by
    simp only [TFlat.wfCheck, Bool.and_eq_true] at hwf
    rcases Option.isSome_iff_exists.1 (lookupL_isSome_of_check hΔ hwf.1) with ⟨j', hj⟩
    rcases Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.2) with ⟨args', ha⟩
    simp only [denote, hj, ha]
    exact .jump
  | .ret vs', _, _, vs, _, hΓ, _, hwf, _ => by
    simp only [TFlat.wfCheck] at hwf
    rcases Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf) with ⟨vs'', hvs⟩
    simp only [denote, hvs]
    exact .ret
  | .exit f args, _, _, vs, _, hΓ, _, hwf, _ => by
    simp only [TFlat.wfCheck] at hwf
    rcases Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf) with ⟨args', ha⟩
    simp only [denote, ha]
    exact .exit
  | .hlt, _, _, _, _, _, _, _, hno => by simp [TFlat.noHlt] at hno
  | .group bodies k, _, _, vs, ls, hΓ, hΔ, hwf, hno => by
    simp only [TFlat.wfCheck, Bool.and_eq_true] at hwf
    simp only [TFlat.noHlt, Bool.and_eq_true] at hno
    simp only [denote]
    exact .group
      (fun Js => denoteB_noHlt_of_wfCheck bodies hΓ (CtxTypes.push Js hΔ) hwf.1 hno.1)
      (fun Js => denote_noHlt_of_wfCheck k hΓ (CtxTypes.push Js hΔ) hwf.2 hno.2)

/-- Block-list companion of `denote_noHlt_of_wfCheck`. -/
theorem denoteB_noHlt_of_wfCheck {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × V t)} → {ls : List ((ts : List Ty) × L ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → tb.wfCheck Γ Δ = true → tb.noHlt = true →
    Blocks.NoHlt (denoteB V L tb vs ls)
  | _, .nil, _, _, _, _, _, _, _, _ => .nil
  | _, .cons b bs, _, _, vs, ls, hΓ, hΔ, hwf, hno => by
    simp only [TBlocks.wfCheck, Bool.and_eq_true] at hwf
    simp only [TBlocks.noHlt, Bool.and_eq_true] at hno
    exact .cons (fun xs => denote_noHlt_of_wfCheck b (CtxTypes.push xs hΓ) hΔ hwf.1 hno.1)
      (denoteB_noHlt_of_wfCheck bs hΓ hΔ hwf.2 hno.2)
end

/-- For a closed `f` whose reification passes `checkTFlat` and has no explicit `.hlt`, `denote`
produces an expression with no `.hlt` fallback at every instantiation. -/
theorem Func.denote_noHlt_of_check {as rs : List Ty} (f : Func as rs)
    (hchk : f.checkTFlat = true)
    (hno : (toTFlat (f K KL (Tup.levels as 0)) as.length 0).noHlt = true)
    (V : Ty → Type) (L : List Ty → Type) (xs : Tup V as) :
    Expr.NoHlt (denote V L (toTFlat (f K KL (Tup.levels as 0)) as.length 0) (pushTup xs []) []) :=
  denote_noHlt_of_wfCheck _ (CtxTypes.push xs .nil) .nil hchk hno

/-! ## Kernel-only `rfl` and `t_wf_reify` tactics -/

open Lean Elab Tactic Meta in
/-- Close `lhs = rhs` with `Eq.refl lhs`, checked solely by the kernel (skipping elaborator
`isDefEq`, which does not scale cleanly and hits recursion limits on large PHOAS terms).

Callers should prefer `t_kernel_rfl` / `t_wf_reify` over plain `Func.wf_of_reify rfl`.
Note: because `t_kernel_rfl` delegates the equality check solely to the Lean kernel without
running elaborator `isDefEq`, any genuine mismatch is reported by the kernel at declaration
type-checking time (`(kernel) declaration type mismatch`). -/
elab "t_kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let some (α, lhs, rhs) := tgt.eq?
    | throwError "t_kernel_rfl: goal is not an equality{indentExpr tgt}"
  if lhs.hasExprMVar || rhs.hasExprMVar then
    throwError "t_kernel_rfl: goal still contains metavariables{indentExpr tgt}"
  let u ← getLevel α
  goal.assign (mkApp2 (mkConst ``Eq.refl [u]) α lhs)
  replaceMainGoal []

/-- Prove `Func.Wf f` for a closed concrete function by reification + kernel `rfl`.
Callers should use `t_wf_reify` rather than `Func.wf_of_reify rfl`, which does not scale
cleanly in the elaborator on large PHOAS terms. -/
macro "t_wf_reify" : tactic => `(tactic| (refine Func.wf_of_reify ?_; t_kernel_rfl))

/-! ## Reification-denotation round-trip (`reifyFunc`, `denoteFunc`, `Func.renorm_spec`) -/

/-- Reify a closed function `f` into its first-order de Bruijn `TFlat` representation. -/
def reifyFunc {as rs : List Ty} (f : Func as rs) : TFlat rs :=
  toTFlat (f K KL (Tup.levels as 0)) as.length 0

/-- Denote a first-order `TFlat` term back into a closed PHOAS `Func`. -/
def denoteFunc {as rs : List Ty} (tf : TFlat rs) : Func as rs :=
  fun V L xs => denote V L tf (pushTup xs []) []

private theorem castTy_self_eq {V : Ty → Type} : ∀ (t : Ty) (v : V t), castTy t t v = some v
  | .bool, _ => rfl
  | .bits _, _ => by simp [castTy]
  | .float _, _ => by simp [castTy]
  | .pair a b, v => by
    simp only [castTy]
    cases h1 : tyDecEq a a with
    | isFalse hne => exact absurd rfl hne
    | isTrue heq1 =>
      cases h2 : tyDecEq b b with
      | isFalse hne => exact absurd rfl hne
      | isTrue heq2 =>
        have h1' : heq1 = rfl := rfl
        have h2' : heq2 = rfl := rfl
        rw [h1', h2']

private theorem castListTy_self_eq {L : List Ty → Type} (ts : List Ty) (l : L ts) :
    castListTy ts ts l = some l := by
  simp only [castListTy]
  cases h : listTyDecEq ts ts with
  | isFalse hne => exact absurd rfl hne
  | isTrue heq =>
    have h' : heq = rfl := rfl
    rw [h']

private theorem lookupV_head {V : Ty → Type} (t : Ty) (v : V t) (vs : List ((u : Ty) × V u)) :
    lookupV (⟨t, v⟩ :: vs) t 0 = some v := by
  simpa [lookupV, listGet?] using castTy_self_eq t v

private theorem lookupL_head {L : List Ty → Type} (ts : List Ty) (l : L ts)
    (ls : List ((us : List Ty) × L us)) :
    lookupL (⟨ts, l⟩ :: ls) ts 0 = some l := by
  simpa [lookupL, listGet?] using castListTy_self_eq ts l

theorem pushTup_length {α : Type} {f : α → Type} :
    {as : List α} → (xs : Tup f as) → (acc : List ((a : α) × f a)) →
    (pushTup xs acc).length = acc.length + as.length
  | [], (), acc => rfl
  | _ :: as, (_, xs), acc => by
    simp only [pushTup, List.length_cons]
    rw [pushTup_length xs _]
    simp only [List.length_cons]
    omega

/-- De Bruijn level context `G` matches the tail-indexed runtime environment `vs`. -/
def CtxMatch {α : Type} {f : α → Type}
    (look : List ((a : α) × f a) → (a : α) → Nat → Option (f a))
    (G : Ctx (fun _ => Nat) f) (vs : List ((a : α) × f a)) : Prop :=
  ∀ p ∈ G, p.2.1 < vs.length ∧ look vs p.1 (vs.length - 1 - p.2.1) = some p.2.2

theorem CtxMatch.mono {α : Type} {f : α → Type}
    {look : List ((a : α) × f a) → (a : α) → Nat → Option (f a)}
    {G₁ G₂ : Ctx (fun _ => Nat) f} {vs : List ((a : α) × f a)}
    (hsub : ∀ p ∈ G₂, p ∈ G₁) (h : CtxMatch look G₁ vs) : CtxMatch look G₂ vs :=
  fun p hp => h p (hsub p hp)

theorem CtxMatch.cons {α : Type} {f : α → Type}
    {look : List ((a : α) × f a) → (a : α) → Nat → Option (f a)}
    (hlook_head : ∀ a (x : f a) vs, look (⟨a, x⟩ :: vs) a 0 = some x)
    (hlook_tail : ∀ a (x : f a) vs b idx, look (⟨a, x⟩ :: vs) b (idx + 1) = look vs b idx)
    {G : Ctx (fun _ => Nat) f} {vs : List ((a : α) × f a)}
    (hvs : CtxMatch look G vs) (a : α) (x : f a) :
    CtxMatch look (⟨a, vs.length, x⟩ :: G) (⟨a, x⟩ :: vs) := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · refine ⟨Nat.lt_succ_self _, ?_⟩
    simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_self]
    exact hlook_head a x vs
  · obtain ⟨hlt, hl⟩ := hvs p hp
    dsimp only at hlt
    refine ⟨Nat.lt_succ_of_lt hlt, ?_⟩
    have hidx : (⟨a, x⟩ :: vs).length - 1 - p.2.1 = (vs.length - 1 - p.2.1) + 1 := by
      rw [List.length_cons]
      omega
    rw [hidx, hlook_tail]
    exact hl

theorem ctxMatch_pushTup {α : Type} {f : α → Type}
    {look : List ((a : α) × f a) → (a : α) → Nat → Option (f a)}
    (hlook_head : ∀ a (x : f a) vs, look (⟨a, x⟩ :: vs) a 0 = some x)
    (hlook_tail : ∀ a (x : f a) vs b idx, look (⟨a, x⟩ :: vs) b (idx + 1) = look vs b idx) :
    {as : List α} → (xs : Tup f as) → {G : Ctx (fun _ => Nat) f} →
    {vs : List ((a : α) × f a)} → CtxMatch look G vs →
    CtxMatch look (Tup.zip (Tup.levels as vs.length) xs ++ G) (pushTup xs vs)
  | [], (), _, _, hvs => by
    simp only [Tup.zip, List.nil_append]
    exact hvs
  | a :: as, (x, xs), G, vs, hvs => by
    have h1 := CtxMatch.cons hlook_head hlook_tail hvs a x
    have h2 := ctxMatch_pushTup hlook_head hlook_tail xs h1
    simp only [List.length_cons] at h2
    refine h2.mono fun p hp => ?_
    simp only [Tup.levels, Tup.zip, List.cons_append, List.mem_append, List.mem_cons] at hp ⊢
    rcases hp with rfl | hp | hp
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl hp
    · exact Or.inr (Or.inr hp)

theorem ctxMatch_pushTupV {V : Ty → Type} {G : Ctx K V} {vs : List ((t : Ty) × V t)}
    (hvs : CtxMatch lookupV G vs) {as : List Ty} (xs : Tup V as) :
    CtxMatch lookupV (Tup.zip (Tup.levels as vs.length) xs ++ G) (pushTup xs vs) :=
  ctxMatch_pushTup lookupV_head (fun _ _ _ _ _ => rfl) xs hvs

theorem ctxMatch_pushTupL {L : List Ty → Type} {D : Ctx KL L} {ls : List ((ts : List Ty) × L ts)}
    (hls : CtxMatch lookupL D ls) {sig : List (List Ty)} (Js : Tup L sig) :
    CtxMatch lookupL (Tup.zip (Tup.levels sig ls.length) Js ++ D) (pushTup Js ls) :=
  ctxMatch_pushTup lookupL_head (fun _ _ _ _ _ => rfl) Js hls

theorem denoteArg_idxArg {V : Ty → Type} {G : Ctx K V} {vs : List ((t : Ty) × V t)}
    (hvs : CtxMatch lookupV G vs) {t : Ty} {a₁ : Arg K t} {a₂ : Arg V t}
    (ha : ArgRel G t a₁ a₂) :
    denoteArg vs (idxArg vs.length a₁) = some a₂ := by
  cases ha with
  | @var lvl v hm =>
    obtain ⟨hlt, hl⟩ := hvs _ hm
    simp only [idxArg, hlt, ↓reduceIte, denoteArg, hl]
  | imm c => rfl

theorem denoteArgs_idxArgs {V : Ty → Type} {G : Ctx K V} {vs : List ((t : Ty) × V t)}
    (hvs : CtxMatch lookupV G vs) :
    {ts : List Ty} → {as₁ : Tup (Arg K) ts} → {as₂ : Tup (Arg V) ts} →
    TRel (ArgRel G) as₁ as₂ →
    denoteArgs vs (idxArgs vs.length as₁) = some as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons h hs => by
    simp only [idxArgs, denoteArgs, denoteArg_idxArg hvs h, denoteArgs_idxArgs hvs hs]

theorem denoteB_toTBlocks_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (nv nl : Nat) (vs : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)) :
    {sig : List (List Ty)} → {ts : List Ty} →
    (bs : Blocks K KL rs sig) → (i : Member ts sig) → (xs : Tup V ts) →
    (denoteB V L (toTBlocks bs nv nl) vs ls).get i xs =
      denote V L (toTFlat (bs.get i (Tup.levels ts nv)) (nv + ts.length) nl) (pushTup xs vs) ls
  | _, _, .cons _ _, .here, _ => rfl
  | _, _, .cons _ bs, .there i, xs => denoteB_toTBlocks_get nv nl vs ls bs i xs

/-- Reification-denotation round-trip preserves `wp` identically under `Wf`. -/
theorem denote_wp_iff {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx K Val} {D : Ctx KL Cont}
    {e₁ : Expr K KL rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts)),
    CtxMatch lookupV G vs → CtxMatch lookupL D ls → ∀ m,
    wp Γ Q X (denote Val Cont (toTFlat e₁ vs.length ls.length) vs ls) m ↔ wp Γ Q X e₂ m := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro vs ls hvs hls m
    cases hop with
    | @mk _ _ code args₁ args₂ hargs =>
      have hda := denoteArgs_idxArgs hvs hargs
      simp only [toTFlat, denote, hda, wp]
      refine ⟨fun h => OpCode.wp_mono code _ (fun xs hxs => ?_) h,
              fun h => OpCode.wp_mono code _ (fun xs hxs => ?_) h⟩
      · have hk := (ih (Tup.levels ts vs.length) xs (pushTup xs vs) ls
          (ctxMatch_pushTupV hvs xs) hls m).1
        rw [pushTup_length xs vs] at hk
        exact hk hxs
      · have hk := (ih (Tup.levels ts vs.length) xs (pushTup xs vs) ls
          (ctxMatch_pushTupV hvs xs) hls m).2
        rw [pushTup_length xs vs] at hk
        exact hk hxs
  | load t ha _ ih =>
    intro vs ls hvs hls m
    have hda := denoteArg_idxArg hvs ha
    simp only [toTFlat, denote, hda, wp]
    constructor
    · rintro ⟨v, hv, hk⟩
      have h1 := CtxMatch.cons lookupV_head (fun _ _ _ _ _ => rfl) hvs t v
      exact ⟨v, hv, (ih vs.length v (⟨t, v⟩ :: vs) ls h1 hls m).1 hk⟩
    · rintro ⟨v, hv, hk⟩
      have h1 := CtxMatch.cons lookupV_head (fun _ _ _ _ _ => rfl) hvs t v
      exact ⟨v, hv, (ih vs.length v (⟨t, v⟩ :: vs) ls h1 hls m).2 hk⟩
  | store hv ha _ ih =>
    intro vs ls hvs hls m
    have hdv := denoteArg_idxArg hvs hv
    have hda := denoteArg_idxArg hvs ha
    simp only [toTFlat, denote, hdv, hda, wp]
    exact and_congr_right fun _ => ih vs ls hvs hls _
  | call f hargs _ ih =>
    intro vs ls hvs hls m
    have hda := denoteArgs_idxArgs hvs hargs
    simp only [toTFlat, denote, hda, wp]
    constructor
    · rintro ⟨P, E, hΓ, hP, hE⟩
      refine ⟨P, E, hΓ, fun r m' hr => ?_, hE⟩
      have hk := (ih (Tup.levels _ vs.length) r (pushTup r vs) ls
        (ctxMatch_pushTupV hvs r) hls m').1
      rw [pushTup_length r vs] at hk
      exact hk (hP r m' hr)
    · rintro ⟨P, E, hΓ, hP, hE⟩
      refine ⟨P, E, hΓ, fun r m' hr => ?_, hE⟩
      have hk := (ih (Tup.levels _ vs.length) r (pushTup r vs) ls
        (ctxMatch_pushTupV hvs r) hls m').2
      rw [pushTup_length r vs] at hk
      exact hk (hP r m' hr)
  | jnz hc _ _ iht ihe =>
    intro vs ls hvs hls m
    have hdc := denoteArg_idxArg hvs hc
    simp only [toTFlat, denote, hdc, wp]
    exact and_congr
      (imp_congr_right fun _ => iht vs ls hvs hls m)
      (imp_congr_right fun _ => ihe vs ls hvs hls m)
  | @jump G D ts j₁ j₂ args₁ args₂ hj hargs =>
    intro vs ls hvs hls m
    obtain ⟨hlt, hl⟩ := hls _ hj
    have hda := denoteArgs_idxArgs hvs hargs
    simp only [toTFlat, hlt, ↓reduceIte, denote, hl, hda]
  | ret hvs' =>
    intro vs ls hvs _ _
    have hda := denoteArgs_idxArgs hvs hvs'
    simp only [toTFlat, denote, hda]
  | exit f hargs =>
    intro vs ls hvs _ _
    have hda := denoteArgs_idxArgs hvs hargs
    simp only [toTFlat, denote, hda]
  | hlt =>
    intro _ _ _ _ _
    rfl
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro vs ls hvs hls m
    simp only [toTFlat, denote, wp]
    refine forall_congr' fun Js => ?_
    have hcl : Closed Γ Q X
        (denoteB Val Cont
          (toTBlocks (b₁ (Tup.levels sig ls.length)) vs.length (ls.length + sig.length))
          vs (pushTup Js ls)) Js ↔
        Closed Γ Q X (b₂ Js) Js := by
      rw [closed_iff, closed_iff]
      refine forall₂_congr fun ts i => forall₂_congr fun xs m' => ?_
      rw [denoteB_toTBlocks_get]
      have hbw := ihb (Tup.levels sig ls.length) Js i (Tup.levels ts vs.length) xs
        (pushTup xs vs) (pushTup Js ls) (ctxMatch_pushTupV hvs xs)
        (ctxMatch_pushTupL hls Js) m'
      rw [pushTup_length xs vs, pushTup_length Js ls] at hbw
      exact imp_congr_left hbw
    have hkw := ihk (Tup.levels sig ls.length) Js vs (pushTup Js ls) hvs
      (ctxMatch_pushTupL hls Js) m
    rw [pushTup_length Js ls] at hkw
    exact imp_congr hcl hkw

/-- Forward direction of `denote_wp_iff`: source `wp` implies reified-and-denoted `wp`. -/
theorem denote_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx K Val} {D : Ctx KL Cont}
    {e₁ : Expr K KL rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂)
    (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts))
    (hvs : CtxMatch lookupV G vs) (hls : CtxMatch lookupL D ls) {m : Mem 64}
    (h : wp Γ Q X e₂ m) :
    wp Γ Q X (denote Val Cont (toTFlat e₁ vs.length ls.length) vs ls) m :=
  (denote_wp_iff hwf vs ls hvs hls m).2 h

/-- Alias for `denote_wp` matching renormalization naming. -/
theorem renorm_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx K Val} {D : Ctx KL Cont}
    {e₁ : Expr K KL rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂)
    (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts))
    (hvs : CtxMatch lookupV G vs) (hls : CtxMatch lookupL D ls) {m : Mem 64}
    (h : wp Γ Q X e₂ m) :
    wp Γ Q X (denote Val Cont (toTFlat e₁ vs.length ls.length) vs ls) m :=
  denote_wp hwf vs ls hvs hls h

/-- Reification-denotation round-trip of any closed function is well-formed. -/
theorem Func.renorm_wf {as rs : List Ty} (f : Func as rs) :
    (denoteFunc (as := as) (reifyFunc f)).Wf :=
  Func.wf_of_denote (reifyFunc f) rfl

/-- Reification-denotation round-trip preserves `Func.wp` for any well-formed function. -/
theorem Func.renorm_spec {as rs : List Ty} {Γ : Env} {f : Func as rs} (h : f.Wf)
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (hw : Func.wp Γ f xs m Q X) :
    Func.wp Γ (denoteFunc (reifyFunc f)) xs m Q X := by
  have hwf := h K Val KL Cont (Tup.levels as 0) xs
  have hvs : CtxMatch lookupV (Tup.zip (Tup.levels as 0) xs) (pushTup xs []) := by
    simpa [List.append_nil] using
      (ctxMatch_pushTupV (G := ([] : Ctx K Val)) (vs := []) (fun _ hp => nomatch hp) xs)
  have hls : CtxMatch lookupL ([] : Ctx KL Cont) [] := fun _ hp => nomatch hp
  have hd := denote_wp hwf (pushTup xs []) [] hvs hls hw
  simpa [Func.wp, denoteFunc, reifyFunc, pushTup_length] using hd

end LeanQbe.T
