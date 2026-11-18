module

public import LeanQbe.T.Flat
public import LeanQbe.T.WfLemmas
public meta import Lean.Elab.Tactic

/-!
# Soundness of `TFlat` reification: `denote_wf` and `Func.wf_of_reify`

* `denote_wf` / `denoteB_wf`: for every `tf : TFlat rs` and any two instantiations
  `(V₁, L₁)` and `(V₂, L₂)` with related contexts `CtxRel G vs₁ vs₂` and `CtxRel D ls₁ ls₂`,
  `denote V₁ L₁ tf vs₁ ls₁` and `denote V₂ L₂ tf vs₂ ls₂` are `Wf G D`-related.
* `Func.wf_of_denote` / `Func.wf_of_reify`: a closed function equal to the denotation of its
  own reification (`toTFlat`) is `Func.Wf`.
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
`isDefEq`, which is much slower and hits recursion limits on large PHOAS terms). -/
elab "t_kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let some (α, lhs, _) := tgt.eq?
    | throwError "t_kernel_rfl: goal is not an equality{indentExpr tgt}"
  let u ← getLevel α
  goal.assign (mkApp2 (mkConst ``Eq.refl [u]) α lhs)
  replaceMainGoal []

/-- Prove `Func.Wf f` for a closed concrete function by reification + kernel `rfl`. -/
macro "t_wf_reify" : tactic => `(tactic| (refine Func.wf_of_reify ?_; t_kernel_rfl))

end LeanQbe.T
