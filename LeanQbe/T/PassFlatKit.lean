module

public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.GroupLfpLemmas
public import LeanQbe.T.Module
public import LeanQbe.T.OptUtilLemmas
public import LeanQbe.T.PassEnvKit

/-!
# Shared Flat-IR, `CallsOk`, and Context-Predicate Kit (`PassFlatKit`)

Factorizes proof boilerplate shared across mid-end flat/reified passes (`LoopRotateLemmas`,
`ZeroPeelLemmas`, `ZeroPeelLemmas1`, `LicmRoLemmas`, `LicmLemmas`):

1. **`PassEnvKit` / `CtxPred` combinators**: `DiagCtx`, `ArgPred` / `ArgsPred`, `OptDeadCtx`, and
   `SomeValCtx` for masked/optional-binder and diagonal contexts.
2. **`TFlatSimpKit`**: `castTy_self`, `castTy_some_eq`, `pushTup` / `pushTypes` / `TBlocks.get`
   identities, generic `RelCtxMatch` + `denote_wf_src` transfer, and `wp_iff_of_diag_eq` via
   `GroupLfpLemmas.wp_label_mono`.
3. **`CallsOkCombinators`**: `callsOkTF`, `callsOkBs`, `callsOkTF_denote`, `callsOkTF_of_denote`,
   `callsOkTF_toTFlat`, `toTFlat_wfCheck`, `Func.renorm_callsOk`, `denoteFunc_callsOk_iff`, and
   `map_eq_append_split`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

namespace PassFlatKit

/-! ## 1. Context-predicate and optional-binder combinators -/

/-- Diagonal context predicate: every entry's left and right witnesses coincide. -/
abbrev DiagCtx {α : Type} {V : α → Type} (G : Ctx V V) : Prop :=
  CtxPred (fun _ v₁ v₂ => v₁ = v₂) G

namespace DiagCtx

theorem nil {α : Type} {V : α → Type} : DiagCtx (V := V) ([] : Ctx V V) :=
  CtxPred.nil _

theorem cons {α : Type} {V : α → Type} {G : Ctx V V} {a : α} {v : V a}
    (hG : DiagCtx G) : DiagCtx (⟨a, (v, v)⟩ :: G) :=
  CtxPred.cons rfl hG

theorem append {α : Type} {V : α → Type} {G₁ G₂ : Ctx V V}
    (h₁ : DiagCtx G₁) (h₂ : DiagCtx G₂) : DiagCtx (G₁ ++ G₂) :=
  CtxPred.append h₁ h₂

theorem zip_self {α : Type} {V : α → Type} :
    {ts : List α} → (xs : Tup V ts) → DiagCtx (Tup.zip xs xs)
  | [], () => nil
  | _ :: _, (_, xs) => cons (zip_self xs)

theorem mem_eq {α : Type} {V : α → Type} {G : Ctx V V} (hG : DiagCtx G)
    {a : α} {v₁ v₂ : V a} (hm : ⟨a, (v₁, v₂)⟩ ∈ G) : v₁ = v₂ :=
  hG ⟨a, (v₁, v₂)⟩ hm

theorem argRel_eq {V : Ty → Type} {G : Ctx V V} (hG : DiagCtx G)
    {t : Ty} {a₁ a₂ : Arg V t} : ArgRel G t a₁ a₂ → a₁ = a₂
  | .var hm => congrArg Arg.var (hG.mem_eq hm)
  | .imm _ => rfl

theorem trel_eq {V : Ty → Type} {G : Ctx V V} (hG : DiagCtx G) :
    {ts : List Ty} → {as₁ as₂ : Tup (Arg V) ts} → TRel (ArgRel G) as₁ as₂ → as₁ = as₂
  | [], (), (), _ => rfl
  | _ :: _, (_, _), (_, _), .cons ha has =>
    congr (congrArg Prod.mk (hG.argRel_eq ha)) (hG.trel_eq has)

theorem opRel_eq {V : Ty → Type} {G : Ctx V V} (hG : DiagCtx G)
    {rs : List Ty} {op₁ op₂ : Op V rs} : OpRel G op₁ op₂ → op₁ = op₂
  | .mk _ hargs => by
    have := hG.trel_eq hargs
    cases op₁; cases op₂; cases this; rfl

end DiagCtx

/-- Pointwise relational lift of a variable predicate `P` to operands `Arg`. -/
@[expose] def ArgPred {V₁ V₂ : Ty → Type} (P : (t : Ty) → V₁ t → V₂ t → Prop)
    {t : Ty} : Arg V₁ t → Arg V₂ t → Prop
  | .var v₁, .var v₂ => P t v₁ v₂
  | .imm c₁, .imm c₂ => c₁ = c₂
  | _, _ => False

/-- Tuple-level lift of `ArgPred P`. -/
@[expose] def ArgsPred {V₁ V₂ : Ty → Type} (P : (t : Ty) → V₁ t → V₂ t → Prop) :
    {ts : List Ty} → Tup (Arg V₁) ts → Tup (Arg V₂) ts → Prop
  | [], (), () => True
  | _ :: _, (a₁, as₁), (a₂, as₂) => ArgPred P a₁ a₂ ∧ ArgsPred P as₁ as₂

theorem ctxPred_argRel_pred {V₁ V₂ : Ty → Type} {P : (t : Ty) → V₁ t → V₂ t → Prop}
    {G : Ctx V₁ V₂} (hG : CtxPred P G) {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} :
    ArgRel G t a₁ a₂ → ArgPred P a₁ a₂
  | .var hm => CtxPred.mem hG hm
  | .imm _ => rfl

theorem ctxPred_trel_pred {V₁ V₂ : Ty → Type} {P : (t : Ty) → V₁ t → V₂ t → Prop}
    {G : Ctx V₁ V₂} (hG : CtxPred P G) :
    {ts : List Ty} → {as₁ : Tup (Arg V₁) ts} → {as₂ : Tup (Arg V₂) ts} →
    TRel (ArgRel G) as₁ as₂ → ArgsPred P as₁ as₂
  | [], (), (), _ => trivial
  | _ :: _, (_, _), (_, _), .cons ha has => ⟨ctxPred_argRel_pred hG ha, ctxPred_trel_pred hG has⟩

/-- Context invariant ensuring `none`-bound binders never satisfy liveness predicate `D`. -/
@[expose] def OptDeadCtx (D : {t : Ty} → K t → Prop) {F : Ty → Type}
    (Gk : Ctx K (fun t => Option (F t))) : Prop :=
  CtxPred (fun _ k o => o = none → ¬ D k) Gk

namespace OptDeadCtx

theorem nil {D : {t : Ty} → K t → Prop} {F : Ty → Type} :
    OptDeadCtx D (F := F) [] :=
  CtxPred.nil _

theorem cons_some {D : {t : Ty} → K t → Prop} {F : Ty → Type}
    {Gk : Ctx K (fun t => Option (F t))} {t : Ty} {k : K t} {a : F t}
    (hG : OptDeadCtx D Gk) : OptDeadCtx D (⟨t, (k, some a)⟩ :: Gk) :=
  CtxPred.cons (fun h => by cases h) hG

theorem cons_none {D : {t : Ty} → K t → Prop} {F : Ty → Type}
    {Gk : Ctx K (fun t => Option (F t))} {t : Ty} {k : K t}
    (hk : ¬ D k) (hG : OptDeadCtx D Gk) : OptDeadCtx D (⟨t, (k, none)⟩ :: Gk) :=
  CtxPred.cons (fun _ => hk) hG

theorem mono {D₁ D₂ : {t : Ty} → K t → Prop} {F : Ty → Type}
    {Gk : Ctx K (fun t => Option (F t))}
    (himp : ∀ {t} {k : K t}, D₁ k → D₂ k) (hG : OptDeadCtx D₂ Gk) :
    OptDeadCtx D₁ Gk :=
  CtxPred.mono (fun h heq hd => h heq (himp hd)) hG

theorem of_in {D : {t : Ty} → K t → Prop} {F : Ty → Type}
    {Gk : Ctx K (fun t => Option (F t))} (hG : OptDeadCtx D Gk)
    {t : Ty} {k : K t} {o : Option (F t)}
    (hm : ⟨t, (k, o)⟩ ∈ Gk) (hd : D k) : ∃ a, o = some a := by
  cases o with
  | none => exact False.elim (CtxPred.mem hG hm rfl hd)
  | some a => exact ⟨a, rfl⟩

end OptDeadCtx

/-- Context invariant relating `some a` binders to target values `v` via `R`. -/
@[expose] def SomeValCtx {F V : Ty → Type} (R : (t : Ty) → F t → V t → Prop)
    (G : Ctx (fun t => Option (F t)) V) : Prop :=
  CtxPred (fun t o v => ∀ a, o = some a → R t a v) G

namespace SomeValCtx

theorem nil {F V : Ty → Type} {R : (t : Ty) → F t → V t → Prop} :
    SomeValCtx R ([] : Ctx (fun t => Option (F t)) V) :=
  CtxPred.nil _

theorem cons_some {F V : Ty → Type} {R : (t : Ty) → F t → V t → Prop}
    {G : Ctx (fun t => Option (F t)) V} {t : Ty} {a : F t} {v : V t}
    (hr : R t a v) (hG : SomeValCtx R G) :
    SomeValCtx R (⟨t, (some a, v)⟩ :: G) :=
  CtxPred.cons (fun _ h => by cases h; exact hr) hG

theorem cons_none {F V : Ty → Type} {R : (t : Ty) → F t → V t → Prop}
    {G : Ctx (fun t => Option (F t)) V} {t : Ty} {v : V t}
    (hG : SomeValCtx R G) : SomeValCtx R (⟨t, (none, v)⟩ :: G) :=
  CtxPred.cons (fun _ h => by cases h) hG

theorem append {F V : Ty → Type} {R : (t : Ty) → F t → V t → Prop}
    {G₁ G₂ : Ctx (fun t => Option (F t)) V}
    (h₁ : SomeValCtx R G₁) (h₂ : SomeValCtx R G₂) : SomeValCtx R (G₁ ++ G₂) :=
  CtxPred.append h₁ h₂

end SomeValCtx

/-! ## 2. `TFlatSimpKit`: casts, `pushTup`, `RelCtxMatch`, and `wp` equality -/

theorem castTy_self {f : Ty → Type} : (t : Ty) → (v : f t) → castTy t t v = some v
  | .bool, _ => rfl
  | .bits _, _ => dite_eq_left rfl
  | .float _, _ => dite_eq_left rfl
  | .pair a b, _ => by
    dsimp only [castTy]
    cases h1 : tyDecEq a a with
    | isFalse h => exact absurd rfl h
    | isTrue eq1 =>
      cases h2 : tyDecEq b b with
      | isFalse h => exact absurd rfl h
      | isTrue eq2 => cases eq1; cases eq2; rfl

theorem castTy_some_eq {f : Ty → Type} {t₁ t₂ : Ty} {v₁ : f t₁} {v₂ : f t₂}
    (h : castTy t₁ t₂ v₁ = some v₂) : ∃ eq : t₁ = t₂, eq ▸ v₁ = v₂ := by
  cases t₁ with
  | bool => cases t₂ with
    | bool => cases h; exact ⟨rfl, rfl⟩
    | bits _ | float _ | pair _ _ => simp [castTy] at h
  | bits m => cases t₂ with
    | bits n =>
      dsimp only [castTy] at h
      split at h
      · next eq => cases eq; exact ⟨rfl, Option.some.inj h⟩
      · cases h
    | bool | float _ | pair _ _ => simp [castTy] at h
  | float f₁ => cases t₂ with
    | float f₂ =>
      dsimp only [castTy] at h
      split at h
      · next eq => cases eq; exact ⟨rfl, Option.some.inj h⟩
      · cases h
    | bool | bits _ | pair _ _ => simp [castTy] at h
  | pair a₁ b₁ => cases t₂ with
    | pair a₂ b₂ =>
      dsimp only [castTy] at h
      cases h1 : tyDecEq a₁ a₂ with
      | isFalse _ => simp [h1] at h
      | isTrue eq1 =>
        cases h2 : tyDecEq b₁ b₂ with
        | isFalse _ => simp [h1, h2] at h
        | isTrue eq2 =>
          cases eq1; cases eq2
          simp [h1, h2] at h
          exact ⟨rfl, h⟩
    | bool | bits _ | float _ => simp [castTy] at h

theorem castListTy_self {f : List Ty → Type} (ts : List Ty) (v : f ts) :
    castListTy ts ts v = some v := by
  dsimp only [castListTy]
  cases h : listTyDecEq ts ts with
  | isFalse hne => exact absurd rfl hne
  | isTrue eq => cases eq; rfl

theorem listGet?_append_left {α : Type} :
    ∀ {xs ys : List α} {i : Nat}, i < xs.length → listGet? (xs ++ ys) i = listGet? xs i
  | _ :: _, _, 0, _ => rfl
  | _ :: xs, ys, i + 1, h =>
    listGet?_append_left (xs := xs) (ys := ys) (i := i) (Nat.lt_of_succ_lt_succ h)

theorem listGet?_append_right {α : Type} :
    ∀ (xs : List α) {ys : List α} (j : Nat), listGet? (xs ++ ys) (xs.length + j) = listGet? ys j
  | [], ys, j => by simp
  | _ :: xs, ys, j => by
    dsimp only [List.cons_append, List.length_cons]
    rw [Nat.succ_add]
    exact listGet?_append_right xs j

theorem pushTup_eq_append {α : Type} {f : α → Type} :
    {as : List α} → (xs : Tup f as) → (acc : List ((a : α) × f a)) →
      pushTup xs acc = pushTup xs [] ++ acc
  | [], (), _ => rfl
  | a :: as, (x, xs), acc => by
    rw [pushTup, pushTup]
    rw [pushTup_eq_append (as := as) xs (⟨a, x⟩ :: acc)]
    rw [pushTup_eq_append (as := as) xs [⟨a, x⟩], List.append_assoc]
    rfl

theorem pushTup_append {α : Type} {f : α → Type} {as : List α}
    (xs : Tup f as) (acc₁ acc₂ : List ((a : α) × f a)) :
    pushTup xs (acc₁ ++ acc₂) = pushTup xs acc₁ ++ acc₂ := by
  rw [pushTup_eq_append xs (acc₁ ++ acc₂), pushTup_eq_append xs acc₁, List.append_assoc]

theorem pushTypes_eq_append {α : Type} :
    ∀ (as acc : List α), pushTypes as acc = pushTypes as [] ++ acc
  | [], _ => rfl
  | a :: as, acc => by
    rw [pushTypes, pushTypes, pushTypes_eq_append as (a :: acc), pushTypes_eq_append as [a]]
    simp

theorem pushTypes_append {α : Type} (as acc₁ acc₂ : List α) :
    pushTypes as (acc₁ ++ acc₂) = pushTypes as acc₁ ++ acc₂ := by
  rw [pushTypes_eq_append as (acc₁ ++ acc₂), pushTypes_eq_append as acc₁, List.append_assoc]

theorem pushTypes_length {α : Type} :
    ∀ (as acc : List α), (pushTypes as acc).length = as.length + acc.length
  | [], _ => by simp [pushTypes]
  | _ :: as, acc => by
    rw [pushTypes, pushTypes_length as (_ :: acc), List.length_cons, List.length_cons]
    omega

/-- Positional lookup of block `i` in `TBlocks rs sig`. -/
@[expose] def tblocksGet {rs : List Ty} :
    {sig : List (List Ty)} → {ts : List Ty} → TBlocks rs sig → Member ts sig → TFlat rs
  | _, _, .cons b _, .here => b
  | _, _, .cons _ bs, .there i => tblocksGet bs i

theorem denoteB_get_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    {vs : List ((t : Ty) × V t)} {ls : List ((ts : List Ty) × L ts)} :
    {sig : List (List Ty)} → (bs : TBlocks rs sig) →
    {ts : List Ty} → (i : Member ts sig) → (xs : Tup V ts) →
    (denoteB V L bs vs ls).get i xs = denote V L (tblocksGet bs i) (pushTup xs vs) ls
  | _, .cons _ _, _, .here, _ => rfl
  | _, .cons _ bs, _, .there i, xs => denoteB_get_eq bs i xs

/-- Relational version of `FlatLemmas.CtxMatch` bridging `V₁ ↔ K` and `V₁ ↔ V₂` into `vs`. -/
@[expose] def RelCtxMatch {α : Type} {V₁ V₂ : α → Type} (nv : Nat)
    (G₁₂ : Ctx V₁ (fun _ => Nat)) (G₁₃ : Ctx V₁ V₂) (vs : List ((a : α) × V₂ a)) : Prop :=
  ∀ {a} {v₁ : V₁ a} {k : Nat}, ⟨a, (v₁, k)⟩ ∈ G₁₂ →
    k < nv ∧ ∃ v₂, listGet? vs (nv - 1 - k) = some ⟨a, v₂⟩ ∧ ⟨a, (v₁, v₂)⟩ ∈ G₁₃

namespace RelCtxMatch

theorem weaken {α : Type} {V₁ V₂ : α → Type} {nv : Nat}
    {G₁₂ G₁₂' : Ctx V₁ (fun _ => Nat)} {G₁₃ G₁₃' : Ctx V₁ V₂}
    {vs : List ((a : α) × V₂ a)}
    (h12 : ∀ p ∈ G₁₂', p ∈ G₁₂) (h13 : ∀ p ∈ G₁₃, p ∈ G₁₃')
    (h : RelCtxMatch nv G₁₂ G₁₃ vs) : RelCtxMatch nv G₁₂' G₁₃' vs := by
  intro a v₁ k hm
  obtain ⟨hlt, v₂, hget, h13m⟩ := h (h12 _ hm)
  exact ⟨hlt, v₂, hget, h13 _ h13m⟩

theorem cons {α : Type} {V₁ V₂ : α → Type} {nv : Nat}
    {G₁₂ : Ctx V₁ (fun _ => Nat)} {G₁₃ : Ctx V₁ V₂} {vs : List ((a : α) × V₂ a)}
    {a : α} (v₁ : V₁ a) (v₂ : V₂ a) (h : RelCtxMatch nv G₁₂ G₁₃ vs) :
    RelCtxMatch (nv + 1) (⟨a, (v₁, nv)⟩ :: G₁₂) (⟨a, (v₁, v₂)⟩ :: G₁₃) (⟨a, v₂⟩ :: vs) := by
  intro a' v₁' k hm
  rcases List.mem_cons.1 hm with ⟨rfl, rfl⟩ | hm'
  · refine ⟨Nat.lt_succ_self _, v₂, ?_, List.mem_cons_self⟩
    have : nv + 1 - 1 - nv = 0 := by omega
    rw [this]; rfl
  · obtain ⟨hlt, v₂', hget, h13m⟩ := h hm'
    have heq : nv + 1 - 1 - k = (nv - 1 - k) + 1 := by omega
    refine ⟨Nat.lt_succ_of_lt hlt, v₂', ?_, List.mem_cons_of_mem _ h13m⟩
    rw [heq]
    exact hget

theorem pushTup {α : Type} {V₁ V₂ : α → Type} :
    {ts : List α} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) →
    {nv : Nat} → {G₁₂ : Ctx V₁ (fun _ => Nat)} → {G₁₃ : Ctx V₁ V₂} →
    {vs : List ((a : α) × V₂ a)} →
    RelCtxMatch nv G₁₂ G₁₃ vs →
    RelCtxMatch (nv + ts.length) (Tup.zip xs₁ (Tup.levels ts nv) ++ G₁₂)
      (Tup.zip xs₁ xs₂ ++ G₁₃) (LeanQbe.T.pushTup xs₂ vs)
  | [], (), (), _, _, _, _, h => fun hm => h hm
  | t :: ts, (x₁, xs₁), (x₂, xs₂), nv, G₁₂, G₁₃, vs, h => fun hm => by
    have hstep : RelCtxMatch (nv + 1) (⟨t, (x₁, nv)⟩ :: G₁₂)
        (⟨t, (x₁, x₂)⟩ :: G₁₃) (⟨t, x₂⟩ :: vs) := RelCtxMatch.cons x₁ x₂ h
    have hrec : RelCtxMatch ((nv + 1) + ts.length)
        (Tup.zip xs₁ (Tup.levels ts (nv + 1)) ++ ⟨t, (x₁, nv)⟩ :: G₁₂)
        (Tup.zip xs₁ xs₂ ++ ⟨t, (x₁, x₂)⟩ :: G₁₃) (LeanQbe.T.pushTup xs₂ (⟨t, x₂⟩ :: vs)) :=
      RelCtxMatch.pushTup xs₁ xs₂ hstep
    have hlen : nv + (t :: ts).length = (nv + 1) + ts.length := by
      simp [List.length_cons]; omega
    dsimp only [Tup.levels, Tup.zip, LeanQbe.T.pushTup] at hm ⊢
    rw [hlen]
    refine hrec.weaken ?_ ?_ hm
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · rcases List.mem_cons.1 hp with rfl | hp
        · exact List.mem_append_right _ List.mem_cons_self
        · exact List.mem_append_left _ hp
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact List.mem_append_left _ (List.mem_cons_of_mem _ hp)
      · rcases List.mem_cons.1 hp with rfl | hp
        · exact List.mem_append_left _ List.mem_cons_self
        · exact List.mem_append_right _ hp

end RelCtxMatch

theorem denoteArg_idxArg_rel {V₁ V₂ : Ty → Type} {nv : Nat}
    {G₁₂ : Ctx V₁ K} {G₁₃ : Ctx V₁ V₂} {vs : List ((t : Ty) × V₂ t)}
    (hG : RelCtxMatch nv G₁₂ G₁₃ vs) {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg K t}
    (ha : ArgRel G₁₂ t a₁ a₂) :
    ∃ a₂', denoteArg vs (idxArg nv a₂) = some a₂' ∧ ArgRel G₁₃ t a₁ a₂' := by
  cases ha with
  | imm c => exact ⟨.imm c, rfl, .imm c⟩
  | @var v₁ k hm =>
    obtain ⟨hlt, v₂, hget, h13m⟩ := hG hm
    refine ⟨.var v₂, ?_, .var h13m⟩
    simp [idxArg, hlt, denoteArg, lookupV, hget, castTy_self]

theorem denoteArgs_idxArgs_rel {V₁ V₂ : Ty → Type} {nv : Nat}
    {G₁₂ : Ctx V₁ K} {G₁₃ : Ctx V₁ V₂} {vs : List ((t : Ty) × V₂ t)}
    (hG : RelCtxMatch nv G₁₂ G₁₃ vs) :
    {ts : List Ty} → {as₁ : Tup (Arg V₁) ts} → {as₂ : Tup (Arg K) ts} →
    TRel (ArgRel G₁₂) as₁ as₂ →
    ∃ as₂', denoteArgs vs (idxArgs nv as₂) = some as₂' ∧ TRel (ArgRel G₁₃) as₁ as₂'
  | [], (), (), _ => ⟨(), rfl, .nil⟩
  | _ :: _, (a₁, as₁), (a₂, as₂), .cons ha has => by
    obtain ⟨a₂', ha', hrel⟩ := denoteArg_idxArg_rel hG ha
    obtain ⟨as₂', has', hrels⟩ := denoteArgs_idxArgs_rel hG has
    exact ⟨(a₂', as₂'), by simp [idxArgs, denoteArgs, ha', has'], .cons hrel hrels⟩

theorem denote_wf_src {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    {G₁₂ : Ctx V₁ K} → {D₁₂ : Ctx L₁ KL} →
    {e₁ : Expr V₁ L₁ rs} → {e₂ : Expr K KL rs} →
    Wf G₁₂ D₁₂ e₁ e₂ →
    ∀ {nv nl : Nat} {G₁₃ : Ctx V₁ V₂} {D₁₃ : Ctx L₁ L₂}
      {vs : List ((t : Ty) × V₂ t)} {ls : List ((ts : List Ty) × L₂ ts)},
      RelCtxMatch nv G₁₂ G₁₃ vs →
      RelCtxMatch nl D₁₂ D₁₃ ls →
      Wf G₁₃ D₁₃ e₁ (denote V₂ L₂ (toTFlat e₂ nv nl) vs ls) := by
  intro G₁₂ D₁₂ e₁ e₂ hwf
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro nv nl G₁₃ D₁₃ vs ls hG hD
    cases hop with
    | mk code hargs =>
      obtain ⟨args', hda, hrels⟩ := denoteArgs_idxArgs_rel hG hargs
      dsimp only [toTFlat, denote]
      rw [hda]
      exact .let_ (.mk _ hrels) fun xs₁ xs₃ =>
        ih xs₁ (Tup.levels ts nv) (RelCtxMatch.pushTup xs₁ xs₃ hG) hD
  | @load G D t a₁ a₂ k₁ k₂ ha _ ih =>
    intro nv nl G₁₃ D₁₃ vs ls hG hD
    obtain ⟨a', hda, hrel⟩ := denoteArg_idxArg_rel hG ha
    dsimp only [toTFlat, denote]
    rw [hda]
    exact .load t hrel fun v₁ v₃ => ih v₁ nv (RelCtxMatch.cons v₁ v₃ hG) hD
  | @store G D t v₁ v₂ a₁ a₂ k₁ k₂ hv ha _ ih =>
    intro nv nl G₁₃ D₁₃ vs ls hG hD
    obtain ⟨v', hdv, hrelv⟩ := denoteArg_idxArg_rel hG hv
    obtain ⟨a', hda, hrela⟩ := denoteArg_idxArg_rel hG ha
    dsimp only [toTFlat, denote]
    rw [hdv, hda]
    exact .store hrelv hrela (ih hG hD)
  | @call G D f as bs args₁ args₂ k₁ k₂ hargs _ ih =>
    intro nv nl G₁₃ D₁₃ vs ls hG hD
    obtain ⟨args', hda, hrels⟩ := denoteArgs_idxArgs_rel hG hargs
    dsimp only [toTFlat, denote]
    rw [hda]
    exact .call f hrels fun xs₁ xs₃ =>
      ih xs₁ (Tup.levels bs nv) (RelCtxMatch.pushTup xs₁ xs₃ hG) hD
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hc _ _ iht ihe =>
    intro nv nl G₁₃ D₁₃ vs ls hG hD
    obtain ⟨c', hdc, hrelc⟩ := denoteArg_idxArg_rel hG hc
    dsimp only [toTFlat, denote]
    rw [hdc]
    exact .jnz hrelc (iht hG hD) (ihe hG hD)
  | @jump G D ts j₁ j₂ args₁ args₂ hj hargs =>
    intro nv nl G₁₃ D₁₃ vs ls hG hD
    obtain ⟨hlt, l₂, hget, h13m⟩ := hD hj
    obtain ⟨args', hda, hrels⟩ := denoteArgs_idxArgs_rel hG hargs
    dsimp only [toTFlat, denote, lookupL]
    simp [hlt, hget, castListTy_self, hda]
    exact .jump h13m hrels
  | @ret G D vs₁ vs₂ hvs =>
    intro nv nl G₁₃ D₁₃ vs ls hG _
    obtain ⟨vs', hdv, hrels⟩ := denoteArgs_idxArgs_rel hG hvs
    dsimp only [toTFlat, denote]
    rw [hdv]
    exact .ret hrels
  | @exit G D f as args₁ args₂ hargs =>
    intro nv nl G₁₃ D₁₃ vs ls hG _
    obtain ⟨args', hda, hrels⟩ := denoteArgs_idxArgs_rel hG hargs
    dsimp only [toTFlat, denote]
    rw [hda]
    exact .exit f hrels
  | hlt =>
    intro _ _ _ _ _ _ _ _
    exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro nv nl G₁₃ D₁₃ vs ls hG hD
    dsimp only [toTFlat, denote]
    refine .group (fun Js₁ Js₃ => WfB.of_get fun i xs₁ xs₃ => ?_) (fun Js₁ Js₃ => ?_)
    · rw [denoteB_toTBlocks_get]
      exact ihb Js₁ (Tup.levels sig nl) i xs₁ (Tup.levels _ nv)
        (RelCtxMatch.pushTup xs₁ xs₃ hG) (RelCtxMatch.pushTup Js₁ Js₃ hD)
    · exact ihk Js₁ (Tup.levels sig nl) hG (RelCtxMatch.pushTup Js₁ Js₃ hD)

theorem wp_iff_of_diag_eq {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx Val Val} {D : Ctx Cont Cont} {e₁ e₂ : Expr Val Cont rs}
    (hWf : Wf G D e₁ e₂)
    (hG : ∀ p ∈ G, p.2.1 = p.2.2) (hD : ∀ p ∈ D, p.2.1 = p.2.2)
    {m : Mem 64} : wp Γ Q X e₁ m ↔ wp Γ Q X e₂ m := by
  refine ⟨?_, ?_⟩
  · exact wp_label_mono hWf hG (fun p hp xs m' hm => hD p hp ▸ hm) m
  · exact wp_label_mono hWf.symm
      (fun p hp => by
        rcases List.mem_map.1 hp with ⟨⟨a, v₁, v₂⟩, hq, rfl⟩
        exact (hG ⟨a, v₁, v₂⟩ hq).symm)
      (fun p hp xs m' hm => by
        rcases List.mem_map.1 hp with ⟨⟨a, l₁, l₂⟩, hq, hEq⟩
        dsimp only at hEq
        cases hEq
        have hl : l₁ = l₂ := hD ⟨a, (l₁, l₂)⟩ hq
        exact hl ▸ hm) m

/-! ## 3. `CallsOkCombinators`: flat-IR call/exit obligations -/

mutual
/-- Flat-IR mirror of `Expr.callsOk`. -/
@[expose] def callsOkTF (allowed : List SigEntry) (exits : List Sym)
    {rs : List Ty} : TFlat rs → Prop
  | .let_ _ k => callsOkTF allowed exits k
  | .load _ _ k => callsOkTF allowed exits k
  | .store _ _ k => callsOkTF allowed exits k
  | .call f (as := as) bs _ k => (f, as, bs) ∈ allowed ∧ callsOkTF allowed exits k
  | .jnz _ t e => callsOkTF allowed exits t ∧ callsOkTF allowed exits e
  | .jump _ _ | .ret _ | .hlt => True
  | .exit f _ => f ∈ exits
  | .group bs k => callsOkBs allowed exits bs ∧ callsOkTF allowed exits k

/-- Block-list companion of `callsOkTF`. -/
@[expose] def callsOkBs (allowed : List SigEntry) (exits : List Sym)
    {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Prop
  | _, .nil => True
  | _, .cons b bs => callsOkTF allowed exits b ∧ callsOkBs allowed exits bs
end

@[simp] theorem callsOkTF_let (a : List SigEntry) (e : List Sym) {rs ts : List Ty}
    (op : Op K ts) (k : TFlat rs) :
    callsOkTF a e (.let_ op k) = callsOkTF a e k := rfl
@[simp] theorem callsOkTF_load (a : List SigEntry) (e : List Sym) {rs : List Ty} (t : Ty)
    (ptr : Arg K i64) (k : TFlat rs) :
    callsOkTF a e (.load t ptr k) = callsOkTF a e k := rfl
@[simp] theorem callsOkTF_store (a : List SigEntry) (e : List Sym) {rs : List Ty} {t : Ty}
    (v : Arg K t) (ptr : Arg K i64) (k : TFlat rs) :
    callsOkTF a e (.store v ptr k) = callsOkTF a e k := rfl
@[simp] theorem callsOkTF_call (a : List SigEntry) (e : List Sym) {rs : List Ty} (f : Sym)
    {as : List Ty} (bs : List Ty) (args : Tup (Arg K) as) (k : TFlat rs) :
    callsOkTF a e (.call f bs args k) = ((f, as, bs) ∈ a ∧ callsOkTF a e k) := rfl
@[simp] theorem callsOkTF_jnz (a : List SigEntry) (e : List Sym) {rs : List Ty}
    (c : Arg K .bool) (t k : TFlat rs) :
    callsOkTF a e (.jnz c t k) = (callsOkTF a e t ∧ callsOkTF a e k) := rfl
@[simp] theorem callsOkTF_jump (a : List SigEntry) (e : List Sym) {rs ts : List Ty} (j : Nat)
    (args : Tup (Arg K) ts) :
    callsOkTF a e (TFlat.jump j args : TFlat rs) = True := rfl
@[simp] theorem callsOkTF_ret (a : List SigEntry) (e : List Sym) {rs : List Ty}
    (vs : Tup (Arg K) rs) :
    callsOkTF a e (.ret vs) = True := rfl
@[simp] theorem callsOkTF_exit (a : List SigEntry) (e : List Sym) {rs : List Ty} (f : Sym)
    {as : List Ty} (args : Tup (Arg K) as) :
    callsOkTF a e (TFlat.exit f args : TFlat rs) = (f ∈ e) := rfl
@[simp] theorem callsOkTF_hlt (a : List SigEntry) (e : List Sym) {rs : List Ty} :
    callsOkTF a e (.hlt : TFlat rs) = True := rfl
@[simp] theorem callsOkTF_group (a : List SigEntry) (e : List Sym) {rs : List Ty}
    {sig : List (List Ty)} (bs : TBlocks rs sig) (k : TFlat rs) :
    callsOkTF a e (.group bs k) = (callsOkBs a e bs ∧ callsOkTF a e k) := rfl
@[simp] theorem callsOkBs_nil (a : List SigEntry) (e : List Sym) {rs : List Ty} :
    callsOkBs a e (.nil : TBlocks rs []) = True := rfl
@[simp] theorem callsOkBs_cons (a : List SigEntry) (e : List Sym) {rs : List Ty}
    {ts : List Ty} {sig : List (List Ty)} (b : TFlat rs) (bs : TBlocks rs sig) :
    callsOkBs a e (.cons (ts := ts) b bs) = (callsOkTF a e b ∧ callsOkBs a e bs) := rfl

theorem callsOkBs_get {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    {sig : List (List Ty)} → {bs : TBlocks rs sig} → callsOkBs allowed exits bs →
    ∀ {ts} (i : Member ts sig), callsOkTF allowed exits (tblocksGet bs i)
  | _, .cons _ _, h, _, .here => h.1
  | _, .cons _ _, h, _, .there i => callsOkBs_get h.2 i

theorem callsOkBs_of_get {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    {sig : List (List Ty)} → {bs : TBlocks rs sig} →
    (∀ {ts} (i : Member ts sig), callsOkTF allowed exits (tblocksGet bs i)) →
    callsOkBs allowed exits bs
  | _, .nil, _ => trivial
  | _, .cons _ _, h => ⟨h .here, callsOkBs_of_get (fun i => h (.there i))⟩

private theorem tup_units_eq {α : Type} :
    {ts : List α} → (xs : Tup (fun _ => Unit) ts) → xs = Tup.units ts
  | [], () => rfl
  | _ :: _, ((), xs) => congrArg ((), ·) (tup_units_eq xs)

mutual
theorem callsOkTF_denote {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    (tf : TFlat rs) → callsOkTF allowed exits tf →
    ∀ (vs : List ((t : Ty) × (fun _ => Unit) t))
      (ls : List ((ts : List Ty) × (fun _ => Unit) ts)),
      (denote (fun _ => Unit) (fun _ => Unit) tf vs ls).callsOk allowed exits
  | .let_ op k, h, vs, ls => by
    dsimp only [denote]
    cases denoteArgs vs op.args with
    | none => trivial
    | some _ =>
      change (denote (fun _ => Unit) (fun _ => Unit) k (pushTup (Tup.units _) vs) ls).callsOk _ _
      exact callsOkTF_denote k h _ ls
  | .load t a k, h, vs, ls => by
    dsimp only [denote]
    cases denoteArg vs a with
    | none => trivial
    | some _ => exact callsOkTF_denote k h _ ls
  | .store v a k, h, vs, ls => by
    dsimp only [denote]
    cases denoteArg vs v <;> cases denoteArg vs a <;>
      first | trivial | exact callsOkTF_denote k h vs ls
  | .call f bs args k, h, vs, ls => by
    dsimp only [denote]
    cases denoteArgs vs args with
    | none => trivial
    | some _ =>
      refine ⟨h.1, ?_⟩
      change (denote (fun _ => Unit) (fun _ => Unit) k (pushTup (Tup.units bs) vs) ls).callsOk _ _
      exact callsOkTF_denote k h.2 _ ls
  | .jnz c t e, h, vs, ls => by
    dsimp only [denote]
    cases denoteArg vs c with
    | none => trivial
    | some _ => exact ⟨callsOkTF_denote t h.1 vs ls, callsOkTF_denote e h.2 vs ls⟩
  | .jump j args, _, vs, ls => by
    dsimp only [denote]
    cases lookupL ls _ j <;> cases denoteArgs vs args <;> trivial
  | .ret xs, _, vs, _ => by
    dsimp only [denote]
    cases denoteArgs vs xs <;> trivial
  | .exit f args, h, vs, _ => by
    dsimp only [denote]
    cases denoteArgs vs args with
    | none => trivial
    | some _ => exact h
  | .hlt, _, _, _ => trivial
  | .group (sig := sig) bs k, h, vs, ls => by
    dsimp only [denote, Expr.callsOk]
    exact ⟨callsOkBs_denote bs h.1 vs (pushTup (Tup.units sig) ls),
           callsOkTF_denote k h.2 vs (pushTup (Tup.units sig) ls)⟩

theorem callsOkBs_denote {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    {sig : List (List Ty)} → (bs : TBlocks rs sig) → callsOkBs allowed exits bs →
    ∀ (vs : List ((t : Ty) × (fun _ => Unit) t))
      (ls : List ((ts : List Ty) × (fun _ => Unit) ts)),
      (denoteB (fun _ => Unit) (fun _ => Unit) bs vs ls).callsOk allowed exits
  | _, .nil, _, _, _ => trivial
  | _, .cons (ts := ts) b bs, h, vs, ls => by
    dsimp only [denoteB, Blocks.callsOk]
    exact ⟨callsOkTF_denote b h.1 (pushTup (Tup.units ts) vs) ls, callsOkBs_denote bs h.2 vs ls⟩
end

mutual
theorem callsOkTF_of_denote {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × (fun _ => Unit) t)} →
    {ls : List ((ts : List Ty) × (fun _ => Unit) ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → tf.wfCheck Γ Δ = true →
    (denote (fun _ => Unit) (fun _ => Unit) tf vs ls).callsOk allowed exits →
    callsOkTF allowed exits tf
  | .let_ op k, Γ, Δ, vs, ls, hΓ, hΔ, hwf, hc => by
    simp only [TFlat.wfCheck, Bool.and_eq_true] at hwf
    obtain ⟨args', hda⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [denote] at hc
    rw [hda] at hc
    exact callsOkTF_of_denote k (CtxTypes.push (Tup.units _) hΓ) hΔ hwf.2 hc
  | .load t a k, Γ, Δ, vs, ls, hΓ, hΔ, hwf, hc => by
    simp only [TFlat.wfCheck, Bool.and_eq_true] at hwf
    obtain ⟨a', hda⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1)
    dsimp only [denote] at hc
    rw [hda] at hc
    exact callsOkTF_of_denote k (CtxTypes.cons hΓ) hΔ hwf.2 hc
  | .store v a k, Γ, Δ, vs, ls, hΓ, hΔ, hwf, hc => by
    simp only [TFlat.wfCheck, Bool.and_eq_true] at hwf
    obtain ⟨v', hdv⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    obtain ⟨a', hda⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.2)
    dsimp only [denote] at hc
    rw [hdv, hda] at hc
    exact callsOkTF_of_denote k hΓ hΔ hwf.2 hc
  | .call f bs args k, Γ, Δ, vs, ls, hΓ, hΔ, hwf, hc => by
    simp only [TFlat.wfCheck, Bool.and_eq_true] at hwf
    obtain ⟨args', hda⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [denote] at hc
    rw [hda] at hc
    exact ⟨hc.1, callsOkTF_of_denote k (CtxTypes.push (Tup.units bs) hΓ) hΔ hwf.2 hc.2⟩
  | .jnz c t e, Γ, Δ, vs, ls, hΓ, hΔ, hwf, hc => by
    simp only [TFlat.wfCheck, Bool.and_eq_true] at hwf
    obtain ⟨c', hdc⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    dsimp only [denote] at hc
    rw [hdc] at hc
    exact ⟨callsOkTF_of_denote t hΓ hΔ hwf.1.2 hc.1, callsOkTF_of_denote e hΓ hΔ hwf.2 hc.2⟩
  | .jump _ _, _, _, _, _, _, _, _, _ => trivial
  | .ret _, _, _, _, _, _, _, _, _ => trivial
  | .exit f args, Γ, _, vs, _, hΓ, _, hwf, hc => by
    simp only [TFlat.wfCheck] at hwf
    obtain ⟨args', hda⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [denote] at hc
    rw [hda] at hc
    exact hc
  | .hlt, _, _, _, _, _, _, _, _ => trivial
  | .group (sig := sig) bs k, Γ, Δ, vs, ls, hΓ, hΔ, hwf, hc => by
    simp only [TFlat.wfCheck, Bool.and_eq_true] at hwf
    exact ⟨callsOkBs_of_denote bs hΓ (CtxTypes.push (Tup.units sig) hΔ) hwf.1 hc.1,
           callsOkTF_of_denote k hΓ (CtxTypes.push (Tup.units sig) hΔ) hwf.2 hc.2⟩

theorem callsOkBs_of_denote {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    {sig : List (List Ty)} → (bs : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × (fun _ => Unit) t)} →
    {ls : List ((ts : List Ty) × (fun _ => Unit) ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → bs.wfCheck Γ Δ = true →
    (denoteB (fun _ => Unit) (fun _ => Unit) bs vs ls).callsOk allowed exits →
    callsOkBs allowed exits bs
  | _, .nil, _, _, _, _, _, _, _, _ => trivial
  | _, .cons (ts := ts) b bs, Γ, Δ, vs, ls, hΓ, hΔ, hwf, hc => by
    simp only [TBlocks.wfCheck, Bool.and_eq_true] at hwf
    exact ⟨callsOkTF_of_denote b (CtxTypes.push (Tup.units ts) hΓ) hΔ hwf.1 hc.1,
           callsOkBs_of_denote bs hΓ hΔ hwf.2 hc.2⟩
end

mutual
theorem callsOkTF_toTFlat {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    {G : Ctx (fun _ => Unit) K} → {D : Ctx (fun _ => Unit) KL} →
    {e₁ : Expr (fun _ => Unit) (fun _ => Unit) rs} → {e₂ : Expr K KL rs} →
    Wf G D e₁ e₂ → (nv nl : Nat) →
    callsOkTF allowed exits (toTFlat e₂ nv nl) ↔ e₁.callsOk allowed exits
  | _, _, _, _, .let_ hop hk, nv, nl => by
    cases hop
    exact callsOkTF_toTFlat (hk (Tup.units _) (Tup.levels _ nv)) (nv + _) nl
  | _, _, _, _, .load _ _ hk, nv, nl =>
    callsOkTF_toTFlat (hk () nv) (nv + 1) nl
  | _, _, _, _, .store _ _ hk, nv, nl =>
    callsOkTF_toTFlat hk nv nl
  | _, _, _, _, .call _ _ hk, nv, nl =>
    and_congr_right fun _ => callsOkTF_toTFlat (hk (Tup.units _) (Tup.levels _ nv)) (nv + _) nl
  | _, _, _, _, .jnz _ ht he, nv, nl =>
    and_congr (callsOkTF_toTFlat ht nv nl) (callsOkTF_toTFlat he nv nl)
  | _, _, _, _, .jump _ _, _, _ => Iff.rfl
  | _, _, _, _, .ret _, _, _ => Iff.rfl
  | _, _, _, _, .exit _ _, _, _ => Iff.rfl
  | _, _, _, _, .hlt, _, _ => Iff.rfl
  | _, _, _, _, .group (sig := sig) hb hk, nv, nl => by
    dsimp only [toTFlat, callsOkTF, Expr.callsOk]
    exact and_congr
      (callsOkBs_toTBlocks (hb (Tup.units sig) (Tup.levels sig nl)) nv (nl + sig.length))
      (callsOkTF_toTFlat (hk (Tup.units sig) (Tup.levels sig nl)) nv (nl + sig.length))

theorem callsOkBs_toTBlocks {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    {G : Ctx (fun _ => Unit) K} → {D : Ctx (fun _ => Unit) KL} →
    {sig : List (List Ty)} → {b₁ : Blocks (fun _ => Unit) (fun _ => Unit) rs sig} →
    {b₂ : Blocks K KL rs sig} →
    WfB G D b₁ b₂ → (nv nl : Nat) →
    callsOkBs allowed exits (toTBlocks b₂ nv nl) ↔ b₁.callsOk allowed exits
  | _, _, _, _, _, .nil, _, _ => Iff.rfl
  | _, _, ts :: _, _, _, .cons hb hbs, nv, nl => by
    dsimp only [toTBlocks, callsOkBs, Blocks.callsOk]
    exact and_congr
      (callsOkTF_toTFlat (hb (Tup.units ts) (Tup.levels ts nv)) (nv + ts.length) nl)
      (callsOkBs_toTBlocks hbs nv nl)
end

/-- Context agreement between level witnesses `K` and flat type list `Γ`. -/
@[expose] def LvlsWf {α : Type} {V : α → Type} (Γ : List α)
    (G : Ctx V (fun _ => Nat)) : Prop :=
  ∀ {a} {v : V a} {k : Nat}, ⟨a, (v, k)⟩ ∈ G →
    k < Γ.length ∧ listGet? Γ (Γ.length - 1 - k) = some a

namespace LvlsWf

theorem cons {α : Type} {V : α → Type} {Γ : List α} {G : Ctx V (fun _ => Nat)}
    {a : α} {v : V a} (hG : LvlsWf Γ G) :
    LvlsWf (a :: Γ) (⟨a, (v, Γ.length)⟩ :: G) := by
  intro a' v' k hm
  rcases List.mem_cons.1 hm with ⟨rfl, rfl⟩ | hm'
  · refine ⟨Nat.lt_succ_self _, ?_⟩
    have : (a :: Γ).length - 1 - Γ.length = 0 := by simp [List.length_cons]
    rw [this]; rfl
  · obtain ⟨hlt, hget⟩ := hG hm'
    have heq : (a :: Γ).length - 1 - k = (Γ.length - 1 - k) + 1 := by
      simp [List.length_cons]; omega
    refine ⟨Nat.lt_succ_of_lt hlt, ?_⟩
    rw [heq]
    exact hget

theorem weaken {α : Type} {V : α → Type} {Γ : List α} {G₁ G₂ : Ctx V (fun _ => Nat)}
    (hsub : ∀ p ∈ G₂, p ∈ G₁) (h : LvlsWf Γ G₁) : LvlsWf Γ G₂ :=
  fun hm => h (hsub _ hm)

theorem pushTup {α : Type} {V : α → Type} :
    {ts : List α} → (xs : Tup V ts) → {Γ : List α} → {G : Ctx V (fun _ => Nat)} →
    LvlsWf Γ G →
    LvlsWf (pushTypes ts Γ) (Tup.zip xs (Tup.levels ts Γ.length) ++ G)
  | [], (), _, _, h => fun hm => h hm
  | a :: ts, (x, xs), Γ, G, h => fun hm => by
    have hstep : LvlsWf (a :: Γ) (⟨a, (x, Γ.length)⟩ :: G) := LvlsWf.cons (v := x) h
    have hrec : LvlsWf (pushTypes ts (a :: Γ))
        (Tup.zip xs (Tup.levels ts (Γ.length + 1)) ++ ⟨a, (x, Γ.length)⟩ :: G) := by
      rw [← List.length_cons (a := a) (as := Γ)]
      exact LvlsWf.pushTup xs hstep
    dsimp only [Tup.levels, Tup.zip, pushTypes] at hm ⊢
    refine hrec.weaken ?_ hm
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · rcases List.mem_cons.1 hp with rfl | hp
      · exact List.mem_append_right _ List.mem_cons_self
      · exact List.mem_append_left _ hp
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)

end LvlsWf

private theorem checkArg_idxArg_of_lvlsWf {V : Ty → Type} {Γ : List Ty}
    {G : Ctx V K} (hG : LvlsWf Γ G) {t : Ty} {a₁ : Arg V t} {a₂ : Arg K t}
    (ha : ArgRel G t a₁ a₂) : checkArg Γ t (idxArg Γ.length a₂) = true := by
  cases ha with
  | imm _ => rfl
  | var hm =>
    obtain ⟨hlt, hget⟩ := hG hm
    simp only [idxArg, hlt, ↓reduceIte, checkArg, hget]
    cases h : tyDecEq t t with
    | isTrue _ => rfl
    | isFalse hne => exact absurd rfl hne

private theorem checkArgs_idxArgs_of_lvlsWf {V : Ty → Type} {Γ : List Ty}
    {G : Ctx V K} (hG : LvlsWf Γ G) :
    {ts : List Ty} → {as₁ : Tup (Arg V) ts} → {as₂ : Tup (Arg K) ts} →
    TRel (ArgRel G) as₁ as₂ → checkArgs Γ (idxArgs Γ.length as₂) = true
  | [], (), (), _ => rfl
  | _ :: _, (_, _), (_, _), .cons ha has => by
    simp [idxArgs, checkArgs, checkArg_idxArg_of_lvlsWf hG ha,
      checkArgs_idxArgs_of_lvlsWf hG has]

mutual
theorem toTFlat_wfCheck_of_wf {rs : List Ty} :
    {G : Ctx (fun _ => Unit) K} → {D : Ctx (fun _ => Unit) KL} →
    {e₁ : Expr (fun _ => Unit) (fun _ => Unit) rs} → {e₂ : Expr K KL rs} →
    Wf G D e₁ e₂ → {Γ : List Ty} → {Δ : List (List Ty)} →
      LvlsWf Γ G → LvlsWf Δ D →
      (toTFlat e₂ Γ.length Δ.length).wfCheck Γ Δ = true
  | _, _, _, _, .let_ hop hk, Γ, Δ, hG, hD => by
    cases hop with
    | mk _ hargs =>
      simp only [toTFlat, TFlat.wfCheck, Bool.and_eq_true]
      refine ⟨checkArgs_idxArgs_of_lvlsWf hG hargs, ?_⟩
      simpa [pushTypes_length, Nat.add_comm] using
        toTFlat_wfCheck_of_wf (hk (Tup.units _) (Tup.levels _ Γ.length))
          (LvlsWf.pushTup (Tup.units _) hG) hD
  | _, _, _, _, .load _ ha hk, Γ, Δ, hG, hD => by
    simp only [toTFlat, TFlat.wfCheck, Bool.and_eq_true]
    exact ⟨checkArg_idxArg_of_lvlsWf hG ha,
      toTFlat_wfCheck_of_wf (hk () Γ.length) (LvlsWf.cons hG) hD⟩
  | _, _, _, _, .store hv ha hk, Γ, Δ, hG, hD => by
    simp only [toTFlat, TFlat.wfCheck, Bool.and_eq_true]
    exact ⟨⟨checkArg_idxArg_of_lvlsWf hG hv, checkArg_idxArg_of_lvlsWf hG ha⟩,
      toTFlat_wfCheck_of_wf hk hG hD⟩
  | _, _, _, _, .call _ hargs hk, Γ, Δ, hG, hD => by
    simp only [toTFlat, TFlat.wfCheck, Bool.and_eq_true]
    refine ⟨checkArgs_idxArgs_of_lvlsWf hG hargs, ?_⟩
    simpa [pushTypes_length, Nat.add_comm] using
      toTFlat_wfCheck_of_wf (hk (Tup.units _) (Tup.levels _ Γ.length))
        (LvlsWf.pushTup (Tup.units _) hG) hD
  | _, _, _, _, .jnz hc ht he, Γ, Δ, hG, hD => by
    simp only [toTFlat, TFlat.wfCheck, Bool.and_eq_true]
    exact ⟨⟨checkArg_idxArg_of_lvlsWf hG hc, toTFlat_wfCheck_of_wf ht hG hD⟩,
      toTFlat_wfCheck_of_wf he hG hD⟩
  | _, _, _, _, .jump hj hargs, Γ, Δ, hG, hD => by
    obtain ⟨hlt, hget⟩ := hD hj
    simp only [toTFlat, TFlat.wfCheck, Bool.and_eq_true]
    refine ⟨?_, checkArgs_idxArgs_of_lvlsWf hG hargs⟩
    simp only [hlt, ↓reduceIte, hget]
    cases h : listTyDecEq _ _ with
    | isTrue _ => rfl
    | isFalse hne => exact absurd rfl hne
  | _, _, _, _, .ret hvs, Γ, _, hG, _ =>
    checkArgs_idxArgs_of_lvlsWf hG hvs
  | _, _, _, _, .exit _ hargs, Γ, _, hG, _ =>
    checkArgs_idxArgs_of_lvlsWf hG hargs
  | _, _, _, _, .hlt, _, _, _, _ => rfl
  | _, D, _, _, .group (sig := sig) hb hk, Γ, Δ, hG, hD => by
    simp only [toTFlat, TFlat.wfCheck, Bool.and_eq_true]
    have hD' : LvlsWf (pushTypes sig Δ)
        (Tup.zip (Tup.units sig) (Tup.levels sig Δ.length) ++ D) :=
      LvlsWf.pushTup (Tup.units sig) hD
    refine ⟨?_, ?_⟩
    · simpa [pushTypes_length, Nat.add_comm] using
        toTBlocks_wfCheck_of_wfB (hb (Tup.units sig) (Tup.levels sig Δ.length)) hG hD'
    · simpa [pushTypes_length, Nat.add_comm] using
        toTFlat_wfCheck_of_wf (hk (Tup.units sig) (Tup.levels sig Δ.length)) hG hD'

theorem toTBlocks_wfCheck_of_wfB {rs : List Ty} :
    {G : Ctx (fun _ => Unit) K} → {D : Ctx (fun _ => Unit) KL} →
    {sig : List (List Ty)} → {b₁ : Blocks (fun _ => Unit) (fun _ => Unit) rs sig} →
    {b₂ : Blocks K KL rs sig} →
    WfB G D b₁ b₂ → {Γ : List Ty} → {Δ : List (List Ty)} →
      LvlsWf Γ G → LvlsWf Δ D →
      (toTBlocks b₂ Γ.length Δ.length).wfCheck Γ Δ = true
  | _, _, _, _, _, .nil, _, _, _, _ => rfl
  | _, _, ts :: _, _, _, .cons hb hbs, Γ, Δ, hG, hD => by
    simp only [toTBlocks, TBlocks.wfCheck, Bool.and_eq_true]
    refine ⟨?_, toTBlocks_wfCheck_of_wfB hbs hG hD⟩
    simpa [pushTypes_length, Nat.add_comm] using
      toTFlat_wfCheck_of_wf (hb (Tup.units ts) (Tup.levels ts Γ.length))
        (LvlsWf.pushTup (Tup.units ts) hG) hD
end

theorem reifyFunc_wfCheck {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (reifyFunc f).wfCheck (pushTypes as []) [] = true := by
  have h0 : LvlsWf (α := Ty) (V := fun _ => Unit) [] [] := fun {_ _ _} hm => nomatch hm
  have hG : LvlsWf (pushTypes as []) (Tup.zip (Tup.units as) (Tup.levels as 0)) := by
    have h1 : LvlsWf (pushTypes as [])
        (Tup.zip (Tup.units as) (Tup.levels as ([] : List Ty).length) ++ []) :=
      LvlsWf.pushTup (Tup.units as) h0
    intro a v k hm
    exact h1 (by simpa using hm)
  have hD0 : LvlsWf (α := List Ty) (V := fun _ => Unit) [] [] := fun {_ _ _} hm => nomatch hm
  have h := toTFlat_wfCheck_of_wf (hf (fun _ => Unit) K (fun _ => Unit) KL (Tup.units as)
    (Tup.levels as 0)) hG hD0
  simpa [reifyFunc, pushTypes_length] using h

theorem callsOkTF_reify_iff {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    callsOkTF allowed exits (reifyFunc f) ↔
      (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits :=
  callsOkTF_toTFlat
    (hf (fun _ => Unit) K (fun _ => Unit) KL (Tup.units as) (Tup.levels as 0)) as.length 0

theorem denoteFunc_callsOk_iff {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {tf : TFlat rs}
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (denoteFunc (as := as) tf (fun _ => Unit) (fun _ => Unit)
      (Tup.units as)).callsOk allowed exits ↔ callsOkTF allowed exits tf := by
  refine ⟨fun h => ?_, fun h => callsOkTF_denote tf h _ _⟩
  exact callsOkTF_of_denote tf (CtxTypes.push (Tup.units as) .nil) .nil hwf h

theorem Func.renorm_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (f.renorm (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits ↔
      (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits := by
  rw [Func.renorm, denoteFunc_callsOk_iff (reifyFunc_wfCheck hf)]
  exact callsOkTF_reify_iff hf

theorem map_eq_append_split {α : Type _} {β : Type _} (f : α → β) :
    ∀ {l : List α} {a b : List β}, l.map f = a ++ b →
      ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.map f = a ∧ l₂.map f = b
  | l, [], b, h => ⟨[], l, rfl, rfl, h⟩
  | [], _ :: _, _, h => by simp at h
  | x :: xs, _ :: as, b, h => by
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨l₁, l₂, hl, h₁, h₂⟩ := map_eq_append_split f h.2
    exact ⟨x :: l₁, l₂, by simp [hl], by simp [h.1, h₁], h₂⟩

end PassFlatKit

end LeanQbe.T
