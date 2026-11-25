module

public import LeanQbe.T.OptUtilLemmas

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-!
# Shared Pass Environment & Relational Context Kit

Generic relational-context (`CtxPred`, `RelKit`, `OutMetaKit`) and fresh-key semantic context
(`PassFValGood`, `FCtxGood`) helpers shared privately across mid-end pass proof modules
(`CanonLemmas`, `DceParamLemmas`, `AssumeBitsLemmas`, `MemLoadLemmas`, `IfOptLemmas`).
-/

section ContextPredicates

/-- Pointwise invariant over entries of a typed context `Ctx V₁ V₂`. -/
def CtxPred {α : Type} {V₁ V₂ : α → Type}
    (P : (a : α) → V₁ a → V₂ a → Prop) (G : Ctx V₁ V₂) : Prop :=
  ∀ p ∈ G, P p.1 p.2.1 p.2.2

namespace CtxPred

theorem nil {α : Type} {V₁ V₂ : α → Type} (P : (a : α) → V₁ a → V₂ a → Prop) :
    CtxPred P ([] : Ctx V₁ V₂) :=
  fun _ h => by cases h

section
variable {α : Type} {V₁ V₂ : α → Type} {P : (a : α) → V₁ a → V₂ a → Prop}

theorem cons {a : α} {v₁ : V₁ a} {v₂ : V₂ a} {G : Ctx V₁ V₂}
    (h : P a v₁ v₂) (hG : CtxPred P G) : CtxPred P (⟨a, (v₁, v₂)⟩ :: G) :=
  fun p hp => by rcases List.mem_cons.mp hp with rfl | hp; exact h; exact hG p hp

theorem append {G₁ G₂ : Ctx V₁ V₂} (h₁ : CtxPred P G₁) (h₂ : CtxPred P G₂) :
    CtxPred P (G₁ ++ G₂) :=
  fun p hp => by rcases List.mem_append.mp hp with hp | hp; exact h₁ p hp; exact h₂ p hp

theorem mono {Q : (a : α) → V₁ a → V₂ a → Prop}
    (hPQ : ∀ {a : α} {v₁ : V₁ a} {v₂ : V₂ a}, P a v₁ v₂ → Q a v₁ v₂)
    {G : Ctx V₁ V₂} (hG : CtxPred P G) : CtxPred Q G :=
  fun p hp => hPQ (hG p hp)

theorem mem {G : Ctx V₁ V₂} (hG : CtxPred P G) {a : α} {v₁ : V₁ a} {v₂ : V₂ a}
    (hm : ⟨a, (v₁, v₂)⟩ ∈ G) : P a v₁ v₂ :=
  hG ⟨a, (v₁, v₂)⟩ hm

theorem append_zip : ∀ {as : List α} {xs : Tup V₁ as} {ys : Tup V₂ as} {G : Ctx V₁ V₂},
    TRel P xs ys → CtxPred P G → CtxPred P (Tup.zip xs ys ++ G)
  | [], (), (), _, .nil, hG => hG
  | _ :: _, (_, _), (_, _), _, .cons hx hxs, hG => cons hx (append_zip hxs hG)

end

theorem zip_tupFreshWith_left_const
    {V W : Ty → Type} {mk : ∀ {t : Ty}, V t → Nat → W t}
    {P : (t : Ty) → W t → V t → Prop}
    (hmk : ∀ {t : Ty} (v : V t) (k : Nat), P t (mk v k) v) :
    ∀ {ts : List Ty} (xs : Tup V ts) (next : Nat),
      CtxPred P (Tup.zip (tupFreshWith mk ts xs next) xs)
  | [], (), _ => fun _ h => by simp [Tup.zip] at h
  | _ :: _, (x, xs), next => fun p hp => by
      simp only [tupFreshWith, Tup.zip, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hmk x next
      · exact zip_tupFreshWith_left_const hmk xs (next + 1) p hp

end CtxPred

theorem argRel_imm?_eq {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {t : Ty}
    {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} (h : ArgRel G t a₁ a₂) : a₁.imm? = a₂.imm? := by
  cases h <;> simp [Arg.imm?]

theorem imm?_eq_some_val {t : Ty} {a : Arg Val t} {c : Val t}
    (h : a.imm? = some c) : a.val = c := by
  cases a <;> simp [Arg.imm?, Arg.val] at h ⊢; exact h

theorem tupMapArg_id {V : Ty → Type} :
    {ts : List Ty} → (as : Tup (Arg V) ts) → tupMapArg (fun _ a => a) as = as
  | [], () => rfl
  | _ :: _, (_, as) => congrArg _ (tupMapArg_id as)

theorem trel_argVal_eq : {ts : List Ty} → {as₁ as₂ : Tup (Arg Val) ts} →
    TRel (fun _ a₁ a₂ => a₁.val = a₂.val) as₁ as₂ → vals as₁ = vals as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons h hs => Prod.ext h (trel_argVal_eq hs)

end ContextPredicates

section RelKit

/-- Parameterized relational context interface for pass value wrappers `W V t`. -/
structure RelKit (W : (Ty → Type) → Ty → Type) where
  out : ∀ {V : Ty → Type} {t : Ty}, W V t → Arg V t
  fresh : ∀ {V : Ty → Type} {t : Ty}, V t → Nat → W V t
  rel : ∀ {V₁ V₂ : Ty → Type}, Ctx V₁ V₂ → (t : Ty) → W V₁ t → W V₂ t → Prop
  rel_weaken : ∀ {V₁ V₂ : Ty → Type} {G₁' G₂' : Ctx V₁ V₂},
    (∀ p, p ∈ G₁' → p ∈ G₂') → ∀ {t : Ty} {w₁ : W V₁ t} {w₂ : W V₂ t},
      rel G₁' t w₁ w₂ → rel G₂' t w₁ w₂
  rel_out : ∀ {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} {t : Ty}
    {w₁ : W V₁ t} {w₂ : W V₂ t}, rel G' t w₁ w₂ → ArgRel G' t (out w₁) (out w₂)
  rel_fresh : ∀ {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} {t : Ty}
    {x : V₁ t} {y : V₂ t} (k : Nat), ⟨t, (x, y)⟩ ∈ G' → rel G' t (fresh x k) (fresh y k)

namespace RelKit

variable {W : (Ty → Type) → Ty → Type} (K : RelKit W)

/-- Context relation lifted pointwise across a `RelKit`. -/
def RelG {V₁ V₂ : Ty → Type} (G' : Ctx V₁ V₂) (G : Ctx (W V₁) (W V₂)) : Prop :=
  CtxPred (K.rel G') G

theorem relG_cons {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} {G : Ctx (W V₁) (W V₂)}
    {t : Ty} {w₁ : W V₁ t} {w₂ : W V₂ t}
    (hw : K.rel G' t w₁ w₂) (hG : K.RelG G' G) : K.RelG G' (⟨t, (w₁, w₂)⟩ :: G) :=
  CtxPred.cons hw hG

theorem relG_append {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} {G₁ G₂ : Ctx (W V₁) (W V₂)}
    (h₁ : K.RelG G' G₁) (h₂ : K.RelG G' G₂) : K.RelG G' (G₁ ++ G₂) :=
  CtxPred.append h₁ h₂

theorem relG_weaken {V₁ V₂ : Ty → Type} {G₁' G₂' : Ctx V₁ V₂} {G : Ctx (W V₁) (W V₂)}
    (hsub : ∀ p, p ∈ G₁' → p ∈ G₂') (hG : K.RelG G₁' G) : K.RelG G₂' G :=
  CtxPred.mono (K.rel_weaken hsub) hG

theorem relG_append_tup {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} {G : Ctx (W V₁) (W V₂)}
    {ts : List Ty} {w₁s : Tup (W V₁) ts} {w₂s : Tup (W V₂) ts}
    (hT : TRel (K.rel G') w₁s w₂s) (hG : K.RelG G' G) : K.RelG G' (Tup.zip w₁s w₂s ++ G) :=
  CtxPred.append_zip hT hG

theorem trel_freshTup {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂}
    (ts : List Ty) (xs : Tup V₁ ts) (ys : Tup V₂ ts) (next : Nat) :
    TRel (fun t w₁ w₂ => K.rel (Tup.zip xs ys ++ G') t w₁ w₂)
      (tupFreshWith K.fresh ts xs next) (tupFreshWith K.fresh ts ys next) :=
  TRel_tupFreshWith (P := K.rel) K.fresh K.fresh
    (fun hsub => K.rel_weaken hsub) (fun _ _ b => K.rel_fresh b List.mem_cons_self) xs ys next

theorem relG_freshTup {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} {G : Ctx (W V₁) (W V₂)}
    (ts : List Ty) (xs : Tup V₁ ts) (ys : Tup V₂ ts) (next : Nat) (hG : K.RelG G' G) :
    K.RelG (Tup.zip xs ys ++ G')
      (Tup.zip (tupFreshWith K.fresh ts xs next) (tupFreshWith K.fresh ts ys next) ++ G) :=
  K.relG_append_tup (K.trel_freshTup (G' := G') ts xs ys next)
    (K.relG_weaken (fun _ hp => List.mem_append_right _ hp) hG)

theorem relG_freshOne {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} {G : Ctx (W V₁) (W V₂)}
    {t : Ty} (x : V₁ t) (y : V₂ t) (next : Nat) (hG : K.RelG G' G) :
    K.RelG (⟨t, (x, y)⟩ :: G') (⟨t, (K.fresh x next, K.fresh y next)⟩ :: G) :=
  K.relG_cons (K.rel_fresh next List.mem_cons_self)
    (K.relG_weaken (fun _ hp => List.mem_cons_of_mem _ hp) hG)

end RelKit

/-- Specialized `RelKit` for wrappers storing `out : Arg V t` plus a `V`-independent `Meta t`. -/
structure OutMetaKit (W : (Ty → Type) → Ty → Type) (Meta : Ty → Type) where
  out : ∀ {V : Ty → Type} {t : Ty}, W V t → Arg V t
  tag : ∀ {V : Ty → Type} {t : Ty}, W V t → Meta t
  fresh : ∀ {V : Ty → Type} {t : Ty}, V t → Nat → W V t
  out_fresh : ∀ {V : Ty → Type} {t : Ty} (x : V t) (k : Nat), out (fresh x k) = .var x
  tag_fresh : ∀ {V₁ V₂ : Ty → Type} {t : Ty} (x : V₁ t) (y : V₂ t) (k : Nat),
    tag (fresh x k) = tag (fresh y k)

namespace OutMetaKit

variable {W : (Ty → Type) → Ty → Type} {Meta : Ty → Type} (M : OutMetaKit W Meta)

/-- Pointwise relation: `out` values are `ArgRel G'` and `tag` fields are equal. -/
def rel {V₁ V₂ : Ty → Type} (G' : Ctx V₁ V₂) (t : Ty) (w₁ : W V₁ t) (w₂ : W V₂ t) : Prop :=
  ArgRel G' t (M.out w₁) (M.out w₂) ∧ M.tag w₁ = M.tag w₂

/-- Convert an `OutMetaKit` into a `RelKit`. -/
def toRelKit : RelKit W where
  out := M.out
  fresh := M.fresh
  rel := M.rel
  rel_weaken hsub _ _ _ h := ⟨ArgRel.weaken hsub h.1, h.2⟩
  rel_out h := h.1
  rel_fresh k hm := ⟨by simpa [M.out_fresh] using ArgRel.var hm, M.tag_fresh _ _ k⟩

theorem rel_weaken {V₁ V₂ : Ty → Type} {G₁' G₂' : Ctx V₁ V₂} {t : Ty}
    {w₁ : W V₁ t} {w₂ : W V₂ t} (hsub : ∀ p, p ∈ G₁' → p ∈ G₂') (h : M.rel G₁' t w₁ w₂) :
    M.rel G₂' t w₁ w₂ :=
  ⟨ArgRel.weaken hsub h.1, h.2⟩

end OutMetaKit

end RelKit

section PassFValGood

/-- Semantic invariant tying lowered `out : Arg Val t` and `k : FKey t` to `v : Val t` below
`next` in `fenv : FEnv`. -/
def PassFValGood (next : Nat) (fenv : FEnv) {t : Ty}
    (out : Arg Val t) (k : FKey t) (v : Val t) : Prop :=
  out.val = v ∧ FKey.FLt next k ∧ FKey.fev fenv k = v

/-- Pointwise `PassFValGood` context invariant parameterized by `out` and `key` projections. -/
def FCtxGood {W : Ty → Type}
    (out : ∀ {t : Ty}, W t → Arg Val t) (key : ∀ {t : Ty}, W t → FKey t)
    (next : Nat) (fenv : FEnv) (G : Ctx W Val) : Prop :=
  CtxPred (fun _ w v => PassFValGood next fenv (out w) (key w) v) G

namespace FCtxGood

section
variable {W : Ty → Type} {out : ∀ {t : Ty}, W t → Arg Val t} {key : ∀ {t : Ty}, W t → FKey t}

theorem cons {next : Nat} {fenv : FEnv} {G : Ctx W Val} {t : Ty} {w : W t} {v : Val t}
    (hw : PassFValGood next fenv (out w) (key w) v) (hG : FCtxGood out key next fenv G) :
    FCtxGood out key next fenv (⟨t, (w, v)⟩ :: G) :=
  CtxPred.cons hw hG

theorem append {next : Nat} {fenv : FEnv} {G₁ G₂ : Ctx W Val}
    (h₁ : FCtxGood out key next fenv G₁) (h₂ : FCtxGood out key next fenv G₂) :
    FCtxGood out key next fenv (G₁ ++ G₂) :=
  CtxPred.append h₁ h₂

theorem fupd {next next' i : Nat} {fenv : FEnv} {G : Ctx W Val} {t : Ty} (v : Val t)
    (hn : next ≤ next') (hi : next ≤ i) (hG : FCtxGood out key next fenv G) :
    FCtxGood out key next' (LeanQbe.T.fupd fenv i v) G :=
  CtxPred.mono (fun h => ⟨h.1, FKey.FLt.le hn h.2.1,
    by rw [FKey.fev_fupd v (FKey.FLt.le hi h.2.1), h.2.2]⟩) hG

theorem fupdTup {next next' start : Nat} {fenv : FEnv} {G : Ctx W Val}
    {ts : List Ty} (xs : Tup Val ts)
    (hn : next ≤ next') (hs : next ≤ start) (hG : FCtxGood out key next fenv G) :
    FCtxGood out key next' (LeanQbe.T.fupdTup fenv start xs) G :=
  CtxPred.mono (fun h => ⟨h.1, FKey.FLt.le hn h.2.1,
    by rw [FKey.fev_fupdTup xs (FKey.FLt.le hs h.2.1), h.2.2]⟩) hG

theorem freshOne {mk : ∀ {t : Ty}, Val t → Nat → W t}
    (hout : ∀ {t : Ty} (v : Val t) (k : Nat), out (mk v k) = .var v)
    (hkey : ∀ {t : Ty} (v : Val t) (k : Nat), key (mk v k) = .var k)
    {next : Nat} {fenv : FEnv} {G : Ctx W Val} {t : Ty} (v : Val t)
    (hG : FCtxGood out key next fenv G) :
    FCtxGood out key (next + 1) (LeanQbe.T.fupd fenv next v) (⟨t, (mk v next, v)⟩ :: G) :=
  cons (by simp [PassFValGood, hout, hkey, FKey.FLt, FKey.fev, fupd_eq])
    (fupd v (Nat.le_succ next) (Nat.le_refl next) hG)

theorem freshTup {mk : ∀ {t : Ty}, Val t → Nat → W t}
    (hout : ∀ {t : Ty} (v : Val t) (k : Nat), out (mk v k) = .var v)
    (hkey : ∀ {t : Ty} (v : Val t) (k : Nat), key (mk v k) = .var k) :
    ∀ {ts : List Ty} (xs : Tup Val ts) (next : Nat) {fenv : FEnv} {G : Ctx W Val},
      FCtxGood out key next fenv G →
      FCtxGood out key (next + ts.length) (LeanQbe.T.fupdTup fenv next xs)
        (Tup.zip (tupFreshWith mk ts xs next) xs ++ G)
  | [], (), next, fenv, G, hG => by simpa [tupFreshWith, Tup.zip, LeanQbe.T.fupdTup] using hG
  | t :: ts, (x, xs), next, fenv, G, hG => by
      have ih := freshTup hout hkey xs (next + 1)
        (fupd x (Nat.le_succ next) (Nat.le_refl next) hG)
      have hhead : PassFValGood (next + 1 + ts.length)
          (LeanQbe.T.fupdTup (LeanQbe.T.fupd fenv next x) (next + 1) xs)
          (out (mk x next)) (key (mk x next)) x := by
        rw [hout, hkey]
        refine ⟨rfl, show next < next + 1 + ts.length by omega, ?_⟩
        rw [FKey.fev_fupdTup xs (show FKey.FLt (next + 1) (.var next) from Nat.lt_succ_self next)]
        exact fupd_eq fenv next x
      have hres := cons hhead ih
      have hlen : next + 1 + ts.length = next + (t :: ts).length := by
        simp [List.length_cons]; omega
      rw [← hlen]; exact hres

theorem argRel_val {next : Nat} {fenv : FEnv} {G : Ctx W Val} {t : Ty} {a : Arg W t}
    {a₂ : Arg Val t} (hG : FCtxGood out key next fenv G) (ha : ArgRel G t a a₂) :
    (match a with | .var w => out w | .imm u => .imm u).val = a₂.val := by
  cases ha with | imm => rfl | var hm => exact (CtxPred.mem hG hm).1

theorem argRel_lt {next : Nat} {fenv : FEnv} {G : Ctx W Val} {t : Ty} {a : Arg W t}
    {a₂ : Arg Val t} (hG : FCtxGood out key next fenv G) (ha : ArgRel G t a a₂) :
    FKey.FLt next (match a with | .var w => key w | .imm u => .imm u) := by
  cases ha with | imm => trivial | var hm => exact (CtxPred.mem hG hm).2.1

theorem argRel_ev {next : Nat} {fenv : FEnv} {G : Ctx W Val} {t : Ty} {a : Arg W t}
    {a₂ : Arg Val t} (hG : FCtxGood out key next fenv G) (ha : ArgRel G t a a₂) :
    FKey.fev fenv (match a with | .var w => key w | .imm u => .imm u) = a₂.val := by
  cases ha with | imm => rfl | var hm => exact (CtxPred.mem hG hm).2.2

theorem trel_vals {next : Nat} {fenv : FEnv} {G : Ctx W Val} {ts : List Ty}
    {as : Tup (Arg W) ts} {as₂ : Tup (Arg Val) ts}
    (f : (t : Ty) → Arg W t → Arg Val t)
    (hf : ∀ {t : Ty} (a : Arg W t), f t a = match a with | .var w => out w | .imm u => .imm u)
    (hG : FCtxGood out key next fenv G) (has : TRel (ArgRel G) as as₂) :
    vals (tupMapArg f as) = vals as₂ :=
  TRel.tupMapArg_vals f (fun ha => by rw [hf]; exact argRel_val hG ha) has

end

end FCtxGood

end PassFValGood

end LeanQbe.T
