module

public import LeanQbe.T.LinkLfp
import LeanQbe.T.WPLemmas

/-!
# Parameterized Fixed-Point Core (`LinkParamEnv`)

Shared Knaster–Tarski fixed-point lattice, relation-monotonicity, well-founded introduction,
and prefix-locality infrastructure over `ParamEnv (α : Type) := α → Env`, instantiated by both
`LinkDepthLfp` (`DepthEnv := ParamEnv Nat`) and `LinkBudgetLfp` (`BudgetEnv := ParamEnv Nat`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-- Parameterized semantic environment indexed by `α`. -/
abbrev ParamEnv (α : Type) : Type := α → Env

namespace ParamEnv

section Lattice

variable {α : Type}

def le (A B : ParamEnv α) : Prop := ∀ a, Env.le (A a) (B a)
theorem le_refl (A : ParamEnv α) : le A A := fun a => Env.le_refl (A a)
theorem le_trans {A B C : ParamEnv α} (h₁ : le A B) (h₂ : le B C) : le A C :=
  fun a => Env.le_trans (h₁ a) (h₂ a)

def bot : ParamEnv α := fun _ _ _ _ _ _ _ _ => False
def top : ParamEnv α := fun _ _ _ _ _ _ _ _ => True
theorem bot_le (A : ParamEnv α) : le bot A := fun _ _ _ _ _ _ _ _ h => False.elim h
def const (Γ : Env) : ParamEnv α := fun _ => Γ

def mono (Φ : ParamEnv α → ParamEnv α) : Prop :=
  ∀ ⦃A B : ParamEnv α⦄, le A B → le (Φ A) (Φ B)

def lfp (Φ : ParamEnv α → ParamEnv α) : ParamEnv α :=
  fun a f as bs xs m Q X => ∀ G : ParamEnv α, le (Φ G) G → G a f as bs xs m Q X

theorem lfp_le {Φ : ParamEnv α → ParamEnv α} {G : ParamEnv α} (h : le (Φ G) G) :
    le (lfp Φ) G :=
  fun _ _ _ _ _ _ _ _ hlfp => hlfp G h

theorem lfp_closed {Φ : ParamEnv α → ParamEnv α} (hm : mono Φ) :
    le (Φ (lfp Φ)) (lfp Φ) :=
  fun a f as bs xs m Q X hΦ _ hG => hG a f as bs xs m Q X (hm (lfp_le hG) a f as bs xs m Q X hΦ)

theorem lfp_post {Φ : ParamEnv α → ParamEnv α} (hm : mono Φ) :
    le (lfp Φ) (Φ (lfp Φ)) :=
  lfp_le (hm (lfp_closed hm))

theorem lfp_fix {Φ : ParamEnv α → ParamEnv α} (hm : mono Φ) : lfp Φ = Φ (lfp Φ) := by
  funext a f as bs xs m Q X
  exact propext ⟨fun h => lfp_post hm a f as bs xs m Q X h,
    fun h => lfp_closed hm a f as bs xs m Q X h⟩

theorem lfp_mono {Φ₁ Φ₂ : ParamEnv α → ParamEnv α} (hm₂ : mono Φ₂)
    (hle : ∀ G, le (Φ₁ G) (Φ₂ G)) : le (lfp Φ₁) (lfp Φ₂) :=
  lfp_le (le_trans (hle (lfp Φ₂)) (lfp_closed hm₂))

end Lattice

section RelOrder

variable {α : Type} (r : α → α → Prop)

def IsRelMono (G : ParamEnv α) : Prop := ∀ ⦃a₁ a₂ : α⦄, r a₁ a₂ → Env.le (G a₁) (G a₂)
def PreservesRelMono (Φ : ParamEnv α → ParamEnv α) : Prop :=
  ∀ ⦃G : ParamEnv α⦄, IsRelMono r G → IsRelMono r (Φ G)

theorem lfp_rel_mono (hrefl : ∀ a, r a a) (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c)
    {Φ : ParamEnv α → ParamEnv α} (hm : mono Φ) (hrm : PreservesRelMono r Φ) :
    IsRelMono r (lfp Φ) := by
  let H : ParamEnv α := fun a f as bs xs m Q X => ∀ a', r a a' → lfp Φ a' f as bs xs m Q X
  have hH_rm : IsRelMono r H := fun _ _ hle _ _ _ _ _ _ _ h a' ha' => h a' (htrans hle ha')
  have hH_le : le H (lfp Φ) := fun a _ _ _ _ _ _ _ h => h a (hrefl a)
  have hpre : le (Φ H) H := fun a f as bs xs m Q X hΦ a' hle =>
    lfp_closed hm a' f as bs xs m Q X
      (hm hH_le a' f as bs xs m Q X (hrm hH_rm hle f as bs xs m Q X hΦ))
  intro a₁ a₂ hle f as bs xs m Q X h
  exact lfp_le hpre a₁ f as bs xs m Q X h a₂ hle

def supBelow {ι : Type} (lt : ι → ι → Prop) (idx : ι → α) (S : ι → Env) (i : ι) : ParamEnv α :=
  fun a f as bs xs m Q X => ∃ j, lt j i ∧ r (idx j) a ∧ S j f as bs xs m Q X

theorem lfp_wf_mono {ι : Type} {lt : ι → ι → Prop} (hwf : WellFounded lt)
    (hrefl : ∀ a, r a a) (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c)
    (idx : ι → α) {Φ : ParamEnv α → ParamEnv α} (hm : mono Φ) (hrm : PreservesRelMono r Φ)
    (S : ι → Env) (hstep : ∀ i, Env.le (S i) (Φ (supBelow r lt idx S i) (idx i))) :
    ∀ i, Env.le (S i) (lfp Φ (idx i)) := by
  have hmono_r := lfp_rel_mono r hrefl htrans hm hrm
  intro i
  induction i using hwf.induction with
  | h i ih =>
      have hsup : le (supBelow r lt idx S i) (lfp Φ) := by
        rintro a f as bs xs m Q X ⟨j, hlt, ha_le, hj⟩
        exact hmono_r ha_le f as bs xs m Q X (ih j hlt f as bs xs m Q X hj)
      exact Env.le_trans (hstep i) (Env.le_trans (hm hsup (idx i)) (lfp_closed hm (idx i)))

theorem lfp_wf_above {ι : Type} {lt : ι → ι → Prop} (hwf : WellFounded lt)
    (idx : ι → α) {Φ : ParamEnv α → ParamEnv α} (hm : mono Φ) (P : ι → Env)
    (hstep : ∀ i a, r (idx i) a → Env.le (P i) (Φ (supBelow r lt idx P i) a)) :
    ∀ i a, r (idx i) a → Env.le (P i) (lfp Φ a) := by
  intro i
  induction i using hwf.induction with
  | h i ih =>
      intro a ha f as bs xs m Q X hP
      have hsup : le (supBelow r lt idx P i) (lfp Φ) := by
        rintro a' f' as' bs' xs' m' Q' X' ⟨j, hlt, hj, hPj⟩
        exact ih j hlt a' hj f' as' bs' xs' m' Q' X' hPj
      exact lfp_closed hm a f as bs xs m Q X
        (hm hsup a f as bs xs m Q X (hstep i a ha f as bs xs m Q X hP))

def PrefixLocal (Φ : ParamEnv α → ParamEnv α) : Prop :=
  ∀ (a : α) ⦃G₁ G₂ : ParamEnv α⦄,
    (∀ a', r a' a → Env.le (G₁ a') (G₂ a')) → Env.le (Φ G₁ a) (Φ G₂ a)

theorem lfp_le_of_prefix_below [DecidableRel r]
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c)
    {Φ : ParamEnv α → ParamEnv α} (hloc : PrefixLocal r Φ) (cap : α) (Mach : ParamEnv α)
    (hpre : ∀ a, r a cap → Env.le (Φ Mach a) (Mach a)) :
    ∀ a, r a cap → Env.le (lfp Φ a) (Mach a) := by
  let Gcap : ParamEnv α := fun a => if r a cap then Mach a else top a
  have hGcap : le (Φ Gcap) Gcap := by
    intro a f as bs xs m Q X hΦ
    by_cases hle : r a cap
    · simp only [Gcap, hle, ↓reduceIte]
      have hag : ∀ a', r a' a → Env.le (Gcap a') (Mach a') := fun a' ha' => by
        simp only [Gcap, htrans ha' hle, ↓reduceIte]; exact Env.le_refl _
      exact hpre a hle f as bs xs m Q X (hloc a hag f as bs xs m Q X hΦ)
    · simp only [Gcap, hle, ↓reduceIte, top]
  intro a hle f as bs xs m Q X hlfp
  simpa [Gcap, hle] using lfp_le hGcap a f as bs xs m Q X hlfp

end RelOrder

end ParamEnv

/-- Two-slot monotonicity predicate for `op₂ : Γcall → Γtail → Env`. -/
def Env.BiMono (op₂ : Env → Env → Env) : Prop :=
  ∀ ⦃C₁ C₂ T₁ T₂ : Env⦄, Env.le C₁ C₂ → Env.le T₁ T₂ → Env.le (op₂ C₁ T₁) (op₂ C₂ T₂)

/-- External-only callee environment offering declared externs of `M` from `Γext`. -/
def Env.extStep (M : Module) (Γext : Env) : Env :=
  fun f as bs xs m Q X => (f, as, bs) ∈ M.externs.map Extern.sig ∧ Γext f as bs xs m Q X

end LeanQbe.T
