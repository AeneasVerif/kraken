module

public import LeanQbe.T.LinkLfp
import LeanQbe.T.WPLemmas

/-!
# Depth-Indexed `DepthEnv.lfp` Order-Theoretic Core (`LinkDepthLfp`)

Purely target-independent order-theoretic fixed-point core over `DepthEnv := Nat → Env`,
generalizing `LinkLfp.Env.lfp` with depth indexing for tail (`depth j ≤ depth i`) and non-tail
(`depth j < depth i`) recursion:
* `DepthEnv`, `DepthEnv.le`, `DepthEnv.mono`, `DepthEnv.lfp`, `DepthEnv.lfp_le`,
  `DepthEnv.lfp_closed`, `DepthEnv.lfp_post`, `DepthEnv.lfp_fix`, `DepthEnv.lfp_mono`.
* `DepthEnv.IsDepthMono`, `DepthEnv.PreservesDepthMono`, `DepthEnv.lfp_depth_mono`,
  `DepthEnv.lfp_depth_mono_of_shift`.
* `DepthEnv.supBelow`, `DepthEnv.lfp_wf`, `DepthEnv.lfp_wf_recIdx`.
* Split call/tail module lifting (`Env.extStep`, `DepthEnv.callSlot`, `DepthEnv.tailSlot`,
  `DepthEnv.mkSccOp`, `DepthEnv.lfp_wf_mkSccOp`) and `DepthEnv.sccOp` / `DepthEnv.semScc`
  bridges into `LinkLfp` (`Env.semScc`, `Env.unfoldRecAt`, `ModuleSccOk`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

open LeanQbe.T.LinkRec
open LeanQbe.T.LinkScc

/-! ## 1. Depth-Indexed Environments and Knaster–Tarski `DepthEnv.lfp` -/

/-- Depth-indexed semantic environment: `G d` holds contracts valid at non-tail call depth `≤ d`. -/
abbrev DepthEnv : Type := Nat → Env

/-- Pointwise implication ordering across all non-tail depth bounds `d : Nat`. -/
@[expose] def DepthEnv.le (A B : DepthEnv) : Prop :=
  ∀ d, Env.le (A d) (B d)

theorem DepthEnv.le_refl (A : DepthEnv) : DepthEnv.le A A :=
  fun d => Env.le_refl (A d)

theorem DepthEnv.le_trans {A B C : DepthEnv} (h₁ : DepthEnv.le A B) (h₂ : DepthEnv.le B C) :
    DepthEnv.le A C :=
  fun d => Env.le_trans (h₁ d) (h₂ d)

/-- Bottom `DepthEnv`. -/
@[expose] def DepthEnv.bot : DepthEnv :=
  fun _ _ _ _ _ _ _ _ => False

theorem DepthEnv.bot_le (A : DepthEnv) : DepthEnv.le DepthEnv.bot A :=
  fun _ _ _ _ _ _ _ _ h => False.elim h

/-- Monotonicity of a transformer `Φ : DepthEnv → DepthEnv` with respect to `DepthEnv.le`. -/
@[expose] def DepthEnv.mono (Φ : DepthEnv → DepthEnv) : Prop :=
  ∀ ⦃A B : DepthEnv⦄, DepthEnv.le A B → DepthEnv.le (Φ A) (Φ B)

/-- Impredicative Knaster–Tarski least fixed point of `Φ : DepthEnv → DepthEnv`. -/
@[expose] def DepthEnv.lfp (Φ : DepthEnv → DepthEnv) : DepthEnv :=
  fun d f as bs xs m Q X =>
    ∀ G : DepthEnv, DepthEnv.le (Φ G) G → G d f as bs xs m Q X

/-- Elimination: `DepthEnv.lfp Φ` lies below every pre-fixpoint `G` (`Φ G ≤ G`). -/
theorem DepthEnv.lfp_le {Φ : DepthEnv → DepthEnv} {G : DepthEnv} (h : DepthEnv.le (Φ G) G) :
    DepthEnv.le (DepthEnv.lfp Φ) G :=
  fun _ _ _ _ _ _ _ _ hlfp => hlfp G h

/-- Pre-fixpoint closure property: for monotone `Φ`, `Φ (DepthEnv.lfp Φ) ≤ DepthEnv.lfp Φ`. -/
theorem DepthEnv.lfp_closed {Φ : DepthEnv → DepthEnv} (hm : DepthEnv.mono Φ) :
    DepthEnv.le (Φ (DepthEnv.lfp Φ)) (DepthEnv.lfp Φ) := by
  intro d f as bs xs m Q X hΦ G hG
  exact hG d f as bs xs m Q X (hm (DepthEnv.lfp_le hG) d f as bs xs m Q X hΦ)

/-- Alias for `DepthEnv.lfp_closed` matching `Env.lfp_pre`. -/
theorem DepthEnv.lfp_pre {Φ : DepthEnv → DepthEnv} (hm : DepthEnv.mono Φ) :
    DepthEnv.le (Φ (DepthEnv.lfp Φ)) (DepthEnv.lfp Φ) :=
  DepthEnv.lfp_closed hm

/-- Post-fixpoint property: for monotone `Φ`, `DepthEnv.lfp Φ ≤ Φ (DepthEnv.lfp Φ)`. -/
theorem DepthEnv.lfp_post {Φ : DepthEnv → DepthEnv} (hm : DepthEnv.mono Φ) :
    DepthEnv.le (DepthEnv.lfp Φ) (Φ (DepthEnv.lfp Φ)) :=
  DepthEnv.lfp_le (hm (DepthEnv.lfp_closed hm))

/-- Fixed-point equation `DepthEnv.lfp Φ = Φ (DepthEnv.lfp Φ)` for monotone `Φ`. -/
theorem DepthEnv.lfp_fix {Φ : DepthEnv → DepthEnv} (hm : DepthEnv.mono Φ) :
    DepthEnv.lfp Φ = Φ (DepthEnv.lfp Φ) := by
  funext d f as bs xs m Q X
  exact propext
    ⟨fun h => DepthEnv.lfp_post hm d f as bs xs m Q X h,
     fun h => DepthEnv.lfp_closed hm d f as bs xs m Q X h⟩

/-- Monotonicity of `DepthEnv.lfp` in the operator `Φ`. -/
theorem DepthEnv.lfp_mono {Φ₁ Φ₂ : DepthEnv → DepthEnv} (hm₂ : DepthEnv.mono Φ₂)
    (hle : ∀ G, DepthEnv.le (Φ₁ G) (Φ₂ G)) :
    DepthEnv.le (DepthEnv.lfp Φ₁) (DepthEnv.lfp Φ₂) :=
  DepthEnv.lfp_le (DepthEnv.le_trans (hle (DepthEnv.lfp Φ₂)) (DepthEnv.lfp_closed hm₂))

/-! ## 2. Depth Monotonicity and Well-Founded Introduction (`DepthEnv.lfp_wf`) -/

/-- A `DepthEnv` is depth-monotone when larger depth bounds include all smaller depth bounds. -/
@[expose] def DepthEnv.IsDepthMono (G : DepthEnv) : Prop :=
  ∀ ⦃d₁ d₂ : Nat⦄, d₁ ≤ d₂ → Env.le (G d₁) (G d₂)

/-- An operator `Φ` preserves depth monotonicity. -/
@[expose] def DepthEnv.PreservesDepthMono (Φ : DepthEnv → DepthEnv) : Prop :=
  ∀ ⦃G : DepthEnv⦄, DepthEnv.IsDepthMono G → DepthEnv.IsDepthMono (Φ G)

/-- `DepthEnv.lfp Φ` is depth-monotone whenever `Φ` is monotone and preserves depth monotonicity. -/
theorem DepthEnv.lfp_depth_mono {Φ : DepthEnv → DepthEnv}
    (hm : DepthEnv.mono Φ) (hdm : DepthEnv.PreservesDepthMono Φ) :
    DepthEnv.IsDepthMono (DepthEnv.lfp Φ) := by
  let G : DepthEnv := fun d f as bs xs m Q X =>
    ∀ d', d ≤ d' → DepthEnv.lfp Φ d' f as bs xs m Q X
  have hG_dm : DepthEnv.IsDepthMono G :=
    fun _ _ hle _ _ _ _ _ _ _ h d' hd' => h d' (Nat.le_trans hle hd')
  have hG_le : DepthEnv.le G (DepthEnv.lfp Φ) :=
    fun d _ _ _ _ _ _ _ h => h d (Nat.le_refl d)
  have hpre : DepthEnv.le (Φ G) G := by
    intro d f as bs xs m Q X hΦ d' hd'
    exact DepthEnv.lfp_closed hm d' f as bs xs m Q X
      (hm hG_le d' f as bs xs m Q X (hdm hG_dm hd' f as bs xs m Q X hΦ))
  intro d₁ d₂ hd f as bs xs m Q X h1
  exact DepthEnv.lfp_le hpre d₁ f as bs xs m Q X h1 d₂ hd

private theorem lfp_shift_step {Φ : DepthEnv → DepthEnv} (hm : DepthEnv.mono Φ)
    (hshift : ∀ (G : DepthEnv) (d : Nat), Env.le (Φ (fun k => G (k + 1)) d) (Φ G (d + 1))) :
    ∀ d, Env.le (DepthEnv.lfp Φ d) (DepthEnv.lfp Φ (d + 1)) := by
  let G : DepthEnv := fun k => DepthEnv.lfp Φ (k + 1)
  have hpre : DepthEnv.le (Φ G) G := fun d =>
    Env.le_trans (hshift (DepthEnv.lfp Φ) d) (DepthEnv.lfp_closed hm (d + 1))
  exact DepthEnv.lfp_le hpre

/-- Alternative depth-monotonicity theorem via shift commutation
`Φ (G ∘ (· + 1)) d ≤ Φ G (d + 1)`. -/
theorem DepthEnv.lfp_depth_mono_of_shift {Φ : DepthEnv → DepthEnv} (hm : DepthEnv.mono Φ)
    (hshift : ∀ (G : DepthEnv) (d : Nat), Env.le (Φ (fun k => G (k + 1)) d) (Φ G (d + 1))) :
    DepthEnv.IsDepthMono (DepthEnv.lfp Φ) := by
  intro d₁ d₂ hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
  induction k with
  | zero => exact Env.le_refl _
  | succ k ih =>
      exact Env.le_trans (ih (Nat.le_add_right d₁ k)) (lfp_shift_step hm hshift (d₁ + k))

/-- Depth-filtered supremum strictly below `i` along `lt`, collecting all predecessors `j` with
`lt j i ∧ depth j ≤ d` (so `d = depth i - 1` captures strict non-tail edges `depth j < depth i`
and `d = depth i` captures tail edges `depth j ≤ depth i`). -/
@[expose] def DepthEnv.supBelow {ι : Type} (lt : ι → ι → Prop) (depth : ι → Nat)
    (S : ι → Env) (i : ι) : DepthEnv :=
  fun d f as bs xs m Q X => ∃ j, lt j i ∧ depth j ≤ d ∧ S j f as bs xs m Q X

theorem DepthEnv.supBelow_call {ι : Type} {lt : ι → ι → Prop} {depth : ι → Nat}
    {S : ι → Env} {i j : ι} (hlt : lt j i) (hdep : depth j < depth i) :
    Env.le (S j) (DepthEnv.supBelow lt depth S i (depth i - 1)) :=
  fun _ _ _ _ _ _ _ hS => ⟨j, hlt, Nat.le_pred_of_lt hdep, hS⟩

theorem DepthEnv.supBelow_tail {ι : Type} {lt : ι → ι → Prop} {depth : ι → Nat}
    {S : ι → Env} {i j : ι} (hlt : lt j i) (hdep : depth j ≤ depth i) :
    Env.le (S j) (DepthEnv.supBelow lt depth S i (depth i)) :=
  fun _ _ _ _ _ _ _ hS => ⟨j, hlt, hdep, hS⟩

/-- Arbitrary well-founded `(ι, lt, wf, depth)` introduction into `DepthEnv.lfp Φ`, supporting
both depth-decreasing non-tail edges (`lt j i ∧ depth j < depth i`) and depth-nonincreasing tail
edges (`lt j i ∧ depth j ≤ depth i`). -/
theorem DepthEnv.lfp_wf {ι : Type} {lt : ι → ι → Prop} (hwf : WellFounded lt)
    (depth : ι → Nat) {Φ : DepthEnv → DepthEnv}
    (hm : DepthEnv.mono Φ) (hdm : DepthEnv.PreservesDepthMono Φ) (S : ι → Env)
    (hstep : ∀ i, Env.le (S i) (Φ (DepthEnv.supBelow lt depth S i) (depth i))) :
    ∀ i, Env.le (S i) (DepthEnv.lfp Φ (depth i)) := by
  have hmono_d := DepthEnv.lfp_depth_mono hm hdm
  intro i
  induction i using (WellFounded.induction hwf) with
  | h i ih =>
      have hsup : DepthEnv.le (DepthEnv.supBelow lt depth S i) (DepthEnv.lfp Φ) := by
        rintro d f as bs xs m Q X ⟨j, hlt, hd_le, hj⟩
        exact hmono_d hd_le f as bs xs m Q X (ih j hlt f as bs xs m Q X hj)
      exact Env.le_trans (hstep i)
        (Env.le_trans (hm hsup (depth i)) (DepthEnv.lfp_closed hm (depth i)))

/-- `RecIdx`-packaged specialization of `DepthEnv.lfp_wf`. -/
theorem DepthEnv.lfp_wf_recIdx {ι : Type} (idx : RecIdx ι) {Φ : DepthEnv → DepthEnv}
    (hm : DepthEnv.mono Φ) (hdm : DepthEnv.PreservesDepthMono Φ) (S : ι → Env)
    (hstep : ∀ i, Env.le (S i) (Φ (DepthEnv.supBelow idx.lt idx.depth S i) (idx.depth i))) :
    ∀ i, Env.le (S i) (DepthEnv.lfp Φ (idx.depth i)) :=
  DepthEnv.lfp_wf idx.wf idx.depth hm hdm S hstep

/-! ## 3. Split-Slot Module Operators (`DepthEnv.mkSccOp`, `DepthEnv.sccOp`, `DepthEnv.semScc`) -/

/-- External-only callee environment offering declared externs of `M` from `Γext` with all
internal recursive callees disabled (used for the non-tail call slot at `d = 0`). -/
@[expose] def Env.extStep (M : Module) (Γext : Env) : Env :=
  fun f as bs xs m Q X =>
    (f, as, bs) ∈ M.externs.map Extern.sig ∧ Γext f as bs xs m Q X

/-- Non-tail call-slot callee environment for `M` at depth `d`: at `d = 0` only `M.externs` are
offered; at `d + 1` recursive callees in `M.fns` are read from `G d`. -/
@[expose] def DepthEnv.callSlot (M : Module) (Γext : Env) (G : DepthEnv) : Nat → Env
  | 0 => Env.extStep M Γext
  | d + 1 => Env.sccStep M (G d) Γext

/-- Tail call-slot callee environment for `M` at depth `d`: recursive callees in `M.fns` are
read from `G d` alongside `M.externs` from `Γext`. -/
@[expose] def DepthEnv.tailSlot (M : Module) (Γext : Env) (G : DepthEnv) (d : Nat) : Env :=
  Env.sccStep M (G d) Γext

theorem DepthEnv.extStep_le_sccStep (M : Module) (Γ Γext : Env) :
    Env.le (Env.extStep M Γext) (Env.sccStep M Γ Γext) :=
  fun _ _ _ _ _ _ _ h => Or.inr h

theorem DepthEnv.callSlot_le_tailSlot {M : Module} {Γext : Env} {G : DepthEnv}
    (hdm : DepthEnv.IsDepthMono G) (d : Nat) :
    Env.le (DepthEnv.callSlot M Γext G d) (DepthEnv.tailSlot M Γext G d) := by
  cases d with
  | zero => exact DepthEnv.extStep_le_sccStep M (G 0) Γext
  | succ d =>
      intro f as bs xs m Q X h
      rcases h with ⟨hfns, hG⟩ | ⟨hext, hG⟩
      · exact Or.inl ⟨hfns, hdm (Nat.le_succ d) f as bs xs m Q X hG⟩
      · exact Or.inr ⟨hext, hG⟩

theorem DepthEnv.callSlot_mono {M : Module} {Γext : Env} {A B : DepthEnv}
    (hle : DepthEnv.le A B) : ∀ d, Env.le (DepthEnv.callSlot M Γext A d)
      (DepthEnv.callSlot M Γext B d)
  | 0 => Env.le_refl _
  | d + 1 => by
      rintro f as bs xs m Q X (⟨hfns, hA⟩ | ⟨hext, hA⟩)
      · exact Or.inl ⟨hfns, hle d f as bs xs m Q X hA⟩
      · exact Or.inr ⟨hext, hA⟩

theorem DepthEnv.tailSlot_mono {M : Module} {Γext : Env} {A B : DepthEnv}
    (hle : DepthEnv.le A B) (d : Nat) :
    Env.le (DepthEnv.tailSlot M Γext A d) (DepthEnv.tailSlot M Γext B d) := by
  rintro f as bs xs m Q X (⟨hfns, hA⟩ | ⟨hext, hA⟩)
  · exact Or.inl ⟨hfns, hle d f as bs xs m Q X hA⟩
  · exact Or.inr ⟨hext, hA⟩

theorem DepthEnv.callSlot_depth_mono {M : Module} {Γext : Env} {G : DepthEnv}
    (hdm : DepthEnv.IsDepthMono G) :
    DepthEnv.IsDepthMono (DepthEnv.callSlot M Γext G) := by
  intro d₁ d₂ hd
  cases d₁ with
  | zero =>
      cases d₂ with
      | zero => exact Env.le_refl _
      | succ d₂ => exact DepthEnv.extStep_le_sccStep M (G d₂) Γext
  | succ d₁ =>
      obtain ⟨d₂, rfl⟩ : ∃ k, d₂ = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
      rintro f as bs xs m Q X (⟨hfns, hG⟩ | ⟨hext, hG⟩)
      · exact Or.inl ⟨hfns, hdm (Nat.succ_le_succ_iff.mp hd) f as bs xs m Q X hG⟩
      · exact Or.inr ⟨hext, hG⟩

theorem DepthEnv.tailSlot_depth_mono {M : Module} {Γext : Env} {G : DepthEnv}
    (hdm : DepthEnv.IsDepthMono G) :
    DepthEnv.IsDepthMono (DepthEnv.tailSlot M Γext G) := by
  intro d₁ d₂ hd f as bs xs m Q X h
  rcases h with ⟨hfns, hG⟩ | ⟨hext, hG⟩
  · exact Or.inl ⟨hfns, hdm hd f as bs xs m Q X hG⟩
  · exact Or.inr ⟨hext, hG⟩

/-- Two-slot monotonicity predicate for `op₂ : Γcall → Γtail → Env`. -/
@[expose] def Env.BiMono (op₂ : Env → Env → Env) : Prop :=
  ∀ ⦃C₁ C₂ T₁ T₂ : Env⦄, Env.le C₁ C₂ → Env.le T₁ T₂ → Env.le (op₂ C₁ T₁) (op₂ C₂ T₂)

/-- Lift a two-slot environment transformer `op₂ Γcall Γtail` into a `DepthEnv → DepthEnv` module
operator via `DepthEnv.callSlot` and `DepthEnv.tailSlot`, ready for split `wpSplit` semantics. -/
@[expose] def DepthEnv.mkSccOp (M : Module) (Γext : Env) (op₂ : Env → Env → Env)
    (G : DepthEnv) (d : Nat) : Env :=
  op₂ (DepthEnv.callSlot M Γext G d) (DepthEnv.tailSlot M Γext G d)

theorem DepthEnv.mkSccOp_mono {M : Module} {Γext : Env} {op₂ : Env → Env → Env}
    (hbi : Env.BiMono op₂) : DepthEnv.mono (DepthEnv.mkSccOp M Γext op₂) :=
  fun _ _ hle d => hbi (DepthEnv.callSlot_mono hle d) (DepthEnv.tailSlot_mono hle d)

theorem DepthEnv.mkSccOp_preservesDepthMono {M : Module} {Γext : Env} {op₂ : Env → Env → Env}
    (hbi : Env.BiMono op₂) : DepthEnv.PreservesDepthMono (DepthEnv.mkSccOp M Γext op₂) :=
  fun _ hdm _ _ hd =>
    hbi (DepthEnv.callSlot_depth_mono hdm hd) (DepthEnv.tailSlot_depth_mono hdm hd)

/-- Well-founded two-slot introduction into `DepthEnv.lfp (DepthEnv.mkSccOp M Γext op₂)`:
non-tail edges (`Γcall`) may invoke predecessors `j` with `lt j i ∧ depth j < depth i` (empty at
`depth i = 0`), while tail edges (`Γtail`) may invoke predecessors `j` with
`lt j i ∧ depth j ≤ depth i`. -/
theorem DepthEnv.lfp_wf_mkSccOp {ι : Type} {lt : ι → ι → Prop} (hwf : WellFounded lt)
    (depth : ι → Nat) (M : Module) (Γext : Env) {op₂ : Env → Env → Env} (hbi : Env.BiMono op₂)
    (S : ι → Env)
    (hstep : ∀ (i : ι) (Γcall Γtail : Env),
      (∀ j, lt j i → depth j < depth i →
        Env.le (Env.restrict (S j) (M.fns.map Fn.sig)) Γcall) →
      Env.le (Env.extStep M Γext) Γcall →
      (∀ j, lt j i → depth j ≤ depth i →
        Env.le (Env.restrict (S j) (M.fns.map Fn.sig)) Γtail) →
      Env.le (Env.extStep M Γext) Γtail →
      Env.le (Env.restrict (S i) (M.fns.map Fn.sig)) (op₂ Γcall Γtail)) :
    ∀ i, Env.le (Env.restrict (S i) (M.fns.map Fn.sig))
      (DepthEnv.lfp (DepthEnv.mkSccOp M Γext op₂) (depth i)) := by
  let S' : ι → Env := fun i => Env.restrict (S i) (M.fns.map Fn.sig)
  refine DepthEnv.lfp_wf hwf depth (DepthEnv.mkSccOp_mono hbi)
    (DepthEnv.mkSccOp_preservesDepthMono hbi) S' fun i => ?_
  refine hstep i _ _ (fun j hlt hdep => ?_) ?_ (fun j hlt hdep => ?_) ?_
  · cases hd : depth i with
    | zero => omega
    | succ d' =>
        intro f as bs xs m Q X hSj
        have hlt_d : depth j ≤ d' := by rw [hd] at hdep; exact Nat.lt_succ_iff.mp hdep
        exact Or.inl ⟨hSj.1, j, hlt, hlt_d, hSj⟩
  · cases depth i with
    | zero => exact Env.le_refl _
    | succ d' => exact DepthEnv.extStep_le_sccStep M _ Γext
  · intro f as bs xs m Q X hSj
    exact Or.inl ⟨hSj.1, j, hlt, hdep, hSj⟩
  · exact DepthEnv.extStep_le_sccStep M _ Γext

/-- Depth-indexed module operator for `M` over `Γext` (evaluating `fn.body` against the
non-tail call slot `DepthEnv.callSlot`, extensible to `Func.wpSplit Γcall Γtail`). -/
@[expose] def DepthEnv.sccOp (M : Module) (Γext : Env) : DepthEnv → DepthEnv :=
  DepthEnv.mkSccOp M Γext fun Γcall _ =>
    fun f as bs xs m Q X =>
      (f, as, bs) ∈ M.fns.map Fn.sig ∧ ∃ fn ∈ M.fns, fn.name = f ∧
        ∃ (ha : fn.as = as) (hr : fn.rs = bs),
          Func.wp Γcall fn.body (ha ▸ xs) m (hr ▸ Q) X

private theorem wp_sccOp_biMono (M : Module) :
    Env.BiMono fun Γcall _ =>
      fun f as bs xs m Q X =>
        (f, as, bs) ∈ M.fns.map Fn.sig ∧ ∃ fn ∈ M.fns, fn.name = f ∧
          ∃ (ha : fn.as = as) (hr : fn.rs = bs),
            Func.wp Γcall fn.body (ha ▸ xs) m (hr ▸ Q) X := by
  rintro C₁ C₂ _ _ hC _ f as bs xs m Q X ⟨hsig, fn, hfn, hnm, ha, hr, hwp⟩
  exact ⟨hsig, fn, hfn, hnm, ha, hr, wp_env_mono hC _ m hwp⟩

theorem DepthEnv.sccOp_mono (M : Module) (Γext : Env) :
    DepthEnv.mono (DepthEnv.sccOp M Γext) :=
  DepthEnv.mkSccOp_mono (wp_sccOp_biMono M)

theorem DepthEnv.sccOp_preservesDepthMono (M : Module) (Γext : Env) :
    DepthEnv.PreservesDepthMono (DepthEnv.sccOp M Γext) :=
  DepthEnv.mkSccOp_preservesDepthMono (wp_sccOp_biMono M)

/-- Canonical depth-indexed least-fixed-point semantics of module `M` over `Γext`. -/
@[expose] def DepthEnv.semScc (M : Module) (Γext : Env) : DepthEnv :=
  DepthEnv.lfp (DepthEnv.sccOp M Γext)

theorem DepthEnv.semScc_depth_mono (M : Module) (Γext : Env) :
    DepthEnv.IsDepthMono (DepthEnv.semScc M Γext) :=
  DepthEnv.lfp_depth_mono (DepthEnv.sccOp_mono M Γext)
    (DepthEnv.sccOp_preservesDepthMono M Γext)

theorem DepthEnv.semScc_fix (M : Module) (Γext : Env) :
    DepthEnv.semScc M Γext = DepthEnv.sccOp M Γext (DepthEnv.semScc M Γext) :=
  DepthEnv.lfp_fix (DepthEnv.sccOp_mono M Γext)

/-! ## 4. Bridges Between `DepthEnv.lfp` and `LinkLfp` (`Env.lfp`, `Env.semScc`, `unfoldRecAt`) -/

/-- Lift a single-environment operator `Φ : Env → Env` pointwise across depths. -/
@[expose] def DepthEnv.liftOp (Φ : Env → Env) (G : DepthEnv) (d : Nat) : Env :=
  Φ (G d)

theorem DepthEnv.liftOp_mono {Φ : Env → Env} (hm : Env.mono Φ) :
    DepthEnv.mono (DepthEnv.liftOp Φ) :=
  fun _ _ hle d => hm (hle d)

/-- `DepthEnv.lfp` of a pointwise-lifted operator agrees with `Env.lfp` at every depth `d`. -/
theorem DepthEnv.lfp_liftOp_eq {Φ : Env → Env} (hm : Env.mono Φ) (d : Nat) :
    DepthEnv.lfp (DepthEnv.liftOp Φ) d = Env.lfp Φ := by
  funext f as bs xs m Q X
  refine propext ⟨fun h => ?_, fun h G hG => ?_⟩
  · exact h (fun _ => Env.lfp Φ) (fun _ => Env.lfp_pre hm)
  · exact h (G d) (hG d)

/-- A tail-only `mkSccOp` (whose `op₂` ignores its non-tail call slot) evaluates at `d = 0` to
the flat single-environment `Env.lfp` of
`fun Γ => op₂ (Env.extStep M Γext) (Env.sccStep M Γ Γext)`. -/
theorem DepthEnv.lfp_tailOnly_zero_eq (M : Module) (Γext : Env) {op₂ : Env → Env → Env}
    (hbi : Env.BiMono op₂) (htail : ∀ C₁ C₂ T, op₂ C₁ T = op₂ C₂ T) :
    DepthEnv.lfp (DepthEnv.mkSccOp M Γext op₂) 0 =
      Env.lfp (fun Γ => op₂ (Env.extStep M Γext) (Env.sccStep M Γ Γext)) := by
  have hm1 : Env.mono (fun Γ => op₂ (Env.extStep M Γext) (Env.sccStep M Γ Γext)) := by
    intro A B hle
    exact hbi (Env.le_refl _) (DepthEnv.tailSlot_mono (A := fun _ => A) (B := fun _ => B)
      (fun _ => hle) 0)
  funext f as bs xs m Q X
  refine propext ⟨fun h => ?_, fun h G hG => ?_⟩
  · refine h (fun _ => Env.lfp (fun Γ => op₂ (Env.extStep M Γext) (Env.sccStep M Γ Γext)))
      (fun d => ?_)
    have hpre := Env.lfp_pre hm1
    dsimp only [DepthEnv.mkSccOp]
    rw [htail (DepthEnv.callSlot M Γext _ d) (Env.extStep M Γext)]
    exact hpre
  · exact h (G 0) (hG 0)

/-- Every depth slice `DepthEnv.semScc M Γext d` embeds into flat `Env.semScc M Γext`. -/
theorem DepthEnv.semScc_le_envSemScc (M : Module) (Γext : Env) (d : Nat) :
    Env.le (DepthEnv.semScc M Γext d) (Env.semScc M Γext) := by
  let G : DepthEnv := fun _ => Env.semScc M Γext
  refine DepthEnv.lfp_le (G := G) (fun k => ?_) d
  have hle : Env.le (DepthEnv.callSlot M Γext G k) (Env.sccStep M (Env.semScc M Γext) Γext) := by
    cases k with
    | zero => exact DepthEnv.extStep_le_sccStep M _ Γext
    | succ _ => exact Env.le_refl _
  refine Env.le_trans ?_ (Env.lfp_pre (LeanQbe.T.sccOp_mono M Γext))
  exact wp_sccOp_biMono M hle (Env.le_refl (DepthEnv.tailSlot M Γext G k))

private theorem unfoldRecBelow_mono_depth {M : Module} {Γext : Env} :
    ∀ {j k : Nat}, j ≤ k → ∀ f as bs xs m Q X,
      Env.unfoldRecBelow M Γext j f as bs xs m Q X →
      Env.unfoldRecBelow M Γext k f as bs xs m Q X
  | _, 0, hjk, f, as, bs, xs, m, Q, X, h => by
      obtain rfl : _ = 0 := Nat.le_zero.mp hjk
      exact h
  | _, k + 1, hjk, f, as, bs, xs, m, Q, X, h => by
      rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
      · exact h
      · exact Or.inl (unfoldRecBelow_mono_depth (Nat.lt_succ_iff.mp hlt) f as bs xs m Q X h)

private theorem sccStep_unfoldRecAt_le (M : Module) (Γext : Env) (d : Nat) :
    Env.le (Env.sccStep M (Env.unfoldRecAt M Γext d) Γext) (Env.unfoldRecAt M Γext d) := by
  rintro f as bs xs m Q X (⟨_, hU⟩ | ⟨hext, hΓ⟩)
  · exact hU
  · exact unfoldRecBelow_mono_depth (Nat.zero_le (d + 1)) f as bs xs m Q X ⟨hext, hΓ⟩

/-- Every depth slice `DepthEnv.semScc M Γext d` refines the `(d + 1)`-step Kleene approximant
`Env.unfoldRecAt M Γext d`. -/
theorem DepthEnv.semScc_le_unfoldRecAt (M : Module) (Γext : Env) (d : Nat) :
    Env.le (DepthEnv.semScc M Γext d) (Env.unfoldRecAt M Γext d) := by
  let U : DepthEnv := fun k => Env.unfoldRecAt M Γext k
  refine DepthEnv.lfp_le (G := U) (fun k => ?_) d
  cases k with
  | zero =>
      rintro f as bs xs m Q X ⟨hsig, fn, hfn, hnm, ha, hr, hwp⟩
      exact Or.inr ⟨hsig, fn, hfn, hnm, ha, hr, hwp⟩
  | succ k =>
      rintro f as bs xs m Q X ⟨hsig, fn, hfn, hnm, ha, hr, hwp⟩
      exact Or.inr ⟨hsig, fn, hfn, hnm, ha, hr,
        wp_env_mono (sccStep_unfoldRecAt_le M Γext k) _ m hwp⟩

/-- Strict (`strict = true`) `ModuleSccOk` embeds directly into `DepthEnv.semScc M Γext
(idx.depth i)` via `DepthEnv.lfp_wf`. -/
theorem DepthEnv.moduleSccOk_strict_le_semScc {ι : Type} {idx : RecIdx ι} {Γrec : ι → Env}
    {Γext : Env} {M : Module} (hM : ModuleSccOk idx Γrec Γext true M) :
    ∀ i, Env.le (Env.restrict (Γrec i) (M.fns.map Fn.sig))
      (DepthEnv.semScc M Γext (idx.depth i)) := by
  refine DepthEnv.lfp_wf_mkSccOp idx.wf idx.depth M Γext (wp_sccOp_biMono M) Γrec ?_
  intro i Γcall _ hrec hext _ _ f as bs xs m Q X ⟨hsig, hΓ⟩
  obtain ⟨fn, hfn, hfeq⟩ := List.mem_map.mp hsig
  rcases Prod.mk.inj hfeq with ⟨rfl, hsig_ab⟩
  rcases Prod.mk.inj hsig_ab with ⟨rfl, rfl⟩
  have hwp := (hM.fnsOk fn hfn).2.2 i xs m Q X hΓ
  refine ⟨hsig, fn, hfn, rfl, rfl, rfl,
    wp_env_mono (fun g as' bs' xs' m' Q' X' hg => ?_) _ m hwp⟩
  rcases hg with ⟨hfns, j, hlt, hst, hΓ'⟩ | ⟨hex, hΓ'⟩
  · rcases hst with hfalse | hdep
    · cases hfalse
    · exact hrec j hlt hdep g as' bs' xs' m' Q' X' ⟨hfns, hΓ'⟩
  · exact hext g as' bs' xs' m' Q' X' ⟨hex, hΓ'⟩

end LeanQbe.T
