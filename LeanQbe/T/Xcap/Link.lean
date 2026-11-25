module

public import LeanQbe.T.Xcap.Core

/-!
# Generic Open-Module XCAP Linking (`Xcap.Link`)

Horizontal module composition and `Ψ`-indexed calling convention over `Xcap.Core`:

* `Sub`, `union`, `Closed.sub`.
* `Iface` (`Ψ`-indexed entry preconditions), `callPre` (generic return-pointer `cptr`
  precondition shared between L0 `rp` and L1 `x30`/`[rsp]`).
* `ModOk`, `ModOk.link` (DAG composition), `ModOk.close` (closed-program `wp`), and
  `ModOk.weaken`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Xcap

universe u v

section
variable {σ : Type u} {Blk : Type v}

/-- Code-map inclusion: every block mapped by `c₁` is mapped identically by `c₂`. -/
@[expose] def Sub (c₁ c₂ : Code Blk) : Prop :=
  ∀ pc b, c₁ pc = some b → c₂ pc = some b

/-- Left-biased union of two code maps (used on disjoint modules). -/
@[expose] def union (c₁ c₂ : Code Blk) : Code Blk :=
  fun pc => (c₁ pc).or (c₂ pc)

theorem Sub.refl (c : Code Blk) : Sub c c :=
  fun _ _ h => h

theorem Sub.trans {c₁ c₂ c₃ : Code Blk} (h₁ : Sub c₁ c₂) (h₂ : Sub c₂ c₃) : Sub c₁ c₃ :=
  fun pc b hb => h₂ pc b (h₁ pc b hb)

theorem Closed.sub {M : Mach σ Blk} {c₁ c₂ : Code Blk} {Ψ : CodeSpec σ} {H : Halt σ}
    (hs : Sub c₁ c₂) (h : Closed M c₂ Ψ H) : Closed M c₁ Ψ H :=
  fun pc b hb => h pc b (hs pc b hb)

/-- Module interface: `(entryPc, Ψ-indexed precondition)` pairs so preconditions may carry
continuation code pointers (`cptr Ψ rp Post`). -/
abbrev Iface (σ : Type u) : Type u :=
  List (BitVec 64 × (CodeSpec σ → σ → Prop))

/-- Shared XCAP call precondition: `Pre s` holds and the return address `rpOf s` is a valid
code pointer at postcondition `Post`. -/
@[expose] def callPre (rpOf : σ → BitVec 64) (Pre Post : σ → Prop) : CodeSpec σ → σ → Prop :=
  fun Ψ s => Pre s ∧ cptr Ψ (rpOf s) Post

/-- Open-module correctness: in every closed host `big` containing `cm`, satisfying `imps`
as `cptr`s implies `exps` hold as `cptr`s. -/
@[expose] def ModOk (M : Mach σ Blk) (cm : Code Blk) (H : Halt σ)
    (imps exps : Iface σ) : Prop :=
  ∀ (big : Code Blk) (Ψ : CodeSpec σ), Sub cm big → Closed M big Ψ H →
    (∀ e ∈ imps, cptr Ψ e.1 (e.2 Ψ)) → ∀ e ∈ exps, cptr Ψ e.1 (e.2 Ψ)

/-- Weakening imports and exports of `ModOk`. -/
theorem ModOk.weaken {M : Mach σ Blk} {cm : Code Blk} {H : Halt σ}
    {i₁ e₁ i₂ e₂ : Iface σ} (h : ModOk M cm H i₁ e₁)
    (hi : ∀ e ∈ i₁, e ∈ i₂) (he : ∀ e ∈ e₂, e ∈ e₁) :
    ModOk M cm H i₂ e₂ :=
  fun big Ψ hs hcl himp e hmem => h big Ψ hs hcl (fun x hx => himp x (hi x hx)) e (he e hmem)

/-- DAG horizontal linking of two disjoint open modules `c₁` and `c₂`. -/
theorem ModOk.link {M : Mach σ Blk} {c₁ c₂ : Code Blk} {H : Halt σ}
    {i₁ e₁ i₂ e₂ : Iface σ} (h₁ : ModOk M c₁ H i₁ e₁) (h₂ : ModOk M c₂ H i₂ e₂)
    (hdisj : ∀ pc, c₁ pc = none ∨ c₂ pc = none)
    (himp : ∀ e ∈ i₂, e ∈ e₁ ∨ e ∈ i₁) :
    ModOk M (union c₁ c₂) H i₁ (e₁ ++ e₂) := by
  intro big Ψ hs hcl hi e he
  have hs₁ : Sub c₁ big := fun pc b hb => hs pc b (by simp [union, hb])
  have hs₂ : Sub c₂ big := fun pc b hb => hs pc b (by
    rcases hdisj pc with h | h
    · simp [union, h, hb]
    · rw [h] at hb; cases hb)
  have hx₁ := h₁ big Ψ hs₁ hcl hi
  rcases List.mem_append.1 he with he | he
  · exact hx₁ e he
  · refine h₂ big Ψ hs₂ hcl (fun e' he' => ?_) e he
    rcases himp e' he' with h | h
    · exact hx₁ e' h
    · exact hi e' h

/-- Closing an open module with empty imports yields `Xcap.wp` for every exported entry. -/
theorem ModOk.close {M : Mach σ Blk} {cm : Code Blk} {H : Halt σ} {exps : Iface σ}
    (h : ModOk M cm H [] exps) {e : BitVec 64 × (CodeSpec σ → σ → Prop)} (he : e ∈ exps)
    {s : σ} (hs : ∀ Ψ, e.2 Ψ s) : wp M cm H e.1 s :=
  fun Ψ hcl => h cm Ψ (Sub.refl cm) hcl (fun _ h => nomatch h) e he s (hs Ψ)

end

end LeanQbe.T.Xcap
