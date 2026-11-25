module

public import LeanQbe.T.Xcap.Lfp

/-!
# Generic XCAP Core over Arbitrary Machine State (`Xcap.Core`)

Target-neutral XCAP weakest-precondition core parameterized over an arbitrary state `σ` and
block type `Blk`, shared across L0 (`BedrockWord`) and L1 (`BedrockMach`) without importing
`Kraken.X64` or `Kraken.AArch64`:

* `Out`, `Mach`, `Code`, `CodeSpec`, `Halt`, `cptr`.
* `bwp`, `Closed`, `wp` (connected to `Xcap.Lfp.lfp` via `step` and `wp_eq_lfp`).
* `Halts`, `Safe`, `adequacy`, `wp_block`, and `wp_of_ranked`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Xcap

universe u v

/-- Block execution outcome: jump to a code word, or halt with an exit word. -/
inductive Out (σ : Type u) : Type u where
  | jump (pc : BitVec 64) (s : σ)
  | halt (c : BitVec 64) (s : σ)

/-- Abstract machine: (possibly nondeterministic) block execution relation. -/
structure Mach (σ : Type u) (Blk : Type v) : Type (max u v) where
  exec : Blk → σ → Out σ → Prop

/-- Address-indexed map of basic blocks. -/
abbrev Code (Blk : Type v) : Type v := BitVec 64 → Option Blk

/-- Code specification assigning a state precondition to each code address. -/
abbrev CodeSpec (σ : Type u) : Type u := BitVec 64 → σ → Prop

/-- Halt postcondition indexed by exit code and final state. -/
abbrev Halt (σ : Type u) : Type u := BitVec 64 → σ → Prop

section
variable {σ : Type u} {Blk : Type v}

/-- Impredicative XCAP code pointer: `p` may be entered in any state satisfying `P`. -/
@[expose] def cptr (Ψ : CodeSpec σ) (p : BitVec 64) (P : σ → Prop) : Prop :=
  ∀ s, P s → Ψ p s

/-- Block weakest precondition, derived directly from `M.exec`. -/
@[expose] def bwp (M : Mach σ Blk) (b : Blk) (Ψ : CodeSpec σ) (H : Halt σ) (s : σ) : Prop :=
  (∃ o, M.exec b s o) ∧
    (∀ pc s', M.exec b s (.jump pc s') → Ψ pc s') ∧
    (∀ c s', M.exec b s (.halt c s') → H c s')

/-- Monotonicity of `bwp` in `Ψ`. -/
theorem bwp_mono (M : Mach σ Blk) (b : Blk) (H : Halt σ) {Ψ₁ Ψ₂ : CodeSpec σ}
    (hΨ : ∀ pc s, Ψ₁ pc s → Ψ₂ pc s) {s : σ} (hb : bwp M b Ψ₁ H s) :
    bwp M b Ψ₂ H s :=
  ⟨hb.1, fun pc s' hx => hΨ pc s' (hb.2.1 pc s' hx), hb.2.2⟩

/-- One-step transformer on `BitVec 64 × σ` matching `Closed`. -/
@[expose] def step (M : Mach σ Blk) (cm : Code Blk) (H : Halt σ)
    (Ψ : Lfp.Pred (BitVec 64 × σ)) : Lfp.Pred (BitVec 64 × σ) :=
  fun p => ∃ b, cm p.1 = some b ∧ bwp M b (fun pc s => Ψ (pc, s)) H p.2

/-- Monotonicity of `step` for `Xcap.Lfp`. -/
theorem step_mono (M : Mach σ Blk) (cm : Code Blk) (H : Halt σ) :
    Lfp.mono (step M cm H) := by
  rintro Ψ₁ Ψ₂ hle ⟨pc, s⟩ ⟨b, hb, hbw⟩
  exact ⟨b, hb, bwp_mono M b H (fun pc' s' h => hle (pc', s') h) hbw⟩

/-- `Ψ` is closed under the code map `cm` (pre-fixed point of `step M cm H`). -/
@[expose] def Closed (M : Mach σ Blk) (cm : Code Blk) (Ψ : CodeSpec σ) (H : Halt σ) : Prop :=
  ∀ pc b, cm pc = some b → ∀ s, bwp M b Ψ H s → Ψ pc s

/-- Code-map weakest precondition as the least closed spec (Knaster–Tarski, zero step-index). -/
@[expose] def wp (M : Mach σ Blk) (cm : Code Blk) (H : Halt σ) (pc : BitVec 64) (s : σ) :
    Prop :=
  ∀ Ψ, Closed M cm Ψ H → Ψ pc s

/-- Equivalence between `Xcap.wp` and `Lfp.lfp (step M cm H)`. -/
theorem wp_eq_lfp (M : Mach σ Blk) (cm : Code Blk) (H : Halt σ) (pc : BitVec 64) (s : σ) :
    wp M cm H pc s ↔ Lfp.lfp (step M cm H) (pc, s) := by
  constructor
  · intro h P hcl
    have hcl' : Closed M cm (fun pc' s' => P (pc', s')) H :=
      fun pc' b hb s' hbw => hcl (pc', s') ⟨b, hb, hbw⟩
    exact h (fun pc' s' => P (pc', s')) hcl'
  · intro h Ψ hcl
    have hcl' : Lfp.Closed (step M cm H) (fun p => Ψ p.1 p.2) := by
      rintro ⟨pc', s'⟩ ⟨b, hb, hbw⟩
      exact hcl pc' b hb s' hbw
    exact h (fun p => Ψ p.1 p.2) hcl'

/-- Big-step halting operational semantics over `cm`. -/
inductive Halts (M : Mach σ Blk) (cm : Code Blk) :
    BitVec 64 → σ → BitVec 64 → σ → Prop where
  | halt {pc b s c s'} :
      cm pc = some b → M.exec b s (.halt c s') → Halts M cm pc s c s'
  | jump {pc b s pc' s' c s''} :
      cm pc = some b → M.exec b s (.jump pc' s') →
      Halts M cm pc' s' c s'' → Halts M cm pc s c s''

/-- Total-correctness safety: every execution path halts in `H`. -/
inductive Safe (M : Mach σ Blk) (cm : Code Blk) (H : Halt σ) :
    BitVec 64 → σ → Prop where
  | step {pc b s} :
      cm pc = some b → (∃ o, M.exec b s o) →
      (∀ pc' s', M.exec b s (.jump pc' s') → Safe M cm H pc' s') →
      (∀ c s', M.exec b s (.halt c s') → H c s') → Safe M cm H pc s

theorem Safe.closed (M : Mach σ Blk) (cm : Code Blk) (H : Halt σ) :
    Closed M cm (Safe M cm H) H :=
  fun _ _ hb _ ⟨he, hj, hh⟩ => .step hb he hj hh

theorem Safe.halts {M : Mach σ Blk} {cm : Code Blk} {H : Halt σ} {pc : BitVec 64} {s : σ}
    (h : Safe M cm H pc s) : ∃ c s', Halts M cm pc s c s' ∧ H c s' := by
  induction h with
  | @step pc b s hb he _ hh ih =>
    obtain ⟨o, ho⟩ := he
    cases o with
    | jump pc' s' =>
      obtain ⟨c, s'', h1, h2⟩ := ih pc' s' ho
      exact ⟨c, s'', .jump hb ho h1, h2⟩
    | halt c s' => exact ⟨c, s', .halt hb ho, hh c s' ho⟩

/-- Adequacy: `wp` implies every run terminates in a state satisfying `H`. -/
theorem adequacy {M : Mach σ Blk} {cm : Code Blk} {H : Halt σ} {pc : BitVec 64} {s : σ}
    (h : wp M cm H pc s) : ∃ c s', Halts M cm pc s c s' ∧ H c s' :=
  (h _ (Safe.closed M cm H)).halts

/-- One-block unfolding rule for verifying basic blocks. -/
theorem wp_block {M : Mach σ Blk} {cm : Code Blk} {H : Halt σ} {pc : BitVec 64} {b : Blk}
    {s : σ} (hb : cm pc = some b) (he : ∃ o, M.exec b s o)
    (hj : ∀ pc' s', M.exec b s (.jump pc' s') → wp M cm H pc' s')
    (hh : ∀ c s', M.exec b s (.halt c s') → H c s') : wp M cm H pc s :=
  fun Ψ hcl => hcl pc b hb s ⟨he, fun pc' s' h => hj pc' s' h Ψ hcl, hh⟩

/-- `Nat`-ranked invariant rule via `Xcap.Lfp.lfp_of_ranked` for loops and cyclic SCCs. -/
theorem wp_of_ranked {M : Mach σ Blk} {cm : Code Blk} {H : Halt σ} (I : Nat → CodeSpec σ)
    (hI : ∀ n pc s, I n pc s → ∃ b, cm pc = some b ∧
      bwp M b (fun pc' s' => ∃ k, k < n ∧ I k pc' s') H s) :
    ∀ n pc s, I n pc s → wp M cm H pc s := by
  intro n pc s hi
  refine (wp_eq_lfp M cm H pc s).2 ?_
  exact Lfp.lfp_of_ranked (step_mono M cm H) (fun k p => I k p.1 p.2)
    (fun k ⟨pc', s'⟩ h => hI k pc' s' h) n (pc, s) hi

end

end LeanQbe.T.Xcap
