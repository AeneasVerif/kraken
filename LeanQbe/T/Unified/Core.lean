module

/-!
# Generic Tiers, Checked Stages, and Passes (`Unified.Core`)

Universe-polymorphic refinement spine shared across all frontends and backends:

* `Tier`: IR program type, well-formedness invariant `Ok`, specification `Spec`, and `Sat`.
* `bindE`: universe-polymorphic `Except String` bind.
* `Stage`: checked, spec-translating compilation stage with sequential composition `Stage.comp`
  (`≫`).
* `Pass`: total, spec-preserving optimization pass with `Pass.toStage`, `Pass.seq`, and
  capability-gated `Pass.gate` (`Pass.gate_off`).
* `Stage.mapM` / `Stage.mapM_sound`: per-function module lifting preserving pointwise specs.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Unified

universe u v u₁ v₁ u₂ v₂ u₃ v₃

/-- An IR tier: programs, a well-formedness invariant, specs (with `top` for failed runs),
and a semantic satisfaction relation (`Sat p s`). -/
structure Tier : Type (max (u + 1) (v + 1)) where
  Prog : Type u
  Ok : Prog → Prop
  Spec : Type v
  top : Spec
  Sat : Prog → Spec → Prop

/-- Universe-polymorphic `Except String` bind (source and target tiers may live in different
universes). -/
@[expose] def bindE {α : Type u} {β : Type v} :
    Except String α → (α → Except String β) → Except String β
  | .ok a, f => f a
  | .error e, _ => .error e

theorem bindE_ok {α : Type u} {β : Type v} {x : Except String α} {f : α → Except String β}
    {c : β} (h : bindE x f = .ok c) : ∃ b, x = .ok b ∧ f b = .ok c := by
  cases x with
  | error e => cases h
  | ok b => exact ⟨b, rfl, h⟩

/-- A checked, spec-translating compilation stage from tier `A` to tier `B`. -/
structure Stage (A : Tier.{u₁, v₁}) (B : Tier.{u₂, v₂}) :
    Type (max u₁ v₁ u₂ v₂) where
  run : A.Prog → Except String B.Prog
  tr : A.Prog → A.Spec → B.Spec
  ok : ∀ p q, A.Ok p → run p = .ok q → B.Ok q
  sound : ∀ p q s, A.Ok p → run p = .ok q → A.Sat p s → B.Sat q (tr p s)

/-- Sequential composition of stages (`s₁ ≫ s₂`); soundness is proved once here. -/
@[expose] def Stage.comp {A : Tier.{u₁, v₁}} {B : Tier.{u₂, v₂}} {C : Tier.{u₃, v₃}}
    (s₁ : Stage A B) (s₂ : Stage B C) : Stage A C where
  run p := bindE (s₁.run p) s₂.run
  tr p s := match s₁.run p with
    | .ok q => s₂.tr q (s₁.tr p s)
    | .error _ => C.top
  ok p r hp h := by
    obtain ⟨q, hq, hr⟩ := bindE_ok h
    exact s₂.ok q r (s₁.ok p q hp hq) hr
  sound p r s hp h hs := by
    obtain ⟨q, hq, hr⟩ := bindE_ok h
    have h2 := s₂.sound q r (s₁.tr p s) (s₁.ok p q hp hq) hr (s₁.sound p q s hp hq hs)
    simp only [hq]
    exact h2

infixr:60 " ≫ " => Stage.comp

/-- A same-tier, total, spec-preserving optimization pass (matching `Func.X_wf`/`X_spec`). -/
structure Pass (A : Tier.{u, v}) : Type (max u v) where
  run : A.Prog → A.Prog
  ok : ∀ p, A.Ok p → A.Ok (run p)
  sound : ∀ p s, A.Ok p → A.Sat p s → A.Sat (run p) s

/-- Lift a total `Pass A` to a `Stage A A` with identity spec translation. -/
@[expose] def Pass.toStage {A : Tier.{u, v}} (P : Pass A) : Stage A A where
  run p := .ok (P.run p)
  tr _ s := s
  ok p q hp h := by cases h; exact P.ok p hp
  sound p q s hp h hs := by cases h; exact P.sound p s hp hs

/-- Sequential composition of passes (left to right). -/
@[expose] def Pass.seq {A : Tier.{u, v}} : List (Pass A) → Pass A
  | [] => ⟨id, fun _ h => h, fun _ _ _ h => h⟩
  | P :: Ps =>
    let R := Pass.seq Ps
    ⟨fun p => R.run (P.run p), fun p h => R.ok _ (P.ok p h),
      fun p s h hs => R.sound _ s (P.ok p h) (P.sound p s h hs)⟩

/-- Capability-gated pass: runs `P` iff `c p = true`, and is the identity otherwise. -/
@[expose] def Pass.gate {A : Tier.{u, v}} (c : A.Prog → Bool) (P : Pass A) : Pass A where
  run p := if c p then P.run p else p
  ok p h := by
    cases hc : c p
    · simpa using h
    · simpa using P.ok p h
  sound p s h hs := by
    cases hc : c p
    · simpa using hs
    · simpa using P.sound p s h hs

theorem Pass.gate_off {A : Tier.{u, v}} (c : A.Prog → Bool) (P : Pass A) (p : A.Prog)
    (h : c p = false) : (Pass.gate c P).run p = p := by
  simp [Pass.gate, h]

/-- Per-function module lifting of a `Stage`. -/
@[expose] def Stage.mapM {A : Tier.{u₁, v₁}} {B : Tier.{u₂, v₂}} (st : Stage A B) :
    List A.Prog → Except String (List B.Prog)
  | [] => .ok []
  | p :: ps => bindE (st.run p) fun q => bindE (st.mapM ps) fun qs => .ok (q :: qs)

theorem Stage.mapM_cons_ok {A : Tier.{u₁, v₁}} {B : Tier.{u₂, v₂}} (st : Stage A B) (p : A.Prog)
    (ps : List A.Prog) (r : List B.Prog) (h : st.mapM (p :: ps) = .ok r) :
    ∃ q qs, st.run p = .ok q ∧ st.mapM ps = .ok qs ∧ r = q :: qs := by
  simp only [Stage.mapM] at h
  obtain ⟨q, hq, h⟩ := bindE_ok h
  obtain ⟨qs, hqs, h⟩ := bindE_ok h
  cases h
  exact ⟨q, qs, hq, hqs, rfl⟩

/-- Pointwise soundness of per-function lifting `Stage.mapM`. -/
theorem Stage.mapM_sound {A : Tier.{u₁, v₁}} {B : Tier.{u₂, v₂}} (st : Stage A B)
    (S : A.Prog → A.Spec) :
    ∀ (ps : List A.Prog) (qs : List B.Prog),
      (∀ p ∈ ps, A.Ok p) → (∀ p ∈ ps, A.Sat p (S p)) → st.mapM ps = .ok qs →
      ∀ q ∈ qs, ∃ p ∈ ps, st.run p = .ok q ∧ B.Ok q ∧ B.Sat q (st.tr p (S p))
  | [], qs, _, _, h => by cases h; intro q hq; cases hq
  | p :: ps, r, hok, hsat, h => by
    obtain ⟨q, qs, hq, hqs, rfl⟩ := st.mapM_cons_ok p ps r h
    intro q' hq'
    rcases List.mem_cons.1 hq' with rfl | hq'
    · exact ⟨p, List.mem_cons_self, hq, st.ok p q' (hok p List.mem_cons_self) hq,
        st.sound p q' (S p) (hok p List.mem_cons_self) hq (hsat p List.mem_cons_self)⟩
    · obtain ⟨p', hp', h1, h2, h3⟩ := st.mapM_sound S ps qs
        (fun x hx => hok x (List.mem_cons_of_mem _ hx))
        (fun x hx => hsat x (List.mem_cons_of_mem _ hx)) hqs q' hq'
      exact ⟨p', List.mem_cons_of_mem _ hp', h1, h2, h3⟩

end LeanQbe.T.Unified
