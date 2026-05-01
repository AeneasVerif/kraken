/-
Kraken - Helper Theorems
-/

import Kraken.Semantics
import Kraken.Tactics

-- UInt64.ofInt (k : Int) ≠ 0 when k is a natural number with k < 2^64 and k ≠ 0
-- This proof uses only core Lean lemmas (no Batteries/Mathlib)
theorem UInt64_ofInt_natCast_ne_zero (k : Nat) (h_lt : k < 2^64) (h_ne : k ≠ 0) :
    UInt64.ofInt (k : Int) ≠ 0 := by
  simp only [UInt64.ofInt, ne_eq]
  intro h
  have h1 := congrArg UInt64.toNat h
  simp only [UInt64.toNat_ofNat] at h1
  -- Int mod to Nat conversion
  have h_klt : (k : Int) < 2^64 := Int.ofNat_lt.mpr h_lt
  have h_mod : (↑k : Int) % (2^64 : Int) = k := Int.emod_eq_of_lt (Int.natCast_nonneg k) h_klt
  conv at h1 => lhs; rw [show (↑k : Int) % (2^64 : Int) = ↑k from h_mod]
  simp only [Int.toNat_natCast] at h1
  -- h1: (UInt64.ofNat k).toNat = 0 % 2^64
  have h2 : (UInt64.ofNat k).toNat = k % 2^64 := UInt64.toNat_ofNat
  have hkmod : k % 2^64 = k := Nat.mod_eq_of_lt h_lt
  have hzero : (0 : Nat) % 2^64 = 0 := Nat.zero_mod (2^64)
  rw [h2, hkmod, hzero] at h1
  exact h_ne h1

-- ============================================================================
-- Omnisemantics Step Mixing
-- ============================================================================

theorem step_interp_eq [Layout] (p: Executable) (pc: Int64) (s: MachineData) (d: Directive) (sz: Nat) (ds: List (Directive × Nat)) (post: MachineState → Prop) [L : Labels]:
  L = p.labels →
  p.directivesFromAddress pc = (d, sz) :: ds →
  (Executable.step p (s, pc) (fun s' => post s') ↔
   d.interp s (.mk pc (pc+.ofNat sz)) (jmp:=fun pc' s' => post (s', pc')) (next := fun s' => post (s', pc+.ofNat sz))) := by
  intros h_labels h_from
  unfold Executable.step
  -- not true. directives could share an address
  have h_at : p.directivesAtAddress pc = [(d, sz)] := by
    sorry
  rw [h_at]
  dsimp [Directives.interp]
  rw [h_labels]


theorem directivesFromAddress_tail [Layout] (p: Executable) (pc: Int64) (d: Directive) (sz: Nat) (ds: List (Directive × Nat)):
  p.directivesFromAddress pc = (d, sz) :: ds →
  p.directivesFromAddress (pc + .ofNat sz) = ds := by
  sorry

theorem directive_interp_mono (d : Directive) (s : MachineData) (p : Std.Rco Int64)
  {next1 next2 : MachineData → Prop} {jmp1 jmp2 : Int64 → MachineData → Prop}
  [Labels]
  (h : Directive.interp d s p next1 jmp1)
  (h_next : ∀ s', next1 s' → next2 s')
  (h_jmp : ∀ pc' s', jmp1 pc' s' → jmp2 pc' s') :
  Directive.interp d s p next2 jmp2 := by
  cases d with
  | label l =>
      dsimp [Directive.interp] at h ⊢
      apply h_next
      exact h
  | instr i =>
      sorry -- Requires monotonicity of Instr.interp and Operation.interp
  | byteArray bs =>
      dsimp [Directive.interp] at h ⊢
      exact h

theorem straightline_to_step1 [Layout] (p: Executable) (initial: MachineState) (post: Post):
  straightline_step p initial post → Eventually (step1 p) post initial := by
  intro h
  unfold straightline_step at h
  unfold Executable.straightline at h
  let _labels : Labels := p.labels
  have h_gen : ∀ (ds : List (Directive × Nat)) (s : MachineData) (pc : Int64),
    ds = p.directivesFromAddress pc →
    Directives.interp ds s pc (fun pc' s' => post (s', pc')) →
    Eventually (step1 p) post (s, pc) := by
    intro ds
    induction ds with
    | nil =>
        intros s pc h_eq h_nil
        dsimp [Directives.interp] at h_nil
        apply Eventually.done
        exact h_nil
    | cons d_sz ds' ih =>
        intros s pc h_eq h_cons
        dsimp [Directives.interp] at h_cons
        obtain ⟨d, sz⟩ := d_sz
        let mid_p := fun (mid : MachineState) =>
          post mid ∨ (mid.2 = pc + .ofNat sz ∧ Directives.interp ds' mid.1 mid.2 (fun pc' s' => post (s', pc')))
        apply Eventually.step (s, pc) mid_p
        · -- Prove step1 p (s, pc) mid_p
          unfold step1
          have h_iff := @step_interp_eq _ p pc s d sz ds' mid_p p.labels (by rfl) h_eq.symm
          rw [h_iff]
          apply directive_interp_mono d s (.mk pc (pc+.ofNat sz)) h_cons
          · intros s' h_next_in
            unfold mid_p
            right
            exact ⟨rfl, h_next_in⟩
          · intros pc' s' h_jmp_in
            unfold mid_p
            left
            exact h_jmp_in
        · -- Prove ∀ mid, mid_p mid → Eventually (step1 p) post mid
          intros mid h_mid
          cases h_mid with
          | inl h_post =>
              apply Eventually.done
              exact h_post
          | inr h_and =>
              obtain ⟨h_mid2, h_interp⟩ := h_and
              have h_eq_next : ds' = p.directivesFromAddress mid.2 := by
                rw [h_mid2]
                exact (directivesFromAddress_tail p pc d sz ds' h_eq.symm).symm
              apply ih mid.1 mid.2 h_eq_next
              exact h_interp
  apply h_gen (p.directivesFromAddress initial.2) initial.1 initial.2 (by rfl)
  exact h

theorem eventually_straightline_to_step1 [Layout] (p: Executable) (initial: MachineState) (post: Post)
  (h: Eventually (straightline_step p) post initial):
  Eventually (step1 p) post initial := by
  induction h with
  | done initial h_post =>
      apply Eventually.done
      assumption
  | step initial mid_p h_step h_rest ih =>
      have h_ev := straightline_to_step1 p initial mid_p h_step
      apply eventually_trans (step1 p) mid_p post initial h_ev ih
