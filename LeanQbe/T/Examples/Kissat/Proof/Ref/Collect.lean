/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Collect
public import LeanQbe.T.Examples.Kissat.Proof.Ref.Reduce

/-!
# Soundness Proofs for `Collect`

Extracted pure-Lean proofs for `Collect` (zero `Kraken.*` imports).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. Shared `Array.push` relocation helpers -/

private theorem push_nonmoved_bound {tgts : Array RefTarget} {sz : Nat} {x : RefTarget}
    (hx : ∀ nid, x ≠ RefTarget.moved nid)
    (hb : ∀ (k nid : Nat), tgts[k]? = some (RefTarget.moved nid) → nid < sz) :
    ∀ (k nid : Nat), (tgts.push x)[k]? = some (RefTarget.moved nid) → nid < sz := by
  intro k nid hk
  simp only [Array.getElem?_push] at hk
  split at hk
  · cases hk with | refl => exact absurd rfl (hx nid)
  · exact hb k nid hk

private theorem push_nonmoved_inj {tgts : Array RefTarget} {x : RefTarget}
    (hx : ∀ nid, x ≠ RefTarget.moved nid)
    (hinj : ∀ (i j nid : Nat), tgts[i]? = some (RefTarget.moved nid) →
      tgts[j]? = some (RefTarget.moved nid) → i = j) :
    ∀ (i j nid : Nat), (tgts.push x)[i]? = some (RefTarget.moved nid) →
      (tgts.push x)[j]? = some (RefTarget.moved nid) → i = j := by
  intro i j nid hi hj
  simp only [Array.getElem?_push] at hi hj
  split at hi <;> split at hj
  · cases hi with | refl => exact absurd rfl (hx nid)
  · cases hi with | refl => exact absurd rfl (hx nid)
  · cases hj with | refl => exact absurd rfl (hx nid)
  · exact hinj i j nid hi hj

private theorem push_raw_none_bound {b : Bool} {raw : Array (Option (Bool × Nat))} {sz : Nat}
    (hb : ∀ (k i : Nat), raw[k]? = some (some (b, i)) → i < sz) :
    ∀ (k i : Nat), (raw.push none)[k]? = some (some (b, i)) → i < sz := by
  intro k i hk
  simp only [Array.getElem?_push] at hk
  split at hk
  · cases hk
  · exact hb k i hk

private theorem push_raw_none_inj {raw : Array (Option (Bool × Nat))}
    (hinj : ∀ (j1 j2 : Nat) (b : Bool) (i : Nat),
      raw[j1]? = some (some (b, i)) → raw[j2]? = some (some (b, i)) → j1 = j2) :
    ∀ (j1 j2 : Nat) (b : Bool) (i : Nat), (raw.push none)[j1]? = some (some (b, i)) →
      (raw.push none)[j2]? = some (some (b, i)) → j1 = j2 := by
  intro j1 j2 b i h1 h2
  simp only [Array.getElem?_push] at h1 h2
  split at h1 <;> split at h2 <;> first | cases h1 | cases h2 | exact hinj j1 j2 b i h1 h2

/-! ## 2. Kissat `sparse_sweep_garbage_clauses` (`collect.c:277-460`) with binary promotion -/

theorem isRootFalse_entailed {s : CdclState} (hinv : LazyTrailInv s) {l : Nat}
    (h : isRootFalse s l = true) : s.f0.EntailsClause (cnfClause [litNeg l]) := by
  unfold isRootFalse at h
  simp only [Bool.and_eq_true, trailHasLit_iff, beq_iff_eq] at h
  obtain ⟨i, hi, hieq⟩ := trail_mem_iff_exists.mp h.1
  have hl0 : stateLevel s s.trail[i] = 0 := by
    rw [hieq, stateLevel_litNeg]; exact h.2
  have hent := lazyTrailEntailment_level0 hinv hi hl0
  rwa [hieq] at hent

/-- Kissat `collect.c:411` assertion (`assert (!dst->reason)`): no active `.large` reason clause
with positive decision level contains a root-satisfied literal. -/
theorem activeReason_not_rootSatisfied {s : CdclState} (hinv : LazyTrailInv s)
    (hpos : ReasonLevelsPos s) {i : Nat} (hi : i < s.trail.size) {cid : Nat} {c : Clause}
    (hrsn : stateReason s s.trail[i] = .large cid)
    (hget : s.clauses[cid]? = some (some c)) :
    c.lits.any (isRootTrue s) = false := by
  apply Bool.eq_false_iff.mpr
  intro hany
  rw [List.any_eq_true] at hany
  obtain ⟨y, hy, hyt⟩ := hany
  unfold isRootTrue at hyt
  simp only [Bool.and_eq_true, trailHasLit_iff, beq_iff_eq] at hyt
  have hrd := hinv.reason_dag i hi
  dsimp only at hrd
  rw [hrsn] at hrd
  obtain ⟨c0, hget0, _, _, hall0⟩ := hrd
  have hc0 : c = c0 := by rw [hget] at hget0; injection hget0 with h1; injection h1
  subst hc0
  by_cases hyeq : y = s.trail[i]
  · have hlpos := hpos i hi cid hrsn
    rw [hyeq] at hyt
    omega
  · obtain ⟨j, hj, _, hjeq, _, _⟩ := hall0 y hy hyeq
    obtain ⟨k, hk, hkeq⟩ := trail_mem_iff_exists.mp hyt.1
    have hkj := hinv.vars_nodup k j hk hj (by rw [hkeq, hjeq, litVar_litNeg])
    subst hkj
    rw [hkeq] at hjeq
    exact litNeg_ne_self y hjeq.symm

/-- Kissat `collect.c:422` assertion (`assert (new_size > 1)`): under `LazyTrailInv` and
`ReasonHasNonRootAntecedent`, stripping root-falsified literals from an active `.large` reason
clause leaves `s.trail[i]` and at least one distinct literal `y`, so length is `≥ 2` and any
surviving size-2 list `[a, b]` satisfies `a ≠ b`. -/
theorem activeReason_stripped_size_ge_two {s : CdclState} (hinv : LazyTrailInv s)
    (hnonroot : ReasonHasNonRootAntecedent s) {i : Nat} (hi : i < s.trail.size)
    {cid : Nat} {c : Clause} (hrsn : stateReason s s.trail[i] = .large cid)
    (hget : s.clauses[cid]? = some (some c)) :
    let lits' := stripFalsified (isRootFalse s) c.lits
    s.trail[i] ∈ lits' ∧
    (∃ y ∈ lits', y ≠ s.trail[i]) ∧
    2 ≤ lits'.length ∧
    (∀ a b, lits' = [a, b] → a ≠ b) := by
  have hrd := hinv.reason_dag i hi
  dsimp only at hrd
  rw [hrsn] at hrd
  obtain ⟨c0, hget0, _, htr_mem, hall0⟩ := hrd
  have hc0 : c = c0 := by rw [hget] at hget0; injection hget0 with h1; injection h1
  subst hc0
  have htr_nrf : isRootFalse s s.trail[i] = false := by
    apply Bool.eq_false_iff.mpr
    intro hrf
    unfold isRootFalse at hrf
    simp only [Bool.and_eq_true, trailHasLit_iff] at hrf
    obtain ⟨k, hk, hkeq⟩ := trail_mem_iff_exists.mp hrf.1
    have hki := hinv.vars_nodup k i hk hi (by rw [hkeq, litVar_litNeg])
    subst hki
    exact litNeg_ne_self s.trail[k] hkeq.symm
  have htr_strip : s.trail[i] ∈ stripFalsified (isRootFalse s) c.lits := by
    simp [stripFalsified, htr_mem, htr_nrf]
  obtain ⟨y, hy, hyne, hypos⟩ := hnonroot i hi cid c hrsn hget
  have hy_nrf : isRootFalse s y = false := by
    apply Bool.eq_false_iff.mpr
    intro hrf
    unfold isRootFalse at hrf
    simp only [Bool.and_eq_true, beq_iff_eq] at hrf
    omega
  have hy_strip : y ∈ stripFalsified (isRootFalse s) c.lits := by
    simp [stripFalsified, hy, hy_nrf]
  have hlen : 2 ≤ (stripFalsified (isRootFalse s) c.lits).length := by
    cases hst : stripFalsified (isRootFalse s) c.lits with
    | nil => rw [hst] at htr_strip; cases htr_strip
    | cons a as =>
      cases as with
      | nil =>
        rw [hst] at htr_strip hy_strip
        simp only [List.mem_singleton] at htr_strip hy_strip
        exact absurd (hy_strip.trans htr_strip.symm) hyne
      | cons b bs => simp
  refine ⟨htr_strip, ⟨y, hy_strip, hyne⟩, hlen, fun a b heq => ?_⟩
  intro hab
  subst hab
  rw [heq] at htr_strip hy_strip
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at htr_strip hy_strip
  exact hyne (hy_strip.trans htr_strip.symm)

private structure SweepAccInv (s : CdclState) (acc : Array (Option Clause))
    (bins : List (Nat × Nat)) (tgts : Array RefTarget) : Prop where
  bound : ∀ (k nid : Nat), tgts[k]? = some (RefTarget.moved nid) → nid < acc.size
  inj : ∀ (i j nid : Nat), tgts[i]? = some (RefTarget.moved nid) →
    tgts[j]? = some (RefTarget.moved nid) → i = j
  clauses_ok : ∀ (k : Nat) (c' : Clause), acc[k]? = some (some c') →
    !c'.garbage = true ∧ s.f0.EntailsClause (cnfClause c'.lits)
  bins_ok : ∀ p ∈ bins, s.f0.EntailsClause (cnfClause [p.1, p.2])

private theorem sweepClauseStep_mono (s : CdclState) (acc : Array (Option Clause))
    (bins : List (Nat × Nat)) (tgts : Array RefTarget) (opt : Option Clause) :
    let res := sweepClauseStep s acc bins tgts opt
    tgts.size ≤ res.2.2.size ∧ acc.size ≤ res.1.size ∧
    (∀ p ∈ bins, p ∈ res.2.1) ∧
    (∀ k, k < tgts.size → res.2.2[k]? = tgts[k]?) ∧
    (∀ k, k < acc.size → res.1[k]? = acc[k]?) := by
  cases opt with
  | none =>
    unfold sweepClauseStep
    refine ⟨by simp, Nat.le_refl _, fun _ hp => hp, fun k hk => ?_, fun _ _ => rfl⟩
    simp [Array.getElem?_push, Nat.ne_of_lt hk]
  | some c =>
    unfold sweepClauseStep
    by_cases hdrop : (c.garbage || c.lits.any (isRootTrue s)) = true
    · simp only [hdrop, ↓reduceIte]
      refine ⟨by simp, Nat.le_refl _, fun _ hp => hp, fun k hk => ?_, fun _ _ => trivial⟩
      simp [Array.getElem?_push, Nat.ne_of_lt hk]
    · have hdrop_f : (c.garbage || c.lits.any (isRootTrue s)) = false :=
        Bool.eq_false_iff.mpr hdrop
      simp only [hdrop_f, Bool.false_eq_true, ↓reduceIte]
      cases hst : stripFalsified (isRootFalse s) c.lits with
      | nil =>
        refine ⟨by simp, by simp, fun _ hp => hp, fun k hk => ?_, fun k hk => ?_⟩ <;>
          simp [Array.getElem?_push, Nat.ne_of_lt hk]
      | cons a as =>
        cases as with
        | nil =>
          refine ⟨by simp, by simp, fun _ hp => hp, fun k hk => ?_, fun k hk => ?_⟩ <;>
            simp [Array.getElem?_push, Nat.ne_of_lt hk]
        | cons b bs =>
          cases bs with
          | cons d ds =>
            refine ⟨by simp, by simp, fun _ hp => hp, fun k hk => ?_, fun k hk => ?_⟩ <;>
              simp [Array.getElem?_push, Nat.ne_of_lt hk]
          | nil =>
            by_cases hab : (a == b) = true
            · simp only [hab, ↓reduceIte]
              refine ⟨by simp, by simp, fun _ hp => hp, fun k hk => ?_, fun k hk => ?_⟩ <;>
                simp [Array.getElem?_push, Nat.ne_of_lt hk]
            · have habf : (a == b) = false := Bool.eq_false_iff.mpr hab
              simp only [habf, Bool.false_eq_true, ↓reduceIte]
              refine ⟨by simp, Nat.le_refl _, fun _ hp => List.mem_cons_of_mem _ hp,
                fun k hk => ?_, fun _ _ => trivial⟩
              simp [Array.getElem?_push, Nat.ne_of_lt hk]

private theorem sweepKeepMoved_preserves {s : CdclState}
    {acc : Array (Option Clause)} {bins : List (Nat × Nat)} {tgts : Array RefTarget}
    (hacc : SweepAccInv s acc bins tgts) (c : Clause) (lits' : List Nat)
    (hng : !c.garbage = true) (hent : s.f0.EntailsClause (cnfClause lits'))
    (hsub : ∀ x ∈ lits', x ∈ c.lits) :
    let acc' := acc.push (some { c with lits := lits' })
    let tgts' := tgts.push (RefTarget.moved acc.size)
    SweepAccInv s acc' bins tgts' ∧ tgts'.size = tgts.size + 1 ∧
    tgts'[tgts.size]? = some (RefTarget.moved acc.size) ∧
    (∃ c' : Clause, acc'[acc.size]? = some (some c') ∧ !c'.garbage = true ∧
      c'.lits = lits' ∧ ∀ x ∈ c'.lits, x ∈ c.lits) := by
  refine ⟨⟨fun k nid hk => ?_, fun i j nid hi hj => ?_, fun k d hk => ?_, hacc.bins_ok⟩,
    by simp, by simp, ⟨{ c with lits := lits' }, by simp, hng, rfl, hsub⟩⟩
  · simp only [Array.getElem?_push] at hk
    split at hk
    · simp only [Option.some.injEq, RefTarget.moved.injEq] at hk
      subst hk; rw [Array.size_push]; exact Nat.lt_succ_self _
    · rw [Array.size_push]; exact Nat.lt_succ_of_lt (hacc.bound k nid hk)
  · simp only [Array.getElem?_push] at hi hj
    split at hi <;> split at hj
    · omega
    · simp only [Option.some.injEq, RefTarget.moved.injEq] at hi; subst hi
      exact absurd (hacc.bound j acc.size hj) (Nat.lt_irrefl _)
    · simp only [Option.some.injEq, RefTarget.moved.injEq] at hj; subst hj
      exact absurd (hacc.bound i acc.size hi) (Nat.lt_irrefl _)
    · exact hacc.inj i j nid hi hj
  · simp only [Array.getElem?_push] at hk
    split at hk
    · simp only [Option.some.injEq] at hk; subst hk; exact ⟨hng, hent⟩
    · exact hacc.clauses_ok k d hk

private theorem sweepClauseStep_preserves {s : CdclState} (hinv : LazyTrailInv s)
    (hpos : ReasonLevelsPos s) (hnonroot : ReasonHasNonRootAntecedent s)
    {acc : Array (Option Clause)} {bins : List (Nat × Nat)} {tgts : Array RefTarget}
    {opt : Option Clause} (hacc : SweepAccInv s acc bins tgts)
    (hsrc : s.clauses[tgts.size]? = some opt)
    (hopt : ∀ c, opt = some c → s.f0.EntailsClause (cnfClause c.lits)) :
    let res := sweepClauseStep s acc bins tgts opt
    SweepAccInv s res.1 res.2.1 res.2.2 ∧
    res.2.2.size = tgts.size + 1 ∧
    (∀ (i : Nat) (_hi : i < s.trail.size) (c : Clause),
      stateReason s s.trail[i] = .large tgts.size →
      opt = some c → !c.garbage = true →
      (∃ nid, ∃ c' : Clause,
        res.2.2[tgts.size]? = some (RefTarget.moved nid) ∧
        res.1[nid]? = some (some c') ∧ !c'.garbage = true ∧
        s.trail[i] ∈ c'.lits ∧ ∀ x ∈ c'.lits, x ≠ s.trail[i] → x ∈ c.lits) ∨
      (∃ a b, res.2.2[tgts.size]? = some (RefTarget.toBinary a b) ∧ (a, b) ∈ res.2.1 ∧
        ((s.trail[i] = a ∧ b ≠ a ∧ s.f0.EntailsClause (cnfClause [a, b]) ∧ b ∈ c.lits) ∨
         (s.trail[i] = b ∧ a ≠ b ∧ s.f0.EntailsClause (cnfClause [b, a]) ∧ a ∈ c.lits)))) := by
  cases opt with
  | none =>
    refine ⟨⟨push_nonmoved_bound (fun _ h => by cases h) hacc.bound,
      push_nonmoved_inj (fun _ h => by cases h) hacc.inj, hacc.clauses_ok, hacc.bins_ok⟩,
      by simp [sweepClauseStep], fun i hi c hrsn heq _ => by cases heq⟩
  | some c =>
    have hc_ent : s.f0.EntailsClause (cnfClause c.lits) := hopt c rfl
    have hstrip_ent : s.f0.EntailsClause (cnfClause (stripFalsified (isRootFalse s) c.lits)) :=
      entails_stripFalsified hc_ent fun l _ hl => isRootFalse_entailed hinv hl
    have hsub_strip : ∀ x ∈ stripFalsified (isRootFalse s) c.lits, x ∈ c.lits := fun x hx => by
      simp [stripFalsified] at hx; exact hx.1
    by_cases hdrop : (c.garbage || c.lits.any (isRootTrue s)) = true
    · unfold sweepClauseStep
      simp only [hdrop, ↓reduceIte]
      refine ⟨⟨push_nonmoved_bound (fun _ h => by cases h) hacc.bound,
        push_nonmoved_inj (fun _ h => by cases h) hacc.inj, hacc.clauses_ok, hacc.bins_ok⟩,
        by simp, fun i hi d hrsn heq hng => ?_⟩
      injection heq with hcd; subst hcd
      exfalso
      have hrt_f := activeReason_not_rootSatisfied hinv hpos hi hrsn hsrc
      have hngf : c.garbage = false := Bool.eq_false_iff.mpr (by simpa using hng)
      simp [hngf, hrt_f] at hdrop
    · have hdrop_f : (c.garbage || c.lits.any (isRootTrue s)) = false :=
        Bool.eq_false_iff.mpr hdrop
      have hng_c : !c.garbage = true := by
        simp only [Bool.or_eq_false_iff] at hdrop_f; simp [hdrop_f.1]
      have hkm := sweepKeepMoved_preserves hacc c (stripFalsified (isRootFalse s) c.lits)
        hng_c hstrip_ent hsub_strip
      have hmk_act :
          ∀ (i : Nat) (_hi : i < s.trail.size) (d : Clause),
            stateReason s s.trail[i] = .large tgts.size →
            some c = some d → !d.garbage = true →
            s.trail[i] ∈ stripFalsified (isRootFalse s) c.lits →
            ∃ nid, ∃ c' : Clause,
              (tgts.push (RefTarget.moved acc.size))[tgts.size]? = some (RefTarget.moved nid) ∧
              (acc.push (some { c with lits := stripFalsified (isRootFalse s) c.lits }))[nid]? =
                some (some c') ∧
              !c'.garbage = true ∧ s.trail[i] ∈ c'.lits ∧
              ∀ x ∈ c'.lits, x ≠ s.trail[i] → x ∈ d.lits := by
        intro i _ d _ heq _ hm_trl
        injection heq with hcd; subst hcd
        obtain ⟨c', hc', hcng', hcl', hcsub⟩ := hkm.2.2.2
        exact ⟨acc.size, c', hkm.2.2.1, hc', hcng', by rwa [hcl'], fun x hx _ => hcsub x hx⟩
      unfold sweepClauseStep
      simp only [hdrop_f, Bool.false_eq_true, ↓reduceIte]
      cases hst : stripFalsified (isRootFalse s) c.lits with
      | nil =>
        refine ⟨by simpa [hst] using hkm.1, by simp, fun i hi d hrsn heq hng => ?_⟩
        exfalso
        injection heq with hcd; subst hcd
        have h2 := (activeReason_stripped_size_ge_two hinv hnonroot hi hrsn hsrc).1
        rw [hst] at h2; cases h2
      | cons a as =>
        cases as with
        | nil =>
          refine ⟨by simpa [hst] using hkm.1, by simp, fun i hi d hrsn heq hng => ?_⟩
          exfalso
          injection heq with hcd; subst hcd
          have h2 := (activeReason_stripped_size_ge_two hinv hnonroot hi hrsn hsrc).2.2.1
          rw [hst] at h2; simp at h2
        | cons b bs =>
          cases bs with
          | cons e es =>
            refine ⟨by simpa [hst] using hkm.1, by simp, fun i hi d hrsn heq hng => ?_⟩
            apply Or.inl
            have hmem := (activeReason_stripped_size_ge_two hinv hnonroot hi hrsn hsrc).1
            simpa [hst] using hmk_act i hi d hrsn heq hng hmem
          | nil =>
            by_cases hab : a = b
            · have habb : (a == b) = true := beq_iff_eq.mpr hab
              simp only [habb, ↓reduceIte]
              refine ⟨by simpa [hst] using hkm.1, by simp, fun i hi d hrsn heq hng => ?_⟩
              exfalso
              injection heq with hcd; subst hcd
              have hne := (activeReason_stripped_size_ge_two hinv hnonroot hi hrsn hsrc).2.2.2
                a b hst
              exact hne hab
            · have habf : (a == b) = false := beq_false_of_ne hab
              simp only [habf, Bool.false_eq_true, ↓reduceIte]
              have hbin_ent : s.f0.EntailsClause (cnfClause [a, b]) := by
                simpa [hst] using hstrip_ent
              refine ⟨⟨push_nonmoved_bound (fun _ h => by cases h) hacc.bound,
                push_nonmoved_inj (fun _ h => by cases h) hacc.inj, hacc.clauses_ok, ?_⟩,
                by simp, fun i hi d hrsn heq _ => ?_⟩
              · intro p hp
                rcases List.mem_cons.mp hp with rfl | hp'
                · exact hbin_ent
                · exact hacc.bins_ok p hp'
              · injection heq with hcd; subst hcd
                apply Or.inr
                refine ⟨a, b, by simp, by simp, ?_⟩
                have ha_mem : a ∈ c.lits := hsub_strip a (by simp [hst])
                have hb_mem : b ∈ c.lits := hsub_strip b (by simp [hst])
                have hmem := (activeReason_stripped_size_ge_two hinv hnonroot hi hrsn hsrc).1
                rw [hst] at hmem
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
                rcases hmem with hta | htb
                · exact Or.inl ⟨hta, Ne.symm hab, hbin_ent, hb_mem⟩
                · exact Or.inr ⟨htb, hab, entails_swap2 hbin_ent, ha_mem⟩

private theorem sweepClauses_foldl_mono (s : CdclState) (xs : List (Option Clause)) :
    ∀ (acc : Array (Option Clause)) (bins : List (Nat × Nat)) (tgts : Array RefTarget),
      let res := xs.foldl (fun (p : Array (Option Clause) × List (Nat × Nat) × Array RefTarget)
        opt => sweepClauseStep s p.1 p.2.1 p.2.2 opt) (acc, bins, tgts)
      tgts.size ≤ res.2.2.size ∧ acc.size ≤ res.1.size ∧
      (∀ p ∈ bins, p ∈ res.2.1) ∧
      (∀ k, k < tgts.size → res.2.2[k]? = tgts[k]?) ∧
      (∀ k, k < acc.size → res.1[k]? = acc[k]?) := by
  induction xs with
  | nil =>
    intro acc bins tgts
    exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ hp => hp, fun _ _ => rfl, fun _ _ => rfl⟩
  | cons x xs ih =>
    intro acc bins tgts
    have hm := sweepClauseStep_mono s acc bins tgts x
    have ih' := ih (sweepClauseStep s acc bins tgts x).1
      (sweepClauseStep s acc bins tgts x).2.1 (sweepClauseStep s acc bins tgts x).2.2
    refine ⟨Nat.le_trans hm.1 ih'.1, Nat.le_trans hm.2.1 ih'.2.1, fun p hp => ?_,
      fun k hk => ?_, fun k hk => ?_⟩
    · rw [List.foldl_cons]; exact ih'.2.2.1 p (hm.2.2.1 p hp)
    · rw [List.foldl_cons]
      exact (ih'.2.2.2.1 k (Nat.lt_of_lt_of_le hk hm.1)).trans (hm.2.2.2.1 k hk)
    · rw [List.foldl_cons]
      exact (ih'.2.2.2.2 k (Nat.lt_of_lt_of_le hk hm.2.1)).trans (hm.2.2.2.2 k hk)

private theorem sweepClauses_foldl_inv {s : CdclState} (hinv : LazyTrailInv s)
    (hpos : ReasonLevelsPos s) (hnonroot : ReasonHasNonRootAntecedent s)
    (xs : List (Option Clause)) :
    ∀ (acc : Array (Option Clause)) (bins : List (Nat × Nat)) (tgts : Array RefTarget),
      SweepAccInv s acc bins tgts →
      (∀ (idx : Nat) (opt : Option Clause), xs[idx]? = some opt →
        s.clauses[tgts.size + idx]? = some opt) →
      (∀ (idx : Nat) (c : Clause), xs[idx]? = some (some c) →
        s.f0.EntailsClause (cnfClause c.lits)) →
      let res := xs.foldl (fun (p : Array (Option Clause) × List (Nat × Nat) × Array RefTarget)
        opt => sweepClauseStep s p.1 p.2.1 p.2.2 opt) (acc, bins, tgts)
      SweepAccInv s res.1 res.2.1 res.2.2 ∧
      (∀ (idx : Nat) (i : Nat) (_hi : i < s.trail.size) (c : Clause),
        stateReason s s.trail[i] = .large (tgts.size + idx) →
        xs[idx]? = some (some c) → !c.garbage = true →
        (∃ nid, ∃ c' : Clause,
          res.2.2[tgts.size + idx]? = some (RefTarget.moved nid) ∧
          res.1[nid]? = some (some c') ∧ !c'.garbage = true ∧
          s.trail[i] ∈ c'.lits ∧ ∀ x ∈ c'.lits, x ≠ s.trail[i] → x ∈ c.lits) ∨
        (∃ a b, res.2.2[tgts.size + idx]? = some (RefTarget.toBinary a b) ∧ (a, b) ∈ res.2.1 ∧
          ((s.trail[i] = a ∧ b ≠ a ∧ s.f0.EntailsClause (cnfClause [a, b]) ∧ b ∈ c.lits) ∨
           (s.trail[i] = b ∧ a ≠ b ∧ s.f0.EntailsClause (cnfClause [b, a]) ∧ a ∈ c.lits)))) := by
  induction xs with
  | nil =>
    intro acc bins tgts hacc _ _
    exact ⟨hacc, fun idx _ _ _ _ hget _ => by simp at hget⟩
  | cons x xs ih =>
    intro acc bins tgts hacc hsrc hxs
    have hx_src : s.clauses[tgts.size]? = some x := hsrc 0 x (by simp)
    have hx_ok : ∀ c, x = some c → s.f0.EntailsClause (cnfClause c.lits) :=
      fun c hc => hxs 0 c (by simp [hc])
    have hstep := sweepClauseStep_preserves hinv hpos hnonroot hacc hx_src hx_ok
    have hih := ih (sweepClauseStep s acc bins tgts x).1
      (sweepClauseStep s acc bins tgts x).2.1 (sweepClauseStep s acc bins tgts x).2.2 hstep.1
      (fun idx opt ho => by
        rw [hstep.2.1, Nat.add_assoc, Nat.add_comm 1 idx, ← Nat.add_assoc]
        exact hsrc (idx + 1) opt (by simpa using ho))
      (fun idx c hc => hxs (idx + 1) c (by simpa using hc))
    have hmono := sweepClauses_foldl_mono s xs (sweepClauseStep s acc bins tgts x).1
      (sweepClauseStep s acc bins tgts x).2.1 (sweepClauseStep s acc bins tgts x).2.2
    refine ⟨hih.1, fun idx i hi c hrsn hget hng => ?_⟩
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Nat.add_zero] at hget hrsn
      rcases hstep.2.2 i hi c hrsn hget hng with
        ⟨nid, c', htg, hc', hng', hm', hsub'⟩ | ⟨a, b, htg, hbin, hbin_or⟩
      · apply Or.inl
        have hn_lt : nid < (sweepClauseStep s acc bins tgts x).1.size :=
          hstep.1.bound tgts.size nid htg
        refine ⟨nid, c', ?_, ?_, hng', hm', hsub'⟩
        · simp only [List.foldl_cons, Nat.add_zero]
          exact (hmono.2.2.2.1 tgts.size (by omega)).trans htg
        · simp only [List.foldl_cons]
          exact (hmono.2.2.2.2 nid hn_lt).trans hc'
      · apply Or.inr
        refine ⟨a, b, ?_, ?_, hbin_or⟩
        · simp only [List.foldl_cons, Nat.add_zero]
          exact (hmono.2.2.2.1 tgts.size (by omega)).trans htg
        · simp only [List.foldl_cons]
          exact hmono.2.2.1 _ hbin
    | succ k =>
      simp only [List.getElem?_cons_succ] at hget
      have hrsn' : stateReason s s.trail[i] =
          .large ((sweepClauseStep s acc bins tgts x).2.2.size + k) := by
        rw [hstep.2.1]; simpa [Nat.add_assoc, Nat.add_comm 1 k] using hrsn
      have hsub := hih.2 k i hi c hrsn' hget hng
      simp only [List.foldl_cons, hstep.2.1] at hsub ⊢
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using hsub

/-- `sweepClauses` produces a `RefTargetSound` compaction, root-stripping, and binary-promotion
result under `LazyTrailInv`, `ReasonLevelsPos`, and `ReasonHasNonRootAntecedent`. -/
theorem sweepClauses_sound {s : CdclState} (hinv : LazyTrailInv s)
    (hpos : ReasonLevelsPos s) (hnonroot : ReasonHasNonRootAntecedent s) :
    let res := sweepClauses s
    RefTargetSound s res.1 res.2.1 res.2.2 := by
  have hinit : SweepAccInv s #[] [] #[] :=
    ⟨fun _ _ h => by simp at h, fun _ _ _ h => by simp at h,
     fun _ _ h => by simp at h, fun _ h => by cases h⟩
  have hfold := sweepClauses_foldl_inv hinv hpos hnonroot s.clauses.toList #[] [] #[] hinit
    (fun idx opt ho => by simpa [Array.getElem?_toList] using ho)
    (fun idx c hc => hinv.db_sound idx c (by simpa [Array.getElem?_toList] using hc))
  have heq : sweepClauses s = s.clauses.toList.foldl
      (fun (p : Array (Option Clause) × List (Nat × Nat) × Array RefTarget) opt =>
        sweepClauseStep s p.1 p.2.1 p.2.2 opt) (#[], [], #[]) := by
    rw [sweepClauses, ← Array.foldl_toList]
  rw [heq]
  refine ⟨hfold.1.inj, fun i hi cid hrsn => ?_, fun nid c hc => (hfold.1.clauses_ok nid c hc).2,
    hfold.1.bins_ok⟩
  have hrd := hinv.reason_dag i hi
  dsimp only at hrd
  rw [hrsn] at hrd
  obtain ⟨c, hget, hng, _, _⟩ := hrd
  rcases hfold.2 cid i hi c (by simpa using hrsn)
      (by simpa [Array.getElem?_toList] using hget) hng with
    ⟨nid, c', htg, hc', hcng', hm', hsub'⟩ | ⟨a, b, htg, hbin, hbin_or⟩
  · apply Or.inl
    exact ⟨nid, c', by simpa using htg, hc', hcng', hm',
      fun x hx hxne => ⟨c, hget, hsub' x hx hxne⟩⟩
  · apply Or.inr
    refine ⟨a, b, by simpa using htg, hbin, ?_⟩
    rcases hbin_or with ⟨ha, hne, hent, hb⟩ | ⟨hb, hne, hent, ha⟩
    · exact Or.inl ⟨ha, hne, hent, c, hget, hb⟩
    · exact Or.inr ⟨hb, hne, hent, c, hget, ha⟩

/-- End-to-end soundness of `sweepClauses` + `applyRefTargets`: preserves `LazyTrailInv`, trail
entailment, surviving clauses, promoted binary watches, and satisfiability (`Sat F₀ → Sat`). -/
theorem sweep_collect_sound {s : CdclState} (hinv : LazyTrailInv s)
    (hpos : ReasonLevelsPos s) (hnonroot : ReasonHasNonRootAntecedent s) :
    let (cls, bins, tgts) := sweepClauses s
    let s' := applyRefTargets s cls tgts
    LazyTrailInv s' ∧
    s'.f0 = s.f0 ∧
    s'.trail = s.trail ∧
    (∀ k, decisionsAtMost s' k = decisionsAtMost s k) ∧
    (∀ (i : Nat) (hi : i < s'.trail.size),
      (s'.f0 ++ unitsCnf (decisionsAtMost s' (stateLevel s' s'.trail[i]))).EntailsClause
        (cnfClause [s'.trail[i]])) ∧
    (∀ (nid : Nat) (c : Clause), s'.clauses[nid]? = some (some c) → !c.garbage = true →
      s.f0.EntailsClause (cnfClause c.lits)) ∧
    (∀ p ∈ bins, s.f0.EntailsClause (cnfClause [p.1, p.2])) ∧
    (∀ α : Nat → Bool, s.f0.Sat α → (survivingCnf s'.clauses ++ binariesCnf bins).Sat α) ∧
    (∀ α : Nat → Bool, s.f0.Sat α →
      (s'.f0 ++ survivingCnf s'.clauses ++ binariesCnf bins).Sat α) :=
  collect_remap_sound hinv (sweepClauses_sound hinv hpos hnonroot)

/-! ## 3. Partitioning irredundant before redundant (`collect.c:213-275`) & `reduceAndCollect` -/

private structure PartitionAccInv (f0 : CNF Nat) (irred red : Array (Option Clause))
    (raw : Array (Option (Bool × Nat))) : Prop where
  bound_ir : ∀ (k i : Nat), raw[k]? = some (some (false, i)) → i < irred.size
  bound_rd : ∀ (k i : Nat), raw[k]? = some (some (true, i)) → i < red.size
  inj : ∀ (j1 j2 : Nat) (b : Bool) (i : Nat),
    raw[j1]? = some (some (b, i)) → raw[j2]? = some (some (b, i)) → j1 = j2
  ir_ok : ∀ (i : Nat) (c : Clause), irred[i]? = some (some c) →
    !c.garbage = true ∧ f0.EntailsClause (cnfClause c.lits)
  rd_ok : ∀ (i : Nat) (c : Clause), red[i]? = some (some c) →
    !c.garbage = true ∧ f0.EntailsClause (cnfClause c.lits)

private theorem partitionStep_mono (irred red : Array (Option Clause))
    (raw : Array (Option (Bool × Nat))) (opt : Option Clause) :
    let res := partitionStep irred red raw opt
    raw.size ≤ res.2.2.size ∧ irred.size ≤ res.1.size ∧ red.size ≤ res.2.1.size ∧
    (∀ k, k < raw.size → res.2.2[k]? = raw[k]?) ∧
    (∀ k, k < irred.size → res.1[k]? = irred[k]?) ∧
    (∀ k, k < red.size → res.2.1[k]? = red[k]?) := by
  cases opt with
  | none =>
    unfold partitionStep
    refine ⟨by simp, Nat.le_refl _, Nat.le_refl _, fun k hk => ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    simp [Array.getElem?_push, Nat.ne_of_lt hk]
  | some c =>
    unfold partitionStep
    by_cases hg : c.garbage = true
    · simp only [hg, ↓reduceIte]
      refine ⟨by simp, Nat.le_refl _, Nat.le_refl _, fun k hk => ?_,
        fun _ _ => trivial, fun _ _ => trivial⟩
      simp [Array.getElem?_push, Nat.ne_of_lt hk]
    · have hgf : c.garbage = false := Bool.eq_false_iff.mpr hg
      by_cases hrd : c.redundant = true
      · simp only [hgf, Bool.false_eq_true, ↓reduceIte, hrd]
        refine ⟨by simp, Nat.le_refl _, by simp, fun k hk => ?_,
          fun _ _ => trivial, fun k hk => ?_⟩ <;>
          simp [Array.getElem?_push, Nat.ne_of_lt hk]
      · have hrdf : c.redundant = false := Bool.eq_false_iff.mpr hrd
        simp only [hgf, hrdf, Bool.false_eq_true, ↓reduceIte]
        refine ⟨by simp, by simp, Nat.le_refl _, fun k hk => ?_, fun k hk => ?_,
          fun _ _ => trivial⟩ <;>
          simp [Array.getElem?_push, Nat.ne_of_lt hk]

private theorem push_raw_bound_same {b : Bool} {raw : Array (Option (Bool × Nat))} {sz : Nat}
    (hb : ∀ (k i : Nat), raw[k]? = some (some (b, i)) → i < sz) :
    ∀ (k i : Nat), (raw.push (some (b, sz)))[k]? = some (some (b, i)) → i < sz + 1 := by
  intro k i hk
  simp only [Array.getElem?_push] at hk
  split at hk
  · simp only [Option.some.injEq, Prod.mk.injEq] at hk; omega
  · exact Nat.lt_succ_of_lt (hb k i hk)

private theorem push_raw_bound_other {b1 b2 : Bool} (hne : b1 ≠ b2)
    {raw : Array (Option (Bool × Nat))} {sz idx : Nat}
    (hb : ∀ (k i : Nat), raw[k]? = some (some (b1, i)) → i < sz) :
    ∀ (k i : Nat), (raw.push (some (b2, idx)))[k]? = some (some (b1, i)) → i < sz := by
  intro k i hk
  simp only [Array.getElem?_push] at hk
  split at hk
  · simp only [Option.some.injEq, Prod.mk.injEq] at hk; exact absurd hk.1.symm hne
  · exact hb k i hk

private theorem push_raw_inj_same {b0 : Bool} {raw : Array (Option (Bool × Nat))} {sz : Nat}
    (hb : ∀ (k i : Nat), raw[k]? = some (some (b0, i)) → i < sz)
    (hinj : ∀ (j1 j2 : Nat) (b : Bool) (i : Nat),
      raw[j1]? = some (some (b, i)) → raw[j2]? = some (some (b, i)) → j1 = j2) :
    ∀ (j1 j2 : Nat) (b : Bool) (i : Nat),
      (raw.push (some (b0, sz)))[j1]? = some (some (b, i)) →
      (raw.push (some (b0, sz)))[j2]? = some (some (b, i)) → j1 = j2 := by
  intro j1 j2 b i h1 h2
  simp only [Array.getElem?_push] at h1 h2
  split at h1 <;> split at h2
  · omega
  · simp only [Option.some.injEq, Prod.mk.injEq] at h1
    rcases h1 with ⟨rfl, rfl⟩
    exact absurd (hb j2 sz h2) (Nat.lt_irrefl _)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h2
    rcases h2 with ⟨rfl, rfl⟩
    exact absurd (hb j1 sz h1) (Nat.lt_irrefl _)
  · exact hinj j1 j2 b i h1 h2

private theorem partitionStep_preserves {f0 : CNF Nat} {irred red : Array (Option Clause)}
    {raw : Array (Option (Bool × Nat))} {opt : Option Clause}
    (hacc : PartitionAccInv f0 irred red raw)
    (hopt : ∀ c, opt = some c → f0.EntailsClause (cnfClause c.lits)) :
    let res := partitionStep irred red raw opt
    PartitionAccInv f0 res.1 res.2.1 res.2.2 ∧
    res.2.2.size = raw.size + 1 ∧
    (∀ c, opt = some c → !c.garbage = true →
      (c.redundant = false ∧
        res.2.2[raw.size]? = some (some (false, irred.size)) ∧
        res.1[irred.size]? = some (some c)) ∨
      (c.redundant = true ∧
        res.2.2[raw.size]? = some (some (true, red.size)) ∧
        res.2.1[red.size]? = some (some c))) := by
  cases opt with
  | none =>
    simp only [partitionStep]
    exact ⟨⟨push_raw_none_bound hacc.bound_ir, push_raw_none_bound hacc.bound_rd,
      push_raw_none_inj hacc.inj, hacc.ir_ok, hacc.rd_ok⟩,
      by simp, fun _ h => by cases h⟩
  | some c =>
    by_cases hg : c.garbage = true
    · simp only [partitionStep, hg, ↓reduceIte]
      exact ⟨⟨push_raw_none_bound hacc.bound_ir, push_raw_none_bound hacc.bound_rd,
        push_raw_none_inj hacc.inj, hacc.ir_ok, hacc.rd_ok⟩,
        by simp, fun d hd hng => by injection hd with hcd; subst hcd; simp [hg] at hng⟩
    · have hgf : c.garbage = false := Bool.eq_false_iff.mpr hg
      have hng : !c.garbage = true := by simp [hgf]
      by_cases hrd : c.redundant = true
      · simp only [partitionStep, hgf, Bool.false_eq_true, ↓reduceIte, hrd]
        refine ⟨⟨push_raw_bound_other Bool.false_ne_true hacc.bound_ir,
          fun k i hk => by rw [Array.size_push]; exact push_raw_bound_same hacc.bound_rd k i hk,
          push_raw_inj_same hacc.bound_rd hacc.inj,
          hacc.ir_ok, fun i d hk => ?_⟩, by simp, fun d hd _ => ?_⟩
        · simp only [Array.getElem?_push] at hk
          split at hk
          · simp only [Option.some.injEq] at hk; subst hk; exact ⟨hng, hopt c rfl⟩
          · exact hacc.rd_ok i d hk
        · injection hd with hcd; subst hcd
          exact Or.inr ⟨hrd, by simp, by simp⟩
      · have hrdf : c.redundant = false := Bool.eq_false_iff.mpr hrd
        simp only [partitionStep, hgf, hrdf, Bool.false_eq_true, ↓reduceIte]
        refine ⟨⟨fun k i hk => by
            rw [Array.size_push]; exact push_raw_bound_same hacc.bound_ir k i hk,
          push_raw_bound_other Bool.false_ne_true.symm hacc.bound_rd,
          push_raw_inj_same hacc.bound_ir hacc.inj, fun i d hk => ?_, hacc.rd_ok⟩,
          by simp, fun d hd _ => ?_⟩
        · simp only [Array.getElem?_push] at hk
          split at hk
          · simp only [Option.some.injEq] at hk; subst hk; exact ⟨hng, hopt c rfl⟩
          · exact hacc.ir_ok i d hk
        · injection hd with hcd; subst hcd
          exact Or.inl ⟨hrdf, by simp, by simp⟩

private theorem partitionClauses_foldl_mono (xs : List (Option Clause)) :
    ∀ (irred red : Array (Option Clause)) (raw : Array (Option (Bool × Nat))),
      let res := xs.foldl (fun (p : Array (Option Clause) × Array (Option Clause) ×
        Array (Option (Bool × Nat))) opt => partitionStep p.1 p.2.1 p.2.2 opt) (irred, red, raw)
      raw.size ≤ res.2.2.size ∧ irred.size ≤ res.1.size ∧ red.size ≤ res.2.1.size ∧
      (∀ k, k < raw.size → res.2.2[k]? = raw[k]?) ∧
      (∀ k, k < irred.size → res.1[k]? = irred[k]?) ∧
      (∀ k, k < red.size → res.2.1[k]? = red[k]?) := by
  induction xs with
  | nil =>
    intro irred red raw
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
      fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  | cons x xs ih =>
    intro irred red raw
    have hm := partitionStep_mono irred red raw x
    have ih' := ih (partitionStep irred red raw x).1 (partitionStep irred red raw x).2.1
      (partitionStep irred red raw x).2.2
    refine ⟨Nat.le_trans hm.1 ih'.1, Nat.le_trans hm.2.1 ih'.2.1,
      Nat.le_trans hm.2.2.1 ih'.2.2.1, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩ <;>
      rw [List.foldl_cons]
    · exact (ih'.2.2.2.1 k (Nat.lt_of_lt_of_le hk hm.1)).trans (hm.2.2.2.1 k hk)
    · exact (ih'.2.2.2.2.1 k (Nat.lt_of_lt_of_le hk hm.2.1)).trans (hm.2.2.2.2.1 k hk)
    · exact (ih'.2.2.2.2.2 k (Nat.lt_of_lt_of_le hk hm.2.2.1)).trans (hm.2.2.2.2.2 k hk)

private theorem partitionClauses_foldl_inv {f0 : CNF Nat} (xs : List (Option Clause)) :
    ∀ (irred red : Array (Option Clause)) (raw : Array (Option (Bool × Nat))),
      PartitionAccInv f0 irred red raw →
      (∀ (idx : Nat) (c : Clause), xs[idx]? = some (some c) → f0.EntailsClause (cnfClause c.lits)) →
      let res := xs.foldl (fun (p : Array (Option Clause) × Array (Option Clause) ×
        Array (Option (Bool × Nat))) opt => partitionStep p.1 p.2.1 p.2.2 opt) (irred, red, raw)
      PartitionAccInv f0 res.1 res.2.1 res.2.2 ∧
      (∀ (idx : Nat) (c : Clause), xs[idx]? = some (some c) → !c.garbage = true →
        (c.redundant = false ∧
          ∃ i < res.1.size,
            res.2.2[raw.size + idx]? = some (some (false, i)) ∧ res.1[i]? = some (some c)) ∨
        (c.redundant = true ∧
          ∃ i < res.2.1.size,
            res.2.2[raw.size + idx]? = some (some (true, i)) ∧ res.2.1[i]? = some (some c))) := by
  induction xs with
  | nil =>
    intro irred red raw hacc _
    exact ⟨hacc, fun idx _ h _ => by simp at h⟩
  | cons x xs ih =>
    intro irred red raw hacc hxs
    have hx_ok : ∀ c, x = some c → f0.EntailsClause (cnfClause c.lits) :=
      fun c hc => hxs 0 c (by simp [hc])
    have hstep := partitionStep_preserves hacc hx_ok
    have hih := ih (partitionStep irred red raw x).1 (partitionStep irred red raw x).2.1
      (partitionStep irred red raw x).2.2 hstep.1
      (fun idx c hc => hxs (idx + 1) c (by simpa using hc))
    have hmono := partitionClauses_foldl_mono xs (partitionStep irred red raw x).1
      (partitionStep irred red raw x).2.1 (partitionStep irred red raw x).2.2
    refine ⟨hih.1, fun idx c hget hng => ?_⟩
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      rcases hstep.2.2 c hget hng with ⟨hrdf, hrm, hir⟩ | ⟨hrdt, hrm, hrd⟩
      · apply Or.inl
        have hsz : irred.size < (partitionStep irred red raw x).1.size := by
          rw [Array.getElem?_eq_some_iff] at hir; exact hir.1
        refine ⟨hrdf, irred.size,
          (by simp only [List.foldl_cons]; exact Nat.lt_of_lt_of_le hsz hmono.2.1), ?_, ?_⟩
        · simp only [List.foldl_cons, Nat.add_zero]
          exact (hmono.2.2.2.1 raw.size (by omega)).trans hrm
        · simp only [List.foldl_cons]
          exact (hmono.2.2.2.2.1 irred.size hsz).trans hir
      · apply Or.inr
        have hsz : red.size < (partitionStep irred red raw x).2.1.size := by
          rw [Array.getElem?_eq_some_iff] at hrd; exact hrd.1
        refine ⟨hrdt, red.size,
          (by simp only [List.foldl_cons]; exact Nat.lt_of_lt_of_le hsz hmono.2.2.1), ?_, ?_⟩
        · simp only [List.foldl_cons, Nat.add_zero]
          exact (hmono.2.2.2.1 raw.size (by omega)).trans hrm
        · simp only [List.foldl_cons]
          exact (hmono.2.2.2.2.2 red.size hsz).trans hrd
    | succ k =>
      simp only [List.getElem?_cons_succ] at hget
      rcases hih.2 k c hget hng with
        ⟨hrdf, i, hilt, hrm, hir⟩ | ⟨hrdt, i, hilt, hrm, hrd⟩
      · apply Or.inl
        refine ⟨hrdf, i, hilt, ?_, hir⟩
        simp only [List.foldl_cons]
        rwa [hstep.2.1, Nat.add_assoc, Nat.add_comm 1 k, ← Nat.add_assoc] at hrm
      · apply Or.inr
        refine ⟨hrdt, i, hilt, ?_, hrd⟩
        simp only [List.foldl_cons]
        rwa [hstep.2.1, Nat.add_assoc, Nat.add_comm 1 k, ← Nat.add_assoc] at hrm

theorem partitionIrredFirst_sound {s : CdclState} (hinv : LazyTrailInv s) :
    let (newClauses, tgts) := partitionIrredFirst s.clauses
    RefTargetSound s newClauses [] tgts := by
  have hinit : PartitionAccInv s.f0 #[] #[] #[] :=
    ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h, fun _ _ _ _ h => by simp at h,
     fun _ _ h => by simp at h, fun _ _ h => by simp at h⟩
  have hfold := partitionClauses_foldl_inv s.clauses.toList #[] #[] #[] hinit
    (fun idx c hc => hinv.db_sound idx c (by simpa [Array.getElem?_toList] using hc))
  have heq : partitionIrredFirst s.clauses =
      let st := s.clauses.toList.foldl (fun (p : Array (Option Clause) ×
        Array (Option Clause) × Array (Option (Bool × Nat))) opt =>
          partitionStep p.1 p.2.1 p.2.2 opt) (#[], #[], #[])
      (st.1 ++ st.2.1, st.2.2.map fun r =>
        match r with
        | none => RefTarget.dropped
        | some (false, i) => RefTarget.moved i
        | some (true, i) => RefTarget.moved (st.1.size + i)) := by
    rw [partitionIrredFirst, ← Array.foldl_toList]
    dsimp only
    rfl
  rw [heq]
  dsimp only
  let st := s.clauses.toList.foldl (fun (p : Array (Option Clause) ×
    Array (Option Clause) × Array (Option (Bool × Nat))) opt => partitionStep p.1 p.2.1 p.2.2 opt)
    (#[], #[], #[])
  refine ⟨fun i j nid hi hj => ?_, fun i hi cid hrsn => ?_, fun nid c hc => ?_,
    fun _ h => by cases h⟩
  · simp only [Array.getElem?_map, Option.map_eq_some_iff] at hi hj
    obtain ⟨r1, hr1, hm1⟩ := hi
    obtain ⟨r2, hr2, hm2⟩ := hj
    cases r1 with
    | none => simp at hm1
    | some p1 =>
      rcases p1 with ⟨b1, k1⟩
      cases r2 with
      | none => simp at hm2
      | some p2 =>
        rcases p2 with ⟨b2, k2⟩
        cases b1 <;> cases b2 <;> simp only [RefTarget.moved.injEq] at hm1 hm2
        · subst hm1
          exact hfold.1.inj i j false k1 hr1 (by simpa [← hm2] using hr2)
        · have hb1 := hfold.1.bound_ir i k1 hr1
          omega
        · have hb2 := hfold.1.bound_ir j k2 hr2
          omega
        · have hke : k1 = k2 := by omega
          subst hke
          exact hfold.1.inj i j true k1 hr1 hr2
  · have hrd := hinv.reason_dag i hi
    dsimp only at hrd
    rw [hrsn] at hrd
    obtain ⟨c, hget, hng, hm, _⟩ := hrd
    apply Or.inl
    rcases hfold.2 cid c (by simpa [Array.getElem?_toList] using hget) hng with
      ⟨_, k, hk, hrw, hst⟩ | ⟨_, k, hk, hrw, hst⟩
    · refine ⟨k, c, ?_, ?_, hng, hm, fun x hx _ => ⟨c, hget, hx⟩⟩
      · simp only [Array.getElem?_map, Option.map_eq_some_iff]
        exact ⟨some (false, k), by simpa using hrw, rfl⟩
      · rw [Array.getElem?_append_left hk]
        exact hst
    · refine ⟨st.1.size + k, c, ?_, ?_, hng, hm, fun x hx _ => ⟨c, hget, hx⟩⟩
      · simp only [Array.getElem?_map, Option.map_eq_some_iff]
        exact ⟨some (true, k), by simpa using hrw, rfl⟩
      · have hle : st.1.size ≤ st.1.size + k := Nat.le_add_right _ _
        rw [Array.getElem?_append_right hle]
        simpa [Nat.add_sub_cancel_left] using hst
  · by_cases hlt : nid < st.1.size
    · rw [Array.getElem?_append_left hlt] at hc
      exact (hfold.1.ir_ok nid c hc).2
    · have hle : st.1.size ≤ nid := Nat.le_of_not_lt hlt
      rw [Array.getElem?_append_right hle] at hc
      exact (hfold.1.rd_ok (nid - st.1.size) c hc).2

/-- End-to-end soundness of `reduceAndCollect`: preserves `LazyTrailInv`, `decisionsAtMost`,
`lazyTrailEntailment`, surviving clause & promoted binary `F₀.EntailsClause`, and
`Sat F₀ → Sat F_after`. -/
theorem reduceAndCollect_sound {s : CdclState} (hinv : LazyTrailInv s)
    (hpos : ReasonLevelsPos s) (hnonroot : ReasonHasNonRootAntecedent s)
    (dropPred : Nat → Clause → Bool) :
    let (s', bins) := reduceAndCollect s dropPred
    LazyTrailInv s' ∧
    s'.f0 = s.f0 ∧
    s'.trail = s.trail ∧
    (∀ k, decisionsAtMost s' k = decisionsAtMost s k) ∧
    (∀ (i : Nat) (hi : i < s'.trail.size),
      (s'.f0 ++ unitsCnf (decisionsAtMost s' (stateLevel s' s'.trail[i]))).EntailsClause
        (cnfClause [s'.trail[i]])) ∧
    (∀ (nid : Nat) (c : Clause), s'.clauses[nid]? = some (some c) → !c.garbage = true →
      s.f0.EntailsClause (cnfClause c.lits)) ∧
    (∀ p ∈ bins, s.f0.EntailsClause (cnfClause [p.1, p.2])) ∧
    (∀ α : Nat → Bool, s.f0.Sat α → (survivingCnf s'.clauses ++ binariesCnf bins).Sat α) ∧
    (∀ α : Nat → Bool, s.f0.Sat α →
      (s'.f0 ++ survivingCnf s'.clauses ++ binariesCnf bins).Sat α) := by
  let pred : Nat → Clause → Bool := fun cid c => c.redundant && dropPred cid c
  let s1 := markGarbageIf s pred
  let sw := sweepClauses s1
  let s2 := applyRefTargets s1 sw.1 sw.2.2
  let pt := partitionIrredFirst s2.clauses
  let s3 := applyRefTargets s2 pt.1 pt.2
  change LazyTrailInv s3 ∧
    s3.f0 = s.f0 ∧
    s3.trail = s.trail ∧
    (∀ k, decisionsAtMost s3 k = decisionsAtMost s k) ∧
    (∀ (i : Nat) (hi : i < s3.trail.size),
      (s3.f0 ++ unitsCnf (decisionsAtMost s3 (stateLevel s3 s3.trail[i]))).EntailsClause
        (cnfClause [s3.trail[i]])) ∧
    (∀ (nid : Nat) (c : Clause), s3.clauses[nid]? = some (some c) → !c.garbage = true →
      s.f0.EntailsClause (cnfClause c.lits)) ∧
    (∀ p ∈ sw.2.1, s.f0.EntailsClause (cnfClause [p.1, p.2])) ∧
    (∀ α : Nat → Bool, s.f0.Sat α → (survivingCnf s3.clauses ++ binariesCnf sw.2.1).Sat α) ∧
    (∀ α : Nat → Bool, s.f0.Sat α →
      (s3.f0 ++ survivingCnf s3.clauses ++ binariesCnf sw.2.1).Sat α)
  have hm := markGarbageIf_sound hinv pred
  have hs := sweep_collect_sound hm.1 (hm.2.2.2.1 hpos) (hm.2.2.2.2.1 hnonroot)
  have hp := collect_remap_sound hs.1 (partitionIrredFirst_sound hs.1)
  have hf0 : s3.f0 = s.f0 := hp.2.1.trans (hs.2.1.trans hm.2.1)
  have htr : s3.trail = s.trail := hp.2.2.1.trans (hs.2.2.1.trans hm.2.2.1)
  have hs2_f0 : s2.f0 = s.f0 := hs.2.1.trans hm.2.1
  have hs1_f0 : s1.f0 = s.f0 := hm.2.1
  have hdec : ∀ k, decisionsAtMost s3 k = decisionsAtMost s k :=
    fun k => (hp.2.2.2.1 k).trans (hs.2.2.2.1 k)
  have hbin_ent : ∀ p ∈ sw.2.1, s.f0.EntailsClause (cnfClause [p.1, p.2]) := by
    intro p hp_mem
    exact hs1_f0 ▸ hs.2.2.2.2.2.2.1 p hp_mem
  have hsurv_ent : ∀ (nid : Nat) (c : Clause), s3.clauses[nid]? = some (some c) →
      !c.garbage = true → s.f0.EntailsClause (cnfClause c.lits) := by
    intro nid c hget hng
    exact hs2_f0 ▸ hp.2.2.2.2.2.1 nid c hget hng
  have hsat_after : ∀ α : Nat → Bool, s.f0.Sat α →
      (survivingCnf s3.clauses ++ binariesCnf sw.2.1).Sat α := by
    intro α hα
    rw [CNF.sat_append]
    have hpt_sat := hp.2.2.2.2.2.2.2.1 α (hs2_f0.symm ▸ hα)
    have hsw_sat := hs.2.2.2.2.2.2.2.1 α (hs1_f0.symm ▸ hα)
    rw [CNF.sat_append] at hpt_sat hsw_sat
    exact ⟨hpt_sat.1, hsw_sat.2⟩
  have hsat_full : ∀ α : Nat → Bool, s.f0.Sat α →
      (s3.f0 ++ survivingCnf s3.clauses ++ binariesCnf sw.2.1).Sat α := by
    intro α hα
    rw [CNF.sat_append, CNF.sat_append]
    have hs3 := hsat_after α hα
    rw [CNF.sat_append] at hs3
    exact ⟨⟨hf0.symm ▸ hα, hs3.1⟩, hs3.2⟩
  exact ⟨hp.1, hf0, htr, hdec, hp.2.2.2.2.1, hsurv_ent, hbin_ent, hsat_after, hsat_full⟩

end LeanQbe.T.Examples.Kissat.Ref
