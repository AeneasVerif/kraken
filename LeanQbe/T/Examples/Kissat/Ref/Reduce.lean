/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Minimize

/-!
# Pure Lean Layer-A CDCL Theory for Clause Collection & Relocation (Part 1)

Pure Lean theory (zero `Kraken.Mem` or `Kraken.Separation` imports) for clause-ID remapping,
deletion of unreferenced clauses, and `reduce` garbage marking (`collect.c`, `reduce.c`,
`trail.c`):

1. **CNF views & active-reason predicate (`survivingCnf`, `binariesCnf`,
   `isActiveLargeReason`)**.
2. **Generalized `RefTarget` relocation (`collect_remap_sound`,
   `collect_remap_preserves_trailInv`, `core_collect_lazy_sound`)**:
   Deleting unreferenced clauses, injectively remapping surviving clause IDs (`RefTarget.moved`),
   and promoting size-2 clauses (`RefTarget.toBinary`) preserves `LazyTrailInv` (`ReasonDagInv`),
   `lazyTrailEntailment`, surviving/binary `F₀.EntailsClause`, and satisfiability (`Sat F₀ → Sat`).
3. **Unreferenced deletion & garbage marking (`deleteUnreferencedClauses_sound`,
   `markGarbageIf_sound`)** plus `ReasonLevelsPos` / `ReasonHasNonRootAntecedent`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. CNF views, active trail reasons, and generalized `RefTarget` relocation -/

/-- Conjunction of all non-garbage clauses stored in `clauses`. -/
@[expose] def survivingCnf (clauses : Array (Option Clause)) : CNF Nat :=
  clauses.foldl (init := CNF.empty) fun acc opt =>
    match opt with
    | some c => if c.garbage then acc else acc.add (cnfClause c.lits)
    | none => acc

/-- Conjunction of promoted binary watch pairs `(a, b)`. -/
@[expose] def binariesCnf (bins : List (Nat × Nat)) : CNF Nat :=
  bins.foldl (init := CNF.empty) fun acc p => acc.add (cnfClause [p.1, p.2])

theorem sat_survivingCnf_iff (α : Nat → Bool) (clauses : Array (Option Clause)) :
    (survivingCnf clauses).Sat α ↔
      ∀ (cid : Nat) (c : Clause), clauses[cid]? = some (some c) → !c.garbage = true →
        (cnfClause c.lits).Sat α := by
  have hgen : ∀ (xs : List (Option Clause)) (init : CNF Nat),
      (xs.foldl (init := init) fun acc opt =>
        match opt with
        | some c => if c.garbage then acc else acc.add (cnfClause c.lits)
        | none => acc).Sat α ↔
        init.Sat α ∧ ∀ (idx : Nat) (c : Clause),
          xs[idx]? = some (some c) → !c.garbage = true → (cnfClause c.lits).Sat α := by
    intro xs
    induction xs with
    | nil => intro init; simp
    | cons x xs ih =>
      intro init
      simp only [List.foldl_cons, ih]
      cases x with
      | none =>
        constructor
        · rintro ⟨hi, hrest⟩
          refine ⟨hi, fun idx c hget hng => ?_⟩
          cases idx with
          | zero => cases hget
          | succ k => exact hrest k c hget hng
        · rintro ⟨hi, hall⟩
          exact ⟨hi, fun k c hget hng => hall (k + 1) c hget hng⟩
      | some c0 =>
        by_cases hg : c0.garbage = true
        · simp only [hg, ↓reduceIte]
          constructor
          · rintro ⟨hi, hrest⟩
            refine ⟨hi, fun idx c hget hng => ?_⟩
            cases idx with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
              subst hget; simp [hg] at hng
            | succ k => exact hrest k c hget hng
          · rintro ⟨hi, hall⟩
            exact ⟨hi, fun k c hget hng => hall (k + 1) c hget hng⟩
        · have hgf : c0.garbage = false := Bool.eq_false_iff.mpr hg
          simp only [hgf, Bool.false_eq_true, ↓reduceIte, CNF.sat_add]
          constructor
          · rintro ⟨⟨hc0, hi⟩, hrest⟩
            refine ⟨hi, fun idx c hget hng => ?_⟩
            cases idx with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
              subst hget; exact hc0
            | succ k => exact hrest k c hget hng
          · rintro ⟨hi, hall⟩
            exact ⟨⟨hall 0 c0 (by simp) (by simp [hgf]), hi⟩,
              fun k c hget hng => hall (k + 1) c hget hng⟩
  have h0 := hgen clauses.toList CNF.empty
  simp only [CNF.sat_empty, true_and] at h0
  rw [survivingCnf, ← Array.foldl_toList]
  simpa [Array.getElem?_toList] using h0

theorem sat_binariesCnf_iff (α : Nat → Bool) (bins : List (Nat × Nat)) :
    (binariesCnf bins).Sat α ↔ ∀ p ∈ bins, (cnfClause [p.1, p.2]).Sat α := by
  rw [binariesCnf]
  exact sat_foldl_cnfClause_iff (fun p => [p.1, p.2]) α bins

/-- Active-reason predicate (`trail.c:26-43`): `true` iff some trail literal cites `.large cid`
as its `stateReason`. -/
@[expose] def isActiveLargeReason (s : CdclState) (cid : Nat) : Bool :=
  s.trail.any fun l => stateReason s l == .large cid

theorem isActiveLargeReason_iff {s : CdclState} {cid : Nat} :
    isActiveLargeReason s cid = true ↔
      ∃ (i : Nat) (_hi : i < s.trail.size), stateReason s s.trail[i] = .large cid := by
  unfold isActiveLargeReason
  rw [Array.any_eq_true]
  constructor
  · rintro ⟨i, hi, heq⟩
    exact ⟨i, hi, beq_iff_eq.mp heq⟩
  · rintro ⟨i, hi, heq⟩
    exact ⟨i, hi, beq_iff_eq.mpr heq⟩

/-- Relocation/promotion target for an old clause slot `cid`. -/
inductive RefTarget where
  | dropped
  | toBinary (a b : Nat)
  | moved (newCid : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Remap a reason belonging to trail literal `lit` through `targets`. -/
@[expose] def remapReasonTarget (targets : Array RefTarget) (lit : Nat) : Reason → Reason
  | .large cid =>
    match targets[cid]? with
    | some (.moved newCid) => .large newCid
    | some (.toBinary a b) => .binary (if lit == a then b else a)
    | _ => .large cid
  | r => r

theorem remapReasonTarget_eq_decision {targets : Array RefTarget} {lit : Nat} {r : Reason} :
    remapReasonTarget targets lit r = .decision ↔ r = .decision := by
  cases r with
  | decision => simp [remapReasonTarget]
  | unit => simp [remapReasonTarget]
  | binary _ => simp [remapReasonTarget]
  | large cid =>
    simp only [remapReasonTarget]
    cases targets[cid]? with
    | none => simp
    | some tgt => cases tgt <;> simp

@[expose] def remapReasonStep (targets : Array RefTarget) (rs : Array Reason)
    (lit : Nat) : Array Reason :=
  let v := litVar lit
  if h : v < rs.size then rs.set v (remapReasonTarget targets lit rs[v]) else rs

/-- Update trail reason entries for every variable assigned on `trail`. -/
@[expose] def remapReasons (trail : Array Nat) (reasons : Array Reason)
    (targets : Array RefTarget) : Array Reason :=
  trail.foldl (remapReasonStep targets) reasons

/-- Apply relocated/compacted clause database and target reason mapping to `CdclState`. -/
@[expose] def applyRefTargets (s : CdclState) (newClauses : Array (Option Clause))
    (targets : Array RefTarget) : CdclState :=
  { s with
    clauses := newClauses
    reasons := remapReasons s.trail s.reasons targets }

private theorem remapReasonStep_getD_eq (targets : Array RefTarget) (rs : Array Reason)
    (lit : Nat) :
    (remapReasonStep targets rs lit).getD (litVar lit) .unit =
      remapReasonTarget targets lit (rs.getD (litVar lit) .unit) := by
  unfold remapReasonStep; dsimp only
  by_cases hlt : litVar lit < rs.size
  · simp only [hlt, ↓reduceDIte, Array.getD_eq_getD_getElem?, Array.getElem?_set_self,
      Option.getD_some, Array.getElem?_eq_getElem hlt]
  · simp only [hlt, ↓reduceDIte, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (Nat.le_of_not_lt hlt), Option.getD_none, remapReasonTarget]

private theorem remapReasonStep_getD_ne (targets : Array RefTarget) (rs : Array Reason)
    {lit v : Nat} (hne : v ≠ litVar lit) :
    (remapReasonStep targets rs lit).getD v .unit = rs.getD v .unit := by
  unfold remapReasonStep; dsimp only
  by_cases hlt : litVar lit < rs.size
  · have hnev : litVar lit ≠ v := Ne.symm hne
    simp [hlt, Array.getD_eq_getD_getElem?, hnev]
  · simp [hlt]

private theorem remapReasonStep_getD_decision (targets : Array RefTarget) (rs : Array Reason)
    (lit v : Nat) :
    ((remapReasonStep targets rs lit).getD v .unit = .decision) ↔
      (rs.getD v .unit = .decision) := by
  by_cases hv : v = litVar lit
  · subst hv; rw [remapReasonStep_getD_eq, remapReasonTarget_eq_decision]
  · rw [remapReasonStep_getD_ne _ _ hv]

private theorem foldl_remapReasonStep_not_mem (targets : Array RefTarget) (v : Nat) :
    ∀ (ls : List Nat) (rs : Array Reason), (∀ x ∈ ls, litVar x ≠ v) →
      (ls.foldl (remapReasonStep targets) rs).getD v .unit = rs.getD v .unit := by
  intro ls
  induction ls with
  | nil => intro rs _; rfl
  | cons x xs ih =>
    intro rs hno
    simp only [List.foldl_cons]
    rw [ih _ fun y hy => hno y (List.mem_cons_of_mem _ hy)]
    exact remapReasonStep_getD_ne targets rs (Ne.symm (hno x (by simp)))

private theorem foldl_remapReasonStep_mem_nodup (targets : Array RefTarget) :
    ∀ (ls : List Nat) (rs : Array Reason) {lit : Nat},
      (ls.map litVar).Nodup → lit ∈ ls →
      (ls.foldl (remapReasonStep targets) rs).getD (litVar lit) .unit =
        remapReasonTarget targets lit (rs.getD (litVar lit) .unit) := by
  intro ls
  induction ls with
  | nil => intro _ _ _ hm; cases hm
  | cons x xs ih =>
    intro rs lit hnd hm
    have hndc := List.nodup_cons.mp hnd
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hm with rfl | hxs
    · rw [foldl_remapReasonStep_not_mem]
      · exact remapReasonStep_getD_eq targets rs lit
      · intro y hy hvar; exact hndc.1 (List.mem_map.mpr ⟨y, hy, hvar⟩)
    · rw [ih _ hndc.2 hxs]
      have hne : litVar lit ≠ litVar x := fun heq =>
        hndc.1 (List.mem_map.mpr ⟨lit, hxs, heq⟩)
      rw [remapReasonStep_getD_ne targets rs hne]

private theorem foldl_remapReasonStep_decision (targets : Array RefTarget) (v : Nat) :
    ∀ (ls : List Nat) (rs : Array Reason),
      ((ls.foldl (remapReasonStep targets) rs).getD v .unit = .decision) ↔
        (rs.getD v .unit = .decision) := by
  intro ls
  induction ls with
  | nil => intro rs; rfl
  | cons x xs ih =>
    intro rs
    simp only [List.foldl_cons, ih, remapReasonStep_getD_decision]

theorem stateReason_applyRefTargets {s : CdclState} (hinv : LazyTrailInv s)
    (newClauses : Array (Option Clause)) (targets : Array RefTarget)
    {i : Nat} (hi : i < s.trail.size) :
    stateReason (applyRefTargets s newClauses targets) s.trail[i] =
      remapReasonTarget targets s.trail[i] (stateReason s s.trail[i]) := by
  have hnd : (s.trail.toList.map litVar).Nodup := list_map_nodup_of_getElem fun a b ha hb hvar =>
    hinv.vars_nodup a b (by simpa using ha) (by simpa using hb) (by simpa using hvar)
  have hmem : s.trail[i] ∈ s.trail.toList :=
    trail_mem_iff_exists.mpr ⟨i, hi, rfl⟩
  simp only [stateReason, applyRefTargets, remapReasons, ← Array.foldl_toList]
  exact foldl_remapReasonStep_mem_nodup targets s.trail.toList s.reasons hnd hmem

theorem stateReason_applyRefTargets_eq_decision (s : CdclState)
    (newClauses : Array (Option Clause)) (targets : Array RefTarget) (l : Nat) :
    stateReason (applyRefTargets s newClauses targets) l = .decision ↔
      stateReason s l = .decision := by
  simp only [stateReason, applyRefTargets, remapReasons, ← Array.foldl_toList]
  exact foldl_remapReasonStep_decision targets (litVar l) s.trail.toList s.reasons

/-- Generalized soundness contract for clause relocation, deletion, and size-2 binary promotion:
- `inj_moved`: distinct original IDs never collide at the same new clause ID.
- `active_preserved`: every active trail `.large cid` reason either moves to a non-garbage clause
  `c'` containing `trail[i]` with `c'.lits ⊆ old_c.lits`, or becomes a binary watch `[a, b]`
  preserving `trail[i]`, its sibling literal `oth ≠ trail[i]` from `old_c.lits`, and `f0`-entailment
  of `[trail[i], oth]`.
- `clauses_entailed`: every non-empty clause slot in `newClauses` is entailed by `s.f0`.
- `binaries_entailed`: every promoted binary pair in `newBinaries` is entailed by `s.f0`. -/
structure RefTargetSound (s : CdclState) (newClauses : Array (Option Clause))
    (newBinaries : List (Nat × Nat)) (targets : Array RefTarget) : Prop where
  inj_moved : ∀ (i j nid : Nat),
    targets[i]? = some (RefTarget.moved nid) →
    targets[j]? = some (RefTarget.moved nid) → i = j
  active_preserved :
    ∀ (i : Nat) (_hi : i < s.trail.size) (cid : Nat),
      stateReason s s.trail[i] = .large cid →
      (∃ newCid c', targets[cid]? = some (RefTarget.moved newCid) ∧
        newClauses[newCid]? = some (some c') ∧ !c'.garbage = true ∧
        s.trail[i] ∈ c'.lits ∧
        ∀ x ∈ c'.lits, x ≠ s.trail[i] →
          ∃ c : Clause, s.clauses[cid]? = some (some c) ∧ x ∈ c.lits) ∨
      (∃ a b, targets[cid]? = some (RefTarget.toBinary a b) ∧ (a, b) ∈ newBinaries ∧
        ((s.trail[i] = a ∧ b ≠ a ∧ s.f0.EntailsClause (cnfClause [a, b]) ∧
            ∃ c : Clause, s.clauses[cid]? = some (some c) ∧ b ∈ c.lits) ∨
         (s.trail[i] = b ∧ a ≠ b ∧ s.f0.EntailsClause (cnfClause [b, a]) ∧
            ∃ c : Clause, s.clauses[cid]? = some (some c) ∧ a ∈ c.lits)))
  clauses_entailed :
    ∀ (nid : Nat) (c : Clause), newClauses[nid]? = some (some c) →
      s.f0.EntailsClause (cnfClause c.lits)
  binaries_entailed :
    ∀ p ∈ newBinaries, s.f0.EntailsClause (cnfClause [p.1, p.2])

/-- **Main Layer-A collection/remapping soundness theorem (`collect_remap_sound`)**:
Any `RefTargetSound` transformation applied via `applyRefTargets` preserves `LazyTrailInv`
(including `ReasonDagInv`), `decisionsAtMost`, `lazyTrailEntailment`, surviving clause entailment,
promoted binary entailment, and satisfiability (`Sat F₀ → Sat F_after`). -/
theorem collect_remap_sound {s : CdclState} (hinv : LazyTrailInv s)
    {newClauses : Array (Option Clause)} {newBinaries : List (Nat × Nat)}
    {targets : Array RefTarget} (hts : RefTargetSound s newClauses newBinaries targets) :
    let s' := applyRefTargets s newClauses targets
    LazyTrailInv s' ∧
    s'.f0 = s.f0 ∧
    s'.trail = s.trail ∧
    (∀ k, decisionsAtMost s' k = decisionsAtMost s k) ∧
    (∀ (i : Nat) (hi : i < s'.trail.size),
      (s'.f0 ++ unitsCnf (decisionsAtMost s' (stateLevel s' s'.trail[i]))).EntailsClause
        (cnfClause [s'.trail[i]])) ∧
    (∀ (nid : Nat) (c : Clause), s'.clauses[nid]? = some (some c) → !c.garbage = true →
      s.f0.EntailsClause (cnfClause c.lits)) ∧
    (∀ p ∈ newBinaries, s.f0.EntailsClause (cnfClause [p.1, p.2])) ∧
    (∀ α : Nat → Bool, s.f0.Sat α →
      (survivingCnf s'.clauses ++ binariesCnf newBinaries).Sat α) ∧
    (∀ α : Nat → Bool, s.f0.Sat α →
      (s'.f0 ++ survivingCnf s'.clauses ++ binariesCnf newBinaries).Sat α) := by
  let s' := applyRefTargets s newClauses targets
  have htr : s'.trail = s.trail := rfl
  have hf0 : s'.f0 = s.f0 := rfl
  have hlvl : ∀ x, stateLevel s' x = stateLevel s x := fun _ => rfl
  have hdec_eq : ∀ k, decisionsAtMost s' k = decisionsAtMost s k := by
    intro k
    unfold decisionsAtMost
    rw [htr]
    apply List.filter_congr
    intro l _
    simp only [s', hlvl, stateReason_applyRefTargets_eq_decision]
  have hinv' : LazyTrailInv s' := by
    refine ⟨hinv.vars_nodup, hinv.levels_le, ?_, hts.clauses_entailed, hinv.units_sound, ?_,
      hinv.inconsistent_sound⟩
    · intro i j hi hj hleq hrsn_j
      change i < s.trail.size at hi
      change j < s.trail.size at hj
      change stateLevel s s.trail[i] = stateLevel s s.trail[j] at hleq
      have hsr : stateReason s' s.trail[j] = .decision ↔ stateReason s s.trail[j] = .decision :=
        stateReason_applyRefTargets_eq_decision s newClauses targets s.trail[j]
      change stateReason s' s.trail[j] = .decision at hrsn_j
      exact hinv.dec_earliest i j hi hj hleq (hsr.mp hrsn_j)
    · intro i hi
      have hi_s : i < s.trail.size := hi
      have hrd := hinv.reason_dag i hi_s
      dsimp only at hrd
      have hsr : stateReason s' s.trail[i] =
          remapReasonTarget targets s.trail[i] (stateReason s s.trail[i]) :=
        stateReason_applyRefTargets hinv newClauses targets hi_s
      change match stateReason s' s'.trail[i] with | _ => _
      simp only [htr, hf0, hlvl, hsr]
      generalize hrsn : stateReason s s.trail[i] = rsn
      rw [hrsn] at hrd
      cases rsn with
      | decision | unit | binary _ => exact hrd
      | large cid =>
        obtain ⟨c0, hget0, _, _, hall0⟩ := hrd
        rcases hts.active_preserved i hi_s cid hrsn with
          ⟨newCid, c', htgt, hget', hng', hm', hsub'⟩ | ⟨a, b, htgt, _, hbin_or⟩
        · dsimp only [remapReasonTarget]
          rw [htgt]; dsimp only
          refine ⟨c', hget', hng', hm', fun x hx hxne => ?_⟩
          obtain ⟨c1, hget1, hx1⟩ := hsub' x hx hxne
          have hc01 : c0 = c1 := by
            rw [hget0] at hget1; injection hget1 with h1; injection h1
          subst hc01
          exact hall0 x hx1 hxne
        · dsimp only [remapReasonTarget]
          rw [htgt]; dsimp only
          rcases hbin_or with ⟨ha, hne, hent, c1, hget1, hb1⟩ | ⟨hb, hne, hent, c1, hget1, ha1⟩
          · have hif : (if s.trail[i] == a then b else a) = b := by simp [ha]
            have hc01 : c0 = c1 := by
              rw [hget0] at hget1; injection hget1 with h1; injection h1
            subst hc01
            rw [hif]
            refine ⟨by simpa [ha] using hent, hall0 b hb1 (by simpa [ha] using hne)⟩
          · have hc01 : c0 = c1 := by
              rw [hget0] at hget1; injection hget1 with h1; injection h1
            subst hc01
            by_cases hba : s.trail[i] = a
            · exact absurd (hb.symm.trans hba) hne.symm
            · have hif : (if s.trail[i] == a then b else a) = a := by simp [hba]
              rw [hif]
              refine ⟨by simpa [hb] using hent, hall0 a ha1 (by simpa [hb] using hne)⟩
  have hsurv : ∀ (nid : Nat) (c : Clause),
      s'.clauses[nid]? = some (some c) → !c.garbage = true →
      s.f0.EntailsClause (cnfClause c.lits) :=
    fun nid c hget _ => hts.clauses_entailed nid c hget
  have hsat_after : ∀ α : Nat → Bool, s.f0.Sat α →
      (survivingCnf s'.clauses ++ binariesCnf newBinaries).Sat α := by
    intro α hα
    rw [CNF.sat_append, sat_survivingCnf_iff, sat_binariesCnf_iff]
    exact ⟨fun nid c hget hng => CNF.entails_clause_def.mp (hsurv nid c hget hng) α hα,
      fun p hp => CNF.entails_clause_def.mp (hts.binaries_entailed p hp) α hα⟩
  have hsat_full : ∀ α : Nat → Bool, s.f0.Sat α →
      (s'.f0 ++ survivingCnf s'.clauses ++ binariesCnf newBinaries).Sat α := by
    intro α hα
    rw [CNF.sat_append, CNF.sat_append]
    have hs := hsat_after α hα
    rw [CNF.sat_append] at hs
    exact ⟨⟨hα, hs.1⟩, hs.2⟩
  exact ⟨hinv', rfl, rfl, hdec_eq, fun i hi => lazyTrailEntailment hinv' i hi,
    hsurv, hts.binaries_entailed, hsat_after, hsat_full⟩

/-- Full `TrailInv` preservation when relocating clauses from a level-monotone state. -/
theorem collect_remap_preserves_trailInv {s : CdclState} (hinv : TrailInv s)
    {newClauses : Array (Option Clause)} {newBinaries : List (Nat × Nat)}
    {targets : Array RefTarget} (hts : RefTargetSound s newClauses newBinaries targets) :
    TrailInv (applyRefTargets s newClauses targets) := by
  have h := (collect_remap_sound hinv.toLazy hts).1
  exact ⟨h.vars_nodup, h.levels_le, hinv.levels_mono, h.dec_earliest, h.db_sound,
    h.units_sound, h.reason_dag, h.inconsistent_sound⟩

theorem core_collect_lazy_sound {s : CdclState} (hinv : LazyTrailInv s) :
    let (s', rmap) := collect s
    LazyTrailInv s' ∧
    s'.f0 = s.f0 ∧
    s'.trail = s.trail ∧
    RefMapSound s.clauses s'.clauses rmap s.f0 ∧
    (∀ i (hi : i < s'.trail.size),
      (s'.f0 ++ unitsCnf (decisionsAtMost s' (stateLevel s' s'.trail[i]))).EntailsClause
        (cnfClause [s'.trail[i]])) ∧
    (∀ (nid : Nat) (c : Clause), s'.clauses[nid]? = some (some c) → !c.garbage = true →
      s.f0.EntailsClause (cnfClause c.lits)) ∧
    (∀ α : Nat → Bool, s.f0.Sat α → (survivingCnf s'.clauses).Sat α) := by
  have hc := collect_preserves_lazyInv hinv
  have hsurv : ∀ (nid : Nat) (c : Clause),
      (collect s).1.clauses[nid]? = some (some c) → !c.garbage = true →
      s.f0.EntailsClause (cnfClause c.lits) :=
    fun nid c hget _ => hc.2.2.2.2 nid c hget
  have hsat : ∀ α : Nat → Bool, s.f0.Sat α → (survivingCnf (collect s).1.clauses).Sat α := by
    intro α hα
    rw [sat_survivingCnf_iff]
    exact fun nid c hget hng => CNF.entails_clause_def.mp (hsurv nid c hget hng) α hα
  exact ⟨hc.1, hc.2.1, rfl, hc.2.2, fun i hi => lazyTrailEntailment hc.1 i hi, hsurv, hsat⟩

/-! ## 2. Deletion of unreferenced clauses and `reduce` garbage marking -/

/-- Delete every clause slot satisfying `dropPred cid c` that is NOT an active trail reason
(`trail.c:26-43`, `!isActiveLargeReason s cid`). -/
@[expose]
def deleteUnreferencedClauses (s : CdclState) (dropPred : Nat → Clause → Bool) : CdclState :=
  let clauses' := Array.ofFn fun (i : Fin s.clauses.size) =>
    match s.clauses[i.1] with
    | some c => if dropPred i.1 c && !isActiveLargeReason s i.1 then none else some c
    | none => none
  { s with clauses := clauses' }

theorem deleteUnreferencedClauses_sound {s : CdclState} (hinv : LazyTrailInv s)
    (dropPred : Nat → Clause → Bool) :
    let s' := deleteUnreferencedClauses s dropPred
    LazyTrailInv s' ∧
    s'.f0 = s.f0 ∧
    s'.trail = s.trail ∧
    (∀ (nid : Nat) (c : Clause), s'.clauses[nid]? = some (some c) →
      s.f0.EntailsClause (cnfClause c.lits)) ∧
    (∀ α : Nat → Bool, s.f0.Sat α → (survivingCnf s'.clauses).Sat α) := by
  let s' := deleteUnreferencedClauses s dropPred
  have hdb : ∀ (cid : Nat) (c : Clause), s'.clauses[cid]? = some (some c) →
      s.f0.EntailsClause (cnfClause c.lits) := by
    intro cid c hget
    simp only [s', deleteUnreferencedClauses, Array.getElem?_ofFn] at hget
    split at hget
    · rename_i hlt
      simp only [Option.some.injEq] at hget
      cases hget0 : s.clauses[cid] with
      | none => simp [hget0] at hget
      | some c0 =>
        rw [hget0] at hget; dsimp only at hget
        split at hget
        · cases hget
        · simp only [Option.some.injEq] at hget
          rw [← hget]
          exact hinv.db_sound cid c0 (by simp [hlt, hget0])
    · cases hget
  have hinv' : LazyTrailInv s' :=
    lazyTrailInv_withClauses hinv s'.clauses hdb fun i hi cid c hrsn hget _ => by
      have hact : isActiveLargeReason s cid = true := isActiveLargeReason_iff.mpr ⟨i, hi, hrsn⟩
      have hlt : cid < s.clauses.size := (Array.getElem?_eq_some_iff.mp hget).1
      have hce : s.clauses[cid] = some c := (Array.getElem?_eq_some_iff.mp hget).2
      simp only [s', deleteUnreferencedClauses, Array.getElem?_ofFn, hlt, ↓reduceDIte, hce, hact,
        Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  have hsat : ∀ α : Nat → Bool, s.f0.Sat α → (survivingCnf s'.clauses).Sat α :=
    fun α hα => (sat_survivingCnf_iff α s'.clauses).mpr fun nid c hget _ =>
      CNF.entails_clause_def.mp (hdb nid c hget) α hα
  exact ⟨hinv', rfl, rfl, hdb, hsat⟩

/-- Every `.large` trail reason points to a strictly positive decision level (`unflushed == 0` /
level-0 unit propagation flushed). -/
@[expose] def ReasonLevelsPos (s : CdclState) : Prop :=
  ∀ (i : Nat) (_hi : i < s.trail.size) (cid : Nat),
    stateReason s s.trail[i] = .large cid → 0 < stateLevel s s.trail[i]

/-- Every `.large` trail reason clause contains at least one strictly non-level-0 antecedent
besides its forced literal (`collect.c:422`, `new_size > 1`). -/
@[expose] def ReasonHasNonRootAntecedent (s : CdclState) : Prop :=
  ∀ (i : Nat) (_hi : i < s.trail.size) (cid : Nat) (c : Clause),
    stateReason s s.trail[i] = .large cid →
    s.clauses[cid]? = some (some c) →
    ∃ x ∈ c.lits, x ≠ s.trail[i] ∧ 0 < stateLevel s x

/-- Mark clauses matching `markPred cid c` as `garbage := true` when not referenced as an active
trail reason (`reduce.c` + `trail.c:26-43`). -/
@[expose] def markGarbageIf (s : CdclState) (markPred : Nat → Clause → Bool) : CdclState :=
  let clauses' := Array.ofFn fun (i : Fin s.clauses.size) =>
    match s.clauses[i.1] with
    | some c =>
      if markPred i.1 c && !isActiveLargeReason s i.1 then some { c with garbage := true }
      else some c
    | none => none
  { s with clauses := clauses' }

theorem markGarbageIf_sound {s : CdclState} (hinv : LazyTrailInv s)
    (markPred : Nat → Clause → Bool) :
    let s' := markGarbageIf s markPred
    LazyTrailInv s' ∧
    s'.f0 = s.f0 ∧
    s'.trail = s.trail ∧
    (ReasonLevelsPos s → ReasonLevelsPos s') ∧
    (ReasonHasNonRootAntecedent s → ReasonHasNonRootAntecedent s') ∧
    (∀ (nid : Nat) (c : Clause), s'.clauses[nid]? = some (some c) →
      s.f0.EntailsClause (cnfClause c.lits)) ∧
    (∀ α : Nat → Bool, s.f0.Sat α → (survivingCnf s'.clauses).Sat α) := by
  let s' := markGarbageIf s markPred
  have hdb : ∀ (cid : Nat) (c : Clause), s'.clauses[cid]? = some (some c) →
      s.f0.EntailsClause (cnfClause c.lits) := by
    intro cid c hget
    simp only [s', markGarbageIf, Array.getElem?_ofFn] at hget
    split at hget
    · rename_i hlt
      simp only [Option.some.injEq] at hget
      cases hget0 : s.clauses[cid] with
      | none => simp [hget0] at hget
      | some c0 =>
        rw [hget0] at hget; dsimp only at hget
        have hc_lits : c.lits = c0.lits := by
          split at hget <;> simp only [Option.some.injEq] at hget <;> rw [← hget]
        rw [hc_lits]
        exact hinv.db_sound cid c0 (by simp [hlt, hget0])
    · cases hget
  have hactive_same : ∀ (i : Nat) (hi : i < s.trail.size) (cid : Nat) (c : Clause),
      stateReason s s.trail[i] = .large cid →
      s'.clauses[cid]? = some (some c) → s.clauses[cid]? = some (some c) := by
    intro i hi cid c hrsn hget
    have hact : isActiveLargeReason s cid = true :=
      isActiveLargeReason_iff.mpr ⟨i, hi, hrsn⟩
    simp only [s', markGarbageIf, Array.getElem?_ofFn] at hget
    split at hget
    · rename_i hlt
      simp only [Option.some.injEq] at hget
      cases hget0 : s.clauses[cid] with
      | none => simp [hget0] at hget
      | some c0 =>
        rw [hget0, hact] at hget
        simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
          Option.some.injEq] at hget
        subst hget; simp [hlt, hget0]
    · cases hget
  have hinv' : LazyTrailInv s' :=
    lazyTrailInv_withClauses hinv s'.clauses hdb fun i hi cid c hrsn hget _ => by
      have hact : isActiveLargeReason s cid = true := isActiveLargeReason_iff.mpr ⟨i, hi, hrsn⟩
      have hlt : cid < s.clauses.size := (Array.getElem?_eq_some_iff.mp hget).1
      have hce : s.clauses[cid] = some c := (Array.getElem?_eq_some_iff.mp hget).2
      simp only [s', markGarbageIf, Array.getElem?_ofFn, hlt, ↓reduceDIte, hce, hact,
        Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  have hrlp : ReasonLevelsPos s → ReasonLevelsPos s' := fun h i hi cid hrsn => h i hi cid hrsn
  have hrnr : ReasonHasNonRootAntecedent s → ReasonHasNonRootAntecedent s' :=
    fun h i hi cid c hrsn hget => h i hi cid c hrsn (hactive_same i hi cid c hrsn hget)
  have hsat : ∀ α : Nat → Bool, s.f0.Sat α → (survivingCnf s'.clauses).Sat α :=
    fun α hα => (sat_survivingCnf_iff α s'.clauses).mpr fun nid c hget _ =>
      CNF.entails_clause_def.mp (hdb nid c hget) α hα
  exact ⟨hinv', rfl, rfl, hrlp, hrnr, hdb, hsat⟩

/-! ## 3. Flushing root-level & root-antecedent trail reasons (`flushRootReasons`) -/

/-- Check whether trail literal `l` sits at level `0` with non-`.unit` reason, or sits at a
positive level with all `.binary`/`.large` antecedents already at level `0`. -/
@[expose] def shouldFlushReason (s : CdclState) (l : Nat) : Bool :=
  let rsn := stateReason s l
  if stateLevel s l == 0 then rsn != .unit
  else match rsn with
  | .binary other => stateLevel s other == 0
  | .large cid =>
    match s.clauses[cid]? with
    | some (some c) => c.lits.all (fun x => x == l || stateLevel s x == 0)
    | _ => false
  | .decision | .unit => false

/-- Demote literal `l` to decision level `0` with reason `.unit` and record it in `units`. -/
@[expose] def flushLitToUnit (s : CdclState) (l : Nat) : CdclState :=
  let v := litVar l
  { s with
    units := if s.units.contains l then s.units else l :: s.units
    levels := arraySetPad s.levels v 0 0
    reasons := arraySetPad s.reasons v .unit .unit }

@[simp] theorem f0_flushLitToUnit (s : CdclState) (l : Nat) :
    (flushLitToUnit s l).f0 = s.f0 := rfl
@[simp] theorem clauses_flushLitToUnit (s : CdclState) (l : Nat) :
    (flushLitToUnit s l).clauses = s.clauses := rfl
@[simp] theorem trail_flushLitToUnit (s : CdclState) (l : Nat) :
    (flushLitToUnit s l).trail = s.trail := rfl
@[simp] theorem level_flushLitToUnit (s : CdclState) (l : Nat) :
    (flushLitToUnit s l).level = s.level := rfl
@[simp] theorem inconsistent_flushLitToUnit (s : CdclState) (l : Nat) :
    (flushLitToUnit s l).inconsistent = s.inconsistent := rfl

@[simp] theorem stateLevel_flushLitToUnit (s : CdclState) (l x : Nat) :
    stateLevel (flushLitToUnit s l) x =
      if litVar x = litVar l then 0 else stateLevel s x :=
  arraySetPad_getD s.levels (litVar l) 0 0 (litVar x)

@[simp] theorem stateReason_flushLitToUnit (s : CdclState) (l x : Nat) :
    stateReason (flushLitToUnit s l) x =
      if litVar x = litVar l then .unit else stateReason s x :=
  arraySetPad_getD s.reasons (litVar l) .unit .unit (litVar x)

private theorem shouldFlushReason_sound {s : CdclState} (hinv : LazyTrailInv s)
    {i : Nat} (hi : i < s.trail.size) (hfl : shouldFlushReason s s.trail[i] = true) :
    stateReason s s.trail[i] ≠ .decision ∧ s.f0.EntailsClause (cnfClause [s.trail[i]]) := by
  have hrd := hinv.reason_dag i hi; dsimp only at hrd
  unfold shouldFlushReason at hfl; dsimp only at hfl
  by_cases hl0 : stateLevel s s.trail[i] = 0
  · have hnotdec : stateReason s s.trail[i] ≠ .decision := by
      intro hdec; rw [hdec] at hrd; omega
    exact ⟨hnotdec, lazyTrailEntailment_level0 hinv hi hl0⟩
  · have hl0f : (stateLevel s s.trail[i] == 0) = false := beq_false_of_ne hl0
    rw [ite_eq_right (by simp [hl0f])] at hfl
    generalize hrsn : stateReason s s.trail[i] = rsn
    rw [hrsn] at hfl hrd
    cases rsn with
    | decision | unit => simp at hfl
    | binary other =>
      simp only [beq_iff_eq] at hfl
      obtain ⟨hbin, j, hj, _, hjeq, _, _⟩ := hrd
      have hl0_j : stateLevel s s.trail[j] = 0 := by rw [hjeq, stateLevel_litNeg]; exact hfl
      have hent_j := lazyTrailEntailment_level0 hinv hj hl0_j
      rw [hjeq] at hent_j
      refine ⟨by simp, CNF.entails_clause_def.mpr fun α hα => ?_⟩
      obtain ⟨y, hy, hys⟩ := (clause_sat_cnfClause_iff α _).mp
        (CNF.entails_clause_def.mp hbin α hα)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hyeq | hyeq <;> rw [hyeq] at hys
      · exact (sat_cnfClause_singleton α _).mpr hys
      · exact absurd ((sat_cnfClause_singleton α other).mpr hys)
          ((sat_cnfClause_litNeg_iff α other).mp (CNF.entails_clause_def.mp hent_j α hα))
    | large cid =>
      dsimp only at hfl
      cases hget : s.clauses[cid]? with
      | none => rw [hget] at hfl; simp at hfl
      | some opt =>
        cases opt with
        | none => rw [hget] at hfl; simp at hfl
        | some c =>
          rw [hget] at hfl
          simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hfl
          obtain ⟨c0, hget0, _, _, hall⟩ := hrd
          rw [hget] at hget0; injection hget0 with h1; injection h1 with hc; subst hc
          refine ⟨by simp, CNF.entails_clause_def.mpr fun α hα => ?_⟩
          obtain ⟨x, hx, hxs⟩ := (clause_sat_cnfClause_iff α c.lits).mp
            (CNF.entails_clause_def.mp (hinv.db_sound cid c hget) α hα)
          by_cases hxeq : x = s.trail[i]
          · rw [hxeq] at hxs; exact (sat_cnfClause_singleton α _).mpr hxs
          · have hxl0 : stateLevel s x = 0 := (hfl x hx).resolve_left hxeq
            obtain ⟨j, hj, _, hjeq, _, _⟩ := hall x hx hxeq
            have hl0_j : stateLevel s s.trail[j] = 0 := by rw [hjeq, stateLevel_litNeg]; exact hxl0
            have hent_j := lazyTrailEntailment_level0 hinv hj hl0_j
            rw [hjeq] at hent_j
            exact absurd ((sat_cnfClause_singleton α x).mpr hxs)
              ((sat_cnfClause_litNeg_iff α x).mp (CNF.entails_clause_def.mp hent_j α hα))

private theorem flushLitToUnit_preserves_lazyInv {s : CdclState} (hinv : LazyTrailInv s)
    {i : Nat} (hi : i < s.trail.size)
    (hne : stateReason s s.trail[i] ≠ .decision)
    (hent : s.f0.EntailsClause (cnfClause [s.trail[i]])) :
    let s' := flushLitToUnit s s.trail[i]
    LazyTrailInv s' ∧
    (∀ k, decisionsAtMost s' k = decisionsAtMost s k) ∧
    (∀ j (_hj : j < s.trail.size), j ≠ i →
      stateLevel s' s.trail[j] = stateLevel s s.trail[j] ∧
      stateReason s' s.trail[j] = stateReason s s.trail[j]) := by
  have hvar_ne : ∀ {j : Nat} (_hj : j < s.trail.size), j ≠ i →
      litVar s.trail[j] ≠ litVar s.trail[i] :=
    fun hj hne_ji hvar => hne_ji (hinv.vars_nodup _ i hj hi hvar)
  have hdec_eq : ∀ k, decisionsAtMost (flushLitToUnit s s.trail[i]) k = decisionsAtMost s k := by
    intro k
    unfold decisionsAtMost
    rw [trail_flushLitToUnit]
    apply List.filter_congr
    intro x hx
    obtain ⟨j, hj, rfl⟩ := trail_mem_iff_exists.mp hx
    by_cases hji : j = i
    · subst hji
      simp [stateReason_flushLitToUnit, hne]
    · have hv := hvar_ne hj hji
      simp [hv]
  have hinv' : LazyTrailInv (flushLitToUnit s s.trail[i]) := by
    refine ⟨hinv.vars_nodup, ?_, ?_, hinv.db_sound, ?_, ?_, hinv.inconsistent_sound⟩
    · intro j hj
      have hj' : j < s.trail.size := hj
      change stateLevel (flushLitToUnit s s.trail[i]) s.trail[j] ≤ s.level
      rw [stateLevel_flushLitToUnit]
      by_cases hji : j = i
      · subst hji; simp
      · simp [hvar_ne hj' hji, hinv.levels_le j hj']
    · intro a b ha hb hleq hrsn_b
      have ha' : a < s.trail.size := ha
      have hb' : b < s.trail.size := hb
      change stateLevel (flushLitToUnit s s.trail[i]) s.trail[a] =
        stateLevel (flushLitToUnit s s.trail[i]) s.trail[b] at hleq
      change stateReason (flushLitToUnit s s.trail[i]) s.trail[b] = .decision at hrsn_b
      rw [stateLevel_flushLitToUnit, stateLevel_flushLitToUnit] at hleq
      rw [stateReason_flushLitToUnit] at hrsn_b
      have hbi : b ≠ i := by
        rintro rfl
        simp at hrsn_b
      have hvb : litVar s.trail[b] ≠ litVar s.trail[i] := hvar_ne hb' hbi
      have hsr_b : stateReason s s.trail[b] = .decision := by simpa [hvb] using hrsn_b
      have hpos_b : 0 < stateLevel s s.trail[b] := by
        have hrd := hinv.reason_dag b hb'; dsimp only at hrd; rw [hsr_b] at hrd; exact hrd
      have hai : a ≠ i := by
        rintro rfl
        simp only [↓reduceIte, hvb] at hleq
        omega
      have hva : litVar s.trail[a] ≠ litVar s.trail[i] := hvar_ne ha' hai
      have hleq_s : stateLevel s s.trail[a] = stateLevel s s.trail[b] := by
        simpa [hva, hvb] using hleq
      exact hinv.dec_earliest a b ha' hb' hleq_s hsr_b
    · intro u hu
      dsimp only [flushLitToUnit] at hu
      split at hu
      · exact hinv.units_sound u hu
      · rcases List.mem_cons.mp hu with rfl | hu'
        · exact hent
        · exact hinv.units_sound u hu'
    · intro j hj
      have hj' : j < s.trail.size := hj
      change match stateReason (flushLitToUnit s s.trail[i]) s.trail[j] with
        | .decision => 0 < stateLevel (flushLitToUnit s s.trail[i]) s.trail[j]
        | .unit =>
          stateLevel (flushLitToUnit s s.trail[i]) s.trail[j] = 0 ∧
            s.f0.EntailsClause (cnfClause [s.trail[j]])
        | .binary other =>
          s.f0.EntailsClause (cnfClause [s.trail[j], other]) ∧
            ∃ (m : Nat) (_hm : m < s.trail.size), m < j ∧ s.trail[m] = litNeg other ∧
              stateLevel (flushLitToUnit s s.trail[i]) other ≤
                stateLevel (flushLitToUnit s s.trail[i]) s.trail[j] ∧
              lexLt (stateLevel (flushLitToUnit s s.trail[i]) other) m
                (stateLevel (flushLitToUnit s s.trail[i]) s.trail[j]) j
        | .large cid =>
          ∃ c : Clause, s.clauses[cid]? = some (some c) ∧ !c.garbage = true ∧
            s.trail[j] ∈ c.lits ∧
            ∀ x ∈ c.lits, x ≠ s.trail[j] →
              ∃ (m : Nat) (_hm : m < s.trail.size), m < j ∧ s.trail[m] = litNeg x ∧
                stateLevel (flushLitToUnit s s.trail[i]) x ≤
                  stateLevel (flushLitToUnit s s.trail[i]) s.trail[j] ∧
                lexLt (stateLevel (flushLitToUnit s s.trail[i]) x) m
                  (stateLevel (flushLitToUnit s s.trail[i]) s.trail[j]) j
      rw [stateReason_flushLitToUnit, stateLevel_flushLitToUnit]
      by_cases hji : j = i
      · subst hji; simp [hent]
      · have hvj : litVar s.trail[j] ≠ litVar s.trail[i] := hvar_ne hj' hji
        have hrd := hinv.reason_dag j hj'; dsimp only at hrd
        rw [ite_eq_right (by simp [hvj]), ite_eq_right (by simp [hvj])]
        generalize hrsn : stateReason s s.trail[j] = rsn; rw [hrsn] at hrd
        cases rsn with
        | decision | unit => exact hrd
        | binary other =>
          obtain ⟨hbin, m, hm, hmlt, hmeq, hle, hlex⟩ := hrd
          refine ⟨hbin, m, hm, hmlt, hmeq, ?_, ?_⟩
          · rw [stateLevel_flushLitToUnit]
            by_cases hvo : litVar other = litVar s.trail[i]
            · simp [hvo]
            · simp [hvo, hle]
          · rw [stateLevel_flushLitToUnit]
            by_cases hvo : litVar other = litVar s.trail[i]
            · rw [ite_eq_left (by simp [hvo])]
              by_cases hpos : 0 < stateLevel s s.trail[j]
              · exact Or.inl hpos
              · exact Or.inr ⟨by omega, hmlt⟩
            · rw [ite_eq_right (by simp [hvo])]; exact hlex
        | large cid =>
          obtain ⟨c, hget, hng, hmem, hall⟩ := hrd
          refine ⟨c, hget, hng, hmem, fun x hx hxne => ?_⟩
          obtain ⟨m, hm, hmlt, hmeq, hle, hlex⟩ := hall x hx hxne
          refine ⟨m, hm, hmlt, hmeq, ?_, ?_⟩
          · rw [stateLevel_flushLitToUnit]
            by_cases hvx : litVar x = litVar s.trail[i]
            · simp [hvx]
            · simp [hvx, hle]
          · rw [stateLevel_flushLitToUnit]
            by_cases hvx : litVar x = litVar s.trail[i]
            · rw [ite_eq_left (by simp [hvx])]
              by_cases hpos : 0 < stateLevel s s.trail[j]
              · exact Or.inl hpos
              · exact Or.inr ⟨by omega, hmlt⟩
            · rw [ite_eq_right (by simp [hvx])]; exact hlex
  exact ⟨hinv', hdec_eq, fun j hj hne_ji => by simp [hvar_ne hj hne_ji]⟩

/-- Single step of `flushRootReasons` at trail position `i`. -/
@[expose] def flushRootReasonStep (s : CdclState) (i : Nat) : CdclState :=
  if h : i < s.trail.size then
    if shouldFlushReason s s.trail[i] then flushLitToUnit s s.trail[i] else s
  else s

@[simp] theorem f0_flushRootReasonStep (s : CdclState) (i : Nat) :
    (flushRootReasonStep s i).f0 = s.f0 := by
  unfold flushRootReasonStep; split
  · split <;> rfl
  · rfl
@[simp] theorem clauses_flushRootReasonStep (s : CdclState) (i : Nat) :
    (flushRootReasonStep s i).clauses = s.clauses := by
  unfold flushRootReasonStep; split
  · split <;> rfl
  · rfl
@[simp] theorem trail_flushRootReasonStep (s : CdclState) (i : Nat) :
    (flushRootReasonStep s i).trail = s.trail := by
  unfold flushRootReasonStep; split
  · split <;> rfl
  · rfl
@[simp] theorem level_flushRootReasonStep (s : CdclState) (i : Nat) :
    (flushRootReasonStep s i).level = s.level := by
  unfold flushRootReasonStep; split
  · split <;> rfl
  · rfl

/-- Left-to-right loop flushing root-level and all-root-antecedent reasons to `.unit`. -/
@[expose] def flushRootReasonsAux (s : CdclState) (i : Nat) : CdclState :=
  if i < s.trail.size then
    flushRootReasonsAux (flushRootReasonStep s i) (i + 1)
  else s
termination_by s.trail.size - i
decreasing_by
  simp only [trail_flushRootReasonStep]
  omega

/-- Flush all root-level and all-root-antecedent trail reasons to `.unit` at level `0`,
establishing `ReasonLevelsPos` and `ReasonHasNonRootAntecedent` (`trail.c`, `unflushed == 0`). -/
@[expose] def flushRootReasons (s : CdclState) : CdclState :=
  flushRootReasonsAux s 0

private def FlushedBefore (s : CdclState) (bound : Nat) : Prop :=
  ∀ (j : Nat) (_hj : j < s.trail.size), j < bound →
    (∀ cid, stateReason s s.trail[j] = .large cid → 0 < stateLevel s s.trail[j]) ∧
    (∀ cid c, stateReason s s.trail[j] = .large cid → s.clauses[cid]? = some (some c) →
      ∃ x ∈ c.lits, x ≠ s.trail[j] ∧ 0 < stateLevel s x)

private theorem flushRootReasonStep_props {s : CdclState} (hinv : LazyTrailInv s)
    {i : Nat} (hi : i < s.trail.size) (hfb : FlushedBefore s i) :
    let s1 := flushRootReasonStep s i
    LazyTrailInv s1 ∧
    (∀ k, decisionsAtMost s1 k = decisionsAtMost s k) ∧
    FlushedBefore s1 (i + 1) := by
  have hs1_def : flushRootReasonStep s i =
      if shouldFlushReason s s.trail[i] then flushLitToUnit s s.trail[i] else s := by
    simp [flushRootReasonStep, hi]
  have hstep : LazyTrailInv (flushRootReasonStep s i) ∧
      (∀ k, decisionsAtMost (flushRootReasonStep s i) k = decisionsAtMost s k) ∧
      (∀ j (_hj : j < s.trail.size), j ≠ i →
        stateLevel (flushRootReasonStep s i) s.trail[j] = stateLevel s s.trail[j] ∧
        stateReason (flushRootReasonStep s i) s.trail[j] = stateReason s s.trail[j]) := by
    by_cases hfl : shouldFlushReason s s.trail[i] = true
    · obtain ⟨hne, hent⟩ := shouldFlushReason_sound hinv hi hfl
      have hp := flushLitToUnit_preserves_lazyInv hinv hi hne hent
      simpa [hs1_def, hfl] using hp
    · have hflf : shouldFlushReason s s.trail[i] = false := Bool.eq_false_iff.mpr hfl
      rw [hs1_def, ite_eq_right (by simp [hflf])]
      exact ⟨hinv, fun _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩
  refine ⟨hstep.1, hstep.2.1, fun j hj_s1 hji => ?_⟩
  have hj : j < s.trail.size := by simpa using hj_s1
  have htr : (flushRootReasonStep s i).trail[j] = s.trail[j] := by
    simp only [trail_flushRootReasonStep]
  have hcl : (flushRootReasonStep s i).clauses = s.clauses := clauses_flushRootReasonStep s i
  rw [htr, hcl]
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hji) with hjlt | rfl
  · obtain ⟨hlvl_eq, hrsn_eq⟩ := hstep.2.2 j hj (Nat.ne_of_lt hjlt)
    have hfbj := hfb j hj hjlt
    refine ⟨fun cid hrsn => ?_, fun cid c hrsn hget => ?_⟩
    · rw [hrsn_eq] at hrsn; rw [hlvl_eq]; exact hfbj.1 cid hrsn
    · rw [hrsn_eq] at hrsn
      obtain ⟨x, hx, hxne, hxpos⟩ := hfbj.2 cid c hrsn hget
      refine ⟨x, hx, hxne, ?_⟩
      have hrd := hinv.reason_dag j hj; dsimp only at hrd; rw [hrsn] at hrd
      obtain ⟨c0, hget0, _, _, hall⟩ := hrd
      rw [hget] at hget0; injection hget0 with h1; injection h1 with hc; subst hc
      obtain ⟨m, hm, hmlt, hmeq, _, _⟩ := hall x hx hxne
      have hmi : m ≠ i := by omega
      have hx_var : litVar x ≠ litVar s.trail[i] := by
        intro heq
        exact hmi (hinv.vars_nodup m i hm hi (by rw [hmeq, litVar_litNeg, heq]))
      by_cases hfl : shouldFlushReason s s.trail[i] = true
      · rw [hs1_def, ite_eq_left hfl, stateLevel_flushLitToUnit, ite_eq_right (by simp [hx_var])]
        exact hxpos
      · have hflf : shouldFlushReason s s.trail[i] = false := Bool.eq_false_iff.mpr hfl
        rw [hs1_def, ite_eq_right (by simp [hflf])]
        exact hxpos
  · have hno : shouldFlushReason s s.trail[j] = false →
        (∀ cid, stateReason s s.trail[j] = .large cid → 0 < stateLevel s s.trail[j]) ∧
        (∀ cid c, stateReason s s.trail[j] = .large cid → s.clauses[cid]? = some (some c) →
          ∃ x ∈ c.lits, x ≠ s.trail[j] ∧ 0 < stateLevel s x) := by
      intro hflf
      unfold shouldFlushReason at hflf; dsimp only at hflf
      have hlpos : ∀ cid, stateReason s s.trail[j] = .large cid → 0 < stateLevel s s.trail[j] := by
        intro cid hrsn
        by_cases hl0 : stateLevel s s.trail[j] = 0
        · simp only [hl0, beq_self_eq_true, ↓reduceIte, hrsn, bne_eq_false_iff_eq] at hflf
          cases hflf
        · exact Nat.pos_of_ne_zero hl0
      refine ⟨hlpos, fun cid c hrsn hget => ?_⟩
      have hl0f : (stateLevel s s.trail[j] == 0) = false :=
        beq_false_of_ne (Nat.ne_of_gt (hlpos cid hrsn))
      rw [ite_eq_right (by simp [hl0f])] at hflf
      rw [hrsn] at hflf; dsimp only at hflf
      rw [hget] at hflf; dsimp only at hflf
      rw [Bool.eq_false_iff] at hflf
      exact Classical.byContradiction fun hnone => by
        apply hflf
        rw [List.all_eq_true]
        intro x hx
        by_cases hxeq : x = s.trail[j]
        · simp [hxeq]
        · have hx0 : stateLevel s x = 0 :=
            Classical.byContradiction fun hxne => hnone ⟨x, hx, hxeq, Nat.pos_of_ne_zero hxne⟩
          simp [hx0]
    by_cases hfl : shouldFlushReason s s.trail[j] = true
    · rw [hs1_def, ite_eq_left hfl]
      refine ⟨fun cid hrsn => ?_, fun cid _ hrsn _ => ?_⟩ <;> simp at hrsn
    · have hflf : shouldFlushReason s s.trail[j] = false := Bool.eq_false_iff.mpr hfl
      rw [hs1_def, ite_eq_right (by simp [hflf])]
      exact hno hflf

private theorem flushRootReasonsAux_sound :
    ∀ (k : Nat) (s : CdclState) (i : Nat),
      s.trail.size - i ≤ k → LazyTrailInv s → FlushedBefore s i →
      let s' := flushRootReasonsAux s i
      LazyTrailInv s' ∧ ReasonLevelsPos s' ∧ ReasonHasNonRootAntecedent s' ∧
      s'.f0 = s.f0 ∧ s'.trail = s.trail ∧ s'.clauses = s.clauses ∧ s'.level = s.level ∧
      (∀ m, decisionsAtMost s' m = decisionsAtMost s m) := by
  intro k
  induction k with
  | zero =>
    intro s i hle hinv hfb
    have hnlt : ¬ i < s.trail.size := by omega
    unfold flushRootReasonsAux
    rw [ite_eq_right (by simp [hnlt])]
    refine ⟨hinv, fun j hj cid hrsn => (hfb j hj (by omega)).1 cid hrsn,
      fun j hj cid c hrsn hget => (hfb j hj (by omega)).2 cid c hrsn hget,
      rfl, rfl, rfl, rfl, fun _ => rfl⟩
  | succ k ih =>
    intro s i hle hinv hfb
    unfold flushRootReasonsAux
    by_cases hlt : i < s.trail.size
    · rw [ite_eq_left (by simp [hlt])]
      have hs1 := flushRootReasonStep_props hinv hlt hfb
      have hih := ih (flushRootReasonStep s i) (i + 1)
        (by simp; omega) hs1.1 hs1.2.2
      exact ⟨hih.1, hih.2.1, hih.2.2.1,
        hih.2.2.2.1.trans (f0_flushRootReasonStep s i),
        hih.2.2.2.2.1.trans (trail_flushRootReasonStep s i),
        hih.2.2.2.2.2.1.trans (clauses_flushRootReasonStep s i),
        hih.2.2.2.2.2.2.1.trans (level_flushRootReasonStep s i),
        fun m => (hih.2.2.2.2.2.2.2 m).trans (hs1.2.1 m)⟩
    · rw [ite_eq_right (by simp [hlt])]
      refine ⟨hinv, fun j hj cid hrsn => (hfb j hj (by omega)).1 cid hrsn,
        fun j hj cid c hrsn hget => (hfb j hj (by omega)).2 cid c hrsn hget,
        rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- **Root-reason flush soundness**: flushing root-level and all-root-antecedent trail reasons
to `.unit` preserves `LazyTrailInv` and `decisionsAtMost` while establishing both
`ReasonLevelsPos` and `ReasonHasNonRootAntecedent` (ready for `sweep_collect_sound` and
`reduceAndCollect_sound`). -/
theorem flushRootReasons_sound {s : CdclState} (hinv : LazyTrailInv s) :
    let s' := flushRootReasons s
    LazyTrailInv s' ∧
    ReasonLevelsPos s' ∧
    ReasonHasNonRootAntecedent s' ∧
    s'.f0 = s.f0 ∧
    s'.trail = s.trail ∧
    s'.clauses = s.clauses ∧
    s'.level = s.level ∧
    (∀ k, decisionsAtMost s' k = decisionsAtMost s k) ∧
    (∀ (i : Nat) (hi : i < s'.trail.size),
      (s'.f0 ++ unitsCnf (decisionsAtMost s' (stateLevel s' s'.trail[i]))).EntailsClause
        (cnfClause [s'.trail[i]])) := by
  have h := flushRootReasonsAux_sound s.trail.size s 0 (Nat.le_refl _) hinv
    (fun _ _ h0 => absurd h0 (Nat.not_lt_zero _))
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2, fun i hi => lazyTrailEntailment h.1 i hi⟩

/-- Convenience bridge from `Trail.TrailInv` through `flushRootReasons` to
`LazyTrailInv` + `ReasonLevelsPos` + `ReasonHasNonRootAntecedent`. -/
theorem flushRoot_of_trailInv {s : CdclState} (hinv : TrailInv s) :
    let s' := flushRootReasons s
    LazyTrailInv s' ∧ ReasonLevelsPos s' ∧ ReasonHasNonRootAntecedent s' ∧
    s'.f0 = s.f0 ∧ s'.trail = s.trail ∧ s'.clauses = s.clauses ∧ s'.level = s.level := by
  have h := flushRootReasons_sound hinv.toLazy
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

end LeanQbe.T.Examples.Kissat.Ref
