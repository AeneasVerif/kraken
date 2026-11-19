module

public import LeanQbe.T.Examples.Kissat.LayerAMinimize1

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

@[expose] public section

namespace LeanQbe.T.Examples.Kissat

open Std.Sat

/-! ## 1. CNF views, active trail reasons, and generalized `RefTarget` relocation -/

/-- Conjunction of all non-garbage clauses stored in `clauses`. -/
def survivingCnf (clauses : Array (Option Clause)) : CNF Nat :=
  clauses.foldl (init := CNF.empty) fun acc opt =>
    match opt with
    | some c => if c.garbage then acc else acc.add (cnfClause c.lits)
    | none => acc

/-- Conjunction of promoted binary watch pairs `(a, b)`. -/
def binariesCnf (bins : List (Nat × Nat)) : CNF Nat :=
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
  unfold binariesCnf
  suffices ∀ init : CNF Nat,
      (bins.foldl (fun acc p => acc.add (cnfClause [p.1, p.2])) init).Sat α ↔
        init.Sat α ∧ ∀ p ∈ bins, (cnfClause [p.1, p.2]).Sat α by
    simpa using this CNF.empty
  induction bins with
  | nil => intro init; simp
  | cons x xs ih =>
    intro init
    simp only [List.foldl_cons, ih, CNF.sat_add, List.mem_cons, forall_eq_or_imp]
    exact ⟨fun ⟨⟨hx, hi⟩, hxs⟩ => ⟨hi, hx, hxs⟩, fun ⟨hi, hx, hxs⟩ => ⟨⟨hx, hi⟩, hxs⟩⟩

/-- Active-reason predicate (`trail.c:26-43`): `true` iff some trail literal cites `.large cid`
as its `stateReason`. -/
def isActiveLargeReason (s : CdclState) (cid : Nat) : Bool :=
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
def remapReasonTarget (targets : Array RefTarget) (lit : Nat) : Reason → Reason
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

def remapReasonStep (targets : Array RefTarget) (rs : Array Reason)
    (lit : Nat) : Array Reason :=
  let v := litVar lit
  if h : v < rs.size then rs.set v (remapReasonTarget targets lit rs[v]) else rs

/-- Update trail reason entries for every variable assigned on `trail`. -/
def remapReasons (trail : Array Nat) (reasons : Array Reason)
    (targets : Array RefTarget) : Array Reason :=
  trail.foldl (remapReasonStep targets) reasons

/-- Apply relocated/compacted clause database and target reason mapping to `CdclState`. -/
def applyRefTargets (s : CdclState) (newClauses : Array (Option Clause))
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

private theorem list_map_nodup_of_getElem {l : List Nat}
    (h : ∀ i j (hi : i < l.length) (hj : j < l.length), litVar l[i] = litVar l[j] → i = j) :
    (l.map litVar).Nodup := by
  induction l with
  | nil => simp
  | cons a as ih =>
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      obtain ⟨b, hb, hvar⟩ := List.mem_map.mp hm
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hb
      have hk1 : k + 1 < (a :: as).length := by simpa using Nat.succ_lt_succ hk
      have heq := h 0 (k + 1) (by simp) hk1 (by simpa using hvar.symm)
      omega
    · refine ih fun i j hi hj hvar => ?_
      have hi1 : i + 1 < (a :: as).length := by simpa using Nat.succ_lt_succ hi
      have hj1 : j + 1 < (a :: as).length := by simpa using Nat.succ_lt_succ hj
      have heq := h (i + 1) (j + 1) hi1 hj1 (by simpa using hvar)
      omega

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
  have hrs := collectClauses_sound hinv.db_sound
  let rmap := (collectClauses s.clauses).2
  let s' : CdclState :=
    { s with
      clauses := (collectClauses s.clauses).1
      reasons := s.reasons.map (remapReason rmap) }
  have htr : s'.trail = s.trail := rfl
  have hf0 : s'.f0 = s.f0 := rfl
  have hlvl : ∀ x, stateLevel s' x = stateLevel s x := fun _ => rfl
  have hinv' : LazyTrailInv s' := by
    refine ⟨hinv.vars_nodup, hinv.levels_le, ?_, hrs.2.2, hinv.units_sound, ?_,
      hinv.inconsistent_sound⟩
    · intro i j hi hj hleq hrsn_j
      have hsr : stateReason s' s'.trail[j] = remapReason rmap (stateReason s s.trail[j]) :=
        stateReason_map (by rfl) _
      rw [hsr, remapReason_eq_decision] at hrsn_j
      exact hinv.dec_earliest i j hi hj hleq hrsn_j
    · intro i hi
      have hrd := hinv.reason_dag i hi; dsimp only at hrd
      have hsr : stateReason s' s.trail[i] = remapReason rmap (stateReason s s.trail[i]) :=
        stateReason_map (by rfl) _
      change match stateReason s' s'.trail[i] with | _ => _
      simp only [htr, hf0, hlvl, hsr]
      generalize hrsn : stateReason s s.trail[i] = rsn; rw [hrsn] at hrd
      cases rsn with
      | decision | unit | binary _ => exact hrd
      | large cid =>
        obtain ⟨c, hget, hng, hlmem, hall⟩ := hrd
        obtain ⟨nid, hlkp, hnew⟩ := hrs.2.1 cid c hget hng
        dsimp only [remapReason]
        rw [show (collectClauses s.clauses).2.lookup cid = some nid from hlkp]
        exact ⟨c, hnew, hng, hlmem, hall⟩
  have hsurv : ∀ (nid : Nat) (c : Clause),
      s'.clauses[nid]? = some (some c) → !c.garbage = true →
      s.f0.EntailsClause (cnfClause c.lits) :=
    fun nid c hget _ => hrs.2.2 nid c hget
  have hsat : ∀ α : Nat → Bool, s.f0.Sat α → (survivingCnf s'.clauses).Sat α := by
    intro α hα
    rw [sat_survivingCnf_iff]
    intro nid c hget hng
    exact CNF.entails_clause_def.mp (hsurv nid c hget hng) α hα
  exact ⟨hinv', rfl, rfl, hrs, fun i hi => lazyTrailEntailment hinv' i hi, hsurv, hsat⟩

/-! ## 2. Deletion of unreferenced clauses and `reduce` garbage marking -/

/-- Delete every clause slot satisfying `dropPred cid c` that is NOT an active trail reason
(`trail.c:26-43`, `!isActiveLargeReason s cid`). -/
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
  have hs_tr : s'.trail = s.trail := rfl
  have hs_f0 : s'.f0 = s.f0 := rfl
  have hs_lvl : ∀ x, stateLevel s' x = stateLevel s x := fun _ => rfl
  have hs_rsn : ∀ x, stateReason s' x = stateReason s x := fun _ => rfl
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
  have hinv' : LazyTrailInv s' := by
    refine ⟨hinv.vars_nodup, hinv.levels_le, hinv.dec_earliest, hdb, hinv.units_sound, ?_,
      hinv.inconsistent_sound⟩
    intro i hi
    have hi_s : i < s.trail.size := hi
    have hrd := hinv.reason_dag i hi_s
    dsimp only at hrd
    change match stateReason s' s'.trail[i] with | _ => _
    simp only [hs_tr, hs_f0, hs_lvl, hs_rsn]
    generalize hrsn : stateReason s s.trail[i] = rsn
    rw [hrsn] at hrd
    cases rsn with
    | decision | unit | binary _ => exact hrd
    | large cid =>
      obtain ⟨c, hget, hng, hm, hall⟩ := hrd
      have hact : isActiveLargeReason s cid = true :=
        isActiveLargeReason_iff.mpr ⟨i, hi_s, hrsn⟩
      have hlt : cid < s.clauses.size := by
        rw [Array.getElem?_eq_some_iff] at hget; exact hget.1
      have hget' : s'.clauses[cid]? = some (some c) := by
        simp only [s', deleteUnreferencedClauses, Array.getElem?_ofFn, hlt, ↓reduceDIte]
        have hce : s.clauses[cid] = some c := by
          rw [Array.getElem?_eq_some_iff] at hget; exact hget.2
        simp [hce, hact]
      exact ⟨c, hget', hng, hm, hall⟩
  have hsat : ∀ α : Nat → Bool, s.f0.Sat α → (survivingCnf s'.clauses).Sat α := by
    intro α hα
    rw [sat_survivingCnf_iff]
    intro nid c hget _
    exact CNF.entails_clause_def.mp (hdb nid c hget) α hα
  exact ⟨hinv', rfl, rfl, hdb, hsat⟩

/-- Every `.large` trail reason points to a strictly positive decision level (`unflushed == 0` /
level-0 unit propagation flushed). -/
def ReasonLevelsPos (s : CdclState) : Prop :=
  ∀ (i : Nat) (_hi : i < s.trail.size) (cid : Nat),
    stateReason s s.trail[i] = .large cid → 0 < stateLevel s s.trail[i]

/-- Every `.large` trail reason clause contains at least one strictly non-level-0 antecedent
besides its forced literal (`collect.c:422`, `new_size > 1`). -/
def ReasonHasNonRootAntecedent (s : CdclState) : Prop :=
  ∀ (i : Nat) (_hi : i < s.trail.size) (cid : Nat) (c : Clause),
    stateReason s s.trail[i] = .large cid →
    s.clauses[cid]? = some (some c) →
    ∃ x ∈ c.lits, x ≠ s.trail[i] ∧ 0 < stateLevel s x

/-- Mark clauses matching `markPred cid c` as `garbage := true` when not referenced as an active
trail reason (`reduce.c` + `trail.c:26-43`). -/
def markGarbageIf (s : CdclState) (markPred : Nat → Clause → Bool) : CdclState :=
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
  have hs_tr : s'.trail = s.trail := rfl
  have hs_f0 : s'.f0 = s.f0 := rfl
  have hs_lvl : ∀ x, stateLevel s' x = stateLevel s x := fun _ => rfl
  have hs_rsn : ∀ x, stateReason s' x = stateReason s x := fun _ => rfl
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
        subst hget
        simp [hlt, hget0]
    · cases hget
  have hinv' : LazyTrailInv s' := by
    refine ⟨hinv.vars_nodup, hinv.levels_le, hinv.dec_earliest, hdb, hinv.units_sound, ?_,
      hinv.inconsistent_sound⟩
    intro i hi
    have hi_s : i < s.trail.size := hi
    have hrd := hinv.reason_dag i hi_s
    dsimp only at hrd
    change match stateReason s' s'.trail[i] with | _ => _
    simp only [hs_tr, hs_f0, hs_lvl, hs_rsn]
    generalize hrsn : stateReason s s.trail[i] = rsn
    rw [hrsn] at hrd
    cases rsn with
    | decision | unit | binary _ => exact hrd
    | large cid =>
      obtain ⟨c, hget, hng, hm, hall⟩ := hrd
      have hact : isActiveLargeReason s cid = true :=
        isActiveLargeReason_iff.mpr ⟨i, hi_s, hrsn⟩
      have hlt : cid < s.clauses.size := by
        rw [Array.getElem?_eq_some_iff] at hget; exact hget.1
      have hget' : s'.clauses[cid]? = some (some c) := by
        simp only [s', markGarbageIf, Array.getElem?_ofFn, hlt, ↓reduceDIte]
        have hce : s.clauses[cid] = some c := by
          rw [Array.getElem?_eq_some_iff] at hget; exact hget.2
        simp [hce, hact]
      exact ⟨c, hget', hng, hm, hall⟩
  have hrlp : ReasonLevelsPos s → ReasonLevelsPos s' := fun h i hi cid hrsn => h i hi cid hrsn
  have hrnr : ReasonHasNonRootAntecedent s → ReasonHasNonRootAntecedent s' :=
    fun h i hi cid c hrsn hget => h i hi cid c hrsn (hactive_same i hi cid c hrsn hget)
  have hsat : ∀ α : Nat → Bool, s.f0.Sat α → (survivingCnf s'.clauses).Sat α := by
    intro α hα
    rw [sat_survivingCnf_iff]
    intro nid c hget _
    exact CNF.entails_clause_def.mp (hdb nid c hget) α hα
  exact ⟨hinv', rfl, rfl, hrlp, hrnr, hdb, hsat⟩

end LeanQbe.T.Examples.Kissat
