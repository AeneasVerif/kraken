module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Full
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Float64
public import LeanQbe.T.Examples.Kissat.Build.Inl.Float64
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Dimacs
public import LeanQbe.T.Examples.Kissat.Build.Inl.Dimacs
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Limits
public import LeanQbe.T.Examples.Kissat.Build.Inl.Limits
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Arena
public import LeanQbe.T.Examples.Kissat.Build.Inl.Arena
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Watch
public import LeanQbe.T.Examples.Kissat.Build.Inl.Watch
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Heap
public import LeanQbe.T.Examples.Kissat.Build.Inl.Heap
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Backtrack
public import LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Clause
public import LeanQbe.T.Examples.Kissat.Build.Inl.Clause
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Tiers
public import LeanQbe.T.Examples.Kissat.Build.Inl.Tiers
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Bump
public import LeanQbe.T.Examples.Kissat.Build.Inl.Bump
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Internal
public import LeanQbe.T.Examples.Kissat.Build.Inl.Internal
public import LeanQbe.T.Examples.Kissat.Build.Oracle.PropSearch
public import LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Parse
public import LeanQbe.T.Examples.Kissat.Build.Inl.Parse
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Collect
public import LeanQbe.T.Examples.Kissat.Build.Inl.Collect
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Compact
public import LeanQbe.T.Examples.Kissat.Build.Inl.Compact
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Reduce
public import LeanQbe.T.Examples.Kissat.Build.Inl.Reduce
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Deduce
public import LeanQbe.T.Examples.Kissat.Build.Inl.Deduce
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Minimize
public import LeanQbe.T.Examples.Kissat.Build.Inl.Minimize
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Learn
public import LeanQbe.T.Examples.Kissat.Build.Inl.Learn
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Analyze
public import LeanQbe.T.Examples.Kissat.Build.Inl.Analyze
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Decide
public import LeanQbe.T.Examples.Kissat.Build.Inl.Decide
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Restart
public import LeanQbe.T.Examples.Kissat.Build.Inl.Restart
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Extend
public import LeanQbe.T.Examples.Kissat.Build.Inl.Extend
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Lucky
public import LeanQbe.T.Examples.Kissat.Build.Inl.Lucky
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Vivify
public import LeanQbe.T.Examples.Kissat.Build.Inl.Vivify
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Backbone
public import LeanQbe.T.Examples.Kissat.Build.Inl.Backbone
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Transitive
public import LeanQbe.T.Examples.Kissat.Build.Inl.Transitive
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Substitute
public import LeanQbe.T.Examples.Kissat.Build.Inl.Substitute
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Dense
public import LeanQbe.T.Examples.Kissat.Build.Inl.Dense
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Congruence
public import LeanQbe.T.Examples.Kissat.Build.Inl.Congruence
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Kitten
public import LeanQbe.T.Examples.Kissat.Build.Inl.Kitten
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Sweep
public import LeanQbe.T.Examples.Kissat.Build.Inl.Sweep
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Forward
public import LeanQbe.T.Examples.Kissat.Build.Inl.Forward
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Gates
public import LeanQbe.T.Examples.Kissat.Build.Inl.Gates
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Definition
public import LeanQbe.T.Examples.Kissat.Build.Inl.Definition
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Eliminate
public import LeanQbe.T.Examples.Kissat.Build.Inl.Eliminate
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Factor
public import LeanQbe.T.Examples.Kissat.Build.Inl.Factor
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Reorder
public import LeanQbe.T.Examples.Kissat.Build.Inl.Reorder
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Probe
public import LeanQbe.T.Examples.Kissat.Build.Inl.Probe
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Walk
public import LeanQbe.T.Examples.Kissat.Build.Inl.Walk
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Search
public import LeanQbe.T.Examples.Kissat.Build.Inl.Search

/-!
# Whole-Module Plan-Inlined Assembly (`41` Subsystems)

Assembles `(srcMod.inlinePlan fullPlan).fns = InlSeg.allFns allSegs` in `O(#segs)`
without unfolding any function bodies.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Full

open LeanQbe.T

/-- Concatenated whole-module inline plan across all subsystems. -/
@[expose] def fullPlan : InlPlan :=
  LeanQbe.T.Examples.Kissat.Build.Oracle.Float64.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Dimacs.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Limits.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Arena.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Watch.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Heap.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Backtrack.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Clause.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Tiers.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Bump.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Internal.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.PropSearch.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Parse.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Collect.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Compact.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Reduce.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Deduce.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Minimize.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Learn.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Analyze.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Decide.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Restart.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Extend.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Lucky.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Vivify.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Backbone.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Transitive.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Substitute.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Dense.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Congruence.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Kitten.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Sweep.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Forward.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Gates.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Definition.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Eliminate.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Factor.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Reorder.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Probe.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Walk.plan
  ++ LeanQbe.T.Examples.Kissat.Build.Oracle.Search.plan

/-- Ordered list of per-subsystem materialized `InlSeg` certificates. -/
@[expose] noncomputable def allSegs : List InlSeg := [
  LeanQbe.T.Examples.Kissat.Build.Inl.Float64.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Dimacs.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Limits.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Arena.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Watch.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Heap.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Clause.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Bump.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Internal.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Parse.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Collect.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Compact.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Reduce.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Deduce.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Minimize.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Learn.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Analyze.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Decide.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Restart.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Extend.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Lucky.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Vivify.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Backbone.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Transitive.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Substitute.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Dense.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Congruence.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Kitten.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Sweep.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Forward.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Gates.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Definition.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Eliminate.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Factor.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Reorder.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Probe.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Walk.inl.seg,
  LeanQbe.T.Examples.Kissat.Build.Inl.Search.inl.seg
]

/-- Concatenated post-inline function list across all subsystems. -/
@[expose] noncomputable def inlFns : List Fn := InlSeg.allFns allSegs

private def catLAcc {α : Type _} (acc : List α) : List (List α) → List α
  | [] => acc
  | b :: rest => catLAcc (acc ++ b) rest

private def catL {α : Type _} : List (List α) → List α
  | [] => []
  | a :: rest => catLAcc a rest

private theorem catLAcc_eq {α : Type _} : ∀ (acc : List α) (xs : List (List α)),
    catLAcc acc xs = acc ++ xs.foldr (· ++ ·) []
  | acc, [] => (List.append_nil acc).symm
  | acc, b :: rest => by
    dsimp only [catLAcc, List.foldr_cons]
    rw [catLAcc_eq (acc ++ b) rest, List.append_assoc]

private theorem foldr_append_eq_allSrcFns :
    ∀ (segs : List InlSeg),
      (segs.map InlSeg.srcFns).foldr (· ++ ·) [] = InlSeg.allSrcFns segs
  | [] => rfl
  | s :: rest => congrArg (s.srcFns ++ ·) (foldr_append_eq_allSrcFns rest)

private theorem catL_eq_allSrcFns :
    ∀ (segs : List InlSeg), catL (segs.map InlSeg.srcFns) = InlSeg.allSrcFns segs
  | [] => rfl
  | s :: rest => by
    show catLAcc s.srcFns (rest.map InlSeg.srcFns) = s.srcFns ++ InlSeg.allSrcFns rest
    rw [catLAcc_eq, foldr_append_eq_allSrcFns]

private theorem foldr_append_eq_flatMap {α β : Type _} (f : α → List β) :
    ∀ (xs : List α), (xs.map f).foldr (· ++ ·) [] = xs.flatMap f
  | [] => rfl
  | x :: rest => congrArg (f x ++ ·) (foldr_append_eq_flatMap f rest)

private theorem catL_eq_flatMap {α β : Type _} (f : α → List β) :
    ∀ (xs : List α), catL (xs.map f) = xs.flatMap f
  | [] => rfl
  | x :: rest => by
    show catLAcc (f x) (rest.map f) = f x ++ rest.flatMap f
    rw [catLAcc_eq, foldr_append_eq_flatMap]

private theorem allSrc_eq :
    LeanQbe.T.Examples.Kissat.Src.Full.kissatModule.fns =
      InlSeg.allSrcFns allSegs :=
  catL_eq_allSrcFns allSegs

private theorem fullPlan_eq : fullPlan = allSegs.flatMap InlSeg.plan :=
  catL_eq_flatMap InlSeg.plan allSegs

private inductive StrTrie where
  | empty : StrTrie
  | node : Bool → List (UInt8 × StrTrie) → StrTrie

private def findChild : List (UInt8 × StrTrie) → UInt8 → Option StrTrie
  | [], _ => none
  | (k, v) :: rest, c =>
    if k.toBitVec.toNat == c.toBitVec.toNat then some v else findChild rest c

private def updChild :
    List (UInt8 × StrTrie) → UInt8 → (StrTrie → StrTrie) → List (UInt8 × StrTrie)
  | [], c, f => [(c, f .empty)]
  | (k, v) :: rest, c, f =>
    if k.toBitVec.toNat == c.toBitVec.toNat then (k, f v) :: rest
    else (k, v) :: updChild rest c f

private def StrTrie.memBytes : StrTrie → List UInt8 → Bool
  | .empty, _ => false
  | .node p _, [] => p
  | .node _ cs, c :: rest =>
    match findChild cs c with | some t => t.memBytes rest | none => false

private def StrTrie.insBytes : StrTrie → List UInt8 → StrTrie
  | .empty, [] => .node true []
  | .empty, c :: rest => .node false [(c, StrTrie.empty.insBytes rest)]
  | .node _ cs, [] => .node true cs
  | .node p cs, c :: rest => .node p (updChild cs c (fun t => t.insBytes rest))

private def StrTrie.checkList (t : StrTrie) : List Sym → Option StrTrie
  | [] => some t
  | s :: rest =>
    let bs := s.toByteArray.data.toList
    if t.memBytes bs then none else (t.insBytes bs).checkList rest

private def StrTrie.checkSegs (t : StrTrie) : List InlSeg → Option StrTrie
  | [] => some t
  | s :: rest =>
    match t.checkList (s.srcFns.map Fn.name) with
    | none => none
    | some t' => t'.checkSegs rest

private theorem u8_beq_eq {a b : UInt8}
    (h : (a.toBitVec.toNat == b.toBitVec.toNat) = true) : a = b := by
  have h1 : a.toBitVec = b.toBitVec := BitVec.eq_of_toNat_eq (beq_iff_eq.mp h)
  exact UInt8.ofBitVec_toBitVec a ▸ UInt8.ofBitVec_toBitVec b ▸
    congrArg UInt8.ofBitVec h1

private theorem findChild_updChild_self (cs : List (UInt8 × StrTrie)) (c : UInt8)
    (f : StrTrie → StrTrie) :
    findChild (updChild cs c f) c = some (f ((findChild cs c).getD .empty)) := by
  induction cs with
  | nil => simp [updChild, findChild]
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    dsimp only [updChild, findChild]
    cases h : (k.toBitVec.toNat == c.toBitVec.toNat)
    · simp only [Bool.false_eq_true, ↓reduceIte, findChild, h, ih]
    · simp only [↓reduceIte, findChild, h, Option.getD_some]

private theorem findChild_updChild_ne (cs : List (UInt8 × StrTrie)) {c q : UInt8}
    (hne : c ≠ q) (f : StrTrie → StrTrie) :
    findChild (updChild cs c f) q = findChild cs q := by
  induction cs with
  | nil =>
    dsimp only [updChild, findChild]
    have h : (c.toBitVec.toNat == q.toBitVec.toNat) = false := by
      cases hb : (c.toBitVec.toNat == q.toBitVec.toNat)
      · rfl
      · exact False.elim (hne (u8_beq_eq hb))
    simp only [h, Bool.false_eq_true, ↓reduceIte]
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    dsimp only [updChild, findChild]
    cases hc : (k.toBitVec.toNat == c.toBitVec.toNat)
    · simp only [Bool.false_eq_true, ↓reduceIte, findChild]
      cases hq : (k.toBitVec.toNat == q.toBitVec.toNat) <;>
        simp only [Bool.false_eq_true, ↓reduceIte, ih]
    · have hk : k = c := u8_beq_eq hc
      subst hk
      have hq : (k.toBitVec.toNat == q.toBitVec.toNat) = false := by
        cases hb : (k.toBitVec.toNat == q.toBitVec.toNat)
        · rfl
        · exact False.elim (hne (u8_beq_eq hb))
      simp only [↓reduceIte, findChild, hq, Bool.false_eq_true]

private theorem StrTrie.memBytes_insBytes (t : StrTrie) (k q : List UInt8) :
    (t.insBytes k).memBytes q = ((q == k) || t.memBytes q) := by
  induction k generalizing t q with
  | nil =>
    cases t <;> cases q <;> simp [StrTrie.insBytes, StrTrie.memBytes, findChild]
  | cons c rest ih =>
    cases q with
    | nil => cases t <;> simp [StrTrie.insBytes, StrTrie.memBytes]
    | cons b qs =>
      cases t with
      | empty =>
        dsimp only [StrTrie.insBytes, StrTrie.memBytes, findChild]
        cases hcb : (c.toBitVec.toNat == b.toBitVec.toNat)
        · have hne : (b == c) = false := by
            cases hb : (b == c)
            · rfl
            · have heq : b = c := eq_of_beq hb; subst heq; simp at hcb
          simp [hne]
        · have heq : c = b := u8_beq_eq hcb; subst heq
          simp [ih .empty qs, StrTrie.memBytes]
      | node p cs =>
        dsimp only [StrTrie.insBytes, StrTrie.memBytes]
        by_cases hcb : c = b
        · subst hcb
          rw [findChild_updChild_self]
          cases hf : findChild cs c with
          | none => simp [ih .empty qs, StrTrie.memBytes]
          | some sub => simp [ih sub qs]
        · rw [findChild_updChild_ne cs hcb]
          have hne : (b == c) = false := beq_false_of_ne (Ne.symm hcb)
          simp [hne]

private theorem StrTrie.checkList_ok :
    ∀ {t t' : StrTrie} {xs : List Sym},
      t.checkList xs = some t' →
      xs.Nodup ∧
      (∀ x ∈ xs, t.memBytes x.toByteArray.data.toList = false) ∧
      (∀ q, t'.memBytes q = true ↔
        (∃ x ∈ xs, x.toByteArray.data.toList = q) ∨ t.memBytes q = true)
  | t, t', [], h => by
    simp only [StrTrie.checkList, Option.some.injEq] at h; subst h
    exact ⟨List.nodup_nil, (fun _ hm => nomatch hm), (fun q => by simp)⟩
  | t, t', s :: rest, h => by
    dsimp only [StrTrie.checkList] at h
    cases hm : t.memBytes s.toByteArray.data.toList
    · simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hnd, hfresh, hmem⟩ := StrTrie.checkList_ok h
      have hns : s ∉ rest := by
        intro hsr; have hf := hfresh s hsr
        rw [StrTrie.memBytes_insBytes] at hf; simp at hf
      refine ⟨List.nodup_cons.mpr ⟨hns, hnd⟩, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hxr
        · exact hm
        · have hf := hfresh x hxr
          rw [StrTrie.memBytes_insBytes, Bool.or_eq_false_iff] at hf; exact hf.2
      · intro q
        rw [hmem q, StrTrie.memBytes_insBytes, Bool.or_eq_true, beq_iff_eq]
        constructor
        · rintro (⟨x, hxr, rfl⟩ | rfl | hq)
          · exact Or.inl ⟨x, List.mem_cons_of_mem _ hxr, rfl⟩
          · exact Or.inl ⟨s, List.mem_cons_self, rfl⟩
          · exact Or.inr hq
        · rintro (⟨x, hx, rfl⟩ | hq)
          · rcases List.mem_cons.mp hx with rfl | hxr
            · exact Or.inr (Or.inl rfl)
            · exact Or.inl ⟨x, hxr, rfl⟩
          · exact Or.inr (Or.inr hq)
    · simp [hm] at h

private theorem StrTrie.checkSegs_ok :
    ∀ {segs : List InlSeg} {t t' : StrTrie},
      t.checkSegs segs = some t' →
      ((InlSeg.allSrcFns segs).map Fn.name).Nodup ∧
      (∀ x ∈ (InlSeg.allSrcFns segs).map Fn.name,
        t.memBytes x.toByteArray.data.toList = false)
  | [], _, _, _ => ⟨List.nodup_nil, fun _ hm => nomatch hm⟩
  | s :: rest, t, t', h => by
    dsimp only [StrTrie.checkSegs] at h
    cases hc : t.checkList (s.srcFns.map Fn.name) with
    | none => simp [hc] at h
    | some t1 =>
      simp only [hc] at h
      obtain ⟨hnd1, hfr1, hmem1⟩ := StrTrie.checkList_ok hc
      obtain ⟨hnd2, hfr2⟩ := StrTrie.checkSegs_ok h
      dsimp only [InlSeg.allSrcFns]; rw [List.map_append, List.nodup_append]
      refine ⟨⟨hnd1, hnd2, ?_⟩, ?_⟩
      · intro a ha b hb hab; subst hab
        have hf := hfr2 a hb
        have ht : t1.memBytes a.toByteArray.data.toList = true :=
          (hmem1 _).mpr (Or.inl ⟨a, ha, rfl⟩)
        rw [ht] at hf; cases hf
      · intro x hx
        rcases List.mem_append.mp hx with h1 | h2
        · exact hfr1 x h1
        · have hf := hfr2 x h2
          cases ht : t.memBytes x.toByteArray.data.toList
          · rfl
          · have ht1 : t1.memBytes x.toByteArray.data.toList = true :=
              (hmem1 _).mpr (Or.inr ht)
            rw [ht1] at hf; cases hf

private theorem StrTrie.nodup_of_isSome {segs : List InlSeg}
    (h : (StrTrie.empty.checkSegs segs).isSome = true) :
    ((InlSeg.allSrcFns segs).map Fn.name).Nodup := by
  cases hc : StrTrie.empty.checkSegs segs with
  | none => simp [hc] at h
  | some t' => exact (StrTrie.checkSegs_ok hc).1

private theorem allNames_nodup_prop :
    ((InlSeg.allSrcFns allSegs).map Fn.name).Nodup :=
  StrTrie.nodup_of_isSome (by decide)

private theorem allNames_nodup :
    listNodup ((InlSeg.allSrcFns allSegs).map Fn.name) = true :=
  listNodup_iff.mpr allNames_nodup_prop

private def segLocalOk (s : InlSeg) : Bool :=
  let ns := s.srcFns.map Fn.name
  let ds := s.depsExports.map Fn.name
  s.plan.all (fun kv => ns.contains kv.1) &&
  listNodup ds &&
  (planTargetsFor s.plan s.srcFns).all (fun nm => ds.contains nm || ns.contains nm)

private theorem allSrcFns_append :
    ∀ (a b : List InlSeg),
      InlSeg.allSrcFns (a ++ b) = InlSeg.allSrcFns a ++ InlSeg.allSrcFns b
  | [], _ => rfl
  | s :: rest, b => by
    dsimp only [List.cons_append, InlSeg.allSrcFns]
    rw [allSrcFns_append rest b, List.append_assoc]

private theorem planFor_append_of_not_mem {a b : InlPlan} {nm : Sym}
    (h : ∀ kv ∈ a, kv.1 ≠ nm) : planFor (a ++ b) nm = planFor b nm := by
  induction a with
  | nil => rfl
  | cons kv rest ih =>
    dsimp only [List.cons_append, planFor]
    rw [beq_false_of_ne (h kv List.mem_cons_self)]
    exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)

private theorem planFor_eq_nil_of_not_mem {a : InlPlan} {nm : Sym}
    (h : ∀ kv ∈ a, kv.1 ≠ nm) : planFor a nm = [] := by
  induction a with
  | nil => rfl
  | cons kv rest ih =>
    dsimp only [planFor]
    rw [beq_false_of_ne (h kv List.mem_cons_self)]
    exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)

private theorem planFor_append_right_not_mem {a b : InlPlan} {nm : Sym}
    (h : ∀ kv ∈ b, kv.1 ≠ nm) : planFor (a ++ b) nm = planFor a nm := by
  induction a with
  | nil => exact planFor_eq_nil_of_not_mem h
  | cons kv rest ih =>
    dsimp only [List.cons_append, planFor]
    split
    · rfl
    · exact ih

private theorem segLocal_keys {segs : List InlSeg}
    (hloc : segs.all segLocalOk = true) :
    ∀ kv ∈ segs.flatMap InlSeg.plan, kv.1 ∈ (InlSeg.allSrcFns segs).map Fn.name := by
  induction segs with
  | nil => intro _ hm; nomatch hm
  | cons s rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hloc
    obtain ⟨hs, hrest⟩ := hloc
    dsimp only [segLocalOk] at hs; simp only [Bool.and_eq_true] at hs
    intro kv hkv
    dsimp only [List.flatMap_cons, InlSeg.allSrcFns] at hkv ⊢
    rw [List.map_append, List.mem_append]
    rcases List.mem_append.mp hkv with h1 | h2
    · exact Or.inl (List.contains_iff_mem.mp (List.all_eq_true.mp hs.1.1 kv h1))
    · exact Or.inr (ih hrest kv h2)

private def DepsSubFrom (prevFns : List Fn) : List InlSeg → Prop
  | [] => True
  | s :: rest => (∀ e ∈ s.depsExports, e ∈ prevFns) ∧ DepsSubFrom (prevFns ++ s.fns) rest

private theorem depsOkFrom_of_local :
    ∀ (segs pre : List InlSeg) (prevFns : List Fn),
      ((InlSeg.allSrcFns (pre ++ segs)).map Fn.name).Nodup →
      pre.all segLocalOk = true →
      segs.all segLocalOk = true →
      DepsSubFrom prevFns segs →
      InlSeg.DepsOkFrom ((pre ++ segs).flatMap InlSeg.plan) prevFns
        ((InlSeg.allSrcFns pre).map Fn.name) segs
  | [], _, _, _, _, _, _ => trivial
  | s :: rest, pre, prevFns, hnd, hlocPre, hloc, ⟨hsub, hsubRest⟩ => by
    simp only [List.all_cons, Bool.and_eq_true] at hloc
    obtain ⟨hs, hlocRest⟩ := hloc
    have hndSplit :
        ((InlSeg.allSrcFns pre).map Fn.name ++
          (s.srcFns.map Fn.name ++ (InlSeg.allSrcFns rest).map Fn.name)).Nodup := by
      simpa [allSrcFns_append, InlSeg.allSrcFns, List.map_append] using hnd
    obtain ⟨_, hndTail, hdisjPre⟩ := List.nodup_append.mp hndSplit
    obtain ⟨_, _, hdisjSuf⟩ := List.nodup_append.mp hndTail
    have hplan :
        checkPlanAgree ((pre ++ s :: rest).flatMap InlSeg.plan) s.plan
          (s.srcFns.map Fn.name) = true := by
      dsimp only [checkPlanAgree]; rw [List.all_eq_true]
      intro nm hnm
      rw [List.flatMap_append, List.flatMap_cons]
      have hnotPre : ∀ kv ∈ pre.flatMap InlSeg.plan, kv.1 ≠ nm := fun kv hkv =>
        hdisjPre kv.1 (segLocal_keys hlocPre kv hkv) nm (List.mem_append_left _ hnm)
      have hnotSuf : ∀ kv ∈ rest.flatMap InlSeg.plan, kv.1 ≠ nm := fun kv hkv eq =>
        hdisjSuf nm hnm kv.1 (segLocal_keys hlocRest kv hkv) eq.symm
      rw [planFor_append_of_not_mem hnotPre, planFor_append_right_not_mem hnotSuf,
        beq_self_eq_true]
    have hdeps :
        checkSegDepsNames ((InlSeg.allSrcFns pre).map Fn.name)
          (s.depsExports.map Fn.name) (planTargetsFor s.plan s.srcFns) = true := by
      dsimp only [segLocalOk] at hs; simp only [Bool.and_eq_true] at hs
      dsimp only [checkSegDepsNames]; rw [Bool.and_eq_true]
      refine ⟨hs.1.2, ?_⟩
      rw [List.all_eq_true]
      intro nm hnm
      have ht := List.all_eq_true.mp hs.2 nm hnm
      rw [Bool.or_eq_true] at ht ⊢
      rcases ht with hd | hself
      · exact Or.inl hd
      · right
        have hmemSelf : nm ∈ s.srcFns.map Fn.name := List.contains_iff_mem.mp hself
        have hnotInPre : nm ∉ (InlSeg.allSrcFns pre).map Fn.name := fun hmp =>
          hdisjPre nm hmp nm (List.mem_append_left _ hmemSelf) rfl
        have hcf : ((InlSeg.allSrcFns pre).map Fn.name).contains nm = false := by
          cases hc : ((InlSeg.allSrcFns pre).map Fn.name).contains nm
          · rfl
          · exact False.elim (hnotInPre (List.contains_iff_mem.mp hc))
        rw [hcf]; rfl
    have hpreEq : (pre ++ [s]) ++ rest = pre ++ s :: rest := by simp
    have hndNext : ((InlSeg.allSrcFns ((pre ++ [s]) ++ rest)).map Fn.name).Nodup := by
      rwa [hpreEq]
    have hlocPreNext : (pre ++ [s]).all segLocalOk = true := by simp [hlocPre, hs]
    have hrest := depsOkFrom_of_local rest (pre ++ [s]) (prevFns ++ s.fns)
      hndNext hlocPreNext hlocRest hsubRest
    have hnamesNext :
        (InlSeg.allSrcFns (pre ++ [s])).map Fn.name =
          (InlSeg.allSrcFns pre).map Fn.name ++ s.srcFns.map Fn.name := by
      simp [allSrcFns_append, InlSeg.allSrcFns, List.map_append]
    rw [hpreEq, hnamesNext] at hrest
    exact ⟨hplan, hsub, hdeps, hrest⟩

private theorem allLocal_ok : allSegs.all segLocalOk = true := by decide

private theorem depL {s l₁ l₂ : List Fn} (h : ∀ x ∈ s, x ∈ l₁) :
    ∀ x ∈ s, x ∈ l₁ ++ l₂ :=
  InlSeg.forall_mem_mono_append_left h

private theorem depR {s l₁ l₂ : List Fn} (h : ∀ x ∈ s, x ∈ l₂) :
    ∀ x ∈ s, x ∈ l₁ ++ l₂ :=
  InlSeg.forall_mem_mono_append_right h

private theorem depE {P : Fn → Prop} {l₁ l₂ : List Fn}
    (h₂ : ∀ x ∈ l₂, P x) (h₁ : ∀ x ∈ l₁, P x) : ∀ x ∈ l₁ ++ l₂, P x :=
  InlSeg.forall_mem_append_elim h₁ h₂

private theorem deps_sub : DepsSubFrom [] allSegs := ⟨
  InlSeg.forall_mem_nil,
  InlSeg.forall_mem_nil,
  depL <| depR Float64.inl.exports_sub,
  InlSeg.forall_mem_nil,
  InlSeg.forall_mem_nil,
  InlSeg.forall_mem_nil,
  depR Heap.inl.exports_sub,
  depE (depR Backtrack.inl.exports_sub) <|
  depE (depL <| depL <| depR Watch.inl.exports_sub) <|
  depL <| depL <| depL <| depR Arena.inl.exports_sub,
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR Float64.inl.exports_sub,
  depE (depR Tiers.inl.exports_sub) <|
  depL <| depL <| depL <| depR Heap.inl.exports_sub,
  depE (depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
    Float64.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depR Heap.inl.exports_sub,
  depE (depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
    Float64.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depL <| depL <| depR Watch.inl.exports_sub,
  depE (depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR Watch.inl.exports_sub) <|
  depE (depR PropSearch.inl.exports_sub) <|
  depE (depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
    Dimacs.inl.exports_sub) <|
  depE (depL <| depL <| depL <| depL <| depL <| depR Backtrack.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depL <| depL <| depR Heap.inl.exports_sub,
  depE (depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
    Arena.inl.exports_sub) <|
  depE (depL <| depL <| depL <| depL <| depL <| depL <| depR Backtrack.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR Watch.inl.exports_sub,
  depE (depR Collect.inl.exports_sub) <|
  depE (depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
    Watch.inl.exports_sub) <|
  depE (depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
    Arena.inl.exports_sub) <|
  depL <| depL <| depR PropSearch.inl.exports_sub,
  depE (depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
    Arena.inl.exports_sub) <|
  depE (depL <| depL <| depL <| depL <| depR Internal.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depR Limits.inl.exports_sub) <|
  depE (depR Compact.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depR Float64.inl.exports_sub) <|
  depE (depL <| depL <| depL <| depL <| depL <| depL <| depR Tiers.inl.exports_sub) <|
  depE (depL <| depL <| depL <| depR PropSearch.inl.exports_sub) <|
  depL <| depR Collect.inl.exports_sub,
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depR Arena.inl.exports_sub) <|
  depE (depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
    Watch.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR Tiers.inl.exports_sub,
  InlSeg.forall_mem_nil,
  depE (depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
    Backtrack.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depR Watch.inl.exports_sub,
  depE (depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
    Tiers.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depR Backtrack.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depR Limits.inl.exports_sub) <|
  depL <| depL <| depR Deduce.inl.exports_sub,
  depE (depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
    Tiers.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depR Backtrack.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR Float64.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depR Limits.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depL <| depR Heap.inl.exports_sub,
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depR Heap.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depR Tiers.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depR Limits.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR Float64.inl.exports_sub,
  InlSeg.forall_mem_nil,
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR Arena.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depR Backtrack.inl.exports_sub) <|
  depE (depL <| depL <| depL <| depR Analyze.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
  PropSearch.inl.exports_sub,
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depR Tiers.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depR PropSearch.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR Arena.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depR Backtrack.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR Watch.inl.exports_sub,
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depR Float64.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depR PropSearch.inl.exports_sub,
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depR PropSearch.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
  Watch.inl.exports_sub,
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depR Collect.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
    Arena.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR Clause.inl.exports_sub) <|
  depE (depL <| depL <| depL <| depL <| depR Extend.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depL <| depL <| depR PropSearch.inl.exports_sub,
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
    Backtrack.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
    Watch.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depR Arena.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depR PropSearch.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depL <| depR Collect.inl.exports_sub,
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depR Arena.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depR Watch.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depR Limits.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
  Clause.inl.exports_sub,
  InlSeg.forall_mem_nil,
  depE (depL <| depL <| depR Dense.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depR Watch.inl.exports_sub) <|
  depE (depL <| depR Congruence.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
    Clause.inl.exports_sub) <|
  depR Kitten.inl.exports_sub,
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depR Clause.inl.exports_sub) <|
  depE (depL <| depL <| depL <| depR Dense.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depR Arena.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depR Collect.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depL <| depL <| depR Watch.inl.exports_sub,
  InlSeg.forall_mem_nil,
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depR Backtrack.inl.exports_sub) <|
  depE (depL <| depL <| depL <| depR Kitten.inl.exports_sub) <|
  depR Gates.inl.exports_sub,
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depR Internal.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR Limits.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
    Float64.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depR Backtrack.inl.exports_sub) <|
  depE (depL <| depL <| depL <| depL <| depL <| depL <| depR Dense.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depR Watch.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR Arena.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depR Clause.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depR Extend.inl.exports_sub,
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
    Limits.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depR Clause.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR Watch.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR Arena.inl.exports_sub,
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR Heap.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
    Arena.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depL <| depL <| depR Bump.inl.exports_sub,
  depE (depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
    Dense.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depL <| depL <| depL <| depL <| depR Tiers.inl.exports_sub,
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
    Backtrack.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR
    Arena.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depL <| depR Float64.inl.exports_sub,
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depR Extend.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depR Parse.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depR Restart.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depR Internal.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR Tiers.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depR Analyze.inl.exports_sub) <|
  depE (depL <| depL <| depR Reorder.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depR Compact.inl.exports_sub) <|
  depE (
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
    depL <| depL <| depL <| depL <| depR PropSearch.inl.exports_sub) <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <| depL <|
  depL <| depL <| depR Collect.inl.exports_sub,
  trivial⟩

private theorem deps_ok : InlSeg.DepsOkFrom fullPlan [] [] allSegs := by
  rw [fullPlan_eq]
  exact depsOkFrom_of_local allSegs [] [] allNames_nodup_prop rfl allLocal_ok deps_sub

/-- Whole-module plan-inlining equality proved in `O(#segs)` via `InlinePlanSeg`. -/
theorem inlFns_eq :
    (LeanQbe.T.Examples.Kissat.Src.Full.kissatModule.inlinePlan fullPlan).fns =
      inlFns :=
  InlSeg.module_inlinePlan_fns_of_segs
    LeanQbe.T.Examples.Kissat.Src.Full.kissatModule fullPlan allSegs
    allSrc_eq allNames_nodup deps_ok

end LeanQbe.T.Examples.Kissat.Build.Inl.Full
