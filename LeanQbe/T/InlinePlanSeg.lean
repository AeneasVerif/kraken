/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.InlinePlan

/-!
# Compositional Subsystem-Local Plan Inlining (`InlinePlanSeg`)

Proves append-splitting and candidate-restriction locality for `inlineFnsPlan` so each subsystem
segment `S` can materialize and kernel-check its post-inline `TFlatFn`s using **only** its own
local `Oracle.<S>.plan` and its dependencies' narrow `Exports` leaves, while `Inl/Full.lean`
assembles `(M.inlinePlan fullPlan).fns = S₁.fns ++ ... ++ S_k.fns` in `O(#segments)` without
unfolding any `Fn.body`:

* `inlineFnsPlan_cons_eq`: per-function step combinator preventing cascading kernel re-reduction.
* `inlineFnsPlan_append`, `inlineFnsPlanCands_append`, `inlineFnsPlanCands_eq`: list splitting.
* `inlineFnsPlan_congr`: plan + candidate-lookup restriction locality.
* `InlSeg`, `SegDepsOkFrom`, `inlineFnsPlan_of_segs`, `Module.inlinePlan_of_segs`: generic
  `O(#segments)` whole-module assembly over pure string-level checkers (`checkPlanAgree`,
  `checkSegDepsNames`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## 1. Per-function step and append-splitting lemmas -/

/-- Single-function step combinator for `inline_seg!`, allowing each function's `rfl` proof to
reference already-materialized `TFlatFn.toFn` constants in `cands` without cascading reduction. -/
theorem inlineFnsPlan_cons_eq (plan : InlPlan) (cands : List Fn) (fn fn' : Fn)
    (rest rest' : List Fn)
    (hfn : fn' = (fn.inline (selectPlanCands plan cands fn.name)).renorm)
    (hrest : rest' = inlineFnsPlan plan (fn' :: cands) rest) :
    fn' :: rest' = inlineFnsPlan plan cands (fn :: rest) := by
  dsimp only [inlineFnsPlan]
  rw [← hfn, ← hrest]

theorem inlineFnsPlan_map_name (plan : InlPlan) :
    ∀ (cands fns : List Fn), (inlineFnsPlan plan cands fns).map Fn.name = fns.map Fn.name
  | _, [] => rfl
  | cands, fn :: rest => by
      dsimp only [inlineFnsPlan, Fn.renorm, Fn.inline]
      simp only [List.map_cons]
      exact congrArg (fn.name :: ·) (inlineFnsPlan_map_name plan _ rest)

theorem inlineFnsPlan_append (plan : InlPlan) :
    ∀ (cands A B : List Fn),
      inlineFnsPlan plan cands (A ++ B) =
        inlineFnsPlan plan cands A ++ inlineFnsPlan plan (inlineFnsPlanCands plan cands A) B
  | _, [], _ => rfl
  | cands, fn :: A, B => by
      simp only [List.cons_append, inlineFnsPlan, inlineFnsPlanCands]
      rw [inlineFnsPlan_append plan _ A B]

theorem inlineFnsPlanCands_append (plan : InlPlan) :
    ∀ (cands A B : List Fn),
      inlineFnsPlanCands plan cands (A ++ B) =
        inlineFnsPlanCands plan (inlineFnsPlanCands plan cands A) B
  | _, [], _ => rfl
  | cands, fn :: A, B => by
      simp only [List.cons_append, inlineFnsPlanCands]
      exact inlineFnsPlanCands_append plan _ A B

theorem inlineFnsPlanCands_eq (plan : InlPlan) :
    ∀ (cands A : List Fn),
      inlineFnsPlanCands plan cands A = (inlineFnsPlan plan cands A).reverse ++ cands
  | _, [] => rfl
  | cands, fn :: A => by
      dsimp only [inlineFnsPlanCands, inlineFnsPlan]
      rw [inlineFnsPlanCands_eq plan _ A, List.reverse_cons, List.append_assoc]
      rfl

/-! ## 2. Candidate-lookup and plan-restriction locality -/

theorem lookupFnByName_mem :
    ∀ {cands : List Fn} {nm : Sym} {fn : Fn},
      lookupFnByName cands nm = some fn → fn ∈ cands ∧ fn.name = nm
  | [], _, _, h => by dsimp only [lookupFnByName] at h; cases h
  | f :: rest, nm, fn, h => by
      dsimp only [lookupFnByName] at h
      split at h
      · rename_i hnm
        injection h with hEq
        subst hEq
        exact ⟨List.mem_cons_self, eq_of_beq hnm⟩
      · obtain ⟨hm, hnm⟩ := lookupFnByName_mem h
        exact ⟨List.mem_cons_of_mem _ hm, hnm⟩

theorem lookupFnByName_eq_none_of_not_mem :
    ∀ {cands : List Fn} {nm : Sym},
      nm ∉ cands.map Fn.name → lookupFnByName cands nm = none
  | [], _, _ => rfl
  | f :: rest, nm, hnot => by
      rw [List.map_cons, List.mem_cons, not_or] at hnot
      dsimp only [lookupFnByName]
      have hne : (f.name == nm) = false := beq_false_of_ne (Ne.symm hnot.1)
      rw [hne]
      exact lookupFnByName_eq_none_of_not_mem hnot.2

theorem lookupFnByName_of_mem_nodup :
    ∀ {cands : List Fn} {e : Fn},
      (cands.map Fn.name).Nodup → e ∈ cands → lookupFnByName cands e.name = some e
  | [], _, _, he => nomatch he
  | f :: rest, e, hnd, he => by
      rw [List.map_cons, List.nodup_cons] at hnd
      dsimp only [lookupFnByName]
      rcases List.mem_cons.mp he with rfl | he'
      · simp
      · have hne : (f.name == e.name) = false :=
          beq_false_of_ne fun eq => hnd.1 (eq ▸ List.mem_map_of_mem he')
        rw [hne]
        exact lookupFnByName_of_mem_nodup hnd.2 he'

private theorem filterMap_congr_mem {α β : Type _} {f g : α → Option β} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x = g x) → xs.filterMap f = xs.filterMap g
  | [], _ => rfl
  | x :: xs, h => by
      simp only [List.filterMap_cons, h x List.mem_cons_self]
      cases g x with
      | none => exact filterMap_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)
      | some b =>
          dsimp only
          exact congrArg (b :: ·)
            (filterMap_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- Locality theorem: `inlineFnsPlan plan cands B` depends on `plan` only at callers in `B`, and on
`cands` only through `lookupFnByName` of callee names listed in `plan` for callers in `B`. -/
theorem inlineFnsPlan_congr {plan₁ plan₂ : InlPlan} :
    ∀ {c₁ c₂ B : List Fn},
      (∀ fn ∈ B, planFor plan₁ fn.name = planFor plan₂ fn.name) →
      (∀ fn ∈ B, ∀ nm ∈ planFor plan₁ fn.name, lookupFnByName c₁ nm = lookupFnByName c₂ nm) →
      inlineFnsPlan plan₁ c₁ B = inlineFnsPlan plan₂ c₂ B
  | _, _, [], _, _ => rfl
  | c₁, c₂, fn :: rest, hplan, hcands => by
      have hp0 : planFor plan₁ fn.name = planFor plan₂ fn.name := hplan fn List.mem_cons_self
      have hcs : selectPlanCands plan₁ c₁ fn.name = selectPlanCands plan₂ c₂ fn.name := by
        dsimp only [selectPlanCands]
        rw [← hp0]
        exact filterMap_congr_mem fun nm hnm => hcands fn List.mem_cons_self nm hnm
      dsimp only [inlineFnsPlan]
      rw [hcs]
      refine congrArg (_ :: ·) (inlineFnsPlan_congr
        (fun g hg => hplan g (List.mem_cons_of_mem _ hg))
        (fun g hg nm hnm => ?_))
      dsimp only [lookupFnByName]
      split
      · rfl
      · exact hcands g (List.mem_cons_of_mem _ hg) nm hnm

/-! ## 3. Pure string-level checkers and `InlSeg` whole-module composition -/

/-- Pure string-only checker verifying `planFor fullPlan nm = planFor segPlan nm` for every caller
name in `names` (zero `Fn.body` unfolding in `Inl/Full.lean`). -/
@[expose] def checkPlanAgree (fullPlan segPlan : InlPlan) (names : List Sym) : Bool :=
  names.all fun nm => planFor fullPlan nm == planFor segPlan nm

theorem planFor_eq_of_checkPlanAgree {fullPlan segPlan : InlPlan} {fns : List Fn}
    (h : checkPlanAgree fullPlan segPlan (fns.map Fn.name) = true) :
    ∀ fn ∈ fns, planFor fullPlan fn.name = planFor segPlan fn.name := by
  intro fn hfn
  have h1 := List.all_eq_true.mp h fn.name (List.mem_map_of_mem hfn)
  exact beq_iff_eq.mp h1

/-- Pure string-only checker verifying that:
1. `depNames` has no duplicate names, and
2. every target in `targets` that appears in `prevNames` also appears in `depNames`. -/
@[expose] def checkSegDepsNames (prevNames depNames targets : List Sym) : Bool :=
  listNodup depNames &&
  targets.all fun nm => depNames.contains nm || !prevNames.contains nm

private theorem nodup_reverse {α : Type _} : ∀ {xs : List α}, xs.Nodup → xs.reverse.Nodup
  | [], h => h
  | x :: xs, h => by
      rw [List.nodup_cons] at h
      rw [List.reverse_cons, List.nodup_append]
      refine ⟨nodup_reverse h.2, by simp, fun a ha b hb heq => ?_⟩
      rw [List.mem_singleton] at hb
      subst hb; subst heq
      exact h.1 (List.mem_reverse.mp ha)

theorem lookupFnByName_agree_of_checkSegDepsNames
    {prevFns depFns : List Fn} {targets : List Sym}
    (hndPrev : (prevFns.map Fn.name).Nodup)
    (hsub : ∀ e ∈ depFns, e ∈ prevFns)
    (hchk : checkSegDepsNames (prevFns.map Fn.name) (depFns.map Fn.name) targets = true) :
    ∀ nm ∈ targets, lookupFnByName prevFns.reverse nm = lookupFnByName depFns nm := by
  dsimp only [checkSegDepsNames] at hchk
  rw [Bool.and_eq_true] at hchk
  have hndDep : (depFns.map Fn.name).Nodup := listNodup_nodup hchk.1
  have hndRev : (prevFns.reverse.map Fn.name).Nodup := by
    rw [List.map_reverse]
    exact nodup_reverse hndPrev
  intro nm hnm
  have ht := List.all_eq_true.mp hchk.2 nm hnm
  rw [Bool.or_eq_true, Bool.not_eq_true'] at ht
  rcases ht with hdep | hnotPrev
  · have hmem : nm ∈ depFns.map Fn.name := by simpa using hdep
    obtain ⟨e, heDep, rfl⟩ := List.mem_map.mp hmem
    have heRev : e ∈ prevFns.reverse := List.mem_reverse.mpr (hsub e heDep)
    rw [lookupFnByName_of_mem_nodup hndRev heRev, lookupFnByName_of_mem_nodup hndDep heDep]
  · have hnotPrev' : nm ∉ prevFns.map Fn.name := by
      intro hm
      have : (prevFns.map Fn.name).contains nm = true := by simpa using hm
      rw [this] at hnotPrev
      cases hnotPrev
    have hnotRev : nm ∉ prevFns.reverse.map Fn.name := by
      rw [List.map_reverse, List.mem_reverse]
      exact hnotPrev'
    have hnotDep : nm ∉ depFns.map Fn.name := by
      intro hm
      obtain ⟨e, heDep, rfl⟩ := List.mem_map.mp hm
      exact hnotPrev' (List.mem_map_of_mem (hsub e heDep))
    rw [lookupFnByName_eq_none_of_not_mem hnotRev, lookupFnByName_eq_none_of_not_mem hnotDep]

/-- Materialized per-subsystem plan-inlining certificate produced by `inline_seg!`. -/
structure InlSeg where
  srcFns : List Fn
  plan : InlPlan
  depsExports : List Fn
  flatFns : List TFlatFn
  fns : List Fn
  fns_flat_eq : fns = flatFns.map TFlatFn.toFn
  inl_eq : fns = inlineFnsPlan plan depsExports srcFns

namespace InlSeg

/-- Right-associated concatenation of segment source function lists. -/
@[expose] def allSrcFns : List InlSeg → List Fn
  | [] => []
  | s :: rest => s.srcFns ++ allSrcFns rest

/-- Right-associated concatenation of segment materialized post-inline function lists. -/
@[expose] def allFns : List InlSeg → List Fn
  | [] => []
  | s :: rest => s.fns ++ allFns rest

/-- Right-associated concatenation of segment materialized `TFlatFn` lists. -/
@[expose] def allFlatFns : List InlSeg → List TFlatFn
  | [] => []
  | s :: rest => s.flatFns ++ allFlatFns rest

theorem fns_map_name (s : InlSeg) : s.fns.map Fn.name = s.srcFns.map Fn.name := by
  rw [s.inl_eq, inlineFnsPlan_map_name]

theorem allFns_map_name :
    ∀ (segs : List InlSeg), (allFns segs).map Fn.name = (allSrcFns segs).map Fn.name
  | [] => rfl
  | s :: rest => by
      dsimp only [allFns, allSrcFns]
      rw [List.map_append, List.map_append, s.fns_map_name, allFns_map_name rest]

theorem allFns_flat_eq : ∀ (segs : List InlSeg), allFns segs = (allFlatFns segs).map TFlatFn.toFn
  | [] => rfl
  | s :: rest => by
      dsimp only [allFns, allFlatFns]
      rw [List.map_append, s.fns_flat_eq, allFns_flat_eq rest]

/-- Inductive dependency-soundness predicate threading accumulated `prevFns` and `prevNames`
across a topological list of `InlSeg`s without unfolding any `Fn.body`. -/
@[expose] def DepsOkFrom (fullPlan : InlPlan) (prevFns : List Fn) (prevNames : List Sym) :
    List InlSeg → Prop
  | [] => True
  | s :: rest =>
      checkPlanAgree fullPlan s.plan (s.srcFns.map Fn.name) = true ∧
      (∀ e ∈ s.depsExports, e ∈ prevFns) ∧
      checkSegDepsNames prevNames (s.depsExports.map Fn.name)
        (planTargetsFor s.plan s.srcFns) = true ∧
      DepsOkFrom fullPlan (prevFns ++ s.fns) (prevNames ++ s.srcFns.map Fn.name) rest

private theorem inlineFnsPlan_of_segs_aux (fullPlan : InlPlan) :
    ∀ (segs : List InlSeg) (prevFns : List Fn) (prevNames : List Sym),
      prevFns.map Fn.name = prevNames →
      (prevNames ++ (allSrcFns segs).map Fn.name).Nodup →
      DepsOkFrom fullPlan prevFns prevNames segs →
      inlineFnsPlan fullPlan prevFns.reverse (allSrcFns segs) = allFns segs
  | [], _, _, _, _, _ => rfl
  | s :: rest, prevFns, prevNames, hpn, hndAll, ⟨hplan, hsub, hdeps, hrest⟩ => by
      dsimp only [allSrcFns, allFns]
      rw [inlineFnsPlan_append]
      have hndPrev : (prevFns.map Fn.name).Nodup := by
        rw [hpn]
        exact (List.nodup_append.mp hndAll).1
      have hplanEq : ∀ fn ∈ s.srcFns, planFor fullPlan fn.name = planFor s.plan fn.name :=
        planFor_eq_of_checkPlanAgree hplan
      have hcandsEq :
          ∀ fn ∈ s.srcFns, ∀ nm ∈ planFor fullPlan fn.name,
            lookupFnByName prevFns.reverse nm = lookupFnByName s.depsExports nm := by
        intro fn hfn nm hnm
        have hnm' : nm ∈ planFor s.plan fn.name := hplanEq fn hfn ▸ hnm
        have ht : nm ∈ planTargetsFor s.plan s.srcFns :=
          List.mem_flatMap.mpr ⟨fn, hfn, hnm'⟩
        have hchk : checkSegDepsNames (prevFns.map Fn.name) (s.depsExports.map Fn.name)
            (planTargetsFor s.plan s.srcFns) = true := hpn ▸ hdeps
        exact lookupFnByName_agree_of_checkSegDepsNames hndPrev hsub hchk nm ht
      have hseg : inlineFnsPlan fullPlan prevFns.reverse s.srcFns = s.fns :=
        (inlineFnsPlan_congr hplanEq hcandsEq).trans s.inl_eq.symm
      have hcandsOut :
          inlineFnsPlanCands fullPlan prevFns.reverse s.srcFns = (prevFns ++ s.fns).reverse := by
        rw [inlineFnsPlanCands_eq, hseg, List.reverse_append]
      have hpn' : (prevFns ++ s.fns).map Fn.name = prevNames ++ s.srcFns.map Fn.name := by
        rw [List.map_append, hpn, s.fns_map_name]
      have hndRest :
          ((prevNames ++ s.srcFns.map Fn.name) ++ (allSrcFns rest).map Fn.name).Nodup := by
        simpa [allSrcFns, List.map_append, List.append_assoc] using hndAll
      rw [hseg, hcandsOut,
        inlineFnsPlan_of_segs_aux fullPlan rest (prevFns ++ s.fns)
          (prevNames ++ s.srcFns.map Fn.name) hpn' hndRest hrest]

/-- Whole-module `inlineFnsPlan` assembly from per-subsystem `InlSeg` certificates in `O(#segs)`
without unfolding any function bodies. -/
theorem inlineFnsPlan_of_segs (fullPlan : InlPlan) (segs : List InlSeg)
    (hnd : listNodup ((allSrcFns segs).map Fn.name) = true)
    (hdeps : DepsOkFrom fullPlan [] [] segs) :
    inlineFnsPlan fullPlan [] (allSrcFns segs) = allFns segs :=
  inlineFnsPlan_of_segs_aux fullPlan segs [] [] rfl
    (by simpa using listNodup_nodup hnd) hdeps

/-- Whole-module `(M.inlinePlan fullPlan).fns = InlSeg.allFns segs` assembly lemma. -/
theorem module_inlinePlan_fns_of_segs (M : Module) (fullPlan : InlPlan) (segs : List InlSeg)
    (hsrc : M.fns = allSrcFns segs)
    (hnd : listNodup ((allSrcFns segs).map Fn.name) = true)
    (hdeps : DepsOkFrom fullPlan [] [] segs) :
    (M.inlinePlan fullPlan).fns = allFns segs := by
  dsimp only [Module.inlinePlan]
  rw [hsrc]
  exact inlineFnsPlan_of_segs fullPlan segs hnd hdeps

/-! ## 4. O(1) Membership Helpers for `exports_sub` & `DepsOkFrom` Assembly -/

theorem forall_mem_nil {α : Type _} {P : α → Prop} : ∀ x ∈ ([] : List α), P x :=
  fun _ h => nomatch h

theorem forall_mem_cons {α : Type _} {P : α → Prop} {a : α} {as : List α}
    (ha : P a) (has : ∀ x ∈ as, P x) : ∀ x ∈ a :: as, P x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact ha
  · exact has x hx'

theorem mem_of_eq_mem {α : Type _} {x y : α} {l : List α} (heq : x = y) (hm : y ∈ l) : x ∈ l :=
  heq ▸ hm

theorem forall_mem_append_elim {α : Type _} {P : α → Prop} {l₁ l₂ : List α}
    (h₁ : ∀ x ∈ l₁, P x) (h₂ : ∀ x ∈ l₂, P x) : ∀ x ∈ l₁ ++ l₂, P x := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact h₁ x h
  · exact h₂ x h

theorem forall_mem_mono_append_left {α : Type _} {s l₁ l₂ : List α}
    (h : ∀ x ∈ s, x ∈ l₁) : ∀ x ∈ s, x ∈ l₁ ++ l₂ :=
  fun x hx => List.mem_append_left l₂ (h x hx)

theorem forall_mem_mono_append_right {α : Type _} {s l₁ l₂ : List α}
    (h : ∀ x ∈ s, x ∈ l₂) : ∀ x ∈ s, x ∈ l₁ ++ l₂ :=
  fun x hx => List.mem_append_right l₁ (h x hx)

end InlSeg

end LeanQbe.T
