/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7Proof
public import LeanQbe.T.Examples.Kissat.FullM7BvaGuFixProof

/-!
# Kissat Unified `M7` Splice & Spec-Table Replacement Helpers (`FullM7Splice`)

Provides composable `spliceFns` and `spliceRows` helpers (preserving module order, signatures,
acyclicity, well-formedness, and `TableImpl` / `ModuleOk` inheritance for untouched functions) so
Wave-4 fixes and dual-target overrides can splice cleanly into `FullM7.m7Module` and inherit
`FullM7Proof` soundness + concrete UNSAT non-vacuity (`XPost := False`).

Concretely wires `FullM7BvaGuFix` (`m7BvaCommitFn` and `m7AnalyzeRsnFn`, `168550f4`) into
`m7BvaGuModule`, proving `m7BvaGu_acyclic`, `m7BvaGu_moduleOk`, `m7BvaGu_solve_bytes_sound`, and
`m7BvaGu_unsat_nv` with zero `sorry`/`axiom`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7Splice

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6Transport
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7BvaGuFix

/-! ## 1. Generic `spliceFns` / `spliceRows` Helpers -/

/-- Replace each `Fn` in `fs` whose `name` matches an entry in `repls` (first match wins). -/
def spliceFns (repls : List Fn) (fs : List Fn) : List Fn :=
  fs.map fun f => (repls.find? (·.name == f.name)).getD f

/-- Replace each `SpecEntry` in `tbl` whose `name` matches an entry in `repls` (first match
wins). -/
def spliceRows (repls : List SpecEntry) (tbl : List SpecEntry) : List SpecEntry :=
  tbl.map fun e => (repls.find? (·.name == e.name)).getD e

theorem spliceFns_mem_of_ne {repls fs : List Fn} {g : Fn} (hg : g ∈ fs)
    (hne : ∀ r ∈ repls, r.name ≠ g.name) : g ∈ spliceFns repls fs := by
  refine List.mem_map.mpr ⟨g, hg, ?_⟩
  cases h : repls.find? (fun x => x.name == g.name) with
  | none => rfl
  | some r =>
    have hb : (r.name == g.name) = true := List.find?_some (p := fun x : Fn => x.name == g.name) h
    exact absurd (beq_iff_eq.mp hb) (hne r (List.mem_of_find?_eq_some h))

theorem spliceFns_append (repls fs₁ fs₂ : List Fn) :
    spliceFns repls (fs₁ ++ fs₂) = spliceFns repls fs₁ ++ spliceFns repls fs₂ := by
  unfold spliceFns; exact List.map_append

theorem spliceFns_length (repls fs : List Fn) :
    (spliceFns repls fs).length = fs.length := by
  unfold spliceFns; simp only [List.length_map]

theorem spliceRows_append (repls rs₁ rs₂ : List SpecEntry) :
    spliceRows repls (rs₁ ++ rs₂) = spliceRows repls rs₁ ++ spliceRows repls rs₂ := by
  unfold spliceRows; exact List.map_append

theorem spliceRows_length (repls tbl : List SpecEntry) :
    (spliceRows repls tbl).length = tbl.length := by
  unfold spliceRows; simp only [List.length_map]

private theorem fn_find_name_eq {repls : List Fn} {f r : Fn}
    (h : repls.find? (fun x => x.name == f.name) = some r) : r.name = f.name := by
  have hb : (r.name == f.name) = true := List.find?_some (p := fun x : Fn => x.name == f.name) h
  exact beq_iff_eq.mp hb

private theorem row_find_name_eq {repls : List SpecEntry} {e r : SpecEntry}
    (h : repls.find? (fun x => x.name == e.name) = some r) : r.name = e.name := by
  have hb : (r.name == e.name) = true :=
    List.find?_some (p := fun x : SpecEntry => x.name == e.name) h
  exact beq_iff_eq.mp hb

theorem spliceFns_sigs {repls fs : List Fn}
    (hsig : ∀ r ∈ repls, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig) :
    (spliceFns repls fs).map Fn.sig = fs.map Fn.sig := by
  unfold spliceFns
  rw [List.map_map]
  apply List.map_congr_left
  intro f hf
  dsimp only [Function.comp_def]
  cases h : repls.find? (fun x => x.name == f.name) with
  | none => rfl
  | some r => exact hsig r (List.mem_of_find?_eq_some h) f hf (fn_find_name_eq h)

theorem spliceFns_wf {repls fs : List Fn}
    (hfs : ∀ f ∈ fs, f.Wf) (hr : ∀ r ∈ repls, r.Wf) :
    ∀ f ∈ spliceFns repls fs, f.Wf := by
  intro f hf
  rcases List.mem_map.mp hf with ⟨g, hg, rfl⟩
  cases h : repls.find? (fun x => x.name == g.name) with
  | none => exact hfs g hg
  | some r => exact hr r (List.mem_of_find?_eq_some h)

theorem spliceRows_sigs {repls tbl : List SpecEntry}
    (hsig : ∀ r ∈ repls, ∀ e ∈ tbl, r.name = e.name →
      (r.name, r.as, r.rs) = (e.name, e.as, e.rs)) :
    (spliceRows repls tbl).map (fun e => (e.name, e.as, e.rs)) =
      tbl.map (fun e => (e.name, e.as, e.rs)) := by
  unfold spliceRows
  rw [List.map_map]
  apply List.map_congr_left
  intro e he
  dsimp only [Function.comp_def]
  cases h : repls.find? (fun x => x.name == e.name) with
  | none => rfl
  | some r => exact hsig r (List.mem_of_find?_eq_some h) e he (row_find_name_eq h)

theorem spliceRows_noExit {repls tbl : List SpecEntry}
    (ht : tbl.all SpecEntry.noExit = true) (hr : repls.all SpecEntry.noExit = true) :
    (spliceRows repls tbl).all SpecEntry.noExit = true := by
  rw [List.all_eq_true] at ht hr ⊢
  intro e he
  rcases List.mem_map.mp he with ⟨e₀, he₀, rfl⟩
  cases h : repls.find? (fun x => x.name == e₀.name) with
  | none => exact ht e₀ he₀
  | some r => exact hr r (List.mem_of_find?_eq_some h)

theorem spliceRows_nodup {repls tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hsig : ∀ r ∈ repls, ∀ e ∈ tbl, r.name = e.name →
      (r.name, r.as, r.rs) = (e.name, e.as, e.rs)) :
    ((spliceRows repls tbl).map SpecEntry.name).Nodup := by
  have hm := congrArg (List.map Prod.fst) (spliceRows_sigs hsig)
  simp only [List.map_map, Function.comp_def] at hm
  exact hm ▸ hnd

/-! ### Simultaneous `splice` + Anchor-Insertion Helpers (`patchFns` / `patchRows`) -/

/-- Helper functions queued immediately before `f.name` from `(anchor, hs) ∈ befores`. -/
def patchInsAt (befores : List (Sym × List Fn)) (f : Fn) : List Fn :=
  (befores.filterMap fun (a, hs) => if a == f.name then some hs else none).flatten

/-- Helper rows queued immediately before `e.name` from `(anchor, rs) ∈ befores`. -/
def patchRowInsAt (befores : List (Sym × List SpecEntry)) (e : SpecEntry) : List SpecEntry :=
  (befores.filterMap fun (a, rs) => if a == e.name then some rs else none).flatten

/-- Simultaneously replace functions matching `repls` and insert queued helpers `befores`
immediately before each matching anchor `Fn` in `fs`. -/
def patchFns (repls : List Fn) (befores : List (Sym × List Fn)) (fs : List Fn) : List Fn :=
  fs.flatMap fun f => patchInsAt befores f ++ [(repls.find? (·.name == f.name)).getD f]

/-- Simultaneously replace rows matching `repls` and insert queued rows `befores` immediately
before each matching anchor `SpecEntry` in `tbl`. -/
def patchRows (repls : List SpecEntry) (befores : List (Sym × List SpecEntry))
    (tbl : List SpecEntry) : List SpecEntry :=
  tbl.flatMap fun e => patchRowInsAt befores e ++ [(repls.find? (·.name == e.name)).getD e]

theorem patchFns_nil (repls fs : List Fn) : patchFns repls [] fs = spliceFns repls fs := by
  unfold patchFns spliceFns patchInsAt
  induction fs with
  | nil => rfl
  | cons f rest ih => simpa using ih

theorem patchRows_nil (repls tbl : List SpecEntry) :
    patchRows repls [] tbl = spliceRows repls tbl := by
  unfold patchRows spliceRows patchRowInsAt
  induction tbl with
  | nil => rfl
  | cons e rest ih => simpa using ih

theorem patchFns_append (repls : List Fn) (befores : List (Sym × List Fn)) (fs₁ fs₂ : List Fn) :
    patchFns repls befores (fs₁ ++ fs₂) =
      patchFns repls befores fs₁ ++ patchFns repls befores fs₂ := by
  unfold patchFns; exact List.flatMap_append

theorem patchRows_append (repls : List SpecEntry) (befores : List (Sym × List SpecEntry))
    (t₁ t₂ : List SpecEntry) :
    patchRows repls befores (t₁ ++ t₂) =
      patchRows repls befores t₁ ++ patchRows repls befores t₂ := by
  unfold patchRows; exact List.flatMap_append

theorem patchFns_mem_of_ne {repls : List Fn} {befores : List (Sym × List Fn)}
    {fs : List Fn} {g : Fn} (hg : g ∈ fs) (hne : ∀ r ∈ repls, r.name ≠ g.name) :
    g ∈ patchFns repls befores fs := by
  refine List.mem_flatMap.mpr ⟨g, hg, List.mem_append_right _ ?_⟩
  cases h : repls.find? (fun x => x.name == g.name) with
  | none => exact List.mem_singleton_self _
  | some r => exact absurd (fn_find_name_eq h) (hne r (List.mem_of_find?_eq_some h))

theorem patchRows_mem_of_ne {repls : List SpecEntry} {befores : List (Sym × List SpecEntry)}
    {tbl : List SpecEntry} {e₀ : SpecEntry} (he : e₀ ∈ tbl)
    (hne : ∀ r ∈ repls, r.name ≠ e₀.name) : e₀ ∈ patchRows repls befores tbl := by
  refine List.mem_flatMap.mpr ⟨e₀, he, List.mem_append_right _ ?_⟩
  cases h : repls.find? (fun x => x.name == e₀.name) with
  | none => exact List.mem_singleton_self _
  | some r => exact absurd (row_find_name_eq h) (hne r (List.mem_of_find?_eq_some h))

theorem patchRows_repl_mem {repls : List SpecEntry} {befores : List (Sym × List SpecEntry)}
    {tbl : List SpecEntry} {e₀ r : SpecEntry} (he : e₀ ∈ tbl)
    (hfind : repls.find? (fun x => x.name == e₀.name) = some r) :
    r ∈ patchRows repls befores tbl := by
  refine List.mem_flatMap.mpr ⟨e₀, he, List.mem_append_right _ ?_⟩
  rw [hfind]; exact List.mem_singleton_self _

theorem patchRows_ins_mem {repls : List SpecEntry} {befores : List (Sym × List SpecEntry)}
    {tbl : List SpecEntry} {a : Sym} {rs : List SpecEntry} {e₀ r : SpecEntry}
    (hb : (a, rs) ∈ befores) (he : e₀ ∈ tbl) (hna : a = e₀.name) (hr : r ∈ rs) :
    r ∈ patchRows repls befores tbl := by
  refine List.mem_flatMap.mpr ⟨e₀, he, List.mem_append_left _ ?_⟩
  refine List.mem_flatten.mpr ⟨rs, List.mem_filterMap.mpr ⟨(a, rs), hb, ?_⟩, hr⟩
  simp [hna]

private theorem mem_patchInsAt {befores : List (Sym × List Fn)} {g fn : Fn}
    (h : fn ∈ patchInsAt befores g) : ∃ hs, (g.name, hs) ∈ befores ∧ fn ∈ hs := by
  unfold patchInsAt at h
  rcases List.mem_flatten.mp h with ⟨hs, hhs, hfn⟩
  rcases List.mem_filterMap.mp hhs with ⟨⟨a, hs0⟩, hm, hif⟩
  cases hcmp : (a == g.name)
  · simp [hcmp] at hif
  · have ha : a = g.name := beq_iff_eq.mp hcmp
    subst ha
    simp at hif
    subst hif
    exact ⟨hs0, hm, hfn⟩

private theorem mem_patchRowInsAt {befores : List (Sym × List SpecEntry)} {e₀ e : SpecEntry}
    (h : e ∈ patchRowInsAt befores e₀) : ∃ rs, (e₀.name, rs) ∈ befores ∧ e ∈ rs := by
  unfold patchRowInsAt at h
  rcases List.mem_flatten.mp h with ⟨rs, hrs, he⟩
  rcases List.mem_filterMap.mp hrs with ⟨⟨a, rs0⟩, hm, hif⟩
  cases hcmp : (a == e₀.name)
  · simp [hcmp] at hif
  · have ha : a = e₀.name := beq_iff_eq.mp hcmp
    subst ha
    simp at hif
    subst hif
    exact ⟨rs0, hm, he⟩

theorem patchFns_wf {repls fs : List Fn} {befores : List (Sym × List Fn)}
    (hfs : ∀ f ∈ fs, f.Wf) (hr : ∀ r ∈ repls, r.Wf)
    (hi : ∀ p ∈ befores, ∀ h ∈ p.2, h.Wf) :
    ∀ f ∈ patchFns repls befores fs, f.Wf := by
  intro fn hfn
  rcases List.mem_flatMap.mp hfn with ⟨g, hg, hmem⟩
  rcases List.mem_append.mp hmem with h_ins | h_rep
  · rcases mem_patchInsAt h_ins with ⟨hs, hm, hfn_hs⟩
    exact hi (g.name, hs) hm fn hfn_hs
  · rcases List.mem_singleton.mp h_rep with rfl
    cases h : repls.find? (fun x => x.name == g.name) with
    | none => exact hfs g hg
    | some r => exact hr r (List.mem_of_find?_eq_some h)

theorem patchRows_noExit {repls tbl : List SpecEntry} {befores : List (Sym × List SpecEntry)}
    (ht : tbl.all SpecEntry.noExit = true) (hr : repls.all SpecEntry.noExit = true)
    (hi : ∀ p ∈ befores, p.2.all SpecEntry.noExit = true) :
    (patchRows repls befores tbl).all SpecEntry.noExit = true := by
  rw [List.all_eq_true] at ht hr ⊢
  intro e he
  rcases List.mem_flatMap.mp he with ⟨e₀, he₀, hmem⟩
  rcases List.mem_append.mp hmem with h_ins | h_rep
  · rcases mem_patchRowInsAt h_ins with ⟨rs, hm, he_rs⟩
    exact (List.all_eq_true.mp (hi (e₀.name, rs) hm)) e he_rs
  · rcases List.mem_singleton.mp h_rep with rfl
    cases h : repls.find? (fun x => x.name == e₀.name) with
    | none => exact ht e₀ he₀
    | some r => exact hr r (List.mem_of_find?_eq_some h)

theorem patchRows_sigs {replsR : List SpecEntry} {beforesR : List (Sym × List SpecEntry)}
    {replsF : List Fn} {beforesF : List (Sym × List Fn)} :
    ∀ (tbl : List SpecEntry) (fs : List Fn),
    tbl.map (fun e => (e.name, e.as, e.rs)) = fs.map Fn.sig →
    (∀ r ∈ replsR, ∀ e ∈ tbl, r.name = e.name →
      (r.name, r.as, r.rs) = (e.name, e.as, e.rs)) →
    (∀ r ∈ replsF, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig) →
    (∀ e ∈ tbl, ∀ f ∈ fs, e.name = f.name →
      (patchRowInsAt beforesR e).map (fun r => (r.name, r.as, r.rs)) =
        (patchInsAt beforesF f).map Fn.sig) →
    (patchRows replsR beforesR tbl).map (fun e => (e.name, e.as, e.rs)) =
      (patchFns replsF beforesF fs).map Fn.sig
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ | _ :: _, [], h, _, _, _ => by simp at h
  | e :: ts, f :: fs, hsig, hsr, hsf, hins => by
    simp only [List.map_cons, List.cons.injEq] at hsig
    rcases hsig with ⟨hef, hts⟩
    have hnm : e.name = f.name := congrArg Prod.fst hef
    have hsr_r : ∀ r ∈ replsR, ∀ e' ∈ ts, r.name = e'.name →
        (r.name, r.as, r.rs) = (e'.name, e'.as, e'.rs) :=
      fun r hr e' he' => hsr r hr e' (List.mem_cons_of_mem e he')
    have hsf_r : ∀ r ∈ replsF, ∀ f' ∈ fs, r.name = f'.name → r.sig = f'.sig :=
      fun r hr f' hf' => hsf r hr f' (List.mem_cons_of_mem f hf')
    have hins_r : ∀ e' ∈ ts, ∀ f' ∈ fs, e'.name = f'.name →
        (patchRowInsAt beforesR e').map (fun r => (r.name, r.as, r.rs)) =
          (patchInsAt beforesF f').map Fn.sig :=
      fun e' he' f' hf' => hins e' (List.mem_cons_of_mem e he') f' (List.mem_cons_of_mem f hf')
    have hrow : ((replsR.find? (fun x => x.name == e.name)).getD e).name = e.name ∧
        (((replsR.find? (fun x => x.name == e.name)).getD e).as,
          ((replsR.find? (fun x => x.name == e.name)).getD e).rs) = (e.as, e.rs) := by
      cases h : replsR.find? (fun x => x.name == e.name) with
      | none => exact ⟨rfl, rfl⟩
      | some r =>
        dsimp only [Option.getD]
        have heq := hsr r (List.mem_of_find?_eq_some h) e List.mem_cons_self (row_find_name_eq h)
        exact ⟨congrArg Prod.fst heq, Prod.ext (congrArg (fun p => p.2.1) heq)
          (congrArg (fun p => p.2.2) heq)⟩
    have hfn : ((replsF.find? (fun x => x.name == f.name)).getD f).sig = f.sig := by
      cases h : replsF.find? (fun x => x.name == f.name) with
      | none => rfl
      | some r =>
        dsimp only [Option.getD]
        exact hsf r (List.mem_of_find?_eq_some h) f List.mem_cons_self (fn_find_name_eq h)
    have ih := patchRows_sigs (replsR := replsR) (beforesR := beforesR)
      (replsF := replsF) (beforesF := beforesF) ts fs hts hsr_r hsf_r hins_r
    unfold patchRows patchFns at ih
    simp only [patchRows, patchFns, List.flatMap_cons, List.map_append, List.map_cons,
      List.map_nil]
    rw [hins e List.mem_cons_self f List.mem_cons_self hnm, ih]
    have hsigr : (((replsR.find? (fun x => x.name == e.name)).getD e).name,
        ((replsR.find? (fun x => x.name == e.name)).getD e).as,
        ((replsR.find? (fun x => x.name == e.name)).getD e).rs) =
        ((replsF.find? (fun x => x.name == f.name)).getD f).sig := by
      rw [hfn, ← hef]
      exact Prod.ext hrow.1 hrow.2
    rw [hsigr]

theorem sig_mem_patchFns_of_mem {repls fs : List Fn} {befores : List (Sym × List Fn)} {g : Fn}
    (hg : g ∈ fs) (hsig : ∀ r ∈ repls, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig) :
    g.sig ∈ (patchFns repls befores fs).map Fn.sig := by
  refine List.mem_map.mpr ⟨(repls.find? (fun x => x.name == g.name)).getD g, ?_, ?_⟩
  · exact List.mem_flatMap.mpr ⟨g, hg, List.mem_append_right _ List.mem_cons_self⟩
  · cases h : repls.find? (fun x => x.name == g.name) with
    | none => rfl
    | some r => exact hsig r (List.mem_of_find?_eq_some h) g hg (fn_find_name_eq h)

private theorem patchFns_names_map {repls fs : List Fn} {befores : List (Sym × List Fn)}
    (hsig : ∀ r ∈ repls, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig) :
    (patchFns repls befores fs).map Fn.name =
      fs.flatMap fun f => (patchInsAt befores f).map Fn.name ++ [f.name] := by
  induction fs with
  | nil => rfl
  | cons f rest ih =>
    have hsig_r : ∀ r ∈ repls, ∀ g ∈ rest, r.name = g.name → r.sig = g.sig :=
      fun r hr g hg => hsig r hr g (List.mem_cons_of_mem f hg)
    have hname : ((repls.find? (fun x => x.name == f.name)).getD f).name = f.name := by
      cases h : repls.find? (fun x => x.name == f.name) with
      | none => rfl
      | some r => exact fn_find_name_eq h
    simp only [patchFns, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil] at ih ⊢
    rw [hname, ih hsig_r]

theorem patchFns_names_nodup {repls fs : List Fn} {befores : List (Sym × List Fn)}
    (hnd : (fs.map Fn.name).Nodup)
    (hsig : ∀ r ∈ repls, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig)
    (hinsNd : ∀ f ∈ fs, ((patchInsAt befores f).map Fn.name).Nodup)
    (hinsDisj : ∀ f ∈ fs, ∀ h ∈ patchInsAt befores f, h.name ∉ fs.map Fn.name)
    (hinsPair : ∀ f₁ ∈ fs, ∀ f₂ ∈ fs, f₁.name ≠ f₂.name →
      ∀ h ∈ patchInsAt befores f₁, h.name ∉ (patchInsAt befores f₂).map Fn.name) :
    ((patchFns repls befores fs).map Fn.name).Nodup := by
  rw [patchFns_names_map hsig]
  clear hsig repls
  induction fs with
  | nil => exact List.nodup_nil
  | cons f rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hinsNd_r : ∀ g ∈ rest, ((patchInsAt befores g).map Fn.name).Nodup :=
      fun g hg => hinsNd g (List.mem_cons_of_mem f hg)
    have hinsDisj_r : ∀ g ∈ rest, ∀ h ∈ patchInsAt befores g, h.name ∉ rest.map Fn.name :=
      fun g hg h hh hm => hinsDisj g (List.mem_cons_of_mem f hg) h hh
        (by simp [List.mem_cons, hm])
    have hinsPair_r : ∀ g₁ ∈ rest, ∀ g₂ ∈ rest, g₁.name ≠ g₂.name →
        ∀ h ∈ patchInsAt befores g₁, h.name ∉ (patchInsAt befores g₂).map Fn.name :=
      fun g₁ hg₁ g₂ hg₂ => hinsPair g₁ (List.mem_cons_of_mem f hg₁)
        g₂ (List.mem_cons_of_mem f hg₂)
    have hrest_nd := ih hnd.2 hinsNd_r hinsDisj_r hinsPair_r
    simp only [List.flatMap_cons, List.nodup_append]
    refine ⟨⟨hinsNd f List.mem_cons_self, by simp, ?_⟩, hrest_nd, ?_⟩
    · intro x hx y hy hxy
      subst hxy
      simp only [List.mem_singleton] at hy
      subst hy
      rcases List.mem_map.mp hx with ⟨h, hh, hnm⟩
      exact hinsDisj f List.mem_cons_self h hh (by simp [List.mem_cons, hnm])
    · intro x hx y hy hxy
      subst hxy
      rcases List.mem_flatMap.mp hy with ⟨g, hg, hy_g⟩
      have hne_fg : f.name ≠ g.name := fun heq => hnd.1 (heq ▸ List.mem_map_of_mem hg)
      rcases List.mem_append.mp hx with hx_ins | hx_f
      · rcases List.mem_map.mp hx_ins with ⟨h, hh, rfl⟩
        rcases List.mem_append.mp hy_g with hy_ins | hy_gname
        · exact hinsPair f List.mem_cons_self g (List.mem_cons_of_mem f hg) hne_fg h hh hy_ins
        · simp only [List.mem_singleton] at hy_gname
          exact hinsDisj f List.mem_cons_self h hh (by
            simp [List.mem_cons, hy_gname, List.mem_map_of_mem hg])
      · simp only [List.mem_singleton] at hx_f
        subst hx_f
        rcases List.mem_append.mp hy_g with hy_ins | hy_gname
        · rcases List.mem_map.mp hy_ins with ⟨h, hh, hnm⟩
          exact hinsDisj g (List.mem_cons_of_mem f hg) h hh (by simp [List.mem_cons, hnm])
        · simp only [List.mem_singleton] at hy_gname
          exact hne_fg hy_gname

/-! ## 2. Fast O(k) Acyclicity Preservation Across `spliceFns` -/

mutual
  theorem expr_checkCallsOk_mono {a₁ a₂ : List SigEntry} {exits : List Sym}
      (hsub : ∀ s ∈ a₁, s ∈ a₂) {rs : List Ty} :
      (e : Expr (fun _ => Unit) (fun _ => Unit) rs) →
      e.checkCallsOk a₁ exits = true → e.checkCallsOk a₂ exits = true
    | .let_ _ k, h => expr_checkCallsOk_mono hsub (k (Tup.units _)) h
    | .load _ _ k, h => expr_checkCallsOk_mono hsub (k ()) h
    | .store _ _ k, h => expr_checkCallsOk_mono hsub k h
    | .call f (as := as) (bs := bs) _ k, h => by
      simp only [Expr.checkCallsOk, Bool.and_eq_true, List.any_eq_true,
        LeanQbe.T.SigEntry.beq_iff_eq] at h ⊢
      rcases h with ⟨⟨s, hs, heq⟩, hk⟩
      exact ⟨⟨s, hsub s hs, heq⟩, expr_checkCallsOk_mono hsub (k (Tup.units bs)) hk⟩
    | .jnz _ t e, h => by
      simp only [Expr.checkCallsOk, Bool.and_eq_true] at h ⊢
      exact ⟨expr_checkCallsOk_mono hsub t h.1, expr_checkCallsOk_mono hsub e h.2⟩
    | .jump _ _, h | .ret _, h | .hlt, h | .exit _ _, h => h
    | .group (sig := sig) bodies k, h => by
      simp only [Expr.checkCallsOk, Bool.and_eq_true] at h ⊢
      exact ⟨blocks_checkCallsOk_mono hsub (bodies (Tup.units sig)) h.1,
        expr_checkCallsOk_mono hsub (k (Tup.units sig)) h.2⟩

  theorem blocks_checkCallsOk_mono {a₁ a₂ : List SigEntry} {exits : List Sym}
      (hsub : ∀ s ∈ a₁, s ∈ a₂) {rs : List Ty} :
      {sig : List (List Ty)} →
      (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig) →
      bs.checkCallsOk a₁ exits = true → bs.checkCallsOk a₂ exits = true
    | _, .nil, h => h
    | _, .cons b bs, h => by
      simp only [Blocks.checkCallsOk, Bool.and_eq_true] at h ⊢
      exact ⟨expr_checkCallsOk_mono hsub (b (Tup.units _)) h.1,
        blocks_checkCallsOk_mono hsub bs h.2⟩
end

theorem fn_checkCallsOk_mono {a₁ a₂ : List SigEntry} {exits : List Sym} {fn : Fn}
    (hsub : ∀ s ∈ a₁, s ∈ a₂) (h : fn.checkCallsOk a₁ exits = true) :
    fn.checkCallsOk a₂ exits = true :=
  expr_checkCallsOk_mono hsub _ h

theorem checkFnsCallsOk_splice (exits : List Sym) (extSigs : List SigEntry) :
    ∀ (seen fs repls : List Fn),
    LeanQbe.T.Module.checkFnsCallsOk exits extSigs (seen.map Fn.sig) fs = true →
    (∀ r ∈ repls, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig) →
    (∀ pre f post r, fs = pre ++ f :: post → r ∈ repls → r.name = f.name →
      r.checkCallsOk ((seen ++ pre).map Fn.sig ++ extSigs) exits = true) →
    LeanQbe.T.Module.checkFnsCallsOk exits extSigs (seen.map Fn.sig) (spliceFns repls fs) = true
  | _, [], _, _, _, _ => rfl
  | seen, f :: rest, repls, hchk, hsig, hrepl => by
    simp only [LeanQbe.T.Module.checkFnsCallsOk, Bool.and_eq_true] at hchk
    unfold spliceFns
    simp only [List.map_cons, LeanQbe.T.Module.checkFnsCallsOk, Bool.and_eq_true]
    have hsig_rest : ∀ r ∈ repls, ∀ g ∈ rest, r.name = g.name → r.sig = g.sig :=
      fun r hr g hg => hsig r hr g (List.mem_cons_of_mem f hg)
    have hrepl_rest : ∀ pre g post r, rest = pre ++ g :: post → r ∈ repls → r.name = g.name →
        r.checkCallsOk (((seen ++ [f]) ++ pre).map Fn.sig ++ extSigs) exits = true := by
      intro pre g post r hsplit hr hnm
      rw [List.append_assoc]
      exact hrepl (f :: pre) g post r (by rw [hsplit]; rfl) hr hnm
    have hhead_sig : ((repls.find? (fun x => x.name == f.name)).getD f).sig = f.sig := by
      cases h : repls.find? (fun x => x.name == f.name) with
      | none => rfl
      | some r =>
        dsimp only [Option.getD]
        exact hsig r (List.mem_of_find?_eq_some h) f List.mem_cons_self (fn_find_name_eq h)
    have hhead_ok : ((repls.find? (fun x => x.name == f.name)).getD f).checkCallsOk
        (seen.map Fn.sig ++ extSigs) exits = true := by
      cases h : repls.find? (fun x => x.name == f.name) with
      | none => exact hchk.1
      | some r =>
        simpa using hrepl [] f rest r rfl (List.mem_of_find?_eq_some h) (fn_find_name_eq h)
    refine ⟨hhead_ok, ?_⟩
    have hchk2 : LeanQbe.T.Module.checkFnsCallsOk exits extSigs ((seen ++ [f]).map Fn.sig) rest =
        true := by
      simpa only [List.map_append, List.map_singleton] using hchk.2
    rw [hhead_sig, show seen.map Fn.sig ++ [f.sig] = (seen ++ [f]).map Fn.sig by simp]
    exact checkFnsCallsOk_splice exits extSigs (seen ++ [f]) rest repls hchk2
      hsig_rest hrepl_rest

/-- Fast `O(|repls|)` preservation of `Module.checkAcyclic = true` under sig-preserving
`spliceFns repls M.fns`, avoiding re-checking untouched functions. -/
theorem spliceModule_checkAcyclic {M : LeanQbe.T.Module} {repls : List Fn}
    (hM : M.checkAcyclic = true)
    (hsig : ∀ r ∈ repls, ∀ f ∈ M.fns, r.name = f.name → r.sig = f.sig)
    (hrepl : ∀ pre f post r, M.fns = pre ++ f :: post → r ∈ repls → r.name = f.name →
      r.checkCallsOk (pre.map Fn.sig ++ M.externs.map Extern.sig) M.exits = true) :
    ({ M with fns := spliceFns repls M.fns } : LeanQbe.T.Module).checkAcyclic = true := by
  simp only [LeanQbe.T.Module.checkAcyclic, Bool.and_eq_true] at hM ⊢
  refine ⟨?_, ?_⟩
  · have hnames : ({ M with fns := spliceFns repls M.fns } : LeanQbe.T.Module).names = M.names := by
      simp only [LeanQbe.T.Module.names]
      have hm := congrArg (List.map Prod.fst) (spliceFns_sigs hsig)
      simp only [List.map_map, Function.comp_def, Fn.sig] at hm
      rw [hm]
    unfold LeanQbe.T.Module.checkNamesNodup
    rw [hnames]
    exact hM.1
  · exact checkFnsCallsOk_splice M.exits (M.externs.map Extern.sig) [] M.fns repls
      hM.2 hsig (fun pre f post r hsplit hr hn => hrepl pre f post r hsplit hr hn)

theorem checkFnsCallsOk_mono {exits : List Sym} {extSigs : List SigEntry} :
    ∀ {seen₁ seen₂ : List SigEntry} {fs : List Fn},
    (∀ s ∈ seen₁ ++ extSigs, s ∈ seen₂ ++ extSigs) →
    LeanQbe.T.Module.checkFnsCallsOk exits extSigs seen₁ fs = true →
    LeanQbe.T.Module.checkFnsCallsOk exits extSigs seen₂ fs = true
  | _, _, [], _, h => h
  | seen₁, seen₂, f :: rest, hsub, h => by
    simp only [LeanQbe.T.Module.checkFnsCallsOk, Bool.and_eq_true] at h ⊢
    refine ⟨fn_checkCallsOk_mono hsub h.1, checkFnsCallsOk_mono ?_ h.2⟩
    intro s hs
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
    rcases hs with (hs | rfl) | hs
    · rcases List.mem_append.mp (hsub s (List.mem_append_left _ hs)) with h2 | h2
      · exact Or.inl (Or.inl h2)
      · exact Or.inr h2
    · exact Or.inl (Or.inr rfl)
    · rcases List.mem_append.mp (hsub s (List.mem_append_right _ hs)) with h2 | h2
      · exact Or.inl (Or.inl h2)
      · exact Or.inr h2

theorem checkFnsCallsOk_append (exits : List Sym) (extSigs : List SigEntry) :
    ∀ (seen : List SigEntry) (xs ys : List Fn),
    LeanQbe.T.Module.checkFnsCallsOk exits extSigs seen (xs ++ ys) =
      (LeanQbe.T.Module.checkFnsCallsOk exits extSigs seen xs &&
       LeanQbe.T.Module.checkFnsCallsOk exits extSigs (seen ++ xs.map Fn.sig) ys)
  | _, [], _ => by simp [LeanQbe.T.Module.checkFnsCallsOk]
  | seen, x :: xs, ys => by
    simp only [List.cons_append, LeanQbe.T.Module.checkFnsCallsOk,
      checkFnsCallsOk_append exits extSigs (seen ++ [x.sig]) xs ys, List.map_cons,
      Bool.and_assoc, List.append_assoc, List.cons_append, List.nil_append]

theorem checkFnsCallsOk_patch (exits : List Sym) (extSigs : List SigEntry)
    (repls : List Fn) (befores : List (Sym × List Fn)) :
    ∀ (origSeen : List Fn) (seen : List SigEntry) (fs : List Fn),
    (∀ g ∈ origSeen, g.sig ∈ seen) →
    LeanQbe.T.Module.checkFnsCallsOk exits extSigs (origSeen.map Fn.sig) fs = true →
    (∀ r ∈ repls, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig) →
    (∀ pre f post, fs = pre ++ f :: post →
      LeanQbe.T.Module.checkFnsCallsOk exits extSigs
        ((origSeen ++ pre).map Fn.sig) (patchInsAt befores f) = true) →
    (∀ pre f post r, fs = pre ++ f :: post → r ∈ repls → r.name = f.name →
      r.checkCallsOk
        ((origSeen ++ pre).map Fn.sig ++ (patchInsAt befores f).map Fn.sig ++ extSigs)
        exits = true) →
    LeanQbe.T.Module.checkFnsCallsOk exits extSigs seen (patchFns repls befores fs) = true
  | _, _, [], _, _, _, _, _ => rfl
  | origSeen, seen, f :: rest, hsub, hchk, hsig, hins, hrepl => by
    simp only [LeanQbe.T.Module.checkFnsCallsOk, Bool.and_eq_true] at hchk
    unfold patchFns
    simp only [List.flatMap_cons]
    have hsig_rest : ∀ r ∈ repls, ∀ g ∈ rest, r.name = g.name → r.sig = g.sig :=
      fun r hr g hg => hsig r hr g (List.mem_cons_of_mem f hg)
    have hins_rest : ∀ pre g post, rest = pre ++ g :: post →
        LeanQbe.T.Module.checkFnsCallsOk exits extSigs
          (((origSeen ++ [f]) ++ pre).map Fn.sig) (patchInsAt befores g) = true := by
      intro pre g post hsplit
      rw [List.append_assoc]
      exact hins (f :: pre) g post (by rw [hsplit]; rfl)
    have hrepl_rest : ∀ pre g post r, rest = pre ++ g :: post → r ∈ repls → r.name = g.name →
        r.checkCallsOk
          (((origSeen ++ [f]) ++ pre).map Fn.sig ++ (patchInsAt befores g).map Fn.sig ++ extSigs)
          exits = true := by
      intro pre g post r hsplit hr hnm
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        hrepl (f :: pre) g post r (by rw [hsplit]; rfl) hr hnm
    have hhead_sig : ((repls.find? (fun x => x.name == f.name)).getD f).sig = f.sig := by
      cases h : repls.find? (fun x => x.name == f.name) with
      | none => rfl
      | some r =>
        dsimp only [Option.getD]
        exact hsig r (List.mem_of_find?_eq_some h) f List.mem_cons_self (fn_find_name_eq h)
    have hsub_ext : ∀ s ∈ origSeen.map Fn.sig ++ extSigs, s ∈ seen ++ extSigs := by
      intro s hs
      rcases List.mem_append.mp hs with hs1 | hs2
      · rcases List.mem_map.mp hs1 with ⟨g, hg, rfl⟩
        exact List.mem_append_left _ (hsub g hg)
      · exact List.mem_append_right _ hs2
    have h_ins_ok : LeanQbe.T.Module.checkFnsCallsOk exits extSigs seen
        (patchInsAt befores f) = true := by
      have h0 := hins [] f rest rfl
      simp only [List.append_nil] at h0
      exact checkFnsCallsOk_mono hsub_ext h0
    have h_mid_ok : ((repls.find? (fun x => x.name == f.name)).getD f).checkCallsOk
        ((seen ++ (patchInsAt befores f).map Fn.sig) ++ extSigs) exits = true := by
      cases h : repls.find? (fun x => x.name == f.name) with
      | none =>
        refine fn_checkCallsOk_mono (fun s hs => ?_) hchk.1
        rcases List.mem_append.mp (hsub_ext s hs) with hs1 | hs2
        · exact List.mem_append_left _ (List.mem_append_left _ hs1)
        · exact List.mem_append_right _ hs2
      | some r =>
        have h0 := hrepl [] f rest r rfl (List.mem_of_find?_eq_some h) (fn_find_name_eq h)
        simp only [List.append_nil] at h0
        refine fn_checkCallsOk_mono (fun s hs => ?_) h0
        rcases List.mem_append.mp hs with hs1 | hs2
        · rcases List.mem_append.mp hs1 with hs1a | hs1b
          · rcases List.mem_map.mp hs1a with ⟨g, hg, rfl⟩
            exact List.mem_append_left _ (List.mem_append_left _ (hsub g hg))
          · exact List.mem_append_left _ (List.mem_append_right _ hs1b)
        · exact List.mem_append_right _ hs2
    rw [List.append_assoc, checkFnsCallsOk_append, h_ins_ok, Bool.true_and,
      checkFnsCallsOk_append, LeanQbe.T.Module.checkFnsCallsOk, h_mid_ok]
    simp only [LeanQbe.T.Module.checkFnsCallsOk, Bool.true_and, List.map_singleton,
      List.append_assoc]
    have hsub_next : ∀ g ∈ origSeen ++ [f],
        g.sig ∈ seen ++ ((patchInsAt befores f).map Fn.sig ++
          [((repls.find? (fun x => x.name == f.name)).getD f).sig]) := by
      intro g hg
      rcases List.mem_append.mp hg with hg1 | hg2
      · exact List.mem_append_left _ (hsub g hg1)
      · simp only [List.mem_singleton] at hg2
        subst hg2
        exact List.mem_append_right _ (List.mem_append_right _ (by simp [hhead_sig]))
    have hchk2 :
        LeanQbe.T.Module.checkFnsCallsOk exits extSigs ((origSeen ++ [f]).map Fn.sig) rest =
          true := by
      simpa only [List.map_append, List.map_singleton] using hchk.2
    exact checkFnsCallsOk_patch exits extSigs repls befores (origSeen ++ [f])
      (seen ++ ((patchInsAt befores f).map Fn.sig ++
        [((repls.find? (fun x => x.name == f.name)).getD f).sig]))
      rest hsub_next hchk2 hsig_rest hins_rest hrepl_rest

/-- Fast `O(|repls| + |befores|)` preservation of `Module.checkAcyclic = true` across
`patchFns repls befores M.fns` (both sig-preserving replacements and helper insertions). -/
theorem patchModule_checkAcyclic {M : LeanQbe.T.Module} {repls : List Fn}
    {befores : List (Sym × List Fn)}
    (hnd : ((patchFns repls befores M.fns).map Fn.name ++ M.externs.map Extern.name).Nodup)
    (hM : M.checkAcyclic = true)
    (hsig : ∀ r ∈ repls, ∀ f ∈ M.fns, r.name = f.name → r.sig = f.sig)
    (hins : ∀ pre f post, M.fns = pre ++ f :: post →
      LeanQbe.T.Module.checkFnsCallsOk M.exits (M.externs.map Extern.sig)
        (pre.map Fn.sig) (patchInsAt befores f) = true)
    (hrepl : ∀ pre f post r, M.fns = pre ++ f :: post → r ∈ repls → r.name = f.name →
      r.checkCallsOk
        (pre.map Fn.sig ++ (patchInsAt befores f).map Fn.sig ++ M.externs.map Extern.sig)
        M.exits = true) :
    ({ M with fns := patchFns repls befores M.fns } : LeanQbe.T.Module).checkAcyclic = true := by
  simp only [LeanQbe.T.Module.checkAcyclic, Bool.and_eq_true] at hM ⊢
  refine ⟨listNodup_iff.mpr hnd, ?_⟩
  exact checkFnsCallsOk_patch M.exits (M.externs.map Extern.sig) repls befores [] [] M.fns
    (fun _ h => nomatch h) hM.2 hsig
    (fun pre f post h => hins pre f post h)
    (fun pre f post r h => hrepl pre f post r h)

theorem idx_eq_of_name_nodup {xs : List Fn} {f f0 : Fn} {i j : Nat}
    (hnd : (xs.map Fn.name).Nodup)
    (hi : xs[i]? = some f0) (hj : xs[j]? = some f) (heq : f.name = f0.name) : j = i := by
  have hi_lt : i < xs.length := (List.getElem?_eq_some_iff.mp hi).1
  have hj_lt : j < xs.length := (List.getElem?_eq_some_iff.mp hj).1
  have hfi : xs[i] = f0 := (List.getElem?_eq_some_iff.mp hi).2
  have hfj : xs[j] = f := (List.getElem?_eq_some_iff.mp hj).2
  have hpw := List.pairwise_iff_getElem.mp hnd
  rcases Nat.lt_trichotomy j i with hlt | rfl | hgt
  · exact False.elim (hpw j i (by simpa using hj_lt) (by simpa using hi_lt) hlt
      (by simp only [List.getElem_map, hfj, hfi, heq]))
  · rfl
  · exact False.elim (hpw i j (by simpa using hi_lt) (by simpa using hj_lt) hgt
      (by simp only [List.getElem_map, hfi, hfj, heq]))

theorem fn_eq_of_mem_idx {xs : List Fn} {f f0 : Fn} {i : Nat}
    (hnd : (xs.map Fn.name).Nodup) (hf : f ∈ xs) (hi : xs[i]? = some f0)
    (heq : f.name = f0.name) : f = f0 := by
  rcases List.mem_iff_getElem.mp hf with ⟨j, hj, rfl⟩
  have hjeq := idx_eq_of_name_nodup hnd hi (List.getElem?_eq_getElem hj) heq
  subst hjeq
  exact (List.getElem?_eq_some_iff.mp hi).2

theorem sig_mem_pre_of_lt_idx {xs pre post : List Fn} {f f0 g : Fn} {k i : Nat}
    (hnd : (xs.map Fn.name).Nodup) (hsplit : xs = pre ++ f :: post)
    (hi : xs[i]? = some f0) (heq : f.name = f0.name)
    (hk : xs[k]? = some g) (hlt : k < i) : g.sig ∈ pre.map Fn.sig := by
  have hpre_get : xs[pre.length]? = some f := by
    rw [hsplit, List.getElem?_append_right (Nat.le_refl _)]
    simp
  have hlen : pre.length = i := idx_eq_of_name_nodup hnd hi hpre_get heq
  have hk_lt : k < pre.length := hlen ▸ hlt
  have hgx : pre[k]'hk_lt = g := by
    have h1 : xs[k]? = pre[k]? := by
      rw [hsplit, List.getElem?_append_left hk_lt]
    exact Option.some.inj ((List.getElem?_eq_getElem hk_lt).symm.trans (h1.symm.trans hk))
  exact List.mem_map.mpr ⟨g, hgx ▸ List.getElem_mem hk_lt, rfl⟩

/-! ## 3. Compositional `ModuleOk`, Soundness & UNSAT NV Inheritance -/

/-- Lift `ModuleOk Γ M` across any same-env `spliceFns repls M.fns` replacement once `repls`
satisfy their specs under `Γ` and `checkAcyclic` holds. -/
theorem spliceModule_moduleOk_sameEnv {Γ : Env} {M : LeanQbe.T.Module}
    (hM : ModuleOk Γ M) {repls : List Fn}
    (hchk : ({ M with fns := spliceFns repls M.fns } : LeanQbe.T.Module).checkAcyclic = true)
    (hrWf : ∀ r ∈ repls, r.Wf)
    (hrWp : ∀ r ∈ repls, ∀ xs m Q X,
      Γ r.name r.as r.rs xs m Q X → Func.wp Γ r.body xs m Q X) :
    ModuleOk Γ { M with fns := spliceFns repls M.fns } := by
  have hwfOrig : ∀ f ∈ M.fns, f.Wf := fun f hf => by
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hf
    exact (hM.fnsOk pre f post hsplit).1
  refine LeanQbe.T.Module.moduleOk_of_checkAcyclic hchk (spliceFns_wf hwfOrig hrWf) ?_
  intro fn hmem
  rcases List.mem_map.mp hmem with ⟨g, hg, rfl⟩
  cases h : repls.find? (fun x => x.name == g.name) with
  | none =>
    intro xs m Q X hspec
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
    exact (hM.fnsOk pre g post hsplit).2.2 xs m Q X hspec
  | some r =>
    intro xs m Q X hspec
    exact hrWp r (List.mem_of_find?_eq_some h) xs m Q X hspec

/-- Lift `ModuleOk Γ M` across simultaneous `spliceFns repls M.fns` and `Γ'` environment upgrade
when `Γ'` preserves untouched rows (`Γ' ≤ Γ` on untouched entries) and refines `Γ` on callees
(`Γ ≤ Γ'`), discharging only modified functions/re-spec'd entries via `hFnWp` and `hrWp`. -/
theorem spliceModule_moduleOk {Γ Γ' : Env} {M : LeanQbe.T.Module}
    (hM : ModuleOk Γ M) {repls : List Fn}
    (hchk : ({ M with fns := spliceFns repls M.fns } : LeanQbe.T.Module).checkAcyclic = true)
    (hrWf : ∀ r ∈ repls, r.Wf)
    (hCallee : ∀ f as bs xs m Q X, Γ f as bs xs m Q X → Γ' f as bs xs m Q X)
    (hFnWp : ∀ g ∈ M.fns, repls.find? (fun x => x.name == g.name) = none →
      (∀ xs m Q X, Γ' g.name g.as g.rs xs m Q X → Func.wp Γ' g.body xs m Q X) ∨
      (∀ xs m Q X, Γ' g.name g.as g.rs xs m Q X → Γ g.name g.as g.rs xs m Q X))
    (hrWp : ∀ r ∈ repls, ∀ xs m Q X,
      Γ' r.name r.as r.rs xs m Q X → Func.wp Γ' r.body xs m Q X) :
    ModuleOk Γ' { M with fns := spliceFns repls M.fns } := by
  have hwfOrig : ∀ f ∈ M.fns, f.Wf := fun f hf => by
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hf
    exact (hM.fnsOk pre f post hsplit).1
  refine LeanQbe.T.Module.moduleOk_of_checkAcyclic hchk (spliceFns_wf hwfOrig hrWf) ?_
  intro fn hmem
  rcases List.mem_map.mp hmem with ⟨g, hg, rfl⟩
  cases h : repls.find? (fun x => x.name == g.name) with
  | some r =>
    intro xs m Q X hspec
    exact hrWp r (List.mem_of_find?_eq_some h) xs m Q X hspec
  | none =>
    intro xs m Q X hspec
    rcases hFnWp g hg h with hNew | hPull
    · exact hNew xs m Q X hspec
    · obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
      have ⟨hwfG, hcallsG, hwpG⟩ := hM.fnsOk pre g post hsplit
      exact wp_env_agree_of_callsOk
        (hwfG Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units g.as))
        hcallsG (fun f as bs _ => hCallee f as bs) m
        (hwpG xs m Q X (hPull xs m Q X hspec))

/-- Same-env `ModuleOk` lift across `patchFns repls befores M.fns`. -/
theorem patchModule_moduleOk_sameEnv {Γ : Env} {M : LeanQbe.T.Module}
    (hM : ModuleOk Γ M) {repls : List Fn} {befores : List (Sym × List Fn)}
    (hchk : ({ M with fns := patchFns repls befores M.fns } :
      LeanQbe.T.Module).checkAcyclic = true)
    (hrWf : ∀ r ∈ repls, r.Wf)
    (hiWf : ∀ p ∈ befores, ∀ h ∈ p.2, h.Wf)
    (hrWp : ∀ r ∈ repls, ∀ xs m Q X,
      Γ r.name r.as r.rs xs m Q X → Func.wp Γ r.body xs m Q X)
    (hiWp : ∀ p ∈ befores, ∀ h ∈ p.2, ∀ xs m Q X,
      Γ h.name h.as h.rs xs m Q X → Func.wp Γ h.body xs m Q X) :
    ModuleOk Γ { M with fns := patchFns repls befores M.fns } := by
  have hwfOrig : ∀ f ∈ M.fns, f.Wf := fun f hf => by
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hf
    exact (hM.fnsOk pre f post hsplit).1
  refine LeanQbe.T.Module.moduleOk_of_checkAcyclic hchk
    (patchFns_wf hwfOrig hrWf hiWf) ?_
  intro fn hmem
  rcases List.mem_flatMap.mp hmem with ⟨g, hg, hmem_g⟩
  rcases List.mem_append.mp hmem_g with h_ins | h_rep
  · rcases mem_patchInsAt h_ins with ⟨hs, hm, hfn_hs⟩
    exact hiWp (g.name, hs) hm fn hfn_hs
  · rcases List.mem_singleton.mp h_rep with rfl
    cases h : repls.find? (fun x => x.name == g.name) with
    | none =>
      intro xs m Q X hspec
      obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
      exact (hM.fnsOk pre g post hsplit).2.2 xs m Q X hspec
    | some r =>
      intro xs m Q X hspec
      exact hrWp r (List.mem_of_find?_eq_some h) xs m Q X hspec

/-- Lift `ModuleOk Γ M` across simultaneous `patchFns repls befores M.fns` and `Γ'` environment
upgrade when `Γ'` preserves untouched rows and refines `Γ` on callees. -/
theorem patchModule_moduleOk {Γ Γ' : Env} {M : LeanQbe.T.Module}
    (hM : ModuleOk Γ M) {repls : List Fn} {befores : List (Sym × List Fn)}
    (hchk : ({ M with fns := patchFns repls befores M.fns } :
      LeanQbe.T.Module).checkAcyclic = true)
    (hrWf : ∀ r ∈ repls, r.Wf)
    (hiWf : ∀ p ∈ befores, ∀ h ∈ p.2, h.Wf)
    (hCallee : ∀ f as bs xs m Q X, Γ f as bs xs m Q X → Γ' f as bs xs m Q X)
    (hFnWp : ∀ g ∈ M.fns, repls.find? (fun x => x.name == g.name) = none →
      (∀ xs m Q X, Γ' g.name g.as g.rs xs m Q X → Func.wp Γ' g.body xs m Q X) ∨
      (∀ xs m Q X, Γ' g.name g.as g.rs xs m Q X → Γ g.name g.as g.rs xs m Q X))
    (hrWp : ∀ r ∈ repls, ∀ xs m Q X,
      Γ' r.name r.as r.rs xs m Q X → Func.wp Γ' r.body xs m Q X)
    (hiWp : ∀ p ∈ befores, ∀ h ∈ p.2, ∀ xs m Q X,
      Γ' h.name h.as h.rs xs m Q X → Func.wp Γ' h.body xs m Q X) :
    ModuleOk Γ' { M with fns := patchFns repls befores M.fns } := by
  have hwfOrig : ∀ f ∈ M.fns, f.Wf := fun f hf => by
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hf
    exact (hM.fnsOk pre f post hsplit).1
  refine LeanQbe.T.Module.moduleOk_of_checkAcyclic hchk
    (patchFns_wf hwfOrig hrWf hiWf) ?_
  intro fn hmem
  rcases List.mem_flatMap.mp hmem with ⟨g, hg, hmem_g⟩
  rcases List.mem_append.mp hmem_g with h_ins | h_rep
  · rcases mem_patchInsAt h_ins with ⟨hs, hm, hfn_hs⟩
    exact hiWp (g.name, hs) hm fn hfn_hs
  · rcases List.mem_singleton.mp h_rep with rfl
    cases h : repls.find? (fun x => x.name == g.name) with
    | some r =>
      intro xs m Q X hspec
      exact hrWp r (List.mem_of_find?_eq_some h) xs m Q X hspec
    | none =>
      intro xs m Q X hspec
      rcases hFnWp g hg h with hNew | hPull
      · exact hNew xs m Q X hspec
      · obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
        have ⟨hwfG, hcallsG, hwpG⟩ := hM.fnsOk pre g post hsplit
        exact wp_env_agree_of_callsOk
          (hwfG Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units g.as))
          hcallsG (fun f as bs _ => hCallee f as bs) m
          (hwpG xs m Q X (hPull xs m Q X hspec))

/-- Lift any spliced `ModuleOk` directly to `kissat_solve_bytes` soundness. -/
theorem spliceModule_solve_bytes_sound
    {Γ : Env} {M : LeanQbe.T.Module}
    (hM : ModuleOk Γ M)
    (hMem : FullM6Orch.m6oSolveBytesFn ∈ M.fns)
    (hRow : ∀ a m Q X, fullM6SolveBytesSpec a m Q X →
      Γ "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp Γ FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
            ∀ (F : Mem 64 → Prop) (M' : Mem 64),
              (Eq m' ⋆ F) M' → cnf.Sat (readModelFromWorkM6 M' work_ptr)) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fullM6_solve_bytes_moduleOk_combinator Γ M "kissat_solve_bytes"
    FullM6Orch.kissat_solve_bytes_body hM hMem hRow hcfit hwfit hm

/-- Lift any spliced `ModuleOk` (`fullM6SolveBytesCoreModelSpec`) to deterministic concrete
UNSAT non-vacuity (`XPost := False`, `r = 20#64`). -/
theorem spliceModule_unsat_nv
    {Γ : Env} {M : LeanQbe.T.Module}
    (hM : ModuleOk Γ M)
    (hMem : FullM6Orch.m6oSolveBytesFn ∈ M.fns)
    (hRow : ∀ a m Q X, fullM6SolveBytesCoreModelSpec a m Q X →
      Γ "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    Func.wp Γ FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hMem
  have hfn := (hM.fnsOk pre _ post hsplit).2.2
  refine fullM6_unsat_nv Γ FullM6Orch.kissat_solve_bytes_body ?_
  intro a m0 Q X hs
  exact hfn a m0 Q X (hRow a m0 Q X hs)

/-! ## 4. Shared Wave-4 Splice Instance: `FullM7BvaGuFix` (`168550f4`) -/

/-- `2`-function Wave-4 BVA/glue_used replacement list (`m7BvaCommitFn`, `m7AnalyzeRsnFn`). -/
def m7BvaGuRepls : List Fn :=
  [m7BvaCommitFn, m7AnalyzeRsnFn]

/-- `410`-function unified `M7` list with `168550f4` (`m7BvaCommitFn`, `m7AnalyzeRsnFn`) spliced
in via `spliceFns`. -/
def m7BvaGuFns : List Fn :=
  spliceFns m7BvaGuRepls m7Fns

/-- Closed `410`-function `M7 + BvaGuFix` module (`externs := []`, `exits := []`). -/
def m7BvaGuModule : LeanQbe.T.Module :=
  { fns := m7BvaGuFns, externs := [], exits := [] }

theorem m7_names_nodup : (m7Fns.map Fn.name).Nodup := by
  have hchk := m7_acyclic
  simp only [LeanQbe.T.Module.checkAcyclic, Bool.and_eq_true] at hchk
  have hnd : (m7Module.names).Nodup := LeanQbe.T.Module.namesNodup_of_checkNamesNodup hchk.1
  change (m7Fns.map Fn.name ++ ([] : List Extern).map Extern.name).Nodup at hnd
  simpa only [List.map_nil, List.append_nil] using hnd

theorem m7_p1_len : m7FnsPart1.length = 112 := by t_kernel_rfl
theorem m7_p2_len : m7FnsPart2.length = 164 := by t_kernel_rfl

theorem m7_get_p1 {k : Nat} (hk : k < 112) : m7Fns[k]? = m7FnsPart1[k]? := by
  unfold m7Fns
  rw [List.append_assoc, List.getElem?_append_left (by rw [m7_p1_len]; exact hk)]

theorem m7_get_p2 {k : Nat} (hk : k < 164) : m7Fns[112 + k]? = m7FnsPart2[k]? := by
  unfold m7Fns
  rw [List.append_assoc, List.getElem?_append_right (by rw [m7_p1_len]; omega), m7_p1_len,
    Nat.add_sub_cancel_left, List.getElem?_append_left (by rw [m7_p2_len]; exact hk)]

theorem m7_get_p3 {k : Nat} : m7Fns[276 + k]? = m7FnsPart3[k]? := by
  unfold m7Fns
  rw [List.append_assoc, List.getElem?_append_right (by rw [m7_p1_len]; omega), m7_p1_len,
    show 276 + k - 112 = 164 + k by omega,
    List.getElem?_append_right (by rw [m7_p2_len]; omega), m7_p2_len, Nat.add_sub_cancel_left]

private theorem m7_p1_12 : m7FnsPart1[12]?.map Fn.sig =
    some ("full_alloc_cl", [i64, i32, i32, .bool], [i64]) := by t_kernel_rfl
private theorem m7_p1_17 : m7FnsPart1[17]?.map Fn.sig =
    some ("full_wstack_defrag", [i64], []) := by t_kernel_rfl
private theorem m7_p1_18 : m7FnsPart1[18]?.map Fn.sig =
    some ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]) := by t_kernel_rfl
private theorem m7_p1_80 : m7FnsPart1[80]?.map Fn.sig =
    some ("full_unwatch_large", [i64, i32, i32], []) := by t_kernel_rfl
private theorem m7_p2_0 : m7FnsPart2[0]?.map Fn.sig =
    some ("full_analyze_lit", [i64, i32, i32], [.bool]) := by t_kernel_rfl
private theorem m7_p2_1 : m7FnsPart2[1]?.map Fn.sig =
    some ("full_analyze_rsn", [i64, i32, i32], [.bool]) := by t_kernel_rfl
private theorem m7_p2_66 : m7FnsPart2[66]?.map Fn.sig =
    some ("full_add_bin", [i64, i32, i32], [i64]) := by t_kernel_rfl
private theorem m7_p2_67 : m7FnsPart2[67]?.map Fn.sig =
    some ("full_delete_binary", [i64, i32, i32], []) := by t_kernel_rfl
private theorem m7_p3_64 : m7FnsPart3[64]?.map Fn.sig =
    some ("full_init_fresh_var", [i64, i32], []) := by t_kernel_rfl
private theorem m7_p3_72 : m7FnsPart3[72]?.map Fn.sig =
    some ("full_bva_commit", [i64, i32], [.bool]) := by t_kernel_rfl

private theorem m7_idx_12 : m7Fns[12]?.map Fn.sig =
    some ("full_alloc_cl", [i64, i32, i32, .bool], [i64]) := by
  rw [m7_get_p1 (by decide)]; exact m7_p1_12
private theorem m7_idx_17 : m7Fns[17]?.map Fn.sig =
    some ("full_wstack_defrag", [i64], []) := by
  rw [m7_get_p1 (by decide)]; exact m7_p1_17
private theorem m7_idx_18 : m7Fns[18]?.map Fn.sig =
    some ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]) := by
  rw [m7_get_p1 (by decide)]; exact m7_p1_18
private theorem m7_idx_80 : m7Fns[80]?.map Fn.sig =
    some ("full_unwatch_large", [i64, i32, i32], []) := by
  rw [m7_get_p1 (by decide)]; exact m7_p1_80
private theorem m7_idx_112 : m7Fns[112]?.map Fn.sig =
    some ("full_analyze_lit", [i64, i32, i32], [.bool]) := by
  rw [show (112 : Nat) = 112 + 0 by rfl, m7_get_p2 (by decide)]; exact m7_p2_0
private theorem m7_idx_113 : m7Fns[113]?.map Fn.sig =
    some ("full_analyze_rsn", [i64, i32, i32], [.bool]) := by
  rw [show (113 : Nat) = 112 + 1 by rfl, m7_get_p2 (by decide)]; exact m7_p2_1
private theorem m7_idx_178 : m7Fns[178]?.map Fn.sig =
    some ("full_add_bin", [i64, i32, i32], [i64]) := by
  rw [show (178 : Nat) = 112 + 66 by rfl, m7_get_p2 (by decide)]; exact m7_p2_66
private theorem m7_idx_179 : m7Fns[179]?.map Fn.sig =
    some ("full_delete_binary", [i64, i32, i32], []) := by
  rw [show (179 : Nat) = 112 + 67 by rfl, m7_get_p2 (by decide)]; exact m7_p2_67
private theorem m7_idx_340 : m7Fns[340]?.map Fn.sig =
    some ("full_init_fresh_var", [i64, i32], []) := by
  rw [show (340 : Nat) = 276 + 64 by rfl, m7_get_p3]; exact m7_p3_64
private theorem m7_idx_348 : m7Fns[348]?.map Fn.sig =
    some ("full_bva_commit", [i64, i32], [.bool]) := by
  rw [show (348 : Nat) = 276 + 72 by rfl, m7_get_p3]; exact m7_p3_72

theorem sig_of_map_idx {i : Nat} {s : SigEntry}
    (h : m7Fns[i]?.map Fn.sig = some s) :
    ∃ g, m7Fns[i]? = some g ∧ g.sig = s := by
  cases hg : m7Fns[i]? with
  | none => simp [hg] at h
  | some g => exact ⟨g, rfl, by simpa [hg] using h⟩

theorem m7BvaGu_acyclic : m7BvaGuModule.checkAcyclic = true := by
  obtain ⟨f348, hf348, hs348⟩ := sig_of_map_idx m7_idx_348
  obtain ⟨f113, hf113, hs113⟩ := sig_of_map_idx m7_idx_113
  obtain ⟨g12, hg12, hsg12⟩ := sig_of_map_idx m7_idx_12
  obtain ⟨g17, hg17, hsg17⟩ := sig_of_map_idx m7_idx_17
  obtain ⟨g18, hg18, hsg18⟩ := sig_of_map_idx m7_idx_18
  obtain ⟨g80, hg80, hsg80⟩ := sig_of_map_idx m7_idx_80
  obtain ⟨g112, hg112, hsg112⟩ := sig_of_map_idx m7_idx_112
  obtain ⟨g178, hg178, hsg178⟩ := sig_of_map_idx m7_idx_178
  obtain ⟨g179, hg179, hsg179⟩ := sig_of_map_idx m7_idx_179
  obtain ⟨g340, hg340, hsg340⟩ := sig_of_map_idx m7_idx_340
  refine spliceModule_checkAcyclic (M := m7Module) m7_acyclic ?_ ?_
  · intro r hr f hf hnm
    rcases List.mem_cons.mp hr with rfl | hr
    · have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf348
        (hnm.symm.trans (congrArg Prod.fst hs348.symm))
      subst hf0; exact hs348.symm
    · rcases List.mem_singleton.mp hr with rfl
      have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf113
        (hnm.symm.trans (congrArg Prod.fst hs113.symm))
      subst hf0; exact hs113.symm
  · intro pre f post r hsplit hr hnm
    simp only [m7Module, List.map_nil, List.append_nil] at hsplit ⊢
    rcases List.mem_cons.mp hr with rfl | hr
    · have hn0 : f.name = f348.name := hnm.symm.trans (congrArg Prod.fst hs348.symm)
      have hc : m7BvaCommitFn.checkCallsOk
          [ ("full_alloc_cl", [i64, i32, i32, .bool], [i64])
          , ("full_wstack_defrag", [i64], [])
          , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool])
          , ("full_unwatch_large", [i64, i32, i32], [])
          , ("full_add_bin", [i64, i32, i32], [i64])
          , ("full_delete_binary", [i64, i32, i32], [])
          , ("full_init_fresh_var", [i64, i32], []) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsg12 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf348 hn0 hg12 (by decide)
      · exact hsg17 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf348 hn0 hg17 (by decide)
      · exact hsg18 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf348 hn0 hg18 (by decide)
      · exact hsg80 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf348 hn0 hg80 (by decide)
      · exact hsg178 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf348 hn0 hg178 (by decide)
      · exact hsg179 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf348 hn0 hg179 (by decide)
      · exact hsg340 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf348 hn0 hg340 (by decide)
    · rcases List.mem_singleton.mp hr with rfl
      have hn0 : f.name = f113.name := hnm.symm.trans (congrArg Prod.fst hs113.symm)
      have hc : m7AnalyzeRsnFn.checkCallsOk
          [("full_analyze_lit", [i64, i32, i32], [.bool])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact hsg112 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf113 hn0 hg112 (by decide)

/-- `ModuleOk` for `m7BvaGuModule` (`410` fns with `168550f4` spliced in), inheriting all `408`
untouched functions directly from `mkM7Env_moduleOk`. -/
theorem m7BvaGu_moduleOk
    (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hWeaken : ∀ a m Q X, solveSpec a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hSolveMonoX : ∀ a m Q X X', solveSpec a m Q X → solveSpec a m Q X')
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve solveSpec) m7BveAllFns tBve) :
    ModuleOk (mkM7Env tBve solveSpec) m7BvaGuModule := by
  have hm := mkM7Env_moduleOk tBve solveSpec hWeaken hSolveMonoX
    hBveSigs hBveNoExit hBveSpecs hBveOk
  have hnd := m7SpecTable_nodup tBve solveSpec hBveSigs
  have hc1 := m7Part1Callees_of_sub (m7SpecTable_part1_mem (tBve := tBve) (solveSpec := solveSpec))
  have hc2 := m7Part2Callees_of_sub (m7SpecTable_part2_mem (tBve := tBve) (solveSpec := solveSpec))
  have hr2 := m7Part2BvaGuRows_of_sub (m7SpecTable_part2_mem (tBve := tBve)
    (solveSpec := solveSpec))
  have hr3 := m7Part3BvaGuRows_of_sub (m7SpecTable_part3Pfx_mem (tBve := tBve)
    (solveSpec := solveSpec))
  refine spliceModule_moduleOk_sameEnv hm m7BvaGu_acyclic ?_ ?_
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact full_bva_commit_m7_wf
    · rcases List.mem_singleton.mp hr with rfl
      exact full_analyze_rsn_m7_wf
  · intro r hr xs m Q X hs
    rcases List.mem_cons.mp hr with rfl | hr
    · have hspec := mkM7Env_elim_of_mem hr3.2 hnd hs
      exact full_bva_commit_m7_wp (mkM7Env tBve solveSpec)
        (mkM7Env_row_mem hnd _ _ _ _ (m7SpecTable_pfx_mem _ m7OrchPfxRows_specs.wstackDefrag))
        (mkM7Env_row_mem hnd _ _ _ _ hr3.1) (mkM7Env_row_mem hnd _ _ _ _ hc2.addBin)
        (mkM7Env_row_mem hnd _ _ _ _ hc1.allocCl)
        (mkM7Env_row_mem hnd _ _ _ _ (m7SpecTable_pfx_mem _ m7OrchPfxRows_specs.watchPush))
        (mkM7Env_row_mem hnd _ _ _ _ hc2.deleteBinary)
        (mkM7Env_row_mem hnd _ _ _ _ hc1.unwatchLarge)
        xs m Q X hspec
    · rcases List.mem_singleton.mp hr with rfl
      have hspec := mkM7Env_elim_of_mem hr2.2 hnd hs
      exact full_analyze_rsn_m7_wp (mkM7Env tBve solveSpec)
        (mkM7Env_row_mem hnd _ _ _ _ hr2.1) xs m Q X hspec

theorem m7BvaGu_solveBytes_mem : FullM6Orch.m6oSolveBytesFn ∈ m7BvaGuModule.fns :=
  spliceFns_mem_of_ne m7oSolveBytesFn_mem fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · decide
    · rcases List.mem_singleton.mp hr with rfl; decide

/-- Top-level `kissat_solve_bytes` soundness for `m7BvaGuModule` (`168550f4` spliced in). -/
theorem m7BvaGu_solve_bytes_sound
    (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesSpec) m7BveAllFns tBve)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp (mkM7Env tBve fullM6SolveBytesSpec) FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
            ∀ (F : Mem 64 → Prop) (M' : Mem 64),
              (Eq m' ⋆ F) M' → cnf.Sat (readModelFromWorkM6 M' work_ptr)) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  spliceModule_solve_bytes_sound
    (m7BvaGu_moduleOk tBve fullM6SolveBytesSpec
      (fun _ _ _ _ h => fullM6SolveBytesCoreModelSpec_of_spec h)
      (fun _ _ _ _ _ h => fullM6SolveBytesSpec_monoX h)
      hBveSigs hBveNoExit hBveSpecs hBveOk)
    m7BvaGu_solveBytes_mem
    (fun _ _ _ _ hs =>
      (mkM7Env_solve_bytes_iff tBve fullM6SolveBytesSpec hBveSigs).mpr
        (fullM6SolveBytesSpec_monoX hs))
    hcfit hwfit hm

/-- Concrete deterministic UNSAT non-vacuity (`XPost := False`, `r = 20#64`) for `m7BvaGuModule`.
-/
theorem m7BvaGu_unsat_nv
    (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesCoreModelSpec) m7BveAllFns tBve) :
    Func.wp (mkM7Env tBve fullM6SolveBytesCoreModelSpec) FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  spliceModule_unsat_nv
    (m7BvaGu_moduleOk tBve fullM6SolveBytesCoreModelSpec
      (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => fullM6SolveBytesCoreModelSpec_monoX h)
      hBveSigs hBveNoExit hBveSpecs hBveOk)
    m7BvaGu_solveBytes_mem
    (fun _ _ _ _ hs =>
      (mkM7Env_solve_bytes_iff tBve fullM6SolveBytesCoreModelSpec hBveSigs).mpr
        (fullM6SolveBytesCoreModelSpec_monoX hs))

end LeanQbe.T.Examples.Kissat.FullM7Splice
