/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8CoreParity
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofProbe
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofMin
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofAnalyze
public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve1
import LeanQbe.T.Examples.Kissat.FullM7AnalyzeSortProof0
import LeanQbe.T.Examples.Kissat.PatchModule
import LeanQbe.T.Examples.Kissat.FullM7Splice
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
import all LeanQbe.T.Examples.Kissat.FullM7Transport1
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
import LeanQbe.T.Examples.Kissat.FullM6Orch
import LeanQbe.T.Examples.Kissat.FullM5HeurCore
import LeanQbe.T.Examples.Kissat.FullM6MinShrink
import LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
import LeanQbe.T.Examples.Kissat.FullM7BveGates
import LeanQbe.T.Examples.Kissat.FullM7FidelityCore
import LeanQbe.T.Examples.Kissat.FullM6SatNv
import LeanQbe.T.Examples.Kissat.FullFastBveBudgets
import LeanQbe.T.Examples.Kissat.FullM3CongBva
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M8 Core Parity Assembly Proofs (`FullM8CoreParityProof`)

Packages unconditional `m8CoreParitySpecTable`, `m8CoreParityEnv`, `m8CoreParity_moduleOk`,
`m8CoreParity_tableImpl`, `m8CoreParity_solve_bytes_sound`, `m8CoreParity_solve_bytes_host_sound`,
and `m8CoreParity_unsat_nv` over `FullM8CoreParity.m8CoreParityModule` (`435` fns, `0` externs,
`0` exits).

Closes all Rank #5 (`ProofMin`), Rank #4 (`ProofProbe`), Analyze (`ProofAnalyze`), and Rank #8
BVE (`FullM8CoreParityProofBve{0,1}`) functions and callers cleanly (`public section`, `0`
`@[expose]`, `0` `*Lemmas*` in `public import`, UNSAT-only with `0` SAT model proofs).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8CoreParity

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Splice
open LeanQbe.T.Examples.Kissat.FullM7Fidelity

/-! ## 1. `PatchModule` Algebraic & Spec-Table Helpers -/

private abbrev rowSig (e : SpecEntry) : SigEntry := (e.name, e.as, e.rs)

theorem m8cp_sym_ne_beq {a b : Sym} (h : a ≠ b) : (a == b) = false :=
  Bool.eq_false_iff.mpr (fun hb => h (beq_iff_eq.mp hb))

private theorem m8cp_patchInsAt_eq (f : Fn) :
    PatchModule.patchInsAt m8CoreParityBefores f = mfPatchInsAt m8CoreParityBefores f := by
  dsimp only [PatchModule.patchInsAt, mfPatchInsAt, m8CoreParityBefores]
  by_cases h1 : ("full_min_shrink_m6" == f.name) <;>
    by_cases h2 : ("full_bve_var_m7" == f.name)
  · exact absurd ((beq_iff_eq.mp h1).trans (beq_iff_eq.mp h2).symm) (by decide)
  · have h1e := beq_iff_eq.mp h1; rw [← h1e]; simp
  · have h2e := beq_iff_eq.mp h2; rw [← h2e]; simp
  · have h1n : "full_min_shrink_m6" ≠ f.name := fun h => h1 (beq_iff_eq.mpr h)
    have h2n : "full_bve_var_m7" ≠ f.name := fun h => h2 (beq_iff_eq.mpr h)
    simp [m8cp_sym_ne_beq h1n, m8cp_sym_ne_beq h2n, h1n, h2n]

private theorem m8CoreParityFns_eq_patchFns :
    m8CoreParityFns =
      PatchModule.patchFns m8CoreParityRepls m8CoreParityBefores m7FidelityFns := by
  unfold m8CoreParityFns mfPatchFns PatchModule.patchFns
  induction m7FidelityFns with
  | nil => rfl
  | cons a t ih => simp only [List.flatMap_cons, m8cp_patchInsAt_eq a, ih]

private theorem m7Fid_patchInsAt_eq (f : Fn) :
    PatchModule.patchInsAt m7FidBefores f = mfPatchInsAt m7FidBefores f := by
  dsimp only [PatchModule.patchInsAt, mfPatchInsAt, m7FidBefores,
    FullM7FidelityCore.fidCorePatchBefores, FullM7FidelitySearch.fidSearchPatchBefores]
  by_cases h1 : ("full_bva_filter_row" == f.name) <;>
    by_cases h2 : ("full_reorder_queue_m7" == f.name) <;>
    by_cases h3 : ("full_search_m6" == f.name)
  · exact absurd ((beq_iff_eq.mp h1).trans (beq_iff_eq.mp h2).symm) (by decide)
  · exact absurd ((beq_iff_eq.mp h1).trans (beq_iff_eq.mp h2).symm) (by decide)
  · exact absurd ((beq_iff_eq.mp h1).trans (beq_iff_eq.mp h3).symm) (by decide)
  · have h1e := beq_iff_eq.mp h1; rw [← h1e]; simp
  · exact absurd ((beq_iff_eq.mp h2).trans (beq_iff_eq.mp h3).symm) (by decide)
  · have h2e := beq_iff_eq.mp h2; rw [← h2e]; simp
  · have h3e := beq_iff_eq.mp h3; rw [← h3e]; simp
  · have h1n : "full_bva_filter_row" ≠ f.name := fun h => h1 (beq_iff_eq.mpr h)
    have h2n : "full_reorder_queue_m7" ≠ f.name := fun h => h2 (beq_iff_eq.mpr h)
    have h3n : "full_search_m6" ≠ f.name := fun h => h3 (beq_iff_eq.mpr h)
    simp [m8cp_sym_ne_beq h1n, m8cp_sym_ne_beq h2n, m8cp_sym_ne_beq h3n, h1n, h2n, h3n]

private theorem m7FidelityFns_eq_patchFns :
    m7FidelityFns = PatchModule.patchFns m7FidRepls m7FidBefores FullM7.m7Fns := by
  unfold m7FidelityFns mfPatchFns PatchModule.patchFns
  induction FullM7.m7Fns with
  | nil => rfl
  | cons a t ih => simp only [List.flatMap_cons, m7Fid_patchInsAt_eq a, ih]

private theorem patchRows_sigs_eq_patchFns {rs : List SpecEntry} {fs : List Fn}
    {rRows : List SpecEntry} {bRows : List (Sym × List SpecEntry)}
    {rFns : List Fn} {bFns : List (Sym × List Fn)}
    (hSigs : rs.map rowSig = fs.map Fn.sig)
    (hBef : ∀ e f, e.name = f.name →
      (PatchModule.patchRowInsAt bRows e).map rowSig =
        (PatchModule.patchInsAt bFns f).map Fn.sig)
    (hRepl : ∀ e ∈ rs, ∀ f ∈ fs, rowSig e = f.sig →
      rowSig ((rRows.find? (·.name == e.name)).getD e) =
        ((rFns.find? (·.name == f.name)).getD f).sig) :
    (PatchModule.patchRows rRows bRows rs).map rowSig =
      (PatchModule.patchFns rFns bFns fs).map Fn.sig := by
  induction rs generalizing fs with
  | nil =>
    cases fs with
    | nil => rfl
    | cons => simp at hSigs
  | cons e es ih =>
    cases fs with
    | nil => simp at hSigs
    | cons f fs =>
      simp only [List.map_cons, List.cons.injEq] at hSigs
      have hnm : e.name = f.name := congrArg Prod.fst hSigs.1
      simp only [PatchModule.patchRows, PatchModule.patchFns, List.flatMap_cons,
        List.map_append, List.map_cons, List.map_nil]
      rw [hBef e f hnm, hRepl e List.mem_cons_self f List.mem_cons_self hSigs.1]
      congr 1
      exact ih hSigs.2 (fun e' he' f' hf' =>
        hRepl e' (List.mem_cons_of_mem _ he') f' (List.mem_cons_of_mem _ hf'))

private theorem patchRows_sigs_eq_patchFns_self {rs : List SpecEntry} {fs : List Fn}
    {rRows : List SpecEntry} {bRows : List (Sym × List SpecEntry)}
    {rFns : List Fn} {bFns : List (Sym × List Fn)}
    (hSigs : rs.map rowSig = fs.map Fn.sig)
    (hBef : ∀ e f, e.name = f.name →
      (PatchModule.patchRowInsAt bRows e).map rowSig =
        (PatchModule.patchInsAt bFns f).map Fn.sig)
    (hReplR : ∀ r ∈ rRows, ∀ e ∈ rs, r.name = e.name → rowSig r = rowSig e)
    (hReplF : ∀ r ∈ rFns, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig) :
    (PatchModule.patchRows rRows bRows rs).map rowSig =
      (PatchModule.patchFns rFns bFns fs).map Fn.sig := by
  refine patchRows_sigs_eq_patchFns hSigs hBef (fun e he f hf hsig => ?_)
  have h1 : rowSig ((rRows.find? (·.name == e.name)).getD e) = rowSig e := by
    cases hfind : rRows.find? (·.name == e.name) with
    | none => rfl
    | some r =>
      have hnm := beq_iff_eq.mp (List.find?_some (p := fun x : SpecEntry => x.name == e.name) hfind)
      exact hReplR r (List.mem_of_find?_eq_some hfind) e he hnm
  have h2 : ((rFns.find? (·.name == f.name)).getD f).sig = f.sig := by
    cases hfind : rFns.find? (·.name == f.name) with
    | none => rfl
    | some r =>
      have hnm := beq_iff_eq.mp (List.find?_some (p := fun x : Fn => x.name == f.name) hfind)
      exact hReplF r (List.mem_of_find?_eq_some hfind) f hf hnm
  rw [h1, h2, hsig]

private theorem m8cp_nodup_name_eq {α : Type _} (name : α → Sym) {xs : List α}
    (hnd : (xs.map name).Nodup) {x y : α} (hx : x ∈ xs) (hy : y ∈ xs)
    (hnm : name x = name y) : x = y := by
  induction xs with
  | nil => cases hx
  | cons a t ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.mem_cons] at hx hy
    rcases hx with hxa | hx <;> rcases hy with hya | hy
    · exact hxa.trans hya.symm
    · rw [hxa] at hnm
      exact absurd (hnm ▸ List.mem_map.mpr ⟨y, hy, rfl⟩) hnd.1
    · rw [hya] at hnm
      exact absurd (hnm.symm ▸ List.mem_map.mpr ⟨x, hx, rfl⟩) hnd.1
    · exact ih hnd.2 hx hy

private theorem m8cp_sig_of_map {xs : List Fn} {i : Nat} {s : SigEntry}
    (h : xs[i]?.map Fn.sig = some s) : ∃ g, xs[i]? = some g ∧ g.sig = s := by
  cases hg : xs[i]? with
  | none => simp [hg] at h
  | some g => exact ⟨g, rfl, by simpa [hg] using h⟩

private theorem m8cp_sig_exists_of_map {xs : List Fn} {i : Nat} {s : SigEntry}
    (h : xs[i]?.map Fn.sig = some s) : ∃ g ∈ xs, g.sig = s :=
  let ⟨g, hg, hsg⟩ := m8cp_sig_of_map h
  ⟨g, List.mem_of_getElem? hg, hsg⟩

private theorem patchRows_noExit {rs rRows : List SpecEntry} {bRows : List (Sym × List SpecEntry)}
    (hrs : rs.all SpecEntry.noExit = true) (hr : rRows.all SpecEntry.noExit = true)
    (hb : ∀ p ∈ bRows, p.2.all SpecEntry.noExit = true) :
    (PatchModule.patchRows rRows bRows rs).all SpecEntry.noExit = true := by
  rw [List.all_eq_true]
  intro x hx
  simp only [PatchModule.patchRows, List.mem_flatMap, List.mem_append, List.mem_singleton] at hx
  rcases hx with ⟨e, he, hins | rfl⟩
  · unfold PatchModule.patchRowInsAt at hins
    split at hins
    · rename_i tgt ins hfind
      exact List.all_eq_true.mp (hb (tgt, ins) (List.mem_of_find?_eq_some hfind)) x hins
    · nomatch hins
  · cases hfind : rRows.find? (·.name == e.name) with
    | none => simp; exact List.all_eq_true.mp hrs e he
    | some r => simp; exact List.all_eq_true.mp hr r (List.mem_of_find?_eq_some hfind)

private theorem rowSigs_eq_fnSigs_nodup {rs : List SpecEntry} {fs : List Fn}
    (hSigs : rs.map rowSig = fs.map Fn.sig) (hnd : (fs.map Fn.name).Nodup) :
    (rs.map SpecEntry.name).Nodup := by
  have h1 := congrArg (List.map Prod.fst) hSigs
  simp only [List.map_map, Function.comp_def, Fn.sig] at h1
  exact h1 ▸ hnd

private theorem rowSigs_eq_fnSigs_len {rs : List SpecEntry} {fs : List Fn}
    (hSigs : rs.map rowSig = fs.map Fn.sig) : rs.length = fs.length := by
  have h1 := congrArg List.length hSigs
  simpa only [List.length_map] using h1

private theorem env_ofTable_append_elim {p t : List SpecEntry} {f : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable (p ++ t) f as bs xs m Q X) :
    Env.ofTable p f as bs xs m Q X ∨ Env.ofTable t f as bs xs m Q X := by
  induction p with
  | nil => exact Or.inr h
  | cons hd tl ih =>
    rw [List.cons_append] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Or.inl ⟨h1, h2⟩)
    · rcases ih h2 with hp | ht
      · exact Or.inl (Or.inr ⟨h1, hp⟩)
      · exact Or.inr ht

private theorem env_ofTable_mem_elim {p : List SpecEntry} {f : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable p f as bs xs m Q X) :
    ∃ e ∈ p, e.name = f ∧ ∃ (has : e.as = as) (hrs : e.rs = bs), e.cast has hrs xs m Q X := by
  induction p with
  | nil => nomatch h
  | cons hd tl ih =>
    rcases h with ⟨⟨h1, h2, h3⟩, hc⟩ | ⟨_, ht⟩
    · exact ⟨hd, List.mem_cons_self, h1, h2, h3, hc⟩
    · obtain ⟨e, he, hnm, h1, h2, hc⟩ := ih ht
      exact ⟨e, List.mem_cons_of_mem _ he, hnm, h1, h2, hc⟩

private theorem patchRows_mem_of_getD {rRows : List SpecEntry} {e x : SpecEntry}
    (h : (rRows.find? (·.name == e.name)).getD e = x) :
    (rRows.find? (·.name == e.name) = none ∧ x = e) ∨
    (∃ r ∈ rRows, r.name = e.name ∧ x = r) := by
  cases hf : rRows.find? (·.name == e.name) with
  | none => rw [hf] at h; exact Or.inl ⟨rfl, h.symm⟩
  | some r =>
    rw [hf] at h
    have hnm := beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == e.name) hf)
    exact Or.inr ⟨r, List.mem_of_find?_eq_some hf, hnm, h.symm⟩

private theorem patchRows_cast_subst {x y : SpecEntry} (heq : x = y)
    {f : Sym} {as bs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (hnm : x.name = f) (has : x.as = as) (hrs : x.rs = bs) (hcast : x.cast has hrs xs m Q X) :
    ∃ (has' : y.as = as) (hrs' : y.rs = bs), y.name = f ∧ y.cast has' hrs' xs m Q X := by
  subst heq; exact ⟨has, hrs, hnm, hcast⟩

private theorem ofTable_patchRows_elim {rRows : List SpecEntry}
    {bRows : List (Sym × List SpecEntry)} {tbl : List SpecEntry}
    (hReplSigs : ∀ r ∈ rRows, ∀ e ∈ tbl, r.name = e.name → rowSig r = rowSig e)
    (hBefDisj : ∀ p ∈ bRows, ∀ b ∈ p.2, b.name ∉ tbl.map SpecEntry.name)
    {f : Sym} {as bs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable (PatchModule.patchRows rRows bRows tbl) f as bs xs m Q X) :
    (∃ r ∈ rRows, r.name = f ∧ ∃ (has : r.as = as) (hrs : r.rs = bs), r.cast has hrs xs m Q X) ∨
    (∃ p ∈ bRows, ∃ b ∈ p.2, b.name = f ∧
      ∃ (has : b.as = as) (hrs : b.rs = bs), b.cast has hrs xs m Q X) ∨
    (f ∉ rRows.map SpecEntry.name ∧ f ∉ (bRows.flatMap Prod.snd).map SpecEntry.name ∧
      Env.ofTable tbl f as bs xs m Q X) := by
  induction tbl with
  | nil => simp [PatchModule.patchRows, Env.ofTable] at h
  | cons hd tl ih =>
    have hReplSigs' : ∀ r ∈ rRows, ∀ e ∈ tl, r.name = e.name → rowSig r = rowSig e :=
      fun r hr e he => hReplSigs r hr e (List.mem_cons_of_mem _ he)
    have hBefDisj' : ∀ p ∈ bRows, ∀ b ∈ p.2, b.name ∉ tl.map SpecEntry.name :=
      fun p hp b hb hmem => hBefDisj p hp b hb (by simp [hmem])
    simp only [PatchModule.patchRows, List.flatMap_cons, List.append_assoc] at h
    rcases env_ofTable_append_elim h with hBef | htl
    · unfold PatchModule.patchRowInsAt at hBef
      split at hBef
      · rename_i tgt ins hfind
        obtain ⟨b, hb_mem, hb_nm, has, hrs, hc⟩ := env_ofTable_mem_elim hBef
        exact Or.inr (Or.inl ⟨(tgt, ins), List.mem_of_find?_eq_some hfind, b, hb_mem, hb_nm,
          has, hrs, hc⟩)
      · cases hBef
    · simp only [List.cons_append, List.nil_append] at htl
      rcases htl with ⟨⟨hnm, has, hrs⟩, hcast⟩ | ⟨hne, htl_rest⟩
      · rcases patchRows_mem_of_getD (rRows := rRows) (e := hd) rfl with ⟨hnone, heq⟩ |
          ⟨r, hr, _, heq⟩
        · obtain ⟨has', hrs', hnm', hcast'⟩ := patchRows_cast_subst heq hnm has hrs hcast
          refine Or.inr (Or.inr
            ⟨fun hmem => ?_, fun hmem => ?_, Or.inl ⟨⟨hnm', has', hrs'⟩, hcast'⟩⟩)
          · rcases List.mem_map.mp hmem with ⟨r, hr, hr_eq⟩
            have hsome : (rRows.find? (·.name == hd.name)).isSome = true :=
              List.find?_isSome.mpr ⟨r, hr, beq_iff_eq.mpr (hr_eq.trans hnm'.symm)⟩
            simp [hnone] at hsome
          · rcases List.mem_map.mp hmem with ⟨b, hb, hb_eq⟩
            rcases List.mem_flatMap.mp hb with ⟨p, hp, hb_p⟩
            exact hBefDisj p hp b hb_p (by simp [hb_eq.trans hnm'.symm])
        · obtain ⟨has', hrs', hnm', hcast'⟩ := patchRows_cast_subst heq hnm has hrs hcast
          exact Or.inl ⟨r, hr, hnm', has', hrs', hcast'⟩
      · have hsig_hd : rowSig ((rRows.find? (·.name == hd.name)).getD hd) = rowSig hd := by
          cases hf : rRows.find? (·.name == hd.name) with
          | none => rfl
          | some r =>
            have hnm := beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == hd.name)
              hf)
            exact hReplSigs r (List.mem_of_find?_eq_some hf) hd List.mem_cons_self hnm
        have hne_hd : ¬ (hd.name = f ∧ hd.as = as ∧ hd.rs = bs) := by
          intro hhd
          apply hne
          refine ⟨(congrArg Prod.fst hsig_hd).trans hhd.1, ?_, ?_⟩
          · exact (congrArg (fun p => p.2.1) hsig_hd).trans hhd.2.1
          · exact (congrArg (fun p => p.2.2) hsig_hd).trans hhd.2.2
        rcases ih hReplSigs' hBefDisj' htl_rest with hr | hb | ⟨hnr, hnb, htl0⟩
        · exact Or.inl hr
        · exact Or.inr (Or.inl hb)
        · exact Or.inr (Or.inr ⟨hnr, hnb, Or.inr ⟨hne_hd, htl0⟩⟩)

theorem ofTable_of_cast {tbl : List SpecEntry} {r : SpecEntry}
    (hr : r ∈ tbl) (hnd : (tbl.map SpecEntry.name).Nodup)
    {f : Sym} {as bs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (hnm : r.name = f) (has : r.as = as) (hrs : r.rs = bs)
    (hcast : r.cast has hrs xs m Q X) :
    Env.ofTable tbl f as bs xs m Q X := by
  cases r
  dsimp only at hnm has hrs
  cases hnm; cases has; cases hrs
  exact Env.ofTable_of_mem hr hnd hcast

private theorem tableImpl_of_moduleOk {Γ : Env} {M : LeanQbe.T.Module} {tbl : List SpecEntry}
    (hM : ModuleOk Γ M)
    (hSigs : tbl.map rowSig = M.fns.map Fn.sig)
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hLift : ∀ e ∈ tbl, ∀ xs m Q X,
      Env.ofTable tbl e.name e.as e.rs xs m Q X → Γ e.name e.as e.rs xs m Q X) :
    TableImpl Γ M.fns tbl := by
  have hAux : ∀ {pre fs : List Fn} {rs : List SpecEntry},
      M.fns = pre ++ fs →
      rs.map rowSig = fs.map Fn.sig →
      (∀ r ∈ rs, r ∈ tbl) →
      TableImpl Γ fs rs := by
    intro pre fs rs hsplit hSigs_fs hsub
    induction fs generalizing pre rs with
    | nil =>
      cases rs with
      | nil => trivial
      | cons => simp at hSigs_fs
    | cons f fs' ih =>
      cases rs with
      | nil => simp at hSigs_fs
      | cons r rs' =>
        simp only [List.map_cons, List.cons.injEq] at hSigs_fs
        have hr_mem : r ∈ tbl := hsub r List.mem_cons_self
        have hfnOk := (hM.fnsOk pre f fs' hsplit).2.2
        have hsig_r : r.name = f.name ∧ r.as = f.as ∧ r.rs = f.rs :=
          ⟨congrArg Prod.fst hSigs_fs.1, congrArg (fun p => p.2.1) hSigs_fs.1,
           congrArg (fun p => p.2.2) hSigs_fs.1⟩
        have himpl : SpecEntry.Impl Γ f r := by
          refine ⟨hsig_r, fun xs m Q X hcast => ?_⟩
          rcases hsig_r with ⟨hnm, has, hrs⟩
          cases r; dsimp only at hnm has hrs; subst hnm; subst has; subst hrs
          exact hfnOk xs m Q X (hLift _ hr_mem xs m Q X (Env.ofTable_of_mem hr_mem hnd hcast))
        refine ⟨himpl, ih (pre := pre ++ [f]) (by rw [hsplit, List.append_assoc, List.cons_append,
          List.nil_append]) hSigs_fs.2 (fun x hx => hsub x (List.mem_cons_of_mem _ hx))⟩
  exact hAux (pre := []) rfl hSigs (fun _ h => h)

/-! ## 2. Temporary `M8BveHook`, `m8CoreParitySpecTable`, & `M8CoreParityEnv` -/

/-- Excluded symbols whose specs change in `FullM8CoreParity` and therefore cannot be
blindly forwarded from `m7FidelityEnv` (`4` names; `"full_has_ternary"` preserves
`Full.fullHasTernarySpec` and needs no exclusion). -/
def m8CpExclNames : List Sym :=
  ["full_min_shrink_m6", "full_min_shrink", "full_bve_var_key_m7", "full_bve_heap_push_m7"]

private structure M8BveHook : Type where
  helperRows : List SpecEntry
  helperRows_sigs : helperRows.map (fun e => (e.name, e.as, e.rs)) = m8BveHelpers.map Fn.sig
  helperRows_noExit : helperRows.all SpecEntry.noExit = true
  varKeySpec : Spec [i64, i32] [i64]
  varKey_noExit : ∀ xs m Q X X', varKeySpec xs m Q X → varKeySpec xs m Q X'
  heapPushSpec : Spec [i64, i64, i32] [i64]
  heapPush_noExit :
    ∀ xs m Q X X', heapPushSpec xs m Q X → heapPushSpec xs m Q X'
  helpers_impl : ∀ (Γ : Env),
    (∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      Γ f as bs xs m Q X) →
    (∀ e ∈ helperRows, ∀ xs m Q X,
      Env.ofTable helperRows e.name e.as e.rs xs m Q X → Γ e.name e.as e.rs xs m Q X) →
    TableImpl Γ m8BveHelpers helperRows
  varM7_wp : ∀ (Γ : Env),
    (∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      Γ f as bs xs m Q X) →
    (∀ e ∈ helperRows, ∀ xs m Q X,
      Env.ofTable helperRows e.name e.as e.rs xs m Q X → Γ e.name e.as e.rs xs m Q X) →
    ∀ a m Q X, FullFastBveBudgets.fullBveVarDefSpec a m Q X → Func.wp Γ full_bve_var_m7_body a m Q X
  var_wp : ∀ (Γ : Env),
    (∀ a m Q X, FullFastBveBudgets.fullBveVarDefSpec a m Q X →
      Γ "full_bve_var_m7" [i64, i32] [i64] a m Q X) →
    ∀ a m Q X, FullFastBveBudgets.fullBveVarDefSpec a m Q X → Func.wp Γ full_bve_var_body a m Q X
  varKey_wp : ∀ (Γ : Env),
    ∀ a m Q X, varKeySpec a m Q X → Func.wp Γ full_bve_var_key_m7_body a m Q X
  heapPush_wp : ∀ (Γ : Env),
    (∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      Γ f as bs xs m Q X) →
    (∀ a m Q X, varKeySpec a m Q X → Γ "full_bve_var_key_m7" [i64, i32] [i64] a m Q X) →
    ∀ a m Q X, heapPushSpec a m Q X →
      Func.wp Γ FullM7BveGates.full_bve_heap_push_m7_body a m Q X
  elimBve_wp : ∀ (Γ : Env),
    (∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      Γ f as bs xs m Q X) →
    (∀ a m Q X, heapPushSpec a m Q X →
      Γ "full_bve_heap_push_m7" [i64, i64, i32] [i64] a m Q X) →
    ∀ a m Q X, FullM3CongBva.m3ElimBveSpec a m Q X →
      Func.wp Γ FullM7FidelityCore.full_elim_bve_fid_body a m Q X

/-- Specification rows for the `3` new Rank #5 minimization DFS/shrink helpers. -/
def m8MinHelperRows : List SpecEntry :=
  [ ⟨"full_min_lit_dfs_m8", [i64, i32, .bool, .bool], [.bool], m8MinLitDfsSpec, true⟩
  , ⟨"full_shrink_lower_m8", [i64, i32, i32], [.bool], m8ShrinkLowerSpec, true⟩
  , ⟨"full_shrink_blk_bool_m8", [i64, i64, i64, i32, i64], [.bool], m8ShrinkBlkBoolSpec, true⟩ ]

theorem m8MinHelperRows_sigs :
    m8MinHelperRows.map (fun e => (e.name, e.as, e.rs)) = m8MinHelpers.map Fn.sig := by
  t_kernel_rfl

theorem m8MinHelperRows_noExit : m8MinHelperRows.all SpecEntry.noExit = true := by
  t_kernel_rfl

theorem m8MinHelperRows_nodup : (m8MinHelperRows.map SpecEntry.name).Nodup := by
  decide

private def m7FidReplRows : List SpecEntry :=
  [ mfExtraRows[51]'(by decide), mfExtraRows[52]'(by decide), mfExtraRows[53]'(by decide)
  , mfExtraRows[54]'(by decide), mfExtraRows[55]'(by decide), mfExtraRows[56]'(by decide) ]

private def m7FidBeforeRows : List (Sym × List SpecEntry) :=
  [ ("full_bva_filter_row", [mfExtraRows[57]'(by decide)])
  , ("full_reorder_queue_m7", [mfExtraRows[58]'(by decide)])
  , ("full_search_m6", [mfExtraRows[59]'(by decide)]) ]

/-- Full `413`-row specification table matching `FullM7Fidelity.m7FidelityFns` (`0` duplicates). -/
def m7FidSpecTable : List SpecEntry :=
  PatchModule.patchRows m7FidReplRows m7FidBeforeRows m7FidBaseTable

private theorem m7FidReplRows_sigs_match :
    ∀ r ∈ m7FidReplRows, ∀ e ∈ m7FidBaseTable, r.name = e.name → rowSig r = rowSig e := by
  have hsigs := m7FidBaseTable_sigs
  intro r hr e he hnm
  have hrowSig : rowSig e ∈ m7FidBaseTable.map rowSig := List.mem_map.mpr ⟨e, he, rfl⟩
  rw [hsigs] at hrowSig
  rcases List.mem_map.mp hrowSig with ⟨f, hf, hfe⟩
  have heq_f : f.name = r.name := (congrArg Prod.fst hfe).trans hnm.symm
  simp only [m7FidReplRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨g217, hg217, hsg217⟩ := sig_of_map_idx mf_idx_217
    have hg := m8cp_nodup_name_eq Fn.name m7_names_nodup hf (List.mem_of_getElem? hg217)
      (by rw [heq_f]; exact (congrArg Prod.fst hsg217).symm)
    rw [← hfe, hg, hsg217]; dsimp only [rowSig]; rfl
  · have hm52 : m7Fns[353]?.map Fn.sig = some ("full_compact_needed", [i64], [.bool]) :=
      mf_idx_353
    obtain ⟨g353, hg353, hsg353⟩ := sig_of_map_idx hm52
    have hg := m8cp_nodup_name_eq Fn.name m7_names_nodup hf (List.mem_of_getElem? hg353)
      (by rw [heq_f]; exact (congrArg Prod.fst hsg353).symm)
    rw [← hfe, hg, hsg353]; dsimp only [rowSig]; rfl
  · obtain ⟨g164, hg164, hsg164⟩ := sig_of_map_idx mf_idx_164
    have hg := m8cp_nodup_name_eq Fn.name m7_names_nodup hf (List.mem_of_getElem? hg164)
      (by rw [heq_f]; exact (congrArg Prod.fst hsg164).symm)
    rw [← hfe, hg, hsg164]; dsimp only [rowSig]; rfl
  · obtain ⟨g118, hg118, hsg118⟩ := sig_of_map_idx mf_idx_118
    have hg := m8cp_nodup_name_eq Fn.name m7_names_nodup hf (List.mem_of_getElem? hg118)
      (by rw [heq_f]; exact (congrArg Prod.fst hsg118).symm)
    rw [← hfe, hg, hsg118]; dsimp only [rowSig]; rfl
  · have hm166 : FullM7.m7Fns[166]?.map Fn.sig = some ("full_walk_warmup_m7", [i64], []) := by
      rw [mf_idx_166]; rfl
    obtain ⟨g166, hg166, hsg166⟩ := sig_of_map_idx hm166
    have hg := m8cp_nodup_name_eq Fn.name m7_names_nodup hf (List.mem_of_getElem? hg166)
      (by rw [heq_f]; exact (congrArg Prod.fst hsg166).symm)
    rw [← hfe, hg, hsg166]; dsimp only [rowSig]; rfl
  · have hm168 : FullM7.m7Fns[168]?.map Fn.sig = some ("full_walk", [i64], []) := by
      rw [mf_idx_168]; rfl
    obtain ⟨g168, hg168, hsg168⟩ := sig_of_map_idx hm168
    have hg := m8cp_nodup_name_eq Fn.name m7_names_nodup hf (List.mem_of_getElem? hg168)
      (by rw [heq_f]; exact (congrArg Prod.fst hsg168).symm)
    rw [← hfe, hg, hsg168]; dsimp only [rowSig]; rfl

theorem m7FidSpecTable_sigs :
    m7FidSpecTable.map (fun e => (e.name, e.as, e.rs)) = m7FidelityFns.map Fn.sig := by
  change (PatchModule.patchRows m7FidReplRows m7FidBeforeRows m7FidBaseTable).map rowSig =
    m7FidelityFns.map Fn.sig
  rw [m7FidelityFns_eq_patchFns]
  refine patchRows_sigs_eq_patchFns_self m7FidBaseTable_sigs ?_ m7FidReplRows_sigs_match
    m7FidRepls_sigs
  intro e f hnm
  dsimp only [PatchModule.patchRowInsAt, PatchModule.patchInsAt, m7FidBeforeRows, m7FidBefores,
    FullM7FidelityCore.fidCorePatchBefores, FullM7FidelitySearch.fidSearchPatchBefores]
  rw [hnm]
  by_cases h1 : ("full_bva_filter_row" == f.name) <;>
    by_cases h2 : ("full_reorder_queue_m7" == f.name) <;>
    by_cases h3 : ("full_search_m6" == f.name)
  · exact absurd ((beq_iff_eq.mp h1).trans (beq_iff_eq.mp h2).symm) (by decide)
  · exact absurd ((beq_iff_eq.mp h1).trans (beq_iff_eq.mp h2).symm) (by decide)
  · exact absurd ((beq_iff_eq.mp h1).trans (beq_iff_eq.mp h3).symm) (by decide)
  · have h1e := beq_iff_eq.mp h1; rw [← h1e]; simp; dsimp only [rowSig]; rfl
  · exact absurd ((beq_iff_eq.mp h2).trans (beq_iff_eq.mp h3).symm) (by decide)
  · have h2e := beq_iff_eq.mp h2; rw [← h2e]; simp; dsimp only [rowSig]; rfl
  · have h3e := beq_iff_eq.mp h3; rw [← h3e]; simp; dsimp only [rowSig]; rfl
  · have h1n : "full_bva_filter_row" ≠ f.name := fun h => h1 (beq_iff_eq.mpr h)
    have h2n : "full_reorder_queue_m7" ≠ f.name := fun h => h2 (beq_iff_eq.mpr h)
    have h3n : "full_search_m6" ≠ f.name := fun h => h3 (beq_iff_eq.mpr h)
    simp [m8cp_sym_ne_beq h1n, m8cp_sym_ne_beq h2n, m8cp_sym_ne_beq h3n]

theorem m7FidSpecTable_noExit : m7FidSpecTable.all SpecEntry.noExit = true := by
  refine patchRows_noExit m7FidBaseTable_noExit ?_ ?_
  · rw [List.all_eq_true]
    intro r hr
    simp only [m7FidReplRows, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact mfExtraRows_noExit _ (List.getElem_mem _)
  · intro p hp
    simp only [m7FidBeforeRows, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      exact List.all_eq_true.mpr (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact mfExtraRows_noExit _ (List.getElem_mem _))

theorem m7FidSpecTable_nodup : (m7FidSpecTable.map SpecEntry.name).Nodup :=
  rowSigs_eq_fnSigs_nodup m7FidSpecTable_sigs m7FidelityFns_names_nodup

private theorem m7Fid_ofTable_to_env {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable m7FidSpecTable f as bs xs m Q X) : m7FidelityEnv f as bs xs m Q X := by
  have hBefDisj : ∀ p ∈ m7FidBeforeRows, ∀ b ∈ p.2,
      b.name ∉ m7FidBaseTable.map SpecEntry.name := by
    have hnd := congrArg (List.map Prod.fst) m7FidBaseTable_sigs
    simp only [List.map_map, Function.comp_def, Fn.sig] at hnd
    change m7FidBaseTable.map SpecEntry.name = FullM7.m7Fns.map Fn.name at hnd
    rw [hnd]
    intro p hp b hb
    simp only [m7FidBeforeRows, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp only [List.mem_singleton] at hb <;> subst hb
    · exact m7Fns_not_mem_bml
    · exact m7Fns_not_mem_sift
    · exact m7Fns_not_mem_hdec
  rcases ofTable_patchRows_elim m7FidReplRows_sigs_match hBefDisj h with hr | hb | hbase
  · rcases hr with ⟨r, hr, rfl, has, hrs, hcast⟩
    have hr_ex : r ∈ mfExtraRows := by
      simp only [m7FidReplRows, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact List.getElem_mem _
    exact M7FidelityEnv.extra (ofTable_of_cast hr_ex mfExtraRows_nodup rfl has hrs hcast)
  · rcases hb with ⟨p, hp, b, hb_p, rfl, has, hrs, hcast⟩
    have hb_ex : b ∈ mfExtraRows := by
      simp only [m7FidBeforeRows, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [List.mem_singleton] at hb_p <;> subst hb_p <;>
        exact List.getElem_mem _
    exact M7FidelityEnv.extra (ofTable_of_cast hb_ex mfExtraRows_nodup rfl has hrs hcast)
  · rcases hbase with ⟨hnr, hnb, hbase⟩
    refine M7FidelityEnv.base (fun hexcl => ?_) hbase
    have hrn : m7FidReplRows.map SpecEntry.name =
        ["full_vivify_tier_m6_hdr", "full_compact_needed", "full_walk_m7",
         "full_bump_analyzed_m6_hdr", "full_walk_warmup_m7", "full_walk"] := by t_kernel_rfl
    have hbn : (m7FidBeforeRows.flatMap Prod.snd).map SpecEntry.name =
        ["full_bva_match_large_fid", "full_reorder_sift_fid", "m6_hdr_decide_fid"] := by
      t_kernel_rfl
    rw [hrn] at hnr; rw [hbn] at hnb
    simp only [mfExclNames, List.mem_cons, List.not_mem_nil, or_false] at hexcl
    rcases hexcl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd (by decide) hnr | exact absurd (by decide) hnb

private def m8CoreParityReplRows (H : M8BveHook) : List SpecEntry :=
  [ ⟨"full_min_shrink_m6", [i64], [], m8MinShrinkSpec, true⟩
  , ⟨"full_bve_var_m7", [i64, i32], [i64], FullFastBveBudgets.fullBveVarDefSpec, true⟩
  , ⟨"full_bve_var", [i64, i32], [i64], FullFastBveBudgets.fullBveVarDefSpec, true⟩
  , ⟨"full_bve_var_key_m7", [i64, i32], [i64], H.varKeySpec, true⟩
  , ⟨"full_probe_dticks_m6_hdr", [i64, .bool], [i64], FullM6Hdr.m6HdrW2aSpec [.bool] [i64], true⟩
  , ⟨"full_probe_m6", [i64, .bool], [i64], FullM6Orch.m6ProbeSpec, true⟩
  , ⟨"full_search_m6", [i64], [i64], FullM6.fullM6SearchSpec, true⟩ ]

private def m8CoreParityBeforeRows (H : M8BveHook) : List (Sym × List SpecEntry) :=
  [ ("full_min_shrink_m6", m8MinHelperRows)
  , ("full_bve_var_m7", H.helperRows) ]

private def m8cpRewireRows (H : M8BveHook) : List SpecEntry :=
  [ ⟨"full_min_shrink", [i64], [], m8MinShrinkSpec, true⟩
  , ⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64], H.heapPushSpec, true⟩ ]

private def m8CoreParitySpecTableOf (H : M8BveHook) : List SpecEntry :=
  PatchModule.patchRows (m8CoreParityReplRows H ++ m8cpRewireRows H)
    (m8CoreParityBeforeRows H) m7FidSpecTable

private theorem m8cp_bveHelperRows_names_eq (H : M8BveHook) :
    H.helperRows.map SpecEntry.name = m8BveHelpers.map Fn.name := by
  have h1 := congrArg (List.map Prod.fst) H.helperRows_sigs
  simpa only [List.map_map, Function.comp_def, Fn.sig] using h1

private theorem m8cp_min_help_not_in_m7Fid :
    ∀ e ∈ m8MinHelperRows, e.name ∉ m7FidelityFns.map Fn.name := by
  have hdisj :
      (["full_min_lit_dfs_m8", "full_shrink_lower_m8", "full_shrink_blk_bool_m8"] : List String).all
        (fun nm => !((m7FidelityFns.map Fn.name).any (· == nm))) = true := by
    t_kernel_rfl
  intro e he hmem
  simp only [m8MinHelperRows, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · have h := List.all_eq_true.mp hdisj "full_min_lit_dfs_m8" (by decide)
    simp only [Bool.not_eq_true', List.any_eq_false, List.mem_map, beq_iff_eq] at h
    rcases List.mem_map.mp hmem with ⟨f, hf, hnm⟩
    exact h _ ⟨f, hf, rfl⟩ hnm
  · have h := List.all_eq_true.mp hdisj "full_shrink_lower_m8" (by decide)
    simp only [Bool.not_eq_true', List.any_eq_false, List.mem_map, beq_iff_eq] at h
    rcases List.mem_map.mp hmem with ⟨f, hf, hnm⟩
    exact h _ ⟨f, hf, rfl⟩ hnm
  · have h := List.all_eq_true.mp hdisj "full_shrink_blk_bool_m8" (by decide)
    simp only [Bool.not_eq_true', List.any_eq_false, List.mem_map, beq_iff_eq] at h
    rcases List.mem_map.mp hmem with ⟨f, hf, hnm⟩
    exact h _ ⟨f, hf, rfl⟩ hnm

private theorem m8cp_bve_help_not_in_m7Fid (H : M8BveHook) :
    ∀ e ∈ H.helperRows, e.name ∉ m7FidelityFns.map Fn.name := by
  have hdisj : (m8BveHelpers.map Fn.name).all
      (fun nm => !((m7FidelityFns.map Fn.name).contains nm)) = true := by
    t_kernel_rfl
  intro e he hmem
  have he_bve : e.name ∈ m8BveHelpers.map Fn.name := by
    rw [← m8cp_bveHelperRows_names_eq H]; exact List.mem_map_of_mem he
  have h1 := List.all_eq_true.mp hdisj e.name he_bve
  simp only [Bool.not_eq_true'] at h1
  exact absurd hmem (by simpa using h1)

private theorem m8cp_befores_sigs_match (H : M8BveHook) (e : SpecEntry) (f : Fn)
    (hnm : e.name = f.name) :
    (PatchModule.patchRowInsAt (m8CoreParityBeforeRows H) e).map rowSig =
      (PatchModule.patchInsAt m8CoreParityBefores f).map Fn.sig := by
  dsimp only [PatchModule.patchRowInsAt, PatchModule.patchInsAt,
    m8CoreParityBeforeRows, m8CoreParityBefores]
  rw [hnm]
  by_cases h1 : ("full_min_shrink_m6" == f.name) <;>
    by_cases h2 : ("full_bve_var_m7" == f.name)
  · exact absurd ((beq_iff_eq.mp h1).trans (beq_iff_eq.mp h2).symm) (by decide)
  · have h1e := beq_iff_eq.mp h1; rw [← h1e]; unfold rowSig; exact m8MinHelperRows_sigs
  · have h2e := beq_iff_eq.mp h2; rw [← h2e]; unfold rowSig; exact H.helperRows_sigs
  · have h1n : "full_min_shrink_m6" ≠ f.name := fun h => h1 (beq_iff_eq.mpr h)
    have h2n : "full_bve_var_m7" ≠ f.name := fun h => h2 (beq_iff_eq.mpr h)
    simp [m8cp_sym_ne_beq h1n, m8cp_sym_ne_beq h2n]

private theorem m8cp_replRows_sigs_of_fns (H : M8BveHook)
    {tbl : List SpecEntry} {fs : List Fn} (hSigs : tbl.map rowSig = fs.map Fn.sig)
    (hnd : (fs.map Fn.name).Nodup)
    (h135 : ∃ g ∈ fs, g.sig = ("full_min_shrink_m6", [i64], []))
    (h137 : ∃ g ∈ fs, g.sig = ("full_min_shrink", [i64], []))
    (h338 : ∃ g ∈ fs, g.sig = ("full_bve_var_m7", [i64, i32], [i64]))
    (h339 : ∃ g ∈ fs, g.sig = ("full_bve_var", [i64, i32], [i64]))
    (h379 : ∃ g ∈ fs, g.sig = ("full_bve_var_key_m7", [i64, i32], [i64]))
    (h382 : ∃ g ∈ fs, g.sig = ("full_bve_heap_push_m7", [i64, i64, i32], [i64]))
    (h402 : ∃ g ∈ fs, g.sig = ("full_probe_dticks_m6_hdr", [i64, .bool], [i64]))
    (h404 : ∃ g ∈ fs, g.sig = ("full_probe_m6", [i64, .bool], [i64]))
    (h408 : ∃ g ∈ fs, g.sig = ("full_search_m6", [i64], [i64])) :
    ∀ r ∈ m8CoreParityReplRows H ++ m8cpRewireRows H,
      ∀ e ∈ tbl, r.name = e.name → rowSig r = rowSig e := by
  intro r hr e he hnm
  have he_sig : rowSig e ∈ tbl.map rowSig := List.mem_map.mpr ⟨e, he, rfl⟩
  rw [hSigs] at he_sig
  rcases List.mem_map.mp he_sig with ⟨f, hf, hfe⟩
  have hfnm : r.name = f.name := hnm.trans (congrArg Prod.fst hfe).symm
  rcases List.mem_append.mp hr with hrRepl | hrRew
  · simp only [m8CoreParityReplRows, List.mem_cons, List.not_mem_nil, or_false] at hrRepl
    rcases hrRepl with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨g, hg, hsg⟩ := h135
      have hfg := m8cp_nodup_name_eq Fn.name hnd hf hg
        (by rw [← hfnm]; exact (congrArg Prod.fst hsg).symm)
      rw [← hfe, hfg, hsg] <;> rfl
    · obtain ⟨g, hg, hsg⟩ := h338
      have hfg := m8cp_nodup_name_eq Fn.name hnd hf hg
        (by rw [← hfnm]; exact (congrArg Prod.fst hsg).symm)
      rw [← hfe, hfg, hsg] <;> rfl
    · obtain ⟨g, hg, hsg⟩ := h339
      have hfg := m8cp_nodup_name_eq Fn.name hnd hf hg
        (by rw [← hfnm]; exact (congrArg Prod.fst hsg).symm)
      rw [← hfe, hfg, hsg] <;> rfl
    · obtain ⟨g, hg, hsg⟩ := h379
      have hfg := m8cp_nodup_name_eq Fn.name hnd hf hg
        (by rw [← hfnm]; exact (congrArg Prod.fst hsg).symm)
      rw [← hfe, hfg, hsg] <;> rfl
    · obtain ⟨g, hg, hsg⟩ := h402
      have hfg := m8cp_nodup_name_eq Fn.name hnd hf hg
        (by rw [← hfnm]; exact (congrArg Prod.fst hsg).symm)
      rw [← hfe, hfg, hsg] <;> rfl
    · obtain ⟨g, hg, hsg⟩ := h404
      have hfg := m8cp_nodup_name_eq Fn.name hnd hf hg
        (by rw [← hfnm]; exact (congrArg Prod.fst hsg).symm)
      rw [← hfe, hfg, hsg] <;> rfl
    · obtain ⟨g, hg, hsg⟩ := h408
      have hfg := m8cp_nodup_name_eq Fn.name hnd hf hg
        (by rw [← hfnm]; exact (congrArg Prod.fst hsg).symm)
      rw [← hfe, hfg, hsg] <;> rfl
  · simp only [m8cpRewireRows, List.mem_cons, List.not_mem_nil, or_false] at hrRew
    rcases hrRew with rfl | rfl
    · obtain ⟨g, hg, hsg⟩ := h137
      have hfg := m8cp_nodup_name_eq Fn.name hnd hf hg
        (by rw [← hfnm]; exact (congrArg Prod.fst hsg).symm)
      rw [← hfe, hfg, hsg] <;> rfl
    · obtain ⟨g, hg, hsg⟩ := h382
      have hfg := m8cp_nodup_name_eq Fn.name hnd hf hg
        (by rw [← hfnm]; exact (congrArg Prod.fst hsg).symm)
      rw [← hfe, hfg, hsg] <;> rfl

private theorem m8cp_fid_idx_135 : m7FidelityFns[135]?.map Fn.sig =
    some ("full_min_shrink_m6", [i64], []) := by t_kernel_rfl
private theorem m8cp_fid_idx_137 : m7FidelityFns[137]?.map Fn.sig =
    some ("full_min_shrink", [i64], []) := by t_kernel_rfl
private theorem m8cp_fid_idx_338 : m7FidelityFns[338]?.map Fn.sig =
    some ("full_bve_var_m7", [i64, i32], [i64]) := by t_kernel_rfl
private theorem m8cp_fid_idx_339 : m7FidelityFns[339]?.map Fn.sig =
    some ("full_bve_var", [i64, i32], [i64]) := by t_kernel_rfl
private theorem m8cp_fid_idx_379 : m7FidelityFns[379]?.map Fn.sig =
    some ("full_bve_var_key_m7", [i64, i32], [i64]) := by t_kernel_rfl
private theorem m8cp_fid_idx_382 : m7FidelityFns[382]?.map Fn.sig =
    some ("full_bve_heap_push_m7", [i64, i64, i32], [i64]) := by t_kernel_rfl
private theorem m8cp_fid_idx_402 : m7FidelityFns[402]?.map Fn.sig =
    some ("full_probe_dticks_m6_hdr", [i64, .bool], [i64]) := by t_kernel_rfl
private theorem m8cp_fid_idx_404 : m7FidelityFns[404]?.map Fn.sig =
    some ("full_probe_m6", [i64, .bool], [i64]) := by t_kernel_rfl
private theorem m8cp_fid_idx_408 : m7FidelityFns[408]?.map Fn.sig =
    some ("full_search_m6", [i64], [i64]) := by t_kernel_rfl

private theorem m8CoreParitySpecTableOf_sigs (H : M8BveHook) :
    (m8CoreParitySpecTableOf H).map (fun e => (e.name, e.as, e.rs)) =
      m8CoreParityFns.map Fn.sig := by
  change (PatchModule.patchRows (m8CoreParityReplRows H ++ m8cpRewireRows H)
    (m8CoreParityBeforeRows H) m7FidSpecTable).map rowSig = m8CoreParityFns.map Fn.sig
  rw [m8CoreParityFns_eq_patchFns]
  refine patchRows_sigs_eq_patchFns_self m7FidSpecTable_sigs (m8cp_befores_sigs_match H) ?_
    m8CoreParity_replSigs
  exact m8cp_replRows_sigs_of_fns H m7FidSpecTable_sigs m7FidelityFns_names_nodup
    (m8cp_sig_exists_of_map m8cp_fid_idx_135) (m8cp_sig_exists_of_map m8cp_fid_idx_137)
    (m8cp_sig_exists_of_map m8cp_fid_idx_338) (m8cp_sig_exists_of_map m8cp_fid_idx_339)
    (m8cp_sig_exists_of_map m8cp_fid_idx_379) (m8cp_sig_exists_of_map m8cp_fid_idx_382)
    (m8cp_sig_exists_of_map m8cp_fid_idx_402) (m8cp_sig_exists_of_map m8cp_fid_idx_404)
    (m8cp_sig_exists_of_map m8cp_fid_idx_408)

private theorem m8CoreParitySpecTableOf_length (H : M8BveHook) :
    (m8CoreParitySpecTableOf H).length = 435 := by
  rw [rowSigs_eq_fnSigs_len (m8CoreParitySpecTableOf_sigs H)]
  t_kernel_rfl

private theorem m8CoreParitySpecTableOf_noExit (H : M8BveHook) :
    (m8CoreParitySpecTableOf H).all SpecEntry.noExit = true := by
  refine patchRows_noExit m7FidSpecTable_noExit ?_ ?_
  · simp only [m8CoreParityReplRows, m8cpRewireRows, List.all_append, List.all_cons, List.all_nil,
      Bool.and_true]
  · intro p hp
    simp only [m8CoreParityBeforeRows, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact m8MinHelperRows_noExit
    · exact H.helperRows_noExit

private theorem m8CoreParitySpecTableOf_nodup (H : M8BveHook) :
    ((m8CoreParitySpecTableOf H).map SpecEntry.name).Nodup :=
  rowSigs_eq_fnSigs_nodup (m8CoreParitySpecTableOf_sigs H) m8CoreParityFns_names_nodup

private inductive M8CoreParityEnv (H : M8BveHook) (Γbase : Env) : Env where
  | base {f as bs xs m Q X} :
      f ∉ m8CpExclNames → Γbase f as bs xs m Q X → M8CoreParityEnv H Γbase f as bs xs m Q X
  | minShrinkM6 {a m Q X} :
      m8MinShrinkSpec a m Q X →
      M8CoreParityEnv H Γbase "full_min_shrink_m6" [i64] [] a m Q X
  | minShrink {a m Q X} :
      m8MinShrinkSpec a m Q X →
      M8CoreParityEnv H Γbase "full_min_shrink" [i64] [] a m Q X
  | varKey {a m Q X} :
      H.varKeySpec a m Q X →
      M8CoreParityEnv H Γbase "full_bve_var_key_m7" [i64, i32] [i64] a m Q X
  | heapPush {a m Q X} :
      H.heapPushSpec a m Q X →
      M8CoreParityEnv H Γbase "full_bve_heap_push_m7" [i64, i64, i32] [i64] a m Q X
  | minHelp {f as bs xs m Q X} :
      Env.ofTable m8MinHelperRows f as bs xs m Q X →
      M8CoreParityEnv H Γbase f as bs xs m Q X
  | bveHelp {f as bs xs m Q X} :
      Env.ofTable H.helperRows f as bs xs m Q X →
      M8CoreParityEnv H Γbase f as bs xs m Q X

private def m8CoreParityEnvOf (H : M8BveHook) : Env :=
  M8CoreParityEnv H m7FidelityEnv

private theorem m8CoreParityEnv_cases {H : M8BveHook} {Γbase : Env} {nm : Sym}
    {as bs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : M8CoreParityEnv H Γbase nm as bs xs m Q X) :
    (nm ∉ m8CpExclNames ∧ Γbase nm as bs xs m Q X) ∨
    (nm = "full_min_shrink_m6" ∧ ∃ (ha : as = [i64]) (hb : bs = []),
      m8MinShrinkSpec (ha ▸ xs) m (hb ▸ Q) X) ∨
    (nm = "full_min_shrink" ∧ ∃ (ha : as = [i64]) (hb : bs = []),
      m8MinShrinkSpec (ha ▸ xs) m (hb ▸ Q) X) ∨
    (nm = "full_bve_var_key_m7" ∧ ∃ (ha : as = [i64, i32]) (hb : bs = [i64]),
      H.varKeySpec (ha ▸ xs) m (hb ▸ Q) X) ∨
    (nm = "full_bve_heap_push_m7" ∧ ∃ (ha : as = [i64, i64, i32]) (hb : bs = [i64]),
      H.heapPushSpec (ha ▸ xs) m (hb ▸ Q) X) ∨
    Env.ofTable m8MinHelperRows nm as bs xs m Q X ∨
    Env.ofTable H.helperRows nm as bs xs m Q X := by
  cases h with
  | base hne hb => exact Or.inl ⟨hne, hb⟩
  | minShrinkM6 hs => exact Or.inr (Or.inl ⟨rfl, rfl, rfl, hs⟩)
  | minShrink hs => exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, hs⟩))
  | varKey hs => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, hs⟩)))
  | heapPush hs => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, hs⟩))))
  | minHelp hm => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm)))))
  | bveHelp hm => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hm)))))

private theorem m8CoreParityEnv_noExit_of (H : M8BveHook) {Γbase : Env}
    (hBase : ∀ f as bs xs m Q X X', Γbase f as bs xs m Q X → Γbase f as bs xs m Q X') :
    ∀ f as bs xs m Q X X',
      M8CoreParityEnv H Γbase f as bs xs m Q X → M8CoreParityEnv H Γbase f as bs xs m Q X' := by
  intro f as bs xs m Q X X' h
  cases h with
  | base hne hb => exact .base hne (hBase _ _ _ _ _ _ _ _ hb)
  | minShrinkM6 hs => exact .minShrinkM6 (m8MinShrinkSpec_monoX hs)
  | minShrink hs => exact .minShrink (m8MinShrinkSpec_monoX hs)
  | varKey hs => exact .varKey (H.varKey_noExit _ _ _ _ _ hs)
  | heapPush hs => exact .heapPush (H.heapPush_noExit _ _ _ _ _ hs)
  | minHelp hm =>
    exact .minHelp (Env.ofTable_noExit (fun e he => List.all_eq_true.mp m8MinHelperRows_noExit e he)
      _ _ _ _ _ _ _ _ hm)
  | bveHelp hm =>
    exact .bveHelp (Env.ofTable_noExit (fun e he => List.all_eq_true.mp H.helperRows_noExit e he)
      _ _ _ _ _ _ _ _ hm)

private theorem m8CoreParityEnvOf_noExit (H : M8BveHook) :
    ∀ f as bs xs m Q X X',
      m8CoreParityEnvOf H f as bs xs m Q X → m8CoreParityEnvOf H f as bs xs m Q X' :=
  m8CoreParityEnv_noExit_of H m7FidelityEnv_noExit

private theorem m8CoreParity_ofTable_name_mem {nm : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost} :
    ∀ {tbl : List SpecEntry},
    Env.ofTable tbl nm as bs xs m Q X → nm ∈ tbl.map SpecEntry.name
  | [], h => False.elim h
  | e :: _, h => by
    by_cases hnm : e.name = nm
    · rw [← hnm]; exact List.mem_cons_self
    · rw [Env.ofTable_cons_ne hnm] at h
      exact List.mem_cons_of_mem _ (m8CoreParity_ofTable_name_mem h)

private theorem m8CoreParityEnvOf_solve_bytes_iff (H : M8BveHook)
    {xs : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m8CoreParityEnvOf H "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X ↔
      m7FidSolveBytesSpec xs m Q (fun _ _ _ _ => False) := by
  constructor
  · intro h
    rcases m8CoreParityEnv_cases h with ⟨_, hb⟩ | ⟨hc, _⟩ | ⟨hc, _⟩ | ⟨hc, _⟩ | ⟨hc, _⟩ |
        hm | hm
    · exact m7FidelityEnv_solve_bytes_iff.mp hb
    · exact absurd hc (by decide)
    · exact absurd hc (by decide)
    · exact absurd hc (by decide)
    · exact absurd hc (by decide)
    · exact False.elim (absurd (m8CoreParity_ofTable_name_mem hm) (by decide))
    · have hn : "kissat_solve_bytes" ∈ H.helperRows.map SpecEntry.name :=
        m8CoreParity_ofTable_name_mem hm
      rcases List.mem_map.mp hn with ⟨e, he, hnm⟩
      exfalso
      apply m8cp_bve_help_not_in_m7Fid H e he
      rw [hnm]
      exact List.mem_map.mpr ⟨m6oSolveBytesFn, m7Fidelity_solveBytes_mem, rfl⟩
  · intro hs
    exact M8CoreParityEnv.base (by decide) (m7FidelityEnv_solve_bytes_iff.mpr hs)

private theorem m8cp_bveHelperRows_nodup (H : M8BveHook) :
    (H.helperRows.map SpecEntry.name).Nodup := by
  have hnd := m8CoreParityFns_names_nodup
  unfold m8CoreParityFns mfPatchFns at hnd
  obtain ⟨g338, hg338, hsg338⟩ := m8cp_sig_of_map m8cp_fid_idx_338
  have hg := List.mem_of_getElem? hg338
  obtain ⟨pre, post, hsp⟩ := List.append_of_mem hg
  rw [hsp, List.flatMap_append, List.flatMap_cons, List.map_append, List.map_append,
    List.nodup_append, List.nodup_append] at hnd
  have hp_ins : mfPatchInsAt m8CoreParityBefores g338 = m8BveHelpers := by
    have hnm : g338.name = "full_bve_var_m7" := congrArg Prod.fst hsg338
    dsimp only [mfPatchInsAt, m8CoreParityBefores]; rw [hnm]; rfl
  have hnd_bh : (m8BveHelpers.map Fn.name).Nodup := by
    have h1 := hnd.2.1.1
    rw [List.map_append, List.nodup_append] at h1
    rw [← hp_ins]; exact h1.1
  exact rowSigs_eq_fnSigs_nodup H.helperRows_sigs hnd_bh

private theorem m8CoreParityEnv_of_specTable_gen (H : M8BveHook) {Γbase : Env}
    {tbl : List SpecEntry} {fs : List Fn}
    (hSigs : tbl.map rowSig = fs.map Fn.sig) (hnd : (fs.map Fn.name).Nodup)
    (hBaseLift : ∀ f as bs xs m Q X, Env.ofTable tbl f as bs xs m Q X → Γbase f as bs xs m Q X)
    (hM7 : ∀ f as bs xs m Q X, m7FidelityEnv f as bs xs m Q X → Γbase f as bs xs m Q X)
    (h135 : ∃ g ∈ fs, g.sig = ("full_min_shrink_m6", [i64], []))
    (h137 : ∃ g ∈ fs, g.sig = ("full_min_shrink", [i64], []))
    (h338 : ∃ g ∈ fs, g.sig = ("full_bve_var_m7", [i64, i32], [i64]))
    (h339 : ∃ g ∈ fs, g.sig = ("full_bve_var", [i64, i32], [i64]))
    (h379 : ∃ g ∈ fs, g.sig = ("full_bve_var_key_m7", [i64, i32], [i64]))
    (h382 : ∃ g ∈ fs, g.sig = ("full_bve_heap_push_m7", [i64, i64, i32], [i64]))
    (h402 : ∃ g ∈ fs, g.sig = ("full_probe_dticks_m6_hdr", [i64, .bool], [i64]))
    (h404 : ∃ g ∈ fs, g.sig = ("full_probe_m6", [i64, .bool], [i64]))
    (h408 : ∃ g ∈ fs, g.sig = ("full_search_m6", [i64], [i64]))
    (hBefDisj : ∀ p ∈ m8CoreParityBeforeRows H, ∀ b ∈ p.2, b.name ∉ tbl.map SpecEntry.name)
    {f : Sym} {as bs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable (PatchModule.patchRows (m8CoreParityReplRows H ++ m8cpRewireRows H)
      (m8CoreParityBeforeRows H) tbl) f as bs xs m Q X) :
    M8CoreParityEnv H Γbase f as bs xs m Q X := by
  have hReplSigs := m8cp_replRows_sigs_of_fns H hSigs hnd h135 h137 h338 h339 h379 h382
    h402 h404 h408
  have hBveVar : ∀ {a m Q X}, FullFastBveBudgets.fullBveVarDefSpec a m Q X →
      m7FidelityEnv "full_bve_var" [i64, i32] [i64] a m Q X := fun {a m Q X} hs =>
    M7FidelityEnv.base (by decide) (m7FidBase_row_mem
      (m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 33) rfl)) (fun _ _ _ _ h => h) _ _ _ _ hs)
  have hBveVarM7 : ∀ {a m Q X}, FullFastBveBudgets.fullBveVarDefSpec a m Q X →
      m7FidelityEnv "full_bve_var_m7" [i64, i32] [i64] a m Q X := fun {a m Q X} hs =>
    M7FidelityEnv.base (by decide)
      (m7FidBase_row_mem m7FidBase_bveVar_mem (fun _ _ _ _ h => h) _ _ _ _ hs)
  have hc3p := m7FidPart3PfxCallees_of_sub m7FidBase_part3Pfx_mem
  have hProbeDt : ∀ {a m Q X}, FullM6Hdr.m6HdrW2aSpec [.bool] [i64] a m Q X →
      m7FidelityEnv "full_probe_dticks_m6_hdr" [i64, .bool] [i64] a m Q X := fun {a m Q X} hs =>
    M7FidelityEnv.base (by decide) (m7FidBase_row_mem hc3p.probeDticks
      (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h) _ _ _ _ hs)
  have hProbe : ∀ {a m Q X}, m6ProbeSpec a m Q X →
      m7FidelityEnv "full_probe_m6" [i64, .bool] [i64] a m Q X := fun {a m Q X} hs =>
    M7FidelityEnv.base (by decide) (m7FidBase_row_mem m7FidBase_probeM6_mem
      (fun _ _ _ _ h => FullM6Orch.m6ProbeSpec_monoX h) _ _ _ _ hs)
  have hSearch : ∀ {a m Q X}, fullM6SearchSpec a m Q X →
      m7FidelityEnv "full_search_m6" [i64] [i64] a m Q X := fun {a m Q X} hs =>
    M7FidelityEnv.base (by decide) (m7FidBase_row_mem m7FidBase_searchM6_mem
      (fun _ _ _ _ h => fullM6SearchSpec_monoX h) _ _ _ _ hs)
  rcases ofTable_patchRows_elim hReplSigs hBefDisj h with hr | hb | hbase
  · rcases hr with ⟨r, hr, rfl, has, hrs, hcast⟩
    rcases List.mem_append.mp hr with hrRepl | hrRew
    · simp only [m8CoreParityReplRows, List.mem_cons, List.not_mem_nil, or_false] at hrRepl
      rcases hrRepl with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · dsimp only at has hrs; cases has; cases hrs
        exact .minShrinkM6 (m8MinShrinkSpec_monoX hcast)
      · dsimp only at has hrs; cases has; cases hrs
        exact .base (by decide) (hM7 _ _ _ _ _ _ _ (hBveVarM7 hcast))
      · dsimp only at has hrs; cases has; cases hrs
        exact .base (by decide) (hM7 _ _ _ _ _ _ _ (hBveVar hcast))
      · dsimp only at has hrs; cases has; cases hrs
        exact .varKey (H.varKey_noExit _ _ _ _ _ hcast)
      · dsimp only at has hrs; cases has; cases hrs
        dsimp only [SpecEntry.cast, SpecEntry.eff] at hcast
        exact .base (by decide) (hM7 _ _ _ _ _ _ _
          (hProbeDt (FullM6Hdr.m6HdrW2aSpec_monoX hcast)))
      · dsimp only at has hrs; cases has; cases hrs
        dsimp only [SpecEntry.cast, SpecEntry.eff] at hcast
        exact .base (by decide) (hM7 _ _ _ _ _ _ _ (hProbe (FullM6Orch.m6ProbeSpec_monoX hcast)))
      · dsimp only at has hrs; cases has; cases hrs
        dsimp only [SpecEntry.cast, SpecEntry.eff] at hcast
        exact .base (by decide) (hM7 _ _ _ _ _ _ _ (hSearch (fullM6SearchSpec_monoX hcast)))
    · simp only [m8cpRewireRows, List.mem_cons, List.not_mem_nil, or_false] at hrRew
      rcases hrRew with rfl | rfl
      · dsimp only at has hrs; cases has; cases hrs; exact .minShrink (m8MinShrinkSpec_monoX hcast)
      · dsimp only at has hrs; cases has; cases hrs
        exact .heapPush (H.heapPush_noExit _ _ _ _ _ hcast)
  · rcases hb with ⟨p, hp, b, hb_p, rfl, has, hrs, hcast⟩
    simp only [m8CoreParityBeforeRows, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact .minHelp (ofTable_of_cast hb_p m8MinHelperRows_nodup rfl has hrs hcast)
    · exact .bveHelp (ofTable_of_cast hb_p (m8cp_bveHelperRows_nodup H) rfl has hrs hcast)
  · rcases hbase with ⟨hnr, _, htbl⟩
    refine .base (fun hexcl => ?_) (hBaseLift f as bs xs m Q X htbl)
    simp only [m8CpExclNames, List.mem_cons, List.not_mem_nil, or_false] at hexcl
    rcases hexcl with rfl | rfl | rfl | rfl
    · exact hnr (by simp [m8CoreParityReplRows])
    · exact hnr (by simp [m8cpRewireRows])
    · exact hnr (by simp [m8CoreParityReplRows])
    · exact hnr (by simp [m8cpRewireRows])

private theorem m8CoreParityEnvOf_of_specTable (H : M8BveHook) {f : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable (m8CoreParitySpecTableOf H) f as bs xs m Q X) :
    m8CoreParityEnvOf H f as bs xs m Q X := by
  refine m8CoreParityEnv_of_specTable_gen H m7FidSpecTable_sigs m7FidelityFns_names_nodup
    (fun _ _ _ _ _ _ _ ht => m7Fid_ofTable_to_env ht) (fun _ _ _ _ _ _ _ hb => hb)
    (m8cp_sig_exists_of_map m8cp_fid_idx_135) (m8cp_sig_exists_of_map m8cp_fid_idx_137)
    (m8cp_sig_exists_of_map m8cp_fid_idx_338) (m8cp_sig_exists_of_map m8cp_fid_idx_339)
    (m8cp_sig_exists_of_map m8cp_fid_idx_379) (m8cp_sig_exists_of_map m8cp_fid_idx_382)
    (m8cp_sig_exists_of_map m8cp_fid_idx_402) (m8cp_sig_exists_of_map m8cp_fid_idx_404)
    (m8cp_sig_exists_of_map m8cp_fid_idx_408) ?_ h
  have hnd := congrArg (List.map Prod.fst) m7FidSpecTable_sigs
  simp only [List.map_map, Function.comp_def, Fn.sig] at hnd
  change m7FidSpecTable.map SpecEntry.name = m7FidelityFns.map Fn.name at hnd
  rw [hnd]
  intro p hp b hb
  simp only [m8CoreParityBeforeRows, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact m8cp_min_help_not_in_m7Fid b hb
  · exact m8cp_bve_help_not_in_m7Fid H b hb

private def m8BveHelperRows : List SpecEntry :=
  [ ⟨"full_bve_find_equiv_m8", [i64, i32, i32], [.bool], m8BveFindEquivSpec, true⟩
  , ⟨"full_bve_find_and_m8", [i64, i32, i32, i32], [.bool], m8BveFindAndSpec, true⟩
  , ⟨"full_bve_match_tern_m8", [i64, i32, i32, i32, i32, i32], [i32], m8BveMatchTernSpec, true⟩
  , ⟨"full_bve_find_ite_side_m8", [i64, i32, i32, i32, .bool], [.bool],
      m8BveFindIteSideSpec, true⟩
  , ⟨"full_bve_find_ite_m8", [i64, i32, i32, i32], [.bool], m8BveFindIteSpec, true⟩
  , ⟨"full_bve_find_xor_m8", [i64, i32, i32, i32], [.bool], m8BveFindXorSpec, true⟩
  , ⟨"full_k6_watch_m8", [i64, i32, i32, i32, i32], [], m8K6WatchSpec, true⟩
  , ⟨"full_k6_assign_m8", [i64, i32, i32], [], m8K6AssignSpec, true⟩
  , ⟨"full_k6_mtf_m8", [i64, i32], [], m8K6MtfSpec, true⟩
  , ⟨"full_k6_backtrack_m8", [i64, i32], [], m8K6BacktrackSpec, true⟩
  , ⟨"full_k6_prop_m8", [i64], [i32], m8K6PropSpec, true⟩
  , ⟨"full_k6_ana_cl_m8", [i64, i32, i32], [], m8K6AnaClSpec, true⟩
  , ⟨"full_k6_analyze_m8", [i64, i32], [.bool], m8K6AnalyzeSpec, true⟩
  , ⟨"full_k6_solve_m8", [i64, i32], [i64], m8K6SolveSpec, true⟩
  , ⟨"full_k6_core_m8", [i64], [], m8K6CoreSpec, true⟩
  , ⟨"full_k6_extract_and_solve_m8", [i64, i32, i32, i32, .bool, i32], [.bool],
      m8K6ExtractSolveSpec, true⟩
  , ⟨"full_bve_def_k6_m8", [i64, i32, i32, i32], [], m8BveGatesSpec, true⟩
  , ⟨"full_bve_gates_m8", [i64, i32, i32, i32], [], m8BveGatesSpec, true⟩
  , ⟨"full_bve_bce_side_m8", [i64, i32, i32, i32, i32, i32], [], m8BveBceSideSpec, true⟩ ]

private theorem m8BveHelperRows_sigs :
    m8BveHelperRows.map (fun e => (e.name, e.as, e.rs)) = m8BveHelpers.map Fn.sig := by
  t_kernel_rfl

private theorem m8BveHelperRows_noExit : m8BveHelperRows.all SpecEntry.noExit = true := by
  t_kernel_rfl

private theorem m8BveHelperRows_nodup : (m8BveHelperRows.map SpecEntry.name).Nodup := by
  decide

private theorem m8cp_base_row {Γ : Env}
    (hBase : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      Γ f as bs xs m Q X)
    {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    (hnef : nm ∉ mfExclNames) (hncp : nm ∉ m8CpExclNames)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ a m Q X, sp a m Q X → Γ nm as bs a m Q X := fun a m Q X hs =>
  hBase nm as bs a m Q X hncp (M7FidelityEnv.base hnef (m7FidBase_row_mem hmem hno a m Q X hs))

private theorem m8cp_bveRow_base {Γ : Env}
    (hBase : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      Γ f as bs xs m Q X)
    (k : Nat) (hk : k < m7FidBveRows.length) {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (heq : m7FidBveRows[k] = ⟨nm, as, bs, sp, true⟩)
    (hnef : nm ∉ mfExclNames) (hncp : nm ∉ m8CpExclNames) :
    ∀ a m Q X, sp a m Q X → Γ nm as bs a m Q X :=
  m8cp_base_row hBase (m7FidBase_bve_mem _ (heq ▸ List.getElem_mem hk)) hnef hncp fun a m Q X hs =>
    by
      have hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBveClosedRows :=
        List.mem_append_left _ (heq ▸ List.getElem_mem hk)
      simpa only [SpecEntry.eff, ↓reduceIte] using
        mf_bve_noExit_spec ⟨nm, as, bs, sp, true⟩ hmem a m Q X hs

private theorem m8cp_bveH {Γ : Env}
    (hBveHelp : ∀ e ∈ m8BveHelperRows, ∀ xs m Q X,
      Env.ofTable m8BveHelperRows e.name e.as e.rs xs m Q X → Γ e.name e.as e.rs xs m Q X)
    (k : Nat) (hk : k < m8BveHelperRows.length) {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (heq : m8BveHelperRows[k] = ⟨nm, as, bs, sp, true⟩)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ a m Q X, sp a m Q X → Γ nm as bs a m Q X := fun a m Q X hs =>
  hBveHelp ⟨nm, as, bs, sp, true⟩ (heq ▸ List.getElem_mem hk) a m Q X
    (Env.ofTable_of_mem (heq ▸ List.getElem_mem hk) m8BveHelperRows_nodup (hno a m Q X hs))

private theorem m8cp_bve_helpers_impl (Γ : Env)
    (hBase : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      Γ f as bs xs m Q X)
    (hBveHelp : ∀ e ∈ m8BveHelperRows, ∀ xs m Q X,
      Env.ofTable m8BveHelperRows e.name e.as e.rs xs m Q X → Γ e.name e.as e.rs xs m Q X) :
    TableImpl Γ m8BveHelpers m8BveHelperRows := by
  have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
  have hTryBce := m8cp_base_row hBase
    (show (⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool],
      Full.fullBveTryBceSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable from
      m7FidP3Bve5_mem (i := 2) (by decide))
    (by decide) (by decide) (fun _ _ _ _ h => h)
  dsimp only [m8BveHelpers, m8BveHelperRows]
  exact ⟨ SpecEntry.Impl.of (full_bve_find_equiv_m8_wp Γ),
    SpecEntry.Impl.of (full_bve_find_and_m8_wp Γ),
    SpecEntry.Impl.of (full_bve_match_tern_m8_wp Γ),
    SpecEntry.Impl.of (full_bve_find_ite_side_m8_wp Γ
      (m8cp_bveRow_base hBase 15 (by decide) rfl (by decide) (by decide))
      (m8cp_bveH hBveHelp 2 (by decide) rfl m8BveMatchTernSpec_noExit)),
    SpecEntry.Impl.of (full_bve_find_ite_m8_wp Γ
      (m8cp_bveH hBveHelp 3 (by decide) rfl m8BveFindIteSideSpec_noExit)),
    SpecEntry.Impl.of (full_bve_find_xor_m8_wp Γ
      (m8cp_bveRow_base hBase 19 (by decide) rfl (by decide) (by decide))),
    SpecEntry.Impl.of (full_k6_watch_m8_wp Γ),
    SpecEntry.Impl.of (full_k6_assign_m8_wp Γ),
    SpecEntry.Impl.of (full_k6_mtf_m8_wp Γ),
    SpecEntry.Impl.of (full_k6_backtrack_m8_wp Γ),
    SpecEntry.Impl.of (full_k6_prop_m8_wp Γ
      (m8cp_bveH hBveHelp 7 (by decide) rfl m8K6AssignSpec_noExit)),
    SpecEntry.Impl.of (full_k6_ana_cl_m8_wp Γ),
    SpecEntry.Impl.of (full_k6_analyze_m8_wp Γ
      (m8cp_bveH hBveHelp 11 (by decide) rfl m8K6AnaClSpec_noExit)
      (m8cp_bveH hBveHelp 9 (by decide) rfl m8K6BacktrackSpec_noExit)
      (m8cp_bveH hBveHelp 8 (by decide) rfl m8K6MtfSpec_noExit)
      (m8cp_bveH hBveHelp 6 (by decide) rfl m8K6WatchSpec_noExit)
      (m8cp_bveH hBveHelp 7 (by decide) rfl m8K6AssignSpec_noExit)),
    SpecEntry.Impl.of (full_k6_solve_m8_wp Γ
      (m8cp_bveH hBveHelp 9 (by decide) rfl m8K6BacktrackSpec_noExit)
      (m8cp_bveH hBveHelp 7 (by decide) rfl m8K6AssignSpec_noExit)
      (m8cp_bveH hBveHelp 10 (by decide) rfl m8K6PropSpec_noExit)
      (m8cp_bveH hBveHelp 12 (by decide) rfl m8K6AnalyzeSpec_noExit)),
    SpecEntry.Impl.of (full_k6_core_m8_wp Γ),
    SpecEntry.Impl.of (full_k6_extract_and_solve_m8_wp Γ
      (m8cp_bveH hBveHelp 6 (by decide) rfl m8K6WatchSpec_noExit)
      (m8cp_bveH hBveHelp 13 (by decide) rfl m8K6SolveSpec_noExit)
      (m8cp_bveH hBveHelp 14 (by decide) rfl m8K6CoreSpec_noExit)),
    SpecEntry.Impl.of (full_bve_def_k6_m8_wp Γ
      (m8cp_bveH hBveHelp 15 (by decide) rfl m8K6ExtractSolveSpec_noExit)),
    SpecEntry.Impl.of (full_bve_gates_m8_wp Γ
      (m8cp_bveH hBveHelp 0 (by decide) rfl m8BveFindEquivSpec_noExit)
      (m8cp_bveH hBveHelp 1 (by decide) rfl m8BveFindAndSpec_noExit)
      (m8cp_bveH hBveHelp 4 (by decide) rfl m8BveFindIteSpec_noExit)
      (m8cp_bveH hBveHelp 5 (by decide) rfl m8BveFindXorSpec_noExit)
      (m8cp_bveH hBveHelp 16 (by decide) rfl m8BveGatesSpec_noExit)),
    SpecEntry.Impl.of (full_bve_bce_side_m8_wp Γ hTryBce
      (m8cp_base_row hBase hc2.extendPush2 (by decide) (by decide) (fun _ _ _ _ h => h))
      (m8cp_base_row hBase hc2.deleteBinary (by decide) (by decide) (fun _ _ _ _ h => h))
      (m8cp_base_row hBase hc2.extendPushCl (by decide) (by decide) (fun _ _ _ _ h => h))),
    trivial ⟩

private def m8BveHook : M8BveHook :=
  { helperRows := m8BveHelperRows
  , helperRows_sigs := m8BveHelperRows_sigs
  , helperRows_noExit := m8BveHelperRows_noExit
  , varKeySpec := m8BveVarKeySpec
  , varKey_noExit := by
      rintro ⟨hp, v, ⟨⟩⟩ m Q X X' h
      obtain ⟨c, s, R, rfl, hlen, hm, hQ⟩ := m8BveVarKeySpec_elim h
      exact m8BveVarKeySpec_intro rfl hlen hm hQ
  , heapPushSpec := m8BveHeapPushSpec
  , heapPush_noExit := by
      rintro ⟨hp, hlen, v, ⟨⟩⟩ m Q X X' h
      obtain ⟨c, s, R, rfl, hl, hm, hQ⟩ := m8BveHeapPushSpec_elim h
      exact m8BveHeapPushSpec_intro rfl hl hm hQ
  , helpers_impl := m8cp_bve_helpers_impl
  , varM7_wp := fun Γ hBase hBveHelp xs m Q X hs => by
      have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
      have hExtNeed := m8cp_base_row hBase
        (show (⟨"full_bve_ext_need", [i64, i32, i32], [i64],
          Full.fullBveExtNeedSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable from
          m7FidP3Bve5_mem (i := 4) (by decide))
        (by decide) (by decide) (fun _ _ _ _ h => h)
      have hWeaken := m8cp_base_row hBase
        (show (⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool],
          FullFastBveBudgets.fullBveWeakenTmkSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable from
          m7FidP3Bve5_mem (i := 1) (by decide))
        (by decide) (by decide) (fun _ _ _ _ h => h)
      have hResPair := m8cp_base_row hBase
        (show (⟨"full_bve_resolve_pair", [i64, i32, i32, i32], [.bool],
          Full.fullBveResolvePairSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable from
          m7FidP3Bve5_mem (i := 0) (by decide))
        (by decide) (by decide) (fun _ _ _ _ h => h)
      have hCommit := m8cp_base_row hBase
        (show (⟨"full_bve_commit_res", [i64, i64, i64], [i64],
          FullFastBveBudgets.fullBveCommitResTmkSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable from
          m7FidP3Bve5_mem (i := 3) (by decide))
        (by decide) (by decide) (fun _ _ _ _ h => h)
      exact full_bve_var_m7_m8_wp Γ
        (m8cp_bveRow_base hBase 9 (by decide) rfl (by decide) (by decide))
        hExtNeed hWeaken
        (m8cp_base_row hBase hc2.setInactive (by decide) (by decide) (fun _ _ _ _ h => h))
        (m8cp_bveH hBveHelp 17 (by decide) rfl m8BveGatesSpec_noExit)
        (m8cp_bveRow_base hBase 31 (by decide) rfl (by decide) (by decide))
        hResPair
        (m8cp_base_row hBase (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.wstackDefrag)
          (by decide) (by decide) (fun _ _ _ _ h => h))
        hCommit
        (m8cp_bveRow_base hBase 1 (by decide) rfl (by decide) (by decide))
        (m8cp_bveH hBveHelp 18 (by decide) rfl m8BveBceSideSpec_noExit)
        xs m Q X hs
  , var_wp := full_bve_var_m8_wp
  , varKey_wp := full_bve_var_key_m7_m8_wp
  , heapPush_wp := fun Γ hBase hKey xs m Q X hs =>
      full_bve_heap_push_m7_m8_wp Γ hKey
        (m8cp_bveRow_base hBase 35 (by decide) rfl (by decide) (by decide))
        (m8cp_bveRow_base hBase 36 (by decide) rfl (by decide) (by decide))
        xs m Q X hs
  , elimBve_wp := fun Γ hBase hPush xs m Q X hs =>
      full_elim_bve_fid_m8_wp Γ
        (m8cp_bveRow_base hBase 1 (by decide) rfl (by decide) (by decide))
        hPush
        (m8cp_bveRow_base hBase 38 (by decide) rfl (by decide) (by decide))
        (m8cp_bveRow_base hBase 39 (by decide) rfl (by decide) (by decide))
        (m8cp_bveRow_base hBase 32 (by decide) rfl (by decide) (by decide))
        xs m Q X hs }

/-! ## 3. Shared Non-Caller Lifting, `m8CoreParity_moduleOk`, Soundness & Tier-3b NV -/

private theorem m8cp_minHelper_impl {Γ : Env}
    (hBase : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      Γ f as bs xs m Q X)
    (hMinHelp : ∀ e ∈ m8MinHelperRows, ∀ xs m Q X,
      Env.ofTable m8MinHelperRows e.name e.as e.rs xs m Q X → Γ e.name e.as e.rs xs m Q X) :
    TableImpl Γ m8MinHelpers m8MinHelperRows := by
  have hMm : ∀ a m Q X, Full.fullMinMarkSpec a m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] a m Q X := fun a m Q X hs =>
    hBase "full_min_mark" [i64, i32, i8] [] a m Q X (by decide)
      (mf_extra_at 5 "full_min_mark" [i64, i32, i8] [] Full.fullMinMarkSpec rfl
        (fun _ _ _ _ h => h) a m Q X hs)
  have hDfs : ∀ a m Q X, m8MinLitDfsSpec a m Q X →
      Γ "full_min_lit_dfs_m8" [i64, i32, .bool, .bool] [.bool] a m Q X := fun a m Q X hs =>
    hMinHelp _ List.mem_cons_self a m Q X
      (Env.ofTable_of_mem (e := m8MinHelperRows[0]'(by decide)) List.mem_cons_self
        m8MinHelperRows_nodup (m8MinLitDfsSpec_monoX hs))
  have hSl : ∀ a m Q X, m8ShrinkLowerSpec a m Q X →
      Γ "full_shrink_lower_m8" [i64, i32, i32] [.bool] a m Q X := fun a m Q X hs =>
    hMinHelp _ (List.mem_cons_of_mem _ List.mem_cons_self) a m Q X
      (Env.ofTable_of_mem (e := m8MinHelperRows[1]'(by decide))
        (List.mem_cons_of_mem _ List.mem_cons_self)
        m8MinHelperRows_nodup (m8ShrinkLowerSpec_monoX hs))
  exact ⟨SpecEntry.Impl.of (full_min_lit_dfs_m8_wp Γ hMm),
    SpecEntry.Impl.of (full_shrink_lower_m8_wp Γ hMm hDfs),
    SpecEntry.Impl.of (full_shrink_blk_bool_m8_wp Γ hSl hMm), trivial⟩

private theorem m8cp_restoreBumpAnaM5_mem :
    (⟨"full_restore_bump_ana_m5", [i64], [], FullM5HeurCore.fullRestoreBumpAnaSpec, true⟩ :
      SpecEntry) ∈ m7FidBaseTable := by
  refine m7FidBase_part2_mem _ ?_
  unfold m7RowsPart2
  (iterate 16 apply List.mem_append_right)
  exact List.mem_append_left _ List.mem_cons_self

private theorem m8cp_elim_row {H : M8BveHook} {Γbase : Env} {nm : Sym} {as bs : List Ty}
    {sp : Spec as bs}
    (hBaseElim : ∀ {xs m Q X}, Γbase nm as bs xs m Q X → sp xs m Q (fun _ _ _ _ => False))
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h1 : nm ∉ m8MinHelperRows.map SpecEntry.name)
    (h2 : nm ∉ H.helperRows.map SpecEntry.name)
    (h3 : nm ≠ "full_min_shrink_m6") (h4 : nm ≠ "full_min_shrink")
    (h5 : nm ≠ "full_bve_var_key_m7") (h6 : nm ≠ "full_bve_heap_push_m7")
    (h : M8CoreParityEnv H Γbase nm as bs xs m Q X) :
    sp xs m Q (fun _ _ _ _ => False) := by
  cases h with
  | base _ hb => exact hBaseElim hb
  | minShrinkM6 => exact absurd rfl h3
  | minShrink => exact absurd rfl h4
  | varKey => exact absurd rfl h5
  | heapPush => exact absurd rfl h6
  | minHelp hm => exact absurd (m8CoreParity_ofTable_name_mem hm) h1
  | bveHelp hm => exact absurd (m8CoreParity_ofTable_name_mem hm) h2

private theorem m8cp_core_repl_wp (H : M8BveHook) {Γ : Env}
    (hBase : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      Γ f as bs xs m Q X)
    (hBveVarM7 : ∀ a m Q X, FullFastBveBudgets.fullBveVarDefSpec a m Q X →
      Γ "full_bve_var_m7" [i64, i32] [i64] a m Q X)
    (hMinHelp : ∀ e ∈ m8MinHelperRows, ∀ xs m Q X,
      Env.ofTable m8MinHelperRows e.name e.as e.rs xs m Q X → Γ e.name e.as e.rs xs m Q X)
    (hBveHelp : ∀ e ∈ H.helperRows, ∀ xs m Q X,
      Env.ofTable H.helperRows e.name e.as e.rs xs m Q X → Γ e.name e.as e.rs xs m Q X)
    (hMinElim : ∀ {xs m Q X}, Γ "full_min_shrink_m6" [i64] [] xs m Q X → m8MinShrinkSpec xs m Q X)
    (hVkElim : ∀ {xs m Q X},
      Γ "full_bve_var_key_m7" [i64, i32] [i64] xs m Q X → H.varKeySpec xs m Q X)
    (hBv7Elim : ∀ {xs m Q X}, Γ "full_bve_var_m7" [i64, i32] [i64] xs m Q X →
      FullFastBveBudgets.fullBveVarDefSpec xs m Q X)
    (hBvElim : ∀ {xs m Q X}, Γ "full_bve_var" [i64, i32] [i64] xs m Q X →
      FullFastBveBudgets.fullBveVarDefSpec xs m Q X)
    (hDtElim : ∀ {xs m Q X}, Γ "full_probe_dticks_m6_hdr" [i64, .bool] [i64] xs m Q X →
      FullM6Hdr.m6HdrW2aSpec [.bool] [i64] xs m Q X)
    (hPrElim : ∀ {xs m Q X}, Γ "full_probe_m6" [i64, .bool] [i64] xs m Q X →
      m6ProbeSpec xs m Q X)
    (hSrElim : ∀ {xs m Q X}, Γ "full_search_m6" [i64] [i64] xs m Q X →
      fullM6SearchSpec xs m Q X) :
    ∀ r ∈ m8CoreParityRepls, ∀ xs m Q X,
      Γ r.name r.as r.rs xs m Q X → Func.wp Γ r.body xs m Q X := by
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc1p := m7FidPart1PfxCallees_of_sub m7FidBase_part1_mem
  have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
  have hc2p := m7Part2PfxCallees_of_sub m7FidBase_part2_mem
  have hc3 := m7FidPart3Callees_of_sub m7FidBase_part3Pfx_mem
  have hc3p := m7FidPart3PfxCallees_of_sub m7FidBase_part3Pfx_mem
  have hBR : ∀ {f as bs sp}, (⟨f, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable →
      ∀ (hnmf : f ∉ mfExclNames) (hncp : f ∉ m8CpExclNames)
        (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)),
      ∀ a m Q X, sp a m Q X → Γ f as bs a m Q X := fun hm hnmf hncp hno a m Q X hs =>
    hBase _ _ _ a m Q X hncp (M7FidelityEnv.base hnmf (m7FidBase_row_mem hm hno a m Q X hs))
  intro r hr xs m Q X hsp
  simp only [m8CoreParityRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine full_min_shrink_m6_m8_wp Γ
      (fun a m Q X hs => hBase _ _ _ a m Q X (by decide)
        (mf_extra_at 10 "full_sort_tmp" [i64] [] FullM7AnalyzeSort.m7SortTmpSpec rfl
          (fun _ _ _ _ h => FullM7AnalyzeSort.m7SortTmpSpec_monoX h) a m Q X hs))
      (fun a m Q X hs => hBase _ _ _ a m Q X (by decide)
        (mf_extra_at 5 "full_min_mark" [i64, i32, i8] [] Full.fullMinMarkSpec rfl
          (fun _ _ _ _ h => h) a m Q X hs))
      (fun a m Q X hs => hMinHelp _ List.mem_cons_self a m Q X
        (Env.ofTable_of_mem (e := m8MinHelperRows[0]'(by decide)) List.mem_cons_self
          m8MinHelperRows_nodup (m8MinLitDfsSpec_monoX hs)))
      (fun a m Q X hs => hMinHelp _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          List.mem_cons_self)) a m Q X
        (Env.ofTable_of_mem (e := m8MinHelperRows[2]'(by decide))
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
          m8MinHelperRows_nodup (m8ShrinkBlkBoolSpec_monoX hs)))
      xs m Q X (hMinElim hsp)
  · exact H.varM7_wp Γ hBase hBveHelp xs m Q X (hBv7Elim hsp)
  · exact H.var_wp Γ hBveVarM7 xs m Q X (hBvElim hsp)
  · exact H.varKey_wp Γ xs m Q X (hVkElim hsp)
  · refine full_probe_dticks_m6_hdr_m8_wp Γ
      (hBR hc1.hdrGetWm (by decide) (by decide)
        (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h))
      xs m Q X (hDtElim hsp)
  · refine full_probe_m6_m8_wp Γ
      (hBR hc3p.probeDticks (by decide) (by decide)
        (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h))
      (hBR hc1.log10Q16M7 (by decide) (by decide)
        (fun _ _ _ _ h => FullM7Search.m7Log10Q16Spec_monoX h))
      (hBR hc1.scaleDeltaM5 (by decide) (by decide) (fun _ _ _ _ h => h))
      (hBR hc2p.vivifyM6Hdr (by decide) (by decide)
        (fun _ _ _ _ h => FullM6OrchAdapters.m6aVivifySpec_monoX h))
      (hBR hc2.enterDense (by decide) (by decide) (fun _ _ _ _ h => h))
      (hBR hc1p.delaying (by decide) (by decide)
        (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h))
      (hBR hc2p.congruenceDense (by decide) (by decide) (fun _ _ _ _ h => h))
      (hBR hc2.rebuildWatches (by decide) (by decide) (fun _ _ _ _ h => h))
      (hBR hc1.hdrSetWm (by decide) (by decide)
        (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h))
      (hBR hc1p.reduceDelay (by decide) (by decide)
        (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h))
      (hBR hc1p.bumpDelay (by decide) (by decide)
        (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h))
      (hBR m7FidBase_sweepDenseM6_mem (by decide) (by decide) (fun _ _ _ _ h => h))
      (hBR hc2p.substitute (by decide) (by decide) (fun _ _ _ _ h => h))
      (hBR m7FidBase_probeTailM6_mem (by decide) (by decide)
        (fun _ _ _ _ h => m6ProbeTailSpec_monoX h))
      (hBR hc2p.backboneM6 (by decide) (by decide) (fun _ _ _ _ h => h))
      (hBR m7FidP3MinU64_mem (by decide) (by decide) (fun _ _ _ _ h => h))
      (hBR m7FidP3Factor_mem (by decide) (by decide) (fun _ _ _ _ h => h))
      xs m Q X (hPrElim hsp)
  · refine full_search_m6_m8_wp Γ
      (hBR hc3.luckyLateM7 (by decide) (by decide)
        (fun _ _ _ _ h => FullM7Search.m7LuckyLateSpec_monoX h))
      (FullM7Proof.m7_fullPropagate_to_bcpS15
        (hBR hc1.propagate (by decide) (by decide) (fun _ _ _ _ h => h)))
      (hBR hc2.analyzeM6 (by decide) (by decide)
        (fun _ _ _ _ h => FullM6Hdr.m6HdrAnalyzeSpec_monoX h))
      (hBR (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.reduceM6) (by decide) (by decide)
        (fun _ _ _ _ h => m6ReduceSpec_monoX h))
      (hBR hc3.switchModeM7 (by decide) (by decide)
        (fun _ _ _ _ h => FullM7Search.m7SwitchModeSpec_monoX h))
      (hBR hc2.restartDue (by decide) (by decide) (fun _ _ _ _ h => h))
      (hBR hc2.restart (by decide) (by decide) (fun _ _ _ _ h => h))
      (hBR (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.reorderM6) (by decide) (by decide)
        (fun _ _ _ _ h => h))
      (hBR hc2.rephase (by decide) (by decide) (fun _ _ _ _ h => m7RephaseSpec_monoX h))
      (hBR (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.simplifyM6) (by decide) (by decide)
        (fun _ _ _ _ h => fullM6SimplifySpec_monoX h))
      (fun a m Q X hs => hBase _ _ _ a m Q X (by decide)
        (mf_extra_at 59 "m6_hdr_decide_fid" [i64] [i64] FullM6Hdr.m6HdrDecideSpec rfl
          (fun _ _ _ _ h => FullM6Hdr.m6HdrDecideSpec_monoX h) a m Q X hs))
      xs m Q X (hSrElim hsp)

private theorem m8cp_tableImpl_mem_wp {Γ : Env} {fs : List Fn} {rs : List SpecEntry}
    (ht : TableImpl Γ fs rs)
    (hLift : ∀ r ∈ rs, ∀ xs m Q X, Γ r.name r.as r.rs xs m Q X →
      r.cast (rfl : r.as = r.as) (rfl : r.rs = r.rs) xs m Q X) :
    ∀ f ∈ fs, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X := by
  induction fs generalizing rs with
  | nil => intro f hf; nomatch hf
  | cons f fs ih =>
    cases rs with
    | nil => exact False.elim ht
    | cons r rs =>
      obtain ⟨⟨⟨hnm, has, hrs⟩, hwp⟩, hrest⟩ := ht
      intro g hg xs m Q X hsp
      rcases List.mem_cons.mp hg with rfl | hmem
      · cases r with
        | mk rnm ras rrs rsp rnx =>
          dsimp only at hnm has hrs; subst hnm; subst has; subst hrs
          exact hwp xs m Q X (hLift _ List.mem_cons_self xs m Q X hsp)
      · exact ih hrest (fun x hx => hLift x (List.mem_cons_of_mem _ hx)) g hmem xs m Q X hsp

private def m8cpSkipNames : List Sym :=
  m8CoreParityRepls.map Fn.name ++
    ["full_min_shrink", "full_analyze", "full_analyze_core_m6",
     "full_bve_heap_push_m7", "full_elim_bve_m7"]

private theorem m8cp_m7Fid_noCallBad :
    PatchModule.checkNoCallBad m8cpSkipNames m8CpExclNames m7FidelityFns = true := by
  t_kernel_rfl

private theorem m8cp_not_mem_replNames_of_find_none {rFns : List Fn} {g : Fn}
    (hf : rFns.find? (·.name == g.name) = none) :
    g.name ∉ rFns.map Fn.name := by
  intro hmem
  rcases List.mem_map.mp hmem with ⟨r, hr, hnm⟩
  have hsome : (rFns.find? (·.name == g.name)).isSome = true :=
    List.find?_isSome.mpr ⟨r, hr, beq_iff_eq.mpr hnm⟩
  simp [hf] at hsome

private theorem m8cp_patch_moduleOk_of_noCallBad {Γbase Γ : Env} {M : LeanQbe.T.Module}
    (hM : ModuleOk Γbase M)
    {repls : List Fn} {befores : List (Sym × List Fn)}
    (hnd : ({ M with fns := PatchModule.patchFns repls befores M.fns } :
      LeanQbe.T.Module).namesNodup)
    (hCalls : ∀ pre fn post,
      ({ M with fns := PatchModule.patchFns repls befores M.fns } : LeanQbe.T.Module).fns =
        pre ++ fn :: post →
      fn.callsOk (pre.map Fn.sig ++ M.externs.map Extern.sig) M.exits)
    (hrWf : ∀ r ∈ repls, r.Wf) (hbWf : ∀ p ∈ befores, ∀ h ∈ p.2, h.Wf)
    {skipNames exclNames : List Sym}
    (hNoBad : PatchModule.checkNoCallBad skipNames exclNames M.fns = true)
    (hCallee : ∀ f as bs xs m Q X,
      f ∉ exclNames → Γbase f as bs xs m Q X → Γ f as bs xs m Q X)
    (hSkipWp : ∀ g ∈ M.fns, g.name ∈ skipNames → repls.find? (·.name == g.name) = none →
      ∀ xs m Q X, Γ g.name g.as g.rs xs m Q X → Func.wp Γ g.body xs m Q X)
    (hUntouchedPull : ∀ g ∈ M.fns, g.name ∉ skipNames →
      repls.find? (·.name == g.name) = none →
      ∀ xs m Q X, Γ g.name g.as g.rs xs m Q X → Γbase g.name g.as g.rs xs m Q X)
    (hrWp : ∀ r ∈ repls, ∀ xs m Q X, Γ r.name r.as r.rs xs m Q X → Func.wp Γ r.body xs m Q X)
    (hbWp : ∀ p ∈ befores, ∀ h ∈ p.2, ∀ xs m Q X,
      Γ h.name h.as h.rs xs m Q X → Func.wp Γ h.body xs m Q X) :
    ModuleOk Γ { M with fns := PatchModule.patchFns repls befores M.fns } := by
  have hwfOrig : ∀ f ∈ M.fns, f.Wf := fun f hf => by
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hf
    exact (hM.fnsOk pre f post hsplit).1
  have hwfAll := PatchModule.patchFns_wf hwfOrig hrWf
    (fun ins hins => let ⟨p, hp, hm⟩ := List.mem_flatMap.mp hins; hbWf p hp ins hm)
  have hmem_fn : ∀ {fn : Fn} {pre post : List Fn},
      ({ M with fns := PatchModule.patchFns repls befores M.fns } : LeanQbe.T.Module).fns =
        pre ++ fn :: post →
      fn ∈ PatchModule.patchFns repls befores M.fns := by
    intro fn pre post hsp
    change fn ∈ ({ M with fns := PatchModule.patchFns repls befores M.fns } : LeanQbe.T.Module).fns
    rw [hsp]; simp
  refine ⟨hnd, fun pre fn post hsplit =>
    ⟨hwfAll fn (hmem_fn hsplit), hCalls pre fn post hsplit, ?_⟩⟩
  rcases List.mem_flatMap.mp (hmem_fn hsplit) with ⟨g, hg, hmem_g⟩
  rcases List.mem_append.mp hmem_g with h_ins | h_rep
  · unfold PatchModule.patchInsAt at h_ins
    split at h_ins
    · rename_i tgt ins hfind
      exact hbWp (tgt, ins) (List.mem_of_find?_eq_some hfind) fn h_ins
    · nomatch h_ins
  · rcases List.mem_singleton.mp h_rep with rfl
    cases hr : repls.find? (·.name == g.name) with
    | some r => exact hrWp r (List.mem_of_find?_eq_some hr)
    | none =>
      by_cases hskip : g.name ∈ skipNames
      · exact hSkipWp g hg hskip hr
      · intro xs m Q X hsp
        obtain ⟨pre', post', hsplit'⟩ := List.append_of_mem hg
        have ⟨hwfG, hcallsG, hwpG⟩ := hM.fnsOk pre' g post' hsplit'
        have hcell : (skipNames.contains g.name || PatchModule.noCallInFn exclNames g) = true :=
          List.all_eq_true.mp hNoBad g hg
        have hno : PatchModule.noCallInFn exclNames g = true := by
          rcases Bool.or_eq_true _ _ |>.mp hcell with hc | hok
          · exact absurd (List.contains_iff_mem.mp hc) hskip
          · exact hok
        exact PatchModule.fn_wp_env_agree_of_noCallIn hwfG hcallsG hno
          (fun f as bs _ hne xs m P E hf => hCallee f as bs xs m P E hne hf)
          (hwpG xs m Q X (hUntouchedPull g hg hskip hr xs m Q X hsp))

private theorem m8cp_analyzeM5_mem :
    (⟨"full_analyze", [i64], [i64], Full.fullAnalyzeSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable := by
  refine m7FidBase_part2_mem _ ?_
  unfold m7RowsPart2
  (iterate 17 apply List.mem_append_right)
  exact List.mem_append_left _ List.mem_cons_self

private theorem m8cp_hasTernary_mem :
    (⟨"full_has_ternary", [i64, i32, i32, i32], [.bool], Full.fullHasTernarySpec, true⟩ :
      SpecEntry) ∈ m7FidBaseTable := by
  refine m7FidBase_part2_mem _ ?_
  unfold m7RowsPart2
  (iterate 52 apply List.mem_append_right)
  exact List.mem_append_left _ List.mem_cons_self

private theorem m8cp_ofTable_sig_elim {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup) {e : SpecEntry} (he : e ∈ tbl)
    {as bs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable tbl e.name as bs xs m Q X) :
    ∃ (has : e.as = as) (hrs : e.rs = bs), e.cast has hrs xs m Q X := by
  induction tbl with
  | nil => nomatch he
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp he with rfl | htl
    · dsimp only [Env.ofTable] at h
      rcases h with ⟨⟨_, has, hrs⟩, hcast⟩ | ⟨_, htl'⟩
      · exact ⟨has, hrs, hcast⟩
      · exact absurd (m8CoreParity_ofTable_name_mem htl')
          (by simpa [List.mem_map] using hnd.1)
    · have hne : hd.name ≠ e.name := fun hEq => hnd.1 ⟨e, htl, hEq.symm⟩
      rw [Env.ofTable_cons_ne hne] at h
      exact ih hnd.2 htl h

private theorem m8cp_helpers_disj_m7Fns :
    (m8MinHelperRows.map SpecEntry.name ++ m8BveHelpers.map Fn.name).all
      (fun nm => !((m7Fns.map Fn.name).contains nm)) = true := by
  t_kernel_rfl

private theorem m8cp_helpers_disj_mfExtra :
    (m8MinHelperRows.map SpecEntry.name ++ m8BveHelpers.map Fn.name).all
      (fun nm => !((mfExtraRows.map SpecEntry.name).contains nm)) = true := by
  t_kernel_rfl

private theorem m8cp_helpers_disj_minBve :
    (m8MinHelperRows.map SpecEntry.name).all
      (fun nm => !((m8BveHelpers.map Fn.name).contains nm)) = true := by
  decide

private theorem m8cp_help_not_in_m7FidEnv (H : M8BveHook) {nm : Sym}
    (hnm : nm ∈ m8MinHelperRows.map SpecEntry.name ∨ nm ∈ H.helperRows.map SpecEntry.name)
    {as bs xs m Q X} (hb : m7FidelityEnv nm as bs xs m Q X) : False := by
  have hmem : nm ∈ m8MinHelperRows.map SpecEntry.name ++ m8BveHelpers.map Fn.name := by
    rcases hnm with h1 | h2
    · exact List.mem_append_left _ h1
    · rw [m8cp_bveHelperRows_names_eq H] at h2
      exact List.mem_append_right _ h2
  cases hb with
  | base _ hb0 =>
    have htb : nm ∈ m7FidBaseTable.map SpecEntry.name := m8CoreParity_ofTable_name_mem hb0
    have hsg := congrArg (List.map Prod.fst) m7FidBaseTable_sigs
    simp only [List.map_map, Function.comp_def, Fn.sig] at hsg
    change nm ∈ m7FidBaseTable.map SpecEntry.name at htb
    rw [hsg] at htb
    have hchk := List.all_eq_true.mp m8cp_helpers_disj_m7Fns nm hmem
    simp only [Bool.not_eq_true'] at hchk
    exact absurd htb (by simpa using hchk)
  | extra he =>
    have hte := m8CoreParity_ofTable_name_mem he
    have hchk := List.all_eq_true.mp m8cp_helpers_disj_mfExtra nm hmem
    simp only [Bool.not_eq_true'] at hchk
    exact absurd hte (by simpa using hchk)

private theorem m8cp_help_not_in_minRows (H : M8BveHook) {e : SpecEntry}
    (he : e ∈ H.helperRows) : e.name ∉ m8MinHelperRows.map SpecEntry.name := by
  intro hm
  have h2 : e.name ∈ m8BveHelpers.map Fn.name := by
    rw [← m8cp_bveHelperRows_names_eq H]; exact List.mem_map_of_mem he
  have hchk := List.all_eq_true.mp m8cp_helpers_disj_minBve e.name hm
  simp only [Bool.not_eq_true'] at hchk
  exact absurd h2 (by simpa using hchk)

private theorem m8cp_minHelper_wp (H : M8BveHook) {Γbase : Env}
    (hNotBase : ∀ nm, (nm ∈ m8MinHelperRows.map SpecEntry.name ∨
        nm ∈ H.helperRows.map SpecEntry.name) →
      ∀ as bs xs m Q X, Γbase nm as bs xs m Q X → False)
    (hBase : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      M8CoreParityEnv H Γbase f as bs xs m Q X) :
    ∀ h ∈ m8MinHelpers, ∀ xs m Q X,
      M8CoreParityEnv H Γbase h.name h.as h.rs xs m Q X →
      Func.wp (M8CoreParityEnv H Γbase) h.body xs m Q X := by
  refine m8cp_tableImpl_mem_wp
    (m8cp_minHelper_impl hBase (fun _ _ _ _ _ _ hm => .minHelp hm)) ?_
  intro r hr xs m Q X hs
  have hr_nm : r.name ∈ m8MinHelperRows.map SpecEntry.name := List.mem_map_of_mem hr
  have hdisj_bve : r.name ∉ H.helperRows.map SpecEntry.name := by
    intro hb
    rcases List.mem_map.mp hb with ⟨b, hb_mem, hb_eq⟩
    exact m8cp_help_not_in_minRows H hb_mem (hb_eq ▸ hr_nm)
  have hdisj_ex : r.name ∉ m8CpExclNames := by
    intro hex
    have hchk : (m8MinHelperRows.map SpecEntry.name).all
        (fun s => !m8CpExclNames.contains s) = true := by decide
    have := List.all_eq_true.mp hchk r.name hr_nm
    simp only [Bool.not_eq_true'] at this
    exact absurd hex (by simpa using this)
  rcases m8CoreParityEnv_cases hs with ⟨_, hb⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ |
      hm | hm
  · exact False.elim (hNotBase r.name (Or.inl hr_nm) _ _ _ _ _ _ hb)
  · exact False.elim (hdisj_ex (heq ▸ by decide))
  · exact False.elim (hdisj_ex (heq ▸ by decide))
  · exact False.elim (hdisj_ex (heq ▸ by decide))
  · exact False.elim (hdisj_ex (heq ▸ by decide))
  · obtain ⟨_, _, hcast⟩ := m8cp_ofTable_sig_elim m8MinHelperRows_nodup hr hm
    exact hcast
  · exact False.elim (hdisj_bve (m8CoreParity_ofTable_name_mem hm))

private theorem m8cp_bveHelper_wp (H : M8BveHook) {Γbase : Env}
    (hNotBase : ∀ nm, (nm ∈ m8MinHelperRows.map SpecEntry.name ∨
        nm ∈ H.helperRows.map SpecEntry.name) →
      ∀ as bs xs m Q X, Γbase nm as bs xs m Q X → False)
    (hBase : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      M8CoreParityEnv H Γbase f as bs xs m Q X) :
    ∀ h ∈ m8BveHelpers, ∀ xs m Q X,
      M8CoreParityEnv H Γbase h.name h.as h.rs xs m Q X →
      Func.wp (M8CoreParityEnv H Γbase) h.body xs m Q X := by
  refine m8cp_tableImpl_mem_wp
    (H.helpers_impl (M8CoreParityEnv H Γbase) hBase (fun _ _ _ _ _ _ hm => .bveHelp hm)) ?_
  intro r hr xs m Q X hs
  have hr_nm : r.name ∈ H.helperRows.map SpecEntry.name := List.mem_map_of_mem hr
  have hr_bve : r.name ∈ m8BveHelpers.map Fn.name := by
    rw [← m8cp_bveHelperRows_names_eq H]; exact hr_nm
  have hdisj_min : r.name ∉ m8MinHelperRows.map SpecEntry.name := by
    intro hm; exact absurd hm (m8cp_help_not_in_minRows H hr)
  have hdisj_ex : r.name ∉ m8CpExclNames := by
    intro hex
    have hchk : (m8BveHelpers.map Fn.name).all (fun s => !m8CpExclNames.contains s) = true := by
      decide
    have := List.all_eq_true.mp hchk r.name hr_bve
    simp only [Bool.not_eq_true'] at this
    exact absurd hex (by simpa using this)
  rcases m8CoreParityEnv_cases hs with ⟨_, hb⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ |
      hm | hm
  · exact False.elim (hNotBase r.name (Or.inr hr_nm) _ _ _ _ _ _ hb)
  · exact False.elim (hdisj_ex (heq ▸ by decide))
  · exact False.elim (hdisj_ex (heq ▸ by decide))
  · exact False.elim (hdisj_ex (heq ▸ by decide))
  · exact False.elim (hdisj_ex (heq ▸ by decide))
  · exact False.elim (hdisj_min (m8CoreParity_ofTable_name_mem hm))
  · obtain ⟨_, _, hcast⟩ := m8cp_ofTable_sig_elim (m8cp_bveHelperRows_nodup H) hr hm
    exact hcast

private theorem m8cp_m7FidBase_elim {H : M8BveHook} {Γbase : Env} {nm : Sym}
    {as bs : List Ty} {sp : Spec as bs}
    (hBaseToM7 : ∀ {xs m Q X}, Γbase nm as bs xs m Q X → m7FidelityEnv nm as bs xs m Q X)
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    (hneEx : nm ∉ mfExtraRows.map SpecEntry.name := by decide)
    (h1 : nm ∉ m8MinHelperRows.map SpecEntry.name := by decide)
    (h2 : nm ∉ m8BveHelpers.map Fn.name)
    (h3 : nm ≠ "full_min_shrink_m6" := by decide) (h4 : nm ≠ "full_min_shrink" := by decide)
    (h5 : nm ≠ "full_bve_var_key_m7" := by decide)
    (h6 : nm ≠ "full_bve_heap_push_m7" := by decide)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : M8CoreParityEnv H Γbase nm as bs xs m Q X) :
    sp xs m Q (fun _ _ _ _ => False) := by
  have h2' : nm ∉ H.helperRows.map SpecEntry.name := by
    rw [m8cp_bveHelperRows_names_eq H]; exact h2
  refine m8cp_elim_row (H := H) (Γbase := Γbase) (fun hb => ?_) h1 h2' h3 h4 h5 h6 h
  cases hBaseToM7 hb with
  | base _ hb0 => exact m7FidBase_elim_of_mem hmem hb0
  | extra he => exact absurd (mf_ofTable_name_mem he) hneEx

private theorem m8cp_minShrink_elim {H : M8BveHook} {Γbase : Env} {xs m Q X}
    (h : M8CoreParityEnv H Γbase "full_min_shrink" [i64] [] xs m Q X) :
    m8MinShrinkSpec xs m Q X := by
  rcases m8CoreParityEnv_cases h with ⟨hne, _⟩ | ⟨hc, _⟩ | ⟨_, ha, hb, hs⟩ | ⟨hc, _⟩ |
      ⟨hc, _⟩ | hm | hm
  · exact absurd (by decide : "full_min_shrink" ∈ m8CpExclNames) hne
  · exact absurd hc (by decide)
  · cases ha; cases hb; exact hs
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd (m8CoreParity_ofTable_name_mem hm) (by decide)
  · have h2 : ("full_min_shrink" : Sym) ∈ m8BveHelpers.map Fn.name := by
      rw [← m8cp_bveHelperRows_names_eq H]; exact m8CoreParity_ofTable_name_mem hm
    exact absurd h2 (by decide)

private theorem m8cp_minShrinkM6_elim {H : M8BveHook} {Γbase : Env} {xs m Q X}
    (h : M8CoreParityEnv H Γbase "full_min_shrink_m6" [i64] [] xs m Q X) :
    m8MinShrinkSpec xs m Q X := by
  rcases m8CoreParityEnv_cases h with ⟨hne, _⟩ | ⟨_, ha, hb, hs⟩ | ⟨hc, _⟩ | ⟨hc, _⟩ |
      ⟨hc, _⟩ | hm | hm
  · exact absurd (by decide : "full_min_shrink_m6" ∈ m8CpExclNames) hne
  · cases ha; cases hb; exact hs
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd (m8CoreParity_ofTable_name_mem hm) (by decide)
  · have h2 : ("full_min_shrink_m6" : Sym) ∈ m8BveHelpers.map Fn.name := by
      rw [← m8cp_bveHelperRows_names_eq H]; exact m8CoreParity_ofTable_name_mem hm
    exact absurd h2 (by decide)

private theorem m8cp_varKey_elim {H : M8BveHook} {Γbase : Env} {xs m Q X}
    (h : M8CoreParityEnv H Γbase "full_bve_var_key_m7" [i64, i32] [i64] xs m Q X) :
    H.varKeySpec xs m Q X := by
  rcases m8CoreParityEnv_cases h with ⟨hne, _⟩ | ⟨hc, _⟩ | ⟨hc, _⟩ | ⟨_, ha, hb, hs⟩ |
      ⟨hc, _⟩ | hm | hm
  · exact absurd (by decide : "full_bve_var_key_m7" ∈ m8CpExclNames) hne
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · cases ha; cases hb; exact hs
  · exact absurd hc (by decide)
  · exact absurd (m8CoreParity_ofTable_name_mem hm) (by decide)
  · have h2 : ("full_bve_var_key_m7" : Sym) ∈ m8BveHelpers.map Fn.name := by
      rw [← m8cp_bveHelperRows_names_eq H]; exact m8CoreParity_ofTable_name_mem hm
    exact absurd h2 (by decide)

private theorem m8cp_heapPush_elim {H : M8BveHook} {Γbase : Env} {xs m Q X}
    (h : M8CoreParityEnv H Γbase "full_bve_heap_push_m7" [i64, i64, i32] [i64] xs m Q X) :
    H.heapPushSpec xs m Q X := by
  rcases m8CoreParityEnv_cases h with ⟨hne, _⟩ | ⟨hc, _⟩ | ⟨hc, _⟩ | ⟨hc, _⟩ |
      ⟨_, ha, hb, hs⟩ | hm | hm
  · exact absurd (by decide : "full_bve_heap_push_m7" ∈ m8CpExclNames) hne
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · cases ha; cases hb; exact hs
  · exact absurd (m8CoreParity_ofTable_name_mem hm) (by decide)
  · have h2 : ("full_bve_heap_push_m7" : Sym) ∈ m8BveHelpers.map Fn.name := by
      rw [← m8cp_bveHelperRows_names_eq H]; exact m8CoreParity_ofTable_name_mem hm
    exact absurd h2 (by decide)

private theorem m8cp_untouched_pull {H : M8BveHook} {Γbase : Env} {fs : List Fn} {rFns : List Fn}
    (hNotHelp : ∀ g ∈ fs,
      g.name ∉ m8MinHelperRows.map SpecEntry.name ∧ g.name ∉ H.helperRows.map SpecEntry.name)
    {g : Fn} (hg : g ∈ fs) (hskip : g.name ∉ m8cpSkipNames)
    (hr : rFns.find? (·.name == g.name) = none)
    (hMin6Mem : ("full_min_shrink_m6" : Sym) ∈ rFns.map Fn.name)
    (hVarKeyMem : ("full_bve_var_key_m7" : Sym) ∈ rFns.map Fn.name)
    {xs m Q X} (hsp : M8CoreParityEnv H Γbase g.name g.as g.rs xs m Q X) :
    Γbase g.name g.as g.rs xs m Q X := by
  rcases m8CoreParityEnv_cases hsp with ⟨_, hb⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ |
      hm | hm
  · exact hb
  · exact False.elim (m8cp_not_mem_replNames_of_find_none hr (heq ▸ hMin6Mem))
  · exact False.elim (hskip (heq ▸ by decide))
  · exact False.elim (m8cp_not_mem_replNames_of_find_none hr (heq ▸ hVarKeyMem))
  · exact False.elim (hskip (heq ▸ by decide))
  · exact False.elim ((hNotHelp g hg).1 (m8CoreParity_ofTable_name_mem hm))
  · exact False.elim ((hNotHelp g hg).2 (m8CoreParity_ofTable_name_mem hm))

private theorem m8cp_m7Fid_not_help (H : M8BveHook) :
    ∀ g ∈ m7FidelityFns,
      g.name ∉ m8MinHelperRows.map SpecEntry.name ∧ g.name ∉ H.helperRows.map SpecEntry.name := by
  intro g hg
  have hgn : g.name ∈ m7FidelityFns.map Fn.name := List.mem_map_of_mem hg
  refine ⟨fun hm => ?_, fun hb => ?_⟩
  · rcases List.mem_map.mp hm with ⟨e, he, hnm⟩
    exact m8cp_min_help_not_in_m7Fid e he (hnm ▸ hgn)
  · rcases List.mem_map.mp hb with ⟨e, he, hnm⟩
    exact m8cp_bve_help_not_in_m7Fid H e he (hnm ▸ hgn)

private theorem m8cp_m7Base_elim_inst (H : M8BveHook) {Γbase : Env} {nm : Sym}
    {as bs : List Ty} {sp : Spec as bs}
    (hBaseToM7 : ∀ f as bs xs m Q X,
      f ∈ ["full_bve_var_m7", "full_bve_var", "full_probe_dticks_m6_hdr",
        "full_probe_m6", "full_search_m6"] →
      Γbase f as bs xs m Q X → m7FidelityEnv f as bs xs m Q X)
    (hnmMem : nm ∈ ["full_bve_var_m7", "full_bve_var", "full_probe_dticks_m6_hdr",
      "full_probe_m6", "full_search_m6"])
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    (hmono : ∀ xs m Q X X', sp xs m Q X → sp xs m Q X')
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : M8CoreParityEnv H Γbase nm as bs xs m Q X)
    (hneEx : nm ∉ mfExtraRows.map SpecEntry.name := by decide)
    (h1 : nm ∉ m8MinHelperRows.map SpecEntry.name := by decide)
    (h2 : nm ∉ m8BveHelpers.map Fn.name := by decide)
    (h3 : nm ≠ "full_min_shrink_m6" := by decide) (h4 : nm ≠ "full_min_shrink" := by decide)
    (h5 : nm ≠ "full_bve_var_key_m7" := by decide)
    (h6 : nm ≠ "full_bve_heap_push_m7" := by decide) : sp xs m Q X :=
  hmono xs m Q _ X (m8cp_m7FidBase_elim (fun hb => hBaseToM7 nm as bs _ _ _ _ hnmMem hb)
    hmem hneEx h1 h2 h3 h4 h5 h6 h)

private theorem m8cp_common_repl_wp (H : M8BveHook) {Γbase : Env}
    (hBase : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      M8CoreParityEnv H Γbase f as bs xs m Q X)
    (hBaseToM7 : ∀ f as bs xs m Q X,
      f ∈ ["full_bve_var_m7", "full_bve_var", "full_probe_dticks_m6_hdr",
        "full_probe_m6", "full_search_m6"] →
      Γbase f as bs xs m Q X → m7FidelityEnv f as bs xs m Q X) :
    ∀ r ∈ m8CoreParityRepls, ∀ xs m Q X,
      M8CoreParityEnv H Γbase r.name r.as r.rs xs m Q X →
      Func.wp (M8CoreParityEnv H Γbase) r.body xs m Q X := by
  have hc3p := m7FidPart3PfxCallees_of_sub m7FidBase_part3Pfx_mem
  refine m8cp_core_repl_wp H hBase
    (fun a m Q X hs => hBase _ _ _ a m Q X (by decide)
      (M7FidelityEnv.base (by decide)
        (m7FidBase_row_mem m7FidBase_bveVar_mem (fun _ _ _ _ h => h) _ _ _ _ hs)))
    (fun _ _ _ _ _ _ hm => .minHelp hm) (fun _ _ _ _ _ _ hm => .bveHelp hm)
    m8cp_minShrinkM6_elim m8cp_varKey_elim
    (fun hsp => m8cp_m7Base_elim_inst H hBaseToM7 (by decide) m7FidBase_bveVar_mem
      (fun _ _ _ _ _ h => h) hsp)
    (fun hsp => m8cp_m7Base_elim_inst H hBaseToM7 (by decide)
      (m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 33) rfl))
      (fun _ _ _ _ _ h => h) hsp)
    (fun hsp => m8cp_m7Base_elim_inst H hBaseToM7 (by decide) hc3p.probeDticks
      (fun _ _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h) hsp)
    (fun hsp => m8cp_m7Base_elim_inst H hBaseToM7 (by decide) m7FidBase_probeM6_mem
      (fun _ _ _ _ _ h => FullM6Orch.m6ProbeSpec_monoX h) hsp)
    (fun hsp => m8cp_m7Base_elim_inst H hBaseToM7 (by decide) m7FidBase_searchM6_mem
      (fun _ _ _ _ _ h => fullM6SearchSpec_monoX h) hsp)

private theorem m8cp_common_skip_wp (H : M8BveHook) {Γbase : Env}
    (hBase : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      M8CoreParityEnv H Γbase f as bs xs m Q X)
    (hAnaToM7 : ∀ {xs m Q X}, Γbase "full_analyze_core_m6" [i64] [i64] xs m Q X →
      m7FidelityEnv "full_analyze_core_m6" [i64] [i64] xs m Q X)
    (hElimToM7 : ∀ {xs m Q X}, Γbase "full_elim_bve_m7" [i64, i64] [i64] xs m Q X →
      m7FidelityEnv "full_elim_bve_m7" [i64, i64] [i64] xs m Q X)
    {g : Fn} (hnm : g.name = "full_min_shrink" ∨ g.name = "full_analyze_core_m6" ∨
      g.name = "full_bve_heap_push_m7" ∨ g.name = "full_elim_bve_m7")
    (hMinEq : g.name = "full_min_shrink" → g = m6oMinShrinkFn)
    (coreBody : Func [i64] [i64])
    (hCoreEq : g.name = "full_analyze_core_m6" →
      g = ⟨"full_analyze_core_m6", [i64], [i64], coreBody⟩)
    (hCoreWp : ∀ xs m Q X, FullM6Hdr.m6HdrAnalyzeSpec xs m Q X →
      Func.wp (M8CoreParityEnv H Γbase) coreBody xs m Q X)
    (hPushEq : g.name = "full_bve_heap_push_m7" →
      g = ⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64],
        FullM7BveGates.full_bve_heap_push_m7_body⟩)
    (hElimEq : g.name = "full_elim_bve_m7" → g = FullM7FidelityCore.fidElimBveM7Fn) :
    ∀ xs m Q X, M8CoreParityEnv H Γbase g.name g.as g.rs xs m Q X →
      Func.wp (M8CoreParityEnv H Γbase) g.body xs m Q X := by
  rcases hnm with h1 | h2 | h3 | h4
  · obtain rfl := hMinEq h1
    exact fun xs m Q X hsp =>
      full_min_shrink_m8_wp (M8CoreParityEnv H Γbase) (fun _ _ _ _ hs => .minShrinkM6 hs)
        xs m Q X (m8cp_minShrink_elim hsp)
  · obtain rfl := hCoreEq h2
    exact fun xs m Q X hsp =>
      hCoreWp xs m Q X (FullM6Hdr.m6HdrAnalyzeSpec_monoX (m8cp_m7FidBase_elim hAnaToM7
        (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.analyzeCoreM6)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp))
  · obtain rfl := hPushEq h3
    exact fun xs m Q X hsp =>
      H.heapPush_wp (M8CoreParityEnv H Γbase) hBase (fun _ _ _ _ hs => .varKey hs)
        xs m Q X (m8cp_heapPush_elim hsp)
  · obtain rfl := hElimEq h4
    exact fun xs m Q X hsp =>
      H.elimBve_wp (M8CoreParityEnv H Γbase) hBase (fun _ _ _ _ hs => .heapPush hs)
        xs m Q X (m8cp_m7FidBase_elim hElimToM7 m7FidBase_elimBveM7_mem
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp)

private theorem m8cp_solve_bytes_sound_of {Γ : Env} {M : LeanQbe.T.Module}
    (hM : ModuleOk Γ M) (hMem : m6oSolveBytesFn ∈ M.fns)
    (hSb : ∀ a m Q X, m7FidSolveBytesSpec a m Q X →
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
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hMem
  have hfn := (hM.fnsOk pre _ post hsplit).2.2
  refine hfn _ m _ (fun _ _ _ _ => False)
    (hSb _ m _ _ (m7FidSolveBytesSpec_intro hcfit hwfit hm ?_))
  intro r m' hdom h20 _ hm'
  exact ⟨hdom, h20, hm'⟩

private theorem m8cp_unsat_nv_of {Γ : Env} {M : LeanQbe.T.Module}
    (hM : ModuleOk Γ M) (hMem : m6oSolveBytesFn ∈ M.fns)
    (hSb : ∀ a m Q X, m7FidSolveBytesSpec a m Q X →
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
  have hm0 :
      (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen ⋆ emp)
        nvM6UnsatInitMem := by
    rw [Std.ExtHashMap.sep_emp]
    exact nvM6UnsatInitMem_sep
  refine hfn _ nvM6UnsatInitMem _ (fun _ _ _ _ => False)
    (hSb _ nvM6UnsatInitMem _ _ (m7FidSolveBytesSpec_intro (by decide) (by decide) hm0 ?_))
  intro r m' _ _ htr hm'
  have hr20 := htr 1 2 9 (by decide) (by decide) (by decide) nvM6_unsat_bound (by decide)
    nvM6Unsat_header nvM6Unsat_unitTrace
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨hr20, nvM6UnsatCnf_unsat, hm'⟩

private theorem m8cp_m7Fid_fn_149 :
    m7FidelityFns[149]? = some
      ⟨"full_analyze", [i64], [i64], FullM5HeurCore.full_analyze_m5_body⟩ := by
  t_kernel_rfl

private theorem m8cp_m7Fid_fn_137 : m7FidelityFns[137]? = some m6oMinShrinkFn := by
  t_kernel_rfl

private theorem m8cp_m7Fid_fn_150 : m7FidelityFns[150]? = some m6oAnalyzeCoreM6Fn := by
  t_kernel_rfl

private theorem m8cp_m7Fid_fn_382 :
    m7FidelityFns[382]? = some
      ⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64],
        FullM7BveGates.full_bve_heap_push_m7_body⟩ := by
  t_kernel_rfl

private theorem m8cp_m7Fid_fn_385 :
    m7FidelityFns[385]? = some FullM7FidelityCore.fidElimBveM7Fn := by
  t_kernel_rfl

private theorem m8CoreParityOf_moduleOk (H : M8BveHook) :
    ModuleOk (m8CoreParityEnvOf H) m8CoreParityModule := by
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc2p := m7Part2PfxCallees_of_sub m7FidBase_part2_mem
  have hBase : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      m8CoreParityEnvOf H f as bs xs m Q X := fun _ _ _ _ _ _ _ hne h => .base hne h
  have hchk := m8CoreParity_acyclic
  simp only [LeanQbe.T.Module.checkAcyclic, Bool.and_eq_true] at hchk
  have hnd : m8CoreParityModule.namesNodup :=
    LeanQbe.T.Module.namesNodup_of_checkNamesNodup hchk.1
  have hCalls : ∀ pre fn post, m8CoreParityModule.fns = pre ++ fn :: post →
      fn.callsOk (pre.map Fn.sig ++ m7FidelityModule.externs.map Extern.sig)
        m7FidelityModule.exits := fun pre fn post hs => by
    simpa [m8CoreParityModule] using LeanQbe.T.Module.checkFnsCallsOk_ok
      m8CoreParityModule.exits (m8CoreParityModule.externs.map Extern.sig)
      [] m8CoreParityModule.fns pre fn post hchk.2 hs
  have hmrg : m8CoreParityModule =
      { m7FidelityModule with
        fns := PatchModule.patchFns m8CoreParityRepls m8CoreParityBefores m7FidelityModule.fns } :=
    by dsimp only [m8CoreParityModule]; rw [m8CoreParityFns_eq_patchFns]; rfl
  rw [hmrg]
  rw [hmrg] at hnd hCalls
  have hCoreWp : ∀ xs m Q X, FullM6Hdr.m6HdrAnalyzeSpec xs m Q X →
      Func.wp (m8CoreParityEnvOf H) m6oAnalyzeCoreM6Fn.body xs m Q X :=
    fun xs m Q X hs => full_analyze_core_m6_m8_wp (m8CoreParityEnvOf H)
      (m8cp_base_row hBase hc2p.oneLitConfl (by decide) (by decide) (fun _ _ _ _ h => h))
      (m8cp_base_row hBase hc2p.anaFailedLit (by decide) (by decide)
        (fun _ _ _ _ h => FullM6OrchAdapters.m6aAnaFailedLitSpec_monoX h))
      (m8cp_base_row hBase m7FidBase_deduce1uipM6Hdr_mem (by decide) (by decide)
        (fun _ _ _ _ h => m7Deduce1uipHdrSpec_monoX h))
      (m8cp_base_row hBase hc2p.restoreBumpAna (by decide) (by decide)
        (fun _ _ _ _ h => FullM6OrchAdapters.m6aRestoreBumpAnaSpec_monoX h))
      (fun _ _ _ _ h => .minShrinkM6 h)
      (m8cp_base_row hBase hc1.tickRel (by decide) (by decide) (fun _ _ _ _ h => h))
      (m8cp_base_row hBase hc1.emaUpdate (by decide) (by decide) (fun _ _ _ _ h => h))
      (m8cp_base_row hBase hc2p.learnClause (by decide) (by decide) (fun _ _ _ _ h => h))
      xs m Q X hs
  refine m8cp_patch_moduleOk_of_noCallBad m7Fidelity_moduleOk hnd hCalls
    m8CoreParityRepls_wf m8CoreParityBefores_wf m8cp_m7Fid_noCallBad
    hBase ?_ ?_ ?_ ?_
  · intro g hg hskip _hnone
    simp only [m8cpSkipNames, m8CoreParityRepls, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hskip
    rcases hskip with h | h | h | h | h | h | h | h | h | h | h | h
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone (by simp [m8CoreParityRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone (by simp [m8CoreParityRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone (by simp [m8CoreParityRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone (by simp [m8CoreParityRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone (by simp [m8CoreParityRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone (by simp [m8CoreParityRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone (by simp [m8CoreParityRepls, h]))
    · refine m8cp_common_skip_wp H hBase (fun h => h) (fun h => h) (Or.inl h)
        (fun hn => m8cp_nodup_name_eq Fn.name m7FidelityFns_names_nodup hg
          (List.mem_of_getElem? m8cp_m7Fid_fn_137) (hn.trans rfl))
        m6oAnalyzeCoreM6Fn.body (fun hn => absurd (h.symm.trans hn) (by decide)) hCoreWp
        (fun hn => absurd (h.symm.trans hn) (by decide))
        (fun hn => absurd (h.symm.trans hn) (by decide))
    · have hgeq : g = ⟨"full_analyze", [i64], [i64], FullM5HeurCore.full_analyze_m5_body⟩ :=
        m8cp_nodup_name_eq Fn.name m7FidelityFns_names_nodup hg
          (List.mem_of_getElem? m8cp_m7Fid_fn_149) (h.trans rfl)
      subst hgeq
      intro xs m Q X hsp
      have hs0 := m8cp_m7FidBase_elim (H := H) (Γbase := m7FidelityEnv) (fun hb => hb)
        m8cp_analyzeM5_mem (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hsp
      exact full_analyze_m5_m8_wp (m8CoreParityEnvOf H)
        (m8cp_base_row hBase hc2p.oneLitConfl (by decide) (by decide) (fun _ _ _ _ h => h))
        (m8cp_base_row hBase (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.deduce1uip)
          (by decide) (by decide) (fun _ _ _ _ h => h))
        (m8cp_base_row hBase m8cp_restoreBumpAnaM5_mem (by decide) (by decide) (fun _ _ _ _ h => h))
        (fun _ _ _ _ hs => .minShrink hs)
        (m8cp_base_row hBase hc1.tickRel (by decide) (by decide) (fun _ _ _ _ h => h))
        (m8cp_base_row hBase hc1.emaUpdate (by decide) (by decide) (fun _ _ _ _ h => h))
        (m8cp_base_row hBase hc2p.learnClause (by decide) (by decide) (fun _ _ _ _ h => h))
        xs m Q X hs0
    · refine m8cp_common_skip_wp H hBase (fun h => h) (fun h => h) (Or.inr (Or.inl h))
        (fun hn => absurd (h.symm.trans hn) (by decide))
        m6oAnalyzeCoreM6Fn.body
        (fun hn => m8cp_nodup_name_eq Fn.name m7FidelityFns_names_nodup hg
          (List.mem_of_getElem? m8cp_m7Fid_fn_150) (hn.trans rfl)) hCoreWp
        (fun hn => absurd (h.symm.trans hn) (by decide))
        (fun hn => absurd (h.symm.trans hn) (by decide))
    · refine m8cp_common_skip_wp H hBase (fun h => h) (fun h => h) (Or.inr (Or.inr (Or.inl h)))
        (fun hn => absurd (h.symm.trans hn) (by decide))
        m6oAnalyzeCoreM6Fn.body (fun hn => absurd (h.symm.trans hn) (by decide)) hCoreWp
        (fun hn => m8cp_nodup_name_eq Fn.name m7FidelityFns_names_nodup hg
          (List.mem_of_getElem? m8cp_m7Fid_fn_382) (hn.trans rfl))
        (fun hn => absurd (h.symm.trans hn) (by decide))
    · refine m8cp_common_skip_wp H hBase (fun h => h) (fun h => h) (Or.inr (Or.inr (Or.inr h)))
        (fun hn => absurd (h.symm.trans hn) (by decide))
        m6oAnalyzeCoreM6Fn.body (fun hn => absurd (h.symm.trans hn) (by decide)) hCoreWp
        (fun hn => absurd (h.symm.trans hn) (by decide))
        (fun hn => m8cp_nodup_name_eq Fn.name m7FidelityFns_names_nodup hg
          (List.mem_of_getElem? m8cp_m7Fid_fn_385) (hn.trans rfl))
  · intro g hg hskip hr xs m Q X hsp
    exact m8cp_untouched_pull (m8cp_m7Fid_not_help H) hg hskip hr (by decide) (by decide) hsp
  · exact m8cp_common_repl_wp H hBase (fun _ _ _ _ _ _ _ _ hb => hb)
  · intro p hp h hh xs m Q X hs
    simp only [m8CoreParityBefores, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact m8cp_minHelper_wp H
        (fun nm hnm _ _ _ _ _ _ hb => m8cp_help_not_in_m7FidEnv H hnm hb) hBase h hh xs m Q X hs
    · exact m8cp_bveHelper_wp H
        (fun nm hnm _ _ _ _ _ _ hb => m8cp_help_not_in_m7FidEnv H hnm hb) hBase h hh xs m Q X hs

private theorem m8cp_patchFns_mem_of_ne {repls fs : List Fn} {befores : List (Sym × List Fn)}
    {g : Fn} (hg : g ∈ fs) (hne : ∀ r ∈ repls, r.name ≠ g.name) :
    g ∈ PatchModule.patchFns repls befores fs := by
  induction fs with
  | nil => nomatch hg
  | cons f fs ih =>
    simp only [PatchModule.patchFns, List.flatMap_cons, List.mem_append, List.mem_singleton]
    rcases List.mem_cons.mp hg with rfl | hmem
    · refine Or.inl (Or.inr ?_)
      cases hfind : repls.find? (·.name == g.name) with
      | none => rfl
      | some r =>
        have hr := List.mem_of_find?_eq_some hfind
        have hnm := beq_iff_eq.mp (List.find?_some (p := fun x : Fn => x.name == g.name) hfind)
        exact absurd hnm (hne r hr)
    · exact Or.inr (ih hmem)

/-- Full `435`-row unconditional specification table for `FullM8CoreParity.m8CoreParityModule`. -/
def m8CoreParitySpecTable : List SpecEntry :=
  m8CoreParitySpecTableOf m8BveHook

theorem m8CoreParitySpecTable_sigs :
    m8CoreParitySpecTable.map (fun e => (e.name, e.as, e.rs)) = m8CoreParityFns.map Fn.sig :=
  m8CoreParitySpecTableOf_sigs m8BveHook

theorem m8CoreParitySpecTable_length : m8CoreParitySpecTable.length = 435 :=
  m8CoreParitySpecTableOf_length m8BveHook

theorem m8CoreParitySpecTable_noExit : m8CoreParitySpecTable.all SpecEntry.noExit = true :=
  m8CoreParitySpecTableOf_noExit m8BveHook

theorem m8CoreParitySpecTable_nodup : (m8CoreParitySpecTable.map SpecEntry.name).Nodup :=
  m8CoreParitySpecTableOf_nodup m8BveHook

/-- Canonical closed unconditional `Env` for `m8CoreParityModule` (`435` fns). -/
def m8CoreParityEnv : Env :=
  m8CoreParityEnvOf m8BveHook

theorem m8CoreParityEnv_noExit :
    ∀ f as bs xs m Q X X', m8CoreParityEnv f as bs xs m Q X → m8CoreParityEnv f as bs xs m Q X' :=
  m8CoreParityEnvOf_noExit m8BveHook

theorem m8CoreParityEnv_solve_bytes_iff {xs : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m8CoreParityEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X ↔
      m7FidSolveBytesSpec xs m Q (fun _ _ _ _ => False) :=
  m8CoreParityEnvOf_solve_bytes_iff m8BveHook

theorem m8CoreParityEnv_of_specTable {f : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable m8CoreParitySpecTable f as bs xs m Q X) :
    m8CoreParityEnv f as bs xs m Q X :=
  m8CoreParityEnvOf_of_specTable m8BveHook h

/-- Closed unconditional `435/435` `ModuleOk` certifying `FullM8CoreParity.m8CoreParityModule`
under `m8CoreParityEnv` (`0` sorry, UNSAT-only, all Rank #4/#5/#8 parity closures closed). -/
theorem m8CoreParity_moduleOk : ModuleOk m8CoreParityEnv m8CoreParityModule :=
  m8CoreParityOf_moduleOk m8BveHook

theorem m8CoreParity_tableImpl :
    TableImpl m8CoreParityEnv m8CoreParityModule.fns m8CoreParitySpecTable :=
  tableImpl_of_moduleOk m8CoreParity_moduleOk m8CoreParitySpecTable_sigs
    m8CoreParitySpecTable_nodup (fun _ _ _ _ _ _ ht => m8CoreParityEnv_of_specTable ht)

theorem m8CoreParity_solveBytes_mem : m6oSolveBytesFn ∈ m8CoreParityModule.fns := by
  change m6oSolveBytesFn ∈ m8CoreParityFns
  rw [m8CoreParityFns_eq_patchFns]
  exact m8cp_patchFns_mem_of_ne m7Fidelity_solveBytes_mem fun r hr => by
    simp only [m8CoreParityRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Top-level unconditional byte-level UNSAT soundness of `m8CoreParityModule` (`435` fns). -/
theorem m8CoreParity_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m8CoreParityEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m8cp_solve_bytes_sound_of m8CoreParity_moduleOk m8CoreParity_solveBytes_mem
    (fun _ _ _ _ hs => m8CoreParityEnv_solve_bytes_iff.mpr hs) hcfit hwfit hm

/-- Host-framed machine-memory UNSAT lift for `m8CoreParityModule`. -/
theorem m8CoreParity_solve_bytes_host_sound
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hpost :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hhost : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem :=
  m7Fidelity_solve_bytes_host_sound hpost hhost

/-- Concrete deterministic Tier-3b UNSAT non-vacuity (`r = 20#64`) for `m8CoreParityModule`. -/
theorem m8CoreParity_unsat_nv :
    Func.wp m8CoreParityEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m8cp_unsat_nv_of m8CoreParity_moduleOk m8CoreParity_solveBytes_mem
    (fun _ _ _ _ hs => m8CoreParityEnv_solve_bytes_iff.mpr hs)

theorem m8CoreParityEnv_minMark {a m Q X} (h : Full.fullMinMarkSpec a m Q X) :
    m8CoreParityEnv "full_min_mark" [i64, i32, i8] [] a m Q X :=
  .base (by decide)
    (mf_extra_at 5 "full_min_mark" [i64, i32, i8] [] Full.fullMinMarkSpec rfl
      (fun _ _ _ _ hs => hs) _ _ _ _ h)

theorem m8CoreParityEnv_getWatermark {a m Q X} (h : FullM6Hdr.m6HdrW2aSpec [i64] [i64] a m Q X) :
    m8CoreParityEnv "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X :=
  let hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  .base (by decide) (M7FidelityEnv.base (by decide)
    (m7FidBase_row_mem hc1.hdrGetWm
      (fun _ _ _ _ hs => FullM6Hdr.m6HdrW2aSpec_monoX hs) _ _ _ _ h))

theorem m8CoreParityEnv_minShrinkM6_wp :
    ∀ a m Q X, m8MinShrinkSpec a m Q X → Func.wp m8CoreParityEnv full_min_shrink_m6_body a m Q X :=
  fun a m Q X hs =>
    m8cp_common_repl_wp m8BveHook (fun _ _ _ _ _ _ _ hne h => .base hne h)
      (fun _ _ _ _ _ _ _ _ hb => hb) m8MinShrinkM6Fn List.mem_cons_self a m Q X (.minShrinkM6 hs)

theorem m8CoreParityEnv_probeDticks_wp :
    ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [.bool] [i64] a m Q X →
      Func.wp m8CoreParityEnv full_probe_dticks_m6_hdr_body a m Q X :=
  full_probe_dticks_m6_hdr_m8_wp m8CoreParityEnv (fun _ _ _ _ hs => m8CoreParityEnv_getWatermark hs)

end LeanQbe.T.Examples.Kissat.FullM8CoreParity

end
