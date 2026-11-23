/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7
public import LeanQbe.T.Examples.Kissat.FullM7BvaGuFix
public import LeanQbe.T.Examples.Kissat.FullM7CompactFix
public import LeanQbe.T.Examples.Kissat.FullM7BvaV5Fix
public import LeanQbe.T.Examples.Kissat.FullM7ParityVivTiers
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySched
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFix
public import LeanQbe.T.Examples.Kissat.FullM7FidelityCore
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySearch
public import LeanQbe.T.Examples.Kissat.FullM7Splice
meta import LeanQbe.T.Examples.Kissat.FullM7
meta import LeanQbe.T.Examples.Kissat.FullM7BvaGuFix
meta import LeanQbe.T.Examples.Kissat.FullM7CompactFix
meta import LeanQbe.T.Examples.Kissat.FullM7BvaV5Fix
meta import LeanQbe.T.Examples.Kissat.FullM7ParityVivTiers
meta import LeanQbe.T.Examples.Kissat.FullM7FidelitySched
meta import LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFix
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityCore
meta import LeanQbe.T.Examples.Kissat.FullM7FidelitySearch
meta import LeanQbe.T.Examples.Kissat.FullM7Splice
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Kissat Unified `M7Fidelity` (`FullM7Fidelity` / Upstream 4.0.4) Assembly (`413` Fns)

Assembles Target A (`m7FidelityModule`, `413` functions, `0` externs, `0` exits) over unchanged
`FullM7.m7Module` (`410` fns, `FullCfg`/`FullMem`, omitting `MemShrink` per Option A) via purely
additive `mfPatchFns` with `29` disjoint canonical replacements and `3` active inserted helpers:
1. `FullM7BvaGuFix` (`2` fns): `full_bva_commit`, `full_analyze_rsn`.
2. `FullM7CompactFix` (`4` fns): `full_compact_needed`, `full_compact_mark_live`,
   `full_compact_vars`, `full_sweep_copy`.
3. `FullM7BvaV5Fix` (`1` fn): `full_forward_sub` (directly called by `full_eliminate_fid2`).
4. `FullM7ParityVivTiers` (`5` fns): `m6_hdr_sync_legacy_tiers`, `full_propagate_ignore_hot`,
   `full_propagate_ignore`, `full_vivify_tier_m6_hdr`, `full_vivify_m6_hdr`.
5. `FullM7FidelitySched` (`2` fns): `full_ilog10`, `full_calc_max_v` (`full_nlogpown_fid` omitted
   as unused after `FullM7FidelitySchedFix` moved all schedules to continuous Q16 `log10`).
6. `FullM7FidelitySchedFix` (`5` fns): `full_reduce_m6`, `full_eliminate_m6`, `full_probe_tail_m6`,
   `full_probe_m6`, `full_preprocess_m6`.
7. `FullM7FidelityCore` (`7` repls + `2` leaf helpers): `full_min_shrink_m6`,
   `full_bva_scan_cands`, `full_bva_match_large_fid` before `full_bva_filter_row`,
   `full_reorder_sift_fid` before `full_reorder_queue_m7`, `full_reorder_m6`, `full_elim_bve_m7`,
   `full_walk_m7`.
8. `FullM7FidelitySearch` (`3` repls + `1` helper): `full_bump_analyzed_m6_hdr`,
   `full_switch_mode_m7`, `m6_hdr_decide_fid` before `full_search_m6`.

Certifies `m7FidelityFns_length` (`413`), `m7FidelityFns_names_nodup`, `m7FidelityFns_wf`,
fast `O(29 + 3)` `m7Fidelity_acyclic`, `m7Fidelity_noExit`, and compile-time `#guard` checks across
`PrintCpp`, `PrintQbe`, and all 4 ISAs.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7Fidelity

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7BvaGuFix
open LeanQbe.T.Examples.Kissat.FullM7CompactFix
open LeanQbe.T.Examples.Kissat.FullM7BvaV5Fix
open LeanQbe.T.Examples.Kissat.FullM7ParityVivTiers
open LeanQbe.T.Examples.Kissat.FullM7FidelitySched
open LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFix
open LeanQbe.T.Examples.Kissat.FullM7FidelityCore
open LeanQbe.T.Examples.Kissat.FullM7FidelitySearch
open LeanQbe.T.Examples.Kissat.FullM7Splice

/-! ## 1. `29` Disjoint Replacements, `3` Inserted Helpers & `413`-Fn `m7FidelityModule` -/

/-- `9` Target A replacements from `BvaGuFix`, `CompactFix`, `BvaV5Fix`, and `FidelitySched`. -/
def m7FidHeadRepls : List Fn :=
  [ m7BvaCommitFn
  , m7AnalyzeRsnFn
  , m7fixCompactNeededFn
  , m7fixCompactMarkLiveFn
  , m7fixCompactVarsFn
  , m7fixSweepCopyFn
  , m7v5ForwardSubFn
  , fidIlog10Fn
  , fidCalcMaxVFn ]

/-- Complete list of `29` disjoint canonical replacement functions for `FullM7Fidelity`. -/
def m7FidRepls : List Fn :=
  m7FidHeadRepls ++ m7ParityVivTiersPatchFns ++ fidSchedFixPatchFns ++
    fidCorePatchFns ++ fidSearchPatchRepls

/-- Complete list of `3` anchor-inserted helper functions (`+2` from `Core`, `+1` from `Search`). -/
def m7FidBefores : List (Sym × List Fn) :=
  fidCorePatchBefores ++ fidSearchPatchBefores

/-- Transparent exposed helper-insertion lookup matching `FullM7Splice.patchInsAt`. -/
def mfPatchInsAt (befores : List (Sym × List Fn)) (f : Fn) : List Fn :=
  (befores.filterMap fun (a, hs) => if a == f.name then some hs else none).flatten

/-- Transparent exposed splice helper matching `FullM7Splice.patchFns` so `m7FidelityModule.fns`
reduces in kernel/chunk inlining. -/
def mfPatchFns (repls : List Fn) (befores : List (Sym × List Fn)) (fs : List Fn) : List Fn :=
  fs.flatMap fun f => mfPatchInsAt befores f ++ [(repls.find? (·.name == f.name)).getD f]

private theorem mf_find_name_eq {repls : List Fn} {f r : Fn}
    (h : repls.find? (fun x => x.name == f.name) = some r) : r.name = f.name :=
  beq_iff_eq.mp (List.find?_some (p := fun x : Fn => x.name == f.name) h)

theorem mem_mfPatchInsAt {befores : List (Sym × List Fn)} {g fn : Fn}
    (h : fn ∈ mfPatchInsAt befores g) : ∃ hs, (g.name, hs) ∈ befores ∧ fn ∈ hs := by
  dsimp only [mfPatchInsAt] at h
  rcases List.mem_flatten.mp h with ⟨hs, hhs, hfn⟩
  rcases List.mem_filterMap.mp hhs with ⟨⟨a, hs0⟩, hm, hif⟩
  cases hcmp : (a == g.name)
  · simp [hcmp] at hif
  · have ha : a = g.name := beq_iff_eq.mp hcmp
    subst ha; simp at hif; subst hif; exact ⟨hs0, hm, hfn⟩

theorem mfPatchFns_mem_of_ne {repls : List Fn} {befores : List (Sym × List Fn)}
    {fs : List Fn} {g : Fn} (hg : g ∈ fs) (hne : ∀ r ∈ repls, r.name ≠ g.name) :
    g ∈ mfPatchFns repls befores fs := by
  refine List.mem_flatMap.mpr ⟨g, hg, List.mem_append_right _ ?_⟩
  cases h : repls.find? (fun x => x.name == g.name) with
  | none => exact List.mem_singleton_self _
  | some r => exact absurd (mf_find_name_eq h) (hne r (List.mem_of_find?_eq_some h))

theorem mfPatchFns_wf {repls fs : List Fn} {befores : List (Sym × List Fn)}
    (hfs : ∀ f ∈ fs, f.Wf) (hr : ∀ r ∈ repls, r.Wf)
    (hi : ∀ p ∈ befores, ∀ h ∈ p.2, h.Wf) :
    ∀ f ∈ mfPatchFns repls befores fs, f.Wf := by
  intro fn hfn
  rcases List.mem_flatMap.mp hfn with ⟨g, hg, hmem⟩
  rcases List.mem_append.mp hmem with h_ins | h_rep
  · rcases mem_mfPatchInsAt h_ins with ⟨hs, hm, hfn_hs⟩
    exact hi (g.name, hs) hm fn hfn_hs
  · rcases List.mem_singleton.mp h_rep with rfl
    cases h : repls.find? (fun x => x.name == g.name) with
    | none => exact hfs g hg
    | some r => exact hr r (List.mem_of_find?_eq_some h)

private theorem mfPatchFns_names_map {repls fs : List Fn} {befores : List (Sym × List Fn)}
    (hsig : ∀ r ∈ repls, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig) :
    (mfPatchFns repls befores fs).map Fn.name =
      fs.flatMap fun f => (mfPatchInsAt befores f).map Fn.name ++ [f.name] := by
  induction fs with
  | nil => rfl
  | cons f rest ih =>
    have hsig_r : ∀ r ∈ repls, ∀ g ∈ rest, r.name = g.name → r.sig = g.sig :=
      fun r hr g hg => hsig r hr g (List.mem_cons_of_mem f hg)
    have hname : ((repls.find? (fun x => x.name == f.name)).getD f).name = f.name := by
      cases h : repls.find? (fun x => x.name == f.name) with
      | none => rfl
      | some r => exact mf_find_name_eq h
    dsimp only [mfPatchFns] at ih ⊢
    simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil] at ih ⊢
    rw [hname, ih hsig_r]

private theorem mfPatchFns_names_nodup {repls fs : List Fn} {befores : List (Sym × List Fn)}
    (hnd : (fs.map Fn.name).Nodup)
    (hsig : ∀ r ∈ repls, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig)
    (hinsNd : ∀ f ∈ fs, ((mfPatchInsAt befores f).map Fn.name).Nodup)
    (hinsDisj : ∀ f ∈ fs, ∀ h ∈ mfPatchInsAt befores f, h.name ∉ fs.map Fn.name)
    (hinsPair : ∀ f₁ ∈ fs, ∀ f₂ ∈ fs, f₁.name ≠ f₂.name →
      ∀ h ∈ mfPatchInsAt befores f₁, h.name ∉ (mfPatchInsAt befores f₂).map Fn.name) :
    ((mfPatchFns repls befores fs).map Fn.name).Nodup := by
  rw [mfPatchFns_names_map hsig]
  clear hsig repls
  induction fs with
  | nil => exact List.nodup_nil
  | cons f rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hinsNd_r : ∀ g ∈ rest, ((mfPatchInsAt befores g).map Fn.name).Nodup :=
      fun g hg => hinsNd g (List.mem_cons_of_mem f hg)
    have hinsDisj_r : ∀ g ∈ rest, ∀ h ∈ mfPatchInsAt befores g, h.name ∉ rest.map Fn.name :=
      fun g hg h hh hm => hinsDisj g (List.mem_cons_of_mem f hg) h hh
        (by simp [List.mem_cons, hm])
    have hinsPair_r : ∀ g₁ ∈ rest, ∀ g₂ ∈ rest, g₁.name ≠ g₂.name →
        ∀ h ∈ mfPatchInsAt befores g₁, h.name ∉ (mfPatchInsAt befores g₂).map Fn.name :=
      fun g₁ hg₁ g₂ hg₂ => hinsPair g₁ (List.mem_cons_of_mem f hg₁)
        g₂ (List.mem_cons_of_mem f hg₂)
    have hrest_nd := ih hnd.2 hinsNd_r hinsDisj_r hinsPair_r
    simp only [List.flatMap_cons, List.nodup_append]
    refine ⟨⟨hinsNd f List.mem_cons_self, by simp, ?_⟩, hrest_nd, ?_⟩
    · intro x hx y hy hxy
      subst hxy
      simp only [List.mem_singleton] at hy; subst hy
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
          exact hinsDisj f List.mem_cons_self h hh
            (by simp [List.mem_cons, hy_gname, List.mem_map_of_mem hg])
      · simp only [List.mem_singleton] at hx_f; subst hx_f
        rcases List.mem_append.mp hy_g with hy_ins | hy_gname
        · rcases List.mem_map.mp hy_ins with ⟨h, hh, hnm⟩
          exact hinsDisj g (List.mem_cons_of_mem f hg) h hh (by simp [List.mem_cons, hnm])
        · simp only [List.mem_singleton] at hy_gname
          exact hne_fg hy_gname

private theorem mfPatchFns_length_sum (repls : List Fn) (befores : List (Sym × List Fn)) :
    ∀ (fs : List Fn),
    (mfPatchFns repls befores fs).length =
      fs.length + (fs.map (fun f => (mfPatchInsAt befores f).length)).sum
  | [] => rfl
  | f :: fs => by
    dsimp only [mfPatchFns]
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil,
      List.map_cons, List.sum_cons]
    have ih := mfPatchFns_length_sum repls befores fs
    dsimp only [mfPatchFns] at ih; rw [ih]; omega

private theorem mfCheckFnsCallsOk_patch (exits : List Sym) (extSigs : List SigEntry)
    (repls : List Fn) (befores : List (Sym × List Fn)) :
    ∀ (origSeen : List Fn) (seen : List SigEntry) (fs : List Fn),
    (∀ g ∈ origSeen, g.sig ∈ seen) →
    LeanQbe.T.Module.checkFnsCallsOk exits extSigs (origSeen.map Fn.sig) fs = true →
    (∀ r ∈ repls, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig) →
    (∀ pre f post, fs = pre ++ f :: post →
      LeanQbe.T.Module.checkFnsCallsOk exits extSigs
        ((origSeen ++ pre).map Fn.sig) (mfPatchInsAt befores f) = true) →
    (∀ pre f post r, fs = pre ++ f :: post → r ∈ repls → r.name = f.name →
      r.checkCallsOk
        ((origSeen ++ pre).map Fn.sig ++ (mfPatchInsAt befores f).map Fn.sig ++ extSigs)
        exits = true) →
    LeanQbe.T.Module.checkFnsCallsOk exits extSigs seen (mfPatchFns repls befores fs) = true
  | _, _, [], _, _, _, _, _ => rfl
  | origSeen, seen, f :: rest, hsub, hchk, hsig, hins, hrepl => by
    simp only [LeanQbe.T.Module.checkFnsCallsOk, Bool.and_eq_true] at hchk
    dsimp only [mfPatchFns]
    simp only [List.flatMap_cons]
    have hsig_rest : ∀ r ∈ repls, ∀ g ∈ rest, r.name = g.name → r.sig = g.sig :=
      fun r hr g hg => hsig r hr g (List.mem_cons_of_mem f hg)
    have hins_rest : ∀ pre g post, rest = pre ++ g :: post →
        LeanQbe.T.Module.checkFnsCallsOk exits extSigs
          (((origSeen ++ [f]) ++ pre).map Fn.sig) (mfPatchInsAt befores g) = true := by
      intro pre g post hsplit; rw [List.append_assoc]
      exact hins (f :: pre) g post (by rw [hsplit]; rfl)
    have hrepl_rest : ∀ pre g post r, rest = pre ++ g :: post → r ∈ repls → r.name = g.name →
        r.checkCallsOk
          (((origSeen ++ [f]) ++ pre).map Fn.sig ++
            (mfPatchInsAt befores g).map Fn.sig ++ extSigs)
          exits = true := by
      intro pre g post r hsplit hr hnm
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        hrepl (f :: pre) g post r (by rw [hsplit]; rfl) hr hnm
    have hhead_sig : ((repls.find? (fun x => x.name == f.name)).getD f).sig = f.sig := by
      cases h : repls.find? (fun x => x.name == f.name) with
      | none => rfl
      | some r =>
        dsimp only [Option.getD]
        exact hsig r (List.mem_of_find?_eq_some h) f List.mem_cons_self (mf_find_name_eq h)
    have hsub_ext : ∀ s ∈ origSeen.map Fn.sig ++ extSigs, s ∈ seen ++ extSigs := by
      intro s hs
      rcases List.mem_append.mp hs with hs1 | hs2
      · rcases List.mem_map.mp hs1 with ⟨g, hg, rfl⟩
        exact List.mem_append_left _ (hsub g hg)
      · exact List.mem_append_right _ hs2
    have h_ins_ok : LeanQbe.T.Module.checkFnsCallsOk exits extSigs seen
        (mfPatchInsAt befores f) = true := by
      have h0 := hins [] f rest rfl
      simp only [List.append_nil] at h0
      exact checkFnsCallsOk_mono hsub_ext h0
    have h_mid_ok : ((repls.find? (fun x => x.name == f.name)).getD f).checkCallsOk
        ((seen ++ (mfPatchInsAt befores f).map Fn.sig) ++ extSigs) exits = true := by
      cases h : repls.find? (fun x => x.name == f.name) with
      | none =>
        refine fn_checkCallsOk_mono (fun s hs => ?_) hchk.1
        rcases List.mem_append.mp (hsub_ext s hs) with hs1 | hs2
        · exact List.mem_append_left _ (List.mem_append_left _ hs1)
        · exact List.mem_append_right _ hs2
      | some r =>
        have h0 := hrepl [] f rest r rfl (List.mem_of_find?_eq_some h) (mf_find_name_eq h)
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
        g.sig ∈ seen ++ ((mfPatchInsAt befores f).map Fn.sig ++
          [((repls.find? (fun x => x.name == f.name)).getD f).sig]) := by
      intro g hg
      rcases List.mem_append.mp hg with hg1 | hg2
      · exact List.mem_append_left _ (hsub g hg1)
      · simp only [List.mem_singleton] at hg2; subst hg2
        exact List.mem_append_right _ (List.mem_append_right _ (by simp [hhead_sig]))
    have hchk2 :
        LeanQbe.T.Module.checkFnsCallsOk exits extSigs ((origSeen ++ [f]).map Fn.sig) rest =
          true := by
      simpa only [List.map_append, List.map_singleton] using hchk.2
    exact mfCheckFnsCallsOk_patch exits extSigs repls befores (origSeen ++ [f])
      (seen ++ ((mfPatchInsAt befores f).map Fn.sig ++
        [((repls.find? (fun x => x.name == f.name)).getD f).sig]))
      rest hsub_next hchk2 hsig_rest hins_rest hrepl_rest

private theorem mfPatchModule_checkAcyclic {M : LeanQbe.T.Module} {repls : List Fn}
    {befores : List (Sym × List Fn)}
    (hnd : ((mfPatchFns repls befores M.fns).map Fn.name ++ M.externs.map Extern.name).Nodup)
    (hM : M.checkAcyclic = true)
    (hsig : ∀ r ∈ repls, ∀ f ∈ M.fns, r.name = f.name → r.sig = f.sig)
    (hins : ∀ pre f post, M.fns = pre ++ f :: post →
      LeanQbe.T.Module.checkFnsCallsOk M.exits (M.externs.map Extern.sig)
        (pre.map Fn.sig) (mfPatchInsAt befores f) = true)
    (hrepl : ∀ pre f post r, M.fns = pre ++ f :: post → r ∈ repls → r.name = f.name →
      r.checkCallsOk
        (pre.map Fn.sig ++ (mfPatchInsAt befores f).map Fn.sig ++ M.externs.map Extern.sig)
        M.exits = true) :
    ({ M with fns := mfPatchFns repls befores M.fns } : LeanQbe.T.Module).checkAcyclic = true := by
  simp only [LeanQbe.T.Module.checkAcyclic, Bool.and_eq_true] at hM ⊢
  refine ⟨listNodup_iff.mpr hnd, ?_⟩
  exact mfCheckFnsCallsOk_patch M.exits (M.externs.map Extern.sig) repls befores [] [] M.fns
    (fun _ h => nomatch h) hM.2 hsig hins hrepl

/-- Ordered `413`-function list of `FullM7Fidelity` (Target A, upstream Kissat 4.0.4). -/
def m7FidelityFns : List Fn :=
  mfPatchFns m7FidRepls m7FidBefores m7Fns

/-- Closed `413`-function `FullM7Fidelity` (`KissatM7Fidelity`) module (`0` externs, `0` exits). -/
def m7FidelityModule : LeanQbe.T.Module :=
  { fns := m7FidelityFns, externs := [], exits := [] }

theorem m7FidRepls_length : m7FidRepls.length = 29 := by rfl

theorem m7FidRepls_names_nodup : (m7FidRepls.map Fn.name).Nodup := by decide

theorem m7FidelityFns_length : m7FidelityFns.length = 413 := by
  have hsum : (m7Fns.map (fun f => (mfPatchInsAt m7FidBefores f).length)).sum = 3 := by
    t_kernel_rfl
  dsimp only [m7FidelityFns]
  rw [mfPatchFns_length_sum, FullM7Proof.m7Fns_length, hsum]

theorem m7FidHeadRepls_wf : ∀ r ∈ m7FidHeadRepls, r.Wf := by
  intro r hr
  simp only [m7FidHeadRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_bva_commit_m7_wf
  · exact full_analyze_rsn_m7_wf
  · exact full_compact_needed_m7fix_wf
  · exact full_compact_mark_live_m7fix_wf
  · exact full_compact_vars_m7fix_wf
  · exact full_sweep_copy_m7fix_wf
  · exact full_forward_sub_m7v5_wf
  · exact full_ilog10_fid_wf
  · exact full_calc_max_v_fid_wf

theorem m7FidRepls_wf : ∀ r ∈ m7FidRepls, r.Wf := by
  intro r hr
  simp only [m7FidRepls, List.mem_append] at hr
  rcases hr with (((h1 | h2) | h3) | h4) | h5
  · exact m7FidHeadRepls_wf r h1
  · exact m7ParityVivTiersPatchFns_wf r h2
  · exact fidSchedFix_fns_wf r h3
  · exact fidCorePatchFns_wf r h4
  · exact fidSearchPatchRepls_wf r h5

theorem m7FidBefores_wf : ∀ p ∈ m7FidBefores, ∀ h ∈ p.2, h.Wf := by
  intro p hp h hh
  rcases List.mem_append.mp hp with h1 | h2
  · exact fidCorePatchBefores_wf p h1 h hh
  · exact fidSearchPatchBefores_wf p h2 h hh

theorem m7FidelityFns_wf : ∀ f ∈ m7FidelityFns, f.Wf :=
  mfPatchFns_wf m7Fns_wf m7FidRepls_wf m7FidBefores_wf

theorem m7Fidelity_noExit : m7FidelityModule.exits = [] := rfl

/-! ## 2. Exact `m7Fns` Index Metadata & Fast `O(29 + 3)` Acyclicity Proof -/

private theorem mf_p1 {k : Nat} (hk : k < 112) {s : SigEntry}
    (h : m7FnsPart1[k]?.map Fn.sig = some s) : m7Fns[k]?.map Fn.sig = some s := by
  rw [m7_get_p1 hk]; exact h

private theorem mf_p2 {k : Nat} (hk : k < 164) {s : SigEntry}
    (h : m7FnsPart2[k]?.map Fn.sig = some s) : m7Fns[112 + k]?.map Fn.sig = some s := by
  rw [m7_get_p2 hk]; exact h

private theorem mf_p3 {k : Nat} {s : SigEntry}
    (h : m7FnsPart3[k]?.map Fn.sig = some s) : m7Fns[276 + k]?.map Fn.sig = some s := by
  rw [m7_get_p3]; exact h

private theorem mf_idx_8 : m7Fns[8]?.map Fn.sig =
    some ("full_isqrt", [i64], [i64]) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_9 : m7Fns[9]?.map Fn.sig =
    some ("full_ilog10", [i64], [i64]) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_10 : m7Fns[10]?.map Fn.sig =
    some ("full_rng_next", [i64], [i64]) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_11 : m7Fns[11]?.map Fn.sig =
    some ("full_arena_next", [i64, i32], [i32]) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_12 : m7Fns[12]?.map Fn.sig =
    some ("full_alloc_cl", [i64, i32, i32, .bool], [i64]) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_17 : m7Fns[17]?.map Fn.sig =
    some ("full_wstack_defrag", [i64], []) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_18 : m7Fns[18]?.map Fn.sig =
    some ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]) :=
  mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_19 : m7Fns[19]?.map Fn.sig =
    some ("full_heap_up", [i64, i32], []) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_20 : m7Fns[20]?.map Fn.sig =
    some ("full_heap_down", [i64, i32], []) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_24 : m7Fns[24]?.map Fn.sig =
    some ("full_rescale", [i64], []) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_25 : m7Fns[25]?.map Fn.sig =
    some ("full_bump_var", [i64, i32], []) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_26 : m7Fns[26]?.map Fn.sig =
    some ("full_bump_decay", [i64], []) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_28 : m7Fns[28]?.map Fn.sig =
    some ("full_queue_mtf", [i64, i32], []) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_31 : m7Fns[31]?.map Fn.sig =
    some ("full_log10_q16_m7", [i64], [i64]) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_32 : m7Fns[32]?.map Fn.sig =
    some ("full_scale_delta_m5", [i64, i64], [i64]) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_34 : m7Fns[34]?.map Fn.sig =
    some ("full_scale_delta", [i64, i64], [i64]) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_35 : m7Fns[35]?.map Fn.sig =
    some ("full_assign_lvl", [i64, i32, i32, i32], []) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_39 : m7Fns[39]?.map Fn.sig =
    some ("full_backtrack", [i64, i64], []) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_43 : m7Fns[43]?.map Fn.sig =
    some ("full_fixed_bytes", [i64], [i64]) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_46 : m7Fns[46]?.map Fn.sig =
    some ("full_calc_max_v", [i64, i64, i64, i64], [i64]) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_56 : m7Fns[56]?.map Fn.sig =
    some ("m6_ext_ensure_init", [i64], []) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_59 : m7Fns[59]?.map Fn.sig =
    some ("m6_hdr_sync_legacy_tiers", [i64], []) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_61 : m7Fns[61]?.map Fn.sig =
    some ("m6_hdr_recompute_tiers", [i64], []) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_66 : m7Fns[66]?.map Fn.sig =
    some ("m6_hdr_delaying", [i64, i64], [.bool]) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_67 : m7Fns[67]?.map Fn.sig =
    some ("m6_hdr_bump_delay", [i64, i64], []) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_68 : m7Fns[68]?.map Fn.sig =
    some ("m6_hdr_reduce_delay", [i64, i64], []) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_70 : m7Fns[70]?.map Fn.sig =
    some ("m6_hdr_get_watermark", [i64, i64], [i64]) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_71 : m7Fns[71]?.map Fn.sig =
    some ("m6_hdr_set_watermark", [i64, i64, i64], []) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_73 : m7Fns[73]?.map Fn.sig =
    some ("m6_hdr_dr_init", [i64], []) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_75 : m7Fns[75]?.map Fn.sig =
    some ("m6_hdr_dr_allow", [i64], [.bool]) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_80 : m7Fns[80]?.map Fn.sig =
    some ("full_unwatch_large", [i64, i32, i32], []) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_81 : m7Fns[81]?.map Fn.sig =
    some ("full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool]) :=
  mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_82 : m7Fns[82]?.map Fn.sig =
    some ("full_prop_chrono_hot", [i64, i64], [.bool]) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_83 : m7Fns[83]?.map Fn.sig =
    some ("full_propagate_ignore_hot", [i64, i64], [i64]) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_85 : m7Fns[85]?.map Fn.sig =
    some ("full_propagate_ignore", [i64, i64], [i64]) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_86 : m7Fns[86]?.map Fn.sig =
    some ("full_propagate", [i64], [i64]) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_97 : m7Fns[97]?.map Fn.sig =
    some ("full_sweep_copy", [i64, i64, i64, i32, .bool], [i64]) :=
  mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_104 : m7Fns[104]?.map Fn.sig =
    some ("full_arena_sweep", [i64], [i64]) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_105 : m7Fns[105]?.map Fn.sig =
    some ("full_mark_reasons", [i64, .bool], []) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_109 : m7Fns[109]?.map Fn.sig =
    some ("full_sort_reds", [i64, i64], []) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_111 : m7Fns[111]?.map Fn.sig =
    some ("full_reduce_m6", [i64, .bool], [i64]) := mf_p1 (by decide) (by t_kernel_rfl)
private theorem mf_idx_112 : m7Fns[112]?.map Fn.sig =
    some ("full_analyze_lit", [i64, i32, i32], [.bool]) :=
  mf_p2 (k := 0) (by decide) (by t_kernel_rfl)
private theorem mf_idx_113 : m7Fns[113]?.map Fn.sig =
    some ("full_analyze_rsn", [i64, i32, i32], [.bool]) :=
  mf_p2 (k := 1) (by decide) (by t_kernel_rfl)
private theorem mf_idx_117 : m7Fns[117]?.map Fn.sig =
    some ("full_sort_ana_qs_m6", [i64, i64], []) := mf_p2 (k := 5) (by decide) (by t_kernel_rfl)
private theorem mf_idx_118 : m7Fns[118]?.map Fn.sig =
    some ("full_bump_analyzed_m6_hdr", [i64], []) := mf_p2 (k := 6) (by decide) (by t_kernel_rfl)
private theorem mf_idx_124 : m7Fns[124]?.map Fn.sig =
    some ("full_min_mark", [i64, i32, i8], []) := mf_p2 (k := 12) (by decide) (by t_kernel_rfl)
private theorem mf_idx_129 : m7Fns[129]?.map Fn.sig =
    some ("full_sort_tmp", [i64], []) := mf_p2 (k := 17) (by decide) (by t_kernel_rfl)
private theorem mf_idx_130 : m7Fns[130]?.map Fn.sig =
    some ("full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool]) :=
  mf_p2 (k := 18) (by decide) (by t_kernel_rfl)
private theorem mf_idx_133 : m7Fns[133]?.map Fn.sig =
    some ("full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool]) :=
  mf_p2 (k := 21) (by decide) (by t_kernel_rfl)
private theorem mf_idx_135 : m7Fns[135]?.map Fn.sig =
    some ("full_min_shrink_m6", [i64], []) := mf_p2 (k := 23) (by decide) (by t_kernel_rfl)
private theorem mf_idx_151 : m7Fns[151]?.map Fn.sig =
    some ("full_analyze_m6_hdr", [i64], [i64]) := mf_p2 (k := 39) (by decide) (by t_kernel_rfl)
private theorem mf_idx_154 : m7Fns[154]?.map Fn.sig =
    some ("full_walk_cb_inv_m7", [i64, i64, i64], [i64]) :=
  mf_p2 (k := 42) (by decide) (by t_kernel_rfl)
private theorem mf_idx_155 : m7Fns[155]?.map Fn.sig =
    some ("full_walk_init_table_m7", [i64, i64], []) :=
  mf_p2 (k := 43) (by decide) (by t_kernel_rfl)
private theorem mf_idx_156 : m7Fns[156]?.map Fn.sig =
    some ("full_walk_effort_m7", [i64, i64], [i64]) :=
  mf_p2 (k := 44) (by decide) (by t_kernel_rfl)
private theorem mf_idx_157 : m7Fns[157]?.map Fn.sig =
    some ("full_walk_init_vals_m7", [i64], []) := mf_p2 (k := 45) (by decide) (by t_kernel_rfl)
private theorem mf_idx_158 : m7Fns[158]?.map Fn.sig =
    some ("full_walk_collect_m7", [i64], [i64]) := mf_p2 (k := 46) (by decide) (by t_kernel_rfl)
private theorem mf_idx_159 : m7Fns[159]?.map Fn.sig =
    some ("full_walk_build_occ_m7", [i64, i64], [i64]) :=
  mf_p2 (k := 47) (by decide) (by t_kernel_rfl)
private theorem mf_idx_161 : m7Fns[161]?.map Fn.sig =
    some ("full_walk_pick_m7", [i64, i32, i64], [i64]) :=
  mf_p2 (k := 49) (by decide) (by t_kernel_rfl)
private theorem mf_idx_162 : m7Fns[162]?.map Fn.sig =
    some ("full_walk_flip_m7", [i64, i32, i64, i64], [i64]) :=
  mf_p2 (k := 50) (by decide) (by t_kernel_rfl)
private theorem mf_idx_163 : m7Fns[163]?.map Fn.sig =
    some ("full_walk_save_min_m7", [i64, i64, .bool], []) :=
  mf_p2 (k := 51) (by decide) (by t_kernel_rfl)
private theorem mf_idx_164 : m7Fns[164]?.map Fn.sig =
    some ("full_walk_m7", [i64], []) := mf_p2 (k := 52) (by decide) (by t_kernel_rfl)
private theorem mf_idx_169 : m7Fns[169]?.map Fn.sig =
    some ("full_rephase", [i64], []) := mf_p2 (k := 57) (by decide) (by t_kernel_rfl)
private theorem mf_idx_170 : m7Fns[170]?.map Fn.sig =
    some ("full_restart_due", [i64], [i64]) := mf_p2 (k := 58) (by decide) (by t_kernel_rfl)
private theorem mf_idx_171 : m7Fns[171]?.map Fn.sig =
    some ("full_restart", [i64], []) := mf_p2 (k := 59) (by decide) (by t_kernel_rfl)
private theorem mf_idx_178 : m7Fns[178]?.map Fn.sig =
    some ("full_add_bin", [i64, i32, i32], [i64]) := mf_p2 (k := 66) (by decide) (by t_kernel_rfl)
private theorem mf_idx_179 : m7Fns[179]?.map Fn.sig =
    some ("full_delete_binary", [i64, i32, i32], []) :=
  mf_p2 (k := 67) (by decide) (by t_kernel_rfl)
private theorem mf_idx_184 : m7Fns[184]?.map Fn.sig =
    some ("full_lucky", [i64], [i64]) := mf_p2 (k := 72) (by decide) (by t_kernel_rfl)
private theorem mf_idx_209 : m7Fns[209]?.map Fn.sig =
    some ("full_viv_clause_m6", [i64, i32], [i64]) := mf_p2 (k := 97) (by decide) (by t_kernel_rfl)
private theorem mf_idx_211 : m7Fns[211]?.map Fn.sig =
    some ("full_viv_collect_m6", [i64, i64], [i64]) := mf_p2 (k := 99) (by decide) (by t_kernel_rfl)
private theorem mf_idx_212 : m7Fns[212]?.map Fn.sig =
    some ("full_viv_count_m6", [i64, i64], []) := mf_p2 (k := 100) (by decide) (by t_kernel_rfl)
private theorem mf_idx_213 : m7Fns[213]?.map Fn.sig =
    some ("full_viv_keys_m6", [i64, i64], []) := mf_p2 (k := 101) (by decide) (by t_kernel_rfl)
private theorem mf_idx_214 : m7Fns[214]?.map Fn.sig =
    some ("full_viv_sort_sched_m6", [i64, i64], []) :=
  mf_p2 (k := 102) (by decide) (by t_kernel_rfl)
private theorem mf_idx_215 : m7Fns[215]?.map Fn.sig =
    some ("full_viv_clear_tier_m6", [i64, i64], []) :=
  mf_p2 (k := 103) (by decide) (by t_kernel_rfl)
private theorem mf_idx_217 : m7Fns[217]?.map Fn.sig =
    some ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64]) :=
  mf_p2 (k := 105) (by decide) (by t_kernel_rfl)
private theorem mf_idx_218 : m7Fns[218]?.map Fn.sig =
    some ("full_vivify_m6_hdr", [i64], [i64]) := mf_p2 (k := 106) (by decide) (by t_kernel_rfl)
private theorem mf_idx_226 : m7Fns[226]?.map Fn.sig =
    some ("full_backbone_m6", [i64, i64], [i64]) := mf_p2 (k := 114) (by decide) (by t_kernel_rfl)
private theorem mf_idx_229 : m7Fns[229]?.map Fn.sig =
    some ("full_transitive_m6", [i64, i64], [i64]) := mf_p2 (k := 117) (by decide) (by t_kernel_rfl)
private theorem mf_idx_235 : m7Fns[235]?.map Fn.sig =
    some ("full_substitute", [i64], [i64]) := mf_p2 (k := 123) (by decide) (by t_kernel_rfl)
private theorem mf_idx_236 : m7Fns[236]?.map Fn.sig =
    some ("full_enter_dense", [i64], [.bool]) := mf_p2 (k := 124) (by decide) (by t_kernel_rfl)
private theorem mf_idx_237 : m7Fns[237]?.map Fn.sig =
    some ("full_rebuild_watches", [i64], [i64]) := mf_p2 (k := 125) (by decide) (by t_kernel_rfl)
private theorem mf_idx_275 : m7Fns[275]?.map Fn.sig =
    some ("full_congruence_dense", [i64, i64], [i64]) :=
  mf_p2 (k := 163) (by decide) (by t_kernel_rfl)
private theorem mf_idx_299 : m7Fns[299]?.map Fn.sig =
    some ("full_sweep_dense_m6", [i64, i64, i64], [i64]) := mf_p3 (k := 23) (by t_kernel_rfl)
private theorem mf_idx_300 : m7Fns[300]?.map Fn.sig =
    some ("full_fwd_dedup_bins", [i64], [.bool]) := mf_p3 (k := 24) (by t_kernel_rfl)
private theorem mf_idx_302 : m7Fns[302]?.map Fn.sig =
    some ("full_dense_flush_units_m7", [i64], [.bool]) := mf_p3 (k := 26) (by t_kernel_rfl)
private theorem mf_idx_303 : m7Fns[303]?.map Fn.sig =
    some ("full_fwd_flush_large_m7", [i64], []) := mf_p3 (k := 27) (by t_kernel_rfl)
private theorem mf_idx_304 : m7Fns[304]?.map Fn.sig =
    some ("full_fwd_reconnect_irred_m7", [i64], []) := mf_p3 (k := 28) (by t_kernel_rfl)
private theorem mf_idx_306 : m7Fns[306]?.map Fn.sig =
    some ("full_fwd_check_cl_m7", [i64, i32], [.bool]) := mf_p3 (k := 30) (by t_kernel_rfl)
private theorem mf_idx_307 : m7Fns[307]?.map Fn.sig =
    some ("full_fwd_connect_subsumer_m7", [i64, i32], []) := mf_p3 (k := 31) (by t_kernel_rfl)
private theorem mf_idx_308 : m7Fns[308]?.map Fn.sig =
    some ("full_fwd_collect_sort_m7", [i64], [i64]) := mf_p3 (k := 32) (by t_kernel_rfl)
private theorem mf_idx_311 : m7Fns[311]?.map Fn.sig =
    some ("full_forward_sub", [i64, i64], [i64]) := mf_p3 (k := 35) (by t_kernel_rfl)
private theorem mf_idx_338 : m7Fns[338]?.map Fn.sig =
    some ("full_bve_var_m7", [i64, i32], [i64]) := mf_p3 (k := 62) (by t_kernel_rfl)
private theorem mf_idx_340 : m7Fns[340]?.map Fn.sig =
    some ("full_init_fresh_var", [i64, i32], []) := mf_p3 (k := 64) (by t_kernel_rfl)
private theorem mf_idx_345 : m7Fns[345]?.map Fn.sig =
    some ("full_bva_scan_cands", [i64, i32, i32, i64], [i32]) := mf_p3 (k := 69) (by t_kernel_rfl)
private theorem mf_idx_347 : m7Fns[347]?.map Fn.sig =
    some ("full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32]) :=
  mf_p3 (k := 71) (by t_kernel_rfl)
private theorem mf_idx_348 : m7Fns[348]?.map Fn.sig =
    some ("full_bva_commit", [i64, i32], [.bool]) := mf_p3 (k := 72) (by t_kernel_rfl)
private theorem mf_idx_352 : m7Fns[352]?.map Fn.sig =
    some ("full_factor", [i64, i64], [i64]) := mf_p3 (k := 76) (by t_kernel_rfl)
private theorem mf_idx_353 : m7Fns[353]?.map Fn.sig =
    some ("full_compact_needed", [i64], [.bool]) := mf_p3 (k := 77) (by t_kernel_rfl)
private theorem mf_idx_355 : m7Fns[355]?.map Fn.sig =
    some ("full_compact_mark_live", [i64], []) := mf_p3 (k := 79) (by t_kernel_rfl)
private theorem mf_idx_360 : m7Fns[360]?.map Fn.sig =
    some ("full_compact_vars", [i64, i64, i64], []) := mf_p3 (k := 84) (by t_kernel_rfl)
private theorem mf_idx_365 : m7Fns[365]?.map Fn.sig =
    some ("full_compact", [i64], [i64]) := mf_p3 (k := 89) (by t_kernel_rfl)
private theorem mf_idx_368 : m7Fns[368]?.map Fn.sig =
    some ("full_reorder_queue_m7", [i64], [i64]) := mf_p3 (k := 92) (by t_kernel_rfl)
private theorem mf_idx_369 : m7Fns[369]?.map Fn.sig =
    some ("full_reorder_m6", [i64, i64], [i64]) := mf_p3 (k := 93) (by t_kernel_rfl)
private theorem mf_idx_374 : m7Fns[374]?.map Fn.sig =
    some ("full_min_u64", [i64, i64], [i64]) := mf_p3 (k := 98) (by t_kernel_rfl)
private theorem mf_idx_376 : m7Fns[376]?.map Fn.sig =
    some ("full_elim_dticks", [i64, .bool], [i64]) := mf_p3 (k := 100) (by t_kernel_rfl)
private theorem mf_idx_380 : m7Fns[380]?.map Fn.sig =
    some ("full_bve_heap_push_m7", [i64, i64, i32], [i64]) := mf_p3 (k := 104) (by t_kernel_rfl)
private theorem mf_idx_381 : m7Fns[381]?.map Fn.sig =
    some ("full_bve_heap_pop_m7", [i64, i64], [i32]) := mf_p3 (k := 105) (by t_kernel_rfl)
private theorem mf_idx_382 : m7Fns[382]?.map Fn.sig =
    some ("full_bve_collect_nbrs_m7", [i64, i32], [i64]) := mf_p3 (k := 106) (by t_kernel_rfl)
private theorem mf_idx_383 : m7Fns[383]?.map Fn.sig =
    some ("full_elim_bve_m7", [i64, i64], [i64]) := mf_p3 (k := 107) (by t_kernel_rfl)
private theorem mf_idx_385 : m7Fns[385]?.map Fn.sig =
    some ("full_eliminate_m6", [i64, .bool], [i64]) := mf_p3 (k := 109) (by t_kernel_rfl)
private theorem mf_idx_388 : m7Fns[388]?.map Fn.sig =
    some ("full_m7_set64", [i64, i64, i64], []) := mf_p3 (k := 112) (by t_kernel_rfl)
private theorem mf_idx_394 : m7Fns[394]?.map Fn.sig =
    some ("full_lucky_late_m7", [i64], [i64]) := mf_p3 (k := 118) (by t_kernel_rfl)
private theorem mf_idx_397 : m7Fns[397]?.map Fn.sig =
    some ("full_decide_m7", [i64], [i64]) := mf_p3 (k := 121) (by t_kernel_rfl)
private theorem mf_idx_398 : m7Fns[398]?.map Fn.sig =
    some ("full_ema_swap_m7", [i64, i64, i64], []) := mf_p3 (k := 122) (by t_kernel_rfl)
private theorem mf_idx_399 : m7Fns[399]?.map Fn.sig =
    some ("full_switch_mode_m7", [i64], []) := mf_p3 (k := 123) (by t_kernel_rfl)
private theorem mf_idx_400 : m7Fns[400]?.map Fn.sig =
    some ("full_probe_dticks_m6_hdr", [i64, .bool], [i64]) := mf_p3 (k := 124) (by t_kernel_rfl)
private theorem mf_idx_401 : m7Fns[401]?.map Fn.sig =
    some ("full_probe_tail_m6", [i64, i64], [i64]) := mf_p3 (k := 125) (by t_kernel_rfl)
private theorem mf_idx_402 : m7Fns[402]?.map Fn.sig =
    some ("full_probe_m6", [i64, .bool], [i64]) := mf_p3 (k := 126) (by t_kernel_rfl)
private theorem mf_idx_403 : m7Fns[403]?.map Fn.sig =
    some ("full_preprocess_m6", [i64], [i64]) := mf_p3 (k := 127) (by t_kernel_rfl)
private theorem mf_idx_404 : m7Fns[404]?.map Fn.sig =
    some ("full_simplify_m6", [i64, .bool, .bool], [i64]) := mf_p3 (k := 128) (by t_kernel_rfl)
private theorem mf_idx_405 : m7Fns[405]?.map Fn.sig =
    some ("full_search_m6", [i64], [i64]) := mf_p3 (k := 129) (by t_kernel_rfl)

theorem m7Fns_not_mem_bml : "full_bva_match_large_fid" ∉ m7Fns.map Fn.name := by
  have hc : (m7Fns.map Fn.name).contains "full_bva_match_large_fid" = false := by t_kernel_rfl
  exact fun hm => absurd hm (by simpa using hc)

theorem m7Fns_not_mem_sift : "full_reorder_sift_fid" ∉ m7Fns.map Fn.name := by
  have hc : (m7Fns.map Fn.name).contains "full_reorder_sift_fid" = false := by t_kernel_rfl
  exact fun hm => absurd hm (by simpa using hc)

theorem m7Fns_not_mem_hdec : "m6_hdr_decide_fid" ∉ m7Fns.map Fn.name := by
  have hc : (m7Fns.map Fn.name).contains "m6_hdr_decide_fid" = false := by t_kernel_rfl
  exact fun hm => absurd hm (by simpa using hc)

private theorem mf_filter_ne {a b : Sym} {v : List Fn} (hb : (a == b) = false) :
    (if a == b then some v else none) = none := by
  rw [hb]; rfl

theorem m7Fid_insAt_cases (f : Fn) :
    mfPatchInsAt m7FidBefores f = [] ∨
      (f.name = "full_bva_filter_row" ∧
        mfPatchInsAt m7FidBefores f = [fidBvaMatchLargeFidFn]) ∨
      (f.name = "full_reorder_queue_m7" ∧
        mfPatchInsAt m7FidBefores f = [fidReorderSiftFidFn]) ∨
      (f.name = "full_search_m6" ∧
        mfPatchInsAt m7FidBefores f = [fidHdrDecideFn]) := by
  by_cases h1 : f.name = "full_bva_filter_row"
  · right; left; refine ⟨h1, ?_⟩
    dsimp only [mfPatchInsAt, m7FidBefores, fidCorePatchBefores, fidSearchPatchBefores]
    rw [h1]; rfl
  · by_cases h2 : f.name = "full_reorder_queue_m7"
    · right; right; left; refine ⟨h2, ?_⟩
      dsimp only [mfPatchInsAt, m7FidBefores, fidCorePatchBefores, fidSearchPatchBefores]
      rw [h2]; rfl
    · by_cases h3 : f.name = "full_search_m6"
      · right; right; right; refine ⟨h3, ?_⟩
        dsimp only [mfPatchInsAt, m7FidBefores, fidCorePatchBefores, fidSearchPatchBefores]
        rw [h3]; rfl
      · left
        have hb1 : ("full_bva_filter_row" == f.name) = false := beq_false_of_ne (Ne.symm h1)
        have hb2 : ("full_reorder_queue_m7" == f.name) = false := beq_false_of_ne (Ne.symm h2)
        have hb3 : ("full_search_m6" == f.name) = false := beq_false_of_ne (Ne.symm h3)
        dsimp only [mfPatchInsAt, m7FidBefores, fidCorePatchBefores, fidSearchPatchBefores,
          List.cons_append, List.nil_append]
        rw [List.filterMap_cons, mf_filter_ne hb1, List.filterMap_cons, mf_filter_ne hb2,
          List.filterMap_cons, mf_filter_ne hb3]
        rfl

private theorem m7FidRepls_sigs :
    ∀ r ∈ m7FidRepls, ∀ f ∈ m7Fns, r.name = f.name → r.sig = f.sig := by
  obtain ⟨f9, hf9, hs9⟩ := sig_of_map_idx mf_idx_9
  obtain ⟨f46, hf46, hs46⟩ := sig_of_map_idx mf_idx_46
  obtain ⟨f59, hf59, hs59⟩ := sig_of_map_idx mf_idx_59
  obtain ⟨f83, hf83, hs83⟩ := sig_of_map_idx mf_idx_83
  obtain ⟨f85, hf85, hs85⟩ := sig_of_map_idx mf_idx_85
  obtain ⟨f97, hf97, hs97⟩ := sig_of_map_idx mf_idx_97
  obtain ⟨f111, hf111, hs111⟩ := sig_of_map_idx mf_idx_111
  obtain ⟨f113, hf113, hs113⟩ := sig_of_map_idx mf_idx_113
  obtain ⟨f118, hf118, hs118⟩ := sig_of_map_idx mf_idx_118
  obtain ⟨f135, hf135, hs135⟩ := sig_of_map_idx mf_idx_135
  obtain ⟨f164, hf164, hs164⟩ := sig_of_map_idx mf_idx_164
  obtain ⟨f217, hf217, hs217⟩ := sig_of_map_idx mf_idx_217
  obtain ⟨f218, hf218, hs218⟩ := sig_of_map_idx mf_idx_218
  obtain ⟨f311, hf311, hs311⟩ := sig_of_map_idx mf_idx_311
  obtain ⟨f345, hf345, hs345⟩ := sig_of_map_idx mf_idx_345
  obtain ⟨f347, hf347, hs347⟩ := sig_of_map_idx mf_idx_347
  obtain ⟨f348, hf348, hs348⟩ := sig_of_map_idx mf_idx_348
  obtain ⟨f353, hf353, hs353⟩ := sig_of_map_idx mf_idx_353
  obtain ⟨f355, hf355, hs355⟩ := sig_of_map_idx mf_idx_355
  obtain ⟨f360, hf360, hs360⟩ := sig_of_map_idx mf_idx_360
  obtain ⟨f368, hf368, hs368⟩ := sig_of_map_idx mf_idx_368
  obtain ⟨f369, hf369, hs369⟩ := sig_of_map_idx mf_idx_369
  obtain ⟨f383, hf383, hs383⟩ := sig_of_map_idx mf_idx_383
  obtain ⟨f385, hf385, hs385⟩ := sig_of_map_idx mf_idx_385
  obtain ⟨f399, hf399, hs399⟩ := sig_of_map_idx mf_idx_399
  obtain ⟨f401, hf401, hs401⟩ := sig_of_map_idx mf_idx_401
  obtain ⟨f402, hf402, hs402⟩ := sig_of_map_idx mf_idx_402
  obtain ⟨f403, hf403, hs403⟩ := sig_of_map_idx mf_idx_403
  obtain ⟨f405, hf405, hs405⟩ := sig_of_map_idx mf_idx_405
  intro r hr f hf hnm
  rw [m7FidRepls, fidSchedFixPatchFns, fidSchedFixFns_eq_patchFns] at hr
  simp only [m7FidHeadRepls, m7ParityVivTiersPatchFns, fidCorePatchFns, fidSearchPatchRepls,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with
    ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl | rfl | rfl | rfl)) |
      (rfl | rfl | rfl | rfl | rfl)) |
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl)) |
      (rfl | rfl | rfl)
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf348
      (hnm.symm.trans (congrArg Prod.fst hs348.symm))) ▸ hs348.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf113
      (hnm.symm.trans (congrArg Prod.fst hs113.symm))) ▸ hs113.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf353
      (hnm.symm.trans (congrArg Prod.fst hs353.symm))) ▸ hs353.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf355
      (hnm.symm.trans (congrArg Prod.fst hs355.symm))) ▸ hs355.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf360
      (hnm.symm.trans (congrArg Prod.fst hs360.symm))) ▸ hs360.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf97
      (hnm.symm.trans (congrArg Prod.fst hs97.symm))) ▸ hs97.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf311
      (hnm.symm.trans (congrArg Prod.fst hs311.symm))) ▸ hs311.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf9
      (hnm.symm.trans (congrArg Prod.fst hs9.symm))) ▸ hs9.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf46
      (hnm.symm.trans (congrArg Prod.fst hs46.symm))) ▸ hs46.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf59
      (hnm.symm.trans (congrArg Prod.fst hs59.symm))) ▸ hs59.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf83
      (hnm.symm.trans (congrArg Prod.fst hs83.symm))) ▸ hs83.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf85
      (hnm.symm.trans (congrArg Prod.fst hs85.symm))) ▸ hs85.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf217
      (hnm.symm.trans (congrArg Prod.fst hs217.symm))) ▸ hs217.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf218
      (hnm.symm.trans (congrArg Prod.fst hs218.symm))) ▸ hs218.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf111
      (hnm.symm.trans (congrArg Prod.fst hs111.symm))) ▸ hs111.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf385
      (hnm.symm.trans (congrArg Prod.fst hs385.symm))) ▸ hs385.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf401
      (hnm.symm.trans (congrArg Prod.fst hs401.symm))) ▸ hs401.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf402
      (hnm.symm.trans (congrArg Prod.fst hs402.symm))) ▸ hs402.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf403
      (hnm.symm.trans (congrArg Prod.fst hs403.symm))) ▸ hs403.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf135
      (hnm.symm.trans (congrArg Prod.fst hs135.symm))) ▸ hs135.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf345
      (hnm.symm.trans (congrArg Prod.fst hs345.symm))) ▸ hs345.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf347
      (hnm.symm.trans (congrArg Prod.fst hs347.symm))) ▸ hs347.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf368
      (hnm.symm.trans (congrArg Prod.fst hs368.symm))) ▸ hs368.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf369
      (hnm.symm.trans (congrArg Prod.fst hs369.symm))) ▸ hs369.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf383
      (hnm.symm.trans (congrArg Prod.fst hs383.symm))) ▸ hs383.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf164
      (hnm.symm.trans (congrArg Prod.fst hs164.symm))) ▸ hs164.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf118
      (hnm.symm.trans (congrArg Prod.fst hs118.symm))) ▸ hs118.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf399
      (hnm.symm.trans (congrArg Prod.fst hs399.symm))) ▸ hs399.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf405
      (hnm.symm.trans (congrArg Prod.fst hs405.symm))) ▸ hs405.symm

theorem m7FidelityFns_names_nodup : (m7FidelityFns.map Fn.name).Nodup := by
  refine mfPatchFns_names_nodup m7_names_nodup m7FidRepls_sigs ?_ ?_ ?_
  · intro f _
    rcases m7Fid_insAt_cases f with h | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> simp
  · intro f _ h hh
    rcases m7Fid_insAt_cases f with h0 | ⟨_, h1⟩ | ⟨_, h2⟩ | ⟨_, h3⟩
    · rw [h0] at hh; cases hh
    · rw [h1, List.mem_singleton] at hh; subst hh; exact m7Fns_not_mem_bml
    · rw [h2, List.mem_singleton] at hh; subst hh; exact m7Fns_not_mem_sift
    · rw [h3, List.mem_singleton] at hh; subst hh; exact m7Fns_not_mem_hdec
  · intro f₁ _ f₂ _ hne h hh hm
    rcases m7Fid_insAt_cases f₁ with h1 | ⟨he1, hp1⟩ | ⟨he1, hp1⟩ | ⟨he1, hp1⟩
    · rw [h1] at hh; cases hh
    · rw [hp1, List.mem_singleton] at hh; subst hh
      rcases m7Fid_insAt_cases f₂ with h2 | ⟨he2, _⟩ | ⟨_, hp2⟩ | ⟨_, hp2⟩
      · rw [h2] at hm; cases hm
      · exact hne (he1.trans he2.symm)
      · rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
      · rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
    · rw [hp1, List.mem_singleton] at hh; subst hh
      rcases m7Fid_insAt_cases f₂ with h2 | ⟨_, hp2⟩ | ⟨he2, _⟩ | ⟨_, hp2⟩
      · rw [h2] at hm; cases hm
      · rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
      · exact hne (he1.trans he2.symm)
      · rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
    · rw [hp1, List.mem_singleton] at hh; subst hh
      rcases m7Fid_insAt_cases f₂ with h2 | ⟨_, hp2⟩ | ⟨_, hp2⟩ | ⟨he2, _⟩
      · rw [h2] at hm; cases hm
      · rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
      · rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
      · exact hne (he1.trans he2.symm)

/-- Fast `O(29 + 3)` preservation of `Module.checkAcyclic = true` across all `413` functions of
`m7FidelityModule`. -/
theorem m7Fidelity_acyclic : m7FidelityModule.checkAcyclic = true := by
  obtain ⟨g8, hg8, hsg8⟩ := sig_of_map_idx mf_idx_8
  obtain ⟨g9, hg9, hsg9⟩ := sig_of_map_idx mf_idx_9
  obtain ⟨g10, hg10, hsg10⟩ := sig_of_map_idx mf_idx_10
  obtain ⟨g11, hg11, hsg11⟩ := sig_of_map_idx mf_idx_11
  obtain ⟨g12, hg12, hsg12⟩ := sig_of_map_idx mf_idx_12
  obtain ⟨g17, hg17, hsg17⟩ := sig_of_map_idx mf_idx_17
  obtain ⟨g18, hg18, hsg18⟩ := sig_of_map_idx mf_idx_18
  obtain ⟨g19, hg19, hsg19⟩ := sig_of_map_idx mf_idx_19
  obtain ⟨g20, hg20, hsg20⟩ := sig_of_map_idx mf_idx_20
  obtain ⟨g24, hg24, hsg24⟩ := sig_of_map_idx mf_idx_24
  obtain ⟨g25, hg25, hsg25⟩ := sig_of_map_idx mf_idx_25
  obtain ⟨g26, hg26, hsg26⟩ := sig_of_map_idx mf_idx_26
  obtain ⟨g28, hg28, hsg28⟩ := sig_of_map_idx mf_idx_28
  obtain ⟨g31, hg31, hsg31⟩ := sig_of_map_idx mf_idx_31
  obtain ⟨g32, hg32, hsg32⟩ := sig_of_map_idx mf_idx_32
  obtain ⟨g34, hg34, hsg34⟩ := sig_of_map_idx mf_idx_34
  obtain ⟨g35, hg35, hsg35⟩ := sig_of_map_idx mf_idx_35
  obtain ⟨g39, hg39, hsg39⟩ := sig_of_map_idx mf_idx_39
  obtain ⟨g43, hg43, hsg43⟩ := sig_of_map_idx mf_idx_43
  obtain ⟨g46, hg46, hsg46⟩ := sig_of_map_idx mf_idx_46
  obtain ⟨g56, hg56, hsg56⟩ := sig_of_map_idx mf_idx_56
  obtain ⟨g59, hg59, hsg59⟩ := sig_of_map_idx mf_idx_59
  obtain ⟨g61, hg61, hsg61⟩ := sig_of_map_idx mf_idx_61
  obtain ⟨g66, hg66, hsg66⟩ := sig_of_map_idx mf_idx_66
  obtain ⟨g67, hg67, hsg67⟩ := sig_of_map_idx mf_idx_67
  obtain ⟨g68, hg68, hsg68⟩ := sig_of_map_idx mf_idx_68
  obtain ⟨g70, hg70, hsg70⟩ := sig_of_map_idx mf_idx_70
  obtain ⟨g71, hg71, hsg71⟩ := sig_of_map_idx mf_idx_71
  obtain ⟨g73, hg73, hsg73⟩ := sig_of_map_idx mf_idx_73
  obtain ⟨g75, hg75, hsg75⟩ := sig_of_map_idx mf_idx_75
  obtain ⟨g80, hg80, hsg80⟩ := sig_of_map_idx mf_idx_80
  obtain ⟨g81, hg81, hsg81⟩ := sig_of_map_idx mf_idx_81
  obtain ⟨g82, hg82, hsg82⟩ := sig_of_map_idx mf_idx_82
  obtain ⟨g83, hg83, hsg83⟩ := sig_of_map_idx mf_idx_83
  obtain ⟨g85, hg85, hsg85⟩ := sig_of_map_idx mf_idx_85
  obtain ⟨g86, hg86, hsg86⟩ := sig_of_map_idx mf_idx_86
  obtain ⟨g97, hg97, hsg97⟩ := sig_of_map_idx mf_idx_97
  obtain ⟨g104, hg104, hsg104⟩ := sig_of_map_idx mf_idx_104
  obtain ⟨g105, hg105, hsg105⟩ := sig_of_map_idx mf_idx_105
  obtain ⟨g109, hg109, hsg109⟩ := sig_of_map_idx mf_idx_109
  obtain ⟨g111, hg111, hsg111⟩ := sig_of_map_idx mf_idx_111
  obtain ⟨g112, hg112, hsg112⟩ := sig_of_map_idx mf_idx_112
  obtain ⟨g113, hg113, hsg113⟩ := sig_of_map_idx mf_idx_113
  obtain ⟨g117, hg117, hsg117⟩ := sig_of_map_idx mf_idx_117
  obtain ⟨g118, hg118, hsg118⟩ := sig_of_map_idx mf_idx_118
  obtain ⟨g124, hg124, hsg124⟩ := sig_of_map_idx mf_idx_124
  obtain ⟨g129, hg129, hsg129⟩ := sig_of_map_idx mf_idx_129
  obtain ⟨g130, hg130, hsg130⟩ := sig_of_map_idx mf_idx_130
  obtain ⟨g133, hg133, hsg133⟩ := sig_of_map_idx mf_idx_133
  obtain ⟨g135, hg135, hsg135⟩ := sig_of_map_idx mf_idx_135
  obtain ⟨g151, hg151, hsg151⟩ := sig_of_map_idx mf_idx_151
  obtain ⟨g154, hg154, hsg154⟩ := sig_of_map_idx mf_idx_154
  obtain ⟨g155, hg155, hsg155⟩ := sig_of_map_idx mf_idx_155
  obtain ⟨g156, hg156, hsg156⟩ := sig_of_map_idx mf_idx_156
  obtain ⟨g157, hg157, hsg157⟩ := sig_of_map_idx mf_idx_157
  obtain ⟨g158, hg158, hsg158⟩ := sig_of_map_idx mf_idx_158
  obtain ⟨g159, hg159, hsg159⟩ := sig_of_map_idx mf_idx_159
  obtain ⟨g161, hg161, hsg161⟩ := sig_of_map_idx mf_idx_161
  obtain ⟨g162, hg162, hsg162⟩ := sig_of_map_idx mf_idx_162
  obtain ⟨g163, hg163, hsg163⟩ := sig_of_map_idx mf_idx_163
  obtain ⟨g164, hg164, hsg164⟩ := sig_of_map_idx mf_idx_164
  obtain ⟨g169, hg169, hsg169⟩ := sig_of_map_idx mf_idx_169
  obtain ⟨g170, hg170, hsg170⟩ := sig_of_map_idx mf_idx_170
  obtain ⟨g171, hg171, hsg171⟩ := sig_of_map_idx mf_idx_171
  obtain ⟨g178, hg178, hsg178⟩ := sig_of_map_idx mf_idx_178
  obtain ⟨g179, hg179, hsg179⟩ := sig_of_map_idx mf_idx_179
  obtain ⟨g184, hg184, hsg184⟩ := sig_of_map_idx mf_idx_184
  obtain ⟨g209, hg209, hsg209⟩ := sig_of_map_idx mf_idx_209
  obtain ⟨g211, hg211, hsg211⟩ := sig_of_map_idx mf_idx_211
  obtain ⟨g212, hg212, hsg212⟩ := sig_of_map_idx mf_idx_212
  obtain ⟨g213, hg213, hsg213⟩ := sig_of_map_idx mf_idx_213
  obtain ⟨g214, hg214, hsg214⟩ := sig_of_map_idx mf_idx_214
  obtain ⟨g215, hg215, hsg215⟩ := sig_of_map_idx mf_idx_215
  obtain ⟨g217, hg217, hsg217⟩ := sig_of_map_idx mf_idx_217
  obtain ⟨g218, hg218, hsg218⟩ := sig_of_map_idx mf_idx_218
  obtain ⟨g226, hg226, hsg226⟩ := sig_of_map_idx mf_idx_226
  obtain ⟨g229, hg229, hsg229⟩ := sig_of_map_idx mf_idx_229
  obtain ⟨g235, hg235, hsg235⟩ := sig_of_map_idx mf_idx_235
  obtain ⟨g236, hg236, hsg236⟩ := sig_of_map_idx mf_idx_236
  obtain ⟨g237, hg237, hsg237⟩ := sig_of_map_idx mf_idx_237
  obtain ⟨g275, hg275, hsg275⟩ := sig_of_map_idx mf_idx_275
  obtain ⟨g299, hg299, hsg299⟩ := sig_of_map_idx mf_idx_299
  obtain ⟨g300, hg300, hsg300⟩ := sig_of_map_idx mf_idx_300
  obtain ⟨g302, hg302, hsg302⟩ := sig_of_map_idx mf_idx_302
  obtain ⟨g303, hg303, hsg303⟩ := sig_of_map_idx mf_idx_303
  obtain ⟨g304, hg304, hsg304⟩ := sig_of_map_idx mf_idx_304
  obtain ⟨g306, hg306, hsg306⟩ := sig_of_map_idx mf_idx_306
  obtain ⟨g307, hg307, hsg307⟩ := sig_of_map_idx mf_idx_307
  obtain ⟨g308, hg308, hsg308⟩ := sig_of_map_idx mf_idx_308
  obtain ⟨g311, hg311, hsg311⟩ := sig_of_map_idx mf_idx_311
  obtain ⟨g338, hg338, hsg338⟩ := sig_of_map_idx mf_idx_338
  obtain ⟨g340, hg340, hsg340⟩ := sig_of_map_idx mf_idx_340
  obtain ⟨g348, hg348, hsg348⟩ := sig_of_map_idx mf_idx_348
  obtain ⟨g352, hg352, hsg352⟩ := sig_of_map_idx mf_idx_352
  obtain ⟨g355, hg355, hsg355⟩ := sig_of_map_idx mf_idx_355
  obtain ⟨g365, hg365, hsg365⟩ := sig_of_map_idx mf_idx_365
  obtain ⟨g368, hg368, hsg368⟩ := sig_of_map_idx mf_idx_368
  obtain ⟨g369, hg369, hsg369⟩ := sig_of_map_idx mf_idx_369
  obtain ⟨g374, hg374, hsg374⟩ := sig_of_map_idx mf_idx_374
  obtain ⟨g376, hg376, hsg376⟩ := sig_of_map_idx mf_idx_376
  obtain ⟨g380, hg380, hsg380⟩ := sig_of_map_idx mf_idx_380
  obtain ⟨g381, hg381, hsg381⟩ := sig_of_map_idx mf_idx_381
  obtain ⟨g382, hg382, hsg382⟩ := sig_of_map_idx mf_idx_382
  obtain ⟨g383, hg383, hsg383⟩ := sig_of_map_idx mf_idx_383
  obtain ⟨g385, hg385, hsg385⟩ := sig_of_map_idx mf_idx_385
  obtain ⟨g388, hg388, hsg388⟩ := sig_of_map_idx mf_idx_388
  obtain ⟨g394, hg394, hsg394⟩ := sig_of_map_idx mf_idx_394
  obtain ⟨g397, hg397, hsg397⟩ := sig_of_map_idx mf_idx_397
  obtain ⟨g398, hg398, hsg398⟩ := sig_of_map_idx mf_idx_398
  obtain ⟨g399, hg399, hsg399⟩ := sig_of_map_idx mf_idx_399
  obtain ⟨g400, hg400, hsg400⟩ := sig_of_map_idx mf_idx_400
  obtain ⟨g401, hg401, hsg401⟩ := sig_of_map_idx mf_idx_401
  obtain ⟨g402, hg402, hsg402⟩ := sig_of_map_idx mf_idx_402
  obtain ⟨g403, hg403, hsg403⟩ := sig_of_map_idx mf_idx_403
  obtain ⟨g404, hg404, hsg404⟩ := sig_of_map_idx mf_idx_404
  obtain ⟨g405, hg405, hsg405⟩ := sig_of_map_idx mf_idx_405
  obtain ⟨g353, hg353, hsg353⟩ := sig_of_map_idx mf_idx_353
  change ({ m7Module with fns := mfPatchFns m7FidRepls m7FidBefores m7Module.fns } :
    LeanQbe.T.Module).checkAcyclic = true
  refine mfPatchModule_checkAcyclic (M := m7Module) ?_ m7_acyclic m7FidRepls_sigs ?_ ?_
  · have hnd := m7FidelityFns_names_nodup
    dsimp only [m7FidelityFns] at hnd
    simpa only [m7Module, List.map_nil, List.append_nil] using hnd
  · intro pre f post hsplit
    simp only [m7Module, List.map_nil] at hsplit ⊢
    rcases m7Fid_insAt_cases f with h0 | ⟨_, h1⟩ | ⟨_, h2⟩ | ⟨hf405, h3⟩
    · rw [h0]; rfl
    · rw [h1]
      have hb : fidBvaMatchLargeFidFn.checkCallsOk [] [] = true := by rfl
      have hm := fn_checkCallsOk_mono (a₂ := pre.map Fn.sig)
        (fun _ h => False.elim (List.not_mem_nil h)) hb
      dsimp only [LeanQbe.T.Module.checkFnsCallsOk]
      rw [List.append_nil, hm]; rfl
    · rw [h2]
      have hb : fidReorderSiftFidFn.checkCallsOk [] [] = true := by rfl
      have hm := fn_checkCallsOk_mono (a₂ := pre.map Fn.sig)
        (fun _ h => False.elim (List.not_mem_nil h)) hb
      dsimp only [LeanQbe.T.Module.checkFnsCallsOk]
      rw [List.append_nil, hm]; rfl
    · rw [h3]
      have hn0 : f.name = g405.name := hf405.trans (congrArg Prod.fst hsg405.symm)
      have hb : fidHdrDecideFn.checkCallsOk
          [ ("full_decide_m7", [i64], [i64]), ("m6_hdr_dr_init", [i64], []) ] [] = true := by rfl
      have hm : fidHdrDecideFn.checkCallsOk (pre.map Fn.sig) [] = true := by
        refine fn_checkCallsOk_mono (fun s hs => ?_) hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact hsg397 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg405 hn0 hg397 (by decide)
        · exact hsg73 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg405 hn0 hg73 (by decide)
      dsimp only [LeanQbe.T.Module.checkFnsCallsOk]
      rw [List.append_nil, hm]; rfl
  · intro pre f post r hsplit hr hnm
    simp only [m7Module, List.map_nil, List.append_nil] at hsplit ⊢
    rw [m7FidRepls, fidSchedFixPatchFns, fidSchedFixFns_eq_patchFns] at hr
    simp only [m7FidHeadRepls, m7ParityVivTiersPatchFns, fidCorePatchFns, fidSearchPatchRepls,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with
      ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
        (rfl | rfl | rfl | rfl | rfl)) |
        (rfl | rfl | rfl | rfl | rfl)) |
        (rfl | rfl | rfl | rfl | rfl | rfl | rfl)) |
        (rfl | rfl | rfl)
    · have hn0 : f.name = g348.name := hnm.symm.trans (congrArg Prod.fst hsg348.symm)
      have hc : m7BvaCommitFn.checkCallsOk
          [ ("full_alloc_cl", [i64, i32, i32, .bool], [i64])
          , ("full_wstack_defrag", [i64], [])
          , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool])
          , ("full_unwatch_large", [i64, i32, i32], [])
          , ("full_add_bin", [i64, i32, i32], [i64])
          , ("full_delete_binary", [i64, i32, i32], [])
          , ("full_init_fresh_var", [i64, i32], []) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsg12 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg348 hn0 hg12 (by decide)
      · exact hsg17 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg348 hn0 hg17 (by decide)
      · exact hsg18 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg348 hn0 hg18 (by decide)
      · exact hsg80 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg348 hn0 hg80 (by decide)
      · exact hsg178 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg348 hn0 hg178 (by decide)
      · exact hsg179 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg348 hn0 hg179 (by decide)
      · exact hsg340 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg348 hn0 hg340 (by decide)
    · have hn0 : f.name = g113.name := hnm.symm.trans (congrArg Prod.fst hsg113.symm)
      have hc : m7AnalyzeRsnFn.checkCallsOk
          [("full_analyze_lit", [i64, i32, i32], [.bool])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact hsg112 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg113 hn0 hg112 (by decide)
    · exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h))
        (by rfl : m7fixCompactNeededFn.checkCallsOk [] [] = true)
    · have hn0 : f.name = g355.name := hnm.symm.trans (congrArg Prod.fst hsg355.symm)
      have hc : m7fixCompactMarkLiveFn.checkCallsOk
          [("full_arena_next", [i64, i32], [i32])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact hsg11 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg355 hn0 hg11 (by decide)
    · exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h))
        (by rfl : m7fixCompactVarsFn.checkCallsOk [] [] = true)
    · have hn0 : f.name = g97.name := hnm.symm.trans (congrArg Prod.fst hsg97.symm)
      have hc : m7fixSweepCopyFn.checkCallsOk
          [ ("full_assign_lvl", [i64, i32, i32, i32], [])
          , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact hsg35 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg97 hn0 hg35 (by decide)
      · exact hsg18 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg97 hn0 hg18 (by decide)
    · have hn0 : f.name = g311.name := hnm.symm.trans (congrArg Prod.fst hsg311.symm)
      have hc : m7v5ForwardSubFn.checkCallsOk
          [ ("full_fwd_dedup_bins", [i64], [.bool])
          , ("full_dense_flush_units_m7", [i64], [.bool])
          , ("full_fwd_collect_sort_m7", [i64], [i64])
          , ("full_fwd_flush_large_m7", [i64], [])
          , ("full_fwd_check_cl_m7", [i64, i32], [.bool])
          , ("full_fwd_connect_subsumer_m7", [i64, i32], [])
          , ("full_arena_next", [i64, i32], [i32])
          , ("full_fwd_reconnect_irred_m7", [i64], []) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsg300 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg311 hn0 hg300 (by decide)
      · exact hsg302 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg311 hn0 hg302 (by decide)
      · exact hsg308 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg311 hn0 hg308 (by decide)
      · exact hsg303 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg311 hn0 hg303 (by decide)
      · exact hsg306 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg311 hn0 hg306 (by decide)
      · exact hsg307 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg311 hn0 hg307 (by decide)
      · exact hsg11 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg311 hn0 hg11 (by decide)
      · exact hsg304 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg311 hn0 hg304 (by decide)
    · exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h))
        (by rfl : fidIlog10Fn.checkCallsOk [] [] = true)
    · have hn0 : f.name = g46.name := hnm.symm.trans (congrArg Prod.fst hsg46.symm)
      have hc : fidCalcMaxVFn.checkCallsOk [("full_fixed_bytes", [i64], [i64])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact hsg43 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg46 hn0 hg43 (by decide)
    · have hn0 : f.name = g59.name := hnm.symm.trans (congrArg Prod.fst hsg59.symm)
      have hc : m7pSyncLegacyTiersFn.checkCallsOk
          [("m6_ext_ensure_init", [i64], [])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact hsg56 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg59 hn0 hg56 (by decide)
    · have hn0 : f.name = g83.name := hnm.symm.trans (congrArg Prod.fst hsg83.symm)
      have hc : m7pPropIgnoreHotFn.checkCallsOk
          [ ("full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool])
          , ("full_prop_chrono_hot", [i64, i64], [.bool]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact hsg81 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg83 hn0 hg81 (by decide)
      · exact hsg82 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg83 hn0 hg82 (by decide)
    · have hn0 : f.name = g85.name := hnm.symm.trans (congrArg Prod.fst hsg85.symm)
      have hc : m7pPropIgnoreFn.checkCallsOk
          [ ("full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool])
          , ("full_prop_chrono_hot", [i64, i64], [.bool]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact hsg81 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg85 hn0 hg81 (by decide)
      · exact hsg82 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg85 hn0 hg82 (by decide)
    · have hn0 : f.name = g217.name := hnm.symm.trans (congrArg Prod.fst hsg217.symm)
      have hc : m7pVivifyTierFn.checkCallsOk
          [ ("full_backtrack", [i64, i64], [])
          , ("full_viv_collect_m6", [i64, i64], [i64])
          , ("full_viv_count_m6", [i64, i64], [])
          , ("full_viv_keys_m6", [i64, i64], [])
          , ("full_viv_sort_sched_m6", [i64, i64], [])
          , ("full_viv_clause_m6", [i64, i32], [i64])
          , ("full_propagate", [i64], [i64])
          , ("full_viv_clear_tier_m6", [i64, i64], []) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsg39 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg217 hn0 hg39 (by decide)
      · exact hsg211 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg217 hn0 hg211 (by decide)
      · exact hsg212 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg217 hn0 hg212 (by decide)
      · exact hsg213 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg217 hn0 hg213 (by decide)
      · exact hsg214 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg217 hn0 hg214 (by decide)
      · exact hsg209 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg217 hn0 hg209 (by decide)
      · exact hsg86 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg217 hn0 hg86 (by decide)
      · exact hsg215 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg217 hn0 hg215 (by decide)
    · have hn0 : f.name = g218.name := hnm.symm.trans (congrArg Prod.fst hsg218.symm)
      have hc : m7pVivifyFn.checkCallsOk
          [ ("full_backtrack", [i64, i64], [])
          , ("m6_hdr_sync_legacy_tiers", [i64], [])
          , ("m6_hdr_get_watermark", [i64, i64], [i64])
          , ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact hsg39 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg218 hn0 hg39 (by decide)
      · exact hsg59 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg218 hn0 hg59 (by decide)
      · exact hsg70 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg218 hn0 hg70 (by decide)
      · exact hsg217 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg218 hn0 hg217 (by decide)
    · have hn0 : f.name = g111.name := hnm.symm.trans (congrArg Prod.fst hsg111.symm)
      have hc : fid2ReduceM6Fn.checkCallsOk
          [ ("full_isqrt", [i64], [i64]), ("full_backtrack", [i64, i64], [])
          , ("full_propagate", [i64], [i64]), ("m6_hdr_recompute_tiers", [i64], [])
          , ("full_mark_reasons", [i64, .bool], []), ("full_arena_next", [i64, i32], [i32])
          , ("full_sort_reds", [i64, i64], []), ("full_log10_q16_m7", [i64], [i64])
          , ("full_arena_sweep", [i64], [i64])
          , ("m6_hdr_set_watermark", [i64, i64, i64], []) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsg8 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg111 hn0 hg8 (by decide)
      · exact hsg39 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg111 hn0 hg39 (by decide)
      · exact hsg86 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg111 hn0 hg86 (by decide)
      · exact hsg61 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg111 hn0 hg61 (by decide)
      · exact hsg105 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg111 hn0 hg105 (by decide)
      · exact hsg11 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg111 hn0 hg11 (by decide)
      · exact hsg109 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg111 hn0 hg109 (by decide)
      · exact hsg31 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg111 hn0 hg31 (by decide)
      · exact hsg104 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg111 hn0 hg104 (by decide)
      · exact hsg71 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg111 hn0 hg71 (by decide)
    · have hn0 : f.name = g385.name := hnm.symm.trans (congrArg Prod.fst hsg385.symm)
      have hc : fid2EliminateM6Fn.checkCallsOk
          [ ("full_elim_dticks", [i64, .bool], [i64]), ("full_log10_q16_m7", [i64], [i64])
          , ("full_scale_delta", [i64, i64], [i64]), ("full_enter_dense", [i64], [.bool])
          , ("full_min_u64", [i64, i64], [i64]), ("full_forward_sub", [i64, i64], [i64])
          , ("full_elim_bve_m7", [i64, i64], [i64]), ("full_rebuild_watches", [i64], [i64]) ] [] =
          true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsg376 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg385 hn0 hg376 (by decide)
      · exact hsg31 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg385 hn0 hg31 (by decide)
      · exact hsg34 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg385 hn0 hg34 (by decide)
      · exact hsg236 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg385 hn0 hg236 (by decide)
      · exact hsg374 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg385 hn0 hg374 (by decide)
      · exact hsg311 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg385 hn0 hg311 (by decide)
      · exact hsg383 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg385 hn0 hg383 (by decide)
      · exact hsg237 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg385 hn0 hg237 (by decide)
    · have hn0 : f.name = g401.name := hnm.symm.trans (congrArg Prod.fst hsg401.symm)
      have hc : fid2ProbeTailM6Fn.checkCallsOk
          [ ("full_backbone_m6", [i64, i64], [i64])
          , ("full_transitive_m6", [i64, i64], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact hsg226 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg401 hn0 hg226 (by decide)
      · exact hsg229 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg401 hn0 hg229 (by decide)
    · have hn0 : f.name = g402.name := hnm.symm.trans (congrArg Prod.fst hsg402.symm)
      have hc : fid2ProbeM6Fn.checkCallsOk
          [ ("full_probe_dticks_m6_hdr", [i64, .bool], [i64])
          , ("full_log10_q16_m7", [i64], [i64]), ("full_scale_delta_m5", [i64, i64], [i64])
          , ("full_vivify_m6_hdr", [i64], [i64]), ("full_enter_dense", [i64], [.bool])
          , ("m6_hdr_delaying", [i64, i64], [.bool]), ("full_congruence_dense", [i64, i64], [i64])
          , ("full_rebuild_watches", [i64], [i64]), ("m6_hdr_set_watermark", [i64, i64, i64], [])
          , ("m6_hdr_reduce_delay", [i64, i64], []), ("m6_hdr_bump_delay", [i64, i64], [])
          , ("full_sweep_dense_m6", [i64, i64, i64], [i64]), ("full_substitute", [i64], [i64])
          , ("full_probe_tail_m6", [i64, i64], [i64]), ("full_backbone_m6", [i64, i64], [i64])
          , ("full_min_u64", [i64, i64], [i64]), ("full_factor", [i64, i64], [i64]) ] [] =
          true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · exact hsg400 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg402 hn0 hg400 (by decide)
      · exact hsg31 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg402 hn0 hg31 (by decide)
      · exact hsg32 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg402 hn0 hg32 (by decide)
      · exact hsg218 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg402 hn0 hg218 (by decide)
      · exact hsg236 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg402 hn0 hg236 (by decide)
      · exact hsg66 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg402 hn0 hg66 (by decide)
      · exact hsg275 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg402 hn0 hg275 (by decide)
      · exact hsg237 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg402 hn0 hg237 (by decide)
      · exact hsg71 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg402 hn0 hg71 (by decide)
      · exact hsg68 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg402 hn0 hg68 (by decide)
      · exact hsg67 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg402 hn0 hg67 (by decide)
      · exact hsg299 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg402 hn0 hg299 (by decide)
      · exact hsg235 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg402 hn0 hg235 (by decide)
      · exact hsg401 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg402 hn0 hg401 (by decide)
      · exact hsg226 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg402 hn0 hg226 (by decide)
      · exact hsg374 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg402 hn0 hg374 (by decide)
      · exact hsg352 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg402 hn0 hg352 (by decide)
    · have hn0 : f.name = g403.name := hnm.symm.trans (congrArg Prod.fst hsg403.symm)
      have hc : fid2PreprocessM6Fn.checkCallsOk
          [ ("full_propagate", [i64], [i64]), ("full_arena_sweep", [i64], [i64])
          , ("full_lucky", [i64], [i64]), ("full_compact_needed", [i64], [.bool])
          , ("full_compact", [i64], [i64]), ("full_scale_delta_m5", [i64, i64], [i64])
          , ("full_probe_m6", [i64, .bool], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsg86 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg403 hn0 hg86 (by decide)
      · exact hsg104 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg403 hn0 hg104 (by decide)
      · exact hsg184 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg403 hn0 hg184 (by decide)
      · exact hsg353 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg403 hn0 hg353 (by decide)
      · exact hsg365 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg403 hn0 hg365 (by decide)
      · exact hsg32 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg403 hn0 hg32 (by decide)
      · exact hsg402 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg403 hn0 hg402 (by decide)
    · have hn0 : f.name = g135.name := hnm.symm.trans (congrArg Prod.fst hsg135.symm)
      have hc : fidMinShrinkM6Fn.checkCallsOk
          [ ("full_sort_tmp", [i64], [])
          , ("full_min_mark", [i64, i32, i8], [])
          , ("full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool])
          , ("full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact hsg129 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg135 hn0 hg129 (by decide)
      · exact hsg124 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg135 hn0 hg124 (by decide)
      · exact hsg133 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg135 hn0 hg133 (by decide)
      · exact hsg130 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg135 hn0 hg130 (by decide)
    · exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h))
        (by rfl : fidBvaScanCandsFn.checkCallsOk [] [] = true)
    · have hp : mfPatchInsAt m7FidBefores f = [fidBvaMatchLargeFidFn] := by
        dsimp only [mfPatchInsAt, m7FidBefores, fidCorePatchBefores, fidSearchPatchBefores]
        rw [hnm.symm]; rfl
      have hc : fidBvaFilterRowFn.checkCallsOk
          [("full_bva_match_large_fid", [i64, i32, i32, i32], [.bool])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact List.mem_append_right _ (by rw [hp]; simp [fidBvaMatchLargeFidFn, Fn.sig])
    · have hn0 : f.name = g368.name := hnm.symm.trans (congrArg Prod.fst hsg368.symm)
      have hp : mfPatchInsAt m7FidBefores f = [fidReorderSiftFidFn] := by
        dsimp only [mfPatchInsAt, m7FidBefores, fidCorePatchBefores, fidSearchPatchBefores]
        rw [hnm.symm]; rfl
      have hc : fidReorderQueueM7Fn.checkCallsOk
          [ ("full_arena_next", [i64, i32], [i32])
          , ("full_rescale", [i64], [])
          , ("full_heap_up", [i64, i32], [])
          , ("full_reorder_sift_fid", [i64, i64, i64], []) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact List.mem_append_left _
          (hsg11 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg368 hn0 hg11 (by decide))
      · exact List.mem_append_left _
          (hsg24 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg368 hn0 hg24 (by decide))
      · exact List.mem_append_left _
          (hsg19 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg368 hn0 hg19 (by decide))
      · exact List.mem_append_right _ (by rw [hp]; simp [fidReorderSiftFidFn, Fn.sig])
    · have hn0 : f.name = g369.name := hnm.symm.trans (congrArg Prod.fst hsg369.symm)
      have hc : fidReorderM6Fn.checkCallsOk
          [("full_reorder_queue_m7", [i64], [i64])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact hsg368 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg369 hn0 hg368 (by decide)
    · have hn0 : f.name = g383.name := hnm.symm.trans (congrArg Prod.fst hsg383.symm)
      have hc : fidElimBveM7Fn.checkCallsOk
          [ ("full_dense_flush_units_m7", [i64], [.bool])
          , ("full_bve_heap_push_m7", [i64, i64, i32], [i64])
          , ("full_bve_heap_pop_m7", [i64, i64], [i32])
          , ("full_bve_collect_nbrs_m7", [i64, i32], [i64])
          , ("full_bve_var_m7", [i64, i32], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl
      · exact hsg302 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg383 hn0 hg302 (by decide)
      · exact hsg380 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg383 hn0 hg380 (by decide)
      · exact hsg381 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg383 hn0 hg381 (by decide)
      · exact hsg382 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg383 hn0 hg382 (by decide)
      · exact hsg338 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg383 hn0 hg338 (by decide)
    · have hn0 : f.name = g164.name := hnm.symm.trans (congrArg Prod.fst hsg164.symm)
      have hc : fidWalkM7Fn.checkCallsOk
          [ ("full_walk_init_vals_m7", [i64], [])
          , ("full_walk_collect_m7", [i64], [i64])
          , ("full_walk_cb_inv_m7", [i64, i64, i64], [i64])
          , ("full_walk_init_table_m7", [i64, i64], [])
          , ("full_walk_build_occ_m7", [i64, i64], [i64])
          , ("full_walk_effort_m7", [i64, i64], [i64])
          , ("full_walk_pick_m7", [i64, i32, i64], [i64])
          , ("full_walk_flip_m7", [i64, i32, i64, i64], [i64])
          , ("full_walk_save_min_m7", [i64, i64, .bool], [])
          , ("full_rng_next", [i64], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsg157 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg164 hn0 hg157 (by decide)
      · exact hsg158 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg164 hn0 hg158 (by decide)
      · exact hsg154 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg164 hn0 hg154 (by decide)
      · exact hsg155 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg164 hn0 hg155 (by decide)
      · exact hsg159 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg164 hn0 hg159 (by decide)
      · exact hsg156 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg164 hn0 hg156 (by decide)
      · exact hsg161 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg164 hn0 hg161 (by decide)
      · exact hsg162 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg164 hn0 hg162 (by decide)
      · exact hsg163 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg164 hn0 hg163 (by decide)
      · exact hsg10 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg164 hn0 hg10 (by decide)
    · have hn0 : f.name = g118.name := hnm.symm.trans (congrArg Prod.fst hsg118.symm)
      have hc : fidBumpAnalyzedFn.checkCallsOk
          [ ("m6_hdr_dr_allow", [i64], [.bool])
          , ("full_sort_ana_qs_m6", [i64, i64], [])
          , ("full_queue_mtf", [i64, i32], [])
          , ("full_bump_var", [i64, i32], [])
          , ("full_bump_decay", [i64], []) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl
      · exact hsg75 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg118 hn0 hg75 (by decide)
      · exact hsg117 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg118 hn0 hg117 (by decide)
      · exact hsg28 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg118 hn0 hg28 (by decide)
      · exact hsg25 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg118 hn0 hg25 (by decide)
      · exact hsg26 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg118 hn0 hg26 (by decide)
    · have hn0 : f.name = g399.name := hnm.symm.trans (congrArg Prod.fst hsg399.symm)
      have hc : fidSwitchModeFn.checkCallsOk
          [ ("full_heap_down", [i64, i32], [])
          , ("full_log10_q16_m7", [i64], [i64])
          , ("full_ema_swap_m7", [i64, i64, i64], [])
          , ("full_ilog10", [i64], [i64])
          , ("full_m7_set64", [i64, i64, i64], []) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl
      · exact hsg20 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg399 hn0 hg20 (by decide)
      · exact hsg31 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg399 hn0 hg31 (by decide)
      · exact hsg398 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg399 hn0 hg398 (by decide)
      · exact hsg9 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg399 hn0 hg9 (by decide)
      · exact hsg388 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg399 hn0 hg388 (by decide)
    · have hn0 : f.name = g405.name := hnm.symm.trans (congrArg Prod.fst hsg405.symm)
      have hp : mfPatchInsAt m7FidBefores f = [fidHdrDecideFn] := by
        dsimp only [mfPatchInsAt, m7FidBefores, fidCorePatchBefores, fidSearchPatchBefores]
        rw [hnm.symm]; rfl
      have hc : fidSearchM6Fn.checkCallsOk
          [ ("full_lucky_late_m7", [i64], [i64])
          , ("full_propagate", [i64], [i64])
          , ("full_analyze_m6_hdr", [i64], [i64])
          , ("full_reduce_m6", [i64, .bool], [i64])
          , ("full_switch_mode_m7", [i64], [])
          , ("full_restart_due", [i64], [i64])
          , ("full_restart", [i64], [])
          , ("full_reorder_m6", [i64, i64], [i64])
          , ("full_rephase", [i64], [])
          , ("full_simplify_m6", [i64, .bool, .bool], [i64])
          , ("m6_hdr_decide_fid", [i64], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact List.mem_append_left _
          (hsg394 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg405 hn0 hg394 (by decide))
      · exact List.mem_append_left _
          (hsg86 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg405 hn0 hg86 (by decide))
      · exact List.mem_append_left _
          (hsg151 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg405 hn0 hg151 (by decide))
      · exact List.mem_append_left _
          (hsg111 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg405 hn0 hg111 (by decide))
      · exact List.mem_append_left _
          (hsg399 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg405 hn0 hg399 (by decide))
      · exact List.mem_append_left _
          (hsg170 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg405 hn0 hg170 (by decide))
      · exact List.mem_append_left _
          (hsg171 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg405 hn0 hg171 (by decide))
      · exact List.mem_append_left _
          (hsg369 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg405 hn0 hg369 (by decide))
      · exact List.mem_append_left _
          (hsg169 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg405 hn0 hg169 (by decide))
      · exact List.mem_append_left _
          (hsg404 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hg405 hn0 hg404 (by decide))
      · exact List.mem_append_right _ (by rw [hp]; simp [fidHdrDecideFn, Fn.sig])

/-! ## 3. Compile-Time `#guard` Verification (`PrintCpp`, `PrintQbe`, 4-ISA Legal) -/

section Guards

open LeanQbe.T.PrintCpp

#guard m7FidRepls.length == 29
#guard (m7FidRepls.map Fn.name).eraseDups.length == 29
#guard m7FidRepls.all fun r => m7Fns.any fun f => f.sig == r.sig
#guard m7FidelityFns.length == 413
#guard (m7FidelityFns.map Fn.name).eraseDups.length == 413
#guard m7FidelityModule.checkAcyclic
#guard m7FidelityModule.exits.isEmpty && m7FidelityModule.externs.isEmpty
#guard (ppTModule m7FidelityModule).isOk
#guard (PrintQbe.module m7FidelityModule).isOk
#guard (ppModule (m7FidelityFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7FidelityFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7FidelityFns.map (Fn.legal .x64AVX512))).isOk
#guard (ppModule (m7FidelityFns.map (Fn.legal .x64AVX2))).isOk
#guard m7FidelityFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard m7FidelityFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard m7FidelityFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard m7FidelityFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

end Guards

end LeanQbe.T.Examples.Kissat.FullM7Fidelity
