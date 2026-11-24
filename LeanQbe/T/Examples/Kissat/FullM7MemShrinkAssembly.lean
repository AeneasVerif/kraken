/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7
public import LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5
public import LeanQbe.T.Examples.Kissat.FullM7PlusAssembly
public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
meta import LeanQbe.T.Examples.Kissat.FullM7
meta import LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5
meta import LeanQbe.T.Examples.Kissat.FullM7PlusAssembly
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Kissat Unified `FullM7Plus` & `FullM7Fidelity` Memory-Shrink Assembly (`412` / `415` Fns)

Clean additive wiring of `FullM7MemShrinkV5` (`151 -> 90 B/var` resident fixed prefix + `58 B/var`
dynamic transient pool `t_base`, V5 `cand = 4096` BVA parity, and `walk_best` compaction aliasing
fix) over unchanged `FullM7.m7Module` via `FullM7Fidelity.mfPatchFns` and list literals/`++` only
(natively extractable via `bench/kissat/extract_c0_direct.py`):
1. `m7PlusMemShrinkModule` (`412` fns = `410 + 2` helpers): `27` replacements (`12` `m7msRepls` +
   `15` non-colliding `FullM7Plus` replacements) + `2` inserted helpers (`full_fill_u64_m7`,
   `full_trans_bytes_m7`).
2. `m7FidelityMemShrinkModule` (`415` fns = `410 + 5` helpers): `39` replacements (`12` `m7msRepls`
   + `27` non-colliding `FullM7Fidelity` replacements) + `5` inserted helpers (`full_fill_u64_m7`,
   `full_trans_bytes_m7`, `full_bva_match_large_fid`, `full_reorder_sift_fid`,
   `m6_hdr_decide_fid`).

Certifies `length`, `names.Nodup`, `Wf`, fast `checkAcyclic`, `exits = []`, `externs = []`, and
compile-time `#guard` checks across `PrintCpp`, `PrintQbe`, and all 4 ISAs.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7BvaGuFix
open LeanQbe.T.Examples.Kissat.FullM7CompactFix
open LeanQbe.T.Examples.Kissat.FullM7BvaV5Fix
open LeanQbe.T.Examples.Kissat.FullM7ParityVivTiers
open LeanQbe.T.Examples.Kissat.FullM7ParityBvaTie
open LeanQbe.T.Examples.Kissat.FullM7FidelitySched
open LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFix
open LeanQbe.T.Examples.Kissat.FullM7FidelityCore
open LeanQbe.T.Examples.Kissat.FullM7FidelitySearch
open LeanQbe.T.Examples.Kissat.FullM7Plus
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM7Splice

/-! ## 1. Replacement & Helper Lists (`extract_c0_direct.py`-Compatible) -/

/-- Non-colliding tail replacements from `FullM7Plus` (`10` fns: omits `m7v5CalcMaxVFn` and
`m7fixCompactVarsFn` which are upgraded by `m7msRepls`). -/
def m7PlusNonMsTailRepls : List Fn :=
  [ m7BvaCommitFn
  , m7AnalyzeRsnFn
  , m7fixCompactNeededFn
  , m7fixCompactMarkLiveFn
  , m7fixSweepCopyFn
  , m7v5ForwardSubFn
  , m7PlusEliminateFn ] ++ m7ParityBvaTiePatchFns

/-- All `27` disjoint canonical replacements for `m7PlusMemShrinkModule`. -/
def m7PlusMsRepls : List Fn :=
  m7msRepls ++ m7ParityVivTiersPatchFns ++ m7PlusNonMsTailRepls

/-- Queued helper insertions for `m7PlusMemShrinkModule` (`+2` helpers). -/
def m7PlusMsBefores : List (Sym × List Fn) :=
  m7msBefores

/-- Non-colliding head replacements from `FullM7Fidelity` (`7` fns: omits `fidCalcMaxVFn` and
`m7fixCompactVarsFn` which are upgraded by `m7msRepls`). -/
def m7FidNonMsHeadRepls : List Fn :=
  [ m7BvaCommitFn
  , m7AnalyzeRsnFn
  , m7fixCompactNeededFn
  , m7fixCompactMarkLiveFn
  , m7fixSweepCopyFn
  , m7v5ForwardSubFn
  , fidIlog10Fn ]

/-- All `39` disjoint canonical replacements for `m7FidelityMemShrinkModule`. -/
def m7FidMsRepls : List Fn :=
  m7msRepls ++ m7FidNonMsHeadRepls ++ m7ParityVivTiersPatchFns ++
    fidSchedFixPatchFns ++ fidCorePatchFns ++ fidSearchPatchRepls

/-- Queued helper insertions for `m7FidelityMemShrinkModule` (`+5` helpers). -/
def m7FidMsBefores : List (Sym × List Fn) :=
  m7msBefores ++ m7FidBefores

/-- Ordered `412`-function list of `FullM7Plus + MemShrinkV5`. -/
def m7PlusMemShrinkFns : List Fn :=
  mfPatchFns m7PlusMsRepls m7PlusMsBefores m7Fns

/-- Closed `412`-function `FullM7Plus + MemShrinkV5` module (`0` externs, `0` exits). -/
def m7PlusMemShrinkModule : LeanQbe.T.Module :=
  { fns := m7PlusMemShrinkFns, externs := [], exits := [] }

/-- Ordered `415`-function list of `FullM7Fidelity + MemShrinkV5`. -/
def m7FidelityMemShrinkFns : List Fn :=
  mfPatchFns m7FidMsRepls m7FidMsBefores m7Fns

/-- Closed `415`-function `FullM7Fidelity + MemShrinkV5` module (`0` externs, `0` exits). -/
def m7FidelityMemShrinkModule : LeanQbe.T.Module :=
  { fns := m7FidelityMemShrinkFns, externs := [], exits := [] }

/-! ## 2. Structural `mfPatchFns` Proofs (Including Earlier Inserted Helpers in Context) -/

private theorem ms_find_name_eq {repls : List Fn} {f r : Fn}
    (h : repls.find? (fun x => x.name == f.name) = some r) : r.name = f.name :=
  beq_iff_eq.mp (List.find?_some (p := fun x : Fn => x.name == f.name) h)

private theorem msPatchFns_names_map {repls fs : List Fn} {befores : List (Sym × List Fn)}
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
      | some r => exact ms_find_name_eq h
    dsimp only [mfPatchFns] at ih ⊢
    simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil] at ih ⊢
    rw [hname, ih hsig_r]

private theorem msPatchFns_names_nodup {repls fs : List Fn} {befores : List (Sym × List Fn)}
    (hnd : (fs.map Fn.name).Nodup)
    (hsig : ∀ r ∈ repls, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig)
    (hinsNd : ∀ f ∈ fs, ((mfPatchInsAt befores f).map Fn.name).Nodup)
    (hinsDisj : ∀ f ∈ fs, ∀ h ∈ mfPatchInsAt befores f, h.name ∉ fs.map Fn.name)
    (hinsPair : ∀ f₁ ∈ fs, ∀ f₂ ∈ fs, f₁.name ≠ f₂.name →
      ∀ h ∈ mfPatchInsAt befores f₁, h.name ∉ (mfPatchInsAt befores f₂).map Fn.name) :
    ((mfPatchFns repls befores fs).map Fn.name).Nodup := by
  rw [msPatchFns_names_map hsig]
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

private theorem msPatchFns_length_sum (repls : List Fn) (befores : List (Sym × List Fn)) :
    ∀ (fs : List Fn),
    (mfPatchFns repls befores fs).length =
      fs.length + (fs.map (fun f => (mfPatchInsAt befores f).length)).sum
  | [] => rfl
  | f :: fs => by
    dsimp only [mfPatchFns]
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil,
      List.map_cons, List.sum_cons]
    have ih := msPatchFns_length_sum repls befores fs
    dsimp only [mfPatchFns] at ih; rw [ih]; omega

private theorem msCheckFnsCallsOk_patch (exits : List Sym) (extSigs : List SigEntry)
    (repls : List Fn) (befores : List (Sym × List Fn)) :
    ∀ (origSeen : List Fn) (seen : List SigEntry) (fs : List Fn),
    (∀ g ∈ origSeen, g.sig ∈ seen) →
    (∀ g ∈ origSeen, ∀ h ∈ mfPatchInsAt befores g, h.sig ∈ seen) →
    LeanQbe.T.Module.checkFnsCallsOk exits extSigs (origSeen.map Fn.sig) fs = true →
    (∀ r ∈ repls, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig) →
    (∀ pre f post, fs = pre ++ f :: post →
      LeanQbe.T.Module.checkFnsCallsOk exits extSigs
        ((origSeen ++ pre).map Fn.sig ++
          ((origSeen ++ pre).flatMap fun g => (mfPatchInsAt befores g).map Fn.sig))
        (mfPatchInsAt befores f) = true) →
    (∀ pre f post r, fs = pre ++ f :: post → r ∈ repls → r.name = f.name →
      r.checkCallsOk
        ((origSeen ++ pre).map Fn.sig ++
          ((origSeen ++ pre).flatMap fun g => (mfPatchInsAt befores g).map Fn.sig) ++
          (mfPatchInsAt befores f).map Fn.sig ++ extSigs)
        exits = true) →
    LeanQbe.T.Module.checkFnsCallsOk exits extSigs seen (mfPatchFns repls befores fs) = true
  | _, _, [], _, _, _, _, _, _ => rfl
  | origSeen, seen, f :: rest, hsub, hinsSeen, hchk, hsig, hins, hrepl => by
    simp only [LeanQbe.T.Module.checkFnsCallsOk, Bool.and_eq_true] at hchk
    dsimp only [mfPatchFns]
    simp only [List.flatMap_cons]
    have hsig_rest : ∀ r ∈ repls, ∀ g ∈ rest, r.name = g.name → r.sig = g.sig :=
      fun r hr g hg => hsig r hr g (List.mem_cons_of_mem f hg)
    have hins_rest : ∀ pre g post, rest = pre ++ g :: post →
        LeanQbe.T.Module.checkFnsCallsOk exits extSigs
          (((origSeen ++ [f]) ++ pre).map Fn.sig ++
            (((origSeen ++ [f]) ++ pre).flatMap fun x => (mfPatchInsAt befores x).map Fn.sig))
          (mfPatchInsAt befores g) = true := by
      intro pre g post hsplit
      rw [List.append_assoc]
      exact hins (f :: pre) g post (by rw [hsplit]; rfl)
    have hrepl_rest : ∀ pre g post r, rest = pre ++ g :: post → r ∈ repls → r.name = g.name →
        r.checkCallsOk
          (((origSeen ++ [f]) ++ pre).map Fn.sig ++
            (((origSeen ++ [f]) ++ pre).flatMap fun x => (mfPatchInsAt befores x).map Fn.sig) ++
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
        exact hsig r (List.mem_of_find?_eq_some h) f List.mem_cons_self (ms_find_name_eq h)
    have hsub_seen : ∀ s ∈ (origSeen.map Fn.sig ++
        origSeen.flatMap (fun g => (mfPatchInsAt befores g).map Fn.sig)) ++ extSigs,
        s ∈ seen ++ extSigs := by
      intro s hs
      rcases List.mem_append.mp hs with hs1 | hs2
      · rcases List.mem_append.mp hs1 with hs1a | hs1b
        · rcases List.mem_map.mp hs1a with ⟨g, hg, rfl⟩
          exact List.mem_append_left _ (hsub g hg)
        · rcases List.mem_flatMap.mp hs1b with ⟨g, hg, hs_g⟩
          rcases List.mem_map.mp hs_g with ⟨h, hh, rfl⟩
          exact List.mem_append_left _ (hinsSeen g hg h hh)
      · exact List.mem_append_right _ hs2
    have hsub_ext : ∀ s ∈ origSeen.map Fn.sig ++ extSigs, s ∈ seen ++ extSigs := by
      intro s hs
      rcases List.mem_append.mp hs with hs1 | hs2
      · exact hsub_seen s (List.mem_append_left _ (List.mem_append_left _ hs1))
      · exact List.mem_append_right _ hs2
    have h_ins_ok : LeanQbe.T.Module.checkFnsCallsOk exits extSigs seen
        (mfPatchInsAt befores f) = true := by
      have h0 := hins [] f rest rfl
      simp only [List.append_nil] at h0
      exact checkFnsCallsOk_mono hsub_seen h0
    have h_mid_ok : ((repls.find? (fun x => x.name == f.name)).getD f).checkCallsOk
        ((seen ++ (mfPatchInsAt befores f).map Fn.sig) ++ extSigs) exits = true := by
      cases h : repls.find? (fun x => x.name == f.name) with
      | none =>
        refine fn_checkCallsOk_mono (fun s hs => ?_) hchk.1
        rcases List.mem_append.mp (hsub_ext s hs) with hs1 | hs2
        · exact List.mem_append_left _ (List.mem_append_left _ hs1)
        · exact List.mem_append_right _ hs2
      | some r =>
        have h0 := hrepl [] f rest r rfl (List.mem_of_find?_eq_some h) (ms_find_name_eq h)
        simp only [List.append_nil] at h0
        refine fn_checkCallsOk_mono (fun s hs => ?_) h0
        rcases List.mem_append.mp hs with hs1 | hs2
        · rcases List.mem_append.mp hs1 with hs1a | hs1b
          · rcases List.mem_append.mp hs1a with hs1a1 | hs1a2
            · rcases List.mem_map.mp hs1a1 with ⟨g, hg, rfl⟩
              exact List.mem_append_left _ (List.mem_append_left _ (hsub g hg))
            · rcases List.mem_flatMap.mp hs1a2 with ⟨g, hg, hs_g⟩
              rcases List.mem_map.mp hs_g with ⟨h, hh, rfl⟩
              exact List.mem_append_left _ (List.mem_append_left _ (hinsSeen g hg h hh))
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
    have hinsSeen_next : ∀ g ∈ origSeen ++ [f], ∀ h ∈ mfPatchInsAt befores g,
        h.sig ∈ seen ++ ((mfPatchInsAt befores f).map Fn.sig ++
          [((repls.find? (fun x => x.name == f.name)).getD f).sig]) := by
      intro g hg h hh
      rcases List.mem_append.mp hg with hg1 | hg2
      · exact List.mem_append_left _ (hinsSeen g hg1 h hh)
      · simp only [List.mem_singleton] at hg2; subst hg2
        exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem hh))
    have hchk2 :
        LeanQbe.T.Module.checkFnsCallsOk exits extSigs ((origSeen ++ [f]).map Fn.sig) rest =
          true := by
      simpa only [List.map_append, List.map_singleton] using hchk.2
    exact msCheckFnsCallsOk_patch exits extSigs repls befores (origSeen ++ [f])
      (seen ++ ((mfPatchInsAt befores f).map Fn.sig ++
        [((repls.find? (fun x => x.name == f.name)).getD f).sig]))
      rest hsub_next hinsSeen_next hchk2 hsig_rest hins_rest hrepl_rest

private theorem msPatchModule_checkAcyclic {M : LeanQbe.T.Module} {repls : List Fn}
    {befores : List (Sym × List Fn)}
    (hnd : ((mfPatchFns repls befores M.fns).map Fn.name ++ M.externs.map Extern.name).Nodup)
    (hM : M.checkAcyclic = true)
    (hsig : ∀ r ∈ repls, ∀ f ∈ M.fns, r.name = f.name → r.sig = f.sig)
    (hins : ∀ pre f post, M.fns = pre ++ f :: post →
      LeanQbe.T.Module.checkFnsCallsOk M.exits (M.externs.map Extern.sig)
        (pre.map Fn.sig ++ (pre.flatMap fun g => (mfPatchInsAt befores g).map Fn.sig))
        (mfPatchInsAt befores f) = true)
    (hrepl : ∀ pre f post r, M.fns = pre ++ f :: post → r ∈ repls → r.name = f.name →
      r.checkCallsOk
        (pre.map Fn.sig ++ (pre.flatMap fun g => (mfPatchInsAt befores g).map Fn.sig) ++
          (mfPatchInsAt befores f).map Fn.sig ++ M.externs.map Extern.sig)
        M.exits = true) :
    ({ M with fns := mfPatchFns repls befores M.fns } : LeanQbe.T.Module).checkAcyclic = true := by
  simp only [LeanQbe.T.Module.checkAcyclic, Bool.and_eq_true] at hM ⊢
  refine ⟨listNodup_iff.mpr hnd, ?_⟩
  exact msCheckFnsCallsOk_patch M.exits (M.externs.map Extern.sig) repls befores [] [] M.fns
    (fun _ h => nomatch h) (fun _ h => nomatch h) hM.2 hsig hins hrepl

private theorem fn_mem_pre_of_lt_idx {xs pre post : List Fn} {f f0 g : Fn} {k i : Nat}
    (hnd : (xs.map Fn.name).Nodup) (hsplit : xs = pre ++ f :: post)
    (hi : xs[i]? = some f0) (heq : f.name = f0.name)
    (hk : xs[k]? = some g) (hlt : k < i) : g ∈ pre := by
  have hpre_get : xs[pre.length]? = some f := by
    rw [hsplit, List.getElem?_append_right (Nat.le_refl _)]; simp
  have hlen : pre.length = i := idx_eq_of_name_nodup hnd hi hpre_get heq
  have hk_lt : k < pre.length := hlen ▸ hlt
  have hgx : pre[k]'hk_lt = g := by
    have h1 : xs[k]? = pre[k]? := by rw [hsplit, List.getElem?_append_left hk_lt]
    exact Option.some.inj ((List.getElem?_eq_getElem hk_lt).symm.trans (h1.symm.trans hk))
  exact hgx ▸ List.getElem_mem hk_lt

private theorem sig_pre {xs pre post : List Fn} {f f0 g : Fn} {k i : Nat}
    (hnd : (xs.map Fn.name).Nodup) (hsplit : xs = pre ++ f :: post)
    (hi : xs[i]? = some f0) (heq : f.name = f0.name)
    (hk : xs[k]? = some g) (hlt : k < i) {sg : SigEntry} (hsg : g.sig = sg)
    {befores : List (Sym × List Fn)} :
    sg ∈ pre.map Fn.sig ++ (pre.flatMap fun x => (mfPatchInsAt befores x).map Fn.sig) :=
  List.mem_append_left _ (hsg ▸ sig_mem_pre_of_lt_idx hnd hsplit hi heq hk hlt)

private theorem sig_pre4 {xs pre post : List Fn} {f f0 g : Fn} {k i : Nat}
    (hnd : (xs.map Fn.name).Nodup) (hsplit : xs = pre ++ f :: post)
    (hi : xs[i]? = some f0) (heq : f.name = f0.name)
    (hk : xs[k]? = some g) (hlt : k < i) {sg : SigEntry} (hsg : g.sig = sg)
    {befores : List (Sym × List Fn)} :
    sg ∈ pre.map Fn.sig ++ (pre.flatMap fun x => (mfPatchInsAt befores x).map Fn.sig) ++
      (mfPatchInsAt befores f).map Fn.sig :=
  List.mem_append_left _ (List.mem_append_left _
    (hsg ▸ sig_mem_pre_of_lt_idx hnd hsplit hi heq hk hlt))

/-! ## 3. Well-Formedness, Lengths & `m7Fns` Index Certificates -/

theorem m7PlusNonMsTailRepls_wf : ∀ r ∈ m7PlusNonMsTailRepls, r.Wf := by
  intro r hr
  simp only [m7PlusNonMsTailRepls, m7ParityBvaTiePatchFns, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)
  · exact full_bva_commit_m7_wf
  · exact full_analyze_rsn_m7_wf
  · exact full_compact_needed_m7fix_wf
  · exact full_compact_mark_live_m7fix_wf
  · exact full_sweep_copy_m7fix_wf
  · exact full_forward_sub_m7v5_wf
  · exact m7PlusEliminate_wf
  · exact full_bva_pick_cand_bt_wf
  · exact full_probe_tail_bt_wf
  · exact full_probe_bt_wf

theorem m7PlusMsRepls_wf : ∀ r ∈ m7PlusMsRepls, r.Wf := by
  intro r hr
  simp only [m7PlusMsRepls, List.mem_append] at hr
  rcases hr with (h1 | h2) | h3
  · exact m7msRepls_wf r h1
  · exact m7ParityVivTiersPatchFns_wf r h2
  · exact m7PlusNonMsTailRepls_wf r h3

theorem m7FidNonMsHeadRepls_wf : ∀ r ∈ m7FidNonMsHeadRepls, r.Wf := by
  intro r hr
  simp only [m7FidNonMsHeadRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_bva_commit_m7_wf
  · exact full_analyze_rsn_m7_wf
  · exact full_compact_needed_m7fix_wf
  · exact full_compact_mark_live_m7fix_wf
  · exact full_sweep_copy_m7fix_wf
  · exact full_forward_sub_m7v5_wf
  · exact full_ilog10_fid_wf

theorem m7FidMsRepls_wf : ∀ r ∈ m7FidMsRepls, r.Wf := by
  intro r hr
  simp only [m7FidMsRepls, List.mem_append] at hr
  rcases hr with ((((h1 | h2) | h3) | h4) | h5) | h6
  · exact m7msRepls_wf r h1
  · exact m7FidNonMsHeadRepls_wf r h2
  · exact m7ParityVivTiersPatchFns_wf r h3
  · exact fidSchedFix_fns_wf r h4
  · exact fidCorePatchFns_wf r h5
  · exact fidSearchPatchRepls_wf r h6

theorem m7FidMsBefores_wf : ∀ p ∈ m7FidMsBefores, ∀ h ∈ p.2, h.Wf := by
  intro p hp h hh
  rcases List.mem_append.mp hp with h1 | h2
  · exact m7msBefores_wf p h1 h hh
  · exact m7FidBefores_wf p h2 h hh

theorem m7PlusMemShrinkFns_wf : ∀ f ∈ m7PlusMemShrinkFns, f.Wf :=
  mfPatchFns_wf m7Fns_wf m7PlusMsRepls_wf m7msBefores_wf

theorem m7FidelityMemShrinkFns_wf : ∀ f ∈ m7FidelityMemShrinkFns, f.Wf :=
  mfPatchFns_wf m7Fns_wf m7FidMsRepls_wf m7FidMsBefores_wf

theorem m7PlusMsRepls_length : m7PlusMsRepls.length = 27 := by rfl
theorem m7FidMsRepls_length : m7FidMsRepls.length = 39 := by rfl
theorem m7PlusMsRepls_names_nodup : (m7PlusMsRepls.map Fn.name).Nodup := by decide
theorem m7FidMsRepls_names_nodup : (m7FidMsRepls.map Fn.name).Nodup := by decide

theorem m7PlusMemShrinkFns_length : m7PlusMemShrinkFns.length = 412 := by
  have hsum : (m7Fns.map (fun f => (mfPatchInsAt m7PlusMsBefores f).length)).sum = 2 := by
    t_kernel_rfl
  dsimp only [m7PlusMemShrinkFns]
  rw [msPatchFns_length_sum, FullM7Proof.m7Fns_length, hsum]

theorem m7FidelityMemShrinkFns_length : m7FidelityMemShrinkFns.length = 415 := by
  have hsum : (m7Fns.map (fun f => (mfPatchInsAt m7FidMsBefores f).length)).sum = 5 := by
    t_kernel_rfl
  dsimp only [m7FidelityMemShrinkFns]
  rw [msPatchFns_length_sum, FullM7Proof.m7Fns_length, hsum]

theorem m7PlusMemShrink_noExit : m7PlusMemShrinkModule.exits = [] := rfl
theorem m7FidelityMemShrink_noExit : m7FidelityMemShrinkModule.exits = [] := rfl

private theorem ms_p1 {k : Nat} (hk : k < 112) {s : SigEntry}
    (h : m7FnsPart1[k]?.map Fn.sig = some s) : m7Fns[k]?.map Fn.sig = some s := by
  rw [m7_get_p1 hk]; exact h

private theorem ms_p2 {k : Nat} (hk : k < 164) {s : SigEntry}
    (h : m7FnsPart2[k]?.map Fn.sig = some s) : m7Fns[112 + k]?.map Fn.sig = some s := by
  rw [m7_get_p2 hk]; exact h

private theorem ms_p3 {k : Nat} {s : SigEntry}
    (h : m7FnsPart3[k]?.map Fn.sig = some s) : m7Fns[276 + k]?.map Fn.sig = some s := by
  rw [m7_get_p3]; exact h

private theorem ms_idx_5 : m7Fns[5]?.map Fn.sig =
    some ("kissat_parse_header", [i64, i64, i64], [.bool]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_8 : m7Fns[8]?.map Fn.sig =
    some ("full_isqrt", [i64], [i64]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_9 : m7Fns[9]?.map Fn.sig =
    some ("full_ilog10", [i64], [i64]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_10 : m7Fns[10]?.map Fn.sig =
    some ("full_rng_next", [i64], [i64]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_11 : m7Fns[11]?.map Fn.sig =
    some ("full_arena_next", [i64, i32], [i32]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_12 : m7Fns[12]?.map Fn.sig =
    some ("full_alloc_cl", [i64, i32, i32, .bool], [i64]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_17 : m7Fns[17]?.map Fn.sig =
    some ("full_wstack_defrag", [i64], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_18 : m7Fns[18]?.map Fn.sig =
    some ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]) :=
  ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_19 : m7Fns[19]?.map Fn.sig =
    some ("full_heap_up", [i64, i32], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_20 : m7Fns[20]?.map Fn.sig =
    some ("full_heap_down", [i64, i32], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_24 : m7Fns[24]?.map Fn.sig =
    some ("full_rescale", [i64], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_25 : m7Fns[25]?.map Fn.sig =
    some ("full_bump_var", [i64, i32], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_26 : m7Fns[26]?.map Fn.sig =
    some ("full_bump_decay", [i64], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_28 : m7Fns[28]?.map Fn.sig =
    some ("full_queue_mtf", [i64, i32], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_31 : m7Fns[31]?.map Fn.sig =
    some ("full_log10_q16_m7", [i64], [i64]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_32 : m7Fns[32]?.map Fn.sig =
    some ("full_scale_delta_m5", [i64, i64], [i64]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_34 : m7Fns[34]?.map Fn.sig =
    some ("full_scale_delta", [i64, i64], [i64]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_35 : m7Fns[35]?.map Fn.sig =
    some ("full_assign_lvl", [i64, i32, i32, i32], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_39 : m7Fns[39]?.map Fn.sig =
    some ("full_backtrack", [i64, i64], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_41 : m7Fns[41]?.map Fn.sig =
    some ("full_zero_tables1", [i64], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_42 : m7Fns[42]?.map Fn.sig =
    some ("full_zero_tables2", [i64], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_43 : m7Fns[43]?.map Fn.sig =
    some ("full_fixed_bytes", [i64], [i64]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_44 : m7Fns[44]?.map Fn.sig =
    some ("full_init_ptrs", [i64, i64, i64], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_45 : m7Fns[45]?.map Fn.sig =
    some ("full_init_hdr", [i64, i64, i64, i64], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_46 : m7Fns[46]?.map Fn.sig =
    some ("full_calc_max_v", [i64, i64, i64, i64], [i64]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_47 : m7Fns[47]?.map Fn.sig =
    some ("full_calc_ext_cap_m5", [i64], [i64]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_48 : m7Fns[48]?.map Fn.sig =
    some ("full_calc_scr_cap_m5", [i64], [i64]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_49 : m7Fns[49]?.map Fn.sig =
    some ("full_init_arenas", [i64, i64, i64, i64], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_50 : m7Fns[50]?.map Fn.sig =
    some ("full_init_state_m5", [i64, i64, i64, i64, i64], [.bool]) :=
  ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_51 : m7Fns[51]?.map Fn.sig =
    some ("full_init_state", [i64, i64, i64, i64, i64], [.bool]) :=
  ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_56 : m7Fns[56]?.map Fn.sig =
    some ("m6_ext_ensure_init", [i64], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_59 : m7Fns[59]?.map Fn.sig =
    some ("m6_hdr_sync_legacy_tiers", [i64], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_61 : m7Fns[61]?.map Fn.sig =
    some ("m6_hdr_recompute_tiers", [i64], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_66 : m7Fns[66]?.map Fn.sig =
    some ("m6_hdr_delaying", [i64, i64], [.bool]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_67 : m7Fns[67]?.map Fn.sig =
    some ("m6_hdr_bump_delay", [i64, i64], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_68 : m7Fns[68]?.map Fn.sig =
    some ("m6_hdr_reduce_delay", [i64, i64], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_70 : m7Fns[70]?.map Fn.sig =
    some ("m6_hdr_get_watermark", [i64, i64], [i64]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_71 : m7Fns[71]?.map Fn.sig =
    some ("m6_hdr_set_watermark", [i64, i64, i64], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_73 : m7Fns[73]?.map Fn.sig =
    some ("m6_hdr_dr_init", [i64], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_75 : m7Fns[75]?.map Fn.sig =
    some ("m6_hdr_dr_allow", [i64], [.bool]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_80 : m7Fns[80]?.map Fn.sig =
    some ("full_unwatch_large", [i64, i32, i32], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_81 : m7Fns[81]?.map Fn.sig =
    some ("full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool]) :=
  ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_82 : m7Fns[82]?.map Fn.sig =
    some ("full_prop_chrono_hot", [i64, i64], [.bool]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_83 : m7Fns[83]?.map Fn.sig =
    some ("full_propagate_ignore_hot", [i64, i64], [i64]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_85 : m7Fns[85]?.map Fn.sig =
    some ("full_propagate_ignore", [i64, i64], [i64]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_86 : m7Fns[86]?.map Fn.sig =
    some ("full_propagate", [i64], [i64]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_97 : m7Fns[97]?.map Fn.sig =
    some ("full_sweep_copy", [i64, i64, i64, i32, .bool], [i64]) :=
  ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_104 : m7Fns[104]?.map Fn.sig =
    some ("full_arena_sweep", [i64], [i64]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_105 : m7Fns[105]?.map Fn.sig =
    some ("full_mark_reasons", [i64, .bool], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_109 : m7Fns[109]?.map Fn.sig =
    some ("full_sort_reds", [i64, i64], []) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_111 : m7Fns[111]?.map Fn.sig =
    some ("full_reduce_m6", [i64, .bool], [i64]) := ms_p1 (by decide) (by t_kernel_rfl)
private theorem ms_idx_112 : m7Fns[112]?.map Fn.sig =
    some ("full_analyze_lit", [i64, i32, i32], [.bool]) :=
  ms_p2 (k := 0) (by decide) (by t_kernel_rfl)
private theorem ms_idx_113 : m7Fns[113]?.map Fn.sig =
    some ("full_analyze_rsn", [i64, i32, i32], [.bool]) :=
  ms_p2 (k := 1) (by decide) (by t_kernel_rfl)
private theorem ms_idx_117 : m7Fns[117]?.map Fn.sig =
    some ("full_sort_ana_qs_m6", [i64, i64], []) := ms_p2 (k := 5) (by decide) (by t_kernel_rfl)
private theorem ms_idx_118 : m7Fns[118]?.map Fn.sig =
    some ("full_bump_analyzed_m6_hdr", [i64], []) := ms_p2 (k := 6) (by decide) (by t_kernel_rfl)
private theorem ms_idx_124 : m7Fns[124]?.map Fn.sig =
    some ("full_min_mark", [i64, i32, i8], []) := ms_p2 (k := 12) (by decide) (by t_kernel_rfl)
private theorem ms_idx_129 : m7Fns[129]?.map Fn.sig =
    some ("full_sort_tmp", [i64], []) := ms_p2 (k := 17) (by decide) (by t_kernel_rfl)
private theorem ms_idx_130 : m7Fns[130]?.map Fn.sig =
    some ("full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool]) :=
  ms_p2 (k := 18) (by decide) (by t_kernel_rfl)
private theorem ms_idx_133 : m7Fns[133]?.map Fn.sig =
    some ("full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool]) :=
  ms_p2 (k := 21) (by decide) (by t_kernel_rfl)
private theorem ms_idx_135 : m7Fns[135]?.map Fn.sig =
    some ("full_min_shrink_m6", [i64], []) := ms_p2 (k := 23) (by decide) (by t_kernel_rfl)
private theorem ms_idx_151 : m7Fns[151]?.map Fn.sig =
    some ("full_analyze_m6_hdr", [i64], [i64]) := ms_p2 (k := 39) (by decide) (by t_kernel_rfl)
private theorem ms_idx_154 : m7Fns[154]?.map Fn.sig =
    some ("full_walk_cb_inv_m7", [i64, i64, i64], [i64]) :=
  ms_p2 (k := 42) (by decide) (by t_kernel_rfl)
private theorem ms_idx_155 : m7Fns[155]?.map Fn.sig =
    some ("full_walk_init_table_m7", [i64, i64], []) :=
  ms_p2 (k := 43) (by decide) (by t_kernel_rfl)
private theorem ms_idx_156 : m7Fns[156]?.map Fn.sig =
    some ("full_walk_effort_m7", [i64, i64], [i64]) :=
  ms_p2 (k := 44) (by decide) (by t_kernel_rfl)
private theorem ms_idx_157 : m7Fns[157]?.map Fn.sig =
    some ("full_walk_init_vals_m7", [i64], []) := ms_p2 (k := 45) (by decide) (by t_kernel_rfl)
private theorem ms_idx_158 : m7Fns[158]?.map Fn.sig =
    some ("full_walk_collect_m7", [i64], [i64]) := ms_p2 (k := 46) (by decide) (by t_kernel_rfl)
private theorem ms_idx_159 : m7Fns[159]?.map Fn.sig =
    some ("full_walk_build_occ_m7", [i64, i64], [i64]) :=
  ms_p2 (k := 47) (by decide) (by t_kernel_rfl)
private theorem ms_idx_161 : m7Fns[161]?.map Fn.sig =
    some ("full_walk_pick_m7", [i64, i32, i64], [i64]) :=
  ms_p2 (k := 49) (by decide) (by t_kernel_rfl)
private theorem ms_idx_162 : m7Fns[162]?.map Fn.sig =
    some ("full_walk_flip_m7", [i64, i32, i64, i64], [i64]) :=
  ms_p2 (k := 50) (by decide) (by t_kernel_rfl)
private theorem ms_idx_163 : m7Fns[163]?.map Fn.sig =
    some ("full_walk_save_min_m7", [i64, i64, .bool], []) :=
  ms_p2 (k := 51) (by decide) (by t_kernel_rfl)
private theorem ms_idx_164 : m7Fns[164]?.map Fn.sig =
    some ("full_walk_m7", [i64], []) := ms_p2 (k := 52) (by decide) (by t_kernel_rfl)
private theorem ms_idx_169 : m7Fns[169]?.map Fn.sig =
    some ("full_rephase", [i64], []) := ms_p2 (k := 57) (by decide) (by t_kernel_rfl)
private theorem ms_idx_170 : m7Fns[170]?.map Fn.sig =
    some ("full_restart_due", [i64], [i64]) := ms_p2 (k := 58) (by decide) (by t_kernel_rfl)
private theorem ms_idx_171 : m7Fns[171]?.map Fn.sig =
    some ("full_restart", [i64], []) := ms_p2 (k := 59) (by decide) (by t_kernel_rfl)
private theorem ms_idx_178 : m7Fns[178]?.map Fn.sig =
    some ("full_add_bin", [i64, i32, i32], [i64]) := ms_p2 (k := 66) (by decide) (by t_kernel_rfl)
private theorem ms_idx_179 : m7Fns[179]?.map Fn.sig =
    some ("full_delete_binary", [i64, i32, i32], []) :=
  ms_p2 (k := 67) (by decide) (by t_kernel_rfl)
private theorem ms_idx_184 : m7Fns[184]?.map Fn.sig =
    some ("full_lucky", [i64], [i64]) := ms_p2 (k := 72) (by decide) (by t_kernel_rfl)
private theorem ms_idx_190 : m7Fns[190]?.map Fn.sig =
    some ("full_probe_run", [i64, i64], [i64]) := ms_p2 (k := 78) (by decide) (by t_kernel_rfl)
private theorem ms_idx_209 : m7Fns[209]?.map Fn.sig =
    some ("full_viv_clause_m6", [i64, i32], [i64]) := ms_p2 (k := 97) (by decide) (by t_kernel_rfl)
private theorem ms_idx_211 : m7Fns[211]?.map Fn.sig =
    some ("full_viv_collect_m6", [i64, i64], [i64]) := ms_p2 (k := 99) (by decide) (by t_kernel_rfl)
private theorem ms_idx_212 : m7Fns[212]?.map Fn.sig =
    some ("full_viv_count_m6", [i64, i64], []) := ms_p2 (k := 100) (by decide) (by t_kernel_rfl)
private theorem ms_idx_213 : m7Fns[213]?.map Fn.sig =
    some ("full_viv_keys_m6", [i64, i64], []) := ms_p2 (k := 101) (by decide) (by t_kernel_rfl)
private theorem ms_idx_214 : m7Fns[214]?.map Fn.sig =
    some ("full_viv_sort_sched_m6", [i64, i64], []) :=
  ms_p2 (k := 102) (by decide) (by t_kernel_rfl)
private theorem ms_idx_215 : m7Fns[215]?.map Fn.sig =
    some ("full_viv_clear_tier_m6", [i64, i64], []) :=
  ms_p2 (k := 103) (by decide) (by t_kernel_rfl)
private theorem ms_idx_217 : m7Fns[217]?.map Fn.sig =
    some ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64]) :=
  ms_p2 (k := 105) (by decide) (by t_kernel_rfl)
private theorem ms_idx_218 : m7Fns[218]?.map Fn.sig =
    some ("full_vivify_m6_hdr", [i64], [i64]) := ms_p2 (k := 106) (by decide) (by t_kernel_rfl)
private theorem ms_idx_226 : m7Fns[226]?.map Fn.sig =
    some ("full_backbone_m6", [i64, i64], [i64]) := ms_p2 (k := 114) (by decide) (by t_kernel_rfl)
private theorem ms_idx_229 : m7Fns[229]?.map Fn.sig =
    some ("full_transitive_m6", [i64, i64], [i64]) := ms_p2 (k := 117) (by decide) (by t_kernel_rfl)
private theorem ms_idx_235 : m7Fns[235]?.map Fn.sig =
    some ("full_substitute", [i64], [i64]) := ms_p2 (k := 123) (by decide) (by t_kernel_rfl)
private theorem ms_idx_236 : m7Fns[236]?.map Fn.sig =
    some ("full_enter_dense", [i64], [.bool]) := ms_p2 (k := 124) (by decide) (by t_kernel_rfl)
private theorem ms_idx_237 : m7Fns[237]?.map Fn.sig =
    some ("full_rebuild_watches", [i64], [i64]) := ms_p2 (k := 125) (by decide) (by t_kernel_rfl)
private theorem ms_idx_275 : m7Fns[275]?.map Fn.sig =
    some ("full_congruence_dense", [i64, i64], [i64]) :=
  ms_p2 (k := 163) (by decide) (by t_kernel_rfl)
private theorem ms_idx_299 : m7Fns[299]?.map Fn.sig =
    some ("full_sweep_dense_m6", [i64, i64, i64], [i64]) := ms_p3 (k := 23) (by t_kernel_rfl)
private theorem ms_idx_300 : m7Fns[300]?.map Fn.sig =
    some ("full_fwd_dedup_bins", [i64], [.bool]) := ms_p3 (k := 24) (by t_kernel_rfl)
private theorem ms_idx_302 : m7Fns[302]?.map Fn.sig =
    some ("full_dense_flush_units_m7", [i64], [.bool]) := ms_p3 (k := 26) (by t_kernel_rfl)
private theorem ms_idx_303 : m7Fns[303]?.map Fn.sig =
    some ("full_fwd_flush_large_m7", [i64], []) := ms_p3 (k := 27) (by t_kernel_rfl)
private theorem ms_idx_304 : m7Fns[304]?.map Fn.sig =
    some ("full_fwd_reconnect_irred_m7", [i64], []) := ms_p3 (k := 28) (by t_kernel_rfl)
private theorem ms_idx_306 : m7Fns[306]?.map Fn.sig =
    some ("full_fwd_check_cl_m7", [i64, i32], [.bool]) := ms_p3 (k := 30) (by t_kernel_rfl)
private theorem ms_idx_307 : m7Fns[307]?.map Fn.sig =
    some ("full_fwd_connect_subsumer_m7", [i64, i32], []) := ms_p3 (k := 31) (by t_kernel_rfl)
private theorem ms_idx_308 : m7Fns[308]?.map Fn.sig =
    some ("full_fwd_collect_sort_m7", [i64], [i64]) := ms_p3 (k := 32) (by t_kernel_rfl)
private theorem ms_idx_311 : m7Fns[311]?.map Fn.sig =
    some ("full_forward_sub", [i64, i64], [i64]) := ms_p3 (k := 35) (by t_kernel_rfl)
private theorem ms_idx_338 : m7Fns[338]?.map Fn.sig =
    some ("full_bve_var_m7", [i64, i32], [i64]) := ms_p3 (k := 62) (by t_kernel_rfl)
private theorem ms_idx_340 : m7Fns[340]?.map Fn.sig =
    some ("full_init_fresh_var", [i64, i32], []) := ms_p3 (k := 64) (by t_kernel_rfl)
private theorem ms_idx_345 : m7Fns[345]?.map Fn.sig =
    some ("full_bva_scan_cands", [i64, i32, i32, i64], [i32]) := ms_p3 (k := 69) (by t_kernel_rfl)
private theorem ms_idx_346 : m7Fns[346]?.map Fn.sig =
    some ("full_bva_pick_cand", [i64, i32, i32], [i32]) := ms_p3 (k := 70) (by t_kernel_rfl)
private theorem ms_idx_347 : m7Fns[347]?.map Fn.sig =
    some ("full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32]) :=
  ms_p3 (k := 71) (by t_kernel_rfl)
private theorem ms_idx_348 : m7Fns[348]?.map Fn.sig =
    some ("full_bva_commit", [i64, i32], [.bool]) := ms_p3 (k := 72) (by t_kernel_rfl)
private theorem ms_idx_352 : m7Fns[352]?.map Fn.sig =
    some ("full_factor", [i64, i64], [i64]) := ms_p3 (k := 76) (by t_kernel_rfl)
private theorem ms_idx_353 : m7Fns[353]?.map Fn.sig =
    some ("full_compact_needed", [i64], [.bool]) := ms_p3 (k := 77) (by t_kernel_rfl)
private theorem ms_idx_355 : m7Fns[355]?.map Fn.sig =
    some ("full_compact_mark_live", [i64], []) := ms_p3 (k := 79) (by t_kernel_rfl)
private theorem ms_idx_360 : m7Fns[360]?.map Fn.sig =
    some ("full_compact_vars", [i64, i64, i64], []) := ms_p3 (k := 84) (by t_kernel_rfl)
private theorem ms_idx_365 : m7Fns[365]?.map Fn.sig =
    some ("full_compact", [i64], [i64]) := ms_p3 (k := 89) (by t_kernel_rfl)
private theorem ms_idx_368 : m7Fns[368]?.map Fn.sig =
    some ("full_reorder_queue_m7", [i64], [i64]) := ms_p3 (k := 92) (by t_kernel_rfl)
private theorem ms_idx_369 : m7Fns[369]?.map Fn.sig =
    some ("full_reorder_m6", [i64, i64], [i64]) := ms_p3 (k := 93) (by t_kernel_rfl)
private theorem ms_idx_374 : m7Fns[374]?.map Fn.sig =
    some ("full_min_u64", [i64, i64], [i64]) := ms_p3 (k := 98) (by t_kernel_rfl)
private theorem ms_idx_376 : m7Fns[376]?.map Fn.sig =
    some ("full_elim_dticks", [i64, .bool], [i64]) := ms_p3 (k := 100) (by t_kernel_rfl)
private theorem ms_idx_380 : m7Fns[380]?.map Fn.sig =
    some ("full_bve_heap_push_m7", [i64, i64, i32], [i64]) := ms_p3 (k := 104) (by t_kernel_rfl)
private theorem ms_idx_381 : m7Fns[381]?.map Fn.sig =
    some ("full_bve_heap_pop_m7", [i64, i64], [i32]) := ms_p3 (k := 105) (by t_kernel_rfl)
private theorem ms_idx_382 : m7Fns[382]?.map Fn.sig =
    some ("full_bve_collect_nbrs_m7", [i64, i32], [i64]) := ms_p3 (k := 106) (by t_kernel_rfl)
private theorem ms_idx_383 : m7Fns[383]?.map Fn.sig =
    some ("full_elim_bve_m7", [i64, i64], [i64]) := ms_p3 (k := 107) (by t_kernel_rfl)
private theorem ms_idx_385 : m7Fns[385]?.map Fn.sig =
    some ("full_eliminate_m6", [i64, .bool], [i64]) := ms_p3 (k := 109) (by t_kernel_rfl)
private theorem ms_idx_388 : m7Fns[388]?.map Fn.sig =
    some ("full_m7_set64", [i64, i64, i64], []) := ms_p3 (k := 112) (by t_kernel_rfl)
private theorem ms_idx_394 : m7Fns[394]?.map Fn.sig =
    some ("full_lucky_late_m7", [i64], [i64]) := ms_p3 (k := 118) (by t_kernel_rfl)
private theorem ms_idx_397 : m7Fns[397]?.map Fn.sig =
    some ("full_decide_m7", [i64], [i64]) := ms_p3 (k := 121) (by t_kernel_rfl)
private theorem ms_idx_398 : m7Fns[398]?.map Fn.sig =
    some ("full_ema_swap_m7", [i64, i64, i64], []) := ms_p3 (k := 122) (by t_kernel_rfl)
private theorem ms_idx_399 : m7Fns[399]?.map Fn.sig =
    some ("full_switch_mode_m7", [i64], []) := ms_p3 (k := 123) (by t_kernel_rfl)
private theorem ms_idx_400 : m7Fns[400]?.map Fn.sig =
    some ("full_probe_dticks_m6_hdr", [i64, .bool], [i64]) := ms_p3 (k := 124) (by t_kernel_rfl)
private theorem ms_idx_401 : m7Fns[401]?.map Fn.sig =
    some ("full_probe_tail_m6", [i64, i64], [i64]) := ms_p3 (k := 125) (by t_kernel_rfl)
private theorem ms_idx_402 : m7Fns[402]?.map Fn.sig =
    some ("full_probe_m6", [i64, .bool], [i64]) := ms_p3 (k := 126) (by t_kernel_rfl)
private theorem ms_idx_403 : m7Fns[403]?.map Fn.sig =
    some ("full_preprocess_m6", [i64], [i64]) := ms_p3 (k := 127) (by t_kernel_rfl)
private theorem ms_idx_404 : m7Fns[404]?.map Fn.sig =
    some ("full_simplify_m6", [i64, .bool, .bool], [i64]) := ms_p3 (k := 128) (by t_kernel_rfl)
private theorem ms_idx_405 : m7Fns[405]?.map Fn.sig =
    some ("full_search_m6", [i64], [i64]) := ms_p3 (k := 129) (by t_kernel_rfl)

theorem m7Fns_not_mem_fill : "full_fill_u64_m7" ∉ m7Fns.map Fn.name := by
  have hc : (m7Fns.map Fn.name).contains "full_fill_u64_m7" = false := by t_kernel_rfl
  exact fun hm => absurd hm (by simpa using hc)

theorem m7Fns_not_mem_trans : "full_trans_bytes_m7" ∉ m7Fns.map Fn.name := by
  have hc : (m7Fns.map Fn.name).contains "full_trans_bytes_m7" = false := by t_kernel_rfl
  exact fun hm => absurd hm (by simpa using hc)

private theorem ms_filter_ne {a b : Sym} {v : List Fn} (hb : (a == b) = false) :
    (if a == b then some v else none) = none := by
  rw [hb]; rfl

theorem m7PlusMs_insAt_cases (f : Fn) :
    mfPatchInsAt m7PlusMsBefores f = [] ∨
      (f.name = "full_zero_tables1" ∧ mfPatchInsAt m7PlusMsBefores f = [m7msFillU64Fn]) ∨
      (f.name = "full_calc_max_v" ∧ mfPatchInsAt m7PlusMsBefores f = [m7msTransBytesFn]) := by
  by_cases h1 : f.name = "full_zero_tables1"
  · right; left; refine ⟨h1, ?_⟩
    dsimp only [mfPatchInsAt, m7PlusMsBefores, m7msBefores]; rw [h1]; rfl
  · by_cases h2 : f.name = "full_calc_max_v"
    · right; right; refine ⟨h2, ?_⟩
      dsimp only [mfPatchInsAt, m7PlusMsBefores, m7msBefores]; rw [h2]; rfl
    · left
      have hb1 : ("full_zero_tables1" == f.name) = false := beq_false_of_ne (Ne.symm h1)
      have hb2 : ("full_calc_max_v" == f.name) = false := beq_false_of_ne (Ne.symm h2)
      dsimp only [mfPatchInsAt, m7PlusMsBefores, m7msBefores]
      rw [List.filterMap_cons, ms_filter_ne hb1, List.filterMap_cons, ms_filter_ne hb2]
      rfl

theorem m7FidMs_insAt_cases (f : Fn) :
    mfPatchInsAt m7FidMsBefores f = [] ∨
      (f.name = "full_zero_tables1" ∧ mfPatchInsAt m7FidMsBefores f = [m7msFillU64Fn]) ∨
      (f.name = "full_calc_max_v" ∧ mfPatchInsAt m7FidMsBefores f = [m7msTransBytesFn]) ∨
      (f.name = "full_bva_filter_row" ∧ mfPatchInsAt m7FidMsBefores f = [fidBvaMatchLargeFidFn]) ∨
      (f.name = "full_reorder_queue_m7" ∧ mfPatchInsAt m7FidMsBefores f = [fidReorderSiftFidFn]) ∨
      (f.name = "full_search_m6" ∧ mfPatchInsAt m7FidMsBefores f = [fidHdrDecideFn]) := by
  by_cases h1 : f.name = "full_zero_tables1"
  · right; left; refine ⟨h1, ?_⟩
    dsimp only [mfPatchInsAt, m7FidMsBefores, m7msBefores, m7FidBefores,
      fidCorePatchBefores, fidSearchPatchBefores]
    rw [h1]; rfl
  · by_cases h2 : f.name = "full_calc_max_v"
    · right; right; left; refine ⟨h2, ?_⟩
      dsimp only [mfPatchInsAt, m7FidMsBefores, m7msBefores, m7FidBefores,
        fidCorePatchBefores, fidSearchPatchBefores]
      rw [h2]; rfl
    · by_cases h3 : f.name = "full_bva_filter_row"
      · right; right; right; left; refine ⟨h3, ?_⟩
        dsimp only [mfPatchInsAt, m7FidMsBefores, m7msBefores, m7FidBefores,
          fidCorePatchBefores, fidSearchPatchBefores]
        rw [h3]; rfl
      · by_cases h4 : f.name = "full_reorder_queue_m7"
        · right; right; right; right; left; refine ⟨h4, ?_⟩
          dsimp only [mfPatchInsAt, m7FidMsBefores, m7msBefores, m7FidBefores,
            fidCorePatchBefores, fidSearchPatchBefores]
          rw [h4]; rfl
        · by_cases h5 : f.name = "full_search_m6"
          · right; right; right; right; right; refine ⟨h5, ?_⟩
            dsimp only [mfPatchInsAt, m7FidMsBefores, m7msBefores, m7FidBefores,
              fidCorePatchBefores, fidSearchPatchBefores]
            rw [h5]; rfl
          · left
            have hb1 : ("full_zero_tables1" == f.name) = false := beq_false_of_ne (Ne.symm h1)
            have hb2 : ("full_calc_max_v" == f.name) = false := beq_false_of_ne (Ne.symm h2)
            have hb3 : ("full_bva_filter_row" == f.name) = false := beq_false_of_ne (Ne.symm h3)
            have hb4 : ("full_reorder_queue_m7" == f.name) = false := beq_false_of_ne (Ne.symm h4)
            have hb5 : ("full_search_m6" == f.name) = false := beq_false_of_ne (Ne.symm h5)
            dsimp only [mfPatchInsAt, m7FidMsBefores, m7msBefores, m7FidBefores,
              fidCorePatchBefores, fidSearchPatchBefores, List.cons_append, List.nil_append]
            rw [List.filterMap_cons, ms_filter_ne hb1, List.filterMap_cons, ms_filter_ne hb2,
              List.filterMap_cons, ms_filter_ne hb3, List.filterMap_cons, ms_filter_ne hb4,
              List.filterMap_cons, ms_filter_ne hb5]
            rfl

/-! ## 4. Signature, `Nodup` & Fast Acyclicity Proofs (`m7PlusMemShrink` & `m7FidelityMemShrink`) -/

private theorem m7PlusMsRepls_sigs :
    ∀ r ∈ m7PlusMsRepls, ∀ f ∈ m7Fns, r.name = f.name → r.sig = f.sig := by
  obtain ⟨f41, hf41, hs41⟩ := sig_of_map_idx ms_idx_41
  obtain ⟨f42, hf42, hs42⟩ := sig_of_map_idx ms_idx_42
  obtain ⟨f43, hf43, hs43⟩ := sig_of_map_idx ms_idx_43
  obtain ⟨f44, hf44, hs44⟩ := sig_of_map_idx ms_idx_44
  obtain ⟨f45, hf45, hs45⟩ := sig_of_map_idx ms_idx_45
  obtain ⟨f46, hf46, hs46⟩ := sig_of_map_idx ms_idx_46
  obtain ⟨f47, hf47, hs47⟩ := sig_of_map_idx ms_idx_47
  obtain ⟨f48, hf48, hs48⟩ := sig_of_map_idx ms_idx_48
  obtain ⟨f49, hf49, hs49⟩ := sig_of_map_idx ms_idx_49
  obtain ⟨f50, hf50, hs50⟩ := sig_of_map_idx ms_idx_50
  obtain ⟨f51, hf51, hs51⟩ := sig_of_map_idx ms_idx_51
  obtain ⟨f59, hf59, hs59⟩ := sig_of_map_idx ms_idx_59
  obtain ⟨f83, hf83, hs83⟩ := sig_of_map_idx ms_idx_83
  obtain ⟨f85, hf85, hs85⟩ := sig_of_map_idx ms_idx_85
  obtain ⟨f97, hf97, hs97⟩ := sig_of_map_idx ms_idx_97
  obtain ⟨f113, hf113, hs113⟩ := sig_of_map_idx ms_idx_113
  obtain ⟨f217, hf217, hs217⟩ := sig_of_map_idx ms_idx_217
  obtain ⟨f218, hf218, hs218⟩ := sig_of_map_idx ms_idx_218
  obtain ⟨f311, hf311, hs311⟩ := sig_of_map_idx ms_idx_311
  obtain ⟨f346, hf346, hs346⟩ := sig_of_map_idx ms_idx_346
  obtain ⟨f348, hf348, hs348⟩ := sig_of_map_idx ms_idx_348
  obtain ⟨f353, hf353, hs353⟩ := sig_of_map_idx ms_idx_353
  obtain ⟨f355, hf355, hs355⟩ := sig_of_map_idx ms_idx_355
  obtain ⟨f360, hf360, hs360⟩ := sig_of_map_idx ms_idx_360
  obtain ⟨f385, hf385, hs385⟩ := sig_of_map_idx ms_idx_385
  obtain ⟨f401, hf401, hs401⟩ := sig_of_map_idx ms_idx_401
  obtain ⟨f402, hf402, hs402⟩ := sig_of_map_idx ms_idx_402
  intro r hr f hf hnm
  simp only [m7PlusMsRepls, m7msRepls, m7ParityVivTiersPatchFns, m7PlusNonMsTailRepls,
    m7ParityBvaTiePatchFns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with
    ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
     (rfl | rfl | rfl | rfl | rfl)) |
    ((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl))
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf41 (hnm.symm.trans (congrArg Prod.fst hs41.symm))) ▸ hs41.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf42 (hnm.symm.trans (congrArg Prod.fst hs42.symm))) ▸ hs42.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf43 (hnm.symm.trans (congrArg Prod.fst hs43.symm))) ▸ hs43.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf44 (hnm.symm.trans (congrArg Prod.fst hs44.symm))) ▸ hs44.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf45 (hnm.symm.trans (congrArg Prod.fst hs45.symm))) ▸ hs45.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf46 (hnm.symm.trans (congrArg Prod.fst hs46.symm))) ▸ hs46.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf47 (hnm.symm.trans (congrArg Prod.fst hs47.symm))) ▸ hs47.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf48 (hnm.symm.trans (congrArg Prod.fst hs48.symm))) ▸ hs48.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf49 (hnm.symm.trans (congrArg Prod.fst hs49.symm))) ▸ hs49.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf50 (hnm.symm.trans (congrArg Prod.fst hs50.symm))) ▸ hs50.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf51 (hnm.symm.trans (congrArg Prod.fst hs51.symm))) ▸ hs51.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf360 (hnm.symm.trans (congrArg Prod.fst hs360.symm))) ▸ hs360.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf59 (hnm.symm.trans (congrArg Prod.fst hs59.symm))) ▸ hs59.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf83 (hnm.symm.trans (congrArg Prod.fst hs83.symm))) ▸ hs83.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf85 (hnm.symm.trans (congrArg Prod.fst hs85.symm))) ▸ hs85.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf217 (hnm.symm.trans (congrArg Prod.fst hs217.symm))) ▸ hs217.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf218 (hnm.symm.trans (congrArg Prod.fst hs218.symm))) ▸ hs218.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf348 (hnm.symm.trans (congrArg Prod.fst hs348.symm))) ▸ hs348.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf113 (hnm.symm.trans (congrArg Prod.fst hs113.symm))) ▸ hs113.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf353 (hnm.symm.trans (congrArg Prod.fst hs353.symm))) ▸ hs353.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf355 (hnm.symm.trans (congrArg Prod.fst hs355.symm))) ▸ hs355.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf97 (hnm.symm.trans (congrArg Prod.fst hs97.symm))) ▸ hs97.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf311 (hnm.symm.trans (congrArg Prod.fst hs311.symm))) ▸ hs311.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf385 (hnm.symm.trans (congrArg Prod.fst hs385.symm))) ▸ hs385.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf346 (hnm.symm.trans (congrArg Prod.fst hs346.symm))) ▸ hs346.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf401 (hnm.symm.trans (congrArg Prod.fst hs401.symm))) ▸ hs401.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf402 (hnm.symm.trans (congrArg Prod.fst hs402.symm))) ▸ hs402.symm

private theorem m7FidMsRepls_sigs :
    ∀ r ∈ m7FidMsRepls, ∀ f ∈ m7Fns, r.name = f.name → r.sig = f.sig := by
  obtain ⟨f9, hf9, hs9⟩ := sig_of_map_idx ms_idx_9
  obtain ⟨f41, hf41, hs41⟩ := sig_of_map_idx ms_idx_41
  obtain ⟨f42, hf42, hs42⟩ := sig_of_map_idx ms_idx_42
  obtain ⟨f43, hf43, hs43⟩ := sig_of_map_idx ms_idx_43
  obtain ⟨f44, hf44, hs44⟩ := sig_of_map_idx ms_idx_44
  obtain ⟨f45, hf45, hs45⟩ := sig_of_map_idx ms_idx_45
  obtain ⟨f46, hf46, hs46⟩ := sig_of_map_idx ms_idx_46
  obtain ⟨f47, hf47, hs47⟩ := sig_of_map_idx ms_idx_47
  obtain ⟨f48, hf48, hs48⟩ := sig_of_map_idx ms_idx_48
  obtain ⟨f49, hf49, hs49⟩ := sig_of_map_idx ms_idx_49
  obtain ⟨f50, hf50, hs50⟩ := sig_of_map_idx ms_idx_50
  obtain ⟨f51, hf51, hs51⟩ := sig_of_map_idx ms_idx_51
  obtain ⟨f59, hf59, hs59⟩ := sig_of_map_idx ms_idx_59
  obtain ⟨f83, hf83, hs83⟩ := sig_of_map_idx ms_idx_83
  obtain ⟨f85, hf85, hs85⟩ := sig_of_map_idx ms_idx_85
  obtain ⟨f97, hf97, hs97⟩ := sig_of_map_idx ms_idx_97
  obtain ⟨f111, hf111, hs111⟩ := sig_of_map_idx ms_idx_111
  obtain ⟨f113, hf113, hs113⟩ := sig_of_map_idx ms_idx_113
  obtain ⟨f118, hf118, hs118⟩ := sig_of_map_idx ms_idx_118
  obtain ⟨f135, hf135, hs135⟩ := sig_of_map_idx ms_idx_135
  obtain ⟨f164, hf164, hs164⟩ := sig_of_map_idx ms_idx_164
  obtain ⟨f217, hf217, hs217⟩ := sig_of_map_idx ms_idx_217
  obtain ⟨f218, hf218, hs218⟩ := sig_of_map_idx ms_idx_218
  obtain ⟨f311, hf311, hs311⟩ := sig_of_map_idx ms_idx_311
  obtain ⟨f345, hf345, hs345⟩ := sig_of_map_idx ms_idx_345
  obtain ⟨f347, hf347, hs347⟩ := sig_of_map_idx ms_idx_347
  obtain ⟨f348, hf348, hs348⟩ := sig_of_map_idx ms_idx_348
  obtain ⟨f353, hf353, hs353⟩ := sig_of_map_idx ms_idx_353
  obtain ⟨f355, hf355, hs355⟩ := sig_of_map_idx ms_idx_355
  obtain ⟨f360, hf360, hs360⟩ := sig_of_map_idx ms_idx_360
  obtain ⟨f368, hf368, hs368⟩ := sig_of_map_idx ms_idx_368
  obtain ⟨f369, hf369, hs369⟩ := sig_of_map_idx ms_idx_369
  obtain ⟨f383, hf383, hs383⟩ := sig_of_map_idx ms_idx_383
  obtain ⟨f385, hf385, hs385⟩ := sig_of_map_idx ms_idx_385
  obtain ⟨f399, hf399, hs399⟩ := sig_of_map_idx ms_idx_399
  obtain ⟨f401, hf401, hs401⟩ := sig_of_map_idx ms_idx_401
  obtain ⟨f402, hf402, hs402⟩ := sig_of_map_idx ms_idx_402
  obtain ⟨f403, hf403, hs403⟩ := sig_of_map_idx ms_idx_403
  obtain ⟨f405, hf405, hs405⟩ := sig_of_map_idx ms_idx_405
  intro r hr f hf hnm
  rw [m7FidMsRepls, fidSchedFixPatchFns, fidSchedFixFns_eq_patchFns] at hr
  simp only [m7msRepls, m7FidNonMsHeadRepls, m7ParityVivTiersPatchFns, fidCorePatchFns,
    fidSearchPatchRepls, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with
    (((((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
       (rfl | rfl | rfl | rfl | rfl | rfl | rfl)) |
      (rfl | rfl | rfl | rfl | rfl)) |
     (rfl | rfl | rfl | rfl | rfl)) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl)) |
    (rfl | rfl | rfl)
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf41 (hnm.symm.trans (congrArg Prod.fst hs41.symm))) ▸ hs41.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf42 (hnm.symm.trans (congrArg Prod.fst hs42.symm))) ▸ hs42.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf43 (hnm.symm.trans (congrArg Prod.fst hs43.symm))) ▸ hs43.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf44 (hnm.symm.trans (congrArg Prod.fst hs44.symm))) ▸ hs44.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf45 (hnm.symm.trans (congrArg Prod.fst hs45.symm))) ▸ hs45.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf46 (hnm.symm.trans (congrArg Prod.fst hs46.symm))) ▸ hs46.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf47 (hnm.symm.trans (congrArg Prod.fst hs47.symm))) ▸ hs47.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf48 (hnm.symm.trans (congrArg Prod.fst hs48.symm))) ▸ hs48.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf49 (hnm.symm.trans (congrArg Prod.fst hs49.symm))) ▸ hs49.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf50 (hnm.symm.trans (congrArg Prod.fst hs50.symm))) ▸ hs50.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf51 (hnm.symm.trans (congrArg Prod.fst hs51.symm))) ▸ hs51.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf360 (hnm.symm.trans (congrArg Prod.fst hs360.symm))) ▸ hs360.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf348 (hnm.symm.trans (congrArg Prod.fst hs348.symm))) ▸ hs348.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf113 (hnm.symm.trans (congrArg Prod.fst hs113.symm))) ▸ hs113.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf353 (hnm.symm.trans (congrArg Prod.fst hs353.symm))) ▸ hs353.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf355 (hnm.symm.trans (congrArg Prod.fst hs355.symm))) ▸ hs355.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf97 (hnm.symm.trans (congrArg Prod.fst hs97.symm))) ▸ hs97.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf311 (hnm.symm.trans (congrArg Prod.fst hs311.symm))) ▸ hs311.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf9 (hnm.symm.trans (congrArg Prod.fst hs9.symm))) ▸ hs9.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf59 (hnm.symm.trans (congrArg Prod.fst hs59.symm))) ▸ hs59.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf83 (hnm.symm.trans (congrArg Prod.fst hs83.symm))) ▸ hs83.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf85 (hnm.symm.trans (congrArg Prod.fst hs85.symm))) ▸ hs85.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf217 (hnm.symm.trans (congrArg Prod.fst hs217.symm))) ▸ hs217.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf218 (hnm.symm.trans (congrArg Prod.fst hs218.symm))) ▸ hs218.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf111 (hnm.symm.trans (congrArg Prod.fst hs111.symm))) ▸ hs111.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf385 (hnm.symm.trans (congrArg Prod.fst hs385.symm))) ▸ hs385.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf401 (hnm.symm.trans (congrArg Prod.fst hs401.symm))) ▸ hs401.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf402 (hnm.symm.trans (congrArg Prod.fst hs402.symm))) ▸ hs402.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf403 (hnm.symm.trans (congrArg Prod.fst hs403.symm))) ▸ hs403.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf135 (hnm.symm.trans (congrArg Prod.fst hs135.symm))) ▸ hs135.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf345 (hnm.symm.trans (congrArg Prod.fst hs345.symm))) ▸ hs345.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf347 (hnm.symm.trans (congrArg Prod.fst hs347.symm))) ▸ hs347.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf368 (hnm.symm.trans (congrArg Prod.fst hs368.symm))) ▸ hs368.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf369 (hnm.symm.trans (congrArg Prod.fst hs369.symm))) ▸ hs369.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf383 (hnm.symm.trans (congrArg Prod.fst hs383.symm))) ▸ hs383.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf164 (hnm.symm.trans (congrArg Prod.fst hs164.symm))) ▸ hs164.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf118 (hnm.symm.trans (congrArg Prod.fst hs118.symm))) ▸ hs118.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf399 (hnm.symm.trans (congrArg Prod.fst hs399.symm))) ▸ hs399.symm
  · exact (fn_eq_of_mem_idx m7_names_nodup hf hf405 (hnm.symm.trans (congrArg Prod.fst hs405.symm))) ▸ hs405.symm

theorem m7PlusMemShrinkFns_names_nodup : (m7PlusMemShrinkFns.map Fn.name).Nodup := by
  refine msPatchFns_names_nodup m7_names_nodup m7PlusMsRepls_sigs ?_ ?_ ?_
  · intro f _
    rcases m7PlusMs_insAt_cases f with h | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> simp
  · intro f _ h hh
    rcases m7PlusMs_insAt_cases f with h0 | ⟨_, h1⟩ | ⟨_, h2⟩
    · rw [h0] at hh; cases hh
    · rw [h1, List.mem_singleton] at hh; subst hh; exact m7Fns_not_mem_fill
    · rw [h2, List.mem_singleton] at hh; subst hh; exact m7Fns_not_mem_trans
  · intro f₁ _ f₂ _ hne h hh hm
    rcases m7PlusMs_insAt_cases f₁ with h1 | ⟨he1, hp1⟩ | ⟨he1, hp1⟩
    · rw [h1] at hh; cases hh
    · rw [hp1, List.mem_singleton] at hh; subst hh
      rcases m7PlusMs_insAt_cases f₂ with h2 | ⟨he2, _⟩ | ⟨_, hp2⟩
      · rw [h2] at hm; cases hm
      · exact hne (he1.trans he2.symm)
      · rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
    · rw [hp1, List.mem_singleton] at hh; subst hh
      rcases m7PlusMs_insAt_cases f₂ with h2 | ⟨_, hp2⟩ | ⟨he2, _⟩
      · rw [h2] at hm; cases hm
      · rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
      · exact hne (he1.trans he2.symm)

theorem m7FidelityMemShrinkFns_names_nodup : (m7FidelityMemShrinkFns.map Fn.name).Nodup := by
  refine msPatchFns_names_nodup m7_names_nodup m7FidMsRepls_sigs ?_ ?_ ?_
  · intro f _
    rcases m7FidMs_insAt_cases f with h | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;>
      rw [h] <;> simp
  · intro f _ h hh
    rcases m7FidMs_insAt_cases f with h0 | ⟨_, h1⟩ | ⟨_, h2⟩ | ⟨_, h3⟩ | ⟨_, h4⟩ | ⟨_, h5⟩
    · rw [h0] at hh; cases hh
    · rw [h1, List.mem_singleton] at hh; subst hh; exact m7Fns_not_mem_fill
    · rw [h2, List.mem_singleton] at hh; subst hh; exact m7Fns_not_mem_trans
    · rw [h3, List.mem_singleton] at hh; subst hh; exact m7Fns_not_mem_bml
    · rw [h4, List.mem_singleton] at hh; subst hh; exact m7Fns_not_mem_sift
    · rw [h5, List.mem_singleton] at hh; subst hh; exact m7Fns_not_mem_hdec
  · intro f₁ _ f₂ _ hne h hh hm
    rcases m7FidMs_insAt_cases f₁ with
      h1 | ⟨he1, hp1⟩ | ⟨he1, hp1⟩ | ⟨he1, hp1⟩ | ⟨he1, hp1⟩ | ⟨he1, hp1⟩
    · rw [h1] at hh; cases hh
    · rw [hp1, List.mem_singleton] at hh; subst hh
      rcases m7FidMs_insAt_cases f₂ with h2 | ⟨he2, _⟩ | ⟨_, hp2⟩ | ⟨_, hp2⟩ | ⟨_, hp2⟩ | ⟨_, hp2⟩
      · rw [h2] at hm; cases hm
      · exact hne (he1.trans he2.symm)
      all_goals
        rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
    · rw [hp1, List.mem_singleton] at hh; subst hh
      rcases m7FidMs_insAt_cases f₂ with h2 | ⟨_, hp2⟩ | ⟨he2, _⟩ | ⟨_, hp2⟩ | ⟨_, hp2⟩ | ⟨_, hp2⟩
      · rw [h2] at hm; cases hm
      · rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
      · exact hne (he1.trans he2.symm)
      all_goals
        rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
    · rw [hp1, List.mem_singleton] at hh; subst hh
      rcases m7FidMs_insAt_cases f₂ with h2 | ⟨_, hp2⟩ | ⟨_, hp2⟩ | ⟨he2, _⟩ | ⟨_, hp2⟩ | ⟨_, hp2⟩
      · rw [h2] at hm; cases hm
      · rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
      · rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
      · exact hne (he1.trans he2.symm)
      all_goals
        rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
    · rw [hp1, List.mem_singleton] at hh; subst hh
      rcases m7FidMs_insAt_cases f₂ with h2 | ⟨_, hp2⟩ | ⟨_, hp2⟩ | ⟨_, hp2⟩ | ⟨he2, _⟩ | ⟨_, hp2⟩
      · rw [h2] at hm; cases hm
      · rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
      · rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
      · rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
      · exact hne (he1.trans he2.symm)
      · rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
    · rw [hp1, List.mem_singleton] at hh; subst hh
      rcases m7FidMs_insAt_cases f₂ with h2 | ⟨_, hp2⟩ | ⟨_, hp2⟩ | ⟨_, hp2⟩ | ⟨_, hp2⟩ | ⟨he2, _⟩
      · rw [h2] at hm; cases hm
      · rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
      · rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
      · rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
      · rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
      · exact hne (he1.trans he2.symm)

theorem m7PlusMemShrink_acyclic : m7PlusMemShrinkModule.checkAcyclic = true := by
  obtain ⟨g5, hg5, hsg5⟩ := sig_of_map_idx ms_idx_5
  obtain ⟨g9, hg9, hsg9⟩ := sig_of_map_idx ms_idx_9
  obtain ⟨g11, hg11, hsg11⟩ := sig_of_map_idx ms_idx_11
  obtain ⟨g12, hg12, hsg12⟩ := sig_of_map_idx ms_idx_12
  obtain ⟨g17, hg17, hsg17⟩ := sig_of_map_idx ms_idx_17
  obtain ⟨g18, hg18, hsg18⟩ := sig_of_map_idx ms_idx_18
  obtain ⟨g32, hg32, hsg32⟩ := sig_of_map_idx ms_idx_32
  obtain ⟨g34, hg34, hsg34⟩ := sig_of_map_idx ms_idx_34
  obtain ⟨g35, hg35, hsg35⟩ := sig_of_map_idx ms_idx_35
  obtain ⟨g39, hg39, hsg39⟩ := sig_of_map_idx ms_idx_39
  obtain ⟨g41, hg41, hsg41⟩ := sig_of_map_idx ms_idx_41
  obtain ⟨g42, hg42, hsg42⟩ := sig_of_map_idx ms_idx_42
  obtain ⟨g43, hg43, hsg43⟩ := sig_of_map_idx ms_idx_43
  obtain ⟨g44, hg44, hsg44⟩ := sig_of_map_idx ms_idx_44
  obtain ⟨g45, hg45, hsg45⟩ := sig_of_map_idx ms_idx_45
  obtain ⟨g46, hg46, hsg46⟩ := sig_of_map_idx ms_idx_46
  obtain ⟨g47, hg47, hsg47⟩ := sig_of_map_idx ms_idx_47
  obtain ⟨g48, hg48, hsg48⟩ := sig_of_map_idx ms_idx_48
  obtain ⟨g49, hg49, hsg49⟩ := sig_of_map_idx ms_idx_49
  obtain ⟨g50, hg50, hsg50⟩ := sig_of_map_idx ms_idx_50
  obtain ⟨g51, hg51, hsg51⟩ := sig_of_map_idx ms_idx_51
  obtain ⟨g56, hg56, hsg56⟩ := sig_of_map_idx ms_idx_56
  obtain ⟨g59, hg59, hsg59⟩ := sig_of_map_idx ms_idx_59
  obtain ⟨g66, hg66, hsg66⟩ := sig_of_map_idx ms_idx_66
  obtain ⟨g67, hg67, hsg67⟩ := sig_of_map_idx ms_idx_67
  obtain ⟨g68, hg68, hsg68⟩ := sig_of_map_idx ms_idx_68
  obtain ⟨g70, hg70, hsg70⟩ := sig_of_map_idx ms_idx_70
  obtain ⟨g71, hg71, hsg71⟩ := sig_of_map_idx ms_idx_71
  obtain ⟨g80, hg80, hsg80⟩ := sig_of_map_idx ms_idx_80
  obtain ⟨g81, hg81, hsg81⟩ := sig_of_map_idx ms_idx_81
  obtain ⟨g82, hg82, hsg82⟩ := sig_of_map_idx ms_idx_82
  obtain ⟨g83, hg83, hsg83⟩ := sig_of_map_idx ms_idx_83
  obtain ⟨g85, hg85, hsg85⟩ := sig_of_map_idx ms_idx_85
  obtain ⟨g86, hg86, hsg86⟩ := sig_of_map_idx ms_idx_86
  obtain ⟨g97, hg97, hsg97⟩ := sig_of_map_idx ms_idx_97
  obtain ⟨g112, hg112, hsg112⟩ := sig_of_map_idx ms_idx_112
  obtain ⟨g113, hg113, hsg113⟩ := sig_of_map_idx ms_idx_113
  obtain ⟨g178, hg178, hsg178⟩ := sig_of_map_idx ms_idx_178
  obtain ⟨g179, hg179, hsg179⟩ := sig_of_map_idx ms_idx_179
  obtain ⟨g190, hg190, hsg190⟩ := sig_of_map_idx ms_idx_190
  obtain ⟨g209, hg209, hsg209⟩ := sig_of_map_idx ms_idx_209
  obtain ⟨g211, hg211, hsg211⟩ := sig_of_map_idx ms_idx_211
  obtain ⟨g212, hg212, hsg212⟩ := sig_of_map_idx ms_idx_212
  obtain ⟨g213, hg213, hsg213⟩ := sig_of_map_idx ms_idx_213
  obtain ⟨g214, hg214, hsg214⟩ := sig_of_map_idx ms_idx_214
  obtain ⟨g215, hg215, hsg215⟩ := sig_of_map_idx ms_idx_215
  obtain ⟨g217, hg217, hsg217⟩ := sig_of_map_idx ms_idx_217
  obtain ⟨g218, hg218, hsg218⟩ := sig_of_map_idx ms_idx_218
  obtain ⟨g226, hg226, hsg226⟩ := sig_of_map_idx ms_idx_226
  obtain ⟨g229, hg229, hsg229⟩ := sig_of_map_idx ms_idx_229
  obtain ⟨g235, hg235, hsg235⟩ := sig_of_map_idx ms_idx_235
  obtain ⟨g236, hg236, hsg236⟩ := sig_of_map_idx ms_idx_236
  obtain ⟨g237, hg237, hsg237⟩ := sig_of_map_idx ms_idx_237
  obtain ⟨g275, hg275, hsg275⟩ := sig_of_map_idx ms_idx_275
  obtain ⟨g299, hg299, hsg299⟩ := sig_of_map_idx ms_idx_299
  obtain ⟨g300, hg300, hsg300⟩ := sig_of_map_idx ms_idx_300
  obtain ⟨g302, hg302, hsg302⟩ := sig_of_map_idx ms_idx_302
  obtain ⟨g303, hg303, hsg303⟩ := sig_of_map_idx ms_idx_303
  obtain ⟨g304, hg304, hsg304⟩ := sig_of_map_idx ms_idx_304
  obtain ⟨g306, hg306, hsg306⟩ := sig_of_map_idx ms_idx_306
  obtain ⟨g307, hg307, hsg307⟩ := sig_of_map_idx ms_idx_307
  obtain ⟨g308, hg308, hsg308⟩ := sig_of_map_idx ms_idx_308
  obtain ⟨g311, hg311, hsg311⟩ := sig_of_map_idx ms_idx_311
  obtain ⟨g340, hg340, hsg340⟩ := sig_of_map_idx ms_idx_340
  obtain ⟨g346, hg346, hsg346⟩ := sig_of_map_idx ms_idx_346
  obtain ⟨g348, hg348, hsg348⟩ := sig_of_map_idx ms_idx_348
  obtain ⟨g352, hg352, hsg352⟩ := sig_of_map_idx ms_idx_352
  obtain ⟨g353, hg353, hsg353⟩ := sig_of_map_idx ms_idx_353
  obtain ⟨g355, hg355, hsg355⟩ := sig_of_map_idx ms_idx_355
  obtain ⟨g360, hg360, hsg360⟩ := sig_of_map_idx ms_idx_360
  obtain ⟨g374, hg374, hsg374⟩ := sig_of_map_idx ms_idx_374
  obtain ⟨g376, hg376, hsg376⟩ := sig_of_map_idx ms_idx_376
  obtain ⟨g383, hg383, hsg383⟩ := sig_of_map_idx ms_idx_383
  obtain ⟨g385, hg385, hsg385⟩ := sig_of_map_idx ms_idx_385
  obtain ⟨g400, hg400, hsg400⟩ := sig_of_map_idx ms_idx_400
  obtain ⟨g401, hg401, hsg401⟩ := sig_of_map_idx ms_idx_401
  obtain ⟨g402, hg402, hsg402⟩ := sig_of_map_idx ms_idx_402
  change ({ m7Module with fns := mfPatchFns m7PlusMsRepls m7PlusMsBefores m7Module.fns } :
    LeanQbe.T.Module).checkAcyclic = true
  refine msPatchModule_checkAcyclic (M := m7Module) ?_ m7_acyclic m7PlusMsRepls_sigs ?_ ?_
  · have hnd := m7PlusMemShrinkFns_names_nodup
    dsimp only [m7PlusMemShrinkFns] at hnd
    simpa only [m7Module, List.map_nil, List.append_nil] using hnd
  · intro pre f post _
    simp only [m7Module, List.map_nil]
    rcases m7PlusMs_insAt_cases f with h0 | ⟨_, h1⟩ | ⟨_, h2⟩
    · rw [h0]; rfl
    · rw [h1]
      have hb : m7msFillU64Fn.checkCallsOk [] [] = true := by rfl
      have hm := fn_checkCallsOk_mono (a₂ := pre.map Fn.sig ++
          (pre.flatMap fun x => (mfPatchInsAt m7PlusMsBefores x).map Fn.sig))
        (fun _ h => False.elim (List.not_mem_nil h)) hb
      dsimp only [LeanQbe.T.Module.checkFnsCallsOk]
      rw [List.append_nil, hm]; rfl
    · rw [h2]
      have hb : m7msTransBytesFn.checkCallsOk [] [] = true := by rfl
      have hm := fn_checkCallsOk_mono (a₂ := pre.map Fn.sig ++
          (pre.flatMap fun x => (mfPatchInsAt m7PlusMsBefores x).map Fn.sig))
        (fun _ h => False.elim (List.not_mem_nil h)) hb
      dsimp only [LeanQbe.T.Module.checkFnsCallsOk]
      rw [List.append_nil, hm]; rfl
  · intro pre f post r hsplit hr hnm
    simp only [m7Module, List.map_nil, List.append_nil] at hsplit ⊢
    simp only [m7PlusMsRepls, m7msRepls, m7ParityVivTiersPatchFns, m7PlusNonMsTailRepls,
      m7ParityBvaTiePatchFns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with
      ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
       (rfl | rfl | rfl | rfl | rfl)) |
      ((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl))
    -- 1. m7msZeroTables1Fn (41)
    · have hp : mfPatchInsAt m7PlusMsBefores f = [m7msFillU64Fn] := by
        dsimp only [mfPatchInsAt, m7PlusMsBefores, m7msBefores]; rw [hnm.symm]; rfl
      have hc : m7msZeroTables1Fn.checkCallsOk
          [("full_fill_u64_m7", [i64, i64, i64], [])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact List.mem_append_right _ (by rw [hp]; simp [m7msFillU64Fn, Fn.sig])
    -- 2. m7msZeroTables2Fn (42)
    · have hn0 : f.name = g42.name := hnm.symm.trans (congrArg Prod.fst hsg42.symm)
      have hg41_pre : g41 ∈ pre := fn_mem_pre_of_lt_idx m7_names_nodup hsplit hg42 hn0 hg41 (by decide)
      have hp41 : mfPatchInsAt m7PlusMsBefores g41 = [m7msFillU64Fn] := by
        dsimp only [mfPatchInsAt, m7PlusMsBefores, m7msBefores]
        rw [show g41.name = "full_zero_tables1" from congrArg Prod.fst hsg41]; rfl
      have hc : m7msZeroTables2Fn.checkCallsOk
          [("full_fill_u64_m7", [i64, i64, i64], [])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨g41, hg41_pre, by rw [hp41]; simp [m7msFillU64Fn, Fn.sig]⟩))
    -- 3. m7msFixedBytesFn (43)
    · exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h))
        (by rfl : m7msFixedBytesFn.checkCallsOk [] [] = true)
    -- 4. m7msInitPtrsFn (44)
    · exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h))
        (by rfl : m7msInitPtrsFn.checkCallsOk [] [] = true)
    -- 5. m7msInitHdrFn (45)
    · exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h))
        (by rfl : m7msInitHdrFn.checkCallsOk [] [] = true)
    -- 6. m7msCalcMaxVFn (46)
    · have hn0 : f.name = g46.name := hnm.symm.trans (congrArg Prod.fst hsg46.symm)
      have hp : mfPatchInsAt m7PlusMsBefores f = [m7msTransBytesFn] := by
        dsimp only [mfPatchInsAt, m7PlusMsBefores, m7msBefores]; rw [hnm.symm]; rfl
      have hc : m7msCalcMaxVFn.checkCallsOk
          [ ("full_fixed_bytes", [i64], [i64])
          , ("full_trans_bytes_m7", [i64], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg46 hn0 hg43 (by decide) hsg43
      · exact List.mem_append_right _ (by rw [hp]; simp [m7msTransBytesFn, Fn.sig])
    -- 7. m7msCalcExtCapM5Fn (47)
    · exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h))
        (by rfl : m7msCalcExtCapM5Fn.checkCallsOk [] [] = true)
    -- 8. m7msCalcScrCapM5Fn (48)
    · exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h))
        (by rfl : m7msCalcScrCapM5Fn.checkCallsOk [] [] = true)
    -- 9. m7msInitArenasFn (49)
    · have hn0 : f.name = g49.name := hnm.symm.trans (congrArg Prod.fst hsg49.symm)
      have hc : m7msInitArenasFn.checkCallsOk [("full_init_ptrs", [i64, i64, i64], [])] [] = true :=
        by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact sig_pre4 m7_names_nodup hsplit hg49 hn0 hg44 (by decide) hsg44
    -- 10. m7msInitStateM5Fn (50)
    · have hn0 : f.name = g50.name := hnm.symm.trans (congrArg Prod.fst hsg50.symm)
      have hg46_pre : g46 ∈ pre := fn_mem_pre_of_lt_idx m7_names_nodup hsplit hg50 hn0 hg46 (by decide)
      have hp46 : mfPatchInsAt m7PlusMsBefores g46 = [m7msTransBytesFn] := by
        dsimp only [mfPatchInsAt, m7PlusMsBefores, m7msBefores]
        rw [show g46.name = "full_calc_max_v" from congrArg Prod.fst hsg46]; rfl
      have hc : m7msInitStateM5Fn.checkCallsOk
          [ ("kissat_parse_header", [i64, i64, i64], [.bool])
          , ("full_fixed_bytes", [i64], [i64])
          , ("full_trans_bytes_m7", [i64], [i64])
          , ("full_calc_max_v", [i64, i64, i64, i64], [i64])
          , ("full_calc_ext_cap_m5", [i64], [i64])
          , ("full_calc_scr_cap_m5", [i64], [i64])
          , ("full_init_arenas", [i64, i64, i64, i64], [])
          , ("full_init_hdr", [i64, i64, i64, i64], [])
          , ("full_zero_tables1", [i64], [])
          , ("full_zero_tables2", [i64], []) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg50 hn0 hg5 (by decide) hsg5
      · exact sig_pre4 m7_names_nodup hsplit hg50 hn0 hg43 (by decide) hsg43
      · exact List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨g46, hg46_pre, by rw [hp46]; simp [m7msTransBytesFn, Fn.sig]⟩))
      · exact sig_pre4 m7_names_nodup hsplit hg50 hn0 hg46 (by decide) hsg46
      · exact sig_pre4 m7_names_nodup hsplit hg50 hn0 hg47 (by decide) hsg47
      · exact sig_pre4 m7_names_nodup hsplit hg50 hn0 hg48 (by decide) hsg48
      · exact sig_pre4 m7_names_nodup hsplit hg50 hn0 hg49 (by decide) hsg49
      · exact sig_pre4 m7_names_nodup hsplit hg50 hn0 hg45 (by decide) hsg45
      · exact sig_pre4 m7_names_nodup hsplit hg50 hn0 hg41 (by decide) hsg41
      · exact sig_pre4 m7_names_nodup hsplit hg50 hn0 hg42 (by decide) hsg42
    -- 11. m7msInitStateFn (51)
    · have hn0 : f.name = g51.name := hnm.symm.trans (congrArg Prod.fst hsg51.symm)
      have hc : m7msInitStateFn.checkCallsOk
          [("full_init_state_m5", [i64, i64, i64, i64, i64], [.bool])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact sig_pre4 m7_names_nodup hsplit hg51 hn0 hg50 (by decide) hsg50
    -- 12. m7msCompactVarsFn (360)
    · exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h))
        (by rfl : m7msCompactVarsFn.checkCallsOk [] [] = true)
    -- 13..17 m7ParityVivTiersPatchFns
    · have hn0 : f.name = g59.name := hnm.symm.trans (congrArg Prod.fst hsg59.symm)
      have hc : m7pSyncLegacyTiersFn.checkCallsOk [("m6_ext_ensure_init", [i64], [])] [] = true :=
        by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact sig_pre4 m7_names_nodup hsplit hg59 hn0 hg56 (by decide) hsg56
    · have hn0 : f.name = g83.name := hnm.symm.trans (congrArg Prod.fst hsg83.symm)
      have hc : m7pPropIgnoreHotFn.checkCallsOk
          [ ("full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool])
          , ("full_prop_chrono_hot", [i64, i64], [.bool]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg83 hn0 hg81 (by decide) hsg81
      · exact sig_pre4 m7_names_nodup hsplit hg83 hn0 hg82 (by decide) hsg82
    · have hn0 : f.name = g85.name := hnm.symm.trans (congrArg Prod.fst hsg85.symm)
      have hc : m7pPropIgnoreFn.checkCallsOk
          [ ("full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool])
          , ("full_prop_chrono_hot", [i64, i64], [.bool]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg85 hn0 hg81 (by decide) hsg81
      · exact sig_pre4 m7_names_nodup hsplit hg85 hn0 hg82 (by decide) hsg82
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
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg217 hn0 hg39 (by decide) hsg39
      · exact sig_pre4 m7_names_nodup hsplit hg217 hn0 hg211 (by decide) hsg211
      · exact sig_pre4 m7_names_nodup hsplit hg217 hn0 hg212 (by decide) hsg212
      · exact sig_pre4 m7_names_nodup hsplit hg217 hn0 hg213 (by decide) hsg213
      · exact sig_pre4 m7_names_nodup hsplit hg217 hn0 hg214 (by decide) hsg214
      · exact sig_pre4 m7_names_nodup hsplit hg217 hn0 hg209 (by decide) hsg209
      · exact sig_pre4 m7_names_nodup hsplit hg217 hn0 hg86 (by decide) hsg86
      · exact sig_pre4 m7_names_nodup hsplit hg217 hn0 hg215 (by decide) hsg215
    · have hn0 : f.name = g218.name := hnm.symm.trans (congrArg Prod.fst hsg218.symm)
      have hc : m7pVivifyFn.checkCallsOk
          [ ("full_backtrack", [i64, i64], [])
          , ("m6_hdr_sync_legacy_tiers", [i64], [])
          , ("m6_hdr_get_watermark", [i64, i64], [i64])
          , ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg218 hn0 hg39 (by decide) hsg39
      · exact sig_pre4 m7_names_nodup hsplit hg218 hn0 hg59 (by decide) hsg59
      · exact sig_pre4 m7_names_nodup hsplit hg218 hn0 hg70 (by decide) hsg70
      · exact sig_pre4 m7_names_nodup hsplit hg218 hn0 hg217 (by decide) hsg217
    -- 18..24 m7PlusNonMsTailRepls head
    · have hn0 : f.name = g348.name := hnm.symm.trans (congrArg Prod.fst hsg348.symm)
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
      · exact sig_pre4 m7_names_nodup hsplit hg348 hn0 hg12 (by decide) hsg12
      · exact sig_pre4 m7_names_nodup hsplit hg348 hn0 hg17 (by decide) hsg17
      · exact sig_pre4 m7_names_nodup hsplit hg348 hn0 hg18 (by decide) hsg18
      · exact sig_pre4 m7_names_nodup hsplit hg348 hn0 hg80 (by decide) hsg80
      · exact sig_pre4 m7_names_nodup hsplit hg348 hn0 hg178 (by decide) hsg178
      · exact sig_pre4 m7_names_nodup hsplit hg348 hn0 hg179 (by decide) hsg179
      · exact sig_pre4 m7_names_nodup hsplit hg348 hn0 hg340 (by decide) hsg340
    · have hn0 : f.name = g113.name := hnm.symm.trans (congrArg Prod.fst hsg113.symm)
      have hc : m7AnalyzeRsnFn.checkCallsOk [("full_analyze_lit", [i64, i32, i32], [.bool])] [] =
          true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact sig_pre4 m7_names_nodup hsplit hg113 hn0 hg112 (by decide) hsg112
    · exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h))
        (by rfl : m7fixCompactNeededFn.checkCallsOk [] [] = true)
    · have hn0 : f.name = g355.name := hnm.symm.trans (congrArg Prod.fst hsg355.symm)
      have hc : m7fixCompactMarkLiveFn.checkCallsOk [("full_arena_next", [i64, i32], [i32])] [] =
          true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact sig_pre4 m7_names_nodup hsplit hg355 hn0 hg11 (by decide) hsg11
    · have hn0 : f.name = g97.name := hnm.symm.trans (congrArg Prod.fst hsg97.symm)
      have hc : m7fixSweepCopyFn.checkCallsOk
          [ ("full_assign_lvl", [i64, i32, i32, i32], [])
          , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg97 hn0 hg35 (by decide) hsg35
      · exact sig_pre4 m7_names_nodup hsplit hg97 hn0 hg18 (by decide) hsg18
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
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg311 hn0 hg300 (by decide) hsg300
      · exact sig_pre4 m7_names_nodup hsplit hg311 hn0 hg302 (by decide) hsg302
      · exact sig_pre4 m7_names_nodup hsplit hg311 hn0 hg308 (by decide) hsg308
      · exact sig_pre4 m7_names_nodup hsplit hg311 hn0 hg303 (by decide) hsg303
      · exact sig_pre4 m7_names_nodup hsplit hg311 hn0 hg306 (by decide) hsg306
      · exact sig_pre4 m7_names_nodup hsplit hg311 hn0 hg307 (by decide) hsg307
      · exact sig_pre4 m7_names_nodup hsplit hg311 hn0 hg11 (by decide) hsg11
      · exact sig_pre4 m7_names_nodup hsplit hg311 hn0 hg304 (by decide) hsg304
    · have hn0 : f.name = g385.name := hnm.symm.trans (congrArg Prod.fst hsg385.symm)
      have hc : m7PlusEliminateFn.checkCallsOk
          [ ("full_elim_dticks", [i64, .bool], [i64])
          , ("full_ilog10", [i64], [i64])
          , ("full_scale_delta", [i64, i64], [i64])
          , ("full_enter_dense", [i64], [.bool])
          , ("full_min_u64", [i64, i64], [i64])
          , ("full_forward_sub", [i64, i64], [i64])
          , ("full_elim_bve_m7", [i64, i64], [i64])
          , ("full_factor", [i64, i64], [i64])
          , ("full_rebuild_watches", [i64], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg385 hn0 hg376 (by decide) hsg376
      · exact sig_pre4 m7_names_nodup hsplit hg385 hn0 hg9 (by decide) hsg9
      · exact sig_pre4 m7_names_nodup hsplit hg385 hn0 hg34 (by decide) hsg34
      · exact sig_pre4 m7_names_nodup hsplit hg385 hn0 hg236 (by decide) hsg236
      · exact sig_pre4 m7_names_nodup hsplit hg385 hn0 hg374 (by decide) hsg374
      · exact sig_pre4 m7_names_nodup hsplit hg385 hn0 hg311 (by decide) hsg311
      · exact sig_pre4 m7_names_nodup hsplit hg385 hn0 hg383 (by decide) hsg383
      · exact sig_pre4 m7_names_nodup hsplit hg385 hn0 hg352 (by decide) hsg352
      · exact sig_pre4 m7_names_nodup hsplit hg385 hn0 hg237 (by decide) hsg237
    -- 25..27 m7ParityBvaTiePatchFns
    · exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h))
        (by rfl : m7btBvaPickCandFn.checkCallsOk [] [] = true)
    · have hn0 : f.name = g401.name := hnm.symm.trans (congrArg Prod.fst hsg401.symm)
      have hc : m7btProbeTailFn.checkCallsOk
          [ ("full_backbone_m6", [i64, i64], [i64])
          , ("full_transitive_m6", [i64, i64], [i64])
          , ("full_min_u64", [i64, i64], [i64])
          , ("full_probe_run", [i64, i64], [i64])
          , ("full_vivify_m6_hdr", [i64], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg401 hn0 hg226 (by decide) hsg226
      · exact sig_pre4 m7_names_nodup hsplit hg401 hn0 hg229 (by decide) hsg229
      · exact sig_pre4 m7_names_nodup hsplit hg401 hn0 hg374 (by decide) hsg374
      · exact sig_pre4 m7_names_nodup hsplit hg401 hn0 hg190 (by decide) hsg190
      · exact sig_pre4 m7_names_nodup hsplit hg401 hn0 hg218 (by decide) hsg218
    · have hn0 : f.name = g402.name := hnm.symm.trans (congrArg Prod.fst hsg402.symm)
      have hc : m7btProbeFn.checkCallsOk
          [ ("full_probe_dticks_m6_hdr", [i64, .bool], [i64])
          , ("full_ilog10", [i64], [i64])
          , ("full_scale_delta_m5", [i64, i64], [i64])
          , ("full_enter_dense", [i64], [.bool])
          , ("m6_hdr_delaying", [i64, i64], [.bool])
          , ("full_congruence_dense", [i64, i64], [i64])
          , ("full_rebuild_watches", [i64], [i64])
          , ("m6_hdr_set_watermark", [i64, i64, i64], [])
          , ("m6_hdr_reduce_delay", [i64, i64], [])
          , ("m6_hdr_bump_delay", [i64, i64], [])
          , ("full_sweep_dense_m6", [i64, i64, i64], [i64])
          , ("full_substitute", [i64], [i64])
          , ("full_probe_tail_m6", [i64, i64], [i64])
          , ("full_backbone_m6", [i64, i64], [i64])
          , ("full_min_u64", [i64, i64], [i64])
          , ("full_factor", [i64, i64], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg400 (by decide) hsg400
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg9 (by decide) hsg9
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg32 (by decide) hsg32
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg236 (by decide) hsg236
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg66 (by decide) hsg66
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg275 (by decide) hsg275
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg237 (by decide) hsg237
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg71 (by decide) hsg71
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg68 (by decide) hsg68
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg67 (by decide) hsg67
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg299 (by decide) hsg299
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg235 (by decide) hsg235
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg401 (by decide) hsg401
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg226 (by decide) hsg226
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg374 (by decide) hsg374
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg352 (by decide) hsg352

theorem m7FidelityMemShrink_acyclic : m7FidelityMemShrinkModule.checkAcyclic = true := by
  obtain ⟨g5, hg5, hsg5⟩ := sig_of_map_idx ms_idx_5
  obtain ⟨g8, hg8, hsg8⟩ := sig_of_map_idx ms_idx_8
  obtain ⟨g9, hg9, hsg9⟩ := sig_of_map_idx ms_idx_9
  obtain ⟨g10, hg10, hsg10⟩ := sig_of_map_idx ms_idx_10
  obtain ⟨g11, hg11, hsg11⟩ := sig_of_map_idx ms_idx_11
  obtain ⟨g12, hg12, hsg12⟩ := sig_of_map_idx ms_idx_12
  obtain ⟨g17, hg17, hsg17⟩ := sig_of_map_idx ms_idx_17
  obtain ⟨g18, hg18, hsg18⟩ := sig_of_map_idx ms_idx_18
  obtain ⟨g19, hg19, hsg19⟩ := sig_of_map_idx ms_idx_19
  obtain ⟨g20, hg20, hsg20⟩ := sig_of_map_idx ms_idx_20
  obtain ⟨g24, hg24, hsg24⟩ := sig_of_map_idx ms_idx_24
  obtain ⟨g25, hg25, hsg25⟩ := sig_of_map_idx ms_idx_25
  obtain ⟨g26, hg26, hsg26⟩ := sig_of_map_idx ms_idx_26
  obtain ⟨g28, hg28, hsg28⟩ := sig_of_map_idx ms_idx_28
  obtain ⟨g31, hg31, hsg31⟩ := sig_of_map_idx ms_idx_31
  obtain ⟨g32, hg32, hsg32⟩ := sig_of_map_idx ms_idx_32
  obtain ⟨g34, hg34, hsg34⟩ := sig_of_map_idx ms_idx_34
  obtain ⟨g35, hg35, hsg35⟩ := sig_of_map_idx ms_idx_35
  obtain ⟨g39, hg39, hsg39⟩ := sig_of_map_idx ms_idx_39
  obtain ⟨g41, hg41, hsg41⟩ := sig_of_map_idx ms_idx_41
  obtain ⟨g42, hg42, hsg42⟩ := sig_of_map_idx ms_idx_42
  obtain ⟨g43, hg43, hsg43⟩ := sig_of_map_idx ms_idx_43
  obtain ⟨g44, hg44, hsg44⟩ := sig_of_map_idx ms_idx_44
  obtain ⟨g45, hg45, hsg45⟩ := sig_of_map_idx ms_idx_45
  obtain ⟨g46, hg46, hsg46⟩ := sig_of_map_idx ms_idx_46
  obtain ⟨g47, hg47, hsg47⟩ := sig_of_map_idx ms_idx_47
  obtain ⟨g48, hg48, hsg48⟩ := sig_of_map_idx ms_idx_48
  obtain ⟨g49, hg49, hsg49⟩ := sig_of_map_idx ms_idx_49
  obtain ⟨g50, hg50, hsg50⟩ := sig_of_map_idx ms_idx_50
  obtain ⟨g51, hg51, hsg51⟩ := sig_of_map_idx ms_idx_51
  obtain ⟨g56, hg56, hsg56⟩ := sig_of_map_idx ms_idx_56
  obtain ⟨g59, hg59, hsg59⟩ := sig_of_map_idx ms_idx_59
  obtain ⟨g61, hg61, hsg61⟩ := sig_of_map_idx ms_idx_61
  obtain ⟨g66, hg66, hsg66⟩ := sig_of_map_idx ms_idx_66
  obtain ⟨g67, hg67, hsg67⟩ := sig_of_map_idx ms_idx_67
  obtain ⟨g68, hg68, hsg68⟩ := sig_of_map_idx ms_idx_68
  obtain ⟨g70, hg70, hsg70⟩ := sig_of_map_idx ms_idx_70
  obtain ⟨g71, hg71, hsg71⟩ := sig_of_map_idx ms_idx_71
  obtain ⟨g73, hg73, hsg73⟩ := sig_of_map_idx ms_idx_73
  obtain ⟨g75, hg75, hsg75⟩ := sig_of_map_idx ms_idx_75
  obtain ⟨g80, hg80, hsg80⟩ := sig_of_map_idx ms_idx_80
  obtain ⟨g81, hg81, hsg81⟩ := sig_of_map_idx ms_idx_81
  obtain ⟨g82, hg82, hsg82⟩ := sig_of_map_idx ms_idx_82
  obtain ⟨g83, hg83, hsg83⟩ := sig_of_map_idx ms_idx_83
  obtain ⟨g85, hg85, hsg85⟩ := sig_of_map_idx ms_idx_85
  obtain ⟨g86, hg86, hsg86⟩ := sig_of_map_idx ms_idx_86
  obtain ⟨g97, hg97, hsg97⟩ := sig_of_map_idx ms_idx_97
  obtain ⟨g104, hg104, hsg104⟩ := sig_of_map_idx ms_idx_104
  obtain ⟨g105, hg105, hsg105⟩ := sig_of_map_idx ms_idx_105
  obtain ⟨g109, hg109, hsg109⟩ := sig_of_map_idx ms_idx_109
  obtain ⟨g111, hg111, hsg111⟩ := sig_of_map_idx ms_idx_111
  obtain ⟨g112, hg112, hsg112⟩ := sig_of_map_idx ms_idx_112
  obtain ⟨g113, hg113, hsg113⟩ := sig_of_map_idx ms_idx_113
  obtain ⟨g117, hg117, hsg117⟩ := sig_of_map_idx ms_idx_117
  obtain ⟨g118, hg118, hsg118⟩ := sig_of_map_idx ms_idx_118
  obtain ⟨g124, hg124, hsg124⟩ := sig_of_map_idx ms_idx_124
  obtain ⟨g129, hg129, hsg129⟩ := sig_of_map_idx ms_idx_129
  obtain ⟨g130, hg130, hsg130⟩ := sig_of_map_idx ms_idx_130
  obtain ⟨g133, hg133, hsg133⟩ := sig_of_map_idx ms_idx_133
  obtain ⟨g135, hg135, hsg135⟩ := sig_of_map_idx ms_idx_135
  obtain ⟨g151, hg151, hsg151⟩ := sig_of_map_idx ms_idx_151
  obtain ⟨g154, hg154, hsg154⟩ := sig_of_map_idx ms_idx_154
  obtain ⟨g155, hg155, hsg155⟩ := sig_of_map_idx ms_idx_155
  obtain ⟨g156, hg156, hsg156⟩ := sig_of_map_idx ms_idx_156
  obtain ⟨g157, hg157, hsg157⟩ := sig_of_map_idx ms_idx_157
  obtain ⟨g158, hg158, hsg158⟩ := sig_of_map_idx ms_idx_158
  obtain ⟨g159, hg159, hsg159⟩ := sig_of_map_idx ms_idx_159
  obtain ⟨g161, hg161, hsg161⟩ := sig_of_map_idx ms_idx_161
  obtain ⟨g162, hg162, hsg162⟩ := sig_of_map_idx ms_idx_162
  obtain ⟨g163, hg163, hsg163⟩ := sig_of_map_idx ms_idx_163
  obtain ⟨g164, hg164, hsg164⟩ := sig_of_map_idx ms_idx_164
  obtain ⟨g169, hg169, hsg169⟩ := sig_of_map_idx ms_idx_169
  obtain ⟨g170, hg170, hsg170⟩ := sig_of_map_idx ms_idx_170
  obtain ⟨g171, hg171, hsg171⟩ := sig_of_map_idx ms_idx_171
  obtain ⟨g178, hg178, hsg178⟩ := sig_of_map_idx ms_idx_178
  obtain ⟨g179, hg179, hsg179⟩ := sig_of_map_idx ms_idx_179
  obtain ⟨g184, hg184, hsg184⟩ := sig_of_map_idx ms_idx_184
  obtain ⟨g209, hg209, hsg209⟩ := sig_of_map_idx ms_idx_209
  obtain ⟨g211, hg211, hsg211⟩ := sig_of_map_idx ms_idx_211
  obtain ⟨g212, hg212, hsg212⟩ := sig_of_map_idx ms_idx_212
  obtain ⟨g213, hg213, hsg213⟩ := sig_of_map_idx ms_idx_213
  obtain ⟨g214, hg214, hsg214⟩ := sig_of_map_idx ms_idx_214
  obtain ⟨g215, hg215, hsg215⟩ := sig_of_map_idx ms_idx_215
  obtain ⟨g217, hg217, hsg217⟩ := sig_of_map_idx ms_idx_217
  obtain ⟨g218, hg218, hsg218⟩ := sig_of_map_idx ms_idx_218
  obtain ⟨g226, hg226, hsg226⟩ := sig_of_map_idx ms_idx_226
  obtain ⟨g229, hg229, hsg229⟩ := sig_of_map_idx ms_idx_229
  obtain ⟨g235, hg235, hsg235⟩ := sig_of_map_idx ms_idx_235
  obtain ⟨g236, hg236, hsg236⟩ := sig_of_map_idx ms_idx_236
  obtain ⟨g237, hg237, hsg237⟩ := sig_of_map_idx ms_idx_237
  obtain ⟨g275, hg275, hsg275⟩ := sig_of_map_idx ms_idx_275
  obtain ⟨g299, hg299, hsg299⟩ := sig_of_map_idx ms_idx_299
  obtain ⟨g300, hg300, hsg300⟩ := sig_of_map_idx ms_idx_300
  obtain ⟨g302, hg302, hsg302⟩ := sig_of_map_idx ms_idx_302
  obtain ⟨g303, hg303, hsg303⟩ := sig_of_map_idx ms_idx_303
  obtain ⟨g304, hg304, hsg304⟩ := sig_of_map_idx ms_idx_304
  obtain ⟨g306, hg306, hsg306⟩ := sig_of_map_idx ms_idx_306
  obtain ⟨g307, hg307, hsg307⟩ := sig_of_map_idx ms_idx_307
  obtain ⟨g308, hg308, hsg308⟩ := sig_of_map_idx ms_idx_308
  obtain ⟨g311, hg311, hsg311⟩ := sig_of_map_idx ms_idx_311
  obtain ⟨g338, hg338, hsg338⟩ := sig_of_map_idx ms_idx_338
  obtain ⟨g340, hg340, hsg340⟩ := sig_of_map_idx ms_idx_340
  obtain ⟨g345, hg345, hsg345⟩ := sig_of_map_idx ms_idx_345
  obtain ⟨g347, hg347, hsg347⟩ := sig_of_map_idx ms_idx_347
  obtain ⟨g348, hg348, hsg348⟩ := sig_of_map_idx ms_idx_348
  obtain ⟨g352, hg352, hsg352⟩ := sig_of_map_idx ms_idx_352
  obtain ⟨g353, hg353, hsg353⟩ := sig_of_map_idx ms_idx_353
  obtain ⟨g355, hg355, hsg355⟩ := sig_of_map_idx ms_idx_355
  obtain ⟨g360, hg360, hsg360⟩ := sig_of_map_idx ms_idx_360
  obtain ⟨g365, hg365, hsg365⟩ := sig_of_map_idx ms_idx_365
  obtain ⟨g368, hg368, hsg368⟩ := sig_of_map_idx ms_idx_368
  obtain ⟨g369, hg369, hsg369⟩ := sig_of_map_idx ms_idx_369
  obtain ⟨g374, hg374, hsg374⟩ := sig_of_map_idx ms_idx_374
  obtain ⟨g376, hg376, hsg376⟩ := sig_of_map_idx ms_idx_376
  obtain ⟨g380, hg380, hsg380⟩ := sig_of_map_idx ms_idx_380
  obtain ⟨g381, hg381, hsg381⟩ := sig_of_map_idx ms_idx_381
  obtain ⟨g382, hg382, hsg382⟩ := sig_of_map_idx ms_idx_382
  obtain ⟨g383, hg383, hsg383⟩ := sig_of_map_idx ms_idx_383
  obtain ⟨g385, hg385, hsg385⟩ := sig_of_map_idx ms_idx_385
  obtain ⟨g388, hg388, hsg388⟩ := sig_of_map_idx ms_idx_388
  obtain ⟨g394, hg394, hsg394⟩ := sig_of_map_idx ms_idx_394
  obtain ⟨g397, hg397, hsg397⟩ := sig_of_map_idx ms_idx_397
  obtain ⟨g398, hg398, hsg398⟩ := sig_of_map_idx ms_idx_398
  obtain ⟨g399, hg399, hsg399⟩ := sig_of_map_idx ms_idx_399
  obtain ⟨g400, hg400, hsg400⟩ := sig_of_map_idx ms_idx_400
  obtain ⟨g401, hg401, hsg401⟩ := sig_of_map_idx ms_idx_401
  obtain ⟨g402, hg402, hsg402⟩ := sig_of_map_idx ms_idx_402
  obtain ⟨g403, hg403, hsg403⟩ := sig_of_map_idx ms_idx_403
  obtain ⟨g404, hg404, hsg404⟩ := sig_of_map_idx ms_idx_404
  obtain ⟨g405, hg405, hsg405⟩ := sig_of_map_idx ms_idx_405
  change ({ m7Module with fns := mfPatchFns m7FidMsRepls m7FidMsBefores m7Module.fns } :
    LeanQbe.T.Module).checkAcyclic = true
  refine msPatchModule_checkAcyclic (M := m7Module) ?_ m7_acyclic m7FidMsRepls_sigs ?_ ?_
  · have hnd := m7FidelityMemShrinkFns_names_nodup
    dsimp only [m7FidelityMemShrinkFns] at hnd
    simpa only [m7Module, List.map_nil, List.append_nil] using hnd
  · intro pre f post hsplit
    simp only [m7Module, List.map_nil] at hsplit ⊢
    rcases m7FidMs_insAt_cases f with h0 | ⟨_, h1⟩ | ⟨_, h2⟩ | ⟨_, h3⟩ | ⟨_, h4⟩ | ⟨hf405, h5⟩
    · rw [h0]; rfl
    · rw [h1]
      have hb : m7msFillU64Fn.checkCallsOk [] [] = true := by rfl
      have hm := fn_checkCallsOk_mono (a₂ := pre.map Fn.sig ++
          (pre.flatMap fun x => (mfPatchInsAt m7FidMsBefores x).map Fn.sig))
        (fun _ h => False.elim (List.not_mem_nil h)) hb
      dsimp only [LeanQbe.T.Module.checkFnsCallsOk]
      rw [List.append_nil, hm]; rfl
    · rw [h2]
      have hb : m7msTransBytesFn.checkCallsOk [] [] = true := by rfl
      have hm := fn_checkCallsOk_mono (a₂ := pre.map Fn.sig ++
          (pre.flatMap fun x => (mfPatchInsAt m7FidMsBefores x).map Fn.sig))
        (fun _ h => False.elim (List.not_mem_nil h)) hb
      dsimp only [LeanQbe.T.Module.checkFnsCallsOk]
      rw [List.append_nil, hm]; rfl
    · rw [h3]
      have hb : fidBvaMatchLargeFidFn.checkCallsOk [] [] = true := by rfl
      have hm := fn_checkCallsOk_mono (a₂ := pre.map Fn.sig ++
          (pre.flatMap fun x => (mfPatchInsAt m7FidMsBefores x).map Fn.sig))
        (fun _ h => False.elim (List.not_mem_nil h)) hb
      dsimp only [LeanQbe.T.Module.checkFnsCallsOk]
      rw [List.append_nil, hm]; rfl
    · rw [h4]
      have hb : fidReorderSiftFidFn.checkCallsOk [] [] = true := by rfl
      have hm := fn_checkCallsOk_mono (a₂ := pre.map Fn.sig ++
          (pre.flatMap fun x => (mfPatchInsAt m7FidMsBefores x).map Fn.sig))
        (fun _ h => False.elim (List.not_mem_nil h)) hb
      dsimp only [LeanQbe.T.Module.checkFnsCallsOk]
      rw [List.append_nil, hm]; rfl
    · rw [h5]
      have hn0 : f.name = g405.name := hf405.trans (congrArg Prod.fst hsg405.symm)
      have hb : fidHdrDecideFn.checkCallsOk
          [ ("full_decide_m7", [i64], [i64]), ("m6_hdr_dr_init", [i64], []) ] [] = true := by rfl
      have hm : fidHdrDecideFn.checkCallsOk (pre.map Fn.sig ++
          (pre.flatMap fun x => (mfPatchInsAt m7FidMsBefores x).map Fn.sig)) [] = true := by
        refine fn_checkCallsOk_mono (fun s hs => ?_) hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact sig_pre m7_names_nodup hsplit hg405 hn0 hg397 (by decide) hsg397
        · exact sig_pre m7_names_nodup hsplit hg405 hn0 hg73 (by decide) hsg73
      dsimp only [LeanQbe.T.Module.checkFnsCallsOk]
      rw [List.append_nil, hm]; rfl
  · intro pre f post r hsplit hr hnm
    simp only [m7Module, List.map_nil, List.append_nil] at hsplit ⊢
    rw [m7FidMsRepls, fidSchedFixPatchFns, fidSchedFixFns_eq_patchFns] at hr
    simp only [m7msRepls, m7FidNonMsHeadRepls, m7ParityVivTiersPatchFns, fidCorePatchFns,
      fidSearchPatchRepls, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with
      (((((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
         (rfl | rfl | rfl | rfl | rfl | rfl | rfl)) |
        (rfl | rfl | rfl | rfl | rfl)) |
       (rfl | rfl | rfl | rfl | rfl)) |
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl)) |
      (rfl | rfl | rfl)
    -- m7msRepls (1..12)
    · have hp : mfPatchInsAt m7FidMsBefores f = [m7msFillU64Fn] := by
        dsimp only [mfPatchInsAt, m7FidMsBefores, m7msBefores, m7FidBefores,
          fidCorePatchBefores, fidSearchPatchBefores]
        rw [hnm.symm]; rfl
      have hc : m7msZeroTables1Fn.checkCallsOk
          [("full_fill_u64_m7", [i64, i64, i64], [])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact List.mem_append_right _ (by rw [hp]; simp [m7msFillU64Fn, Fn.sig])
    · have hn0 : f.name = g42.name := hnm.symm.trans (congrArg Prod.fst hsg42.symm)
      have hg41_pre : g41 ∈ pre := fn_mem_pre_of_lt_idx m7_names_nodup hsplit hg42 hn0 hg41 (by decide)
      have hp41 : mfPatchInsAt m7FidMsBefores g41 = [m7msFillU64Fn] := by
        dsimp only [mfPatchInsAt, m7FidMsBefores, m7msBefores, m7FidBefores,
          fidCorePatchBefores, fidSearchPatchBefores]
        rw [show g41.name = "full_zero_tables1" from congrArg Prod.fst hsg41]; rfl
      have hc : m7msZeroTables2Fn.checkCallsOk
          [("full_fill_u64_m7", [i64, i64, i64], [])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨g41, hg41_pre, by rw [hp41]; simp [m7msFillU64Fn, Fn.sig]⟩))
    · exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h))
        (by rfl : m7msFixedBytesFn.checkCallsOk [] [] = true)
    · exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h))
        (by rfl : m7msInitPtrsFn.checkCallsOk [] [] = true)
    · exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h))
        (by rfl : m7msInitHdrFn.checkCallsOk [] [] = true)
    · have hn0 : f.name = g46.name := hnm.symm.trans (congrArg Prod.fst hsg46.symm)
      have hp : mfPatchInsAt m7FidMsBefores f = [m7msTransBytesFn] := by
        dsimp only [mfPatchInsAt, m7FidMsBefores, m7msBefores, m7FidBefores,
          fidCorePatchBefores, fidSearchPatchBefores]
        rw [hnm.symm]; rfl
      have hc : m7msCalcMaxVFn.checkCallsOk
          [ ("full_fixed_bytes", [i64], [i64])
          , ("full_trans_bytes_m7", [i64], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg46 hn0 hg43 (by decide) hsg43
      · exact List.mem_append_right _ (by rw [hp]; simp [m7msTransBytesFn, Fn.sig])
    · exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h))
        (by rfl : m7msCalcExtCapM5Fn.checkCallsOk [] [] = true)
    · exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h))
        (by rfl : m7msCalcScrCapM5Fn.checkCallsOk [] [] = true)
    · have hn0 : f.name = g49.name := hnm.symm.trans (congrArg Prod.fst hsg49.symm)
      have hc : m7msInitArenasFn.checkCallsOk [("full_init_ptrs", [i64, i64, i64], [])] [] = true :=
        by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact sig_pre4 m7_names_nodup hsplit hg49 hn0 hg44 (by decide) hsg44
    · have hn0 : f.name = g50.name := hnm.symm.trans (congrArg Prod.fst hsg50.symm)
      have hg46_pre : g46 ∈ pre := fn_mem_pre_of_lt_idx m7_names_nodup hsplit hg50 hn0 hg46 (by decide)
      have hp46 : mfPatchInsAt m7FidMsBefores g46 = [m7msTransBytesFn] := by
        dsimp only [mfPatchInsAt, m7FidMsBefores, m7msBefores, m7FidBefores,
          fidCorePatchBefores, fidSearchPatchBefores]
        rw [show g46.name = "full_calc_max_v" from congrArg Prod.fst hsg46]; rfl
      have hc : m7msInitStateM5Fn.checkCallsOk
          [ ("kissat_parse_header", [i64, i64, i64], [.bool])
          , ("full_fixed_bytes", [i64], [i64])
          , ("full_trans_bytes_m7", [i64], [i64])
          , ("full_calc_max_v", [i64, i64, i64, i64], [i64])
          , ("full_calc_ext_cap_m5", [i64], [i64])
          , ("full_calc_scr_cap_m5", [i64], [i64])
          , ("full_init_arenas", [i64, i64, i64, i64], [])
          , ("full_init_hdr", [i64, i64, i64, i64], [])
          , ("full_zero_tables1", [i64], [])
          , ("full_zero_tables2", [i64], []) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg50 hn0 hg5 (by decide) hsg5
      · exact sig_pre4 m7_names_nodup hsplit hg50 hn0 hg43 (by decide) hsg43
      · exact List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨g46, hg46_pre, by rw [hp46]; simp [m7msTransBytesFn, Fn.sig]⟩))
      · exact sig_pre4 m7_names_nodup hsplit hg50 hn0 hg46 (by decide) hsg46
      · exact sig_pre4 m7_names_nodup hsplit hg50 hn0 hg47 (by decide) hsg47
      · exact sig_pre4 m7_names_nodup hsplit hg50 hn0 hg48 (by decide) hsg48
      · exact sig_pre4 m7_names_nodup hsplit hg50 hn0 hg49 (by decide) hsg49
      · exact sig_pre4 m7_names_nodup hsplit hg50 hn0 hg45 (by decide) hsg45
      · exact sig_pre4 m7_names_nodup hsplit hg50 hn0 hg41 (by decide) hsg41
      · exact sig_pre4 m7_names_nodup hsplit hg50 hn0 hg42 (by decide) hsg42
    · have hn0 : f.name = g51.name := hnm.symm.trans (congrArg Prod.fst hsg51.symm)
      have hc : m7msInitStateFn.checkCallsOk
          [("full_init_state_m5", [i64, i64, i64, i64, i64], [.bool])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact sig_pre4 m7_names_nodup hsplit hg51 hn0 hg50 (by decide) hsg50
    · exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h))
        (by rfl : m7msCompactVarsFn.checkCallsOk [] [] = true)
    -- m7FidNonMsHeadRepls (13..19)
    · have hn0 : f.name = g348.name := hnm.symm.trans (congrArg Prod.fst hsg348.symm)
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
      · exact sig_pre4 m7_names_nodup hsplit hg348 hn0 hg12 (by decide) hsg12
      · exact sig_pre4 m7_names_nodup hsplit hg348 hn0 hg17 (by decide) hsg17
      · exact sig_pre4 m7_names_nodup hsplit hg348 hn0 hg18 (by decide) hsg18
      · exact sig_pre4 m7_names_nodup hsplit hg348 hn0 hg80 (by decide) hsg80
      · exact sig_pre4 m7_names_nodup hsplit hg348 hn0 hg178 (by decide) hsg178
      · exact sig_pre4 m7_names_nodup hsplit hg348 hn0 hg179 (by decide) hsg179
      · exact sig_pre4 m7_names_nodup hsplit hg348 hn0 hg340 (by decide) hsg340
    · have hn0 : f.name = g113.name := hnm.symm.trans (congrArg Prod.fst hsg113.symm)
      have hc : m7AnalyzeRsnFn.checkCallsOk [("full_analyze_lit", [i64, i32, i32], [.bool])] [] =
          true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact sig_pre4 m7_names_nodup hsplit hg113 hn0 hg112 (by decide) hsg112
    · exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h))
        (by rfl : m7fixCompactNeededFn.checkCallsOk [] [] = true)
    · have hn0 : f.name = g355.name := hnm.symm.trans (congrArg Prod.fst hsg355.symm)
      have hc : m7fixCompactMarkLiveFn.checkCallsOk [("full_arena_next", [i64, i32], [i32])] [] =
          true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact sig_pre4 m7_names_nodup hsplit hg355 hn0 hg11 (by decide) hsg11
    · have hn0 : f.name = g97.name := hnm.symm.trans (congrArg Prod.fst hsg97.symm)
      have hc : m7fixSweepCopyFn.checkCallsOk
          [ ("full_assign_lvl", [i64, i32, i32, i32], [])
          , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg97 hn0 hg35 (by decide) hsg35
      · exact sig_pre4 m7_names_nodup hsplit hg97 hn0 hg18 (by decide) hsg18
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
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg311 hn0 hg300 (by decide) hsg300
      · exact sig_pre4 m7_names_nodup hsplit hg311 hn0 hg302 (by decide) hsg302
      · exact sig_pre4 m7_names_nodup hsplit hg311 hn0 hg308 (by decide) hsg308
      · exact sig_pre4 m7_names_nodup hsplit hg311 hn0 hg303 (by decide) hsg303
      · exact sig_pre4 m7_names_nodup hsplit hg311 hn0 hg306 (by decide) hsg306
      · exact sig_pre4 m7_names_nodup hsplit hg311 hn0 hg307 (by decide) hsg307
      · exact sig_pre4 m7_names_nodup hsplit hg311 hn0 hg11 (by decide) hsg11
      · exact sig_pre4 m7_names_nodup hsplit hg311 hn0 hg304 (by decide) hsg304
    · exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h))
        (by rfl : fidIlog10Fn.checkCallsOk [] [] = true)
    -- m7ParityVivTiersPatchFns (20..24)
    · have hn0 : f.name = g59.name := hnm.symm.trans (congrArg Prod.fst hsg59.symm)
      have hc : m7pSyncLegacyTiersFn.checkCallsOk [("m6_ext_ensure_init", [i64], [])] [] = true :=
        by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact sig_pre4 m7_names_nodup hsplit hg59 hn0 hg56 (by decide) hsg56
    · have hn0 : f.name = g83.name := hnm.symm.trans (congrArg Prod.fst hsg83.symm)
      have hc : m7pPropIgnoreHotFn.checkCallsOk
          [ ("full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool])
          , ("full_prop_chrono_hot", [i64, i64], [.bool]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg83 hn0 hg81 (by decide) hsg81
      · exact sig_pre4 m7_names_nodup hsplit hg83 hn0 hg82 (by decide) hsg82
    · have hn0 : f.name = g85.name := hnm.symm.trans (congrArg Prod.fst hsg85.symm)
      have hc : m7pPropIgnoreFn.checkCallsOk
          [ ("full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool])
          , ("full_prop_chrono_hot", [i64, i64], [.bool]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg85 hn0 hg81 (by decide) hsg81
      · exact sig_pre4 m7_names_nodup hsplit hg85 hn0 hg82 (by decide) hsg82
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
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg217 hn0 hg39 (by decide) hsg39
      · exact sig_pre4 m7_names_nodup hsplit hg217 hn0 hg211 (by decide) hsg211
      · exact sig_pre4 m7_names_nodup hsplit hg217 hn0 hg212 (by decide) hsg212
      · exact sig_pre4 m7_names_nodup hsplit hg217 hn0 hg213 (by decide) hsg213
      · exact sig_pre4 m7_names_nodup hsplit hg217 hn0 hg214 (by decide) hsg214
      · exact sig_pre4 m7_names_nodup hsplit hg217 hn0 hg209 (by decide) hsg209
      · exact sig_pre4 m7_names_nodup hsplit hg217 hn0 hg86 (by decide) hsg86
      · exact sig_pre4 m7_names_nodup hsplit hg217 hn0 hg215 (by decide) hsg215
    · have hn0 : f.name = g218.name := hnm.symm.trans (congrArg Prod.fst hsg218.symm)
      have hc : m7pVivifyFn.checkCallsOk
          [ ("full_backtrack", [i64, i64], [])
          , ("m6_hdr_sync_legacy_tiers", [i64], [])
          , ("m6_hdr_get_watermark", [i64, i64], [i64])
          , ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg218 hn0 hg39 (by decide) hsg39
      · exact sig_pre4 m7_names_nodup hsplit hg218 hn0 hg59 (by decide) hsg59
      · exact sig_pre4 m7_names_nodup hsplit hg218 hn0 hg70 (by decide) hsg70
      · exact sig_pre4 m7_names_nodup hsplit hg218 hn0 hg217 (by decide) hsg217
    -- fidSchedFixPatchFns (25..29)
    · have hn0 : f.name = g111.name := hnm.symm.trans (congrArg Prod.fst hsg111.symm)
      have hc : fid2ReduceM6Fn.checkCallsOk
          [ ("full_isqrt", [i64], [i64]), ("full_backtrack", [i64, i64], [])
          , ("full_propagate", [i64], [i64]), ("m6_hdr_recompute_tiers", [i64], [])
          , ("full_mark_reasons", [i64, .bool], []), ("full_arena_next", [i64, i32], [i32])
          , ("full_sort_reds", [i64, i64], []), ("full_log10_q16_m7", [i64], [i64])
          , ("full_arena_sweep", [i64], [i64])
          , ("m6_hdr_set_watermark", [i64, i64, i64], []) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg111 hn0 hg8 (by decide) hsg8
      · exact sig_pre4 m7_names_nodup hsplit hg111 hn0 hg39 (by decide) hsg39
      · exact sig_pre4 m7_names_nodup hsplit hg111 hn0 hg86 (by decide) hsg86
      · exact sig_pre4 m7_names_nodup hsplit hg111 hn0 hg61 (by decide) hsg61
      · exact sig_pre4 m7_names_nodup hsplit hg111 hn0 hg105 (by decide) hsg105
      · exact sig_pre4 m7_names_nodup hsplit hg111 hn0 hg11 (by decide) hsg11
      · exact sig_pre4 m7_names_nodup hsplit hg111 hn0 hg109 (by decide) hsg109
      · exact sig_pre4 m7_names_nodup hsplit hg111 hn0 hg31 (by decide) hsg31
      · exact sig_pre4 m7_names_nodup hsplit hg111 hn0 hg104 (by decide) hsg104
      · exact sig_pre4 m7_names_nodup hsplit hg111 hn0 hg71 (by decide) hsg71
    · have hn0 : f.name = g385.name := hnm.symm.trans (congrArg Prod.fst hsg385.symm)
      have hc : fid2EliminateM6Fn.checkCallsOk
          [ ("full_elim_dticks", [i64, .bool], [i64]), ("full_log10_q16_m7", [i64], [i64])
          , ("full_scale_delta", [i64, i64], [i64]), ("full_enter_dense", [i64], [.bool])
          , ("full_min_u64", [i64, i64], [i64]), ("full_forward_sub", [i64, i64], [i64])
          , ("full_elim_bve_m7", [i64, i64], [i64]), ("full_rebuild_watches", [i64], [i64]) ] [] =
          true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg385 hn0 hg376 (by decide) hsg376
      · exact sig_pre4 m7_names_nodup hsplit hg385 hn0 hg31 (by decide) hsg31
      · exact sig_pre4 m7_names_nodup hsplit hg385 hn0 hg34 (by decide) hsg34
      · exact sig_pre4 m7_names_nodup hsplit hg385 hn0 hg236 (by decide) hsg236
      · exact sig_pre4 m7_names_nodup hsplit hg385 hn0 hg374 (by decide) hsg374
      · exact sig_pre4 m7_names_nodup hsplit hg385 hn0 hg311 (by decide) hsg311
      · exact sig_pre4 m7_names_nodup hsplit hg385 hn0 hg383 (by decide) hsg383
      · exact sig_pre4 m7_names_nodup hsplit hg385 hn0 hg237 (by decide) hsg237
    · have hn0 : f.name = g401.name := hnm.symm.trans (congrArg Prod.fst hsg401.symm)
      have hc : fid2ProbeTailM6Fn.checkCallsOk
          [ ("full_backbone_m6", [i64, i64], [i64])
          , ("full_transitive_m6", [i64, i64], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg401 hn0 hg226 (by decide) hsg226
      · exact sig_pre4 m7_names_nodup hsplit hg401 hn0 hg229 (by decide) hsg229
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
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg400 (by decide) hsg400
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg31 (by decide) hsg31
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg32 (by decide) hsg32
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg218 (by decide) hsg218
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg236 (by decide) hsg236
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg66 (by decide) hsg66
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg275 (by decide) hsg275
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg237 (by decide) hsg237
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg71 (by decide) hsg71
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg68 (by decide) hsg68
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg67 (by decide) hsg67
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg299 (by decide) hsg299
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg235 (by decide) hsg235
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg401 (by decide) hsg401
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg226 (by decide) hsg226
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg374 (by decide) hsg374
      · exact sig_pre4 m7_names_nodup hsplit hg402 hn0 hg352 (by decide) hsg352
    · have hn0 : f.name = g403.name := hnm.symm.trans (congrArg Prod.fst hsg403.symm)
      have hc : fid2PreprocessM6Fn.checkCallsOk
          [ ("full_propagate", [i64], [i64]), ("full_arena_sweep", [i64], [i64])
          , ("full_lucky", [i64], [i64]), ("full_compact_needed", [i64], [.bool])
          , ("full_compact", [i64], [i64]), ("full_scale_delta_m5", [i64, i64], [i64])
          , ("full_probe_m6", [i64, .bool], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg403 hn0 hg86 (by decide) hsg86
      · exact sig_pre4 m7_names_nodup hsplit hg403 hn0 hg104 (by decide) hsg104
      · exact sig_pre4 m7_names_nodup hsplit hg403 hn0 hg184 (by decide) hsg184
      · exact sig_pre4 m7_names_nodup hsplit hg403 hn0 hg353 (by decide) hsg353
      · exact sig_pre4 m7_names_nodup hsplit hg403 hn0 hg365 (by decide) hsg365
      · exact sig_pre4 m7_names_nodup hsplit hg403 hn0 hg32 (by decide) hsg32
      · exact sig_pre4 m7_names_nodup hsplit hg403 hn0 hg402 (by decide) hsg402
    -- fidCorePatchFns (30..36)
    · have hn0 : f.name = g135.name := hnm.symm.trans (congrArg Prod.fst hsg135.symm)
      have hc : fidMinShrinkM6Fn.checkCallsOk
          [ ("full_sort_tmp", [i64], [])
          , ("full_min_mark", [i64, i32, i8], [])
          , ("full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool])
          , ("full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg135 hn0 hg129 (by decide) hsg129
      · exact sig_pre4 m7_names_nodup hsplit hg135 hn0 hg124 (by decide) hsg124
      · exact sig_pre4 m7_names_nodup hsplit hg135 hn0 hg133 (by decide) hsg133
      · exact sig_pre4 m7_names_nodup hsplit hg135 hn0 hg130 (by decide) hsg130
    · exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h))
        (by rfl : fidBvaScanCandsFn.checkCallsOk [] [] = true)
    · have hp : mfPatchInsAt m7FidMsBefores f = [fidBvaMatchLargeFidFn] := by
        dsimp only [mfPatchInsAt, m7FidMsBefores, m7msBefores, m7FidBefores,
          fidCorePatchBefores, fidSearchPatchBefores]
        rw [hnm.symm]; rfl
      have hc : fidBvaFilterRowFn.checkCallsOk
          [("full_bva_match_large_fid", [i64, i32, i32, i32], [.bool])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact List.mem_append_right _ (by rw [hp]; simp [fidBvaMatchLargeFidFn, Fn.sig])
    · have hn0 : f.name = g368.name := hnm.symm.trans (congrArg Prod.fst hsg368.symm)
      have hp : mfPatchInsAt m7FidMsBefores f = [fidReorderSiftFidFn] := by
        dsimp only [mfPatchInsAt, m7FidMsBefores, m7msBefores, m7FidBefores,
          fidCorePatchBefores, fidSearchPatchBefores]
        rw [hnm.symm]; rfl
      have hc : fidReorderQueueM7Fn.checkCallsOk
          [ ("full_arena_next", [i64, i32], [i32])
          , ("full_rescale", [i64], [])
          , ("full_heap_up", [i64, i32], [])
          , ("full_reorder_sift_fid", [i64, i64, i64], []) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg368 hn0 hg11 (by decide) hsg11
      · exact sig_pre4 m7_names_nodup hsplit hg368 hn0 hg24 (by decide) hsg24
      · exact sig_pre4 m7_names_nodup hsplit hg368 hn0 hg19 (by decide) hsg19
      · exact List.mem_append_right _ (by rw [hp]; simp [fidReorderSiftFidFn, Fn.sig])
    · have hn0 : f.name = g369.name := hnm.symm.trans (congrArg Prod.fst hsg369.symm)
      have hc : fidReorderM6Fn.checkCallsOk [("full_reorder_queue_m7", [i64], [i64])] [] = true :=
        by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact sig_pre4 m7_names_nodup hsplit hg369 hn0 hg368 (by decide) hsg368
    · have hn0 : f.name = g383.name := hnm.symm.trans (congrArg Prod.fst hsg383.symm)
      have hc : fidElimBveM7Fn.checkCallsOk
          [ ("full_dense_flush_units_m7", [i64], [.bool])
          , ("full_bve_heap_push_m7", [i64, i64, i32], [i64])
          , ("full_bve_heap_pop_m7", [i64, i64], [i32])
          , ("full_bve_collect_nbrs_m7", [i64, i32], [i64])
          , ("full_bve_var_m7", [i64, i32], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg383 hn0 hg302 (by decide) hsg302
      · exact sig_pre4 m7_names_nodup hsplit hg383 hn0 hg380 (by decide) hsg380
      · exact sig_pre4 m7_names_nodup hsplit hg383 hn0 hg381 (by decide) hsg381
      · exact sig_pre4 m7_names_nodup hsplit hg383 hn0 hg382 (by decide) hsg382
      · exact sig_pre4 m7_names_nodup hsplit hg383 hn0 hg338 (by decide) hsg338
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
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg164 hn0 hg157 (by decide) hsg157
      · exact sig_pre4 m7_names_nodup hsplit hg164 hn0 hg158 (by decide) hsg158
      · exact sig_pre4 m7_names_nodup hsplit hg164 hn0 hg154 (by decide) hsg154
      · exact sig_pre4 m7_names_nodup hsplit hg164 hn0 hg155 (by decide) hsg155
      · exact sig_pre4 m7_names_nodup hsplit hg164 hn0 hg159 (by decide) hsg159
      · exact sig_pre4 m7_names_nodup hsplit hg164 hn0 hg156 (by decide) hsg156
      · exact sig_pre4 m7_names_nodup hsplit hg164 hn0 hg161 (by decide) hsg161
      · exact sig_pre4 m7_names_nodup hsplit hg164 hn0 hg162 (by decide) hsg162
      · exact sig_pre4 m7_names_nodup hsplit hg164 hn0 hg163 (by decide) hsg163
      · exact sig_pre4 m7_names_nodup hsplit hg164 hn0 hg10 (by decide) hsg10
    -- fidSearchPatchRepls (37..39)
    · have hn0 : f.name = g118.name := hnm.symm.trans (congrArg Prod.fst hsg118.symm)
      have hc : fidBumpAnalyzedFn.checkCallsOk
          [ ("m6_hdr_dr_allow", [i64], [.bool])
          , ("full_sort_ana_qs_m6", [i64, i64], [])
          , ("full_queue_mtf", [i64, i32], [])
          , ("full_bump_var", [i64, i32], [])
          , ("full_bump_decay", [i64], []) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg118 hn0 hg75 (by decide) hsg75
      · exact sig_pre4 m7_names_nodup hsplit hg118 hn0 hg117 (by decide) hsg117
      · exact sig_pre4 m7_names_nodup hsplit hg118 hn0 hg28 (by decide) hsg28
      · exact sig_pre4 m7_names_nodup hsplit hg118 hn0 hg25 (by decide) hsg25
      · exact sig_pre4 m7_names_nodup hsplit hg118 hn0 hg26 (by decide) hsg26
    · have hn0 : f.name = g399.name := hnm.symm.trans (congrArg Prod.fst hsg399.symm)
      have hc : fidSwitchModeFn.checkCallsOk
          [ ("full_heap_down", [i64, i32], [])
          , ("full_log10_q16_m7", [i64], [i64])
          , ("full_ema_swap_m7", [i64, i64, i64], [])
          , ("full_ilog10", [i64], [i64])
          , ("full_m7_set64", [i64, i64, i64], []) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl
      · exact sig_pre4 m7_names_nodup hsplit hg399 hn0 hg20 (by decide) hsg20
      · exact sig_pre4 m7_names_nodup hsplit hg399 hn0 hg31 (by decide) hsg31
      · exact sig_pre4 m7_names_nodup hsplit hg399 hn0 hg398 (by decide) hsg398
      · exact sig_pre4 m7_names_nodup hsplit hg399 hn0 hg9 (by decide) hsg9
      · exact sig_pre4 m7_names_nodup hsplit hg399 hn0 hg388 (by decide) hsg388
    · have hn0 : f.name = g405.name := hnm.symm.trans (congrArg Prod.fst hsg405.symm)
      have hp : mfPatchInsAt m7FidMsBefores f = [fidHdrDecideFn] := by
        dsimp only [mfPatchInsAt, m7FidMsBefores, m7msBefores, m7FidBefores,
          fidCorePatchBefores, fidSearchPatchBefores]
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
      · exact sig_pre4 m7_names_nodup hsplit hg405 hn0 hg394 (by decide) hsg394
      · exact sig_pre4 m7_names_nodup hsplit hg405 hn0 hg86 (by decide) hsg86
      · exact sig_pre4 m7_names_nodup hsplit hg405 hn0 hg151 (by decide) hsg151
      · exact sig_pre4 m7_names_nodup hsplit hg405 hn0 hg111 (by decide) hsg111
      · exact sig_pre4 m7_names_nodup hsplit hg405 hn0 hg399 (by decide) hsg399
      · exact sig_pre4 m7_names_nodup hsplit hg405 hn0 hg170 (by decide) hsg170
      · exact sig_pre4 m7_names_nodup hsplit hg405 hn0 hg171 (by decide) hsg171
      · exact sig_pre4 m7_names_nodup hsplit hg405 hn0 hg369 (by decide) hsg369
      · exact sig_pre4 m7_names_nodup hsplit hg405 hn0 hg169 (by decide) hsg169
      · exact sig_pre4 m7_names_nodup hsplit hg405 hn0 hg404 (by decide) hsg404
      · exact List.mem_append_right _ (by rw [hp]; simp [fidHdrDecideFn, Fn.sig])

/-! ## 5. Compile-Time `#guard` Verification (`PrintCpp`, `PrintQbe`, 4-ISA Legal) -/

section Guards

open LeanQbe.T.PrintCpp

#guard m7PlusMsRepls.length == 27
#guard (m7PlusMsRepls.map Fn.name).eraseDups.length == 27
#guard m7PlusMsRepls.all fun r => m7Fns.any fun f => f.sig == r.sig
#guard m7PlusMemShrinkFns.length == 412
#guard (m7PlusMemShrinkFns.map Fn.name).eraseDups.length == 412
#guard m7PlusMemShrinkModule.checkAcyclic
#guard m7PlusMemShrinkModule.exits.isEmpty && m7PlusMemShrinkModule.externs.isEmpty
#guard (ppTModule m7PlusMemShrinkModule).isOk
#guard (PrintQbe.module m7PlusMemShrinkModule).isOk
#guard (ppModule (m7PlusMemShrinkFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7PlusMemShrinkFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7PlusMemShrinkFns.map (Fn.legal .x64AVX512))).isOk
#guard (ppModule (m7PlusMemShrinkFns.map (Fn.legal .x64AVX2))).isOk
#guard m7PlusMemShrinkFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard m7PlusMemShrinkFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard m7PlusMemShrinkFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard m7PlusMemShrinkFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

#guard m7FidMsRepls.length == 39
#guard (m7FidMsRepls.map Fn.name).eraseDups.length == 39
#guard m7FidMsRepls.all fun r => m7Fns.any fun f => f.sig == r.sig
#guard m7FidelityMemShrinkFns.length == 415
#guard (m7FidelityMemShrinkFns.map Fn.name).eraseDups.length == 415
#guard m7FidelityMemShrinkModule.checkAcyclic
#guard m7FidelityMemShrinkModule.exits.isEmpty && m7FidelityMemShrinkModule.externs.isEmpty
#guard (ppTModule m7FidelityMemShrinkModule).isOk
#guard (PrintQbe.module m7FidelityMemShrinkModule).isOk
#guard (ppModule (m7FidelityMemShrinkFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7FidelityMemShrinkFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7FidelityMemShrinkFns.map (Fn.legal .x64AVX512))).isOk
#guard (ppModule (m7FidelityMemShrinkFns.map (Fn.legal .x64AVX2))).isOk
#guard m7FidelityMemShrinkFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard m7FidelityMemShrinkFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard m7FidelityMemShrinkFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard m7FidelityMemShrinkFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

end Guards

end LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5
