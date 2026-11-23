/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7ParityVivTiersProof0
public import LeanQbe.T.Examples.Kissat.FullM7Splice
public import LeanQbe.T.Examples.Kissat.FullFastCoreLemmas
import LeanQbe.T.Logic.C0Step
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `M7` Shared Vivification & Focused-Tier Module Proof & `M7` Splice

No blanket expose attributes, no local attributes, no unrestricted imports, no stubs or custom
axioms, plain `public section`, UNSAT-only (`XPost := False`, zero SAT model proofs):
1. Standalone `16`-row `m7ParityVivTiersSpecTable`, `m7ParityVivTiersEnv`,
   `m7ParityVivTiers_tableImpl`, and `m7ParityVivTiers_moduleOk`.
2. Canonical `5`-row `m7ParityVivTiersPatchRows` + `m7ParityVivTiersSplicedModule` (`410` fns via
   `FullM7Splice.patchFns m7ParityVivTiersPatchFns [] m7Fns`), proving
   `m7ParityVivTiers_spliced_checkAcyclic`, `m7ParityVivTiers_spliced_moduleOk`,
   `m7ParityVivTiers_spliced_solve_bytes_sound`, and `m7ParityVivTiers_spliced_unsat_nv`.
3. Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) under `m7ParityVivTiersEnv` for all `4`
   modified functions.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7ParityVivTiers

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6Transport
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Splice
open Kraken.Bedrock2.Test

/-! ## 1. Standalone `16`-Row Spec Table, `Env`, and `ModuleOk` -/

/-- Closed `16`-row specification table aligned 1-to-1 with `m7ParityVivTiersModule` (`4` defined
functions + `12` external callees, all `noExit = true`). -/
def m7ParityVivTiersSpecTable : List SpecEntry :=
  [ ⟨"m6_hdr_sync_legacy_tiers", [i64], [], m6HdrW2aSpec [] [], true⟩
  , ⟨"full_propagate_ignore_hot", [i64, i64], [i64],
      Full.FullPropDecSpecs.fullPropagateIgnoreSpec, true⟩
  , ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], m6aVivifyTierSpec, true⟩
  , ⟨"full_vivify_m6_hdr", [i64], [i64], m6aVivifySpec, true⟩
  , ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
  , ⟨"full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool],
      FullM7BcpHot.fullPropLitOvfHotSpec, true⟩
  , ⟨"full_prop_chrono_hot", [i64, i64], [.bool],
      FullM7BcpHot.fullPropChronoHotSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  , ⟨"full_viv_collect_m6", [i64, i64], [i64],
      FullM6VivBackbone.fullVivCollectM6Spec, true⟩
  , ⟨"full_viv_count_m6", [i64, i64], [], FullM6VivBackbone.fullVivCountM6Spec, true⟩
  , ⟨"full_viv_keys_m6", [i64, i64], [], FullM6VivBackbone.fullVivKeysM6Spec, true⟩
  , ⟨"full_viv_sort_sched_m6", [i64, i64], [],
      FullM6VivBackbone.fullVivSortSchedM6Spec, true⟩
  , ⟨"full_viv_clause_m6", [i64, i32], [i64], FullM6VivBackbone.fullVivClauseM6Spec, true⟩
  , ⟨"full_propagate", [i64], [i64], FullM6BcpS15.fullBcpS15Spec, true⟩
  , ⟨"full_viv_clear_tier_m6", [i64, i64], [],
      FullM6VivBackbone.fullVivClearTierM6Spec, true⟩
  , ⟨"m6_hdr_get_watermark", [i64, i64], [i64], m6HdrW2aSpec [i64] [i64], true⟩ ]

theorem m7ParityVivTiersSpecTable_length : m7ParityVivTiersSpecTable.length = 16 := by rfl

theorem m7ParityVivTiersSpecTable_sigs :
    m7ParityVivTiersSpecTable.map (fun e => (e.name, e.as, e.rs)) =
      m7ParityVivTiersModule.fns.map Fn.sig ++
        m7ParityVivTiersModule.externs.map Extern.sig := by
  rfl

theorem m7ParityVivTiersSpecTable_nodup :
    (m7ParityVivTiersSpecTable.map SpecEntry.name).Nodup := by
  show ([ "m6_hdr_sync_legacy_tiers", "full_propagate_ignore_hot"
    , "full_vivify_tier_m6_hdr", "full_vivify_m6_hdr", "m6_ext_ensure_init"
    , "full_prop_lit_ovf_hot", "full_prop_chrono_hot", "full_backtrack"
    , "full_viv_collect_m6", "full_viv_count_m6", "full_viv_keys_m6"
    , "full_viv_sort_sched_m6", "full_viv_clause_m6", "full_propagate"
    , "full_viv_clear_tier_m6", "m6_hdr_get_watermark" ] : List String).Nodup
  decide

theorem m7ParityVivTiersSpecTable_noExit :
    ∀ e ∈ m7ParityVivTiersSpecTable, e.noExit = true := by
  intro e he
  simp only [m7ParityVivTiersSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> rfl

/-- Closed specification environment induced by `m7ParityVivTiersSpecTable`. -/
def m7ParityVivTiersEnv : Env :=
  Env.ofTable m7ParityVivTiersSpecTable

theorem m7ParityVivTiersEnv_noExit :
    ∀ f as bs xs m Q X X',
      m7ParityVivTiersEnv f as bs xs m Q X →
      m7ParityVivTiersEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m7ParityVivTiersSpecTable_noExit

private theorem m7pEnv_row_at (i : Nat) (e : SpecEntry)
    (hi : m7ParityVivTiersSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → m7ParityVivTiersEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) m7ParityVivTiersSpecTable_nodup
      (hno xs m Q X h)

/-- Row-by-row `TableImpl` for all `4` functions of `m7ParityVivTiersModule`. -/
theorem m7ParityVivTiers_tableImpl :
    TableImpl m7ParityVivTiersEnv m7ParityVivTiersModule.fns m7ParityVivTiersSpecTable := by
  let hEnsure := m7pEnv_row_at 4 ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
    (hno := fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h)
  let hOvf := m7pEnv_row_at 5
    ⟨"full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool],
      FullM7BcpHot.fullPropLitOvfHotSpec, true⟩
  let hChrono := m7pEnv_row_at 6
    ⟨"full_prop_chrono_hot", [i64, i64], [.bool],
      FullM7BcpHot.fullPropChronoHotSpec, true⟩
  let hBt := m7pEnv_row_at 7 ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  let hCol := m7pEnv_row_at 8
    ⟨"full_viv_collect_m6", [i64, i64], [i64], FullM6VivBackbone.fullVivCollectM6Spec, true⟩
  let hCnt := m7pEnv_row_at 9
    ⟨"full_viv_count_m6", [i64, i64], [], FullM6VivBackbone.fullVivCountM6Spec, true⟩
  let hKeys := m7pEnv_row_at 10
    ⟨"full_viv_keys_m6", [i64, i64], [], FullM6VivBackbone.fullVivKeysM6Spec, true⟩
  let hSort := m7pEnv_row_at 11
    ⟨"full_viv_sort_sched_m6", [i64, i64], [],
      FullM6VivBackbone.fullVivSortSchedM6Spec, true⟩
  let hCls := m7pEnv_row_at 12
    ⟨"full_viv_clause_m6", [i64, i32], [i64], FullM6VivBackbone.fullVivClauseM6Spec, true⟩
  let hProp := m7pEnv_row_at 13
    ⟨"full_propagate", [i64], [i64], FullM6BcpS15.fullBcpS15Spec, true⟩
  let hClr := m7pEnv_row_at 14
    ⟨"full_viv_clear_tier_m6", [i64, i64], [],
      FullM6VivBackbone.fullVivClearTierM6Spec, true⟩
  let hSync := m7pEnv_row_at 0
    ⟨"m6_hdr_sync_legacy_tiers", [i64], [], m6HdrW2aSpec [] [], true⟩
    (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  let hGetWm := m7pEnv_row_at 15
    ⟨"m6_hdr_get_watermark", [i64, i64], [i64], m6HdrW2aSpec [i64] [i64], true⟩
    (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  let hVivTier := m7pEnv_row_at 2
    ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], m6aVivifyTierSpec, true⟩
    (hno := fun _ _ _ _ h => m6aVivifyTierSpec_monoX h)
  exact ⟨ SpecEntry.Impl.of (m6_hdr_sync_legacy_tiers_wp m7ParityVivTiersEnv hEnsure)
    , SpecEntry.Impl.of (full_propagate_ignore_hot_wp m7ParityVivTiersEnv hOvf hChrono)
    , SpecEntry.Impl.of (full_vivify_tier_m6_hdr_wp m7ParityVivTiersEnv
        hBt hCol hCnt hKeys hSort hCls hProp hClr)
    , SpecEntry.Impl.of (full_vivify_m6_hdr_wp m7ParityVivTiersEnv
        hBt hSync hGetWm hVivTier)
    , trivial ⟩

/-- Closed `ModuleOk` for `m7ParityVivTiersModule` under `m7ParityVivTiersEnv`. -/
theorem m7ParityVivTiers_moduleOk :
    ModuleOk m7ParityVivTiersEnv m7ParityVivTiersModule :=
  Env.ofTable_moduleOk m7ParityVivTiers_acyclic
    (FullM6ProofUtil.allFns_of_mem m7ParityVivTiers_fns_wf) m7ParityVivTiers_tableImpl

/-! ## 2. Canonical `M7` Splice (`patchFns` / `patchRows`, `410` Fns) -/

/-- Exact `5`-row `SpecEntry` list matching `m7ParityVivTiersPatchFns` and preserving every
existing `FullM7Proof.m7SpecTable` contract identically. -/
def m7ParityVivTiersPatchRows : List SpecEntry :=
  [ ⟨"m6_hdr_sync_legacy_tiers", [i64], [], m6HdrW2aSpec [] [], true⟩
  , ⟨"full_propagate_ignore_hot", [i64, i64], [i64],
      Full.FullPropDecSpecs.fullPropagateIgnoreSpec, true⟩
  , ⟨"full_propagate_ignore", [i64, i64], [i64], Full.fullPropagateIgnoreSpec, true⟩
  , ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], m6aVivifyTierSpec, true⟩
  , ⟨"full_vivify_m6_hdr", [i64], [i64], m6aVivifySpec, true⟩ ]

theorem m7ParityVivTiersPatchRows_sigs :
    m7ParityVivTiersPatchRows.map (fun e => (e.name, e.as, e.rs)) =
      m7ParityVivTiersPatchFns.map Fn.sig := by
  rfl

theorem m7ParityVivTiersPatchRows_noExit :
    m7ParityVivTiersPatchRows.all SpecEntry.noExit = true := by
  rfl

/-- Canonical `Full.fullPropagateIgnoreSpec` bridge for `full_propagate_ignore_hot_body`
under `"full_propagate_ignore"`. -/
theorem full_propagate_ignore_canon_hot_wp (Γ : Env)
    (hOvf : ∀ args m Q X, FullM7BcpHot.fullPropLitOvfHotSpec args m Q X →
      Γ "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool] args m Q X)
    (hChrono : ∀ args m Q X, FullM7BcpHot.fullPropChronoHotSpec args m Q X →
      Γ "full_prop_chrono_hot" [i64, i64] [.bool] args m Q X) :
    ∀ args m Q X, Full.fullPropagateIgnoreSpec args m Q X →
      Func.wp Γ full_propagate_ignore_hot_body args m Q X := by
  rintro ⟨h, ign, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, hQ⟩
  refine full_propagate_ignore_hot_wp Γ hOvf hChrono (c.hdr, ign, ()) m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, ?_⟩
  dsimp only
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' hlen' hw' htr' hperm' hfl' hr
    hr0 hr1 hr2 hnoop hm'
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' hlen' hw'
    ⟨htr'.te_ge, htr'.trl_pref, htr'.lvl_pres⟩ ⟨rfl, hperm'.1, hperm'.2⟩ hfl' hr hr0
    (fun h1 => let ⟨hf, ho, hc, hign, _⟩ := hr1 h1
      ⟨hf, ho, hc.elim (fun ⟨ht, h0, h1', hent, hf0, hf1⟩ => Or.inl ⟨ht, h0, h1', hf0, hf1, hent⟩)
        (fun h => Or.inr h), hign⟩)
    hr2 hnoop hm'

/-- `410`-function unified `M7` list with `m7ParityVivTiersPatchFns` spliced in via `patchFns`. -/
def m7ParityVivTiersSplicedFns : List Fn :=
  patchFns m7ParityVivTiersPatchFns [] m7Fns

/-- Closed `410`-function `M7` module with `FullM7ParityVivTiers` spliced in (`externs := []`,
`exits := []`). -/
def m7ParityVivTiersSplicedModule : LeanQbe.T.Module :=
  { m7Module with fns := m7ParityVivTiersSplicedFns }

theorem m7ParityVivTiersSplicedFns_eq_splice :
    m7ParityVivTiersSplicedFns = spliceFns m7ParityVivTiersPatchFns m7Fns :=
  patchFns_nil m7ParityVivTiersPatchFns m7Fns

theorem m7ParityVivTiersSplicedFns_sigs :
    m7ParityVivTiersSplicedFns.map Fn.sig = m7Fns.map Fn.sig := by
  rw [m7ParityVivTiersSplicedFns_eq_splice]
  exact spliceFns_sigs (fun r hr f hf hnm => by
    have idx_39 : m7Fns[39]?.map Fn.sig =
        some ("full_backtrack", [i64, i64], []) := by
      rw [m7_get_p1 (by decide)]; t_kernel_rfl
    have idx_59 : m7Fns[59]?.map Fn.sig =
        some ("m6_hdr_sync_legacy_tiers", [i64], []) := by
      rw [m7_get_p1 (by decide)]; t_kernel_rfl
    have idx_83 : m7Fns[83]?.map Fn.sig =
        some ("full_propagate_ignore_hot", [i64, i64], [i64]) := by
      rw [m7_get_p1 (by decide)]; t_kernel_rfl
    have idx_85 : m7Fns[85]?.map Fn.sig =
        some ("full_propagate_ignore", [i64, i64], [i64]) := by
      rw [m7_get_p1 (by decide)]; t_kernel_rfl
    have idx_217 : m7Fns[217]?.map Fn.sig =
        some ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64]) := by
      rw [show (217 : Nat) = 112 + 105 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl
    have idx_218 : m7Fns[218]?.map Fn.sig =
        some ("full_vivify_m6_hdr", [i64], [i64]) := by
      rw [show (218 : Nat) = 112 + 106 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl
    obtain ⟨f59, hf59, hs59⟩ := sig_of_map_idx idx_59
    obtain ⟨f83, hf83, hs83⟩ := sig_of_map_idx idx_83
    obtain ⟨f85, hf85, hs85⟩ := sig_of_map_idx idx_85
    obtain ⟨f217, hf217, hs217⟩ := sig_of_map_idx idx_217
    obtain ⟨f218, hf218, hs218⟩ := sig_of_map_idx idx_218
    simp only [m7ParityVivTiersPatchFns, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf59
        (hnm.symm.trans (congrArg Prod.fst hs59.symm))
      subst hf0; exact hs59.symm
    · have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf83
        (hnm.symm.trans (congrArg Prod.fst hs83.symm))
      subst hf0; exact hs83.symm
    · have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf85
        (hnm.symm.trans (congrArg Prod.fst hs85.symm))
      subst hf0; exact hs85.symm
    · have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf217
        (hnm.symm.trans (congrArg Prod.fst hs217.symm))
      subst hf0; exact hs217.symm
    · have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf218
        (hnm.symm.trans (congrArg Prod.fst hs218.symm))
      subst hf0; exact hs218.symm)

private theorem m7p_p1_idx {k : Nat} (hk : k < 112) {s : SigEntry}
    (h : m7FnsPart1[k]?.map Fn.sig = some s) : m7Fns[k]?.map Fn.sig = some s := by
  rw [m7_get_p1 hk]; exact h

private theorem m7p_p2_idx {k : Nat} (hk : k < 164) {s : SigEntry}
    (h : m7FnsPart2[k]?.map Fn.sig = some s) : m7Fns[112 + k]?.map Fn.sig = some s := by
  rw [m7_get_p2 hk]; exact h

private theorem m7p_idx_39 : m7Fns[39]?.map Fn.sig =
    some ("full_backtrack", [i64, i64], []) := m7p_p1_idx (by decide) (by t_kernel_rfl)
private theorem m7p_idx_56 : m7Fns[56]?.map Fn.sig =
    some ("m6_ext_ensure_init", [i64], []) := m7p_p1_idx (by decide) (by t_kernel_rfl)
private theorem m7p_idx_59 : m7Fns[59]?.map Fn.sig =
    some ("m6_hdr_sync_legacy_tiers", [i64], []) := m7p_p1_idx (by decide) (by t_kernel_rfl)
private theorem m7p_idx_70 : m7Fns[70]?.map Fn.sig =
    some ("m6_hdr_get_watermark", [i64, i64], [i64]) := m7p_p1_idx (by decide) (by t_kernel_rfl)
private theorem m7p_idx_81 : m7Fns[81]?.map Fn.sig =
    some ("full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool]) :=
  m7p_p1_idx (by decide) (by t_kernel_rfl)
private theorem m7p_idx_82 : m7Fns[82]?.map Fn.sig =
    some ("full_prop_chrono_hot", [i64, i64], [.bool]) := m7p_p1_idx (by decide) (by t_kernel_rfl)
private theorem m7p_idx_83 : m7Fns[83]?.map Fn.sig =
    some ("full_propagate_ignore_hot", [i64, i64], [i64]) :=
  m7p_p1_idx (by decide) (by t_kernel_rfl)
private theorem m7p_idx_85 : m7Fns[85]?.map Fn.sig =
    some ("full_propagate_ignore", [i64, i64], [i64]) :=
  m7p_p1_idx (by decide) (by t_kernel_rfl)
private theorem m7p_idx_86 : m7Fns[86]?.map Fn.sig =
    some ("full_propagate", [i64], [i64]) := m7p_p1_idx (by decide) (by t_kernel_rfl)
private theorem m7p_idx_209 : m7Fns[209]?.map Fn.sig =
    some ("full_viv_clause_m6", [i64, i32], [i64]) :=
  m7p_p2_idx (k := 97) (by decide) (by t_kernel_rfl)
private theorem m7p_idx_211 : m7Fns[211]?.map Fn.sig =
    some ("full_viv_collect_m6", [i64, i64], [i64]) :=
  m7p_p2_idx (k := 99) (by decide) (by t_kernel_rfl)
private theorem m7p_idx_212 : m7Fns[212]?.map Fn.sig =
    some ("full_viv_count_m6", [i64, i64], []) :=
  m7p_p2_idx (k := 100) (by decide) (by t_kernel_rfl)
private theorem m7p_idx_213 : m7Fns[213]?.map Fn.sig =
    some ("full_viv_keys_m6", [i64, i64], []) :=
  m7p_p2_idx (k := 101) (by decide) (by t_kernel_rfl)
private theorem m7p_idx_214 : m7Fns[214]?.map Fn.sig =
    some ("full_viv_sort_sched_m6", [i64, i64], []) :=
  m7p_p2_idx (k := 102) (by decide) (by t_kernel_rfl)
private theorem m7p_idx_215 : m7Fns[215]?.map Fn.sig =
    some ("full_viv_clear_tier_m6", [i64, i64], []) :=
  m7p_p2_idx (k := 103) (by decide) (by t_kernel_rfl)
private theorem m7p_idx_217 : m7Fns[217]?.map Fn.sig =
    some ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64]) :=
  m7p_p2_idx (k := 105) (by decide) (by t_kernel_rfl)
private theorem m7p_idx_218 : m7Fns[218]?.map Fn.sig =
    some ("full_vivify_m6_hdr", [i64], [i64]) :=
  m7p_p2_idx (k := 106) (by decide) (by t_kernel_rfl)

/-- Fast `O(5)` `checkAcyclic = true` preservation on the `410`-fn `m7ParityVivTiersSplicedModule`.
-/
theorem m7ParityVivTiers_spliced_checkAcyclic :
    m7ParityVivTiersSplicedModule.checkAcyclic = true := by
  obtain ⟨f59, hf59, hs59⟩ := sig_of_map_idx m7p_idx_59
  obtain ⟨f83, hf83, hs83⟩ := sig_of_map_idx m7p_idx_83
  obtain ⟨f85, hf85, hs85⟩ := sig_of_map_idx m7p_idx_85
  obtain ⟨f217, hf217, hs217⟩ := sig_of_map_idx m7p_idx_217
  obtain ⟨f218, hf218, hs218⟩ := sig_of_map_idx m7p_idx_218
  obtain ⟨g39, hg39, hsg39⟩ := sig_of_map_idx m7p_idx_39
  obtain ⟨g56, hg56, hsg56⟩ := sig_of_map_idx m7p_idx_56
  obtain ⟨g70, hg70, hsg70⟩ := sig_of_map_idx m7p_idx_70
  obtain ⟨g81, hg81, hsg81⟩ := sig_of_map_idx m7p_idx_81
  obtain ⟨g82, hg82, hsg82⟩ := sig_of_map_idx m7p_idx_82
  obtain ⟨g86, hg86, hsg86⟩ := sig_of_map_idx m7p_idx_86
  obtain ⟨g209, hg209, hsg209⟩ := sig_of_map_idx m7p_idx_209
  obtain ⟨g211, hg211, hsg211⟩ := sig_of_map_idx m7p_idx_211
  obtain ⟨g212, hg212, hsg212⟩ := sig_of_map_idx m7p_idx_212
  obtain ⟨g213, hg213, hsg213⟩ := sig_of_map_idx m7p_idx_213
  obtain ⟨g214, hg214, hsg214⟩ := sig_of_map_idx m7p_idx_214
  obtain ⟨g215, hg215, hsg215⟩ := sig_of_map_idx m7p_idx_215
  change ({ m7Module with fns := m7ParityVivTiersSplicedFns } :
    LeanQbe.T.Module).checkAcyclic = true
  rw [m7ParityVivTiersSplicedFns_eq_splice]
  refine spliceModule_checkAcyclic (M := m7Module) m7_acyclic ?_ ?_
  · intro r hr f hf hnm
    simp only [m7ParityVivTiersPatchFns, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
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
  · intro pre f post r hsplit hr hnm
    simp only [m7Module, List.map_nil, List.append_nil] at hsplit ⊢
    simp only [m7ParityVivTiersPatchFns, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · have hn0 : f.name = f59.name := hnm.symm.trans (congrArg Prod.fst hs59.symm)
      have hc : m7pSyncLegacyTiersFn.checkCallsOk
          [("m6_ext_ensure_init", [i64], [])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact hsg56 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf59 hn0 hg56 (by decide)
    · have hn0 : f.name = f83.name := hnm.symm.trans (congrArg Prod.fst hs83.symm)
      have hc : m7pPropIgnoreHotFn.checkCallsOk
          [ ("full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool])
          , ("full_prop_chrono_hot", [i64, i64], [.bool]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact hsg81 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf83 hn0 hg81 (by decide)
      · exact hsg82 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf83 hn0 hg82 (by decide)
    · have hn0 : f.name = f85.name := hnm.symm.trans (congrArg Prod.fst hs85.symm)
      have hc : m7pPropIgnoreFn.checkCallsOk
          [ ("full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool])
          , ("full_prop_chrono_hot", [i64, i64], [.bool]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact hsg81 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf85 hn0 hg81 (by decide)
      · exact hsg82 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf85 hn0 hg82 (by decide)
    · have hn0 : f.name = f217.name := hnm.symm.trans (congrArg Prod.fst hs217.symm)
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
      · exact hsg39 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf217 hn0 hg39 (by decide)
      · exact hsg211 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf217 hn0 hg211 (by decide)
      · exact hsg212 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf217 hn0 hg212 (by decide)
      · exact hsg213 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf217 hn0 hg213 (by decide)
      · exact hsg214 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf217 hn0 hg214 (by decide)
      · exact hsg209 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf217 hn0 hg209 (by decide)
      · exact hsg86 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf217 hn0 hg86 (by decide)
      · exact hsg215 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf217 hn0 hg215 (by decide)
    · have hn0 : f.name = f218.name := hnm.symm.trans (congrArg Prod.fst hs218.symm)
      have hc : m7pVivifyFn.checkCallsOk
          [ ("full_backtrack", [i64, i64], [])
          , ("m6_hdr_sync_legacy_tiers", [i64], [])
          , ("m6_hdr_get_watermark", [i64, i64], [i64])
          , ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact hsg39 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf218 hn0 hg39 (by decide)
      · exact hs59 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf218 hn0 hf59 (by decide)
      · exact hsg70 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf218 hn0 hg70 (by decide)
      · exact hs217 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf218 hn0 hf217 (by decide)

private theorem m7p_row_sig_of_idx {tbl : List SpecEntry}
    (hsig : tbl.map (fun e => (e.name, e.as, e.rs)) = m7Fns.map Fn.sig)
    {k : Nat} {f : Fn} (hk : m7Fns[k]? = some f)
    {e : SpecEntry} (he : e ∈ tbl) (hnm : e.name = f.name) :
    (e.name, e.as, e.rs) = f.sig := by
  rcases List.mem_iff_getElem.mp he with ⟨j, hj, rfl⟩
  have hlen_t : tbl.length = m7Fns.length := by
    have hl := congrArg List.length hsig
    simpa only [List.length_map] using hl
  have hj_lt : j < m7Fns.length := hlen_t ▸ hj
  have hget_f : (m7Fns.map Fn.sig)[j]? = some (tbl[j].name, tbl[j].as, tbl[j].rs) := by
    rw [← hsig, List.getElem?_map, List.getElem?_eq_getElem hj]
    rfl
  rw [List.getElem?_map, List.getElem?_eq_getElem hj_lt] at hget_f
  rw [Option.map_some, Option.some.injEq] at hget_f
  have hjeq : j = k := idx_eq_of_name_nodup m7_names_nodup hk (List.getElem?_eq_getElem hj_lt)
    (by
      have hn := congrArg Prod.fst hget_f
      simpa [Fn.sig] using hn.trans hnm)
  subst hjeq
  have hfi : m7Fns[j] = f := (List.getElem?_eq_some_iff.mp hk).2
  simpa [hfi] using hget_f.symm

/-- Splicing `m7ParityVivTiersPatchRows` into `m7SpecTable` via `patchRows` preserves all
`410` row signatures identically (`0` spec changes). -/
theorem m7ParityVivTiers_patchRows_sigs (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    (patchRows m7ParityVivTiersPatchRows [] (m7SpecTable tBve solveSpec)).map
        (fun e => (e.name, e.as, e.rs)) =
      m7ParityVivTiersSplicedFns.map Fn.sig := by
  calc (patchRows m7ParityVivTiersPatchRows [] (m7SpecTable tBve solveSpec)).map
        (fun e => (e.name, e.as, e.rs))
      = (spliceRows m7ParityVivTiersPatchRows (m7SpecTable tBve solveSpec)).map
          (fun e => (e.name, e.as, e.rs)) := by rw [patchRows_nil]
    _ = (m7SpecTable tBve solveSpec).map (fun e => (e.name, e.as, e.rs)) :=
        spliceRows_sigs ?_
    _ = m7Fns.map Fn.sig := m7SpecTable_sigs tBve solveSpec hBveSigs
    _ = (spliceFns m7ParityVivTiersPatchFns m7Fns).map Fn.sig := (spliceFns_sigs ?_).symm
    _ = m7ParityVivTiersSplicedFns.map Fn.sig := by
        unfold m7ParityVivTiersSplicedFns; rw [patchFns_nil]
  · obtain ⟨f59, hf59, hs59⟩ := sig_of_map_idx m7p_idx_59
    obtain ⟨f83, hf83, hs83⟩ := sig_of_map_idx m7p_idx_83
    obtain ⟨f85, hf85, hs85⟩ := sig_of_map_idx m7p_idx_85
    obtain ⟨f217, hf217, hs217⟩ := sig_of_map_idx m7p_idx_217
    obtain ⟨f218, hf218, hs218⟩ := sig_of_map_idx m7p_idx_218
    intro r hr e he hnm
    simp only [m7ParityVivTiersPatchRows, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · have hrs := m7p_row_sig_of_idx (m7SpecTable_sigs tBve solveSpec hBveSigs) hf59 he
        (hnm.symm.trans (congrArg Prod.fst hs59.symm))
      exact hs59.symm.trans hrs.symm
    · have hrs := m7p_row_sig_of_idx (m7SpecTable_sigs tBve solveSpec hBveSigs) hf83 he
        (hnm.symm.trans (congrArg Prod.fst hs83.symm))
      exact hs83.symm.trans hrs.symm
    · have hrs := m7p_row_sig_of_idx (m7SpecTable_sigs tBve solveSpec hBveSigs) hf85 he
        (hnm.symm.trans (congrArg Prod.fst hs85.symm))
      exact hs85.symm.trans hrs.symm
    · have hrs := m7p_row_sig_of_idx (m7SpecTable_sigs tBve solveSpec hBveSigs) hf217 he
        (hnm.symm.trans (congrArg Prod.fst hs217.symm))
      exact hs217.symm.trans hrs.symm
    · have hrs := m7p_row_sig_of_idx (m7SpecTable_sigs tBve solveSpec hBveSigs) hf218 he
        (hnm.symm.trans (congrArg Prod.fst hs218.symm))
      exact hs218.symm.trans hrs.symm
  · obtain ⟨f59, hf59, hs59⟩ := sig_of_map_idx m7p_idx_59
    obtain ⟨f83, hf83, hs83⟩ := sig_of_map_idx m7p_idx_83
    obtain ⟨f85, hf85, hs85⟩ := sig_of_map_idx m7p_idx_85
    obtain ⟨f217, hf217, hs217⟩ := sig_of_map_idx m7p_idx_217
    obtain ⟨f218, hf218, hs218⟩ := sig_of_map_idx m7p_idx_218
    intro r hr f hf hnm
    simp only [m7ParityVivTiersPatchFns, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf59
        (hnm.symm.trans (congrArg Prod.fst hs59.symm))
      subst hf0; exact hs59.symm
    · have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf83
        (hnm.symm.trans (congrArg Prod.fst hs83.symm))
      subst hf0; exact hs83.symm
    · have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf85
        (hnm.symm.trans (congrArg Prod.fst hs85.symm))
      subst hf0; exact hs85.symm
    · have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf217
        (hnm.symm.trans (congrArg Prod.fst hs217.symm))
      subst hf0; exact hs217.symm
    · have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf218
        (hnm.symm.trans (congrArg Prod.fst hs218.symm))
      subst hf0; exact hs218.symm

/-- Splicing `m7ParityVivTiersPatchRows` into `m7SpecTable` preserves `noExit = true` across all
`410` entries. -/
theorem m7ParityVivTiers_patchRows_noExit (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBveNoExit : tBve.all SpecEntry.noExit = true) :
    (patchRows m7ParityVivTiersPatchRows [] (m7SpecTable tBve solveSpec)).all
        SpecEntry.noExit = true :=
  patchRows_noExit (m7SpecTable_noExit tBve solveSpec hBveNoExit)
    m7ParityVivTiersPatchRows_noExit (fun _ h => nomatch h)

private theorem m7p_fn_81 : m7Fns[81]? = some FullM7BcpHot.m7PropLitOvfFn := by
  rw [m7_get_p1 (by decide)]; t_kernel_rfl

private theorem m7p_fn_82 : m7Fns[82]? = some FullM7BcpHot.m7PropChronoFn := by
  rw [m7_get_p1 (by decide)]; t_kernel_rfl

def m7pHasBinFn : Fn :=
  ⟨"full_has_bin", [i64, i32, i32], [.bool], Full.full_has_bin_body⟩

def m7pExtraBaseFns : List Fn :=
  [ ⟨"m6_hdr_init", [i64], [], m6_hdr_init_body⟩
  , ⟨"m6_ext_ensure_init", [i64], [], m6_ext_ensure_init_body⟩
  , FullM7BcpHot.m7PropLitOvfFn
  , FullM7BcpHot.m7PropChronoFn
  , m7pHasBinFn ] ++
  FullM6VivBackbone.m6VivBackbone_fns.take 1 ++
  (FullM6VivBackbone.m6VivBackbone_fns.drop 3).take 25

def m7pExtraBaseRows : List SpecEntry :=
  [ ⟨"m6_hdr_init", [i64], [], m6HdrInitSpec, true⟩
  , ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
  , ⟨"full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool],
      FullM7BcpHot.fullPropLitOvfHotSpec, true⟩
  , ⟨"full_prop_chrono_hot", [i64, i64], [.bool],
      FullM7BcpHot.fullPropChronoHotSpec, true⟩
  , ⟨"full_has_bin", [i64, i32, i32], [.bool], Full.fullHasBinSpec, true⟩ ] ++
  FullM6VivBackbone.m6VivBackboneSpecTable.take 1 ++
  (FullM6VivBackbone.m6VivBackboneSpecTable.drop 3).take 25

def m7pExtraRows : List SpecEntry :=
  m7pExtraBaseRows ++
  [⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], m6aVivifyTierSpec, true⟩]

private theorem m7pExtraRows_nodup : (m7pExtraRows.map SpecEntry.name).Nodup := by
  show ([ "m6_hdr_init", "m6_ext_ensure_init", "full_prop_lit_ovf_hot", "full_prop_chrono_hot"
    , "full_has_bin", "full_add_bin_m6"
    , "full_viv_unreason_m6", "full_viv_watch_rank_m6", "full_viv_best_watch_m6"
    , "full_viv_simplify_m6", "full_viv_commit_m6", "full_viv_mark_garb_m6"
    , "full_viv_subsumes_bin_m6", "full_viv_subsumes_cl_m6", "full_viv_deduce_m6"
    , "full_viv_best_implied_m6", "full_viv_reestablish_m6", "full_viv_inst_check_m6"
    , "full_viv_inst_m6", "full_viv_finish_m6", "full_viv_sort_counts_m6"
    , "full_viv_has_l0_m6", "full_viv_l0_simp_m6", "full_viv_reuse_prefix_m6"
    , "full_viv_clause_m6", "full_viv_tier_match_m6", "full_viv_collect_m6"
    , "full_viv_count_m6", "full_viv_keys_m6", "full_viv_sort_sched_m6"
    , "full_viv_clear_tier_m6", "full_vivify_tier_m6_hdr" ] : List String).Nodup
  decide

private theorem m7pExtraRows_noExit : ∀ e ∈ m7pExtraRows, e.noExit = true := by
  intro e he
  exact List.all_eq_true.mp (by t_kernel_rfl : m7pExtraRows.all (·.noExit) = true) e he

private theorem m7p_ofTable_name_mem {nm : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost} :
    ∀ {tbl : List SpecEntry},
    Env.ofTable tbl nm as bs xs m Q X → nm ∈ tbl.map SpecEntry.name
  | [], h => False.elim h
  | e :: _, h => by
    by_cases hnm : e.name = nm
    · rw [← hnm]; exact List.mem_cons_self
    · rw [Env.ofTable_cons_ne hnm] at h
      exact List.mem_cons_of_mem _ (m7p_ofTable_name_mem h)

/-- Hot-BCP + vivification-tier environment extension matching `FullM7Transport0`'s unexposed
`m7Prop{LitOvf,Chrono}HotSpec` entries and vivification helper rows on `Γ`. -/
inductive M7pHotEnv (Γ : Env) : Env where
  | base {f as bs xs m Q X} :
      f ≠ "full_vivify_tier_m6_hdr" →
      Γ f as bs xs m Q X → M7pHotEnv Γ f as bs xs m Q X
  | extra {f as bs xs m Q X} :
      Env.ofTable m7pExtraRows f as bs xs m Q X →
      M7pHotEnv Γ f as bs xs m Q X

theorem m7pHotEnv_noExit {Γ : Env}
    (hΓ : ∀ f as bs xs m Q X X', Γ f as bs xs m Q X → Γ f as bs xs m Q X') :
    ∀ f as bs xs m Q X X',
      M7pHotEnv Γ f as bs xs m Q X → M7pHotEnv Γ f as bs xs m Q X' := by
  intro f as bs xs m Q X X' h
  cases h with
  | base hne hb => exact .base hne (hΓ _ _ _ _ _ _ _ _ hb)
  | extra he => exact .extra (Env.ofTable_noExit m7pExtraRows_noExit _ _ _ _ _ _ _ _ he)

theorem m7pHotEnv_solve_bytes_iff (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    M7pHotEnv (mkM7Env tBve solveSpec) "kissat_solve_bytes"
        [i64, i64, i64, i64, i64] [i64] xs m Q X ↔
      solveSpec xs m Q (fun _ _ _ _ => False) := by
  constructor
  · intro h
    cases h with
    | base _ hb => exact (mkM7Env_solve_bytes_iff tBve solveSpec hBveSigs).mp hb
    | extra he =>
      exfalso
      have hm := m7p_ofTable_name_mem he
      exact absurd hm (by decide)
  · intro hs
    exact M7pHotEnv.base (by decide)
      ((mkM7Env_solve_bytes_iff tBve solveSpec hBveSigs).mpr hs)

private theorem m7p_extra_at {Γ : Env} (i : Nat) (nm : Sym) (as bs : List Ty) (sp : Spec as bs)
    (hi : m7pExtraRows[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ xs m Q X, sp xs m Q X → M7pHotEnv Γ nm as bs xs m Q X := fun xs m Q X hs =>
  M7pHotEnv.extra (Env.ofTable_of_mem (List.mem_of_getElem? hi) m7pExtraRows_nodup
    (hno xs m Q X hs))

private theorem m7p_extra_elim {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7pExtraRows)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable m7pExtraRows nm as bs xs m Q X) :
    sp xs m Q (fun _ _ _ _ => False) :=
  env_ofTable_elim_of_mem hmem m7pExtraRows_nodup h

private theorem m7p_extra_elim_cast {e : SpecEntry} {fn : Fn}
    (hmem : e ∈ m7pExtraRows)
    (hnm : e.name = fn.name) (has : e.as = fn.as) (hrs : e.rs = fn.rs)
    {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (h : Env.ofTable m7pExtraRows fn.name fn.as fn.rs xs m Q X) :
    e.cast has hrs xs m Q X := by
  cases e with
  | mk enm eas ers esp enx =>
    dsimp only at hnm has hrs
    cases hnm; cases has; cases hrs
    exact env_ofTable_elim_of_mem hmem m7pExtraRows_nodup h

private theorem m7p_tableImpl_getElem {Γ : Env} :
    ∀ {fs : List Fn} {rs : List SpecEntry} (i : Nat)
      (h1 : i < fs.length) (h2 : i < rs.length),
      TableImpl Γ fs rs → SpecEntry.Impl Γ (fs[i]'h1) (rs[i]'h2)
  | [], _, i, h1, _, _ => absurd h1 (Nat.not_lt_zero i)
  | _ :: _, [], _, _, _, ht => False.elim ht
  | _ :: _, _ :: _, 0, _, _, ht => ht.1
  | _ :: _, _ :: _, i + 1, h1, h2, ht =>
    m7p_tableImpl_getElem i (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2) ht.2

mutual
private def m7pNoCall (nm : Sym) {rs : List Ty} :
    Expr (fun _ => Unit) (fun _ => Unit) rs → Bool
  | .let_ _ k => m7pNoCall nm (k (Tup.units _))
  | .load _ _ k => m7pNoCall nm (k ())
  | .store _ _ k => m7pNoCall nm k
  | .call f _ k => (f != nm) && m7pNoCall nm (k (Tup.units _))
  | .jnz _ t e => m7pNoCall nm t && m7pNoCall nm e
  | .jump _ _ | .ret _ | .hlt | .exit _ _ => true
  | .group (sig := sig) bodies k =>
      m7pBlocksNoCall nm (bodies (Tup.units sig)) && m7pNoCall nm (k (Tup.units sig))

private def m7pBlocksNoCall (nm : Sym) {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Unit) rs sig → Bool
  | _, .nil => true
  | _, .cons b bs => m7pNoCall nm (b (Tup.units _)) && m7pBlocksNoCall nm bs
end

mutual
private theorem m7p_callsOk_filter (nm : Sym) {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} :
    (e : Expr (fun _ => Unit) (fun _ => Unit) rs) →
    e.callsOk allowed exits → m7pNoCall nm e = true →
    e.callsOk (allowed.filter (fun s => s.1 != nm)) exits
  | .let_ _ k, hc, hn => m7p_callsOk_filter nm (k (Tup.units _)) hc hn
  | .load _ _ k, hc, hn => m7p_callsOk_filter nm (k ()) hc hn
  | .store _ _ k, hc, hn => m7p_callsOk_filter nm k hc hn
  | .call f (as := _) (bs := bs) _ k, hc, hn => by
    change (_ && _) = true at hn
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hn
    exact ⟨List.mem_filter.mpr ⟨hc.1, h1⟩,
      m7p_callsOk_filter nm (k (Tup.units bs)) hc.2 h2⟩
  | .jnz _ t e, hc, hn => by
    change (_ && _) = true at hn
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hn
    exact ⟨m7p_callsOk_filter nm t hc.1 h1, m7p_callsOk_filter nm e hc.2 h2⟩
  | .jump _ _, hc, _ | .ret _, hc, _ | .hlt, hc, _ | .exit _ _, hc, _ => hc
  | .group (sig := sig) bodies k, hc, hn => by
    change (_ && _) = true at hn
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hn
    exact ⟨m7p_blocksCallsOk_filter nm (bodies (Tup.units sig)) hc.1 h1,
      m7p_callsOk_filter nm (k (Tup.units sig)) hc.2 h2⟩

private theorem m7p_blocksCallsOk_filter (nm : Sym) {allowed : List SigEntry}
    {exits : List Sym} {rs : List Ty} :
    {sig : List (List Ty)} → (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig) →
    bs.callsOk allowed exits → m7pBlocksNoCall nm bs = true →
    bs.callsOk (allowed.filter (fun s => s.1 != nm)) exits
  | _, .nil, _, _ => trivial
  | _, .cons b bs, hc, hn => by
    change (_ && _) = true at hn
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hn
    exact ⟨m7p_callsOk_filter nm (b (Tup.units _)) hc.1 h1,
      m7p_blocksCallsOk_filter nm bs hc.2 h2⟩
end

private theorem m7p_all_nonviv_no_vt :
    (m7Fns.filter (fun fn => fn.name != "full_vivify_m6_hdr")).all
      (fun fn => m7pNoCall "full_vivify_tier_m6_hdr"
        (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as))) = true := by
  t_kernel_rfl

private theorem m7p_extraBaseFns_sigs :
    m7pExtraBaseRows.map (fun e => (e.name, e.as, e.rs)) = m7pExtraBaseFns.map Fn.sig := by
  t_kernel_rfl

private theorem m7p_extraBaseFns_sub : ∀ f ∈ m7pExtraBaseFns, f ∈ m7Fns := by
  have hf54 : m7Fns[54]? = some ⟨"m6_hdr_init", [i64], [], m6_hdr_init_body⟩ := by
    rw [m7_get_p1 (by decide)]; t_kernel_rfl
  have hf56 : m7Fns[56]? = some ⟨"m6_ext_ensure_init", [i64], [], m6_ext_ensure_init_body⟩ := by
    rw [m7_get_p1 (by decide)]; t_kernel_rfl
  have hf175 : m7Fns[175]? = some m7pHasBinFn := by
    rw [show (175 : Nat) = 112 + 63 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl
  have hf177 : (m7FnsPart2.drop 65).take 1 = FullM6VivBackbone.m6VivBackbone_fns.take 1 := by
    t_kernel_rfl
  have hfViv : (m7FnsPart2.drop 79).take 25 =
      (FullM6VivBackbone.m6VivBackbone_fns.drop 3).take 25 := by t_kernel_rfl
  intro f hf
  simp only [m7pExtraBaseFns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with ((rfl | rfl | rfl | rfl | rfl) | hab) | hviv
  · exact List.mem_of_getElem? hf54
  · exact List.mem_of_getElem? hf56
  · exact List.mem_of_getElem? m7p_fn_81
  · exact List.mem_of_getElem? m7p_fn_82
  · exact List.mem_of_getElem? hf175
  · rw [← hf177] at hab
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_of_mem_drop (List.mem_of_mem_take hab)))
  · rw [← hfViv] at hviv
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_of_mem_drop (List.mem_of_mem_take hviv)))

private theorem m7p_hasBin_wp (Γ : Env) :
    ∀ a m Q X, Full.fullHasBinSpec a m Q X → Func.wp Γ Full.full_has_bin_body a m Q X := by
  have hf97 : Full.fullFns[97]? = some m7pHasBinFn := by t_kernel_rfl
  have hndF : ((Full.fullSpecTable Full.fullSolveBytesSpec).map SpecEntry.name).Nodup := by
    have hm := congrArg (List.map Prod.fst) (Full.fullSpecTable_sigs Full.fullSolveBytesSpec)
    have hn : (Full.fullSpecTable Full.fullSolveBytesSpec).map SpecEntry.name =
        Full.fullFns.map Fn.name := by
      simpa only [List.map_map, Function.comp_def, Fn.sig] using hm
    exact tbl_nodup_of_sigs (M := Full.fullModule) Full.full_acyclic hn
  have hrow97 : (Full.fullSpecTable Full.fullSolveBytesSpec)[97]? =
      some ⟨"full_has_bin", [i64, i32, i32], [.bool], Full.fullHasBinSpec, true⟩ := by
    t_kernel_rfl
  obtain ⟨pre, post, hsp⟩ := List.append_of_mem (List.mem_of_getElem? hf97)
  have ⟨hwf, _, hwp⟩ := Full.fullEnv_moduleOk.fnsOk pre m7pHasBinFn post hsp
  have hcalls : m7pHasBinFn.callsOk [] [] := Fn.callsOk_of_checkCallsOk (by t_kernel_rfl)
  intro xs m Q X hspec
  have henv : Full.fullEnv "full_has_bin" [i64, i32, i32] [.bool] xs m Q X :=
    Env.ofTable_of_mem (List.mem_of_getElem? hrow97) hndF hspec
  exact wp_env_agree_of_callsOk
    (hwf Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units _))
    hcalls (fun _ _ _ h => nomatch h) m (hwp xs m Q X henv)

/-- Closed `410`-fn `ModuleOk` for `m7ParityVivTiersSplicedModule` under
`M7pHotEnv (mkM7Env tBve solveSpec)`. -/
theorem m7ParityVivTiers_spliced_moduleOk
    (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hWeaken : ∀ a m Q X, solveSpec a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hSolveMonoX : ∀ a m Q X X', solveSpec a m Q X → solveSpec a m Q X')
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve solveSpec) m7BveAllFns tBve) :
    ModuleOk (M7pHotEnv (mkM7Env tBve solveSpec)) m7ParityVivTiersSplicedModule := by
  have hm := mkM7Env_moduleOk tBve solveSpec hWeaken hSolveMonoX
    hBveSigs hBveNoExit hBveSpecs hBveOk
  have hnd := m7SpecTable_nodup tBve solveSpec hBveSigs
  have hc1 := m7Part1Callees_of_sub (m7SpecTable_part1_mem (tBve := tBve) (solveSpec := solveSpec))
  have hc2 := m7Part2Callees_of_sub (m7SpecTable_part2_mem (tBve := tBve) (solveSpec := solveSpec))
  have hc2p :=
    m7Part2PfxCallees_of_sub (m7SpecTable_part2_mem (tBve := tBve) (solveSpec := solveSpec))
  have hWp := m7SpecTable_pfx_mem (tBve := tBve) (solveSpec := solveSpec) _
    m7OrchPfxRows_specs.watchPush
  have hWd := m7SpecTable_pfx_mem (tBve := tBve) (solveSpec := solveSpec) _
    m7OrchPfxRows_specs.wstackDefrag
  let Γ0 := mkM7Env tBve solveSpec
  let Γ' := M7pHotEnv Γ0
  have hbase : ∀ (nm : Sym) (as bs : List Ty) (sp : Spec as bs),
      nm ≠ "full_vivify_tier_m6_hdr" →
      (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7SpecTable tBve solveSpec →
      (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
        exact fun _ _ _ _ h => h) →
      ∀ xs m Q X, sp xs m Q X → Γ' nm as bs xs m Q X :=
    fun nm as bs sp hne hmem hno xs m Q X hsp =>
      M7pHotEnv.base hne (mkM7Env_row_mem hnd nm as bs sp hmem hno xs m Q X hsp)
  have rInit := m7p_extra_at (Γ := Γ0) 0 "m6_hdr_init" [i64] [] m6HdrInitSpec rfl
    (fun _ _ _ _ h => m6HdrInitSpec_monoX h)
  have rEnsure := m7p_extra_at (Γ := Γ0) 1 "m6_ext_ensure_init" [i64] []
    m6ExtEnsureInitSpec rfl (fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h)
  have rOvf := m7p_extra_at (Γ := Γ0) 2 "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool]
    FullM7BcpHot.fullPropLitOvfHotSpec rfl
  have rChrono := m7p_extra_at (Γ := Γ0) 3 "full_prop_chrono_hot" [i64, i64] [.bool]
    FullM7BcpHot.fullPropChronoHotSpec rfl
  have rHb := m7p_extra_at (Γ := Γ0) 4 "full_has_bin" [i64, i32, i32] [.bool]
    Full.fullHasBinSpec rfl
  have rAb6 := m7p_extra_at (Γ := Γ0) 5 "full_add_bin_m6" [i64, i32, i32] [i64]
    FullM6VivBackbone.fullAddBinM6Spec rfl
  have rBt := hbase _ _ _ _ (by decide) hc1.backtrack
  have rUnw := hbase _ _ _ _ (by decide) hc1.unwatchLarge
  have rAu := hbase _ _ _ _ (by decide) hc2.addUnit
  have rAsg := hbase _ _ _ _ (by decide) hc1.assign
  have rALvl := hbase _ _ _ _ (by decide) hc1.assignLvl
  have rPI := hbase _ _ _ _ (by decide) hc1.propagateIgn
  have rNext := hbase _ _ _ _ (by decide) hc1.arenaNext
  have rWp := hbase _ _ _ _ (by decide) hWp
  have rWd := hbase _ _ _ _ (by decide) hWd
  have rPropS15 := m7_fullPropagate_to_bcpS15 (hbase _ _ _ _ (by decide) hc1.propagate)
  have rSync := hbase _ _ _ _ (by decide) hc1.hdrSyncLegacy
    (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rGetWm := hbase _ _ _ _ (by decide) hc1.hdrGetWm
    (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rVivTier := m7p_extra_at (Γ := Γ0) 31 _ _ _ _ rfl
    (fun _ _ _ _ h => m6aVivifyTierSpec_monoX h)
  have r0 := m7p_extra_at (Γ := Γ0) 6 _ _ _ _ rfl
  have r1 := m7p_extra_at (Γ := Γ0) 7 _ _ _ _ rfl
  have r2 := m7p_extra_at (Γ := Γ0) 8 _ _ _ _ rfl
  have r3 := m7p_extra_at (Γ := Γ0) 9 _ _ _ _ rfl
  have r4 := m7p_extra_at (Γ := Γ0) 10 _ _ _ _ rfl
  have r5 := m7p_extra_at (Γ := Γ0) 11 _ _ _ _ rfl
  have r6 := m7p_extra_at (Γ := Γ0) 12 _ _ _ _ rfl
  have r7 := m7p_extra_at (Γ := Γ0) 13 _ _ _ _ rfl
  have r8 := m7p_extra_at (Γ := Γ0) 14 _ _ _ _ rfl
  have r9 := m7p_extra_at (Γ := Γ0) 15 _ _ _ _ rfl
  have r10 := m7p_extra_at (Γ := Γ0) 16 _ _ _ _ rfl
  have r11 := m7p_extra_at (Γ := Γ0) 17 _ _ _ _ rfl
  have r12 := m7p_extra_at (Γ := Γ0) 18 _ _ _ _ rfl
  have r13 := m7p_extra_at (Γ := Γ0) 19 _ _ _ _ rfl
  have r14 := m7p_extra_at (Γ := Γ0) 20 _ _ _ _ rfl
  have r15 := m7p_extra_at (Γ := Γ0) 21 _ _ _ _ rfl
  have r16 := m7p_extra_at (Γ := Γ0) 22 _ _ _ _ rfl
  have r17 := m7p_extra_at (Γ := Γ0) 23 _ _ _ _ rfl
  have r18 := m7p_extra_at (Γ := Γ0) 24 _ _ _ _ rfl
  have r19 := m7p_extra_at (Γ := Γ0) 25 _ _ _ _ rfl
  have r20 := m7p_extra_at (Γ := Γ0) 26 _ _ _ _ rfl
  have r21 := m7p_extra_at (Γ := Γ0) 27 _ _ _ _ rfl
  have r22 := m7p_extra_at (Γ := Γ0) 28 _ _ _ _ rfl
  have r23 := m7p_extra_at (Γ := Γ0) 29 _ _ _ _ rfl
  have r24 := m7p_extra_at (Γ := Γ0) 30 _ _ _ _ rfl
  have hExtraImpl : TableImpl Γ' m7pExtraBaseFns m7pExtraBaseRows := by
    have h5 : TableImpl Γ'
        [ ⟨"m6_hdr_init", [i64], [], m6_hdr_init_body⟩
        , ⟨"m6_ext_ensure_init", [i64], [], m6_ext_ensure_init_body⟩
        , FullM7BcpHot.m7PropLitOvfFn
        , FullM7BcpHot.m7PropChronoFn
        , m7pHasBinFn ]
        [ ⟨"m6_hdr_init", [i64], [], m6HdrInitSpec, true⟩
        , ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
        , ⟨"full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool],
            FullM7BcpHot.fullPropLitOvfHotSpec, true⟩
        , ⟨"full_prop_chrono_hot", [i64, i64], [.bool],
            FullM7BcpHot.fullPropChronoHotSpec, true⟩
        , ⟨"full_has_bin", [i64, i32, i32], [.bool], Full.fullHasBinSpec, true⟩ ] :=
      ⟨ SpecEntry.Impl.of (m6_hdr_init_wp Γ')
      , SpecEntry.Impl.of (m6_ext_ensure_init_wp Γ' rInit)
      , SpecEntry.Impl.of (FullM7BcpHot.full_prop_lit_ovf_hot_wp Γ' rWp)
      , SpecEntry.Impl.of (FullM7BcpHot.full_prop_chrono_hot_wp Γ' rWd rUnw rWp)
      , SpecEntry.Impl.of (m7p_hasBin_wp Γ'), trivial ⟩
    have hAbImpl : TableImpl Γ' (FullM6VivBackbone.m6VivBackbone_fns.take 1)
        (FullM6VivBackbone.m6VivBackboneSpecTable.take 1) := by
      rw [show FullM6VivBackbone.m6VivBackbone_fns.take 1 =
          [⟨"full_add_bin_m6", [i64, i32, i32], [i64],
            FullM6VivBackbone.full_add_bin_m6_body⟩] from rfl]
      exact ⟨SpecEntry.Impl.of
        (FullM6VivBackbone.full_add_bin_m6_ext_wp Γ' rHb rALvl rWp), trivial⟩
    have hVivImpl : TableImpl Γ' ((FullM6VivBackbone.m6VivBackbone_fns.drop 3).take 25)
        ((FullM6VivBackbone.m6VivBackboneSpecTable.drop 3).take 25) := by
      rw [show (FullM6VivBackbone.m6VivBackbone_fns.drop 3).take 25 =
          [ ⟨"full_viv_unreason_m6", [i64, i32], [], FullM6VivBackbone.full_viv_unreason_m6_body⟩
          , ⟨"full_viv_watch_rank_m6", [i64, i32], [i64],
              FullM6VivBackbone.full_viv_watch_rank_m6_body⟩
          , ⟨"full_viv_best_watch_m6", [i64, i32], [],
              FullM6VivBackbone.full_viv_best_watch_m6_body⟩
          , ⟨"full_viv_simplify_m6", [i64, i32], [i64],
              FullM6VivBackbone.full_viv_simplify_m6_body⟩
          , ⟨"full_viv_commit_m6", [i64, i32, i32, i32], [i64],
              FullM6VivBackbone.full_viv_commit_m6_body⟩
          , ⟨"full_viv_mark_garb_m6", [i64, i32], [],
              FullM6VivBackbone.full_viv_mark_garb_m6_body⟩
          , ⟨"full_viv_subsumes_bin_m6", [i64, i32, i32], [.bool],
              FullM6VivBackbone.full_viv_subsumes_bin_m6_body⟩
          , ⟨"full_viv_subsumes_cl_m6", [i64, i32, i32], [.bool],
              FullM6VivBackbone.full_viv_subsumes_cl_m6_body⟩
          , ⟨"full_viv_deduce_m6", [i64, i32, i32, i32], [i32],
              FullM6VivBackbone.full_viv_deduce_m6_body⟩
          , ⟨"full_viv_best_implied_m6", [i64, i32], [i32],
              FullM6VivBackbone.full_viv_best_implied_m6_body⟩
          , ⟨"full_viv_reestablish_m6", [i64, i32], [],
              FullM6VivBackbone.full_viv_reestablish_m6_body⟩
          , ⟨"full_viv_inst_check_m6", [i64, i32, i32, i32], [.bool],
              FullM6VivBackbone.full_viv_inst_check_m6_body⟩
          , ⟨"full_viv_inst_m6", [i64, i32, i32], [i64],
              FullM6VivBackbone.full_viv_inst_m6_body⟩
          , ⟨"full_viv_finish_m6", [i64, i32, i32, .bool, i32, .bool], [i64],
              FullM6VivBackbone.full_viv_finish_m6_body⟩
          , ⟨"full_viv_sort_counts_m6", [i64, i32], [],
              FullM6VivBackbone.full_viv_sort_counts_m6_body⟩
          , ⟨"full_viv_has_l0_m6", [i64, i32, i32], [.bool],
              FullM6VivBackbone.full_viv_has_l0_m6_body⟩
          , ⟨"full_viv_l0_simp_m6", [i64, i32, i32], [i64],
              FullM6VivBackbone.full_viv_l0_simp_m6_body⟩
          , ⟨"full_viv_reuse_prefix_m6", [i64, i32, i32], [],
              FullM6VivBackbone.full_viv_reuse_prefix_m6_body⟩
          , ⟨"full_viv_clause_m6", [i64, i32], [i64],
              FullM6VivBackbone.full_viv_clause_m6_body⟩
          , ⟨"full_viv_tier_match_m6", [i64, i32, i64], [.bool],
              FullM6VivBackbone.full_viv_tier_match_m6_body⟩
          , ⟨"full_viv_collect_m6", [i64, i64], [i64],
              FullM6VivBackbone.full_viv_collect_m6_body⟩
          , ⟨"full_viv_count_m6", [i64, i64], [],
              FullM6VivBackbone.full_viv_count_m6_body⟩
          , ⟨"full_viv_keys_m6", [i64, i64], [], FullM6VivBackbone.full_viv_keys_m6_body⟩
          , ⟨"full_viv_sort_sched_m6", [i64, i64], [],
              FullM6VivBackbone.full_viv_sort_sched_m6_body⟩
          , ⟨"full_viv_clear_tier_m6", [i64, i64], [],
              FullM6VivBackbone.full_viv_clear_tier_m6_body⟩ ] from rfl]
      exact ⟨ SpecEntry.Impl.of (FullM6VivBackbone.full_viv_unreason_m6_wp Γ' rBt)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_watch_rank_m6_wp Γ')
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_best_watch_m6_wp Γ' r1)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_simplify_m6_wp Γ' rUnw rAu rAb6 rWp)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_commit_m6_wp Γ'
            rBt rUnw rAu rAb6 rWp r0 r2)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_mark_garb_m6_wp Γ' r0 rUnw)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_subsumes_bin_m6_wp Γ')
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_subsumes_cl_m6_wp Γ')
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_deduce_m6_wp Γ' r6 r7)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_best_implied_m6_wp Γ')
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_reestablish_m6_wp Γ' rBt)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_inst_check_m6_wp Γ')
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_inst_m6_wp Γ'
            rBt rAsg rPI r8 r11 r4)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_finish_m6_wp Γ'
            r8 r5 rBt r4 r10 r12)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_sort_counts_m6_wp Γ')
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_has_l0_m6_wp Γ')
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_l0_simp_m6_wp Γ' r15 rBt r3)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_reuse_prefix_m6_wp Γ' rBt)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_clause_m6_wp Γ'
            r16 r14 r17 r9 rAsg rPI rBt r13)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_tier_match_m6_wp Γ')
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_collect_m6_wp Γ' rNext r19)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_count_m6_wp Γ')
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_keys_m6_wp Γ')
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_sort_sched_m6_wp Γ')
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_clear_tier_m6_wp Γ' rNext r19)
        , trivial ⟩
    exact tableImpl_append rfl (tableImpl_append rfl h5 hAbImpl) hVivImpl
  have hwfOrig := allFns_wf_of_moduleOk hm
  have hm217 : m7Fns[217]? = some FullM6OrchAdapters.m6aVivifyTierM6HdrFn := by
    rw [show (217 : Nat) = 112 + 105 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl
  have hm218 : m7Fns[218]? = some FullM6OrchAdapters.m6aVivifyM6HdrFn := by
    rw [show (218 : Nat) = 112 + 106 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl
  have hnotExtra : ∀ (nm : Sym) {as bs xs m Q X}, nm ∉ m7pExtraRows.map SpecEntry.name →
      Env.ofTable m7pExtraRows nm as bs xs m Q X → False := by
    intro _ _ _ _ _ _ _ hni he; exact hni (m7p_ofTable_name_mem he)
  have hM_hot : ModuleOk Γ' m7Module := by
    refine LeanQbe.T.Module.moduleOk_of_checkAcyclic m7_acyclic hwfOrig ?_
    intro g hg xs m Q X hrow
    change g ∈ m7Fns at hg
    by_cases hgt : g.name = "full_vivify_tier_m6_hdr"
    · have hgeq : g = FullM6OrchAdapters.m6aVivifyTierM6HdrFn :=
        fn_eq_of_mem_idx m7_names_nodup hg hm217 hgt
      subst hgeq
      cases hrow with
      | base hne _ => exact absurd rfl hne
      | extra he =>
        have hspec : m6aVivifyTierSpec xs m Q X :=
          m6aVivifyTierSpec_monoX (m7p_extra_elim (List.mem_of_getElem? (i := 31) rfl) he)
        exact FullM6OrchAdapters.full_vivify_tier_m6_hdr_wp Γ'
          rBt r20 r21 r22 r23 r18 rPropS15 r24 xs m Q X hspec
    · by_cases hgm : g.name = "full_vivify_m6_hdr"
      · have hgeq : g = FullM6OrchAdapters.m6aVivifyM6HdrFn :=
          fn_eq_of_mem_idx m7_names_nodup hg hm218 hgm
        subst hgeq
        cases hrow with
        | base _ hb =>
          have hspec : m6aVivifySpec xs m Q X :=
            m6aVivifySpec_monoX (mkM7Env_elim_of_mem hc2p.vivifyM6Hdr hnd hb)
          exact FullM6OrchAdapters.full_vivify_m6_hdr_wp Γ'
            rBt rSync rGetWm rVivTier xs m Q X hspec
        | extra he => exact False.elim (hnotExtra _ (by decide) he)
      · cases hrow with
        | base _ hb =>
          obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
          have ⟨hwfG, hcallsG, hwpG⟩ := hm.fnsOk pre g post hsplit
          have hnoVt : m7pNoCall "full_vivify_tier_m6_hdr"
              (g.body (fun _ => Unit) (fun _ => Unit) (Tup.units g.as)) = true :=
            (List.all_eq_true.mp m7p_all_nonviv_no_vt g
              (List.mem_filter.mpr ⟨hg, bne_iff_ne.mpr hgm⟩))
          exact wp_env_agree_of_callsOk
            (hwfG Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units g.as))
            (m7p_callsOk_filter "full_vivify_tier_m6_hdr" _ hcallsG hnoVt)
            (fun f as bs hmem' _ _ _ _ hc =>
              M7pHotEnv.base (bne_iff_ne.mp (List.mem_filter.mp hmem').2) hc)
            m (hwpG xs m Q X hb)
        | extra he =>
          have hm_n := m7p_ofTable_name_mem he
          have hbase_mem : g.name ∈ m7pExtraBaseRows.map SpecEntry.name := by
            simpa [m7pExtraRows, List.map_append, hgt] using hm_n
          rcases List.mem_map.mp hbase_mem with ⟨r, hr, hnm⟩
          rcases List.mem_iff_getElem.mp hr with ⟨idx, hidx, rfl⟩
          have hlen_e : m7pExtraBaseFns.length = m7pExtraBaseRows.length := by
            have hl := congrArg List.length m7p_extraBaseFns_sigs
            simpa only [List.length_map] using hl.symm
          have hidx_f : idx < m7pExtraBaseFns.length := hlen_e ▸ hidx
          have hf_idx : m7pExtraBaseFns[idx]'hidx_f ∈ m7pExtraBaseFns := List.getElem_mem hidx_f
          have hsig_eq : (m7pExtraBaseRows[idx].name, m7pExtraBaseRows[idx].as,
              m7pExtraBaseRows[idx].rs) = (m7pExtraBaseFns[idx]'hidx_f).sig := by
            have hopt := congrArg (fun l => l[idx]?) m7p_extraBaseFns_sigs
            rw [List.getElem?_map, List.getElem?_eq_getElem hidx, List.getElem?_map,
              List.getElem?_eq_getElem hidx_f] at hopt
            exact Option.some.inj hopt
          have hfn_eq_name : (m7pExtraBaseFns[idx]'hidx_f).name = g.name :=
            (congrArg Prod.fst hsig_eq).symm.trans hnm
          have hg_eq : g = m7pExtraBaseFns[idx]'hidx_f := by
            have hm1 := m7p_extraBaseFns_sub _ hf_idx
            rcases List.mem_iff_getElem.mp hg with ⟨i1, hi1, rfl⟩
            rcases List.mem_iff_getElem.mp hm1 with ⟨i2, hi2, heq2⟩
            have heq_idx : i1 = i2 := idx_eq_of_name_nodup m7_names_nodup
              (List.getElem?_eq_getElem hi2) (List.getElem?_eq_getElem hi1)
              (by rw [heq2]; exact hfn_eq_name.symm)
            subst heq_idx
            exact heq2
          subst hg_eq
          have hImpl_idx : SpecEntry.Impl Γ' (m7pExtraBaseFns[idx]'hidx_f)
              (m7pExtraBaseRows[idx]'hidx) :=
            m7p_tableImpl_getElem idx hidx_f hidx hExtraImpl
          have r_in_extra : m7pExtraBaseRows[idx] ∈ m7pExtraRows :=
            List.mem_append_left _ (List.getElem_mem hidx)
          rcases hImpl_idx with ⟨⟨hn, ha, hr_⟩, hwp⟩
          exact hwp xs m Q X (m7p_extra_elim_cast r_in_extra hn ha hr_ he)
  change ModuleOk Γ' { m7Module with fns := m7ParityVivTiersSplicedFns }
  rw [show ({ m7Module with fns := m7ParityVivTiersSplicedFns } : LeanQbe.T.Module) =
      { m7Module with fns := spliceFns m7ParityVivTiersPatchFns m7Module.fns } by
    rw [m7ParityVivTiersSplicedFns_eq_splice]; rfl]
  refine spliceModule_moduleOk_sameEnv hM_hot
    (by
      change ({ m7Module with fns := spliceFns m7ParityVivTiersPatchFns m7Fns } :
        LeanQbe.T.Module).checkAcyclic = true
      rw [← m7ParityVivTiersSplicedFns_eq_splice]
      exact m7ParityVivTiers_spliced_checkAcyclic)
    m7ParityVivTiersPatchFns_wf ?_
  intro r hr xs m Q X hrow
  simp only [m7ParityVivTiersPatchFns, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · cases hrow with
    | base _ hb =>
      exact m6_hdr_sync_legacy_tiers_wp Γ' rEnsure xs m Q X
        (m6HdrW2aSpec_monoX (mkM7Env_elim_of_mem hc1.hdrSyncLegacy hnd hb))
    | extra he => exact False.elim (hnotExtra _ (by decide) he)
  · cases hrow with
    | base _ hb =>
      exact full_propagate_ignore_hot_wp Γ' rOvf rChrono xs m Q X
        (mkM7Env_elim_of_mem hc1.propIgnoreHot hnd hb)
    | extra he => exact False.elim (hnotExtra _ (by decide) he)
  · cases hrow with
    | base _ hb =>
      exact full_propagate_ignore_canon_hot_wp Γ' rOvf rChrono xs m Q X
        (mkM7Env_elim_of_mem hc1.propagateIgn hnd hb)
    | extra he => exact False.elim (hnotExtra _ (by decide) he)
  · cases hrow with
    | base hne _ => exact absurd rfl hne
    | extra he =>
      have hspec : m6aVivifyTierSpec xs m Q X :=
        m6aVivifyTierSpec_monoX (m7p_extra_elim (List.mem_of_getElem? (i := 31) rfl) he)
      exact full_vivify_tier_m6_hdr_wp Γ'
        rBt r20 r21 r22 r23 r18 rPropS15 r24 xs m Q X hspec
  · cases hrow with
    | base _ hb =>
      exact full_vivify_m6_hdr_wp Γ' rBt rSync rGetWm rVivTier xs m Q X
        (m6aVivifySpec_monoX (mkM7Env_elim_of_mem hc2p.vivifyM6Hdr hnd hb))
    | extra he => exact False.elim (hnotExtra _ (by decide) he)

theorem m7ParityVivTiers_solveBytes_mem :
    FullM6Orch.m6oSolveBytesFn ∈ m7ParityVivTiersSplicedModule.fns := by
  change FullM6Orch.m6oSolveBytesFn ∈ m7ParityVivTiersSplicedFns
  rw [m7ParityVivTiersSplicedFns_eq_splice]
  exact spliceFns_mem_of_ne m7oSolveBytesFn_mem fun r hr => by
    simp only [m7ParityVivTiersPatchFns, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Top-level `kissat_solve_bytes` soundness for `m7ParityVivTiersSplicedModule`. -/
theorem m7ParityVivTiers_spliced_solve_bytes_sound
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
    Func.wp (M7pHotEnv (mkM7Env tBve fullM6SolveBytesSpec)) FullM6Orch.kissat_solve_bytes_body
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
    (m7ParityVivTiers_spliced_moduleOk tBve fullM6SolveBytesSpec
      (fun _ _ _ _ h => fullM6SolveBytesCoreModelSpec_of_spec h)
      (fun _ _ _ _ _ h => fullM6SolveBytesSpec_monoX h)
      hBveSigs hBveNoExit hBveSpecs hBveOk)
    m7ParityVivTiers_solveBytes_mem
    (fun _ _ _ _ hs =>
      (m7pHotEnv_solve_bytes_iff tBve fullM6SolveBytesSpec hBveSigs).mpr
        (fullM6SolveBytesSpec_monoX hs))
    hcfit hwfit hm

/-- Concrete deterministic UNSAT non-vacuity (`XPost := False`, `r = 20#64`) for
`m7ParityVivTiersSplicedModule`. -/
theorem m7ParityVivTiers_spliced_unsat_nv
    (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesCoreModelSpec) m7BveAllFns tBve) :
    Func.wp (M7pHotEnv (mkM7Env tBve fullM6SolveBytesCoreModelSpec))
      FullM6Orch.kissat_solve_bytes_body
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
    (m7ParityVivTiers_spliced_moduleOk tBve fullM6SolveBytesCoreModelSpec
      (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => fullM6SolveBytesCoreModelSpec_monoX h)
      hBveSigs hBveNoExit hBveSpecs hBveOk)
    m7ParityVivTiers_solveBytes_mem
    (fun _ _ _ _ hs =>
      (m7pHotEnv_solve_bytes_iff tBve fullM6SolveBytesCoreModelSpec hBveSigs).mpr
        (fullM6SolveBytesCoreModelSpec_monoX hs))

/-! ## 3. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, zero SAT model checks) -/

section ConcreteNonVacuity

private theorem nvM7p_F0_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by
        dsimp only [nvOneLitF0, cnfOfClauses]; exact Array.mem_def.mpr List.mem_cons_self))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by
        dsimp only [nvOneLitF0, cnfOfClauses]
        exact Array.mem_def.mpr (List.mem_cons_of_mem _ List.mem_cons_self)))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;>
    simp only [litOfLiteral, mkLit, Bool.false_eq_true, eq_self, ↓reduceIte] at hm0 hm1
  · omega
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

private theorem nvM7p_sparseW :
    FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState := by
  have hmv : nvOneLitCfg.max_vars = 1 := rfl
  have hcv : nvOneLitState.core.cur_vars = 1 := rfl
  have hte : nvOneLitState.core.trail_end = 1 := rfl
  have hcl : nvOneLitState.core.cur_level = 0 := rfl
  have hdm : nvOneLitState.core.dense_mode = 0#64 := rfl
  have hrefs : fullArenaClauseRefsCore nvOneLitState.core = [] := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvOneLitState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        exact absurd hp (by dsimp only [fullWatchSizeCore, nvOneLitState]; decide)
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        exact absurd hp (by dsimp only [fullWatchSizeCore, nvOneLitState]; decide)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> exact WatchSliceOk.empty
  have hent0 : (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) := by
    rw [CNF.entails_clause_def]; intro α hα
    exact (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by
        dsimp only [cnfOfClauses]; exact Array.mem_def.mpr List.mem_cons_self))
  have hw : FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState.core :=
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl,
        fun r hr => (by rw [hrefs] at hr; cases hr),
        fun r hr => (by rw [hrefs] at hr; cases hr),
        fun r hr => (by rw [hrefs] at hr; cases hr),
        fun r hr => (by rw [hrefs] at hr; cases hr)⟩
      watches := hwat, cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hte] at hi hj; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
          dsimp only [nvOneLitState] <;> decide
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by
            rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h)⟩
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by
            rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h)⟩
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact Nat.le_refl 0
      dec_earliest := fun _ j _ hj _ hpos => by
        rw [hte] at hj; obtain rfl : j = 0 := (by omega); exact absurd hpos.1 (by decide)
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact hent0
      trail_pos_inv := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      level0_rsn_none := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      frame_trail_lt := fun L hL => by rw [hcl] at hL; obtain rfl : L = 0 := (by omega); decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega); obtain rfl : L2 = 0 := (by omega)
        exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne }
  refine ⟨nvOneLit_lengths, hw, ⟨fun v hv => ?_, fun l hl => ?_⟩, fun r hr => ?_,
    ⟨FullLastLearnedWf.of_cleared fun i hi => by
      dsimp only [nvOneLitState, nvOneLitScratch]
      simp only [List.getElem?_replicate, show i < 16 by omega, ↓reduceIte,
        Option.getD_some], Nat.le_refl 0⟩, rfl⟩
  · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
  · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  · change r ∈ ([] : List Nat) at hr; cases hr

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `m6_hdr_sync_legacy_tiers` under
`m7ParityVivTiersEnv`. -/
theorem nv_m7p_sync_legacy_tiers :
    Func.wp m7ParityVivTiersEnv m6_hdr_sync_legacy_tiers_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun () m' => ∃ ext' s', s'.core = nvOneLitState.core ∧ s'.LengthsOk nvOneLitCfg ∧
        M6HdrExtOk ext' ∧ nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullM6HdrMem nvOneLitCfg nvM6ExtWords nvOneLitState ⋆ emp) nvM6HdrMem := by
    rw [sep_emp]; exact nvM6HdrMem_ok
  exact m7ParityVivTiers_tableImpl.1.2 _ _ _ _
    (m6HdrW2aSpec_of rfl nvM6HdrCfg_ok nvM6ExtWords_ok nvOneLit_lengths hm
      fun () ext' s' m' hcore hlen _ hext _ hm' => by
        rw [sep_emp] at hm'
        exact ⟨ext', s', hcore, hlen, hext, nvM7p_F0_unsat, hm'⟩)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_propagate_ignore_hot` on live
binary watch conflict `FastCore.nvFastPropMem` under `m7ParityVivTiersEnv`. -/
theorem nv_m7p_propagate_ignore_hot :
    Func.wp m7ParityVivTiersEnv full_propagate_ignore_hot_body
      (FastCore.nvFastPropCfg.hdr, 0xFFFFFFFF#64, ()) FastCore.nvFastPropMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) ∧ (r = 1#64 → Full.nvOneLitF0.Unsat) ∧
        ∃ s', FullMem FastCore.nvFastPropCfg s' m')
      (fun _ _ _ _ => False) := by
  refine m7ParityVivTiers_tableImpl.2.1.2 _ _ _ _
    ⟨FastCore.nvFastPropCfg, Full.nvOneLitF0, [[0], [1]], FastCore.nvFastPropState, emp, rfl,
      FastCore.nvFastProp_lengths, FastCore.nvFastProp_witness, rfl,
      by rw [sep_emp]; exact FastCore.nvFastPropMem_ok, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' _s' _ _ _ _ _ hr _ hr1 _ _ hm'
  rw [sep_emp] at hm'
  exact ⟨hr, fun h1 => (hr1 h1).2.2.2.2 rfl, _, hm'⟩

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_vivify_tier_m6_hdr` under
`m7ParityVivTiersEnv`. -/
theorem nv_m7p_vivify_tier :
    Func.wp m7ParityVivTiersEnv full_vivify_tier_m6_hdr_body
      (nvOneLitCfg.hdr, 0#64, 1#64, 100#64, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s', FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 ∧
        (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact m7ParityVivTiers_tableImpl.2.2.1.2 _ _ _ _
    (m6aVivifyTierSpec_of nvM7p_sparseW.toSparse hm
      fun r s' m' hsp' _ _ hnz _ hr hu hm' => by
        rw [sep_emp] at hm'
        obtain ⟨hcl, hpr⟩ := hnz (by decide)
        exact ⟨s', hsp', hcl, hpr, hr, hu, hm'⟩)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_vivify_m6_hdr` under
`m7ParityVivTiersEnv`. -/
theorem nv_m7p_vivify :
    Func.wp m7ParityVivTiersEnv full_vivify_m6_hdr_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s', M6HdrExtOk ext' ∧ FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 ∧
        (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullM6HdrMem nvOneLitCfg nvM6ExtWords nvOneLitState ⋆ emp) nvM6HdrMem := by
    rw [sep_emp]; exact nvM6HdrMem_ok
  exact m7ParityVivTiers_tableImpl.2.2.2.1.2 _ _ _ _
    (m6aVivifySpec_of nvM6HdrCfg_ok nvM6ExtWords_ok nvM7p_sparseW.toSparse hm
      fun r ext' s' m' ⟨hext', _⟩ hsp' ⟨hcl', hpr'⟩ _ hr hu hm' => by
        rw [sep_emp] at hm'
        exact ⟨ext', s', hext', hsp', hcl', hpr', hr, hu, hm'⟩)

end ConcreteNonVacuity

end LeanQbe.T.Examples.Kissat.FullM7ParityVivTiers
