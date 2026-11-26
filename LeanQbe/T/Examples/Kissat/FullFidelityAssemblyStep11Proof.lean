/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep11
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
public import LeanQbe.T.Examples.Kissat.FullFidelityStep11
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.PatchModule
import LeanQbe.T.Examples.Kissat.FullFidelityStep11ProofAnalyze
import LeanQbe.T.Examples.Kissat.FullFidelityStep11ProofFailed
import LeanQbe.T.Examples.Kissat.FullFidelityStep11ProofMin
import LeanQbe.T.Examples.Kissat.FullFidelityStep11ProofMode
import LeanQbe.T.Examples.Kissat.FullFidelityStep11ProofRsn
import LeanQbe.T.Examples.Kissat.FullFidelityStep11ProofViv
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical Gate-1 `KissatFidelity` Assembly Proof — Step 11 (`FullFidelityAssemblyStep11Proof`)

Certifies `FullFidelityAssemblyStep11.fidStep11Module` (`505` fns, `0` externs, `0` exits,
`0` `import all`, `0` `@[expose]` on theorems/lemmas) via `PatchModule` +
`FullFidelityAssemblyUtil`:
1. `fidStep11Bundle : PatchBundle` layering `fidStep11Pr1Repls` (`8` sig-preserving repls covering
   `S11-1`, `S11-2`, `S11-4`) together with empty PR 2 / PR 3 plug-in slots onto `fidStep10Module`
   (`505 -> 505` fns).
2. Closed `505/505` `fidStep11_moduleOk : ModuleOk fidStep11Env fidStep11Module`,
   `fidStep11Env_noExit`, `fidStep11_solve_bytes_sound`, `fidStep11_solve_bytes_host_sound`,
   `fidStep11_unsat_nv` (`XPost := False`, `r = 20#64`, `std3`), `fidStep11Module_acyclic`, and
   `fidStep11UnsatPkg : KissatUnsatPkg`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep11

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.KissatCertCommon
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
open LeanQbe.T.Examples.Kissat.FullFidelityStep11
open LeanQbe.T.Examples.Kissat.PatchModule
open Kraken.Bedrock2.Test

/-! ## 1. `PatchBundle`, `length`, `namesNodup`, & Slot Plan (`505/505`) -/

/-- The `8` sig-preserving replacement specification rows for PR 1 (`fidStep11Pr1Repls`). -/
def fidStep11Pr1Rows : List SpecEntry :=
  [ ⟨"full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool], m6AnalyzeRsnHdrSpec, true⟩
  , ⟨"full_ana_failed_lit_m6_hdr", [i64], [i64], m6aAnaFailedLitSpecP M6ExtW2bPres, true⟩
  , ⟨"full_min_shrink_m6", [i64], [], FullM8CoreParity.m8MinShrinkSpec, true⟩
  , ⟨"full_analyze", [i64], [i64], Full.fullAnalyzeSpec, true⟩
  , ⟨"full_analyze_core_m6", [i64], [i64], m6HdrAnalyzeSpec, true⟩
  , ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], m6aVivifyTierSpec, true⟩
  , ⟨"full_switch_mode_m7", [i64], [], FullM7Search.m7SwitchModeSpec, true⟩
  , ⟨"full_preprocess_m6", [i64], [i64], fullM6PreprocessSpec, true⟩ ]

/-- PR 2 (`S11-3` + `S11-5` tumble) plug-in replacement spec rows (empty in PR 1). -/
def fidStep11TumRows : List SpecEntry :=
  []

/-- PR 3 (`S11-6a` + `S11-7` + `S11-8`) plug-in replacement spec rows (empty in PR 1). -/
def fidStep11Pr3Rows : List SpecEntry :=
  []

/-- Combined Step-11 replacement specification rows (`PR1 ++ PR2 ++ PR3`). -/
def fidStep11ReplRows : List SpecEntry :=
  fidStep11Pr1Rows ++ fidStep11TumRows ++ fidStep11Pr3Rows

/-- PR 2 (`S11-3` + `S11-5` tumble) plug-in `before` helper rows (empty in PR 1). -/
def fidStep11TumBeforeRows : List SpecEntry :=
  []

/-- PR 3 (`S11-6a` + `S11-7` + `S11-8`) plug-in `before` helper rows (empty in PR 1). -/
def fidStep11Pr3BeforeRows : List SpecEntry :=
  []

/-- Combined Step-11 `before` helper specification rows (`PR2 ++ PR3`). -/
def fidStep11BeforeRows : List SpecEntry :=
  fidStep11TumBeforeRows ++ fidStep11Pr3BeforeRows

/-- Step-11 `PatchBundle` composing `fidStep10Module` + `FullFidelityAssemblyStep11` (`505` fns). -/
def fidStep11Bundle : PatchBundle where
  baseMod := fidStep10Module
  baseTable := fidStep10BaseSpecTable
  baseOk := fidStep10Base_moduleOk
  repls := fidStep11AllRepls
  replRows := fidStep11ReplRows
  befores := fidStep11AllBefores
  beforeRows := fidStep11BeforeRows

/-- Closed `Env` for `fidStep11Module` (`505` fns). -/
def fidStep11Env : Env :=
  patchEnv fidStep11Bundle

theorem fidStep11_externs_empty : fidStep11Module.externs = [] :=
  fidStep10_externs_empty

private theorem fidStep11AllRepls_eq : fidStep11AllRepls = fidStep11Pr1Repls :=
  rfl

private theorem fidStep11AllBefores_eq : fidStep11AllBefores = [] :=
  rfl

private theorem fidStep11Fns_eq_splice :
    fidStep11Fns = spliceFns fidStep11AllRepls fidStep10Fns := by
  rw [fidStep11Fns, fidStep11AllBefores_eq, patchFns_nil]

theorem fidStep11Fns_length : fidStep11Fns.length = 505 := by
  rw [fidStep11Fns_eq_splice, PatchModule.spliceFns, List.length_map]
  exact fidStep10Fns_length

private theorem spliceFns_map_name_11 (repls fs : List Fn) :
    (spliceFns repls fs).map Fn.name = fs.map Fn.name := by
  rw [PatchModule.spliceFns, List.map_map]
  refine List.map_congr_left fun f _ => ?_
  dsimp only [Function.comp_def]
  cases h : repls.find? (·.name == f.name) with
  | none => rfl
  | some r => exact beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == f.name) h)

theorem fidStep11Module_names_nodup : fidStep11Module.namesNodup := by
  change (fidStep11Module.fns.map Fn.name ++ fidStep11Module.externs.map Extern.name).Nodup
  rw [fidStep11Fns_eq, fidStep11Fns_eq_splice, spliceFns_map_name_11]
  exact fidStep10Module_names_nodup

theorem fidStep11Module_map_name :
    fidStep11Module.fns.map Fn.name = fidStep10FnNames := by
  rw [fidStep11Fns_eq, fidStep11Fns_eq_splice, spliceFns_map_name_11, ← fidStep10Fns_eq,
    fidStep10Module_map_name]

private def fidStep11FrontNames : List Sym :=
  [ "full_analyze_rsn_m6_hdr", "full_ana_failed_lit_m6_hdr", "full_min_shrink_m6"
  , "full_analyze", "full_analyze_core_m6", "full_vivify_tier_m6_hdr"
  , "full_switch_mode_m7", "full_preprocess_m6" ]

private theorem fidStep11_frontNames_eq :
    fidStep11Bundle.frontTable.map SpecEntry.name = fidStep11FrontNames :=
  rfl

private theorem fidStep11_front_nodup :
    (fidStep11Bundle.frontTable.map SpecEntry.name).Nodup := by
  rw [fidStep11_frontNames_eq]
  decide

private theorem slot10_mem_of_at {j : Nat} {s : SigEntry}
    (hs : fidStep10Module.fns[j]?.map Fn.sig = some s) :
    ∃ g ∈ fidStep10Module.fns, fidStep10Module.fns[j]? = some g ∧ g.sig = s := by
  cases h : fidStep10Module.fns[j]? with
  | none => simp [h] at hs
  | some g =>
    simp only [h, Option.map_some, Option.some.injEq] at hs
    exact ⟨g, List.mem_of_getElem? h, rfl, hs⟩

theorem fidStep11Module_replSigs_ok :
    ∀ r ∈ fidStep11AllRepls, ∀ g ∈ fidStep10Module.fns,
      r.name = g.name → r.sig = g.sig := by
  have hnd := module_fns_namesNodup fidStep10Module_names_nodup
  intro r hr g hg hnm
  rw [fidStep11AllRepls_eq] at hr
  have hslot : ∀ {j : Nat} {s : SigEntry}, fidStep10Module.fns[j]?.map Fn.sig = some s →
      r.sig = s → r.sig = g.sig := by
    intro j s hs hrs
    obtain ⟨g0, hg0, _, hsg⟩ := slot10_mem_of_at hs
    have hgnm : r.name = g0.name := congrArg Prod.fst (hrs.trans hsg.symm)
    rw [nodup_name_eq Fn.name hnd hg hg0 (hnm.symm.trans hgnm), hsg, hrs]
  simp only [fidStep11Pr1Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hslot (fidStep10_step11_sig_at (p := (118, _)) (by decide)) rfl
  · exact hslot (fidStep10_step11_sig_at (p := (124, _)) (by decide)) rfl
  · exact hslot (fidStep10_step11_sig_at (p := (142, _)) (by decide)) rfl
  · exact hslot (fidStep10_step11_sig_at (p := (156, _)) (by decide)) rfl
  · exact hslot (fidStep10_step11_sig_at (p := (158, _)) (by decide)) rfl
  · exact hslot (fidStep10_step11_sig_at (p := (229, _)) (by decide)) rfl
  · exact hslot (fidStep10_step11_sig_at (p := (493, _)) (by decide)) rfl
  · exact hslot (fidStep10_step11_sig_at (p := (497, _)) (by decide)) rfl

/-! ## 2. Per-Function `checkCallsOk`, `sameSpecs`, & Split Infrastructure -/

private theorem analyzeRsnM6Hdr11_callsOk :
    fidStep11AnalyzeRsnM6HdrFn.checkCallsOk
      [ ("full_analyze_lit", [i64, i32, i32], [.bool])
      , ("m6_hdr_record_used", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

private theorem anaFailedLitM6Hdr11_callsOk :
    fidStep11AnaFailedLitM6HdrFn.checkCallsOk
      [ ("full_clear_ana", [i64], [])
      , ("full_bump_analyzed_m6_hdr", [i64], [])
      , ("full_backtrack", [i64, i64], [])
      , ("full_assign_lvl", [i64, i32, i32, i32], [])
      , ("full_ema_update", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

private theorem minShrinkM6_11_callsOk :
    fidStep11MinShrinkM6Fn.checkCallsOk
      [ ("full_sort_tmp", [i64], [])
      , ("full_min_mark", [i64, i32, i8], [])
      , ("full_min_lit_dfs_m8", [i64, i32, .bool, .bool], [.bool])
      , ("full_shrink_blk_bool_m8", [i64, i64, i64, i32, i64], [.bool]) ] [] = true := by
  t_kernel_rfl

private theorem analyze11_callsOk :
    fidStep11AnalyzeFn.checkCallsOk
      [ ("full_one_lit_confl", [i64], [i64])
      , ("full_deduce_1uip", [i64], [i64])
      , ("full_restore_bump_ana_m5", [i64], [])
      , ("full_min_shrink", [i64], [])
      , ("full_tick_rel", [i64], [])
      , ("full_ema_update", [i64, i64], [])
      , ("full_learn_clause", [i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

private theorem analyzeCoreM6_11_callsOk :
    fidStep11AnalyzeCoreM6Fn.checkCallsOk
      [ ("full_one_lit_confl", [i64], [i64])
      , ("full_ana_failed_lit_m6_hdr", [i64], [i64])
      , ("full_deduce_1uip_m6_hdr", [i64], [i64])
      , ("full_restore_bump_ana_m6_hdr", [i64], [])
      , ("full_min_shrink_m6", [i64], [])
      , ("full_tick_rel", [i64], [])
      , ("full_ema_update", [i64, i64], [])
      , ("full_learn_clause_m6", [i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

private theorem vivifyTierM6Hdr11_callsOk :
    fidStep11VivifyTierM6HdrFn.checkCallsOk
      [ ("full_backtrack", [i64, i64], [])
      , ("full_viv_collect_fid", [i64, i64], [i64])
      , ("full_viv_count_fid", [i64, i64], [])
      , ("full_viv_sort_fid", [i64, i64], [])
      , ("full_viv_clause_m6", [i64, i32], [i64])
      , ("full_propagate", [i64], [i64])
      , ("full_viv_clear_tier_m6", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

private theorem switchModeM7_11_callsOk :
    fidStep11SwitchModeM7Fn.checkCallsOk
      [ ("full_ilog10", [i64], [i64])
      , ("full_heap_down", [i64, i32], [])
      , ("full_ema_swap_m7", [i64, i64, i64], [])
      , ("full_log10_q16_m7", [i64], [i64])
      , ("full_m7_get64", [i64, i64], [i64])
      , ("full_m7_set64", [i64, i64, i64], []) ] [] = true := by
  t_kernel_rfl

private theorem preprocessM6_11_callsOk :
    fidStep11PreprocessM6Fn.checkCallsOk
      [ ("full_propagate", [i64], [i64])
      , ("full_arena_sweep", [i64], [i64])
      , ("full_lucky", [i64], [i64])
      , ("full_compact_needed", [i64], [.bool])
      , ("full_compact", [i64], [i64])
      , ("full_scale_delta_m5", [i64, i64], [i64])
      , ("full_probe_m6", [i64, .bool], [i64]) ] [] = true := by
  t_kernel_rfl

private theorem fid11_of_step10 {f : Sym} {as bs : List Ty}
    (hf11 : !(fidStep11FrontNames.contains f) = true := by decide)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidStep10Env f as bs xs m Q X) :
    fidStep11Env f as bs xs m Q X := by
  change patchEnv fidStep11Bundle f as bs xs m Q X
  have hfnone : fidStep11Bundle.frontTable.find? (·.name == f) = none := by
    rw [List.find?_eq_none]
    intro e he hbeq
    have hm : f ∈ fidStep11FrontNames :=
      fidStep11_frontNames_eq ▸ (beq_iff_eq.mp hbeq ▸ List.mem_map_of_mem he)
    simp [hm] at hf11
  rw [patchEnv_base_eq fidStep11Bundle hfnone]
  dsimp only [fidStep11Bundle]
  rwa [fidStep10Base_eq_env]

private theorem fid11_frontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidStep11Bundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ a m Q X, sp a m Q X → fidStep11Env nm as bs a m Q X := fun a m Q X hs =>
  patchEnv_of_front_mem fidStep11Bundle fidStep11_front_nodup (List.mem_of_getElem? hi)
    (hno a m Q X hs)

private theorem fidStep11_sameSpecs :
    ∀ e ∈ fidStep11Bundle.frontTable, ∀ xs m P E,
      Env.ofTable fidStep11Bundle.baseTable e.name e.as e.rs xs m P E → e.eff xs m P E := by
  intro e he xs m P E hBase
  dsimp only [fidStep11Bundle] at hBase
  rw [fidStep10Base_eq_env] at hBase
  simp only [fidStep11Bundle, PatchBundle.frontTable, fidStep11ReplRows, fidStep11Pr1Rows,
    fidStep11TumRows, fidStep11Pr3Rows, fidStep11BeforeRows, fidStep11TumBeforeRows,
    fidStep11Pr3BeforeRows, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6AnalyzeRsnHdrSpec_monoX (fidStep10Env_elim_analyzeRsnM6Hdr hBase)
  · exact m6aAnaFailedLitSpecP_monoXP (fidStep10Env_elim_anaFailedLitM6Hdr hBase)
  · exact FullM8CoreParity.m8MinShrinkSpec_monoX (fidStep10Env_elim_minShrinkM6 hBase)
  · rcases xs with ⟨_, ⟨⟩⟩
    exact fidStep10Env_elim_analyze hBase
  · exact m6HdrAnalyzeSpec_monoX (fidStep10Env_elim_analyzeCoreM6 hBase)
  · exact m6aVivifyTierSpec_monoX (fidStep10Env_elim_vivifyTierM6Hdr hBase)
  · exact FullM7Search.m7SwitchModeSpec_monoX (fidStep10Env_elim_switchModeM7 hBase)
  · exact fullM6PreprocessSpec_monoX (fidStep10Env_elim_preprocessM6 hBase)

private theorem fidStep11_agree :
    ∀ s ∈ fidStep10Module.sigs,
      ∀ xs m P E, Env.ofTable fidStep10BaseSpecTable s.1 s.2.1 s.2.2 xs m P E →
        fidStep11Env s.1 s.2.1 s.2.2 xs m P E :=
  patchEnv_agree_of_sameSpecs fidStep11Bundle fidStep11_front_nodup fidStep11_sameSpecs

private theorem spliceFns_split_mem_11 {repls fs pre post : List Fn} {fn : Fn}
    (hreplSigs : ∀ r ∈ repls, ∀ g ∈ fs, r.name = g.name → r.sig = g.sig)
    (hsplit : spliceFns repls fs = pre ++ fn :: post) :
    ∃ bPre f0 bPost,
      fs = bPre ++ f0 :: bPost ∧
      fn = (repls.find? (·.name == f0.name)).getD f0 ∧
      pre.map Fn.sig = bPre.map Fn.sig := by
  induction fs generalizing pre with
  | nil => simp [spliceFns] at hsplit
  | cons f fs ih =>
    simp only [spliceFns, List.map_cons] at hsplit
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hsplit
      obtain ⟨rfl, _⟩ := hsplit
      exact ⟨[], f, fs, rfl, rfl, rfl⟩
    | cons p pre' =>
      simp only [List.cons_append, List.cons.injEq] at hsplit
      obtain ⟨rfl, htail⟩ := hsplit
      obtain ⟨bPre', f0, bPost, hfs', hfn', hsig⟩ :=
        ih (fun r hr g hg => hreplSigs r hr g (by simp [hg])) htail
      refine ⟨f :: bPre', f0, bPost, by rw [hfs', List.cons_append], hfn', ?_⟩
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨?_, hsig⟩
      cases hf : repls.find? (·.name == f.name) with
      | none => rfl
      | some rf =>
        have hnm : rf.name = f.name :=
          beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == f.name) hf)
        exact hreplSigs rf (List.mem_of_find?_eq_some hf) f List.mem_cons_self hnm

private theorem fidStep11_front_none_of_repl_none {nm : Sym}
    (h : fidStep11AllRepls.find? (·.name == nm) = none) :
    fidStep11Bundle.frontTable.find? (·.name == nm) = none := by
  rw [List.find?_eq_none]
  intro e he hbeq
  have hnm : e.name = nm := beq_iff_eq.mp hbeq
  have hmem : e.name ∈ fidStep11AllRepls.map Fn.name := by
    have hm : e.name ∈ fidStep11FrontNames := fidStep11_frontNames_eq ▸ List.mem_map_of_mem he
    rw [fidStep11AllRepls_eq]
    exact hm
  obtain ⟨r, hr, hrn⟩ := List.mem_map.mp hmem
  have hnone := List.find?_eq_none.mp h r hr
  simp [hnm, hrn] at hnone

private theorem nodup_getElem?_inj_11 {α : Type _} {xs : List α} (hnd : xs.Nodup)
    {i j : Nat} {a : α} (hi : xs[i]? = some a) (hj : xs[j]? = some a) : i = j := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons x xs ih =>
    have ⟨hnmem, hnd'⟩ := List.nodup_cons.mp hnd
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp at hi hj; subst hi
        exact False.elim (hnmem (List.mem_iff_getElem?.mpr ⟨j, hj⟩))
    | succ i =>
      cases j with
      | zero =>
        simp at hi hj; subst hj
        exact False.elim (hnmem (List.mem_iff_getElem?.mpr ⟨i, hi⟩))
      | succ j =>
        simp at hi hj
        exact congrArg Nat.succ (ih hnd' hi hj)

private theorem fidStep11_callsOk_at {fn : Fn} {deps : List SigEntry}
    {bPre bPost pre : List Fn} {f0 : Fn} {slot : Nat} {s0 : SigEntry}
    (hnd : (fidStep10Module.fns.map Fn.name).Nodup)
    (hfs : fidStep10Module.fns = bPre ++ f0 :: bPost)
    (hs0 : fidStep10Module.fns[slot]?.map Fn.sig = some s0)
    (hfnm : f0.name = s0.1)
    (hpreSig : pre.map Fn.sig = bPre.map Fn.sig)
    (hchk : fn.checkCallsOk deps [] = true)
    (hdeps : ∀ d ∈ deps, ∃ k, k < slot ∧ fidStep10Module.fns[k]?.map Fn.sig = some d) :
    fn.callsOk (pre.map Fn.sig ++ fidStep11Module.externs.map Extern.sig)
      fidStep11Module.exits := by
  rw [fidStep11_noExit, fidStep11_externs_empty, List.map_nil, List.append_nil, hpreSig]
  refine fn_callsOk_mono (fun d hd => ?_) (Fn.callsOk_of_checkCallsOk hchk)
  obtain ⟨k, hlt, hk⟩ := hdeps d hd
  have hlen : bPre.length = slot := by
    cases hg0 : fidStep10Module.fns[slot]? with
    | none => simp [hg0] at hs0
    | some g0 =>
      simp only [hg0, Option.map_some, Option.some.injEq] at hs0
      have hi1 : (fidStep10Module.fns.map Fn.name)[bPre.length]? = some s0.1 := by
        rw [hfs]; simp [hfnm]
      have hi2 : (fidStep10Module.fns.map Fn.name)[slot]? = some s0.1 := by
        simp [List.getElem?_map, hg0, ← hs0, Fn.sig]
      exact nodup_getElem?_inj_11 hnd hi1 hi2
  cases hg : fidStep10Module.fns[k]? with
  | none => simp [hg] at hk
  | some g =>
    simp only [hg, Option.map_some, Option.some.injEq] at hk
    have hgb : bPre[k]? = some g := by
      rwa [hfs, List.getElem?_append_left (hlen ▸ hlt)] at hg
    exact hk ▸ List.mem_map_of_mem (List.mem_of_getElem? hgb)

/-! ## 3. Closed `505/505` `fidStep11_moduleOk`, UNSAT Soundness, `Mem 64` NV & `KissatUnsatPkg` -/

/-- Closed `505/505` `ModuleOk` for `FullFidelityAssemblyStep11.fidStep11Module` under
`fidStep11Env` (`0` externs, `0` exits, `std3` axioms only). -/
theorem fidStep11_moduleOk : ModuleOk fidStep11Env fidStep11Module := by
  refine ⟨fidStep11Module_names_nodup, fun pre fn post hsplit => ?_⟩
  have hsplit' : spliceFns fidStep11AllRepls fidStep10Module.fns = pre ++ fn :: post := by
    change patchFns fidStep11AllRepls fidStep11AllBefores fidStep10Module.fns = pre ++ fn :: post
      at hsplit
    rwa [fidStep11AllBefores_eq, patchFns_nil] at hsplit
  obtain ⟨bPre, f0, bPost, hfs, hfn_eq, hpreSig⟩ :=
    spliceFns_split_mem_11 fidStep11Module_replSigs_ok hsplit'
  have hf0_ok := fidStep10Base_moduleOk.fnsOk bPre f0 bPost hfs
  have hnd10 := module_fns_namesNodup fidStep10Module_names_nodup
  cases hrepl : fidStep11AllRepls.find? (·.name == f0.name) with
  | none =>
    simp only [hrepl, Option.getD_none] at hfn_eq
    subst hfn_eq
    have hfrontNone := fidStep11_front_none_of_repl_none hrepl
    have hcalls10 : fn.callsOk (bPre.map Fn.sig) [] := by
      simpa only [fidStep10_noExit, fidStep10_externs_empty, List.map_nil, List.append_nil] using
        hf0_ok.2.1
    refine ⟨hf0_ok.1, ?_, fun xs m Q X hlookup => ?_⟩
    · simpa only [fidStep11_noExit, fidStep11_externs_empty, List.map_nil, List.append_nil,
        hpreSig] using hcalls10
    · change fidStep11Env fn.name fn.as fn.rs xs m Q X at hlookup
      dsimp only [fidStep11Env] at hlookup
      rw [patchEnv_base_eq fidStep11Bundle hfrontNone] at hlookup
      dsimp only [fidStep11Bundle] at hlookup
      have hwp_base := hf0_ok.2.2 xs m Q X hlookup
      refine wp_env_agree_of_callsOk (hf0_ok.1 _ _ _ _ _ _) hf0_ok.2.1 (fun f as bs hs => ?_)
        m hwp_base
      apply fidStep11_agree (f, as, bs)
      simp only [Module.sigs, List.mem_append, List.mem_map] at hs ⊢
      rcases hs with ⟨g, hg, hgsig⟩ | ⟨ex, hex, hexsig⟩
      · exact Or.inl ⟨g, hfs ▸ List.mem_append_left _ hg, hgsig⟩
      · exact Or.inr ⟨ex, hex, hexsig⟩
  | some r =>
    have hr_mem : r ∈ fidStep11AllRepls := List.mem_of_find?_eq_some hrepl
    have hf0_nm : f0.name = r.name :=
      (beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == f0.name) hrepl)).symm
    simp only [hrepl, Option.getD_some] at hfn_eq
    subst hfn_eq
    rw [fidStep11AllRepls_eq] at hr_mem
    refine ⟨fidStep11Pr1Repls_wf fn hr_mem, ?_, ?_⟩
    · simp only [fidStep11Pr1Repls, List.mem_cons, List.not_mem_nil, or_false] at hr_mem
      rcases hr_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · refine fidStep11_callsOk_at hnd10 hfs
          (fidStep10_step11_sig_at
            (p := (118, ("full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool]))) (by decide))
          hf0_nm hpreSig analyzeRsnM6Hdr11_callsOk fun d hd => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · exact ⟨116, by decide, fidStep10_step11_sig_at (p := (116, _)) (by decide)⟩
        · exact ⟨65, by decide, fidStep10_step11_sig_at (p := (65, _)) (by decide)⟩
      · refine fidStep11_callsOk_at hnd10 hfs
          (fidStep10_step11_sig_at (p := (124, ("full_ana_failed_lit_m6_hdr", [i64], [i64])))
            (by decide))
          hf0_nm hpreSig anaFailedLitM6Hdr11_callsOk fun d hd => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl
        · exact ⟨119, by decide, fidStep10_step11_sig_at (p := (119, _)) (by decide)⟩
        · exact ⟨122, by decide, fidStep10_step11_sig_at (p := (122, _)) (by decide)⟩
        · exact ⟨40, by decide, fidStep10_step11_sig_at (p := (40, _)) (by decide)⟩
        · exact ⟨36, by decide, fidStep10_step11_sig_at (p := (36, _)) (by decide)⟩
        · exact ⟨34, by decide, fidStep10_step11_sig_at (p := (34, _)) (by decide)⟩
      · refine fidStep11_callsOk_at hnd10 hfs
          (fidStep10_step11_sig_at (p := (142, ("full_min_shrink_m6", [i64], []))) (by decide))
          hf0_nm hpreSig minShrinkM6_11_callsOk fun d hd => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl
        · exact ⟨133, by decide, fidStep10_step11_sig_at (p := (133, _)) (by decide)⟩
        · exact ⟨128, by decide, fidStep10_step11_sig_at (p := (128, _)) (by decide)⟩
        · exact ⟨139, by decide, fidStep10_step11_sig_at (p := (139, _)) (by decide)⟩
        · exact ⟨141, by decide, fidStep10_step11_sig_at (p := (141, _)) (by decide)⟩
      · refine fidStep11_callsOk_at hnd10 hfs
          (fidStep10_step11_sig_at (p := (156, ("full_analyze", [i64], [i64]))) (by decide))
          hf0_nm hpreSig analyze11_callsOk fun d hd => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨148, by decide, fidStep10_step11_sig_at (p := (148, _)) (by decide)⟩
        · exact ⟨145, by decide, fidStep10_step11_sig_at (p := (145, _)) (by decide)⟩
        · exact ⟨155, by decide, fidStep10_step11_sig_at (p := (155, _)) (by decide)⟩
        · exact ⟨144, by decide, fidStep10_step11_sig_at (p := (144, _)) (by decide)⟩
        · exact ⟨30, by decide, fidStep10_step11_sig_at (p := (30, _)) (by decide)⟩
        · exact ⟨34, by decide, fidStep10_step11_sig_at (p := (34, _)) (by decide)⟩
        · exact ⟨150, by decide, fidStep10_step11_sig_at (p := (150, _)) (by decide)⟩
      · refine fidStep11_callsOk_at hnd10 hfs
          (fidStep10_step11_sig_at (p := (158, ("full_analyze_core_m6", [i64], [i64]))) (by decide))
          hf0_nm hpreSig analyzeCoreM6_11_callsOk fun d hd => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨148, by decide, fidStep10_step11_sig_at (p := (148, _)) (by decide)⟩
        · exact ⟨124, by decide, fidStep10_step11_sig_at (p := (124, _)) (by decide)⟩
        · exact ⟨146, by decide, fidStep10_step11_sig_at (p := (146, _)) (by decide)⟩
        · exact ⟨123, by decide, fidStep10_step11_sig_at (p := (123, _)) (by decide)⟩
        · exact ⟨142, by decide, fidStep10_step11_sig_at (p := (142, _)) (by decide)⟩
        · exact ⟨30, by decide, fidStep10_step11_sig_at (p := (30, _)) (by decide)⟩
        · exact ⟨34, by decide, fidStep10_step11_sig_at (p := (34, _)) (by decide)⟩
        · exact ⟨157, by decide, fidStep10_step11_sig_at (p := (157, _)) (by decide)⟩
      · refine fidStep11_callsOk_at hnd10 hfs
          (fidStep10_step11_sig_at (p := (229, ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64],
            [i64]))) (by decide))
          hf0_nm hpreSig vivifyTierM6Hdr11_callsOk fun d hd => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨40, by decide, fidStep10_step11_sig_at (p := (40, _)) (by decide)⟩
        · exact ⟨225, by decide, fidStep10_step11_sig_at (p := (225, _)) (by decide)⟩
        · exact ⟨226, by decide, fidStep10_step11_sig_at (p := (226, _)) (by decide)⟩
        · exact ⟨228, by decide, fidStep10_step11_sig_at (p := (228, _)) (by decide)⟩
        · exact ⟨217, by decide, fidStep10_step11_sig_at (p := (217, _)) (by decide)⟩
        · exact ⟨90, by decide, fidStep10_step11_sig_at (p := (90, _)) (by decide)⟩
        · exact ⟨223, by decide, fidStep10_step11_sig_at (p := (223, _)) (by decide)⟩
      · refine fidStep11_callsOk_at hnd10 hfs
          (fidStep10_step11_sig_at (p := (493, ("full_switch_mode_m7", [i64], []))) (by decide))
          hf0_nm hpreSig switchModeM7_11_callsOk fun d hd => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨9, by decide, fidStep10_step11_sig_at (p := (9, _)) (by decide)⟩
        · exact ⟨21, by decide, fidStep10_step11_sig_at (p := (21, _)) (by decide)⟩
        · exact ⟨492, by decide, fidStep10_step11_sig_at (p := (492, _)) (by decide)⟩
        · exact ⟨32, by decide, fidStep10_step11_sig_at (p := (32, _)) (by decide)⟩
        · exact ⟨481, by decide, fidStep10_step11_sig_at (p := (481, _)) (by decide)⟩
        · exact ⟨482, by decide, fidStep10_step11_sig_at (p := (482, _)) (by decide)⟩
      · refine fidStep11_callsOk_at hnd10 hfs
          (fidStep10_step11_sig_at (p := (497, ("full_preprocess_m6", [i64], [i64]))) (by decide))
          hf0_nm hpreSig preprocessM6_11_callsOk fun d hd => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨90, by decide, fidStep10_step11_sig_at (p := (90, _)) (by decide)⟩
        · exact ⟨108, by decide, fidStep10_step11_sig_at (p := (108, _)) (by decide)⟩
        · exact ⟨192, by decide, fidStep10_step11_sig_at (p := (192, _)) (by decide)⟩
        · exact ⟨446, by decide, fidStep10_step11_sig_at (p := (446, _)) (by decide)⟩
        · exact ⟨458, by decide, fidStep10_step11_sig_at (p := (458, _)) (by decide)⟩
        · exact ⟨33, by decide, fidStep10_step11_sig_at (p := (33, _)) (by decide)⟩
        · exact ⟨496, by decide, fidStep10_step11_sig_at (p := (496, _)) (by decide)⟩
    · simp only [fidStep11Pr1Repls, List.mem_cons, List.not_mem_nil, or_false] at hr_mem
      rcases hr_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · intro xs m Q X hlk
        have hfind : fidStep11Bundle.frontTable.find?
            (·.name == fidStep11AnalyzeRsnM6HdrFn.name) = some fidStep11Pr1Rows[0] := rfl
        exact (SpecEntry.Impl.of (full_analyze_rsn_m6_hdr_step11_wp fidStep11Env
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_analyzeLit _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide)
            (fidStep10Env_hdrRecordUsed _ _ _ _ hs)))).2
          xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
      · intro xs m Q X hlk
        have hfind : fidStep11Bundle.frontTable.find?
            (·.name == fidStep11AnaFailedLitM6HdrFn.name) = some fidStep11Pr1Rows[1] := rfl
        exact (SpecEntry.Impl.of (full_ana_failed_lit_m6_hdr_step11_wp fidStep11Env
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_clearAna _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide)
            (fidStep10Env_bumpAnalyzedM6Hdr _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_backtrack _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_assignLvl _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_emaUpdate _ _ _ _ hs)))).2
          xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
      · intro xs m Q X hlk
        have hfind : fidStep11Bundle.frontTable.find?
            (·.name == fidStep11MinShrinkM6Fn.name) = some fidStep11Pr1Rows[2] := rfl
        exact (SpecEntry.Impl.of (full_min_shrink_m6_step11_wp fidStep11Env
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_sortTmp _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_minMark _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_minLitDfsM8 _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide)
            (fidStep10Env_shrinkBlkBoolM8 _ _ _ _ hs)))).2
          xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
      · intro xs m Q X hlk
        have hfind : fidStep11Bundle.frontTable.find?
            (·.name == fidStep11AnalyzeFn.name) = some fidStep11Pr1Rows[3] := rfl
        exact (SpecEntry.Impl.of (full_analyze_step11_wp fidStep11Env
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_oneLitConfl _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_deduce1uip _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide)
            (fidStep10Env_restoreBumpAnaM5 _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_minShrink _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_tickRel _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_emaUpdate _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_learnClause _ _ _ _ hs)))).2
          xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
      · intro xs m Q X hlk
        have hfind : fidStep11Bundle.frontTable.find?
            (·.name == fidStep11AnalyzeCoreM6Fn.name) = some fidStep11Pr1Rows[4] := rfl
        exact (SpecEntry.Impl.of (full_analyze_core_m6_step11_wp fidStep11Env
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_oneLitConfl _ _ _ _ hs))
          (fid11_frontRow 1 "full_ana_failed_lit_m6_hdr" (m6aAnaFailedLitSpecP M6ExtW2bPres) rfl
            (fun _ _ _ _ h => m6aAnaFailedLitSpecP_monoXP h))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide)
            (fidStep10Env_deduce1uipM6Hdr _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide)
            (fidStep10Env_restoreBumpAnaM6Hdr _ _ _ _ hs))
          (fid11_frontRow 2 "full_min_shrink_m6" FullM8CoreParity.m8MinShrinkSpec rfl
            (fun _ _ _ _ h => FullM8CoreParity.m8MinShrinkSpec_monoX h))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_tickRel _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_emaUpdate _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide)
            (fidStep10Env_learnClauseM6 _ _ _ _ hs)))).2
          xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
      · intro xs m Q X hlk
        have hfind : fidStep11Bundle.frontTable.find?
            (·.name == fidStep11VivifyTierM6HdrFn.name) = some fidStep11Pr1Rows[5] := rfl
        exact (SpecEntry.Impl.of (full_vivify_tier_m6_hdr_step11_wp fidStep11Env
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_backtrack _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide)
            (fidStep10Env_vivCollectFid _ _ _ _ (fid11VivCollectSpec_of_strict hs)))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_vivCountFid _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_vivSortFid _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_vivClauseM6 _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_propagate _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide)
            (fidStep10Env_vivClearTierM6 _ _ _ _ hs)))).2
          xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
      · intro xs m Q X hlk
        have hfind : fidStep11Bundle.frontTable.find?
            (·.name == fidStep11SwitchModeM7Fn.name) = some fidStep11Pr1Rows[6] := rfl
        exact (SpecEntry.Impl.of (full_switch_mode_m7_step11_wp fidStep11Env
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_ilog10 _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_heapDown _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_emaSwapM7 _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_log10Q16M7 _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_m7Get64 _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_m7Set64 _ _ _ _ hs)))).2
          xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
      · intro xs m Q X hlk
        have hfind : fidStep11Bundle.frontTable.find?
            (·.name == fidStep11PreprocessM6Fn.name) = some fidStep11Pr1Rows[7] := rfl
        exact (SpecEntry.Impl.of (full_preprocess_m6_step11_wp fidStep11Env
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_propagate _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_arenaSweep _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_lucky _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_compactNeeded _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_compact _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_scaleDeltaM5 _ _ _ _ hs))
          (fun _ _ _ _ hs => fid11_of_step10 (by decide) (fidStep10Env_probeM6 _ _ _ _ hs)))).2
          xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)

theorem fidStep11Env_noExit :
    ∀ f as bs xs m Q X X',
      fidStep11Env f as bs xs m Q X → fidStep11Env f as bs xs m Q X' :=
  patchEnv_noExit_of fidStep11Bundle (by decide) fidStep10BaseSpecTable_noExit

theorem fidStep11Env_solve_bytes_of {a : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m7FidSolveBytesSpec a m Q X →
      fidStep11Env "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X :=
  fun hs => fid11_of_step10 (by decide) (fidStep10Env_solve_bytes_of hs)

theorem fidStep11_solveBytes_mem : m6oSolveBytesFn ∈ fidStep11Module.fns :=
  patchBundle_solveBytes_mem fidStep11Bundle fidStep10_solveBytes_mem fun r hr => by
    change r ∈ fidStep11AllRepls at hr
    rw [fidStep11AllRepls_eq] at hr
    simp only [fidStep11Pr1Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Top-level byte-level UNSAT soundness of `fidStep11Module` (`505` fns, `XPost := False`). -/
theorem fidStep11_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidStep11Env m6oSolveBytesFn.body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fid_solve_bytes_sound_of fidStep11_moduleOk fidStep11_solveBytes_mem
    (fun _ _ _ _ hs => fidStep11Env_solve_bytes_of hs) hcfit hwfit hm

/-- Host-framed machine-memory UNSAT lift for `fidStep11Module`. -/
theorem fidStep11_solve_bytes_host_sound
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hpost :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hhost : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem :=
  FullFidelityAssemblyUtil.fid_solve_bytes_host_sound hpost hhost

/-- Concrete deterministic `Mem 64` UNSAT non-vacuity (`r = 20#64`) for `fidStep11Module`. -/
theorem fidStep11_unsat_nv :
    Func.wp fidStep11Env m6oSolveBytesFn.body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fid_unsat_nv_of fidStep11_moduleOk fidStep11_solveBytes_mem
    (fun _ _ _ _ hs => fidStep11Env_solve_bytes_of hs)

/-- Acyclicity certificate (`checkAcyclic = true`) lifted in `O(1)` from `fidStep11_moduleOk`. -/
theorem fidStep11Module_acyclic : fidStep11Module.checkAcyclic = true :=
  moduleCheckAcyclic_of_moduleOk fidStep11_moduleOk

/-- Canonical Gate-1 Step-11 `KissatUnsatPkg` (`fidStep11Module`, `fidInlPolicy`). -/
def fidStep11UnsatPkg : KissatUnsatPkg :=
  mkFidUnsatPkg fidStep11Module fidInlPolicy fidStep11_solveBytes_mem
    fidStep11Env fidStep11_moduleOk fidStep11Env_noExit
    (fun _ _ _ _ hs => fidStep11Env_solve_bytes_of hs)

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep11

end
