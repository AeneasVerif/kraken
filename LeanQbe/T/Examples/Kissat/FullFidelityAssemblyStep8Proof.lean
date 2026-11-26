/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep8
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7
public import LeanQbe.T.Examples.Kissat.FullFidelityStep8
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.PatchModule
import LeanQbe.T.Examples.Kissat.FullFidelityStep8ProofWalkDel
import LeanQbe.T.Examples.Kissat.FullFidelityStep8ProofWatch1
import LeanQbe.T.Examples.Kissat.FullFidelityStep8ProofBva
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical Gate-1 `KissatFidelity` Assembly Proof — Step 8 (`FullFidelityAssemblyStep8Proof`)

Certifies `FullFidelityAssemblyStep8.fidStep8Module` (`501` fns, `0` externs, `0` exits,
`0` `import all`, `0` `@[expose]` on theorems/lemmas) via `PatchModule` +
`FullFidelityAssemblyUtil`:
1. `fidStep8Bundle : PatchBundle` layering `FullFidelityStep8.fidStep8Repls` (`5` fns) onto
   `fidStep7Module` (`501` fns -> `501` fns).
2. Closed `501/501` `fidStep8_moduleOk : ModuleOk fidStep8Env fidStep8Module`,
   `fidStep8Env_noExit`, `fidStep8_solve_bytes_sound`, `fidStep8_solve_bytes_host_sound`,
   `fidStep8_unsat_nv` (`XPost := False`, `std3`), and `fidStep8UnsatPkg : KissatUnsatPkg`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep8

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.KissatCertCommon
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
open LeanQbe.T.Examples.Kissat.PatchModule
open Kraken.Bedrock2.Test

/-! ## 1. `PatchBundle`, `length`, `namesNodup`, & Algebraic Slot Plan (`501/501`) -/

/-- The `5` unchanged `SpecEntry` rows for `FullFidelityStep8.fidStep8Repls`. -/
def fidStep8ReplRows : List SpecEntry :=
  [ ⟨"full_walk_effort_m7", [i64, i64], [i64], FullM7Walk.m7EffortSpec, true⟩
  , ⟨"full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  , ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  , ⟨"full_delete_bin_side", [i64, i32, i32], [], Full.fullDeleteBinSideSpec, true⟩
  , ⟨"full_bva_commit", [i64, i32], [.bool], FullFidelityStep7.step7BvaCommitSpec, true⟩ ]

/-- Step-8 `PatchBundle` composing `fidStep7Module` + `FullFidelityStep8`. -/
def fidStep8Bundle : PatchBundle where
  baseMod := fidStep7Module
  baseTable := fidStep7BaseSpecTable
  baseOk := fidStep7Base_moduleOk
  repls := FullFidelityStep8.fidStep8Repls
  replRows := fidStep8ReplRows

/-- Closed `Env` for `fidStep8Module` (`501` fns). -/
def fidStep8Env : Env :=
  patchEnv fidStep8Bundle

theorem fidStep8_externs_empty : fidStep8Module.externs = [] :=
  fidStep7_externs_empty

theorem fidStep8Fns_length : fidStep8Fns.length = 501 := by
  rw [fidStep8Fns, patchFns_nil, PatchModule.spliceFns, List.length_map]
  exact fidStep7Fns_length

private theorem patchFns_nil_befores_map_name (repls fs : List Fn) :
    (patchFns repls [] fs).map Fn.name = fs.map Fn.name := by
  rw [patchFns_nil, PatchModule.spliceFns, List.map_map]
  refine List.map_congr_left fun f _ => ?_
  dsimp only [Function.comp_def]
  cases h : repls.find? (·.name == f.name) with
  | none => rfl
  | some r => exact beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == f.name) h)

theorem fidStep8Module_names_nodup : fidStep8Module.namesNodup := by
  change (fidStep8Module.fns.map Fn.name ++ fidStep8Module.externs.map Extern.name).Nodup
  rw [fidStep8Fns_eq, fidStep8Fns, patchFns_nil_befores_map_name]
  exact fidStep7Module_names_nodup

theorem fidStep8Module_map_name :
    fidStep8Module.fns.map Fn.name = fidStep7FnNames := by
  rw [fidStep8Fns_eq, fidStep8Fns, patchFns_nil_befores_map_name, ← fidStep7Module_map_name]
  rfl

private def fidStep8FrontNames : List Sym :=
  [ "full_walk_effort_m7", "full_watch_push_slow_m6", "full_watch_push_m6"
  , "full_delete_bin_side", "full_bva_commit" ]

private theorem fidStep8_frontNames_eq :
    fidStep8Bundle.frontTable.map SpecEntry.name = fidStep8FrontNames :=
  rfl

private theorem fidStep8_front_nodup :
    (fidStep8Bundle.frontTable.map SpecEntry.name).Nodup := by
  rw [fidStep8_frontNames_eq]
  decide

private theorem nodup_getElem?_inj' {α : Type _} {xs : List α} (hnd : xs.Nodup)
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
        simp at hi hj
        subst hi
        exact False.elim (hnmem (List.mem_iff_getElem?.mpr ⟨j, hj⟩))
    | succ i =>
      cases j with
      | zero =>
        simp at hi hj
        subst hj
        exact False.elim (hnmem (List.mem_iff_getElem?.mpr ⟨i, hi⟩))
      | succ j =>
        simp at hi hj
        exact congrArg Nat.succ (ih hnd' hi hj)

private theorem slot_ok_sound {fs : List Fn} (hnd : (fs.map Fn.name).Nodup)
    {i : Nat} {sig : SigEntry} {deps : List SigEntry}
    (hok : ((fs[i]?.map Fn.sig == some sig) &&
      deps.all fun d => ((fs.take i).map Fn.sig).contains d) = true) :
    (∃ g ∈ fs, fs[i]? = some g ∧ g.sig = sig) ∧
    (∀ bPre g bPost, fs = bPre ++ g :: bPost → g.name = sig.1 →
      ∀ d ∈ deps, d ∈ bPre.map Fn.sig) := by
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨hsig, hdeps⟩ := hok
  cases hg : fs[i]? with
  | none => simp [hg] at hsig
  | some g0 =>
    simp only [hg, Option.map_some, Option.some.injEq] at hsig
    refine ⟨⟨g0, List.mem_of_getElem? hg, rfl, hsig⟩, ?_⟩
    intro bPre g bPost hsplit hgnm d hd
    have hi1 : (fs.map Fn.name)[i]? = some sig.1 := by
      simp [List.getElem?_map, hg, ← hsig, Fn.sig]
    have hi2 : (fs.map Fn.name)[bPre.length]? = some sig.1 := by
      rw [hsplit]
      simp [hgnm]
    have hlen := (nodup_getElem?_inj' hnd hi1 hi2).symm
    have htake : bPre = fs.take i := by
      rw [← hlen]
      have ht := congrArg (List.take bPre.length) hsplit
      simpa [List.take_left'] using ht.symm
    rw [htake]
    exact List.contains_iff_mem.mp (hdeps d hd)

private theorem fidStep8_slots_unpacked :
    ( ((fidStep7Module.fns[161]?.map Fn.sig == some ("full_walk_effort_m7", [i64, i64], [i64])) &&
        ([] : List SigEntry).all fun d =>
          ((fidStep7Module.fns.take 161).map Fn.sig).contains d) = true ) ∧
    ( ((fidStep7Module.fns[16]?.map Fn.sig ==
          some ("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool])) &&
        ([("full_wstack_defrag_m6", [i64], [])] : List SigEntry).all fun d =>
          ((fidStep7Module.fns.take 16).map Fn.sig).contains d) = true ) ∧
    ( ((fidStep7Module.fns[17]?.map Fn.sig ==
          some ("full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool])) &&
        ([("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool])] :
          List SigEntry).all fun d =>
            ((fidStep7Module.fns.take 17).map Fn.sig).contains d) = true ) ∧
    ( ((fidStep7Module.fns[181]?.map Fn.sig ==
          some ("full_delete_bin_side", [i64, i32, i32], [])) &&
        ([] : List SigEntry).all fun d =>
          ((fidStep7Module.fns.take 181).map Fn.sig).contains d) = true ) ∧
    ( ((fidStep7Module.fns[436]?.map Fn.sig ==
          some ("full_bva_commit", [i64, i32], [.bool])) &&
        ([ ("full_bva_steps_cap_fid", [i64], [i32])
         , ("full_wstack_defrag", [i64], [])
         , ("full_init_fresh_var", [i64, i32], [])
         , ("full_add_bin", [i64, i32, i32], [i64])
         , ("full_alloc_cl", [i64, i32, i32, .bool], [i64])
         , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool])
         , ("full_delete_binary", [i64, i32, i32], [])
         , ("full_unwatch_large", [i64, i32, i32], []) ] : List SigEntry).all fun d =>
           ((fidStep7Module.fns.take 436).map Fn.sig).contains d) = true ) := by
  have h := fidStep7_step8_slots_ok
  have ⟨h1234, h5⟩ := (Bool.and_eq_true _ _).mp h
  have ⟨h123, h4⟩ := (Bool.and_eq_true _ _).mp h1234
  have ⟨h12, h3⟩ := (Bool.and_eq_true _ _).mp h123
  have ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h12
  exact ⟨h1, h2, h3, h4, h5⟩

theorem fidStep8Module_replSigs_ok :
    ∀ r ∈ FullFidelityStep8.fidStep8Repls, ∀ g ∈ fidStep7Module.fns,
      r.name = g.name → r.sig = g.sig := by
  have hnd := module_fns_namesNodup fidStep7Module_names_nodup
  have hs := fidStep8_slots_unpacked
  have s0 := (slot_ok_sound hnd hs.1).1
  have s1 := (slot_ok_sound hnd hs.2.1).1
  have s2 := (slot_ok_sound hnd hs.2.2.1).1
  have s3 := (slot_ok_sound hnd hs.2.2.2.1).1
  have s4 := (slot_ok_sound hnd hs.2.2.2.2).1
  intro r hr g hg hnm
  simp only [FullFidelityStep8.fidStep8Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨g0, hg0, _, hsg⟩ := s0
    rw [nodup_name_eq Fn.name hnd hg hg0 (hnm.symm.trans (congrArg Prod.fst hsg).symm)]
    exact hsg.symm
  · obtain ⟨g0, hg0, _, hsg⟩ := s1
    rw [nodup_name_eq Fn.name hnd hg hg0 (hnm.symm.trans (congrArg Prod.fst hsg).symm)]
    exact hsg.symm
  · obtain ⟨g0, hg0, _, hsg⟩ := s2
    rw [nodup_name_eq Fn.name hnd hg hg0 (hnm.symm.trans (congrArg Prod.fst hsg).symm)]
    exact hsg.symm
  · obtain ⟨g0, hg0, _, hsg⟩ := s3
    rw [nodup_name_eq Fn.name hnd hg hg0 (hnm.symm.trans (congrArg Prod.fst hsg).symm)]
    exact hsg.symm
  · obtain ⟨g0, hg0, _, hsg⟩ := s4
    rw [nodup_name_eq Fn.name hnd hg hg0 (hnm.symm.trans (congrArg Prod.fst hsg).symm)]
    exact hsg.symm

/-! ## 2. Single-Function Calls, `sameSpecs`, & `fidStep8_moduleOk` (`501/501`) -/

private theorem walkEffort_callsOk :
    FullFidelityStep8.fidStep8WalkEffortM7Fn.checkCallsOk [] [] = true := by
  t_kernel_rfl

private theorem watchPushSlow_callsOk :
    FullFidelityStep8.fidStep8WatchPushSlowM6Fn.checkCallsOk
      [("full_wstack_defrag_m6", [i64], [])] [] = true := by
  t_kernel_rfl

private theorem watchPush_callsOk :
    FullFidelityStep8.fidStep8WatchPushM6Fn.checkCallsOk
      [("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool])] [] = true := by
  t_kernel_rfl

private theorem deleteBinSide_callsOk :
    FullFidelityStep8.fidStep8DeleteBinSideFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

private theorem bvaCommit_callsOk :
    FullFidelityStep8.fidStep8BvaCommitFn.checkCallsOk
      [ ("full_bva_steps_cap_fid", [i64], [i32])
      , ("full_wstack_defrag", [i64], [])
      , ("full_init_fresh_var", [i64, i32], [])
      , ("full_add_bin", [i64, i32, i32], [i64])
      , ("full_alloc_cl", [i64, i32, i32, .bool], [i64])
      , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool])
      , ("full_delete_binary", [i64, i32, i32], [])
      , ("full_unwatch_large", [i64, i32, i32], []) ] [] = true := by
  t_kernel_rfl

private theorem fid8_of_step7 {f : Sym} {as bs : List Ty}
    (hf8 : !(fidStep8FrontNames.contains f) = true := by decide)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidStep7Env f as bs xs m Q X) :
    fidStep8Env f as bs xs m Q X := by
  change patchEnv fidStep8Bundle f as bs xs m Q X
  have hfnone : fidStep8Bundle.frontTable.find? (·.name == f) = none := by
    rw [List.find?_eq_none]
    intro e he hbeq
    have hm : f ∈ fidStep8FrontNames :=
      fidStep8_frontNames_eq ▸ (beq_iff_eq.mp hbeq ▸ List.mem_map_of_mem he)
    simp [hm] at hf8
  rw [patchEnv_base_eq fidStep8Bundle hfnone]
  dsimp only [fidStep8Bundle]
  rw [fidStep7Base_eq_env]
  exact h

private theorem fidStep8_sameSpecs :
    ∀ e ∈ fidStep8Bundle.frontTable, ∀ xs m P E,
      Env.ofTable fidStep8Bundle.baseTable e.name e.as e.rs xs m P E → e.eff xs m P E := by
  intro e he xs m P E hBase
  dsimp only [fidStep8Bundle] at hBase
  rw [fidStep7Base_eq_env] at hBase
  simp only [fidStep8Bundle, PatchBundle.frontTable, fidStep8ReplRows,
    List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact fidStep7_m7EffortSpec_monoX (fidStep7Env_elim_walkEffort hBase)
  · exact fidStep7Env_elim_watchPushSlow hBase
  · exact fidStep7Env_elim_watchPushM6 hBase
  · exact fidStep7Env_elim_deleteBinSide hBase
  · exact FullFidelityStep7.step7BvaCommitSpec_monoX (X := E) (X' := fun _ _ _ _ => False)
      (fidStep7Env_elim_bvaCommit hBase)

private theorem fidStep8_agree :
    ∀ s ∈ fidStep7Module.sigs,
      ∀ xs m P E, Env.ofTable fidStep7BaseSpecTable s.1 s.2.1 s.2.2 xs m P E →
        fidStep8Env s.1 s.2.1 s.2.2 xs m P E :=
  patchEnv_agree_of_sameSpecs fidStep8Bundle fidStep8_front_nodup fidStep8_sameSpecs

private theorem spliceFns_split_mem {repls fs pre post : List Fn} {fn : Fn}
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

private theorem fidStep8_front_none_of_repl_none {nm : Sym}
    (h : FullFidelityStep8.fidStep8Repls.find? (·.name == nm) = none) :
    fidStep8Bundle.frontTable.find? (·.name == nm) = none := by
  rw [List.find?_eq_none]
  intro e he hbeq
  have hnm : e.name = nm := beq_iff_eq.mp hbeq
  have hmem : e.name ∈ FullFidelityStep8.fidStep8Repls.map Fn.name := by
    have hm : e.name ∈ fidStep8FrontNames :=
      fidStep8_frontNames_eq ▸ List.mem_map_of_mem he
    exact hm
  obtain ⟨r, hr, hrn⟩ := List.mem_map.mp hmem
  have hnone := List.find?_eq_none.mp h r hr
  simp [hnm, hrn] at hnone

private theorem callsOk_sub_deps {fn : Fn} {deps bPrePre : List SigEntry}
    (hchk : fn.checkCallsOk deps [] = true)
    (hsub : ∀ d ∈ deps, d ∈ bPrePre) :
    fn.callsOk (bPrePre ++ fidStep8Module.externs.map Extern.sig) fidStep8Module.exits := by
  rw [fidStep8_noExit, fidStep8_externs_empty, List.map_nil, List.append_nil]
  exact fn_callsOk_mono hsub (Fn.callsOk_of_checkCallsOk hchk)

/-- Closed `501/501` `ModuleOk` for `FullFidelityAssemblyStep8.fidStep8Module` under
`fidStep8Env` (`0` externs, `0` exits, `std3` axioms only). -/
theorem fidStep8_moduleOk : ModuleOk fidStep8Env fidStep8Module := by
  refine ⟨fidStep8Module_names_nodup, fun pre fn post hsplit => ?_⟩
  have hsplit' : spliceFns FullFidelityStep8.fidStep8Repls fidStep7Module.fns =
      pre ++ fn :: post := by
    change patchFns FullFidelityStep8.fidStep8Repls [] fidStep7Module.fns = pre ++ fn :: post
      at hsplit
    rwa [patchFns_nil] at hsplit
  obtain ⟨bPre, f0, bPost, hfs, hfn_eq, hpreSig⟩ :=
    spliceFns_split_mem fidStep8Module_replSigs_ok hsplit'
  have hf0_ok := fidStep7Base_moduleOk.fnsOk bPre f0 bPost hfs
  have hnd7 := module_fns_namesNodup fidStep7Module_names_nodup
  have hslots := fidStep8_slots_unpacked
  cases hrepl : FullFidelityStep8.fidStep8Repls.find? (·.name == f0.name) with
  | none =>
    simp only [hrepl, Option.getD_none] at hfn_eq
    subst hfn_eq
    have hfrontNone := fidStep8_front_none_of_repl_none hrepl
    have hcalls7 : fn.callsOk (List.map Fn.sig bPre) [] := by
      simpa only [fidStep7_noExit, fidStep7_externs_empty, List.map_nil, List.append_nil] using
        hf0_ok.2.1
    refine ⟨hf0_ok.1, ?_, fun xs m Q X hlookup => ?_⟩
    · simpa only [fidStep8_noExit, fidStep8_externs_empty, List.map_nil, List.append_nil,
        hpreSig] using hcalls7
    · change fidStep8Env fn.name fn.as fn.rs xs m Q X at hlookup
      dsimp only [fidStep8Env] at hlookup
      rw [patchEnv_base_eq fidStep8Bundle hfrontNone] at hlookup
      dsimp only [fidStep8Bundle] at hlookup
      have hwp_base := hf0_ok.2.2 xs m Q X hlookup
      refine wp_env_agree_of_callsOk (hf0_ok.1 _ _ _ _ _ _) hf0_ok.2.1 (fun f as bs hs => ?_)
        m hwp_base
      apply fidStep8_agree (f, as, bs)
      simp only [Module.sigs, List.mem_append, List.mem_map] at hs ⊢
      rcases hs with ⟨g, hg, hgsig⟩ | ⟨ex, hex, hexsig⟩
      · exact Or.inl ⟨g, hfs ▸ List.mem_append_left _ hg, hgsig⟩
      · exact Or.inr ⟨ex, hex, hexsig⟩
  | some r =>
    have hr_mem : r ∈ FullFidelityStep8.fidStep8Repls := List.mem_of_find?_eq_some hrepl
    have hf0_nm : r.name = f0.name :=
      beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == f0.name) hrepl)
    simp only [hrepl, Option.getD_some] at hfn_eq
    subst hfn_eq
    refine ⟨FullFidelityStep8.fidStep8Repls_wf fn hr_mem, ?_, ?_⟩
    · simp only [FullFidelityStep8.fidStep8Repls, List.mem_cons, List.not_mem_nil,
        or_false] at hr_mem
      rw [hpreSig]
      rcases hr_mem with rfl | rfl | rfl | rfl | rfl
      · exact callsOk_sub_deps walkEffort_callsOk fun _ hd => nomatch hd
      · exact callsOk_sub_deps watchPushSlow_callsOk
          ((slot_ok_sound hnd7 hslots.2.1).2 bPre f0 bPost hfs hf0_nm.symm)
      · exact callsOk_sub_deps watchPush_callsOk
          ((slot_ok_sound hnd7 hslots.2.2.1).2 bPre f0 bPost hfs hf0_nm.symm)
      · exact callsOk_sub_deps deleteBinSide_callsOk fun _ hd => nomatch hd
      · exact callsOk_sub_deps bvaCommit_callsOk
          ((slot_ok_sound hnd7 hslots.2.2.2.2).2 bPre f0 bPost hfs hf0_nm.symm)
    · simp only [FullFidelityStep8.fidStep8Repls, List.mem_cons, List.not_mem_nil,
        or_false] at hr_mem
      rcases hr_mem with rfl | rfl | rfl | rfl | rfl
      · intro xs m Q X hlk
        have hfind : fidStep8Bundle.frontTable.find?
            (·.name == FullFidelityStep8.fidStep8WalkEffortM7Fn.name) =
            some fidStep8ReplRows[0] := rfl
        have hcast := env_ofTable_find?_of_append hfind rfl rfl hlk
        dsimp only [fidStep8ReplRows, List.getElem_cons_zero, List.getElem_cons_succ,
          SpecEntry.cast, SpecEntry.eff, ite_true] at hcast
        exact FullFidelityStep8.full_walk_effort_m7_step8_wp fidStep8Env xs m Q X
          (fidStep7_m7EffortSpec_elim (fidStep7_m7EffortSpec_monoX hcast))
      · intro xs m Q X hlk
        have hfind : fidStep8Bundle.frontTable.find?
            (·.name == FullFidelityStep8.fidStep8WatchPushSlowM6Fn.name) =
            some fidStep8ReplRows[1] := rfl
        have hcast := env_ofTable_find?_of_append hfind rfl rfl hlk
        dsimp only [fidStep8ReplRows, List.getElem_cons_zero, List.getElem_cons_succ,
          SpecEntry.cast, SpecEntry.eff, ite_true] at hcast
        exact FullFidelityStep8.full_watch_push_slow_m6_step8_wp fidStep8Env
          (fun _ _ _ _ hs => fid8_of_step7 (by decide) (fidStep7Env_wstackDefragM6 _ _ _ _ hs))
          xs m Q X hcast
      · intro xs m Q X hlk
        have hfind : fidStep8Bundle.frontTable.find?
            (·.name == FullFidelityStep8.fidStep8WatchPushM6Fn.name) =
            some fidStep8ReplRows[2] := rfl
        have hcast := env_ofTable_find?_of_append hfind rfl rfl hlk
        dsimp only [fidStep8ReplRows, List.getElem_cons_zero, List.getElem_cons_succ,
          SpecEntry.cast, SpecEntry.eff, ite_true] at hcast
        have hSlow : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
            fidStep8Env "full_watch_push_slow_m6" [i64, i32, i32, i32, i32] [.bool] a m Q X :=
          fun _ _ _ _ hs =>
            patchEnv_of_front_mem fidStep8Bundle fidStep8_front_nodup
              (List.mem_of_getElem? (i := 1) rfl) hs
        exact FullFidelityStep8.full_watch_push_m6_step8_wp fidStep8Env hSlow xs m Q X hcast
      · intro xs m Q X hlk
        have hfind : fidStep8Bundle.frontTable.find?
            (·.name == FullFidelityStep8.fidStep8DeleteBinSideFn.name) =
            some fidStep8ReplRows[3] := rfl
        have hcast := env_ofTable_find?_of_append hfind rfl rfl hlk
        dsimp only [fidStep8ReplRows, List.getElem_cons_zero, List.getElem_cons_succ,
          SpecEntry.cast, SpecEntry.eff, ite_true] at hcast
        exact FullFidelityStep8.full_delete_bin_side_step8_wp fidStep8Env xs m Q X hcast
      · intro xs m Q X hlk
        have hfind : fidStep8Bundle.frontTable.find?
            (·.name == FullFidelityStep8.fidStep8BvaCommitFn.name) =
            some fidStep8ReplRows[4] := rfl
        have hcast := env_ofTable_find?_of_append hfind rfl rfl hlk
        dsimp only [fidStep8ReplRows, List.getElem_cons_zero, List.getElem_cons_succ,
          SpecEntry.cast, SpecEntry.eff, ite_true] at hcast
        exact FullFidelityStep8.full_bva_commit_step8_wp fidStep8Env
          (fun _ _ _ _ hs => fid8_of_step7 (by decide) (fidStep7Env_bvaStepsCap _ _ _ _ hs))
          (fun _ _ _ _ hs => fid8_of_step7 (by decide) (fidStep7Env_wstackDefrag _ _ _ _ hs))
          (fun _ _ _ _ hs => fid8_of_step7 (by decide) (fidStep7Env_initFreshVar _ _ _ _ hs))
          (fun _ _ _ _ hs => fid8_of_step7 (by decide) (fidStep7Env_addBin _ _ _ _ hs))
          (fun _ _ _ _ hs => fid8_of_step7 (by decide) (fidStep7Env_allocCl _ _ _ _ hs))
          (fun _ _ _ _ hs => fid8_of_step7 (by decide) (fidStep7Env_watchPush _ _ _ _ hs))
          (fun _ _ _ _ hs => fid8_of_step7 (by decide) (fidStep7Env_deleteBinary _ _ _ _ hs))
          (fun _ _ _ _ hs => fid8_of_step7 (by decide) (fidStep7Env_unwatchLarge _ _ _ _ hs))
          xs m Q X
          (FullFidelityStep7.step7BvaCommitSpec_monoX (X := fun _ _ _ _ => False) hcast)

/-! ## 3. Exit-Freedom, UNSAT Soundness, Host Lift, `Mem 64` NV & `KissatUnsatPkg` -/

theorem fidStep8Env_noExit :
    ∀ f as bs xs m Q X X',
      fidStep8Env f as bs xs m Q X → fidStep8Env f as bs xs m Q X' :=
  patchEnv_noExit_of fidStep8Bundle (by decide) fidStep7BaseSpecTable_noExit

theorem fidStep8Env_solve_bytes_of {a : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m7FidSolveBytesSpec a m Q X →
      fidStep8Env "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X :=
  fun hs => fid8_of_step7 (by decide) (fidStep7Env_solve_bytes_of hs)

theorem fidStep8_solveBytes_mem : m6oSolveBytesFn ∈ fidStep8Module.fns :=
  patchBundle_solveBytes_mem fidStep8Bundle fidStep7_solveBytes_mem fun r hr => by
    change r ∈ FullFidelityStep8.fidStep8Repls at hr
    simp only [FullFidelityStep8.fidStep8Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Top-level byte-level UNSAT soundness of `fidStep8Module` (`501` fns, `XPost := False`). -/
theorem fidStep8_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidStep8Env FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fid_solve_bytes_sound_of fidStep8_moduleOk fidStep8_solveBytes_mem
    (fun _ _ _ _ hs => fidStep8Env_solve_bytes_of hs) hcfit hwfit hm

/-- Host-framed machine-memory UNSAT lift for `fidStep8Module`. -/
theorem fidStep8_solve_bytes_host_sound
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

/-- Concrete deterministic `Mem 64` UNSAT non-vacuity (`r = 20#64`) for `fidStep8Module`. -/
theorem fidStep8_unsat_nv :
    Func.wp fidStep8Env FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fid_unsat_nv_of fidStep8_moduleOk fidStep8_solveBytes_mem
    (fun _ _ _ _ hs => fidStep8Env_solve_bytes_of hs)

/-- Acyclicity certificate (`checkAcyclic = true`) lifted in `O(1)` from `fidStep8_moduleOk`. -/
theorem fidStep8Module_acyclic : fidStep8Module.checkAcyclic = true :=
  moduleCheckAcyclic_of_moduleOk fidStep8_moduleOk

/-- Canonical Gate-1 Step-8 `KissatUnsatPkg` (`fidStep8Module`, `fidInlPolicy`). -/
def fidStep8UnsatPkg : KissatUnsatPkg :=
  mkFidUnsatPkg fidStep8Module fidInlPolicy fidStep8_solveBytes_mem
    fidStep8Env fidStep8_moduleOk fidStep8Env_noExit
    (fun _ _ _ _ hs => fidStep8Env_solve_bytes_of hs)

/-! ## 4. Additive Thin Spec Interface for `fidStep8Env` (`0` `import all` Needed Down-Stream) -/

def fidStep8BaseSpecTable : List SpecEntry :=
  fidStep8Bundle.frontTable ++ fidStep8Bundle.baseTable

theorem fidStep8Base_eq_env : Env.ofTable fidStep8BaseSpecTable = fidStep8Env := by
  unfold fidStep8BaseSpecTable fidStep8Env patchEnv
  rfl

theorem fidStep8Base_moduleOk :
    ModuleOk (Env.ofTable fidStep8BaseSpecTable) fidStep8Module :=
  fidStep8_moduleOk

theorem fidStep8Base_noExit :
    ∀ f as bs xs m Q X X',
      Env.ofTable fidStep8BaseSpecTable f as bs xs m Q X →
      Env.ofTable fidStep8BaseSpecTable f as bs xs m Q X' :=
  fidStep8Env_noExit

theorem fidStep8BaseSpecTable_noExit :
    fidStep8BaseSpecTable.all SpecEntry.noExit = true := by
  unfold fidStep8BaseSpecTable
  rw [List.all_append, Bool.and_eq_true]
  exact ⟨by decide, fidStep7BaseSpecTable_noExit⟩

theorem fidStep8Base_solve_bytes_of {a : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m7FidSolveBytesSpec a m Q X →
      Env.ofTable fidStep8BaseSpecTable "kissat_solve_bytes"
        [i64, i64, i64, i64, i64] [i64] a m Q X :=
  fidStep8Env_solve_bytes_of

-- Step 7 exported callees (30 total) lifted into `fidStep8Env`
theorem fidStep8Env_bvaStepsCap :
    ∀ a m Q X, FullFidelityBva.fidBvaStepsCapSpec a m Q X →
      fidStep8Env "full_bva_steps_cap_fid" [i64] [i32] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_bvaStepsCap a m Q X hs)

theorem fidStep8Env_wstackDefrag :
    ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      fidStep8Env "full_wstack_defrag" [i64] [] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_wstackDefrag a m Q X hs)

theorem fidStep8Env_initFreshVar :
    ∀ a m Q X, FullFidelityStep7.step7InitFreshVarSpec a m Q X →
      fidStep8Env "full_init_fresh_var" [i64, i32] [] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_initFreshVar a m Q X hs)

theorem fidStep8Env_addBin :
    ∀ a m Q X, Full.fullAddBinSpec a m Q X →
      fidStep8Env "full_add_bin" [i64, i32, i32] [i64] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_addBin a m Q X hs)

theorem fidStep8Env_allocCl :
    ∀ a m Q X, Full.fullAllocClSpec a m Q X →
      fidStep8Env "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_allocCl a m Q X hs)

theorem fidStep8Env_watchPush :
    ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      fidStep8Env "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_watchPush a m Q X hs)

theorem fidStep8Env_deleteBinary :
    ∀ a m Q X, Full.fullDeleteBinarySpec a m Q X →
      fidStep8Env "full_delete_binary" [i64, i32, i32] [] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_deleteBinary a m Q X hs)

theorem fidStep8Env_unwatchLarge :
    ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      fidStep8Env "full_unwatch_large" [i64, i32, i32] [] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_unwatchLarge a m Q X hs)

theorem fidStep8Env_arenaNext :
    ∀ a m Q X, Full.fullArenaNextSpec a m Q X →
      fidStep8Env "full_arena_next" [i64, i32] [i32] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_arenaNext a m Q X hs)

theorem fidStep8Env_arenaSweep :
    ∀ a m Q X, Full.fullArenaSweepSpec a m Q X →
      fidStep8Env "full_arena_sweep" [i64] [i64] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_arenaSweep a m Q X hs)

theorem fidStep8Env_sweepBinsRangeM6 :
    ∀ a m Q X, FullM6WatchGc.fullSweepBinsRangeSpec a m Q X →
      fidStep8Env "full_sweep_bins_range_m6" [i64, i64] [] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_sweepBinsRangeM6 a m Q X hs)

theorem fidStep8Env_sweepCopy :
    ∀ a m Q X, Full.fullSweepCopySpec a m Q X →
      fidStep8Env "full_sweep_copy" [i64, i64, i64, i32, .bool] [i64] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_sweepCopy a m Q X hs)

theorem fidStep8Env_moveRedEndM6 :
    ∀ a m Q X, FullM6WatchGc.fullMoveRedEndSpec a m Q X →
      fidStep8Env "full_move_red_end_m6" [i64, i64, i64] [] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_moveRedEndM6 a m Q X hs)

theorem fidStep8Env_rewatchRangeM6 :
    ∀ a m Q X, FullM6WatchGc.fullRewatchRangeSpec a m Q X →
      fidStep8Env "full_rewatch_range_m6" [i64, i64, i64] [.bool] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_rewatchRangeM6 a m Q X hs)

theorem fidStep8Env_backtrack :
    ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      fidStep8Env "full_backtrack" [i64, i64] [] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_backtrack a m Q X hs)

theorem fidStep8Env_hdrRecomputeTiers :
    ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [] [] a m Q X →
      fidStep8Env "m6_hdr_recompute_tiers" [i64] [] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_hdrRecomputeTiers a m Q X hs)

theorem fidStep8Env_markReasons :
    ∀ a m Q X, Full.fullMarkReasonsSpec a m Q X →
      fidStep8Env "full_mark_reasons" [i64, .bool] [] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_markReasons a m Q X hs)

theorem fidStep8Env_isqrt :
    ∀ a m Q X, Full.fullIsqrtSpec a m Q X →
      fidStep8Env "full_isqrt" [i64] [i64] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_isqrt a m Q X hs)

theorem fidStep8Env_sortReds :
    ∀ a m Q X, Full.fullSortRedsSpec a m Q X →
      fidStep8Env "full_sort_reds" [i64, i64] [] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_sortReds a m Q X hs)

theorem fidStep8Env_log10Q16M7 :
    ∀ a m Q X, FullM7Search.m7Log10Q16Spec a m Q X →
      fidStep8Env "full_log10_q16_m7" [i64] [i64] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_log10Q16M7 a m Q X hs)

theorem fidStep8Env_hdrSetWatermark :
    ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [i64, i64] [] a m Q X →
      fidStep8Env "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_hdrSetWatermark a m Q X hs)

theorem fidStep8Env_hdrGetWatermark :
    ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [i64] a m Q X →
      fidStep8Env "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_hdrGetWatermark a m Q X hs)

theorem fidStep8Env_congExtractBinaries :
    ∀ a m Q X, FullM6CongSubst.m6CongExtractBinariesSpec a m Q X →
      fidStep8Env "full_cong_extract_binaries" [i64, i64] [i64] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_congExtractBinaries a m Q X hs)

theorem fidStep8Env_congFindUnitsEquivs :
    ∀ a m Q X, FullM6CongSubst.m6CongFindUnitsEquivsSpec a m Q X →
      fidStep8Env "full_cong_find_units_equivs" [i64] [i64] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_congFindUnitsEquivs a m Q X hs)

theorem fidStep8Env_probeDticksM6Hdr :
    ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [.bool] [i64] a m Q X →
      fidStep8Env "full_probe_dticks_m6_hdr" [i64, .bool] [i64] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_probeDticksM6Hdr a m Q X hs)

theorem fidStep8Env_scaleDeltaM5 :
    ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      fidStep8Env "full_scale_delta_m5" [i64, i64] [i64] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_scaleDeltaM5 a m Q X hs)

theorem fidStep8Env_hdrDelaying :
    ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [.bool] a m Q X →
      fidStep8Env "m6_hdr_delaying" [i64, i64] [.bool] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_hdrDelaying a m Q X hs)

theorem fidStep8Env_hdrReduceDelay :
    ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [] a m Q X →
      fidStep8Env "m6_hdr_reduce_delay" [i64, i64] [] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_hdrReduceDelay a m Q X hs)

theorem fidStep8Env_hdrBumpDelay :
    ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [] a m Q X →
      fidStep8Env "m6_hdr_bump_delay" [i64, i64] [] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_hdrBumpDelay a m Q X hs)

theorem fidStep8Env_sweepDenseM6 :
    ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      fidStep8Env "full_sweep_dense_m6" [i64, i64, i64] [i64] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_sweepDenseM6 a m Q X hs)

-- Front-table Step7/Step6/Step3/Step2 callees (17 total) lifted via `fidStep7Env_*`
theorem fidStep8Env_sortBinWatches :
    ∀ a m Q X, FullFidelityStep7.step7SortBinWatchesSpec a m Q X →
      fidStep8Env "full_sort_bin_watches_fid" [i64] [] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_sortBinWatches a m Q X hs)

theorem fidStep8Env_vivifyM6Hdr :
    ∀ a m Q X, FullM6OrchAdapters.m6aVivifySpec a m Q X →
      fidStep8Env "full_vivify_m6_hdr" [i64] [i64] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_vivifyM6Hdr a m Q X hs)

theorem fidStep8Env_bvaTryLit :
    ∀ a m Q X, FullFidelityStep7.step7BvaTryLitSpec a m Q X →
      fidStep8Env "full_bva_try_lit" [i64, i32, i64] [.bool] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_bvaTryLit a m Q X hs)

theorem fidStep8Env_fheapUp :
    ∀ a m Q X, FullFidelityBva.fidFheapUpSpec a m Q X →
      fidStep8Env "full_fheap_up_fid" [i64, i64, i64, i32] [] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_fheapUp a m Q X hs)

theorem fidStep8Env_fheapDown :
    ∀ a m Q X, FullFidelityBva.fidFheapDownSpec a m Q X →
      fidStep8Env "full_fheap_down_fid" [i64, i64, i64, i32, i32] [] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_fheapDown a m Q X hs)

theorem fidStep8Env_bvaCountLitDeg :
    ∀ a m Q X, FullFidelityBva.fidBvaCountLitDegSpec a m Q X →
      fidStep8Env "full_bva_count_lit_deg_fid" [i64, i32] [i32] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_bvaCountLitDeg a m Q X hs)

theorem fidStep8Env_bvaConnectClauses :
    ∀ a m Q X, FullFidelityBva.fidBvaConnectClausesSpec a m Q X →
      fidStep8Env "full_bva_connect_clauses_fid" [i64] [] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_bvaConnectClauses a m Q X hs)

theorem fidStep8Env_congExtract :
    ∀ a m Q X, FullFidelityCong.fidCongExtractSpec a m Q X →
      fidStep8Env "full_cong_extract" [i64, i64, i64] [i64] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_congExtract a m Q X hs)

theorem fidStep8Env_congWorklist :
    ∀ a m Q X, FullFidelityCong.fidCongWorklistSpec a m Q X →
      fidStep8Env "full_cong_worklist" [i64, i64, i64, i64] [i64] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_congWorklist a m Q X hs)

theorem fidStep8Env_congFwdSubsume :
    ∀ a m Q X, FullM6CongSubst.m6CongFwdSubsumeSpec a m Q X →
      fidStep8Env "full_cong_fwd_subsume" [i64, i64] [i64] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_congFwdSubsume a m Q X hs)

theorem fidStep8Env_congExtractIteAll :
    ∀ a m Q X, FullFidelityCong.fidCongExtractIteAllSpec a m Q X →
      fidStep8Env "full_cong_extract_ite_all_m7" [i64, i32, i32, i64] [i32] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_congExtractIteAll a m Q X hs)

theorem fidStep8Env_propagate :
    ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      fidStep8Env "full_propagate" [i64] [i64] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_propagate a m Q X hs)

theorem fidStep8Env_flushTrail :
    ∀ a m Q X, FullM6CompactFlush.fullFlushTrailSpec a m Q X →
      fidStep8Env "full_flush_trail" [i64] [i64] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_flushTrail a m Q X hs)

theorem fidStep8Env_backboneM6 :
    ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      fidStep8Env "full_backbone_m6" [i64, i64] [i64] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_backboneM6 a m Q X hs)

theorem fidStep8Env_transitiveM6 :
    ∀ a m Q X, FullFastBveBudgets.fullTransitiveFastSpec a m Q X →
      fidStep8Env "full_transitive_m6" [i64, i64] [i64] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_transitiveM6 a m Q X hs)

theorem fidStep8Env_substitute :
    ∀ a m Q X, Full.fullSubstituteSpec a m Q X →
      fidStep8Env "full_substitute" [i64] [i64] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_substitute a m Q X hs)

theorem fidStep8Env_enterDense :
    ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      fidStep8Env "full_enter_dense" [i64] [.bool] a m Q X :=
  fun a m Q X hs => fid8_of_step7 (by decide) (fidStep7Env_enterDense a m Q X hs)

-- Eliminators for `10` sig-preserved Step-9 repls (`bva_upd_lit_fid` changes `7 -> 6` args)
private theorem fidStep8_find_none_front8 {nm : Sym}
    (h : !(fidStep8FrontNames.contains nm) = true) :
    fidStep8Bundle.frontTable.find? (·.name == nm) = none := by
  rw [List.find?_eq_none]
  intro e he hbeq
  have hm : nm ∈ fidStep8FrontNames :=
    fidStep8_frontNames_eq ▸ (beq_iff_eq.mp hbeq ▸ List.mem_map_of_mem he)
  simp [hm] at h

private theorem fidStep8_peel_from_base {f : Sym} {as bs : List Ty}
    (hf8 : !(fidStep8FrontNames.contains f) = true := by decide)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidStep8Env f as bs xs m Q X) :
    fidStep7Env f as bs xs m Q X := by
  change patchEnv fidStep8Bundle f as bs xs m Q X at h
  rw [patchEnv_base_eq fidStep8Bundle (fidStep8_find_none_front8 hf8)] at h
  dsimp only [fidStep8Bundle] at h
  rwa [fidStep7Base_eq_env] at h

theorem fidStep8Env_elim_propFlushDel {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (h : fidStep8Env "full_prop_flush_del_fid" [i64, i64] [.bool] xs m Q X) :
    FullFidelityBcp.fidPropFlushDelSpec xs m Q X :=
  fidStep7Env_elim_propFlushDel (fidStep8_peel_from_base (by decide) h)

theorem fidStep8Env_elim_arenaSweepM6 {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidStep8Env "full_arena_sweep_m6" [i64] [i64] xs m Q X) :
    Full.fullArenaSweepSpec xs m Q X :=
  fidStep7Env_elim_arenaSweepM6 (fidStep8_peel_from_base (by decide) h)

theorem fidStep8Env_elim_reduceM6 {xs : Tup Val [i64, .bool]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidStep8Env "full_reduce_m6" [i64, .bool] [i64] xs m Q X) :
    m6ReduceSpec xs m Q X :=
  fidStep7Env_elim_reduceM6 (fidStep8_peel_from_base (by decide) h)

theorem fidStep8Env_elim_congruenceDense {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidStep8Env "full_congruence_dense" [i64, i64] [i64] xs m Q X) :
    FullM3CongBva.m3CongruenceDenseSpec xs m Q X :=
  fidStep7Env_elim_congruenceDense (fidStep8_peel_from_base (by decide) h)

theorem fidStep8Env_elim_rebuildWatches {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidStep8Env "full_rebuild_watches" [i64] [i64] xs m Q X) :
    Full.fullRebuildWatchesSpec xs m Q X :=
  fidStep7Env_elim_rebuildWatches (fidStep8_peel_from_base (by decide) h)

theorem fidStep8Env_elim_bvaCommit {xs : Tup Val [i64, i32]} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (h : fidStep8Env "full_bva_commit" [i64, i32] [.bool] xs m Q X) :
    FullFidelityStep7.step7BvaCommitSpec xs m Q X := by
  have hfind : fidStep8Bundle.frontTable.find? (·.name == "full_bva_commit") =
      some fidStep8ReplRows[4] := rfl
  have hc : FullFidelityStep7.step7BvaCommitSpec xs m Q (fun _ _ _ _ => False) :=
    env_ofTable_find?_of_append hfind rfl rfl h
  exact FullFidelityStep7.step7BvaCommitSpec_monoX hc

theorem fidStep8Env_elim_factor {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidStep8Env "full_factor" [i64, i64] [i64] xs m Q X) :
    FullBvaHeap.fullFactorHeapSpec xs m Q X :=
  fidStep7Env_elim_factor (fidStep8_peel_from_base (by decide) h)

theorem fidStep8Env_elim_compactNeeded {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (h : fidStep8Env "full_compact_needed" [i64] [.bool] xs m Q X) :
    FullM4Compact.fullCompactNeededSpec xs m Q X :=
  fidStep7Env_elim_compactNeeded (fidStep8_peel_from_base (by decide) h)

theorem fidStep8Env_elim_compactFlush {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidStep8Env "full_compact_flush" [i64] [i64] xs m Q X) :
    FullM4Compact.fullCompactFlushSpec xs m Q X :=
  fidStep7Env_elim_compactFlush (fidStep8_peel_from_base (by decide) h)

theorem fidStep8Env_elim_probeM6 {xs : Tup Val [i64, .bool]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidStep8Env "full_probe_m6" [i64, .bool] [i64] xs m Q X) :
    m6ProbeSpec xs m Q X :=
  fidStep7Env_elim_probeM6 (fidStep8_peel_from_base (by decide) h)

private theorem spliceFns_map_sig {repls fs : List Fn}
    (hreplSigs : ∀ r ∈ repls, ∀ g ∈ fs, r.name = g.name → r.sig = g.sig) :
    (spliceFns repls fs).map Fn.sig = fs.map Fn.sig := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [spliceFns, List.map_cons, List.cons.injEq]
    refine ⟨?_, ih fun r hr g hg => hreplSigs r hr g (by simp [hg])⟩
    cases hf : repls.find? (·.name == f.name) with
    | none => rfl
    | some rf =>
      have hnm : rf.name = f.name :=
        beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == f.name) hf)
      exact hreplSigs rf (List.mem_of_find?_eq_some hf) f List.mem_cons_self hnm

theorem fidStep8Fns_map_sig :
    fidStep8Module.fns.map Fn.sig = fidStep7Module.fns.map Fn.sig := by
  rw [fidStep8Fns_eq, fidStep8Fns, patchFns_nil]
  exact spliceFns_map_sig fidStep8Module_replSigs_ok

theorem fidStep8_step9_sig_at {p : Nat × SigEntry} (hp : p ∈ fidStep7_step9_sigPairs) :
    fidStep8Module.fns[p.1]?.map Fn.sig = some p.2 := by
  have h1 : (fidStep8Module.fns.map Fn.sig)[p.1]? = some p.2 := by
    rw [fidStep8Fns_map_sig, List.getElem?_map]
    exact fidStep7_step9_sig_at hp
  simpa [List.getElem?_map] using h1

private theorem fidStep8Repls_noCallBvaUpdLit :
    FullFidelityStep8.fidStep8Repls.all (noCallInFn ["full_bva_upd_lit_fid"]) = true := by
  t_kernel_rfl

private theorem spliceFns_drop (repls : List Fn) :
    ∀ (fs : List Fn) (k : Nat), (spliceFns repls fs).drop k = spliceFns repls (fs.drop k)
  | _, 0 => rfl
  | [], _ + 1 => rfl
  | _ :: fs, k + 1 => spliceFns_drop repls fs k

mutual
private theorem callsOk_not_mem_noCallIn {allowed : List SigEntry} {exits : List Sym}
    {badNm : Sym} {rs : List Ty} :
    ∀ (e : Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ s ∈ allowed, s.1 ≠ badNm) → e.callsOk allowed exits →
      checkNoCallInExpr [badNm] e = true
  | .let_ _ k, hbad, hc => callsOk_not_mem_noCallIn (k (Tup.units _)) hbad hc
  | .load _ _ k, hbad, hc => callsOk_not_mem_noCallIn (k ()) hbad hc
  | .store _ _ k, hbad, hc => callsOk_not_mem_noCallIn k hbad hc
  | .call f (as := as) (bs := bs) _ k, hbad, hc => by
      simp only [Expr.callsOk] at hc
      simp only [checkNoCallInExpr, Bool.and_eq_true]
      refine ⟨?_, callsOk_not_mem_noCallIn (k (Tup.units bs)) hbad hc.2⟩
      have hne : f ≠ badNm := hbad (f, as, bs) hc.1
      simp [hne]
  | .jnz _ t e, hbad, hc => by
      simp only [checkNoCallInExpr, Bool.and_eq_true]
      exact ⟨callsOk_not_mem_noCallIn t hbad hc.1, callsOk_not_mem_noCallIn e hbad hc.2⟩
  | .jump _ _, _, _ | .ret _, _, _ | .exit _ _, _, _ | .hlt, _, _ => rfl
  | .group (sig := sig) bodies k, hbad, hc => by
      simp only [checkNoCallInExpr, Bool.and_eq_true]
      exact ⟨blocks_callsOk_not_mem_noCallIn (bodies (Tup.units sig)) hbad hc.1,
        callsOk_not_mem_noCallIn (k (Tup.units sig)) hbad hc.2⟩

private theorem blocks_callsOk_not_mem_noCallIn {allowed : List SigEntry} {exits : List Sym}
    {badNm : Sym} {rs : List Ty} :
    ∀ {sig : List (List Ty)} (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig),
      (∀ s ∈ allowed, s.1 ≠ badNm) → bs.callsOk allowed exits →
      checkNoCallInBlocks [badNm] bs = true
  | _, .nil, _, _ => rfl
  | _, .cons b bs, hbad, hc => by
    simp only [checkNoCallInBlocks, Bool.and_eq_true]
    exact ⟨callsOk_not_mem_noCallIn (b (Tup.units _)) hbad hc.1,
      blocks_callsOk_not_mem_noCallIn bs hbad hc.2⟩
end

private theorem fn_callsOk_not_mem_noCallIn {allowed : List SigEntry} {exits : List Sym}
    {badNm : Sym} {fn : Fn} (hbad : ∀ s ∈ allowed, s.1 ≠ badNm) (hc : fn.callsOk allowed exits) :
    noCallInFn [badNm] fn = true :=
  callsOk_not_mem_noCallIn _ hbad hc

theorem fidStep8_noCallBvaUpdLit_ok :
    ∀ fn ∈ fidStep8Module.fns, fn.name ≠ "full_factor" →
      noCallInFn ["full_bva_upd_lit_fid"] fn = true := by
  have hslot440 : fidStep8Module.fns[440]?.map Fn.sig =
      some ("full_bva_upd_lit_fid", [i64, i64, i64, i64, i32, i64, i32], [i32]) :=
    fidStep8_step9_sig_at (p := (440, _)) (by decide)
  have hnd : (fidStep8Module.fns.map Fn.name).Nodup :=
    module_fns_namesNodup fidStep8Module_names_nodup
  intro fn hfn hne
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hfn
  by_cases hlt : pre.length < 441
  · have hok := fidStep8_moduleOk.fnsOk pre fn post hsplit
    have hcalls : fn.callsOk (pre.map Fn.sig) [] := by
      simpa only [fidStep8_noExit, fidStep8_externs_empty, List.map_nil, List.append_nil] using
        hok.2.1
    refine fn_callsOk_not_mem_noCallIn (fun s hs hnm => ?_) hcalls
    obtain ⟨g, hg, hgs⟩ := List.mem_map.mp hs
    obtain ⟨g0, hg0, hgi0⟩ := List.mem_iff_getElem.mp hg
    have hg0_idx : (fidStep8Module.fns.map Fn.name)[g0]? = some "full_bva_upd_lit_fid" := by
      have hg_eq : fidStep8Module.fns[g0]? = some g := by
        rw [hsplit, List.getElem?_append_left (by omega), List.getElem?_eq_getElem hg0, hgi0]
      have hgnm : g.name = "full_bva_upd_lit_fid" := (congrArg Prod.fst hgs).trans hnm
      simp [List.getElem?_map, hg_eq, hgnm]
    have h440_nm : (fidStep8Module.fns.map Fn.name)[440]? = some "full_bva_upd_lit_fid" := by
      cases h440 : fidStep8Module.fns[440]? with
      | none => simp [h440] at hslot440
      | some f440 =>
        simp only [h440, Option.map_some, Option.some.injEq] at hslot440
        have hnm440 : f440.name = "full_bva_upd_lit_fid" := congrArg Prod.fst hslot440
        simp [List.getElem?_map, h440, hnm440]
    have heq440 := nodup_getElem?_inj' hnd hg0_idx h440_nm
    omega
  · have hge : 441 ≤ pre.length := Nat.not_lt.mp hlt
    have hmem_drop : fn ∈ fidStep8Module.fns.drop 441 := by
      have hdrop : fidStep8Module.fns.drop 441 = pre.drop 441 ++ fn :: post := by
        rw [hsplit, List.drop_append_of_le_length hge]
      rw [hdrop]; simp
    rw [fidStep8Fns_eq, fidStep8Fns, patchFns_nil, spliceFns_drop] at hmem_drop
    simp only [PatchModule.spliceFns, List.mem_map] at hmem_drop
    obtain ⟨f7, hf7_mem, rfl⟩ := hmem_drop
    cases hr : FullFidelityStep8.fidStep8Repls.find? (·.name == f7.name) with
    | none =>
      have hcell := List.all_eq_true.mp fidStep7_noCallBvaUpdLit_tail f7 hf7_mem
      rcases (Bool.or_eq_true _ _).mp hcell with hskip | hok
      · simp only [List.contains_iff_mem, List.mem_singleton] at hskip
        exact absurd hskip (by simpa [hr] using hne)
      · simpa [hr] using hok
    | some r =>
      have hr_mem := List.mem_of_find?_eq_some hr
      simpa [hr] using List.all_eq_true.mp fidStep8Repls_noCallBvaUpdLit r hr_mem

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep8

end
