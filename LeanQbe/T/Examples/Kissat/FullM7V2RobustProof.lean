/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7V2RobustProof0
public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
public import LeanQbe.T.Examples.Kissat.FullM7PlusAssemblyProof
import LeanQbe.T.Examples.Kissat.FullM6SatNv
import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.WPLemmas

/-!
# Kissat `M7` v2 Robustness Closed & Splice Verification (`FullM7V2RobustProof`)

M1-clean (`public section`, `0 @[expose]`, `0 @[local]`, `0 import all`, `0 sorry`, `std3` axioms
only) UNSAT-only verification (`XPost := False`, zero SAT model-finding proofs) for
`FullM7V2Robust`, with zero edits to any existing `FullM6*` / `FullM7*` module or cert slice:

* **Standalone closed `5+12`-entry verification (`v2RobustModule`):**
  `v2RobustEnv`, `v2Robust_checkAcyclic`, `v2RobustEnv_noExit`, `v2Robust_moduleOk`.
* **Generic `patchFns` & `V2RobustEnv` bridge:**
  `V2RobustEnv`, `v2rEnv_noExit_of`, `V2RobustCallees`, `patchModule_moduleOk`,
  `patchFns_eq_fid`, `patchFns_eq_plus`.
* **Target A (`m7FidV2RobustModule`, `415` fns) & Target B (`m7PlusV2RobustModule`, `412` fns):**
  `m7FidV2Robust_checkAcyclic`, `m7FidV2RobustEnv_noExit`, `m7FidV2Robust_moduleOk_of`,
  `m7FidV2Robust_solve_bytes_sound_of`, `m7FidV2Robust_solve_bytes_host_sound`,
  `m7FidV2Robust_unsat_nv_of`, and symmetric `m7PlusV2Robust_*`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7V2Robust

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM7Proof

/-! ## 1. Closed `V2RobustEnv`, Eliminators, & Generic `patchModule_moduleOk` -/

/-- Closed extension of a base `Env` `Γ` adding the two fresh v2 robustness helpers
`full_watch_pop_c0` (`fullWatchPopC0Spec`) and `full_reduce_purge_c0`
(`fullReducePurgeC0Spec`), while delegating all remaining symbols cleanly to `Γ`. -/
inductive V2RobustEnv (Γ : Env) : Env where
  | base {f as bs xs m Q X} :
      f ≠ "full_watch_pop_c0" →
      f ≠ "full_reduce_purge_c0" →
      Γ f as bs xs m Q X → V2RobustEnv Γ f as bs xs m Q X
  | watchPop {xs m Q X} :
      fullWatchPopC0Spec xs m Q (fun _ _ _ _ => False) →
      V2RobustEnv Γ "full_watch_pop_c0" [i64, i32, i32] [] xs m Q X
  | reducePurge {xs m Q X} :
      fullReducePurgeC0Spec xs m Q (fun _ _ _ _ => False) →
      V2RobustEnv Γ "full_reduce_purge_c0" [i64] [i64] xs m Q X

theorem v2rEnv_noExit_of {Γ : Env}
    (hno : ∀ f as bs xs m Q X X', Γ f as bs xs m Q X → Γ f as bs xs m Q X') :
    ∀ f as bs xs m Q X X', V2RobustEnv Γ f as bs xs m Q X → V2RobustEnv Γ f as bs xs m Q X' := by
  intro f as bs xs m Q X X' h
  cases h with
  | base h1 h2 hb => exact .base h1 h2 (hno _ _ _ _ _ _ _ _ hb)
  | watchPop hw => exact .watchPop hw
  | reducePurge hr => exact .reducePurge hr

private theorem V2RobustEnv.elim_ne {Γ : Env} {f : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h1 : f ≠ "full_watch_pop_c0") (h2 : f ≠ "full_reduce_purge_c0")
    (h : V2RobustEnv Γ f as bs xs m Q X) : Γ f as bs xs m Q X := by
  cases h with
  | base _ _ hb => exact hb
  | watchPop => exact absurd rfl h1
  | reducePurge => exact absurd rfl h2

private theorem V2RobustEnv.elim_watchPop_aux {Γ : Env} {f : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (hf : f = "full_watch_pop_c0") (h : V2RobustEnv Γ f as bs xs m Q X) :
    ∃ (ha : as = [i64, i32, i32]) (hb : bs = []),
      fullWatchPopC0Spec (ha ▸ xs) m (hb ▸ Q) (fun _ _ _ _ => False) := by
  cases h with
  | base h1 _ _ => exact absurd hf h1
  | watchPop hw => exact ⟨rfl, rfl, hw⟩
  | reducePurge => exact absurd hf (by decide)

private theorem V2RobustEnv.elim_watchPop {Γ : Env} {xs : Tup Val [i64, i32, i32]}
    {m : Mem 64} {Q : Post []} {X : XPost}
    (h : V2RobustEnv Γ "full_watch_pop_c0" [i64, i32, i32] [] xs m Q X) :
    fullWatchPopC0Spec xs m Q (fun _ _ _ _ => False) := by
  have ⟨rfl, rfl, hw⟩ := V2RobustEnv.elim_watchPop_aux rfl h
  exact hw

private theorem V2RobustEnv.elim_reducePurge_aux {Γ : Env} {f : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (hf : f = "full_reduce_purge_c0") (h : V2RobustEnv Γ f as bs xs m Q X) :
    ∃ (ha : as = [i64]) (hb : bs = [i64]),
      fullReducePurgeC0Spec (ha ▸ xs) m (hb ▸ Q) (fun _ _ _ _ => False) := by
  cases h with
  | base _ h2 _ => exact absurd hf h2
  | watchPop => exact absurd hf (by decide)
  | reducePurge hr => exact ⟨rfl, rfl, hr⟩

private theorem V2RobustEnv.elim_reducePurge {Γ : Env} {xs : Tup Val [i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : V2RobustEnv Γ "full_reduce_purge_c0" [i64] [i64] xs m Q X) :
    fullReducePurgeC0Spec xs m Q (fun _ _ _ _ => False) := by
  have ⟨rfl, rfl, hr⟩ := V2RobustEnv.elim_reducePurge_aux rfl h
  exact hr

/-- Base-environment callee interface needed to certify any `M` patched with
`v2RobustRepls` / `v2RobustBefores` under `V2RobustEnv Γ`. -/
structure V2RobustCallees (Γ : Env) : Prop where
  allocCl : ∀ a m Q X, fullAllocClSpec a m Q X →
    Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X
  watchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
    Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X
  assignLvl : ∀ a m Q X, fullAssignLvlSpec a m Q X →
    Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X
  backtrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
    Γ "full_backtrack" [i64, i64] [] a m Q X
  detNewLevel : ∀ a m Q X, fullDetNewLevelSpec a m Q X →
    Γ "full_det_new_level" [i64, i64] [i64] a m Q X
  wstackDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
    Γ "full_wstack_defrag" [i64] [] a m Q X
  reduce : ∀ a m Q X, fullReduceSpec a m Q X →
    Γ "full_reduce" [i64, .bool] [i64] a m Q X
  addClause : ∀ a m Q X, fullAddClauseSpec a m Q X →
    Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X
  eagerSubsume : ∀ a m Q X, fullEagerSubsumeSpec a m Q X →
    Γ "full_eager_subsume" [i64, i64] [] a m Q X
  propagate : ∀ a m Q X, fullPropagateSpec a m Q X →
    Γ "full_propagate" [i64] [i64] a m Q X
  markReasons : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
    Γ "full_mark_reasons" [i64, .bool] [] a m Q X
  arenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
    Γ "full_arena_next" [i64, i32] [i32] a m Q X
  arenaSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
    Γ "full_arena_sweep" [i64] [i64] a m Q X
  addClauseElim : ∀ xs m Q X,
    Γ "full_add_clause" [i64, i32, i32, .bool] [i64] xs m Q X →
    fullAddClauseSpec xs m Q X
  sweepCopyElim : ∀ xs m Q X,
    Γ "full_sweep_copy" [i64, i64, i64, i32, .bool] [i64] xs m Q X →
    fullSweepCopySpec xs m Q X
  learnClauseElim : ∀ xs m Q X,
    Γ "full_learn_clause" [i64, i64] [i64] xs m Q X →
    fullLearnClauseSpec xs m Q X

private theorem v2r_mem_patchInsAt {befores : List (Sym × List Fn)} {g fn : Fn}
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

private theorem v2r_befores_wp {Γ : Env} (hc : V2RobustCallees Γ) :
    ∀ p ∈ v2RobustBefores, ∀ b ∈ p.2, ∀ xs m Q X,
      V2RobustEnv Γ b.name b.as b.rs xs m Q X → Func.wp (V2RobustEnv Γ) b.body xs m Q X := by
  intro p hp b hb xs m Q X hrow
  simp only [v2RobustBefores, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · simp only [List.mem_singleton] at hb; subst hb
    exact full_watch_pop_c0_wp (V2RobustEnv Γ) xs m Q X
      (fullWatchPopC0Spec_monoX (V2RobustEnv.elim_watchPop hrow))
  · simp only [List.mem_singleton] at hb; subst hb
    exact full_reduce_purge_c0_wp (V2RobustEnv Γ)
      (fun a m' Q' X' hs => .base (by decide) (by decide) (hc.backtrack a m' Q' X' hs))
      (fun a m' Q' X' hs => .base (by decide) (by decide) (hc.propagate a m' Q' X' hs))
      (fun a m' Q' X' hs => .base (by decide) (by decide) (hc.markReasons a m' Q' X' hs))
      (fun a m' Q' X' hs => .base (by decide) (by decide) (hc.arenaNext a m' Q' X' hs))
      (fun a m' Q' X' hs => .base (by decide) (by decide) (hc.arenaSweep a m' Q' X' hs))
      xs m Q X (fullReducePurgeC0Spec_monoX (V2RobustEnv.elim_reducePurge hrow))

private theorem v2r_repls_wp {Γ : Env} (hc : V2RobustCallees Γ) :
    ∀ r ∈ v2RobustRepls, ∀ xs m Q X,
      V2RobustEnv Γ r.name r.as r.rs xs m Q X → Func.wp (V2RobustEnv Γ) r.body xs m Q X := by
  intro r hr xs m Q X hrow
  have hPop : ∀ a m' Q' X', fullWatchPopC0Spec a m' Q' X' →
      V2RobustEnv Γ "full_watch_pop_c0" [i64, i32, i32] [] a m' Q' X' :=
    fun _ _ _ _ hw => .watchPop (fullWatchPopC0Spec_monoX hw)
  simp only [v2RobustRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact full_add_clause_wp (V2RobustEnv Γ)
      (fun a m' Q' X' hs => .base (by decide) (by decide) (hc.allocCl a m' Q' X' hs))
      (fun a m' Q' X' hs => .base (by decide) (by decide) (hc.watchPush a m' Q' X' hs))
      hPop xs m Q X
      (hc.addClauseElim xs m Q X (V2RobustEnv.elim_ne (by decide) (by decide) hrow))
  · exact full_sweep_copy_wp (V2RobustEnv Γ)
      (fun a m' Q' X' hs => .base (by decide) (by decide) (hc.assignLvl a m' Q' X' hs))
      (fun a m' Q' X' hs => .base (by decide) (by decide) (hc.watchPush a m' Q' X' hs))
      hPop xs m Q X
      (hc.sweepCopyElim xs m Q X (V2RobustEnv.elim_ne (by decide) (by decide) hrow))
  · exact full_learn_clause_wp (V2RobustEnv Γ)
      (fun a m' Q' X' hs => .base (by decide) (by decide) (hc.backtrack a m' Q' X' hs))
      (fun a m' Q' X' hs => .base (by decide) (by decide) (hc.assignLvl a m' Q' X' hs))
      (fun a m' Q' X' hs => .base (by decide) (by decide) (hc.detNewLevel a m' Q' X' hs))
      (fun a m' Q' X' hs => .base (by decide) (by decide) (hc.wstackDefrag a m' Q' X' hs))
      (fun a m' Q' X' hs => .base (by decide) (by decide) (hc.reduce a m' Q' X' hs))
      (fun a m' Q' X' hs => .reducePurge (fullReducePurgeC0Spec_monoX hs))
      (fun a m' Q' X' hs => .base (by decide) (by decide) (hc.addClause a m' Q' X' hs))
      (fun a m' Q' X' hs => .base (by decide) (by decide) (hc.eagerSubsume a m' Q' X' hs))
      xs m Q X
      (hc.learnClauseElim xs m Q X (V2RobustEnv.elim_ne (by decide) (by decide) hrow))

/-- Generic `patchFns` soundness theorem: patching any verified `ModuleOk Γ M` with
`v2RobustRepls` / `v2RobustBefores` yields `ModuleOk (V2RobustEnv Γ)` whenever `M` does not
already define/declare the two inserted helper names and `Γ` exposes `V2RobustCallees`. -/
theorem patchModule_moduleOk {Γ : Env} {M : LeanQbe.T.Module}
    (hM : ModuleOk Γ M)
    (hchk : ({ M with fns := patchFns v2RobustRepls v2RobustBefores M.fns } :
      LeanQbe.T.Module).checkAcyclic = true)
    (hNotFns : M.fns.all (fun fn =>
      fn.name != "full_watch_pop_c0" && fn.name != "full_reduce_purge_c0") = true)
    (hNotExts : M.externs.all (fun ex =>
      ex.name != "full_watch_pop_c0" && ex.name != "full_reduce_purge_c0") = true)
    (hc : V2RobustCallees Γ) :
    ModuleOk (V2RobustEnv Γ) { M with fns := patchFns v2RobustRepls v2RobustBefores M.fns } := by
  have hwfOrig : ∀ f ∈ M.fns, f.Wf := fun f hf => by
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hf
    exact (hM.fnsOk pre f post hsplit).1
  have hNoHelperFn : ∀ g ∈ M.fns,
      g.name ≠ "full_watch_pop_c0" ∧ g.name ≠ "full_reduce_purge_c0" := fun g hg => by
    simpa [Bool.and_eq_true, bne_iff_ne] using List.all_eq_true.mp hNotFns g hg
  have hNoHelperEx : ∀ ex ∈ M.externs,
      ex.name ≠ "full_watch_pop_c0" ∧ ex.name ≠ "full_reduce_purge_c0" := fun ex hex => by
    simpa [Bool.and_eq_true, bne_iff_ne] using List.all_eq_true.mp hNotExts ex hex
  refine LeanQbe.T.Module.moduleOk_of_checkAcyclic hchk
    (patchFns_wf hwfOrig v2RobustRepls_wf v2RobustBefores_wf) ?_
  intro fn hmem
  rcases List.mem_flatMap.mp hmem with ⟨g, hg, hfn⟩
  rcases List.mem_append.mp hfn with hins | hcur
  · rcases v2r_mem_patchInsAt hins with ⟨hs, hm, hfn_hs⟩
    exact v2r_befores_wp hc (g.name, hs) hm fn hfn_hs
  · rcases List.mem_singleton.mp hcur with rfl
    cases h : v2RobustRepls.find? (fun x => x.name == g.name) with
    | some r =>
      intro xs m Q X hspec
      exact v2r_repls_wp hc r (List.mem_of_find?_eq_some h) xs m Q X hspec
    | none =>
      intro xs m Q X hspec
      obtain ⟨h1, h2⟩ := hNoHelperFn g hg
      have hb : Γ g.name g.as g.rs xs m Q X := V2RobustEnv.elim_ne h1 h2 hspec
      obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
      have ⟨hwfG, hcallsG, hwpG⟩ := hM.fnsOk pre g post hsplit
      refine wp_env_agree_of_callsOk
        (hwfG Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units g.as))
        hcallsG
        (fun f as bs hmemSig xs' m' Q' X' hc0 => by
          rcases List.mem_append.mp hmemSig with hf | he
          · rcases List.mem_map.mp hf with ⟨cfn, hcfn_pre, hsig⟩
            have hcfn_M : cfn ∈ M.fns :=
              hsplit ▸ List.mem_append_left (g :: post) hcfn_pre
            have hnm : cfn.name = f := congrArg Prod.fst hsig
            obtain ⟨hc1, hc2⟩ := hNoHelperFn cfn hcfn_M
            exact .base (hnm ▸ hc1) (hnm ▸ hc2) hc0
          · rcases List.mem_map.mp he with ⟨cex, hcex_M, hsig⟩
            have hnm : cex.name = f := congrArg Prod.fst hsig
            obtain ⟨hc1, hc2⟩ := hNoHelperEx cex hcex_M
            exact .base (hnm ▸ hc1) (hnm ▸ hc2) hc0)
        m (hwpG xs m Q X hb)

theorem patchFns_eq_fid :
    FullM7V2Robust.patchFns v2RobustRepls v2RobustBefores FullM7Fidelity.m7FidelityFns =
      m7FidV2RobustFns :=
  rfl

theorem patchFns_eq_plus :
    FullM7V2Robust.patchFns v2RobustRepls v2RobustBefores FullM7Plus.m7PlusFns =
      m7PlusV2RobustFns :=
  rfl

/-! ## 2. Closed Standalone `5+12`-Entry Verification (`v2RobustModule`) -/

section StandaloneSection

/-- Closed standalone `Env` for the `12` external callees of `v2RobustModule` (`XPost := False`,
zero hooks). -/
inductive V2RobustExtEnv : Env where
  | allocCl {xs m Q X} : fullAllocClSpec xs m Q X →
      V2RobustExtEnv "full_alloc_cl" [i64, i32, i32, .bool] [i64] xs m Q X
  | watchPush {xs m Q X} : fullWatchPushSpec xs m Q X →
      V2RobustExtEnv "full_watch_push" [i64, i32, i32, i32, i32] [.bool] xs m Q X
  | assignLvl {xs m Q X} : fullAssignLvlSpec xs m Q X →
      V2RobustExtEnv "full_assign_lvl" [i64, i32, i32, i32] [] xs m Q X
  | backtrack {xs m Q X} : fullBacktrackSpec xs m Q X →
      V2RobustExtEnv "full_backtrack" [i64, i64] [] xs m Q X
  | detNewLevel {xs m Q X} : fullDetNewLevelSpec xs m Q X →
      V2RobustExtEnv "full_det_new_level" [i64, i64] [i64] xs m Q X
  | wstackDefrag {xs m Q X} : fullWstackDefragSpec xs m Q X →
      V2RobustExtEnv "full_wstack_defrag" [i64] [] xs m Q X
  | reduce {xs m Q X} : fullReduceSpec xs m Q X →
      V2RobustExtEnv "full_reduce" [i64, .bool] [i64] xs m Q X
  | addClause {xs m Q X} : fullAddClauseSpec xs m Q X →
      V2RobustExtEnv "full_add_clause" [i64, i32, i32, .bool] [i64] xs m Q X
  | sweepCopy {xs m Q X} : fullSweepCopySpec xs m Q X →
      V2RobustExtEnv "full_sweep_copy" [i64, i64, i64, i32, .bool] [i64] xs m Q X
  | learnClause {xs m Q X} : fullLearnClauseSpec xs m Q X →
      V2RobustExtEnv "full_learn_clause" [i64, i64] [i64] xs m Q X
  | eagerSubsume {xs m Q X} : fullEagerSubsumeSpec xs m Q X →
      V2RobustExtEnv "full_eager_subsume" [i64, i64] [] xs m Q X
  | propagate {xs m Q X} : fullPropagateSpec xs m Q X →
      V2RobustExtEnv "full_propagate" [i64] [i64] xs m Q X
  | markReasons {xs m Q X} : fullMarkReasonsSpec xs m Q X →
      V2RobustExtEnv "full_mark_reasons" [i64, .bool] [] xs m Q X
  | arenaNext {xs m Q X} : fullArenaNextSpec xs m Q X →
      V2RobustExtEnv "full_arena_next" [i64, i32] [i32] xs m Q X
  | arenaSweep {xs m Q X} : fullArenaSweepSpec xs m Q X →
      V2RobustExtEnv "full_arena_sweep" [i64] [i64] xs m Q X

/-- Closed `Env` certifying `v2RobustModule` (`5` C0 functions + `12` external callee specs). -/
def v2RobustEnv : Env := V2RobustEnv V2RobustExtEnv

theorem v2Robust_checkAcyclic : v2RobustModule.checkAcyclic = true :=
  v2Robust_acyclic

theorem v2RobustEnv_noExit : ∀ f as bs xs m Q X X',
    v2RobustEnv f as bs xs m Q X → v2RobustEnv f as bs xs m Q X' := by
  refine v2rEnv_noExit_of fun f as bs xs m Q X X' h => ?_
  cases h with
  | allocCl s => exact .allocCl s
  | watchPush s => exact .watchPush s
  | assignLvl s => exact .assignLvl s
  | backtrack s => exact .backtrack s
  | detNewLevel s => exact .detNewLevel s
  | wstackDefrag s => exact .wstackDefrag s
  | reduce s => exact .reduce s
  | addClause s => exact .addClause s
  | sweepCopy s => exact .sweepCopy s
  | learnClause s => exact .learnClause s
  | eagerSubsume s => exact .eagerSubsume s
  | propagate s => exact .propagate s
  | markReasons s => exact .markReasons s
  | arenaNext s => exact .arenaNext s
  | arenaSweep s => exact .arenaSweep s

private theorem v2rExt_addClause_elim {xs : Tup Val [i64, i32, i32, .bool]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : V2RobustExtEnv "full_add_clause" [i64, i32, i32, .bool] [i64] xs m Q X) :
    fullAddClauseSpec xs m Q X := by
  have aux : ∀ {f as bs xs m Q X} (hf : f = "full_add_clause"),
      V2RobustExtEnv f as bs xs m Q X →
      ∃ (ha : as = [i64, i32, i32, .bool]) (hb : bs = [i64]),
        fullAddClauseSpec (ha ▸ xs) m (hb ▸ Q) X := by
    intro f as bs xs m Q X hf he
    cases he with
    | addClause s => exact ⟨rfl, rfl, s⟩
    | _ => exact absurd hf (by decide)
  have ⟨rfl, rfl, s⟩ := aux rfl h
  exact s

private theorem v2rExt_sweepCopy_elim {xs : Tup Val [i64, i64, i64, i32, .bool]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : V2RobustExtEnv "full_sweep_copy" [i64, i64, i64, i32, .bool] [i64] xs m Q X) :
    fullSweepCopySpec xs m Q X := by
  have aux : ∀ {f as bs xs m Q X} (hf : f = "full_sweep_copy"),
      V2RobustExtEnv f as bs xs m Q X →
      ∃ (ha : as = [i64, i64, i64, i32, .bool]) (hb : bs = [i64]),
        fullSweepCopySpec (ha ▸ xs) m (hb ▸ Q) X := by
    intro f as bs xs m Q X hf he
    cases he with
    | sweepCopy s => exact ⟨rfl, rfl, s⟩
    | _ => exact absurd hf (by decide)
  have ⟨rfl, rfl, s⟩ := aux rfl h
  exact s

private theorem v2rExt_learnClause_elim {xs : Tup Val [i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : V2RobustExtEnv "full_learn_clause" [i64, i64] [i64] xs m Q X) :
    fullLearnClauseSpec xs m Q X := by
  have aux : ∀ {f as bs xs m Q X} (hf : f = "full_learn_clause"),
      V2RobustExtEnv f as bs xs m Q X →
      ∃ (ha : as = [i64, i64]) (hb : bs = [i64]),
        fullLearnClauseSpec (ha ▸ xs) m (hb ▸ Q) X := by
    intro f as bs xs m Q X hf he
    cases he with
    | learnClause s => exact ⟨rfl, rfl, s⟩
    | _ => exact absurd hf (by decide)
  have ⟨rfl, rfl, s⟩ := aux rfl h
  exact s

private theorem v2rExtCallees : V2RobustCallees V2RobustExtEnv := {
  allocCl := fun _ _ _ _ s => .allocCl s
  watchPush := fun _ _ _ _ s => .watchPush s
  assignLvl := fun _ _ _ _ s => .assignLvl s
  backtrack := fun _ _ _ _ s => .backtrack s
  detNewLevel := fun _ _ _ _ s => .detNewLevel s
  wstackDefrag := fun _ _ _ _ s => .wstackDefrag s
  reduce := fun _ _ _ _ s => .reduce s
  addClause := fun _ _ _ _ s => .addClause s
  eagerSubsume := fun _ _ _ _ s => .eagerSubsume s
  propagate := fun _ _ _ _ s => .propagate s
  markReasons := fun _ _ _ _ s => .markReasons s
  arenaNext := fun _ _ _ _ s => .arenaNext s
  arenaSweep := fun _ _ _ _ s => .arenaSweep s
  addClauseElim := fun _ _ _ _ h => v2rExt_addClause_elim h
  sweepCopyElim := fun _ _ _ _ h => v2rExt_sweepCopy_elim h
  learnClauseElim := fun _ _ _ _ h => v2rExt_learnClause_elim h }

/-- Closed `5/5` `ModuleOk` for standalone `v2RobustModule` under `v2RobustEnv`. -/
theorem v2Robust_moduleOk : ModuleOk v2RobustEnv v2RobustModule := by
  refine LeanQbe.T.Module.moduleOk_of_checkAcyclic v2Robust_acyclic v2Robust_fns_wf ?_
  intro fn hmem xs m Q X hspec
  simp only [v2RobustModule, v2Robust_fns] at hmem
  have hmem' : fn ∈ v2Robust_fns := hmem
  simp only [v2Robust_fns, List.mem_cons, List.not_mem_nil, or_false] at hmem'
  rcases hmem' with rfl | rfl | rfl | rfl | rfl
  · exact v2r_befores_wp v2rExtCallees ("full_add_clause", [v2rWatchPopFn])
      (by simp [v2RobustBefores]) v2rWatchPopFn (by simp) xs m Q X hspec
  · exact v2r_repls_wp v2rExtCallees v2rAddClauseFn
      (by simp [v2RobustRepls]) xs m Q X hspec
  · exact v2r_repls_wp v2rExtCallees v2rSweepCopyFn
      (by simp [v2RobustRepls]) xs m Q X hspec
  · exact v2r_befores_wp v2rExtCallees ("full_learn_clause", [v2rReducePurgeFn])
      (by simp [v2RobustBefores]) v2rReducePurgeFn (by simp) xs m Q X hspec
  · exact v2r_repls_wp v2rExtCallees v2rLearnClauseFn
      (by simp [v2RobustRepls]) xs m Q X hspec

theorem v2RobustEnv_watchPop {xs : Tup Val [i64, i32, i32]} {m : Mem 64} {Q : Post []}
    {X : XPost} (h : fullWatchPopC0Spec xs m Q X) :
    v2RobustEnv "full_watch_pop_c0" [i64, i32, i32] [] xs m Q X :=
  .watchPop (fullWatchPopC0Spec_monoX h)

theorem v2RobustEnv_addClause {xs : Tup Val [i64, i32, i32, .bool]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : fullAddClauseSpec xs m Q X) :
    v2RobustEnv "full_add_clause" [i64, i32, i32, .bool] [i64] xs m Q X :=
  .base (by decide) (by decide) (.addClause h)

theorem v2RobustEnv_sweepCopy {xs : Tup Val [i64, i64, i64, i32, .bool]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : fullSweepCopySpec xs m Q X) :
    v2RobustEnv "full_sweep_copy" [i64, i64, i64, i32, .bool] [i64] xs m Q X :=
  .base (by decide) (by decide) (.sweepCopy h)

theorem v2RobustEnv_reducePurge {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : fullReducePurgeC0Spec xs m Q X) :
    v2RobustEnv "full_reduce_purge_c0" [i64] [i64] xs m Q X :=
  .reducePurge (fullReducePurgeC0Spec_monoX h)

theorem v2RobustEnv_reducePurge_of_full {h : BitVec 64} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (hr : fullReduceSpec (h, true, ()) m Q X) :
    v2RobustEnv "full_reduce_purge_c0" [i64] [i64] (h, ()) m Q X :=
  v2RobustEnv_reducePurge (fullReducePurgeC0Spec_of_full hr)

theorem v2RobustEnv_learnClause {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : fullLearnClauseSpec xs m Q X) :
    v2RobustEnv "full_learn_clause" [i64, i64] [i64] xs m Q X :=
  .base (by decide) (by decide) (.learnClause h)

end StandaloneSection

/-! ## 3. Target A (`m7FidV2RobustModule`, `415` Fns) Bridge & UNSAT Theorems -/

section TargetFidelity

open FullM7Fidelity

/-- Closed `Env` extending `m7FidelityEnv` with `full_watch_pop_c0` and `full_reduce_purge_c0`. -/
def m7FidV2RobustEnv : Env := V2RobustEnv m7FidelityEnv

theorem m7FidV2Robust_checkAcyclic : m7FidV2RobustModule.checkAcyclic = true :=
  m7FidV2Robust_acyclic

theorem m7FidV2RobustEnv_noExit : ∀ f as bs xs m Q X X',
    m7FidV2RobustEnv f as bs xs m Q X → m7FidV2RobustEnv f as bs xs m Q X' :=
  v2rEnv_noExit_of m7FidelityEnv_noExit

/-- `415/415` `ModuleOk` for `m7FidV2RobustModule` under `m7FidV2RobustEnv` given
`V2RobustCallees m7FidelityEnv`. -/
theorem m7FidV2Robust_moduleOk_of (hc : V2RobustCallees m7FidelityEnv) :
    ModuleOk m7FidV2RobustEnv m7FidV2RobustModule :=
  patchModule_moduleOk m7Fidelity_moduleOk m7FidV2Robust_acyclic
    (by t_kernel_rfl) (by rfl) hc

theorem m7FidV2Robust_solveBytes_mem :
    FullM6Orch.m6oSolveBytesFn ∈ m7FidV2RobustModule.fns := by
  refine patchFns_mem_of_ne m7Fidelity_solveBytes_mem fun r hr => ?_
  simp only [v2RobustRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> decide

/-- Top-level UNSAT-only `kissat_solve_bytes` soundness theorem for `m7FidV2RobustModule`
(`415` fns) under `m7FidV2RobustEnv` (`XPost := False`, zero SAT model proofs). -/
theorem m7FidV2Robust_solve_bytes_sound_of (hc : V2RobustCallees m7FidelityEnv)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m7FidV2RobustEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m7FidV2Robust_solveBytes_mem
  have hfn := ((m7FidV2Robust_moduleOk_of hc).fnsOk pre _ post hsplit).2.2
  refine hfn _ m _ (fun _ _ _ _ => False)
    (.base (by decide) (by decide)
      (m7FidelityEnv_solve_bytes (m7FidSolveBytesSpec_intro hcfit hwfit hm ?_)))
  intro r m' hdom h20 _ hmem
  exact ⟨hdom, h20, hmem⟩

/-- Host-framed machine-memory UNSAT lift for `m7FidV2RobustModule`. -/
theorem m7FidV2Robust_solve_bytes_host_sound
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hq :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hdmem : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) ⋆ F_host) st_dmem :=
  ⟨hq.1, hq.2.1, sep_mono (fun _ hm0 => by subst hm0; exact hq.2.2) hdmem⟩

/-- Concrete deterministic Tier-3b UNSAT non-vacuity (`XPost := False`, `r = 20#64`) for
`m7FidV2RobustModule` on `nvM6UnsatInitMem`. -/
theorem m7FidV2Robust_unsat_nv_of (hc : V2RobustCallees m7FidelityEnv) :
    Func.wp m7FidV2RobustEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m7FidV2Robust_solveBytes_mem
  have hfn := ((m7FidV2Robust_moduleOk_of hc).fnsOk pre _ post hsplit).2.2
  have hm0 : (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen ⋆ emp)
      nvM6UnsatInitMem := by
    rw [Std.ExtHashMap.sep_emp]
    exact nvM6UnsatInitMem_sep
  refine hfn _ _ _ (fun _ _ _ _ => False)
    (.base (by decide) (by decide)
      (m7FidelityEnv_solve_bytes (m7FidSolveBytesSpec_intro (by decide) (by decide) hm0 ?_)))
  intro r m' _ _ htr hm'
  have hr20 : r = 20#64 := htr 1 2 9 (by decide) (by decide) (by decide) nvM6_unsat_bound
    (by decide) nvM6Unsat_header nvM6Unsat_unitTrace
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨hr20, nvM6UnsatCnf_unsat, hm'⟩

end TargetFidelity

/-! ## 4. Target B (`m7PlusV2RobustModule`, `412` Fns) Bridge & UNSAT Theorems -/

section TargetPlus

open FullM7Plus

/-- Closed `Env` extending `m7PlusEnv` with `full_watch_pop_c0` and `full_reduce_purge_c0`. -/
def m7PlusV2RobustEnv : Env := V2RobustEnv m7PlusEnv

theorem m7PlusV2Robust_checkAcyclic : m7PlusV2RobustModule.checkAcyclic = true :=
  m7PlusV2Robust_acyclic

theorem m7PlusV2RobustEnv_noExit : ∀ f as bs xs m Q X X',
    m7PlusV2RobustEnv f as bs xs m Q X → m7PlusV2RobustEnv f as bs xs m Q X' :=
  v2rEnv_noExit_of m7PlusEnv_noExit

/-- `412/412` `ModuleOk` for `m7PlusV2RobustModule` under `m7PlusV2RobustEnv` given
`V2RobustCallees m7PlusEnv`. -/
theorem m7PlusV2Robust_moduleOk_of (hc : V2RobustCallees m7PlusEnv) :
    ModuleOk m7PlusV2RobustEnv m7PlusV2RobustModule :=
  patchModule_moduleOk m7Plus_moduleOk m7PlusV2Robust_acyclic
    (by t_kernel_rfl) (by rfl) hc

theorem m7PlusV2Robust_solveBytes_mem :
    FullM6Orch.m6oSolveBytesFn ∈ m7PlusV2RobustModule.fns := by
  refine patchFns_mem_of_ne m7Plus_solveBytes_mem fun r hr => ?_
  simp only [v2RobustRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> decide

/-- Top-level UNSAT-only `kissat_solve_bytes` soundness theorem for `m7PlusV2RobustModule`
(`412` fns) under `m7PlusV2RobustEnv` (`XPost := False`, zero SAT model proofs). -/
theorem m7PlusV2Robust_solve_bytes_sound_of (hc : V2RobustCallees m7PlusEnv)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m7PlusV2RobustEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m7PlusV2Robust_solveBytes_mem
  have hfn := ((m7PlusV2Robust_moduleOk_of hc).fnsOk pre _ post hsplit).2.2
  refine hfn _ m _ (fun _ _ _ _ => False)
    (.base (by decide) (by decide)
      (m7PlusEnv_solve_bytes (m7PlusSolveBytesSpec_intro hcfit hwfit hm ?_)))
  intro r m' hdom h20 _ hmem
  exact ⟨hdom, h20, hmem⟩

/-- Host-framed machine-memory UNSAT lift for `m7PlusV2RobustModule`. -/
theorem m7PlusV2Robust_solve_bytes_host_sound
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hq :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hdmem : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) ⋆ F_host) st_dmem :=
  ⟨hq.1, hq.2.1, sep_mono (fun _ hm0 => by subst hm0; exact hq.2.2) hdmem⟩

/-- Concrete deterministic Tier-3b UNSAT non-vacuity (`XPost := False`, `r = 20#64`) for
`m7PlusV2RobustModule` on `nvM6UnsatInitMem`. -/
theorem m7PlusV2Robust_unsat_nv_of (hc : V2RobustCallees m7PlusEnv) :
    Func.wp m7PlusV2RobustEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m7PlusV2Robust_solveBytes_mem
  have hfn := ((m7PlusV2Robust_moduleOk_of hc).fnsOk pre _ post hsplit).2.2
  have hm0 : (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen ⋆ emp)
      nvM6UnsatInitMem := by
    rw [Std.ExtHashMap.sep_emp]
    exact nvM6UnsatInitMem_sep
  refine hfn _ _ _ (fun _ _ _ _ => False)
    (.base (by decide) (by decide)
      (m7PlusEnv_solve_bytes (m7PlusSolveBytesSpec_intro (by decide) (by decide) hm0 ?_)))
  intro r m' _ _ htr hm'
  have hr20 : r = 20#64 := htr 1 2 9 (by decide) (by decide) (by decide) nvM6_unsat_bound
    (by decide) nvM6Unsat_header nvM6Unsat_unitTrace
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨hr20, nvM6UnsatCnf_unsat, hm'⟩

end TargetPlus

end LeanQbe.T.Examples.Kissat.FullM7V2Robust
