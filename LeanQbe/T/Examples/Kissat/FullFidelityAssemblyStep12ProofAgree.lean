/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12Proof0
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof0b
public import LeanQbe.T.Examples.Kissat.FullM7AnalyzeHdrProof
public import LeanQbe.T.Examples.Kissat.PatchModule
import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyProof
import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7Proof
import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep8Proof
import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9Proof
import LeanQbe.T.Examples.Kissat.FullFidelityStep10ProofLearn
import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
import LeanQbe.T.Examples.Kissat.FullM6OrchProof0
import LeanQbe.T.Examples.Kissat.FullM6OrchProof1
import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof0
import LeanQbe.T.Examples.Kissat.FullM6SatSound
import LeanQbe.T.Examples.Kissat.FullM7SearchProof0

/-!
# Kissat Fidelity Step 12 Environment Lifts, `agree`, & Callees
(`FullFidelityAssemblyStep12ProofAgree`)

Environment transport lemmas (`fid12_of_step10`, `fid12_peel_to_step10`, `fid12_frontRow`),
base callee spec intro wrappers into `fidStep12Env`, and `fidStep12_agree` over all `40`
non-`bad` rows of `fidStep12Bundle.frontTable` (`< 1,000` LOC, `0` `@[expose]` on thms/lemmas,
`0` `import all`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullDefSweep
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullFidelityAssembly
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep8
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
open LeanQbe.T.Examples.Kissat.FullFidelityVivK6
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullFidelityBva
open LeanQbe.T.Examples.Kissat.FullFidelityCong
open LeanQbe.T.Examples.Kissat.FullFidelityStep7
open LeanQbe.T.Examples.Kissat.FullFidelityStep9
open LeanQbe.T.Examples.Kissat.FullFidelityStep11Pr3
open LeanQbe.T.Examples.Kissat.FullFidelityStep12A
open LeanQbe.T.Examples.Kissat.FullFidelityStep12B
open LeanQbe.T.Examples.Kissat.FullFidelityStep12C
open LeanQbe.T.Examples.Kissat.FullFidelityTumble
open LeanQbe.T.Examples.Kissat.FullM3Backbone
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM4Compact
open LeanQbe.T.Examples.Kissat.FullM5HeurCore
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM7MemShrink
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.PatchModule

/-! ## 1. Core `fidStep12Env` Lifts & Peels -/

theorem fid12_of_step10 {f : Sym} {as bs : List Ty}
    (hf12 : !(fidStep12FrontNames.contains f) = true := by decide)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidStep10Env f as bs xs m Q X) :
    fidStep12Env f as bs xs m Q X := by
  change patchEnv fidStep12Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep12Bundle (fidStep12_front_none_of_names hf12)]
  dsimp only [fidStep12Bundle]
  rwa [fidStep10Base_eq_env]

theorem fid12_peel_to_step10 {f : Sym} {as bs : List Ty}
    (hf12 : !(fidStep12FrontNames.contains f) = true)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidStep12Env f as bs xs m Q X) :
    fidStep10Env f as bs xs m Q X := by
  change patchEnv fidStep12Bundle f as bs xs m Q X at h
  rw [patchEnv_base_eq fidStep12Bundle (fidStep12_front_none_of_names hf12)] at h
  dsimp only [fidStep12Bundle] at h
  rwa [fidStep10Base_eq_env] at h

theorem fid12_frontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidStep12Bundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ a m Q X, sp a m Q X → fidStep12Env nm as bs a m Q X := fun a m Q X hs =>
  patchEnv_of_front_mem fidStep12Bundle fidStep12_front_nodup (List.mem_of_getElem? hi)
    (hno a m Q X hs)

private theorem fid12_peel_step9_from10 {f : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidStep10Env f as bs xs m Q X)
    (hf10 : !(fidStep10FrontNames.contains f) = true := by decide) :
    fidStep9Env f as bs xs m Q X :=
  fidStep10Env_s12Peel hf10 h

private theorem fid12_peel_step7_from10 {f : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidStep10Env f as bs xs m Q X)
    (hf8 : !(fidStep8FrontNames.contains f) = true := by decide)
    (hf9 : !(fidStep9FrontNames.contains f) = true := by decide)
    (hf10 : !(fidStep10FrontNames.contains f) = true := by decide) :
    fidStep7Env f as bs xs m Q X :=
  fidStep8Env_s12Peel hf8 (fidStep9Env_s12Peel hf9 (fidStep10Env_s12Peel hf10 h))

private theorem fid12_peel_fid_from10 {f : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidStep10Env f as bs xs m Q X)
    (hf7 : !(fidStep7FrontNames.contains f) = true := by decide)
    (hf8 : !(fidStep8FrontNames.contains f) = true := by decide)
    (hf9 : !(fidStep9FrontNames.contains f) = true := by decide)
    (hf10 : !(fidStep10FrontNames.contains f) = true := by decide) :
    fidEnv f as bs xs m Q X :=
  fidStep7Env_s12Peel hf7 (fid12_peel_step7_from10 h hf8 hf9 hf10)

private theorem fid12_of_step9 {f : Sym} {as bs : List Ty}
    (hf10 : !(fidStep10FrontNames.contains f) = true := by decide)
    (hf12 : !(fidStep12FrontNames.contains f) = true := by decide)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidStep9Env f as bs xs m Q X) :
    fidStep12Env f as bs xs m Q X :=
  fid12_of_step10 hf12 (fidStep10Env_s12Lift hf10 h)

private theorem fid12_of_step8 {f : Sym} {as bs : List Ty}
    (hf9 : !(fidStep9FrontNames.contains f) = true := by decide)
    (hf10 : !(fidStep10FrontNames.contains f) = true := by decide)
    (hf12 : !(fidStep12FrontNames.contains f) = true := by decide)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidStep8Env f as bs xs m Q X) :
    fidStep12Env f as bs xs m Q X :=
  fid12_of_step9 hf10 hf12 (fidStep9Env_s12Lift hf9 h)

private theorem fid12_of_step7 {f : Sym} {as bs : List Ty}
    (hf8 : !(fidStep8FrontNames.contains f) = true := by decide)
    (hf9 : !(fidStep9FrontNames.contains f) = true := by decide)
    (hf10 : !(fidStep10FrontNames.contains f) = true := by decide)
    (hf12 : !(fidStep12FrontNames.contains f) = true := by decide)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidStep7Env f as bs xs m Q X) :
    fidStep12Env f as bs xs m Q X :=
  fid12_of_step8 hf9 hf10 hf12 (fidStep8Env_s12Lift hf8 h)

private theorem fid12_of_fid {f : Sym} {as bs : List Ty}
    (hf7 : !(fidStep7FrontNames.contains f) = true := by decide)
    (hf8 : !(fidStep8FrontNames.contains f) = true := by decide)
    (hf9 : !(fidStep9FrontNames.contains f) = true := by decide)
    (hf10 : !(fidStep10FrontNames.contains f) = true := by decide)
    (hf12 : !(fidStep12FrontNames.contains f) = true := by decide)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidEnv f as bs xs m Q X) :
    fidStep12Env f as bs xs m Q X :=
  fid12_of_step7 hf8 hf9 hf10 hf12 (fidStep7Env_s12Lift hf7 h)

/-! ## 2. `fidStep12_sameSpecs` & `fidStep12_agree` -/

private theorem fid12Pr3ReplRows_eq :
    fid12Pr3ReplRows =
      fidStep11Pr3ReplRows.take 4 ++
        [ ⟨"full_deduce_1uip_m6_hdr", [i64], [i64],
            FullFidelityStep11.s11Deduce1uipHdrSpec, true⟩ ] ++
        (fidStep11Pr3ReplRows.drop 5).take 2 ++ fidStep11Pr3ReplRows.drop 8 :=
  rfl

private theorem fid12Step12AReplRows_eq :
    fid12Step12AReplRows = FullFidelityStep12A.fidStep12AReplRows.take 5 :=
  rfl

private theorem fid12_before_not_in10 :
    fidStep12BeforeRows.all (fun b => !(fidStep10FnNames.contains b.name)) = true := by
  t_kernel_rfl

private theorem fidStep12_sameSpecs :
    ∀ e ∈ fidStep12Bundle.frontTable,
      e.name ∈ fidStep10FnNames →
      e.name ∉ fidStep12Bad →
      ∀ xs m P E,
        Env.ofTable fidStep12Bundle.baseTable e.name e.as e.rs xs m P E →
        e.eff xs m P E := by
  intro e he he10 hnb xs m P E hBase
  dsimp only [fidStep12Bundle] at hBase
  rw [fidStep10Base_eq_env] at hBase
  simp only [fidStep12Bundle, PatchBundle.frontTable, fidStep12ReplRows, List.append_assoc,
    List.mem_append] at he
  rcases he with hrw | hpr1 | htum | hpr3 | h12b | h12c | h12a | hbef
  · simp only [fidStep12BRewireRows, List.mem_singleton] at hrw
    subst hrw
    exact fidEnv_elim_congWorkStep (fid12_peel_fid_from10 hBase)
  · simp only [fid12Pr1Rows, List.mem_cons, List.not_mem_nil, or_false] at hpr1
    rcases hpr1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact m6AnalyzeRsnHdrSpec_monoX (fidStep10Env_elim_analyzeRsnM6Hdr hBase)
    · exact m6aAnaFailedLitSpecP_monoXP (fidStep10Env_elim_anaFailedLitM6Hdr hBase)
    · exact FullM8CoreParity.m8MinShrinkSpec_monoX (fidStep10Env_elim_minShrinkM6 hBase)
    · rcases xs with ⟨_, ⟨⟩⟩
      exact fidStep10Env_elim_analyze hBase
    · exact m6HdrAnalyzeSpec_monoX (fidStep10Env_elim_analyzeCoreM6 hBase)
    · exact m6aVivifyTierSpec_monoX (fidStep10Env_elim_vivifyTierM6Hdr hBase)
    · exact FullM7Search.m7SwitchModeSpec_monoX (fidStep10Env_elim_switchModeM7 hBase)
    · exact fullM6PreprocessSpec_monoX (fidStep10Env_elim_preprocessM6 hBase)
  · simp only [fidStep11TumReplRows, List.mem_cons, List.not_mem_nil, or_false] at htum
    rcases htum with rfl | rfl | rfl | rfl | rfl | rfl
    · exact fidEnv_elim_zeroTables2 (fid12_peel_fid_from10 hBase)
    · exact fidEnv_elim_initHdr (fid12_peel_fid_from10 hBase)
    · exact absurd (by decide : "full_ingest_cl" ∈ fidStep12Bad) hnb
    · exact fidEnv_elim_parseBodyM6 (fid12_peel_fid_from10 hBase)
    · exact fidEnv_elim_extend (fid12_peel_fid_from10 hBase)
    · exact fidEnv_elim_luckyScan (fid12_peel_fid_from10 hBase)
  · simp only [fid12Pr3ReplRows_eq, fidStep11Pr3ReplRows, List.take, List.drop,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hpr3
    rcases hpr3 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fidEnv_elim_m6SweepCone (fid12_peel_fid_from10 hBase)
    · exact fidEnv_elim_saveTargetBest (fid12_peel_fid_from10 hBase)
    · exact fidEnv_elim_backtrack (fid12_peel_fid_from10 hBase)
    · exact fidEnv_elim_deduce1uipM6 (fid12_peel_fid_from10 hBase)
    · rcases xs with ⟨_, ⟨⟩⟩
      obtain ⟨_, _, _, _, _, _, _, rfl, hcfg, hext, hcut, hlvl, hcf, hm, hQ⟩ :=
        m6Deduce1uipHdrSpec_elim (fidEnv_elim_deduce1uipM6Hdr (fid12_peel_fid_from10 hBase))
      exact FullFidelityStep11.s11Deduce1uipHdrSpec_of hcfg hext hcut hlvl hcf hm hQ
    · exact fidEnv_elim_oneLitConfl (fid12_peel_fid_from10 hBase)
    · exact fidStep7Env_elim_learnClause (fid12_peel_step7_from10 hBase)
    · exact absurd (by decide : "full_viv_collect_fid" ∈ fidStep12Bad) hnb
    · dsimp only [SpecEntry.eff]; simp only [ite_true]
      exact fidEnv_elim_vivSort2Fid (fid12_peel_fid_from10
        (fidStep10Env_noExit _ _ _ _ _ _ _ _ hBase))
    · dsimp only [SpecEntry.eff]; simp only [ite_true]
      exact fidEnv_elim_vivSortFid (fid12_peel_fid_from10
        (fidStep10Env_noExit _ _ _ _ _ _ _ _ hBase))
    · exact fidEnv_elim_vivClauseM6 (fid12_peel_fid_from10 hBase)
  · simp only [fidStep12BReplRows, List.mem_cons, List.not_mem_nil, or_false] at h12b
    rcases h12b with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by decide : "full_cong_extract" ∈ fidStep12Bad) hnb
    · exact absurd (by decide : "full_cong_and_match" ∈ fidStep12Bad) hnb
    · exact absurd (by decide : "full_cong_enq_var" ∈ fidStep12Bad) hnb
    · exact absurd (by decide : "full_cong_eval_gate" ∈ fidStep12Bad) hnb
    · exact absurd (by decide : "full_cong_worklist" ∈ fidStep12Bad) hnb
    · exact fidStep9Env_elim_congruenceDense (fid12_peel_step9_from10 hBase)
    · exact fidEnv_elim_backboneSchedM6 (fid12_peel_fid_from10 hBase)
    · exact fidEnv_elim_backboneM6 (fid12_peel_fid_from10 hBase)
    · exact fidEnv_elim_densePropUnitM7 (fid12_peel_fid_from10 hBase)
    · exact fidEnv_elim_forwardSubM7 (fid12_peel_fid_from10 hBase)
    · exact fidEnv_elim_bveCommitRes (fid12_peel_fid_from10 hBase)
    · exact fidEnv_elim_bveVarM7 (fid12_peel_fid_from10 hBase)
  · simp only [fidStep12CReplRows, List.mem_cons, List.not_mem_nil, or_false] at h12c
    rcases h12c with rfl | rfl | rfl | rfl
    · exact fidEnv_elim_addClause (fid12_peel_fid_from10 hBase)
    · exact fidEnv_elim_sweepCopy (fid12_peel_fid_from10 hBase)
    · exact FullFidelityStep10.step10LearnClauseM6Spec_monoX (fidStep10Env_elim_learnClauseM6 hBase)
    · exact fidEnv_elim_vivSortCountsM6 (fid12_peel_fid_from10 hBase)
  · simp only [fid12Step12AReplRows_eq, FullFidelityStep12A.fidStep12AReplRows, List.take,
      List.mem_cons, List.not_mem_nil, or_false] at h12a
    rcases h12a with rfl | rfl | rfl | rfl | rfl
    · exact fidEnv_elim_transSortM6 (fid12_peel_fid_from10 hBase)
    · exact fidEnv_elim_m6SweepSim (fid12_peel_fid_from10 hBase)
    · exact fidEnv_elim_m6SweepVars (fid12_peel_fid_from10 hBase)
    · exact fidStep9Env_elim_factor (fid12_peel_step9_from10 hBase)
    · exact m6ProbeSpec_monoX (fidStep9Env_elim_probeM6 (fid12_peel_step9_from10 hBase))
  · exfalso
    have hnb10 := List.all_eq_true.mp fid12_before_not_in10 e hbef
    rw [List.contains_iff_mem.mpr he10] at hnb10
    cases hnb10

theorem fidStep12_agree :
    ∀ s ∈ fidStep10Module.sigs, s.1 ∉ fidStep12Bad →
      ∀ xs m P E, Env.ofTable fidStep10BaseSpecTable s.1 s.2.1 s.2.2 xs m P E →
        fidStep12Env s.1 s.2.1 s.2.2 xs m P E := by
  rintro ⟨nm, as, bs⟩ hs hne xs m P E hBase
  cases hf : fidStep12Bundle.frontTable.find? (·.name == nm) with
  | none =>
    change patchEnv fidStep12Bundle nm as bs xs m P E
    rw [patchEnv_base_eq fidStep12Bundle hf]
    exact hBase
  | some e =>
    have he := List.mem_of_find?_eq_some hf
    have hnm : e.name = nm :=
      beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == nm) hf)
    have he10 : e.name ∈ fidStep10FnNames := by
      have hm := hs
      unfold LeanQbe.T.Module.sigs at hm
      rw [fidStep10_externs_empty, List.map_nil, List.append_nil] at hm
      obtain ⟨g, hg, hgs⟩ := List.mem_map.mp hm
      rw [← fidStep10Module_map_name]
      exact hnm ▸ List.mem_map.mpr ⟨g, hg, congrArg Prod.fst hgs⟩
    by_cases hsig : e.as = as ∧ e.rs = bs
    · obtain ⟨has, hrs⟩ := hsig
      subst hnm; subst has; subst hrs
      exact patchEnv_of_front_mem fidStep12Bundle fidStep12_front_nodup he
        (fidStep12_sameSpecs e he he10 hne xs m P E hBase)
    · have hneq : ∀ e' ∈ fidStep12Bundle.frontTable,
          ¬ (e'.name = nm ∧ e'.as = as ∧ e'.rs = bs) := by
        intro e' he' ⟨hnm', has', hrs'⟩
        have heq := nodup_name_eq SpecEntry.name fidStep12_front_nodup he' he
          (hnm'.trans hnm.symm)
        subst heq
        exact hsig ⟨has', hrs'⟩
      have hLift : ∀ (pfx : List SpecEntry),
          (∀ e' ∈ pfx, ¬ (e'.name = nm ∧ e'.as = as ∧ e'.rs = bs)) →
          Env.ofTable (pfx ++ fidStep12Bundle.baseTable) nm as bs xs m P E := by
        intro pfx hpfx
        induction pfx with
        | nil => exact hBase
        | cons x xs' ih =>
          rw [List.cons_append]
          exact Or.inr ⟨hpfx x List.mem_cons_self,
            ih fun y hy => hpfx y (List.mem_cons_of_mem _ hy)⟩
      exact hLift fidStep12Bundle.frontTable hneq

/-! ## 3. Base Callee Spec Intro Wrappers into `fidStep12Env` -/

theorem fid12_ilog10 : ∀ a m Q X, fullIlog10Spec a m Q X →
    fidStep12Env "full_ilog10" [i64] [i64] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_ilog10 a m Q X hs)

theorem fid12_heapDown : ∀ a m Q X, fullHeapDownSpec a m Q X →
    fidStep12Env "full_heap_down" [i64, i32] [] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_heapDown a m Q X hs)

theorem fid12_tickRel : ∀ a m Q X, fullTickRelSpec a m Q X →
    fidStep12Env "full_tick_rel" [i64] [] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_tickRel a m Q X hs)

theorem fid12_log10Q16M7 : ∀ a m Q X, m7Log10Q16Spec a m Q X →
    fidStep12Env "full_log10_q16_m7" [i64] [i64] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_log10Q16M7 a m Q X hs)

theorem fid12_scaleDeltaM5 : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
    fidStep12Env "full_scale_delta_m5" [i64, i64] [i64] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_scaleDeltaM5 a m Q X hs)

theorem fid12_emaUpdate : ∀ a m Q X, fullEmaUpdateSpec a m Q X →
    fidStep12Env "full_ema_update" [i64, i64] [] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_emaUpdate a m Q X hs)

theorem fid12_assignLvl : ∀ a m Q X, fullAssignLvlSpec a m Q X →
    fidStep12Env "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_assignLvl a m Q X hs)

theorem fid12_hdrRecordUsed : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
    fidStep12Env "m6_hdr_record_used" [i64, i64] [] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_hdrRecordUsed a m Q X hs)

theorem fid12_propagate : ∀ a m Q X, fullBcpS15Spec a m Q X →
    fidStep12Env "full_propagate" [i64] [i64] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_propagate a m Q X hs)

theorem fid12_arenaSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
    fidStep12Env "full_arena_sweep" [i64] [i64] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_arenaSweep a m Q X hs)

theorem fid12_analyzeLit : ∀ a m Q X, fullAnalyzeLitSpec a m Q X →
    fidStep12Env "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_analyzeLit a m Q X hs)

theorem fid12_clearAna : ∀ a m Q X, fullClearAnaSpec a m Q X →
    fidStep12Env "full_clear_ana" [i64] [] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_clearAna a m Q X hs)

theorem fid12_bumpAnalyzedM6Hdr :
    ∀ a m Q X, m6aBumpAnalyzedSpecP M6ExtW2bPres a m Q X →
      fidStep12Env "full_bump_analyzed_m6_hdr" [i64] [] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_bumpAnalyzedM6Hdr a m Q X hs)

theorem fid12_restoreBumpAnaM6Hdr :
    ∀ a m Q X, m6aRestoreBumpAnaSpecP M6ExtW2bPres a m Q X →
      fidStep12Env "full_restore_bump_ana_m6_hdr" [i64] [] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_restoreBumpAnaM6Hdr a m Q X hs)

theorem fid12_minMark : ∀ a m Q X, fullMinMarkSpec a m Q X →
    fidStep12Env "full_min_mark" [i64, i32, i8] [] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_minMark a m Q X hs)

theorem fid12_sortTmp : ∀ a m Q X, step7SortTmpSpec a m Q X →
    fidStep12Env "full_sort_tmp" [i64] [] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_sortTmp a m Q X hs)

theorem fid12_minLitDfsM8 : ∀ a m Q X, m8MinLitDfsSpec a m Q X →
    fidStep12Env "full_min_lit_dfs_m8" [i64, i32, .bool, .bool] [.bool] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_minLitDfsM8 a m Q X hs)

theorem fid12_shrinkBlkBoolM8 : ∀ a m Q X, m8ShrinkBlkBoolSpec a m Q X →
    fidStep12Env "full_shrink_blk_bool_m8" [i64, i64, i64, i32, i64] [.bool] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_shrinkBlkBoolM8 a m Q X hs)

theorem fid12_minShrink : ∀ a m Q X, m8MinShrinkSpec a m Q X →
    fidStep12Env "full_min_shrink" [i64] [] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_minShrink a m Q X hs)

theorem fid12_deduce1uip : ∀ a m Q X, fullDeduce1uipSpec a m Q X →
    fidStep12Env "full_deduce_1uip" [i64] [i64] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_deduce1uip a m Q X hs)

theorem fid12_deduce1uipM6Hdr :
    ∀ a m Q X, FullFidelityStep11.s11Deduce1uipHdrSpec a m Q X →
      fidStep12Env "full_deduce_1uip_m6_hdr" [i64] [i64] a m Q X :=
  fid12_frontRow 19 "full_deduce_1uip_m6_hdr" FullFidelityStep11.s11Deduce1uipHdrSpec
    rfl (fun _ _ _ _ h => FullFidelityStep11.s11Deduce1uipHdrSpec_monoX h)

theorem fid12_detNewLevel : ∀ a m Q X, fullDetNewLevelSpec a m Q X →
    fidStep12Env "full_det_new_level" [i64, i64] [i64] a m Q X :=
  fun a m Q X hs => fid12_of_step9 (by decide) (by decide) (fidStep9Env_detNewLevel a m Q X hs)

theorem fid12_restoreBumpAnaM5 : ∀ a m Q X, fullRestoreBumpAnaSpec a m Q X →
    fidStep12Env "full_restore_bump_ana_m5" [i64] [] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_restoreBumpAnaM5 a m Q X hs)

theorem fid12_eagerSubsume : ∀ a m Q X, fullEagerSubsumeSpec a m Q X →
    fidStep12Env "full_eager_subsume" [i64, i64] [] a m Q X :=
  fun a m Q X hs => fid12_of_step9 (by decide) (by decide) (fidStep9Env_eagerSubsume a m Q X hs)

theorem fid12_vivClearTierM6 : ∀ a m Q X, fullVivClearTierM6Spec a m Q X →
    fidStep12Env "full_viv_clear_tier_m6" [i64, i64] [] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_vivClearTierM6 a m Q X hs)

theorem fid12_vivCountFid : ∀ a m Q X, fullVivCountFidSpec a m Q X →
    fidStep12Env "full_viv_count_fid" [i64, i64] [] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_vivCountFid a m Q X hs)

theorem fid12_compactNeeded : ∀ a m Q X, fullCompactNeededSpec a m Q X →
    fidStep12Env "full_compact_needed" [i64] [.bool] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_compactNeeded a m Q X hs)

theorem fid12_compact : ∀ a m Q X, fullCompactSpec a m Q X →
    fidStep12Env "full_compact" [i64] [i64] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_compact a m Q X hs)

theorem fid12_m7Get64 : ∀ a m Q X, m7Get64Spec a m Q X →
    fidStep12Env "full_m7_get64" [i64, i64] [i64] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_m7Get64 a m Q X hs)

theorem fid12_m7Set64 : ∀ a m Q X, m7Set64Spec a m Q X →
    fidStep12Env "full_m7_set64" [i64, i64, i64] [] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_m7Set64 a m Q X hs)

theorem fid12_emaSwapM7 : ∀ a m Q X, m7EmaSwapSpec a m Q X →
    fidStep12Env "full_ema_swap_m7" [i64, i64, i64] [] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_emaSwapM7 a m Q X hs)

theorem fid12_rebuildWatchesNosort : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
    fidStep12Env "full_rebuild_watches_nosort_fid" [i64] [i64] a m Q X :=
  fun a m Q X hs => fid12_of_step10 (by decide) (fidStep10Env_rebuildWatchesNosort a m Q X hs)

theorem fid12_wstackDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
    fidStep12Env "full_wstack_defrag" [i64] [] a m Q X :=
  fun a m Q X hs => fid12_of_step9 (by decide) (by decide) (fidStep9Env_wstackDefrag a m Q X hs)

theorem fid12_reduceM6 : ∀ a m Q X, m6ReduceSpec a m Q X →
    fidStep12Env "full_reduce_m6" [i64, .bool] [i64] a m Q X :=
  fun a m Q X hs => fid12_of_step9 (by decide) (by decide) (fidStep9Env_reduceM6 a m Q X hs)

theorem fid12_bvaUpdLitFid : ∀ a m Q X, step9BvaUpdLitSpec a m Q X →
    fidStep12Env "full_bva_upd_lit_fid" [i64, i64, i64, i64, i64, i64] [i32] a m Q X :=
  fun a m Q X hs => fid12_of_step9 (by decide) (by decide) (fidStep9Env_bvaUpdLitFid a m Q X hs)

theorem fid12_bvaStepsCap : ∀ a m Q X, fidBvaStepsCapSpec a m Q X →
    fidStep12Env "full_bva_steps_cap_fid" [i64] [i32] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_bvaStepsCap a m Q X hs)

theorem fid12_addBin : ∀ a m Q X, fullAddBinSpec a m Q X →
    fidStep12Env "full_add_bin" [i64, i32, i32] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_addBin a m Q X hs)

theorem fid12_allocCl : ∀ a m Q X, fullAllocClSpec a m Q X →
    fidStep12Env "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_allocCl a m Q X hs)

theorem fid12_watchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
    fidStep12Env "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_watchPush a m Q X hs)

theorem fid12_deleteBinary : ∀ a m Q X, fullDeleteBinarySpec a m Q X →
    fidStep12Env "full_delete_binary" [i64, i32, i32] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_deleteBinary a m Q X hs)

theorem fid12_unwatchLarge : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
    fidStep12Env "full_unwatch_large" [i64, i32, i32] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_unwatchLarge a m Q X hs)

theorem fid12_arenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
    fidStep12Env "full_arena_next" [i64, i32] [i32] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_arenaNext a m Q X hs)

theorem fid12_markReasons : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
    fidStep12Env "full_mark_reasons" [i64, .bool] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_markReasons a m Q X hs)

theorem fid12_probeDticksM6Hdr : ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
    fidStep12Env "full_probe_dticks_m6_hdr" [i64, .bool] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_probeDticksM6Hdr a m Q X hs)

theorem fid12_hdrDelaying : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
    fidStep12Env "m6_hdr_delaying" [i64, i64] [.bool] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_hdrDelaying a m Q X hs)

theorem fid12_hdrReduceDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
    fidStep12Env "m6_hdr_reduce_delay" [i64, i64] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_hdrReduceDelay a m Q X hs)

theorem fid12_hdrBumpDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
    fidStep12Env "m6_hdr_bump_delay" [i64, i64] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_hdrBumpDelay a m Q X hs)

theorem fid12_hdrGetWatermark : ∀ a m Q X, m6HdrW2aSpec [i64] [i64] a m Q X →
    fidStep12Env "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_hdrGetWatermark a m Q X hs)

theorem fid12_hdrSetWatermark : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
    fidStep12Env "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_hdrSetWatermark a m Q X hs)

theorem fid12_congExtractBinaries : ∀ a m Q X, m6CongExtractBinariesSpec a m Q X →
    fidStep12Env "full_cong_extract_binaries" [i64, i64] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_congExtractBinaries a m Q X hs)

theorem fid12_congFindUnitsEquivs : ∀ a m Q X, m6CongFindUnitsEquivsSpec a m Q X →
    fidStep12Env "full_cong_find_units_equivs" [i64] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_congFindUnitsEquivs a m Q X hs)

theorem fid12_congFwdSubsume : ∀ a m Q X, m6CongFwdSubsumeSpec a m Q X →
    fidStep12Env "full_cong_fwd_subsume" [i64, i64] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_congFwdSubsume a m Q X hs)

theorem fid12_congExtractIteAll : ∀ a m Q X, fidCongExtractIteAllSpec a m Q X →
    fidStep12Env "full_cong_extract_ite_all_m7" [i64, i32, i32, i64] [i32] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_congExtractIteAll a m Q X hs)

theorem fid12_sweepDenseM6 : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
    fidStep12Env "full_sweep_dense_m6" [i64, i64, i64] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_sweepDenseM6 a m Q X hs)

theorem fid12_sortBinWatches : ∀ a m Q X, step7SortBinWatchesSpec a m Q X →
    fidStep12Env "full_sort_bin_watches_fid" [i64] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_sortBinWatches a m Q X hs)

theorem fid12_vivifyM6Hdr : ∀ a m Q X, m6aVivifySpec a m Q X →
    fidStep12Env "full_vivify_m6_hdr" [i64] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_vivifyM6Hdr a m Q X hs)

theorem fid12_bvaTryLit : ∀ a m Q X, step7BvaTryLitSpec a m Q X →
    fidStep12Env "full_bva_try_lit" [i64, i32, i64] [.bool] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_bvaTryLit a m Q X hs)

theorem fid12_fheapUp : ∀ a m Q X, fidFheapUpSpec a m Q X →
    fidStep12Env "full_fheap_up_fid" [i64, i64, i64, i32] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_fheapUp a m Q X hs)

theorem fid12_fheapDown : ∀ a m Q X, fidFheapDownSpec a m Q X →
    fidStep12Env "full_fheap_down_fid" [i64, i64, i64, i32, i32] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_fheapDown a m Q X hs)

theorem fid12_bvaConnectClauses : ∀ a m Q X, fidBvaConnectClausesSpec a m Q X →
    fidStep12Env "full_bva_connect_clauses_fid" [i64] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_bvaConnectClauses a m Q X hs)

theorem fid12_enterDense : ∀ a m Q X, schedEnterDenseSpec a m Q X →
    fidStep12Env "full_enter_dense" [i64] [.bool] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_enterDense a m Q X hs)

theorem fid12_transitiveM6 : ∀ a m Q X, fullTransitiveFastSpec a m Q X →
    fidStep12Env "full_transitive_m6" [i64, i64] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_transitiveM6 a m Q X hs)

theorem fid12_substitute : ∀ a m Q X, fullSubstituteSpec a m Q X →
    fidStep12Env "full_substitute" [i64] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step8 (by decide) (by decide) (by decide) (fidStep8Env_substitute a m Q X hs)

theorem fid12_reduce : ∀ a m Q X, fullReduceSpec a m Q X →
    fidStep12Env "full_reduce" [i64, .bool] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_step7 (by decide) (by decide) (by decide) (by decide)
      (fidStep7Env_reduce a m Q X hs)

theorem fid12_bveGatesFid : ∀ a m Q X, m8BveGatesSpec a m Q X →
    fidStep12Env "full_bve_gates_fid" [i64, i32, i32, i32] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_bveGatesFid a m Q X hs)

theorem fid12_congExtractXorK : ∀ a m Q X, fidCongExtractXorKSpec a m Q X →
    fidStep12Env "full_cong_extract_xor_k" [i64, i32, i32, i64, i64] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_congExtractXorK a m Q X hs)

theorem fid12_congTryXorIte : ∀ a m Q X, fidCongTryXorIteSpec a m Q X →
    fidStep12Env "full_cong_try_xor_ite" [i64, i32, i32, i32, i64, i64] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_congTryXorIte a m Q X hs)

theorem fid12_luckyLateCanon : ∀ a m Q X, fullLuckySpec a m Q X →
    fidStep12Env "full_lucky_late_m7" [i64] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_luckyLateM7 a m Q X (m7LuckyLateSpec_to_canon hs))

theorem fid12_propagateIgnore : ∀ a m Q X, fullPropagateIgnoreS15Spec a m Q X →
    fidStep12Env "full_propagate_ignore" [i64, i64] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_propagateIgnore a m Q X hs)

theorem fid12_m6CollectCands : ∀ a m Q X, m6CollectCandsSpec a m Q X →
    fidStep12Env "full_m6_collect_cands" [i64] [i32] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_m6CollectCands a m Q X hs)

theorem fid12_m6MaxV : ∀ a m Q X, m6MaxVSpec a m Q X →
    fidStep12Env "full_m6_max_v" [i64] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_m6MaxV a m Q X hs)

theorem fid12_k6Init : ∀ a m Q X, k6InitSpec a m Q X →
    fidStep12Env "full_k6_init" [i64, i32] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_k6Init a m Q X hs)

theorem fid12_k6AddClause : ∀ a m Q X, k6AddClauseSpec a m Q X →
    fidStep12Env "full_k6_add_clause" [i64, i64, i32] [.bool] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_k6AddClause a m Q X hs)

theorem fid12_m6DenseProp : ∀ a m Q X, m6DensePropSpec a m Q X →
    fidStep12Env "full_m6_dense_prop" [i64] [.bool] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_m6DenseProp a m Q X hs)

theorem fid12_m6SweepRefineSig : ∀ a m Q X, m6SweepRefineSigSpec a m Q X →
    fidStep12Env "full_m6_sweep_refine_sig" [i64, i32, i32] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_m6SweepRefineSig a m Q X hs)

theorem fid12_m6SweepSolve : ∀ a m Q X, m6SweepSolveSpec a m Q X →
    fidStep12Env "full_m6_sweep_solve" [i64, i32, i64] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_m6SweepSolve a m Q X hs)

theorem fid12_m6SweepFlipRound : ∀ a m Q X, m6SweepFlipRoundSpec a m Q X →
    fidStep12Env "full_m6_sweep_flip_round" [i64, i32] [i32] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_m6SweepFlipRound a m Q X hs)

theorem fid12_m6SweepVar : ∀ a m Q X, m6SweepVarSpec a m Q X →
    fidStep12Env "full_m6_sweep_var" [i64, i32, i64] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_m6SweepVar a m Q X hs)

theorem fid12_vivBestImpliedM6 : ∀ a m Q X, fullVivBestImpliedM6Spec a m Q X →
    fidStep12Env "full_viv_best_implied_m6" [i64, i32] [i32] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_vivBestImpliedM6 a m Q X hs)

theorem fid12_vivFinishM6 : ∀ a m Q X, fullVivFinishM6Spec a m Q X →
    fidStep12Env "full_viv_finish_m6" [i64, i32, i32, .bool, i32, .bool] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_vivFinishM6 a m Q X hs)

theorem fid12_vivL0SimpM6 : ∀ a m Q X, fullVivL0SimpM6Spec a m Q X →
    fidStep12Env "full_viv_l0_simp_m6" [i64, i32, i32] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_vivL0SimpM6 a m Q X hs)

theorem fid12_vivReusePrefixM6 : ∀ a m Q X, fullVivReusePrefixM6Spec a m Q X →
    fidStep12Env "full_viv_reuse_prefix_m6" [i64, i32, i32] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_vivReusePrefixM6 a m Q X hs)

theorem fid12_vivTierMatchM6 : ∀ a m Q X, fullVivTierMatchM6Spec a m Q X →
    fidStep12Env "full_viv_tier_match_m6" [i64, i32, i64] [.bool] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_vivTierMatchM6 a m Q X hs)

theorem fid12_kissatSkipWsComments : ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
    fidStep12Env "kissat_skip_ws_comments" [i64, i64] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_kissatSkipWsComments a m Q X hs)

theorem fid12_kissatNextLit : ∀ a m Q X, kissatNextLitSpec a m Q X →
    fidStep12Env "kissat_next_lit" [i64, i64] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_kissatNextLit a m Q X hs)

theorem fid12_heapPush : ∀ a m Q X, fullHeapPushSpec a m Q X →
    fidStep12Env "full_heap_push" [i64, i32] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_heapPush a m Q X hs)

theorem fid12_assign : ∀ a m Q X, fullAssignSpec a m Q X →
    fidStep12Env "full_assign" [i64, i32, i32] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_assign a m Q X hs)

theorem fid12_backtrackRawM5 : ∀ a m Q X, fullBacktrackRawSpec a m Q X →
    fidStep12Env "full_backtrack_raw_m5" [i64, i64] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_backtrackRawM5 a m Q X hs)

theorem fid12_skipCl : ∀ a m Q X, fullSkipClSpec a m Q X →
    fidStep12Env "full_skip_cl" [i64, i64] [.bool] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_skipCl a m Q X hs)

theorem fid12_analyzeRsn : ∀ a m Q X, fullAnalyzeRsnSpec a m Q X →
    fidStep12Env "full_analyze_rsn" [i64, i32, i32] [.bool] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_analyzeRsn a m Q X hs)

theorem fid12_otfsLarge : ∀ a m Q X, fullOtfsLargeSpec a m Q X →
    fidStep12Env "full_otfs_large" [i64, i32, i32] [.bool] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_otfsLarge a m Q X hs)

theorem fid12_otfsBin : ∀ a m Q X, fullOtfsBinSpec a m Q X →
    fidStep12Env "full_otfs_bin" [i64, i32, i32] [.bool] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_otfsBin a m Q X hs)

theorem fid12_otfsSubsume : ∀ a m Q X, fullOtfsSubsumeSpec a m Q X →
    fidStep12Env "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_otfsSubsume a m Q X hs)

theorem fid12_setInactive : ∀ a m Q X, fullSetInactiveSpec a m Q X →
    fidStep12Env "full_set_inactive" [i64, i32, i32] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_setInactive a m Q X hs)

theorem fid12_addUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
    fidStep12Env "full_add_unit" [i64, i32] [.bool] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_addUnit a m Q X hs)

theorem fid12_prioritizeBinariesM6 : ∀ a m Q X, fullPrioritizeBinariesM6Spec a m Q X →
    fidStep12Env "full_prioritize_binaries_m6" [i64] [.bool] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_prioritizeBinariesM6 a m Q X hs)

theorem fid12_backboneKeepM6 : ∀ a m Q X, fullBackboneKeepM6Spec a m Q X →
    fidStep12Env "full_backbone_keep_m6" [i64, i64] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_backboneKeepM6 a m Q X hs)

theorem fid12_backboneRoundM6 : ∀ a m Q X, fullBackboneRoundM6Spec a m Q X →
    fidStep12Env "full_backbone_round_m6" [i64, i64, .bool] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_backboneRoundM6 a m Q X hs)

theorem fid12_congFind : ∀ a m Q X, fullCongFindSpec a m Q X →
    fidStep12Env "full_cong_find" [i64, i32] [i32] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_congFind a m Q X hs)

theorem fid12_congUnitFold : ∀ a m Q X, m3CongUnitFoldSpec a m Q X →
    fidStep12Env "full_cong_unit_fold" [i64, i32, i32] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_congUnitFold a m Q X hs)

theorem fid12_congEquivFold : ∀ a m Q X, m3CongEquivFoldSpec a m Q X →
    fidStep12Env "full_cong_equiv_fold" [i64, i32, i32, i32] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_congEquivFold a m Q X hs)

theorem fid12_sortU32 : ∀ a m Q X, fullSortU32Spec a m Q X →
    fidStep12Env "full_sort_u32" [i64, i32] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_sortU32 a m Q X hs)

theorem fid12_congCountBins : ∀ a m Q X, m6CongCountBinsSpec a m Q X →
    fidStep12Env "full_cong_count_bins" [i64] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_congCountBins a m Q X hs)

theorem fid12_congXorMatch : ∀ a m Q X, m6CongXorMatchSpec a m Q X →
    fidStep12Env "full_cong_xor_match" [i64, i32, i32] [i32] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_congXorMatch a m Q X hs)

theorem fid12_fwdDedupBins : ∀ a m Q X, fullFwdDedupBinsSpec a m Q X →
    fidStep12Env "full_fwd_dedup_bins" [i64] [.bool] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_fwdDedupBins a m Q X hs)

theorem fid12_denseFlushUnitsM7 : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
    fidStep12Env "full_dense_flush_units_m7" [i64] [.bool] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_denseFlushUnitsM7 a m Q X hs)

theorem fid12_fwdFlushLargeM7 : ∀ a m Q X, fullFwdFlushLargeM6Spec a m Q X →
    fidStep12Env "full_fwd_flush_large_m7" [i64] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_fwdFlushLargeM7 a m Q X hs)

theorem fid12_fwdReconnectIrredM7 : ∀ a m Q X, fullFwdReconnectIrredM6Spec a m Q X →
    fidStep12Env "full_fwd_reconnect_irred_m7" [i64] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_fwdReconnectIrredM7 a m Q X hs)

theorem fid12_fwdCheckClM7 : ∀ a m Q X, fullFwdCheckClM7Spec a m Q X →
    fidStep12Env "full_fwd_check_cl_m7" [i64, i32] [.bool] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_fwdCheckClM7 a m Q X hs)

theorem fid12_fwdConnectSubsumerM7 : ∀ a m Q X, fullFwdConnectSubsumerM6Spec a m Q X →
    fidStep12Env "full_fwd_connect_subsumer_m7" [i64, i32] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_fwdConnectSubsumerM7 a m Q X hs)

theorem fid12_fwdCollectSortM7 : ∀ a m Q X, fullFwdCollectSortM6Spec a m Q X →
    fidStep12Env "full_fwd_collect_sort_m7" [i64] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_fwdCollectSortM7 a m Q X hs)

theorem fid12_bveCollectM7 : ∀ a m Q X, fullBveCollectSpec a m Q X →
    fidStep12Env "full_bve_collect_m7" [i64, i32, i64, i32] [i32] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_bveCollectM7 a m Q X hs)

theorem fid12_bveGatesM7 : ∀ a m Q X, fullBveGatesM7Spec a m Q X →
    fidStep12Env "full_bve_gates_m7" [i64, i32, i32, i32] [] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_bveGatesM7 a m Q X hs)

theorem fid12_bveResolvePair : ∀ a m Q X, fullBveResolvePairSpec a m Q X →
    fidStep12Env "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_bveResolvePair a m Q X hs)

theorem fid12_bveWeaken : ∀ a m Q X, fullBveWeakenTmkSpec a m Q X →
    fidStep12Env "full_bve_weaken" [i64, i32, i32, i32] [.bool] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_bveWeaken a m Q X hs)

theorem fid12_bveExtNeed : ∀ a m Q X, fullBveExtNeedSpec a m Q X →
    fidStep12Env "full_bve_ext_need" [i64, i32, i32] [i64] a m Q X :=
  fun a m Q X hs =>
    fid12_of_fid (by decide) (by decide) (by decide) (by decide) (by decide)
      (fidEnv_bveExtNeed a m Q X hs)

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12

end
