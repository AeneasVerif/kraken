module

public import LeanQbe.T.Examples.Kissat.FullM4Bump
public import LeanQbe.T.Examples.Kissat.FullSpec2
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
public import LeanQbe.T.Logic.C0Agrees
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat M4g `Func.wp`, `ModuleOk`, and Concrete `Mem 64` UNSAT Non-Vacuity (`FullM4BumpProof`)

Proves UNSAT-only safety (`XPost := False`, `0` SAT proofs) for `FullM4Bump.full_bump_var_m4`:
1. Parametric `full_bump_var_m4_wp` against the exact canonical `Full.fullBumpVarSpec` given
   `Full.fullHeapUpSpec` and `Full.fullRescaleSpec`.
2. Closed `3`-row `m4BumpSpecTable`, `m4BumpEnv`, and `m4Bump_moduleOk : ModuleOk m4BumpEnv
   m4BumpModule`.
3. Concrete `Mem 64` UNSAT non-vacuity (`nv_m4_bump_var`, `XPost := False`) on `nvOneLitCfg` /
   `nvOneLitState` / `nvOneLitMem` (`v = 0#32`, `stable = 0#64`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4Bump

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Parametric `Func.wp` Proof (`Full.fullBumpVarSpec`) -/

section BumpVarProof

open scoped FullArenaTactics

private theorem m4_bv32_setWidth64_toNat (x : BitVec 32) :
    (BitVec.setWidth 64 x).toNat = x.toNat :=
  zext_toNat x (by decide)

attribute [local bv_c0] List.length_set m4_bv32_setWidth64_toNat

private theorem m4_probePres_refl (s : FullState) : FullProbeScratchPres s s :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem m4_probePres_trans {s1 s2 s3 : FullState}
    (h12 : FullProbeScratchPres s1 s2) (h23 : FullProbeScratchPres s2 s3) :
    FullProbeScratchPres s1 s3 :=
  ⟨⟨h23.1.1.trans h12.1.1, h23.1.2.trans h12.1.2⟩,
    h23.2.1.trans h12.2.1, h23.2.2.1.trans h12.2.2.1, h23.2.2.2.1.trans h12.2.2.2.1,
    h23.2.2.2.2.1.trans h12.2.2.2.2.1, h23.2.2.2.2.2.1.trans h12.2.2.2.2.2.1,
    h23.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.1, h23.2.2.2.2.2.2.2.trans h12.2.2.2.2.2.2.2⟩

private theorem m4_hlen_upd_score {c : FullCfg} {s : FullState}
    (hlen : FullState.LengthsOk c s) (sc' : List (BitVec 64)) (hs : sc'.length = c.max_vars) :
    FullState.LengthsOk c { core := s.core, scratch := { s.scratch with score := sc' } } :=
  hlen.with_scratch { hlen.scratch_ok with score_len := hs }

/-- Mode-guarded `full_bump_var_m4` satisfies canonical `Full.fullBumpVarSpec` parametrically in
`Γ`. -/
theorem full_bump_var_m4_wp (Γ : Env)
    (hUp : ∀ a m Q X, fullHeapUpSpec a m Q X → Γ "full_heap_up" [i64, i32] [] a m Q X)
    (hRes : ∀ a m Q X, fullRescaleSpec a m Q X → Γ "full_rescale" [i64] [] a m Q X) :
    ∀ a m Q X, fullBumpVarSpec a m Q X → Func.wp Γ full_bump_var_m4_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le; obtain hsl := hsok.score_len
  c0_steps
  · exact hQ () s m rfl hlen (m4_probePres_refl s) hm
  all_goals first
  | (refine wp_safety_slice_call hUp (fun _ => True) trivial rfl ?_ hm
       fun _ s1 m1 hcore1 hlen1 _ hpres1 hm1 => ?_
     · exact m4_hlen_upd_score hlen _ (by simp [hsl])
     · dsimp only [fullSafetySlice] at hm1 hlen1
       c0_steps
       all_goals first
       | (refine wp_safety_slice_call hRes (fun _ => True) trivial rfl hlen1 hm1
            fun _ s2 m2 hcore2 hlen2 _ hpres2 hm2 => ?_
          dsimp only [fullSafetySlice] at hm2 hlen2
          c0_steps
          exact hQ () s2 m2 (hcore1.trans hcore2) hlen2
            (m4_probePres_trans hpres1.1 hpres2) hm2)
       | exact hQ () s1 m1 hcore1 hlen1 hpres1.1 hm1)
  | (refine wp_safety_slice_call hRes (fun _ => True) trivial rfl ?_ hm
       fun _ s2 m2 hcore2 hlen2 _ hpres2 hm2 => ?_
     · exact m4_hlen_upd_score hlen _ (by simp [hsl])
     · dsimp only [fullSafetySlice] at hm2 hlen2
       c0_steps
       exact hQ () s2 m2 hcore2 hlen2 hpres2 hm2)
  | (refine hQ () _ m ?_ ?_ ?_ hm
     · exact rfl
     · exact m4_hlen_upd_score hlen _ (by simp [hsl])
     · exact ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

end BumpVarProof

/-! ## 2. Closed `3`-Row `m4BumpSpecTable`, `m4BumpEnv`, and `ModuleOk` -/

section ModuleOkSection

/-- Closed `3`-row `m4BumpSpecTable` (`full_bump_var_m4` + `2` external callees, all `noExit`). -/
def m4BumpSpecTable : List SpecEntry :=
  [ ⟨"full_bump_var_m4", [i64, i32], [], fullBumpVarSpec, true⟩
  , ⟨"full_heap_up", [i64, i32], [], fullHeapUpSpec, true⟩
  , ⟨"full_rescale", [i64], [], fullRescaleSpec, true⟩ ]

theorem m4BumpSpecTable_nodup : (m4BumpSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem m4BumpSpecTable_noExit : ∀ e ∈ m4BumpSpecTable, e.noExit = true := by
  intro e he
  simp only [m4BumpSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> rfl

/-- Closed environment for `m4BumpModule`. -/
def m4BumpEnv : Env := Env.ofTable m4BumpSpecTable

theorem m4BumpEnv_noExit :
    ∀ f as bs xs m Q X X', m4BumpEnv f as bs xs m Q X → m4BumpEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m4BumpSpecTable_noExit

private theorem m4BumpEnv_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m4BumpSpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → m4BumpEnv nm as bs xs m Q X :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) hmem m4BumpSpecTable_nodup (hno xs m Q X hs)

theorem m4Bump_var_impl :
    SpecEntry.Impl m4BumpEnv
      ⟨"full_bump_var_m4", [i64, i32], [], full_bump_var_m4_body⟩
      ⟨"full_bump_var_m4", [i64, i32], [], fullBumpVarSpec, true⟩ :=
  SpecEntry.Impl.of (full_bump_var_m4_wp m4BumpEnv
    (m4BumpEnv_row (by simp [m4BumpSpecTable]) (fun _ _ _ _ h => h))
    (m4BumpEnv_row (by simp [m4BumpSpecTable]) (fun _ _ _ _ h => h)))

theorem m4Bump_allFns_wf : AllFns Fn.Wf m4BumpModule.fns :=
  ⟨full_bump_var_m4_wf, trivial⟩

theorem m4Bump_tableImpl : TableImpl m4BumpEnv m4BumpModule.fns m4BumpSpecTable :=
  ⟨m4Bump_var_impl, trivial⟩

/-- Headline `ModuleOk` certifying `m4BumpModule` under `m4BumpEnv` (`0` `sorry`). -/
theorem m4Bump_moduleOk : ModuleOk m4BumpEnv m4BumpModule :=
  Env.ofTable_moduleOk m4Bump_acyclic m4Bump_allFns_wf m4Bump_tableImpl

end ModuleOkSection

/-! ## 3. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

section ConcreteNonVacuity

private theorem nvM4BumpF0_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [nvOneLitF0, cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [nvOneLitF0, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bump_var_m4` on
`nvOneLitCfg` (`v = 0#32 < cur_vars = 1`, `stable = 0#64` focused fast path). -/
theorem nv_m4_bump_var :
    Func.wp m4BumpEnv full_bump_var_m4_body (nvOneLitCfg.hdr, 0#32, ()) nvOneLitMem
      (fun () m' => ∃ s',
        PreservesCoreSlice FullState.core nvOneLitState s' ∧
        s'.LengthsOk nvOneLitCfg ∧ FullProbeScratchPres nvOneLitState s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact m4Bump_var_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitState, emp, rfl, nvOneLit_lengths, hm, fun () s' m' hco hln hpr hm' => by
      rw [sep_emp] at hm'; exact ⟨s', hco, hln, hpr, nvM4BumpF0_unsat, hm'⟩⟩

end ConcreteNonVacuity

end LeanQbe.T.Examples.Kissat.FullM4Bump
