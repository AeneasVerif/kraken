module

public import LeanQbe.T.Examples.Kissat.FullM5KittenDefFixProof1
public import LeanQbe.T.Examples.Kissat.FullM5KittenDefFixProof2
public import LeanQbe.T.Examples.Kissat.FullM5KittenDefFixProof3
public import LeanQbe.T.Examples.Kissat.FullKittenLemmas
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas
public import LeanQbe.T.Examples.Kissat.FullFastAdapters

/-!
# Kissat `M5` Kitten & Gate-Definition Assembly + UNSAT Non-Vacuity

1. Concrete `KittenInvLawsM5` instances for `FullFast.fastKInv` (`fastKInv_laws_m5`) and
   `FullDefSweep.defSweepKInv` (`defSweepKInv_laws_m5`).
2. Closed `13`-row `m5KittenDefFixSpecTable` (`6` owned `_m5` functions + `7` canonical
   `FullKitten` externs), `m5KittenDefFixEnv`, signature/no-exit lemmas, `SpecEntry.Impl`
   witnesses for all `6/6` owned functions (wiring `full_find_definition_m5` to the real
   `FullKitten` specs of `full_kitten_{add_clause,solve,core}_m5` via `FullFast.fastKInv`),
   and unconditional `m5KittenDefFix_moduleOk : ModuleOk m5KittenDefFixEnv m5KittenDefFixModule`.
3. Concrete `Mem 64` UNSAT non-vacuity (`XPost := fun _ _ _ _ => False`, `0` SAT proofs) for
   all `6` owned functions plus the `r = 20#64` UNSAT solve witness.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5KittenDefFix

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

open scoped KittenMemTactics KittenMemATactics KittenProjTactics FullDefSweep.FullDefSweepTactics

/-! ## 1. `KittenInvLawsM5` Instances (`fastKInv` & `defSweepKInv`) -/

private theorem ks_getElem_slice_m5 (scr : List (BitVec 32)) (off len i : Nat) (hi : i < len) :
    (((scr.drop 256).drop off).take len)[i]? = scr[256 + off + i]? := by
  rw [List.getElem?_take_of_lt hi, List.getElem?_drop, List.getElem?_drop, Nat.add_assoc]

private theorem kittenState_vmtf_eq {scr : List (BitVec 32)} {nv' : Nat}
    (h1 : 1 ≤ nv') (hnv' : nv' ≤ 128) :
    let scr' := (((scr.set 267 (BitVec.ofNat 32 (nv' - 1))).set
      268 (BitVec.ofNat 32 (nv' - 1))).set 269 (BitVec.ofNat 32 nv')).set
      (256 + 416 + (nv' - 1)) 0xFFFFFFFF#32
    kittenStateOfScratch scr' =
      { kittenStateOfScratch scr with
        qlast := (scr'.drop 256)[11]?.getD 0#32
        qsearch := (scr'.drop 256)[12]?.getD 0#32
        qstamp := (scr'.drop 256)[13]?.getD 0#32
        qnext := ((scr'.drop 256).drop 416).take 128 } := by
  intro scr'
  have hpres : ∀ i, i ≠ 267 → i ≠ 268 → i ≠ 269 → i ≠ 256 + 416 + (nv' - 1) →
      scr'[i]? = scr[i]? := by
    intro i h11 h12 h13 hqn
    simp only [scr']
    rw [List.getElem?_set_ne (Ne.symm hqn), List.getElem?_set_ne (Ne.symm h13),
      List.getElem?_set_ne (Ne.symm h12), List.getElem?_set_ne (Ne.symm h11)]
  have hne : ∀ j, j ≠ 11 → j ≠ 12 → j ≠ 13 → j < 25 →
      (scr'.drop 256)[j]?.getD 0#32 = (scr.drop 256)[j]?.getD 0#32 := by
    intro j h11 h12 h13 hj
    simp only [List.getElem?_drop]
    rw [hpres _ (by omega) (by omega) (by omega) (by omega)]
  have hslice : ∀ a b, (a + b ≤ 416 ∨ 544 ≤ a) → 25 ≤ a →
      ((scr'.drop 256).drop a).take b = ((scr.drop 256).drop a).take b := by
    intro a b hdisj ha
    apply List.ext_getElem?; intro k
    by_cases hk : k < b
    · rw [ks_getElem_slice_m5 _ _ _ _ hk, ks_getElem_slice_m5 _ _ _ _ hk]
      exact hpres _ (by omega) (by omega) (by omega) (by omega)
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have harena : (scr'.drop 256).drop 8608 = (scr.drop 256).drop 8608 := by
    apply List.ext_getElem?; intro k
    simp only [List.getElem?_drop]
    exact hpres _ (by omega) (by omega) (by omega) (by omega)
  dsimp only [kittenStateOfScratch, KittenState.ofSlab]
  congr 1
  all_goals first
    | rfl
    | exact hne _ (by decide) (by decide) (by decide) (by decide)
    | exact hslice _ _ (by omega) (by decide)
    | exact harena

/-- `FullFast.fastKInv` satisfies `KittenInvLawsM5` (including the 4 VMTF queue-repair writes). -/
theorem fastKInv_laws_m5 : KittenInvLawsM5 FullFast.fastKInv where
  toKittenInvLaws := FullFast.fastKInv_laws
  set_nv_vmtf {nv nv' cls ta scr} h h1 hnv' hna hlt := by
    have h0 := FullFast.fastKInv_laws.set_nv h h1 hnv' hna hlt
    let scr0 := (scr.set 256 (BitVec.ofNat 32 nv')).set 262 (BitVec.ofNat 32 nv')
    let scr' := (((scr0.set 267 (BitVec.ofNat 32 (nv' - 1))).set
      268 (BitVec.ofNat 32 (nv' - 1))).set 269 (BitVec.ofNat 32 nv')).set
      (256 + 416 + (nv' - 1)) 0xFFFFFFFF#32
    rcases h0 with ⟨⟨hlen1, hlen2, hinv0⟩, h1', h128', hnv_eq, hcl512, honc, haux, hperm,
      hlt_cls, hante, hna_le, hfresh, huns⟩
    have hlen' : scr'.length = scr0.length := by simp [scr']
    have hks' := kittenState_vmtf_eq (scr := scr0) h1 h128'
    have hinv' : (kittenStateOfScratch scr').Inv (scr'.length - 8864) := by
      rw [hks', hlen']
      have hlen0 : kMinScratchCap ≤ scr0.length := hlen1
      have hsh' : ({ kittenStateOfScratch scr0 with
            qlast := (scr'.drop 256)[11]?.getD 0#32
            qsearch := (scr'.drop 256)[12]?.getD 0#32
            qstamp := (scr'.drop 256)[13]?.getD 0#32
            qnext := ((scr'.drop 256).drop 416).take 128 } : KittenState).ShapesOk
          (scr0.length - 8864) :=
        { hinv0.shapes with
          qnext_len := by
            rw [List.length_take, List.length_drop, List.length_drop, hlen']
            unfold kMinScratchCap at hlen0; omega }
      refine ⟨hsh', { hinv0.clauses with }, ?_, { hinv0.assign with },
        fun i hi => hinv0.reasons i hi⟩
      rcases hinv0.watches with ⟨ws, hw1, hw2, hw3, hw4⟩
      exact ⟨ws, hw1, hw2, hw3, hw4⟩
    refine ⟨⟨hlen'.symm ▸ hlen1, hlen'.symm ▸ hlen2, hinv'⟩, h1', h128',
      by rw [hks']; exact hnv_eq, hcl512, by rw [hks']; exact honc,
      fun i hi => by rw [hks']; exact haux i hi,
      by rw [hks']; exact hperm, hlt_cls,
      by rw [hks']; exact hante, by rw [hks']; exact hna_le,
      fun hf => by rw [hks']; exact hfresh hf, fun hc => by cases hc⟩

/-- `FullDefSweep.defSweepKInv` satisfies `KittenInvLawsM5`. -/
theorem defSweepKInv_laws_m5 : KittenInvLawsM5 FullDefSweep.defSweepKInv where
  toKittenInvLaws := FullDefSweep.defSweepKInv_laws
  set_nv_vmtf {nv nv' cls ta scr} h h1 hnv' hna hlt := by
    have h0 := FullDefSweep.defSweepKInv_laws.set_nv h h1 hnv' hna hlt
    rcases h0 with ⟨hlen, h1', h128', hcl, honc, haux, hlts, hna_le, hass⟩
    have hqn_lt : 256 + 416 + (nv' - 1) < 800 := by omega
    refine ⟨by simpa using hlen, h1', h128', hcl, ?_, ?_, hlts, ?_, ?_⟩
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by decide),
        List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide)]
      exact honc
    · intro i hi
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact haux i hi
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by decide),
        List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide)]
      exact hna_le
    · intro i hi
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by decide),
        List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide)] at hi
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hass i hi

/-! ## 2. Closed `13`-Row Spec Table, `m5KittenDefFixEnv`, & `ModuleOk` -/

/-- `13`-row specification table: `6` owned M5 functions + `7` canonical `FullKitten` externs. -/
def m5KittenDefFixSpecTable : List SpecEntry :=
  [ ⟨"full_kitten_add_clause_m5", [i64, i32, i64, i32], [.bool], fullKittenAddClauseSpec, true⟩
  , ⟨"full_kitten_ana_clause_m5", [i64, i32, i32], [], fullKittenAnaClauseM5Spec, true⟩
  , ⟨"full_kitten_build_failing_m5", [i64, i32], [], fullKittenBuildFailingSpec, true⟩
  , ⟨"full_kitten_solve_m5", [i64, i64], [i64], fullKittenSolveSpec, true⟩
  , ⟨"full_kitten_core_m5", [i64], [i32], fullKittenCoreSpec, true⟩
  , ⟨"full_find_definition_m5", [i64, i32, i32, i32], [],
      FullDefSweep.fullFindDefinitionSpec, true⟩
  , ⟨"full_kitten_init", [i64, i32, i32], [], fullKittenInitSpec, true⟩
  , ⟨"full_kitten_watch", [i64, i32, i32, i32], [], fullKittenWatchSpec, true⟩
  , ⟨"full_kitten_assign", [i64, i32, i32], [], fullKittenAssignSpec, true⟩
  , ⟨"full_kitten_backtrack", [i64, i32], [], fullKittenBacktrackSpec, true⟩
  , ⟨"full_kitten_propagate", [i64], [i32], fullKittenPropagateSpec, true⟩
  , ⟨"full_kitten_analyze", [i64, i32], [.bool], fullKittenAnalyzeSpec, true⟩
  , ⟨"full_kitten_shrink", [i64], [], fullKittenShrinkSpec, true⟩
  ]

/-- Closed specification environment for `m5KittenDefFixModule`. -/
def m5KittenDefFixEnv : Env := Env.ofTable m5KittenDefFixSpecTable

theorem m5KittenDefFixSpecTable_nodup :
    (m5KittenDefFixSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem m5KittenDefFixSpecTable_noExit :
    ∀ e ∈ m5KittenDefFixSpecTable, e.noExit = true := by
  intro e he
  have hall : m5KittenDefFixSpecTable.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem m5KittenDefFixSpecTable_sigs :
    (m5KittenDefFixSpecTable.take 6).map (fun e => (e.name, e.as, e.rs)) =
      m5KittenDefFix_fns.map (fun f => (f.name, f.as, f.rs)) :=
  rfl

theorem m5KittenDefFixSpecTable_ext_sigs :
    (m5KittenDefFixSpecTable.drop 6).map (fun e => ⟨e.name, e.as, e.rs⟩) =
      m5KittenDefFixExterns :=
  rfl

theorem m5KittenDefFixEnv_noExit :
    ∀ f as bs xs m Q X X',
      m5KittenDefFixEnv f as bs xs m Q X → m5KittenDefFixEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m5KittenDefFixSpecTable_noExit

theorem m5KittenDefFixEnv_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m5KittenDefFixSpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → m5KittenDefFixEnv nm as bs xs m Q X :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) hmem m5KittenDefFixSpecTable_nodup
      (hno xs m Q X hs)

theorem m5KittenDefFix_fns_wf : ∀ f ∈ m5KittenDefFix_fns, f.Wf := by
  intro f hf
  simp only [m5KittenDefFix_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_kitten_add_clause_m5_wf
  · exact full_kitten_ana_clause_m5_wf
  · exact full_kitten_build_failing_m5_wf
  · exact full_kitten_solve_m5_wf
  · exact full_kitten_core_m5_wf
  · exact full_find_definition_m5_wf

private theorem m5KittenDefFix_allFns_wf : AllFns Fn.Wf m5KittenDefFixModule.fns :=
  ⟨full_kitten_add_clause_m5_wf, full_kitten_ana_clause_m5_wf,
   full_kitten_build_failing_m5_wf, full_kitten_solve_m5_wf,
   full_kitten_core_m5_wf, full_find_definition_m5_wf, trivial⟩

theorem m5KittenDefFix_add_clause_impl :
    SpecEntry.Impl m5KittenDefFixEnv
      ⟨"full_kitten_add_clause_m5", [i64, i32, i64, i32], [.bool],
        full_kitten_add_clause_m5_body⟩
      ⟨"full_kitten_add_clause_m5", [i64, i32, i64, i32], [.bool],
        fullKittenAddClauseSpec, true⟩ :=
  SpecEntry.Impl.of (full_kitten_add_clause_m5_wp m5KittenDefFixEnv
    (m5KittenDefFixEnv_row (by simp [m5KittenDefFixSpecTable]) (fun _ _ _ _ h => h)))

theorem m5KittenDefFix_ana_clause_impl :
    SpecEntry.Impl m5KittenDefFixEnv
      ⟨"full_kitten_ana_clause_m5", [i64, i32, i32], [], full_kitten_ana_clause_m5_body⟩
      ⟨"full_kitten_ana_clause_m5", [i64, i32, i32], [], fullKittenAnaClauseM5Spec, true⟩ :=
  SpecEntry.Impl.of (full_kitten_ana_clause_m5_wp m5KittenDefFixEnv)

theorem m5KittenDefFix_build_failing_impl :
    SpecEntry.Impl m5KittenDefFixEnv
      ⟨"full_kitten_build_failing_m5", [i64, i32], [], full_kitten_build_failing_m5_body⟩
      ⟨"full_kitten_build_failing_m5", [i64, i32], [], fullKittenBuildFailingSpec, true⟩ :=
  SpecEntry.Impl.of (full_kitten_build_failing_m5_wp m5KittenDefFixEnv)

theorem m5KittenDefFix_solve_impl :
    SpecEntry.Impl m5KittenDefFixEnv
      ⟨"full_kitten_solve_m5", [i64, i64], [i64], full_kitten_solve_m5_body⟩
      ⟨"full_kitten_solve_m5", [i64, i64], [i64], fullKittenSolveSpec, true⟩ :=
  SpecEntry.Impl.of (full_kitten_solve_m5_wp m5KittenDefFixEnv
    (m5KittenDefFixEnv_row (by simp [m5KittenDefFixSpecTable]) (fun _ _ _ _ h => h))
    (m5KittenDefFixEnv_row (by simp [m5KittenDefFixSpecTable]) (fun _ _ _ _ h => h))
    (m5KittenDefFixEnv_row (by simp [m5KittenDefFixSpecTable]) (fun _ _ _ _ h => h))
    (m5KittenDefFixEnv_row (by simp [m5KittenDefFixSpecTable]) (fun _ _ _ _ h => h))
    (m5KittenDefFixEnv_row (by simp [m5KittenDefFixSpecTable]) (fun _ _ _ _ h => h)))

theorem m5KittenDefFix_core_impl :
    SpecEntry.Impl m5KittenDefFixEnv
      ⟨"full_kitten_core_m5", [i64], [i32], full_kitten_core_m5_body⟩
      ⟨"full_kitten_core_m5", [i64], [i32], fullKittenCoreSpec, true⟩ :=
  SpecEntry.Impl.of (full_kitten_core_m5_wp m5KittenDefFixEnv)

private theorem m5_add_clause_fast_adapter :
    ∀ a m Q X, FullDefSweep.fullKittenAddClauseSpec FullFast.fastKInv a m Q X →
      m5KittenDefFixEnv "full_kitten_add_clause_m5" [i64, i32, i64, i32] [.bool] a m Q X := by
  let Γ' : Env := fun f as bs =>
    if f == "full_kitten_add_clause" then m5KittenDefFixEnv "full_kitten_add_clause_m5" as bs
    else m5KittenDefFixEnv f as bs
  have h := FullFast.fast_kitten_add_clause_adapter (Γ := Γ')
    (m5KittenDefFixEnv_row (by simp [m5KittenDefFixSpecTable]) (fun _ _ _ _ h => h))
  exact h

private theorem m5_solve_fast_adapter :
    ∀ a m Q X, FullDefSweep.fullKittenSolveSpec FullFast.fastKInv a m Q X →
      m5KittenDefFixEnv "full_kitten_solve_m5" [i64, i64] [i64] a m Q X := by
  let Γ' : Env := fun f as bs =>
    if f == "full_kitten_solve" then m5KittenDefFixEnv "full_kitten_solve_m5" as bs
    else m5KittenDefFixEnv f as bs
  have h := FullFast.fast_kitten_solve_adapter (Γ := Γ')
    (m5KittenDefFixEnv_row (by simp [m5KittenDefFixSpecTable]) (fun _ _ _ _ h => h))
  exact h

private theorem m5_core_fast_adapter :
    ∀ a m Q X, FullDefSweep.fullKittenCoreSpec FullFast.fastKInv a m Q X →
      m5KittenDefFixEnv "full_kitten_core_m5" [i64] [i32] a m Q X := by
  let Γ' : Env := fun f as bs =>
    if f == "full_kitten_core" then m5KittenDefFixEnv "full_kitten_core_m5" as bs
    else m5KittenDefFixEnv f as bs
  have h := FullFast.fast_kitten_core_adapter (Γ := Γ')
    (m5KittenDefFixEnv_row (by simp [m5KittenDefFixSpecTable]) (fun _ _ _ _ h => h))
  exact h

theorem m5KittenDefFix_find_definition_impl :
    SpecEntry.Impl m5KittenDefFixEnv
      ⟨"full_find_definition_m5", [i64, i32, i32, i32], [], full_find_definition_m5_body⟩
      ⟨"full_find_definition_m5", [i64, i32, i32, i32], [],
        FullDefSweep.fullFindDefinitionSpec, true⟩ :=
  SpecEntry.Impl.of (full_find_definition_m5_wp m5KittenDefFixEnv fastKInv_laws_m5
    (FullFast.fast_kitten_init_adapter
      (m5KittenDefFixEnv_row (by simp [m5KittenDefFixSpecTable]) (fun _ _ _ _ h => h)))
    m5_add_clause_fast_adapter
    m5_solve_fast_adapter
    m5_core_fast_adapter
    (FullFast.fast_kitten_shrink_adapter
      (m5KittenDefFixEnv_row (by simp [m5KittenDefFixSpecTable]) (fun _ _ _ _ h => h))))

/-- Unconditional `ModuleOk` certifying all `6/6` owned M5 functions of `m5KittenDefFixModule`
against the closed `13`-row `m5KittenDefFixEnv` (wiring `full_find_definition_m5` directly to
`full_kitten_{add_clause,solve,core}_m5` via `FullFast.fastKInv`). -/
theorem m5KittenDefFix_moduleOk : ModuleOk m5KittenDefFixEnv m5KittenDefFixModule :=
  Env.ofTable_moduleOk m5KittenDefFixModule_acyclic m5KittenDefFix_allFns_wf
    ⟨m5KittenDefFix_add_clause_impl, m5KittenDefFix_ana_clause_impl,
     m5KittenDefFix_build_failing_impl, m5KittenDefFix_solve_impl,
     m5KittenDefFix_core_impl, m5KittenDefFix_find_definition_impl, trivial⟩

/-! ## 3. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT proofs) -/

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) for
`full_kitten_add_clause_m5` on `Full.nvKittenMem`. -/
theorem nv_full_kitten_add_clause_m5 :
    Func.wp m5KittenDefFixEnv full_kitten_add_clause_m5_body
      (nvKittenCfg.hdr, 0#32, nvKittenCfg.pTmp, 0#32, ()) nvKittenMem
      (fun (ok, ()) m' => ∃ scr',
        let s' : FullState :=
          { nvKittenState with scratch := { nvKittenState.scratch with scratch_buf := scr' } }
        KittenScratchInv scr' ∧ (cnfOfClauses (kittenOrigClausesS scr')).Unsat ∧
        (ok = true ∨ ok = false) ∧ FullMem nvKittenCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvKittenCfg nvKittenState ⋆ emp) nvKittenMem := by
    rw [sep_emp]; exact nvKittenMem_ok
  have hsync : KittenTrailSynced (kittenStateOfScratch nvKittenScratchBuf) := by
    rw [nvKittenKs_ofSlab]; intro i hi; change i < 0 at hi; omega
  exact m5KittenDefFix_add_clause_impl.2 _ _ _ _
    ⟨nvKittenCfg, nvKittenState, nvKittenScratchBuf, nvKittenState.core.tmp,
     FullSweepFwdHelpers.fullSweepAddRestTmp nvKittenCfg nvKittenState ⋆ emp,
     rfl, nvKittenState_lengths, rfl, nvKitten_scratchInv, hsync,
     by rw [nvKittenKs_ofSlab]; rfl, by rw [nvKittenKs_ofSlab]; rfl,
     by rw [nvKittenKs_ofSlab]; rfl, by decide, by decide,
     fun i hi => by change i < 0 at hi; omega,
     FullSweepFwdHelpers.fullMem_focus_addCl_tmp hm,
     fun ok scr' m' _ _ hscr' _ _ _ _ _ _ _ _ hf ht hm' => by
       have hmFull := FullSweepFwdHelpers.fullMem_unfocus_addCl_tmp hm'
       rw [sep_emp] at hmFull
       have huns' : (cnfOfClauses (kittenOrigClausesS scr')).Unsat := by
         cases ok
         · rw [hf rfl]; exact nvKitten_unsat
         · obtain ⟨_, _, _, _, horig', _⟩ := ht rfl
           rw [horig', CNF.unsat_iff_not_sat]; intro α hα
           exact CNF.unsat_iff_not_sat.mp nvKitten_unsat α
             ((cnfOfClauses_append _ _ α).mp hα).1
       exact ⟨scr', hscr', huns', by cases ok <;> simp, hmFull⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) for
`full_kitten_solve_m5` on `Full.nvKittenMem`. -/
theorem nv_full_kitten_solve_m5 :
    Func.wp m5KittenDefFixEnv full_kitten_solve_m5_body
      (nvKittenCfg.hdr, 8192#64, ()) nvKittenMem
      (fun (r, ()) m' => ∃ fuel' scr',
        let s' : FullState :=
          { nvKittenState with
            core := { nvKittenState.core with fuel := fuel' }
            scratch := { nvKittenState.scratch with scratch_buf := scr' } }
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (cnfOfClauses (kittenOrigClausesS scr') ++ unitsCnf (kittenAssumpLitsS scr')).Unsat ∧
        FullMem nvKittenCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvKittenCfg nvKittenState ⋆ emp) nvKittenMem := by
    rw [sep_emp]; exact nvKittenMem_ok
  exact m5KittenDefFix_solve_impl.2 _ _ _ _
    ⟨nvKittenCfg, nvKittenState, emp, rfl, nvKittenState_lengths, nvKitten_scratchInv, hm,
     fun r fuel' scr' m' _ _ _ _ _ _ _ _ _ hperm _ _ hr _ hm' => by
       rw [sep_emp] at hm'
       have huns0 : (cnfOfClauses (kittenOrigClausesS nvKittenScratchBuf) ++
           unitsCnf (kittenAssumpLitsS scr')).Unsat :=
         cnfOfClauses_unsat_append_left _ nvKitten_unsat
       have huns' : (cnfOfClauses (kittenOrigClausesS scr') ++
           unitsCnf (kittenAssumpLitsS scr')).Unsat :=
         (hperm.unsat_iff (unitsCnf (kittenAssumpLitsS scr'))).mpr huns0
       exact ⟨fuel', scr', hr, huns', hm'⟩⟩

/-- Concrete `Mem 64` `r = 20#64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) for
`full_kitten_solve_m5` under `m5KittenDefFixEnv`. -/
theorem nv_full_kitten_solve_m5_unsat20 :
    Func.wp m5KittenDefFixEnv full_kitten_solve_m5_body
      (nvKittenCfg.hdr, 8192#64, ()) nvKittenMem
      (fun (r, ()) m' => ∃ scr',
        r = 20#64 ∧
        (kittenStateOfScratch scr').incons ≠ 0xFFFFFFFF#32 ∧
        (cnfOfClauses (kittenOrigClausesS scr') ++ unitsCnf (kittenAssumpLitsS scr')).Unsat ∧
        FullMem nvKittenCfg
          { nvKittenState with
            scratch := { nvKittenState.scratch with scratch_buf := scr' } } m')
      (fun _ _ _ _ => False) := by
  have h8864 : 8864 ≤ nvKittenState.scratch.scratch_buf.length := by
    change 8864 ≤ nvKittenScratchBuf.length
    rw [nvKittenScratchBuf_length]; decide
  have h256 : 256 ≤ nvKittenState.scratch.scratch_buf.length := by omega
  have hinv0 : nvKittenKs.Inv 1376 := by
    have h := nvKitten_scratchInv.2.2
    rw [nvKittenKs_ofSlab, show nvKittenScratchBuf.length - 8864 = 1376 by
      rw [nvKittenScratchBuf_length]] at h
    exact h
  have hm0 : (FullKittenFrame nvKittenCfg nvKittenState ⋆
      KittenMem (nvKittenCfg.pScratchBuf + 1024#64) nvKittenKs ⋆ emp) nvKittenMem := by
    have hm1 := nvKittenMem_ok
    rw [fullMem_eq_kittenFrame h8864] at hm1
    change (FullKittenFrame nvKittenCfg nvKittenState ⋆
      KittenMem (nvKittenCfg.pScratchBuf + 1024#64)
        (kittenStateOfScratch nvKittenScratchBuf)) nvKittenMem at hm1
    rw [nvKittenKs_ofSlab] at hm1
    rw [sep_emp]; exact hm1
  have hkPtr : nvKittenCfg.pScratchBuf + BitVec.ofNat 64 256 * 4 =
      nvKittenCfg.pScratchBuf + 1024#64 := kPtr_base_eq _
  unfold Func.wp full_kitten_solve_m5_body
  c0_hsteps_nogrp
  refine wp_call_of_spec _ _
    (m5KittenDefFixEnv_row (sp := fullKittenBacktrackSpec)
      (by simp [m5KittenDefFixSpecTable]) (fun _ _ _ _ h => h) _ _ _ _
      ⟨1376, nvKittenKs, FullKittenFrame nvKittenCfg nvKittenState ⋆ emp, hinv0,
       fun i hi _ => by change i < 0 at hi; omega, by rw [hkPtr]; exact sep_ac hm0,
       fun ks1 m1 hinv1 _ _ _ _ hbt1 _ _ hm1 => ?_⟩)
  have hmA1 : (KittenMemA (nvKittenCfg.pScratchBuf + BitVec.ofNat 64 256 * 4) 1376 ks1 ⋆
      (FullKittenFrame nvKittenCfg nvKittenState ⋆ emp)) m1 :=
    kittenMem_to_amem hinv1.shapes (sep_ac hm1)
  c0_hsplit
  · have hinc1 : ks1.incons ≠ 0xFFFFFFFF#32 := ‹_›
    c0_hsteps!
    let ks2 := ks1.putHdr KHdrField.failing 0xFFFFFFFF#32
    obtain ⟨hsh2, hmFin1⟩ := kittenMemA_to_mem (ks := ks2) hm
    have huns1 := cnfOfClauses_unsat_append_left (unitsCnf (kittenAssumpLits ks1))
      (hinv1.clauses.incons_ok hinc1).2.1
    have hm_join := fullMem_join_kitten (c := nvKittenCfg) (s := nvKittenState) (acap := 1376)
      (ks' := ks2) (R := emp) h256 hsh2 (by rw [← hkPtr]; exact sep_ac hmFin1)
    dsimp only at hm_join
    rw [sep_emp] at hm_join
    let scr' := nvKittenState.scratch.scratch_buf.take 256 ++ ks2.toSlab
    have htk : (nvKittenState.scratch.scratch_buf.take 256).length = 256 :=
      List.length_take_of_le h256
    have hof2 : kittenStateOfScratch scr' = ks2 := by
      unfold kittenStateOfScratch
      rw [show scr' = nvKittenState.scratch.scratch_buf.take 256 ++ ks2.toSlab from rfl,
        slab_drop_exact _ ks2.toSlab htk]
      exact KittenState.ofSlab_toSlab hsh2
    refine ⟨scr', rfl, by rw [hof2]; exact hinc1, ?_, hm_join⟩
    unfold kittenOrigClausesS kittenAssumpLitsS
    rw [hof2]
    exact huns1
  · exact absurd (hbt1.incons.symm.trans ‹ks1.incons = 0xFFFFFFFF#32›) (by decide)

/-- Concrete `Mem 64` for `nv_full_kitten_core_m5`: `nvKittenMem` with `k[KH_ANTE] := 1`. -/
def nvM5CoreMem : Mem 64 :=
  storeMem nvKittenMem i32 ((nvKittenCfg.pScratchBuf + 1024#64) + BitVec.ofNat 64 9 * 4) 1#32

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) for
`full_kitten_core_m5` on `nvM5CoreMem` (`ante = 1`, `incons = 0`, empty clause `0`). -/
theorem nv_full_kitten_core_m5 :
    Func.wp m5KittenDefFixEnv full_kitten_core_m5_body
      (nvKittenCfg.hdr, ()) nvM5CoreMem
      (fun (_csz, ()) m' => ∃ scr',
        KittenScratchInv scr' ∧
        (cnfOfClauses (kittenCoreClausesS scr') ++ unitsCnf (kittenAssumpLitsS scr')).Unsat ∧
        FullMem nvKittenCfg
          { nvKittenState with scratch := { nvKittenState.scratch with scratch_buf := scr' } } m')
      (fun _ _ _ _ => False) := by
  have h8864 : 8864 ≤ nvKittenState.scratch.scratch_buf.length := by
    change 8864 ≤ nvKittenScratchBuf.length
    rw [nvKittenScratchBuf_length]; decide
  have h256 : 256 ≤ nvKittenState.scratch.scratch_buf.length := by omega
  have hinv0 : nvKittenKs.Inv 1376 := by
    have h := nvKitten_scratchInv.2.2
    rw [nvKittenKs_ofSlab, show nvKittenScratchBuf.length - 8864 = 1376 by
      rw [nvKittenScratchBuf_length]] at h
    exact h
  have hm0 : (KittenMem (nvKittenCfg.pScratchBuf + 1024#64) nvKittenKs ⋆
      (FullKittenFrame nvKittenCfg nvKittenState ⋆ emp)) nvKittenMem := by
    have hm1 := nvKittenMem_ok
    rw [fullMem_eq_kittenFrame h8864] at hm1
    change (FullKittenFrame nvKittenCfg nvKittenState ⋆
      KittenMem (nvKittenCfg.pScratchBuf + 1024#64)
        (kittenStateOfScratch nvKittenScratchBuf)) nvKittenMem at hm1
    rw [nvKittenKs_ofSlab] at hm1
    have hm2 : ((FullKittenFrame nvKittenCfg nvKittenState ⋆
        KittenMem (nvKittenCfg.pScratchBuf + 1024#64) nvKittenKs) ⋆ emp) nvKittenMem := by
      rw [sep_emp]; exact hm1
    exact sep_ac hm2
  have hm_ante := (KittenMemTactics.store_kitten_ante 1#32 hm0).2
  let ksC : KittenState := { nvKittenKs with ante := 1#32 }
  have hshC : ksC.ShapesOk 1376 := { hinv0.shapes with }
  have hm_core := fullMem_join_kitten (c := nvKittenCfg) (s := nvKittenState) (acap := 1376)
    (ks' := ksC) (R := emp) h256 hshC (sep_ac hm_ante)
  let scrC := nvKittenState.scratch.scratch_buf.take 256 ++ ksC.toSlab
  let sC : FullState :=
    { nvKittenState with scratch := { nvKittenState.scratch with scratch_buf := scrC } }
  have htk : (nvKittenState.scratch.scratch_buf.take 256).length = 256 :=
    List.length_take_of_le h256
  have hlen_scrC : scrC.length = 10240 := by
    simp only [scrC, List.length_append, htk, KittenState.toSlab_length hshC]
  have hlenC : sC.LengthsOk nvKittenCfg :=
    (fun (c : FullCfg) (s : FullState) (scr' : List (BitVec 32)) (h : s.LengthsOk c)
        (hl : scr'.length = c.scratch_cap) =>
      (⟨h.core_ok, { h.scratch_ok with scratch_buf_len := hl }⟩ :
        ({ s with scratch := { s.scratch with scratch_buf := scr' } } : FullState).LengthsOk c))
      nvKittenCfg nvKittenState scrC nvKittenState_lengths hlen_scrC
  have hksC : kittenStateOfScratch scrC = ksC := by
    unfold kittenStateOfScratch
    rw [show scrC = nvKittenState.scratch.scratch_buf.take 256 ++ ksC.toSlab from rfl,
      slab_drop_exact _ ksC.toSlab htk]
    exact KittenState.ofSlab_toSlab hshC
  have hinvC : KittenScratchInv scrC := by
    refine ⟨by rw [hlen_scrC]; decide, by rw [hlen_scrC]; decide, ?_⟩
    rw [hksC, show scrC.length - 8864 = 1376 by rw [hlen_scrC]]
    refine ⟨hshC, ?_, hinv0.watches, ?_, hinv0.reasons⟩
    · refine { hinv0.clauses with
        cl_wf := fun cid hcid => by
          have hw := hinv0.clauses.cl_wf cid hcid
          exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, fun _ hge => by
            change 1 ≤ cid at hge; change cid < 1 at hcid; omega⟩
        incons_ok := fun h =>
          let hi := hinv0.clauses.incons_ok h
          ⟨hi.1, hi.2.1, fun l hl => by
            have he : kittenClauseLits ksC 0 = [] := by decide
            rw [show ksC.incons.toNat = 0 from rfl, he] at hl; cases hl⟩
        failing_ok := fun _ hf => absurd rfl hf }
    · exact { hinv0.assign with
        lvl0_ok := fun i hi => by change i < 0 at hi; omega }
  exact m5KittenDefFix_core_impl.2 _ _ _ _
    ⟨nvKittenCfg, sC, emp, rfl, hlenC, hinvC,
     by change (kittenStateOfScratch scrC).ante ≠ 0#32; rw [hksC]; decide,
     Or.inl (by change (kittenStateOfScratch scrC).incons ≠ 0xFFFFFFFF#32; rw [hksC]; decide),
     hm_core,
     fun _ scr' m' _ _ hscr' _ _ _ _ _ _ _ _ _ _ _ hcore_u hm' => by
       rw [sep_emp] at hm'; exact ⟨scr', hscr', hcore_u, hm'⟩⟩

/-- Concrete UNSAT `KittenState` for `nv_full_kitten_build_failing_m5`: unit clause `[0]` forced on
trail against falsified assumption `alit = 1` (`¬x0`). -/
def nvM5FailKs : KittenState :=
  { nvKittenKs with
    nv := 1#32, nc := 1#32, orig_nc := 1#32, lvl := 0#32, prop := 1#32, trl_end := 1#32,
    unass := 0#32, incons := 0xFFFFFFFF#32, failing := 0xFFFFFFFF#32, ante := 1#32,
    alen := 1#32, acap := 1376#32, nassump := 1#32, nunits := 1#32,
    vals := ((List.replicate 256 0#32).set 0 1#32).set 1 2#32,
    assump := (List.replicate 128 0#32).set 0 1#32,
    whead := List.replicate 256 0xFFFFFFFF#32,
    clMeta := (List.replicate 896 0#32).set 0 1#32 }

theorem nvM5FailKs_shapes : nvM5FailKs.ShapesOk 1376 :=
  ⟨List.length_replicate, List.length_replicate, List.length_replicate,
   List.length_replicate, List.length_replicate, List.length_replicate,
   List.length_replicate, List.length_replicate,
   by dsimp only [nvM5FailKs]; simp only [List.length_set, List.length_replicate],
   by dsimp only [nvM5FailKs]; simp only [List.length_set, List.length_replicate],
   List.length_replicate, List.length_replicate, List.length_replicate,
   List.length_replicate, List.length_replicate, List.length_replicate,
   List.length_replicate, List.length_replicate,
   by dsimp only [nvM5FailKs]; simp only [List.length_set, List.length_replicate],
   List.length_replicate, List.length_replicate⟩

/-- Concrete `39936`-byte `Mem 64` for `nvM5FailKs` at `0x2000#64`. -/
def nvM5FailMem : Mem 64 := (bytesOf (t := i32) nvM5FailKs.toSlab).At 0x2000#64

theorem nvM5FailMem_ok : KittenMem 0x2000#64 nvM5FailKs nvM5FailMem := by
  rw [kittenMem_eq_array 0x2000#64 nvM5FailKs_shapes]
  exact (nv_arr_p (t := i32) (a := 0x2000#64) (xs := nvM5FailKs.toSlab) 39936
    (by rw [KittenState.toSlab_length nvM5FailKs_shapes]; decide) (by decide)).2

private theorem nvM5Fail_cl0 : kittenClauseLits nvM5FailKs 0 = [0] := by
  unfold kittenClauseLits kittenClauseOff kittenClauseSize kittenClauseMeta
  have hm0 : nvM5FailKs.clMeta[0]?.getD 0#32 = 1#32 := by decide
  have ho0 : nvM5FailKs.clOff[0]?.getD 0#32 = 0#32 := by decide
  rw [hm0, ho0]
  have ha0 : nvM5FailKs.arena.take 1 = [0#32] := rfl
  simpa using congrArg (List.map BitVec.toNat) ha0

private theorem nvM5Fail_orig : kittenOrigClauses nvM5FailKs = [[0]] := by
  unfold kittenOrigClauses
  rw [show nvM5FailKs.orig_nc.toNat = 1 from rfl, List.range_one, List.map_singleton, nvM5Fail_cl0]

private theorem nvM5Fail_unsat :
    (cnfOfClauses (kittenOrigClauses nvM5FailKs) ++
      unitsCnf (kittenAssumpLits nvM5FailKs)).Unsat := by
  rw [nvM5Fail_orig, show kittenAssumpLits nvM5FailKs = [1] from by decide]
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have h1 := (cnf_sat_cnfOfClauses_iff α [[0]]).mp (CNF.sat_append.mp hα).1 [0] (by simp)
  have h2 := (sat_unitsCnf_iff α [1]).mp (CNF.sat_append.mp hα).2 1 (by simp)
  rw [clause_sat_cnfClause_iff] at h1 h2
  obtain ⟨_, hm1, hs1⟩ := h1; obtain ⟨_, hm2, hs2⟩ := h2
  simp at hm1 hm2; subst hm1 hm2
  simp [litVar, litSign] at hs1 hs2; rw [hs1] at hs2; cases hs2

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) for
`full_kitten_build_failing_m5` on `nvM5FailMem` (`[0]` vs assumption `[1]`). -/
theorem nv_full_kitten_build_failing_m5 :
    Func.wp m5KittenDefFixEnv full_kitten_build_failing_m5_body
      (0x2000#64, 1#32, ()) nvM5FailMem
      (fun () m' => ∃ ks',
        ks'.Inv 1376 ∧ ks'.failing = 1#32 ∧
        (cnfOfClauses (kittenOrigClauses ks') ++ unitsCnf (kittenAssumpLits ks')).Unsat ∧
        KittenMem 0x2000#64 ks' m')
      (fun _ _ _ _ => False) := by
  have hm : (KittenMem 0x2000#64 nvM5FailKs ⋆ emp) nvM5FailMem := by
    rw [sep_emp]; exact nvM5FailMem_ok
  have htrl_lits : kittenTrailLits nvM5FailKs = [0] := by decide
  have hcl : KittenClausesOk 1376 nvM5FailKs :=
    { acap_ge := by decide, acap_lt := by decide, acap_eq := rfl
      nv_le := by decide, nc_le := by decide, orig_nc_le := by decide
      orig_nc_max := by decide, alen_le := by decide, nassump_le := by decide
      nunits_le := by decide, nres_le := by decide, nkl_le := by decide, nana_le := by decide
      cl_wf := fun cid hcid => by
        change cid < 1 at hcid
        obtain rfl : cid = 0 := by omega
        refine ⟨by decide, fun h => by change 1 ≤ 0 at h; omega, by decide,
          fun l hl => by rw [nvM5Fail_cl0, List.mem_singleton] at hl; subst hl; decide,
          by rw [nvM5Fail_orig, nvM5Fail_cl0]; exact CNF.entails_clause_def.mpr fun α hα =>
            (cnf_sat_cnfOfClauses_iff α [[0]]).mp hα [0] (by simp),
          fun _ hge => by change 1 ≤ 0 at hge; omega⟩
      cl_mono := fun c1 c2 h1 h2 => by change c2 < 1 at h2; omega
      units_ok := fun i hi => by
        change i < 1 at hi
        obtain rfl : i = 0 := by omega
        decide
      incons_ok := fun h => absurd rfl h
      failing_ok := fun _ h => absurd rfl h
      assump_ok := fun i hi => by
        change i < 1 at hi
        obtain rfl : i = 0 := by omega
        decide
      flags_clean := fun v hv => by
        change v < 1 at hv
        obtain rfl : v = 0 := by omega
        decide }
  have hwat : KittenWatchesOk nvM5FailKs :=
    ⟨[[], []], rfl, by decide,
     fun l hl => by
       change l < 2 at hl
       rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
       · rw [show nvM5FailKs.whead[0]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 by decide]; exact .nil
       · rw [show nvM5FailKs.whead[1]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 by decide]; exact .nil,
     fun l hl w hw => by
       change l < 2 at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp at hw⟩
  have hba : KittenBaseAssignOk nvM5FailKs :=
    { trl_end_le := by decide, prop_le := by decide, unass_eq := by decide
      vals_dom := fun l hl => by
        change l < 2 at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
      vals_neg_iff := fun l hl => by
        change l < 2 at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
      vals_nz_iff_trl := fun l hl => by
        change l < 2 at hl
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, by decide, by decide⟩, fun _ => by decide⟩
        · exact ⟨fun _ => ⟨0, by decide, by decide⟩, fun _ => by decide⟩
      trl_nodup := by rw [htrl_lits]; decide
      trl_lt := fun l hl => by rw [htrl_lits, List.mem_singleton] at hl; subst hl; decide
      trl_lvl_le := fun v hv => by
        change v < 1 at hv
        obtain rfl : v = 0 := by omega
        decide
      unass_lvl_zero := fun v hv hu => by
        change v < 1 at hv
        obtain rfl : v = 0 := by omega
        exact absurd hu (by decide)
      trl_lvl_mono := fun i j hij hj => by
        change j < 1 at hj
        obtain rfl : j = 0 := by omega
        obtain rfl : i = 0 := by omega
        exact Nat.le_refl _
      dec_earliest := fun i j hji hi _ => by change i < 1 at hi; omega
      lvl0_ok := fun i hi _ => by
        change i < 1 at hi
        obtain rfl : i = 0 := by omega
        refine ⟨by decide, by decide, by decide, ?_, fun _ => ⟨by decide, ?_⟩⟩
        · rw [nvM5Fail_orig]; exact CNF.entails_clause_def.mpr fun α hα =>
            (cnf_sat_cnfOfClauses_iff α [[0]]).mp hα [0] (by simp)
        · change kittenClauseLits nvM5FailKs 0 = [0]; exact nvM5Fail_cl0 }
  have hrsn : Full.ReasonOk nvM5FailKs := fun i hi => by
    change i < 1 at hi
    obtain rfl : i = 0 := by omega
    right
    have hr0 : (nvM5FailKs.rsn[(nvM5FailKs.trl[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 :=
      by decide
    have hl0 : (nvM5FailKs.trl[0]?.getD 0#32).toNat = 0 := by decide
    refine ⟨by decide, ?_, fun l hl hne => by
      rw [hr0, nvM5Fail_cl0, List.mem_singleton] at hl
      rw [hl0] at hne; exact absurd hl hne⟩
    rw [hr0, hl0, nvM5Fail_cl0]; exact List.mem_singleton.mpr rfl
  have hsync : KittenTrailSynced nvM5FailKs := fun i hi => by
    change i < 1 at hi
    obtain rfl : i = 0 := by omega
    decide
  have hdec : KittenAllDecisionsInAssumps nvM5FailKs := fun d hd => by
    have h0 : kittenTrailDecisions nvM5FailKs = [] := by decide
    rw [h0] at hd; cases hd
  exact m5KittenDefFix_build_failing_impl.2 _ _ _ _
    ⟨1376, nvM5FailKs, emp, ⟨nvM5FailKs_shapes, hcl, hwat, hba, hrsn⟩, hsync,
     by decide, by decide, by decide, hdec, hm,
     fun ks' m' hinv' _ hfail' hpres' hm' => by
       rw [sep_emp] at hm'
       have huns' : (cnfOfClauses (kittenOrigClauses ks') ++
           unitsCnf (kittenAssumpLits ks')).Unsat := by
         unfold kittenAssumpLits
         rw [hpres'.orig_eq, hpres'.nassump, hpres'.assump]
         exact nvM5Fail_unsat
       exact ⟨ks', hinv', hfail', huns', hm'⟩⟩

/-- Concrete UNSAT `KittenState` for `nv_full_kitten_ana_clause_m5`: clauses `[0], [1]`, decision
`0` at level `1`, conflicting clause `cid = 1` (`[1]`). -/
def nvM5AnaKs : KittenState :=
  { nvKittenKs with
    nv := 1#32, nc := 2#32, orig_nc := 2#32, lvl := 1#32, prop := 1#32, trl_end := 1#32,
    unass := 0#32, incons := 0xFFFFFFFF#32, failing := 0xFFFFFFFF#32, ante := 0#32,
    alen := 2#32, acap := 1376#32, nkl := 1#32, nana := 0#32, nres := 0#32, status := 0#32,
    lvlArr := (List.replicate 128 0#32).set 0 1#32,
    rsn := (List.replicate 128 0#32).set 0 0xFFFFFFFF#32,
    vals := ((List.replicate 256 0#32).set 0 1#32).set 1 2#32,
    whead := List.replicate 256 0xFFFFFFFF#32,
    clOff := (List.replicate 896 0#32).set 1 1#32,
    clMeta := ((List.replicate 896 0#32).set 0 1#32).set 1 1#32,
    arena := (List.replicate 1376 0#32).set 1 1#32 }

theorem nvM5AnaKs_shapes : nvM5AnaKs.ShapesOk 1376 :=
  ⟨List.length_replicate,
   by dsimp only [nvM5AnaKs]; simp only [List.length_set, List.length_replicate],
   by dsimp only [nvM5AnaKs]; simp only [List.length_set, List.length_replicate],
   List.length_replicate, List.length_replicate, List.length_replicate,
   List.length_replicate, List.length_replicate,
   by dsimp only [nvM5AnaKs]; simp only [List.length_set, List.length_replicate],
   List.length_replicate, List.length_replicate, List.length_replicate,
   List.length_replicate, List.length_replicate, List.length_replicate,
   List.length_replicate, List.length_replicate,
   by dsimp only [nvM5AnaKs]; simp only [List.length_set, List.length_replicate],
   by dsimp only [nvM5AnaKs]; simp only [List.length_set, List.length_replicate],
   List.length_replicate,
   by dsimp only [nvM5AnaKs]; simp only [List.length_set, List.length_replicate]⟩

/-- Concrete `39936`-byte `Mem 64` for `nvM5AnaKs` at `0x2000#64`. -/
def nvM5AnaMem : Mem 64 := (bytesOf (t := i32) nvM5AnaKs.toSlab).At 0x2000#64

theorem nvM5AnaMem_ok : KittenMem 0x2000#64 nvM5AnaKs nvM5AnaMem := by
  rw [kittenMem_eq_array 0x2000#64 nvM5AnaKs_shapes]
  exact (nv_arr_p (t := i32) (a := 0x2000#64) (xs := nvM5AnaKs.toSlab) 39936
    (by rw [KittenState.toSlab_length nvM5AnaKs_shapes]; decide) (by decide)).2

private theorem nvM5Ana_cl0 : kittenClauseLits nvM5AnaKs 0 = [0] := by
  unfold kittenClauseLits kittenClauseOff kittenClauseSize kittenClauseMeta
  have hm0 : nvM5AnaKs.clMeta[0]?.getD 0#32 = 1#32 := by decide
  have ho0 : nvM5AnaKs.clOff[0]?.getD 0#32 = 0#32 := by decide
  rw [hm0, ho0]; decide

private theorem nvM5Ana_cl1 : kittenClauseLits nvM5AnaKs 1 = [1] := by
  unfold kittenClauseLits kittenClauseOff kittenClauseSize kittenClauseMeta
  have hm1 : nvM5AnaKs.clMeta[1]?.getD 0#32 = 1#32 := by decide
  have ho1 : nvM5AnaKs.clOff[1]?.getD 0#32 = 1#32 := by decide
  rw [hm1, ho1]; decide

private theorem nvM5Ana_orig : kittenOrigClauses nvM5AnaKs = [[0], [1]] := by
  unfold kittenOrigClauses
  rw [show nvM5AnaKs.orig_nc.toNat = 2 from rfl]
  simp only [List.range_succ, List.map_append, List.map_singleton, nvM5Ana_cl0, nvM5Ana_cl1]; rfl

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) for
`full_kitten_ana_clause_m5` on `nvM5AnaMem` (`F0 = [[0], [1]]` UNSAT). -/
theorem nv_full_kitten_ana_clause_m5 :
    Func.wp m5KittenDefFixEnv full_kitten_ana_clause_m5_body
      (0x2000#64, 1#32, 0xFFFFFFFF#32, ()) nvM5AnaMem
      (fun () m' => ∃ ks',
        KittenAnaInvM5 1376 ks' [[0], [1]] 1 ∧
        (cnfOfClauses [[0], [1]]).Unsat ∧
        KittenMem 0x2000#64 ks' m')
      (fun _ _ _ _ => False) := by
  have hm : (KittenMem 0x2000#64 nvM5AnaKs ⋆ emp) nvM5AnaMem := by
    rw [sep_emp]; exact nvM5AnaMem_ok
  have htrl_lits : kittenTrailLits nvM5AnaKs = [0] := by decide
  have hwat : KittenWatchesOk nvM5AnaKs :=
    ⟨[[], []], rfl, by decide,
     fun l hl => by
       change l < 2 at hl
       rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
       · rw [show nvM5AnaKs.whead[0]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 by decide]; exact .nil
       · rw [show nvM5AnaKs.whead[1]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 by decide]; exact .nil,
     fun l hl w hw => by
       change l < 2 at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp at hw⟩
  have hba : KittenBaseAssignOk nvM5AnaKs :=
    { trl_end_le := by decide, prop_le := by decide, unass_eq := by decide
      vals_dom := fun l hl => by
        change l < 2 at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
      vals_neg_iff := fun l hl => by
        change l < 2 at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
      vals_nz_iff_trl := fun l hl => by
        change l < 2 at hl
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, by decide, by decide⟩, fun _ => by decide⟩
        · exact ⟨fun _ => ⟨0, by decide, by decide⟩, fun _ => by decide⟩
      trl_nodup := by rw [htrl_lits]; decide
      trl_lt := fun l hl => by rw [htrl_lits, List.mem_singleton] at hl; subst hl; decide
      trl_lvl_le := fun v hv => by
        change v < 1 at hv
        obtain rfl : v = 0 := by omega
        decide
      unass_lvl_zero := fun v hv hu => by
        change v < 1 at hv
        obtain rfl : v = 0 := by omega
        exact absurd hu (by decide)
      trl_lvl_mono := fun i j hij hj => by
        change j < 1 at hj
        obtain rfl : j = 0 := by omega
        obtain rfl : i = 0 := by omega
        exact Nat.le_refl _
      dec_earliest := fun i j hji hi _ => by change i < 1 at hi; omega
      lvl0_ok := fun i hi hlv => by
        change i < 1 at hi
        obtain rfl : i = 0 := by omega
        exact absurd hlv (by decide) }
  have hana : KittenAnaInvM5 1376 nvM5AnaKs [[0], [1]] 1 :=
    { shapes := nvM5AnaKs_shapes, nv_le := by decide, nc_le := by decide
      orig_nc_le := by decide, orig_nc_max := by decide, alen_le := by decide
      acap_lt := by decide, acap_eq := rfl, lvl_pos := by decide, idx_le := by decide
      cl_wf := fun cid hcid => by
        change cid < 2 at hcid
        rcases (by omega : cid = 0 ∨ cid = 1) with rfl | rfl
        · refine ⟨by decide, fun h => by change 2 ≤ 0 at h; omega, by decide,
            fun l hl => by rw [nvM5Ana_cl0, List.mem_singleton] at hl; subst hl; decide,
            by rw [nvM5Ana_cl0]; exact CNF.entails_clause_def.mpr fun α hα =>
              (cnf_sat_cnfOfClauses_iff α [[0], [1]]).mp hα [0] (by simp),
            fun h _ => absurd rfl h⟩
        · refine ⟨by decide, fun h => by change 2 ≤ 1 at h; omega, by decide,
            fun l hl => by rw [nvM5Ana_cl1, List.mem_singleton] at hl; subst hl; decide,
            by rw [nvM5Ana_cl1]; exact CNF.entails_clause_def.mpr fun α hα =>
              (cnf_sat_cnfOfClauses_iff α [[0], [1]]).mp hα [1] (by simp),
            fun h _ => absurd rfl h⟩
      cl_mono := fun c1 c2 h1 h2 => by
        change c2 < 2 at h2
        obtain rfl : c1 = 0 := by omega
        obtain rfl : c2 = 1 := by omega
        decide
      orig_eq := nvM5Ana_orig, watches := hwat, assign := hba
      synced := fun i hi => by
        change i < 1 at hi
        obtain rfl : i = 0 := by omega
        decide
      reasons := fun i hi => by
        change i < 1 at hi
        obtain rfl : i = 0 := by omega
        exact Or.inl (by decide)
      nres_le := by decide, nkl_pos := by decide, nkl_le := by decide, nana_le := by decide
      ana_nodup := by decide
      ana_lt := fun i hi => by change i < 0 at hi; omega
      flags_seen := fun v hv => by
        change v < 1 at hv
        obtain rfl : v = 0 := by omega
        exact ⟨fun h => absurd (by decide) h, fun ⟨i, hi, _⟩ => by change i < 0 at hi; omega⟩
      kl_nonTop := fun i h1 h2 => by change i < 1 at h2; omega
      kl_injective := fun v hv hfl => by
        change v < 1 at hv
        obtain rfl : v = 0 := by omega
        exact absurd (by decide) hfl
      lvl0_seen_in_res := fun ha => absurd rfl ha
      kl_nodup := by decide
      status_eq := by decide
      seen_in_trl := fun v hv hfl => by
        change v < 1 at hv
        obtain rfl : v = 0 := by omega
        exact absurd (by decide) hfl }
  exact m5KittenDefFix_ana_clause_impl.2 _ _ _ _
    ⟨1376, nvM5AnaKs, [[0], [1]], 1, emp, hana, by decide, Or.inl rfl,
     ⟨0, by decide, by decide⟩,
     fun l hl _ => by
       rw [show (1#32).toNat = 1 from rfl, nvM5Ana_cl1, List.mem_singleton] at hl
       subst hl; exact ⟨0, by decide, by decide⟩,
     Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩, hm,
     fun ks' m' hinv' _ _ _ hm' => by
       rw [sep_emp] at hm'
       exact ⟨ks', hinv', FullDefSweep.nvDefSweepF0_unsat, hm'⟩⟩

private theorem nvM5Def_entails_00 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0, 0]) := by
  rw [CNF.entails_clause_def]; intro α hα
  have h0 := (cnf_sat_cnfOfClauses_iff α [[0], [1]]).mp hα [0] (by simp)
  rw [clause_sat_cnfClause_iff] at h0 ⊢
  obtain ⟨l, hl, hs⟩ := h0; exact ⟨l, List.mem_cons_of_mem _ hl, hs⟩

private theorem nvM5Def_entails_11 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [1, 1]) := by
  rw [CNF.entails_clause_def]; intro α hα
  have h1 := (cnf_sat_cnfOfClauses_iff α [[0], [1]]).mp hα [1] (by simp)
  rw [clause_sat_cnfClause_iff] at h1 ⊢
  obtain ⟨l, hl, hs⟩ := h1; exact ⟨l, List.mem_cons_of_mem _ hl, hs⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) for
`full_find_definition_m5` on `FullDefSweep.nvDefSweepMem` (`42716`-byte image). -/
theorem nv_full_find_definition_m5 :
    Func.wp m5KittenDefFixEnv full_find_definition_m5_body
      (FullDefSweep.nvDefSweepCfg.hdr, 0#32, 1#32, 1#32, ()) FullDefSweep.nvDefSweepMem
      (fun () m' => ∃ s',
        FullDenseInvW FullDefSweep.nvDefSweepCfg nvOneLitF0 [[0], [1]] s' ∧
        FullDefSweep.TmkZero s' ∧ nvOneLitF0.Unsat ∧
        FullMem FullDefSweep.nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullDefSweep.nvDefSweepCfg FullDefSweep.nvDefSweepState ⋆ emp)
      FullDefSweep.nvDefSweepMem := by
    rw [sep_emp]; exact FullDefSweep.nvDefSweepMem_ok
  have hpos : ∀ i < 1, FullBveEntryOkW [[0], [1]] FullDefSweep.nvDefSweepState 0
      (FullDefSweep.nvDefSweepState.scratch.scratch_buf[i]?.getD 0#32) := by
    intro i hi; obtain rfl : i = 0 := by omega
    have hget : FullDefSweep.nvDefSweepState.scratch.scratch_buf[0]?.getD 0#32 =
        0x80000000#32 := by
      change FullDefSweep.nvDefSweepScratchBuf[0]?.getD 0#32 = 0x80000000#32
      unfold FullDefSweep.nvDefSweepScratchBuf
      rw [List.getElem?_set_ne (by decide),
        List.getElem?_set_self (by rw [List.length_replicate]; decide)]
      rfl
    rw [hget]
    show if (0x80000000#32 &&& 0x80000000#32) ≠ 0#32 then _ else _
    rw [ite_eq_left (by decide)]
    exact ⟨by decide, nvM5Def_entails_00⟩
  have hneg : ∀ j < 1, FullBveEntryOkW [[0], [1]] FullDefSweep.nvDefSweepState 1
      (FullDefSweep.nvDefSweepState.scratch.scratch_buf[64 + j]?.getD 0#32) := by
    intro j hj; obtain rfl : j = 0 := by omega
    have hget : FullDefSweep.nvDefSweepState.scratch.scratch_buf[64]?.getD 0#32 =
        0x80000001#32 := by
      change FullDefSweep.nvDefSweepScratchBuf[64]?.getD 0#32 = 0x80000001#32
      unfold FullDefSweep.nvDefSweepScratchBuf
      rw [List.getElem?_set_self (by rw [List.length_set, List.length_replicate]; decide)]
      rfl
    rw [hget]
    show if (0x80000001#32 &&& 0x80000000#32) ≠ 0#32 then _ else _
    rw [ite_eq_left (by decide)]
    exact ⟨by decide, nvM5Def_entails_11⟩
  exact m5KittenDefFix_find_definition_impl.2 _ _ _ _
    ⟨FullDefSweep.nvDefSweepCfg, nvOneLitF0, [[0], [1]], FullDefSweep.nvDefSweepState, emp, rfl,
     FullDefSweep.nvDefSweep_invW, by decide, FullDefSweep.nvDefSweep_tmkZero, by decide,
     by decide, by decide, hpos, hneg, hm,
     fun s' m' hd ht _ _ _ _ _ _ _ hm' => by
       rw [sep_emp] at hm'; exact ⟨s', hd, ht, FullDefSweep.nvDefSweepF0_unsat, hm'⟩⟩

end LeanQbe.T.Examples.Kissat.FullM5KittenDefFix
