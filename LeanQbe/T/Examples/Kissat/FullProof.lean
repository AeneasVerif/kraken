module

public import LeanQbe.T.Examples.Kissat.FullBridgeLemmas
public import LeanQbe.T.Examples.Kissat.FullBridgeLemmas5
public import LeanQbe.T.Examples.Kissat.FullBridgeLemmas6
public import LeanQbe.T.Examples.Kissat.FullBridgeLemmas7
public import LeanQbe.T.Examples.Kissat.FullBridgeLemmas8a
public import LeanQbe.T.Examples.Kissat.FullBridgeLemmas8b
public import LeanQbe.T.Examples.Kissat.FullBridgeLemmas9
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` UNSAT Non-Vacuity & 166-Function `ModuleOk` Assembly (`Stage 4`)

Assembles:
1. Concrete UNSAT (`20#64`) non-vacuity witness (`fullNvUnsatBytes` → `20#64` and
   `fullNvUnsatCnf.Unsat` on `4096` B work, `fuel = 16`, strictly UNSAT-only).
2. Canonical `fullEnv` / `fullUnsatEnv` source-level soundness (`full_solve_bytes_correct`) and
   non-vacuity (`full_unsat_nonvacuous`).
3. Turn-key `166`-row `TableImpl` and `ModuleOk` assembly (`mkFullEnv_tableImpl_of_missing`,
   `mkFullEnv_moduleOk_of_missing`, `fullEnv_moduleOk_of_missing`,
   `fullUnsatEnv_modOk_rem`) covering all `151 / 166` landed bridges
   (`FullBridgeLemmas{1..7,9}`) and parameterized strictly by the remaining `6` ProbeTrans
   (`fullRemaining8aIndices`) and `9` Analyze/OTFS (`fullRemaining8bIndices`) bridges.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Concrete UNSAT (`20#64`) non-vacuity witness (`4096`-byte work) -/

/-- Concrete UNSAT DIMACS input (`p cnf 1 2\n1 0\n-1 0\n`, 19 bytes). -/
def fullNvUnsatBytes : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 49, 32, 50, 10, 49, 32, 48, 10, 45, 49, 32, 48, 10]

/-- Parsed `Std.Sat.CNF Nat` for `fullNvUnsatBytes`. -/
def fullNvUnsatCnf : CNF Nat :=
  (CNF.empty.add (CNF.Clause.ofLiterals [(1, true)])).add (CNF.Clause.ofLiterals [(1, false)])

theorem parseDimacs_fullNvUnsatBytes : parseDimacs fullNvUnsatBytes = some fullNvUnsatCnf := rfl

private theorem fullNvUnsat_header :
    parseHeader fullNvUnsatBytes = some (1, 2, fullNvUnsatBytes.drop 9) := by decide

private theorem fullNvUnsat_trace :
    UnitUnsatTrace 1 (List.replicate 2 0#8) (fullNvUnsatBytes.drop 9) 2 := by
  have hcl1 : parseClause 1 (fullNvUnsatBytes.drop 9) =
      some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral 0], fullNvUnsatBytes.drop 13) := rfl
  have hcl2 : parseClause 1 (fullNvUnsatBytes.drop 13) =
      some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral 1], [10]) := rfl
  exact UnitUnsatTrace.step (l := 0) (by decide) hcl1 (by decide)
    (UnitUnsatTrace.conflict (l := 1) (by decide) hcl2 (by decide) ⟨CNF.empty, rfl⟩)

/-- Concrete UNSAT witness contract (`fullNvUnsatBytes`, `work_len = 4096`, `fuel = 16`). -/
def fullUnsatWitnessSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q _ =>
    ∃ R : Mem 64 → Prop,
      cnf_ptr ≠ 0#64 ∧ work_ptr ≠ 0#64 ∧
      cnf_len = BitVec.ofNat 64 fullNvUnsatBytes.length ∧ work_len = 4096#64 ∧ fuel = 16#64 ∧
      cnf_ptr.toNat + fullNvUnsatBytes.length < 2 ^ 64 ∧ work_ptr.toNat + 4096 < 2 ^ 64 ∧
      (bytes cnf_ptr fullNvUnsatBytes ⋆ region work_ptr 4096 ⋆ R) m ∧
      ∀ m', fullNvUnsatCnf.Unsat →
        (bytes cnf_ptr fullNvUnsatBytes ⋆ region work_ptr 4096 ⋆ R) m' → Q (20#64, ()) m'

theorem fullSolveBytesCoreSpec_of_unsatWitness
    {args : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : fullUnsatWitnessSpec args m Q X) : fullSolveBytesCoreSpec args m Q X := by
  obtain ⟨R, hcp, hwp, hcl, hwl, hfu, hcfit, hwfit, hm, hQ⟩ := h
  refine ⟨fullNvUnsatBytes, 4096, R, hcl, hwl, hcfit, hwfit, hm, fun r m' _ hu huns_w hm' => ?_⟩
  have hr20 : r = 20#64 :=
    huns_w 1 2 9 hcp hwp (by rw [hfu]; decide)
      (by unfold fullFixedBytes valsBytes markBytes u32FullBytes fullMinDepthOf; decide)
      (by decide) fullNvUnsat_header fullNvUnsat_trace
  subst hr20
  obtain ⟨cnf, hparse, huns⟩ := hu rfl
  rw [parseDimacs_fullNvUnsatBytes] at hparse; cases Option.some.inj hparse
  exact hQ m' huns hm'

abbrev fullNvCnfPtr : BitVec 64 := 0x1000#64
abbrev fullNvWorkPtr (cnfBytes : List UInt8) : BitVec 64 :=
  fullNvCnfPtr + BitVec.ofNat 64 cnfBytes.length

def fullPayload (cnfBytes : List UInt8) : List UInt8 :=
  cnfBytes ++ List.replicate 4096 0

theorem fullPayload_length (cnfBytes : List UInt8) :
    (fullPayload cnfBytes).length = cnfBytes.length + 4096 := by
  simp only [fullPayload, List.length_append, List.length_replicate]

theorem fullPayload_sep (cnfBytes : List UInt8) (hcb : cnfBytes.length ≤ 4096) :
    (bytes fullNvCnfPtr cnfBytes ⋆ region (fullNvWorkPtr cnfBytes) 4096)
      ((fullPayload cnfBytes).At fullNvCnfPtr) := by
  have h4096 : (List.replicate 4096 (0 : UInt8)).length = 4096 := List.length_replicate
  have h1 := Mem.At_append_sep cnfBytes (List.replicate 4096 0) fullNvCnfPtr
    (by simp only [h4096]; omega)
  have h0 : (Eq ((cnfBytes ++ List.replicate 4096 0).At fullNvCnfPtr))
      ((fullPayload cnfBytes).At fullNvCnfPtr) := rfl
  rw [h1] at h0
  exact sep_mono_r (fun _ hfW => ⟨List.replicate 4096 0, h4096, hfW.symm⟩) h0

/-- Closed 166-function environment for concrete UNSAT non-vacuity (`20#64`). -/
def fullUnsatEnv : Env := mkFullEnv fullUnsatWitnessSpec

/-! ## 2. Environment helpers & headline source-level UNSAT soundness / non-vacuity -/

private theorem fullFns_nodup : (fullFns.map Fn.name).Nodup := by
  have hchk := full_acyclic
  simp only [fullModule, Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

private theorem fullSpecTable_nodup (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((fullSpecTable mainSpec).map SpecEntry.name).Nodup := by
  have h : (fullSpecTable mainSpec).map SpecEntry.name = fullFns.map Fn.name := by
    have hm := congrArg (List.map Prod.fst) (fullSpecTable_sigs mainSpec)
    simpa only [List.map_map, Function.comp_def] using hm
  rw [h]
  exact fullFns_nodup

private theorem mkFullEnv_row_at {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry)
    (hi : (fullSpecTable mainSpec)[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkFullEnv mainSpec e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) (fullSpecTable_nodup mainSpec) (hno xs m Q X h)

private theorem allFns_of_forall {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | _ :: _, h =>
    ⟨h _ List.mem_cons_self, allFns_of_forall fun f hf => h f (List.mem_cons_of_mem _ hf)⟩

theorem mkFullEnv_noExit (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ f as bs xs m Q X X',
      mkFullEnv mainSpec f as bs xs m Q X →
      mkFullEnv mainSpec f as bs xs m Q X' :=
  Env.ofTable_noExit (fullSpecTable_noExit mainSpec)

theorem fullEnv_noExit :
    ∀ f as bs xs m Q X X', fullEnv f as bs xs m Q X → fullEnv f as bs xs m Q X' :=
  mkFullEnv_noExit fullSolveBytesSpec

theorem fullUnsatEnv_noExit :
    ∀ f as bs xs m Q X X', fullUnsatEnv f as bs xs m Q X → fullUnsatEnv f as bs xs m Q X' :=
  mkFullEnv_noExit fullUnsatWitnessSpec

/-- Headline source-level UNSAT-only correctness of `D-Full` `kissat_solve_bytes` under
canonical 166-function `fullEnv`. -/
theorem full_solve_bytes_correct
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fullEnv kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  kissat_solve_bytes_wp fullEnv
    (mkFullEnv_row_at (mainSpec := fullSolveBytesSpec) 41
      ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩)
    (mkFullEnv_row_at (mainSpec := fullSolveBytesSpec) 44
      ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩)
    (mkFullEnv_row_at (mainSpec := fullSolveBytesSpec) 162
      ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩)
    (mkFullEnv_row_at (mainSpec := fullSolveBytesSpec) 164
      ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩)
    (mkFullEnv_row_at (mainSpec := fullSolveBytesSpec) 96
      ⟨"full_extend", [i64], [], fullExtendSpec, true⟩)
    (mkFullEnv_row_at (mainSpec := fullSolveBytesSpec) 7
      ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩)
    _ m _ X
    ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, fun _ _ hdom hu hm' => ⟨hdom, hu, hm'⟩⟩

/-- Closed concrete UNSAT non-vacuity under canonical 166-function `fullUnsatEnv`:
`kissat_solve_bytes` returns `20#64` and proves `fullNvUnsatCnf.Unsat` on `fullNvUnsatBytes`
with `work_len = 4096` and `fuel = 16`. -/
theorem full_unsat_nonvacuous :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp fullUnsatEnv kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun rs _ => rs = (20#64, ()) ∧ fullNvUnsatCnf.Unsat) (fun _ _ _ _ => False) :=
  kissat_solve_bytes_core_wp fullUnsatEnv
    (mkFullEnv_row_at (mainSpec := fullUnsatWitnessSpec) 41
      ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩)
    (mkFullEnv_row_at (mainSpec := fullUnsatWitnessSpec) 44
      ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩)
    (mkFullEnv_row_at (mainSpec := fullUnsatWitnessSpec) 162
      ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩)
    (mkFullEnv_row_at (mainSpec := fullUnsatWitnessSpec) 164
      ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩)
    (mkFullEnv_row_at (mainSpec := fullUnsatWitnessSpec) 96
      ⟨"full_extend", [i64], [], fullExtendSpec, true⟩)
    (mkFullEnv_row_at (mainSpec := fullUnsatWitnessSpec) 7
      ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩)
    _ _ _ _
    (fullSolveBytesCoreSpec_of_unsatWitness
      ⟨emp, by decide, by decide, rfl, rfl, rfl, by decide, by decide,
        by rw [sep_emp]; exact fullPayload_sep fullNvUnsatBytes (by decide),
        fun _ hu _ => ⟨rfl, hu⟩⟩)

/-! ## 3. Turn-key `166`-row `TableImpl` & `ModuleOk` assembly (`151/166` closed) -/

/-- Indices of the `6` ProbeTrans functions (`FullBridgeLemmas8a`, in flight). -/
def fullRemaining8aIndices : List Nat := [106, 107, 108, 109, 110, 111]

/-- Indices of the `9` Analyze/OTFS functions (`FullBridgeLemmas8b`, in flight). -/
def fullRemaining8bIndices : List Nat := [62, 63, 64, 66, 67, 68, 77, 78, 79]

private theorem impl_of_idx {Γ : Env} {tbl : List SpecEntry} {n : Nat} {fn : Fn} {e : SpecEntry}
    {idxs : List Nat}
    (h : ∀ k ∈ idxs, ∃ f r, fullFns[k]? = some f ∧ tbl[k]? = some r ∧ SpecEntry.Impl Γ f r)
    (hn : n ∈ idxs := by decide)
    (hf : fullFns[n]? = some fn := by rfl)
    (he : tbl[n]? = some e := by rfl) :
    SpecEntry.Impl Γ fn e := by
  obtain ⟨f, r, hf', he', himpl⟩ := h n hn
  cases Option.some.inj (hf.symm.trans hf')
  cases Option.some.inj (he.symm.trans he')
  exact himpl

private theorem tableImpl_drop_step {Γ : Env} {fs : List Fn} {tbl : List SpecEntry}
    {i : Nat} {fn : Fn} {e : SpecEntry}
    (hf : fs[i]? = some fn) (he : tbl[i]? = some e)
    (himpl : SpecEntry.Impl Γ fn e)
    (hrest : TableImpl Γ (fs.drop (i + 1)) (tbl.drop (i + 1))) :
    TableImpl Γ (fs.drop i) (tbl.drop i) := by
  have hfi : i < fs.length := (List.getElem?_eq_some_iff.mp hf).1
  have hei : i < tbl.length := (List.getElem?_eq_some_iff.mp he).1
  rw [List.drop_eq_getElem_cons hfi, List.drop_eq_getElem_cons hei]
  have hfe : fs[i]'hfi = fn := Option.some.inj ((List.getElem?_eq_getElem hfi).symm.trans hf)
  have hee : tbl[i]'hei = e := Option.some.inj ((List.getElem?_eq_getElem hei).symm.trans he)
  rw [hfe, hee]
  exact ⟨himpl, hrest⟩

private theorem full_table_drop_138
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    TableImpl (mkFullEnv mainSpec) (fullFns.drop 138) ((fullSpecTable mainSpec).drop 138) := by
  let Γ := mkFullEnv mainSpec
  let h7 := full_bridge_7_mk_ok mainSpec
  let h9 := full_bridge_9_mk_ok mainSpec hweaken
  let h10 := mkFullEnv_row_at (mainSpec := mainSpec) 10
    ⟨"full_rng_next", [i64], [i64], fullRngNextSpec, true⟩
  let h12 := mkFullEnv_row_at (mainSpec := mainSpec) 12
    ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], fullAllocClSpec, true⟩
  let h15 := mkFullEnv_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let h30 := mkFullEnv_row_at (mainSpec := mainSpec) 30
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let h49 := mkFullEnv_row_at (mainSpec := mainSpec) 49
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  let h94 := mkFullEnv_row_at (mainSpec := mainSpec) 94
    ⟨"full_extend_push2", [i64, i32, i32], [.bool], fullExtendPush2Spec, true⟩
  let h95 := mkFullEnv_row_at (mainSpec := mainSpec) 95
    ⟨"full_extend_push_cl", [i64, i32, i32], [.bool], fullExtendPushClSpec, true⟩
  let h98 := mkFullEnv_row_at (mainSpec := mainSpec) 98
    ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  let h100 := mkFullEnv_row_at (mainSpec := mainSpec) 100
    ⟨"full_delete_binary", [i64, i32, i32], [], fullDeleteBinarySpec, true⟩
  let h101 := mkFullEnv_row_at (mainSpec := mainSpec) 101
    ⟨"full_set_inactive", [i64, i32, i32], [], fullSetInactiveSpec, true⟩
  let h102 := mkFullEnv_row_at (mainSpec := mainSpec) 102
    ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  let h126 := mkFullEnv_row_at (mainSpec := mainSpec) 126
    ⟨"full_enter_dense", [i64], [.bool], fullEnterDenseSpec, true⟩
  let h127 := mkFullEnv_row_at (mainSpec := mainSpec) 127
    ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  let h138 := mkFullEnv_row_at (mainSpec := mainSpec) 138
    ⟨"full_sweep_add_cl", [i64, i64, i32, i32], [i64], fullSweepAddClSpec, true⟩
  let h139 := mkFullEnv_row_at (mainSpec := mainSpec) 139
    ⟨"full_sweep_cone", [i64, i32], [i64], fullSweepConeSpec, true⟩
  let h140 := mkFullEnv_row_at (mainSpec := mainSpec) 140
    ⟨"full_sweep_dpll", [i64, i32, i32, i32, i32], [i64], fullSweepDpllSpec, true⟩
  let h141 := mkFullEnv_row_at (mainSpec := mainSpec) 141
    ⟨"full_sweep_refine", [i64, i32, i32], [], fullSweepRefineSpec, true⟩
  let h142 := mkFullEnv_row_at (mainSpec := mainSpec) 142
    ⟨"full_sweep_seed_sim", [i64, i32, i32], [i32], fullSweepSeedSimSpec, true⟩
  let h143 := mkFullEnv_row_at (mainSpec := mainSpec) 143
    ⟨"full_sweep_var", [i64, i32], [i64], fullSweepVarSpec, true⟩
  let h148 := mkFullEnv_row_at (mainSpec := mainSpec) 148
    ⟨"full_bve_collect", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩
  let h149 := mkFullEnv_row_at (mainSpec := mainSpec) 149
    ⟨"full_bve_mark_and", [i64, i32, i32, i32, i32], [.bool], fullBveMarkAndSpec, true⟩
  let h150 := mkFullEnv_row_at (mainSpec := mainSpec) 150
    ⟨"full_bve_gates", [i64, i32, i32, i32], [], fullBveGatesSpec, true⟩
  let h151 := mkFullEnv_row_at (mainSpec := mainSpec) 151
    ⟨"full_bve_resolve_pair", [i64, i32, i32, i32], [.bool], fullBveResolvePairSpec, true⟩
  let h152 := mkFullEnv_row_at (mainSpec := mainSpec) 152
    ⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool], fullBveWeakenSpec, true⟩
  let h153 := mkFullEnv_row_at (mainSpec := mainSpec) 153
    ⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool], fullBveTryBceSpec, true⟩
  let h154 := mkFullEnv_row_at (mainSpec := mainSpec) 154
    ⟨"full_bve_commit_res", [i64, i64, i64], [i64], fullBveCommitResSpec, true⟩
  let h155 := mkFullEnv_row_at (mainSpec := mainSpec) 155
    ⟨"full_bve_ext_need", [i64, i32, i32], [i64], fullBveExtNeedSpec, true⟩
  refine tableImpl_drop_step rfl rfl (.of (full_sweep_add_cl_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_sweep_cone_bridge_wp Γ h138)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_sweep_dpll_bridge_wp Γ h10)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_sweep_refine_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_sweep_seed_sim_bridge_wp Γ h140 h141)) ?_
  refine tableImpl_drop_step rfl rfl
    (.of (full_sweep_var_bridge_wp Γ h139 h142 h140 h141 h102 h98)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_sweep_sat_bridge_wp Γ h30 h126 h143 h127 h49)) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 145) h7) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 146) h7) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 147) h7) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_bve_collect_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_bve_mark_and_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_bve_gates_bridge_wp Γ h149)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_bve_resolve_pair_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_bve_weaken_bridge_wp Γ h94 h100 h95)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_bve_try_bce_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_bve_commit_res_bridge_wp Γ h12 h15 h98 h102)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_bve_ext_need_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl
    (.of (full_bve_var_bridge_wp Γ h148 h155 h152 h101 h150 h151 h154 h153 h94 h100 h95)) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 157) h7) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 158) h7) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 159) h7) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 160) h9) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 161) h9) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 162) h9) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 163) h9) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 164) h9) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 165) h9) ?_
  trivial

private theorem full_table_drop_97
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X)
    (h8a : ∀ n ∈ fullRemaining8aIndices,
      ∃ fn row, fullFns[n]? = some fn ∧ (fullSpecTable mainSpec)[n]? = some row ∧
        SpecEntry.Impl (mkFullEnv mainSpec) fn row) :
    TableImpl (mkFullEnv mainSpec) (fullFns.drop 97) ((fullSpecTable mainSpec).drop 97) := by
  let Γ := mkFullEnv mainSpec
  let h7 := full_bridge_7_mk_ok mainSpec
  let h11 := mkFullEnv_row_at (mainSpec := mainSpec) 11
    ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  let h15 := mkFullEnv_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let h27 := mkFullEnv_row_at (mainSpec := mainSpec) 27
    ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
  let h28 := mkFullEnv_row_at (mainSpec := mainSpec) 28
    ⟨"full_assign", [i64, i32, i32], [], fullAssignSpec, true⟩
  let h30 := mkFullEnv_row_at (mainSpec := mainSpec) 30
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let h49 := mkFullEnv_row_at (mainSpec := mainSpec) 49
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  let h57 := mkFullEnv_row_at (mainSpec := mainSpec) 57
    ⟨"full_sweep_bins", [i64], [], fullSweepBinsSpec, true⟩
  let h60 := mkFullEnv_row_at (mainSpec := mainSpec) 60
    ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  let h82 := mkFullEnv_row_at (mainSpec := mainSpec) 82
    ⟨"full_analyze", [i64], [i64], fullAnalyzeSpec, true⟩
  let h94 := mkFullEnv_row_at (mainSpec := mainSpec) 94
    ⟨"full_extend_push2", [i64, i32, i32], [.bool], fullExtendPush2Spec, true⟩
  let h97 := mkFullEnv_row_at (mainSpec := mainSpec) 97
    ⟨"full_has_bin", [i64, i32, i32], [.bool], fullHasBinSpec, true⟩
  let h98 := mkFullEnv_row_at (mainSpec := mainSpec) 98
    ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  let h99 := mkFullEnv_row_at (mainSpec := mainSpec) 99
    ⟨"full_delete_bin_side", [i64, i32, i32], [], fullDeleteBinSideSpec, true⟩
  let h101 := mkFullEnv_row_at (mainSpec := mainSpec) 101
    ⟨"full_set_inactive", [i64, i32, i32], [], fullSetInactiveSpec, true⟩
  let h102 := mkFullEnv_row_at (mainSpec := mainSpec) 102
    ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  let h103 := mkFullEnv_row_at (mainSpec := mainSpec) 103
    ⟨"full_lucky_scan", [i64, .bool, .bool], [i64], fullLuckyScanSpec, true⟩
  let h104 := mkFullEnv_row_at (mainSpec := mainSpec) 104
    ⟨"full_lucky_polar", [i64], [i64], fullLuckyPolarSpec, true⟩
  let h120 := mkFullEnv_row_at (mainSpec := mainSpec) 120
    ⟨"full_tarjan_pop_scc", [i64, i32, i32, i32], [.bool], fullTarjanPopSccSpec, true⟩
  let h121 := mkFullEnv_row_at (mainSpec := mainSpec) 121
    ⟨"full_tarjan_scc", [i64], [i64], fullTarjanSccSpec, true⟩
  let h122 := mkFullEnv_row_at (mainSpec := mainSpec) 122
    ⟨"full_subst_elim_vars", [i64, i64], [.bool], fullSubstElimVarsSpec, true⟩
  let h123 := mkFullEnv_row_at (mainSpec := mainSpec) 123
    ⟨"full_subst_rewrite_bins", [i64], [.bool], fullSubstRewriteBinsSpec, true⟩
  let h124 := mkFullEnv_row_at (mainSpec := mainSpec) 124
    ⟨"full_subst_rewrite_ar", [i64], [.bool], fullSubstRewriteArSpec, true⟩
  let h126 := mkFullEnv_row_at (mainSpec := mainSpec) 126
    ⟨"full_enter_dense", [i64], [.bool], fullEnterDenseSpec, true⟩
  let h127 := mkFullEnv_row_at (mainSpec := mainSpec) 127
    ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  let h128 := mkFullEnv_row_at (mainSpec := mainSpec) 128
    ⟨"full_cong_find", [i64, i32], [i32], fullCongFindSpec, true⟩
  let h129 := mkFullEnv_row_at (mainSpec := mainSpec) 129
    ⟨"full_cong_merge", [i64, i32, i32], [.bool], fullCongMergeSpec, true⟩
  let h130 := mkFullEnv_row_at (mainSpec := mainSpec) 130
    ⟨"full_has_ternary", [i64, i32, i32, i32], [.bool], fullHasTernarySpec, true⟩
  let h131 := mkFullEnv_row_at (mainSpec := mainSpec) 131
    ⟨"full_sort_u32", [i64, i32], [], fullSortU32Spec, true⟩
  let h132 := mkFullEnv_row_at (mainSpec := mainSpec) 132
    ⟨"full_cong_extract_ite", [i64, i32, i32, i32, i64], [i64], fullCongExtractIteSpec, true⟩
  let h133 := mkFullEnv_row_at (mainSpec := mainSpec) 133
    ⟨"full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64], fullCongEmitXorSpec, true⟩
  let h134 := mkFullEnv_row_at (mainSpec := mainSpec) 134
    ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64], fullCongTryXorIteSpec, true⟩
  let h135 := mkFullEnv_row_at (mainSpec := mainSpec) 135
    ⟨"full_cong_extract", [i64, i64], [i64], fullCongExtractSpec, true⟩
  let h136 := mkFullEnv_row_at (mainSpec := mainSpec) 136
    ⟨"full_cong_hash_step", [i64, i64, i64, i64], [.bool], fullCongHashStepSpec, true⟩
  refine tableImpl_drop_step rfl rfl (.of (full_has_bin_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_add_bin_bridge_wp Γ h97 h27 h15)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_delete_bin_side_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_delete_binary_bridge_wp Γ h99)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_set_inactive_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_add_unit_bridge_wp Γ h30 h27)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_lucky_scan_bridge_wp Γ h28 h30 h49 h82)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_lucky_polar_bridge_wp Γ h11)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_lucky_bridge_wp Γ h104 h103 h28 h30 h49)) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 106) h8a) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 107) h8a) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 108) h8a) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 109) h8a) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 110) h8a) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 111) h8a) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 112) h7) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 113) h7) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 114) h7) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 115) h7) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 116) h7) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 117) h7) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 118) h7) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 119) h7) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_tarjan_pop_scc_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_tarjan_scc_bridge_wp Γ h120)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_subst_elim_vars_bridge_wp Γ h102 h49 h94 h101)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_subst_rewrite_bins_bridge_wp Γ h102 h98)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_subst_rewrite_ar_bridge_wp Γ h11 h102 h98)) ?_
  refine tableImpl_drop_step rfl rfl
    (.of (full_substitute_bridge_wp Γ h30 h121 h122 h123 h124 h60 h49)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_enter_dense_bridge_wp Γ h30 h57 h15 h60 h11)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_rebuild_watches_bridge_wp Γ h60 h49)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_cong_find_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_cong_merge_bridge_wp Γ h128 h98)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_has_ternary_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_sort_u32_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_cong_extract_ite_bridge_wp Γ h130)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_cong_emit_xor_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_cong_try_xor_ite_bridge_wp Γ h130 h133 h132)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_cong_extract_bridge_wp Γ h11 h97 h134)) ?_
  refine tableImpl_drop_step rfl rfl
    (.of (full_cong_hash_step_bridge_wp Γ h128 h131 h129 h102)) ?_
  refine tableImpl_drop_step rfl rfl
    (.of (full_congruence_bridge_wp Γ h30 h126 h135 h136 h127 h49)) ?_
  exact full_table_drop_138 mainSpec hweaken

private theorem full_table_drop_50
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X)
    (h8a : ∀ n ∈ fullRemaining8aIndices,
      ∃ fn row, fullFns[n]? = some fn ∧ (fullSpecTable mainSpec)[n]? = some row ∧
        SpecEntry.Impl (mkFullEnv mainSpec) fn row)
    (h8b : ∀ n ∈ fullRemaining8bIndices,
      ∃ fn row, fullFns[n]? = some fn ∧ (fullSpecTable mainSpec)[n]? = some row ∧
        SpecEntry.Impl (mkFullEnv mainSpec) fn row) :
    TableImpl (mkFullEnv mainSpec) (fullFns.drop 50) ((fullSpecTable mainSpec).drop 50) := by
  let Γ := mkFullEnv mainSpec
  let h8 := mkFullEnv_row_at (mainSpec := mainSpec) 8
    ⟨"full_isqrt", [i64], [i64], fullIsqrtSpec, true⟩
  let h9 := mkFullEnv_row_at (mainSpec := mainSpec) 9
    ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
  let h10 := mkFullEnv_row_at (mainSpec := mainSpec) 10
    ⟨"full_rng_next", [i64], [i64], fullRngNextSpec, true⟩
  let h11 := mkFullEnv_row_at (mainSpec := mainSpec) 11
    ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  let h14 := mkFullEnv_row_at (mainSpec := mainSpec) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  let h15 := mkFullEnv_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let h17 := mkFullEnv_row_at (mainSpec := mainSpec) 17
    ⟨"full_heap_down", [i64, i32], [], fullHeapDownSpec, true⟩
  let h19 := mkFullEnv_row_at (mainSpec := mainSpec) 19
    ⟨"full_heap_pop", [i64], [i64], fullHeapPopSpec, true⟩
  let h21 := mkFullEnv_row_at (mainSpec := mainSpec) 21
    ⟨"full_bump_var", [i64, i32], [], fullBumpVarSpec, true⟩
  let h22 := mkFullEnv_row_at (mainSpec := mainSpec) 22
    ⟨"full_bump_decay", [i64], [], fullBumpDecaySpec, true⟩
  let h24 := mkFullEnv_row_at (mainSpec := mainSpec) 24
    ⟨"full_queue_mtf", [i64, i32], [], fullQueueMtfSpec, true⟩
  let h25 := mkFullEnv_row_at (mainSpec := mainSpec) 25
    ⟨"full_tick_rel", [i64], [], fullTickRelSpec, true⟩
  let h26 := mkFullEnv_row_at (mainSpec := mainSpec) 26
    ⟨"full_ema_update", [i64, i64], [], fullEmaUpdateSpec, true⟩
  let h27 := mkFullEnv_row_at (mainSpec := mainSpec) 27
    ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
  let h28 := mkFullEnv_row_at (mainSpec := mainSpec) 28
    ⟨"full_assign", [i64, i32, i32], [], fullAssignSpec, true⟩
  let h30 := mkFullEnv_row_at (mainSpec := mainSpec) 30
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let h31 := mkFullEnv_row_at (mainSpec := mainSpec) 31
    ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], fullAddClauseSpec, true⟩
  let h49 := mkFullEnv_row_at (mainSpec := mainSpec) 49
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  let h50 := mkFullEnv_row_at (mainSpec := mainSpec) 50
    ⟨"full_recompute_tiers", [i64], [], fullRecomputeTiersSpec, true⟩
  let h51 := mkFullEnv_row_at (mainSpec := mainSpec) 51
    ⟨"full_mark_reasons", [i64, .bool], [], fullMarkReasonsSpec, true⟩
  let h52 := mkFullEnv_row_at (mainSpec := mainSpec) 52
    ⟨"full_red_less", [i64, i32, i32], [.bool], fullRedLessSpec, true⟩
  let h53 := mkFullEnv_row_at (mainSpec := mainSpec) 53
    ⟨"full_red_sift", [i64, i64, i64, i64], [], fullRedSiftSpec, true⟩
  let h54 := mkFullEnv_row_at (mainSpec := mainSpec) 54
    ⟨"full_sort_reds", [i64, i64], [], fullSortRedsSpec, true⟩
  let h55 := mkFullEnv_row_at (mainSpec := mainSpec) 55
    ⟨"full_lit_rank", [i64, i64, i32], [i64], fullLitRankSpec, true⟩
  let h57 := mkFullEnv_row_at (mainSpec := mainSpec) 57
    ⟨"full_sweep_bins", [i64], [], fullSweepBinsSpec, true⟩
  let h58 := mkFullEnv_row_at (mainSpec := mainSpec) 58
    ⟨"full_sweep_copy", [i64, i64, i64, i32, .bool], [i64], fullSweepCopySpec, true⟩
  let h59 := mkFullEnv_row_at (mainSpec := mainSpec) 59
    ⟨"full_rewatch_arena", [i64, i64], [.bool], fullRewatchArenaSpec, true⟩
  let h60 := mkFullEnv_row_at (mainSpec := mainSpec) 60
    ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  let h61 := mkFullEnv_row_at (mainSpec := mainSpec) 61
    ⟨"full_reduce", [i64, .bool], [i64], fullReduceSpec, true⟩
  let h69 := mkFullEnv_row_at (mainSpec := mainSpec) 69
    ⟨"full_min_mark", [i64, i32, i8], [], fullMinMarkSpec, true⟩
  let h70 := mkFullEnv_row_at (mainSpec := mainSpec) 70
    ⟨"full_min_lit", [i64, i32], [.bool], fullMinLitSpec, true⟩
  let h71 := mkFullEnv_row_at (mainSpec := mainSpec) 71
    ⟨"full_tmp_less", [i64, i64, i32, i32], [.bool], fullTmpLessSpec, true⟩
  let h72 := mkFullEnv_row_at (mainSpec := mainSpec) 72
    ⟨"full_sort_tmp_sift", [i64, i64, i64, i64, i64], [], fullSortTmpSiftSpec, true⟩
  let h73 := mkFullEnv_row_at (mainSpec := mainSpec) 73
    ⟨"full_sort_tmp", [i64], [], fullSortTmpSpec, true⟩
  let h74 := mkFullEnv_row_at (mainSpec := mainSpec) 74
    ⟨"full_shrink_lower", [i64, i32, i32], [.bool], fullShrinkLowerSpec, true⟩
  let h75 := mkFullEnv_row_at (mainSpec := mainSpec) 75
    ⟨"full_shrink_blk", [i64, i64, i64, i32, i64], [], fullShrinkBlkSpec, true⟩
  let h76 := mkFullEnv_row_at (mainSpec := mainSpec) 76
    ⟨"full_min_shrink", [i64], [], fullMinShrinkSpec, true⟩
  let h77 := mkFullEnv_row_at (mainSpec := mainSpec) 77
    ⟨"full_det_new_level", [i64, i64], [i64], fullDetNewLevelSpec, true⟩
  let h78 := mkFullEnv_row_at (mainSpec := mainSpec) 78
    ⟨"full_one_lit_confl", [i64], [i64], fullOneLitConflSpec, true⟩
  let h79 := mkFullEnv_row_at (mainSpec := mainSpec) 79
    ⟨"full_deduce_1uip", [i64], [i64], fullDeduce1uipSpec, true⟩
  let h80 := mkFullEnv_row_at (mainSpec := mainSpec) 80
    ⟨"full_eager_subsume", [i64, i64], [], fullEagerSubsumeSpec, true⟩
  let h81 := mkFullEnv_row_at (mainSpec := mainSpec) 81
    ⟨"full_learn_clause", [i64, i64], [i64], fullLearnClauseSpec, true⟩
  let h83 := mkFullEnv_row_at (mainSpec := mainSpec) 83
    ⟨"full_next_dec_var", [i64], [i64], fullNextDecVarSpec, true⟩
  let h86 := mkFullEnv_row_at (mainSpec := mainSpec) 86
    ⟨"full_walk_collect", [i64], [i64], fullWalkCollectSpec, true⟩
  let h87 := mkFullEnv_row_at (mainSpec := mainSpec) 87
    ⟨"full_walk_cl_sat", [i64, i64, i64], [.bool], fullWalkClSatSpec, true⟩
  let h88 := mkFullEnv_row_at (mainSpec := mainSpec) 88
    ⟨"full_walk_pick_lit", [i64, i64, i64], [i32], fullWalkPickLitSpec, true⟩
  let h89 := mkFullEnv_row_at (mainSpec := mainSpec) 89
    ⟨"full_walk", [i64], [], fullWalkSpec, true⟩
  refine tableImpl_drop_step rfl rfl (.of (full_recompute_tiers_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_mark_reasons_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_red_less_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_red_sift_bridge_wp Γ h52)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_sort_reds_bridge_wp Γ h53)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_lit_rank_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_unwatch_large_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_sweep_bins_bridge_wp Γ h14)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_sweep_copy_bridge_wp Γ h27 h15)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_rewatch_arena_bridge_wp Γ h55 h15)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_arena_sweep_bridge_wp Γ h57 h11 h58 h59)) ?_
  refine tableImpl_drop_step rfl rfl
    (.of (full_reduce_bridge_wp Γ h8 h9 h11 h50 h51 h54 h30 h49 h60)) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 62) h8b) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 63) h8b) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 64) h8b) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_bump_analyzed_bridge_wp Γ h21 h24 h22)) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 66) h8b) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 67) h8b) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 68) h8b) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_min_mark_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_min_lit_bridge_wp Γ h69)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_tmp_less_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_sort_tmp_sift_bridge_wp Γ h71)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_sort_tmp_bridge_wp Γ h72)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_shrink_lower_bridge_wp Γ h69 h70)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_shrink_blk_bridge_wp Γ h74 h69)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_min_shrink_bridge_wp Γ h73 h69 h70 h75)) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 77) h8b) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 78) h8b) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 79) h8b) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_eager_subsume_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl
    (.of (full_learn_clause_bridge_wp Γ h30 h27 h77 h14 h61 h31 h80)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_analyze_bridge_wp Γ h78 h79 h76 h25 h26 h81)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_next_dec_var_bridge_wp Γ h19)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_decide_bridge_wp Γ h83 h28)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_warmup_bridge_wp Γ h83 h28 h49 h30)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_walk_collect_bridge_wp Γ h11)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_walk_cl_sat_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_walk_pick_lit_bridge_wp Γ h10)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_walk_bridge_wp Γ h86 h87 h10 h88)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_rephase_bridge_wp Γ h30 h89 h9)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_switch_mode_bridge_wp Γ h17 h9)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_restart_due_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_restart_bridge_wp Γ h83 h30)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_extend_push2_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_extend_push_cl_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_extend_bridge_wp Γ)) ?_
  exact full_table_drop_97 mainSpec hweaken h8a

private theorem full_table_drop_8
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X)
    (h8a : ∀ n ∈ fullRemaining8aIndices,
      ∃ fn row, fullFns[n]? = some fn ∧ (fullSpecTable mainSpec)[n]? = some row ∧
        SpecEntry.Impl (mkFullEnv mainSpec) fn row)
    (h8b : ∀ n ∈ fullRemaining8bIndices,
      ∃ fn row, fullFns[n]? = some fn ∧ (fullSpecTable mainSpec)[n]? = some row ∧
        SpecEntry.Impl (mkFullEnv mainSpec) fn row) :
    TableImpl (mkFullEnv mainSpec) (fullFns.drop 8) ((fullSpecTable mainSpec).drop 8) := by
  let Γ := mkFullEnv mainSpec
  let h2 := mkFullEnv_row_at (mainSpec := mainSpec) 2
    ⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, true⟩
  let h5 := mkFullEnv_row_at (mainSpec := mainSpec) 5
    ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩
  let h6 := mkFullEnv_row_at (mainSpec := mainSpec) 6
    ⟨"kissat_next_lit", [i64, i64], [i64], kissatNextLitSpec, true⟩
  let h12 := mkFullEnv_row_at (mainSpec := mainSpec) 12
    ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], fullAllocClSpec, true⟩
  let h13 := mkFullEnv_row_at (mainSpec := mainSpec) 13
    ⟨"full_wsort_sift", [i64, i64, i64, i64], [], fullWsortSiftSpec, true⟩
  let h14 := mkFullEnv_row_at (mainSpec := mainSpec) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  let h15 := mkFullEnv_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let h16 := mkFullEnv_row_at (mainSpec := mainSpec) 16
    ⟨"full_heap_up", [i64, i32], [], fullHeapUpSpec, true⟩
  let h17 := mkFullEnv_row_at (mainSpec := mainSpec) 17
    ⟨"full_heap_down", [i64, i32], [], fullHeapDownSpec, true⟩
  let h18 := mkFullEnv_row_at (mainSpec := mainSpec) 18
    ⟨"full_heap_push", [i64, i32], [], fullHeapPushSpec, true⟩
  let h20 := mkFullEnv_row_at (mainSpec := mainSpec) 20
    ⟨"full_rescale", [i64], [], fullRescaleSpec, true⟩
  let h23 := mkFullEnv_row_at (mainSpec := mainSpec) 23
    ⟨"full_queue_renumber", [i64], [], fullQueueRenumberSpec, true⟩
  let h27 := mkFullEnv_row_at (mainSpec := mainSpec) 27
    ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
  let h29 := mkFullEnv_row_at (mainSpec := mainSpec) 29
    ⟨"full_save_target_best", [i64], [], fullSaveTargetBestSpec, true⟩
  let h31 := mkFullEnv_row_at (mainSpec := mainSpec) 31
    ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], fullAddClauseSpec, true⟩
  let h32 := mkFullEnv_row_at (mainSpec := mainSpec) 32
    ⟨"full_zero_tables1", [i64], [], fullZeroTables1Spec, true⟩
  let h33 := mkFullEnv_row_at (mainSpec := mainSpec) 33
    ⟨"full_zero_tables2", [i64], [], fullZeroTables2Spec, true⟩
  let h34 := mkFullEnv_row_at (mainSpec := mainSpec) 34
    ⟨"full_fixed_bytes", [i64], [i64], fullFixedBytesSpec, true⟩
  let h35 := mkFullEnv_row_at (mainSpec := mainSpec) 35
    ⟨"full_init_ptrs", [i64, i64, i64], [], fullInitPtrsSpec, true⟩
  let h36 := mkFullEnv_row_at (mainSpec := mainSpec) 36
    ⟨"full_init_hdr", [i64, i64, i64, i64], [], fullInitHdrSpec, true⟩
  let h37 := mkFullEnv_row_at (mainSpec := mainSpec) 37
    ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], fullCalcMaxVSpec, true⟩
  let h38 := mkFullEnv_row_at (mainSpec := mainSpec) 38
    ⟨"full_calc_ext_cap", [i64], [i64], fullCalcExtCapSpec, true⟩
  let h39 := mkFullEnv_row_at (mainSpec := mainSpec) 39
    ⟨"full_calc_scr_cap", [i64], [i64], fullCalcScrCapSpec, true⟩
  let h40 := mkFullEnv_row_at (mainSpec := mainSpec) 40
    ⟨"full_init_arenas", [i64, i64, i64, i64], [], fullInitArenasSpec, true⟩
  let h42 := mkFullEnv_row_at (mainSpec := mainSpec) 42
    ⟨"full_skip_cl", [i64, i64], [.bool], fullSkipClSpec, true⟩
  let h43 := mkFullEnv_row_at (mainSpec := mainSpec) 43
    ⟨"full_ingest_cl", [i64, i64], [i64], fullIngestClSpec, true⟩
  let h45 := mkFullEnv_row_at (mainSpec := mainSpec) 45
    ⟨"full_find_repl", [i64, i64], [i64], fullFindReplSpec, true⟩
  let h46 := mkFullEnv_row_at (mainSpec := mainSpec) 46
    ⟨"full_assign_level", [i64, i32, i32], [i32], fullAssignLevelSpec, true⟩
  let h47 := mkFullEnv_row_at (mainSpec := mainSpec) 47
    ⟨"full_prop_lit", [i64, i32, i64], [.bool], fullPropLitSpec, true⟩
  let h48 := mkFullEnv_row_at (mainSpec := mainSpec) 48
    ⟨"full_propagate_ignore", [i64, i64], [i64], fullPropagateIgnoreSpec, true⟩
  refine tableImpl_drop_step rfl rfl (.of (full_isqrt_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_ilog10_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_rng_next_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_arena_next_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_alloc_cl_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_wsort_sift_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_wstack_defrag_bridge_wp Γ h13)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_watch_push_bridge_wp Γ h14)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_heap_up_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_heap_down_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_heap_push_bridge_wp Γ h16)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_heap_pop_bridge_wp Γ h17)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_rescale_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_bump_var_bridge_wp Γ h16 h20)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_bump_decay_bridge_wp Γ h20)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_queue_renumber_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_queue_mtf_bridge_wp Γ h23)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_tick_rel_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_ema_update_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_assign_lvl_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_assign_bridge_wp Γ h27)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_save_target_best_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_backtrack_bridge_wp Γ h29 h18)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_add_clause_bridge_wp Γ h12 h15)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_zero_tables1_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_zero_tables2_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_fixed_bytes_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_init_ptrs_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_init_hdr_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_calc_max_v_bridge_wp Γ h34)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_calc_ext_cap_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_calc_scr_cap_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_init_arenas_bridge_wp Γ h35)) ?_
  refine tableImpl_drop_step rfl rfl
    (.of (full_init_state_bridge_wp Γ h5 h34 h37 h38 h39 h40 h36 h32 h33)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_skip_cl_bridge_wp Γ h6)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_ingest_cl_bridge_wp Γ h6 h27 h31)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_parse_body_bridge_wp Γ h42 h43 h2)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_find_repl_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_assign_level_bridge_wp Γ)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_prop_lit_bridge_wp Γ h45 h15 h27 h46)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_propagate_ignore_bridge_wp Γ h47)) ?_
  refine tableImpl_drop_step rfl rfl (.of (full_propagate_bridge_wp Γ h48)) ?_
  exact full_table_drop_50 mainSpec hweaken h8a h8b

/-- Row-by-row `TableImpl` for all `166` functions in `fullFns` against `fullSpecTable mainSpec`,
discharging `151 / 166` rows unconditionally and parameterized strictly by `8a` (`6` ProbeTrans)
and `8b` (`9` Analyze/OTFS). -/
theorem mkFullEnv_tableImpl_of_missing
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X)
    (h8a : ∀ n ∈ fullRemaining8aIndices,
      ∃ fn row, fullFns[n]? = some fn ∧ (fullSpecTable mainSpec)[n]? = some row ∧
        SpecEntry.Impl (mkFullEnv mainSpec) fn row)
    (h8b : ∀ n ∈ fullRemaining8bIndices,
      ∃ fn row, fullFns[n]? = some fn ∧ (fullSpecTable mainSpec)[n]? = some row ∧
        SpecEntry.Impl (mkFullEnv mainSpec) fn row) :
    TableImpl (mkFullEnv mainSpec) fullFns (fullSpecTable mainSpec) := by
  let h7 := full_bridge_7_mk_ok mainSpec
  change TableImpl (mkFullEnv mainSpec) (fullFns.drop 0) ((fullSpecTable mainSpec).drop 0)
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 0) h7) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 1) h7) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 2) h7) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 3) h7) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 4) h7) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 5) h7) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 6) h7) ?_
  refine tableImpl_drop_step rfl rfl (impl_of_idx (n := 7) h7) ?_
  exact full_table_drop_8 mainSpec hweaken h8a h8b

/-- Turn-key `ModuleOk` assembly for `mkFullEnv mainSpec` on `fullModule` (`151/166` closed). -/
theorem mkFullEnv_moduleOk_of_missing
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X)
    (h8a : ∀ n ∈ fullRemaining8aIndices,
      ∃ fn row, fullFns[n]? = some fn ∧ (fullSpecTable mainSpec)[n]? = some row ∧
        SpecEntry.Impl (mkFullEnv mainSpec) fn row)
    (h8b : ∀ n ∈ fullRemaining8bIndices,
      ∃ fn row, fullFns[n]? = some fn ∧ (fullSpecTable mainSpec)[n]? = some row ∧
        SpecEntry.Impl (mkFullEnv mainSpec) fn row) :
    ModuleOk (mkFullEnv mainSpec) fullModule :=
  Env.ofTable_moduleOk full_acyclic (allFns_of_forall fullFns_wf)
    (mkFullEnv_tableImpl_of_missing mainSpec hweaken h8a h8b)

/-- Turn-key `ModuleOk fullEnv fullModule` (`151/166` closed; plug in `8a` & `8b` in Phase 2). -/
theorem fullEnv_moduleOk_of_missing
    (h8a : ∀ n ∈ fullRemaining8aIndices,
      ∃ fn row, fullFns[n]? = some fn ∧ (fullSpecTable fullSolveBytesSpec)[n]? = some row ∧
        SpecEntry.Impl fullEnv fn row)
    (h8b : ∀ n ∈ fullRemaining8bIndices,
      ∃ fn row, fullFns[n]? = some fn ∧ (fullSpecTable fullSolveBytesSpec)[n]? = some row ∧
        SpecEntry.Impl fullEnv fn row) :
    ModuleOk fullEnv fullModule :=
  mkFullEnv_moduleOk_of_missing fullSolveBytesSpec
    (fun _ _ _ _ => fullSolveBytesCoreSpec_of_spec) h8a h8b

/-- Turn-key `ModuleOk fullUnsatEnv fullModule` (`151/166` closed). -/
theorem fullUnsatEnv_modOk_rem
    (h8a : ∀ n ∈ fullRemaining8aIndices,
      ∃ fn row, fullFns[n]? = some fn ∧ (fullSpecTable fullUnsatWitnessSpec)[n]? = some row ∧
        SpecEntry.Impl fullUnsatEnv fn row)
    (h8b : ∀ n ∈ fullRemaining8bIndices,
      ∃ fn row, fullFns[n]? = some fn ∧ (fullSpecTable fullUnsatWitnessSpec)[n]? = some row ∧
        SpecEntry.Impl fullUnsatEnv fn row) :
    ModuleOk fullUnsatEnv fullModule :=
  mkFullEnv_moduleOk_of_missing fullUnsatWitnessSpec
    (fun _ _ _ _ => fullSolveBytesCoreSpec_of_unsatWitness) h8a h8b

private theorem full_remaining_8b_of_79
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (h79 : ∃ fn row, fullFns[79]? = some fn ∧ (fullSpecTable mainSpec)[79]? = some row ∧
      SpecEntry.Impl (mkFullEnv mainSpec) fn row) :
    ∀ n ∈ fullRemaining8bIndices,
      ∃ fn row, fullFns[n]? = some fn ∧ (fullSpecTable mainSpec)[n]? = some row ∧
        SpecEntry.Impl (mkFullEnv mainSpec) fn row := by
  intro n hn
  simp only [fullRemaining8bIndices, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_bridge_8b_mk_ok mainSpec 62 (by simp [fullBridge8bIndices])
  · exact full_bridge_8b_mk_ok mainSpec 63 (by simp [fullBridge8bIndices])
  · exact full_bridge_8b_mk_ok mainSpec 64 (by simp [fullBridge8bIndices])
  · exact full_bridge_8b_mk_ok mainSpec 66 (by simp [fullBridge8bIndices])
  · exact full_bridge_8b_mk_ok mainSpec 67 (by simp [fullBridge8bIndices])
  · exact full_bridge_8b_mk_ok mainSpec 68 (by simp [fullBridge8bIndices])
  · exact full_bridge_8b_mk_ok mainSpec 77 (by simp [fullBridge8bIndices])
  · exact full_one_lit_confl_mk_ok mainSpec
  · exact h79

/-- `ModuleOk` assembly for `mkFullEnv mainSpec` on `fullModule` discharging `165/166` rows
unconditionally and parameterized strictly by row `[79]` (`full_deduce_1uip`). -/
theorem mkFullEnv_moduleOk_of_79
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X)
    (h79 : ∃ fn row, fullFns[79]? = some fn ∧ (fullSpecTable mainSpec)[79]? = some row ∧
      SpecEntry.Impl (mkFullEnv mainSpec) fn row) :
    ModuleOk (mkFullEnv mainSpec) fullModule :=
  mkFullEnv_moduleOk_of_missing mainSpec hweaken (full_bridge_8a_mk_ok mainSpec)
    (full_remaining_8b_of_79 mainSpec h79)

/-- `ModuleOk fullEnv fullModule` discharging `165/166` rows, parameterized only by `[79]`. -/
theorem fullEnv_moduleOk_of_79
    (h79 : ∃ fn row, fullFns[79]? = some fn ∧
      (fullSpecTable fullSolveBytesSpec)[79]? = some row ∧
      SpecEntry.Impl fullEnv fn row) :
    ModuleOk fullEnv fullModule :=
  mkFullEnv_moduleOk_of_79 fullSolveBytesSpec
    (fun _ _ _ _ => fullSolveBytesCoreSpec_of_spec) h79

/-- `ModuleOk fullUnsatEnv fullModule` discharging `165/166` rows, parameterized only by `[79]`. -/
theorem fullUnsatEnv_moduleOk_of_79
    (h79 : ∃ fn row, fullFns[79]? = some fn ∧
      (fullSpecTable fullUnsatWitnessSpec)[79]? = some row ∧
      SpecEntry.Impl fullUnsatEnv fn row) :
    ModuleOk fullUnsatEnv fullModule :=
  mkFullEnv_moduleOk_of_79 fullUnsatWitnessSpec
    (fun _ _ _ _ => fullSolveBytesCoreSpec_of_unsatWitness) h79

end LeanQbe.T.Examples.Kissat.Full
