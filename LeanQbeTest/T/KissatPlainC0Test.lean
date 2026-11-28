module

public import LeanQbe.T.Examples.Kissat.Plain
public import LeanQbe.T.Examples.Kissat.PlainArena
public import LeanQbe.T.Examples.Kissat.PlainSpec
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
public import LeanQbeTest.T.KissatC0Harness
meta import LeanQbe.T.Examples.Kissat.Plain
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal
meta import LeanQbeTest.T.KissatC0Harness

/-!
# Verification, Axiom Audit, and Differential Suite for `Kissat` `D-Plain`

* Checks `plainModule.checkAcyclic`, `PrintCpp`, `PrintQbe`, and `Legal` emission across
  `aarch64` / `scalar64` / `x64AVX2`.
* Single-line `#print axioms` audit (`[propext, Classical.choice, Quot.sound]`).
* Cross-checks pure-Lean `cdclSolve` on core SAT/UNSAT/edge DIMACS cases and exercises
  `COMPACT` arena, binary+blocking watches, `reduce`/`collect` GC, VMTF+VSIDS mode
  switching, rephasing, Luby+EMA restarts, `lucky` checks, `shrink`, and `minimize`.
* Emits `plain_gen.hpp`, `plain.ssa`, `plain_driver.cpp`, and `plain_cases.h`.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.KissatPlainC0Test

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Plain
open LeanQbe.T.Examples.LratBytes
open LeanQbeTest.T.KissatC0Harness

/-! ## 1. Static Checks & Axiom Audit -/

#guard plainModule.checkAcyclic == true
#guard plain1Module.checkAcyclic == true
#guard plainModule.exits.isEmpty && plainModule.externs.isEmpty
#guard plain1_fns.length == 31
#guard plain2_fns.length == 20
#guard plainFns.length == 59
#guard (ppTModule plainModule).isOk
#guard (PrintQbe.module plainModule).isOk
#guard (ppModule (plainFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (plainFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (plainFns.map (Fn.legal .x64AVX2))).isOk

example : (plainSpecTable plainSolveBytesSpec).length = 59 := rfl

example : ∀ e ∈ plainSpecTable plainSolveBytesSpec, e.noExit = true :=
  plainSpecTable_noExit plainSolveBytesSpec

example : (plainSpecTable plainSolveBytesSpec).map (fun e => (e.name, e.as, e.rs)) =
    plainFns.map (fun f => (f.name, f.as, f.rs)) :=
  plainSpecTable_sigs plainSolveBytesSpec

example : Env := mkPlainEnv plainSolveBytesCoreSpec
example : Env := plainEnv

example {args m Q X} (h : plainSolveBytesSpec args m Q X) :
    plainSolveBytesCoreSpec args m Q X :=
  plainSolveBytesCoreSpec_of_spec h

example {c F0 s} (h : PlainCoreInv c F0 s) (hall : ∀ v < c.mv, s.vals[2 * v]?.getD 0#8 ≠ 0#8) :
    c.mv ≤ s.trail_end :=
  h.mv_le_te hall

#print axioms LeanQbe.T.Examples.Kissat.Plain.plain1_fns_wf
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain2_fns_wf
#print axioms LeanQbe.T.Examples.Kissat.Plain.plainFns_wf
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain1_acyclic
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_acyclic
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_prop_lit_wf
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_sweep_wf
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_reduce_wf
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_min_lit_wf
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_shrink_blk_wf
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_min_shrk_wf
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_analyze_wf
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_decide_wf
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_lucky_wf
#print axioms LeanQbe.T.Examples.Kissat.Plain.kissat_solve_bytes_wf
#print axioms LeanQbe.T.Examples.Kissat.Plain.PlainCfg.regions_to_avail
#print axioms LeanQbe.T.Examples.Kissat.Plain.load_arena_mv
#print axioms LeanQbe.T.Examples.Kissat.Plain.store_arena_arena
#print axioms LeanQbe.T.Examples.Kissat.Plain.assign_preserves_core
#print axioms LeanQbe.T.Examples.Kissat.Plain.addClause_preserves_core
#print axioms LeanQbe.T.Examples.Kissat.Plain.swapCl_preserves_core
#print axioms LeanQbe.T.Examples.Kissat.Plain.plainInv_init
#print axioms LeanQbe.T.Examples.Kissat.Plain.plainMinMark_entails
#print axioms LeanQbe.T.Examples.Kissat.Plain.plainSpecTable_noExit
#print axioms LeanQbe.T.Examples.Kissat.Plain.plainSpecTable_sigs

/-! ## 2. Test Corpus (59 Cases) -/

private def corpus : List KissatCase :=
  let nvStr := String.fromUTF8! nvDimacsBytes.toByteArray
  let php32 := mkPhpDimacs 3 2
  let php43 := mkPhpDimacs 4 3
  let php54 := mkPhpDimacs 5 4
  let sat3_8 := mkPlanted3Sat 8 28 42
  let sat3_10 := mkPlanted3Sat 10 36 1337
  let sat3_12 := mkPlanted3Sat 12 44 98765
  let sat3_15 := mkPlanted3Sat 15 54 202611
  let sat3_22 := mkPlanted3Sat 22 88 777111
  [ ⟨"empty_cnf_0", "p cnf 0 0\n", 2048, 100, 10, 0, true⟩
  , ⟨"empty_cnf_3", "p cnf 3 0\n", 4096, 100, 10, 0, true⟩
  , ⟨"empty_clause_only", "p cnf 2 1\n0\n", 4096, 100, 20, 0, true⟩
  , ⟨"empty_clause_second", "p cnf 2 2\n1 2 0\n0\n", 4096, 100, 20, 0, true⟩
  , ⟨"nv_unsat", nvStr, 4096, 100, 20, 0, true⟩
  , ⟨"single_unit_sat", "p cnf 1 1\n1 0\n", 4096, 100, 10, 0, true⟩
  , ⟨"neg_unit_sat", "p cnf 2 1\n-2 0\n", 4096, 100, 10, 0, true⟩
  , ⟨"tautology_sat", "p cnf 2 2\n1 -1 2 0\n-2 0\n", 4096, 100, 10, 0, true⟩
  , ⟨"tautology_unsat", "p cnf 1 3\n1 -1 0\n1 0\n-1 0\n", 4096, 100, 20, 0, true⟩
  , ⟨"dup_lits_sat", "p cnf 2 2\n1 1 2 2 0\n-1 -1 0\n", 4096, 100, 10, 0, true⟩
  , ⟨"dup_lits_unsat", "p cnf 1 2\n1 1 0\n-1 -1 0\n", 4096, 100, 20, 0, true⟩
  , ⟨"dup_neg_taut", "p cnf 3 3\n1 2 -1 0\n2 2 3 0\n-2 -3 0\n", 4096, 100, 10, 0, true⟩
  , ⟨"impl_chain_sat", mkImplChain 8 false, 4096, 500, 10, 0, true⟩
  , ⟨"impl_chain_unsat", mkImplChain 8 true, 4096, 500, 20, 0, true⟩
  , ⟨"two_wl_long_sat", mkLongClause 7 false, 4096, 500, 10, 0, true⟩
  , ⟨"two_wl_long_unsat", mkLongClause 7 true, 4096, 500, 20, 0, true⟩
  , ⟨"two_wl_backtrack_unsat", mk2WlBacktrackUnsat, 4096, 1000, 20, 0, true⟩
  , ⟨"uip1_diamond_unsat", mk1UipDiamondUnsat, 4096, 1000, 20, 0, true⟩
  , ⟨"min_diamond_unsat", mkMinDiamondUnsat, 8192, 2000, 20, 0, true⟩
  , ⟨"shrink_bin_unsat", mkShrinkBinaryUnsat, 8192, 2000, 20, 0, true⟩
  , ⟨"lucky_all_pos_sat", mkLuckyPosSat, 4096, 500, 10, 0, true⟩
  , ⟨"lucky_all_neg_sat", mkLuckyNegSat, 4096, 500, 10, 0, true⟩
  , ⟨"root_unit_1uip_unsat", mkRootUnitMixed1Uip true, 4096, 1000, 20, 0, true⟩
  , ⟨"root_unit_1uip_sat", mkRootUnitMixed1Uip false, 4096, 1000, 10, 0, true⟩
  , ⟨"unsat_2sat_cycle", mk2SatCycleUnsat, 4096, 1000, 20, 0, true⟩
  , ⟨"unsat_all_3var", mkAllCubeDimacs 3, 4096, 1000, 20, 0, true⟩
  , ⟨"unsat_parity_4var", mkParity4Unsat, 8192, 2000, 20, 0, true⟩
  , ⟨"php_3_2", php32, 8192, 2000, 20, 0, true⟩
  , ⟨"php_4_3", php43, 32768, 20000, 20, 0, true⟩
  , ⟨"php_5_4", php54, 131072, 200000, 20, 0, false⟩
  , ⟨"ordering_4", mkOrdering4, 16384, 20000, 20, 0, false⟩
  , ⟨"sat_3sat_5v", mkPlanted3Sat 5 12 7, 4096, 500, 10, 0, true⟩
  , ⟨"sat_3sat_8v", sat3_8, 8192, 2000, 10, 0, true⟩
  , ⟨"sat_3sat_10v", sat3_10, 16384, 5000, 10, 0, true⟩
  , ⟨"sat_3sat_12v", sat3_12, 16384, 10000, 10, 0, true⟩
  , ⟨"sat_3sat_15v", sat3_15, 32768, 20000, 10, 0, true⟩
  , ⟨"sat_3sat_22v", sat3_22, 65536, 50000, 10, 0, false⟩
  , ⟨"sat_horn_8v", mkHornSat, 4096, 500, 10, 0, true⟩
  , ⟨"analyze_reduce_flush_sat", mkAnalyzeReduceFlushSat, 4984, 2000, 10, 0, true⟩
  , ⟨"sat_comments_crlf",
      "c hdr\r\nc 2\n  p \t cnf  2  2 \r\n1 -2 0 c inline\n2 0\nc eof",
      4096, 100, 10, 0, true⟩
  , ⟨"sat_unaligned_work", sat3_8, 8195, 2000, 10, 0, true⟩
  , ⟨"fuel_0_nv", nvStr, 4096, 0, 0, 0, false⟩
  , ⟨"fuel_1_php32", php32, 8192, 1, 0, 0, false⟩
  , ⟨"fuel_1_sat3", sat3_8, 8192, 1, 0, 0, false⟩
  , ⟨"fuel_2_php43", php43, 32768, 2, 0, 0, false⟩
  , ⟨"tiny_work_0", nvStr, 0, 100, 0, 0, false⟩
  , ⟨"tiny_work_127", nvStr, 127, 100, 0, 0, false⟩
  , ⟨"tiny_work_767", nvStr, 767, 100, 0, 0, false⟩
  , ⟨"tiny_work_1100", nvStr, 1100, 100, 0, 0, false⟩
  , ⟨"tiny_work_php32_oom", php32, 1600, 1000, 0, 0, false⟩
  , ⟨"bad_empty", "", 4096, 100, 0, 0, false⟩
  , ⟨"bad_hdr_sat", "p sat 1 2\n1 0\n-1 0\n", 4096, 100, 0, 0, false⟩
  , ⟨"bad_oob_var", "p cnf 1 2\n2 0\n-1 0\n", 4096, 100, 0, 0, false⟩
  , ⟨"bad_neg_zero", "p cnf 1 1\n-0 0\n", 4096, 100, 0, 0, false⟩
  , ⟨"bad_missing_zero", "p cnf 1 1\n1", 4096, 100, 0, 0, false⟩
  , ⟨"bad_trailing_garbage", "p cnf 1 1\n0\nextra\n", 4096, 100, 0, 0, false⟩
  , ⟨"bad_unsat_then_garbage", "p cnf 1 2\n0\nextra\n", 4096, 100, 0, 0, false⟩
  , ⟨"bad_too_few_clauses", "p cnf 1 2\n1 0\n", 4096, 100, 0, 0, false⟩
  , ⟨"bad_var_overflow", "p cnf 268435456 1\n0\n", 4096, 100, 0, 0, false⟩
  ]

#guard corpus.length == 59
#guard corpus.all checkLayerACase
#guard checkLayerACase ⟨"fuel_0_check", "p cnf 1 2\n1 0\n-1 0\n", 4096, 0, 0, 0, false⟩

/-! ## 3. Artifact Generator (`plain_gen.hpp`, `plain.ssa`, `plain_cases.h`) -/

def generateArtifacts (outDir : System.FilePath) : IO UInt32 :=
  writeC0Artifacts outDir plainModule corpus "plain"
    (mkBasicDiffDriverCpp "plain_gen.hpp" "plain_cases.h" "plain") false "Plain"

end LeanQbeTest.T.KissatPlainC0Test

public def main (args : List String) : IO UInt32 :=
  LeanQbeTest.T.KissatPlainC0Test.generateArtifacts
    (args.headD "/tmp/leanqbe-kissat-plain")
