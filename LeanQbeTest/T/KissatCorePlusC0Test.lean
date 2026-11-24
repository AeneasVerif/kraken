module

public import LeanQbe.T.Examples.Kissat.CorePlus
public import LeanQbe.T.Examples.Kissat.CorePlusArena
public import LeanQbe.T.Examples.Kissat.CorePlusSpec
public import LeanQbe.T.Examples.Kissat.Core
public import LeanQbe.T.Examples.Kissat.CoreLemmas
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
public import LeanQbeTest.T.KissatC0Harness
meta import LeanQbe.T.Examples.Kissat.CorePlus
meta import LeanQbe.T.Examples.Kissat.Core
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal
meta import LeanQbeTest.T.KissatC0Harness

/-!
# Verification, Axiom Audit, and Differential Suite for `Kissat` `D-Core+`

* Checks `coreplusModule.checkAcyclic`, `PrintCpp`, `PrintQbe`, and `Legal` emission across
  `aarch64` / `scalar64` / `x64AVX2`.
* Single-line `#print axioms` audit (`[propext, Classical.choice, Quot.sound]`).
* Cross-checks pure-Lean `cdclSolve` on core SAT/UNSAT/edge DIMACS cases and exercises
  minimization, EVSIDS heap, phase saving, and reluctant restarts in C++/x64/Arm64.
* Emits `coreplus_gen.hpp`, `coreplus.ssa`, `coreplus_driver.cpp`, and `coreplus_cases.h`.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.KissatCorePlusC0Test

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.CorePlus
open LeanQbe.T.Examples.LratBytes
open LeanQbeTest.T.KissatC0Harness

/-! ## 1. Static Checks & Axiom Audit -/

#guard coreplusModule.checkAcyclic == true
#guard coreplusModule.exits.isEmpty && coreplusModule.externs.isEmpty
#guard coreplus_fns.length == 28
#guard coreplusFns.length == 36
#guard (ppTModule coreplusModule).isOk
#guard (PrintQbe.module coreplusModule).isOk
#guard (ppModule (coreplusFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (coreplusFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (coreplusFns.map (Fn.legal .x64AVX2))).isOk

#print axioms LeanQbe.T.Examples.Kissat.CorePlus.coreplus_fns_wf
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.coreplusFns_wf
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.coreplus_acyclic
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_heap_sift_up_wf
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_heap_pop_max_wf
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_bump_var_wf
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_tick_reluctant_wf
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_minimize_lit_wf
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_minimize_clause_wf
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_analyze_wf
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_decide_wf
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_solve_bytes_wf
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.entails_of_minMarkInv

/-! ## 2. Test Corpus (54 Cases) -/

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
  [ ⟨"empty_cnf_0", "p cnf 0 0\n", 1024, 100, 10, 0, true⟩
  , ⟨"empty_cnf_3", "p cnf 3 0\n", 1024, 100, 10, 0, true⟩
  , ⟨"empty_clause_only", "p cnf 2 1\n0\n", 1024, 100, 20, 0, true⟩
  , ⟨"empty_clause_second", "p cnf 2 2\n1 2 0\n0\n", 1024, 100, 20, 0, true⟩
  , ⟨"nv_unsat", nvStr, 1024, 100, 20, 0, true⟩
  , ⟨"single_unit_sat", "p cnf 1 1\n1 0\n", 1024, 100, 10, 0, true⟩
  , ⟨"neg_unit_sat", "p cnf 2 1\n-2 0\n", 1024, 100, 10, 0, true⟩
  , ⟨"tautology_sat", "p cnf 2 2\n1 -1 2 0\n-2 0\n", 1024, 100, 10, 0, true⟩
  , ⟨"tautology_unsat", "p cnf 1 3\n1 -1 0\n1 0\n-1 0\n", 1024, 100, 20, 0, true⟩
  , ⟨"dup_lits_sat", "p cnf 2 2\n1 1 2 2 0\n-1 -1 0\n", 1024, 100, 10, 0, true⟩
  , ⟨"dup_lits_unsat", "p cnf 1 2\n1 1 0\n-1 -1 0\n", 1024, 100, 20, 0, true⟩
  , ⟨"dup_neg_taut", "p cnf 3 3\n1 2 -1 0\n2 2 3 0\n-2 -3 0\n", 1024, 100, 10, 0, true⟩
  , ⟨"impl_chain_sat", mkImplChain 8 false, 4096, 500, 10, 0, true⟩
  , ⟨"impl_chain_unsat", mkImplChain 8 true, 4096, 500, 20, 0, true⟩
  , ⟨"two_wl_long_sat", mkLongClause 7 false, 4096, 500, 10, 0, true⟩
  , ⟨"two_wl_long_unsat", mkLongClause 7 true, 4096, 500, 20, 0, true⟩
  , ⟨"two_wl_backtrack_unsat", mk2WlBacktrackUnsat, 4096, 1000, 20, 0, true⟩
  , ⟨"uip1_diamond_unsat", mk1UipDiamondUnsat, 4096, 1000, 20, 0, true⟩
  , ⟨"min_diamond_unsat", mkMinDiamondUnsat, 4096, 2000, 20, 0, true⟩
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
  , ⟨"sat_comments_crlf",
      "c hdr\r\nc 2\n  p \t cnf  2  2 \r\n1 -2 0 c inline\n2 0\nc eof",
      1024, 100, 10, 0, true⟩
  , ⟨"sat_unaligned_work", sat3_8, 8195, 2000, 10, 0, true⟩
  , ⟨"fuel_0_nv", nvStr, 1024, 0, 0, 0, false⟩
  , ⟨"fuel_1_php32", php32, 8192, 1, 0, 0, false⟩
  , ⟨"fuel_1_sat3", sat3_8, 8192, 1, 0, 0, false⟩
  , ⟨"fuel_2_php43", php43, 32768, 2, 0, 0, false⟩
  , ⟨"tiny_work_0", nvStr, 0, 100, 0, 0, false⟩
  , ⟨"tiny_work_127", nvStr, 127, 100, 0, 0, false⟩
  , ⟨"tiny_work_359", nvStr, 359, 100, 0, 0, false⟩
  , ⟨"tiny_work_php32_oom", php32, 600, 1000, 0, 0, false⟩
  , ⟨"bad_empty", "", 1024, 100, 0, 0, false⟩
  , ⟨"bad_hdr_sat", "p sat 1 2\n1 0\n-1 0\n", 1024, 100, 0, 0, false⟩
  , ⟨"bad_oob_var", "p cnf 1 2\n2 0\n-1 0\n", 1024, 100, 0, 0, false⟩
  , ⟨"bad_neg_zero", "p cnf 1 1\n-0 0\n", 1024, 100, 0, 0, false⟩
  , ⟨"bad_missing_zero", "p cnf 1 1\n1", 1024, 100, 0, 0, false⟩
  , ⟨"bad_trailing_garbage", "p cnf 1 1\n0\nextra\n", 1024, 100, 0, 0, false⟩
  , ⟨"bad_unsat_then_garbage", "p cnf 1 2\n0\nextra\n", 1024, 100, 0, 0, false⟩
  , ⟨"bad_too_few_clauses", "p cnf 1 2\n1 0\n", 1024, 100, 0, 0, false⟩
  , ⟨"bad_var_overflow", "p cnf 268435456 1\n0\n", 1024, 100, 0, 0, false⟩
  ]

#guard corpus.length == 54
#guard corpus.all checkLayerACase
#guard checkLayerACase ⟨"fuel_0_check", "p cnf 1 2\n1 0\n-1 0\n", 1024, 0, 0, 0, false⟩

/-! ## 3. Artifact Generator (`coreplus_gen.hpp`, `coreplus.ssa`, `coreplus_cases.h`) -/

def generateArtifacts (outDir : System.FilePath) : IO UInt32 :=
  writeC0Artifacts outDir coreplusModule corpus "coreplus"
    (mkBasicDiffDriverCpp "coreplus_gen.hpp" "coreplus_cases.h" "coreplus") false "CorePlus"

end LeanQbeTest.T.KissatCorePlusC0Test

public def main (args : List String) : IO UInt32 :=
  LeanQbeTest.T.KissatCorePlusC0Test.generateArtifacts
    (args.headD "/tmp/leanqbe-kissat-coreplus")
