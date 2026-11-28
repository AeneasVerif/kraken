module

public import LeanQbe.T.Examples.Kissat.Solver
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
public import LeanQbeTest.T.KissatC0Harness
meta import LeanQbe.T.Examples.Kissat.Solver
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal
meta import LeanQbeTest.T.KissatC0Harness

/-!
# Verification, Axiom Audit, and Differential Suite for `Kissat` C0 Solver

* Checks `dimacsModule.checkAcyclic`, `kissatModule.checkAcyclic`, `PrintCpp`, `PrintQbe`, and
  `Legal` emission across `aarch64` / `scalar64` / `x64AVX2`.
* Single-line `#print axioms` audit (`[propext, Classical.choice, Quot.sound]`).
* Cross-checks pure-Lean `cdclSolve` across a 51-case SAT/UNSAT/edge-case DIMACS corpus.
* Emits `kissat_gen.hpp`, `kissat.ssa`, `kissat_driver.cpp`, and `kissat_cases.h` for
  `test/kissat/run.sh`.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.KissatC0Test

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.LratBytes
open LeanQbeTest.T.KissatC0Harness

/-! ## 1. Static Checks & Axiom Audit -/

#guard dimacsModule.checkAcyclic == true
#guard kissatModule.checkAcyclic == true
#guard dimacsModule.exits.isEmpty && dimacsModule.externs.isEmpty
#guard kissatModule.exits.isEmpty && kissatModule.externs.isEmpty
#guard dimacs_fns.length == 8
#guard solver_fns.length == 17
#guard kissatFns.length == 25
#guard (ppTModule kissatModule).isOk
#guard (PrintQbe.module kissatModule).isOk
#guard (ppModule (kissatFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (kissatFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (kissatFns.map (Fn.legal .x64AVX2))).isOk

#print axioms LeanQbe.T.Examples.Kissat.dimacsFns_wf
#print axioms LeanQbe.T.Examples.Kissat.dimacsModule_checkAcyclic
#print axioms LeanQbe.T.Examples.Kissat.solverFns_wf
#print axioms LeanQbe.T.Examples.Kissat.kissatFns_wf
#print axioms LeanQbe.T.Examples.Kissat.kissatModule_checkAcyclic
#print axioms LeanQbe.T.Examples.Kissat.kissat_parse_header_wf
#print axioms LeanQbe.T.Examples.Kissat.kissat_check_model_wf
#print axioms LeanQbe.T.Examples.Kissat.kissat_propagate_lit_wf
#print axioms LeanQbe.T.Examples.Kissat.kissat_analyze_wf
#print axioms LeanQbe.T.Examples.Kissat.kissat_solve_bytes_wf

/-! ## 2. Test Corpus (51 Cases) -/

private def corpus : List KissatCase :=
  let nvStr := String.fromUTF8! nvDimacsBytes.toByteArray
  let php32 := mkPhpDimacs 3 2
  let php43 := mkPhpDimacs 4 3
  let php54 := mkPhpDimacs 5 4
  let sat3_8 := mkPlanted3Sat 8 28 42
  let sat3_10 := mkPlanted3Sat 10 36 1337
  let sat3_12 := mkPlanted3Sat 12 44 98765
  let sat3_15 := mkPlanted3Sat 15 54 202611
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
  , ⟨"root_unit_1uip_unsat", mkRootUnitMixed1Uip true, 4096, 1000, 20, 0, true⟩
  , ⟨"root_unit_1uip_sat", mkRootUnitMixed1Uip false, 4096, 1000, 10, 0, true⟩
  , ⟨"unsat_2sat_cycle", mk2SatCycleUnsat, 4096, 1000, 20, 0, true⟩
  , ⟨"unsat_all_3var", mkAllCubeDimacs 3, 4096, 1000, 20, 0, true⟩
  , ⟨"unsat_parity_4var", mkParity4Unsat, 8192, 2000, 20, 0, true⟩
  , ⟨"php_3_2", php32, 8192, 2000, 20, 0, true⟩
  , ⟨"php_4_3", php43, 32768, 20000, 20, 0, true⟩
  , ⟨"php_5_4", php54, 131072, 200000, 20, 0, true⟩
  , ⟨"sat_3sat_5v", mkPlanted3Sat 5 12 7, 4096, 500, 10, 0, true⟩
  , ⟨"sat_3sat_8v", sat3_8, 8192, 2000, 10, 0, true⟩
  , ⟨"sat_3sat_10v", sat3_10, 16384, 5000, 10, 0, true⟩
  , ⟨"sat_3sat_12v", sat3_12, 16384, 10000, 10, 0, true⟩
  , ⟨"sat_3sat_15v", sat3_15, 32768, 20000, 10, 0, true⟩
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
  , ⟨"tiny_work_200", nvStr, 200, 100, 0, 0, false⟩
  , ⟨"tiny_work_php32_oom", php32, 500, 1000, 0, 0, false⟩
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

#guard corpus.length == 51
#guard (corpus.filter (fun c => c.name != "php_5_4")).all checkLayerACase
#guard checkLayerACase ⟨"fuel_0_check", "p cnf 1 2\n1 0\n-1 0\n", 1024, 0, 0, 0, false⟩

/-! ## 3. Artifact Generator (`kissat_gen.hpp`, `kissat.ssa`, `kissat_cases.h`, driver) -/

def generateArtifacts (outDir : System.FilePath) : IO UInt32 :=
  writeC0Artifacts outDir kissatModule corpus "kissat"
    (mkBasicDiffDriverCpp "kissat_gen.hpp" "kissat_cases.h") false "Kissat"

end LeanQbeTest.T.KissatC0Test

public def main (args : List String) : IO UInt32 :=
  LeanQbeTest.T.KissatC0Test.generateArtifacts (args.headD "/tmp/leanqbe-kissat")
