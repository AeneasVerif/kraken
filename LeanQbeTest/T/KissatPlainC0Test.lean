module

public import LeanQbe.T.Examples.Kissat.Plain
public import LeanQbe.T.Examples.Kissat.PlainArena
public import LeanQbe.T.Examples.Kissat.PlainSpec
public import LeanQbe.T.Examples.Kissat.Core
public import LeanQbe.T.Examples.Kissat.CoreLemmas
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.Plain
meta import LeanQbe.T.Examples.Kissat.Core
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Axiom Audit, and Differential Suite for `Kissat` Stage 3 (`D-Plain`)

* Checks `plainModule.checkAcyclic`, `PrintCpp`, `PrintQbe`, and `Legal` emission across
  `aarch64` / `scalar64` / `x64AVX2`.
* Single-line `#print axioms` audit (`[propext, Classical.choice, Quot.sound]`).
* Cross-checks `X2-LayerA` `cdclSolve` on core SAT/UNSAT/edge DIMACS cases and exercises
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

/-! ## 2. Formula Generators & Differential Test Corpus (59 Cases) -/

private def joinLines (ls : List String) : String :=
  String.intercalate "\n" ls ++ "\n"

private def mkHeader (mv nc : Nat) : String :=
  s!"p cnf {mv} {nc}"

private def mkPhpDimacs (pigeons holes : Nat) : String :=
  let mv := pigeons * holes
  let alo := (List.range pigeons).map fun i =>
    let ls := (List.range holes).map fun j => toString (i * holes + j + 1)
    String.intercalate " " (ls ++ ["0"])
  let amo := (List.range holes).flatMap fun j =>
    (List.range pigeons).flatMap fun i1 =>
      (List.range pigeons).filterMap fun i2 =>
        if i1 < i2 then
          some s!"-{i1 * holes + j + 1} -{i2 * holes + j + 1} 0"
        else none
  let cls := alo ++ amo
  joinLines (mkHeader mv cls.length :: cls)

private def mkAllCubeDimacs (n : Nat) : String :=
  let ncls := 1 <<< n
  let cls := (List.range ncls).map fun mask =>
    let ls := (List.range n).map fun i =>
      if (mask >>> i) % 2 == 1 then s!"-{i + 1}" else s!"{i + 1}"
    String.intercalate " " (ls ++ ["0"])
  joinLines (mkHeader n cls.length :: cls)

private def mkParity4Unsat : String :=
  let mkPar (rem : Nat) :=
    ((List.range 16).filterMap fun mask =>
      let negs := (List.range 4).foldl (fun acc i => acc + (mask >>> i) % 2) 0
      if negs % 2 == rem then
        let ls := (List.range 4).map fun i =>
          if (mask >>> i) % 2 == 1 then s!"-{i + 1}" else s!"{i + 1}"
        some (String.intercalate " " (ls ++ ["0"]))
      else none)
  let all := mkPar 1 ++ mkPar 0
  joinLines (mkHeader 4 all.length :: all)

private def lcgNext (x : Nat) : Nat :=
  (x * 1664525 + 1013904223) % (1 <<< 32)

private def plantedSign (v : Nat) : Bool :=
  v % 3 == 0

private def mkPlanted3Sat (nv nc seed : Nat) : String := Id.run do
  let mut s := seed
  let mut cls : List String := []
  for _ in [:nc] do
    s := lcgNext s
    let v0 := (s >>> 8) % nv
    s := lcgNext s
    let v1 := (v0 + 1 + ((s >>> 8) % (nv - 1))) % nv
    s := lcgNext s
    let v2 := (v1 + 1 + ((s >>> 8) % (nv - 1))) % nv
    s := lcgNext s
    let p0 := plantedSign v0
    let p1 := ((s >>> 16) % 2 == 0)
    let p2 := ((s >>> 17) % 2 == 0)
    let fmt := fun v p => if p then s!"{v + 1}" else s!"-{v + 1}"
    cls := cls ++ [s!"{fmt v0 p0} {fmt v1 p1} {fmt v2 p2} 0"]
  return joinLines (mkHeader nv cls.length :: cls)

private def mkImplChain (n : Nat) (unsat : Bool) : String :=
  let edges := (List.range (n - 1)).map fun i => s!"-{i + 1} {i + 2} 0"
  let cls := ["1 0"] ++ edges ++ (if unsat then [s!"-{n} 0"] else [])
  joinLines (mkHeader n cls.length :: cls)

private def mkLongClause (n : Nat) (unsat : Bool) : String :=
  let longCl := String.intercalate " " ((List.range n).map (fun i => toString (i + 1)) ++ ["0"])
  let lim := if unsat then n else n - 1
  let units := (List.range lim).map fun i => s!"-{i + 1} 0"
  let cls := longCl :: units
  joinLines (mkHeader n cls.length :: cls)

private def mk2SatCycleUnsat : String :=
  joinLines (mkHeader 5 6 ::
    [ "-1 2 0", "-2 3 0", "-3 -1 0", "1 4 0", "-4 5 0", "-5 1 0" ])

private def mk1UipDiamondUnsat : String :=
  joinLines (mkHeader 5 7 ::
    [ "1 2 0", "-1 3 0", "-1 4 0", "-3 -4 5 0", "-4 -5 0", "-2 3 0", "-2 4 0" ])

private def mk2WlBacktrackUnsat : String :=
  joinLines (mkHeader 4 10 ::
    [ "1 2 3 4 0", "-1 -2 3 4 0", "1 -2 3 4 0", "-1 2 3 4 0"
    , "1 2 3 -4 0", "-1 -2 3 -4 0", "1 -2 3 -4 0", "-1 2 3 -4 0"
    , "-3 4 0", "-3 -4 0" ])

private def mkHornSat : String :=
  joinLines (mkHeader 8 8 ::
    [ "1 0", "-1 2 0", "-1 -2 3 0", "-2 -3 4 0"
    , "-3 -4 5 0", "-4 -5 6 0", "-6 7 0", "-5 -7 8 0" ])

private def mkRootUnitMixed1Uip (unsat : Bool) : String :=
  let base :=
    [ "1 2 3 4 0", "1 2 3 -4 0", "1 2 -3 4 0", "1 2 -3 -4 0"
    , "1 -2 3 4 0", "1 -2 3 -4 0", "1 -2 -3 4 0" ]
  let cls := base ++ (if unsat then [ "1 -2 -3 -4 0", "-1 0" ] else [ "-1 0" ])
  joinLines (mkHeader 4 cls.length :: cls)

private def mkMinDiamondUnsat : String :=
  joinLines (mkHeader 8 10 ::
    [ "1 2 3 0", "-2 4 0", "-3 4 0", "-4 5 0", "-5 6 0"
    , "-4 -6 7 0", "-6 -7 0", "-1 8 0", "-1 -8 0", "-2 -3 0" ])

private def mkShrinkBinaryUnsat : String :=
  joinLines (mkHeader 7 10 ::
    [ "1 2 3 4 0", "-2 5 0", "-3 5 0", "-5 6 0", "-5 -6 0"
    , "1 -2 -3 4 0", "-1 7 0", "-1 -7 0", "-4 7 0", "-4 -7 0" ])

private def mkLuckyPosSat : String :=
  joinLines (mkHeader 6 4 ::
    [ "1 -2 3 0", "-1 2 4 0", "-3 -4 5 0", "-5 6 0" ])

private def mkLuckyNegSat : String :=
  joinLines (mkHeader 6 4 ::
    [ "-1 2 -3 0", "1 -2 -4 0", "3 4 -5 0", "5 -6 0" ])

private def mkAnalyzeReduceFlushSat : String :=
  let core :=
    [ "1 0"
    , "2 3 4 0", "2 3 -4 0", "2 -3 4 0", "2 -3 -4 0"
    , "-2 -3 -4 5 0", "-2 -3 -4 -5 0", "-2 -3 4 5 0", "-2 -3 4 -5 0"
    , "15 4 3 0", "15 4 -3 0", "15 -4 3 0", "15 -4 -3 0"
    , "-16 -15 14 0", "-16 -15 -14 0" ]
  let pad := (List.range 16).map fun m =>
    let mid := (List.range 4).map fun j =>
      let v := 6 + j
      if (m >>> j) % 2 == 1 then s!"-{v}" else s!"{v}"
    String.intercalate " " (["2", "-3"] ++ mid ++ ["10", "11", "12", "13", "5", "4", "14", "0"])
  let cls := core ++ pad
  joinLines (mkHeader 16 cls.length :: cls)

private def mkOrdering4 : String :=
  let vars (i j : Nat) := i * 3 + (if j < i then j else j - 1) + 1
  let asym := (List.range 4).flatMap fun i =>
    ((List.range 4).filter (i < ·)).map fun j => s!"-{vars i j} -{vars j i} 0"
  let trans := (List.range 4).flatMap fun i =>
    (List.range 4).flatMap fun j =>
      (List.range 4).filterMap fun k =>
        if i != j && j != k && i != k then
          some s!"-{vars i j} -{vars j k} {vars i k} 0"
        else none
  let tot := (List.range 4).map fun i =>
    let ls := ((List.range 4).filter (· != i)).map fun j => toString (vars j i)
    String.intercalate " " (ls ++ ["0"])
  let cls := asym ++ trans ++ tot
  joinLines (mkHeader 12 cls.length :: cls)

structure PlainCase where
  name : String
  cnf : String
  workLen : Nat
  fuel : Nat
  expected : Nat
  checkLayerA : Bool := true

private def corpus : List PlainCase :=
  let nvStr := String.fromUTF8! nvDimacsBytes.toByteArray
  let php32 := mkPhpDimacs 3 2
  let php43 := mkPhpDimacs 4 3
  let php54 := mkPhpDimacs 5 4
  let sat3_8 := mkPlanted3Sat 8 28 42
  let sat3_10 := mkPlanted3Sat 10 36 1337
  let sat3_12 := mkPlanted3Sat 12 44 98765
  let sat3_15 := mkPlanted3Sat 15 54 202611
  let sat3_22 := mkPlanted3Sat 22 88 777111
  [ ⟨"empty_cnf_0", "p cnf 0 0\n", 2048, 100, 10, true⟩
  , ⟨"empty_cnf_3", "p cnf 3 0\n", 4096, 100, 10, true⟩
  , ⟨"empty_clause_only", "p cnf 2 1\n0\n", 4096, 100, 20, true⟩
  , ⟨"empty_clause_second", "p cnf 2 2\n1 2 0\n0\n", 4096, 100, 20, true⟩
  , ⟨"nv_unsat", nvStr, 4096, 100, 20, true⟩
  , ⟨"single_unit_sat", "p cnf 1 1\n1 0\n", 4096, 100, 10, true⟩
  , ⟨"neg_unit_sat", "p cnf 2 1\n-2 0\n", 4096, 100, 10, true⟩
  , ⟨"tautology_sat", "p cnf 2 2\n1 -1 2 0\n-2 0\n", 4096, 100, 10, true⟩
  , ⟨"tautology_unsat", "p cnf 1 3\n1 -1 0\n1 0\n-1 0\n", 4096, 100, 20, true⟩
  , ⟨"dup_lits_sat", "p cnf 2 2\n1 1 2 2 0\n-1 -1 0\n", 4096, 100, 10, true⟩
  , ⟨"dup_lits_unsat", "p cnf 1 2\n1 1 0\n-1 -1 0\n", 4096, 100, 20, true⟩
  , ⟨"dup_neg_taut", "p cnf 3 3\n1 2 -1 0\n2 2 3 0\n-2 -3 0\n", 4096, 100, 10, true⟩
  , ⟨"impl_chain_sat", mkImplChain 8 false, 4096, 500, 10, true⟩
  , ⟨"impl_chain_unsat", mkImplChain 8 true, 4096, 500, 20, true⟩
  , ⟨"two_wl_long_sat", mkLongClause 7 false, 4096, 500, 10, true⟩
  , ⟨"two_wl_long_unsat", mkLongClause 7 true, 4096, 500, 20, true⟩
  , ⟨"two_wl_backtrack_unsat", mk2WlBacktrackUnsat, 4096, 1000, 20, true⟩
  , ⟨"uip1_diamond_unsat", mk1UipDiamondUnsat, 4096, 1000, 20, true⟩
  , ⟨"min_diamond_unsat", mkMinDiamondUnsat, 8192, 2000, 20, true⟩
  , ⟨"shrink_bin_unsat", mkShrinkBinaryUnsat, 8192, 2000, 20, true⟩
  , ⟨"lucky_all_pos_sat", mkLuckyPosSat, 4096, 500, 10, true⟩
  , ⟨"lucky_all_neg_sat", mkLuckyNegSat, 4096, 500, 10, true⟩
  , ⟨"root_unit_1uip_unsat", mkRootUnitMixed1Uip true, 4096, 1000, 20, true⟩
  , ⟨"root_unit_1uip_sat", mkRootUnitMixed1Uip false, 4096, 1000, 10, true⟩
  , ⟨"unsat_2sat_cycle", mk2SatCycleUnsat, 4096, 1000, 20, true⟩
  , ⟨"unsat_all_3var", mkAllCubeDimacs 3, 4096, 1000, 20, true⟩
  , ⟨"unsat_parity_4var", mkParity4Unsat, 8192, 2000, 20, true⟩
  , ⟨"php_3_2", php32, 8192, 2000, 20, true⟩
  , ⟨"php_4_3", php43, 32768, 20000, 20, true⟩
  , ⟨"php_5_4", php54, 131072, 200000, 20, false⟩
  , ⟨"ordering_4", mkOrdering4, 16384, 20000, 20, false⟩
  , ⟨"sat_3sat_5v", mkPlanted3Sat 5 12 7, 4096, 500, 10, true⟩
  , ⟨"sat_3sat_8v", sat3_8, 8192, 2000, 10, true⟩
  , ⟨"sat_3sat_10v", sat3_10, 16384, 5000, 10, true⟩
  , ⟨"sat_3sat_12v", sat3_12, 16384, 10000, 10, true⟩
  , ⟨"sat_3sat_15v", sat3_15, 32768, 20000, 10, true⟩
  , ⟨"sat_3sat_22v", sat3_22, 65536, 50000, 10, false⟩
  , ⟨"sat_horn_8v", mkHornSat, 4096, 500, 10, true⟩
  , ⟨"analyze_reduce_flush_sat", mkAnalyzeReduceFlushSat, 4984, 2000, 10, true⟩
  , ⟨"sat_comments_crlf",
      "c hdr\r\nc 2\n  p \t cnf  2  2 \r\n1 -2 0 c inline\n2 0\nc eof",
      4096, 100, 10, true⟩
  , ⟨"sat_unaligned_work", sat3_8, 8195, 2000, 10, true⟩
  , ⟨"fuel_0_nv", nvStr, 4096, 0, 0, false⟩
  , ⟨"fuel_1_php32", php32, 8192, 1, 0, false⟩
  , ⟨"fuel_1_sat3", sat3_8, 8192, 1, 0, false⟩
  , ⟨"fuel_2_php43", php43, 32768, 2, 0, false⟩
  , ⟨"tiny_work_0", nvStr, 0, 100, 0, false⟩
  , ⟨"tiny_work_127", nvStr, 127, 100, 0, false⟩
  , ⟨"tiny_work_767", nvStr, 767, 100, 0, false⟩
  , ⟨"tiny_work_1100", nvStr, 1100, 100, 0, false⟩
  , ⟨"tiny_work_php32_oom", php32, 1600, 1000, 0, false⟩
  , ⟨"bad_empty", "", 4096, 100, 0, false⟩
  , ⟨"bad_hdr_sat", "p sat 1 2\n1 0\n-1 0\n", 4096, 100, 0, false⟩
  , ⟨"bad_oob_var", "p cnf 1 2\n2 0\n-1 0\n", 4096, 100, 0, false⟩
  , ⟨"bad_neg_zero", "p cnf 1 1\n-0 0\n", 4096, 100, 0, false⟩
  , ⟨"bad_missing_zero", "p cnf 1 1\n1", 4096, 100, 0, false⟩
  , ⟨"bad_trailing_garbage", "p cnf 1 1\n0\nextra\n", 4096, 100, 0, false⟩
  , ⟨"bad_unsat_then_garbage", "p cnf 1 2\n0\nextra\n", 4096, 100, 0, false⟩
  , ⟨"bad_too_few_clauses", "p cnf 1 2\n1 0\n", 4096, 100, 0, false⟩
  , ⟨"bad_var_overflow", "p cnf 268435456 1\n0\n", 4096, 100, 0, false⟩
  ]

private def checkLayerACase (tc : PlainCase) : Bool :=
  if !tc.checkLayerA then true
  else
    match parseDimacs tc.cnf.toUTF8.toList with
    | none => false
    | some cnf =>
      match cdclSolve tc.fuel cnf with
      | .sat σ => tc.expected == 10 && checkModel cnf σ
      | .unsat => tc.expected == 20
      | .unknown => false

#guard corpus.length == 59
#guard corpus.all checkLayerACase
#guard checkLayerACase ⟨"fuel_0_check", "p cnf 1 2\n1 0\n-1 0\n", 4096, 0, 0, false⟩

/-! ## 3. Artifact Generator (`plain_gen.hpp`, `plain.ssa`, `plain_cases.h`) -/

private def cEscapeString (s : String) : String :=
  let hex (n : Nat) : Char :=
    if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)
  String.ofList <| s.toUTF8.toList.foldr (fun b acc =>
    let n := b.toNat
    if n == '\\'.toNat then '\\' :: '\\' :: acc
    else if n == '"'.toNat then '\\' :: '"' :: acc
    else if n == '\n'.toNat then '\\' :: 'n' :: acc
    else if n == '\r'.toNat then '\\' :: 'r' :: acc
    else if n == '\t'.toNat then '\\' :: 't' :: acc
    else if n < 32 || n >= 127 then
      '\\' :: 'x' :: hex (n / 16) :: hex (n % 16) :: acc
    else Char.ofNat n :: acc) []

private def mkCasesHeader (cases : List PlainCase) : String :=
  let rows := cases.map fun c =>
    s!"  \{\"{c.name}\", \"{cEscapeString c.cnf}\", {c.cnf.toUTF8.size}ULL, " ++
    s!"{c.workLen}ULL, {c.fuel}ULL, {c.expected}ULL},"
  String.intercalate "\n"
    ([ "#pragma once"
     , "#include <stddef.h>"
     , "#include <stdint.h>"
     , ""
     , "typedef struct {"
     , "  const char *name;"
     , "  const char *cnf;"
     , "  uint64_t cnf_len;"
     , "  uint64_t work_len;"
     , "  uint64_t fuel;"
     , "  uint64_t expected;"
     , "} KissatDiffCase;"
     , ""
     , "static const KissatDiffCase kKissatCases[] = {" ] ++
     rows ++
     [ "};"
     , "static const size_t kKissatCaseCount = sizeof(kKissatCases) / sizeof(kKissatCases[0]);" ])

private def mkDriverCpp : String :=
  String.intercalate "\n"
    [ "#include <cstdint>"
    , "#include <cstdio>"
    , "#include <cstdlib>"
    , "#include <vector>"
    , "#include \"plain_gen.hpp\""
    , "#include \"plain_cases.h\""
    , "#include \"kissat_verify.h\""
    , ""
    , "static void run_all(uint64_t align_off) {"
    , "  for (size_t i = 0; i < kKissatCaseCount; ++i) {"
    , "    const auto &tc = kKissatCases[i];"
    , "    ::tqbe::Mem mem;"
    , "    const uint64_t cnf_ptr = 0x10000ULL;"
    , "    const uint64_t work_ptr = 0x100000ULL + align_off;"
    , "    if (tc.cnf_len > 0) mem.alloc(cnf_ptr, tc.cnf_len, 0x5A);"
    , "    for (size_t k = 0; k < tc.cnf_len; ++k) {"
    , "      ::tqbe::store<::tqbe::bits<8>>(mem, ::tqbe::bits<64>(cnf_ptr + k),"
    , "        ::tqbe::bits<8>((uint8_t)tc.cnf[k]));"
    , "    }"
    , "    if (tc.work_len > 0) mem.alloc(work_ptr, tc.work_len, 0xA5);"
    , "    uint64_t got = kissat_solve_bytes(mem, ::tqbe::bits<64>(cnf_ptr),"
    , "      ::tqbe::bits<64>(tc.cnf_len), ::tqbe::bits<64>(work_ptr),"
    , "      ::tqbe::bits<64>(tc.work_len), ::tqbe::bits<64>(tc.fuel)).word(0);"
    , "    if (got != tc.expected) {"
    , "      std::fprintf(stderr, \"FAIL [cpp off=%llu] %s: got=%llu exp=%llu\\n\","
    , "        (unsigned long long)align_off, tc.name,"
    , "        (unsigned long long)got, (unsigned long long)tc.expected);"
    , "      std::exit(1);"
    , "    }"
    , "    for (size_t k = 0; k < tc.cnf_len; ++k) {"
    , "      uint8_t b = (uint8_t)::tqbe::load<::tqbe::bits<8>>("
    , "        mem, ::tqbe::bits<64>(cnf_ptr + k)).word(0);"
    , "      if (b != (uint8_t)tc.cnf[k]) {"
    , "        std::fprintf(stderr, \"FAIL [cpp] %s: mutated cnf[%zu]\\n\", tc.name, k);"
    , "        std::exit(1);"
    , "      }"
    , "    }"
    , "    if (got == 10ULL) {"
    , "      uint64_t pad = (work_ptr & 7ULL) ? (8ULL - (work_ptr & 7ULL)) : 0ULL;"
    , "      uint64_t hdr = work_ptr + pad;"
    , "      uint64_t mv = ::tqbe::load<::tqbe::bits<64>>(mem, ::tqbe::bits<64>(hdr)).word(0);"
    , "      uint64_t vp = ::tqbe::load<::tqbe::bits<64>>(mem, ::tqbe::bits<64>(hdr + 64)).word(0);"
    , "      std::vector<int8_t> vals(mv * 2ULL, 0);"
    , "      for (uint64_t j = 0; j < mv * 2ULL; ++j) {"
    , "        vals[j] = (int8_t)::tqbe::load<::tqbe::bits<8>>("
    , "          mem, ::tqbe::bits<64>(vp + j)).word(0);"
    , "      }"
    , "      if (!kissat_verify_dimacs_model(tc.cnf, tc.cnf_len, vals.data(), mv)) {"
    , "        std::fprintf(stderr, \"FAIL [cpp] %s: invalid SAT model\\n\", tc.name);"
    , "        std::exit(1);"
    , "      }"
    , "    }"
    , "  }"
    , "}"
    , ""
    , "int main() {"
    , "  run_all(0ULL);"
    , "  run_all(3ULL);"
    , "  std::printf(\"PASS: plain cpp differential (%zu cases x 2 alignments)\\n\","
    , "    kKissatCaseCount);"
    , "  return 0;"
    , "}" ]

def generateArtifacts (outDir : System.FilePath) : IO UInt32 := do
  for c in corpus do
    if !checkLayerACase c then
      throw (IO.userError s!"X2-LayerA cdclSolve mismatch on case '{c.name}'")
  IO.FS.createDirAll outDir
  let cpp ← match ppTModule plainModule with
    | .ok s => pure s
    | .error e => throw (IO.userError e)
  let qbe ← match PrintQbe.module plainModule with
    | .ok s => pure s
    | .error e => throw (IO.userError e)
  IO.FS.writeFile (outDir / "plain_gen.hpp") cpp
  IO.FS.writeFile (outDir / "plain.ssa") (qbe ++ "\n")
  IO.FS.writeFile (outDir / "plain_cases.h") (mkCasesHeader corpus ++ "\n")
  IO.FS.writeFile (outDir / "plain_driver.cpp") (mkDriverCpp ++ "\n")
  IO.println s!"Generated Plain C0 artifacts ({corpus.length} cases) in {outDir}."
  pure 0

end LeanQbeTest.T.KissatPlainC0Test

public def main (args : List String) : IO UInt32 :=
  LeanQbeTest.T.KissatPlainC0Test.generateArtifacts
    (args.headD "/tmp/leanqbe-kissat-plain")
