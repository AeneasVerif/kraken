module

public import LeanQbe.T.Examples.Kissat.Full
public import LeanQbe.T.Examples.Kissat.Core
public import LeanQbe.T.Examples.Kissat.CoreLemmas
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.Full
meta import LeanQbe.T.Examples.Kissat.Core
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Axiom Audit, and Differential Suite for `Kissat` Stage 4 (`D-Full`)

* Static checks: `fullModule.checkAcyclic`, empty `exits`/`externs`, `PrintCpp`, `PrintQbe`,
  and `Legal` emission across `aarch64`, `scalar64`, and `x64AVX2`.
* Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
* Cross-checks `X2-LayerA` `cdclSolve` on core DIMACS cases and exercises every `D-Full`
  subsystem: chrono, OTFS, VMTF+VSIDS mode switching, WalkSAT/rephase, reduce/sweep,
  HBR probing, transitive reduction, vivification, Tarjan SCC substitution, gate congruence
  closure, bounded cone SAT sweeping, forward subsumption/SSR, BVE/Gate-BVE/Pure/BCE,
  BVA factoring (`cur_vars > d.mv`), model reconstruction (`full_extend`), and mutations.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.KissatFullC0Test

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.LratBytes

/-! ## 1. Static Checks & Single-Line Axiom Audit -/

#guard fullModule.checkAcyclic == true
#guard full1Module.checkAcyclic == true
#guard full2Module.checkAcyclic == true
#guard full3Module.checkAcyclic == true
#guard fullModule.exits.isEmpty && fullModule.externs.isEmpty
#guard full1_fns.length == 51
#guard full2_fns.length == 38
#guard full3_fns.length == 31
#guard full4_fns.length == 38
#guard fullFns.length == 166
#guard (ppTModule fullModule).isOk
#guard (PrintQbe.module fullModule).isOk
#guard (ppModule (fullFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (fullFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (fullFns.map (Fn.legal .x64AVX2))).isOk

#print axioms LeanQbe.T.Examples.Kissat.Full.full1_fns_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full2_fns_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full3_fns_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full4_fns_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.fullFns_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full1_acyclic
#print axioms LeanQbe.T.Examples.Kissat.Full.full2_acyclic
#print axioms LeanQbe.T.Examples.Kissat.Full.full3_acyclic
#print axioms LeanQbe.T.Examples.Kissat.Full.full_acyclic
#print axioms LeanQbe.T.Examples.Kissat.Full.full_assign_lvl_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_backtrack_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_prop_lit_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_rewatch_arena_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_arena_sweep_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_reduce_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_otfs_large_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_otfs_bin_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_min_shrink_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_analyze_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_walk_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_rephase_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_switch_mode_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_extend_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_lucky_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_probe_assume_pair_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_trans_lit_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_viv_clause_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_tarjan_scc_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_substitute_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_cong_extract_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_congruence_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_sweep_dpll_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_sweep_sat_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_fwd_check_cl_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_forward_sub_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_bve_gates_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_bve_var_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_bva_try_lit_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_factor_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_probe_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_eliminate_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.kissat_solve_bytes_full_wf

/-! ## 2. Formula Generators & Differential / Inprocessing Corpus -/

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
        if i1 < i2 then some s!"-{i1 * holes + j + 1} -{i2 * holes + j + 1} 0" else none
  let cls := alo ++ amo
  joinLines (mkHeader mv cls.length :: cls)

private def mkAllCubeDimacs (n : Nat) : String :=
  let cls := (List.range (1 <<< n)).map fun mask =>
    let ls := (List.range n).map fun i =>
      if (mask >>> i) % 2 == 1 then s!"-{i + 1}" else s!"{i + 1}"
    String.intercalate " " (ls ++ ["0"])
  joinLines (mkHeader n cls.length :: cls)

private def mkParity4Unsat : String :=
  let mkPar (rem : Nat) :=
    (List.range 16).filterMap fun mask =>
      let negs := (List.range 4).foldl (fun acc i => acc + (mask >>> i) % 2) 0
      if negs % 2 == rem then
        let ls := (List.range 4).map fun i =>
          if (mask >>> i) % 2 == 1 then s!"-{i + 1}" else s!"{i + 1}"
        some (String.intercalate " " (ls ++ ["0"]))
      else none
  let all := mkPar 1 ++ mkPar 0
  joinLines (mkHeader 4 all.length :: all)

private def lcgNext (x : Nat) : Nat :=
  (x * 1664525 + 1013904223) % (1 <<< 32)

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
    let p0 := (v0 % 3 == 0)
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
  let cls := longCl :: (List.range lim).map fun i => s!"-{i + 1} 0"
  joinLines (mkHeader n cls.length :: cls)

private def mk2SatCycleUnsat : String :=
  joinLines (mkHeader 5 6 ::
    [ "-1 2 0", "-2 3 0", "-3 -1 0", "1 4 0", "-4 5 0", "-5 1 0" ])

private def mk1UipDiamondUnsat : String :=
  joinLines (mkHeader 5 7 ::
    [ "1 2 0", "-1 3 0", "-1 4 0", "-3 -4 5 0", "-4 -5 0", "-2 3 0", "-2 4 0" ])

private def mkMinDiamondUnsat : String :=
  joinLines (mkHeader 8 10 ::
    [ "1 2 3 0", "-2 4 0", "-3 4 0", "-4 5 0", "-5 6 0"
    , "-4 -6 7 0", "-6 -7 0", "-1 8 0", "-1 -8 0", "-2 -3 0" ])

private def mkShrinkBinaryUnsat : String :=
  joinLines (mkHeader 7 10 ::
    [ "1 2 3 4 0", "-2 5 0", "-3 5 0", "-5 6 0", "-5 -6 0"
    , "1 -2 -3 4 0", "-1 7 0", "-1 -7 0", "-4 7 0", "-4 -7 0" ])

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

private def mkProbeHbrSat : String :=
  joinLines (mkHeader 8 9 ::
    [ "-1 2 0", "-1 3 0", "-2 -3 4 0", "4 5 6 0", "-4 -5 -6 0"
    , "5 7 8 0", "-5 -7 -8 0", "-1 7 8 0", "1 7 -8 0" ])

private def mkTransitiveSat : String :=
  joinLines (mkHeader 6 9 ::
    [ "-1 2 0", "-2 3 0", "-1 3 0", "3 4 5 0", "-3 -4 -5 0"
    , "4 5 6 0", "-4 -5 -6 0", "-1 4 6 0", "1 4 -6 0" ])

private def mkVivifySat : String :=
  joinLines (mkHeader 6 8 ::
    [ "1 2 3 4 0", "1 3 0", "1 5 -6 0", "1 -5 6 0"
    , "2 5 6 0", "2 -5 -6 0", "3 4 5 0", "-3 -4 -6 0" ])

private def mkSubstSccSat : String :=
  joinLines (mkHeader 6 8 ::
    [ "-1 2 0", "-2 1 0", "-2 3 0", "-3 2 0"
    , "3 4 5 0", "-3 -4 6 0", "4 5 -6 0", "-4 -5 6 0" ])

private def mkSubstSccUnsat : String :=
  joinLines (mkHeader 3 6 ::
    [ "-1 2 0", "-2 3 0", "-3 -1 0", "1 -2 0", "2 -3 0", "3 1 0" ])

private def mkCongAndSat : String :=
  joinLines (mkHeader 7 10 ::
    [ "-3 1 0", "-3 2 0", "3 -1 -2 0"
    , "-4 1 0", "-4 2 0", "4 -1 -2 0"
    , "3 -4 5 0", "-3 4 5 0", "5 6 7 0", "-5 -6 -7 0" ])

private def mkCongIteUnsat : String :=
  joinLines (mkHeader 6 12 ::
    [ "-1 -4 2 0", "-1 4 -2 0", "1 -4 3 0", "1 4 -3 0"
    , "-1 -5 2 0", "-1 5 -2 0", "1 -5 3 0", "1 5 -3 0"
    , "4 5 6 0", "-4 -5 6 0", "4 5 -6 0", "-4 -5 -6 0" ])

private def mkCongXorUnsat : String :=
  joinLines (mkHeader 5 12 ::
    [ "-3 1 2 0", "-3 -1 -2 0", "3 -1 2 0", "3 1 -2 0"
    , "-4 1 2 0", "-4 -1 -2 0", "4 -1 2 0", "4 1 -2 0"
    , "3 4 5 0", "-3 -4 5 0", "3 4 -5 0", "-3 -4 -5 0" ])

private def mkSweepConeSat : String :=
  joinLines (mkHeader 8 13 ::
    [ "-3 1 0", "-3 2 0", "3 -1 -2 0"
    , "-4 1 0", "-4 5 0", "4 -1 -5 0"
    , "-5 2 0", "-5 6 0", "5 -2 -6 0"
    , "-1 6 0", "3 -4 7 0", "-3 4 7 0", "7 8 0" ])

private def mkFwdSubStrSat : String :=
  joinLines (mkHeader 9 11 ::
    [ "1 2 3 4 5 0"
    , "1 6 7 0", "1 -6 -7 0", "1 8 9 0", "1 -8 -9 0"
    , "-1 2 3 0", "-1 2 3 0"
    , "-1 6 -7 0", "-1 -6 7 0", "-1 8 -9 0", "-1 -8 9 0" ])

private def mkBveGatesSat : String :=
  joinLines (mkHeader 8 10 ::
    [ "-3 1 0", "-3 2 0", "3 -1 -2 0"
    , "3 4 5 0", "-3 5 6 0", "-4 -5 -6 0"
    , "4 5 -6 0", "7 8 0", "-7 4 5 0", "7 -4 -5 0" ])

private def mkBceSat : String :=
  joinLines (mkHeader 9 10 ::
    [ "1 2 3 0"
    , "1 4 5 0", "1 -4 -5 0", "1 5 6 0", "1 -5 -6 0"
    , "-1 -2 7 8 0", "-1 -2 -7 -8 0", "-1 -2 8 9 0"
    , "-1 -2 -8 -9 0", "-1 -2 7 -9 0" ])

private def mkBvaFactorSat : String :=
  let grid :=
    [ "-1 -3 0", "-1 -4 0", "-1 -5 0"
    , "-2 -3 0", "-2 -4 0", "-2 -5 0" ]
  let guard1 :=
    [ "1 6 7 0", "1 6 -7 0", "1 -6 7 0", "1 7 8 0", "1 -7 8 0"
    , "2 6 7 0", "2 6 -7 0", "2 -6 7 0", "2 7 8 0", "2 -7 8 0" ]
  let guard2 :=
    [ "3 9 10 0", "3 9 -10 0", "3 -9 10 0", "3 10 11 0", "3 -10 11 0"
    , "4 9 10 0", "4 9 -10 0", "4 -9 10 0", "4 10 11 0", "4 -10 11 0"
    , "5 9 10 0", "5 9 -10 0", "5 -9 10 0", "5 10 11 0", "5 -10 11 0" ]
  let cls := grid ++ guard1 ++ guard2
  joinLines (mkHeader 11 cls.length :: cls)

structure FullCase where
  name : String
  cnf : String
  workLen : Nat
  fuel : Nat
  expected : Nat
  reqMask : Nat := 0
  checkLayerA : Bool := true

private def corpus : List FullCase :=
  let nvStr := String.fromUTF8! nvDimacsBytes.toByteArray
  let php32 := mkPhpDimacs 3 2
  let php43 := mkPhpDimacs 4 3
  let php54 := mkPhpDimacs 5 4
  let sat3_8 := mkPlanted3Sat 8 28 42
  let sat3_10 := mkPlanted3Sat 10 36 1337
  let sat3_12 := mkPlanted3Sat 12 44 98765
  let sat3_15 := mkPlanted3Sat 15 54 202611
  let sat3_22 := mkPlanted3Sat 22 88 777111
  [ ⟨"empty_cnf_0", "p cnf 0 0\n", 8192, 100, 10, 0, true⟩
  , ⟨"empty_cnf_3", "p cnf 3 0\n", 8192, 100, 10, 0, true⟩
  , ⟨"empty_clause_only", "p cnf 2 1\n0\n", 8192, 100, 20, 0, true⟩
  , ⟨"empty_clause_second", "p cnf 2 2\n1 2 0\n0\n", 8192, 100, 20, 0, true⟩
  , ⟨"nv_unsat", nvStr, 8192, 100, 20, 0, true⟩
  , ⟨"single_unit_sat", "p cnf 1 1\n1 0\n", 8192, 100, 10, 0, true⟩
  , ⟨"neg_unit_sat", "p cnf 2 1\n-2 0\n", 8192, 100, 10, 0, true⟩
  , ⟨"tautology_sat", "p cnf 2 2\n1 -1 2 0\n-2 0\n", 8192, 100, 10, 0, true⟩
  , ⟨"tautology_unsat", "p cnf 1 3\n1 -1 0\n1 0\n-1 0\n", 8192, 100, 20, 0, true⟩
  , ⟨"dup_lits_sat", "p cnf 2 2\n1 1 2 2 0\n-1 -1 0\n", 8192, 100, 10, 0, true⟩
  , ⟨"dup_lits_unsat", "p cnf 1 2\n1 1 0\n-1 -1 0\n", 8192, 100, 20, 0, true⟩
  , ⟨"dup_neg_taut", "p cnf 3 3\n1 2 -1 0\n2 2 3 0\n-2 -3 0\n", 8192, 100, 10, 0, true⟩
  , ⟨"impl_chain_sat", mkImplChain 8 false, 16384, 500, 10, 0, true⟩
  , ⟨"impl_chain_unsat", mkImplChain 8 true, 16384, 500, 20, 0, true⟩
  , ⟨"two_wl_long_sat", mkLongClause 7 false, 16384, 500, 10, 0, true⟩
  , ⟨"two_wl_long_unsat", mkLongClause 7 true, 16384, 500, 20, 0, true⟩
  , ⟨"uip1_diamond_unsat", mk1UipDiamondUnsat, 16384, 1000, 20, 0, true⟩
  , ⟨"min_diamond_unsat", mkMinDiamondUnsat, 16384, 2000, 20, 0, true⟩
  , ⟨"shrink_bin_unsat", mkShrinkBinaryUnsat, 16384, 2000, 20, 0, true⟩
  , ⟨"unsat_2sat_cycle", mk2SatCycleUnsat, 16384, 1000, 20, 0, true⟩
  , ⟨"unsat_all_3var", mkAllCubeDimacs 3, 16384, 1000, 20, 0, true⟩
  , ⟨"unsat_parity_4var", mkParity4Unsat, 16384, 2000, 20, 0, true⟩
  , ⟨"php_3_2", php32, 32768, 2000, 20, 0, true⟩
  , ⟨"php_4_3", php43, 65536, 20000, 20, 0, true⟩
  , ⟨"php_5_4", php54, 262144, 200000, 20, 0, false⟩
  , ⟨"ordering_4", mkOrdering4, 65536, 20000, 20, 0, false⟩
  , ⟨"sat_3sat_5v", mkPlanted3Sat 5 12 7, 16384, 500, 10, 0, true⟩
  , ⟨"sat_3sat_8v", sat3_8, 32768, 2000, 10, 0, true⟩
  , ⟨"sat_3sat_10v", sat3_10, 32768, 5000, 10, 0, true⟩
  , ⟨"sat_3sat_12v", sat3_12, 32768, 10000, 10, 0, true⟩
  , ⟨"sat_3sat_15v", sat3_15, 65536, 20000, 10, 0, true⟩
  , ⟨"sat_3sat_22v", sat3_22, 131072, 50000, 10, 0, false⟩
  , ⟨"inproc_hbr_sat", mkProbeHbrSat, 32768, 5000, 10, 1, true⟩
  , ⟨"inproc_trans_sat", mkTransitiveSat, 32768, 5000, 10, 2, true⟩
  , ⟨"inproc_viv_sat", mkVivifySat, 32768, 5000, 10, 4, true⟩
  , ⟨"inproc_subst_sat", mkSubstSccSat, 32768, 5000, 10, 8, true⟩
  , ⟨"inproc_subst_unsat", mkSubstSccUnsat, 32768, 5000, 20, 0, true⟩
  , ⟨"inproc_cong_and_sat", mkCongAndSat, 32768, 5000, 10, 16, true⟩
  , ⟨"inproc_cong_ite_unsat", mkCongIteUnsat, 32768, 5000, 20, 16, true⟩
  , ⟨"inproc_cong_xor_unsat", mkCongXorUnsat, 32768, 5000, 20, 16, true⟩
  , ⟨"inproc_sweep_sat", mkSweepConeSat, 65536, 10000, 10, 32, true⟩
  , ⟨"inproc_fwd_sub_str", mkFwdSubStrSat, 32768, 5000, 10, 192, true⟩
  , ⟨"inproc_bve_gates_sat", mkBveGatesSat, 32768, 5000, 10, 256, true⟩
  , ⟨"inproc_bce_sat", mkBceSat, 32768, 5000, 10, 512, true⟩
  , ⟨"inproc_bva_factor_sat", mkBvaFactorSat, 65536, 10000, 10, 1024, true⟩
  , ⟨"sat_comments_crlf",
      "c hdr\r\nc 2\n  p \t cnf  2  2 \r\n1 -2 0 c inline\n2 0\nc eof",
      8192, 100, 10, 0, true⟩
  , ⟨"sat_unaligned_work", sat3_8, 32771, 2000, 10, 0, true⟩
  , ⟨"fuel_0_nv", nvStr, 8192, 0, 0, 0, false⟩
  , ⟨"fuel_1_php43", php43, 65536, 1, 0, 0, false⟩
  , ⟨"fuel_1_sat3", sat3_10, 32768, 1, 0, 0, false⟩
  , ⟨"tiny_work_0", nvStr, 0, 100, 0, 0, false⟩
  , ⟨"tiny_work_127", nvStr, 127, 100, 0, 0, false⟩
  , ⟨"tiny_work_1151", nvStr, 1151, 100, 0, 0, false⟩
  , ⟨"tiny_work_php32_oom", php32, 1600, 1000, 0, 0, false⟩
  , ⟨"bad_empty", "", 8192, 100, 0, 0, false⟩
  , ⟨"bad_hdr_sat", "p sat 1 2\n1 0\n-1 0\n", 8192, 100, 0, 0, false⟩
  , ⟨"bad_oob_var", "p cnf 1 2\n2 0\n-1 0\n", 8192, 100, 0, 0, false⟩
  , ⟨"bad_neg_zero", "p cnf 1 1\n-0 0\n", 8192, 100, 0, 0, false⟩
  , ⟨"bad_missing_zero", "p cnf 1 1\n1", 8192, 100, 0, 0, false⟩
  , ⟨"bad_trailing_garbage", "p cnf 1 1\n0\nextra\n", 8192, 100, 0, 0, false⟩
  , ⟨"bad_unsat_then_garbage", "p cnf 1 2\n0\nextra\n", 8192, 100, 0, 0, false⟩
  , ⟨"bad_too_few_clauses", "p cnf 1 2\n1 0\n", 8192, 100, 0, 0, false⟩
  , ⟨"bad_var_overflow", "p cnf 268435456 1\n0\n", 8192, 100, 0, 0, false⟩
  ]

private def checkLayerACase (tc : FullCase) : Bool :=
  if !tc.checkLayerA then true
  else
    match parseDimacs tc.cnf.toUTF8.toList with
    | none => false
    | some cnf =>
      match cdclSolve tc.fuel cnf with
      | .sat σ => tc.expected == 10 && checkModel cnf σ
      | .unsat => tc.expected == 20
      | .unknown => false

#guard corpus.length == 63
#guard corpus.all checkLayerACase

/-! ## 3. Artifact Generator (`full_gen.hpp`, `full.ssa`, `full_cases.h`, `full_driver.cpp`) -/

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

private def mkCasesHeader (cases : List FullCase) : String :=
  let rows := cases.map fun c =>
    s!"  \{\"{c.name}\", \"{cEscapeString c.cnf}\", {c.cnf.toUTF8.size}ULL, " ++
    s!"{c.workLen}ULL, {c.fuel}ULL, {c.expected}ULL, {c.reqMask}ULL},"
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
     , "  uint64_t req_mask;"
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
    , "#include \"full_gen.hpp\""
    , "#include \"full_cases.h\""
    , "#include \"kissat_verify.h\""
    , ""
    , "static inline uint64_t ld64(::tqbe::Mem &mem, uint64_t a) {"
    , "  return ::tqbe::load<::tqbe::bits<64>>(mem, ::tqbe::bits<64>(a)).word(0);"
    , "}"
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
    , "      std::fprintf(stderr, \"FAIL [off=%llu] %s: got=%llu exp=%llu\\n\","
    , "        (unsigned long long)align_off, tc.name,"
    , "        (unsigned long long)got, (unsigned long long)tc.expected);"
    , "      std::exit(1);"
    , "    }"
    , "    for (size_t k = 0; k < tc.cnf_len; ++k) {"
    , "      uint8_t b = (uint8_t)::tqbe::load<::tqbe::bits<8>>("
    , "        mem, ::tqbe::bits<64>(cnf_ptr + k)).word(0);"
    , "      if (b != (uint8_t)tc.cnf[k]) {"
    , "        std::fprintf(stderr, \"FAIL %s: mutated cnf[%zu]\\n\", tc.name, k);"
    , "        std::exit(1);"
    , "      }"
    , "    }"
    , "    if (tc.req_mask != 0ULL) {"
    , "      uint64_t pad = (work_ptr & 7ULL) ? (8ULL - (work_ptr & 7ULL)) : 0ULL;"
    , "      uint64_t hdr = work_ptr + pad;"
    , "      uint64_t mv = ld64(mem, hdr), cv = ld64(mem, hdr + 97*8);"
    , "      uint64_t hbr = ld64(mem, hdr + 130*8), tr = ld64(mem, hdr + 131*8);"
    , "      uint64_t viv = ld64(mem, hdr + 132*8), sub = ld64(mem, hdr + 133*8);"
    , "      uint64_t cng = ld64(mem, hdr + 134*8), swp = ld64(mem, hdr + 135*8);"
    , "      uint64_t bve = ld64(mem, hdr + 136*8), bce = ld64(mem, hdr + 137*8);"
    , "      uint64_t bva = ld64(mem, hdr + 138*8);"
    , "      uint64_t fsub = ld64(mem, hdr + 140*8), fstr = ld64(mem, hdr + 141*8);"
    , "      if (((tc.req_mask & 1) && !hbr) || ((tc.req_mask & 2) && !tr) ||"
    , "          ((tc.req_mask & 4) && !viv) || ((tc.req_mask & 8) && !sub) ||"
    , "          ((tc.req_mask & 16) && !cng) || ((tc.req_mask & 32) && !swp) ||"
    , "          ((tc.req_mask & 64) && !fsub) || ((tc.req_mask & 128) && !fstr) ||"
    , "          ((tc.req_mask & 256) && !bve) || ((tc.req_mask & 512) && !bce) ||"
    , "          ((tc.req_mask & 1024) && (!bva || cv <= mv))) {"
    , "        std::fprintf(stderr,"
    , "          \"FAIL %s req_mask=%llu: hbr=%llu tr=%llu viv=%llu sub=%llu cng=%llu \""
    , "          \"swp=%llu fsub=%llu fstr=%llu bve=%llu bce=%llu bva=%llu cv=%llu mv=%llu\\n\","
    , "          tc.name, (unsigned long long)tc.req_mask, (unsigned long long)hbr,"
    , "          (unsigned long long)tr, (unsigned long long)viv, (unsigned long long)sub,"
    , "          (unsigned long long)cng, (unsigned long long)swp, (unsigned long long)fsub,"
    , "          (unsigned long long)fstr, (unsigned long long)bve, (unsigned long long)bce,"
    , "          (unsigned long long)bva, (unsigned long long)cv, (unsigned long long)mv);"
    , "        std::exit(1);"
    , "      }"
    , "    }"
    , "    if (got == 10ULL) {"
    , "      uint64_t pad = (work_ptr & 7ULL) ? (8ULL - (work_ptr & 7ULL)) : 0ULL;"
    , "      uint64_t hdr = work_ptr + pad;"
    , "      uint64_t mv = ld64(mem, hdr);"
    , "      uint64_t vp = ld64(mem, hdr + 64);"
    , "      std::vector<int8_t> vals(mv * 2ULL, 0);"
    , "      for (uint64_t j = 0; j < mv * 2ULL; ++j) {"
    , "        vals[j] = (int8_t)::tqbe::load<::tqbe::bits<8>>("
    , "          mem, ::tqbe::bits<64>(vp + j)).word(0);"
    , "      }"
    , "      if (!kissat_verify_dimacs_model(tc.cnf, tc.cnf_len, vals.data(), mv)) {"
    , "        std::fprintf(stderr, \"FAIL %s: invalid SAT model\\n\", tc.name);"
    , "        std::exit(1);"
    , "      }"
    , "    }"
    , "  }"
    , "}"
    , ""
    , "static void run_subsystem_and_mutation_tests() {"
    , "  ::tqbe::Mem mem;"
    , "  const char *cnf = \"p cnf 3 3\\n1 2 0\\n-1 -2 0\\n3 0\\n\";"
    , "  const uint64_t clen = 28ULL, cptr = 0x10000ULL, wptr = 0x100000ULL;"
    , "  mem.alloc(cptr, clen, 0);"
    , "  for (size_t k = 0; k < clen; ++k) {"
    , "    ::tqbe::store<::tqbe::bits<8>>(mem, ::tqbe::bits<64>(cptr + k),"
    , "      ::tqbe::bits<8>((uint8_t)cnf[k]));"
    , "  }"
    , "  mem.alloc(wptr, 16384ULL, 0xA5);"
    , "  uint64_t r = kissat_solve_bytes(mem, ::tqbe::bits<64>(cptr), ::tqbe::bits<64>(clen),"
    , "    ::tqbe::bits<64>(wptr), ::tqbe::bits<64>(16384ULL), ::tqbe::bits<64>(5000ULL)).word(0);"
    , "  if (r != 10ULL) { std::fprintf(stderr, \"FAIL mut_setup\\n\"); std::exit(1); }"
    , "  uint64_t vp = ld64(mem, wptr + 64);"
    , "  int8_t v0 = (int8_t)::tqbe::load<::tqbe::bits<8>>(mem, ::tqbe::bits<64>(vp + 4)).word(0);"
    , "  ::tqbe::store<::tqbe::bits<8>>(mem, ::tqbe::bits<64>(vp + 4),"
    , "    ::tqbe::bits<8>((uint8_t)(-v0)));"
    , "  ::tqbe::store<::tqbe::bits<8>>(mem, ::tqbe::bits<64>(vp + 5),"
    , "    ::tqbe::bits<8>((uint8_t)v0));"
    , "  uint64_t chk = kissat_check_model(mem, ::tqbe::bits<64>(cptr),"
    , "    ::tqbe::bits<64>(cptr + clen), ::tqbe::bits<64>(wptr), ::tqbe::bits<64>(vp),"
    , "    ::tqbe::bits<64>(3ULL)).word(0);"
    , "  if (chk != 0ULL) { std::fprintf(stderr, \"FAIL mut_model accepted\\n\"); std::exit(1); }"
    , "  full_init_state(mem, ::tqbe::bits<64>(cptr), ::tqbe::bits<64>(cptr + clen),"
    , "    ::tqbe::bits<64>(wptr), ::tqbe::bits<64>(16384ULL), ::tqbe::bits<64>(5000ULL));"
    , "  full_parse_body(mem, ::tqbe::bits<64>(wptr), ::tqbe::bits<64>(cptr + clen));"
    , "  full_walk(mem, ::tqbe::bits<64>(wptr));"
    , "  full_rephase(mem, ::tqbe::bits<64>(wptr));"
    , "  uint64_t confl = 10000ULL;"
    , "  ::tqbe::store<::tqbe::bits<64>>(mem, ::tqbe::bits<64>(wptr + 42*8),"
    , "    ::tqbe::bits<64>(confl));"
    , "  full_switch_mode(mem, ::tqbe::bits<64>(wptr));"
    , "  full_reduce(mem, ::tqbe::bits<64>(wptr), true);"
    , "  uint64_t sw = ld64(mem, wptr + 70*8), rph = ld64(mem, wptr + 84*8);"
    , "  uint64_t red = ld64(mem, wptr + 86*8), wlk = ld64(mem, wptr + 139*8);"
    , "  if (sw == 0ULL || rph == 0ULL || red == 0ULL || wlk == 0ULL) {"
    , "    std::fprintf(stderr, \"FAIL unit_heur: sw=%llu rph=%llu red=%llu wlk=%llu\\n\","
    , "      (unsigned long long)sw, (unsigned long long)rph,"
    , "      (unsigned long long)red, (unsigned long long)wlk);"
    , "    std::exit(1);"
    , "  }"
    , "}"
    , ""
    , "int main() {"
    , "  run_all(0ULL);"
    , "  run_all(3ULL);"
    , "  run_subsystem_and_mutation_tests();"
    , "  std::printf(\"PASS: full cpp differential (%zu cases x 2 alignments + mutations)\\n\","
    , "    kKissatCaseCount);"
    , "  return 0;"
    , "}" ]

def generateArtifacts (outDir : System.FilePath) : IO UInt32 := do
  for c in corpus do
    if !checkLayerACase c then
      throw (IO.userError s!"X2-LayerA cdclSolve mismatch on case '{c.name}'")
  IO.FS.createDirAll outDir
  let cpp ← match ppTModule fullModule with
    | .ok s => pure s
    | .error e => throw (IO.userError e)
  let qbe ← match PrintQbe.module fullModule with
    | .ok s => pure s
    | .error e => throw (IO.userError e)
  IO.FS.writeFile (outDir / "full_gen.hpp") cpp
  IO.FS.writeFile (outDir / "full.ssa") (qbe ++ "\n")
  IO.FS.writeFile (outDir / "full_cases.h") (mkCasesHeader corpus ++ "\n")
  IO.FS.writeFile (outDir / "full_driver.cpp") (mkDriverCpp ++ "\n")
  IO.println s!"Generated Full C0 artifacts ({corpus.length} cases) in {outDir}."
  pure 0

end LeanQbeTest.T.KissatFullC0Test

public def main (args : List String) : IO UInt32 :=
  LeanQbeTest.T.KissatFullC0Test.generateArtifacts
    (args.headD "/tmp/leanqbe-kissat-full")
