module

public import LeanQbe.T.Examples.Kissat.Solver
public import LeanQbe.T.Examples.Kissat.Core
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.Solver
meta import LeanQbe.T.Examples.Kissat.Core
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Shared Test Harness, DIMACS Generators, and C++ Differential Driver for Kissat C0

Target-neutral test utilities shared across `KissatC0Test`, `KissatCorePlusC0Test`,
`KissatPlainC0Test`, and `KissatFullC0Test`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatC0Harness

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.LratBytes

/-! ## 1. Shared DIMACS Formula Generators -/

def joinLines (ls : List String) : String :=
  String.intercalate "\n" ls ++ "\n"

def mkHeader (mv nc : Nat) : String :=
  s!"p cnf {mv} {nc}"

def mkPhpDimacs (pigeons holes : Nat) : String :=
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

def mkAllCubeDimacs (n : Nat) : String :=
  let ncls := 1 <<< n
  let cls := (List.range ncls).map fun mask =>
    let ls := (List.range n).map fun i =>
      if (mask >>> i) % 2 == 1 then s!"-{i + 1}" else s!"{i + 1}"
    String.intercalate " " (ls ++ ["0"])
  joinLines (mkHeader n cls.length :: cls)

def mkParity4Unsat : String :=
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

def lcgNext (x : Nat) : Nat :=
  (x * 1664525 + 1013904223) % (1 <<< 32)

def plantedSign (v : Nat) : Bool :=
  v % 3 == 0

def mkPlanted3Sat (nv nc seed : Nat) : String := Id.run do
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

def mkImplChain (n : Nat) (unsat : Bool) : String :=
  let edges := (List.range (n - 1)).map fun i => s!"-{i + 1} {i + 2} 0"
  let cls := ["1 0"] ++ edges ++ (if unsat then [s!"-{n} 0"] else [])
  joinLines (mkHeader n cls.length :: cls)

def mkLongClause (n : Nat) (unsat : Bool) : String :=
  let longCl := String.intercalate " " ((List.range n).map (fun i => toString (i + 1)) ++ ["0"])
  let lim := if unsat then n else n - 1
  let units := (List.range lim).map fun i => s!"-{i + 1} 0"
  let cls := longCl :: units
  joinLines (mkHeader n cls.length :: cls)

def mk2SatCycleUnsat : String :=
  joinLines (mkHeader 5 6 ::
    [ "-1 2 0", "-2 3 0", "-3 -1 0", "1 4 0", "-4 5 0", "-5 1 0" ])

def mk1UipDiamondUnsat : String :=
  joinLines (mkHeader 5 7 ::
    [ "1 2 0", "-1 3 0", "-1 4 0", "-3 -4 5 0", "-4 -5 0", "-2 3 0", "-2 4 0" ])

def mk2WlBacktrackUnsat : String :=
  joinLines (mkHeader 4 10 ::
    [ "1 2 3 4 0", "-1 -2 3 4 0", "1 -2 3 4 0", "-1 2 3 4 0"
    , "1 2 3 -4 0", "-1 -2 3 -4 0", "1 -2 3 -4 0", "-1 2 3 -4 0"
    , "-3 4 0", "-3 -4 0" ])

def mkHornSat : String :=
  joinLines (mkHeader 8 8 ::
    [ "1 0", "-1 2 0", "-1 -2 3 0", "-2 -3 4 0"
    , "-3 -4 5 0", "-4 -5 6 0", "-6 7 0", "-5 -7 8 0" ])

def mkRootUnitMixed1Uip (unsat : Bool) : String :=
  let base :=
    [ "1 2 3 4 0", "1 2 3 -4 0", "1 2 -3 4 0", "1 2 -3 -4 0"
    , "1 -2 3 4 0", "1 -2 3 -4 0", "1 -2 -3 4 0" ]
  let cls := base ++ (if unsat then [ "1 -2 -3 -4 0", "-1 0" ] else [ "-1 0" ])
  joinLines (mkHeader 4 cls.length :: cls)

def mkMinDiamondUnsat : String :=
  joinLines (mkHeader 8 10 ::
    [ "1 2 3 0", "-2 4 0", "-3 4 0", "-4 5 0", "-5 6 0"
    , "-4 -6 7 0", "-6 -7 0", "-1 8 0", "-1 -8 0", "-2 -3 0" ])

def mkOrdering4 : String :=
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

def mkShrinkBinaryUnsat : String :=
  joinLines (mkHeader 7 10 ::
    [ "1 2 3 4 0", "-2 5 0", "-3 5 0", "-5 6 0", "-5 -6 0"
    , "1 -2 -3 4 0", "-1 7 0", "-1 -7 0", "-4 7 0", "-4 -7 0" ])

def mkLuckyPosSat : String :=
  joinLines (mkHeader 6 4 ::
    [ "1 -2 3 0", "-1 2 4 0", "-3 -4 5 0", "-5 6 0" ])

def mkLuckyNegSat : String :=
  joinLines (mkHeader 6 4 ::
    [ "-1 2 -3 0", "1 -2 -4 0", "3 4 -5 0", "5 -6 0" ])

def mkAnalyzeReduceFlushSat : String :=
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

def mkProbeHbrSat : String :=
  joinLines (mkHeader 8 9 ::
    [ "-1 2 0", "-1 3 0", "-2 -3 4 0", "4 5 6 0", "-4 -5 -6 0"
    , "5 7 8 0", "-5 -7 -8 0", "-1 7 8 0", "1 7 -8 0" ])

def mkTransitiveSat : String :=
  joinLines (mkHeader 6 9 ::
    [ "-1 2 0", "-2 3 0", "-1 3 0", "3 4 5 0", "-3 -4 -5 0"
    , "4 5 6 0", "-4 -5 -6 0", "-1 4 6 0", "1 4 -6 0" ])

def mkVivifySat : String :=
  joinLines (mkHeader 6 8 ::
    [ "1 2 3 4 0", "1 3 0", "1 5 -6 0", "1 -5 6 0"
    , "2 5 6 0", "2 -5 -6 0", "3 4 5 0", "-3 -4 -6 0" ])

def mkSubstSccSat : String :=
  joinLines (mkHeader 6 8 ::
    [ "-1 2 0", "-2 1 0", "-2 3 0", "-3 2 0"
    , "3 4 5 0", "-3 -4 6 0", "4 5 -6 0", "-4 -5 6 0" ])

def mkSubstSccUnsat : String :=
  joinLines (mkHeader 3 6 ::
    [ "-1 2 0", "-2 3 0", "-3 -1 0", "1 -2 0", "2 -3 0", "3 1 0" ])

def mkCongAndSat : String :=
  joinLines (mkHeader 7 10 ::
    [ "-3 1 0", "-3 2 0", "3 -1 -2 0"
    , "-4 1 0", "-4 2 0", "4 -1 -2 0"
    , "3 -4 5 0", "-3 4 5 0", "5 6 7 0", "-5 -6 -7 0" ])

def mkCongIteUnsat : String :=
  joinLines (mkHeader 6 12 ::
    [ "-1 -4 2 0", "-1 4 -2 0", "1 -4 3 0", "1 4 -3 0"
    , "-1 -5 2 0", "-1 5 -2 0", "1 -5 3 0", "1 5 -3 0"
    , "4 5 6 0", "-4 -5 6 0", "4 5 -6 0", "-4 -5 -6 0" ])

def mkCongXorUnsat : String :=
  joinLines (mkHeader 5 12 ::
    [ "-3 1 2 0", "-3 -1 -2 0", "3 -1 2 0", "3 1 -2 0"
    , "-4 1 2 0", "-4 -1 -2 0", "4 -1 2 0", "4 1 -2 0"
    , "3 4 5 0", "-3 -4 5 0", "3 4 -5 0", "-3 -4 -5 0" ])

def mkSweepConeSat : String :=
  joinLines (mkHeader 8 13 ::
    [ "-3 1 0", "-3 2 0", "3 -1 -2 0"
    , "-4 1 0", "-4 5 0", "4 -1 -5 0"
    , "-5 2 0", "-5 6 0", "5 -2 -6 0"
    , "-1 6 0", "3 -4 7 0", "-3 4 7 0", "7 8 0" ])

def mkFwdSubStrSat : String :=
  joinLines (mkHeader 9 11 ::
    [ "1 2 3 4 5 0"
    , "1 6 7 0", "1 -6 -7 0", "1 8 9 0", "1 -8 -9 0"
    , "-1 2 3 0", "-1 2 3 0"
    , "-1 6 -7 0", "-1 -6 7 0", "-1 8 -9 0", "-1 -8 9 0" ])

def mkBveGatesSat : String :=
  joinLines (mkHeader 8 10 ::
    [ "-3 1 0", "-3 2 0", "3 -1 -2 0"
    , "3 4 5 0", "-3 5 6 0", "-4 -5 -6 0"
    , "4 5 -6 0", "7 8 0", "-7 4 5 0", "7 -4 -5 0" ])

def mkBceSat : String :=
  joinLines (mkHeader 9 10 ::
    [ "1 2 3 0"
    , "1 4 5 0", "1 -4 -5 0", "1 5 6 0", "1 -5 -6 0"
    , "-1 -2 7 8 0", "-1 -2 -7 -8 0", "-1 -2 8 9 0"
    , "-1 -2 -8 -9 0", "-1 -2 7 -9 0" ])

def mkBvaFactorSat : String :=
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

/-! ## 2. Test Case Representation & Layer A Verification -/

structure KissatCase where
  name : String
  cnf : String
  workLen : Nat
  fuel : Nat
  expected : Nat
  reqMask : Nat := 0
  checkLayerA : Bool := true

def checkLayerACase (tc : KissatCase) : Bool :=
  if !tc.checkLayerA then true
  else
    match parseDimacs tc.cnf.toUTF8.toList with
    | none => false
    | some cnf =>
      match cdclSolve tc.fuel cnf with
      | .sat σ => tc.expected == 10 && checkModel cnf σ
      | .unsat => tc.expected == 20
      | .unknown => false

/-! ## 3. Artifact Generation & C++ Driver Builders -/

def cEscapeString (s : String) : String :=
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

def mkCasesHeader (cases : List KissatCase) : String :=
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

def mkFullCasesHeader (cases : List KissatCase) : String :=
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

def mkBasicDiffDriverCpp (genHeader casesHeader : String) (passTag : String := "") : String :=
  let passLine := if passTag.isEmpty then
    "  std::printf(\"PASS: cpp differential (%zu cases x 2 alignments)\\n\", kKissatCaseCount);"
  else
    s!"  std::printf(\"PASS: {passTag} cpp differential (%zu cases x 2 alignments)\\n\", kKissatCaseCount);"
  String.intercalate "\n"
    [ "#include <cstdint>"
    , "#include <cstdio>"
    , "#include <cstdlib>"
    , "#include <vector>"
    , s!"#include \"{genHeader}\""
    , s!"#include \"{casesHeader}\""
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
    , passLine
    , "  return 0;"
    , "}" ]

def writeC0Artifacts (outDir : System.FilePath) (mod : Module) (cases : List KissatCase)
    (prefix_ : String) (driverCpp : String) (isFull : Bool := false)
    (passLabel : String := "") : IO UInt32 := do
  for c in cases do
    if !checkLayerACase c then
      throw (IO.userError s!"X2-LayerA cdclSolve mismatch on case '{c.name}'")
  IO.FS.createDirAll outDir
  let cpp ← match ppTModule mod with
    | .ok s => pure s
    | .error e => throw (IO.userError e)
  let qbe ← match PrintQbe.module mod with
    | .ok s => pure s
    | .error e => throw (IO.userError e)
  IO.FS.writeFile (outDir / s!"{prefix_}_gen.hpp") cpp
  IO.FS.writeFile (outDir / s!"{prefix_}.ssa") (qbe ++ "\n")
  let casesHeader := if isFull then mkFullCasesHeader cases else mkCasesHeader cases
  IO.FS.writeFile (outDir / s!"{prefix_}_cases.h") (casesHeader ++ "\n")
  IO.FS.writeFile (outDir / s!"{prefix_}_driver.cpp") (driverCpp ++ "\n")
  let label := if passLabel.isEmpty then prefix_ else passLabel
  IO.println s!"Generated {label} C0 artifacts ({cases.length} cases) in {outDir}."
  pure 0

end LeanQbeTest.T.KissatC0Harness
