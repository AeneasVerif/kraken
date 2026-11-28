module

import LeanQbe.T.PrintCpp
import LeanQbe.T.Legal
import LeanQbe.T.Examples.LratBytes
import LeanQbe.T.Examples.LratBytesSpec
import LeanQbe.T.Examples.LratBytesLemmas
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.Examples.LratBytesSpec

/-!
# Verification, Axiom Audit, and C++20 Differential Suite for `LeanQbe.T.Examples.LratBytes`

- Pure Lean `#guard` checks covering `runLratCheckBytes`, DIMACS round-trip, deletion,
  multi-byte LEB128, malformed inputs, and `PrintCpp` lowering across all `LegalTarget`s.
- 1-line `#print axioms` checks for all headline theorems.
- C++20 code generator (`runGenerate` / `main`) emitting standalone TUs, namespaced pre/post-Legal
  headers, and a differential test driver driven directly by Lean's `runLratCheckBytes` oracle.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.LratBytesTest

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.LratBytes
open Std.Sat

-- ============================================================================
-- 1. Test vectors (untrusted DIMACS + binary LRAT bytes)
-- ============================================================================

/-- 2-variable 4-clause UNSAT DIMACS with a comment line and extra whitespace. -/
def unsat2Dimacs : List UInt8 :=
  ("c 2-var unsat\np cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n").toUTF8.toList

/-- Valid binary LRAT proof for `unsat2Dimacs` including an explicit deletion step:
    - `a 5  1 0  1 2 0`
    - `d 1 2 0`
    - `a 6 -1 0  3 4 0`
    - `a 7  0    5 6 0` -/
def unsat2AcceptPrf : List UInt8 :=
  [0x61, 10, 2, 0, 2, 4, 0, 0x64, 2, 4, 0, 0x61, 12, 3, 0, 6, 8, 0, 0x61, 14, 0, 10, 12, 0]

/-- Invalid proof for `unsat2Dimacs`: deletes clause 1 before citing it as a hint. -/
def unsat2UseAfterDelPrf : List UInt8 :=
  [0x64, 2, 0, 0x61, 10, 2, 0, 2, 4, 0, 0x61, 12, 3, 0, 6, 8, 0, 0x61, 14, 0, 10, 12, 0]

/-- Invalid proof for `unsat2Dimacs`: wrong hint list on final empty clause. -/
def unsat2BadHintPrf : List UInt8 :=
  [0x61, 10, 2, 0, 2, 4, 0, 0x61, 12, 3, 0, 6, 8, 0, 0x61, 14, 0, 10, 0]

/-- 64-variable 2-clause UNSAT DIMACS (`x64 ∧ ¬x64`) exercising 2-byte LEB128 literals. -/
def var64Dimacs : List UInt8 := ("p cnf 64 2\n64 0\n-64 0\n").toUTF8.toList

/-- Valid binary LRAT proof for `var64Dimacs` exercising a 2-byte LEB128 literal
    (`lit = +64`, encoded as `2 * 64 = 128 = [0x80, 0x01]`):
    - `a 3  64 0  1 0`
    - `a 4   0    3 2 0` -/
def var64Leb2AcceptPrf : List UInt8 :=
  [0x61, 0x06, 0x80, 0x01, 0x00, 0x02, 0x00, 0x61, 0x08, 0x00, 0x06, 0x04, 0x00]

/-- Malformed DIMACS header (wrong format token `sat` instead of `cnf`). -/
def malformedDimacs : List UInt8 := ("p sat 1 2\n1 0\n-1 0\n").toUTF8.toList

/-- Out-of-range variable in DIMACS body (`var 2 > nvars 1`). -/
def oobVarDimacs : List UInt8 := ("p cnf 1 2\n2 0\n-1 0\n").toUTF8.toList

/-- Satisfiable 2-clause formula `(1 ∨ 2) ∧ (-1 ∨ 2)`. -/
def sat2Dimacs : List UInt8 := ("p cnf 2 2\n1 2 0\n-1 2 0\n").toUTF8.toList

/-- Unrecognized proof tag byte (`0x78` = `'x'`). -/
def badTagPrf : List UInt8 := [0x78, 0x06, 0x00, 0x02, 0x04, 0x00]

/-- Differential test case: `(name, cnfBytes, prfBytes, workLen, expected)`. -/
structure DiffCase where
  name : String
  cnf : List UInt8
  prf : List UInt8
  workLen : Nat
  expected : Bool

def diffCases : List DiffCase :=
  [ ⟨"nv_accept", nvDimacsBytes, nvLratAcceptBytes, 512, true⟩
  , ⟨"nv_reject_bad_hint", nvDimacsBytes, nvLratRejectBytes, 512, false⟩
  , ⟨"nv_small_work_127", nvDimacsBytes, nvLratAcceptBytes, 127, false⟩
  , ⟨"nv_small_work_0", nvDimacsBytes, nvLratAcceptBytes, 0, false⟩
  , ⟨"nv_empty_prf", nvDimacsBytes, [], 512, false⟩
  , ⟨"var64_leb2_accept", var64Dimacs, var64Leb2AcceptPrf, 2048, true⟩
  , ⟨"var64_leb2_tight_work", var64Dimacs, var64Leb2AcceptPrf, 400, false⟩
  , ⟨"unsat2_accept_with_del", unsat2Dimacs, unsat2AcceptPrf, 1024, true⟩
  , ⟨"unsat2_use_after_del", unsat2Dimacs, unsat2UseAfterDelPrf, 1024, false⟩
  , ⟨"unsat2_bad_hint", unsat2Dimacs, unsat2BadHintPrf, 1024, false⟩
  , ⟨"malformed_header", malformedDimacs, nvLratAcceptBytes, 512, false⟩
  , ⟨"oob_var_dimacs", oobVarDimacs, nvLratAcceptBytes, 512, false⟩
  , ⟨"sat2_rejected", sat2Dimacs, nvLratAcceptBytes, 512, false⟩
  , ⟨"bad_prf_tag", nvDimacsBytes, badTagPrf, 512, false⟩
  ]

-- ============================================================================
-- 2. Pure Lean `#guard` checks
-- ============================================================================

#guard (parseDimacs (encodeDimacs nvBytesCnf)).isSome == true
#guard (parseDimacs malformedDimacs).isNone == true
#guard diffCases.all fun c => runLratCheckBytes c.cnf c.prf c.workLen == c.expected

-- Skeptical-Auditor Ground-Truth Grounded Checks on `encodeDimacs`
example : asciiSpace = (32 : UInt8) := rfl
example : asciiNewline = (10 : UInt8) := rfl
example : asciiMinus = (45 : UInt8) := rfl
example : asciiZero = (48 : UInt8) := rfl
example : dimacsHeaderPrefix = [112, 32, 99, 110, 102, 32] := rfl
example : [asciiZero, asciiNewline] = [48, 10] := rfl

private def mkCnf (cls : List (List (Nat × Bool))) : CNF Nat :=
  cls.foldl (fun acc ls => acc.add (CNF.Clause.ofLiterals ls)) CNF.empty

private def dimacsCases : List (CNF Nat × String) :=
  [ (mkCnf [], "p cnf 0 0\n")
  , (nvBytesCnf, "p cnf 1 2\n1 0\n-1 0\n")
  , (mkCnf [[(1, true), (12, false)], [(1, false)]], "p cnf 12 2\n1 -12 0\n-1 0\n")
  , (mkCnf [[(1, true), (2, false), (3, true)], [(2, true), (3, false)], [(1, false)]],
      "p cnf 3 3\n1 -2 3 0\n2 -3 0\n-1 0\n")
  , (mkCnf [[]], "p cnf 0 1\n0\n")
  , (mkCnf [[(100, true), (250, false)]], "p cnf 250 1\n100 -250 0\n")
  ]

private def cnfLits (cnf : CNF Nat) : List (List (Nat × Bool)) :=
  cnf.clauses.toList.map (·.literals)

#guard dimacsCases.all fun (cnf, txt) =>
  let bs := encodeDimacs cnf
  String.fromUTF8? bs.toByteArray == some txt &&
  bs == txt.toUTF8.toList &&
  match parseDimacs bs with | some res => cnfLits res == cnfLits cnf | none => false

-- `PrintCpp` codegen checks (pre-Legal `ppTModule` + all `LegalTarget`s)
#guard (ppTModule lratBytesModule).isOk
#guard match ppTModule lratBytesModule with
  | .ok s => ["lb_parse_dimacs_header(", "lb_parse_dimacs_body(", "lb_read_add_lits(",
      "lb_rup_check(", "lb_check_prf(", "lrat_check_bytes("].all fun fn =>
      (s.splitOn fn).length > 1
  | .error _ => false
#guard [LegalTarget.aarch64, .scalar64, .x64AVX2, .x64AVX512].all fun t =>
  (ppModule (lratBytesFns.map (Fn.legal t))).isOk

-- ============================================================================
-- 3. 1-line `#print axioms` audit on headline theorems
-- ============================================================================

#print axioms LeanQbe.T.Examples.LratBytes.lratBytesFns_wf
#print axioms LeanQbe.T.Examples.LratBytes.parseDimacs_encodeDimacs
#print axioms LeanQbe.T.Examples.LratBytes.runLratCheckBytes_sound
#print axioms LeanQbe.T.Examples.LratBytes.lratBytesEnv_sound
#print axioms LeanQbe.T.Examples.LratBytes.lratBytesEnv_moduleOk
#print axioms LeanQbe.T.Examples.LratBytes.lratCheckBytes_correct
#print axioms LeanQbe.T.Examples.LratBytes.lratCheckBytes_encoded_correct
#print axioms LeanQbe.T.Examples.LratBytes.lratCheckBytes_accepts
#print axioms LeanQbe.T.Examples.LratBytes.lratCheckBytes_rejects
#print axioms LeanQbe.T.Examples.LratBytes.nvBytesCnf_unsat

-- ============================================================================
-- 4. C++20 differential generator (`runGenerate` / `main`)
-- ============================================================================

private def emitNamespace (ns : String) (fns : List Fn) : Except String String := do
  let symMap ← buildSymMap fns
  let decls := String.join (fns.map (ppFnDecl symMap))
  let defs := String.intercalate "\n" (fns.map (ppFn symMap))
  pure (s!"namespace {ns} " ++ "{\n" ++ decls ++ "\n" ++ defs ++ "\n} // namespace " ++ ns ++ "\n")

private def ppByteList (bs : List UInt8) : String :=
  "{" ++ String.intercalate ", " (bs.map fun b => toString b.toNat) ++ "}"

private def ppDiffCase (c : DiffCase) : String :=
  let expected := if runLratCheckBytes c.cnf c.prf c.workLen then 1 else 0
  s!"  DiffCase\{\"{c.name}\", {ppByteList c.cnf}, {ppByteList c.prf}, {c.workLen}u, {expected}u},"

private def mkDriverCpp : String :=
  let caseLines := String.intercalate "\n" (diffCases.map ppDiffCase)
  String.intercalate "\n"
    [ "#include <cstdint>"
    , "#include <cstdio>"
    , "#include <cstdlib>"
    , "#include <vector>"
    , "#include \"gen_lrat_suite.hpp\""
    , ""
    , "struct DiffCase {"
    , "  const char* name;"
    , "  std::vector<uint8_t> cnf;"
    , "  std::vector<uint8_t> prf;"
    , "  uint64_t work_len;"
    , "  uint64_t expected;"
    , "};"
    , ""
    , "template <typename Fn>"
    , "static void run_suite(const char* target, Fn fn, const std::vector<DiffCase>& cases) {"
    , "  for (const auto& tc : cases) {"
    , "    ::tqbe::Mem mem;"
    , "    const uint64_t cnf_ptr = 0x1000ULL;"
    , "    const uint64_t prf_ptr = cnf_ptr + tc.cnf.size();"
    , "    const uint64_t work_ptr = prf_ptr + tc.prf.size();"
    , "    const size_t total = tc.cnf.size() + tc.prf.size() + static_cast<size_t>(tc.work_len);"
    , "    if (total > 0) mem.alloc(cnf_ptr, total, 0xA5);"
    , "    for (size_t i = 0; i < tc.cnf.size(); ++i)"
    , "      ::tqbe::store<::tqbe::bits<8>>(mem,"
    , "        ::tqbe::bits<64>(cnf_ptr + i), ::tqbe::bits<8>(tc.cnf[i]));"
    , "    for (size_t i = 0; i < tc.prf.size(); ++i)"
    , "      ::tqbe::store<::tqbe::bits<8>>(mem,"
    , "        ::tqbe::bits<64>(prf_ptr + i), ::tqbe::bits<8>(tc.prf[i]));"
    , "    const uint64_t got = fn("
    , "      mem,"
    , "      ::tqbe::bits<64>(cnf_ptr),"
    , "      ::tqbe::bits<64>(tc.cnf.size()),"
    , "      ::tqbe::bits<64>(prf_ptr),"
    , "      ::tqbe::bits<64>(tc.prf.size()),"
    , "      ::tqbe::bits<64>(work_ptr),"
    , "      ::tqbe::bits<64>(tc.work_len)).word(0);"
    , "    if (got != tc.expected) {"
    , "      std::fprintf(stderr, \"FAIL [%s] %s: got=%llu expected=%llu\\n\","
    , "        target, tc.name, (unsigned long long)got, (unsigned long long)tc.expected);"
    , "      std::exit(1);"
    , "    }"
    , "    auto chk = [&](const char* w, const std::vector<uint8_t>& v, uint64_t p) {"
    , "      for (size_t i = 0; i < v.size(); ++i) {"
    , "        if (::tqbe::load<::tqbe::bits<8>>(mem, ::tqbe::bits<64>(p + i)).word(0) != v[i]) {"
    , "          std::fprintf(stderr, \"FAIL [%s] %s: %s byte %zu mutated\\n\","
    , "            target, tc.name, w, i); std::exit(1);"
    , "        }"
    , "      }"
    , "    };"
    , "    chk(\"cnf\", tc.cnf, cnf_ptr); chk(\"prf\", tc.prf, prf_ptr);"
    , "  }"
    , "}"
    , ""
    , "int main() {"
    , "  const std::vector<DiffCase> cases = {"
    , caseLines
    , "  };"
    , "  run_suite(\"pre\", lrat_pre::lrat_check_bytes, cases);"
    , "  run_suite(\"aarch64\", lrat_aarch64::lrat_check_bytes, cases);"
    , "  run_suite(\"scalar64\", lrat_scalar64::lrat_check_bytes, cases);"
    , "  run_suite(\"avx2\", lrat_avx2::lrat_check_bytes, cases);"
    , "  run_suite(\"avx512\", lrat_avx512::lrat_check_bytes, cases);"
    , "  std::printf(\"OK: %zu cases x 5 targets \""
    , "    \"(pre, aarch64, scalar64, avx2, avx512) passed.\\n\", cases.size());"
    , "  return 0;"
    , "}"
    , ""
    ]

/-- Generate standalone C++20 TUs, `gen_lrat_suite.hpp`, and `gen_lrat_driver.cpp` in `outDir`. -/
def runGenerate (outDir : String) : IO UInt32 := do
  let writeChecked (fname : String) (res : Except String String) : IO Unit := do
    match res with
    | .ok s => IO.FS.writeFile s!"{outDir}/{fname}" s
    | .error e => throw (IO.userError s!"emit {fname} failed: {e}")

  writeChecked "gen_lrat_mod.cpp" (ppTModule lratBytesModule)
  writeChecked "gen_lrat_aarch64.cpp" (ppModule (lratBytesFns.map (Fn.legal .aarch64)))
  writeChecked "gen_lrat_avx2.cpp" (ppModule (lratBytesFns.map (Fn.legal .x64AVX2)))
  let blocks ← [
    ("lrat_pre", lratBytesFns),
    ("lrat_aarch64", lratBytesFns.map (Fn.legal .aarch64)),
    ("lrat_scalar64", lratBytesFns.map (Fn.legal .scalar64)),
    ("lrat_avx2", lratBytesFns.map (Fn.legal .x64AVX2)),
    ("lrat_avx512", lratBytesFns.map (Fn.legal .x64AVX512))
  ].mapM fun (ns, fns) =>
    match emitNamespace ns fns with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"emitNamespace {ns}: {e}")
  let header := "#pragma once\n#include \"tqbe_rt.hpp\"\n\n" ++ String.intercalate "\n" blocks
  IO.FS.writeFile s!"{outDir}/gen_lrat_suite.hpp" header
  IO.FS.writeFile s!"{outDir}/gen_lrat_driver.cpp" mkDriverCpp
  IO.println s!"Generated LRAT C++20 suite ({diffCases.length} cases x 5 targets) in {outDir}."
  pure 0

end LeanQbeTest.T.LratBytesTest

/-- Entrypoint for standalone codegen CLI execution (`args[0]` = output directory). -/
public def main (args : List String) : IO UInt32 :=
  LeanQbeTest.T.LratBytesTest.runGenerate (args.headD "/tmp/leanqbe-tlrat")
