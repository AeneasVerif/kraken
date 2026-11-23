> **[Historical design note]** Written during an earlier milestone (at commit `384800c`); file sizes and build timings reflect that snapshot. See `LeanQbe-README.md` for current paths and audit targets.

# Untrusted-Bytes LRAT Proof Checker on `LeanQbe.T`

Modules covered:
- `LeanQbe/T/Examples/LratBytes.lean`
- `LeanQbe/T/Examples/LratBytesSpec.lean`
- `LeanQbe/T/Examples/LratBytesDimacsLemmas.lean`
- `LeanQbe/T/Examples/LratBytesRupLemmas.lean`
- `LeanQbe/T/Examples/LratBytesCheckLemmas.lean`
- `LeanQbe/T/Examples/LratBytesLemmas.lean`
- `LeanQbeTest/T/LratBytesTest.lean`
- `test/t_lrat/run.sh`
- `docs/reports/t_lrat.md`

## Status

| Deliverable | State |
|---|---|
| 6-function typed-IR module (`lratBytesModule : LeanQbe.T.Module`) | done (`LratBytes.lean`, 998 LOC): callees-first order, `≤ 6` `i64` args, single `i64` return, `exits = []` |
| Well-formedness & pure/memory specs (`Func.Wf`, `lratBytesFns_wf`, `lratBytesModule_namesNodup`, `WorkCfg`/`WorkState`, `runLratCheckBytes`, 6 typed `Spec`s) | done (`LratBytesSpec.lean`, 1,060 LOC): all 6 `Func.Wf` proved via `t_wf_reify` |
| DIMACS parser & encoder soundness (`lbParseDimacsHeader_correct`, `lbParseDimacsBody_correct`, `parseBodyPure_sound`, `parseDimacs_encodeDimacs`) | done (`LratBytesDimacsLemmas.lean`, 1,238 LOC) |
| Clause reader & RUP verifier soundness (`lbReadAddLits_correct`, `lbRupCheck_correct`, `rupCheckPure_sound`) | done (`LratBytesRupLemmas.lean`, 1,159 LOC) |
| Top-level checker & pure soundness (`checkPrfAux_sound_of`, `runLratCheckBytes_sound_of`, `lbCheckPrf_correct_of`, `lratCheckBytes_exact_of`) | done (`LratBytesCheckLemmas.lean`, 1,327 LOC) |
| Headline theorems, `ModuleOk`, & non-vacuity (`lratBytesEnv_moduleOk`, `lratCheckBytes_correct`, `lratCheckBytes_encoded_correct`, `lratCheckBytes_accepts_nonvacuous`, `lratCheckBytes_rejects_nonvacuous`, 1-line aliases `lratCheckBytes_accepts`/`lratCheckBytes_rejects`, `@[simp]` length exports) | done (`LratBytesLemmas.lean`, 531 LOC) |
| Verification, axiom audit & C++20 differential harness (`LeanQbeTest/T/LratBytesTest.lean`, `test/t_lrat/run.sh`) | done (296 + 40 LOC): 14 differential cases × 5 targets × 2 modes × 2 compilers (`g++`, `clang++` ASan+UBSan) all pass |

## Architecture

### Typed-IR Module (`lratBytesModule`)
All six functions are defined with executable `def` + `tqbe(...)` notation (preserving both fast elaboration and runtime `PrintCpp.ppTModule` / `Fn.legal` execution) and assembled in callees-first acyclic order in `lratBytesModule`:

1. `lb_parse_dimacs_header(cnf_ptr, cnf_end, work_ptr) -> i64`
2. `lb_parse_dimacs_body(cnf_end, work_ptr) -> i64`
3. `lb_read_add_lits(cur, prf_end, work_ptr) -> i64`
4. `lb_rup_check(cur, prf_end, work_ptr, clause_ptr) -> i64`
5. `lb_check_prf(work_ptr, prf_end) -> i64`
6. `lrat_check_bytes(cnf_ptr, cnf_len, prf_ptr, prf_len, work_ptr, work_len) -> i64`

Memory layout in the caller-supplied `work` scratch buffer mirrors the earlier untyped-IR version:
- Header (`work + 0..79`): `max_var`, `nclauses`, `cap_c`, `val_base`, `trail_base`, `trail_lim`, `ctab_base`, `pool_lim`, `pool_top`, `prf_cur` (ten `i64` slots).
- Arrays (`work + 80..`): `val` (`i8`), `trail` (`i32`), `ctab` (`i64`), and `pool` (`i32` zero-terminated clauses).
- Input regions `cnfBytes` and `prfBytes` are read-only and guaranteed byte-for-byte unchanged on return (`lratCheckBytesSpec`).

### Key Typed-IR Adaptations & Pure Mirror Note
- **Explicit width conversions and `.bool` branches:** Untyped `loadub`/`loadsw`/`storeb`/`storew` become typed `load i8` + `zext`, `load i32` + `sext`, and `trunc` + `store i8`/`store i32` (with zero-immediate stores `store 0:i8`/`store 0:w`). Comparisons (`ceql`, `cnel`, `cultl`, `culel`, `csltl`, `cnew`) return `.bool`, boolean disjunctions use `.or .bool`, and `jnz` consumes `.bool`.
- **Pure mirror (`rupInnerPure` / `rupPhase2Aux`) simplification:** In the earlier untyped IR, `jnz %unit` tested `lo32 unit != 0`. In `LeanQbe.T`, `jnz` takes `.bool`, so `rupInner` and `lbRupCheck` emit `%unit_nz:b = cnel %unit, 0; jnz %unit_nz, ...`. Correspondingly, the pure mirror functions `rupInnerPure` and `rupPhase2Aux` test `unit != 0` directly instead of `lo32 unit != 0`. Because `unit` always satisfies `IsInt32 unit`, the two conditions are equivalent; `rupCheckPure_sound` is proved directly against the `unit != 0` mirror, and none of the headline theorems (`runLratCheckBytes_sound`, `lratCheckBytes_correct`, `lratBytesEnv_moduleOk`, `lratCheckBytes_encoded_correct`) mention the internal mirror.

### Self-Containment Audit
All 7 `.lean` files have **zero** imports of earlier untyped-IR modules (`LeanQbe.Examples.*`, `LeanQbe.IL`, `LeanQbe.Logic.*`, `LeanQbe.Main*`, `LeanQbe.Wf`, `LeanQbe.Abi`, `LeanQbe.Notation`). Every pure DIMACS/LRAT definition, soundness proof, and non-vacuity instance (`parseDimacs`, `encodeDimacs`, `ValidDimacsCnf`, `WorkCfg`, `WorkState`, `runLratCheckBytes`, `nvBytesCnf`, `nvDimacsBytes`, `nvLratAcceptBytes`, `nvLratRejectBytes`) is self-contained under `LeanQbe.T.Examples.LratBytes*`, importing strictly `LeanQbe.T.*`, `Kraken.*`, and `Std.Sat.CNF`.

> **Note on Kraken import:** `LeanQbe/T/Examples/LratBytesSpec.lean` imports `Kraken.Bedrock2.Test.LratTrimCheckProof` (a frozen Kraken test module providing the pure LRAT trim-check soundness lemmas `lrat_check_sound` / `lrat_add_sound`), matching the earlier proof's dependency boundary.

### Headline Theorems & Native-Certificate Exports
- `lratBytesEnv_moduleOk : ModuleOk lratBytesEnv lratBytesModule`
- `lratCheckBytes_correct : Func.spec lratBytesEnv lratCheckBytes ...` (`r = 0 ∨ r = 1`, `r = 1 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`, memory restored, `exits = []`)
- `lratCheckBytes_encoded_correct` (structured `ValidDimacsCnf` round-trip contract)
- `lratCheckBytes_accepts_nonvacuous` & `lratCheckBytes_rejects_nonvacuous` (concrete-memory source-level non-vacuity on `nvDimacsBytes` / `nvLratAcceptBytes` / `nvLratRejectBytes`), plus short aliases `lratCheckBytes_accepts` / `lratCheckBytes_rejects` so `#print axioms` stays ≤ 120 columns (single-line report for `scripts/check.sh` Step 4)
- `@[simp]` length exports for native certificates: `nvDimacsBytes_length`, `nvLratAcceptBytes_length`, `nvLratRejectBytes_length`

## File Sizes, Timings, and Hygiene

### Standalone `timeout 180 lake env lean -DwarningAsError=true <file>`

| File | Role | LOC | Standalone Wall (s) | Status |
|---|---|---:|---:|---|
| `LeanQbe/T/Examples/LratBytes.lean` | Impl + pure spec | 998 | 1.153 | `exit=0` |
| `LeanQbe/T/Examples/LratBytesSpec.lean` | `Wf` + specs + mirror | 1,060 | 2.727 | `exit=0` |
| `LeanQbe/T/Examples/LratBytesDimacsLemmas.lean` | DIMACS proofs | 1,238 | 4.092 | `exit=0` |
| `LeanQbe/T/Examples/LratBytesRupLemmas.lean` | Add-lits + RUP proofs | 1,159 | 5.326 | `exit=0` |
| `LeanQbe/T/Examples/LratBytesCheckLemmas.lean` | Check-prf + top-level | 1,327 | 4.414 | `exit=0` |
| `LeanQbe/T/Examples/LratBytesLemmas.lean` | `ModuleOk` + non-vacuity | 531 | 2.188 | `exit=0` |
| `LeanQbeTest/T/LratBytesTest.lean` | `#guard` + axioms + C++ gen | 296 | 0.794 | `exit=0` |
| `test/t_lrat/run.sh` | C++20 differential script | 40 | — | `exit=0` |

- **Totals vs caps:** Impl = **998 LOC** (cap `≤ 1,200`); Proof = **5,315 LOC** (cap `≤ 6,000`); max single `.lean` file = **1,327 LOC** (cap `≤ 2,000`); max standalone build = **5.326 s** (cap `< 180 s`).
- **Hygiene:** `0` `sorry`, `0` custom `axiom`, `0` native tactics (`bv_decide`, `native_decide`, `ofReduceBool`).

### Axiom Audit (`LeanQbeTest/T/LratBytesTest.lean`)
All ten audited headline theorems emit complete single-line `#print axioms` reports strictly within `[propext, Classical.choice, Quot.sound]`:
- `LeanQbe.T.Examples.LratBytes.lratBytesFns_wf` (`[propext, Classical.choice]`)
- `LeanQbe.T.Examples.LratBytes.parseDimacs_encodeDimacs`
- `LeanQbe.T.Examples.LratBytes.runLratCheckBytes_sound`
- `LeanQbe.T.Examples.LratBytes.lratBytesEnv_sound`
- `LeanQbe.T.Examples.LratBytes.lratBytesEnv_moduleOk`
- `LeanQbe.T.Examples.LratBytes.lratCheckBytes_correct`
- `LeanQbe.T.Examples.LratBytes.lratCheckBytes_encoded_correct`
- `LeanQbe.T.Examples.LratBytes.lratCheckBytes_accepts` (alias of `lratCheckBytes_accepts_nonvacuous`)
- `LeanQbe.T.Examples.LratBytes.lratCheckBytes_rejects` (alias of `lratCheckBytes_rejects_nonvacuous`)
- `LeanQbe.T.Examples.LratBytes.nvBytesCnf_unsat`

## C++20 Differential & Sanitizer Verification (`test/t_lrat/run.sh`)
`test/t_lrat/run.sh` writes all generated C++20 files and binaries to a temporary directory under `/tmp/` and verifies:
1. Standalone `-c` compilation of `gen_lrat_mod.cpp` (`PrintCpp.ppTModule lratBytesModule`), `gen_lrat_aarch64.cpp`, and `gen_lrat_avx2.cpp`.
2. Differential execution of **14 test cases** (covering `nv_accept`, `nv_reject_bad_hint`, tight/zero work buffers, empty proof, 2-byte LEB128 literals with 64 vars, 2-var 4-clause UNSAT with explicit deletion, use-after-delete rejection, bad hint rejection, malformed header, out-of-range variable, satisfiable formula rejection, bad proof tag) across **5 targets** (`pre`, `aarch64`, `scalar64`, `avx2`, `avx512`) against Lean's `runLratCheckBytes` ground truth, asserting non-zero-initialized (`0xA5`) work buffers and byte-for-byte preservation of `cnfBytes` and `prfBytes`.
3. Executed under both `-DTQBE_CATCH_UB` and default trap mode, compiled with both `g++ -std=c++20 -O2 -Wall -Wextra -Werror` and `clang++ -std=c++20 -O2 -Wall -Wextra -Werror -fsanitize=undefined,address` (**280/280 runs passed, 0 sanitizer errors, 0 warnings**).
