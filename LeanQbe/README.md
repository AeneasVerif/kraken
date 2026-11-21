# lean-qbe: the verified `LeanQbe.T` compiler and verified workloads

`LeanQbe.T` is a typed SSA intermediate language with a weakest-precondition program logic
(`Func.wp`) and an optimizing compiler to x86-64 (SysV) and AArch64 (AAPCS64), written and
verified in Lean 4 (`leanprover/lean4:nightly-2026-11-08`). Programs are written in **C0**, a
small C subset elaborated into `LeanQbe.T` by a Lean macro. The compiler produces a
kernel-checked certificate (`LinkedCert`) relating every source function's `Func.wp` spec to
its machine code under the Kraken x86-64 / AArch64 instruction semantics.

## Verified workstreams and theorem-auditing index

Each workstream has audit files under `LeanQbeTest/T/` that restate its headline theorems with
full, unabbreviated types, explain every hypothesis, and end with one-line `#print axioms`
reports (standard axioms only). Architecture-specific audits are split so that no module
imports both `Kraken.X64` and `Kraken.AArch64`.

| # | Workstream | What is audited | Audit files |
|---|---|---|---|
| 1 | **Verified Kissat SAT solver** (`D-Full`, `D-Plain`) | DIMACS spec; `D-Plain` SAT + UNSAT and `D-Full` UNSAT soundness of the x86-64 / AArch64 machine code ([details](#verified-kissat)) | [Spec](LeanQbeTest/T/KissatAuditSpec.lean), [X64](LeanQbeTest/T/KissatAuditX64.lean), [Arm64](LeanQbeTest/T/KissatAuditArm64.lean) |
| 2 | **Verified compiler, linker, `LinkRec` and `LinkScc`/`LinkLfp`** | IR passes, legalization, instruction selection (`@[scoped isel_step]` & `emitClean` via `IselStepAttr`/`IselStepRules`), `FlagRaOpt`, `LinkedCert`, cyclic & SCC-DAG modules | [Spec](LeanQbeTest/T/CompilerAuditSpec.lean), [X64](LeanQbeTest/T/CompilerAuditX64.lean), [Arm64](LeanQbeTest/T/CompilerAuditArm64.lean) |
| 3 | **Impure Lean 4 `LCNF` and `LeanLRC` lowering** | lowering of Lean's compiler IR (`LeanQbe/T/LeanLCNF`, `LeanQbe/T/LeanLRC`) into `LeanQbe.T` | [Audit](LeanQbeTest/T/LcnfAudit.lean) |
| 4 | **Verified native LRAT proof checker** (`LratBytes`) | `lrat_check_bytes` returns `1` only for valid DIMACS of an unsatisfiable CNF | [Spec](LeanQbeTest/T/LratAuditSpec.lean), [X64](LeanQbeTest/T/LratAuditX64.lean), [Arm64](LeanQbeTest/T/LratAuditArm64.lean) |
| 5 | **Cryptographic and data-structure workloads** (`ChaCha20` SIMD, 256-bit `Bignum`, `UnionFind`) | functional correctness of the example programs and their compiled code | [Spec](LeanQbeTest/T/WorkloadsAuditSpec.lean), [X64](LeanQbeTest/T/WorkloadsAuditX64.lean), [Arm64](LeanQbeTest/T/WorkloadsAuditArm64.lean) |
| 6 | **C0 frontend & separation-logic proof tooling** | `Func.wp` core rules, C0 elaborator/`Wf`, `C0HeadStep`/`C0Agrees`, `SepTree`/`SlabChain`/`C0Lens`, `ControlComb` & deduplicated `LegalEmit` | [Audit](LeanQbeTest/T/C0LogicAudit.lean) |

Check all audit files (each one also builds as part of `scripts/check.sh`):

```bash
lake build --wfail LeanQbeTest.T.KissatAuditSpec LeanQbeTest.T.KissatAuditX64 \
  LeanQbeTest.T.KissatAuditArm64 LeanQbeTest.T.CompilerAuditSpec LeanQbeTest.T.CompilerAuditX64 \
  LeanQbeTest.T.CompilerAuditArm64 LeanQbeTest.T.LcnfAudit LeanQbeTest.T.LratAuditSpec \
  LeanQbeTest.T.LratAuditX64 LeanQbeTest.T.LratAuditArm64 LeanQbeTest.T.WorkloadsAuditSpec \
  LeanQbeTest.T.WorkloadsAuditX64 LeanQbeTest.T.WorkloadsAuditArm64 LeanQbeTest.T.C0LogicAudit
```

## Verified Kissat

**Verified Kissat** is a port of the Kissat SAT solver to C0 with end-to-end machine-code
correctness theorems:

| Solver | Lean module | Functions | Algorithm | Proved |
|---|---|---|---|---|
| `D-Plain` | `LeanQbe.T.Examples.Kissat.Plain` | 59 | CDCL (`kissat --plain`): watched literals, 1UIP learning, minimization and shrinking, VSIDS heap / VMTF queue, restarts, rephasing, mode switching, lucky phases, clause reduction | **SAT and UNSAT**, x86-64 and AArch64, unconditional |
| `D-Full` | `LeanQbe.T.Examples.Kissat.Full` | 166 | CDCL + inprocessing: probing, vivification, forward/OTFS subsumption, BVE and BVA, congruence closure, equivalent-literal substitution, transitive reduction, SAT sweeping, local-search walking, … | **UNSAT soundness + UNSAT non-vacuity**, x86-64 and AArch64, unconditional |
| `D-Full M2a Sched` | `LeanQbe.T.Examples.Kissat.FullFastSched` | 173 | Stage-4/M2a fast scheduler (`15` fast-sched + `16/173` rows + `kissat_solve_bytes`) | **UNSAT soundness + NV**, x64/Arm64 cert parameterized on `ModuleOk` |
| `D-Full M2a Budgets` | `LeanQbe.T.Examples.Kissat.FullFastBveBudgets` | 7 | Fast BVE/Tarjan/budgeted inprocessing + `init_hdr` (`FullFastBveBudgetsLemmas`) | **UNSAT soundness + NV**, source `ModuleOk` (`7/7` + 21 externs) |
| `D-Full M2b FastCore` | `LeanQbe.T.Examples.Kissat.FullFastCore` | 3 | Stage-5 fast-core BCP (`[47..49]` spliced into `Full.fullModule`) | **UNSAT soundness + NV**, standalone + splice `ModuleOk` |
| `D-Full M2b BvaHeap` | `LeanQbe.T.Examples.Kissat.FullBvaHeap` | 13 | 3-hop BVA & max-degree binary heap factoring (`FullBvaHeapLemmas`) | **UNSAT soundness + NV**, `bvaHeap_moduleOk` |
| `D-Full M2b FullKitten` | `LeanQbe.T.Examples.Kissat.Full` (`FullKitten`) | 15 | Embedded sub-solver (`FullKittenLemmas`) | **UNSAT soundness + NV**, unconditional `fullKittenEnv_moduleOk` |

Both solvers export one C entry point:

```c
uint64_t kissat_solve_bytes(const uint8_t *cnf_ptr, uint64_t cnf_len,
                            uint8_t *work_ptr, uint64_t work_len, uint64_t fuel);
/* 10 = SAT, 20 = UNSAT, 0 = unknown (malformed DIMACS, out of fuel, or workspace too small) */
```

### Kissat: build and run

Prerequisites: `elan` (picks up `lean-toolchain`), a C compiler, and for AArch64 on an x86-64
host `aarch64-linux-gnu-gcc` and `qemu-aarch64`.

```bash
# Native solver binary (default: D-Full, x86-64, written to /tmp/kissat-leanqbe-full).
bash bench/kissat/build_solver.sh --module Full --arch x64 -o /tmp/kissat-leanqbe-full
/tmp/kissat-leanqbe-full [--work-mb <MB>] [--fuel <N>] input.cnf     # or '-' for stdin
printf 'p cnf 1 2\n1 0\n-1 0\n' | /tmp/kissat-leanqbe-full -          # s UNSATISFIABLE, exit 20

# D-Plain, AArch64 (runs under qemu-aarch64 on x86-64 hosts).
bash bench/kissat/build_solver.sh --module Plain --arch arm64 -o /tmp/kissat-leanqbe-plain-arm64
qemu-aarch64 -L /usr/aarch64-linux-gnu /tmp/kissat-leanqbe-plain-arm64 input.cnf

# Differential test suites (x86-64 + AArch64 + C++ ASan/UBSan, optional reference Kissat).
bash bench/kissat/run_full.sh --module Full
bash bench/kissat/run_plain.sh

# Proofs: build the three audit files, then the full quality gate.
lake build --wfail LeanQbeTest.T.KissatAuditSpec LeanQbeTest.T.KissatAuditX64 \
  LeanQbeTest.T.KissatAuditArm64
scripts/check.sh
```

[`scripts/check.sh`](scripts/check.sh) builds every library and both executables with warnings
as errors, rejects `sorry` and native-code tactics (`native_decide`, `bv_decide`, …), checks that
no module imports both `Kraken.X64` and `Kraken.AArch64`, and audits the axioms of every
`#print axioms` in the build plus the theorems listed in `scripts/headline.txt`.

### Kissat: what is proved

Start with the three audit files. They restate every headline theorem with its full type (no
wrapper definitions) and explain each hypothesis:

- [`KissatAuditSpec.lean`](LeanQbeTest/T/KissatAuditSpec.lean): the trusted specification
  (`CNF.Unsat`, `CNF.Sat`, `parseDimacs`) with executable checks, and the source-level contracts.
- [`KissatAuditX64.lean`](LeanQbeTest/T/KissatAuditX64.lean): the x86-64 machine-code theorems.
- [`KissatAuditArm64.lean`](LeanQbeTest/T/KissatAuditArm64.lean): the AArch64 mirror.

#### `D-Plain`: SAT and UNSAT, end to end

[`solve_x64_correct`](LeanQbe/T/Amd64/KissatPlain.lean#L64) and
[`solve_arm64_correct`](LeanQbe/T/Arm64/KissatPlain.lean#L64): for **any** executable that
contains the compiled 59-function module, and any call with the input bytes, a workspace, a
stack frame and an arbitrary caller frame `R` laid out as the ABI requires, every execution
returns to the caller after finitely many steps with

- result `∈ {0, 10, 20}` (`rax` / `X0`);
- `20 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`;
- `10 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α`;
- callee-saved registers (`rbx, rbp, r12..r15` / `X19..X29`) and the stack pointer restored;
- input bytes unchanged (read-only), workspace and stack frame restored, `R` untouched.

Non-vacuity: [`x64_unsat_nonvacuous`](LeanQbe/T/Amd64/KissatPlain.lean#L179),
[`x64_sat_nonvacuous`](LeanQbe/T/Amd64/KissatPlain.lean#L204) and their AArch64 counterparts
[`arm64_unsat_nonvacuous`](LeanQbe/T/Arm64/KissatPlain.lean#L176),
[`arm64_sat_nonvacuous`](LeanQbe/T/Arm64/KissatPlain.lean#L203) run the machine code on concrete
inputs (`p cnf 1 2 / 1 0 / -1 0` returns 20, `p cnf 1 1 / 1 0` returns 10). Source level:
[`plain_solve_bytes_correct`](LeanQbe/T/Examples/Kissat/PlainLemmas.lean#L1331),
[`plainEnv_moduleOk`](LeanQbe/T/Examples/Kissat/PlainLemmas.lean#L1325).

#### `D-Full`: UNSAT soundness, end to end

[`full_solve_bytes_unsat_x64`](LeanQbe/T/Amd64/KissatFull.lean#L45) /
[`full_solve_bytes_unsat_arm64`](LeanQbe/T/Arm64/KissatFull.lean#L46) give the same guarantees
for the 166-function solver except the `10 → SAT` clause, against the UNSAT-only contract
[`fullSolveBytesSpec`](LeanQbe/T/Examples/Kissat/FullSpec.lean#L57), backed unconditionally by
[`fullEnv_moduleOk`](LeanQbe/T/Examples/Kissat/FullProof.lean#L839) (all 166 functions proved).
Model reconstruction after inprocessing is intentionally not verified, so `10` from `D-Full` is
not a certified answer. [`full_unsat_nonvacuous_x64`](LeanQbe/T/Amd64/KissatFull.lean#L160) /
[`full_unsat_nonvacuous_arm64`](LeanQbe/T/Arm64/KissatFull.lean#L160) exhibit a concrete call on
which the machine code returns 20.

- **M2 fast-path components:** [`FullFastSchedLemmas`](LeanQbe/T/Examples/Kissat/FullFastSchedLemmas.lean)
  + [`KissatFastSched`](LeanQbe/T/Amd64/KissatFastSched.lean), [`FullFastBveBudgetsLemmas`](LeanQbe/T/Examples/Kissat/FullFastBveBudgetsLemmas.lean),
  [`FullFastCoreLemmas`](LeanQbe/T/Examples/Kissat/FullFastCoreLemmas.lean), [`FullBvaHeapLemmas`](LeanQbe/T/Examples/Kissat/FullBvaHeapLemmas.lean),
  and [`FullKittenLemmas`](LeanQbe/T/Examples/Kissat/FullKittenLemmas.lean) stage M2 slices (`KissatAudit{Spec,X64,Arm64}.lean`).

#### Axioms

Every audited theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. The
repository contains no `sorry`, no `axiom`, and no `native_decide` / `bv_decide` /
`ofReduceBool`; `scripts/check.sh` enforces this.

### Kissat: trusted computing base

To believe that the `kissat-leanqbe` binary only prints `s UNSATISFIABLE` for unsatisfiable
inputs (and, for `D-Plain`, `s SATISFIABLE` only for satisfiable ones) you must trust:

1. **The specification:** `Std.Sat.CNF.Unsat` / `Std.Sat.CNF.Sat` from the Lean standard library
   and [`parseDimacs`](LeanQbe/T/Examples/LratBytes.lean#L149), a ~50-line pure DIMACS parser
   (checked on examples in `KissatAuditSpec.lean`).
2. **The Lean kernel** and the three standard axioms above.
3. **The Kraken ISA semantics** for x86-64 / AArch64 (the model the machine-code theorems are
   stated in) and the assembler/linker that turn the printed directives (`Kraken.X64.PrintATT`,
   `Kraken.AArch64.Print`) into an executable.
4. **The harness:** [`kissat_cli.c`](bench/kissat/kissat_cli.c) (~100 lines: reads the file,
   maps it read-only between guard pages, calls `kissat_solve_bytes`, prints the answer) and
   the C runtime it links against. Its call must meet the theorems' preconditions (ABI, memory
   disjointness), which the guard-page layout provides.

Not trusted: the C0 sources of both solvers, the C0 elaborator, every `LeanQbe.T` compiler pass
(optimization, legalization, register allocation, instruction selection, linking), and all
`Func.wp` proofs — all are checked by the kernel.

**File-organization & verification policy.** Modules follow conceptual boundaries (`~1k–3k` LOC
typical, shorter fine) bounded by per-file resource caps (`≤ 120s` / `≤ 300s` `*Cert*`,
`≤ 2.5 GiB` RSS, default `200k` heartbeats, `≤ 100` cols) rather than rigid line limits.
Source-level `Func.wp`/`ModuleOk` verification and differential testing run independently of
native `LinkedCert` (`*Cert*`) kernel compilation proofs.

## Repository layout

| Path | Contents |
|---|---|
| `LeanQbe/T/` | IR, program logic, compiler passes and their proofs (architecture-independent) |
| `LeanQbe/T/Examples/Kissat/` | C0 sources, specs and `Func.wp` proofs of the Kissat solvers |
| `LeanQbe/T/Amd64/`, `LeanQbe/T/Arm64/` | target instances, compilation certificates, end-to-end theorems |
| `LeanQbeTest/T/` | tests and audit files (each module imports at most one architecture) |
| `bench/kissat/` | solver CLI, build script, CNF generators, differential test suites |
| `scripts/check.sh` | quality gate |
| `docs/reports/` | design notes per component |
