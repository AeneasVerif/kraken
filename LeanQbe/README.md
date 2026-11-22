# lean-qbe: the verified `LeanQbe.T` compiler and verified workloads

`LeanQbe.T` is a typed SSA intermediate language with a weakest-precondition program logic
(`Func.wp`) and an optimizing compiler to x86-64 (SysV) and AArch64 (AAPCS64), written and
verified in Lean 4 (`leanprover/lean4:nightly-2026-11-08`). Programs are written in **C0**, a
small C subset elaborated into `LeanQbe.T` by a Lean macro. The compiler produces a
kernel-checked certificate (`LinkedCert`) relating every source function's `Func.wp` spec to
its machine code under the Kraken x86-64 / AArch64 instruction semantics.

## Verified workstreams and theorem-auditing index

Each workstream has audit files under `LeanQbeTest/T/` (or `LeanQbeBootstrap0Test/`) that restate
its headline theorems with full, unabbreviated types, explain every hypothesis and TCB assumption,
and end with one-line `#print axioms` reports (standard axioms `[propext, Classical.choice,
Quot.sound]` only). Architecture-specific audits are split so that no module imports both
`Kraken.X64` and `Kraken.AArch64`.

| # | Workstream | What is audited | Audit files |
|---|---|---|---|
| 1 | **Verified Kissat SAT solver** (`D-Plain`, `D-Full M3`, `D-Full M4` source-only; legacy `D-Full` / `M2 Fast`) | DIMACS spec; `D-Plain` SAT+UNSAT and `M3` UNSAT machine soundness & closed NV ([details](#verified-kissat)) | [Spec](LeanQbeTest/T/KissatAuditSpec.lean), [X64](LeanQbeTest/T/KissatAuditX64.lean), [Arm64](LeanQbeTest/T/KissatAuditArm64.lean), [LegacyX64](LeanQbeLegacyTest/KissatLegacyAuditX64.lean), [LegacyArm64](LeanQbeLegacyTest/KissatLegacyAuditArm64.lean) |
| 2 | **Verified compiler, linker, `LinkRec` and `LinkScc`/`LinkLfp`** | IR passes (`Func.licm` in `Func.lateCfg`, `Fold` cmp/ext narrowing), isel (`IselStepAttr`/`IselStepRules`), `FlagRaOpt`, `Spill`, `[base + disp]` (`Hints.elide` / `DefFact.addImm64`), `LinkedCert`, cyclic & SCC-DAG | [Spec](LeanQbeTest/T/CompilerAuditSpec.lean), [X64](LeanQbeTest/T/CompilerAuditX64.lean), [Arm64](LeanQbeTest/T/CompilerAuditArm64.lean) |
| 3 | **Impure Lean 4 `LCNF` and `LeanLRC` lowering** | Structural `Fn.Wf` of `LeanQbe/T/LeanLCNF` and `LeanQbe/T/LeanLRC` lowering into `LeanQbe.T` | [Audit](LeanQbeTest/T/LcnfAudit.lean) |
| 4 | **Verified native LRAT proof checker** (`LratBytes`) | `lrat_check_bytes` returns `1` only for valid DIMACS of an unsatisfiable CNF | [Spec](LeanQbeTest/T/LratAuditSpec.lean), [X64](LeanQbeTest/T/LratAuditX64.lean), [Arm64](LeanQbeTest/T/LratAuditArm64.lean) |
| 5 | **Cryptographic and data-structure workloads** (`ChaCha20` SIMD, 256-bit `Bignum`, `UnionFind`) | Functional correctness of the example programs and their compiled machine code | [Spec](LeanQbeTest/T/WorkloadsAuditSpec.lean), [X64](LeanQbeTest/T/WorkloadsAuditX64.lean), [Arm64](LeanQbeTest/T/WorkloadsAuditArm64.lean) |
| 6 | **C0 frontend & separation-logic proof tooling** | `Func.wp` core rules, C0 elaborator/`Wf`, `C0HeadStep`/`C0Agrees`, `SepTree`/`SlabChain`/`C0Lens`, `ControlComb` & deduplicated `LegalEmit` | [Audit](LeanQbeTest/T/C0LogicAudit.lean) |
| 7 | **Bootstrapping (`LeanQbeBootstrap0` Stage A & `PrintAsm0`)** | Stage-A `leanqbe0Mod0` (`124` fns) structural WF/acyclicity/sig + `leanqbe0Cert` IR→x64 compilation cert; `PrintAsm0` equivalence ([details](#bootstrapping-leanqbebootstrap0-stage-a--printasm0)) | [Bootstrap0Audit](LeanQbeBootstrap0Test/Bootstrap0Audit.lean), [PrintAsm0Test](LeanQbeTest/T/PrintAsm0Test.lean) |

Check all active audit files (also built by `scripts/check.sh`):

```bash
lake build --wfail LeanQbeTest.T.KissatAuditSpec LeanQbeTest.T.KissatAuditX64 \
  LeanQbeTest.T.KissatAuditArm64 LeanQbeTest.T.CompilerAuditSpec LeanQbeTest.T.CompilerAuditX64 \
  LeanQbeTest.T.CompilerAuditArm64 LeanQbeTest.T.LcnfAudit LeanQbeTest.T.LratAuditSpec \
  LeanQbeTest.T.LratAuditX64 LeanQbeTest.T.LratAuditArm64 LeanQbeTest.T.WorkloadsAuditSpec \
  LeanQbeTest.T.WorkloadsAuditX64 LeanQbeTest.T.WorkloadsAuditArm64 LeanQbeTest.T.C0LogicAudit \
  LeanQbeTest.T.PrintAsm0Test LeanQbeBootstrap0Test.Bootstrap0Audit
```

## Verified Kissat

**Verified Kissat** is a port of the Kissat SAT solver to C0 with end-to-end machine-code
correctness theorems:

| Solver | Lean module | Functions | Status | Proved |
|---|---|---|---|---|
| `D-Plain` | `LeanQbe.T.Examples.Kissat.Plain` | 59 | Active | **SAT and UNSAT**, x86-64 and AArch64, unconditional (`KissatAudit{Spec,X64,Arm64}`) |
| `D-Full M3` | `LeanQbe.T.Examples.Kissat.FullM3` | 204 | Active | **UNSAT soundness + closed UNSAT NV**, x86-64 and AArch64, unconditional (`KissatAudit{Spec,X64,Arm64}`) |
| `D-Full M4` | `LeanQbe.T.Examples.Kissat.FullM4` | 231 | Active (source-only) | **UNSAT soundness + UNSAT NV**, source level (`231/231` `ModuleOk` + `Mem 64` NV in `KissatAuditSpec`); no native `LinkedCert` yet |
| `D-Full` | `LeanQbe.T.Examples.Kissat.Full` | 166 | Retired legacy | **UNSAT soundness + UNSAT NV**, x86-64 and AArch64 (`LeanQbeLegacyTest/KissatLegacyAudit*`, `INCLUDE_LEGACY=1`) |
| `D-Full M2 Fast` | `LeanQbe.T.Examples.Kissat.FullFast` | 196 | Retired legacy | **UNSAT soundness + UNSAT NV**, x86-64 and AArch64 (`LeanQbeLegacyTest/KissatLegacyAudit*`, `INCLUDE_LEGACY=1`) |

(The superseded `FullFastSched` module has `16/173` rows proved in `KissatAuditSpec.lean` and an
undischarged `ModuleOk` hypothesis in `LeanQbeLegacyTest/`; it was superseded by `FullFast` and
`FullM3`.)

All five solvers export one C entry point:

```c
uint64_t kissat_solve_bytes(const uint8_t *cnf_ptr, uint64_t cnf_len,
                            uint8_t *work_ptr, uint64_t work_len, uint64_t fuel);
/* 20 = UNSAT, 0 = unknown; 10 = SAT (certified on D-Plain only; uncertified on UNSAT-only solvers) */
```

### Kissat: build and run

Prerequisites: `elan` (picks up `lean-toolchain`), a C compiler, and for AArch64 on an x86-64
host `aarch64-linux-gnu-gcc` and `qemu-aarch64`.

```bash
# Default certified UNSAT-only binary: D-Full M3, x86-64, exact certified inline=0 IR,
# and kissat_cli.c compiled with -DKISSAT_UNSAT_ONLY=1 (r == 10 prints "s UNKNOWN", exit 0).
bash bench/kissat/build_solver.sh --module FullM3 --arch x64 -o /tmp/kissat-leanqbe-fullm3
/tmp/kissat-leanqbe-fullm3 [--work-mb <MB>] [--fuel <N>] <input.cnf | ->
printf 'p cnf 1 2\n1 0\n-1 0\n' | /tmp/kissat-leanqbe-fullm3 -      # s UNSATISFIABLE, exit 20

# D-Plain SAT+UNSAT binary, AArch64 (runs under qemu-aarch64 on x86-64 hosts).
# Plain compiles without -DKISSAT_UNSAT_ONLY=1, so r == 10 prints "s SATISFIABLE" (exit 10).
bash bench/kissat/build_solver.sh --module Plain --arch arm64 -o /tmp/kissat-leanqbe-plain-arm64
qemu-aarch64 -L /usr/aarch64-linux-gnu /tmp/kissat-leanqbe-plain-arm64 input.cnf

# Uncertified variants require explicit flags / warn on stderr:
#   --inline-max <N> (N > 0) or --debug rewrites IR/directives outside LinkedCert.
#   --module FullM4 has no native LinkedCert yet and requires --allow-uncertified.

# Differential test suites (x86-64 + AArch64 + C++ ASan/UBSan, optional reference Kissat).
bash test/kissat/run.sh
bash bench/kissat/run_full.sh --module Full
bash bench/kissat/run_plain.sh

# Proofs: build the audit files, then run the quality gate.
lake build --wfail LeanQbeTest.T.KissatAuditSpec LeanQbeTest.T.KissatAuditX64 \
  LeanQbeTest.T.KissatAuditArm64
scripts/check.sh
```

[`scripts/check.sh`](scripts/check.sh) builds active targets (plus `LeanQbeBootstrap0` and
`LeanQbeBootstrap0Test` in `full` and `x64` scopes) with warnings as errors, scans all tracked
`.lean` files for `sorry`, `admit`, non-meta `axiom `, `@[implemented_by]`, `@[extern]`,
`trustCompiler`, and native-code tactics (`native_decide`, `bv_decide`, `ofReduceBool`, …), checks
architecture and active-vs-legacy import closures, and audits the axioms of every `#print axioms`
in the build plus the headline theorems listed in [`scripts/headlines.d/*.txt`](scripts/headlines.d).
Run `INCLUDE_LEGACY=1 ./scripts/check.sh` or [`scripts/tier3_check.sh`](scripts/tier3_check.sh) to
also build and audit the retired `LeanQbeLegacy*` targets.

### Kissat: what is proved

Start with the three active audit files (and `LeanQbeLegacyTest/KissatLegacyAudit*.lean` for
retired `D-Full` and `M2 Fast`). They restate every headline theorem with its full type (no wrapper
definitions) and explain each hypothesis:

- [`KissatAuditSpec.lean`](LeanQbeTest/T/KissatAuditSpec.lean): the trusted specification
  (`CNF.Unsat`, `CNF.Sat`, `parseDimacs`) with executable checks, and source-level contracts for
  `D-Plain`, `D-Full`, `M2 Fast`, `M3`, `M4`, and partial `FullFastSched`.
- [`KissatAuditX64.lean`](LeanQbeTest/T/KissatAuditX64.lean): the active x86-64 machine-code
  theorems (`D-Plain` and `D-Full M3`, including closed concrete-host non-vacuity
  `audit_m3_x64_nv_closed`).
- [`KissatAuditArm64.lean`](LeanQbeTest/T/KissatAuditArm64.lean): the AArch64 mirror (including
  closed concrete-host non-vacuity `audit_m3_arm_nv_closed`).
- [`KissatLegacyAuditX64.lean`](LeanQbeLegacyTest/KissatLegacyAuditX64.lean) and
  [`KissatLegacyAuditArm64.lean`](LeanQbeLegacyTest/KissatLegacyAuditArm64.lean): retired
  machine-code theorems for `D-Full` (`166` fns) and `D-Full M2 Fast` (`196` fns).

#### `D-Plain`: SAT and UNSAT, end to end

[`solve_x64_correct`](LeanQbe/T/Amd64/KissatPlain.lean#L66) and
[`solve_arm64_correct`](LeanQbe/T/Arm64/KissatPlain.lean#L66): for **any** executable that
contains the compiled 59-function `inline=0` module, and any call with the input bytes, a
workspace, a stack frame and an arbitrary caller frame `R` laid out as the ABI requires, every
execution returns to the caller after finitely many steps with

- result `∈ {0, 10, 20}` (`rax` / `X0`);
- `20 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`;
- `10 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α`;
- callee-saved registers (`rbx, rbp, r12..r15` / `X19..X29`) and the stack pointer restored;
- input bytes unchanged (read-only), workspace and stack frame restored, `R` untouched.

Non-vacuity: [`x64_unsat_nonvacuous`](LeanQbe/T/Amd64/KissatPlain.lean#L181),
[`x64_sat_nonvacuous`](LeanQbe/T/Amd64/KissatPlain.lean#L206) and their AArch64 counterparts
[`arm64_unsat_nonvacuous`](LeanQbe/T/Arm64/KissatPlain.lean#L178),
[`arm64_sat_nonvacuous`](LeanQbe/T/Arm64/KissatPlain.lean#L205) run the machine code on concrete
inputs (`p cnf 1 2 / 1 0 / -1 0` returns 20, `p cnf 1 1 / 1 0` returns 10). Source level:
[`plain_solve_bytes_correct`](LeanQbe/T/Examples/Kissat/PlainLemmas.lean#L1329),
[`plainEnv_moduleOk`](LeanQbe/T/Examples/Kissat/PlainLemmas.lean#L1323).

#### `D-Full M3` (and retired `D-Full` / `M2 Fast` / source-only `D-Full M4`): UNSAT soundness

Model reconstruction after inprocessing is intentionally not verified, so `10` from any `D-Full`
variant is not a certified answer; [`kissat_cli.c`](bench/kissat/kissat_cli.c) is compiled with
`-DKISSAT_UNSAT_ONLY=1` for all modules except `Plain`, mapping `r == 10` to `"s UNKNOWN"` and exit
`0`.

- **`D-Full M3` (204 functions, active flagship):**
  [`FullM3Proof.m3Env_moduleOk`](LeanQbe/T/Examples/Kissat/FullM3Proof.lean) combines M3a
  (`FullM3VivChrono`), M3b (`FullM3CongBva`), and M3c (`FullM3Backbone`), lifted unconditionally to
  x86-64 ([`Amd64/KissatM3.lean`](LeanQbe/T/Amd64/KissatM3.lean)) and AArch64
  ([`Arm64/KissatM3.lean`](LeanQbe/T/Arm64/KissatM3.lean)), with closed concrete-host UNSAT
  non-vacuity audited in `KissatAudit{X64,Arm64}.lean` (`audit_m3_{x64,arm}_nv_closed`).
- **`D-Full M4` (231 functions, active source level only):**
  [`FullM4Proof.m4Env_moduleOk`](LeanQbe/T/Examples/Kissat/FullM4Proof.lean) unifies M4a–M4g with
  [`m4_solve_bytes_correct`](LeanQbe/T/Examples/Kissat/FullM4Proof1.lean) and
  [`m4_unsat_nonvacuous`](LeanQbe/T/Examples/Kissat/FullM4Proof1.lean) (`KissatAuditSpec.lean`);
  native `LinkedCert` is not yet built.
- **Retired `D-Full` (166 fns) and `D-Full M2 Fast` (196 fns):**
  Unconditional UNSAT machine-code proofs and non-vacuity live in
  [`LeanQbeLegacyTest/KissatLegacyAuditX64.lean`](LeanQbeLegacyTest/KissatLegacyAuditX64.lean) and
  [`LeanQbeLegacyTest/KissatLegacyAuditArm64.lean`](LeanQbeLegacyTest/KissatLegacyAuditArm64.lean).

#### Axioms

Every audited theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. The
repository contains no `sorry`, no `admit`, no non-meta `axiom`, no `@[implemented_by]`/`@[extern]`,
and no `native_decide` / `bv_decide` / `ofReduceBool`; [`scripts/check.sh`](scripts/check.sh)
enforces this across all tracked `.lean` files.

### Kissat: trusted computing base

To believe that a default-built `kissat-leanqbe` binary (`--inline-max 0`, without `--debug`) only
prints `s UNSATISFIABLE` for unsatisfiable inputs (and, for `D-Plain`, `s SATISFIABLE` only for
satisfiable ones) you must trust:

1. **The specification:** `Std.Sat.CNF.Unsat` / `Std.Sat.CNF.Sat` from the Lean standard library
   and [`parseDimacs`](LeanQbe/T/Examples/LratBytes.lean#L150), a pure ASCII DIMACS parser
   (checked on examples in `KissatAuditSpec.lean`). `parseDimacs` is overflow-safe (rejects
   headers/variable IDs `>= 2^28 = 268,435,456` via `dimacsBound`) and `-0`-safe (rejects `-0`),
   and rejects missing headers, out-of-range variables, truncated clauses, and trailing tokens;
   its exact dialect rules are:
   - lowercase `'c'` skips through `'\n'` at any whitespace-delimited boundary (not only
     start-of-line; uppercase `'C'` and `'c'` attached to digits like `12c` are rejected);
   - leading zeros are accepted (`00` terminates a clause, `01` parses as variable `1`);
   - an empty clause (`0`) inside `nc` yields an `Unsat` CNF (`p cnf 0 0` yields `CNF.empty`);
   - SATLIB `%` end-of-file trailers are rejected (`none`).
2. **The Lean kernel** and the three standard axioms above.
3. **The Kraken ISA semantics** for x86-64 / AArch64 (the model the machine-code theorems are
   stated in) and the assembler/linker that turn the printed directives (`Kraken.X64.PrintATT`,
   `Kraken.AArch64.Print`) into an executable.
4. **The harness:** [`kissat_cli.c`](bench/kissat/kissat_cli.c) (reads input, checks
   `RLIMIT_STACK >= 65536` B, maps input read-only and workspace read-write between `PROT_NONE`
   guard pages, calls `kissat_solve_bytes`, and under `-DKISSAT_UNSAT_ONLY=1` maps uncertified `10`
   to `s UNKNOWN` / exit `0`) and the C runtime it links against.

Not trusted: the C0 sources of both solvers, the C0 elaborator, every `LeanQbe.T` compiler pass
(optimization, legalization, register allocation, instruction selection, linking), and all
`Func.wp` proofs — all are checked by the kernel. (Note: `--inline-max > 0`, `--debug` via
`DebugAsm`, and `--module FullM4` with `--allow-uncertified` operate outside `LinkedCert`.)

## Bootstrapping (`LeanQbeBootstrap0` Stage A & `PrintAsm0`)

`LeanQbeBootstrap0` implements a minimal monomorphic scalar compiler (`leanqbe0Compile` in
[`LeanQbe/T/Bootstrap0/Compiler0.lean`](LeanQbe/T/Bootstrap0/Compiler0.lean)) and records Stage-A
artifacts audited in [`LeanQbeBootstrap0Test/Bootstrap0Audit.lean`](LeanQbeBootstrap0Test/Bootstrap0Audit.lean):

- **What is certified today (Stage A):**
  - [`leanqbe0Mod0`](LeanQbe/T/Bootstrap0/Mod0.lean) (`124`-function `LeanQbe.T.Module` lowered
    from `leanqbe0Compile` via `LeanLCNF`) satisfies kernel-checked `Fn.Wf` (`leanqbe0Mod0_wf`),
    strict acyclicity (`leanqbe0Mod0_acyclic`), and `x64LegalTarget` signature legality
    (`leanqbe0Mod0_legalSig`).
  - [`leanqbe0Cert`](LeanQbe/T/Bootstrap0/Cert.lean) is a kernel-checked `LinkedCert` compiling
    all `124` functions of `leanqbe0Mod0` to SysV x86-64 directives with stack bounds `≤ 2048` B,
    parameterized by assumed `rtExtBounds0` (`64` per `rtExterns` C runtime entry) and exit
    symbol `["lcnf_panic"]` (`nX = 64`).
  - [`PrintAsm0Lemmas`](LeanQbe/T/Amd64/PrintAsm0Lemmas.lean) (audited in
    [`PrintAsm0Test.lean`](LeanQbeTest/T/PrintAsm0Test.lean)) proves bit-for-bit equality between
    the minimal Stage-B AT&T printer (`printModule0` / `printAmd64Asm0`) and
    `Driver.emitAsm` / `Kraken.X64.toATT` on `DirSubset0`.
- **What remains in the TCB / active Stage B work (not yet proved):**
  - No `ModuleOk`, `FnSpec`, or `Eventually` theorem for `leanqbe0Mod0` (C runtime behavior in
    `lcnf_rt.c` and `rtExtBounds0 = 64` / `nX = 64` are assumed, not specified/discharged).
  - `LeanLCNF` meta extraction (`lcnf_of_lean!` / `splice_lcnf_tflat!`) proves `Fn.Wf`, not
    semantic equivalence to Lean's `leanqbe0Compile`.
  - `leanqbe0Compile` (`Compiler0.lean`) does not yet have a `Sound0` compiler-correctness theorem;
    `Bridge0` and `Codec0` are unverified; `PrintAsm0` / `PrintDir0` are not yet wired end-to-end
    into `leanqbe0`; and a native binary self-compile fixpoint has not yet been executed or proved.

**File-organization & verification policy.** Modules follow conceptual boundaries (`~1k–3k` LOC
typical, shorter fine) bounded by per-file resource caps (`≤ 120s` / `≤ 300s` `*Cert*`,
`≤ 2.5 GiB` RSS, default `200k` heartbeats, `≤ 100` cols) rather than rigid line limits.
Source-level `Func.wp`/`ModuleOk` verification and differential testing run independently of
native `LinkedCert` (`*Cert*`) kernel compilation proofs.

## Repository layout

| Path | Contents |
|---|---|
| `LeanQbe/T/` | IR, program logic, compiler passes and their proofs (architecture-independent) |
| `LeanQbe/T/Bootstrap0/` | Stage-A monomorphic `leanqbe0Compile`, lowered `leanqbe0Mod0`, and x64 `leanqbe0Cert` |
| `LeanQbe/T/Examples/Kissat/` | C0 sources, specs and `Func.wp` proofs of the Kissat solvers |
| `LeanQbe/T/Amd64/`, `LeanQbe/T/Arm64/` | target instances, active compilation certificates, end-to-end theorems |
| `LeanQbeTest/T/`, `LeanQbeBootstrap0Test/` | tests and active audit files (each module imports at most one architecture) |
| `LeanQbeLegacyTest/` | retired `D-Full` and `D-Full M2 Fast` machine-code audits (`INCLUDE_LEGACY=1`) |
| `bench/kissat/` | solver CLI (`kissat_cli.c`), build script, CNF generators, differential test suites |
| `scripts/check.sh`, `scripts/headlines.d/` | quality gate and headline axiom registries |
| `docs/reports/` | design notes per component (older E1-era notes carry a historical banner) |
