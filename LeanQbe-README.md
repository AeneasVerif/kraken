# LeanQbe.T

**LeanQbe.T** is a formally verified compiler written in Lean 4. It lowers typed Static Single
Assignment (SSA) intermediate representations—along with C0, Lean `LCNF`, Lean `λRC`, WebAssembly,
and Bedrock2 frontends—to native SysV x86-64 and AAPCS64 AArch64 machine code (as well as QBE IL
and C++20), with end-to-end semantic correctness proved inside Lean's kernel.

Machine-code correctness proofs compose through **Kraken** ([README.md](README.md)), formalizing the
x86-64 (`Kraken.X64`) and AArch64 (`Kraken.AArch64`) instruction-set architectures in separation
logic. All active theorems depend only on Lean 4's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`), without `sorry` or custom trust axioms.

### Highlights

- **Verified Optimizing Compiler:** Typed SSA passes (`fold`, `canon`, `copy`, `gvn`, `ifOpt`, loop
  peeling, `licm`, loop rotation, conditional threading, tail duplication, address-range and
  dead-load elimination), legalization, register spilling, graph-coloring register allocation, and
  instruction selection targeting SysV x86-64 (scalar + AVX2/AVX-512) and AAPCS64 AArch64.
- **Unified Multi-Frontend / Multi-Backend Layering:**
  - [Unified pipeline](LeanQbe/T/Unified/Driver.lean) sharing mid-end optimization (`midEnd`) and
    register allocation (`regaBackend`) across C0, Lean `LCNF`, and `Kraken.Bedrock2`, together with
    witness-checked CFG recovery and contification over structured `BedrockWord` programs and
    cross-calling `Xcap` contracts.
  - [Direct flat-IR optimizer (`MainFlat`)](LeanQbe/T/MainFlat.lean) proved equivalent to the PHOAS
    pipeline (`compileFlatFn_eq_compileFn`).
- **Frontends & Standalone Runtime:**
  - Extended C0 compiler supporting `#include` headers, function-like and variadic `#define` macros,
    `offsetof`, `_Static_assert`, provenance checks, and SysV LP64 bitfield layout.
  - Lean `LCNF` compiler paired with a standalone 86-function pure-C0 runtime
    ([LcnfC0Full.lean](LeanQbe/T/LeanLCNF/LcnfC0Full.lean)) covering 35 of 38 runtime calls (leaving
    only three floating-point helpers external), with verified SysV x86-64
    ([LcnfC0FullCertX64.lean](LeanQbe/T/Amd64/LcnfC0FullCertX64.lean)) and AAPCS64 AArch64
    ([LcnfC0FullCertArm64.lean](LeanQbe/T/Arm64/LcnfC0FullCertArm64.lean)) `LinkedCert`s
    (`≤ 272 B` stack bound) and closed concrete machine execution witnesses on both architectures,
    alongside a Lean `λRC` frontend (`LeanLRC`).
  - Universal Software Fault Isolation (SFI) safety proofs for validated WebAssembly modules
    (including bulk memory operations) and mutual/cyclic recursion linking.
- **Verified Systems Programs & Kissat SAT Solver:**
  - RFC 8439 ChaCha20 block cipher (row-SIMD `v4i32`), Curve25519 constant-time bignum kernels,
    disjoint-set Union-Find, and an untrusted-bytes DIMACS + binary LRAT UNSAT proof checker
    (`lrat_check_bytes`).
  - Verified C0 port of the **Kissat 4.0.4** SAT solver with full Conflict-Driven Clause Learning
    (CDCL) and inprocessing: source/IR UNSAT soundness, fail-closed compile guards, and
    parameterized machine-code proofs across all `504` functions on both SysV x86-64
    (`≤ 1,560 B` stack bound) and AAPCS64 AArch64 (`≤ 1,392 B` stack bound), materialized
    machine-code certificates and 140-CNF benchmarks on a `413`-function certified baseline, and
    a `59`-function minimal CDCL solver (`KissatPlain`) with dual SAT and UNSAT machine-code
    soundness.
- **Stage-0 Bootstrapping Workstream:** Lowered 124-function Stage-0 compiler module certified to
  compile to `17,150` SysV x86-64 directives within a 2048-byte stack budget, paired with separate
  semantic soundness checks on guarded scalar programs, binary codec round-trips, and printer
  parity.

---

## Where to Start

- **Audit specifications ([LeanQbeTest/T/](LeanQbeTest/T/)):** Self-contained files restating
  top-level specifications, trusted computing bases (TCB), and concrete non-vacuity witnesses for
  the [compiler core](LeanQbeTest/T/CompilerAuditSpec.lean),
  [x86-64 backend](LeanQbeTest/T/CompilerAuditX64.lean),
  [AArch64 backend](LeanQbeTest/T/CompilerAuditArm64.lean),
  [workloads](LeanQbeTest/T/WorkloadsAuditSpec.lean),
  [LRAT proof checker](LeanQbeTest/T/LratAuditX64.lean),
  [WebAssembly sandbox](LeanQbeTest/T/WasmAuditSpec.lean),
  [C0 logic](LeanQbeTest/T/C0LogicAudit.lean), and
  [Kissat solver](LeanQbeTest/T/KissatFidelityAuditSpec.lean).
- **Quality gate & fast preflight:** Run [scripts/preflight.sh](scripts/preflight.sh) for fast
  diff, firewall, hub-sync, and hygiene checks, or [scripts/check.sh](scripts/check.sh) for the full
  build, axiom audit, headline manifest verification, and native test sweep.
- **CLI drivers:**
  ```bash
  timeout 600 lake build leanqbe leanqbe-arm64
  .lake/build/bin/leanqbe --list
  .lake/build/bin/leanqbe uf_bench > /tmp/uf.s
  .lake/build/bin/leanqbe --il uf_bench > /tmp/uf.ssa
  .lake/build/bin/leanqbe-arm64 uf_bench > /tmp/uf_arm64.s
  ```
- **Differential & native test suites:** [test/run.sh](test/run.sh),
  [test/arm64/run.sh](test/arm64/run.sh), [test/c0/run.sh](test/c0/run.sh),
  [test/lcnf/run.sh](test/lcnf/run.sh), [test/t_bignum/run.sh](test/t_bignum/run.sh),
  [test/t_chacha/run.sh](test/t_chacha/run.sh), [test/t_lrat/run.sh](test/t_lrat/run.sh), and
  [test/kissat/run.sh](test/kissat/run.sh).
- **Kissat native solver & 4-way benchmark tools:**
  [bench/kissat/build_solver.sh](bench/kissat/build_solver.sh),
  [bench/kissat/extract_c0_direct.py](bench/kissat/extract_c0_direct.py),
  [bench/kissat/run_4way_stage1.py](bench/kissat/run_4way_stage1.py), and the minimal
  4-way comparison script [bench/kissat/compare_4way_min.py](bench/kissat/compare_4way_min.py).

---

## Architecture Overview

1. **Typed SSA & Program Semantics (`IL.lean`, `Flat.lean`, `WP.lean`):**
   - Programs are represented in typed Parametric Higher-Order Abstract Syntax (PHOAS)
     (`Prog` / `Func` / `Fn` in [IL.lean](LeanQbe/T/IL.lean)) alongside a first-order de Bruijn /
     flat form ([Flat.lean](LeanQbe/T/Flat.lean)).
   - Semantics are defined by total-correctness weakest preconditions (`wp`, `Func.wp`, `ModuleOk`
     in [WP.lean](LeanQbe/T/WP.lean)) over 64-bit byte-addressed memory (`Mem 64`) and
     separation-logic assertions (`⋆`, `region`, `array`, `cell`), guaranteeing explicit
     postconditions for normal returns (`Post`), abnormal exits (`XPost`), and unmodified caller
     memory frames (`R`).
2. **Frontends & Structured Recovery (`Frontend/`, `LeanLCNF/`, `LeanLRC/`, `Wasm/`, `Bedrock2/`,
   `BedrockWord/`):**
   - **Extended C0 ([Frontend/C0.lean](LeanQbe/T/Frontend/C0.lean)):** Elaborates a structured C
     subset into typed SSA with `#include` (`c0_header!`), parameterized and variadic `#define`
     macros, `offsetof`, `_Static_assert`, provenance checks, and SysV LP64 struct/bitfield layout,
     backed by symbolic separation-logic stepping tactics ([C0Step](LeanQbe/T/Logic/C0Step.lean)).
   - **Lean `LCNF` & `λRC` ([LeanLCNF/Hub.lean](LeanQbe/T/LeanLCNF/Hub.lean),
     [LeanLRC/Hub.lean](LeanQbe/T/LeanLRC/Hub.lean)):** Compiles Lean's intermediate code to
     `LeanQbe.T`, with a standalone verified pure-C0 runtime
     ([LcnfC0Full.lean](LeanQbe/T/LeanLCNF/LcnfC0Full.lean)) combining base runtime helpers,
     multi-precision integers (`BigNum`), containers, and strings (`86` functions, `35 / 38`
     runtime calls covered, `ModuleOk` and `Mem 64` non-vacuity proved), together with verified
     SysV x86-64 ([LcnfC0FullCertX64.lean](LeanQbe/T/Amd64/LcnfC0FullCertX64.lean)) and AAPCS64
     AArch64 ([LcnfC0FullCertArm64.lean](LeanQbe/T/Arm64/LcnfC0FullCertArm64.lean)) `LinkedCert`s
     (`≤ 272 B` stack bound) and closed concrete execution witnesses on both architectures
     ([LcnfC0FullCertTest.lean](LeanQbeTest/T/LcnfC0FullCertTest.lean),
     [LcnfC0FullCertArm64Test.lean](LeanQbeTest/T/LcnfC0FullCertArm64Test.lean)).
   - **WebAssembly ([Wasm/Safety.lean](LeanQbe/T/Wasm/Safety.lean)):** Decodes, validates, and
     compiles Wasm modules—including bulk-memory operations—with proved SFI host-memory isolation
     across arbitrary call graphs (`ModuleSccOk`).
   - **Bedrock2 & Structured Words ([Bedrock2/ToT.lean](LeanQbe/T/Bedrock2/ToT.lean),
     [BedrockWord/Core.lean](LeanQbe/T/BedrockWord/Core.lean)):** Lowers Bedrock2 programs via
     structured ASTs and witness-checked CFG recovery and contification
     ([CfgRecovery.lean](LeanQbe/T/Unified/CfgRecovery.lean),
     [CfgContify.lean](LeanQbe/T/Unified/CfgContify.lean)).
3. **Unified Pipeline & External Interop (`Unified/`, `Xcap/`):**
   - [Unified/Core.lean](LeanQbe/T/Unified/Core.lean) and
     [Unified/Driver.lean](LeanQbe/T/Unified/Driver.lean) decouple frontends (C0, `LCNF`, `Bedrock2`)
     from backends through shared optimization (`midEnd`) and register allocation (`regaBackend`).
   - [Xcap/Bridge.lean](LeanQbe/T/Xcap/Bridge.lean) converts compiled `FnSpec` guarantees to and
     from Certified Assembly Programming (`Xcap.cptr`) code pointers, enabling verified cross-calls
     between `LeanQbe.T`-compiled functions and externally verified machine-code blocks.
4. **Target Abstraction, Cross-ISA Isolation, & Certificate Linking:**
   - [Target.lean](LeanQbe/T/Target.lean) encapsulates GPR/vector register classes, calling
     conventions, stack layout, instruction selection, and label hygiene behind abstract backend
     contracts (`GprTarget`, `VecTarget`, `FrameTarget`, `LegalTarget`, `LabelClean`).
   - Machine-independent libraries never import `Kraken.X64` or `Kraken.AArch64`, and
     [LeanQbeAmd64.lean](LeanQbeAmd64.lean) and [LeanQbeArm64.lean](LeanQbeArm64.lean) are strictly
     disjoint (enforced by [check_firewall.py](scripts/check_firewall.py)).
   - [MainCertCore.lean](LeanQbe/T/MainCertCore.lean) defines `LinkedCert` certificates verified
     inside Lean (`compile_linked!`, `compile_linked_chunks!`) and composed across modules, mutual
     recursion, and least fixed points ([MainLink.lean](LeanQbe/T/MainLink.lean),
     [LinkRec.lean](LeanQbe/T/LinkRec.lean), [LinkScc.lean](LeanQbe/T/LinkScc.lean),
     [LinkLfp.lean](LeanQbe/T/LinkLfp.lean)).

---

## Verified Components and Audit Files

Every major workstream has a self-contained audit module in [LeanQbeTest/T/](LeanQbeTest/T/) or
[LeanQbeBootstrap0Test/](LeanQbeBootstrap0Test/) exposing its exact theorem signatures and Trusted
Computing Base:

| Workstream | Core Specification / Proof | Audits & Tests (Core / x86-64 / AArch64) |
| :--- | :--- | :--- |
| **Compiler Core & Linking** | [Main.lean](LeanQbe/T/Main.lean), [MainCertCore.lean](LeanQbe/T/MainCertCore.lean), [LinkScc.lean](LeanQbe/T/LinkScc.lean), [LinkRec.lean](LeanQbe/T/LinkRec.lean) | [CompilerAuditSpec.lean](LeanQbeTest/T/CompilerAuditSpec.lean) / [CompilerAuditX64.lean](LeanQbeTest/T/CompilerAuditX64.lean) / [CompilerAuditArm64.lean](LeanQbeTest/T/CompilerAuditArm64.lean) |
| **Flat-IR Parity Pipeline** | [MainFlat.lean](LeanQbe/T/MainFlat.lean), [MainFlatLemmas.lean](LeanQbe/T/MainFlatLemmas.lean) | [MainFlatParityTest.lean](LeanQbeTest/T/MainFlatParityTest.lean) / [MainFlatParityArm64Test.lean](LeanQbeTest/T/MainFlatParityArm64Test.lean) |
| **Unified Pipeline & CFG Recovery** | [Unified/Driver.lean](LeanQbe/T/Unified/Driver.lean), [Unified/CfgRecoveryBridge.lean](LeanQbe/T/Unified/CfgRecoveryBridge.lean) | [UnifiedPipelineTest.lean](LeanQbeTest/T/UnifiedPipelineTest.lean), [UnifiedC0Test.lean](LeanQbeTest/T/UnifiedC0Test.lean), [UnifiedLcnfTest.lean](LeanQbeTest/T/UnifiedLcnfTest.lean), [UnifiedBedrock2X64Test.lean](LeanQbeTest/T/UnifiedBedrock2X64Test.lean), [UnifiedBedrock2Arm64Test.lean](LeanQbeTest/T/UnifiedBedrock2Arm64Test.lean), [BedrockCfgRecoveryTest.lean](LeanQbeTest/T/BedrockCfgRecoveryTest.lean) |
| **XCAP Interop Bridge** | [Xcap/Core.lean](LeanQbe/T/Xcap/Core.lean), [Xcap/Bridge.lean](LeanQbe/T/Xcap/Bridge.lean) | [XcapBridgeTest.lean](LeanQbeTest/T/XcapBridgeTest.lean) / [XcapBridgeX64Test.lean](LeanQbeTest/T/XcapBridgeX64Test.lean) / [XcapBridgeArm64Test.lean](LeanQbeTest/T/XcapBridgeArm64Test.lean) |
| **C0 Frontend & Logic** | [Frontend/C0.lean](LeanQbe/T/Frontend/C0.lean), [Logic/C0Step.lean](LeanQbe/T/Logic/C0Step.lean) | [C0LogicAudit.lean](LeanQbeTest/T/C0LogicAudit.lean), [C0ExtensionsTest.lean](LeanQbeTest/T/C0ExtensionsTest.lean) |
| **Lean `LCNF` & Standalone C0 Runtime** | [LeanLCNF/Hub.lean](LeanQbe/T/LeanLCNF/Hub.lean), [LcnfC0Full.lean](LeanQbe/T/LeanLCNF/LcnfC0Full.lean), [LcnfC0FullCertX64.lean](LeanQbe/T/Amd64/LcnfC0FullCertX64.lean), [LcnfC0FullCertArm64.lean](LeanQbe/T/Arm64/LcnfC0FullCertArm64.lean) | [LcnfAudit.lean](LeanQbeTest/T/LcnfAudit.lean), [LcnfC0FullTest.lean](LeanQbeTest/T/LcnfC0FullTest.lean) / [LcnfC0FullCertTest.lean](LeanQbeTest/T/LcnfC0FullCertTest.lean) / [LcnfC0FullCertArm64Test.lean](LeanQbeTest/T/LcnfC0FullCertArm64Test.lean) |
| **ChaCha20, Curve25519, UnionFind** | [ChaCha.lean](LeanQbe/T/Examples/ChaCha.lean), [Bignum.lean](LeanQbe/T/Examples/Bignum.lean), [UnionFind.lean](LeanQbe/T/Examples/UnionFind.lean) | [WorkloadsAuditSpec.lean](LeanQbeTest/T/WorkloadsAuditSpec.lean) / [WorkloadsAuditX64.lean](LeanQbeTest/T/WorkloadsAuditX64.lean) / [WorkloadsAuditArm64.lean](LeanQbeTest/T/WorkloadsAuditArm64.lean) |
| **LRAT Proof Checker (`lrat_check_bytes`)** | [LratBytes.lean](LeanQbe/T/Examples/LratBytes.lean), [LratBytesSpec.lean](LeanQbe/T/Examples/LratBytesSpec.lean) | [LratAuditSpec.lean](LeanQbeTest/T/LratAuditSpec.lean) / [LratAuditX64.lean](LeanQbeTest/T/LratAuditX64.lean) / [LratAuditArm64.lean](LeanQbeTest/T/LratAuditArm64.lean) |
| **WebAssembly Sandbox** | [Wasm/Safety.lean](LeanQbe/T/Wasm/Safety.lean), [Wasm/BulkSafety.lean](LeanQbe/T/Wasm/BulkSafety.lean) | [WasmAuditSpec.lean](LeanQbeTest/T/WasmAuditSpec.lean) / [WasmAuditX64.lean](LeanQbeTest/T/WasmAuditX64.lean) / [WasmAuditArm64.lean](LeanQbeTest/T/WasmAuditArm64.lean) |
| **Kissat SAT Solver (Full-Fidelity)** | [FidelityHub.lean](LeanQbe/T/Examples/Kissat/FidelityHub.lean), [FullFidelityBase.lean](LeanQbe/T/Examples/Kissat/FullFidelityBase.lean), [504-fn assembly](LeanQbe/T/Examples/Kissat/FullFidelityAssemblyStep9.lean) | [KissatFidelityStep9Test.lean](LeanQbeTest/T/KissatFidelityStep9Test.lean) / [KissatFidelityParamAuditX64.lean](LeanQbeTest/T/KissatFidelityParamAuditX64.lean) / [KissatFidelityParamAuditArm64.lean](LeanQbeTest/T/KissatFidelityParamAuditArm64.lean) |
| **Kissat SAT Solver (413-fn Certified Baseline)** | [413-fn assembly](LeanQbe/T/Examples/Kissat/FullM7FidelityAssembly.lean) | [Spec audit](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean) / [x86-64 audit](LeanQbeTest/T/KissatM7FidelityAuditX64.lean) / [AArch64 audit](LeanQbeTest/T/KissatM7FidelityAuditArm64.lean) |
| **Kissat Minimal CDCL (`KissatPlain`, Optional)** | [Plain.lean](LeanQbe/T/Examples/Kissat/Plain.lean) | [x86-64 audit](LeanQbeLegacyTest/KissatM3PlainLegacyAuditX64.lean) / [AArch64 audit](LeanQbeLegacyTest/KissatM3PlainLegacyAuditArm64.lean) |
| **Stage-0 Bootstrap (`LeanQbeBootstrap0`)** | [Bootstrap0/Mod0.lean](LeanQbe/T/Bootstrap0/Mod0.lean), [Bootstrap0/Cert.lean](LeanQbe/T/Bootstrap0/Cert.lean), [Bootstrap0/Sound0.lean](LeanQbe/T/Bootstrap0/Sound0.lean) | [Bootstrap0Audit.lean](LeanQbeBootstrap0Test/Bootstrap0Audit.lean), [Sound0Test.lean](LeanQbeBootstrap0Test/Sound0Test.lean), [Codec0Test.lean](LeanQbeBootstrap0Test/Codec0Test.lean), [PrintDir0Test.lean](LeanQbeBootstrap0Test/PrintDir0Test.lean), [StageCTest.lean](LeanQbeBootstrap0Test/StageCTest.lean) |

### Building, Auditing, and Testing

Run the main quality gate or build the active audit targets directly:

```bash
# Fast hygiene, firewall, hub-sync, and diff-whitespace check
timeout 60 bash scripts/preflight.sh

# Full build + Lean axiom/headline checks + native differential test suites
timeout 3600 bash scripts/check.sh

# Docs-only / incremental scoped gate (classifies README-only changes with zero rebuilds)
timeout 120 env CHECK_SCOPE=auto CHECK_BASE=HEAD~1 bash scripts/check.sh
```

To build and verify individual audit targets without running the entire sweep:

```bash
timeout 1800 lake build --wfail \
  LeanQbeTest.T.CompilerAuditSpec LeanQbeTest.T.CompilerAuditX64 LeanQbeTest.T.CompilerAuditArm64 \
  LeanQbeTest.T.WorkloadsAuditSpec LeanQbeTest.T.WorkloadsAuditX64 LeanQbeTest.T.WorkloadsAuditArm64 \
  LeanQbeTest.T.LratAuditSpec LeanQbeTest.T.LratAuditX64 LeanQbeTest.T.LratAuditArm64 \
  LeanQbeTest.T.WasmAuditSpec LeanQbeTest.T.WasmAuditX64 LeanQbeTest.T.WasmAuditArm64 \
  LeanQbeTest.T.C0LogicAudit LeanQbeTest.T.LcnfAudit LeanQbeTest.T.LcnfC0FullTest \
  LeanQbeTest.T.LcnfC0FullCertTest LeanQbeTest.T.LcnfC0FullCertArm64Test \
  LeanQbeTest.T.MainFlatParityTest LeanQbeTest.T.UnifiedPipelineTest \
  LeanQbeTest.T.XcapBridgeTest \
  LeanQbeTest.T.KissatFidelityStep9Test LeanQbeTest.T.KissatFidelityAuditSpec \
  LeanQbeTest.T.KissatFidelityParamAuditX64 LeanQbeTest.T.KissatFidelityParamAuditArm64 \
  LeanQbeTest.T.KissatFidelityCompileGuardX64 LeanQbeTest.T.KissatFidelityCompileGuardArm64 \
  LeanQbeTest.T.KissatM7FidelityAuditSpec \
  LeanQbeTest.T.KissatM7FidelityAuditX64 LeanQbeTest.T.KissatM7FidelityAuditArm64

# Optional: Stage-0 bootstrap audit and minimal SAT+UNSAT KissatPlain legacy audits
timeout 900 lake build --wfail LeanQbeBootstrap0Test
timeout 900 lake build --wfail LeanQbeLegacyTest.KissatM3PlainLegacyAuditX64 LeanQbeLegacyTest.KissatM3PlainLegacyAuditArm64
```

Native differential execution suites validate emitted x86-64 assembly, AArch64 assembly (under
`qemu-aarch64`), C++20 output (under `g++` and `clang++ -fsanitize=undefined,address`), and stock
QBE where applicable:

| Suite | Coverage |
| :--- | :--- |
| [test/run.sh](test/run.sh) | Core x86-64 scalar/litmus binaries, `PrintQbe` cross-compilation, and C0/LRC/Kissat integration |
| [test/arm64/run.sh](test/arm64/run.sh) | AAPCS64 AArch64 assembly vs. stock QBE under `qemu-aarch64` |
| [test/c0/run.sh](test/c0/run.sh) | Positive/negative C0 probes, SysV struct/bitfield layout, and host C differential tests |
| [test/lcnf/run.sh](test/lcnf/run.sh), [test/lcnf/run_c0rt.sh](test/lcnf/run_c0rt.sh) & [test/lrc/run.sh](test/lrc/run.sh) | `LeanLCNF` / `LeanLRC` reference Lean executables vs. C++20, x86-64, and AArch64 (including compiled `rtC0CoreMod` runtime lane) |
| [test/cpp/run.sh](test/cpp/run.sh) | C++20 standalone compilation and trap behavior under `g++` and `clang++` ASan/UBSan |
| [test/t_bignum/run.sh](test/t_bignum/run.sh), [test/t_chacha/run.sh](test/t_chacha/run.sh) | Differential x86-64 & AArch64 tests for Curve25519 arithmetic and RFC 8439 ChaCha20 |
| [test/t_lrat/run.sh](test/t_lrat/run.sh), [test/t_qbe/run.sh](test/t_qbe/run.sh) | C++20 ASan/UBSan tests for `lrat_check_bytes` and stock QBE IL emission |
| [test/kissat/run.sh](test/kissat/run.sh), [test/kissat/test_cli_solver.sh](test/kissat/test_cli_solver.sh) | Native Kissat solver verification against SAT witnesses and DRAT/LRAT UNSAT checks |
| [test/bootstrap0/run_stage_c_native.sh](test/bootstrap0/run_stage_c_native.sh) | Stage-0 native binary emission & differential execution |

---

## Compiler Optimization and Lowering Pipeline

`LeanQbe.T.compile` ([Main.lean](LeanQbe/T/Main.lean), [Opt.lean](LeanQbe/T/Opt.lean)) runs a
verified sequence of passes parameterized by a `Target` record:

1. **Early Optimization (`Func.earlyOpt`):**
   Runs constant folding and algebraic simplification, operator canonicalization, copy propagation,
   global value numbering (GVN), branch/switch and bounded boolean simplification, loop-header and
   zero-trip guard peeling, and dead-code elimination with parameter pruning.
2. **Legalization (`Func.legal`):**
   Rewrites unsupported constants, widths, addressing modes, and instructions according to the
   target's `LegalTarget` contract ([Legal.lean](LeanQbe/T/Legal.lean)).
3. **Mid-Stage / Late Optimization (`Fn.midStage` / `Func.lateOpt`):**
   Combines constant-division strength reduction, redundant load forwarding, range and bitwidth
   assumption propagation, dead-load and base+offset address-range elimination, loop-invariant code
   motion (LICM), bottom-tested loop rotation, jump threading, tail duplication, and shared epilogue
   merging, interleaved with folding, GVN, copy propagation, and dead-code elimination.
4. **First-Order Flat Pipeline (`MainFlat`):**
   [MainFlat.lean](LeanQbe/T/MainFlat.lean) executes the entire early and mid-stage optimization
   pipeline directly on flat first-order representation (`TFlat`), proved equal to the PHOAS
   pipeline (`compileFlatFn_eq_compileFn`).
5. **Spilling, Register Allocation, & Code Emission (`Spill.lean`, `Rega.lean`, `Amd64/`,
   `Arm64/`):**
   - `Spill.hints` inserts spill/reload hints to fit architectural register budgets while preserving
     control-flow and weakest-precondition semantics (`Spill.Cfg`).
   - `Rega.lowerFn` assigns physical GPR/vector registers and stack slots (`Frame`), enforcing
     target ABI invariants and unique `.L` labels (`LabelClean`).
   - Target backends emit verified SysV x86-64 or AAPCS64 AArch64 directives inside Kraken's
     machine models (`Kraken.X64`, `Kraken.AArch64`).
6. **Certificate Linking & External Interop (`MainCertCore.lean`, `MainLink.lean`, `LinkRec.lean`,
   `LinkScc.lean`, `Xcap/`):**
   - Compiled modules produce kernel-checked `LinkedCert` artifacts bounding stack usage and exit
     symbols, linked compositionally across separate compilation units (`checkLink`), recursive
     strongly connected components (`ModuleSccOk`), and opaque externally verified assembly
     (`Xcap.cptr`).

---

## Verified Kissat SAT Solver

A Boolean satisfiability (**SAT**) solver determines whether a Conjunctive Normal Form (CNF)
Boolean formula has a satisfying variable assignment (**SAT**) or none exists (**UNSAT**). Modern
**CDCL** (Conflict-Driven Clause Learning) solvers combine backtracking search with learned
conflict clauses and **inprocessing** (periodic formula simplifications such as bounded variable
elimination/addition, congruence closure, vivification, probing, and sweeping).

In `LeanQbe.T`, Kissat 4.0.4 has been ported to pure verified C0 (`0` external calls, `0` exit
symbols) with verified end-to-end compilation:

| Target | Functions | Soundness Scope | Architecture Status | Primary Audits |
| :--- | :--- | :--- | :--- | :--- |
| **Full-Fidelity Kissat** | `504` | UNSAT soundness + framing + concrete `8,192 B` UNSAT non-vacuity | Source/IR proofs (`ModuleOk`); parameterized machine-code proofs & compile guards on SysV x86-64 (`≤ 1,560 B`) and AAPCS64 AArch64 (`≤ 1,392 B`) | [KissatFidelityStep9Test.lean](LeanQbeTest/T/KissatFidelityStep9Test.lean), [KissatFidelityParamAuditX64.lean](LeanQbeTest/T/KissatFidelityParamAuditX64.lean), [KissatFidelityParamAuditArm64.lean](LeanQbeTest/T/KissatFidelityParamAuditArm64.lean), [KissatFidelityCompileGuardX64.lean](LeanQbeTest/T/KissatFidelityCompileGuardX64.lean), [KissatFidelityCompileGuardArm64.lean](LeanQbeTest/T/KissatFidelityCompileGuardArm64.lean) |
| **Certified Baseline (413 functions)** | `413` | UNSAT soundness + framing + materialized `LinkedCert` + concrete machine non-vacuity | Materialized x86-64 & AArch64 machine certificates + 140-CNF benchmark measurements | [Spec](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean), [x86-64](LeanQbeTest/T/KissatM7FidelityAuditX64.lean), [AArch64](LeanQbeTest/T/KissatM7FidelityAuditArm64.lean) |
| **Minimal CDCL (`KissatPlain`)** | `59` | **Dual SAT + UNSAT** soundness + framing + concrete SAT/UNSAT non-vacuity (`2,048 B`) | Materialized x86-64 & AArch64 machine certificates (pure CDCL, no inprocessing) | [x86-64](LeanQbeLegacyTest/KissatM3PlainLegacyAuditX64.lean), [AArch64](LeanQbeLegacyTest/KissatM3PlainLegacyAuditArm64.lean) |

### Building and Running the Native Solver

```bash
# Build native x86-64 Kissat binary (defaults to the 413-function certified baseline)
timeout 600 bash bench/kissat/build_solver.sh

# Run verified solver test suites and CLI wrapper checks
timeout 600 bash test/kissat/run.sh
timeout 600 bash test/kissat/test_cli_solver.sh

# Extract standalone C0 source (supports --target fidelity-step9 for all 504 functions)
python3 bench/kissat/extract_c0_direct.py --target fidelity-step9 -o /tmp/kissat_c0.c
```

### Trusted Computing Base (TCB) & Non-Vacuity

- **Verified by Lean:** All C0 elaboration, SSA optimization passes, spilling, register allocation,
  instruction selection, linking, and UNSAT preservation proofs (as well as SAT assignment validity
  for `KissatPlain`) are proved inside Lean 4. Every theorem depends only on
  `[propext, Classical.choice, Quot.sound]`, and concrete non-vacuity witnesses (`_nv`) execute
  inside Kraken to confirm the machine-code preconditions are satisfiable.
- **Outside Lean / In the TCB:**
  - Lean 4 kernel and Kraken operational ISA models (`Kraken.X64`, `Kraken.AArch64`).
  - `parseDimacs` specification ([LratBytes.lean](LeanQbe/T/Examples/LratBytes.lean)): requires
    variables `< 2^28`, rejects `-0`, missing headers, out-of-range variables, truncated clauses,
    trailing non-whitespace tokens, and `%` trailers; skips `'c'` comments to newline from any
    whitespace-delimited position; treats empty clauses as UNSAT and `p cnf 0 0` as empty CNF.
  - Native CLI harness ([kissat_cli.c](bench/kissat/kissat_cli.c)): enforces `RLIMIT_STACK >= 65536`,
    surrounds read-only CNF input and solver workspace with `PROT_NONE` guard pages, passes
    `-DKISSAT_UNSAT_ONLY` for UNSAT-certified builds (and `-DKISSAT_CLI_PLAIN_LAYOUT=1` for
    `KissatPlain`), and relies on the host assembler/linker (`cc`).
  - Downstream SAT consumers checking SAT outputs of UNSAT-only builds rely on external model
    verification (`kissat_verify_dimacs_model` in [kissat_verify.h](test/kissat/kissat_verify.h)),
    whereas `KissatPlain` proves SAT model soundness inside Lean.

### Four-Way Benchmark Comparison

[bench/kissat/run_4way_stage1.py](bench/kissat/run_4way_stage1.py) and
[bench/kissat/compare_4way_min.py](bench/kissat/compare_4way_min.py) benchmark the `413`-function
certified Kissat solver on 140 CNF instances on x86-64 (comparing extracted C compiled with
`gcc -O2`, verified `LeanQbe.T` native x86-64 codegen, and stock QBE):

| Pipeline | Solved (`140` CNFs) | SAT / UNSAT | Timeouts | Mean / Median Solve | PAR-2 | `.text` Size | vs. `C0-direct` | vs. `C1` (`gcc -O2`) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`C1`** (`gcc -O2` upstream Kissat) | `135 / 140` | `54S / 81U` | `5` | `1280.0 / 286.1 ms` | `3.589 s` | `373,722 B` | — | `1.00x` |
| **`C0-direct`** (`gcc -O2` extracted C0) | `135 / 140` | `55S / 80U` | `5` | `1505.8 / 306.9 ms` | `3.861 s` | `265,224 B` | `1.00x` | `1.07x` |
| **`C3b`** (`leanqbe --il` -> stock QBE) | `135 / 140` | `55S / 80U` | `5` | `1600.6 / 336.3 ms` | `3.970 s` | `227,928 B` | `1.10x` | `1.18x` |
| **`C4`** (`LeanQbe.T` verified x86-64) | `135 / 140` | `55S / 80U` | `5` | `1729.4 / 343.9 ms` | `4.121 s` | `260,792 B` | `1.12x` | `1.20x` |

---

## Bootstrapping Compiler (`LeanQbeBootstrap0`)

The bootstrapping workstream ([Mod0.lean](LeanQbe/T/Bootstrap0/Mod0.lean),
[Bootstrap0Audit.lean](LeanQbeBootstrap0Test/Bootstrap0Audit.lean)) studies compiling a
Lean-extracted Stage-0 compiler (`leanqbe0Compile`) with `LeanQbe.T` itself:

- **Stage A (`leanqbe0Mod0`, `leanqbe0Cert`):** Proves `Fn.Wf`, call-graph acyclicity
  (`checkAcyclic = true`), and signature legality for all `124` functions in `leanqbe0Mod0`, and
  checks a `LinkedCert` compiling `leanqbe0Mod0` into `17,150` SysV x86-64 directives within a
  `≤ 2048 B` stack budget (parameterized by assumed `64 B` stack/exit bounds for `rtExterns` and
  single exit `lcnf_panic`).
- **Stage B & C (`Sound0`, `Codec0`, `PrintDir0`, `StageC`):** Separately proves semantic soundness
  for `leanqbe0Compile` on guarded scalar programs (with bounded `0x7fffffff` worklist fuel),
  binary codec round-trips, AT&T assembly printer parity, and native harness differential testing via
  [test/bootstrap0/run_stage_c_native.sh](test/bootstrap0/run_stage_c_native.sh).
- **Explicit Non-Claims:** Stage A is a syntactic compilation certificate, not semantic equivalence
  (`ModuleOk` / `Eventually`) for the compiled `leanqbe0` binary itself; `lcnf_of_lean!` /
  `splice_lcnf_tflat!` extraction is outside the proof kernel; and a self-hosted binary fixpoint has
  not been proved.

---

## Repository Layout

| Path | Contents |
| :--- | :--- |
| [LeanQbe.lean](LeanQbe.lean), [LeanQbeAmd64.lean](LeanQbeAmd64.lean), [LeanQbeArm64.lean](LeanQbeArm64.lean) | Top-level library roots with strict x86-64 / AArch64 import isolation |
| [Main.lean](Main.lean), [MainArm64.lean](MainArm64.lean), [LeanQbe/T/Driver.lean](LeanQbe/T/Driver.lean) | CLI executables (`leanqbe`, `leanqbe-arm64`) |
| `LeanQbe/T/` | Core SSA IR (`IL`, `Flat`), semantics (`WP`), optimizer (`Opt`, `Main`, `MainFlat`), spilling (`Spill`), register allocation (`Rega`), certificates (`MainCert*`), linking (`MainLink*`, `LinkRec`, `LinkScc`, `LinkLfp`), QBE/C++20 printers (`PrintQbe`, `PrintCpp`) |
| `LeanQbe/T/Amd64/` & `LeanQbe/T/Arm64/` | SysV x86-64 and AAPCS64 AArch64 target contracts, instruction selection, frame lowering, and assembly printers |
| `LeanQbe/T/Unified/` | Arch-free multi-frontend / multi-backend driver, CFG recovery, and contification (`C0`, `LeanLCNF`, `Bedrock2`) |
| `LeanQbe/T/Xcap/` | Bidirectional `FnSpec` <-> `Xcap.cptr` bridge and linking combinators |
| `LeanQbe/T/Frontend/C0/`, `LeanLCNF/`, `LeanLRC/`, `Wasm/`, `Bedrock2/`, `BedrockWord/` | Source language frontends, SFI Wasm compiler, and standalone 86-fn C0 `LCNF` runtime (`LcnfC0Full`) |
| `LeanQbe/T/Logic/` | Separation-logic tree/slab automation, symbolic C0 stepper (`C0Step`), and control/legality combinators |
| `LeanQbe/T/Examples/` | Verified `ChaCha20`, `Curve25519` bignum, `UnionFind`, `LratBytes`, `LratTrim`, litmus programs, and Kissat SAT solver modules |
| `LeanQbe/T/Bootstrap0/` | Stage-0 bootstrapping compiler modules, codec, sound scalar checker, and AT&T printer |
| `LeanQbeTest/T/`, `LeanQbeBootstrap0Test/`, `LeanQbeLegacyTest/` | Lean audit specifications, parity/unit tests, compile guards, and optional legacy solver audits |
| `scripts/`, `test/`, `bench/` | [check.sh](scripts/check.sh) / [preflight.sh](scripts/preflight.sh) gates, native differential suites, and Kissat / QBE benchmark harnesses |
