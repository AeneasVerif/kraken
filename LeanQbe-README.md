# lean-qbe: a verified compiler for `LeanQbe.T`

This repository contains `LeanQbe.T`, a typed SSA intermediate language in the style of
[QBE](https://c9x.me/compile/), together with an optimizing compiler from `LeanQbe.T` to x86-64
(System V ABI) and AArch64 (AAPCS64). The language, its program logic, the compiler, and its
correctness proofs are written in Lean 4 (toolchain `leanprover/lean4:nightly-2026-11-08`). The
machine-level semantics come from Kraken, the x86-64 and AArch64 instruction-set models that this
repository builds on (see [`README.md`](README.md)).

The main components are:

- **`LeanQbe.T`** ([`LeanQbe/T/`](LeanQbe/T/)): a typed SSA intermediate representation. Functions
  (`Func`) are made of basic blocks with typed values, explicit memory operations, and calls.
- **`Func.wp`** ([`WP.lean`](LeanQbe/T/WP.lean#L70)): a weakest-precondition semantics for
  `LeanQbe.T` functions. A function's specification is stated as a `Func.wp` precondition, and
  [`ModuleOk`](LeanQbe/T/Module.lean#L196) records that every function of a module meets its
  specification under the specifications of the functions it calls.
- **C0** ([`LeanQbe/T/Frontend/C0.lean`](LeanQbe/T/Frontend/C0.lean)): a subset of C (integer
  types, pointers, structs and unions, structured control flow, function calls, and a small
  preprocessor) that a Lean macro parses and elaborates into `LeanQbe.T`. Most example programs in this repository are written in
  C0 and verified against `Func.wp` specifications.
- **The compiler** ([`Main.lean`](LeanQbe/T/Main.lean)): optimizes `LeanQbe.T`, legalizes it for a
  target, allocates registers, selects instructions, and links the result. Every pass is proved
  to preserve `Func.wp` specifications.
- **`LinkedCert`** ([`MainCertCore.lean`](LeanQbe/T/MainCertCore.lean#L207)): a certificate,
  checked by the Lean kernel, stating that the assembly directives produced for a whole module
  implement each source function's `Func.wp` specification under the Kraken x86-64 or AArch64
  instruction semantics. Combining a source-level `ModuleOk` proof with a `LinkedCert` yields a
  theorem about the behavior of the generated machine code.

## Verified components and audit files

For each verified component, the repository contains *audit files* under
[`LeanQbeTest/T/`](LeanQbeTest/T/) and [`LeanQbeBootstrap0Test/`](LeanQbeBootstrap0Test/). An
audit file restates the main theorems with their full types, explains every hypothesis and
trusted assumption, and ends with `#print axioms` reports showing that only the standard axioms
`propext`, `Classical.choice`, and `Quot.sound` are used. Architecture-specific audits are kept in
separate files, so no module imports both `Kraken.X64` and `Kraken.AArch64`.

| Component | What is audited | Audit files |
|---|---|---|
| Kissat SAT solver ([details](#verified-kissat-sat-solver)) | SAT and UNSAT soundness of the compiled solver on x86-64 and AArch64, and non-vacuity of the UNSAT result | [Spec](LeanQbeTest/T/KissatAuditSpec.lean), [X64](LeanQbeTest/T/KissatAuditX64.lean), [Arm64](LeanQbeTest/T/KissatAuditArm64.lean), [M5X64](LeanQbeTest/T/KissatM5AuditX64.lean), [M5Arm64](LeanQbeTest/T/KissatM5AuditArm64.lean), [M5SoundX64](LeanQbeTest/T/KissatM5SoundAuditX64.lean), [M5SoundArm64](LeanQbeTest/T/KissatM5SoundAuditArm64.lean), [SatSound](LeanQbeTest/T/KissatSatSoundTest.lean), [M6Sat](LeanQbeTest/T/KissatM6SatSoundTest.lean) |
| Compiler and linker ([details](#compiler-optimization-and-lowering-pipeline)) | Optimization passes, inlining, `LinkedCert`, and linking of recursive and mutually recursive functions (`LinkRec`, `LinkScc`) | [Spec](LeanQbeTest/T/CompilerAuditSpec.lean), [X64](LeanQbeTest/T/CompilerAuditX64.lean), [Arm64](LeanQbeTest/T/CompilerAuditArm64.lean) |
| Lean 4 `LCNF` / `LeanLRC` lowering | Well-formedness (`Fn.Wf`) of code lowered from the Lean compiler's `LCNF` intermediate representation ([`LeanLCNF`](LeanQbe/T/LeanLCNF/), [`LeanLRC`](LeanQbe/T/LeanLRC/)) into `LeanQbe.T` | [Audit](LeanQbeTest/T/LcnfAudit.lean) |
| LRAT proof checker | `lrat_check_bytes` returns `1` only for a well-formed DIMACS input whose CNF is unsatisfiable | [Spec](LeanQbeTest/T/LratAuditSpec.lean), [X64](LeanQbeTest/T/LratAuditX64.lean), [Arm64](LeanQbeTest/T/LratAuditArm64.lean) |
| Cryptography, bignum, and pointer code | ChaCha20 (SIMD), Curve25519 field arithmetic (`Bignum`), and union-find: source and machine-code proofs | [Spec](LeanQbeTest/T/WorkloadsAuditSpec.lean), [X64](LeanQbeTest/T/WorkloadsAuditX64.lean), [Arm64](LeanQbeTest/T/WorkloadsAuditArm64.lean) |
| C0 front end and proof tooling | `Func.wp` rules, the C0 elaborator and its well-formedness results, C0 step lemmas (`C0HeadStep`, `C0Agrees`), and separation-style memory reasoning (`SepTree`, `SlabChain`, `C0Lens`) | [Audit](LeanQbeTest/T/C0LogicAudit.lean) |
| WebAssembly memory sandbox | Module validation (`validateModule`), software-fault-isolation bounds on linear memory (`WasmMemInv`), and preservation of the host's caller frame on x86-64 and AArch64 | [Spec](LeanQbeTest/T/WasmAuditSpec.lean), [X64](LeanQbeTest/T/WasmAuditX64.lean), [Arm64](LeanQbeTest/T/WasmAuditArm64.lean) |
| Bootstrapping compiler ([details](#bootstrapping-compiler)) | A small compiler written in Lean, lowered to `LeanQbe.T` and certified for x86-64, with soundness, serialization, and printer proofs | [Bootstrap0](LeanQbeBootstrap0Test/Bootstrap0Audit.lean), [Codec0](LeanQbeBootstrap0Test/Codec0Test.lean), [PrintDir0](LeanQbeBootstrap0Test/PrintDir0Test.lean), [PrintAsm0](LeanQbeTest/T/PrintAsm0Test.lean), [Sound0](LeanQbeBootstrap0Test/Sound0Test.lean), [StageC](LeanQbeBootstrap0Test/StageCTest.lean) |

To build all audit files (they are also built by `scripts/check.sh`):

```bash
lake build --wfail LeanQbeTest.T.KissatAuditSpec LeanQbeTest.T.KissatAuditX64 \
  LeanQbeTest.T.KissatAuditArm64 LeanQbeTest.T.KissatM5AuditX64 \
  LeanQbeTest.T.KissatM5AuditArm64 LeanQbeTest.T.KissatM5SoundAuditX64 \
  LeanQbeTest.T.KissatM5SoundAuditArm64 LeanQbeTest.T.KissatSatSoundTest \
  LeanQbeTest.T.KissatM6SatSoundTest LeanQbeTest.T.KissatM5Test \
  LeanQbeTest.T.CompilerAuditSpec LeanQbeTest.T.CompilerAuditX64 \
  LeanQbeTest.T.CompilerAuditArm64 LeanQbeTest.T.LcnfAudit LeanQbeTest.T.LratAuditSpec \
  LeanQbeTest.T.LratAuditX64 LeanQbeTest.T.LratAuditArm64 \
  LeanQbeTest.T.WorkloadsAuditSpec LeanQbeTest.T.WorkloadsAuditX64 \
  LeanQbeTest.T.WorkloadsAuditArm64 LeanQbeTest.T.C0LogicAudit \
  LeanQbeTest.T.WasmAuditSpec LeanQbeTest.T.WasmAuditX64 \
  LeanQbeTest.T.WasmAuditArm64 LeanQbeTest.T.PrintAsm0Test \
  LeanQbeBootstrap0Test.Bootstrap0Audit LeanQbeBootstrap0Test.Codec0Test \
  LeanQbeBootstrap0Test.PrintDir0Test LeanQbeBootstrap0Test.Sound0Test \
  LeanQbeBootstrap0Test.StageCTest
```

[`scripts/check.sh`](scripts/check.sh) is the repository's quality gate. It builds all active
targets with warnings treated as errors, and scans every tracked `.lean` file for `sorry`,
`admit`, non-meta `axiom` declarations, `@[implemented_by]`, `@[extern]`, `trustCompiler`, and
tactics that rely on native code evaluation (`native_decide`, `bv_decide`, `ofReduceBool`, and
similar). It also checks that no module imports both architectures, that active modules do not
import retired ones, that the compiler's interface and entry-point modules do not re-export
proof modules (`*Lemmas*`) through public imports, and that re-export ("hub") files are in sync
([`scripts/sync_hubs.py`](scripts/sync_hubs.py),
[`scripts/check_firewall.py`](scripts/check_firewall.py)). Finally, it checks the
`#print axioms` output of the theorems listed in [`scripts/headlines.d`](scripts/headlines.d).

Earlier, superseded versions of the Kissat solver and their audit suites live in
[`LeanQbeLegacyTest/`](LeanQbeLegacyTest/); they are built and audited only with
`INCLUDE_LEGACY=1 ./scripts/check.sh` (or [`scripts/tier3_check.sh`](scripts/tier3_check.sh)).

## Compiler optimization and lowering pipeline

This section follows the order in which passes run, as defined in [`Opt.lean`](LeanQbe/T/Opt.lean)
and [`Main.lean`](LeanQbe/T/Main.lean). Each pass is a function on `LeanQbe.T` functions together
with a theorem stating that it preserves `Func.wp` specifications (typically named `*_spec` or
`*_ok`). The headline theorems are restated in
[`CompilerAuditSpec.lean`](LeanQbeTest/T/CompilerAuditSpec.lean),
[`CompilerAuditX64.lean`](LeanQbeTest/T/CompilerAuditX64.lean), and
[`CompilerAuditArm64.lean`](LeanQbeTest/T/CompilerAuditArm64.lean).

### 1. Module-level inlining

[`Module.optInlinePolicy`](LeanQbe/T/MainInline.lean#L21) (and its fixed-budget variant
`Module.optInline`) inlines calls to non-recursive callees across a whole module before any
per-function optimization runs.

- An `InlinePolicy` decides which call sites to inline. It combines a callee size budget with
  more generous limits for leaf functions and for callees with a single call site, a cap on the
  size of the resulting caller, limits on how much loop code may be duplicated, and an option to
  keep callees out of line when their call sites sit behind cold, single-sided guards (slow
  paths). The tuned general-purpose policy used for the Kissat solver is
  [`InlinePolicy.b5`](LeanQbe/T/Inline.lean#L377); the policy is applied by
  [`Module.inlinePolicy`](LeanQbe/T/Inline.lean#L572).
- Correctness: [`Module.inline_ok`](LeanQbe/T/InlineLemmas.lean#L683),
  [`Module.optInlinePolicy_ok`](LeanQbe/T/MainInline.lean#L110), and
  [`Module.optInline_ok`](LeanQbe/T/OptLemmas.lean#L552).
- For large modules, the inlined module is computed once at elaboration time and recorded
  together with a kernel-checked equation relating it to `Module.optInlinePolicy`
  ([`inline_mod!`](LeanQbe/T/MainCertInline.lean#L566)). A chunked variant
  ([`InlineChunk.lean`](LeanQbe/T/InlineChunk.lean),
  [`inline_chunk_base!`](LeanQbe/T/MainCertInlineChunk.lean#L586), `inline_mod_chunk!`,
  `inline_mod_join!`) processes the module in pieces to bound memory use. Tests:
  [`InlineB5Test.lean`](LeanQbeTest/T/InlineB5Test.lean) and
  [`InlinePolicyB5Test.lean`](LeanQbeTest/T/InlinePolicyB5Test.lean).

### 2. SSA optimizations before legalization

[`Func.earlyOpt`](LeanQbe/T/Opt.lean#L198) (correctness:
[`Func.earlyOpt_spec`](LeanQbe/T/OptLemmas.lean#L281)) runs the following passes in order:

1. [`Func.fold`](LeanQbe/T/Fold.lean#L863) — constant folding and algebraic simplification
   ([`FoldLemmas.lean#L2926`](LeanQbe/T/FoldLemmas.lean#L2926)).
2. [`Func.canon`](LeanQbe/T/Canon.lean#L254) — ordering of commutative operands and reassociation of constant chains
   ([`CanonLemmas.lean#L829`](LeanQbe/T/CanonLemmas.lean#L829)).
3. [`Func.copy`](LeanQbe/T/Copy.lean#L187) — copy propagation
   ([`CopyLemmas.lean#L849`](LeanQbe/T/CopyLemmas.lean#L849)).
4. [`Func.gvn`](LeanQbe/T/Gvn.lean#L259) — global value numbering
   ([`GvnLemmas.lean#L812`](LeanQbe/T/GvnLemmas.lean#L812)).
5. `Func.copy`, then `Func.fold` again.
6. [`Func.ifOpt`](LeanQbe/T/IfOpt.lean#L350) — if-conversion of branch diamonds into `select`
   instructions ([`Func.ifOptWith`](LeanQbe/T/IfOpt.lean#L345);
   [`IfOptLemmas.lean#L1821`](LeanQbe/T/IfOptLemmas.lean#L1821)).
7. [`Func.simplifyGroupFast`](LeanQbe/T/Opt.lean#L123) /
   [`Func.simplifyGroupPlan`](LeanQbe/T/SimplifyGroupPlan.lean#L449) — control-flow
   simplification
   ([`SimplifyGroupPlanLemmas.lean#L677`](LeanQbe/T/SimplifyGroupPlanLemmas.lean#L677)).
8. [`Func.peelFast`](LeanQbe/T/Opt.lean#L132) / [`Func.peel`](LeanQbe/T/Peel.lean#L202) — loop
   peeling ([`PeelLemmas.lean#L904`](LeanQbe/T/PeelLemmas.lean#L904)).
9. [`Func.zeroPeelWith`](LeanQbe/T/ZeroPeel.lean#L512) — widening of constant-fill loops and
   peeling of single-iteration loops
   ([`ZeroPeelLemmas.lean#L2461`](LeanQbe/T/ZeroPeelLemmas.lean#L2461),
   [`ZeroPeelLemmas1.lean`](LeanQbe/T/ZeroPeelLemmas1.lean)).
10. `Func.copy`, then `Func.fold` again.
11. [`Func.dceP`](LeanQbe/T/DceParam.lean#L279) — dead-code elimination, including unused block
    parameters ([`DceParamLemmas.lean#L688`](LeanQbe/T/DceParamLemmas.lean#L688)).
12. `Func.renorm` — renumbering into a normalized form ([`Flat.lean`](LeanQbe/T/Flat.lean),
    [`FlatLemmas.lean#L756`](LeanQbe/T/FlatLemmas.lean#L756)).

### 3. Target legalization

[`Func.legal`](LeanQbe/T/Legal.lean#L115) rewrites types and operations that the target does not
support directly into supported ones, while keeping multi-word arithmetic chains (add with carry
`addc`, subtract with borrow `subb`, widening multiply `umulw`) intact. It is checked by
[`LegalCheck3.lean`](LeanQbe/T/LegalCheck3.lean) and proved in
[`LegalLemmas.lean`](LeanQbe/T/LegalLemmas.lean).

### 4. SSA and loop optimizations after legalization

[`Func.lateOpt`](LeanQbe/T/Opt.lean#L238), invoked from [`Fn.midStage`](LeanQbe/T/Main.lean#L56)
(correctness: [`Func.lateOpt_spec`](LeanQbe/T/OptLemmas.lean#L430)), runs four groups of passes in
order, renormalizing (`Func.renorm`) between groups:

1. [`Func.lateCorePre`](LeanQbe/T/Opt.lean#L203): `Func.fold`, `Func.canon`,
   [`Func.divConst`](LeanQbe/T/DivConst.lean#L278) (division by constants via multiplication and
   shifts; [`DivConstLemmas.lean#L1385`](LeanQbe/T/DivConstLemmas.lean#L1385)), `Func.copy`.
2. [`Func.lateCorePost`](LeanQbe/T/Opt.lean#L207):
   [`Func.memLoad`](LeanQbe/T/MemLoad.lean#L425) (load common-subexpression elimination and store-to-load forwarding;
   [`MemLoadLemmas.lean#L1761`](LeanQbe/T/MemLoadLemmas.lean#L1761)), `Func.gvn`,
   [`Func.assumeBits`](LeanQbe/T/AssumeBits.lean#L301) (simplification using known-bits facts;
   [`AssumeBitsLemmas.lean#L1114`](LeanQbe/T/AssumeBitsLemmas.lean#L1114)), `Func.fold`.
3. [`Func.lateCfgPre`](LeanQbe/T/Opt.lean#L217):
   [`Func.ifOptBits`](LeanQbe/T/IfOpt.lean#L354) (if-conversion restricted to machine integer
   types; [`IfOptLemmas.lean#L1827`](LeanQbe/T/IfOptLemmas.lean#L1827)),
   `Func.simplifyGroupFast`, [`Func.deadLoadElim`](LeanQbe/T/Dce.lean#L153) (removal of unused
   loads; [`DceLemmas.lean#L451`](LeanQbe/T/DceLemmas.lean#L451)),
   [`Func.assumeElim`](LeanQbe/T/MemLoad.lean#L465) (removal of branches whose other arm halts;
   [`MemLoadLemmas.lean#L1865`](LeanQbe/T/MemLoadLemmas.lean#L1865)), `Func.fold`, `Func.gvn`.
4. [`Func.lateCfgPost`](LeanQbe/T/Opt.lean#L222) and
   [`Func.lateLoopRotate`](LeanQbe/T/Opt.lean#L226):
   [`Func.licm`](LeanQbe/T/Licm.lean#L885) (loop-invariant code motion;
   [`LicmLemmas.lean#L813`](LeanQbe/T/LicmLemmas.lean#L813)), `Func.dceP`,
   [`Func.loopRotate`](LeanQbe/T/LoopRotate.lean#L931) (loop rotation;
   [`LoopRotateLemmas.lean#L2863`](LeanQbe/T/LoopRotateLemmas.lean#L2863)),
   [`Func.mergeRets`](LeanQbe/T/Opt.lean#L182) (merging of return blocks;
   [`OptLemmas.lean#L211`](LeanQbe/T/OptLemmas.lean#L211)).

### 5. Register allocation, instruction selection, and linking

The back end consists of an unverified hint analysis followed by verified lowering:

- **Hint analysis (untrusted).** [`Spill.hints`](LeanQbe/T/Spill.lean#L1968) and
  [`SpillFlags.lean`](LeanQbe/T/SpillFlags.lean) compute register-allocation and code-layout
  hints: spill placement and related options ([`Spill.Cfg`](LeanQbe/T/Spill.lean#L276)),
  splitting of live ranges into hot and cold parts
  ([`tryEvictSplit`](LeanQbe/T/Spill.lean#L652),
  [`SpillB5Test.lean`](LeanQbeTest/T/SpillB5Test.lean)), allocation of condition flags,
  addressing-mode folding (`[base + disp]` and scaled-index forms), and inversion of branches
  toward the hot path using execution weights. These hints are not part of the trusted base:
  every hint is re-checked during lowering, so an incorrect hint can cause compilation to fail
  or produce slower code, but cannot produce incorrect code.
- **Register allocation and lowering.** [`Rega.lowerFn`](LeanQbe/T/Rega.lean#L1697) (proved in
  [`RegaLemmas4.lean#L1060`](LeanQbe/T/RegaLemmas4.lean#L1060) and `RegaLemmas1.lean` to
  `RegaLemmas3.lean`) validates the hints and performs register allocation. It also removes
  redundant 32-to-64-bit zero extensions on x86-64
  ([`elideZext32?`](LeanQbe/T/Rega.lean#L732), [`zeroUpper32Op`](LeanQbe/T/Target.lean#L275);
  [`X64Zext32ElideTest.lean`](LeanQbeTest/T/X64Zext32ElideTest.lean)), fuses comparisons with
  conditional branches and lays out the hot successor as the fall-through
  ([`fuseJnzChoice`](LeanQbe/T/Rega.lean#L1241), [`jnzSetup`](LeanQbe/T/Rega.lean#L1260);
  [`InvertJnzTest.lean`](LeanQbeTest/T/InvertJnzTest.lean),
  [`InvertJnzArm64Test.lean`](LeanQbeTest/T/InvertJnzArm64Test.lean)), and sequentializes
  parallel moves (tested in `FlagRaOptTest.lean` and `FlagRaOptArm64Test.lean`).
- **Instruction selection.** Selection of `[base + disp]` addressing, x86-64 scaled-index
  addressing `[base + idx*scale + disp]` ([`recordAddVarImm`](LeanQbe/T/Rega.lean#L571),
  [`recordDef_elide_ok`](LeanQbe/T/RegaLemmas1.lean#L2267), example
  [`addrSibScaledDispFn`](LeanQbeTest/T/FlagRaOptTest.lean#L328)), bit operations, conditional
  selects, stack frames, and SIMD instructions
  ([`Amd64/Isel.lean`](LeanQbe/T/Amd64/Isel.lean),
  [`Amd64/IselLemmas5.lean#L1342`](LeanQbe/T/Amd64/IselLemmas5.lean#L1342),
  [`Arm64/Isel.lean`](LeanQbe/T/Arm64/Isel.lean),
  [`Arm64/IselLemmas4.lean#L1595`](LeanQbe/T/Arm64/IselLemmas4.lean#L1595)).
- **Linking and certificates.** [`compileFn`](LeanQbe/T/Main.lean#L138) and
  [`compileModule`](LeanQbe/T/Main.lean#L197) drive the full pipeline
  ([`compileFn_correct`](LeanQbe/T/MainLemmas.lean#L728)). Separately compiled pieces of a
  module can be linked compositionally
  ([`compileModule_append`](LeanQbe/T/MainLink.lean#L231)); `LinkedCert` itself is built in
  [`MainCertCore.lean`](LeanQbe/T/MainCertCore.lean) and
  [`MainCertProof.lean`](LeanQbe/T/MainCertProof.lean). Recursive functions
  ([`link_rec_compiled`](LeanQbe/T/LinkRecLemmas.lean#L1123)) and groups of mutually recursive
  functions, i.e. strongly connected components of the call graph
  ([`link_scc_compiled`](LeanQbe/T/LinkSccLemmas2.lean#L67),
  [`link_scc_static`](LeanQbe/T/LinkLfp.lean#L240)), are supported.

## Verified Kissat SAT solver

The largest program verified with this toolchain is a port of the
[Kissat](https://github.com/arminbiere/kissat) SAT solver to C0. The current verified version is
the module `LeanQbe.T.Examples.Kissat.FullM5`
([`FullM5.lean`](LeanQbe/T/Examples/Kissat/FullM5.lean#L354)), which consists of 270 functions
after inlining with `InlinePolicy.b5`. For this module, the repository proves soundness of both
SAT and UNSAT answers for the compiled machine code on x86-64 and on AArch64.

The solver exports a single C entry point:

```c
uint64_t kissat_solve_bytes(const uint8_t *cnf_ptr, uint64_t cnf_len,
                            uint8_t *work_ptr, uint64_t work_len, uint64_t fuel);
/* Returns 20 = UNSAT, 10 = SAT (model left in the workspace), 0 = unknown. */
```

`cnf_ptr`/`cnf_len` is a DIMACS CNF file in memory, `work_ptr`/`work_len` is a caller-provided
workspace, and `fuel` bounds the number of solver steps. The solver returns `0` for malformed
input or when it runs out of fuel or workspace.

Newer solver modules are also present under
[`LeanQbe/T/Examples/Kissat/`](LeanQbe/T/Examples/Kissat/): `FullM6` (382 functions) has a C0
source, a well-formedness and acyclicity proof, a chunked inlined module, and source-level SAT and
UNSAT proof combinators, but no machine-code certificate yet; the `FullM7*` files contain
individual C0 components with their source-level proofs. Neither is covered by a machine-code
soundness theorem.

### Building and running the solver

Prerequisites: `elan` (which installs the toolchain named in `lean-toolchain`), a C compiler, and,
for AArch64 binaries on an x86-64 host, `aarch64-linux-gnu-gcc` and `qemu-aarch64`.

[`bench/kissat/build_solver.sh`](bench/kissat/build_solver.sh) builds the Lean code, prints the
certified assembly for the selected module and architecture, and links it with the command-line
wrapper [`bench/kissat/kissat_cli.c`](bench/kissat/kissat_cli.c). The defaults are
`--module FullM5 --arch x64`, producing `/tmp/kissat-leanqbe-fullm5`.

```bash
# x86-64
bash bench/kissat/build_solver.sh --module FullM5 --arch x64 -o /tmp/kissat-leanqbe-fullm5

# AArch64 (runs under qemu-aarch64 on an x86-64 host)
bash bench/kissat/build_solver.sh --module FullM5 --arch arm64 -o /tmp/kissat-leanqbe-fullm5-arm64

# Usage: kissat-leanqbe [--work-mb <MB>] [--fuel <N>] [-n|--no-model] <input.cnf | ->
printf 'p cnf 1 2\n1 0\n-1 0\n' | /tmp/kissat-leanqbe-fullm5 -
# s UNSATISFIABLE          (exit status 20)

printf 'p cnf 2 2\n1 2 0\n-1 0\n' | /tmp/kissat-leanqbe-fullm5 -
# s SATISFIABLE            (exit status 10)
# v -1 2 0

qemu-aarch64 -L /usr/aarch64-linux-gnu /tmp/kissat-leanqbe-fullm5-arm64 input.cnf
```

The program prints a DIMACS status line (`s SATISFIABLE`, `s UNSATISFIABLE`, or `s UNKNOWN`) and
exits with status `10`, `20`, or `0` respectively; for satisfiable inputs it also prints the
model as `v ... 0` lines unless `-n` is given. Exit status `1` indicates a usage or I/O error.

The emitted assembly matches the `LinkedCert` only for the default settings. The options
`--inline-max <N>` with `N > 0` and `--debug` change the generated code and print a warning;
binaries built with them, or with `--allow-uncertified`, are not covered by the proofs.

Tests and proofs:

```bash
# Builds FullM5 for x86-64 and AArch64 and checks exit codes, models, -n, stdin input,
# and workspace guard pages.
bash test/kissat/test_cli_solver.sh

# Machine-code and source-level audit files for the solver.
lake build --wfail LeanQbeTest.T.KissatAuditSpec LeanQbeTest.T.KissatAuditX64 \
  LeanQbeTest.T.KissatAuditArm64 LeanQbeTest.T.KissatSatSoundTest
```

### What is proved

The audit files restate the main theorems with full types:

- [`KissatAuditX64.lean`](LeanQbeTest/T/KissatAuditX64.lean) and
  [`KissatAuditArm64.lean`](LeanQbeTest/T/KissatAuditArm64.lean) re-export the machine-code audits
  for `FullM5` from [`KissatM5AuditX64.lean`](LeanQbeTest/T/KissatM5AuditX64.lean),
  [`KissatM5AuditArm64.lean`](LeanQbeTest/T/KissatM5AuditArm64.lean),
  [`KissatM5SoundAuditX64.lean`](LeanQbeTest/T/KissatM5SoundAuditX64.lean), and
  [`KissatM5SoundAuditArm64.lean`](LeanQbeTest/T/KissatM5SoundAuditArm64.lean). The theorems
  are also listed in [`scripts/headlines.d/kissat_m5.txt`](scripts/headlines.d/kissat_m5.txt).
- [`KissatSatSoundTest.lean`](LeanQbeTest/T/KissatSatSoundTest.lean) covers source-level SAT and
  UNSAT soundness and a concrete SAT non-vacuity example;
  [`KissatM6SatSoundTest.lean`](LeanQbeTest/T/KissatM6SatSoundTest.lean) covers the source-level
  proof combinators for `FullM6`.
- [`KissatAuditSpec.lean`](LeanQbeTest/T/KissatAuditSpec.lean) audits the specification:
  the DIMACS parser `parseDimacs` and the predicates `CNF.Unsat` and `CNF.Sat`.

#### Machine-code soundness

[`m5_solve_bytes_model_x64`](LeanQbe/T/Amd64/KissatM5Sound.lean#L89) and
[`m5_solve_bytes_model_arm64`](LeanQbe/T/Arm64/KissatM5Sound.lean#L88), together with the
UNSAT-only theorems [`m5_solve_bytes_unsat_x64`](LeanQbe/T/Amd64/KissatM5.lean#L88) and
[`m5_solve_bytes_unsat_arm64`](LeanQbe/T/Arm64/KissatM5.lean#L88), state the following. Take any
executable that contains the compiled 270-function module (`kissatM5_compiled_x64` or
`kissatM5_compiled_arm64`), and any call to `kissat_solve_bytes` that follows the platform ABI,
passes DIMACS bytes and a suitably aligned workspace, has enough stack, and has a caller frame
`R`. Then execution terminates and returns to the caller with:

- a result in `{0, 10, 20}` (in `rax` or `X0`);
- if the result is `20`: `∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`;
- if the result is `10`: `∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ (∃ α, cnf.Sat α) ∧
  cnf.Sat (readModelFromWork st.data.dmem work_ptr)`, i.e. the assignment stored in the
  workspace satisfies the input formula;
- callee-saved registers (`rbx`, `rbp`, `r12`–`r15` on x86-64; `X19`–`X29` on AArch64) and the
  stack pointer restored;
- the input bytes unchanged, the workspace and stack frame accounted for as separate memory
  regions, and the caller frame `R` untouched.

#### How SAT answers are checked

Kissat's inprocessing transformations (such as variable elimination) require reconstructing a
model of the original formula at the end of the search. Rather than verifying that
reconstruction, the solver checks its result. In
[`FullM5Orch.lean`](LeanQbe/T/Examples/Kissat/FullM5Orch.lean#L643), after model reconstruction
(`full_extend`) for a candidate SAT result, `kissat_solve_bytes_m5` restores the original variable
count and calls the verified function `kissat_check_model`, which evaluates every clause of the
original, read-only DIMACS input under the assignment
[`readModelFromWork`](LeanQbe/T/Examples/Kissat/FullSatSound.lean#L102). The solver returns `10`
only if every clause is satisfied, and `0` otherwise. The corresponding source-level theorem is
[`kissat_solve_bytes_m5_model_wp`](LeanQbe/T/Examples/Kissat/FullSatSound.lean#L838);
[`ModuleOk.respec_tail`](LeanQbe/T/Examples/Kissat/FullSatSound.lean#L42) transfers the
specifications of the remaining 268 functions into the environment used for this proof.

#### Non-vacuity

A soundness theorem whose hypotheses can never be met would be vacuous. The repository therefore
also shows that the hypotheses are satisfiable and that the interesting results are reachable:

- Machine code (UNSAT): [`audit_m5_x64_nv_closed`](LeanQbeTest/T/KissatM5AuditX64.lean#L137) and
  [`audit_m5_arm_nv_closed`](LeanQbeTest/T/KissatM5AuditArm64.lean#L135) instantiate the
  machine-code theorems on the concrete hosts `kissatM5_compiled_x64.host` and
  `kissatM5_compiled_arm64.host` and show that executions returning `20` exist.
- Source level (SAT): [`m5_sat_nonvacuous`](LeanQbe/T/Examples/Kissat/FullM5SatNv.lean#L2721)
  (audited as [`audit_m5_sat_nv`](LeanQbeTest/T/KissatSatSoundTest.lean#L151)) runs the
  solver on `"p cnf 1 1\n1 0\n"` under `Func.wp` with a 4096-byte workspace and `fuel = 16`, and
  shows that it returns `10` with a satisfying assignment readable via `readModelFromWork`.

#### Axioms

Every audited theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. The
repository contains no `sorry`, `admit`, non-meta `axiom`, `@[implemented_by]`, `@[extern]`,
`native_decide`, `bv_decide`, or `ofReduceBool`; [`scripts/check.sh`](scripts/check.sh) enforces
this for all tracked `.lean` files.

### Trusted computing base

To conclude that a `kissat-leanqbe` binary built with the default settings prints
`s UNSATISFIABLE` only for unsatisfiable inputs, and `s SATISFIABLE` with a model only for
satisfiable ones, one must trust:

1. **The specification:** `Std.Sat.CNF.Unsat` and `Std.Sat.CNF.Sat` from the Lean standard library,
   and [`parseDimacs`](LeanQbe/T/Examples/LratBytes.lean#L150), a pure ASCII DIMACS parser
   (checked on examples in `KissatAuditSpec.lean`). `parseDimacs` rejects headers and variable
   indices `>= 2^28`, the literal `-0`, missing headers, out-of-range variables, truncated
   clauses, and trailing tokens. Its dialect differs from other parsers in a few details:
   - a lowercase `c` starts a comment that runs to the end of the line at any
     whitespace-delimited position, not only at the start of a line (uppercase `C`, or a `c`
     attached to digits such as `12c`, is rejected);
   - leading zeros are accepted (`00` terminates a clause, `01` denotes variable `1`);
   - an empty clause yields an unsatisfiable CNF, and `p cnf 0 0` yields the empty CNF;
   - SATLIB-style `%` end-of-file trailers are rejected.
2. **The Lean kernel** and the three standard axioms listed above.
3. **The Kraken ISA semantics** for x86-64 and AArch64, in which the machine-code theorems are
   stated, and the assembler and linker that turn the printed directives (`Kraken.X64.PrintATT`,
   `Kraken.AArch64.Print`) into an executable.
4. **The harness:** [`kissat_cli.c`](bench/kissat/kissat_cli.c), which reads the input, checks
   that `RLIMIT_STACK` is at least 65536 bytes, maps the input read-only and the workspace
   read-write between inaccessible guard pages, calls `kissat_solve_bytes`, and prints the result
   and model; and the C runtime it links against.

The following are not trusted, because they are checked by the Lean kernel: the C0 solver
sources, the C0 elaborator, the inlining policy and its materialization, every compiler pass
(optimization, legalization, register allocation, instruction selection, and linking), and all
`Func.wp` proofs.

## Bootstrapping compiler

`LeanQbeBootstrap0` contains `leanqbe0Compile`
([`Compiler0.lean`](LeanQbe/T/Bootstrap0/Compiler0.lean)), a minimal compiler for monomorphic
scalar programs, written in Lean. It is lowered from Lean into `LeanQbe.T` and compiled by the
verified compiler. The results are organized in three stages:

- **Stage A: the compiler as a certified `LeanQbe.T` module**
  ([`Bootstrap0Audit.lean`](LeanQbeBootstrap0Test/Bootstrap0Audit.lean)).
  [`leanqbe0Mod0`](LeanQbe/T/Bootstrap0/Mod0.lean) is the 124-function `LeanQbe.T` module obtained
  by lowering `leanqbe0Compile` through `LeanLCNF`. It is proved well-formed
  (`leanqbe0Mod0_wf`), free of recursion (`leanqbe0Mod0_acyclic`), and legal for x86-64
  (`leanqbe0Mod0_legalSig`). [`leanqbe0Cert`](LeanQbe/T/Bootstrap0/Cert.lean#L39) is a
  `LinkedCert` for all 124 functions on x86-64 (System V), with stack usage of at most 2048 bytes,
  assuming a stack bound of 64 bytes (`rtExtBounds0`) for each C runtime function it calls
  (`rtExterns`) and a single exit symbol `lcnf_panic`.
- **Stage B: compiler soundness, serialization, and printers.**
  - [`Sound0.lean`](LeanQbe/T/Bootstrap0/Sound0.lean#L1360) (audited in
    [`Sound0Test.lean`](LeanQbeBootstrap0Test/Sound0Test.lean)) proves that `leanqbe0Compile`
    produces code meeting its source semantics (`leanqbe0Compile_fnSpec`,
    `leanqbe0Compile_sound_layout`, `bridge_leanqbe0Compile_fnSpec`,
    `bridge_leanqbe0Compile_layout`), and runs small example programs (`dummyAddMod0`,
    `dummyLoopMod0`, `c0_add_two`) to completion on x86-64.
  - [`Codec0.lean`](LeanQbe/T/Bootstrap0/Codec0.lean)
    ([`Codec0Test.lean`](LeanQbeBootstrap0Test/Codec0Test.lean)) proves that its binary encoding
    of modules round-trips (`decodeMod0_encodeMod0`, `encodeMod0_decodeMod0`) and that malformed
    buffers are rejected.
  - [`PrintAsm0.lean`](LeanQbe/T/Amd64/PrintAsm0.lean) /
    [`PrintAsm0Lemmas.lean`](LeanQbe/T/Amd64/PrintAsm0Lemmas.lean)
    ([`PrintAsm0Test.lean`](LeanQbeTest/T/PrintAsm0Test.lean)) and
    [`PrintDir0.lean`](LeanQbe/T/Bootstrap0/PrintDir0.lean)
    ([`PrintDir0Test.lean`](LeanQbeBootstrap0Test/PrintDir0Test.lean)) prove that its AT&T
    assembly printer agrees character for character with `Kraken.X64.toATT` / `Driver.emitAsm`
    on all 27 constructors of its directive type `Dir0`.
- **Stage C: concrete executions**
  ([`StageC.lean`](LeanQbe/T/Bootstrap0/StageC.lean),
  [`StageCTest.lean`](LeanQbeBootstrap0Test/StageCTest.lean)) connects the Stage B results to
  concrete x86-64 executions of compiled example programs (`c0_sqr`, `c0_pipeline`,
  `sat_lit_var`, `sat_lit_sign`, `sat_lit_neg`).

The following are assumed rather than proved:

- There is no `ModuleOk`, `FnSpec`, or termination theorem for `leanqbe0Mod0` itself; the
  behavior of the C runtime (`lcnf_rt.c`) and its stack bounds are assumed.
- Extraction of Lean code into `LeanLCNF` (`lcnf_of_lean!`, `splice_lcnf_tflat!`) is proved to
  produce well-formed code (`Fn.Wf`), not to be semantically equivalent to evaluating
  `leanqbe0Compile` in Lean.
- The native binary has not been used to compile itself, and no self-compilation fixpoint is
  proved.

## Repository layout

| Path | Contents |
|---|---|
| `LeanQbe/T/` | IR, `Func.wp` logic, compiler and inliner passes, linking proofs |
| `LeanQbe/T/Frontend/C0/` | C0 lexer, parser, and elaborator |
| `LeanQbe/T/Wasm/` | WebAssembly validator, sandboxed lowering, and linear-memory safety proofs |
| `LeanQbe/T/Bootstrap0/` | Bootstrapping compiler `leanqbe0Compile`, its certificate, and its proofs |
| `LeanQbe/T/Examples/Kissat/` | C0 sources, specifications, inlining policies, and `Func.wp` proofs of the Kissat solver |
| `LeanQbe/T/Amd64/`, `LeanQbe/T/Arm64/` | Target instances, machine-code certificates, and end-to-end theorems |
| `LeanQbeTest/T/`, `LeanQbeBootstrap0Test/` | Tests and audit files (each imports at most one architecture) |
| `LeanQbeLegacyTest/` | Audits of superseded solver versions (built with `INCLUDE_LEGACY=1`) |
| `bench/kissat/` | Solver command-line wrapper, build script, CNF generators, and differential tests |
| `test/kissat/` | Command-line solver tests |
| `scripts/` | [`check.sh`](scripts/check.sh), [`tier3_check.sh`](scripts/tier3_check.sh), hub and import checks, theorem lists (`headlines.d/`) |
| `docs/reports/` | Design notes on individual components |
