# lean-qbe: a verified compiler for `LeanQbe.T`

`LeanQbe.T` is a typed SSA intermediate language in the style of
[QBE](https://c9x.me/compile/), together with an optimizing compiler to x86-64 (System V ABI) and
AArch64 (AAPCS64). The language, its weakest-precondition program logic, the compiler passes, and
the machine-code certificates are written and proved in Lean 4
(`leanprover/lean4:nightly-2026-11-08`) on top of the Kraken x86-64 and AArch64 instruction-set
models (see [`README.md`](README.md)). All audited theorems use only Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`), with no `sorry`, non-meta `axiom`,
`native_decide`, or `bv_decide`.

The main case study is a C0 port of the [Kissat 4.0.4](https://github.com/arminbiere/kissat)
CDCL SAT solver, currently certified at its `FullM7Fidelity` baseline (413 functions; bounded
workspace and step fuel) covering Kissat's search and inprocessing. It is certified down to x86-64
and AArch64 machine code for UNSAT soundness, memory/register framing, and concrete UNSAT
non-vacuity, while checking candidate SAT models at runtime against the original DIMACS input via
`kissat_check_model`. Alongside it, `KissatPlain` (59 functions) is a smaller pure-CDCL reference
solver without inprocessing whose machine-code proofs cover **both SAT and UNSAT soundness** on
x86-64 and AArch64. On a 140-CNF benchmark suite (30 s limit), the certified `FullM7Fidelity`
baseline solves 135/140 instances (matching upstream Kissat 4.0.4's 135/140) at 1.12x
geometric-mean wall time vs `clang -O3` on the same C0 source, 1.02x vs `clang++ -O3` on the same
`LeanQbe.T` IR, and 1.20x (1.15x PAR-2) vs upstream Kissat 4.0.4.

### Where to start

- **Inspect the theorems and TCB:** standalone audit files under [`LeanQbeTest/T/`](LeanQbeTest/T/)
  (for example [`KissatM7FidelityAuditX64.lean`](LeanQbeTest/T/KissatM7FidelityAuditX64.lean),
  [`KissatM7FidelityAuditArm64.lean`](LeanQbeTest/T/KissatM7FidelityAuditArm64.lean), and
  [`CompilerAuditX64.lean`](LeanQbeTest/T/CompilerAuditX64.lean)) restate the headline theorems
  with their full types and `#print axioms` checks. See
  [Trusted computing base](#trusted-computing-base) for what the kernel checks versus what remains
  trusted, and [`scripts/check.sh`](scripts/check.sh) for the repository quality gate.
- **Build and run the solver:** [`bench/kissat/build_solver.sh`](bench/kissat/build_solver.sh)
  emits certified x86-64 or AArch64 assembly and links a standalone DIMACS CLI binary.
- **Reproduce the benchmarks:** [`bench/kissat/compare_4way_min.py`](bench/kissat/compare_4way_min.py)
  is a self-contained 245-line Python script that prints every compile and link command, calls
  `Driver.compileFns` directly, runs all four comparison builds sequentially in rotated order,
  checks every SAT model, and reports timings and code sizes.

### Architecture overview

- **`LeanQbe.T`** ([`LeanQbe/T/`](LeanQbe/T/)): a typed SSA intermediate representation. Functions
  (`Func`) consist of basic blocks with typed values, explicit memory operations, and calls.
- **`Func.wp`** ([`WP.lean`](LeanQbe/T/WP.lean)): a weakest-precondition semantics for
  `LeanQbe.T` functions. A function's specification is stated as a `Func.wp` precondition, and
  [`ModuleOk`](LeanQbe/T/Module.lean) records that every function of a module meets its
  specification under the specifications of the functions it calls.
- **C0** ([`LeanQbe/T/Frontend/C0.lean`](LeanQbe/T/Frontend/C0.lean), tested in
  [`C0ExtensionsTest.lean`](LeanQbeTest/T/C0ExtensionsTest.lean) and
  [`test/c0/run.sh`](test/c0/run.sh)): a subset of C (integer types, pointers, structs and
  unions, structured control flow, function calls, `#include` headers, parameterized/variadic
  macros, `offsetof`, `_Static_assert`, and audit pragmas) parsed and elaborated into `LeanQbe.T` by
  a Lean macro. Most verified programs in this repository are written in C0 and proved against
  `Func.wp` specifications.
- **The compiler** ([`Main.lean`](LeanQbe/T/Main.lean)): performs whole-module inlining, pre- and
  post-legalization SSA/loop optimizations, target legalization, hint-validated register
  allocation, instruction selection, and compositional linking. Every pass is proved to preserve
  `Func.wp` specifications.
- **`LinkedCert`** ([`MainCertCore.lean`](LeanQbe/T/MainCertCore.lean)): a kernel-checked
  certificate stating that the assembly directives produced for a whole module implement each
  source function's `Func.wp` specification under the Kraken x86-64 or AArch64 semantics.
  Combining a source-level `ModuleOk` proof with a `LinkedCert` yields an end-to-end theorem about
  the generated machine code.

## Verified components and audit files

For each verified component, the repository provides standalone *audit files* under
[`LeanQbeTest/T/`](LeanQbeTest/T/), [`LeanQbeBootstrap0Test/`](LeanQbeBootstrap0Test/), and
[`LeanQbeLegacyTest/`](LeanQbeLegacyTest/). Each audit file restates the headline theorems with
their full types, documents every hypothesis and trusted assumption, and ends with `#print axioms`
checks confirming that only `propext`, `Classical.choice`, and `Quot.sound` are used.
Architecture-specific audits live in separate files so no module imports both `Kraken.X64` and
`Kraken.AArch64`.

| Component | What is audited | Audit files |
|---|---|---|
| Kissat SAT solver ([details](#verified-kissat-sat-solver)) | `FullM7Fidelity` (413 fns): x86-64 & AArch64 `LinkedCert` UNSAT soundness and concrete UNSAT non-vacuity (runtime `kissat_check_model` on SAT); `KissatPlain` (59 fns, optional `LeanQbeLegacy*` library): x86-64 & AArch64 SAT and UNSAT soundness + concrete SAT/UNSAT non-vacuity | [Spec](LeanQbeTest/T/KissatAuditSpec.lean), [M7FidSpec](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean), [M7FidX64](LeanQbeTest/T/KissatM7FidelityAuditX64.lean), [M7FidArm64](LeanQbeTest/T/KissatM7FidelityAuditArm64.lean), [PlainX64](LeanQbeLegacyTest/KissatM3PlainLegacyAuditX64.lean), [PlainArm64](LeanQbeLegacyTest/KissatM3PlainLegacyAuditArm64.lean) |
| Compiler and linker ([details](#compiler-optimization-and-lowering-pipeline)) | Optimization passes, inlining, `LinkedCert`, and linking of recursive and mutually recursive functions (`LinkRec`, `LinkScc`) | [Spec](LeanQbeTest/T/CompilerAuditSpec.lean), [X64](LeanQbeTest/T/CompilerAuditX64.lean), [Arm64](LeanQbeTest/T/CompilerAuditArm64.lean) |
| Lean 4 `LCNF` / `LeanLRC` lowering | Well-formedness (`Fn.Wf`) of code lowered from the Lean compiler's `LCNF` intermediate representation ([`LeanLCNF`](LeanQbe/T/LeanLCNF/), [`LeanLRC`](LeanQbe/T/LeanLRC/)) into `LeanQbe.T`, plus source-level `Func.wp` / `ModuleOk` proofs and concrete `Mem 64` non-vacuity for the C0 slab allocator/reference-counting ([`LcnfC0Rt`](LeanQbe/T/LeanLCNF/LcnfC0Rt.lean)), arbitrary-precision `Nat`/`Int` ([`LcnfC0BigNum`](LeanQbe/T/LeanLCNF/LcnfC0BigNum.lean)), and copy-on-write `ByteArray`/`Array` ([`LcnfC0Containers`](LeanQbe/T/LeanLCNF/LcnfC0Containers.lean)) runtime primitives | [Audit](LeanQbeTest/T/LcnfAudit.lean), [C0Rt](LeanQbeTest/T/LcnfC0RtTest.lean), [C0BigNum](LeanQbeTest/T/LcnfC0BigNumTest.lean), [C0Containers](LeanQbeTest/T/LcnfC0ContainersTest.lean) |
| LRAT proof checker | `lrat_check_bytes` returns `1` only for a well-formed DIMACS input whose CNF is unsatisfiable | [Spec](LeanQbeTest/T/LratAuditSpec.lean), [X64](LeanQbeTest/T/LratAuditX64.lean), [Arm64](LeanQbeTest/T/LratAuditArm64.lean) |
| Cryptography, bignum, and pointer code | ChaCha20 (SIMD), Curve25519 field arithmetic (`Bignum`), and union-find: source and machine-code proofs | [Spec](LeanQbeTest/T/WorkloadsAuditSpec.lean), [X64](LeanQbeTest/T/WorkloadsAuditX64.lean), [Arm64](LeanQbeTest/T/WorkloadsAuditArm64.lean) |
| C0 front end and proof tooling | `Func.wp` rules, the C0 elaborator and its well-formedness results, C0 step lemmas ([`C0Step`](LeanQbe/T/Logic/C0Step.lean), [`C0HeadStep`](LeanQbe/T/Logic/C0HeadStep.lean), [`C0Agrees`](LeanQbe/T/Logic/C0Agrees.lean)), and separation-style memory reasoning ([`MemLemmas`](LeanQbe/T/Logic/MemLemmas.lean), [`SepTree`](LeanQbe/T/Logic/SepTree.lean), [`SlabChain`](LeanQbe/T/Logic/SlabChain.lean), [`SlabLayoutElab`](LeanQbe/T/Logic/SlabLayoutElab.lean), [`ProofKit`](LeanQbe/T/Logic/ProofKit.lean)) | [Audit](LeanQbeTest/T/C0LogicAudit.lean), [ProofKit](LeanQbeTest/T/ProofKitTest.lean) |
| WebAssembly memory sandbox | Module validation (`validateModule`), software-fault-isolation bounds on linear memory (`WasmMemInv`), and preservation of the host's caller frame on x86-64 and AArch64 | [Spec](LeanQbeTest/T/WasmAuditSpec.lean), [X64](LeanQbeTest/T/WasmAuditX64.lean), [Arm64](LeanQbeTest/T/WasmAuditArm64.lean) |
| Bootstrapping compiler ([details](#bootstrapping-compiler)) | A small compiler written in Lean, lowered to `LeanQbe.T` and certified for x86-64, with soundness, serialization, and printer proofs | [Bootstrap0](LeanQbeBootstrap0Test/Bootstrap0Audit.lean), [Codec0](LeanQbeBootstrap0Test/Codec0Test.lean), [PrintDir0](LeanQbeBootstrap0Test/PrintDir0Test.lean), [PrintAsm0](LeanQbeTest/T/PrintAsm0Test.lean), [Sound0](LeanQbeBootstrap0Test/Sound0Test.lean), [StageC](LeanQbeBootstrap0Test/StageCTest.lean) |

To build the active audit files (also checked by [`scripts/check.sh`](scripts/check.sh)):

- In `LeanQbeTest/T/` for `Lcnf` containers and C0 extensions: [`LcnfC0ContainersTest`](LeanQbeTest/T/LcnfC0ContainersTest.lean) and [`C0ExtensionsTest`](LeanQbeTest/T/C0ExtensionsTest.lean).

```bash
lake build --wfail LeanQbeTest.T.KissatAuditSpec \
  LeanQbeTest.T.KissatM7FidelityAuditSpec \
  LeanQbeTest.T.KissatM7FidelityAuditX64 LeanQbeTest.T.KissatM7FidelityAuditArm64 \
  LeanQbeTest.T.CompilerAuditSpec LeanQbeTest.T.CompilerAuditX64 \
  LeanQbeTest.T.CompilerAuditArm64 LeanQbeTest.T.LcnfAudit \
  LeanQbeTest.T.LcnfC0RtTest LeanQbeTest.T.LcnfC0BigNumTest \
  LeanQbeTest.T.LcnfC0ContainersTest LeanQbeTest.T.C0ExtensionsTest \
  LeanQbeTest.T.LratAuditSpec LeanQbeTest.T.LratAuditX64 LeanQbeTest.T.LratAuditArm64 \
  LeanQbeTest.T.WorkloadsAuditSpec LeanQbeTest.T.WorkloadsAuditX64 \
  LeanQbeTest.T.WorkloadsAuditArm64 LeanQbeTest.T.C0LogicAudit \
  LeanQbeTest.T.ProofKitTest LeanQbeTest.T.WasmAuditSpec \
  LeanQbeTest.T.WasmAuditX64 LeanQbeTest.T.WasmAuditArm64 \
  LeanQbeTest.T.PrintAsm0Test LeanQbeBootstrap0Test.Bootstrap0Audit \
  LeanQbeBootstrap0Test.Codec0Test LeanQbeBootstrap0Test.PrintDir0Test \
  LeanQbeBootstrap0Test.Sound0Test LeanQbeBootstrap0Test.StageCTest
```

To build the optional `KissatPlain` dual SAT+UNSAT audit files as well:

```bash
lake build --wfail LeanQbeLegacyTest.KissatM3PlainLegacyAuditX64 \
  LeanQbeLegacyTest.KissatM3PlainLegacyAuditArm64
```

[`scripts/check.sh`](scripts/check.sh) is the repository's quality gate. It builds all active
targets with warnings treated as errors, and scans every tracked `.lean` file for `sorry`,
`admit`, non-meta `axiom` declarations, `@[implemented_by]`, `@[extern]`, `trustCompiler`, and
tactics that rely on native code evaluation (`native_decide`, `bv_decide`, `ofReduceBool`, and
similar). It also checks that no module imports both architectures, that the compiler's interface
and entry-point modules do not re-export proof modules (`*Lemmas*`) through public imports, and
that re-export ("hub") files are in sync ([`scripts/sync_hubs.py`](scripts/sync_hubs.py),
[`scripts/check_firewall.py`](scripts/check_firewall.py)). Finally, it checks the `#print axioms`
output of the active theorems listed in [`scripts/headlines.d`](scripts/headlines.d).

## Compiler optimization and lowering pipeline

This section follows the order in which passes run, as defined in [`Opt.lean`](LeanQbe/T/Opt.lean)
and [`Main.lean`](LeanQbe/T/Main.lean). Each pass is a function on `LeanQbe.T` functions together
with a theorem stating that it preserves `Func.wp` specifications (typically named `*_spec` or
`*_ok`). The headline theorems are restated in
[`CompilerAuditSpec.lean`](LeanQbeTest/T/CompilerAuditSpec.lean),
[`CompilerAuditX64.lean`](LeanQbeTest/T/CompilerAuditX64.lean), and
[`CompilerAuditArm64.lean`](LeanQbeTest/T/CompilerAuditArm64.lean).

### 1. Module-level inlining

[`Module.optInlinePolicy`](LeanQbe/T/MainInline.lean) (and its fixed-budget variant
`Module.optInline`) inlines calls to non-recursive callees across a whole module before any
per-function optimization runs.

- An `InlinePolicy` decides which call sites to inline. It combines a callee size budget with
  more generous limits for leaf functions and for callees with a single call site, a cap on the
  size of the resulting caller, limits on how much loop code may be duplicated, and an option to
  keep callees out of line when their call sites sit behind cold, single-sided guards (slow
  paths). A general-purpose policy is [`InlinePolicy.b5`](LeanQbe/T/Inline.lean), and the
  certified solver uses [`m7InlPolicy`](LeanQbe/T/Examples/Kissat/FullM7InlPolicy.lean), applied
  by [`Module.inlinePolicy`](LeanQbe/T/Inline.lean).
- Correctness: [`Module.inline_ok`](LeanQbe/T/InlineLemmas.lean),
  [`Module.optInlinePolicy_ok`](LeanQbe/T/MainInline.lean), and
  [`Module.optInline_ok`](LeanQbe/T/OptLemmas.lean).
- For large modules, the inlined module is computed once at elaboration time and recorded
  together with a kernel-checked equation relating it to `Module.optInlinePolicy`
  ([`inline_mod!`](LeanQbe/T/MainCertInline.lean)). A chunked variant
  ([`InlineChunk.lean`](LeanQbe/T/InlineChunk.lean),
  [`inline_chunk_base!`](LeanQbe/T/MainCertInlineChunk.lean), `inline_mod_chunk!`,
  `inline_mod_join!`) processes the module in pieces to bound memory use. Tests:
  [`InlineB5Test.lean`](LeanQbeTest/T/InlineB5Test.lean) and
  [`InlinePolicyB5Test.lean`](LeanQbeTest/T/InlinePolicyB5Test.lean).

### 2. SSA optimizations before legalization

[`Func.earlyOpt`](LeanQbe/T/Opt.lean) (correctness:
[`Func.earlyOpt_spec`](LeanQbe/T/OptLemmas.lean)) runs the following passes in order:

1. [`Func.fold`](LeanQbe/T/Fold.lean) — constant folding and algebraic simplification
   ([`FoldLemmas.lean`](LeanQbe/T/FoldLemmas.lean)).
2. [`Func.canon`](LeanQbe/T/Canon.lean) — ordering of commutative operands and reassociation
   of constant chains ([`CanonLemmas.lean`](LeanQbe/T/CanonLemmas.lean)).
3. [`Func.copy`](LeanQbe/T/Copy.lean) — copy propagation
   ([`CopyLemmas.lean`](LeanQbe/T/CopyLemmas.lean)).
4. [`Func.gvn`](LeanQbe/T/Gvn.lean) — global value numbering
   ([`GvnLemmas.lean`](LeanQbe/T/GvnLemmas.lean)).
5. `Func.copy`, then `Func.fold` again.
6. [`Func.ifOpt`](LeanQbe/T/IfOpt.lean) — if-conversion of branch diamonds into `select`
   instructions ([`Func.ifOptWith`](LeanQbe/T/IfOpt.lean);
   [`IfOptLemmas.lean`](LeanQbe/T/IfOptLemmas.lean)).
7. [`Func.simplifyGroupFast`](LeanQbe/T/Opt.lean) /
   [`Func.simplifyGroupPlan`](LeanQbe/T/SimplifyGroupPlan.lean) — control-flow
   simplification
   ([`SimplifyGroupPlanLemmas.lean`](LeanQbe/T/SimplifyGroupPlanLemmas.lean)).
8. [`Func.peelFast`](LeanQbe/T/Opt.lean) / [`Func.peel`](LeanQbe/T/Peel.lean) — loop
   peeling ([`PeelLemmas.lean`](LeanQbe/T/PeelLemmas.lean)).
9. [`Func.zeroPeelWith`](LeanQbe/T/ZeroPeel.lean) — widening of constant-fill loops and
   peeling of single-iteration loops
   ([`ZeroPeelLemmas.lean`](LeanQbe/T/ZeroPeelLemmas.lean),
   [`ZeroPeelLemmas1.lean`](LeanQbe/T/ZeroPeelLemmas1.lean)).
10. `Func.copy`, then `Func.fold` again.
11. [`Func.dceP`](LeanQbe/T/DceParam.lean) — dead-code elimination, including unused block
    parameters ([`DceParamLemmas.lean`](LeanQbe/T/DceParamLemmas.lean)).
12. `Func.renorm` — renumbering into a normalized form ([`Flat.lean`](LeanQbe/T/Flat.lean),
    [`FlatLemmas.lean`](LeanQbe/T/FlatLemmas.lean)).

### 3. Target legalization

[`Func.legal`](LeanQbe/T/Legal.lean) rewrites types and operations that the target does not
support directly into supported ones, while keeping multi-word arithmetic chains (add with carry
`addc`, subtract with borrow `subb`, widening multiply `umulw`) intact. It is checked by
[`LegalCheck3.lean`](LeanQbe/T/LegalCheck3.lean) and proved in
[`LegalLemmas.lean`](LeanQbe/T/LegalLemmas.lean).

### 4. SSA and loop optimizations after legalization

[`Func.lateOpt`](LeanQbe/T/Opt.lean), invoked from [`Fn.midStage`](LeanQbe/T/Main.lean)
(correctness: [`Func.lateOpt_spec`](LeanQbe/T/OptLemmas.lean)), runs four groups of passes in
order, renormalizing (`Func.renorm`) between groups:

1. [`Func.lateCorePre`](LeanQbe/T/Opt.lean): `Func.fold`, `Func.canon`,
   [`Func.divConst`](LeanQbe/T/DivConst.lean) (division by constants via multiplication and
   shifts; [`DivConstLemmas.lean`](LeanQbe/T/DivConstLemmas.lean)), `Func.copy`.
2. [`Func.lateCorePost`](LeanQbe/T/Opt.lean):
   [`Func.memLoad`](LeanQbe/T/MemLoad.lean) (load common-subexpression elimination and
   store-to-load forwarding; [`MemLoadLemmas.lean`](LeanQbe/T/MemLoadLemmas.lean)),
   `Func.gvn`, [`Func.assumeBits`](LeanQbe/T/AssumeBits.lean) (simplification using
   known-bits facts; [`AssumeBitsLemmas.lean`](LeanQbe/T/AssumeBitsLemmas.lean)),
   `Func.fold`.
3. [`Func.lateCfgPre`](LeanQbe/T/Opt.lean):
   [`Func.ifOptBits`](LeanQbe/T/IfOpt.lean) (if-conversion restricted to machine integer
   types; [`IfOptLemmas.lean`](LeanQbe/T/IfOptLemmas.lean)),
   `Func.simplifyGroupFast`, [`Func.deadLoadElim`](LeanQbe/T/Dce.lean) (removal of unused
   loads; [`DceLemmas.lean`](LeanQbe/T/DceLemmas.lean)),
   [`Func.assumeElim`](LeanQbe/T/MemLoad.lean) (removal of branches whose other arm halts;
   [`MemLoadLemmas.lean`](LeanQbe/T/MemLoadLemmas.lean)), `Func.fold`, `Func.gvn`.
4. [`Func.lateCfgPost`](LeanQbe/T/Opt.lean) and
   [`Func.lateLoopRotate`](LeanQbe/T/Opt.lean):
   [`Func.licm`](LeanQbe/T/Licm.lean) (loop-invariant code motion;
   [`LicmLemmas.lean`](LeanQbe/T/LicmLemmas.lean)), `Func.dceP`,
   [`Func.loopRotate`](LeanQbe/T/LoopRotate.lean) (loop rotation;
   [`LoopRotateLemmas.lean`](LeanQbe/T/LoopRotateLemmas.lean)),
   [`Func.mergeRets`](LeanQbe/T/Opt.lean) (merging of return blocks;
   [`OptLemmas.lean`](LeanQbe/T/OptLemmas.lean)).

### 5. Register allocation, instruction selection, and linking

The back end consists of an unverified hint analysis followed by verified lowering:

- **Hint analysis (untrusted).** [`Spill.hints`](LeanQbe/T/Spill.lean) and
  [`SpillFlags.lean`](LeanQbe/T/SpillFlags.lean) compute register-allocation and code-layout
  hints: spill placement and related options ([`Spill.Cfg`](LeanQbe/T/Spill.lean)),
  splitting of live ranges into hot and cold parts
  ([`tryEvictSplit`](LeanQbe/T/Spill.lean),
  [`SpillB5Test.lean`](LeanQbeTest/T/SpillB5Test.lean)), allocation of condition flags,
  addressing-mode folding (`[base + disp]` and scaled-index forms), and inversion of branches
  toward the hot path using execution weights. These hints are not part of the trusted base:
  every hint is re-checked during lowering, so an incorrect hint can cause compilation to fail
  or produce slower code, but cannot produce incorrect code.
- **Register allocation and lowering.** [`Rega.lowerFn`](LeanQbe/T/Rega.lean) (proved in
  [`RegaLemmas4.lean`](LeanQbe/T/RegaLemmas4.lean) and `RegaLemmas1.lean` to
  `RegaLemmas3.lean`) validates the hints and performs register allocation. It also removes
  redundant 32-to-64-bit zero extensions on x86-64
  ([`elideZext32?`](LeanQbe/T/Rega.lean), [`zeroUpper32Op`](LeanQbe/T/Target.lean);
  [`X64Zext32ElideTest.lean`](LeanQbeTest/T/X64Zext32ElideTest.lean)), fuses comparisons with
  conditional branches and lays out the hot successor as the fall-through
  ([`fuseJnzChoice`](LeanQbe/T/Rega.lean), [`jnzSetup`](LeanQbe/T/Rega.lean);
  [`InvertJnzTest.lean`](LeanQbeTest/T/InvertJnzTest.lean),
  [`InvertJnzArm64Test.lean`](LeanQbeTest/T/InvertJnzArm64Test.lean)), and sequentializes
  parallel moves (tested in [`FlagRaOptTest.lean`](LeanQbeTest/T/FlagRaOptTest.lean) and
  [`FlagRaOptArm64Test.lean`](LeanQbeTest/T/FlagRaOptArm64Test.lean)).
- **Instruction selection.** Selection of `[base + disp]` addressing, x86-64 scaled-index
  addressing `[base + idx*scale + disp]` ([`recordAddVarImm`](LeanQbe/T/Rega.lean),
  [`recordDef_elide_ok`](LeanQbe/T/RegaLemmas1.lean), example
  [`addrSibScaledDispFn`](LeanQbeTest/T/FlagRaOptTest.lean)), bit operations, conditional
  selects, stack frames, and SIMD instructions
  ([`Amd64/Isel.lean`](LeanQbe/T/Amd64/Isel.lean),
  [`Amd64/IselLemmas5.lean`](LeanQbe/T/Amd64/IselLemmas5.lean),
  [`Arm64/Isel.lean`](LeanQbe/T/Arm64/Isel.lean),
  [`Arm64/IselLemmas4.lean`](LeanQbe/T/Arm64/IselLemmas4.lean)).
- **Linking and certificates.** [`compileFn`](LeanQbe/T/Main.lean) and
  [`compileModule`](LeanQbe/T/Main.lean) drive the full pipeline
  ([`compileFn_correct`](LeanQbe/T/MainLemmas.lean)). Separately compiled pieces of a
  module can be linked compositionally
  ([`compileModule_append`](LeanQbe/T/MainLink.lean)); `LinkedCert` itself is built in
  [`MainCertCore.lean`](LeanQbe/T/MainCertCore.lean) and
  [`MainCertProof.lean`](LeanQbe/T/MainCertProof.lean). Recursive functions
  ([`link_rec_compiled`](LeanQbe/T/LinkRecLemmas.lean)) and groups of mutually recursive
  functions, i.e. strongly connected components of the call graph
  ([`link_scc_compiled`](LeanQbe/T/LinkSccLemmas2.lean),
  [`link_scc_static`](LeanQbe/T/LinkLfp.lean)), are supported.

## Verified Kissat SAT solver

The largest verified program in the repository is a C0 port of the
[Kissat 4.0.4](https://github.com/arminbiere/kissat) SAT solver. Two certified solvers illustrate
the main trade-off between full inprocessing and end-to-end SAT/UNSAT proofs:

| Solver | Functions | Scope | Machine-code guarantees (x86-64 & AArch64) |
|---|---:|---|---|
| **`FullM7Fidelity`** ([`FullM7FidelityAssembly.lean`](LeanQbe/T/Examples/Kissat/FullM7FidelityAssembly.lean)) | 413 | Certified Kissat 4.0.4 search and inprocessing baseline (fixed workspace and fuel); inlined via [`m7InlPolicy`](LeanQbe/T/Examples/Kissat/FullM7InlPolicy.lean) ([`FullM7FidelityInl.lean`](LeanQbe/T/Examples/Kissat/FullM7FidelityInl.lean)) | Closed `ModuleOk` (0 externs, 0 exits), UNSAT soundness, memory/register framing, and concrete UNSAT non-vacuity; runtime `kissat_check_model` on SAT |
| **`KissatPlain`** ([`Plain.lean`](LeanQbe/T/Examples/Kissat/Plain.lean)) | 59 | Pure CDCL reference solver (no inprocessing) | Closed `ModuleOk` (0 externs, 0 exits), **both SAT and UNSAT soundness**, memory/register framing, and concrete SAT & UNSAT non-vacuity |

- **`FullM7Fidelity`** (413 functions; current certified baseline while ongoing parity and compiler work advances): mirrors upstream Kissat 4.0.4's search orchestration,
  inprocessing schedule, preprocessing, and heuristics — CDCL with chronological backtracking,
  1-UIP analysis with recursive minimization and shrinking, focused/stable EMA search with
  target/best phase saving, 3-tier learned-clause management, chronological vivification,
  backbone, 2-literal hash congruence and gate extraction, BVE with forward subsumption, BVA
  factoring, watch-list GC/compaction, and random-walk local search. Its inlining policy
  `m7InlPolicy` is an untrusted performance heuristic checked by Lean's kernel via
  `Module.optInlinePolicy_ok`, so inlining adds no soundness assumptions beyond Lean's three
  standard axioms. Certified by
  [`kissatM7Fidelity_compiled_x64`](LeanQbe/T/Amd64/KissatM7Fidelity.lean) and
  [`kissatM7Fidelity_compiled_arm64`](LeanQbe/T/Arm64/KissatM7Fidelity.lean).
- **`KissatPlain`** (`Plain`, 59 functions): a compact pure-CDCL reference solver with blocking-literal
  watches, VSIDS/VMTF dual-mode search, phase saving, Luby/EMA restarts, clause reduction, and
  minimization/shrinking. Because it performs no equisatisfiable inprocessing, its machine-code
  proofs cover both SAT and UNSAT soundness directly on x86-64 and AArch64
  ([`Amd64/KissatPlain.lean`](LeanQbe/T/Amd64/KissatPlain.lean),
  [`Arm64/KissatPlain.lean`](LeanQbe/T/Arm64/KissatPlain.lean)). Its compiled certificates and
  audit files live in the optional `LeanQbeLegacyAmd64`, `LeanQbeLegacyArm64`, and
  `LeanQbeLegacyTest` libraries so routine builds stay focused on the main solver.

Both solvers export the same C entry point:

```c
uint64_t kissat_solve_bytes(const uint8_t *cnf_ptr, uint64_t cnf_len,
                            uint8_t *work_ptr, uint64_t work_len, uint64_t fuel);
/* Returns 20 = UNSAT, 10 = SAT (model left in the workspace), 0 = unknown. */
```

`cnf_ptr`/`cnf_len` is a DIMACS CNF file in memory, `work_ptr`/`work_len` is a caller-provided
workspace, and `fuel` bounds the number of solver steps. The solver returns `0` for malformed
input or when it runs out of fuel or workspace.

### Building and running the solver

Prerequisites: `elan` (which installs the toolchain named in `lean-toolchain`), a C compiler, and,
for AArch64 binaries on an x86-64 host, `aarch64-linux-gnu-gcc` and `qemu-aarch64`.

[`bench/kissat/build_solver.sh`](bench/kissat/build_solver.sh) builds the Lean code, emits the
assembly for the selected module and architecture, and links it with the command-line wrapper
[`bench/kissat/kissat_cli.c`](bench/kissat/kissat_cli.c):

```bash
# Certified FullM7Fidelity (413 fns, full Kissat 4.0.4) on x86-64 and AArch64
bash bench/kissat/build_solver.sh --module FullM7Fidelity --arch x64 -o /tmp/kissat-leanqbe
bash bench/kissat/build_solver.sh --module FullM7Fidelity --arch arm64 -o /tmp/kissat-leanqbe-arm64

# Certified KissatPlain (59 fns, pure CDCL, SAT+UNSAT proofs) on x86-64 and AArch64
bash bench/kissat/build_solver.sh --module Plain --arch x64 -o /tmp/kissat-leanqbe-plain
bash bench/kissat/build_solver.sh --module Plain --arch arm64 -o /tmp/kissat-leanqbe-plain-arm64

# Usage: kissat-leanqbe [--work-mb <MB>] [--fuel <N>] [-n|--no-model] <input.cnf | ->
printf 'p cnf 1 2\n1 0\n-1 0\n' | /tmp/kissat-leanqbe -
# s UNSATISFIABLE          (exit status 20)

printf 'p cnf 2 2\n1 2 0\n-1 0\n' | /tmp/kissat-leanqbe -
# s SATISFIABLE            (exit status 10)
# v -1 2 0

qemu-aarch64 -L /usr/aarch64-linux-gnu /tmp/kissat-leanqbe-arm64 input.cnf
```

The program prints a DIMACS status line (`s SATISFIABLE`, `s UNSATISFIABLE`, or `s UNKNOWN`) and
exits with status `10`, `20`, or `0` respectively; for satisfiable inputs it also prints the
model as `v ... 0` lines unless `-n` is given. Exit status `1` indicates a usage or I/O error.

The emitted assembly matches the `LinkedCert` only under the default build settings
(`--inline-max 0`). Passing `--inline-max <N>` (`N > 0`) or `--debug` alters the generated code
and prints a warning; such binaries are not covered by machine-code proofs.

Tests and audits:

```bash
# Builds x86-64 and AArch64 CLI binaries and checks exit codes, DIMACS models,
# -n/--no-model, stdin `-`, and workspace guard pages.
bash test/kissat/test_cli_solver.sh

# Specification and machine-code audit files for FullM7Fidelity (and optional KissatPlain).
lake build --wfail LeanQbeTest.T.KissatAuditSpec \
  LeanQbeTest.T.KissatM7FidelityAuditSpec \
  LeanQbeTest.T.KissatM7FidelityAuditX64 LeanQbeTest.T.KissatM7FidelityAuditArm64
lake build --wfail LeanQbeLegacyTest.KissatM3PlainLegacyAuditX64 \
  LeanQbeLegacyTest.KissatM3PlainLegacyAuditArm64
```

### What is proved

The audit files restate the main theorems with full types:

- **`FullM7Fidelity` (413 functions):**
  [`KissatM7FidelityAuditX64.lean`](LeanQbeTest/T/KissatM7FidelityAuditX64.lean) and
  [`KissatM7FidelityAuditArm64.lean`](LeanQbeTest/T/KissatM7FidelityAuditArm64.lean) audit the
  compiled x86-64 and AArch64 machine-code UNSAT soundness and non-vacuity theorems from
  [`Amd64/KissatM7Fidelity.lean`](LeanQbe/T/Amd64/KissatM7Fidelity.lean) and
  [`Arm64/KissatM7Fidelity.lean`](LeanQbe/T/Arm64/KissatM7Fidelity.lean)
  ([`scripts/headlines.d/kissat_m7_fidelity.txt`](scripts/headlines.d/kissat_m7_fidelity.txt)).
  [`KissatM7FidelityAuditSpec.lean`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean) audits the
  closed `ModuleOk` ([`m7f_mod_ok`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean)),
  inlined-module equivalence ([`m7f_inl_ok`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean)),
  source and inlined `Func.wp` UNSAT soundness
  ([`m7f_unsat`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean),
  [`m7f_inl_wp`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean)), and concrete 8,192 B UNSAT
  non-vacuity ([`m7f_nv`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean),
  [`m7f_inl_nv`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean);
  [`scripts/headlines.d/kissat_m7_fidelity_spec.txt`](scripts/headlines.d/kissat_m7_fidelity_spec.txt)).
- **`KissatPlain` (59 functions):**
  [`KissatM3PlainLegacyAuditX64.lean`](LeanQbeLegacyTest/KissatM3PlainLegacyAuditX64.lean) and
  [`KissatM3PlainLegacyAuditArm64.lean`](LeanQbeLegacyTest/KissatM3PlainLegacyAuditArm64.lean)
  audit the compiled x86-64 and AArch64 machine-code SAT and UNSAT soundness and non-vacuity
  theorems from [`Amd64/KissatPlain.lean`](LeanQbe/T/Amd64/KissatPlain.lean) and
  [`Arm64/KissatPlain.lean`](LeanQbe/T/Arm64/KissatPlain.lean)
  ([`scripts/headlines.d/kissat_plain_legacy.txt`](scripts/headlines.d/kissat_plain_legacy.txt)),
  backed by the source-level proof [`plainEnv_moduleOk`](LeanQbe/T/Examples/Kissat/PlainLemmas.lean).
- **Specification:** [`KissatAuditSpec.lean`](LeanQbeTest/T/KissatAuditSpec.lean) audits the
  DIMACS parser `parseDimacs` and the predicates `CNF.Unsat` and `CNF.Sat`.

#### Machine-code soundness

For **`FullM7Fidelity`** (`413` functions),
[`m7Fidelity_solve_bytes_unsat_x64`](LeanQbe/T/Amd64/KissatM7Fidelity.lean) and
[`m7Fidelity_solve_bytes_unsat_arm64`](LeanQbe/T/Arm64/KissatM7Fidelity.lean) (with
answer-only corollaries
[`kissat_m7Fidelity_x64_unsat_correct`](LeanQbe/T/Amd64/KissatM7Fidelity.lean) and
[`kissat_m7Fidelity_arm64_unsat_correct`](LeanQbe/T/Arm64/KissatM7Fidelity.lean)) state the
following over the compiled module (`kissatM7Fidelity_compiled_x64` /
`kissatM7Fidelity_compiled_arm64`). Take any executable containing the compiled code and any call
to `kissat_solve_bytes` that follows the platform ABI, passes DIMACS bytes and a workspace, has
enough stack, and has a caller frame `R`. Then execution terminates and returns to the caller
with:

- a result in `{0, 10, 20}` (in `rax` or `X0`);
- if the result is `20`: `∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`;
- callee-saved registers (`rbx`, `rbp`, `r12`–`r15` on x86-64; `X19`–`X29` on AArch64) and the
  stack pointer restored;
- the input bytes unchanged, the workspace and stack frame accounted for as separate memory
  regions, and the caller frame `R` untouched.

For **`KissatPlain`** (`59` functions),
[`solve_x64_correct`](LeanQbe/T/Amd64/KissatPlain.lean) and
[`solve_arm64_correct`](LeanQbe/T/Arm64/KissatPlain.lean) state the same ABI, framing, and
UNSAT guarantees over `plainCert`, and additionally prove that:

- if the result is `10`: `∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α`.

#### How SAT answers are checked

Kissat's inprocessing transformations (such as variable elimination) require reconstructing a model
of the original formula at the end of the search. Rather than formally verifying model
reconstruction, `FullM7Fidelity` checks its answer at runtime. In
[`FullM6Orch.lean`](LeanQbe/T/Examples/Kissat/FullM6Orch.lean), after model
reconstruction (`full_extend`) for a candidate SAT result, the entry point restores the original
variable count and calls `kissat_check_model`, which evaluates every clause of the original,
read-only DIMACS input and returns `10` only if every clause is satisfied (`0` otherwise). On
`FullM7Fidelity`, machine-code proofs are scoped to UNSAT soundness and memory/register framing,
while SAT outputs rely on this runtime check (and are also independently checked by the benchmark
harnesses). On `KissatPlain`, `kissat_check_model` is verified end-to-end as part of the
machine-code SAT soundness theorem.

#### Non-vacuity

A soundness theorem whose hypotheses can never be met would be vacuous. Each solver therefore
also proves concrete non-vacuous executions:

- **`FullM7Fidelity` (x86-64 & AArch64 UNSAT):**
  [`audit_m7f_x64_nv_closed`](LeanQbeTest/T/KissatM7FidelityAuditX64.lean) and
  [`audit_m7f_arm_nv_closed`](LeanQbeTest/T/KissatM7FidelityAuditArm64.lean) (with
  concrete-host witnesses [`m7Fidelity_x64_run_unsat`](LeanQbe/T/Amd64/KissatM7Fidelity.lean)
  and [`m7Fidelity_arm64_run_unsat`](LeanQbe/T/Arm64/KissatM7Fidelity.lean)) instantiate the
  machine-code theorems on `kissatM7Fidelity_compiled_{x64,arm64}.host` and exhibit executions
  returning `20`.
- **`KissatPlain` (x86-64 & AArch64 SAT & UNSAT):**
  [`audit_plain_x64_unsat_nonvacuous`](LeanQbeLegacyTest/KissatM3PlainLegacyAuditX64.lean),
  [`audit_plain_x64_sat_nonvacuous`](LeanQbeLegacyTest/KissatM3PlainLegacyAuditX64.lean),
  [`audit_plain_arm64_unsat_nonvacuous`](LeanQbeLegacyTest/KissatM3PlainLegacyAuditArm64.lean),
  and
  [`audit_plain_arm64_sat_nonvacuous`](LeanQbeLegacyTest/KissatM3PlainLegacyAuditArm64.lean)
  instantiate the machine-code theorems on `plainCert.host` with a 2048-byte workspace and
  `fuel = 16`, exhibiting concrete executions returning `20` on `"p cnf 1 2\n1 0\n-1 0\n"` and
  `10` on `"p cnf 1 1\n1 0\n"`.

#### Axioms

Every audited theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. The
repository contains no `sorry`, `admit`, non-meta `axiom`, `@[implemented_by]`, `@[extern]`,
`native_decide`, `bv_decide`, or `ofReduceBool`; [`scripts/check.sh`](scripts/check.sh) enforces
this for all tracked `.lean` files.

### Trusted computing base

To conclude that a certified `kissat-leanqbe` binary (built with default settings) prints
`s UNSATISFIABLE` only for unsatisfiable inputs — and for `KissatPlain`, `s SATISFIABLE` only for
satisfiable inputs — one must trust:

1. **The specification:** `Std.Sat.CNF.Unsat` and `Std.Sat.CNF.Sat` from the Lean standard library,
   and [`parseDimacs`](LeanQbe/T/Examples/LratBytes.lean), a pure ASCII DIMACS parser
   (checked on examples in [`KissatAuditSpec.lean`](LeanQbeTest/T/KissatAuditSpec.lean)).
   `parseDimacs` rejects headers and variable indices `>= 2^28`, the literal `-0`, missing headers,
   out-of-range variables, truncated clauses, and trailing tokens. Its dialect differs from some
   other parsers in a few details:
   - a lowercase `c` starts a comment that runs to the end of the line at any
     whitespace-delimited position, not only at the start of a line (uppercase `C`, or a `c`
     attached to digits such as `12c`, is rejected);
   - leading zeros are accepted (`00` terminates a clause, `01` denotes variable `1`);
   - an empty clause yields an unsatisfiable CNF, and `p cnf 0 0` yields the empty CNF;
   - SATLIB-style `%` end-of-file trailers are rejected.
2. **The Lean kernel** and the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
3. **The Kraken ISA semantics** for x86-64 and AArch64, in which the machine-code theorems are
   stated, together with the assembler and linker that turn the printed directives
   (`Kraken.X64.PrintATT`, `Kraken.AArch64.Print`) into an executable.
4. **The harness:** [`kissat_cli.c`](bench/kissat/kissat_cli.c), which reads the input, checks
   that `RLIMIT_STACK` is at least 65536 bytes, maps the input read-only and the workspace
   read-write between inaccessible guard pages, calls `kissat_solve_bytes`, and prints the result
   and model; plus the C runtime it links against. (For `FullM7Fidelity`, trusting SAT output also
   relies on the runtime `kissat_check_model` routine rather than a machine-code SAT proof.)

**Not in the TCB** (checked by the Lean kernel): the C0 solver sources, the C0 elaborator, the
inlining policy and its chunked materialization, every compiler pass (optimization, legalization,
register allocation, instruction selection, and linking), and all `Func.wp` proofs.

### Benchmarks and differential testing

To measure compiler overhead separately from algorithmic or data-layout differences, the
repository compares four x86-64 builds under an identical C driver
([`bench/kissat/bench_main.c`](bench/kissat/bench_main.c), which maps guard pages, checks
workspace slack, and independently verifies every SAT model against the input DIMACS):

- **`C1`**: upstream Kissat 4.0.4 compiled with `clang -O3`.
- **`C0-direct`**: the identical `FullM7Fidelity` C0 source extracted directly to C99
  ([`extract_c0_direct.py`](bench/kissat/extract_c0_direct.py), checked 1-to-1 against Lean via
  `--check-fns lean`) and compiled with `clang -std=c99 -O3 -fwrapv -fno-strict-aliasing`.
- **`C3b`**: the same module lowered to `LeanQbe.T` and emitted via `PrintCpp`
  (`-DTQBE_NATIVE_MEM`), compiled with `clang++ -std=c++20 -O3`.
- **`C4`**: the same module compiled by LeanQbe's certified x86-64 pipeline (`toATTAligned`, linked
  `-no-pie`), matching `kissatM7Fidelity_compiled_x64`.

The pairwise ratios isolate each stage: `C0-direct / C1` measures source and data-layout
differences vs upstream Kissat; `C3b / C0-direct` measures lowering to `LeanQbe.T` IR; `C4 / C3b`
measures LeanQbe's verified backend against `clang++ -O3`; and `C4 / C0-direct` is the total
verified-compiler overhead against `clang -O3` on the same C0 source.

Two benchmark scripts run this 4-way comparison:

- [`bench/kissat/compare_4way_min.py`](bench/kissat/compare_4way_min.py) (*recommended for
  independent reproduction*): a 245-line standard-library Python script that prints every compile
  and link command, invokes `Driver.compileFns` directly, runs CNFs sequentially in rotated order,
  verifies every SAT model, and prints timings, `.text` size, PAR-2, and pairwise ratios.
- [`bench/kissat/run_4way_stage1.py`](bench/kissat/run_4way_stage1.py): parallel runner over a
  140-CNF benchmark manifest, additionally checking bit-exact solver telemetry parity across
  `C0-direct`, `C3b`, and `C4`, and writing JSON/Markdown summaries.

```bash
# Minimal 245-line auditable 4-way comparison on any .cnf files, directory, or JSON manifest.
python3 bench/kissat/compare_4way_min.py --module FullM7Fidelity --c1 /path/to/kissat --timeout 30 a.cnf b.cnf
python3 bench/kissat/compare_4way_min.py --module FullM7Fidelity --c1 /path/to/kissat \
  --manifest /path/to/manifest.json --limit 6

# Full parallel 140-CNF 4-way benchmark (external CNFs and upstream Kissat are not committed in git).
python3 bench/kissat/run_4way_stage1.py --module FullM7Fidelity --jobs 8 \
  --manifest /path/to/manifest.json --c1-bin /path/to/kissat \
  --out-json /tmp/m7fid_4way.json --out-md /tmp/m7fid_4way.md

# Standalone direct C0-to-C99 extraction with 1-to-1 function-name check against Lean.
python3 bench/kissat/extract_c0_direct.py --target m7fidelity --out /tmp/m7fid_direct.c --check-fns lean
```

#### Certified `FullM7Fidelity` results (140 CNFs, x86-64)

Measured on Intel Xeon @ 2.60 GHz (`clang`/`clang++` 21.1.8) across 140 unique CNFs (`PV-35`: 35,
`Hard-24`: 24, `SV-21`: 21, `quick60`: 60; 30 s timeout, 60 s PAR-2 penalty, 20 ms geometric-mean
floor, 2B fuel, `--jobs 8`). There were 0 soundness or model errors, 0 verdict disagreements across
all four builds, 0 OOMs, and 135/135 bit-exact solver telemetry parity across `C0-direct`, `C3b`,
and `C4`. Common Wall columns cover the 133 instances solved by all four engines (`C1` and
`FullM7Fidelity` each solve 135/140, differing on 2 `quick60` instances each); pairwise ratios use
each pair's mutually solved subset:

| Engine | Solved (`S/U`) | Timeouts | Common Wall AM / GM (ms) | All-140 PAR-2 AM (s) | Linked `.text` (B) | Wall GM vs `C0-direct` | Wall GM vs `C3b` | Wall GM vs `C1` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `C1` (Kissat 4.0.4, `clang -O3`) | 135/140 (54S/81U) | 5 | 1280.0 / 286.1 | 3.589 | 373,722 | — | — | 1.00x |
| `C0-direct` (C0 -> C99, `clang -O3`) | 135/140 (55S/80U) | 5 | 1505.8 / 306.9 | 3.861 | 265,224 | 1.00x | — | 1.07x |
| `C3b` (`LeanQbe.T` -> C++20, `clang++ -O3`) | 135/140 (55S/80U) | 5 | 1600.6 / 336.3 | 3.970 | 227,928 | 1.10x | 1.00x | 1.18x |
| **`C4` (`FullM7Fidelity`, certified LeanQbe x64)** | **135/140** (55S/80U) | **5** | 1729.4 / 343.9 | **4.121** | 260,792 | **1.12x** | **1.02x** | **1.20x** |

Per-suite breakdown (Wall GM ratios; PAR-2 AM in seconds):

| Suite (`N`, 4-way common) | `C1` Solved | `C4` Solved | `C4` PAR-2 AM (s) | `C4 / C0-direct` | `C4 / C3b` | `C4 / C1` |
|---|---:|---:|---:|---:|---:|---:|
| `PV-35` (35, 35) | 35/35 | 35/35 | 1.845 | 1.15x | 1.11x | 1.28x |
| `Hard-24` (24, 24) | 24/24 | 24/24 | 0.752 | 1.13x | 0.98x | 1.04x |
| `SV-21` (21, 21) | 21/21 | 21/21 | 0.640 | 1.09x | 1.02x | 1.07x |
| `quick60` (60, 53) | 55/60 | 55/60 | 8.015 | 1.11x | 0.99x | 1.29x |
| **Overall** (140, 133) | **135/140** | **135/140** | **4.121** | **1.12x** | **1.02x** | **1.20x** |

Additional testing and differential-debugging harnesses live under [`bench/kissat/`](bench/kissat/)
and [`test/kissat/`](test/kissat/):

- [`test_cli_solver.sh`](test/kissat/test_cli_solver.sh): builds x86-64 and AArch64 (`qemu-aarch64`)
  CLI binaries and checks exit codes, DIMACS models, `-n`/`--no-model`, stdin `-`, and tight
  guarded workspaces.
- [`fuzz_oom_witness.py`](test/kissat/fuzz_oom_witness.py) with
  [`gen_inproc_cnfs.py`](bench/kissat/gen_inproc_cnfs.py) and
  [`gen_cnfs.py`](bench/kissat/gen_cnfs.py): fuzzes workspace capacity boundaries to test safe
  OOM return (`0`), zero SAT/UNSAT flips, and internal invariants
  ([`check_c3b_invariants.hpp`](test/kissat/check_c3b_invariants.hpp)).
- [`check_canaries.py`](bench/kissat/check_canaries.py),
  [`gen_canary_cnfs.py`](bench/kissat/gen_canary_cnfs.py),
  [`diff_telemetry.py`](bench/kissat/diff_telemetry.py), and
  [`diff_lockstep.py`](bench/kissat/diff_lockstep.py): synthetic UNSAT canary generators and
  differential telemetry/trace comparison tools against upstream Kissat 4.0.4.

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
  (`leanqbe0Mod0_legalSig`). [`leanqbe0Cert`](LeanQbe/T/Bootstrap0/Cert.lean) is a
  `LinkedCert` for all 124 functions on x86-64 (System V), with stack usage of at most 2048 bytes,
  assuming a stack bound of 64 bytes (`rtExtBounds0`) for each C runtime function it calls
  (`rtExterns`) and a single exit symbol `lcnf_panic`.
- **Stage B: compiler soundness, serialization, and printers.**
  - [`Sound0.lean`](LeanQbe/T/Bootstrap0/Sound0.lean) (audited in
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
| `LeanQbeTest/T/`, `LeanQbeBootstrap0Test/` | Active tests and standalone audit files (each imports at most one architecture) |
| `LeanQbeLegacyTest/` | Optional audit files for `KissatPlain` and earlier archived Kissat builds |
| `bench/kissat/` | Solver CLI wrapper, build script (`build_solver.sh`), 4-way benchmarks (`compare_4way_min.py`, `run_4way_stage1.py`), C0-to-C99 extractor (`extract_c0_direct.py`), and differential tools |
| `test/kissat/` | CLI solver tests (`test_cli_solver.sh`), OOM/witness fuzzer (`fuzz_oom_witness.py`), and test helpers |
| `scripts/` | [`check.sh`](scripts/check.sh), hub and import checks, theorem lists (`headlines.d/`) |
| `docs/reports/` | Design notes on individual components |
