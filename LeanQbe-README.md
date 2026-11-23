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
CDCL SAT solver: `FullM7Fidelity` (413 functions, matching upstream Kissat 4.0.4 search and
inprocessing), `FullM7Plus` (410 functions, a tuned variant), and `FullM6` (382 functions). All
three are certified down to x86-64 and AArch64 machine code for UNSAT soundness and concrete
non-vacuity, checking candidate SAT models at runtime via `kissat_check_model`. An earlier
270-function solver (`FullM5`) is kept alongside them because its machine-code proofs also cover
constructive SAT model extraction. On a 140-CNF benchmark suite (30 s limit), certified
`FullM7Fidelity` solves 135/140 instances (matching upstream Kissat 4.0.4's 135/140) at 1.12x
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
  is a self-contained 159-line Python script that prints every compile and link command, calls
  `Driver.compileFns` directly, runs all four configurations sequentially in rotated order, checks
  every SAT model, and reports timings and code sizes.

### Architecture overview

- **`LeanQbe.T`** ([`LeanQbe/T/`](LeanQbe/T/)): a typed SSA intermediate representation. Functions
  (`Func`) consist of basic blocks with typed values, explicit memory operations, and calls.
- **`Func.wp`** ([`WP.lean`](LeanQbe/T/WP.lean#L70)): a weakest-precondition semantics for
  `LeanQbe.T` functions. A function's specification is stated as a `Func.wp` precondition, and
  [`ModuleOk`](LeanQbe/T/Module.lean#L196) records that every function of a module meets its
  specification under the specifications of the functions it calls.
- **C0** ([`LeanQbe/T/Frontend/C0.lean`](LeanQbe/T/Frontend/C0.lean)): a subset of C (integer
  types, pointers, structs and unions, structured control flow, function calls, and a small
  preprocessor) parsed and elaborated into `LeanQbe.T` by a Lean macro. Most verified programs in
  this repository are written in C0 and proved against `Func.wp` specifications.
- **The compiler** ([`Main.lean`](LeanQbe/T/Main.lean)): performs whole-module inlining, pre- and
  post-legalization SSA/loop optimizations, target legalization, hint-validated register
  allocation, instruction selection, and compositional linking. Every pass is proved to preserve
  `Func.wp` specifications.
- **`LinkedCert`** ([`MainCertCore.lean`](LeanQbe/T/MainCertCore.lean#L207)): a kernel-checked
  certificate stating that the assembly directives produced for a whole module implement each
  source function's `Func.wp` specification under the Kraken x86-64 or AArch64 semantics.
  Combining a source-level `ModuleOk` proof with a `LinkedCert` yields an end-to-end theorem about
  the generated machine code.

## Verified components and audit files

For each verified component, the repository provides standalone *audit files* under
[`LeanQbeTest/T/`](LeanQbeTest/T/) and [`LeanQbeBootstrap0Test/`](LeanQbeBootstrap0Test/). Each
audit file restates the headline theorems with their full types, documents every hypothesis and
trusted assumption, and ends with `#print axioms` checks confirming that only `propext`,
`Classical.choice`, and `Quot.sound` are used. Architecture-specific audits live in separate files
so no module imports both `Kraken.X64` and `Kraken.AArch64`.

| Component | What is audited | Audit files |
|---|---|---|
| Kissat SAT solver ([details](#verified-kissat-sat-solver)) | `FullM7Fidelity` (413 fns), `FullM7Plus` (410 fns), and `FullM6` (382 fns): dual-arch x86-64 & AArch64 `LinkedCert` UNSAT soundness and concrete UNSAT non-vacuity (runtime `kissat_check_model` on SAT); `FullM5` (270 fns): dual-arch machine-code SAT (constructive model) and UNSAT soundness | [Spec](LeanQbeTest/T/KissatAuditSpec.lean), [M7FidX64](LeanQbeTest/T/KissatM7FidelityAuditX64.lean), [M7FidArm64](LeanQbeTest/T/KissatM7FidelityAuditArm64.lean), [M7FidSpec](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean), [M7PlusX64](LeanQbeTest/T/KissatM7PlusAuditX64.lean), [M7PlusArm64](LeanQbeTest/T/KissatM7PlusAuditArm64.lean), [M7PlusSpec](LeanQbeTest/T/KissatM7PlusAuditSpec.lean), [M6X64](LeanQbeTest/T/KissatM6AuditX64.lean), [M6Arm64](LeanQbeTest/T/KissatM6AuditArm64.lean), [M5SoundX64](LeanQbeTest/T/KissatM5SoundAuditX64.lean), [M5SoundArm64](LeanQbeTest/T/KissatM5SoundAuditArm64.lean) |
| Compiler and linker ([details](#compiler-optimization-and-lowering-pipeline)) | Optimization passes, inlining, `LinkedCert`, and linking of recursive and mutually recursive functions (`LinkRec`, `LinkScc`) | [Spec](LeanQbeTest/T/CompilerAuditSpec.lean), [X64](LeanQbeTest/T/CompilerAuditX64.lean), [Arm64](LeanQbeTest/T/CompilerAuditArm64.lean) |
| Lean 4 `LCNF` / `LeanLRC` lowering | Well-formedness (`Fn.Wf`) of code lowered from the Lean compiler's `LCNF` intermediate representation ([`LeanLCNF`](LeanQbe/T/LeanLCNF/), [`LeanLRC`](LeanQbe/T/LeanLRC/)) into `LeanQbe.T` | [Audit](LeanQbeTest/T/LcnfAudit.lean) |
| LRAT proof checker | `lrat_check_bytes` returns `1` only for a well-formed DIMACS input whose CNF is unsatisfiable | [Spec](LeanQbeTest/T/LratAuditSpec.lean), [X64](LeanQbeTest/T/LratAuditX64.lean), [Arm64](LeanQbeTest/T/LratAuditArm64.lean) |
| Cryptography, bignum, and pointer code | ChaCha20 (SIMD), Curve25519 field arithmetic (`Bignum`), and union-find: source and machine-code proofs | [Spec](LeanQbeTest/T/WorkloadsAuditSpec.lean), [X64](LeanQbeTest/T/WorkloadsAuditX64.lean), [Arm64](LeanQbeTest/T/WorkloadsAuditArm64.lean) |
| C0 front end and proof tooling | `Func.wp` rules, the C0 elaborator and its well-formedness results, C0 step lemmas (`C0HeadStep`, `C0Agrees`), and separation-style memory reasoning (`SepTree`, `SlabChain`, `C0Lens`) | [Audit](LeanQbeTest/T/C0LogicAudit.lean) |
| WebAssembly memory sandbox | Module validation (`validateModule`), software-fault-isolation bounds on linear memory (`WasmMemInv`), and preservation of the host's caller frame on x86-64 and AArch64 | [Spec](LeanQbeTest/T/WasmAuditSpec.lean), [X64](LeanQbeTest/T/WasmAuditX64.lean), [Arm64](LeanQbeTest/T/WasmAuditArm64.lean) |
| Bootstrapping compiler ([details](#bootstrapping-compiler)) | A small compiler written in Lean, lowered to `LeanQbe.T` and certified for x86-64, with soundness, serialization, and printer proofs | [Bootstrap0](LeanQbeBootstrap0Test/Bootstrap0Audit.lean), [Codec0](LeanQbeBootstrap0Test/Codec0Test.lean), [PrintDir0](LeanQbeBootstrap0Test/PrintDir0Test.lean), [PrintAsm0](LeanQbeTest/T/PrintAsm0Test.lean), [Sound0](LeanQbeBootstrap0Test/Sound0Test.lean), [StageC](LeanQbeBootstrap0Test/StageCTest.lean) |

To build the audit files (also built by `scripts/check.sh`):

```bash
lake build --wfail LeanQbeTest.T.KissatAuditSpec \
  LeanQbeTest.T.KissatM7FidelityAuditX64 LeanQbeTest.T.KissatM7FidelityAuditArm64 \
  LeanQbeTest.T.KissatM7FidelityAuditSpec \
  LeanQbeTest.T.KissatM7PlusAuditX64 LeanQbeTest.T.KissatM7PlusAuditArm64 \
  LeanQbeTest.T.KissatM7PlusAuditSpec \
  LeanQbeTest.T.KissatM6AuditX64 LeanQbeTest.T.KissatM6AuditArm64 \
  LeanQbeTest.T.KissatM5SoundAuditX64 LeanQbeTest.T.KissatM5SoundAuditArm64 \
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
similar). It also checks that no module imports both architectures, that the compiler's interface
and entry-point modules do not re-export proof modules (`*Lemmas*`) through public imports, and
that re-export ("hub") files are in sync ([`scripts/sync_hubs.py`](scripts/sync_hubs.py),
[`scripts/check_firewall.py`](scripts/check_firewall.py)). Finally, it checks the `#print axioms`
output of the theorems listed in [`scripts/headlines.d`](scripts/headlines.d).

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
  paths). A general-purpose policy is [`InlinePolicy.b5`](LeanQbe/T/Inline.lean#L377) (used for
  `FullM5`; later Kissat builds use `m6InlPolicy` and `m7InlPolicy`), applied by
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

1. [`Func.fold`](LeanQbe/T/Fold.lean#L868) — constant folding and algebraic simplification
   ([`FoldLemmas.lean#L2964`](LeanQbe/T/FoldLemmas.lean#L2964)).
2. [`Func.canon`](LeanQbe/T/Canon.lean#L254) — ordering of commutative operands and reassociation of constant chains
   ([`CanonLemmas.lean#L829`](LeanQbe/T/CanonLemmas.lean#L829)).
3. [`Func.copy`](LeanQbe/T/Copy.lean#L187) — copy propagation
   ([`CopyLemmas.lean#L849`](LeanQbe/T/CopyLemmas.lean#L849)).
4. [`Func.gvn`](LeanQbe/T/Gvn.lean#L259) — global value numbering
   ([`GvnLemmas.lean#L812`](LeanQbe/T/GvnLemmas.lean#L812)).
5. `Func.copy`, then `Func.fold` again.
6. [`Func.ifOpt`](LeanQbe/T/IfOpt.lean#L436) — if-conversion of branch diamonds into `select`
   instructions ([`Func.ifOptWith`](LeanQbe/T/IfOpt.lean#L431);
   [`IfOptLemmas.lean#L2395`](LeanQbe/T/IfOptLemmas.lean#L2395)).
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
   [`Func.ifOptBits`](LeanQbe/T/IfOpt.lean#L440) (if-conversion restricted to machine integer
   types; [`IfOptLemmas.lean#L2401`](LeanQbe/T/IfOptLemmas.lean#L2401)),
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

- **Hint analysis (untrusted).** [`Spill.hints`](LeanQbe/T/Spill.lean#L1988) and
  [`SpillFlags.lean`](LeanQbe/T/SpillFlags.lean) compute register-allocation and code-layout
  hints: spill placement and related options ([`Spill.Cfg`](LeanQbe/T/Spill.lean#L276)),
  splitting of live ranges into hot and cold parts
  ([`tryEvictSplit`](LeanQbe/T/Spill.lean#L653),
  [`SpillB5Test.lean`](LeanQbeTest/T/SpillB5Test.lean)), allocation of condition flags,
  addressing-mode folding (`[base + disp]` and scaled-index forms), and inversion of branches
  toward the hot path using execution weights. These hints are not part of the trusted base:
  every hint is re-checked during lowering, so an incorrect hint can cause compilation to fail
  or produce slower code, but cannot produce incorrect code.
- **Register allocation and lowering.** [`Rega.lowerFn`](LeanQbe/T/Rega.lean#L1902) (proved in
  [`RegaLemmas4.lean#L1061`](LeanQbe/T/RegaLemmas4.lean#L1061) and `RegaLemmas1.lean` to
  `RegaLemmas3.lean`) validates the hints and performs register allocation. It also removes
  redundant 32-to-64-bit zero extensions on x86-64
  ([`elideZext32?`](LeanQbe/T/Rega.lean#L737), [`zeroUpper32Op`](LeanQbe/T/Target.lean#L275);
  [`X64Zext32ElideTest.lean`](LeanQbeTest/T/X64Zext32ElideTest.lean)), fuses comparisons with
  conditional branches and lays out the hot successor as the fall-through
  ([`fuseJnzChoice`](LeanQbe/T/Rega.lean#L1419), [`jnzSetup`](LeanQbe/T/Rega.lean#L1438);
  [`InvertJnzTest.lean`](LeanQbeTest/T/InvertJnzTest.lean),
  [`InvertJnzArm64Test.lean`](LeanQbeTest/T/InvertJnzArm64Test.lean)), and sequentializes
  parallel moves (tested in `FlagRaOptTest.lean` and `FlagRaOptArm64Test.lean`).
- **Instruction selection.** Selection of `[base + disp]` addressing, x86-64 scaled-index
  addressing `[base + idx*scale + disp]` ([`recordAddVarImm`](LeanQbe/T/Rega.lean#L572),
  [`recordDef_elide_ok`](LeanQbe/T/RegaLemmas1.lean#L2301), example
  [`addrSibScaledDispFn`](LeanQbeTest/T/FlagRaOptTest.lean#L328)), bit operations, conditional
  selects, stack frames, and SIMD instructions
  ([`Amd64/Isel.lean`](LeanQbe/T/Amd64/Isel.lean),
  [`Amd64/IselLemmas5.lean#L1486`](LeanQbe/T/Amd64/IselLemmas5.lean#L1486),
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

The largest verified program in the repository is a C0 port of the
[Kissat 4.0.4](https://github.com/arminbiere/kissat) SAT solver. Four certified solver
configurations are available, each with kernel-checked x86-64 and AArch64 `LinkedCert`
machine-code certificates. Inlining policies (`m7InlPolicy`, `m6InlPolicy`, `InlinePolicy.b5`)
are untrusted performance heuristics checked by Lean's kernel via `Module.optInlinePolicy_ok`, so
inlining adds no assumptions and does not affect theorem strength.

| Configuration | Fns | Inlining policy | Machine-code guarantees (x86-64 & AArch64) |
|---|---:|---|---|
| **`FullM7Fidelity`** ([`FullM7FidelityAssembly.lean`](LeanQbe/T/Examples/Kissat/FullM7FidelityAssembly.lean#L336)) | 413 | [`m7InlPolicy`](LeanQbe/T/Examples/Kissat/FullM7InlPolicy.lean#L113) ([`FullM7FidelityInl.lean`](LeanQbe/T/Examples/Kissat/FullM7FidelityInl.lean#L62)) | `0`-hook `ModuleOk`, UNSAT soundness + concrete UNSAT non-vacuity; runtime `kissat_check_model` on SAT |
| **`FullM7Plus`** ([`FullM7PlusAssembly.lean`](LeanQbe/T/Examples/Kissat/FullM7PlusAssembly.lean#L250)) | 410 | [`m7InlPolicy`](LeanQbe/T/Examples/Kissat/FullM7InlPolicy.lean#L113) ([`FullM7PlusInl.lean`](LeanQbe/T/Examples/Kissat/FullM7PlusInl.lean#L62)) | `0`-hook `ModuleOk`, UNSAT soundness + concrete UNSAT non-vacuity; runtime `kissat_check_model` on SAT |
| **`FullM6`** ([`FullM6.lean`](LeanQbe/T/Examples/Kissat/FullM6.lean#L210)) | 382 | [`m6InlPolicy`](LeanQbe/T/Examples/Kissat/FullM6InlPolicy.lean#L107) ([`FullM6Inl.lean`](LeanQbe/T/Examples/Kissat/FullM6Inl.lean#L46)) | `0`-hook `ModuleOk`, UNSAT soundness + concrete UNSAT non-vacuity; runtime `kissat_check_model` on SAT |
| **`FullM5`** ([`FullM5.lean`](LeanQbe/T/Examples/Kissat/FullM5.lean#L354)) | 270 | [`InlinePolicy.b5`](LeanQbe/T/Inline.lean#L377) ([`FullM5InlB5.lean`](LeanQbe/T/Examples/Kissat/FullM5InlB5.lean#L31)) | `0`-hook `ModuleOk`, **SAT (constructive model) + UNSAT** soundness + concrete UNSAT non-vacuity |

#### Solver configurations

- **`FullM7Fidelity`** (413 functions): closely mirrors upstream Kissat 4.0.4's search
  orchestration, inprocessing schedule, preprocessing, and heuristics — CDCL with chronological
  backtracking, 1-UIP analysis with recursive minimization and shrinking, focused/stable EMA
  search with target/best phase saving, 3-tier learned-clause management, chronological
  vivification, backbone, 2-literal hash congruence and gate extraction, BVE with forward
  subsumption, BVA factoring, watch-list GC/compaction, and random-walk local search. Certified by
  [`kissatM7Fidelity_compiled_x64`](LeanQbe/T/Amd64/KissatM7Fidelity.lean#L34) and
  [`kissatM7Fidelity_compiled_arm64`](LeanQbe/T/Arm64/KissatM7Fidelity.lean#L34).
- **`FullM7Plus`** (410 functions): shares the same core engine as `FullM7Fidelity` with tuned
  preprocessing BVE, BVA tie-breaking/factoring, compaction, and vivification tiers. Certified by
  [`kissatM7Plus_compiled_x64`](LeanQbe/T/Amd64/KissatM7Plus.lean#L33) and
  [`kissatM7Plus_compiled_arm64`](LeanQbe/T/Arm64/KissatM7Plus.lean#L33).
- **`FullM6`** (382 functions): a smaller certified solver prior to the M7 gate/BVA/search
  additions, retained as a benchmark baseline. Certified by
  [`kissatM6_compiled_x64`](LeanQbe/T/Amd64/KissatM6.lean#L37) and
  [`kissatM6_compiled_arm64`](LeanQbe/T/Arm64/KissatM6.lean#L37).
- **`FullM5`** (270 functions): core CDCL with BVE, congruence, ternary HBR, probing, and
  embedded Kitten definition extraction; retained specifically because its machine-code proofs
  cover **both SAT (constructive model extraction) and UNSAT** on x86-64 and AArch64.

All four configurations export the same C entry point:

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
[`bench/kissat/kissat_cli.c`](bench/kissat/kissat_cli.c). All four certified configurations
(`FullM7Fidelity`, `FullM7Plus`, `FullM6`, and `FullM5`, the script default) build directly with
no extra flags.

```bash
# Certified FullM7Fidelity (413 fns, Kissat 4.0.4 fidelity) on x86-64 and AArch64
bash bench/kissat/build_solver.sh --module FullM7Fidelity --arch x64 -o /tmp/kissat-leanqbe-m7fid
bash bench/kissat/build_solver.sh --module FullM7Fidelity --arch arm64 -o /tmp/kissat-leanqbe-m7fid-arm64

# Certified FullM7Plus (410 fns) and FullM6 (382 fns)
bash bench/kissat/build_solver.sh --module FullM7Plus --arch x64 -o /tmp/kissat-leanqbe-m7plus
bash bench/kissat/build_solver.sh --module FullM6 --arch x64 -o /tmp/kissat-leanqbe-fullm6

# Certified FullM5 (270 fns, SAT+UNSAT machine-code proofs)
bash bench/kissat/build_solver.sh --module FullM5 --arch x64 -o /tmp/kissat-leanqbe-fullm5

# Usage: kissat-leanqbe [--work-mb <MB>] [--fuel <N>] [-n|--no-model] <input.cnf | ->
printf 'p cnf 1 2\n1 0\n-1 0\n' | /tmp/kissat-leanqbe-m7fid -
# s UNSATISFIABLE          (exit status 20)

printf 'p cnf 2 2\n1 2 0\n-1 0\n' | /tmp/kissat-leanqbe-m7fid -
# s SATISFIABLE            (exit status 10)
# v -1 2 0

qemu-aarch64 -L /usr/aarch64-linux-gnu /tmp/kissat-leanqbe-m7fid-arm64 input.cnf
```

The program prints a DIMACS status line (`s SATISFIABLE`, `s UNSATISFIABLE`, or `s UNKNOWN`) and
exits with status `10`, `20`, or `0` respectively; for satisfiable inputs it also prints the
model as `v ... 0` lines unless `-n` is given. Exit status `1` indicates a usage or I/O error.

The emitted assembly matches the `LinkedCert` only under the default build settings
(`--inline-max 0`). Passing `--inline-max <N>` (`N > 0`) or `--debug` alters the generated code
and prints a warning; such binaries are not covered by machine-code proofs.

Tests and proofs:

```bash
# Builds certified x86-64 and AArch64 CLI binaries and checks exit codes, DIMACS models,
# -n/--no-model, stdin `-`, and workspace guard pages.
bash test/kissat/test_cli_solver.sh

# Machine-code and specification audit files for all four certified Kissat configurations.
lake build --wfail LeanQbeTest.T.KissatAuditSpec \
  LeanQbeTest.T.KissatM7FidelityAuditX64 LeanQbeTest.T.KissatM7FidelityAuditArm64 \
  LeanQbeTest.T.KissatM7FidelityAuditSpec \
  LeanQbeTest.T.KissatM7PlusAuditX64 LeanQbeTest.T.KissatM7PlusAuditArm64 \
  LeanQbeTest.T.KissatM7PlusAuditSpec \
  LeanQbeTest.T.KissatM6AuditX64 LeanQbeTest.T.KissatM6AuditArm64 \
  LeanQbeTest.T.KissatM5SoundAuditX64 LeanQbeTest.T.KissatM5SoundAuditArm64
```

### What is proved

The audit files restate the main theorems with full types:

- **`FullM7Fidelity` (413 functions):**
  [`KissatM7FidelityAuditX64.lean`](LeanQbeTest/T/KissatM7FidelityAuditX64.lean) and
  [`KissatM7FidelityAuditArm64.lean`](LeanQbeTest/T/KissatM7FidelityAuditArm64.lean) audit the
  compiled x86-64 and AArch64 machine-code UNSAT soundness and non-vacuity theorems from
  [`Amd64/KissatM7Fidelity.lean`](LeanQbe/T/Amd64/KissatM7Fidelity.lean) and
  [`Arm64/KissatM7Fidelity.lean`](LeanQbe/T/Arm64/KissatM7Fidelity.lean) (34 audited theorems in
  [`scripts/headlines.d/kissat_m7_fidelity.txt`](scripts/headlines.d/kissat_m7_fidelity.txt)).
  [`KissatM7FidelityAuditSpec.lean`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean) audits the
  closed `0`-hook `ModuleOk`
  ([`m7f_mod_ok`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean#L113)), inlined-module equivalence
  ([`m7f_inl_ok`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean#L139)), source & inlined `Func.wp`
  UNSAT soundness ([`m7f_unsat`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean#L146),
  [`m7f_inl_wp`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean#L196)), and concrete 8,192 B UNSAT
  non-vacuity ([`m7f_nv`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean#L222),
  [`m7f_inl_nv`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean#L237); 24 entries in
  [`scripts/headlines.d/kissat_m7_fidelity_spec.txt`](scripts/headlines.d/kissat_m7_fidelity_spec.txt)).
- **`FullM7Plus` (410 functions):**
  [`KissatM7PlusAuditX64.lean`](LeanQbeTest/T/KissatM7PlusAuditX64.lean) and
  [`KissatM7PlusAuditArm64.lean`](LeanQbeTest/T/KissatM7PlusAuditArm64.lean) audit the compiled
  x86-64 and AArch64 machine-code UNSAT soundness and non-vacuity theorems from
  [`Amd64/KissatM7Plus.lean`](LeanQbe/T/Amd64/KissatM7Plus.lean) and
  [`Arm64/KissatM7Plus.lean`](LeanQbe/T/Arm64/KissatM7Plus.lean) (32 audited theorems in
  [`scripts/headlines.d/kissat_m7_plus.txt`](scripts/headlines.d/kissat_m7_plus.txt)).
  [`KissatM7PlusAuditSpec.lean`](LeanQbeTest/T/KissatM7PlusAuditSpec.lean) audits the closed
  `0`-hook `ModuleOk` ([`audit_m7p_mod_ok`](LeanQbeTest/T/KissatM7PlusAuditSpec.lean#L110)),
  inlined-module equivalence ([`audit_m7p_inl_ok`](LeanQbeTest/T/KissatM7PlusAuditSpec.lean#L136)),
  source & inlined `Func.wp` UNSAT soundness
  ([`audit_m7p_unsat`](LeanQbeTest/T/KissatM7PlusAuditSpec.lean#L142),
  [`audit_m7p_inl_wp`](LeanQbeTest/T/KissatM7PlusAuditSpec.lean#L192)), and concrete 8,192 B UNSAT
  non-vacuity ([`audit_m7p_nv`](LeanQbeTest/T/KissatM7PlusAuditSpec.lean#L217),
  [`audit_m7p_inl_nv`](LeanQbeTest/T/KissatM7PlusAuditSpec.lean#L232); 33 entries in
  [`scripts/headlines.d/kissat_m7_plus_spec.txt`](scripts/headlines.d/kissat_m7_plus_spec.txt)).
- **`FullM6` (382 functions):**
  [`KissatM6AuditX64.lean`](LeanQbeTest/T/KissatM6AuditX64.lean) and
  [`KissatM6AuditArm64.lean`](LeanQbeTest/T/KissatM6AuditArm64.lean) audit the compiled x86-64 and
  AArch64 machine-code UNSAT soundness and non-vacuity theorems from
  [`Amd64/KissatM6.lean`](LeanQbe/T/Amd64/KissatM6.lean) and
  [`Arm64/KissatM6.lean`](LeanQbe/T/Arm64/KissatM6.lean) (49 theorems in
  [`scripts/headlines.d/kissat_m6.txt`](scripts/headlines.d/kissat_m6.txt)).
- **`FullM5` (270 functions):**
  [`KissatM5SoundAuditX64.lean`](LeanQbeTest/T/KissatM5SoundAuditX64.lean) and
  [`KissatM5SoundAuditArm64.lean`](LeanQbeTest/T/KissatM5SoundAuditArm64.lean) (together with
  [`KissatM5AuditX64.lean`](LeanQbeTest/T/KissatM5AuditX64.lean) and
  [`KissatM5AuditArm64.lean`](LeanQbeTest/T/KissatM5AuditArm64.lean); 49 theorems in
  [`scripts/headlines.d/kissat_m5.txt`](scripts/headlines.d/kissat_m5.txt)) audit machine-code
  SAT (constructive model) and UNSAT soundness;
  [`KissatSatSoundTest.lean`](LeanQbeTest/T/KissatSatSoundTest.lean) includes a concrete source
  SAT non-vacuity witness.
- **Specification:** [`KissatAuditSpec.lean`](LeanQbeTest/T/KissatAuditSpec.lean) audits the
  DIMACS parser `parseDimacs` and the predicates `CNF.Unsat` and `CNF.Sat`.

#### Machine-code soundness

For **`FullM7Fidelity`** (`413` fns), **`FullM7Plus`** (`410` fns), and **`FullM6`** (`382` fns),
[`m7Fidelity_solve_bytes_unsat_x64`](LeanQbe/T/Amd64/KissatM7Fidelity.lean#L118) /
[`m7Fidelity_solve_bytes_unsat_arm64`](LeanQbe/T/Arm64/KissatM7Fidelity.lean#L117),
[`m7Plus_solve_bytes_unsat_x64`](LeanQbe/T/Amd64/KissatM7Plus.lean#L117) /
[`m7Plus_solve_bytes_unsat_arm64`](LeanQbe/T/Arm64/KissatM7Plus.lean#L116), and
[`m6_solve_bytes_unsat_x64`](LeanQbe/T/Amd64/KissatM6.lean#L114) /
[`m6_solve_bytes_unsat_arm64`](LeanQbe/T/Arm64/KissatM6.lean#L113) (with answer-only corollaries
[`kissat_m7Fidelity_x64_unsat_correct`](LeanQbe/T/Amd64/KissatM7Fidelity.lean#L174),
[`kissat_m7Fidelity_arm64_unsat_correct`](LeanQbe/T/Arm64/KissatM7Fidelity.lean#L172),
[`kissat_m7Plus_x64_unsat_correct`](LeanQbe/T/Amd64/KissatM7Plus.lean#L173),
[`kissat_m7Plus_arm64_unsat_correct`](LeanQbe/T/Arm64/KissatM7Plus.lean#L171),
[`kissat_m6_x64_unsat_correct`](LeanQbe/T/Amd64/KissatM6.lean#L171), and
[`kissat_m6_arm64_unsat_correct`](LeanQbe/T/Arm64/KissatM6.lean#L169)) state the following over
the compiled module (`kissatM7Fidelity_compiled_{x64,arm64}`, `kissatM7Plus_compiled_{x64,arm64}`,
or `kissatM6_compiled_{x64,arm64}`). Take any executable containing the compiled code and any call
to `kissat_solve_bytes` that follows the platform ABI, passes DIMACS bytes and a suitably aligned
workspace, has enough stack, and has a caller frame `R`. Then execution terminates and returns to
the caller with:

- a result in `{0, 10, 20}` (in `rax` or `X0`);
- if the result is `20`: `∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`;
- callee-saved registers (`rbx`, `rbp`, `r12`–`r15` on x86-64; `X19`–`X29` on AArch64) and the
  stack pointer restored;
- the input bytes unchanged, the workspace and stack frame accounted for as separate memory
  regions, and the caller frame `R` untouched.

Per project scope, the `FullM7Fidelity`, `FullM7Plus`, and `FullM6` machine-code theorems certify
UNSAT soundness and memory/register framing and omit machine-code SAT model-check proofs.

For **`FullM5`** (`270` fns), [`m5_solve_bytes_model_x64`](LeanQbe/T/Amd64/KissatM5Sound.lean#L89)
and [`m5_solve_bytes_model_arm64`](LeanQbe/T/Arm64/KissatM5Sound.lean#L88) (together with the
UNSAT-only theorems [`m5_solve_bytes_unsat_x64`](LeanQbe/T/Amd64/KissatM5.lean#L88) and
[`m5_solve_bytes_unsat_arm64`](LeanQbe/T/Arm64/KissatM5.lean#L88)) state the same ABI, framing,
and UNSAT guarantees for the compiled 270-function module (`kissatM5_compiled_{x64,arm64}`), and
additionally prove that:

- if the result is `10`: `∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ (∃ α, cnf.Sat α) ∧
  cnf.Sat (readModelFromWork st.data.dmem work_ptr)`, i.e. the assignment stored in the workspace
  satisfies the input formula.

#### How SAT answers are checked

Kissat's inprocessing transformations (such as variable elimination) require reconstructing a model
of the original formula at the end of the search. Rather than verifying that reconstruction, the
solver checks its result. In [`FullM5Orch.lean`](LeanQbe/T/Examples/Kissat/FullM5Orch.lean#L643)
and [`FullM6Orch.lean`](LeanQbe/T/Examples/Kissat/FullM6Orch.lean#L773-L777) (reused by
`FullM7Plus` and `FullM7Fidelity`), after model reconstruction (`full_extend`) for a candidate SAT
result, the entry point restores the original variable count and calls `kissat_check_model`, which
evaluates every clause of the original, read-only DIMACS input and returns `10` only if every
clause is satisfied (`0` otherwise). For `FullM5`, this runtime check is proved end-to-end against
[`readModelFromWork`](LeanQbe/T/Examples/Kissat/FullSatSound.lean#L102) via
[`kissat_solve_bytes_m5_model_wp`](LeanQbe/T/Examples/Kissat/FullSatSound.lean#L838) and
[`ModuleOk.respec_tail`](LeanQbe/T/Examples/Kissat/FullSatSound.lean#L42), and lifted to x86-64
and AArch64 machine code in `KissatM5Sound.lean`. For `FullM7Fidelity`, `FullM7Plus`, and `FullM6`,
`kissat_check_model` runs at runtime and is checked by the CLI and benchmark harnesses, while
machine-code proofs remain scoped to UNSAT soundness and non-vacuity.

#### Non-vacuity

A soundness theorem whose hypotheses can never be met would be vacuous. Each certified solver
therefore also proves that its hypotheses are satisfiable and that non-trivial executions exist:

- Machine code (`FullM7Fidelity` UNSAT):
  [`audit_m7f_x64_nv_closed`](LeanQbeTest/T/KissatM7FidelityAuditX64.lean#L141) and
  [`audit_m7f_arm_nv_closed`](LeanQbeTest/T/KissatM7FidelityAuditArm64.lean#L139) (with
  concrete-host witnesses [`m7Fidelity_x64_run_unsat`](LeanQbe/T/Amd64/KissatM7Fidelity.lean#L300)
  and [`m7Fidelity_arm64_run_unsat`](LeanQbe/T/Arm64/KissatM7Fidelity.lean#L298)) instantiate the
  machine-code theorems on `kissatM7Fidelity_compiled_{x64,arm64}.host` and exhibit executions
  returning `20`.
- Machine code (`FullM7Plus` UNSAT):
  [`audit_m7p_x64_nv_closed`](LeanQbeTest/T/KissatM7PlusAuditX64.lean#L139) and
  [`audit_m7p_arm_nv_closed`](LeanQbeTest/T/KissatM7PlusAuditArm64.lean#L137) (with
  concrete-host witnesses [`m7Plus_x64_run_unsat`](LeanQbe/T/Amd64/KissatM7Plus.lean#L299) and
  [`m7Plus_arm64_run_unsat`](LeanQbe/T/Arm64/KissatM7Plus.lean#L297)).
- Machine code (`FullM6` UNSAT):
  [`audit_m6_x64_nv_closed`](LeanQbeTest/T/KissatM6AuditX64.lean#L138) and
  [`audit_m6_arm_nv_closed`](LeanQbeTest/T/KissatM6AuditArm64.lean#L149) (with concrete-host
  witnesses [`m6_x64_run_unsat`](LeanQbe/T/Amd64/KissatM6.lean#L264) and
  [`m6_arm64_run_unsat`](LeanQbe/T/Arm64/KissatM6.lean#L273)).
- Machine code (`FullM5` UNSAT):
  [`audit_m5_x64_nv_closed`](LeanQbeTest/T/KissatM5AuditX64.lean#L137) and
  [`audit_m5_arm_nv_closed`](LeanQbeTest/T/KissatM5AuditArm64.lean#L135).
- Source level (`FullM5` SAT): [`m5_sat_nonvacuous`](LeanQbe/T/Examples/Kissat/FullM5SatNv.lean#L2721)
  (audited as [`audit_m5_sat_nv`](LeanQbeTest/T/KissatSatSoundTest.lean#L151)) runs the solver on
  `"p cnf 1 1\n1 0\n"` under `Func.wp` with a 4096-byte workspace and `fuel = 16`, showing that it
  returns `10` with a satisfying assignment readable via `readModelFromWork`.

#### Axioms

Every audited theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. The
repository contains no `sorry`, `admit`, non-meta `axiom`, `@[implemented_by]`, `@[extern]`,
`native_decide`, `bv_decide`, or `ofReduceBool`; [`scripts/check.sh`](scripts/check.sh) enforces
this for all tracked `.lean` files.

### Trusted computing base

To conclude that a certified `kissat-leanqbe` binary (`FullM7Fidelity`, `FullM7Plus`, `FullM6`, or
`FullM5`, built with default settings) prints `s UNSATISFIABLE` only for unsatisfiable inputs, and
`s SATISFIABLE` with a satisfying model only for satisfiable inputs (proved down to machine code
for `FullM5`, and checked at runtime by `kissat_check_model` for `FullM7Fidelity`, `FullM7Plus`,
and `FullM6`), one must trust:

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
2. **The Lean kernel** and the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
3. **The Kraken ISA semantics** for x86-64 and AArch64, in which the machine-code theorems are
   stated, together with the assembler and linker that turn the printed directives
   (`Kraken.X64.PrintATT`, `Kraken.AArch64.Print`) into an executable.
4. **The harness:** [`kissat_cli.c`](bench/kissat/kissat_cli.c), which reads the input, checks
   that `RLIMIT_STACK` is at least 65536 bytes, maps the input read-only and the workspace
   read-write between inaccessible guard pages, calls `kissat_solve_bytes`, and prints the result
   and model; plus the C runtime it links against. (For `FullM7Fidelity`, `FullM7Plus`, and
   `FullM6`, trusting SAT output also relies on the runtime `kissat_check_model` routine rather
   than a machine-code SAT proof.)

**Not in the TCB** (checked by the Lean kernel for all four certified binaries): the C0 solver
sources, the C0 elaborator, the inlining policy and its chunked materialization, every compiler
pass (optimization, legalization, register allocation, instruction selection, and linking), and
all `Func.wp` proofs.

### Benchmarks and differential testing

The repository includes a benchmarking and differential-testing suite under
[`bench/kissat/`](bench/kissat/) and [`test/kissat/`](test/kissat/) to isolate compiler overhead,
check bit-exact solver parity across backends, and guard against regressions:

| Harness | Suite / Corpus | What it checks | Supported modules |
|---|---|---|---|
| [`compare_4way_min.py`](bench/kissat/compare_4way_min.py) | Any positional `.cnf` files, `--cnf-dir`, or `--manifest` (`--limit N`) | Self-contained 159-line 4-way benchmark: prints every compile/link command, invokes `Driver.compileFns` directly, runs sequentially in rotated order, checks `C1` DIMACS models + `bench_main.c` models/slack + 0 disagreements, reports AM/GM/PAR-2/`.text` | `FullM7Fidelity`, `FullM7Plus`, `FullM6` (default), `FullM5` |
| [`run_4way_stage1.py`](bench/kissat/run_4way_stage1.py) | Stage-1 140 unique CNFs (`PV-35`: 35 [13S/22U], `Hard-24`: 24 [4S/20U], `SV-21`: 21 [13S/8U], `quick60`: 60 [28S/32U]; 58 SAT / 82 UNSAT) | Parallel Stage-1 4-way harness (`C1` vs `C0-direct` vs `C3b` vs `C4`), 0 verdict disagreements, SAT DIMACS model verification, 35-key bit-exact C0 telemetry parity, JSON/Markdown reports, `.text` & static non-NOP instruction counts | `FullM7Fidelity`, `FullM7Plus`, `FullM6` (default), `FullM5` |
| [`test_cli_solver.sh`](test/kissat/test_cli_solver.sh) | 10 built-in SAT/UNSAT/UNKNOWN/guard-page CNFs (incl. 32-var 128-clause canary) | Certified x86-64 & AArch64 (`qemu-aarch64`) CLI builds, certification gating, DIMACS `v ... 0` model validation, `-n`/`--no-model`, stdin `-`, tight 1 MB guarded workspace | Certified CLI binaries |
| [`check_canaries.py`](bench/kissat/check_canaries.py) + [`gen_canary_cnfs.py`](bench/kissat/gen_canary_cnfs.py) | 34 base / 40 total (`--include-c11`) mathematically UNSAT canaries across 10–11 stress families | Ratchet checks against [`canary_baseline.json`](bench/kissat/canary_baseline.json), bit-identical `C4 == C3b` work parity, regression ceilings vs `C1` | `FullM6` or arbitrary `--c3b-gen-hpp` |
| [`diff_telemetry.py`](bench/kissat/diff_telemetry.py) + [`diff_lockstep.py`](bench/kissat/diff_lockstep.py) + [`run_c11_guardrails.sh`](bench/kissat/run_c11_guardrails.sh) | Canary & custom CNF suites (`bench_main.c` `--full-telemetry-m2` / `--extended-telemetry-m2`) | 26 standard + 31 extended telemetry metrics vs upstream Kissat 4.0.4 (`C1`); lockstep event-trace first-divergence bisection (`DEC`, `CONFL`, `LEARN`, `RST`, `MODE`, `RED`, `INPROC`, `UNIT0`, `END`) | Any C0 solver build (`C3b` / `C4`) |
| [`fuzz_oom_witness.py`](test/kissat/fuzz_oom_witness.py) + [`gen_inproc_cnfs.py`](bench/kissat/gen_inproc_cnfs.py) + [`gen_cnfs.py`](bench/kissat/gen_cnfs.py) | 316 inprocessing stress CNFs (9 families) + 45 structured CNFs | Workspace capacity boundary fuzzing, safe OOM return (`0`), zero SAT/UNSAT flips, structural invariants ([`check_c3b_invariants.hpp`](test/kissat/check_c3b_invariants.hpp)) | `C3b` / `C4` builds |

#### Reproducible 4-way performance benchmark

Two companion scripts evaluate the same four x86-64 corners under an identical C driver
([`bench/kissat/bench_main.c`](bench/kissat/bench_main.c) with `PROT_NONE` guard pages, `0xAA`
slack checks, and full DIMACS clause verification):

- **[`bench/kissat/compare_4way_min.py`](bench/kissat/compare_4way_min.py)** (*recommended for
  independent auditing*): a `159`-line, plain-stdlib Python script that prints every exact compile
  and link command, invokes `Driver.compileFns` directly (matching `LinkedCert.code` with no
  parallel wrapper), runs CNFs sequentially in rotated order `(i + j) % 4` with zero concurrency
  noise, independently checks every `C1` SAT model in Python, and prints per-CNF timings,
  `size .text`, PAR-2, and pairwise ratios.
- **[`bench/kissat/run_4way_stage1.py`](bench/kissat/run_4way_stage1.py)**: the full parallel
  Stage-1 (`140`-CNF) harness adding `--jobs N` concurrency, per-suite breakdowns, 35-key
  bit-exact C0 telemetry parity verification, and structured JSON/Markdown report generation.

The four corners separate algorithm/data-layout differences, IR lowering, and verified backend code
generation:

- **`C1`**: upstream Kissat 4.0.4 compiled with `clang -O3`.
- **`C0-direct`**: the identical C0 solver source extracted directly to C99
  ([`extract_c0_direct.py`](bench/kissat/extract_c0_direct.py) /
  [`build_c0_direct.sh`](bench/kissat/build_c0_direct.sh), checked 1-to-1 against Lean via
  `--check-fns lean`) and compiled with `clang -std=c99 -O3 -fwrapv -fno-strict-aliasing`.
- **`C3b`**: the same module lowered to `LeanQbe.T` and emitted via `PrintCpp`
  (`-DTQBE_NATIVE_MEM`), compiled with `clang++ -std=c++20 -O3`.
- **`C4`**: the same module compiled by LeanQbe's certified x86-64 pipeline (`toATTAligned`, linked
  `-no-pie`), matching the kernel-checked `LinkedCert` assembly for `FullM7Fidelity`,
  `FullM7Plus`, `FullM6`, and `FullM5`.

Pairwise ratios decompose the end-to-end runtime gap (`C4 / C1`) into three orthogonal stages:

1. **`C0-direct / C1`** — C0 source & SoA data-layout differences vs upstream Kissat 4.0.4 (`clang -O3` on both).
2. **`C3b / C0-direct`** — `C0 -> LeanQbe.T -> PrintCpp` IR lowering overhead (`clang++ -O3` vs `clang -O3`).
3. **`C4 / C3b`** — verified LeanQbe backend codegen (optimization, register allocation, instruction selection) vs `clang++ -O3`.
4. **`C4 / C0-direct`** — total verified compiler overhead vs `clang -O3` on identical C0 source (`≈ (C3b / C0-direct) × (C4 / C3b)`).

Every C0-derived Stage-1 run verifies **35-key bit-exact telemetry parity**
(`C0-direct == C3b == C4` via `--full-telemetry-m2`): `status`, `conflicts`, `learned_lits`,
`min_removed`, `num_irred`, `num_redundant`, `num_binary`, `switched`, `search_ticks`, `rephased`,
`reductions`, `tier1`, `tier2`, `restarts`, `oom`, `max_vars`, `cur_vars`, `unassigned`, `otfs`,
`eager_sub`, `probings`, `eliminations`, `elim_bound`, `hbr`, `trans`, `viv`, `subst`, `cong`,
`sweep`, `bve`, `bce`, `bva`, `walks`, `last_probe_ticks`, and `last_elim_ticks`.

```bash
# Minimal 159-line auditable 4-way comparison on any .cnf files, directory, or Stage-1 manifest.
# Prints every exact compile/link command and runs sequentially in rotated order with zero contention.
python3 bench/kissat/compare_4way_min.py --module FullM7Fidelity --c1 /path/to/kissat --timeout 30 a.cnf b.cnf
python3 bench/kissat/compare_4way_min.py --module FullM7Fidelity --c1 /path/to/kissat \
  --manifest /path/to/manifest_stage1.json --limit 6

# Full parallel Stage-1 (140-CNF) 4-way benchmark + 35-key bit-exact telemetry parity.
# Pass --manifest <stage1.json> and --c1-bin <kissat-4.0.4> (or set STAGE1_MANIFEST / KISSAT_C1_BIN),
# since external Stage-1 CNF benchmarks and the upstream Kissat binary are not committed in git.
python3 bench/kissat/run_4way_stage1.py --module FullM7Fidelity --jobs 8 \
  --out-json /tmp/m7fid_4way.json --out-md /tmp/m7fid_4way.md
python3 bench/kissat/run_4way_stage1.py --module FullM7Plus --jobs 8 \
  --out-json /tmp/m7plus_4way.json --out-md /tmp/m7plus_4way.md
python3 bench/kissat/run_4way_stage1.py --module FullM6 --jobs 8 \
  --out-json /tmp/m6_4way.json --out-md /tmp/m6_4way.md

# Standalone direct C0-to-C99 extraction with 1-to-1 ordered function-name parity check against Lean
python3 bench/kissat/extract_c0_direct.py --target m7fidelity --out /tmp/m7fid_direct.c --check-fns lean
python3 bench/kissat/extract_c0_direct.py --target m7plus --out /tmp/m7plus_direct.c --check-fns lean
python3 bench/kissat/extract_c0_direct.py --target m6 --out /tmp/m6_direct.c --check-fns lean
```

##### Summary across certified solvers (Stage-1 140 CNFs, x86-64)

Measured on Intel Xeon @ 2.60 GHz (`48` vCPUs, `clang`/`clang++` 21.1.8) across the `140` unique
Stage-1 CNFs (`PV-35`: 35, `Hard-24`: 24, `SV-21`: 21, `quick60`: 60), `30.0 s` timeout (`60.0 s`
PAR-2 penalty), `20.0 ms` GM floor, `2,000,000,000` fuel, `--jobs 8`, and interleaved per-CNF
engine order. All three certified runs recorded **0** soundness/model errors, **0** cross-solver
disagreements, **0** OOMs, and **100%** bit-exact 35-key C0 telemetry parity (`C0-direct == C3b ==
C4`):

| Certified `C4` target (Fns, commit) | Solved (`S/U`) | `C4 / C0-direct` (W-GM / I-GM) | `C4 / C3b` (W-GM / I-GM) | `C4 / C1` (W-GM / I-GM) | All-140 PAR-2 AM (`vs C1`) | Linked `.text` (B) / Non-NOP Insns | 35-key parity (`0` diffs) |
|---|---:|---|---|---|---|---:|---:|
| `C1` (Kissat 4.0.4, `clang -O3`, ref) | `135/140` (`54S/81U`) | — | — | `1.0000x / 1.0000x` | `3.563–3.589 s` (`1.00x`) | `373,722 / 92,883` | Reference |
| **`FullM7Fidelity`** (`413`, `e6b2c31d`) | **`135/140`** (`55S/80U`) | **`1.1216x / 1.1442x`** | **`1.0236x / 1.0557x`** | **`1.2020x / 1.2397x`** | **`4.121 s` (`1.1483x`)** | `260,792 / 63,876` | `135/135` |
| **`FullM7Plus`** (`410`, `e6b2c31d`) | `132/140` (`52S/80U`) | **`1.1163x / 1.1611x`** | **`1.0654x / 1.0926x`** | **`1.1211x / 1.1387x`** | `4.820 s` (`1.3529x`) | `259,208 / 63,488` | `132/132` |
| **`FullM6`** (`382`, `b200244a`) | `131/140` (`51S/80U`) | **`1.1025x / 1.1337x`** | **`1.0599x / 1.0771x`** | **`1.1723x / 1.1856x`** | `5.502 s` (`1.5412x`) | `206,024 / 49,848` | `130/130` |

*In uncontended sequential checks via `compare_4way_min.py --limit 6` on `e6b2c31d` (`6/6` common,
`0` errors/disagreements), `FullM7Fidelity` measures `C4 / C0-direct = 1.0991x`, `C4 / C3b =
0.9511x`, `C4 / C1 = 1.2475x`, and `FullM7Plus` measures `C4 / C0-direct = 1.0957x`, `C4 / C3b =
1.0092x`, `C4 / C1 = 1.7102x` (`C0-direct / C1 = 1.5608x` on that 6-CNF prefix).*

##### Certified `FullM7Fidelity` (`413` fns, `kissatM7Fidelity_compiled_x64`) — Stage-1 140-CNF breakdown

Measured on commit `e6b2c31d` (uncontended 48-vCPU host, start loadavg `6.08, 5.11, 3.56`, end
`4.05, 5.76, 4.30`; `0` soundness/model errors, `0` disagreements, `135/135` 35-key bit-exact
parity). Common Wall/Int columns cover the strict 133-instance 4-way common-solved subset (`C1`
and `FullM7Fidelity` each solve `135/140`, differing on 2 `quick60` instances each); pairwise
ratios cover each pair's mutually solved subset:

| Engine | Solved (`S/U`) | TO | Common Wall AM / GM (ms) | Common Int AM / GM (ms) | All-140 PAR-2 AM (s) / GM (ms) | Linked `.text` (B) / Non-NOP Insns | `vs C0-direct` (W-GM / I-GM) | `vs C3b` (W-GM / I-GM) | `vs C1` (W-GM / I-GM) |
|---|---|---:|---:|---:|---:|---:|---|---|---|
| `C1` (Kissat 4.0.4, `clang -O3`) | `135/140` (`54S/81U`) | 5 | `1280.0 / 286.1` | `1251.6 / 258.7` | `3.589 / 365.4` | `373,722 / 92,883` | — | — | — |
| `C0-direct` (`FullM7Fidelity` C99, `clang -O3`) | `135/140` (`55S/80U`) | 5 | `1505.8 / 306.9` | `1480.0 / 280.4` | `3.861 / 393.2` | `265,224 / 65,582` | `1.0000x / 1.0000x` | — | `1.0724x / 1.0839x` |
| `C3b` (`FullM7Fidelity` PrintCpp, `clang++ -O3`) | `135/140` (`55S/80U`) | 5 | `1600.6 / 336.3` | `1582.3 / 303.9` | `3.970 / 429.4` | `227,928 / 55,859` | `1.0958x / 1.0839x` | `1.0000x / 1.0000x` | `1.1754x / 1.1750x` |
| **`C4` (`FullM7Fidelity`, certified LeanQbe x64)** | **`135/140`** (`55S/80U`) | **5** | `1729.4 / 343.9` | `1711.2 / 320.7` | **`4.121 / 439.2`** | `260,792 / 63,876` | **`1.1216x / 1.1442x`** | **`1.0236x / 1.0557x`** | **`1.2020x / 1.2397x`** |

| Suite (`N`, 4-way common) | `C1` Solved | `C4` Solved | `C4` PAR-2 AM (s) | `C4 / C0-direct` (W-GM / I-GM) | `C4 / C3b` (W-GM / I-GM) | `C4 / C1` (W-GM / I-GM) |
|---|---:|---:|---:|---|---|---|
| `PV-35` (`35`, `35`) | `35/35` | `35/35` | `1.845` | `1.1514x / 1.1457x` | `1.1052x / 1.0722x` | `1.2773x / 1.2674x` |
| `Hard-24` (`24`, `24`) | `24/24` | `24/24` | `0.752` | `1.1303x / 1.1249x` | `0.9816x / 0.9817x` | `1.0429x / 1.0540x` |
| `SV-21` (`21`, `21`) | `21/21` | `21/21` | `0.640` | `1.0939x / 1.1631x` | `1.0198x / 1.0830x` | `1.0734x / 1.3617x` |
| `quick60` (`60`, `53`) | `55/60` | `55/60` | `8.015` | `1.1099x / 1.1446x` | `0.9942x / 1.0685x` | `1.2878x / 1.2670x` |
| **OVERALL** (`140`, `133`) | **`135/140`** | **`135/140`** | **`4.121`** | **`1.1216x / 1.1442x`** | **`1.0236x / 1.0557x`** | **`1.2020x / 1.2397x`** |

Gap attribution (`FullM7Fidelity`, mutually solved): `C0-direct / C1` = `1.0724x` W-GM (`1.0839x`
I-GM, `1.1764x` W-AM); `C3b / C0-direct` = `1.0958x` W-GM (`1.0839x` I-GM); `C4 / C3b` = `1.0236x`
W-GM (`1.0557x` I-GM); total compiler overhead `C4 / C0-direct` = `1.1216x` W-GM (`1.1442x` I-GM,
`1.1516x` W-AM). On All-140 PAR-2, `C4` is `1.0675x` AM (`1.1170x` GM) vs `C0-direct`, `1.0381x`
AM (`1.0227x` GM) vs `C3b`, and `1.1483x` AM (`1.2019x` GM) vs `C1`.

##### Certified `FullM7Plus` (`410` fns, `kissatM7Plus_compiled_x64`) — Stage-1 140-CNF breakdown

Measured on commit `e6b2c31d` (uncontended 48-vCPU host, start loadavg `4.85, 2.25, 2.26`, end
`4.67, 4.70, 3.37`; `0` soundness/model errors, `0` disagreements, `132/132` 35-key bit-exact
parity). Common Wall/Int columns cover the strict 132-instance 4-way common-solved subset:

| Engine | Solved (`S/U`) | TO | Common Wall AM / GM (ms) | Common Int AM / GM (ms) | All-140 PAR-2 AM (s) / GM (ms) | Linked `.text` (B) / Non-NOP Insns | `vs C0-direct` (W-GM / I-GM) | `vs C3b` (W-GM / I-GM) | `vs C1` (W-GM / I-GM) |
|---|---|---:|---:|---:|---:|---:|---|---|---|
| `C1` (Kissat 4.0.4, `clang -O3`) | `135/140` (`54S/81U`) | 5 | `1174.2 / 270.7` | `1157.0 / 249.2` | `3.563 / 356.1` | `373,722 / 92,883` | — | — | — |
| `C0-direct` (`FullM7Plus` C99, `clang -O3`) | `132/140` (`52S/80U`) | 8 | `1276.7 / 271.9` | `1241.5 / 244.4` | `4.632 / 370.1` | `262,616 / 64,978` | `1.0000x / 1.0000x` | — | `1.0043x / 0.9807x` |
| `C3b` (`FullM7Plus` PrintCpp, `clang++ -O3`) | `132/140` (`52S/80U`) | 8 | `1326.8 / 284.9` | `1309.1 / 259.7` | `4.680 / 386.8` | `225,832 / 55,366` | `1.0478x / 1.0627x` | `1.0000x / 1.0000x` | `1.0523x / 1.0422x` |
| **`C4` (`FullM7Plus`, certified LeanQbe x64)** | `132/140` (`52S/80U`) | 8 | `1475.8 / 303.5` | `1453.3 / 283.8` | `4.820 / 410.6` | `259,208 / 63,488` | **`1.1163x / 1.1611x`** | **`1.0654x / 1.0926x`** | **`1.1211x / 1.1387x`** |

| Suite (`N`, 4-way common) | `C1` Solved | `C4` Solved | `C4` PAR-2 AM (s) | `C4 / C0-direct` (W-GM / I-GM) | `C4 / C3b` (W-GM / I-GM) | `C4 / C1` (W-GM / I-GM) |
|---|---:|---:|---:|---|---|---|
| `PV-35` (`35`, `35`) | `35/35` | `35/35` | `1.774` | `1.1641x / 1.1561x` | `1.0966x / 1.1079x` | `1.3822x / 1.3590x` |
| `Hard-24` (`24`, `24`) | `24/24` | `24/24` | `0.529` | `1.1588x / 1.1448x` | `1.0556x / 1.0491x` | `0.8083x / 0.7882x` |
| `SV-21` (`21`, `21`) | `21/21` | `21/21` | `0.562` | `0.9239x / 1.1767x` | `0.9961x / 1.1141x` | `0.8659x / 1.0425x` |
| `quick60` (`60`, `52`) | `55/60` | `52/60` | `9.804` | `1.1515x / 1.1658x` | `1.0783x / 1.0943x` | `1.2571x / 1.2415x` |
| **OVERALL** (`140`, `132`) | **`135/140`** | `132/140` | `4.820` | **`1.1163x / 1.1611x`** | **`1.0654x / 1.0926x`** | **`1.1211x / 1.1387x`** |

Gap attribution (`FullM7Plus`, mutually solved): `C0-direct / C1` = `1.0043x` W-GM (`0.9807x` I-GM,
`1.0873x` W-AM); `C3b / C0-direct` = `1.0478x` W-GM (`1.0627x` I-GM); `C4 / C3b` = `1.0654x` W-GM
(`1.0926x` I-GM); total compiler overhead `C4 / C0-direct` = `1.1163x` W-GM (`1.1611x` I-GM,
`1.1559x` W-AM). On All-140 PAR-2, `C4` is `1.0405x` AM (`1.1094x` GM) vs `C0-direct`, `1.0300x`
AM (`1.0616x` GM) vs `C3b`, and `1.3529x` AM (`1.1531x` GM) vs `C1`.

##### Certified `FullM6` (`382` fns, `kissatM6_compiled_x64`) — Stage-1 140-CNF breakdown

Measured on commit `b200244a` (start loadavg `7.62, 6.52, 4.97`; `0` soundness/model errors, `0`
disagreements, `130/130` 35-key bit-exact parity; common Wall/Int columns cover the 129-instance
4-way common-solved subset):

| Engine | Solved (`S/U`) | TO | Common Wall AM / GM (ms) | Common Int AM / GM (ms) | All-140 PAR-2 AM (s) / GM (ms) | Linked `.text` (B) / Non-NOP Insns | `vs C0-direct` (W-GM / I-GM) | `vs C3b` (W-GM / I-GM) | `vs C1` (W-GM / I-GM) |
|---|---|---:|---:|---:|---:|---:|---|---|---|
| `C1` (Kissat 4.0.4, `clang -O3`) | `135/140` (`54S/81U`) | 5 | `970.1 / 252.0` | `952.0 / 232.0` | `3.570 / 357.7` | `373,722 / 92,883` | — | — | — |
| `C0-direct` (`FullM6` C99, `clang -O3`) | `132/140` (`52S/80U`) | 8 | `1217.5 / 267.8` | `1191.0 / 242.5` | `5.001 / 400.6` | `249,464 / 60,963` | `1.0000x / 1.0000x` | — | `1.0783x / 1.0605x` |
| `C3b` (`FullM6` PrintCpp, `clang++ -O3`) | `131/140` (`52S/79U`) | 9 | `1304.1 / 278.7` | `1285.1 / 255.4` | `5.342 / 418.3` | `215,960 / 52,430` | `1.0402x / 1.0526x` | `1.0000x / 1.0000x` | `1.1215x / 1.1161x` |
| **`C4` (`FullM6`, certified LeanQbe x64)** | `131/140` (`51S/80U`) | 9 | `1420.3 / 295.3` | `1394.9 / 275.0` | `5.502 / 442.3` | `206,024 / 49,848` | **`1.1025x / 1.1337x`** | **`1.0599x / 1.0771x`** | **`1.1723x / 1.1856x`** |

*(Gap attribution: `C0-direct / C1` = `1.0783x` W-GM, `C3b / C0-direct` = `1.0402x` W-GM, `C4 /
C3b` = `1.0599x` W-GM, `C4 / C0-direct` = `1.1025x` W-GM / `1.1337x` I-GM; All-140 PAR-2 AM
ratios `1.1003x` vs `C0-direct` and `1.5412x` vs `C1`. One borderline `PV-35` instance
`hw_ibm_2004_01_k90_sat` timed out at `30.0 s` on `C4` in this run and solved in `24.7 s` on prior
repeats of identical `FullM6` code.)*

##### Code size and emission summary (x86-64)

| Target | Certification on `main` | Fns | `C4` Emit Time / `.s` (B) | `C4` Object / Linked `.text` (B) / Non-NOP Insns | `C0-direct` Linked `.text` (B) / Insns | `C3b` Linked `.text` (B) / Insns |
|---|---|---:|---:|---:|---:|---:|
| `C1` (Kissat 4.0.4, `clang -O3`) | Upstream reference | — | — | — | `373,722 / 92,883` *(ref)* | — |
| **`FullM7Fidelity`** (`m7InlPolicy`) | **Certified x86-64 & AArch64 `LinkedCert`** | `413` | `12.14 s / 1,466,178` | `252,853 / 260,792 / 63,876` | `265,224 / 65,582` | `227,928 / 55,859` |
| **`FullM7Plus`** (`m7InlPolicy`) | **Certified x86-64 & AArch64 `LinkedCert`** | `410` | `12.07 s / 1,458,034` | `251,274 / 259,208 / 63,488` | `262,616 / 64,978` | `225,832 / 55,366` |
| **`FullM6`** (`m6InlPolicy`) | **Certified x86-64 & AArch64 `LinkedCert`** | `382` | `7.98 s / 1,139,941` | `198,090 / 206,024 / 49,848` | `249,464 / 60,963` | `215,960 / 52,430` |

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
| `bench/kissat/` | Solver CLI wrapper, build scripts, 159-line 4-way benchmark (`compare_4way_min.py`), Stage-1 harness (`run_4way_stage1.py`), C0-to-C99 extractor (`extract_c0_direct.py`), CNF generators, canary ratchet, and telemetry/lockstep tools |
| `test/kissat/` | CLI solver tests (`test_cli_solver.sh`), OOM/witness fuzzer (`fuzz_oom_witness.py`), and IR helpers |
| `scripts/` | [`check.sh`](scripts/check.sh), hub and import checks, theorem lists (`headlines.d/`) |
| `docs/reports/` | Design notes on individual components |
