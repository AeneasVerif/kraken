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
| Kissat SAT solver ([details](#verified-kissat-sat-solver)) | `FullM6` (382 fns): UNSAT soundness and concrete UNSAT non-vacuity of compiled x86-64 and AArch64 machine code; `FullM5` (270 fns): SAT and UNSAT soundness and UNSAT non-vacuity on both architectures | [Spec](LeanQbeTest/T/KissatAuditSpec.lean), [X64](LeanQbeTest/T/KissatAuditX64.lean), [Arm64](LeanQbeTest/T/KissatAuditArm64.lean), [M6X64](LeanQbeTest/T/KissatM6AuditX64.lean), [M6Arm64](LeanQbeTest/T/KissatM6AuditArm64.lean), [M6Proof](LeanQbeTest/T/KissatM6ProofTest.lean), [M6Sat](LeanQbeTest/T/KissatM6SatSoundTest.lean), [M5X64](LeanQbeTest/T/KissatM5AuditX64.lean), [M5Arm64](LeanQbeTest/T/KissatM5AuditArm64.lean), [M5SoundX64](LeanQbeTest/T/KissatM5SoundAuditX64.lean), [M5SoundArm64](LeanQbeTest/T/KissatM5SoundAuditArm64.lean), [SatSound](LeanQbeTest/T/KissatSatSoundTest.lean) |
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
  LeanQbeTest.T.KissatAuditArm64 LeanQbeTest.T.KissatM6AuditX64 \
  LeanQbeTest.T.KissatM6AuditArm64 LeanQbeTest.T.KissatM6ProofTest \
  LeanQbeTest.T.KissatM6SatSoundTest LeanQbeTest.T.KissatM5AuditX64 \
  LeanQbeTest.T.KissatM5AuditArm64 LeanQbeTest.T.KissatM5SoundAuditX64 \
  LeanQbeTest.T.KissatM5SoundAuditArm64 LeanQbeTest.T.KissatSatSoundTest \
  LeanQbeTest.T.KissatM5Test \
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
[Kissat](https://github.com/arminbiere/kissat) SAT solver to C0. Two certified solver modules are
active in this repository:

- **`LeanQbe.T.Examples.Kissat.FullM6`** ([`FullM6.lean`](LeanQbe/T/Examples/Kissat/FullM6.lean#L210)):
  382 functions inlined with the profile-guided policy
  [`m6InlPolicy`](LeanQbe/T/Examples/Kissat/FullM6InlPolicy.lean#L107) and materialized in
  [`FullM6Inl.lean`](LeanQbe/T/Examples/Kissat/FullM6Inl.lean#L46). For this module, the repository
  proves unconditional (`0` hooks) **UNSAT soundness** and **concrete UNSAT non-vacuity** of the
  compiled x86-64 and AArch64 machine code (`kissatM6_compiled_x64` and `kissatM6_compiled_arm64`).
  Per project scope, `FullM6` machine-code proofs cover UNSAT soundness and non-vacuity and omit
  machine-code SAT soundness/model-check proofs; at runtime (and in CLI/benchmark tests), `FullM6`
  still executes `kissat_check_model`
  ([`FullM6Orch.lean`](LeanQbe/T/Examples/Kissat/FullM6Orch.lean#L776)) on every candidate SAT
  assignment before returning `10`.
- **`LeanQbe.T.Examples.Kissat.FullM5`** ([`FullM5.lean`](LeanQbe/T/Examples/Kissat/FullM5.lean#L354)):
  270 functions after inlining with `InlinePolicy.b5`. For this module, the repository proves
  soundness of **both SAT and UNSAT** answers (including constructive model extraction) and
  concrete UNSAT non-vacuity for the compiled machine code on x86-64 and on AArch64.

The solver exports a single C entry point:

```c
uint64_t kissat_solve_bytes(const uint8_t *cnf_ptr, uint64_t cnf_len,
                            uint8_t *work_ptr, uint64_t work_len, uint64_t fuel);
/* Returns 20 = UNSAT, 10 = SAT (model left in the workspace), 0 = unknown. */
```

`cnf_ptr`/`cnf_len` is a DIMACS CNF file in memory, `work_ptr`/`work_len` is a caller-provided
workspace, and `fuel` bounds the number of solver steps. The solver returns `0` for malformed
input or when it runs out of fuel or workspace.

A newer development module, `FullM7` (410 functions,
[`FullM7.lean`](LeanQbe/T/Examples/Kissat/FullM7.lean#L397)) together with `FullM7*` C0 components
and source-level proofs, is also present under
[`LeanQbe/T/Examples/Kissat/`](LeanQbe/T/Examples/Kissat/); it does not yet have machine-code
certificates.

### Building and running the solver

Prerequisites: `elan` (which installs the toolchain named in `lean-toolchain`), a C compiler, and,
for AArch64 binaries on an x86-64 host, `aarch64-linux-gnu-gcc` and `qemu-aarch64`.

[`bench/kissat/build_solver.sh`](bench/kissat/build_solver.sh) builds the Lean code, prints the
certified assembly for the selected module and architecture, and links it with the command-line
wrapper [`bench/kissat/kissat_cli.c`](bench/kissat/kissat_cli.c). Both `--module FullM6` (382
functions, matching `kissatM6_compiled_{x64,arm64}.code`) and `--module FullM5` (270 functions,
default) build certified binaries without `--allow-uncertified`.

```bash
# Certified FullM6 (382 fns) on x86-64 and AArch64
bash bench/kissat/build_solver.sh --module FullM6 --arch x64 -o /tmp/kissat-leanqbe-fullm6
bash bench/kissat/build_solver.sh --module FullM6 --arch arm64 -o /tmp/kissat-leanqbe-fullm6-arm64

# Certified FullM5 (270 fns, SAT+UNSAT machine-code proofs; default --module)
bash bench/kissat/build_solver.sh --module FullM5 --arch x64 -o /tmp/kissat-leanqbe-fullm5
bash bench/kissat/build_solver.sh --module FullM5 --arch arm64 -o /tmp/kissat-leanqbe-fullm5-arm64

# Usage: kissat-leanqbe [--work-mb <MB>] [--fuel <N>] [-n|--no-model] <input.cnf | ->
printf 'p cnf 1 2\n1 0\n-1 0\n' | /tmp/kissat-leanqbe-fullm6 -
# s UNSATISFIABLE          (exit status 20)

printf 'p cnf 2 2\n1 2 0\n-1 0\n' | /tmp/kissat-leanqbe-fullm6 -
# s SATISFIABLE            (exit status 10)
# v -1 2 0

qemu-aarch64 -L /usr/aarch64-linux-gnu /tmp/kissat-leanqbe-fullm6-arm64 input.cnf
```

The program prints a DIMACS status line (`s SATISFIABLE`, `s UNSATISFIABLE`, or `s UNKNOWN`) and
exits with status `10`, `20`, or `0` respectively; for satisfiable inputs it also prints the
model as `v ... 0` lines unless `-n` is given. Exit status `1` indicates a usage or I/O error.

The emitted assembly matches the `LinkedCert` only for the default settings (`--inline-max 0`).
The options `--inline-max <N>` with `N > 0` and `--debug` change the generated code and print a
warning; binaries built with them, or with `--allow-uncertified`, are not covered by the proofs.

Tests and proofs:

```bash
# Builds FullM5 and FullM6 (certified) plus FullM7 (--allow-uncertified) for x86-64 and AArch64
# and checks exit codes, DIMACS models, -n, stdin input, and workspace guard pages.
bash test/kissat/test_cli_solver.sh

# Machine-code and source-level audit files for FullM6 and FullM5.
lake build --wfail LeanQbeTest.T.KissatAuditSpec LeanQbeTest.T.KissatM6AuditX64 \
  LeanQbeTest.T.KissatM6AuditArm64 LeanQbeTest.T.KissatM6ProofTest \
  LeanQbeTest.T.KissatM6SatSoundTest LeanQbeTest.T.KissatAuditX64 \
  LeanQbeTest.T.KissatAuditArm64 LeanQbeTest.T.KissatSatSoundTest
```

### What is proved

The audit files restate the main theorems with full types:

- **FullM6 (382 functions):** [`KissatM6AuditX64.lean`](LeanQbeTest/T/KissatM6AuditX64.lean) and
  [`KissatM6AuditArm64.lean`](LeanQbeTest/T/KissatM6AuditArm64.lean) audit the compiled x86-64 and
  AArch64 machine-code UNSAT soundness and non-vacuity theorems from
  [`Amd64/KissatM6.lean`](LeanQbe/T/Amd64/KissatM6.lean) and
  [`Arm64/KissatM6.lean`](LeanQbe/T/Arm64/KissatM6.lean).
  [`KissatM6ProofTest.lean`](LeanQbeTest/T/KissatM6ProofTest.lean) audits the 382-function
  source-level `ModuleOk`, soundness, and UNSAT non-vacuity proofs
  ([`FullM6Proof.lean`](LeanQbe/T/Examples/Kissat/FullM6Proof.lean)), and
  [`KissatM6SatSoundTest.lean`](LeanQbeTest/T/KissatM6SatSoundTest.lean) audits the source-level
  proof combinators. The full list of audited theorems is in
  [`scripts/headlines.d/kissat_m6.txt`](scripts/headlines.d/kissat_m6.txt).
- **FullM5 (270 functions):** [`KissatAuditX64.lean`](LeanQbeTest/T/KissatAuditX64.lean) and
  [`KissatAuditArm64.lean`](LeanQbeTest/T/KissatAuditArm64.lean) re-export the machine-code audits
  for `FullM5` from [`KissatM5AuditX64.lean`](LeanQbeTest/T/KissatM5AuditX64.lean),
  [`KissatM5AuditArm64.lean`](LeanQbeTest/T/KissatM5AuditArm64.lean),
  [`KissatM5SoundAuditX64.lean`](LeanQbeTest/T/KissatM5SoundAuditX64.lean), and
  [`KissatM5SoundAuditArm64.lean`](LeanQbeTest/T/KissatM5SoundAuditArm64.lean)
  ([`scripts/headlines.d/kissat_m5.txt`](scripts/headlines.d/kissat_m5.txt));
  [`KissatSatSoundTest.lean`](LeanQbeTest/T/KissatSatSoundTest.lean) covers source-level SAT and
  UNSAT soundness and a concrete SAT non-vacuity example.
- **Specification:** [`KissatAuditSpec.lean`](LeanQbeTest/T/KissatAuditSpec.lean) audits the
  DIMACS parser `parseDimacs` and the predicates `CNF.Unsat` and `CNF.Sat`.

#### Machine-code soundness

For **`FullM6`**, [`m6_solve_bytes_unsat_x64`](LeanQbe/T/Amd64/KissatM6.lean#L114) and
[`m6_solve_bytes_unsat_arm64`](LeanQbe/T/Arm64/KissatM6.lean#L113) (with answer-only corollaries
[`kissat_m6_x64_unsat_correct`](LeanQbe/T/Amd64/KissatM6.lean#L171) and
[`kissat_m6_arm64_unsat_correct`](LeanQbe/T/Arm64/KissatM6.lean#L169)) state the following over
the compiled 382-function module ([`kissatM6_compiled_x64`](LeanQbe/T/Amd64/KissatM6.lean#L37) or
[`kissatM6_compiled_arm64`](LeanQbe/T/Arm64/KissatM6.lean#L37)). Take any executable containing the
compiled code and any call to `kissat_solve_bytes` that follows the platform ABI, passes DIMACS
bytes and a suitably aligned workspace, has enough stack, and has a caller frame `R`. Then
execution terminates and returns to the caller with:

- a result in `{0, 10, 20}` (in `rax` or `X0`);
- if the result is `20`: `∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`;
- callee-saved registers (`rbx`, `rbp`, `r12`–`r15` on x86-64; `X19`–`X29` on AArch64) and the
  stack pointer restored;
- the input bytes unchanged, the workspace and stack frame accounted for as separate memory
  regions, and the caller frame `R` untouched.

Per project scope, the `FullM6` machine-code theorems certify UNSAT soundness and memory/register
framing and omit machine-code SAT model-check proofs.

For **`FullM5`**, [`m5_solve_bytes_model_x64`](LeanQbe/T/Amd64/KissatM5Sound.lean#L89) and
[`m5_solve_bytes_model_arm64`](LeanQbe/T/Arm64/KissatM5Sound.lean#L88) (together with the
UNSAT-only theorems [`m5_solve_bytes_unsat_x64`](LeanQbe/T/Amd64/KissatM5.lean#L88) and
[`m5_solve_bytes_unsat_arm64`](LeanQbe/T/Arm64/KissatM5.lean#L88)) state the same ABI, framing,
and UNSAT guarantees for the compiled 270-function module (`kissatM5_compiled_x64` or
`kissatM5_compiled_arm64`), and additionally prove that:

- if the result is `10`: `∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ (∃ α, cnf.Sat α) ∧
  cnf.Sat (readModelFromWork st.data.dmem work_ptr)`, i.e. the assignment stored in the
  workspace satisfies the input formula.

#### How SAT answers are checked

Kissat's inprocessing transformations (such as variable elimination) require reconstructing a
model of the original formula at the end of the search. Rather than verifying that
reconstruction, the solver checks its result. In both
[`FullM5Orch.lean`](LeanQbe/T/Examples/Kissat/FullM5Orch.lean#L643) and
[`FullM6Orch.lean`](LeanQbe/T/Examples/Kissat/FullM6Orch.lean#L773-L777), after model
reconstruction (`full_extend`) for a candidate SAT result, the entry point restores the original
variable count and calls `kissat_check_model`, which evaluates every clause of the original,
read-only DIMACS input and returns `10` only if every clause is satisfied (`0` otherwise). For
`FullM5`, this runtime check is proved end-to-end against
[`readModelFromWork`](LeanQbe/T/Examples/Kissat/FullSatSound.lean#L102) via
[`kissat_solve_bytes_m5_model_wp`](LeanQbe/T/Examples/Kissat/FullSatSound.lean#L838) and
[`ModuleOk.respec_tail`](LeanQbe/T/Examples/Kissat/FullSatSound.lean#L42), and lifted to x86-64
and AArch64 machine code in `KissatM5Sound.lean`. For `FullM6`, `kissat_check_model` runs at
runtime and is checked by the CLI and benchmark harnesses, while machine-code proofs remain scoped
to UNSAT soundness and non-vacuity.

#### Non-vacuity

A soundness theorem whose hypotheses can never be met would be vacuous. The repository therefore
also shows that the hypotheses are satisfiable and that the interesting results are reachable:

- Machine code (`FullM6` UNSAT):
  [`audit_m6_x64_nv_closed`](LeanQbeTest/T/KissatM6AuditX64.lean#L138) and
  [`audit_m6_arm_nv_closed`](LeanQbeTest/T/KissatM6AuditArm64.lean#L149) (along with concrete-host
  execution witnesses [`m6_x64_run_unsat`](LeanQbe/T/Amd64/KissatM6.lean#L264) and
  [`m6_arm64_run_unsat`](LeanQbe/T/Arm64/KissatM6.lean#L273)) instantiate the machine-code
  theorems on `kissatM6_compiled_x64.host` and `kissatM6_compiled_arm64.host` and show that
  executions returning `20` exist.
- Machine code (`FullM5` UNSAT):
  [`audit_m5_x64_nv_closed`](LeanQbeTest/T/KissatM5AuditX64.lean#L137) and
  [`audit_m5_arm_nv_closed`](LeanQbeTest/T/KissatM5AuditArm64.lean#L135) instantiate the
  machine-code theorems on `kissatM5_compiled_x64.host` and `kissatM5_compiled_arm64.host` and show
  that executions returning `20` exist.
- Source level (`FullM5` SAT): [`m5_sat_nonvacuous`](LeanQbe/T/Examples/Kissat/FullM5SatNv.lean#L2721)
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
`s UNSATISFIABLE` only for unsatisfiable inputs (for both `FullM6` and `FullM5`), and
`s SATISFIABLE` with a satisfying model only for satisfiable inputs (proved at the machine-code
level for `FullM5`, and checked at runtime by `kissat_check_model` for `FullM6`), one must trust:

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

### Reproducible 4-way performance benchmark

[`bench/kissat/run_4way_stage1.py`](bench/kissat/run_4way_stage1.py) builds and evaluates four
corners on x86-64 to separate C0 source/algorithm differences from IR lowering and LeanQbe back-end
code generation:

- **`C1`**: upstream Kissat 4.0.4 compiled with `clang -O3`.
- **`C0-direct`**: the identical `FullM6` C0 source extracted directly to C99
  ([`extract_c0_direct.py`](bench/kissat/extract_c0_direct.py)) and compiled with
  `clang -std=c99 -O3 -fwrapv -fno-strict-aliasing`.
- **`C3b`**: `FullM6` lowered to `LeanQbe.T` and emitted via `PrintCpp` (`-DTQBE_NATIVE_MEM`),
  compiled with `clang++ -std=c++20 -O3`.
- **`C4` (`FullM6`)**: `FullM6` compiled by the verified LeanQbe x86-64 pipeline
  (`FullM6Inl.m6InlFns`, matching `kissatM6_compiled_x64.code`, printed with `toATTAligned` and
  linked `-no-pie`).

`C0-direct`, `C3b`, and `C4` link against the same
[`bench/kissat/bench_main.c`](bench/kissat/bench_main.c) harness (guarded buffers + full DIMACS
model checking).

```bash
# Build certified FullM6 CLI binaries (x86-64 and AArch64)
bash bench/kissat/build_solver.sh --module FullM6 --arch x64 -o /tmp/kissat-leanqbe-fullm6
bash bench/kissat/build_solver.sh --module FullM6 --arch arm64 -o /tmp/kissat-leanqbe-fullm6-arm64

# Run the reproducible 4-way Stage-1 (140-CNF) benchmark
# (--manifest / --c1-bin may also be set via STAGE1_MANIFEST / KISSAT_C1_BIN)
python3 bench/kissat/run_4way_stage1.py --module FullM6 --jobs 8 \
  --out-json /tmp/m6_4way.json --out-md /tmp/m6_4way.md
```

**Environment and methodology:** Stage-1 suite of 140 unique CNFs (`PV-35`: 35, `Hard-24`: 24,
`SV-21`: 21, `quick60`: 60), `30.0 s` per-CNF timeout (`60.0 s` PAR-2 penalty), `20.0 ms` floor
for geometric means, `2,000,000,000` fuel, `--jobs 8`, and interleaved per-CNF engine order on
Intel Xeon @ 2.60 GHz (48 vCPUs, `clang`/`clang++` 21.1.8; measured under background build loadavg
14.65–19.91, with a repeat run matching within ~1% on all aggregate ratios). Every SAT assignment
was verified against the DIMACS clauses with **0** soundness/model errors, **0** cross-solver
verdict disagreements, and **132/132** bit-exact 35-key telemetry parity (`0` diffs across
`C0-direct == C3b == C4`).

| Engine | Solved (`S/U`) | TO | Common Wall AM / GM (ms) | Common Int AM / GM (ms) | All-140 PAR-2 AM (s) / GM (ms) | Linked `.text` (B) / Non-NOP Insns | `vs C0-direct` (W-GM / I-GM) | `vs C3b` (W-GM / I-GM) | `vs C1` (W-GM / I-GM) |
|---|---|---:|---:|---:|---:|---:|---|---|---|
| `C1` (Kissat 4.0.4, `clang -O3`) | `135/140` (`54S/81U`) | 5 | `1204.3 / 270.0` | `1192.1 / 252.0` | `3.646 / 363.6` | `373,722 / 92,883` | — | — | — |
| `C0-direct` (`FullM6` C99, `clang -O3`) | `132/140` (`52S/80U`) | 8 | `1610.5 / 300.4` | `1583.3 / 267.1` | `5.069 / 418.8` | `249,464 / 60,963` | `1.0000x / 1.0000x` | — | `1.1126x / 1.0599x` |
| `C3b` (`FullM6` PrintCpp, `clang++ -O3`) | `132/140` (`52S/80U`) | 8 | `1655.0 / 307.1` | `1635.3 / 277.8` | `5.117 / 427.6` | `215,960 / 52,430` | `1.0225x / 1.0398x` | `1.0000x / 1.0000x` | `1.1374x / 1.1021x` |
| **`C4` (`FullM6`, certified LeanQbe x64)** | `132/140` (`52S/80U`) | 8 | `1782.4 / 327.8` | `1755.0 / 296.6` | `5.248 / 454.8` | `206,024 / 49,848` | **`1.0915x / 1.1104x`** | **`1.0675x / 1.0679x`** | **`1.2140x / 1.1767x`** |

*(Common Wall/Int AM and GM are over the strict 131-instance 4-way common-solved subset; pairwise
ratios are over each pair's mutually solved subset; `.text` object sizes are `241,541 B`
`C0-direct`, `208,036 B` `C3b`, and `198,090 B` `C4` with `1,139,941 B` `.s` assembly emitted in
`8.87 s`.)*

Per-suite breakdown (`C4` vs `C0-direct` / `C3b` / `C1`, mutually solved Wall GM / Int GM):

| Suite (`N`, 4-way common) | `C1` Solved | `C4` Solved | `C4` PAR-2 AM (s) | `C4 / C0-direct` (W-GM / I-GM) | `C4 / C3b` (W-GM / I-GM) | `C4 / C1` (W-GM / I-GM) |
|---|---:|---:|---:|---|---|---|
| `PV-35` (`35`, `35`) | `35/35` | `35/35` | `2.220` | `1.1362x / 1.1186x` | `1.1064x / 1.0780x` | `1.2490x / 1.1999x` |
| `Hard-24` (`24`, `24`) | `24/24` | `24/24` | `0.767` | `1.0897x / 1.0984x` | `1.0421x / 1.0534x` | `0.9031x / 0.8960x` |
| `SV-21` (`21`, `21`) | `21/21` | `21/21` | `0.753` | `0.9735x / 1.0982x` | `1.0892x / 1.1016x` | `1.1725x / 1.0707x` |
| `quick60` (`60`, `51`) | `55/60` | `52/60` | `10.381` | `1.1136x / 1.1153x` | `1.0454x / 1.0545x` | `1.3882x / 1.3722x` |
| **OVERALL** (`140`, `131`) | **`135/140`** | **`132/140`** | **`5.248`** | **`1.0915x / 1.1104x`** | **`1.0675x / 1.0679x`** | **`1.2140x / 1.1767x`** |

On All-140 PAR-2 (`30.0 s` cap, `60.0 s` penalty), `C4` is `1.0353x` AM (`1.0861x` GM) vs
`C0-direct`, `1.0257x` AM (`1.0636x` GM) vs `C3b`, and `1.4395x` AM (`1.2510x` GM) vs `C1`.

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
