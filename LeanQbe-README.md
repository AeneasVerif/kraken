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
| Kissat SAT solver — certified machine code ([details](#verified-kissat-sat-solver)) | **`FullM6`** (`382` fns, primary): dual-arch x86-64 and AArch64 `LinkedCert` UNSAT soundness and concrete UNSAT non-vacuity (runtime `kissat_check_model` on SAT); **`FullM5`** (`270` fns, earlier baseline): dual-arch SAT (with constructive model soundness) and UNSAT machine-code proofs plus concrete UNSAT non-vacuity | [Spec](LeanQbeTest/T/KissatAuditSpec.lean), [M6X64](LeanQbeTest/T/KissatM6AuditX64.lean), [M6Arm64](LeanQbeTest/T/KissatM6AuditArm64.lean), [M6Proof](LeanQbeTest/T/KissatM6ProofTest.lean), [M6Sat](LeanQbeTest/T/KissatM6SatSoundTest.lean), [X64](LeanQbeTest/T/KissatAuditX64.lean), [Arm64](LeanQbeTest/T/KissatAuditArm64.lean), [M5X64](LeanQbeTest/T/KissatM5AuditX64.lean), [M5Arm64](LeanQbeTest/T/KissatM5AuditArm64.lean), [M5SoundX64](LeanQbeTest/T/KissatM5SoundAuditX64.lean), [M5SoundArm64](LeanQbeTest/T/KissatM5SoundAuditArm64.lean), [M5Test](LeanQbeTest/T/KissatM5Test.lean), [SatSound](LeanQbeTest/T/KissatSatSoundTest.lean) |
| Kissat SAT solver — source & PGO-inlined WP ([details](#verified-kissat-sat-solver)) | **`FullM7Plus`** (`410` fns) and **`FullM7Fidelity`** (`413` fns, upstream Kissat 4.0.4 fidelity): closed `0`-hook `ModuleOk`, `m7InlPolicy` PGO-inlined IR equivalence, `Func.wp` UNSAT soundness, and concrete UNSAT non-vacuity (`LinkedCert`s in progress); **`FullM7FidelityCore`** (`9`-fn subsystem / `412`-fn spliced) | [M7PlusSpec](LeanQbeTest/T/KissatM7PlusAuditSpec.lean), [M7PlusAsm](LeanQbeTest/T/KissatM7PlusAssemblyTest.lean), [M7FidSpec](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean), [M7FidCore](LeanQbeTest/T/KissatM7FidelityCoreTest.lean) |
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
  LeanQbeTest.T.KissatM5Test LeanQbeTest.T.KissatM7PlusAuditSpec \
  LeanQbeTest.T.KissatM7PlusAssemblyTest LeanQbeTest.T.KissatM7FidelityAuditSpec \
  LeanQbeTest.T.KissatM7FidelityCoreTest \
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

The largest program verified with this toolchain is a port of the
[Kissat](https://github.com/arminbiere/kissat) SAT solver to C0. Active solver modules on `main`
fall into two tiers: **certified machine-code solvers** (`LinkedCert`s on both x86-64 and AArch64)
and **source / PGO-inlined WP-verified next-generation solvers** whose dual-arch machine-code
certificates are in progress.

| Module | Fns | Verification tier on `main` | Inlining policy | Key proved guarantees |
|---|---:|---|---|---|
| **`FullM6`** ([`FullM6.lean`](LeanQbe/T/Examples/Kissat/FullM6.lean#L210)) | `382` | **Certified machine code** (primary; x86-64 & AArch64 `LinkedCert`s) | [`m6InlPolicy`](LeanQbe/T/Examples/Kissat/FullM6InlPolicy.lean#L107) ([`FullM6Inl.lean`](LeanQbe/T/Examples/Kissat/FullM6Inl.lean#L46), 6 chunks) | `0`-hook `ModuleOk`, dual-arch machine-code **UNSAT soundness** + concrete **UNSAT non-vacuity**; runtime `kissat_check_model` on SAT |
| **`FullM5`** ([`FullM5.lean`](LeanQbe/T/Examples/Kissat/FullM5.lean#L354)) | `270` | **Certified machine code** (earlier baseline; x86-64 & AArch64 `LinkedCert`s) | [`InlinePolicy.b5`](LeanQbe/T/Inline.lean#L377) ([`FullM5InlB5.lean`](LeanQbe/T/Examples/Kissat/FullM5InlB5.lean#L31)) | `0`-hook `ModuleOk`, dual-arch machine-code **SAT (constructive model) + UNSAT soundness** + concrete UNSAT non-vacuity; source SAT non-vacuity |
| **`FullM7Plus`** ([`FullM7PlusAssembly.lean`](LeanQbe/T/Examples/Kissat/FullM7PlusAssembly.lean#L250)) | `410` | **WP + PGO-inlined IR verified** (dual-arch `LinkedCert`s in progress) | [`m7InlPolicy`](LeanQbe/T/Examples/Kissat/FullM7InlPolicy.lean#L113) ([`FullM7PlusInl.lean`](LeanQbe/T/Examples/Kissat/FullM7PlusInl.lean#L62), 13 chunks) | `0`-hook `ModuleOk`, `m7InlPolicy` equivalence, source & inlined `Func.wp` **UNSAT soundness** + concrete UNSAT non-vacuity |
| **`FullM7Fidelity`** ([`FullM7FidelityAssembly.lean`](LeanQbe/T/Examples/Kissat/FullM7FidelityAssembly.lean#L336)) | `413` | **WP + PGO-inlined IR verified** (dual-arch `LinkedCert`s in progress) | [`m7InlPolicy`](LeanQbe/T/Examples/Kissat/FullM7InlPolicy.lean#L113) ([`FullM7FidelityInl.lean`](LeanQbe/T/Examples/Kissat/FullM7FidelityInl.lean#L62), 13 chunks) | `0`-hook `ModuleOk`, `m7InlPolicy` equivalence, source & inlined `Func.wp` **UNSAT soundness** + concrete UNSAT non-vacuity |

#### Solver progression

- **Certified machine-code solvers (`FullM6` and `FullM5`):**
  - **`FullM6`** (`382` fns, **primary certified solver**) extends `FullM5` (`+112` fns) with a
    unified `3,456 B` `M6Hdr` layout, watch-list GC/defrag (`FullM6WatchGc`), compact flush and
    arena sweep (`FullM6CompactFlush`), recursive clause minimization and shrinking
    (`FullM6MinShrink`), 3-tier learned-clause management (`FullM6Tiers`), chronological
    vivification and backbone (`FullM6VivBackbone`), congruence substitution and gate equivalence
    (`FullM6CongSubst`), BVE with forward subsumption (`FullM6BveFwd`), hop-free BVA
    (`FullM6BvaNoHops`), focused/stable search orchestration (`FullM6Orch`), random-walk local
    search warmup (`FullM6WalkParse`), and fast BCP (`FullM6BcpS15`). Its machine-code proofs
    (`kissatM6_compiled_x64` and `kissatM6_compiled_arm64`) certify unconditional (`0`-hook)
    **UNSAT soundness** and **concrete UNSAT non-vacuity**; per project scope, machine-code SAT
    model-check proofs are omitted, while at runtime `FullM6` still runs `kissat_check_model`
    ([`FullM6Orch.lean`](LeanQbe/T/Examples/Kissat/FullM6Orch.lean#L776)) before returning `10`.
  - **`FullM5`** (`270` fns, **earlier certified baseline**) implements core CDCL with 1-UIP
    analysis, chronological backtracking, VSIDS/VMTF, Luby restarts, OTFS, BVE, Tarjan-SCC
    congruence, ternary HBR, probing, and embedded Kitten definition extraction. It remains active
    because its machine-code proofs cover **both SAT (constructive model extraction) and UNSAT**
    on x86-64 and AArch64.
- **Next-generation WP-verified solvers (`FullM7Plus` and `FullM7Fidelity`):**
  - Both build atop the intermediate `410`-function `FullM7`
    ([`FullM7.lean`](LeanQbe/T/Examples/Kissat/FullM7.lean#L397)) base (`+28` fns over `FullM6`,
    adding analyze-sort, RNG score bumping/rescaling, hot ignore-set BCP, 2-literal hash
    congruence & ITE/AND/XOR BVE gate extraction, BVA factoring, queue/heap reordering, full
    random-walk local search with break counts, and EMA multi-mode search with target/best phase
    saving).
  - **`FullM7Plus`** (`410` fns) splices `17` disjoint canonical replacements onto `FullM7`
    (`FullM7BvaGuFix`, `FullM7CompactFix`, `FullM7BvaV5Fix`, `FullM7ParityVivTiers`,
    `FullM7ParityBvaTie`) and is proved closed (`0`-hook `ModuleOk`, PGO-inlined equivalence,
    `Func.wp` UNSAT soundness, and concrete UNSAT non-vacuity) in
    [`FullM7PlusAssemblyProof.lean`](LeanQbe/T/Examples/Kissat/FullM7PlusAssemblyProof.lean#L931)
    and [`KissatM7PlusAuditSpec.lean`](LeanQbeTest/T/KissatM7PlusAuditSpec.lean).
  - **`FullM7Fidelity`** (`413` fns) is a high-fidelity C0 replica of upstream Kissat 4.0.4,
    applying `29` canonical replacements and `3` inserted helpers onto `FullM7` — including the
    upstream scheduling/search/core fidelity modules `FullM7Fidelity{Sched,SchedFix,Core,Search}`
    (where `FullM7FidelityCore`
    ([`FullM7FidelityCore.lean`](LeanQbe/T/Examples/Kissat/FullM7FidelityCore.lean#L777)) also
    exposes standalone `9`-fn and spliced `412`-fn WP audits in
    [`KissatM7FidelityCoreTest.lean`](LeanQbeTest/T/KissatM7FidelityCoreTest.lean)). Its closed
    `0`-hook `ModuleOk`, PGO-inlined equivalence, `Func.wp` UNSAT soundness, and concrete UNSAT
    non-vacuity are audited in
    [`FullM7FidelityAssemblyProof.lean`](LeanQbe/T/Examples/Kissat/FullM7FidelityAssemblyProof.lean#L1107)
    and [`KissatM7FidelityAuditSpec.lean`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean).
  - Neither `FullM7Plus` nor `FullM7Fidelity` has machine-code `LinkedCert`s on `main` yet;
    their native binaries therefore require `--allow-uncertified` in `build_solver.sh` until
    their dual-arch `LinkedCert`s land. Earlier superseded solver generations (`Plain`, `Full`,
    `FullFast`, `FullM3`, `FullM4`) live in [`LeanQbeLegacyTest/`](LeanQbeLegacyTest/).

All active Kissat modules export the same C entry point:

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

[`bench/kissat/build_solver.sh`](bench/kissat/build_solver.sh) builds the Lean code, prints the
assembly for the selected module and architecture, and links it with the command-line wrapper
[`bench/kissat/kissat_cli.c`](bench/kissat/kissat_cli.c). Both `--module FullM6` (`382` fns,
matching `kissatM6_compiled_{x64,arm64}.code`) and `--module FullM5` (`270` fns, script default)
build **certified** binaries without `--allow-uncertified`. The WP-verified next-generation
modules (`--module FullM7Plus`, `--module FullM7Fidelity`, and `--module FullM7`) are fail-closed
and require `--allow-uncertified` until their machine-code `LinkedCert`s land.

```bash
# Certified FullM6 (382 fns, primary certified solver) on x86-64 and AArch64
bash bench/kissat/build_solver.sh --module FullM6 --arch x64 -o /tmp/kissat-leanqbe-fullm6
bash bench/kissat/build_solver.sh --module FullM6 --arch arm64 -o /tmp/kissat-leanqbe-fullm6-arm64

# Certified FullM5 (270 fns, SAT+UNSAT machine-code proofs; default --module)
bash bench/kissat/build_solver.sh --module FullM5 --arch x64 -o /tmp/kissat-leanqbe-fullm5
bash bench/kissat/build_solver.sh --module FullM5 --arch arm64 -o /tmp/kissat-leanqbe-fullm5-arm64

# WP-verified next-generation solvers (uncertified native codegen until LinkedCerts land)
bash bench/kissat/build_solver.sh --module FullM7Plus --allow-uncertified --arch x64 -o /tmp/kissat-leanqbe-m7plus
bash bench/kissat/build_solver.sh --module FullM7Fidelity --allow-uncertified --arch x64 -o /tmp/kissat-leanqbe-m7fid

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

The emitted assembly matches the `LinkedCert` only for certified modules (`FullM6`, `FullM5`)
built with the default settings (`--inline-max 0`). The options `--inline-max <N>` with `N > 0`
and `--debug` change the generated code and print a warning; binaries built with them, or with
`--allow-uncertified`, are not covered by machine-code proofs.

Tests and proofs:

```bash
# Builds FullM5 and FullM6 (certified) plus FullM7 (--allow-uncertified) for x86-64 and AArch64
# and checks certification gating, exit codes, DIMACS models, -n, stdin, and workspace guard pages.
bash test/kissat/test_cli_solver.sh

# Machine-code and source/IR audit files for FullM6, FullM5, FullM7Plus, and FullM7Fidelity.
lake build --wfail LeanQbeTest.T.KissatAuditSpec \
  LeanQbeTest.T.KissatM6AuditX64 LeanQbeTest.T.KissatM6AuditArm64 \
  LeanQbeTest.T.KissatM6ProofTest LeanQbeTest.T.KissatM6SatSoundTest \
  LeanQbeTest.T.KissatAuditX64 LeanQbeTest.T.KissatAuditArm64 \
  LeanQbeTest.T.KissatM5Test LeanQbeTest.T.KissatSatSoundTest \
  LeanQbeTest.T.KissatM7PlusAuditSpec LeanQbeTest.T.KissatM7PlusAssemblyTest \
  LeanQbeTest.T.KissatM7FidelityAuditSpec LeanQbeTest.T.KissatM7FidelityCoreTest
```

### What is proved

The audit files restate the main theorems with full types:

- **FullM6 (`382` functions, certified machine code):**
  [`KissatM6AuditX64.lean`](LeanQbeTest/T/KissatM6AuditX64.lean) and
  [`KissatM6AuditArm64.lean`](LeanQbeTest/T/KissatM6AuditArm64.lean) audit the compiled x86-64 and
  AArch64 machine-code UNSAT soundness and non-vacuity theorems from
  [`Amd64/KissatM6.lean`](LeanQbe/T/Amd64/KissatM6.lean) and
  [`Arm64/KissatM6.lean`](LeanQbe/T/Arm64/KissatM6.lean).
  [`KissatM6ProofTest.lean`](LeanQbeTest/T/KissatM6ProofTest.lean) audits the 382-function
  source-level `ModuleOk`, soundness, and UNSAT non-vacuity proofs
  ([`FullM6Proof.lean`](LeanQbe/T/Examples/Kissat/FullM6Proof.lean)), and
  [`KissatM6SatSoundTest.lean`](LeanQbeTest/T/KissatM6SatSoundTest.lean) audits the source-level
  proof combinators. Audited headline list:
  [`scripts/headlines.d/kissat_m6.txt`](scripts/headlines.d/kissat_m6.txt) (49 theorems).
- **FullM5 (`270` functions, certified machine code):**
  [`KissatAuditX64.lean`](LeanQbeTest/T/KissatAuditX64.lean) and
  [`KissatAuditArm64.lean`](LeanQbeTest/T/KissatAuditArm64.lean) re-export the machine-code audits
  for `FullM5` from [`KissatM5AuditX64.lean`](LeanQbeTest/T/KissatM5AuditX64.lean),
  [`KissatM5AuditArm64.lean`](LeanQbeTest/T/KissatM5AuditArm64.lean),
  [`KissatM5SoundAuditX64.lean`](LeanQbeTest/T/KissatM5SoundAuditX64.lean), and
  [`KissatM5SoundAuditArm64.lean`](LeanQbeTest/T/KissatM5SoundAuditArm64.lean)
  ([`scripts/headlines.d/kissat_m5.txt`](scripts/headlines.d/kissat_m5.txt), 49 theorems);
  [`KissatM5Test.lean`](LeanQbeTest/T/KissatM5Test.lean) and
  [`KissatSatSoundTest.lean`](LeanQbeTest/T/KissatSatSoundTest.lean) cover source-level `ModuleOk`,
  SAT and UNSAT soundness, and a concrete SAT non-vacuity example.
- **FullM7Plus (`410` functions, source & PGO-inlined WP):**
  [`KissatM7PlusAuditSpec.lean`](LeanQbeTest/T/KissatM7PlusAuditSpec.lean) and
  [`KissatM7PlusAssemblyTest.lean`](LeanQbeTest/T/KissatM7PlusAssemblyTest.lean) audit the closed
  `0`-hook `ModuleOk` ([`audit_m7p_mod_ok`](LeanQbeTest/T/KissatM7PlusAuditSpec.lean#L110)),
  `m7InlPolicy` PGO-inlined equivalence and `ModuleOk`
  ([`audit_m7p_inl_ok`](LeanQbeTest/T/KissatM7PlusAuditSpec.lean#L136)), source & inlined
  `Func.wp` UNSAT soundness ([`audit_m7p_unsat`](LeanQbeTest/T/KissatM7PlusAuditSpec.lean#L142),
  [`audit_m7p_inl_wp`](LeanQbeTest/T/KissatM7PlusAuditSpec.lean#L192)), concrete `8,192 B` UNSAT
  non-vacuity ([`audit_m7p_nv`](LeanQbeTest/T/KissatM7PlusAuditSpec.lean#L217),
  [`audit_m7p_inl_nv`](LeanQbeTest/T/KissatM7PlusAuditSpec.lean#L232)), and 4-ISA legalization
  guards (`aarch64`, `scalar64`, `x64AVX2`, `x64AVX512`). Audited headline list:
  [`scripts/headlines.d/kissat_m7_plus_spec.txt`](scripts/headlines.d/kissat_m7_plus_spec.txt)
  (33 constants/theorems). No machine-code `LinkedCert` is claimed here.
- **FullM7Fidelity (`413` functions, source & PGO-inlined WP):**
  [`KissatM7FidelityAuditSpec.lean`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean) audits the
  closed `0`-hook `ModuleOk` ([`m7f_mod_ok`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean#L113)),
  `m7InlPolicy` PGO-inlined equivalence and `ModuleOk`
  ([`m7f_inl_ok`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean#L139)), source & inlined `Func.wp`
  UNSAT soundness ([`m7f_unsat`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean#L146),
  [`m7f_inl_wp`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean#L196)), and concrete `8,192 B` UNSAT
  non-vacuity ([`m7f_nv`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean#L222),
  [`m7f_inl_nv`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean#L237)).
  [`KissatM7FidelityCoreTest.lean`](LeanQbeTest/T/KissatM7FidelityCoreTest.lean) separately audits
  the `9`-fn standalone / `412`-fn spliced `FullM7FidelityCore` subsystem
  ([`fidCorePatched_moduleOk`](LeanQbe/T/Examples/Kissat/FullM7FidelityCoreProof.lean#L1364)).
  Audited headline list:
  [`scripts/headlines.d/kissat_m7_fidelity_spec.txt`](scripts/headlines.d/kissat_m7_fidelity_spec.txt)
  (24 constants/theorems). No machine-code `LinkedCert` is claimed here.
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
- Source & PGO-inlined IR (`FullM7Plus` and `FullM7Fidelity` UNSAT):
  [`audit_m7p_nv`](LeanQbeTest/T/KissatM7PlusAuditSpec.lean#L217) /
  [`audit_m7p_inl_nv`](LeanQbeTest/T/KissatM7PlusAuditSpec.lean#L232) and
  [`m7f_nv`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean#L222) /
  [`m7f_inl_nv`](LeanQbeTest/T/KissatM7FidelityAuditSpec.lean#L237) show deterministic `Func.wp`
  executions returning `20` on `8,192 B` `nvM6UnsatInitMem` (`XPost := False`) on both the
  un-inlined and `m7InlPolicy`-inlined modules.

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

The following are not trusted for certified binaries (`FullM6` and `FullM5`), because they are
checked by the Lean kernel: the C0 solver sources, the C0 elaborator, the inlining policy and its
materialization, every compiler pass (optimization, legalization, register allocation, instruction
selection, and linking), and all `Func.wp` proofs. For `FullM7Plus` and `FullM7Fidelity`, the
source C0, `m7InlPolicy` materialization, and `Func.wp` UNSAT proofs are kernel-checked on `main`,
while native code generation remains outside the certified TCB until their dual-arch `LinkedCert`s
land.

### Benchmarks and differential testing

The repository contains a multi-tier benchmarking and differential testing suite under
[`bench/kissat/`](bench/kissat/) and [`test/kissat/`](test/kissat/) to validate solver
correctness, isolate compiler overhead, and prevent performance regressions:

| Harness | Suite / Corpus | What it checks | Supported modules |
|---|---|---|---|
| [`compare_4way_min.py`](bench/kissat/compare_4way_min.py) | Any positional `.cnf` files, `--cnf-dir`, or `--manifest` (`--limit N`) | **Minimal (`<= 160`-line) auditable 4-way script**: prints every exact compile/link command, invokes `Driver.compileFns` directly (no parallel shim), runs sequentially in rotated order, checks `C1` DIMACS models + `bench_main.c` models/slack + `0` disagreements, reports AM/GM/PAR-2/`.text` | `FullM6` (default), `FullM7Plus`, `FullM7Fidelity`, `FullM5` |
| [`run_4way_stage1.py`](bench/kissat/run_4way_stage1.py) | Stage-1 `140` unique CNFs (`PV-35`: 35 [13S/22U], `Hard-24`: 24 [4S/20U], `SV-21`: 21 [13S/8U], `quick60`: 60 [28S/32U]; 58 SAT / 82 UNSAT) | Full parallel Stage-1 4-way harness (`C1` vs `C0-direct` vs `C3b` vs `C4`), `0` verdict disagreements, 100% SAT DIMACS model verification, 35-key bit-exact C0 telemetry parity, JSON/Markdown reports, `.text` & non-NOP instruction counts | `FullM5`, `FullM6` (default), `FullM7`, `FullM7Plus`, `FullM7Fidelity` |
| [`test_cli_solver.sh`](test/kissat/test_cli_solver.sh) | 10 built-in SAT/UNSAT/UNKNOWN/guard-page CNFs (incl. 32-var 128-clause canary) | `--allow-uncertified` gating, certified x86-64 & AArch64 (`qemu-aarch64`) builds, DIMACS `v ... 0` model validation, `-n`/`--no-model`, stdin `-`, tight 1 MB guarded workspace | `FullM5`, `FullM6` (certified); `FullM7` (`--allow-uncertified`) |
| [`check_canaries.py`](bench/kissat/check_canaries.py) + [`gen_canary_cnfs.py`](bench/kissat/gen_canary_cnfs.py) | 34 base / 40 total (`--include-c11`) mathematically UNSAT canaries across 10–11 stress families (`01_php_bva`–`11_c11_regressions`) | Ratchet checks against [`canary_baseline.json`](bench/kissat/canary_baseline.json), bit-identical `C4 == C3b` work parity, regression ceilings vs `C1` | `Full`, `FullFast`, `FullM3`–`FullM6`, arbitrary `--c3b-gen-hpp` |
| [`diff_telemetry.py`](bench/kissat/diff_telemetry.py) + [`diff_lockstep.py`](bench/kissat/diff_lockstep.py) + [`run_c11_guardrails.sh`](bench/kissat/run_c11_guardrails.sh) | Canary & custom CNF suites (`bench_main.c` `--full-telemetry-m2` / `--extended-telemetry-m2`) | 26 standard + 31 extended telemetry metrics vs upstream Kissat 4.0.4 (`C1`); lockstep event-trace first-divergence bisection (`DEC`, `CONFL`, `LEARN`, `RST`, `MODE`, `RED`, `INPROC`, `UNIT0`, `END`) | Any C0 solver build (`C3b` / `C4`) |
| [`fuzz_oom_witness.py`](test/kissat/fuzz_oom_witness.py) + [`gen_inproc_cnfs.py`](bench/kissat/gen_inproc_cnfs.py) + [`gen_cnfs.py`](bench/kissat/gen_cnfs.py) | `316` inprocessing stress CNFs (9 families) + `45` structured CNFs | Workspace capacity boundary fuzzing (`arena`, `watch_stk`, `extend_stk`, `scratch_buf`), safe OOM return (`0`), zero SAT/UNSAT flips, structural invariants ([`check_c3b_invariants.hpp`](test/kissat/check_c3b_invariants.hpp)) | `C3b` / `C4` builds |
| [`run_4corner.sh`](bench/kissat/run_4corner.sh), [`run_full.sh`](bench/kissat/run_full.sh), [`run_plain.sh`](bench/kissat/run_plain.sh), [`run.sh`](bench/kissat/run.sh), [`test/kissat/run.sh`](test/kissat/run.sh) | 10-family canaries, 181-CNF Stage 2/3, 300+ CNF Stage 4 differential suites | Differential verification across pure Lean, PrintCpp ASan/UBSan, x86-64, AArch64 QEMU, stock QBE, and upstream Kissat | Earlier stages (`Solver`, `CorePlus`, `Plain`, `Full`, `FullFast`, `FullM3`, `FullM4`) |

#### Reproducible 4-way performance benchmark

Two companion scripts build and evaluate the same four x86-64 corners against an identical C
driver ([`bench/kissat/bench_main.c`](bench/kissat/bench_main.c) with `PROT_NONE` guard pages,
`0xAA` slack checks, and full DIMACS clause verification):

- **[`bench/kissat/compare_4way_min.py`](bench/kissat/compare_4way_min.py)** (*recommended for
  independent auditing*): a self-contained, plain-stdlib Python script (`<= 160` lines) that
  prints every exact compile and link command, calls `Driver.compileFns` directly (matching
  `LinkedCert.code` with no custom parallel shim), runs CNFs sequentially in rotated order
  `(i + j) % 4` with zero parallel contention, independently verifies every `C1` SAT model in
  Python, and prints per-CNF timings, `size .text`, PAR-2, and pairwise ratios.
- **[`bench/kissat/run_4way_stage1.py`](bench/kissat/run_4way_stage1.py)**: the full parallel
  Stage-1 (`140`-CNF) harness adding `--jobs N` concurrency, per-suite breakdowns, 35-key
  bit-exact C0 telemetry parity verification, and structured JSON/Markdown report generation.

The four corners separate algorithm/layout differences, IR lowering, and verified backend code
generation:

- **`C1`**: upstream Kissat 4.0.4 compiled with `clang -O3`.
- **`C0-direct`**: the identical C0 solver source extracted directly to C99
  ([`extract_c0_direct.py`](bench/kissat/extract_c0_direct.py) /
  [`build_c0_direct.sh`](bench/kissat/build_c0_direct.sh), verified 1-to-1 against Lean via
  `--check-fns lean`) and compiled with `clang -std=c99 -O3 -fwrapv -fno-strict-aliasing`.
- **`C3b`**: the same module lowered to `LeanQbe.T` and emitted via `PrintCpp`
  (`-DTQBE_NATIVE_MEM`), compiled with `clang++ -std=c++20 -O3`.
- **`C4`**: the same module compiled by LeanQbe's x86-64 pipeline (`toATTAligned`, linked
  `-no-pie`). For `FullM6` (`FullM6Inl.m6InlFns`) and `FullM5` (`InlinePolicy.b5`), `C4` matches
  the kernel-checked `LinkedCert` assembly; for `FullM7Plus` (`FullM7PlusInl.m7PlusInlFns`) and
  `FullM7Fidelity` (`FullM7FidelityInl.m7FidInlFns`), `C4` exercises the WP-verified PGO-inlined
  IR while dual-arch `LinkedCert`s are in progress.

Pairwise ratios decompose the end-to-end runtime gap (`C4 / C1`) into three orthogonal stages:

1. **`C0-direct / C1`** — C0 source & SoA data-layout differences vs upstream Kissat 4.0.4 (`clang -O3` on both).
2. **`C3b / C0-direct`** — `C0 -> LeanQbe.T -> PrintCpp` IR lowering overhead (`clang++ -O3` vs `clang -O3`).
3. **`C4 / C3b`** — verified LeanQbe backend codegen (optimization, register allocation, instruction selection) vs `clang++ -O3`.
4. **`C4 / C0-direct`** — total LeanQbe compiler overhead vs `clang -O3` on identical C0 source (`≈ (C3b / C0-direct) × (C4 / C3b)`).

Every C0-derived run checks **35-key bit-exact telemetry parity** (`C0-direct == C3b == C4` via
`--full-telemetry-m2`): `status`, `conflicts`, `learned_lits`, `min_removed`, `num_irred`,
`num_redundant`, `num_binary`, `switched`, `search_ticks`, `rephased`, `reductions`, `tier1`,
`tier2`, `restarts`, `oom`, `max_vars`, `cur_vars`, `unassigned`, `otfs`, `eager_sub`,
`probings`, `eliminations`, `elim_bound`, `hbr`, `trans`, `viv`, `subst`, `cong`, `sweep`, `bve`,
`bce`, `bva`, `walks`, `last_probe_ticks`, and `last_elim_ticks`.

```bash
# Minimal (<= 160-line) auditable 4-way comparison on any .cnf files, directory, or Stage-1 manifest.
# Prints every exact compile/link command and runs sequentially in rotated order with zero contention.
python3 bench/kissat/compare_4way_min.py --module FullM6 --c1 /path/to/kissat --timeout 30 a.cnf b.cnf
python3 bench/kissat/compare_4way_min.py --module FullM6 --c1 /path/to/kissat \
  --manifest /path/to/manifest_stage1.json --limit 6

# Full parallel Stage-1 (140-CNF) 4-way benchmark + 35-key telemetry parity for certified FullM6.
# Pass --manifest <stage1.json> and --c1-bin <kissat-4.0.4> (or set STAGE1_MANIFEST / KISSAT_C1_BIN),
# since external Stage-1 CNF benchmarks and the upstream Kissat binary are not committed in git.
python3 bench/kissat/run_4way_stage1.py --module FullM6 --jobs 8 \
  --out-json /tmp/m6_4way.json --out-md /tmp/m6_4way.md

# Same 4-way harness on WP-verified next-gen modules (uncertified native codegen; add --limit 2 for a quick parity smoke test)
python3 bench/kissat/run_4way_stage1.py --module FullM7Plus --jobs 8 --limit 2 \
  --out-json /tmp/m7plus_smoke.json --out-md /tmp/m7plus_smoke.md
python3 bench/kissat/run_4way_stage1.py --module FullM7Fidelity --jobs 8 --limit 2 \
  --out-json /tmp/m7fid_smoke.json --out-md /tmp/m7fid_smoke.md

# Standalone direct C0-to-C99 extraction with 1-to-1 ordered function-name parity check against Lean
python3 bench/kissat/extract_c0_direct.py --target m6 --out /tmp/m6_direct.c --check-fns lean
python3 bench/kissat/extract_c0_direct.py --target m7plus --out /tmp/m7plus_direct.c --check-fns lean
python3 bench/kissat/extract_c0_direct.py --target m7fidelity --out /tmp/m7fid_direct.c --check-fns lean
```

##### Certified `FullM6` (`382` fns, `kissatM6_compiled_x64`) — Stage-1 140-CNF results

**Environment and methodology:** Measured on commit `b200244a` across the Stage-1 suite of `140`
unique CNFs (`PV-35`: 35, `Hard-24`: 24, `SV-21`: 21, `quick60`: 60), `30.0 s` per-CNF timeout
(`60.0 s` PAR-2 penalty), `20.0 ms` floor for geometric means, `2,000,000,000` fuel, `--jobs 8`,
and interleaved per-CNF engine order on Intel Xeon @ 2.60 GHz (`48` vCPUs, `clang`/`clang++`
21.1.8, start loadavg `7.62, 6.52, 4.97`). Every SAT assignment passed DIMACS verification with
**0** soundness/model errors, **0** cross-solver verdict disagreements, and **130/130** bit-exact
35-key telemetry parity (`0` diffs across `C0-direct == C3b == C4`).

| Engine | Solved (`S/U`) | TO | Common Wall AM / GM (ms) | Common Int AM / GM (ms) | All-140 PAR-2 AM (s) / GM (ms) | Linked `.text` (B) / Non-NOP Insns | `vs C0-direct` (W-GM / I-GM) | `vs C3b` (W-GM / I-GM) | `vs C1` (W-GM / I-GM) |
|---|---|---:|---:|---:|---:|---:|---|---|---|
| `C1` (Kissat 4.0.4, `clang -O3`) | `135/140` (`54S/81U`) | 5 | `970.1 / 252.0` | `952.0 / 232.0` | `3.570 / 357.7` | `373,722 / 92,883` | — | — | — |
| `C0-direct` (`FullM6` C99, `clang -O3`) | `132/140` (`52S/80U`) | 8 | `1217.5 / 267.8` | `1191.0 / 242.5` | `5.001 / 400.6` | `249,464 / 60,963` | `1.0000x / 1.0000x` | — | `1.0783x / 1.0605x` |
| `C3b` (`FullM6` PrintCpp, `clang++ -O3`) | `131/140` (`52S/79U`) | 9 | `1304.1 / 278.7` | `1285.1 / 255.4` | `5.342 / 418.3` | `215,960 / 52,430` | `1.0402x / 1.0526x` | `1.0000x / 1.0000x` | `1.1215x / 1.1161x` |
| **`C4` (`FullM6`, certified LeanQbe x64)** | `131/140` (`51S/80U`) | 9 | `1420.3 / 295.3` | `1394.9 / 275.0` | `5.502 / 442.3` | `206,024 / 49,848` | **`1.1025x / 1.1337x`** | **`1.0599x / 1.0771x`** | **`1.1723x / 1.1856x`** |

*(Common Wall/Int AM and GM are over the strict 129-instance 4-way common-solved subset; pairwise
ratios are over each pair's mutually solved subset. One borderline `PV-35` instance
`hw_ibm_2004_01_k90_sat` timed out at `30.0 s` on `C4` in this run and solved in `24.7 s` on prior
repeats on identical `FullM6` code, where `C4` solved `132/140` with `C4 / C0-direct` `1.09–1.10x`
and `C4 / C1` `1.19–1.21x` W-GM. Object `.text` sizes are `241,541 B` `C0-direct`, `208,036 B`
`C3b`, and `198,090 B` `C4` with `1,139,941 B` `.s` assembly emitted in `7.98 s`.)*

Per-suite breakdown for certified `FullM6` (`C4` vs `C0-direct` / `C3b` / `C1`, mutually solved
Wall GM / Int GM):

| Suite (`N`, 4-way common) | `C1` Solved | `C4` Solved | `C4` PAR-2 AM (s) | `C4 / C0-direct` (W-GM / I-GM) | `C4 / C3b` (W-GM / I-GM) | `C4 / C1` (W-GM / I-GM) |
|---|---:|---:|---:|---|---|---|
| `PV-35` (`35`, `34`) | `35/35` | `34/35` | `3.203` | `1.0984x / 1.1177x` | `1.0711x / 1.0663x` | `1.1286x / 1.1236x` |
| `Hard-24` (`24`, `24`) | `24/24` | `24/24` | `0.757` | `1.1054x / 1.0912x` | `1.0450x / 1.0356x` | `0.9107x / 0.8921x` |
| `SV-21` (`21`, `21`) | `21/21` | `21/21` | `0.658` | `0.9722x / 1.1358x` | `0.9922x / 1.0953x` | `1.0135x / 1.0926x` |
| `quick60` (`60`, `50`) | `55/60` | `52/60` | `10.438` | `1.1613x / 1.1636x` | `1.0886x / 1.0969x` | `1.4377x / 1.4530x` |
| **OVERALL** (`140`, `129`) | **`135/140`** | **`131/140`** | **`5.502`** | **`1.1025x / 1.1337x`** | **`1.0599x / 1.0771x`** | **`1.1723x / 1.1856x`** |

Gap attribution on mutually solved Stage-1 CNFs (`FullM6` on `b200244a`):
- C0 source & SoA data layout vs upstream Kissat (`C0-direct / C1`): `1.0783x` Wall GM / `1.0605x` Int GM (`1.3449x` Wall AM).
- `C0 -> LeanQbe.T -> PrintCpp` IR lowering (`C3b / C0-direct`): `1.0402x` Wall GM / `1.0526x` Int GM (`1.0630x` Wall AM).
- LeanQbe verified backend codegen vs `clang++ -O3` (`C4 / C3b`): `1.0599x` Wall GM / `1.0771x` Int GM (`1.0891x` Wall AM).
- Total verified compiler overhead vs `clang -O3` on identical C0 (`C4 / C0-direct`): `1.1025x` Wall GM / `1.1337x` Int GM (`1.1539x` Wall AM).
- On All-140 PAR-2 (`30.0 s` cap, `60.0 s` penalty), `C4` is `1.1003x` AM (`1.1040x` GM) vs `C0-direct`, `1.0300x` AM (`1.0573x` GM) vs `C3b`, and `1.5412x` AM (`1.2366x` GM) vs `C1`.

##### Code size, emission, and parity summary across active modules (`b200244a`)

For the WP-verified next-generation modules (`FullM7Plus` and `FullM7Fidelity`), full 140-CNF
wall-clock tables will be published once their dual-arch `LinkedCert`s land; deterministic x86-64
code-size, emission, and smoke-parity metrics verified directly on `b200244a` are:

| Target | Verification status | Fns | `C4` Emit Time / `.s` (B) | `C4` Linked `.text` (B) / Non-NOP Insns | `C0-direct` Linked `.text` (B) / Insns | `C3b` Linked `.text` (B) / Insns | Parity check on `b200244a` |
|---|---|---:|---:|---:|---:|---:|---|
| `C1` (Kissat 4.0.4, `clang -O3`) | Upstream reference | — | — | — | `373,722 / 92,883` *(ref)* | — | Reference solver |
| **`FullM6`** (`m6InlPolicy`) | **Certified x86-64 & AArch64 `LinkedCert`** | `382` | `7.98 s / 1,139,941` | `206,024 / 49,848` | `249,464 / 60,963` | `215,960 / 52,430` | `382/382` fn parity; `130/130` 140-CNF 35-key bit-exact (`0` diffs) |
| **`FullM7Plus`** (`m7InlPolicy`) | WP + PGO-inlined IR (`LinkedCert` pending) | `410` | `12.20 s / 1,458,034` | `259,208 / 63,488` | `262,616 / 64,978` | `225,832 / 55,366` | `410/410` fn parity; `2/2` `--limit 2` 35-key bit-exact (`0` diffs) |
| **`FullM7Fidelity`** (`m7InlPolicy`) | WP + PGO-inlined IR (`LinkedCert` pending) | `413` | `12.12 s / 1,466,178` | `260,792 / 63,876` | `265,224 / 65,582` | `227,928 / 55,859` | `413/413` fn parity; `2/2` `--limit 2` 35-key bit-exact (`0` diffs) |

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
| `bench/kissat/` | Solver CLI wrapper, build scripts, minimal auditable 4-way script (`compare_4way_min.py`), full Stage-1 benchmark harness (`run_4way_stage1.py`), direct C0-to-C99 extractor (`extract_c0_direct.py`), CNF generators, canary ratchet, telemetry diff, and lockstep trace tools |
| `test/kissat/` | CLI solver integration tests (`test_cli_solver.sh`), differential tests (`run.sh`), OOM/witness saturation fuzzer (`fuzz_oom_witness.py`), and IR emission helpers |
| `scripts/` | [`check.sh`](scripts/check.sh), [`tier3_check.sh`](scripts/tier3_check.sh), hub and import checks, theorem lists (`headlines.d/`) |
| `docs/reports/` | Design notes on individual components |
