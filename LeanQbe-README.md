# lean-qbe: the verified `LeanQbe.T` compiler and verified workloads

`LeanQbe.T` is a typed SSA intermediate language with a weakest-precondition program logic
(`Func.wp`) and an optimizing compiler to x86-64 (SysV) and AArch64 (AAPCS64), written and
verified in Lean 4 (`leanprover/lean4:nightly-2026-11-08`). Programs are written in **C0**, a
small C subset elaborated into `LeanQbe.T` by a Lean macro. The compiler produces a
kernel-checked certificate (`LinkedCert`) relating every source function's `Func.wp` spec to
its machine code under the Kraken x86-64 / AArch64 instruction semantics.

## Verified workstreams and theorem-auditing index

Each workstream has audit files under `LeanQbeTest/T/`, `LeanQbeBootstrap0Test/`, or
`LeanQbeLegacyTest/` that restate headline theorems with unabbreviated types, explain every
hypothesis and TCB assumption, and end with one-line `#print axioms` reports (standard axioms
`[propext, Classical.choice, Quot.sound]` only). Architecture-specific audits are split so no
module imports both `Kraken.X64` and `Kraken.AArch64`.

| # | Workstream | What is audited | Audit files |
|---|---|---|---|
| 1 | **Verified Kissat SAT solver** (`D-Full M5` active default; `D-Full M6` source/inlining landed) | SAT+UNSAT model soundness (`readModelFromWork`) + closed UNSAT NV ([details](#verified-kissat)) | [Spec](LeanQbeTest/T/KissatAuditSpec.lean), [X64](LeanQbeTest/T/KissatAuditX64.lean), [Arm64](LeanQbeTest/T/KissatAuditArm64.lean), [M5X64](LeanQbeTest/T/KissatM5AuditX64.lean), [M5Arm64](LeanQbeTest/T/KissatM5AuditArm64.lean), [M5SoundX64](LeanQbeTest/T/KissatM5SoundAuditX64.lean), [M5SoundArm64](LeanQbeTest/T/KissatM5SoundAuditArm64.lean), [SatSound](LeanQbeTest/T/KissatSatSoundTest.lean), [M6Sat](LeanQbeTest/T/KissatM6SatSoundTest.lean), [Legacy](LeanQbeLegacyTest/KissatM4LegacyAuditX64.lean) |
| 2 | **Compiler, pipeline & linker** | Mid-end, policy/chunked inlining, loop/memory/flag-register passes, `LinkedCert`, `LinkRec`/`LinkScc` ([details](#compiler-optimization-and-lowering-pipeline)) | [Spec](LeanQbeTest/T/CompilerAuditSpec.lean), [X64](LeanQbeTest/T/CompilerAuditX64.lean), [Arm64](LeanQbeTest/T/CompilerAuditArm64.lean) |
| 3 | **Impure Lean 4 `LCNF`/`LeanLRC`** | Structural `Fn.Wf` of `LeanQbe/T/LeanLCNF` and `LeanQbe/T/LeanLRC` lowering into `LeanQbe.T` | [Audit](LeanQbeTest/T/LcnfAudit.lean) |
| 4 | **Native LRAT proof checker** | `lrat_check_bytes` returns `1` only for valid DIMACS of an unsatisfiable CNF | [Spec](LeanQbeTest/T/LratAuditSpec.lean), [X64](LeanQbeTest/T/LratAuditX64.lean), [Arm64](LeanQbeTest/T/LratAuditArm64.lean) |
| 5 | **Crypto, bignum & pointer code** | `ChaCha20` SIMD, Curve25519 `Bignum`, and `UnionFind` source and machine-code proofs | [Spec](LeanQbeTest/T/WorkloadsAuditSpec.lean), [X64](LeanQbeTest/T/WorkloadsAuditX64.lean), [Arm64](LeanQbeTest/T/WorkloadsAuditArm64.lean) |
| 6 | **C0 frontend & proof tooling** | `Func.wp` rules, C0 elaborator/`Wf`, `C0HeadStep`/`C0Agrees`, `SepTree`/`SlabChain`/`C0Lens` | [Audit](LeanQbeTest/T/C0LogicAudit.lean) |
| 7 | **Wasm SFI memory sandbox** | `validateModule`, `WasmMemInv` SFI bounds, host frame `R` preservation (x64 & Arm64) | [Spec](LeanQbeTest/T/WasmAuditSpec.lean), [X64](LeanQbeTest/T/WasmAuditX64.lean), [Arm64](LeanQbeTest/T/WasmAuditArm64.lean) |
| 8 | **Bootstrapping (`Stage A`–`C`)** | `leanqbe0Cert`, `Sound0`/`Codec0`/`PrintDir0`/`PrintAsm0`, `StageC` runs ([details](#bootstrapping-stage-a-to-stage-c)) | [Bootstrap0](LeanQbeBootstrap0Test/Bootstrap0Audit.lean), [Codec0](LeanQbeBootstrap0Test/Codec0Test.lean), [PrintDir0](LeanQbeBootstrap0Test/PrintDir0Test.lean), [PrintAsm0](LeanQbeTest/T/PrintAsm0Test.lean), [Sound0](LeanQbeBootstrap0Test/Sound0Test.lean), [StageC](LeanQbeBootstrap0Test/StageCTest.lean) |

Check all active audit files (also built by `scripts/check.sh`):

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

[`scripts/check.sh`](scripts/check.sh) builds active targets (including `LeanQbeBootstrap0` and
`LeanQbeBootstrap0Test` in `full` and `x64` scopes) with warnings as errors, scans tracked
`.lean` files for `sorry`, `admit`, non-meta `axiom `, `@[implemented_by]`, `@[extern]`,
`trustCompiler`, and native-code tactics (`native_decide`, `bv_decide`, `ofReduceBool`, …), checks
architecture and active-vs-legacy import closures, enforces module-boundary firewall rules
(`L1`–`L4`: `MainLemmas`, `Targ`, `TargLemmas`, and `Main`/`Isa`) and 15 synchronized barrel/hub
files (`1028` tracked modules), and audits `#print axioms` across the build and
[`scripts/headlines.d`](scripts/headlines.d). Run
`INCLUDE_LEGACY=1 ./scripts/check.sh` or [`scripts/tier3_check.sh`](scripts/tier3_check.sh) to
also build and audit the retired `LeanQbeLegacy*` targets.

## Compiler optimization and lowering pipeline

Cross-checked against [`Opt.lean`](LeanQbe/T/Opt.lean) and [`Main.lean`](LeanQbe/T/Main.lean)
(Workstream #2, audited in [`CompilerAuditSpec.lean`](LeanQbeTest/T/CompilerAuditSpec.lean),
[`CompilerAuditX64.lean`](LeanQbeTest/T/CompilerAuditX64.lean), and
[`CompilerAuditArm64.lean`](LeanQbeTest/T/CompilerAuditArm64.lean)):

### Execution order (Stage 0 to Stage 4)

1. **Stage 0 — Module-level acyclic inlining**
   (`Module.optInline` / [`Module.optInlinePolicy`](LeanQbe/T/MainInline.lean#L21)):
   - Bounded and PGO acyclic callee inlining with cold-guard, loop-duplication, and loop-free
     helper gates (`InlinePolicy.b5` at [`Inline.lean#L377`](LeanQbe/T/Inline.lean#L377),
     [`Module.inlinePolicy`](LeanQbe/T/Inline.lean#L572); proved in
     [`InlineLemmas.lean`](LeanQbe/T/InlineLemmas.lean#L683),
     [`MainInline.lean#L110`](LeanQbe/T/MainInline.lean#L110), and
     [`OptLemmas.lean#L552`](LeanQbe/T/OptLemmas.lean#L552)).
   - Kernel-checked materialization via [`inline_mod!`](LeanQbe/T/MainCertInline.lean#L566),
     plus bounded-memory chunked materialization ([`InlineChunk.lean`](LeanQbe/T/InlineChunk.lean),
     [`inline_chunk_base!`](LeanQbe/T/MainCertInlineChunk.lean#L586) / `inline_mod_chunk!` /
     `inline_mod_join!`), tested in [`InlineB5Test.lean`](LeanQbeTest/T/InlineB5Test.lean) and
     [`InlinePolicyB5Test.lean`](LeanQbeTest/T/InlinePolicyB5Test.lean).

2. **Stage 1 — Pre-`Legal` typed-IR mid-end**
   ([`Func.earlyOpt`](LeanQbe/T/Opt.lean#L198), proved in
   [`OptLemmas.lean#L281`](LeanQbe/T/OptLemmas.lean#L281), in exact execution order):
   - [`Func.fold`](LeanQbe/T/Fold.lean#L863)
     ([`FoldLemmas.lean#L2926`](LeanQbe/T/FoldLemmas.lean#L2926))
     → [`Func.canon`](LeanQbe/T/Canon.lean#L254)
       ([`CanonLemmas.lean#L829`](LeanQbe/T/CanonLemmas.lean#L829))
     → [`Func.copy`](LeanQbe/T/Copy.lean#L187)
       ([`CopyLemmas.lean#L849`](LeanQbe/T/CopyLemmas.lean#L849))
     → [`Func.gvn`](LeanQbe/T/Gvn.lean#L259)
       ([`GvnLemmas.lean#L812`](LeanQbe/T/GvnLemmas.lean#L812))
     → `Func.copy` → `Func.fold`
     → [`Func.ifOpt`](LeanQbe/T/IfOpt.lean#L345) (branch-diamond if-conversion;
       [`IfOptLemmas.lean#L1821`](LeanQbe/T/IfOptLemmas.lean#L1821))
     → [`Func.simplifyGroupFast`](LeanQbe/T/Opt.lean#L123) /
       [`Func.simplifyGroupPlan`](LeanQbe/T/SimplifyGroupPlan.lean#L449)
       ([`SimplifyGroupPlanLemmas.lean#L677`](LeanQbe/T/SimplifyGroupPlanLemmas.lean#L677))
     → [`Func.peelFast`](LeanQbe/T/Opt.lean#L132) /
       [`Func.peel`](LeanQbe/T/Peel.lean#L202)
       ([`PeelLemmas.lean#L904`](LeanQbe/T/PeelLemmas.lean#L904))
     → [`Func.zeroPeelWith`](LeanQbe/T/ZeroPeel.lean#L512) (constant-fill widening & single-iter
       peeling; [`ZeroPeelLemmas.lean#L2461`](LeanQbe/T/ZeroPeelLemmas.lean#L2461),
       [`ZeroPeelLemmas1.lean`](LeanQbe/T/ZeroPeelLemmas1.lean))
     → `Func.copy` → `Func.fold`
     → [`Func.dceP`](LeanQbe/T/DceParam.lean#L279)
       ([`DceParamLemmas.lean#L688`](LeanQbe/T/DceParamLemmas.lean#L688))
     → `Func.renorm` ([`Flat.lean`](LeanQbe/T/Flat.lean),
       [`FlatLemmas.lean#L756`](LeanQbe/T/FlatLemmas.lean#L756)).

3. **Stage 2 — Target legalization**
   ([`Func.legal`](LeanQbe/T/Legal.lean#L115),
   checked by [`LegalCheck3.lean`](LeanQbe/T/LegalCheck3.lean)
   and proved in [`LegalLemmas.lean`](LeanQbe/T/LegalLemmas.lean)):
   - Target type/opcode legalization preserving multi-word widening arithmetic chains (`addc`,
     `subb`, `umulw`).

4. **Stage 3 — Post-`Legal` typed-IR mid-end**
   ([`Func.lateOpt`](LeanQbe/T/Opt.lean#L238) / [`Fn.midStage`](LeanQbe/T/Main.lean#L56), proved
   in [`OptLemmas.lean#L430`](LeanQbe/T/OptLemmas.lean#L430), in exact execution order with
   `Fn.renorm` boundaries):
   - [`Func.lateCorePre`](LeanQbe/T/Opt.lean#L203): `Func.fold` → `Func.canon` →
     [`Func.divConst`](LeanQbe/T/DivConst.lean#L278)
     ([`DivConstLemmas.lean#L1385`](LeanQbe/T/DivConstLemmas.lean#L1385)) → `Func.copy` →
     `Func.renorm`.
   - [`Func.lateCorePost`](LeanQbe/T/Opt.lean#L207):
     [`Func.memLoad`](LeanQbe/T/MemLoad.lean#L425)
     ([`MemLoadLemmas.lean#L1761`](LeanQbe/T/MemLoadLemmas.lean#L1761)) → `Func.gvn` →
     [`Func.assumeBits`](LeanQbe/T/AssumeBits.lean#L301)
     ([`AssumeBitsLemmas.lean#L1114`](LeanQbe/T/AssumeBitsLemmas.lean#L1114)) → `Func.fold` →
     `Func.renorm`.
   - [`Func.lateCfgPre`](LeanQbe/T/Opt.lean#L217):
     [`Func.ifOptBits`](LeanQbe/T/IfOpt.lean#L354)
     ([`IfOptLemmas.lean#L1827`](LeanQbe/T/IfOptLemmas.lean#L1827)) → `Func.simplifyGroupFast` →
     [`Func.deadLoadElim`](LeanQbe/T/Dce.lean#L153)
     ([`DceLemmas.lean#L451`](LeanQbe/T/DceLemmas.lean#L451)) →
     [`Func.assumeElim`](LeanQbe/T/MemLoad.lean#L465)
     ([`MemLoadLemmas.lean#L1865`](LeanQbe/T/MemLoadLemmas.lean#L1865)) → `Func.fold` →
     `Func.gvn` → `Func.renorm`.
   - [`Func.lateCfgPost`](LeanQbe/T/Opt.lean#L222) +
     [`Func.lateLoopRotate`](LeanQbe/T/Opt.lean#L226):
     [`Func.licm`](LeanQbe/T/Licm.lean#L885)
     ([`LicmLemmas.lean#L813`](LeanQbe/T/LicmLemmas.lean#L813)) → `Func.dceP` →
     [`Func.loopRotate`](LeanQbe/T/LoopRotate.lean#L931)
     ([`LoopRotateLemmas.lean#L2863`](LeanQbe/T/LoopRotateLemmas.lean#L2863)) →
     [`Func.mergeRets`](LeanQbe/T/Opt.lean#L182)
     ([`OptLemmas.lean#L211`](LeanQbe/T/OptLemmas.lean#L211)) → `Func.renorm`.

5. **Stage 4 — Untrusted hint analysis, verified backend lowering, and linking**
   (`Spill` → `Rega` → `Isel` → `Link`):
   - **Hint oracle (`Spill` + `SpillFlags`):** [`Spill.hints`](LeanQbe/T/Spill.lean#L1968) and
     [`SpillFlags.lean`](LeanQbe/T/SpillFlags.lean) compute untrusted hints outside the TCB:
     [`Spill.Cfg`](LeanQbe/T/Spill.lean#L276) (`sink`, `joinGuard`, `cacheHint`, `regEntry`),
     hot/cold live-range splitting ([`tryEvictSplit`](LeanQbe/T/Spill.lean#L652),
     [`SpillB5Test.lean`](LeanQbeTest/T/SpillB5Test.lean)), flag-web coloring, `[base + disp]` /
     SIB elision hints, and execution-weight cold branch inversion (`invertJnz`).
   - **Verified register allocation & lowering (`Rega`):**
     [`Rega.lowerFn`](LeanQbe/T/Rega.lean#L1697) (proved in
     [`RegaLemmas4.lean#L1060`](LeanQbe/T/RegaLemmas4.lean#L1060) and `RegaLemmas1..3.lean`)
     re-checks every hint, performs x86-64 redundant `zext32 -> 64` elision
     ([`elideZext32?`](LeanQbe/T/Rega.lean#L732) & [`zeroUpper32Op`](LeanQbe/T/Target.lean#L275);
     [`X64Zext32ElideTest.lean`](LeanQbeTest/T/X64Zext32ElideTest.lean)), lowers fused
     compare-and-branch with cold-branch inversion and hot fallthrough layout
     ([`fuseJnzChoice`](LeanQbe/T/Rega.lean#L1241), [`jnzSetup`](LeanQbe/T/Rega.lean#L1260);
     [`InvertJnzTest.lean`](LeanQbeTest/T/InvertJnzTest.lean),
     [`InvertJnzArm64Test.lean`](LeanQbeTest/T/InvertJnzArm64Test.lean)), and shuffles parallel
     moves (`FlagRaOptTest.lean` / `FlagRaOptArm64Test.lean`).
   - **Target instruction selection (`Isel` / `Emit`):** `[base + disp]` (`DefFact.addImm64`),
     x86-64 SIB `[base + idx*scale + disp]` scaled-displacement addressing
     ([`recordAddVarImm`](LeanQbe/T/Rega.lean#L571) / `.addrSum`,
     [`RegaLemmas1.lean#L2267`](LeanQbe/T/RegaLemmas1.lean#L2267),
     [`addrSibScaledDispFn`](LeanQbeTest/T/FlagRaOptTest.lean#L328)), bit-ops/cselect, and
     frame/SIMD lowering ([`Amd64/Isel.lean`](LeanQbe/T/Amd64/Isel.lean),
     [`Amd64/IselLemmas5.lean#L1342`](LeanQbe/T/Amd64/IselLemmas5.lean#L1342),
     [`Arm64/Isel.lean`](LeanQbe/T/Arm64/Isel.lean),
     [`Arm64/IselLemmas4.lean#L1595`](LeanQbe/T/Arm64/IselLemmas4.lean#L1595)).
   - **Linking & kernel certificates (`Link`):** [`compileFn`](LeanQbe/T/Main.lean#L138) /
     [`compileModule`](LeanQbe/T/Main.lean#L197)
     ([`MainLemmas.lean#L728`](LeanQbe/T/MainLemmas.lean#L728)),
     compositional multi-chunk linking ([`MainLink.lean#L231`](LeanQbe/T/MainLink.lean#L231)),
     [`MainCertCore.lean`](LeanQbe/T/MainCertCore.lean) /
     [`MainCertProof.lean`](LeanQbe/T/MainCertProof.lean), cyclic recursion
     ([`LinkRecLemmas.lean#L1123`](LeanQbe/T/LinkRecLemmas.lean#L1123)), and SCC linking
     ([`LinkSccLemmas2.lean#L67`](LeanQbe/T/LinkSccLemmas2.lean#L67),
     [`LinkLfp.lean#L240`](LeanQbe/T/LinkLfp.lean#L240)).

- **Incrementality & hub discipline:** [`scripts/sync_hubs.py`](scripts/sync_hubs.py) (`--check`)
  validates the 15 pure re-export barrel/hub files across `1028` tracked modules, and
  [`scripts/check_firewall.py`](scripts/check_firewall.py) (`--require-isa`) verifies layers
  `L1`–`L4` (`MainLemmas`, `Targ`, `TargLemmas`, `Main`/`Isa`) have zero `*Lemmas*` leaks.

## Verified Kissat

**Verified Kissat** is a C0 port of the Kissat SAT solver with end-to-end machine-code soundness
theorems:

| Solver | Lean module | Fns | Status | Proved |
|---|---|---|---|---|
| `D-Full M5` | `LeanQbe.T.Examples.Kissat.FullM5` | 270 | Active default | **UNSAT (`20`) + constructive SAT (`10`)** (`InlinePolicy.b5`), x64 & Arm64, closed UNSAT NV (`KissatM5Audit*`, `KissatM5SoundAudit*`), source SAT NV |
| `D-Full M6` | `LeanQbe.T.Examples.Kissat.FullM6` | 382 | Source/inl landed | WF/acyclic, chunked [`FullM6Inl`](LeanQbe/T/Examples/Kissat/FullM6Inl.lean#L46) (`63` budgets), `FullM6OrchProof2`, [`FullM6SatSound`](LeanQbe/T/Examples/Kissat/FullM6SatSound.lean); `FullM6Proof` + `KissatM6*` certs in progress |
| `D-Full M4` | `LeanQbe.T.Examples.Kissat.FullM4` | 231 | Retired legacy | **UNSAT (`20`) + SAT (`10`) model soundness** & closed UNSAT NV, x64 & Arm64 (`KissatM4LegacyAudit*`) |
| `D-Full M3` | `LeanQbe.T.Examples.Kissat.FullM3` | 204 | Retired legacy | **UNSAT (`20`) soundness + closed UNSAT NV**, x64 & Arm64 (`KissatM3PlainLegacyAudit*`) |
| `D-Plain` | `LeanQbe.T.Examples.Kissat.Plain` | 59 | Retired legacy | **SAT (`10`) and UNSAT (`20`)** + closed SAT/UNSAT NV, x64 & Arm64 (`KissatM3PlainLegacyAudit*`) |
| `D-Full`, `M2 Fast` | `...Kissat.Full`, `...Kissat.FullFast` | 166 / 196 | Retired legacy | **UNSAT (`20`) soundness + UNSAT NV**, x64 & Arm64 (`KissatLegacyAudit*`, `INCLUDE_LEGACY=1`) |

(The superseded `FullFastSched` module has `16/173` rows proved in `KissatAuditSpec.lean` and an
undischarged `ModuleOk` hypothesis in `LeanQbeLegacyTest/`; it was superseded by `FullFast`, `M3`,
and `M5`.)

Every solver exports one C entry point:

```c
uint64_t kissat_solve_bytes(const uint8_t *cnf_ptr, uint64_t cnf_len,
                            uint8_t *work_ptr, uint64_t work_len, uint64_t fuel);
/* 20 = UNSAT, 0 = unknown; 10 = SAT (certified on M5, M4, Plain; UNSAT-only on M3, Fast, Full) */
```

### Kissat: build and run

Prerequisites: `elan` (picks up `lean-toolchain`), a C compiler, and for AArch64 on an x86-64
host `aarch64-linux-gnu-gcc` and `qemu-aarch64`.

```bash
# build_solver.sh accepts --module FullM5|FullM6|FullM7|FullM4|FullM3|Plain|Full|FullFast
# (aliases m5..m3; default FullM5, --arch x64, --inline-max 0).
# Default --inline-max 0 emits the certified policy/IR (InlinePolicy.b5 for FullM5,
# FullM6Inl.m6InlFns for FullM6, FullM7Inl.m7InlFns/m7InlPolicy for FullM7, inline=0 elsewhere).
# FullM5, FullM4 (via KissatM4Sound), and Plain build in SAT+UNSAT mode, printing
# "s SATISFIABLE" + DIMACS `v ... 0` models on exit 10 (pass -n/--no-model to suppress `v ... 0`).
bash bench/kissat/build_solver.sh --module FullM5 --arch x64 -o /tmp/kissat-leanqbe-fullm5
/tmp/kissat-leanqbe-fullm5 [--work-mb <MB>] [--fuel <N>] [-n|--no-model] <input.cnf | ->
printf 'p cnf 1 2\n1 0\n-1 0\n' | /tmp/kissat-leanqbe-fullm5 -      # s UNSATISFIABLE, exit 20
printf 'p cnf 1 1\n1 0\n'       | /tmp/kissat-leanqbe-fullm5 -      # s SATISFIABLE + v 1 0, exit 10

# AArch64 certified SAT+UNSAT build (runs under qemu-aarch64 on x86-64 hosts).
bash bench/kissat/build_solver.sh --module FullM5 --arch arm64 -o /tmp/kissat-leanqbe-fullm5-arm64
qemu-aarch64 -L /usr/aarch64-linux-gnu /tmp/kissat-leanqbe-fullm5-arm64 input.cnf

# Cert gating and uncertified options (warn on stderr and diverge from LinkedCert):
#   --module FullM6|FullM7 require KissatM6Sound/KissatM7Sound for the target arch unless
#     --allow-uncertified is passed (FullM7.lean is not yet present on this branch).
#   --module FullM3|Full|FullFast pass -DKISSAT_UNSAT_ONLY=1 (mapping r == 10 to "s UNKNOWN", exit 0).
#   --inline-max <N> (N > 0) or --debug rewrites IR/directives outside LinkedCert.

# Differential test suites (x86-64 + AArch64 + C++ ASan/UBSan, optional reference Kissat).
bash test/kissat/run.sh
bash bench/kissat/run_plain.sh
bash bench/kissat/run_full.sh --module CorePlus,Plain

# Proofs: audit active M5 theorems, then run the quality gate.
lake build --wfail LeanQbeTest.T.KissatAuditSpec LeanQbeTest.T.KissatAuditX64 \
  LeanQbeTest.T.KissatAuditArm64 LeanQbeTest.T.KissatSatSoundTest
scripts/check.sh
```

### Kissat: what is proved

Start with the active audit files (and `LeanQbeLegacyTest/` when `INCLUDE_LEGACY=1` for retired
`D-Full M4`, `D-Full M3`, `D-Plain`, `D-Full`, and `D-Full M2 Fast`). They restate headline
theorems with full types and explain each hypothesis:

- [`KissatAuditX64.lean`](LeanQbeTest/T/KissatAuditX64.lean) and
  [`KissatAuditArm64.lean`](LeanQbeTest/T/KissatAuditArm64.lean): re-export the active **`D-Full
  M5`** (`270` fns, `InlinePolicy.b5`) machine-code audit suites from
  [`KissatM5AuditX64.lean`](LeanQbeTest/T/KissatM5AuditX64.lean),
  [`KissatM5AuditArm64.lean`](LeanQbeTest/T/KissatM5AuditArm64.lean),
  [`KissatM5SoundAuditX64.lean`](LeanQbeTest/T/KissatM5SoundAuditX64.lean), and
  [`KissatM5SoundAuditArm64.lean`](LeanQbeTest/T/KissatM5SoundAuditArm64.lean) (registered in
  [`scripts/headlines.d/kissat_m5.txt`](scripts/headlines.d/kissat_m5.txt)).
- [`KissatSatSoundTest.lean`](LeanQbeTest/T/KissatSatSoundTest.lean) and
  [`KissatM6SatSoundTest.lean`](LeanQbeTest/T/KissatM6SatSoundTest.lean): audit source-level
  SAT+UNSAT soundness for `D-Full M4`/`D-Full M5` (`m4SoundEnv`, `m5SoundEnv`), M5 concrete source
  SAT non-vacuity (`m5_sat_nonvacuous`), and parameterized `M6` combinators over `FullM6Hdr`.
- [`KissatAuditSpec.lean`](LeanQbeTest/T/KissatAuditSpec.lean): audits `parseDimacs`, `CNF.Unsat`,
  `CNF.Sat`, and source contracts for `D-Plain` through `D-Full M4`.

#### `D-Full M5` (270 fns, `InlinePolicy.b5`): SAT and UNSAT, end to end

[`m5_solve_bytes_model_x64`](LeanQbe/T/Amd64/KissatM5Sound.lean#L89) /
[`m5_solve_bytes_model_arm64`](LeanQbe/T/Arm64/KissatM5Sound.lean#L88) (alongside UNSAT framing
[`m5_solve_bytes_unsat_x64`](LeanQbe/T/Amd64/KissatM5.lean#L88) /
[`m5_solve_bytes_unsat_arm64`](LeanQbe/T/Arm64/KissatM5.lean#L88)): for **any** host executable
containing the compiled 270-function `InlinePolicy.b5` module (`kissatM5_compiled_{x64,arm64}`)
and any ABI-valid call with DIMACS bytes, aligned workspace, stack budget, and caller frame `R`,
execution terminates and returns to the caller with:

- result `∈ {0, 10, 20}` (`rax` / `X0`);
- `20 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`;
- `10 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ (∃ α, cnf.Sat α) ∧
  cnf.Sat (readModelFromWork st.data.dmem work_ptr)`;
- callee-saved registers (`rbx, rbp, r12..r15` / `X19..X29`) and stack pointer restored;
- input bytes unchanged, workspace and stack frame restored as `region`s, `R` untouched.

**How SAT (`10`) is certified without verifying all of inprocessing model reconstruction:** in
[`FullM5Orch.lean#L643`](LeanQbe/T/Examples/Kissat/FullM5Orch.lean#L643), after `full_extend(h)`
runs on candidate `r == 10`, `kissat_solve_bytes_m5` restores original variable count and invokes
verified `kissat_check_model` directly against the read-only DIMACS buffer (proved by
[`kissat_solve_bytes_m5_model_wp`](LeanQbe/T/Examples/Kissat/FullSatSound.lean#L838)), returning
`10` iff every clause holds under
[`readModelFromWork`](LeanQbe/T/Examples/Kissat/FullSatSound.lean#L102) (otherwise `0`).
[`FullSatSound.lean`](LeanQbe/T/Examples/Kissat/FullSatSound.lean#L42) uses `ModuleOk.respec_tail`
to transport the `268`-function prefix (and `230`-function M4 prefix) into `m5SoundEnv` /
`m4SoundEnv` without re-proving prefix functions.

**Non-vacuity:**
- Machine code (UNSAT): [`audit_m5_x64_nv_closed`](LeanQbeTest/T/KissatM5AuditX64.lean#L137) and
  [`audit_m5_arm_nv_closed`](LeanQbeTest/T/KissatM5AuditArm64.lean#L135) instantiate arbitrary-host
  non-vacuity on the closed compiled hosts `kissatM5_compiled_x64.host` and
  `kissatM5_compiled_arm64.host` (`m5_{x64,arm64}_run_unsat` reach `r = 20`).
- Source level (SAT): [`FullM5SatNv.lean`](LeanQbe/T/Examples/Kissat/FullM5SatNv.lean#L2721)
  (`m5_sat_nonvacuous`, `m5_sat_nonvacuous_m5`, audited in
  [`KissatSatSoundTest.lean#L151`](LeanQbeTest/T/KissatSatSoundTest.lean#L151)) runs
  `"p cnf 1 1\n1 0\n"` in `Func.wp` (`XPost := False`, `4096` B workspace, `fuel = 16`), returning
  `10#64` with a verified satisfying assignment via `readModelFromWork`.

#### `D-Full M6` (382 fns, in completion) & retired legacy generations

- **`D-Full M6` (382 functions):** C0 solver source
  ([`FullM6.lean`](LeanQbe/T/Examples/Kissat/FullM6.lean#L210), `m6_acyclic`), chunked PGO
  inlining ([`FullM6Inl.lean`](LeanQbe/T/Examples/Kissat/FullM6Inl.lean#L46)), tail orchestrator
  proof [`FullM6OrchProof2.lean`](LeanQbe/T/Examples/Kissat/FullM6OrchProof2.lean#L1907), and
  SAT+UNSAT proof combinators over the `FullM6Hdr` workspace header
  ([`FullM6SatSound.lean`](LeanQbe/T/Examples/Kissat/FullM6SatSound.lean#L116),
  `readModelFromWorkM6`) are landed. Closed `FullM6Proof` assembly and generated x86-64/AArch64
  `KissatM6*` certificates (preset in [`scripts/gen_cert_slices.py`](scripts/gen_cert_slices.py))
  are in active completion.
- **Retired legacy builds (`LeanQbeLegacyTest/`, `INCLUDE_LEGACY=1`):**
  - `D-Full M4` (`231` fns): dual-arch **SAT (`10`) + UNSAT (`20`)** soundness and closed UNSAT NV
    in [`KissatM4LegacyAuditX64.lean`](LeanQbeLegacyTest/KissatM4LegacyAuditX64.lean) and
    [`KissatM4LegacyAuditArm64.lean`](LeanQbeLegacyTest/KissatM4LegacyAuditArm64.lean).
  - `D-Plain` (`59` fns, **SAT+UNSAT** + closed SAT/UNSAT NV) and `D-Full M3` (`204` fns,
    **UNSAT-only** `-DKISSAT_UNSAT_ONLY=1` + closed UNSAT NV) in
    [`KissatM3PlainLegacyAuditX64.lean`](LeanQbeLegacyTest/KissatM3PlainLegacyAuditX64.lean) and
    [`KissatM3PlainLegacyAuditArm64.lean`](LeanQbeLegacyTest/KissatM3PlainLegacyAuditArm64.lean).
  - `D-Full` (`166` fns) and `D-Full M2 Fast` (`196` fns): **UNSAT-only** soundness + NV in
    [`KissatLegacyAuditX64.lean`](LeanQbeLegacyTest/KissatLegacyAuditX64.lean) and
    [`KissatLegacyAuditArm64.lean`](LeanQbeLegacyTest/KissatLegacyAuditArm64.lean).

#### Axioms

Every audited theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. The
repository contains no `sorry`, no `admit`, no non-meta `axiom`, no `@[implemented_by]`/`@[extern]`,
and no `native_decide` / `bv_decide` / `ofReduceBool`; [`scripts/check.sh`](scripts/check.sh)
enforces this across all tracked `.lean` files.

### Kissat: trusted computing base

To believe that a default-built `kissat-leanqbe` binary (`--inline-max 0`, without `--debug`) only
prints `s UNSATISFIABLE` for unsatisfiable inputs (and, for certified SAT builds such as
`D-Full M5` / `D-Full M4` / `D-Plain`, reports SAT only for satisfiable ones) you must trust:

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
   guard pages, calls `kissat_solve_bytes`, maps `r == 10` to `s UNKNOWN` under
   `-DKISSAT_UNSAT_ONLY=1`, and otherwise prints `s SATISFIABLE` followed by DIMACS `v ... 0`
   model lines read from the workspace header unless `-n`/`--no-model` is passed) and the C
   runtime it links against.

Not trusted: the C0 solver sources, C0 elaborator, `InlinePolicy` / inlining materialization, every
`LeanQbe.T` compiler pass (optimization, legalization, register allocation, instruction selection,
linking), and all `Func.wp` proofs — all are checked by the kernel. (`--inline-max > 0`, `--debug`
via `DebugAsm`, and `--allow-uncertified` builds operate outside `LinkedCert`.)

## Bootstrapping: Stage A to Stage C

`LeanQbeBootstrap0` implements a minimal monomorphic scalar compiler (`leanqbe0Compile` in
[`LeanQbe/T/Bootstrap0/Compiler0.lean`](LeanQbe/T/Bootstrap0/Compiler0.lean)) across three
verified stages:

- **Stage A (IR + x64 cert, [`Bootstrap0Audit.lean`](LeanQbeBootstrap0Test/Bootstrap0Audit.lean)):**
  [`leanqbe0Mod0`](LeanQbe/T/Bootstrap0/Mod0.lean) (`124`-function `LeanQbe.T.Module` lowered from
  `leanqbe0Compile` via `LeanLCNF`) satisfies kernel-checked `Fn.Wf` (`leanqbe0Mod0_wf`), strict
  acyclicity (`leanqbe0Mod0_acyclic`), and `x64LegalTarget` signature legality
  (`leanqbe0Mod0_legalSig`). [`leanqbe0Cert`](LeanQbe/T/Bootstrap0/Cert.lean#L39) is a
  kernel-checked `LinkedCert` compiling all `124` functions to SysV x86-64 directives with stack
  bounds `≤ 2048` B under assumed `rtExtBounds0` (`64` per `rtExterns` C runtime entry) and exit
  symbol `["lcnf_panic"]` (`nX = 64`).
- **Stage B (compiler soundness, codec, & printers):**
  - [`Sound0.lean`](LeanQbe/T/Bootstrap0/Sound0.lean#L1360) (audited in
    [`Sound0Test.lean`](LeanQbeBootstrap0Test/Sound0Test.lean)) proves end-to-end semantic soundness
    for `leanqbe0Compile` (`leanqbe0Compile_fnSpec`, `leanqbe0Compile_sound_layout`,
    `bridge_leanqbe0Compile_fnSpec`, `bridge_leanqbe0Compile_layout`), plus closed x64 execution of
    `dummyAddMod0`, `dummyLoopMod0`, and bridged `c0_add_two`.
  - [`Codec0.lean`](LeanQbe/T/Bootstrap0/Codec0.lean)
    ([`Codec0Test.lean`](LeanQbeBootstrap0Test/Codec0Test.lean))
    proves canonical binary round-trip (`decodeMod0_encodeMod0`, `encodeMod0_decodeMod0`) and
    malformed-buffer rejection while passing the closure-free, global-free `LeanLCNF` gate.
  - [`PrintAsm0.lean`](LeanQbe/T/Amd64/PrintAsm0.lean) /
    [`PrintAsm0Lemmas.lean`](LeanQbe/T/Amd64/PrintAsm0Lemmas.lean)
    ([`PrintAsm0Test.lean`](LeanQbeTest/T/PrintAsm0Test.lean)) and
    [`PrintDir0.lean`](LeanQbe/T/Bootstrap0/PrintDir0.lean)
    ([`PrintDir0Test.lean`](LeanQbeBootstrap0Test/PrintDir0Test.lean)) prove bit-for-bit AT&T parity
    against `Kraken.X64.toATT` / `Driver.emitAsm` across `DirSubset0` and all `27` `Dir0`
    constructors with `0` closures and `0` globals.
- **Stage C ([`StageC.lean`](LeanQbe/T/Bootstrap0/StageC.lean),
  [`StageCTest.lean`](LeanQbeBootstrap0Test/StageCTest.lean)):**
  connects `Bridge0`, `Compiler0`, `Sound0`, and `PrintAsm0` to concrete x64 machine executions
  (`c0_sqr`, `c0_pipeline`, `sat_lit_{var,sign,neg}`).
- **What remains in the TCB (not yet proved):**
  - No `ModuleOk`, `FnSpec`, or `Eventually` theorem for `leanqbe0Mod0` itself (`lcnf_rt.c`
    behavior and `rtExtBounds0 = 64` / `nX = 64` are assumed).
  - `LeanLCNF` meta extraction (`lcnf_of_lean!` / `splice_lcnf_tflat!`) proves `Fn.Wf`, not
    semantic equivalence to Lean evaluation of `leanqbe0Compile`.
  - A native binary self-compilation fixpoint has not yet been executed or proved.

**File-organization & verification policy.** Modules follow conceptual boundaries (`~1k–3k` LOC
typical, shorter fine) bounded by per-file resource caps (`≤ 120s` / `≤ 300s` `*Cert*`,
`≤ 2.5 GiB` RSS, default `200k` heartbeats, `≤ 100` cols) rather than rigid line limits. Source
`Func.wp`/`ModuleOk` verification and differential testing run independently of native `LinkedCert`
compilation proofs.

## Repository layout

| Path | Contents |
|---|---|
| `LeanQbe/T/` | IR, `Func.wp` logic, compiler/inliner passes, `MainLink`/`LinkRec`/`LinkScc` proofs |
| `LeanQbe/T/Wasm/` | Phase-1 WebAssembly validator, SFI lowering, and linear-memory safety proofs |
| `LeanQbe/T/Bootstrap0/` | Stage-A `leanqbe0Compile` / `leanqbe0Cert`, Stage-B `Sound0`/`Codec0`/`PrintDir0`, Stage-C bridge |
| `LeanQbe/T/Examples/Kissat/` | C0 sources, specs, PGO policies/chunks, and `Func.wp` proofs of Kissat solvers |
| `LeanQbe/T/Amd64/`, `LeanQbe/T/Arm64/` | target instances, active `KissatM5*` certs, `PrintAsm0`, end-to-end theorems |
| `LeanQbeTest/T/`, `LeanQbeBootstrap0Test/` | tests and active audit files (at most one architecture imported per module) |
| `LeanQbeLegacyTest/` | retired `D-Full M4`, `M3`, `Plain`, `D-Full`, and `M2 Fast` audits (`INCLUDE_LEGACY=1`) |
| `bench/kissat/` | solver CLI (`kissat_cli.c`), build script, CNF generators, differential suites |
| `scripts/` | [`check.sh`](scripts/check.sh), [`tier3_check.sh`](scripts/tier3_check.sh), `sync_hubs.py`, `check_firewall.py`, `gen_cert_slices.py`, `headlines.d/` |
| `docs/reports/` | design notes per component (historical notes from earlier untyped-IR and pre-M5 milestones carry a banner) |
