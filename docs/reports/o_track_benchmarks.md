# `O-Track` Wave 3 Report: Staged Typed-IR Optimizer, Mid-End Unifications, & Benchmarks

## 1. Scope & Architecture (`o-wire` on `main @ a9503f6`)

This wave wires the full `O-M1` + `O-M2` optimizer passes into a staged kernel-checked pipeline,
resolves `#014-B1`, `#014-B2`, and `#015-B1` mid-end code-health unifications, updates all `10`
native x64/Arm64 compiler certificates and test suites, and verifies end-to-end correctness and
benchmark speedups.

### 1.1 Mid-End Code-Health Unifications (`#014-B1`, `#014-B2`, `#015-B1`)

| Ticket | Unification | Target Modules | Result |
|---|---|---|---|
| `#014-B1` | Shared `CmpOp.swap` & `swap_evalBits` / `swap_evalFloat` | `LeanQbe/T/Ops.lean`, `OpsLemmas.lean` | Removed duplicates in `Canon`, `Amd64/Isel*`, `Arm64/Isel*` |
| `#014-B2` | Shared `lift2_comm` & `lift2_assoc` | `LeanQbe/T/OpsLemmas.lean` | Removed duplicates in `CanonLemmas`, `FoldLemmas` (`1,482` LOC) |
| `#015-B1` | Shared `flattenArg`/`Args`/`Op`, `toArgTup`, `OptV`, `someTup`/`noneTup`, `argSweep` + WP/WF transport lemmas | `LeanQbe/T/OptUtil.lean` (`292` LOC), `LeanQbe/T/OptUtilLemmas.lean` (`447` LOC) | Unified `Dce*`, `Inline*`, `DivConst*`, `Peel*`, `SimplifyGroup*` (`-344` net LOC across touched files before new `OptTest`/`InlineTest`/docs) |

### 1.2 Staged Optimizer Pipeline (`LeanQbe/T/Opt.lean`, `OptLemmas.lean`, `Main.lean`, `MainLemmas.lean`, `Driver.lean`)

* **PHOAS Flatness Across Stages (`Func.renorm`):**
  Made `Func.renorm` (`LeanQbe/T/Flat.lean`) a regular `def` (`Func.renorm_wf`, `Func.renorm_spec`,
  `Func.renorm_callsOk`) and marked `Opt.lean` stage helpers (`Func.earlyCore`, `Func.earlyOpt`,
  `Func.lateCore`, `Func.lateCfg`, `Func.lateOpt`) `@[irreducible]` with `*_eq` lemmas. This
  keeps `Meta.whnf` theorem checking instantaneous (`0 maxHeartbeats` overrides) while `t_kernel_rfl`
  and compiled evaluators normalize cleanly.
* **Linear-Time Gates (`Func.simplifyGroupFast`, `Func.peelFast`):**
  * `Func.simplifyGroupFast` inspects `reifyFunc f` with linear `hasSimpGroup` / `tflatLoops`,
    collapsing `IfOptBits` diamonds (`tailJump == true`), dead groups (`jc == 0`), and compact
    single-use joins (`jc == 1 ∧ tflatSize ≤ 16` when `tflatLoops ≤ 1`), while avoiding `O(3^d)`
    closure re-traversal across deep multi-loop `while` nests (e.g. `LratBytes`).
  * `Func.peelFast` applies bounded 1-iteration peeling (`Func.peel ... 24`) to compact single-loop
    functions (`tflatLoops ≤ 1 ∧ tflatSize ≤ 40`), preventing loop code expansion across multi-loop
    parsers while preserving `mb7_rotate` peeling gains.
* **Two-Stage `Fn.mid` (`Main.lean`, `MainLemmas.lean`):**
  * **Stage 1 (`Func.earlyOpt`, pre-`Legal`):**
    `fold → canon → copy → gvn → copy → fold → simplifyGroupFast → peelFast 24 → dce → renorm`
    (simplifies source/inlined bodies while preserving `C4`–`C9` widening `addc`/`subb`/`mulx`
    chains; checked by `(f.earlyOpt).body.supportsSource legalTarget`).
  * **Stage 2 (`Func.lateOpt`, post-`Legal`):**
    `renorm (dce (renorm (assumeElim (deadLoadElim (simplifyGroupFast (ifOptBits (renorm (fold (gvn (memLoad (renorm (copy (divConst (canon (fold f)))))))))))))))`
  * **Driver Inlining (`Driver.lean`):** `Module.optInline` (`Module.inline 40` + `Fn.renorm`)
    is applied before compilation in CLI assembly emission (`Module.optInline_ok`), while `--il`
    keeps pre-inline QBE IL parity for stock-QBE differential baselines.

---

## 2. Headline Benchmarks (`bench/run.sh`)

Comparison of `lean-qbe` pre-`O-Track` (`main @ a9503f6`) vs post-`O-Track` (all 13 rows pass
exact C hash verification `0xd88e09b152cc8e5a / 0x0000092c781efeb6 / 0x00000000005b645a`):

| Variant | UF (call) ms | UF (inline) ms | UF insns (x64 / arm64) | LRAT (full) ms | LRAT (rup) ms | LRAT insns (x64 / arm64) |
|---|---:|---:|---:|---:|---:|---:|
| `gcc -O2 (C)` | `68.50` | `66.00` | `-` | `18.21` | `7.64` | `-` |
| `clang -O2 (C)` | `68.31` | `66.82` | `-` | `20.48` | `9.05` | `-` |
| `stock QBE` | `79.77` | `76.69` | `77` / `91` | `43.34` | `18.32` | `717` / `732` |
| `lean-qbe` pre (`a9503f6`) | `81.64` | `79.76` | `91` / `82` | `42.55` | `17.65` | `872` / `669` |
| **`lean-qbe` post (`O-Track`)** | **`79.49`** (`-2.6%`) | `80.41` (`+0.8%`) | `128` / `107` | **`42.11`** (`-1.0%`) | **`17.61`** (`-0.2%`) | `901` / `691` |

`lean-qbe (x64)` beats `stock QBE` on `UF (call)` (`79.49 ms` vs `79.77 ms`), `LRAT (full)`
(`42.11 ms` vs `43.34 ms`), and `LRAT (rup)` (`17.61 ms` vs `18.32 ms`).

---

## 3. Targeted Microbenchmarks (`MB1`–`MB8`)

Five-run x64 medians (`ms`) and emitted instruction counts (`x64` / `arm64`, with `qemu-aarch64`
hash parity verified across all variants and C baselines):

| MB | Kernel | Pre (`a9503f6`) ms | Post (`O-Track`) ms | Delta vs Pre | Stock QBE ms | Pre insns (x64 / arm64) | Post insns (x64 / arm64) |
|---|---|---:|---:|---:|---:|---:|---:|
| `mb1` | `addr_scan` | `112.13` | `112.15` | `+0.0%` | `73.61` | `51` / `38` | `51` / `39` |
| `mb2` | `licm` | `160.39` | `161.20` | `+0.5%` | `76.21` | `48` / `37` | `47` / `37` |
| `mb3` | `ifconv` | `151.04` | **`48.00`** | **`-68.2%` (`3.15x`)** | `53.03` | `30` / `28` | `66` / `50` |
| `mb4` | `reassoc` | `171.83` | **`78.54`** | **`-54.3%` (`2.19x`)** | `61.95` | `56` / `48` | `49` / `40` |
| `mb5` | `load_opt` | `143.95` | **`98.45`** | **`-31.6%` (`1.46x`)** | `77.56` | `58` / `38` | `51` / `34` |
| `mb6` | `pressure` | `114.98` | **`111.32`** | **`-3.2%`** | `110.75` | `115` / `86` | `117` / `86` |
| `mb7` | `rotate` | `82.61` | **`77.73`** | **`-5.9%`** | `161.47` | `22` / `27` | `40` / `40` |
| `mb8` | `const_div` | `133.56` | **`66.65`** | **`-50.1%` (`2.00x`)** | `133.43` | `55` / `28` | `142` / `77` |

Key takeaways:
* **`mb3_ifconv` (`-68.2%`):** `Func.ifOptBits → Func.simplifyGroupFast` eliminates the diamond
  branch inside the inner loop into conditional moves, outperforming stock QBE (`48.00 ms` vs
  `53.03 ms`).
* **`mb4_reassoc` (`-54.3%`):** `Func.canon` reassociation + constant folding shrinks the
  dependency chain (`56 → 49` x64 insns, `48 → 40` arm64 insns) and cuts runtime more than `2.1x`.
* **`mb5_load_opt` (`-31.6%`):** `Func.memLoad` store-to-load forwarding and redundant load
  elimination trim `7` insns on x64 (`4` on arm64) and speed up execution `1.46x`.
* **`mb8_const_div` (`-50.1%`):** `Func.divConst` replaces hardware `udiv`/`urem` by `3, 10, 65521`
  with magic multiply-shift sequences (`2.00x` speedup vs both pre-`O-Track` and stock QBE).
* **`mb7_rotate` (`-5.9%`):** `Func.peelFast` reduces runtime to `77.73 ms` (`2.08x` faster than
  stock QBE `161.47 ms`).

---

## 4. Verification, Headline Axioms, & `mul4x4` Crypto Preservation

* **All `10` Native Certificates Pass (`0 maxHeartbeats` overrides):**
  Updated all `Amd64`/`Arm64` certs (`Litmus`, `UnionFind`, `Bignum`, `ChaCha`, `LratBytes`), with
  standalone `Amd64/LratBytes.lean` checking in **`67.30 s` CPU** (`63.95 u + 3.35 s`, `-15.0%`
  faster than the `79.18 s` `a9503f6` baseline) and `Arm64/LratBytes.lean` in **`39.71 s` CPU**.
* **`mul4x4` Carry-Chain Preservation (`LeanQbe/T/Amd64/Bignum.lean`):**
  `#guard` assertions verify `mulx == 11`, `adcx == 12`, `adox == 12`, `setcc == 0` (`1,022 B`
  `.text`), and `ChaCha` shrinks (`77 → 75` dirs / `365 B` x64, `485 → 481` dirs / `1,928 B` Arm64).
* **`scripts/headline.txt` (`+13` O-Track Spec Theorems):**
  Added single-line `[propext, Classical.choice, Quot.sound]` axiom audits for `Module.inline_ok`,
  `Func.renorm_spec`, `Func.canon_spec`, `Func.divConst_spec`, `Func.memLoad_spec`,
  `Func.deadLoadElim_spec`, `Func.assumeElim_spec`, `Func.ifOpt_spec`, `Func.simplifyGroup_spec`,
  `Func.peel_spec`, `Func.earlyOpt_spec`, `Func.lateOpt_spec`, and `Module.optInline_ok`.
