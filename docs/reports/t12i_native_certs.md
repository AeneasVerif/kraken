# `T12i` & `T16` Report: Native x64 and AArch64 Kernel Certificates (`Litmus`, `UnionFind`, `LratBytes`)

## 1. Scope & Deliverables

Branch `swarm-w3-lrat-b2169f63` (forked from `main @ df3000a`) completes `T16` (`LratBytes` native x64 and AArch64 certificates) on top of `T12i` (`Litmus` and `UnionFind`, landed in `df3000a`), with **zero E1 imports** and **zero cross-architecture imports**:

| File | Role | LOC | Max Col | `maxHeartbeats` |
|---|---|---:|---:|---|
| `LeanQbe/T/Amd64/Litmus.lean` | `T12i` 10-module x64 Litmus certs (`df3000a`) | 640 | 100 | default (`200,000`) |
| `LeanQbe/T/Amd64/UnionFind.lean` | `T12i` x64 UnionFind cert (`df3000a`) | 290 | 100 | default (`200,000`) |
| `LeanQbe/T/Amd64/LratBytes.lean` | `T16` x64 LRAT-bytes cert (new) | 328 | 98 | default (`200,000`) |
| `LeanQbe/T/Arm64/Litmus.lean` | `T12i` 10-module Arm64 Litmus certs (`df3000a`) | 668 | 100 | default (`200,000`) |
| `LeanQbe/T/Arm64/UnionFind.lean` | `T12i` Arm64 UnionFind cert (`df3000a`) | 293 | 99 | default (`200,000`) |
| `LeanQbe/T/Arm64/LratBytes.lean` | `T16` Arm64 LRAT-bytes cert (new) | 335 | 98 | default (`200,000`) |
| `LeanQbeAmd64.lean` | Wire `LeanQbe.T.Amd64.LratBytes` (updated) | 32 | 97 | — |
| `LeanQbeArm64.lean` | Wire `LeanQbe.T.Arm64.LratBytes` (updated) | 27 | 97 | — |
| `LeanQbe/Amd64/LratBytes.lean` | E1 x64 baseline (reference, untouched) | 229 | 104 | `set_option maxHeartbeats 48000` |
| `LeanQbe/Arm64/LratBytes.lean` | E1 Arm64 baseline (reference, untouched) | 227 | 103 | `set_option maxHeartbeats 48000` |

### Key Architecture Comparison (`T16` vs E1)

1. **Pre-spliced untrusted hints (`splice_module_hints`):** All `LeanQbe.T` certificates run register allocation outside the kernel via `meta import` + `splice_module_hints` (costing `1.01M`–`3.68M` raw heartbeats, `< 0.4 s`), leaving a concrete `Hints` literal. The kernel checks `checkCompile ... = true` via `t_kernel_rfl` (`compiled_check`) and constructs `compiled` via `compileChecked` (`~27k` raw heartbeats). In contrast, E1 runs register allocation inside kernel reduction (`compileChecked ... (by kernel_rfl)`).
2. **Zero `maxHeartbeats` overrides:** Separating `compiled_check` (`t_kernel_rfl`) from `compiled` and offloading register allocation keeps both `T.Amd64.LratBytes.compiled_check` and `T.Arm64.LratBytes.compiled_check` below `22,000` `maxHeartbeats` units (`>= 9.09x` margin under Lean's default `200,000`), whereas E1 fails kernel timeout at `26,000` and requires `29,000` (`set_option maxHeartbeats 48000` override).
3. **Closure isolation (`G5` & cross-arch):**
   * `LeanQbe.T.Amd64.LratBytes`: `2,572` transitive modules, `0` E1 (`LeanQbe.*` excluding `LeanQbe.T.*`), `0` `Arm64`/`AArch64` modules.
   * `LeanQbe.T.Arm64.LratBytes`: `2,567` transitive modules, `0` E1 (`LeanQbe.*` excluding `LeanQbe.T.*`), `0` `Amd64`/`X64` modules.
   * `0 sorry`, `0 bv_decide`/`native_decide`/`ofReduceBool`/`ofReduceNat`, `0` lines `> 100` cols, all deliverables `<= 335` LOC.

---

## 2. Standalone `-DwarningAsError=true` Build Times

Measured sequentially via `/usr/bin/time timeout 300 lake env lean -DwarningAsError=true <file>` on Lean `nightly-2026-11-08` (all `.olean` dependencies prebuilt, exit code `0`):

| Module | LOC | CPU Time (`user + sys`) | Wall Time |
|---|---:|---:|---:|
| `LeanQbe/T/Amd64/Litmus.lean` | 640 | `8.20 s` (`7.65 u + 0.55 s`) | `6.67 s` |
| `LeanQbe/T/Amd64/UnionFind.lean` | 290 | `11.43 s` (`10.69 u + 0.74 s`) | `10.86 s` |
| `LeanQbe/T/Amd64/LratBytes.lean` | 328 | `79.18 s` (`74.98 u + 4.20 s`) | `76.51 s` |
| `LeanQbe/T/Arm64/Litmus.lean` | 668 | `8.05 s` (`7.50 u + 0.55 s`) | `6.57 s` |
| `LeanQbe/T/Arm64/UnionFind.lean` | 293 | `6.43 s` (`5.93 u + 0.50 s`) | `5.89 s` |
| `LeanQbe/T/Arm64/LratBytes.lean` | 335 | `43.00 s` (`41.11 u + 1.89 s`) | `40.58 s` |
| `LeanQbe/Amd64/LratBytes.lean` (E1) | 229 | `26.00 s` (`25.06 u + 0.94 s`) | `24.55 s` |
| `LeanQbe/Arm64/LratBytes.lean` (E1) | 227 | `25.11 s` (`24.16 u + 0.95 s`) | `24.17 s` |

Note: Both `T.Amd64.LratBytes.lean` (`79.18 s` CPU / `76.51 s` wall, max RSS `7,771,304 KB`) and `T.Arm64.LratBytes.lean` (`43.00 s` CPU / `40.58 s` wall, max RSS `7,773,644 KB`) remain well under the `120 s` standalone ceiling and `600 s` `scripts/check.sh` timeout.

---

## 3. Kernel Heartbeats, Profiler Timings, & `maxHeartbeats` Margins

> **Measurement methodology (`nightly-2026-11-08`):**
> * `raw_hb` is `IO.getNumHeartbeats` delta around each single command with `set_option Elab.async false` (Lean's internal allocation counter; default `Core.getMaxHeartbeats` = `200,000,000` for `maxHeartbeats = 200000`).
> * `Kernel Typecheck` is `-Dprofiler=true` kernel `type checking` time.
> * `set_option maxHeartbeats` threshold is measured directly by failing (`(kernel) deterministic timeout`) vs passing under `set_option maxHeartbeats <N> in`. Because kernel reduction heartbeats differ from allocation `raw_hb`, `E1` hits deterministic timeout at fewer `raw_hb` (`~192M`, threshold `26k < N <= 29k`) than `T16` (`~223M`, threshold `20k < N <= 22k`).

### 3.1 `UnionFind` and `LratBytes` (`T12i`/`T16` vs E1)

| Target / Module | `splice` `raw_hb` | Check `raw_hb` | `compiled` `raw_hb` | `supportsSource` `raw_hb` | Kernel Typecheck (`check` / `supp`) | `maxHeartbeats` Threshold | Headroom vs Limit |
|---|---:|---:|---:|---:|---|---|---|
| `T.Amd64.UnionFind` | `1,349,285` | `11,915,358` | — | `2,826,316` | `1.62 s` / `395 ms` | `1,000 < N <= 1,100` | `>= 181.8x` (vs `200,000`) |
| `T.Arm64.UnionFind` | `1,206,133` | `11,973,091` | — | `2,824,675` | `1.60 s` / `385 ms` | `<= 200,000` (pass; `11.97M` `raw_hb`) | — |
| `T.Amd64.LratBytes` (`T16`) | `3,677,781` (`321 ms`) | `222,853,802` | `27,394` | `51,044,017` | `32.7 s` / `9.59 s` | `20,000 < N <= 22,000` | `>= 9.09x` (vs `200,000`) |
| `T.Arm64.LratBytes` (`T16`) | `3,428,714` (`399 ms`) | `223,580,382` | `27,505` | `51,042,368` | `31.9 s` / `7.88 s` | `20,000 < N <= 22,000` | `>= 9.09x` (vs `200,000`) |
| `E1.Amd64.LratBytes` | — (in-kernel) | — (combined) | `192,265,346` | — | `23.9 s` (`compiled`) | `26,000 < N <= 29,000` | `1.66x–1.85x` (vs `48,000`) |
| `E1.Arm64.LratBytes` | — (in-kernel) | — (combined) | `187,159,970` | — | `23.6 s` (`compiled`) | `26,000 < N <= 29,000` | `1.66x–1.85x` (vs `48,000`) |

*Note on `E1.Amd64.LratBytes` split check:* Separating `theorem chk : checkCompile ... = true := by kernel_rfl` from `compileChecked` in E1 still hits `(kernel) deterministic timeout` at `maxHeartbeats 26000` (`type checking 21.6 s`), confirming the higher kernel heartbeat threshold comes from running regalloc in-kernel rather than only `def` proof abstraction.

### 3.2 `Litmus` Per-Module Breakdown (`LeanQbe/T/{Amd64,Arm64}/Litmus.lean`)

| Litmus Module | x64 `splice` `raw_hb` | x64 `*_check` `raw_hb` | x64 Typecheck | Arm64 `splice` `raw_hb` | Arm64 `*_check` `raw_hb` | Arm64 Typecheck |
|---|---:|---:|---:|---:|---:|---:|
| `tracer` | `1,150,300` | `784,792` | `102 ms` | `1,012,401` | `784,242` | `101 ms` |
| `ifelse` | `1,145,737` | `2,106,657` | `269 ms` | `1,013,354` | `2,095,769` | `270 ms` |
| `sumto` | `1,200,838` | `2,475,179` | `327 ms` | `1,043,415` | `2,470,748` | `316 ms` |
| `evenodd` | `1,161,644` | `2,843,874` | `383 ms` | `1,021,939` | `2,834,924` | `371 ms` |
| `nested` | `1,263,324` | `4,941,889` | `664 ms` | `1,123,368` | `4,935,771` | `681 ms` |
| `swap` | `1,167,709` | `2,222,337` | `304 ms` | `1,026,707` | `2,215,002` | `288 ms` |
| `spill10` | `1,328,440` | `9,542,756` | `1.33 s` | `1,084,638` | `9,602,642` | `1.35 s` |
| `callinc` | `1,155,733` | `1,332,102` | `169 ms` | `1,022,871` | `1,334,332` | `172 ms` |
| `twice` | `1,171,421` | `2,062,281` | `267 ms` | `1,036,576` | `2,048,319` | `269 ms` |
| `sumcall` | `1,201,470` | `3,708,929` | `508 ms` | `1,074,800` | `3,737,454` | `511 ms` |
| `allFns_supportsSource_all` | — | `6,603,992` | `885 ms` | — | `6,602,346` | `874 ms` |
| **10-module sum (`Litmus` checks + `supportsSource`)** | `11,946,616` | `38,624,788` | `5.21 s` (`7.23 s` incl. `UF`) | `10,460,069` | `38,661,549` | `5.20 s` (`7.19 s` incl. `UF`) |

---

## 4. Stack Frame Bounds (`compiled.bound`) & Emitted Directives (`compiled.code.length`)

| Suite / Module | x64 `compiled.bounds` (bytes) | x64 Dirs | Arm64 `compiled.bounds` (bytes) | Arm64 Dirs |
|---|---|---:|---|---:|
| `Litmus.tracer` | `tracer: 8` | 7 | `tracer: 16` | 8 |
| `Litmus.ifelse` | `ifelse: 8` | 17 | `ifelse: 16` | 17 |
| `Litmus.sumto` | `sumto: 8` | 18 | `sumto: 16` | 17 |
| `Litmus.evenodd` | `evenodd: 8` | 28 | `evenodd: 16` | 26 |
| `Litmus.nested` | `nested: 8` | 33 | `nested: 16` | 30 |
| `Litmus.swap` | `swap: 8` | 20 | `swap: 16` | 18 |
| `Litmus.spill10` | `spill10: 56` | 45 | `spill10: 16` | 28 |
| `Litmus.callinc` | `inc: 8, callinc: 24` | 14 | `inc: 16, callinc: 32` | 17 |
| `Litmus.twice` | `check: 8, twice: 40` | 25 | `check: 16, twice: 48` | 27 |
| `Litmus.sumcall` | `inc: 8, sumcall: 40` | 34 | `inc: 16, sumcall: 48` | 35 |
| **`Litmus` total (10 modules)** | max `56` (`spill10`) | **241** | max `48` (`twice`/`sumcall`) | **223** |
| **`UnionFind` (`T12i`)** | `find: 8, union: 40, unionInline: 8` | **102** | `find: 16, union: 48, unionInline: 16` | **93** |
| **`LratBytes` (`T16`)** | `lb_parse_dimacs_header: 8, lb_parse_dimacs_body: 72, lb_read_add_lits: 56, lb_rup_check: 88, lb_check_prf: 184, lrat_check_bytes: 264` | **1,505** (`+31.7%` vs E1) | `lb_parse_dimacs_header: 16, lb_parse_dimacs_body: 16, lb_read_add_lits: 16, lb_rup_check: 16, lb_check_prf: 112, lrat_check_bytes: 176` | **1,192** (`+15.5%` vs E1) |
| **`LratBytes` (E1 baseline)** | `lb_parse_dimacs_header: 24, lb_parse_dimacs_body: 72, lb_read_add_lits: 56, lb_rup_check: 88, lb_check_prf: 184, lrat_check_bytes: 264` | **1,143** | `lb_parse_dimacs_header: 16, lb_parse_dimacs_body: 16, lb_read_add_lits: 16, lb_rup_check: 16, lb_check_prf: 112, lrat_check_bytes: 176` | **1,032** |

Observations:
* **Stack bounds parity (`T16` vs E1):** On AArch64, all six `LratBytes` functions match E1's exact frame bounds (`16/16/16/16/112/176` bytes). On x64, five of six functions match identically (`72/56/88/184/264`), while `lb_parse_dimacs_header` drops from `24` bytes (E1) to `8` bytes (`T16`).
* **Directive counts:** `T16` emits `+362` directives (`1,505` vs `1,143`, `-21` from BMI2 variable shifts) on x64 and `+160` directives (`1,192` vs `1,032`) on AArch64 compared to E1, reflecting explicit typed-IR width conversions (`zext`/`sext`/`trunc`), `.bool` branch materialization, and `GprTarget`/`Targ` legalization.
* **Register pressure (`Litmus.spill10`):** AArch64's larger allocatable GPR set keeps `spill10` at a minimal `16`-byte frame (`28` dirs) vs `56` bytes (`45` dirs) on SysV x64.

---

## 5. `T16` Theorems & Axiom Audit

Every theorem in `LeanQbe/T/Amd64/LratBytes.lean` and `LeanQbe/T/Arm64/LratBytes.lean` emits a complete single-line `#print axioms` output depending strictly on `[propext, Classical.choice, Quot.sound]`:

* **x64 (`LeanQbe.T.Amd64.LratBytes`):** `compiled_check`, `compiled`, `lrat_bytes_module_fnspec`, `lrat_check_bytes_x64_of_fnspec`, `lrat_check_bytes_x64_correct`, `lrat_check_bytes_x64_unsat`, `lrat_check_bytes_x64_accepts` (`rax = 1 ∧ nvBytesCnf.Unsat`), `lrat_check_bytes_x64_rejects` (`rax = 0`).
* **Arm64 (`LeanQbe.T.Arm64.LratBytes`):** `compiled_check`, `compiled`, `lrat_bytes_module_fnspec`, `lrat_check_bytes_arm64_of_fnspec`, `lrat_check_bytes_arm64_correct`, `lrat_check_bytes_arm64_unsat`, `lrat_check_bytes_arm64_accepts` (`x0 = 1 ∧ nvBytesCnf.Unsat`), `lrat_check_bytes_arm64_rejects` (`x0 = 0`).

---

## 6. Related Wave-3 Native Certificates (`T13` Bignum & `T14` ChaCha on `main @ 3b42664`)

As recorded on the swarm board (`w3-crypto` `#385`, `@reviewer` `#387`, `@coordinator` `#392`, landed on `main @ 3b42664`), the remaining native crypto certificates also compile with **zero `maxHeartbeats` overrides**, `<= 100` cols, `0` E1/cross-arch imports, and `24/24` single-line `[propext, Classical.choice, Quot.sound]` axioms:

| File (`main @ 3b42664`) | LOC | Standalone CPU | Module / Kernel Metrics (`dirs` / `bound` / `.text`) |
|---|---:|---:|---|
| `LeanQbe/T/Amd64/Bignum.lean` | 496 | `19.79 s` (`18.74 u + 1.05 s`) | `mul4x4`: `257` / `104 B` / `1019 B`; `addMod25519`: `68` / `40 B` / `255 B`; `subMod25519`: `78` / `56 B` / `300 B` |
| `LeanQbe/T/Arm64/Bignum.lean` | 481 | `20.07 s` (`19.06 u + 1.02 s`) | `mul4x4`: `225` / `48 B` / `904 B`; `addMod25519`: `44` / `16 B` / `200 B`; `subMod25519`: `52` / `16 B` / `232 B` |
| `LeanQbe/T/Amd64/ChaCha.lean` | 262 | `7.98 s` (`7.44 u + 0.54 s`) | `chacha20Block` (EVEX `v4i32` SIMD): `77` / `8 B` / `367 B` |
| `LeanQbe/T/Arm64/ChaCha.lean` | 266 | `37.40 s` (`35.41 u + 1.99 s`) | `chacha20Block` (scalarized `v4i32`): `485` / `192 B` / `1944 B` |

