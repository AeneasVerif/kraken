# opt: Target-parameterized typed-IR legalisation (`T5`, `G13`)

Owner: `opt` (finished & modularized in Wave 0A by `t5-finisher`).
Files: `LeanQbe/T/{Legal,LegalLemmas,LegalCheck1,LegalCheck2,LegalCheck3}.lean`,
`LeanQbeTest/T/LegalTest.lean`, wiring in `LeanQbe.lean`, and headline audit entries in
`scripts/headline.txt`.

## Status

| Deliverable | State |
|---|---|
| `G13` packing oracle & target capability record (`PackOracle`, `LegalTarget`) | done (`Legal.lean`): target-neutral capability record (zero `Kraken.X64`/`Kraken.AArch64` imports), presets `aarch64`, `scalar64`, `x64` (`x64SSE`, `x64AVX2`, `x64AVX512`), baseline `PackOracle.g13` |
| PHOAS→PHOAS legalisation pass (`legalExpr`, `legalBlocks`, `Func.legal`, `Fn.legal`) | done (`Legal.lean`, 2,816 LOC): (a) pair splitting & aligned/unaligned memory, (b) `bits n` widening with zero-extension invariant & masking/sign-extension, (c) vector halving & scalarization, (d) derived opcodes (`bool`, `ternlog`, `blend`, uniform-imm vector `shl`/`rotl`, 128-bit shuffles/SHA, `bitcast`) |
| Decidable legality predicate (`TFlat.isLegal`, `Func.isLegal`, `Func.supportsSource`) | done (`Legal.lean`): computable kernel-reducible `Bool` checker over reified `TFlat` |
| Well-formedness & semantic preservation (`Func.legal_wf`, `Fn.legal_wf`, `Func.legal_wp_of_refines`, `Func.legal_wp`, `Func.legal_spec`, `Fn.legal_spec`) | done (`LegalLemmas.lean`, 15,680 LOC, 0 `sorry`, standard axioms only) |
| Decidable legality proof (`Func.legal_isLegal`, `Fn.legal_isLegal`) | done, split cleanly into 3 modular files `≤ 2.5k` LOC each (`LegalCheck1.lean` 2,370 LOC, `LegalCheck2.lean` 1,890 LOC, `LegalCheck3.lean` 1,637 LOC; each `< 10 s` standalone) |
| Test suite (`LeanQbeTest/T/LegalTest.lean`) | done (473 LOC): ports all 8 `T1` `Examples`, `T1` `Smoke`, `T3` `NotationTest`, `T4` `UnionFind`, plus dedicated rule (a)–(e) & negative tests across `x64AVX512`/`x64SSE`/`aarch64`/`scalar64` (`_wf`, `_isLegal` by `t_kernel_rfl`, `_wp`/`_spec`) |

## Architecture & Scope Boundary (Scalar FP & `H4` `backendOk`)

- **Target-neutral capability record (`PackOracle`, `LegalTarget`):** `LeanQbe.T.Legal` imports neither `Kraken.X64` nor `Kraken.AArch64` (verified by `scripts/check.sh` Step 3). `PackOracle.g13` keeps balanced `Ty.vec k leaf` trees of supported vector register bit width packed and splits all other `pair a b` values into leaves; `LegalTarget.aarch64` uses `PackOracle.none` (`allowPackBridge := false`, `floatFmts := []`).
- **No `select → jnz` conversion (`G2`) and no new emulation hooks:** `legalExpr` preserves existing `.jnz` nodes and never converts `select`/`blend` into branches (`blend` lowers to scalar `select`, never `jnz`).
- **Important boundary — `Legal` vs `H4` `backendOk` for x64 scalar FP:** `LegalTarget.x64` sets `floatFmts := [.s, .d]` (`Legal.lean:141`), so `Func.isLegal (.x64 …)` permits scalar `f32`/`f64` operations and variables (and expands scalar float bitwise ops via integer `bitcast` when `scalarFloatBitwise = false`). Because upstream Kraken x64 does not model scalar floating-point instructions (`addss`/`addsd`/`cvt*`, per `typed_ir_plan.md` §0), **`Func.isLegal` is NOT the backend's entry contract**: the backend entry predicate **`H4` `backendOk`** rejects scalar-FP variables/opcodes separately on targets lacking scalar FP, so `T7` (`Rega`) does not grow a scalar float register bank. `LegalTarget.aarch64` sets `floatFmts := []`, so `Func.supportsSource .aarch64` already rejects scalar floats directly (`scalarFloatFn_not_supp_arm`, `notation_floatCastAndTerms_not_supp_arm` in `LegalTest.lean`).

## Pass Rules & Proof Structure

1. **Rule (a) Pair & wide-vector splitting:** Splits non-packed `.pair a b` across function arguments/results (`encodeVal`/`encodeTup`/`legalSig`), `let_` binders, `group` block signatures (`Member.map`, `tupLiftMap`), `jump`, `call`, `ret`, and `exit`. Eliminates `mkpair`/`unpair` on split pairs with zero instructions, preserves packed-boundary `mkpair`/`unpair` bridges only when `allowPackBridge = true`, splits byte-aligned `load`/`store` directly at byte offsets, and legalizes non-byte-aligned `load`/`store` via 64-bit word / byte-chunk transfers.
2. **Rule (b) `bits n` widening:** Widens `bits n` (`n ∉ target.bitWidths`, `n ≤ 64`) to `w = target.widenWidth n` under the zero-extension invariant (`x' = x.setWidth w`), masking arithmetic/bitwise/shift/multiply/conversion results back to `n` bits and sign-extending (`shl` + `ashr`) inputs for signed comparisons, `ashr`, `sdiv`/`srem`/`sdiv0`, `smulw`, `cls`, `sext`, and `sitofp`.
3. **Rule (c) Vector halving & scalarization:** Recursively halves `Ty.vec (k + 1) t = .pair (Ty.vec k t) (Ty.vec k t)` down to `vecWidths` (`512 → 256 → 128`) on vector targets or down to scalar leaves on `aarch64`/`scalar64`. Uniform-immediate vector `shl`/`rotl` expand to `rotr` (+ `and` mask) on `x64`; unsupported vector ops and 128-bit shuffles (`shufd`/`shufb`/`alignr`/`blendw`) scalarize cleanly on scalar targets.
4. **Rule (d) Derived opcode expansion:** Expands `bool` `cmp`/`select`/`add`/`sub`/`mul`/`neg`/`ternlog`, scalar `ternlog` (into `and`/`or`/`not`), `blend` on `bool` masks (into `select`), and non-native `bitcast`s (via 64-bit word streams).
5. **Proof modules:**
   - `LeanQbe/T/LegalLemmas.lean` (15,680 LOC): `Wf.induct`-based proofs of `Func.legal_wf`, `Fn.legal_wf`, `Func.legal_wp_of_refines`, `Func.legal_wp`, `Func.legal_spec`, and `Fn.legal_spec` (grandfathered single file per `typed_ir_plan.md` §1; `40.3 s` standalone).
   - `LeanQbe/T/LegalCheck1.lean` (2,370 LOC): `TFlat.isLegal` equation helpers, `CtxExtends`/`LvlOk`/`ArgNormal`/`ArgsNormal`/`CLegal`/`DLegal` invariants, pack/unpack bridge lemmas, generic emitters, bit/bool/word64 helpers, `legalLoad_isLegal`/`legalStore_isLegal`, and `legalFloatBit2_isLegal`.
   - `LeanQbe/T/LegalCheck2.lean` (1,890 LOC): scalarized 128-bit SIMD & SHA-256 legality, generic tree lifters (`legalUnaryTree_isLegal`..`legalBlendTree_isLegal`), and explicit 128-bit shuffle legality (`legalShufd/Blendw/Alignr/Shufb_isLegal`).
   - `LeanQbe/T/LegalCheck3.lean` (1,637 LOC): `legalOp_isLegal`, `legalExpr_isLegal_wf`, `Func.legal_isLegal`, and `Fn.legal_isLegal`.

## File Sizes & Timings

### Standalone elaboration (`timeout 300 lake env lean <file>`)

| Module | LOC | Wall (s) | CPU (s) | Status |
|---|---:|---:|---:|---|
| `LeanQbe/T/Legal.lean` | 2,816 | 7.8 | 11.9 | `rc=0` |
| `LeanQbe/T/LegalLemmas.lean` | 15,680 | 40.3 | 192.8 | `rc=0` |
| `LeanQbe/T/LegalCheck1.lean` | 2,370 | 4.2 | 15.3 | `rc=0` |
| `LeanQbe/T/LegalCheck2.lean` | 1,890 | 5.1 | 13.4 | `rc=0` |
| `LeanQbe/T/LegalCheck3.lean` | 1,637 | 9.6 | 10.5 | `rc=0` |
| `LeanQbeTest/T/LegalTest.lean` | 473 | 10.7 | 13.8 | `rc=0` |

### Kernel scaling (`(ScaleTest.slN.legal .x64AVX512).isLegal .x64AVX512 = true` by `t_kernel_rfl`)

| Benchmark | Ops | Wall (s) | Status |
|---|---:|---:|---|
| `ScaleTest.sl250` | 250 | 2.84 | `rc=0` |
| `ScaleTest.sl1000` | 1,000 | 6.58 | `rc=0` |
| `ScaleTest.sl2000` | 2,000 | 20.52 | `rc=0` |

## Verification Results

- **Full quality gate (`timeout 900 bash scripts/check.sh`)**: **ALL PASSED** (`rc=0`):
  - Step 1: `lake build --wfail LeanQbe LeanQbeAmd64 LeanQbeArm64 LeanQbeTest leanqbe leanqbe-arm64` succeeded with zero warnings.
  - Steps 2 & 2b: zero `sorry` / `sorryAx`, zero `bv_decide` / `native_decide` / `ofReduceBool` across all tracked `.lean` files.
  - Step 3: `LeanQbe` import closure includes all 5 `LeanQbe.T.Legal*` modules (`Legal`, `LegalLemmas`, `LegalCheck1`–`LegalCheck3`) and zero `Kraken.X64`/`Kraken.AArch64` imports.
  - Step 4: **383 / 383** complete one-line `#print axioms` reports in `scripts/headline.txt` (including 32 new `T5` theorems: `Func.legal_wf`, `Fn.legal_wf`, `Func.legal_wp_of_refines`, `Func.legal_wp`, `Func.legal_spec`, `Fn.legal_spec`, `Func.legal_isLegal`, `Fn.legal_isLegal`, plus 24 `LeanQbeTest.T.LegalTest` theorems), all strictly within `[propext, Classical.choice, Quot.sound]`.
  - Step 5 (CPU check times): `LegalLemmas.lean` 157 s, `Amd64/IselLemmas.lean` 45 s, `RegaLemmas.lean` 30 s, `Amd64/LratBytes.lean` 30 s, `Arm64/LratBytes.lean` 29 s, `LratBytesCheckLemmas.lean` 17 s, `LratBytesDimacsLemmas.lean` 13 s.
- **x64 native litmus & LRAT suite (`timeout 300 bash test/run.sh`)**: **ALL PASSED** (`rc=0`, both `leanqbe` and stock `qbe`).
- **AArch64 QEMU litmus & LRAT suite (`timeout 300 bash test/arm64/run.sh`)**: **ALL PASSED** (`rc=0`, both `leanqbe-arm64` and stock `qbe -t arm64`).
- **Review `#55` doc cleanup (`docs/reports/logic.md`)**: verified `UnionFindLemmas` restated as 228 vs 187 comparable source-level lines (`+41` / ~22%, noting E1 lines 189–263 are compiled-target theorems deferred to `T11`/`T12`) and `LeanQbe/T/Logic/` stated as 4,247 vs 1,046 lines (`~4.1×` E1).
