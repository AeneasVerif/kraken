> **[Historical design note]** Written during an earlier milestone (at commit `2a28b05`); `scripts/headline.txt` referenced below has since been split into `scripts/headlines.d/*.txt`. See `LeanQbe-README.md` for current paths.

# SysV x86-64 SIMD Instruction Selection (`VecIsa` & `VecTarget`)

Modules covered:
- `LeanQbe/T/Amd64/IselVec.lean`
- `LeanQbe/T/Amd64/IselVecLemmas1.lean`
- `LeanQbe/T/Amd64/IselVecLemmas2.lean`
- `LeanQbe/T/Amd64/IselVecLemmas3.lean` (split from `IselVecLemmas2.lean` to keep per-file build times bounded)
- `LeanQbeTest/T/Amd64VecTest.lean`
- `docs/reports/t10_simd.md`

## Status & Metrics

| Deliverable | LOC | Standalone (`-DwarningAsError=true`) | Role |
|---|---:|---:|---|
| `LeanQbe/T/Amd64/IselVec.lean` | 520 | 0.856s real (1.028s user) | `x64Vec : VecIsa Reg64 RegMm CondCode Directive` & `x64SupportsVecOp` |
| `LeanQbe/T/Amd64/IselVecLemmas1.lean` | 1,241 | 1.767s real (4.644s user) | `x64VecSpec` metadata, `vmov`/`vmovi`/`vslot*`/`vload`/`vstore` specs & `NoLab` theorems |
| `LeanQbe/T/Amd64/IselVecLemmas2.lean` | 1,475 | 1.907s real (6.422s user) | BitVec/float/ternlog bridge lemmas, Kraken instruction `FallsTo` specs, `x64EmitUnary`/`Vpaddd`/`BinInPlace`/`Ternlog1Vec` |
| `LeanQbe/T/Amd64/IselVecLemmas3.lean` | 1,489 | 9.515s real (21.738s user) | `x64Vop_spec`, `x64Vop_noLab`, `x64VecSpec : VecTarget ...`, `ParserChecks` (`Kraken.X64.Parser`) |
| `LeanQbeTest/T/Amd64VecTest.lean` | 758 | 3.276s real (4.842s user) | Kernel `rfl`, `Host.ofLayout` ChaCha/`addps`+`subps`+NaN/`mkpair`+`unpair`/unaligned round-trips, `#print axioms` |

* Full Lake build (`lake build --wfail LeanQbe.T.Amd64.IselVec LeanQbe.T.Amd64.IselVecLemmas1 LeanQbe.T.Amd64.IselVecLemmas2 LeanQbe.T.Amd64.IselVecLemmas3 LeanQbeTest.T.Amd64VecTest`): passed (`134 jobs`, `3.457s` real, `EXIT=0`).
* Total proof LOC (`IselVecLemmas1..3`): `4,205` LOC (`1,241 + 1,475 + 1,489`), split into 3 files so every file checks in under `10s` standalone with `-DwarningAsError=true`.

## Design & Implementation Summary

### 1. Register Bank, ABI & Width Predicates (`LeanQbe/T/Amd64/IselVec.lean`)
* **`mm0..mm15` register bank**:
  * `x64VecArgRegs := [.mm0, .mm1, .mm2, .mm3, .mm4, .mm5, .mm6, .mm7]`
  * `x64VecRetRegs := [.mm0, .mm1]`
  * `x64VecScratch := [.mm14, .mm15]`
  * `x64VecAllocatable := [.mm0 .. .mm13]`
  Keeping the bank in `mm0..mm15` ensures both 128-bit legacy SSE operations (`pshufd`, `pshufb`, `palignr`, `pblendw`, `addps`, `subps`) and VEX/EVEX operations (`vmovdqu32`, `vpaddd`, `vprord`, `vpsrld`, `vpternlogd`) accept every register uniformly.
* **`isAbiVec` vs `vecSlotWidth`**:
  * `x64IsAbiVec t := x64IsVecBits t && t.size == 128` (`v4i32`, `v4f32`, matching SysV `__m128i`/`__m128`).
  * `x64VecSlotWidth t` maps balanced `i32`/`f32` trees of size `64` (`v2i32`/`v2f32` intermediate `mkpair`/`unpair` bridge pairs) to `some .w64`, `128` to `some .w128`, `256` to `some .w256`, `512` to `some .w512`, and `none` otherwise.

### 2. Unaligned Moves, Immediates, Stack Slots, and Memory
* **Moves (`x64Vmov`)**: `.vmovdqu32` at `.W128` (for `.w64`/`.w128`), `.W256` (`.w256`), and `.W512` (`.w512`), `maskNone` flags.
* **Immediates (`x64Vmovi`)**:
  * `.w64`: `movabs` into `%r10` followed by `vmovIn .W64` (`vmovq %r10, %xmm_d`).
  * `.w128`: `movabs` + `vmovIn .W64` of high 64 bits into `%xmm_d`, `pshufd $0x4e`, `movabs` + `vmovIn .W64` of low 64 bits into `.mm14`, and `vpternlogd $0xFE` (`A | B | C`, zeroing upper bits via `.W128`), all preserving flags (`maskNone`).
  * `.w256`/`.w512`: `vpternlogd $0x00` for zero vectors and `vpternlogd $0xFF` for all-ones vectors; `none` otherwise.
* **Unaligned stack slots (`x64VslotSt`/`x64VslotLd`)**: `.vmovOut .W64` / `.vmovIn .W64` for `.w64` (`1` slot), and `.vmovdqu32` (`checkAlign = false`) for `.w128`/`.w256`/`.w512` (`2`/`4`/`8` slots), falling back to `movabs $off, %r10` + indexed `(%rsp, %r10, 1)` when `8 * i >= 2 ^ 31` (`x64FrameSpec.spOk` is `True`).
* **Unaligned memory (`x64Vload`/`x64Vstore`)**: `.vmovIn .W64`/`.vmovOut .W64` for `64`-bit vector types and `.vmovdqu32` (`checkAlign = false`) for `128`/`256`/`512`-bit vector types, routing `.imm c` and non-int32 `.baseDisp` displacements through `%r10` via `movabs` + `lea (%rb, %r10, 1), %r10`.

### 3. Vector Instruction Selection (`x64Vop` & `x64SupportsVecOp`)
* Kernel-`rfl`-safe `x64SupportsVecOp` (no SHA-NI: `.sha256rnds2`, `.sha256msg1`, `.sha256msg2` all return `false`):
  * **`128`/`256`/`512`-bit `i32`/`f32` vectors**: `.copy` (`x64Vmov`/`x64Vmovi`), bitwise `.and`/`.or`/`.xor`/`.not`/`.ternlog` via `vpternlogd` (`0xC0`, `0xFC`, `0x3C`, `0x33`, `imm`; handling all register/immediate/aliasing combinations including single-variable linear reductions `x64EmitTernlog1Vec` with `.mm15`).
  * **`128`/`256`/`512`-bit `i32` vectors**: `.add` (`vpaddd`), and uniform immediate-splat `.rotr`/`.lshr` (`vprord`/`vpsrld` with leaf count reduced `% 32` via `x64UniformI32Splat?` so `vpsrld` never saturates shifts `≥ 32` to `0`).
  * **`128`-bit vectors (`v4i32`/`v4f32`)**: `.shufd` (`pshufd`), `.shufb` (`pshufb`), `.alignr` (`palignr`), `.blendw` (`pblendw`), all register-staged (`x64BinInPlace128`) so legacy SSE instructions never read memory (`checkAlign := true`).
  * **`v4f32` floating-point**: `.fadd` (`addps`) and `.fsub` (`subps`) proved sound against `OpCode.wp` (`floatResultWp` over `Float.Model.UnpackedFloat.add`/`sub` including NaN propagation via `sseBinOp`). Note Kraken `subps` computes `b - a` and writes `a`, matching `(pa, pb)` staged into `(dst = pa, src = pb)`.
  * **Pack/unpack bridges (`mkpair`/`unpair`)**:
    * `i32 × i32 ↔ v2i32`: GPR `.r10`/`.r11` packing with `shl $32`/`or`/`vmovIn .W64` (`maskAll` flags) and unpacking with `vmovOut .W64`/`movl`/`shr $32` (`maskAll` flags).
    * `t × t ↔ pair t t` (`t.size == 64`, i.e., `v2i32`, `v2f32`): `vmovq` (`vmovq_mm` zero-extending low 64 bits) + `pshufd $0x4e` + `vpternlogd $0xFE` via `.mm14` (`maskNone` flags).

## Verification & Hygiene Audit

1. **Certified Target (`x64VecSpec`) & `NoLab` Theorems**:
   * `LeanQbe.T.Amd64.x64VecSpec : VecTarget x64Mach x64Vec x64CondReads x64Frame.sp x64Scratch x64FrameSpec.spOk` in `LeanQbe/T/Amd64/IselVecLemmas3.lean`.
   * Complete `NoLab` suite (`Kraken.Directive.label l ∉ ...`): `x64Vmov_noLab`, `x64Vmovi_noLab`, `x64VslotSt_noLab`, `x64VslotLd_noLab`, `x64Vload_noLab`, `x64Vstore_noLab` in `IselVecLemmas1.lean`, and `x64Vop_noLab` in `IselVecLemmas3.lean`.
2. **Parser & Concrete `Host.ofLayout` Tests**:
   * Kernel `rfl` `ParserChecks`: `parser_evex_rfl`, `parser_sse_mem_bridge_rfl` (`IselVecLemmas3.lean`) and `x64Vec_evex_sse_parser_rfl` (`Amd64VecTest.lean`).
   * Concrete `Host.ofLayout` theorems in `LeanQbeTest/T/Amd64VecTest.lean`:
     * `chachaQrProg_run` + `chachaQrModel_rfc8439_lane0_shufd` (ChaCha20 quarter-round + `shufd $0x39` on `v4i32` rows matching RFC 8439 §2.1.1).
     * `floatVecProg_nan_run` (`addps`/`subps` on `v4f32` including binary32 IEEE-754 arithmetic and arbitrary NaN lane propagation).
     * `bridgeProg_run` (`i32 × i32 ↔ v2i32 ↔ v4i32` and `v2f32 × v2f32 ↔ v4f32` round-trips).
     * `unalignedProg_run` (`vslotSt`/`vslotLd` at `.w64`, `.w128`, `.w512` with misaligned `%rsp` and index `2 ^ 29`, plus unaligned `vstore`/`vload` at `[rbx + 2147483648]`).
3. **Zero `sorry` / Native Tactics / `maxHeartbeats`**:
   * `grep -rnE 'sorry|bv_decide|native_decide|decide \+native|ofReduceBool|maxHeartbeats'` across `LeanQbe/T/Amd64/IselVec*.lean` and `LeanQbeTest/T/Amd64VecTest.lean` returned 0 matches.
4. **Axiom Audit (`#print axioms` in `LeanQbeTest/T/Amd64VecTest.lean`)**:
   * `LeanQbe.T.Amd64.x64Vmov_noLab`: `[propext]`.
   * `LeanQbe.T.Amd64.x64VecSpec`, `x64Vmovi_noLab`, `x64VslotSt_noLab`, `x64VslotLd_noLab`, `x64Vload_noLab`, `x64Vstore_noLab`, `x64Vop_noLab`, `chachaQrProg_run`, `floatVecProg_nan_run`, `bridgeProg_run`, `unalignedProg_run`: `[propext, Classical.choice, Quot.sound]`.
5. **Import Isolation**:
   * Verified via `lake env lean --deps` on `IselVecLemmas3.lean` and `Amd64VecTest.lean` plus transitive filesystem import BFS across all 5 files (`46` modules): zero Arm64/AArch64 imports and zero earlier untyped-IR (`LeanQbe.*` outside `LeanQbe.T.*` and `Kraken.*`) imports.
