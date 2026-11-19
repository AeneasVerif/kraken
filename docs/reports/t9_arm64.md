# `t9-arm64`: AArch64 Scalar `GprIsa` + `GprTarget` (`T9`)

Owner: `t9-arm64` (forked cleanly from `main` after `T11b @ 27aa0ae`).
Owned files:
- `LeanQbe/T/Arm64/Isel.lean`
- `LeanQbe/T/Arm64/IselLemmas1.lean`
- `LeanQbe/T/Arm64/IselLemmas2.lean`
- `LeanQbe/T/Arm64/IselLemmas3.lean`
- `LeanQbe/T/Arm64/IselLemmas4.lean`
- `LeanQbeTest/T/Arm64IselTest.lean`
- `docs/reports/t9_arm64.md`

## Status

| Deliverable | LOC | Standalone (`-DwarningAsError=true`) | State |
|---|---|---|---|
| `LeanQbe/T/Arm64/Isel.lean` | 808 | 1.61s | `armGpr : GprIsa Reg Empty ArmCond Directive`, `armSupportsScalarOp` |
| `LeanQbe/T/Arm64/IselLemmas1.lean` | 1,190 | 6.07s | `clearFlags`, `mov`, `movi`, `setcc`, `jmp`, `jcc`, `jnzGpr`, `load`, `store` specs + 9 `NoLab` theorems |
| `LeanQbe/T/Arm64/IselLemmas2.lean` | 1,166 | 2.06s | `.bool`, `copy`, `zext`/`sext`/`trunc`, `ofBool`, `and`/`or`/`xor`/`not`/`add`/`sub`/`mul`/`neg`, `shl`/`lshr`/`ashr`/`rotl`/`rotr` |
| `LeanQbe/T/Arm64/IselLemmas3.lean` | 1,335 | 4.86s | `cmp`, `select`, `udiv`/`sdiv`/`urem`/`srem`/`udiv0`/`sdiv0`, `bswap`, `clz`/`cls`/`rbit`/`ctz`, `addc`/`subb` |
| `LeanQbe/T/Arm64/IselLemmas4.lean` | 1,474 | 7.43s | `umulw`/`smulw`, `fshl`/`fshr`, `armOp_spec`, `armGprSpec`, `armOp_noLab`, `ParserChecks` (`Kraken.AArch64.Parser`) |
| `LeanQbeTest/T/Arm64IselTest.lean` | 766 | 2.03s | Kernel `rfl`, `VariantHint`, 7 `Host.ofLayout` witness suites, `#print axioms` |
| **Proof total (`IselLemmas1..4`)** | **5,165** | — | Max single proof file `1,474` LOC (`<= 1,500`), max standalone `7.43s` (`< 120s`) |

## Design & Soundness Summary

### 1. Core `armGpr` Lowering & `.SP` / Sub-Word Corner Cases (`LeanQbe/T/Arm64/Isel.lean`)
- **`armGpr : GprIsa Reg Empty ArmCond Directive`** over `LeanQbe.T.Arm64.Base` (`armMach`, `armScratch := [.reg .X16, .reg .X17]`, `armCondReads`, `armNegCond`):
  - **`clearFlags` / `zeroFlags`**: `armZeroFlags := [.cs, .vs]`; `armClearFlags` emits `ADDS_s xzr, xzr, xzr` (`0 + 0 = 0`, setting `c = false`, `v = false`, `FlagMask.all`, zero allocatable GPRs clobbered).
  - **`mov` / `movi` / `setcc` for all `Reg = XRegOrSp`**: `armMov` uses `ADD_e rd, rs, #0` (no SP alignment check, `FlagMask.none`); `armMovi` and `armSetcc` use `LDR rd, =c` / `CSINC rd, xzr, xzr, (armNegCond c).toKraken` directly for `.reg d` and route `.SP` via scratch `.X16` + `armIselMovToSp .X16` (`add sp, x16, #0`, named `armIselMovToSp` to avoid colliding with `Frame.lean`'s `armMovToSp` when `LeanQbeArm64` imports both).
  - **`jnzGpr` upper-bit safety**: Because `GprHolds regVal .bool b` only constrains bits `0..7` (`regVal.setWidth 8 = BitVec.ofNat 8 b.toNat`), `armJnzGpr` uses `TBNZ w_r, #0, label` (`FlagMask.none`), copying `.SP` through `.X16` via `ADD_e x16, sp, #0` when `r = .SP`.
  - **Memory `load`/`store` `.SP` alignment & `.bool .flag` stores**: To avoid Kraken's `AddrExpr.checkSPAlignment` fault when `SP % 16 ≠ 0`, `armSetupAddr` copies `.SP` to scratch `.X16` via `ADD_e` so `mem.base` is always `.low (.reg rx) .W64` (never `.SP`), adding arbitrary 64-bit displacements in `.X16` via `ADD_e` (when `0 < disp < 4096`) or `LDR .X17` literal pool + `ADD_s`. In `armStore .bool (.flag cc)`, `CSINC .X17, xzr, xzr, (armNegCond cc).toKraken` materializes the flag into `.X17` before any address computation.
- **Scalar opcode coverage (`armSupportsScalarOp`, `defaultSupportsScalarOp [8, 16, 32, 64] true false true` with custom rules)**:
  - `[8, 16, 32, 64]`: `copy`, `add`, `sub`, `mul`, `neg`, `and`, `or`, `xor`, `not`, `shl`, `lshr`, `ashr`, `rotl`, `rotr`, `ofBool`, `udiv`, `sdiv`, `urem`, `srem`, `udiv0`, `sdiv0` (`UDIV`/`SDIV` match `OpCode.udiv0`/`sdiv0` on `/ 0` and `INT_MIN / -1`), branchless `select` (`CSEL`), `cmp` (`.gpr` and `.flag`), `zext`, `sext`, `trunc`, `bitcast`, plus `.bool` (`copy`, `and`, `or`, `xor`, `not`). At widths `8`/`16`, `armExt32` zero/sign-extends operands (`UBFM`/`SBFM`) and `AND_i` masks variable shift/rotate counts mod `8` (`#7`) / `16` (`#15`).
  - `[16, 32, 64]`: `bswap` (`REV16` at 16, `REV` at 32/64).
  - `[32, 64]`: `clz`, `cls`, `rbit`, `ctz` (`RBIT + CLZ`; `hasPopcnt = false`), `addc` (carry-in/out over `.flag .cs`, `.gpr`, `.imm` via `ADDS_s`/`ADCS`/`ADC`), `subb` (borrow inversion over `.flag .cc`, `.gpr`, `.imm` via `SUBS_s`/`SBCS`/`SBC`), `umulw`/`smulw` (`UMADDL`/`SMADDL` + `UBFM` at 32; `MADD` + `UMULH`/`SMULH` with aliasing guard via `.X16` at 64), and `fshl`/`fshr` (`EXTR` for `.imm`, `ANDS_i #mask` + `SUB_s` + `LSLV`/`LSRV` + `ORR_s` + `CSEL .EQ` for `.gpr` so runtime shift-by-0 preserves exact bits).

### 2. Verification & Deliverables (`IselLemmas1..4.lean`, `Arm64IselTest.lean`)
- **`LeanQbe.T.Arm64.armGprSpec : GprTarget armMach armGpr armScratch`** (`IselLemmas4.lean`) with zero extra hypotheses.
- **Complete `NoLab` suite (all 10 builders)**: `armClearFlags_noLab`, `armMov_noLab`, `armMovi_noLab`, `armSetcc_noLab`, `armJmp_noLab`, `armJcc_noLab`, `armJnzGpr_noLab`, `armLoad_noLab`, `armStore_noLab` (`IselLemmas1.lean`), and `armOp_noLab` (`IselLemmas4.lean`).
- **Kernel `rfl` `ParserChecks` (`IselLemmas4.lean`)**: `parser_moves_branches_rfl`, `parser_mem_sp_flag_rfl`, `parser_ops_rfl` verified against `Kraken.AArch64.Parser` (`⸨prog| ... ⸩`).
- **Concrete `Host.ofLayout` execution witnesses & kernel checks (`Arm64IselTest.lean`)**:
  - `armGpr_supports_rfl`, `armGpr_variantHint_rfl` (`VariantHint.decInc` / `.disp` on `add`/`sub`, rejection of non-`.default` on `addc`/`subb`).
  - `div0_witness` (`udiv0`/`sdiv0` on `/ 0` and `INT_MIN / -1`).
  - `bitCount_witness` (`clz 64`, `cls 32`, `rbit 32`, `ctz 32`).
  - `carry_borrow_chain_witness` (`clearFlags` + multi-word `addc` `.cs` chain + `subb` `.cc` borrow chain).
  - `mul_funnel_select_witness` (`umulw 64` with input/dst aliasing, `smulw 32`, `fshl`/`fshr` `.imm`/`.gpr`/shift-by-0, `select`).
  - `subword_garbage_witness` (`ashr i8`, `shl i16`, `cmp .slt i8`, `sdiv 16` with upper garbage bits `[8..63]`/`[16..63]`).
  - `sp_corner_witness` & `jnzGpr_false_witness` (unaligned `SP = 0x123456789ABCDEF3`, `.bool .flag` store & load at unaligned `SP + 16`, `movi`/`mov`/`setcc`/`jnzGpr .SP`, and `jnzGpr` `.bool false` fallthrough with bits `8..63` set).

## Hygiene, Build, Import-Closure & Axiom Audit
- **Build & co-import**: `timeout 300 time lake build --wfail LeanQbe.T.Arm64.FrameLemmas LeanQbe.T.Arm64.Isel LeanQbe.T.Arm64.IselLemmas1 LeanQbe.T.Arm64.IselLemmas2 LeanQbe.T.Arm64.IselLemmas3 LeanQbe.T.Arm64.IselLemmas4 LeanQbeTest.T.Arm64IselTest` exited `0` (`118` jobs, `26.67s`), simultaneous co-import of `Frame` + `FrameLemmas` + `Isel` + `IselLemmas1..4` passed with zero symbol collisions, and every module passed standalone `lake env lean -DwarningAsError=true` in `≤ 7.5s`.
- **No `sorry` or native tactics**: Zero `sorry`/`admit`/`axiom` declarations, zero `bv_decide`, `native_decide`, `decide +native`, `ofReduceBool`, `ofReduceNat`, `maxHeartbeats`, or `maxRecDepth`.
- **Import-closure audit**: Inspected transitive `.header.moduleNames` closure across all 6 owned modules (`2,517` modules): strictly `LeanQbe.T.*` (no `Amd64`, no untyped E1 `LeanQbe.*`), `LeanQbeTest.T.Arm64IselTest`, and `Kraken.*` (no `Kraken.X64.*`).
- **Axioms (`#print axioms`)**: `armGprSpec`, all 10 `NoLab` theorems, and all 7 `Arm64IselTest` witness theorems depend strictly on `[propext, Classical.choice, Quot.sound]`.

## Optional Post-Merge Cleanup (Not Modified Here)
- Per `#266`, local `armDirFallsTo` / `armWp_cons` / `armWp_append` / `armFallsTo_of_wp` helpers in `IselLemmas1.lean` (mirroring `FrameLemmas.lean`) were kept untouched and can be consolidated into `LeanQbe/T/Arm64/Base.lean` post-merge.
