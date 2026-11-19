# `t11b-abi`: Target-Generic ABI/Frame Lemmas & SysV x64 / AAPCS64 `FrameTarget` (`T11b`)

Owner: `t11b-abi` (forked from `main @ 72eb727`).
Owned files:
- `LeanQbe/T/AbiLemmas.lean`
- `LeanQbe/T/Amd64/Frame.lean`
- `LeanQbe/T/Amd64/FrameLemmas.lean`
- `LeanQbe/T/Arm64/Frame.lean`
- `LeanQbe/T/Arm64/FrameLemmas.lean`
- `LeanQbeTest/T/Amd64FrameTest.lean`
- `LeanQbeTest/T/Arm64FrameTest.lean`
- `docs/reports/t11b_abi.md`

## Status

| Deliverable | LOC | Standalone (`-DwarningAsError=true`) | State |
|---|---|---|---|
| `LeanQbe/T/AbiLemmas.lean` | 317 | 1.08s | Built cleanly (`0` warnings, `0` arch/E1 imports) |
| `LeanQbe/T/Amd64/Frame.lean` | 138 | 0.36s | `x64Frame : FrameIsa Reg64 Directive` |
| `LeanQbe/T/Amd64/FrameLemmas.lean` | 570 | 1.14s | `x64FrameSpec`, `NoLab`, `ParserChecks` (`Kraken.X64.Parser`) |
| `LeanQbe/T/Arm64/Frame.lean` | 173 | 0.39s | `armFrame : FrameIsa Reg Directive` |
| `LeanQbe/T/Arm64/FrameLemmas.lean` | 927 | 1.64s | `armFrameSpec`, `NoLab`, `ParserChecks` (`Kraken.AArch64.Parser`) |
| `LeanQbeTest/T/Amd64FrameTest.lean` | 407 | 1.97s | Kernel `rfl`, arbitrary-`ns` round-trip, concrete `Host.ofLayout` e2e |
| `LeanQbeTest/T/Arm64FrameTest.lean` | 456 | 1.57s | Kernel `rfl`, arbitrary-`ns` round-trip, `.SP` checks, concrete `Host.ofLayout` e2e |

## Design & Verification Summary

### 1. Target-Generic ABI & Frame Helpers (`LeanQbe/T/AbiLemmas.lean`)
Imports strictly `LeanQbe.T.TargetLemmas`, `LeanQbe.T.Logic.MemLemmas`, and `LeanQbe.T.Logic.Bytes` (zero architecture or untyped-E1 imports):
- **Boolean/BitVec/Int64 arithmetic**: `Nat.blt_iff_lt`, `Int64_toBitVec_ofNat`, `ofInt_toInt_ofNat`, `ofInt_toInt_ofBitVec`, `ofInt_toInt_add`, `ofInt_toInt_add_toNat`, 16-byte stack-alignment lemmas `aligned16_sub`, `aligned16_add`, `aligned16_add8_sub`, `aligned16_add8_sub_call`.
- **ABI register holding**: `abiGprHolds_bool_of_gprHolds`, `abiGprHolds_bits_of_gprHolds`, `abiGprHolds_bits64_of_gprHolds`.
- **Memory region/array conversions**: `cell64_region`, `toBytes8_ofInt_ofBytes`, `region_cell64`, `region_sep_cell64`, `region_split3`, `region_frame_split`, `region_frame_split_ra`, `array64_region`, `region_array64`.
- **`Target` footprint & contract composition**: `Target.entry_exit`, `Target.retAddr_of_entry'`, `Target.retAddr_of_entry`, `Target.exit_of_entry`, `Target.exit_of_entry_assoc`, `Target.FnSpec.of_spec`, `Target.FnSpec.mono_exit`, `Target.FnSpec.mono_stack`, `Target.link`.

### 2. SysV x64 Frame (`LeanQbe/T/Amd64/{Frame,FrameLemmas}.lean`)
- **`x64Frame : FrameIsa Reg64 Directive`**: `sp := .rsp`, `scratch := [.r10, .r11]`, `allocatable := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9]`, `calleeSaved := [.rbx, .rbp, .r12, .r13, .r14, .r15]`, `raRegs := []`, `argRegs := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]`, `retRegs := [.rax, .rdx, .rcx, .rsi, .rdi, .r8, .r9]`, `bitWidths := [8, 16, 32, 64]`, `raBytes := 8`, `frameSize ns := 8 * ns + (if ns % 2 == 0 then 8 else 0)` (reducible by kernel `rfl`).
- **Large frames & slot offsets (`≥ 2 ^ 31`)**: Controlled by `x64FitsImm31 n := Nat.blt n 0x80000000`. Direct 32-bit sign-extended immediates/displacements are emitted when `< 2^31`; otherwise `movabs $c, %r10` (`x64MoviD`) materializes the 64-bit constant into scratch `%r10`, using `subq`/`addq %r10, %rsp` in `prologue`/`epilogue` and indexed addressing `(%rsp, %r10, 1)` (`x64AtSpR10`, `maskNone` flags) in `slotSt`/`slotLd`. `x64Prologue_spec`, `x64Epilogue_spec`, `x64SlotSt_spec`, and `x64SlotLd_spec` hold unconditionally for all `x64FrameSize ns + 8 ≤ 2 ^ 64`.
- **ABI canonicalization (`x64CanonAbi`)**: Zero-extends low 8/16/32 bits to full 64 bits with `maskNone` flags (`movzbl %r_b, %r_d` for `.bool`/`.bits 8`, `movzwl %r_w, %r_d` for `.bits 16`, `movl %r_d, %r_d` for `.bits 32`, `[]` for `.bits 64`).
- **Verification**: `x64FrameSpec : FrameTarget x64Mach x64Frame x64CondReads`, all 8 `NoLab` theorems (`x64Prologue_noLab`, ..., `x64Ret_noLab`), and 15 kernel-checked `Kraken.X64.Parser` `ParserChecks`.

### 3. AAPCS64 Arm64 Frame (`LeanQbe/T/Arm64/{Frame,FrameLemmas}.lean`)
- **`armFrame : FrameIsa Reg Directive`**: `sp := .SP`, `scratch := [.reg .X16, .reg .X17]`, `allocatable := x0..x15`, `calleeSaved := x19..x29`, `raRegs := [.reg .X30]`, `argRegs := x0..x7`, `retRegs := x0..x7`, `bitWidths := [8, 16, 32, 64]`, `raBytes := 0`, `frameSize ns := (8 * ns + 8 + 15) / 16 * 16`.
- **Large frames (`≥ 4096`), large slot offsets (`≥ 32768`), and `.SP` routing**:
  - `armSubSp`/`armAddSp` check `armFitsImm12 n := Nat.blt n 4096`; larger offsets load via literal pool (`ldr x16, =n`) and execute `sub`/`add sp, sp, x16` (using `UXTX #0`, `maskNone` flags).
  - `armStSpXReg`/`armLdSpXReg` check `armFitsMemOff o := Nat.blt o 32768`; larger offsets load via `ldr x16, =o` and index via `[sp, x16]` (`armAtSpIdx .X16`, preserving flags).
  - `.SP` operations in `armSlotSt`, `armSlotLd`, and `armCanonAbi` route via `.X17` (`slotSt`/`slotLd`, safely disjoint from `.X16` used by large offsets) or `.X16` (`canonAbi`). `armPrologue_spec`, `armEpilogue_spec`, `armSlotSt_spec`, and `armSlotLd_spec` hold unconditionally for `armFrameSize ns ≤ 2 ^ 64` and `sp.toNat % 16 = 0`.
- **ABI canonicalization (`armCanonAbi`)**: Emits `ubfm x_r, x_r, #0, #7` (`.bool`/`.bits 8`), `ubfm x_r, x_r, #0, #15` (`.bits 16`), `orr w_r, wzr, w_r` (`mov w_r, w_r`, `.bits 32`), or `[]` (`.bits 64`), all with `maskNone` flags.
- **Verification**: `armFrameSpec : FrameTarget armMach armFrame armCondReads`, all 8 `NoLab` theorems (`armPrologue_noLab`, ..., `armRet_noLab`), and 19 kernel-checked `Kraken.AArch64.Parser` `ParserChecks`.

## Hygiene & Axiom Audit
- **Build (`lake build --wfail`)**: Built all 7 modules cleanly with `-DwarningAsError=true`.
- **`sorry` & native tactics**: Zero `sorry`/`sorryAx`; zero `bv_decide`, `native_decide`, `decide +native`, `ofReduceBool`, or `ofReduceNat`.
- **Import isolation (`G5` + arch separation)**: Verified transitive `.header.moduleNames` closures:
  - `LeanQbe.T.AbiLemmas` contains zero architecture (`Amd64`/`Arm64`/`Kraken.X64`/`Kraken.AArch64`) and zero untyped E1 imports.
  - `LeanQbeTest.T.Amd64FrameTest` contains zero Arm64/AArch64 and zero E1 imports.
  - `LeanQbeTest.T.Arm64FrameTest` contains zero Amd64/X64 and zero E1 imports.
- **Axioms (`#print axioms`)**: `x64FrameSpec`, `armFrameSpec`, all `NoLab` theorems, all checked `AbiLemmas` theorems, `x64EchoProg_spec`, `callerCallee_e2e` (x64 & Arm64), `armEchoProg_spec`, and `armSpCorner_spec` depend strictly on `[propext, Classical.choice, Quot.sound]` (or subsets thereof).
