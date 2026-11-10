# Kraken worktrees and upstreamed lemmas (worker `kraken`)

## Worktrees

| Worktree | Branch | Role |
|---|---|---|
| `/usr/local/google/home/andreser/kraken/lean-qbe-dev` | `lean-qbe-dev` | development |
| `/usr/local/google/home/andreser/kraken/lean-qbe` | `lean-qbe` | consumer (lean-qbe's Lake path dependency); fast-forwarded only to green commits |

Base: `andreser/bedrock2-lrat-trim-proof` at `ae789b6`. That branch already contains the toolchain bump
to `leanprover/lean4:nightly-2026-11-08` (`617c404`, same change as `2644b16`), so the planned
cherry-pick of `2644b16` was empty and was skipped. No upstream tracking is configured; nothing is pushed.

Build check, in either worktree:

```bash
timeout 3000 lake build Kraken KrakenAArch64 KrakenBedrock2
```

The only warnings are the three pre-existing `declaration uses sorry` in Kraken's own examples
(`Kraken/X64/Examples/Examples.lean:112`, `:463`, `Kraken/X64/Examples/IncrementDMA.lean:70`).
`.lake` was seeded by copying `kraken/bedrock2/.lake` (same commit and toolchain), so the first build
replayed rather than rebuilt (166 jobs, 0.15 s).

## History

| Milestone | Commit | What |
|---|---|---|
| K0 | `ae789b6` | worktrees created, builds clean |
| K1 | `1fc7dfb` | x64 generic lemmas from Spike K (below) |
| K2 | `4952311` | AArch64 counterparts (below) |
| K2+ | `d0d005e` | `Host.label_undefined` (undefined labels resolve to -1), x64 and AArch64 |

## K1: x64 lemmas (commit `1fc7dfb`)

All statements are generic in the `Host` and the position. Axioms: only `propext`, `Classical.choice`,
`Quot.sound` (checked with `#print axioms` for every headline lemma below). No `sorry`.

| File | Lemmas |
|---|---|
| `Kraken/Data/List/Infix.lean` | `List.isInfixAt_singleton` |
| `Kraken/Layout.lean` | `Executable.sizeBefore_le_total`, `Executable.sizeBefore_eq_of_addrOf_eq` (executable below `2^64` bytes) |
| `Kraken/X64/Inert.lean` | `Directive.inert_label` |
| `Kraken/X64/WP/Host.lean` | `Host.label_eq_addrOf` (first definition), `Host.LabelsUnique`, `Host.LabelsUnique.first`, `Host.label_eq_addrOf_of_unique`, `Program.definedLabels`, `Host.labelsUnique_of_nodup` (decidable), `Host.ofLayout` (concrete hosts: zero size only for labels, size below `2^64`) |
| `Kraken/X64/WP/Basic.lean` | `Host.eventually_of_interp_cps`, `Host.step1_iff_interp` (converse, positive size), `Host.eventually_label`, `Program.wp_nil`, `Program.wp_singleton`, `Program.wp_label`, `Program.wp_append` |
| `Kraken/X64/WP/Control.lean` (new) | encodings `Directive.jmpTo`, `jccTo`, `callTo`, `ret`; `Host.eventually_jmp`, `eventually_jcc`, `eventually_jcc_taken`, `eventually_jcc_fallthrough`, `eventually_call`, `eventually_ret`; `Program.wp_callTo` |
| `Kraken/X64/Sep.lean` | `store_All_of_sep`, `load_All_of_sep` (now imports `Kraken.X64.OmniSemantics`) |
| `Kraken/X64/Regs.lean` (new) | `Reg64s.get_low64`, `get_low32`, `set_low64`, `set_low32`, `get64_set64_same`, `get64_set64_of_ne`, `get64_set64`, `set64_set64_same`, `set64_set64_comm`, `set64_get64_self`, `ext_get64`; `AddrExpr.interp_base_disp` |
| `Kraken/X64/WPTests.lean` (new) | parser encodings by `rfl`; a concrete host built with `Host.ofLayout`, `LabelsUnique` by `decide`, and `jmp L; L: ret` proved to return; the Spike K counterexample showing the first-definition hypothesis of `eventually_jmp` cannot be dropped |

Not upstreamed (they are compiler-shaped, not Kraken-shaped): `doWhile`, `ifThenElse`, `countdown`,
`dec64`. The `not_inert_*`/`size_pos_*` lemmas were not needed by anything.

The lean-qbe regression spike `spike/k/SpikeK.lean` still checks against the new Kraken (its names live
in namespace `SpikeK`).

## K2: AArch64 (commit `4952311`)

`Kraken/AArch64/{Inert,WP/Host,WP/Basic}.lean` are verbatim copies of the x64 files *including the
K1 additions* (label resolution, `LabelsUnique`, `Host.ofLayout`, CPS step lemma, `wp` rules); only
the import lines differ. This confirms Spike K's finding that these files are
architecture-independent. Duplication: 31 + 241 + 197 lines. Making Kraken architecture-generic would
remove it but is out of scope (plan 2.6).

| File | Lemmas |
|---|---|
| `Kraken/AArch64/WP/Control.lean` (new) | encodings `Directive.bTo`, `bCondTo`, `blTo`, `ret` (to `x30`), `cbzTo`, `cbnzTo` (any width); `Host.eventually_b`, `eventually_bCond`, `eventually_bCond_taken`, `eventually_bCond_fallthrough`, `eventually_bl` (`x30 := addrOf (i+1)`), `eventually_ret` (`s.regs.X30 = ra.toUInt64`), `eventually_cbz`, `eventually_cbnz` |
| `Kraken/AArch64/Regs.lean` (new) | `Reg64s.getXReg_setXReg_same/_of_ne`, `getXReg_setXReg`, `setXReg_setXReg_same/_comm`, `setXReg_getXReg_self`, `SP_setXReg`, normal forms for `getRegOrZr`/`setRegOrZr` (`x`, `w`, `xzr`) and `getRegOrSp`/`setRegOrSp` (`x`, `sp`) |
| `Kraken/AArch64/Sep.lean` | `store_All_of_sep`, `load_All_of_sep` |
| `Kraken/AArch64/WPTests.lean` (new) | parser encodings by `rfl`; concrete host where `bl f; b e; f: ret; e:` provably runs to the end |

`KrakenAArch64.lean` now imports `Regs` and `WP`. Axioms as for K1. lean-qbe's `spike/k/SpikeKAArch64.lean`
still checks (it does not import the new modules, so its root-namespace copies do not clash).

Note: with expected type `Kraken.Directive Instr` (e.g. the parser's output type) the dot forms
`.bTo` etc. do not resolve; write `Directive.bTo`. With expected type `Directive` (e.g. `Host.prog[i]?`)
they do.

## Arm64: the AArch64 `Target` instance (plan step 2d), lean-qbe commits `76a9d73`, `86d31fb`

`LeanQbe.Arm64.target : Target` implements Target **v1** (abi's 4684edf: op/load/store snippets, jnz on
`Truthy`, frames, calls, tail jumps) on Kraken AArch64, with no `sorry` and standard axioms only.
`timeout 900 lake build --wfail LeanQbeArm64` builds it.

| File | Content |
|---|---|
| `Arm64/Targ.lean` | registers (`XRegOrSp`), register sets, `mov` (= `add rd, rs, #0`, valid for `sp`), `movi` (literal pool `ldr x, =c`), `jmp` (`b`), `jnz` (`cbnz w_r`, i.e. QBE's low-32-bit test), `ret`, frame snippets |
| `Arm64/Isel.lean` | `op`, `load`, `store` snippets and `isa`. Class `w` ops use the 32-bit instruction forms, which match QBE's `lo32`/`zext32` exactly; immediates go to x16/x17 |
| `Arm64/TargLemmas.lean` | `Runs c s s'` (straight-line code falls through from `s` to `s'` in every host) with `nil/append/single/cons`; moves, constants, operands, loads and stores at every width/sign/class, `jmp`, `jnz`, `ret` |
| `Arm64/IselLemmas.lean` | `op_runs` for every `bin`/`cmp`/`ext`/`copy` at both classes (written by helper `arm64-isel`) |
| `Arm64/FrameLemmas.lean` | `sub/add sp`, `str/ldr [sp, #o]` with the alignment check, prologue, epilogue, slots, `bl`, `b` |
| `Arm64/Abi.lean` | the instance |
| `Arm64/Tracer.lean` | the tracer through `lowerFn_correct`: lowers to `add x0,x0,x1; str x0,[x2]; ret` by `rfl`; `tracer_correct` (Kraken AArch64 notions only, any host containing the code with unique labels) and `tracer_nonvacuous` (a concrete state meeting every premise) |

Register roles: scratch x16/x17; allocatable x0-x15; arguments x0-x7; results x0/x1; callee-saved
x19-x29; return address in x30 (`raRegs = [x30]`, `raBytes = 0`, `RetAddr` = empty region); x18 unused.
Frame: `frameSize ns = 8ns+8` rounded up to 16; `sub sp,sp,#F; str x30,[sp,#8ns]` and the mirror
image; `Saved` = the saved-x30 word plus padding.

Executed: the printed tracer assembly assembles with `aarch64-linux-gnu-gcc` and returns the right sum
and stores it, for 5 vectors under `qemu-aarch64` (harness in my scratch folder, `arm64run/`).

Findings:

- `bv_decide` adds `Lean.ofReduceBool`; all bit-level facts are proved with `ext` + `simp` + `omega`
  instead. 64-bit constants via `movz`/`movk` needed mask reasoning; the literal pool (`ldr x, =c`,
  which Kraken models as returning `c`) avoids it and is one instruction.
- Kraken faults (`unaligned_sp`) on `sp`-based accesses when `sp % 16 ≠ 0`; Target v1 got `spOk` for this.
- `prologue_spec` needs `frameSize ns ≤ 2^64` to split the frame region; Target v1 got that premise.
- Known limits (assembly-time, loud): frames ≥ 4096 bytes (`sub sp` immediate), and branch ranges.
- `⋆` is left-associative (`p ⋆ q ⋆ r = (p ⋆ q) ⋆ r`); `ac_rfl` works for rearranging.

## Step 4 (part 1): AArch64 litmus parity (lean-qbe commits `2e0ac0f`, `38d1e17`)

All six litmus programs (`tracer`, `ifelse`, `sumto`, `evenodd`, `nested`, `swap` from generic
`LeanQbe/Examples/LitmusProgs.lean`) now go through the full AArch64 pipeline (`compileFn Arm64.isa`:
mid-end `Func.opt`, first-fit allocation oracle `Spill.hints`, verified lowering `Rega.lowerFn`):

| File | Content |
|---|---|
| `LeanQbe/Arm64/LitmusCode.lean` | GENERATED by `test/arm64/GenLitmus.lean`: for each of the 6 programs, `…Code : Program` (parsed by `parseAArch64`), `…_compile : compileFn isa … = .ok …Code` by `kernel_rfl`, and `…_fnspec` via `compileFn_correct` in any AArch64 host |
| `LeanQbe/Arm64/Litmus.lean` | `sumto_correct`: end-to-end theorem on Kraken AArch64 (`x0 = n < 2^32`, `x30 = ra`, `sp` 16-aligned, `dmem =⋆ R` → `pc = ra`, `x0 = tri n.toNat`, `x19`–`x29` and `sp` preserved, `dmem =⋆ R`), generic in `[Host]` and `k₀` under `LabelsUnique`; `sumto_nonvacuous` (concrete host and state, `x0 = 3` → `pc = 0x1234 ∧ x0 = 6`) |
| `test/arm64/Emit.lean`, `GenLitmus.lean`, `run.sh` | AArch64 emitter, code/proof generator, and test runner (`test/arm64/run.sh`: 12/12 PASS — 6 programs × our AArch64 assembly and stock QBE `-t arm64` on `leanqbe --il`, cross-assembled with `aarch64-linux-gnu-gcc` and run under `qemu-aarch64` against `test/*_main.c`) |

## Next

- Upstream x64 `div`/`idiv` (and bit-scan instructions) into Kraken (`krakendiv` helper in progress).
- Regenerate `LitmusCode.lean` and extend `LeanQbe/Arm64/Litmus*.lean` when `rega`'s R3 (calls, exits,
  spills, linking) and union-find (step 5) land.
