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
| K3 | `6aa97bf` | x64 `div` and `idiv` (all widths, reg/mem, `#DE` fault, hardware tests) |
| K3+ | `89d18c6` | x64 parser: all condition-code suffixes (`ge`/`nl`, `g`/`nle`, `o`/`no`, `s`/`ns`, `p`/`pe`/`np`/`po`) |

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

## K3: x64 `div` and `idiv` in Kraken (commit `6aa97bf`)

Added by helper `krakendiv` in `kraken/lean-qbe-dev` and fast-forwarded to the consumer:

- `Operation.div` and `Operation.idiv (src : RegOrMem w)` across all widths (8, 16, 32, 64 bits):
  divides `ah:al` (8-bit) or `dx:ax` / `edx:eax` / `rdx:rax` by `src`, writes quotient to `al`/`rax`
  and remainder to `ah`/`rdx` (zero-extending 32-bit results), and leaves status flags `undefined`.
  `idiv` truncates toward zero (`Int.tdiv`/`Int.tmod`).
- `#DE` (division by zero, or quotient overflow including `INT_MIN / -1`) is modelled via a new fault
  constructor `Effects.divide_error` (`Effects.All` maps it to `False`, matching QBE's undefined
  division semantics).
- Parser (string and `x64` syntax), AT&T and Intel printers, round-trip and `#DE` unit tests, plus
  hardware differential tests `Kraken/X64/Test/asm/test_{div,idiv}.S`: `asm_tests.py --skip-sde`
  passes 52/52 natively, and `fuzz_x64.py` passes 6,000 random sequences with 0 failures.
- Note on bit-scan instructions (`tzcnt`, `lzcnt`, `bsr`, `popcnt`): upstream PR #216 (`fb94f20`,
  `b304cbf`) already implements them; we did not duplicate it since QBE's IL has no bit-scan ops.

## Step 5 (part 1): Union-Find end to end on AArch64 (lean-qbe commit `1b51e20`)

`LeanQbe/Arm64/UnionFind.lean` (imported by `LeanQbeArm64.lean`) compiles `UnionFind.find` (with path
halving) and `UnionFind.unionInline` through `compileFn Arm64.isa`, checks the emitted AArch64
assembly by `kernel_rfl`, and connects `compileFn_correct` with `UnionFind.find_correct` and
`UnionFind.unionInline_correct` to prove end-to-end theorems stated solely in terms of Kraken's
AArch64 operational semantics (`step1`) and the functional partition model (`uf`, `merge`):

- `find_arm64_correct`: in any `[Host]` containing `findCode` at `k₀` under `Host.LabelsUnique`, from
  `x0 = p`, `x1 = x` (`x.toNat < n`), `x30 = ra`, `sp` 16-byte aligned, and `dmem =⋆ uf p n rep ⋆ R`,
  execution reaches `ra` with `x0 = rep x`, `x19`–`x29` and `sp` restored, and `dmem =⋆ uf p n rep ⋆ R`.
- `unionInline_arm64_correct`: in any `[Host]` containing `unionInlineCode` at `k₀` under
  `Host.LabelsUnique`, from `x0 = p`, `x1 = x`, `x2 = y` (`x, y < n`), `x30 = ra`, `sp` 16-byte
  aligned, and `dmem =⋆ uf p n rep ⋆ R`, execution reaches `ra` with `x19`–`x29` and `sp` restored,
  and `dmem =⋆ uf p n (merge rep x y) ⋆ R`.
- `find_arm64_nonvacuous` and `unionInline_arm64_nonvacuous`: concrete host `ufHost` containing both
  `findCode ++ unionInlineCode` and concrete initial states on `uf_init` (`init 4` at `0x2000`),
  proving `find(0x2000, 3)` returns `3` and `unionInline(0x2000, 1, 2)` merges `1` and `2` while
  keeping `0` distinct.
- `test/arm64/unionfind_main.c`: C driver linked with both our compiled AArch64 assembly and stock
  QBE `-t arm64` output via `test/arm64/run.sh` (14/14 PASS under `qemu-aarch64`).

## Step 4 & Step 5 (R3 update): Calls, Exits, Spills, and Module Linking on AArch64 (commit `1ff3055`)

Following `@rega`'s R3 (`8344d4f`), all functions on AArch64 emit `Arm64.prologue`/`Arm64.epilogue`
(saving and restoring `x30` in the 16-byte-aligned stack frame `frameSize ns = (8*ns + 8 + 15)/16*16`),
and `LeanQbe/Arm64/{Tracer,LitmusCode,Litmus,UnionFind}.lean` are updated and extended:

- **`LeanQbe/Arm64/LitmusCode.lean`** (regenerated by `test/arm64/GenLitmus.lean`): all 12 litmus
  functions (`tracer`, `ifelse`, `sumto`, `evenodd`, `nested`, `swap`, `inc`, `callinc`, `check`,
  `twice`, `spill10`, `sumcall`) plus module compiles `callinc_module_compile`, `twice_module_compile`,
  and `sumcall_module_compile` checked by `kernel_rfl`.
- **`LeanQbe/Arm64/Litmus.lean`**:
  - `sumto_correct` & `sumto_nonvacuous` (16-byte stack frame).
  - `callinc_module_fnspec`, `callinc_correct`, `callinc_nonvacuous`: links `[inc, callinc]` via
    `compile_correct` (stack bounds 16 and 32 bytes; `callinc` spills `a` to slot 0 across two calls to
    `inc`).
  - `twice_module_fnspec`, `twice_correct`, `twice_nonvacuous_exit`: links `[check, twice]` via
    `compile_correct` (`nX = 16`, stack bounds 16 and 48 bytes; `check` exits to `"fail"` with the
    failing argument in `x0` and 16-byte aligned entry `sp`).
  - `spill10_correct` & `spill10_nonvacuous`: leaf function with 10 simultaneous live values.
- **`LeanQbe/Arm64/UnionFind.lean`**:
  - `uf_module_compile` & `uf_module_fnspec`: links `[findFn, unionFn]` (`union` spills 3 values across
    two calls to `find`; stack bounds `16` and `48` bytes).
  - `find_arm64_correct`, `union_arm64_correct`, `unionInline_arm64_correct`, and concrete-host
    non-vacuity theorems `find_arm64_nonvacuous`, `union_arm64_nonvacuous`, `unionInline_arm64_nonvacuous`.

## Step 7: `lrat-trim` End-to-End on Kraken AArch64 (`LeanQbe/Arm64/LratTrim.lean`, commit `1ff3055`)

`LeanQbe/Arm64/LratTrim.lean` (imported by `LeanQbeArm64.lean`) compiles the 4-function verified LRAT
checker module `LratTrim.lratCheckFns` through `compile Arm64.isa`, checks the emitted AArch64
assembly (649 directives total) in the kernel (`rup_compile`, `strict_compile`, `clause_compile`,
`proof_compile`, `lrat_module_compile` by `kernel_rfl`), and links all four contracts via
`compile_correct` and `lratEnv_step`:

| Function | Spill slots (`Arm64.isa`) | Frame size | Stack bound (`lratBound`) |
|---|---|---|---|
| `br_check_clause_non_strictly_by_propagation` (`checkRup`) | 17 | 144 B | 144 B |
| `br_check_clause_strictly_by_resolution` (`strictCheck`) | 9 | 80 B | 80 B |
| `br_check_clause` (`checkClause`) | 0 | 16 B | 160 B (`16 + max 144 80`) |
| `br_check_proof` (`checkProof`) | 7 | 64 B | 224 B (`64 + 160`) |

- **`lrat_module_fnspec`**: links all 4 functions in any AArch64 `[Host]` with `LabelsUnique` and
  `target.Defined hh "lrat_fail"`, parameterized over `(nX : Nat) (hnX : nX ≤ 80)` exit stack bytes.
- **`checkProof_arm64_correct`**: closed Kraken-AArch64 end-to-end theorem for `br_check_proof` (generic
  in `[Host]`, `k₀`, and `k_fail` under `Host.LabelsUnique`), proving that from any state satisfying
  `CheckProofPre` for `cnf₀` with `st` in `x0`, 224 bytes of stack below `sp`, return address `ra` in
  `x30`, and 16-byte aligned `sp`, execution either:
  1. returns to `ra` with `cnf₀.Unsat`, callee-saved registers `x19`–`x29` and `sp` restored, and
     `FullMemInv` preserved in memory; or
  2. exits to `"lrat_fail"` at `Host.addrOf k_fail` with 16-byte aligned entry `sp`.
- **`checkProof_arm64_nonvacuous`**: concrete-byte non-vacuity instance on `lratHost`
  (`lratCheckCode ++ [.label "lrat_fail"]`) and `(zeros224 ++ nvCheckBytes).At 0x0f20#64` (via
  `nvCheck_pre`).
- **`test/arm64/run.sh`**: 26/26 PASS under `qemu-aarch64` across all 13 suites (`callinc`, `evenodd`,
  `ifelse`, `lrat_trim`, `nested`, `spill10`, `sumcall`, `sumto`, `swap`, `tracer`, `twice`, `uf`,
  `unionfind`) for both our compiled AArch64 assembly and stock QBE `-t arm64`.
- All headline theorems depend only on `[propext, Classical.choice, Quot.sound]`.

## Arm64 `compile_sound`, Label Entry Points, and Accepting UNSAT Witness (#176, #177, #183)

Updated `LeanQbe/Arm64/{LitmusCode,Litmus,UnionFind,LratTrim}.lean` and `test/arm64/GenLitmus.lean`
to use `compileModule` + `compile_sound` and `Labels.label` entry/exit points, and added the
concrete accepting UNSAT witness on AArch64:

- **`LeanQbe/Arm64/LitmusCode.lean` & `Litmus.lean`**:
  - `callinc_module_compile`, `twice_module_compile`, `sumcall_module_compile` now check
    `compileModule` pairs `(code, bounds)` via `kernel_rfl`.
  - `callinc_module_fnspec` and `twice_module_fnspec` link via `compile_sound`.
  - `sumto_correct`, `callinc_correct`, `twice_correct`, `spill10_correct` (and their non-vacuity
    theorems) enter at `Labels.label "..."`, and `twice_correct` exits to `Labels.label "fail"`
    under `target.Defined hh "fail"`.
- **`LeanQbe/Arm64/UnionFind.lean`**:
  - `uf_module_compile` & `uf_module_fnspec` check and link via `compileModule`/`compile_sound`
    (`ufBounds = [("find", 16), ("union", 48)]`); removed the manual `findFn_*`/`unionFn_*` lemmas.
  - `find_arm64_correct`, `union_arm64_correct`, `unionInline_arm64_correct` (and their
    non-vacuity theorems) enter at `Labels.label "..."`.
- **`LeanQbe/Arm64/LratTrim.lean`**:
  - `lrat_module_compile` (`compileModule isa 0 [] ["lrat_fail"] 80 lratCheckFns`) &
    `lrat_module_fnspec` (`nX = 80`, using `compile_sound`, `lratCheckFns_wf`, `lratEnv_sound`);
    removed the manual `rupFn_*`/`strictFn_*`/`clauseFn_*`/`proofFn_*` lemmas.
  - `checkProof_arm64_correct` and `checkProof_arm64_nonvacuous` enter at
    `Labels.label "br_check_proof"` and exit to `Labels.label "lrat_fail"` under `target.Defined`.
  - **`lrat_accepts_fnspec` & `checkProof_arm64_accepts`**: links `lratAcceptEnv` via `compile_sound`
    and instantiates `@logic`'s `checkProof_accepts_nonvacuous` (`X := fun _ _ _ => False`) on
    `(zeros224 ++ nvAcceptBytes).At 0x0f20#64` (CNF `[[1], [-1]]` with a 1-step resolution proof),
    proving `Eventually (step1 Host.exe) (fun st => st.pc = 0x1234 ∧ nvAcceptCnf.Unsat)`.

## Next

- Complete any remaining cross-module checks or downstream Arm64 tasks if requested.
