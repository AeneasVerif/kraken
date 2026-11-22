> **[Historical design note]** Written during an earlier milestone; several `LeanQbe/*.lean` (E1) and `scripts/headline.txt` paths referenced below have since moved to `LeanQbe/T/` and `scripts/headlines.d/`. See `README.md` for current paths.

# abi: target signature, function contract, x64 instance

Owner: `abi`. Files: `LeanQbe/{Abi,AbiLemmas}.lean`, `LeanQbe/Amd64/{Targ,TargLemmas,FrameLemmas}.lean`,
`spike/frames/`. Helper `memframe` (added by abi) wrote `AbiLemmas.lean`, `Amd64/FrameLemmas.lean`
and is writing `spike/frames/FramesProof.lean`.

## Status

| Milestone | State |
|---|---|
| A0: `Target` v0 + `FnSpec` v0 (`Abi.lean`) | done; superseded by v0.1 |
| `Target` v0.1 (generic `op`/`load`/`store` snippets, `jnz` on `Truthy`, rega #18) | done, reviewed (reviewer #35: snippet specs fine) |
| x64 instance `Amd64.target` | done, no sorry, std axioms, in headline.txt |
| `AbiLemmas` (memory framing for rega's `MemFacts`, Entry → Exit) | done (memframe) |
| `Target` v1 + `FnSpec` v1 (frames, calls, exits) in `Abi.lean` | **accepted and frozen** (reviewer #113, coordinator #114, at db4cf24) |
| x64 instance of v1 | done, no sorry |
| Linking: `FnSpec.of_spec`, `mono_exit`, `mono_stack`, `link` (acyclic) | done (`AbiLemmas.lean`) |
| A1: frames/calls/exits by hand (`spike/frames/`) | done: `g_spec`, `abort_spec` (abi), `f_spec` + three concrete instances (memframe, a0d1e6b) |
| x64 `Isel` (all integer ops of `LeanQbe.Ops`, including `div`/`rem`/`udiv`/`urem`) | done (`d135d79`, helper x64isel): `op_isSome`, `load_isSome`, `store_isSome`, 75 `parse(...) = ... := rfl` checks |
| x64 `Isel` fast paths (`fastOp`, `fastStore`, `fastIsa`, `fastTarget`) | done: immediate shifts (`shl`/`shr`/`sar $c`), 2-address `binRegIns`, direct `cmpRegIns`, direct `storeRegIns`, `eventually_fastOp`, `eventually_fastStore`, `fastOp_isSome`, `fastStore_isSome` |
| `Target.call_fnspec` (call + callee FnSpec, for R3) | done (`42d1ad3`, helper memframe) |
| Plan step 6: `bench/` harness + QBE pass ablation + fast-isel ablation | done (`bench/run.sh`, `bench/uf_bench.c`, `bench/lrat_bench.c`, `bench/DumpBench.lean`) |

## What exists

### `LeanQbe/Abi.lean` (generic, imports no architecture)

- `Isa`: executable data only, which is all `Rega.lower` needs. Registers (`DecidableEq`), directive
  type, `label`, register sets (`sp`, `scratch`, `allocatable`, `argRegs`, `retRegs`,
  `calleeSaved`), snippets `mov`, `movi`, `op : Op Reg → Reg → Option (List Directive)`,
  `load`, `store` (both `Option`, `none` = unsupported, the lowering fails), `jmp`, `jnz`, `ret`.
- `Target extends Isa`: machine data / addresses / states / hosts, `get`, `mem`, `step h`
  (runs are Kraken's `Eventually (step h)`), `prog h`, `addrOf h k`, `labelAddr h l`, the
  return-address convention (`raBytes`, `RetAddr`, `raReg`), `spEntry`, register-set disjointness
  facts, `labelAddr_eq` (first definition), and one continuation-form step lemma per snippet:
  `code.IsInfixAt (prog h) k → side conditions → (∀ s', relation s s' → run from k + code.length)
  → run from k`. Rules: flags dead between snippets; a snippet clobbers only its destination and
  scratch; encoding details stay inside the snippet.
- Generic definitions: `Run`, `Keeps`, `LabelsUnique`, `Defined`, `ArgsIn`/`RetsIn`
  (`(regs.take vs.length).map (get s) = vs`), `Entry sp ra n = region (sp - n) n ⋆ RetAddr sp ra`,
  `Exit sp n = region (sp - n) (n + raBytes)`, `Restored`, `FnSpec h sym spec n` (v0).
- `Arg.vars`, `Op.vars`.

### Version 1 additions (frames, calls, exits)

- `Isa`: `raRegs` (registers of the return-address convention: x64 none, AArch64 `x30`),
  `frameSize ns`, `prologue ns`, `epilogue ns`, `slotSt i r`, `slotLd rd i`, `call sym`,
  `tailJmp sym`.
- `Target`: `Saved sp ra ns` (arch frame overhead: what the return-address convention keeps, plus
  padding), `spOk` (AArch64: 16-aligned for sp-based accesses), facts (raRegs disjoint from every
  other register set, `8 ns ≤ frameSize ns`, `spOk_frame`, `spEntry_call`, `raReg_of_raRegs`),
  and a continuation-form spec for each new snippet. `call_spec` continues from `labelAddr h sym`
  with the return address in place, so the generic proof applies the callee's `FnSpec` there.
- `FnSpec h sym spec n nX`: the exit branch is a *call-ready* state for the exit symbol with at
  least `nX` bytes of stack (decision 1 below).
- Generic `word a v` (8 bytes holding `v`) and `slots a σ` (consecutive words) for spill slots;
  `region_word`, `slots_append`, `slots_get`, `slots_region`, `region_slots` in AbiLemmas.

### `LeanQbe/Amd64/` (x64 instance)

- `Isel.lean` + `IselLemmas.lean`: complete x64 instruction selection for every operation in
  `LeanQbe.Ops` (`copy`, `ext{s,u}{b,h,w,l}`, `add sub mul div rem udiv urem and or xor shl shr sar`,
  all 10 `CmpOp`s, and all `load`/`store` widths `b/h/w/l` × signedness × class, from register or
  immediate addresses), with 75 `parse(...) = ... := rfl` checks against Kraken's x64 parser and
  totality theorems `op_isSome`, `load_isSome`, `store_isSome`. Also provides verified fast-path
  instruction selection (`fastOp`, `fastStore`, `eventually_fastOp`, `eventually_fastStore`,
  `fastOp_isSome`, `fastStore_isSome`):
  - immediate shifts (`shiftImmIns`: `shl`/`shr`/`sar $c, %rd` in 1–2 instructions without touching `%rcx`);
  - two-address register operations (`binRegIns`: 1 instruction when `ra = rd` or `isComm o ∧ rb = rd`,
    2 instructions when `rb ≠ rd` or `ra = rd ∧ b = .imm cb`, instead of 4 through `%r11`/`%r10`);
  - direct comparisons (`cmpRegIns`: 3 instructions for register-register `cmp`, 4 for register-immediate,
    instead of 5);
  - direct register stores (`storeRegIns`: 1 instruction `mov{b,w,l,q} %rv, (%ra)` instead of 2).
- `Targ.lean`: register roles (scratch r10 r11; allocatable rax rcx rdx rsi rdi r8 r9; arguments
  rdi rsi rdx rcx r8 r9; results rax rdx; callee-saved rbx rbp r12–r15), control-flow and frame
  snippets (`push`, `pop`, `sub/add $c, %rsp`, rsp-relative load/store, `call`, `jmp`), `isa : Isa`,
  and `fastIsa : Isa` (`{ isa with op := fastOp, store := fastStore }`).
- `TargLemmas.lean`: step lemmas for control-flow and frame directives, `Amd64.target : Target`, and
  `Amd64.fastTarget : Target`.
- `FrameLemmas.lean` (memframe): step lemmas for the frame directives, in separation-logic form
  with `region` (owned, contents arbitrary) and `word a v` (8 bytes holding `v`).

### `LeanQbe/AbiLemmas.lean` (memframe)

`loadVal_frame`, `storeOk_frame`, `storeMem_frame` (an access to the source memory `m` inside
`M =⋆ Eq m ⋆ F` behaves the same on `M` and keeps the frame), `sep_mono(_r)`, `region_split`,
`region_zero`, `word`, `Target.entry_exit`, `Target.retAddr_of_entry'`, `Target.exit_of_entry`.
Together they give rega's `MemFacts T` for every `T`.

## A1: the contract checked on hand-written code (`spike/frames/`)

`Frames.lean` (abi) and `FramesProof.lean` (memframe). Every encoding is checked against Kraken's
parser by `rfl`.

- `g(a)`: leaf; `test %edi,%edi; jnz g.ok; jmp abort; g.ok: rax := rdi + rdi; ret`. Returns `a + a`
  or exits to `abort(a)`. `g_spec : nX ≤ n → FnSpec h "g" gSpec n nX`.
- `abort: ret`, an exit target in the host with its own `abort_spec`.
- `f(a, b)`: `push %rbx; sub $16,%rsp` (24-byte frame, ≡ 8 mod 16), `a` in callee-saved `rbx`
  across the call, `b` spilled to `(%rsp)`, `call g`, reload, two adds, then `ret` or its own
  `exit @abort(a)` (epilogue + `jmp abort`). `f_spec (hg : FnSpec h "g" gSpec n nX) (hX : nX ≤ 32 +
  n) : FnSpec h "f" fSpec (32 + n) nX`: the stack bound adds up (24 + 8 + n), g's exit propagates
  with f's frame folded into `F`.
- Non-vacuity on one concrete host (`fCode ++ gCode ++ abortCode`, LabelsUnique by `decide`), with
  in-host contracts linked rather than assumed and a concrete state built from real bytes:
  `f_returns` (rax = 5, rsp restored, the 48-byte footprint returned), `f_exits_in_g` (exit inside
  g, propagated), `f_exits_itself`; each exit state is fed to `abort_spec` with `nX = 8` bytes.

What the spike changed in the contract: the exit branch became a call-ready state (not "tail call
from our own entry"), gained `nX ≤ n'` (reviewer) and `n' + raBytes ≤ 2^64` (memframe: without
it the `nX` guarantee cannot be consumed on AArch64, where a region larger than memory is
satisfiable).

## Decisions settled by A1 (plan 2.4 open points)

1. **Exit = call-ready state.** At an `exit @sym(args)` the machine is in a state from which `sym`
   could be called: pc at `labelAddr sym`, `sym` defined in the host, arguments in the argument
   registers, an entry-aligned stack pointer, some return address `ra'` where the convention keeps
   it, at least `nX` bytes of stack below the stack pointer (`Entry sp' ra' n'` with `nX ≤ n'`),
   memory `Eq m' ⋆ Entry sp' ra' n' ⋆ F ⋆ R` with the caller's frame `R` untouched. So an exit
   target can itself be specified by an `FnSpec`. I first tried "tail call relative to the
   function's own entry" (same stack pointer, return address and callee-saved registers); it is
   not compositional, because an exit inside a callee happens in the caller's frame. `nX` is
   explicit (reviewer #60.1, #75.2): with `n' = 0` allowed, a real exit target such as C's `abort`
   could not be used. A function that exits itself needs `nX ≤ n`.
2. **Alignment at calls.** `spEntry` is a precondition of `FnSpec` and is established at every
   call. On x64 the frame size, pushes included, is ≡ 8 mod 16.
3. **Stack bounds add up.** A function with a frame of `F` bytes calling functions with bounds
   `n_i` has bound `F + raBytes + max n_i` (x64: the 8 bytes `call` pushes). `f_spec` is stated
   generic in `g`'s bound `n` and concludes `32 + n` for `f`'s 24-byte frame.
4. **Results.** Version 1 keeps the C ABI's two result registers on x64 (rax, rdx) and the lowering
   rejects more results. More result registers for internal calls (rcx, rsi, …) are a cheap later
   extension; external C callees never return more than two.
5. **Arity.** `ArgsIn` with more values than argument registers is false, so `FnSpec` says nothing
   about such calls (reviewer #22.2). The lowering must reject more than six parameters;
   `lower_correct` should state that it does.
6. **Non-register state.** Kraken's x64 `MachineData` has GPRs, zmm registers, flags and memory; all
   zmm registers are caller-saved in SysV and DF/MXCSR/x87 are not modelled. Kraken's AArch64
   `MachineData` has no SIMD registers. So `Restored` over GPRs is complete for both models today
   (reviewer #22.3). If Kraken adds callee-saved state (AArch64 d8–d15), `Restored` needs a field.

## Open

- Reviewer #22.1 (exit symbols identified by address) is resolved (reviewer #60.2): `Defined h
  sym'` excludes undefined symbols (which resolve to -1), and two defined labels at one address
  denote the same code.
- Known gap (reviewer #22.3, #75.4, coordinator #119.1): `Restored` covers general-purpose registers
  only. Checked both `Kraken/X64/Semantics.lean` and `Kraken/AArch64/Semantics.lean`: x64's
  `MachineData` has only `regs`, caller-saved `zmms` (`zmm0`–`zmm31`), `status` (`cf,pf,af,zf,sf,of`),
  and `dmem` (no `DF`, `MXCSR`, or `x87` control word); AArch64's `MachineData` has only `regs`
  (`X0`–`X30`, `SP`), `status` (`n,z,c,v`), and `dmem` (no SIMD/FP `d8`–`d15`). A `Frozen : MData →
  MData → Prop` field on `Target` would therefore instantiate to `fun _ _ => True` on both
  `Amd64.target` and `Arm64.target` today while touching ~40 places across 6 workers' files, so we
  skip it per #119.1.
- Calls happen only at `sp = sp0 - frameSize ns`: nothing may push between prologue and call.

## Plan step 6: Benchmarks and QBE pass ablation (`bench/`)

`bench/run.sh` builds an instrumented copy of stock QBE in `/tmp` (with runtime environment switches
to disable one optimization pass at a time), dumps our PHOAS programs (`UnionFind` and all 5
functions of `LratTrim.lratTrimFns`) to QBE IL (`uf.ssa`, `lrat_trim.ssa`) and x64 assembly
(`uf_leaf.s`), links against C drivers (`bench/uf_bench.c`, `bench/lrat_bench.c`), verifies
identical output hashes across all compilers, and reports the median of 5 runs:

- **Union-Find (`uf_bench.c`)**: $N = 65536$ elements, 40 rounds; each round performs $N/2$ random
  unions (`uf_union` calling `find`, or `unionInline` with `find` inlined twice) followed by $2N$
  random `find` queries with path halving.
- **LRAT-trim (`lrat_bench.c`)**: synthetic 2000-variable, 4009-clause unsatisfiable formula + LRAT
  proof valid simultaneously for `br_trim_proof` (with unused CNF and proof clauses),
  `br_check_proof` in RUP mode (`strict = 0`), and `br_check_proof` in strict backward resolution
  mode (`strict = 1`), run for 150 rounds (`LRAT (full)` = `trim_proof + check_proof(rup) +
  check_proof(strict)`; `LRAT (rup)` = `br_check_clause_non_strictly_by_propagation` alone).

| Compiler / Variant | UF (call) ms | UF (inline) ms | UF insns | LRAT (full) ms | LRAT (rup) ms | LRAT insns | Hash check |
|---|---:|---:|---:|---:|---:|---:|---|
| `gcc -O2` (C) | 68.19 | 66.36 | — | 18.72 | 7.69 | — | `0xd88e09b152cc8e5a` / `0x0000092c781efeb6` |
| `clang -O2` (C) | 68.35 | 67.64 | — | 20.64 | 9.08 | — | `0xd88e09b152cc8e5a` / `0x0000092c781efeb6` |
| **stock QBE (all passes)** | **79.60** | **76.65** | **77** | **31.22** | **13.23** | **644** | `0xd88e09b152cc8e5a` / `0x0000092c781efeb6` |
| QBE `-isel-addr` (no addressing modes) | 82.03 | 79.89 | 91 (+18%) | 35.10 (+12.4%) | 14.50 (+9.6%) | 736 (+14%) | match |
| QBE `-copy` (no copy/phi propagation) | 78.61 | 76.73 | 82 (+6%) | 34.76 (+11.3%) | 14.64 (+10.7%) | 773 (+20%) | match |
| QBE `-rega-coalesce` (no reg hints) | 79.35 | 77.21 | 87 (+13%) | 33.01 (+5.7%) | 13.40 (+1.3%) | 677 (+5%) | match |
| QBE `-fold` (no constant folding) | 79.53 | 76.68 | 77 (0%) | 31.30 (+0.3%) | 13.23 (0%) | 644 (0%) | match |
| QBE `-simpl` (no pow2 div/rem simpl) | 79.78 | 76.64 | 77 (0%) | 31.36 (+0.4%) | 13.16 (-0.5%) | 644 (0%) | match |
| QBE `-gvn/gcm` (no CSE / GCM sinking) | 80.66 | 79.35 | 83 (+8%) | 29.26 (-6.3%) | 12.39 (-6.3%) | 646 (+0.3%) | match |
| QBE `-all-opt` (all 6 disabled) | 81.95 | 80.41 | 95 (+23%) | 42.60 (+36.5%) | 19.84 (+50.0%) | 806 (+25%) | match |
| `lean-qbe (x64, simple isel)` (`Amd64.isa`) | 88.66 | 84.51 | 156 | 73.20 | 32.74 | 1375 | `0xd88e09b152cc8e5a` / `0x0000092c781efeb6` |
| **`lean-qbe (x64, fast isel)` (`Amd64.fastIsa`)** | **83.66** | **80.67** | **90 (-42%)** | **60.49 (-17.4%)** | **27.31 (-16.6%)** | **1058 (-23%)** | `0xd88e09b152cc8e5a` / `0x0000092c781efeb6` |

### Ranking of passes and takeaways for `lean-qbe`

1. **Instruction selection (`isel` addressing modes and direct operand use) ranks #1**:
   - In stock QBE, disabling addressing modes (`-isel-addr`) adds +12.4% runtime and +92
     instructions on LRAT.
   - In `lean-qbe`, replacing the scratch-bouncing snippets (`Amd64.isa`) with the verified fast
     paths (`Amd64.fastIsa`: immediate shifts `shlq $c`, 2-address `binRegIns`, direct `cmpRegIns`,
     and direct `storeRegIns`) cuts Union-Find (`find + union + unionInline`) from **156 to 90
     instructions (-42%)** (fewer than QBE `-all-opt`'s 95 instructions, and within 3 instructions of
     QBE `-rega-coalesce`'s 87!) and `find + unionInline` from **122 to 67 instructions (-45%)**,
     bringing `UF (inline)` to **80.67 ms** (within **5.2%** of stock QBE's 76.65 ms, and matching
     QBE `-all-opt`'s 80.41 ms) and `UF (call)` to **83.66 ms** (within **5.1%** of stock QBE's
     79.60 ms).
   - On the full 5-function LRAT-trim kernel (`br_check_clause_non_strictly_by_propagation`,
     `br_check_clause_strictly_by_resolution`, `br_check_clause`, `br_check_proof`, `br_trim_proof`),
     `Amd64.fastIsa` cuts the emitted x64 assembly from **1375 to 1058 instructions (-23%, -317
     instructions)**, reducing `LRAT (full)` runtime from **73.20 ms to 60.49 ms (-17.4%)** and
     `LRAT (rup)` from **32.74 ms to 27.31 ms (-16.6%)**. The remaining gap on LRAT between
     `lean-qbe (x64, fast isel)` (1058 insns) and QBE `-all-opt` (806 insns) comes from our
     untrusted allocator (`Spill.lean`) keeping only the 7 caller-saved registers in `allocatable`
     (whereas stock QBE also allocates the 5 callee-saved registers `rbx, r12–r15` across loops).
2. **Copy propagation (`copy`) ranks #2** (+11.3% runtime and +129 instructions on LRAT when
   disabled in QBE), mostly by eliminating the copies introduced around join-point parameters.
   `LeanQbe/Fold.lean` already implements `copy.l` propagation inside lexical scope.
3. **Register-allocator coalescing (`rega` hints) ranks #3** (+5.7% runtime and +33 instructions on
   LRAT). In our architecture this lives entirely in the untrusted oracle (`Spill.lean`), requiring
   zero proof work.
4. **Constant folding (`fold`) and `simpl` have ~0% effect** on hand-written / macro-expanded IL
   that does not contain constant-on-constant arithmetic or unsigned division by powers of two.
5. **GVN + GCM (`-gvn/gcm`) helps slightly on Union-Find** (-3.4% runtime, -6 instructions) **but
   slightly hurts on LRAT** (+6.3% runtime when enabled, because GCM's aggressive instruction
   sinking moves address computations across loop back-edges). This confirms plan section 6's
   expectation: `Gcm` is low priority and should not be ported before `Isel` and oracle coalescing.

## Measurements

- `lake build LeanQbe.Amd64.TargLemmas`: about 3.5 s. `Abi.lean` 0.6 s.
- `Amd64/{Targ,TargLemmas,Isel,IselLemmas,FrameLemmas}.lean`: 105 + 434 + 326 + 1784 + 219 lines.
