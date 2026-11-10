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
| A1: frames/calls/exits by hand (`spike/frames/`) | `FnSpec1` candidate stated; `g_spec` proved; `f_spec` + non-vacuity in progress (memframe) |
| `FnSpec` v1 in `Abi.lean`, prologue/epilogue/slot/call/exit snippets | design below, not yet in `Abi.lean` |

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

### `LeanQbe/Amd64/` (x64 instance)

- `Targ.lean`: register roles (scratch r10 r11; allocatable rax rcx rdx rsi rdi r8 r9; arguments
  rdi rsi rdx rcx r8 r9; results rax rdx; callee-saved rbx rbp r12–r15) and snippets. Supported:
  `copy`, `add sub and or xor` at both classes with register or immediate operands (both operands
  go through r11/r10, so any destination works), `loadl` at class l from a register address,
  `storel` of a register or immediate to a register address, `jnz` as `testl r32, r32; jnz`.
  Frame directives for step 2b: `push`, `pop`, `sub/add $c, %rsp`, rsp-relative load/store,
  `call`, `jmp`.
- `TargLemmas.lean`: every encoding is checked equal to Kraken's parser output by `rfl`; one step
  lemma per directive and per snippet; `Amd64.target : Target` (reducible), which unfolds to
  `step1 Host.exe`, `regs.get64`, `dmem`, `Labels.label`, RA bytes at rsp, `spEntry sp :=
  (sp + 8) % 16 = 0`, `raReg := True` (reviewer #35 checked this).
- `FrameLemmas.lean` (memframe): step lemmas for the frame directives, in separation-logic form
  with `region` (owned, contents arbitrary) and `word a v` (8 bytes holding `v`).

### `LeanQbe/AbiLemmas.lean` (memframe)

`loadVal_frame`, `storeOk_frame`, `storeMem_frame` (an access to the source memory `m` inside
`M =⋆ Eq m ⋆ F` behaves the same on `M` and keeps the frame), `sep_mono(_r)`, `region_split`,
`region_zero`, `word`, `Target.entry_exit`, `Target.retAddr_of_entry'`, `Target.exit_of_entry`.
Together they give rega's `MemFacts T` for every `T`.

## Decisions settled by A1 (plan 2.4 open points)

1. **Exit = tail call.** At an `exit @sym(args)` the machine is in a state from which `sym` could be
   called with the same return address, stack budget and frame: pc at `labelAddr sym`, `sym`
   defined in the host, arguments in the argument registers, stack pointer and callee-saved
   registers as on entry, the return address still in place, memory `Eq m' ⋆ Entry sp ra n ⋆ R`.
   So an exit target can itself be specified by an `FnSpec`, and alignment at the exit is the
   entry alignment. (`Target.TailCall`, `Target.FnSpec1` in `spike/frames/Frames.lean`.)
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

- Reviewer #22.1 (exit symbols identified by address): `Defined h sym'` excludes undefined
  symbols (which resolve to -1). Two defined labels with no instruction between them still share
  an address. With exits as tail calls, reaching that address *is* running `sym'`'s code, so the
  machine-level claim is honest; a final theorem that must tell exit targets apart needs a
  decidable host hypothesis "these symbols have pairwise distinct addresses". To add with v1.
- `FnSpec` v1 into `Abi.lean` (replacing v0's exit branch) once `f_spec` closes; coordinate with
  rega (`lowerFn_correct` proves v0 today, its exit branch is not produced yet).
- Snippets for v1: prologue/epilogue, slot load/store, call, exit; see the design section once
  written.
- More x64 operations (cmp, ext, mul, shifts, other load/store widths) when rega needs them.

## Measurements

- `lake build LeanQbe.Amd64.TargLemmas`: about 1.1 s. `Abi.lean` 0.6 s.
- `TargLemmas.lean` 430 lines, of which the `Target` instance is about 70.
