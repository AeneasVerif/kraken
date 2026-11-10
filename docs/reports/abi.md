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
| x64 `Isel` (all integer ops Kraken x64 supports) | in progress (helper x64isel) |
| `Target.call_fnspec` (call + callee FnSpec, for R3) | in progress (memframe) |

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
- Known gap (reviewer #22.3, #75.4): `Restored` covers general-purpose registers only. Today that
  is complete for Kraken's models (see decision 6), but AArch64 d8–d15 or x64 DF/MXCSR would need
  a field if Kraken models them.
- Calls happen only at `sp = sp0 - frameSize ns`: nothing may push between prologue and call.
- More x64 operations (cmp, ext, mul, shifts, other load/store widths) when rega needs them.

## Measurements

- `lake build LeanQbe.Amd64.TargLemmas`: about 1.1 s. `Abi.lean` 0.6 s.
- `TargLemmas.lean` 430 lines, of which the `Target` instance is about 70.
