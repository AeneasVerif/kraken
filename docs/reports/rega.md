# rega: verified lowering, pipeline, litmus tests

Owner: `rega`. Files: `LeanQbe/{Rega,RegaLemmas,Main}.lean`, `Main.lean` (CLI), `LeanQbe/Examples/Litmus*.lean`,
`test/`, later `LeanQbe/{Live,Spill,Cfg}.lean` and `spike/e3/`.

## Status

| Milestone | State |
|---|---|
| Proof skeleton against a mock target (E1) | done, scratch only (not in the repo), no sorry |
| R1: `lower` for param/let/store/ret, generic proof, x64 tracer | done: no hypotheses left (`memFacts` from AbiLemmas), generic-host Kraken-only theorem plus non-vacuity |
| R1 extras | `lower` already covers load, jnz, jump, join-point groups (R2's E1 half) |
| R2, E1 half: control-flow litmus, oracle, pipeline | done: five programs checked by kernel `rfl`, with FnSpec instances and native runs; `sumto` end to end with a loop proof |
| R2, E3 half: the same skeleton in E3, the D8 comparison | done (spike/e3/, written by helper `e3`; see below) |
| R3: calls, exits, spills, oracle | not started |

## What exists

### `LeanQbe/Rega.lean` (executable, imports no lemmas)

`lower (h : Hints I) (fn : String) : Expr Nat Nat → St I → Except String (List I.Directive × Nat × Nat)`,
a single structural recursion. Its state:

- `nv`, `nl`: the next fresh name and label. They are threaded through the recursion, so names and
  labels are unique within a function and the oracle can key its hints by them.
- `R : List (Arg Nat × Reg)`: the symbolic register file. `(.var x, r)` means that `r` holds name `x`;
  `(.imm c, r)` means that `r` holds `c`. It is a relation rather than a map (`Name → Option Loc` in
  the plan): a value can sit in several registers, which `jump l(x, x)` needs, and constants can be
  tracked, which `ret 0` and immediate jump arguments need.
- `PL`: the registers of the parameters still to be bound (the argument registers at function entry,
  the entry map's `ploc` at a block).
- `pend`: the labels declared and not yet defined. It mirrors `wp`'s `acc` exactly, and `let`, `param`
  and the other constructors reset it to `[]` just as `wp` does.

Hints: `dest : Nat → Option Reg` (a register per name) and `entry : Nat → Entry` (per label:
`live : List (Arg Nat × Reg)` and `ploc : List Reg`). Moves at `jump`/`ret` come from an untrusted
parallel-move pass (`pmove`), are executed symbolically (`execMoves`, whose destinations must be
allocatable) and are then checked against the targets. There are dynamic checks: operands must not
be in scratch registers, entry-map registers must not be scratch, a destination must be
allocatable, and arities must match.

Layout: `rest ++ [label ℓ] ++ body` for a block; `jnz c ℓ ++ else ++ [label ℓ] ++ then` for a
conditional; `jnz` on an immediate lowers only the taken branch. `call` and `exit` return an error
until step 3.

### `LeanQbe/RegaLemmas.lean`

- `lower_correct`: one induction on `Wf G D e₁ e₂`, about 250 lines. Its invariants:
  `Agree G R s` (every entry holds its name's value or its constant), `Inv F s₀ m s`
  (`mem s =⋆ Eq m ⋆ F` and the registers that are neither allocatable nor scratch are unchanged
  since entry), and `ValsIn PL args`.
  The join point for label `ℓ` is
  `LabJ G ℓ as m := ∃ k, prog[k] = label ℓ ∧ ∀ s, Agree G (entry ℓ).live s → ValsIn (entry ℓ).ploc as s → Inv F s₀ m s → Run h k s post`.
  `label` instantiates the source's `∀ J` with it, `block` proves it closed at its own index
  `k + |rest|`, and `jump` uses it after the checked moves. `DOk G D` says that every `(J, ℓ) ∈ D`
  is a `LabJ G' ℓ` for some `G' ⊆ G`. The main lemma takes the `ret` step and the memory facts as
  hypotheses (`Hyps`), so the induction never mentions frames or the return address.
- `lowerFn_correct`: `lowerFn hints f = .ok code` placed in host `h`, `LabelsUnique h`,
  `Func.Wf f.body`, `n + raBytes ≤ 2^64` and `MemFacts T` give
  `T.FnSpec h f.name (Func.spec Γ f.body) n`. It proves `ret` from `ret_spec`, which needs
  the RetAddr rearrangement, `Restored`, `RetsIn` and the Entry-to-Exit step.

The plan's paper argument held. There is no three-way `Wf`, no liveness, no dominance, and no
machine-level loop induction. The direct lowering (D9) works so far, and the `toFlat` fallback is
not needed.

### `LeanQbe/Examples/Litmus.lean` (x64)

- `tracer` (`x = add a b; storel x, p; ret x`) and its hints (`x ↦ rax`).
- `tracer_lower : lowerFn tracerHints tracer = .ok tracerCode` by `rfl`. `tracerCode` is written as
  AT&T text and parsed by Kraken's `parse(...)`, so the check compares the compiler's output with
  assembly as the parser reads it.
- `host`: `Host.ofLayout tracerCode` with labels of size 0 and instructions of size 4. Label
  uniqueness is decided.
- `tracer_correct`: a statement about Kraken only (`step1 Host.exe`, `regs.get64`, `dmem`,
  `Mem.loadInt/storeInt`, `⋆`), for every `[Host]` that contains `tracerCode` at some `k₀` and
  satisfies `Host.LabelsUnique` (generic in the layout, D2). The concrete `host` is one instance.
- `tracer_nonvacuous`: a concrete state (`rsp = 0x7008`, `p = 0x7010`, return address
  `0x1234`, `R = emp`) that meets every premise; the run ends at `0x1234` with `rax = 42`.

### Oracle: `LeanQbe/Live.lean`, `LeanQbe/Spill.lean` (untrusted, no lemmas)

- `Live.toTree` replays `lower`'s traversal to get a first-order tree with the same name and label
  numbering. `liveLabels` computes the live-in set of each join point by fixpoint iteration over the
  jumps; `liveIn` gives the live set of each subterm.
- `Spill.hints I f`: first fit. Each name gets one register for its whole life, chosen at its
  definition and avoiding the registers of values live there. Block parameters avoid the live-in
  registers of their label. Entry maps are the live-in sets with the chosen registers. There is no
  spilling yet: running out of registers is a compile error.
- `Rega.pmove` (also untrusted): register moves first, in an order that never overwrites the last
  copy of a needed value; a cycle is broken through a free scratch register (`execMoves` accepts
  scratch destinations); constants are loaded last.

### Pipeline: `LeanQbe/Main.lean`, `LeanQbe/MainLemmas.lean`

`compileFn I f := lowerFn (Spill.hints I f.opt) f.opt`, where `Func.opt` is core's verified mid-end
(fold, CSE, fold). `compileFn_correct` gives `T.FnSpec h f.name (Func.spec Γ f.body) n nX` for the
*source* function, via `Func.opt_wf`, `Func.opt_spec` and `FnSpec.of_spec`.

### Control-flow litmus: `LeanQbe/Examples/LitmusCf.lean`, `LitmusCfLemmas.lean`

`ifelse`, `sumto` (counting loop), `evenodd` (two mutually recursive join points), `nested` (two
nested loops; `m` and `k` stay live across both, `i` across the inner one), `swap` (the loop swaps
its parameters, which forces a move cycle through `r10`). For each program:
- `…_lower : lowerFn (Spill.hints Amd64.isa f) f = .ok fCode` by `rfl` (the kernel runs the oracle
  and `lower`), where `fCode` is assembly text parsed by Kraken's `parse(...)`;
- `…_compile : compileFn Amd64.isa f = .ok fCode` by `kernel_rfl` (the elaborator's `rfl` gives
  up on the mid-end's table lookups; the kernel does not);
- `…_wf` by `wf_tac`, and `…_fnspec` (`lowerFn_correct` in every x64 host that contains the code).

`sumto_spec` is the source contract (`rax = 1 + … + n` for `n < 2^32`), proved by induction over the
loop counter. `sumto_correct` is a Kraken-only theorem about the binary the pipeline emits, for every
host that contains it.

### CLI and tests

`lake build leanqbe; .lake/build/bin/leanqbe <name>` prints GNU as input, compiled by `compileFn`.
`test/run.sh` builds the CLI, then for each `test/<name>_main.c` emits, assembles, links and runs.
All six programs (tracer plus the five control-flow programs) pass against C reference
implementations, including edge vectors (`0x100000000` for jnz's 32-bit test, overflow).

## D8 and D9 evidence (R2)

**D9 (direct lowering from PHOAS) holds.** The proof closed in E1, against the real IL and Target,
for straight-line code, branches, loops, irreducible groups and nested loops. It needs a two-way
`Wf`, no liveness argument and no machine-level loop induction. The `toFlat` fallback is not needed.

**D8 (E1 against E3)** compares the same lowering proof against the same mock target (spike/e3/,
full table in spike/e3/README.md):

| | E1 | E3 |
|---|---|---|
| main lemma | 215 lines, one `induction hwf` | 214 + 16 lines, three mutual lemmas, no hand-written induction principle needed |
| junk cases | 3 constructs (`args = []` in 7 cases, block without a pending label, the `acc`/`pend` invariant everywhere), about 14 lines | none |
| `Wf` | 19 lines | 36 lines |
| elaboration / kernel of the main lemma | 1.04 s / 28 ms | 1.28 s / about 61 ms |
| even/odd `lower … = .ok` by `rfl` | works (62 ms; kernel only 24 ms) | works (65 ms; kernel only 25 ms) |

Both encodings work and cost about the same; E3's advantage is that ill-formed terms cannot be
written, so the junk lines disappear. My recommendation: keep E1 for the lowering. Everything else
is built on it (core's Fold/Gvn, logic's notation and proofs, Print), the junk cost is small and
local, and switching would mean redoing those passes for no gain in the lowering.

## Measured

- Module-system pitfall: `toString (n : Nat)` and `Nat.toDigits` do not reduce by `rfl` inside a
  `module` file, although a non-module scratch check passes. `lname` uses its own `natDigits`.

- `lake build LeanQbe.RegaLemmas`: about 2 s. `LeanQbe.Examples.Litmus` with `rfl`: about 1.4 s.
- The mock skeleton (E1 IR plus mock target, everything in one file) checks in under 2 s.

## Open

- The E3 comparison (helper `e3`), then the R2 milestone post.
- R3 (after gate G1): calls, exits and spills on Target v1 (`slots`, `prologue`, `call`,
  `tailJmp`), the stock-QBE comparison on the printed IL, and the four-way check per litmus test.
