# rega: verified lowering, pipeline, litmus tests

Owner: `rega`. Files: `LeanQbe/{Rega,RegaLemmas,Main}.lean`, `Main.lean` (CLI), `LeanQbe/Examples/Litmus*.lean`,
`test/`, later `LeanQbe/{Live,Spill,Cfg}.lean` and `spike/e3/`.

## Status

| Milestone | State |
|---|---|
| Proof skeleton against a mock target (E1) | done, scratch only (not in the repo), no sorry |
| R1: `lower` for param/let/store/ret, generic proof, x64 tracer | done: no hypotheses left (`memFacts` from AbiLemmas), generic-host Kraken-only theorem plus non-vacuity |
| R1 extras | `lower` already covers load, jnz, jump, join-point groups (R2's E1 half) |
| R2: litmus programs for control flow, the E3 comparison | next |
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

### CLI and tests

`lake build leanqbe; .lake/build/bin/leanqbe tracer` prints GNU as input. `test/run.sh` builds the
CLI, then for each `test/<name>_main.c` emits, assembles, links and runs. The tracer passes on 5
vectors, including overflow.

## Measured

- `lake build LeanQbe.RegaLemmas`: about 2 s. `LeanQbe.Examples.Litmus` with `rfl`: about 1.4 s.
- The mock skeleton (E1 IR plus mock target, everything in one file) checks in under 2 s.

## Open

- R2: litmus programs for if/else, a counting loop, even/odd and nested loops, then the E3 skeleton
  and the comparison.
