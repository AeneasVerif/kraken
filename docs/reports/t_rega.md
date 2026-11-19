# `T7` Report: PHOAS-First Checked Register Allocation (`Rega`) and Its Correctness Proof

Branch `swarm-t7-rega-12d22ef4` (forked from `main = 384800c`). Zero edits to `Target.lean`,
`LeanQbe.lean`, `scripts/*`, `kraken/*`, or any E1 `LeanQbe/*.lean` file.

## 1. Architecture

* **`Rega.lowerFn`** (`LeanQbe/T/Rega.lean`) lowers PHOAS `Expr VNat LNat` / `Blocks` directly
  (no `TFlat`, no `denote`), consuming untrusted literal `Hints` (`LeanQbe.T.Trie`). Every hint is
  checked: symbolic register state `regs : List (SymArg × RegLoc)`, multi-granule slot state
  `Trie SlotEntry` (`L10`), lexical `defs : Trie DefFact` (`L9`) and `vecWidths`, read-only flag
  cache with `setcc` as the only flag move (`L3`–`L6`), `PreStep.clearFlags` (`L7`), `canonAbi` at
  `call`/`ret`/`exit`, `entryScopeOk nv` at block entry (Trap 3), pure-`Bool` comparisons only
  (Trap 2), monotone label counter `nl` (Trap 5). `jnz` threads zero-move jumps (`jnzSetup`,
  `zeroMoveJump?`) and may invert the condition.
* **`Spill.hints`** (`Spill.lean`, untrusted): E1-parity per-bank (GPR + Vec) priority graph colouring,
  cross-call spilling with callee-saved promotion, ABI/affinity preferences, pressure budgets,
  `10 * mult` loop weights, local flag/carry probing, GPR/Vec parallel-move cycle breaking.
  **Known heuristic gap:** it never emits `.adcx/.adox/.decInc/.disp` variants and never homes a
  non-adjacent carry or a block parameter in a flag; the `G12d` `adcxAdox` and `cfLoop` litmus
  programs therefore patch those hints (`patchHints`) on top of `Spill.hints`. `Rega` accepted
  every program without workarounds (soundness never depends on the oracle).
* **`Live.lean`** mirrors the `(nv, nl, ip)` numbering in a first-order `Tree` and computes liveness,
  reusing `Arg.vars`/`tupVars`/`Op.vars`.

## 2. Proof structure (`T7b`)

| File | LOC | Contents |
|---|---:|---|
| `RegaLemmas1.lean` | 1,200 | `GprSym`/`VecSym`/`FlagSym` (∀-quantified over context entries, so out-of-scope ids are vacuous), `Agree`, frame `Inv`, `execMoves_ok`, `stepPre_ok`, `holdsLoc_ok`, `shuffle_ok`, block-entry/parameter/ABI binding |
| `RegaLemmas2.lean` | 867 | `FnPost` (= `Target.FnSpec`'s postcondition), `Hyps`, `ret_ok`, `exit_ok`, `call_ok`, `fn_entry_ok` (prologue/`saveCs`/`restoreCs`/`canonAbi`/epilogue) |
| `RegaLemmas3.lean` | 1,192 | operands (`tryArg`/`pickPArgs`/`tryAddr`), `lowerOp_ok`/`lowerLoad_ok`/`lowerStore_ok`, structural `LabelClean`/`lowerFn_labelsUnique`/`lowerFn_label_mem`, `lowerExpr_nv_le` |
| `RegaLemmas4.lean` | 876 | `LabJ`/`DOk`/`FT`, `lowerBlocks_closed`, **`lowerExpr_correct`** by `Wf.induct` (all 10 forms), **`lowerFn_correct`** |
| `RegaLemmas.lean` | 14 | thin facade |
| **Total** | **4,149** | (cap 3,300: **1.26×**, below the 1.5× warning line; every file ≤ 1,200) |

Headline: `Rega.lowerFn_correct : f.Wf → lowerFn T.toIsa hints E f = .ok code →
code.IsInfixAt (T.mach.prog host) k₀ → T.LabelsUnique host → frame ≤ n → n + raBytes ≤ 2^64 →
(callee FnSpecs + stack bounds) → (exits Defined) → T.FnSpec host f.name (Func.spec Γ f.body) n nX`.
`raReg_of_raRegs` suffices (no `raReg_congr`). Join points use the `LabJ` pattern (no `pend_mem`).

## 3. Gates

* **`G12c`** (kernel `t_kernel_rfl` on the mock ISA, `RegaScaleTest.lean`): `sl250` 0.7 s,
  `sl1000` 2.9 s, `sl2000` 5.9 s (2.0×; reviewer re-run 1.88×), `bl50` 0.7 s, `bl250` 3.6 s,
  `bl250_cross` 3.8 s, `spill20` 0.2 s (`nslots > 0 ∧ saved ≠ []`). `pmoveAux`/`shuffle` run in the
  kernel; `findSlotFor`/`slotBusy` are linear in `nslots` (re-measure with large spill sets and the
  real Amd64 ISA at `T8`).
* **`G12a`/`G12d`** (`RegaLitmusTarget/Progs/Test.lean`): concrete toy-x64 `litmusTarget` with all
  `GprTarget`/`FrameTarget`/`VecTarget` fields proved; 13 programs (`branches`, `loop`, irreducible
  `evenOdd`, `nested`, `(i64,bool)` `pairLoop`, `vec 2 i32` `vecLoop` with `vmovi`, `inc`+`carryCall`,
  `bits8`; `cmpJcc`, `adcChain`, `adcxAdox`, loop-carried-CF `cfLoop` with `dec`/`jnz`+`lea`), each
  with `Fn.Wf`, kernel-checked lowering, emitted-code pins, end-to-end `*_correct : FnSpec` via
  `lowerFn_correct`, and concrete-host `*_nonvacuous` executions (e.g. `cfLoop 3 2^63 = (2^63+25, false)`).
* **Axioms:** every headline theorem is `[propext, Classical.choice, Quot.sound]`; 0 `sorry`,
  0 `bv_decide`/`native_decide`/`ofReduceBool`.

## 4. Follow-ups

1. `Spill` variant/flag-home heuristics (see §1) — needed for `G12d` without hint patches.
2. Reviewer notes from `#212`: module-level label distinctness (`f.L1` vs `f` + `.L1`), linear slot
   scans in `shuffle`, `Live` → `Rega` import direction.
3. Audit `#003-A1`: drop dead `DefFact.{addVar64, copy}` (kept for now to avoid churn).
4. On rebase onto `main` (`72eb727`): take main's `TargetLemmas.lean` (adds `@[simp]` incl.
   `SlotWidth.bits_eq_64_mul_slots`, which may perturb some `simp` calls), switch `listTyEq` to
   `Ty.listBeq`.
