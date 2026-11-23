> **[Historical design note]** Written during an earlier milestone (at commit `384800c`); `Spill.lean` has since added flag-web/variant allocation and `Rega.lean` has gained additional verified lowering rules. See `LeanQbe-README.md` for current paths and capabilities.

# PHOAS-First Checked Register Allocation (`Rega`) and Its Correctness Proof

Snapshot from commit `384800c`, covering `LeanQbe/T/Rega.lean`, `RegaLemmas1..4.lean`, `Live.lean`, `Spill.lean`, and the register-allocator litmus/scaling tests.

## 1. Architecture

* **`Rega.lowerFn`** (`LeanQbe/T/Rega.lean`) lowers PHOAS `Expr VNat LNat` / `Blocks` directly
  (no `TFlat`, no `denote`), consuming untrusted literal `Hints` (`LeanQbe.T.Trie`). Every hint is
  checked: symbolic register state `regs : List (SymArg × RegLoc)`, multi-granule slot state
  `Trie SlotEntry`, lexical `defs : Trie DefFact` and `vecWidths`, read-only flag cache with
  `setcc` as the only flag move, `PreStep.clearFlags`, `canonAbi` at `call`/`ret`/`exit`,
  `entryScopeOk nv` at block entry, pure-`Bool` comparisons only, and monotone label counter `nl`.
  `jnz` threads zero-move jumps (`jnzSetup`, `zeroMoveJump?`) and may invert the condition.
* **`Spill.hints`** (`Spill.lean`, untrusted): per-bank (GPR + Vec) priority graph coloring,
  cross-call spilling with callee-saved promotion, ABI/affinity preferences, pressure budgets,
  `10 * mult` loop weights, local flag/carry probing, and GPR/Vec parallel-move cycle breaking.
  **Historical heuristic gap (later resolved in `docs/reports/spill_flags.md`):** at this snapshot,
  `Spill.hints` did not emit `.adcx/.adox/.decInc/.disp` variants or home non-adjacent carries or
  block parameters in flags; the `adcxAdox` and `cfLoop` litmus programs therefore used
  `patchHints`. `Rega` accepted every program without workarounds (soundness never depends on the
  oracle).
* **`Live.lean`** mirrors the `(nv, nl, ip)` numbering in a first-order `Tree` and computes liveness,
  reusing `Arg.vars`/`tupVars`/`Op.vars`.

## 2. Proof Structure

| File | LOC | Contents |
|---|---:|---|
| `RegaLemmas1.lean` | 1,200 | `GprSym`/`VecSym`/`FlagSym` (∀-quantified over context entries, so out-of-scope ids are vacuous), `Agree`, frame `Inv`, `execMoves_ok`, `stepPre_ok`, `holdsLoc_ok`, `shuffle_ok`, block-entry/parameter/ABI binding |
| `RegaLemmas2.lean` | 867 | `FnPost` (= `Target.FnSpec`'s postcondition), `Hyps`, `ret_ok`, `exit_ok`, `call_ok`, `fn_entry_ok` (prologue/`saveCs`/`restoreCs`/`canonAbi`/epilogue) |
| `RegaLemmas3.lean` | 1,192 | operands (`tryArg`/`pickPArgs`/`tryAddr`), `lowerOp_ok`/`lowerLoad_ok`/`lowerStore_ok`, structural `LabelClean`/`lowerFn_labelsUnique`/`lowerFn_label_mem`, `lowerExpr_nv_le` |
| `RegaLemmas4.lean` | 876 | `LabJ`/`DOk`/`FT`, `lowerBlocks_closed`, **`lowerExpr_correct`** by `Wf.induct` (all 10 forms), **`lowerFn_correct`** |
| `RegaLemmas.lean` | 14 | thin facade |
| **Total** | **4,149** | every proof file ≤ 1,200 LOC at this snapshot |

Headline: `Rega.lowerFn_correct : f.Wf → lowerFn T.toIsa hints E f = .ok code →
code.IsInfixAt (T.mach.prog host) k₀ → T.LabelsUnique host → frame ≤ n → n + raBytes ≤ 2^64 →
(callee FnSpecs + stack bounds) → (exits Defined) → T.FnSpec host f.name (Func.spec Γ f.body) n nX`.
`raReg_of_raRegs` suffices (no `raReg_congr`). Join points use the `LabJ` pattern (no `pend_mem`).

## 3. Scaling and Litmus Checks

* **Kernel scaling** (`t_kernel_rfl` on the mock ISA, `RegaScaleTest.lean`): `sl250` 0.7 s,
  `sl1000` 2.9 s, `sl2000` 5.9 s, `bl50` 0.7 s, `bl250` 3.6 s, `bl250_cross` 3.8 s, `spill20` 0.2 s
  (`nslots > 0 ∧ saved ≠ []`). `pmoveAux`/`shuffle` run in the kernel; `findSlotFor`/`slotBusy`
  are linear in `nslots`.
* **Litmus suite** (`RegaLitmusTarget/Progs/Test.lean`): concrete toy-x64 `litmusTarget` with all
  `GprTarget`/`FrameTarget`/`VecTarget` fields proved; 13 programs (`branches`, `loop`, irreducible
  `evenOdd`, `nested`, `(i64,bool)` `pairLoop`, `vec 2 i32` `vecLoop` with `vmovi`, `inc`+`carryCall`,
  `bits8`; `cmpJcc`, `adcChain`, `adcxAdox`, loop-carried-CF `cfLoop` with `dec`/`jnz`+`lea`), each
  with `Fn.Wf`, kernel-checked lowering, emitted-code pins, end-to-end `*_correct : FnSpec` via
  `lowerFn_correct`, and concrete-host `*_nonvacuous` executions (e.g. `cfLoop 3 2^63 = (2^63+25, false)`).
* **Axioms:** every headline theorem is `[propext, Classical.choice, Quot.sound]`; 0 `sorry`,
  0 `bv_decide`/`native_decide`/`ofReduceBool`.

## 4. Follow-ups (Recorded at Snapshot Time)

1. `Spill` variant/flag-home heuristics (see section 1) — needed for `adcxAdox` and `cfLoop`
   without hint patches (later addressed in `docs/reports/spill_flags.md`).
2. Module-level label distinctness (`f.L1` vs `f` + `.L1`), linear slot scans in `shuffle`, and
   `Live` → `Rega` import direction.
3. Drop unused `DefFact.{addVar64, copy}` constructors.
4. Rebase onto `TargetLemmas.lean` (`SlotWidth.bits_eq_64_mul_slots`) and switch `listTyEq` to
   `Ty.listBeq`.
