# logic: program logic, notation, union-find (plan step 2c)

Owner: `logic`. Files: `LeanQbe/Logic/{Mem,MemLemmas,Rules}.lean`, `LeanQbe/Notation.lean`,
`LeanQbe/Examples/{UnionFind,UnionFindLemmas,LratRup,LratRupLemmas,LratTrim,LratTrimStrictLemmas,LratTrimCheckLemmas}.lean`.

## Status

| Milestone | State |
|---|---|
| L1 notation + logic | done: `Notation.lean` (direct `Expr` elaborator + `qbe_def` command), `Logic/{Mem,MemLemmas,Rules}.lean`; builds with `--wfail`, no `sorry` |
| L2 union-find | done, specs accepted by reviewer (#34): `find` (path halving, a join-point loop), `union` (calls `$find`), `unionInline` (macro), total correctness against a functional model, non-vacuity (`uf_init`, `find_nonvacuous`, `union_nonvacuous`, `merge_init_1_2`), `Func.Wf` for all three |
| L3 RUP check (step 7) | done, spec accepted by reviewer (#104): `checkRup` = Kraken's `br_check_clause_non_strictly_by_propagation` in QBE notation, proved against the Bedrock2 spec; non-vacuity (`checkRup_nonvacuous`) + completeness (`checkRup_accepts_tautology`); `Func.Wf` |
| L4 Full LRAT-trim (step 7) | done, specs accepted by reviewer (#145, #155): all 5 `lrat-trim.c` functions ported (`checkRup`, `strictCheck`, `checkClause`, `checkProof`, `trimProof`), differential-tested bit-for-bit against Bedrock2 C on x64 and arm64 (#153), and proved (`strictCheck_correct`, `checkClause_rup_correct`, `checkClause_strict_correct`, `checkProof_correct`) with concrete-memory non-vacuity (`strictCheck_nonvacuous`, `checkClause_rup_nonvacuous`, `checkClause_strict_nonvacuous`, `checkProof_nonvacuous`) and `Func.Wf` |
| Risk 8 elaboration scaling | done (#125, #144, #149): replaced macro expansion with a direct de-Bruijn `Expr` elaborator in `Notation.lean` and added `qbe_def` (bypasses `addPreDefinitions`/codegen): 4000-insn function elaborates + kernel-checks in **103 ms** (wall **0.59 s**), down from **> 120 s timeout** |

Axioms of `find_correct`, `union_correct`, `unionInline_correct`, `union_nonvacuous`, `checkRup_correct`,
`checkRup_nonvacuous`, `checkRup_accepts_tautology`, `strictCheck_correct`, `strictCheck_nonvacuous`,
`checkClause_rup_correct`, `checkClause_strict_correct`, `checkProof_correct`, `checkProof_nonvacuous`,
`wp_loop`: `propext, Classical.choice, Quot.sound`.

Check: `timeout 900 lake build --wfail LeanQbe.Notation LeanQbe.Examples.UnionFindLemmas LeanQbe.Examples.LratRupLemmas LeanQbe.Examples.LratTrimStrictLemmas LeanQbe.Examples.LratTrimCheckLemmas`.

## What exists

**Notation** (`Notation.lean`). `qbe(%p, %x) { … }` is a function, `qbe { … }` a fragment. Both
elaborate to `Expr V L` for whatever `V L` the expected type has, so the same text gives the `wp`
instance and the compiler instance. The syntax is QBE's (`%x =l add %a, %b`, `%c =w csltl`, `loadub`,
`storew`, `%r =l call $f(%a, 1)`, `exit $f(…)`, `jmp @l(…)`, `ret`). There are three PHOAS
differences: `jnz %c, T, E` where each target is `@l(args)` or an inline `{ block }`; join points
`@l(%a, %b) { … }`, where consecutive ones form one mutually recursive group scoped over the
statements after it; and Lean functions as macros, `%r <- f(%a, %b)` meaning `f a b fun r => …`.
`⟨t⟩` splices a Lean term. Checked by `rfl` against hand-written terms in a prototype (evenOdd, find,
union).

**Logic** (`Logic/`). It is about 220 lines:
- `cell64 a v`, `array64 a xs` over Kraken's `Mem 64` with `Kraken.Separation`'s `⋆`, in the byte
  layout of `storeMem` (`Int.toBytes 8 v.toInt`, which is Kraken's own store);
- `loadVal_cell64`, `store_cell64`, `loadVal_array64`, `store_array64` (element `i` at
  `a + ofNat (8*i)`), `array64_focus/_set/_append`;
- `sep_ex_l`, `sep_pure_l`, which pull `∃` and pure facts out of `⋆` (missing in Kraken);
- `array64_bytes`: every array that fits is satisfied by its bytes (non-vacuity of any `array64`
  spec);
- `wp_loop`, the loop rule. `Inv : Nat → args → Mem → Prop` is indexed by the measure, and the body
  may jump back only at a smaller measure. It is derived from `wp`'s block closure hypothesis by strong
  induction, in 6 lines. `wp_join` covers forward join points;
- `wp_unfold`: one `simp only` set that unfolds `wp` over straight-line code and evaluates operations
  and comparisons (`truthy_boolVal`, `shl_three`).

**Union-find** (`Examples/UnionFind*.lean`).
- The model is the partition itself: `rep : Val → Val` gives the canonical representative.
  `uf p n rep` means: the array of `n` words at `p` is a `Forest` whose roots are exactly `rep`'s
  values. The forest also carries a ghost `rank` that decreases towards the roots; it is `find`'s
  termination measure.
- `findSpec`: from `uf p n rep ⋆ R` and `x < n`, return `[rep x]` with `uf p n rep ⋆ R` (same
  partition, different array).
- `unionSpec`: end in `uf p n (merge rep x y) ⋆ R`, where
  `merge rep x y i = if rep i = rep x then rep y else rep i`.
- Both are `Spec`s (`args m Q X`), so they plug into `Γ` and `Func.spec`. `union_correct` assumes
  `findSpec → Γ "find"`, and `find_correct Γ'` discharges that when `Γ "find" = Func.spec Γ' find`.

## Measured

| | lines | elaboration |
|---|---|---|
| `Logic/` (3 files) | 221 | 0.35 s + 0.33 s + 0.03 s |
| `Notation.lean` | 235 | 1.8 s (meta code compiled) |
| `UnionFind.lean` (programs, model, specs) | 115 | 0.3 s |
| `UnionFindLemmas.lean` (all proofs, Wf, non-vacuity) | 160 | 2.6 s, of which `grind` 1.4 s |

Proof breakdown:
- `findK_spec`, the loop: 30 lines;
- `link_spec` + `union_correct` + `unionInline_correct`: 30 lines;
- the model lemmas `Forest.halve` and `Forest.link`: one `grind` line each. They were 40 hand-written
  lines in the prototype, which checked in 0.3 s instead of 1.4 s.

For comparison, Kraken's Bedrock2 `exec_rup_phase1_loop` (`LratTrimRupProof.lean`) has a
26-line invariant. Most of it is locals bookkeeping (`l'["x"]? = some …`, the "every other local
unchanged" clause). In PHOAS the SSA values are Lean variables, so `find`'s invariant is 2 lines and
there is no locals reasoning at all.

## Where the logic hurt (and what fixed it)

1. **`simp` and `Decidable` instances.** In a prototype with `if a = b then 1 else 0` comparisons,
   `simp only [wp, Arg.val]` rewrote the condition but not the instance
   (`instDecidableEqBitVec (Arg.var v).val …`). After that, every `ite` lemma silently failed to fire.
   `dsimp` avoids it. Core's `boolVal`/`CmpOp.eval` (Bool-valued) side-steps it, and `wp_unfold` uses
   `truthy_boolVal`. Reported to core (#17).
2. **`Iff` lemmas do not `dsimp`.** `wp_param_cons` is an `Iff`, so continuing after `call` needs
   `simp only [wp_param_cons]`, not `dsimp`.
3. **Specs of fragments mention `.var`, not values.** After instantiation, the tail of `union` has
   `Arg.var (rep x)`. So the fragment lemma `link_spec` is stated with `⟨.var (rep x)⟩`, and `.imm`
   would not match. This is mildly surprising but harmless.
4. **`$f` in syntax.** Outside quotations Lean parses `$f` as a *pseudo-antiquotation* node. The
   notation looks for the identifier inside that node.
5. **Partially applied definitions.** `simp only [uf]` does not unfold `uf p n rep` inside `⋆`
   (equation lemmas want all arguments). `unfold uf` does.
6. **Ghost measure.** The loop rule wants the measure as an index of the invariant. `find`'s measure
   is the rank of the current node, and the rank function sits inside `uf`'s existential. The proof
   unpacks it once before the loop; this works because path halving keeps the ranks unchanged.
7. **Not needed, so not built:** a frame rule (specs thread `⋆ R` themselves), `ecancel` (one array
   in the frame), a rule for multi-block groups (`Smoke.evenOdd` uses the raw closure hypotheses),
   a `wp` for `ret` inside a macro.

## L3: the RUP check, compared with Bedrock2

Files: `Examples/LratRup.lean` (program + `checkRupSpec`), `Examples/LratRupLemmas.lean` (proof).
Check: `timeout 900 lake build --wfail LeanQbe.Examples.LratRupLemmas`. Axioms of `checkRup_correct`
and `checkRup_nonvacuous`: the standard three. `checkRup_wf` uses no axioms.

**Same function, same spec.**
- The program is `br_check_clause_non_strictly_by_propagation` with its inline helpers, on the same
  memory layout.
- `checkRupSpec` has the hypotheses and the return postcondition of Kraken's
  `br_check_clause_non_strictly_by_propagation_ok`, over the *imported* Bedrock2 model and memory
  predicates (`ClauseTable`, `ZeroTermInts`, `kernelState`, `assignBytes`, …).
- `lrat_fail` is `exit $lrat_fail(…)`, so the exit postcondition must accept exits to `lrat_fail`.
  That is the analogue of Bedrock2's `lratFailExt`, which accepts any postcondition.
- The pure RUP lemmas (`phase1_step_*`, `phase2_inner_*`, `entails_insert_of_unit_prop`, …) are
  reused from `LratTrimRupProof.lean` unchanged.
- Idiomatic QBE changes: Bedrock2's `checked` flag and its `lit = 0` / `aid = 0` loop exits become
  jumps to the continuations `@finish` / `@ph2` / `@fail`; mutable locals become join-point
  parameters; `abs` and the conditional negation are branch-free (`(x xor s) - s`, `s = x sar 63`);
  `(load4 << 32) .>> 32` is `loadsw`.

| part | Bedrock2 `LratTrimRupProof.lean` | lean-qbe `LratRupLemmas.lean` |
|---|---|---|
| reused pure RUP and model lemmas | ≈ 220 | 0 (imported) |
| bit-level facts | ≈ 30 (sec. 2) | 32 |
| memory bridging (QBE loads/stores on Kraken's `byte1`/`int4`/`word8` arrays) | in `LratTrimSpec` | 76 |
| helpers: assigned/assign literal, flush | ≈ 120 | 64 |
| backtrack loop | ≈ 74 | 47 |
| phase 1 loop | ≈ 160 | 65 |
| phase 2 inner loop | ≈ 230 | 127 |
| phase 2 outer loop | ≈ 200 | 80 |
| main theorem | ≈ 220 | 73 |
| state predicate `PState`, misc | | 28 |
| non-vacuity (concrete memory) + accepts-tautology | none | 104 + 75 |
| **total** | **1347** | **725** (620 without non-vacuity) |
| check time (wall / user, this machine) | 3.7 s / 9.6 s | 1.75 s / 5.1 s |

The program-specific proof is about 45 % of Bedrock2's. Bedrock2's figure is 1347 − 220 reused lines;
ours is 620 − 107 lines of bridging.

**Inherited weakness, and a completeness data point.** As the reviewer noted (#104), the spec,
like Bedrock2's, is also met by a function that always exits to `lrat_fail`, so it does not show that
valid clauses are accepted. `checkRup_accepts_tautology` is a first data point the other way, and
Bedrock2's development has none. On the tautology `[1, -1]` in concrete memory, `checkRup` returns
with exit postcondition `False`, so it provably does not fail. The proof (≈ 75 lines) reuses the
loop lemmas and makes `@fail` and `@ph2` unreachable (no assignment falsifies a tautology).

**What was easier, and why.**
1. *No locals.* Every Bedrock2 loop invariant carries 5 to 10 `l'["x"]? = some v` facts plus an
   "every other local is unchanged" clause (a 7-way `≠` chain). Every step re-establishes them with
   `local_pres` and `simp [h1.symm, …]`. In PHOAS the loop-carried state is the join point's parameter
   list and everything else is a Lean variable in scope, so there is no frame reasoning on variables at
   all. This is the largest single saving.
2. *Breaks are jumps.* Without the `checked` flag, the invariants lose their
   `checked = 0 ∧ … ∨ checked = 1 ∧ …` disjunctions. The phase-1 invariant has none, and the outer loop
   has one where Bedrock2 has two.
3. *Loops are lemmas over their exits.* Each loop lemma takes the continuation predicates of the
   labels it may jump to as hypotheses (`hfin`, `hph2`, `hfail`, `hdone`). The main theorem
   instantiates them with `wp_join`, which makes the composition 73 lines.
4. *`wp_unfold`* turns each basic block into one readable goal with existentials for loads and
   `storeOk ∧` for stores.

**What was harder.**
1. *`jnz` tests the low 32 bits* (QBE semantics, decided by core). Branching on a loaded literal
   needs `IsInt32` (`truthy_iff`). Writing `cnel %x, 0` first would have avoided it.
2. *Separation re-association is still manual*: `sep_assoc`, `sep_comm_l`, and
   `sep_cast h (by ac_rfl)` with an explicit frame. Kraken's `ecancel` fails when the frame
   metavariable is delayed-assigned (inside `have … := f (by ecancel)`). That happens about 15 times.
3. *Logic changes made during L3.*
   - `wp_unfold` used to unfold through join-point groups, which made nested `@setunit` goals
     unreadable. It now rewrites with per-construct lemmas (`wp_let`, `wp_load`, …) and stops at
     `label`, calls and macros.
   - Generic any-width load/store lemmas went into `Logic/MemLemmas.lean`.
   - The notation's words (`ret`, `exit`, `call`, …) had become global keywords, which broke
     `.ret` and Kraken's `Directive.ret` in importers. They are now non-reserved; only `qbe` is
     reserved.

## L4: Full LRAT-trim (`strictCheck`, `checkClause`, `checkProof`, `trimProof`) compared with Bedrock2

Files: `Examples/LratTrim.lean` (549 lines: all remaining `lrat-trim.c` functions + `lratTrimFns` +
specs), `Examples/LratTrimStrictLemmas.lean` (447 lines), `Examples/LratTrimCheckLemmas.lean` (524 lines).
Differential check (#138, #153): `Print.module LratTrim.lratTrimFns` (811 lines of QBE IL) compiled
with stock QBE on `amd64_sysv` and `arm64` produces bit-for-bit identical exit codes, `lrat_fail`
arguments, kernel-state counters, `used`, `marks`, and `values` as `Kraken.Bedrock2.Test.lratTrimC`
(`gcc -O2`) across all 12 test cases.

### `strictCheck` (`br_check_clause_strictly_by_resolution`)

| part | Bedrock2 `LratTrimStrictProof.lean` | lean-qbe `LratTrimStrictLemmas.lean` | ratio |
|---|---:|---:|---:|
| reused pure resolution & model lemmas | ≈ 496 | 0 (imported) | — |
| small program/framing helpers | 56 | 24 | 2.33× |
| loop 1 (`strictScan_spec` vs `strict_loop1_ok`) | 56 | 37 | 1.51× |
| loop 2 inner (`strictInner_spec` vs `strict_inner_loop_ok`) | 202 | 76 | 2.66× |
| loop 2 outer (`strictOuter_spec` vs `strict_outer_loop_ok`) | 200 | 104 | 1.92× |
| loop 3 (`strictFinal_spec` vs `strict_loop3_ok`) | 113 | 58 | 1.95× |
| top-level (`strictCheck_correct` + `_wf` vs §8) | 219 | 86 | 2.55× |
| non-vacuity (`strictCheck_nonvacuous`, concrete bytes) | 0 | 30 | — |
| **program-specific proof** | **846** | **385** | **2.20×** (45.5 %) |
| **total file** | **1342** | **447** (417 without non-vacuity) | **3.00×** |
| check time (wall / user) | 3.07 s / 4.69 s | 1.46 s / 2.66 s | **2.10×** |

### `checkClause` and `checkProof` (`br_check_clause`, `br_check_proof`)

| part | Bedrock2 `LratTrimCheckProof.lean` | lean-qbe `LratTrimCheckLemmas.lean` | ratio |
|---|---:|---:|---:|
| reused pure state/entailment lemmas | ≈ 253 | 0 (imported) | — |
| field/memory accessors (`loaduw_int4`, `loadsw_kfield`, `storel_stat_chk_*`) | 86 | 63 | 1.37× |
| `checkClause` (`checkClause_step`, `_rup_correct`, `_strict_correct`) | 165 | 84 | 1.96× |
| `checkProof` (`fullMemInv_*`, `checkProof_correct`) | 942 | 234 | **4.03×** |
| well-formedness (`checkClause_wf`, `checkProof_wf`) | 0 | 6 | — |
| non-vacuity (`checkClause_rup_nonvacuous`, `checkClause_strict_nonvacuous`, `checkProof_nonvacuous`) | 0 | 108 | — |
| **program-specific proof** | **1193** | **381** | **3.13×** (31.9 %) |
| **total file** | **1446** | **524** (415 without non-vacuity) | **2.76×** (3.48× w/o NV) |
| check time (wall / user) | 1.67 s / 3.33 s | 2.69 s / 3.64 s (w/o NV; 2.76 s w/ NV) | — |

### Combined LRAT-trim proof summary (all 3 files)

| metric | Bedrock2 (`Rup` + `Strict` + `Check`) | lean-qbe (`LratRup` + `Strict` + `Check`) | ratio |
|---|---:|---:|---:|
| program-specific proof lines | 1127 + 846 + 1193 = **3166** | 513 + 385 + 381 = **1279** | **2.48× shorter** (40.4 %) |
| total proof file lines (excl. concrete-byte non-vacuity) | 1347 + 1342 + 1446 = **4135** | 620 + 417 + 415 = **1452** | **2.85× shorter** (35.1 %) |
| total proof file lines (incl. 5 concrete-byte non-vacuity + tautology theorems) | **4135** (0 non-vacuity) | 792 + 447 + 524 = **1763** | **2.35× shorter** |
| total check time (wall / user) | 8.44 s / 17.62 s | 5.97 s / 11.80 s | **1.41× faster** |

**Module linking and accepting UNSAT witness (`LratTrimCheckLemmas.lean`).**
- `lratCheckFns`, `lratCheckFns_wf`, `lratEnv`, and `lratEnv_sound` package the 4-function checker call
  graph (`checkRup`, `strictCheck`, `checkClause`, `checkProof`) for `compileModule` / `compile_sound`.
- To demonstrate that the return branch (`cnf₀.Unsat`, without reaching `lrat_fail`) is inhabited end-to-end
  (#177), `nvAcceptBytes` (274 concrete bytes at `0x1000`) encodes `nvAcceptCnf = [[1], [-1]]` together with
  its 1-step resolution proof of the empty clause (`antecedents = [1, 2]`, `empty_clause = 3`). `nvAccept_pre`
  proves `CheckProofPre` for `nvAcceptCnf` on `nvAcceptBytes.At 0x1000`, and `lratAcceptEnv_sound` +
  `checkProof_accepts_nonvacuous` step `checkProof → checkClause → strictCheck` via bounded loop unrolling
  (`wp_unroll`) with exit postcondition `X = fun _ _ _ => False`, concluding `nvAcceptCnf.Unsat` unconditionally.

## Risk 8: Elaboration scaling (`elab_rules` + `qbe_def`)

Benchmark: single function with $N$ sequential `%x_i =l add ...` instructions (`Big{250,1000,2000,4000}.lean`):

| $N$ (insns) | old `macro_rules` + `def` | new `elab_rules` + `def` | `elab_rules` + `noncomputable def` | `elab_rules` + `qbe_def` (wall / user) | `qbe_def` breakdown (parse + elab + kernel) |
|---:|---:|---:|---:|---:|---:|
| 250 | 0.69 s | 0.44 s | 0.41 s | **0.40 s** / 0.21 s | 3.6 ms + 2.1 ms + 1.7 ms = **7.4 ms** |
| 1000 | 7.30 s | 0.90 s | 0.72 s | **0.44 s** / 0.25 s | 15.1 ms + 3.1 ms + 5.3 ms = **23.5 ms** |
| 2000 | 32.0 s | 2.66 s | 1.92 s | **0.47 s** / 0.27 s | 30.2 ms + 6.3 ms + 11.3 ms = **47.8 ms** |
| 4000 | > 120 s (timeout) | 10.67 s | 6.48 s | **0.59 s** / 0.37 s | 63.0 ms + 13.7 ms + 23.9 ms = **100.6 ms** |

Two bottlenecks caused quadratic scaling in `def`:
1. **Nested `fun` term elaboration** (`macro_rules` expanding each statement to `Expr.let_ ... fun x => ...`):
   replaced in `Notation.lean` (`7b0044b`) by a direct `elab_rules : term <= expectedType` elaborator that
   tracks a `NameMap Nat` binder environment and constructs `Lean.Expr` nodes with de Bruijn `.bvar`s in
   $O(N)$ time (13.7 ms at $N = 4000$).
2. **Lean's `def` post-elaboration pipeline** (`addPreDefinitions` / `abstractNestedProofs` taking 6.1 s
   and `LCNF mono` codegen taking 3.5 s at $N = 4000$): bypassed by `qbe_def`, which elaborates the term
   and calls `addDecl (.defnDecl ...)` directly in the kernel (23.9 ms kernel typecheck at $N = 4000$).
