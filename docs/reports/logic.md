# logic: program logic, notation, union-find (plan step 2c)

Owner: `logic`. Files: `LeanQbe/Logic/{Mem,MemLemmas,Rules}.lean`, `LeanQbe/Notation.lean`,
`LeanQbe/Examples/{UnionFind,UnionFindLemmas,LratRup,LratRupLemmas,LratTrim,LratTrimStrictLemmas,LratTrimCheckLemmas,LratBytes,LratBytesSpec,LratBytesDimacsLemmas,LratBytesRupLemmas,LratBytesCheckLemmas,LratBytesLemmas}.lean`.

## Status

| Milestone | State |
|---|---|
| L1 notation + logic | done: `Notation.lean` (direct `Expr` elaborator + `qbe_def` command), `Logic/{Mem,MemLemmas,Rules}.lean`; builds with `--wfail`, no `sorry` |
| L2 union-find | done, specs accepted by reviewer (#34): `find` (path halving, a join-point loop), `union` (calls `$find`), `unionInline` (macro), total correctness against a functional model, non-vacuity (`uf_init`, `find_nonvacuous`, `union_nonvacuous`, `merge_init_1_2`), `Func.Wf` for all three |
| L3 RUP check (step 7) | done, spec accepted by reviewer (#104): `checkRup` = Kraken's `br_check_clause_non_strictly_by_propagation` in QBE notation, proved against the Bedrock2 spec; non-vacuity (`checkRup_nonvacuous`) + completeness (`checkRup_accepts_tautology`); `Func.Wf` |
| L4 Full LRAT-trim (step 7) | done, specs accepted by reviewer (#145, #155): all 5 `lrat-trim.c` functions ported (`checkRup`, `strictCheck`, `checkClause`, `checkProof`, `trimProof`), differential-tested bit-for-bit against Bedrock2 C on x64 and arm64 (#153), and proved (`strictCheck_correct`, `checkClause_rup_correct`, `checkClause_strict_correct`, `checkProof_correct`) with concrete-memory non-vacuity (`strictCheck_nonvacuous`, `checkClause_rup_nonvacuous`, `checkClause_strict_nonvacuous`, `checkProof_nonvacuous`) and `Func.Wf` |
| L5 Untrusted-bytes LRAT checker | done, TCB & spec accepted by reviewer (#203), 5-way differential/guard-page tested (#202): 6-function module `lratBytesFns` (`lrat_check_bytes`, `exits = []`, zero input validity preconditions) over raw ASCII DIMACS + Binary LRAT bytes + uninitialized `region work_ptr work_len`; proved (`lratBytesFns_wf`, `lratBytesExactEnv_sound`, `lratBytesEnv_sound`, `parseDimacs_encodeDimacs`, `lratCheckBytes_encoded_correct`, `nvBytesCnf_unsat`, `lratBytesAcceptEnv_sound`, `lratBytesRejectEnv_sound`, `lratCheckBytes_accepts_nonvacuous`, `lratCheckBytes_rejects_nonvacuous`) |
| Risk 8 elaboration scaling | done (#125, #144, #149): replaced macro expansion with a direct de-Bruijn `Expr` elaborator in `Notation.lean` and added `qbe_def` (bypasses `addPreDefinitions`/codegen): 4000-insn function elaborates + kernel-checks in **103 ms** (wall **0.59 s**), down from **> 120 s timeout** |

Axioms of `find_correct`, `union_correct`, `unionInline_correct`, `union_nonvacuous`, `checkRup_correct`,
`checkRup_nonvacuous`, `checkRup_accepts_tautology`, `strictCheck_correct`, `strictCheck_nonvacuous`,
`checkClause_rup_correct`, `checkClause_strict_correct`, `checkProof_correct`, `checkProof_nonvacuous`,
`lratBytesEnv_sound`, `lratBytesExactEnv_sound`, `parseDimacs_encodeDimacs`, `nvBytesCnf_unsat`,
`lratBytesAcceptEnv_sound`, `lratBytesRejectEnv_sound`, `wp_loop`: `propext, Classical.choice, Quot.sound`.

Check: `timeout 900 lake build --wfail LeanQbe.Notation LeanQbe.Examples.UnionFindLemmas LeanQbe.Examples.LratRupLemmas LeanQbe.Examples.LratTrimStrictLemmas LeanQbe.Examples.LratTrimCheckLemmas LeanQbe.Examples.LratBytesLemmas`.

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

## L5: Untrusted-bytes ASCII DIMACS + Binary LRAT proof checker (`lrat_check_bytes`)

Unlike L3/L4 (which port Bedrock2's `lrat-trim.c` over a pre-parsed in-memory `kernelState` and abort on
invalid proofs via `exit $lrat_fail`), L5 builds a **total, standalone byte-level proof checker**
`lrat_check_bytes(cnf_ptr, cnf_len, prf_ptr, prf_len, work_ptr, work_len) -> 0 | 1` with **`exits = []`**
and **zero structural preconditions** on `cnfBytes`, `prfBytes`, or `work`:

- **Precondition**: `((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆ R_mem) m`
  with only 64-bit slice non-wraparound (`ptr.toNat + len < 2 ^ 64`).
- **Postcondition (`lratCheckBytesSpec`)**: returns `[r]` (`X` unconstrained, instantiated to `False`) with
  `r = 0 ∨ r = 1`, `r = 1 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`, and memory restored to
  `((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆ R_mem) m'`.
- **Encoder round-trip (`parseDimacs_encodeDimacs`)**: for any `ValidDimacsCnf cnf` (`cnfMaxVar cnf < 2^28`,
  `cnf.clauses.size < 2^28`, positive variables `1 ≤ l.1`), `parseDimacs (encodeDimacs cnf) = some cnf`,
  yielding `lratCheckBytes_encoded_correct` where `parseDimacs` disappears completely from the conclusion
  (`r = 1 → cnf.Unsat`).

### Architecture and proof decomposition

To keep every function $\le 6$ arguments (fitting System V x86-64 `rdi..r9` and AAPCS64 `x0..x5` without
stack arguments) and compile cleanly in $< 2\text{ s}$ via `kernel_rfl`, `lratBytesFns` splits into 6
acyclic functions sharing an 80-byte workspace header at `work_ptr` once `work_len ≥ 128`:

| File | Lines | Contents |
|---|---:|---|
| `LratBytes.lean` | 949 | `parseDimacs` (~100 lines, 100% structurally recursive), `encodeDimacs`, `encodeLrat`, 6 QBE functions (`lb_parse_dimacs_header`, `lb_parse_dimacs_body`, `lb_read_add_lits`, `lb_rup_check`, `lb_check_prf`, `lrat_check_bytes`), `lratCheckBytesSpec`, `nvBytesCnf`, `nvDimacsBytes`, `nvLratAcceptBytes`, `nvLratRejectBytes` |
| `LratBytesSpec.lean` | 727 | `lratBytesFns_wf` (`wf_reify`), `loadub_At`, `region` ↔ `byte1Array`/`int4Array`/`word8Array` bridges, pure mirror `runLratCheckBytes`, `WorkCfg`, `TableRel`, `WorkState`, `WorkState.to_region`, per-function contracts |
| `LratBytesDimacsLemmas.lean` | 1982 | `lbParseDimacsHeader_correct`, `lbParseDimacsBody_correct`, `parseBodyPure_sound`, `ValidDimacsCnf`, `parseDimacs_encodeDimacs` |
| `LratBytesRupLemmas.lean` | 1923 | `readLeb128_spec`, `lbReadAddLits_correct` (zig-zag decoding + pool arena allocation), `lbRupCheck_correct` (RUP phase 1 + phase 2 + trail backtrack), `rupCheckPure_sound` |
| `LratBytesCheckLemmas.lean` | 2066 | `TableSound`, `initClauseTable_sound`, `checkPrfAux_sound_of`, `runLratCheckBytes_sound_of`, `lbCheckPrf_correct_of` (`'a'`/`'d'` loop + empty-clause termination), `lratCheckBytes_exact_of` (workspace partitioning, zeroing loops, full call-chain composition) |
| `LratBytesLemmas.lean` | 458 | `runLratCheckBytes_sound`, `lratBytesExactEnv_sound`, `lratBytesEnv_sound`, `lratCheckBytes_encoded_correct`, `nvBytesCnf_unsat`, `lratBytesAcceptEnv_sound`, `lratBytesRejectEnv_sound`, `lratCheckBytes_accepts_nonvacuous`, `lratCheckBytes_rejects_nonvacuous` |

### Proof-engineering notes

1. **Two-layer refinement via `runLratCheckBytes`.** Every QBE function is proved to refine a total,
   structurally recursive pure mirror (`lratCheckBytesExactSpec`: `r = if runLratCheckBytes ... then 1 else 0`).
   This yields both soundness (`lratBytesEnv_sound` via `runLratCheckBytes_sound`) and exact executable
   completeness on concrete inputs (`nvAccept_run` and `nvReject_run` by `rfl`, proving `nvBytesCnf_unsat`
   and inhabiting both `r = 1` and `r = 0` without loop unrolling).
2. **Zero-cleanup rejection via `region`.** Because the workspace starts and finishes as `region work_ptr work_len`,
   every reject branch (`ret 0` on malformed DIMACS, 5+-byte/truncated LEB128, `-0`, RAT hint, out-of-range
   variable/clause ID, pool exhaustion, or RUP non-conflict) collapses `WorkState` (plus any modified
   `values`/`trail`/pool slices) back to `region c.hdr c.activeBytes` in one step (`WorkState.to_region`),
   requiring backtracking only after a succeeding non-empty RUP step.
3. **`Std.Sat.CNF.Clause` module opacity.** Under Lean 4's `module` system, `CNF.Clause.ofLiterals` is
   encapsulated across module boundaries (`CNF.Clause.literals_ofLiterals` is `@[simp]`, not defeq).
   `LratBytesLemmas.lean` exports `nvDimacsBytes_eq` and `@[simp]` length lemmas (`nvDimacsBytes_length`,
   `nvLratAcceptBytes_length`, `nvLratRejectBytes_length`) so downstream x86-64 and AArch64 machine proofs
   discharge slice bounds by `simp` without needing `import all Std.Sat.CNF.Basic`.

## T3: Typed IR Notation (`LeanQbe.T.Notation`)

`LeanQbe/T/Notation.lean` adds QBE-style typed notation (`tqbe { … }`, `tqbe -> … { … }`,
`tqbe(%a:t, …) -> … { … }`, `tqbe $sym(%a:t, …) -> … { … }`, and `tqbe_def`) elaborating
directly to `LeanQbe.T.Expr` / `Func` / `Fn` via a direct de Bruijn `TermElabM` elaborator (no
mutable-local SSA conversion; structured sugar only per `G6`):

- **Typed parameters and `group` signature inference**: `@label(%x:t, …)` infers `group` block
  signatures directly; supports QBE shorthands (`b`, `w`, `l`, `s`, `d`) and explicit types
  (`bool`, `i8`, `i16`, `i32`, `i64`, `bits n`, `f16`, `f32`, `f64`, `f128`, `v4i32`, `v8i32`,
  `v2i64`, `v4f32`, `vec k t`, `pair a b`, `(a, b)`, `mask t`, or Lean `Ty` identifiers).
- **Multi-result, pair, and vector operations**: `%s, %c =l addc …`, `subb`, `%lo, %hi =l umulw`
  / `smulw`, `%p =(l,l) mkpair …`, `unpair`, `fst`, `snd`, wildcards `%_`, multi-result `call`,
  lane-wise vector immediates (`[a₀, a₁, …]`, `splat c`, nested pairs), plus scalar/float/cast/SIMD
  (`ternlog`, `shufd`, `shufb`, `alignr`, `blendw`, `sha256*`, `bitcast`) and memory ops.
- **Structured §2 sugar**: `loop @l(%x:t = init, …) { … }` (with optional `-> @brk(%r:t)` or
  `%r:t <- loop …`, supporting `%_` wildcard loop parameters), `break` / `continue` (innermost
  or role-checked `@label`), `check %c else <target>`, `switch %v { k => <target>, …, _ => <target> }`
  (omitting `_ =>` emits `.hlt` on fallthrough), and `<-` / `use` macro splicing.

### Direct projection/explicit-`Op.mk` elaborator performance design

To prevent the `27.3 s` elaboration slowdown and `> 120 s` `LCNF base` timeout observed in `T2`
when nesting pattern-matching lambdas `fun (x, ()) => …`, `LeanQbe.T.Notation` emits:
1. **Typed tuple projections (`Prod.fst` / `Prod.snd`)** over explicit `Tup V ts` binders rather
   than pattern-matching `match` expressions on `Prod`/`PUnit` (`Prod`/`PUnit` definitional eta
   still preserves `rfl` against hand-written pattern matches, while matching `t_wf_tac`'s
   `Tup`/`TRel` shape).
2. **Explicit `{sig}`/`{rs}` `Op.mk` applications** with de Bruijn `.bvar`s instead of wrapper calls
   whose implicit type arguments trigger repeated unification across 2000 nested continuations.

Stand-alone `-Dprofiler=true` benchmark (`maxRecDepth 16384`) on a literal 2000-instruction straight-line
executable `def` (`set_option profiler true` + `wf_reify` / `t_wf_reify`):

| Target | `process pre-definitions` | `LCNF base` | `LCNF mono` | `LCNF impure` | `IR` | `wf_reify` / `t_wf_reify` kernel check | Total wall time |
|---|---:|---:|---:|---:|---:|---:|---:|
| E1 `sl2000` (`qbe(%a)` + `wf_reify`) | 1.45 s | 305 ms | 2.35 s | 170 ms | 36.4 ms | 5.64 s | **10.99 s** |
| T3 `sl2000` (`tqbe(%a:l)` + `t_wf_reify`) | 4.09 s | 492 ms | 226 ms | 14.9 ms | 2.51 ms | 6.50 s | **12.74 s** (`1.16×`) |

### `rfl` parity & `T3` test suite (`LeanQbeTest/T/NotationTest.lean`)

- **Kernel `rfl` parity**: `add128`, `mulByAdd`, `qrStep` (`[16, 16, 16, 16]` and `splat 16`),
  `vumin k` (polymorphic `vec k w`), `evenOdd` (`@even`/`@odd` mutual group), `readLeb128T`, and
  `lbCheckPrf` (typed IR transliteration of `LeanQbe/Examples/LratBytes.lean`'s `'a'`/`'d'`
  `switch`/`check`/nested-loop proof loop) all prove `= <handwritten term>` by `rfl`, plus
  `Func.Wf` via `t_wf_reify` (or `t_wf_tac` for polymorphic `vumin k`) and `checkTFlat = true`.
- **2000-instruction executable `def` in suite**: `LeanQbeTest.T.NotationTest.sl2000` (`def`, not
  `noncomputable def`) elaborates via `tqbe(%a:l) -> l` and passes both `sl2000_wf` (`t_wf_reify`)
  and `sl2000_check` (`t_kernel_rfl`).
- **Companion `T2` `#29` cleanups**: clarified `Func.checkTFlat` docstring in `LeanQbe/T/Flat.lean`,
  documented `t_wf_reify`/`t_kernel_rfl` preference + added cheap `hasExprMVar` check in
  `LeanQbe/T/FlatLemmas.lean`, and added cross-block 50-block benchmark `bl50_cross` in
  `LeanQbeTest/T/ScaleTest.lean`.
- **Elaborator hardening & negative test coverage**: LHS binder type checks on `addc`/`subb`/`unpair`,
  shadow-free macro argument resolution (`withResolvedMacroArgs` when `%x` and `@x` share a name),
  symbolic `bitcast` size proofs (`dsimp` + `omega` under `Tactic.run` without leaking `sorry`/noise
  on mismatch), pair immediate type inference (`(1:l, 2:w)`), `%x:l = load %p` LHS-typed loads,
  optional `()` on `loop ... -> @brk`, `%_` loop parameters, label-role enforcement (`break @L`
  requires `.loopBreak`, `continue @L` requires `.loopHeader`, scoped inside the loop body with loop
  initializers elaborated before break-label local declarations), hygienic anonymous internal binders
  for `switch` comparisons and unnamed loops/breaks (no leaked `_cmp`/`_loop`/`_break` user names),
  rejection of bare integer literals at `.float` leaves and symbolic float trees (`vec k s`,
  requiring explicit `imm ⟨...⟩` bit patterns such as `(Float.toBits 2.0).toBitVec`), range checks
  on bitvector literals (`k < 2^n`, `-k` in `[1, 2^(n-1)]` for `n ≥ 1`, and `-0` rejected at all bit
  widths), `imm8 < 256`, literal-only
  and duplicate-free `switch` arms (with `.hlt` fallback when `_ =>` is omitted), concrete
  `zext`/`sext`/`trunc`/`ext*` direction checks, symbolic label jump guard, float `switch` rejection,
  duplicate group label / binder / loop-break-name checks, and `#guard_msgs` negative tests in
  `LeanQbeTest/T/NotationTest.lean`.

### Step T4 — Typed IR proof kit & Union-Find (`LeanQbe/T/Logic/*`, `LeanQbe/T/Examples/UnionFind*`)

Added the `LeanQbe.T` separation-logic and algebraic proof kit in `LeanQbe/T/Logic/` (10 modules, all re-exported via `public import` in `LeanQbe.lean`, zero `Kraken.X64`/`Kraken.AArch64` imports), ported Union-Find to `LeanQbe.T.Examples.UnionFind`, re-proved all 8 `T1` spike-4 tests using the kit, and updated `LeanQbeTest/T/NotationTest.lean` float immediates to concrete IEEE bit patterns (`#46` fix).

* **`LeanQbe/T/Logic/` modules (4,247 lines total vs 1,046 lines in E1 `LeanQbe/Logic/`):**
  - `Arith.lean` (647 lines): positional `limbsVal`/`limbsArg` (`@[grind =]`), `carry_zero_of_lt`, `mac_bound`, `add2_combine`, `add2_combine_mul`, `add128_combine`/`add128_combine_ci`/`add128_combine0`, `add256_combine_ci`/`add256_combine0`, `add_limb_step`, `mac_combine`, `schoolbook_step`, `schoolbook_2carry_step`, `subb2_borrow_eq_decide`, `subb128_borrow_eq_decide`/`subb128_borrow_eq_decide0` (avoiding `omega` blowup on `≥ 2^128` coefficients), signed widening multiplication identity `smulw_toInt` + `smulw_hi_toInt`/`smulw_lo_toNat` (`#18` #7), width extension/truncation helpers, `sdivDefined_iff`/`sdivDefined_of_pos`, and both `Decidable` and non-`Decidable` `BEq`/bitvector `CmpOp.evalBits`/`CmpOp.evalBool` equivalences.
  - `BitVec.lean` (201 lines vs 186 in E1, `+15`): 64-bit pointer arithmetic (`ptr4`, `shl_two`, `shl_three`), cursor comparisons, and `jnz` branching lemmas (`ult_branch`, `ule_branch`, `bv_eq_zero_branch`, `bv_odd_branch`, `cursor_eof_branch`).
  - `Ops.lean` (1,216 lines, new in `T4`): `vals_nil`/`vals_cons` (`Tup (Arg Val)` pattern-matched so `vals` reduces cleanly under `simp` even on symbolic `tqbe` terms), `Op.mk` helpers (`wp_let_op`, `wp_let_mk1..3`, `wp_let_unary`/`binary`/`ternary`/`cmp`/`select`/`cast`), per-opcode `wp_let_*_eq` rewrite rules for all 64 `OpCode` constructors (including shuffle/SHA/FP), and `wp_addc`-style named-result specs for every scalar opcode in `OpCode` (`wp_add`, `wp_sub`, `wp_mul`, `wp_neg`, `wp_and`, `wp_or`, `wp_xor`, `wp_not`, `wp_ternlog`, `wp_shl`, `wp_lshr`, `wp_ashr`, `wp_rotl`, `wp_rotr`, `wp_fshl`, `wp_fshr`, `wp_bswap`, `wp_clz`, `wp_cls`, `wp_rbit`, `wp_ctz`, `wp_popcnt`, `wp_cmp*`/`wp_eq`..`wp_sge` without mask `cast`, `wp_select*`, `wp_zext*`, `wp_sext*`, `wp_trunc*`, `wp_ofBool*`, `wp_addc_mk`, `wp_subb_mk`, `wp_umulw_mk`, `wp_smulw`, `wp_smulw_div_mod`, `wp_udiv`, `wp_sdiv`, `wp_urem`, `wp_srem`, `wp_udiv0`, `wp_sdiv0`, `wp_mkpair`, `wp_unpair`, `wp_bitcast*`, `wp_shufd`..`wp_sha256msg2`, `wp_fadd`..`wp_fcvt`). Note: `OpCode` has total `udiv0`/`sdiv0` only (not `srem0`/`urem0`, per `typed_ir_plan.md` §0).
  - `Vec.lean` (680 lines, new in `T4`): `setLane`, `splatV`, `ofLaneFn`, `maskLane`, `setMaskLane`, `splatMask`, `vec_ext`, leaf-wise `lane_lift1`..`3`, **`lane_liftCmp`**, **`lane_liftFCmp`**, **`lane_blendV`**, and **`lane_blend_liftCmp`** (`#18` #7), bitvector specializations, vector opcode lane specs (`wp_vec_add`/`sub`/`mul`/`neg`/`and`/`or`/`xor`/`not`/`ternlog`/`shl`/`lshr`/`ashr`/`rotl`/`rotr` + `wp_vec_*_splat`, cast-free `wp_vec_cmp`, `wp_vec_blend` covering `qrStep`, `vumin`, `vpaddd`, `vpternlogd`, `vprord`, `vpsrld`), and generic `Lanewise1`..`4` + `LanewiseX` (`lanewiseX_iff_lane`, `lanewise*_mono`, `lanewise3_blend_cmp`).
  - `Mem.lean` (54 lines vs 32 in E1, `+22`), `MemLemmas.lean` (548 lines vs 168 in E1, `+380`), `Cells.lean` (206 lines vs 185 in E1, `+21`), `Bytes.lean` (319 lines vs 272 in E1, `+47`), `ZeroTerm.lean` (77 lines vs 75 in E1, `+2`): separation-logic framing over `Kraken.Mem 64` for `cell`, `cell64`, `array`, `array64`, `bytes`, `region`, `word8`/`int4`/`byte1`, `ZeroTermInts`, `bytes64`/`array64_bytes`, `bytesOf`/`array_bytes`, generic `loadVal_frame`/`storeOk_frame`/`storeMem_frame`, and post-`t_wp_unfold` `load_*_step`/`store_*_step` rules.
  - `Rules.lean` (299 lines vs 128 in E1, `+171`): `Blocks.get_here/there`, group-matched `wp_loop_group`, `wp_join_group`, `wp_loop_break_group`, `wp_unroll_group` unifying directly with `tqbe`'s `Expr.group` without higher-order unification issues, `wp_load_cell`/`cell64`/`array64` + `wp_store_cell`/`cell64`/`array64`, `t_wp_unfold` / `t_wp_unfold_all` (non-`Decidable` `BEq`/bitvector cmp rules, shuffles/SHA/FP coverage, plus `scoped` `wp_unfold` / `wp_unfold_all` / `wp_step` / `branch_t` / `branch_f`).
* **Union-Find port (`LeanQbe/T/Examples/UnionFind.lean`: 131 lines vs 125 in E1, `+6`; `UnionFindLemmas.lean`: 228 lines vs 263 in E1, `-35`):**
  - `findK`, `find`, `union`, `unionInline` (`tqbe` notation throughout, including `findK` fragment), `Forest`, `uf`, `merge`, `findSpec`, `unionSpec`, `ufFns`, `ufEnv`.
  - Proved `Forest.halve`/`Forest.link` (via `grind`), `findK_spec`, `find_correct`, `link_spec` (`tqbe` notation), `union_correct`, `unionInline_correct`, `find_wf`/`union_wf`/`unionInline_wf` (via `t_wf_reify`), `uf_init`, `union_nonvacuous`, `find_nonvacuous`, `merge_init_1_2`, `ufFns_wf`, `ufEnv_sound`. (`uf_fnSpec` and compiled `*_witness`/`*_returns` depend on `Abi`/`Rega`/`Main` and are deferred to `T11`/`T12`; E1 lines 1–187 were 187 source-level lines vs 228 here including full `Forest` proofs + module soundness.)
* **Proof-kit test suite (`LeanQbeTest/T/KitTest.lean`, 986 lines; `#46` fix in `NotationTest.lean`):**
  - Section 1 re-proves all 8 `T1` spike-4 functions (`add128`, `add256` via `addLimbs_wp`, `mac`, `ult128`, `umin`, `mulByAdd`, `qrStep`, `vumin`) in **168 lines** (`KitTest.lean` lines 27–194) vs **358 lines** total in `LeanQbeTest/T/Examples.lean` (`qrStep_kit` 2 lines, `umin_kit` 4 lines, `add128_kit` 7 lines, `vumin_kit` 9 lines).
  - Sections 2–7 test `tqbe` versions (`add128Tqbe`..`qrStepTqbe` `= Examples.*` by `rfl`), `t_wf_reify`, polymorphic `qrStepK`, `vpaddd`/`vpternlogd`/`vprord`/`vpsrld`/shuffle/SHA, `smulw8` edge cases (`-128 * -128`, `-128 * -1`, `-5 * 3`, `0 * -128`), `smulw64_div_mod_test`, `mulAdd64_schoolbook_spec`, `add256_combine0`, `schoolbook_2carry_step`, `udiv0`/`sdiv0`/`udiv`/`sdiv`/`urem`/`srem`/`sdivDefined_iff`, bit/cast/control-flow (`wp_loop_break_group`, `wp_join_group`, `wp_unroll_group`, `wp_step`, `branch_t`/`f`, `bswap`/`switch`/`check`), all 13 scalar float opcodes + `floatResultWp` NaN non-vacuity, separation-logic framing + post-unfold `load_array64_step`/`store_array64_step`, and `zeroTerm_jnz_step`.
  - Updated `LeanQbeTest/T/NotationTest.lean` lines 489–490, 506–508, 550, and 940–942 from `(Float.toBits ...).toBitVec` / `(Float32.toBits ...).toBitVec` to concrete IEEE literal bitvectors (`0x00000000#32`, `0x3f800000#32`, `0x0000000000000000#64`, `0x3ff0000000000000#64`, `0x3ff8000000000000#64`, `0x4000000000000000#64`, `0x4008000000000000#64`) so `#46` remains kernel-reducible.
