# logic: program logic, notation, union-find (plan step 2c)

Owner: `logic`. Files: `LeanQbe/Logic/{Mem,MemLemmas,Rules}.lean`, `LeanQbe/Notation.lean`,
`LeanQbe/Examples/{UnionFind,UnionFindLemmas,LratRup,LratRupLemmas}.lean`.

## Status

| Milestone | State |
|---|---|
| L1 notation + logic | done: builds with `--wfail`, no `sorry` |
| L3 RUP check (step 7 pulled forward) | done, proof complete, spec awaiting review: `checkRup` = Kraken's `br_check_clause_non_strictly_by_propagation` in QBE notation, proved against the Bedrock2 spec; non-vacuity; `Func.Wf` |
| L2 union-find | done, specs accepted by reviewer (#34): `find` (path halving, a join-point loop), `union` (calls `$find`), `unionInline` (macro), total correctness against a functional model, non-vacuity (`uf_init`, `find_nonvacuous`, `union_nonvacuous`, `merge_init_1_2`), `Func.Wf` for all three |

Axioms of `find_correct`, `union_correct`, `unionInline_correct`, `union_nonvacuous`, `wp_loop`:
`propext, Classical.choice, Quot.sound`.

Check: `timeout 900 lake build --wfail LeanQbe.Examples.UnionFindLemmas LeanQbe.Notation`.

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
| non-vacuity (concrete memory) | none | 104 |
| **total** | **1347** | **725** (620 without non-vacuity) |
| check time (wall / user, this machine) | 3.7 s / 9.6 s | 1.75 s / 5.1 s |

The program-specific proof is about 45 % of Bedrock2's. Bedrock2's figure is 1347 − 220 reused lines;
ours is 620 − 107 lines of bridging.

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

**Elaboration (plan risk 8).** The 234-line program file elaborates in 0.38 s (eight definitions, the
largest ~30 statements), and `Func.Wf` by `wf_tac` takes under 0.1 s. Nothing quadratic is visible at
this size.

## Next

- If the reviewer asks: a `Spec`-level linking corollary (`Γ` with `find` and `union` together).
- Step 5 needs `findSpec`/`unionSpec` to compose with `FnSpec`. Their shape (`args m Q X`,
  monotone) was chosen for that.
- A delaborator, so that goals print in QBE syntax (not started).
