# logic: program logic, notation, union-find (plan step 2c)

Owner: `logic`. Files: `LeanQbe/Logic/{Mem,MemLemmas,Rules}.lean`, `LeanQbe/Notation.lean`,
`LeanQbe/Examples/{UnionFind,UnionFindLemmas}.lean`.

## Status

| Milestone | State |
|---|---|
| L1 notation + logic | done: builds with `--wfail`, no `sorry` |
| L2 union-find | done: `find` (path halving, a join-point loop), `union` (calls `$find`), `unionInline` (macro), total correctness against a functional model, non-vacuity, `Func.Wf` for all three |

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

## Next

- If the reviewer asks: a `Spec`-level linking corollary (`Γ` with `find` and `union` together).
- Step 5 needs `findSpec`/`unionSpec` to compose with `FnSpec`. Their shape (`args m Q X`,
  monotone) was chosen for that.
- A delaborator, so that goals print in QBE syntax (not started).
