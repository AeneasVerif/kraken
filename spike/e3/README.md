# D8: E1 versus E3 for the direct lowering proof

`E1Skel.lean` (uniform E1 encoding) and `E3Skel.lean` (arity-typed mutual E3 encoding,
`Expr` / `Block n` / `Blocks sig` with `letRecs sig bodies k`) contain the same development:

- the same mock `Target` and op set (const/add/load, store, jnz, jump, ret, unreachable = `hlt`);
- the same lowering design: names `V := Nat`, symbolic relation `List (Nat × Reg)`, untrusted
  hints `dest`/`entry`, moves checked at jumps;
- the same join-point predicate `LabJ G ℓ` (in E3 it takes the arity, `LabJ G n ℓ : Cont n`) and
  the same `DOk` environment invariant;
- `lower_correct` with no `sorry`, axioms `[propext, Classical.choice, Quot.sound]` in both;
- a toy target (`Reg := Nat`, `Dir` a 7-constructor inductive, `Ev := True`), the even/odd
  group, and `lower … = .ok (evenOddCode, 8, 4)` by `rfl`. Lines 1–740 of `E1Skel.lean` are
  unchanged; the toy part is appended after them.

The encoding-independent parts (code placement, `Target`, `Agree`/`Inv`, symbolic-state, move
and shuffle lemmas, about 240 lines) are copied verbatim into `E3Skel.lean`.

## Statements

E1 (one lemma by `induction hwf`):

```
lower_correct : Wf G D e₁ e₂ → lower h e₂ st = .ok (code, nv', nl') → (G below st.nv) →
  st.nv ≤ nv' ∧ ∀ k args acc m s, InfixAt code prog k → DOk G D →
    Forall₂ (fun J ℓ => J = LabJ G ℓ) acc st.pend →
    Agree G st.R s → RegsHold s st.PL args → Inv m s → wp Q e₁ args acc m → Ev k s
```

E3 (three lemmas, mutual structural recursion on the `Wf`/`WfB`/`WfBs` derivation):

```
lowerE_correct  : Wf G D e₁ e₂ → lowerE h e₂ st = .ok … → … →
  st.nv ≤ nv' ∧ ∀ k m s, InfixAt code prog k → DOk G D → Agree G st.R s → Inv m s →
    wp Q e₁ m → Ev k s
lowerB_correct  : WfB G D b₁ b₂ → lowerB h b₂ PL st = .ok … → … →
  st.nv ≤ nv' ∧ ∀ k (J : Cont n), InfixAt code prog k → DOk G D →
    (∀ as m, (∀ s, Agree G st.R s → RegsHold s PL (argsToList n as) → Inv m s → Ev k s) → J as m) →
    closedBlock Q b₁ J
lowerBs_correct : WfBs G D bs₁ bs₂ → lowerBs h bs₂ ls nv nl = .ok … → … →
  nv ≤ nv' ∧ ∀ k, InfixAt code prog k → DOk G D → closedBlocks Q bs₁ (labsJ G sig ls)
lower_correct   : WfB [] [] b₁ b₂ → lowerB h b₂ argRegs ⟨0, 0, []⟩ = .ok (code, …) →
  ∀ k as m s, InfixAt code prog k → RegsHold s argRegs (argsToList n as) → Inv m s →
    wpBlock Q b₁ as m → Ev k s
```

Nothing structurally new was needed. The relation is still two-way (Chlipala-style, `G` for
variables, `D : List ((n : Nat) × L₁ n × L₂ n)` for labels). The join-point predicate is
`LabJ`, indexed by arity. A group is instantiated all at once as
`labsJ G sig (freshLabels sig nl)`. The only new idea is the statement of `lowerB_correct`: its
continuation `J` is universally quantified with a sufficient condition, because `closedBlock`
on `.param f` peels one argument off `J` (`fun as m => J (v, as) m`), so `J` is no longer of the
form `LabJ …` below the first parameter.

## Comparison

Line counts are non-blank lines. Times are wall-clock on this machine (48 cores; single file,
`Elab.async false` for per-command times). Each was measured over 3 runs, and the runs agreed
within ±2 %.

| | E1 (`E1Skel.lean`) | E3 (`E3Skel.lean`) |
|---|---|---|
| IR definition | 10 (1 inductive, 9 ctors) | 27 (`Labels`, `Args`, 3 mutual inductives, 7+2+2 ctors) |
| `wp` | 18 (with `args`, `acc` parameters) | 20 (`wp`/`closedBlock`/`closedBlocks`, mutual) + 9 for `wpBlock` and its lemma (top-level statement only) |
| `Wf` definition | 19 (1 inductive, 9 rules) | 31 (3 mutual inductives, 7+2+2 rules) + 5 (`LPair`, `zipL`) |
| Induction principle | `induction hwf` (auto) | none written: mutual structural recursion on the derivation (`match hwf with` in term mode, tactic blocks per arm, `termination_by structural hwf`, which is optional because it is inferred) |
| `lower` | 50 (one function) | 58 (`lowerE`/`lowerB`/`lowerBs`, mutual structural) + 4 `freshLabels` |
| `LabJ`/`DOk` | 10 | 14 (+`labsJ`) and 31 of helper lemmas (`DOk.mono`, `mem_zipL_labsJ`, `DOk.group`, `bound_cons`) |
| Main lemma, statement | 13 | 12 + 13 + 10 (three statements) + 16 top-level `lower_correct` |
| Main lemma, total | 215 | 214 (+16 top-level) |
| per case: let / store / jnz | 37 / 18 / 32 | 26 / 17 / 32 |
| per case: jump / ret / hlt | 23 / 17 / 5 | 21 / 15 / 5 |
| per case: binders | `param` 21 | `WfB.body` 7, `WfB.param` 13 |
| per case: join points | `label` 16 + `block` 28 = 44 | `letRecs` 16 + `WfBs.nil` 5 + `WfBs.cons` 14 = 35 |
| Junk cases (only reject ill-formed terms) | see below: 3 constructs, ≈ 14 proof lines + 2 `wp` equations + 2 `lower` error branches + one extra invariant (`acc`/`pend`) in every case | none |
| `lower_correct` elaboration (whole main lemma, `#time`) | 1.04 s | 1.28 s (the mutual block; `process pre-definitions` for the structural recursion is 0.24 s of it) |
| `lower_correct` kernel | 28 ms | ≈ 61 ms (4 kernel checks attributed to the mutual block: 32 + 11 + 11 + 6 ms) |
| even/odd `rfl` (elaborator `rfl`, includes kernel re-check) | works, 62 ms | works, 65 ms |
| even/odd kernel-only `Eq.refl` (`kernel_rfl`) | works, 24 ms (\*) | works, 25 ms |
| File check, `lake env lean` | 1.87 s | 2.68 s, of which 0.23 s is `public meta import Lean` (only needed for `kernel_rfl`) |
| `lake build` of the module (clean, includes Lake overhead) | 2.15 s | 3.16 s |

(\*) `E1Skel.lean` imports nothing, and its header may not change, so `kernel_rfl` cannot be
defined there. The kernel-only check for E1 was run in a scratch copy with
`public meta import Lean` added. `E3Skel.lean` has `kernel_rfl` and checks both variants.

### Junk cases in E1 (absent in E3)

1. **Parameters in non-entry position.** `wp` threads an `args : List Val` through every
   constructor and has `args = []` as a conjunct of 7 of them. Each of the 7 proof cases
   spends a line on `obtain ⟨rfl, hw⟩ := hw`. `wp (.param _) [] … = False`.
2. **`block` without a pending label.** `wp (.block …) _ [] _ = False`. `lower` has an error
   branch `"block"`, and the proof a `· simp at hl` branch.
3. **The pending-label accumulator.** `St.pend`, the `acc : List Cont` argument of `wp`, and the
   invariant `Forall₂ (fun J ℓ => J = LabJ G ℓ) acc st.pend` are hypotheses of every case. Only
   `label` (`hP.append_single rfl`, 5 lines) and `block` (`cases hP`, 3 lines) use them. Every
   other case passes `.nil`.

In E3 these terms cannot be written. A block's parameters are `Block n` binders, and a group's
blocks come with their labels in `letRecs`. Both encodings keep the checks that come from
untrusted hints: jump arity against `entry.ploc`, and `PL` too short for a block's parameters.

### What differs in the proofs

- The leaf cases (store, jnz, jump, ret, hlt) are the same script in both, minus E1's
  `args = []` line.
- E1's `let_` and `param` repeat the "`DOk` under a larger `G`" and "fresh name above `G`"
  arguments inline, 3 + 4 lines each time. In E3 they became `DOk.mono` and `bound_cons`,
  because three lemmas need them. Moving them to helpers would shorten E1's `let_` to about 28
  lines. Per case, the honest difference is the junk lines, not the encoding.
- Join points. In E1, `label` registers `LabJ G ℓ` in `acc`, and later `block` pops it and
  proves it from the block body: 44 lines, coupled through `acc`/`pend`. In E3, `letRecs`
  instantiates the whole group at once and gets `closedBlocks` from `lowerBs_correct`
  (16 lines). `WfBs.cons` (14 lines) proves one block's `LabJ` from `lowerB_correct`. The
  price is 31 lines of environment lemmas (`mem_zipL_labsJ` needs `cases` on a `Sigma`
  equality) and three statements instead of one.
- E1's `param` case (21 lines) does the same work as E3's `WfB.param` (13 lines), plus a
  `body` case that switches from the continuation-style `closedBlock` to the expression lemma
  (7 lines).

### What fought me

Very little. Everything except one `rename_i` compiled on the first build. The E3 points from
spike A (mutual indexed inductives with reflexive fields, `Labels`/`Args` `@[reducible]`, tuple
patterns `fun (even, odd, ()) => …`) carried over.

- Mutual structural recursion over a mutual inductive *predicate* family with indices
  (`WfB … {n} …`, `WfBs … {sig} …`) works on `nightly-2026-11-08`. It works in term-mode
  `match hwf with`, with `by` blocks per arm and recursive calls under `fun v => …`. No
  hand-written induction principle was needed. `induction` does not support mutual inductives,
  so the three statements have to be written out in full.
- `split` on `match PL with` in `lowerB` substituted `PL` and produced no equation hypothesis
  (`rename_i r PL'`, not `r PL' hPL`).
- Toy instance (both files): numerals at type `toy.Reg` need `(1 : Nat)` annotations
  (`OfNat toy.Reg 1` is not found through the structure projection).
- `rfl` on the toy lowering: labels in the expected code are written `lname k`, not `"L0"`,
  so that `rfl` never has to compute with `String` (not measured with literals).

## Reproduce

```
timeout 900 lake build spike.e3.E1Skel spike.e3.E3Skel   # prints #print axioms for lower_correct
timeout 300 lake env lean spike/e3/E3Skel.lean
```
