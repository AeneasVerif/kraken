# core: repository setup and the IR

Owner: `core`. Files: `lakefile.toml`, `lean-toolchain`, `.gitignore`, library roots, `scripts/`,
`spike/{e1,a,k}`, `LeanQbe/{Ops,IL,WP,Wf,Print}*.lean`, later `LeanQbe/{Copy,Fold,Gvn}*.lean`.

## C0: skeleton (done)

- Lake package `LeanQbe`, toolchain `leanprover/lean4:nightly-2026-11-08`, `requiresModuleSystem = true`
  (every file starts with `module`), `autoImplicit = false`. Path dependency on the Kraken consumer
  worktree `/usr/local/google/home/andreser/kraken/lean-qbe`.
- Libraries: `LeanQbe` (generic), `LeanQbeAmd64`, `LeanQbeArm64` (roots import their modules),
  `Spike` (glob `spike.+`: every file under `spike/` is built), executable `leanqbe` (stub `Main.lean`).
- `scripts/check.sh`: (1) `lake build --wfail` of all targets; (2) no `sorry` in the build log;
  (3) the closure of the generic root contains no `Kraken.X64*` / `Kraken.AArch64*`, and every file under
  `LeanQbe/` is reachable from its root; (4) axiom audit of `scripts/headline.txt` plus every
  `#print axioms` in the build log; allowed: `propext`, `Classical.choice`, `Quot.sound`.
  Negative-tested: a `sorry`, a user axiom, an x64 import in the generic root and an orphan module each
  make it fail.
- Spikes ported to the new nightly: `spike/e1/E1.lean`, `spike/a/{Core,Examples}.lean`
  (`Examples` now imports `Core` instead of inlining it), `spike/k/SpikeK.lean`,
  `spike/k/SpikeKAArch64.lean`. Breakage from the toolchain: none in the proofs. Module-system
  changes only: `module` headers, `@[expose] public section`, and in `spike/a/Core.lean`
  `public meta import Lean` + `meta partial def nfData` (helpers of an `elab` must be `meta`).
- Timing: full `scripts/check.sh` on a warm Kraken build, about 5 s.

## C1: the IR interface (done, 7c8dc63; review requested)

- `LeanQbe/Ops.lean`: `Val`, `Cls`, `Sz`, `BinOp`, `CmpOp`, `Arg V = var | imm`, pure `Op V`
  (`bin`, `cmp`, `ext`, `copy`), `Op.eval : Op Val → Option Val`; memory on Kraken `Mem 64`:
  `loadVal`, `storeOk`, `storeMem` (definitionally Kraken's `Mem.loadInt` / `Mem.storeInt` at that width).
- `LeanQbe/IL.lean`: E1 `Expr V L` + `load`, `store`, `call f args k`, `exit f args`, multi-result `ret`.
- `LeanQbe/WP.lean`: `wp Γ Q X e args acc m` with callee contracts `Γ : Sym → Spec` (call: `∃ P E` so
  `wp_mono` needs nothing about `Γ`), exit postcondition `X` (D5), `jnz` on `Truthy c := lo32 c ≠ 0`
  (QBE uses the argument at class `w`).
- `LeanQbe/Wf.lean`: `ArgRel`, `OpRel`, `Wf G D e₁ e₂`, `Func.Wf`, tactic `wf_tac`.
- Lemmas: `wp_mono`, `Func.spec_mono`, `closed_param`, `forall_args_nil`, `wp_call_of_spec`, `Wf.weaken`.
- `spike/il/Smoke.lean`: tracer function (wp + Wf), even/odd join points, call + exit example.
- Design choices on request of `logic`: `∃` forms (not `match`) for `Op.wp`, `load`, `storeOk`; user simp set
  then needs `Option.some.injEq, exists_eq_left'`.

## C2: printer (done)

- `LeanQbe/Print.lean`: `Print.fn`, `Print.module` at `V := Nat`, `L := Nat`. Every value at class `l`;
  class-`w` operations computed at `w` (or `l` for `ext`) and zero-extended with `extuw`; block parameters
  through temporaries `%L{ℓ}_p{i}` assigned at the jump (QBE builds SSA from multiply-assigned temps);
  `exit` = `call` + `hlt`; more than one result (ret or call) is rejected (stock QBE has one).
- `scripts/qbe_difftest.sh` + `scripts/QbeDiff.lean`: differential test. 86 one-instruction functions
  (13 binops × 2 classes, 10 comparisons × 2, 8 extensions × 2, copy × 2, 6 with immediates, 16 store/load
  round trips) × 25 test vectors each (pairs for binary ops) where `Op.eval` is defined, plus the smoke
  functions: **38950 results, all equal to `Op.eval`, on amd64 (native) and arm64 (qemu)**. About 15 s.
  First run found one printer bug (QBE rejects `extsw` at class `w`), no semantic mismatch.
- `spike/il/PrintTest.lean`: `#guard` regression of the printed tracer and of the junk rejections.

### C2 follow-ups

- `checker` found that stock QBE amd64 tests all 64 bits in `jnz` when the condition is a 64-bit
  flag-setting op in the same block (upstream bug; QBE's doc says 32). The printer now emits
  `%c =w cnew c, 0` before every `jnz`. Difftest now uses an interpreter oracle (in `scripts/QbeDiff.lean`,
  built from `Op.eval`, `loadVal`, `storeOk`/`storeMem` on a concrete `Mem 64`, `Truthy`), covers `jnz` on
  `add.l`, and runs an `exit` path: 46068 results equal on amd64 and arm64 (25b3206, reproduced by checker).

## Step 2e, part 1: constant folding + copy propagation (done, c2482e9)

- `LeanQbe/Fold.lean` (90 lines): `fold n : Expr (Arg V) L → Expr V L`, read at `V' := Arg V` so that
  substitution is instantiation. Removes constant operations (when defined), `copy.l`, and `jnz` on an
  immediate. `n` = pending labels (statically known): instructions are only removed where `n = 0`, because
  removing one between a `label` and its `block` (junk) would change which block defines which label
  (found while proving; the first version without `n` was not provable).
- `LeanQbe/FoldLemmas.lean` (316 lines, 0.6 s): `fold_wp` (source `wp` ⇒ output `wp`, by induction on
  `Wf` between the `Arg Val` and `Val` instantiations with `Good G`: every input variable denotes an
  operand with the source value), `fold_wf` (`Wf` preserved, for any two instantiations), and
  `Func.fold_spec`, `Func.fold_wf` for closed functions. About 130 lines are operand/operation lemmas
  reusable by the next pass, 110 the `wp` induction, 60 the `Wf` induction.
- `spike/il/FoldTest.lean`: output on a concrete program by `rfl`, its `Wf`, its contract via `fold_spec`.
- Cost / friction: one afternoon hour. The PHOAS pattern itself was cheap; the friction was
  (1) Lean's equation lemmas for a `match` on three discriminants with overlapping patterns timed out in
  `simp only [fold]` (rewrote as `if n = 0 then match …`), (2) `simp only [Arg.val]` turning `.val` into a
  `match` that blocks later rewrites (use definitional `have` instead), (3) name resolution inside
  `theorem Func.x` picking `Func.y` over the root `y`.

## Step 2e, part 2: common-subexpression elimination (done, c146d07)

- `LeanQbe/Gvn.lean` (73 lines): `gvn n next tbl : Expr (Arg V × Key) L → Expr V L`. Input variables carry
  their replacement operand and a key (`Arg Nat`: a counter-assigned name, because variables of an
  arbitrary `V` cannot be compared). The table maps key-level operations to earlier results and is passed
  down the term, so lexical scope = the operations executed on every path to here. Loads, parameters and
  call results get fresh keys. Same pending-label rule as `fold`.
- `LeanQbe/GvnLemmas.lean` (448 lines, under 1 s): `gvn_wp` with the invariant "a valuation `ρ` of the keys
  below the counter; every variable's operand and key evaluate to the source value; every table entry
  evaluates to its operand" (plus "keys below the counter", so extending `ρ` at the counter is harmless);
  `gvn_wf` with "both instantiations compute the same keys and the same table shape"; `Func.gvn_spec`,
  `Func.gvn_wf`.
- `spike/il/GvnTest.lean`: a repeated `add` before and inside a branch is replaced, loads are kept (kernel
  `rfl`), `Wf`, a contract through `gvn_spec`.
- Finding: the elaborator's `rfl` fails on `Func.gvn prog = …` even for a two-instruction program, while
  the kernel accepts it at once (and rejects a wrong right-hand side). The test uses Spike A's
  `kernel_rfl` (hand `Eq.refl` to the kernel). Same pitfall family as Spike A's.

## Step 2e verdict (plan risk 5)

PHOAS-to-PHOAS passes are cheap in Lean for this IR. Both passes went through on the first design except
for one semantic point (junk shapes, see Fold). Effort: about one hour for Fold+Copy, under an hour for
CSE; proof sizes 316 and 448 lines, of which the `wp` and `Wf` inductions are about 170 and 250, and all
proofs check in under a second. What made it cheap: `Wf` as one inductive predicate (induction on it gives
every case with both terms in hand), `wp` monotone without hypotheses, and choosing the input
instantiation (`Arg V`, `Arg V × Key`) so that the analysis result is just the variable. Not done: global
value numbering across join points (needs dominance information at block entries), folding of branches
on values known only through the table.

## Mid-end pipeline (done, 64df075)

`LeanQbe/Opt.lean`: `Func.opt = fold ∘ gvn ∘ fold`; `OptLemmas`: `Func.opt_wf`, `Func.opt_spec` (three lines
each, by composition). Used by rega's `compileFn` (Main.lean) and `compileFn_correct`.

## Plan risk 8: elaboration and checking of large programs

Programs generated by `scratch/scale/gen.py` (in core's brain folder): straight-line chains
`%x_i = op %x_{i-1}, %a` ("sl", every instruction also uses the first parameter, the worst case for
context lookups) and chains of `k` join points with 3 instructions each ("bl", 3k+1 instructions), written
in logic's `qbe` notation, `def prog : Fn`. Times from `-Dprofiler=true`, this machine, one file each.

| program | def elab (macro notation) | def elab (term elaborator, 7b0044b) | codegen | `wf_tac` | `wf_reify` kernel | `lowerFn` kernel |
|---|---|---|---|---|---|---|
| sl 250 | 0.16 s | 0.04 s | 0.05 s | 15 s (+1 s kernel) | 0.16 s | 2.4 s |
| sl 1000 | 1.46 s | 0.39 s | 0.58 s | (minutes, stopped) | 1.6 s | 28 s |
| sl 2000 | 5.2 s | 1.5 s | 2.4 s | | 5.2 s | |
| sl 4000 | 22.9 s | 6.1 s | 10 s | | 26 s | |
| bl 50 (151) | 0.12 s | 0.03 s | 0.05 s | 1.3 s | 0.13 s | 1.9 s |
| bl 250 (751) | 1.05 s | 0.20 s | 0.55 s | | 1.8 s | 32 s |
| bl 1000 (3001) | 12.9 s | 2.8 s | 9.6 s | | 18 s | |

Findings and fixes:

1. **`wf_tac` was quadratic with a large constant** (membership search through a context list at every
   variable). Replaced for real programs by **`wf_reify`** (LeanQbe/Flat.lean, FlatLemmas.lean): a
   first-order mirror `Flat` with de Bruijn levels, `toFlat`, `denote`, and one generic theorem
   `denote_wf` (every denotation is `Wf`). For a concrete `f`, the kernel checks
   `f = fun V L => denote V L (toFlat (f Nat Nat) 0 0) [] 0 [] 0` (via `kernel_rfl`, no elaborator
   `isDefEq`) and `Func.wf_of_reify` concludes. 100× faster at 250 instructions. It is still quadratic
   in the worst case (list lookup by level, the chain references the first parameter from everywhere).
   I tried a binary trie for the contexts: slower (2000: 9.0 s vs 5.2 s), because the kernel evaluates
   the trie insertions lazily and, under binders (open terms), without caching; list `cons` cells are
   already constructors. Reverted; the trie version is kept in scratch.
2. **Definition elaboration** was quadratic in the elaborator itself, also for plain constructor syntax
   (1000 → 1.0 s, 2000 → 3.3 s), so not the notation's fault. A term elaborator that builds the `Expr`
   directly is linear (my 30-line probe: 4000 lets in 16 ms); logic turned the notation into one
   (7b0044b), 4× faster. What remains is Lean's definition pipeline ("process pre-definitions",
   quadratic: 6 s at 4000 even for a directly built term) and code generation (10 s at 4000). Declaring
   the same term with `addDecl` directly takes 0.9 s at 4000 including the kernel check: a `qbe_def`
   command that does this would make big proof-side programs linear (suggested to logic, #129).
   `noncomputable` removes codegen for programs used only in proofs.
3. **`lowerFn` by kernel evaluation** is superlinear (250 → 2.4 s, 1000 → 28 s); reported to rega
   (list-based maps in the oracle and the symbolic register file are the likely cause).
4. Practical guidance today: split programs into Lean-level helpers (as LratRup does), use `wf_reify`,
   `noncomputable def` for proof-only programs, kernel-only `rfl` for big equalities.

## Parsing QBE's own tests (done, e13c812)

- `LeanQbe/Parse.lean`: QBE IL text (integer subset) to `Flat`, and `Parse.toFn` gives a `Fn` whose `Wf`
  is `denote_wf` (no per-program proof). Phis become join-point parameters: every block is a join point
  of one group taking *all* temporaries as parameters, so non-SSA input works too; `$sym` operands become
  calls to an address getter `leanqbe_addr_sym` that the test harness links in C.
- `scripts/qbe_tests.sh` (+ `QbeTests.lean`): parse every `qbe/test/*.ssa`, print with `LeanQbe.Print`,
  compile with stock QBE, link with the test's own C driver, run. **19 of QBE's tests parse and pass**
  (cmp1, conaddr, copy, cup, eucl, fold1, gvn1, gvn2, isel1, isel3, isel4, isel6, ldhoist, loop, philv,
  prime, rega1, spill1, sum); the other 57 are outside the subset (`alloc*`, floating point, aggregates,
  varargs, thread-locals, own data, no driver), each skipped with the reason.
- Next step (needs rega's R3 calls and x64isel's operations): compile the parsed functions with
  `compileFn` instead of stock QBE, for a third opinion on our backend.
