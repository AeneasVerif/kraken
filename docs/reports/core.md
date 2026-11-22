> **[Historical design note]** Written during an earlier milestone; several `LeanQbe/*.lean` (E1) and `scripts/headline.txt` paths referenced below have since moved to `LeanQbe/T/` and `scripts/headlines.d/`. See `README.md` for current paths.

# core: repository setup and the IR

Owner: `core`. Files: `lakefile.toml`, `lean-toolchain`, `.gitignore`, library roots, `scripts/`,
`spike/{e1,a,k}`, `LeanQbe/{Ops,IL,WP,Wf,Print}*.lean`, later `LeanQbe/{Copy,Fold,Gvn}*.lean`.

## C0: skeleton (done)

- Lake package `LeanQbe`, toolchain `leanprover/lean4:nightly-2026-11-08`, `requiresModuleSystem = true`
  (every file starts with `module`), `autoImplicit = false`. Path dependency on the Kraken consumer
  worktree (`../kraken/lean-qbe`).
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

Programs generated by `scratch/scale/gen.py` (historical scratch generator): straight-line chains
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
- **Compiled through our own verified `LeanQbe.compile Amd64.isa` pipeline (`Func.opt` + `Spill.hints` + `Rega.lowerFn`)**:
  `Parse.lowerFn` carries only cross-block temporaries as join-point parameters (keeping block-local
  definitions local and function parameters in outer lexical scope). **17 of the 19 parsed QBE tests
  compile through `compile Amd64.isa`, link with QBE's C drivers, and pass natively** (`cmp1`, `conaddr`,
  `copy`, `cup`, `eucl`, `fold1`, `gvn1`, `gvn2`, `isel1`, `isel3`, `isel4`, `ldhoist`, `loop`, `philv`,
  `prime`, `rega1`, `sum`; the other 2 exceed D6 register-parameter arity: `isel6` has 9 call arguments,
  `spill1` has 17 loop phis).

## Algebraic simplifications and strength reductions in `Fold` (done)

Extended `LeanQbe/Fold.lean` (249 lines) and `LeanQbe/FoldLemmas.lean` (580 lines) while keeping
`Func.fold_spec` and `Func.fold_wf` intact (standard 3 axioms, check time ~1 s):

- **Key-carrying PHOAS instantiation (`FVal V = Arg V × FKey`)**: each bound variable carries its
  replacement operand `Arg V` and a symbolic key `FKey = Arg Nat` so that `a.fkey == b.fkey` detects
  equal variables without `DecidableEq V`. Identity eliminations preserve both `.fout` and `.fkey`, so
  equality propagates through chains of simplified operations.
- **Instruction elimination (`Op.simpAct : Op (FVal V) → Option SimpAct`)**:
  - constant folding when all operands are immediate and `Op.eval` is defined;
  - `copy .l a → a` and redundant 64-bit extension `ext .l .l sg a → a`;
  - annihilators at `.w` and `.l`: `mul a 0 → 0`, `mul 0 b → 0`, `and a 0 → 0`, `and 0 b → 0`;
  - self-annihilators at `.w` and `.l`: `sub x x → 0`, `xor x x → 0`;
  - self-identities at `.l`: `and .l x x → x`, `or .l x x → x`;
  - identities at `.l`: `add x 0`, `add 0 x`, `sub x 0`, `mul x 1`, `mul 1 x`, `or x 0`, `or 0 x`,
    `xor x 0`, `xor 0 x`, `and x (-1)`, `and (-1) x`, `shl/shr/sar x 0 → x`;
  - self-comparisons at `.w` and `.l`: `eq/sle/sge/ule/uge x x → 1`, `ne/slt/sgt/ult/ugt x x → 0`.
  Factoring the result through `SimpAct = imm c | fst | snd` (independent of `V`) keeps the `Wf`
  preservation lemma `OpRel.simpAct_eq` a 10-line equality proof and keeps the `.let_` case of `fold_wp`
  and `fold_wf` at two branches regardless of how many rules `binAct`/`cmpAct`/`extAct`/`copyAct` have.
- **Operation rewriting (`Op.rewrite : Op V → Op V`)**:
  - power-of-two multiply strength reduction: `mul x (2^m) → shl x m` and `mul (2^m) x → shl x m`
    at `.l` (`m < 64`) and `.w` (`m < 32`), proved via `BitVec.shiftLeft_eq_mul_twoPow`;
  - class-`w` identity rules (`add.w x 0`, `sub.w x 0`, `mul.w x 1`, `or.w x 0`, `xor.w x 0`,
    `and.w x (-1)`, `shl/shr/sar.w x 0`) → `copy .w x`;
  - redundant 32-bit extensions (`ext .w .w sg a`, `ext .w .l sg a`, `ext .l .w false a`) → `copy .w a`.
- **Tests (`spike/il/FoldTest.lean`)**: `algProg_fold_out` checks by elaborator `rfl` that a 24-instruction
  program exercising every identity, annihilator, self-rule, chained key propagation into `ceql` + `jnz`,
  `mul _ 8 → shl _ 3`, `mul.w 4 _ → shl.w _ 2`, and `extuw → copy.w` folds to 3 instructions.

---

## T1: Typed IR Core and `wp` (`LeanQbe.T`)

Implemented the target-neutral typed IR and relational total-correctness weakest precondition in namespace `LeanQbe.T`, leaving all existing E1 compiler files (`LeanQbe/{Ops,IL,WP,Wf,Flat,Fold,Gvn,Opt,Rega,Abi,Main}*.lean`, `LeanQbe/{Amd64,Arm64}/*.lean`, `LeanQbe/Examples/*.lean`) untouched (`G5`).

- **Types & bit views (`LeanQbe/T/Ty.lean`, `LeanQbe/T/TyLemmas.lean`)**:
  - `Ty := bool | bits n | float f | pair a b`, IEEE format `Fmt := h | s | d | q`, semantic domain `Val : Ty → Type`, low-priority `@[instance_reducible]` `Val.{decEq, inhabited, repr}` (avoiding `--wfail` reducibility warnings and stdlib instance shadowing), balanced `2^k`-lane trees `Ty.vec k t` (`v4i32`, `v8i32`, `v2i64`, `v4f32`), `Ty.mask`, `Ty.size`, `Ty.bytes`, `toBits`/`ofBits`, `bitcastVal`, `lane`, and right-nested `Unit`-terminated `Tup` + `Member`/`TRel`/`EnvRel`.
  - Round-trip and layout lemmas: `Ty.vec_size`, `Ty.hasFloat_vec`, `Ty.isFloatTree_vec`, `Ty.bswapOk_vec`, `Ty.size_le_eight_bytes`, `setWidth_bytes_size`, `ofBits_toBits`, `toBits_ofBits`, `toBits_inj`, `ofBits_inj`, `bitcastVal_self`, `bitcastVal_bitcastVal`, `Tup.get_map`, `TRel.mono`, `envRel_toTup`.
- **Operations & partial memory (`LeanQbe/T/Ops.lean`, `LeanQbe/T/OpsLemmas.lean`)**:
  - 64-constructor multi-result `OpCode sig rs` covering all §0 scalar, multi-result (`addc`, `subb`, `umulw`, `smulw`), comparison/select/blend, pair/bitcast, shuffle/align/blendw (`shufd`, `shufb`, `alignr`, `blendw`), SHA-256 (`sha256rnds2`, `sha256msg1`, `sha256msg2`), and IEEE float ops (`fadd`, `fsub`, `fmul`, `fdiv`, `ffma`, `fsqrt`, `fneg`, `fabs`, `fcmp`, `fptoui`, `fptosi`, `uitofp`, `sitofp`, `fcvt`), plus semantics-only ops (`ternlog`, `fshl`, `fshr`, `clz`, `cls`, `rbit`, `ctz`, `popcnt`, `udiv`/`sdiv`/`urem`/`srem`, `udiv0`/`sdiv0`, `rotl`, `rotr`, `bswap`, `ofBool`).
  - Variant C parameters `(m : Ty := t.mask) (h : m = t.mask := by rfl)` on `cmp`, `blend`, and `fcmp` so `deriving DecidableEq` succeeds on both `OpCode` and `(sig : List Ty) × (rs : List Ty) × OpCode sig rs`.
  - Relational `OpCode.wp` (`UB = False`, NaN payloads universally quantified `∀ r, isFloatNaN f r = true → k r` via Lean's `Float.Model`, leaf-wise vector/pair lifting) and partial byte memory (`loadVal`, `storeOk`, `storeMem`) over `Kraken.Mem 64`.
  - `OpsLemmas`: `OpCode.wp_mono`, `Op.wp_mono`, `isFloatNaN_packedNaN`, all 64 `@[simp]` `OpCode.wp_<ctor>` tuple-argument rewrite lemmas (avoiding 64-way pattern-matcher unfolding blowup under nested `let_` binders), arithmetic carry/borrow/mul lemmas (`addc_toNat`, `subb_toNat`, `umulw_toNat`), `lane_lift1`/`2`, `loadInt_empty`, `storeOk_empty`, `loadVal_storeMem`, partial-overlap unmapped lemmas (`loadBytes_eq_none_of_unmapped`, `loadVal_of_unmapped`, `not_storeOk_of_unmapped`), disjoint-address frame preservation (`loadBytes_storeInt_disjoint`, `loadVal_storeMem_disjoint`, `storeOk_storeMem_disjoint`), and `storeOk_storeMem`.
- **Typed IL & `wp` (`LeanQbe/T/IL.lean`, `LeanQbe/T/WP.lean`, `LeanQbe/T/WPLemmas.lean`)**:
  - Spike-2 head-bound `Tup` binders and mutual `Expr`/`Blocks` with `group`, `load`, `store`, signature-indexed `call`, `exit` (D5), `hlt`, `Func`, `Fn`, `Blocks.get`, and `loop1`.
  - Total-correctness `wp`, `Closed`, `Func.wp`/`Func.spec`, `Expr.induct`, `closed_iff`, `wp_mono` (via `induction e using Expr.induct`), `Spec.Mono`, `Func.spec_mono`, `wp_env_mono`, `Func.spec_env_mono`, `wp_loop`, `wp_loop1`, `wp_join`, `wp_let`, `wp_let_op1..3`, `wp_call_of_spec`/`wp_call_ret1`, and `wp_addc`/`wp_subb`/`wp_umulw`.
  - Re-exported from `LeanQbe.lean` with no `Kraken.X64` or `Kraken.AArch64` imports.
- **Tests (`LeanQbeTest/T/Examples.lean`, `LeanQbeTest/T/Smoke.lean`)**:
  - Ported all 8 spike-4 programs (`add128`, `addLimbs`/`add256`, `mac`, `ult128`, `umin`, `mulByAdd`, `qrStep`, `vumin`) with 12 proved theorems (`add128_spec`, `wp_addLimbs`, `add256_spec`, `mac_spec`, `ult128_spec`, `umin_spec`, `mulByAdd_spec`, `qrStep_spec`, `add_v8_split`, `blend_ult_min`, `vumin_spec`, `bitcast_v4i32_u128`).
  - Added 57 smoke and edge-case theorems in `LeanQbeTest.T.Smoke` covering mutual groups (`evenOdd_correct`, `sumLanes_correct`), partial memory round-trip, empty/partial-overlap UB, and disjoint-address frame preservation (`tracer_correct`, `tracer_unmapped_false`, `partial_unmapped_store_false`, `partial_unmapped_load_false`, `store_disjoint_load_preserves`), signature-indexed `call`/`exit` (`caller_correct`), non-vacuity (`spin_false`), div/rem UB vs AArch64 `udiv0`/`sdiv0`, full IEEE float ops (`fadd`/`fsub`/`fmul`/`fdiv`/`ffma`/`fsqrt`/`fneg`/`fabs`/`fcmp`/`fptoui`/`fptosi`/`uitofp`/`sitofp`/`fcvt`) including quantified NaNs and conversions/overflows, `ternlog`, `shufd`/`shufb`/`alignr`/`blendw`, non-zero FIPS SHA-256 vectors (`sha256rnds2_fips`, `sha256msg1_concrete`, `sha256msg2_concrete`), bit-manipulation/shift ops, `smulw`, and `DecidableEq` (including `cmp`, `fcmp`, `blend`, `bitcast`).
- **Gate & Axiom Checks (`scripts/check.sh`, `scripts/headline.txt`)**:
  - Added 46 `T1` headline theorems to `scripts/headline.txt` (under `LeanQbe.T.WPLemmas`, `LeanQbeTest.T.Examples`, and `LeanQbeTest.T.Smoke`).
  - `bash scripts/check.sh`: passes under `--wfail`, zero `sorry`, zero native-code axioms, clean import closures, `179 complete reports for 179 headline theorems` strictly within `[propext, Classical.choice, Quot.sound]`, `== check.sh: ALL PASSED`.

---

## T2: Relational `Wf`, `Wf.induct`, and Computable `TFlat` Reification (`LeanQbe.T`)

Implemented parametric well-formedness (`Wf` / `WfB`), dependent one-motive induction (`Wf.induct`), and total computable de Bruijn reification (`TFlat` / `TBlocks`) for `LeanQbe.T`, leaving all E1 files untouched (`G5`) and importing neither `Kraken.X64` nor `Kraken.AArch64` in `LeanQbe.lean`.

### 1. Opportunistic `T1` Review `#18` Cleanups

- **`LeanQbe/T/Ty.lean`**: Documented bit-packed pair layout on `Ty.size`, `Ty.bytes`, `toBits`, and `ofBits` (no inter-field padding; first pair component in low bits; `bytes = ⌈t.size / 8⌉`; e.g., `.pair .bool i8` has `size = 9`, `bytes = 2`, with the `i8` straddling bits `1..8` across the byte 0 / byte 1 boundary).
- **`LeanQbe/T/Ops.lean`, `LeanQbe/T/OpsLemmas.lean`, `LeanQbeTest/T/Smoke.lean`**:
  - Documented `FCmpOp` ordering (`.eq`, `.lt`, `.le`, `.gt`, `.ge` ordered, `false` on NaN; `.ne` unordered-or-not-equal matching IEEE/C `!=`), `fptoui`/`fptosi` out-of-range UB (`False` on NaN, `±∞`, or out-of-range truncated integer), and `zext`/`sext`/`trunc` width direction requirements.
  - Enforced `m ≤ n` on `.zext`/`.sext` and `n ≤ m` on `.trunc` in `OpCode.wp` (wrong-direction casts are now UB `False`; updated `OpCode.wp_mono` and `@[simp]` lemmas `OpCode.wp_{zext,sext,trunc}`).
  - Enforced `.bool` load byte ∈ `{0, 1}` in `loadVal` (returns `none`, i.e., UB, for any byte `> 1`), proved `loadVal_bool_invalid`, and updated `loadVal_storeMem` and `sumLanes_correct`. Added regression tests `ext_trunc_wrong_direction_ub`, `load_bool_invalid_byte_ub`, `store_load_bool_roundtrip`, and `fcmp_ne_nan_unordered_true` in `LeanQbeTest/T/Smoke.lean`.

### 2. Well-Formedness and `Wf.induct` (`LeanQbe/T/Wf.lean`, `LeanQbe/T/WfLemmas.lean`)

- **Relational definitions (`LeanQbe/T/Wf.lean`)**:
  - `ArgRel G t a₁ a₂` (paired variable in `G : Ctx V₁ V₂`, or equal immediate `Val t`), `OpRel G op₁ op₂` (equal `OpCode` and `TRel (ArgRel G)` operands), mutual `Wf G D e₁ e₂` / `WfB G D bs₁ bs₂` matching spike-2 head-bound `Tup` binders (`Tup.zip xs₁ xs₂ ++ G` for `let_` / `call` / block params; `⟨t, v₁, v₂⟩ :: G` for `load`; `Tup.zip Js₁ Js₂ ++ D` for `group`), `Func.Wf`, `Fn.Wf`, and syntax-directed `t_wf_tac` (using `TRel.nil'`/`TRel.cons'` and `Tup.zip` simplification so all `Examples` and `Smoke` functions including symbolic `vumin k` discharge with zero warnings).
- **Lemmas and dependent induction (`LeanQbe/T/WfLemmas.lean`)**:
  - Positional block projection `WfB.get` and reconstruction `WfB.of_get` (so inductive motives only need a single block-body expression case rather than a second `WfB` motive).
  - Dependent one-motive `Wf.induct` / `WfB.induct_get` (usable via `induction hwf using Wf.induct`) mirroring `Typed2.lean`, exposing derivations and sub-derivations for downstream `T5`/`T6` passes.
  - Context weakening and congruence (`ArgRel.weaken`, `TRel.argRel_weaken`, `OpRel.weaken`, `Wf.weaken`, `WfB.weaken`, `Wf.weaken_G`, `Wf.weaken_D`, `Wf.cons_G`, `Wf.append_G`, `Wf.append_D`, `Wf.congr`, `WfB.congr`), tuple/op mapping (`TRel.cons_iff`, `TRel.map`, `ArgRel.mapV`, `OpRel.mapV`), symmetry (`Ctx.flip`, `Wf.symm`, `WfB.symm`, `Func.Wf.refl`), and inversion helpers (`Wf.{let,load,store,call,jnz,group,jump,ret,exit}_inv`, `WfB.cons_inv`, `ArgRel.{var,imm}_iff`, `OpRel.mk_iff`).

### 3. First-Order Mirror and Computable Reification (`LeanQbe/T/Flat.lean`, `LeanQbe/T/FlatLemmas.lean`)

- **`TFlat` / `TBlocks` & reification (`LeanQbe/T/Flat.lean`)**:
  - `TFlat rs` / `TBlocks rs sig`: typed first-order AST with de Bruijn *indices* (`0` = newest bound variable/label) using `K := fun _ => Nat`, `KL := fun _ => Nat`.
  - Total `toTFlat` / `toTBlocks` converts de Bruijn levels `(nv, nl)` into indices via `if lvl < nv then nv - 1 - lvl else nv` (and `if j < nl then nl - 1 - j else nl`), ensuring out-of-scope levels cannot alias valid index `0` via `Nat` truncation.
  - `denote` / `denoteB` interprets `TFlat` back into `Expr V L rs` for arbitrary `V L`, checking bounds (`listGet?`) and type equality (`tyDecEq`/`listTyDecEq`, `castTy`/`castListTy`), mapping any out-of-scope or ill-typed reference to `.hlt`.
  - Total computable `TFlat.wfCheck` / `TBlocks.wfCheck` / `Func.checkTFlat` checks in-scope well-typedness in `Bool` (via `tyDecEq`/`listTyDecEq`), and `TFlat.noHlt` / `TBlocks.noHlt` checks absence of explicit `.hlt` nodes.
- **Soundness & tactics (`LeanQbe/T/FlatLemmas.lean`)**:
  - `denote_wf` / `denoteB_wf` (`denote` across related environments `CtxRel G vs₁ vs₂` and `CtxRel D ls₁ ls₂` is always `Wf G D`-related, even when `.hlt` fallback fires), `Func.wf_of_denote`, `Func.wf_of_reify`, and full soundness of `wfCheck` (`lookupV_isSome_of_check`, `lookupL_isSome_of_check`, `denoteArg_isSome_of_checkArg`, `denoteArgs_isSome_of_checkArgs`, `denote_noHlt_of_wfCheck`, `denoteB_noHlt_of_wfCheck`, `Func.denote_noHlt_of_check`, proving `Expr.NoHlt` holds at every instantiation when `wfCheck = true` and `noHlt = true`).
  - Kernel-only `Eq.refl` tactic `t_kernel_rfl` and `t_wf_reify` (`refine Func.wf_of_reify ?_; t_kernel_rfl`), named with `t_` prefix so importing both `LeanQbe.FlatLemmas` and `LeanQbe.T.FlatLemmas` in `LeanQbe.lean` causes no syntax collision.
  - Note on `Ty.vec k`: symbolic `k : Nat` blocks kernel `rfl` inside `tyDecEq`/`castTy` (as in `vumin (k : Nat)`), whereas any concrete `k` (`0`, `2`, `3`) succeeds with `t_wf_reify`; parametric `vumin_wf (k : Nat)` is proved directly via `t_wf_tac` in `ReifyTest.lean`.

### 4. Tests and Scaling Benchmarks vs E1 (`LeanQbeTest/T/{ReifyTest,ScaleTest}.lean`)

- **`LeanQbeTest/T/ReifyTest.lean`**: `t_wf_reify` on all 8 spike-4 programs (`add128`, `add256`, `mac`, `ult128`, `umin`, `mulByAdd`, `qrStep`, and `vumin` at `k = 0, 2, 3`, plus parametric `∀ k, Func.Wf (vumin k)` via `t_wf_tac`), all 6 closed functions in `Smoke.lean` (`evenOdd`, `sumLanes`, `tracer`, `storeThenLoadOther`, `caller`, `spin`), direct `Func.wf_of_reify rfl`, `Func.checkTFlat ... = true`, `Func.denote_noHlt_of_check` soundness tests, negative tests (`oobRawExpr`, `illTypedTFlat` failing `wfCheck` and `Expr.NoHlt` while still satisfying `denote_wf`), and `Wf.induct` / `Wf.weaken` checks.
- **`LeanQbeTest/T/ScaleTest.lean`**: Kernel `t_wf_reify` and `Func.checkTFlat ... = true` checks for `sl 250`, `sl 1000`, `sl 2000`, and `bl 50` (50-block `group`, 151 instructions).

Benchmark comparison on literal straight-line chains (`sl 250/1000/2000`, using both previous result and first parameter `%a`) and 50-block `group` (`bl 50`), profiled with `-Dprofiler=true` on literal `noncomputable def` constructor terms (`set_option maxRecDepth 16384 maxHeartbeats 4000000`) alongside live E1 constructor terms (`wf_reify`) and E1's historical baseline above (`T3` has not yet introduced its direct `Expr` term elaborator):

| Program | T2 total elab (`process pre-def`) | E1 live elab (`process pre-def` / hist. macro) | T2 `t_wf_reify` kernel (`checkTFlat`) | E1 live `wf_reify` (hist.) | T2 / E1 kernel ratio (live / hist.) | Notes (`>2×` flagged) |
|---|---|---|---|---|---|---|
| `sl 250` | `0.990 s` (`0.126 s`) | `0.120 s` (`0.029 s` / `0.16 s`) | `0.371 s` (`0.252 s`) | `0.166 s` (`0.16 s`) | **`2.23×`** / **`2.32×`** | Kernel **`>2×`** (`2.23×` live); total elab **`8.25×` vs live** (`6.19×` vs macro) |
| `sl 1000` | `7.04 s` (`1.88 s`) | `0.948 s` (`0.403 s` / `1.46 s`) | `2.22 s` (`1.76 s`) | `1.42 s` (`1.6 s`) | `1.56×` / `1.39×` | Kernel within `2×`; total elab **`7.43×` vs live** (`4.82×` vs macro) |
| `sl 2000` | `27.3 s` (`7.78 s`) | `3.20 s` (`1.62 s` / `5.2 s`) | `6.67 s` (`5.43 s`) | `4.99 s` (`5.2 s`) | `1.34×` / `1.28×` | Kernel within `2×`; total elab **`8.53×` vs live** (`5.25×` vs macro) |
| `bl 50 (151)` | `0.636 s` (`0.019 s`) | `0.096 s` (`0.011 s` / `0.12 s`) | `0.243 s` (`~0.10 s`) | `0.125 s` (`0.13 s`) | `1.94×` / `1.87×` | Kernel borderline `<2×` (`1.94×`); total elab **`6.63×` vs live** (`5.30×` vs macro) |

Key scaling findings and guidance for `T3`:

1. **Rejected `TFlat` designs**:
   - Intrinsically typed `Member`-indexed `TFlat rs Γ Δ`: `0.625 s` at `sl 250` and **`8.63 s` at `sl 1000` (`6.0×` E1)** due to `O(N^2)` context/index AST terms.
   - Skew-binary random-access list (`RList`) contexts: `0.576 s` / `2.97 s` / `7.1 s` at `sl 250/1000/2000`, slower than `List` because open-binder evaluation does not cache `rCons` reductions.
   - Storing de Bruijn *levels* inside `TFlat` (`n - 1 - i` subtraction during `denote`): `0.382 s` / `2.59 s` / `8.58 s` / `0.265 s` (`sl 250/1000/2000`/`bl 50`), slower than pre-converting to de Bruijn indices in `toTFlat`.
2. **Literal `def` elaboration (`6.6×`–`8.5×` total elab / `4.3×`–`4.8×` `process pre-def`, flagged `>2×`)**: Before `T3` introduces a direct `qbe` term elaborator, plain constructor `def`s spend `27.3 s` total elaboration (`7.78 s` `process pre-definitions`) at `sl 2000` due to dependent `Expr` constructors, `Op.mk` sigma indices, `op2` unfolding, and pattern-matching `fun (x, ()) =>` lambdas. Switching literal terms to `.1` projections + explicit `⟨code, args⟩` cuts `sl 2000` total elab from `27.3 s` to `17.8 s` (`process pre-definitions` `5.26 s`), while `T3`'s direct term elaborator (like E1's `7b0044b`) is expected to drop term elaboration to milliseconds.
3. **Codegen `LCNF base` blowup (`>2×`, flagged)**: Compiling literal non-`noncomputable` functions written with pattern-matching lambdas `fun (x, ()) => ...` took `0.46 s` (`sl 250`), `9.02–13.4 s` (`sl 1000`), and timed out (`>120 s`) at `sl 2000` (vs E1 `0.05 s`/`0.58 s`/`2.4 s`), because Lean's LCNF base compiler performs nested `Prod`/`PUnit` `cases` analysis (`O(N^2)`). Switching the continuation binder to projection syntax `fun p => ... p.1` cut `LCNF base` at `sl 1000` by `40×` to `0.335 s` (`LCNF mono` `1.14 s`; vs E1 `0.108 s` / `0.450 s`), and `noncomputable def` removes codegen completely (`0 ms`). **Recommendation for `T3` (`Notation.lean`)**: desugar typed binders directly as `fun p =>` with `.1` projections and explicit `{sig}` `Op.mk` in a term elaborator rather than `fun (x, ()) =>` pattern-matching lambdas, and prefer `noncomputable def` for proof-only programs.
