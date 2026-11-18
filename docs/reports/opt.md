# opt: Typed-IR mid-end optimisations (`T6`)

Owner: `opt`. Generic `LeanQbe.T` pass modules (`LeanQbe/T/{Fold,Copy,Gvn,Dce,Opt}*.lean`),
pass tests (`LeanQbeTest/T/{FoldTest,CopyTest,GvnTest,DceTest,OptTest}.lean`), wiring in
`LeanQbe.lean`, and headline audit entries in `scripts/headline.txt`.

## Status

| Deliverable | State |
|---|---|
| `T6.1 Fold` (`Fold.lean`, `FoldLemmas.lean`) | done: deterministic constant eval (`OpCode.eval?`), canonical quiet NaN refinement (`canonNaN`, `isFloatNaN_packedNaN`), total `udiv0`/`sdiv0`, algebraic identities/annihilators/self-rules (`SimpAct`), strength reduction (`mul → shl`, `udiv → lshr`, `urem → and`), static `jnz`; `fold_wp`, `fold_wf`, `Func.fold_wf`, `Func.fold_spec` |
| `T6.2 Copy` (`Copy.lean`, `CopyLemmas.lean`) | done: `OpCode.copy` elimination, `mkpair`/`unpair` projection propagation (`fst`/`snd`), immediate nested pair unpacking (`CVal.ofImm`), `mkpair (fst p) (snd p) → p` identity (`mkpairProjStep`); `copy_wp`, `copy_wf`, `Func.copy_wf`, `Func.copy_spec` |
| `T6.3 Gvn` (`Gvn.lean`, `GvnLemmas.lean`) | done: lexical CSE/GVN over pure `let_` only (never deduplicating `load`/`store`/`call`/`exit`) keyed by `GvnKey := (sig : List Ty) × (rs : List Ty) × OpCode sig rs × Tup (Arg K) sig` with operand-first `gvnKeyDecEq` and 16-bit prime-modulus hash-bucketed trie `GvnTrie` (`GvnTbl.find`/`insert` `@[irreducible]`); `OpCode.wp_self`, `gvn_wp`, `gvn_wf`, `Func.gvn_wf`, `Func.gvn_spec` |
| `T6.4 Dce` (`Dce.lean`, `DceLemmas.lean`) | done: two-phase `O(log N)` bottom-up liveness (`NatTrie` + `List Nat` overflow for `≥ 2^32`, avoiding `WellFounded.fix` so kernel `t_kernel_rfl` scales) and top-down sweep dropping unused pure `let_` only (never `load`/`store`/`call`/`exit`, preserving outer variables live in `group` blocks); `OpCode.wp_exists`, `dce_wp`, `dce_wf`, `Func.dce_wf`, `Func.dce_spec` |
| `T6.5 Opt` (`Opt.lean`, `OptLemmas.lean`) | done: 6-pass `Func.opt f := Func.dce (Func.fold (Func.copy (Func.gvn (Func.copy (Func.fold f)))))` with `Func.opt_wf` and `Func.opt_spec` |
| Tests & Gate | done: `FoldTest`, `CopyTest`, `GvnTest`, `DceTest`, `OptTest` (E1 ports + scalar/multi-result/pair/vector/float-NaN/UB/side-effect/`group`/post-GVN pair/250-insn scaling/`UnionFind` checks with `_out`, `_wf`, `_spec`), all 76 new headline theorems in `scripts/headline.txt`, zero `sorry`/native tactics, `scripts/check.sh` passed |

## Passes and Key Proofs

1. **Constant folding & strength reduction (`LeanQbe/T/Fold.lean`, `LeanQbe/T/FoldLemmas.lean`)**
   - Variables use `FVal V t := Arg V t × FKey t` so constant substitutions, copy replacements, and
     symbolic algebraic rules (e.g. `sub x x → 0`, `xor x x → 0`, `cmp .eq x x → splatMaskVal t true`)
     work over arbitrary PHOAS `V` (`FKey t := Option Nat`).
   - `OpCode.eval?` evaluates deterministic opcodes, picks `canonNaN f` (`packedNaN f.format`) for
     NaN-producing IEEE ops (`evalFloatLeaf1..3_sound` via `isFloatNaN_packedNaN`), evaluates total
     `udiv0`/`sdiv0` at zero, and returns `none` conservatively when guarded ops (`udiv`/`sdiv`/`urem`/
     `srem`/`fptoui`/`fptosi`/`shuf*`) fail their definedness checks.
   - `Op.simpAct` separates pure `let_` elimination into `SimpAct` (`SimpElem.imm | .arg`), completely
     independent of `V`, making `OpRel.simpAct_sound` (for `fold_wp`) and `OpRel.simpAct_eq` (for
     `fold_wf`) share the exact same action table. `Op.rewrite` lowers power-of-two `mul` (scalar and
     non-float vector via `leafPow2Shift?`) to `shl`, `udiv` to `lshr`, and `urem` to `and`.
   - `fold_wp` and `fold_wf` proceed by `Wf.induct`, with `FGood ρ b G` tracking valuation agreement
     for keys `< b` and `FRelG G' G` keeping both PHOAS sides lockstep.

2. **Copy & pair propagation (`LeanQbe/T/Copy.lean`, `LeanQbe/T/CopyLemmas.lean`)**
   - Variables carry `CVal V t` recording output operand `out`, optional lexical identity `id`,
     known components `CParts` (`.unknown | .pair cx cy`), and pair-projection provenance
     `CProjFst`/`CProjSnd`.
   - Eliminates `OpCode.copy`, decomposes constant pairs in `CVal.ofImm` and constant `mkpair`,
     eliminates `unpair` of constructed/immediate pairs (`CParts.pair`), and folds identity pairs
     `mkpair (fst p) (snd p) → p` (`mkpairProjStep`) when `pid` and types agree.
   - `Op.copyLet` is factored cleanly outside `mutual def copy` so Lean generates direct equation
     lemmas; `copy_wp` tracks an `Option (Val t)` projection map `CGoodCtx` via `Wf.induct`, and
     `copy_wf` proves structural agreement (`CRelG`).

3. **Lexical GVN / CSE (`LeanQbe/T/Gvn.lean`, `LeanQbe/T/GvnLemmas.lean`)**
   - Uses `GVal V t := V t × Nat` and `GvnKey := (sig : List Ty) × (rs : List Ty) × OpCode sig rs × Tup (Arg K) sig`
     with structural `DecidableEq` (`listTyDecEq`, derived `OpCode` `DecidableEq`, `tupDecEq argKDecEq`)
     comparing operands (`tupDecEq argKDecEq`) before `OpCode` constructor checks.
   - Lookup/insertion uses a 16-bit prime-modulus hash-bucketed binary trie `GvnTrie`
     (`gvnHash := (tupArgHash args * 131 + opCodeTag code) % 65521`, depth ≤ 16) rather than a flat list,
     with `GvnTbl.find`/`insert` marked `@[irreducible]` so elaborator `Meta.isDefEq` does not hit
     `maxRecDepth` under `apply Func.gvn_spec` while `t_kernel_rfl` scales cleanly (`1.68 s` at 250 ops,
     `7.08 s` at 2000 distinct live ops).
   - Only pure `let_` ops enter `GvnTbl`; `load`, `store`, `call`, `exit` are never deduplicated, while
     lexical `tbl` descends safely into `jnz` branches and `group` block bodies/continuations because
     `OpCode.wp` is memory-independent.
   - Soundness hinges on `OpCode.wp_self`: any satisfied `c.wp args P` witnesses outputs satisfying
     every other valid `Q` (`c.wp args (fun r => P r ∧ ∀ Q, c.wp args Q → Q r)`), handling both
     nondeterministic float NaNs (`floatResultWp_self`, `liftFloatRel1..3_self`, `convertFloat_self`)
     and partial/UB ops without requiring determinism.

4. **Dead-code elimination (`LeanQbe/T/Dce.lean`, `LeanQbe/T/DceLemmas.lean`)**
   - *Plan note (`#78` note 3):* Although the initial plan text wrote "port E1's … DCE", E1 had no
     standalone `Dce.lean` (E1 `Fold` only elided folded/copied definitions), so `T6` implemented
     `LeanQbe/T/Dce.lean` and `LeanQbe/T/DceLemmas.lean` from scratch.
   - `Func.dce` computes `(liveVars as.length (f K KL0 (Tup.levels as 0))).2` once over erased
     `Expr K KL0 rs` using structural `NatTrie` (`< 2^32`, `O(log N)`) + `List Nat` overflow
     (no `WellFounded.fix`), so kernel `t_kernel_rfl` evaluates fast.
   - Drops only unused pure `let_` bindings; cascading dead chains disappear in one bottom-up pass,
     while `load`, `store`, `call`, `exit`, and variables referenced inside `group` block bodies are
     always retained (`liveVarsB_sub`).
   - *Fallback semantics (`Dce.lean:118-121, 183-226`):* `dceSweep` / `dceSweepB` return `.hlt` if
     the `KeepTree` / `KeepBlocks` shape disagrees with the `Expr` / `Blocks` constructor, and
     `argSweep` replaces `.var none` with `.imm default`. Both fallback arms are provably
     unreachable on every `Wf` function because `liveVars` traverses the identical PHOAS skeleton
     and `NoneDead` guarantees no live use ever reads a dropped binder (`dce_wp`, `dce_wf`). In
     differential C++ testing of unverified programs, `PrintCpp` traps on `.hlt` via
     `__builtin_trap()` by default (`revised_architecture_and_plan.md` §2.6) rather than falling
     through silently.
   - `dce_wp` combines `Wf` inversions on `ek ~ e₁` (`Wf.rhs_*`) with `NoneDead s Gk` and `SomeEq G`,
     discharging dropped `let_` via `OpCode.wp_exists` (exhibiting `packedNaN` via `isFloatNaN_packedNaN`
     on float NaN quantifiers and `False.elim` on UB). `dce_wf` tracks `DceRel` lockstep across
     kept/dropped binders using `dceSweepB_liveVarsB_get`.

5. **Pipeline (`LeanQbe/T/Opt.lean`, `LeanQbe/T/OptLemmas.lean`)**
   - `Func.opt f := Func.dce (Func.fold (Func.copy (Func.gvn (Func.copy (Func.fold f)))))` composes
     initial folding, copy/pair propagation, GVN/CSE, post-GVN copy/pair cleanup (catching
     `mkpair (fst p) (snd p) → p` exposed once GVN merges duplicate pair-producing expressions),
     post-CSE algebraic/branch folding, and dead-code elimination.
   - `Func.opt_wf` and `Func.opt_spec` chain the six per-pass `_wf` and `_spec` theorems directly.

## Line Counts vs E1

| Area | E1 files (lines) | T6 files (lines) | Notes |
|---|---:|---:|---|
| Fold | `Fold.lean` 264 + `FoldLemmas.lean` 490 = **754** | `T/Fold.lean` 564 + `T/FoldLemmas.lean` 1966 = **2530** | Covers 64 typed ops, multi-result, pairs, vectors, IEEE floats/NaNs, strength reduction |
| Copy | _(folded inside `Fold`)_ | `T/Copy.lean` 193 + `T/CopyLemmas.lean` 856 = **1049** | Dedicated copy + `mkpair`/`unpair` projection pass |
| Gvn | `Gvn.lean` 73 + `GvnLemmas.lean` 382 = **455** | `T/Gvn.lean` 288 + `T/GvnLemmas.lean` 936 = **1224** | `Sigma`-typed `OpCode` keys, 16-bit `GvnTrie`, `OpCode.wp_self` over all 64 ops |
| Dce | _(none in E1; written new in `T6`, see §4)_ | `T/Dce.lean` 233 + `T/DceLemmas.lean` 1108 = **1341** | Structural `NatTrie` liveness, `OpCode.wp_exists` (NaN & UB), `group` block liveness |
| Opt | `Opt.lean` 22 + `OptLemmas.lean` 25 = **47** | `T/Opt.lean` 31 + `T/OptLemmas.lean` 42 = **73** | 6-pass pipeline `Fold → Copy → Gvn → Copy → Fold → Dce` |
| Tests | `{Fold,Gvn,Opt}Test.lean` = 105 + 53 + 30 = **188** | `T/{Fold,Copy,Gvn,Dce,Opt}Test.lean` = 286 + 203 + 291 + 227 + 197 = **1204** | E1 parity ports plus typed multi-result/pair/vector/float-NaN/UB/effect/`group`/scaling/`UnionFind` tests |

## Verification Results

- **Full quality gate (`timeout 900 bash scripts/check.sh`, post-T5 cherry-pick on `54e9534`)**: **ALL PASSED** (exit code 0):
  - Step 1: `lake build --wfail LeanQbe LeanQbeAmd64 LeanQbeArm64 LeanQbeTest leanqbe leanqbe-arm64` succeeded with zero warnings (after disambiguating `CopyLemmas.lean`'s internal `CGood` → `CopyGood` so `LeanQbe.T.CopyLemmas` and `LeanQbe.T.LegalLemmas` coexist in `LeanQbe.lean`).
  - Step 2 & 2b: zero `sorry`/`sorryAx` and zero `bv_decide`/`native_decide`/`ofReduceBool` across all tracked `.lean` files.
  - Step 3 (import closure): all 10 new `LeanQbe.T.*` modules are reachable from `LeanQbe` with zero `Kraken.X64`/`Kraken.AArch64` imports.
  - Step 4 (axiom audit): **459 / 459** complete one-line `#print axioms` reports in `scripts/headline.txt` (including all 76 `T6` pass and test theorems on top of `T5`'s 383), all strictly within `[propext, Classical.choice, Quot.sound]`.
  - Step 5 (CPU check times): `LegalLemmas.lean` 158 s, `Amd64/IselLemmas.lean` 43 s, `T/FoldLemmas.lean` 40 s, `Amd64/LratBytes.lean` 31 s, `RegaLemmas.lean` 29 s, `Arm64/LratBytes.lean` 29 s, `LratBytesCheckLemmas.lean` 16 s.
- **Native & QEMU suites**: `timeout 300 bash test/run.sh` and `timeout 300 bash test/arm64/run.sh` **ALL PASSED** (`rc=0`).
- **Targeted CPU check times (`timeout 300 lake env lean`)**:
  - Pass proof modules: `T/FoldLemmas.lean` 10.39 s, `T/CopyLemmas.lean` 3.39 s, `T/GvnLemmas.lean` 2.36 s, `T/DceLemmas.lean` 1.51 s, `T/OptLemmas.lean` 0.40 s (all `rc=0`).
  - Test modules: `T/FoldTest.lean` 1.82 s, `T/CopyTest.lean` 1.04 s, `T/GvnTest.lean` 2.32 s, `T/DceTest.lean` 1.33 s, `T/OptTest.lean` 8.17 s (all `rc=0`).
- **Kernel scaling checks (`t_kernel_rfl` / `kernel_rfl` on identical live `add` chains, T6 vs E1 `#78` note 1):**
  - **T6 (`Fold → Copy → Gvn → Copy → Fold → Dce`, 16-bit `GvnTrie` + `NatTrie`):**
    - `250` distinct ops (`Func.opt f = f`): `Func.gvn` 1.68 s, `Func.opt` **6.18 s**.
    - `2000` distinct ops: `Func.fold` 4.29 s, `Func.copy` 2.29 s, `Func.gvn` 7.08 s, `Func.dce` 3.34 s; `(Func.opt f).checkTFlat = true` **39.31 s** (`Func.opt f = f` **119.16 s**).
  - **E1 (`LeanQbe.Func.opt = Fold → Gvn → Fold`, flat-list `Gvn` table) on the same live `add` chain (`kernel_rfl`):**
    - `250` distinct ops: `toFlat (Func.opt f)` **11.36 s**, `Func.opt f = f` **11.63 s** (`1.9×` slower than T6's 6-pass pipeline).
    - `500` distinct ops: `toFlat (Func.opt f)` **43.65 s** (`3.84×` vs 250 ops, quadratic in list-backed `Gvn`).
    - `1000` distinct ops: both `toFlat (Func.opt f)` and `Func.opt f = f` hit the `150 s` timeout (`rc=124`; extrapolates to `~175 s` at 1,000 ops and `~700 s` at 2,000 ops).
    - Summary: T6's trie-backed 6-pass `Func.opt` checks `2,000` ops (`39.31 s`) faster than E1's 3-pass `Func.opt` checks `500` ops (`43.65 s`), and eliminates E1's quadratic `Gvn` blowup.
