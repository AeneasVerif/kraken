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
