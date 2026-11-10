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
