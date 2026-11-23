> **[Historical design note]** Written during an earlier milestone (at commit `373db35`); the pipeline and certificate infrastructure (`MainLink`, `MainCert*`, `LinkRec`, `LinkScc`) have since expanded. See `LeanQbe-README.md` for current paths and pipeline order.

# Generic PHOAS Compiler Driver, Module Linking, & Kernel Certificate Harness

Snapshot from commit `373db35`, covering `LeanQbe/T/Main.lean`, `LeanQbe/T/MainLemmas.lean`, and `LeanQbeTest/T/MainTest.lean`.

## 1. Architecture & Deliverables

| File | LOC | Contents |
|---|---:|---|
| `LeanQbe/T/Main.lean` | 243 | `Fn.opt`, `Fn.mid` (`opt → legal lt → opt`), `Fn.computeHints` (meta/CLI only), `Expr.extAux`/`Blocks.extAux`/`Fn.ext`, `compileFn`, `compile`, `lookupBound` (keyed by legalized `SigEntry` via `SigEntry.beq`), `lookupFnBound`, `calleesBound`, `checkAndBoundExt`/`Mid`/`checkAndBound`, callee-first `compileModule`, `fnNameOk`, `listNodupBEq` (`:= Rega.listNodup`), `stringsNodup`, `labelsNodupBy`, `checkCompileResult`, `checkCompileResultWithLabels`, `@[irreducible] extractCode extractBounds` |
| `LeanQbe/T/MainLemmas.lean` | 1,184 | `fnSpec_of_spec` (`private`, avoiding collision with `AbiLemmas.Target.FnSpec.of_spec`), `encodeTup_eq_cast_of_legalSig_eq`, `fnSpec_of_legalEnv_legalSig_eq` / `_noExit`, `lname_ne_cross` & `lname_inj_cross` (bridging `Rega.LabelClean` + `fnNameOk` + `stringsNodup`/`checkNamesNodup` directly to `T.LabelsUnique host`), `compileFn_correct` / `_iso`, `compile_sound` (over `Module.checkAcyclic = true`), `TargetLayout` (`TargetLayout.ofClean` + `labelsNodup` option), `Compiled` (`fnSpec`, `fnSpec_host`, `fnSpec_host_src`), `checkCompile` / `compileChecked` (+ `WithLabels` variant), `@[irreducible] stackZeros`, `TargetInit` (`run_fnSpec`, `run_ret1`, `run_ret1_i64`, `run_ret1_sep`, `run_ret1_sep_i64`), and `meta section` command elaborator `splice_module_hints` (`Lean.ToExpr` + `unsafe evalExpr`) |
| `LeanQbeTest/T/MainTest.lean` | 592 | `litmusLabelClean : Rega.LabelClean litmusTarget.toIsa`, `litmusLayout` (`ofClean`) & `litmusLayoutWithLabels` (`progLabelsOk`), `litmusInit : TargetInit litmusTarget` (polymorphic `setAbiRegs` over all legal `as : List Ty` + contiguous `stackZeros` / `raBytes` / `bs` with `sp0 = 0x0ff8#64`), 2-function caller+callee module `litmusMod` (`fnModInc` + `fnModCaller`), `checkAcyclic = true` by `rfl`, `splice_module_hints`, `checkCompile = true` & `checkCompileWithLabels = true` by `t_kernel_rfl`, `Compiled.fnSpec_host_src`, and concrete `TargetInit.run_ret1` / `run_ret1_i64` / `run_ret1_sep_i64` witnesses |

## 2. Key Design Points

* **Zero Untyped-IR / Arch Dependencies:** Verified via `env.header.moduleNames` transitive closure checks over both `LeanQbe.T.MainLemmas` and `LeanQbeTest.T.MainTest`: zero `Kraken.X64`/`AArch64`, `LeanQbe.T.{Amd64,Arm64}.*`, or earlier untyped-IR `LeanQbe.*` imports.
* **Cross-Function Label Hygiene Without O(L²) Scan:** `fnNameOk` rejects `".L"` substrings, giving structural disjointness (`lname_ne_cross`, `lname_inj_cross`) so `checkCompile` only checks `fnNames.all fnNameOk`, `exits.all fnNameOk`, and `stringsNodup (fnNames ++ exits)`. Targets supplying explicit `labelsNodup` can alternatively use `checkCompileWithLabels` / `compileCheckedWithLabels`.
* **Kernel `whnf` Separation:** `legalEnv_elim_mid` and `mid_pipeline_spec` separate `Eq.ndrec` elimination on `has : lt.legalSig f.as = f.as` / `hbs : lt.legalSig f.rs = f.rs` from `Func.opt` / `Func.legal` pipeline lemmas, avoiding kernel `whnf` expansion across optimization passes inside `compileFn_correct`.
* **Untrusted `splice_module_hints`:** Uses `Lean.ToExpr` + `unsafe evalExpr Lean.Expr (mkConst \`\`Lean.Expr)` inside `meta section` ONLY, emitting a safe kernel literal definition so `compileModule` / `checkCompile` remain purely kernel-checked.
* **Co-Import Compatibility & Deduplication:** Alongside `Target.FnSpec.of_spec` in
  `LeanQbe/T/AbiLemmas.lean`, the local helper in `MainLemmas.lean` is named
  `private theorem fnSpec_of_spec`; and `Main.lean` / `MainLemmas.lean` reuse
  `Rega.listNodup` and `Rega.listNodup_nodup` directly (`listNodupBEq := Rega.listNodup`).

## 3. Verification Results

* **`lake build --wfail LeanQbe.T.Main LeanQbe.T.MainLemmas LeanQbeTest.T.MainTest`:** passed (120 jobs, exit 0, `-DwarningAsError=true` clean).
* **Standalone `-DwarningAsError=true` timings (`lake env lean -DwarningAsError=true <file>`):**
  * `LeanQbe/T/Main.lean` (243 LOC): real **0.40s** (user 0.37s, sys 0.14s), exit 0
  * `LeanQbe/T/MainLemmas.lean` (1,184 LOC): real **10.31s** (user 21.30s, sys 0.49s), exit 0
  * `LeanQbeTest/T/MainTest.lean` (592 LOC): real **6.40s** (user 8.85s, sys 0.51s), exit 0
* **Axioms (`#print axioms` in `LeanQbeTest/T/MainTest.lean`, single-line outputs):**
  * `litmusLabelClean`, `litmus_check`, `litmusInc_fnSpec`, `litmusCaller_fnSpec`, `litmusCaller_fnSpec_withLabels`, `litmusCaller_run_ret1`, `litmusCaller_run_i64`, `litmusCaller_run_sep`, `LeanQbe.T.compileFn_correct`, `LeanQbe.T.compile_sound`: all `[propext, Classical.choice, Quot.sound]`.
  * Zero `sorry`, zero `bv_decide`/`native_decide`/`ofReduceBool`/`ofReduceNat`.
