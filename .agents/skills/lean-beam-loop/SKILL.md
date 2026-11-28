---
name: lean-beam-loop
description: >-
  Default interactive single-file Lean 4 proof loop via scripts/beam_bounded.sh.
  Use for single-file WP proof development and tactic repair (diag, goals,
  run-at --stdin), and follow its mandatory stop rules before build_bounded.sh
  or audit_axioms.
---

# Lean Beam Proof Loop

Use `scripts/beam_bounded.sh` for **single-file interactive proof iteration**
instead of repeated cold `lake env lean` or `scripts/build_bounded.sh` calls.
It keeps one persistent `lean --server` + file worker inside a bounded
`systemd` unit (`leanqbe-builds.slice`, `MemoryMax=24G`) and isolates session
state under `/tmp/lean-beam-$USER/<hash>` so the worktree stays clean.

## `beam_bounded.sh` vs `build_bounded.sh`

| Task | Tool | Why |
| --- | --- | --- |
| Single-file WP proof / tactic iteration | `scripts/beam_bounded.sh` | Warm worker (~1-22 ms `goals`/`run-at`, ~200 ms re-`sync`) |
| Missing dependency `.olean`s / cold build | `scripts/build_bounded.sh` | Builds upstream `.olean`s with bounded threads & RAM |
| Multi-file signature/import refactors | `scripts/build_bounded.sh` | Cross-module rebuilds without stale import state |
| Final `--wfail`, `audit_axioms`, `check.sh` | `scripts/build_bounded.sh` (after `stop`) | Full compiler warnings, termination & axiom checks |

## Single-File Inner Loop

All `diag`, `goals`, `run-at`, `sync`, and `hover` calls **auto-start** the
daemon if it is not running yet. Always pass the `version` printed by the latest
`diag` or `sync` to subsequent `goals` / `run-at` / `hover` probes.

1. **Sync & read compact diagnostics** (`1-based` `file:line:col`, capped cleanly):
   ```bash
   scripts/beam_bounded.sh diag <file.lean>
   # -> <file.lean>:142:4 [error]: ...
   # -> diag: <file.lean> (version=1, save_ready=false): 1 error(s), 0 warning(s)
   ```

2. **Inspect goals before editing** (`0-based` `line0` and UTF-16 `col0`! Subtract `1` from `diag` line/col):
   ```bash
   scripts/beam_bounded.sh goals before <file.lean> <version> <line0> <col0>
   scripts/beam_bounded.sh goals after <file.lean> <version> <line0> <col0>
   ```

3. **Probe candidate tactics with `run-at --stdin` BEFORE editing the file:**
   Prefer `run-at --stdin` over trial-and-error disk edits! Probes run in an
   isolated elaboration state without touching disk or re-elaborating the whole file:
   ```bash
   scripts/beam_bounded.sh run-at <file.lean> <version> <line0> <col0> --stdin <<'EOF'
   simp only [wp_let_op2, wp_ret]
   omega
   EOF
   ```
   - Check `result.success == true` and `result.proof_state.goals == []` (or inspect remaining subgoals).
   - **Position rules:**
     - Probe at a tactic's first character after indentation to test replacing it (`before`-state).
     - At `sorry`, `_`, or `?x`, the probe runs directly against that placeholder's goal.
     - Probe text's first line starts at column `0`; align sibling tactics at column `0` and indent sub-blocks (`· ...`, `have ... := by`) normally.
     - Empty lines accept only `col0 = 0`.
   - Use `scripts/beam_bounded.sh hover <file.lean> <version> <line0> <col0>` for quick type/docstring checks.

4. **Commit probe to disk & re-`diag`:**
   Once a probe succeeds (`result.proof_state.goals == []`), edit `<file.lean>` on
   disk and run `scripts/beam_bounded.sh diag <file.lean>` to confirm
   `0 error(s), 0 warning(s)`, `save_ready=true`, and pick up the new `version`.

## Mandatory Stop & Final Gate Rules

- **NEVER run `lake build`, `scripts/build_bounded.sh`, or `scripts/check.sh` while `lean-beam` is active.** Concurrent Lake builds race with `beam-daemon` file workers on `.olean` traces.
- **ALWAYS run `scripts/beam_bounded.sh stop` before:**
  1. Final `scripts/build_bounded.sh <target>` (`--wfail` is enabled by default)
  2. `audit_axioms` verification and `scripts/preflight.sh` / `scripts/check.sh`
  3. Committing or posting `[done]`
- Confirm `git status --porcelain` has `0` `.beam/` leftovers after `stop`.
- `save_ready=true` and `run-at` success are **not** a substitute for final `scripts/build_bounded.sh` + `audit_axioms` (probes do not run whole-declaration termination or axiom checks, and `--wfail` catches warnings).
