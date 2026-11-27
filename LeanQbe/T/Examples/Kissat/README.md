# Kissat 4.0.4 Verified C0 Solver — Upstream-Mirrored Source Layout (`Src/`)

This directory contains the flat, data-pure C0 source modules of the formally verified Kissat
4.0.4 SAT solver (`LeanQbe.T.Examples.Kissat.Src`), organized 1:1 with upstream
`kissat/src/*.c`.

## Architecture (`40` Upstream C0 Files + `Header.lean` + `Full.lean`)

- **`Src/Header.lean`** (`internal.h`, `kissat.h`): Single shared C0 header registered via
  `c0_header! "kissat_internal.h"` containing `KissatDimacs` (32 B), `FullHdr` (1,152 B),
  `M6HdrExt` (2,304 B), `FullM6Hdr` (3,456 B), compile-time `_Static_assert` layout checks,
  all `196` unanimous shared `#define` constants (with unified `FL_BONE0 = 128u` and
  `FL_BONE1 = 256u`), and the scoped `kissat_c0!` / `kissat_wf_reify` helpers.
  - Note: the sole pass-local macro variant (`KM_CORE`: `0x20000000u` in `full_k6_core_m7` /
    `full_bve_def_k6_m7` vs `0x80000000u` in `full_k6_core_fid` /
    `full_k6_extract_and_solve_fid`) is kept local in `Src/Definition.lean` (`KM_CORE_M7` vs
    `KM_CORE_FID`) so every compiled `LeanQbe.T.Func` AST stays bit-for-bit identical.
- **`Src/<Upstream>.lean` (`40` files, `410` live functions, `16,140` C0 LOC):** Every file
  uses `#include "kissat_internal.h"`, keeps the Pass-1 (`R2`) C0 function symbol names so
  `R3` proof migration ports all `410` WP proofs verbatim (clean upstream `kissat_*` names
  follow mechanically in `R4`), and proves per-function `Func.Wf` (`fns_wf`) with zero
  `*Proof*`/`*Spec*`/`*Lemmas*`/`*Audit*`/`Amd64`/`Arm64`/`Kraken` imports.
- **`Src/Full.lean`**: Flat `410`-function concatenation `kissatModule`
  (`Dimacs.fns ++ Limits.fns ++ ... ++ Search.fns`) with `0` `PatchModule` / `patchFns` /
  `renameFuncCalls` layers, `0` dead slots, `0` externs, `0` exits, `#guard` acyclicity
  checks, and kernel-checked `kissatModule_wf : ∀ f ∈ kissatModule.fns, f.Wf`.

## Upstream `kissat/src/*.c` to `Src/*.lean` Map (Topological Order)

| Topo # | DAG Lvl | `Src/<Name>.lean` | Upstream `kissat/src/*.c` Mirror | Fns | C0 LOC | `Plain`? |
|---:|:---:|:---|:---|---:|---:|:---:|
| 1 | `L0` | `Src/Dimacs.lean` | `parse.c` (byte lexer), `check.c` | 9 | 195 | Yes |
| 2 | `L0` | `Src/Limits.lean` | `kimits.c`, `smooth.c`, `reluctant.c`, `random.h`, `sort.c` | 17 | 302 | Yes |
| 3 | `L0` | `Src/Arena.lean` | `arena.c` | 2 | 26 | Yes |
| 4 | `L0` | `Src/Watch.lean` | `watch.c`, `vector.c` | 15 | 486 | Yes |
| 5 | `L0` | `Src/Heap.lean` | `heap.c` | 4 | 77 | Yes |
| 6 | `L1` | `Src/Backtrack.lean` | `assign.c`, `backtrack.c` | 6 | 128 | Yes |
| 7 | `L2` | `Src/Clause.lean` | `clause.c` | 4 | 70 | Yes |
| 8 | `L0` | `Src/Tiers.lean` | `tiers.c` (+ `M6HdrExt` delay/watermarks/decision-rate) | 18 | 235 | Yes |
| 9 | `L1` | `Src/Bump.lean` | `bump.c`, `queue.c` | 13 | 326 | Yes |
| 10 | `L1` | `Src/Internal.lean` | `internal.c`, `flags.c`, `resize.c` | 14 | 259 | Yes |
| 11 | `L2` | `Src/PropSearch.lean` | `propsearch.c`, `proplit.h`, `trail.c` (`flush_trail`) | 7 | 676 | Yes |
| 12 | `L3` | `Src/Parse.lean` | `parse.c` (clause ingestion + `tumble`) | 5 | 168 | Yes |
| 13 | `L2` | `Src/Collect.lean` | `collect.c`, `trail.c` (`mark_reasons`) | 15 | 465 | Yes |
| 14 | `L3` | `Src/Reduce.lean` | `reduce.c` | 6 | 193 | Yes |
| 15 | `L1` | `Src/Deduce.lean` | `deduce.c`, `strengthen.c` (OTFS) | 10 | 441 | Yes |
| 16 | `L0` | `Src/Minimize.lean` | `minimize.c`, `shrink.c` | 7 | 324 | Yes |
| 17 | `L4` | `Src/Learn.lean` | `learn.c` (incl. `eager_subsume` & OOM recovery) | 5 | 304 | Yes |
| 18 | `L5` | `Src/Analyze.lean` | `analyze.c` | 6 | 303 | Yes |
| 19 | `L2` | `Src/Decide.lean` | `decide.c` | 4 | 133 | Yes |
| 20 | `L3` | `Src/Walk.lean` | `walk.c`, `warmup.c`, `rephase.c` | 14 | 706 | — |
| 21 | `L3` | `Src/Restart.lean` | `restart.c`, `mode.c` | 3 | 150 | Yes |
| 22 | `L0` | `Src/Extend.lean` | `extend.c`, `weaken.c` | 5 | 149 | Yes |
| 23 | `L6` | `Src/Lucky.lean` | `lucky.c` | 4 | 277 | Yes |
| 24 | `L3` | `Src/Vivify.lean` | `vivify.c` | 28 | 862 | — |
| 25 | `L3` | `Src/Backbone.lean` | `backbone.c` | 7 | 238 | — |
| 26 | `L3` | `Src/Transitive.lean` | `transitive.c` | 3 | 154 | — |
| 27 | `L3` | `Src/Substitute.lean` | `substitute.c` | 6 | 245 | — |
| 28 | `L3` | `Src/Dense.lean` | `dense.c`, `propdense.c` | 7 | 204 | — |
| 29 | `L3` | `Src/Congruence.lean` | `congruence.c` | 32 | 1,626 | — |
| 30 | `L0` | `Src/Kitten.lean` | `kitten.c` | 14 | 444 | — |
| 31 | `L4` | `Src/Sweep.lean` | `sweep.c` | 21 | 907 | — |
| 32 | `L4` | `Src/Forward.lean` | `forward.c` | 8 | 418 | — |
| 33 | `L0` | `Src/Gates.lean` | `gates.c`, `ands.c`, `equivalences.c`, `ifthenelse.c` | 13 | 685 | — |
| 34 | `L2` | `Src/Definition.lean` | `definition.c` | 26 | 1,352 | — |
| 35 | `L5` | `Src/Eliminate.lean` | `eliminate.c`, `resolve.c` | 15 | 607 | — |
| 36 | `L5` | `Src/Factor.lean` | `factor.c` | 14 | 928 | — |
| 37 | `L3` | `Src/Compact.lean` | `compact.c` | 13 | 483 | — |
| 38 | `L2` | `Src/Reorder.lean` | `reorder.c` | 3 | 232 | — |
| 39 | `L6` | `Src/Probe.lean` | `probe.c` | 2 | 206 | — |
| 40 | `L7` | `Src/Search.lean` | `preprocess.c`, `search.c`, `internal.c` (`kissat_solve`) | 5 | 156 | Yes |
| — | — | **Total (`40` C0 files)** | **`kissatModule` (`Src/Full.lean`)** | **410** | **16,140** | **23 files** |
