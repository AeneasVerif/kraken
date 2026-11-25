# Direct C0-to-C99 Benchmark Path (`C0-direct`)

`C0-direct` compiles Kissat C0 directly as a strict C99 subset using `clang`
(`-std=c99 -O3 -fwrapv -fno-strict-aliasing -Wall -Wextra -Werror`), bypassing Lean
elaboration, `LeanQbe.T.Module`, `PrintCpp`, and `clang++`.

## Architecture & Splice Fidelity

1. **Block & Splice Extraction (`bench/kissat/extract_c0_direct.py`)**
   - Scans `LeanQbe/T/Examples/Kissat/*.lean` (excluding `*Lemmas*`, `*Proof*`, `*Spec*`,
     `*Arena*`, `*SatNv*`, `*InlB5*`) for `kissat_c0!` blocks, `Fn` rename handles
     (`def ... : Fn := ⟨"export_name", ..., orig_body⟩` or
     `{ name := "export_name", ..., body := orig_body }`), `List Fn` splice definitions
     (`++`, `.take`, `.drop`, `[...]`, `spliceFns`, `patchFns`), and `patchFns` insertion
     plans (`List (Sym × List Fn)`: `[("anchor", <List Fn>), ...]`, named plans, `++`).
   - Evaluates `FullFidelityAssemblyStep7.fidStep7Fns` (`501` functions, default
     `--target fidelity`, alias `fid`; falls back to Step-6 `FullFidelityAssembly.fidFns`
     when Step-7 is not present, with explicit `fidelity-step7` / `fidelity-step6`),
     `FullM8OptAssembly.m8OptFns` (`--target m8opt`, aliases `opt`, `m8`),
     `Plain.plainFns` (`59` functions, `--target plain`), or legacy/transitional targets
     (`m7fidelity`, `m7plus`, `m7`, `m6`, `m5`) in exact topological splice order.
   - Supports `--check-fns <file|lean|csv>` to assert 1-to-1 ordered name parity.
   - Supports `--split-dir <dir>` to emit a shared `kissat_common.h`, one `src_<Stem>.c`
     per Kissat C0 source file (keeping per-block `#define` scoping inside each TU so
     single-file edits leave `kissat_common.h` untouched), and deterministic
     `c0_fn_hashes.json` (`c0_sha256`, per-TU hash, per-fn `sha256`). Only files whose
     bytes change are rewritten, and stale `src_*.c` files are removed automatically.
   - Supports `--diff-base <rev>` (plus `--diff-json <path>`) to compare the current C0
     functions against any git revision and report `UNCHANGED` (`0` changed functions) or
     the changed function list for fast incremental testing and L2 skips.

2. **Faithful C99 Emission**
   - Prepends `#include "c0.h"` (`LeanQbe/T/Frontend/C0/c0.h` for `u8..u64`, `i8..i64`,
     `bool`, `c0_assume`, etc.) and emits deduplicated `typedef`s (`KissatDimacs`,
     `FullHdr`, etc.), deduplicated `static` tables (if any), and forward prototypes for
     all active functions.
   - **Per-Block Macro Scoping (`#undef` / `#define`):** Because each `kissat_c0!` block is
     elaborated in Lean as an independent translation unit (e.g., `FullM5DenseSafe` defines
     `FL_FACT_P=256u`/`FL_FACT_N=512u` while `FullBvaHeap` defines `32u`/`64u`), the
     emitter tracks active macros across block boundaries and emits `#undef`/`#define`
     transitions so every function compiles with its exact block macro environment.
   - **Zero-Warning Hygiene:** Rewrites aliased function declarators to their spliced
     export names (e.g., `full_prop_lit_m4` -> `full_prop_lit_raw`) and inserts
     `(void)param;` for unused parameters (e.g., `budget` in `full_reorder_m5`).

3. **Incremental Split-TU Compilation & Linkage (`bench/kissat/build_c0_direct.sh`)**
   - Default mode splits extraction into `$OUT_DIR/split_<target>` (`--split-dir` to
     override, `--single` for monolithic single-TU `<target>_direct.c`), checks per-TU
     `sha256` stamps (over `compiler+flags+c0.h+kissat_common.h+src_*.c`) and compiles only
     changed TUs in parallel via `xargs -P 8` (`--jobs`, plus `ccache` when installed).
   - Default `--asan` optimization uses strict `-O1 -g -fno-omit-frame-pointer` with
     `-fsanitize=undefined,address -fno-sanitize-recover=all` (strict alignment preserved);
     release builds use `-O3` (`--opt-level` overrides).
   - Separate linkage against `bench/kissat/bench_main.c` preserves the cross-TU ABI
     boundary used by `C3b` and `C4-b5` (`const uint8_t *` / `uint8_t *` vs `u64`).
   - `bench/kissat/check_canaries.py --fn-diff-json <path>` prioritizes canary families
     matching modified C0 functions first (`--skip-unchanged` exits `0` cleanly when
     `unchanged=true`).

## Usage

```bash
# Build incremental split-TU release C0-direct binary (default: Step-7 fidelity, 501 fns)
bash bench/kissat/build_c0_direct.sh --target fidelity --out-dir /tmp/c0direct

# Build strict -O1 ASan + UBSan binary and run 40-canary verification
bash bench/kissat/build_c0_direct.sh --target fidelity --out-dir /tmp/c0direct --asan
python3 -B bench/kissat/check_canaries.py --include-c11 --poison-work \
  --fid-c0d /tmp/c0direct/bench_c0direct_fidelity_asan

# Compute per-function diff vs base commit and prioritize affected canary families
python3 -B bench/kissat/extract_c0_direct.py --target fidelity \
  --diff-base HEAD~1 --diff-json /tmp/c0diff.json
python3 -B bench/kissat/check_canaries.py --include-c11 --fn-diff-json /tmp/c0diff.json \
  --fid-c0d /tmp/c0direct/bench_c0direct_fidelity_asan

# Legacy monolithic C99 extraction + parity verification against Lean
python3 -B bench/kissat/extract_c0_direct.py --target m5 --out /tmp/m5_direct.c --check-fns lean
```
