# Direct C0-to-C99 Benchmark Path (`C0-direct`)

`C0-direct` compiles Kissat C0 directly as a strict C99 subset using `clang`
(`-std=c99 -O3 -fwrapv -fno-strict-aliasing -Wall -Wextra -Werror`), bypassing Lean
elaboration, `LeanQbe.T.Module`, `PrintCpp`, and `clang++`.

## Architecture & Splice Fidelity

1. **Block & Splice Extraction (`bench/kissat/extract_c0_direct.py`)**
   - Scans `LeanQbe/T/Examples/Kissat/*.lean` (excluding `*Lemmas*`, `*Proof*`, `*Spec*`,
     `*Arena*`, `*SatNv*`, `*InlB5*`) for `kissat_c0!` blocks, `Fn` rename handles
     (`def ... : Fn := ⟨"export_name", ..., orig_body⟩`), and `List Fn` splice definitions
     (`++`, `.take`, `.drop`, `[...]`).
   - Evaluates `FullM5.m5Fns` (`270` functions, `--target m5`) or `FullM6.m6Fns`
     (`382` functions, `--target m6`) in exact topological splice order.
   - Supports `--check-fns <file|lean|csv>` to assert 1-to-1 ordered name parity.

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

3. **Separate-TU Linkage (`bench/kissat/bench_main.c`)**
   - Compiles `<target>_direct.c` into `<target>_direct.o` and `bench/kissat/bench_main.c`
     into `bench_main.o` in separate translation units, matching the other benchmark paths
     (`C3b`: `PrintCpp` C++20 compiled with `clang++ -O3`; `C4-b5`: `LeanQbe.T` native x86-64
     assembly with `InlinePolicy.b5`).
   - Separate linkage avoids prototype type-mismatch between `bench_main.c`
     (`const uint8_t *`, `uint8_t *`) and C0 (`u64`, `u64`), which share identical SysV
     LP64 register passing (`%rdi`, `%rdx`), and preserves the exact `bench_main.c`
     cross-TU call boundary used by `C3b` and `C4-b5`.

## Usage

```bash
# Build release C0-direct binary (<1s)
bash bench/kissat/build_c0_direct.sh --target m5 --out-dir /tmp/c0direct

# Build ASan + UBSan binary
bash bench/kissat/build_c0_direct.sh --target m5 --out-dir /tmp/c0direct --asan

# Extract C99 source only and verify 270-fn parity against Lean
python3 bench/kissat/extract_c0_direct.py --target m5 --out /tmp/m5_direct.c --check-fns lean
```
