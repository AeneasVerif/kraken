# Kissat Callgrind Dynamic Profiling Suite

Dynamic x86-64 instruction (`Ir`) profiling and comparison toolkit for compiled Kissat binaries,
using `valgrind --tool=callgrind` and `objdump`. It compares **C4** (`LeanQbe.T` native x86-64
assembly binaries) against **C3b** (`PrintCpp`-emitted C++20 binaries compiled with `clang++ -O3`).

## Prerequisites

- `valgrind` (with Callgrind)
- `objdump` (GNU binutils)
- `python3` (stdlib only)
- Unstripped ELF binaries (C4 built via `run_4corner.sh` / `build_solver.sh`; C3b built with
  symbol retention)

## Quick Start: C4 vs C3b Dynamic Comparison

Use [run_prof.sh](run_prof.sh) as the single-command runner to collect Callgrind traces under
`timeout` and emit both per-instruction-class and per-function C4 vs C3b reports:

```bash
timeout 600 bench/kissat/prof/run_prof.sh \
  --c4 /path/to/c4_FullM3 \
  --c3b /path/to/c3b_FullM3 \
  --out-dir /tmp/kissat_prof \
  --timeout 300 \
  path/to/canary1.cnf path/to/canary2.cnf
```

Common options for `run_prof.sh`:
- `--work <bytes>` (default `67108864`) and `--fuel <ticks>` (default `200000000`)
- `--flag <tel_flag>` (default `--full-telemetry-m2`; pass `""` for plain `work fuel cnf`)
- `--top <N>` (default `14` hottest functions per CNF)
- `--skip-existing` to reuse already-collected `<bin>.<cnf_stem>.out` traces in `--out-dir`

## Re-analyzing Collected Traces

- **C4 vs C3b comparison** from existing `.out` files:
  ```bash
  timeout 60 python3 -B bench/kissat/prof/summary.py \
    --c4 /path/to/c4_FullM3 --c3b /path/to/c3b_FullM3 \
    --cg-dir /tmp/kissat_prof c05_bve_vivify_2600 c08_mycielski5_4col
  ```
  Or compare a single explicit pair with `--c4-out` / `--c3b-out` and `--label`.

- **Single-binary instruction class + top-function breakdown**:
  ```bash
  timeout 60 python3 -B bench/kissat/prof/prof.py /path/to/bin /tmp/kissat_prof/bin.cnf.out --top 30
  ```

- **Standalone trace collection**:
  ```bash
  bench/kissat/prof/run_cg.sh --out /tmp/kissat_prof/bin.cnf.out --timeout 300 /path/to/bin path/to/file.cnf
  ```

## Deep-Dive Diagnostic Tools

- [blocks.py](blocks.py): Per-`.L` basic-block `Ir`, approx execution count, and `%rsp` stack-traffic percentage for named functions:
  ```bash
  timeout 60 python3 -B bench/kissat/prof/blocks.py /path/to/c4_FullM3 /tmp/kissat_prof/c4.out full_prop_lit_raw full_watch_push
  ```
- [hot.py](hot.py): Hottest instructions within a function (filtering by `--lo` fraction of peak `Ir` and `--max-lines`):
  ```bash
  timeout 60 python3 -B bench/kissat/prof/hot.py /path/to/c4_FullM3 /tmp/kissat_prof/c4.out full_prop_lit_raw --lo 0.2 --max-lines 40
  ```
- [incl.py](incl.py): Inclusive `Ir` and call counts per callee (works best on C3b symbol names; supports `--edges` and pattern filters):
  ```bash
  timeout 60 python3 -B bench/kissat/prof/incl.py /tmp/kissat_prof/c3b.out --edges full_viv
  ```
- [reload.py](reload.py): Estimates dynamically-redundant intra-block `%rsp` reloads in C4 code:
  ```bash
  timeout 60 python3 -B bench/kissat/prof/reload.py /path/to/c4_FullM3 /tmp/kissat_prof/c4.out
  ```
- [movrr.py](movrr.py): Classifies dynamic C4 register-to-register `mov` idioms (`zext-self`, `addr-chain copy`, `2-address copy`, `call-arg/ABI shuffle`, `block-edge shuffle`):
  ```bash
  timeout 60 python3 -B bench/kissat/prof/movrr.py /path/to/c4_FullM3 /tmp/kissat_prof/c4.out
  ```
