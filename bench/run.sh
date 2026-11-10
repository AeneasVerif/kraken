#!/usr/bin/env bash
# Benchmark and QBE pass-ablation suite (plan step 6).
# Compares:
#   1. gcc -O2 and clang -O2 on C (union-find C and Bedrock2-generated lrat-trim C);
#   2. stock QBE on `LeanQbe.Print.module` output (`uf.ssa`, `lrat_trim.ssa`), plus pass ablations
#      disabling one QBE pass at a time (fold, copy, gvn/gcm, simpl, isel addressing, rega coalescing);
#   3. lean-qbe x64 compiled assembly (`uf_leaf.s` today; `uf.s` and `lrat_trim.s` as soon as R3 lands).
# Every command runs under `timeout`. Never modifies `qbe/`.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-bench.XXXXXX")}"
mkdir -p "$OUT"
QBE_SRC="${QBE_SRC:-$ROOT/qbe}"
[ -d "$QBE_SRC" ] || QBE_SRC="/usr/local/google/home/andreser/lean-qbe/qbe"

echo "== 1. Dumping QBE IL and lean-qbe x64 assembly into $OUT"
timeout 600 lake env lean --run bench/DumpBench.lean "$OUT"

echo "== 2. Building instrumented stock QBE (with env-var pass ablation switches) in $OUT/qbe-src"
rm -rf "$OUT/qbe-src"
cp -r "$QBE_SRC" "$OUT/qbe-src"

python3 - "$OUT/qbe-src" <<'PY'
import sys, pathlib
d = pathlib.Path(sys.argv[1])

# 1. fold.c: QBE_NO_FOLD disables foldref
p = d / "fold.c"
s = p.read_text()
s = s.replace("foldref(Fn *fn, Ins *i)\n{", "foldref(Fn *fn, Ins *i)\n{\n\tif (getenv(\"QBE_NO_FOLD\")) return R;")
p.write_text(s)

# 2. copy.c: QBE_NO_COPY disables copyref and phicopyref
p = d / "copy.c"
s = p.read_text()
s = s.replace("copyref(Fn *fn, Blk *b, Ins *i)\n{", "copyref(Fn *fn, Blk *b, Ins *i)\n{\n\tif (getenv(\"QBE_NO_COPY\")) return R;")
s = s.replace("phicopyref(Fn *fn, Blk *b, Phi *p)\n{", "phicopyref(Fn *fn, Blk *b, Phi *p)\n{\n\tif (getenv(\"QBE_NO_COPY\")) return R;")
p.write_text(s)

# 3. gvn.c: QBE_NO_FOLD disables assoccon; QBE_NO_GVNGCM disables gvndup and dedupjmp
p = d / "gvn.c"
s = p.read_text()
s = s.replace("assoccon(Fn *fn, Blk *b, Ins *i1)\n{", "assoccon(Fn *fn, Blk *b, Ins *i1)\n{\n\tif (getenv(\"QBE_NO_FOLD\")) return;")
s = s.replace("gvndup(Ins *i, int insert)\n{", "gvndup(Ins *i, int insert)\n{\n\tif (getenv(\"QBE_NO_GVNGCM\")) return 0;")
s = s.replace("dedupjmp(Fn *fn, Blk *b)\n{", "dedupjmp(Fn *fn, Blk *b)\n{\n\tif (getenv(\"QBE_NO_GVNGCM\")) return;")
p.write_text(s)

# 4. main.c: QBE_NO_GVNGCM skips gcm(fn); QBE_NO_SIMPL skips simpl(fn)
p = d / "main.c"
s = p.read_text()
s = s.replace("\tgcm(fn);\n", "\tif (!getenv(\"QBE_NO_GVNGCM\")) gcm(fn);\n")
s = s.replace("\tsimpl(fn);\n", "\tif (!getenv(\"QBE_NO_SIMPL\")) simpl(fn);\n")
p.write_text(s)

# 5. amd64/isel.c: QBE_NO_ADDR disables amatch and seladdr offset folding
p = d / "amd64/isel.c"
s = p.read_text()
s = s.replace("seladdr(Ref *r, Num *tn, Fn *fn)\n{", "seladdr(Ref *r, Num *tn, Fn *fn)\n{\n\tif (getenv(\"QBE_NO_ADDR\")) return;")
s = s.replace("amatch(Addr *a, Num *tn, Ref r, Fn *fn)\n{", "amatch(Addr *a, Num *tn, Ref r, Fn *fn)\n{\n\tif (getenv(\"QBE_NO_ADDR\")) return 0;")
p.write_text(s)

# 6. rega.c: QBE_NO_COALESCE disables sethint
p = d / "rega.c"
s = p.read_text()
s = s.replace("sethint(int t, int r)\n{", "sethint(int t, int r)\n{\n\tif (getenv(\"QBE_NO_COALESCE\")) return;")
p.write_text(s)
PY

timeout 300 make -C "$OUT/qbe-src" -j8 >/dev/null
QBE="$OUT/qbe-src/qbe"

insns() { # count instructions in a .s file (indented or unindented)
  grep -vE '^\s*($|\.|#|/\*|[A-Za-z0-9_.$]+:)' "$1" 2>/dev/null | wc -l | tr -d ' '
}

median_ms() { # run binary ($1) with optional arg ($2) 5 times, print median ms and check hash
  local bin="$1"
  local arg="${2:-}"
  local times=()
  local hash=""
  for _ in 1 2 3 4 5; do
    local out
    if [ -n "$arg" ]; then out="$(timeout 60 "$bin" "$arg")"; else out="$(timeout 60 "$bin")"; fi
    local m h
    m="$(sed -n 's/.*ms=\([0-9.]*\).*/\1/p' <<<"$out")"
    h="$(sed -n 's/.*hash=\(0x[0-9a-f]*\).*/\1/p' <<<"$out")"
    times+=("$m")
    hash="$h"
  done
  local med
  med="$(printf '%s\n' "${times[@]}" | sort -n | sed -n '3p')"
  echo "$med $hash"
}

echo ""
echo "== 3. C baselines (gcc -O2, clang -O2)"
timeout 60 gcc -std=c11 -O2 -DUF_IN_C bench/uf_bench.c -o "$OUT/uf_gcc"
timeout 60 clang -std=c11 -O2 -DUF_IN_C bench/uf_bench.c -o "$OUT/uf_clang"
timeout 60 gcc -std=c11 -O2 bench/lrat_bench.c bench/lrat_trim_bedrock2.c -o "$OUT/lrat_gcc"
timeout 60 clang -std=c11 -O2 bench/lrat_bench.c bench/lrat_trim_bedrock2.c -o "$OUT/lrat_clang"

echo "| Compiler / Variant | UF (call) ms | UF (inline) ms |UF insns| LRAT (full) ms | LRAT (rup) ms |LRAT insns| Hash check |"
echo "|---|---:|---:|---:|---:|---:|---:|---|"

for cc in gcc clang; do
  read -r ufc h1 <<<"$(median_ms "$OUT/uf_$cc")"
  read -r ufi h2 <<<"$(median_ms "$OUT/uf_$cc" inline)"
  read -r lrf h3 <<<"$(median_ms "$OUT/lrat_$cc")"
  read -r lrr h4 <<<"$(median_ms "$OUT/lrat_$cc" rup)"
  echo "| $cc -O2 (C) | $ufc | $ufi | - | $lrf | $lrr | - | $h1 / $h3 |"
done

# QBE variants
declare -a LABELS=(
  "stock QBE (all passes)"
  "QBE -fold"
  "QBE -copy"
  "QBE -gvn/gcm"
  "QBE -simpl"
  "QBE -isel-addr"
  "QBE -rega-coalesce"
  "QBE -all-opt"
)
declare -a ENVS=(
  ""
  "QBE_NO_FOLD=1"
  "QBE_NO_COPY=1"
  "QBE_NO_GVNGCM=1"
  "QBE_NO_SIMPL=1"
  "QBE_NO_ADDR=1"
  "QBE_NO_COALESCE=1"
  "QBE_NO_FOLD=1 QBE_NO_COPY=1 QBE_NO_GVNGCM=1 QBE_NO_SIMPL=1 QBE_NO_ADDR=1 QBE_NO_COALESCE=1"
)

for idx in "${!LABELS[@]}"; do
  lbl="${LABELS[$idx]}"
  env_vars="${ENVS[$idx]}"
  tag="qbe_$idx"
  env $env_vars timeout 60 "$QBE" -o "$OUT/uf_$tag.s" "$OUT/uf.ssa"
  env $env_vars timeout 60 "$QBE" -o "$OUT/lrat_$tag.s" "$OUT/lrat_trim.ssa"
  timeout 60 gcc -std=c11 -O2 bench/uf_bench.c "$OUT/uf_$tag.s" -o "$OUT/uf_$tag"
  timeout 60 gcc -std=c11 -O2 bench/lrat_bench.c "$OUT/lrat_$tag.s" -o "$OUT/lrat_$tag"
  ufi_cnt="$(insns "$OUT/uf_$tag.s")"
  lri_cnt="$(insns "$OUT/lrat_$tag.s")"
  read -r ufc h1 <<<"$(median_ms "$OUT/uf_$tag")"
  read -r ufi h2 <<<"$(median_ms "$OUT/uf_$tag" inline)"
  read -r lrf h3 <<<"$(median_ms "$OUT/lrat_$tag")"
  read -r lrr h4 <<<"$(median_ms "$OUT/lrat_$tag" rup)"
  echo "| $lbl | $ufc | $ufi | $ufi_cnt | $lrf | $lrr | $lri_cnt | $h1 / $h3 |"
done

if [ -f "$OUT/uf.s" ] && [ -f "$OUT/lrat_trim.s" ]; then
  timeout 60 gcc -std=c11 -O2 bench/uf_bench.c "$OUT/uf.s" -o "$OUT/uf_leanqbe"
  timeout 60 gcc -std=c11 -O2 bench/lrat_bench.c "$OUT/lrat_trim.s" -o "$OUT/lrat_leanqbe"
  read -r ufc h1 <<<"$(median_ms "$OUT/uf_leanqbe")"
  read -r ufi _ <<<"$(median_ms "$OUT/uf_leanqbe" inline)"
  read -r lrf h3 <<<"$(median_ms "$OUT/lrat_leanqbe")"
  read -r lrr _ <<<"$(median_ms "$OUT/lrat_leanqbe" rup)"
  ufi_cnt="$(insns "$OUT/uf.s")"
  lri_cnt="$(insns "$OUT/lrat_trim.s")"
  echo "| lean-qbe (x64, simple isel) | $ufc | $ufi | $ufi_cnt | $lrf | $lrr | $lri_cnt | $h1 / $h3 |"
fi

if [ -f "$OUT/uf_fast.s" ] && [ -f "$OUT/lrat_trim_fast.s" ]; then
  timeout 60 gcc -std=c11 -O2 bench/uf_bench.c "$OUT/uf_fast.s" -o "$OUT/uf_leanqbe_fast"
  timeout 60 gcc -std=c11 -O2 bench/lrat_bench.c "$OUT/lrat_trim_fast.s" -o "$OUT/lrat_leanqbe_fast"
  read -r ufc h1 <<<"$(median_ms "$OUT/uf_leanqbe_fast")"
  read -r ufi _ <<<"$(median_ms "$OUT/uf_leanqbe_fast" inline)"
  read -r lrf h3 <<<"$(median_ms "$OUT/lrat_leanqbe_fast")"
  read -r lrr _ <<<"$(median_ms "$OUT/lrat_leanqbe_fast" rup)"
  ufi_cnt="$(insns "$OUT/uf_fast.s")"
  lri_cnt="$(insns "$OUT/lrat_trim_fast.s")"
  echo "| **lean-qbe (x64, fast isel)** | $ufc | $ufi | $ufi_cnt | $lrf | $lrr | $lri_cnt | $h1 / $h3 |"
fi
