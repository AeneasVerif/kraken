#!/usr/bin/env bash
# Benchmark and QBE pass-ablation suite (plan step 6).
# Compares:
#   1. gcc -O2 and clang -O2 on C (union-find C and Bedrock2-generated lrat-trim C);
#   2. stock QBE on the QBE IL that `leanqbe --il` prints for the modules `uf_bench` and `lrat_trim`,
#      plus pass ablations disabling one QBE pass at a time (fold, copy, gvn/gcm, simpl, isel
#      addressing, rega coalescing);
#   3. lean-qbe: the x64 assembly that `leanqbe` emits for the same two modules.
# Every row must print the result hashes of the first row (gcc -O2 on C) in each of its four runs.
# A row that prints other hashes, and a run that fails or prints no hash, is listed after the table
# and makes the exit code 1; so does every command that fails (`set -e`).
# Every command runs under `timeout`. Never modifies `qbe/`.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-bench.XXXXXX")}"
mkdir -p "$OUT"
QBE_SRC="${QBE_SRC:-$ROOT/qbe}"
HAS_QBE_ABLATION=0
if [ -d "$QBE_SRC" ]; then
  HAS_QBE_ABLATION=1
elif QBE="${QBE:-$(command -v qbe || true)}" && [ -n "$QBE" ]; then
  echo "NOTE: QBE_SRC not found at $QBE_SRC; using $QBE (skipping pass-ablation variants)."
else
  echo "FAIL: QBE source directory ($QBE_SRC) and qbe binary not found; set QBE_SRC or QBE" >&2
  exit 1
fi

echo "== 1. Emitting QBE IL and lean-qbe (x64 + arm64) assembly into $OUT"
timeout 1800 lake build leanqbe leanqbe-arm64 >"$OUT/build.log" 2>&1 || { tail -20 "$OUT/build.log"; exit 1; }
LEANQBE="$ROOT/.lake/build/bin/leanqbe"
LEANQBE_ARM64="$ROOT/.lake/build/bin/leanqbe-arm64"
timeout 60 "$LEANQBE" --il uf_bench >"$OUT/uf.ssa"
timeout 60 "$LEANQBE" --il lrat_trim >"$OUT/lrat_trim.ssa"
timeout 60 "$LEANQBE" uf_bench >"$OUT/uf.s"
timeout 60 "$LEANQBE" lrat_trim >"$OUT/lrat_trim.s"
timeout 60 "$LEANQBE_ARM64" uf_bench >"$OUT/uf_arm64.s"
timeout 60 "$LEANQBE_ARM64" lrat_trim >"$OUT/lrat_trim_arm64.s"

if [ "$HAS_QBE_ABLATION" = "1" ]; then
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
else
  echo "== 2. Using prebuilt stock QBE: $QBE"
fi

insns() { # count instructions in a .s file (indented or unindented)
  grep -vE '^\s*($|\.|#|/\*|[A-Za-z0-9_.$]+:)' "$1" 2>/dev/null | wc -l | tr -d ' '
}

median_ms() { # run binary ($1) with optional arg ($2) 5 times, print the median ms and the hash;
              # print "FAILED FAILED" if a run fails or prints no ms= and hash=, or if the hash varies
  local bin="$1"
  local arg="${2:-}"
  local times=()
  local hash=""
  local ok=1
  for _ in 1 2 3 4 5; do
    local out
    if [ -n "$arg" ]; then out="$(timeout 60 "$bin" "$arg")" || ok=0; else out="$(timeout 60 "$bin")" || ok=0; fi
    local m h
    m="$(sed -n 's/.*ms=\([0-9.]*\).*/\1/p' <<<"$out")"
    h="$(sed -n 's/.*hash=\(0x[0-9a-f]*\).*/\1/p' <<<"$out")"
    [ -n "$m" ] && [ -n "$h" ] || ok=0
    [ -z "$hash" ] || [ "$h" = "$hash" ] || ok=0
    times+=("$m")
    hash="$h"
  done
  local med
  med="$(printf '%s\n' "${times[@]}" | sort -n | sed -n '3p')"
  if [ $ok = 1 ]; then echo "$med $hash"; else echo "FAILED FAILED"; fi
}

# The first row whose runs all succeed (gcc -O2 on C) sets the reference result hashes; check_row
# records every other row that does not print exactly those. The table shows the hashes of the
# UF (call) and LRAT (full) runs; all four are compared.
REF=""
REF_LBL=""
ROWS=0
FAILS=()
check_row() { # $1 = label, $2 $3 $4 $5 = result hashes: UF (call), UF (inline), LRAT (full), LRAT (rup)
  local lbl="$1" hs="$2 $3 $4 $5" h valid=1 note=""
  ROWS=$((ROWS + 1))
  for h in "$2" "$3" "$4" "$5"; do
    case "$h" in 0x*) ;; *) valid=0 ;; esac
  done
  if [ $valid = 1 ] && [ -z "$REF" ]; then REF="$hs"; REF_LBL="$lbl"
  elif [ "$hs" != "$REF" ]; then
    [ $valid = 1 ] || note=" (FAILED: a run failed, printed no hash, or printed different hashes in its five repetitions)"
    FAILS+=("$lbl: result hashes $hs differ from those of ${REF_LBL:-the reference row, which is missing}: ${REF:--}$note")
  fi
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
  check_row "$cc -O2 (C)" "$h1" "$h2" "$h3" "$h4"
done

# QBE variants
if [ "$HAS_QBE_ABLATION" = "1" ]; then
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
else
  declare -a LABELS=("stock QBE (all passes)")
  declare -a ENVS=("")
fi

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
  check_row "$lbl" "$h1" "$h2" "$h3" "$h4"
done

timeout 60 gcc -std=c11 -O2 bench/uf_bench.c "$OUT/uf.s" -o "$OUT/uf_leanqbe"
timeout 60 gcc -std=c11 -O2 bench/lrat_bench.c "$OUT/lrat_trim.s" -o "$OUT/lrat_leanqbe"
read -r ufc h1 <<<"$(median_ms "$OUT/uf_leanqbe")"
read -r ufi h2 <<<"$(median_ms "$OUT/uf_leanqbe" inline)"
read -r lrf h3 <<<"$(median_ms "$OUT/lrat_leanqbe")"
read -r lrr h4 <<<"$(median_ms "$OUT/lrat_leanqbe" rup)"
ufi_cnt="$(insns "$OUT/uf.s")"
lri_cnt="$(insns "$OUT/lrat_trim.s")"
echo "| **lean-qbe (x64)** | $ufc | $ufi | $ufi_cnt | $lrf | $lrr | $lri_cnt | $h1 / $h3 |"
check_row "lean-qbe (x64)" "$h1" "$h2" "$h3" "$h4"

CC_ARM64="${CC_AARCH64:-aarch64-linux-gnu-gcc}"
RUN_ARM64="qemu-aarch64 -L /usr/aarch64-linux-gnu"
arm64_hash() {
  local bin="$1" arg="${2:-}" out h
  if [ -n "$arg" ]; then out="$(timeout 60 $RUN_ARM64 "$bin" "$arg")" || return 0
  else out="$(timeout 60 $RUN_ARM64 "$bin")" || return 0; fi
  h="$(sed -n 's/.*hash=\(0x[0-9a-f]*\).*/\1/p' <<<"$out")"
  echo "${h:-FAILED}"
}
link_arm64() {
  timeout 60 "$CC_ARM64" -std=c11 -O2 "$1" "$2" -o "$3" 2>&1 | grep -v -e 'SFrame' >&2 || true
  [ -x "$3" ]
}

timeout 60 "$QBE" -t arm64 -o "$OUT/uf_qbe_arm64.s" "$OUT/uf.ssa"
timeout 60 "$QBE" -t arm64 -o "$OUT/lrat_qbe_arm64.s" "$OUT/lrat_trim.ssa"
for pair in "stock QBE (arm64):$OUT/uf_qbe_arm64.s:$OUT/lrat_qbe_arm64.s:qbe_arm64" \
            "**lean-qbe (arm64)**:$OUT/uf_arm64.s:$OUT/lrat_trim_arm64.s:leanqbe_arm64"; do
  IFS=: read -r lbl ufs lrs tag <<<"$pair"
  ufi_cnt="$(insns "$ufs")"
  lri_cnt="$(insns "$lrs")"
  link_arm64 bench/uf_bench.c "$ufs" "$OUT/uf_$tag"
  link_arm64 bench/lrat_bench.c "$lrs" "$OUT/lrat_$tag"
  h1="$(arm64_hash "$OUT/uf_$tag")"
  h2="$(arm64_hash "$OUT/uf_$tag" inline)"
  h3="$(arm64_hash "$OUT/lrat_$tag")"
  h4="$(arm64_hash "$OUT/lrat_$tag" rup)"
  echo "| $lbl | - | - | $ufi_cnt | - | - | $lri_cnt | $h1 / $h3 |"
  check_row "${lbl//\*/}" "$h1" "$h2" "$h3" "$h4"
done

echo ""
if [ ${#FAILS[@]} -eq 0 ]; then
  echo "== bench: all $ROWS rows print the result hashes of $REF_LBL in all four runs: $REF"
else
  printf 'FAIL: %s\n' "${FAILS[@]}"
  echo "== bench: FAILED"
  exit 1
fi
