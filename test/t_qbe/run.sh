#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"

OUT_USER="${OUT+set}"
OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-tqbe.XXXXXX")}"
mkdir -p "$OUT"
cleanup() {
  if [ -z "$OUT_USER" ]; then
    rm -rf "$OUT"
  fi
}
trap cleanup EXIT

for tool in cc aarch64-linux-gnu-gcc qemu-aarch64 make; do
  command -v "$tool" >/dev/null 2>&1 || {
    echo "FAIL: required tool not found: $tool" >&2
    exit 1
  }
done
[ -d /usr/aarch64-linux-gnu ] || {
  echo "FAIL: missing sysroot /usr/aarch64-linux-gnu" >&2
  exit 1
}

QBE_SRC="${QBE_SRC:-$ROOT/qbe}"
if [ ! -d "$QBE_SRC" ] && [ -d /usr/local/google/home/andreser/lean-qbe/qbe ]; then
  QBE_SRC=/usr/local/google/home/andreser/lean-qbe/qbe
fi
if [ -z "${QBE:-}" ]; then
  [ -d "$QBE_SRC" ] || {
    echo "FAIL: QBE source directory not found: $QBE_SRC" >&2
    exit 1
  }
  rm -rf "$OUT/qbe-src"
  cp -R "$QBE_SRC" "$OUT/qbe-src"
  timeout 120 make -C "$OUT/qbe-src" clean >/dev/null 2>&1 || true
  timeout 120 make -C "$OUT/qbe-src" -j"$(nproc)"
  QBE="$OUT/qbe-src/qbe"
fi
[ -x "$QBE" ] || {
  echo "FAIL: qbe binary not executable: $QBE" >&2
  exit 1
}

echo "[1/3] Building LeanQbe.T QBE printer & program table..."
timeout 600 lake build --wfail LeanQbe.T.Examples.Programs LeanQbe.T.PrintQbe

cat > "$OUT/emit_qbe.lean" <<'EOF'
import LeanQbe.T.Examples.Programs
import LeanQbe.T.PrintQbe

def main (args : List String) : IO UInt32 := do
  match args with
  | outDir :: names =>
    for name in names do
      match LeanQbe.T.programs.lookup name with
      | none =>
        IO.eprintln s!"unknown program: {name}"
        return 1
      | some fs =>
        match LeanQbe.T.PrintQbe.fns fs with
        | .error e =>
          IO.eprintln s!"PrintQbe failed for {name}: {e}"
          return 1
        | .ok txt =>
          IO.FS.writeFile s!"{outDir}/{name}.ssa" (txt ++ "\n")
    return 0
  | _ =>
    IO.eprintln "usage: emit_qbe <outDir> <prog>..."
    return 2
EOF

CASES=(
  "tracer:test/tracer_main.c"
  "ifelse:test/ifelse_main.c"
  "sumto:test/sumto_main.c"
  "evenodd:test/evenodd_main.c"
  "nested:test/nested_main.c"
  "swap:test/swap_main.c"
  "spill10:test/spill10_main.c"
  "callinc:test/callinc_main.c"
  "twice:test/twice_main.c"
  "sumcall:test/sumcall_main.c"
  "uf:test/uf_main.c"
  "unionfind:test/arm64/unionfind_main.c"
  "lrat_trim:test/lrat_trim_main.c"
  "lrat_bytes:test/lrat_bytes_main.c"
)

PROGS=()
for entry in "${CASES[@]}"; do
  PROGS+=("${entry%%:*}")
done

echo "[2/3] Emitting QBE IL modules..."
timeout 120 lake env lean --run "$OUT/emit_qbe.lean" "$OUT" "${PROGS[@]}"

link_arm64() {
  local sfile="$1" cfile="$2" outbin="$3" errfile="$4"
  local rc=0
  timeout 60 aarch64-linux-gnu-gcc -O1 -no-pie "$sfile" "$cfile" -o "$outbin" 2>"$errfile" || rc=$?
  grep -v -e 'SFrame' "$errfile" >&2 || true
  return "$rc"
}

echo "[3/3] Running stock QBE (x64 & arm64) round-trip tests..."
pass=0
for entry in "${CASES[@]}"; do
  prog="${entry%%:*}"
  main_c="$ROOT/${entry#*:}"
  ssa="$OUT/$prog.ssa"

  echo "  [x64]   $prog"
  timeout 60 "$QBE" "$ssa" -o "$OUT/$prog.x64.s"
  timeout 60 cc -O1 -no-pie "$OUT/$prog.x64.s" "$main_c" -o "$OUT/$prog.x64.bin"
  timeout 30 "$OUT/$prog.x64.bin" >/dev/null
  pass=$((pass + 1))

  echo "  [arm64] $prog"
  timeout 60 "$QBE" -t arm64 "$ssa" -o "$OUT/$prog.arm64.s"
  link_arm64 "$OUT/$prog.arm64.s" "$main_c" "$OUT/$prog.arm64.bin" "$OUT/$prog.arm64.ld.err"
  timeout 30 qemu-aarch64 -L /usr/aarch64-linux-gnu "$OUT/$prog.arm64.bin" >/dev/null
  pass=$((pass + 1))
done

total=$(( ${#CASES[@]} * 2 ))
echo "PASS: test/t_qbe/run.sh ($pass/$total QBE x64+arm64 runs passed)"
