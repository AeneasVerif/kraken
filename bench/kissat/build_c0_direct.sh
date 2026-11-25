#!/usr/bin/env bash
# Direct C0 -> C99 -> clang -std=c99 builder (zero Lean/QBE/PrintCpp/clang++).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
if [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullFidelityAssemblyStep7.lean" ] || \
   [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullFidelityAssembly.lean" ]; then
  TARGET="fidelity"
elif [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM7FidelityAssembly.lean" ]; then
  TARGET="m7fidelity"
else
  TARGET="m5"
fi
OUT_DIR="/tmp/kissat-c0direct"
OUT_BIN=""
SPLIT_MODE=1
SPLIT_DIR=""
JOBS=8
ASAN=0
OPT_LEVEL=""
CHECK_FNS=""
DIFF_BASE=""

usage() {
  cat <<'EOF'
usage: bash bench/kissat/build_c0_direct.sh [options]
  --target <fidelity|fidelity-step7|fidelity-step6|m8opt|plain|m7fidelity|m7plus|m7|m6|m5>
                         Kissat C0 splice target (aliases: fid, opt, m8; default: auto)
  --out-dir <dir>        Output directory for sources/objects/binary (default: /tmp/kissat-c0direct)
  -o, --out <bin>        Output binary path (default: <out-dir>/bench_c0direct_<target>[_asan])
  --split-dir <dir>      Split-TU source directory (default in split mode: <out-dir>/split_<target>)
  --single               Compile legacy monolithic <target>_direct.c instead of split TUs
  -j, --jobs <N>         Parallel compile workers in split mode (default: 8)
  --opt-level <level>    Optimization flag (default: -O1 under --asan, -O3 otherwise)
  --asan                 Enable ASan+UBSan (-O1 -g -fsanitize=undefined,address, strict align)
  --check-fns <arg>      Optional parity check forwarded to extract_c0_direct.py
  --diff-base <rev>      Forward --diff-base <rev> to extract_c0_direct.py
  -h, --help             Show this help
EOF
}

while [ $# -gt 0 ]; do
  case "$1" in
    --target) TARGET="$2"; shift 2 ;;
    --out-dir) OUT_DIR="$2"; shift 2 ;;
    -o|--out) OUT_BIN="$2"; shift 2 ;;
    --split-dir) SPLIT_DIR="$2"; SPLIT_MODE=1; shift 2 ;;
    --single) SPLIT_MODE=0; shift ;;
    -j|--jobs) JOBS="$2"; shift 2 ;;
    --opt-level) OPT_LEVEL="$2"; shift 2 ;;
    --asan) ASAN=1; shift ;;
    --check-fns) CHECK_FNS="$2"; shift 2 ;;
    --diff-base) DIFF_BASE="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "ERROR: unknown argument '$1'" >&2; usage >&2; exit 2 ;;
  esac
done

case "$TARGET" in
  plain|fidelity|fid|fidelity-step7|fidelity-step6|fidelity-c0|m8opt|opt|m8|m5|m6|m7|\
  m7plus|m7fidelity|m7plus-memshrink|m7fidelity-memshrink) ;;
  *) echo "ERROR: unsupported --target '$TARGET'" >&2; exit 2 ;;
esac

mkdir -p "$OUT_DIR"
SUFFIX=""
SAN_FLAGS=()
if [ "$ASAN" -eq 1 ]; then
  SUFFIX="_asan"
  SAN_FLAGS=(-g -fno-omit-frame-pointer -fsanitize=undefined,address -fno-sanitize-recover=all)
  OPT_LEVEL="${OPT_LEVEL:--O1}"
else
  OPT_LEVEL="${OPT_LEVEL:--O3}"
fi
case "$OPT_LEVEL" in
  -O*) ;;
  O*) OPT_LEVEL="-$OPT_LEVEL" ;;
  *) OPT_LEVEL="-O$OPT_LEVEL" ;;
esac

OUT_BIN="${OUT_BIN:-$OUT_DIR/bench_c0direct_${TARGET}${SUFFIX}}"
CC="${CC:-clang}"
CC_CMD=("$CC")
if command -v ccache >/dev/null 2>&1; then
  CC_CMD=(ccache "$CC")
fi
C0_FLAGS=(-std=c99 "$OPT_LEVEL" -fwrapv -fno-strict-aliasing -Wall -Wextra -Werror)
# Plain's C0 has one unparenthesized `a || b && c` (clang -Wlogical-op-parentheses,
# gcc -Wparentheses); fidelity/opt targets stay warning-free without it.
if [ "$TARGET" = plain ]; then C0_FLAGS+=(-Wno-parentheses); fi
MAIN_FLAGS=(-std=c99 "$OPT_LEVEL" -Wall -Wextra -Werror)

if [ "$SPLIT_MODE" -eq 0 ]; then
  C_SRC="$OUT_DIR/${TARGET}_direct.c"
  C_OBJ="$OUT_DIR/${TARGET}_direct${SUFFIX}.o"
  MAIN_OBJ="$OUT_DIR/bench_main${SUFFIX}.o"

  EXT_ARGS=(--target "$TARGET" --out "$C_SRC")
  [ -n "$CHECK_FNS" ] && EXT_ARGS+=(--check-fns "$CHECK_FNS")
  [ -n "$DIFF_BASE" ] && EXT_ARGS+=(--diff-base "$DIFF_BASE")

  t0_ns="$(date +%s%N)"
  timeout 30 python3 -B "$ROOT/bench/kissat/extract_c0_direct.py" "${EXT_ARGS[@]}"
  t1_ns="$(date +%s%N)"

  timeout 60 "${CC_CMD[@]}" "${C0_FLAGS[@]}" "${SAN_FLAGS[@]}" \
    -I"$ROOT/LeanQbe/T/Frontend/C0" -c "$C_SRC" -o "$C_OBJ"
  t2_ns="$(date +%s%N)"

  timeout 60 "${CC_CMD[@]}" "${MAIN_FLAGS[@]}" "${SAN_FLAGS[@]}" \
    -I"$ROOT/test/kissat" -c "$ROOT/bench/kissat/bench_main.c" -o "$MAIN_OBJ"
  timeout 60 "$CC" "${SAN_FLAGS[@]}" "$C_OBJ" "$MAIN_OBJ" -o "$OUT_BIN"
  t3_ns="$(date +%s%N)"

  awk -v t0="$t0_ns" -v t1="$t1_ns" -v t2="$t2_ns" -v t3="$t3_ns" -v bin="$OUT_BIN" \
    'BEGIN { printf "Built %s (extract=%.0fms compile=%.0fms link+main=%.0fms total=%.0fms)\n",
               bin, (t1-t0)/1e6, (t2-t1)/1e6, (t3-t2)/1e6, (t3-t0)/1e6 }'
  exit 0
fi

SPLIT_DIR="${SPLIT_DIR:-$OUT_DIR/split_${TARGET}}"
OBJ_DIR="$OUT_DIR/obj_${TARGET}${SUFFIX}"
mkdir -p "$SPLIT_DIR" "$OBJ_DIR"
MAIN_OBJ="$OBJ_DIR/bench_main.o"
MAIN_STAMP="$OBJ_DIR/bench_main.sha256"
LINK_STAMP="$OBJ_DIR/link.sha256"

EXT_ARGS=(--target "$TARGET" --split-dir "$SPLIT_DIR")
[ -n "$CHECK_FNS" ] && EXT_ARGS+=(--check-fns "$CHECK_FNS")
[ -n "$DIFF_BASE" ] && EXT_ARGS+=(--diff-base "$DIFF_BASE")

t0_ns="$(date +%s%N)"
timeout 30 python3 -B "$ROOT/bench/kissat/extract_c0_direct.py" "${EXT_ARGS[@]}"
t1_ns="$(date +%s%N)"

CC_VER="$("$CC" --version | head -n1)"
STAMP_INFO="$(timeout 30 python3 -B - "$ROOT" "$SPLIT_DIR" "$OBJ_DIR" "$OUT_BIN" \
  "$CC_VER|${C0_FLAGS[*]}|${SAN_FLAGS[*]}" "$CC_VER|${MAIN_FLAGS[*]}|${SAN_FLAGS[*]}" \
  "$CC_VER|${SAN_FLAGS[*]}" <<'PY'
import hashlib, pathlib, sys

root = pathlib.Path(sys.argv[1])
split_dir = pathlib.Path(sys.argv[2])
obj_dir = pathlib.Path(sys.argv[3])
out_bin = pathlib.Path(sys.argv[4])
c0_key, main_key, link_key = sys.argv[5], sys.argv[6], sys.argv[7]

hdr_hash = hashlib.sha256(
    (root / "LeanQbe/T/Frontend/C0/c0.h").read_bytes()
    + (split_dir / "kissat_common.h").read_bytes()
).hexdigest()

srcs = sorted(split_dir.glob("src_*.c"))
active_objs = {f"{s.stem}.o" for s in srcs}
active_stamps = {f"{s.stem}.sha256" for s in srcs}
for old_o in obj_dir.glob("src_*.o"):
    if old_o.name not in active_objs:
        old_o.unlink()
for old_s in obj_dir.glob("src_*.sha256"):
    if old_s.name not in active_stamps:
        old_s.unlink()

dirty = []
obj_sigs = []
for src in srcs:
    obj = obj_dir / f"{src.stem}.o"
    stf = obj_dir / f"{src.stem}.sha256"
    cur = hashlib.sha256(
        f"{c0_key}\n{hdr_hash}\n".encode("utf-8") + src.read_bytes()
    ).hexdigest()
    obj_sigs.append(f"{obj.name}:{cur}")
    prev = stf.read_text().strip() if (obj.is_file() and stf.is_file()) else ""
    if prev != cur:
        dirty.extend((str(src), str(obj), str(stf), cur))

dirty_nul = obj_dir / ".dirty_tus.nul"
dirty_nul.write_bytes(b"\0".join(x.encode("utf-8") for x in dirty) + (b"\0" if dirty else b""))

main_obj = obj_dir / "bench_main.o"
main_stf = obj_dir / "bench_main.sha256"
main_cur = hashlib.sha256(
    f"{main_key}\n".encode("utf-8")
    + (root / "bench/kissat/bench_main.c").read_bytes()
    + (root / "test/kissat/kissat_verify.h").read_bytes()
    + (root / "test/guarded_buf.h").read_bytes()
).hexdigest()
dirty_main = 0 if (
    main_obj.is_file() and main_stf.is_file() and main_stf.read_text().strip() == main_cur
) else 1

link_cur = hashlib.sha256(
    f"{link_key}\n{main_cur}\n{','.join(obj_sigs)}\n".encode("utf-8")
).hexdigest()
link_stf = obj_dir / "link.sha256"
need_link = 0 if (
    out_bin.is_file() and link_stf.is_file() and link_stf.read_text().strip() == link_cur
    and not dirty and not dirty_main
) else 1

print(f"{len(srcs)} {len(dirty)//4} {dirty_main} {main_cur} {need_link} {link_cur}")
PY
)"
read -r TOTAL_TUS DIRTY_TUS DIRTY_MAIN MAIN_CUR NEED_LINK LINK_CUR <<<"$STAMP_INFO"

if [ "$DIRTY_TUS" -gt 0 ]; then
  XARGS_SCRIPT='n=$(($# - 4)); "${@:1:$n}" -c "${@:$((n+1)):1}" -o "${@:$((n+2)):1}"'
  XARGS_SCRIPT="$XARGS_SCRIPT"' && printf "%s\n" "${@:$((n+4)):1}" > "${@:$((n+3)):1}"'
  timeout 120 xargs -0 -r -P "$JOBS" -n 4 bash -c "$XARGS_SCRIPT" \
    _ "${CC_CMD[@]}" "${C0_FLAGS[@]}" "${SAN_FLAGS[@]}" \
    -I"$ROOT/LeanQbe/T/Frontend/C0" -I"$SPLIT_DIR" <"$OBJ_DIR/.dirty_tus.nul"
fi
if [ "$DIRTY_MAIN" -eq 1 ]; then
  timeout 60 "${CC_CMD[@]}" "${MAIN_FLAGS[@]}" "${SAN_FLAGS[@]}" \
    -I"$ROOT/test/kissat" -c "$ROOT/bench/kissat/bench_main.c" -o "$MAIN_OBJ"
  printf '%s\n' "$MAIN_CUR" >"$MAIN_STAMP"
fi
t2_ns="$(date +%s%N)"

if [ "$NEED_LINK" -eq 1 ]; then
  mapfile -t LINK_OBJS < <(LC_ALL=C printf '%s\n' "$OBJ_DIR"/src_*.o | sort)
  timeout 60 "$CC" "${SAN_FLAGS[@]}" "${LINK_OBJS[@]}" "$MAIN_OBJ" -o "$OUT_BIN"
  printf '%s\n' "$LINK_CUR" >"$LINK_STAMP"
fi
t3_ns="$(date +%s%N)"

AWK_FMT='Built %s (rebuilt=%d/%d tus, main=%d, link=%d | extract=%.0fms compile=%.0fms'
AWK_FMT="$AWK_FMT"' link=%.0fms total=%.0fms)\n'
awk -v t0="$t0_ns" -v t1="$t1_ns" -v t2="$t2_ns" -v t3="$t3_ns" -v bin="$OUT_BIN" \
  -v dt="$DIRTY_TUS" -v tt="$TOTAL_TUS" -v dm="$DIRTY_MAIN" -v nl="$NEED_LINK" \
  -v fmt="$AWK_FMT" \
  'BEGIN { printf fmt, bin, dt, tt, dm, nl, (t1-t0)/1e6, (t2-t1)/1e6, (t3-t2)/1e6, (t3-t0)/1e6 }'
