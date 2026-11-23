#!/usr/bin/env bash
set -euo pipefail

# Standalone guardrail runner for c11_* regression canaries, OOM/witness/h->oom monotonicity
# fuzzing, PrintCpp C++20 (C3b) structural invariants, and upstream Kissat (C1) vs C3b telemetry.
# Does not modify repository state.

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"

KISSAT_BIN="${KISSAT_BIN:-}"
C4_BIN=""
C3B_BIN=""
GEN_HPP=""
LABEL="FullM4"
PER_TIMEOUT=15
QUICK=0
WITH_BASE=0
SKIP_TELEM=0
OUT_DIR=""

usage() {
  cat <<'EOF'
Usage: bench/kissat/run_c11_guardrails.sh [OPTIONS]
  --gen-hpp PATH       C3b emitted *_gen.hpp (enables C3b harness, invariants, ext telemetry)
  --c4-bin PATH        Optional C4 native bench_main binary for C4==C3b parity checks
  --c3b-bin PATH       Optional prebuilt C3b bench_main binary (fallback if no --gen-hpp)
  --kissat PATH        Upstream Kissat 4.0.4 (C1) binary (auto-detected on PATH if omitted)
  --label NAME         Model prefix for canary checks (default: FullM4; e.g. FullM5, FullM6)
  --timeout SEC        Per-solver timeout in seconds (default: 15)
  --quick              Use --fast fuzzing grid
  --with-base          Also run check_canaries.py --include-c11 across all 40 canaries
  --skip-telem         Skip diff_telemetry.py even if --kissat is present
  --out-dir DIR        Save JSON/Markdown telemetry & fuzz reports in DIR
  -h, --help           Show this help
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --gen-hpp) GEN_HPP="$2"; shift 2 ;;
    --c4-bin) C4_BIN="$2"; shift 2 ;;
    --c3b-bin) C3B_BIN="$2"; shift 2 ;;
    --kissat) KISSAT_BIN="$2"; shift 2 ;;
    --label) LABEL="$2"; shift 2 ;;
    --timeout) PER_TIMEOUT="$2"; shift 2 ;;
    --quick) QUICK=1; shift ;;
    --with-base) WITH_BASE=1; shift ;;
    --skip-telem) SKIP_TELEM=1; shift ;;
    --out-dir) OUT_DIR="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown arg: $1" >&2; usage >&2; exit 2 ;;
  esac
done

if [[ -z "$KISSAT_BIN" ]]; then
  if command -v kissat >/dev/null 2>&1; then
    KISSAT_BIN="$(command -v kissat)"
  fi
fi

if [[ -z "$GEN_HPP" && -z "$C3B_BIN" && -z "$C4_BIN" ]]; then
  echo "Error: pass at least --gen-hpp, --c3b-bin, or --c4-bin" >&2
  exit 2
fi

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/kissat-c11-guardrails.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT
REPORT_DIR="${OUT_DIR:-$TMP_DIR/reports}"
mkdir -p "$REPORT_DIR" "$TMP_DIR/cnfs_base" "$TMP_DIR/cnfs_c11" "$TMP_DIR/cnfs_all"

echo "[1/5] Generating and verifying canary manifests (34 base / 6 c11 / 40 combined)..."
timeout 60 python3 -B bench/kissat/gen_canary_cnfs.py "$TMP_DIR/cnfs_base" --summary
timeout 60 python3 -B bench/kissat/gen_canary_cnfs.py "$TMP_DIR/cnfs_c11" --c11-only --summary
timeout 60 python3 -B bench/kissat/gen_canary_cnfs.py \
  "$TMP_DIR/cnfs_all" --include-c11 --summary
timeout 30 python3 -B -c '
import json, sys
for p, exp in [(sys.argv[1], 34), (sys.argv[2], 6), (sys.argv[3], 40)]:
    n = len(json.load(open(p))["canaries"])
    assert n == exp, f"{p}: expected {exp}, got {n}"
print("Manifest counts verified: base=34, c11=6, combined=40")
' "$TMP_DIR/cnfs_base/manifest.json" \
  "$TMP_DIR/cnfs_c11/manifest.json" \
  "$TMP_DIR/cnfs_all/manifest.json"

echo "[2/5] Compiling and unit-testing test/kissat/check_c3b_invariants.hpp (OFF + ON)..."
cat >"$TMP_DIR/test_inv.cpp" <<'EOF'
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>
#include "test/kissat/check_c3b_invariants.hpp"

struct MemBuf {
  const uint8_t* p;
  size_t sz;
  uint8_t read_byte(uint64_t a) const { return a < sz ? p[a] : 0; }
};

int main() {
  std::vector<uint8_t> buf(1 << 20, 0);
  uint64_t hdr = 64ULL;
  uint8_t* h = buf.data() + hdr;
  auto w64 = [&](uint64_t wi, uint64_t v) { std::memcpy(h + wi * 8ULL, &v, 8); };
  auto w32 = [&](uint64_t a, uint32_t v) { std::memcpy(buf.data() + a, &v, 4); };
  w64(kissat_c3b_inv::W_MAX_VARS, 4ULL);
  w64(kissat_c3b_inv::W_CUR_VARS, 2ULL);
  w64(kissat_c3b_inv::W_ARENA, hdr + 4096ULL);
  w64(kissat_c3b_inv::W_ARENA_CAP, 1024ULL);
  w64(kissat_c3b_inv::W_WATCH_STK, hdr + 8192ULL);
  w64(kissat_c3b_inv::W_WCAP, 64ULL);
  w64(kissat_c3b_inv::W_WATCH_VEC, hdr + 16384ULL);
  w64(kissat_c3b_inv::W_VALUES, hdr + 20480ULL);
  w64(kissat_c3b_inv::W_LEVEL, hdr + 24576ULL);
  uint64_t sb = hdr + 65536ULL;
  w64(kissat_c3b_inv::W_SCRATCH_BUF, sb);
  w64(kissat_c3b_inv::W_SCRATCH_CAP, 16384ULL);
  uint64_t kb = sb + 256ULL * 4ULL;
  w32(kb + 10u * 4ULL, 0xFFFFFFFFu);
  w32(kb + 11u * 4ULL, 0xFFFFFFFFu);
  w32(kb + 12u * 4ULL, 0xFFFFFFFFu);

  MemBuf mv{buf.data(), buf.size()};
  std::string err;
  if (!kissat_c3b_inv::check_2wl(mv, hdr, &err)) return 1;
  if (!kissat_c3b_inv::check_bins(mv, hdr, &err)) return 2;
  if (!kissat_c3b_inv::check_kitten(mv, hdr, &err)) return 3;
  auto snap = kissat_c3b_inv::check_probe_iso_begin(mv, hdr);
  if (!kissat_c3b_inv::check_probe_iso_end(mv, hdr, snap, &err)) return 4;
#ifdef KISSAT_C3B_CHECK_INV
  w64(kissat_c3b_inv::W_REL_WAIT, 77ULL);
  if (kissat_c3b_inv::check_probe_iso_end(mv, hdr, snap, &err)) return 5;
  w64(kissat_c3b_inv::W_REL_WAIT, 0ULL);
#endif
  w64(kissat_c3b_inv::W_ARENA, reinterpret_cast<uint64_t>(buf.data() + hdr + 4096ULL));
  w64(kissat_c3b_inv::W_WATCH_STK, reinterpret_cast<uint64_t>(buf.data() + hdr + 8192ULL));
  w64(kissat_c3b_inv::W_WATCH_VEC, reinterpret_cast<uint64_t>(buf.data() + hdr + 16384ULL));
  w64(kissat_c3b_inv::W_VALUES, reinterpret_cast<uint64_t>(buf.data() + hdr + 20480ULL));
  w64(kissat_c3b_inv::W_LEVEL, reinterpret_cast<uint64_t>(buf.data() + hdr + 24576ULL));
  w64(kissat_c3b_inv::W_SCRATCH_BUF, reinterpret_cast<uint64_t>(buf.data() + sb));
  if (!kissat_c3b_inv::check_2wl(h, &err)) return 6;
  if (!kissat_c3b_inv::check_bins(h, &err)) return 7;
  if (!kissat_c3b_inv::check_kitten(h, &err)) return 8;
  return 0;
}
EOF
CXX="${CXX:-clang++}"
timeout 60 "$CXX" -std=c++20 -O2 -Wall -Wextra -Werror -I"$ROOT" \
  "$TMP_DIR/test_inv.cpp" -o "$TMP_DIR/test_inv_off"
timeout 30 "$TMP_DIR/test_inv_off"
SAN_FLAGS=""
if timeout 30 "$CXX" -std=c++20 -fsanitize=address,undefined -x c++ - \
  -o "$TMP_DIR/san_probe" <<<'int main(){return 0;}' 2>/dev/null; then
  SAN_FLAGS="-fsanitize=address,undefined"
fi
timeout 60 "$CXX" -std=c++20 -O2 -Wall -Wextra -Werror $SAN_FLAGS -DKISSAT_C3B_CHECK_INV \
  -I"$ROOT" "$TMP_DIR/test_inv.cpp" -o "$TMP_DIR/test_inv_on"
timeout 30 "$TMP_DIR/test_inv_on"
echo "check_c3b_invariants.hpp compile+unit checks PASSED"
timeout 60 python3 -B - "$TMP_DIR" "$ROOT" <<'PYEOF'
import os, stat, subprocess, sys
tmp_dir, root = sys.argv[1], sys.argv[2]
sys.path.insert(0, os.path.join(root, "bench", "kissat"))
import check_canaries as cc
import diff_telemetry as dt

# Unit: detect_alarms flags C3b & C1 crash records
_, al3 = dt.detect_alarms(
    {"status": 20, "timeout": False, "crash": False},
    {"status": -1, "timeout": False, "crash": True, "ms": 0.0}, 5, 10,
)
assert any(a.startswith("C3B_CRASH(") for a in al3), al3
_, al1 = dt.detect_alarms(
    {"status": -1, "timeout": False, "crash": True, "ms": 0.0},
    {"status": 20, "timeout": False, "crash": False}, 5, 10,
)
assert any(a.startswith("C1_CRASH(") for a in al1), al1

# Unit: check_canaries merge_baseline_doc preserves base metadata under --c11-only
class Args:
    c11_only, include_c11, commit = True, False, "deadbeef"
    work_bytes, fuel, per_timeout = 123, 456, 99
prev = {"schema_version": 1, "base_commit": "abc", "work_bytes": 67108864,
        "fuel": 200000000, "per_timeout_sec": 5, "configs": [], "canaries": {}}
merged = cc.merge_baseline_doc(prev, {}, [("FullM5_C3b", "p", True)], Args)
assert (merged["work_bytes"], merged["fuel"], merged["per_timeout_sec"]) == (
    67108864, 200000000, 5), merged
assert cc.collect_parity_models([("FullM5_C3b", "p", True)]) == ["FullM5"]

# Mock CLI: --fail-on-critical and --fail-on-alarm exit 1 on rc=139
mdir = os.path.join(tmp_dir, "mock_telem")
cdir = os.path.join(mdir, "cnfs")
os.makedirs(cdir, exist_ok=True)
with open(os.path.join(cdir, "t.cnf"), "w") as f:
    f.write("p cnf 1 1\n1 0\n")
def mk(name, body):
    p = os.path.join(mdir, name)
    with open(p, "w") as f:
        f.write("#!/usr/bin/env bash\n" + body + "\n")
    os.chmod(p, os.stat(p).st_mode | stat.S_IXUSR)
    return p
k20, k139 = mk("k20", "exit 20"), mk("k139", "exit 139")
c20, c139 = mk("c20", 'printf "t.cnf\\t20\\t0.1\\n"; exit 0'), mk("c139", "exit 139")
script = os.path.join(root, "bench", "kissat", "diff_telemetry.py")
for kb, cb, flag, tag in [
    (k20, c139, "--fail-on-critical", "C3B_CRASH(status=139)"),
    (k20, c139, "--fail-on-alarm", "C3B_CRASH(status=139)"),
    (k139, c20, "--fail-on-critical", "C1_CRASH(status=139)"),
]:
    pr = subprocess.run(
        ["timeout", "30", sys.executable, "-B", script, "--kissat", kb,
         "--c3b-bin", cb, "--cnf-dir", cdir, flag],
        capture_output=True, text=True,
    )
    assert pr.returncode == 1 and tag in (pr.stdout + pr.stderr), (
        flag, tag, pr.returncode, pr.stdout, pr.stderr)
print("Harness crash/metadata regression checks PASSED")
PYEOF

echo "[3/5] Running check_canaries.py (--c11-only)..."
CANARY_ARGS=(--per-timeout "$PER_TIMEOUT")
if [[ -n "$KISSAT_BIN" ]]; then
  CANARY_ARGS+=(--kissat "$KISSAT_BIN")
fi
if [[ -n "$C4_BIN" ]]; then
  case "$LABEL" in
    FullM3) CANARY_ARGS+=(--m3-c4 "$C4_BIN") ;;
    FullM4) CANARY_ARGS+=(--m4-c4 "$C4_BIN") ;;
    FullM5) CANARY_ARGS+=(--m5-c4 "$C4_BIN") ;;
    FullM6) CANARY_ARGS+=(--m6-c4 "$C4_BIN") ;;
    FullFast) CANARY_ARGS+=(--fast-c4 "$C4_BIN") ;;
    *) CANARY_ARGS+=(--full-c4 "$C4_BIN") ;;
  esac
fi
if [[ -n "$C3B_BIN" ]]; then
  case "$LABEL" in
    FullM3) CANARY_ARGS+=(--m3-c3b "$C3B_BIN") ;;
    FullM4) CANARY_ARGS+=(--m4-c3b "$C3B_BIN") ;;
    FullM5) CANARY_ARGS+=(--m5-c3b "$C3B_BIN") ;;
    FullM6) CANARY_ARGS+=(--m6-c3b "$C3B_BIN") ;;
    FullFast) CANARY_ARGS+=(--fast-c3b "$C3B_BIN") ;;
    *) CANARY_ARGS+=(--full-c3b "$C3B_BIN") ;;
  esac
elif [[ -n "$GEN_HPP" ]]; then
  CANARY_ARGS+=(--c3b-gen-hpp "${LABEL}_C3b=$GEN_HPP")
fi
timeout 300 python3 -B bench/kissat/check_canaries.py \
  --cnf-dir "$TMP_DIR/cnfs_all" --c11-only "${CANARY_ARGS[@]}"
if [[ "$WITH_BASE" -eq 1 ]]; then
  echo "Running check_canaries.py (--include-c11, all 40)..."
  timeout 600 python3 -B bench/kissat/check_canaries.py \
    --cnf-dir "$TMP_DIR/cnfs_all" --include-c11 "${CANARY_ARGS[@]}"
fi

echo "[4/5] Running fuzz_oom_witness.py OOM/witness/invariant guardrails..."
FUZZ_COMMON=(--timeout "$PER_TIMEOUT")
if [[ -n "$KISSAT_BIN" ]]; then
  FUZZ_COMMON+=(--kissat "$KISSAT_BIN")
fi
if [[ "$QUICK" -eq 1 ]]; then
  FUZZ_COMMON+=(--fast)
fi
if [[ -n "$GEN_HPP" ]]; then
  timeout 300 python3 -B test/kissat/fuzz_oom_witness.py \
    --gen-hpp "$GEN_HPP" "${FUZZ_COMMON[@]}" \
    --check-oom-monotone --check-inv --check-search-inv \
    --json-out "$REPORT_DIR/fuzz_default.json"
  timeout 300 python3 -B test/kissat/fuzz_oom_witness.py \
    --gen-hpp "$GEN_HPP" --cnfs-dir "$TMP_DIR/cnfs_c11" "${FUZZ_COMMON[@]}" \
    --check-oom-monotone --check-inv --check-search-inv \
    --json-out "$REPORT_DIR/fuzz_c11.json"
  timeout 180 python3 -B test/kissat/fuzz_oom_witness.py \
    --gen-hpp "$GEN_HPP" --fast --check-oom-monotone --test-oom-sticky \
    --json-out "$REPORT_DIR/fuzz_sticky.json"
elif [[ -n "$C3B_BIN" ]]; then
  timeout 300 python3 -B test/kissat/fuzz_oom_witness.py \
    --c3b-bin "$C3B_BIN" "${FUZZ_COMMON[@]}" \
    --json-out "$REPORT_DIR/fuzz_default.json"
  timeout 300 python3 -B test/kissat/fuzz_oom_witness.py \
    --c3b-bin "$C3B_BIN" --cnfs-dir "$TMP_DIR/cnfs_c11" "${FUZZ_COMMON[@]}" \
    --json-out "$REPORT_DIR/fuzz_c11.json"
else
  echo "Skipping fuzz_oom_witness.py (no --gen-hpp or --c3b-bin given)"
fi

if [[ "$SKIP_TELEM" -eq 0 && -n "$KISSAT_BIN" && ( -n "$GEN_HPP" || -n "$C3B_BIN" ) ]]; then
  echo "[5/5] Running diff_telemetry.py (--c11-only)..."
  TELEM_ARGS=(--kissat "$KISSAT_BIN" --c11-only --timeout "$PER_TIMEOUT" --fail-on-critical)
  if [[ -n "$GEN_HPP" ]]; then
    TELEM_ARGS+=(--gen-hpp "$GEN_HPP" --extended-telemetry)
  else
    TELEM_ARGS+=(--c3b-bin "$C3B_BIN")
  fi
  timeout 300 python3 -B bench/kissat/diff_telemetry.py \
    "${TELEM_ARGS[@]}" \
    --json-out "$REPORT_DIR/telem_c11.json" \
    --md-out "$REPORT_DIR/telem_c11.md"
else
  echo "[5/5] Skipping diff_telemetry.py (--skip-telem or missing --kissat/C3b target)"
fi

echo "ALL C11 GUARDRAILS PASSED (reports in $REPORT_DIR)"
