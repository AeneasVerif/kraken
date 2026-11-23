#!/usr/bin/env bash
# Self-contained L1 verification for bench/kissat/build_solver.sh and bench/kissat/kissat_cli.c.
#
# Builds FullM5 (certified), FullM6, and FullM7 (--allow-uncertified until Sound certs land) on
# both x64 and arm64 (qemu-aarch64), verifying SAT/UNSAT/UNKNOWN exit codes, DIMACS `v ... 0`
# models on sat_unit/sat_chain/multi-clause SAT canary, `-n`/`--no-model`, stdin `-`, and
# guard-page safety.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

BUILD_TIMEOUT="${BUILD_TIMEOUT:-600}"
RUN_TIMEOUT="${RUN_TIMEOUT:-30}"

TMP="$(mktemp -d "${TMPDIR:-/tmp}/kissat-cli-test.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT

echo "== [1/4] certification gating & CLI argument checks =="
for mod_pair in "FullM6:KissatM6Sound" "FullM7:KissatM7Sound"; do
  mod="${mod_pair%%:*}"
  sound="${mod_pair#*:}"
  for pair in "x64:Amd64" "arm64:Arm64"; do
    arch="${pair%%:*}"
    arch_dir="${pair#*:}"
    if [ ! -f "LeanQbe/T/$arch_dir/${sound}.lean" ]; then
      set +e
      err_out="$(timeout "$RUN_TIMEOUT" bash bench/kissat/build_solver.sh \
        --module "$mod" --arch "$arch" -o "$TMP/should_fail" 2>&1)"
      rc=$?
      set -e
      if [ "$rc" -ne 2 ]; then
        echo "FAIL: expected exit 2 for uncertified $mod ($arch), got $rc" >&2
        echo "$err_out" >&2
        exit 1
      fi
      grep -q -- '--allow-uncertified' <<<"$err_out" || {
        echo "FAIL: missing --allow-uncertified hint for $mod ($arch)" >&2
        exit 1
      }
    fi
  done
done

echo "== [2/4] build FullM5 (certified), FullM6, and FullM7 on x64 + arm64 =="
if [ -z "${STAGE_LEAN_PATH:-}" ]; then
  if [ "${SKIP_BUILD:-0}" != "1" ]; then
    EXTRA_BUILD_MODS=()
    [ ! -f "LeanQbe/T/Examples/Kissat/FullM7Inl.lean" ] || \
      EXTRA_BUILD_MODS+=(LeanQbe.T.Examples.Kissat.FullM7Inl)
    [ ! -f "LeanQbe/T/Examples/Kissat/FullM7InlPolicy.lean" ] || \
      EXTRA_BUILD_MODS+=(LeanQbe.T.Examples.Kissat.FullM7InlPolicy)
    timeout "$BUILD_TIMEOUT" lake build --wfail \
      LeanQbe.T.Examples.Kissat.FullM5 LeanQbe.T.Examples.Kissat.FullM6 \
      LeanQbe.T.Examples.Kissat.FullM7 LeanQbe.T.Opt LeanQbe.T.Driver \
      LeanQbe.T.MainInline LeanQbe.T.Examples.Kissat.FullM6Inl \
      LeanQbe.T.Amd64.Targ LeanQbe.T.Amd64.PrintATTAlign \
      LeanQbe.T.Arm64.Targ Kraken.AArch64.Print "${EXTRA_BUILD_MODS[@]}"
  fi
  STAGE_LEAN_PATH="$(timeout "$RUN_TIMEOUT" lake env printenv LEAN_PATH)"
  export STAGE_LEAN_PATH
fi

M6_X64_FLAGS=()
[ -f "LeanQbe/T/Amd64/KissatM6Sound.lean" ] || M6_X64_FLAGS=(--allow-uncertified)
M6_ARM64_FLAGS=()
[ -f "LeanQbe/T/Arm64/KissatM6Sound.lean" ] || M6_ARM64_FLAGS=(--allow-uncertified)
M7_X64_FLAGS=()
[ -f "LeanQbe/T/Amd64/KissatM7Sound.lean" ] || M7_X64_FLAGS=(--allow-uncertified)
M7_ARM64_FLAGS=()
[ -f "LeanQbe/T/Arm64/KissatM7Sound.lean" ] || M7_ARM64_FLAGS=(--allow-uncertified)

run_build_wave() {
  local pids=() tags=() logs=()
  while [ $# -gt 0 ]; do
    local tag="$1"
    shift
    local log="$TMP/build_${tag}.log"
    tags+=("$tag")
    logs+=("$log")
    local args=()
    while [ $# -gt 0 ] && [ "$1" != "::" ]; do
      args+=("$1")
      shift
    done
    [ $# -gt 0 ] && shift
    timeout "$BUILD_TIMEOUT" bash bench/kissat/build_solver.sh "${args[@]}" >"$log" 2>&1 &
    pids+=("$!")
  done
  local fail=0 i
  for i in "${!pids[@]}"; do
    if wait "${pids[$i]}"; then
      cat "${logs[$i]}"
    else
      echo "FAIL: build ${tags[$i]} failed:" >&2
      cat "${logs[$i]}" >&2
      fail=1
    fi
  done
  [ "$fail" -eq 0 ] || exit 1
}

run_build_wave \
  "m7-x64" --module FullM7 --arch x64 ${M7_X64_FLAGS[@]+"${M7_X64_FLAGS[@]}"} \
    -o "$TMP/kissat-m7-x64" :: \
  "m7-arm64" --module m7 --arch arm64 ${M7_ARM64_FLAGS[@]+"${M7_ARM64_FLAGS[@]}"} \
    -o "$TMP/kissat-m7-arm64" :: \
  "m5-x64" --module FullM5 --arch x64 -o "$TMP/kissat-m5-x64"

run_build_wave \
  "m5-arm64" --module m5 --arch arm64 -o "$TMP/kissat-m5-arm64" :: \
  "m6-x64" --module FullM6 --arch x64 ${M6_X64_FLAGS[@]+"${M6_X64_FLAGS[@]}"} \
    -o "$TMP/kissat-m6-x64" :: \
  "m6-arm64" --module m6 --arch arm64 ${M6_ARM64_FLAGS[@]+"${M6_ARM64_FLAGS[@]}"} \
    -o "$TMP/kissat-m6-arm64"

echo "== [3/4] generate SAT/UNSAT/UNKNOWN/guard-page CNF corpus =="
CDIR="$TMP/cnfs"
mkdir -p "$CDIR"
timeout "$RUN_TIMEOUT" python3 -B - "$CDIR" <<'PY'
import os, random, sys

cdir = sys.argv[1]

def w(name, txt):
    with open(os.path.join(cdir, name), "wb") as f:
        f.write(txt.encode("ascii"))

w("sat_zero.cnf", "p cnf 0 0\n")
w("sat_unit.cnf", "p cnf 1 1\n1 0\n")
w("sat_no_nl.cnf", "p cnf 1 1\n1 0")
w("sat_chain.cnf", "p cnf 4 4\n-1 2 0\n-2 3 0\n-3 4 0\n1 2 3 4 0\n")
w("unsat_unit.cnf", "p cnf 1 2\n1 0\n-1 0\n")
w("unsat_php3.cnf",
  "p cnf 6 9\n1 2 0\n3 4 0\n5 6 0\n-1 -3 0\n-1 -5 0\n-3 -5 0\n-2 -4 0\n-2 -6 0\n-4 -6 0\n")
w("bad_hdr.cnf", "p sat 1 1\n")
w("empty.cnf", "")
w("oversize_work.cnf", "p cnf 1000000 1\n1 0\n")

# Multi-clause SAT canary (32 vars, 128 clauses) exercising propagation, decisions,
# conflict backtracking, and multi-line DIMACS `v ...` wrapping.
rng = random.Random(20261123)
mv = 32
assign = {v: ((v * 7 + 3) % 2 == 0) for v in range(1, mv + 1)}
clauses = []
for v in range(1, mv):
    s1 = v if assign[v] else -v
    s2 = (v + 1) if assign[v + 1] else -(v + 1)
    clauses.append([-s1, s2])
while len(clauses) < 128:
    vs = rng.sample(range(1, mv + 1), 3)
    lits = [v if rng.randrange(2) else -v for v in vs]
    if any((l > 0) == assign[abs(l)] for l in lits):
        clauses.append(lits)
lines = [f"c multi-clause SAT canary\np cnf {mv} {len(clauses)}"]
lines.extend(" ".join(str(x) for x in cl) + " 0" for cl in clauses)
w("sat_multi.cnf", "\n".join(lines) + "\n")
PY

echo "== [4/4] verify exit codes, DIMACS models, -n, stdin -, and guard pages =="
timeout 360 python3 -B - "$TMP" "$CDIR" "$RUN_TIMEOUT" <<'PY'
import os, subprocess, sys

tmp, cdir, run_to = sys.argv[1], sys.argv[2], sys.argv[3]

def parse_dimacs(path):
    raw = open(path, "r", encoding="ascii").read()
    lines = [l for l in raw.splitlines() if l.strip() and not l.lstrip().startswith("c")]
    hdr = lines[0].split()
    assert hdr[0] == "p" and hdr[1] == "cnf"
    mv, nc = int(hdr[2]), int(hdr[3])
    toks = " ".join(lines[1:]).split()
    clauses, cur = [], []
    for t in toks:
        v = int(t)
        if v == 0:
            clauses.append(cur)
            cur = []
        else:
            cur.append(v)
    assert not cur and len(clauses) == nc
    return mv, clauses

def check_model_output(stdout, cnf_path):
    mv, clauses = parse_dimacs(cnf_path)
    slines = [l for l in stdout.splitlines() if l.startswith("s ")]
    vlines = [l for l in stdout.splitlines() if l.startswith("v ")]
    assert slines == ["s SATISFIABLE"], f"unexpected s-lines: {slines!r}"
    assert vlines, f"missing v-lines in stdout:\n{stdout}"
    toks = []
    for vl in vlines:
        assert len(vl) <= 80, f"v-line exceeds 80 cols: {vl!r}"
        toks.extend(int(x) for x in vl[2:].split())
    assert toks and toks[-1] == 0, f"model missing trailing 0: {toks!r}"
    vals = {}
    for lit in toks[:-1]:
        assert lit != 0 and 1 <= abs(lit) <= mv, f"out-of-range lit {lit} (mv={mv})"
        v = abs(lit)
        pol = lit > 0
        assert v not in vals, f"duplicate var {v} in v-lines"
        vals[v] = pol
    assert len(vals) == mv, f"assigned {len(vals)} != mv={mv}"
    for idx, cl in enumerate(clauses):
        assert any(vals[abs(l)] == (l > 0) for l in cl), (
            f"clause {idx} ({cl}) unsatisfied by model for {cnf_path}"
        )

def run_bin(base_cmd, args, stdin_bytes=None):
    return subprocess.run(
        ["timeout", run_to] + base_cmd + args,
        input=stdin_bytes,
        capture_output=True,
    )

targets = [
    ("FullM5-x64", [f"{tmp}/kissat-m5-x64"]),
    ("FullM5-arm64", ["qemu-aarch64", "-L", "/usr/aarch64-linux-gnu", f"{tmp}/kissat-m5-arm64"]),
    ("FullM6-x64", [f"{tmp}/kissat-m6-x64"]),
    ("FullM6-arm64", ["qemu-aarch64", "-L", "/usr/aarch64-linux-gnu", f"{tmp}/kissat-m6-arm64"]),
    ("FullM7-x64", [f"{tmp}/kissat-m7-x64"]),
    ("FullM7-arm64", ["qemu-aarch64", "-L", "/usr/aarch64-linux-gnu", f"{tmp}/kissat-m7-arm64"]),
]

for label, cmd in targets:
    for cname in (
        "sat_zero.cnf", "sat_unit.cnf", "sat_no_nl.cnf", "sat_chain.cnf", "sat_multi.cnf"
    ):
        p = os.path.join(cdir, cname)
        r = run_bin(cmd, [p])
        assert r.returncode == 10, f"{label} {cname}: rc={r.returncode} stderr={r.stderr!r}"
        check_model_output(r.stdout.decode("ascii"), p)

    # -n and --no-model suppress `v ...` lines while keeping `s SATISFIABLE` and rc=10.
    for flag, cname in (("-n", "sat_chain.cnf"), ("--no-model", "sat_multi.cnf")):
        p = os.path.join(cdir, cname)
        r = run_bin(cmd, [flag, p])
        assert r.returncode == 10, f"{label} {flag}: rc={r.returncode}"
        out = r.stdout.decode("ascii")
        assert out == "s SATISFIABLE\n", f"{label} {flag}: unexpected stdout {out!r}"

    # UNSAT cases -> rc=20 and `s UNSATISFIABLE`.
    for cname in ("unsat_unit.cnf", "unsat_php3.cnf"):
        p = os.path.join(cdir, cname)
        r = run_bin(cmd, [p])
        assert r.returncode == 20, f"{label} {cname}: rc={r.returncode}"
        out = r.stdout.decode("ascii")
        assert out == "s UNSATISFIABLE\n", f"{label} {cname}: unexpected stdout {out!r}"

    # Stdin `-` for both SAT and UNSAT.
    p_sat = os.path.join(cdir, "sat_chain.cnf")
    r_stdin_sat = run_bin(cmd, ["-"], stdin_bytes=open(p_sat, "rb").read())
    assert r_stdin_sat.returncode == 10, f"{label} stdin SAT: rc={r_stdin_sat.returncode}"
    check_model_output(r_stdin_sat.stdout.decode("ascii"), p_sat)

    p_unsat = os.path.join(cdir, "unsat_unit.cnf")
    r_stdin_unsat = run_bin(cmd, ["-"], stdin_bytes=open(p_unsat, "rb").read())
    assert r_stdin_unsat.returncode == 20, f"{label} stdin UNSAT: rc={r_stdin_unsat.returncode}"
    assert r_stdin_unsat.stdout.decode("ascii") == "s UNSATISFIABLE\n"

    # UNKNOWN (rc=0): --fuel 0, malformed header, empty file, and tight workspace OOM guard.
    unknown_cases = [
        (["--fuel", "0", os.path.join(cdir, "sat_chain.cnf")], "fuel0"),
        ([os.path.join(cdir, "bad_hdr.cnf")], "bad_hdr"),
        ([os.path.join(cdir, "empty.cnf")], "empty"),
        (["--work-mb", "1", os.path.join(cdir, "oversize_work.cnf")], "oversize_work"),
    ]
    for args, tag in unknown_cases:
        r = run_bin(cmd, args)
        assert r.returncode == 0, f"{label} {tag}: rc={r.returncode} stderr={r.stderr!r}"
        assert r.stdout.decode("ascii") == "s UNKNOWN\n", f"{label} {tag}: {r.stdout!r}"

    # Tight guarded 1 MB workspace still solves SAT and UNSAT cleanly without hitting PROT_NONE.
    p_multi = os.path.join(cdir, "sat_multi.cnf")
    r_w1_sat = run_bin(cmd, ["--work-mb", "1", p_multi])
    assert r_w1_sat.returncode == 10, f"{label} work1 SAT: rc={r_w1_sat.returncode}"
    check_model_output(r_w1_sat.stdout.decode("ascii"), p_multi)

    p_php = os.path.join(cdir, "unsat_php3.cnf")
    r_w1_unsat = run_bin(cmd, ["--work-mb", "1", p_php])
    assert r_w1_unsat.returncode == 20, f"{label} work1 UNSAT: rc={r_w1_unsat.returncode}"
    assert r_w1_unsat.stdout.decode("ascii") == "s UNSATISFIABLE\n"

    print(f"PASS: {label}")
PY

echo "== test/kissat/test_cli_solver.sh: ALL PASSED =="
