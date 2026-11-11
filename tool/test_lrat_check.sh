#!/usr/bin/env bash
# Build and test `tool/lrat_check.rs` (unit tests, CLI edge cases, differential
# check against stock QBE, and a synthetic multi-thousand-clause UNSAT benchmark).
# All builds and test runs execute under `timeout`.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

TMP="$(mktemp -d "${TMPDIR:-/tmp}/lrat-check-test.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT

if [ ! -x "$ROOT/.lake/build/bin/leanqbe" ]; then
  timeout 1800 lake build leanqbe
fi

echo "== 1. Build lean-qbe and stock-QBE variants + Rust unit tests"
timeout 60 "$ROOT/.lake/build/bin/leanqbe" lrat_bytes >"$TMP/lrat_bytes.s"
timeout 60 cc -c "$TMP/lrat_bytes.s" -o "$TMP/lrat_bytes.o"

timeout 120 rustc --edition 2021 --test -C link-arg="$TMP/lrat_bytes.o" \
  "$ROOT/tool/lrat_check.rs" -o "$TMP/lrat_check_unit"
timeout 60 "$TMP/lrat_check_unit"

timeout 300 "$ROOT/tool/build_lrat_check.sh" --out "$TMP/lrat_check_ours"
(cd "$TMP" && timeout 300 "$ROOT/tool/build_lrat_check.sh" --out ./rel_lrat_check >/dev/null)
test -x "$TMP/rel_lrat_check"
timeout 300 "$ROOT/tool/build_lrat_check.sh" --qbe --out "$TMP/lrat_check_qbe"

echo "== 2. CLI integration tests (lean-qbe & stock QBE)"
timeout 120 python3 - "$TMP/lrat_check_ours" "$TMP/lrat_check_qbe" "$TMP" <<'PY'
import pathlib, subprocess, sys

ours = sys.argv[1]
qbe = sys.argv[2]
tmp = pathlib.Path(sys.argv[3])

def leb(n: int) -> bytes:
    out = bytearray()
    while True:
        b = n & 0x7f
        n >>= 7
        if n:
            b |= 0x80
        out.append(b)
        if not n:
            return bytes(out)

def lit(x: int) -> bytes:
    if x == 0:
        return b"\x00"
    v = abs(x)
    return leb((v << 1) | (1 if x < 0 else 0))

def add_step(cid: int, lits: list[int], hints: list[int]) -> bytes:
    return b"a" + leb(2 * cid) + b"".join(lit(x) for x in lits) + b"\x00" + b"".join(leb(2 * h) for h in hints) + b"\x00"

def del_step(cids: list[int]) -> bytes:
    return b"d" + b"".join(leb(2 * c) for c in cids) + b"\x00"

def run(bin_path, args, stdin_bytes=None):
    return subprocess.run([bin_path, *args], input=stdin_bytes, capture_output=True, timeout=30)

# 1. Valid 1-var and 2-var UNSAT instances
cnf1 = tmp / "u1.cnf"
prf1 = tmp / "u1.lrat"
cnf1.write_bytes(b"p cnf 1 2\n1 0\n-1 0\n")
prf1.write_bytes(add_step(3, [1], [1]) + del_step([1]) + add_step(4, [], [3, 2]))

cnf2 = tmp / "u2.cnf"
prf2 = tmp / "u2.lrat"
cnf2.write_bytes(
    b"c leading comment\r\n"
    b"  p \t cnf  2   4 \r\n"
    b"1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n"
    b"c trailing comment"
)
prf2.write_bytes(
    add_step(5, [2], [1, 2])
    + del_step([1, 2])
    + add_step(6, [-2], [3, 4])
    + add_step(7, [], [5, 6])
)

# 2. Invalid LRAT / malformed DIMACS
bad_prf = tmp / "bad.lrat"
bad_prf.write_bytes(add_step(3, [], [1]))

empty_f = tmp / "empty"
empty_f.write_bytes(b"")

bogus_hdr = tmp / "bogus_hdr.cnf"
bogus_hdr.write_bytes(b"p cnf 268435455 268435455\n1 0\n")

# Leading-dash filename test
dash_cnf = tmp / "-dash.cnf"
dash_cnf.write_bytes(cnf1.read_bytes())

# 3. Synthetic 5000-step chain UNSAT (mirrors bench/lrat_bench.c)
M = 5000
chain_lines = [f"p cnf {5 + M} {7 + M}\n"]
for i in range(1, 6):
    chain_lines.append(f"{i} 0\n")
for s in range(1, M + 1):
    chain_lines.append(f"-1 -2 -3 -4 -{4 + s} {5 + s} 0\n")
chain_lines.append(f"-1 -2 -3 -4 -{5 + M} 0\n")
chain_lines.append("1 2 0\n")  # unused clause
chain_cnf = tmp / "chain.cnf"
chain_cnf.write_text("".join(chain_lines))

chain_prf_parts = []
first_id = 8 + M
for s in range(1, M + 1):
    cid = 7 + M + s
    prev = 5 if s == 1 else (6 + M + s)
    chain_prf_parts.append(add_step(cid, [5 + s], [1, 2, 3, 4, prev, 5 + s]))
chain_prf_parts.append(add_step(8 + 2 * M, [1], [1]))  # extra clause
chain_prf_parts.append(add_step(9 + 2 * M, [], [1, 2, 3, 4, 7 + 2 * M, 6 + M]))
chain_prf = tmp / "chain.lrat"
chain_prf.write_bytes(b"".join(chain_prf_parts))

for label, bin_path in [("leanqbe", ours), ("stock-qbe", qbe)]:
    r = run(bin_path, ["--help"])
    assert r.returncode == 0 and b"usage: lrat_check" in r.stdout, (label, r)

    for c, p in [(cnf1, prf1), (cnf2, prf2), (chain_cnf, chain_prf)]:
        r = run(bin_path, [str(c), str(p)])
        assert r.returncode == 0 and r.stdout == b"s VERIFIED\n", (label, c, r)

    r = run(bin_path, ["-q", str(cnf1), str(prf1)])
    assert r.returncode == 0 and r.stdout == b"" and r.stderr == b"", (label, r)

    r = run(bin_path, ["-v", str(chain_cnf), str(chain_prf)])
    assert r.returncode == 0 and b"s VERIFIED\n" in r.stdout and b"c time " in r.stdout, (label, r)
    for line in r.stdout.decode().splitlines():
        if line.startswith("c time ") or line.startswith("c work "):
            print(f"[{label}] {line}")

    # Stdin '-' for cnf, and '-' for prf
    r = run(bin_path, ["-", str(prf1)], stdin_bytes=cnf1.read_bytes())
    assert r.returncode == 0 and r.stdout == b"s VERIFIED\n", (label, r)
    r = run(bin_path, [str(cnf1), "-"], stdin_bytes=prf1.read_bytes())
    assert r.returncode == 0 and r.stdout == b"s VERIFIED\n", (label, r)

    # `--` separator for leading-dash file
    r = run(bin_path, ["--", str(dash_cnf), str(prf1)])
    assert r.returncode == 0 and r.stdout == b"s VERIFIED\n", (label, r)

    # 0-var UNSAT and header-only huge mv rejection (must not 1.34 GiB OOM)
    zero_cnf = tmp / "zero_var.cnf"
    zero_cnf.write_bytes(b"p cnf 0 1\n0")
    zero_prf = tmp / "zero_var.lrat"
    zero_prf.write_bytes(add_step(2, [], [1]))
    r = run(bin_path, [str(zero_cnf), str(zero_prf)])
    assert r.returncode == 0 and r.stdout == b"s VERIFIED\n", (label, r)

    hdr_only_huge_mv = tmp / "hdr_only_huge_mv.cnf"
    hdr_only_huge_mv.write_bytes(b"p cnf 268435455 1\n")
    r = run(bin_path, ["-v", str(hdr_only_huge_mv), str(prf1)])
    assert r.returncode == 1 and b"c work 4096 bytes\n" in r.stdout and b"s NOT VERIFIED\n" in r.stdout, (label, r)

    # Rejections (exit 1)
    for c, p in [(cnf1, bad_prf), (empty_f, prf1), (cnf1, empty_f), (bogus_hdr, prf1)]:
        r = run(bin_path, [str(c), str(p)])
        assert r.returncode == 1 and r.stdout == b"s NOT VERIFIED\n", (label, c, p, r)

    r = run(bin_path, ["-q", str(cnf1), str(bad_prf)])
    assert r.returncode == 1 and r.stdout == b"", (label, r)

    for wb in ["0", "64", "127"]:
        r = run(bin_path, ["--work-bytes", wb, str(cnf1), str(prf1)])
        assert r.returncode == 1 and r.stdout == b"s NOT VERIFIED\n", (label, wb, r)

    r = run(bin_path, ["--work-bytes=1024", str(cnf1), str(prf1)])
    assert r.returncode == 0 and r.stdout == b"s VERIFIED\n", (label, r)

    # CLI / I/O / OOM errors (exit 2, never SIGABRT)
    for bad_args in [
        [],
        [str(cnf1)],
        [str(cnf1), str(prf1), str(tmp / "trimmed.lrat")],
        ["-", "-"],
        ["-S", str(cnf1), str(prf1)],
        ["--strict", str(cnf1), str(prf1)],
        ["-f", str(cnf1), str(prf1)],
        ["--bogus", str(cnf1), str(prf1)],
        ["--work-bytes", "notanumber", str(cnf1), str(prf1)],
        ["--work-bytes", str(1 << 62), str(cnf1), str(prf1)],
        ["--work-bytes", str((1 << 63) - 1), str(cnf1), str(prf1)],
        [str(tmp / "does_not_exist.cnf"), str(prf1)],
        [str(cnf1), str(tmp / "does_not_exist.lrat")],
    ]:
        r = run(bin_path, bad_args)
        assert r.returncode == 2 and len(r.stderr) > 0, (label, bad_args, r)

print("ALL CLI INTEGRATION TESTS PASSED")
PY
