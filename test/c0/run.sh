#!/usr/bin/env bash
# C0 frontend layout parity, C0/C99/C++20 compilation, and differential test suite.
# Writes all generated C++ headers, object files, and binaries strictly under /tmp/.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-c0.XXXXXX")}"
mkdir -p "$OUT/logs"
echo "outputs in $OUT"

echo "== 1. build C0 frontend & C0Test, generate C++20 headers into $OUT =="
if [ "${SKIP_BUILD:-0}" != "1" ]; then
  timeout 300 lake build --wfail LeanQbe.T.Frontend.C0 LeanQbeTest.T.C0Test
else
  echo "SKIP_BUILD=1: skipping lake build LeanQbe.T.Frontend.C0 LeanQbeTest.T.C0Test"
fi
timeout 120 lake env lean --run LeanQbeTest/T/C0Test.lean "$OUT"

C99_FLAGS="-std=c99 -O2 -fwrapv -fno-strict-aliasing -Wall -Wextra -Werror"
C11_FLAGS="-std=c11 -O2 -fwrapv -fno-strict-aliasing -Wall -Wextra -Werror"
CPP_INC="-I$ROOT/LeanQbe/T/Runtime -I$ROOT/LeanQbe/T/Frontend/C0 -I$ROOT/test/c0 -I$OUT"
CPP_FLAGS="-std=c++20 -O2 -Wall -Wextra -Werror $CPP_INC"

run_v1_d2() {
  echo "== 2. (V1) compile & run C99/C11 layout parity checks (gcc + clang ASan/UBSan) =="
  (
    timeout 60 gcc $C99_FLAGS "$ROOT/test/c0/test_layout_check.c" -o "$OUT/layout_gcc_c99"
    timeout 60 "$OUT/layout_gcc_c99"
  ) &
  local p1=$!
  (
    timeout 60 gcc $C11_FLAGS "$ROOT/test/c0/test_layout_check.c" -o "$OUT/layout_gcc_c11"
    timeout 60 "$OUT/layout_gcc_c11"
  ) &
  local p2=$!
  (
    timeout 60 clang $C99_FLAGS -fsanitize=undefined,address \
      "$ROOT/test/c0/test_layout_check.c" -o "$OUT/layout_clang"
    timeout 60 "$OUT/layout_clang"
  ) &
  local p3=$!
  wait "$p1"; wait "$p2"; wait "$p3"

  cat > "$OUT/d2_main.cpp" <<'EOF'
#include "c0.h"
#include "d2_diff.h"
int main() { return run_d2_tests(); }
EOF

  echo "== 3. (D2) compile native C99 fixtures & run C++20 differential suite =="
  echo "   (gcc+g++ and clang+clang++ ASan/UBSan)"
  run_d2_pair() {
    local CC="$1" CXX="$2" EXTRA="$3"
    local src_pids=()
    echo "--- [$CC / $CXX ${EXTRA:-O2}] ---"
    for src in test_layout.c proplit.c lean_rc.c v4_sum_pos64.c extra_cf.c; do
      timeout 60 "$CC" $C99_FLAGS $EXTRA -c "$ROOT/test/c0/$src" -o "$OUT/${src%.c}.$CC.o" &
      src_pids+=($!)
    done
    for pid in "${src_pids[@]}"; do wait "$pid"; done
    timeout 60 "$CXX" $CPP_FLAGS $EXTRA \
      "$OUT/d2_main.cpp" \
      "$OUT/test_layout.$CC.o" \
      "$OUT/proplit.$CC.o" \
      "$OUT/lean_rc.$CC.o" \
      "$OUT/v4_sum_pos64.$CC.o" \
      "$OUT/extra_cf.$CC.o" \
      -o "$OUT/d2_runner_$CXX"
    timeout 60 "$OUT/d2_runner_$CXX"
  }
  run_d2_pair gcc g++ "" >"$OUT/logs/d2_gcc.log" 2>&1 &
  local pd1=$!
  run_d2_pair clang clang++ "-fsanitize=undefined,address" >"$OUT/logs/d2_clang.log" 2>&1 &
  local pd2=$!
  local d2_fail=0
  wait "$pd1" || d2_fail=1
  wait "$pd2" || d2_fail=1
  cat "$OUT/logs/d2_gcc.log"
  cat "$OUT/logs/d2_clang.log"
  return "$d2_fail"
}

run_neg_diag() {
  echo "== 5. (Negative diagnostics) verify #203 token-level parse & register bitfield errors =="
  cat > "$OUT/neg_diag.lean" <<'EOF'
import LeanQbe.T.Frontend.C0
open LeanQbe.T.Frontend.C0

private def assertErrContains (label : String) (r : Except String α)
    (subs : List String) : IO Unit := do
  match r with
  | .ok _ => throw (IO.userError s!"{label}: expected failure, got .ok")
  | .error e =>
    for s in subs do
      if (e.splitOn s).length ≤ 1 then
        throw (IO.userError s!"{label}: error '{e}' missing '{s}'")

def main : IO Unit := do
  assertErrContains "parse-tok" (parseC0 "u32 f(u32 x) { return x + ; }")
    ["line 1", "symbol ';'"]
  assertErrContains "parse-do" (parseC0 "u32 f(u32 x) { do { x = 1; } x; }")
    ["while", "identifier 'x'"]
  let bfSrc :=
    "typedef struct { u32 x : 5; u32 y : 27; } bf_t; u32 f(bf_t v) { v.x += 3; return v.x; }"
  let regSrc := "typedef struct { u32 x; u32 y; } p_t; u32 f(p_t v) { v.x += 3; return v.x; }"
  assertErrContains "reg-bf" (parseC0 bfSrc >>= lowerTranslationUnit) ["register bitfield", "v.x"]
  assertErrContains "reg-val" (parseC0 regSrc >>= lowerTranslationUnit) ["register bitfield", "v.x"]
  IO.println "Negative diagnostics (#203) passed."
EOF
  timeout 60 lake env lean --run "$OUT/neg_diag.lean"
}

echo "== 2-5. running Steps 2+3 (V1+D2) and Step 5 (neg_diag) concurrently with Step 4 (111 probes + PCH) =="
run_v1_d2 >"$OUT/logs/v1_d2.log" 2>&1 &
pid_v1_d2=$!
run_neg_diag >"$OUT/logs/neg_diag.log" 2>&1 &
pid_neg_diag=$!

# Precompile tqbe_rt.hpp once for g++ (.gch) and clang++ ASan/UBSan (.pch) in parallel with Step 4.
# Symlink tqbe_rt.hpp into $OUT so g++'s `#pragma once` matches `$OUT/tqbe_rt.hpp.gch` when
# `<probe>.hpp` re-includes `"tqbe_rt.hpp"`. (Step 3 puts `-I$ROOT/LeanQbe/T/Runtime` before `-I$OUT`.)
ln -sf "$ROOT/LeanQbe/T/Runtime/tqbe_rt.hpp" "$OUT/tqbe_rt.hpp"
timeout 60 g++ -std=c++20 -O2 -w -DTQBE_CATCH_UB=1 -x c++-header \
  "$OUT/tqbe_rt.hpp" -o "$OUT/tqbe_rt.hpp.gch" >"$OUT/logs/pch_gpp.log" 2>&1 &
pid_gch=$!
timeout 60 clang++ -std=c++20 -O2 -w -fsanitize=undefined,address -DTQBE_CATCH_UB=1 -x c++-header \
  "$ROOT/LeanQbe/T/Runtime/tqbe_rt.hpp" -o "$OUT/tqbe_rt.hpp.pch" >"$OUT/logs/pch_clang.log" 2>&1 &
pid_pch=$!

step4_rc=0
timeout 300 python3 -B - "$ROOT" "$OUT" "$pid_gch" "$pid_pch" >"$OUT/logs/probes.log" 2>&1 <<'PY' || step4_rc=$?
import concurrent.futures, glob, os, re, struct, subprocess, sys, time

ROOT, OUT = sys.argv[1], sys.argv[2]
PDIR = os.path.join(OUT, "probes")
os.makedirs(PDIR, exist_ok=True)
WIDTH = {
    "u8": 8, "u16": 16, "u32": 32, "u64": 64,
    "i8": 8, "i16": 16, "i32": 32, "i64": 64,
    "bool": 1, "f64": 64,
}

# Expected frontend rejections (negative tests for excluded/unsupported C constructs)
EXPECTED_REJ = {
    "x_goto_inner_label", "x_regloop", "y_arrparam", "z_floatsuf",
}
NOT_REJ = {
    "rej_chain_assign", "rej_decl_multi_noinit", "rej_define_expr", "rej_dowhile0_macro",
    "rej_empty_ret", "rej_for_comma", "rej_ifelse_all_ret_loop", "rej_sizeof_var",
    "rej_void_cast",
}
# N8/N10 probes: lowered matches C99/IEEE-754 clang (differs only on gcc 40-bit bf extension
# or gcc -O2 NaN bug)
USE_CLANG_REF = {"bf1", "bf_promo", "bf_signed", "y_float"}
# Probes whose buffer dump embeds process-local pointer addresses (compare return values;
# pointer parity covered in D2)
PTR_IN_BUF = {"x_list", "x_ptrptr"}

def parse_specs(path):
    specs = []
    for line in open(path):
        m = re.match(r"\s*//T\s+(\w+)\s+(\S+)\s*:(.*?):(.*)$", line)
        if not m:
            continue
        fn, ret, ats, sets = m.group(1), m.group(2), m.group(3).split(), m.group(4)
        rets = (
            [] if ret == "void" else
            (ret.strip("()").split(",") if ret.startswith("(") else [ret])
        )
        calls = []
        for cs in sets.split("|"):
            cs = cs.strip()
            if not cs and ats:
                continue
            vals = re.findall(r"\w+\[[^\]]*\](?:\+\d+)?|[^\s]+", cs)
            assert len(vals) == len(ats), (path, fn, cs, ats)
            calls.append(vals)
        specs.append((fn, rets, ats, calls))
    return specs

def buf_bytes(v):
    m = re.match(r"(\w+)\[([^\]]*)\](?:\+(\d+))?$", v)
    ty, items, off = m.group(1), m.group(2), int(m.group(3) or 0)
    w = WIDTH[ty] // 8 if ty != "bool" else 1
    data = b""
    for it in items.split(","):
        if it.strip():
            data += (eval(it) & ((1 << (8 * w)) - 1)).to_bytes(w, "little")
    return data, off

def scalar_u(ty, v):
    if ty == "f64":
        return struct.unpack("<Q", struct.pack("<d", float(eval(v))))[0]
    return eval(v) & ((1 << WIDTH[ty]) - 1)

def gen_driver(name, specs, cpp):
    L = []
    if cpp:
        # TQBE_CATCH_UB=1 is passed via -DTQBE_CATCH_UB=1 so precompiled tqbe_rt.hpp (.gch/.pch)
        # is valid as the first header before any macro definitions.
        L += [
            '#include "tqbe_rt.hpp"',
            f'#include "{name}.hpp"', "#include <tuple>",
        ]
    else:
        L += [f'#include "{ROOT}/test/c0/probes/{name}.c"']
    L += ["#include <stdio.h>", "#include <stdlib.h>", "#include <string.h>", "#include <stdint.h>"]
    if cpp:
        L += [
            "template<size_t N> static unsigned long long val(::tqbe::bits<N> b){ "
            "return b.data; }",
            "static unsigned long long val(bool b){ return b; }",
            "static unsigned long long val(::tqbe::fval<::tqbe::Fmt::d> f){ return f.raw.data; }",
            "template<class... X> static void pr(const std::tuple<X...>& t){ "
            "std::apply([](auto&... x){ ((printf(\" %llx\", val(x))), ...); }, t); }",
            "template<class X> static void pr(const X& x){ printf(\" %llx\", val(x)); }",
        ]
    L += [
        "static void dump(const char*nm, const unsigned char*b, size_t n){ "
        "printf(\" %s=\", nm); for(size_t i=0;i<n;i++) printf(\"%02x\", b[i]); }"
    ]
    L += ["int main(void){"]
    idx = 0
    for fn, rets, ats, calls in specs:
        for vals in calls:
            L.append(f"  {{ printf(\"%d {fn} ->\", {idx});")
            idx += 1
            args, bufs = [], []
            if cpp:
                L.append("  ::tqbe::Mem mem;")
            for k, (ty, v) in enumerate(zip(ats, vals)):
                if ty == "p":
                    data, off = buf_bytes(v)
                    n = len(data)
                    init = ",".join(str(b) for b in data)
                    L.append(
                        f"  static const unsigned char i{k}[] = {{{init}}}; "
                        f"unsigned char *b{k} = (unsigned char*)malloc({max(n,1)}); "
                        f"memcpy(b{k}, i{k}, {n});"
                    )
                    bufs.append((k, n))
                    if cpp:
                        L.append(f"  mem.map_bytes((uint64_t)(uintptr_t)b{k}, b{k}, {n});")
                        args.append(f"::tqbe::bits<64>((uint64_t)(uintptr_t)b{k} + {off})")
                    else:
                        args.append(f"(void*)(b{k} + {off})")
                else:
                    u = scalar_u(ty, v)
                    if cpp:
                        if ty == "bool":
                            val_str = "true" if u else "false"
                        elif ty == "f64":
                            val_str = f"::tqbe::fval<::tqbe::Fmt::d>::from_u64({u}ULL)"
                        else:
                            val_str = f"::tqbe::bits<{WIDTH[ty]}>({u}ULL)"
                        args.append(val_str)
                    else:
                        if ty == "f64":
                            L.append(
                                f"  double d{k}; {{ uint64_t t = {u}ULL; "
                                f"memcpy(&d{k}, &t, 8); }}"
                            )
                            args.append(f"d{k}")
                        elif ty == "bool":
                            args.append("true" if u else "false")
                        else:
                            args.append(f"({ty}){u}ULL")
            if cpp:
                cpp_kw = {
                    "alignas", "alignof", "and", "and_eq", "asm", "auto", "bitand", "bitor",
                    "bool", "break", "case", "catch", "char", "char8_t", "char16_t", "char32_t",
                    "class", "compl", "concept", "const", "consteval", "constexpr", "constinit",
                    "const_cast", "continue", "co_await", "co_return", "co_yield", "decltype",
                    "default", "delete", "do", "double", "dynamic_cast", "else", "enum",
                    "explicit", "export", "extern", "false", "float", "for", "friend", "goto",
                    "if", "inline", "int", "long", "mutable", "namespace", "new", "noexcept",
                    "not", "not_eq", "nullptr", "operator", "or", "or_eq", "private", "protected",
                    "public", "register", "reinterpret_cast", "requires", "return", "short",
                    "signed", "sizeof", "static", "static_assert", "static_cast", "struct",
                    "switch", "template", "this", "thread_local", "throw", "true", "try",
                    "typedef", "typeid", "typename", "union", "unsigned", "using", "virtual",
                    "void", "volatile", "wchar_t", "while", "xor", "xor_eq",
                }
                cpp_fn = f"fn_{fn}" if fn in cpp_kw else fn
                call = f"c0p_{name}::{cpp_fn}({', '.join(['mem'] + args)})"
                L.append(f"  try {{ auto r = {call}; pr(r);")
                for k, n in bufs:
                    L.append(
                        f"  {{ unsigned char o[{max(n,1)}]; "
                        f"for (size_t i=0;i<{n};i++) "
                        f"o[i]=mem.read_byte((uint64_t)(uintptr_t)b{k}+i); "
                        f"dump(\"b{k}\", o, {n}); }}"
                    )
                L.append(
                    "  } catch (const ::tqbe::UbException& e) { "
                    "printf(\" UB(%s)\", e.what()); "
                    "} catch (const ::tqbe::ExitException& e) { "
                    "printf(\" EXIT(%s)\", e.target.c_str()); }"
                )
            else:
                call = f"{fn}({', '.join(args)})"
                if not rets:
                    L.append(f"  {call};")
                elif len(rets) == 1:
                    rt = rets[0]
                    if rt == "f64":
                        L.append(
                            f"  {{ double r = {call}; uint64_t t; "
                            f"memcpy(&t,&r,8); printf(\" %llx\", (unsigned long long)t); }}"
                        )
                    elif rt == "bool":
                        L.append(
                            f"  {{ bool r = {call}; "
                            f"printf(\" %llx\", (unsigned long long)r); }}"
                        )
                    else:
                        L.append(
                            f"  {{ {rt} r = {call}; "
                            f"printf(\" %llx\", (unsigned long long)(u{WIDTH[rt]})r); }}"
                        )
                else:
                    L.append(f"  {{ __typeof__({call}) r = {call};")
                    for j, rt in enumerate(rets):
                        cast = (
                            "(unsigned long long)" if rt == "bool"
                            else f"(unsigned long long)(u{WIDTH[rt]})"
                        )
                        L.append(f"    printf(\" %llx\", {cast}r._{j});")
                    L.append("  }")
                for k, n in bufs:
                    L.append(f"  dump(\"b{k}\", b{k}, {n});")
            L.append("  printf(\"\\n\"); }")
    L.append("  return 0; }")
    return "\n".join(L) + "\n", idx

probe_paths = sorted(glob.glob(os.path.join(ROOT, "test/c0/probes/*.c")))
names = [os.path.basename(p)[:-2] for p in probe_paths]
assert len(names) == 111, f"expected 111 probes, got {len(names)}"

lean = """import LeanQbe.T.Frontend.C0
import LeanQbe.T.PrintCpp
open LeanQbe.T LeanQbe.T.Frontend.C0
def emitNs (path ns : String) (fns : List Fn) : IO Unit := do
  match PrintCpp.buildSymMap fns with
  | .error e => throw (IO.userError e)
  | .ok symMap =>
    let decls := String.join (fns.map (PrintCpp.ppFnDecl symMap))
    let defs := String.intercalate "\\n" (fns.map (PrintCpp.ppFn symMap))
    IO.FS.writeFile path (
      "#pragma once\\n#include \\"tqbe_rt.hpp\\"\\nnamespace " ++ ns ++ " {\\n"
      ++ decls ++ "\\n" ++ defs ++ "\\n}\\n")
"""
linemap = {}
for n in names:
    hpp = os.path.join(PDIR, f"{n}.hpp")
    if os.path.exists(hpp):
        os.remove(hpp)
    ln = lean.count("\n") + 1
    lean += (
        f'namespace P_{n}\n'
        f'c0_file! p "{ROOT}/test/c0/probes/{n}.c"\n'
        f'#eval emitNs "{hpp}" "c0p_{n}" p_fns\n'
        f'end P_{n}\n'
    )
    linemap[ln + 1] = n

lean_file = os.path.join(PDIR, "all_probes.lean")
open(lean_file, "w").write(lean)
r = subprocess.run(
    ["timeout", "240", "lake", "env", "lean", lean_file],
    cwd=ROOT, capture_output=True, text=True,
)
errs = {}
cur = None
for ln in (r.stdout + r.stderr).split("\n"):
    m = re.match(r".*all_probes\.lean:(\d+):\d+: error: (.*)$", ln)
    if m:
        cur = linemap.get(int(m.group(1)))
        if cur:
            errs[cur] = m.group(2)
        continue
    if cur and ln.strip() and not re.match(r".*all_probes\.lean:\d+", ln):
        errs[cur] += " " + ln.strip()
    else:
        cur = None

# Ensure background PCH/GCH builds have completed before launching C++ probe compiles.
gch_path = os.path.join(OUT, "tqbe_rt.hpp.gch")
pch_path = os.path.join(OUT, "tqbe_rt.hpp.pch")
for pid_str in (sys.argv[3], sys.argv[4]):
    pid = int(pid_str)
    while os.path.exists(f"/proc/{pid}"):
        try:
            with open(f"/proc/{pid}/stat") as fh:
                if fh.read().split()[2] == "Z":
                    break
        except OSError:
            break
        time.sleep(0.05)

use_gch = os.path.isfile(gch_path)
use_pch = os.path.isfile(pch_path)
rt_dir = os.path.join(ROOT, "LeanQbe/T/Runtime")

def check_one(n):
    hpp = os.path.join(PDIR, f"{n}.hpp")
    is_rej = (n.startswith("rej_") and n not in NOT_REJ) or n in EXPECTED_REJ
    if is_rej:
        if os.path.exists(hpp) or n not in errs:
            return f"FAIL {n}: expected rejection, got accepted (err={errs.get(n)})"
        return ("REJ", 0)
    if not os.path.exists(hpp):
        return f"FAIL {n}: unexpectedly rejected: {errs.get(n, '(no message)')}"
    specs = parse_specs(os.path.join(ROOT, "test/c0/probes", f"{n}.c"))
    nat_src, total = gen_driver(n, specs, cpp=False)
    low_src, _ = gen_driver(n, specs, cpp=True)
    open(os.path.join(PDIR, f"{n}_nat.c"), "w").write(nat_src)
    open(os.path.join(PDIR, f"{n}_low.cpp"), "w").write(low_src)
    cc = "clang" if n in USE_CLANG_REF else "gcc"
    inc = ["-I", os.path.join(ROOT, "LeanQbe/T/Frontend/C0")]
    c1 = subprocess.run(
        ["timeout", "60", cc, "-std=c99", "-O2", "-fwrapv", "-fno-strict-aliasing", "-w"]
        + inc + [os.path.join(PDIR, f"{n}_nat.c"), "-o", os.path.join(PDIR, f"{n}_nat")],
        capture_output=True, text=True,
    )
    if c1.returncode != 0:
        return f"FAIL {n} native {cc} compile: {c1.stderr[:500]}"
    rn = subprocess.run(
        ["timeout", "10", os.path.join(PDIR, f"{n}_nat")],
        capture_output=True, text=True,
    )
    if rn.returncode != 0:
        return f"FAIL {n} native run rc={rn.returncode}"
    nat_lines = rn.stdout.strip().split("\n") if rn.stdout.strip() else []
    if len(nat_lines) != total:
        return f"FAIL {n} native line count mismatch ({len(nat_lines)} vs {total})"
    gpp_flags = (["-I", OUT] if use_gch else []) + ["-I", rt_dir]
    clang_flags = (["-include-pch", pch_path] if use_pch else []) + ["-I", rt_dir]
    for cxx, extra, inc_flags in [
        ("g++", [], gpp_flags),
        ("clang++", ["-fsanitize=undefined,address"], clang_flags),
    ]:
        binp = os.path.join(PDIR, f"{n}_{cxx}")
        c2 = subprocess.run(
            ["timeout", "60", cxx, "-std=c++20", "-O2", "-w", "-DTQBE_CATCH_UB=1"] + extra
            + inc_flags + ["-I", PDIR, os.path.join(PDIR, f"{n}_low.cpp"), "-o", binp],
            capture_output=True, text=True,
        )
        if c2.returncode != 0:
            return f"FAIL {n} lowered {cxx} compile: {c2.stderr[:500]}"
        rl = subprocess.run(
            ["timeout", "10", binp],
            capture_output=True, text=True,
            env=dict(os.environ, ASAN_OPTIONS="detect_leaks=0"),
        )
        if rl.returncode != 0:
            return f"FAIL {n} lowered {cxx} run rc={rl.returncode}: {rl.stderr[:300]}"
        low_lines = rl.stdout.strip().split("\n") if rl.stdout.strip() else []
        if len(low_lines) != total:
            return f"FAIL {n} {cxx} line count mismatch ({len(low_lines)} vs {total})"
        for i, (la, lb) in enumerate(zip(nat_lines, low_lines)):
            if n == "call_order" and any(x in la for x in ("k1 ", "k1n ", "k3c ")):
                continue
            if n in PTR_IN_BUF:
                ra, rb = la.split(" b0=")[0], lb.split(" b0=")[0]
                if ra != rb:
                    return f"FAIL {n} ({cxx}) case {i} return mismatch:\n  nat: {la}\n  low: {lb}"
            elif la != lb:
                return f"FAIL {n} ({cxx}) case {i} mismatch ({cc}):\n  nat: {la}\n  low: {lb}"
    checked = sum(
        1 for la in nat_lines
        if not (n == "call_order" and any(x in la for x in ("k1 ", "k1n ", "k3c ")))
    )
    return ("PASS", checked)

failures, rej_cnt, pass_cnt, case_cnt = [], 0, 0, 0
with concurrent.futures.ThreadPoolExecutor(16) as ex:
    for res in ex.map(check_one, names):
        if isinstance(res, str):
            failures.append(res)
        elif res[0] == "REJ":
            rej_cnt += 1
        else:
            pass_cnt += 1
            case_cnt += res[1]

for f in failures:
    print(f, file=sys.stderr)
if failures:
    sys.exit(1)
print(
    f"Regression probes passed (g++ + clang++ ASan/UBSan): {pass_cnt} matched "
    f"({case_cnt} cases), {rej_cnt} rejected as expected."
)
PY

fail=0
if ! wait "$pid_gch"; then
  echo "FAIL: g++ precompiled header build failed:" >&2
  cat "$OUT/logs/pch_gpp.log" >&2 || true
  fail=1
fi
if ! wait "$pid_pch"; then
  echo "FAIL: clang++ precompiled header build failed:" >&2
  cat "$OUT/logs/pch_clang.log" >&2 || true
  fail=1
fi
if ! wait "$pid_v1_d2"; then
  echo "FAIL: Steps 2-3 (V1 + D2) failed:" >&2
  fail=1
fi
cat "$OUT/logs/v1_d2.log"
echo "== 4. (Regression) all 111 adversarial differential probes under test/c0/probes/ =="
cat "$OUT/logs/probes.log"
if [ "$step4_rc" -ne 0 ]; then
  echo "FAIL: Step 4 (111 probes) exited with rc=$step4_rc" >&2
  fail=1
fi
if ! wait "$pid_neg_diag"; then
  echo "FAIL: Step 5 (negative diagnostics) failed:" >&2
  fail=1
fi
cat "$OUT/logs/neg_diag.log"

if [ "$fail" -ne 0 ]; then
  exit 1
fi

echo "== test/c0/run.sh: ALL PASSED =="
