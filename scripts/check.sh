#!/usr/bin/env bash
# lean-qbe quality gate. Run from anywhere: scripts/check.sh
#
# Environment knobs:
#   CHECK_SCOPE=full|auto|x64|arm64
#       Defaults to `full` when `CHECK_BASE` is unset (100% backward compatible), or `auto`
#       when `CHECK_BASE` is set. In `auto` mode (with `CHECK_BASE` defaulting to `HEAD~1`),
#       a fail-closed classifier selects:
#         - `class0`: ONLY when >=1 files changed, 0 `.lean`/gate/toolchain files changed, and
#           100% of changed files match the non-Lean allowlist (0 `lake` calls, <15s).
#         - `x64`:    ONLY when >=1 `.lean` files changed, 100% of changed `.lean` files are under
#           `LeanQbe/T/Amd64/` or `LeanQbeTest/T/*{X64,Amd64}*.lean`, and any non-`.lean` files
#           are docs / `scripts/headlines.d/amd64.txt`. Skips `LeanQbeArm64` & `leanqbe-arm64`.
#         - `arm64`:  Symmetric for `LeanQbe/T/Arm64/` / `LeanQbeTest/T/*Arm64*.lean`.
#         - `full`:   Fail-closed default for any other file or empty/unresolvable diff.
#   INCLUDE_LEGACY=0|1
#       Controls whether `scripts/headlines.d/*legacy*.txt` files are audited in Step 4.
#       Defaults to `0` if `LeanQbeLegacy*` targets exist in `lakefile.toml`, else `1`.
#   LAKE_JOBS=<N>
#       Sets `LEAN_NUM_THREADS=$LAKE_JOBS` for Step 1 `lake build` (defaults to
#       `${LEAN_NUM_THREADS:-6}` so uncapped runs never spawn `nproc` `lean` workers;
#       Lake 5.0 controls build concurrency via `LEAN_NUM_THREADS`, as `lake build -j`
#       does not exist).
#   CHECK_LOCK_FILE=<path>
#       Advisory `flock` lockfile serializing Step 1 `lake build` across worktrees
#       (default: `/tmp/leanqbe_check_build.lock`). Set `CHECK_NO_LOCK=1` to bypass.
#   CHECK_MEM_MAX=<size>
#       `MemoryMax` passed to `systemd-run --user --scope` for Step 1 `lake build`
#       (default: `48G`, `OOMPolicy=kill`). Set `CHECK_NO_SCOPE=1` to bypass.
#   CHECK_TIMES=0|1
#       Set to `1` to enable standalone Step 5 re-elaboration CPU timing.
#
# Steps (for Lean scopes `full`, `x64`, `arm64`):
#  1. Builds scoped targets with warnings as errors (`lake build --wfail`, including
#     `LeanQbeBootstrap0` & `LeanQbeBootstrap0Test` in `full` and `x64` scopes).
#  2. Fails on any `sorry` (build log and source files) and scans all tracked `.lean` files
#     for `sorry`, `admit`, non-meta `axiom `, `@[implemented_by]`, `@[extern]`, `trustCompiler`,
#     and native-code tactics (`bv_decide`, `native_decide`, `decide +native`, `ofReduceBool`,
#     `ofReduceNat`) outside comments and string/char literals.
#  3. Checks import closures (`LeanQbe` arch-free, `LeanQbeAmd64` / `LeanQbeBootstrap0` /
#     `LeanQbeBootstrap0Test` no AArch64, `LeanQbeArm64` no X64, 0 legacy Kissat certs in active
#     `LeanQbe{Amd64,Arm64}` / `LeanQbeBootstrap0*` closures, reachability of `LeanQbe/T/` from
#     active, `LeanQbeBootstrap0`, or `LeanQbeLegacy{Amd64,Arm64}` roots; no retired untyped files).
#  3b. Incrementality firewall (`check_firewall.py --require-isa`) and barrel/hub lint
#      (`sync_hubs.py --check` when present).
#  4. Parallel axiom audit (`Audit_generic`, `Audit_x64`, `Audit_arm64`, isolated root-`main`
#     batches, with 16-way per-module fallback) for active `scripts/headlines.d/*.txt` (or
#     `scripts/headline.txt` if `headlines.d` is absent).
#  5. Standalone re-elaboration timing when `CHECK_TIMES=1`.
#
# Every command runs under `timeout`. Exit code 0 iff all checks pass.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

export LAKE_ARTIFACT_CACHE="${LAKE_ARTIFACT_CACHE:-true}"
export LAKE_RESTORE_ARTIFACTS="${LAKE_RESTORE_ARTIFACTS:-true}"

classify_stdin() {
  python3 -c '
import re, sys

files = [line.strip() for line in sys.stdin if line.strip()]
if not files:
    print("full")
    sys.exit(0)

forbidden_class0_re = re.compile(
    r"^(?:lakefile\.toml|lean-toolchain|lake-manifest\.json"
    r"|scripts/check\.sh|scripts/headline\.txt|scripts/headlines\.d/)"
)
class0_re = re.compile(
    r"^(?:(?:LeanQbe-)?README\.md|NOTES\.md|DEVELOPER\.md|CONTRIBUTING\.md"
    r"|docs/.*|bench/.*"
    r"|test/.*\.(?:c|h|py|sh|cnf|lrat)"
    r"|scripts/(?:fast_land|tier3_check|all)\.sh"
    r"|scripts/(?:gen_cert_slices|test_gen_cert_slices|merge_lean_imports)\.py)$"
)
x64_lean_re = re.compile(
    r"^(?:LeanQbe/T/Amd64/.*|LeanQbeTest/T/[^/]*(?:X64|Amd64)[^/]*)\.lean$"
)
arm64_lean_re = re.compile(
    r"^(?:LeanQbe/T/Arm64/.*|LeanQbeTest/T/[^/]*Arm64[^/]*)\.lean$"
)
x64_nonlean_re = re.compile(
    r"^(?:(?:LeanQbe-)?README\.md|NOTES\.md|DEVELOPER\.md|CONTRIBUTING\.md|docs/.*|scripts/headlines\.d/amd64\.txt)$"
)
arm64_nonlean_re = re.compile(
    r"^(?:(?:LeanQbe-)?README\.md|NOTES\.md|DEVELOPER\.md|CONTRIBUTING\.md|docs/.*|scripts/headlines\.d/arm64\.txt)$"
)

if all(
    (not f.endswith(".lean"))
    and (not forbidden_class0_re.match(f))
    and class0_re.fullmatch(f)
    for f in files
):
    print("class0")
    sys.exit(0)

lean_files = [f for f in files if f.endswith(".lean")]
nonlean_files = [f for f in files if not f.endswith(".lean")]

if (
    lean_files
    and all(x64_lean_re.fullmatch(f) and ("Arm64" not in f) for f in lean_files)
    and all(x64_nonlean_re.fullmatch(f) for f in nonlean_files)
):
    print("x64")
    sys.exit(0)

if (
    lean_files
    and all(
        arm64_lean_re.fullmatch(f) and ("X64" not in f) and ("Amd64" not in f)
        for f in lean_files
    )
    and all(arm64_nonlean_re.fullmatch(f) for f in nonlean_files)
):
    print("arm64")
    sys.exit(0)

print("full")
'
}

MODE="run"
while [ $# -gt 0 ]; do
  case "$1" in
    --classify-stdin) MODE="classify_stdin"; shift ;;
    --print-scope) MODE="print_scope"; shift ;;
    -h|--help)
      sed -n '2,51p' "${BASH_SOURCE[0]}"
      exit 0 ;;
    *)
      echo "check.sh: unknown option: $1" >&2
      exit 2 ;;
  esac
done

if [ "$MODE" = "classify_stdin" ]; then
  classify_stdin
  exit $?
fi

BUILD_TIMEOUT="${BUILD_TIMEOUT:-3600}"
LEAN_TIMEOUT="${LEAN_TIMEOUT:-600}"
LAKE_JOBS="${LAKE_JOBS:-${LEAN_NUM_THREADS:-6}}"
CHECK_LOCK_FILE="${CHECK_LOCK_FILE:-/tmp/leanqbe_check_build.lock}"
CHECK_MEM_MAX="${CHECK_MEM_MAX:-48G}"
CHECK_NO_LOCK="${CHECK_NO_LOCK:-0}"
CHECK_NO_SCOPE="${CHECK_NO_SCOPE:-0}"
ALLOWED="propext Classical.choice Quot.sound"

if [ -z "${CHECK_SCOPE:-}" ]; then
  if [ -n "${CHECK_BASE:-}" ]; then
    CHECK_SCOPE="auto"
  else
    CHECK_SCOPE="full"
  fi
fi

case "$CHECK_SCOPE" in
  auto|x64|arm64|full) ;;
  *) echo "FAIL: invalid CHECK_SCOPE='$CHECK_SCOPE' (expected auto|x64|arm64|full)" >&2; exit 2 ;;
esac

if [ -z "${INCLUDE_LEGACY:-}" ]; then
  if grep -qE '^name[[:space:]]*=[[:space:]]*"LeanQbeLegacy' lakefile.toml 2>/dev/null; then
    INCLUDE_LEGACY=0
  else
    INCLUDE_LEGACY=1
  fi
fi
case "$INCLUDE_LEGACY" in
  0|1) ;;
  *) echo "FAIL: invalid INCLUDE_LEGACY='$INCLUDE_LEGACY' (expected 0|1)" >&2; exit 2 ;;
esac

CHANGED_FILES=""
RESOLVED_SCOPE="$CHECK_SCOPE"
if [ "$CHECK_SCOPE" = "auto" ]; then
  CHECK_BASE="${CHECK_BASE:-HEAD~1}"
  if git rev-parse --verify "${CHECK_BASE}^{commit}" >/dev/null 2>&1; then
    if CHANGED_FILES="$({
      git diff --name-only --no-renames "${CHECK_BASE}...HEAD" &&
      git diff --name-only --no-renames HEAD &&
      git ls-files --others --exclude-standard
    } | sort -u)"; then
      RESOLVED_SCOPE="$(printf '%s\n' "$CHANGED_FILES" | classify_stdin)"
    else
      RESOLVED_SCOPE="full"
    fi
  else
    RESOLVED_SCOPE="full"
  fi
fi

if [ "$MODE" = "print_scope" ]; then
  printf '%s\n' "$RESOLVED_SCOPE"
  exit 0
fi

TMP="$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-check.XXXXXX")"
SCOPE_UNIT=""
build_pid=""
cleanup() {
  if [ -n "$SCOPE_UNIT" ]; then
    systemctl --user stop "$SCOPE_UNIT" >/dev/null 2>&1 || true
  fi
  if [ -n "$build_pid" ]; then
    kill "$build_pid" 2>/dev/null || true
  fi
  rm -rf "$TMP"
}
trap cleanup EXIT
trap 'cleanup; exit 130' INT
trap 'cleanup; exit 143' TERM
trap 'cleanup; exit 129' HUP
fail=0
err() { echo "FAIL: $*"; fail=1; }

scan_lean_forbidden_tokens() {
  timeout 60 python3 -B - <<'PY'
import pathlib, re, subprocess, sys

raw = subprocess.check_output(
    ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard", "*.lean", ":(exclude)Kraken", ":(exclude)Kraken*.lean", ":(exclude)Att2Intel.lean", ":(exclude)Bedrock2C.lean"]
)
files = [f.decode("utf-8") for f in raw.split(b"\0") if f]

def strip_lean(src: str) -> str:
    out = []
    i = 0
    n = len(src)
    depth = 0
    in_str = False
    while i < n:
        ch = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if depth > 0:
            if ch == "/" and nxt == "-":
                depth += 1
                i += 2
                continue
            if ch == "-" and nxt == "/":
                depth -= 1
                i += 2
                continue
            if ch == "\n":
                out.append("\n")
            i += 1
            continue
        if in_str:
            if ch == "\\" and i + 1 < n:
                if src[i + 1] == "\n":
                    out.append("\n")
                i += 2
                continue
            if ch == '"':
                in_str = False
                i += 1
                continue
            if ch == "\n":
                out.append("\n")
            i += 1
            continue
        if ch == "-" and nxt == "-":
            while i < n and src[i] != "\n":
                i += 1
            continue
        if ch == "/" and nxt == "-":
            depth = 1
            i += 2
            continue
        if ch == '"':
            in_str = True
            out.append('""')
            i += 1
            continue
        if ch == "'" and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] in "_'")):
            if i + 2 < n and src[i + 1] == "\\":
                j = i + 2
                while j < n and src[j] != "\n" and src[j] != "'" and j - i < 12:
                    j += 1
                if j < n and src[j] == "'":
                    out.append("''")
                    i = j + 1
                    continue
            elif i + 2 < n and src[i + 1] != "\n" and src[i + 2] == "'":
                out.append("''")
                i += 3
                continue
        out.append(ch)
        i += 1
    return "".join(out)

pre_re = re.compile(
    r"\b(?:sorry|admit|bv_decide|native_decide|ofReduceBool|ofReduceNat"
    r"|trustCompiler|axiom|implemented_by|extern)\b|\+native"
)
tok_re = re.compile(
    r"\b(sorry|admit|bv_decide|native_decide|ofReduceBool|ofReduceNat|trustCompiler)\b"
    r"|decide\s+\+native"
)
axiom_re = re.compile(
    r"(?:^|;)\s*(?:(?:public|private|protected|unsafe|noncomputable|local|scoped)\s+)*axiom\b"
)
attr_re = re.compile(r"@\[[^\]]*\b(?:implemented_by|extern)\b")

hits = []
for rel in files:
    p = pathlib.Path(rel)
    if not p.is_file():
        hits.append(f"{rel}: tracked file missing from working tree")
        continue
    raw = p.read_text(encoding="utf-8")
    if not pre_re.search(raw):
        continue
    cleaned = strip_lean(raw)
    for lineno, line in enumerate(cleaned.splitlines(), 1):
        m = tok_re.search(line) or axiom_re.search(line)
        if m:
            hits.append(f"{rel}:{lineno}: {line.strip()}")
    for m in attr_re.finditer(cleaned):
        lineno = cleaned[:m.start()].count("\n") + 1
        hits.append(f"{rel}:{lineno}: {m.group(0)}")
if hits:
    for h in hits[:50]:
        print(h, file=sys.stderr)
    sys.exit(1)
PY
}

echo "== check.sh: scope=$RESOLVED_SCOPE (requested=$CHECK_SCOPE, INCLUDE_LEGACY=$INCLUDE_LEGACY)"

# Collect active headline lines (<Module> <const>) into $TMP/headlines_all.txt
python3 - "$INCLUDE_LEGACY" "$TMP/headlines_all.txt" <<'PY'
import pathlib, sys

inc_legacy = sys.argv[1] == "1"
out_path = pathlib.Path(sys.argv[2])
hdir = pathlib.Path("scripts/headlines.d")
files = sorted(hdir.glob("*.txt")) if hdir.is_dir() else []
if files:
    if not inc_legacy:
        files = [f for f in files if "legacy" not in f.name]
elif pathlib.Path("scripts/headline.txt").is_file():
    files = [pathlib.Path("scripts/headline.txt")]

lines = []
for f in files:
    for raw in f.read_text().splitlines():
        s = raw.strip()
        if not s or s.startswith("#"):
            continue
        lines.append(s)
out_path.write_text("\n".join(lines) + ("\n" if lines else ""))
PY

headline_total="$(wc -l <"$TMP/headlines_all.txt" | tr -d ' ')"

if [ "$RESOLVED_SCOPE" = "class0" ]; then
  echo "== 1c0. shell syntax (bash -n)"
  while IFS= read -r shf; do
    [ -f "$shf" ] || continue
    timeout 30 bash -n "$shf" || err "bash -n failed: $shf"
  done < <(git ls-files --cached --others --exclude-standard '*.sh' | sort -u)

  echo "== 2c0. python syntax (py_compile)"
  mapfile -t py_files < <(git ls-files --cached --others --exclude-standard '*.py' | sort -u)
  if [ "${#py_files[@]}" -gt 0 ]; then
    timeout 30 env PYTHONDONTWRITEBYTECODE=1 PYTHONPYCACHEPREFIX="$TMP/pycache" \
      python3 -m py_compile "${py_files[@]}" || err "python3 -m py_compile failed"
  fi

  echo "== 2c0b. generator unit tests & pure-Python gates (0 lake calls)"
  if [ -f scripts/test_gen_cert_slices.py ]; then
    timeout 120 env PYTHONDONTWRITEBYTECODE=1 python3 -B scripts/test_gen_cert_slices.py \
      >"$TMP/test_gen_cert_slices.log" 2>&1 \
      || { tail -n 30 "$TMP/test_gen_cert_slices.log"; err "scripts/test_gen_cert_slices.py failed"; }
  fi
  timeout 60 python3 -B "$ROOT/scripts/check_firewall.py" --root "$ROOT" --require-isa \
    || err "incrementality firewall check failed (check_firewall.py)"
  timeout 60 python3 -B "$ROOT/scripts/sync_hubs.py" --root "$ROOT" --check \
    || err "barrel/hub check failed (sync_hubs.py --check)"

  echo "== 3c0. forbidden tokens, native-code tactics & tracked-file hygiene (0 lake calls)"
  scan_lean_forbidden_tokens \
    || err "forbidden token (sorry/admit/axiom/@[implemented_by]/@[extern]/trustCompiler/native tactic) in a .lean file"
  if git ls-files --cached 'LeanQbe/*.lean' 'LeanQbe/**/*.lean' \
      | grep -v '^LeanQbe/T/'; then
    err "retired untyped E1 .lean files remain tracked under LeanQbe/ outside LeanQbe/T/"
  fi
  if git ls-files --cached 'LeanQbeTest/*.lean' 'LeanQbeTest/**/*.lean' \
      | grep -v '^LeanQbeTest/T/'; then
    err "retired untyped E1 .lean files remain tracked under LeanQbeTest/ outside LeanQbeTest/T/"
  fi
  if git ls-files --cached 'LeanQbeTest/*SpikeS2*' 'LeanQbeTest/**/*SpikeS2*' | grep .; then
    err "temporary SpikeS2 files remain tracked under LeanQbeTest/"
  fi
  g5_re='^\s*(public\s+|meta\s+)*import\s+(all\s+)?LeanQbe\.([^T]|T[^.])'
  if git ls-files -z 'LeanQbe/T/*.lean' 'LeanQbe/T/**/*.lean' \
      | (set +o pipefail; xargs -0 grep -HnE "$g5_re" 2>/dev/null); then
    err "LeanQbe/T module imports untyped E1 module (G5 violation)"
  fi
  while IFS= read -r cf; do
    [ -f "$cf" ] || continue
    if grep -nE '^(<{7}|={7}|>{7})( |$)' "$cf"; then
      err "merge conflict marker in $cf"
    fi
  done <<<"$CHANGED_FILES"
  if [ "$headline_total" -le 0 ]; then
    err "no active headline theorems found in scripts/headlines.d/ or scripts/headline.txt"
  fi

  if [ $fail -eq 0 ]; then
    echo "== check.sh: ALL PASSED (class0, 0 lake calls)"
  else
    echo "== check.sh: FAILED"
  fi
  exit $fail
fi

# Shared arch-classifier & batch helper for Step 1 (`scoped-tests`) and Step 4 (`audit-batches`)
cat >"$TMP/arch_scope.py" <<'PY'
import pathlib, re, sys

IMP_RE = re.compile(
    r"^\s*(?:public\s+|meta\s+)*(?:import\s+all\s+|import\s+)([A-Za-z0-9_.']+)"
)
X64_PFX = ("Kraken.X64", "LeanQbe.T.Amd64.")
ARM_PFX = ("Kraken.AArch64", "LeanQbe.T.Arm64.")


def make_classifier(c_gen=frozenset(), x64_only=frozenset(), arm_only=frozenset()):
    memo = {}

    def classify(mod, stack):
        if mod in memo:
            return memo[mod]
        if mod in c_gen:
            memo[mod] = "generic"
            return "generic"
        if mod in x64_only or mod == "LeanQbeAmd64" or mod.startswith(X64_PFX):
            memo[mod] = "x64"
            return "x64"
        if mod in arm_only or mod == "LeanQbeArm64" or mod.startswith(ARM_PFX):
            memo[mod] = "arm64"
            return "arm64"
        if mod in stack:
            return "generic"
        p = pathlib.Path(mod.replace(".", "/") + ".lean")
        if not p.is_file():
            return "conflict"
        arches = set()
        nxt = stack | {mod}
        for line in p.read_text().splitlines():
            m = IMP_RE.match(line)
            if not m:
                continue
            imp = m.group(1)
            if imp == "LeanQbeAmd64" or imp in x64_only or imp.startswith(X64_PFX):
                arches.add("x64")
            elif imp == "LeanQbeArm64" or imp in arm_only or imp.startswith(ARM_PFX):
                arches.add("arm64")
            elif imp not in c_gen and imp.startswith(("LeanQbe.", "LeanQbeTest.", "LeanQbeBootstrap0Test.")):
                sub = classify(imp, nxt)
                if sub in ("x64", "arm64", "conflict"):
                    arches.add(sub)
        if "conflict" in arches or ("x64" in arches and "arm64" in arches):
            res = "conflict"
        elif "x64" in arches:
            res = "x64"
        elif "arm64" in arches:
            res = "arm64"
        else:
            res = "generic"
        memo[mod] = res
        return res

    return classify


def run_scoped_tests(scope, hpath, changed_path):
    classify = make_classifier()
    want_mods = []
    seen = set()
    for raw in hpath.read_text().splitlines():
        parts = raw.split()
        if len(parts) < 2:
            continue
        mod = parts[0]
        if not mod.startswith(("LeanQbeTest.", "LeanQbeBootstrap0Test.")) or mod in seen:
            continue
        if classify(mod, set()) in ("generic", scope):
            seen.add(mod)
            want_mods.append(mod)

    changed = [l.strip() for l in changed_path.read_text().splitlines() if l.strip()]
    for f in changed:
        if (
            f.startswith(("LeanQbeTest/", "LeanQbeBootstrap0Test/"))
            and f.endswith(".lean")
            and pathlib.Path(f).is_file()
        ):
            mod = f[:-5].replace("/", ".")
            if mod not in seen:
                seen.add(mod)
                want_mods.append(mod)

    for m in want_mods:
        print(m)


def run_audit_batches(tmp, scope):
    def read_set(name):
        p = tmp / f"closure_{name}.txt"
        return set(p.read_text().splitlines()) if p.exists() else set()

    c_gen = read_set("LeanQbe")
    c_x64 = read_set("LeanQbeAmd64")
    c_arm = read_set("LeanQbeArm64")
    classify = make_classifier(c_gen, c_x64 - c_gen, c_arm - c_gen)

    ns_re = re.compile(r"^\s*namespace\s+\S+")
    sec_re = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s+|public\s+|private\s+|protected\s+)*section(?:\s|$)"
    )
    end_re = re.compile(r"^\s*end(?:\s|$)")
    def_main_re = re.compile(
        r"^(?:(?:public|private|protected|noncomputable)\s+)*def\s+main\b"
    )

    main_memo = {}

    def has_root_main(mod, stack):
        if mod in main_memo:
            return main_memo[mod]
        if mod in stack:
            return False
        p = pathlib.Path(mod.replace(".", "/") + ".lean")
        if not p.is_file():
            return False
        scopes = []
        nxt = stack | {mod}
        found = False
        for line in p.read_text().splitlines():
            m = IMP_RE.match(line)
            if m:
                imp = m.group(1)
                if (
                    imp.startswith(("LeanQbe.", "LeanQbeTest.", "LeanQbeBootstrap0Test."))
                    and has_root_main(imp, nxt)
                ):
                    found = True
                    break
            if ns_re.match(line):
                scopes.append("ns")
            elif sec_re.match(line):
                scopes.append("sec")
            elif end_re.match(line) and scopes:
                scopes.pop()
            elif "ns" not in scopes and def_main_re.match(line):
                found = True
                break
        main_memo[mod] = found
        return found

    buckets = {b: ([], []) for b in ("generic", "x64", "arm64")}
    solo_buckets = {}
    conflict_mods = []
    seen_mods = {b: set() for b in ("generic", "x64", "arm64")}
    seen_conf = set()
    selected = []

    for raw in (tmp / "headlines_all.txt").read_text().splitlines():
        s = raw.strip()
        if not s or s.startswith("#"):
            continue
        parts = s.split()
        if len(parts) < 2:
            continue
        mod, const = parts[0], parts[1]
        b = classify(mod, set())
        if scope == "x64" and b == "arm64":
            continue
        if scope == "arm64" and b == "x64":
            continue
        selected.append(f"{mod} {const}")
        if b == "conflict":
            if mod not in seen_conf:
                seen_conf.add(mod)
                conflict_mods.append(mod)
            continue
        if has_root_main(mod, set()):
            solo_buckets.setdefault(mod, []).append(const)
            continue
        if mod not in seen_mods[b]:
            seen_mods[b].add(mod)
            buckets[b][0].append(mod)
        buckets[b][1].append(const)

    out_sel = "\n".join(selected) + ("\n" if selected else "")
    (tmp / "selected_headlines.txt").write_text(out_sel)

    for b, (mods, consts) in buckets.items():
        if not mods:
            continue
        lines = [f"import {m}" for m in mods] + [f"#print axioms {c}" for c in consts]
        (tmp / f"Batch_{b}.lean").write_text("\n".join(lines) + "\n")
        (tmp / f"mods_batch_{b}.txt").write_text("\n".join(mods) + "\n")
    for idx, (mod, consts) in enumerate(solo_buckets.items(), 1):
        b = f"solo_{idx}"
        lines = [f"import {mod}"] + [f"#print axioms {c}" for c in consts]
        (tmp / f"Batch_{b}.lean").write_text("\n".join(lines) + "\n")
        (tmp / f"mods_batch_{b}.txt").write_text(f"{mod}\n")
    if conflict_mods:
        (tmp / "mods_conflict.txt").write_text("\n".join(conflict_mods) + "\n")


mode = sys.argv[1]
if mode == "scoped-tests":
    run_scoped_tests(sys.argv[2], pathlib.Path(sys.argv[3]), pathlib.Path(sys.argv[4]))
elif mode == "audit-batches":
    run_audit_batches(pathlib.Path(sys.argv[2]), sys.argv[3])
else:
    raise SystemExit(f"unknown arch_scope mode: {mode}")
PY

# Determine scoped Step 1 build targets
if [ "$RESOLVED_SCOPE" = "full" ]; then
  TARGETS=(LeanQbe LeanQbeAmd64 LeanQbeArm64 LeanQbeTest LeanQbeBootstrap0 LeanQbeBootstrap0Test leanqbe leanqbe-arm64)
else
  TARGETS=(LeanQbe)
  if [ "$RESOLVED_SCOPE" = "x64" ]; then
    TARGETS+=(LeanQbeAmd64 LeanQbeBootstrap0 LeanQbeBootstrap0Test leanqbe)
  else
    TARGETS+=(LeanQbeArm64 leanqbe-arm64)
  fi
  printf '%s\n' "$CHANGED_FILES" >"$TMP/changed_files.txt"
  mapfile -t SCOPED_TESTS < <(
    timeout 60 python3 -B "$TMP/arch_scope.py" scoped-tests \
      "$RESOLVED_SCOPE" "$TMP/headlines_all.txt" "$TMP/changed_files.txt"
  )
  TARGETS+=("${SCOPED_TESTS[@]}")
fi

echo "== 1. build (warnings as errors, LAKE_JOBS=$LAKE_JOBS): ${TARGETS[*]}"
build_cmd=(timeout --foreground "$BUILD_TIMEOUT" env "LEAN_NUM_THREADS=$LAKE_JOBS" lake build --wfail "${TARGETS[@]}")
if [ "$CHECK_NO_SCOPE" != "1" ] \
    && command -v systemd-run >/dev/null 2>&1 \
    && systemd-run --user --scope true >/dev/null 2>&1; then
  SCOPE_UNIT="leanqbe-check-${$}-$(date +%s).scope"
  build_cmd=(systemd-run --user --scope --quiet --unit="$SCOPE_UNIT" \
    -p "MemoryMax=$CHECK_MEM_MAX" -p OOMPolicy=kill "${build_cmd[@]}")
fi
if [ "$CHECK_NO_LOCK" != "1" ] && command -v flock >/dev/null 2>&1; then
  if ! flock -n "$CHECK_LOCK_FILE" true 2>/dev/null; then
    echo "   waiting for build lock: $CHECK_LOCK_FILE"
  fi
  flock -F "$CHECK_LOCK_FILE" "${build_cmd[@]}" >"$TMP/build.log" 2>&1 &
  build_pid=$!
  wait "$build_pid"
  rc=$?
else
  "${build_cmd[@]}" >"$TMP/build.log" 2>&1 &
  build_pid=$!
  wait "$build_pid"
  rc=$?
fi
build_pid=""
if [ -n "$SCOPE_UNIT" ]; then
  systemctl --user stop "$SCOPE_UNIT" >/dev/null 2>&1 || true
  SCOPE_UNIT=""
fi
grep -E '^(✖|error|warning)|warning:|error:' "$TMP/build.log" | head -100
tail -n 1 "$TMP/build.log"
[ $rc -eq 0 ] || err "lake build exited with $rc (124 = timeout); full log: rerun 'lake build --wfail ${TARGETS[*]}'"

echo "== 2. sorry"
if grep -n "declaration uses 'sorry'\|declaration uses \`sorry\`\|sorryAx" "$TMP/build.log"; then
  err "sorry in the build"
fi

echo "== 2b. forbidden tokens & native-code tactics across all tracked .lean files"
scan_lean_forbidden_tokens \
  || err "forbidden token (sorry/admit/axiom/@[implemented_by]/@[extern]/trustCompiler/native tactic) in a .lean file"

echo "== 3. import closures"
python3 - "$TMP" "$RESOLVED_SCOPE" <<'PY' || err "import closure or reachability check failed"
import json, pathlib, re, subprocess, sys

tmp = pathlib.Path(sys.argv[1])
scope = sys.argv[2]

imp_re = re.compile(
    r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.']+)"
)

def extract_imports(p: pathlib.Path):
    imps = []
    depth = 0
    with p.open("r", encoding="utf-8") as f:
        for line in f:
            if depth == 0 and "import" not in line and "/-" not in line:
                continue
            out = []
            i, n = 0, len(line)
            while i < n:
                if depth > 0:
                    if i + 1 < n and line[i:i+2] == "/-":
                        depth += 1
                        i += 2
                    elif i + 1 < n and line[i:i+2] == "-/":
                        depth -= 1
                        i += 2
                    else:
                        i += 1
                elif i + 1 < n and line[i:i+2] == "--":
                    break
                elif i + 1 < n and line[i:i+2] == "/-":
                    depth += 1
                    i += 2
                else:
                    out.append(line[i])
                    i += 1
            cleaned_line = "".join(out).strip()
            if cleaned_line:
                m = imp_re.match(cleaned_line)
                if m:
                    imps.append(m.group(1))
    return imps

def closure(roots):
    seen, stack = set(), list(roots)
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        p = pathlib.Path(mod.replace(".", "/") + ".lean")
        if p.is_file():
            for imp in extract_imports(p):
                stack.append(imp)
    return sorted(seen)

# Fallback guard: if lake-manifest.json has external dependencies, use Lean #eval
has_external_packages = False
manifest_p = pathlib.Path("lake-manifest.json")
if manifest_p.is_file():
    try:
        data = json.loads(manifest_p.read_text(encoding="utf-8"))
        if data.get("packages"):
            has_external_packages = True
    except Exception:
        pass

if has_external_packages:
    def lean_closure(root):
        lean_src = f"import Lean\nimport {root}\nopen Lean in\n#eval show CoreM Unit from do\n  for n in (← getEnv).header.moduleNames do\n    IO.println s!\"MOD {{n}}\"\n"
        f = tmp / f"Closure_{root}.lean"
        f.write_text(lean_src, encoding="utf-8")
        out = subprocess.check_output(["lake", "env", "lean", str(f)]).decode("utf-8")
        return [l[4:].strip() for l in out.splitlines() if l.startswith("MOD ")]
    active_fn = lean_closure
else:
    active_fn = lambda r: closure([r])

case_roots = {
    "x64": ["LeanQbe", "LeanQbeAmd64"],
    "arm64": ["LeanQbe", "LeanQbeArm64"],
    "full": ["LeanQbe", "LeanQbeAmd64", "LeanQbeArm64"],
}[scope]

closures = {}
for r in case_roots:
    c = active_fn(r)
    closures[r] = set(c)
    (tmp / f"closure_{r}.txt").write_text("\n".join(c) + "\n", encoding="utf-8")

errors = []

# Generic LeanQbe architecture check
if "LeanQbe" in closures:
    kraken_in_gen = [m for m in closures["LeanQbe"] if m.startswith(("Kraken.X64", "Kraken.AArch64"))]
    if kraken_in_gen:
        errors.append(f"the generic LeanQbe imports an architecture ({', '.join(kraken_in_gen)})")

if scope != "arm64" and "LeanQbeAmd64" in closures:
    kraken_aarch = [m for m in closures["LeanQbeAmd64"] if m.startswith("Kraken.AArch64")]
    if kraken_aarch:
        errors.append(f"LeanQbeAmd64 imports Kraken.AArch64 ({', '.join(kraken_aarch)})")

if scope != "x64" and "LeanQbeArm64" in closures:
    kraken_x64 = [m for m in closures["LeanQbeArm64"] if m.startswith("Kraken.X64")]
    if kraken_x64:
        errors.append(f"LeanQbeArm64 imports Kraken.X64 ({', '.join(kraken_x64)})")

for r in case_roots:
    if r not in closures[r]:
        errors.append(f"could not compute the closure of {r}")

legacy_cert_re = re.compile(
    r"^LeanQbe\.T\.(Amd64|Arm64)\.(Kissat|KissatCorePlus|KissatFull.*|KissatFastSched.*|KissatFast.*|KissatPlain.*|KissatM3.*|KissatM4.*)$"
)
if scope != "arm64" and "LeanQbeAmd64" in closures:
    legacy_in_x64 = [m for m in closures["LeanQbeAmd64"] if legacy_cert_re.match(m)]
    if legacy_in_x64:
        errors.append(f"active LeanQbeAmd64 closure imports legacy Kissat certs ({', '.join(legacy_in_x64)})")

if scope != "x64" and "LeanQbeArm64" in closures:
    legacy_in_arm = [m for m in closures["LeanQbeArm64"] if legacy_cert_re.match(m)]
    if legacy_in_arm:
        errors.append(f"active LeanQbeArm64 closure imports legacy Kissat certs ({', '.join(legacy_in_arm)})")

# Legacy & Bootstrap0 closures
for arch in ("Amd64", "Arm64"):
    mods = closure([f"LeanQbeLegacy{arch}"])
    closures[f"legacy_{arch}"] = set(mods)
    (tmp / f"legacy_closure_{arch}.txt").write_text("\n".join(mods) + "\n", encoding="utf-8")

b0_mods = closure(["LeanQbeBootstrap0"])
closures["bootstrap0"] = set(b0_mods)
(tmp / "bootstrap0_closure.txt").write_text("\n".join(b0_mods) + "\n", encoding="utf-8")

raw_b0t = subprocess.check_output(
    ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard", "LeanQbeBootstrap0Test"]
)
b0t_roots = [
    f.decode("utf-8")[:-5].replace("/", ".")
    for f in raw_b0t.split(b"\0")
    if f and f.decode("utf-8").endswith(".lean")
]
b0t_mods = closure(b0t_roots)
closures["bootstrap0_test"] = set(b0t_mods)
(tmp / "bootstrap0_test_closure.txt").write_text("\n".join(b0t_mods) + "\n", encoding="utf-8")

if scope != "arm64":
    if any(m.startswith(("Kraken.AArch64", "LeanQbe.T.Arm64.")) for m in closures["legacy_Amd64"]):
        errors.append("LeanQbeLegacyAmd64 imports AArch64/Arm64 modules")
    if any(m.startswith(("Kraken.AArch64", "LeanQbe.T.Arm64.")) for m in closures["bootstrap0"]):
        errors.append("LeanQbeBootstrap0 imports AArch64/Arm64 modules")
    if any(m.startswith(("Kraken.AArch64", "LeanQbe.T.Arm64.")) for m in closures["bootstrap0_test"]):
        errors.append("LeanQbeBootstrap0Test imports AArch64/Arm64 modules")
    if any(legacy_cert_re.match(m) for m in closures["bootstrap0"]):
        errors.append("LeanQbeBootstrap0 closure imports legacy Kissat certs")
    if any(legacy_cert_re.match(m) for m in closures["bootstrap0_test"]):
        errors.append("LeanQbeBootstrap0Test closure imports legacy Kissat certs")

if scope != "x64":
    if any(m.startswith(("Kraken.X64", "LeanQbe.T.Amd64.")) for m in closures["legacy_Arm64"]):
        errors.append("LeanQbeLegacyArm64 imports X64/Amd64 modules")

# Reachability check of tracked LeanQbe/T/*.lean files
raw_tracked = subprocess.check_output(
    ["git", "ls-files", "-z", "--cached", "LeanQbe/T/*.lean", "LeanQbe/T/**/*.lean"]
)
tracked_files = sorted(f.decode("utf-8") for f in raw_tracked.split(b"\0") if f)

for f in tracked_files:
    m = f[:-5].replace("/", ".")
    if m.startswith("LeanQbe.T.Amd64."):
        if scope == "arm64":
            continue
        if m not in closures.get("LeanQbeAmd64", set()) and m not in closures.get("legacy_Amd64", set()):
            errors.append(f"{f} is not imported by LeanQbeAmd64.lean or LeanQbeLegacyAmd64.lean")
    elif m.startswith("LeanQbe.T.Bootstrap0."):
        if scope == "arm64":
            continue
        if m not in closures.get("bootstrap0", set()):
            errors.append(f"{f} is not imported by LeanQbeBootstrap0.lean")
    elif m.startswith("LeanQbe.T.Arm64."):
        if scope == "x64":
            continue
        if m not in closures.get("LeanQbeArm64", set()) and m not in closures.get("legacy_Arm64", set()):
            errors.append(f"{f} is not imported by LeanQbeArm64.lean or LeanQbeLegacyArm64.lean")
    else:
        if m not in closures.get("LeanQbe", set()):
            errors.append(f"{f} is not imported by the root LeanQbe.lean (so it is not built)")

if errors:
    for e in errors:
        print(f"FAIL: {e}", file=sys.stderr)
    sys.exit(1)
PY
if git ls-files --cached 'LeanQbe/*.lean' 'LeanQbe/**/*.lean' | grep -v '^LeanQbe/T/'; then
  err "retired untyped E1 .lean files remain tracked under LeanQbe/ outside LeanQbe/T/"
fi
if git ls-files --cached 'LeanQbeTest/*.lean' 'LeanQbeTest/**/*.lean' | grep -v '^LeanQbeTest/T/'; then
  err "retired untyped E1 .lean files remain tracked under LeanQbeTest/ outside LeanQbeTest/T/"
fi
if git ls-files --cached 'LeanQbeTest/*SpikeS2*' 'LeanQbeTest/**/*SpikeS2*' | grep .; then
  err "temporary SpikeS2 files remain tracked under LeanQbeTest/"
fi
if git ls-files -z 'LeanQbe/T/*.lean' 'LeanQbe/T/**/*.lean' \
    | (set +o pipefail; xargs -0 grep -HnE '^\s*(public\s+|meta\s+)*import\s+(all\s+)?LeanQbe\.([^T]|T[^.])' 2>/dev/null); then
  err "LeanQbe/T module imports untyped E1 module (G5 violation)"
fi
if git ls-files -z 'LeanQbeBootstrap0Test/*.lean' 'LeanQbeBootstrap0Test/**/*.lean' \
    | (set +o pipefail; xargs -0 grep -HnE '^\s*(public\s+|meta\s+)*import\s+(all\s+)?LeanQbe\.([^T]|T[^.])' 2>/dev/null); then
  err "LeanQbeBootstrap0Test module imports untyped E1 module (G5 violation)"
fi

echo "== 3b. incrementality firewall & barrel hub lint"
if [ -f "$ROOT/scripts/check_firewall.py" ]; then
  timeout 60 python3 -B "$ROOT/scripts/check_firewall.py" --root "$ROOT" --require-isa \
    || err "incrementality firewall check failed (check_firewall.py)"
else
  err "missing $ROOT/scripts/check_firewall.py"
fi
if [ -f "$ROOT/scripts/sync_hubs.py" ]; then
  timeout 60 python3 -B "$ROOT/scripts/sync_hubs.py" --root "$ROOT" --check \
    || err "barrel/hub check failed (sync_hubs.py --check)"
fi

echo "== 4. axiom audit"
# Build log: every `#print axioms` that the build printed.
grep -E "depends on axioms|does not depend on any axioms" "$TMP/build.log" >"$TMP/axioms.txt" || true
# Headline theorems: `<Module> <constant>` from scripts/headlines.d/*.txt (or
# scripts/headline.txt), filtered by INCLUDE_LEGACY and CHECK_SCOPE, partitioned into
# parallel batches (generic, x64, arm64, plus isolated root-`main` modules so separate
# executables never collide on `main`). Falls back to 16-way per-module audit if needed.
if [ "$headline_total" -gt 0 ]; then
  timeout 60 python3 -B "$TMP/arch_scope.py" audit-batches "$TMP" "$RESOLVED_SCOPE" \
    || err "headline audit batching failed"

  want="$(wc -l <"$TMP/selected_headlines.txt" | tr -d ' ')"
  if [ "$want" -gt 0 ]; then
    batch_names=()
    batch_pids=()
    batch_jobs="${AUDIT_JOBS:-16}"
    : >"$TMP/fallback_mods.txt"
    [ -s "$TMP/mods_conflict.txt" ] && cat "$TMP/mods_conflict.txt" >>"$TMP/fallback_mods.txt"
    for audit_lean in "$TMP"/Batch_*.lean; do
      [ -s "$audit_lean" ] || continue
      b="$(basename "$audit_lean" .lean)"
      b="${b#Batch_}"
      while [ "$(jobs -rp | wc -l)" -ge "$batch_jobs" ]; do
        wait -n 2>/dev/null || true
      done
      timeout "$LEAN_TIMEOUT" lake env lean "$audit_lean" \
        >"$TMP/audit_batch_${b}.out" 2>&1 &
      batch_pids+=("$!")
      batch_names+=("$b")
    done
    for i in "${!batch_names[@]}"; do
      b="${batch_names[$i]}"
      if ! wait "${batch_pids[$i]}"; then
        echo "NOTE: batch audit_${b} failed; falling back to per-module parallel audit"
        rm -f "$TMP/audit_batch_${b}.out"
        cat "$TMP/mods_batch_${b}.txt" >>"$TMP/fallback_mods.txt"
      fi
    done

    if [ -s "$TMP/fallback_mods.txt" ]; then
      fb_jobs="${AUDIT_JOBS:-16}"
      fb_idx=0
      fb_pids=()
      fb_mods=()
      while IFS= read -r mod; do
        [ -n "$mod" ] || continue
        fb_idx=$((fb_idx + 1))
        f="$TMP/Audit_fb_${fb_idx}.lean"
        echo "import $mod" >"$f"
        awk -v m="$mod" '$1 == m {print "#print axioms " $2}' "$TMP/selected_headlines.txt" >>"$f"
        while [ "$(jobs -rp | wc -l)" -ge "$fb_jobs" ]; do
          wait -n 2>/dev/null || true
        done
        timeout "$LEAN_TIMEOUT" lake env lean "$f" >"$TMP/audit_fb_${fb_idx}.out" 2>&1 &
        fb_pids+=("$!")
        fb_mods+=("$mod:$fb_idx")
      done <"$TMP/fallback_mods.txt"
      for i in "${!fb_pids[@]}"; do
        if ! wait "${fb_pids[$i]}"; then
          IFS=: read -r mod idx <<<"${fb_mods[$i]}"
          cat "$TMP/audit_fb_${idx}.out"
          err "axiom audit of $mod failed to elaborate"
        fi
      done
    fi

    for outf in "$TMP"/audit_*.out; do
      [ -f "$outf" ] || continue
      sed 's/^/headline: /' "$outf"
      cat "$outf" >>"$TMP/axioms.txt"
    done
  else
    err "no headline theorems selected for scope=$RESOLVED_SCOPE (INCLUDE_LEGACY=$INCLUDE_LEGACY)"
  fi
else
  want=0
  err "no headline theorem to audit in scripts/headlines.d/ or scripts/headline.txt"
fi
# Every headline theorem must have one complete report: the loop below fails on the lines that are
# not a complete report, and this count fails if a report is missing.
got="$(cat "$TMP"/audit_*.out 2>/dev/null | grep -cE 'depends on axioms: \[.*\]$|does not depend on any axioms$')"
echo "$(grep -c . "$TMP/axioms.txt") lines of axiom reports; $got complete reports for $want headline theorems"
[ "$got" -eq "$want" ] || err "$got complete one-line axiom reports for $want headline theorems"
while IFS= read -r line; do
  case "$line" in
    *"does not depend on any axioms") continue ;;
    *"depends on axioms: ["*"]") ;;
    *) err "axiom report is not one complete line (Lean breaks a long report over lines), so its axioms cannot be read: $line"; continue ;;
  esac
  axs="$(sed -n 's/.*depends on axioms: \[\(.*\)\].*/\1/p' <<<"$line" | tr -d ' ' | tr ',' ' ')"
  for a in $axs; do
    case " $ALLOWED " in *" $a "*) ;; *) err "disallowed axiom $a: $line" ;; esac
  done
done <"$TMP/axioms.txt"

if [ "${CHECK_TIMES:-0}" = "1" ]; then
  echo "== 5. check times (CPU)"
  time_check() { # $1 = .lean file; appends "<CPU seconds> <exit code> <file>" to $TMP/times.txt
    local cpu rc
    cpu="$( { TIMEFORMAT='%U %S'; time timeout "$LEAN_TIMEOUT" lake env lean "$1" >/dev/null 2>&1; } 2>&1 )"
    rc=$?
    echo "$(awk '{print int($1 + $2 + 0.5)}' <<<"$cpu") $rc $1" >>"$TMP/times.txt"
  }
  : >"$TMP/timed.txt"
  cand_arches=()
  [ "$RESOLVED_SCOPE" != "arm64" ] && cand_arches+=(Amd64)
  [ "$RESOLVED_SCOPE" != "x64" ] && cand_arches+=(Arm64)
  for arch in "${cand_arches[@]}"; do
    for mod in LratBytes KissatM5Cert1 KissatM5Cert KissatM5CertLink KissatM5 KissatM5Sound \
        KissatM6Cert1 KissatM6Cert KissatM6CertLink KissatM6 \
        KissatM7PlusCert1 KissatM7PlusCert KissatM7PlusCertLink KissatM7Plus \
        KissatM7FidelityCert1 KissatM7FidelityCert KissatM7FidelityCertLink KissatM7Fidelity; do
      [ -f "LeanQbe/T/$arch/$mod.lean" ] && echo "LeanQbe/T/$arch/$mod.lean" >>"$TMP/timed.txt"
    done
    if [ "$INCLUDE_LEGACY" = "1" ]; then
      for mod in Kissat KissatCorePlus KissatPlainCert1 KissatPlainCert KissatPlain \
          KissatM3Cert1a KissatM3Cert KissatM3 \
          KissatM4Cert1 KissatM4Cert KissatM4CertLink KissatM4 KissatM4Sound; do
        [ -f "LeanQbe/T/$arch/$mod.lean" ] && echo "LeanQbe/T/$arch/$mod.lean" >>"$TMP/timed.txt"
      done
    fi
  done
  git ls-files 'LeanQbe/*Lemmas*.lean' 'LeanQbe/**/*Lemmas*.lean' | sort -u | xargs wc -l \
    | grep -v ' total$' | sort -rn | head -n 5 | awk '{print $2}' >>"$TMP/timed.txt"
  : >"$TMP/times.txt"
  times_jobs="${CHECK_TIMES_JOBS:-4}"
  while IFS= read -r f; do
    [ -f "$f" ] || continue
    while [ "$(jobs -rp | wc -l)" -ge "$times_jobs" ]; do
      wait -n 2>/dev/null || true
    done
    time_check "$f" &
  done <"$TMP/timed.txt"
  wait
  while read -r cpu rc f; do
    printf '%4d s  %s\n' "$cpu" "$f"
    [ "$rc" -eq 0 ] || err "$f failed to check (exit code $rc; 124 = timeout)"
  done <"$TMP/times.txt"
else
  echo "== 5. standalone timing skipped (set CHECK_TIMES=1 to run) =="
fi

if [ $fail -eq 0 ]; then echo "== check.sh: ALL PASSED"; else echo "== check.sh: FAILED"; fi
exit $fail
