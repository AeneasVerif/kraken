#!/usr/bin/env bash
# lean-qbe quality gate. Run from anywhere: scripts/check.sh
#
# Environment knobs:
#   CHECK_SCOPE=full|auto|rdeps|x64|arm64
#       Defaults to `full` when `CHECK_BASE` is unset (100% backward compatible), or `auto`
#       when `CHECK_BASE` is set. In `auto` mode (with `CHECK_BASE` defaulting to `HEAD~1`),
#       a fail-closed classifier selects:
#         - `class0`: ONLY when >=1 files changed, 0 `.lean`/gate/toolchain files changed, and
#           100% of changed files match the non-Lean allowlist (0 `lake` calls, <15s).
#         - `rdeps`:  Graph-driven reverse-dependency scope via `scripts/rdeps_scope.py` when
#           changed files are non-core `.lean` + safe non-`.lean` files with `0` deletions and
#           `|rdeps| <= CHECK_RDEPS_MAX` (default `250`). Uses a 2-slot fast-lane lock
#           (`/tmp/leanqbe_check_fast_{0,1}.lock`) and `MemoryMax=16G`.
#         - `x64`:    ONLY when `rdeps` fails closed and 100% of changed `.lean` files are under
#           `LeanQbe/T/Amd64/` or `LeanQbeTest/T/*{X64,Amd64}*.lean`, and any non-`.lean` files
#           are docs / `scripts/headlines.d/amd64.txt`. Skips `LeanQbeArm64` & `leanqbe-arm64`.
#         - `arm64`:  Symmetric for `LeanQbe/T/Arm64/` / `LeanQbeTest/T/*Arm64*.lean`.
#         - `full`:   Fail-closed default for any other file or empty/unresolvable diff.
#   CHECK_RDEPS_MAX=<N>
#       Maximum reverse-dependency closure size allowed for `rdeps` before failing closed
#       (default: `250`).
#   INCLUDE_LEGACY=0|1
#       Controls whether `scripts/headlines.d/*legacy*.txt` files are audited in Step 4.
#       Defaults to `0` if `LeanQbeLegacy*` targets exist in `lakefile.toml`, else `1`.
#   LAKE_JOBS=<N>
#       Sets `LEAN_NUM_THREADS=$LAKE_JOBS` for Step 1 `lake build` (defaults to
#       `${LEAN_NUM_THREADS:-6}` so uncapped runs never spawn `nproc` `lean` workers;
#       Lake 5.0 controls build concurrency via `LEAN_NUM_THREADS`, as `lake build -j`
#       does not exist).
#   CHECK_LOCK_FILE=<path>
#       Advisory `flock` lockfile serializing heavy Step 1 `lake build` (`full|x64|arm64`)
#       (default: `/tmp/leanqbe_check_build.lock`). Fast-lane `rdeps` builds use a 2-slot
#       lock (`${CHECK_FAST_LOCK_PREFIX:-/tmp/leanqbe_check_fast}_{0,1}.lock`). Set
#       `CHECK_NO_LOCK=1` to bypass.
#   CHECK_MEM_MAX=<size>
#       `MemoryMax` passed to `systemd-run --user --scope --slice=leanqbe-builds.slice`
#       (with `MemorySwapMax=0`, `OOMPolicy=kill`) for Step 1 `lake build`
#       (default: `48G` for heavy scopes, `16G` via `CHECK_FAST_MEM_MAX` for `rdeps`).
#       Set `CHECK_NO_SCOPE=1` to bypass.
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
#  4. Single-session compiled `.olean` axiom & `isUnsafe` audit (`audit_axioms` over
#     `importModules (loadExts := false)`) for active `scripts/headlines.d/*.txt` (or
#     `scripts/headline.txt` if `headlines.d` is absent), plus `#print axioms` verification
#     from the Step 1 build log (`<= std3` and `!isUnsafe`).
#  5. Standalone re-elaboration timing when `CHECK_TIMES=1`.
#
# Every command runs under `timeout`. Exit code 0 iff all checks pass.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# shellcheck source=scripts/common.sh
source "$ROOT/scripts/common.sh"
leanqbe_export_lake_cache

classify_stdin() {
  python3 -B "$ROOT/scripts/lean_imports.py" classify-stdin
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
USER_CHECK_LOCK_FILE="${CHECK_LOCK_FILE+set}"
USER_CHECK_MEM_MAX="${CHECK_MEM_MAX+set}"
CHECK_LOCK_FILE="${CHECK_LOCK_FILE:-/tmp/leanqbe_check_build.lock}"
CHECK_FAST_LOCK_PREFIX="${CHECK_FAST_LOCK_PREFIX:-/tmp/leanqbe_check_fast}"
CHECK_MEM_MAX="${CHECK_MEM_MAX:-48G}"
CHECK_FAST_MEM_MAX="${CHECK_FAST_MEM_MAX:-16G}"
CHECK_RDEPS_MAX="${CHECK_RDEPS_MAX:-250}"
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
  auto|rdeps|x64|arm64|full) ;;
  *) echo "FAIL: invalid CHECK_SCOPE='$CHECK_SCOPE' (expected auto|rdeps|x64|arm64|full)" >&2; exit 2 ;;
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

RDEPS_LEG_ARGS=()
[ "$INCLUDE_LEGACY" = "1" ] && RDEPS_LEG_ARGS=(--include-legacy)

rdeps_scope_ok() {
  [ -n "$CHANGED_FILES" ] && [ -f "$ROOT/scripts/rdeps_scope.py" ] \
    && printf '%s\n' "$CHANGED_FILES" | timeout 60 python3 -B "$ROOT/scripts/rdeps_scope.py" \
      --root "$ROOT" --changed - --base "$CHECK_BASE" \
      --max-rdeps "$CHECK_RDEPS_MAX" "${RDEPS_LEG_ARGS[@]}" --check-only >/dev/null 2>&1
}

CHANGED_FILES=""
RESOLVED_SCOPE="$CHECK_SCOPE"
if [ "$CHECK_SCOPE" = "auto" ] || [ "$CHECK_SCOPE" = "rdeps" ]; then
  CHECK_BASE="${CHECK_BASE:-HEAD~1}"
  if git rev-parse --verify "${CHECK_BASE}^{commit}" >/dev/null 2>&1; then
    if CHANGED_FILES="$({
      git diff --name-only --no-renames "${CHECK_BASE}...HEAD" &&
      git diff --name-only --no-renames HEAD &&
      git ls-files --others --exclude-standard
    } | sort -u)"; then
      if [ "$CHECK_SCOPE" = "auto" ]; then
        has_deleted=0
        while IFS= read -r cf; do
          [ -n "$cf" ] && [ ! -f "$ROOT/$cf" ] && { has_deleted=1; break; }
        done <<<"$CHANGED_FILES"
        STATIC_SCOPE="$(printf '%s\n' "$CHANGED_FILES" | classify_stdin)"
        if [ "$has_deleted" -eq 1 ]; then
          RESOLVED_SCOPE="full"
        elif [ "$STATIC_SCOPE" = "class0" ]; then
          RESOLVED_SCOPE="class0"
        elif rdeps_scope_ok; then
          RESOLVED_SCOPE="rdeps"
        else
          RESOLVED_SCOPE="$STATIC_SCOPE"
        fi
      elif rdeps_scope_ok; then
        RESOLVED_SCOPE="rdeps"
      else
        RESOLVED_SCOPE="full"
      fi
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
_LEANQBE_CLEANUP_PATHS+=("$TMP")
leanqbe_register_traps
fail=0
err() { echo "FAIL: $*"; fail=1; }

scan_lean_forbidden_tokens() {
  timeout 60 python3 -B "$ROOT/scripts/lean_imports.py" scan-forbidden "$ROOT"
}

check_e1_g5_hygiene() {
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
  local g5_re='^\s*(public\s+|meta\s+)*import\s+(all\s+)?LeanQbe\.([^T]|T[^.])'
  if git ls-files -z 'LeanQbe/T/*.lean' 'LeanQbe/T/**/*.lean' \
      | (set +o pipefail; xargs -0 grep -HnE "$g5_re" 2>/dev/null); then
    err "LeanQbe/T module imports untyped E1 module (G5 violation)"
  fi
}

echo "== check.sh: scope=$RESOLVED_SCOPE (requested=$CHECK_SCOPE, INCLUDE_LEGACY=$INCLUDE_LEGACY)"

# Collect active headline lines (<Module> <const>) into $TMP/headlines_all.txt
python3 -B "$ROOT/scripts/_common.py" collect-headlines "$ROOT" "$INCLUDE_LEGACY" "$TMP/headlines_all.txt"

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

  echo "== 2c0b. scripts unit tests & pure-Python gates (0 lake calls)"
  timeout 180 env PYTHONDONTWRITEBYTECODE=1 CHECK_NO_LAKE_TESTS=1 \
    python3 -B -m unittest discover -s "$ROOT/scripts" -p 'test_*.py' \
    >"$TMP/scripts_unittest.log" 2>&1 \
    || { tail -n 30 "$TMP/scripts_unittest.log"; err "scripts unit tests failed (unittest discover)"; }
  timeout 60 python3 -B "$ROOT/scripts/check_firewall.py" --root "$ROOT" --require-isa \
    || err "incrementality firewall check failed (check_firewall.py)"
  timeout 60 python3 -B "$ROOT/scripts/sync_hubs.py" --root "$ROOT" --check \
    || err "barrel/hub check failed (sync_hubs.py --check)"

  echo "== 3c0. forbidden tokens, native-code tactics & tracked-file hygiene (0 lake calls)"
  scan_lean_forbidden_tokens \
    || err "forbidden token (sorry/admit/axiom/@[implemented_by]/@[extern]/trustCompiler/native tactic) in a .lean file"
  check_e1_g5_hygiene
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

# Determine scoped Step 1 build targets
if [ "$RESOLVED_SCOPE" = "full" ]; then
  TARGETS=(LeanQbe LeanQbeAmd64 LeanQbeArm64 LeanQbeTest LeanQbeBootstrap0 LeanQbeBootstrap0Test leanqbe leanqbe-arm64)
elif [ "$RESOLVED_SCOPE" = "rdeps" ]; then
  printf '%s\n' "$CHANGED_FILES" >"$TMP/changed_files.txt"
  if mapfile -t TARGETS < <(
    timeout 60 python3 -B "$ROOT/scripts/rdeps_scope.py" \
      --root "$ROOT" --changed "$TMP/changed_files.txt" \
      --base "${CHECK_BASE:-HEAD~1}" \
      --max-rdeps "$CHECK_RDEPS_MAX" "${RDEPS_LEG_ARGS[@]}" \
      --out-headlines "$TMP/rdeps_headlines_filter.txt"
  ) && [ "${#TARGETS[@]}" -gt 0 ]; then
    :
  else
    echo "   rdeps exceeded cap or hit core/deleted file; failing closed to full"
    RESOLVED_SCOPE="full"
    TARGETS=(LeanQbe LeanQbeAmd64 LeanQbeArm64 LeanQbeTest LeanQbeBootstrap0 LeanQbeBootstrap0Test leanqbe leanqbe-arm64)
  fi
else
  TARGETS=(LeanQbe)
  if [ "$RESOLVED_SCOPE" = "x64" ]; then
    TARGETS+=(LeanQbeAmd64 LeanQbeBootstrap0 LeanQbeBootstrap0Test leanqbe)
  else
    TARGETS+=(LeanQbeArm64 leanqbe-arm64)
  fi
  printf '%s\n' "$CHANGED_FILES" >"$TMP/changed_files.txt"
  mapfile -t SCOPED_TESTS < <(
    timeout 60 python3 -B "$ROOT/scripts/_common.py" scoped-tests "$ROOT" \
      "$RESOLVED_SCOPE" "$TMP/headlines_all.txt" "$TMP/changed_files.txt"
  )
  TARGETS+=("${SCOPED_TESTS[@]}")
fi

ACTIVE_MEM_MAX="$CHECK_MEM_MAX"
if [ "$RESOLVED_SCOPE" = "rdeps" ] && [ -z "$USER_CHECK_MEM_MAX" ]; then
  ACTIVE_MEM_MAX="$CHECK_FAST_MEM_MAX"
fi

echo "== 1. build (warnings as errors, LAKE_JOBS=$LAKE_JOBS, MemoryMax=$ACTIVE_MEM_MAX): ${TARGETS[*]}"
cgroup_lock_args=()
if [ "$RESOLVED_SCOPE" = "rdeps" ] && [ -z "$USER_CHECK_LOCK_FILE" ]; then
  cgroup_lock_args=(--fast-lock "$CHECK_FAST_LOCK_PREFIX")
else
  cgroup_lock_args=(--lock "$CHECK_LOCK_FILE")
fi
rc=0
run_cgroup --mem "$ACTIVE_MEM_MAX" --unit-prefix leanqbe-check \
  --timeout "$BUILD_TIMEOUT" --log "$TMP/build.log" "${cgroup_lock_args[@]}" -- \
  env "LEAN_NUM_THREADS=$LAKE_JOBS" lake build --wfail "${TARGETS[@]}" || rc=$?
leanqbe_print_build_summary "$TMP/build.log"
[ $rc -eq 0 ] || err "lake build exited with $rc (124 = timeout); full log: rerun 'lake build --wfail ${TARGETS[*]}'"

echo "== 2. sorry"
if leanqbe_has_sorry_in_log "$TMP/build.log"; then
  err "sorry in the build"
fi

echo "== 2b. forbidden tokens & native-code tactics across all tracked .lean files"
scan_lean_forbidden_tokens \
  || err "forbidden token (sorry/admit/axiom/@[implemented_by]/@[extern]/trustCompiler/native tactic) in a .lean file"

echo "== 3. import closures"
timeout 60 python3 -B "$ROOT/scripts/_common.py" check-closures "$ROOT" "$TMP" "$RESOLVED_SCOPE" \
  || err "import closure or reachability check failed"
check_e1_g5_hygiene
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
if [ "$RESOLVED_SCOPE" = "full" ] || printf '%s\n' "$CHANGED_FILES" | grep -q '^scripts/'; then
  echo "== 3c. scripts unit tests (unittest discover)"
  timeout 180 env PYTHONDONTWRITEBYTECODE=1 \
    python3 -B -m unittest discover -s "$ROOT/scripts" -p 'test_*.py' \
    >"$TMP/scripts_unittest.log" 2>&1 \
    || { tail -n 30 "$TMP/scripts_unittest.log"; err "scripts unit tests failed (unittest discover)"; }
fi

echo "== 4. axiom & isUnsafe audit"
# Build log: every `#print axioms` that the build printed.
grep -E "depends on axioms|does not depend on any axioms" "$TMP/build.log" >"$TMP/axioms.txt" || true
# Headline theorems: `<Module> <constant>` from scripts/headlines.d/*.txt (or
# scripts/headline.txt), filtered by INCLUDE_LEGACY and CHECK_SCOPE, audited in a
# single compiled `audit_axioms` session (`importModules (loadExts := false)`,
# O(V+E) shared `Std.HashSet Name`, verifying `<= std3` and `!isUnsafe`).
want=0
got=0
if [ "$headline_total" -gt 0 ]; then
  rdeps_filter_arg=""
  [ "$RESOLVED_SCOPE" = "rdeps" ] && [ -f "$TMP/rdeps_headlines_filter.txt" ] \
    && rdeps_filter_arg="$TMP/rdeps_headlines_filter.txt"
  timeout 60 python3 -B "$ROOT/scripts/_common.py" audit-batches "$ROOT" "$TMP" "$RESOLVED_SCOPE" "$rdeps_filter_arg" \
    || err "headline audit batching failed"

  want="$(wc -l <"$TMP/selected_headlines.txt" | tr -d ' ')"
  if [ "$want" -gt 0 ]; then
    audit_key="$(cat "$ROOT/lean-toolchain" "$ROOT/scripts/AuditAxioms.lean" | sha256sum | cut -c1-16)"
    local_bin="$ROOT/.lake/build/bin/audit_axioms"
    local_key_file="$ROOT/.lake/build/bin/audit_axioms.key"
    cache_dir="${AUDIT_AXIOMS_CACHE_DIR:-${XDG_CACHE_HOME:-$HOME/.cache}/lean-qbe}"
    cache_bin="$cache_dir/audit_axioms-${audit_key}"
    AUDIT_BIN=""
    if [ -x "$local_bin" ] && [ -f "$local_key_file" ] \
        && [ "$(cat "$local_key_file" 2>/dev/null || true)" = "$audit_key" ]; then
      AUDIT_BIN="$local_bin"
    elif [ -x "$cache_bin" ]; then
      AUDIT_BIN="$cache_bin"
    else
      if run_cgroup --mem "$ACTIVE_MEM_MAX" --unit-prefix leanqbe-audit \
          --timeout "$LEAN_TIMEOUT" --log "$TMP/audit_build.log" -- \
          env "LEAN_NUM_THREADS=$LAKE_JOBS" lake build --wfail audit_axioms; then
        AUDIT_BIN="$local_bin"
        printf '%s\n' "$audit_key" >"$local_key_file" 2>/dev/null || true
        if mkdir -p "$cache_dir" 2>/dev/null; then
          cp -f "$local_bin" "$cache_bin.tmp.$$" 2>/dev/null \
            && chmod +x "$cache_bin.tmp.$$" 2>/dev/null \
            && mv -f "$cache_bin.tmp.$$" "$cache_bin" 2>/dev/null \
            || rm -f "$cache_bin.tmp.$$" 2>/dev/null || true
        fi
      else
        cat "$TMP/audit_build.log" >&2
        err "failed to build audit_axioms executable"
      fi
    fi

    if [ -n "$AUDIT_BIN" ]; then
      if timeout "$LEAN_TIMEOUT" lake env "$AUDIT_BIN" "$TMP/audit_manifest.txt" \
          >"$TMP/audit_axioms.out" 2>&1; then
        cat "$TMP/audit_axioms.out"
        got="$(sed -n 's/^audit_axioms: TOTAL \([0-9][0-9]*\) theorems verified.*/\1/p' \
          "$TMP/audit_axioms.out" | tail -n 1)"
        got="${got:-0}"
      else
        cat "$TMP/audit_axioms.out" >&2
        err "audit_axioms failed (disallowed axiom, unsafe decl, or missing theorem)"
      fi
    fi
  elif [ "$RESOLVED_SCOPE" = "rdeps" ]; then
    echo "   0 headline theorems match rdeps scope; passing cleanly"
  else
    err "no headline theorems selected for scope=$RESOLVED_SCOPE (INCLUDE_LEGACY=$INCLUDE_LEGACY)"
  fi
else
  err "no headline theorem to audit in scripts/headlines.d/ or scripts/headline.txt"
fi
ax_lines="$(grep -c . "$TMP/axioms.txt" || true)"
ax_lines="${ax_lines:-0}"
echo "$ax_lines build-log axiom lines; $got/$want headline theorems verified (0 unsafe, <= std3)"
[ "$got" -eq "$want" ] || err "$got verified headline theorems for $want expected headline theorems"
while IFS= read -r line; do
  [ -n "$line" ] || continue
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
    for mod in LratBytes \
        KissatM7FidelityCert1 KissatM7FidelityCert KissatM7FidelityCertLink KissatM7Fidelity; do
      [ -f "LeanQbe/T/$arch/$mod.lean" ] && echo "LeanQbe/T/$arch/$mod.lean" >>"$TMP/timed.txt"
    done
    if [ "$INCLUDE_LEGACY" = "1" ]; then
      for mod in Kissat KissatCorePlus KissatPlainCert1 KissatPlainCert KissatPlain \
          KissatM3Cert1a KissatM3Cert KissatM3 \
          KissatM4Cert1 KissatM4Cert KissatM4CertLink KissatM4 KissatM4Sound \
          KissatM5Cert1 KissatM5Cert KissatM5CertLink KissatM5 KissatM5Sound \
          KissatM6Cert1 KissatM6Cert KissatM6CertLink KissatM6 \
          KissatM7PlusCert1 KissatM7PlusCert KissatM7PlusCertLink KissatM7Plus; do
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
    leanqbe_throttle_jobs "$times_jobs"
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
