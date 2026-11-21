#!/usr/bin/env bash
set -euo pipefail

# End-to-end verification of P0+P1 DebugAsm & CFI across SysV x64 and AAPCS64 Arm64:
#   1. Bit-identical `.text` vs `Driver.emitAsm` (objcopy -O binary -j .text + sha256sum)
#   2. Zero leaked `{fn}.L{i}` local symbols in `nm` / `readelf -sW`; FUNC + Size > 0
#   3. Clean `.eh_frame` DWARF CFI (`readelf --debug-dump=frames`) for GCC and Clang
#   4. Multi-frame `-O2 -fomit-frame-pointer` + GDB `-batch` (`disas`, `bt`, `info frame`, `list`)
#   5. Arm64 QEMU execution + post-`.size` `.ltorg` large-frame check
#   6. `bench/kissat/build_solver.sh --debug` smoke check on Plain (if Plain.olean is cached)

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

TMP="$(mktemp -d /tmp/leanqbe_debug_cfi.XXXXXX)"
trap 'rm -rf "$TMP"' EXIT

build_lean_path() {
  local wt="$ROOT/.lake/build/lib/lean"
  local parent="/usr/local/google/home/andreser/lean-qbe/.lake/build/lib/lean"
  local kraken="$ROOT/.lake/build/lib/lean"
  if [ -f "$wt/LeanQbe/T/Amd64/Targ.olean" ] && \
     [ -f "$wt/LeanQbe/T/Arm64/Targ.olean" ]; then
    local lp="$wt"
    [ -d "$kraken" ] && lp="$lp:$kraken"
    for p in "$ROOT/.lake/packages/"*/.lake/build/lib/lean; do
      [ -d "$p" ] && lp="$lp:$p"
    done
    echo "$lp"
    return
  fi
  if [ -n "${STAGE_LEAN_PATH:-}" ]; then
    echo "$STAGE_LEAN_PATH"
    return
  fi
  # Thin symlink view combining prebuilt parent modules with worktree DebugAsm.*
  local ov="$TMP/lean_ov"
  mkdir -p "$ov"
  cp -rs "$parent/LeanQbe" "$ov/LeanQbe"
  rm -f "$ov/LeanQbe/T/Amd64"/DebugAsm.* "$ov/LeanQbe/T/Arm64"/DebugAsm.* 2>/dev/null || true
  ln -sf "$wt/LeanQbe/T/Amd64"/DebugAsm.* "$ov/LeanQbe/T/Amd64/"
  ln -sf "$wt/LeanQbe/T/Arm64"/DebugAsm.* "$ov/LeanQbe/T/Arm64/"
  local lp="$ov"
  [ -d "$kraken" ] && lp="$lp:$kraken"
  for p in /usr/local/google/home/andreser/lean-qbe/.lake/packages/*/.lake/build/lib/lean; do
    [ -d "$p" ] && lp="$lp:$p"
  done
  echo "$lp"
}

LP="$(build_lean_path)"
export LEAN_PATH="$LP"

cat > "$TMP/gen_x64.lean" <<'LEAN'
import LeanQbe.T.Amd64.DebugAsm
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Driver
import LeanQbe.T.Examples.LitmusProgs
import LeanQbe.T.Notation
import Kraken.X64.PrintATT

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Litmus LeanQbe.T.Notation

def multiExit : Fn := tqbe $multi_exit(%n:l, %a:l, %b:l, %c:l) -> l {
  %w =w trunc %n
  %z =b cnew %w, 0
  jnz %z, {
    %m =l sub %n, 1
    %wm =w trunc %m
    %nz =b cnew %wm, 0
    jnz %nz, {
      %r =l call $c_probe(%n, %a)
      %s1 =l add %a, %b
      %s2 =l add %s1, %c
      %s3 =l add %s2, %r
      ret %s3
    }, {
      exit $c_fail_exit(%a)
    }
  }, {
    ret 42
  }
}

def deepCaller : Fn := tqbe $deep_caller(%n:l, %x:l, %y:l) -> l {
  %k1 =l add %x, 10
  %k2 =l add %y, 20
  %r1 =l call $c_mid(%n, %k1, %k2, 7:l)
  %k3 =l add %k1, %k2
  %sum =l add %r1, %k3
  ret %sum
}

def loopBranch : Fn := tqbe $loop_branch(%n:l, %acc:l) -> l {
  loop @lp(%i:l = %n, %s:l = %acc) {
    %w =w trunc %i
    %c =b cnew %w, 0
    jnz %c, {
      %r =l call $c_probe(%i, %s)
      %s1 =l add %s, %r
      %i1 =l sub %i, 1
      continue @lp(%i1, %s1)
    }, {
      ret %s
    }
  }
}

def main (args : List String) : IO Unit := do
  let outDir := args[0]!
  let baseFns := [spill10, evenodd, nested, sumcall]
  let meHint : X64Hints :=
    { Fn.computeHints x64Target.toIsa x64LegalTarget multiExit with
      saved := [.rbx, .rbp, .r12, .r13] }
  let dcHint : X64Hints :=
    { Fn.computeHints x64Target.toIsa x64LegalTarget deepCaller with
      saved := [.rbx, .r12, .r14] }
  let fns := baseFns ++ [multiExit, deepCaller, loopBranch]
  let hs := baseFns.map (Fn.computeHints x64Target.toIsa x64LegalTarget) ++
    [meHint, dcHint, Fn.computeHints x64Target.toIsa x64LegalTarget loopBranch]
  let dirs ← IO.ofExcept (compile x64Target.toIsa x64LegalTarget fns hs)
  let raw := Driver.emitAsm (fun c => Kraken.X64.toATT c ++ "\n") fns dirs
  let dbgSome ← IO.ofExcept (emitX64DebugAsmChecked fns dirs (some hs) ["c_fail_exit"] true)
  let dbgNone ← IO.ofExcept (emitX64DebugAsmChecked fns dirs none ["c_fail_exit"] true)
  if dbgSome != dbgNone then
    throw (IO.userError "x64 emitX64DebugAsm some vs none mismatch")
  IO.FS.writeFile s!"{outDir}/x64_raw.s" raw
  IO.FS.writeFile s!"{outDir}/x64_dbg.s" dbgSome
LEAN

cat > "$TMP/gen_arm64.lean" <<'LEAN'
import LeanQbe.T.Arm64.DebugAsm
import LeanQbe.T.Arm64.Targ
import LeanQbe.T.Driver
import LeanQbe.T.Examples.LitmusProgs
import LeanQbe.T.Notation
import Kraken.AArch64.Print

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Litmus LeanQbe.T.Notation

def multiExit : Fn := tqbe $multi_exit(%n:l, %a:l, %b:l, %c:l) -> l {
  %w =w trunc %n
  %z =b cnew %w, 0
  jnz %z, {
    %m =l sub %n, 1
    %wm =w trunc %m
    %nz =b cnew %wm, 0
    jnz %nz, {
      %r =l call $c_probe(%n, %a)
      %s1 =l add %a, %b
      %s2 =l add %s1, %c
      %s3 =l add %s2, %r
      ret %s3
    }, {
      exit $c_fail_exit(%a)
    }
  }, {
    ret 42
  }
}

def deepCaller : Fn := tqbe $deep_caller(%n:l, %x:l, %y:l) -> l {
  %k1 =l add %x, 10
  %k2 =l add %y, 20
  %r1 =l call $c_mid(%n, %k1, %k2, 7:l)
  %k3 =l add %k1, %k2
  %sum =l add %r1, %k3
  ret %sum
}

def loopBranch : Fn := tqbe $loop_branch(%n:l, %acc:l) -> l {
  loop @lp(%i:l = %n, %s:l = %acc) {
    %w =w trunc %i
    %c =b cnew %w, 0
    jnz %c, {
      %r =l call $c_probe(%i, %s)
      %s1 =l add %s, %r
      %i1 =l sub %i, 1
      continue @lp(%i1, %s1)
    }, {
      ret %s
    }
  }
}

def leafSimple : Fn := tqbe $big_pool_fn(%a:l, %b:l) -> l {
  %c =l add %a, %b
  ret %c
}

def main (args : List String) : IO Unit := do
  let outDir := args[0]!
  let baseFns := [spill10, evenodd, nested, sumcall]
  let meHint : Arm64Hints :=
    { Fn.computeHints armTarget.toIsa armLegalTarget multiExit with
      saved := [.reg .X19, .reg .X20, .reg .X21, .reg .X29] }
  let dcHint : Arm64Hints :=
    { Fn.computeHints armTarget.toIsa armLegalTarget deepCaller with
      saved := [.reg .X19, .reg .X22, .reg .X28] }
  let fns := baseFns ++ [multiExit, deepCaller, loopBranch]
  let hs := baseFns.map (Fn.computeHints armTarget.toIsa armLegalTarget) ++
    [meHint, dcHint, Fn.computeHints armTarget.toIsa armLegalTarget loopBranch]
  let dirs ← IO.ofExcept (compile armTarget.toIsa armLegalTarget fns hs)
  let printArm := fun c => ".p2align 2\n" ++
    String.intercalate "\n" (c.map Kraken.AArch64.Print.directive) ++ "\n"
  let raw := Driver.emitAsm printArm fns dirs
  let eoFns := [evenodd]
  let eoHs := [Fn.computeHints armTarget.toIsa armLegalTarget evenodd]
  let eoDirs ← IO.ofExcept (compile armTarget.toIsa armLegalTarget eoFns eoHs)
  let eoRaw := Driver.emitAsm printArm eoFns eoDirs
  let eoDbg ← IO.ofExcept (emitArm64DebugAsmChecked eoFns eoDirs (some eoHs) [] true)
  IO.FS.writeFile s!"{outDir}/arm64_eo_raw.s" eoRaw
  IO.FS.writeFile s!"{outDir}/arm64_eo_dbg.s" eoDbg
  let nlFns := [spill10, sumcall, deepCaller]
  let nlHs := nlFns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let nlDirs ← IO.ofExcept (compile armTarget.toIsa armLegalTarget nlFns nlHs)
  let nlRaw := Driver.emitAsm printArm nlFns nlDirs
  let nlDbg ← IO.ofExcept (emitArm64DebugAsmChecked nlFns nlDirs (some nlHs) [] true)
  IO.FS.writeFile s!"{outDir}/arm64_nl_raw.s" nlRaw
  IO.FS.writeFile s!"{outDir}/arm64_nl_dbg.s" nlDbg
  let dbgSome ← IO.ofExcept (emitArm64DebugAsmChecked fns dirs (some hs) ["c_fail_exit"] true)
  let dbgNone ← IO.ofExcept (emitArm64DebugAsmChecked fns dirs none ["c_fail_exit"] true)
  if dbgSome != dbgNone then
    throw (IO.userError "arm64 emitArm64DebugAsm some vs none mismatch")
  IO.FS.writeFile s!"{outDir}/arm64_raw.s" raw
  IO.FS.writeFile s!"{outDir}/arm64_dbg.s" dbgSome
  let bigHint : Arm64Hints :=
    { Fn.computeHints armTarget.toIsa armLegalTarget leafSimple with
      nslots := 600, saved := [.reg .X19, .reg .X20] }
  let bigDirs ← IO.ofExcept (compile armTarget.toIsa armLegalTarget [leafSimple] [bigHint])
  let bigAsm ← IO.ofExcept
    (emitArm64DebugAsmChecked [leafSimple] bigDirs (some [bigHint]) [] true)
  IO.FS.writeFile s!"{outDir}/arm64_big.s" bigAsm
LEAN

echo "== [1/6] Generating x64 & Arm64 raw vs debug assemblies via Lean"
timeout 120 lean --run "$TMP/gen_x64.lean" "$TMP"
timeout 120 lean --run "$TMP/gen_arm64.lean" "$TMP"

echo "== [2/6] Verifying x64 .text byte-identity, zero local leaks, and clean CFI"
gcc -c "$TMP/x64_raw.s" -o "$TMP/x64_raw_gcc.o"
gcc -g -c "$TMP/x64_dbg.s" -o "$TMP/x64_dbg_gcc.o"
clang -c "$TMP/x64_raw.s" -o "$TMP/x64_raw_clang.o"
clang -g -c "$TMP/x64_dbg.s" -o "$TMP/x64_dbg_clang.o"

objcopy -O binary -j .text "$TMP/x64_raw_gcc.o" "$TMP/x64_raw_gcc.text"
objcopy -O binary -j .text "$TMP/x64_dbg_gcc.o" "$TMP/x64_dbg_gcc.text"
objcopy -O binary -j .text "$TMP/x64_raw_clang.o" "$TMP/x64_raw_clang.text"
objcopy -O binary -j .text "$TMP/x64_dbg_clang.o" "$TMP/x64_dbg_clang.text"

cmp -s "$TMP/x64_raw_gcc.text" "$TMP/x64_dbg_gcc.text" || {
  echo "FAIL: x64 gcc .text mismatch"; exit 1
}
cmp -s "$TMP/x64_raw_clang.text" "$TMP/x64_dbg_clang.text" || {
  echo "FAIL: x64 clang .text mismatch"; exit 1
}
echo "  x64 .text SHA-256: $(sha256sum "$TMP/x64_dbg_gcc.text" | awk '{print $1}')"

for obj in "$TMP/x64_dbg_gcc.o" "$TMP/x64_dbg_clang.o"; do
  if nm "$obj" | grep -E '\.L[0-9]+' ; then
    echo "FAIL: leaked local label symbol in $obj"; exit 1
  fi
  for fn in spill10 evenodd nested sumcall multi_exit deep_caller loop_branch; do
    readelf -sW "$obj" | awk -v fn="$fn" \
      '$8 == fn && $4 == "FUNC" && strtonum($3) > 0 { ok=1 } END { exit !ok }' || {
        echo "FAIL: missing FUNC / non-zero Size for $fn in $obj"; exit 1
      }
  done
  readelf --debug-dump=frames "$obj" > "$TMP/frames.txt" 2>"$TMP/frames.err"
  [ ! -s "$TMP/frames.err" ] || { cat "$TMP/frames.err"; echo "FAIL: frames warn"; exit 1; }
  grep -q 'DW_CFA_remember_state' "$TMP/frames.txt" || {
    echo "FAIL: missing DW_CFA_remember_state in $obj"; exit 1
  }
  grep -q 'DW_CFA_restore_state' "$TMP/frames.txt" || {
    echo "FAIL: missing DW_CFA_restore_state in $obj"; exit 1
  }
done
echo "  x64 gcc+clang: 0 local leaks, all FUNC+Size>0, CFI clean!"

echo "== [3/6] Verifying Arm64 .text byte-identity, zero leaked .L symbols, .ltorg, and clean CFI"
awk '/^[A-Za-z_][A-Za-z0-9_]*:/ { if (seen++) print "\t.ltorg" } { print }
  END { print "\t.ltorg" }' "$TMP/arm64_raw.s" > "$TMP/arm64_raw_ltorg.s"
aarch64-linux-gnu-gcc -c "$TMP/arm64_raw_ltorg.s" -o "$TMP/arm64_raw.o"
aarch64-linux-gnu-gcc -g -c "$TMP/arm64_dbg.s" -o "$TMP/arm64_dbg.o"
aarch64-linux-gnu-gcc -c "$TMP/arm64_eo_raw.s" -o "$TMP/arm64_eo_raw.o"
aarch64-linux-gnu-gcc -g -c "$TMP/arm64_eo_dbg.s" -o "$TMP/arm64_eo_dbg.o"
aarch64-linux-gnu-gcc -c "$TMP/arm64_nl_raw.s" -o "$TMP/arm64_nl_raw.o"
aarch64-linux-gnu-gcc -g -c "$TMP/arm64_nl_dbg.s" -o "$TMP/arm64_nl_dbg.o"
aarch64-linux-gnu-gcc -g -c "$TMP/arm64_big.s" -o "$TMP/arm64_big.o"

aarch64-linux-gnu-objcopy -O binary -j .text "$TMP/arm64_raw.o" "$TMP/arm64_raw.text"
aarch64-linux-gnu-objcopy -O binary -j .text "$TMP/arm64_dbg.o" "$TMP/arm64_dbg.text"
cmp -s "$TMP/arm64_raw.text" "$TMP/arm64_dbg.text" || {
  echo "FAIL: arm64 .text mismatch"; exit 1
}
aarch64-linux-gnu-objcopy -O binary -j .text "$TMP/arm64_eo_raw.o" "$TMP/arm64_eo_raw.text"
aarch64-linux-gnu-objcopy -O binary -j .text "$TMP/arm64_eo_dbg.o" "$TMP/arm64_eo_dbg.text"
cmp -s "$TMP/arm64_eo_raw.text" "$TMP/arm64_eo_dbg.text" || {
  echo "FAIL: arm64 evenodd single-fn .text mismatch"; exit 1
}
aarch64-linux-gnu-objcopy -O binary -j .text "$TMP/arm64_nl_raw.o" "$TMP/arm64_nl_raw.text"
aarch64-linux-gnu-objcopy -O binary -j .text "$TMP/arm64_nl_dbg.o" "$TMP/arm64_nl_dbg.text"
cmp -s "$TMP/arm64_nl_raw.text" "$TMP/arm64_nl_dbg.text" || {
  echo "FAIL: arm64 multi-fn non-literal .text mismatch"; exit 1
}
echo "  arm64 .text SHA-256 (7-fn): $(sha256sum "$TMP/arm64_dbg.text" | awk '{print $1}')"
echo "  arm64 .text SHA-256 (evenodd): $(sha256sum "$TMP/arm64_eo_dbg.text" | awk '{print $1}')"
echo "  arm64 .text SHA-256 (3-fn no-lit): $(sha256sum "$TMP/arm64_nl_dbg.text" | awk '{print $1}')"

if aarch64-linux-gnu-nm "$TMP/arm64_dbg.o" | grep -E '\.L[0-9]+' ; then
  echo "FAIL: leaked local label symbol in arm64_dbg.o"; exit 1
fi
for fn in spill10 evenodd nested sumcall multi_exit deep_caller loop_branch; do
  aarch64-linux-gnu-readelf -sW "$TMP/arm64_dbg.o" | awk -v fn="$fn" \
    '$8 == fn && $4 == "FUNC" && strtonum($3) > 0 { ok=1 } END { exit !ok }' || {
      echo "FAIL: missing FUNC / non-zero Size for $fn in arm64_dbg.o"; exit 1
    }
done
aarch64-linux-gnu-readelf --debug-dump=frames "$TMP/arm64_dbg.o" \
  > "$TMP/arm_frames.txt" 2>"$TMP/arm_frames.err"
[ ! -s "$TMP/arm_frames.err" ] || { cat "$TMP/arm_frames.err"; echo "FAIL: arm64 readelf"; exit 1; }
grep -q 'DW_CFA_remember_state' "$TMP/arm_frames.txt"
grep -q 'DW_CFA_restore_state' "$TMP/arm_frames.txt"
grep -q 'DW_CFA_offset: r30 (x30)' "$TMP/arm_frames.txt"
aarch64-linux-gnu-readelf --debug-dump=frames "$TMP/arm64_big.o" \
  > "$TMP/arm_big_frames.txt" 2>"$TMP/arm_big.err"
[ ! -s "$TMP/arm_big.err" ] || { cat "$TMP/arm_big.err"; exit 1; }
awk '/\.size big_pool_fn/{sz=NR} /\.ltorg/{lt=NR} END{exit !(sz>0 && lt>sz)}' \
  "$TMP/arm64_big.s" || {
    echo "FAIL: .ltorg not strictly after .size in arm64_big.s"; exit 1
  }
echo "  arm64 nm=0 local leaks, all FUNC+Size>0, CFI + post-.size .ltorg clean!"

echo "== [4/6] Executing -O2 -fomit-frame-pointer C+Asm harness on x64 and Arm64 (QEMU)"
cat > "$TMP/harness.c" <<'C'
#include <stdio.h>
#include <stdlib.h>

extern long spill10(long a, long b);
extern long evenodd(long n);
extern long nested(long n, long m, long k);
extern long sumcall(long n, long b);
extern long multi_exit(long n, long a, long b, long c);
extern long deep_caller(long n, long x, long y);
extern long loop_branch(long n, long acc);

__attribute__((noinline))
long c_probe(long a, long b) {
  return a * 3 + b + 5;
}

__attribute__((noinline))
long inc(long a) {
  return a + 1;
}

__attribute__((noinline))
long c_mid(long n, long a, long b, long c) {
  return multi_exit(n, a, b, c) + 100;
}

__attribute__((noinline))
long c_outer(long n, long x, long y) {
  return deep_caller(n, x, y) + loop_branch(4, 1);
}

void c_fail_exit(long x) {
  (void)x;
  exit(77);
}

int main(int argc, char **argv) {
  long n = (argc > 1) ? atol(argv[1]) : 5;
  long r_outer = c_outer(n, 3, 4);
  long r_early = multi_exit(0, 1, 2, 3);
  long r_eo = evenodd(12) + evenodd(13);
  long r_sp = spill10(2, 99);
  if (r_early != 42 || r_eo != 1 || argc == 99) {
    return 1;
  }
  printf("ok r_outer=%ld r_early=%ld r_sp=%ld\n", r_outer, r_early, r_sp);
  return 0;
}
C

gcc -std=c99 -O2 -fomit-frame-pointer -g -no-pie "$TMP/harness.c" "$TMP/x64_dbg.s" \
  -o "$TMP/x64_bin"
"$TMP/x64_bin" 5 | grep -q 'ok r_outer='

aarch64-linux-gnu-gcc -std=c99 -O2 -fomit-frame-pointer -g -static \
  "$TMP/harness.c" "$TMP/arm64_dbg.s" -o "$TMP/arm64_bin"
timeout 30 qemu-aarch64 "$TMP/arm64_bin" 5 | grep -q 'ok r_outer='
echo "  both x64 native and arm64 qemu-aarch64 harnesses passed!"

echo "== [5/6] Real GDB verification on -O2 -fomit-frame-pointer x64 binary"
if nm "$TMP/x64_bin" | grep -qE ' (spill10|evenodd|multi_exit)\.L[0-9]+'; then
  echo "FAIL: linked x64_bin still has local .L symbols"; exit 1
fi
cat > "$TMP/gdb.cmds" <<'GDB'
set pagination off
set confirm off
disassemble multi_exit
disassemble loop_branch
list deep_caller
break c_probe
run 5
backtrace
frame 1
info frame
continue
quit
GDB
timeout 30 gdb -batch -x "$TMP/gdb.cmds" "$TMP/x64_bin" > "$TMP/gdb.out" 2>&1
grep -q 'End of assembler dump.' "$TMP/gdb.out"
grep -q 'in multi_exit' "$TMP/gdb.out"
grep -q 'in c_mid' "$TMP/gdb.out"
grep -q 'in deep_caller' "$TMP/gdb.out"
grep -q 'in c_outer' "$TMP/gdb.out"
grep -q 'in main' "$TMP/gdb.out"
grep -q 'Saved registers:' "$TMP/gdb.out"
grep -q 'x64_dbg.s' "$TMP/gdb.out"
echo "  GDB disas + 6-frame -O2 bt + saved regs + .s line info verified!"

echo "== [6/6] Kissat Plain --debug build_solver.sh smoke check (cached STAGE_LEAN_PATH)"
PLAIN_OL="/usr/local/google/home/andreser/lean-qbe/.lake/build/lib/lean/LeanQbe/T/Examples/Kissat"
if [ -f "$PLAIN_OL/Plain.olean" ]; then
  STAGE_LEAN_PATH="$LP" timeout 300 bash bench/kissat/build_solver.sh \
    --module Plain --arch x64 --debug \
    --save-asm "$TMP/kissat_x64.s" -o "$TMP/kissat_x64"
  grep -q '\.cfi_startproc' "$TMP/kissat_x64.s"
  grep -q '\.size kissat_solve_bytes, \.-kissat_solve_bytes' "$TMP/kissat_x64.s"
  if nm "$TMP/kissat_x64" | grep -qE 'kissat_.*\.L[0-9]+'; then
    echo "FAIL: kissat_x64 leaked local .L symbols"; exit 1
  fi
  timeout 30 readelf --debug-dump=frames "$TMP/kissat_x64" \
    > "$TMP/k_frames.txt" 2>"$TMP/k_frames.err"
  [ ! -s "$TMP/k_frames.err" ] || { cat "$TMP/k_frames.err"; exit 1; }
  timeout 30 gdb -batch -ex 'disas kissat_solve_bytes' \
    -ex 'info line kissat_solve_bytes' -ex 'list kissat_solve_bytes' \
    "$TMP/kissat_x64" > "$TMP/k_gdb.out" 2>&1
  grep -q 'End of assembler dump.' "$TMP/k_gdb.out"
  grep -q 'kissat_x64.s' "$TMP/k_gdb.out"
  echo "  Kissat Plain x64 --debug verified with readelf/nm/gdb!"

  STAGE_LEAN_PATH="$LP" timeout 300 bash bench/kissat/build_solver.sh \
    --module Plain --arch arm64 --debug \
    --save-asm "$TMP/kissat_arm64.s" -o "$TMP/kissat_arm64"
  grep -q '\.ltorg' "$TMP/kissat_arm64.s"
  if aarch64-linux-gnu-nm "$TMP/kissat_arm64" | grep -qE 'kissat_.*\.L[0-9]+'; then
    echo "FAIL: kissat_arm64 leaked local .L symbols"; exit 1
  fi
  timeout 30 aarch64-linux-gnu-readelf --debug-dump=frames "$TMP/kissat_arm64" \
    > "$TMP/ka_frames.txt" 2>"$TMP/ka_frames.err"
  [ ! -s "$TMP/ka_frames.err" ] || { cat "$TMP/ka_frames.err"; exit 1; }
  echo "  Kissat Plain arm64 --debug verified with readelf/nm!"
else
  echo "  SKIP Kissat Plain smoke check (Plain.olean not prebuilt)"
fi

echo "ALL P0+P1 DEBUG ASM + CFI CHECKS PASSED"
