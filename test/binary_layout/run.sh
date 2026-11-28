#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-binlayout.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

RUN_SCOPE=(
  systemd-run --user --scope --slice=leanqbe-builds.slice
  -p MemoryMax=24G -p OOMPolicy=kill
  env LAKE_JOBS=4 LEAN_NUM_THREADS=4
  LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
)

echo "[1/5] Building BinaryLayout and UnionFind Lean prerequisites..."
timeout 240 "${RUN_SCOPE[@]}" lake build --wfail \
  LeanQbe.T.BinaryLayout \
  LeanQbe.T.BinaryLayoutElab \
  LeanQbe.T.Amd64.BinaryLayout \
  LeanQbe.T.Arm64.BinaryLayout \
  LeanQbe.T.Driver \
  LeanQbe.T.Amd64.UnionFind \
  LeanQbe.T.Arm64.UnionFind \
  Kraken.X64.PrintATT \
  Kraken.AArch64.Print

echo "[2/5] Emitting real x86-64 and AArch64 assembly from UnionFind.compiled.code..."
cat > "$TMP_DIR/emit.lean" <<EOF
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.UnionFind
import Kraken.X64.PrintATT

def main : IO Unit := do
  let asm := LeanQbe.T.Driver.emitAsm (I := LeanQbe.T.Amd64.x64Isa)
    Kraken.X64.toATT LeanQbe.T.Examples.UnionFind.ufFns
    LeanQbe.T.Amd64.UnionFind.compiled.code
  IO.FS.writeFile "$TMP_DIR/uf_x64.s" (asm ++ "\n")
EOF
timeout 60 "${RUN_SCOPE[@]}" lake env lean --run "$TMP_DIR/emit.lean"

cat > "$TMP_DIR/emit_arm64.lean" <<EOF
import LeanQbe.T.Driver
import LeanQbe.T.Arm64.UnionFind
import Kraken.AArch64.Print

def main : IO Unit := do
  let asm := LeanQbe.T.Driver.emitAsm (I := LeanQbe.T.Arm64.armIsa)
    Kraken.AArch64.print LeanQbe.T.Examples.UnionFind.ufFns
    LeanQbe.T.Arm64.UnionFind.compiled.code
  IO.FS.writeFile "$TMP_DIR/uf_arm64.s" (asm ++ "\n")
EOF
timeout 60 "${RUN_SCOPE[@]}" lake env lean --run "$TMP_DIR/emit_arm64.lean"

echo "[3/5] Assembling .o and linking C-FFI + LeanQbe .so binaries..."
cat > "$TMP_DIR/shim_before.c" <<'EOF'
#include <stdint.h>
extern uint64_t find(uint64_t *p, uint64_t x);
extern void uf_union(uint64_t *p, uint64_t x, uint64_t y) __asm__("union");
uint64_t ffi_shim_before(uint64_t *p, uint64_t x, uint64_t y) {
  uf_union(p, x, y);
  return find(p, x);
}
EOF
cat > "$TMP_DIR/shim_after.c" <<'EOF'
#include <stdint.h>
uint64_t ffi_shim_after(uint64_t a, uint64_t b) { return a + b + 17; }
EOF

cc -c -o "$TMP_DIR/uf_x64.o" "$TMP_DIR/uf_x64.s"
cc -shared -fPIC -o "$TMP_DIR/libuf_x64.so" \
  "$TMP_DIR/shim_before.c" "$TMP_DIR/uf_x64.s" "$TMP_DIR/shim_after.c"

cat > "$TMP_DIR/driver.c" <<'EOF'
#include <stdint.h>
#include <stdio.h>
extern uint64_t ffi_shim_before(uint64_t *p, uint64_t x, uint64_t y);
int main(void) {
  uint64_t arr[4] = {0, 1, 2, 3};
  uint64_t r = ffi_shim_before(arr, 1, 2);
  if (r != ffi_shim_before(arr, 2, 2)) return 1;
  printf("runtime x64 .so check ok: rep=%llu\n", (unsigned long long)r);
  return 0;
}
EOF
cc -o "$TMP_DIR/run_so" "$TMP_DIR/driver.c" "$TMP_DIR/libuf_x64.so" -Wl,-rpath,"$TMP_DIR"
timeout 15 "$TMP_DIR/run_so"

echo "[4/5] Verifying x86-64 binary_layout_x64! on real .o and .so + UnionFind proofs..."
cat > "$TMP_DIR/verify_x64.lean" <<EOF
import LeanQbe.T.BinaryLayout
import LeanQbe.T.BinaryLayoutElab
import LeanQbe.T.Amd64.BinaryLayout
import LeanQbe.T.Amd64.UnionFind

set_option autoImplicit false

private abbrev ufProg : _root_.Program :=
  LeanQbe.T.Amd64.UnionFind.compiled.code

binary_layout_x64! ufObj "$TMP_DIR/uf_x64.o" for ufProg
binary_layout_x64! ufSo "$TMP_DIR/libuf_x64.so" for ufProg
binary_layout_x64! ufRawFind "$TMP_DIR/libuf_x64.so" (symbols := ["find"])

theorem uf_so_vma_nonzero : ufSoStart ≠ 0 := by decide

theorem uf_so_matches_obj_sizes : ufSoSizes = ufObjSizes := by decide

theorem uf_so_variable_sizes :
    ∃ i j : Fin ufSoSizes.size, ufSoSizes[i] ≠ ufSoSizes[j] :=
  ⟨⟨1, by decide⟩, ⟨3, by decide⟩, by decide⟩

theorem uf_raw_find_nonempty : ufRawFindSizes.size > 0 := by decide

section
attribute [local instance] ufSoLayout ufSoHost

theorem uf_so_find_correct
    (p x : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64) (hx : x.toNat < n)
    (s : _root_.MachineData) (ra : Int64) (R : _root_.Mem 64 → Prop)
    (hrdi : s.regs.get64 Reg64.rdi = p)
    (hrsi : s.regs.get64 Reg64.rsi = x)
    (hal : BitVec.toNat (s.regs.get64 Reg64.rsp + 8#64) % 16 = 0)
    (hmem : (LeanQbe.T.Examples.UnionFind.uf p n rep ⋆
      (LeanQbe.T.region
          (s.regs.get64 Reg64.rsp - BitVec.ofNat 64 (LeanQbe.T.Amd64.UnionFind.compiled.bound "find"))
          (LeanQbe.T.Amd64.UnionFind.compiled.bound "find") ⋆
        LeanQbe.T.cell64 (s.regs.get64 Reg64.rsp) ra.toBitVec) ⋆ R) s.dmem) :
    Eventually (_root_.step1 _root_.Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 Reg64.rax = rep x ∧
        (∀ r : Reg64, r ∈ [Reg64.rbx, Reg64.rbp, Reg64.r12, Reg64.r13, Reg64.r14, Reg64.r15] →
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 Reg64.rsp = s.regs.get64 Reg64.rsp + 8#64 ∧
        (LeanQbe.T.Examples.UnionFind.uf p n rep ⋆
          LeanQbe.T.region
            (s.regs.get64 Reg64.rsp - BitVec.ofNat 64 (LeanQbe.T.Amd64.UnionFind.compiled.bound "find"))
            (LeanQbe.T.Amd64.UnionFind.compiled.bound "find" + 8) ⋆ R) st.data.dmem)
      { data := s, pc := label "find" } :=
  LeanQbe.T.Amd64.UnionFind.find_x64_correct 0
    (by simp [List.IsInfixAt, ufSoHost_prog])
    ufSoHost_labelsUnique p x n rep hx s ra R hrdi hrsi hal hmem

theorem uf_so_union_correct
    (p x y : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64)
    (hx : x.toNat < n) (hy : y.toNat < n)
    (s : _root_.MachineData) (ra : Int64) (R : _root_.Mem 64 → Prop)
    (hrdi : s.regs.get64 Reg64.rdi = p)
    (hrsi : s.regs.get64 Reg64.rsi = x)
    (hrdx : s.regs.get64 Reg64.rdx = y)
    (hal : BitVec.toNat (s.regs.get64 Reg64.rsp + 8#64) % 16 = 0)
    (hmem : (LeanQbe.T.Examples.UnionFind.uf p n rep ⋆
      (LeanQbe.T.region
          (s.regs.get64 Reg64.rsp - BitVec.ofNat 64 (LeanQbe.T.Amd64.UnionFind.compiled.bound "union"))
          (LeanQbe.T.Amd64.UnionFind.compiled.bound "union") ⋆
        LeanQbe.T.cell64 (s.regs.get64 Reg64.rsp) ra.toBitVec) ⋆ R) s.dmem) :
    Eventually (_root_.step1 _root_.Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r : Reg64, r ∈ [Reg64.rbx, Reg64.rbp, Reg64.r12, Reg64.r13, Reg64.r14, Reg64.r15] →
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 Reg64.rsp = s.regs.get64 Reg64.rsp + 8#64 ∧
        (LeanQbe.T.Examples.UnionFind.uf p n (LeanQbe.T.Examples.UnionFind.merge rep x y) ⋆
          LeanQbe.T.region
            (s.regs.get64 Reg64.rsp - BitVec.ofNat 64 (LeanQbe.T.Amd64.UnionFind.compiled.bound "union"))
            (LeanQbe.T.Amd64.UnionFind.compiled.bound "union" + 8) ⋆ R) st.data.dmem)
      { data := s, pc := label "union" } :=
  LeanQbe.T.Amd64.UnionFind.union_x64_correct 0
    (by simp [List.IsInfixAt, ufSoHost_prog])
    ufSoHost_labelsUnique p x y n rep hx hy s ra R hrdi hrsi hrdx hal hmem

end

/-- info: 'uf_so_find_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uf_so_find_correct

/-- info: 'uf_so_union_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uf_so_union_correct

#eval IO.println s!"x64 .so start={ufSoStart}, directives={ufSoSizes.size}, distinctInstrSizes={((ufSoSizes.toList.zip (ufProg.map LeanQbe.T.dirTag)).filterMap fun (sz, tag) => match tag with | .instr => some sz | _ => none).eraseDups}"
EOF
timeout 120 "${RUN_SCOPE[@]}" lake env lean "$TMP_DIR/verify_x64.lean"

if command -v aarch64-linux-gnu-gcc >/dev/null 2>&1; then
  echo "[5/5] Verifying AArch64 binary_layout_arm64! on real .so + UnionFind proofs..."
  aarch64-linux-gnu-gcc -shared -fPIC -o "$TMP_DIR/libuf_arm64.so" \
    "$TMP_DIR/shim_before.c" "$TMP_DIR/uf_arm64.s" "$TMP_DIR/shim_after.c" 2>&1 | \
    { grep -v -e 'SFrame' || true; }
  cat > "$TMP_DIR/verify_arm64.lean" <<EOF
import LeanQbe.T.BinaryLayout
import LeanQbe.T.BinaryLayoutElab
import LeanQbe.T.Arm64.BinaryLayout
import LeanQbe.T.Arm64.UnionFind

set_option autoImplicit false

private abbrev ufArmProg : _root_.Program :=
  LeanQbe.T.Arm64.UnionFind.compiled.code

binary_layout_arm64! ufArmSo "$TMP_DIR/libuf_arm64.so" for ufArmProg

theorem uf_arm_so_vma_nonzero : ufArmSoStart ≠ 0 := by decide

section
attribute [local instance] ufArmSoLayout ufArmSoHost

theorem uf_arm_so_find_correct
    (p x : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64) (hx : x.toNat < n)
    (s : _root_.MachineData) (ra : Int64) (R : _root_.Mem 64 → Prop)
    (hx0 : (s.regs.getXReg XReg.X0).toBitVec = p)
    (hx1 : (s.regs.getXReg XReg.X1).toBitVec = x)
    (hx30 : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : (LeanQbe.T.Examples.UnionFind.uf p n rep ⋆
      LeanQbe.T.region
        (s.regs.SP.toBitVec - BitVec.ofNat 64 (LeanQbe.T.Arm64.UnionFind.compiled.bound "find"))
        (LeanQbe.T.Arm64.UnionFind.compiled.bound "find") ⋆ R) s.dmem) :
    Eventually (_root_.step1 _root_.Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg XReg.X0).toBitVec = rep x ∧
        (∀ r : XReg, r ∈ [XReg.X19, XReg.X20, XReg.X21, XReg.X22, XReg.X23, XReg.X24,
          XReg.X25, XReg.X26, XReg.X27, XReg.X28, XReg.X29] →
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (LeanQbe.T.Examples.UnionFind.uf p n rep ⋆
          LeanQbe.T.region
            (s.regs.SP.toBitVec - BitVec.ofNat 64 (LeanQbe.T.Arm64.UnionFind.compiled.bound "find"))
            (LeanQbe.T.Arm64.UnionFind.compiled.bound "find") ⋆ R) st.data.dmem)
      { data := s, pc := label "find" } :=
  LeanQbe.T.Arm64.UnionFind.find_arm64_correct 0
    (by simp [List.IsInfixAt, ufArmSoHost_prog])
    ufArmSoHost_labelsUnique p x n rep hx s ra R hx0 hx1 hx30 hsp hmem

theorem uf_arm_so_union_correct
    (p x y : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64)
    (hx : x.toNat < n) (hy : y.toNat < n)
    (s : _root_.MachineData) (ra : Int64) (R : _root_.Mem 64 → Prop)
    (hx0 : (s.regs.getXReg XReg.X0).toBitVec = p)
    (hx1 : (s.regs.getXReg XReg.X1).toBitVec = x)
    (hx2 : (s.regs.getXReg XReg.X2).toBitVec = y)
    (hx30 : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : (LeanQbe.T.Examples.UnionFind.uf p n rep ⋆
      LeanQbe.T.region
        (s.regs.SP.toBitVec - BitVec.ofNat 64 (LeanQbe.T.Arm64.UnionFind.compiled.bound "union"))
        (LeanQbe.T.Arm64.UnionFind.compiled.bound "union") ⋆ R) s.dmem) :
    Eventually (_root_.step1 _root_.Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r : XReg, r ∈ [XReg.X19, XReg.X20, XReg.X21, XReg.X22, XReg.X23, XReg.X24,
          XReg.X25, XReg.X26, XReg.X27, XReg.X28, XReg.X29] →
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (LeanQbe.T.Examples.UnionFind.uf p n (LeanQbe.T.Examples.UnionFind.merge rep x y) ⋆
          LeanQbe.T.region
            (s.regs.SP.toBitVec - BitVec.ofNat 64 (LeanQbe.T.Arm64.UnionFind.compiled.bound "union"))
            (LeanQbe.T.Arm64.UnionFind.compiled.bound "union") ⋆ R) st.data.dmem)
      { data := s, pc := label "union" } :=
  LeanQbe.T.Arm64.UnionFind.union_arm64_correct 0
    (by simp [List.IsInfixAt, ufArmSoHost_prog])
    ufArmSoHost_labelsUnique p x y n rep hx hy s ra R hx0 hx1 hx2 hx30 hsp hmem

end

/-- info: 'uf_arm_so_find_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uf_arm_so_find_correct

/-- info: 'uf_arm_so_union_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uf_arm_so_union_correct

#eval IO.println s!"arm64 .so start={ufArmSoStart}, directives={ufArmSoSizes.size}"
EOF
  timeout 120 "${RUN_SCOPE[@]}" lake env lean "$TMP_DIR/verify_arm64.lean"
else
  echo "[5/5] Skipping AArch64 cross-link check (aarch64-linux-gnu-gcc not present)."
fi

echo "PASS: test/binary_layout/run.sh"
