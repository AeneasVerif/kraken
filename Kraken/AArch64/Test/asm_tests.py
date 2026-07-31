#!/usr/bin/env python3
import argparse
import json
import os
import re
import random
import shutil
import struct
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

BIN_DIR = Path(__file__).resolve().parent.parent.parent.parent / ".lake/build/bin"
KRAKEN_RUNNER_AARCH64 = BIN_DIR / "krakenrunner_aarch64"

REGS = [f"x{i}" for i in range(31)] + ["sp"]
FLAG_MAP = {"n": 31, "z": 30, "c": 29, "v": 28}
TIMEOUT_SECONDS = 50

class Color:
    GREEN = "\033[92m"
    RED = "\033[91m"
    CYAN = "\033[96m"
    BOLD = "\033[1m"
    RESET = "\033[0m"

def generate_random_regs(rng: random.Random) -> Dict[str, int]:
    init_regs = {}
    for r in REGS:
        if r == "sp":
            init_regs[r] = 0
        else:
            init_regs[r] = rng.randint(0, (1 << 64) - 1)
    return init_regs

def get_boilerplate(instruction_text: str) -> str:
    return f"""
.data
.align 8
_init_state: .space 248
_final_state: .space 264

.text
.globl _start
_start:
    # Read 248 bytes (31 x 8 bytes) of initial register values from stdin
    mov x0, #0          // stdin (fd 0)
    adrp x1, _init_state
    add x1, x1, :lo12:_init_state
    mov x2, #248        // length 31 * 8
    mov x8, #63         // __NR_read on arm64
    svc #0

    # Load initial register values into x1..x30, then x0
    adrp x0, _init_state
    add x0, x0, :lo12:_init_state
    ldr x1, [x0, #8]
    ldr x2, [x0, #16]
    ldr x3, [x0, #24]
    ldr x4, [x0, #32]
    ldr x5, [x0, #40]
    ldr x6, [x0, #48]
    ldr x7, [x0, #56]
    ldr x8, [x0, #64]
    ldr x9, [x0, #72]
    ldr x10, [x0, #80]
    ldr x11, [x0, #88]
    ldr x12, [x0, #96]
    ldr x13, [x0, #104]
    ldr x14, [x0, #112]
    ldr x15, [x0, #120]
    ldr x16, [x0, #128]
    ldr x17, [x0, #136]
    ldr x18, [x0, #144]
    ldr x19, [x0, #152]
    ldr x20, [x0, #160]
    ldr x21, [x0, #168]
    ldr x22, [x0, #176]
    ldr x23, [x0, #184]
    ldr x24, [x0, #192]
    ldr x25, [x0, #200]
    ldr x26, [x0, #208]
    ldr x27, [x0, #216]
    ldr x28, [x0, #224]
    ldr x29, [x0, #232]
    ldr x30, [x0, #240]
    ldr x0, [x0, #0]

# --- Test Code Start ---
{instruction_text}
# --- Test Code End ---
    # 1. Back up test's x0 into tpidr_el0 (EL0 read/write register)
    msr tpidr_el0, x0

    # 2. Get address of _final_state into x0
    adrp x0, _final_state
    add x0, x0, :lo12:_final_state

    # 3. Store x1 at _final_state[8] so x1 can be used as a scratch register
    str x1, [x0, #8]

    # 4. Read test's condition flags (NZCV) into x1 and store at _final_state[256]
    mrs x1, nzcv
    str x1, [x0, #256]

    # 5. Store registers x2 through x30
    str x2, [x0, #16]
    str x3, [x0, #24]
    str x4, [x0, #32]
    str x5, [x0, #40]
    str x6, [x0, #48]
    str x7, [x0, #56]
    str x8, [x0, #64]
    str x9, [x0, #72]
    str x10, [x0, #80]
    str x11, [x0, #88]
    str x12, [x0, #96]
    str x13, [x0, #104]
    str x14, [x0, #112]
    str x15, [x0, #120]
    str x16, [x0, #128]
    str x17, [x0, #136]
    str x18, [x0, #144]
    str x19, [x0, #152]
    str x20, [x0, #160]
    str x21, [x0, #168]
    str x22, [x0, #176]
    str x23, [x0, #184]
    str x24, [x0, #192]
    str x25, [x0, #200]
    str x26, [x0, #208]
    str x27, [x0, #216]
    str x28, [x0, #224]
    str x29, [x0, #232]
    str x30, [x0, #240]

    # 6. Save SP at _final_state[248]
    mov x1, sp
    str x1, [x0, #248]

    # 7. Restore test's original x0 from tpidr_el0 and save to _final_state[0]
    mrs x1, tpidr_el0
    str x1, [x0, #0]

    # 8. Linux sys_write(1, _final_state, 264)
    mov x0, #1          // stdout
    adrp x1, _final_state
    add x1, x1, :lo12:_final_state
    mov x2, #264        // size
    mov x8, #64         // __NR_write
    svc #0

    # 9. Linux sys_exit(0)
    mov x0, #0
    mov x8, #93         // __NR_exit
    svc #0
"""

@dataclass
class ExecutionState:
    regs: Dict[str, int]
    flags: Dict[str, bool]

def parse_raw_state(raw_bytes: bytes) -> ExecutionState:
    fmt = f"<{len(REGS)}Q Q"
    unpacked = struct.unpack(fmt, raw_bytes)
    reg_values = unpacked[:-1]
    nzcv = unpacked[-1]

    return ExecutionState(
        regs=dict(zip(REGS, reg_values)),
        flags={name: bool(nzcv & (1 << bit)) for name, bit in FLAG_MAP.items()}
    )

def find_tool(names: List[str]) -> Optional[str]:
    for name in names:
        path = shutil.which(name)
        if path:
            return path
    return None

def find_elan_lld() -> Optional[str]:
    elan_dir = Path.home() / ".elan"
    if elan_dir.exists():
        for lld_path in elan_dir.rglob("ld.lld"):
            if lld_path.is_file() and os.access(lld_path, os.X_OK):
                return str(lld_path)
    return None

def get_assembler() -> Optional[List[str]]:
    as_bin = find_tool(["aarch64-linux-gnu-as", "aarch64-none-elf-as"])
    if as_bin:
        return [as_bin]
    clang_bin = find_tool(["clang", "clang-19", "clang-18", "clang-17", "clang-16"])
    if clang_bin:
        return [clang_bin, "--target=aarch64-linux-gnu", "-c"]
    return None

def get_linker() -> Optional[List[str]]:
    ld_bin = find_tool(["aarch64-linux-gnu-ld", "aarch64-none-elf-ld", "ld.lld", "lld"])
    if ld_bin:
        return [ld_bin]
    elan_lld = find_elan_lld()
    if elan_lld:
        return [elan_lld]
    return None

def compile_test_binary(asm_path: Path, tmp_dir: Path) -> Tuple[Optional[Path], Optional[str]]:
    as_cmd = get_assembler()
    ld_cmd = get_linker()

    if not as_cmd or not ld_cmd:
        return None, "Missing assembler or linker tools."

    s_file = tmp_dir / asm_path.name
    obj_file = tmp_dir / f"{asm_path.stem}.o"
    bin_file = tmp_dir / f"{asm_path.stem}.bin"

    full_source = get_boilerplate(asm_path.read_text())
    s_file.write_text(full_source)

    try:
        subprocess.run(as_cmd + ["-o", str(obj_file), str(s_file)], check=True, capture_output=True)
        subprocess.run(ld_cmd + ["-o", str(bin_file), str(obj_file)], check=True, capture_output=True)
        return bin_file, None
    except subprocess.CalledProcessError as e:
        err = (e.stderr or b"").decode(errors="replace").replace(str(tmp_dir), "...").strip()
        prologue_len = full_source.split("# --- Test Code Start ---")[0].count("\n") + 1
        line_nr_adjusted_err = re.sub(r":(\d+):", lambda m: f":{int(m.group(1)) - prologue_len}:", err)
        return None, f"Compilation Error ({e.cmd[0]}):\n{line_nr_adjusted_err}"

def run_real_aarch64_qemu(bin_file: Path, qemu_bin: str, init_regs: Dict[str, int]) -> Tuple[Optional[ExecutionState], Optional[str]]:
    raw_input = struct.pack("<31Q", *[init_regs[f"x{i}"] for i in range(31)])
    try:
        res = subprocess.run([qemu_bin, str(bin_file)], input=raw_input, check=True, capture_output=True, timeout=TIMEOUT_SECONDS)
        return parse_raw_state(res.stdout), None
    except subprocess.CalledProcessError as e:
        err = (e.stderr or b"").decode(errors="replace").strip()
        return None, f"QEMU AArch64 Error ({e.cmd[0]}):\n{err}"

def run_kraken_aarch64(path: Path, init_regs: Dict[str, int], tmp_dir: Path) -> Tuple[Optional[ExecutionState], Optional[str]]:
    tmp_json = tmp_dir / f"init_{random.randint(0, 1000000)}.json"
    tmp_json.write_text(json.dumps(init_regs))

    try:
        res = subprocess.run([KRAKEN_RUNNER_AARCH64, path, str(tmp_json)], capture_output=True, check=True, timeout=TIMEOUT_SECONDS)
        data = json.loads(res.stdout)
        return ExecutionState(regs=data["regs"], flags=data["flags"]), None
    except subprocess.CalledProcessError as e:
        return None, f"Kraken Error:\n{(e.stderr or b'').decode(errors='replace').strip()}"
    except subprocess.TimeoutExpired as e:
        return None, f"Kraken Error: {e}\nStderr:\n{(e.stderr or b'').decode(errors='replace').strip()}"
    except Exception as e:
        return None, f"Kraken Error: {e}"
    finally:
        if tmp_json.exists():
            tmp_json.unlink()

def get_undefined_flags(path: Path) -> List[str]:
    first_line = path.read_text().splitlines()[0] if path.read_text().splitlines() else ""
    if first_line.startswith("# Undefined flags:"):
        raw_flags = first_line.split(":", 1)[1]
        return [f.strip() for f in raw_flags.split(",") if f.strip()]
    return []

def compare_states(real: ExecutionState, kraken: ExecutionState, undefined_flags: List[str]) -> List[str]:
    diffs = []
    for r in [r for r in REGS if r != "sp"]:
        rv, kv = real.regs[r], kraken.regs[r]
        if rv != kv:
            diffs.append(f"{r}: QEMU={rv:#x} ({rv}), kraken={kv:#x} ({kv})")

    for f in [f for f in FLAG_MAP if f not in undefined_flags]:
        if real.flags[f] != kraken.flags[f]:
            diffs.append(f"flag {f}: QEMU={real.flags[f]} | kraken={kraken.flags[f]}")
    return diffs

def test_file_fuzz(path: Path, iterations: int, base_seed: int) -> Tuple[bool, str]:
    qemu_bin = find_tool(["qemu-aarch64", "qemu-aarch64-static"])
    if not qemu_bin:
        return False, "qemu-aarch64 not found."

    with tempfile.TemporaryDirectory() as tmp_dir_str:
        tmp_dir = Path(tmp_dir_str)
        bin_file, compile_err = compile_test_binary(path, tmp_dir)
        if compile_err:
            print(f"{path.name:50} [{Color.RED}COMPILE ERROR{Color.RESET}]")
            return False, compile_err

        undefined_flags = get_undefined_flags(path)
        rng = random.Random(base_seed)

        start_time = time.time()
        for iter_idx in range(1, iterations + 1):
            init_regs = generate_random_regs(rng)

            real, real_err = run_real_aarch64_qemu(bin_file, qemu_bin, init_regs)
            kraken, kraken_err = run_kraken_aarch64(path, init_regs, tmp_dir)

            if real_err or kraken_err:
                if iterations == 1:
                    print(f"{path.name:50} [{Color.RED}FAIL{Color.RESET}]")
                else:
                    print(f"\r{path.name:50} [{Color.RED}FAIL at iter {iter_idx}/{iterations}{Color.RESET}]")
                return False, f"Iteration {iter_idx} error:\n" + (real_err or kraken_err)

            diffs = compare_states(real, kraken, undefined_flags)
            if diffs:
                if iterations == 1:
                    print(f"{path.name:50} [{Color.RED}FAIL{Color.RESET}]")
                else:
                    print(f"\r{path.name:50} [{Color.RED}MISMATCH at iter {iter_idx}/{iterations}{Color.RESET}]")
                report = [f"Fuzz failure at iteration {iter_idx}/{iterations}:"]
                report.append("Initial registers:")
                for r in REGS:
                    if r != "sp" and init_regs[r] != 0:
                        report.append(f"  {r}: {init_regs[r]:#x} ({init_regs[r]})")
                report.append("\nDifferences:")
                report.extend(f"  {d}" for d in diffs)
                return False, "\n".join(report)

            if iterations > 1:
                if iter_idx % 10 == 0 or iter_idx == iterations:
                    elapsed = time.time() - start_time
                    rate = iter_idx / elapsed if elapsed > 0 else 0
                    sys.stdout.write(f"\r{path.name:50} [{Color.GREEN}FUZZING {iter_idx}/{iterations}{Color.RESET} ({rate:.1f} iters/s)]")
                    sys.stdout.flush()

        if iterations == 1:
            print(f"{path.name:50} [{Color.GREEN}PASS{Color.RESET}]")
        else:
            print()
        return True, ""

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Kraken AArch64 Test & Fuzz Runner (QEMU vs Lean Semantics)")
    parser.add_argument("target", type=str, help="Target assembly file (.S) or directory containing test files")
    parser.add_argument("--fuzz", type=int, default=1, help="Number of fuzz iterations with random initial registers (default: 1)")
    parser.add_argument("--seed", type=int, default=42, help="Base random seed for fuzzing (default: 42)")

    args = parser.parse_args()

    if not KRAKEN_RUNNER_AARCH64.exists():
        print(f"{Color.RED}Error: Kraken AArch64 runner not found at {KRAKEN_RUNNER_AARCH64}{Color.RESET}")
        print(f"\nTo build it, run the following from the project root:")
        print(f"  {Color.GREEN}lake build krakenrunner_aarch64{Color.RESET}\n")
        sys.exit(1)

    target_path = Path(args.target).resolve()
    files = sorted(target_path.rglob("*.S")) if target_path.is_dir() else ([target_path] if target_path.exists() else [])

    if not files:
        print(f"Error: No .S files found at {target_path}")
        sys.exit(1)

    if args.fuzz > 1:
        print(f"{Color.BOLD}Running AArch64 Tests (Fuzz iterations: {args.fuzz}, Seed: {args.seed}){Color.RESET}\n")

    errors = []
    for idx, f in enumerate(files):
        file_seed = args.seed + idx * 1000
        success, report = test_file_fuzz(f, args.fuzz, file_seed)
        if not success:
            errors.append((f.name, report))

    print(f"\n{Color.BOLD}{'='*60}{Color.RESET}")
    print(f"Result: {len(files) - len(errors)}/{len(files)} passed")
    print(f"{Color.BOLD}{'='*60}{Color.RESET}")

    if errors:
        print(f"\n{Color.RED}Failures:{Color.RESET}")
        for name, report in errors:
            indented = "\n".join(f"    {l}" for l in report.splitlines())
            print(f"\n  {Color.BOLD}{name}{Color.RESET}:\n{indented}")
        sys.exit(1)
    sys.exit(0)
