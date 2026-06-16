#!/usr/bin/env python3
import json
import os
import re
import struct
import subprocess
import sys
import tempfile
import shutil
import platform
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent.parent.parent
KRAKEN_RUNNER = SCRIPT_DIR / ".lake/build/bin/krakenrunner"
LOCAL_SDE_RUNNER = SCRIPT_DIR / "tool" / "sde" / "sde64"
SDE_RUNNER = LOCAL_SDE_RUNNER if LOCAL_SDE_RUNNER.exists() else shutil.which("sde64")
NATIVE_X64 = platform.machine().lower() in ["x86_64", "amd64"]

REGS = ["rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rsp", "rbp",
        "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]
# Maps each flag to its bit in the EFLAGS register.
FLAG_MAP = {"cf": 0, "pf": 2, "af": 4, "zf": 6, "sf": 7, "of": 11}
TIMEOUT_SECONDS = 50

class Color:
    GREEN = "\033[92m"
    RED = "\033[91m"
    BOLD = "\033[1m"
    RESET = "\033[0m"

def get_boilerplate_native(instruction_text: str) -> str:
    reg_count = len(REGS)
    # We move all base registers + the eflags register into memory, so as to dump it later to stdout.
    total_bytes = (reg_count + 1) * 8
    moves = "\n    ".join([f"movq %{reg}, _final_state + {i*8}(%rip)" for i, reg in enumerate(REGS)])
    return f"""
.data
.align 8
_final_state: .space {total_bytes}

.text
.globl _start
_start:
# --- Test Code Start ---
{instruction_text}
# --- Test Code End ---
{moves}
    pushfq
    popq %rax
    movq %rax, _final_state + {reg_count * 8}(%rip)

    # print syscall: arguments are 1 (syscall number), 1 (stdout), address of _final_state, and length of _final_state
    # See e.g. https://x64.syscall.sh/ for syscall table.
    movq $1, %rax
    movq $1, %rdi
    leaq _final_state(%rip), %rsi
    movq ${total_bytes}, %rdx
    syscall

    movq $60, %rax
    xorq %rdi, %rdi
    syscall
"""

def get_boilerplate_sde(instruction_text: str) -> str:
    return f"""
.text
.globl _start
_start:
# --- Test Code Start ---
{instruction_text}
# --- Test Code End ---
    int3
"""

@dataclass
class ExecutionState:
    regs: Dict[str, int]
    flags: Dict[str, bool]

def parse_raw_state(raw_bytes: bytes) -> ExecutionState:
    fmt = f"<{len(REGS)}Q Q"
    unpacked = struct.unpack(fmt, raw_bytes)
    reg_values = unpacked[:-1]
    rflags = unpacked[-1]
    return ExecutionState(
        regs=dict(zip(REGS, reg_values)),
        flags={name: bool(rflags & (1 << bit)) for name, bit in FLAG_MAP.items()}
    )

def parse_sde_debugtrace(trace_path: Path) -> Tuple[Optional[ExecutionState], Optional[str]]:
    regs = {r: 0 for r in REGS}
    rflags_val = 0x202
    EOF_MARKER_LINE = '# $eof'
    with open(trace_path) as f:
        for line in f:
            if line == EOF_MARKER_LINE+'\n':
                break
            if "|" not in line:
                continue
            state_part = line.split("|", 2)[1]
            for p in state_part.split(","):
                name, val = p.lower().strip().split("=", 2)
                name = name.strip()
                val = int(val.strip(), 16)
                if name == "rflags":
                    rflags_val = val
                elif name in regs:
                    regs[name] = val
        else:
            return None, f'SDE debugtrace did not contain the line "{EOF_MARKER_LINE}"'
        if f.read(1) != '':
            return None, f'SDE debugtrace end after the line "{EOF_MARKER_LINE}"'

    return ExecutionState(
        regs=regs,
        flags={name: bool(rflags_val & (1 << bit)) for name, bit in FLAG_MAP.items()}
    ), None


class AssembleAndLinkError(Exception):
    pass

def assemble_and_link(asm_path: Path, full_source: str, tmp: Path) -> Path:
    s_file = tmp / asm_path.name
    obj_file = tmp / f"{asm_path.stem}.o"
    bin_file = tmp / f"{asm_path.stem}.bin"

    try:
        s_file.write_text(full_source)
        subprocess.run(["as", "-o", str(obj_file), str(s_file)], check=True, capture_output=True, timeout=TIMEOUT_SECONDS)
        subprocess.run(["ld", "-o", str(bin_file), str(obj_file)], check=True, capture_output=True, timeout=TIMEOUT_SECONDS)
        return bin_file
    except subprocess.SubprocessError as e:
        cmd_name = Path(e.cmd[0]).name if hasattr(e, "cmd") else "toolchain"
        err_bytes = getattr(e, "stderr", None)
        err = err_bytes.decode(errors="replace").replace(str(tmp), "...").strip() if err_bytes else str(e)
        prologue_len = full_source.split("# --- Test Code Start ---")[0].count("\n") + 1
        line_nr_adjusted_err = re.sub(r":(\d+):", lambda m: f":{int(m.group(1)) - prologue_len}:", err)
        raise AssembleAndLinkError(f"x86 Error ({cmd_name}):\n{line_nr_adjusted_err}")

def run_native(asm_path: Path) -> Tuple[Optional[ExecutionState], Optional[str]]:
    with tempfile.TemporaryDirectory() as tmp_dir:
        tmp = Path(tmp_dir)
        full_source = get_boilerplate_native(asm_path.read_text())

        bin_file = assemble_and_link(asm_path, full_source, tmp)
        try:
            res = subprocess.run([str(bin_file)], check=True, capture_output=True, timeout=TIMEOUT_SECONDS)
            return parse_raw_state(res.stdout), None
        except subprocess.SubprocessError as e:
            return None, f"x86 Error: {e}\nStderr:\n{(e.stderr or b'').decode(errors='replace').strip()}"

def run_sde(asm_path: Path) -> Tuple[Optional[ExecutionState], Optional[str]]:
    with tempfile.TemporaryDirectory() as tmp_dir:
        tmp = Path(tmp_dir)
        trace_file = tmp / "trace.txt"
        full_source = get_boilerplate_sde(asm_path.read_text())

        bin_file = assemble_and_link(asm_path, full_source, tmp)
        try:
            subprocess.run([str(SDE_RUNNER), "-stop_int3", "1", "-early_out",
                            "-dt_lines", "-dt_rawinst", "-dt_print_funcsim",
                            "-debugtrace", "-odebugtrace", str(trace_file), "--",
                            str(bin_file)], check=True, capture_output=True, timeout=TIMEOUT_SECONDS)
        except subprocess.SubprocessError as e:
            return None, f"SDE Error: {e}\nStderr:\n{(e.stderr or b'').decode(errors='replace').strip()}"
        if not trace_file.exists():
            return None, "SDE debugtrace file was not generated"
        return parse_sde_debugtrace(trace_file)

def run_kraken(path: Path) -> Tuple[Optional[ExecutionState], Optional[str]]:
    try:
        res = subprocess.run([KRAKEN_RUNNER, path], capture_output=True, check=True, timeout=TIMEOUT_SECONDS)
        data = json.loads(res.stdout)
        return ExecutionState(regs=data["regs"], flags=data["flags"]), None
    except subprocess.SubprocessError as e:
        return None, f"Kraken Error: {e}\nStderr:\n{(e.stderr or b'').decode(errors='replace').strip()}"

# Parse the preamble for flags to be masked out because they are left undefined by the test.
def get_undefined_flags(path: Path) -> List[str]:
    first_line = path.read_text().splitlines()[0]
    # TODO String parsing is brittle, a structured format for test metadata would be more sustainable long term.
    if first_line.startswith("# Undefined flags:"):
        raw_flags = first_line.split(":", 1)[1]
        return [f.strip() for f in raw_flags.split(",") if f.strip()]
    return []

def compare_states(reference: ExecutionState, kraken: ExecutionState, undefined_flags: List[str], reference_name: str) -> List[str]:
    diffs = []
    for r in [r for r in REGS if r != "rsp"]:
        rv, kv = reference.regs[r], kraken.regs[r]
        if rv != kv:
            diffs.append(f"{r}: {reference_name}={rv:#x} ({rv}), kraken={kv:#x} ({kv})")
    for f in [f for f in FLAG_MAP if not f in undefined_flags]:
        if reference.flags[f] != kraken.flags[f]:
            diffs.append(f"flag {f}: x86={reference.flags[f]} | kraken={kraken.flags[f]}")
    return diffs

def test_file(path: Path) -> Tuple[bool, str]:
    print(f"{path.name:50}", end="", flush=True)

    try:
        kraken, kraken_err = run_kraken(path)
        native, native_err = run_native(path) if NATIVE_X64 else (None, None)
        sde, sde_err = run_sde(path) if SDE_RUNNER else (None, None)
    except AssembleAndLinkError as e:
        print(f"[{Color.RED}INVALID{Color.RESET}]")
        return False, str(e)

    if native_err or kraken_err or sde_err:
        print(f"[{Color.RED}CRASH{Color.RESET}]")
        return False, native_err or kraken_err or sde_err

    undefined_flags = get_undefined_flags(path)
    if native:
        diffs = compare_states(native, kraken, undefined_flags, "native")
        if diffs:
            print(f"[{Color.RED}FAIL{Color.RESET}]")
            return False, "\n".join(diffs)
    if sde:
        diffs = compare_states(sde, kraken, undefined_flags, "sde")
        if diffs:
            print(f"[{Color.RED}FAIL{Color.RESET}]")
            return False, "\n".join(diffs)

    print(f"[{Color.GREEN}PASS{Color.RESET}]")
    return True, ""

if __name__ == "__main__":
    if not NATIVE_X64 and not SDE_RUNNER:
        print(f"{Color.RED}Error: Neither native x86_64 execution nor SDE runner is available.{Color.RESET}")
        print("Cannot compare Kraken execution against any real reference. Aborting.")
        sys.exit(1)

    if not KRAKEN_RUNNER.exists():
        print(f"{Color.RED}Error: Kraken runner not found at {KRAKEN_RUNNER}{Color.RESET}")
        print(f"\nTo build it, run the following from the project root:")
        print(f"  {Color.GREEN}lake build krakenrunner{Color.RESET}\n")
        sys.exit(1)

    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <file.S or dir>")
        sys.exit(1)

    target = Path(sys.argv[1]).resolve()
    files = sorted(target.rglob("*.S")) if target.is_dir() else ([target] if target.exists() else [])

    if not files:
        print(f"Error: No .S files found at {target}")
        sys.exit(1)

    errors = []
    for f in files:
        success, report = test_file(f)
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
