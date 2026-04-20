#!/usr/bin/env python3
import json
import os
import re
import struct
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent.parent.parent
KRAKEN_RUNNER = SCRIPT_DIR / ".lake/build/bin/krakenrunner"

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

def get_boilerplate(instruction_text: str) -> str:
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

def run_real_x86(asm_path: Path) -> Tuple[Optional[ExecutionState], Optional[str]]:
    with tempfile.TemporaryDirectory() as tmp_dir:
        tmp = Path(tmp_dir)
        s_file = tmp / asm_path.name
        obj_file = tmp / f"{asm_path.stem}.o"
        bin_file = tmp / f"{asm_path.stem}.bin"
        
        full_source = get_boilerplate(asm_path.read_text())
        s_file.write_text(full_source)

        try:
            subprocess.run(["as", "-o", str(obj_file), str(s_file)], check=True, capture_output=True)
            subprocess.run(["ld", "-o", str(bin_file), str(obj_file)], check=True, capture_output=True)
            res = subprocess.run([str(bin_file)], check=True, capture_output=True, timeout=TIMEOUT_SECONDS)
            return parse_raw_state(res.stdout), None
        except subprocess.CalledProcessError as e:
            err = (e.stderr or b"").decode(errors="replace").replace(str(tmp), "...").strip()
            prologue_len = full_source.split("# --- Test Code Start ---")[0].count("\n") + 1
            line_nr_adjusted_err = re.sub(r":(\d+):", lambda m: f":{int(m.group(1)) - prologue_len}:", err)
            return None, f"x86 Error ({e.cmd[0]}):\n{line_nr_adjusted_err}"

def run_kraken(path: Path) -> Tuple[Optional[ExecutionState], Optional[str]]:
    try:
        res = subprocess.run([KRAKEN_RUNNER, path], capture_output=True, check=True, timeout=TIMEOUT_SECONDS)
        data = json.loads(res.stdout)
        return ExecutionState(regs=data["regs"], flags=data["flags"]), None
    except subprocess.CalledProcessError as e:
        return None, f"Kraken Error:\n{(e.stderr or b"").decode(errors="replace").strip()}"
    except Exception as e:
        return None, f"Kraken Error: {e}"

# Parse the preamble for flags to be masked out because they are left undefined by the test.
def get_undefined_flags(path: Path) -> List[str]:
    first_line = path.read_text().splitlines()[0]
    # TODO String parsing is brittle, a structured format for test metadata would be more sustainable long term.
    if first_line.startswith("# Undefined flags:"):
        raw_flags = first_line.split(":", 1)[1]
        return [f.strip() for f in raw_flags.split(",") if f.strip()]
    return []

def compare_states(real: ExecutionState, kraken: ExecutionState, undefined_flags: List[str]) -> List[str]:
    diffs = []
    for r in [r for r in REGS if r != "rsp"]:
        rv, kv = real.regs[r], kraken.regs[r]
        if rv != kv:
            diffs.append(f"{r}: x86={rv:#x} ({rv}), kraken={kv:#x} ({kv})")
            
    for f in [f for f in FLAG_MAP if not f in undefined_flags]:
        if real.flags[f] != kraken.flags[f]:
            diffs.append(f"flag {f}: x86={real.flags[f]} | kraken={kraken.flags[f]}")
    return diffs

def test_file(path: Path) -> Tuple[bool, str]:
    print(f"{path.name:50}", end="")
    
    real, real_err = run_real_x86(path)
    kraken, kraken_err = run_kraken(path)

    if real_err or kraken_err:
        print(f"[{Color.RED}CRASH{Color.RESET}]")
        return False, real_err or kraken_err

    undefined_flags = get_undefined_flags(path)
    diffs = compare_states(real, kraken, undefined_flags)
    if diffs:
        print(f"[{Color.RED}FAIL{Color.RESET}]")
        return False, "\n".join(diffs)

    print(f"[{Color.GREEN}PASS{Color.RESET}]")
    return True, ""

if __name__ == "__main__":
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
