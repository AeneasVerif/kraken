#!/usr/bin/env python3
import json
import os
import re
import struct
import subprocess
import sys
import tempfile
import difflib
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

BIN_DIR = Path(__file__).resolve().parent.parent.parent.parent / ".lake/build/bin"
KRAKEN_RUNNER = BIN_DIR / "krakenrunner_x64"
ATT2INTEL = BIN_DIR / "att2intel"

REGS = ["rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rsp", "rbp",
        "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]
# The extended zmm registers are frequently unavailable on actual machines.
ZMMS = [f"zmm{i}" for i in range(32)]
# ymm16..31 are only available on AVX512(VL), but we'll assume we have AVX2.
SAFE_YMMS = [f"ymm{i}" for i in range(16)]
# Maps each flag to its bit in the EFLAGS register.
FLAG_MAP = {"cf": 0, "pf": 2, "af": 4, "zf": 6, "sf": 7, "of": 11, "df": 10}
TIMEOUT_SECONDS = 50
# Kraken's initial rsp and its stack mapping [STACK - STACK_SIZE, STACK), filled with 0xff
# (`stackLocation`, `stackSize` and `initStack` in KrakenRunnerX64.lean). The low byte of STACK
# is 0, so PF of rsp arithmetic (e.g. `subq $8, %rsp`) is predictable.
STACK = 0x7ffecafee200
STACK_SIZE = 800
# The dumped machine state: GPRs, rflags, then ymms (see `parse_raw_state`).
YMM_BASE = (len(REGS) + 1) * 8
STATE_BYTES = YMM_BASE + 32 * len(SAFE_YMMS)
# A section for Kraken's stack. Linking with LD_STACK places it at [STACK - STACK_SIZE, STACK), so
# the binary has exactly Kraken's stack mapping and can use Kraken's absolute rsp.
STACK_SECTION = f""".section .stack, "aw", @nobits
.space {STACK_SIZE}"""
LD_STACK = f"--section-start=.stack={STACK - STACK_SIZE:#x}"

class Color:
    GREEN = "\033[92m"
    RED = "\033[91m"
    CYAN = "\033[96m"
    BOLD = "\033[1m"
    RESET = "\033[0m"

def reset_state() -> str:
  """Assembly that sets up Kraken's initial state (`initData` in KrakenRunnerX64.lean): rsp = STACK,
  rflags = 0, the stack filled with 0xff, and all other GPRs and ymm registers zero."""
  zero_gprs = "\n    ".join(f"movq $0, %{r}" for r in REGS if r != "rsp")
  return f"""
    movq ${STACK}, %rsp
    pushq $0
    popfq                       # rflags = 0
    leaq -{STACK_SIZE}(%rsp), %rdi
    movb $0xff, %al
    movq ${STACK_SIZE}, %rcx
    rep stosb                   # memset(rdi, al, rcx)
    vzeroall
    {zero_gprs}
"""

def save_state(out: str) -> str:
  """Assembly that stores the machine state (STATE_BYTES bytes) at `out`, in the layout
  `parse_raw_state` reads. Clobbers rax and rsp."""
  saves = [f"movq %{r}, {out} + {i * 8}(%rip)" for i, r in enumerate(REGS)]
  saves += [f"vmovups %{y}, {out} + {YMM_BASE + i * 32}(%rip)" for i, y in enumerate(SAFE_YMMS)]
  # rflags can only be read via the stack, and the code may have moved rsp.
  saves += [f"movq ${STACK}, %rsp", "pushfq", "popq %rax", f"movq %rax, {out} + {len(REGS) * 8}(%rip)"]
  return "\n    " + "\n    ".join(saves) + "\n"

def get_boilerplate(instruction_text: str) -> str:
  return f"""
.bss
_final_state: .space {STATE_BYTES}
{STACK_SECTION}
.text
.globl _start
_start:
{reset_state()}
# --- Test Code Start ---
{instruction_text}
# --- Test Code End ---
{save_state("_final_state")}
{write_and_exit("_final_state", STATE_BYTES)}"""

def write_and_exit(buf: str, nbytes: int) -> str:
  """Assembly that writes the `nbytes` bytes at label `buf` to stdout, then exits with status 0.
  Linux syscall numbers: write = 1, exit = 60 (see e.g. https://x64.syscall.sh/)."""
  return f"""
    movq $1, %rax               # write(
    movq $1, %rdi               #   stdout,
    leaq {buf}(%rip), %rsi      #   buf,
    movq ${nbytes}, %rdx        #   nbytes)
    syscall
    movq $60, %rax              # exit(
    xorq %rdi, %rdi             #   0)
    syscall
"""

@dataclass
class ExecutionState:
    regs: Dict[str, int]
    zmms: Dict[str, int]
    flags: Dict[str, bool]

def parse_raw_state(raw_bytes: bytes) -> ExecutionState:
    fmt = f"<{len(REGS)}Q Q" + "32s" * len(SAFE_YMMS)
    unpacked = struct.unpack(fmt, raw_bytes)
    reg_values = unpacked[:len(REGS)]
    rflags = unpacked[len(REGS)]
    ymm_raw = unpacked[len(REGS) + 1:]
    ymm_values = [
        f"{int.from_bytes(chunk, byteorder='little'):x}"
        for chunk in ymm_raw
    ]
    return ExecutionState(
        regs=dict(zip(REGS, reg_values)),
        zmms=dict(zip(ZMMS, ymm_values)),
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
            subprocess.run(["ld", LD_STACK, "-o", str(bin_file), str(obj_file)], check=True, capture_output=True)
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
        return ExecutionState(regs=data["regs"], zmms=data["zmms"], flags=data["flags"]), None
    except subprocess.CalledProcessError as e:
        return None, f"Kraken Error:\n{(e.stderr or b"").decode(errors="replace").strip()}"
    # This except clause ensures any stderr messages are shown even if there is a timeout
    # (The default Exception object does not have a stderr attribute, so we cannot show this there)
    except subprocess.TimeoutExpired as e:
        return None, f"Kraken Error: {e}\nStderr:\n{(e.stderr or b'').decode(errors='replace').strip()}"
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
    for r in REGS:
        rv, kv = real.regs.get(r, 0), kraken.regs.get(r, 0)
        if rv != kv:
            diffs.append(f"{r}: x86={rv:#x} ({rv}), kraken={kv:#x} ({kv})")

    for r in ZMMS:
        rv, kv = real.zmms.get(r, '0'), kraken.zmms.get(r, '0')
        if rv != kv:
            diffs.append(f"{r}: x86={rv}, kraken={kv}")

    for f in [f for f in FLAG_MAP if not f in undefined_flags]:
        if real.flags[f] != kraken.flags[f]:
            diffs.append(f"flag {f}: x86={real.flags[f]} | kraken={kraken.flags[f]}")
    return diffs


def assembled_text(src_path: Path, tmp_dir: Path) -> Tuple[Path, bytes]:
    obj_path = tmp_dir / f"{src_path.stem}.o"
    bin_path = tmp_dir / f"{src_path.stem}.bin"
    try:
        subprocess.run(['as', "-o", str(obj_path), str(src_path)],
                       capture_output=True, check=True)
        subprocess.run(["objcopy", "-O", "binary", "-j", ".text", str(obj_path), str(bin_path)],
                       capture_output=True, check=True)
    except subprocess.CalledProcessError as e:
        print(f"Subprocess failed: {' '.join(str(x) for x in e.cmd)}", file=sys.stderr)
        err_msg = e.stderr.decode().strip() if isinstance(e.stderr, bytes) else (e.stderr or "")
        print(f"Error: {err_msg}", file=sys.stderr)
        raise
    return obj_path, bin_path.read_bytes()

def disassemble(obj_path: Path) -> List[str]:
    try:
        res = subprocess.run(["objdump", "-d", str(obj_path)],
                             capture_output=True, check=True, text=True)
    except subprocess.CalledProcessError as e:
        print(f"Subprocess failed: {' '.join(str(x) for x in e.cmd)}", file=sys.stderr)
        print(f"Error: {e.stderr}", file=sys.stderr)
        raise
    return res.stdout.splitlines()

def colorize_diff(diff_lines: List[str]) -> List[str]:
    colored = []
    for line in diff_lines:
        if line.startswith('---') or line.startswith('+++'):
            colored.append(f"{Color.BOLD}{line}{Color.RESET}")
        elif line.startswith('-'):
            colored.append(f"{Color.RED}{line}{Color.RESET}")
        elif line.startswith('+'):
            colored.append(f"{Color.GREEN}{line}{Color.RESET}")
        elif line.startswith('@@'):
            colored.append(f"{Color.CYAN}{line}{Color.RESET}")
        else:
            colored.append(line)
    return colored

def test_roundtrip(asm_path: Path) -> Tuple[bool, str]:
    with tempfile.TemporaryDirectory() as tmp:
        tmp_dir = Path(tmp)
        intel_src = tmp_dir / f"{asm_path.stem}.intel.S"

        try:
            with open(intel_src, "w") as f:
                subprocess.run([ATT2INTEL, asm_path],
                               stdout=f, stderr=subprocess.PIPE, check=True)
        except subprocess.CalledProcessError as e:
            err_msg = e.stderr.decode().strip() if isinstance(e.stderr, bytes) else (e.stderr or "")
            return False, f"att2intel failed: {' '.join(str(x) for x in e.cmd)}\n{err_msg}"

        try:
            orig_obj, orig_bytes = assembled_text(asm_path, tmp_dir)
            intel_obj, intel_bytes = assembled_text(intel_src, tmp_dir)
            if orig_bytes != intel_bytes:
                diff = difflib.unified_diff(
                    disassemble(orig_obj), disassemble(intel_obj),
                    fromfile="AT&T", tofile="Intel", lineterm=""
                )
                colored = colorize_diff(diff)
                return False, f"Roundtrip mismatch:\n" + "\n".join(colored)
        except subprocess.CalledProcessError as e:
            err_msg = e.stderr.decode().strip() if isinstance(e.stderr, bytes) else (e.stderr or "")
            return False, f"assembler failed: {' '.join(str(x) for x in e.cmd)}\n{err_msg}"
    return True, ""

def test_file(path: Path) -> Tuple[bool, str]:
    print(f"{path.name:50}", end="", flush=True)

    roundtrip_success, roundtrip_err = test_roundtrip(path)
    if not roundtrip_success:
        print(f"[{Color.RED}ROUNDTRIP FAIL{Color.RESET}]")
        return False, roundtrip_err

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
        print(f"  {Color.GREEN}lake build krakenrunner_x64{Color.RESET}\n")
        sys.exit(1)

    if not ATT2INTEL.exists():
        print(f"{Color.RED}Error: att2intel not found at {ATT2INTEL}{Color.RESET}")
        print(f"\nTo build it, run the following from the project root:")
        print(f"  {Color.GREEN}lake build att2intel{Color.RESET}\n")
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
