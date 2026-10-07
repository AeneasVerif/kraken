#!/usr/bin/env python3
"""Batched differential fuzzer: runs random AArch64 sequences that Kraken deems deterministic
(krakenrunner_aarch64 --generate) on QEMU and compares with Kraken's prediction (--batch)."""

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "Test"))
import asm_tests
from fuzz import run_fuzzer


def main():
    as_cmd = asm_tests.get_assembler()
    ld_cmd = asm_tests.get_linker()
    qemu_bin = asm_tests.find_tool(["qemu-aarch64", "qemu-aarch64-static"])
    if not as_cmd or not ld_cmd or not qemu_bin:
        raise RuntimeError("Missing AArch64 assembler, linker, or qemu-aarch64.")
    return run_fuzzer(asm_tests, as_cmd=as_cmd, ld_cmd=ld_cmd, emu_cmd=[qemu_bin], description=__doc__)


if __name__ == "__main__":
    sys.exit(main())
