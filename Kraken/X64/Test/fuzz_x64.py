#!/usr/bin/env python3
"""Batched differential fuzzer: runs random x86_64 sequences that Kraken deems deterministic
(krakenrunner_x64 --generate) on hardware and compares with Kraken's prediction (--batch)."""

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "Test"))
import asm_tests
from fuzz import run_fuzzer

if __name__ == "__main__":
    sys.exit(run_fuzzer(asm_tests, as_cmd=["as"], ld_cmd=["ld"], description=__doc__))
