#!/usr/bin/env python3
"""Check compiler provenance and instruction layouts for the sum-to-n examples."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


@dataclass(frozen=True)
class Architecture:
    target: str
    assembly: str
    lean_file: str
    lean_sizes_name: str
    encoded_token_digits: int


ARCHITECTURES = {
    "x64": Architecture(
        target="x86_64-unknown-linux-gnu",
        assembly="Kraken/X64/Examples/sum_to_n.S",
        lean_file="Kraken/X64/Examples/SumToN.lean",
        lean_sizes_name="compiledSumToNSizes",
        encoded_token_digits=2,
    ),
    "aarch64": Architecture(
        target="aarch64-unknown-linux-gnu",
        assembly="Kraken/AArch64/Examples/sum_to_n.S",
        lean_file="Kraken/AArch64/Examples/SumToN.lean",
        lean_sizes_name="compiledSumToNAArch64Sizes",
        encoded_token_digits=8,
    ),
}

COMPILE_FLAGS = [
    "-std=gnu11",
    "-Oz",
    "-S",
    "-fno-asynchronous-unwind-tables",
    "-fno-stack-protector",
    "-fno-pic",
    "-fno-unroll-loops",
    "-fno-vectorize",
    "-fno-slp-vectorize",
    "-fno-ident",
]

DISASSEMBLY_ADDRESS = re.compile(r"^\s*([0-9a-fA-F]+):\s+(.*)$")
LABEL = re.compile(r"^([.$A-Za-z_][.$A-Za-z_0-9]*):")


def run(command: list[str]) -> str:
    result = subprocess.run(
        command,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"command failed ({result.returncode}): {' '.join(command)}\n{result.stdout}"
        )
    return result.stdout


def disassemble(
    objdump: str, object_file: Path, encoded_token_digits: int
) -> list[tuple[int, str]]:
    output = run([objdump, "-d", str(object_file)])
    instructions: list[tuple[int, str]] = []
    for line in output.splitlines():
        match = DISASSEMBLY_ADDRESS.match(line)
        if not match:
            continue
        encoded_tokens: list[str] = []
        for token in match.group(2).split():
            if len(token) != encoded_token_digits or not all(
                char in "0123456789abcdefABCDEF" for char in token
            ):
                break
            encoded_tokens.append(token.lower())
        if encoded_tokens:
            instructions.append((int(match.group(1), 16), "".join(encoded_tokens)))
    if not instructions:
        raise RuntimeError(f"could not parse any instructions from:\n{output}")
    return instructions


def assembly_events(assembly: Path) -> list[tuple[str, str]]:
    events: list[tuple[str, str]] = []
    for line in assembly.read_text().splitlines():
        stripped = line.strip()
        label = LABEL.match(stripped)
        if label:
            events.append(("label", label.group(1)))
        elif stripped and not stripped.startswith((".", "#", "//")):
            events.append(("instruction", stripped.split(maxsplit=1)[0]))
    return events


def directive_sizes(
    events: list[tuple[str, str]], instructions: list[tuple[int, str]]
) -> list[int]:
    encoded_sizes = iter(len(encoded) // 2 for _, encoded in instructions)
    sizes: list[int] = []
    try:
        for kind, _ in events:
            sizes.append(0 if kind == "label" else next(encoded_sizes))
    except StopIteration as error:
        raise RuntimeError(
            "assembly source contains more instructions than the disassembly"
        ) from error
    try:
        next(encoded_sizes)
    except StopIteration:
        return sizes
    raise RuntimeError("disassembly contains more instructions than the assembly source")


def lean_sizes(lean_file: Path, declaration: str) -> list[int]:
    pattern = re.compile(
        rf"{re.escape(declaration)}\s*:\s*List Nat\s*:=\s*\[([^]]+)\]"
    )
    match = pattern.search(lean_file.read_text())
    if not match:
        raise RuntimeError(f"could not find {declaration} in {lean_file}")
    return [int(item.strip()) for item in match.group(1).split(",")]


def require_tool(name: str) -> str:
    resolved = shutil.which(name)
    if resolved is None:
        raise RuntimeError(f"required tool not found: {name}")
    return resolved


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--arch", choices=ARCHITECTURES, required=True)
    parser.add_argument("--clang", default=os.environ.get("CLANG", "clang"))
    parser.add_argument("--objdump", default=os.environ.get("OBJDUMP", "objdump"))
    args = parser.parse_args()

    architecture = ARCHITECTURES[args.arch]
    clang = require_tool(args.clang)
    objdump = require_tool(args.objdump)
    root = Path(__file__).resolve().parents[2]
    source = root / "Kraken/Examples/sum_to_n.c"
    checked_assembly = root / architecture.assembly
    lean_file = root / architecture.lean_file

    with tempfile.TemporaryDirectory(prefix=f"kraken-sum-to-n-{args.arch}-") as directory:
        temporary = Path(directory)
        generated_assembly = temporary / "sum_to_n.S"
        generated_object = temporary / "generated.o"
        checked_object = temporary / "checked.o"

        target_flag = f"--target={architecture.target}"
        run(
            [
                clang,
                target_flag,
                *COMPILE_FLAGS,
                "-o",
                str(generated_assembly),
                str(source),
            ]
        )
        run(
            [clang, target_flag, "-c", "-o", str(generated_object), str(generated_assembly)]
        )
        run(
            [clang, target_flag, "-c", "-o", str(checked_object), str(checked_assembly)]
        )

        generated_instructions = disassemble(
            objdump, generated_object, architecture.encoded_token_digits
        )
        checked_instructions = disassemble(
            objdump, checked_object, architecture.encoded_token_digits
        )
        if generated_instructions != checked_instructions:
            raise RuntimeError(
                "the checked-in assembly no longer matches the compiler output\n"
                f"generated: {generated_instructions}\n"
                f"checked:   {checked_instructions}"
            )

        checked_events = assembly_events(checked_assembly)
        # Local label names are a Clang implementation detail and may vary by
        # release.  Exact offsets and encodings above include the branch
        # displacements, so they are the stable compiler-provenance check.  We
        # parse the checked-in source separately to connect those bytes to the
        # directive layout modeled in Lean.
        derived_sizes = directive_sizes(checked_events, checked_instructions)
        modeled_sizes = lean_sizes(lean_file, architecture.lean_sizes_name)
        if derived_sizes != modeled_sizes:
            raise RuntimeError(
                "the Lean layout no longer matches the assembled instruction sizes\n"
                f"assembled: {derived_sizes}\n"
                f"Lean:      {modeled_sizes}"
            )

    offsets = [offset for offset, _ in checked_instructions]
    print(
        f"verified {args.arch} compiler output, checked-in assembly, "
        "and Lean instruction sizes"
    )
    print(f"instruction offsets: {offsets}")
    print(f"directive sizes:     {modeled_sizes}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except RuntimeError as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(1)
