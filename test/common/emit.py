#!/usr/bin/env python3
"""Unified target-parameterized assembly emitter CLI (`test/common/emit.py`).

Direct Python launcher for emitting target assembly that:
  - Avoids an outer `import Lean` process startup on every invocation
  - Uses `tempfile.TemporaryDirectory` + signal cleanup (zero leaked `/tmp/leanqbe_emit_*.lean`)
  - Respects `STAGE_LEAN_PATH` and `LEAN_PATH`
  - Supports `--both-arches` to spawn x64 and Arm64 emissions in parallel

Usage:
  python3 -B test/common/emit.py --arch <x64|arm64> --suite <suite> [args...]
  python3 -B test/common/emit.py --both-arches --suite <suite> [common_args...]
  python3 -B test/common/emit.py --both-arches --suite <suite> \
      --x64-arg <arg> [--x64-arg ...] --arm64-arg <arg> [--arm64-arg ...]
"""

import os
import pathlib
import signal
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]

TEMPLATES: dict[tuple[str, str], str] = {
    ("x64", "kissat"): """\
import LeanQbe.T.Examples.Kissat.Solver
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.PrintATTAlign

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Amd64

public def main (args : List String) : IO Unit := do
  let outPath : System.FilePath := match args with
    | p :: _ => p
    | [] => "/tmp/kissat_x64.s"
  let hints := kissatFns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← match LeanQbe.T.compile x64Target.toIsa x64LegalTarget kissatFns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let asm := Driver.emitAsm (fun c => toATTAligned c ++ "\\n") kissatFns dirs
  IO.FS.writeFile outPath asm
""",
    ("arm64", "kissat"): """\
import LeanQbe.T.Examples.Kissat.Solver
import LeanQbe.T.Driver
import LeanQbe.T.Arm64.Targ
import Kraken.AArch64.Print

open LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Arm64

public def main (args : List String) : IO Unit := do
  let outPath : System.FilePath := match args with
    | p :: _ => p
    | [] => "/tmp/kissat_arm64.s"
  let hints := kissatFns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let dirs ← match LeanQbe.T.compile armTarget.toIsa armLegalTarget kissatFns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let pp := fun c =>
    ".p2align 2\\n" ++ String.intercalate "\\n" (c.map Kraken.AArch64.Print.directive)
  IO.FS.writeFile outPath (Driver.emitAsm (fun c => pp c ++ "\\n") kissatFns dirs)
""",
    ("x64", "plain"): """\
import LeanQbe.T.Examples.Kissat.Plain
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.PrintATTAlign

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.Examples.Kissat.Plain LeanQbe.T.Amd64

public def main (args : List String) : IO Unit := do
  let outPath : System.FilePath := match args with
    | p :: _ => p
    | [] => "/tmp/plain_x64.s"
  let hints := plainFns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← match LeanQbe.T.compile x64Target.toIsa x64LegalTarget plainFns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let asm := Driver.emitAsm (fun c => toATTAligned c ++ "\\n") plainFns dirs
  IO.FS.writeFile outPath asm
""",
    ("arm64", "plain"): """\
import LeanQbe.T.Examples.Kissat.Plain
import LeanQbe.T.Driver
import LeanQbe.T.Arm64.Targ
import Kraken.AArch64.Print

open LeanQbe.T LeanQbe.T.Examples.Kissat.Plain LeanQbe.T.Arm64

public def main (args : List String) : IO Unit := do
  let outPath : System.FilePath := match args with
    | p :: _ => p
    | [] => "/tmp/plain_arm64.s"
  let hints := plainFns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let dirs ← match LeanQbe.T.compile armTarget.toIsa armLegalTarget plainFns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let pp := fun c =>
    ".p2align 2\\n" ++ String.intercalate "\\n" (c.map Kraken.AArch64.Print.directive)
  IO.FS.writeFile outPath (Driver.emitAsm (fun c => pp c ++ "\\n") plainFns dirs)
""",
    ("x64", "m3"): """\
import LeanQbe.T.Examples.Kissat.FullM3
import LeanQbe.T.PrintCpp
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.PrintATTAlign

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.PrintCpp LeanQbe.T.Examples.Kissat.FullM3 LeanQbe.T.Amd64

public def main (args : List String) : IO Unit := do
  let (outPath, cppPath?) : System.FilePath × Option System.FilePath := match args with
    | p :: c :: _ => (p, some c)
    | [p] => (p, none)
    | [] => ("/tmp/kissat_m3_x64.s", none)
  let fns := m3Module.fns
  let hints := fns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← match LeanQbe.T.compile x64Target.toIsa x64LegalTarget fns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let asm := Driver.emitAsm (fun c => toATTAligned c ++ "\\n") fns dirs
  IO.FS.writeFile outPath asm
  if let some cppPath := cppPath? then
    let cpp ← match ppTModule m3Module with
      | .ok s => pure s
      | .error e => throw (IO.userError e)
    IO.FS.writeFile cppPath cpp
""",
    ("arm64", "m3"): """\
import LeanQbe.T.Examples.Kissat.FullM3
import LeanQbe.T.Driver
import LeanQbe.T.Arm64.Targ
import Kraken.AArch64.Print

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.Examples.Kissat.FullM3 LeanQbe.T.Arm64

public def main (args : List String) : IO Unit := do
  let outPath : System.FilePath := match args with
    | p :: _ => p
    | [] => "/tmp/kissat_m3_arm64.s"
  let fns := m3Module.fns
  let hints := fns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let dirs ← match LeanQbe.T.compile armTarget.toIsa armLegalTarget fns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let pp := fun c =>
    ".p2align 2\\n" ++ String.intercalate "\\n" (c.map Kraken.AArch64.Print.directive)
  IO.FS.writeFile outPath (Driver.emitAsm (fun c => pp c ++ "\\n") fns dirs)
""",
    ("x64", "m4"): """\
import LeanQbe.T.Examples.Kissat.FullM4
import LeanQbe.T.PrintCpp
import LeanQbe.T.Opt
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.PrintATTAlign

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.PrintCpp LeanQbe.T.Examples.Kissat.FullM4 LeanQbe.T.Amd64

public def main (args : List String) : IO Unit := do
  let (outPath, cppPath?) : System.FilePath × Option System.FilePath := match args with
    | p :: c :: _ => (p, some c)
    | [p] => (p, none)
    | [] => ("/tmp/kissat_m4_x64.s", none)
  let fns := (m4Module.optInline 40).fns
  let hints := fns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← match LeanQbe.T.compile x64Target.toIsa x64LegalTarget fns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let asm := Driver.emitAsm (fun c => toATTAligned c ++ "\\n") fns dirs
  IO.FS.writeFile outPath asm
  if let some cppPath := cppPath? then
    let cpp ← match ppTModule m4Module with
      | .ok s => pure s
      | .error e => throw (IO.userError e)
    IO.FS.writeFile cppPath cpp
""",
    ("arm64", "m4"): """\
import LeanQbe.T.Examples.Kissat.FullM4
import LeanQbe.T.Opt
import LeanQbe.T.Driver
import LeanQbe.T.Arm64.Targ
import Kraken.AArch64.Print

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.Examples.Kissat.FullM4 LeanQbe.T.Arm64

public def main (args : List String) : IO Unit := do
  let outPath : System.FilePath := match args with
    | p :: _ => p
    | [] => "/tmp/kissat_m4_arm64.s"
  let fns := (m4Module.optInline 40).fns
  let hints := fns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let dirs ← match LeanQbe.T.compile armTarget.toIsa armLegalTarget fns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let pp := fun c =>
    ".p2align 2\\n" ++ String.intercalate "\\n" (c.map Kraken.AArch64.Print.directive)
  IO.FS.writeFile outPath (Driver.emitAsm (fun c => pp c ++ "\\n") fns dirs)
""",
    ("x64", "lcnf"): """\
import LeanQbe.T.LeanLCNF.Lower1
import LeanQbe.T.LeanLCNF.Demo
import LeanQbe.T.LeanLCNF.Coverage
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.PrintATTAlign

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64

private def emitOne (tag : String) (m : LcModule) (out : System.FilePath) : IO Unit := do
  let t0 ← IO.monoMsNow
  let tfs ← IO.ofExcept (lowerModule m)
  let fns := Frontend.C0.tflatFnsToFns tfs
  let hints := fns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← IO.ofExcept (LeanQbe.T.compile x64Target.toIsa x64LegalTarget fns hints)
  IO.FS.writeFile out (Driver.emitAsm (fun c => toATTAligned c ++ "\\n") fns dirs)
  IO.eprintln s!"emit_x64 ({tag}): {fns.length} functions in {(← IO.monoMsNow) - t0} ms"

def main (args : List String) : IO Unit := do
  let out : System.FilePath := args.headD "lcnf_x64.s"
  emitOne "demo" Demo.lcnfProgram out
  match args with
  | _ :: covOut :: _ => emitOne "cov" Coverage.covProgram covOut
  | _ => pure ()
""",
    ("arm64", "lcnf"): """\
import LeanQbe.T.LeanLCNF.Lower1
import LeanQbe.T.LeanLCNF.Demo
import LeanQbe.T.LeanLCNF.Coverage
import LeanQbe.T.Driver
import LeanQbe.T.Arm64.Targ
import Kraken.AArch64.Print

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Arm64

private def emitOne (tag : String) (m : LcModule) (out : System.FilePath) : IO Unit := do
  let t0 ← IO.monoMsNow
  let tfs ← IO.ofExcept (lowerModule m)
  let fns := Frontend.C0.tflatFnsToFns tfs
  let hints := fns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let dirs ← IO.ofExcept (LeanQbe.T.compile armTarget.toIsa armLegalTarget fns hints)
  let pp := fun c =>
    ".p2align 2\\n" ++ String.intercalate "\\n" (c.map Kraken.AArch64.Print.directive)
  IO.FS.writeFile out (Driver.emitAsm (fun c => pp c ++ "\\n") fns dirs)
  IO.eprintln s!"emit_arm64 ({tag}): {fns.length} functions in {(← IO.monoMsNow) - t0} ms"

def main (args : List String) : IO Unit := do
  let out : System.FilePath := args.headD "lcnf_arm64.s"
  emitOne "demo" Demo.lcnfProgram out
  match args with
  | _ :: covOut :: _ => emitOne "cov" Coverage.covProgram covOut
  | _ => pure ()
""",
    ("x64", "bignum"): """\
import LeanQbe.T.Amd64.Bignum
import LeanQbe.T.Amd64.PrintATTAlign

set_option autoImplicit false

open LeanQbe.T.Amd64.Bignum

private def emitFn (name body : String) : String :=
  ".text\\n.globl " ++ name ++ "\\n" ++ body ++ "\\n"

def main (args : List String) : IO UInt32 := do
  let outDir := args.headD "/tmp/leanqbe-tbignum"
  IO.FS.writeFile s!"{outDir}/mul4x4_x64.s"
    (emitFn "mul4x4" (LeanQbe.T.Amd64.toATTAligned mul4x4Compiled.code))
  IO.FS.writeFile s!"{outDir}/addMod25519_x64.s"
    (emitFn "addMod25519" (LeanQbe.T.Amd64.toATTAligned addMod25519Compiled.code))
  IO.FS.writeFile s!"{outDir}/subMod25519_x64.s"
    (emitFn "subMod25519" (LeanQbe.T.Amd64.toATTAligned subMod25519Compiled.code))
  return 0
""",
    ("arm64", "bignum"): """\
import LeanQbe.T.Arm64.Bignum
import Kraken.AArch64.Print

open LeanQbe.T.Arm64.Bignum

private def emitFn (name : String) (body : List String) : String :=
  ".text\\n.globl " ++ name ++ "\\n.p2align 2\\n" ++
    String.intercalate "\\n" body ++ "\\n"

def main (args : List String) : IO UInt32 := do
  let outDir := args.headD "/tmp/leanqbe-tbignum"
  IO.FS.writeFile s!"{outDir}/mul4x4_arm64.s"
    (emitFn "mul4x4" (mul4x4Compiled.code.map Kraken.AArch64.Print.directive))
  IO.FS.writeFile s!"{outDir}/addMod25519_arm64.s"
    (emitFn "addMod25519" (addMod25519Compiled.code.map Kraken.AArch64.Print.directive))
  IO.FS.writeFile s!"{outDir}/subMod25519_arm64.s"
    (emitFn "subMod25519" (subMod25519Compiled.code.map Kraken.AArch64.Print.directive))
  return 0
""",
    ("x64", "chacha"): """\
import LeanQbe.T.Amd64.ChaCha
import LeanQbe.T.Amd64.PrintATTAlign

set_option autoImplicit false

open LeanQbe.T.Amd64.ChaCha

def main (args : List String) : IO UInt32 := do
  let outDir := args.headD "/tmp/leanqbe-tchacha"
  let asm := ".text\\n.globl chacha20Block\\n" ++
    LeanQbe.T.Amd64.toATTAligned compiled.code ++ "\\n"
  IO.FS.writeFile s!"{outDir}/chacha_x64.s" asm
  return 0
""",
    ("arm64", "chacha"): """\
import LeanQbe.T.Arm64.ChaCha
import Kraken.AArch64.Print

open LeanQbe.T.Arm64.ChaCha

def main (args : List String) : IO UInt32 := do
  let outDir := args.headD "/tmp/leanqbe-tchacha"
  let asm :=
    ".text\\n.globl chacha20Block\\n.p2align 2\\n" ++
      String.intercalate "\\n" (compiled.code.map Kraken.AArch64.Print.directive) ++ "\\n"
  IO.FS.writeFile s!"{outDir}/chacha_arm64.s" asm
  return 0
""",
}

SUITE_ALIASES: dict[str, str] = {
    "kissat": "kissat",
    "solver": "kissat",
    "dmin": "kissat",
    "coreplus": "coreplus",
    "plain": "plain",
    "m3": "m3",
    "fullm3": "m3",
    "m4": "m4",
    "fullm4": "m4",
    "lcnf": "lcnf",
    "bignum": "bignum",
    "t_bignum": "bignum",
    "chacha": "chacha",
    "t_chacha": "chacha",
}

ARCH_ALIASES: dict[str, str] = {
    "x64": "x64",
    "x86_64": "x64",
    "x86-64": "x64",
    "amd64": "x64",
    "arm64": "arm64",
    "aarch64": "arm64",
    "arm": "arm64",
}


def get_lean_cmd_and_env() -> tuple[list[str], dict[str, str]]:
    env = os.environ.copy()
    stage = env.get("STAGE_LEAN_PATH", "")
    if stage:
        lake_lib = str(ROOT / ".lake" / "build" / "lib" / "lean")
        existing = env.get("LEAN_PATH", "")
        parts = [p for p in [stage, lake_lib, existing] if p]
        env["LEAN_PATH"] = ":".join(parts)
        return ["lean"], env
    if env.get("LEAN_PATH", ""):
        return ["lean"], env
    return ["lake", "env", "lean"], env


def parse_args(argv: list[str]) -> tuple[list[str], str, dict[str, list[str]]]:
    arch: str | None = None
    both_arches = False
    suite_raw: str | None = None
    rest: list[str] = []
    x64_args: list[str] = []
    arm64_args: list[str] = []
    i = 0
    while i < len(argv):
        tok = argv[i]
        if tok == "--arch" and i + 1 < len(argv):
            arch = ARCH_ALIASES.get(argv[i + 1].lower())
            if arch is None:
                raise ValueError(f"invalid --arch '{argv[i + 1]}'")
            i += 2
        elif tok == "--both-arches":
            both_arches = True
            i += 1
        elif tok == "--suite" and i + 1 < len(argv):
            suite_raw = argv[i + 1].lower()
            i += 2
        elif tok == "--x64-arg" and i + 1 < len(argv):
            x64_args.append(argv[i + 1])
            i += 2
        elif tok == "--arm64-arg" and i + 1 < len(argv):
            arm64_args.append(argv[i + 1])
            i += 2
        elif tok in ("-h", "--help"):
            print(
                "usage: python3 -B test/common/emit.py "
                "(--arch <x64|arm64> | --both-arches) --suite <suite> "
                "[--x64-arg <arg> ...] [--arm64-arg <arg> ...] [args...]"
            )
            sys.exit(0)
        else:
            rest.append(tok)
            i += 1

    if suite_raw is None or suite_raw not in SUITE_ALIASES:
        raise ValueError(
            "missing or invalid --suite "
            "<kissat|coreplus|plain|m3|m4|lcnf|bignum|chacha>"
        )
    suite = SUITE_ALIASES[suite_raw]

    if both_arches:
        if arch is not None:
            raise ValueError("cannot specify both --arch and --both-arches")
        return (
            ["x64", "arm64"],
            suite,
            {
                "x64": x64_args if (x64_args or arm64_args) else rest,
                "arm64": arm64_args if (x64_args or arm64_args) else rest,
            },
        )
    if arch is None:
        raise ValueError("missing --arch <x64|arm64> or --both-arches")
    per_arch = x64_args if (arch == "x64" and x64_args) else (
        arm64_args if (arch == "arm64" and arm64_args) else rest
    )
    return [arch], suite, {arch: per_arch}


def main(argv: list[str]) -> int:
    try:
        arches, suite, arch_args = parse_args(argv)
    except ValueError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        print(
            "usage: python3 -B test/common/emit.py "
            "(--arch <x64|arm64> | --both-arches) --suite <suite> [args...]",
            file=sys.stderr,
        )
        return 2

    cmd_prefix, env = get_lean_cmd_and_env()
    procs: list[tuple[str, subprocess.Popen[bytes]]] = []

    def terminate_children() -> None:
        for _, p in procs:
            if p.poll() is None:
                try:
                    p.terminate()
                except OSError:
                    pass
        for _, p in procs:
            if p.poll() is None:
                try:
                    p.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    try:
                        p.kill()
                    except OSError:
                        pass

    def handle_signal(signum: int, _frame: object) -> None:
        terminate_children()
        raise SystemExit(128 + signum)

    old_term = signal.signal(signal.SIGTERM, handle_signal)
    old_int = signal.signal(signal.SIGINT, handle_signal)
    try:
        with tempfile.TemporaryDirectory(prefix="leanqbe_emit_") as tmpdir:
            for arch in arches:
                code = TEMPLATES.get((arch, suite))
                if code is None:
                    print(
                        f"ERROR: unknown (arch, suite) combination: ({arch}, {suite})",
                        file=sys.stderr,
                    )
                    return 2
                script = os.path.join(tmpdir, f"emit_{arch}_{suite}.lean")
                with open(script, "w", encoding="utf-8") as fh:
                    fh.write(code)
                cmd = cmd_prefix + ["--run", script] + arch_args[arch]
                procs.append((arch, subprocess.Popen(cmd, env=env)))

            rc = 0
            for arch, p in procs:
                ret = p.wait()
                if ret != 0:
                    print(
                        f"ERROR: emit ({arch}, {suite}) exited with status {ret}",
                        file=sys.stderr,
                    )
                    if rc == 0:
                        rc = ret
            return rc
    finally:
        terminate_children()
        signal.signal(signal.SIGTERM, old_term)
        signal.signal(signal.SIGINT, old_int)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
