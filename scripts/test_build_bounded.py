#!/usr/bin/env python3
"""Unit tests for `scripts/build_bounded.sh` resource bounds and footgun guards."""

from __future__ import annotations

import os
import subprocess
import sys
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
BUILD_BOUNDED_SH = SCRIPTS_DIR / "build_bounded.sh"


def _run_build_bounded(
    *args: str,
    cwd: Path = REPO_ROOT,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    run_env = os.environ.copy()
    if env:
        run_env.update(env)
    return subprocess.run(
        ["bash", str(BUILD_BOUNDED_SH), *args],
        cwd=str(cwd),
        env=run_env,
        capture_output=True,
        text=True,
        timeout=60,
        check=False,
    )


class TestBuildBounded(unittest.TestCase):
    """Covers build_bounded.sh flags, cgroup formatting, broad-target guards, and dry-run."""

    def test_script_is_executable(self) -> None:
        self.assertTrue(BUILD_BOUNDED_SH.is_file(), f"{BUILD_BOUNDED_SH} must exist")
        self.assertTrue(
            os.access(BUILD_BOUNDED_SH, os.X_OK),
            f"{BUILD_BOUNDED_SH} must be executable (+x)",
        )

    def test_bash_syntax_check(self) -> None:
        res = subprocess.run(
            ["bash", "-n", str(BUILD_BOUNDED_SH)],
            capture_output=True,
            text=True,
            timeout=10,
            check=False,
        )
        self.assertEqual(res.returncode, 0, f"bash -n failed: {res.stderr}")

    def test_default_args_dry_run(self) -> None:
        res = _run_build_bounded("--dry-run", "LeanQbeCore")
        self.assertEqual(res.returncode, 0, f"stdout: {res.stdout}\nstderr: {res.stderr}")
        out = res.stdout.strip()

        # Exact command line verification (LEAN_NUM_THREADS=1, no -j on lake build)
        expected = (
            "timeout 600 systemd-run --user --scope --quiet --slice=leanqbe-builds.slice "
            "-p MemoryMax=18G -p MemorySwapMax=0 -p OOMPolicy=kill "
            "env LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true "
            "LEAN_NUM_THREADS=1 lake build --wfail LeanQbeCore"
        )
        self.assertEqual(out, expected)

        # Verify key individual flags and guards
        self.assertIn("timeout 600", out)
        self.assertIn("systemd-run --user --scope --quiet --slice=leanqbe-builds.slice", out)
        self.assertIn("MemoryMax=18G", out)
        self.assertIn("MemorySwapMax=0", out)
        self.assertIn("OOMPolicy=kill", out)
        self.assertIn("LAKE_ARTIFACT_CACHE=true", out)
        self.assertIn("LAKE_RESTORE_ARTIFACTS=true", out)
        self.assertIn("LEAN_NUM_THREADS=1", out)
        self.assertIn("lake build --wfail", out)
        self.assertNotIn("lake build -j", out)
        self.assertTrue(out.endswith("LeanQbeCore"))

    def test_custom_args_dry_run(self) -> None:
        res = _run_build_bounded(
            "-j",
            "2",
            "-m",
            "24G",
            "-t",
            "900",
            "--no-wfail",
            "--dry-run",
            "LeanQbeCore",
        )
        self.assertEqual(res.returncode, 0, f"stdout: {res.stdout}\nstderr: {res.stderr}")
        out = res.stdout.strip()
        expected = (
            "timeout 900 systemd-run --user --scope --quiet --slice=leanqbe-builds.slice "
            "-p MemoryMax=24G -p MemorySwapMax=0 -p OOMPolicy=kill "
            "env LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true "
            "LEAN_NUM_THREADS=2 lake build LeanQbeCore"
        )
        self.assertEqual(out, expected)
        self.assertNotIn("--wfail", out)
        self.assertNotIn("lake build -j", out)

    def test_threads_flag_alias_dry_run(self) -> None:
        res = _run_build_bounded(
            "--threads",
            "4",
            "-m",
            "24G",
            "-t",
            "900",
            "--no-wfail",
            "--dry-run",
            "LeanQbeCore",
        )
        self.assertEqual(res.returncode, 0, f"stdout: {res.stdout}\nstderr: {res.stderr}")
        out = res.stdout.strip()
        expected = (
            "timeout 900 systemd-run --user --scope --quiet --slice=leanqbe-builds.slice "
            "-p MemoryMax=24G -p MemorySwapMax=0 -p OOMPolicy=kill "
            "env LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true "
            "LEAN_NUM_THREADS=4 lake build LeanQbeCore"
        )
        self.assertEqual(out, expected)

    def test_alternative_flag_syntax_dry_run(self) -> None:
        # Combined short flags -j2 -m24G -t900
        res = _run_build_bounded(
            "-j2",
            "-m24G",
            "-t900",
            "--no-wfail",
            "--dry-run",
            "LeanQbeAmd64Core",
        )
        self.assertEqual(res.returncode, 0, res.stderr)
        out = res.stdout.strip()
        self.assertIn("timeout 900", out)
        self.assertIn("MemoryMax=24G", out)
        self.assertIn("LEAN_NUM_THREADS=2", out)
        self.assertIn("lake build LeanQbeAmd64Core", out)
        self.assertNotIn("--wfail", out)

        # Long form flags --jobs, --mem, --timeout, --wfail
        res2 = _run_build_bounded(
            "--jobs",
            "3",
            "--mem",
            "32G",
            "--timeout",
            "1200",
            "--wfail",
            "--dry-run",
            "LeanQbeArm64Core",
        )
        self.assertEqual(res2.returncode, 0, res2.stderr)
        out2 = res2.stdout.strip()
        self.assertIn("timeout 1200", out2)
        self.assertIn("MemoryMax=32G", out2)
        self.assertIn("LEAN_NUM_THREADS=3", out2)
        self.assertIn("lake build --wfail LeanQbeArm64Core", out2)

        # Equals syntax for long flags
        res3 = _run_build_bounded(
            "--jobs=4",
            "--mem=16G",
            "--timeout=300",
            "--dry-run",
            "LeanQbeCompileGuards",
        )
        self.assertEqual(res3.returncode, 0, res3.stderr)
        out3 = res3.stdout.strip()
        self.assertIn("timeout 300", out3)
        self.assertIn("MemoryMax=16G", out3)
        self.assertIn("LEAN_NUM_THREADS=4", out3)
        self.assertIn("lake build --wfail LeanQbeCompileGuards", out3)

    def test_broad_target_rejection_empty_and_option_only_args(self) -> None:
        # Bare invocation without targets
        res = _run_build_bounded()
        self.assertNotEqual(res.returncode, 0)
        self.assertIn("error: no build targets specified", res.stderr)
        self.assertIn("LeanQbeCore", res.stderr)

        # Bare dry-run invocation without targets
        res_dry = _run_build_bounded("--dry-run")
        self.assertNotEqual(res_dry.returncode, 0)
        self.assertIn("error: no build targets specified", res_dry.stderr)

        # Option-only invocation after -- (no real targets)
        res_opt = _run_build_bounded("--dry-run", "--", "--no-build")
        self.assertNotEqual(res_opt.returncode, 0)
        self.assertIn("error: no build targets specified", res_opt.stderr)

    def test_broad_target_rejection_bare_and_prefixed_umbrella_targets(self) -> None:
        umbrella_cases = [
            # Bare umbrella
            "LeanQbe",
            "LeanQbeAmd64",
            "LeanQbeArm64",
            "LeanQbeTest",
            # Prefixed variants
            "+LeanQbe",
            "+LeanQbeAmd64",
            "@/LeanQbe",
            "@LeanQbeArm64",
            # Suffix facets
            "LeanQbe:elabArts",
            "LeanQbeTest:o",
            "+LeanQbeTest:o",
            # Bootstrap0 umbrella targets
            "LeanQbeBootstrap0",
            "LeanQbeBootstrap0Test",
            "+LeanQbeBootstrap0:static",
        ]
        for tgt in umbrella_cases:
            with self.subTest(target=tgt):
                res = _run_build_bounded(tgt)
                self.assertNotEqual(res.returncode, 0)
                self.assertIn(f"broad umbrella target '{tgt}' rejected", res.stderr)
                self.assertIn("--allow-broad", res.stderr)

                res_dry = _run_build_bounded("--dry-run", tgt)
                self.assertNotEqual(res_dry.returncode, 0)
                self.assertIn(f"broad umbrella target '{tgt}' rejected", res_dry.stderr)

        # Mixed targets containing at least one broad umbrella target
        res_mixed = _run_build_bounded("--dry-run", "LeanQbeCore", "+LeanQbeAmd64")
        self.assertNotEqual(res_mixed.returncode, 0)
        self.assertIn("broad umbrella target '+LeanQbeAmd64' rejected", res_mixed.stderr)

    def test_allow_broad_acceptance(self) -> None:
        # Empty args with --allow-broad
        res_empty = _run_build_bounded("--allow-broad", "--dry-run")
        self.assertEqual(res_empty.returncode, 0, res_empty.stderr)
        self.assertIn("lake build --wfail", res_empty.stdout.strip())

        # Each umbrella target with --allow-broad
        broad_targets = [
            "LeanQbe",
            "LeanQbeAmd64",
            "LeanQbeArm64",
            "LeanQbeTest",
            "+LeanQbe",
            "LeanQbeBootstrap0",
        ]
        for tgt in broad_targets:
            with self.subTest(target=tgt):
                res = _run_build_bounded("--allow-broad", "--dry-run", tgt)
                self.assertEqual(res.returncode, 0, res.stderr)
                self.assertTrue(res.stdout.strip().endswith(tgt))

    def test_fine_grained_targets_accepted(self) -> None:
        fine_grained = [
            "LeanQbeCore",
            "LeanQbeAmd64Core",
            "LeanQbeArm64Core",
            "LeanQbeCompileGuards",
            "LeanQbeTest.T.Smoke",
            "leanqbe",
            "leanqbe-arm64",
            "+LeanQbe.T.CoreHub",
            "LeanQbe/T/Core.lean:o",
        ]
        for tgt in fine_grained:
            with self.subTest(target=tgt):
                res = _run_build_bounded("--dry-run", tgt)
                self.assertEqual(res.returncode, 0, f"{tgt} failed: {res.stderr}")
                self.assertTrue(res.stdout.strip().endswith(tgt))

        # Multiple fine-grained targets
        res_multi = _run_build_bounded(
            "--dry-run", "LeanQbeCore", "LeanQbeAmd64Core", "LeanQbeArm64Core"
        )
        self.assertEqual(res_multi.returncode, 0, res_multi.stderr)
        self.assertTrue(
            res_multi.stdout.strip().endswith("LeanQbeCore LeanQbeAmd64Core LeanQbeArm64Core")
        )

    def test_double_dash_target_separator(self) -> None:
        res = _run_build_bounded("--dry-run", "--", "LeanQbeCore")
        self.assertEqual(res.returncode, 0, res.stderr)
        self.assertTrue(res.stdout.strip().endswith("LeanQbeCore"))

        # Non-option target accompanied by lake options
        res2 = _run_build_bounded("--dry-run", "--", "--no-build", "LeanQbeCore")
        self.assertEqual(res2.returncode, 0, res2.stderr)
        self.assertTrue(res2.stdout.strip().endswith("--no-build LeanQbeCore"))

    def test_help_flag(self) -> None:
        for flag in ("-h", "--help"):
            with self.subTest(flag=flag):
                res = _run_build_bounded(flag)
                self.assertEqual(res.returncode, 0)
                self.assertIn("Usage: scripts/build_bounded.sh", res.stdout)
                self.assertIn("--allow-broad", res.stdout)

    def test_empty_option_values_rejected(self) -> None:
        empty_cases = [
            ("-j", ""),
            ("--jobs=",),
            ("-m", ""),
            ("--mem=",),
            ("-t", ""),
            ("--timeout=",),
            ("--threads", ""),
            ("--threads=",),
        ]
        for opt_tuple in empty_cases:
            with self.subTest(opt=opt_tuple):
                res = _run_build_bounded(*opt_tuple)
                self.assertNotEqual(res.returncode, 0)
                self.assertIn("requires a non-empty argument", res.stderr)

    def test_missing_and_unknown_options(self) -> None:
        res_unknown = _run_build_bounded("--unknown-flag")
        self.assertNotEqual(res_unknown.returncode, 0)
        self.assertIn("unknown option '--unknown-flag'", res_unknown.stderr)

        for opt in ("-j", "-m", "-t", "--threads", "--jobs", "--mem", "--timeout"):
            with self.subTest(opt=opt):
                res_missing = _run_build_bounded(opt)
                self.assertNotEqual(res_missing.returncode, 0)
                self.assertIn(f"{opt} requires a non-empty argument", res_missing.stderr)

    def test_real_smoke_build(self) -> None:
        # Real non---dry-run smoke execution with fine-grained target LeanQbeTest.T.Smoke
        res = _run_build_bounded("-j", "1", "-m", "12G", "LeanQbeTest.T.Smoke")
        self.assertEqual(
            res.returncode,
            0,
            f"smoke build failed (rc={res.returncode}):\nstdout: {res.stdout}\nstderr: {res.stderr}",
        )
        self.assertIn("Build completed successfully", res.stdout + res.stderr)


if __name__ == "__main__":
    unittest.main()
