#!/usr/bin/env python3
"""Unit tests for `bv_decide_qbe/scripts/run_upstream_suite.py`."""

from __future__ import annotations

import json
import math
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_upstream_suite as suite  # noqa: E402


class RunUpstreamSuiteTests(unittest.TestCase):
    """Test CLI parsing, rewriting, classification, and compare aggregation."""

    def test_cli_defaults_and_options(self) -> None:
        parser = suite.build_arg_parser()
        args = parser.parse_args(["--lean4-tests-dir", "/tmp/lean4/tests"])
        self.assertEqual(args.lean4_tests_dir, Path("/tmp/lean4/tests"))
        self.assertEqual(args.mode, "compat")
        self.assertEqual(args.timeout, 120.0)
        self.assertEqual(args.jobs, 1)
        self.assertIsNone(args.filter)
        self.assertIsNone(args.out_json)
        self.assertIsNone(args.bv_decide_qbe_dir)

        args2 = parser.parse_args(
            [
                "--lean4-tests-dir",
                "/tmp/lean4/tests",
                "--mode",
                "compare",
                "--timeout",
                "45",
                "--jobs",
                "2",
                "--filter",
                "bv_arith|bv_bitblast_stress",
                "--out-json",
                "/tmp/out.json",
                "--bv-decide-qbe-dir",
                "/tmp/qbe",
            ]
        )
        self.assertEqual(args2.mode, "compare")
        self.assertEqual(args2.timeout, 45.0)
        self.assertEqual(args2.jobs, 2)
        self.assertEqual(args2.filter, "bv_arith|bv_bitblast_stress")
        self.assertEqual(args2.out_json, Path("/tmp/out.json"))
        self.assertEqual(args2.bv_decide_qbe_dir, Path("/tmp/qbe"))

    def test_rewrite_for_qbe(self) -> None:
        src = "\n".join(
            [
                "module",
                "meta import Std.Tactic.BVDecide",
                "import Std.Tactic.BVDecide",
                "example : True := by",
                "  sym =>",
                "    bv_decide_push",
                "    bv_decide +uf",
            ]
        )
        rewritten = suite.rewrite_for_qbe(src)
        expected = "\n".join(
            [
                "module",
                "meta import BvDecideQbe.Tactic",
                "import BvDecideQbe.Tactic",
                "example : True := by",
                "  sym =>",
                "    bv_decide_qbe_push",
                "    bv_decide_qbe +uf",
            ]
        )
        self.assertEqual(rewritten, expected)
        self.assertNotIn("bv_decide_qbe_qbe", rewritten)

    def test_classify_verbatim_pass_and_timeout_and_failure(self) -> None:
        lean_file = Path("/tmp/test/elab/bv_arith.lean")
        st, note, kinds = suite.classify_qbe_output(
            lean_file, suite.RunOutput(returncode=0, elapsed_s=0.5, stdout="", stderr="")
        )
        self.assertEqual((st, note, kinds), ("PASS", "verbatim", []))

        st, note, kinds = suite.classify_qbe_output(
            lean_file,
            suite.RunOutput(returncode=-1, elapsed_s=12.0, stdout="", stderr="", timed_out=True),
        )
        self.assertEqual(st, "FAIL")
        self.assertIn("timeout", note)

        st, note, _ = suite.classify_qbe_output(
            lean_file,
            suite.RunOutput(
                returncode=1,
                elapsed_s=0.2,
                stdout=f"{lean_file}:5:2: error: unsolved goals\n",
                stderr="",
            ),
        )
        self.assertEqual(st, "FAIL")
        self.assertIn("unsolved goals", note)

    def test_classify_expected_axiom_and_sat_cex_diffs(self) -> None:
        lean_ax = Path("/tmp/test/elab/bv_axiom_check.lean")
        ax_out = "\n".join(
            [
                "'bv_axiomCheck' depends on axioms: [propext, Classical.choice, Quot.sound, bv_axiomCheck._leanqbe.bv_solve.ax_1_2]",
                f"{lean_ax}:10:0: error: ❌️ Docstring on `#guard_msgs` does not match generated message:",
                "",
                "- info: 'bv_axiomCheck' depends on axioms: [propext, Classical.choice, Quot.sound, bv_axiomCheck._native.bv_decide_qbe.ax_1_5]",
                "+ info: 'bv_axiomCheck' depends on axioms: [propext, Classical.choice, Quot.sound, bv_axiomCheck._leanqbe.bv_solve.ax_1_2]",
            ]
        )
        st, _note, kinds = suite.classify_qbe_output(
            lean_ax, suite.RunOutput(returncode=1, elapsed_s=0.3, stdout=ax_out, stderr="")
        )
        self.assertEqual((st, kinds), ("PASS_EXPECTED_DIFF", ["axiom_name"]))

        # Adding an unexpected axiom must fail, not pass as expected diff.
        bad_ax_out = ax_out.replace(
            "bv_axiomCheck._leanqbe.bv_solve.ax_1_2]",
            "sorryAx, bv_axiomCheck._leanqbe.bv_solve.ax_1_2]",
        )
        st_bad, _note, _ = suite.classify_qbe_output(
            lean_ax, suite.RunOutput(returncode=1, elapsed_s=0.3, stdout=bad_ax_out, stderr="")
        )
        self.assertEqual(st_bad, "FAIL")

        # SAT CEX value + variable-order diff must pass as expected diff.
        lean_uf = Path("/tmp/test/elab/bv_uf.lean")
        cex_out = "\n".join(
            [
                f"{lean_uf}:68:2: error: - The prover used the following expressions as uninterpreted functions:",
                "  - f x",
                "  - f y",
                "The prover found a counterexample, consider the following assignment:",
                "f x = 0#8",
                "f y = 128#8",
                "y = 0#8",
                "x = 128#8",
                f"{lean_uf}:65:0: error: ❌️ Docstring on `#guard_msgs` does not match generated message:",
                "",
                "  error: - The prover used the following expressions as uninterpreted functions:",
                "    - f x",
                "    - f y",
                "  The prover found a counterexample, consider the following assignment:",
                "- f x = 127#8",
                "- x = 255#8",
                "- f y = 255#8",
                "- y = 127#8",
                "+ f x = 0#8",
                "+ f y = 128#8",
                "+ y = 0#8",
                "+ x = 128#8",
            ]
        )
        st_cex, _note, kinds_cex = suite.classify_qbe_output(
            lean_uf, suite.RunOutput(returncode=1, elapsed_s=0.4, stdout=cex_out, stderr="")
        )
        self.assertEqual((st_cex, kinds_cex), ("PASS_EXPECTED_DIFF", ["sat_cex"]))

        # Potentially spurious SAT CEX assignment diff must also pass as sat_cex.
        lean_spurious = Path("/tmp/test/elab/bv_counterexample.lean")
        spurious_out = "\n".join(
            [
                f"{lean_spurious}:113:2: error: The prover found a potentially spurious counterexample:",
                "- It abstracted the following unsupported expressions as opaque variables:",
                "  - zeros 32",
                "- The following potentially relevant hypotheses could not be used:",
                "  - x.toNat = y.toNat derived via assumption h1",
                "Consider the following assignment:",
                "x = 0#32",
                "zeros 32 = 0#32",
                "y = 1#32",
                f"{lean_spurious}:112:0: error: ❌️ Docstring on `#guard_msgs` does not match generated message:",
                "",
                "  error: The prover found a potentially spurious counterexample:",
                "  - It abstracted the following unsupported expressions as opaque variables:",
                "    - zeros 32",
                "  - The following potentially relevant hypotheses could not be used:",
                "    - x.toNat = y.toNat derived via assumption h1",
                "  Consider the following assignment:",
                "  x = 0#32",
                "  zeros 32 = 0#32",
                "- y = 2147483648#32",
                "+ y = 1#32",
            ]
        )
        st_spur, _note, kinds_spur = suite.classify_qbe_output(
            lean_spurious, suite.RunOutput(returncode=1, elapsed_s=0.3, stdout=spurious_out, stderr="")
        )
        self.assertEqual((st_spur, kinds_spur), ("PASS_EXPECTED_DIFF", ["sat_cex"]))

        # Stray unguarded error alongside valid guard diff must fail.
        st_stray, _note, _ = suite.classify_qbe_output(
            lean_uf,
            suite.RunOutput(
                returncode=1,
                elapsed_s=0.4,
                stdout=cex_out + f"\n{lean_uf}:99:2: error: tactic failed\n",
                stderr="",
            ),
        )
        self.assertEqual(st_stray, "FAIL")

    def test_run_suite_with_tiny_fixtures_and_wam_wgm(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            tests_dir = root / "tests"
            (tests_dir / "elab").mkdir(parents=True)
            (tests_dir / "elab_bench").mkdir(parents=True)

            (tests_dir / "elab" / "bv_arith.lean").write_text(
                "import Std.Tactic.BVDecide\nexample : True := by bv_decide\n",
                encoding="utf-8",
            )
            (tests_dir / "elab" / "bv_import.lean").write_text(
                "-- tests missing import error\nexample : True := by bv_decide\n",
                encoding="utf-8",
            )
            (tests_dir / "elab_bench" / "bv_bench.lean").write_text(
                "import Std.Tactic.BVDecide\nexample : True := by bv_decide\n",
                encoding="utf-8",
            )
            (tests_dir / "elab" / "unrelated.lean").write_text("def x := 1\n", encoding="utf-8")

            seen_rewrites: dict[str, str] = {}

            def fake_runner(cmd, lean_file, env, timeout_s):
                is_qbe = any("--load-dynlib=" in c for c in cmd)
                if is_qbe:
                    seen_rewrites[lean_file.name] = lean_file.read_text(encoding="utf-8")
                    elapsed = 1.0 if lean_file.name == "bv_arith.lean" else 2.0
                else:
                    elapsed = 2.0 if lean_file.name == "bv_arith.lean" else 8.0
                return suite.RunOutput(returncode=0, elapsed_s=elapsed, stdout="", stderr="")

            results, counts, cmp_sum = suite.run_suite(
                tests_dir=tests_dir,
                mode="compare",
                timeout_s=30.0,
                jobs=1,
                bv_dir=root / "bv_decide_qbe",
                repo_root=root,
                lean_prefix=root / "tc",
                runner=fake_runner,
                skip_artifact_check=True,
            )

            self.assertEqual([r.file for r in results], [
                "elab/bv_arith.lean",
                "elab/bv_import.lean",
                "elab_bench/bv_bench.lean",
            ])
            self.assertIn("import BvDecideQbe.Tactic", seen_rewrites["bv_arith.lean"])
            self.assertIn("by bv_decide_qbe", seen_rewrites["bv_arith.lean"])
            self.assertNotIn("bv_import.lean", seen_rewrites)
            self.assertEqual(counts["total"], 3)
            self.assertEqual(counts["pass"], 2)
            self.assertEqual(counts["na"], 1)
            self.assertEqual(counts["fail"], 0)
            self.assertEqual(cmp_sum["paired_count"], 2)
            self.assertAlmostEqual(cmp_sum["total_up_s"], 10.0)
            self.assertAlmostEqual(cmp_sum["total_qbe_s"], 3.0)
            self.assertAlmostEqual(cmp_sum["w_am"], 0.3)
            self.assertAlmostEqual(cmp_sum["w_gm"], math.sqrt(0.5 * 0.25))

            report = suite.format_report(results, counts, cmp_sum, "compare")
            self.assertIn("W-AM=0.300x", report)
            self.assertIn("W-GM=", report)

            out_json = root / "report.json"
            # Also exercise main() end-to-end with --out-json and mocked runner/artifacts.
            lib_dir = root / "bv_decide_qbe" / ".lake" / "build" / "lib"
            (lib_dir / "lean" / "BvDecideQbe").mkdir(parents=True)
            (lib_dir / f"libkissat_qbe{suite.shared_lib_ext()}").write_text("", encoding="utf-8")
            (lib_dir / f"libbv__decide__qbe_BvDecideQbeNative{suite.shared_lib_ext()}").write_text(
                "", encoding="utf-8"
            )
            (lib_dir / "lean" / "BvDecideQbe" / "Tactic.olean").write_text("", encoding="utf-8")
            orig_resolve_prefix = suite.resolve_lean_prefix
            orig_runner = suite.run_lean_file
            try:
                suite.resolve_lean_prefix = lambda: root / "tc"
                suite.run_lean_file = fake_runner
                rc = suite.main(
                    [
                        "--lean4-tests-dir",
                        str(tests_dir),
                        "--mode",
                        "compare",
                        "--jobs",
                        "2",
                        "--filter",
                        "bv_arith|bv_bench",
                        "--out-json",
                        str(out_json),
                        "--bv-decide-qbe-dir",
                        str(root / "bv_decide_qbe"),
                    ]
                )
            finally:
                suite.resolve_lean_prefix = orig_resolve_prefix
                suite.run_lean_file = orig_runner

            self.assertEqual(rc, 0)
            payload = json.loads(out_json.read_text(encoding="utf-8"))
            self.assertEqual(payload["counts"]["total"], 2)
            self.assertEqual(payload["counts"]["pass"], 2)
            self.assertEqual(payload["compare"]["paired_count"], 2)
            self.assertAlmostEqual(payload["compare"]["w_am"], 0.3)

            # Non-existent tests dir returns exit code 2 cleanly.
            rc_err = suite.main(["--lean4-tests-dir", str(root / "missing")])
            self.assertEqual(rc_err, 2)


if __name__ == "__main__":
    unittest.main()
