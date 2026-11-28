#!/usr/bin/env python3
"""Unit and integration tests for `bench/kissat/plot_dual_arch_survival.py`."""
from __future__ import annotations

import csv
import io
import json
import lzma
import re
import subprocess
import sys
import tempfile
import unittest
import xml.etree.ElementTree as ET
from pathlib import Path

BENCH_DIR = Path(__file__).resolve().parent
REPO_ROOT = BENCH_DIR.parents[1]
SCRIPT_PATH = BENCH_DIR / "plot_dual_arch_survival.py"
E190_CSV = BENCH_DIR / "data" / "kissat_e190f461_survival.csv"

sys.path.insert(0, str(BENCH_DIR))
import plot_dual_arch_survival as pda  # noqa: E402


SVG_NS = "http://www.w3.org/2000/svg"
FORBIDDEN_AXION_RE = re.compile(r"a" r"xion", re.IGNORECASE)
FORBIDDEN_BAREMETAL_RE = re.compile(r"bare[- ]?metal", re.IGNORECASE)
UNLABELED_RATIO_RE = re.compile(r"(?<![WI-])\b(?:GM|AM)\b")


def assert_strict_svg_invariants(
    test: unittest.TestCase,
    svg_text: str,
    expect_dense_min_vertices: int | None = None,
    expect_arm64_label: bool = True,
    expect_x64_label: bool = True,
) -> dict[str, object]:
    raw_bytes = svg_text.encode("utf-8")
    test.assertLess(len(raw_bytes), 40 * 1024, f"SVG too large: {len(raw_bytes)} B")
    test.assertIsNone(FORBIDDEN_AXION_RE.search(svg_text))
    test.assertIsNone(FORBIDDEN_BAREMETAL_RE.search(svg_text))

    root = ET.fromstring(svg_text)
    bg_rects = [
        el
        for el in root.findall(f"{{{SVG_NS}}}rect")
        if el.get("width") == "100%" and el.get("height") == "100%" and el.get("fill") == "#ffffff"
    ]
    test.assertTrue(bg_rects, "Expected opaque #ffffff background rect")

    all_text = "\n".join("".join(el.itertext()) for el in root.iter(f"{{{SVG_NS}}}text"))
    if expect_x64_label:
        test.assertIn("AMD EPYC Zen 5", all_text)
    if expect_arm64_label:
        test.assertIn("Arm Neoverse-V2", all_text)
    test.assertIn("W-GM", all_text)
    test.assertIn("W-AM", all_text)
    for el in root.iter(f"{{{SVG_NS}}}text"):
        txt = "".join(el.itertext())
        test.assertIsNone(
            UNLABELED_RATIO_RE.search(txt),
            f"Found unlabeled GM/AM in SVG text: {txt!r}",
        )

    curve_vertices: list[int] = []
    for el in root.iter(f"{{{SVG_NS}}}path"):
        if el.get("data-survival-curve") == "1":
            d = el.get("d", "")
            v_cnt = len(re.findall(r"[MLHVmlhv]", d))
            curve_vertices.append(v_cnt)
            test.assertLessEqual(v_cnt, 400, f"Curve exceeded 400 vertices: {v_cnt}")
            if expect_dense_min_vertices is not None:
                test.assertGreaterEqual(
                    v_cnt,
                    expect_dense_min_vertices,
                    f"Dense curve under-decimated (< {expect_dense_min_vertices}): {v_cnt}",
                )
    test.assertGreater(len(curve_vertices), 0, "Expected at least one survival curve path")
    return {"bytes": len(raw_bytes), "curve_vertices": curve_vertices}


class TestPlotDualArchSurvival(unittest.TestCase):
    def test_default_git_ref_is_artifacts(self) -> None:
        parser = pda.build_parser()
        args = parser.parse_args(["plot", "--git-path", "bench/results/foo", "-o", "/tmp/out.svg"])
        self.assertEqual(args.git_ref, "artifacts")

    def test_e190_export_plot_and_determinism(self) -> None:
        self.assertTrue(E190_CSV.is_file(), f"Missing fixture CSV: {E190_CSV}")
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            out_dir = tmp / "e190"
            svg1 = tmp / "plot1.svg"
            svg2 = tmp / "plot2.svg"

            rc_exp = pda.main(
                [
                    "export",
                    "--csv",
                    str(E190_CSV),
                    "--run-tag",
                    "e190f461",
                    "--commit",
                    "e190f461",
                    "--out-dir",
                    str(out_dir),
                ]
            )
            self.assertEqual(rc_exp, 0)

            xz_path = out_dir / "survival.csv.xz"
            manifest_path = out_dir / "manifest.json"
            self.assertTrue(xz_path.is_file())
            self.assertTrue(manifest_path.is_file())
            self.assertLess(xz_path.stat().st_size, 1_000_000)

            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
            self.assertEqual(manifest["commit"], "e190f461")
            self.assertEqual(manifest["run_tag"], "e190f461")
            self.assertEqual(manifest["row_count"], 1207)
            self.assertEqual(manifest["hosts"]["x64"]["cpu_label"], "AMD EPYC Zen 5")
            self.assertEqual(manifest["hosts"]["arm64"]["cpu_label"], "Arm Neoverse-V2")
            self.assertEqual(manifest["summary"]["x64"]["c1"]["solved"], 1163)
            self.assertEqual(manifest["summary"]["x64"]["c4"]["solved"], 1146)
            self.assertAlmostEqual(manifest["summary"]["x64"]["c4"]["w_gm"], 1.21, places=2)
            self.assertAlmostEqual(manifest["summary"]["x64"]["c4"]["w_am"], 1.32, places=2)
            self.assertAlmostEqual(manifest["summary"]["arm64"]["c4"]["w_gm"], 1.22, places=2)
            self.assertAlmostEqual(manifest["summary"]["arm64"]["c4"]["w_am"], 1.26, places=2)

            csv_text = lzma.decompress(xz_path.read_bytes()).decode("utf-8")
            self.assertIsNone(FORBIDDEN_AXION_RE.search(csv_text))
            self.assertIsNone(FORBIDDEN_BAREMETAL_RE.search(csv_text))
            self.assertIn("# commit: e190f461", csv_text)
            self.assertIn("# arm64_cpu: Arm Neoverse-V2", csv_text)
            body_lines = [ln for ln in csv_text.splitlines() if ln and not ln.startswith("#")]
            reader = csv.DictReader(io.StringIO("\n".join(body_lines)))
            first_row = next(reader)
            self.assertTrue(first_row["x64_c1_ms"].isdigit())

            self.assertEqual(
                pda.main(["plot", "--results-dir", str(out_dir), "-o", str(svg1)]),
                0,
            )
            # Also exercise default-mode CLI without explicit `plot` subcommand.
            self.assertEqual(
                pda.main(["--results-dir", str(out_dir), "-o", str(svg2)]),
                0,
            )

            txt1 = svg1.read_text(encoding="utf-8")
            txt2 = svg2.read_text(encoding="utf-8")
            self.assertEqual(txt1, txt2, "SVG output must be deterministic across runs")
            info = assert_strict_svg_invariants(self, txt1, expect_dense_min_vertices=250)
            self.assertEqual(len(info["curve_vertices"]), 8)

    def test_synthetic_dense_1000_instance_decimation(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            csv_path = tmp / "synthetic_1000.csv"
            with csv_path.open("w", encoding="utf-8", newline="") as f:
                w = csv.writer(f)
                w.writerow(
                    [
                        "id",
                        "verdict",
                        "x64_c1_s",
                        "x64_c0direct_s",
                        "x64_c3b_s",
                        "x64_c4_s",
                        "arm64_c1_s",
                        "arm64_c0direct_s",
                        "arm64_c3b_s",
                        "arm64_c4_s",
                    ]
                )
                for i in range(1000):
                    frac = i / 999.0
                    base = 0.012 * ((28.0 / 0.012) ** frac)
                    verdict = "sat" if i % 2 == 0 else "unsat"
                    w.writerow(
                        [
                            f"inst_{i:04d}",
                            verdict,
                            f"{base:.6f}" if i < 965 else "",
                            f"{base * 1.07:.6f}" if i < 955 else "",
                            f"{base * 1.14:.6f}" if i < 950 else "",
                            f"{base * 1.18:.6f}" if i < 948 else "",
                            f"{base * 1.04:.6f}" if i < 960 else "",
                            f"{base * 1.09:.6f}" if i < 950 else "",
                            f"{base * 1.21:.6f}" if i < 945 else "",
                            f"{base * 1.24:.6f}" if i < 945 else "",
                        ]
                    )

            svg_out = tmp / "synthetic_1000.svg"
            self.assertEqual(
                pda.main(["plot", "--csv", str(csv_path), "--commit", "deadbeef", "-o", str(svg_out)]),
                0,
            )
            info = assert_strict_svg_invariants(
                self, svg_out.read_text(encoding="utf-8"), expect_dense_min_vertices=250
            )
            self.assertEqual(len(info["curve_vertices"]), 8)
            for v in info["curve_vertices"]:
                self.assertGreaterEqual(v, 250)
                self.assertLessEqual(v, 400)

    def test_git_ref_artifacts_end_to_end(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            repo = tmp / "repo"
            repo.mkdir()
            git = lambda *args: subprocess.run(
                ["git", "-C", str(repo), *args],
                check=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            git("init", "-b", "main")
            git("config", "user.name", "Test User")
            git("config", "user.email", "test@example.com")
            (repo / "README.md").write_text("main branch\n", encoding="utf-8")
            git("add", "README.md")
            git("commit", "-m", "init main")

            # Export a dual-arch dataset directly onto `artifacts` branch.
            sample_csv = tmp / "mini.csv"
            sample_csv.write_text(
                "id,verdict,x64_c1_s,x64_c0direct_s,x64_c3b_s,x64_c4_s,"
                "arm64_c1_s,arm64_c0direct_s,arm64_c3b_s,arm64_c4_s\n"
                "cnf1,sat,0.050,0.060,0.070,0.075,0.055,0.065,0.080,0.085\n"
                "cnf2,unsat,0.500,0.550,0.600,0.620,0.520,0.560,0.640,0.660\n"
                "cnf3,unsat,5.000,5.200,5.400,5.500,5.100,5.300,5.600,5.700\n"
                "cnf4,sat,,,,,,,,\n",
                encoding="utf-8",
            )
            git("checkout", "-b", "artifacts")
            art_dir = repo / "bench" / "results" / "gate_g5_test"
            self.assertEqual(
                pda.main(
                    [
                        "export",
                        "--csv",
                        str(sample_csv),
                        "--run-tag",
                        "gate_g5_test",
                        "--commit",
                        "cafe1234",
                        "--out-dir",
                        str(art_dir),
                    ]
                ),
                0,
            )
            git("add", "bench/results/gate_g5_test")
            git("commit", "-m", "add gate_g5_test artifacts")
            git("checkout", "main")
            self.assertFalse((repo / "bench" / "results").exists())

            svg_from_git = tmp / "from_git.svg"
            svg_from_file = tmp / "from_git_file.svg"
            svg_from_csv = tmp / "from_csv.svg"

            # Default `--git-ref` should resolve to `artifacts`.
            proc = subprocess.run(
                [
                    sys.executable,
                    str(SCRIPT_PATH),
                    "plot",
                    "--git-repo",
                    str(repo),
                    "--git-path",
                    "bench/results/gate_g5_test",
                    "-o",
                    str(svg_from_git),
                ],
                check=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            self.assertIn("Wrote", proc.stdout)

            # Also verify direct file path under `--git-ref artifacts`.
            self.assertEqual(
                pda.main(
                    [
                        "plot",
                        "--git-ref",
                        "artifacts",
                        "--git-repo",
                        str(repo),
                        "--git-path",
                        "bench/results/gate_g5_test/survival.csv.xz",
                        "-o",
                        str(svg_from_file),
                    ]
                ),
                0,
            )
            self.assertEqual(
                pda.main(
                    [
                        "plot",
                        "--csv",
                        str(sample_csv),
                        "--commit",
                        "cafe1234",
                        "-o",
                        str(svg_from_csv),
                    ]
                ),
                0,
            )

            txt_git = svg_from_git.read_text(encoding="utf-8")
            txt_file = svg_from_file.read_text(encoding="utf-8")
            txt_csv = svg_from_csv.read_text(encoding="utf-8")
            assert_strict_svg_invariants(self, txt_git)
            self.assertEqual(txt_git, txt_file)
            self.assertEqual(txt_git, txt_csv)

    def test_devrez_json_and_per_arch_csv_merge(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            x64_json = tmp / "x64_results.json"
            arm64_csv = tmp / "arm64_results.csv"
            out_dir = tmp / "exported"
            svg_out = tmp / "devrez.svg"

            x64_payload = {
                "meta": {
                    "arch": "x86_64",
                    "suite": "stage1",
                    "timeout_s": 30.0,
                    "hostname": "host-x64",
                    "devrez": {
                        "entity": {"CPU Type": "turin"},
                        "lscpu_guard": {"model": "AMD EPYC 9B45 128-Core Processor"},
                    },
                    "solvers": ["c0direct", "c3b", "c4_g4_full"],
                },
                "results": [
                    {
                        "id": "p1",
                        "expected": "sat",
                        "solvers": {
                            "c0direct": {"status": 10, "wall_ms": 100.0, "verdict_ok": True, "model_ok": True, "timed_out": False},
                            "c3b": {"status": 10, "wall_ms": 110.0, "verdict_ok": True, "model_ok": True, "timed_out": False},
                            "c4_g4_full": {"status": 10, "wall_ms": 105.0, "verdict_ok": True, "model_ok": True, "timed_out": False},
                        },
                    },
                    {
                        "id": "p2",
                        "expected": "unsat",
                        "solvers": {
                            "c0direct": {"status": 20, "wall_ms": 2000.0, "verdict_ok": True, "model_ok": True, "timed_out": False},
                            "c3b": {"status": 20, "wall_ms": 2100.0, "verdict_ok": True, "model_ok": True, "timed_out": False},
                            "c4_g4_full": {"status": -1, "wall_ms": 30000.0, "verdict_ok": True, "model_ok": True, "timed_out": True},
                        },
                    },
                ],
            }
            x64_json.write_text(json.dumps(x64_payload), encoding="utf-8")

            arm64_csv.write_text(
                "id,stage_origin,expected,c0direct_status,c0direct_wall_ms,c0direct_model_ok,c0direct_verdict_ok,c0direct_timed_out,"
                "c3b_status,c3b_wall_ms,c3b_model_ok,c3b_verdict_ok,c3b_timed_out,"
                "c4_g4_full_status,c4_g4_full_wall_ms,c4_g4_full_model_ok,c4_g4_full_verdict_ok,c4_g4_full_timed_out\n"
                "p1,stage1,sat,10,120.0,True,True,False,10,130.0,True,True,False,10,125.0,True,True,False\n"
                "p2,stage1,unsat,20,2200.0,True,True,False,20,2400.0,True,True,False,20,2350.0,True,True,False\n",
                encoding="utf-8",
            )

            self.assertEqual(
                pda.main(
                    [
                        "export",
                        "--x64",
                        str(x64_json),
                        "--arm64",
                        str(arm64_csv),
                        "--solver-map",
                        "c4_g4_full=c4",
                        "--run-tag",
                        "g4_check",
                        "--out-dir",
                        str(out_dir),
                    ]
                ),
                0,
            )
            manifest = json.loads((out_dir / "manifest.json").read_text(encoding="utf-8"))
            self.assertEqual(manifest["solvers"], ["c0direct", "c3b", "c4"])
            self.assertEqual(manifest["summary"]["x64"]["c4"]["solved"], 1)
            self.assertEqual(manifest["summary"]["arm64"]["c4"]["solved"], 2)

            self.assertEqual(
                pda.main(["plot", "--results-dir", str(out_dir), "-o", str(svg_out)]),
                0,
            )
            assert_strict_svg_invariants(self, svg_out.read_text(encoding="utf-8"))

    def test_single_arch_plot_and_style_rejection(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            x64_json = tmp / "x64.json"
            x64_json.write_text(
                json.dumps(
                    {
                        "meta": {"timeout_s": 10.0},
                        "results": [
                            {
                                "id": "a",
                                "expected": "sat",
                                "solvers": {
                                    "c1": {"status": 10, "wall_ms": 50.0, "verdict_ok": True, "timed_out": False},
                                    "c4": {"status": 10, "wall_ms": 60.0, "verdict_ok": True, "timed_out": False},
                                },
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            svg_single = tmp / "single.svg"
            self.assertEqual(
                pda.main(["plot", "--x64", str(x64_json), "-o", str(svg_single)]),
                0,
            )
            assert_strict_svg_invariants(
                self, svg_single.read_text(encoding="utf-8"), expect_arm64_label=False
            )

            # Enforce rejection of disallowed CPU/hosting labels.
            bad_cpu = "Google A" + "xion"
            with self.assertRaises(ValueError):
                pda.main(
                    [
                        "plot",
                        "--x64",
                        str(x64_json),
                        "--arm64-cpu",
                        bad_cpu,
                        "-o",
                        str(tmp / "bad1.svg"),
                    ]
                )

            bad_host = "Bare" + "-Metal Server"
            with self.assertRaises(ValueError):
                pda.main(
                    [
                        "plot",
                        "--x64",
                        str(x64_json),
                        "--title",
                        bad_host,
                        "-o",
                        str(tmp / "bad2.svg"),
                    ]
                )

            # Verify SVG validator catches unlabeled GM/AM ratio text as well.
            bad_svg = (
                '<svg xmlns="http://www.w3.org/2000/svg">'
                '<rect width="100%" height="100%" fill="#ffffff"/>'
                '<text x="10" y="10">1.20x GM</text>'
                '<path d="M0 0h10v10" data-survival-curve="1"/>'
                "</svg>"
            )
            with self.assertRaises(ValueError):
                pda.validate_svg_document(bad_svg)


if __name__ == "__main__":
    unittest.main()
