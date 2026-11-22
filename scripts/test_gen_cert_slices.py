#!/usr/bin/env python3
"""Unit tests for `scripts/gen_cert_slices.py` autobalancing, presets, and hygiene."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gen_cert_slices as gcs  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parent.parent


class GenCertSlicesTest(unittest.TestCase):
    """Covers LPT bin packing, straggler isolation, `FullM5`, and Lean invariants."""

    def _assert_hygiene(self, files: list[tuple[str, str]]) -> None:
        gcs.validate_generated_files(files)
        for rel, content in files:
            lines = content.splitlines()
            self.assertEqual(lines[0], "module", f"{rel}: missing module header")
            self.assertIn("set_option autoImplicit false", content, rel)
            self.assertLessEqual(len(lines), gcs.MAX_FILE_LINES, rel)
            self.assertNotIn("import all ", content, rel)
            for ln in lines:
                self.assertLessEqual(len(ln), gcs.MAX_LINE_LEN, f"{rel}: {ln}")

    def test_lpt_pack_balances_workers(self) -> None:
        weights = [700.0, 600.0, 500.0, 400.0, 300.0, 200.0, 200.0, 100.0]
        sched = gcs.lpt_pack(weights, workers=4)
        self.assertEqual(sched.workers, 4)
        self.assertAlmostEqual(sum(sched.loads), sum(weights))
        self.assertEqual(sum(len(b) for b in sched.bins), len(weights))
        self.assertLessEqual(sched.makespan, 800.0)
        self.assertLess(sched.max_mean_ratio, 1.15)

    def test_autobalance_isolates_stragglers_and_packs_leaves(self) -> None:
        # 12 tiny leaves, 1 massive straggler, 12 tiny leaves, 1 prop_lit_raw straggler, 8 leaves.
        metrics: list[gcs.FnMetric] = []
        idx = 0
        for k in range(12):
            metrics.append(gcs.FnMetric(idx, f"leaf_a_{k}", 30, 0, 1, 0, 35.0, "test"))
            idx += 1
        metrics.append(gcs.FnMetric(idx, "full_cong_work_step", 720, 7, 73, 25, 1850.0, "test"))
        idx += 1
        for k in range(12):
            metrics.append(gcs.FnMetric(idx, f"leaf_b_{k}", 35, 0, 1, 0, 42.0, "test"))
            idx += 1
        metrics.append(gcs.FnMetric(idx, "full_prop_lit_raw", 530, 6, 29, 1, 1050.0, "test"))
        idx += 1
        for k in range(8):
            metrics.append(gcs.FnMetric(idx, f"leaf_c_{k}", 40, 0, 1, 0, 48.0, "test"))
            idx += 1

        tup = tuple(metrics)
        uniform = gcs.compute_slices(len(tup), 12, None)
        balanced = gcs.autobalance_slices(tup, slice_size=12, workers=8)
        self.assertEqual(sum(s.count for s in balanced), len(tup))
        for s in balanced:
            self.assertTrue(1 <= s.count <= gcs.MAX_SLICE_SIZE)

        sing_names = {tup[s.start].name for s in balanced if s.count == 1}
        self.assertIn("full_cong_work_step", sing_names)
        self.assertIn("full_prop_lit_raw", sing_names)

        # Tiny leaf block [0, 12) must remain tightly packed.
        self.assertEqual((balanced[0].start, balanced[0].count), (0, 12))

        bef = gcs.compute_slice_stats(tup, uniform, workers=8)
        aft = gcs.compute_slice_stats(tup, balanced, workers=8)
        self.assertLess(aft.cost_max, bef.cost_max)
        self.assertLess(aft.lpt.makespan, bef.lpt.makespan)
        bef_w3 = gcs.compute_slice_stats(tup, uniform, workers=3)
        aft_w3 = gcs.compute_slice_stats(tup, balanced, workers=3)
        self.assertLess(aft_w3.lpt.max_mean_ratio, bef_w3.lpt.max_mean_ratio)

    def test_profile_json_and_full_m3_m4_presets(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            p_path = Path(tmp) / "probe.json"
            rows = [
                {
                    "index": i,
                    "name": (
                        "full_cong_work_step"
                        if i == 150
                        else "full_prop_lit_raw"
                        if i == 47
                        else f"fn_{i}"
                    ),
                    "mid_tflat_size": 704 if i == 150 else (533 if i == 47 else 60),
                    "mid_loops": 7 if i in (47, 150) else 1,
                    "mid_groups": 73 if i == 150 else (29 if i == 47 else 3),
                    "mid_calls": 25 if i == 150 else 1,
                }
                for i in range(204)
            ]
            p_path.write_text(json.dumps(rows), encoding="utf-8")
            args = gcs.parse_args(
                ["--module", "FullM3", "--profile", str(p_path), "--root", str(REPO_ROOT), "--dry-run"]
            )
            cfg = gcs.build_config(args)
            self.assertEqual(cfg.prefix, "KissatM3")
            self.assertEqual(cfg.stem, "m3")
            self.assertEqual(cfg.total_fns, 204)
            self.assertLess(cfg.after_stats.cost_max_mean, cfg.before_stats.cost_max_mean)
            sing_names = {nm for _, nm, _ in cfg.after_stats.singletons}
            self.assertIn("full_cong_work_step", sing_names)
            self.assertIn("full_prop_lit_raw", sing_names)

            files = gcs.build_plan(cfg, ["amd64", "arm64"])
            self._assert_hygiene(files)

    def test_full_m5_preset_and_s1_s2_invariants(self) -> None:
        args = gcs.parse_args(
            ["--module", "FullM5", "--target-slices", "27", "--root", str(REPO_ROOT), "--dry-run"]
        )
        cfg = gcs.build_config(args)
        self.assertEqual(cfg.prefix, "KissatM5")
        self.assertEqual(cfg.stem, "m5")
        self.assertEqual(cfg.source_mod, "LeanQbe.T.Examples.Kissat.FullM5")
        self.assertEqual(cfg.proof_mod, "LeanQbe.T.Examples.Kissat.FullM5Proof")
        self.assertEqual(cfg.hub_mod, "LeanQbe.T.Examples.Kissat.M5Hub")
        self.assertEqual(cfg.fns, "m5Fns")
        self.assertEqual(cfg.mod, "m5Module")
        self.assertEqual(cfg.cert_name, "m5Cert")
        self.assertEqual(len(cfg.slices), 27)
        files = gcs.build_plan(cfg, ["amd64", "arm64"])
        # 27 slices + Bounds + Cert + CertLink + Top = 31/arch => 62 dual-arch files.
        self.assertEqual(len(files), 62)
        self._assert_hygiene(files)

        by_path = dict(files)
        slice1 = by_path["LeanQbe/T/Amd64/KissatM5Cert1.lean"]
        self.assertIn("public import LeanQbe.T.MainCertCore", slice1)
        self.assertIn("meta import LeanQbe.T.MainCertElab", slice1)

        cert_x64 = by_path["LeanQbe/T/Amd64/KissatM5Cert.lean"]
        self.assertIn("public import LeanQbe.T.MainCertProof", cert_x64)
        self.assertIn("noncomputable def m5Cert", cert_x64)
        self.assertIn("#print axioms m5Cert", cert_x64)

        link_arm = by_path["LeanQbe/T/Arm64/KissatM5CertLink.lean"]
        self.assertIn("theorem ax_solve", link_arm)
        self.assertIn("#print axioms ax_solve", link_arm)
        self.assertNotIn("#print axioms solve_arm64_of_fnspec", link_arm)

        top_arm = by_path["LeanQbe/T/Arm64/KissatM5.lean"]
        self.assertIn("@[reducible] noncomputable def kissatM5_compiled_arm64", top_arm)
        self.assertIn("theorem ax_unsat_sound", top_arm)
        self.assertIn("#print axioms ax_unsat_sound", top_arm)
        self.assertNotIn("#print axioms m5_solve_bytes_unsat_sound_arm64", top_arm)

    def test_static_repo_resolution_matches_m3_and_m4(self) -> None:
        m3_args = gcs.parse_args(["--module", "FullM3", "--root", str(REPO_ROOT), "--dry-run"])
        m3_cfg = gcs.build_config(m3_args)
        self.assertEqual(m3_cfg.total_fns, 204)
        self.assertLess(m3_cfg.after_stats.cost_max_mean, m3_cfg.before_stats.cost_max_mean)
        self._assert_hygiene(gcs.build_plan(m3_cfg, ["amd64", "arm64"]))

        m4_args = gcs.parse_args(["--module", "FullM4", "--root", str(REPO_ROOT), "--dry-run"])
        m4_cfg = gcs.build_config(m4_args)
        self.assertEqual(m4_cfg.total_fns, 231)
        self.assertLess(m4_cfg.after_stats.cost_max_mean, m4_cfg.before_stats.cost_max_mean)
        self._assert_hygiene(gcs.build_plan(m4_cfg, ["amd64", "arm64"]))

    def test_max_bound_mismatched_profile_and_nonpositive_target_slices(self) -> None:
        # 1. --max-bound != 2048 must match LinkedCert ... [] [] 0 <maxBound> in <Prefix>.lean.
        mb_args = gcs.parse_args(
            [
                "--module",
                "FullM5",
                "--max-bound",
                "4096",
                "--target-slices",
                "27",
                "--root",
                str(REPO_ROOT),
                "--dry-run",
            ]
        )
        mb_cfg = gcs.build_config(mb_args)
        mb_files = dict(gcs.build_plan(mb_cfg, ["amd64"]))
        self._assert_hygiene(list(mb_files.items()))
        self.assertIn("m5Cert :", mb_files["LeanQbe/T/Amd64/KissatM5Cert.lean"])
        self.assertIn("m5Module [] [] 0 4096 :=", mb_files["LeanQbe/T/Amd64/KissatM5Cert.lean"])
        self.assertIn("m5Module [] [] 0 4096 :=", mb_files["LeanQbe/T/Amd64/KissatM5.lean"])

        # 2. Mismatched --profile length must fail closed against known module counts.
        with tempfile.TemporaryDirectory() as tmp:
            bad_prof = Path(tmp) / "short_10.json"
            rows = [
                {"index": i, "name": f"fn_{i}", "mid_tflat_size": 50}
                for i in range(10)
            ]
            bad_prof.write_text(json.dumps(rows), encoding="utf-8")
            for mod in ("Plain", "FullM5"):
                bad_args = gcs.parse_args(
                    [
                        "--module",
                        mod,
                        "--profile",
                        str(bad_prof),
                        "--root",
                        str(REPO_ROOT),
                        "--dry-run",
                    ]
                )
                with self.assertRaises(ValueError):
                    gcs.build_config(bad_args)

        # 3. Non-positive --target-slices must fail with ValueError.
        for bad_k in (0, -3):
            with self.assertRaises(ValueError):
                gcs.autobalance_slices(mb_cfg.fn_metrics, target_slices=bad_k)
            bad_k_args = gcs.parse_args(
                [
                    "--module",
                    "FullM5",
                    "--target-slices",
                    str(bad_k),
                    "--root",
                    str(REPO_ROOT),
                    "--dry-run",
                ]
            )
            with self.assertRaises(ValueError):
                gcs.build_config(bad_k_args)


if __name__ == "__main__":
    unittest.main()
