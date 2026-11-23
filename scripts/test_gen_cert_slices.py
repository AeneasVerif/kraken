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

    def test_full_m6_preset_chunked_inl_and_m6hdr_soundness(self) -> None:
        args = gcs.parse_args(["--module", "FullM6", "--root", str(REPO_ROOT), "--dry-run"])
        cfg = gcs.build_config(args)
        self.assertEqual(cfg.prefix, "KissatM6")
        self.assertEqual(cfg.stem, "m6")
        self.assertEqual(cfg.total_fns, 382)
        self.assertEqual(cfg.max_dirs, 600)
        self.assertTrue(cfg.is_inlined)
        self.assertEqual(cfg.inl_mod, "LeanQbe.T.Examples.Kissat.FullM6Inl")
        self.assertEqual(cfg.inl_fns, "m6InlFns")
        self.assertEqual(cfg.inl_mod_sym, "m6InlMod")
        self.assertEqual(cfg.inl_policy, "m6InlPolicy")
        self.assertEqual(cfg.hdr_model, "m6")
        self.assertTrue(all(m.source == "c0-static" for m in cfg.fn_metrics))
        self.assertLess(cfg.after_stats.cost_max_mean, cfg.before_stats.cost_max_mean)
        sing_names = {nm for _, nm, _ in cfg.after_stats.singletons}
        self.assertIn("full_arena_sweep_m6", sing_names)

        files = gcs.build_plan(cfg, ["amd64", "arm64"])
        # Per arch: Bounds + N slices + Cert + CertLink + Top + Sound = len(slices) + 5.
        self.assertEqual(len(files), 2 * (len(cfg.slices) + 5))
        self._assert_hygiene(files)

        by_path = dict(files)
        bounds_x64 = by_path["LeanQbe/T/Amd64/KissatM6Bounds.lean"]
        self.assertIn("public import LeanQbe.T.Examples.Kissat.FullM6Inl", bounds_x64)
        self.assertIn("eval_prefix_ext! m6AllExt x64Target x64LegalTarget m6InlFns", bounds_x64)

        slice1 = by_path["LeanQbe/T/Amd64/KissatM6Cert1.lean"]
        self.assertIn("public import LeanQbe.T.Examples.Kissat.FullM6Inl", slice1)
        self.assertIn("(maxDirs := 600)", slice1)

        cert_x64 = by_path["LeanQbe/T/Amd64/KissatM6Cert.lean"]
        self.assertIn("public import LeanQbe.T.MainCertInline", cert_x64)
        self.assertIn("(m6Module.optInlinePolicy m6InlPolicy)", cert_x64)
        self.assertIn("m6InlCert.castModule m6InlMod.eq", cert_x64)

        for arch_dir, tag in (("Amd64", "x64"), ("Arm64", "arm64")):
            link = by_path[f"LeanQbe/T/{arch_dir}/KissatM6CertLink.lean"]
            self.assertIn("fnSpec_noExit_of_legalSigAll_optInlinePolicy", link)
            self.assertIn(f"solve_{tag}_of_fnspec", link)
            expected_ax = "solve_x64_of_fnspec" if tag == "x64" else "ax_solve"
            self.assertIn(f"#print axioms {expected_ax}", link)

            top = by_path[f"LeanQbe/T/{arch_dir}/KissatM6.lean"]
            self.assertIn("public import LeanQbe.T.Examples.Kissat.FullM6SatNv", top)
            self.assertIn("public import LeanQbe.T.Examples.Kissat.FullM6SatSound", top)
            self.assertIn(f"m6_solve_bytes_unsat_{tag}", top)
            self.assertIn(f"m6_{tag}_unsat_nonvacuous", top)
            self.assertIn(f"m6_{tag}_run_unsat", top)
            self.assertIn("nvM6UnsatBytes", top)

            snd = by_path[f"LeanQbe/T/{arch_dir}/KissatM6Sound.lean"]
            self.assertIn("readModelFromWorkM6", snd)
            self.assertIn(f"m6_solve_bytes_model_{tag}", snd)
            self.assertIn(f"m6_solve_bytes_sound_{tag}", snd)
            self.assertIn(f"m6_{tag}_sat_nonvacuous", snd)
            self.assertIn(f"m6_{tag}_run_sat", snd)
            self.assertIn("nvM6SatBytes", snd)
            opp = "Arm64" if arch_dir == "Amd64" else "Amd64"
            self.assertNotIn(f"LeanQbe.T.{opp}", snd)

    def test_full_m7_preset_with_profile_and_total_fns(self) -> None:
        # Without FullM7.lean, --total-fns, or --profile, FullM7 fails closed.
        missing_args = gcs.parse_args(["--module", "FullM7", "--root", str(REPO_ROOT), "--dry-run"])
        with self.assertRaises(ValueError):
            gcs.build_config(missing_args)

        # Explicit --total-fns 396 works cleanly with FullM7Inl + maxDirs=600 + M6Hdr wrappers.
        tf_args = gcs.parse_args(
            ["--module", "FullM7", "--total-fns", "396", "--root", str(REPO_ROOT), "--dry-run"]
        )
        tf_cfg = gcs.build_config(tf_args)
        self.assertEqual(tf_cfg.prefix, "KissatM7")
        self.assertEqual(tf_cfg.stem, "m7")
        self.assertEqual(tf_cfg.max_dirs, 600)
        self.assertEqual(tf_cfg.inl_mod, "LeanQbe.T.Examples.Kissat.FullM7Inl")
        self.assertEqual(tf_cfg.hdr_model, "m6")
        tf_files = gcs.build_plan(tf_cfg, ["amd64", "arm64"])
        self._assert_hygiene(tf_files)

        with tempfile.TemporaryDirectory() as tmp:
            p_path = Path(tmp) / "m7_probe.json"
            rows = [
                {
                    "index": i,
                    "name": (
                        "full_arena_sweep_m6"
                        if i == 102
                        else "full_cong_eval_gate"
                        if i == 251
                        else f"m7_fn_{i}"
                    ),
                    "mid_tflat_size": 1061 if i == 102 else (2400 if i == 251 else 65),
                    "mid_loops": 6 if i in (102, 251) else 1,
                    "mid_groups": 30 if i == 102 else (45 if i == 251 else 3),
                    "mid_calls": 5 if i == 102 else 1,
                }
                for i in range(396)
            ]
            p_path.write_text(json.dumps(rows), encoding="utf-8")
            pr_args = gcs.parse_args(
                [
                    "--module",
                    "FullM7",
                    "--profile",
                    str(p_path),
                    "--root",
                    str(REPO_ROOT),
                    "--dry-run",
                ]
            )
            pr_cfg = gcs.build_config(pr_args)
            self.assertEqual(pr_cfg.total_fns, 396)
            sing_names = {nm for _, nm, _ in pr_cfg.after_stats.singletons}
            self.assertIn("full_arena_sweep_m6", sing_names)
            self.assertIn("full_cong_eval_gate", sing_names)
            pr_files = dict(gcs.build_plan(pr_cfg, ["amd64", "arm64"]))
            self._assert_hygiene(list(pr_files.items()))
            self.assertIn(
                "m7InlCert.castModule m7InlMod.eq",
                pr_files["LeanQbe/T/Arm64/KissatM7Cert.lean"],
            )
            self.assertIn("readModelFromWorkM6", pr_files["LeanQbe/T/Arm64/KissatM7Sound.lean"])


if __name__ == "__main__":
    unittest.main()
