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
        # 12 tiny leaves, 1 large straggler, 12 tiny leaves, 1 prop_lit_raw straggler, 8 leaves.
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
        # Per arch: Bounds + N slices + Cert + CertLink + Top = len(slices) + 4 (no Sound).
        self.assertEqual(len(files), 2 * (len(cfg.slices) + 4))
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
        self.assertIn("allChunks_link", cert_x64)
        self.assertIn("public section", cert_x64)
        self.assertNotIn("@[expose] public section", cert_x64)
        self.assertNotIn("LinkedCert.append", cert_x64)
        self.assertNotIn("set_option profiler", cert_x64)
        self.assertTrue(all(len(ln) <= 100 for ln in cert_x64.splitlines()))

        for arch_dir, tag in (("Amd64", "x64"), ("Arm64", "arm64")):
            link = by_path[f"LeanQbe/T/{arch_dir}/KissatM6CertLink.lean"]
            self.assertIn("fnSpec_noExit_of_legalSigAll_optInlinePolicy", link)
            self.assertIn(f"solve_{tag}_of_fnspec", link)
            expected_ax = "solve_x64_of_fnspec" if tag == "x64" else "ax_solve"
            self.assertIn(f"#print axioms {expected_ax}", link)

            top = by_path[f"LeanQbe/T/{arch_dir}/KissatM6.lean"]
            self.assertIn("public section", top)
            self.assertNotIn("@[expose] public section", top)
            self.assertIn("m6CoreEnv", top)
            self.assertIn("m6CoreEnv_moduleOk", top)
            self.assertIn("m6CoreEnv_solve_bytes_iff.mpr", top)
            self.assertIn("import LeanQbe.T.Examples.Kissat.FullM6SatNv", top)
            self.assertIn("import LeanQbe.T.Examples.Kissat.FullM6SatSound", top)
            self.assertNotIn("public import LeanQbe.T.Examples.Kissat.FullM6Sat", top)
            self.assertIn(f"m6_solve_bytes_unsat_{tag}", top)
            self.assertIn(f"m6_{tag}_unsat_nonvacuous", top)
            self.assertIn(f"m6_{tag}_run_unsat", top)
            self.assertIn("nvM6UnsatBytes", top)
            self.assertNotIn(f"LeanQbe/T/{arch_dir}/KissatM6Sound.lean", by_path)
            expected_top_ax = "kissat_m6_x64_unsat_correct" if tag == "x64" else "ax_unsat_sound"
            self.assertIn(f"#print axioms {expected_top_ax}", top)
            if tag == "arm64":
                self.assertNotIn("#print axioms kissat_m6_arm64_unsat_correct", top)

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
        self.assertEqual(tf_cfg.entry_const, "FullM6Orch.m6oSolveBytesFn")
        tf_files = gcs.build_plan(tf_cfg, ["amd64", "arm64"])
        self._assert_hygiene(tf_files)
        tf_by_path = dict(tf_files)
        for arch_dir in ("Amd64", "Arm64"):
            top = tf_by_path[f"LeanQbe/T/{arch_dir}/KissatM7.lean"]
            self.assertNotIn("m6Nv", top)
            self.assertNotRegex(top, r"\bm6Nv\w*")
            self.assertIn("def m7NvWorkLen : Nat := 6144", top)
            self.assertIn("def m7NvPayload (cnfBytes : List UInt8)", top)
            self.assertIn(
                "(by rw [m7NvPayload_length]; unfold m7NvWorkLen; decide)",
                top,
            )
            self.assertIn("region nvM6UnsatWorkPtr m7NvWorkLen", top)
            self.assertIn("heq ▸ m7NvPayload_sep nvM6UnsatBytes (by decide)", top)
            self.assertIn("FullM6Orch.m6oSolveBytesFn ∈ m7Module.fns", top)
            self.assertIn("some FullM6Orch.m6oSolveBytesFn)", top)
            snd = tf_by_path[f"LeanQbe/T/{arch_dir}/KissatM7Sound.lean"]
            self.assertNotIn("m6Nv", snd)
            self.assertIn("FullM6Orch.m6oSolveBytesFn ∈ m7Module.fns", snd)
            self.assertIn("some FullM6Orch.m6oSolveBytesFn)", snd)

        # CLI --entry-const override remains intact for FullM7.
        ov_args = gcs.parse_args(
            [
                "--module",
                "FullM7",
                "--total-fns",
                "396",
                "--entry-const",
                "FullM7Orch.m7oSolveBytesFn",
                "--root",
                str(REPO_ROOT),
                "--dry-run",
            ]
        )
        ov_cfg = gcs.build_config(ov_args)
        self.assertEqual(ov_cfg.entry_const, "FullM7Orch.m7oSolveBytesFn")
        ov_files = dict(gcs.build_plan(ov_cfg, ["amd64", "arm64"]))
        self._assert_hygiene(list(ov_files.items()))
        for arch_dir in ("Amd64", "Arm64"):
            self.assertIn(
                "FullM7Orch.m7oSolveBytesFn ∈ m7Module.fns",
                ov_files[f"LeanQbe/T/{arch_dir}/KissatM7.lean"],
            )
            self.assertIn(
                "FullM7Orch.m7oSolveBytesFn ∈ m7Module.fns",
                ov_files[f"LeanQbe/T/{arch_dir}/KissatM7Sound.lean"],
            )

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
            self.assertEqual(pr_cfg.entry_const, "FullM6Orch.m6oSolveBytesFn")
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
            for arch_dir in ("Amd64", "Arm64"):
                top = pr_files[f"LeanQbe/T/{arch_dir}/KissatM7.lean"]
                self.assertNotIn("m6Nv", top)
                self.assertNotRegex(top, r"\bm6Nv\w*")
                self.assertIn("m7NvPayload_length", top)
                self.assertIn("m7NvWorkLen", top)
                self.assertIn("m7NvPayload_sep", top)
                self.assertIn("FullM6Orch.m6oSolveBytesFn ∈ m7Module.fns", top)

    def test_full_m7_plus_preset_unsat_only(self) -> None:
        args = gcs.parse_args(
            ["--module", "FullM7Plus", "--root", str(REPO_ROOT), "--dry-run"]
        )
        cfg = gcs.build_config(args)
        self.assertEqual(cfg.prefix, "KissatM7Plus")
        self.assertEqual(cfg.total_fns, 410)
        self.assertEqual(cfg.entry_idx, 409)
        self.assertFalse(cfg.emit_sound)
        self.assertEqual(cfg.module_ok, "m7Plus_moduleOk")
        self.assertEqual(cfg.solve_spec_intro, "m7PlusSolveBytesSpec_intro")
        self.assertEqual(cfg.solve_mem_thm, "m7Plus_solveBytes_mem")
        self.assertEqual(cfg.open_source_ns, "LeanQbe.T.Examples.Kissat.FullM7Plus")
        files = dict(gcs.build_plan(cfg, ["amd64", "arm64"]))
        self._assert_hygiene(list(files.items()))
        for arch_dir in ("Amd64", "Arm64"):
            self.assertNotIn(f"LeanQbe/T/{arch_dir}/KissatM7PlusSound.lean", files)
            top = files[f"LeanQbe/T/{arch_dir}/KissatM7Plus.lean"]
            self.assertIn("m7Plus_moduleOk", top)
            self.assertIn("m7PlusSolveBytesSpec_intro", top)
            self.assertIn("m7Plus_solveBytes_mem", top)
            self.assertIn("#print axioms ax_unsat_nv", top)
            self.assertNotIn("FullM6SatSound", top)
            self.assertNotRegex(top, r"\bsat_nv\b")
            link = files[f"LeanQbe/T/{arch_dir}/KissatM7PlusCertLink.lean"]
            self.assertIn("LeanQbe.T.Examples.Kissat.FullM7Plus", link)
            self.assertNotIn("FullM7PlusAssembly", link)

    def test_full_m7_fidelity_preset_and_option_r_reuse(self) -> None:
        args = gcs.parse_args(
            ["--module", "FullM7Fidelity", "--root", str(REPO_ROOT), "--dry-run"]
        )
        cfg = gcs.build_config(args)
        self.assertEqual(cfg.prefix, "KissatM7Fidelity")
        self.assertEqual(cfg.stem, "m7Fidelity")
        self.assertEqual(cfg.total_fns, 413)
        self.assertEqual(cfg.entry_idx, 412)
        self.assertFalse(cfg.emit_sound)
        self.assertEqual(cfg.module_ok, "m7Fidelity_moduleOk")
        self.assertEqual(cfg.no_exit, "m7FidelityEnv_noExit")
        self.assertEqual(cfg.solve_spec_intro, "m7FidSolveBytesSpec_intro")
        self.assertFalse(cfg.solve_spec_has_sat)
        self.assertEqual(cfg.solve_mem_thm, "m7Fidelity_solveBytes_mem")
        self.assertTrue(all(m.source == "c0-static" for m in cfg.fn_metrics))
        files = dict(gcs.build_plan(cfg, ["amd64", "arm64"]))
        self._assert_hygiene(list(files.items()))
        for arch_dir in ("Amd64", "Arm64"):
            self.assertNotIn(f"LeanQbe/T/{arch_dir}/KissatM7FidelitySound.lean", files)
            bnds = files[f"LeanQbe/T/{arch_dir}/KissatM7FidelityBounds.lean"]
            self.assertIn("(prefixDef := m7FidelityExtPrefix)", bnds)
            self.assertNotIn("@[expose]", bnds)
            sl1 = files[f"LeanQbe/T/{arch_dir}/KissatM7FidelityCert1.lean"]
            self.assertIn("abbrev slice1Mod : Module :=", sl1)
            self.assertNotIn("@[expose]", sl1)
            top = files[f"LeanQbe/T/{arch_dir}/KissatM7Fidelity.lean"]
            self.assertIn("m7FidSolveBytesSpec_intro", top)
            self.assertIn("(fun _ _ hdom hu _ hm' =>", top)
            self.assertIn("#print axioms ax_run_unsat", top)
            self.assertNotIn("FullM6SatSound", top)
            self.assertNotIn("@[expose]", top)

        with tempfile.TemporaryDirectory() as tmp:
            p_path = Path(tmp) / "prof.json"
            rows = [
                {
                    "index": i,
                    "name": f"fn_{i}",
                    "ir_size": 450 if i in (5, 35) else 80,
                    "jnz": 100,
                    "defer": 100,
                }
                for i in range(40)
            ]
            p_path.write_text(json.dumps(rows), encoding="utf-8")
            r_path = Path(tmp) / "reuse.json"
            r_path.write_text(
                json.dumps(
                    {
                        "reuse_prefix": "KissatM7Plus",
                        "reuse_inl_mod": "LeanQbe.T.Examples.Kissat.FullM7PlusInl",
                        "reuse_inl_fns": "m7PlusInlFns",
                        "reused_slices": [{"src_index": 2, "start": 12, "count": 12}],
                    }
                ),
                encoding="utf-8",
            )
            r_args = gcs.parse_args(
                [
                    "--module",
                    "FullM7Fidelity",
                    "--total-fns",
                    "40",
                    "--profile",
                    str(p_path),
                    "--reuse-spec",
                    str(r_path),
                    "--singleton-size",
                    "400",
                    "--max-slice-size",
                    "650",
                    "--max-slice-count",
                    "10",
                    "--root",
                    str(REPO_ROOT),
                    "--dry-run",
                ]
            )
            r_cfg = gcs.build_config(r_args)
            r_files = dict(gcs.build_plan(r_cfg, ["amd64", "arm64"]))
            self._assert_hygiene(list(r_files.items()))
            cert = r_files["LeanQbe/T/Amd64/KissatM7FidelityCert.lean"]
            self.assertIn("public import LeanQbe.T.Amd64.KissatM7PlusCert2", cert)
            self.assertIn("KissatM7PlusCert2.cert2.chunks", cert)
            self.assertIn("private theorem reuse_eq", cert)
            self.assertNotIn("open LeanQbe.T.Amd64.KissatM7FidelityCert1", cert)

            # Bridged reuse mode emits bridge import and theorem calls, no inline reuse_eq.
            b_path = Path(tmp) / "reuse_bridge.json"
            b_path.write_text(
                json.dumps(
                    {
                        "reuse_prefix": "KissatM7Plus",
                        "reuse_inl_mod": "LeanQbe.T.Examples.Kissat.FullM7PlusInl",
                        "reuse_inl_fns": "m7PlusInlFns",
                        "reuse_bridge_mod": (
                            "LeanQbe.T.Examples.Kissat.FullM7FidelityM7PlusBridge"
                        ),
                        "reuse_thm_prefix": "reuse_m7p_eq_",
                        "reused_slices": [{"src_index": 2, "start": 12, "count": 12}],
                    }
                ),
                encoding="utf-8",
            )
            b_args = gcs.parse_args(
                [
                    "--module",
                    "FullM7Fidelity",
                    "--total-fns",
                    "40",
                    "--profile",
                    str(p_path),
                    "--reuse-spec",
                    str(b_path),
                    "--singleton-size",
                    "400",
                    "--max-slice-size",
                    "650",
                    "--max-slice-count",
                    "10",
                    "--root",
                    str(REPO_ROOT),
                    "--dry-run",
                ]
            )
            b_cfg = gcs.build_config(b_args)
            b_files = dict(gcs.build_plan(b_cfg, ["amd64", "arm64"]))
            self._assert_hygiene(list(b_files.items()))
            b_cert = b_files["LeanQbe/T/Amd64/KissatM7FidelityCert.lean"]
            self.assertIn(
                "public import LeanQbe.T.Examples.Kissat.FullM7FidelityM7PlusBridge",
                b_cert,
            )
            self.assertIn("← reuse_m7p_eq_2]", b_cert)
            self.assertNotIn("private theorem reuse_eq", b_cert)

            # Pruned-relink mode via CLI flag emits eval_raw_callees! + relinkChunkListCover.
            p_args = gcs.parse_args(
                [
                    "--module",
                    "FullM7Fidelity",
                    "--total-fns",
                    "40",
                    "--profile",
                    str(p_path),
                    "--reuse-spec",
                    str(b_path),
                    "--reuse-mode",
                    "pruned_relink",
                    "--singleton-size",
                    "400",
                    "--max-slice-size",
                    "650",
                    "--max-slice-count",
                    "10",
                    "--root",
                    str(REPO_ROOT),
                    "--dry-run",
                ]
            )
            p_cfg = gcs.build_config(p_args)
            self.assertEqual(p_cfg.reuse_mode, "pruned_relink")
            p_files = dict(gcs.build_plan(p_cfg, ["amd64", "arm64"]))
            self._assert_hygiene(list(p_files.items()))
            for arch_dir in ("Amd64", "Arm64"):
                p_cert = p_files[f"LeanQbe/T/{arch_dir}/KissatM7FidelityCert.lean"]
                self.assertIn("public import LeanQbe.T.MainLinkReuseCover", p_cert)
                self.assertIn("meta import LeanQbe.T.MainLinkReuseElab", p_cert)
                self.assertIn("eval_raw_callees! rCallees", p_cert)
                self.assertIn("eval_pruned_ext! rExt", p_cert)
                self.assertIn("calleesCover_of_checkRaw", p_cert)
                self.assertIn("relinkChunkListCover", p_cert)
                self.assertIn("relinkChunkListCover_fns", p_cert)
                self.assertIn("relinkChunkListCover_maxBound", p_cert)
                self.assertIn("private theorem reuseBaseFns_wf", p_cert)

            # JSON-configured pruned_relink with custom proof module & src_start works.
            pr_path = Path(tmp) / "reuse_pruned.json"
            pr_path.write_text(
                json.dumps(
                    {
                        "reuse_prefix": "KissatM7Plus",
                        "reuse_mode": "pruned_relink",
                        "reuse_inl_mod": "LeanQbe.T.Examples.Kissat.FullM7PlusInl",
                        "reuse_inl_fns": "m7PlusInlFns",
                        "reuse_inl_mod_sym": "m7PlusInlMod",
                        "reuse_inl_policy": "m7InlPolicy",
                        "reuse_proof_mod": "LeanQbe.T.Examples.Kissat.FullM7PlusAssemblyProof0",
                        "reuse_proof_ns": "LeanQbe.T.Examples.Kissat.FullM7Plus",
                        "reuse_acyclic": "m7Plus_acyclic",
                        "reuse_wf": "m7PlusFns_wf",
                        "reused_slices": [
                            {"src_index": 2, "start": 12, "src_start": 10, "count": 12}
                        ],
                    }
                ),
                encoding="utf-8",
            )
            pr_args = gcs.parse_args(
                [
                    "--module",
                    "FullM7Fidelity",
                    "--total-fns",
                    "40",
                    "--profile",
                    str(p_path),
                    "--reuse-spec",
                    str(pr_path),
                    "--singleton-size",
                    "400",
                    "--max-slice-size",
                    "650",
                    "--max-slice-count",
                    "10",
                    "--root",
                    str(REPO_ROOT),
                    "--dry-run",
                ]
            )
            pr_cfg = gcs.build_config(pr_args)
            pr_files = dict(gcs.build_plan(pr_cfg, ["amd64", "arm64"]))
            self._assert_hygiene(list(pr_files.items()))
            pr_cert = pr_files["LeanQbe/T/Amd64/KissatM7FidelityCert.lean"]
            self.assertIn("(m7PlusInlFns.drop 10).take 12", pr_cert)
            self.assertIn("FullM7PlusAssemblyProof0", pr_cert)
            self.assertIn("m7Plus_acyclic m7PlusFns_wf", pr_cert)

            bad_args = gcs.parse_args(
                [
                    "--module",
                    "FullM7Fidelity",
                    "--reuse-mode",
                    "pruned_relink",
                    "--root",
                    str(REPO_ROOT),
                    "--dry-run",
                ]
            )
            with self.assertRaises(ValueError):
                gcs.build_config(bad_args)

    def test_opt_in_cert_style_slices_and_abi_common_standalone_m8(self) -> None:
        # Standalone M8 simulation via explicit opt-in `--cert-style slices --abi-common`.
        args = gcs.parse_args(
            [
                "--prefix",
                "KissatM8",
                "--stem",
                "m8",
                "--source-mod",
                "LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly",
                "--source-ns",
                "LeanQbe.T.Examples.Kissat.FullM7Fidelity",
                "--proof-mod",
                "LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof",
                "--proof-ns",
                "LeanQbe.T.Examples.Kissat.FullM7Fidelity",
                "--inl-mod",
                "LeanQbe.T.Examples.Kissat.FullM7FidelityInl",
                "--inl-policy-mod",
                "LeanQbe.T.Examples.Kissat.FullM7InlPolicy",
                "--inl-fns",
                "m8InlFns",
                "--inl-mod-sym",
                "m8InlMod",
                "--inl-policy",
                "m7InlPolicy",
                "--fns",
                "m8Fns",
                "--mod",
                "m8Module",
                "--env",
                "m8Env",
                "--module-ok",
                "m8_moduleOk",
                "--no-exit",
                "m8Env_noExit",
                "--entry-const",
                "FullM6Orch.m6oSolveBytesFn",
                "--solve-spec-intro",
                "m7FidSolveBytesSpec_intro",
                "--solve-spec-no-sat",
                "--solve-mem-thm",
                "m8_solveBytes_mem",
                "--hdr-model",
                "m6",
                "--no-sound",
                "--sat-sound-mod",
                "",
                "--total-fns",
                "415",
                "--cert-style",
                "slices",
                "--abi-common",
                "--fns-length-thm",
                "m8InlFns_length",
                "--max-dirs",
                "600",
                "--root",
                str(REPO_ROOT),
                "--dry-run",
            ]
        )
        cfg = gcs.build_config(args)
        self.assertEqual(cfg.cert_style, "slices")
        self.assertTrue(cfg.abi_common)
        self.assertEqual(cfg.fns_length_thm, "m8InlFns_length")
        files = dict(gcs.build_plan(cfg, ["amd64", "arm64"]))
        self._assert_hygiene(list(files.items()))

        ladder_args = gcs.parse_args(
            [
                "--prefix",
                "KissatM8",
                "--stem",
                "m8",
                "--source-mod",
                "LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly",
                "--source-ns",
                "LeanQbe.T.Examples.Kissat.FullM7Fidelity",
                "--proof-mod",
                "LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof",
                "--proof-ns",
                "LeanQbe.T.Examples.Kissat.FullM7Fidelity",
                "--inl-mod",
                "LeanQbe.T.Examples.Kissat.FullM7FidelityInl",
                "--inl-policy-mod",
                "LeanQbe.T.Examples.Kissat.FullM7InlPolicy",
                "--inl-fns",
                "m8InlFns",
                "--inl-mod-sym",
                "m8InlMod",
                "--inl-policy",
                "m7InlPolicy",
                "--fns",
                "m8Fns",
                "--mod",
                "m8Module",
                "--env",
                "m8Env",
                "--module-ok",
                "m8_moduleOk",
                "--no-exit",
                "m8Env_noExit",
                "--entry-const",
                "FullM6Orch.m6oSolveBytesFn",
                "--solve-spec-intro",
                "m7FidSolveBytesSpec_intro",
                "--solve-spec-no-sat",
                "--solve-mem-thm",
                "m8_solveBytes_mem",
                "--hdr-model",
                "m6",
                "--no-sound",
                "--sat-sound-mod",
                "",
                "--total-fns",
                "415",
                "--cert-style",
                "ladder",
                "--max-dirs",
                "600",
                "--root",
                str(REPO_ROOT),
                "--dry-run",
            ]
        )
        ladder_files = dict(gcs.build_plan(gcs.build_config(ladder_args), ["amd64", "arm64"]))

        for arch_dir, abi_const, tag in (
            ("Amd64", "x64KissatAbi", "x64"),
            ("Arm64", "arm64KissatAbi", "arm64"),
        ):
            cert = files[f"LeanQbe/T/{arch_dir}/KissatM8Cert.lean"]
            ladder_cert = ladder_files[f"LeanQbe/T/{arch_dir}/KissatM8Cert.lean"]
            self.assertIn("public import LeanQbe.T.MainCertSlices", cert)
            self.assertIn("public import LeanQbe.T.MainCertInline", cert)
            self.assertIn("ChunkSlice.ofCert", cert)
            self.assertIn("ChunkSlice.ofDrop", cert)
            self.assertIn("LinkedCert.ofChunkSlices", cert)
            self.assertIn("m8InlFns_length", cert)
            self.assertIn("allSlices_link", cert)
            self.assertIn("m8InlCert.castModule m8InlMod.eq", cert)
            self.assertIn("#print axioms m8Cert", cert)
            self.assertNotIn("sufChunks", cert)
            self.assertNotIn("private theorem fns_eq", cert)
            self.assertNotIn("private theorem maxB", cert)
            self.assertLess(len(cert.splitlines()), len(ladder_cert.splitlines()))

            link = files[f"LeanQbe/T/{arch_dir}/KissatM8CertLink.lean"]
            ladder_link = ladder_files[f"LeanQbe/T/{arch_dir}/KissatM8CertLink.lean"]
            self.assertIn("public import LeanQbe.T.Examples.Kissat.KissatCertCommon", link)
            self.assertIn(f"import LeanQbe.T.{arch_dir}.KissatAbi", link)
            self.assertIn("KissatCertCommon.solve_of_abi_fnspec", link)
            self.assertIn(abi_const, link)
            self.assertIn(f"solve_{tag}_of_fnspec", link)
            self.assertIn("#print axioms", link)
            self.assertLess(len(link.splitlines()), len(ladder_link.splitlines()))

            top = files[f"LeanQbe/T/{arch_dir}/KissatM8.lean"]
            ladder_top = ladder_files[f"LeanQbe/T/{arch_dir}/KissatM8.lean"]
            self.assertIn("public import LeanQbe.T.Examples.Kissat.KissatCertCommon", top)
            self.assertIn(f"import LeanQbe.T.{arch_dir}.KissatAbi", top)
            self.assertIn("private def m8UnsatPkg : KissatUnsatPkg where", top)
            self.assertIn("m6NvWorkLen", top)
            self.assertIn("m6NvPayload", top)
            self.assertIn("KissatCertCommon.module_fnspec_of_abi", top)
            self.assertIn("KissatCertCommon.solve_bytes_unsat_of_abi", top)
            self.assertIn("KissatCertCommon.unsat_correct_of_abi", top)
            self.assertIn("KissatCertCommon.unsat_nonvacuous_of_abi", top)
            self.assertIn("KissatCertCommon.run_unsat_of_abi", top)
            self.assertNotIn("def m8NvWorkLen", top)
            self.assertNotIn("def m8NvPayload", top)
            self.assertNotIn("theorem sep_exists_eq", top)
            self.assertIn(f"#print axioms m8_{tag}_run_unsat", top)
            self.assertLess(len(top.splitlines()), len(ladder_top.splitlines()))

            self.assertNotIn(f"LeanQbe/T/{arch_dir}/KissatM8Sound.lean", files)

        # Single-slice uninlined `--cert-style slices` uses ChunkSlice.ofDrop directly.
        single_args = gcs.parse_args(
            [
                "--module",
                "FullM5",
                "--cert-style",
                "slices",
                "--slice-sizes",
                ",".join(["12"] * 19 + ["6"]),
                "--root",
                str(REPO_ROOT),
                "--dry-run",
            ]
        )
        single_cfg = gcs.build_config(single_args)
        single_files = dict(gcs.build_plan(single_cfg, ["amd64"]))
        self._assert_hygiene(list(single_files.items()))
        m5_cert = single_files["LeanQbe/T/Amd64/KissatM5Cert.lean"]
        self.assertIn("ChunkSlice.ofDrop", m5_cert)
        self.assertIn("m5Fns_length", m5_cert)
        self.assertIn("LinkedCert.ofChunkSlices", m5_cert)
        self.assertNotIn("sufChunks", m5_cert)

        # Fail closed when `--abi-common` is requested without m6 hdr model or inlined module.
        bad_abi_args = gcs.parse_args(
            [
                "--module",
                "FullM5",
                "--abi-common",
                "--root",
                str(REPO_ROOT),
                "--dry-run",
            ]
        )
        with self.assertRaises(ValueError):
            gcs.build_config(bad_abi_args)


if __name__ == "__main__":
    unittest.main()
