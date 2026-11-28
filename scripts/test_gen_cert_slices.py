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
    """Covers LPT bin packing, straggler isolation, live presets, and Lean invariants."""

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

    def test_retired_legacy_presets_rejected(self) -> None:
        for dead in (
            "Full", "FullFast", "FullFastSched", "FullM3", "FullM4",
            "FullM5", "FullM6", "FullM7", "FullM7Plus", "FullM7Fidelity",
        ):
            self.assertNotIn(dead, gcs.MODULE_PRESETS)
            with self.assertRaises(ValueError):
                gcs.resolve_preset(dead)

    def test_profile_json_and_plain_preset(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            p_path = Path(tmp) / "probe.json"
            rows = [
                {
                    "index": i,
                    "name": (
                        "plain_sweep"
                        if i == 30
                        else "plain_shrink_blk"
                        if i == 47
                        else f"fn_{i}"
                    ),
                    "mid_tflat_size": 704 if i == 30 else (533 if i == 47 else 60),
                    "mid_loops": 7 if i in (30, 47) else 1,
                    "mid_groups": 73 if i == 30 else (29 if i == 47 else 3),
                    "mid_calls": 25 if i == 30 else 1,
                }
                for i in range(59)
            ]
            p_path.write_text(json.dumps(rows), encoding="utf-8")
            args = gcs.parse_args(
                ["--module", "Plain", "--profile", str(p_path), "--root", str(REPO_ROOT), "--dry-run"]
            )
            cfg = gcs.build_config(args)
            self.assertEqual(cfg.prefix, "KissatPlain")
            self.assertEqual(cfg.stem, "plain")
            self.assertEqual(cfg.total_fns, 59)
            self.assertLess(cfg.after_stats.cost_max_mean, cfg.before_stats.cost_max_mean)
            sing_names = {nm for _, nm, _ in cfg.after_stats.singletons}
            self.assertIn("plain_sweep", sing_names)
            self.assertIn("plain_shrink_blk", sing_names)

            files = gcs.build_plan(cfg, ["amd64", "arm64"])
            self._assert_hygiene(files)

    def test_plain_preset_and_s1_s2_invariants(self) -> None:
        args = gcs.parse_args(
            ["--module", "Plain", "--target-slices", "6", "--root", str(REPO_ROOT), "--dry-run"]
        )
        cfg = gcs.build_config(args)
        self.assertEqual(cfg.prefix, "KissatPlain")
        self.assertEqual(cfg.stem, "plain")
        self.assertEqual(cfg.source_mod, "LeanQbe.T.Examples.Kissat.Plain")
        self.assertEqual(cfg.proof_mod, "LeanQbe.T.Examples.Kissat.PlainLemmas")
        self.assertEqual(cfg.fns, "plainFns")
        self.assertEqual(cfg.mod, "plainModule")
        self.assertEqual(cfg.cert_name, "plainCert")
        self.assertEqual(len(cfg.slices), 6)
        files = gcs.build_plan(cfg, ["amd64", "arm64"])
        # 6 slices + Bounds + Cert + CertLink + Top = 10/arch => 20 dual-arch files.
        self.assertEqual(len(files), 20)
        self._assert_hygiene(files)

        by_path = dict(files)
        slice1 = by_path["LeanQbe/T/Amd64/KissatPlainCert1.lean"]
        self.assertIn("public import LeanQbe.T.MainCertCore", slice1)
        self.assertIn("meta import LeanQbe.T.MainCertElab", slice1)

        cert_x64 = by_path["LeanQbe/T/Amd64/KissatPlainCert.lean"]
        self.assertIn("public import LeanQbe.T.MainCertProof", cert_x64)
        self.assertIn("noncomputable def plainCert", cert_x64)
        self.assertIn("#print axioms plainCert", cert_x64)

        link_arm = by_path["LeanQbe/T/Arm64/KissatPlainCertLink.lean"]
        self.assertIn("theorem ax_solve", link_arm)
        self.assertIn("#print axioms ax_solve", link_arm)
        self.assertNotIn("#print axioms solve_arm64_of_fnspec", link_arm)

        top_arm = by_path["LeanQbe/T/Arm64/KissatPlain.lean"]
        self.assertIn("@[reducible] noncomputable def kissatPlain_compiled_arm64", top_arm)
        self.assertIn("theorem ax_unsat_sound", top_arm)
        self.assertIn("#print axioms ax_unsat_sound", top_arm)
        self.assertNotIn("#print axioms plain_solve_bytes_unsat_sound_arm64", top_arm)

    def test_static_repo_resolution_matches_plain_and_fidelity(self) -> None:
        pl_args = gcs.parse_args(["--module", "Plain", "--root", str(REPO_ROOT), "--dry-run"])
        pl_cfg = gcs.build_config(pl_args)
        self.assertEqual(pl_cfg.total_fns, 59)
        self.assertTrue(all(m.source == "c0-static" for m in pl_cfg.fn_metrics))
        self.assertLess(pl_cfg.after_stats.cost_max_mean, pl_cfg.before_stats.cost_max_mean)
        self._assert_hygiene(gcs.build_plan(pl_cfg, ["amd64", "arm64"]))

        fid_args = gcs.parse_args(
            ["--module", "FullFidelity", "--allow-prefix-eval", "--root", str(REPO_ROOT), "--dry-run"]
        )
        fid_cfg = gcs.build_config(fid_args)
        self.assertEqual(fid_cfg.total_fns, 469)
        self._assert_hygiene(gcs.build_plan(fid_cfg, ["amd64", "arm64"]))

    def test_max_bound_mismatched_profile_and_nonpositive_target_slices(self) -> None:
        # 1. --max-bound != 2048 must match LinkedCert ... [] [] 0 <maxBound> in <Prefix>.lean.
        mb_args = gcs.parse_args(
            [
                "--module",
                "Plain",
                "--max-bound",
                "4096",
                "--target-slices",
                "6",
                "--root",
                str(REPO_ROOT),
                "--dry-run",
            ]
        )
        mb_cfg = gcs.build_config(mb_args)
        mb_files = dict(gcs.build_plan(mb_cfg, ["amd64"]))
        self._assert_hygiene(list(mb_files.items()))
        self.assertIn("plainCert :", mb_files["LeanQbe/T/Amd64/KissatPlainCert.lean"])
        self.assertIn("plainModule [] [] 0 4096 :=", mb_files["LeanQbe/T/Amd64/KissatPlainCert.lean"])
        self.assertIn("plainModule [] [] 0 4096 :=", mb_files["LeanQbe/T/Amd64/KissatPlain.lean"])

        # 2. Mismatched --profile length must fail closed against known module counts.
        with tempfile.TemporaryDirectory() as tmp:
            bad_prof = Path(tmp) / "short_10.json"
            rows = [
                {"index": i, "name": f"fn_{i}", "mid_tflat_size": 50}
                for i in range(10)
            ]
            bad_prof.write_text(json.dumps(rows), encoding="utf-8")
            for mod in ("Plain", "FullFidelity"):
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
                    "Plain",
                    "--target-slices",
                    str(bad_k),
                    "--root",
                    str(REPO_ROOT),
                    "--dry-run",
                ]
            )
            with self.assertRaises(ValueError):
                gcs.build_config(bad_k_args)

    def test_explicit_cli_chunked_inl_ladder_and_entry_const_override(self) -> None:
        base_cli = [
            "--prefix", "KissatCustom",
            "--stem", "cust",
            "--source-mod", "LeanQbe.T.Examples.Kissat.FullFidelityAssembly",
            "--source-ns", "LeanQbe.T.Examples.Kissat.FullFidelityAssembly",
            "--proof-mod", "LeanQbe.T.Examples.Kissat.FullFidelityAssemblyProof",
            "--proof-ns", "LeanQbe.T.Examples.Kissat.FullFidelityAssembly",
            "--inl-mod", "LeanQbe.T.Examples.Kissat.FullFidelityInlData",
            "--inl-policy-mod", "LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy",
            "--inl-fns", "custInlFns",
            "--inl-mod-sym", "custInlMod",
            "--inl-policy", "fidInlPolicy",
            "--fns", "custFns",
            "--mod", "custModule",
            "--env", "custEnv",
            "--module-ok", "cust_moduleOk",
            "--no-exit", "custEnv_noExit",
            "--entry-const", "FullM6Orch.m6oSolveBytesFn",
            "--hdr-model", "m6",
            "--max-dirs", "600",
            "--total-fns", "60",
            "--cert-style", "ladder",
            "--root", str(REPO_ROOT),
            "--dry-run",
        ]
        cfg = gcs.build_config(gcs.parse_args(base_cli))
        self.assertEqual(cfg.prefix, "KissatCustom")
        self.assertEqual(cfg.max_dirs, 600)
        self.assertTrue(cfg.is_inlined)
        self.assertEqual(cfg.hdr_model, "m6")
        self.assertEqual(cfg.entry_const, "FullM6Orch.m6oSolveBytesFn")
        files = dict(gcs.build_plan(cfg, ["amd64", "arm64"]))
        self._assert_hygiene(list(files.items()))
        self.assertIn("custInlCert.castModule custInlMod.eq", files["LeanQbe/T/Amd64/KissatCustomCert.lean"])
        self.assertIn("allChunks_link", files["LeanQbe/T/Amd64/KissatCustomCert.lean"])
        self.assertIn("eval_prefix_ext! custAllExt x64Target x64LegalTarget custInlFns",
                      files["LeanQbe/T/Amd64/KissatCustomBounds.lean"])
        for arch_dir in ("Amd64", "Arm64"):
            top = files[f"LeanQbe/T/{arch_dir}/KissatCustom.lean"]
            self.assertNotRegex(top, r"\bm6Nv\w*")
            self.assertIn("def custNvWorkLen : Nat := 6144", top)
            self.assertIn("FullM6Orch.m6oSolveBytesFn ∈ custModule.fns", top)
            snd = files[f"LeanQbe/T/{arch_dir}/KissatCustomSound.lean"]
            self.assertIn("readModelFromWorkM6", snd)
            self.assertIn("FullM6Orch.m6oSolveBytesFn ∈ custModule.fns", snd)

        # CLI --entry-const override propagates to Top and Sound.
        ov_cfg = gcs.build_config(gcs.parse_args([*base_cli, "--entry-const", "CustomOrch.solveFn"]))
        self.assertEqual(ov_cfg.entry_const, "CustomOrch.solveFn")
        ov_files = dict(gcs.build_plan(ov_cfg, ["amd64", "arm64"]))
        self._assert_hygiene(list(ov_files.items()))
        for arch_dir in ("Amd64", "Arm64"):
            self.assertIn("CustomOrch.solveFn ∈ custModule.fns", ov_files[f"LeanQbe/T/{arch_dir}/KissatCustom.lean"])
            self.assertIn("CustomOrch.solveFn ∈ custModule.fns", ov_files[f"LeanQbe/T/{arch_dir}/KissatCustomSound.lean"])

    def test_full_m8opt_option_r_reuse_modes(self) -> None:
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
                        "reuse_prefix": "KissatFidelity",
                        "reuse_inl_mod": "LeanQbe.T.Examples.Kissat.FullFidelityInl",
                        "reuse_inl_fns": "fidInlFns",
                        "reuse_bridge_mod": "",
                        "reused_slices": [{"src_index": 2, "start": 12, "count": 12}],
                    }
                ),
                encoding="utf-8",
            )
            common = [
                "--module", "FullM8Opt",
                "--cert-style", "ladder",
                "--total-fns", "40",
                "--profile", str(p_path),
                "--singleton-size", "400",
                "--max-slice-size", "650",
                "--max-slice-count", "10",
                "--root", str(REPO_ROOT),
                "--dry-run",
            ]
            # 1. Verbatim reuse without bridge emits inline reuse_eq (FullFidelity has no default bridge).
            fid_common = [
                "--module", "FullFidelity",
                "--prefix", "KissatFidNext",
                "--cert-style", "ladder",
                "--total-fns", "40",
                "--profile", str(p_path),
                "--singleton-size", "400",
                "--max-slice-size", "650",
                "--max-slice-count", "10",
                "--root", str(REPO_ROOT),
                "--dry-run",
            ]
            r_cfg = gcs.build_config(
                gcs.parse_args([*fid_common, "--reuse-spec", str(r_path), "--reuse-mode", "verbatim"])
            )
            self.assertEqual(r_cfg.reuse_mode, "verbatim")
            r_files = dict(gcs.build_plan(r_cfg, ["amd64", "arm64"]))
            self._assert_hygiene(list(r_files.items()))
            cert = r_files["LeanQbe/T/Amd64/KissatFidNextCert.lean"]
            self.assertIn("public import LeanQbe.T.Amd64.KissatFidelityCert2", cert)
            self.assertIn("KissatFidelityCert2.cert2.chunks", cert)
            self.assertIn("private theorem reuse_eq", cert)
            self.assertNotIn("open LeanQbe.T.Amd64.KissatFidNextCert1", cert)

            # 2. Default reuse mode without --reuse-mode is pruned_relink.
            d_cfg = gcs.build_config(gcs.parse_args([*common, "--reuse-spec", str(r_path)]))
            self.assertEqual(d_cfg.reuse_mode, "pruned_relink")

            # 3. Bridged verbatim reuse emits bridge import and theorem calls, no inline reuse_eq.
            b_path = Path(tmp) / "reuse_bridge.json"
            b_path.write_text(
                json.dumps(
                    {
                        "reuse_prefix": "KissatFidelity",
                        "reuse_inl_mod": "LeanQbe.T.Examples.Kissat.FullFidelityInl",
                        "reuse_inl_fns": "fidInlFns",
                        "reuse_bridge_mod": "LeanQbe.T.Examples.Kissat.FullFidelityM8OptBridge",
                        "reuse_thm_prefix": "reuse_fid_eq_",
                        "reused_slices": [{"src_index": 2, "start": 12, "count": 12}],
                    }
                ),
                encoding="utf-8",
            )
            b_cfg = gcs.build_config(
                gcs.parse_args([*common, "--reuse-spec", str(b_path), "--reuse-mode", "verbatim"])
            )
            b_files = dict(gcs.build_plan(b_cfg, ["amd64", "arm64"]))
            self._assert_hygiene(list(b_files.items()))
            b_cert = b_files["LeanQbe/T/Amd64/KissatM8OptCert.lean"]
            self.assertIn("public import LeanQbe.T.Examples.Kissat.FullFidelityM8OptBridge", b_cert)
            self.assertIn("← reuse_fid_eq_2]", b_cert)
            self.assertNotIn("private theorem reuse_eq", b_cert)

            # 4. Pruned-relink mode emits eval_raw_callees! + relinkChunkListCover.
            p_cfg = gcs.build_config(
                gcs.parse_args([*common, "--reuse-spec", str(b_path), "--reuse-mode", "pruned_relink"])
            )
            self.assertEqual(p_cfg.reuse_mode, "pruned_relink")
            p_files = dict(gcs.build_plan(p_cfg, ["amd64", "arm64"]))
            self._assert_hygiene(list(p_files.items()))
            for arch_dir in ("Amd64", "Arm64"):
                p_cert = p_files[f"LeanQbe/T/{arch_dir}/KissatM8OptCert.lean"]
                self.assertIn("public import LeanQbe.T.MainLinkReuseCover", p_cert)
                self.assertIn("meta import LeanQbe.T.MainLinkReuseElab", p_cert)
                self.assertIn("eval_raw_callees! rCallees", p_cert)
                self.assertIn("eval_pruned_ext! rExt", p_cert)
                self.assertIn("calleesCover_of_checkRaw", p_cert)
                self.assertIn("relinkChunkListCover", p_cert)
                self.assertIn("relinkChunkListCover_fns", p_cert)
                self.assertIn("relinkChunkListCover_maxBound", p_cert)
                self.assertIn("private theorem reuseBaseFns_wf", p_cert)

            # 5. JSON-configured pruned_relink with custom proof module & src_start works.
            pr_path = Path(tmp) / "reuse_pruned.json"
            pr_path.write_text(
                json.dumps(
                    {
                        "reuse_prefix": "KissatFidelity",
                        "reuse_mode": "pruned_relink",
                        "reuse_inl_mod": "LeanQbe.T.Examples.Kissat.FullFidelityInl",
                        "reuse_inl_fns": "fidInlFns",
                        "reuse_inl_mod_sym": "fidInlMod",
                        "reuse_inl_policy": "fidInlPolicy",
                        "reuse_proof_mod": "LeanQbe.T.Examples.Kissat.FullFidelityAssemblyProof",
                        "reuse_proof_ns": "LeanQbe.T.Examples.Kissat.FullFidelityAssembly",
                        "reuse_acyclic": "fid_acyclic",
                        "reuse_wf": "fidFns_wf",
                        "reused_slices": [
                            {"src_index": 2, "start": 12, "src_start": 10, "count": 12}
                        ],
                    }
                ),
                encoding="utf-8",
            )
            pr_cfg = gcs.build_config(gcs.parse_args([*common, "--reuse-spec", str(pr_path)]))
            pr_files = dict(gcs.build_plan(pr_cfg, ["amd64", "arm64"]))
            self._assert_hygiene(list(pr_files.items()))
            pr_cert = pr_files["LeanQbe/T/Amd64/KissatM8OptCert.lean"]
            self.assertIn("(fidInlFns.drop 10).take 12", pr_cert)
            self.assertIn("FullFidelityAssemblyProof", pr_cert)
            self.assertIn("fid_acyclic fidFns_wf", pr_cert)

            # 6. Explicit `--slice-sizes` + `--cert-only` with `--reuse-spec` uses preset defaults.
            co_args = gcs.parse_args(
                [
                    *common,
                    "--reuse-spec", str(b_path),
                    "--reuse-mode", "pruned_relink",
                    "--slice-sizes", "6,6,8,8",
                    "--cert-only",
                ]
            )
            co_cfg = gcs.build_config(co_args)
            co_files = dict(gcs.build_plan(co_cfg, ["amd64", "arm64"], cert_only=co_args.cert_only))
            self._assert_hygiene(list(co_files.items()))
            self.assertEqual(
                sorted(co_files.keys()),
                [
                    "LeanQbe/T/Amd64/KissatM8OptCert.lean",
                    "LeanQbe/T/Arm64/KissatM8OptCert.lean",
                ],
            )
            self.assertEqual([s.count for s in co_cfg.slices], [6, 6, 12, 8, 8])
            self.assertIn("fid_acyclic fidFns_wf", co_files["LeanQbe/T/Amd64/KissatM8OptCert.lean"])

            # 7. --reuse-mode without --reuse-spec fails closed.
            bad_args = gcs.parse_args(
                [
                    "--module", "FullM8Opt",
                    "--reuse-mode", "pruned_relink",
                    "--root", str(REPO_ROOT),
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
                "LeanQbe.T.Examples.Kissat.FullFidelityAssembly",
                "--source-ns",
                "LeanQbe.T.Examples.Kissat.FullFidelityAssembly",
                "--proof-mod",
                "LeanQbe.T.Examples.Kissat.FullFidelityAssemblyProof",
                "--proof-ns",
                "LeanQbe.T.Examples.Kissat.FullFidelityAssembly",
                "--inl-mod",
                "LeanQbe.T.Examples.Kissat.FullFidelityInlData",
                "--inl-policy-mod",
                "LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy",
                "--inl-fns",
                "m8InlFns",
                "--inl-mod-sym",
                "m8InlMod",
                "--inl-policy",
                "fidInlPolicy",
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
                "LeanQbe.T.Examples.Kissat.FullFidelityAssembly",
                "--source-ns",
                "LeanQbe.T.Examples.Kissat.FullFidelityAssembly",
                "--proof-mod",
                "LeanQbe.T.Examples.Kissat.FullFidelityAssemblyProof",
                "--proof-ns",
                "LeanQbe.T.Examples.Kissat.FullFidelityAssembly",
                "--inl-mod",
                "LeanQbe.T.Examples.Kissat.FullFidelityInlData",
                "--inl-policy-mod",
                "LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy",
                "--inl-fns",
                "m8InlFns",
                "--inl-mod-sym",
                "m8InlMod",
                "--inl-policy",
                "fidInlPolicy",
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
                "Plain",
                "--cert-style",
                "slices",
                "--slice-sizes",
                "12,12,12,12,11",
                "--root",
                str(REPO_ROOT),
                "--dry-run",
            ]
        )
        single_cfg = gcs.build_config(single_args)
        single_files = dict(gcs.build_plan(single_cfg, ["amd64"]))
        self._assert_hygiene(list(single_files.items()))
        pl_cert = single_files["LeanQbe/T/Amd64/KissatPlainCert.lean"]
        self.assertIn("ChunkSlice.ofDrop", pl_cert)
        self.assertIn("plainFns_length", pl_cert)
        self.assertIn("LinkedCert.ofChunkSlices", pl_cert)
        self.assertNotIn("sufChunks", pl_cert)

        # Fail closed when `--abi-common` is requested without m6 hdr model or inlined module.
        bad_abi_args = gcs.parse_args(
            [
                "--module",
                "Plain",
                "--abi-common",
                "--root",
                str(REPO_ROOT),
                "--dry-run",
            ]
        )
        with self.assertRaises(ValueError):
            gcs.build_config(bad_abi_args)

    def test_c0_header_scan_ignores_type_suffixed_call_sites(self) -> None:
        # `..._bool_m6(..)) {` / `..._u64_m7(..)) {` are calls, not `_m6` / `_m7` definitions:
        # a phantom entry would shift every later function's cost onto its neighbour.
        code = (
            "bool full_shrink_blk_bool_m6(u64 h) { return h > 0; }\n"
            "u64 full_min_shrink_m6(u64 h) {\n"
            "  if (!full_shrink_blk_bool_m6(h)) { return 0; }\n"
            "  return 1;\n"
            "}\n"
            "u64 full_cong_find_m7(u64 cb, u64 k) {\n"
            "  if (full_cong_bsearch_u64_m7(cb, k)) { return 1; }\n"
            "  return 0;\n"
            "}\n"
        )
        self.assertEqual(
            list(gcs.extract_c0_metrics(code)),
            ["full_shrink_blk_bool_m6", "full_min_shrink_m6", "full_cong_find_m7"],
        )

    def test_full_fidelity_m8opt_presets_and_pin_cuts(self) -> None:
        for alias in ("FullFidelity", "KissatFidelity", "fidelity", "fid"):
            self.assertEqual(gcs.resolve_preset(alias).prefix, "KissatFidelity")
        for alias in ("FullM8Opt", "KissatM8Opt", "FullM8", "m8opt", "opt", "m8"):
            self.assertEqual(gcs.resolve_preset(alias).prefix, "KissatM8Opt")

        with tempfile.TemporaryDirectory() as tmp:
            cuts = (26, 27, 60, 61)
            cuts_path = Path(tmp) / "pin_cuts.json"
            cuts_path.write_text(json.dumps(list(cuts)), encoding="utf-8")

            fid_args = gcs.parse_args(
                [
                    "--module",
                    "FullFidelity",
                    "--allow-prefix-eval",
                    "--pin-cuts",
                    str(cuts_path),
                    "--root",
                    str(REPO_ROOT),
                    "--dry-run",
                ]
            )
            fid_cfg = gcs.build_config(fid_args)
            self.assertEqual(fid_cfg.prefix, "KissatFidelity")
            self.assertEqual(fid_cfg.stem, "fid")
            self.assertEqual(fid_cfg.total_fns, 469)
            self.assertEqual(fid_cfg.cert_style, "slices")
            self.assertTrue(fid_cfg.abi_common)
            self.assertEqual(fid_cfg.fns_length_thm, "fidInlFns_length")
            for sl in fid_cfg.slices:
                for cut in cuts:
                    self.assertFalse(sl.start < cut < sl.end, (sl, cut))
            fid_files = dict(gcs.build_plan(fid_cfg, ["amd64", "arm64"]))
            self._assert_hygiene(list(fid_files.items()))
            fid_cert = fid_files["LeanQbe/T/Amd64/KissatFidelityCert.lean"]
            self.assertIn("fidInlFns_length", fid_cert)
            self.assertIn("LinkedCert.ofChunkSlices", fid_cert)

            reuse_path = Path(tmp) / "m8opt_reuse.json"
            reuse_path.write_text(
                json.dumps(
                    {
                        "reused_slices": [
                            {"src_index": 0, "start": 0, "src_start": 0, "count": 12},
                            {"src_index": 1, "start": 12, "src_start": 12, "count": 12},
                        ]
                    }
                ),
                encoding="utf-8",
            )
            opt_args = gcs.parse_args(
                [
                    "--module",
                    "FullM8Opt",
                    "--reuse-spec",
                    str(reuse_path),
                    "--root",
                    str(REPO_ROOT),
                    "--dry-run",
                ]
            )
            opt_cfg = gcs.build_config(opt_args)
            self.assertEqual(opt_cfg.prefix, "KissatM8Opt")
            self.assertEqual(opt_cfg.stem, "m8Opt")
            self.assertEqual(opt_cfg.total_fns, 494)
            self.assertEqual(opt_cfg.reuse_prefix, "KissatFidelity")
            self.assertEqual(opt_cfg.reuse_mode, "pruned_relink")
            self.assertEqual(
                opt_cfg.reuse_bridge_mod,
                "LeanQbe.T.Examples.Kissat.FullFidelityM8OptBridge",
            )
            self.assertEqual(opt_cfg.fns_length_thm, "m8OptInlFns_length")
            opt_files = dict(gcs.build_plan(opt_cfg, ["amd64", "arm64"]))
            self._assert_hygiene(list(opt_files.items()))
            for arch_dir in ("Amd64", "Arm64"):
                opt_cert = opt_files[f"LeanQbe/T/{arch_dir}/KissatM8OptCert.lean"]
                self.assertIn("public import LeanQbe.T.MainLinkReuseCover", opt_cert)
                self.assertIn("eval_raw_callees! rCallees", opt_cert)
                self.assertIn("FullFidelityM8OptBridge", opt_cert)

    def test_n2_n4_n6_no_bounds_literal_micro_slices_and_tree(self) -> None:
        # 1. FullFidelity preset defaults to FullFidelityInlData + pruneExt + no-bounds-import.
        fid_args = gcs.parse_args(
            ["--module", "FullFidelity", "--allow-prefix-eval", "--root", str(REPO_ROOT), "--dry-run"]
        )
        fid_cfg = gcs.build_config(fid_args)
        self.assertEqual(fid_cfg.inl_mod, "LeanQbe.T.Examples.Kissat.FullFidelityInlData")
        self.assertTrue(fid_cfg.prune_ext)
        self.assertTrue(fid_cfg.no_bounds_import)
        fid_files = dict(gcs.build_plan(fid_cfg, ["amd64", "arm64"]))
        self._assert_hygiene(list(fid_files.items()))
        self.assertNotIn("LeanQbe/T/Amd64/KissatFidelityBounds.lean", fid_files)
        self.assertNotIn("LeanQbe/T/Arm64/KissatFidelityBounds.lean", fid_files)
        fid_s2 = fid_files["LeanQbe/T/Amd64/KissatFidelityCert2.lean"]
        self.assertNotIn("KissatFidelityBounds", fid_s2)
        self.assertIn("eval_prefix_ext! slice2Ext", fid_s2)
        self.assertIn("(pruneFor := slice2Mod.fns)", fid_s2)
        self.assertIn("(pruneExt := true)", fid_s2)

        # 2. --bounds-json emits pure literal slice{k}Ext and isolates late-fn edits.
        with tempfile.TemporaryDirectory() as tmp:
            fn_rows_a = [
                {
                    "name": f"fn_{i}",
                    "as": ["i64"],
                    "rs": ["i64"],
                    "bound": 16 + i,
                    "callees": [f"fn_{i - 1}"] if i > 0 else [],
                }
                for i in range(12)
            ]
            fn_rows_b = [dict(r) for r in fn_rows_a]
            fn_rows_b[11]["bound"] = 999  # Editing the last function #11
            bounds_a = Path(tmp) / "bounds_a.json"
            bounds_b = Path(tmp) / "bounds_b.json"
            bounds_a.write_text(json.dumps(fn_rows_a), encoding="utf-8")
            bounds_b.write_text(json.dumps(fn_rows_b), encoding="utf-8")

            base_cli = [
                "--prefix",
                "KissatMini",
                "--stem",
                "mini",
                "--total-fns",
                "12",
                "--slice-sizes",
                "3,3,3,3",
                "--cert-style",
                "slices",
                "--prune-ext",
                "--tree-groups",
                "2",
                "--root",
                str(REPO_ROOT),
                "--dry-run",
            ]
            files_a = dict(
                gcs.build_plan(
                    gcs.build_config(gcs.parse_args([*base_cli, "--bounds-json", str(bounds_a)])),
                    ["amd64"],
                )
            )
            files_b = dict(
                gcs.build_plan(
                    gcs.build_config(gcs.parse_args([*base_cli, "--bounds-json", str(bounds_b)])),
                    ["amd64"],
                )
            )
            self._assert_hygiene(list(files_a.items()))
            self.assertNotIn("LeanQbe/T/Amd64/KissatMiniBounds.lean", files_a)
            for k in (1, 2, 3, 4):
                rel = f"LeanQbe/T/Amd64/KissatMiniCert{k}.lean"
                self.assertEqual(files_a[rel], files_b[rel], f"late-fn edit mutated {rel}")
            s2 = files_a["LeanQbe/T/Amd64/KissatMiniCert2.lean"]
            self.assertIn("private def slice2Ext : List (SigEntry × Nat) := [", s2)
            self.assertIn('(("fn_2", [i64], [i64]), 18)', s2)
            self.assertNotIn('"fn_0"', s2)
            self.assertNotIn("eval_prefix_ext!", s2)
            self.assertIn("(pruneExt := true)", s2)

            cert = files_a["LeanQbe/T/Amd64/KissatMiniCert.lean"]
            self.assertIn("ChunkSlice.ofSlices", cert)
            self.assertIn("CheckedSliceGroup", cert)
            self.assertIn("LinkedCert.ofCheckedGroups", cert)
            self.assertIn("private theorem grp0_ext", cert)
            self.assertIn("private theorem grp1_ext", cert)
            self.assertIn("private theorem allGroups_meta", cert)

        # 3. Cost-capped micro-slicing (--max-slice-weight) + 2-level tree on 501-fn Step 7!
        s7_args = gcs.parse_args(
            [
                "--module",
                "FullFidelityStep7",
                "--allow-prefix-eval",
                "--max-slice-weight",
                "1200",
                "--slice-size",
                "4",
                "--tree-groups",
                "8",
                "--root",
                str(REPO_ROOT),
                "--dry-run",
            ]
        )
        s7_cfg = gcs.build_config(s7_args)
        self.assertEqual(s7_cfg.total_fns, 501)
        self.assertEqual(s7_cfg.source_mod, "LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7")
        self.assertEqual(s7_cfg.mod, "fidStep7Module")
        self.assertTrue(s7_cfg.prune_ext)
        self.assertTrue(s7_cfg.no_bounds_import)
        self.assertEqual(s7_cfg.tree_groups, 8)
        self.assertEqual(sum(sl.count for sl in s7_cfg.slices), 501)
        self.assertTrue(all(1 <= sl.count <= 4 for sl in s7_cfg.slices))
        self.assertGreater(len(s7_cfg.slices), 100)
        for sl in s7_cfg.slices:
            if sl.count > 1:
                wt = sum(s7_cfg.fn_metrics[i].cost for i in range(sl.start, sl.end))
                self.assertLessEqual(wt, 1200.0 + 1e-6)
        s7_files = dict(gcs.build_plan(s7_cfg, ["amd64", "arm64"]))
        self._assert_hygiene(list(s7_files.items()))
        for arch_dir in ("Amd64", "Arm64"):
            self.assertNotIn(f"LeanQbe/T/{arch_dir}/KissatFidelityStep7Bounds.lean", s7_files)
            s7_cert = s7_files[f"LeanQbe/T/{arch_dir}/KissatFidelityStep7Cert.lean"]
            self.assertIn("LinkedCert.ofCheckedGroups", s7_cert)
            self.assertIn("private theorem grp7_ext", s7_cert)
            self.assertIn("allGroups_meta", s7_cert)
            s7_s2 = s7_files[f"LeanQbe/T/{arch_dir}/KissatFidelityStep7Cert2.lean"]
            self.assertNotIn("KissatFidelityStep7Bounds", s7_s2)
            self.assertIn("(pruneExt := true)", s7_s2)

        # Fail closed when --tree-groups >= 2 is requested with --cert-style ladder.
        bad_tree_args = gcs.parse_args(
            [
                "--module",
                "Plain",
                "--cert-style",
                "ladder",
                "--tree-groups",
                "4",
                "--root",
                str(REPO_ROOT),
                "--dry-run",
            ]
        )
        with self.assertRaises(ValueError):
            gcs.build_config(bad_tree_args)

    def test_n5_shard4_flat_flag_and_full_fidelity_step11_preset(self) -> None:
        # 1. FullFidelityStep11 preset defaults: flat=True, chunk_size=1, workers=2,
        #    max_dirs=600, tree_groups=8, prune_ext=True, materialized FullFidelityStep11Inl.
        s11_args = gcs.parse_args(
            [
                "--module", "FullFidelityStep11", "--allow-prefix-eval",
                "--root", str(REPO_ROOT), "--dry-run",
            ]
        )
        s11_cfg = gcs.build_config(s11_args)
        self.assertEqual(s11_cfg.prefix, "KissatFidelityStep11")
        self.assertEqual(s11_cfg.stem, "fidStep11")
        self.assertEqual(s11_cfg.total_fns, 505)
        self.assertEqual(s11_cfg.inl_mod, "LeanQbe.T.Examples.Kissat.FullFidelityStep11Inl")
        self.assertTrue(gcs.is_materialized_inl_mod(s11_cfg.cert_source_mod))
        self.assertTrue(s11_cfg.flat)
        self.assertEqual(s11_cfg.chunk_size, 1)
        self.assertEqual(s11_cfg.max_dirs, 600)
        self.assertEqual(s11_cfg.tree_groups, 8)
        self.assertEqual(s11_cfg.cert_style, "slices")
        self.assertTrue(s11_cfg.prune_ext)
        self.assertTrue(s11_cfg.no_bounds_import)
        self.assertEqual(s11_cfg.after_stats.lpt.workers, 2)

        s11_files = dict(gcs.build_plan(s11_cfg, ["amd64", "arm64"]))
        self._assert_hygiene(list(s11_files.items()))
        for arch_dir in ("Amd64", "Arm64"):
            s1 = s11_files[f"LeanQbe/T/{arch_dir}/KissatFidelityStep11Cert1.lean"]
            s2 = s11_files[f"LeanQbe/T/{arch_dir}/KissatFidelityStep11Cert2.lean"]
            for sl_src in (s1, s2):
                self.assertIn("public import LeanQbe.T.MainCertFlat", sl_src)
                self.assertIn("meta import LeanQbe.T.MainCertFlatElab", sl_src)
                self.assertNotIn("meta import LeanQbe.T.Examples.Kissat.FullFidelityStep11Inl", sl_src)
                self.assertIn("noncomputable abbrev slice", sl_src)
                self.assertIn("(flat := true)", sl_src)
                self.assertIn("(pruneExt := true)", sl_src)
            self.assertIn("slice1Mod 1", s1)
            self.assertIn("eval_prefix_ext! slice2Ext", s2)
            self.assertEqual(s2.count("(flat := true)"), 2)

        # 2. Explicit --bounds-import with --flat emits flat imports + `(flat := true)` in Bounds.
        b_args = gcs.parse_args(
            [
                "--module",
                "FullFidelityStep11",
                "--bounds-import",
                "--root",
                str(REPO_ROOT),
                "--dry-run",
            ]
        )
        b_cfg = gcs.build_config(b_args)
        b_files = dict(gcs.build_plan(b_cfg, ["amd64", "arm64"]))
        self._assert_hygiene(list(b_files.items()))
        for arch_dir in ("Amd64", "Arm64"):
            bnd = b_files[f"LeanQbe/T/{arch_dir}/KissatFidelityStep11Bounds.lean"]
            self.assertIn("public import LeanQbe.T.MainCertFlat", bnd)
            self.assertIn("meta import LeanQbe.T.MainCertFlatElab", bnd)
            self.assertNotIn("meta import LeanQbe.T.Examples.Kissat.FullFidelityStep11Inl", bnd)
            self.assertIn("(flat := true)", bnd)

        # 3. --no-flat disables flat imports/options on FullFidelityStep11; --flat enables on M6.
        nf_cfg = gcs.build_config(
            gcs.parse_args(
                [
                    "--module", "FullFidelityStep11", "--no-flat", "--allow-prefix-eval",
                    "--root", str(REPO_ROOT), "--dry-run",
                ]
            )
        )
        self.assertFalse(nf_cfg.flat)
        nf_files = dict(gcs.build_plan(nf_cfg, ["amd64"]))
        self._assert_hygiene(list(nf_files.items()))
        nf_s1 = nf_files["LeanQbe/T/Amd64/KissatFidelityStep11Cert1.lean"]
        self.assertNotIn("MainCertFlat", nf_s1)
        self.assertNotIn("(flat := true)", nf_s1)

        fid_flat_cfg = gcs.build_config(
            gcs.parse_args(
                [
                    "--module", "FullFidelity", "--flat", "--bounds-import",
                    "--root", str(REPO_ROOT), "--dry-run",
                ]
            )
        )
        self.assertTrue(fid_flat_cfg.flat)
        self.assertEqual(fid_flat_cfg.chunk_size, 1)
        self.assertEqual(fid_flat_cfg.after_stats.lpt.workers, 2)
        fid_files = dict(gcs.build_plan(fid_flat_cfg, ["amd64"]))
        self._assert_hygiene(list(fid_files.items()))
        self.assertIn(
            "public import LeanQbe.T.MainCertFlat",
            fid_files["LeanQbe/T/Amd64/KissatFidelityBounds.lean"],
        )
        self.assertIn(
            "meta import LeanQbe.T.MainCertFlatElab",
            fid_files["LeanQbe/T/Amd64/KissatFidelityCert1.lean"],
        )
        self.assertIn("(flat := true)", fid_files["LeanQbe/T/Amd64/KissatFidelityCert1.lean"])

        # 4. FullFidelityStep12 unified 517-fn preset defaults & dry-run hygiene.
        s12_cfg = gcs.build_config(
            gcs.parse_args(
                [
                    "--module", "step12", "--allow-prefix-eval",
                    "--root", str(REPO_ROOT), "--dry-run",
                ]
            )
        )
        self.assertEqual(s12_cfg.prefix, "KissatFidelityStep12")
        self.assertEqual(s12_cfg.stem, "fidStep12")
        self.assertEqual(s12_cfg.total_fns, 517)
        self.assertEqual(s12_cfg.inl_mod, "LeanQbe.T.Examples.Kissat.FullFidelityStep12Inl")
        self.assertTrue(s12_cfg.flat)
        self.assertEqual(s12_cfg.chunk_size, 1)
        self.assertEqual(s12_cfg.tree_groups, 8)
        s12_files = dict(gcs.build_plan(s12_cfg, ["amd64", "arm64"]))
        self._assert_hygiene(list(s12_files.items()))
        self.assertIn(
            "fidStep12Cert",
            s12_files["LeanQbe/T/Amd64/KissatFidelityStep12Cert.lean"],
        )

    def test_p0_bounds_json_default_discovery_and_prefix_eval_guard(self) -> None:
        # 1. > 200-fn preset with no_bounds_import refuses O(N^2) eval_prefix_ext! by default.
        for mod in ("FullFidelity", "FullFidelityStep11", "FullFidelityStep12"):
            with self.assertRaisesRegex(ValueError, "--allow-prefix-eval"):
                gcs.build_config(
                    gcs.parse_args(["--module", mod, "--root", str(REPO_ROOT), "--dry-run"])
                )

        # 2. <= 200-fn module with --no-bounds-import is NOT blocked.
        pl_cfg = gcs.build_config(
            gcs.parse_args(
                ["--module", "Plain", "--no-bounds-import", "--root", str(REPO_ROOT), "--dry-run"]
            )
        )
        self.assertTrue(pl_cfg.no_bounds_import)
        pl_files = dict(gcs.build_plan(pl_cfg, ["amd64", "arm64"]))
        self._assert_hygiene(list(pl_files.items()))
        self.assertIn("eval_prefix_ext! slice2Ext", pl_files["LeanQbe/T/Amd64/KissatPlainCert2.lean"])

        # 3. Auto-discovers bench/kissat/<Prefix>_bounds_{x64,arm64}.json and uses pure literals
        #    without needing --allow-prefix-eval, supporting both `rs` and `bs` + `f64`/`bool`.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            bdir = tmp_root / "bench" / "kissat"
            bdir.mkdir(parents=True)
            rows_x64 = [
                {
                    "name": f"fn_{i}",
                    "as": ["i64", "bool"] if i == 0 else ["i64"],
                    "rs": ["f64"] if i == 0 else ["i64"],
                    "bound": 32 + i,
                    "callees": (["fn_0", f"fn_{i - 1}"] if i > 0 else []),
                }
                for i in range(210)
            ]
            rows_arm = [
                {
                    "name": f"fn_{i}",
                    "as": ["i64", "bool"] if i == 0 else ["i64"],
                    "bs": ["f64"] if i == 0 else ["i64"],
                    "bound": 48 + i,
                    "callees": (["fn_0", f"fn_{i - 1}"] if i > 0 else []),
                }
                for i in range(210)
            ]
            (bdir / "KissatAuto_bounds_x64.json").write_text(
                json.dumps(rows_x64), encoding="utf-8"
            )
            (bdir / "KissatAuto_bounds_arm64.json").write_text(
                json.dumps(rows_arm), encoding="utf-8"
            )
            auto_cfg = gcs.build_config(
                gcs.parse_args(
                    [
                        "--prefix", "KissatAuto",
                        "--stem", "auto",
                        "--total-fns", "210",
                        "--uniform",
                        "--slice-size", "12",
                        "--cert-style", "slices",
                        "--no-bounds-import",
                        "--root", str(tmp_root),
                        "--dry-run",
                    ]
                )
            )
            self.assertEqual(len(auto_cfg.bounds_json_sources), 2)
            auto_files = dict(gcs.build_plan(auto_cfg, ["amd64", "arm64"]))
            self._assert_hygiene(list(auto_files.items()))
            for arch_dir in ("Amd64", "Arm64"):
                self.assertNotIn(f"LeanQbe/T/{arch_dir}/KissatAutoBounds.lean", auto_files)
                s2 = auto_files[f"LeanQbe/T/{arch_dir}/KissatAutoCert2.lean"]
                self.assertNotIn("eval_prefix_ext!", s2)
                self.assertIn("private def slice2Ext : List (SigEntry × Nat) := [", s2)
            self.assertIn('(("fn_0", [i64, .bool], [f64]), 32)', auto_files["LeanQbe/T/Amd64/KissatAutoCert2.lean"])
            self.assertIn('(("fn_11", [i64], [i64]), 43)', auto_files["LeanQbe/T/Amd64/KissatAutoCert2.lean"])
            self.assertIn('(("fn_0", [i64, .bool], [f64]), 48)', auto_files["LeanQbe/T/Arm64/KissatAutoCert2.lean"])
            self.assertIn('(("fn_11", [i64], [i64]), 59)', auto_files["LeanQbe/T/Arm64/KissatAutoCert2.lean"])
            self.assertEqual(gcs._format_lean_ty("f64"), "f64")
            self.assertEqual(gcs._format_lean_ty("f32"), "f32")
            self.assertEqual(gcs._format_lean_ty("bool"), ".bool")

            # 5. Additive SrcFull preset resolves cleanly to 418-fn Src.Full + Src.InlPolicy.
            for alias in ("SrcFull", "srcfull", "src-full", "kissatsrcfull", "kissatfull"):
                self.assertEqual(gcs.resolve_preset(alias).name, "SrcFull")
            sf_cfg = gcs.build_config(
                gcs.parse_args(
                    [
                        "--module", "SrcFull", "--allow-prefix-eval",
                        "--root", str(REPO_ROOT), "--dry-run",
                    ]
                )
            )
            self.assertEqual(sf_cfg.total_fns, 418)
            self.assertEqual(sf_cfg.source_mod, "LeanQbe.T.Examples.Kissat.Src.Full")
            self.assertEqual(sf_cfg.inl_policy_mod, "LeanQbe.T.Examples.Kissat.Src.InlPolicy")
            self.assertEqual(sf_cfg.inl_policy, "kissatInlChunkPolicy")
            self.assertEqual(sf_cfg.sat_nv_mod, "LeanQbe.T.Examples.Kissat.Proof.Spec.SatNv1")
            self._assert_hygiene(gcs.build_plan(sf_cfg, ["amd64", "arm64"]))

            # 4. Partial-arch bounds JSON refuses silent fallback to eval_prefix_ext! on uncovered arch.
            (bdir / "KissatAuto_bounds_arm64.json").unlink()
            partial_cfg = gcs.build_config(
                gcs.parse_args(
                    [
                        "--prefix", "KissatAuto",
                        "--stem", "auto",
                        "--total-fns", "210",
                        "--cert-style", "slices",
                        "--no-bounds-import",
                        "--root", str(tmp_root),
                        "--dry-run",
                    ]
                )
            )
            self._assert_hygiene(gcs.build_plan(partial_cfg, ["amd64"]))
            with self.assertRaisesRegex(ValueError, "--allow-prefix-eval"):
                gcs.build_plan(partial_cfg, ["arm64"])


if __name__ == "__main__":
    unittest.main()
