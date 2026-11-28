#!/usr/bin/env python3
"""Unit tests for `scripts/gen_build_segs.py` declarative subsystem cert generation."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gen_build_segs as gbs  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parent.parent


class GenBuildSegsTest(unittest.TestCase):
    """Covers `Src/Full.lean` parsing, DAG validation, heavy-fn isolation, and hygiene."""

    def test_parses_41_subsystems_from_src_full(self) -> None:
        args = gbs.parse_args(["--root", str(REPO_ROOT), "--dry-run"])
        mf = gbs.load_manifest(
            REPO_ROOT,
            None,
            base_ns=args.base_ns,
            src_full_mod=args.src_full_mod,
            src_full_mod_sym=args.src_full_mod_sym,
            heavy_threshold=args.heavy_threshold,
            profile_path=None,
            max_bound=args.max_bound,
            max_dirs=args.max_dirs,
            chunk_size=args.chunk_size,
            tree_groups=args.tree_groups,
        )
        self.assertEqual(len(mf.segs), 41)
        self.assertEqual(mf.segs[0].name, "Float64")
        self.assertEqual(mf.segs[-1].name, "Search")
        files = dict(gbs.build_plan(mf, ["amd64", "arm64"]))
        # 41 Inl + 1 Inl.Full + 2 * (41 seg + 1 Full) = 126 files
        self.assertEqual(len(files), 126)
        viv_x64 = files["LeanQbe/T/Examples/Kissat/Build/Amd64/Vivify.lean"]
        self.assertIn("seg_cert! cert x64Target", viv_x64)
        self.assertIn(
            "(hints := LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Vivify.hints)", viv_x64
        )
        self.assertNotIn("LeanQbe.T.Spill", viv_x64)
        self.assertNotIn("drop ", viv_x64)

    def test_manifest_with_deps_exports_and_profile_heavy_split(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tdir = Path(tmp)
            manifest = {
                "base_ns": "LeanQbeTest.T.ToyBuild",
                "src_full_mod": "LeanQbeTest.T.ToySrc.Full",
                "src_full_mod_sym": "toyMod",
                "segs": [
                    {
                        "name": "S1",
                        "src_mod": "LeanQbeTest.T.ToySrc.S1",
                        "fns": ["toy_inc", "toy_helper1"],
                        "deps": [],
                        "exports": ["toy_inc"],
                    },
                    {
                        "name": "S2",
                        "src_mod": "LeanQbeTest.T.ToySrc.S2",
                        "fns": ["toy_add_inc", "toy_mix2"],
                        "deps": ["S1"],
                        "exports": ["toy_add_inc"],
                    },
                    {
                        "name": "S3",
                        "src_mod": "LeanQbeTest.T.ToySrc.S3",
                        "fns": ["toy_step3", "toy_main"],
                        "deps": ["S2"],
                        "exports": [],
                    },
                ],
            }
            prof = [
                {"name": "toy_inc", "flat_size": 10},
                {"name": "toy_mix2", "flat_size": 1250},
                {"name": "toy_main", "flat_size": 200},
            ]
            mpath = tdir / "manifest.json"
            ppath = tdir / "profile.json"
            mpath.write_text(json.dumps(manifest), encoding="utf-8")
            ppath.write_text(json.dumps(prof), encoding="utf-8")

            mf = gbs.load_manifest(
                REPO_ROOT,
                mpath,
                base_ns="unused",
                src_full_mod="unused",
                src_full_mod_sym="unused",
                heavy_threshold=1000,
                profile_path=ppath,
                max_bound=2048,
                max_dirs=600,
                chunk_size=1,
                tree_groups=0,
            )
            self.assertEqual(mf.segs[1].heavy_fns, ("toy_mix2",))
            files = dict(gbs.build_plan(mf, ["amd64", "arm64"]))

            # Inl/S2 imports S1/Exports ONLY (never Inl/S1 or Src/S1).
            inl2 = files["LeanQbeTest/T/ToyBuild/Inl/S2.lean"]
            self.assertIn("public import LeanQbeTest.T.ToyBuild.Inl.S1.Exports", inl2)
            self.assertIn("public import LeanQbeTest.T.ToyBuild.Inl.S2.Exports", inl2)
            self.assertNotIn("ToyBuild.Inl.S1\n", inl2)
            self.assertNotIn("ToySrc.S1", inl2)
            self.assertIn("inline_seg! inl LeanQbeTest.T.ToySrc.S2.fns", inl2)

            # Inl/Full joins via InlSeg.module_inlinePlan_fns_of_segs.
            inl_full = files["LeanQbeTest/T/ToyBuild/Inl/Full.lean"]
            self.assertIn("InlSeg.module_inlinePlan_fns_of_segs", inl_full)
            self.assertIn("InlSeg.DepsOkFrom", inl_full)

            # Heavy fn toy_mix2 is isolated into name-keyed fn_cert! and excluded from S2.
            for arch_dir in ("Amd64", "Arm64"):
                s2 = files[f"LeanQbeTest/T/ToyBuild/{arch_dir}/S2.lean"]
                self.assertIn('(exclude := ["toy_mix2"])', s2)
                heavy = files[f"LeanQbeTest/T/ToyBuild/{arch_dir}/S2/ToyMix2.lean"]
                self.assertIn("fn_cert! cert", heavy)
                self.assertIn("S2.inl.flat.f1", heavy)
                self.assertIn("hint_toy_mix2", heavy)
                full = files[f"LeanQbeTest/T/ToyBuild/{arch_dir}/Full.lean"]
                self.assertIn(f"{arch_dir}.S2.cert.part0", full)
                self.assertIn(f"{arch_dir}.S2.ToyMix2.cert", full)
                self.assertIn("LinkedCert.ofSegs", full)

    def test_multi_dep_right_assoc_and_line_width_under_deep_namespace(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            mpath = Path(tmp) / "multi.json"
            mpath.write_text(
                json.dumps(
                    {
                        "base_ns": "LeanQbe.T.Examples.Kissat.Build",
                        "src_full_mod": "LeanQbe.T.Examples.Kissat.Src.Full",
                        "src_full_mod_sym": "kissatModule",
                        "segs": [
                            {"name": "Float64", "src_mod": "A.Float64", "fns": ["f0"], "exports": ["f0"]},
                            {"name": "Dimacs", "src_mod": "A.Dimacs", "fns": ["f1"], "deps": ["Float64"], "exports": ["f1"]},
                            {"name": "Limits", "src_mod": "A.Limits", "fns": ["f2"], "deps": ["Float64"], "exports": ["f2"]},
                            {
                                "name": "Search",
                                "src_mod": "A.Search",
                                "fns": ["f3"],
                                "deps": ["Float64", "Dimacs", "Limits"],
                                "exports": [],
                            },
                        ],
                    }
                ),
                encoding="utf-8",
            )
            mf = gbs.load_manifest(
                REPO_ROOT,
                mpath,
                base_ns="unused",
                src_full_mod="unused",
                src_full_mod_sym="unused",
                heavy_threshold=1000,
                profile_path=None,
                max_bound=2048,
                max_dirs=600,
                chunk_size=1,
                tree_groups=0,
            )
            files = dict(gbs.build_plan(mf, ["amd64"]))
            inl_full = files["LeanQbe/T/Examples/Kissat/Build/Inl/Full.lean"]
            # Left-associated `((d0 ++ d1) ++ d2)` matching Lean `infixl:65 " ++ "`.
            self.assertIn("depE (depR Limits.inl.exports_sub) <|", inl_full)
            self.assertIn("depE (depL <| depR Dimacs.inl.exports_sub) <|", inl_full)
            self.assertIn("depL <| depL <| depR Float64.inl.exports_sub,", inl_full)

    def test_rejects_cyclic_or_out_of_order_deps(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            mpath = Path(tmp) / "bad.json"
            mpath.write_text(
                json.dumps(
                    {
                        "segs": [
                            {"name": "S1", "src_mod": "A.S1", "deps": ["S2"]},
                            {"name": "S2", "src_mod": "A.S2", "deps": []},
                        ]
                    }
                ),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "DAG violation"):
                gbs.load_manifest(
                    REPO_ROOT,
                    mpath,
                    base_ns="A.Build",
                    src_full_mod="A.Full",
                    src_full_mod_sym="m",
                    heavy_threshold=1000,
                    profile_path=None,
                    max_bound=2048,
                    max_dirs=600,
                    chunk_size=1,
                    tree_groups=0,
                )


if __name__ == "__main__":
    unittest.main()
