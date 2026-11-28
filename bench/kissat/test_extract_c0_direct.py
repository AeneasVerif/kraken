#!/usr/bin/env python3
"""Unit tests for Step-7 C0-direct split-TU extraction, fn-hash diffs, and canary ordering."""

import json
import os
import pathlib
import subprocess
import tempfile
import unittest

import sys

sys.dont_write_bytecode = True

THIS_DIR = pathlib.Path(__file__).resolve().parent
ROOT = THIS_DIR.parents[1]
KDIR = ROOT / "LeanQbe/T/Examples/Kissat"
sys.path.insert(0, str(THIS_DIR))

import check_canaries
import extract_c0_direct as ext


class ExtractC0DirectTest(unittest.TestCase):
    def test_step12_target_resolution_and_fallbacks(self):
        self.assertEqual(
            ext.resolve_target_spec(KDIR, "fidelity"),
            ("Src.Full", "Src.Full", "kissatFns"),
        )
        self.assertEqual(
            ext.resolve_target_spec(KDIR, "fid"),
            ("Src.Full", "Src.Full", "kissatFns"),
        )
        with tempfile.TemporaryDirectory() as td:
            fake = pathlib.Path(td)
            (fake / "FullFidelityAssembly.lean").write_text("", encoding="utf-8")
            self.assertEqual(
                ext.resolve_target_spec(fake, "fidelity"),
                ("FullFidelityAssembly", "FullFidelityAssembly", "fidFns"),
            )
            self.assertEqual(ext.default_target_for_kdir(fake), "fidelity")
        with tempfile.TemporaryDirectory() as td:
            fake_src = pathlib.Path(td)
            (fake_src / "Src").mkdir()
            (fake_src / "Src" / "Full.lean").write_text("", encoding="utf-8")
            self.assertEqual(
                ext.resolve_target_spec(fake_src, "fidelity"),
                ("Src.Full", "Src.Full", "kissatFns"),
            )
            self.assertEqual(ext.default_target_for_kdir(fake_src), "fidelity")

    def test_fidelity_and_plain_fn_counts(self):
        fid_fns, _, _, sym = ext.load_fns_for_target(KDIR, "fidelity")
        self.assertEqual(sym, "kissatFns")
        self.assertEqual(len(fid_fns), 418)
        src_fns, src_mod, src_ns, src_sym = ext.load_fns_for_target(KDIR, "src-full")
        self.assertEqual((src_mod, src_ns, src_sym), ("Src.Full", "Src.Full", "kissatFns"))
        self.assertEqual(len(src_fns), 418)
        self.assertEqual(src_fns[0]["name"], "f64u_msb64")
        self.assertEqual(src_fns[-1]["name"], "kissat_solve_bytes")
        plain_fns, _, _, _ = ext.load_fns_for_target(KDIR, "plain")
        self.assertEqual(len(plain_fns), 59)

    def test_split_dir_stability_mtime_and_stale_cleanup(self):
        fns, _, _, sym = ext.load_fns_for_target(KDIR, "src-full")
        with tempfile.TemporaryDirectory() as td:
            sdir = pathlib.Path(td)
            stale = sdir / "src_ObsoleteLegacy.c"
            stale.write_text("/* stale */\n", encoding="utf-8")

            info1 = ext.emit_split_dir(fns, sdir, "src-full", sym)
            self.assertTrue(info1["written_hdr"])
            self.assertEqual(info1["tu_count"], 41)
            self.assertEqual(info1["removed_tus"], ["src_ObsoleteLegacy.c"])
            self.assertFalse(stale.exists())
            self.assertTrue((sdir / "kissat_common.h").is_file())
            self.assertTrue((sdir / "src_Src_Float64.c").is_file())
            self.assertTrue((sdir / "src_Src_Factor.c").is_file())
            self.assertTrue((sdir / "src_Src_Watch.c").is_file())

            hdoc = json.loads((sdir / "c0_fn_hashes.json").read_text(encoding="utf-8"))
            self.assertEqual(hdoc["fn_count"], 418)
            self.assertEqual(hdoc["tu_count"], info1["tu_count"])
            self.assertIn("full_bva_commit", hdoc["functions"])
            self.assertIn("full_sort_bin_watches_fid", hdoc["functions"])

            hdr_ns = (sdir / "kissat_common.h").stat().st_mtime_ns
            fac_ns = (sdir / "src_Src_Factor.c").stat().st_mtime_ns

            # Second identical emit must preserve mtimes on all untouched files.
            info2 = ext.emit_split_dir(fns, sdir, "src-full", sym)
            self.assertFalse(info2["written_hdr"])
            self.assertEqual(info2["written_tus"], [])
            self.assertEqual((sdir / "kissat_common.h").stat().st_mtime_ns, hdr_ns)
            self.assertEqual((sdir / "src_Src_Factor.c").stat().st_mtime_ns, fac_ns)

            # Mutating one body inside Watch leaves kissat_common.h and Factor untouched.
            edited = [dict(f) for f in fns]
            for f in edited:
                if f["name"] == "full_sort_bin_watches_fid":
                    f["text"] = f["text"].replace("{", "{ /* noop edit */ ", 1)
                    break
            info3 = ext.emit_split_dir(edited, sdir, "src-full", sym)
            self.assertFalse(info3["written_hdr"])
            self.assertEqual(info3["written_tus"], ["src_Src_Watch.c"])
            self.assertEqual((sdir / "kissat_common.h").stat().st_mtime_ns, hdr_ns)
            self.assertEqual((sdir / "src_Src_Factor.c").stat().st_mtime_ns, fac_ns)
            self.assertNotEqual(info3["c0_sha256"], info1["c0_sha256"])

    def test_diff_against_base_unchanged_and_single_fn_change(self):
        fns, _, _, _ = ext.load_fns_for_target(KDIR, "src-full")
        r = subprocess.run(
            ["git", "-C", str(ROOT), "rev-parse", "HEAD"],
            capture_output=True, text=True, check=True,
        )
        head_rev = r.stdout.strip()
        diff_same = ext.diff_against_base(fns, ROOT, "src-full", head_rev)
        self.assertTrue(diff_same["unchanged"])
        self.assertEqual(diff_same["changed_fns"], [])

        mutated = [dict(f) for f in fns]
        for f in mutated:
            if f["name"] == "full_bva_commit":
                f["text"] = f["text"].replace(";", "; /* delta */", 1)
                break
        diff_one = ext.diff_against_base(mutated, ROOT, "src-full", head_rev)
        self.assertFalse(diff_one["unchanged"])
        self.assertEqual(diff_one["changed_fns"], ["full_bva_commit"])
        self.assertEqual(diff_one["modified_fns"], ["full_bva_commit"])
        self.assertEqual(diff_one["added_fns"], [])
        self.assertEqual(diff_one["removed_fns"], [])
        self.assertIn("src_Src_Factor.c", diff_one["changed_tus"])

    def test_canary_priority_and_baseline_c0d_lookup(self):
        manifest = [
            {"file": "c08_walk.cnf", "family": "08_long_horizon"},
            {"file": "c02_miter.cnf", "family": "02_deep_miter"},
            {"file": "c01_php.cnf", "family": "01_php_bva"},
            {"file": "c11_bva.cnf", "family": "11_c11_regressions"},
        ]
        ordered_bva, fams_bva = check_canaries.prioritize_manifest(manifest, ["full_bva_commit"])
        self.assertEqual(fams_bva, ["01_php_bva", "11_c11_regressions"])
        self.assertEqual([e["file"] for e in ordered_bva[:2]], ["c01_php.cnf", "c11_bva.cnf"])

        ordered_walk, fams_walk = check_canaries.prioritize_manifest(
            manifest, ["full_walk_effort_m7"],
        )
        self.assertEqual(fams_walk[0], "08_long_horizon")
        self.assertEqual(ordered_walk[0]["file"], "c08_walk.cnf")

        base_runs = {
            "KissatFidelity_C4": {"status": 20, "conflicts": 42},
            "KissatM8Opt_C3b": {"status": 20, "conflicts": 77},
        }
        self.assertEqual(
            check_canaries.lookup_baseline_run(base_runs, "KissatFidelity_C0d"),
            {"status": 20, "conflicts": 42},
        )
        self.assertEqual(
            check_canaries.lookup_baseline_run(base_runs, "KissatM8Opt_C0d"),
            {"status": 20, "conflicts": 77},
        )
        self.assertIsNone(
            check_canaries.lookup_baseline_run({"KissatFidelity_C4": {}}, "KissatM8Opt_C0d")
        )


if __name__ == "__main__":
    unittest.main()
