#!/usr/bin/env python3
"""Unit tests for `scripts/check_firewall.py` including `--data-proof` (`N1`)."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
sys.path.insert(0, str(SCRIPTS_DIR))

import check_firewall as cf  # noqa: E402


class TestDataProofFirewall(unittest.TestCase):
    """Covers `check_firewall.py --require-isa --data-proof` (`L1-L4`, `D1`, `D2`)."""

    def test_repo_data_proof_firewall_is_clean(self) -> None:
        groups = cf.run_audit(REPO_ROOT, require_isa=True, data_proof=True)
        by_id = {g.leak_id: g for g in groups}
        self.assertIn("D1", by_id)
        self.assertIn("D2", by_id)
        self.assertIn(
            "LeanQbe/T/Examples/Kissat/Src/Full.lean",
            by_id["D1"].files,
        )
        self.assertIn(
            "LeanQbe/T/Examples/Kissat/Src/InlPolicy.lean",
            by_id["D1"].files,
        )
        for gid in ("L1", "L2", "L3", "L4", "D1", "D2"):
            self.assertEqual(by_id[gid].violations, [], f"{gid}: {by_id[gid].violations}")

    def test_data_proof_firewall_catches_proof_and_meta_leaks(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sdir = root / "LeanQbe" / "T" / "Examples" / "Kissat" / "Src"
            sdir.mkdir(parents=True)
            (sdir / "LeafA.lean").write_text(
                "module\n"
                "public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec\n"
                "meta import LeanQbe.T.PrintCpp\n",
                encoding="utf-8",
            )
            (sdir / "Full.lean").write_text(
                "module\n"
                "public import LeanQbe.T.Examples.Kissat.Src.LeafA\n"
                "meta import LeanQbe.T.Legal\n",
                encoding="utf-8",
            )
            dp_files = cf.discover_data_proof_files(root)
            d1, d2 = cf.check_data_proof_files(root, dp_files, {})
            d1_kinds = {(v.file, v.kind, v.module) for v in d1}
            d2_mods = {(v.file, v.module) for v in d2}
            self.assertIn(
                (
                    "LeanQbe/T/Examples/Kissat/Src/LeafA.lean",
                    "data-to-proof",
                    "LeanQbe.T.Examples.Kissat.Proof.Float64.Spec",
                ),
                d1_kinds,
            )
            self.assertIn(
                (
                    "LeanQbe/T/Examples/Kissat/Src/Full.lean",
                    "transitive-data-to-proof",
                    "LeanQbe.T.Examples.Kissat.Proof.Float64.Spec",
                ),
                d1_kinds,
            )
            self.assertIn(
                ("LeanQbe/T/Examples/Kissat/Src/LeafA.lean", "LeanQbe.T.PrintCpp"),
                d2_mods,
            )
            self.assertIn(
                ("LeanQbe/T/Examples/Kissat/Src/Full.lean", "LeanQbe.T.Legal"),
                d2_mods,
            )


if __name__ == "__main__":
    unittest.main()
