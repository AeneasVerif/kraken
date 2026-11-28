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


class TestPurityFirewalls(unittest.TestCase):
    """Covers opt-in `--purity-ref` (`P-Ref`) and `--purity-spec` (`P-Spec`) rules."""

    def test_purity_ref_accepts_clean_and_catches_all_violations(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            rdir = root / "LeanQbe" / "T" / "Examples" / "Kissat" / "Ref"
            rdir.mkdir(parents=True)
            (rdir / "Clean.lean").write_text(
                "module\n"
                "public import LeanQbe.T.Examples.Kissat.Ref.Base\n"
                "def helper (x : Nat) : Nat := x + 1\n",
                encoding="utf-8",
            )
            (rdir / "Dirty.lean").write_text(
                "module\n"
                "public import Kraken.Mem\n"
                "public import LeanQbe.T.Frontend.C0.Ast\n"
                "public import LeanQbe.T.Logic.SpecTable\n"
                "public import LeanQbe.T.Examples.Kissat.Src.Arena\n"
                "public import LeanQbe.T.Examples.Kissat.Spec.Core\n"
                "public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec\n"
                "meta import Lean.Elab.Command\n"
                "theorem bad : True := trivial\n"
                "lemma bad2 : True := trivial\n"
                "axiom badAx : False\n"
                "macro \"m\" : tactic => `(tactic| trivial)\n"
                "elab \"e\" : tactic => pure ()\n"
                "syntax \"s\" : term\n",
                encoding="utf-8",
            )
            files = cf.discover_purity_ref_files(root)
            self.assertEqual(
                files,
                [
                    "LeanQbe/T/Examples/Kissat/Ref/Clean.lean",
                    "LeanQbe/T/Examples/Kissat/Ref/Dirty.lean",
                ],
            )
            viols = cf.check_purity_ref_files(root, files, {})
            self.assertFalse(any(v.file.endswith("Clean.lean") for v in viols))
            dirty_kinds = [(v.kind, v.module, v.line) for v in viols]
            self.assertIn(("ref-forbidden-import", "Kraken.Mem", 2), dirty_kinds)
            self.assertIn(("ref-forbidden-import", "LeanQbe.T.Frontend.C0.Ast", 3), dirty_kinds)
            self.assertIn(("ref-forbidden-import", "LeanQbe.T.Logic.SpecTable", 4), dirty_kinds)
            self.assertIn(
                ("ref-forbidden-import", "LeanQbe.T.Examples.Kissat.Src.Arena", 5),
                dirty_kinds,
            )
            self.assertIn(
                ("ref-forbidden-import", "LeanQbe.T.Examples.Kissat.Spec.Core", 6),
                dirty_kinds,
            )
            self.assertIn(
                ("ref-forbidden-import", "LeanQbe.T.Examples.Kissat.Proof.Arena.Spec", 7),
                dirty_kinds,
            )
            self.assertIn(("ref-meta-import", "Lean.Elab.Command", 8), dirty_kinds)
            decl_lines = {v.line for v in viols if v.kind == "ref-forbidden-decl"}
            self.assertEqual(decl_lines, {9, 10, 11, 12, 13, 14})

    def test_purity_spec_accepts_clean_and_catches_all_violations(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sdir = root / "LeanQbe" / "T" / "Examples" / "Kissat" / "Spec"
            sdir.mkdir(parents=True)
            (sdir / "Clean.lean").write_text(
                "module\n"
                "public import LeanQbe.T.Logic.SpecTable\n"
                "public import LeanQbe.T.Logic.C0Agrees\n"
                "public import LeanQbe.T.Examples.Kissat.Spec.Core\n"
                "public import LeanQbe.T.Examples.Kissat.Spec.Layout\n"
                "public import LeanQbe.T.Examples.Kissat.Ref.Base\n"
                "public import Kraken.Mem\n"
                "public import Kraken.Separation\n"
                "@[expose] def cleanSpec : Spec [i64] [] :=\n"
                "  FullContract.toSpec (W := Unit)\n"
                "    { pre  := fun _ _ _ () => True\n"
                "      post := fun _ _ _ () _ _ => a ∧ b ∧ c }\n",
                encoding="utf-8",
            )
            bad_pre_conj = " ∧ ".join(f"p{i}" for i in range(13))
            pdir = root / "LeanQbe" / "T" / "Examples" / "Kissat" / "Proof" / "Watch"
            pdir.mkdir(parents=True)
            (pdir / "Spec.lean").write_text(
                "module\n"
                "public import LeanQbe.T.Logic.C0Step\n"
                "public import LeanQbe.T.Logic.SlabChain\n"
                "public import Kraken.SeparationTactics\n"
                "public import LeanQbe.T.Examples.Kissat.Spec.Arena\n"
                "public import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas\n"
                "import all LeanQbe.T.Examples.Kissat.Ref.Base\n"
                "meta import Lean.Elab.Command\n"
                "@[expose] def deps : List SpecEntry := []\n"
                "abbrev deps2 := 0\n"
                "theorem bad_thm : True := trivial\n"
                "@[expose] def badSafetySliceSpec := 0\n"
                "@[expose] def badStep13 := 0\n"
                "@[expose] def rawIdx (ws' : List Nat) := ws'[0]? = some 1 ∧ hdr[17]? = some 2\n"
                "@[expose] def tooMany : Spec [i64] [] :=\n"
                "  FullContract.toSpec (W := Unit)\n"
                f"    {{ pre  := fun _ _ _ () => {bad_pre_conj}\n"
                "      post := fun _ _ _ () _ _ => True }\n",
                encoding="utf-8",
            )
            files = cf.discover_purity_spec_files(root)
            self.assertEqual(
                files,
                [
                    "LeanQbe/T/Examples/Kissat/Proof/Watch/Spec.lean",
                    "LeanQbe/T/Examples/Kissat/Spec/Clean.lean",
                ],
            )
            viols = cf.check_purity_spec_files(root, files, {})
            self.assertEqual([v for v in viols if v.file.endswith("Clean.lean")], [])
            kinds = {(v.kind, v.module, v.line) for v in viols}
            self.assertIn(("spec-forbidden-import", "LeanQbe.T.Logic.C0Step", 2), kinds)
            self.assertIn(("spec-forbidden-import", "LeanQbe.T.Logic.SlabChain", 3), kinds)
            self.assertIn(("spec-forbidden-import", "Kraken.SeparationTactics", 4), kinds)
            self.assertIn(
                ("spec-cross-spec-import", "LeanQbe.T.Examples.Kissat.Spec.Arena", 5),
                kinds,
            )
            self.assertIn(
                (
                    "spec-proof-import",
                    "LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas",
                    6,
                ),
                kinds,
            )
            self.assertIn(
                ("spec-import-all", "LeanQbe.T.Examples.Kissat.Ref.Base", 7),
                kinds,
            )
            self.assertIn(("spec-meta-import", "Lean.Elab.Command", 8), kinds)
            self.assertTrue(any(v.kind == "spec-deps-decl" and v.line == 9 for v in viols))
            self.assertTrue(any(v.kind == "spec-forbidden-decl" and v.line == 11 for v in viols))
            legacy_lines = {v.line for v in viols if v.kind == "spec-legacy-ident"}
            self.assertEqual(legacy_lines, {12, 13})
            raw_lines = [v for v in viols if v.kind == "spec-raw-index"]
            self.assertGreaterEqual(len(raw_lines), 1)
            conj_viols = [v for v in viols if v.kind == "spec-conjunct-cap"]
            self.assertEqual(len(conj_viols), 1)
            self.assertIn("13 > 12", conj_viols[0].detail)

    def test_default_check_firewall_stays_clean(self) -> None:
        groups = cf.run_audit(REPO_ROOT, require_isa=True)
        for g in groups:
            self.assertEqual(g.violations, [], f"{g.leak_id}: {g.violations}")


if __name__ == "__main__":
    unittest.main()
