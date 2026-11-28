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
        groups = cf.run_audit(REPO_ROOT, require_isa=True, purity_ref=True)
        by_id = {g.leak_id: g for g in groups}
        self.assertIn("LeanQbe/T/Examples/Vibesat/Ref/XorF2.lean", by_id["P-Ref"].files)
        for g in groups:
            self.assertEqual(g.violations, [], f"{g.leak_id}: {g.violations}")


class TestModsysFirewalls(unittest.TestCase):
    """Covers Wave M0 `--modsys` / `--modsys-report-only` rules (`M1`-`M6`)."""

    def test_m1_through_m6_catch_violations_and_accept_clean(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)

            def wf(rel: str, body: str) -> None:
                p = root / rel
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(body, encoding="utf-8")

            # M1: MainFlat privately reaches a Lemmas file; MainCertSegElab meta-imports
            # a proof-bearing module; Amd64.Isa is clean.
            wf("LeanQbe/T/MainFlat.lean", "module\npublic import LeanQbe.T.LegalFlat\n")
            wf("LeanQbe/T/LegalFlat.lean", "module\nimport LeanQbe.T.MainLemmas\n")
            wf("LeanQbe/T/MainLemmas.lean", "module\n")
            wf("LeanQbe/T/Amd64/Isa.lean", "module\n")
            wf("LeanQbe/T/MainCertSeg.lean", "module\nimport LeanQbe.T.Logic.C0Step\n")
            wf("LeanQbe/T/Logic/C0Step.lean", "module\n")
            wf(
                "LeanQbe/T/MainCertSegElab.lean",
                "module\npublic meta import LeanQbe.T.MainCertSeg\n",
            )

            # M2: Build/Amd64 dirty vs clean
            wf(
                "LeanQbe/T/Examples/Kissat/Build/Amd64/Dirty.lean",
                "module\n"
                "meta import LeanQbe.T.MainCertSegElab\n"
                "meta import LeanQbe.T.Amd64.Targ\n",
            )
            wf(
                "LeanQbe/T/Examples/Kissat/Build/Amd64/Clean.lean",
                "module\n"
                "import LeanQbe.T.MainCertSegElab\n"
                "meta import LeanQbe.T.Amd64.Isa\n",
            )

            # M3: public meta import allowlist vs hard-deny paths
            wf(
                "LeanQbe/T/Examples/Kissat/Src/Header.lean",
                "module\npublic meta import Lean.Elab.Tactic\n",
            )
            wf(
                "LeanQbe/T/Examples/Kissat/Proof/Sub/Tactics.lean",
                "module\npublic meta import Lean.Elab.Tactic\n",
            )
            wf(
                "LeanQbe/T/FooElab.lean",
                "module\npublic meta import Lean.Elab.Command\n",
            )

            # M4: Proof-only public import in Proof/ and *Lemmas*
            wf(
                "LeanQbe/T/Examples/Kissat/Proof/Sub/WpBad.lean",
                "module\n"
                "public import LeanQbe.T.Logic.C0Step\n"
                "public import LeanQbe.T.Logic.ProofKit\n"
                "public import LeanQbe.T.Logic.ControlComb\n"
                "public import Kraken.SeparationTactics\n"
                "public import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas\n"
                "import LeanQbe.T.Logic.C0HeadStep\n",
            )
            wf(
                "LeanQbe/T/BadLemmas.lean",
                "module\npublic import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics\n",
            )

            # M5: import all (both BAD_IMPORT_ALL and Kraken import all)
            wf(
                "LeanQbe/T/Bedrock2/BadAll.lean",
                "module\nimport all LeanQbe.T.FlatLemmas\nimport all Kraken.Mem\n",
            )

            # M6: hub import + leaf test vs shared fixture test
            wf(
                "LeanQbeTest/T/SharedFixture.lean",
                "module\npublic import LeanQbe.T.Amd64.Isa\n",
            )
            wf(
                "LeanQbeTest/T/LeafBad.lean",
                "module\n"
                "public import LeanQbe.T.CoreHub\n"
                "public import LeanQbeTest.T.SharedFixture\n"
                "public meta import Lean.Elab.Term\n",
            )
            wf(
                "LeanQbeTest/T/LeafClean.lean",
                "module\nimport LeanQbeTest.T.SharedFixture\nmeta import Lean.Elab.Term\n",
            )

            groups = cf.run_audit(root, modsys=True)
            by_id = {g.leak_id: g for g in groups}
            for mid in ("M1", "M2", "M3", "M4", "M5", "M6"):
                self.assertIn(mid, by_id)
                self.assertFalse(by_id[mid].report_only)

            m1_hits = {(v.file, v.kind, v.module) for v in by_id["M1"].violations}
            self.assertIn(
                ("LeanQbe/T/MainFlat.lean", "m1-exec-proof-leak", "LeanQbe.T.MainLemmas"),
                m1_hits,
            )
            self.assertIn(
                (
                    "LeanQbe/T/MainCertSegElab.lean",
                    "m1-cert-elab-meta-proof-leak",
                    "LeanQbe.T.Logic.C0Step",
                ),
                m1_hits,
            )
            self.assertFalse(any(v.file == "LeanQbe/T/Amd64/Isa.lean" for v in by_id["M1"].violations))

            m2_hits = {(v.file, v.kind, v.module) for v in by_id["M2"].violations}
            self.assertEqual(
                m2_hits,
                {
                    (
                        "LeanQbe/T/Examples/Kissat/Build/Amd64/Dirty.lean",
                        "m2-meta-elab-import",
                        "LeanQbe.T.MainCertSegElab",
                    ),
                    (
                        "LeanQbe/T/Examples/Kissat/Build/Amd64/Dirty.lean",
                        "m2-meta-targ-import",
                        "LeanQbe.T.Amd64.Targ",
                    ),
                },
            )

            m3_files = {v.file for v in by_id["M3"].violations}
            self.assertIn("LeanQbe/T/Examples/Kissat/Src/Header.lean", m3_files)
            self.assertIn("LeanQbe/T/Examples/Kissat/Proof/Sub/Tactics.lean", m3_files)
            self.assertIn("LeanQbeTest/T/LeafBad.lean", m3_files)
            self.assertNotIn("LeanQbe/T/FooElab.lean", m3_files)
            self.assertNotIn("LeanQbe/T/MainCertSegElab.lean", m3_files)

            m4_hits = {(v.file, v.module) for v in by_id["M4"].violations}
            self.assertIn(
                ("LeanQbe/T/Examples/Kissat/Proof/Sub/WpBad.lean", "LeanQbe.T.Logic.C0Step"),
                m4_hits,
            )
            self.assertIn(
                ("LeanQbe/T/Examples/Kissat/Proof/Sub/WpBad.lean", "Kraken.SeparationTactics"),
                m4_hits,
            )
            self.assertNotIn(
                ("LeanQbe/T/Examples/Kissat/Proof/Sub/WpBad.lean", "LeanQbe.T.Logic.C0HeadStep"),
                m4_hits,
            )
            self.assertIn(
                ("LeanQbe/T/BadLemmas.lean", "LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics"),
                m4_hits,
            )

            m5_hits = {(v.file, v.kind, v.module) for v in by_id["M5"].violations}
            self.assertEqual(
                m5_hits,
                {
                    ("LeanQbe/T/Bedrock2/BadAll.lean", "bad-import-all", "LeanQbe.T.FlatLemmas"),
                    ("LeanQbe/T/Bedrock2/BadAll.lean", "import-all", "Kraken.Mem"),
                },
            )
            # Ratcheting allowlist hides only allowlisted entry
            groups_al = cf.run_audit(
                root,
                modsys=True,
                m5_allowlist={"LeanQbe/T/Bedrock2/BadAll.lean": {"Kraken.Mem"}},
            )
            m5_al = {g.leak_id: g for g in groups_al}["M5"].violations
            self.assertEqual([(v.kind, v.module) for v in m5_al], [("bad-import-all", "LeanQbe.T.FlatLemmas")])

            m6_hits = {(v.file, v.kind, v.module) for v in by_id["M6"].violations}
            self.assertIn(("LeanQbeTest/T/LeafBad.lean", "m6-hub-import", "LeanQbe.T.CoreHub"), m6_hits)
            self.assertIn(
                ("LeanQbeTest/T/LeafBad.lean", "m6-leaf-test-public-import", "LeanQbeTest.T.SharedFixture"),
                m6_hits,
            )
            self.assertIn(
                ("LeanQbeTest/T/LeafBad.lean", "m6-leaf-test-public-meta-import", "Lean.Elab.Term"),
                m6_hits,
            )
            self.assertFalse(any(v.file == "LeanQbeTest/T/SharedFixture.lean" for v in by_id["M6"].violations))
            self.assertFalse(any(v.file == "LeanQbeTest/T/LeafClean.lean" for v in by_id["M6"].violations))

            # --modsys-report-only still exits 0 when L1-L5 are clean, but fails if L1 leaks
            self.assertEqual(cf.main(["--root", str(root), "--modsys-report-only"]), 0)
            wf("LeanQbe/T/MainLemmas.lean", "module\npublic import LeanQbe.T.OptLemmas\n")
            self.assertEqual(cf.main(["--root", str(root), "--modsys-report-only"]), 1)

    def test_real_repo_m0_modsys_invariants_and_report_only_cli(self) -> None:
        groups = cf.run_audit(
            REPO_ROOT,
            require_isa=True,
            data_proof=True,
            purity_ref=True,
            modsys_report_only=True,
        )
        by_id = {g.leak_id: g for g in groups}
        for mid in ("M1", "M2", "M3", "M4", "M5", "M6"):
            self.assertIn(mid, by_id)
            self.assertTrue(by_id[mid].report_only)
        # Wave M0 guarantees: 0 BAD_IMPORT_ALL, 0 hub imports, 0 demo-cert public meta imports
        bad_all = [v for v in by_id["M5"].violations if v.kind == "bad-import-all"]
        self.assertEqual(bad_all, [], f"unexpected BAD_IMPORT_ALL: {bad_all}")
        hub_viols = [v for v in by_id["M6"].violations if v.kind == "m6-hub-import"]
        self.assertEqual(hub_viols, [], f"unexpected hub imports: {hub_viols}")
        demo_m3 = [
            v for v in by_id["M3"].violations if "LcnfC0LoopDemoCert" in v.file
        ]
        self.assertEqual(demo_m3, [], f"unexpected demo-cert M3 violations: {demo_m3}")
        # M1 catches current MainFlat proof-import bypasses in report-only mode
        self.assertTrue(any(v.file == "LeanQbe/T/MainFlat.lean" for v in by_id["M1"].violations))
        # CLI exits 0 under --modsys-report-only when strict checks pass
        rc = cf.main(
            [
                "--root",
                str(REPO_ROOT),
                "--require-isa",
                "--data-proof",
                "--purity-ref",
                "--modsys-report-only",
                "--max-per-group",
                "3",
            ]
        )
        self.assertEqual(rc, 0)


if __name__ == "__main__":
    unittest.main()
