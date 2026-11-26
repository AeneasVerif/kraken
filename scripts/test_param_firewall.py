"""Unit tests for L5 param/compile-guard firewall, rdeps, and frontier metadata."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

import check_firewall  # noqa: E402
import l2_audit  # noqa: E402
import rdeps_scope  # noqa: E402


def _write_files(root: Path, mapping: dict[str, str]) -> None:
    """Create relative Lean/config files inside synthetic workspace `root`."""
    for rel, body in mapping.items():
        path = root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body, encoding="utf-8")


class ParamFirewallTests(unittest.TestCase):
    """Tests for `check_firewall.py` L5 and companion guard infrastructure."""

    def test_real_repo_passes_l1_through_l5(self) -> None:
        reports = check_firewall.run_audit(REPO_ROOT, require_isa=True)
        by_id = {g.leak_id: g for g in reports}
        self.assertIn("L5", by_id)
        for gid, grp in by_id.items():
            self.assertEqual(
                grp.violations,
                [],
                f"{gid} reported unexpected violations: {grp.violations}",
            )
        expected_l5 = {
            "LeanQbe/T/Amd64/KissatFidelityParam.lean",
            "LeanQbe/T/Arm64/KissatFidelityParam.lean",
            "LeanQbe/T/CompileGuard.lean",
            "LeanQbeTest/T/KissatFidelityCompileGuardX64.lean",
            "LeanQbeTest/T/KissatFidelityCompileGuardArm64.lean",
        }
        self.assertTrue(expected_l5.issubset(set(by_id["L5"].files)))

    def test_l5_catches_param_leaks(self) -> None:
        bad_imports = [
            ("LeanQbe.T.Amd64.FakeCert", "param-cert-leak"),
            ("LeanQbe.T.MainCertInline", "param-cert-leak"),
            ("LeanQbe.T.Examples.Kissat.FullFidelityInl0", "param-inl-leak"),
            ("LeanQbe.T.Arm64.KissatAbi", "param-cross-arch"),
            ("Lean", "param-lean-meta"),
        ]
        for imp_mod, expected_kind in bad_imports:
            with self.subTest(imp_mod=imp_mod):
                with tempfile.TemporaryDirectory() as tmp:
                    root = Path(tmp)
                    _write_files(
                        root,
                        {
                            "LeanQbe/T/Amd64/TestParam.lean": (
                                f"module\npublic import {imp_mod}\n"
                            ),
                            "LeanQbe/T/MainCertInline.lean": "module\n",
                            "LeanQbe/T/Amd64/FakeCert.lean": "module\n",
                            "LeanQbe/T/Examples/Kissat/FullFidelityInl0.lean": "module\n",
                            "LeanQbe/T/Arm64/KissatAbi.lean": "module\n",
                        },
                    )
                    l5 = [g for g in check_firewall.run_audit(root) if g.leak_id == "L5"][0]
                    kinds = {v.kind for v in l5.violations}
                    self.assertIn(expected_kind, kinds)

    def test_l5_catches_compile_guard_core_leaks(self) -> None:
        for bad_imp in (
            "LeanQbe.T.MainLemmas",
            "LeanQbe.T.MainCertProof",
            "LeanQbe.T.MainInline",
            "LeanQbe.T.Amd64.Targ",
            "Lean",
        ):
            with self.subTest(bad_imp=bad_imp):
                with tempfile.TemporaryDirectory() as tmp:
                    root = Path(tmp)
                    _write_files(
                        root,
                        {
                            "LeanQbe/T/CompileGuard.lean": f"module\npublic import {bad_imp}\n",
                            "LeanQbe/T/MainLemmas.lean": "module\n",
                            "LeanQbe/T/MainCertProof.lean": "module\n",
                            "LeanQbe/T/MainInline.lean": "module\n",
                            "LeanQbe/T/Amd64/Targ.lean": "module\n",
                        },
                    )
                    l5 = [g for g in check_firewall.run_audit(root) if g.leak_id == "L5"][0]
                    kinds = {v.kind for v in l5.violations}
                    self.assertIn("compile-guard-core-leak", kinds)

    def test_l5_catches_guard_leaf_violations(self) -> None:
        cases = [
            ("public import LeanQbe.T.CompileGuard\n", "guard-public-import"),
            ("meta import LeanQbe.T.MainInline\n", "guard-direct-forbidden"),
            ("meta import LeanQbe.T.CompileGuard\nmeta import HelperBridge\n", "guard-transitive-leak"),
            ("meta import LeanQbe.T.Arm64.Isa\n", "guard-cross-arch"),
            ("meta import HelperLeanBridge\n", "guard-lean-meta"),
        ]
        for body, expected_kind in cases:
            with self.subTest(expected_kind=expected_kind):
                with tempfile.TemporaryDirectory() as tmp:
                    root = Path(tmp)
                    _write_files(
                        root,
                        {
                            "LeanQbeTest/T/FakeCompileGuardX64.lean": f"module\n{body}",
                            "LeanQbe/T/CompileGuard.lean": "module\n",
                            "LeanQbe/T/MainInline.lean": "module\n",
                            "LeanQbe/T/Arm64/Isa.lean": "module\n",
                            "HelperBridge.lean": "module\npublic import LeanQbe.T.Amd64.Targ\n",
                            "LeanQbe/T/Amd64/Targ.lean": "module\n",
                            "HelperLeanBridge.lean": "module\npublic import Lean\n",
                        },
                    )
                    l5 = [g for g in check_firewall.run_audit(root) if g.leak_id == "L5"][0]
                    kinds = {v.kind for v in l5.violations}
                    self.assertIn(expected_kind, kinds)

    def test_l5_allows_patchmodule_lean_bridge(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_files(
                root,
                {
                    "LeanQbe/T/Amd64/OkParam.lean": (
                        "module\npublic import LeanQbe.T.Examples.Kissat.Step7\n"
                    ),
                    "LeanQbe/T/Examples/Kissat/Step7.lean": (
                        "module\npublic import LeanQbe.T.Examples.Kissat.PatchModule\n"
                    ),
                    "LeanQbe/T/Examples/Kissat/PatchModule.lean": (
                        "module\npublic meta import Lean\n"
                    ),
                },
            )
            l5 = [g for g in check_firewall.run_audit(root) if g.leak_id == "L5"][0]
            self.assertEqual(l5.violations, [])

    def test_rdeps_tracks_meta_imports_to_compile_guards(self) -> None:
        direct_rdeps = rdeps_scope.compute_rdeps(
            REPO_ROOT, ["LeanQbe/T/CompileGuard.lean"], include_legacy=True
        )
        self.assertIsNotNone(direct_rdeps)
        assert direct_rdeps is not None
        self.assertIn("LeanQbeTest.T.KissatFidelityCompileGuardX64", direct_rdeps)
        self.assertIn("LeanQbeTest.T.KissatFidelityCompileGuardArm64", direct_rdeps)

        for changed in (
            "LeanQbe/T/Main.lean",
            "LeanQbe/T/Amd64/Isa.lean",
            "LeanQbe/T/Arm64/Isa.lean",
        ):
            rdeps = rdeps_scope.compute_rdeps(
                REPO_ROOT, [changed], max_rdeps=2000, include_legacy=True
            )
            self.assertIsNotNone(rdeps)
            assert rdeps is not None
            if "Arm64" not in changed:
                self.assertIn("LeanQbeTest.T.KissatFidelityCompileGuardX64", rdeps)
            if "Amd64" not in changed:
                self.assertIn("LeanQbeTest.T.KissatFidelityCompileGuardArm64", rdeps)

    def test_frontier_lakefile_and_headlines_present(self) -> None:
        for mod in (
            "LeanQbe.T.Amd64.KissatFidelityParam",
            "LeanQbe.T.Arm64.KissatFidelityParam",
            "LeanQbeTest.T.KissatFidelityCompileGuardX64",
            "LeanQbeTest.T.KissatFidelityCompileGuardArm64",
        ):
            self.assertIn(mod, l2_audit.CANARY_FRONTIER)

        lakefile = (REPO_ROOT / "lakefile.toml").read_text(encoding="utf-8")
        self.assertIn('name = "LeanQbeCompileGuards"', lakefile)
        self.assertLess(
            lakefile.index('name = "LeanQbeCompileGuards"'),
            lakefile.rindex('name = "LeanQbe"'),
        )

        headlines_path = REPO_ROOT / "scripts" / "headlines.d" / "kissat_fidelity_param.txt"
        self.assertTrue(headlines_path.is_file())
        entries = [
            line.strip().split()
            for line in headlines_path.read_text(encoding="utf-8").splitlines()
            if line.strip() and not line.strip().startswith("#")
        ]
        self.assertEqual(len(entries), 60)
        for pair in entries:
            self.assertEqual(len(pair), 2)


if __name__ == "__main__":
    unittest.main()
