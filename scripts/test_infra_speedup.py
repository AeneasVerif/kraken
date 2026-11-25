#!/usr/bin/env python3
"""Unit & smoke tests for P0-1/P0-2/P0-4/P0-5/P1-1/P2-1/P2-2 infrastructure scripts."""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
import tomllib
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
sys.path.insert(0, str(SCRIPTS_DIR))

import lean_imports as li  # noqa: E402
import rdeps_scope as rs  # noqa: E402
import select_tests as st  # noqa: E402
import sync_hubs as sh  # noqa: E402


class TestLegacyStageA(unittest.TestCase):
    def test_shared_legacy_regex_partition(self) -> None:
        self.assertIs(sh.load_legacy_regex(REPO_ROOT), li.LEGACY_CERT_RE)
        # Retired generations
        for mod in (
            "LeanQbe.T.Amd64.KissatM5",
            "LeanQbe.T.Arm64.KissatM5Cert12",
            "LeanQbe.T.Amd64.KissatM6",
            "LeanQbe.T.Arm64.KissatM6CertLink",
            "LeanQbe.T.Amd64.KissatM7Plus",
            "LeanQbe.T.Amd64.KissatM7PlusCert",
            "LeanQbe.T.Amd64.KissatM7PlusCertLink",
            "LeanQbe.T.Amd64.KissatM7PlusCert1",
            "LeanQbe.T.Amd64.KissatM7PlusCert14",
            "LeanQbe.T.Arm64.KissatM7PlusCert22",
            "LeanQbe.T.Amd64.KissatM7PlusCert45",
            "LeanQbe.T.Arm64.KissatM7PlusCert56",
        ):
            self.assertIsNotNone(li.LEGACY_CERT_RE.match(mod), mod)

        # Active kept modules: KissatM7PlusBounds + 38 reused slices + all KissatM7Fidelity*
        for mod in (
            "LeanQbe.T.Amd64.KissatM7PlusBounds",
            "LeanQbe.T.Arm64.KissatM7PlusBounds",
            "LeanQbe.T.Amd64.KissatM7PlusCert2",
            "LeanQbe.T.Amd64.KissatM7PlusCert13",
            "LeanQbe.T.Amd64.KissatM7PlusCert16",
            "LeanQbe.T.Amd64.KissatM7PlusCert23",
            "LeanQbe.T.Amd64.KissatM7PlusCert42",
            "LeanQbe.T.Amd64.KissatM7PlusCert43",
            "LeanQbe.T.Amd64.KissatM7PlusCert44",
            "LeanQbe.T.Arm64.KissatM7PlusCert44",
            "LeanQbe.T.Amd64.KissatM7Fidelity",
            "LeanQbe.T.Amd64.KissatM7FidelityCert",
            "LeanQbe.T.Arm64.KissatM7FidelityCert49",
        ):
            self.assertIsNone(li.LEGACY_CERT_RE.match(mod), mod)

    def test_no_active_test_leaks_legacy(self) -> None:
        imp_cache: dict[str, list[str]] = {}

        def imps(mod: str) -> list[str]:
            if mod not in imp_cache:
                p = REPO_ROOT / li.mod_to_rel_path(mod)
                imp_cache[mod] = [i.module for i in li.parse_imports(p)[1]] if p.is_file() else []
            return imp_cache[mod]

        for p in sorted((REPO_ROOT / "LeanQbeTest").rglob("*.lean")):
            root_mod = li.rel_path_to_mod(p.relative_to(REPO_ROOT))
            seen: set[str] = set()
            stack = [root_mod]
            while stack:
                cur = stack.pop()
                if cur in seen:
                    continue
                seen.add(cur)
                self.assertFalse(
                    cur.startswith("LeanQbeLegacy"),
                    f"{root_mod} transitively imports {cur}",
                )
                self.assertIsNone(
                    li.LEGACY_CERT_RE.match(cur),
                    f"{root_mod} transitively imports legacy cert {cur}",
                )
                for nxt in imps(cur):
                    if nxt not in seen:
                        stack.append(nxt)


class TestRdepsScope(unittest.TestCase):
    def test_leaf_test_module_small_rdeps(self) -> None:
        mods = rs.compute_rdeps(REPO_ROOT, ["LeanQbeTest/T/Amd64FrameTest.lean"])
        self.assertEqual(mods, ["LeanQbeTest.T.Amd64FrameTest"])

    def test_barrel_skipped_on_leaf_edit(self) -> None:
        mods = rs.compute_rdeps(
            REPO_ROOT,
            [
                "LeanQbe/T/Examples/Kissat/FullFidelityAssembly.lean",
                "LeanQbe/T/Examples/Kissat/FidelityHub.lean",
            ],
        )
        self.assertIsNotNone(mods)
        assert mods is not None
        self.assertIn("LeanQbe.T.Examples.Kissat.FullFidelityAssembly", mods)
        self.assertNotIn("LeanQbe.T.Examples.Kissat.FidelityHub", mods)
        self.assertLess(len(mods), 40)

    def test_fail_closed_cases(self) -> None:
        # Empty list
        self.assertIsNone(rs.compute_rdeps(REPO_ROOT, []))
        # Deletion / missing file
        self.assertIsNone(rs.compute_rdeps(REPO_ROOT, ["LeanQbe/T/DoesNotExist.lean"]))
        # Toolchain / gate files
        for f in (
            "lakefile.toml",
            "lean-toolchain",
            "lake-manifest.json",
            "scripts/check.sh",
            "scripts/AuditAxioms.lean",
        ):
            self.assertIsNone(rs.compute_rdeps(REPO_ROOT, [f]), f)
        # Barrel-only edit -> no non-barrel seeds -> fail closed
        self.assertIsNone(rs.compute_rdeps(REPO_ROOT, ["LeanQbe.lean"]))
        # Widely imported core file exceeds max_rdeps
        self.assertIsNone(rs.compute_rdeps(REPO_ROOT, ["LeanQbe/T/IL.lean"], max_rdeps=250))

    def test_exe_root_mapping(self) -> None:
        tgts = rs.modules_to_lake_targets(["Main", "MainArm64", "LeanQbeTest.T.Smoke"])
        self.assertEqual(tgts, ["LeanQbeTest.T.Smoke", "leanqbe", "leanqbe-arm64"])


class TestSelectTests(unittest.TestCase):
    def test_proof_doc_script_barrel_zero_suites(self) -> None:
        self.assertEqual(
            st.select_suites(
                [
                    "LeanQbe-README.md",
                    "docs/design.md",
                    "scripts/check.sh",
                    "scripts/headlines.d/core.txt",
                    "LeanQbe.lean",
                    "LeanQbeAmd64.lean",
                    "LeanQbe/T/Examples/Kissat/FullFidelityAssemblyProof.lean",
                    "LeanQbe/T/OptLemmas.lean",
                    "LeanQbe/T/Amd64/KissatM7FidelityCert1.lean",
                    "LeanQbeTest/T/Smoke.lean",
                    "LeanQbeLegacyTest/KissatM5Test.lean",
                ]
            ),
            [],
        )

    def test_subsystem_routing(self) -> None:
        self.assertEqual(
            st.select_suites(["LeanQbe/T/Frontend/C0/Lower.lean"]),
            ["./test/c0/run.sh"],
        )
        self.assertEqual(
            st.select_suites(["LeanQbe/T/LeanLCNF/Lower.lean"]),
            ["./test/lcnf/run.sh"],
        )
        self.assertEqual(
            st.select_suites(["LeanQbe/T/LeanLRC/Lower.lean"]),
            ["./test/lrc/run.sh"],
        )
        self.assertEqual(
            st.select_suites(["LeanQbe/T/Bootstrap0/Emit.lean"]),
            ["./test/bootstrap0/run_stage_c_native.sh"],
        )
        self.assertEqual(
            st.select_suites(["LeanQbe/T/Examples/Kissat/FullFidelityAssembly.lean"]),
            ["bash ./bench/kissat/build_c0_direct.sh --asan"],
        )
        self.assertEqual(
            st.select_suites(["LeanQbe/T/Examples/Kissat/Solver.lean"]),
            ["./test/kissat/run.sh"],
        )
        self.assertEqual(
            st.select_suites(["LeanQbe/T/PrintCpp.lean"]),
            ["./test/cpp/run.sh", "./test/t_lrat/run.sh"],
        )
        self.assertEqual(
            st.select_suites(["LeanQbe/T/PrintQbe.lean"]),
            ["./test/t_qbe/run.sh"],
        )
        self.assertEqual(
            st.select_suites(["LeanQbe/T/Examples/LratBytes.lean"]),
            ["./test/t_lrat/run.sh", "./tool/test_lrat_check.sh"],
        )
        self.assertEqual(
            st.select_suites(["LeanQbe/T/Amd64/Bignum.lean"]),
            ["./test/t_bignum/run.sh"],
        )
        self.assertEqual(
            st.select_suites(["LeanQbe/T/Arm64/ChaCha.lean"]),
            ["./test/t_chacha/run.sh"],
        )
        self.assertEqual(
            st.select_suites(["LeanQbe/T/Amd64/Frame.lean"]),
            ["./test/run.sh", "./test/kissat/run.sh"],
        )
        self.assertEqual(
            st.select_suites(["LeanQbe/T/Arm64/Frame.lean"]),
            ["./test/arm64/run.sh", "./test/kissat/run.sh"],
        )
        self.assertEqual(
            st.select_suites(["LeanQbe/T/IL.lean"]),
            ["./test/run.sh", "./test/arm64/run.sh", "./test/kissat/run.sh"],
        )


class TestCheckAndFastLandSmoke(unittest.TestCase):
    def test_check_classify_stdin(self) -> None:
        def classify(lines: list[str]) -> str:
            res = subprocess.run(
                ["bash", str(SCRIPTS_DIR / "check.sh"), "--classify-stdin"],
                input="\n".join(lines) + "\n",
                capture_output=True,
                text=True,
                check=True,
                timeout=30,
            )
            return res.stdout.strip()

        self.assertEqual(classify(["scripts/preflight.sh", "scripts/select_tests.py"]), "class0")
        self.assertEqual(classify(["scripts/check.sh"]), "full")
        self.assertEqual(classify(["scripts/AuditAxioms.lean"]), "full")
        self.assertEqual(classify(["LeanQbe/T/Amd64/Frame.lean"]), "x64")
        self.assertEqual(classify(["LeanQbe/T/Arm64/Frame.lean"]), "arm64")

    def test_fast_land_dry_run_branch_override(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            env = os.environ.copy()
            sym = subprocess.run(
                ["git", "-C", str(REPO_ROOT), "symbolic-ref", "--short", "HEAD"],
                capture_output=True,
                text=True,
                check=False,
            )
            cur = sym.stdout.strip() if sym.returncode == 0 else ""
            if cur:
                env["LAND_BRANCH"] = cur
            else:
                head_sha = subprocess.check_output(
                    ["git", "-C", str(REPO_ROOT), "rev-parse", "HEAD"], text=True
                ).strip()
                # Detached HEAD: find a matching branch ref if present, else use default.
                refs = subprocess.run(
                    [
                        "git",
                        "-C",
                        str(REPO_ROOT),
                        "for-each-ref",
                        "--format=%(refname:short) %(objectname)",
                        "refs/heads/",
                    ],
                    capture_output=True,
                    text=True,
                    check=False,
                )
                matched = next(
                    (
                        ln.split()[0]
                        for ln in refs.stdout.splitlines()
                        if len(ln.split()) == 2 and ln.split()[1] == head_sha
                    ),
                    None,
                )
                if matched:
                    env["LAND_BRANCH"] = matched
            res = subprocess.run(
                [
                    "bash",
                    str(SCRIPTS_DIR / "fast_land.sh"),
                    "--dry-run",
                    tmp,
                    "HEAD",
                ],
                cwd=str(REPO_ROOT),
                env=env,
                capture_output=True,
                text=True,
                timeout=30,
                check=False,
            )
            # Dirty tree during uncommitted dev is rejected cleanly; clean tree passes dry-run.
            if subprocess.check_output(
                ["git", "-C", str(REPO_ROOT), "status", "--porcelain"], text=True
            ).strip():
                self.assertIn("working tree is dirty", res.stderr)
            elif cur or "LAND_BRANCH" in env:
                self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
                self.assertIn("CHECK_SCOPE=auto", res.stdout)
            else:
                # Detached HEAD with no matching branch ref: fast_land checks CAS cleanly.
                self.assertIn("fast_land", res.stdout + res.stderr)


class TestP1DecouplingAndHubs(unittest.TestCase):
    def test_kissat_hub_split_classification(self) -> None:
        pfx = "LeanQbe.T.Examples.Kissat."
        cases = {
            f"{pfx}FullFidelityAssembly": f"{pfx}FidelityHub",
            f"{pfx}FullM8CoreParity": f"{pfx}M8Hub",
            f"{pfx}FullM7": f"{pfx}M7Hub",
            f"{pfx}FullM6": f"{pfx}M6Hub",
            f"{pfx}FullM5": f"{pfx}M5Hub",
            f"{pfx}FullM4": f"{pfx}M4Hub",
            f"{pfx}FullM3": f"{pfx}M3Hub",
            f"{pfx}Core": f"{pfx}BaseHub",
        }
        for mod, want in cases.items():
            self.assertEqual(sh.classify_module(mod, li.LEGACY_CERT_RE), want, mod)
            self.assertIn(want, sh.ALL_HUBS)
            self.assertIn(want, rs.BARRELS)

    def test_arch_roots_import_corehub_not_leanqbe(self) -> None:
        for root_mod in (
            "LeanQbeAmd64",
            "LeanQbeArm64",
            "LeanQbeLegacyAmd64",
            "LeanQbeLegacyArm64",
        ):
            _, imps = li.parse_imports(REPO_ROOT / li.mod_to_rel_path(root_mod))
            direct = {i.module for i in imps}
            self.assertIn("LeanQbe.T.CoreHub", direct, root_mod)
            self.assertNotIn("LeanQbe", direct, root_mod)

    def test_four_unit_tests_decoupled_from_kissat(self) -> None:
        imp_cache: dict[str, list[str]] = {}

        def local_closure(root_mod: str) -> set[str]:
            seen: set[str] = set()
            stack = [root_mod]
            while stack:
                cur = stack.pop()
                if cur in seen:
                    continue
                p = REPO_ROOT / li.mod_to_rel_path(cur)
                if not p.is_file():
                    continue
                seen.add(cur)
                if cur not in imp_cache:
                    imp_cache[cur] = [i.module for i in li.parse_imports(p)[1]]
                for nxt in imp_cache[cur]:
                    if nxt not in seen:
                        stack.append(nxt)
            return seen

        for test_mod in (
            "LeanQbeTest.T.KitTest",
            "LeanQbeTest.T.LegalTest",
            "LeanQbeTest.T.NotationTest",
            "LeanQbeTest.T.TargetConsumerTest",
        ):
            cl = local_closure(test_mod)
            self.assertLess(len(cl), 220, f"{test_mod} closure too large: {len(cl)}")
            kissat = [m for m in cl if "Examples.Kissat" in m]
            self.assertEqual(kissat, [], f"{test_mod} leaked Kissat modules: {kissat[:5]}")

    def test_optional_lakefile_targets_preserve_defaults(self) -> None:
        data = tomllib.loads((REPO_ROOT / "lakefile.toml").read_text(encoding="utf-8"))
        self.assertEqual(
            data["defaultTargets"],
            ["LeanQbe", "LeanQbeAmd64", "LeanQbeArm64", "LeanQbeTest", "leanqbe", "leanqbe-arm64"],
        )
        libs = {entry["name"] for entry in data.get("lean_lib", [])}
        for name in ("LeanQbeCore", "LeanQbeAmd64Core", "LeanQbeArm64Core", "LeanQbeCoreTest"):
            self.assertIn(name, libs)
        exes = {entry["name"]: entry for entry in data.get("lean_exe", [])}
        self.assertIn("audit_axioms", exes)
        self.assertEqual(exes["audit_axioms"]["root"], "scripts.AuditAxioms")


if __name__ == "__main__":
    unittest.main()
