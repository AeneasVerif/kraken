#!/usr/bin/env python3
"""Unit & smoke tests for P0-1/P0-2/P0-4/P0-5/P1-1/P2-1/P2-2 infrastructure scripts."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
import tomllib
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
sys.path.insert(0, str(SCRIPTS_DIR))

import _common  # noqa: E402
import lean_imports as li  # noqa: E402
import rdeps_scope as rs  # noqa: E402
import select_tests as st  # noqa: E402
import sync_hubs as sh  # noqa: E402


class TestHubIsolationAndNoLegacy(unittest.TestCase):
    def test_no_legacy_libs_or_imports(self) -> None:
        self.assertEqual(len(sh.ALL_HUBS), 20)
        for hub in sh.ALL_HUBS:
            self.assertNotIn("Legacy", hub)
        self.assertFalse((REPO_ROOT / "LeanQbeLegacyTest").exists())
        self.assertFalse((REPO_ROOT / "LeanQbeLegacyAmd64.lean").exists())
        self.assertFalse((REPO_ROOT / "LeanQbeLegacyArm64.lean").exists())

        for p in sorted((REPO_ROOT / "LeanQbeTest").rglob("*.lean")):
            _, imps = li.parse_imports(p)
            for imp in imps:
                self.assertFalse(
                    imp.module.startswith("LeanQbeLegacy"),
                    f"{p} imports retired {imp.module}",
                )


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
        # Includes Step-7..10+ assembly proofs + dual-arch KissatFidelityParam/CompileGuard rdeps.
        self.assertLess(len(mods), 120)

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
                    "LeanQbe/T/Amd64/KissatPlainCert1.lean",
                    "LeanQbeTest/T/Smoke.lean",
                    "LeanQbeTest/T/KissatM5Test.lean",
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


def _git(repo: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", "-C", str(repo), *args],
        capture_output=True,
        text=True,
        timeout=30,
        check=check,
    )


def _current_branch(repo: Path) -> str | None:
    res = _git(repo, "symbolic-ref", "--short", "HEAD", check=False)
    if res.returncode != 0:
        return None
    return res.stdout.strip() or None


def _run_fast_land_dry_run(
    script: Path,
    staging: Path,
    target: str,
    *,
    cwd: Path,
    land_branch: str | None = None,
) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    if land_branch is None:
        env.pop("LAND_BRANCH", None)
    else:
        env["LAND_BRANCH"] = land_branch
    return subprocess.run(
        ["bash", str(script), "--dry-run", str(staging), target],
        cwd=str(cwd),
        env=env,
        capture_output=True,
        text=True,
        timeout=30,
        check=False,
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
            cur = _current_branch(REPO_ROOT)
            dirty = bool(_git(REPO_ROOT, "status", "--porcelain").stdout.strip())
            head_sha = _git(REPO_ROOT, "rev-parse", "HEAD").stdout.strip()
            main_res = _git(
                REPO_ROOT, "rev-parse", "--verify", "refs/heads/leanqbe/main^{commit}", check=False
            )
            main_sha = main_res.stdout.strip() if main_res.returncode == 0 else None

            if cur is not None:
                land_branch = cur
            elif main_sha == head_sha:
                land_branch = "leanqbe/main"
            else:
                land_branch = f"__test_detached_cas_{os.getpid()}__"
                while (
                    _git(
                        REPO_ROOT,
                        "show-ref",
                        "--verify",
                        "--quiet",
                        f"refs/heads/{land_branch}",
                        check=False,
                    ).returncode
                    == 0
                ):
                    land_branch += "_x"

            res = _run_fast_land_dry_run(
                SCRIPTS_DIR / "fast_land.sh",
                Path(tmp),
                "HEAD",
                cwd=REPO_ROOT,
                land_branch=land_branch,
            )
            # Dirty tree during uncommitted dev is rejected cleanly; clean tree passes dry-run.
            if dirty:
                self.assertIn("working tree is dirty", res.stderr)
            else:
                self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
                self.assertIn("CHECK_SCOPE=auto", res.stdout)
                if cur is None:
                    self.assertIn("running on detached HEAD", res.stdout)
                    if main_sha is not None and main_sha != head_sha:
                        bad = _run_fast_land_dry_run(
                            SCRIPTS_DIR / "fast_land.sh",
                            Path(tmp),
                            "HEAD",
                            cwd=REPO_ROOT,
                            land_branch="leanqbe/main",
                        )
                        self.assertEqual(bad.returncode, 1, bad.stdout + bad.stderr)
                        self.assertIn("!= refs/heads/leanqbe/main", bad.stderr)

    def test_fast_land_dry_run_symbolic_and_detached_cas(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "repo"
            staging = Path(tmp) / "staging"
            staging.mkdir()
            (root / "scripts").mkdir(parents=True)
            for name in (
                "fast_land.sh",
                "common.sh",
                "select_tests.py",
                "sync_hubs.py",
                "lean_imports.py",
            ):
                shutil.copy2(SCRIPTS_DIR / name, root / "scripts" / name)

            _git(root, "init")
            _git(root, "symbolic-ref", "HEAD", "refs/heads/leanqbe/main")
            _git(root, "config", "user.name", "Test")
            _git(root, "config", "user.email", "test@example.com")
            _git(root, "config", "commit.gpgsign", "false")
            _git(root, "add", "scripts")
            _git(root, "commit", "-m", "base")

            _git(root, "checkout", "-b", "feature")
            (root / "NOTES.md").write_text("doc note\n", encoding="utf-8")
            _git(root, "add", "NOTES.md")
            _git(root, "commit", "-m", "doc")

            fast_land = root / "scripts" / "fast_land.sh"

            # Symbolic branch mode
            _git(root, "checkout", "leanqbe/main")
            sym_ok = _run_fast_land_dry_run(fast_land, staging, "feature", cwd=root)
            self.assertEqual(sym_ok.returncode, 0, sym_ok.stdout + sym_ok.stderr)
            self.assertIn("fast-forwards main", sym_ok.stdout)
            self.assertIn("CHECK_SCOPE=auto", sym_ok.stdout)

            sym_bad = _run_fast_land_dry_run(
                fast_land, staging, "feature", cwd=root, land_branch="other"
            )
            self.assertEqual(sym_bad.returncode, 1, sym_bad.stdout + sym_bad.stderr)
            self.assertIn("must run on 'other'", sym_bad.stderr)

            # Detached HEAD matching leanqbe/main CAS
            _git(root, "checkout", "--detach", "leanqbe/main")
            det_ok = _run_fast_land_dry_run(fast_land, staging, "feature", cwd=root)
            self.assertEqual(det_ok.returncode, 0, det_ok.stdout + det_ok.stderr)
            self.assertIn("running on detached HEAD", det_ok.stdout)
            self.assertIn("git update-ref refs/heads/leanqbe/main", det_ok.stdout)
            self.assertIn("CHECK_SCOPE=auto", det_ok.stdout)

            # Detached HEAD CAS mismatch rejected, matching LAND_BRANCH accepted
            _git(root, "checkout", "--detach", "feature")
            det_bad = _run_fast_land_dry_run(fast_land, staging, "HEAD", cwd=root)
            self.assertEqual(det_bad.returncode, 1, det_bad.stdout + det_bad.stderr)
            self.assertIn("!= refs/heads/leanqbe/main", det_bad.stderr)

            det_override = _run_fast_land_dry_run(
                fast_land, staging, "HEAD", cwd=root, land_branch="feature"
            )
            self.assertEqual(det_override.returncode, 0, det_override.stdout + det_override.stderr)
            self.assertIn("will CAS-update refs/heads/feature", det_override.stdout)
            self.assertIn("CHECK_SCOPE=auto", det_override.stdout)


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
            self.assertEqual(sh.classify_module(mod), want, mod)
            self.assertIn(want, sh.ALL_HUBS)
            self.assertIn(want, rs.BARRELS)

    def test_arch_roots_import_corehub_not_leanqbe(self) -> None:
        for root_mod in (
            "LeanQbeAmd64",
            "LeanQbeArm64",
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
            # CoreHub includes pure decoupling helpers (`CompileGuard`, `MainCertInlineProof`),
            # N5 `OptFlat*`/`MainFlat*`, and split lemma modules (still decoupled from Kissat,
            # Unified, Wasm, and non-core Logic helpers).
            self.assertLess(len(cl), 320, f"{test_mod} closure too large: {len(cl)}")
            kissat = [m for m in cl if "Examples.Kissat" in m]
            self.assertEqual(kissat, [], f"{test_mod} leaked Kissat modules: {kissat[:5]}")
            trimmed = [
                m
                for m in cl
                if m.startswith(("LeanQbe.T.Unified.", "LeanQbe.T.Wasm."))
                or m
                in {
                    "LeanQbe.T.Logic.CanonicalEnv",
                    "LeanQbe.T.Logic.MemAlgebra",
                    "LeanQbe.T.Logic.SlabLayoutElab",
                    "LeanQbe.T.Logic.U32",
                }
            ]
            self.assertEqual(trimmed, [], f"{test_mod} leaked trimmed modules: {trimmed[:5]}")

    def test_trimmed_hub_classification_and_corehub_separation(self) -> None:
        self.assertEqual(sh.classify_module("LeanQbe.T.Unified.Ssa"), "LeanQbe.T.Unified.Hub")
        self.assertEqual(sh.classify_module("LeanQbe.T.Wasm.Ast"), "LeanQbe.T.Wasm.Hub")
        for mod in (
            "LeanQbe.T.Logic.CanonicalEnv",
            "LeanQbe.T.Logic.MemAlgebra",
            "LeanQbe.T.Logic.SlabLayoutElab",
            "LeanQbe.T.Logic.U32",
        ):
            self.assertEqual(sh.classify_module(mod), "LeanQbe.T.Logic.ExtraHub")
        for hub in ("LeanQbe.T.Unified.Hub", "LeanQbe.T.Wasm.Hub", "LeanQbe.T.Logic.ExtraHub"):
            self.assertIn(hub, sh.ALL_HUBS)
            self.assertIn(hub, rs.BARRELS)
        core_cl = li.compute_import_closure(["LeanQbe.T.CoreHub"], REPO_ROOT)
        for mod in core_cl:
            self.assertFalse(mod.startswith(("LeanQbe.T.Unified.", "LeanQbe.T.Wasm.")), mod)
            self.assertNotIn(
                mod,
                {
                    "LeanQbe.T.Logic.CanonicalEnv",
                    "LeanQbe.T.Logic.MemAlgebra",
                    "LeanQbe.T.Logic.SlabLayoutElab",
                    "LeanQbe.T.Logic.U32",
                },
            )

    def test_optional_lakefile_targets_preserve_defaults(self) -> None:
        data = tomllib.loads((REPO_ROOT / "lakefile.toml").read_text(encoding="utf-8"))
        self.assertEqual(
            data["defaultTargets"],
            ["LeanQbe", "LeanQbeAmd64", "LeanQbeArm64", "LeanQbeTest", "leanqbe", "leanqbe-arm64"],
        )
        libs = {entry["name"] for entry in data.get("lean_lib", [])}
        for name in ("LeanQbeCore", "LeanQbeAmd64Core", "LeanQbeArm64Core"):
            self.assertIn(name, libs)
        for retired in (
            "LeanQbeCoreTest",
            "LeanQbeLegacyAmd64",
            "LeanQbeLegacyArm64",
            "LeanQbeLegacyTest",
        ):
            self.assertNotIn(retired, libs)
        exes = {entry["name"]: entry for entry in data.get("lean_exe", [])}
        self.assertIn("audit_axioms", exes)
        self.assertEqual(exes["audit_axioms"]["root"], "scripts.AuditAxioms")


class TestPreflightAndGateParity(unittest.TestCase):
    """Covers P0-1 + P0-5 preflight hygiene, swap/slice flags, and unittest wiring."""

    def _run_preflight_in_temp_repo(
        self,
        base_files: dict[str, str],
        head_files: dict[str, str],
    ) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            scripts = root / "scripts"
            scripts.mkdir()
            for name in ("preflight.sh", "lean_imports.py"):
                shutil.copy2(SCRIPTS_DIR / name, scripts / name)
            (scripts / "check_firewall.py").write_text(
                "import sys\nsys.exit(0)\n", encoding="utf-8"
            )
            (scripts / "sync_hubs.py").write_text(
                "import sys\nsys.exit(0)\n", encoding="utf-8"
            )
            for rel, txt in base_files.items():
                p = root / rel
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(txt, encoding="utf-8")
            _git(root, "init")
            _git(root, "config", "user.name", "Test")
            _git(root, "config", "user.email", "test@example.com")
            _git(root, "config", "commit.gpgsign", "false")
            _git(root, "add", "-A")
            _git(root, "commit", "-m", "base")
            base_sha = _git(root, "rev-parse", "HEAD").stdout.strip()

            for rel, txt in head_files.items():
                p = root / rel
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(txt, encoding="utf-8")
            _git(root, "add", "-A")
            _git(root, "commit", "-m", "change")

            return subprocess.run(
                ["bash", str(scripts / "preflight.sh"), base_sha],
                cwd=str(root),
                capture_output=True,
                text=True,
                timeout=30,
                check=False,
            )

    def test_preflight_catches_axiom_and_expose_on_theorem(self) -> None:
        res_ax = self._run_preflight_in_temp_repo(
            {"README.md": "ok\n"},
            {"LeanQbe/T/BadAx.lean": "module\nprivate axiom badAx : False\n"},
        )
        self.assertNotEqual(res_ax.returncode, 0)
        self.assertIn("forbidden token", res_ax.stderr)

        res_exp = self._run_preflight_in_temp_repo(
            {"README.md": "ok\n"},
            {
                "LeanQbe/T/BadExpose.lean": (
                    "module\n@[expose]\nprivate lemma bad_lem : True := trivial\n"
                )
            },
        )
        self.assertNotEqual(res_exp.returncode, 0)
        self.assertIn("@[expose] on theorem/lemma", res_exp.stderr)

        # Comments, strings, @[expose] def, and bv_decide_qbe/ must NOT fail.
        res_ok = self._run_preflight_in_temp_repo(
            {"README.md": "ok\n"},
            {
                "LeanQbe/T/Clean.lean": (
                    "module\n"
                    "-- axiom ignored in comment\n"
                    "/- @[expose] theorem ignored_block : True := trivial -/\n"
                    '@[expose] def msg : String := "axiom @[expose] theorem"\n'
                    "@[simp] theorem clean_ok : True := trivial\n"
                ),
                "bv_decide_qbe/TestSkip.lean": "axiom ignoredHere : False\n",
            },
        )
        self.assertEqual(res_ok.returncode, 0, res_ok.stdout + res_ok.stderr)

    def test_preflight_2500_loc_and_grandfathered_handling(self) -> None:
        new_2500 = "\n".join(["-- line"] * 2500) + "\n"
        res_new = self._run_preflight_in_temp_repo(
            {"README.md": "ok\n"},
            {"LeanQbe/T/TooBig.lean": new_2500},
        )
        self.assertNotEqual(res_new.returncode, 0)
        self.assertIn("2500 LOC >= 2500", res_new.stderr)

        grand_base = "\n".join(["-- line"] * 2600) + "\n"
        grand_same = "\n".join(["-- ok"] * 2600) + "\n"
        res_same = self._run_preflight_in_temp_repo(
            {"LeanQbe/T/Grand.lean": grand_base},
            {"LeanQbe/T/Grand.lean": grand_same},
        )
        self.assertEqual(res_same.returncode, 0, res_same.stdout + res_same.stderr)

        grand_grown = "\n".join(["-- ok"] * 2601) + "\n"
        res_grown = self._run_preflight_in_temp_repo(
            {"LeanQbe/T/Grand.lean": grand_base},
            {"LeanQbe/T/Grand.lean": grand_grown},
        )
        self.assertNotEqual(res_grown.returncode, 0)
        self.assertIn("grandfathered file grew 2600 -> 2601", res_grown.stderr)

    def test_preflight_p0_5_proof_shard_rules_and_no_false_positives(self) -> None:
        # 1. Any `import all` banned in Kissat/Proof/ & Bitblast/Proof/
        res_imp = self._run_preflight_in_temp_repo(
            {"README.md": "ok\n"},
            {
                "LeanQbe/T/Examples/Kissat/Proof/Sub.lean": (
                    "module\nimport all Kraken.Mem\n"
                )
            },
        )
        self.assertNotEqual(res_imp.returncode, 0)
        self.assertIn("forbidden `import all` in Proof/ shard", res_imp.stderr)

        # 2. File-level `@[expose] public section` over theorems banned
        res_sec = self._run_preflight_in_temp_repo(
            {"README.md": "ok\n"},
            {
                "LeanQbe/T/Examples/Bitblast/Proof/BadSec.lean": (
                    "module\n@[expose] public section\ntheorem bad : True := trivial\n"
                )
            },
        )
        self.assertNotEqual(res_sec.returncode, 0)
        self.assertIn("@[expose] public section", res_sec.stderr)

        # 3. Single theorem > 450 lines flagged; <= 450 lines + trailing doc comment OK
        long_thm = (
            "module\npublic section\ntheorem mega_wp : True := by\n"
            + "\n".join(["  have h := True.intro"] * 449)
            + "\n  exact h\n"
        )
        res_long = self._run_preflight_in_temp_repo(
            {"README.md": "ok\n"},
            {"LeanQbe/T/Examples/Kissat/Proof/Mega.lean": long_thm},
        )
        self.assertNotEqual(res_long.returncode, 0)
        self.assertIn("451 lines > 450", res_long.stderr)

        ok_450 = (
            "module\npublic section\ntheorem ok_wp : True := by\n"
            + "\n".join(["  have h := True.intro"] * 448)
            + "\n  exact h\n\n/-- trailing doc comment for next decl -/\n"
            + "\n".join(["-- comment"] * 10)
            + "\ntheorem tiny : True := trivial\n"
        )
        res_450 = self._run_preflight_in_temp_repo(
            {"README.md": "ok\n"},
            {"LeanQbe/T/Examples/Bitblast/Proof/Ok450.lean": ok_450},
        )
        self.assertEqual(res_450.returncode, 0, res_450.stdout + res_450.stderr)

        # 4. Non-theorem data defs in Bitblast/Proof/ & Kissat/Proof/Spec/ must pass
        res_spec_ok = self._run_preflight_in_temp_repo(
            {"README.md": "ok\n"},
            {
                "LeanQbe/T/Examples/Kissat/Proof/Spec/DataOnly.lean": (
                    "module\n@[expose] public section\n"
                    "structure SpecHdr where\n  x : Nat\n"
                    "def specFn (h : SpecHdr) : Nat := h.x\n"
                ),
                "LeanQbe/T/Examples/Bitblast/Proof/SpecAndProof.lean": (
                    "module\n@[expose] public section\n"
                    "def localSpec : Nat := 1\n"
                    "end\n"
                    "public section\n"
                    "@[expose] def exposedData : Nat := 2\n"
                    "theorem proof_ok : localSpec = 1 := rfl\n"
                ),
            },
        )
        self.assertEqual(res_spec_ok.returncode, 0, res_spec_ok.stdout + res_spec_ok.stderr)

    def test_gate_scripts_swap_slice_and_unittest_wiring(self) -> None:
        common_sh = (SCRIPTS_DIR / "common.sh").read_text(encoding="utf-8")
        self.assertIn("--slice=", common_sh)
        self.assertIn("MemorySwapMax=0", common_sh)
        self.assertIn("OOMPolicy=kill", common_sh)

        check_txt = (SCRIPTS_DIR / "check.sh").read_text(encoding="utf-8")
        self.assertIn("common.sh", check_txt)
        self.assertIn("run_cgroup", check_txt)
        self.assertIn("unittest discover", check_txt)

        fast_txt = (SCRIPTS_DIR / "fast_land.sh").read_text(encoding="utf-8")
        self.assertIn("common.sh", fast_txt)
        self.assertIn("run_cgroup", fast_txt)

    def test_common_sh_build_and_run_cgroup(self) -> None:
        common_sh = SCRIPTS_DIR / "common.sh"
        script = (
            f'source "{common_sh}"\n'
            'LEANQBE_FORCE_SCOPE=1 build_cgroup_cmd c_on 12G u1 leanqbe-builds.slice '
            '-- lake build\n'
            'printf "ON:%s\\n" "${c_on[*]}"\n'
            'CHECK_NO_SCOPE=1 LEANQBE_FORCE_SCOPE=0 build_cgroup_cmd c_off 12G u1 '
            'leanqbe-builds.slice -- lake build\n'
            'printf "OFF:%s\\n" "${c_off[*]}"\n'
            'CHECK_NO_SCOPE=1 run_cgroup --mem 8G --timeout 10 -- echo cgroup-ok\n'
        )
        res = subprocess.run(
            ["timeout", "15", "bash", "-c", script],
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(res.returncode, 0, res.stderr)
        self.assertIn(
            "ON:systemd-run --user --scope --quiet --unit=u1 "
            "--slice=leanqbe-builds.slice -p MemoryMax=12G "
            "-p MemorySwapMax=0 -p OOMPolicy=kill lake build",
            res.stdout,
        )
        self.assertIn("OFF:lake build", res.stdout)
        self.assertIn("cgroup-ok", res.stdout)

    def test_consolidated_rdeps_closure_and_scope_classification(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "A.lean").write_text("def a : Nat := 1\n", encoding="utf-8")
            (root / "B.lean").write_text(
                "import A\ndef b : Nat := a + 1\n", encoding="utf-8"
            )
            (root / "LeanQbe.lean").write_text("import B\n", encoding="utf-8")
            (root / "Test.lean").write_text(
                "import B\ndef t : Nat := b\n", encoding="utf-8"
            )
            closure = li.compute_import_closure(["LeanQbe"], root)
            self.assertEqual(closure, {"LeanQbe", "A", "B"})

            rdeps = li.collect_lean_rdeps(
                root,
                ["A"],
                lean_rel_paths=["A.lean", "B.lean", "LeanQbe.lean", "Test.lean"],
                barrels={"LeanQbe"},
            )
            self.assertEqual(rdeps, ["A", "B", "Test"])

        self.assertEqual(li.classify_scope_paths(["README.md"]), "class0")
        self.assertEqual(li.classify_scope_paths(["scripts/common.sh"]), "full")
        self.assertEqual(li.classify_scope_paths(["scripts/_common.py"]), "full")
        self.assertEqual(
            li.classify_scope_paths(["LeanQbe/T/Amd64/Foo.lean"]), "x64"
        )

    def test_audit_batches_rdeps_filter_cli(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td) / "repo"
            tmp_dir = Path(td) / "tmp"
            (root / "LeanQbe" / "T").mkdir(parents=True)
            tmp_dir.mkdir()
            (root / "LeanQbe" / "T" / "ModA.lean").write_text(
                "theorem thm_a : True := trivial\n", encoding="utf-8"
            )
            (root / "LeanQbe" / "T" / "ModB.lean").write_text(
                "theorem thm_b : True := trivial\n", encoding="utf-8"
            )
            (tmp_dir / "closure_LeanQbe.txt").write_text(
                "LeanQbe.T.ModA\nLeanQbe.T.ModB\n", encoding="utf-8"
            )
            (tmp_dir / "headlines_all.txt").write_text(
                "LeanQbe.T.ModA thm_a\nLeanQbe.T.ModB thm_b\n", encoding="utf-8"
            )
            rf = tmp_dir / "rdeps_headlines_filter.txt"
            rf.write_text("LeanQbe.T.ModA\n", encoding="utf-8")

            rc = _common.main(
                ["audit-batches", str(root), str(tmp_dir), "rdeps", str(rf)]
            )
            self.assertEqual(rc, 0)
            selected = (tmp_dir / "selected_headlines.txt").read_text(encoding="utf-8")
            manifest = (tmp_dir / "audit_manifest.txt").read_text(encoding="utf-8")
            self.assertEqual(selected, "LeanQbe.T.ModA thm_a\n")
            self.assertIn("thm_a", manifest)
            self.assertNotIn("thm_b", manifest)

            rc_full = _common.main(
                ["audit-batches", str(root), str(tmp_dir), "full", ""]
            )
            self.assertEqual(rc_full, 0)
            self.assertEqual(
                (tmp_dir / "selected_headlines.txt").read_text(encoding="utf-8"),
                "LeanQbe.T.ModA thm_a\nLeanQbe.T.ModB thm_b\n",
            )


if __name__ == "__main__":
    unittest.main()
